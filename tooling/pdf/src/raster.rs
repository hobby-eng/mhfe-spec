use crate::failure::{Failure, Result};
use crate::layout::{PAGE_HEIGHT, PAGE_WIDTH, Position};
use png::{ColorType, Transformations};
use serde::Serialize;
use std::fs::File;
use std::io::{BufReader, BufWriter};
use std::path::Path;

const MAX_IMAGE_BYTES: usize = 64 * 1024 * 1024;
const PIXEL_DIFFERENCE: i16 = 64;
const PAGE_DIFFERENCE: f64 = 0.015;
const MATH_DIFFERENCE: f64 = 0.12;

/// White-composited luminance pixels shared by native and independent PDF rasterizers.
pub(crate) struct Raster {
    width: usize,
    height: usize,
    pixels: Vec<u8>,
}

#[derive(Serialize)]
pub(crate) struct RasterResult {
    pub(crate) page: usize,
    pub(crate) differing_pixels: usize,
    pub(crate) difference_ratio: f64,
}

impl Raster {
    /// Locate long rules in a PDF-rendered equation, independently of its math tree.
    pub(crate) fn rules(&self, start: Position, end: Position) -> (Vec<f64>, Vec<f64>) {
        let sx = self.width as f64 / PAGE_WIDTH;
        let sy = self.height as f64 / PAGE_HEIGHT;
        let left = (20.0 / 25.4 * 72.0 * sx) as usize;
        let right = self.width.saturating_sub(left);
        let top = (start.y.max(0.0) * sy) as usize;
        let bottom = ((end.y * sy) as usize).min(self.height);
        let columns = (left..right).filter(|x| {
            (top..bottom)
                .filter(|y| self.pixels[y * self.width + x] < 220)
                .count() as f64
                > (bottom - top) as f64 * 0.7
        });
        let rows = (top..bottom).filter(|y| {
            (left..right)
                .filter(|x| self.pixels[y * self.width + x] < 220)
                .count() as f64
                > (right - left) as f64 * 0.8
        });
        let groups = |coordinates: Vec<usize>, scale: f64| {
            let mut result = Vec::new();
            let mut previous = None;
            for coordinate in coordinates {
                if previous.is_none_or(|p| coordinate > p + 1) {
                    result.push(coordinate as f64 / scale);
                }
                previous = Some(coordinate);
            }
            result
        };
        (groups(columns.collect(), sx), groups(rows.collect(), sy))
    }

    pub(crate) fn read(path: &Path) -> Result<Self> {
        let mut decoder = png::Decoder::new(BufReader::new(File::open(path)?));
        decoder.set_transformations(Transformations::EXPAND | Transformations::STRIP_16);
        decoder.set_limits(png::Limits {
            bytes: MAX_IMAGE_BYTES,
        });
        let mut reader = decoder
            .read_info()
            .map_err(|e| Failure::new("PDF-PNG", e.to_string()))?;
        let size = reader
            .output_buffer_size()
            .filter(|n| *n <= MAX_IMAGE_BYTES)
            .ok_or_else(|| Failure::new("PDF-PNG", "Oversized page image"))?;
        let mut buffer = vec![0; size];
        let frame = reader
            .next_frame(&mut buffer)
            .map_err(|e| Failure::new("PDF-PNG", e.to_string()))?;
        let channels = match frame.color_type {
            ColorType::Rgb => 3,
            ColorType::Rgba => 4,
            ColorType::Grayscale => 1,
            ColorType::GrayscaleAlpha => 2,
            ColorType::Indexed => return Err(Failure::new("PDF-PNG", "Unexpanded indexed image")),
        };
        let pixels = buffer[..frame.buffer_size()]
            .chunks_exact(channels)
            .map(|pixel| {
                let value = if channels <= 2 {
                    u32::from(pixel[0])
                } else {
                    (u32::from(pixel[0]) + u32::from(pixel[1]) + u32::from(pixel[2])) / 3
                };
                let alpha = if channels == 2 {
                    u32::from(pixel[1])
                } else if channels == 4 {
                    u32::from(pixel[3])
                } else {
                    255
                };
                ((value * alpha + 255 * (255 - alpha)) / 255) as u8
            })
            .collect();
        let mut raster = Self {
            width: frame.width as usize,
            height: frame.height as usize,
            pixels,
        };
        // Filter once per page; all formula regions reuse the same pixels.
        let mut filtered = Vec::with_capacity(raster.pixels.len());
        for y in 0..raster.height {
            for x in 0..raster.width {
                filtered.push(raster.filtered(x, y));
            }
        }
        raster.pixels = filtered;
        Ok(raster)
    }

    fn filtered(&self, x: usize, y: usize) -> u8 {
        let mut sum = 0u32;
        let mut count = 0;
        for yy in y.saturating_sub(1)..=(y + 1).min(self.height - 1) {
            for xx in x.saturating_sub(1)..=(x + 1).min(self.width - 1) {
                sum += u32::from(self.pixels[yy * self.width + xx]);
                count += 1;
            }
        }
        (sum / count) as u8
    }

    fn difference(&self, other: &Self, bounds: (usize, usize, usize, usize)) -> (usize, usize) {
        let (left, top, right, bottom) = bounds;
        let mut changed = 0;
        let mut total = 0;
        for y in top..bottom.min(self.height).min(other.height) {
            for x in left..right.min(self.width).min(other.width) {
                if (i16::from(self.pixels[y * self.width + x])
                    - i16::from(other.pixels[y * other.width + x]))
                .abs()
                    > PIXEL_DIFFERENCE
                {
                    changed += 1;
                }
                total += 1;
            }
        }
        (changed, total)
    }

    fn ink_difference(&self, other: &Self, bounds: (usize, usize, usize, usize)) -> f64 {
        let (left, top, right, bottom) = bounds;
        let mut changed = 0u64;
        let mut ink_a = 0u64;
        let mut ink_b = 0u64;
        for y in top..bottom.min(self.height).min(other.height) {
            for x in left..right.min(self.width).min(other.width) {
                let a = self.pixels[y * self.width + x];
                let b = other.pixels[y * other.width + x];
                // Font rasterizers may shift an antialiased edge by one pixel.
                // Require visible ink to have nearby ink in the other image.
                // Different edge weights are normal; erasing a glyph leaves no ink.
                // Thresholds 32/16 ignore faint antialiasing fringes symmetrically.
                let nearby = |raster: &Self| {
                    let mut ink = 0;
                    for yy in y.saturating_sub(1)..=(y + 1).min(raster.height - 1) {
                        for xx in x.saturating_sub(1)..=(x + 1).min(raster.width - 1) {
                            ink = ink.max(255 - raster.pixels[yy * raster.width + xx]);
                        }
                    }
                    ink
                };
                if 255 - a > 32 && nearby(other) < 16 {
                    changed += u64::from(255 - a);
                }
                if 255 - b > 32 && nearby(self) < 16 {
                    changed += u64::from(255 - b);
                }
                ink_a += u64::from(255 - a);
                ink_b += u64::from(255 - b);
            }
        }
        changed as f64 / ink_a.max(ink_b).max(1) as f64
    }

    pub(crate) fn save_difference(&self, other: &Self, path: &Path) -> Result<()> {
        let mut output = vec![255; self.width * self.height];
        for y in 0..self.height.min(other.height) {
            for x in 0..self.width.min(other.width) {
                let difference =
                    self.pixels[y * self.width + x].abs_diff(other.pixels[y * other.width + x]);
                output[y * self.width + x] = 255 - difference.saturating_mul(3);
            }
        }
        let mut encoder = png::Encoder::new(
            BufWriter::new(File::create(path)?),
            self.width as u32,
            self.height as u32,
        );
        encoder.set_color(ColorType::Grayscale);
        encoder.set_depth(png::BitDepth::Eight);
        let mut writer = encoder
            .write_header()
            .map_err(|error| Failure::new("PDF-PNG", error.to_string()))?;
        writer
            .write_image_data(&output)
            .map_err(|error| Failure::new("PDF-PNG", error.to_string()))?;
        Ok(())
    }

    pub(crate) fn compare(
        &self,
        other: &Self,
        page: usize,
        math: &[(Position, Position)],
    ) -> Result<RasterResult> {
        // The two exporters round A4 pixel dimensions differently by at most one pixel.
        if self.width.abs_diff(other.width) > 1 || self.height.abs_diff(other.height) > 1 {
            return Err(Failure::new(
                "PDF-RASTER",
                "Native and PDF page dimensions differ",
            ));
        }
        let (changed, total) = self.difference(other, (0, 0, self.width, self.height));
        let ratio = changed as f64 / total.max(1) as f64;
        if ratio > PAGE_DIFFERENCE {
            return Err(Failure::new(
                "PDF-RASTER",
                format!("Appearance changed on page {page}: {ratio:.5}"),
            ));
        }
        for (start, end) in math
            .iter()
            .filter(|(start, end)| start.page <= page && end.page >= page)
        {
            let sx = self.width as f64 / PAGE_WIDTH;
            let sy = self.height as f64 / PAGE_HEIGHT;
            let one_line =
                start.page == end.page && (start.y - end.y).abs() < 1.0 && end.x >= start.x;
            let left = if one_line {
                ((start.x - 2.0).max(0.0) * sx) as usize
            } else {
                0
            };
            let right = if one_line {
                ((end.x + 2.0) * sx) as usize
            } else {
                self.width
            };
            let top = if start.page == page {
                ((start.y - 22.0).max(0.0) * sy) as usize
            } else {
                0
            };
            let bottom = if end.page == page {
                ((end.y + 22.0) * sy) as usize
            } else {
                self.height
            };
            let (changed, total) = self.difference(other, (left, top, right, bottom));
            let ink_ratio = self.ink_difference(other, (left, top, right, bottom));
            if total == 0
                || changed as f64 / total as f64 > MATH_DIFFERENCE
                || ink_ratio > MATH_DIFFERENCE
            {
                return Err(Failure::new(
                    "PDF-RASTER",
                    format!(
                        "Mathematical appearance changed on page {page}, relative ink difference {ink_ratio:.5}"
                    ),
                ));
            }
        }
        Ok(RasterResult {
            page,
            differing_pixels: changed,
            difference_ratio: ratio,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_a_missing_formula_even_when_the_page_difference_is_small() {
        let mut native = Raster {
            width: 500,
            height: 500,
            pixels: vec![255; 250_000],
        };
        for y in 120..140 {
            for x in 100..130 {
                native.pixels[y * 500 + x] = 0;
            }
        }
        let damaged = Raster {
            width: 500,
            height: 500,
            pixels: vec![255; 250_000],
        };
        let bounds = [(
            Position {
                page: 1,
                x: 119.0,
                y: 219.0,
            },
            Position {
                page: 1,
                x: 160.0,
                y: 219.0,
            },
        )];
        assert!(native.compare(&damaged, 1, &bounds).is_err());
        assert!(native.compare(&native, 1, &bounds).is_ok());
    }
    #[test]
    fn detects_an_erased_letter_shaped_formula_by_ink_not_white_area() {
        let mut native = Raster {
            width: 500,
            height: 500,
            pixels: vec![255; 250_000],
        };
        for (y, row) in [
            "11110", "10001", "10001", "11110", "10000", "10000", "10000",
        ]
        .iter()
        .enumerate()
        {
            for (x, b) in row.bytes().enumerate() {
                if b == b'1' {
                    native.pixels[(120 + y) * 500 + 100 + x] = 0;
                }
            }
        }
        let damaged = Raster {
            width: 500,
            height: 500,
            pixels: vec![255; 250_000],
        };
        assert!(native.difference(&damaged, (0, 0, 500, 500)).0 < 100);
        let start = Position {
            page: 1,
            x: 119.0,
            y: 205.0,
        };
        let end = Position {
            page: 1,
            x: 127.0,
            y: 205.0,
        };
        assert!(native.compare(&damaged, 1, &[(start, end)]).is_err());
    }
}
