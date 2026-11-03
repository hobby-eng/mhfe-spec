ARG DOCUMENT_TOOLS_STAGE=download-tools
FROM rust:1.99.1-bookworm@sha256:9181b56c2a21ab1d5e73cffe04fc762426d30aa7fac3c91141dd033f49a7fc8b AS builder

ENV CARGO_BUILD_JOBS=2 RUSTUP_TOOLCHAIN=1.99.1
WORKDIR /build
COPY Cargo.toml Cargo.lock rust-toolchain.toml ./
COPY tooling/pdf/ tooling/pdf/
RUN --mount=type=cache,id=mhfe-spec-registry,target=/usr/local/cargo/registry,sharing=locked \
    --mount=type=cache,id=mhfe-spec-target-rust-1.99.1,target=/build/target,sharing=locked \
    cargo test --locked --package mhfe-spec-tools \
    && cargo build --locked --release --package mhfe-spec-tools --bin xtask \
    && install -D target/release/xtask /out/xtask

FROM debian:bookworm-slim@sha256:99c0b25c46d0214d5a2091092e7908907dcaecd6a962cde0ac700acee222b6f3 AS runtime

RUN apt-get update \
    && apt-get install -y --no-install-recommends ca-certificates curl poppler-utils xz-utils \
    && rm -rf /var/lib/apt/lists/*
RUN apt-get update \
    && apt-get install -y --no-install-recommends cabextract \
    && rm -rf /var/lib/apt/lists/*
COPY --from=builder /out/xtask /usr/local/bin/mhfe-spec-tools

FROM runtime AS download-tools
RUN mhfe-spec-tools install-tools /opt/pdf-tools

# This optional named context contains only the two public pinned executables.
# The renderer checks their hashes before executing either one.
FROM scratch AS cached-tools
COPY --from=pinned-tools typst /opt/pdf-tools/typst
COPY --from=pinned-tools pandoc /opt/pdf-tools/pandoc

FROM ${DOCUMENT_TOOLS_STAGE} AS selected-tools
FROM runtime
COPY --from=selected-tools /opt/pdf-tools/ /opt/pdf-tools/
ENV MHFE_TYPST=/opt/pdf-tools/typst \
    MHFE_PANDOC=/opt/pdf-tools/pandoc \
    RAYON_NUM_THREADS=2 \
    TZ=UTC \
    LANG=C.UTF-8
WORKDIR /work
