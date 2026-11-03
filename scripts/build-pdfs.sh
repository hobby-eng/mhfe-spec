#!/usr/bin/env bash
set -euo pipefail

root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
cd -- "$root"

if [[ $# -eq 1 && "$1" == --local ]]; then
  # Use the workspace toolchain homes only on the owner's existing workspace.
  if [[ -d ../workingspace/cargo && -d ../workingspace/rustup ]]; then
    export CARGO_HOME="${CARGO_HOME:-$root/../workingspace/cargo}"
    export RUSTUP_HOME="${RUSTUP_HOME:-$root/../workingspace/rustup}"
    export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$root/../workingspace/mhfe-spec-target}"
    export PATH="$CARGO_HOME/bin:$PATH"
  fi
  exec cargo xtask pdf --local
elif [[ $# -ne 0 ]]; then
  printf '%s\n' 'Usage: bash scripts/build-pdfs.sh [--local]' >&2
  exit 2
fi

source_commit="$(git rev-parse HEAD)"
source_date="$(git log -1 --format=%ct HEAD)"
mkdir -p output
build_network="${MHFE_PDF_BUILD_NETWORK:-default}"
case "$build_network" in default|host) ;; *) printf '%s\n' 'Build network must be default or host' >&2; exit 2 ;; esac
tools_cache="${MHFE_PDF_TOOLS_DIR:-}"
if [[ -z "$tools_cache" && -d ../workingspace/pdf-tools/typst-0.15.1-pandoc-3.13 ]]; then
  tools_cache=../workingspace/pdf-tools/typst-0.15.1-pandoc-3.13
fi
build_args=()
if [[ -n "$tools_cache" ]]; then
  tools_cache="$(cd -- "$tools_cache" && pwd -P)"
  for tool in typst pandoc; do
    [[ -f "$tools_cache/$tool" && ! -L "$tools_cache/$tool" ]] || { printf '%s\n' 'Tool cache needs regular typst and pandoc executables' >&2; exit 2; }
  done
  build_args+=(--build-context "pinned-tools=$tools_cache" --build-arg DOCUMENT_TOOLS_STAGE=cached-tools)
fi
font_dir="${MHFE_PDF_FONT_DIR:-}"
if [[ -z "$font_dir" && -d ../workingspace/pdf-fonts/times-new-roman-2.82 ]]; then
  font_dir=../workingspace/pdf-fonts/times-new-roman-2.82
elif [[ -z "$font_dir" && -d /usr/share/fonts/truetype/msttcorefonts ]]; then
  font_dir=/usr/share/fonts/truetype/msttcorefonts
fi
[[ -n "$font_dir" ]] || { printf '%s\n' 'Set MHFE_PDF_FONT_DIR to a Times New Roman font cache outside this repository' >&2; exit 2; }
mkdir -p -- "$font_dir"
font_dir="$(cd -- "$font_dir" && pwd -P)"
case "$font_dir/" in "$root/"*) printf '%s\n' 'Keep the font cache outside this repository' >&2; exit 2 ;; esac
docker build "${build_args[@]}" --network "$build_network" --platform linux/amd64 --tag mhfe-spec-pdf:local \
  --file tooling/pdf/Dockerfile .
install_network=bridge
[[ "$build_network" != host ]] || install_network=host
docker run --rm --network "$install_network" --read-only --cap-drop ALL \
  --security-opt no-new-privileges --memory 256m --cpus 1 --pids-limit 32 \
  --user "$(id -u):$(id -g)" --env HOME=/tmp --tmpfs /tmp:rw,noexec,nosuid,size=32m \
  --mount "type=bind,source=$font_dir,target=/opt/pdf-fonts" \
  mhfe-spec-pdf:local mhfe-spec-tools install-fonts /opt/pdf-fonts
docker run --rm --network none --read-only --cap-drop ALL \
  --security-opt no-new-privileges --memory 2g --cpus 2 --pids-limit 128 \
  --user "$(id -u):$(id -g)" --env HOME=/tmp --env "MHFE_SOURCE_COMMIT=$source_commit" --env "SOURCE_DATE_EPOCH=$source_date" --env MHFE_PDF_FONT_DIR=/opt/pdf-fonts --tmpfs /tmp:rw,noexec,nosuid,size=128m \
  --mount "type=bind,source=$font_dir,target=/opt/pdf-fonts,readonly" \
  --mount "type=bind,source=$root,target=/work,readonly" \
  --mount "type=bind,source=$root/output,target=/work/output" \
  mhfe-spec-pdf:local mhfe-spec-tools pdf --local
