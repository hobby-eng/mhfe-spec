#!/usr/bin/env bash
# Runs one heavy job of the code-proof run in a user scope cp-<name>.scope with a memory cap, a swap
# cap and a wall-clock limit, with the workspace toolchains on PATH.
#   tools/run.sh <name> <mem, e.g. 6G> <timeout, e.g. 2h> <command...>
# A job that exceeds its memory is killed inside its scope by the kernel; one that exceeds its time
# gets SIGTERM, then SIGKILL 60 s later. Exit status: the command's, 124 on timeout.
# The workspace holds mhfe_spec, the mhfe_core checkout and the toolchains in workingspace/;
# MHFE_WORKSPACE overrides it.
WS_ROOT=${MHFE_WORKSPACE:-$(cd "$(dirname "$0")/../../../.." && pwd)}
set -euo pipefail
name=$1 mem=$2 limit=$3; shift 3
ws=$WS_ROOT/workingspace
export CARGO_HOME=$ws/cargo RUSTUP_HOME=$ws/rustup ELAN_HOME=$ws/lean/elan
export PATH=$ws/cargo/bin:$ws/lean/elan/bin:$PATH
# Below the cap, keep a margin for the desktop.
exec systemd-run --user --scope --quiet --collect --unit="cp-$name-$$" \
  -p MemoryMax="$mem" -p MemorySwapMax="${MEMSWAP:-4G}" -p MemoryHigh="${MEMHIGH:-infinity}" -p CPUQuota=600% \
  timeout --kill-after=60 "$limit" "$@"
