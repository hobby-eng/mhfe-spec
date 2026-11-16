#!/usr/bin/env bash
# Checks one Lean file of lean/ against the built project: tools/lean1.sh MhfeCore/Proofs/X.lean
# The workspace holds mhfe_spec, the mhfe_core checkout and the toolchains in workingspace/;
# MHFE_WORKSPACE overrides it.
WS_ROOT=${MHFE_WORKSPACE:-$(cd "$(dirname "$0")/../../../.." && pwd)}
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
bin=$WS_ROOT/workingspace/lean/lean-4.35.0-linux/bin
cd "$here/lean"
exec "$here/tools/run.sh" lean1 "${MEM:-6G}" "${LIMIT:-30m}" unshare -rn env PATH="$bin:$PATH" \
  "$bin/lake" env lean "$@"
