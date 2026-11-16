#!/usr/bin/env bash
# Runs Lake 4.35.0 in the current Lean project without network, in a capped scope.
#   tools/lake.sh <name> <mem> <timeout> <lake args...>
# The workspace holds mhfe_spec, the mhfe_core checkout and the toolchains in workingspace/;
# MHFE_WORKSPACE overrides it.
WS_ROOT=${MHFE_WORKSPACE:-$(cd "$(dirname "$0")/../../../.." && pwd)}
set -euo pipefail
name=$1 mem=$2 limit=$3; shift 3
bin=$WS_ROOT/workingspace/lean/lean-4.35.0-linux/bin
here=$(cd "$(dirname "$0")" && pwd)
exec "$here/run.sh" "$name" "$mem" "$limit" unshare -rn env PATH="$bin:$PATH" "$bin/lake" "$@"
