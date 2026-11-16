#!/usr/bin/env bash
# Extracts the harness of mhfe_core (tools/make-harness.py) to Lean with hax 0.5.0 (Charon +
# Aeneas), into lean/ of this folder.
#   tools/extract.sh [extra charon arguments...]
# The checkout of mhfe_core is only read; the script checks afterwards that it is unchanged.
# The workspace holds mhfe_spec, the mhfe_core checkout and the toolchains in workingspace/;
# MHFE_WORKSPACE overrides it.
WS_ROOT=${MHFE_WORKSPACE:-$(cd "$(dirname "$0")/../../../.." && pwd)}
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
ws=$WS_ROOT/workingspace
crate=$here/harness
real=$WS_ROOT/mhfe_core
export CARGO_HOME=$ws/cargo RUSTUP_HOME=$ws/rustup XDG_CACHE_HOME=$ws/hax/cache
export PATH=$ws/cargo/bin:$PATH
charon_args=${X_CHARON:-}
unset CHARON_ARGS
aeneas_args=${X_AENEAS:-}
before=$(git -C "$real" status --porcelain)
cd "$crate"
"$here/tools/run.sh" extract "${MEM:-8G}" "${LIMIT:-2h}" \
  "$ws/hax/bin-0.5.0/cargo-hax" hax into -v --output-dir "$here/lean" lean \
  --charon-args="$charon_args" --aeneas-args="$aeneas_args" && status=0 || status=$?
after=$(git -C "$real" status --porcelain)
if [ "$before" != "$after" ]; then
  echo "extract.sh: the checkout of mhfe_core changed:" >&2
  git -C "$real" status --porcelain >&2
  exit 3
fi
exit $status
