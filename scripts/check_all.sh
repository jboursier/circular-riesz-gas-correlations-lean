#!/usr/bin/env bash
# The full check: a zero-warning build, the source sweep and the axiom report of the main results.
#
#   scripts/check_all.sh            # lake build, then the checks
#   scripts/check_all.sh --no-build # the checks only, after a build
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"
mkdir -p .lake

if [[ "${1:-}" != "--no-build" ]]; then
  echo "== lake build"
  lake build 2>&1 | tee .lake/build.log
  if grep -iE '(^|[[:space:]])warning:|declaration uses .sorry|sorryAx' .lake/build.log; then
    echo "The build must have no warnings and no incomplete proofs." >&2
    exit 1
  fi
fi

echo "== source sweep"
python3 scripts/check_sources.py "$ROOT"

echo "== axiom report of the main results"
lake env lean Riesz2/Meta/AxiomsAudit.lean 2>&1 | tee .lake/axioms-audit.log
python3 scripts/check_axioms.py .lake/axioms-audit.log

echo "ALL CHECKS PASSED"
