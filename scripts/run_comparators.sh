#!/usr/bin/env bash
# Run the comparator pairs under Riesz2Audit/. A missing pair or a failed check is fatal.
#
#   scripts/run_comparators.sh [--no-sandbox] [PAIR ...]
#
# With no PAIR, all six pairs run. Each pair is checked by `lake comparator`, bundled with the
# Lean toolchain, which replays the solution with Lean's kernel and with the NanoDa and con-ron
# kernels of the toolchain. The comparator runs the build inside a `bwrap` sandbox, so it needs
# bubblewrap (Linux). On a machine without bubblewrap, such as macOS, `--no-sandbox` runs it
# unsandboxed: the checks are the same, but they then trust the machine that runs them.
# Logs are written to .lake/comparator-logs/<PAIR>.log.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"

ALL=(LongRangeGapCorrelations ShortRangeGapCorrelations Convergence QuantitativeConvergence
     Hyperuniformity Repulsion)
SANDBOX=()
if [[ "${1:-}" == "--no-sandbox" ]]; then
  SANDBOX=(--inadvisably-no-sandbox)
  shift
elif ! command -v bwrap >/dev/null; then
  echo "Missing command: bwrap (bubblewrap). On macOS, pass --no-sandbox." >&2
  exit 1
fi
PAIRS=("$@")
[[ ${#PAIRS[@]} -gt 0 ]] || PAIRS=("${ALL[@]}")

PREFIX="$(lean --print-prefix)"
for tool in nanoda_bin con-ron; do
  [[ -x "$PREFIX/bin/$tool" ]] || { echo "The toolchain does not bundle $tool" >&2; exit 1; }
done
LOGS="$ROOT/.lake/comparator-logs"
CONFIGS="$(mktemp -d)"
trap 'rm -rf "$CONFIGS"' EXIT
mkdir -p "$LOGS"

# Check each configuration, then write a copy that adds the toolchain's kernels.
for pair in "${PAIRS[@]}"; do
  python3 - "$ROOT/Riesz2Audit/$pair/comparator.json" "$CONFIGS/$pair.json" "$pair" "$PREFIX" <<'PY'
import json, sys
source, target, pair, prefix = sys.argv[1:]
config = json.load(open(source))
expected = {
    'challenge_module': f'Riesz2Audit.{pair}.Challenge',
    'solution_module': f'Riesz2Audit.{pair}.Solution',
}
for key, value in expected.items():
    if config.get(key) != value:
        raise SystemExit(f'{source}: {key} must be {value}')
if set(config) != {'challenge_module', 'solution_module', 'theorem_names', 'permitted_axioms'}:
    raise SystemExit(f'{source}: unexpected configuration fields')
if sorted(config['permitted_axioms']) != ['Classical.choice', 'Quot.sound', 'propext']:
    raise SystemExit(f'{source}: permitted_axioms must be exactly the three standard axioms')
if len(config['theorem_names']) != 1:
    raise SystemExit(f'{source}: one theorem per pair')
config['external_kernels'] = {'nanoda': [f'{prefix}/bin/nanoda_bin'],
                              'con-ron': [f'{prefix}/bin/con-ron']}
json.dump(config, open(target, 'w'), indent=2)
PY
done

failed=0
for pair in "${PAIRS[@]}"; do
  printf '\n== %s\n' "$pair"
  if lake comparator --config "$CONFIGS/$pair.json" "${SANDBOX[@]}" 2>&1 | tee "$LOGS/$pair.log" \
      && grep -Fxq 'Your solution is okay!' "$LOGS/$pair.log"; then
    echo "$pair: OK"
  else
    echo "$pair: FAILED" >&2
    failed=1
  fi
done
[[ $failed -eq 0 ]] || exit 1
printf '\nAll %s comparator pairs passed. Logs: %s\n' "${#PAIRS[@]}" "$LOGS"
