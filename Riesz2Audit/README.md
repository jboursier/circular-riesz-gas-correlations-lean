# Independent statement comparisons

The six main results of the paper are each restated here using only Mathlib and copies of the
definitions their statements use. Each restatement is proved from the library, and
[leanprover/comparator](https://github.com/leanprover/comparator) checks that the statement
proved from the library is the restated one. To read a result independently of the library,
read its `Challenge.lean` together with its `Definitions.lean`.

## How a pair is built and checked

Each subdirectory is one comparator pair:

| File | Role |
| --- | --- |
| `Definitions.lean` | Every definition the statement uses, copied verbatim in dependency order from `Riesz2/Frozen/` and the imported `Riesz1/Frozen/`, inside `Riesz2Audit.<Pair>`. It imports Mathlib only. |
| `Challenge.lean` | Imports `Definitions.lean` and states the theorem. Its final proof is the only `sorry`. Read this file and its definitions module. |
| `Solution.lean` | Imports `Definitions.lean` and the library. It states the same theorem and proves it `by exact` the corresponding library theorem. |
| `comparator.json` | The challenge and solution modules, the theorem name, and the permitted axioms. |

For example, the library's `Riesz2.gap` is
`Riesz2Audit.LongRangeGapCorrelations.Riesz2.gap` in that pair's definitions. Imported companion
definitions keep their `Riesz1` namespace inside the pair namespace. The solution can therefore
import both the copied definitions and the library. The two statements agree after unfolding
the definitions, and Lean's kernel checks the application of the library theorem.

The challenge and solution import the same Mathlib-only `Definitions.lean`.

The comparator checks the theorem and every definition it depends on. `comparator.json` permits
exactly `propext`, `Classical.choice` and `Quot.sound`. `scripts/run_comparators.sh` adds the
NanoDa and con-ron kernels bundled with the Lean toolchain, so that the solution is replayed
by three independent kernels. See the [README](../README.md#running-the-comparators) for commands.

## The pairs

| Pair | Paper statement | Library declaration |
| --- | --- | --- |
| [`LongRangeGapCorrelations`](LongRangeGapCorrelations/) | Theorem 1 | `Riesz2.longRangeGapCorrelations` |
| [`ShortRangeGapCorrelations`](ShortRangeGapCorrelations/) | Theorem 2 | `Riesz2.shortRangeGapCorrelations` |
| [`Convergence`](Convergence/) | Theorem 3 | `Riesz2.convergence` |
| [`QuantitativeConvergence`](QuantitativeConvergence/) | Theorem 4 | `Riesz2.quantitativeConvergence` |
| [`Hyperuniformity`](Hyperuniformity/) | Corollary 1.1 | `Riesz2.hyperuniformity` |
| [`Repulsion`](Repulsion/) | Proposition 1.2 | `Riesz2.repulsion` |

Each challenge's module documentation states the result in mathematical language and explains
how its objects are specified. Each definitions module describes the definitions it contains.

## Conventions shared by the challenges

- Parameters are `β > 0`, `s > 0`, `s ≠ 1`. Theorem 1 and Corollary 1.1 use `0 < s < 1`,
  and Theorem 2 uses `s > 1`. The other three results cover both ranges.
- A finite configuration is its ordered real lift `x_0 < ... < x_{N-1} < x_0+1` with
  `0 ≤ x_0 < 1`. The paper's label 1 is label 0. Gaps use the cyclic extension to integer labels.
- The long-range Gibbs law is the one defined by the imported companion library. Its definitions
  are copied into the audit modules, so those modules need no import of either Riesz library.
- Palm probabilities use the Campbell measure pulled back to configurations containing `0` and
  unbounded in both directions. `PalmRegular` concludes the support, normalization, index
  stationarity and mean-one integrable gaps needed to interpret this law.
- Real-valued definitions are total. The statements conclude their specified moment,
  integrability and measurability assertions. Finite Gibbs normalization is proved separately
  for every admissible parameter pair and positive particle number.
- Limits indexed by particle number use `N = n+1`. The count CLT uses positive real radii.
