# Decay of correlations and thermodynamic limit for the circular Riesz gas

A machine-checked **Lean 4** formalization of the paper

> Jeanne Boursier,
> *Decay of correlations and thermodynamic limit for the circular Riesz gas*,
> [arXiv:2209.00396](https://arxiv.org/abs/2209.00396).

The six main results of the paper, Theorems 1, 2, 3 and 4, Corollary 1.1 and Proposition 1.2,
are proved for every inverse temperature `β > 0` in their respective exponent ranges. The
formalization follows the revised version of the paper (2026). Its numbering is used below
and may differ from earlier arXiv versions.

The development builds on [mathlib](https://github.com/leanprover-community/mathlib4) and the
[formalization of the companion paper](https://github.com/jboursier/circular-riesz-gas-lean),
*Optimal local laws and central limit theorem for the circular Riesz gas*
([arXiv:2112.05881](https://arxiv.org/abs/2112.05881)). Lake imports the companion library as
`Riesz1`, pinned at commit `72fbdc2`, and this development uses its proved results.

[![CI](https://github.com/jboursier/circular-riesz-gas-correlations-lean/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/jboursier/circular-riesz-gas-correlations-lean/actions/workflows/build.yml)
[![Comparator audit](https://github.com/jboursier/circular-riesz-gas-correlations-lean/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/jboursier/circular-riesz-gas-correlations-lean/actions/workflows/comparator.yml)

## What is proved

The paper studies `N` particles on the circle `T = ℝ/ℤ`, at inverse temperature `β > 0`,
with exponent `s ∈ (0, 1) ∪ (1, ∞)`:

> `g_s(x) = lim_{M→∞}(Σ_{k=-M}^M |x+k|^{-s} - 2M^{1-s}/(1-s))`, for `x ≠ 0`,
> `H_N = N^{-s} Σ_{i ≠ j} g_s(x_i-x_j)`,
> `dP_{N,β} = Z_{N,β}^{-1} exp(-β H_N) 1_{D_N} dX_N`.

Here `D_N` consists of cyclically ordered configurations, with real lifts
`x_1 < ... < x_N < x_1+1` extended by `x_{i+N} = x_i+1`. Write
`y_i = N(x_{i+1}-x_i)` and `d_N(i,j) = min(|i-j|, N-|i-j|)`. The interaction is long-range
for `0 < s < 1` and short-range, or hypersingular, for `s > 1`.

The six results are stated in [`Riesz2/Frozen/`](Riesz2/Frozen/), one file each.
`import Riesz2` loads them.

| Paper | Lean declaration | Content |
| --- | --- | --- |
| Theorem 1 | [`Riesz2.longRangeGapCorrelations`](Riesz2/Frozen/LongRangeGapCorrelations.lean) | Long-range decay of gap correlations and a negative covariance of the matching order on every mesoscopic scale. |
| Theorem 2 | [`Riesz2.shortRangeGapCorrelations`](Riesz2/Frozen/ShortRangeGapCorrelations.lean) | Short-range decay of gap correlations, including the finite-volume correction. |
| Theorem 3 | [`Riesz2.convergence`](Riesz2/Frozen/Convergence.lean) | A unique local total variation limit, its stationarity, intensity and Palm regularity. |
| Theorem 4 | [`Riesz2.quantitativeConvergence`](Riesz2/Frozen/QuantitativeConvergence.lean) | A rate for convergence of labelled gap blocks to the Palm law. |
| Corollary 1.1 | [`Riesz2.hyperuniformity`](Riesz2/Frozen/Hyperuniformity.lean) | Count and Palm span CLTs, variance asymptotics and hyperuniformity. |
| Proposition 1.2 | [`Riesz2.repulsion`](Riesz2/Frozen/Repulsion.lean) | Exponential repulsion of every labelled Palm gap. |

For Theorems 1 and 2, an observable is a Lipschitz function `ξ : ℝ → ℝ` supplied with a
Lebesgue almost everywhere strongly measurable, essentially bounded representative `ξ'` of its
almost everywhere derivative (`GapObservable`). Put

> `A_i(ξ;c,δ,d) = (E_{P_{N,β}}[ξ'(y_i)²])^{1/2} + ‖ξ'‖_{L∞(ℝ)} exp(-c d^δ)`.

The supremum here is the Lebesgue essential supremum. The expectation uses the supplied
representative of the derivative.

**Theorem 1 (long-range gap correlations).** For every `0 < s < 1`, both assertions hold:

1. For every `ε > 0` there is `δ > 0` such that, for every `β > 0`, there are `C, c > 0`
   such that, for every `N ≥ 1`, every pair of labels `i,j` and every pair of observables
   `ξ,χ`, the four variables `ξ(y_i)`, `χ(y_j)`, `ξ'(y_i)` and `χ'(y_j)` are almost everywhere
   strongly measurable with finite second moments, and, with `d = d_N(i,j)`,
   `|Cov_{P_{N,β}}[ξ(y_i),χ(y_j)]| ≤ C (1+d)^{-(2-s-ε)} A_i(ξ;c,δ,d) A_j(χ;c,δ,d)`.
2. For every `β > 0` there is `c₀ > 0` such that, for every sequence of positive integers
   `(n_N)` with `n_N → ∞` and `n_N/N → 0`, there is `m₀ ∈ ℕ` such that, for every `m ≥ m₀`,
   setting `N = m+1`, there are labels `i,j` with `n_N/2 ≤ d_N(i,j) ≤ n_N`. The two gaps
   `y_i,y_j` are almost everywhere strongly measurable with finite second moments, and
   `Cov_{P_{N,β}}[y_i,y_j] ≤ -c₀ d_N(i,j)^{s-2}`.

Thus `δ` is chosen before `β`, and `c₀` is chosen before the scale sequence and independently
of `ε`.

**Theorem 2 (short-range gap correlations).** For every `s > 1` and every `ε > 0` there is
`δ > 0` such that, for every `β > 0`, there are `C, c > 0` such that, for every `N ≥ 1`,
every pair of labels `i,j` and every pair of observables `ξ,χ`, the four variables `ξ(y_i)`,
`χ(y_j)`, `ξ'(y_i)` and `χ'(y_j)` are almost everywhere strongly measurable with finite second
moments, and, with `d = d_N(i,j)`,

> `|Cov_{P_{N,β}}[ξ(y_i),χ(y_j)]| ≤ C ((1+d)^{-s+ε} + N^{-1+ε}) A_i(ξ;c,δ,d) A_j(χ;c,δ,d)`.

For the remaining results, let `Q_{N,β}` be the law of
`C_N = Σ_i δ_{Nx_i} 1_{|x_i|<1/4}`, using the centered representatives of the particles.
Local convergence includes that every `Q_{N,β}` is a probability measure and requires
convergence in total variation after restriction to `[-R,R]`, for every `R > 0`. Under the
Palm law `Riesz_{s,β}^0`, write the points in increasing order as `(z_i)_{i∈ℤ}`, with `z_0 = 0`.

**Theorem 3 (convergence of the microscopic point process).** For every pair of parameters
`β > 0`, `s > 0`, `s ≠ 1`, there is a unique point process `P = Riesz_{s,β}` such that
`Q_{N,β}` converges locally to `P`. This process is translation invariant and has intensity one.
Its Palm law has the following properties (`PalmRegular`), in the order of the definition:

1. The set of configurations containing `0` and unbounded in both directions is measurable
   and has Palm mass one.
2. The Palm measure pulled back to that set is a probability measure. The Palm measure on
   all configurations is a probability measure and gives its complement mass zero.
3. The law of the two-sided sequence `(z_{i+1}-z_i)_{i∈ℤ}` is invariant under an index shift.
4. For every `i ∈ ℤ`, the gap `z_{i+1}-z_i` is integrable and has expectation one.

**Theorem 4 (quantitative convergence).** For every pair of parameters `β > 0`, `s > 0`,
`s ≠ 1`, there is a unique local limit `P = Riesz_{s,β}`, and `PalmRegular P` holds.
For every `ε > 0` there is `C > 0` such that, for every pair of positive integers `N,K`
with `K ≤ N^{min(s,2)/2}/32`, and every Lipschitz function `G : ℝ^K → ℝ`, both random
variables in the expectations below are integrable, and

> `|E_{P_{N,β}} G(y_1,...,y_K) - E_{Riesz_{s,β}^0} G(z_1-z_0,...,z_K-z_{K-1})|`
> `≤ C N^{-min(s,2)min(s,1)/4+ε} Σ_{j=1}^K ‖∂_j G‖∞`.

Here `‖∂_j G‖∞` denotes the least Lipschitz constant of `G` along coordinate `j`
(`coordinateDerivativeNorm`). Its sum is `blockDerivativeNorm`. In particular, the constant
`C` is chosen before `N`, `K` and `G`.

**Corollary 1.1 (hyperuniformity).** For every `0 < s < 1` and every `β > 0`, there is a
unique local limit `P = Riesz_{s,β}`. Set `σ² = cot(πs/2)/(2βπs)`. The process is stationary
with intensity one, and `PalmRegular P` holds. Every interval count `N_{(a,b]}`, for every
`a,b ∈ ℝ`, has a finite second moment under `P`. For every positive integer `K`, `z_K` has
a finite second moment under the Palm law. These variables are almost everywhere strongly
measurable. The following conclusions hold in this order:

1. Under `P`, `R^{-s/2}(N_{(0,R]}-R) → N(0,σ²)` in law as positive real `R → ∞`.
2. `R^{-s} Var_P[N_{(0,R]}] → σ²` as positive real `R → ∞`.
3. Under the Palm law, `K^{-s/2}(z_K-K) → N(0,σ²)` in law along `K = n+1 → ∞`.
4. `K^{-s} Var_{Riesz_{s,β}^0}[z_K] → σ²` along `K = n+1 → ∞`.
5. `Var_P[N_{(0,R]}]/R → 0` as positive real `R → ∞`.

Both convergence-in-law assertions include that all the displayed laws and their Gaussian
limit are probability measures.

**Proposition 1.2 (repulsion).** For every pair of parameters `β > 0`, `s > 0`, `s ≠ 1`,
there is a unique local limit `P = Riesz_{s,β}`, and `PalmRegular P` holds. There are `c, C > 0`
such that, for every `i ∈ ℤ` and every `u ∈ ℝ` with `0 < u ≤ 1`,

> `P_{Riesz_{s,β}^0}(z_{i+1}-z_i ≤ u) ≤ C exp(-c u^{-s})`.

## Standing assumptions and scope

1. **Parameters and constants.** `Parameters` contains precisely `β > 0`, `s > 0`, `s ≠ 1`.
   `Riesz1.RieszExponent` contains `0 < s < 1`, and `ShortExponent` contains `s > 1`.
   Theorem 1 and Corollary 1.1 concern the first range, and Theorem 2 the second. The other
   three results cover both. Constants have the quantifier order displayed above, so the six
   statements give constants for each fixed `β`. The paper's convention makes its constants
   locally uniform in `β`. The library proves these compact-temperature versions of Theorems 1,
   2 and 4 and Proposition 1.2:
   [`Riesz2.longRangeGapCorrelations_locallyUniform`](Riesz2/DecayLong/LongRangeLocallyUniform.lean),
   [`Riesz2.DecayShort.shortRangeGapCorrelations_locallyUniform`](Riesz2/DecayShort/ShortRangeLocallyUniform.lean),
   [`Riesz2.QuantitativeConvergenceResult.quantitativeConvergence_locallyUniform`](Riesz2/Thermodynamic/QuantitativeConvergenceResult.lean)
   and [`Riesz2.repulsion_locallyUniform`](Riesz2/Thermodynamic/RepulsionResult.lean). Except
   for the second, they take some of the literature inputs of item 8 as explicit arguments,
   which [`Riesz2/Frozen/External/`](Riesz2/Frozen/External/) proves.
2. **The finite model and labels.** The circle is Mathlib's `AddCircle 1`. A configuration is
   the ordered real lift `x_0 < ... < x_{N-1} < x_0+1` with `0 ≤ x_0 < 1`, imported from
   `Riesz1`. The paper's label 1 is label 0 in Lean. `Riesz1.cyclicLift` extends labels to all
   integers, and `gap X i = N(x_{i+1}-x_i)`, including the gap across the end of the cycle.
   The long-range Gibbs law is exactly the imported `Riesz1.gibbsMeasure`. Its kernel is twice
   the real part of Mathlib's even Hurwitz zeta function. Its assigned value at `0` is unused
   by the off-diagonal energy. For `s > 1`, `shortKernelLift` is the convergent sum
   `Σ_{k∈ℤ}|x+k|^{-s}` off the integer lattice. Both energies sum over ordered pairs. These
   definitions encode the kernel in the paper's limit formula.
3. **Observables.** `GapObservable` supplies a Lipschitz function and an almost everywhere
   derivative representative. This encodes the paper's locally absolutely continuous functions
   with bounded derivatives. `derivativeSup` uses the Lebesgue essential supremum, while the
   derivative's `L²` norm is taken under the actual gap law. Theorems 1 and 2 also cover `N = 1`,
   where the gap is constant and its covariance is zero. The paper states them for `N ≥ 2`.
   `BlockObservable K` contains all Lipschitz functions on `ℝ^K`, with the usual supremum metric
   on the finite product. Theorem 4 specifies each derivative norm by the least coordinate
   Lipschitz constant, rather than a chosen pointwise partial derivative.
4. **Point configurations and the microscopic law.** `LineConfiguration` is a locally finite
   subset of `ℝ`, so simplicity is built in. Its σ-algebra is generated by the counts in bounded
   Borel sets. The paper uses counts in all Borel sets, which give the same σ-algebra by bounded
   exhaustion. `PointProcess` is a Mathlib probability measure on this space. `microscopicLaw`
   retains particles whose centered circle representative lies in `(-1/4,1/4)`, multiplies their
   positions by `N`, and takes their law. The window is strict, as in the paper.
5. **Gap and Palm laws.** `gapLaw` is the pushforward of the ordered Gibbs law by the full
   vector of cyclic microscopic gaps (`gapVector`). Finite labelled gap blocks list the first
   `K` gaps using cyclic labels (`finiteGapBlock`). The Palm measure is defined by the Campbell
   formula: average the sum of the configurations `C-x` over particles `x ∈ C ∩ [0,1)`
   (`palmKernel`, `palmMeasure`). Its pullback to configurations containing `0` and unbounded in both directions
   is `rootedPalmMeasure`. `rootedPoint` enumerates these configurations with `z_0 = 0` using
   infima and suprema. `rootedGapBlock` consists of the first `K` gaps of this enumeration.
   The assertions in `PalmRegular`, including measurability of its carrier, normalization,
   two-sided support, index stationarity, integrability and mean one, are conclusions.
6. **Limits.** `UniqueRieszLimit` asserts existence and uniqueness among all point processes
   satisfying `LocalConverges`. `limitingRieszProcess` chooses this unique process after a proof
   of existence has been supplied. That proof is concluded in Theorems 3 and 4, Corollary 1.1
   and Proposition 1.2. Local convergence uses `sup_A |μ(A)-ν(A)|` on each window `[-R,R]` and
   the sequence `N = n+1`. A mesoscopic sequence is a map from positive integers to positive
   integers, with `n_N → ∞` and `n_N/N → 0`. Uniqueness concerns the point-process limit of the
   microscopic laws in local total variation. In Theorem 4 the bound on the positive integer
   `K` is a real inequality, equivalent to the paper's floor bound, and it excludes `N = 1`.
   Convergence in law is convergence of integrals of every bounded continuous real function.
   The count CLT uses all positive real radii, and the Palm CLT uses `K = n+1`.
7. **Total definitions and explicit conclusions.** Real-valued integrals, series and inverses
   are total. Non-integrable Bochner integrals and non-summable real series have conventional
   values, and `ENNReal.toReal ∞ = 0`. Partition functions, `L²` norms and variances are
   therefore first defined in `[0,∞]`. Their required finiteness is proved. Theorems 1 and 2 conclude the
   four second-moment and measurability assertions in `GapSecondMoments`, and the mesoscopic
   lower bound of Theorem 1 concludes them for the two selected gaps. Theorem 4 concludes
   integrability of both observables. Corollary 1.1 concludes all interval-count and positive
   Palm-span second moments before stating the CLTs and variance limits. It also explicitly
   concludes sublinear number variance. Finite-model measurability, positivity and finiteness of
   the partition functions, and normalization of the Gibbs laws are separate library theorems
   for every admissible parameter pair and positive particle number (`finiteModel_valid`,
   `gibbsMeasure_probability`, in
   [`Riesz2/Preliminaries/FiniteModelValidity.lean`](Riesz2/Preliminaries/FiniteModelValidity.lean)).
8. **Literature inputs and scope.** The companion library is imported, including its proved
   external results. Four further literature inputs are stated in
   [`Riesz2/Frozen/External/`](Riesz2/Frozen/External/) and proved in
   [`Riesz2/Main/External/`](Riesz2/Main/External/): the periodic-zeta connection formula,
   compact-temperature uniformity of the companion gap rigidity estimate, one-dimensional
   log-concave density and Poincaré bounds, and convergence of log-concave densities. The proofs
   of the six results use these proved versions. The paper's remarks on DLR equations and on
   the failure of number rigidity are not formalized.

## Guarantees

- **No `sorry` in the library.** The six comparator challenges under
  [`Riesz2Audit/`](Riesz2Audit/) each contain one intentional statement-level `sorry`, which the
  corresponding solution proves.
- **Standard axioms only.** The axiom report of each main result lists exactly `propext`,
  `Classical.choice` and `Quot.sound`.
  [`Riesz2/Meta/AxiomsAudit.lean`](Riesz2/Meta/AxiomsAudit.lean) prints the reports, and
  `scripts/check_axioms.py` rejects any other axiom, `sorryAx`, and missing or unexpected reports.
- **Builds from a clean checkout.** `lake build` of a fresh clone of this repository completed
  its 11,189 jobs with 0 warnings and no errors. Continuous integration rejects any warning. `scripts/check_sources.py` rejects `sorry`, `admit`, new axioms, `opaque`,
  `native_decide`, `implemented_by`, `extern`, kernel type-check bypasses, and heartbeat or
  recursion-depth overrides.
- **Independent statement comparisons.** Each main result has a Mathlib-only restatement under
  [`Riesz2Audit/`](Riesz2Audit/). Its definitions are copied from both frozen libraries. The
  solution proves the restatement from the library, and
  [leanprover/comparator](https://github.com/leanprover/comparator) compares the statements and
  their definitions and replays the solution with Lean, NanoDa and con-ron. See
  [`Riesz2Audit/README.md`](Riesz2Audit/README.md).
- **Statements checked before the proofs.** The statements and their definitions were written
  before the proofs and compared with the paper by independent refute-first audits, including
  blind back-translations into mathematics. [`Riesz2/Sanity/`](Riesz2/Sanity/) checks definitions
  against known values.
- **Pinned dependencies.** Lean and Mathlib `v4.35.0`, and `Riesz1` at
  `72fbdc2b2ea09a2ad64b8ae25074f30a3805b747`. Exact revisions are recorded in
  [`lake-manifest.json`](lake-manifest.json).

## Size

The library contains 742 Lean files with 242,409 physical lines, on top of Mathlib and the
imported companion library. The 18 comparator files under `Riesz2Audit/`, with 6,171 lines, are
not included in these counts.

## Building

Install [elan](https://github.com/leanprover/elan). The toolchain is pinned in
[`lean-toolchain`](lean-toolchain), and Lake fetches Mathlib and `Riesz1`.

```bash
lake exe cache get   # prebuilt mathlib
lake build
```

With Mathlib downloaded, a fresh build takes about 45 minutes on an Apple M4 with
10 cores.

To reproduce the axiom reports:

```bash
lake env lean Riesz2/Meta/AxiomsAudit.lean 2>&1 | tee .lake/axioms-audit.log
python3 scripts/check_axioms.py .lake/axioms-audit.log
```

`scripts/check_all.sh` runs the zero-warning build, the source sweep and the axiom report.

## Running the comparators

Each pair has a `Riesz2Audit/<Pair>/comparator.json` permitting exactly `propext`,
`Classical.choice` and `Quot.sound`. Each challenge and its solution import the same Mathlib-only
`Definitions.lean`. The solution additionally imports the library and proves the theorem
`by exact` the corresponding library theorem.

```bash
lake build Riesz2Audit           # the challenges and their solutions
./scripts/run_comparators.sh     # all six pairs, or name some pairs
```

The comparator builds inside a `bubblewrap` sandbox, which is available on Linux. On macOS,
`./scripts/run_comparators.sh --no-sandbox` runs the same checks without the sandbox. Logs are
kept under `.lake/comparator-logs/`. The runner adds the NanoDa and con-ron kernels bundled
with the toolchain.

**CI** builds the library, rejects warnings and checks the axiom reports. **Comparator audit**
checks the six pairs, one job per pair, after a successful build on `main`. Both workflows can
be started from the
[Actions page](https://github.com/jboursier/circular-riesz-gas-correlations-lean/actions).
See [`CONTRIBUTING.md`](CONTRIBUTING.md) for build conventions.

## Repository layout

```text
Riesz2.lean                 root module, importing the six main results
Riesz2/
  Frozen/                   main statements and the Riesz2 definitions they use
  Frozen/External/          the four further literature inputs and their proved anchors
  Main/                     proofs of the main results
  Main/External/            proofs of the four literature inputs
  Preliminaries/            kernels, Riesz matrices, gap coordinates and finite-model validity
  HelfferSjostrand/         Helffer–Sjöstrand equations, Brascamp–Lieb and well-posedness
  DecayShort/               short-range correlations
  DecayLong/                long-range correlations
  Thermodynamic/            local limits, gap comparison, fluctuations and repulsion
  Bridges/                  connections to the imported companion library
  ToMathlib/                results at Mathlib generality
  Sanity/                   checks of definitions against known values
  Meta/AxiomsAudit.lean     axiom reports, built but not imported by the root
Riesz2Audit/                six Mathlib-only definitions modules, challenges and solutions
scripts/                    source sweep, axiom check and comparator runner
.github/workflows/          build and comparator workflows
.lake/packages/Riesz1/      imported companion formalization, fetched by Lake
```

## How this was built

The Lean code was written with AI assistance under the direction of the author, who fixed the
statements to be formalized. OpenAI's GPT-6.1 Sol, through the Codex CLI, wrote the statements
and the proofs and audited the statements against the paper. Anthropic's Claude Haiku 5.5 made
blind back-translations of the statements and mechanical edits. Claude Opus 5.5 coordinated
the agents, reviewed their work and prepared this release through Claude Code. The revision of
the paper that this repository formalizes was prepared with GPT-6 Astra and Claude Opus 5.5.
Every proof is checked by the Lean kernel. The models, tooling and review status are disclosed
in [`formalization.yaml`](formalization.yaml), following the
[mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml) standard.

We thank Scott Armstrong for providing the skill files used for the formalization.

## Author and citation

The Lean development is by **Jeanne Boursier**. To cite it, use [`CITATION.cff`](CITATION.cff).

The author was supported by a grant from the Fondation CFM pour la Recherche and by the ERC
Advanced Grant LDRAM (ERC-2019-ADG 884584).

## License

The Lean development is licensed under the Apache License 2.0. See [`LICENSE`](LICENSE).
