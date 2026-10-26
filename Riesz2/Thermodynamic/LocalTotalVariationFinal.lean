/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.LocalTotalVariationPart2
public import Riesz2.Thermodynamic.GapNondegeneracyPart2
public import Riesz2.Thermodynamic.GapNondegeneracyPart3
public import Riesz2.Thermodynamic.LimitDensity
public import Riesz2.Thermodynamic.GapTotalVariation

/-!
# Local total variation from ordinary-gap Cauchy estimates

The composition in the proof of Theorem 3 assumes the ordinary-gap Cauchy estimate and
log-concave density convergence.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace Riesz2

local notation "Gaps" => (ℤ → Ioi (0 : ℝ))
local instance localTotalVariationFinalConfigurationMeasurableSpace :
    MeasurableSpace LineConfiguration := configurationMeasurableSpace

/-- See the proof of Theorem 3 in the paper: the suspension of the
unique gap limit is a local total variation limit of the actual microscopic laws.
The hypotheses are the ordinary-gap Cauchy estimate and log-concave
density convergence. -/
theorem convergence_local_total_variation_from_cauchy_internal
    (hcomparison :
      ∀ (p : Parameters) (ζ : ℝ), 0 < ζ → ∃ C : ℝ, 0 < C ∧
        ∀ (n N N' : ℕ+) (_ : 2 ≤ (n : ℕ)),
          (N : ℕ) ≤ (N' : ℕ) → 4 * (n : ℕ) ≤ (N : ℕ) →
          (n : ℝ) ^ (2 / p.val.2) ≤ (N : ℝ) →
          ∀ (G : BlockObservable n) (J : Finset (Fin (n : ℕ))),
            MiddleConsecutiveBlock n J → DependsOnBlockCoordinates G J →
            Integrable (fun X : Riesz1.Configuration N => G.val (finiteGapBlock X))
              (gibbsMeasure p N) ∧
            Integrable (fun X : Riesz1.Configuration N' => G.val (finiteGapBlock X))
              (gibbsMeasure p N') ∧
            |(∫ X : Riesz1.Configuration N, G.val (finiteGapBlock X) ∂gibbsMeasure p N) -
              (∫ X : Riesz1.Configuration N', G.val (finiteGapBlock X) ∂gibbsMeasure p N')| ≤
              C * (n : ℝ) ^ (-min p.val.2 1 / 2 + ζ) * blockDerivativeNorm G)
    (hconvergence : External.LogConcaveConvergence) (p : Parameters) :
    ∃! q : ProbabilityMeasure Gaps,
      Tendsto (fun n : ℕ => periodicGapLaw p n.succPNat) atTop (𝓝 q) ∧
      ∃ P : PointProcess,
        (P : Measure LineConfiguration) =
          gapSuspensionMeasure (reconstructionGapMeasure q.toMeasure) ∧
        LocalConverges (microscopicLaw p) P := by
  obtain ⟨q, hq, _⟩ := convergence_gap_limit_from_cauchy_internal hcomparison p
  obtain ⟨q', hq', _⟩ := convergence_gap_total_variation_from_predecessors_internal
    hcomparison
    (by
      intro p q hq k hk
      simpa only [zero_add] using
        GapNondegeneracy.block_nondegeneracy_from_finite_internal
          GapNondegeneracy.finite_gibbs_covariance_lower_bound p q hq k hk)
    convergence_limit_density hconvergence p
  have heq : q' = q := tendsto_nhds_unique hq'.1 hq.1
  subst q'
  have hs : ∀ᵐ y ∂q.toMeasure, y ∈ reconstructibleGapSequences :=
    hq.2.2.2.2.2.2.mono fun y hy =>
      mem_reconstructibleGapSequences_of_divergent_sums y hy.1 hy.2
  have := reconstructionGapMeasure_probability q.toMeasure hs
  have hm := reconstructionGapMeasure_mean q.toMeasure hs 0 (hq.2.2.1 0).1 (hq.2.2.1 0).2
  let P := gapSuspensionProcess (reconstructionGapMeasure q.toMeasure) hm.1 hm.2
  refine ⟨q, ⟨hq.1, P, rfl, ?_⟩, fun q' hh => tendsto_nhds_unique hh.1 hq.1⟩
  refine ⟨microscopicLaw_probability p, ?_⟩
  intro R _hR
  have hTV := convergence_local_total_variation_from_gap_predecessors_internal
    p q hq.1 hs (hq.2.2.1 0) (fun m hm =>
      ((hq'.2 (2 * m) (-(m : ℤ))).2.2.2 ⟨m, by omega⟩).2) R
  exact hTV

end Riesz2
