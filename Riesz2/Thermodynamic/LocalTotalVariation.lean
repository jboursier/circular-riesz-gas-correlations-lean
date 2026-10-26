/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.LocalReconstruction
public import Riesz2.Thermodynamic.GapTotalVariation
public import Riesz2.ToMathlib.WeightedTestVariation

/-!
# Local total variation: weighted finite-block tests

Analytic steps in the proof of Theorem 3, using the Euclidean block projection of the
gap total variation convergence result.
-/

public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Riesz2

local notation "Gaps" => (ℤ → Ioi (0 : ℝ))
local notation "gapProj" => (fun (k : ℕ) (a : ℤ) (y : Gaps) =>
  (WithLp.toLp 2 (fun j : Fin k => (y (a + (Fin.val j : ℤ)) : ℝ)) : EuclideanSpace ℝ (Fin k)))
local notation "gapMarginal" => (fun (q : ProbabilityMeasure Gaps) (k : ℕ) (a : ℤ) =>
  ProbabilityMeasure.map q (gapProj k a))

/-- See the proof of Theorem 3 in the paper, integrability of the
finite-block tests bounded by the distinguished gap. Integrability follows from weak gap convergence and moment transfer. -/
theorem gap_block_dominated_tests_integrable_from_gap_limit_internal
    (p : Parameters) (q : ProbabilityMeasure Gaps)
    (hq : Tendsto (fun n : ℕ => periodicGapLaw p n.succPNat) atTop (𝓝 q))
    (k : ℕ) (a : ℤ) (i : Fin k)
    (H : EuclideanSpace ℝ (Fin k) → ℝ) (hH : Measurable H)
    (hb : ∀ x, |H x| ≤ |x i|) :
    (∀ N : ℕ+, Integrable H (gapMarginal (periodicGapLaw p N) k a)) ∧
      Integrable H (gapMarginal q k a) := by
  let V : ℕ → ℕ+ := fun n => (n + 1).succPNat
  have hV : ∀ n, 2 ≤ (V n : ℕ) := by intro n; simp [V]
  have hqV : Tendsto (fun n => periodicGapLaw p (V n)) atTop (𝓝 q) :=
    (tendsto_add_atTop_iff_nat 1).mpr hq
  obtain ⟨D, _, hfinite, hlimit⟩ := periodicGapLaw_limit_all_moments p V hV q hqV 2 (by norm_num)
  have hi (μ : ProbabilityMeasure Gaps)
      (hm : (∫⁻ y : Gaps, ENNReal.ofReal ((y (a + (i.val : ℤ)) : ℝ) ^ (2 : ℝ)) ∂μ) ≤
        ENNReal.ofReal D) : Integrable H (gapMarginal μ k a) := by
    have hy := (gapCoordinate_memLp_two_internal μ (a + (i.val : ℤ))
      (hm.trans_lt ENNReal.ofReal_lt_top)).integrable (by norm_num)
    exact integrable_of_abs_le_weight
      (integrable_gap_block_coordinate_internal μ k a i hy) hH hb
  exact ⟨fun N => hi _ ((le_add_right le_rfl).trans (hfinite N _)),
    hi _ ((le_add_right le_rfl).trans (hlimit _))⟩

/-- See the proof of Theorem 3 in the paper, the uniform
finite-block-test step. The premise is exactly the weighted convergence clause
of the proof of Theorem 3, at the block and coordinate used.
It controls every measurable reconstruction integral bounded by that gap. -/
theorem gap_block_dominated_tests_tendsto_from_weighted_predecessor_internal
    (p : Parameters) (q : ProbabilityMeasure Gaps) (k : ℕ) (a : ℤ) (i : Fin k)
    (hweighted : Tendsto (fun n : ℕ =>
      ⨆ F : {F : EuclideanSpace ℝ (Fin k) → ℝ // Measurable F ∧ ∀ x, |F x| ≤ 1},
        ENNReal.ofReal |(∫ x, x i * F.val x ∂gapMarginal (periodicGapLaw p n.succPNat) k a) -
          (∫ x, x i * F.val x ∂gapMarginal q k a)|) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      ⨆ H : {H : EuclideanSpace ℝ (Fin k) → ℝ // Measurable H ∧ ∀ x, |H x| ≤ |x i|},
        ENNReal.ofReal |(∫ x, H.val x ∂gapMarginal (periodicGapLaw p n.succPNat) k a) -
          (∫ x, H.val x ∂gapMarginal q k a)|) atTop (𝓝 0) :=
  dominated_testSup_tendsto_of_weightedTestSup_tendsto
    (fun n => (gapMarginal (periodicGapLaw p n.succPNat) k a).toMeasure)
    (gapMarginal q k a).toMeasure (fun x => x i) (by fun_prop) hweighted

end Riesz2
