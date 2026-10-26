/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.VarianceThreeTerm
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Moment passage for extended variances

The proof of Corollary 1.1 uses the extended variance.
The companion library identifies its real value after square integrability
has been established. Convergence of first and second moments then gives
convergence both in the real numbers and in the extended nonnegative reals.
-/

public section
noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Riesz2

/-- The companion extended variance agrees with the difference of the first
two moments, after its square-integrability hypotheses are supplied. -/
theorem variance_toReal_eq_second_sub_sq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → ℝ) (hF : MemLp F 2 μ) :
    (Riesz1.variance μ F (hF.integrable one_le_two)).toReal =
      (∫ x, F x ^ 2 ∂μ) - (∫ x, F x ∂μ) ^ 2 := by
  rw [Riesz1.variance_toReal_of_memLp μ hF,
    ← ProbabilityTheory.variance_eq_integral hF.aemeasurable,
    ProbabilityTheory.variance_eq_sub hF]
  rfl

/-- See the proof of Corollary 1.1 in the paper, fixed-window variance passage.
All variables have second moments. The extended variance cannot
acquire an infinite junk value in the passage through `toReal`. -/
theorem variance_tendsto_of_first_second_moments
    {ι Ω' : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] [MeasurableSpace Ω']
    {l : Filter ι} (μ : (i : ι) → Measure (Ω i)) (ν : Measure Ω')
    [∀ i, IsProbabilityMeasure (μ i)] [IsProbabilityMeasure ν]
    (F : (i : ι) → Ω i → ℝ) (G : Ω' → ℝ)
    (hF : ∀ i, MemLp (F i) 2 (μ i)) (hG : MemLp G 2 ν)
    (hfirst : Tendsto (fun i => ∫ x, F i x ∂μ i) l (𝓝 (∫ x, G x ∂ν)))
    (hsecond : Tendsto (fun i => ∫ x, F i x ^ 2 ∂μ i) l (𝓝 (∫ x, G x ^ 2 ∂ν))) :
    Tendsto (fun i => (Riesz1.variance (μ i) (F i) ((hF i).integrable one_le_two)).toReal)
      l (𝓝 (Riesz1.variance ν G (hG.integrable one_le_two)).toReal) ∧
    Tendsto (fun i => Riesz1.variance (μ i) (F i) ((hF i).integrable one_le_two))
      l (𝓝 (Riesz1.variance ν G (hG.integrable one_le_two))) := by
  have ht : Tendsto
      (fun i => (Riesz1.variance (μ i) (F i) ((hF i).integrable one_le_two)).toReal)
      l (𝓝 (Riesz1.variance ν G (hG.integrable one_le_two)).toReal) := by
    simp only [variance_toReal_eq_second_sub_sq _ _ (hF _),
      variance_toReal_eq_second_sub_sq _ _ hG]
    exact hsecond.sub (hfirst.pow 2)
  refine ⟨ht, ?_⟩
  have ht' := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht
  simpa only [Function.comp_def,
    ENNReal.ofReal_toReal (Riesz1.variance_ne_top_of_memLp _ hG),
    ENNReal.ofReal_toReal (Riesz1.variance_ne_top_of_memLp _ (hF _))] using ht'

end Riesz2
