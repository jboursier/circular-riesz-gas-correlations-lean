/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Independent draws conditional on a common base

Marginals and event domination for the explicit product of two Markov kernels.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Riesz2.CommonBaseKernel

variable {L X Y : Type*} [MeasurableSpace L] [MeasurableSpace X] [MeasurableSpace Y]
variable (κ : Kernel L X) (η : Kernel L Y) [IsMarkovKernel κ] [IsMarkovKernel η]
variable (ρ : Measure L)

/-- Independent conditional draws, integrated over their common base law. -/
def law : Measure (X × Y) := (κ ×ₖ η) ∘ₘ ρ

instance law_probability [IsProbabilityMeasure ρ] : IsProbabilityMeasure (law κ η ρ) := by
  unfold law
  infer_instance

/-- The first marginal is the first kernel mixed over the common base. -/
theorem fst_law : (law κ η ρ).fst = κ ∘ₘ ρ := by
  change ((κ ×ₖ η) ∘ₘ ρ).map Prod.fst = _
  rw [Measure.map_comp _ _ measurable_fst]
  rw [← Kernel.fst_eq, Kernel.fst_prod]

/-- The second marginal is the second kernel mixed over the common base. -/
theorem snd_law : (law κ η ρ).snd = η ∘ₘ ρ := by
  change ((κ ×ₖ η) ∘ₘ ρ).map Prod.snd = _
  rw [Measure.map_comp _ _ measurable_snd]
  rw [← Kernel.snd_eq, Kernel.snd_prod]

omit [IsMarkovKernel κ] in
/-- A dominated base law dominates every nonnegative conditional expectation.
The scalar and the reference measure may be infinite. -/
theorem comp_le_smul (μ : Measure L) (a : ℝ≥0∞) (hρ : ρ ≤ a • μ) :
    κ ∘ₘ ρ ≤ a • (κ ∘ₘ μ) := by
  rw [← Measure.comp_smul]
  apply Measure.le_iff.mpr
  intro E hE
  rw [Measure.bind_apply hE (Kernel.aemeasurable _),
    Measure.bind_apply hE (Kernel.aemeasurable _)]
  exact lintegral_mono' hρ le_rfl

/-- The probability of either bad coordinate event is bounded by the two
original marginal bad-event masses times the base-density domination factor. -/
theorem bad_event_le (μ ν : Measure L) (a : ℝ≥0∞)
    (hμ : ρ ≤ a • μ) (hν : ρ ≤ a • ν)
    (E : Set X) (F : Set Y) (hE : MeasurableSet E) (hF : MeasurableSet F) :
    law κ η ρ ((Prod.fst ⁻¹' E) ∪ (Prod.snd ⁻¹' F)) ≤
      a * (κ ∘ₘ μ) E + a * (η ∘ₘ ν) F := by
  apply (measure_union_le _ _).trans
  have h₁ : law κ η ρ (Prod.fst ⁻¹' E) = (κ ∘ₘ ρ) E := by
    rw [← fst_law κ η ρ, Measure.fst_apply hE]
  have h₂ : law κ η ρ (Prod.snd ⁻¹' F) = (η ∘ₘ ρ) F := by
    rw [← snd_law κ η ρ, Measure.snd_apply hF]
  rw [h₁, h₂]
  apply add_le_add
  · simpa only [Measure.smul_apply, smul_eq_mul] using (comp_le_smul κ ρ μ a hμ) E
  · simpa only [Measure.smul_apply, smul_eq_mul] using (comp_le_smul η ρ ν a hν) F

end Riesz2.CommonBaseKernel
