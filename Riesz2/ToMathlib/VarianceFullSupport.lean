/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.Variance
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Support

/-!
# Positive variance forces full affine support

A probability whose nonzero linear functionals have positive centered second
moment cannot be concentrated on a proper affine subspace.
-/

public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace Riesz2

/-- Positive variances of all nonzero inner products imply full affine span of
support. The first moments are explicit, and the second moments may be infinite. -/
theorem affineSpan_support_eq_top_of_variance_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Q : ProbabilityMeasure E)
    (hi : ∀ a : E, Integrable (fun x => ⟪a, x⟫_ℝ) Q)
    (hv : ∀ a : E, a ≠ 0 → 0 < Riesz1.variance Q.toMeasure
      (fun x => ⟪a, x⟫_ℝ) (hi a)) :
    affineSpan ℝ Q.toMeasure.support = ⊤ := by
  let S := affineSpan ℝ Q.toMeasure.support
  have hsupp : ∀ᵐ x ∂Q.toMeasure, x ∈ Q.toMeasure.support := Q.toMeasure.support_mem_ae
  obtain ⟨z, hz⟩ := hsupp.exists
  have hzS : z ∈ S := subset_affineSpan ℝ _ hz
  apply (AffineSubspace.direction_eq_top_iff_of_nonempty ⟨z, hzS⟩).mp
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro a ha
  by_contra ha0
  have hconst : (fun x => ⟪a, x⟫_ℝ) =ᵐ[Q.toMeasure] (fun _ => ⟪a, z⟫_ℝ) := by
    filter_upwards [hsupp] with x hx
    have hdir := S.vsub_mem_direction (subset_affineSpan ℝ _ hx) hzS
    have hzero := S.direction.inner_left_of_mem_orthogonal hdir ha
    change ⟪a, x - z⟫_ℝ = 0 at hzero
    simpa only [inner_sub_right, sub_eq_zero] using hzero
  have hmean : (∫ x, ⟪a, x⟫_ℝ ∂Q) = ⟪a, z⟫_ℝ := by
    rw [integral_congr_ae hconst]
    simp
  have hzero : Riesz1.variance Q.toMeasure (fun x => ⟪a, x⟫_ℝ) (hi a) = 0 := by
    unfold Riesz1.variance
    rw [hmean]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [hconst] with x hx
    simp [hx]
  exact (ne_of_gt (hv a ha0)) hzero

end Riesz2
