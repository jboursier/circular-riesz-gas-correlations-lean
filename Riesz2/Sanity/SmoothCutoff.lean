/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.PhysicalCutoff
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic

/-! # A concrete smooth cutoff from two primitives of the standard transition -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Interval
namespace Riesz2.DefinitionSanity

/-- The smooth curvature is zero below one half and one above one. -/
def cutoffCurvature (x : ℝ) : ℝ := Real.smoothTransition (2 * x - 1)

/-- Its primitive has zero initial value. -/
def cutoffSlope (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, cutoffCurvature t

/-- The cutoff is the second primitive, also with zero initial value. -/
def cutoffFunction (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, cutoffSlope t

theorem curvature_smooth : ContDiff ℝ (⊤ : ℕ∞) cutoffCurvature := by
  unfold cutoffCurvature
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

theorem slope_hasDeriv (x : ℝ) : HasDerivAt cutoffSlope (cutoffCurvature x) x := by
  exact intervalIntegral.integral_hasDerivAt_right
    (curvature_smooth.continuous.intervalIntegrable 0 x)
    (curvature_smooth.continuous.stronglyMeasurableAtFilter _ _)
    curvature_smooth.continuous.continuousAt

theorem slope_deriv : deriv cutoffSlope = cutoffCurvature := by
  funext x
  exact (slope_hasDeriv x).deriv

theorem slope_smooth : ContDiff ℝ (⊤ : ℕ∞) cutoffSlope := by
  apply contDiff_infty_iff_deriv.mpr
  exact ⟨fun x => (slope_hasDeriv x).differentiableAt, by rw [slope_deriv]; exact curvature_smooth⟩

theorem cutoff_hasDeriv (x : ℝ) : HasDerivAt cutoffFunction (cutoffSlope x) x := by
  exact intervalIntegral.integral_hasDerivAt_right
    (slope_smooth.continuous.intervalIntegrable 0 x)
    (slope_smooth.continuous.stronglyMeasurableAtFilter _ _)
    slope_smooth.continuous.continuousAt

theorem cutoff_deriv : deriv cutoffFunction = cutoffSlope := by
  funext x
  exact (cutoff_hasDeriv x).deriv

theorem cutoff_smooth : ContDiff ℝ (⊤ : ℕ∞) cutoffFunction := by
  apply contDiff_infty_iff_deriv.mpr
  exact ⟨fun x => (cutoff_hasDeriv x).differentiableAt, by rw [cutoff_deriv]; exact slope_smooth⟩

theorem cutoff_second_deriv : deriv (deriv cutoffFunction) = cutoffCurvature := by
  rw [cutoff_deriv, slope_deriv]

theorem curvature_nonneg (x : ℝ) : 0 ≤ cutoffCurvature x := Real.smoothTransition.nonneg _

theorem curvature_le_one (x : ℝ) : cutoffCurvature x ≤ 1 := Real.smoothTransition.le_one _

theorem curvature_one (x : ℝ) (hx : 1 ≤ x) : cutoffCurvature x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith

theorem slope_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ cutoffSlope x := by
  exact intervalIntegral.integral_nonneg_of_forall hx curvature_nonneg

theorem cutoff_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ cutoffFunction x := by
  apply intervalIntegral.integral_nonneg hx
  intro t ht
  exact slope_nonneg t ht.1

theorem slope_zero (x : ℝ) (hx : x ∈ Icc (0 : ℝ) (1 / 2)) : cutoffSlope x = 0 := by
  apply intervalIntegral.integral_zero_ae
  apply ae_of_all
  intro t ht
  apply Real.smoothTransition.zero_of_nonpos
  have ht' : t ∈ Ioc (0 : ℝ) x := by simpa [uIoc_of_le hx.1] using ht
  linarith [ht'.2, hx.2]

theorem cutoff_zero (x : ℝ) (hx : x ∈ Icc (0 : ℝ) (1 / 2)) : cutoffFunction x = 0 := by
  apply intervalIntegral.integral_zero_ae
  apply ae_of_all
  intro t ht
  have ht' : t ∈ Ioc (0 : ℝ) x := by simpa [uIoc_of_le hx.1] using ht
  exact slope_zero t ⟨ht'.1.le, ht'.2.trans hx.2⟩

theorem cutoff_convex : ConvexOn ℝ (Ici (0 : ℝ)) cutoffFunction := by
  apply convexOn_of_deriv2_nonneg (convex_Ici 0) cutoff_smooth.continuous.continuousOn
    (cutoff_smooth.differentiable (by norm_num)).differentiableOn
  · rw [cutoff_deriv]
    exact (slope_smooth.differentiable (by norm_num)).differentiableOn
  · intro x _
    change 0 ≤ deriv (deriv cutoffFunction) x
    rw [cutoff_second_deriv]
    exact curvature_nonneg x

/-- The cutoff carrier contains an actual nonanalytic smooth cutoff. -/
theorem physicalCutoff_nonempty : Nonempty PhysicalCutoff := by
  refine ⟨⟨cutoffFunction, cutoff_smooth.contDiffOn, cutoff_convex,
    fun x hx => cutoff_nonneg x hx, cutoff_zero, 1, le_rfl, ?_, ?_⟩⟩
  · intro x _
    rw [cutoff_second_deriv]
    exact ⟨curvature_nonneg x, curvature_le_one x⟩
  · intro x hx
    rw [cutoff_second_deriv, curvature_one x hx]

end Riesz2.DefinitionSanity
end
end
