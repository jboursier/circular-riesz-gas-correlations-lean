/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Probability.Moments.Covariance
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Covariance bounded by centered second moments

This formulation retains the finite centered second moments explicitly,
as needed for the density-defined conditional physical forces.
-/

public section
noncomputable section

open MeasureTheory ProbabilityTheory

namespace Riesz2.CovarianceCauchySchwarz

/-- Cauchy--Schwarz for covariance, with finite second moments as premises.
No totalized variance or nonintegrable signed integral enters the bound. -/
theorem abs_covariance_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    |cov[X, Y; μ]| ≤
      Real.sqrt (∫ x, (X x - ∫ w, X w ∂μ) ^ 2 ∂μ) *
        Real.sqrt (∫ x, (Y x - ∫ w, Y w ∂μ) ^ 2 ∂μ) := by
  have hXc := hX.sub (memLp_const (∫ w, X w ∂μ))
  have hYc := hY.sub (memLp_const (∫ w, Y w ∂μ))
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all μ fun x => abs_nonneg (X x - ∫ w, X w ∂μ))
    (ae_of_all μ fun x => abs_nonneg (Y x - ∫ w, Y w ∂μ))
    (by rw [ENNReal.ofReal_ofNat]; exact hXc.abs)
    (by rw [ENNReal.ofReal_ofNat]; exact hYc.abs)
  apply abs_integral_le_integral_abs.trans
  simpa only [Pi.sub_apply, Real.rpow_two, sq_abs,
    Real.sqrt_eq_rpow, abs_mul] using hCS

end Riesz2.CovarianceCauchySchwarz
