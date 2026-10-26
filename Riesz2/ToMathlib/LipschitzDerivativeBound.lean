/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Tactic

/-!
# Lipschitz bounds from an almost everywhere derivative bound

A Lipschitz function whose almost everywhere derivative is bounded by `U` in absolute value
satisfies `|f y - f x| ≤ U |y - x|`. The proof applies the fundamental theorem of calculus for
absolutely continuous functions on the interval between `x` and `y`. The essential supremum
form uses `eLpNorm _ ∞`, the definition of the derivative norm.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz2.LipschitzDerivative

/-- Ordered case of `abs_sub_le_of_ae_hasDerivAt_bound`. -/
private theorem abs_sub_le_of_le {f g : ℝ → ℝ} {L : NNReal} (hf : LipschitzWith L f)
    {U : ℝ} (hd : ∀ᵐ t ∂volume, HasDerivAt f (g t) t) (hU : ∀ᵐ t ∂volume, |g t| ≤ U)
    {x y : ℝ} (hxy : x ≤ y) : |f y - f x| ≤ U * |y - x| := by
  have hac : AbsolutelyContinuousOnInterval f x y :=
    (hf.lipschitzOnWith (s := uIcc x y)).absolutelyContinuousOnInterval
  have hFTC : ∫ t in x..y, deriv f t = f y - f x := hac.integral_deriv_eq_sub
  have hderiv : ∀ᵐ t ∂volume, t ∈ Ioc x y → deriv f t = g t :=
    hd.mono fun t ht _ => ht.deriv
  have hbound : ‖∫ t in Ioc x y, g t‖ ≤ U * (y - x) := by
    have h := norm_setIntegral_le_of_norm_le_const_ae' (μ := volume) (f := g)
      (s := Ioc x y) measure_Ioc_lt_top
      (hU.mono fun t ht _ => by rw [Real.norm_eq_abs]; exact ht)
    simpa only [Real.volume_real_Ioc_of_le hxy] using h
  have hyx : |y - x| = y - x := abs_of_nonneg (sub_nonneg.mpr hxy)
  rw [intervalIntegral.integral_of_le hxy] at hFTC
  rw [← hFTC, setIntegral_congr_ae measurableSet_Ioc hderiv, hyx, ← Real.norm_eq_abs]
  exact hbound

/-- A Lipschitz function whose almost everywhere derivative is bounded by `U` is
`U`-Lipschitz on the real line. -/
theorem abs_sub_le_of_ae_hasDerivAt_bound {f g : ℝ → ℝ} {L : NNReal} (hf : LipschitzWith L f)
    {U : ℝ} (hd : ∀ᵐ t ∂volume, HasDerivAt f (g t) t) (hU : ∀ᵐ t ∂volume, |g t| ≤ U)
    (x y : ℝ) : |f y - f x| ≤ U * |y - x| := by
  rcases le_total x y with hxy | hyx
  · exact abs_sub_le_of_le hf hd hU hxy
  · rw [abs_sub_comm (f y) (f x), abs_sub_comm y x]
    exact abs_sub_le_of_le hf hd hU hyx

/-- The essential supremum of the derivative, written with `eLpNorm _ ∞`, gives the
Lipschitz constant when it is finite. -/
theorem abs_sub_le_of_eLpNorm_top_hasDerivAt {f g : ℝ → ℝ} {L : NNReal}
    (hf : LipschitzWith L f) (hg : AEStronglyMeasurable g volume)
    (hfin : eLpNorm g ∞ volume < ⊤) (hd : ∀ᵐ t ∂volume, HasDerivAt f (g t) t)
    (x y : ℝ) : |f y - f x| ≤ (eLpNorm g ∞ volume).toReal * |y - x| := by
  apply abs_sub_le_of_ae_hasDerivAt_bound hf hd _ x y
  have hess := enorm_ae_le_eLpNormEssSup g volume
  rw [← eLpNorm_exponent_top hg] at hess
  filter_upwards [hess] with t ht
  rw [← ENNReal.ofReal_le_iff_le_toReal hfin.ne, ← Real.enorm_eq_ofReal_abs]
  exact ht

end Riesz2.LipschitzDerivative
