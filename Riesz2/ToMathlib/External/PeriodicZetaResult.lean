/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.External.PeriodicZeta
public import Riesz2.ToMathlib.External.OrderedCosineSeries

/-!
# Periodic-zeta connection formula

The ordered cosine-series limit is proved in `OrderedCosineSeries`.
The even Hurwitz-zeta functional equation gives the symmetrized identity
with its real Gamma prefactor.
-/

public section

noncomputable section

namespace Riesz2

/-- The periodic-zeta connection formula: the ordinary ordered cosine series
converges and satisfies the real periodic-zeta connection formula, with
exactly the parameters and normalization of the predicate. -/
theorem periodicZeta_result : External.PeriodicZeta := by
  intro s x hs0 hs1 hx0 hx1
  refine ⟨(HurwitzZeta.cosZeta (x : UnitAddCircle) (s : ℂ)).re,
    OrderedCosineSeries.tendsto_sum_cos_rpow s x hs0 hx0 hx1, ?_⟩
  have hsneg (n : ℕ) : (s : ℂ) ≠ -(n : ℂ) := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hr
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hsone : (s : ℂ) ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.one_re] at hr
    linarith
  have hfe := HurwitzZeta.hurwitzZetaEven_one_sub
    (x : UnitAddCircle) hsneg (Or.inr hsone)
  have hreflection : ((1 - x : ℝ) : UnitAddCircle) = -(x : UnitAddCircle) := by
    rw [AddCircle.coe_sub, AddCircle.coe_period, zero_sub]
  have hsymm :
      HurwitzZeta.hurwitzZeta (x : UnitAddCircle) ((1 - s : ℝ) : ℂ) +
        HurwitzZeta.hurwitzZeta ((1 - x : ℝ) : UnitAddCircle)
          ((1 - s : ℝ) : ℂ) =
      2 * HurwitzZeta.hurwitzZetaEven (x : UnitAddCircle) (1 - (s : ℂ)) := by
    rw [hreflection, Complex.ofReal_sub, Complex.ofReal_one,
      HurwitzZeta.hurwitzZetaEven_eq]
    ring
  have hp : (2 * (Real.pi : ℂ)) ^ (-(s : ℂ)) =
      (((2 * Real.pi) ^ (-s) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl
  have hc : Complex.cos ((Real.pi : ℂ) * (s : ℂ) / 2) =
      (Real.cos (Real.pi * s / 2) : ℂ) := by
    rw [Complex.ofReal_cos]
    push_cast
    rfl
  rw [hfe, hp, Complex.Gamma_ofReal, hc] at hsymm
  have hreal := congrArg Complex.re hsymm
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat,
    Complex.im_ofNat, mul_zero, zero_mul, sub_zero, add_zero] at hreal
  rw [Real.rpow_neg (by positivity)] at hreal
  rw [hreal]
  ring

end Riesz2
