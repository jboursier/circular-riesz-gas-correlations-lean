/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.EndpointCuspFourier
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The far-product envelope at a Fourier cusp

The Leibniz estimate and its truncated power integral in Step 1 of
Lemma 2.4. Constants precede the amplitude and the symbol,
and no derivative of the original symbol is taken at the seam.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped BigOperators ContDiff

namespace Riesz2.EndpointCuspFourier

open EndpointCuspCutoff

/-- Leibniz' rule gives the far-product envelope in Lemma 2.4,
Step 1, for every finite derivative order and every real cusp exponent. -/
theorem farPart_derivative_bound (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T a B α : ℝ), 0 < a → 4 * a ≤ T → 0 ≤ B →
      ∀ F : ℝ → ℂ, ContDiffOn ℝ r F (Ioo 0 T) →
      (∀ j : ℕ, j ≤ r → ∀ x ∈ Ioo 0 T,
        ‖iteratedDeriv j F x‖ ≤ B * (min x (T - x)) ^ (α - j)) →
      ∀ x ∈ Ioo 0 T, ‖iteratedDeriv r (farPart T a F) x‖ ≤
        C * B * (min x (T - x)) ^ (α - r) := by
  choose D hD hb using farCutoff_derivative_radius_bound
  let C := ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) * D i
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hD i).le)
  refine ⟨C + 1, by positivity, fun T a B α ha hTa hB F hF hbound x hx => ?_⟩
  let ρ := min x (T - x)
  have hρ : 0 < ρ := lt_min hx.1 (by linarith [hx.2])
  have hcut : ContDiffAt ℝ r (fun y => 1 - cutoff T a y) x :=
    (contDiff_const.sub ((cutoff_contDiff T a).of_le (by simp))).contDiffAt
  have hFs := hF.contDiffAt (isOpen_Ioo.mem_nhds hx)
  have he : iteratedDeriv r (farPart T a F) x =
      ∑ i ∈ Finset.range (r + 1),
        r.choose i • iteratedDeriv i (fun y => 1 - cutoff T a y) x •
          iteratedDeriv (r - i) F x := by
    change iteratedDeriv r ((fun y => 1 - cutoff T a y) • F) x = _
    simpa only [iteratedDerivWithin_univ] using
      iteratedDerivWithin_smul (mem_univ x) uniqueDiffOn_univ
        hcut.contDiffWithinAt hFs.contDiffWithinAt
  have hterm (i : ℕ) (hi : i ∈ Finset.range (r + 1)) :
      |iteratedDeriv i (fun y => 1 - cutoff T a y) x| *
          ‖iteratedDeriv (r - i) F x‖ ≤
        D i * B * ρ ^ (α - r) := by
    have hir : i ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    calc
      _ ≤ (D i / ρ ^ i) * (B * ρ ^ (α - (r - i : ℕ))) :=
        mul_le_mul (hb i T a ha hTa x hx) (hbound (r - i) (by omega) x hx)
          (norm_nonneg _) (div_nonneg (hD i).le (pow_nonneg hρ.le i))
      _ = D i * B * ρ ^ (α - r) := by
        rw [div_eq_mul_inv, ← Real.rpow_natCast, ← Real.rpow_neg hρ.le]
        rw [show D i * (ρ ^ (-(i : ℝ))) * (B * ρ ^ (α - (r - i : ℕ))) =
          D i * B * (ρ ^ (-(i : ℝ)) * ρ ^ (α - (r - i : ℕ))) by ring]
        rw [← Real.rpow_add hρ, Nat.cast_sub hir]
        congr 2
        ring
  rw [he]
  calc
    _ ≤ ∑ i ∈ Finset.range (r + 1),
        (r.choose i : ℝ) *
          (|iteratedDeriv i (fun y => 1 - cutoff T a y) x| *
            ‖iteratedDeriv (r - i) F x‖) := by
      apply (norm_sum_le _ _).trans_eq
      apply Finset.sum_congr rfl
      intro i _
      simp only [nsmul_eq_mul, norm_mul, Complex.norm_natCast, norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) *
        (D i * B * ρ ^ (α - r)) :=
      Finset.sum_le_sum (fun i hi =>
        mul_le_mul_of_nonneg_left (hterm i hi) (Nat.cast_nonneg _))
    _ = C * B * ρ ^ (α - r) := by
      dsimp only [C]
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intros
      ring
    _ ≤ (C + 1) * B * ρ ^ (α - r) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hB)
        (Real.rpow_nonneg hρ.le _)

/-- Integrating the negative power in Lemma 2.4, Step 1,
costs `a^(p+1)/(-p-1)` when `p < -1`. The upper-end contribution has the good sign. -/
theorem truncated_power_integral_bound {a b p : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hp : p < -1) :
    (∫ x in a..b, x ^ p) ≤ a ^ (p + 1) / (-p - 1) := by
  have hn : (0 : ℝ) ∉ uIcc a b := by
    rw [uIcc_of_le hab]
    intro h
    linarith [h.1]
  rw [integral_rpow (Or.inr ⟨by linarith, hn⟩)]
  have hden : 0 < -p - 1 := by linarith
  have hb : 0 ≤ b ^ (p + 1) := Real.rpow_nonneg (ha.le.trans hab) _
  have he : (b ^ (p + 1) - a ^ (p + 1)) / (p + 1) =
      (a ^ (p + 1) - b ^ (p + 1)) / (-p - 1) := by
    field_simp [show p + 1 ≠ 0 by linarith, show -p - 1 ≠ 0 by linarith]
    ring
  rw [he]
  exact div_le_div_of_nonneg_right (by linarith) hden.le

/-- Internal integration of a far-supported radius envelope in
Lemma 2.4, Step 1. All integrability comes from continuity
on the compact interval. The singular power is integrated only away from zero. -/
theorem integral_norm_le_far_envelope_internal {T a A p : ℝ}
    (ha : 0 < a) (hTa : 2 * a ≤ T) (hA : 0 ≤ A) (hp : p < -1)
    {G : ℝ → ℂ} (hG : ContinuousOn G (Icc 0 T))
    (hz : ∀ x ∈ Ioo 0 T, min x (T - x) < a → G x = 0)
    (hb : ∀ x ∈ Ioo 0 T, ‖G x‖ ≤ A * (min x (T - x)) ^ p) :
    ‖∫ x in (0 : ℝ)..T, G x‖ ≤ 2 * A * a ^ (p + 1) / (-p - 1) := by
  have hT : 0 < T := by linarith
  have hab : a ≤ T - a := by linarith
  have hsub : Icc a (T - a) ⊆ Icc 0 T := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hleft : (∫ x in (0 : ℝ)..a, G x) = 0 := by
    calc
      _ = ∫ x in (0 : ℝ)..a, (0 : ℂ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le ha.le
        intro x hx
        exact hz x ⟨hx.1, by linarith [hx.2]⟩
          ((min_le_left _ _).trans_lt hx.2)
      _ = 0 := by simp
  have hright : (∫ x in T - a..T, G x) = 0 := by
    calc
      _ = ∫ x in T - a..T, (0 : ℂ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
        intro x hx
        exact hz x ⟨by linarith [hx.1], hx.2⟩
          ((min_le_right _ _).trans_lt (by linarith [hx.1]))
      _ = 0 := by simp
  have hi (u v : ℝ) (hu : u ∈ Icc 0 T) (hv : v ∈ Icc 0 T) :
      IntervalIntegrable G volume u v :=
    (hG.mono (uIcc_subset_Icc hu hv)).intervalIntegrable
  have he : (∫ x in (0 : ℝ)..T, G x) = ∫ x in a..T - a, G x := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hi 0 a ⟨le_rfl, hT.le⟩ ⟨ha.le, by linarith⟩)
      (hi a T ⟨ha.le, by linarith⟩ ⟨hT.le, le_rfl⟩), hleft, zero_add]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hi a (T - a) ⟨ha.le, by linarith⟩ ⟨by linarith, by linarith⟩)
      (hi (T - a) T ⟨by linarith, by linarith⟩ ⟨hT.le, le_rfl⟩), hright, add_zero]
  have hpow : ContinuousOn (fun x : ℝ => x ^ p) (Icc a (T - a)) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt (ha.trans_le hx.1)))
  have hpowT : ContinuousOn (fun x : ℝ => (T - x) ^ p) (Icc a (T - a)) :=
    (continuous_const.sub continuous_id).continuousOn.rpow_const
      (fun x hx => Or.inl (ne_of_gt (show 0 < T - x by linarith [hx.2])))
  have hbi : IntervalIntegrable (fun x : ℝ => A * (x ^ p + (T - x) ^ p)) volume a (T - a) :=
    (continuousOn_const.mul (hpow.add hpowT)).intervalIntegrable_of_Icc hab
  have hbound (x : ℝ) (hx : x ∈ Icc a (T - a)) :
      ‖G x‖ ≤ A * (x ^ p + (T - x) ^ p) := by
    have hx0 : 0 < x := ha.trans_le hx.1
    have hxT : 0 < T - x := by linarith [hx.2]
    apply (hb x ⟨hx0, by linarith⟩).trans
    apply mul_le_mul_of_nonneg_left _ hA
    rcases le_total x (T - x) with hh | hh
    · rw [min_eq_left hh]
      exact le_add_of_nonneg_right (Real.rpow_nonneg hxT.le _)
    · rw [min_eq_right hh]
      exact le_add_of_nonneg_left (Real.rpow_nonneg hx0.le _)
  have hmono := intervalIntegral.integral_mono_on hab
    ((hG.mono hsub).norm.intervalIntegrable_of_Icc hab) hbi hbound
  have hreflect : (∫ x in a..T - a, (T - x) ^ p) = ∫ x in a..T - a, x ^ p := by
    simpa only [sub_sub_cancel] using
      intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ p) T (a := a) (b := T - a)
  rw [he]
  calc
    _ ≤ ∫ x in a..T - a, ‖G x‖ := intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ x in a..T - a, A * (x ^ p + (T - x) ^ p) := hmono
    _ = 2 * A * ∫ x in a..T - a, x ^ p := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
        (hpow.intervalIntegrable_of_Icc hab) (hpowT.intervalIntegrable_of_Icc hab), hreflect]
      ring
    _ ≤ 2 * A * (a ^ (p + 1) / (-p - 1)) :=
      mul_le_mul_of_nonneg_left (truncated_power_integral_bound ha hab hp) (by positivity)
    _ = _ := by ring

/-- The integrated highest far derivative in Lemma 2.4, Step 1.
This is the paper's power-envelope integration, with the two halves of the
period bounded by two reflected power integrals. -/
theorem far_integral_bound (r : ℕ) (α : ℝ) (hα : α < (r : ℝ) - 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T a B : ℝ), 0 < a → 4 * a ≤ T → 0 ≤ B →
      ∀ F : ℝ → ℂ, ContDiffOn ℝ r F (Ioo 0 T) →
      (∀ j : ℕ, j ≤ r → ∀ x ∈ Ioo 0 T,
        ‖iteratedDeriv j F x‖ ≤ B * (min x (T - x)) ^ (α - j)) →
      ∀ n : ℤ, ‖∫ x in (0 : ℝ)..T,
        iteratedDeriv r (farPart T a F) x *
          Complex.exp (-(n : ℂ) * Complex.I * (x : ℂ))‖ ≤
        C * B * a ^ (α - r + 1) := by
  obtain ⟨D, hD, hb⟩ := farPart_derivative_bound r
  have hdenpos : 0 < (r : ℝ) - α - 1 := by linarith
  refine ⟨2 * D / ((r : ℝ) - α - 1), div_pos (by positivity) hdenpos, ?_⟩
  intro T a B ha hTa hB F hF hbound n
  have h3 : 3 * a ≤ T := by linarith
  have hc : ContinuousOn (fun x => iteratedDeriv r (farPart T a F) x *
      Complex.exp (-(n : ℂ) * Complex.I * (x : ℂ))) (Icc 0 T) := by
    apply ContinuousOn.mul ?_ (by fun_prop)
    intro x hx
    exact (contDiffAt_iteratedDeriv (farPart_contDiffAt ha h3 hF hx)
      (by omega : 0 + r ≤ r)).continuousAt.continuousWithinAt
  have he := integral_norm_le_far_envelope_internal ha (by linarith : 2 * a ≤ T)
    (mul_nonneg hD.le hB) (by linarith : α - (r : ℝ) < -1) hc
    (fun x _ hx => by rw [farPart_derivative_eq_zero ha h3 F r hx, zero_mul])
    (fun x hx => by
      have hw : ‖Complex.exp (-(n : ℂ) * Complex.I * (x : ℂ))‖ = 1 := by
        rw [Complex.norm_exp]
        simp
      rw [norm_mul, hw, mul_one]
      exact hb T a B α ha hTa hB F hF hbound x hx)
  apply he.trans_eq
  have hden : -(α - (r : ℝ)) - 1 = (r : ℝ) - α - 1 := by ring
  rw [hden]
  ring

/-- Substituting `a = |n|⁻¹` in the smooth-cutoff split proves the nonzero
coefficient integral estimate in Lemma 2.4, Step 1. The
condition `α < r-1` includes `r = 3, α = 1`. -/
theorem integral_decay_of_endpoint_bounds (r : ℕ) (α : ℝ)
    (hα : 0 < α) (hαr : α < (r : ℝ) - 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 0 ≤ B → ∀ F : ℝ → ℂ,
      Continuous F → ContDiffOn ℝ r F (Ioo 0 (2 * Real.pi)) →
      (∀ x ∈ Icc 0 (2 * Real.pi),
        ‖F x‖ ≤ B * (min x (2 * Real.pi - x)) ^ α) →
      (∀ j : ℕ, j ≤ r → ∀ x ∈ Ioo 0 (2 * Real.pi),
        ‖iteratedDeriv j F x‖ ≤ B * (min x (2 * Real.pi - x)) ^ (α - j)) →
      ∀ n : ℤ, n ≠ 0 →
        ‖∫ x in (0 : ℝ)..(2 * Real.pi), F x *
          Complex.exp (-(n : ℂ) * Complex.I * (x : ℂ))‖ ≤
          C * B / |(n : ℝ)| ^ (1 + α) := by
  obtain ⟨D, hD, hb⟩ := far_integral_bound r α hαr
  refine ⟨4 * 2 ^ α + D, by positivity, fun B hB F hF hFs hF0 hbound n hn => ?_⟩
  let q := |(n : ℝ)|
  let a := q⁻¹
  have hq1 : 1 ≤ q := by
    dsimp only [q]
    exact_mod_cast Int.one_le_abs hn
  have hq : 0 < q := zero_lt_one.trans_le hq1
  have ha : 0 < a := inv_pos.mpr hq
  have ha1 : a ≤ 1 := (inv_le_one₀ hq).mpr hq1
  have hTa : 4 * a ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hs := near_far_integral_bound (by positivity) ha hTa hB hα hF hFs hF0 n hn
  have hf := hb (2 * Real.pi) a B ha hTa hB F hFs hbound n
  have hnear : 4 * a * (B * (2 * a) ^ α) =
      4 * 2 ^ α * B * a ^ (1 + α) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ha.le,
      Real.rpow_add ha, Real.rpow_one]
    ring
  have hfar : q⁻¹ ^ r * (D * B * a ^ (α - (r : ℝ) + 1)) =
      D * B * a ^ (1 + α) := by
    change a ^ r * (D * B * a ^ (α - (r : ℝ) + 1)) = _
    rw [← Real.rpow_natCast]
    calc
      _ = D * B * (a ^ (r : ℝ) * a ^ (α - (r : ℝ) + 1)) := by ring
      _ = _ := by rw [← Real.rpow_add ha]; congr 2; ring
  calc
    _ ≤ 4 * a * (B * (2 * a) ^ α) + q⁻¹ ^ r *
        (D * B * a ^ (α - (r : ℝ) + 1)) :=
      hs.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hf
        (show 0 ≤ q⁻¹ ^ r by positivity)))
    _ = (4 * 2 ^ α + D) * B * a ^ (1 + α) := by rw [hnear, hfar]; ring
    _ = (4 * 2 ^ α + D) * B / q ^ (1 + α) := by
      dsimp only [a]
      rw [Real.inv_rpow hq.le, div_eq_mul_inv]

end Riesz2.EndpointCuspFourier
