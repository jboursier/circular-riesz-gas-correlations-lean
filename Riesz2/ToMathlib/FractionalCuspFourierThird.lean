/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.FractionalCuspFourier
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Fourier decay for a cusp of order between one and two

The order-three oscillatory estimate needed for the increment clause of
the proof of Lemma 5.13, proved by the smooth-cutoff
coefficient estimate of Lemma 2.4.
-/

public section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz2.FractionalCuspFourier

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The order-three coefficient bound of Lemma 2.4, via the
smooth seam cutoff at cusp order `1 + η`. -/
theorem third_order_coefficient_decay {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 < A →
      ∀ H : C(AddCircle (2 * Real.pi), ℂ), H 0 = 0 →
      ContDiffOn ℝ 3 (fun x : ℝ => H (x : AddCircle (2 * Real.pi)))
        (Ioo 0 (2 * Real.pi)) →
      (∀ j : ℕ, j ≤ 3 → ∀ x ∈ Ioo (0 : ℝ) (2 * Real.pi),
        ‖iteratedDeriv j (fun t : ℝ => H (t : AddCircle (2 * Real.pi))) x‖ ≤
          A * (min x (2 * Real.pi - x)) ^ (1 + η - (j : ℝ))) →
      ∀ n : ℤ, ‖fourierCoeff H n‖ ≤ K * A / (1 + |(n : ℝ)| ^ (2 + η)) := by
  obtain ⟨K, hK, hb⟩ := fourierCoeff_decay_of_endpoint_bounds 3 (1 + η)
    (by linarith) (by norm_num; linarith)
  refine ⟨2 * K, by positivity, fun A hA H hH0 hHs hHb n => ?_⟩
  have hh := hb A hA H hH0 hHs hHb n
  rw [show 1 + (1 + η) = 2 + η by ring] at hh
  have hd := (cusp_denominator_comparison (abs_nonneg (n : ℝ))
    (show 0 ≤ 2 + η by linarith)).1
  calc
    _ ≤ K * A / (1 + |(n : ℝ)|) ^ (2 + η) := hh
    _ = (2 * K * A) / (2 * (1 + |(n : ℝ)|) ^ (2 + η)) := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hd

/-- Multiplication by the negative first character gives the forward difference
of the existing negative-sign Fourier coefficients. -/
theorem coefficient_forward_difference (H : C(AddCircle (2 * Real.pi), ℂ)) (n : ℤ) :
    fourierCoeff (fun x => (fourier (-1) x - 1) * H x) n =
      fourierCoeff H (n + 1) - fourierCoeff H n := by
  have hi : Integrable (fun x : AddCircle (2 * Real.pi) =>
      fourier (-(n + 1)) x * H x) AddCircle.haarAddCircle := by
    simpa only [smul_eq_mul] using (H.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).fourier_smul (-(n + 1))
  have hj : Integrable (fun x : AddCircle (2 * Real.pi) =>
      fourier (-n) x * H x) AddCircle.haarAddCircle := by
    simpa only [smul_eq_mul] using (H.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).fourier_smul (-n)
  simp only [fourierCoeff, smul_eq_mul]
  rw [← integral_sub hi hj]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [show -(n + 1) = -n + -1 by ring, fourier_add]
  ring

/-- The angular negative first character vanishes to first order at either
endpoint of the period. -/
theorem first_character_sub_one_bound {x : ℝ} (hx : x ∈ Ioo 0 (2 * Real.pi)) :
    ‖fourier (-1) (x : AddCircle (2 * Real.pi)) - 1‖ ≤
      min x (2 * Real.pi - x) := by
  have hl : ‖fourier (-1) (x : AddCircle (2 * Real.pi)) - 1‖ ≤ x := by
    rw [fourier_angular]
    convert Real.norm_exp_I_mul_ofReal_sub_one_le (x := -x) using 1 <;>
      simp only [Int.cast_neg, Int.cast_one, Complex.ofReal_neg, neg_mul, mul_one,
        mul_neg, Real.norm_eq_abs, abs_neg, abs_of_pos hx.1]
  have he : fourier (-1) (x : AddCircle (2 * Real.pi)) =
      Complex.exp (Complex.I * ((2 * Real.pi - x : ℝ) : ℂ)) := by
    have hco : (x : AddCircle (2 * Real.pi)) =
        -((2 * Real.pi - x : ℝ) : AddCircle (2 * Real.pi)) := by
      simp only [AddCircle.coe_sub, AddCircle.coe_period, zero_sub, neg_neg]
    rw [hco]
    have hh : fourier (-1) (-((2 * Real.pi - x : ℝ) : AddCircle (2 * Real.pi))) =
        fourier 1 ((2 * Real.pi - x : ℝ) : AddCircle (2 * Real.pi)) := by
      simp only [fourier_apply, neg_smul, neg_neg, one_smul]
    rw [hh, fourier_angular]
    simp
  apply le_min hl
  rw [he]
  simpa only [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hx.2)] using
    Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2 * Real.pi - x)

/-- All positive angular derivatives of the negative first character have
unit norm. -/
theorem first_character_derivative_norm (j : ℕ) (hj : 0 < j) (x : ℝ) :
    ‖iteratedDeriv j
      (fun t : ℝ => fourier (-1) (t : AddCircle (2 * Real.pi)) - 1) x‖ = 1 := by
  let w := fun t : ℝ => Complex.exp (-Complex.I * (t : ℂ))
  have hw (t : ℝ) : HasDerivAt w (-Complex.I * w t) t := by
    simpa only [w, Int.cast_one, neg_mul, one_mul] using hasDerivAt_oscillation 1 t
  have hd : ∀ j : ℕ, iteratedDeriv j w = fun t => (-Complex.I) ^ j * w t := by
    intro j
    induction j with
    | zero => simp only [iteratedDeriv_zero, pow_zero, one_mul]
    | succ j ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      rw [((hw t).const_mul ((-Complex.I) ^ j)).deriv, pow_succ]
      ring
  have he : (fun t : ℝ => fourier (-1) (t : AddCircle (2 * Real.pi)) - 1) =
      fun t => -1 + w t := by
    funext t
    rw [fourier_angular]
    simp only [Int.cast_neg, Int.cast_one, mul_neg, mul_one]
    dsimp only [w]
    ring
  rw [he, iteratedDeriv_const_add hj, hd, norm_mul, norm_pow,
    norm_neg, Complex.norm_I, one_pow, one_mul]
  simpa only [w, Int.cast_one, neg_mul, one_mul] using norm_oscillation 1 x

/-- Multiplication by a factor with a simple endpoint zero increases the
cusp order by one. This finite-order product estimate is uniform in the
amplitude. -/
theorem simple_zero_product_bounds {η A : ℝ} (hA : 0 ≤ A) {E F : ℝ → ℂ}
    (hE : ContDiffOn ℝ 3 E (Ioo 0 (2 * Real.pi)))
    (hF : ContDiffOn ℝ 3 F (Ioo 0 (2 * Real.pi)))
    (hE0 : ∀ x ∈ Ioo (0 : ℝ) (2 * Real.pi), ‖E x‖ ≤ min x (2 * Real.pi - x))
    (hEd : ∀ j : ℕ, 0 < j → j ≤ 3 → ∀ x ∈ Ioo (0 : ℝ) (2 * Real.pi),
      ‖iteratedDeriv j E x‖ ≤ 1)
    (hFb : ∀ j : ℕ, j ≤ 3 → ∀ x ∈ Ioo (0 : ℝ) (2 * Real.pi),
      ‖iteratedDeriv j F x‖ ≤ A * (min x (2 * Real.pi - x)) ^ (η - (j : ℝ))) :
    ∀ j : ℕ, j ≤ 3 → ∀ x ∈ Ioo (0 : ℝ) (2 * Real.pi),
      ‖iteratedDeriv j (fun t => E t * F t) x‖ ≤
        (8 * (1 + Real.pi) ^ (3 : ℕ) * A) *
          (min x (2 * Real.pi - x)) ^ (1 + η - (j : ℝ)) := by
  intro j hj x hx
  let r := min x (2 * Real.pi - x)
  have hr : 0 < r := lt_min hx.1 (by linarith [hx.2])
  have hrπ : r ≤ 1 + Real.pi := by
    have h1 := min_le_left x (2 * Real.pi - x)
    have h2 := min_le_right x (2 * Real.pi - x)
    dsimp [r]
    linarith only [h1, h2]
  let P := (1 + Real.pi) ^ (3 : ℕ)
  have hP : 1 ≤ P := one_le_pow₀ (by linarith [Real.pi_pos])
  have hterm : ∀ i ∈ Finset.range (j + 1),
      ‖iteratedDeriv i E x‖ * ‖iteratedDeriv (j - i) F x‖ ≤
        P * A * r ^ (1 + η - (j : ℝ)) := by
    intro i hi
    have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    by_cases hi0 : i = 0
    · subst i
      simp only [iteratedDeriv_zero, Nat.sub_zero]
      calc
        _ ≤ r * (A * r ^ (η - (j : ℝ))) :=
          mul_le_mul (hE0 x hx) (hFb j hj x hx) (norm_nonneg _) (by positivity)
        _ = A * r ^ (1 + η - (j : ℝ)) := by
          rw [show 1 + η - (j : ℝ) = 1 + (η - (j : ℝ)) by ring,
            Real.rpow_add hr, Real.rpow_one]
          ring
        _ ≤ _ := by
          have hm := mul_le_mul_of_nonneg_right hP
            (show 0 ≤ A * r ^ (1 + η - (j : ℝ)) by positivity)
          nlinarith only [hm]
    · have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
      have him : (j - i : ℕ) ≤ 3 := by omega
      have hpow : r ^ ((i : ℝ) - 1) ≤ P := by
        calc
          _ ≤ (1 + Real.pi) ^ ((i : ℝ) - 1) := Real.rpow_le_rpow hr.le hrπ (by
            have hh : (1 : ℝ) ≤ i := by exact_mod_cast hi1
            linarith only [hh])
          _ ≤ (1 + Real.pi) ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le
            (by linarith [Real.pi_pos]) (by
              have hh : (i : ℝ) ≤ 3 := by exact_mod_cast hij.trans hj
              linarith only [hh])
          _ = _ := by norm_num only [Real.rpow_ofNat]; rfl
      have he : r ^ (η - ((j - i : ℕ) : ℝ)) =
          r ^ (1 + η - (j : ℝ)) * r ^ ((i : ℝ) - 1) := by
        rw [← Real.rpow_add hr, Nat.cast_sub hij]
        congr 1
        ring
      calc
        _ ≤ 1 * (A * r ^ (η - ((j - i : ℕ) : ℝ))) :=
          mul_le_mul (hEd i (Nat.pos_of_ne_zero hi0) (hij.trans hj) x hx)
            (hFb (j - i) him x hx) (norm_nonneg _) (by positivity)
        _ ≤ _ := by
          rw [one_mul, he]
          have hm := mul_le_mul_of_nonneg_left hpow
            (show 0 ≤ A * r ^ (1 + η - (j : ℝ)) by positivity)
          nlinarith only [hm]
  have hEs : ContDiffAt ℝ j E x :=
    (hE.contDiffAt (isOpen_Ioo.mem_nhds hx)).of_le (by exact_mod_cast hj)
  have hFs : ContDiffAt ℝ j F x :=
    (hF.contDiffAt (isOpen_Ioo.mem_nhds hx)).of_le (by exact_mod_cast hj)
  rw [iteratedDeriv_fun_mul hEs hFs]
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * (‖iteratedDeriv i E x‖ * ‖iteratedDeriv (j - i) F x‖) := by
      apply (norm_sum_le _ _).trans_eq
      apply Finset.sum_congr rfl
      intro i _
      simp only [norm_mul, Complex.norm_natCast, mul_assoc]
    _ ≤ ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * (P * A * r ^ (1 + η - (j : ℝ))) :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hterm i hi) (Nat.cast_nonneg _))
    _ = (2 : ℝ) ^ j * (P * A * r ^ (1 + η - (j : ℝ))) := by
      rw [← Finset.sum_mul]
      congr 1
      exact_mod_cast Nat.sum_range_choose j
    _ ≤ _ := by
      have htwo : (2 : ℝ) ^ j ≤ 8 := by interval_cases j <;> norm_num
      have hm := mul_le_mul_of_nonneg_right htwo
        (show 0 ≤ P * A * r ^ (1 + η - (j : ℝ)) by positivity)
      dsimp only [P, r] at hm
      nlinarith only [hm]

/-- Fourier coefficients of an ordinary cusp have first differences with an
extra power of decay, provided its derivatives are controlled through order
three. This supplies the analytic increment argument in the proof of Lemma 5.13, using the existing Fourier convention. -/
theorem coefficient_increment_decay {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 < A →
      ∀ H : C(AddCircle (2 * Real.pi), ℂ),
      ContDiffOn ℝ 3 (fun x : ℝ => H (x : AddCircle (2 * Real.pi)))
        (Ioo 0 (2 * Real.pi)) →
      (∀ j : ℕ, j ≤ 3 → ∀ x ∈ Ioo (0 : ℝ) (2 * Real.pi),
        ‖iteratedDeriv j (fun t : ℝ => H (t : AddCircle (2 * Real.pi))) x‖ ≤
          A * (min x (2 * Real.pi - x)) ^ (η - (j : ℝ))) →
      ∀ n : ℤ, ‖fourierCoeff H (n + 1) - fourierCoeff H n‖ ≤
        K * A / (1 + |(n : ℝ)| ^ (2 + η)) := by
  obtain ⟨K, hK, hb⟩ := third_order_coefficient_decay hη hη1
  refine ⟨K * (8 * (1 + Real.pi) ^ (3 : ℕ)), by positivity, ?_⟩
  intro A hA H hHs hHb n
  let V : C(AddCircle (2 * Real.pi), ℂ) :=
    ⟨fun x => (fourier (-1) x - 1) * H x,
      ((map_continuous (fourier (-1))).sub continuous_const).mul H.continuous⟩
  have hV0 : V 0 = 0 := by simp [V]
  have hE : ContDiff ℝ 3
      (fun x : ℝ => fourier (-1) (x : AddCircle (2 * Real.pi)) - 1) := by
    simp_rw [fourier_angular]
    exact ((contDiff_const.mul Complex.ofRealCLM.contDiff).cexp).sub contDiff_const
  have hVs : ContDiffOn ℝ 3 (fun x : ℝ => V (x : AddCircle (2 * Real.pi)))
      (Ioo 0 (2 * Real.pi)) := hE.contDiffOn.mul hHs
  have hVb := simple_zero_product_bounds hA.le hE.contDiffOn hHs
    (fun _ hx => first_character_sub_one_bound hx)
    (fun j hj _ x _ => (first_character_derivative_norm j hj x).le) hHb
  have hh := hb (8 * (1 + Real.pi) ^ (3 : ℕ) * A) (by positivity) V hV0 hVs hVb n
  change ‖fourierCoeff (fun x => (fourier (-1) x - 1) * H x) n‖ ≤ _ at hh
  rw [coefficient_forward_difference] at hh
  convert hh using 1
  ring

end Riesz2.FractionalCuspFourier
