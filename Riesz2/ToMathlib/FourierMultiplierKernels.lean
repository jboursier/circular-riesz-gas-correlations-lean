/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.FractionalCuspFourier
public import Riesz2.ToMathlib.EndpointCuspFourier
public import Riesz1.ToMathlib.Poincare.Circle
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Kernels of localized Fourier multipliers

The angular localized form of Lemma 2.4 in the paper,
with every positive scale. The shared endpoint-support, summation and aliasing
lemmas also supply the existing sine-annulus API.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped BigOperators ContDiff

namespace Riesz2.DiscreteInterpolation

local instance fourierMultiplierKernelsPeriodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The direct coefficient bound in Step 3 of Lemma 2.4 retains
the length of the frequency support. -/
theorem norm_fourierCoeffOn_le_radius_support {f : ℝ → ℂ} {t B : ℝ} {radius : ℝ → ℝ}
    (ht : 0 < t) (hB : 0 ≤ B) (hf : Continuous f)
    (hbound : ∀ x, ‖f x‖ ≤ B)
    (hcompare : ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi),
      min θ (2 * Real.pi - θ) ≤ Real.pi / 2 * radius θ)
    (hsupp : Function.support f ⊆ {θ | radius θ ≤ 4 * t}) (n : ℤ) :
    ‖fourierCoeffOn (by positivity : (0 : ℝ) < 2 * Real.pi) f n‖ ≤ 2 * B * t := by
  let g : ℝ → ℂ := fun x =>
    fourier (-n) (x : AddCircle (2 * Real.pi - 0)) • f x
  have hgn (x : ℝ) : ‖g x‖ = ‖f x‖ := by
    simp only [g, norm_smul, fourier_apply, Circle.norm_coe, one_mul]
  have hg : Continuous g := by
    exact ((fourier (-n)).continuous.comp (AddCircle.continuous_mk' _)).smul hf
  have hi := norm_integral_le_endpoint_support
    (T := 2 * Real.pi) (L := 2 * Real.pi * t) (B := B)
    (by positivity) (by positivity) hB hg (fun x _ => by rw [hgn]; exact hbound x)
    (fun x hx => by
      have h0 : f x = 0 := by
        by_contra hne
        have hr := hsupp hne
        change radius x ≤ 4 * t at hr
        have hL : 0 < 2 * Real.pi * t := by positivity
        have he := hcompare x ⟨by linarith [hx.1], by linarith [hx.2]⟩
        have hm : 2 * Real.pi * t < min x (2 * Real.pi - x) :=
          lt_min hx.1 (by linarith [hx.2])
        nlinarith [mul_le_mul_of_nonneg_left hr Real.pi_pos.le]
      simp only [g, h0, smul_zero])
  rw [fourierCoeffOn_eq_integral]
  simp_rw [sub_zero]
  simp only [norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  dsimp only [g] at hi
  calc
    _ ≤ (1 / (2 * Real.pi)) * (2 * (2 * Real.pi * t) * B) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = 2 * B * t := by field_simp

/-- The two coefficient estimates in Step 3 of Lemma 2.4.
The second estimate uses the first estimate on the second derivative, so its
scale is `t⁻¹`, rather than the weaker global `t⁻²`. -/
theorem localized_coefficient_bounds_of_radius {b : ℝ → ℂ} {t A : ℝ} {radius : ℝ → ℝ}
    (ht : 0 < t) (hcontinuous : Continuous radius)
    (h0 : radius 0 = 0) (hperiod : radius (2 * Real.pi) = 0)
    (hcompare : ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi),
      min θ (2 * Real.pi - θ) ≤ Real.pi / 2 * radius θ)
    (hb : ContDiff ℝ 2 b)
    (hsupp : Function.support b ⊆
      {θ | t ≤ radius θ ∧ radius θ ≤ 4 * t})
    (hbound : ∀ j : ℕ, j ≤ 2 → ∀ x, ‖iteratedDeriv j b x‖ ≤ A / t ^ j) :
    (∀ n : ℤ, ‖fourierCoeffOn (by positivity : (0 : ℝ) < 2 * Real.pi) b n‖ ≤
      2 * A * t) ∧
    (∀ n : ℤ, n ≠ 0 →
      ‖fourierCoeffOn (by positivity : (0 : ℝ) < 2 * Real.pi) b n‖ ≤
        2 * A / t / |(n : ℝ)| ^ 2) := by
  have hA : 0 ≤ A := by
    have h := hbound 0 (by omega) 0
    simpa only [iteratedDeriv_zero, pow_zero, div_one] using (norm_nonneg _).trans h
  have hsupp_deriv (j : ℕ) : tsupport (iteratedDeriv j b) ⊆
      {θ | t ≤ radius θ ∧ radius θ ≤ 4 * t} := by
    have hc : IsClosed {θ | t ≤ radius θ ∧ radius θ ≤ 4 * t} :=
      (isClosed_le continuous_const hcontinuous).inter
        (isClosed_le hcontinuous continuous_const)
    induction j with
    | zero => exact closure_minimal hsupp hc
    | succ j ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih
  have hzero (j : ℕ) (x : ℝ) (hx : radius x = 0) :
      iteratedDeriv j b x = 0 := by
    by_contra hne
    have hm := hsupp_deriv j (subset_closure hne)
    change t ≤ radius x ∧ radius x ≤ 4 * t at hm
    rw [hx] at hm
    linarith [hm.1]
  have hz (j : ℕ) : iteratedDeriv j b 0 = 0 := hzero j 0 h0
  have hT (j : ℕ) : iteratedDeriv j b (2 * Real.pi) = 0 :=
    hzero j _ hperiod
  have hd : ContDiff ℝ 1 (deriv b) := hb.deriv'
  have hc2 : Continuous (deriv (deriv b)) := hd.continuous_deriv (by norm_num)
  have hlo := norm_fourierCoeffOn_le_radius_support ht hA hb.continuous
    (fun x => by simpa only [iteratedDeriv_zero, pow_zero, div_one] using hbound 0 (by omega) x)
    hcompare (fun x hx => (hsupp hx).2)
  refine ⟨hlo, fun n hn => ?_⟩
  have h1 := Riesz1.fourierCoeffOn_eq_mul_fourierCoeffOn_deriv
    (T := 2 * Real.pi) (by positivity)
    (fun x => (hb.differentiable (by norm_num) x).hasDerivAt)
    hd.continuous (by simpa only [iteratedDeriv_zero] using (hT 0).trans (hz 0).symm) n hn
  have h2 := Riesz1.fourierCoeffOn_eq_mul_fourierCoeffOn_deriv
    (T := 2 * Real.pi) (by positivity)
    (fun x => (hd.differentiable (by norm_num) x).hasDerivAt)
    hc2 (by simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      (hT 1).trans (hz 1).symm) n hn
  have h3 := norm_fourierCoeffOn_le_radius_support ht (by positivity : 0 ≤ A / t ^ 2) hc2
    (fun x => by simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hbound 2 le_rfl x)
    hcompare (fun x hx => (hsupp_deriv 2
      (subset_closure (by simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hx))).2) n
  have hnR : |(n : ℝ)| ≠ 0 := abs_ne_zero.mpr (by exact_mod_cast hn)
  have hfactor : ‖(2 * Real.pi : ℂ) / (2 * Real.pi * Complex.I * n)‖ =
      1 / |(n : ℝ)| := by
    simp only [norm_div, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one,
      Complex.norm_intCast]
    field_simp
  rw [h1, h2, norm_mul, norm_mul, Complex.ofReal_mul, Complex.ofReal_ofNat, hfactor]
  calc
    _ ≤ (1 / |(n : ℝ)|) * ((1 / |(n : ℝ)|) * (2 * (A / t ^ 2) * t)) := by
      gcongr
    _ = 2 * A / t / |(n : ℝ)| ^ 2 := by field_simp

/-- A positive telescoping majorant, with exact mass independent of the scale. -/
theorem hasSum_scale_majorant {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => t / ((1 + t * n) * (1 + t * (n + 1)))) 1 := by
  have he (n : ℕ) :
      t / ((1 + t * n) * (1 + t * (n + 1))) =
        (1 + t * n)⁻¹ - (1 + t * (n + 1))⁻¹ := by
    have h1 : (1 + t * n) ≠ 0 := by positivity
    have h2 : (1 + t * (n + 1)) ≠ 0 := by positivity
    field_simp
    ring
  have hsum (n : ℕ) :
      ∑ i ∈ Finset.range n, t / ((1 + t * i) * (1 + t * (i + 1))) =
        1 - (1 + t * n)⁻¹ := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih, he]; push_cast; ring
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => by positivity) 1).2
  simp_rw [hsum]
  have hl := (tendsto_mul_add_inv_atTop_nhds_zero t 1 ht.ne').comp
    tendsto_natCast_atTop_atTop
  simpa only [sub_zero, add_comm, Function.comp_apply] using tendsto_const_nhds.sub hl

/-- A summable telescoping majorant for the localized coefficients. -/
theorem coefficient_le_scale_majorant {φ : ℤ → ℂ} {t A : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hA : 0 ≤ A)
    (hlo : ∀ n, ‖φ n‖ ≤ 2 * A * t)
    (hhi : ∀ n : ℤ, n ≠ 0 → ‖φ n‖ ≤ 2 * A / t / |(n : ℝ)| ^ 2) (n : ℤ) :
    ‖φ n‖ ≤ 16 * A * (t / ((1 + t * |(n : ℝ)|) * (1 + t * (|(n : ℝ)| + 1)))) := by
  have hn0 : 0 ≤ |(n : ℝ)| := abs_nonneg _
  have hD : 0 < (1 + t * |(n : ℝ)|) * (1 + t * (|(n : ℝ)| + 1)) := by positivity
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hD).2
  by_cases hsmall : t * |(n : ℝ)| ≤ 1
  · have hD6 : (1 + t * |(n : ℝ)|) * (1 + t * (|(n : ℝ)| + 1)) ≤ 6 := by
      have h1 : 1 + t * |(n : ℝ)| ≤ 2 := by linarith
      have h2 : 1 + t * (|(n : ℝ)| + 1) ≤ 3 := by nlinarith
      have hh := mul_le_mul h1 h2 (by positivity) (by norm_num : (0 : ℝ) ≤ 2)
      norm_num at hh
      exact hh
    calc
      ‖φ n‖ * _ ≤ ‖φ n‖ * 6 := mul_le_mul_of_nonneg_left hD6 (norm_nonneg _)
      _ ≤ (2 * A * t) * 6 := mul_le_mul_of_nonneg_right (hlo n) (by norm_num)
      _ ≤ _ := by nlinarith [mul_nonneg hA ht.le]
  · have hq : 1 ≤ t * |(n : ℝ)| := (lt_of_not_ge hsmall).le
    have hn : n ≠ 0 := by intro hz; subst n; norm_num at hq
    have hnR : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
    have hD6 : (1 + t * |(n : ℝ)|) * (1 + t * (|(n : ℝ)| + 1)) ≤
        6 * (t ^ 2 * |(n : ℝ)| ^ 2) := by
      have h1 : 1 + t * |(n : ℝ)| ≤ 2 * (t * |(n : ℝ)|) := by linarith
      have h2 : 1 + t * (|(n : ℝ)| + 1) ≤ 3 * (t * |(n : ℝ)|) := by nlinarith
      calc
        (1 + t * |(n : ℝ)|) * (1 + t * (|(n : ℝ)| + 1)) ≤
            (2 * (t * |(n : ℝ)|)) * (3 * (t * |(n : ℝ)|)) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = _ := by ring
    have hh := hhi n hn
    have hh' : ‖φ n‖ * (t * |(n : ℝ)| ^ 2) ≤ 2 * A := by
      apply (le_div_iff₀ (by positivity : 0 < t * |(n : ℝ)| ^ 2)).mp
      simpa only [div_div] using hh
    calc
      _ ≤ ‖φ n‖ * (6 * (t ^ 2 * |(n : ℝ)| ^ 2)) :=
        mul_le_mul_of_nonneg_left hD6 (norm_nonneg _)
      _ = 6 * t * (‖φ n‖ * (t * |(n : ℝ)| ^ 2)) := by ring
      _ ≤ 6 * t * (2 * A) := mul_le_mul_of_nonneg_left hh' (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg hA ht.le]

/-- The direct and twice-integrated coefficient estimates give a uniform
absolute sum. This is the scale cancellation in the proof of Lemma 5.9. -/
theorem summable_norm_and_tsum_le_of_two_bounds {φ : ℤ → ℂ} {t A : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hA : 0 ≤ A)
    (hlo : ∀ n, ‖φ n‖ ≤ 2 * A * t)
    (hhi : ∀ n : ℤ, n ≠ 0 → ‖φ n‖ ≤ 2 * A / t / |(n : ℝ)| ^ 2) :
    Summable (fun n => ‖φ n‖) ∧ (∑' n : ℤ, ‖φ n‖) ≤ 32 * A := by
  have hb := coefficient_le_scale_majorant ht ht1 hA hlo hhi
  let w := fun n : ℕ => t / ((1 + t * n) * (1 + t * (n + 1)))
  have hw : HasSum w 1 := hasSum_scale_majorant ht
  have hpos : Summable (fun n : ℕ => ‖φ (n : ℤ)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => by
      simpa only [Int.cast_natCast, Nat.abs_cast] using hb (n : ℤ))
      (hw.summable.mul_left (16 * A))
  have hneg : Summable (fun n : ℕ => ‖φ (-(n : ℤ))‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => by
      simpa only [Int.cast_neg, abs_neg, Int.cast_natCast, Nat.abs_cast] using hb (-(n : ℤ)))
      (hw.summable.mul_left (16 * A))
  have hp : (∑' n : ℕ, ‖φ (n : ℤ)‖) ≤ 16 * A := by
    calc
      _ ≤ ∑' n : ℕ, 16 * A * w n := hpos.tsum_le_tsum (fun n => by
        simpa only [Int.cast_natCast, Nat.abs_cast] using hb (n : ℤ))
        (hw.summable.mul_left _)
      _ = 16 * A := by rw [tsum_mul_left, hw.tsum_eq, mul_one]
  have hm : (∑' n : ℕ, ‖φ (-(n : ℤ))‖) ≤ 16 * A := by
    calc
      _ ≤ ∑' n : ℕ, 16 * A * w n := hneg.tsum_le_tsum (fun n => by
        simpa only [Int.cast_neg, abs_neg, Int.cast_natCast, Nat.abs_cast] using hb (-(n : ℤ)))
        (hw.summable.mul_left _)
      _ = 16 * A := by rw [tsum_mul_left, hw.tsum_eq, mul_one]
  have hs : Summable (fun n : ℤ => ‖φ n‖) :=
    Summable.of_nat_of_neg (f := fun n : ℤ => ‖φ n‖) hpos hneg
  refine ⟨hs, ?_⟩
  have hns : Summable (fun n : ℕ => ‖φ (-((n : ℤ) + 1))‖) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ => ‖φ (-(n : ℤ))‖) 1).mpr hneg
  have hsplit := tsum_of_nat_of_neg_add_one (f := fun n : ℤ => ‖φ n‖) hpos hns
  have hnegshift : (∑' n : ℕ, ‖φ (-((n + 1 : ℕ) : ℤ))‖) ≤
      ∑' n : ℕ, ‖φ (-(n : ℤ))‖ := by
    rw [hneg.tsum_eq_zero_add]
    exact le_add_of_nonneg_left (norm_nonneg _)
  rw [hsplit]
  push_cast at hnegshift
  linarith

/-- Aliasing cannot increase the counting-measure `ℓ¹` norm. -/
theorem sum_norm_periodizeSequence_le (N : ℕ+) (φ : ℤ → ℂ)
    (hφ : Summable (fun n => ‖φ n‖)) :
    (∑ i : Fin (N : ℕ), ‖periodizeSequence N φ hφ i‖) ≤ ∑' n : ℤ, ‖φ n‖ := by
  have hnorm : Summable (fun n : ℤ => ‖(‖φ n‖ : ℂ)‖) := by simpa using hφ
  have hm := congrArg Complex.re
    (tsum_eq_sum_periodizeSequence N (fun n : ℤ => (‖φ n‖ : ℂ)) hnorm)
  simp only [Complex.re_sum, periodizeSequence, ← Complex.ofReal_tsum,
    Complex.ofReal_re] at hm
  rw [hm]
  apply Finset.sum_le_sum
  intro i _
  exact norm_tsum_le_tsum_norm (summable_norm_periodizeSequence N φ hφ i.val)

/-- The inverse finite transform of a sampled angular function is its aliased
continuous Fourier series, in the existing positive-forward convention. -/
theorem cycleFourierInv_sample_eq_periodization
    (N : ℕ+) (b : C(AddCircle (2 * Real.pi), ℂ))
    (hb : Summable (fun n : ℤ => ‖fourierCoeff b n‖)) :
    cycleFourierInv N (fun k => b ((cycleAngle N k : ℝ) : AddCircle (2 * Real.pi))) =
      periodizeSequence N (fourierCoeff b) hb := by
  apply cycleFourier_injective N
  funext k
  rw [cycleFourier_cycleFourierInv, inverse_aliasing,
    FractionalCuspFourier.latticeFourier_fourierCoeff]


end Riesz2.DiscreteInterpolation

namespace Riesz2.FourierMultiplierKernels

local instance fourierMultiplierAngularPeriodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Distance to `2πℤ` in Lemma 2.4, on the whole angular line. -/
def angularRadius (θ : ℝ) : ℝ := ‖(θ : AddCircle (2 * Real.pi))‖

/-- The representative formula for the distance in Lemma 2.4. -/
theorem angularRadius_eq_min {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    angularRadius θ = min θ (2 * Real.pi - θ) := by
  by_cases h : θ ≤ Real.pi
  · rw [angularRadius, (AddCircle.norm_coe_eq_abs_iff (2 * Real.pi) (by positivity)).2 (by
      rw [abs_of_nonneg hθ.1, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      linarith), abs_of_nonneg hθ.1, min_eq_left (by linarith)]
  · have he : (θ : AddCircle (2 * Real.pi)) =
        -((2 * Real.pi - θ : ℝ) : AddCircle (2 * Real.pi)) := by
      simp only [AddCircle.coe_sub, AddCircle.coe_period, zero_sub, neg_neg]
    rw [angularRadius, he, norm_neg,
      (AddCircle.norm_coe_eq_abs_iff (2 * Real.pi) (by positivity)).2 (by
        rw [abs_of_nonneg (by linarith [hθ.2]),
          abs_of_pos (by positivity : 0 < 2 * Real.pi)]
        linarith), abs_of_nonneg (by linarith [hθ.2]), min_eq_right (by linarith)]

/-- The zero-frequency coefficient estimate of Lemma 2.4,
Step 1. It is valid throughout the written range, including `α = 1`. -/
theorem fourierMultiplier_zero_coefficient_bound {α B : ℝ} (hα : 0 < α) (hB : 0 ≤ B)
    (m : C(AddCircle (2 * Real.pi), ℂ)) (hm0 : m 0 = 0)
    (hb : ∀ θ ∈ Ioo (0 : ℝ) (2 * Real.pi),
      ‖m (θ : AddCircle (2 * Real.pi))‖ ≤ B * angularRadius θ ^ α) :
    ‖fourierCoeff m 0‖ ≤ B * Real.pi ^ α := by
  have he (x : ℝ) (hx : x ∈ Ioc 0 (2 * Real.pi)) :
      ‖m (x : AddCircle (2 * Real.pi))‖ ≤ B * Real.pi ^ α := by
    rcases lt_or_eq_of_le hx.2 with hlt | rfl
    · have hr : 0 ≤ angularRadius x := norm_nonneg _
      have hrπ : angularRadius x ≤ Real.pi := by
        rw [angularRadius_eq_min ⟨hx.1.le, hx.2⟩]
        have h1 := min_le_left x (2 * Real.pi - x)
        have h2 := min_le_right x (2 * Real.pi - x)
        linarith
      exact (hb x ⟨hx.1, hlt⟩).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr hrπ hα.le) hB)
    · simp only [AddCircle.coe_period, hm0, norm_zero]
      positivity
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := 2 * Real.pi) (C := B * Real.pi ^ α)
    (f := fun x : ℝ => m (x : AddCircle (2 * Real.pi))) (fun x hx =>
      he x (by rwa [uIoc_of_le (by positivity)] at hx))
  rw [FractionalCuspFourier.fourierCoeff_angular]
  simp only [Int.cast_zero, neg_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  simp only [sub_zero, abs_of_pos (by positivity : 0 < 2 * Real.pi)] at hi
  calc
    _ ≤ (1 / (2 * Real.pi)) * (B * Real.pi ^ α * (2 * Real.pi)) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ = B * Real.pi ^ α := by field_simp

/-- Exact mass in Lemma 2.4, part 1. This identity holds for
every complex symbol and every complex zero mode, independently of regularity
or decay. The formula is the manuscript's inverse finite transform. -/
theorem fourierMultiplier_kernel_mass (N : ℕ+) (m : ℝ → ℂ) (z₀ : ℂ) :
    (∑ h : Fin (N : ℕ), ((N : ℕ) : ℂ)⁻¹ *
      (z₀ + ∑ k ∈ Finset.univ.erase (0 : Fin (N : ℕ)),
        m (cycleAngle N k) *
          Complex.exp (-(Complex.I * (h.val : ℂ) * (cycleAngle N k : ℂ))))) = z₀ := by
  classical
  let Φ : Fin (N : ℕ) → ℂ := fun k => if k = 0 then z₀ else m (cycleAngle N k)
  have he (h : Fin (N : ℕ)) :
      ((N : ℕ) : ℂ)⁻¹ *
        (z₀ + ∑ k ∈ Finset.univ.erase (0 : Fin (N : ℕ)),
          m (cycleAngle N k) *
            Complex.exp (-(Complex.I * (h.val : ℂ) * (cycleAngle N k : ℂ)))) =
      cycleFourierInv N Φ h := by
    unfold cycleFourierInv
    congr 1
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin (N : ℕ)))]
    simp only [Φ, ↓reduceIte, cycleAngle, Fin.val_zero, Nat.cast_zero,
      mul_zero, zero_div, Complex.ofReal_zero, neg_zero, Complex.exp_zero, mul_one]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [ite_eq_right (Finset.mem_erase.mp hk).1]
  simp_rw [he]
  have h := cycleFourier_cycleFourierInv (N := N) Φ 0
  simpa only [cycleFourier, cycleAngle, Fin.val_zero, Nat.cast_zero,
    mul_zero, zero_div, Complex.ofReal_zero, neg_zero, Complex.exp_zero, mul_one,
    Φ, ↓reduceIte] using h

/-- The inverse finite transform in Lemma 2.4, part 1,
with its independently prescribed complex zero mode, evaluated at any integer. -/
def multiplierKernel (N : ℕ+) (m : ℝ → ℂ) (z₀ : ℂ) (h : ℤ) : ℂ :=
  ((N : ℕ) : ℂ)⁻¹ * (z₀ + ∑ k ∈ Finset.univ.erase (0 : Fin (N : ℕ)),
    m (cycleAngle N k) * Complex.exp (-(Complex.I * (h : ℂ) * (cycleAngle N k : ℂ))))

/-- The integer formula in Lemma 2.4 is precisely the existing
inverse finite transform on the residue class of the integer. -/
theorem multiplierKernel_eq_cycleFourierInv (N : ℕ+) (m : ℝ → ℂ) (z₀ : ℂ) (h : ℤ) :
    multiplierKernel N m z₀ h = cycleFourierInv N
      (fun k => if k = 0 then z₀ else m (cycleAngle N k)) (Riesz1.labelOf N h) := by
  classical
  have he (k : Fin (N : ℕ)) :
      Complex.exp (-(Complex.I * ((Riesz1.labelOf N h).val : ℂ) * (cycleAngle N k : ℂ))) =
        Complex.exp (-(Complex.I * (h : ℂ) * (cycleAngle N k : ℂ))) := by
    rw [kernel_neg_eq, show -((Riesz1.labelOf N h).val : ℤ) * (k.val : ℤ) =
      ((Riesz1.labelOf N h).val : ℤ) * (-(k.val : ℤ)) by ring, zpow_labelOf]
    have hx := exp_mul_angle_eq_zpow (N := N) (-h) k
    rw [Int.cast_neg] at hx
    rw [show Complex.I * -(h : ℂ) * (cycleAngle N k : ℂ) =
      -(Complex.I * (h : ℂ) * (cycleAngle N k : ℂ)) by ring] at hx
    rw [hx]
    congr 1
    ring
  unfold multiplierKernel cycleFourierInv
  simp_rw [he]
  congr 1
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin (N : ℕ)))]
  simp only [↓reduceIte, cycleAngle, Fin.val_zero, Nat.cast_zero, mul_zero,
    zero_div, Complex.ofReal_zero, neg_zero, Complex.exp_zero, mul_one]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [ite_eq_right (Finset.mem_erase.mp hk).1]

/-- The circle-symbol form of Lemma 2.4, part 1. The proof
follows its coefficient, reconstruction and periodization steps. Its constants
precede the amplitude, cycle size, symbol and arbitrary complex zero mode. -/
theorem fourierMultiplier_kernel_circle (r : ℕ) (α : ℝ)
    (hα : 0 < α) (hαr : α < (r : ℝ) - 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 0 < B → ∀ N : ℕ+, 2 ≤ (N : ℕ) →
      ∀ m : C(AddCircle (2 * Real.pi), ℂ), m 0 = 0 →
      ContDiffOn ℝ r (fun θ : ℝ => m (θ : AddCircle (2 * Real.pi)))
        (Ioo 0 (2 * Real.pi)) →
      (∀ j : ℕ, j ≤ r → ∀ θ ∈ Ioo 0 (2 * Real.pi),
        ‖iteratedDeriv j (fun x : ℝ => m (x : AddCircle (2 * Real.pi))) θ‖ ≤
          B * angularRadius θ ^ (α - j)) → ∀ z₀ : ℂ,
      (∀ h : ℤ, ‖fourierCoeff m h‖ ≤ C * B / (1 + |(h : ℝ)|) ^ (1 + α)) ∧
      (∀ h : ℤ, ‖multiplierKernel N (fun θ => m (θ : AddCircle (2 * Real.pi))) z₀ h‖ ≤
        C * B / (1 + ((Riesz1.cyclicDist N h 0 : ℤ) : ℝ)) ^ (1 + α) + ‖z₀‖ / (N : ℝ)) ∧
      (∑ h : Fin (N : ℕ), multiplierKernel N
        (fun θ => m (θ : AddCircle (2 * Real.pi))) z₀ h.val) = z₀ := by
  classical
  obtain ⟨A, hA, hcoeff⟩ := FractionalCuspFourier.fourierCoeff_decay_of_endpoint_bounds r α hα hαr
  obtain ⟨T, hT, htail⟩ := inverse_power_sum (show 1 < 1 + α by linarith)
  let C := A + 2 * A * T * 2 ^ (1 + α)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun B hB N hN m hm0 hms hmb z₀ => ?_⟩
  have hbound := hcoeff B hB m hm0 hms (fun j hj θ hθ => by
    rw [← angularRadius_eq_min (Ioo_subset_Icc_self hθ)]
    exact hmb j hj θ hθ)
  have hlegacy (n : ℤ) : ‖fourierCoeff m n‖ ≤
      (2 * A * B) / (1 + |(n : ℝ)| ^ (1 + α)) := by
    have hd := (FractionalCuspFourier.cusp_denominator_comparison (abs_nonneg (n : ℝ))
      (show 0 ≤ 1 + α by linarith)).1
    calc
      _ ≤ A * B / (1 + |(n : ℝ)|) ^ (1 + α) := hbound n
      _ = (2 * A * B) / (2 * (1 + |(n : ℝ)|) ^ (1 + α)) := by ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hd
  have hs := FractionalCuspFourier.summable_norm_of_coefficient_bound
    (show 1 < 1 + α by linarith) hlegacy
  have hsample := DiscreteInterpolation.cycleFourierInv_sample_eq_periodization N m hs
  have hkernel (h : ℤ) :
      multiplierKernel N (fun θ => m (θ : AddCircle (2 * Real.pi))) z₀ h =
        periodizeSequence N (fourierCoeff m) hs (Riesz1.labelOf N h) +
          ((N : ℕ) : ℂ)⁻¹ * z₀ := by
    rw [multiplierKernel_eq_cycleFourierInv]
    have he : (fun k : Fin (N : ℕ) =>
        if k = 0 then z₀ else m ((cycleAngle N k : ℝ) : AddCircle (2 * Real.pi))) =
        (fun k => m ((cycleAngle N k : ℝ) : AddCircle (2 * Real.pi)) +
          if k = 0 then z₀ else 0) := by
      funext k
      split_ifs with hk
      · subst k
        simp [cycleAngle, hm0]
      · simp
    rw [he, ← hsample]
    simp only [cycleFourierInv, add_mul, Finset.sum_add_distrib, mul_add]
    congr 1
    simp [cycleAngle]
  refine ⟨fun h => (hbound h).trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by
      dsimp [C]
      have : 0 ≤ 2 * A * T * 2 ^ (1 + α) := by positivity
      linarith) hB.le) (by positivity)), ?_, ?_⟩
  · intro h
    obtain ⟨hts, htb, _⟩ := htail N hN ((Riesz1.labelOf N h).val : ℤ)
    have hd : Riesz1.cyclicDist N ((Riesz1.labelOf N h).val : ℤ) 0 =
        Riesz1.cyclicDist N h 0 := by
      simp only [Riesz1.cyclicDist, Riesz1.APG.labelOf_val, Int.zero_emod, sub_zero]
      rw [Int.emod_emod]
    rw [hd] at htb
    let d : ℝ := (Riesz1.cyclicDist N h 0 : ℤ)
    have hd0 : 0 ≤ d := by
      have hNN : (0 : ℤ) < (N : ℕ) := by exact_mod_cast N.pos
      have hh0 := Int.emod_nonneg h hNN.ne'
      have hhN := Int.emod_lt_of_pos h hNN
      have hdist : (0 : ℤ) ≤ Riesz1.cyclicDist N h 0 := by
        simp only [Riesz1.cyclicDist, Int.zero_emod, sub_zero, abs_of_nonneg hh0]
        exact le_min hh0 (by omega)
      dsimp only [d]
      exact_mod_cast hdist
    have hperiod : ‖periodizeSequence N (fourierCoeff m) hs (Riesz1.labelOf N h)‖ ≤
        (2 * A * B) * T / (1 + d ^ (1 + α)) := by
      calc
        _ ≤ ∑' l : ℤ, ‖fourierCoeff m (((Riesz1.labelOf N h).val : ℤ) + l * (N : ℕ))‖ :=
          norm_tsum_le_tsum_norm (summable_norm_periodizeSequence N _ hs _)
        _ ≤ ∑' l : ℤ, (2 * A * B) *
            (1 / (1 + |((Riesz1.labelOf N h).val : ℝ) + (l : ℝ) * (N : ℝ)| ^ (1 + α))) := by
          apply Summable.tsum_le_tsum _ (summable_norm_periodizeSequence N _ hs _) (hts.mul_left _)
          intro l
          convert hlegacy (((Riesz1.labelOf N h).val : ℤ) + l * (N : ℕ)) using 1
          push_cast
          ring
        _ = (2 * A * B) * ∑' l : ℤ,
            1 / (1 + |((Riesz1.labelOf N h).val : ℝ) + (l : ℝ) * (N : ℝ)| ^ (1 + α)) := tsum_mul_left
        _ ≤ (2 * A * B) * (T / (1 + d ^ (1 + α))) :=
          mul_le_mul_of_nonneg_left htb (by positivity)
        _ = _ := by ring
    have hden := (FractionalCuspFourier.cusp_denominator_comparison hd0
      (show 0 ≤ 1 + α by linarith)).2
    have hdecay : (2 * A * B) * T / (1 + d ^ (1 + α)) ≤
        C * B / (1 + d) ^ (1 + α) := by
      calc
        _ = (2 * A * T * 2 ^ (1 + α) * B) /
            (2 ^ (1 + α) * (1 + d ^ (1 + α))) := by field_simp
        _ ≤ (2 * A * T * 2 ^ (1 + α) * B) / (1 + d) ^ (1 + α) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hden
        _ ≤ _ := div_le_div_of_nonneg_right (by dsimp [C]; nlinarith) (by positivity)
    rw [hkernel]
    calc
      _ ≤ _ := norm_add_le _ _
      _ ≤ C * B / (1 + d) ^ (1 + α) + ‖z₀‖ / (N : ℝ) := by
        rw [norm_mul, norm_inv, Complex.norm_natCast]
        exact add_le_add (hperiod.trans hdecay) (by rw [div_eq_mul_inv, mul_comm])
  · simpa only [multiplierKernel, Int.cast_natCast] using
      fourierMultiplier_kernel_mass N (fun θ => m (θ : AddCircle (2 * Real.pi))) z₀

/-- Lemma 2.4, part 1, with its literal coefficient decay,
integer kernel bound and exact complex mass. Periodicity makes the punctured
regularity and derivative hypotheses on one open period equivalent to those
on the whole punctured line. The constant precedes `B`, `N`, `m` and `z₀`. -/
theorem fourierMultiplier_kernel (r : ℕ) (_hr : r = 2 ∨ r = 3) (α : ℝ)
    (hα : 0 < α) (hαr : α < (r : ℝ) - 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 0 < B → ∀ N : ℕ+, 2 ≤ (N : ℕ) →
      ∀ m : ℝ → ℂ, Continuous m → Function.Periodic m (2 * Real.pi) → m 0 = 0 →
      ContDiffOn ℝ r m (Ioo 0 (2 * Real.pi)) →
      (∀ j : ℕ, j ≤ r → ∀ θ ∈ Ioo 0 (2 * Real.pi),
        ‖iteratedDeriv j m θ‖ ≤ B * angularRadius θ ^ (α - j)) → ∀ z₀ : ℂ,
      (∀ h : ℤ, ‖(1 / (2 * Real.pi)) • ∫ θ in (0 : ℝ)..(2 * Real.pi),
          m θ * Complex.exp (-(h : ℂ) * Complex.I * (θ : ℂ))‖ ≤
        C * B / (1 + |(h : ℝ)|) ^ (1 + α)) ∧
      (∀ h : ℤ, ‖multiplierKernel N m z₀ h‖ ≤
        C * B / (1 + ((Riesz1.cyclicDist N h 0 : ℤ) : ℝ)) ^ (1 + α) + ‖z₀‖ / (N : ℝ)) ∧
      (∑ h : Fin (N : ℕ), multiplierKernel N m z₀ h.val) = z₀ := by
  obtain ⟨C, hC, hb⟩ := fourierMultiplier_kernel_circle r α hα hαr
  refine ⟨C, hC, fun B hB N hN m hm hp hm0 hms hmb z₀ => ?_⟩
  have hqc : Continuous hp.lift :=
    (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (2 * Real.pi))).continuous_iff.mpr
      (by
        change Continuous (fun θ : ℝ => hp.lift (θ : AddCircle (2 * Real.pi)))
        simpa only [hp.lift_coe] using hm)
  let M : C(AddCircle (2 * Real.pi), ℂ) := ⟨hp.lift, hqc⟩
  have he : (fun θ : ℝ => M (θ : AddCircle (2 * Real.pi))) = m := by
    funext θ
    exact hp.lift_coe θ
  have hM0 : M 0 = 0 := by
    have h := congrFun he 0
    simpa only [AddCircle.coe_zero, hm0] using h
  have h := hb B hB N hN M hM0 (by rwa [he]) (by rwa [he]) z₀
  simp_rw [FractionalCuspFourier.fourierCoeff_angular] at h
  simpa only [M, ContinuousMap.coe_mk, hp.lift_coe] using h

/-- The localized conclusion of Lemma 2.4, part 2. The symbol
is a continuous map on the angular circle, so its lift is periodic. The inverse
finite transform is precisely the displayed kernel, since the support excludes
zero. The absolute constant precedes the amplitude, size, scale and symbol. -/
theorem localized_fourierMultiplier_kernel_circle :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 0 < B → ∀ (N : ℕ+), 2 ≤ (N : ℕ) →
      ∀ t : ℝ, 0 < t → ∀ m : C(AddCircle (2 * Real.pi), ℂ),
      ContDiff ℝ 2 (fun θ : ℝ => m (θ : AddCircle (2 * Real.pi))) →
      Function.support (fun θ : ℝ => m (θ : AddCircle (2 * Real.pi))) ⊆
        {θ | t ≤ angularRadius θ ∧ angularRadius θ ≤ 4 * t} →
      (∀ j : ℕ, j ≤ 2 → ∀ θ : ℝ,
        ‖iteratedDeriv j (fun x : ℝ => m (x : AddCircle (2 * Real.pi))) θ‖ ≤
          B / t ^ j) →
      (∑ h : Fin (N : ℕ), ‖cycleFourierInv N
        (fun k => m ((cycleAngle N k : ℝ) : AddCircle (2 * Real.pi))) h‖) ≤ C * B := by
  refine ⟨32, by norm_num, ?_⟩
  intro B hB N _ t ht m hm hsupp hbound
  let u := min t 1
  have hu : 0 < u := lt_min ht zero_lt_one
  have hut : u ≤ t := min_le_left _ _
  have hu1 : u ≤ 1 := min_le_right _ _
  have hsupport : Function.support (fun θ : ℝ => m (θ : AddCircle (2 * Real.pi))) ⊆
      {θ | u ≤ angularRadius θ ∧ angularRadius θ ≤ 4 * u} := by
    intro θ hθ
    obtain ⟨hlo, hhi⟩ := hsupp hθ
    refine ⟨hut.trans hlo, ?_⟩
    by_cases ht1 : t ≤ 1
    · simpa only [u, min_eq_left ht1] using hhi
    · have hh := AddCircle.norm_le_half_period (2 * Real.pi)
        (x := (θ : AddCircle (2 * Real.pi))) (by positivity)
      rw [abs_of_pos (by positivity : 0 < 2 * Real.pi)] at hh
      change angularRadius θ ≤ _ at hh
      dsimp only [u]
      rw [min_eq_right (le_of_not_ge ht1)]
      linarith [Real.pi_lt_four]
  have hboundu : ∀ j : ℕ, j ≤ 2 → ∀ θ : ℝ,
      ‖iteratedDeriv j (fun x : ℝ => m (x : AddCircle (2 * Real.pi))) θ‖ ≤ B / u ^ j := by
    intro j hj θ
    exact (hbound j hj θ).trans (div_le_div_of_nonneg_left hB.le
      (by positivity) (pow_le_pow_left₀ hu.le hut j))
  have hcompare : ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi),
      min θ (2 * Real.pi - θ) ≤ Real.pi / 2 * angularRadius θ := by
    intro θ hθ
    rw [angularRadius_eq_min hθ]
    have hn : 0 ≤ min θ (2 * Real.pi - θ) := le_min hθ.1 (by linarith [hθ.2])
    nlinarith [Real.pi_gt_three]
  obtain ⟨hlo, hhi⟩ := DiscreteInterpolation.localized_coefficient_bounds_of_radius
    hu ((AddCircle.continuous_mk' (2 * Real.pi)).norm)
    (by simp) (by simp) hcompare hm hsupport hboundu
  have hcoeff (n : ℤ) : fourierCoeff m n =
      fourierCoeffOn (by positivity : (0 : ℝ) < 2 * Real.pi)
        (fun θ : ℝ => m (θ : AddCircle (2 * Real.pi))) n := by
    rw [fourierCoeff_eq_intervalIntegral m n 0, fourierCoeffOn_eq_integral]
    simp only [zero_add, sub_zero]
    congr 2
    funext x
    simp only [smul_eq_mul]
    rw [fourier_coe_apply, fourier_coe_apply]
    simp only [sub_zero]
  obtain ⟨hs, hsum⟩ := DiscreteInterpolation.summable_norm_and_tsum_le_of_two_bounds
    hu hu1 hB.le (φ := fourierCoeff m)
    (fun n => by rw [hcoeff]; exact hlo n)
    (fun n hn => by rw [hcoeff]; exact hhi n hn)
  rw [DiscreteInterpolation.cycleFourierInv_sample_eq_periodization N m hs]
  exact (DiscreteInterpolation.sum_norm_periodizeSequence_le N _ hs).trans hsum

/-- The literal real-line version of Lemma 2.4, part 2, for
all positive scales and angular support. The displayed sum excludes frequency
zero, as in the manuscript. -/
theorem localized_fourierMultiplier_kernel :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 0 < B → ∀ (N : ℕ+), 2 ≤ (N : ℕ) →
      ∀ t : ℝ, 0 < t → ∀ m : ℝ → ℂ,
      Function.Periodic m (2 * Real.pi) → ContDiff ℝ 2 m →
      Function.support m ⊆ {θ | t ≤ angularRadius θ ∧ angularRadius θ ≤ 4 * t} →
      (∀ j : ℕ, j ≤ 2 → ∀ θ : ℝ, ‖iteratedDeriv j m θ‖ ≤ B / t ^ j) →
      (∑ h : Fin (N : ℕ), ‖((N : ℕ) : ℂ)⁻¹ *
        ∑ k ∈ Finset.univ.erase (0 : Fin (N : ℕ)),
          m (cycleAngle N k) *
            Complex.exp (-(Complex.I * (h.val : ℂ) * (cycleAngle N k : ℂ)))‖) ≤ C * B := by
  obtain ⟨C, hC, hb⟩ := localized_fourierMultiplier_kernel_circle
  refine ⟨C, hC, ?_⟩
  intro B hB N hN t ht m hp hm hsupp hbound
  have hqc : Continuous hp.lift :=
    (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (2 * Real.pi))).continuous_iff.mpr
      (by
        change Continuous (fun θ : ℝ => hp.lift (θ : AddCircle (2 * Real.pi)))
        simpa only [hp.lift_coe] using hm.continuous)
  let M : C(AddCircle (2 * Real.pi), ℂ) := ⟨hp.lift, hqc⟩
  have he : (fun θ : ℝ => M (θ : AddCircle (2 * Real.pi))) = m := by
    funext θ
    exact hp.lift_coe θ
  have hM := hb B hB N hN t ht M (by rwa [he]) (by rwa [he]) (by rwa [he])
  have hz : m 0 = 0 := by
    by_contra hn
    have hh := (hsupp hn).1
    simp only [angularRadius, AddCircle.coe_zero, norm_zero] at hh
    linarith
  convert hM using 1
  apply Finset.sum_congr rfl
  intro h _
  congr 1
  simp only [cycleFourierInv, M, ContinuousMap.coe_mk, hp.lift_coe]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin (N : ℕ)))]
  simp only [cycleAngle, Fin.val_zero, Nat.cast_zero, mul_zero, zero_div, hz, zero_mul, add_zero]

end Riesz2.FourierMultiplierKernels
