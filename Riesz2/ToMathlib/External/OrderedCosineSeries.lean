/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.NumberTheory.LSeries.HurwitzZeta
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Tactic

/-!
# Ordered cosine series

Infrastructure for the periodic-zeta connection formula. Summation by parts gives
an absolutely convergent series of differences on the positive half-plane.
Its holomorphy identifies the ordinary partial-sum limit with `cosZeta`.
The original conditionally convergent series is never evaluated using `tsum`.
-/

public section

noncomputable section

open Filter Set
open scoped Topology BigOperators

namespace Riesz2.OrderedCosineSeries

/-- A first difference of complex powers has one extra power of decay. -/
theorem norm_cpow_neg_sub_le {z : ℂ} (hz : 0 < z.re) {a : ℝ} (ha : 0 < a) :
    ‖(a : ℂ) ^ (-z) - ((a + 1 : ℝ) : ℂ) ^ (-z)‖ ≤
      ‖z‖ * a ^ (-z.re - 1) := by
  have hz0 : -z ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.zero_re] at this
    linarith
  have hder (t : ℝ) (ht : t ∈ Icc a (a + 1)) :
      HasDerivWithinAt (fun t : ℝ => (t : ℂ) ^ (-z))
        ((-z) * (t : ℂ) ^ (-z - 1)) (Icc a (a + 1)) t :=
    (hasDerivAt_ofReal_cpow_const (ne_of_gt (ha.trans_le ht.1)) hz0).hasDerivWithinAt
  have hbound (t : ℝ) (ht : t ∈ Ico a (a + 1)) :
      ‖(-z) * (t : ℂ) ^ (-z - 1)‖ ≤ ‖z‖ * a ^ (-z.re - 1) := by
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans_le ht.1)]
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ha ht.1 (by linarith)) (norm_nonneg _)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hder hbound
    (a + 1) (by constructor <;> linarith)
  simpa only [norm_sub_rev, add_sub_cancel_left, mul_one] using h

/-- Finite summation by parts, with a terminal coefficient at the next index. -/
theorem sum_by_parts (c a : ℕ → ℂ) (M : ℕ) :
    (∑ n ∈ Finset.range M, c n * a n) =
      a M * (∑ n ∈ Finset.range M, c n) +
        ∑ n ∈ Finset.range M,
          (∑ k ∈ Finset.range (n + 1), c k) * (a n - a (n + 1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [Finset.sum_range_succ]
    ring

/-- The transformed Dirichlet series converges absolutely for positive real part. -/
theorem summable_prefix_differences (c : ℕ → ℂ) {B : ℝ}
    (hB : ∀ M, ‖∑ n ∈ Finset.range M, c n‖ ≤ B) {z : ℂ} (hz : 0 < z.re) :
    Summable (fun n : ℕ => (∑ k ∈ Finset.range (n + 1), c k) *
      (((n + 1 : ℕ) : ℂ) ^ (-z) - ((n + 2 : ℕ) : ℂ) ^ (-z))) := by
  have hp : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-z.re - 1)) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith))
  apply Summable.of_norm_bounded (hp.mul_left (B * ‖z‖))
  intro n
  rw [norm_mul]
  calc
    _ ≤ B * (‖z‖ * ((n + 1 : ℕ) : ℝ) ^ (-z.re - 1)) :=
      mul_le_mul (hB _) (by
        convert norm_cpow_neg_sub_le hz (by positivity : 0 < ((n + 1 : ℕ) : ℝ)) using 1
        norm_num [Nat.cast_add, add_assoc])
        (norm_nonneg _) ((norm_nonneg _).trans (hB 0))
    _ = _ := by ring

/-- Ordinary ordered convergence for bounded summatory coefficients. The `tsum`
on the right is the absolutely convergent transformed series, not the original one. -/
theorem tendsto_sum_prefix_differences (c : ℕ → ℂ) {B : ℝ}
    (hB : ∀ M, ‖∑ n ∈ Finset.range M, c n‖ ≤ B) {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun M : ℕ => ∑ n ∈ Finset.range M,
      c n * ((n + 1 : ℕ) : ℂ) ^ (-z)) atTop
      (𝓝 (∑' n : ℕ, (∑ k ∈ Finset.range (n + 1), c k) *
        (((n + 1 : ℕ) : ℂ) ^ (-z) - ((n + 2 : ℕ) : ℂ) ^ (-z)))) := by
  have hp : Tendsto (fun M : ℕ => ‖((M + 1 : ℕ) : ℂ) ^ (-z)‖) atTop (𝓝 0) := by
    have heq (M : ℕ) : ‖((M + 1 : ℕ) : ℂ) ^ (-z)‖ =
        ((M + 1 : ℕ) : ℝ) ^ (-z.re) := by
      rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
        Complex.neg_re]
    simp_rw [heq]
    exact (tendsto_rpow_neg_atTop hz).comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
  have hb : Tendsto (fun M : ℕ => ((M + 1 : ℕ) : ℂ) ^ (-z) *
      ∑ n ∈ Finset.range M, c n) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun M => ‖((M + 1 : ℕ) : ℂ) ^ (-z)‖ * B)
    · intro M
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hB M) (norm_nonneg _)
    · simpa using hp.mul_const B
  have h := hb.add (summable_prefix_differences c hB hz).hasSum.tendsto_sum_nat
  simp only [zero_add] at h
  convert h using 1
  ext M
  simpa only [Nat.add_assoc] using sum_by_parts c
    (fun n => ((n + 1 : ℕ) : ℂ) ^ (-z)) M

/-- The absolutely convergent summation-by-parts expression is holomorphic
throughout the positive half-plane. -/
theorem differentiableOn_prefix_differences (c : ℕ → ℂ) {B : ℝ}
    (hB : ∀ M, ‖∑ n ∈ Finset.range M, c n‖ ≤ B) :
    DifferentiableOn ℂ (fun z : ℂ => ∑' n : ℕ,
      (∑ k ∈ Finset.range (n + 1), c k) *
        (((n + 1 : ℕ) : ℂ) ^ (-z) - ((n + 2 : ℕ) : ℂ) ^ (-z)))
      {z : ℂ | 0 < z.re} := by
  intro z hz
  let δ := z.re / 2
  let R := ‖z‖ + 1
  let U := {w : ℂ | δ < w.re ∧ ‖w‖ < R}
  have hδ : 0 < δ := half_pos hz
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)
  have hzU : z ∈ U := ⟨by dsimp [δ]; change 0 < z.re at hz; linarith,
    by dsimp [R]; linarith⟩
  have hsum : Summable (fun n : ℕ => (B * R) * ((n + 1 : ℕ) : ℝ) ^ (-δ - 1)) :=
    ((summable_nat_add_iff 1).mpr
      (Real.summable_nat_rpow.mpr (by linarith : -δ - 1 < -1))).mul_left _
  have hdiff : DifferentiableOn ℂ (fun w : ℂ => ∑' n : ℕ,
      (∑ k ∈ Finset.range (n + 1), c k) *
        (((n + 1 : ℕ) : ℂ) ^ (-w) - ((n + 2 : ℕ) : ℂ) ^ (-w))) U := by
    apply Complex.differentiableOn_tsum_of_summable_norm hsum
    · intro n w _
      exact ((((differentiableAt_id.neg).const_cpow (c := ((n + 1 : ℕ) : ℂ))
        (Or.inl (by exact_mod_cast (show n + 1 ≠ 0 by omega)))).sub
        ((differentiableAt_id.neg).const_cpow (c := ((n + 2 : ℕ) : ℂ))
        (Or.inl (by exact_mod_cast (show n + 2 ≠ 0 by omega))))).const_mul
          (∑ k ∈ Finset.range (n + 1), c k)).differentiableWithinAt
    · exact hU
    · intro n w hw
      rw [norm_mul]
      have hd : ‖((n + 1 : ℕ) : ℂ) ^ (-w) - ((n + 2 : ℕ) : ℂ) ^ (-w)‖ ≤
          ‖w‖ * ((n + 1 : ℕ) : ℝ) ^ (-w.re - 1) := by
        convert norm_cpow_neg_sub_le (hδ.trans hw.1)
          (by positivity : 0 < ((n + 1 : ℕ) : ℝ)) using 1
        norm_num [Nat.cast_add, add_assoc]
      calc
        _ ≤ B * (‖w‖ * ((n + 1 : ℕ) : ℝ) ^ (-w.re - 1)) :=
          mul_le_mul (hB _) hd (norm_nonneg _) hB0
        _ ≤ B * (R * ((n + 1 : ℕ) : ℝ) ^ (-δ - 1)) := by
          apply mul_le_mul_of_nonneg_left _ hB0
          exact mul_le_mul hw.2.le
            (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
              (by linarith [hw.1])) (Real.rpow_nonneg (by positivity) _) hR
        _ = _ := by ring
  exact (hdiff.differentiableAt (hU.mem_nhds hzU)).differentiableWithinAt

/-- A bounded prefix-sum estimate for the cosine coefficients away from the
integer frequencies, including the alternating frequency `x = 1/2`. -/
theorem norm_sum_cos_le {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (M : ℕ) :
    ‖∑ n ∈ Finset.range M, (Real.cos (2 * Real.pi * x * (n + 1)) : ℂ)‖ ≤
      1 / Real.sin (Real.pi * x) := by
  have hs : 0 < Real.sin (Real.pi * x) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hx0)
      (by nlinarith [Real.pi_pos])
  have h := Real.sin_mul_sum_cos M (2 * Real.pi * x) (2 * Real.pi * x)
  have heq (n : ℕ) : 2 * Real.pi * x * (n : ℝ) + 2 * Real.pi * x =
      2 * Real.pi * x * (n + 1) := by ring
  simp_rw [heq] at h
  have hp : (2 * Real.pi * x) / 2 = Real.pi * x := by ring
  rw [hp] at h
  have habs : |Real.sin (Real.pi * x) *
      ∑ n ∈ Finset.range M, Real.cos (2 * Real.pi * x * (n + 1))| ≤ 1 := by
    rw [h, abs_mul]
    exact (mul_le_mul (Real.abs_sin_le_one _) (Real.abs_cos_le_one _)
      (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  rw [abs_mul, abs_of_pos hs] at habs
  rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
  exact (le_div_iff₀ hs).mpr (by simpa only [mul_comm] using habs)

/-- The ordinary cosine Dirichlet series equals its analytic continuation
throughout the positive half-plane, rather than only in absolute convergence. -/
theorem tendsto_sum_cos_cpow {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun M : ℕ => ∑ n ∈ Finset.range M,
      (Real.cos (2 * Real.pi * x * (n + 1)) : ℂ) * ((n + 1 : ℕ) : ℂ) ^ (-z))
      atTop (𝓝 (HurwitzZeta.cosZeta (x : UnitAddCircle) z)) := by
  let c : ℕ → ℂ := fun n => Real.cos (2 * Real.pi * x * (n + 1))
  let F : ℂ → ℂ := fun w => ∑' n : ℕ, (∑ k ∈ Finset.range (n + 1), c k) *
    (((n + 1 : ℕ) : ℂ) ^ (-w) - ((n + 2 : ℕ) : ℂ) ^ (-w))
  have hB : ∀ M, ‖∑ n ∈ Finset.range M, c n‖ ≤ 1 / Real.sin (Real.pi * x) :=
    norm_sum_cos_le hx0 hx1
  have hF : AnalyticOnNhd ℂ F {w : ℂ | 0 < w.re} :=
    (differentiableOn_prefix_differences c hB).analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re)
  have hx : (x : UnitAddCircle) ≠ 0 := by
    intro h
    exact hx0.ne' ((AddCircle.coe_eq_zero_iff_of_mem_Ico ⟨hx0.le, hx1⟩).mp h)
  have hZ : AnalyticOnNhd ℂ (HurwitzZeta.cosZeta (x : UnitAddCircle))
      {w : ℂ | 0 < w.re} :=
    ((HurwitzZeta.differentiable_cosZeta_of_ne_zero hx).differentiableOn).analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re)
  have heq {w : ℂ} (hw : 1 < w.re) : F w = HurwitzZeta.cosZeta (x : UnitAddCircle) w := by
    have hsum := HurwitzZeta.hasSum_nat_cosZeta x hw
    have hshift := (hasSum_nat_add_iff' 1).mpr hsum
    have hw0 : w ≠ 0 := by intro h; simp [h] at hw; linarith
    simp only [Finset.sum_range_one, Nat.cast_zero, Complex.zero_cpow hw0,
      div_zero, sub_zero] at hshift
    have hterm (n : ℕ) :
        (Real.cos (2 * Real.pi * x * ((n + 1 : ℕ) : ℝ)) : ℂ) /
          ((n + 1 : ℕ) : ℂ) ^ w = c n * ((n + 1 : ℕ) : ℂ) ^ (-w) := by
      simp only [c, Nat.cast_add, Nat.cast_one, Complex.cpow_neg, div_eq_mul_inv]
    simp_rw [hterm] at hshift
    exact tendsto_nhds_unique (tendsto_sum_prefix_differences c hB (by linarith : 0 < w.re))
      hshift.tendsto_sum_nat
  have hevent : F =ᶠ[𝓝 (2 : ℂ)] HurwitzZeta.cosZeta (x : UnitAddCircle) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (2 : ℂ) ∈ {w : ℂ | 1 < w.re} by norm_num)] with w hw
    exact heq hw
  have hid := hF.eqOn_of_preconnected_of_eventuallyEq hZ
    (convex_halfSpace_re_gt 0).isPreconnected
    (show (2 : ℂ) ∈ {w : ℂ | 0 < w.re} by norm_num) hevent
  have h := tendsto_sum_prefix_differences c hB hz
  change Tendsto _ _ (𝓝 (F z)) at h
  rwa [hid hz] at h

/-- Complex-valued ordered limit of the real partial sums in the periodic-zeta connection formula. The stronger range `s > 0` is valid. -/
theorem tendsto_sum_cos_rpow_complex (s x : ℝ) (hs : 0 < s)
    (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto (fun M : ℕ => ((∑ n ∈ Finset.range M,
      ((n + 1 : ℕ) : ℝ) ^ (-s) * Real.cos (2 * Real.pi * (n + 1) * x) : ℝ) : ℂ))
      atTop (𝓝 (HurwitzZeta.cosZeta (x : UnitAddCircle) (s : ℂ))) := by
  convert tendsto_sum_cos_cpow hx0 hx1 (z := (s : ℂ)) (by simpa using hs) using 1
  funext M
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [Complex.ofReal_mul, Complex.ofReal_cpow (by positivity)]
  simp only [Complex.ofReal_neg, Complex.ofReal_natCast]
  have ha : 2 * Real.pi * (n + 1) * x = 2 * Real.pi * x * (n + 1) := by ring
  rw [ha, mul_comm]

/-- Ordinary real partial-sum convergence in the periodic-zeta connection formula. -/
theorem tendsto_sum_cos_rpow (s x : ℝ) (hs : 0 < s)
    (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto (fun M : ℕ => ∑ n ∈ Finset.range M,
      ((n + 1 : ℕ) : ℝ) ^ (-s) * Real.cos (2 * Real.pi * (n + 1) * x))
      atTop (𝓝 (HurwitzZeta.cosZeta (x : UnitAddCircle) (s : ℂ)).re) := by
  simpa only [Function.comp_def, Complex.ofReal_re] using
    Complex.continuous_re.continuousAt.tendsto.comp
      (tendsto_sum_cos_rpow_complex s x hs hx0 hx1)

/-- The limiting cosine zeta value at a positive real exponent is real. -/
theorem cosZeta_im_eq_zero (s x : ℝ) (hs : 0 < s)
    (hx0 : 0 < x) (hx1 : x < 1) :
    (HurwitzZeta.cosZeta (x : UnitAddCircle) (s : ℂ)).im = 0 := by
  have h := Complex.continuous_im.continuousAt.tendsto.comp
    (tendsto_sum_cos_rpow_complex s x hs hx0 hx1)
  simp only [Function.comp_def, Complex.ofReal_im] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

end Riesz2.OrderedCosineSeries
