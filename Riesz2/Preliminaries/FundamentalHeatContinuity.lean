/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.FundamentalHeatIntegral
import all Riesz1.Kernel.FundamentalHeatIntegral

/-!
# Continuity of the heat integral before evaluating the images

For the proof of manuscript Lemma 2.3, we dominate the weighted heat kernel
locally uniformly in space, separately at small and large times. This proves
continuity of the improper time integral without its finite-part evaluation.
-/

public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace Riesz2

/-- Lemma 2.3, heat step: the Gaussian lattice sum at time two is bounded
on a compact spatial interval, by continuity of the fixed-time heat kernel. -/
lemma fundamentalHeat_gaussian_bound (a b : ℝ) :
    ∃ C : ℝ, ∀ x ∈ Icc a b,
      ∑' k : ℤ, Real.exp (-(x - k) ^ 2 / (4 * 2)) ≤ C := by
  have hc : Continuous (fun x : ℝ =>
      (4 * π * 2) ^ (1 / 2 : ℝ) * Riesz1.circleHeatKernel 2 two_pos x) :=
    (Riesz1.continuous_circleHeatKernel 2 two_pos).const_mul _
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hc.continuousOn
  exact ⟨C, fun x hx => by
    rw [Riesz1.tsum_gauss_eq_rpow_mul_heat two_pos]
    exact hC (mem_image_of_mem _ hx)⟩

/-- Lemma 2.3, heat step: on a compact interval inside `(0,1)` the
Gaussian image sum has a uniform exponentially small bound at small times. -/
lemma fundamentalHeat_gaussian_small {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    ∃ C : ℝ, ∀ x ∈ Icc a b, ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∑' k : ℤ, Real.exp (-(x - k) ^ 2 / (4 * t)) ≤
        Real.exp (-(min a (1 - b)) ^ 2 / (8 * t)) * C := by
  obtain ⟨C, hC⟩ := fundamentalHeat_gaussian_bound a b
  refine ⟨C, fun x hx t ht ht1 => ?_⟩
  have hx0 : 0 < x := ha.trans_le hx.1
  have hx1 : x < 1 := hx.2.trans_lt hb
  have hd : min a (1 - b) ≤ min x (1 - x) :=
    min_le_min hx.1 (by linarith [hx.2])
  have hd0 : 0 ≤ min a (1 - b) := le_min ha.le (by linarith)
  have he : Real.exp (-(min x (1 - x)) ^ 2 / (8 * t)) ≤
      Real.exp (-(min a (1 - b)) ^ 2 / (8 * t)) := by
    apply Real.exp_le_exp.2
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  calc
    _ ≤ ∑' k : ℤ, Real.exp (-(min x (1 - x)) ^ 2 / (8 * t)) *
        Real.exp (-(x - k) ^ 2 / (4 * 2)) :=
      (Riesz1.summable_gauss_int t ht x).tsum_le_tsum
        (fun k => Riesz1.exp_gauss_le_exp_mul hx0 hx1 ht ht1 k)
        ((Riesz1.summable_gauss_width_two x).mul_left _)
    _ = Real.exp (-(min x (1 - x)) ^ 2 / (8 * t)) *
        ∑' k : ℤ, Real.exp (-(x - k) ^ 2 / (4 * 2)) := tsum_mul_left
    _ ≤ Real.exp (-(min a (1 - b)) ^ 2 / (8 * t)) * C :=
      (mul_le_mul_of_nonneg_right he (tsum_nonneg fun _ => (Real.exp_pos _).le)).trans
        (mul_le_mul_of_nonneg_left (hC x hx) (Real.exp_pos _).le)

/-- Lemma 2.3, heat step: the local small-time envelope is integrable.
The collision distance `d` is strictly positive. The second power is integrable
at zero precisely because `s < 1`. -/
lemma fundamentalHeat_small_integrable (s : Riesz1.RieszExponent) {d : ℝ}
    (hd : 0 < d) (C : ℝ) :
    IntegrableOn (fun t : ℝ =>
      C * (t ^ (-1 - s.val / 2) * Real.exp (-d ^ 2 / (8 * t))) +
        t ^ (-(1 + s.val) / 2)) (Ioc 0 1) := by
  have hgauss := Riesz1.integrableOn_rpow_neg_exp_div_Ioi
    (α := s.val / 2) (c := d ^ 2 / 8) (by linarith [s.2.1]) (by positivity)
  have hg : IntegrableOn (fun t : ℝ =>
      t ^ (-1 - s.val / 2) * Real.exp (-d ^ 2 / (8 * t))) (Ioc 0 1) := by
    refine (hgauss.mono_set Ioc_subset_Ioi_self).congr_fun (fun t _ => ?_) measurableSet_Ioc
    simp only [neg_div, div_div]
  have hp : IntegrableOn (fun t : ℝ => t ^ (-(1 + s.val) / 2)) (Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
      (intervalIntegral.intervalIntegrable_rpow' (by linarith [s.2.2]))
  exact (hg.const_mul C).add hp

/-- Lemma 2.3, heat step: the weighted heat integrand has a uniform
integrable small-time envelope on every compact subinterval of `(0,1)`. -/
lemma fundamentalHeat_small_bound (s : Riesz1.RieszExponent) {a b : ℝ}
    (ha : 0 < a) (hb : b < 1) :
    ∃ C : ℝ, ∀ x ∈ Icc a b, ∀ t : ℝ, 0 < t → t ≤ 1 →
      ‖(HurwitzZeta.cosKernel (x : UnitAddCircle) (4 * π * t) - 1) *
        t ^ (-(1 + s.val) / 2)‖ ≤
      C * (t ^ (-1 - s.val / 2) *
        Real.exp (-(min a (1 - b)) ^ 2 / (8 * t))) + t ^ (-(1 + s.val) / 2) := by
  obtain ⟨C, hC⟩ := fundamentalHeat_gaussian_small ha hb
  refine ⟨(4 * π) ^ (-(1 / 2 : ℝ)) * C, fun x hx t ht ht1 => ?_⟩
  have hW := Riesz1.cosKernel_four_pi_nonneg ht (x : UnitAddCircle)
  have habs : |HurwitzZeta.cosKernel (x : UnitAddCircle) (4 * π * t) - 1| ≤
      HurwitzZeta.cosKernel (x : UnitAddCircle) (4 * π * t) + 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hpow : (4 * π * t) ^ (-(1 / 2 : ℝ)) * t ^ (-(1 + s.val) / 2) =
      (4 * π) ^ (-(1 / 2 : ℝ)) * t ^ (-1 - s.val / 2) := by
    rw [Real.mul_rpow (by positivity) ht.le, mul_assoc, ← Real.rpow_add ht]
    congr 2
    ring
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.le _)]
  calc
    _ ≤ (HurwitzZeta.cosKernel (x : UnitAddCircle) (4 * π * t) + 1) *
        t ^ (-(1 + s.val) / 2) :=
      mul_le_mul_of_nonneg_right habs (Real.rpow_nonneg ht.le _)
    _ = ((4 * π * t) ^ (-(1 / 2 : ℝ)) *
        ∑' k : ℤ, Real.exp (-(x - k) ^ 2 / (4 * t))) *
        t ^ (-(1 + s.val) / 2) + t ^ (-(1 + s.val) / 2) := by
      rw [Riesz1.cosKernel_four_pi_eq_circleHeatKernel ht x,
        Riesz1.circleHeatKernel_eq_gauss]
      ring
    _ ≤ ((4 * π * t) ^ (-(1 / 2 : ℝ)) *
        (Real.exp (-(min a (1 - b)) ^ 2 / (8 * t)) * C)) *
        t ^ (-(1 + s.val) / 2) + t ^ (-(1 + s.val) / 2) := by
      gcongr
      exact hC x hx t ht ht1
    _ = _ := by
      calc
        _ = ((4 * π * t) ^ (-(1 / 2 : ℝ)) * t ^ (-(1 + s.val) / 2)) *
            (Real.exp (-(min a (1 - b)) ^ 2 / (8 * t)) * C) +
            t ^ (-(1 + s.val) / 2) := by ring
        _ = _ := by rw [hpow]; ring

/-- Lemma 2.3, heat step: measurability of each time section follows
from positive-time joint continuity, without evaluating its integral. -/
lemma fundamentalHeat_time_measurable (s : Riesz1.RieszExponent) (x : ℝ) :
    AEStronglyMeasurable (fun t : ℝ =>
      (HurwitzZeta.cosKernel (x : UnitAddCircle) (4 * π * t) - 1) *
        t ^ (-(1 + s.val) / 2)) (volume.restrict (Ioi 0)) := by
  have hW : ContinuousOn (fun t : ℝ =>
      HurwitzZeta.cosKernel (x : UnitAddCircle) (4 * π * t)) (Ioi 0) := by
    exact (Complex.continuous_re.comp_continuousOn
      Riesz1.continuousOn_cosKernel_four_pi).comp
        (continuous_const.prodMk continuous_id).continuousOn (fun _ ht => ht)
  exact ((hW.sub continuousOn_const).mul
    (continuousOn_id.rpow_const (fun _ ht => Or.inl (ne_of_gt ht)))).aestronglyMeasurable
      measurableSet_Ioi

/-- Lemma 2.3, before the image evaluation: the improper heat time
integral is continuous off collisions. Small times are dominated by a Gaussian
envelope on a compact neighborhood. Large times use exponential heat decay. -/
theorem fundamentalHeat_continuousOn (s : Riesz1.RieszExponent) :
    ContinuousOn (fun x : ℝ => Riesz1.heatIntegral s (x : UnitAddCircle)) (Ioo 0 1) := by
  intro x hx
  let a := x / 2
  let b := (x + 1) / 2
  have ha : 0 < a := by dsimp [a]; linarith [hx.1]
  have hb : b < 1 := by dsimp [b]; linarith [hx.2]
  have hax : a < x := by dsimp [a]; linarith [hx.1]
  have hxb : x < b := by dsimp [b]; linarith [hx.2]
  obtain ⟨C, hC⟩ := fundamentalHeat_small_bound s ha hb
  let B : ℝ → ℝ := fun t => if t ≤ 1 then
    C * (t ^ (-1 - s.val / 2) * Real.exp (-(min a (1 - b)) ^ 2 / (8 * t))) +
      t ^ (-(1 + s.val) / 2)
    else (HurwitzZeta.cosKernel 0 (4 * π * 1) - 1) *
      Real.exp (-(4 * π ^ 2) * (t - 1)) * t ^ (-(1 + s.val) / 2)
  have hB : IntegrableOn B (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1), integrableOn_union]
    constructor
    · exact (fundamentalHeat_small_integrable s (d := min a (1 - b))
        (lt_min ha (by linarith)) C).congr_fun
        (fun t ht => by simp [B, ht.2]) measurableSet_Ioc
    · exact ((Riesz1.integrableOn_heat_decay s
        (HurwitzZeta.cosKernel 0 (4 * π * 1) - 1)).mono_set
        (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).congr_fun
        (fun t ht => by simp [B, not_le.mpr ht]) measurableSet_Ioi
  have hlocal : ∀ᶠ y in 𝓝 x, y ∈ Icc a b :=
    Filter.mem_of_superset (Ioo_mem_nhds hax hxb) Ioo_subset_Icc_self
  have hcont : ContinuousAt (fun y : ℝ => ∫ t in Ioi (0 : ℝ),
      (HurwitzZeta.cosKernel (y : UnitAddCircle) (4 * π * t) - 1) *
        t ^ (-(1 + s.val) / 2)) x := by
    refine continuousAt_of_dominated (bound := B)
      (Filter.Eventually.of_forall (fundamentalHeat_time_measurable s)) ?_ hB ?_
    · filter_upwards [hlocal] with y hy
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      by_cases ht1 : t ≤ 1
      · simpa [B, ht1] using hC y hy t ht ht1
      · dsimp [B]
        rw [ite_eq_right (by exact ht1), abs_mul,
          abs_of_nonneg (Real.rpow_nonneg (le_of_lt ht) _)]
        have h := mul_le_mul_of_nonneg_right
          (Riesz1.abs_cosKernel_sub_one_le_tail (le_of_lt (not_le.mp ht1))
            (y : UnitAddCircle)) (Real.rpow_nonneg (le_of_lt ht) (-(1 + s.val) / 2))
        simpa only [mul_comm] using h
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (((Riesz1.continuous_cosKernel_four_pi ht).comp
        (AddCircle.continuous_mk' (1 : ℝ))).sub continuous_const).continuousAt.mul
          continuousAt_const
  exact (hcont.const_mul (Riesz1.rieszConstant s / Real.Gamma ((1 - s.val) / 2))).continuousWithinAt

end Riesz2

end
