/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.CutoffApproximation
public import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# The endpoint cutoff in the multiplier proof

The restriction to `[0,T]` of the seam cutoff used in Step 1 of
Lemma 2.4. It is the sum of the left and right rescaled
scalar cutoffs. When `4a < T`, their transitions are disjoint. The formula is
defined on the entire real line, where it is smooth and identically one near
either endpoint. Only its restriction to one period is used for integration.
-/

@[expose] public section
noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace Riesz2.EndpointCuspCutoff

open CutoffApproximation

/-- The one-period representative of the cutoff in Step 1 of
Lemma 2.4, with transition width `a`. -/
def cutoff (T a x : ℝ) : ℝ := scalarCutoff (x / a) + scalarCutoff ((T - x) / a)

/-- Smoothness of the endpoint representative in Lemma 2.4. -/
theorem cutoff_contDiff (T a : ℝ) : ContDiff ℝ ∞ (cutoff T a) :=
  (scalarCutoff_contDiff.comp (contDiff_id.div_const a)).add
    (scalarCutoff_contDiff.comp ((contDiff_const.sub contDiff_id).div_const a))

/-- Reflection symmetry of the cutoff in Lemma 2.4. -/
theorem cutoff_reflect (T a x : ℝ) : cutoff T a (T - x) = cutoff T a x := by
  simp only [cutoff, sub_sub_cancel, add_comm]

/-- The cutoff in Lemma 2.4 is one on the left seam neighborhood. -/
theorem cutoff_eq_one_left {T a x : ℝ} (ha : 0 < a) (hTa : 3 * a ≤ T)
    (hx : x ≤ a) : cutoff T a x = 1 := by
  rw [cutoff, scalarCutoff_eq_one ((div_le_one ha).mpr hx),
    scalarCutoff_eq_zero ((le_div_iff₀ ha).mpr (by linarith)), add_zero]

/-- The cutoff in Lemma 2.4 is one on the right seam neighborhood. -/
theorem cutoff_eq_one_right {T a x : ℝ} (ha : 0 < a) (hTa : 3 * a ≤ T)
    (hx : T - a ≤ x) : cutoff T a x = 1 := by
  rw [← cutoff_reflect T a x]
  exact cutoff_eq_one_left ha hTa (by linarith)

/-- The cutoff in Lemma 2.4 vanishes away from both endpoints. -/
theorem cutoff_eq_zero {T a x : ℝ} (ha : 0 < a)
    (hx : 2 * a ≤ x) (hxT : x ≤ T - 2 * a) : cutoff T a x = 0 := by
  rw [cutoff, scalarCutoff_eq_zero ((le_div_iff₀ ha).mpr hx),
    scalarCutoff_eq_zero ((le_div_iff₀ ha).mpr (by linarith)), add_zero]

/-- The cutoff takes values in `[0,1]`, as used in Lemma 2.4. -/
theorem cutoff_mem_Icc {T a : ℝ} (ha : 0 < a) (hTa : 4 * a ≤ T) (x : ℝ) :
    cutoff T a x ∈ Icc (0 : ℝ) 1 := by
  refine ⟨add_nonneg (scalarCutoff_nonneg _) (scalarCutoff_nonneg _), ?_⟩
  by_cases hx : x ≤ 2 * a
  · have hz : scalarCutoff ((T - x) / a) = 0 :=
      scalarCutoff_eq_zero ((le_div_iff₀ ha).mpr (by linarith))
    simpa only [cutoff, hz, add_zero] using scalarCutoff_le_one (x / a)
  · have hz : scalarCutoff (x / a) = 0 :=
      scalarCutoff_eq_zero ((le_div_iff₀ ha).mpr (by linarith))
    simpa only [cutoff, hz, zero_add] using scalarCutoff_le_one ((T - x) / a)

/-- On a period, the cutoff in Lemma 2.4 is one when `ρ ≤ a`. -/
theorem cutoff_eq_one_of_radius_le {T a x : ℝ} (ha : 0 < a) (hTa : 3 * a ≤ T)
    (hx : min x (T - x) ≤ a) : cutoff T a x = 1 := by
  rcases le_total x (T - x) with h | h
  · rw [min_eq_left h] at hx
    exact cutoff_eq_one_left ha hTa hx
  · rw [min_eq_right h] at hx
    exact cutoff_eq_one_right ha hTa (by linarith)

/-- On a period, the cutoff in Lemma 2.4 is zero when `2a ≤ ρ`. -/
theorem cutoff_eq_zero_of_le_radius {T a x : ℝ} (ha : 0 < a)
    (hx : 2 * a ≤ min x (T - x)) : cutoff T a x = 0 := by
  exact cutoff_eq_zero ha (hx.trans (min_le_left _ _))
    (by linarith [hx.trans (min_le_right x (T - x))])

/-- Exact derivative rescaling of the left cutoff in Lemma 2.4. -/
theorem iteratedDeriv_left (j : ℕ) (a x : ℝ) :
    iteratedDeriv j (fun y => scalarCutoff (y / a)) x =
      a⁻¹ ^ j * iteratedDeriv j scalarCutoff (x / a) :=
  iteratedDeriv_scaledCutoff j a x

/-- Exact derivative rescaling of the reflected cutoff in Lemma 2.4. -/
theorem iteratedDeriv_right (j : ℕ) (T a x : ℝ) :
    iteratedDeriv j (fun y => scalarCutoff ((T - y) / a)) x =
      (-1 : ℝ) ^ j * (a⁻¹ ^ j * iteratedDeriv j scalarCutoff ((T - x) / a)) := by
  have he : (fun y => scalarCutoff ((T - y) / a)) =
      (fun y => (fun z => scalarCutoff (z / a)) (T - y)) := rfl
  rw [he, iteratedDeriv_comp_const_sub (f := fun z => scalarCutoff (z / a))]
  simp only [smul_eq_mul, iteratedDeriv_left]

/-- The derivative bounds of Lemma 2.4, uniform in the period and scale. -/
theorem cutoff_derivative_bound (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T a : ℝ, 0 < a → ∀ x : ℝ,
      |iteratedDeriv j (cutoff T a) x| ≤ C / a ^ j := by
  obtain ⟨B, hB, hb⟩ := scalarCutoff_derivative_bound j
  refine ⟨2 * B, by positivity, fun T a ha x => ?_⟩
  have he := iteratedDeriv_add (n := j) (x := x)
    (f := fun y => scalarCutoff (y / a))
    (g := fun y => scalarCutoff ((T - y) / a))
    ((scalarCutoff_contDiff.comp (contDiff_id.div_const a)).of_le (by simp)).contDiffAt
    ((scalarCutoff_contDiff.comp
      ((contDiff_const.sub contDiff_id).div_const a)).of_le (by simp)).contDiffAt
  change |iteratedDeriv j ((fun y => scalarCutoff (y / a)) +
    (fun y => scalarCutoff ((T - y) / a))) x| ≤ _
  rw [he]
  have hl : |iteratedDeriv j (fun y => scalarCutoff (y / a)) x| ≤ a⁻¹ ^ j * B := by
    rw [iteratedDeriv_left, abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hb _) (by positivity)
  have hr : |iteratedDeriv j (fun y => scalarCutoff ((T - y) / a)) x| ≤ a⁻¹ ^ j * B := by
    rw [iteratedDeriv_right, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hb _) (by positivity)
  calc
    _ ≤ _ := abs_add_le _ _
    _ ≤ a⁻¹ ^ j * B + a⁻¹ ^ j * B := add_le_add hl hr
    _ = 2 * B / a ^ j := by rw [div_eq_mul_inv, inv_pow]; ring

/-- Positive derivatives of the cutoff in Lemma 2.4 have annular support. -/
theorem cutoff_derivative_support {T a : ℝ} (ha : 0 < a) (hTa : 3 * a ≤ T)
    (j : ℕ) (hj : 0 < j) :
    Function.support (iteratedDeriv j (cutoff T a)) ⊆
      {x | a ≤ min x (T - x) ∧ min x (T - x) ≤ 2 * a} := by
  intro x hx
  by_contra hn
  have he : min x (T - x) < a ∨ 2 * a < min x (T - x) := by
    simpa only [mem_ofPred_eq, not_and_or, not_le] using hn
  rcases he with he | he
  · have hev : cutoff T a =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      have hc : Continuous (fun y : ℝ => min y (T - y)) :=
        continuous_id.min (continuous_const.sub continuous_id)
      filter_upwards [hc.continuousAt.eventually (gt_mem_nhds he)] with y hy
      exact cutoff_eq_one_of_radius_le ha hTa hy.le
    exact hx (by rw [hev.iteratedDeriv_eq j, iteratedDeriv_const]; simp [hj.ne'])
  · have hev : cutoff T a =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      have hc : Continuous (fun y : ℝ => min y (T - y)) :=
        continuous_id.min (continuous_const.sub continuous_id)
      filter_upwards [hc.continuousAt.eventually (lt_mem_nhds he)] with y hy
      exact cutoff_eq_zero_of_le_radius ha hy.le
    exact hx (by rw [hev.iteratedDeriv_eq j, iteratedDeriv_const]; simp [hj.ne'])

/-- A positive cutoff derivative costs at most `Cρ⁻ʲ`, exactly as in
Lemma 2.4, Step 1. The annular support is essential here. -/
theorem cutoff_derivative_radius_bound (j : ℕ) (hj : 0 < j) :
    ∃ C : ℝ, 0 < C ∧ ∀ T a : ℝ, 0 < a → 3 * a ≤ T →
      ∀ x ∈ Ioo 0 T,
        |iteratedDeriv j (cutoff T a) x| ≤ C / (min x (T - x)) ^ j := by
  obtain ⟨D, hD, hb⟩ := cutoff_derivative_bound j
  refine ⟨D * 2 ^ j, by positivity, fun T a ha hTa x hx => ?_⟩
  have hρ : 0 < min x (T - x) := lt_min hx.1 (by linarith [hx.2])
  by_cases hz : iteratedDeriv j (cutoff T a) x = 0
  · rw [hz, abs_zero]
    positivity
  · have hs := (cutoff_derivative_support ha hTa j hj hz).2
    have hp := pow_le_pow_left₀ hρ.le hs j
    rw [mul_pow] at hp
    apply (le_div_iff₀ (by positivity : 0 < min x (T - x) ^ j)).mpr
    calc
      _ ≤ (D / a ^ j) * min x (T - x) ^ j :=
        mul_le_mul_of_nonneg_right (hb T a ha x) (by positivity)
      _ ≤ (D / a ^ j) * (2 ^ j * a ^ j) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = D * 2 ^ j := by field_simp

/-- All derivatives of the far cutoff in Lemma 2.4, including
order zero, have the radius envelope required by Leibniz' rule. -/
theorem farCutoff_derivative_radius_bound (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T a : ℝ, 0 < a → 4 * a ≤ T →
      ∀ x ∈ Ioo 0 T,
        |iteratedDeriv j (fun y => 1 - cutoff T a y) x| ≤
          C / (min x (T - x)) ^ j := by
  by_cases hj : j = 0
  · subst j
    refine ⟨1, zero_lt_one, fun T a ha hTa x _ => ?_⟩
    have hc := cutoff_mem_Icc ha hTa x
    simpa only [iteratedDeriv_zero, pow_zero, div_one,
      abs_of_nonneg (sub_nonneg.mpr hc.2)] using (by linarith [hc.1] : 1 - cutoff T a x ≤ 1)
  · obtain ⟨C, hC, hb⟩ := cutoff_derivative_radius_bound j (Nat.pos_of_ne_zero hj)
    refine ⟨C, hC, fun T a ha hTa x hx => ?_⟩
    rw [iteratedDeriv_const_sub (Nat.pos_of_ne_zero hj), iteratedDeriv_neg, abs_neg]
    exact hb T a ha (by linarith) x hx

/-- The far part of the decomposition in Step 1 of Lemma 2.4. -/
def farPart (T a : ℝ) (F : ℝ → ℂ) (x : ℝ) : ℂ := (1 - cutoff T a x) • F x

/-- Exact near/far decomposition from Lemma 2.4. -/
theorem near_add_far (T a : ℝ) (F : ℝ → ℂ) (x : ℝ) :
    cutoff T a x • F x + farPart T a F x = F x := by
  rw [farPart, ← add_smul]
  simp

/-- The far part in Lemma 2.4 vanishes on both seam neighborhoods. -/
theorem farPart_eq_zero {T a x : ℝ} (ha : 0 < a) (hTa : 3 * a ≤ T)
    (F : ℝ → ℂ) (hx : min x (T - x) ≤ a) : farPart T a F x = 0 := by
  rw [farPart, cutoff_eq_one_of_radius_le ha hTa hx, sub_self, zero_smul]

/-- The far part in Lemma 2.4 agrees with the symbol away from the cutoff. -/
theorem farPart_eq_self {T a x : ℝ} (ha : 0 < a) (F : ℝ → ℂ)
    (hx : 2 * a ≤ min x (T - x)) : farPart T a F x = F x := by
  rw [farPart, cutoff_eq_zero_of_le_radius ha hx, sub_zero, one_smul]

/-- Every far-product derivative vanishes inside the removed seam neighborhoods
in Lemma 2.4, Step 1, without any regularity assumption on the symbol. -/
theorem farPart_derivative_eq_zero {T a x : ℝ} (ha : 0 < a) (hTa : 3 * a ≤ T)
    (F : ℝ → ℂ) (j : ℕ) (hx : min x (T - x) < a) :
    iteratedDeriv j (farPart T a F) x = 0 := by
  have he : farPart T a F =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
    have hc : Continuous (fun y : ℝ => min y (T - y)) :=
      continuous_id.min (continuous_const.sub continuous_id)
    filter_upwards [hc.continuousAt.eventually (gt_mem_nhds hx)] with y hy
    exact farPart_eq_zero ha hTa F hy.le
  rw [he.iteratedDeriv_eq j, iteratedDeriv_const]
  split_ifs <;> rfl

/-- Every derivative of the far part in Lemma 2.4 vanishes at the seams. -/
theorem farPart_endpoint_derivatives {T a : ℝ} (ha : 0 < a) (hTa : 3 * a ≤ T)
    (F : ℝ → ℂ) (j : ℕ) :
    iteratedDeriv j (farPart T a F) 0 = 0 ∧
      iteratedDeriv j (farPart T a F) T = 0 := by
  have hleft : farPart T a F =ᶠ[𝓝 0] (fun _ => (0 : ℂ)) := by
    filter_upwards [gt_mem_nhds ha] with y hy
    exact farPart_eq_zero ha hTa F ((min_le_left _ _).trans hy.le)
  have hright : farPart T a F =ᶠ[𝓝 T] (fun _ => (0 : ℂ)) := by
    filter_upwards [lt_mem_nhds (show T - a < T by linarith)] with y hy
    exact farPart_eq_zero ha hTa F ((min_le_right _ _).trans (by linarith))
  constructor
  · rw [hleft.iteratedDeriv_eq j, iteratedDeriv_const]; split_ifs <;> rfl
  · rw [hright.iteratedDeriv_eq j, iteratedDeriv_const]; split_ifs <;> rfl

/-- Removing the seam makes the far part in Lemma 2.4 smooth
at every point of the closed integration interval. -/
theorem farPart_contDiffAt {T a : ℝ} {r : ℕ} (ha : 0 < a) (hTa : 3 * a ≤ T)
    {F : ℝ → ℂ} (hF : ContDiffOn ℝ r F (Ioo 0 T))
    {x : ℝ} (_hx : x ∈ Icc 0 T) : ContDiffAt ℝ r (farPart T a F) x := by
  by_cases hnear : min x (T - x) < a
  · have he : farPart T a F =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
      have hc : Continuous (fun y : ℝ => min y (T - y)) :=
        continuous_id.min (continuous_const.sub continuous_id)
      filter_upwards [hc.continuousAt.eventually (gt_mem_nhds hnear)] with y hy
      exact farPart_eq_zero ha hTa F hy.le
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hm : a ≤ min x (T - x) := le_of_not_gt hnear
    have hi : x ∈ Ioo 0 T := ⟨ha.trans_le (hm.trans (min_le_left _ _)), by
      have := hm.trans (min_le_right x (T - x)); linarith⟩
    exact (contDiffAt_const.sub ((cutoff_contDiff T a).of_le (by simp)).contDiffAt).smul
      (hF.contDiffAt (isOpen_Ioo.mem_nhds hi))

end Riesz2.EndpointCuspCutoff
