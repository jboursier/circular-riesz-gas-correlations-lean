/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.CutoffApproximationPart2
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Extending a smooth Poincaré inequality to an open interval

The bounded locally C¹ observable is first clamped to a compact subinterval,
then mollified in the weighted form norm. This supplies the analytic passage
in Lemma 6.5, preserving the Poincaré coefficient.
-/

public section
noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff

namespace Riesz2.BoundedIntervalPoincare

/-- Strong L² convergence preserves the uncentered second moment. -/
theorem square_tendsto {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {u : ℕ → X → ℝ} {f : X → ℝ} (hu : ∀ k, MemLp (u k) 2 μ) (hf : MemLp f 2 μ)
    (ht : Tendsto (fun k => (hu k).toLp (u k)) atTop (𝓝 (hf.toLp f))) :
    Tendsto (fun k => ∫ x, (u k x)^2 ∂μ) atTop (𝓝 (∫ x, (f x)^2 ∂μ)) := by
  have he (g : X → ℝ) (hg : MemLp g 2 μ) :
      (∫ x, (g x)^2 ∂μ) = ‖hg.toLp g‖^2 := by
    rw [← real_inner_self_eq_norm_sq]
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    simp only [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  simpa only [← he] using ht.norm.pow 2

/-- A real Poincaré inequality passes to a strong limit in both parts of
its form norm. This general helper has no regularity assumptions. -/
theorem form_limit {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {u d : ℕ → ℝ → ℝ} {f g : ℝ → ℝ} {A : ℝ}
    (hu : ∀ k, MemLp (u k) 2 μ) (hd : ∀ k, MemLp (d k) 2 μ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (ht : Tendsto (fun k => (hu k).toLp (u k)) atTop (𝓝 (hf.toLp f)))
    (hdt : Tendsto (fun k => (hd k).toLp (d k)) atTop (𝓝 (hg.toLp g)))
    (hb : ∀ k, (∫ x, (u k x - ∫ y, u k y ∂μ)^2 ∂μ) ≤ A * ∫ x, (d k x)^2 ∂μ) :
    (∫ x, (f x - ∫ y, f y ∂μ)^2 ∂μ) ≤ A * ∫ x, (g x)^2 ∂μ := by
  have hz := (Riesz1.WeightedSobolev.tendsto_toLp_iff_lintegral_sq u hu f hf).mp ht
  have hr := Riesz1.WeightedSobolev.tendsto_integral_sq_of_lintegral
    (fun k => ((hu k).sub hf).aestronglyMeasurable) hz
  exact le_of_tendsto_of_tendsto
    (Riesz1.WeightedSobolev.tendsto_integral_sub_mean_sq hf hu hr)
    ((square_tendsto hd hg hdt).const_mul A) (Eventually.of_forall hb)

/-- Local C¹ regularity makes each compact clamp globally Lipschitz. -/
theorem clamped_lipschitz {f : ℝ → ℝ} {lo hi a b : ℝ}
    (hf : ContDiffOn ℝ 1 f (Ioo lo hi)) (ha : lo < a) (hb : b < hi) (hab : a ≤ b) :
    ∃ K : ℝ≥0, LipschitzWith K (IccExtend hab (fun y => f y.val)) := by
  have hsub : Icc a b ⊆ Ioo lo hi := fun x hx => ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩
  have hc : ContinuousOn (deriv f) (Icc a b) :=
    (hf.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)).mono hsub
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  let K : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  have hLip : LipschitzOnWith K f (Icc a b) :=
    (convex_Icc a b).lipschitzOnWith_of_nnnorm_deriv_le
      (fun x hx => (hf.contDiffAt (isOpen_Ioo.mem_nhds (hsub hx))).differentiableAt (by simp))
      (fun x hx => by exact_mod_cast (hB x hx).trans (le_max_left B 0))
  refine ⟨K, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (hLip.dist_le_mul _ (projIcc a b hab x).property _ (projIcc a b hab y).property).trans
  have hc : dist ((projIcc a b hab x) : ℝ) ((projIcc a b hab y) : ℝ) ≤ dist x y := by
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq] using
      (LipschitzWith.projIcc hab).dist_le_mul x y
  exact mul_le_mul_of_nonneg_left hc K.property

/-- Off the two endpoints, the derivative of the clamp is exactly the
truncation of the original derivative. -/
theorem clamped_deriv {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) {x : ℝ}
    (ha : x ≠ a) (hb : x ≠ b) :
    deriv (IccExtend hab (fun y => f y.val)) x = (Ioo a b).indicator (deriv f) x := by
  by_cases hx : x ∈ Ioo a b
  · rw [indicator_of_mem hx]
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    simp only [IccExtend, Function.comp_def, projIcc_of_mem hab ⟨hy.1.le, hy.2.le⟩]
  · have he : x < a ∨ b < x := by
      simp only [mem_Ioo, not_and_or, not_lt] at hx
      rcases hx with h | h
      · exact Or.inl (lt_of_le_of_ne h ha)
      · exact Or.inr (lt_of_le_of_ne h (Ne.symm hb))
    rw [indicator_of_notMem hx]
    rcases he with h | h
    · have heq : (IccExtend hab (fun y => f y.val)) =ᶠ[𝓝 x] fun _ => f a := by
        filter_upwards [eventually_lt_nhds h] with y hy
        simp only [IccExtend, Function.comp_def, projIcc_of_le_left hab hy.le]
      rw [heq.deriv_eq, deriv_const]
    · have heq : (IccExtend hab (fun y => f y.val)) =ᶠ[𝓝 x] fun _ => f b := by
        filter_upwards [eventually_gt_nhds h] with y hy
        simp only [IccExtend, Function.comp_def, projIcc_of_right_le hab hy.le]
      rw [heq.deriv_eq, deriv_const]

/-- Smooth Poincaré passes to each compact clamp by weighted mollification. -/
theorem clamp_poincare {w f : ℝ → ℝ} {lo hi a b A M : ℝ}
    (hf : ContDiffOn ℝ 1 f (Ioo lo hi))
    (hw : ContinuousOn w (Ioo lo hi)) (hp : ∀ x ∈ Ioo lo hi, 0 < w x)
    (ha : lo < a) (hb : b < hi) (hab : a ≤ b)
    (hbound : ∀ x ∈ Ioo lo hi, |f x| ≤ M)
    (hA : 0 ≤ A)
    [IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (w x)))]
    (hd : MemLp (deriv f) 2 (volume.withDensity (fun x => ENNReal.ofReal (w x))))
    (hP : ∀ u : ℝ → ℝ, ContDiff ℝ ∞ u →
      MemLp u 2 (volume.withDensity (fun x => ENNReal.ofReal (w x))) →
      MemLp (deriv u) 2 (volume.withDensity (fun x => ENNReal.ofReal (w x))) →
      (∫ x, (u x - ∫ y, u y ∂volume.withDensity (fun x => ENNReal.ofReal (w x)))^2
        ∂volume.withDensity (fun x => ENNReal.ofReal (w x))) ≤
      A * ∫ x, (deriv u x)^2 ∂volume.withDensity (fun x => ENNReal.ofReal (w x))) :
    (∫ x, ((IccExtend hab (fun y => f y.val)) x - ∫ y, (IccExtend hab (fun y => f y.val)) y
      ∂volume.withDensity (fun x => ENNReal.ofReal (w x)))^2
      ∂volume.withDensity (fun x => ENNReal.ofReal (w x))) ≤
      A * ∫ x, (deriv f x)^2 ∂volume.withDensity (fun x => ENNReal.ofReal (w x)) := by
  let μ := volume.withDensity (fun x => ENNReal.ofReal (w x))
  let F := IccExtend hab (fun y => f y.val)
  obtain ⟨K,hK⟩ := clamped_lipschitz hf ha hb hab
  have hbF (x : ℝ) : |F x| ≤ M := hbound _
    ⟨ha.trans_le (projIcc a b hab x).property.1, (projIcc a b hab x).property.2.trans_lt hb⟩
  have hder : deriv F =ᵐ[μ] (Ioo a b).indicator (deriv f) := by
    filter_upwards [μ.ae_ne a, μ.ae_ne b] with x hxa hxb
    exact clamped_deriv hab hxa hxb
  have hFd : MemLp (deriv F) 2 μ := (memLp_congr_ae hder).mpr (MemLp.indicator measurableSet_Ioo.nullMeasurableSet hd)
  have hF : MemLp F 2 μ := MemLp.of_bound hK.continuous.aestronglyMeasurable M
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hbF x)
  let r := min (a-lo) (hi-b) / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hsmall : Icc (a-r) (b+r) ⊆ Ioo lo hi := by
    intro x hx
    have h1 := min_le_left (a-lo) (hi-b)
    have h2 := min_le_right (a-lo) (hi-b)
    dsimp [r] at hx
    constructor <;> linarith [hx.1,hx.2]
  have hs : Function.support (deriv F) ⊆ Icc a b := by
    intro x hx
    by_contra hnot
    have hne : x ≠ a ∧ x ≠ b := by constructor <;> intro he <;> subst x <;> exact hnot (by constructor <;> linarith)
    have hz := clamped_deriv (f := f) hab hne.1 hne.2
    rw [indicator_of_notMem (fun h => hnot ⟨h.1.le,h.2.le⟩)] at hz
    exact hx hz
  obtain ⟨ρ,hρ⟩ := Riesz1.exists_isMollifier
  obtain ⟨φ,hsφ,hbφ,_hsupp,hiφ,ht,hdt⟩ :=
    CutoffApproximation.exists_smooth_form_approximation_of_density hρ hK.continuous
      (fun u v => hK.lipschitzOnWith.absolutelyContinuousOnInterval) hbF hr hs
      (hw.mono hsmall) (fun x hx => hp x ⟨ha.trans_le hx.1,hx.2.trans_lt hb⟩) hFd
  have ht' := (Riesz1.WeightedSobolev.tendsto_toLp_iff_lintegral_sq φ
    (fun k => (hiφ k).1) F hF).mpr ht
  have hdt' := (Riesz1.WeightedSobolev.tendsto_toLp_iff_lintegral_sq (fun k => deriv (φ k))
    (fun k => (hiφ k).2) (deriv F) hFd).mpr hdt
  apply (form_limit (fun k => (hiφ k).1) (fun k => (hiφ k).2) hF hFd ht' hdt'
    (fun k => hP (φ k) (hsφ k) (hiφ k).1 (hiφ k).2)).trans
  apply mul_le_mul_of_nonneg_left _ hA
  apply integral_mono_ae hFd.integrable_sq hd.integrable_sq
  filter_upwards [hder] with x hx
  rw [hx]
  by_cases h : x ∈ Ioo a b
  · simp only [indicator_of_mem h,le_refl]
  · simp only [indicator_of_notMem h,zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    positivity

/-- A bounded C¹ function on an open interval satisfies every smooth
Poincaré inequality of its supported probability density, with the exact
same coefficient. Endpoint clamping and weighted mollification introduce
no loss. -/
theorem on_open_interval {w f : ℝ → ℝ} {lo hi A M : ℝ} (hlohi : lo < hi)
    (hf : ContDiffOn ℝ 1 f (Ioo lo hi))
    (hw : ContinuousOn w (Ioo lo hi)) (hp : ∀ x ∈ Ioo lo hi, 0 < w x)
    (hbound : ∀ x ∈ Ioo lo hi, |f x| ≤ M) (hA : 0 ≤ A)
    [IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (w x)))]
    (hsupp : ∀ᵐ x ∂volume.withDensity (fun x => ENNReal.ofReal (w x)), x ∈ Ioo lo hi)
    (hfm : AEStronglyMeasurable f (volume.withDensity (fun x => ENNReal.ofReal (w x))))
    (hd : MemLp (deriv f) 2 (volume.withDensity (fun x => ENNReal.ofReal (w x))))
    (hP : ∀ u : ℝ → ℝ, ContDiff ℝ ∞ u →
      MemLp u 2 (volume.withDensity (fun x => ENNReal.ofReal (w x))) →
      MemLp (deriv u) 2 (volume.withDensity (fun x => ENNReal.ofReal (w x))) →
      (∫ x, (u x - ∫ y, u y ∂volume.withDensity (fun x => ENNReal.ofReal (w x)))^2
        ∂volume.withDensity (fun x => ENNReal.ofReal (w x))) ≤
      A * ∫ x, (deriv u x)^2 ∂volume.withDensity (fun x => ENNReal.ofReal (w x))) :
    MemLp f 2 (volume.withDensity (fun x => ENNReal.ofReal (w x))) ∧
      (∫ x, (f x - ∫ y, f y ∂volume.withDensity (fun x => ENNReal.ofReal (w x)))^2
        ∂volume.withDensity (fun x => ENNReal.ofReal (w x))) ≤
      A * ∫ x, (deriv f x)^2 ∂volume.withDensity (fun x => ENNReal.ofReal (w x)) := by
  let μ := volume.withDensity (fun x => ENNReal.ofReal (w x))
  let r (k : ℕ) : ℝ := (hi-lo)/(k+3)
  have hr k : 0 < r k := div_pos (sub_pos.mpr hlohi) (by positivity)
  have hr2 k : 2*r k < hi-lo := by
    dsimp [r]
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : (0 : ℝ) < k+3)]
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  let a := fun k => lo+r k
  let b := fun k => hi-r k
  have ha k : lo < a k := by dsimp [a]; linarith [hr k]
  have hb k : b k < hi := by dsimp [b]; linarith [hr k]
  have hab k : a k ≤ b k := by dsimp [a,b]; linarith [hr2 k]
  let F := fun k => IccExtend (hab k) (fun y => f y.val)
  have hFbound k x : |F k x| ≤ M := hbound _
    ⟨(ha k).trans_le (projIcc _ _ (hab k) x).property.1,
      (projIcc _ _ (hab k) x).property.2.trans_lt (hb k)⟩
  have hF k : MemLp (F k) 2 μ := by
    obtain ⟨K,hK⟩ := clamped_lipschitz hf (ha k) (hb k) (hab k)
    exact MemLp.of_bound hK.continuous.aestronglyMeasurable M
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hFbound k x)
  have hfm' : MemLp f 2 μ := MemLp.of_bound hfm M (by
    filter_upwards [hsupp] with x hx
    simpa only [Real.norm_eq_abs] using hbound x hx)
  have hrlim : Tendsto r atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop ((tendsto_atTop_add_const_right atTop 3 tendsto_natCast_atTop_atTop))
  have halim : Tendsto a atTop (𝓝 lo) := by simpa only [add_zero] using hrlim.const_add lo
  have hblim : Tendsto b atTop (𝓝 hi) := by simpa only [sub_zero] using hrlim.const_sub hi
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun k => F k x) atTop (𝓝 (f x)) := by
    filter_upwards [hsupp] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [(tendsto_order.mp halim).2 x hx.1, (tendsto_order.mp hblim).1 x hx.2] with k hk1 hk2
    simp only [F,IccExtend,Function.comp_def,projIcc_of_mem _ ⟨hk1.le,hk2.le⟩]
  have ht := Riesz1.WeightedSobolev.tendsto_toLp_of_dominated hF hfm' (memLp_const M)
    (fun k => ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hFbound k x)
    (by filter_upwards [hsupp] with x hx; simpa only [Real.norm_eq_abs] using hbound x hx) hlim
  refine ⟨hfm', ?_⟩
  exact form_limit hF (fun _ => hd) hfm' hd ht tendsto_const_nhds
    (fun k => clamp_poincare hf hw hp (ha k) (hb k) (hab k) hbound hA hd hP)

end Riesz2.BoundedIntervalPoincare
