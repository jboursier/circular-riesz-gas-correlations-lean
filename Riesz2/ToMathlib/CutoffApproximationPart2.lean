/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.CutoffApproximation
public import Riesz1.ToMathlib.CircleMollifyWeakDerivative
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous

/-!
# Mollification of locally absolutely continuous functions

Shared infrastructure for the mollification paragraph of Lemma 6.5. The convolution and derivative are the existing
Riesz1 objects. Translation continuity in Lebesgue L² supplies the strong
approximate identity. Bounded densities then transfer the convergence.
-/

public section
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff NNReal ENNReal

namespace Riesz2.CutoffApproximation

/-- Translation continuity in the squared Lebesgue L² seminorm, used in the
mollification paragraph of Lemma 6.5. -/
theorem tendsto_translation_lintegral_sq {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    Tendsto (fun t : ℝ => ∫⁻ x, ‖f (x - t) - f x‖ₑ ^ 2) (𝓝 0) (𝓝 0) := by
  have : Fact ((2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by norm_num⟩
  let F := hf.toLp f
  have hc : Continuous (fun t : ℝ => (DomAddAct.mk (-t)) +ᵥ F) :=
    (DomAddAct.continuous_mk.comp continuous_neg).vadd continuous_const
  have ht : Tendsto (fun t : ℝ => ‖((DomAddAct.mk (-t)) +ᵥ F) - F‖ₑ ^ 2)
      (𝓝 0) (𝓝 0) := by
    simpa only [neg_zero, show DomAddAct.mk (0 : ℝ) = 0 from rfl, zero_vadd,
      sub_self, enorm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      using ENNReal.Tendsto.pow (n := 2) ((hc.tendsto 0).sub (tendsto_const_nhds (x := F))).enorm
  convert ht using 1
  funext t
  have hcoe : ((DomAddAct.mk (-t)) +ᵥ F) - F =ᵐ[volume]
      (fun x => f (x - t) - f x) := by
    filter_upwards [Lp.coeFn_sub ((DomAddAct.mk (-t)) +ᵥ F) F,
      DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (-t)) F,
      (measurePreserving_add_left volume (-t)).quasiMeasurePreserving.ae hf.coeFn_toLp,
      hf.coeFn_toLp] with x hx hy hz hw
    change ((DomAddAct.mk (-t)) +ᵥ F) x = F (-t + x) at hy
    change F (-t + x) = f (-t + x) at hz
    calc
      _ = F (-t + x) - F x := hx.trans (congrArg (fun z => z - F x) hy)
      _ = f (x - t) - f x := by rw [hz, hw]; congr 1; congr 1; ring
  rw [Lp.enorm_def]
  have he := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0))
    (by norm_num) (Lp.aestronglyMeasurable (((DomAddAct.mk (-t)) +ᵥ F) - F))
  norm_num only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] at he
  rw [he]
  exact lintegral_congr_ae (hcoe.symm.fun_comp (fun z : ℝ => ‖z‖ₑ ^ 2))

namespace Internal

/-- Jensen's square bound, also valid when the right side is infinite. -/
theorem enorm_integral_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] {g : Ω → ℝ}
    (hg : AEStronglyMeasurable g ν) :
    ‖∫ x, g x ∂ν‖ₑ ^ 2 ≤ ∫⁻ x, ‖g x‖ₑ ^ 2 ∂ν := by
  have he := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hg
  norm_num only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] at he
  rw [← he]
  apply pow_le_pow_left' _ 2
  exact (enorm_integral_le_lintegral_enorm _).trans
    (lintegral_enorm_le_eLpNorm_one.trans
      (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)))

/-- The square error of convolution is bounded by the kernel average of
the square translation errors. This is an internal analytic estimate for
Lemma 6.5. -/
theorem mollifyLine_error_sq_le {ρ f : ℝ → ℝ} (hρ : Riesz1.IsMollifier ρ)
    (hf : MemLp f 2 volume) (hm : Measurable f) {h : ℝ} (hh : 0 < h) :
    (∫⁻ x, ‖Riesz1.mollifyLine ρ h f x - f x‖ₑ ^ 2) ≤
      ∫⁻ t, ENNReal.ofReal (Riesz1.scaledMollifier ρ h t) *
        (∫⁻ x, ‖f (x - t) - f x‖ₑ ^ 2) := by
  let κ := Riesz1.scaledMollifier ρ h
  have hk : Continuous κ := (Riesz1.contDiff_scaledMollifier hρ).continuous
  have hn t : 0 ≤ κ t := Riesz1.scaledMollifier_nonneg' hρ hh t
  have hi : Integrable κ volume := Riesz1.integrable_scaledMollifier' hρ hh
  have hmass : ∫ t, κ t = 1 := Riesz1.integral_scaledMollifier hρ hh
  let ν := volume.withDensity (fun t => ENNReal.ofReal (κ t))
  have : IsProbabilityMeasure ν := ⟨by
    change volume.withDensity (fun t => ENNReal.ofReal (κ t)) univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hn), hmass]
    simp⟩
  have hpoint x : ‖Riesz1.mollifyLine ρ h f x - f x‖ₑ ^ 2 ≤
      ∫⁻ t, ‖f (x - t) - f x‖ₑ ^ 2 ∂ν := by
    have hc := (Riesz1.hasCompactSupport_scaledMollifier hρ hh).convolutionExists_left
      (ContinuousLinearMap.mul ℝ ℝ) hk (hf.locallyIntegrable (by norm_num)) x
    change Integrable (fun t => κ t * f (x - t)) volume at hc
    have he : (∫ t, f (x - t) - f x ∂ν) = Riesz1.mollifyLine ρ h f x - f x := by
      rw [integral_withDensity_eq_integral_toReal_smul
        hk.measurable.ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      simp only [ENNReal.toReal_ofReal (hn _), smul_eq_mul, mul_sub]
      rw [integral_sub hc (hi.mul_const _), integral_mul_const, hmass, one_mul,
        Riesz1.mollifyLine_eq]
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun t => mul_comm _ _
    rw [← he]
    exact enorm_integral_sq_le ν
      ((hm.comp (measurable_const.sub measurable_id)).sub measurable_const).aestronglyMeasurable
  calc
    _ ≤ ∫⁻ x, ∫⁻ t, ‖f (x - t) - f x‖ₑ ^ 2 ∂ν := lintegral_mono hpoint
    _ = ∫⁻ t, ∫⁻ x, ‖f (x - t) - f x‖ₑ ^ 2 ∂volume ∂ν := by
      apply lintegral_lintegral_swap
      exact (((hm.comp (measurable_fst.sub measurable_snd)).sub
        (hm.comp measurable_fst)).enorm.pow_const 2).aemeasurable
    _ = _ := lintegral_withDensity_eq_lintegral_mul _ hk.measurable.ennreal_ofReal
      (by fun_prop)

end Internal

/-- Strong Lebesgue L² convergence of the existing Riesz1 mollification for
a measurable L² input, as needed by Lemma 6.5. -/
theorem mollifyLine_lintegral_sq_convergence {ρ f : ℝ → ℝ}
    (hρ : Riesz1.IsMollifier ρ) (hf : MemLp f 2 volume) (hm : Measurable f) :
    Tendsto (fun h : ℝ => ∫⁻ x, ‖Riesz1.mollifyLine ρ h f x - f x‖ₑ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  have ht := ENNReal.tendsto_nhds_zero.mp (tendsto_translation_lintegral_sq hf) ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhds_iff.mp ht
  filter_upwards [Ioo_mem_nhdsGT hδ] with h hh
  apply (Internal.mollifyLine_error_sq_le hρ hf hm hh.1).trans
  have hmass : (∫⁻ t, ENNReal.ofReal (Riesz1.scaledMollifier ρ h t)) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (Riesz1.integrable_scaledMollifier' hρ hh.1)
      (Eventually.of_forall (Riesz1.scaledMollifier_nonneg' hρ hh.1)),
      Riesz1.integral_scaledMollifier hρ hh.1]
    simp
  calc
    _ ≤ ∫⁻ t, ENNReal.ofReal (Riesz1.scaledMollifier ρ h t) * ε := by
      apply lintegral_mono
      intro t
      by_cases hz : Riesz1.scaledMollifier ρ h t = 0
      · simp [hz]
      change ENNReal.ofReal _ * _ ≤ ENNReal.ofReal _ * ε
      gcongr
      apply hd
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
      have hs : |t| < h / 2 := lt_of_not_ge fun he =>
        hz (Riesz1.scaledMollifier_eq_zero hρ hh.1 he)
      linarith [hh.2]
    _ = ε := by
      rw [lintegral_mul_const _
        ((Riesz1.contDiff_scaledMollifier hρ).continuous.measurable.ennreal_ofReal),
        hmass, one_mul]

/-- The existing convolution depends only on the Lebesgue almost everywhere
class of its input. This supports Lemma 6.5. -/
theorem mollifyLine_congr_ae {ρ f g : ℝ → ℝ} (hfg : f =ᵐ[volume] g)
    (h x : ℝ) : Riesz1.mollifyLine ρ h f x = Riesz1.mollifyLine ρ h g x := by
  apply integral_congr_ae
  filter_upwards [hfg] with y hy
  rw [hy]

/-- The strong approximate identity for every Lebesgue L² function, without
a choice of representative in its statement (Lemma 6.5). -/
theorem mollifyLine_lintegral_sq_convergence_of_memLp {ρ f : ℝ → ℝ}
    (hρ : Riesz1.IsMollifier ρ) (hf : MemLp f 2 volume) :
    Tendsto (fun h : ℝ => ∫⁻ x, ‖Riesz1.mollifyLine ρ h f x - f x‖ₑ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  let g := hf.aestronglyMeasurable.mk f
  have hfg : f =ᵐ[volume] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg : MemLp g 2 volume := hf.ae_eq hfg
  have ht := mollifyLine_lintegral_sq_convergence hρ hg
    hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  apply ht.congr
  intro h
  apply lintegral_congr_ae
  filter_upwards [hfg] with x hx
  rw [mollifyLine_congr_ae hfg h x, hx]

/-- Compact derivative support grows by at most half the mollifier radius.
This is the support control used in Lemma 6.5. -/
theorem support_mollifyLine_subset {ρ g : ℝ → ℝ} (hρ : Riesz1.IsMollifier ρ)
    {a b r h : ℝ} (hg : Function.support g ⊆ Icc a b)
    (hh : 0 < h) (hhr : h ≤ 2 * r) :
    Function.support (Riesz1.mollifyLine ρ h g) ⊆ Icc (a - r) (b + r) := by
  intro x hx
  by_contra hnx
  apply hx
  apply integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro y
  change g y * Riesz1.scaledMollifier ρ h (x - y) = 0
  by_cases hy : g y = 0
  · simp only [hy, zero_mul]
  have hyab := hg hy
  have hr : h / 2 ≤ |x - y| := by
    rcases not_and_or.mp hnx with hx | hx
    · have hx := lt_of_not_ge hx
      linarith [neg_le_abs (x - y), hyab.1]
    · have hx := lt_of_not_ge hx
      linarith [le_abs_self (x - y), hyab.2]
  rw [Riesz1.scaledMollifier_eq_zero hρ hh hr, mul_zero]

namespace Internal

/-- A compactly supported function belongs to global L² if it belongs to L²
on its support interval. -/
theorem memLp_of_support_subset {g : ℝ → ℝ} {p : ℝ≥0∞} {μ : Measure ℝ}
    {s : Set ℝ} (hs : MeasurableSet s) (hg : Function.support g ⊆ s)
    (hm : MemLp g p (μ.restrict s)) : MemLp g p μ := by
  have he : s.indicator g = g := indicator_eq_self.mpr hg
  rw [← he]
  exact (memLp_indicator_iff_restrict hs.nullMeasurableSet).mpr hm

/-- Upper comparison of measures only on the actual support of an error. -/
theorem supported_lintegral_sq_le {g : ℝ → ℝ} {μ : Measure ℝ}
    {s : Set ℝ} {C : ℝ≥0} (hg : Function.support g ⊆ s)
    (hμ : μ.restrict s ≤ (C : ℝ≥0∞) • volume) :
    (∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ) ≤ (C : ℝ≥0∞) * ∫⁻ x, ‖g x‖ₑ ^ 2 := by
  have hs : Function.support (fun x => ‖g x‖ₑ ^ 2) ⊆ s := by
    intro x hx
    apply hg
    intro he
    apply hx
    simp [he]
  rw [← setLIntegral_eq_of_support_subset hs]
  exact (lintegral_mono' hμ le_rfl).trans_eq (lintegral_smul_measure _ _)

end Internal

/-- Weighted L² convergence of convolution for a compactly supported L² input.
Only an upper bound for the weight on a fixed enlargement of the support is
needed. The measure may behave arbitrarily elsewhere (Lemma 6.5). -/
theorem mollifyLine_weighted_lintegral_sq_convergence {ρ g : ℝ → ℝ}
    (hρ : Riesz1.IsMollifier ρ) (hg : MemLp g 2 volume)
    {a b r : ℝ} (hr : 0 < r) (hs : Function.support g ⊆ Icc a b)
    (μ : Measure ℝ) {C : ℝ≥0}
    (hμ : μ.restrict (Icc (a - r) (b + r)) ≤ (C : ℝ≥0∞) • volume) :
    Tendsto (fun h : ℝ => ∫⁻ x, ‖Riesz1.mollifyLine ρ h g x - g x‖ₑ ^ 2 ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
  have ht := ENNReal.Tendsto.const_mul
    (mollifyLine_lintegral_sq_convergence_of_memLp hρ hg)
    (Or.inr ENNReal.coe_ne_top : (0 : ℝ≥0∞) ≠ 0 ∨ (C : ℝ≥0∞) ≠ ⊤)
  rw [mul_zero] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Eventually.of_forall fun _ => zero_le)
  filter_upwards [Ioo_mem_nhdsGT hr] with h hh
  apply Internal.supported_lintegral_sq_le (s := Icc (a - r) (b + r)) _ hμ
  intro x hx
  by_contra hnx
  have hmx : Riesz1.mollifyLine ρ h g x = 0 := by
    by_contra he
    exact hnx (support_mollifyLine_subset hρ hs hh.1 (by linarith [hh.2]) he)
  have hgx : g x = 0 := by
    by_contra he
    have := hs he
    exact hnx ⟨by linarith [this.1], by linarith [this.2]⟩
  exact hx (by simp [hmx, hgx])

/-- Weighted scalar-form convergence for a bounded locally absolutely
continuous function whose derivative is supported in a compact interval.
The upper and lower measure comparisons are needed only on the indicated
compact intervals. This is the mollification interface for the clamped
functions in Lemma 6.5. No C¹ assumption or bound
on the original derivative is imposed. -/
theorem mollifyLine_form_convergence_of_absolutelyContinuous {ρ f : ℝ → ℝ}
    (hρ : Riesz1.IsMollifier ρ) (hf : Continuous f)
    (hAC : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    {M a b r : ℝ} (hb : ∀ x, |f x| ≤ M) (hr : 0 < r)
    (hs : Function.support (deriv f) ⊆ Icc a b)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hd : MemLp (deriv f) 2 μ)
    {B C : ℝ≥0} (hlo : volume.restrict (Icc a b) ≤ (B : ℝ≥0∞) • μ)
    (hup : μ.restrict (Icc (a - r) (b + r)) ≤ (C : ℝ≥0∞) • volume)
    (h : ℕ → ℝ) (hh : ∀ k, 0 < h k) (hsmall : ∀ k, h k ≤ 2 * r)
    (hl : Tendsto h atTop (𝓝 0)) :
    (∀ k, ContDiff ℝ ∞ (Riesz1.mollifyLine ρ (h k) f)) ∧
    (∀ k x, |Riesz1.mollifyLine ρ (h k) f x| ≤ M) ∧
    (∀ k, Function.support (deriv (Riesz1.mollifyLine ρ (h k) f)) ⊆
      Icc (a - r) (b + r)) ∧
    (∀ k, MemLp (Riesz1.mollifyLine ρ (h k) f) 2 μ ∧
      MemLp (deriv (Riesz1.mollifyLine ρ (h k) f)) 2 μ) ∧
    Tendsto (fun k => ∫⁻ x, ‖Riesz1.mollifyLine ρ (h k) f x - f x‖ₑ ^ 2 ∂μ)
      atTop (𝓝 0) ∧
    Tendsto (fun k => ∫⁻ x,
      ‖deriv (Riesz1.mollifyLine ρ (h k) f) x - deriv f x‖ₑ ^ 2 ∂μ)
      atTop (𝓝 0) := by
  have hdv : MemLp (deriv f) 2 volume :=
    Internal.memLp_of_support_subset measurableSet_Icc hs
      (hd.of_measure_le_smul ENNReal.coe_ne_top hlo)
  have hc k : ContDiff ℝ ∞ (Riesz1.mollifyLine ρ (h k) f) :=
    Riesz1.contDiff_mollifyLine_of_locallyIntegrable hρ (hh k) hf.locallyIntegrable
  have he k : deriv (Riesz1.mollifyLine ρ (h k) f) =
      Riesz1.mollifyLine ρ (h k) (deriv f) :=
    funext (Riesz1.Internal.deriv_mollifyLine_of_absolutelyContinuous hρ (hh k) hf hAC)
  have hsupport k : Function.support (deriv (Riesz1.mollifyLine ρ (h k) f)) ⊆
      Icc (a - r) (b + r) := by
    rw [he k]
    exact support_mollifyLine_subset hρ hs (hh k) (hsmall k)
  have hbc k x : |Riesz1.mollifyLine ρ (h k) f x| ≤ M :=
    Riesz1.abs_mollifyLine_le_of_bound hρ (hh k) hb x
  have hm k : MemLp (Riesz1.mollifyLine ρ (h k) f) 2 μ :=
    MemLp.of_bound (hc k).continuous.aestronglyMeasurable M
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hbc k x)
  have hmd k : MemLp (deriv (Riesz1.mollifyLine ρ (h k) f)) 2 μ := by
    apply ((hc k).continuous_deriv (by simp)).memLp_of_hasCompactSupport
    exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
      (closure_minimal (hsupport k) isClosed_Icc)
  have hm₀ : MemLp f 2 μ := MemLp.of_bound hf.aestronglyMeasurable M
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x)
  have hgt : Tendsto h atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hl, Eventually.of_forall hh⟩
  refine ⟨hc, hbc, hsupport, fun k => ⟨hm k, hmd k⟩, ?_, ?_⟩
  · apply (Riesz1.WeightedSobolev.tendsto_toLp_iff_lintegral_sq _ hm _ hm₀).mp
    apply Riesz1.WeightedSobolev.tendsto_toLp_of_dominated hm hm₀ (memLp_const M)
      (fun k => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => (Riesz1.tendsto_mollifyLine_fun hρ hf x).comp hgt)
    · simpa only [Real.norm_eq_abs] using hbc k x
    · simpa only [Real.norm_eq_abs] using hb x
  · have ht := (mollifyLine_weighted_lintegral_sq_convergence hρ hdv hr hs μ hup).comp hgt
    simpa only [he, Function.comp_def] using ht

/-- A continuous density is bounded above on a compact set and, when positive,
bounded below on a smaller compact set. The resulting measure comparisons
justify the weighted mollification step of Lemma 6.5. -/
theorem compact_density_comparisons {w : ℝ → ℝ} {s t : Set ℝ}
    (hs : IsCompact s) (ht : IsCompact t) (hst : s ⊆ t)
    (hw : ContinuousOn w t) (hp : ∀ x ∈ s, 0 < w x) :
    ∃ B C : ℝ≥0,
      volume.restrict s ≤ (B : ℝ≥0∞) • volume.withDensity (fun x => ENNReal.ofReal (w x)) ∧
      (volume.withDensity (fun x => ENNReal.ofReal (w x))).restrict t ≤
        (C : ℝ≥0∞) • volume := by
  obtain ⟨m, hm, hmin⟩ := hs.exists_forall_le' (hw.mono hst) hp
  obtain ⟨M, hmax⟩ := (ht.image_of_continuousOn hw).bddAbove
  let B : ℝ≥0 := ⟨m⁻¹, inv_nonneg.mpr hm.le⟩
  let C : ℝ≥0 := ⟨max M 0, le_max_right _ _⟩
  refine ⟨B, C, ?_, ?_⟩
  · have hfg : (fun _ : ℝ => (1 : ℝ≥0∞)) ≤ᵐ[volume.restrict s]
        ((B : ℝ≥0∞) • (fun x => ENNReal.ofReal (w x))) := by
      filter_upwards [ae_restrict_mem hs.isClosed.measurableSet] with x hx
      change 1 ≤ (B : ℝ≥0∞) * ENNReal.ofReal (w x)
      have hB : (B : ℝ≥0∞) = ENNReal.ofReal m⁻¹ := by
        exact (show ENNReal.ofReal (B : ℝ) = (B : ℝ≥0∞) from ENNReal.ofReal_coe_nnreal).symm
      rw [hB, ← ENNReal.ofReal_mul (inv_nonneg.mpr hm.le), ← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      calc
        1 = m⁻¹ * m := (inv_mul_cancel₀ hm.ne').symm
        _ ≤ m⁻¹ * w x := mul_le_mul_of_nonneg_left (hmin x hx) (inv_nonneg.mpr hm.le)
    have he : volume.restrict s ≤ (B : ℝ≥0∞) •
        (volume.restrict s).withDensity (fun x => ENNReal.ofReal (w x)) := by
      simpa only [withDensity_const, one_smul, withDensity_smul' _ _ ENNReal.coe_ne_top]
        using (withDensity_mono hfg)
    rw [← restrict_withDensity hs.isClosed.measurableSet] at he
    exact he.trans (by gcongr; exact Measure.restrict_le_self)
  · rw [restrict_withDensity ht.isClosed.measurableSet]
    calc
      _ ≤ (volume.restrict t).withDensity (fun _ => (C : ℝ≥0∞)) := by
        apply withDensity_mono
        filter_upwards [ae_restrict_mem ht.isClosed.measurableSet] with x hx
        rw [show (C : ℝ≥0∞) = ENNReal.ofReal (max M 0) from
          (show ENNReal.ofReal (C : ℝ) = (C : ℝ≥0∞) from ENNReal.ofReal_coe_nnreal).symm]
        exact ENNReal.ofReal_le_ofReal ((hmax (mem_image_of_mem w hx)).trans (le_max_left _ _))
      _ = (C : ℝ≥0∞) • volume.restrict t := withDensity_const _
      _ ≤ (C : ℝ≥0∞) • volume := by gcongr; exact Measure.restrict_le_self

/-- Bounded locally absolutely continuous functions with compactly supported
weighted L² derivative admit bounded smooth approximations in the weighted
scalar form norm. The weight is assumed continuous only on a compact
enlargement and positive on the derivative support interval. This is the
complete fixed-clamp mollification interface of Lemma 6.5.
The approximations are literally `Riesz1.mollifyLine` at radii `r / (k + 1)`. -/
theorem exists_smooth_form_approximation_of_density {ρ f w : ℝ → ℝ}
    (hρ : Riesz1.IsMollifier ρ) (hf : Continuous f)
    (hAC : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    {M a b r : ℝ} (hb : ∀ x, |f x| ≤ M) (hr : 0 < r)
    (hs : Function.support (deriv f) ⊆ Icc a b)
    (hw : ContinuousOn w (Icc (a - r) (b + r)))
    (hp : ∀ x ∈ Icc a b, 0 < w x)
    [IsFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal (w x)))]
    (hd : MemLp (deriv f) 2 (volume.withDensity (fun x => ENNReal.ofReal (w x)))) :
    ∃ φ : ℕ → ℝ → ℝ,
      (∀ k, ContDiff ℝ ∞ (φ k)) ∧
      (∀ k x, |φ k x| ≤ M) ∧
      (∀ k, Function.support (deriv (φ k)) ⊆ Icc (a - r) (b + r)) ∧
      (∀ k, MemLp (φ k) 2 (volume.withDensity (fun x => ENNReal.ofReal (w x))) ∧
        MemLp (deriv (φ k)) 2 (volume.withDensity (fun x => ENNReal.ofReal (w x)))) ∧
      Tendsto (fun k => ∫⁻ x, ‖φ k x - f x‖ₑ ^ 2
        ∂volume.withDensity (fun x => ENNReal.ofReal (w x))) atTop (𝓝 0) ∧
      Tendsto (fun k => ∫⁻ x, ‖deriv (φ k) x - deriv f x‖ₑ ^ 2
        ∂volume.withDensity (fun x => ENNReal.ofReal (w x))) atTop (𝓝 0) := by
  have hsub : Icc a b ⊆ Icc (a - r) (b + r) := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨B, C, hlo, hup⟩ := compact_density_comparisons isCompact_Icc isCompact_Icc hsub hw hp
  let h (k : ℕ) : ℝ := r / (k + 1)
  have hh k : 0 < h k := by dsimp [h]; positivity
  have hsmall k : h k ≤ 2 * r := by
    have hden : (1 : ℝ) ≤ k + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
    exact (div_le_self hr.le hden).trans (by linarith)
  have hl : Tendsto h atTop (𝓝 0) := by
    simpa only [h, div_eq_mul_inv, one_div, one_mul, mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul r
  exact ⟨fun k => Riesz1.mollifyLine ρ (h k) f,
    mollifyLine_form_convergence_of_absolutelyContinuous hρ hf hAC hb hr hs _ hd
      hlo hup h hh hsmall hl⟩

end Riesz2.CutoffApproximation
