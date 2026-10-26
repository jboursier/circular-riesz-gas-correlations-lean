/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Covering.Differentiation
public import Mathlib.MeasureTheory.Covering.Besicovitch
public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Riesz2.Frozen.External.LogConcaveConvergence
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Riesz2.ToMathlib.LogConcaveRpow
public import Mathlib.Tactic

/-!
# Limit lemmas for log-concave densities

`Riesz2.logConcaveDensity_limits` proves the representative and unweighted L¹ conclusions
for log-concave densities.
The exponential-envelope and weighted conclusions are proved in
`LogConcaveExponentialTails` and `LogConcaveConvergenceResult`.

Separation of positive superlevel sets, compactness of normalized functionals, Portmanteau,
and Lebesgue differentiation give a one-sided almost everywhere limit inferior bound.
Fatou identifies the extended limit inferior with the given density almost everywhere.
Log-concavity and positive finite mass exclude infinite values at every point. Its real
values give the required representative. A one-sided Scheffé argument proves L¹ convergence.
All nonnegative integrals remain extended valued.
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Riesz2.DensityScheffe

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The overlap with a value converges to that value if it is bounded above by the
pointwise limit inferior. -/
theorem tendsto_min_of_le_liminf {u : ℕ → ℝ≥0∞} {a : ℝ≥0∞}
    (h : a ≤ liminf u atTop) :
    Tendsto (fun n => min a (u n)) atTop (𝓝 a) := by
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
  · rw [← inf_liminf]
    exact le_inf le_rfl h
  · exact limsup_le_of_le (h := Eventually.of_forall fun n => min_le_left _ _)

/-- Under a one-sided limit inferior bound, the integrals of the overlaps converge to
the finite limiting mass. No bound on the approximating functions is required. -/
theorem tendsto_lintegral_min_of_le_liminf {F : ℕ → α → ℝ≥0∞} {g : α → ℝ≥0∞}
    (hF : ∀ n, AEMeasurable (F n) μ) (hg : AEMeasurable g μ)
    (hfin : (∫⁻ x, g x ∂μ) ≠ ⊤)
    (hlim : ∀ᵐ x ∂μ, g x ≤ liminf (fun n => F n x) atTop) :
    Tendsto (fun n => ∫⁻ x, min (g x) (F n x) ∂μ) atTop
      (𝓝 (∫⁻ x, g x ∂μ)) := by
  exact tendsto_lintegral_of_dominated_convergence' g
    (fun n => hg.min (hF n))
    (fun n => ae_of_all _ fun x => min_le_left _ _) hfin
    (hlim.mono fun x hx => tendsto_min_of_le_liminf hx)

/-- Scheffé's argument with convergent finite masses and only a one-sided pointwise
limit inferior bound. The two summands are the positive and negative density deficits. -/
theorem tendsto_lintegral_deficits_of_le_liminf
    {F : ℕ → α → ℝ≥0∞} {g : α → ℝ≥0∞}
    (hF : ∀ n, AEMeasurable (F n) μ) (hg : AEMeasurable g μ)
    (hfin : (∫⁻ x, g x ∂μ) ≠ ⊤)
    (hmass : Tendsto (fun n => ∫⁻ x, F n x ∂μ) atTop (𝓝 (∫⁻ x, g x ∂μ)))
    (hlim : ∀ᵐ x ∂μ, g x ≤ liminf (fun n => F n x) atTop) :
    Tendsto (fun n => ∫⁻ x, (F n x - g x) + (g x - F n x) ∂μ)
      atTop (𝓝 0) := by
  have hover := tendsto_lintegral_min_of_le_liminf hF hg hfin hlim
  have hminfin (n : ℕ) : (∫⁻ x, min (g x) (F n x) ∂μ) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (lintegral_mono fun x => min_le_left _ _)
  have hid (n : ℕ) :
      (∫⁻ x, (F n x - g x) + (g x - F n x) ∂μ) =
        ((∫⁻ x, F n x ∂μ) - ∫⁻ x, min (g x) (F n x) ∂μ) +
        ((∫⁻ x, g x ∂μ) - ∫⁻ x, min (g x) (F n x) ∂μ) := by
    have hpoint (x : α) :
        (F n x - g x) + (g x - F n x) =
          (F n x - min (g x) (F n x)) + (g x - min (g x) (F n x)) := by
      rcases le_total (g x) (F n x) with h | h
      · simp [min_eq_left h, tsub_eq_zero_of_le h]
      · simp [min_eq_right h, tsub_eq_zero_of_le h]
    simp_rw [hpoint]
    have hmeas : AEMeasurable (fun x => F n x - min (g x) (F n x)) μ :=
      (hF n).sub (hg.min (hF n))
    rw [lintegral_add_left' hmeas,
      lintegral_sub' (hg.min (hF n)) (hminfin n)
        (ae_of_all _ fun x => min_le_right _ _),
      lintegral_sub' (hg.min (hF n)) (hminfin n)
        (ae_of_all _ fun x => min_le_left _ _)]
  simp_rw [hid]
  simpa only [tsub_self, add_zero] using
    (ENNReal.Tendsto.sub hmass hover (Or.inl hfin)).add
      (ENNReal.Tendsto.sub tendsto_const_nhds hover (Or.inl hfin))

/-- For nonnegative real functions, the extended positive and negative deficits sum to
the extended absolute difference. -/
theorem ofReal_abs_sub_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal |a - b| =
      (ENNReal.ofReal a - ENNReal.ofReal b) +
        (ENNReal.ofReal b - ENNReal.ofReal a) := by
  rcases le_total b a with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h),
      tsub_eq_zero_of_le (ENNReal.ofReal_le_ofReal h), add_zero,
      ENNReal.ofReal_sub _ hb]
  · rw [abs_of_nonpos (sub_nonpos.mpr h), neg_sub,
      tsub_eq_zero_of_le (ENNReal.ofReal_le_ofReal h), zero_add,
      ENNReal.ofReal_sub _ ha]

/-- The real-density form of the one-sided Scheffé lemma. All masses and distances are
nonnegative extended integrals, including when an early density has infinite mass. -/
theorem tendsto_lintegral_abs_sub_of_le_liminf
    {F : ℕ → α → ℝ} {g : α → ℝ}
    (hF : ∀ n, AEMeasurable (F n) μ) (hg : AEMeasurable g μ)
    (hF0 : ∀ n, ∀ᵐ x ∂μ, 0 ≤ F n x) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hfin : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) ≠ ⊤)
    (hmass : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (F n x) ∂μ) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (g x) ∂μ)))
    (hlim : ∀ᵐ x ∂μ, ENNReal.ofReal (g x) ≤
      liminf (fun n => ENNReal.ofReal (F n x)) atTop) :
    Tendsto (fun n => ∫⁻ x, ENNReal.ofReal |F n x - g x| ∂μ) atTop (𝓝 0) := by
  have hid (n : ℕ) :
      (∫⁻ x, ENNReal.ofReal |F n x - g x| ∂μ) =
        ∫⁻ x, (ENNReal.ofReal (F n x) - ENNReal.ofReal (g x)) +
          (ENNReal.ofReal (g x) - ENNReal.ofReal (F n x)) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hF0 n, hg0] with x hx hy
    exact ofReal_abs_sub_eq hx hy
  simp_rw [hid]
  exact tendsto_lintegral_deficits_of_le_liminf
    (fun n => (hF n).ennreal_ofReal) hg.ennreal_ofReal hfin hmass hlim

/-- Scheffé's lemma for real probability densities, on an arbitrary measure space. -/
theorem tendsto_lintegral_abs_sub_of_ae_tendsto
    {F : ℕ → α → ℝ} {g : α → ℝ}
    (hF : ∀ n, AEMeasurable (F n) μ) (hg : AEMeasurable g μ)
    (hF0 : ∀ n, ∀ᵐ x ∂μ, 0 ≤ F n x) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hFmass : ∀ n, (∫⁻ x, ENNReal.ofReal (F n x) ∂μ) = 1)
    (hgmass : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) = 1)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => ∫⁻ x, ENNReal.ofReal |F n x - g x| ∂μ) atTop (𝓝 0) := by
  apply tendsto_lintegral_abs_sub_of_le_liminf hF hg hF0 hg0
  · rw [hgmass]
    exact ENNReal.one_ne_top
  · simp_rw [hFmass, hgmass]
    exact tendsto_const_nhds
  · filter_upwards [hlim] with x hx
    exact (ENNReal.tendsto_ofReal hx).liminf_eq.ge

/-- Probability densities converging in measure converge in L¹. There is no finiteness
assumption on the underlying measure. -/
theorem tendsto_lintegral_abs_sub_of_tendstoInMeasure
    {F : ℕ → α → ℝ} {g : α → ℝ}
    (hF : ∀ n, AEMeasurable (F n) μ) (hg : AEMeasurable g μ)
    (hF0 : ∀ n, ∀ᵐ x ∂μ, 0 ≤ F n x) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hFmass : ∀ n, (∫⁻ x, ENNReal.ofReal (F n x) ∂μ) = 1)
    (hgmass : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) = 1)
    (hlim : TendstoInMeasure μ F atTop g) :
    Tendsto (fun n => ∫⁻ x, ENNReal.ofReal |F n x - g x| ∂μ) atTop (𝓝 0) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, _, hms⟩ := (hlim.comp hns).exists_seq_tendsto_ae
  exact ⟨ms, tendsto_lintegral_abs_sub_of_ae_tendsto
    (fun n => hF _) hg (fun n => hF0 _) hg0 (fun n => hFmass _) hgmass hms⟩

end Riesz2.DensityScheffe

namespace Riesz2.LogConcaveDensityLimits.Internal

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The multiplicative interpolation inequality implies concavity of the logarithm on
the positive set, including convexity of that set. Log-concavity is taken on the positive set. -/
theorem concaveOn_log_of_rpow_mul_rpow_le {f : E → ℝ}
    (h : ∀ (x y : E) (t : ℝ), 0 < t → t < 1 →
      f x ^ t * f y ^ (1 - t) ≤ f (t • x + (1 - t) • y)) :
    ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) := by
  have hpositive {x y : E} (hx : 0 < f x) (hy : 0 < f y)
      {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
      0 < f (a • x + b • y) := by
    by_cases ha0 : a = 0
    · simpa [ha0, show b = 1 by linarith] using hy
    by_cases hb0 : b = 0
    · simpa [hb0, show a = 1 by linarith] using hx
    have hbpos := lt_of_le_of_ne hb (Ne.symm hb0)
    have hmul := h x y a (lt_of_le_of_ne ha (Ne.symm ha0)) (by linarith)
    rw [show 1 - a = b by linarith] at hmul
    exact (mul_pos (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hy _)).trans_le hmul
  refine ⟨fun x hx y hy a b ha hb hab => hpositive hx hy ha hb hab, ?_⟩
  intro x hx y hy a b ha hb hab
  by_cases ha0 : a = 0
  · simp [ha0, show b = 1 by linarith]
  by_cases hb0 : b = 0
  · simp [hb0, show a = 1 by linarith]
  have hbpos := lt_of_le_of_ne hb (Ne.symm hb0)
  have hmul := h x y a (lt_of_le_of_ne ha (Ne.symm ha0)) (by linarith)
  rw [show 1 - a = b by linarith] at hmul
  have hlog := Real.log_le_log
    (mul_pos (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hy _)) hmul
  rw [Real.log_mul (Real.rpow_pos_of_pos hx _).ne' (Real.rpow_pos_of_pos hy _).ne',
    Real.log_rpow hx, Real.log_rpow hy] at hlog
  simpa only [smul_eq_mul] using hlog

/-- Log-concavity on the positive set is preserved by an everywhere finite pointwise
limit. This is an internal closure lemma. Weak convergence does not supply its pointwise
convergence premise by itself. -/
theorem concaveOn_log_of_pointwise_tendsto
    {F : ℕ → E → ℝ} {g : E → ℝ}
    (hF0 : ∀ n x, 0 ≤ F n x)
    (hF : ∀ n, ConcaveOn ℝ {x | 0 < F n x} (fun x => Real.log (F n x)))
    (hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (g x))) :
    (∀ x, 0 ≤ g x) ∧ ConcaveOn ℝ {x | 0 < g x} (fun x => Real.log (g x)) := by
  refine ⟨fun x => ge_of_tendsto' (hlim x) (fun n => hF0 n x),
    concaveOn_log_of_rpow_mul_rpow_le ?_⟩
  intro x y t ht0 ht1
  exact le_of_tendsto_of_tendsto
    (((hlim x).rpow_const (Or.inr ht0.le)).mul
      ((hlim y).rpow_const (Or.inr (sub_pos.mpr ht1).le)))
    (hlim (t • x + (1 - t) • y))
    (Eventually.of_forall fun n =>
      Riesz2.rpow_mul_rpow_le_of_concaveOn_log (hF0 n) (hF n) x y ht0 ht1)

/-- The extended pointwise limit inferior preserves the multiplicative log-concavity
inequality. Extended values are retained here until finiteness has been proved. -/
theorem rpow_mul_rpow_le_liminf
    {F : ℕ → E → ℝ} (hF0 : ∀ n x, 0 ≤ F n x)
    (hF : ∀ n, ConcaveOn ℝ {x | 0 < F n x} (fun x => Real.log (F n x)))
    (x y : E) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (liminf (fun n => ENNReal.ofReal (F n x)) atTop) ^ t *
        (liminf (fun n => ENNReal.ofReal (F n y)) atTop) ^ (1 - t) ≤
      liminf (fun n => ENNReal.ofReal (F n (t • x + (1 - t) • y))) atTop := by
  have hxpow := Monotone.map_liminf_of_continuousAt (F := atTop)
    (fun a b hab => ENNReal.rpow_le_rpow hab ht0.le)
    (fun n => ENNReal.ofReal (F n x)) ENNReal.continuous_rpow_const.continuousAt
  have hypow := Monotone.map_liminf_of_continuousAt (F := atTop)
    (fun a b hab => ENNReal.rpow_le_rpow hab (sub_pos.mpr ht1).le)
    (fun n => ENNReal.ofReal (F n y)) ENNReal.continuous_rpow_const.continuousAt
  rw [hxpow, hypow]
  refine ENNReal.le_liminf_mul.trans (liminf_le_liminf (Eventually.of_forall ?_))
  intro n
  dsimp only [Function.comp_apply, Pi.mul_apply]
  rw [ENNReal.ofReal_rpow_of_nonneg (hF0 n x) ht0.le,
    ENNReal.ofReal_rpow_of_nonneg (hF0 n y) (sub_pos.mpr ht1).le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (hF0 n x) _)]
  exact ENNReal.ofReal_le_ofReal
    (Riesz2.rpow_mul_rpow_le_of_concaveOn_log (hF0 n) (hF n) x y ht0 ht1)

end Riesz2.LogConcaveDensityLimits.Internal

namespace Riesz2.LogConcaveDensityLimits.Internal

open MeasureTheory.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [IsAddHaarMeasure μ]

/-- An extended log-concave function of positive finite integral is finite at every
point. An infinite value would force infinite values on an affine image of its positive
set. This justifies taking a real representative without assigning a default value. -/
theorem ne_top_of_midpoint_logConcave {H : E → ℝ≥0∞} (hH : Measurable H)
    (hfin : (∫⁻ x, H x ∂μ) ≠ ⊤) (hne : (∫⁻ x, H x ∂μ) ≠ 0)
    (hmid : ∀ x y, H x ^ (1 / 2 : ℝ) * H y ^ (1 / 2 : ℝ) ≤
      H ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)) :
    ∀ x, H x ≠ ⊤ := by
  intro x hx
  have hfinite : ∀ᵐ y ∂μ, H y < ⊤ := ae_lt_top hH hfin
  have hq : QuasiMeasurePreserving
      (fun y : E => (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) μ μ :=
    (measurePreserving_add_left μ ((1 / 2 : ℝ) • x)).quasiMeasurePreserving.comp
      (quasiMeasurePreserving_smul μ (by norm_num : (1 / 2 : ℝ) ≠ 0))
  have hzero : H =ᵐ[μ] 0 := by
    filter_upwards [hq.ae hfinite] with y hy
    by_contra hy0
    have hp : 0 < H y := bot_lt_iff_ne_bot.mpr hy0
    have hb := hmid x y
    rw [hx, ENNReal.top_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
      ENNReal.top_mul (ENNReal.rpow_pos_of_nonneg hp (by norm_num)).ne'] at hb
    exact hy.ne (top_le_iff.mp hb)
  exact hne (lintegral_eq_zero_of_ae_eq_zero hzero)

/-- Internal reduction of both unweighted conclusions of convergence of log-concave densities to the geometric lower limit inferior bound.
The representative is the real value of the extended limit
inferior, which is finite at every point. -/
theorem density_limits_of_le_liminf
    {F : ℕ → E → ℝ} {g : E → ℝ}
    (hFm : ∀ n, Measurable (F n)) (hF0 : ∀ n x, 0 ≤ F n x)
    (hFmass : ∀ n, (∫⁻ x, ENNReal.ofReal (F n x) ∂μ) = 1)
    (hF : ∀ n, ConcaveOn ℝ {x | 0 < F n x} (fun x => Real.log (F n x)))
    (hgm : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (hgmass : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) = 1)
    (hlim : ∀ᵐ x ∂μ, ENNReal.ofReal (g x) ≤
      liminf (fun n => ENNReal.ofReal (F n x)) atTop) :
    (∃ g' : E → ℝ, Measurable g' ∧ (∀ x, 0 ≤ g' x) ∧
      (∫⁻ x, ENNReal.ofReal (g' x) ∂μ) = 1 ∧
      ConcaveOn ℝ {x | 0 < g' x} (fun x => Real.log (g' x)) ∧ g' =ᵐ[μ] g) ∧
    Tendsto (fun n => ∫⁻ x, ENNReal.ofReal |F n x - g x| ∂μ) atTop (𝓝 0) := by
  let H : E → ℝ≥0∞ := fun x => liminf (fun n => ENNReal.ofReal (F n x)) atTop
  have hHm : Measurable H := Measurable.liminf fun n => (hFm n).ennreal_ofReal
  have hmassle : (∫⁻ x, H x ∂μ) ≤ 1 := by
    have hfatou := lintegral_liminf_le (fun n => (hFm n).ennreal_ofReal)
      (μ := μ) (u := atTop)
    simpa only [hFmass, liminf_const] using hfatou
  have hae : (fun x => ENNReal.ofReal (g x)) =ᵐ[μ] H :=
    ae_eq_of_ae_le_of_lintegral_le hlim (by rw [hgmass]; exact ENNReal.one_ne_top)
      hHm.aemeasurable (by rw [hgmass]; exact hmassle)
  have hHmass : (∫⁻ x, H x ∂μ) = 1 := (lintegral_congr_ae hae).symm.trans hgmass
  have hmul (x y : E) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
      H x ^ t * H y ^ (1 - t) ≤ H (t • x + (1 - t) • y) :=
    rpow_mul_rpow_le_liminf hF0 hF x y ht0 ht1
  have hHfin : ∀ x, H x ≠ ⊤ := ne_top_of_midpoint_logConcave hHm
    (by rw [hHmass]; exact ENNReal.one_ne_top) (by rw [hHmass]; exact one_ne_zero)
    (fun x y => by
      convert hmul x y (1 / 2) (by norm_num) (by norm_num) using 1 <;> norm_num)
  have hrepr : (fun x => (H x).toReal) =ᵐ[μ] g := by
    filter_upwards [hae] with x hx
    rw [← hx, ENNReal.toReal_ofReal (hg0 x)]
  refine ⟨⟨fun x => (H x).toReal, hHm.ennreal_toReal,
    fun x => ENNReal.toReal_nonneg, ?_, ?_, hrepr⟩, ?_⟩
  · simpa only [ENNReal.ofReal_toReal (hHfin _)] using hHmass
  · apply concaveOn_log_of_rpow_mul_rpow_le
    intro x y t ht0 ht1
    have hb := ENNReal.toReal_mono (hHfin _) (hmul x y t ht0 ht1)
    simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow] using hb
  · apply Riesz2.DensityScheffe.tendsto_lintegral_abs_sub_of_le_liminf
      (fun n => (hFm n).aemeasurable) hgm.aemeasurable
      (fun n => ae_of_all _ (hF0 n)) (ae_of_all _ hg0)
      (by rw [hgmass]; exact ENNReal.one_ne_top) _ hlim
    simp_rw [hFmass, hgmass]
    exact tendsto_const_nhds

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- Every positive superlevel set of a log-concave function is convex. -/
theorem convex_superlevel_of_concaveOn_log {f : E → ℝ}
    (hf : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    {a : ℝ} (ha : 0 < a) : Convex ℝ {x | a ≤ f x} := by
  have hset : {x | a ≤ f x} = {x ∈ {x | 0 < f x} | Real.log a ≤ Real.log (f x)} := by
    ext x
    constructor
    · intro hx
      exact ⟨ha.trans_le hx, Real.log_le_log ha hx⟩
    · rintro ⟨hx, hlog⟩
      exact (Real.log_le_log_iff ha hx).mp hlog
  rw [hset]
  exact hf.convex_ge (Real.log a)

/-- A density value below a positive level with positive-volume superlevel set gives
a nonzero linear functional and an entire halfspace on which the density is below that
level. This is the separating-halfspace step toward the weak-to-pointwise argument. -/
theorem exists_low_halfspace {f : E → ℝ}
    (hf : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    {a : ℝ} (ha : 0 < a) (hvol : 0 < μ {y | a ≤ f y})
    {x : E} (hx : f x < a) :
    ∃ ℓ : StrongDual ℝ E, ℓ ≠ 0 ∧ ∀ y, ℓ x < ℓ y → f y < a := by
  have hconv := convex_superlevel_of_concaveOn_log hf ha
  have hinterior : (interior {y | a ≤ f y}).Nonempty := by
    by_contra hempty
    have hempty' : interior {y | a ≤ f y} = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
    have hnull : μ {y | a ≤ f y} = 0 := by
      apply measure_mono_null _ (hconv.addHaar_frontier μ)
      intro y hy
      exact ⟨subset_closure hy, by simp [hempty']⟩
    exact hvol.ne' hnull
  have hxout : x ∉ interior {y | a ≤ f y} :=
    fun h => (not_le_of_gt hx) (interior_subset (s := {y : E | a ≤ f y}) h)
  obtain ⟨ℓ, hℓ, hsep⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point hconv hxout hinterior
  refine ⟨ℓ, hℓ, fun y hy => ?_⟩
  by_contra hya
  exact (hsep y (not_lt.mp hya)).not_gt hy

end Riesz2.LogConcaveDensityLimits.Internal

namespace Riesz2.LogConcaveDensityLimits.Internal

open Metric
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]

/-- Compactness of normalized separating functionals gives a fixed direction and
arbitrarily small balls on which a subsequence is below the same level. -/
theorem exists_subseq_low_balls {F : ℕ → E → ℝ} {x : E} {a : ℝ}
    (hsep : ∀ n, ∃ ℓ : StrongDual ℝ E, ℓ ≠ 0 ∧ ∀ y, ℓ x < ℓ y → F n y < a) :
    ∃ v : E, ‖v‖ = 1 ∧ ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ r : ℝ, 0 < r → ∀ᶠ n in atTop,
        ∀ y ∈ ball (x + (r / 2) • v) (r / 4), F (ns n) y < a := by
  choose ℓ hℓ hlow using hsep
  let L : ℕ → StrongDual ℝ E := fun n => ‖ℓ n‖⁻¹ • ℓ n
  have hnorm (n : ℕ) : ‖L n‖ = 1 := by
    simp only [L, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hℓ n))
  have hlowL (n : ℕ) (y : E) (hy : L n x < L n y) : F n y < a := by
    apply hlow n y
    have hp : 0 < ‖ℓ n‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr (hℓ n))
    exact (mul_lt_mul_iff_right₀ hp).mp hy
  obtain ⟨l, hl, ns, hns, hlim⟩ :=
    (isCompact_sphere (0 : StrongDual ℝ E) 1).tendsto_subseq
      (fun n => by simpa only [mem_sphere, dist_zero_right] using hnorm n)
  have hlnorm : ‖l‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hl
  let v := (InnerProductSpace.toDual ℝ E).symm l
  have hv : ‖v‖ = 1 := by simpa only [v, LinearIsometryEquiv.norm_map] using hlnorm
  have hlv : l v = 1 := by
    rw [← InnerProductSpace.toDual_symm_apply, real_inner_self_eq_norm_sq, hv]
    norm_num
  have hlimv : Tendsto (fun n => L (ns n) v) atTop (𝓝 1) := by
    have hcont : Continuous (fun k : StrongDual ℝ E => k v) := by fun_prop
    simpa only [hlv, Function.comp_def] using (hcont.tendsto l).comp hlim
  have hlarge : ∀ᶠ n in atTop, (3 / 4 : ℝ) < L (ns n) v :=
    hlimv.eventually (lt_mem_nhds (by norm_num : (3 / 4 : ℝ) < 1))
  refine ⟨v, hv, ns, hns, fun r hr => ?_⟩
  filter_upwards [hlarge] with n hn
  intro y hy
  apply hlowL
  have hdist : ‖y - (x + (r / 2) • v)‖ < r / 4 := by
    simpa only [mem_ball, dist_eq_norm] using hy
  have hnormbound := (L (ns n)).le_opNorm (y - (x + (r / 2) • v))
  rw [hnorm, one_mul, Real.norm_eq_abs] at hnormbound
  have hneg := (neg_le_abs (L (ns n) (y - (x + (r / 2) • v))))
  have hid : L (ns n) y - L (ns n) x =
      L (ns n) (y - (x + (r / 2) • v)) + (r / 2) * L (ns n) v := by
    simp only [map_sub, map_add, map_smul, smul_eq_mul]
    ring
  have hmul : r * (3 / 4 : ℝ) < r * L (ns n) v := mul_lt_mul_of_pos_left hn hr
  linarith

end Riesz2.LogConcaveDensityLimits.Internal

namespace Riesz2.LogConcaveDensityLimits.Internal

open Metric MeasureTheory.Measure
open scoped MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    {μ : Measure E} [IsAddHaarMeasure μ]

/-- A Lebesgue point with value above `a` has average above `a` on some ball in any
fixed direction, with its radius a fixed fraction of its distance to that point. -/
theorem exists_directional_ball_integral_gt {g : E → ℝ} (hg : Integrable g μ)
    {x : E} {a : ℝ} (ha : a < g x)
    (hLeb : Tendsto (fun r : ℝ => ⨍ y in closedBall x r, ‖g y - g x‖ ∂μ)
      (𝓝[>] 0) (𝓝 0)) (v : E) (hv : ‖v‖ ≤ 1) :
    ∃ r : ℝ, 0 < r ∧
      a * μ.real (ball (x + (r / 2) • v) (r / 4)) <
        ∫ y in ball (x + (r / 2) • v) (r / 4), g y ∂μ := by
  let c : ℝ := (1 / 4 : ℝ) ^ Module.finrank ℝ E
  have hc : 0 < c := pow_pos (by norm_num) _
  have hε : 0 < (g x - a) * c := mul_pos (sub_pos.mpr ha) hc
  obtain ⟨r, hrsmall, hr⟩ :=
    ((hLeb.eventually (gt_mem_nhds hε)).and self_mem_nhdsWithin).exists
  have hrpos : 0 < r := hr
  let B := ball (x + (r / 2) • v) (r / 4)
  let C := closedBall x r
  have hBC : B ⊆ C := by
    intro y hy
    have hy' : ‖y - (x + (r / 2) • v)‖ < r / 4 := by
      simpa only [B, mem_ball, dist_eq_norm] using hy
    have hnorm : ‖(r / 2) • v‖ ≤ r / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
      nlinarith
    have hid : y - x = (y - (x + (r / 2) • v)) + (r / 2) • v := by abel
    rw [mem_closedBall, dist_eq_norm, hid]
    exact (norm_add_le _ _).trans (by linarith)
  have hCpos : 0 < μ.real C :=
    ENNReal.toReal_pos (measure_closedBall_pos μ x hrpos).ne' measure_closedBall_lt_top.ne
  have hratio : μ.real B = c * μ.real C := by
    dsimp only [B, C, c]
    rw [← addHaar_real_closedBall_eq_addHaar_real_ball μ,
      addHaar_real_closedBall μ _ (by linarith : 0 ≤ r / 4),
      addHaar_real_closedBall μ _ hrpos.le]
    rw [show r / 4 = (1 / 4 : ℝ) * r by ring, mul_pow]
    ring
  have hosc : (∫ y in C, ‖g y - g x‖ ∂μ) < (g x - a) * μ.real B := by
    rw [setAverage_eq, smul_eq_mul] at hrsmall
    rw [← div_eq_inv_mul, div_lt_iff₀ hCpos] at hrsmall
    rw [hratio]
    nlinarith
  have hgB := hg.integrableOn (s := B)
  have hconstB : IntegrableOn (fun _ : E => g x) B μ :=
    integrableOn_const measure_ball_lt_top.ne
  have hoscC : IntegrableOn (fun y => ‖g y - g x‖) C μ :=
    (hg.integrableOn.sub (integrableOn_const measure_closedBall_lt_top.ne)).norm
  have hdiff : g x * μ.real B - ∫ y in B, g y ∂μ ≤ ∫ y in C, ‖g y - g x‖ ∂μ := by
    calc
      g x * μ.real B - ∫ y in B, g y ∂μ = ∫ y in B, g x - g y ∂μ := by
        rw [integral_sub hconstB hgB, setIntegral_const, smul_eq_mul, mul_comm (μ.real B)]
      _ ≤ ∫ y in B, ‖g y - g x‖ ∂μ := by
        apply integral_mono (hconstB.sub hgB) ((hgB.sub hconstB).norm)
        intro y
        change g x - g y ≤ ‖g y - g x‖
        rw [Real.norm_eq_abs]
        linarith [neg_le_abs (g y - g x)]
      _ ≤ ∫ y in C, ‖g y - g x‖ ∂μ :=
        setIntegral_mono_set hoscC (ae_of_all _ fun y => norm_nonneg _) (ae_of_all _ hBC)
  exact ⟨r, hrpos, by change a * μ.real B < ∫ y in B, g y ∂μ; nlinarith⟩

end Riesz2.LogConcaveDensityLimits.Internal

namespace Riesz2.LogConcaveDensityLimits.Internal

variable {E : Type*} [MeasurableSpace E] {μ : Measure E}

/-- A real set integral computes the mass of a nonnegative integrable density. -/
theorem withDensity_apply_eq_ofReal_setIntegral {g : E → ℝ}
    (hg : Integrable g μ) (hg0 : ∀ y, 0 ≤ g y) {B : Set E} (hB : MeasurableSet B) :
    (μ.withDensity (fun y => ENNReal.ofReal (g y))) B =
      ENNReal.ofReal (∫ y in B, g y ∂μ) := by
  rw [withDensity_apply _ hB]
  exact (ofReal_integral_eq_lintegral_ofReal hg.integrableOn (ae_of_all _ hg0)).symm

/-- An average strictly above a nonnegative level means the density law has more mass
than the constant density at that level. -/
theorem constant_mass_lt_withDensity {g : E → ℝ}
    (hg : Integrable g μ) (hg0 : ∀ y, 0 ≤ g y) {B : Set E}
    (hB : MeasurableSet B) (hBfin : μ B ≠ ⊤) {a : ℝ} (ha : 0 ≤ a)
    (hint : a * μ.real B < ∫ y in B, g y ∂μ) :
    ENNReal.ofReal a * μ B < (μ.withDensity (fun y => ENNReal.ofReal (g y))) B := by
  rw [withDensity_apply_eq_ofReal_setIntegral hg hg0 hB,
    ← ENNReal.ofReal_toReal hBfin, ← ENNReal.ofReal_mul ha]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
    (mul_nonneg ha ENNReal.toReal_nonneg)).mpr hint

/-- A density bounded by a level almost everywhere on a set has at most the mass of
the corresponding constant density there. -/
theorem withDensity_apply_le_constant {f : E → ℝ} {B : Set E}
    (hB : MeasurableSet B) {a : ℝ}
    (hfa : ∀ᵐ y ∂μ.restrict B, f y ≤ a) :
    (μ.withDensity (fun y => ENNReal.ofReal (f y))) B ≤ ENNReal.ofReal a * μ B := by
  rw [withDensity_apply _ hB]
  calc
    (∫⁻ y in B, ENNReal.ofReal (f y) ∂μ) ≤ ∫⁻ _ in B, ENNReal.ofReal a ∂μ :=
      lintegral_mono_ae (hfa.mono fun y hy => ENNReal.ofReal_le_ofReal hy)
    _ = ENNReal.ofReal a * μ B := by simp

/-- Mass above the constant-density threshold forces a positive-volume superlevel
set. This supplies the nonempty-interior premise of separation. -/
theorem superlevel_measure_pos_of_constant_mass_lt {f : E → ℝ} {B : Set E}
    (hB : MeasurableSet B) {a : ℝ}
    (hmass : ENNReal.ofReal a * μ B <
      (μ.withDensity (fun y => ENNReal.ofReal (f y))) B) :
    0 < μ {y | a ≤ f y} := by
  by_contra hpos
  have hzero : μ {y | a ≤ f y} = 0 := le_antisymm (not_lt.mp hpos) bot_le
  have hfa : ∀ᵐ y ∂μ, f y ≤ a :=
    (measure_eq_zero_iff_ae_notMem.mp hzero).mono fun y hy => (not_le.mp hy).le
  exact hmass.not_ge (withDensity_apply_le_constant hB (ae_restrict_of_ae hfa))

end Riesz2.LogConcaveDensityLimits.Internal

namespace Riesz2.LogConcaveDensityLimits.Internal

open Metric MeasureTheory.Measure
open scoped MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    [CompleteSpace E] {μ : Measure E} [IsAddHaarMeasure μ]

/-- At a Lebesgue point of the limit density, every positive lower level is eventually
a lower bound for the approximating log-concave densities. -/
theorem eventually_le_density_at_lebesgue_point
    {F : ℕ → E → ℝ} {g : E → ℝ}
    (hF : ∀ n, ConcaveOn ℝ {x | 0 < F n x} (fun x => Real.log (F n x)))
    (hg : Integrable g μ) (hg0 : ∀ y, 0 ≤ g y)
    (P : ℕ → ProbabilityMeasure E) (Q : ProbabilityMeasure E)
    (hP : ∀ n, (P n : Measure E) = μ.withDensity (fun y => ENNReal.ofReal (F n y)))
    (hQ : (Q : Measure E) = μ.withDensity (fun y => ENNReal.ofReal (g y)))
    (hweak : Tendsto P atTop (𝓝 Q)) {x : E} {a : ℝ} (ha0 : 0 < a) (ha : a < g x)
    (hLeb : Tendsto (fun r : ℝ => ⨍ y in closedBall x r, ‖g y - g x‖ ∂μ)
      (𝓝[>] 0) (𝓝 0)) : ∀ᶠ n in atTop, a ≤ F n x := by
  obtain ⟨r₀, hr₀, hint₀⟩ := exists_directional_ball_integral_gt hg ha hLeb
    (0 : E) (by simp)
  let B₀ := ball (x + (r₀ / 2) • (0 : E)) (r₀ / 4)
  have hm₀ : ENNReal.ofReal a * μ B₀ < (Q : Measure E) B₀ := by
    rw [hQ]
    exact constant_mass_lt_withDensity hg hg0 isOpen_ball.measurableSet
      measure_ball_lt_top.ne ha0.le hint₀
  have hlarge : ∀ᶠ n in atTop, ENNReal.ofReal a * μ B₀ < (P n : Measure E) B₀ :=
    eventually_lt_of_lt_liminf (hm₀.trans_le
      (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak isOpen_ball))
  by_contra hbad
  have hbad' : ∃ᶠ n in atTop, F n x < a := by
    simpa only [not_le] using not_eventually.mp hbad
  obtain ⟨ns, hns, hnsall⟩ := exists_seq_forall_of_frequently (hbad'.and_eventually hlarge)
  have hsep (n : ℕ) : ∃ ℓ : StrongDual ℝ E, ℓ ≠ 0 ∧
      ∀ y, ℓ x < ℓ y → F (ns n) y < a := by
    apply exists_low_halfspace (μ := μ) (hF (ns n)) ha0 _ (hnsall n).1
    apply superlevel_measure_pos_of_constant_mass_lt isOpen_ball.measurableSet
    simpa only [hP] using (hnsall n).2
  obtain ⟨v, hv, ms, hms, hlow⟩ := exists_subseq_low_balls hsep
  obtain ⟨r, hr, hint⟩ := exists_directional_ball_integral_gt hg ha hLeb v hv.le
  let B := ball (x + (r / 2) • v) (r / 4)
  have hm : ENNReal.ofReal a * μ B < (Q : Measure E) B := by
    rw [hQ]
    exact constant_mass_lt_withDensity hg hg0 isOpen_ball.measurableSet
      measure_ball_lt_top.ne ha0.le hint
  have hbounded : ∀ᶠ n in atTop,
      (P (ns (ms n)) : Measure E) B ≤ ENNReal.ofReal a * μ B := by
    filter_upwards [hlow r hr] with n hn
    rw [hP]
    apply withDensity_apply_le_constant isOpen_ball.measurableSet
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with y hy
    exact (hn y hy).le
  have hweak' : Tendsto (fun n => P (ns (ms n))) atTop (𝓝 Q) :=
    hweak.comp (hns.comp hms.tendsto_atTop)
  have hlimlower := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak'
    (G := B) isOpen_ball
  have hlimupper : liminf (fun n => (P (ns (ms n)) : Measure E) B) atTop ≤
      ENNReal.ofReal a * μ B := by
    exact (liminf_le_liminf hbounded).trans_eq (liminf_const _)
  exact hm.not_ge (hlimlower.trans hlimupper)

/-- Weak convergence of log-concave densities to a density implies the one-sided
almost everywhere limit inferior bound used by the Scheffé and representative arguments. -/
theorem le_liminf_of_weak
    {F : ℕ → E → ℝ} {g : E → ℝ}
    (hF : ∀ n, ConcaveOn ℝ {x | 0 < F n x} (fun x => Real.log (F n x)))
    (hg : Integrable g μ) (hg0 : ∀ y, 0 ≤ g y)
    (P : ℕ → ProbabilityMeasure E) (Q : ProbabilityMeasure E)
    (hP : ∀ n, (P n : Measure E) = μ.withDensity (fun y => ENNReal.ofReal (F n y)))
    (hQ : (Q : Measure E) = μ.withDensity (fun y => ENNReal.ofReal (g y)))
    (hweak : Tendsto P atTop (𝓝 Q)) :
    ∀ᵐ x ∂μ, ENNReal.ofReal (g x) ≤
      liminf (fun n => ENNReal.ofReal (F n x)) atTop := by
  have hLeb := (Besicovitch.vitaliFamily μ).ae_tendsto_average_norm_sub hg.locallyIntegrable
  filter_upwards [hLeb] with x hx
  have hx' := hx.comp (Besicovitch.tendsto_filterAt μ x)
  refine (le_liminf_iff).mpr fun b hb => ?_
  have hbfin : b ≠ ⊤ := ne_top_of_lt hb
  have hgpos : 0 < g x := ENNReal.ofReal_pos.mp (bot_le.trans_lt hb)
  have hb' : b.toReal < g x := by
    apply (ENNReal.ofReal_lt_ofReal_iff hgpos).mp
    rwa [ENNReal.ofReal_toReal hbfin]
  obtain ⟨a, hba, hag⟩ := exists_between hb'
  have ha0 : 0 < a := ENNReal.toReal_nonneg.trans_lt hba
  have hevent := eventually_le_density_at_lebesgue_point hF hg hg0 P Q hP hQ hweak ha0 hag hx'
  filter_upwards [hevent] with n hn
  calc
    b = ENNReal.ofReal b.toReal := (ENNReal.ofReal_toReal hbfin).symm
    _ < ENNReal.ofReal a := (ENNReal.ofReal_lt_ofReal_iff ha0).mpr hba
    _ ≤ ENNReal.ofReal (F n x) := ENNReal.ofReal_le_ofReal hn

end Riesz2.LogConcaveDensityLimits.Internal

namespace Riesz2

open scoped BoundedContinuousFunction

/-- A log-concave representative of the limiting density and unweighted L¹ convergence. -/
theorem logConcaveDensity_limits (d : ℕ) (hd : 1 ≤ d)
    (F : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (hF : ∀ n, (Measurable (F n) ∧ (∀ x, 0 ≤ F n x) ∧
      (∫⁻ x, ENNReal.ofReal (F n x)) = 1) ∧
      ConcaveOn ℝ {x | 0 < F n x} (fun x => Real.log (F n x)))
    (hg : Measurable g ∧ (∀ x, 0 ≤ g x) ∧ (∫⁻ x, ENNReal.ofReal (g x)) = 1)
    (hweak : ∀ φ : EuclideanSpace ℝ (Fin d) →ᵇ ℝ,
      Tendsto (fun n => ∫ x, φ x ∂volume.withDensity (fun x => ENNReal.ofReal (F n x)))
        atTop (𝓝 (∫ x, φ x ∂volume.withDensity (fun x => ENNReal.ofReal (g x))))) :
    (∃ g' : EuclideanSpace ℝ (Fin d) → ℝ,
      (Measurable g' ∧ (∀ x, 0 ≤ g' x) ∧ (∫⁻ x, ENNReal.ofReal (g' x)) = 1) ∧
      ConcaveOn ℝ {x | 0 < g' x} (fun x => Real.log (g' x)) ∧ g' =ᵐ[volume] g) ∧
    Tendsto (fun n => ∫⁻ x, ENNReal.ofReal |F n x - g x|) atTop (𝓝 0) := by
  let E := EuclideanSpace ℝ (Fin d)
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hprobF (n : ℕ) : IsProbabilityMeasure
      (volume.withDensity (fun x => ENNReal.ofReal (F n x))) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact (hF n).1.2.2
  have hprobg : IsProbabilityMeasure
      (volume.withDensity (fun x => ENNReal.ofReal (g x))) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hg.2.2
  let P : ℕ → ProbabilityMeasure E := fun n => ⟨volume.withDensity
    (fun x => ENNReal.ofReal (F n x)), hprobF n⟩
  let Q : ProbabilityMeasure E := ⟨volume.withDensity
    (fun x => ENNReal.ofReal (g x)), hprobg⟩
  have hgint : Integrable g := ⟨hg.1.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ hg.2.1)).mpr (by rw [hg.2.2]; exact ENNReal.one_lt_top)⟩
  have hweak' : Tendsto P atTop (𝓝 Q) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr hweak
  have hlim := LogConcaveDensityLimits.Internal.le_liminf_of_weak
    (fun n => (hF n).2) hgint hg.2.1 P Q (fun _ => rfl) rfl hweak'
  obtain ⟨⟨g', hgm, hg0, hgmass, hglc, heq⟩, hL1⟩ :=
    LogConcaveDensityLimits.Internal.density_limits_of_le_liminf
      (fun n => (hF n).1.1) (fun n => (hF n).1.2.1) (fun n => (hF n).1.2.2)
      (fun n => (hF n).2) hg.1 hg.2.1 hg.2.2 hlim
  exact ⟨⟨g', ⟨hgm, hg0, hgmass⟩, hglc, heq⟩, hL1⟩

end Riesz2

end
