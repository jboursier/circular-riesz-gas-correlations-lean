/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.External.LogConcaveConvergence
public import Riesz2.ToMathlib.DensityTestVariation
public import Riesz2.Frozen.ConvergesInLawAlong
public import Riesz1.Frozen.NormalLaw
public import Riesz1.Gibbs.AnchoredCoordinates
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian moment convergence from the convergence of log-concave densities

Cule–Samworth Proposition 2(c), supplied as an explicit argument, controls
unbounded first and second moments by its weighted density difference.
The one-dimensional Euclidean carrier is transported to the real line.
-/

public section
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace Riesz2.LogConcaveGaussianMoments

/-- The centered Gaussian density is log-concave for every positive variance. -/
lemma gaussian_logConcave (v : ℝ≥0) (hv : 0 < v) :
    ConcaveOn ℝ {x | 0 < gaussianPDFReal 0 v x}
      (fun x => Real.log (gaussianPDFReal 0 v x)) := by
  have hs : {x | 0 < gaussianPDFReal 0 v x} = (univ : Set ℝ) := by
    ext x
    simp [gaussianPDFReal_pos 0 v x hv.ne']
  rw [hs]
  have hq : ConcaveOn ℝ univ (fun x : ℝ => -(x ^ 2)) := even_two.convexOn_pow.neg
  have hc := (hq.smul (by positivity : (0 : ℝ) ≤ (2 * (v : ℝ))⁻¹)).add_const
    (Real.log (Real.sqrt (2 * Real.pi * v))⁻¹)
  apply hc.congr
  intro x _
  simp only [Pi.add_apply, smul_eq_mul, gaussianPDFReal, sub_zero]
  rw [Real.log_mul (inv_ne_zero (Real.sqrt_ne_zero'.mpr (by positivity)))
    (Real.exp_ne_zero _), Real.log_exp]
  ring

/-- The Euclidean density convergence theorem gives exponential-weighted density convergence on ℝ. -/
theorem weighted_density_convergence_internal
    (hconvergence : External.LogConcaveConvergence)
    (f : ℕ → ℝ → ℝ)
    (hf : ∀ n, Measurable (f n) ∧ (∀ x, 0 ≤ f n x) ∧
      (∫⁻ x, ENNReal.ofReal (f n x)) = 1 ∧
      ConcaveOn ℝ {x | 0 < f n x} (fun x => Real.log (f n x)))
    (v : ℝ≥0) (hv : 0 < v)
    (hw : ConvergesInLawAlong atTop
      (fun n => volume.withDensity (fun x => ENNReal.ofReal (f n x))) (Riesz1.normalLaw v)) :
    ∃ a : ℝ, 0 < a ∧ Tendsto
      (fun n => ∫⁻ x, ENNReal.ofReal
        (Real.exp (a * |x|) * |f n x - gaussianPDFReal 0 v x|)) atTop (𝓝 0) := by
  let E := EuclideanSpace ℝ (Fin 1)
  let e : E ≃L[ℝ] ℝ := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)
  have he : MeasurePreserving e :=
    (volume_preserving_piUnique (fun _ : Fin 1 => ℝ)).comp
      (PiLp.volume_preserving_ofLp (Fin 1))
  have henorm (x : E) : ‖x‖ = |e x| := by
    simp [E, e, EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]
  have hmass (u : ℝ → ℝ) (hu : Measurable u) :
      (∫⁻ x : E, ENNReal.ofReal (u (e x))) = ∫⁻ x, ENNReal.ofReal (u x) :=
    he.lintegral_comp (hu.ennreal_ofReal)
  have hlaw (u : ℝ → ℝ) (hu : Measurable u) :
      (volume.withDensity (fun x : E => ENNReal.ofReal (u (e x)))).map e =
        volume.withDensity (fun x => ENNReal.ofReal (u x)) := by
    rw [Riesz1.map_withDensity_comp volume e.continuous.measurable hu.ennreal_ofReal,
      he.map_eq]
  let g := gaussianPDFReal 0 v
  have hg : Measurable g ∧ (∀ x, 0 ≤ g x) ∧ (∫⁻ x, ENNReal.ofReal (g x)) = 1 :=
    ⟨measurable_gaussianPDFReal 0 v, gaussianPDFReal_nonneg 0 v,
      lintegral_gaussianPDFReal_eq_one 0 hv.ne'⟩
  have hgE : Measurable (g ∘ e) ∧ (∀ x, 0 ≤ g (e x)) ∧
      (∫⁻ x : E, ENNReal.ofReal (g (e x))) = 1 :=
    ⟨hg.1.comp e.continuous.measurable, fun x => hg.2.1 _, (hmass g hg.1).trans hg.2.2⟩
  have hglog : ConcaveOn ℝ {x : E | 0 < g (e x)} (fun x => Real.log (g (e x))) :=
    (gaussian_logConcave v hv).comp_linearMap e.toLinearMap
  obtain ⟨a₀, ha₀, b₀, henv⟩ := (hconvergence 1 (by omega)).2 (g ∘ e) hgE hglog
  have hwE (φ : E →ᵇ ℝ) :
      Tendsto (fun n => ∫ x : E, φ x ∂volume.withDensity (fun x => ENNReal.ofReal (f n (e x))))
        atTop (𝓝 (∫ x : E, φ x ∂volume.withDensity (fun x => ENNReal.ofReal (g (e x))))) := by
    have hi (u : ℝ → ℝ) (hu : Measurable u) :
        (∫ x : E, φ x ∂volume.withDensity (fun x => ENNReal.ofReal (u (e x)))) =
          ∫ x, φ (e.symm x) ∂volume.withDensity (fun x => ENNReal.ofReal (u x)) := by
      rw [← hlaw u hu, integral_map e.continuous.measurable.aemeasurable (by fun_prop)]
      simp only [ContinuousLinearEquiv.symm_apply_apply]
    have ht := hw.2.2 (φ.compContinuous ⟨e.symm, e.symm.continuous⟩)
    rw [Riesz1.normalLaw, gaussianReal_of_var_ne_zero 0 hv.ne'] at ht
    simpa only [hi _ (hf _).1, hi g hg.1, BoundedContinuousFunction.compContinuous_apply,
      g, gaussianPDF_def, ContinuousMap.coe_mk] using ht
  have hfc : ∀ n, (Measurable (fun x : E => f n (e x)) ∧
      (∀ x, 0 ≤ f n (e x)) ∧ (∫⁻ x : E, ENNReal.ofReal (f n (e x))) = 1) ∧
      ConcaveOn ℝ {x : E | 0 < f n (e x)} (fun x => Real.log (f n (e x))) :=
    fun n => ⟨⟨(hf n).1.comp e.continuous.measurable, fun x => (hf n).2.1 _,
      (hmass _ (hf n).1).trans (hf n).2.2.1⟩,
      (hf n).2.2.2.comp_linearMap e.toLinearMap⟩
  have ht := ((hconvergence 1 (by omega)).1 (fun n x => f n (e x)) (g ∘ e)
    hfc hgE hwE).2.2 a₀ b₀ ha₀ henv (a₀ / 2) (half_pos ha₀) (by linarith)
  refine ⟨a₀ / 2, half_pos ha₀, ?_⟩
  have hm (n : ℕ) : Measurable (fun x : ℝ => ENNReal.ofReal
      (Real.exp (a₀ / 2 * |x|) * |f n x - g x|)) := by
    simpa only [Real.norm_eq_abs, Pi.mul_apply, Pi.sub_apply, id_eq] using
      (((((measurable_id : Measurable (fun x : ℝ => x)).norm.const_mul (a₀ / 2)).exp).mul
        ((hf n).1.sub hg.1).norm).ennreal_ofReal)
  have hi (n : ℕ) := he.lintegral_comp (hm n)
  simp only [Function.comp_def, henorm] at ht
  exact ht.congr hi

/-- Polynomial tests are controlled by any positive exponential weight. -/
lemma abs_pow_le_exp (a : ℝ) (ha : 0 < a) (p : ℕ) (x : ℝ) :
    |x ^ p| ≤ (a⁻¹ ^ p * (p.factorial : ℝ)) * Real.exp (a * |x|) := by
  have hb := (div_le_iff₀ (show (0 : ℝ) < p.factorial by positivity)).mp
    (Real.pow_div_factorial_le_exp (a * |x|) (by positivity) p)
  calc
    |x ^ p| = a⁻¹ ^ p * (a * |x|) ^ p := by
      rw [abs_pow, mul_pow, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ ha.ne', one_pow, one_mul]
    _ ≤ a⁻¹ ^ p * (Real.exp (a * |x|) * (p.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- First and second moments follow from Proposition 2(c). Individual moment
integrability is explicit. No uniform moment or tail estimate is used. -/
theorem moments_tendsto_internal (hconvergence : External.LogConcaveConvergence)
    (μ : ℕ → Measure ℝ)
    (hd : ∀ n, ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧
      ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) ∧
      μ n = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hi : ∀ n, Integrable (fun x : ℝ => x) (μ n) ∧ Integrable (fun x : ℝ => x ^ 2) (μ n))
    (v : ℝ≥0) (hv : 0 < v)
    (hw : ConvergesInLawAlong atTop μ (Riesz1.normalLaw v)) :
    Tendsto (fun n => ∫ x : ℝ, x ∂μ n) atTop (𝓝 (∫ x : ℝ, x ∂Riesz1.normalLaw v)) ∧
      Tendsto (fun n => ∫ x : ℝ, x ^ 2 ∂μ n) atTop
        (𝓝 (∫ x : ℝ, x ^ 2 ∂Riesz1.normalLaw v)) := by
  choose f hfm hf0 hlog hμ using hd
  have hf (n : ℕ) : Measurable (f n) ∧ (∀ x, 0 ≤ f n x) ∧
      (∫⁻ x, ENNReal.ofReal (f n x)) = 1 ∧
      ConcaveOn ℝ {x | 0 < f n x} (fun x => Real.log (f n x)) := by
    have hp := (hw.1 n).measure_univ
    rw [hμ n, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hp
    exact ⟨hfm n, hf0 n, hp, hlog n⟩
  obtain ⟨a, ha, ht⟩ := weighted_density_convergence_internal hconvergence f hf v hv
    (by simpa only [← hμ] using hw)
  have hg : Riesz1.normalLaw v = volume.withDensity
      (fun x => ENNReal.ofReal (gaussianPDFReal 0 v x)) :=
    gaussianReal_of_var_ne_zero 0 hv.ne'
  have hg1 : Integrable (fun x : ℝ => x) (Riesz1.normalLaw v) :=
    (memLp_id_gaussianReal 1).integrable (by norm_num)
  have hg2 : Integrable (fun x : ℝ => x ^ 2) (Riesz1.normalLaw v) :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mp (memLp_id_gaussianReal 2)
  have hm (p : ℕ) (hif : ∀ n, Integrable (fun x : ℝ => x ^ p) (μ n))
      (hig : Integrable (fun x : ℝ => x ^ p) (Riesz1.normalLaw v)) :
      Tendsto (fun n => ∫ x : ℝ, x ^ p ∂μ n) atTop
        (𝓝 (∫ x : ℝ, x ^ p ∂Riesz1.normalLaw v)) := by
    let C : ℝ := a⁻¹ ^ p * (p.factorial : ℝ)
    have hscaled : Tendsto (fun n => ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal
        (Real.exp (a * |x|) * |f n x - gaussianPDFReal 0 v x|)) atTop (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul ht (Or.inr ENNReal.ofReal_ne_top)
    have hzero : Tendsto (fun n => ENNReal.ofReal |(∫ x : ℝ, x ^ p ∂μ n) -
        (∫ x : ℝ, x ^ p ∂Riesz1.normalLaw v)|) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hscaled (fun _ => bot_le)
      intro n
      have hb := ofReal_abs_integral_sub_density_le volume (hfm n) (hf0 n)
        (measurable_gaussianPDFReal 0 v) (gaussianPDFReal_nonneg 0 v)
        (hμ n ▸ hif n) (hg ▸ hig)
      rw [← hμ n, ← hg] at hb
      refine hb.trans ?_
      dsimp only
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_mono
      intro x
      dsimp only
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ C)]
      apply ENNReal.ofReal_le_ofReal
      calc
        |x ^ p| * |f n x - gaussianPDFReal 0 v x| ≤
            (C * Real.exp (a * |x|)) * |f n x - gaussianPDFReal 0 v x| := by
          exact mul_le_mul_of_nonneg_right (abs_pow_le_exp a ha p x) (abs_nonneg _)
        _ = _ := by ring
    have hr := (ENNReal.tendsto_toReal_zero_iff).mpr hzero
    simp only [ENNReal.toReal_ofReal (abs_nonneg _)] at hr
    exact tendsto_iff_dist_tendsto_zero.mpr (by simpa only [Real.dist_eq] using hr)
  constructor
  · simpa only [pow_one] using hm 1
      (by simpa only [pow_one] using fun n => (hi n).1)
      (by simpa only [pow_one] using hg1)
  · exact hm 2 (fun n => (hi n).2) hg2

end Riesz2.LogConcaveGaussianMoments

end
