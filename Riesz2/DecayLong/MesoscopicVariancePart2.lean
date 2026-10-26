/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.MesoscopicVariance
public import Riesz2.ToMathlib.LogConcaveGaussianMoments
public import Riesz1.Frozen.NormalLaw
public import Riesz2.Thermodynamic.MesoscopicGapLimitsPart2
import Riesz2.Sanity.FiniteLaws
import Riesz2.Frozen.External.LogConcaveConvergenceProof

/-!
# Log-concave moment convergence

Moment convergence for Lemma 5.19, using the weak convergence convention
and Gaussian law of the companion paper. Proposition 2(c) of Cule–Samworth
gives convergence of the first two moments through a weighted density
difference.
-/

public section

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace Riesz2.MesoscopicVariance

/-- The second moment of the centered companion Gaussian equals its
variance parameter, including variance zero. -/
theorem normalLaw_second_moment (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 2 ∂Riesz1.normalLaw v) = (v : ℝ) := by
  have h := ProbabilityTheory.variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [ProbabilityTheory.variance_eq_integral (X := fun x : ℝ => x)
    measurable_id.aemeasurable] at h
  simpa only [ProbabilityTheory.integral_id_gaussianReal, sub_zero, Riesz1.normalLaw] using h

/-- See Lemma 5.19:
probability laws with bounded, compactly supported log-concave Lebesgue
densities converging weakly to a nondegenerate centered Gaussian have
first moments tending to zero and second moments tending to its variance.
The proof supplies finite moments from the actual densities. -/
theorem logconcave_moments (μ : ℕ → Measure ℝ)
    (hdensity : ∀ k, ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧
      Bornology.IsBounded (range f) ∧ HasCompactSupport f ∧
      ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) ∧
      μ k = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (v : ℝ≥0) (_hv : 0 < v)
    (hw : ConvergesInLawAlong atTop μ (Riesz1.normalLaw v)) :
    Tendsto (fun k => ∫ x : ℝ, x ∂μ k) atTop (𝓝 0) ∧
      Tendsto (fun k => ∫ x : ℝ, x ^ 2 ∂μ k) atTop (𝓝 (v : ℝ)) := by
  have : ∀ k, IsProbabilityMeasure (μ k) := hw.1
  have hd : ∀ k, ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧
      ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) ∧
      μ k = volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
    intro k
    obtain ⟨f, hf, hnn, _, _, hlog, hμ⟩ := hdensity k
    exact ⟨f, hf, hnn, hlog, hμ⟩
  have hi (k : ℕ) : Integrable (fun x : ℝ => x) (μ k) ∧
      Integrable (fun x : ℝ => x ^ 2) (μ k) := by
    obtain ⟨f, hf, _, _, hc, _, hμ⟩ := hdensity k
    obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ x ∈ tsupport f, ‖x‖ ≤ R :=
      hc.isCompact.isBounded.exists_norm_le
    have hb : ∀ᵐ x ∂μ k, ‖x‖ ≤ R := by
      rw [hμ]
      apply (ae_withDensity_iff hf.ennreal_ofReal).mpr
      exact Eventually.of_forall fun x hx => hR x (subset_tsupport f (by
        intro hz
        exact hx (by rw [hz, ENNReal.ofReal_zero])))
    have hid : MemLp (fun x : ℝ => x) 2 (μ k) :=
      MemLp.of_bound measurable_id.aestronglyMeasurable R hb
    exact ⟨hid.integrable one_le_two,
      (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mp hid⟩
  have h := LogConcaveGaussianMoments.moments_tendsto_internal
    External.logConcaveConvergence μ hd hi v _hv hw
  rw [normalLaw_second_moment v] at h
  simpa only [Riesz1.normalLaw, ProbabilityTheory.integral_id_gaussianReal] using h

/-- See Lemma 5.19, the
distributional step. The law uses the finite block and
the paper's normalization, along arbitrary mesoscopic pairs. Initial
full-cycle blocks and singleton systems are allowed. -/
theorem finiteGapBlock_normalized_CLT
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (N K : ℕ → ℕ+)
    (hK : Tendsto (fun j => (K j : ℕ)) atTop atTop)
    (hKN : Tendsto (fun j => (K j : ℝ) / (N j : ℝ)) atTop (𝓝 0)) :
    ConvergesInLawAlong atTop
      (fun j => (gibbsMeasure (ofLong β s) (N j)).map
        (fun X => ((∑ i : Fin (K j : ℕ), finiteGapBlock X i) - (K j : ℝ)) /
          (K j : ℝ) ^ (s.val / 2)))
      (Riesz1.normalLaw ⟨Riesz1.countVariance (longParameters β s),
        companionCountVariance_nonneg β s⟩) := by
  have h := mesoscopic_gapCLT_pairs β s N (fun j => (K j : ℕ)) hK hKN
  have heq (j : ℕ) : (fun X : Riesz1.Configuration (N j) =>
      (K j : ℝ) ^ (-s.val / 2) *
        (cyclicGapSum (N j) ⟨0, (N j).pos⟩ (K j : ℕ) (gapVector X) - (K j : ℝ))) =
      (fun X => ((∑ i : Fin (K j : ℕ), finiteGapBlock X i) - (K j : ℝ)) /
        (K j : ℝ) ^ (s.val / 2)) := by
    funext X
    rw [cyclicGapSum_zero_eq_finiteGapBlock, show -s.val / 2 = -(s.val / 2) by ring,
      Real.rpow_neg (by positivity : (0 : ℝ) ≤ K j)]
    exact (mul_comm _ _).trans (div_eq_mul_inv _ _).symm
  have hv : NNReal.mk (Riesz1.countVariance (longParameters β s))
      (companionCountVariance_nonneg β s) =
      (⟨Riesz1.countVariance (longParameters β s), companionCountVariance_nonneg β s⟩ : ℝ≥0) :=
    NNReal.eq rfl
  rw [hv] at h
  simpa only [heq] using h

/-- Application of Proposition 2(c) of Cule–Samworth to normalized span
densities. Log-concavity and weak convergence are the inputs. An index shift
discards exceptional initial point masses before applying the result. -/
theorem variance_limit_of_logconcave_densities_internal
    (hconvergence : External.LogConcaveConvergence)
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (N K : ℕ → ℕ+)
    (hK : Tendsto (fun j => (K j : ℕ)) atTop atTop)
    (hKN : Tendsto (fun j => (K j : ℝ) / (N j : ℝ)) atTop (𝓝 0))
    (hdensity : ∀ᶠ j in atTop, ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧
      ConcaveOn ℝ (Function.support f) (fun x => Real.log (f x)) ∧
      (gibbsMeasure (ofLong β s) (N j)).map
        (fun X => ((∑ i : Fin (K j : ℕ), finiteGapBlock X i) - (K j : ℝ)) /
          (K j : ℝ) ^ (s.val / 2)) =
        volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    Tendsto (fun j =>
      let S := fun X : Riesz1.Configuration (N j) =>
        ∑ i : Fin (K j : ℕ), finiteGapBlock X i
      let h := integrable_finiteGapBlock_sum (ofLong β s) (N j) (K j)
      (Riesz1.variance (gibbsMeasure (ofLong β s) (N j)) S h).toReal /
        (K j : ℝ) ^ s.val) atTop (𝓝 (Riesz1.countVariance (longParameters β s))) := by
  let μ := fun j => (gibbsMeasure (ofLong β s) (N j)).map
    (fun X => ((∑ i : Fin (K j : ℕ), finiteGapBlock X i) - (K j : ℝ)) /
      (K j : ℝ) ^ (s.val / 2))
  have hw := finiteGapBlock_normalized_CLT β s N K hK hKN
  have hprob : ∀ j, IsProbabilityMeasure (μ j) := hw.1
  have hmeas (j : ℕ) : Measurable (fun X : Riesz1.Configuration (N j) =>
      ((∑ i : Fin (K j : ℕ), finiteGapBlock X i) - (K j : ℝ)) /
        (K j : ℝ) ^ (s.val / 2)) := by
    simp_rw [finiteGapBlock_sum_eq_blockLength]
    exact ((Riesz1.measurable_blockLength 0 (K j)).sub_const _).div_const _
  have hi (j : ℕ) : Integrable (fun x : ℝ => x) (μ j) ∧
      Integrable (fun x : ℝ => x ^ 2) (μ j) := by
    have : IsProbabilityMeasure (gibbsMeasure (ofLong β s) (N j)) :=
      FrozenSanity.gibbsMeasure_probability _ _
    have hbounded := (finiteGapBlock_sum_memLp (ofLong β s) (N j) (K j) ⊤).sub
      (memLp_const (K j : ℝ))
    have hnorm := hbounded.mul_const (((K j : ℝ) ^ (s.val / 2))⁻¹)
    have hid : MemLp (fun x : ℝ => x) 2 (μ j) := by
      dsimp only [μ]
      apply (memLp_map_measure_iff (g := fun x : ℝ => x)
        measurable_id.aestronglyMeasurable (hmeas j).aemeasurable).mpr
      simpa only [Function.comp_def, div_eq_mul_inv, Pi.sub_apply] using hnorm.mono_exponent (by simp : (2 : ℝ≥0∞) ≤ ⊤)
    exact ⟨hid.integrable one_le_two,
      (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mp hid⟩
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp hdensity
  have hd (j : ℕ) : ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧
      ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) ∧
      μ (j + j₀) = volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
    obtain ⟨f, hfm, hf0, hlog, heq⟩ := hj₀ (j + j₀) (by omega)
    have hs : Function.support f = {x | 0 < f x} := by
      ext x
      exact ⟨fun hx => lt_of_le_of_ne (hf0 x) (Ne.symm hx), fun hx => hx.ne'⟩
    exact ⟨f, hfm, hf0, hs ▸ hlog, heq⟩
  have hw' : ConvergesInLawAlong atTop (fun j => μ (j + j₀))
      (Riesz1.normalLaw ⟨Riesz1.countVariance (longParameters β s),
        companionCountVariance_nonneg β s⟩) :=
    ⟨fun j => hprob _, hw.2.1, fun f => (hw.2.2 f).comp (tendsto_add_atTop_nat j₀)⟩
  have hsecond : Tendsto (fun j => ∫ x : ℝ, x ^ 2 ∂μ j) atTop
      (𝓝 (∫ x : ℝ, x ^ 2 ∂Riesz1.normalLaw
        ⟨Riesz1.countVariance (longParameters β s), companionCountVariance_nonneg β s⟩)) := by
    apply (tendsto_add_atTop_iff_nat j₀).mp
    exact (LogConcaveGaussianMoments.moments_tendsto_internal hconvergence
      (fun j => μ (j + j₀)) hd (fun j => hi (j + j₀)) _
      (by exact limiting_variance_pos β s) hw').2
  have hGaussian : (∫ x : ℝ, x ^ 2 ∂Riesz1.normalLaw
      (⟨Riesz1.countVariance (longParameters β s), companionCountVariance_nonneg β s⟩ : ℝ≥0)) =
      Riesz1.countVariance (longParameters β s) := normalLaw_second_moment _
  rw [hGaussian] at hsecond
  apply hsecond.congr'
  have hadm := mesoscopic_pairs_eventually_admissible (fun j => (K j : ℕ)) N hK hKN
  filter_upwards [hadm, hK.eventually_ge_atTop 2] with j hj hKj
  have hN : 2 ≤ (N j : ℕ) := by omega
  rw [finiteGapBlock_normalized_second_moment β s _ _ hN]
  exact integral_map (hmeas j).aemeasurable (by fun_prop)

end Riesz2.MesoscopicVariance

end
