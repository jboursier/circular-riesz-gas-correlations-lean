/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Externals.PrekopaLeindlerProof
public import Riesz1.ToMathlib.LogConcave.MarginalConcave
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Tactic

/-!
# Log-concavity of survival without a prescribed interval support

The density-to-survival step in the proof of Theorem 1. This applies the
proved one-dimensional Prékopa–Leindler inequality to densities restricted
to upper rays. No choice of the endpoints of the density's support is
needed, and zeros are allowed throughout.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz2.GeneralLogConcaveSurvival

/-- The midpoint Prékopa inequality for upper-ray integrals of an
integrable log-concave density. The finite-dimensional input is reused
from Riesz 1 through the measure-preserving identification of `Fin 1 → ℝ`
with `ℝ`. -/
theorem sqrt_survival_mul_le {f : ℝ → ℝ} (hf : Measurable f)
    (hfi : Integrable f) (hnn : ∀ x, 0 ≤ f x)
    (hlog : ConcaveOn ℝ (Function.support f) (fun x => Real.log (f x)))
    (a b : ℝ) :
    Real.sqrt ((∫ x in Ici a, f x) * ∫ x in Ici b, f x) ≤
      ∫ x in Ici ((a + b) / 2), f x := by
  let F (t : ℝ) : ℝ → ℝ := (Ici t).indicator f
  have hF (t : ℝ) : Measurable (F t) := hf.indicator measurableSet_Ici
  have hFn (t x : ℝ) : 0 ≤ F t x := indicator_nonneg (fun x _ => hnn x) x
  have hFi (t : ℝ) : Integrable (F t) := hfi.indicator measurableSet_Ici
  have hmid (x y : ℝ) :
      Real.sqrt (F a x * F b y) ≤ F ((a + b) / 2) ((x + y) / 2) := by
    by_cases hx : x ∈ Ici a
    · by_cases hy : y ∈ Ici b
      · have hxy : (x + y) / 2 ∈ Ici ((a + b) / 2) := by
          change (a + b) / 2 ≤ (x + y) / 2
          linarith [show a ≤ x from hx, show b ≤ y from hy]
        simp only [F, indicator_of_mem hx, indicator_of_mem hy, indicator_of_mem hxy]
        simpa only [smul_eq_mul, one_div, div_eq_mul_inv, mul_comm, one_mul] using
          Riesz1.sqrt_mul_le_midpoint_of_concaveOn_log f hnn hlog x y
      · simp only [F, indicator_of_notMem hy, mul_zero, Real.sqrt_zero]
        exact hFn _ _
    · simp only [F, indicator_of_notMem hx, zero_mul, Real.sqrt_zero]
      exact hFn _ _
  have hPL := Riesz1.Externals.midpoint_lintegral (n := 0)
    (f := fun z => ENNReal.ofReal (F a (z 0)))
    (g := fun z => ENNReal.ofReal (F b (z 0)))
    (w := fun z => ENNReal.ofReal (F ((a + b) / 2) (z 0)))
    (((hF a).comp (measurable_pi_apply 0)).ennreal_ofReal)
    (((hF b).comp (measurable_pi_apply 0)).ennreal_ofReal)
    (((hF ((a + b) / 2)).comp (measurable_pi_apply 0)).ennreal_ofReal) (by
      intro x y
      change ENNReal.ofReal (F a (x 0)) ^ (1 - (1 / 2 : ℝ)) *
        ENNReal.ofReal (F b (y 0)) ^ (1 / 2 : ℝ) ≤
          ENNReal.ofReal (F ((a + b) / 2) ((1 / 2 : ℝ) * (x 0 + y 0)))
      norm_num only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
      rw [ENNReal.ofReal_rpow_of_nonneg (hFn a _) (by norm_num),
        ENNReal.ofReal_rpow_of_nonneg (hFn b _) (by norm_num),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (hFn a _) _),
        ← Real.mul_rpow (hFn a _) (hFn b _), ← Real.sqrt_eq_rpow]
      have he : (1 / 2 : ℝ) * (x 0 + y 0) = (x 0 + y 0) / 2 := by ring
      rw [he]
      exact ENNReal.ofReal_le_ofReal (hmid (x 0) (y 0)))
  have hbridge (t : ℝ) :
      (∫⁻ z : Fin 1 → ℝ, ENNReal.ofReal (F t (z 0))) =
        ∫⁻ x : ℝ, ENNReal.ofReal (F t x) :=
    Riesz1.PrekopaLeindler.lintegral_fin1 _
  rw [hbridge, hbridge, hbridge] at hPL
  have heq (t : ℝ) : ∫⁻ x, ENNReal.ofReal (F t x) = ENNReal.ofReal (∫ x, F t x) :=
    (ofReal_integral_eq_lintegral_ofReal (hFi t) (Filter.Eventually.of_forall (hFn t))).symm
  simp_rw [heq] at hPL
  have hIn (t : ℝ) : 0 ≤ ∫ x, F t x := integral_nonneg (hFn t)
  norm_num only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hPL
  rw [ENNReal.ofReal_rpow_of_nonneg (hIn a) (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (hIn b) (by norm_num),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (hIn a) _),
    ← Real.mul_rpow (hIn a) (hIn b), ← Real.sqrt_eq_rpow,
    ENNReal.ofReal_le_ofReal_iff (hIn _)] at hPL
  simpa only [F, integral_indicator measurableSet_Ici] using hPL

/-- The survival function of an integrable nonnegative log-concave
density has concave logarithm on its entire positive set. This is the
survival step of the proof of Theorem 1, without any assumption on the support endpoints. -/
theorem concaveOn_log_survival {f : ℝ → ℝ} (hf : Measurable f)
    (hfi : Integrable f) (hnn : ∀ x, 0 ≤ f x)
    (hlog : ConcaveOn ℝ (Function.support f) (fun x => Real.log (f x))) :
    ConcaveOn ℝ {t | 0 < ∫ x in Ici t, f x}
      (fun t => Real.log (∫ x in Ici t, f x)) := by
  let S := fun t => ∫ x in Ici t, f x
  have hanti : Antitone S := by
    intro a b hab
    exact setIntegral_mono_set hfi.integrableOn
      (Filter.Eventually.of_forall hnn)
      (Filter.Eventually.of_forall (fun x hx => hab.trans hx))
  have hconv : Convex ℝ {t | 0 < S t} := by
    intro x hx y hy a b ha hb hab
    change 0 < S x at hx
    change 0 < S y at hy
    have hmax : 0 < S (max x y) := by
      rcases le_total x y with h | h
      · simpa only [max_eq_right h] using hy
      · simpa only [max_eq_left h] using hx
    have hle : a * x + b * y ≤ max x y := by
      have hax := mul_le_mul_of_nonneg_left (le_max_left x y) ha
      have hby := mul_le_mul_of_nonneg_left (le_max_right x y) hb
      calc a * x + b * y ≤ a * max x y + b * max x y := add_le_add hax hby
        _ = (a + b) * max x y := by ring
        _ = max x y := by rw [hab, one_mul]
    exact hmax.trans_le (hanti hle)
  have hcont : Continuous S := by
    rw [continuous_iff_continuousAt]
    intro t
    have hc : ContinuousOn S (Ici (t - 1)) := hfi.integrableOn.continuousOn_Ici_primitive_Ici
    exact hc.continuousAt (Ici_mem_nhds (by linarith : t - 1 < t))
  apply Riesz1.concaveOn_of_continuousOn_midpoint hconv
    (hcont.continuousOn.log (fun t ht => ht.ne'))
  intro x hx y hy
  have hxy := sqrt_survival_mul_le hf hfi hnn hlog x y
  have hpos : 0 < Real.sqrt (S x * S y) := Real.sqrt_pos.mpr (mul_pos hx hy)
  have h := Real.log_le_log hpos hxy
  rw [Real.log_sqrt (mul_pos hx hy).le, Real.log_mul hx.ne' hy.ne'] at h
  exact h

/-- A log-concave probability density gives log-concavity of the actual
upper-ray probabilities. Normalization supplies integrability. The
Bochner integral of a potentially nonintegrable density is never used
to assert its total mass. -/
theorem probability_density_log_survival (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f : ℝ → ℝ} (hf : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hlog : ConcaveOn ℝ (Function.support f) (fun x => Real.log (f x)))
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    Integrable f ∧
      ConcaveOn ℝ {t | 0 < (μ (Ici t)).toReal}
        (fun t => Real.log ((μ (Ici t)).toReal)) := by
  have hmass : ∫⁻ x, ENNReal.ofReal (f x) = 1 := by
    rw [← Measure.restrict_univ (μ := volume),
      ← withDensity_apply _ MeasurableSet.univ, ← hμ, measure_univ]
  have hfi : Integrable f := by
    refine ⟨hf.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnn)).mpr ?_⟩
    rw [hmass]
    exact ENNReal.one_lt_top
  have heq (t : ℝ) : (μ (Ici t)).toReal = ∫ x in Ici t, f x := by
    rw [hμ, withDensity_apply _ measurableSet_Ici,
      ← ofReal_integral_eq_lintegral_ofReal hfi.integrableOn
        (Filter.Eventually.of_forall hnn),
      ENNReal.toReal_ofReal (integral_nonneg fun x => hnn x)]
  refine ⟨hfi, ?_⟩
  simpa only [heq] using concaveOn_log_survival hf hfi hnn hlog

end Riesz2.GeneralLogConcaveSurvival

end
