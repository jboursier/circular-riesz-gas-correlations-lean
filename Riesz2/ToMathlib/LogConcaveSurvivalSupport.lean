/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.LogConcave.Survival
public import Riesz1.ToMathlib.LogConcave.PrekopaContinuity

/-!
# Log-concavity of survival on its whole positive support

The companion library proves log-concavity on `[0,b)`. Clamping a real
threshold at zero extends that conclusion to the whole positive support
`(-∞,b)` of the survival function of a density positive on `(0,b)`.
-/

public section

open MeasureTheory Set

namespace Riesz2

/-- A log-concave density positive exactly on `(0,b)` has a log-concave
survival function on its entire positive support, including negative
thresholds. -/
theorem concaveOn_log_survival_Iio {b : ℝ} {f : ℝ → ℝ} (hb : 0 < b)
    (hf : Integrable f) (hpos : ∀ x ∈ Ioo (0 : ℝ) b, 0 < f x)
    (hzero : ∀ x ∉ Ioo (0 : ℝ) b, f x = 0)
    (hlog : ConcaveOn ℝ (Ioo (0 : ℝ) b) (fun x => Real.log (f x))) :
    ConcaveOn ℝ (Iio b) (fun u => Real.log (∫ x in Ici u, f x)) := by
  let S : ℝ → ℝ := fun u => ∫ x in Ici u, f x
  have hclamp (u : ℝ) : S u = S (max 0 u) := by
    dsimp only [S]
    rw [← integral_indicator measurableSet_Ici, ← integral_indicator measurableSet_Ici]
    congr 1
    funext x
    simp only [Set.indicator_apply, Set.mem_Ici]
    by_cases hx : x ∈ Ioo (0 : ℝ) b
    · by_cases hu : u ≤ x
      · have hmax : max 0 u ≤ x := max_le hx.1.le hu
        simp only [ite_eq_left hu, ite_eq_left hmax]
      · have hmax : ¬max 0 u ≤ x := fun h => hu ((le_max_right _ _).trans h)
        simp only [ite_eq_right hu, ite_eq_right hmax]
    · simp [hzero x hx]
  have hnonneg : ∀ x, 0 ≤ f x := Riesz1.logConcave_nonneg hpos hzero
  have hmono : Antitone S := by
    intro u v huv
    exact setIntegral_mono_set hf.integrableOn (Filter.Eventually.of_forall hnonneg)
      (Filter.Eventually.of_forall (fun x hx => huv.trans hx))
  have hc := Riesz1.logConcave_concaveOn_log_survival hf hpos hzero hlog
  have hm (u : ℝ) (hu : u < b) : max 0 u ∈ Ico (0 : ℝ) b :=
    ⟨le_max_left _ _, max_lt hb hu⟩
  refine ⟨convex_Iio b, fun u hu v hv a c ha hc' hac => ?_⟩
  have hmid := (convex_Ico (0 : ℝ) b) (hm u hu) (hm v hv) ha hc' hac
  have hle : max 0 (a * u + c * v) ≤ a * max 0 u + c * max 0 v := by
    apply max_le
    · exact add_nonneg (mul_nonneg ha (le_max_left _ _)) (mul_nonneg hc' (le_max_left _ _))
    · exact add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) ha)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) hc')
  have hSpos : 0 < S (a * max 0 u + c * max 0 v) :=
    Riesz1.logConcave_survival_pos hf hpos hzero hmid.1 hmid.2
  have hi := hc.2 (hm u hu) (hm v hv) ha hc' hac
  change a * Real.log (S u) + c * Real.log (S v) ≤ Real.log (S (a * u + c * v))
  rw [hclamp u, hclamp v, hclamp (a * u + c * v)]
  exact hi.trans (Real.log_le_log hSpos (hmono hle))

/-- Internal measure bridge: an interval density that is positive and
log-concave gives log-concavity of the actual probability of a closed upper
ray. Finite mass proves integrability before real integrals are used. -/
theorem interval_density_log_survival {b : ℝ} (hb : 0 < b)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {f : ℝ → ℝ}
    (hf : ContinuousOn f (Ioo (0 : ℝ) b))
    (hpos : ∀ x ∈ Ioo (0 : ℝ) b, 0 < f x)
    (hlog : ConcaveOn ℝ (Ioo (0 : ℝ) b) (fun x => Real.log (f x)))
    (hν : ν = (volume.restrict (Ioo (0 : ℝ) b)).withDensity
      (fun x => ENNReal.ofReal (f x))) :
    ConcaveOn ℝ (Iio b) (fun u => Real.log ((ν (Ici u)).toReal)) := by
  let F := (Ioo (0 : ℝ) b).indicator f
  have hFmeas : Measurable F := Riesz1.measurable_indicator_of_continuousOn isOpen_Ioo hf
  have hFpos (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) b) : 0 < F x := by
    simpa only [F, indicator_of_mem hx] using hpos x hx
  have hFzero (x : ℝ) (hx : x ∉ Ioo (0 : ℝ) b) : F x = 0 := indicator_of_notMem hx _
  have hFnonneg := Riesz1.logConcave_nonneg hFpos hFzero
  have hνF : ν = volume.withDensity (fun x => ENNReal.ofReal (F x)) := by
    rw [hν, ← withDensity_indicator measurableSet_Ioo]
    congr 1
    funext x
    by_cases hx : x ∈ Ioo (0 : ℝ) b
    · simp only [F, indicator_of_mem hx]
    · simp only [F, indicator_of_notMem hx, ENNReal.ofReal_zero]
  have hFint : Integrable F := by
    refine ⟨hFmeas.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hFnonneg)).mpr ?_⟩
    have hmass : ∫⁻ x, ENNReal.ofReal (F x) = 1 := by
      rw [← Measure.restrict_univ (μ := volume), ← withDensity_apply _ MeasurableSet.univ,
        ← hνF, measure_univ]
    rw [hmass]
    exact ENNReal.one_lt_top
  have hFlog : ConcaveOn ℝ (Ioo (0 : ℝ) b) (fun x => Real.log (F x)) :=
    hlog.congr (fun x hx => congrArg Real.log (indicator_of_mem hx f).symm)
  have hsurv (u : ℝ) : (ν (Ici u)).toReal = ∫ x in Ici u, F x := by
    rw [hνF, withDensity_apply _ measurableSet_Ici,
      ← ofReal_integral_eq_lintegral_ofReal hFint.integrableOn
        (Filter.Eventually.of_forall hFnonneg), ENNReal.toReal_ofReal
          (integral_nonneg (fun x => hFnonneg x))]
  have hc := concaveOn_log_survival_Iio hb hFint hFpos hFzero hFlog
  exact hc.congr (fun u _ => congrArg Real.log (hsurv u).symm)

end Riesz2
