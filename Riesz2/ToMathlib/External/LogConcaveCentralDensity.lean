/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.WeakLogConcaveMoments
public import Riesz1.Gibbs.AnchoredCoordinates
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Tactic

/-!
# Central lower bounds for one-dimensional log-concave densities

Central-density lower bounds for log-concave functions on their positive support. All moment bounds are proved for the
actual probability measure, without any bounded-support assumption.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace Riesz2.LogConcaveCentralDensity

/-- The two closed rays cover the line, even for a measure with atoms. -/
theorem one_le_closed_ray_sum (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : ℝ) :
    1 ≤ (μ (Ici a)).toReal + (μ (Iic a)).toReal := by
  have hu : Ici a ∪ Iic a = univ := by
    ext x
    simp only [mem_union, mem_Ici, mem_Iic, mem_univ, iff_true]
    exact le_total a x
  have h := measure_union_le (μ := μ) (Ici a) (Iic a)
  rw [hu, measure_univ] at h
  have ht := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨measure_ne_top _ _, measure_ne_top _ _⟩) h
  simpa only [ENNReal.toReal_one, ENNReal.toReal_add
    (measure_ne_top _ _) (measure_ne_top _ _)] using ht

/-- Unit second moment gives quarter-quantile bounds at `-2` and `2`. -/
theorem quarter_quantiles_of_second_moment (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hi : Integrable (fun x : ℝ => x ^ 2) μ) (hsecond : (∫ x : ℝ, x ^ 2 ∂μ) = 1) :
    3 / 4 ≤ (μ (Ici (-2))).toReal ∧ (μ (Ici 2)).toReal ≤ 1 / 4 ∧
      3 / 4 ≤ (μ (Iic 2)).toReal ∧ (μ (Iic (-2))).toReal ≤ 1 / 4 := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ fun x : ℝ => sq_nonneg x) hi (4 : ℝ)
  rw [hsecond] at hm
  have htail : (μ {x : ℝ | 2 ≤ |x|}).toReal ≤ 1 / 4 := by
    have hset : {x : ℝ | 4 ≤ x ^ 2} = {x : ℝ | 2 ≤ |x|} := by
      ext x
      change 4 ≤ x ^ 2 ↔ 2 ≤ |x|
      constructor
      · intro hx
        by_contra hn
        have hn' : |x| < 2 := lt_of_not_ge hn
        nlinarith [sq_abs x, abs_nonneg x]
      · intro hx
        nlinarith [sq_abs x, sq_nonneg (|x| - 2)]
    rw [hset] at hm
    change 4 * (μ {x : ℝ | 2 ≤ |x|}).toReal ≤ 1 at hm
    linarith
  have hR : (μ (Ici 2)).toReal ≤ 1 / 4 := by
    apply le_trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)) htail
    intro x hx
    exact hx.trans (le_abs_self x)
  have hL : (μ (Iic (-2))).toReal ≤ 1 / 4 := by
    apply le_trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)) htail
    intro x (hx : x ≤ -2)
    exact (show 2 ≤ -x by linarith).trans (neg_le_abs x)
  exact ⟨by linarith [one_le_closed_ray_sum μ (-2)], hR,
    by linarith [one_le_closed_ray_sum μ 2], hL⟩

/-- A universal fourth-moment bound for every log-concave density with
unit second moment. The mean need not vanish for this step. -/
theorem exists_uniform_fourth_moment :
    ∃ M : ℝ, 0 < M ∧ ∀ (f : ℝ → ℝ), Measurable f →
      (∀ x, 0 ≤ f x) →
      ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) →
      ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      μ = volume.withDensity (fun x => ENNReal.ofReal (f x)) →
      Integrable (fun x : ℝ => x ^ 2) μ → (∫ x : ℝ, x ^ 2 ∂μ) = 1 →
      MemLp (fun x : ℝ => x ^ 2) 2 μ ∧ (∫ x : ℝ, (x ^ 2) ^ 2 ∂μ) ≤ M := by
  have hc : 0 < Real.log 3 / (2 * 2) :=
    LogConcaveQuantileTail.quarter_quantile_rate_pos (by norm_num)
  obtain ⟨M, hM, hb⟩ := LogConcaveQuantileTail.exists_fourth_moment_bound_internal
    hc (Real.exp_pos ((Real.log 3 / (2 * 2)) * 2)).le
  refine ⟨M, hM, fun f hf hnn hlog μ hprob hμ hi hsecond => ?_⟩
  have : IsProbabilityMeasure μ := hprob
  have hs : Function.support f = {x | 0 < f x} := by
    ext x
    simp only [Function.mem_support, mem_ofPred_eq]
    exact ne_comm.trans (hnn x).lt_iff_ne.symm
  have hlogs := hlog
  rw [← hs] at hlogs
  obtain ⟨hRL, hRR, hLL, hLR⟩ := quarter_quantiles_of_second_moment μ hi hsecond
  exact hb μ (WeakLogConcaveMoments.global_tail_of_quarter_quantiles μ
    (GeneralLogConcaveSurvival.probability_density_log_survival μ hf hnn hlogs hμ).2
    (WeakLogConcaveMoments.probability_density_log_lower_survival μ hf hnn hlogs hμ)
    (by norm_num : (0 : ℝ) < 2) hRL hRR hLL hLR)

/-- Elementary truncation inequality used to pass from fourth and
second moments to a lower bound on the first absolute moment. -/
theorem sq_le_truncated_first_add_fourth (x : ℝ) {T : ℝ} (hT : 0 < T) :
    x ^ 2 ≤ T * |x| + (x ^ 2) ^ 2 / T ^ 2 := by
  by_cases hx : |x| ≤ T
  · have h : |x| ^ 2 ≤ T * |x| := by nlinarith [abs_nonneg x]
    rw [sq_abs] at h
    exact h.trans (le_add_of_nonneg_right (by positivity))
  · have hx' : T ≤ |x| := (lt_of_not_ge hx).le
    have hsq : T ^ 2 ≤ x ^ 2 := by nlinarith [sq_abs x]
    have h : x ^ 2 ≤ (x ^ 2) ^ 2 / T ^ 2 := by
      rw [le_div_iff₀ (sq_pos_of_pos hT)]
      nlinarith [sq_nonneg x]
    exact h.trans (le_add_of_nonneg_left (mul_nonneg hT.le (abs_nonneg x)))

/-- An explicit nonzero first absolute moment from a unit second
moment and a fourth-moment bound. This is a general probability lemma. -/
theorem first_abs_moment_lower (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {M : ℝ} (hM : 0 < M)
    (hfour : MemLp (fun x : ℝ => x ^ 2) 2 μ)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂μ) = 1)
    (hbound : (∫ x : ℝ, (x ^ 2) ^ 2 ∂μ) ≤ M) :
    1 / (2 * (M + 1)) ≤ ∫ x : ℝ, |x| ∂μ := by
  have hi2 := hfour.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hi4 := (memLp_two_iff_integrable_sq
    (measurable_id.pow_const 2).aestronglyMeasurable).mp hfour
  change Integrable (fun x : ℝ => (x ^ 2) ^ 2) μ at hi4
  have hi1 : Integrable (fun x : ℝ => x) μ :=
    ((memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr hi2).integrable
      (by norm_num)
  have hT : 0 < M + 1 := by linarith
  have hb := integral_mono hi2 ((hi1.abs.const_mul (M + 1)).add (hi4.div_const _))
    (fun x => sq_le_truncated_first_add_fourth x hT)
  change (∫ x : ℝ, x ^ 2 ∂μ) ≤
    ∫ x : ℝ, (M + 1) * |x| + (x ^ 2) ^ 2 / (M + 1) ^ 2 ∂μ at hb
  rw [hsecond, integral_add (hi1.abs.const_mul _) (hi4.div_const _),
    integral_const_mul, integral_div] at hb
  have hq : M / (M + 1) ^ 2 ≤ 1 / 2 := by
    rw [div_le_iff₀ (sq_pos_of_pos hT)]
    nlinarith [sq_nonneg M]
  have hb' : 1 ≤ (M + 1) * (∫ x : ℝ, |x| ∂μ) + 1 / 2 :=
    hb.trans (add_le_add_right ((div_le_div_of_nonneg_right hbound
      (sq_nonneg (M + 1))).trans hq) _)
  rw [div_le_iff₀ (by positivity : 0 < 2 * (M + 1))]
  linarith

/-- Extract a point of positive density away from zero from a lower
bound on a one-sided first moment. The map `Y` may be either orientation
of the real coordinate. This is an internal moment-to-density lemma. -/
theorem exists_density_point_internal {f Y : ℝ → ℝ}
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hY : Measurable Y) (hiY : Integrable Y μ) (habs : ∀ x, |Y x| = |x|)
    (hi2 : Integrable (fun x : ℝ => x ^ 2) μ) (hsecond : (∫ x : ℝ, x ^ 2 ∂μ) = 1)
    {δ R d p : ℝ} (hδ : 0 < δ) (hR : 0 < R) (hd : 0 < d)
    (hp : p ≤ ∫ x, max (Y x) 0 ∂μ)
    (hgap : δ + (2 * R * d) * R + 1 / R < p) :
    ∃ x : ℝ, δ ≤ Y x ∧ |x| ≤ R ∧ d ≤ f x := by
  let E := {x : ℝ | δ ≤ Y x ∧ |x| ≤ R}
  have hE : MeasurableSet E := (measurableSet_le measurable_const hY).inter
    (measurableSet_le continuous_abs.measurable measurable_const)
  by_contra hn
  have hsmall : ∀ x ∈ E, f x ≤ d := by
    intro x hx
    exact (lt_of_not_ge fun h => hn ⟨x, hx.1, hx.2, h⟩).le
  have hvol : volume E ≤ ENNReal.ofReal (2 * R) := by
    calc volume E ≤ volume (Icc (-R) R) := measure_mono fun x hx => abs_le.mp hx.2
      _ = ENNReal.ofReal (2 * R) := by rw [Real.volume_Icc]; congr 1; ring
  have hmass : μ E ≤ ENNReal.ofReal (2 * R * d) := by
    rw [hμ, withDensity_apply _ hE]
    calc (∫⁻ x in E, ENNReal.ofReal (f x)) ≤ ∫⁻ _x in E, ENNReal.ofReal d := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem hE] with x hx
          exact ENNReal.ofReal_le_ofReal (hsmall x hx)
      _ = ENNReal.ofReal d * volume E := by rw [lintegral_const, Measure.restrict_apply_univ]
      _ ≤ ENNReal.ofReal d * ENNReal.ofReal (2 * R) := by gcongr
      _ = ENNReal.ofReal (2 * R * d) := by rw [← ENNReal.ofReal_mul hd.le]; congr 1; ring
  have hmassR : (μ E).toReal ≤ 2 * R * d := by
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * R * d)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
  have hpt (x : ℝ) : max (Y x) 0 ≤ δ + E.indicator (fun _ => R) x + x ^ 2 / R := by
    by_cases hx : x ∈ E
    · rw [indicator_of_mem hx]
      have hYle : Y x ≤ R := (le_abs_self _).trans ((habs x).trans_le hx.2)
      have : max (Y x) 0 ≤ R := max_le hYle hR.le
      linarith [div_nonneg (sq_nonneg x) hR.le]
    · rw [indicator_of_notMem hx]
      by_cases hYδ : Y x ≤ δ
      · have : max (Y x) 0 ≤ δ := max_le hYδ hδ.le
        linarith [div_nonneg (sq_nonneg x) hR.le]
      · have hxR : R ≤ |x| := by
          by_contra h
          exact hx ⟨(lt_of_not_ge hYδ).le, (lt_of_not_ge h).le⟩
        have hsq : |x| ≤ x ^ 2 / R := by
          rw [le_div_iff₀ hR]
          nlinarith [sq_abs x, abs_nonneg x]
        have : max (Y x) 0 ≤ |x| := max_le
          ((le_abs_self _).trans_eq (habs x)) (abs_nonneg x)
        linarith
  have hiP : Integrable (fun x => max (Y x) 0) μ := hiY.sup (integrable_const 0)
  have hiI : Integrable (E.indicator (fun _ : ℝ => R)) μ :=
    (integrable_const R).indicator hE
  have hb := integral_mono hiP (((integrable_const δ).add hiI).add (hi2.div_const R)) hpt
  change (∫ x, max (Y x) 0 ∂μ) ≤
    ∫ x, (δ + E.indicator (fun _ => R) x) + x ^ 2 / R ∂μ at hb
  have hiD : Integrable (fun x => δ + E.indicator (fun _ : ℝ => R) x) μ :=
    (integrable_const δ).add hiI
  rw [integral_add hiD (hi2.div_const R)] at hb
  have hadd := integral_add (integrable_const δ (μ := μ)) hiI
  rw [hadd, integral_const, integral_indicator_const R hE, integral_div, hsecond] at hb
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] at hb
  have hb' : p ≤ δ + (2 * R * d) * R + 1 / R :=
    hp.trans (hb.trans (by nlinarith [mul_le_mul_of_nonneg_right hmassR hR.le]))
  exact (not_le_of_gt hgap) hb'

/-- A positive lower bound at two points of a log-concave density holds
on the entire closed interval between them, for the actual representative. -/
theorem density_lower_on_interval {f : ℝ → ℝ}
    (hlog : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    {l r d x : ℝ} (hd : 0 < d) (hl : d ≤ f l) (hr : d ≤ f r)
    (hx : x ∈ Icc l r) : d ≤ f x := by
  have hlp : 0 < f l := hd.trans_le hl
  have hrp : 0 < f r := hd.trans_le hr
  have hseg : x ∈ segment ℝ l r := by
    rw [segment_eq_Icc (hx.1.trans hx.2)]
    exact hx
  have hxp : 0 < f x := hlog.1.segment_subset hlp hrp hseg
  have hlogs := hlog.ge_on_segment hlp hrp hseg
  have hmin : Real.log d ≤ min (Real.log (f l)) (Real.log (f r)) :=
    le_min (Real.log_le_log hd hl) (Real.log_le_log hd hr)
  exact (Real.log_le_log_iff hd hxp).mp (hmin.trans hlogs)

/-- Variance-one case of the central-density clause of one-dimensional log-concavity estimates. The constant is universal, and the
bound holds at every point of the indicated closed interval. -/
theorem exists_normalized_central_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) →
      ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) →
      (∫⁻ x, ENNReal.ofReal (f x)) = 1 →
      let μ := volume.withDensity (fun x => ENNReal.ofReal (f x))
      (∫ x : ℝ, x ∂μ) = 0 → (∫⁻ x : ℝ, ENNReal.ofReal (x ^ 2) ∂μ) = 1 →
      ∀ x : ℝ, |x| ≤ c → c ≤ f x := by
  obtain ⟨M, hM, hbound⟩ := exists_uniform_fourth_moment
  let T := M + 1
  let R := 16 * T
  let δ := 1 / R
  let d := δ / (4 * R ^ 2)
  have hT : 0 < T := by dsimp [T]; linarith
  have hR : 0 < R := by dsimp [R]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  refine ⟨min δ d, lt_min hδ hd, fun f hf hnn hlog hmass => ?_⟩
  dsimp only
  let μ := volume.withDensity (fun x => ENNReal.ofReal (f x))
  intro hmean hvar
  change (∫ x : ℝ, x ∂μ) = 0 at hmean
  have : IsProbabilityMeasure μ := ⟨by
    simpa only [μ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hmass⟩
  have hi2 : Integrable (fun x : ℝ => x ^ 2) μ := by
    refine ⟨(measurable_id.pow_const 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all μ fun x => sq_nonneg x)).mpr ?_⟩
    rw [hvar]
    exact ENNReal.one_lt_top
  have hsecond : (∫ x : ℝ, x ^ 2 ∂μ) = 1 := by
    have he := ofReal_integral_eq_lintegral_ofReal hi2 (ae_of_all μ fun x => sq_nonneg x)
    rw [hvar] at he
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun x => sq_nonneg x)
      (by norm_num)).mp (by simpa using he)
  obtain ⟨hfour, hfour_le⟩ := hbound f hf hnn hlog μ inferInstance rfl hi2 hsecond
  have hi1 : Integrable (fun x : ℝ => x) μ :=
    ((memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr hi2).integrable
      (by norm_num)
  have hfirst := first_abs_moment_lower μ hM hfour hsecond hfour_le
  have hδeq : 8 * δ = 1 / (2 * (M + 1)) := by
    dsimp [δ, R, T]
    field_simp
    ring
  have hpos : 4 * δ ≤ ∫ x : ℝ, max x 0 ∂μ := by
    have he := integral_abs_eq_two_mul_integral_posPart_sub_integral hi1
    simp only [PosPart.posPart] at he
    change (∫ x : ℝ, |x| ∂μ) = 2 * (∫ x : ℝ, max x 0 ∂μ) - ∫ x : ℝ, x ∂μ at he
    rw [hmean] at he
    rw [← hδeq] at hfirst
    linarith
  have hneg : 4 * δ ≤ ∫ x : ℝ, max (-x) 0 ∂μ := by
    have he := integral_abs_eq_two_mul_integral_negPart_add_integral hi1
    simp only [NegPart.negPart] at he
    change (∫ x : ℝ, |x| ∂μ) = 2 * (∫ x : ℝ, max (-x) 0 ∂μ) + ∫ x : ℝ, x ∂μ at he
    rw [hmean] at he
    rw [← hδeq] at hfirst
    linarith
  have hdR : (2 * R * d) * R = δ / 2 := by
    dsimp [d]
    field_simp
    ring
  have hgap : δ + (2 * R * d) * R + 1 / R < 4 * δ := by
    rw [hdR]
    change δ + δ / 2 + δ < 4 * δ
    linarith
  obtain ⟨r, hr, _, hfr⟩ := exists_density_point_internal μ rfl
    measurable_id hi1 (fun _ => rfl) hi2 hsecond hδ hR hd hpos hgap
  obtain ⟨l, hl, _, hfl⟩ := exists_density_point_internal μ rfl
    measurable_neg hi1.neg (fun x => abs_neg x) hi2 hsecond hδ hR hd hneg hgap
  change δ ≤ r at hr
  intro x hx
  apply (min_le_right δ d).trans
  apply density_lower_on_interval hlog hd hfl hfr
  have hxδ : |x| ≤ δ := hx.trans (min_le_left δ d)
  have hx' := abs_le.mp hxδ
  exact ⟨by linarith, by linarith⟩

/-- The canonical affine pullback density, including its Jacobian.
The formula is pointwise on the whole line, including zeros of `f`. -/
theorem map_standardize_density {f : ℝ → ℝ} (hf : Measurable f)
    (a : ℝ) {b : ℝ} (hb : 0 < b) :
    (volume.withDensity (fun x => ENNReal.ofReal (f x))).map (fun x => (x - a) / b) =
      volume.withDensity (fun x => ENNReal.ofReal (b * f (a + b * x))) := by
  let F := fun x : ℝ => (x - a) / b
  have hF : Measurable F := by dsimp [F]; fun_prop
  have hmap : (volume : Measure ℝ).map F = ENNReal.ofReal b • volume := by
    have he : F = (fun x : ℝ => b⁻¹ * x) ∘ (fun x => x + -a) := by
      ext x
      dsimp [F]
      ring
    rw [he, ← Measure.map_map (by fun_prop) (by fun_prop), map_add_right_eq_self,
      Real.map_volume_mul_left (inv_ne_zero hb.ne'), inv_inv, abs_of_pos hb]
  have hcomp : (fun x => ENNReal.ofReal (f x)) =
      (fun z => ENNReal.ofReal (f (a + b * z))) ∘ F := by
    ext x
    congr 2
    dsimp [F]
    field_simp
    ring
  have hmf : Measurable (fun z : ℝ => ENNReal.ofReal (f (a + b * z))) :=
    (hf.comp (by fun_prop)).ennreal_ofReal
  change (volume.withDensity (fun x => ENNReal.ofReal (f x))).map F = _
  rw [hcomp]
  change (volume.withDensity (fun x => ENNReal.ofReal (f (a + b * F x)))).map F = _
  rw [Riesz1.map_withDensity_comp volume hF hmf, hmap, withDensity_smul_measure]
  have he : (fun x => ENNReal.ofReal (b * f (a + b * x))) =
      ENNReal.ofReal b • (fun x => ENNReal.ofReal (f (a + b * x))) := by
    ext x
    exact ENNReal.ofReal_mul hb.le
  rw [he, withDensity_smul _ hmf]

/-- Log-concavity of the canonical affine pullback density, with no
choice of a density representative. -/
theorem concaveOn_log_standardize {f : ℝ → ℝ}
    (hlog : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ConcaveOn ℝ {x | 0 < b * f (a + b * x)}
      (fun x => Real.log (b * f (a + b * x))) := by
  let A : ℝ →ᵃ[ℝ] ℝ :=
    { toFun := fun x => a + b * x
      linear := b • LinearMap.id
      map_vadd' := by intro x y; simp [smul_eq_mul]; ring }
  have hpos : {x | 0 < b * f (a + b * x)} = A ⁻¹' {x | 0 < f x} := by
    ext x
    exact mul_pos_iff_of_pos_left hb
  rw [hpos]
  apply ((hlog.comp_affineMap A).add_const (Real.log b)).congr
  intro x hx
  change Real.log (f (A x)) + Real.log b = Real.log (b * f (A x))
  rw [Real.log_mul hb.ne' (ne_of_gt hx)]
  ring

/-- Central-density clause of one-dimensional log-concavity estimates,
under the stated density, mean and extended-variance hypotheses. The universal constant precedes the density. -/
theorem exists_central_density_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ f : ℝ → ℝ,
      Measurable f → (∀ x, 0 ≤ f x) →
      ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) →
      (∫⁻ x, ENNReal.ofReal (f x)) = 1 →
      let μ := volume.withDensity (fun x => ENNReal.ofReal (f x))
      ∀ a v : ℝ, Integrable (fun x => x) μ → (∫ x, x ∂μ) = a → 0 < v →
        (∫⁻ x, ENNReal.ofReal ((x - a) ^ 2) ∂μ) = ENNReal.ofReal v →
        ∀ x, |x - a| ≤ c * Real.sqrt v → c / Real.sqrt v ≤ f x := by
  obtain ⟨c, hc, hcentral⟩ := exists_normalized_central_lower
  refine ⟨c, hc, fun f hf hnn hlog hmass => ?_⟩
  dsimp only
  let μ := volume.withDensity (fun x => ENNReal.ofReal (f x))
  intro a v hi hmean hv hvar
  have : IsProbabilityMeasure μ := ⟨by
    simpa only [μ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hmass⟩
  let b := Real.sqrt v
  have hb : 0 < b := Real.sqrt_pos.mpr hv
  have hb2 : b ^ 2 = v := Real.sq_sqrt hv.le
  let g := fun x : ℝ => b * f (a + b * x)
  let ν := volume.withDensity (fun x => ENNReal.ofReal (g x))
  have hgm : Measurable g := by dsimp [g]; fun_prop
  have hgnn : ∀ x, 0 ≤ g x := fun x => mul_nonneg hb.le (hnn _)
  have hgl : ConcaveOn ℝ {x | 0 < g x} (fun x => Real.log (g x)) :=
    concaveOn_log_standardize hlog a hb
  have hν : ν = μ.map (fun x => (x - a) / b) := (map_standardize_density hf a hb).symm
  have : IsProbabilityMeasure ν := by
    rw [hν]
    exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance
  have hgmass : (∫⁻ x, ENNReal.ofReal (g x)) = 1 := by
    have hm := measure_univ (μ := ν)
    simpa only [ν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hm
  have hgmean : (∫ x : ℝ, x ∂ν) = 0 := by
    rw [hν, integral_map (μ := μ) (φ := fun x : ℝ => (x - a) / b)
      (f := fun x : ℝ => x) (by fun_prop) (by fun_prop),
      integral_div, integral_sub hi (integrable_const a)]
    change ((∫ x : ℝ, x ∂μ) - _) / b = 0
    change (∫ x : ℝ, x ∂μ) = a at hmean
    rw [hmean]
    simp
  have hgvar : (∫⁻ x : ℝ, ENNReal.ofReal (x ^ 2) ∂ν) = 1 := by
    rw [hν, lintegral_map (by fun_prop) (by fun_prop)]
    have hpt (x : ℝ) : ENNReal.ofReal (((x - a) / b) ^ 2) =
        ENNReal.ofReal ((x - a) ^ 2) / ENNReal.ofReal v := by
      rw [div_pow, hb2, ENNReal.ofReal_div_of_pos hv]
    simp_rw [hpt]
    simp_rw [div_eq_mul_inv]
    rw [lintegral_mul_const _ (by fun_prop), hvar]
    change ENNReal.ofReal v / ENNReal.ofReal v = 1
    exact ENNReal.div_self (ne_of_gt (ENNReal.ofReal_pos.mpr hv)) ENNReal.ofReal_ne_top
  have hlow := hcentral g hgm hgnn hgl hgmass hgmean hgvar
  intro x hx
  have hxc : |(x - a) / b| ≤ c := by
    rw [abs_div, abs_of_pos hb, div_le_iff₀ hb]
    exact hx
  have he : a + b * ((x - a) / b) = x := by field_simp; ring
  have h := hlow ((x - a) / b) hxc
  change c ≤ b * f (a + b * ((x - a) / b)) at h
  rw [he] at h
  exact (div_le_iff₀ hb).mpr (by simpa only [mul_comm] using h)

end Riesz2.LogConcaveCentralDensity
