/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.TotalVariation
public import Riesz1.ToMathlib.TotalVariation.Density
public import Riesz1.ToMathlib.TotalVariation.Event
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Tactic

/-!
# Tilts by nonnegative penalties on a probability space

For a probability measure `μ`, a measurable penalty `G ≥ 0` and a parameter `b ≥ 0`, the tilt
`expTilt μ b G` has density `e^{-bG} / Z` with respect to `μ`, where `Z = ∫ e^{-bG} dμ`. The
normalizer is an extended integral, as in the tilted particle law. The file proves:

* the tilt is a probability measure, with the density formula and a bound on lower integrals.
* the total variation distance to `μ` is at most the mass of `{G ≠ 0}`.
* for a `L²` observable `f`, the change of its mean is controlled by `√q + q` times its `L²`
  norm, where `q` bounds the mass of `{G ≠ 0}`.
* the normalizer is at least `exp(-b ∫ G dμ)` when `G` is integrable.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal

namespace Riesz2.NonnegativeTilt

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The real normalizer `Z = ∫ e^{-bG} dμ` of the tilt by the penalty `G`. -/
@[expose] noncomputable def expTiltNormalizer (μ : Measure Ω) (b : ℝ) (G : Ω → ℝ) : ℝ :=
  ∫ ω, Real.exp (-b * G ω) ∂μ

/-- The tilt of `μ` by `e^{-bG}`, normalized in the extended sense as in the tilted
particle law: the inverse of the extended normalizer times the weighted measure. -/
@[expose] noncomputable def expTilt (μ : Measure Ω) (b : ℝ) (G : Ω → ℝ) : Measure Ω :=
  (∫⁻ ω, ENNReal.ofReal (Real.exp (-b * G ω)) ∂μ)⁻¹ •
    μ.withDensity (fun ω => ENNReal.ofReal (Real.exp (-b * G ω)))

section Basic

variable {μ : Measure Ω} {b : ℝ} {G : Ω → ℝ}

theorem measurable_exp_neg_mul (hG : Measurable G) :
    Measurable (fun ω => Real.exp (-b * G ω)) :=
  (hG.const_mul (-b)).exp

omit [MeasurableSpace Ω] in
theorem exp_neg_mul_le_one (hb : 0 ≤ b) (hG0 : ∀ ω, 0 ≤ G ω) (ω : Ω) :
    Real.exp (-b * G ω) ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  rw [neg_mul]
  exact neg_nonpos.mpr (mul_nonneg hb (hG0 ω))

theorem integrable_exp_neg_mul [IsFiniteMeasure μ] (hG : Measurable G) (hb : 0 ≤ b)
    (hG0 : ∀ ω, 0 ≤ G ω) : Integrable (fun ω => Real.exp (-b * G ω)) μ :=
  (integrable_const (1 : ℝ)).mono' (measurable_exp_neg_mul hG).aestronglyMeasurable
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact exp_neg_mul_le_one hb hG0 ω)

theorem expTiltNormalizer_le_one [IsProbabilityMeasure μ] (hG : Measurable G) (hb : 0 ≤ b)
    (hG0 : ∀ ω, 0 ≤ G ω) : expTiltNormalizer μ b G ≤ 1 := by
  unfold expTiltNormalizer
  have h := integral_mono (integrable_exp_neg_mul (μ := μ) hG hb hG0)
    (integrable_const (1 : ℝ)) (fun ω => exp_neg_mul_le_one hb hG0 ω)
  simpa using h

theorem expTiltNormalizer_pos [IsProbabilityMeasure μ] (hG : Measurable G) (hb : 0 ≤ b)
    (hG0 : ∀ ω, 0 ≤ G ω) : 0 < expTiltNormalizer μ b G :=
  integral_exp_pos (integrable_exp_neg_mul hG hb hG0)

theorem lintegral_normalizer_eq (hG : Measurable G) (hb : 0 ≤ b) (hG0 : ∀ ω, 0 ≤ G ω)
    [IsFiniteMeasure μ] :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-b * G ω)) ∂μ =
      ENNReal.ofReal (expTiltNormalizer μ b G) :=
  (ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_mul hG hb hG0)
    (ae_of_all _ fun _ => (Real.exp_pos _).le)).symm

/-- The tilt is a probability measure whenever `μ` is one, `b ≥ 0` and `G ≥ 0` is
measurable. -/
theorem expTilt_isProbabilityMeasure [IsProbabilityMeasure μ] (hG : Measurable G) (hb : 0 ≤ b)
    (hG0 : ∀ ω, 0 ≤ G ω) : IsProbabilityMeasure (expTilt μ b G) := by
  constructor
  have hpos := expTiltNormalizer_pos (μ := μ) hG hb hG0
  have hle := expTiltNormalizer_le_one (μ := μ) hG hb hG0
  have hl : 0 < ∫⁻ ω, ENNReal.ofReal (Real.exp (-b * G ω)) ∂μ := by
    rw [lintegral_normalizer_eq hG hb hG0]
    exact ENNReal.ofReal_pos.mpr hpos
  have hfin : ∫⁻ ω, ENNReal.ofReal (Real.exp (-b * G ω)) ∂μ ≠ ⊤ := by
    rw [lintegral_normalizer_eq hG hb hG0]
    exact ENNReal.ofReal_ne_top
  rw [expTilt, Measure.smul_apply, smul_eq_mul, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  exact ENNReal.inv_mul_cancel hl.ne' hfin

/-- The tilt has the density `Z⁻¹ e^{-bG}` with respect to `μ`. -/
theorem expTilt_eq_withDensity [IsProbabilityMeasure μ] (hG : Measurable G) (hb : 0 ≤ b)
    (hG0 : ∀ ω, 0 ≤ G ω) :
    expTilt μ b G = μ.withDensity (fun ω => ENNReal.ofReal
      ((expTiltNormalizer μ b G)⁻¹ * Real.exp (-b * G ω))) := by
  have hpos := expTiltNormalizer_pos (μ := μ) hG hb hG0
  have hm := (measurable_exp_neg_mul (b := b) hG).ennreal_ofReal
  unfold expTilt
  rw [lintegral_normalizer_eq hG hb hG0, ← withDensity_smul _ hm]
  congr 1
  funext ω
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr hpos.le), ENNReal.ofReal_inv_of_pos hpos]

/-- The integral against the tilt is the normalized weighted integral. -/
theorem integral_expTilt (hG : Measurable G) (hb : 0 ≤ b) (hG0 : ∀ ω, 0 ≤ G ω)
    [IsProbabilityMeasure μ] (f : Ω → ℝ) :
    ∫ ω, f ω ∂(expTilt μ b G) =
      (expTiltNormalizer μ b G)⁻¹ * ∫ ω, Real.exp (-b * G ω) * f ω ∂μ := by
  have hpos := expTiltNormalizer_pos (μ := μ) hG hb hG0
  have hm : Measurable (fun ω => ENNReal.ofReal
      ((expTiltNormalizer μ b G)⁻¹ * Real.exp (-b * G ω))) :=
    ((measurable_exp_neg_mul hG).const_mul _).ennreal_ofReal
  rw [expTilt_eq_withDensity hG hb hG0,
    integral_withDensity_eq_integral_toReal_smul hm
      (ae_of_all _ fun ω => ENNReal.ofReal_lt_top) f, ← integral_const_mul]
  congr 1
  funext ω
  rw [ENNReal.toReal_ofReal (mul_nonneg (inv_nonneg.mpr hpos.le)
    (Real.exp_pos _).le), smul_eq_mul]
  ring

/-- The extended-valued integral against the tilt is at most the inverse normalizer times the
integral against `μ`. -/
theorem lintegral_expTilt_le (hG : Measurable G) (hb : 0 ≤ b) (hG0 : ∀ ω, 0 ≤ G ω)
    [IsFiniteMeasure μ] {g : Ω → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, g ω ∂(expTilt μ b G) ≤
      (∫⁻ ω, ENNReal.ofReal (Real.exp (-b * G ω)) ∂μ)⁻¹ * ∫⁻ ω, g ω ∂μ := by
  have hm := (measurable_exp_neg_mul (b := b) hG).ennreal_ofReal
  unfold expTilt
  rw [lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul μ hm hg, smul_eq_mul]
  refine mul_le_mul_of_nonneg_left (lintegral_mono fun ω => ?_) zero_le
  simp only [Pi.mul_apply]
  calc
    ENNReal.ofReal (Real.exp (-b * G ω)) * g ω ≤ 1 * g ω :=
      mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_one.mpr (exp_neg_mul_le_one hb hG0 ω))
        zero_le
    _ = g ω := one_mul _

end Basic

section Total

variable {μ : Measure Ω} {b : ℝ} {G : Ω → ℝ}

/-- Event supremum of a difference of two probability measures, through the half-variation
estimate of the companion library. -/
private theorem event_discrepancy_eq' (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (A : Set Ω) :
    (μ A - ν A) + (ν A - μ A) = ENNReal.ofReal |μ.real A - ν.real A| := by
  simp only [Measure.real]
  rcases le_total (μ A) (ν A) with h | h
  · rw [tsub_eq_zero_of_le h, zero_add, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr (ENNReal.toReal_mono (measure_ne_top ν A) h))]
    exact (ENNReal.ofReal_toReal ((lt_of_le_of_lt tsub_le_self (measure_lt_top ν A)).ne)).symm.trans
      (congrArg ENNReal.ofReal (ENNReal.toReal_sub_of_le h (measure_ne_top ν A)))
  · rw [tsub_eq_zero_of_le h, add_zero,
      abs_of_nonneg (sub_nonneg.mpr (ENNReal.toReal_mono (measure_ne_top μ A) h))]
    exact (ENNReal.ofReal_toReal ((lt_of_le_of_lt tsub_le_self (measure_lt_top μ A)).ne)).symm.trans
      (congrArg ENNReal.ofReal (ENNReal.toReal_sub_of_le h (measure_ne_top μ A)))

/-- The total variation of two probability measures is at most `b` once the half event
distance is at most `b`. -/
private theorem totalVariation_le_of_half_etvDist_le' (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {b : ℝ} (hb : (etvDist μ ν).toReal / 2 ≤ b) :
    Riesz2.totalVariation μ ν ≤ ENNReal.ofReal b := by
  apply iSup_le
  intro A
  rw [event_discrepancy_eq']
  exact ENNReal.ofReal_le_ofReal
    ((Riesz1.abs_measureReal_sub_le_etvDist_div_two μ ν A.property).trans hb)

/-- The total variation distance between `μ` and its tilt is at most the mass of `{G ≠ 0}`. -/
theorem totalVariation_expTilt_le [IsProbabilityMeasure μ] (hG : Measurable G) (hb : 0 ≤ b)
    (hG0 : ∀ ω, 0 ≤ G ω) :
    letI := expTilt_isProbabilityMeasure (μ := μ) hG hb hG0
    Riesz2.totalVariation μ (expTilt μ b G) ≤
      ENNReal.ofReal (μ.real {ω | G ω ≠ 0}) := by
  have := expTilt_isProbabilityMeasure (μ := μ) hG hb hG0
  have hpos := expTiltNormalizer_pos (μ := μ) hG hb hG0
  have hle := expTiltNormalizer_le_one (μ := μ) hG hb hG0
  have hg : Measurable (fun ω => (expTiltNormalizer μ b G)⁻¹ * Real.exp (-b * G ω)) :=
    (measurable_exp_neg_mul hG).const_mul _
  have hg1 : ∫ ω, (expTiltNormalizer μ b G)⁻¹ * Real.exp (-b * G ω) ∂μ = 1 := by
    rw [integral_const_mul]
    exact inv_mul_cancel₀ hpos.ne'
  have hE : MeasurableSet {ω | G ω = 0} := measurableSet_eq_fun hG measurable_const
  have he := Riesz1.half_etvDist_le_measure_compl_of_one_le_on μ (expTilt μ b G) hg
    (fun ω => mul_nonneg (inv_nonneg.mpr hpos.le) (Real.exp_pos _).le) hg1 hE
    (fun ω hω => by
      change G ω = 0 at hω
      simp only [hω, mul_zero, Real.exp_zero, mul_one]
      exact (one_le_inv₀ hpos).mpr hle)
    (expTilt_eq_withDensity hG hb hG0)
  have hcompl : {ω | G ω = 0}ᶜ = {ω | G ω ≠ 0} := by ext ω; simp
  rw [hcompl] at he
  exact totalVariation_le_of_half_etvDist_le' μ _ he

/-- Total variation is monotone under a measurable map, since image events are preimages. -/
theorem totalVariation_map_le {Ω' : Type*} [MeasurableSpace Ω'] (μ ν : Measure Ω)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (φ : Ω → Ω') (hφ : Measurable φ) :
    Riesz2.totalVariation (μ.map φ) (ν.map φ) ≤ Riesz2.totalVariation μ ν := by
  apply iSup_le
  intro A
  rw [Measure.map_apply hφ A.property, Measure.map_apply hφ A.property]
  exact le_iSup (fun B : {B : Set Ω // MeasurableSet B} =>
    (μ B.val - ν B.val) + (ν B.val - μ B.val)) ⟨φ ⁻¹' A.val, hφ A.property⟩

end Total

section Perturbation

variable {μ : Measure Ω} {b : ℝ} {G : Ω → ℝ}

/-- For a probability measure, the mean of an `L²` function is at most its `L²` norm. -/
theorem abs_integral_le_sqrt_integral_sq [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : MemLp f 2 μ) : |∫ ω, f ω ∂μ| ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂μ) := by
  apply Real.abs_le_sqrt
  have hv := ProbabilityTheory.variance_nonneg f μ
  rw [ProbabilityTheory.variance_eq_sub hf] at hv
  simp only [Pi.pow_apply] at hv
  linarith

/-- The normalizer loses at most the mass of `{G ≠ 0}`: `1 - Z ≤ μ{G ≠ 0}`. -/
theorem one_sub_expTiltNormalizer_le [IsProbabilityMeasure μ] (hG : Measurable G) (hb : 0 ≤ b)
    (hG0 : ∀ ω, 0 ≤ G ω) : 1 - expTiltNormalizer μ b G ≤ μ.real {ω | G ω ≠ 0} := by
  have he_int : Integrable (fun ω => Real.exp (-b * G ω)) μ :=
    integrable_exp_neg_mul hG hb hG0
  have hone_sub : 1 - expTiltNormalizer μ b G = ∫ ω, (1 - Real.exp (-b * G ω)) ∂μ := by
    rw [integral_sub (integrable_const (1 : ℝ)) he_int, integral_const]
    simp [expTiltNormalizer]
  have hS : MeasurableSet {ω | G ω ≠ 0} := (measurableSet_eq_fun hG measurable_const).compl
  rw [hone_sub]
  have h := integral_mono ((integrable_const (1 : ℝ)).sub he_int)
    ((integrable_const (1 : ℝ)).indicator hS) (fun ω => by
      simp only [Pi.sub_apply]
      by_cases hω : ω ∈ {ω | G ω ≠ 0}
      · rw [Set.indicator_of_mem hω]
        have := Real.exp_pos (-b * G ω)
        linarith
      · rw [Set.indicator_of_notMem hω]
        have hG0' : G ω = 0 := by
          by_contra h'
          exact hω h'
        simp [hG0'])
  rw [integral_indicator_const _ hS, smul_eq_mul, mul_one] at h
  exact h

/-- Jensen's inequality for the normalizer: `exp(-b ∫ G dμ) ≤ Z`, for an integrable penalty. -/
theorem exp_neg_mul_integral_le_expTiltNormalizer [IsProbabilityMeasure μ] (hG : Measurable G)
    (hb : 0 ≤ b) (hG0 : ∀ ω, 0 ≤ G ω) (hGi : Integrable G μ) :
    Real.exp (-b * ∫ ω, G ω ∂μ) ≤ expTiltNormalizer μ b G := by
  set m := ∫ ω, G ω ∂μ with hm_def
  have hpt : ∀ ω, Real.exp (-b * m) * (1 - b * (G ω - m)) ≤ Real.exp (-b * G ω) := by
    intro ω
    have h1 := Real.add_one_le_exp (-b * (G ω - m))
    have h2 : Real.exp (-b * G ω) = Real.exp (-b * m) * Real.exp (-b * (G ω - m)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [h2]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    linarith
  have hGm : Integrable (fun ω => G ω - m) μ := hGi.sub (integrable_const m)
  have hl : Integrable (fun ω => Real.exp (-b * m) * (1 - b * (G ω - m))) μ :=
    ((integrable_const (1 : ℝ)).sub (hGm.const_mul b)).const_mul _
  have hint : ∫ ω, Real.exp (-b * m) * (1 - b * (G ω - m)) ∂μ = Real.exp (-b * m) := by
    rw [integral_const_mul]
    have h1 : ∫ ω, (1 - b * (G ω - m)) ∂μ = 1 := by
      rw [integral_sub (integrable_const (1 : ℝ)) (hGm.const_mul b), integral_const,
        integral_const_mul, integral_sub hGi (integrable_const m), integral_const, hm_def]
      simp
    rw [h1, mul_one]
  have hr : Integrable (fun ω => Real.exp (-b * G ω)) μ :=
    integrable_exp_neg_mul hG hb hG0
  have h := integral_mono hl hr hpt
  rw [hint] at h
  exact h

/-- The mean of an `L²` observable changes under the tilt by at most `(√q + q)` times the
inverse normalizer times its `L²` norm, when the mass of `{G ≠ 0}` is at most `q`. -/
theorem abs_integral_expTilt_sub_le [IsProbabilityMeasure μ] (hG : Measurable G) (hb : 0 ≤ b)
    (hG0 : ∀ ω, 0 ≤ G ω) {f : Ω → ℝ} (hf : MemLp f 2 μ) {q : ℝ}
    (hq : μ.real {ω | G ω ≠ 0} ≤ q) :
    |∫ ω, f ω ∂(expTilt μ b G) - ∫ ω, f ω ∂μ| ≤
      (expTiltNormalizer μ b G)⁻¹ * (Real.sqrt q + q) * Real.sqrt (∫ ω, f ω ^ 2 ∂μ) := by
  have hpos : 0 < expTiltNormalizer μ b G := expTiltNormalizer_pos (μ := μ) hG hb hG0
  have hle : expTiltNormalizer μ b G ≤ 1 := expTiltNormalizer_le_one (μ := μ) hG hb hG0
  have hz_eq : expTiltNormalizer μ b G = ∫ ω, Real.exp (-b * G ω) ∂μ := rfl
  set z := expTiltNormalizer μ b G with hz_def
  set F := ∫ ω, f ω ^ 2 ∂μ with hF_def
  set M := ∫ ω, f ω ∂μ with hM_def
  set S : Set Ω := {ω | G ω ≠ 0} with hS_def
  have hS : MeasurableSet S := (measurableSet_eq_fun hG measurable_const).compl
  have hq0 : 0 ≤ q := (measureReal_nonneg).trans hq
  have hf1 : Integrable f μ := hf.integrable one_le_two
  have he_int : Integrable (fun ω => Real.exp (-b * G ω)) μ :=
    integrable_exp_neg_mul hG hb hG0
  have hbdd : ∀ ω, |Real.exp (-b * G ω) - 1| ≤ 1 := by
    intro ω
    have h1 := exp_neg_mul_le_one hb hG0 ω
    have h2 : 0 < Real.exp (-b * G ω) := Real.exp_pos _
    rw [abs_le]
    constructor <;> linarith
  have hef : Integrable (fun ω => (Real.exp (-b * G ω) - 1) * f ω) μ :=
    hf1.bdd_mul (c := 1)
      ((measurable_exp_neg_mul hG).sub measurable_const).aestronglyMeasurable
      (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hbdd ω)
  -- Pointwise domination of `|(e - 1) f|` by the restriction of `|f|` to `S`.
  have hdom : ∀ ω, |(Real.exp (-b * G ω) - 1) * f ω| ≤ S.indicator (fun ω => |f ω|) ω := by
    intro ω
    by_cases hω : G ω = 0
    · have hnot : ω ∉ S := fun h => h hω
      simp only [Set.indicator_of_notMem hnot, hω, mul_zero, Real.exp_zero, sub_self,
        zero_mul, abs_zero, le_refl]
    · have hmem : ω ∈ S := hω
      rw [Set.indicator_of_mem hmem, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (hbdd ω)
  -- Cauchy–Schwarz for the restriction of `|f|` to `S`.
  have hCS : ∫ ω, S.indicator (fun ω => |f ω|) ω ∂μ ≤ Real.sqrt (μ.real S) * Real.sqrt F := by
    have hmem1 : MemLp (S.indicator (fun _ : Ω => (1 : ℝ))) (ENNReal.ofReal 2) μ := by
      rw [ENNReal.ofReal_ofNat]
      exact MemLp.indicator hS.nullMeasurableSet (memLp_const (1 : ℝ))
    have hmem2 : MemLp (fun ω => |f ω|) (ENNReal.ofReal 2) μ := by
      rw [ENNReal.ofReal_ofNat]
      exact hf.abs
    have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2)
      Real.HolderConjugate.two_two
      (f := S.indicator (fun _ : Ω => (1 : ℝ))) (g := fun ω => |f ω|)
      (ae_of_all _ fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
      (ae_of_all _ fun ω => abs_nonneg _) hmem1 hmem2
    have hone : ∫ ω, (S.indicator (fun _ : Ω => (1 : ℝ)) ω) ^ (2 : ℝ) ∂μ = μ.real S := by
      have : (fun ω => (S.indicator (fun _ : Ω => (1 : ℝ)) ω) ^ (2 : ℝ)) =
          S.indicator (fun _ : Ω => (1 : ℝ)) := by
        funext ω
        by_cases hω : ω ∈ S <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hω]
      rw [this, integral_indicator_const _ hS, smul_eq_mul, mul_one]
    have hsq : ∫ ω, |f ω| ^ (2 : ℝ) ∂μ = F := by
      rw [hF_def]
      congr 1
      funext ω
      rw [Real.rpow_two, sq_abs]
    rw [hone, hsq] at hcs
    have hpow : ∀ x : ℝ, 0 ≤ x → x ^ (1 / (2 : ℝ)) = Real.sqrt x := fun x _ =>
      (Real.sqrt_eq_rpow x).symm
    rw [hpow _ measureReal_nonneg, hpow _ (integral_nonneg fun ω => sq_nonneg _)] at hcs
    have hint : ∫ ω, S.indicator (fun ω => |f ω|) ω ∂μ =
        ∫ ω, S.indicator (fun _ : Ω => (1 : ℝ)) ω * |f ω| ∂μ := by
      congr 1
      funext ω
      by_cases hω : ω ∈ S <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hω]
    rw [hint]
    exact hcs
  -- The `L¹` estimate of the error `∫ (e - 1) f`.
  have hA : |∫ ω, (Real.exp (-b * G ω) - 1) * f ω ∂μ| ≤ Real.sqrt q * Real.sqrt F := by
    calc
      |∫ ω, (Real.exp (-b * G ω) - 1) * f ω ∂μ|
          ≤ ∫ ω, |(Real.exp (-b * G ω) - 1) * f ω| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ ω, S.indicator (fun ω => |f ω|) ω ∂μ :=
          integral_mono hef.abs ((hf1.abs).indicator hS) hdom
      _ ≤ Real.sqrt (μ.real S) * Real.sqrt F := hCS
      _ ≤ Real.sqrt q * Real.sqrt F :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hq) (Real.sqrt_nonneg _)
  have hnn : 0 ≤ 1 - z := by linarith
  have hup : 1 - z ≤ μ.real S := one_sub_expTiltNormalizer_le hG hb hG0
  have hMbound : |M| ≤ Real.sqrt F := abs_integral_le_sqrt_integral_sq hf
  have hbound2 : |(1 - z) * M| ≤ q * Real.sqrt F := by
    rw [abs_mul, abs_of_nonneg hnn]
    exact mul_le_mul (by linarith) hMbound (abs_nonneg _) hq0
  -- The exact identity for the tilted mean.
  have hsplit : ∫ ω, Real.exp (-b * G ω) * f ω ∂μ =
      ∫ ω, (Real.exp (-b * G ω) - 1) * f ω ∂μ + M := by
    rw [hM_def, ← integral_add hef hf1]
    congr 1
    funext ω
    ring
  have hkey : ∫ ω, f ω ∂(expTilt μ b G) - M =
      z⁻¹ * (∫ ω, (Real.exp (-b * G ω) - 1) * f ω ∂μ + (1 - z) * M) := by
    rw [integral_expTilt hG hb hG0 f, hsplit]
    have hinv : z⁻¹ * z = 1 := inv_mul_cancel₀ hpos.ne'
    linear_combination M * hinv
  rw [hkey, abs_mul, abs_of_pos (inv_pos.mpr hpos)]
  have htri : |∫ ω, (Real.exp (-b * G ω) - 1) * f ω ∂μ + (1 - z) * M| ≤
      Real.sqrt q * Real.sqrt F + q * Real.sqrt F :=
    (abs_add_le _ _).trans (add_le_add hA hbound2)
  calc
    z⁻¹ * |∫ ω, (Real.exp (-b * G ω) - 1) * f ω ∂μ + (1 - z) * M|
        ≤ z⁻¹ * (Real.sqrt q * Real.sqrt F + q * Real.sqrt F) :=
          mul_le_mul_of_nonneg_left htri (inv_pos.mpr hpos).le
    _ = z⁻¹ * (Real.sqrt q + q) * Real.sqrt F := by ring

end Perturbation

end Riesz2.NonnegativeTilt
