/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.SingleGapTails
public import Riesz2.HelfferSjostrand.PhysicalEnergy
public import Riesz2.Sanity.TiltedLaws
public import Riesz2.Frozen.TotalVariation
public import Riesz1.ToMathlib.TotalVariation.Density
public import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Upper-gap tilts for the short-range local law

The arbitrary-set version of Appendix B is connected below to
the first-block penalty, normalizer and particle law. The comparison
lemmas prove the measure-theoretic clauses of the proof of Lemma B.1.
All normalizers are extended integrals, with positivity proved separately.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace Riesz2.DecayShort

/-- See Appendix B of the paper: the upper-gap penalty on an arbitrary finite set
of gap labels. Its arguments are actual positive microscopic gaps. -/
def upperGapPenalty {N : ℕ+} (θ : PhysicalCutoff) (R : {R : ℝ // 0 < R})
    (J : Finset (Fin (N : ℕ))) (X : Riesz1.Configuration N) : ℝ :=
  ∑ i ∈ J, θ.val (gap X i.val / R)

/-- See Appendix B of the paper: the extended normalizer of an arbitrary-set tilt. -/
def upperGapNormalizer (p : Parameters) (N : ℕ+) (θ : PhysicalCutoff)
    (R : {R : ℝ // 0 < R})
    (J : Finset (Fin (N : ℕ))) : ℝ≥0∞ :=
  ∫⁻ X, ENNReal.ofReal (Real.exp (-p.val.1 * upperGapPenalty θ R J X))
    ∂gibbsMeasure p N

/-- See Appendix B of the paper: the arbitrary-set tilted particle law, whose
gap image is the tilted gap law. Normalization is proved below for `R > 0`. -/
def upperTiltedParticleMeasure (p : Parameters) (N : ℕ+) (θ : PhysicalCutoff)
    (R : {R : ℝ // 0 < R})
    (J : Finset (Fin (N : ℕ))) : Measure (Riesz1.Configuration N) :=
  (upperGapNormalizer p N θ R J)⁻¹ • (gibbsMeasure p N).withDensity
    (fun X => ENNReal.ofReal (Real.exp (-p.val.1 * upperGapPenalty θ R J X)))

/-- Every penalty summand is nonnegative on its entire positive-scale carrier. -/
theorem upperGapPenalty_nonneg {N : ℕ+} (θ : PhysicalCutoff) (R : {R : ℝ // 0 < R})
    (J : Finset (Fin (N : ℕ))) (X : Riesz1.Configuration N) :
    0 ≤ upperGapPenalty θ R J X := by
  apply Finset.sum_nonneg
  intro i _
  exact θ.property.2.2.1 _ (div_nonneg (Riesz1.gap_pos X i.val).le R.property.le)

/-- Measurability uses the cutoff only on the nonnegative half-line. No
regularity outside its carrier is assumed. -/
theorem upperGapPenalty_measurable {N : ℕ+} (θ : PhysicalCutoff) (R : {R : ℝ // 0 < R})
    (J : Finset (Fin (N : ℕ))) :
    Measurable (upperGapPenalty (N := N) θ R J) := by
  have hθ : Continuous (fun t : Ici (0 : ℝ) => θ.val t.val) :=
    continuousOn_iff_continuous_domRestrict.mp θ.property.1.continuousOn
  apply Finset.measurable_sum
  intro i _
  let f : Riesz1.Configuration N → Ici (0 : ℝ) := fun X =>
    ⟨gap X i.val / R, div_nonneg (Riesz1.gap_pos X i.val).le R.property.le⟩
  have hf : Measurable f := ((Riesz1.measurable_gap i.val).div_const R).subtype_mk
  exact hθ.measurable.comp hf

/-- The penalty vanishes whenever each selected gap is at most `R / 2`.
This includes the empty set of labels. -/
theorem upperGapPenalty_eq_zero {N : ℕ+} (θ : PhysicalCutoff) (R : {R : ℝ // 0 < R})
    (J : Finset (Fin (N : ℕ))) (X : Riesz1.Configuration N)
    (h : ∀ i ∈ J, gap X i.val ≤ R / 2) : upperGapPenalty θ R J X = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  apply θ.property.2.2.2.1
  exact ⟨(div_pos (Riesz1.gap_pos X i.val) R.property).le,
    (div_le_iff₀ R.property).mpr (by simpa only [div_eq_mul_inv, mul_comm, one_mul] using h i hi)⟩

/-- See the proof of Lemma B.1 in the paper, first clause, with numerical
constants independent of exponent and temperature. The proof is a finite
union bound applied to the one-gap exponential moment. -/
theorem upperGapPenalty_event_bound (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) (R : {R : ℝ // 0 < R})
    (J : Finset (Fin (N : ℕ))) :
    (gibbsMeasure p N) {X | upperGapPenalty θ R J X ≠ 0} ≤
      ENNReal.ofReal (3 * J.card * Real.exp (-(Real.log 2 / 8) * R)) := by
  have := gibbsMeasure_probability p N
  have hd : 0 < Real.log 2 / 4 := div_pos (Real.log_pos one_lt_two) (by norm_num)
  have hsub : {X | upperGapPenalty θ R J X ≠ 0} ⊆
      ⋃ i ∈ J, {X : Riesz1.Configuration N | R / 2 ≤ gap X i.val} := by
    intro X hX
    by_contra h
    apply hX
    apply upperGapPenalty_eq_zero θ R J X
    intro i hi
    have : ¬ R / 2 ≤ gap X i.val := fun hle => h (mem_iUnion.mpr
      ⟨i, mem_iUnion.mpr ⟨hi, hle⟩⟩)
    exact (lt_of_not_ge this).le
  calc
    _ ≤ (gibbsMeasure p N) (⋃ i ∈ J, {X | R / 2 ≤ gap X i.val}) := measure_mono hsub
    _ ≤ ∑ i ∈ J, (gibbsMeasure p N) {X | R / 2 ≤ gap X i.val} :=
      measure_biUnion_finset_le J _
    _ ≤ ∑ _i ∈ J, ENNReal.ofReal (3 * Real.exp (-(Real.log 2 / 4) * (R / 2))) := by
      apply Finset.sum_le_sum
      intro i _
      have he := SingleGapTails.exponential_moment p N hN i.val
      exact ExponentialPower.closed_tail hd he.1 he.2 (R / 2)
    _ = ENNReal.ofReal (3 * J.card * Real.exp (-(Real.log 2 / 8) * R)) := by
      rw [Finset.sum_const, ← ENNReal.ofReal_nsmul]
      congr 1
      simp only [nsmul_eq_mul]
      have hh : -(Real.log 2 / 4) * (R / 2) = -(Real.log 2 / 8) * R := by ring
      rw [hh]
      ring

/-- The arbitrary-set normalizer is strictly positive and at most one,
without a large-scale assumption and including the empty tilt. -/
theorem upperGapNormalizer_valid (p : Parameters) (N : ℕ+) (θ : PhysicalCutoff)
    (R : {R : ℝ // 0 < R})
    (J : Finset (Fin (N : ℕ))) :
    0 < upperGapNormalizer p N θ R J ∧ upperGapNormalizer p N θ R J ≤ 1 := by
  have := gibbsMeasure_probability p N
  have hm := ((upperGapPenalty_measurable θ R J).const_mul (-p.val.1)).exp.ennreal_ofReal
  constructor
  · rw [upperGapNormalizer, lintegral_pos_iff_support hm]
    have hs : Function.support (fun X : Riesz1.Configuration N =>
        ENNReal.ofReal (Real.exp (-p.val.1 * upperGapPenalty θ R J X))) = univ := by
      ext X
      simp [Function.mem_support, Real.exp_pos]
    rw [hs]
    simp
  · calc
      _ ≤ ∫⁻ _ : Riesz1.Configuration N, (1 : ℝ≥0∞) ∂gibbsMeasure p N := by
        apply lintegral_mono
        intro X
        apply ENNReal.ofReal_le_one.mpr
        apply Real.exp_le_one_iff.mpr
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr p.property.1.le)
          (upperGapPenalty_nonneg θ R J X)
      _ = 1 := by simp

/-- Arbitrary upper-gap tilts are actual probabilities. -/
theorem upperTiltedParticleMeasure_probability (p : Parameters) (N : ℕ+)
    (θ : PhysicalCutoff) (R : {R : ℝ // 0 < R})
    (J : Finset (Fin (N : ℕ))) :
    IsProbabilityMeasure (upperTiltedParticleMeasure p N θ R J) := by
  have hz := upperGapNormalizer_valid p N θ R J
  constructor
  rw [upperTiltedParticleMeasure, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact ENNReal.inv_mul_cancel hz.1.ne' (hz.2.trans_lt ENNReal.one_lt_top).ne

/-- The Boltzmann weight is integrable, independently of the number of labels. -/
theorem integrable_upperGapWeight (p : Parameters) (N : ℕ+) (θ : PhysicalCutoff)
    (R : {R : ℝ // 0 < R})
    (J : Finset (Fin (N : ℕ))) :
    Integrable (fun X : Riesz1.Configuration N =>
      Real.exp (-p.val.1 * upperGapPenalty θ R J X)) (gibbsMeasure p N) := by
  have := gibbsMeasure_probability p N
  refine (integrable_const (1 : ℝ)).mono'
    (((upperGapPenalty_measurable θ R J).const_mul _).exp.aestronglyMeasurable) ?_
  apply ae_of_all
  intro X
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr p.property.1.le)
    (upperGapPenalty_nonneg θ R J X)

/-- The real integral equals the extended normalizer, with no nonintegrable
integral convention involved. -/
theorem upperGapNormalizer_eq_ofReal_integral (p : Parameters) (N : ℕ+)
    (θ : PhysicalCutoff) (R : {R : ℝ // 0 < R})
    (J : Finset (Fin (N : ℕ))) :
    upperGapNormalizer p N θ R J = ENNReal.ofReal
      (∫ X, Real.exp (-p.val.1 * upperGapPenalty θ R J X) ∂gibbsMeasure p N) := by
  exact (ofReal_integral_eq_lintegral_ofReal (integrable_upperGapWeight p N θ R J)
    (ae_of_all _ (fun _ => (Real.exp_pos _).le))).symm

/-- The normalizer loses at most the mass of the event where the penalty
is nonzero (the proof of Lemma B.1). -/
theorem upperGapNormalizer_lower (p : Parameters) (N : ℕ+) (θ : PhysicalCutoff)
    (R : {R : ℝ // 0 < R})
    (J : Finset (Fin (N : ℕ))) :
    1 - (gibbsMeasure p N) {X | upperGapPenalty θ R J X ≠ 0} ≤
      upperGapNormalizer p N θ R J := by
  have := gibbsMeasure_probability p N
  have hE : MeasurableSet {X | upperGapPenalty θ R J X = 0} :=
    measurableSet_eq_fun (upperGapPenalty_measurable θ R J) measurable_const
  have hmass : (gibbsMeasure p N) {X | upperGapPenalty θ R J X = 0} ≤
      upperGapNormalizer p N θ R J := by
    rw [← setLIntegral_one {X | upperGapPenalty θ R J X = 0},
      ← lintegral_indicator hE]
    apply lintegral_mono
    intro X
    by_cases h : upperGapPenalty θ R J X = 0
    · simp [h]
    · simp [h]
  have hcompl : {X : Riesz1.Configuration N | upperGapPenalty θ R J X = 0} =
      {X | upperGapPenalty θ R J X ≠ 0}ᶜ := by ext X; simp
  have hne : MeasurableSet {X | upperGapPenalty θ R J X ≠ 0} := by
    simpa only [compl_ofPred] using hE.compl
  rwa [hcompl, measure_compl hne (measure_ne_top _ _), measure_univ] at hmass

/-- See the proof of Lemma B.1 in the paper, the half-mass normalizer clause. -/
theorem upperGapNormalizer_ge_half (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) (R : {R : ℝ // 0 < R}) (J : Finset (Fin (N : ℕ)))
    (hsmall : 3 * J.card * Real.exp (-(Real.log 2 / 8) * R) ≤ 1 / 2) :
    (1 / 2 : ℝ≥0∞) ≤ upperGapNormalizer p N θ R J := by
  have hp := (upperGapPenalty_event_bound p N hN θ R J).trans
    (ENNReal.ofReal_le_ofReal hsmall)
  have hl := (tsub_le_tsub_left hp 1).trans (upperGapNormalizer_lower p N θ R J)
  simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
    ENNReal.ofReal_one, ENNReal.ofReal_ofNat, ENNReal.sub_half ENNReal.one_ne_top] using hl

/-- The arbitrary-set tilt has the usual normalized real density. -/
theorem upperTiltedParticleMeasure_eq_withDensity (p : Parameters) (N : ℕ+)
    (θ : PhysicalCutoff) (R : {R : ℝ // 0 < R})
    (J : Finset (Fin (N : ℕ))) :
    upperTiltedParticleMeasure p N θ R J =
      (gibbsMeasure p N).withDensity (fun X => ENNReal.ofReal
        ((∫ Y, Real.exp (-p.val.1 * upperGapPenalty θ R J Y) ∂gibbsMeasure p N)⁻¹ *
          Real.exp (-p.val.1 * upperGapPenalty θ R J X))) := by
  have := gibbsMeasure_probability p N
  have hi := integrable_upperGapWeight p N θ R J
  have hz : 0 < ∫ X, Real.exp (-p.val.1 * upperGapPenalty θ R J X) ∂gibbsMeasure p N :=
    integral_exp_pos hi
  rw [upperTiltedParticleMeasure, upperGapNormalizer_eq_ofReal_integral,
    ← withDensity_smul _ (((upperGapPenalty_measurable θ R J).const_mul _).exp.ennreal_ofReal)]
  congr 1
  funext X
  simp only [Pi.smul_apply, smul_eq_mul, ENNReal.ofReal_mul (inv_nonneg.mpr hz.le),
    ENNReal.ofReal_inv_of_pos hz]

private theorem event_discrepancy_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (A : Set Ω) :
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

/-- The event-supremum distance is bounded using the companion
library's half-variation estimate, with its normalization preserved. -/
private theorem totalVariation_le_of_half_etvDist_le {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {b : ℝ}
    (hb : (etvDist μ ν).toReal / 2 ≤ b) : totalVariation μ ν ≤ ENNReal.ofReal b := by
  apply iSup_le
  intro A
  rw [event_discrepancy_eq]
  exact ENNReal.ofReal_le_ofReal
    ((Riesz1.abs_measureReal_sub_le_etvDist_div_two μ ν A.property).trans hb)

/-- See the proof of Lemma B.1 in the paper, total variation comparison. In
fact the distance is at most the exceptional event's mass without any
half-mass assumption on the normalizer. -/
theorem upperTiltedParticleMeasure_totalVariation (p : Parameters) (N : ℕ+)
    (θ : PhysicalCutoff) (R : {R : ℝ // 0 < R})
    (J : Finset (Fin (N : ℕ))) :
    letI := gibbsMeasure_probability p N
    letI := upperTiltedParticleMeasure_probability p N θ R J
    totalVariation (gibbsMeasure p N) (upperTiltedParticleMeasure p N θ R J) ≤
      (gibbsMeasure p N) {X | upperGapPenalty θ R J X ≠ 0} := by
  have := gibbsMeasure_probability p N
  have := upperTiltedParticleMeasure_probability p N θ R J
  let z := ∫ X, Real.exp (-p.val.1 * upperGapPenalty θ R J X) ∂gibbsMeasure p N
  have hz : 0 < z := integral_exp_pos (integrable_upperGapWeight p N θ R J)
  have hz1 : z ≤ 1 := by
    have h := upperGapNormalizer_valid p N θ R J
    rw [upperGapNormalizer_eq_ofReal_integral] at h
    exact ENNReal.ofReal_le_one.mp h.2
  have hg : Measurable (fun X : Riesz1.Configuration N =>
      z⁻¹ * Real.exp (-p.val.1 * upperGapPenalty θ R J X)) :=
    (((upperGapPenalty_measurable θ R J).const_mul _).exp.const_mul _)
  have hg1 : ∫ X, z⁻¹ * Real.exp (-p.val.1 * upperGapPenalty θ R J X)
      ∂gibbsMeasure p N = 1 := by
    rw [integral_const_mul]
    exact inv_mul_cancel₀ hz.ne'
  have he := Riesz1.half_etvDist_le_measure_compl_of_one_le_on
    (gibbsMeasure p N) (upperTiltedParticleMeasure p N θ R J) hg
    (fun X => mul_nonneg (inv_nonneg.mpr hz.le) (Real.exp_pos _).le) hg1
    (measurableSet_eq_fun (upperGapPenalty_measurable θ R J) measurable_const)
    (fun X hX => by
      change upperGapPenalty θ R J X = 0 at hX
      simp only [hX, mul_zero, Real.exp_zero, mul_one]
      exact (one_le_inv₀ hz).mpr hz1)
    (upperTiltedParticleMeasure_eq_withDensity p N θ R J)
  simpa only [compl_ofPred, Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
    totalVariation_le_of_half_etvDist_le _ _ he

/-- See the proof of Lemma B.1 in the paper, domination by twice the original
law. This event formulation is the a.e. density bound and applies to
nonmeasurable sets by monotonicity of measures. -/
theorem upperTiltedParticleMeasure_le_two (p : Parameters) (N : ℕ+) (θ : PhysicalCutoff)
    (R : {R : ℝ // 0 < R}) (J : Finset (Fin (N : ℕ)))
    (hz : (1 / 2 : ℝ≥0∞) ≤ upperGapNormalizer p N θ R J) :
    upperTiltedParticleMeasure p N θ R J ≤ (2 : ℝ≥0∞) • gibbsMeasure p N := by
  have hweight : (gibbsMeasure p N).withDensity (fun X =>
      ENNReal.ofReal (Real.exp (-p.val.1 * upperGapPenalty θ R J X))) ≤ gibbsMeasure p N := by
    conv_rhs => rw [← withDensity_one (μ := gibbsMeasure p N)]
    apply withDensity_mono
    apply ae_of_all
    intro X
    apply ENNReal.ofReal_le_one.mpr
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr p.property.1.le)
      (upperGapPenalty_nonneg θ R J X)
  have hinv : (upperGapNormalizer p N θ R J)⁻¹ ≤ 2 := by
    calc
      _ ≤ (1 / 2 : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.mpr hz
      _ = 2 := by norm_num
  unfold upperTiltedParticleMeasure
  intro A
  simp only [Measure.smul_apply, smul_eq_mul]
  calc
    _ ≤ (upperGapNormalizer p N θ R J)⁻¹ * (gibbsMeasure p N) A := by
      gcongr
    _ ≤ 2 * (gibbsMeasure p N) A := by gcongr

/-- The ambient upper-gap penalty is twice differentiable at every
positive point, using only the cutoff's smoothness on its carrier. -/
theorem upperGapPenalty_contDiffAt {N : ℕ+} (θ : PhysicalCutoff)
    (R : {R : ℝ // 0 < R}) (J : Finset (Fin (N : ℕ)))
    (y : EuclideanSpace ℝ (Fin (N : ℕ))) (hy : ∀ i, 0 < y i) :
    ContDiffAt ℝ 2 (fun z : EuclideanSpace ℝ (Fin (N : ℕ)) =>
      ∑ i ∈ J, θ.val (z i / R)) y := by
  apply ContDiffAt.sum
  intro i _
  have hθ : ContDiffAt ℝ 2 θ.val (y i / R) :=
    (θ.property.1.of_le (by norm_num)).contDiffAt
      (Ici_mem_nhds (div_pos (hy i) R.property))
  exact hθ.comp y ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt.div_const R)

/-- The bilinear Hessian of the actual ambient upper-gap penalty. -/
theorem upperGapPenalty_hessian {N : ℕ+} (θ : PhysicalCutoff)
    (R : {R : ℝ // 0 < R}) (J : Finset (Fin (N : ℕ)))
    (y : EuclideanSpace ℝ (Fin (N : ℕ))) (hy : ∀ i, 0 < y i)
    (u v : EuclideanSpace ℝ (Fin (N : ℕ))) :
    fderiv ℝ (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin (N : ℕ)) =>
      ∑ i ∈ J, θ.val (z i / R))) y u v =
      ∑ i ∈ J, deriv (deriv θ.val) (y i / R) / (R : ℝ) ^ 2 * (u i * v i) := by
  classical
  have hK : ContDiffOn ℝ 2 θ.val (Ioi (0 : ℝ)) :=
    (θ.property.1.of_le (by norm_num)).mono Ioi_subset_Ici_self
  let l (i : Fin (N : ℕ)) : EuclideanSpace ℝ (Fin (N : ℕ)) →L[ℝ] ℝ :=
    (R : ℝ)⁻¹ • EuclideanSpace.proj i
  have hl (i : Fin (N : ℕ)) (z : EuclideanSpace ℝ (Fin (N : ℕ))) : l i z = z i / R := by
    simp only [l, smul_apply, EuclideanSpace.coe_proj,
      smul_eq_mul, div_eq_mul_inv, mul_comm]
  have he := (finite_linear_potential_derivatives (fun i : Fin (N : ℕ) => if i ∈ J then 1 else 0)
    (fun _ : Fin (N : ℕ) => θ.val) l (fun _ => Ioi (0 : ℝ)) (fun _ => isOpen_Ioi)
    (fun _ => hK) y (fun i => by rw [hl]; exact div_pos (hy i) R.property) u v).2
  simp only [hl, ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  field_simp

/-- Nearest-pair curvature and cutoff curvature complement each other.
This is the scalar estimate in the proof of Lemma B.1. -/
theorem upperGapPenalty_curvature_scalar (θ : PhysicalCutoff) {s x R : ℝ}
    (hs : 1 < s) (hx : 0 < x) (hR : 1 ≤ R) :
    R ^ (-s - 2) ≤ s * (s + 1) * x ^ (-s - 2) +
      deriv (deriv θ.val) (x / R) / R ^ 2 := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  obtain ⟨C, _, hθ, hθlarge⟩ := θ.property.2.2.2.2
  have hθnonneg := (hθ (x / R) (div_pos hx hR0)).1
  have hcoeff : 1 ≤ s * (s + 1) := by nlinarith
  have hp := Real.rpow_nonneg hx.le (-s - 2)
  by_cases hsmall : x ≤ R
  · have hpow := Real.rpow_le_rpow_of_nonpos hx hsmall (show -s - 2 ≤ 0 by linarith)
    have hpen := div_nonneg hθnonneg (sq_nonneg R)
    nlinarith
  · have hlarge : 1 ≤ x / R := (one_le_div hR0).mpr (le_of_not_ge hsmall)
    have hh := hθlarge (x / R) hlarge
    have hpow := Real.rpow_le_rpow_of_exponent_le hR (show -s - 2 ≤ -(2 : ℝ) by linarith)
    have he : R ^ (-(2 : ℝ)) = 1 / R ^ 2 := by
      rw [Real.rpow_neg hR0.le, Real.rpow_two, one_div]
    rw [he] at hpow
    have hdiv := div_le_div_of_nonneg_right hh (sq_nonneg R)
    nlinarith [mul_nonneg (show 0 ≤ s * (s + 1) by positivity) hp]

/-- See the proof of Lemma B.1 in the paper, full-simplex curvature clause.
The realizing energy agrees with the physical ambient extension.
The bound holds in every ambient direction, hence in particular on the
tangent space, and includes `N = 2`. -/
theorem upperGapPenalty_curvature (p : Parameters) (hs : 1 < p.val.2)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (θ : PhysicalCutoff)
    (R : {R : ℝ // 0 < R}) (hR : 1 ≤ (R : ℝ))
    (J : Finset (Fin (N : ℕ))) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ∀ (y : Fin (N : ℕ) → ℝ), y ∈ Riesz1.gapSimplex N →
        ∀ u : EuclideanSpace ℝ (Fin (N : ℕ)),
          (R : ℝ) ^ (-p.val.2 - 2) * (∑ i ∈ J, (u i) ^ 2) ≤
            fderiv ℝ (fderiv ℝ (fun z => W z + ∑ i ∈ J, θ.val (z i / R)))
              (WithLp.toLp 2 y) u u := by
  classical
  obtain ⟨W, hW, hval, _, _, hlow, _⟩ :=
    (PhysicalEnergy.restriction_and_derivatives p N hN).2.2
  refine ⟨W, hW, hval, ?_⟩
  intro y hy u
  let x : EuclideanSpace ℝ (Fin (N : ℕ)) := WithLp.toLp 2 y
  let F : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ := fun z => ∑ i ∈ J, θ.val (z i / R)
  have hx : x ∈ gapAmbientDomain N := PhysicalEnergy.simplex_subset_ambient N y hy
  have hpos (z : EuclideanSpace ℝ (Fin (N : ℕ))) (hz : z ∈ gapAmbientDomain N) :
      ∀ i, 0 < z i := by
    intro i
    simpa only [PhysicalEnergy.gapSum_one] using (hz i 1 (by omega) (by omega)).1
  have hWo : IsOpen (gapAmbientDomain N) := PhysicalEnergy.isOpen_gapAmbientDomain N
  have hWd (z) (hz : z ∈ gapAmbientDomain N) : ContDiffAt ℝ 2 W z :=
    (hW.of_le (by norm_num)).contDiffAt (hWo.mem_nhds hz)
  have hFd (z) (hz : z ∈ gapAmbientDomain N) : ContDiffAt ℝ 2 F z :=
    upperGapPenalty_contDiffAt θ R J z (hpos z hz)
  have he : fderiv ℝ (fun z => W z + F z) =ᶠ[𝓝 x]
      fun z => fderiv ℝ W z + fderiv ℝ F z := by
    filter_upwards [hWo.mem_nhds hx] with z hz
    exact fderiv_fun_add ((hWd z hz).differentiableAt (by norm_num))
      ((hFd z hz).differentiableAt (by norm_num))
  have hWdd : DifferentiableAt ℝ (fderiv ℝ W) x :=
    ((hWd x hx).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hFdd : DifferentiableAt ℝ (fderiv ℝ F) x :=
    ((hFd x hx).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hh : fderiv ℝ (fderiv ℝ (fun z => W z + F z)) x u u =
      fderiv ℝ (fderiv ℝ W) x u u +
        ∑ i ∈ J, deriv (deriv θ.val) (y i / R) / (R : ℝ) ^ 2 * (u i) ^ 2 := by
    rw [he.fderiv_eq, fderiv_fun_add hWdd hFdd]
    simp only [add_apply]
    rw [upperGapPenalty_hessian θ R J x (hpos x hx) u u]
    simp only [x, pow_two]
  change _ ≤ fderiv ℝ (fderiv ℝ (fun z => W z + F z)) x u u
  rw [hh]
  have hbase := hlow y hy u
  have hnonneg (i : Fin (N : ℕ)) : 0 ≤ y i ^ (-p.val.2 - 2) * (u i) ^ 2 :=
    mul_nonneg (Real.rpow_nonneg (hy.1 i).le _) (sq_nonneg _)
  have hsub : ∑ i ∈ J, y i ^ (-p.val.2 - 2) * (u i) ^ 2 ≤
      ∑ i, y i ^ (-p.val.2 - 2) * (u i) ^ 2 :=
    Finset.sum_le_univ_sum_of_nonneg (fun i => hnonneg i)
  have hcoef : 0 ≤ p.val.2 * (p.val.2 + 1) := by positivity
  have hJ := mul_le_mul_of_nonneg_left hsub hcoef
  have hscalar : (R : ℝ) ^ (-p.val.2 - 2) * (∑ i ∈ J, (u i) ^ 2) ≤
      p.val.2 * (p.val.2 + 1) * (∑ i ∈ J, y i ^ (-p.val.2 - 2) * (u i) ^ 2) +
        ∑ i ∈ J, deriv (deriv θ.val) (y i / R) / (R : ℝ) ^ 2 * (u i) ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hi := mul_le_mul_of_nonneg_right
      (upperGapPenalty_curvature_scalar θ hs (hy.1 i) hR) (sq_nonneg (u i))
    nlinarith
  exact hscalar.trans (add_le_add (hJ.trans hbase) le_rfl)

/-- See the proof of Lemma B.1 in the paper, total variation on the actual
full gap image, compared to the `gapLaw`. -/
theorem upperTiltedGapLaw_totalVariation (p : Parameters) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (θ : PhysicalCutoff) (R : {R : ℝ // 0 < R})
    (J : Finset (Fin (N : ℕ))) :
    letI := gibbsMeasure_probability p N
    letI := upperTiltedParticleMeasure_probability p N θ R J
    letI : IsProbabilityMeasure (gapLaw p N) := by unfold gapLaw; infer_instance
    totalVariation (gapLaw p N)
        ((upperTiltedParticleMeasure p N θ R J).map gapVector) ≤
      ENNReal.ofReal (3 * J.card * Real.exp (-(Real.log 2 / 8) * R)) := by
  have := gibbsMeasure_probability p N
  have := upperTiltedParticleMeasure_probability p N θ R J
  have : IsProbabilityMeasure (gapLaw p N) := by unfold gapLaw; infer_instance
  have hm : Measurable (@gapVector N) := Riesz1.measurable_gapVector N
  have hTV := (upperTiltedParticleMeasure_totalVariation p N θ R J).trans
    (upperGapPenalty_event_bound p N hN θ R J)
  apply iSup_le
  intro A
  change ((gapLaw p N) A.val -
      ((upperTiltedParticleMeasure p N θ R J).map gapVector) A.val) +
    (((upperTiltedParticleMeasure p N θ R J).map gapVector) A.val -
      (gapLaw p N) A.val) ≤ _
  rw [gapLaw, Measure.map_apply hm A.property, Measure.map_apply hm A.property]
  exact (le_iSup (fun B : {B : Set (Riesz1.Configuration N) // MeasurableSet B} =>
    ((gibbsMeasure p N) B.val - (upperTiltedParticleMeasure p N θ R J) B.val) +
      ((upperTiltedParticleMeasure p N θ R J) B.val - (gibbsMeasure p N) B.val))
      ⟨gapVector ⁻¹' A.val, hm A.property⟩).trans hTV

/-- The first `n` labels as a finite subset of all `N` labels. This is
the image of the canonical inclusion, including the full-cycle case. -/
def firstGapSet (N n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ)) : Finset (Fin (N : ℕ)) :=
  Finset.univ.map (Fin.castLEEmb hn)

/-- The canonical first-block inclusion preserves its number of labels. -/
theorem firstGapSet_card (N n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ)) :
    (firstGapSet N n hn).card = (n : ℕ) := by
  simp only [firstGapSet, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- The general penalty specializes literally to the upper-only
physical penalty at the scale prescribed by its exponent parameter. -/
theorem upperGapPenalty_firstGapSet (N n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ) (X : Riesz1.Configuration N) :
    upperGapPenalty θ ⟨(n : ℝ) ^ ε, Real.rpow_pos_of_pos (by positivity) _⟩ (firstGapSet N n hn) X =
      physicalGapPenalty N n hn θ ε false X := by
  classical
  simp only [upperGapPenalty, firstGapSet, Finset.sum_map, Fin.castLEEmb_apply,
    physicalGapPenalty, Bool.false_eq_true, ↓reduceIte, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg θ.val
  change gap X i.val / (n : ℝ) ^ ε = (n : ℝ) ^ (-ε) * gap X i.val
  rw [Real.rpow_neg (show 0 ≤ (n : ℝ) by positivity), div_eq_mul_inv, mul_comm]

/-- The first-block extended normalizer equals `tiltNormalizer`. -/
theorem upperGapNormalizer_firstGapSet (p : Parameters) (N n : ℕ+)
    (hn : (n : ℕ) ≤ (N : ℕ)) (θ : PhysicalCutoff) (ε : ℝ) :
    upperGapNormalizer p N θ ⟨(n : ℝ) ^ ε, Real.rpow_pos_of_pos (by positivity) _⟩ (firstGapSet N n hn) =
      tiltNormalizer p N n hn θ ε false := by
  unfold upperGapNormalizer tiltNormalizer
  simp_rw [upperGapPenalty_firstGapSet]

/-- The general first-block tilt equals `tiltedParticleMeasure`. -/
theorem upperTiltedParticleMeasure_firstGapSet (p : Parameters) (N n : ℕ+)
    (hn : (n : ℕ) ≤ (N : ℕ)) (θ : PhysicalCutoff) (ε : ℝ) :
    upperTiltedParticleMeasure p N θ ⟨(n : ℝ) ^ ε, Real.rpow_pos_of_pos (by positivity) _⟩ (firstGapSet N n hn) =
      tiltedParticleMeasure p N n hn θ ε false := by
  unfold upperTiltedParticleMeasure tiltedParticleMeasure
  rw [upperGapNormalizer_firstGapSet]
  simp_rw [upperGapPenalty_firstGapSet]

/-- See the proof of Lemma B.1 in the paper, measure comparison clauses for
the first-block penalty and law. The constants are uniform in all
positive temperatures and all admissible exponents. -/
theorem physicalUpperTilt_comparison (p : Parameters) (N n : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (hn : (n : ℕ) ≤ (N : ℕ)) (θ : PhysicalCutoff) (ε : ℝ) :
    letI := gibbsMeasure_probability p N
    letI := DefinitionSanity.tilted_probability p N n hn θ ε false
    let E := 3 * (n : ℝ) * Real.exp (-(Real.log 2 / 8) * (n : ℝ) ^ ε)
    (gibbsMeasure p N) {X | physicalGapPenalty N n hn θ ε false X ≠ 0} ≤ ENNReal.ofReal E ∧
      totalVariation (gibbsMeasure p N) (tiltedParticleMeasure p N n hn θ ε false) ≤
        ENNReal.ofReal E ∧
      (E ≤ 1 / 2 → (1 / 2 : ℝ≥0∞) ≤ tiltNormalizer p N n hn θ ε false ∧
        tiltedParticleMeasure p N n hn θ ε false ≤ (2 : ℝ≥0∞) • gibbsMeasure p N) := by
  have := gibbsMeasure_probability p N
  have := DefinitionSanity.tilted_probability p N n hn θ ε false
  let R : {R : ℝ // 0 < R} := ⟨(n : ℝ) ^ ε, Real.rpow_pos_of_pos (by positivity) _⟩
  let J := firstGapSet N n hn
  have he := upperGapPenalty_event_bound p N hN θ R J
  have ht := (upperTiltedParticleMeasure_totalVariation p N θ R J).trans he
  have hhalf := upperGapNormalizer_ge_half p N hN θ R J
  have hdom := upperTiltedParticleMeasure_le_two p N θ R J
  simp only [J, R, upperGapPenalty_firstGapSet, firstGapSet_card,
    upperGapNormalizer_firstGapSet, upperTiltedParticleMeasure_firstGapSet] at he ht hhalf hdom
  exact ⟨he, ht, fun h => ⟨hhalf h, hdom (hhalf h)⟩⟩

/-- Empty-set boundary check for the arbitrary-set construction: no
forcing changes the original particle probability. -/
theorem upperTiltedParticleMeasure_empty (p : Parameters) (N : ℕ+)
    (θ : PhysicalCutoff) (R : {R : ℝ // 0 < R}) :
    upperTiltedParticleMeasure p N θ R ∅ = gibbsMeasure p N := by
  have := gibbsMeasure_probability p N
  simp [upperTiltedParticleMeasure, upperGapNormalizer, upperGapPenalty]

end Riesz2.DecayShort
