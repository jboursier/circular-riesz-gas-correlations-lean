/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.ObservableTransfer
import all Riesz2.DecayShort.LocalLaw
public import Riesz2.Frozen.GapDerivativeNorm
public import Riesz2.ToMathlib.CyclicIntervals

/-!
# Removal of the long-range upper-gap tilt

See the proof of Theorem 1 in the paper. We reuse the existing arbitrary-set
penalty and its bridge to the physical penalty. Only upper tails enter the rare
event, so its exponent and rate are independent of temperature. Centered fourth moments
control unbounded observables. Measure domination gives the sharp square-root-of-two
norm comparison even for derivative representatives which are only a.e. measurable.
-/

public section
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace Riesz2.DecayLong.ObservableTransfer

open Riesz2.DecayShort

/-- The upper-only active penalty is the already constructed upper-gap penalty.
See Section 5 of the paper. -/
theorem upper_penalty_eq {N : ℕ+} (θ : PhysicalCutoff) (R : {R : ℝ // 0 < R})
    (I : Finset (Fin (N : ℕ))) :
    activeGapPenalty θ R false I = upperGapPenalty θ R I := by
  funext X
  simp only [activeGapPenalty, upperGapPenalty, Bool.false_eq_true, ↓reduceIte, add_zero]

/-- The arbitrary-set upper tilt is the existing normalized upper-gap law. -/
theorem upper_tilt_eq (p : Parameters) (N : ℕ+) (θ : PhysicalCutoff)
    (R : {R : ℝ // 0 < R}) (I : Finset (Fin (N : ℕ))) :
    activeTilt p N θ R false I = upperTiltedParticleMeasure p N θ R I := by
  rw [activeTilt, upper_penalty_eq]
  rfl

/-- The real normalizer agrees with the existing extended normalizer. -/
theorem upper_normalizer_eq (p : Parameters) (N : ℕ+) (θ : PhysicalCutoff)
    (R : {R : ℝ // 0 < R}) (I : Finset (Fin (N : ℕ))) :
    ENNReal.ofReal (NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (activeGapPenalty θ R false I)) = upperGapNormalizer p N θ R I := by
  rw [upper_penalty_eq, upperGapNormalizer_eq_ofReal_integral]
  rfl

/-- Upper forcing has a temperature-independent exceptional-event bound. -/
theorem upper_penalty_mass (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) (R : {R : ℝ // 0 < R}) (I : Finset (Fin (N : ℕ))) :
    (gibbsMeasure p N).real {X | activeGapPenalty θ R false I X ≠ 0} ≤
      3 * I.card * Real.exp (-(Real.log 2 / 8) * R) := by
  have := gibbsMeasure_probability p N
  rw [upper_penalty_eq]
  exact measureReal_le_of_le_ofReal (by positivity)
    (upperGapPenalty_event_bound p N hN θ R I)

/-- A half-normalizer bounds the actual density and the measure by two. -/
theorem upper_density_bound (p : Parameters) (N : ℕ+) (θ : PhysicalCutoff)
    (R : {R : ℝ // 0 < R}) (I : Finset (Fin (N : ℕ)))
    (hz : 1 / 2 ≤ NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (activeGapPenalty θ R false I)) :
    (∀ X, (NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (activeGapPenalty θ R false I))⁻¹ *
        Real.exp (-p.val.1 * activeGapPenalty θ R false I X) ≤ 2) ∧
    activeTilt p N θ R false I ≤ (2 : ℝ≥0∞) • gibbsMeasure p N := by
  have hzpos : 0 < NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (activeGapPenalty θ R false I) := lt_of_lt_of_le (by norm_num) hz
  have hinv : (NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (activeGapPenalty θ R false I))⁻¹ ≤ 2 := by
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hz
  refine ⟨fun X => ?_, ?_⟩
  · exact (mul_le_of_le_one_right (inv_nonneg.mpr hzpos.le)
      (NonnegativeTilt.exp_neg_mul_le_one p.property.1.le
        (activeGapPenalty_nonneg θ R.property.le false I) X)).trans hinv
  · rw [upper_tilt_eq]
    apply upperTiltedParticleMeasure_le_two
    rw [← upper_normalizer_eq]
    exact (by norm_num [ENNReal.ofReal_div_of_pos] :
      (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2)).trans_le
      (ENNReal.ofReal_le_ofReal hz)

/-- The sharp `L²` measure comparison applies to every function, including any
Lebesgue-a.e. derivative representative in `GapObservable`. -/
theorem upper_norm_bound (p : Parameters) (N : ℕ+) (θ : PhysicalCutoff)
    (R : {R : ℝ // 0 < R}) (I : Finset (Fin (N : ℕ)))
    (hz : 1 / 2 ≤ NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (activeGapPenalty θ R false I)) (f : Riesz1.Configuration N → ℝ) :
    eLpNorm f 2 (activeTilt p N θ R false I) ≤
      ENNReal.ofReal (Real.sqrt 2) * eLpNorm f 2 (gibbsMeasure p N) := by
  have h := eLpNorm_le_of_measure_le_smul (f := f) (p := 2)
    (upper_density_bound p N θ R I hz).2
  convert h using 1
  simp only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat,
    smul_eq_mul, Real.sqrt_eq_rpow]
  rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by norm_num)]
  norm_num

/-- Internal fourth-moment estimate. The hypotheses here are estimates supplied by
the single-gap theorem when assembling the final result below. -/
theorem internal_covariance_bound {N : ℕ+} (p : Parameters) (θ : PhysicalCutoff)
    {R : ℝ} (hR : 1 ≤ R) (I : Finset (Fin (N : ℕ))) {q D2 D4 : ℝ}
    (hD2 : 0 ≤ D2) (hq1 : q ≤ 1)
    (hz : 1 / 2 ≤ NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (activeGapPenalty θ R false I))
    (hq : (gibbsMeasure p N).real {X | activeGapPenalty θ R false I X ≠ 0} ≤ q)
    (f g : GapObservable) (i j : ℤ)
    (hi2 : Integrable (fun X : Riesz1.Configuration N => gap X i ^ (2 : ℝ)) (gibbsMeasure p N))
    (hj2 : Integrable (fun X : Riesz1.Configuration N => gap X j ^ (2 : ℝ)) (gibbsMeasure p N))
    (hi4 : Integrable (fun X : Riesz1.Configuration N => gap X i ^ (4 : ℝ)) (gibbsMeasure p N))
    (hj4 : Integrable (fun X : Riesz1.Configuration N => gap X j ^ (4 : ℝ)) (gibbsMeasure p N))
    (h2i : ∫ X, gap X i ^ (2 : ℝ) ∂gibbsMeasure p N ≤ D2)
    (h2j : ∫ X, gap X j ^ (2 : ℝ) ∂gibbsMeasure p N ≤ D2)
    (h4i : ∫ X, gap X i ^ (4 : ℝ) ∂gibbsMeasure p N ≤ D4)
    (h4j : ∫ X, gap X j ^ (4 : ℝ) ∂gibbsMeasure p N ≤ D4) :
    |covariance (fun X => f.val.1 (gap X i)) (fun X => g.val.1 (gap X j)) (gibbsMeasure p N) -
      covariance (fun X => f.val.1 (gap X i)) (fun X => g.val.1 (gap X j))
        (activeTilt p N θ R false I)| ≤
      4 * Real.sqrt q * (Real.sqrt (8 * D4 + 8) + 6 * (2 * D2 + 2)) *
        derivativeSup f * derivativeSup g := by
  have hq0 : 0 ≤ q := measureReal_nonneg.trans hq
  let K := (NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
    (activeGapPenalty θ R false I))⁻¹ * (Real.sqrt q + q)
  have hzpos : 0 < NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (activeGapPenalty θ R false I) := lt_of_lt_of_le (by norm_num) hz
  have hzinv : (NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (activeGapPenalty θ R false I))⁻¹ ≤ 2 := by
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hz
  have hsqrt : Real.sqrt q ≤ 1 := (Real.sqrt_le_sqrt hq1).trans_eq (by norm_num)
  have hqsqrt : q ≤ Real.sqrt q := by
    nlinarith only [Real.sq_sqrt hq0, Real.sqrt_nonneg q, hsqrt]
  have hK0 : 0 ≤ K := mul_nonneg (inv_nonneg.mpr hzpos.le) (by positivity)
  have hK : K ≤ 4 * Real.sqrt q := by
    dsimp [K]
    calc
      _ ≤ 2 * (Real.sqrt q + q) := mul_le_mul_of_nonneg_right hzinv (by positivity)
      _ ≤ _ := by linarith
  have hK4 : K ≤ 4 := by linarith
  have hb := covariance_activeTilt_pair_le p θ hR false I (by norm_num : (0 : ℝ) < 1 / 2)
    hz hq (rfl : K = _) f g i j hi2 hj2 hi4 hj4 h2i h2j h4i h4j
  have hc : Real.sqrt (8 * D4 + 8) + (2 + K) * (2 * D2 + 2) ≤
      Real.sqrt (8 * D4 + 8) + 6 * (2 * D2 + 2) := by nlinarith
  have hU : 0 ≤ derivativeSup f := ENNReal.toReal_nonneg
  have hV : 0 ≤ derivativeSup g := ENNReal.toReal_nonneg
  calc
    _ ≤ K * (derivativeSup f * derivativeSup g) *
        (Real.sqrt (8 * D4 + 8) + (2 + K) * (2 * D2 + 2)) := hb
    _ ≤ (4 * Real.sqrt q) * (derivativeSup f * derivativeSup g) *
        (Real.sqrt (8 * D4 + 8) + 6 * (2 * D2 + 2)) := by
      apply mul_le_mul _ hc (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right hK (mul_nonneg hU hV)
    _ = _ := by ring

/-- See the proof of Theorem 1 in the paper, with its exponent fixed to
`η` before the inverse temperature. The conclusion holds for every active set,
so in particular for proper cyclic blocks and the full cycle. The measures in
the covariance are particle laws evaluated at the gap functions.
The total-variation conclusion is also stated for their gap images. -/
theorem arbitrary_set_tilt (s η : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (β : ℝ), 0 < β → ∀ (θ : PhysicalCutoff),
      ∃ C c : ℝ, ∃ n0 : ℕ, 0 < C ∧ 0 < c ∧ 2 ≤ n0 ∧
        ∀ (p : Parameters), p.val.2 = s → p.val.1 = β →
          ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (I : Finset (Fin (N : ℕ))), n0 ≤ I.card →
          letI := gibbsMeasure_probability p N
          letI : IsProbabilityMeasure (gapLaw p N) := by unfold gapLaw; infer_instance
          letI := activeTilt_isProbabilityMeasure p θ
            (Real.rpow_nonneg (Nat.cast_nonneg I.card) η) false I
          let R := (I.card : ℝ) ^ η
          let F := activeGapPenalty θ R false I
          let Z := NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1 F
          let Q := activeTilt p N θ R false I
          1 / 2 ≤ Z ∧ Z ≤ 1 ∧ IsProbabilityMeasure Q ∧
          Q = (gibbsMeasure p N).withDensity
            (fun X => ENNReal.ofReal (Z⁻¹ * Real.exp (-p.val.1 * F X))) ∧
          (∀ X, Z⁻¹ * Real.exp (-p.val.1 * F X) ≤ 2) ∧
          Q ≤ (2 : ℝ≥0∞) • gibbsMeasure p N ∧
          totalVariation (gibbsMeasure p N) Q ≤
            ENNReal.ofReal (C * Real.exp (-c * (I.card : ℝ) ^ δ)) ∧
          totalVariation (gapLaw p N) (Q.map (gapVector (N := N))) ≤
            ENNReal.ofReal (C * Real.exp (-c * (I.card : ℝ) ^ δ)) ∧
          (∀ (f g : GapObservable) (i j : Fin (N : ℕ)),
            GapSecondMoments p N i.val j.val f g ∧
            MemLp (fun X => f.val.1 (gap X i.val)) 2 Q ∧
            MemLp (fun X => g.val.1 (gap X j.val)) 2 Q ∧
            MemLp (fun X => f.val.2 (gap X i.val)) 2 Q ∧
            MemLp (fun X => g.val.2 (gap X j.val)) 2 Q ∧
            |covariance (fun X => f.val.1 (gap X i.val)) (fun X => g.val.1 (gap X j.val))
                (gibbsMeasure p N) -
              covariance (fun X => f.val.1 (gap X i.val)) (fun X => g.val.1 (gap X j.val)) Q| ≤
              C * Real.exp (-c * (I.card : ℝ) ^ δ) * derivativeSup f * derivativeSup g) ∧
          (∀ (f : Riesz1.Configuration N → ℝ),
            eLpNorm f 2 Q ≤ ENNReal.ofReal (Real.sqrt 2) * eLpNorm f 2 (gibbsMeasure p N)) := by
  refine ⟨η, hη, fun β hβ θ => ?_⟩
  let a := Real.log 2 / 8
  have ha : 0 < a := div_pos (Real.log_pos one_lt_two) (by norm_num)
  obtain ⟨B, hB, hpoly⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := 1) (c := a) (c' := a / 2) hη (by linarith)
  let Kq := 3 * B + 1
  have hKq : 0 < Kq := by dsimp [Kq]; positivity
  obtain ⟨n0, hn0⟩ := exists_threshold_exp (Kq := Kq) (c := a / 2) hη (by linarith)
  obtain ⟨D2, hD2, hm2⟩ := gap_moment_bound hs (ne_of_lt hs1) hβ 2 (by norm_num)
  obtain ⟨D4, hD4, hm4⟩ := gap_moment_bound hs (ne_of_lt hs1) hβ 4 (by norm_num)
  let M := Real.sqrt (8 * D4 + 8) + 6 * (2 * D2 + 2)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let C := Kq + 4 * Real.sqrt Kq * M + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, a / 4, max n0 2, hC, by positivity, le_max_right _ _, ?_⟩
  intro p hps hpβ N hN I hI
  dsimp only
  have hp := gibbsMeasure_probability p N
  have hn : 1 ≤ I.card := by omega
  have hnR : (1 : ℝ) ≤ I.card := by exact_mod_cast hn
  have hR : 1 ≤ (I.card : ℝ) ^ η := Real.one_le_rpow hnR hη.le
  let R : {R : ℝ // 0 < R} := ⟨(I.card : ℝ) ^ η, lt_of_lt_of_le zero_lt_one hR⟩
  let q := Kq * Real.exp (-(a / 2) * (I.card : ℝ) ^ η)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hqhalf : q ≤ 1 / 2 := hn0 I.card (by omega)
  have hmass : (gibbsMeasure p N).real
      {X | activeGapPenalty θ R false I X ≠ 0} ≤ q := by
    have hb := hpoly (I.card : ℝ) hnR
    rw [Real.rpow_one] at hb
    calc
      _ ≤ 3 * I.card * Real.exp (-a * (I.card : ℝ) ^ η) := upper_penalty_mass p N hN θ R I
      _ ≤ (3 * B) * Real.exp (-(a / 2) * (I.card : ℝ) ^ η) := by linarith
      _ ≤ q := by dsimp [q, Kq]; nlinarith [Real.exp_pos (-(a / 2) * (I.card : ℝ) ^ η)]
  have hG := activeGapPenalty_measurable θ R.property.le false I
  have hG0 := activeGapPenalty_nonneg θ R.property.le false I
  have hz : 1 / 2 ≤ NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (activeGapPenalty θ R false I) := by
    have := NonnegativeTilt.one_sub_expTiltNormalizer_le (μ := gibbsMeasure p N)
      hG p.property.1.le hG0
    linarith
  have hd := upper_density_bound p N θ R I hz
  have hprob := activeTilt_isProbabilityMeasure p θ R.property.le false I
  have hdom : ∀ {f : Riesz1.Configuration N → ℝ}, MemLp f 2 (gibbsMeasure p N) →
      MemLp f 2 (activeTilt p N θ R false I) :=
    fun hf => hf.of_measure_le_smul (by norm_num) hd.2
  have hqC : q ≤ C * Real.exp (-(a / 4) * (I.card : ℝ) ^ η) := by
    have he : Real.exp (-(a / 2) * (I.card : ℝ) ^ η) ≤
        Real.exp (-(a / 4) * (I.card : ℝ) ^ η) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.rpow_nonneg (Nat.cast_nonneg I.card) η])
    have hKC : Kq ≤ C := by
      dsimp [C]
      nlinarith [mul_nonneg (Real.sqrt_nonneg Kq) hM]
    exact mul_le_mul hKC he (Real.exp_pos _).le hC.le
  have htv := (totalVariation_activeTilt_le p θ R.property.le false I).trans
    (ENNReal.ofReal_le_ofReal (hmass.trans hqC))
  refine ⟨hz, NonnegativeTilt.expTiltNormalizer_le_one hG p.property.1.le hG0,
    hprob, NonnegativeTilt.expTilt_eq_withDensity hG p.property.1.le hG0,
    hd.1, hd.2, htv, ?_, ?_, fun f => upper_norm_bound p N θ R I hz f⟩
  · exact (NonnegativeTilt.totalVariation_map_le _ _ _ (Riesz1.measurable_gapVector N)).trans htv
  · intro f g i j
    have h2 (k : ℤ) : ∫ X, gap X k ^ (2 : ℝ) ∂gibbsMeasure p N ≤ D2 := by
      have hb := (hm2 p hps hpβ N hN k).2.2
      have hi : 0 ≤ ∫ X, gap X k ^ (-(2 : ℝ)) ∂gibbsMeasure p N :=
        integral_nonneg fun X => Real.rpow_nonneg (Riesz1.gap_pos X k).le _
      linarith
    have h4 (k : ℤ) : ∫ X, gap X k ^ (4 : ℝ) ∂gibbsMeasure p N ≤ D4 := by
      have hb := (hm4 p hps hpβ N hN k).2.2
      have hi : 0 ≤ ∫ X, gap X k ^ (-(4 : ℝ)) ∂gibbsMeasure p N :=
        integral_nonneg fun X => Real.rpow_nonneg (Riesz1.gap_pos X k).le _
      linarith
    have hm := gapSecondMoments_observable p N hN f g i j
      (hm2 p hps hpβ N hN i.val).1 (hm2 p hps hpβ N hN j.val).1
    refine ⟨hm, hdom hm.1, hdom hm.2.1, hdom hm.2.2.1, hdom hm.2.2.2, ?_⟩
    have hb := internal_covariance_bound p θ hR I hD2.le (by linarith : q ≤ 1) hz hmass
      f g i.val j.val (hm2 p hps hpβ N hN i.val).1 (hm2 p hps hpβ N hN j.val).1
      (hm4 p hps hpβ N hN i.val).1 (hm4 p hps hpβ N hN j.val).1
      (h2 _) (h2 _) (h4 _) (h4 _)
    have hsq : Real.sqrt q = Real.sqrt Kq * Real.exp (-(a / 4) * (I.card : ℝ) ^ η) := by
      have he : Real.exp (-(a / 2) * (I.card : ℝ) ^ η) =
          Real.exp (-(a / 4) * (I.card : ℝ) ^ η) ^ 2 := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      dsimp [q]
      rw [he, Real.sqrt_mul hKq.le, Real.sqrt_sq (Real.exp_pos _).le]
    have hcoeff : 4 * Real.sqrt Kq * M ≤ C := by dsimp [C]; linarith
    calc
      _ ≤ 4 * Real.sqrt q * M * derivativeSup f * derivativeSup g := hb
      _ = (4 * Real.sqrt Kq * M) * Real.exp (-(a / 4) * (I.card : ℝ) ^ η) *
          derivativeSup f * derivativeSup g := by rw [hsq]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
        apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
        exact mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le

/-- See Section 5 of the paper: the real normalizer used above is precisely the
extended normalizer on the first block, with its finiteness retained. -/
theorem first_block_normalizer (p : Parameters) (N n : ℕ+)
    (hn : (n : ℕ) ≤ (N : ℕ)) (θ : PhysicalCutoff) (η : ℝ) :
    ENNReal.ofReal (NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (activeGapPenalty θ ((n : ℝ) ^ η) false (Finset.univ.map (Fin.castLEEmb hn)))) =
        tiltNormalizer p N n hn θ η false := by
  have := gibbsMeasure_probability p N
  have hR : 0 ≤ (n : ℝ) ^ η := Real.rpow_nonneg (Nat.cast_nonneg _) η
  rw [← NonnegativeTilt.lintegral_normalizer_eq (activeGapPenalty_measurable θ hR false _)
    p.property.1.le (activeGapPenalty_nonneg θ hR false _),
    activeGapPenalty_firstGapSet hn θ η false]
  rfl

/-- Covariance of gap-coordinate observables is unchanged on passing from a
particle law to its gap image (Theorem 1). -/
theorem covariance_gap_image {N : ℕ+} (μ : Measure (Riesz1.Configuration N))
    (f g : GapObservable) (i j : Fin (N : ℕ)) :
    covariance (fun y => f.val.1 (y i)) (fun y => g.val.1 (y j)) (μ.map gapVector) =
      covariance (fun X => f.val.1 (gap X i.val)) (fun X => g.val.1 (gap X j.val)) μ := by
  exact covariance_map_fun
    (((CenteredObservable.continuous_observable f).measurable.comp
      (measurable_pi_apply i)).aestronglyMeasurable)
    (((CenteredObservable.continuous_observable g).measurable.comp
      (measurable_pi_apply j)).aestronglyMeasurable)
    (Riesz1.measurable_gapVector N).aemeasurable

/-- See the proof of Theorem 1 in the paper for a cyclic block of `n ≥ 2`
gaps, either proper (`2n ≤ N`) or the full cycle. The exponent precedes β.
Every observable and derivative in this conclusion is `L²` under both laws.
The last comparison applies, in particular, to any derivative representative.
`covariance_gap_image` identifies the displayed covariances with those under
the physical and tilted gap laws. -/
theorem decay_gap_correlations_tilt (s η : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (β : ℝ), 0 < β → ∀ (θ : PhysicalCutoff),
      ∃ C c : ℝ, ∃ n0 : ℕ, 0 < C ∧ 0 < c ∧ 2 ≤ n0 ∧
        ∀ (p : Parameters), p.val.2 = s → p.val.1 = β →
          ∀ (N n : ℕ+), 2 ≤ (N : ℕ) → 2 ≤ (n : ℕ) → n0 ≤ (n : ℕ) →
          (2 * (n : ℕ) ≤ (N : ℕ) ∨ n = N) → ∀ a : ℤ,
          letI := gibbsMeasure_probability p N
          letI : IsProbabilityMeasure (gapLaw p N) := by unfold gapLaw; infer_instance
          letI := activeTilt_isProbabilityMeasure p θ
            (Real.rpow_nonneg (Nat.cast_nonneg (n : ℕ)) η) false (cyclicInterval N a n)
          let F := activeGapPenalty θ ((n : ℝ) ^ η) false (cyclicInterval N a n)
          let Z := NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1 F
          let Q := activeTilt p N θ ((n : ℝ) ^ η) false (cyclicInterval N a n)
          1 / 2 ≤ Z ∧ Z ≤ 1 ∧ IsProbabilityMeasure Q ∧
          Q = (gibbsMeasure p N).withDensity
            (fun X => ENNReal.ofReal (Z⁻¹ * Real.exp (-p.val.1 * F X))) ∧
          (∀ X, Z⁻¹ * Real.exp (-p.val.1 * F X) ≤ 2) ∧
          Q ≤ (2 : ℝ≥0∞) • gibbsMeasure p N ∧
          totalVariation (gibbsMeasure p N) Q ≤ ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ δ)) ∧
          totalVariation (gapLaw p N) (Q.map (gapVector (N := N))) ≤
            ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ δ)) ∧
          (∀ (f g : GapObservable) (i j : Fin (N : ℕ)),
            GapSecondMoments p N i.val j.val f g ∧
            MemLp (fun X => f.val.1 (gap X i.val)) 2 Q ∧
            MemLp (fun X => g.val.1 (gap X j.val)) 2 Q ∧
            MemLp (fun X => f.val.2 (gap X i.val)) 2 Q ∧
            MemLp (fun X => g.val.2 (gap X j.val)) 2 Q ∧
            |covariance (fun X => f.val.1 (gap X i.val)) (fun X => g.val.1 (gap X j.val))
                (gibbsMeasure p N) -
              covariance (fun X => f.val.1 (gap X i.val)) (fun X => g.val.1 (gap X j.val)) Q| ≤
              C * Real.exp (-c * (n : ℝ) ^ δ) * derivativeSup f * derivativeSup g) ∧
          (∀ (f : Riesz1.Configuration N → ℝ),
            eLpNorm f 2 Q ≤ ENNReal.ofReal (Real.sqrt 2) * eLpNorm f 2 (gibbsMeasure p N)) := by
  obtain ⟨δ, hδ, h⟩ := arbitrary_set_tilt s η hs hs1 hη
  refine ⟨δ, hδ, fun β hβ θ => ?_⟩
  obtain ⟨C, c, n0, hC, hc, hn0, hb⟩ := h β hβ θ
  refine ⟨C, c, n0, hC, hc, hn0, fun p hps hpβ N n hN _ hn hgeom a => ?_⟩
  have hnN : (n : ℕ) ≤ (N : ℕ) := by
    rcases hgeom with hgeom | rfl
    · omega
    · exact le_rfl
  have hcard := card_cyclicInterval a hnN
  have ht := hb p hps hpβ N hN (cyclicInterval N a n) (by simpa only [hcard] using hn)
  simpa only [hcard] using ht

end Riesz2.DecayLong.ObservableTransfer
