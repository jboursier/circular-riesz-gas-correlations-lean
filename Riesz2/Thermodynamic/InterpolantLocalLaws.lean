/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.InterpolatingDensities
public import Riesz2.Frozen.GoodBlockEvent
public import Riesz2.ToMathlib.MomentEventBounds

/-!
# Weighted exceptional mass for the two-sided tilt

Preparatory estimates for Appendix C. The block event is the `goodBlockEvent`. All
exceptional masses below are nonnegative integrals.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Riesz2.InterpolantLocalLaws

/-- The weight of Subsection 6.1, evaluated by its displayed formula.
Applications to gap laws have strictly positive coordinates. -/
@[expose] def exceptionalWeight (s : ℝ) {n : ℕ+} (x : Fin (n : ℕ) → ℝ) : ℝ :=
  1 + ∑ i, x i ^ (-4 * s - 12)

/-- The exceptional weight is at least one, including at empty exceptional events. -/
theorem one_le_exceptionalWeight (s : ℝ) {n : ℕ+} (x : Fin (n : ℕ) → ℝ) (hx : ∀ i, 0 ≤ x i) :
    1 ≤ exceptionalWeight s x := by
  unfold exceptionalWeight
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hx i) _)

/-- Measurability of the weight on the actual positive-gap carrier. -/
theorem measurable_exceptionalWeight {Ω : Type*} [MeasurableSpace Ω]
    (s : ℝ) {n : ℕ+} (X : Ω → Fin (n : ℕ) → ℝ)
    (hX : ∀ i, Measurable (fun ω => X ω i)) :
    Measurable (fun ω => exceptionalWeight s (X ω)) := by
  exact measurable_const.add (Finset.measurable_sum _ fun i _ => (hX i).pow_const _)

/-- A deterministic square bound used in Appendix C.
Its right side involves precisely the doubled inverse power. -/
theorem exceptionalWeight_sq_le (s : ℝ) {n : ℕ+}
    (x : Fin (n : ℕ) → ℝ) (hx : ∀ i, 0 < x i) :
    exceptionalWeight s x ^ 2 ≤
      2 + 2 * (n : ℝ) * ∑ i, x i ^ (-8 * s - 24) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin (n : ℕ) => (1 : ℝ)) (fun i => x i ^ (-4 * s - 12))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hcs
  have hp (i : Fin (n : ℕ)) : (x i ^ (-4 * s - 12)) ^ 2 = x i ^ (-8 * s - 24) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hx i).le]
    congr 1
    ring
  simp only [hp] at hcs
  dsimp [exceptionalWeight]
  nlinarith [sq_nonneg ((∑ i, x i ^ (-4 * s - 12)) - 1)]

/-- The restriction of the block event to a length simplex is
exactly the rigidity event of Subsection 6.1. No second family of
cutoff events is introduced. -/
theorem goodBlockEvent_on_length (s : ℝ) (n N : ℕ+) (η L : ℝ)
    (hL : L < (N : ℝ)) (x : Fin (n : ℕ) → ℝ) (hx : ∑ i, x i = L) :
    x ∈ goodBlockEvent s n N η ↔
      (∀ i, (n : ℝ) ^ (-η) ≤ x i ∧ x i ≤ (n : ℝ) ^ η) ∧
      ∀ a b : ℕ, a < b → b ≤ (n : ℕ) →
        |(∑ i ∈ Finset.univ.filter (fun i : Fin (n : ℕ) => a ≤ i.val ∧ i.val < b), x i) -
          (b - a : ℕ)| ≤ (n : ℝ) ^ η * (b - a : ℕ) ^ (min s 1 / 2) := by
  simp only [goodBlockEvent, mem_ofPred_eq, hx, hL, true_and]

/-- The rigidity event is Borel, including its strict total-mass bound. -/
theorem measurableSet_goodBlockEvent (s : ℝ) (n N : ℕ+) (η : ℝ) :
    MeasurableSet (goodBlockEvent s n N η) := by
  unfold goodBlockEvent
  simp only [ofPred_and, ofPred_forall]
  measurability

/-- The uniform second moment needed in Appendix C.
It is proved for the physical tilted law in both exponent regimes, and
the constant precedes both sizes and every active coordinate. -/
theorem tilted_weight_second_moment (s β ε : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (hβ : 0 < β) (hε : 0 < ε) (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s → p.val.1 = β →
      ∀ N n : ℕ+, 2 ≤ (N : ℕ) → ∀ hn : (n : ℕ) ≤ (N : ℕ),
        (∫⁻ X, ENNReal.ofReal (exceptionalWeight s (finiteGapBlock (K := n) X) ^ 2)
          ∂tiltedParticleMeasure p N n hn θ ε true) ≤ ENNReal.ofReal (C * (n : ℝ) ^ 2) := by
  obtain ⟨M, hM, hm⟩ := InterpolatingDensities.tilted_gap_moments
    s β ε hs hs1 hβ hε θ (8 * s + 24) (by positivity)
  refine ⟨2 + 2 * M, by positivity, fun p hps hpβ N n hN hn => ?_⟩
  let μ := tiltedParticleMeasure p N n hn θ ε true
  have := (InterpolatingDensities.tilt_valid p N n hn θ ε true).2.2
  have hu (i : Fin (n : ℕ)) :
      (∫⁻ X, ENNReal.ofReal (gap X (i.val : ℤ) ^ (-8 * s - 24)) ∂μ) ≤
        ENNReal.ofReal M := by
    have hi := (le_add_left (le_refl
      (∫⁻ X, ENNReal.ofReal (gap X (i.val : ℤ) ^ (-(8 * s + 24))) ∂μ))).trans
        (hm p hps hpβ N n hN hn i.val)
    simpa only [show -(8 * s + 24) = -8 * s - 24 by ring] using hi
  calc
    _ ≤ ∫⁻ X, ENNReal.ofReal
        (2 + 2 * (n : ℝ) * ∑ i : Fin (n : ℕ), gap X i.val ^ (-8 * s - 24)) ∂μ := by
      apply lintegral_mono
      intro X
      apply ENNReal.ofReal_le_ofReal
      exact exceptionalWeight_sq_le s (finiteGapBlock X) (fun i => Riesz1.gap_pos X i.val)
    _ = ENNReal.ofReal 2 + ENNReal.ofReal (2 * (n : ℝ)) *
        ∑ i : Fin (n : ℕ), ∫⁻ X, ENNReal.ofReal (gap X i.val ^ (-8 * s - 24)) ∂μ := by
      have he (X : Riesz1.Configuration N) : ENNReal.ofReal
          (2 + 2 * (n : ℝ) * ∑ i : Fin (n : ℕ), gap X i.val ^ (-8 * s - 24)) =
          ENNReal.ofReal 2 + ENNReal.ofReal (2 * (n : ℝ)) *
            ∑ i : Fin (n : ℕ), ENNReal.ofReal (gap X i.val ^ (-8 * s - 24)) := by
        have hnn (i : Fin (n : ℕ)) : 0 ≤ gap X i.val ^ (-8 * s - 24) :=
          Real.rpow_nonneg (Riesz1.gap_pos X i.val).le _
        rw [ENNReal.ofReal_add (by norm_num)
          (mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => hnn i)),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg (fun i _ => hnn i)]
      simp_rw [he]
      have hF : Measurable (fun X : Riesz1.Configuration N =>
          ∑ i : Fin (n : ℕ), ENNReal.ofReal (gap X i.val ^ (-8 * s - 24))) :=
        Finset.measurable_sum _ fun i _ =>
          ((show Measurable (fun X : Riesz1.Configuration N => gap X i.val) from
            Riesz1.measurable_gap i.val).pow_const _).ennreal_ofReal
      rw [lintegral_add_left measurable_const, lintegral_const_mul _ hF]
      rw [lintegral_finsetSum _ (fun (i : Fin (n : ℕ)) _ =>
        ((show Measurable (fun X : Riesz1.Configuration N => gap X i.val) from
          Riesz1.measurable_gap i.val).pow_const (-8 * s - 24)).ennreal_ofReal)]
      simp
    _ ≤ ENNReal.ofReal 2 + ENNReal.ofReal (2 * (n : ℝ)) *
        ∑ _ : Fin (n : ℕ), ENNReal.ofReal M := by
      gcongr with i
      exact hu i
    _ = ENNReal.ofReal (2 + 2 * (n : ℝ) ^ 2 * M) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by norm_num) (by positivity)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal ((2 + 2 * M) * (n : ℝ) ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
      nlinarith [sq_nonneg ((n : ℝ) - 1)]

/-- Weighted Cauchy--Schwarz for every exceptional event under the
physical tilt. The second moment and integrability follow from the moment bounds. -/
theorem tilted_weighted_event (s β ε : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (hβ : 0 < β) (hε : 0 < ε) (θ : PhysicalCutoff) :
    ∃ K : ℝ, 0 < K ∧ ∀ p : Parameters, p.val.2 = s → p.val.1 = β →
      ∀ N n : ℕ+, 2 ≤ (N : ℕ) → ∀ hn : (n : ℕ) ≤ (N : ℕ),
      ∀ E : Set (Riesz1.Configuration N), MeasurableSet E →
        (∫⁻ X in E, ENNReal.ofReal (exceptionalWeight s (finiteGapBlock (K := n) X))
          ∂tiltedParticleMeasure p N n hn θ ε true) ≤
          ENNReal.ofReal (K * (n : ℝ) *
            Real.sqrt ((tiltedParticleMeasure p N n hn θ ε true).real E)) := by
  obtain ⟨C, hC, hm⟩ := tilted_weight_second_moment s β ε hs hs1 hβ hε θ
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hC, fun p hps hpβ N n hN hn E hE => ?_⟩
  let μ := tiltedParticleMeasure p N n hn θ ε true
  have : IsProbabilityMeasure μ := (InterpolatingDensities.tilt_valid p N n hn θ ε true).2.2
  let W := fun X : Riesz1.Configuration N => exceptionalWeight s (finiteGapBlock (K := n) X)
  have hW : Measurable W := measurable_exceptionalWeight s _
    (fun i => Riesz1.measurable_gap i.val)
  have hW0 (X : Riesz1.Configuration N) : 0 ≤ W X :=
    zero_le_one.trans (one_le_exceptionalWeight s _ (fun i => (Riesz1.gap_pos X i.val).le))
  have hbound := hm p hps hpβ N n hN hn
  have hWi : Integrable (fun X => W X ^ 2) μ := by
    refine ⟨hW.pow_const 2 |>.aestronglyMeasurable, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun X => sq_nonneg (W X))).mpr
    exact hbound.trans_lt ENNReal.ofReal_lt_top
  have hW1 : Integrable W μ := MomentEvent.integrable_of_integrable_sq hW hWi
  have hreal : (∫ X, W X ^ 2 ∂μ) ≤ C * (n : ℝ) ^ 2 := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ C * (n : ℝ) ^ 2)).mp
    rw [ofReal_integral_eq_lintegral_ofReal hWi
      (Filter.Eventually.of_forall fun X => sq_nonneg (W X))]
    exact hbound
  have hcs := Riesz1.integral_on_event_le_second_moment
    hW.aestronglyMeasurable hW0 hWi hE
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hcs
  have hsqrt : Real.sqrt (∫ X, W X ^ 2 ∂μ) ≤ Real.sqrt C * (n : ℝ) := by
    apply (Real.sqrt_le_sqrt hreal).trans_eq
    rw [Real.sqrt_mul hC.le, Real.sqrt_sq (by positivity : (0 : ℝ) ≤ n)]
  calc
    _ = ENNReal.ofReal (∫ X in E, W X ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal hW1.integrableOn
        (Filter.Eventually.of_forall hW0)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hcs.trans
      (mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _)))

/-- Density comparison for the tilt, assuming a lower bound on the normalizer. -/
theorem internal_tilted_event_le (p : Parameters) (N n : ℕ+)
    (hn : (n : ℕ) ≤ (N : ℕ)) (θ : PhysicalCutoff) (ε : ℝ)
    {z : ℝ} (hz : 0 < z)
    (hZ : z ≤ NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (physicalGapPenalty N n hn θ ε true))
    (E : Set (Riesz1.Configuration N)) (hE : MeasurableSet E) :
    (tiltedParticleMeasure p N n hn θ ε true) E ≤
      ENNReal.ofReal z⁻¹ * (gibbsMeasure p N) E := by
  have hG0 := DecayShort.activeGapPenalty_nonneg (N := N) θ
    (show 0 ≤ (n : ℝ) ^ ε by positivity) true (InterpolatingDensities.activeLabels N n hn)
  rw [InterpolatingDensities.activeGapPenalty_eq] at hG0
  have hnrm : (tiltNormalizer p N n hn θ ε true)⁻¹ ≤ ENNReal.ofReal z⁻¹ := by
    rw [InterpolatingDensities.normalizer_eq, ENNReal.ofReal_inv_of_pos hz]
    exact ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal hZ)
  unfold tiltedParticleMeasure
  rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ hE]
  apply mul_le_mul hnrm
  · calc
      _ ≤ ∫⁻ _ in E, (1 : ℝ≥0∞) ∂gibbsMeasure p N := by
        apply lintegral_mono
        intro X
        exact ENNReal.ofReal_le_one.mpr
          (NonnegativeTilt.exp_neg_mul_le_one p.property.1.le hG0 X)
      _ = (gibbsMeasure p N) E := by simp
  · exact zero_le
  · exact zero_le

/-- The single-gap cutoff part of Appendix C, before
the interval tests. Its stretched-exponential power is fixed before β,
and the physical tilt has the exact two-sided penalty of Subsection 6.1. -/
theorem tilted_coordinate_cutoffs (s ε η : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ β : ℝ, 0 < β → ∀ θ : PhysicalCutoff,
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → p.val.1 = β →
      ∀ N n : ℕ+, 2 ≤ (N : ℕ) → ∀ hn : (n : ℕ) ≤ (N : ℕ),
        (tiltedParticleMeasure p N n hn θ ε true)
          {X | ∃ i : Fin (n : ℕ), gap X i.val < (n : ℝ) ^ (-η) ∨
            (n : ℝ) ^ η < gap X i.val} ≤
          ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ δ)) := by
  let δ := η * min s 1
  have hδ : 0 < δ := mul_pos hη (lt_min hs zero_lt_one)
  refine ⟨δ, hδ, fun β hβ θ => ?_⟩
  obtain ⟨Ct, ct, hCt, hct, ht, _⟩ := SingleGapTails.single_gap_tails
    s β β hs hs1 hβ le_rfl
  obtain ⟨z, _, _, _, hz, _, _, _, hnorm⟩ :=
    InterpolatingDensities.penalty_support_and_normalizer s β ε hs hs1 hβ hε θ
  obtain ⟨B, hB, hb⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := 1) (c := ct) (c' := ct / 2) hδ (by linarith)
  refine ⟨z⁻¹ * (2 * Ct * (B + 1)), ct / 2, by positivity, by positivity, ?_⟩
  intro p hps hpβ N n hN hn
  let E : Set (Riesz1.Configuration N) := {X | ∃ i : Fin (n : ℕ),
    gap X i.val < (n : ℝ) ^ (-η) ∨ (n : ℝ) ^ η < gap X i.val}
  have hE : MeasurableSet E := by
    simp only [E, ofPred_exists]
    apply MeasurableSet.iUnion
    intro i
    exact (measurableSet_lt (show Measurable (fun X : Riesz1.Configuration N => gap X i.val)
      from Riesz1.measurable_gap i.val) measurable_const).union
      (measurableSet_lt measurable_const (Riesz1.measurable_gap i.val))
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by positivity
  have hlow : (n : ℝ) ^ (-η) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  have hupp : 1 ≤ (n : ℝ) ^ η := Real.one_le_rpow hn1 hη.le
  have hbase : (gibbsMeasure p N) E ≤
      ENNReal.ofReal (2 * Ct * ((n : ℝ) * Real.exp (-ct * (n : ℝ) ^ δ))) := by
    have hi (i : Fin (n : ℕ)) : (gibbsMeasure p N)
        {X | gap X i.val < (n : ℝ) ^ (-η) ∨ (n : ℝ) ^ η < gap X i.val} ≤
        ENNReal.ofReal (2 * Ct * Real.exp (-ct * (n : ℝ) ^ δ)) := by
      obtain ⟨hl, hu⟩ := ht p hps (by rw [hpβ]) (by rw [hpβ]) N hN i.val
      have hl' := hl ((n : ℝ) ^ (-η)) (by positivity) hlow
      have hu' := hu ((n : ℝ) ^ η) hupp
      have hp1 : (n : ℝ) ^ δ ≤ (n : ℝ) ^ η :=
        Real.rpow_le_rpow_of_exponent_le hn1 (mul_le_of_le_one_right hη.le (min_le_right _ _))
      have hp2 : (n : ℝ) ^ δ ≤ ((n : ℝ) ^ (-η)) ^ (-s) := by
        rw [← Real.rpow_mul hn0.le]
        apply Real.rpow_le_rpow_of_exponent_le hn1
        dsimp [δ]
        nlinarith [min_le_left s 1]
      calc
        _ ≤ (gibbsMeasure p N) {X | gap X i.val ≤ (n : ℝ) ^ (-η)} +
            (gibbsMeasure p N) {X | (n : ℝ) ^ η ≤ gap X i.val} := by
          apply (measure_mono (show {X | gap X i.val < (n : ℝ) ^ (-η) ∨
            (n : ℝ) ^ η < gap X i.val} ⊆ _ from fun X h =>
              h.elim (fun h => Or.inl h.le) (fun h => Or.inr h.le))).trans
          exact measure_union_le _ _
        _ ≤ ENNReal.ofReal (Ct * Real.exp (-ct * ((n : ℝ) ^ (-η)) ^ (-s))) +
            ENNReal.ofReal (Ct * Real.exp (-ct * (n : ℝ) ^ η)) := add_le_add hl' hu'
        _ ≤ ENNReal.ofReal (Ct * Real.exp (-ct * (n : ℝ) ^ δ)) +
            ENNReal.ofReal (Ct * Real.exp (-ct * (n : ℝ) ^ δ)) := by
          apply add_le_add <;> apply ENNReal.ofReal_le_ofReal <;>
            apply mul_le_mul_of_nonneg_left _ hCt.le <;>
            apply Real.exp_le_exp.mpr
          · nlinarith
          · nlinarith
        _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
    calc
      _ ≤ ∑ i : Fin (n : ℕ), (gibbsMeasure p N)
          {X | gap X i.val < (n : ℝ) ^ (-η) ∨ (n : ℝ) ^ η < gap X i.val} :=
        by simpa only [E, ofPred_exists, tsum_fintype] using
          measure_iUnion_le (μ := gibbsMeasure p N) (fun i : Fin (n : ℕ) =>
            {X | gap X i.val < (n : ℝ) ^ (-η) ∨ (n : ℝ) ^ η < gap X i.val})
      _ ≤ ∑ _ : Fin (n : ℕ), ENNReal.ofReal (2 * Ct * Real.exp (-ct * (n : ℝ) ^ δ)) :=
        Finset.sum_le_sum (fun i _ => hi i)
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
  apply (internal_tilted_event_le p N n hn θ ε hz (hnorm p hps hpβ N n hN hn).2 E hE).trans
  apply (mul_le_mul_of_nonneg_left hbase zero_le).trans
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hh := hb (n : ℝ) hn1
  rw [Real.rpow_one] at hh
  have hmul := mul_le_mul_of_nonneg_left hh (show 0 ≤ z⁻¹ * (2 * Ct) by positivity)
  have hpos : 0 < z⁻¹ * (2 * Ct) * Real.exp (-(ct / 2) * (n : ℝ) ^ δ) := by positivity
  nlinarith

/-- The weighted single-gap cutoff estimate in
Appendix C. The exponent is temperature independent. -/
theorem tilted_weighted_coordinate_cutoffs (s ε η : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ β : ℝ, 0 < β → ∀ θ : PhysicalCutoff,
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → p.val.1 = β →
      ∀ N n : ℕ+, 2 ≤ (N : ℕ) → ∀ hn : (n : ℕ) ≤ (N : ℕ),
        (∫⁻ X in {X | ∃ i : Fin (n : ℕ), gap X i.val < (n : ℝ) ^ (-η) ∨
            (n : ℝ) ^ η < gap X i.val},
          ENNReal.ofReal (exceptionalWeight s (finiteGapBlock (K := n) X))
          ∂tiltedParticleMeasure p N n hn θ ε true) ≤
          ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ δ)) := by
  obtain ⟨δ, hδ, htail⟩ := tilted_coordinate_cutoffs s ε η hs hs1 hε hη
  refine ⟨δ, hδ, fun β hβ θ => ?_⟩
  obtain ⟨Ct, ct, hCt, hct, ht⟩ := htail β hβ θ
  obtain ⟨K, hK, hw⟩ := tilted_weighted_event s β ε hs hs1 hβ hε θ
  obtain ⟨B, hB, hb⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := 1) (c := ct / 2) (c' := ct / 4) hδ (by linarith)
  refine ⟨K * Real.sqrt Ct * (B + 1), ct / 4, by positivity, by positivity, ?_⟩
  intro p hps hpβ N n hN hn
  let μ := tiltedParticleMeasure p N n hn θ ε true
  let E : Set (Riesz1.Configuration N) := {X | ∃ i : Fin (n : ℕ),
    gap X i.val < (n : ℝ) ^ (-η) ∨ (n : ℝ) ^ η < gap X i.val}
  have hE : MeasurableSet E := by
    simp only [E, ofPred_exists]
    apply MeasurableSet.iUnion
    intro i
    exact (measurableSet_lt (show Measurable (fun X : Riesz1.Configuration N => gap X i.val)
      from Riesz1.measurable_gap i.val) measurable_const).union
      (measurableSet_lt measurable_const (Riesz1.measurable_gap i.val))
  have ht' : μ.real E ≤ Ct * Real.exp (-ct * (n : ℝ) ^ δ) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) (ht p hps hpβ N n hN hn)
  have hsqrt : Real.sqrt (μ.real E) ≤
      Real.sqrt Ct * Real.exp (-(ct / 2) * (n : ℝ) ^ δ) := by
    apply (Real.sqrt_le_sqrt ht').trans_eq
    rw [Real.sqrt_mul hCt.le, Real.sqrt_eq_rpow (Real.exp _), ← Real.exp_mul]
    congr 2
    ring
  refine (hw p hps hpβ N n hN hn E hE).trans (ENNReal.ofReal_le_ofReal ?_)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hpoly := hb (n : ℝ) hn1
  rw [Real.rpow_one] at hpoly
  calc
    _ ≤ K * (n : ℝ) * (Real.sqrt Ct * Real.exp (-(ct / 2) * (n : ℝ) ^ δ)) :=
      mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = K * Real.sqrt Ct * ((n : ℝ) * Real.exp (-(ct / 2) * (n : ℝ) ^ δ)) := by ring
    _ ≤ K * Real.sqrt Ct * (B * Real.exp (-(ct / 4) * (n : ℝ) ^ δ)) :=
      mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ ≤ _ := by
      nlinarith [show 0 < K * Real.sqrt Ct * Real.exp (-(ct / 4) * (n : ℝ) ^ δ) by positivity]

end Riesz2.InterpolantLocalLaws
