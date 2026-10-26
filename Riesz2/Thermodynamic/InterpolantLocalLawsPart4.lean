/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.InterpolantLocalLawsPart3
public import Mathlib.Analysis.PSeries
public import Riesz1.Rigidity.RigidityGapsSplit

/-!
# Full-law local laws and exterior prefix and suffix geometry

Completion of Appendix C, using the literal physical two-sided tilt and compact
temperature intervals.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Riesz2.InterpolantLocalLaws

/-- The vanishing interval of the physical cutoff permits every power at
least two as a global upper bound on the positive half-line. -/
theorem cutoff_power_bound (θ : PhysicalCutoff) {r : ℝ} (hr : 2 ≤ r) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 0 ≤ t → θ.val t ≤ K * t ^ r := by
  obtain ⟨A, hA, hθ⟩ := θ.exists_sq_bound
  refine ⟨(A + 1) * 2 ^ r, by positivity, fun t ht => ?_⟩
  by_cases hsmall : t ≤ 1 / 2
  · rw [θ.property.2.2.2.1 t ⟨ht, hsmall⟩]
    positivity
  · have ht0 : 0 < t := by linarith
    have h2t : 1 ≤ 2 * t := by linarith
    have hp := Real.rpow_le_rpow_of_exponent_le h2t hr
    rw [Real.rpow_two, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ht] at hp
    have hpow : t ^ 2 ≤ 2 ^ r * t ^ r := by nlinarith [sq_nonneg t]
    exact (hθ t ht).trans (by
      have := mul_le_mul_of_nonneg_left hpow hA
      have := Real.rpow_nonneg ht r
      nlinarith [show (0 : ℝ) ≤ 2 ^ r by positivity])

/-- Compact-temperature normalization for the penalty in Subsection 6.1.
A high moment controls the mean penalty uniformly even at bounded sizes. Jensen therefore gives a positive lower bound before both sizes and β. -/
theorem compact_tilt_normalizer (s ε βlo βhi : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (hε : 0 < ε) (hlo : 0 < βlo) (hle : βlo ≤ βhi) (θ : PhysicalCutoff) :
    ∃ z : ℝ, 0 < z ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ N n : ℕ+, 2 ≤ (N : ℕ) →
      ∀ hn : (n : ℕ) ≤ (N : ℕ),
        z ≤ NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
          (physicalGapPenalty N n hn θ ε true) := by
  let r := 2 + 1 / ε
  have hr : 2 ≤ r := by dsimp [r]; linarith [div_pos zero_lt_one hε]
  have hr0 : 0 < r := by linarith
  obtain ⟨K, hK, hθ⟩ := cutoff_power_bound θ hr
  obtain ⟨D, hD, hm⟩ := SingleGapTails.single_gap_moment_integrals
    s βlo βhi hs hs1 hlo hle r hr0
  refine ⟨Real.exp (-βhi * (K * D)), Real.exp_pos _, ?_⟩
  intro p hps hpl hph N n hN hn
  have := gibbsMeasure_probability p N
  let μ := gibbsMeasure p N
  let a := K * (n : ℝ) ^ (-ε * r)
  let H := fun X : Riesz1.Configuration N =>
    a * ∑ i : Fin (n : ℕ), (gap X i.val ^ r + gap X i.val ^ (-r))
  have hi (i : Fin (n : ℕ)) := hm p hps hpl hph N hN i.val
  have hHi : Integrable H μ :=
    (integrable_finsetSum _ fun i _ => (hi i).1.add (hi i).2.1).const_mul a
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hH0 (X : Riesz1.Configuration N) : 0 ≤ H X := by
    dsimp [H]; exact mul_nonneg ha (Finset.sum_nonneg fun i _ => by
      exact add_nonneg (Real.rpow_nonneg (Riesz1.gap_pos X i.val).le _)
        (Real.rpow_nonneg (Riesz1.gap_pos X i.val).le _))
  have hpoint (X : Riesz1.Configuration N) :
      physicalGapPenalty N n hn θ ε true X ≤ H X := by
    unfold physicalGapPenalty H
    simp only [↓reduceIte]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hx : 0 < gap X i.val := Riesz1.gap_pos X i.val
    have hp := hθ ((n : ℝ) ^ (-ε) * gap X i.val) (by positivity)
    have hq := hθ ((n : ℝ) ^ (-ε) * (gap X i.val)⁻¹) (by positivity)
    rw [Real.mul_rpow (by positivity) hx.le, ← Real.rpow_mul (by positivity)] at hp
    rw [Real.mul_rpow (by positivity) (inv_nonneg.mpr hx.le),
      ← Real.rpow_mul (by positivity), Real.inv_rpow hx.le, ← Real.rpow_neg hx.le] at hq
    change θ.val ((n : ℝ) ^ (-ε) * gap X i.val) +
      θ.val ((n : ℝ) ^ (-ε) * (gap X i.val)⁻¹) ≤ _
    dsimp [a]
    nlinarith
  have hG := DecayShort.activeGapPenalty_measurable (N := N) θ
    (show 0 ≤ (n : ℝ) ^ ε by positivity) true (InterpolatingDensities.activeLabels N n hn)
  have hG0 := DecayShort.activeGapPenalty_nonneg (N := N) θ
    (show 0 ≤ (n : ℝ) ^ ε by positivity) true (InterpolatingDensities.activeLabels N n hn)
  rw [InterpolatingDensities.activeGapPenalty_eq] at hG hG0
  have hGi : Integrable (physicalGapPenalty N n hn θ ε true) μ :=
    hHi.mono' hG.aestronglyMeasurable (Filter.Eventually.of_forall fun X => by
      rw [Real.norm_of_nonneg (hG0 X)]; exact hpoint X)
  have hmean : (∫ X, physicalGapPenalty N n hn θ ε true X ∂μ) ≤ K * D := by
    have hmi (i : Fin (n : ℕ)) :
        (∫ X, gap X i.val ^ r + gap X i.val ^ (-r) ∂μ) ≤ D := by
      rw [integral_add (hi i).1 (hi i).2.1]
      apply (ENNReal.ofReal_le_ofReal_iff hD.le).mp
      have hp0 (X : Riesz1.Configuration N) : 0 ≤ gap X i.val ^ r :=
        Real.rpow_nonneg (show 0 ≤ gap X i.val from (Riesz1.gap_pos X _).le) _
      have hn0 (X : Riesz1.Configuration N) : 0 ≤ gap X i.val ^ (-r) :=
        Real.rpow_nonneg (show 0 ≤ gap X i.val from (Riesz1.gap_pos X _).le) _
      rw [ENNReal.ofReal_add (integral_nonneg hp0) (integral_nonneg hn0),
        ofReal_integral_eq_lintegral_ofReal (hi i).1
          (Filter.Eventually.of_forall hp0),
        ofReal_integral_eq_lintegral_ofReal (hi i).2.1
          (Filter.Eventually.of_forall hn0)]
      exact (hi i).2.2
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
    have hscale : (n : ℝ) * (n : ℝ) ^ (-ε * r) ≤ 1 := by
      conv_lhs => lhs; rw [← Real.rpow_one (n : ℝ)]
      rw [← Real.rpow_add (by positivity)]
      apply Real.rpow_le_one_of_one_le_of_nonpos hn1
      dsimp [r]
      have he := div_mul_cancel₀ (1 : ℝ) hε.ne'
      nlinarith
    calc
      _ ≤ ∫ X, H X ∂μ := integral_mono hGi hHi hpoint
      _ = a * ∑ i : Fin (n : ℕ), ∫ X, gap X i.val ^ r + gap X i.val ^ (-r) ∂μ := by
        dsimp only [H]
        rw [integral_const_mul]
        congr 1
        exact integral_finsetSum Finset.univ (f := fun (i : Fin (n : ℕ)) (X : Riesz1.Configuration N) => gap X i.val ^ r + gap X i.val ^ (-r))
          (fun i _ => (hi i).1.add (hi i).2.1)
      _ ≤ a * ∑ _ : Fin (n : ℕ), D :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hmi i) ha
      _ ≤ K * D := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        dsimp [a]
        nlinarith [mul_le_mul_of_nonneg_right hscale (mul_nonneg hK.le hD.le)]
  have hj := NonnegativeTilt.exp_neg_mul_integral_le_expTiltNormalizer hG
    p.property.1.le hG0 hGi
  apply le_trans (Real.exp_le_exp.mpr ?_) hj
  have := mul_le_mul_of_nonneg_left hmean p.property.1.le
  have := mul_le_mul_of_nonneg_right hph (mul_nonneg hK.le hD.le)
  linarith

/-- Compact-temperature moment bounds for the literal two-sided tilt,
used in Appendix C. -/
theorem compact_tilted_gap_moments (s ε βlo βhi : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (hε : 0 < ε) (hlo : 0 < βlo) (hle : βlo ≤ βhi) (θ : PhysicalCutoff) (r : ℝ) (hr : 0 < r) :
    ∃ M : ℝ, 0 < M ∧ ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ N n : ℕ+, 2 ≤ (N : ℕ) → ∀ hn : (n : ℕ) ≤ (N : ℕ), ∀ j : ℤ,
        (∫⁻ X, ENNReal.ofReal (gap X j ^ r) ∂tiltedParticleMeasure p N n hn θ ε true) +
          (∫⁻ X, ENNReal.ofReal (gap X j ^ (-r)) ∂tiltedParticleMeasure p N n hn θ ε true) ≤
            ENNReal.ofReal M := by
  obtain ⟨z, hz, hrate⟩ := compact_tilt_normalizer s ε βlo βhi hs hs1 hε hlo hle θ
  obtain ⟨D, hD, hm⟩ := SingleGapTails.single_gap_moment_integrals s βlo βhi hs hs1 hlo hle r hr
  refine ⟨z⁻¹ * D, mul_pos (inv_pos.mpr hz) hD, fun p hps hpl hph N n hN hn j => ?_⟩
  have := gibbsMeasure_probability p N
  have hR : 0 ≤ (n : ℝ) ^ ε := by positivity
  have hG := DecayShort.activeGapPenalty_measurable (N := N) θ hR true (InterpolatingDensities.activeLabels N n hn)
  have hG0 := DecayShort.activeGapPenalty_nonneg (N := N) θ hR true (InterpolatingDensities.activeLabels N n hn)
  have hZ := hrate p hps hpl hph N n hN hn
  rw [← InterpolatingDensities.activeGapPenalty_eq] at hZ
  have hp := NonnegativeTilt.lintegral_expTilt_le (μ := gibbsMeasure p N) hG p.property.1.le hG0
    (((Riesz1.measurable_gap j).pow_const r).ennreal_ofReal)
  have hi := NonnegativeTilt.lintegral_expTilt_le (μ := gibbsMeasure p N) hG p.property.1.le hG0
    (((Riesz1.measurable_gap j).pow_const (-r)).ennreal_ofReal)
  rw [← InterpolatingDensities.activeTilt_eq, DecayShort.activeTilt]
  apply (add_le_add hp hi).trans
  rw [← mul_add, NonnegativeTilt.lintegral_normalizer_eq hG p.property.1.le hG0,
    ENNReal.ofReal_mul (inv_nonneg.mpr hz.le)]
  apply mul_le_mul
  · rw [ENNReal.ofReal_inv_of_pos hz]
    exact ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal hZ)
  · exact (hm p hps hpl hph N hN j).2.2
  · exact zero_le
  · exact zero_le

/-- The second moment of the exceptional weight, uniformly on compact
positive temperature intervals (Appendix C). -/
theorem compact_tilted_weight_second_moment (s ε βlo βhi : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (hε : 0 < ε) (hlo : 0 < βlo) (hle : βlo ≤ βhi) (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ N n : ℕ+, 2 ≤ (N : ℕ) → ∀ hn : (n : ℕ) ≤ (N : ℕ),
        (∫⁻ X, ENNReal.ofReal (exceptionalWeight s (finiteGapBlock (K := n) X) ^ 2)
          ∂tiltedParticleMeasure p N n hn θ ε true) ≤ ENNReal.ofReal (C * (n : ℝ) ^ 2) := by
  obtain ⟨M, hM, hm⟩ := compact_tilted_gap_moments
    s ε βlo βhi hs hs1 hε hlo hle θ (8 * s + 24) (by positivity)
  refine ⟨2 + 2 * M, by positivity, fun p hps hpl hph N n hN hn => ?_⟩
  let μ := tiltedParticleMeasure p N n hn θ ε true
  have := (InterpolatingDensities.tilt_valid p N n hn θ ε true).2.2
  have hu (i : Fin (n : ℕ)) :
      (∫⁻ X, ENNReal.ofReal (gap X (i.val : ℤ) ^ (-8 * s - 24)) ∂μ) ≤
        ENNReal.ofReal M := by
    have hi := (le_add_left (le_refl
      (∫⁻ X, ENNReal.ofReal (gap X (i.val : ℤ) ^ (-(8 * s + 24))) ∂μ))).trans
        (hm p hps hpl hph N n hN hn i.val)
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
theorem compact_tilted_weighted_event (s ε βlo βhi : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (hε : 0 < ε) (hlo : 0 < βlo) (hle : βlo ≤ βhi) (θ : PhysicalCutoff) :
    ∃ K : ℝ, 0 < K ∧ ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ N n : ℕ+, 2 ≤ (N : ℕ) → ∀ hn : (n : ℕ) ≤ (N : ℕ),
      ∀ E : Set (Riesz1.Configuration N), MeasurableSet E →
        (∫⁻ X in E, ENNReal.ofReal (exceptionalWeight s (finiteGapBlock (K := n) X))
          ∂tiltedParticleMeasure p N n hn θ ε true) ≤
          ENNReal.ofReal (K * (n : ℝ) *
            Real.sqrt ((tiltedParticleMeasure p N n hn θ ε true).real E)) := by
  obtain ⟨C, hC, hm⟩ := compact_tilted_weight_second_moment s ε βlo βhi hs hs1 hε hlo hle θ
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hC, fun p hps hpl hph N n hN hn E hE => ?_⟩
  let μ := tiltedParticleMeasure p N n hn θ ε true
  have : IsProbabilityMeasure μ := (InterpolatingDensities.tilt_valid p N n hn θ ε true).2.2
  let W := fun X : Riesz1.Configuration N => exceptionalWeight s (finiteGapBlock (K := n) X)
  have hW : Measurable W := measurable_exceptionalWeight s _
    (fun i => Riesz1.measurable_gap i.val)
  have hW0 (X : Riesz1.Configuration N) : 0 ≤ W X :=
    zero_le_one.trans (one_le_exceptionalWeight s _ (fun i => (Riesz1.gap_pos X i.val).le))
  have hbound := hm p hps hpl hph N n hN hn
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

/-- The weighted clause of Appendix C, with prefactors
chosen uniformly on every compact positive temperature interval. -/
theorem compact_full_law_weighted_rigidity (hRig : External.LongRangeRigidityLocallyUniform)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ ηstar astar : ℝ, 0 < ηstar ∧ 0 < astar ∧
      ∀ η : ℝ, 0 < η → η ≤ ηstar → ∀ ε : ℝ, 0 < ε →
      ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
        ∀ N n : ℕ+, 2 ≤ (n : ℕ) → 4 * (n : ℕ) ≤ (N : ℕ) →
          (n : ℝ) ^ (2 / s) ≤ (N : ℝ) → ∀ hn : (n : ℕ) ≤ (N : ℕ),
          (∫⁻ X in {X | finiteGapBlock X ∉ goodBlockEvent s n N η},
            ENNReal.ofReal (exceptionalWeight s (finiteGapBlock (K := n) X))
            ∂tiltedParticleMeasure p N n hn θ ε true) ≤
            ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ (astar * η))) := by
  let u := (1 - min s 1 / 2) / 4
  let a := min (min s 1) (u / (4 * (4 * (s + 2))))
  have hu : 0 < u := by dsimp [u]; linarith [min_le_right s 1]
  have ha : 0 < a := by dsimp [a]; exact lt_min (lt_min hs zero_lt_one) (by positivity)
  refine ⟨min (1 / 4) u, a, lt_min (by norm_num) hu, ha, ?_⟩
  intro η hη hηstar ε hε βlo βhi hlo hle θ
  have hη1 : η ≤ 1 / 4 := hηstar.trans (min_le_left _ _)
  have hηu : η / 2 ≤ (1 - min s 1 / 2) / 4 := by
    have hh := hηstar.trans (min_le_right _ _)
    dsimp [u] at hh
    linarith
  obtain ⟨Ct, ct, hCt, hct, ht⟩ := physical_goodBlock_probability hRig s hs hs1
    hη hη1 hηu βlo βhi hlo hle
  obtain ⟨z, hz, hnorm⟩ := compact_tilt_normalizer s ε βlo βhi hs hs1 hε hlo hle θ
  obtain ⟨K, hK, hw⟩ := compact_tilted_weighted_event s ε βlo βhi hs hs1 hε hlo hle θ
  let δ := a * η
  have hδ : 0 < δ := mul_pos ha hη
  obtain ⟨B, hB, hb⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := 1) (c := ct / 2) (c' := ct / 4) hδ (by linarith)
  refine ⟨K * Real.sqrt (z⁻¹ * Ct) * (B + 1), ct / 4, by positivity, by positivity, ?_⟩
  intro p hps hpl hph N n hn2 hsize _ hn
  have hN : 2 ≤ (N : ℕ) := by omega
  have hnN : (n : ℕ) ≤ (N : ℕ) / 2 := by omega
  let μ := tiltedParticleMeasure p N n hn θ ε true
  let E : Set (Riesz1.Configuration N) := {X | finiteGapBlock X ∉ goodBlockEvent s n N η}
  have hfinite : Measurable (finiteGapBlock (N := N) (K := n)) :=
    measurable_pi_iff.mpr (fun i => Riesz1.measurable_gap i.val)
  have hE : MeasurableSet E := (measurableSet_goodBlockEvent s n N η).compl.preimage hfinite
  have hbase : (gibbsMeasure p N) E ≤ ENNReal.ofReal (Ct * Real.exp (-ct * (n : ℝ) ^ δ)) := by
    simpa only [δ, a, u, mul_comm η] using
      ht p hps hpl hph N n hN hn2 hnN
  have htail : μ E ≤ ENNReal.ofReal (z⁻¹ * Ct * Real.exp (-ct * (n : ℝ) ^ δ)) := by
    apply (internal_tilted_event_le p N n hn θ ε hz
      (hnorm p hps hpl hph N n hN hn) E hE).trans
    apply (mul_le_mul_of_nonneg_left hbase zero_le).trans_eq
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  have ht' : μ.real E ≤ z⁻¹ * Ct * Real.exp (-ct * (n : ℝ) ^ δ) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) htail
  have hsqrt : Real.sqrt (μ.real E) ≤
      Real.sqrt (z⁻¹ * Ct) * Real.exp (-(ct / 2) * (n : ℝ) ^ δ) := by
    apply (Real.sqrt_le_sqrt ht').trans_eq
    rw [Real.sqrt_mul (by positivity : 0 ≤ z⁻¹ * Ct),
      Real.sqrt_eq_rpow (Real.exp _), ← Real.exp_mul]
    congr 2
    ring
  refine (hw p hps hpl hph N n hN hn E hE).trans (ENNReal.ofReal_le_ofReal ?_)
  have hpoly := hb (n : ℝ) (show 1 ≤ (n : ℝ) by exact_mod_cast n.pos)
  rw [Real.rpow_one] at hpoly
  calc
    _ ≤ K * (n : ℝ) * (Real.sqrt (z⁻¹ * Ct) * Real.exp (-(ct / 2) * (n : ℝ) ^ δ)) :=
      mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = K * Real.sqrt (z⁻¹ * Ct) * ((n : ℝ) * Real.exp (-(ct / 2) * (n : ℝ) ^ δ)) := by ring
    _ ≤ K * Real.sqrt (z⁻¹ * Ct) * (B * Real.exp (-(ct / 4) * (n : ℝ) ^ δ)) :=
      mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ ≤ _ := by
      nlinarith [show 0 < K * Real.sqrt (z⁻¹ * Ct) * Real.exp (-(ct / 4) * (n : ℝ) ^ δ)
        by positivity]

/-- The display equation (C.2) of the paper, in the short-range
regime: every `0 < η < 1/4`, with the tail power chosen before η and the
constants uniform on each compact positive temperature interval. -/
theorem short_full_law_weighted_rigidity (hRig : External.LongRangeRigidityLocallyUniform)
    (s : ℝ) (hs : 1 < s) :
    ∃ astar : ℝ, 0 < astar ∧
      ∀ η : ℝ, 0 < η → η < 1 / 4 → ∀ ε : ℝ, 0 < ε →
      ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
        ∀ N n : ℕ+, 2 ≤ (n : ℕ) → 4 * (n : ℕ) ≤ (N : ℕ) →
          (n : ℝ) ^ (2 / s) ≤ (N : ℝ) → ∀ hn : (n : ℕ) ≤ (N : ℕ),
          (∫⁻ X in {X | finiteGapBlock X ∉ goodBlockEvent s n N η},
            ENNReal.ofReal (exceptionalWeight s (finiteGapBlock (K := n) X))
            ∂tiltedParticleMeasure p N n hn θ ε true) ≤
            ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ (astar * η))) := by
  have hs0 : 0 < s := by linarith
  have hs1 : s ≠ 1 := ne_of_gt hs
  let u := (1 - min s 1 / 2) / 4
  let a := min (min s 1) (u / (4 * (4 * (s + 2))))
  have hu : 0 < u := by dsimp [u]; linarith [min_le_right s 1]
  have ha : 0 < a := by dsimp [a]; exact lt_min (lt_min hs0 zero_lt_one) (by positivity)
  refine ⟨a, ha, ?_⟩
  intro η hη hηstar ε hε βlo βhi hlo hle θ
  have hη1 : η ≤ 1 / 4 := hηstar.le
  have hηu : η / 2 ≤ (1 - min s 1 / 2) / 4 := by
    rw [min_eq_right hs.le]
    linarith
  obtain ⟨Ct, ct, hCt, hct, ht⟩ := physical_goodBlock_probability hRig s hs0 hs1
    hη hη1 hηu βlo βhi hlo hle
  obtain ⟨z, hz, hnorm⟩ := compact_tilt_normalizer s ε βlo βhi hs0 hs1 hε hlo hle θ
  obtain ⟨K, hK, hw⟩ := compact_tilted_weighted_event s ε βlo βhi hs0 hs1 hε hlo hle θ
  let δ := a * η
  have hδ : 0 < δ := mul_pos ha hη
  obtain ⟨B, hB, hb⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := 1) (c := ct / 2) (c' := ct / 4) hδ (by linarith)
  refine ⟨K * Real.sqrt (z⁻¹ * Ct) * (B + 1), ct / 4, by positivity, by positivity, ?_⟩
  intro p hps hpl hph N n hn2 hsize _ hn
  have hN : 2 ≤ (N : ℕ) := by omega
  have hnN : (n : ℕ) ≤ (N : ℕ) / 2 := by omega
  let μ := tiltedParticleMeasure p N n hn θ ε true
  let E : Set (Riesz1.Configuration N) := {X | finiteGapBlock X ∉ goodBlockEvent s n N η}
  have hfinite : Measurable (finiteGapBlock (N := N) (K := n)) :=
    measurable_pi_iff.mpr (fun i => Riesz1.measurable_gap i.val)
  have hE : MeasurableSet E := (measurableSet_goodBlockEvent s n N η).compl.preimage hfinite
  have hbase : (gibbsMeasure p N) E ≤ ENNReal.ofReal (Ct * Real.exp (-ct * (n : ℝ) ^ δ)) := by
    simpa only [δ, a, u, mul_comm η] using
      ht p hps hpl hph N n hN hn2 hnN
  have htail : μ E ≤ ENNReal.ofReal (z⁻¹ * Ct * Real.exp (-ct * (n : ℝ) ^ δ)) := by
    apply (internal_tilted_event_le p N n hn θ ε hz
      (hnorm p hps hpl hph N n hN hn) E hE).trans
    apply (mul_le_mul_of_nonneg_left hbase zero_le).trans_eq
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  have ht' : μ.real E ≤ z⁻¹ * Ct * Real.exp (-ct * (n : ℝ) ^ δ) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) htail
  have hsqrt : Real.sqrt (μ.real E) ≤
      Real.sqrt (z⁻¹ * Ct) * Real.exp (-(ct / 2) * (n : ℝ) ^ δ) := by
    apply (Real.sqrt_le_sqrt ht').trans_eq
    rw [Real.sqrt_mul (by positivity : 0 ≤ z⁻¹ * Ct),
      Real.sqrt_eq_rpow (Real.exp _), ← Real.exp_mul]
    congr 2
    ring
  refine (hw p hps hpl hph N n hN hn E hE).trans (ENNReal.ofReal_le_ofReal ?_)
  have hpoly := hb (n : ℝ) (show 1 ≤ (n : ℝ) by exact_mod_cast n.pos)
  rw [Real.rpow_one] at hpoly
  calc
    _ ≤ K * (n : ℝ) * (Real.sqrt (z⁻¹ * Ct) * Real.exp (-(ct / 2) * (n : ℝ) ^ δ)) :=
      mul_le_mul_of_nonneg_left hsqrt (by positivity)
    _ = K * Real.sqrt (z⁻¹ * Ct) * ((n : ℝ) * Real.exp (-(ct / 2) * (n : ℝ) ^ δ)) := by ring
    _ ≤ K * Real.sqrt (z⁻¹ * Ct) * (B * Real.exp (-(ct / 4) * (n : ℝ) ^ δ)) :=
      mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ ≤ _ := by
      nlinarith [show 0 < K * Real.sqrt (z⁻¹ * Ct) * Real.exp (-(ct / 4) * (n : ℝ) ^ δ)
        by positivity]

/-- A finite tail of a stretched exponential is bounded independently of
its upper endpoint. Summability is proved using a positive power-series
majorant, so no totalized infinite sum enters the estimate. -/
theorem stretched_exponential_sum {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 1 ≤ n → ∀ S : Finset ℕ,
      (∀ k ∈ S, n ≤ k) →
      (∑ k ∈ S, Real.exp (-c * (k : ℝ) ^ d)) ≤
        B * Real.exp (-(c / 2) * (n : ℝ) ^ d) := by
  classical
  obtain ⟨A, hA, hb⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := 2) (c := c / 2) (c' := c / 4) hd (by linarith)
  let f := fun k : ℕ => (k : ℝ) ^ (-2 : ℝ)
  have hf : Summable f := Real.summable_nat_rpow.mpr (by norm_num)
  have hf0 (k : ℕ) : 0 ≤ f k := Real.rpow_nonneg (Nat.cast_nonneg _) _
  let T := ∑' k, f k
  have hT : 0 ≤ T := tsum_nonneg hf0
  refine ⟨(A + 1) * (T + 1), by positivity, fun n hn S hS => ?_⟩
  have ht (k : ℕ) (hk : k ∈ S) :
      Real.exp (-c * (k : ℝ) ^ d) ≤
        (A * Real.exp (-(c / 2) * (n : ℝ) ^ d)) * f k := by
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (hn.trans (hS k hk))
    have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk1
    have hpow : (n : ℝ) ^ d ≤ (k : ℝ) ^ d :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hS k hk) hd.le
    have hab := hb (k : ℝ) hk1
    have hexp : Real.exp (-(c / 4) * (k : ℝ) ^ d) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    have hbound : Real.exp (-(c / 2) * (k : ℝ) ^ d) ≤ A * f k := by
      have hmul : (k : ℝ) ^ (2 : ℝ) * Real.exp (-(c / 2) * (k : ℝ) ^ d) ≤ A :=
        hab.trans (by nlinarith)
      have heq : (k : ℝ) ^ (2 : ℝ) * f k = 1 := by
        dsimp [f]
        rw [← Real.rpow_add hk0]
        norm_num
      nlinarith [Real.rpow_pos_of_pos hk0 (2 : ℝ)]
    calc
      _ = Real.exp (-(c / 2) * (k : ℝ) ^ d) *
          Real.exp (-(c / 2) * (k : ℝ) ^ d) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (-(c / 2) * (n : ℝ) ^ d) * (A * f k) :=
        mul_le_mul (Real.exp_le_exp.mpr (by nlinarith)) hbound
          (Real.exp_pos _).le (Real.exp_pos _).le
      _ = _ := by ring
  calc
    _ ≤ ∑ k ∈ S, (A * Real.exp (-(c / 2) * (n : ℝ) ^ d)) * f k :=
      Finset.sum_le_sum ht
    _ = (A * Real.exp (-(c / 2) * (n : ℝ) ^ d)) * ∑ k ∈ S, f k := by rw [Finset.mul_sum]
    _ ≤ (A * Real.exp (-(c / 2) * (n : ℝ) ^ d)) * T :=
      mul_le_mul_of_nonneg_left (hf.sum_le_tsum S (fun k _ => hf0 k)) (by positivity)
    _ ≤ _ := by nlinarith [Real.exp_pos (-(c / 2) * (n : ℝ) ^ d)]

/-- Internal half-volume estimate for arbitrary labels measured from an endpoint. Short
ranks use the finite grid. Long ranks use the convergent infinite tail
majorant. This is the exterior-sum step of Appendix C. -/
theorem internal_half_volume_tails (hRig : External.LongRangeRigidityLocallyUniform)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) (hεs : ε / 2 ≤ (1 - min s 1 / 2) / 4)
    (βlo βhi : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ N n : ℕ+, 2 ≤ (N : ℕ) → 2 ≤ (n : ℕ) → (n : ℕ) ≤ (N : ℕ) / 2 →
      ∀ j : ℕ → ℤ,
        (gibbsMeasure p N) {X | ∃ k : ℕ, 1 ≤ k ∧ k ≤ (N : ℕ) / 2 ∧
          (n : ℝ) ^ ε * (k : ℝ) ^ (min s 1 / 2 + ε) <
            |Riesz1.blockLength X (j k) k - k|} ≤
          ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^
            (ε * ((1 - min s 1 / 2) / 4) / (4 * (4 * (s + 2)))))) := by
  classical
  let u := (1 - min s 1 / 2) / 4
  let δ := ε * u / (4 * (4 * (s + 2)))
  let d := (ε / 2) / (4 * (s + 2))
  have hu : 0 < u := by dsimp [u]; linarith [min_le_right s 1]
  have hu1 : u ≤ 1 := by dsimp [u]; linarith [lt_min hs zero_lt_one]
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have hδd : δ ≤ d := by
    have heq : δ = (ε * u / 4) / (4 * (s + 2)) := by dsimp [δ]; rw [div_div]
    rw [heq]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hu1 hε.le]
  obtain ⟨Cs, cs, hCs, hcs, ht⟩ := physical_block_tails hRig s hs hs1 hε hε1 hεs βlo βhi hlo hle
  obtain ⟨Cl, cl, hCl, hcl, hl⟩ := physical_block_rigidity hRig s hs hs1
    (show 0 < ε / 2 by positivity) hεs βlo βhi hlo hle
  obtain ⟨B, hB, hb⟩ := stretched_exponential_sum hd hcl
  let c := min cs (cl / 2)
  have hc : 0 < c := lt_min hcs (by positivity)
  obtain ⟨A, hA, ha⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := 1) (c := c) (c' := c / 2) hδ (by linarith)
  refine ⟨(Cs + Cl * B) * (A + 1), c / 2, by positivity, by positivity, ?_⟩
  intro p hps hpl hph N n hN hn hnN j
  let μ := gibbsMeasure p N
  let E := fun k : ℕ => {X : Riesz1.Configuration N |
    (n : ℝ) ^ ε * (k : ℝ) ^ (min s 1 / 2 + ε) <
      |Riesz1.blockLength X (j k) k - k|}
  let S := Finset.Icc 1 (n : ℕ)
  let T := Finset.Icc ((n : ℕ) + 1) ((N : ℕ) / 2)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hsub : {X : Riesz1.Configuration N | ∃ k : ℕ, 1 ≤ k ∧ k ≤ (N : ℕ) / 2 ∧
      (n : ℝ) ^ ε * (k : ℝ) ^ (min s 1 / 2 + ε) <
        |Riesz1.blockLength X (j k) k - k|} ⊆
      (⋃ k ∈ S, E k) ∪ (⋃ k ∈ T, E k) := by
    rintro X ⟨k, hk, hkN, hbad⟩
    by_cases hkn : k ≤ (n : ℕ)
    · exact Or.inl (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨Finset.mem_Icc.mpr ⟨hk, hkn⟩, hbad⟩⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hkN⟩, hbad⟩⟩)
  have hs (k : ℕ) (hk : k ∈ S) : μ (E k) ≤
      ENNReal.ofReal (Cs * Real.exp (-cs * (n : ℝ) ^ δ)) := by
    obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
    apply (measure_mono (show E k ⊆ {X |
      (n : ℝ) ^ ε * (k : ℝ) ^ (min s 1 / 2) <
        |Riesz1.blockLength X (j k) k - k|} from ?_)).trans
      (ht p hps hpl hph N hN n k hn hnN hk1 hkn (j k))
    intro X hX
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hk1) (by linarith))
      (by positivity)) hX
  have hl' (k : ℕ) (hk : k ∈ T) : μ (E k) ≤
      ENNReal.ofReal (Cl * Real.exp (-cl * (k : ℝ) ^ d)) := by
    obtain ⟨hkn, hkN⟩ := Finset.mem_Icc.mp hk
    have hk1 : 1 ≤ k := by omega
    apply (measure_mono (show E k ⊆ {X |
      (k : ℝ) ^ (min s 1 / 2 + ε / 2) ≤
        |Riesz1.blockLength X (j k) k - k|} from ?_)).trans
      (by simpa only [d] using hl p hps hpl hph N hN (j k) k hk1 hkN)
    intro X hX
    change _ ≤ _
    change (n : ℝ) ^ ε * (k : ℝ) ^ (min s 1 / 2 + ε) < _ at hX
    apply le_of_lt (lt_of_le_of_lt ?_ hX)
    have hp := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ k by exact_mod_cast hk1)
      (show min s 1 / 2 + ε / 2 ≤ min s 1 / 2 + ε by linarith)
    exact hp.trans (le_mul_of_one_le_left (by positivity) (Real.one_le_rpow hn1 hε.le))
  have hsumS : μ (⋃ k ∈ S, E k) ≤
      ENNReal.ofReal ((n : ℝ) * Cs * Real.exp (-c * (n : ℝ) ^ δ)) := by
    apply (measure_biUnion_finset_le S E).trans
    apply (Finset.sum_le_sum hs).trans
    rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    -- Lowering the rate is done after counting the short ranks.
    apply ENNReal.ofReal_le_ofReal
    have he : Real.exp (-cs * (n : ℝ) ^ δ) ≤ Real.exp (-c * (n : ℝ) ^ δ) :=
      Real.exp_le_exp.mpr (by nlinarith [min_le_left cs (cl / 2), Real.rpow_nonneg (show 0 ≤ (n : ℝ) by positivity) δ])
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he
      (show 0 ≤ (n : ℝ) * Cs by positivity)
  have hsumT : μ (⋃ k ∈ T, E k) ≤
      ENNReal.ofReal (Cl * B * Real.exp (-c * (n : ℝ) ^ δ)) := by
    apply (measure_biUnion_finset_le T E).trans
    apply (Finset.sum_le_sum hl').trans
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity), ← Finset.mul_sum]
    apply ENNReal.ofReal_le_ofReal
    have hb' := hb n (by have := n.pos; omega) T (fun k hk => by have := (Finset.mem_Icc.mp hk).1; omega)
    have hnp := Real.rpow_le_rpow_of_exponent_le hn1 hδd
    have he : Real.exp (-(cl / 2) * (n : ℝ) ^ d) ≤ Real.exp (-c * (n : ℝ) ^ δ) :=
      Real.exp_le_exp.mpr (by
        have := mul_le_mul (min_le_right cs (cl / 2)) hnp (by positivity) (by positivity : 0 ≤ cl / 2)
        linarith)
    calc
      _ ≤ Cl * (B * Real.exp (-(cl / 2) * (n : ℝ) ^ d)) := mul_le_mul_of_nonneg_left hb' hCl.le
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he (show 0 ≤ Cl * B by positivity)
  apply ((measure_mono hsub).trans (measure_union_le _ _)).trans
  apply (add_le_add hsumS hsumT).trans
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hab := ha (n : ℝ) hn1
  rw [Real.rpow_one] at hab
  have hh := mul_le_mul_of_nonneg_left hab (show 0 ≤ Cs + Cl * B by positivity)
  have hbase := mul_le_mul_of_nonneg_right hn1
    (show 0 ≤ Cl * B * Real.exp (-c * (n : ℝ) ^ δ) by positivity)
  change _ ≤ (Cs + Cl * B) * (A + 1) * Real.exp (-(c / 2) * (n : ℝ) ^ δ)
  calc
    _ ≤ (Cs + Cl * B) * ((n : ℝ) * Real.exp (-c * (n : ℝ) ^ δ)) := by
      nlinarith only [hbase]
    _ ≤ (Cs + Cl * B) * (A * Real.exp (-(c / 2) * (n : ℝ) ^ δ)) := hh
    _ ≤ _ := by
      nlinarith only [show 0 ≤ (Cs + Cl * B) * Real.exp (-(c / 2) * (n : ℝ) ^ δ) by positivity]

/-- All ranks measured from an endpoint, including those above half the volume, satisfy
the exterior bound. The complementary block is the literal companion
block, with exactly the opposite centered deviation. -/
theorem anchored_rank_tails (hRig : External.LongRangeRigidityLocallyUniform)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) (hεs : ε / 2 ≤ (1 - min s 1 / 2) / 4)
    (βlo βhi : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ N n : ℕ+, 2 ≤ (N : ℕ) → 2 ≤ (n : ℕ) → (n : ℕ) ≤ (N : ℕ) / 2 →
      ∀ j : ℕ → ℤ,
        (gibbsMeasure p N) {X | ∃ r : ℕ, 1 ≤ r ∧ r < (N : ℕ) ∧
          (n : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε) <
            |Riesz1.blockLength X (j r) r - r|} ≤
          ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^
            (ε * ((1 - min s 1 / 2) / 4) / (4 * (4 * (s + 2)))))) := by
  obtain ⟨C, c, hC, hc, ht⟩ := internal_half_volume_tails hRig s hs hs1 hε hε1 hεs βlo βhi hlo hle
  refine ⟨2 * C, c, by positivity, hc, ?_⟩
  intro p hps hpl hph N n hN hn hnN j
  let j' := fun k : ℕ => j ((N : ℕ) - k) + (((N : ℕ) - k : ℕ) : ℤ)
  let E := fun f : ℕ → ℤ => {X : Riesz1.Configuration N | ∃ k : ℕ,
    1 ≤ k ∧ k ≤ (N : ℕ) / 2 ∧
      (n : ℝ) ^ ε * (k : ℝ) ^ (min s 1 / 2 + ε) <
        |Riesz1.blockLength X (f k) k - k|}
  have hsub : {X : Riesz1.Configuration N | ∃ r : ℕ, 1 ≤ r ∧ r < (N : ℕ) ∧
      (n : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε) <
        |Riesz1.blockLength X (j r) r - r|} ⊆ E j ∪ E j' := by
    rintro X ⟨r, hr, hrN, hbad⟩
    by_cases hrhalf : r ≤ (N : ℕ) / 2
    · exact Or.inl ⟨r, hr, hrhalf, hbad⟩
    · have hk1 : 1 ≤ (N : ℕ) - r := by omega
      have hkhalf : (N : ℕ) - r ≤ (N : ℕ) / 2 := by omega
      have hkr : (N : ℕ) - r ≤ r := by omega
      have hback : (N : ℕ) - ((N : ℕ) - r) = r := by omega
      refine Or.inr ⟨(N : ℕ) - r, hk1, hkhalf, ?_⟩
      dsimp [j']
      rw [hback, ← Riesz1.abs_blockLength_sub_reflect X (j r) hrN.le]
      apply lt_of_le_of_lt _ hbad
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hkr)
        (by linarith [lt_min hs zero_lt_one])
  apply ((measure_mono hsub).trans (measure_union_le _ _)).trans
  apply (add_le_add (ht p hps hpl hph N n hN hn hnN j)
    (ht p hps hpl hph N n hN hn hnN j')).trans_eq
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-- The exterior prefix/suffix sums in Subsection 6.1 are the literal
particle blocks, with zero-based gap labels. This bridge includes the
full exterior and does not require a half-volume restriction. -/
theorem anchored_exterior_sum {N : ℕ+} (X : Riesz1.Configuration N)
    (j : ℤ) (r : ℕ) :
    (∑ a ∈ Finset.range r, gap X (j + a)) = Riesz1.blockLength X j r := by
  simpa only [gap, Riesz1.gap] using (Riesz1.blockLength_eq_sum X j r).symm

/-- The residual length `L_N(y)` in Subsection 6.1, for an actual exterior,
is the active particle block length. Together with `anchored_exterior_sum`
this identifies every geometric condition in Subsection 6.1 literally. -/
theorem exterior_residual_length {N n : ℕ+} (hn : (n : ℕ) ≤ (N : ℕ))
    (X : Riesz1.Configuration N) :
    (N : ℝ) - (∑ a ∈ Finset.range ((N : ℕ) - (n : ℕ)), gap X ((n : ℤ) + a)) =
      Riesz1.blockLength X 0 n := by
  rw [anchored_exterior_sum]
  have h := Riesz1.blockLength_reflect X 0 hn
  rw [zero_add, Nat.cast_sub hn] at h
  linarith

/-- All geometric conditions in Subsection 6.1, under the two-sided law of
Subsection 6.1, with constants uniform in volume and compact temperature.
The two exterior sums start just after the active block and end at the
last gap, respectively. This is the second clause of
Appendix C. -/
theorem compact_exterior_geometry (hRig : External.LongRangeRigidityLocallyUniform)
    (s ε βlo βhi : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) (hεs : ε / 2 ≤ (1 - min s 1 / 2) / 4)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (θ : PhysicalCutoff) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ N n : ℕ+, 2 ≤ (n : ℕ) → 4 * (n : ℕ) ≤ (N : ℕ) →
      ∀ hn : (n : ℕ) ≤ (N : ℕ),
        (tiltedParticleMeasure p N n hn θ ε true)
          {X | (n : ℝ) ^ (min s 1 / 2 + ε) < |Riesz1.blockLength X 0 n - n| ∨
            ∃ r : ℕ, 1 ≤ r ∧ r ≤ (N : ℕ) - (n : ℕ) ∧
              (4 * (n : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε) <
                |Riesz1.blockLength X n r - r| ∨
               4 * (n : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε) <
                |Riesz1.blockLength X (((N : ℕ) - r : ℕ) : ℤ) r - r|)} ≤
          ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^
            (ε * ((1 - min s 1 / 2) / 4) / (4 * (4 * (s + 2)))))) := by
  obtain ⟨Ct, ct, hCt, hct, ht⟩ := physical_block_tails hRig s hs hs1 hε hε1 hεs βlo βhi hlo hle
  obtain ⟨Cr, cr, hCr, hcr, hr⟩ := anchored_rank_tails hRig s hs hs1 hε hε1 hεs βlo βhi hlo hle
  obtain ⟨z, hz, hnorm⟩ := compact_tilt_normalizer s ε βlo βhi hs hs1 hε hlo hle θ
  let c := min ct cr
  let δ := ε * ((1 - min s 1 / 2) / 4) / (4 * (4 * (s + 2)))
  have hc : 0 < c := lt_min hct hcr
  refine ⟨z⁻¹ * (Ct + 2 * Cr), c, by positivity, hc, ?_⟩
  intro p hps hpl hph N n hn2 hsize hn
  have hN : 2 ≤ (N : ℕ) := by omega
  have hnN : (n : ℕ) ≤ (N : ℕ) / 2 := by omega
  let μ := gibbsMeasure p N
  let E0 := {X : Riesz1.Configuration N |
    (n : ℝ) ^ (min s 1 / 2 + ε) < |Riesz1.blockLength X 0 n - n|}
  let E1 := {X : Riesz1.Configuration N | ∃ r : ℕ, 1 ≤ r ∧ r < (N : ℕ) ∧
    (n : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε) < |Riesz1.blockLength X n r - r|}
  let E2 := {X : Riesz1.Configuration N | ∃ r : ℕ, 1 ≤ r ∧ r < (N : ℕ) ∧
    (n : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε) <
      |Riesz1.blockLength X (((N : ℕ) - r : ℕ) : ℤ) r - r|}
  let E := {X : Riesz1.Configuration N |
    (n : ℝ) ^ (min s 1 / 2 + ε) < |Riesz1.blockLength X 0 n - n| ∨
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ (N : ℕ) - (n : ℕ) ∧
      (4 * (n : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε) <
        |Riesz1.blockLength X n r - r| ∨
       4 * (n : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε) <
        |Riesz1.blockLength X (((N : ℕ) - r : ℕ) : ℤ) r - r|)}
  have lower (A b : ℝ) (hA : 0 ≤ A) (hcb : c ≤ b) :
      ENNReal.ofReal (A * Real.exp (-b * (n : ℝ) ^ δ)) ≤
        ENNReal.ofReal (A * Real.exp (-c * (n : ℝ) ^ δ)) := by
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hA
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hcb (show 0 ≤ (n : ℝ) ^ δ by positivity)
    linarith
  have h0 : μ E0 ≤ ENNReal.ofReal (Ct * Real.exp (-c * (n : ℝ) ^ δ)) := by
    have heq : (n : ℝ) ^ (min s 1 / 2 + ε) = (n : ℝ) ^ ε * (n : ℝ) ^ (min s 1 / 2) := by
      rw [← Real.rpow_add (by positivity)]
      congr 1
      ring
    apply le_trans _ (lower Ct ct hCt.le (min_le_left _ _))
    simpa only [E0, heq] using ht p hps hpl hph N hN n n hn2 hnN (by omega) le_rfl 0
  have h1 : μ E1 ≤ ENNReal.ofReal (Cr * Real.exp (-c * (n : ℝ) ^ δ)) :=
    (hr p hps hpl hph N n hN hn2 hnN (fun _ => (n : ℤ))).trans
      (lower Cr cr hCr.le (min_le_right _ _))
  have h2 : μ E2 ≤ ENNReal.ofReal (Cr * Real.exp (-c * (n : ℝ) ^ δ)) :=
    (hr p hps hpl hph N n hN hn2 hnN (fun r => (((N : ℕ) - r : ℕ) : ℤ))).trans
      (lower Cr cr hCr.le (min_le_right _ _))
  have hsub : E ⊆ E0 ∪ (E1 ∪ E2) := by
    rintro X (h | ⟨r, hr1, hrn, h | h⟩)
    · exact Or.inl h
    · refine Or.inr (Or.inl ⟨r, hr1, by have := n.pos; omega, lt_of_le_of_lt ?_ h⟩)
      nlinarith [show 0 ≤ (n : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε) by positivity]
    · refine Or.inr (Or.inr ⟨r, hr1, by have := n.pos; omega, lt_of_le_of_lt ?_ h⟩)
      nlinarith [show 0 ≤ (n : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε) by positivity]
  have hbase : μ E ≤ ENNReal.ofReal ((Ct + 2 * Cr) * Real.exp (-c * (n : ℝ) ^ δ)) := by
    apply ((measure_mono hsub).trans (measure_union_le _ _)).trans
    apply (add_le_add h0 ((measure_union_le _ _).trans (add_le_add h1 h2))).trans_eq
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have hE : MeasurableSet E := by
    have hB (j : ℤ) (r : ℕ) : Measurable (fun X : Riesz1.Configuration N =>
        |Riesz1.blockLength X j r - r|) :=
      ((Riesz1.measurable_blockLength j r).sub measurable_const).abs
    simp only [E, ofPred_or, ofPred_exists, ofPred_and]
    refine (measurableSet_lt measurable_const (hB 0 n)).union ?_
    apply MeasurableSet.iUnion
    intro r
    exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
      ((measurableSet_lt measurable_const (hB n r)).union
        (measurableSet_lt measurable_const (hB (((N : ℕ) - r : ℕ) : ℤ) r))))
  apply (internal_tilted_event_le p N n hn θ ε hz
    (hnorm p hps hpl hph N n hN hn) E hE).trans
  apply (mul_le_mul_of_nonneg_left hbase zero_le).trans_eq
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- See Appendix C in the paper, complete statement.
The structural constants precede both tolerances and temperature. The
weighted interior bound and every exterior prefix and suffix geometric condition
hold simultaneously, uniformly in volume and on every compact positive
temperature interval. The displayed equality fixes the geometric power
as a function of `s` and `ε` alone. -/
theorem full_law_local_laws (hRig : External.LongRangeRigidityLocallyUniform)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ ηstar astar εstar : ℝ, 0 < ηstar ∧ 0 < astar ∧ 0 < εstar ∧
      ∀ η : ℝ, 0 < η → η ≤ ηstar → ∀ ε : ℝ, 0 < ε → ε ≤ εstar →
      ∃ δ : ℝ, δ = ε * ((1 - min s 1 / 2) / 4) / (4 * (4 * (s + 2))) ∧ 0 < δ ∧
      ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
        ∀ N n : ℕ+, 2 ≤ (n : ℕ) → 4 * (n : ℕ) ≤ (N : ℕ) →
          (n : ℝ) ^ (2 / s) ≤ (N : ℝ) → ∀ hn : (n : ℕ) ≤ (N : ℕ),
          ((∫⁻ X in {X | finiteGapBlock X ∉ goodBlockEvent s n N η},
            ENNReal.ofReal (exceptionalWeight s (finiteGapBlock (K := n) X))
            ∂tiltedParticleMeasure p N n hn θ ε true) ≤
            ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ (astar * η)))) ∧
          ((tiltedParticleMeasure p N n hn θ ε true)
            {X | (n : ℝ) ^ (min s 1 / 2 + ε) < |Riesz1.blockLength X 0 n - n| ∨
              ∃ r : ℕ, 1 ≤ r ∧ r ≤ (N : ℕ) - (n : ℕ) ∧
                (4 * (n : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε) <
                  |Riesz1.blockLength X n r - r| ∨
                 4 * (n : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε) <
                  |Riesz1.blockLength X (((N : ℕ) - r : ℕ) : ℤ) r - r|)} ≤
            ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ δ))) := by
  obtain ⟨ηstar, astar, hηstar, hastar, hw⟩ := compact_full_law_weighted_rigidity hRig s hs hs1
  let u := (1 - min s 1 / 2) / 4
  have hu : 0 < u := by dsimp [u]; linarith [min_le_right s 1]
  refine ⟨ηstar, astar, min (1 / 4) u, hηstar, hastar, lt_min (by norm_num) hu, ?_⟩
  intro η hη hηs ε hε hεs
  let δ := ε * u / (4 * (4 * (s + 2)))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, rfl, hδ, ?_⟩
  intro βlo βhi hlo hle θ
  obtain ⟨Cw, cw, hCw, hcw, hw'⟩ := hw η hη hηs ε hε βlo βhi hlo hle θ
  have hε1 : ε ≤ 1 / 4 := hεs.trans (min_le_left _ _)
  have hεu : ε / 2 ≤ (1 - min s 1 / 2) / 4 := by
    have := hεs.trans (min_le_right _ _)
    dsimp [u] at this
    linarith
  obtain ⟨Cg, cg, hCg, hcg, hg⟩ := compact_exterior_geometry hRig s ε βlo βhi hs hs1
    hε hε1 hεu hlo hle θ
  refine ⟨Cw + Cg, min cw cg, by positivity, lt_min hcw hcg, ?_⟩
  intro p hps hpl hph N n hn2 hsize hsize' hn
  have lower (A b q : ℝ) (hA : A ≤ Cw + Cg) (hb : min cw cg ≤ b) :
      ENNReal.ofReal (A * Real.exp (-b * (n : ℝ) ^ q)) ≤
        ENNReal.ofReal ((Cw + Cg) * Real.exp (-(min cw cg) * (n : ℝ) ^ q)) := by
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul hA _ (Real.exp_pos _).le (by positivity)
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right hb (show 0 ≤ (n : ℝ) ^ q by positivity)
    linarith
  exact ⟨(hw' p hps hpl hph N n hn2 hsize hsize' hn).trans
      (lower Cw cw (astar * η) (by linarith) (min_le_left _ _)),
    (hg p hps hpl hph N n hn2 hsize hn).trans
      (lower Cg cg δ (by linarith) (min_le_right _ _))⟩

end Riesz2.InterpolantLocalLaws
