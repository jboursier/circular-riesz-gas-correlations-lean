/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.InterpolantLocalLaws
public import Riesz2.ToMathlib.FiniteRigidityGrid
public import Riesz2.DecayShort.LocalLawPart3
public import Riesz2.Frozen.External.LongRangeRigidityLocallyUniform
public import Riesz1.Rigidity.ReductionScalesMean

/-!
# Physical finite-grid block estimates

The physical specialization and ordinary-interval part of Appendix C. The same finite
grid applies in both exponent regimes and keeps a tail power linear in the tolerance.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Riesz2.InterpolantLocalLaws

/-- The cyclic-interval sum in the short-range local law is the literal
particle block length used by the long-range rigidity input. -/
theorem cyclicInterval_gapVector {N : ℕ+} (X : Riesz1.Configuration N)
    (j : ℤ) {k : ℕ} (hk : k ≤ (N : ℕ)) :
    (∑ i ∈ cyclicInterval N j k, gapVector X i) = Riesz1.blockLength X j k := by
  classical
  rw [cyclicInterval, Finset.sum_image]
  · rw [Riesz1.blockLength_eq_sum]
    apply Finset.sum_congr rfl
    intro a _
    exact (gap_eq_gapVector_labelOf X (j + a)).symm
  · intro a ha b hb he
    have ha' := Finset.mem_range.mp ha
    have hb' := Finset.mem_range.mp hb
    have hd := Riesz1.dvd_of_labelOf_eq N he
    rw [show j + (b : ℤ) - (j + a) = (b : ℤ) - a by ring] at hd
    have hz := Int.eq_zero_of_abs_lt_dvd hd
      (show |(b : ℤ) - a| < ((N : ℕ) : ℤ) by rw [abs_lt]; constructor <;> omega)
    omega

/-- Physical block tails at a fixed exponent, uniformly on compact
temperature intervals, in both regimes (Appendix C).
The compact-temperature rigidity bound is a hypothesis. -/
theorem physical_block_rigidity (hRig : External.LongRangeRigidityLocallyUniform)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) {b : ℝ}
    (hb : 0 < b) (hbu : b ≤ (1 - min s 1 / 2) / 4)
    (βlo βhi : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ N : ℕ+, 2 ≤ (N : ℕ) → ∀ j : ℤ, ∀ k : ℕ,
        1 ≤ k → k ≤ (N : ℕ) / 2 →
        (gibbsMeasure p N) {X | (k : ℝ) ^ (min s 1 / 2 + b) ≤
          |Riesz1.blockLength X j k - k|} ≤
          ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ (b / (4 * (s + 2))))) := by
  by_cases hlong : s < 1
  · let sr : Riesz1.RieszExponent := ⟨s, hs, hlong⟩
    have hbs : b < (1 - sr.val / 2) / 2 := by
      dsimp [sr]
      rw [min_eq_left hlong.le] at hbu
      linarith
    obtain ⟨C, c, hC, hc, ht⟩ := hRig sr b hb hbs βlo βhi hlo hle
    refine ⟨C, c, hC, hc, fun p hps hpl hph N hN j k hk hkN => ?_⟩
    let β : InverseTemperature := ⟨p.val.1, p.property.1⟩
    have hp : p = ofLong β sr := Subtype.ext (Prod.ext rfl hps)
    have ht' := ht β ⟨hpl, hph⟩ N hN j k hk hkN
    simpa only [← hp, sr, min_eq_left hlong.le, Riesz1.blockLength] using ht'
  · have hshort : 1 < s := lt_of_le_of_ne (le_of_not_gt hlong) hs1.symm
    obtain ⟨C, c, hC, hc, ht⟩ :=
      DecayShort.shortRange_localLaw s βlo βhi b hshort hlo hle hb
    refine ⟨C, c, hC, hc, fun p hps hpl hph N hN j k hk hkN => ?_⟩
    have hA : MeasurableSet {x : Fin (N : ℕ) → ℝ | (k : ℝ) ^ (1 / 2 + b) ≤
        |(∑ i ∈ cyclicInterval N j k, x i) - (k : ℝ)|} :=
      measurableSet_le measurable_const
        (((Finset.measurable_sum _ fun i _ => measurable_pi_apply i).sub measurable_const).abs)
    have hmap := Measure.map_apply (μ := gibbsMeasure p N)
      (show Measurable (gapVector (N := N)) from Riesz1.measurable_gapVector N) hA
    have ht' := ht p hps hpl hph N hN k hk hkN j
    rw [gapLaw, hmap] at ht'
    have he : (fun X : Riesz1.Configuration N => gapVector X) ⁻¹'
        {x | (k : ℝ) ^ (1 / 2 + b) ≤ |(∑ i ∈ cyclicInterval N j k, x i) - k|} =
        {X | (k : ℝ) ^ (min s 1 / 2 + b) ≤ |Riesz1.blockLength X j k - k|} := by
      ext X
      simp only [mem_preimage, mem_ofPred_eq, min_eq_right hshort.le,
        cyclicInterval_gapVector X j (show k ≤ (N : ℕ) by omega)]
    rwa [he] at ht'

/-- Finite-grid amplification on the actual physical particle laws.
The coefficient of `η` is independent of `η` and of the temperature. All prefactors precede the volume, active size and starting label.
This is the individual-block step of Appendix C. -/
theorem physical_block_tails (hRig : External.LongRangeRigidityLocallyUniform)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) {η : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1 / 4) (hηs : η / 2 ≤ (1 - min s 1 / 2) / 4)
    (βlo βhi : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ N : ℕ+, 2 ≤ (N : ℕ) → ∀ n k : ℕ,
        2 ≤ n → n ≤ (N : ℕ) / 2 → 1 ≤ k → k ≤ n → ∀ j : ℤ,
        (gibbsMeasure p N) {X | (n : ℝ) ^ η * (k : ℝ) ^ (min s 1 / 2) <
          |Riesz1.blockLength X j k - k|} ≤
          ENNReal.ofReal (C * Real.exp
            (-c * (n : ℝ) ^ (η * ((1 - min s 1 / 2) / 4) / (4 * (4 * (s + 2)))))) := by
  let A := {q : ℕ+ × Parameters × ℤ // 2 ≤ (q.1 : ℕ) ∧
    q.2.1.val.2 = s ∧ βlo ≤ q.2.1.val.1 ∧ q.2.1.val.1 ≤ βhi}
  let μ := fun a : A => gibbsMeasure a.val.2.1 a.val.1
  let S := fun (a : A) k (X : Riesz1.Configuration a.val.1) =>
    Riesz1.blockLength X a.val.2.2 k
  let R := fun a : A => (a.val.1 : ℕ) / 2
  have hσ : 0 < min s 1 := lt_min hs zero_lt_one
  have hu : 0 < (1 - min s 1 / 2) / 4 := by linarith [min_le_right s 1]
  have hinput : ∀ b : ℝ, 0 < b → b ≤ (1 - min s 1 / 2) / 4 →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (a : A) k, 1 ≤ k → k ≤ R a →
        μ a {X | (k : ℝ) ^ (min s 1 / 2 + b) ≤ |S a k X - k|} ≤
          ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ (b / (4 * (s + 2))))) := by
    intro b hb hbu
    obtain ⟨C, c, hC, hc, ht⟩ := physical_block_rigidity hRig s hs hs1 hb hbu βlo βhi hlo hle
    exact ⟨C, c, hC, hc, fun a k hk hkR =>
      ht a.val.2.1 a.property.2.1 a.property.2.2.1 a.property.2.2.2
        a.val.1 a.property.1 a.val.2.2 k hk hkR⟩
  obtain ⟨C, c, hC, hc, ht⟩ := FiniteRigidityGrid.internal_all_block_tails_all_sizes
    μ S R (fun a => DefinitionSanity.particle_law_probability _ _)
    (show 0 ≤ min s 1 / 2 by positivity) hη hη1 hu hηs
    (show (1 - min s 1 / 2) / 4 ≤ 1 by linarith)
    (show 0 < 4 * (s + 2) by positivity)
    (show min s 1 / 2 + (1 - min s 1 / 2) / 4 ≤ 1 by linarith [min_le_right s 1])
    (fun a k X => by
      dsimp [S]
      rw [Riesz1.blockLength_eq_sum]
      exact Finset.sum_nonneg fun i _ => (Riesz1.gap_pos X _).le)
    (fun a X k h hkh => by
      dsimp [S, Riesz1.blockLength]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply sub_le_sub_right
      exact (Riesz1.cyclicLift_strictMono X).monotone (by omega)) hinput
  exact ⟨C, c, hC, hc, fun p hps hpl hph N hN n k hn hnN hk hkn j =>
    ht ⟨(N, p, j), hN, hps, hpl, hph⟩ n k hn hnN hk hkn⟩

/-- Ordinary intervals in the active block have the particle block
length used in the physical rigidity estimate, including both endpoints. -/
theorem ordinary_interval_blockLength {N n : ℕ+} (X : Riesz1.Configuration N)
    (a b : ℕ) (hab : a ≤ b) (hb : b ≤ (n : ℕ)) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin (n : ℕ) => a ≤ i.val ∧ i.val < b),
      finiteGapBlock X i) = Riesz1.blockLength X a (b - a) := by
  classical
  rw [Riesz1.blockLength_eq_sum]
  apply Finset.sum_bij (fun i _ => i.val - a)
  · intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    exact Finset.mem_range.mpr (by omega)
  · intro i hi j hj hij
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    apply Fin.ext
    omega
  · intro k hk
    have hk' := Finset.mem_range.mp hk
    refine ⟨⟨a + k, by omega⟩, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    change gap X (i.val : ℤ) = gap X ((a : ℤ) + (i.val - a : ℕ))
    congr 1
    omega

/-- Simultaneous ordinary-interval deviations in an active window.
There are at most `2*n²` tests, and their polynomial cost is absorbed
without changing the linear tail power (Appendix C). -/
theorem ordinary_interval_tails (hRig : External.LongRangeRigidityLocallyUniform)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) {η : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1 / 4) (hηs : η / 2 ≤ (1 - min s 1 / 2) / 4)
    (βlo βhi : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ N n : ℕ+, 2 ≤ (N : ℕ) → 2 ≤ (n : ℕ) → (n : ℕ) ≤ (N : ℕ) / 2 →
        (gibbsMeasure p N) {X | ∃ a b : ℕ, a < b ∧ b ≤ (n : ℕ) ∧
          (n : ℝ) ^ η * (b - a : ℕ) ^ (min s 1 / 2) <
            |(∑ i ∈ Finset.univ.filter (fun i : Fin (n : ℕ) => a ≤ i.val ∧ i.val < b),
              finiteGapBlock X i) - (b - a : ℕ)|} ≤
          ENNReal.ofReal (C * Real.exp
            (-c * (n : ℝ) ^ (η * ((1 - min s 1 / 2) / 4) / (4 * (4 * (s + 2)))))) := by
  classical
  obtain ⟨C, c, hC, hc, ht⟩ := physical_block_tails hRig s hs hs1 hη hη1 hηs βlo βhi hlo hle
  let δ := η * ((1 - min s 1 / 2) / 4) / (4 * (4 * (s + 2)))
  have hcap : 0 < (1 - min s 1 / 2) / 4 := by linarith [min_le_right s 1]
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨B, hB, hb⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := 2) (c := c) (c' := c / 2) hδ (by linarith)
  refine ⟨2 * C * (B + 1), c / 2, by positivity, by positivity, ?_⟩
  intro p hps hpl hph N n hN hn hnN
  let μ := gibbsMeasure p N
  have : IsProbabilityMeasure μ := DefinitionSanity.particle_law_probability p N
  let I := Fin (n : ℕ) × Fin ((n : ℕ) + 1)
  let E : I → Set (Riesz1.Configuration N) := fun ab =>
    if ab.1.val < ab.2.val then
      {X | (n : ℝ) ^ η * (ab.2.val - ab.1.val : ℕ) ^ (min s 1 / 2) <
        |Riesz1.blockLength X ab.1.val (ab.2.val - ab.1.val) - (ab.2.val - ab.1.val : ℕ)|}
    else ∅
  have htail (i : I) : μ (E i) ≤ ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ δ)) := by
    dsimp [E]
    split_ifs with hi
    · exact ht p hps hpl hph N hN n _ hn hnN (by omega)
        (by have := i.2.isLt; omega) i.1.val
    · simp
  have hsub : {X : Riesz1.Configuration N | ∃ a b : ℕ, a < b ∧ b ≤ (n : ℕ) ∧
      (n : ℝ) ^ η * (b - a : ℕ) ^ (min s 1 / 2) <
        |(∑ i ∈ Finset.univ.filter (fun i : Fin (n : ℕ) => a ≤ i.val ∧ i.val < b),
          finiteGapBlock X i) - (b - a : ℕ)|} ⊆ ⋃ i : I, E i := by
    rintro X ⟨a, b, hab, hbn, hbad⟩
    refine mem_iUnion.mpr ⟨(⟨a, by omega⟩, ⟨b, by omega⟩), ?_⟩
    dsimp [E]
    rw [ite_eq_left hab]
    rwa [ordinary_interval_blockLength X a b hab.le hbn] at hbad
  have hcard : (Fintype.card I : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by
    simp only [I, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
    nlinarith
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).mpr
  calc
    μ.real _ ≤ μ.real (⋃ i : I, E i) := measureReal_mono hsub
    _ ≤ ∑ i : I, μ.real (E i) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _ : I, C * Real.exp (-c * (n : ℝ) ^ δ) := by
      apply Finset.sum_le_sum
      intro i _
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) (htail i)
    _ = (Fintype.card I : ℝ) * (C * Real.exp (-c * (n : ℝ) ^ δ)) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ 2 * C * ((n : ℝ) ^ 2 * Real.exp (-c * (n : ℝ) ^ δ)) := by
      nlinarith [mul_le_mul_of_nonneg_right hcard
        (show 0 ≤ C * Real.exp (-c * (n : ℝ) ^ δ) by positivity)]
    _ ≤ 2 * C * ((B + 1) * Real.exp (-(c / 2) * (n : ℝ) ^ δ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hh := hb (n : ℝ) (show 1 ≤ (n : ℝ) by exact_mod_cast n.pos)
      rw [Real.rpow_two] at hh
      nlinarith [Real.exp_pos (-(c / 2) * (n : ℝ) ^ δ)]
    _ = _ := by ring

/-- Borelness of the ordinary-interval exceptional event. The integer
endpoints range over a countable family and every tested sum is finite. -/
theorem measurableSet_ordinary_interval_deviations (s η : ℝ) (N n : ℕ+) :
    MeasurableSet {X : Riesz1.Configuration N | ∃ a b : ℕ, a < b ∧ b ≤ (n : ℕ) ∧
      (n : ℝ) ^ η * (b - a : ℕ) ^ (min s 1 / 2) <
        |(∑ i ∈ Finset.univ.filter (fun i : Fin (n : ℕ) => a ≤ i.val ∧ i.val < b),
          finiteGapBlock X i) - (b - a : ℕ)|} := by
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro a
  apply MeasurableSet.iUnion
  intro b
  by_cases hab : a < b
  · by_cases hbn : b ≤ (n : ℕ)
    · simp only [hab, hbn, true_and]
      exact measurableSet_lt measurable_const
        (((Finset.measurable_sum _ fun i _ =>
          (show Measurable (fun X : Riesz1.Configuration N => finiteGapBlock (K := n) X i)
            from Riesz1.measurable_gap i.val)).sub measurable_const).abs)
    · simp [hbn]
  · simp [hab]

/-- Weighted ordinary-interval tails under the literal two-sided tilt.
Together with the single-gap cutoff estimate this supplies the
weighted rigidity inequality in Appendix C. -/
theorem tilted_weighted_interval_tails (hRig : External.LongRangeRigidityLocallyUniform)
    (s ε η : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (hε : 0 < ε) (hη : 0 < η) (hη1 : η ≤ 1 / 4)
    (hηs : η / 2 ≤ (1 - min s 1 / 2) / 4) (β : ℝ) (hβ : 0 < β) (θ : PhysicalCutoff) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → p.val.1 = β →
      ∀ N n : ℕ+, 2 ≤ (N : ℕ) → 2 ≤ (n : ℕ) →
      (n : ℕ) ≤ (N : ℕ) / 2 → ∀ hn : (n : ℕ) ≤ (N : ℕ),
        (∫⁻ X in {X | ∃ a b : ℕ, a < b ∧ b ≤ (n : ℕ) ∧
          (n : ℝ) ^ η * (b - a : ℕ) ^ (min s 1 / 2) <
            |(∑ i ∈ Finset.univ.filter (fun i : Fin (n : ℕ) => a ≤ i.val ∧ i.val < b),
              finiteGapBlock X i) - (b - a : ℕ)|},
          ENNReal.ofReal (exceptionalWeight s (finiteGapBlock (K := n) X))
          ∂tiltedParticleMeasure p N n hn θ ε true) ≤
          ENNReal.ofReal (C * Real.exp
            (-c * (n : ℝ) ^ (η * ((1 - min s 1 / 2) / 4) / (4 * (4 * (s + 2)))))) := by
  obtain ⟨Ct, ct, hCt, hct, ht⟩ := ordinary_interval_tails hRig s hs hs1
    hη hη1 hηs β β hβ le_rfl
  obtain ⟨z, _, _, _, hz, _, _, _, hnorm⟩ :=
    InterpolatingDensities.penalty_support_and_normalizer s β ε hs hs1 hβ hε θ
  obtain ⟨K, hK, hw⟩ := tilted_weighted_event s β ε hs hs1 hβ hε θ
  let δ := η * ((1 - min s 1 / 2) / 4) / (4 * (4 * (s + 2)))
  have hcap : 0 < (1 - min s 1 / 2) / 4 := by linarith [min_le_right s 1]
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨B, hB, hb⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := 1) (c := ct / 2) (c' := ct / 4) hδ (by linarith)
  refine ⟨K * Real.sqrt (z⁻¹ * Ct) * (B + 1), ct / 4, by positivity, by positivity, ?_⟩
  intro p hps hpβ N n hN hn2 hnN hn
  let μ := tiltedParticleMeasure p N n hn θ ε true
  let E : Set (Riesz1.Configuration N) := {X | ∃ a b : ℕ, a < b ∧ b ≤ (n : ℕ) ∧
    (n : ℝ) ^ η * (b - a : ℕ) ^ (min s 1 / 2) <
      |(∑ i ∈ Finset.univ.filter (fun i : Fin (n : ℕ) => a ≤ i.val ∧ i.val < b),
        finiteGapBlock X i) - (b - a : ℕ)|}
  have hE : MeasurableSet E := measurableSet_ordinary_interval_deviations s η N n
  have hbase := ht p hps (by rw [hpβ]) (by rw [hpβ]) N n hN hn2 hnN
  have htail : μ E ≤ ENNReal.ofReal (z⁻¹ * Ct * Real.exp (-ct * (n : ℝ) ^ δ)) := by
    apply (internal_tilted_event_le p N n hn θ ε hz
      (hnorm p hps hpβ N n hN hn).2 E hE).trans
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
  refine (hw p hps hpβ N n hN hn E hE).trans (ENNReal.ofReal_le_ofReal ?_)
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

/-- Simultaneous coordinate and ordinary-interval rigidity for the
unmodified physical law. This uses the block event, with its
strict mass condition, and gives a power linear in `η` in both regimes. -/
theorem physical_goodBlock_probability (hRig : External.LongRangeRigidityLocallyUniform)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) {η : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1 / 4) (hηs : η / 2 ≤ (1 - min s 1 / 2) / 4)
    (βlo βhi : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ N n : ℕ+, 2 ≤ (N : ℕ) → 2 ≤ (n : ℕ) → (n : ℕ) ≤ (N : ℕ) / 2 →
        (gibbsMeasure p N) {X | finiteGapBlock X ∉ goodBlockEvent s n N η} ≤
          ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^
            (η * min (min s 1) (((1 - min s 1 / 2) / 4) / (4 * (4 * (s + 2))))))) := by
  classical
  obtain ⟨Ct, ct, hCt, hct, ht⟩ := ordinary_interval_tails hRig s hs hs1
    hη hη1 hηs βlo βhi hlo hle
  obtain ⟨Cg, cg, hCg, hcg, hg, _⟩ :=
    SingleGapTails.single_gap_tails s βlo βhi hs hs1 hlo hle
  let q := ((1 - min s 1 / 2) / 4) / (4 * (4 * (s + 2)))
  let δ := η * min (min s 1) q
  let c := min cg ct
  have hcap : 0 < (1 - min s 1 / 2) / 4 := by linarith [min_le_right s 1]
  have hq : 0 < q := by dsimp [q]; positivity
  have hδ : 0 < δ := mul_pos hη (lt_min (lt_min hs zero_lt_one) hq)
  have hc : 0 < c := lt_min hcg hct
  obtain ⟨B, hB, hb⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := 1) (c := c) (c' := c / 2) hδ (by linarith)
  refine ⟨(2 * Cg + Ct) * (B + 1), c / 2, by positivity, by positivity, ?_⟩
  intro p hps hpl hph N n hN hn hnN
  let μ := gibbsMeasure p N
  have : IsProbabilityMeasure μ := DefinitionSanity.particle_law_probability p N
  let U : Set (Riesz1.Configuration N) := {X | ∃ i : Fin (n : ℕ),
    gap X i.val < (n : ℝ) ^ (-η) ∨ (n : ℝ) ^ η < gap X i.val}
  let V : Set (Riesz1.Configuration N) := {X | ∃ a b : ℕ, a < b ∧ b ≤ (n : ℕ) ∧
    (n : ℝ) ^ η * (b - a : ℕ) ^ (min s 1 / 2) <
      |(∑ i ∈ Finset.univ.filter (fun i : Fin (n : ℕ) => a ≤ i.val ∧ i.val < b),
        finiteGapBlock X i) - (b - a : ℕ)|}
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by positivity
  have hδη : δ ≤ η := by
    have hm := (min_le_left (min s 1) q).trans (min_le_right s 1)
    dsimp [δ]
    nlinarith
  have hδηs : δ ≤ η * s := by
    have hm := (min_le_left (min s 1) q).trans (min_le_left s 1)
    dsimp [δ]
    nlinarith
  have hδq : δ ≤ η * ((1 - min s 1 / 2) / 4) / (4 * (4 * (s + 2))) := by
    have hm := mul_le_mul_of_nonneg_left (min_le_right (min s 1) q) hη.le
    simpa only [δ, q, mul_div_assoc] using hm
  have hweaken {D e r : ℝ} (hD : 0 ≤ D) (he : c ≤ e) (hr : δ ≤ r) :
      ENNReal.ofReal (D * Real.exp (-e * (n : ℝ) ^ r)) ≤
        ENNReal.ofReal (D * Real.exp (-c * (n : ℝ) ^ δ)) := by
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hD
    apply Real.exp_le_exp.mpr
    have hpow := Real.rpow_le_rpow_of_exponent_le hn1 hr
    have he0 : 0 ≤ e := hc.le.trans he
    nlinarith [mul_le_mul he hpow (by positivity : 0 ≤ (n : ℝ) ^ δ) he0]
  have hcut (i : Fin (n : ℕ)) :
      μ {X | gap X i.val < (n : ℝ) ^ (-η) ∨ (n : ℝ) ^ η < gap X i.val} ≤
        ENNReal.ofReal (2 * Cg * Real.exp (-c * (n : ℝ) ^ δ)) := by
    obtain ⟨hl, hu⟩ := hg p hps hpl hph N hN i.val
    have hl' := hl ((n : ℝ) ^ (-η)) (by positivity)
      (Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith))
    have hu' := hu ((n : ℝ) ^ η) (Real.one_le_rpow hn1 hη.le)
    have hp : ((n : ℝ) ^ (-η)) ^ (-s) = (n : ℝ) ^ (η * s) := by
      rw [← Real.rpow_mul hn0.le]
      congr 1
      ring
    rw [hp] at hl'
    calc
      _ ≤ μ {X | gap X i.val ≤ (n : ℝ) ^ (-η)} + μ {X | (n : ℝ) ^ η ≤ gap X i.val} := by
        apply (measure_mono (show {X : Riesz1.Configuration N |
            gap X i.val < (n : ℝ) ^ (-η) ∨ (n : ℝ) ^ η < gap X i.val} ⊆
            {X | gap X i.val ≤ (n : ℝ) ^ (-η)} ∪ {X | (n : ℝ) ^ η ≤ gap X i.val}
            from fun X h =>
          h.elim (fun h => Or.inl h.le) (fun h => Or.inr h.le))).trans
        exact measure_union_le _ _
      _ ≤ ENNReal.ofReal (Cg * Real.exp (-c * (n : ℝ) ^ δ)) +
          ENNReal.ofReal (Cg * Real.exp (-c * (n : ℝ) ^ δ)) :=
        add_le_add (hl'.trans (hweaken hCg.le (min_le_left _ _) hδηs))
          (hu'.trans (hweaken hCg.le (min_le_left _ _) hδη))
      _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
  have hU : μ U ≤ ENNReal.ofReal ((n : ℝ) * (2 * Cg * Real.exp (-c * (n : ℝ) ^ δ))) := by
    calc
      _ ≤ ∑ i : Fin (n : ℕ), μ {X | gap X i.val < (n : ℝ) ^ (-η) ∨
          (n : ℝ) ^ η < gap X i.val} := by
        simpa only [U, ofPred_exists, tsum_fintype] using measure_iUnion_le (μ := μ)
          (fun i : Fin (n : ℕ) => {X | gap X i.val < (n : ℝ) ^ (-η) ∨
            (n : ℝ) ^ η < gap X i.val})
      _ ≤ ∑ _ : Fin (n : ℕ), ENNReal.ofReal (2 * Cg * Real.exp (-c * (n : ℝ) ^ δ)) :=
        Finset.sum_le_sum (fun i _ => hcut i)
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  have hV : μ V ≤ ENNReal.ofReal (Ct * Real.exp (-c * (n : ℝ) ^ δ)) :=
    (ht p hps hpl hph N n hN hn hnN).trans (hweaken hCt.le (min_le_right _ _) hδq)
  have hsub : {X : Riesz1.Configuration N | finiteGapBlock X ∉ goodBlockEvent s n N η} ⊆ U ∪ V := by
    intro X hX
    by_contra hnot
    have hU' : X ∉ U := fun h => hnot (Or.inl h)
    have hV' : X ∉ V := fun h => hnot (Or.inr h)
    apply hX
    have hsum : (∑ i : Fin (n : ℕ), finiteGapBlock X i) = Riesz1.blockLength X 0 n := by
      rw [Riesz1.blockLength_eq_sum]
      simpa only [finiteGapBlock, gap, Riesz1.gap, zero_add] using
        (Fin.sum_univ_eq_sum_range (fun j : ℕ => gap X j) (n : ℕ))
    refine ⟨?_, ?_, ?_⟩
    · rw [hsum]
      exact Riesz1.blockLength_lt_N X 0 (by have := n.pos; omega)
    · intro i
      constructor
      · exact not_lt.mp (fun h => hU' ⟨i, Or.inl h⟩)
      · exact not_lt.mp (fun h => hU' ⟨i, Or.inr h⟩)
    · intro a b hab hbn
      exact not_lt.mp (fun h => hV' ⟨a, b, hab, hbn, h⟩)
  apply ((measure_mono hsub).trans (measure_union_le U V)).trans
  apply (add_le_add hU hV).trans
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hpoly := hb (n : ℝ) hn1
  rw [Real.rpow_one] at hpoly
  have he := Real.exp_pos (-c * (n : ℝ) ^ δ)
  have he' := Real.exp_pos (-(c / 2) * (n : ℝ) ^ δ)
  have hstep : (n : ℝ) * (2 * Cg * Real.exp (-c * (n : ℝ) ^ δ)) +
      Ct * Real.exp (-c * (n : ℝ) ^ δ) ≤
      (2 * Cg + Ct) * ((n : ℝ) * Real.exp (-c * (n : ℝ) ^ δ)) := by
    have h := mul_le_mul_of_nonneg_right hn1
      (show 0 ≤ Ct * Real.exp (-c * (n : ℝ) ^ δ) by positivity)
    nlinarith
  calc
    _ ≤ (2 * Cg + Ct) * ((n : ℝ) * Real.exp (-c * (n : ℝ) ^ δ)) := hstep
    _ ≤ (2 * Cg + Ct) * (B * Real.exp (-(c / 2) * (n : ℝ) ^ δ)) :=
      mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ ≤ _ := by nlinarith

/-- The weighted rigidity inequality of Appendix C. Both structural constants precede `η`,
the forcing tolerance and the temperature. This theorem supplies the
displayed weighted inequality. Exterior prefix and suffix geometry is separate. -/
theorem full_law_weighted_rigidity (hRig : External.LongRangeRigidityLocallyUniform)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ ηstar astar : ℝ, 0 < ηstar ∧ 0 < astar ∧
      ∀ η : ℝ, 0 < η → η ≤ ηstar → ∀ ε : ℝ, 0 < ε →
      ∀ β : ℝ, 0 < β → ∀ θ : PhysicalCutoff,
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ p : Parameters, p.val.2 = s → p.val.1 = β →
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
  intro η hη hηstar ε hε β hβ θ
  have hη1 : η ≤ 1 / 4 := hηstar.trans (min_le_left _ _)
  have hηu : η / 2 ≤ (1 - min s 1 / 2) / 4 := by
    have hh := hηstar.trans (min_le_right _ _)
    dsimp [u] at hh
    linarith
  obtain ⟨Ct, ct, hCt, hct, ht⟩ := physical_goodBlock_probability hRig s hs hs1
    hη hη1 hηu β β hβ le_rfl
  obtain ⟨z, _, _, _, hz, _, _, _, hnorm⟩ :=
    InterpolatingDensities.penalty_support_and_normalizer s β ε hs hs1 hβ hε θ
  obtain ⟨K, hK, hw⟩ := tilted_weighted_event s β ε hs hs1 hβ hε θ
  let δ := a * η
  have hδ : 0 < δ := mul_pos ha hη
  obtain ⟨B, hB, hb⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := 1) (c := ct / 2) (c' := ct / 4) hδ (by linarith)
  refine ⟨K * Real.sqrt (z⁻¹ * Ct) * (B + 1), ct / 4, by positivity, by positivity, ?_⟩
  intro p hps hpβ N n hn2 hsize _ hn
  have hN : 2 ≤ (N : ℕ) := by omega
  have hnN : (n : ℕ) ≤ (N : ℕ) / 2 := by omega
  let μ := tiltedParticleMeasure p N n hn θ ε true
  let E : Set (Riesz1.Configuration N) := {X | finiteGapBlock X ∉ goodBlockEvent s n N η}
  have hfinite : Measurable (finiteGapBlock (N := N) (K := n)) :=
    measurable_pi_iff.mpr (fun i => Riesz1.measurable_gap i.val)
  have hE : MeasurableSet E := (measurableSet_goodBlockEvent s n N η).compl.preimage hfinite
  have hbase : (gibbsMeasure p N) E ≤ ENNReal.ofReal (Ct * Real.exp (-ct * (n : ℝ) ^ δ)) := by
    simpa only [δ, a, u, mul_comm η] using
      ht p hps (by rw [hpβ]) (by rw [hpβ]) N n hN hn2 hnN
  have htail : μ E ≤ ENNReal.ofReal (z⁻¹ * Ct * Real.exp (-ct * (n : ℝ) ^ δ)) := by
    apply (internal_tilted_event_le p N n hn θ ε hz
      (hnorm p hps hpβ N n hN hn).2 E hE).trans
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
  refine (hw p hps hpβ N n hN hn E hE).trans (ENNReal.ofReal_le_ofReal ?_)
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

end Riesz2.InterpolantLocalLaws
