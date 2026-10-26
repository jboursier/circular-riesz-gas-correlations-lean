/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.MesoscopicGapLimits
public import Riesz2.Frozen.GapLaw
public import Riesz2.Thermodynamic.FiniteCountLimitsPart2
public import Riesz2.ToMathlib.WeakLawScaling
public import Riesz1.CLT.SelectionCyclic
public import Riesz2.DecayLong.MesoscopicVariance
import Riesz2.Sanity.FiniteLaws

/-!
# Arbitrary-pair span central limit theorem

The companion volume-indexed gap CLT is transferred to arbitrary pairs and connected
with the cyclic sums. This supplies the distributional part of the proof of Corollary
1.1.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Riesz2

/-- A cyclic span is measurable on the finite gap-coordinate space. -/
lemma measurable_cyclicGapSum (N : ℕ+) (i : Fin (N : ℕ)) (K : ℕ) :
    Measurable (cyclicGapSum N i K) := by
  unfold cyclicGapSum
  exact Finset.measurable_sum _ fun _ _ => measurable_pi_apply _

/-- The profile-normalized span is measurable even at sizes outside the eventual CLT range. -/
lemma measurable_profileNormalizedSpan (s : Riesz1.RieszExponent) (N : ℕ+) (K : ℕ) :
    Measurable (fun X : Riesz1.Configuration N =>
      (cyclicGapSum N ⟨0, N.pos⟩ K (gapVector X) - K) /
        Real.sqrt ((N : ℝ) ^ s.val *
          Riesz1.periodicZeta s (((K : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle))) :=
  (((measurable_cyclicGapSum N _ K).comp (Riesz1.measurable_gapVector N)).sub_const _).div_const _

/-- Internal full-volume form with only eventual proper-block admissibility. -/
theorem gapProfileCLT_sections (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (k : ℕ+ → ℕ) (hkTop : Tendsto k atTop atTop)
    (hk : ∀ᶠ N : ℕ+ in atTop, 1 ≤ k N ∧ k N ≤ (N : ℕ) / 2) :
    ConvergesInLawAlong atTop
      (fun N : ℕ+ => (gibbsMeasure (ofLong β s) N).map
        (fun X => (cyclicGapSum N ⟨0, N.pos⟩ (k N) (gapVector X) - k N) /
          Real.sqrt ((N : ℝ) ^ s.val *
            Riesz1.periodicZeta s (((k N : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle))))
      (Riesz1.normalLaw (NNReal.mk (Riesz1.countVariance (longParameters β s))
        (companionCountVariance_nonneg β s))) := by
  let k' : ℕ+ → ℕ := fun N => min (max 1 (k N)) (max 1 ((N : ℕ) / 2))
  have hvalid : ∀ N : ℕ+, 2 ≤ (N : ℕ) → 1 ≤ k' N ∧ k' N ≤ (N : ℕ) / 2 := by
    intro N hN
    dsimp [k']
    omega
  have he : ∀ᶠ N : ℕ+ in atTop, k' N = k N := by
    filter_upwards [hk] with N hN
    dsimp [k']
    omega
  have hk'Top : Tendsto (fun n => k' (Riesz1.particleNumber n)) atTop atTop :=
    (hkTop.congr' (he.mono fun _ h => h.symm)).comp tendsto_particleNumber_atTop
  have hconv := (companionGapCLT β s k' hvalid hk'Top).2
  simp only [ConvergesInLawAlong] at hconv
  unfold Riesz1.normalizedGap at hconv
  let r : ℕ+ → ℕ := fun N => (N : ℕ) - 2
  have hr : Tendsto r atTop atTop := by
    apply tendsto_atTop.mpr
    intro m
    filter_upwards [eventually_ge_atTop (⟨m + 2, by omega⟩ : ℕ+)] with N hN
    change m ≤ (N : ℕ) - 2
    have : m + 2 ≤ (N : ℕ) := hN
    omega
  have hPN : ∀ N : ℕ+, 2 ≤ (N : ℕ) → Riesz1.particleNumber (r N + 1) = N := by
    intro N hN
    apply PNat.eq
    change (N : ℕ) - 2 + 1 + 1 = (N : ℕ)
    omega
  refine ⟨fun N => ?_, hconv.2.1, fun f => ?_⟩
  · dsimp only
    have : IsProbabilityMeasure (gibbsMeasure (ofLong β s) N) := by
      rw [gibbsMeasure_ofLong]
      exact (Riesz1.modelWellDefined (longParameters β s) N).2.2
    exact (Measure.isProbabilityMeasure_map_iff
      (measurable_profileNormalizedSpan s N (k N)).aemeasurable).mpr inferInstance
  · apply ((hconv.2.2 f).comp hr).congr'
    filter_upwards [he, eventually_ge_atTop (2 : ℕ+)] with N heN hN
    have hN' : 2 ≤ (N : ℕ) := hN
    simp only [Function.comp_def]
    have htype : Riesz1.particleNumber (r N + 1) = N := hPN N hN'
    rw [htype, heN]
    congr 1
    apply Measure.map_congr
    filter_upwards [] with X
    rw [cyclicGapSum_zero_eq_span X (k N) ((heN ▸ hvalid N hN').2.trans
      (Nat.div_le_self _ _))]
    rfl

/-- The half-cycle filler grows and is admissible at every size at least two. -/
lemma halfCycle_filler_limits :
    Tendsto (fun N : ℕ+ => (N : ℕ) / 2) atTop atTop ∧
    (∀ᶠ N : ℕ+ in atTop, 1 ≤ (N : ℕ) / 2 ∧ (N : ℕ) / 2 ≤ (N : ℕ) / 2) := by
  constructor
  · apply tendsto_atTop.mpr
    intro m
    filter_upwards [eventually_ge_atTop (⟨2 * m + 1, by omega⟩ : ℕ+)] with N hN
    change m ≤ (N : ℕ) / 2
    have : 2 * m + 1 ≤ (N : ℕ) := hN
    omega
  · filter_upwards [eventually_ge_atTop (2 : ℕ+)] with N hN
    have : 2 ≤ (N : ℕ) := hN
    omega

/-- See the proof of Corollary 1.1 in the paper: the companion profile-normalized CLT
along arbitrary pairs. Only eventual half-cycle admissibility and diverging gap counts are needed. -/
theorem gapProfileCLT_pairs (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ → ℕ+) (K : ℕ → ℕ) (hK : Tendsto K atTop atTop)
    (hvalid : ∀ᶠ j in atTop, 1 ≤ K j ∧ K j ≤ (N j : ℕ) / 2) :
    ConvergesInLawAlong atTop
      (fun j => (gibbsMeasure (ofLong β s) (N j)).map
        (fun X => (cyclicGapSum (N j) ⟨0, (N j).pos⟩ (K j) (gapVector X) - K j) /
          Real.sqrt ((N j : ℝ) ^ s.val *
            Riesz1.periodicZeta s (((K j : ℝ) / (N j : ℝ) : ℝ) : UnitAddCircle))))
      (Riesz1.normalLaw (NNReal.mk (Riesz1.countVariance (longParameters β s))
        (companionCountVariance_nonneg β s))) := by
  have hN : Tendsto N atTop atTop := by
    apply tendsto_atTop.mpr
    intro M
    filter_upwards [hK.eventually_ge_atTop (M : ℕ), hvalid] with j hj hv
    change (M : ℕ) ≤ (N j : ℕ)
    omega
  refine ⟨fun j => ?_, by exact ProbabilityTheory.instIsProbabilityMeasureGaussianReal _ _, fun f => ?_⟩
  · dsimp only
    have : IsProbabilityMeasure (gibbsMeasure (ofLong β s) (N j)) := by
      rw [gibbsMeasure_ofLong]
      exact (Riesz1.modelWellDefined (longParameters β s) (N j)).2.2
    exact (Measure.isProbabilityMeasure_map_iff
      (measurable_profileNormalizedSpan s (N j) (K j)).aemeasurable).mpr inferInstance
  · exact tendsto_pairs_of_sections (fun (_ : ℕ+) (k : ℕ) => k)
      (fun N (k : ℕ) => 1 ≤ k ∧ k ≤ (N : ℕ) / 2)
      (fun N (k : ℕ) => ∫ x, f x ∂((gibbsMeasure (ofLong β s) N).map
        (fun X => (cyclicGapSum N ⟨0, N.pos⟩ k (gapVector X) - k) /
          Real.sqrt ((N : ℝ) ^ s.val *
            Riesz1.periodicZeta s (((k : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle)))))
      atTop (pure True) _ (fun N => (N : ℕ) / 2)
      halfCycle_filler_limits.1 (tendsto_pure.mpr (halfCycle_filler_limits.2.mono
        (fun _ h => propext (iff_true_intro h))))
      (fun k hk hv => (gapProfileCLT_sections β s k hk
        (hv.eventually (mem_pure.mpr rfl) |>.mono fun _ h => of_eq_true h.symm)).2.2 f)
      N K hN hK (tendsto_pure.mpr (hvalid.mono fun _ h => propext (iff_true_intro h)))

/-- See the proof of Corollary 1.1 in the paper, the span CLT with the power
normalization of the paper, along every mesoscopic pair, including sequences with exceptional initial sizes. -/
theorem mesoscopic_gapCLT_pairs (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ → ℕ+) (K : ℕ → ℕ) (hK : Tendsto K atTop atTop)
    (hKN : Tendsto (fun j => (K j : ℝ) / (N j : ℝ)) atTop (𝓝 0)) :
    ConvergesInLawAlong atTop
      (fun j => (gibbsMeasure (ofLong β s) (N j)).map
        (fun X => (K j : ℝ) ^ (-s.val / 2) *
          (cyclicGapSum (N j) ⟨0, (N j).pos⟩ (K j) (gapVector X) - K j)))
      (Riesz1.normalLaw (NNReal.mk (Riesz1.countVariance (longParameters β s))
        (companionCountVariance_nonneg β s))) := by
  have hv := mesoscopic_pairs_eventually_admissible K N hK hKN
  let K' : ℕ → ℕ+ := fun j => ⟨max 1 (K j), by omega⟩
  have he : ∀ᶠ j in atTop, (K' j : ℕ) = K j := by
    filter_upwards [hK.eventually_ge_atTop 1] with j hj
    exact max_eq_right hj
  have hKN' : Tendsto (fun j => (K' j : ℝ) / (N j : ℝ)) atTop (𝓝 0) := by
    apply hKN.congr'
    filter_upwards [he] with j hj
    simp only [show (K' j : ℝ) = (K j : ℝ) by exact_mod_cast hj]
  have hf : Tendsto (fun j => Real.sqrt ((N j : ℝ) ^ s.val *
      Riesz1.periodicZeta s (((K j : ℝ) / (N j : ℝ) : ℝ) : UnitAddCircle)) /
      (K j : ℝ) ^ (s.val / 2)) atTop (𝓝 1) := by
    apply (mesoscopic_gap_sqrt_ratio_limit s K' N hKN').congr'
    filter_upwards [he] with j hj
    simp only [show (K' j : ℝ) = (K j : ℝ) by exact_mod_cast hj]
  have hp := convergesInLawAlong_map_mul (gapProfileCLT_pairs β s N K hK hv) hf
  simp only [ConvergesInLawAlong, one_mul, Measure.map_id'] at hp
  refine ⟨fun j => ?_, hp.2.1, fun f => ?_⟩
  · dsimp only
    have : IsProbabilityMeasure (gibbsMeasure (ofLong β s) (N j)) := by
      rw [gibbsMeasure_ofLong]
      exact (Riesz1.modelWellDefined (longParameters β s) (N j)).2.2
    exact (Measure.isProbabilityMeasure_map_iff
      ((((measurable_cyclicGapSum (N j) _ (K j)).comp
        (Riesz1.measurable_gapVector (N j))).sub_const _).const_mul _).aemeasurable).mpr
      inferInstance
  · apply (hp.2.2 f).congr'
    filter_upwards [hv] with j hj
    have hN : (0 : ℝ) < N j := by exact_mod_cast (N j).pos
    have hKj : (0 : ℝ) < K j := by exact_mod_cast hj.1
    have ht : (K j : ℝ) / (N j : ℝ) < 1 := by
      rw [div_lt_one hN]
      exact_mod_cast (show K j < (N j : ℕ) by have := (N j).pos; omega)
    have hd : 0 < Real.sqrt ((N j : ℝ) ^ s.val *
        Riesz1.periodicZeta s (((K j : ℝ) / (N j : ℝ) : ℝ) : UnitAddCircle)) :=
      Real.sqrt_pos.mpr (mul_pos (Real.rpow_pos_of_pos hN _)
        ((companionVarianceProfile s).1 _ (div_pos hKj hN) ht))
    congr 1
    rw [Measure.map_map (by fun_prop) (measurable_profileNormalizedSpan s (N j) (K j))]
    apply Measure.map_congr
    filter_upwards [] with X
    dsimp only [Function.comp_def]
    rw [show -s.val / 2 = -(s.val / 2) by ring, Real.rpow_neg hKj.le]
    field_simp

/-- The cyclic sum agrees with the library periodic extension, including sums longer
than one period. -/
lemma cyclicGapSum_eq_sum_gapOf (N : ℕ+) (i : Fin (N : ℕ)) (K : ℕ)
    (g : Fin (N : ℕ) → ℝ) :
    cyclicGapSum N i K g =
      ∑ a ∈ Finset.range K, Riesz1.gapOf g (((i : ℕ) : ℤ) + (a : ℤ)) := by
  unfold cyclicGapSum
  apply Finset.sum_congr rfl
  intro a _
  unfold Riesz1.gapOf
  congr 1

/-- Shifting the origin of the library gap vector is the label shift. -/
lemma cyclicGapSum_zero_shiftFin (N : ℕ+) (i : Fin (N : ℕ)) (K : ℕ)
    (g : Fin (N : ℕ) → ℝ) :
    cyclicGapSum N ⟨0, N.pos⟩ K (Riesz1.shiftFin N (i : ℕ) g) =
      cyclicGapSum N i K g := by
  simp only [cyclicGapSum_eq_sum_gapOf, Nat.cast_zero, zero_add,
    Riesz1.gapOf_shiftFin]

/-- The long-range finite gap law is invariant under the library's arbitrary cyclic shift. -/
lemma longGapLaw_map_shiftFin (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (i : ℕ) :
    (gapLaw (ofLong β s) N).map (Riesz1.shiftFin N (i : ℤ)) = gapLaw (ofLong β s) N := by
  have hμ : gibbsMeasure (ofLong β s) N = Riesz1.gibbsMeasure (longParameters β s) N :=
    gibbsMeasure_ofLong β s N
  unfold gapLaw
  rw [hμ]
  change ((Riesz1.gibbsMeasure (longParameters β s) N).map Riesz1.gapVector).map
    (Riesz1.shiftFin N (i : ℤ)) = (Riesz1.gibbsMeasure (longParameters β s) N).map Riesz1.gapVector
  rw [Measure.map_map (Riesz1.measurable_shiftFin _) (Riesz1.measurable_gapVector N)]
  exact Riesz1.map_shiftFin_gibbsMeasure (longParameters β s) hN i

/-- See the proof of Corollary 1.1 in the paper: the law of a finite span is independent
of its starting label. Consequently every moment and every variance is label-independent. -/
theorem cyclicGapSum_law_eq_zero (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (i : Fin (N : ℕ)) (K : ℕ) :
    (gapLaw (ofLong β s) N).map (cyclicGapSum N i K) =
      (gapLaw (ofLong β s) N).map (cyclicGapSum N ⟨0, N.pos⟩ K) := by
  by_cases hN : 2 ≤ (N : ℕ)
  · have h := congrArg (fun μ : Measure (Fin (N : ℕ) → ℝ) =>
        μ.map (cyclicGapSum N ⟨0, N.pos⟩ K)) (longGapLaw_map_shiftFin β s N hN i.val)
    rw [Measure.map_map (measurable_cyclicGapSum N _ K) (Riesz1.measurable_shiftFin _)] at h
    have he : cyclicGapSum N ⟨0, N.pos⟩ K ∘ Riesz1.shiftFin N (i : ℕ) =
        cyclicGapSum N i K := funext (cyclicGapSum_zero_shiftFin N i K)
    rwa [he] at h
  · have hi : i = (⟨0, N.pos⟩ : Fin (N : ℕ)) := Fin.ext (by have := i.isLt; have := N.pos; omega)
    rw [hi]

/-- See the proof of Corollary 1.1 in the paper: the power-normalized CLT under the
finite gap law, with any sequence of starting labels. -/
theorem mesoscopic_gapCLT_labels (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ → ℕ+) (K : ℕ → ℕ) (i : ∀ j, Fin (N j : ℕ))
    (hK : Tendsto K atTop atTop)
    (hKN : Tendsto (fun j => (K j : ℝ) / (N j : ℝ)) atTop (𝓝 0)) :
    ConvergesInLawAlong atTop
      (fun j => (gapLaw (ofLong β s) (N j)).map
        (fun g => (K j : ℝ) ^ (-s.val / 2) * (cyclicGapSum (N j) (i j) (K j) g - K j)))
      (Riesz1.normalLaw (NNReal.mk (Riesz1.countVariance (longParameters β s))
        (companionCountVariance_nonneg β s))) := by
  have he (j : ℕ) :
      (gapLaw (ofLong β s) (N j)).map
        (fun g => (K j : ℝ) ^ (-s.val / 2) * (cyclicGapSum (N j) (i j) (K j) g - K j)) =
      (gibbsMeasure (ofLong β s) (N j)).map
        (fun X => (K j : ℝ) ^ (-s.val / 2) *
          (cyclicGapSum (N j) ⟨0, (N j).pos⟩ (K j) (gapVector X) - K j)) := by
    have h := congrArg (fun μ : Measure ℝ => μ.map
        (fun x => (K j : ℝ) ^ (-s.val / 2) * (x - K j)))
      (cyclicGapSum_law_eq_zero β s (N j) (i j) (K j))
    rw [Measure.map_map (by fun_prop) (measurable_cyclicGapSum (N j) _ _),
      Measure.map_map (by fun_prop) (measurable_cyclicGapSum (N j) _ _)] at h
    simp only [Function.comp_def] at h
    rw [h]
    unfold gapLaw
    have hV : Measurable (gapVector (N := N j)) := Riesz1.measurable_gapVector (N j)
    rw [Measure.map_map (((measurable_cyclicGapSum (N j) _ _).sub_const _).const_mul _) hV]
    rfl
  have h := mesoscopic_gapCLT_pairs β s N K hK hKN
  refine ⟨fun j => ?_, h.2.1, fun f => ?_⟩
  · dsimp only
    rw [he]
    exact h.1 j
  · simpa only [he] using h.2.2 f

/-- Bridge to the finite-block moment API. Full and repeated periods are included. -/
lemma cyclicGapSum_zero_eq_finiteGapBlock (N K : ℕ+) (X : Riesz1.Configuration N) :
    cyclicGapSum N ⟨0, N.pos⟩ (K : ℕ) (gapVector X) =
      ∑ j : Fin (K : ℕ), finiteGapBlock X j := by
  rw [MesoscopicVariance.finiteGapBlock_sum_eq_blockLength,
    Riesz1.blockLength_eq_sum, cyclicGapSum_eq_sum_gapOf]
  apply Finset.sum_congr rfl
  intro a _
  exact (Riesz1.gap_eq_gapOf_gapVector X (0 + (a : ℤ))).symm

/-- All finite cyclic spans have all finite moments, by the block moment theorem
and label invariance. -/
theorem memLp_cyclicGapSum (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (i : Fin (N : ℕ)) (K : ℕ) (q : ℝ≥0∞) :
    MemLp (cyclicGapSum N i K) q (gapLaw (ofLong β s) N) := by
  have hV : Measurable (gapVector (N := N)) := Riesz1.measurable_gapVector N
  have : IsProbabilityMeasure (gibbsMeasure (ofLong β s) N) :=
    FrozenSanity.gibbsMeasure_probability (ofLong β s) N
  have hz : MemLp (cyclicGapSum N ⟨0, N.pos⟩ K) q (gapLaw (ofLong β s) N) := by
    unfold gapLaw
    apply (memLp_map_measure_iff (measurable_cyclicGapSum N _ K).aestronglyMeasurable hV.aemeasurable).mpr
    simp only [Function.comp_def]
    cases K with
    | zero => simpa only [cyclicGapSum, Finset.range_zero, Finset.sum_empty] using
        (memLp_const (0 : ℝ) : MemLp (fun _ : Riesz1.Configuration N => (0 : ℝ)) q (gibbsMeasure (ofLong β s) N))
    | succ k =>
      have h := MesoscopicVariance.finiteGapBlock_sum_memLp (ofLong β s) N ⟨k + 1, by omega⟩ q
      have he : (fun X : Riesz1.Configuration N =>
          cyclicGapSum N ⟨0, N.pos⟩ (k + 1) (gapVector X)) =
          (fun X => ∑ j : Fin (k + 1), finiteGapBlock (K := ⟨k + 1, by omega⟩) X j) :=
        funext (cyclicGapSum_zero_eq_finiteGapBlock N ⟨k + 1, by omega⟩)
      rw [he]
      exact h
  have hid := (memLp_map_measure_iff aestronglyMeasurable_id
    (measurable_cyclicGapSum N ⟨0, N.pos⟩ K).aemeasurable).mpr hz
  rw [← cyclicGapSum_law_eq_zero β s N i K] at hid
  exact (memLp_map_measure_iff aestronglyMeasurable_id
    (measurable_cyclicGapSum N i K).aemeasurable).mp hid

/-- Every finite cyclic span has an integrable first moment. -/
lemma integrable_cyclicGapSum (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (i : Fin (N : ℕ)) (K : ℕ) :
    Integrable (cyclicGapSum N i K) (gapLaw (ofLong β s) N) := by
  have hV : Measurable (gapVector (N := N)) := Riesz1.measurable_gapVector N
  have : IsProbabilityMeasure (gapLaw (ofLong β s) N) := by
    unfold gapLaw
    exact (Measure.isProbabilityMeasure_map_iff hV.aemeasurable).mpr
      (FrozenSanity.gibbsMeasure_probability (ofLong β s) N)
  exact (memLp_cyclicGapSum β s N i K 2).integrable one_le_two

/-- See the proof of Corollary 1.1 in the paper: finite variances are finite
extended integrals and are independent of the label. -/
theorem cyclicGapSum_variance_finite_and_label_independent
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (N : ℕ+)
    (i : Fin (N : ℕ)) (K : ℕ) :
    Riesz1.variance (gapLaw (ofLong β s) N) (cyclicGapSum N i K)
      (integrable_cyclicGapSum β s N i K) < ⊤ ∧
    Riesz1.variance (gapLaw (ofLong β s) N) (cyclicGapSum N i K)
      (integrable_cyclicGapSum β s N i K) =
    Riesz1.variance (gapLaw (ofLong β s) N) (cyclicGapSum N ⟨0, N.pos⟩ K)
      (integrable_cyclicGapSum β s N ⟨0, N.pos⟩ K) := by
  have hV : Measurable (gapVector (N := N)) := Riesz1.measurable_gapVector N
  have : IsProbabilityMeasure (gapLaw (ofLong β s) N) := by
    unfold gapLaw
    exact (Measure.isProbabilityMeasure_map_iff hV.aemeasurable).mpr
      (FrozenSanity.gibbsMeasure_probability (ofLong β s) N)
  exact ⟨(Riesz1.variance_ne_top_of_memLp _ (memLp_cyclicGapSum β s N i K 2)).lt_top,
    Riesz1.variance_eq_of_map_eq (measurable_cyclicGapSum N i K)
      (measurable_cyclicGapSum N ⟨0, N.pos⟩ K) (cyclicGapSum_law_eq_zero β s N i K)
      (integrable_cyclicGapSum β s N i K) (integrable_cyclicGapSum β s N ⟨0, N.pos⟩ K)⟩

end Riesz2

end
