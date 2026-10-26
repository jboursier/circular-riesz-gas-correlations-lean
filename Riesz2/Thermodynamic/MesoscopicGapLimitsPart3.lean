/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.MesoscopicGapLimitsPart2
public import Riesz2.ToMathlib.CoordinateLogConcaveDensity
public import Riesz2.DecayLong.MesoscopicVariancePart2
public import Riesz1.Rigidity.GapLawMarginalLaw
import Riesz2.Frozen.External.LogConcaveConvergenceProof

/-!
# Proper-block densities for mesoscopic gap limits

The affine marginalization step of the proof of Corollary 1.1. Cumulative coordinates
and their physical law are reused literally from Riesz1.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Riesz2

/-- See the proof of Corollary 1.1 in the paper, affine marginalization:
every cumulative offset, including in a two-particle system, has a normalized
Borel log-concave density. -/
theorem anchoredCoordinate_logConcaveDensity (P : Riesz1.Parameters)
    (n : ℕ) (i : Fin (n + 1)) :
    ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧
      (∫⁻ x, ENNReal.ofReal (f x)) = 1 ∧
      ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) ∧
      (Riesz1.anchoredLaw P (n + 1)).map (fun y => y i) =
        volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
  let c := (Riesz1.partitionFunction P (n + 1).succPNat).toReal⁻¹
  let V := fun y => P.val.1 * Riesz1.anchoredEnergy (Riesz1.parametersExponent P) (n + 1) y
  have hc : 0 < c := inv_pos.mpr (ENNReal.toReal_pos
    (Riesz1.partitionFunction_pos P _).ne' (Riesz1.partitionFunction_lt_top P _).ne)
  have hV : ConvexOn ℝ (Riesz1.anchoredDomain (n + 1)) V :=
    (Riesz1.convexOn_anchoredEnergy _ _).smul P.2.1.le
  have hbounded : Bornology.IsBounded (Riesz1.anchoredDomain (n + 1)) := by
    apply (isCompact_univ_pi (fun _ : Fin (n + 1) => isCompact_Icc (a := (0 : ℝ)) (b := 1))).isBounded.subset
    intro y hy j _
    exact ⟨(hy.1 j).1.le, (hy.1 j).2.le⟩
  have hlaw : Riesz1.anchoredLaw P (n + 1) = volume.withDensity
      (fun y => ENNReal.ofReal ((Riesz1.anchoredDomain (n + 1)).indicator
        (fun z => c * Real.exp (-V z)) y)) := by
    rw [Riesz1.anchoredLaw_eq_extendedDensity]
    congr 1
    ext y
    unfold Riesz1.extendedAnchoredProbabilityDensity
    by_cases hy : y ∈ Riesz1.anchoredDomain (n + 1)
    · rw [indicator_of_mem hy, indicator_of_mem hy]
      unfold Riesz1.anchoredProbabilityDensity V c
      rw [neg_mul]
    · rw [indicator_of_notMem hy, indicator_of_notMem hy]
  have hprob : IsProbabilityMeasure (volume.withDensity
      (fun y => ENNReal.ofReal ((Riesz1.anchoredDomain (n + 1)).indicator
        (fun z => c * Real.exp (-V z)) y))) := by
    rw [← hlaw]
    exact Riesz1.isProbabilityMeasure_anchoredLaw P _
  obtain ⟨f, hfm, hf0, hf1, hfLog, hfLaw⟩ :=
    exists_coordinate_logConcaveDensity (Riesz1.anchoredDomain (n + 1))
      (Riesz1.isOpen_anchoredDomain _) hbounded V hV c hc i
  exact ⟨f, hfm, hf0, hf1, hfLog, by rwa [← hlaw] at hfLaw⟩

/-- A proper span starting at zero is a scaled cumulative coordinate starting at zero.
This identity holds at every configuration, without measure-theoretic exceptions. -/
lemma cyclicGapSum_eq_anchoredCoordinate (n : ℕ) (i : Fin (n + 1))
    (X : Riesz1.Configuration (n + 1).succPNat) :
    cyclicGapSum (n + 1).succPNat ⟨0, by simp⟩ (i.val + 1) (gapVector X) =
      (n + 2 : ℝ) * (Riesz1.anchorCoords (n + 1) X.val).2 i := by
  rw [cyclicGapSum_zero_eq_span X (i.val + 1) (by simp),
    Riesz1.cyclicLift_eq_anchor_add, Riesz1.cyclicLift_eq_anchor_add]
  have hi : ((i.val + 1 : ℕ) : ℤ) = ((i.succ : Fin ((n + 1).succPNat : ℕ)) : ℕ) := by simp
  have hz : Riesz1.anchoredCyclicOffset (n + 1)
      (Riesz1.anchorCoords (n + 1) X.val).2 0 = 0 := by
    simpa [Riesz1.anchorVector, Nat.succPNat] using
      Riesz1.anchoredCyclicOffset_natCast (n + 1)
        (Riesz1.anchorCoords (n + 1) X.val).2 (0 : Fin (n + 2))
  rw [hi, Riesz1.anchoredCyclicOffset_natCast (n + 1) _ i.succ, hz]
  simp only [Riesz1.anchorVector, Fin.cons_succ, add_zero, add_sub_cancel_left,
    Nat.succPNat_coe, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
  ring

/-- See the proof of Corollary 1.1 in the paper, physical affine
marginalization. Every proper cyclic span and every positive affine
normalization has a normalized Borel log-concave density on the real line. -/
theorem proper_cyclicGapSum_affine_logConcaveDensity
    (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (K : ℕ) (hK : 1 ≤ K) (hKN : K < (N : ℕ))
    (j : Fin (N : ℕ)) (a b : ℝ) (ha : 0 < a) :
    ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧
      (∫⁻ x, ENNReal.ofReal (f x)) = 1 ∧
      ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) ∧
      (gapLaw (ofLong β s) N).map (fun g => a * cyclicGapSum N j K g + b) =
        volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
  obtain ⟨n, hN⟩ : ∃ n : ℕ, N = (n + 1).succPNat := by
    refine ⟨(N : ℕ) - 2, PNat.eq ?_⟩
    simp only [Nat.succPNat_coe]
    omega
  subst N
  let i : Fin (n + 1) := ⟨K - 1, by simp only [Nat.succPNat_coe] at hKN; omega⟩
  have hi : i.val + 1 = K := by dsimp [i]; omega
  obtain ⟨f, hfm, hf0, hf1, hfLog, hfLaw⟩ :=
    anchoredCoordinate_logConcaveDensity (longParameters β s) n i
  obtain ⟨g, hgm, hg0, hg1, hgLog, hgLaw⟩ := exists_affine_logConcaveDensity
    f hfm hf0 hf1 hfLog (a * (n + 2)) b (by positivity)
  refine ⟨g, hgm, hg0, hg1, hgLog, ?_⟩
  have hz := congrArg (fun μ : Measure ℝ => μ.map (fun x => a * x + b))
    (cyclicGapSum_law_eq_zero β s (n + 1).succPNat j K)
  rw [Measure.map_map (by fun_prop) (measurable_cyclicGapSum _ _ _),
    Measure.map_map (by fun_prop) (measurable_cyclicGapSum _ _ _)] at hz
  rw [show (fun g => a * cyclicGapSum (n + 1).succPNat j K g + b) =
      (fun x => a * x + b) ∘ cyclicGapSum (n + 1).succPNat j K from rfl, hz]
  change ((gibbsMeasure (ofLong β s) (n + 1).succPNat).map Riesz1.gapVector).map _ = _
  have hmeas : Measurable ((fun x : ℝ => a * x + b) ∘
      cyclicGapSum (n + 1).succPNat ⟨0, by simp⟩ K) :=
    ((measurable_id.const_mul a).add_const b).comp (measurable_cyclicGapSum _ _ K)
  rw [Measure.map_map hmeas (Riesz1.measurable_gapVector _), gibbsMeasure_ofLong]
  have hpoint : (fun X : Riesz1.Configuration (n + 1).succPNat =>
      a * cyclicGapSum (n + 1).succPNat ⟨0, by simp⟩ K (gapVector X) + b) =
      ((fun x => (a * (n + 2)) * x + b) ∘ (fun y => y i)) ∘
        (fun X => (Riesz1.anchorCoords (n + 1) X.val).2) := by
    ext X
    rw [← hi, cyclicGapSum_eq_anchoredCoordinate]
    simp only [Function.comp_def]
    ring
  change (Riesz1.gibbsMeasure (longParameters β s) (n + 1).succPNat).map
    (fun X => a * cyclicGapSum (n + 1).succPNat ⟨0, by simp⟩ K (gapVector X) + b) = _
  rw [hpoint, ← Measure.map_map (by fun_prop)
      ((Riesz1.measurable_anchorCoords_config _).snd),
    Riesz1.map_snd_gibbsMeasure]
  have he := Measure.map_map (μ := Riesz1.anchoredLaw (longParameters β s) (n + 1))
    (show Measurable (fun x : ℝ => (a * (n + 2)) * x + b) by fun_prop)
    (show Measurable (fun y : Fin (n + 1) → ℝ => y i) from measurable_pi_apply i)
  exact he.symm.trans (by rw [hfLaw]; exact hgLaw)

/-- See the proof of Corollary 1.1 in the paper: the eventual density
input to the finite-block variance theorem. Its proper-block premise follows from mesoscopicity. -/
theorem mesoscopic_finiteGapBlock_logConcaveDensity
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (N K : ℕ → ℕ+)
    (hK : Tendsto (fun j => (K j : ℕ)) atTop atTop)
    (hKN : Tendsto (fun j => (K j : ℝ) / (N j : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ j in atTop, ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧
      ConcaveOn ℝ (Function.support f) (fun x => Real.log (f x)) ∧
      (gibbsMeasure (ofLong β s) (N j)).map
        (fun X => ((∑ i : Fin (K j : ℕ), finiteGapBlock X i) - (K j : ℝ)) /
          (K j : ℝ) ^ (s.val / 2)) =
        volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
  filter_upwards [mesoscopic_pairs_eventually_admissible (fun j => (K j : ℕ)) N hK hKN]
    with j hj
  have hproper : (K j : ℕ) < (N j : ℕ) := by omega
  let a := ((K j : ℝ) ^ (s.val / 2))⁻¹
  have ha : 0 < a := inv_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)
  obtain ⟨f, hfm, hf0, _, hfLog, hfLaw⟩ := proper_cyclicGapSum_affine_logConcaveDensity
    β s (N j) (K j : ℕ) (K j).pos hproper ⟨0, (N j).pos⟩ a (-a * (K j : ℝ)) ha
  have hs : Function.support f = {x | 0 < f x} := by
    ext x
    exact ⟨fun hx => lt_of_le_of_ne (hf0 x) (Ne.symm hx), fun hx => hx.ne'⟩
  refine ⟨f, hfm, hf0, hs.symm ▸ hfLog, ?_⟩
  have hV : Measurable (gapVector (N := N j)) := Riesz1.measurable_gapVector _
  unfold gapLaw at hfLaw
  rw [Measure.map_map (((measurable_cyclicGapSum _ _ _).const_mul a).add_const _) hV] at hfLaw
  have he : (fun X : Riesz1.Configuration (N j) =>
      a * cyclicGapSum (N j) ⟨0, (N j).pos⟩ (K j : ℕ) (gapVector X) + -a * (K j : ℝ)) =
      (fun X => ((∑ i : Fin (K j : ℕ), finiteGapBlock X i) - (K j : ℝ)) /
        (K j : ℝ) ^ (s.val / 2)) := by
    ext X
    rw [cyclicGapSum_zero_eq_finiteGapBlock]
    dsimp [a]
    ring
  simpa only [Function.comp_def, he] using hfLaw

/-- See the proof of Corollary 1.1 in the paper, variance asymptotic
for the finite block, along every pair of positive integer sequences. -/
theorem mesoscopic_finiteGapBlock_variance_limit
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (N K : ℕ → ℕ+)
    (hK : Tendsto (fun j => (K j : ℕ)) atTop atTop)
    (hKN : Tendsto (fun j => (K j : ℝ) / (N j : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun j =>
      let S := fun X : Riesz1.Configuration (N j) =>
        ∑ i : Fin (K j : ℕ), finiteGapBlock X i
      let h := MesoscopicVariance.integrable_finiteGapBlock_sum (ofLong β s) (N j) (K j)
      (Riesz1.variance (gibbsMeasure (ofLong β s) (N j)) S h).toReal /
        (K j : ℝ) ^ s.val) atTop (𝓝 (Riesz1.countVariance (longParameters β s))) :=
  MesoscopicVariance.variance_limit_of_logconcave_densities_internal
    External.logConcaveConvergence β s N K hK hKN
    (mesoscopic_finiteGapBlock_logConcaveDensity β s N K hK hKN)

/-- The entire span law agrees with the block law, after
cyclic relabelling. This bridge permits transporting integrals and variance
between the gap-coordinate and particle-configuration carriers. -/
lemma cyclicGapSum_law_eq_finiteGapBlock
    (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N K : ℕ+) (i : Fin (N : ℕ)) :
    (gapLaw (ofLong β s) N).map (cyclicGapSum N i (K : ℕ)) =
      (gibbsMeasure (ofLong β s) N).map
        (fun X => ∑ j : Fin (K : ℕ), finiteGapBlock X j) := by
  rw [cyclicGapSum_law_eq_zero]
  unfold gapLaw
  have hV : Measurable (gapVector (N := N)) := Riesz1.measurable_gapVector N
  rw [Measure.map_map (measurable_cyclicGapSum N _ _) hV]
  congr 1
  exact funext (cyclicGapSum_zero_eq_finiteGapBlock N K)

/-- See the proof of Corollary 1.1 in the paper: the extended variance
of any labelled span equals that of the particle block. -/
theorem cyclicGapSum_variance_eq_finiteGapBlock
    (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N K : ℕ+) (i : Fin (N : ℕ)) :
    Riesz1.variance (gapLaw (ofLong β s) N) (cyclicGapSum N i (K : ℕ))
      (integrable_cyclicGapSum β s N i (K : ℕ)) =
    Riesz1.variance (gibbsMeasure (ofLong β s) N)
      (fun X => ∑ j : Fin (K : ℕ), finiteGapBlock X j)
      (MesoscopicVariance.integrable_finiteGapBlock_sum (ofLong β s) N K) := by
  have hS : Measurable (fun X : Riesz1.Configuration N =>
      ∑ j : Fin (K : ℕ), finiteGapBlock X j) := by
    simp_rw [MesoscopicVariance.finiteGapBlock_sum_eq_blockLength]
    exact Riesz1.measurable_blockLength 0 K
  rw [Riesz1.variance_eq_lintegral_map (measurable_cyclicGapSum N i (K : ℕ)),
    Riesz1.variance_eq_lintegral_map hS, cyclicGapSum_law_eq_finiteGapBlock β s N K i]

/-- See the proof of Corollary 1.1 in the paper, the two-parameter
variance asymptotic for arbitrary integer block lengths and arbitrary varying
labels. Initial empty, full, and repeated blocks are allowed. -/
theorem mesoscopic_cyclicGapSum_variance_limit
    (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ → ℕ+) (K : ℕ → ℕ) (i : ∀ j, Fin (N j : ℕ))
    (hK : Tendsto K atTop atTop)
    (hKN : Tendsto (fun j => (K j : ℝ) / (N j : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun j => (K j : ℝ) ^ (-s.val) *
      (Riesz1.variance (gapLaw (ofLong β s) (N j))
        (cyclicGapSum (N j) (i j) (K j))
        (integrable_cyclicGapSum β s (N j) (i j) (K j))).toReal)
      atTop (𝓝 (Riesz1.countVariance (longParameters β s))) := by
  let K' : ℕ → ℕ+ := fun j => ⟨max 1 (K j), by omega⟩
  have he : ∀ᶠ j in atTop, (K' j : ℕ) = K j := by
    filter_upwards [hK.eventually_ge_atTop 1] with j hj
    exact max_eq_right hj
  have hK' : Tendsto (fun j => (K' j : ℕ)) atTop atTop :=
    hK.congr' (he.mono fun _ h => h.symm)
  have hKN' : Tendsto (fun j => (K' j : ℝ) / (N j : ℝ)) atTop (𝓝 0) := by
    apply hKN.congr'
    filter_upwards [he] with j hj
    exact congrArg (fun k : ℕ => (k : ℝ) / (N j : ℝ)) hj.symm
  have h := mesoscopic_finiteGapBlock_variance_limit β s N K' hK' hKN'
  apply h.congr'
  filter_upwards [he] with j hj
  dsimp only
  rw [← cyclicGapSum_variance_eq_finiteGapBlock β s (N j) (K' j) (i j)]
  have hjR : (K' j : ℝ) = (K j : ℝ) := congrArg (fun k : ℕ => (k : ℝ)) hj
  rw [hjR, hj, Real.rpow_neg (Nat.cast_nonneg (K j))]
  ring

/-- The Gaussian central limit theorem and variance asymptotic in the proof
of Corollary 1.1 hold along every mesoscopic pair, with finite moments and
label-independent variance. The moment step applies Proposition 2(c) of
Cule–Samworth through the log-concave convergence result. -/
theorem hyper_riesz_mesoscopic_gaps (s : Riesz1.RieszExponent) (β : InverseTemperature)
    (K : ℕ → ℕ) (N : ℕ → ℕ+) (i : ∀ j, Fin (N j : ℕ))
    (hK : Tendsto K atTop atTop)
    (hKN : Tendsto (fun j => (K j : ℝ) / (N j : ℝ)) atTop (𝓝 0)) :
    ConvergesInLawAlong atTop
      (fun j => (gapLaw (ofLong β s) (N j)).map
        (fun g => (K j : ℝ) ^ (-s.val / 2) * (cyclicGapSum (N j) (i j) (K j) g - K j)))
      (Riesz1.normalLaw (NNReal.mk (Riesz1.countVariance (longParameters β s))
        (companionCountVariance_nonneg β s))) ∧
    (∀ j, Riesz1.variance (gapLaw (ofLong β s) (N j))
      (cyclicGapSum (N j) (i j) (K j))
      (integrable_cyclicGapSum β s (N j) (i j) (K j)) < ⊤) ∧
    Tendsto (fun j => (K j : ℝ) ^ (-s.val) *
      (Riesz1.variance (gapLaw (ofLong β s) (N j))
        (cyclicGapSum (N j) (i j) (K j))
        (integrable_cyclicGapSum β s (N j) (i j) (K j))).toReal)
      atTop (𝓝 (Riesz1.countVariance (longParameters β s))) ∧
    (∀ j (k : Fin (N j : ℕ)),
      Riesz1.variance (gapLaw (ofLong β s) (N j))
        (cyclicGapSum (N j) (i j) (K j))
        (integrable_cyclicGapSum β s (N j) (i j) (K j)) =
      Riesz1.variance (gapLaw (ofLong β s) (N j))
        (cyclicGapSum (N j) k (K j))
        (integrable_cyclicGapSum β s (N j) k (K j))) := by
  refine ⟨mesoscopic_gapCLT_labels β s N K i hK hKN,
    fun j => (cyclicGapSum_variance_finite_and_label_independent β s (N j) (i j) (K j)).1,
    mesoscopic_cyclicGapSum_variance_limit β s N K i hK hKN, ?_⟩
  intro j k
  exact (cyclicGapSum_variance_finite_and_label_independent β s (N j) (i j) (K j)).2.trans
    (cyclicGapSum_variance_finite_and_label_independent β s (N j) k (K j)).2.symm

end Riesz2

end
