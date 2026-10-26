/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.ConvergenceResult
public import Riesz2.Thermodynamic.LocalTotalVariationFinal
public import Riesz2.Frozen.RepulsionProbability
public import Riesz2.Frozen.OrdinaryGapCauchy

/-!
# Repulsion for labelled Palm gaps

Proposition 1.2: transfer the finite-volume lower tail at label zero through total
variation, then use Palm label-shift invariance. The tail constants are uniform on
compact positive temperature intervals.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace Riesz2

local notation "Gaps" => (ℤ → Ioi (0 : ℝ))
local notation "gapProj" => (fun (k : ℕ) (a : ℤ) (y : Gaps) =>
  (WithLp.toLp 2 (fun j : Fin k => (y (a + (Fin.val j : ℤ)) : ℝ)) : EuclideanSpace ℝ (Fin k)))
local notation "gapMarginal" => (fun (q : ProbabilityMeasure Gaps) (k : ℕ) (a : ℤ) =>
  ProbabilityMeasure.map q (gapProj k a))
local instance repulsionResultConfigurationMeasurableSpace :
    MeasurableSpace LineConfiguration := configurationMeasurableSpace

/-- See Proposition 1.2 of the paper: the event in a one-dimensional
Euclidean block is exactly the event for the labelled positive coordinate. -/
theorem repulsion_gapMarginal_event_internal (q : ProbabilityMeasure Gaps) (i : ℤ) (u : ℝ) :
    (gapMarginal q 1 i).toMeasure {x | x 0 ≤ u} =
      q.toMeasure {y | (y i : ℝ) ≤ u} := by
  rw [ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (continuous_gap_block_projection_internal 1 i).measurable
      (measurableSet_le (by fun_prop) measurable_const)]
  congr 1
  ext y
  change (y (i + (0 : ℤ)) : ℝ) ≤ u ↔ (y i : ℝ) ≤ u
  rw [add_zero]

/-- The proof of Proposition 1.2 of the paper, internal transfer:
choose compact-temperature constants once, pass only label zero through total
variation, and then move that event using invariance under label shifts. -/
theorem repulsion_gap_limit_via_shift_internal (s βlo βhi : ℝ)
    (hs : 0 < s) (hs1 : s ≠ 1) (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ q : ProbabilityMeasure Gaps,
      Tendsto (fun n : ℕ => totalVariation
        (gapMarginal (periodicGapLaw p n.succPNat) 1 0).toMeasure
        (gapMarginal q 1 0).toMeasure) atTop (𝓝 0) →
      (∀ i : ℤ, q.map (gapIndexShift i) = q) →
      ∀ i : ℤ, ∀ u : ℝ, 0 < u → u ≤ 1 →
        q.toMeasure {y | (y i : ℝ) ≤ u} ≤
          ENNReal.ofReal (C * Real.exp (-c * u ^ (-s))) := by
  obtain ⟨C, c, hC, hc, ht⟩ := SingleGapTails.single_gap_tails_density s βlo βhi hs hs1 hlo hle
  refine ⟨c, C, hc, hC, ?_⟩
  intro p hps hpl hph q hTV hshift
  have hzero (u : ℝ) (hu : 0 < u) (hu1 : u ≤ 1) :
      q.toMeasure {y | (y 0 : ℝ) ≤ u} ≤
        ENNReal.ofReal (C * Real.exp (-c * u ^ (-s))) := by
    rw [← repulsion_gapMarginal_event_internal q 0 u]
    let A : Set (EuclideanSpace ℝ (Fin 1)) := {x | x 0 ≤ u}
    let B := ENNReal.ofReal (C * Real.exp (-c * u ^ (-s)))
    have hA : MeasurableSet A := measurableSet_le (by fun_prop) measurable_const
    have hfinite : ∀ᶠ n : ℕ in atTop,
        (gapMarginal (periodicGapLaw p n.succPNat) 1 0).toMeasure A ≤ B := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      change (gapMarginal (periodicGapLaw p n.succPNat) 1 0).toMeasure {x | x 0 ≤ u} ≤ B
      rw [repulsion_gapMarginal_event_internal, periodicGapLaw_toMeasure,
        Measure.map_apply (measurable_periodicGapSequence n.succPNat)
          (show MeasurableSet {y : Gaps | (y 0 : ℝ) ≤ u} from
            measurableSet_le (measurable_subtype_coe.comp (measurable_pi_apply 0))
              measurable_const)]
      exact (ht p hps hpl hph n.succPNat
        (by simp only [Nat.succPNat_coe]; omega) 0).1 u hu hu1
    -- Total variation controls the closed event, even if the limit has an atom at u.
    have hd : (gapMarginal q 1 0).toMeasure A - B ≤ 0 := by
      apply ge_of_tendsto hTV
      filter_upwards [hfinite] with n hn
      calc
        (gapMarginal q 1 0).toMeasure A - B ≤
            (gapMarginal q 1 0).toMeasure A -
              (gapMarginal (periodicGapLaw p n.succPNat) 1 0).toMeasure A :=
          tsub_le_tsub_left hn _
        _ ≤ totalVariation (gapMarginal q 1 0).toMeasure
            (gapMarginal (periodicGapLaw p n.succPNat) 1 0).toMeasure :=
          measure_sub_le_totalVariation _ _ A hA
        _ = totalVariation (gapMarginal (periodicGapLaw p n.succPNat) 1 0).toMeasure
            (gapMarginal q 1 0).toMeasure := totalVariation_symm _ _
    exact tsub_eq_zero_iff_le.mp (le_antisymm hd bot_le)
  intro i u hu hu1
  have he := congrArg (fun r : ProbabilityMeasure Gaps =>
    r.toMeasure {y | (y 0 : ℝ) ≤ u}) (hshift i)
  have hm : MeasurableSet {y : Gaps | (y 0 : ℝ) ≤ u} :=
    measurableSet_le (measurable_subtype_coe.comp (measurable_pi_apply 0)) measurable_const
  rw [ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (gapIndexShift i).continuous.measurable hm] at he
  have hevent : q.toMeasure {y | (y i : ℝ) ≤ u} =
      q.toMeasure {y | (y 0 : ℝ) ≤ u} := by
    simpa only [Set.preimage_ofPred_eq, gapIndexShift_apply, add_zero] using he
  rw [hevent]
  exact hzero u hu hu1

/-- See Proposition 1.2 of the paper: the repulsion event is the
labelled coordinate event whenever the full Palm gap law is identified. -/
theorem repulsionProbability_eq_gap_event_internal (P : PointProcess)
    (q : ProbabilityMeasure Gaps)
    (hgap : (rootedPalmMeasure P).map rootedGap =
      q.toMeasure.map (fun y : Gaps => fun i => (y i : ℝ))) (i : ℤ) (u : ℝ) :
    repulsionProbability P i u = q.toMeasure {y | (y i : ℝ) ≤ u} := by
  have he := congrArg (fun μ : Measure (ℤ → ℝ) => μ {y | y i ≤ u}) hgap
  rw [Measure.map_apply (measurable_pi_iff.mpr measurable_rootedGap)
      (measurableSet_le (measurable_pi_apply i) measurable_const),
    Measure.map_apply
      (show Measurable (fun y : Gaps => fun j => (y j : ℝ)) from
        measurable_pi_iff.mpr fun j =>
          measurable_subtype_coe.comp (measurable_pi_apply j))
      (measurableSet_le (measurable_pi_apply i) measurable_const)] at he
  exact he

/-- Proposition 1.2 of the paper, internal composition with the
ordinary-gap Cauchy estimate: choose uniform tail constants before β, identify the
Palm law, transfer the label-zero event and then shift its label. -/
theorem repulsion_from_cauchy_locallyUniform_internal
    (hcomparison :
      ∀ (p : Parameters) (ζ : ℝ), 0 < ζ → ∃ C : ℝ, 0 < C ∧
        ∀ (n N N' : ℕ+) (_ : 2 ≤ (n : ℕ)),
          (N : ℕ) ≤ (N' : ℕ) → 4 * (n : ℕ) ≤ (N : ℕ) →
          (n : ℝ) ^ (2 / p.val.2) ≤ (N : ℝ) →
          ∀ (G : BlockObservable n) (J : Finset (Fin (n : ℕ))),
            MiddleConsecutiveBlock n J → DependsOnBlockCoordinates G J →
            Integrable (fun X : Riesz1.Configuration N => G.val (finiteGapBlock X))
              (gibbsMeasure p N) ∧
            Integrable (fun X : Riesz1.Configuration N' => G.val (finiteGapBlock X))
              (gibbsMeasure p N') ∧
            |(∫ X : Riesz1.Configuration N, G.val (finiteGapBlock X) ∂gibbsMeasure p N) -
              (∫ X : Riesz1.Configuration N', G.val (finiteGapBlock X) ∂gibbsMeasure p N')| ≤
              C * (n : ℝ) ^ (-min p.val.2 1 / 2 + ζ) * blockDerivativeNorm G)
    (hconvergence : External.LogConcaveConvergence)
    (s βlo βhi : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∃ h : UniqueRieszLimit p,
        let P := limitingRieszProcess p h
        PalmRegular P ∧ ∀ i : ℤ, ∀ u : ℝ, 0 < u → u ≤ 1 →
          repulsionProbability P i u ≤ ENNReal.ofReal (C * Real.exp (-c * u ^ (-s))) := by
  obtain ⟨c, C, hc, hC, ht⟩ := repulsion_gap_limit_via_shift_internal s βlo βhi hs hs1 hlo hle
  refine ⟨c, C, hc, hC, ?_⟩
  intro p hps hpl hph
  obtain ⟨h, _hstat, _hint, hreg⟩ := convergence_from_cauchy_internal hcomparison hconvergence p
  obtain ⟨q, hq, _⟩ := convergence_gap_total_variation_from_predecessors_internal
    hcomparison
    (by
      intro p q hq k hk
      simpa only [zero_add] using
        GapNondegeneracy.block_nondegeneracy_from_finite_internal
          GapNondegeneracy.finite_gibbs_covariance_lower_bound p q hq k hk)
    convergence_limit_density hconvergence p
  obtain ⟨qP, hqP, _⟩ := convergence_palm_inversion_from_cauchy_internal hcomparison p
  have heq : qP = q := tendsto_nhds_unique hqP.1 hq.1
  subst qP
  obtain ⟨P, hP, _hs, _hi, _hpalm, _hroot, hgap, _hfinite⟩ := hqP.2
  obtain ⟨qL, hqL, _⟩ :=
    convergence_local_total_variation_from_cauchy_internal hcomparison hconvergence p
  have heq : qL = q := tendsto_nhds_unique hqL.1 hq.1
  subst qL
  obtain ⟨PL, hPL, hlocal⟩ := hqL.2
  have heq : P = PL := ProbabilityMeasure.toMeasure_injective (hP.trans hPL.symm)
  have hchosen : limitingRieszProcess p h = P := by
    apply localConverges_unique _ _ P (Classical.choose_spec h.exists)
    simpa only [heq] using hlocal
  obtain ⟨qS, hqS, _⟩ := convergence_gap_limit_from_cauchy_internal hcomparison p
  have heq : qS = q := tendsto_nhds_unique hqS.1 hq.1
  subst qS
  have htail := ht p hps hpl hph q (hq.2 1 0).2.2.1 hqS.2.1
  refine ⟨h, hreg, fun i u hu hu1 => ?_⟩
  rw [hchosen, repulsionProbability_eq_gap_event_internal P q hgap i u]
  exact htail i u hu hu1

/-- Proposition 1.2 of the paper, fixed-temperature specialization
of the compact-temperature proof at label zero. -/
theorem repulsion_from_cauchy_internal
    (hcomparison :
      ∀ (p : Parameters) (ζ : ℝ), 0 < ζ → ∃ C : ℝ, 0 < C ∧
        ∀ (n N N' : ℕ+) (_ : 2 ≤ (n : ℕ)),
          (N : ℕ) ≤ (N' : ℕ) → 4 * (n : ℕ) ≤ (N : ℕ) →
          (n : ℝ) ^ (2 / p.val.2) ≤ (N : ℝ) →
          ∀ (G : BlockObservable n) (J : Finset (Fin (n : ℕ))),
            MiddleConsecutiveBlock n J → DependsOnBlockCoordinates G J →
            Integrable (fun X : Riesz1.Configuration N => G.val (finiteGapBlock X))
              (gibbsMeasure p N) ∧
            Integrable (fun X : Riesz1.Configuration N' => G.val (finiteGapBlock X))
              (gibbsMeasure p N') ∧
            |(∫ X : Riesz1.Configuration N, G.val (finiteGapBlock X) ∂gibbsMeasure p N) -
              (∫ X : Riesz1.Configuration N', G.val (finiteGapBlock X) ∂gibbsMeasure p N')| ≤
              C * (n : ℝ) ^ (-min p.val.2 1 / 2 + ζ) * blockDerivativeNorm G)
    (hconvergence : External.LogConcaveConvergence) :
    ∀ p : Parameters, ∃ h : UniqueRieszLimit p,
      let P := limitingRieszProcess p h
      PalmRegular P ∧ ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        ∀ i : ℤ, ∀ u : ℝ, 0 < u → u ≤ 1 →
          repulsionProbability P i u ≤ ENNReal.ofReal (C * Real.exp (-c * u ^ (-p.val.2))) := by
  intro p
  obtain ⟨c, C, hc, hC, ht⟩ := repulsion_from_cauchy_locallyUniform_internal
    hcomparison hconvergence p.val.2 p.val.1 p.val.1 p.property.2.1 p.property.2.2
    p.property.1 le_rfl
  obtain ⟨h, hreg, hb⟩ := ht p rfl le_rfl le_rfl
  exact ⟨h, hreg, c, C, hc, hC, hb⟩

/-- Proposition 1.2 of the paper, with the local uniformity in β
specified by the manuscript's constants convention: both positive constants
precede β, every Palm label, and every cutoff. -/
theorem repulsion_locallyUniform (hconvergence : External.LogConcaveConvergence)
    (s βlo βhi : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∃ h : UniqueRieszLimit p,
        let P := limitingRieszProcess p h
        PalmRegular P ∧ ∀ i : ℤ, ∀ u : ℝ, 0 < u → u ≤ 1 →
          repulsionProbability P i u ≤ ENNReal.ofReal (C * Real.exp (-c * u ^ (-s))) :=
  repulsion_from_cauchy_locallyUniform_internal Riesz2.ordinaryGapCauchy hconvergence
    s βlo βhi hs hs1 hlo hle

end Riesz2
