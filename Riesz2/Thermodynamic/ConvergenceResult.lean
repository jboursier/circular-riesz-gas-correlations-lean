/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.LocalTotalVariationPart2
public import Riesz2.Thermodynamic.GapNondegeneracyPart2
public import Riesz2.Thermodynamic.GapNondegeneracyPart3
public import Riesz2.Thermodynamic.LimitDensity
public import Riesz2.Thermodynamic.GapTotalVariation
public import Riesz2.Thermodynamic.LocalLimitUniqueness
public import Riesz2.Frozen.PalmRegular
public import Riesz2.Frozen.LimitingRieszProcess

/-!
# Unique limiting process and Palm regularity

Theorem 3 follows from the ordinary-gap Cauchy estimate and the log-concave density
convergence hypothesis.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace Riesz2

local notation "Gaps" => (ℤ → Ioi (0 : ℝ))
local instance convergenceResultConfigurationMeasurableSpace :
    MeasurableSpace LineConfiguration := configurationMeasurableSpace

/-- See Theorem 3 of the paper: reconstruction identifies every clause
of the Palm regularity predicate, including support, probability,
index invariance, integrability and all labelled means. This internal bridge
uses the actual Palm maps. -/
theorem palmRegular_of_reconstruction_internal
    (q : Measure reconstructibleGapSequences) [IsProbabilityMeasure q]
    (hshift : ∀ a : ℤ, q.map (reindexReconstructibleGaps a) = q)
    (hmean : ∀ i : ℤ,
      Integrable (fun y : reconstructibleGapSequences => (y.val i : ℝ)) q ∧
        (∫ y : reconstructibleGapSequences, (y.val i : ℝ) ∂q) = 1)
    (P : PointProcess)
    (hpalm : palmMeasure P = q.map reconstructConfiguration)
    (hroot : rootedPalmMeasure P = q.map reconstructRootedConfiguration) :
    PalmRegular P := by
  have hpre : reconstructConfiguration ⁻¹' rootedConfigurations = univ := by
    ext y
    simp only [mem_preimage, mem_univ, iff_true]
    exact reconstructConfiguration_mem_rootedConfigurations y
  have hrootprob : IsProbabilityMeasure (rootedPalmMeasure P) := by
    rw [hroot]
    exact Measure.isProbabilityMeasure_map_iff measurable_reconstructRootedConfiguration.aemeasurable |>.mpr inferInstance
  have hpalmprob : IsProbabilityMeasure (palmMeasure P) := by
    rw [hpalm]
    exact Measure.isProbabilityMeasure_map_iff measurable_reconstructConfiguration.aemeasurable |>.mpr inferInstance
  refine ⟨measurableSet_rootedConfigurations, ?_, hrootprob, hpalmprob, ?_, ?_, ?_⟩
  · rw [hpalm, Measure.map_apply measurable_reconstructConfiguration
      measurableSet_rootedConfigurations, hpre, measure_univ]
  · rw [hpalm, Measure.map_apply measurable_reconstructConfiguration
      measurableSet_rootedConfigurations.compl, preimage_compl, hpre, compl_univ, measure_empty]
  · have hm : Measurable (fun y : reconstructibleGapSequences => fun i => (y.val i : ℝ)) :=
      measurable_pi_iff.mpr fun i =>
        measurable_subtype_coe.comp ((measurable_pi_apply i).comp measurable_subtype_coe)
    have hmroot : Measurable (fun C : RootedConfiguration => fun i => rootedGap C (i + 1)) :=
      measurable_pi_iff.mpr fun i => measurable_rootedGap (i + 1)
    rw [hroot, Measure.map_map hmroot measurable_reconstructRootedConfiguration,
      Measure.map_map (measurable_pi_iff.mpr measurable_rootedGap)
        measurable_reconstructRootedConfiguration]
    have hgap (y : reconstructibleGapSequences) :
        rootedGap (reconstructRootedConfiguration y) = fun i => (y.val i : ℝ) :=
      funext (rootedGap_reconstructRootedConfiguration y)
    simp only [Function.comp_def, hgap]
    have he := congrArg (fun μ : Measure reconstructibleGapSequences =>
      μ.map (fun y i => (y.val i : ℝ))) (hshift 1)
    rw [Measure.map_map hm (measurable_reindexReconstructibleGaps 1)] at he
    exact he
  · intro i
    rw [hroot]
    have hi : Integrable (fun y : reconstructibleGapSequences =>
        rootedGap (reconstructRootedConfiguration y) i) q := by
      simpa only [rootedGap_reconstructRootedConfiguration] using (hmean i).1
    refine ⟨(integrable_map_measure (measurable_rootedGap i).aestronglyMeasurable
      measurable_reconstructRootedConfiguration.aemeasurable).mpr hi, ?_⟩
    rw [integral_map measurable_reconstructRootedConfiguration.aemeasurable
      (measurable_rootedGap i).aestronglyMeasurable]
    simpa only [rootedGap_reconstructRootedConfiguration] using (hmean i).2

/-- The conclusion of Theorem 3, assuming the ordinary-gap Cauchy estimate
and the log-concave density convergence predicate. -/
theorem convergence_from_cauchy_internal
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
      IsStationary P ∧ HasIntensity P 1 ∧ PalmRegular P := by
  intro p
  obtain ⟨q, hq, _⟩ := convergence_gap_limit_from_cauchy_internal hcomparison p
  obtain ⟨qP, hqP, _⟩ := convergence_palm_inversion_from_cauchy_internal hcomparison p
  have heq : qP = q := tendsto_nhds_unique hqP.1 hq.1
  subst qP
  obtain ⟨P, hP, hstat, hint, hpalm, hroot, _hgap, _hfinite⟩ := hqP.2
  have hs : ∀ᵐ y ∂q.toMeasure, y ∈ reconstructibleGapSequences :=
    hq.2.2.2.2.2.2.mono fun y hy =>
      mem_reconstructibleGapSequences_of_divergent_sums y hy.1 hy.2
  have := reconstructionGapMeasure_probability q.toMeasure hs
  have hm := reconstructionGapMeasure_mean q.toMeasure hs 0 (hq.2.2.1 0).1 (hq.2.2.1 0).2
  have := gapSuspensionMeasure_probability _ hm.1 hm.2
  have hreg : PalmRegular P := palmRegular_of_reconstruction_internal _
    (fun a => reconstructionGapMeasure_shift q.toMeasure hs a (by
      have he := congrArg ProbabilityMeasure.toMeasure (hq.2.1 a)
      rw [ProbabilityMeasure.toMeasure_map] at he
      change q.toMeasure.map (fun y j => y (a + j)) = q.toMeasure at he
      simpa only [add_comm] using he))
    (fun i => reconstructionGapMeasure_mean q.toMeasure hs i (hq.2.2.1 i).1 (hq.2.2.1 i).2)
    P hpalm hroot
  obtain ⟨qTV, hqTV, _⟩ := convergence_gap_total_variation_from_predecessors_internal
    hcomparison
    (by
      intro p q hq k hk
      simpa only [zero_add] using
        GapNondegeneracy.block_nondegeneracy_from_finite_internal
          GapNondegeneracy.finite_gibbs_covariance_lower_bound p q hq k hk)
    convergence_limit_density hconvergence p
  have heq : qTV = q := tendsto_nhds_unique hqTV.1 hq.1
  subst qTV
  have hlocal : LocalConverges (microscopicLaw p) P := by
    refine ⟨microscopicLaw_probability p, ?_⟩
    intro R _hR
    have hTV := convergence_local_total_variation_from_gap_predecessors_internal
      p q hq.1 hs (hq.2.2.1 0) (fun m hm =>
        ((hqTV.2 (2 * m) (-(m : ℤ))).2.2.2 ⟨m, by omega⟩).2) R
    simpa only [hP, Riesz1.particleNumber, Nat.succPNat] using hTV
  have huniq : UniqueRieszLimit p :=
    ⟨P, hlocal, fun Q hQ => localConverges_unique _ Q P hQ hlocal⟩
  refine ⟨huniq, ?_⟩
  have hchosen : limitingRieszProcess p huniq = P :=
    localConverges_unique _ _ P (Classical.choose_spec huniq.exists) hlocal
  change IsStationary (limitingRieszProcess p huniq) ∧
    HasIntensity (limitingRieszProcess p huniq) 1 ∧ PalmRegular (limitingRieszProcess p huniq)
  rw [hchosen]
  exact ⟨hstat, hint, hreg⟩

end Riesz2
