/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.FluctuationLimitTransfer
public import Riesz2.Thermodynamic.LocalTotalVariationFinal
public import Riesz2.Thermodynamic.LocalLimitUniqueness
public import Riesz2.Frozen.Convergence
public import Riesz2.Frozen.OrdinaryGapCauchy

/-!
# Hyperuniformity of the Riesz process

See Corollary 1.1. The Cauchy and convergence results identify the limiting process with
the gap suspension. Fixed-window fluctuation transfer supplies both central limit
theorems, both variance asymptotics and the required second moments. Log-concave density
convergence is an explicit hypothesis.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

local instance hyperuniformityResultConfigurationMeasurableSpace :
    MeasurableSpace LineConfiguration := configurationMeasurableSpace

/-- See Corollary 1.1 of the paper: the stationary count and labelled Palm
span CLTs, their extended variance limits, every bounded-interval count
second moment, every positive labelled-span second moment, and the
hyperuniformity limit. Existence, stationarity, intensity one and Palm
regularity are conclusions. -/
theorem hyperuniformity_result (hconvergence : External.LogConcaveConvergence) :
  letI := configurationMeasurableSpace
  ∀ (s : Riesz1.RieszExponent) (β : InverseTemperature),
    ∃ h : UniqueRieszLimit (ofLong β s),
      let P := limitingRieszProcess (ofLong β s) h
      let v : ℝ≥0 := ⟨Riesz1.countVariance (longParameters β s),
        by
          have hs : 0 < s.val := s.property.1
          have hβ : 0 < β.val := β.property
          have hangle : 0 ≤ Real.pi * s.val / 2 := by positivity
          have hhalf : Real.pi * s.val / 2 ≤ Real.pi / 2 := by
            nlinarith [s.property.2, Real.pi_pos]
          unfold Riesz1.countVariance longParameters
          change 0 ≤ Real.cos (Real.pi * s.val / 2) / Real.sin (Real.pi * s.val / 2) /
            (2 * β.val * Real.pi * s.val)
          exact div_nonneg
            (div_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hhalf⟩)
              (Real.sin_nonneg_of_mem_Icc ⟨hangle, by linarith [Real.pi_pos]⟩))
            (by positivity)⟩
      IsStationary P ∧ HasIntensity P 1 ∧
      ∃ hPalm : PalmRegular P,
        letI : IsProbabilityMeasure (rootedPalmMeasure P) := hPalm.2.2.1
        ∃ hCount : ∀ a b : ℝ, MemLp (intervalCount a b) 2 (P : Measure LineConfiguration),
        ∃ hSpan : ∀ K : ℕ+, MemLp (fun C => rootedPoint C (K : ℕ)) 2 (rootedPalmMeasure P),
          ConvergesInLawAlong (atTop : Filter {R : ℝ // 0 < R})
            (fun R => (P : Measure LineConfiguration).map
              (fun C => R.val ^ (-s.val / 2) * (intervalCount 0 R.val C - R.val)))
            (Riesz1.normalLaw v) ∧
          Tendsto (fun R : {R : ℝ // 0 < R} =>
            ENNReal.ofReal (R.val ^ (-s.val)) *
              numberVariance P R.val ((hCount 0 R.val).integrable (by norm_num)))
            atTop (𝓝 (v : ℝ≥0∞)) ∧
          Riesz1.ConvergesInLaw
            (fun n =>
              let K := Riesz1.particleNumber n
              (rootedPalmMeasure P).map
                (fun C => (K : ℝ) ^ (-s.val / 2) * (rootedPoint C (K : ℕ) - (K : ℝ))))
            (Riesz1.normalLaw v) ∧
          Tendsto (fun n : ℕ =>
            let K := Riesz1.particleNumber n
            ENNReal.ofReal ((K : ℝ) ^ (-s.val)) *
              palmSpanVariance P K ((hSpan K).integrable (by norm_num)))
            atTop (𝓝 (v : ℝ≥0∞)) ∧
          Tendsto (fun R : {R : ℝ // 0 < R} =>
            hyperuniformityRatio P R ((hCount 0 R.val).integrable (by norm_num)))
            atTop (𝓝 0) :=
  by
    intro s β
    obtain ⟨h, hstat, hint, hreg⟩ := convergence (ofLong β s)
    obtain ⟨q, hq, _⟩ := convergence_local_total_variation_from_cauchy_internal
      ordinaryGapCauchy hconvergence (ofLong β s)
    obtain ⟨P, hP, hlocal⟩ := hq.2
    obtain ⟨qPalm, hqPalm, _⟩ := convergence_palm_inversion_from_cauchy_internal
      ordinaryGapCauchy (ofLong β s)
    have heq : qPalm = q := tendsto_nhds_unique hqPalm.1 hq.1
    subst qPalm
    obtain ⟨PPalm, hPPalm, _hstatPalm, _hintPalm, _hpalm, hroot, _hgap, _hfinite⟩ :=
      hqPalm.2
    have hprocess : PPalm = P :=
      ProbabilityMeasure.toMeasure_injective (hPPalm.trans hP.symm)
    subst PPalm
    obtain ⟨qTV, hqTV, _⟩ := convergence_gap_total_variation_from_predecessors_internal
      ordinaryGapCauchy
      (by
        intro p q hq k hk
        simpa only [zero_add] using
          GapNondegeneracy.block_nondegeneracy_from_finite_internal
            GapNondegeneracy.finite_gibbs_covariance_lower_bound p q hq k hk)
      convergence_limit_density hconvergence (ofLong β s)
    have heqTV : qTV = q := tendsto_nhds_unique hqTV.1 hq.1
    subst qTV
    have hchosen : limitingRieszProcess (ofLong β s) h = P :=
      localConverges_unique _ _ P (Classical.choose_spec h.exists) hlocal
    refine ⟨h, hstat, hint, hreg, ?_⟩
    refine fixed_window_fluctuation_transfer_internal β s q hq.1
      (fun k => (hqTV.2 k 0).2.2.1) _ ?_ ?_
      hreg.2.2.1 ?_ _ rfl
    · rw [hchosen]
      exact hP
    · rw [hchosen]
      exact periodic_localConverges_from_microscopic_internal (ofLong β s) P hlocal
    · rw [hchosen]
      exact hroot

end Riesz2
