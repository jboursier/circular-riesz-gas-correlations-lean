/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2Audit.Hyperuniformity.Definitions
public import Riesz2.Frozen.Hyperuniformity

/-!
# Corollary 1.1 (Hyperuniformity of the Riesz process): the proof

The statement of the challenge, on the definitions of `Definitions.lean`, proved from
`Riesz2.hyperuniformity` of the library. These definitions are copies of those of the library, so the
two statements agree after unfolding the definitions.
-/

@[expose] public section

namespace Riesz2Audit.Hyperuniformity

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- For 0 < s < 1, let σ² = cot(πs/2)/(2βπs). Under Riesz_{s,β}, R^{-s/2}(N_{(0,R]}−R) converges
to N(0,σ²), and Var[N_{(0,R]}] ∼ σ²R^s. Under its Palm law, K^{-s/2}(z_K−K) has the same
Gaussian limit and Var[z_K] ∼ σ²K^s. In particular the number variance is sublinear. The
statement includes the required second moments and Palm normalization.
This is Corollary 1.1 of the paper. -/
theorem hyperuniformity :
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
  by exact _root_.Riesz2.hyperuniformity

end Riesz2

end

end Riesz2Audit.Hyperuniformity

end
