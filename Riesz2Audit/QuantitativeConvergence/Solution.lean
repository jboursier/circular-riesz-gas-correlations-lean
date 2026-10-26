/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2Audit.QuantitativeConvergence.Definitions
public import Riesz2.Frozen.QuantitativeConvergence

/-!
# Theorem 4 (Quantitative convergence of labelled gaps): the proof

The statement of the challenge, on the definitions of `Definitions.lean`, proved from
`Riesz2.quantitativeConvergence` of the library. These definitions are copies of those of the library, so the
two statements agree after unfolding the definitions.
-/

@[expose] public section

namespace Riesz2Audit.QuantitativeConvergence

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- For β > 0 and s ∈ (0,1) ∪ (1,+∞), expectations of Lipschitz functions G of the first K
microscopic gaps converge to those under Riesz_{s,β}^0. For 1 ≤ K ≤
floor(N^{min(s,2)/2}/32), the error is at most C N^{-min(s,2)min(s,1)/4+ε} ∑ⱼ ‖∂ⱼG‖∞. The
statement also supplies the limiting process and integrability of both observables.
This is Theorem 4 of the paper. -/
theorem quantitativeConvergence :
  letI := configurationMeasurableSpace
  ∀ p : Parameters, ∃ h : UniqueRieszLimit p,
    let P := limitingRieszProcess p h
    PalmRegular P ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ N K : ℕ+, (K : ℝ) ≤ (N : ℝ) ^ exponentA p.val.2 / 32 →
        ∀ G : BlockObservable K,
          Integrable (fun X : Riesz1.Configuration N => G.val (finiteGapBlock X))
            (gibbsMeasure p N) ∧
          Integrable (fun C => G.val (rootedGapBlock K C)) (rootedPalmMeasure P) ∧
          |(∫ X, G.val (finiteGapBlock X) ∂gibbsMeasure p N) -
            (∫ C, G.val (rootedGapBlock K C) ∂rootedPalmMeasure P)| ≤
              C * (N : ℝ) ^ (-convergenceRate p.val.2 + ε) * blockDerivativeNorm G :=
  by exact _root_.Riesz2.quantitativeConvergence

end Riesz2

end

end Riesz2Audit.QuantitativeConvergence

end
