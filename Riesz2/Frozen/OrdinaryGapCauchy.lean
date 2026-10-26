/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.GibbsMeasure
public import Riesz2.Frozen.FiniteGapBlock
public import Riesz2.Frozen.BlockDerivativeNorm
public import Riesz2.Frozen.DependsOnBlockCoordinates
public import Riesz2.Frozen.MiddleConsecutiveBlock
import Riesz2.Main.OrdinaryGapCauchy

/-!
# Cauchy estimate for ordinary gap laws: `Riesz2.ordinaryGapCauchy`

The Cauchy estimate for expectations of Lipschitz observables of ordinary gaps in the proof
of Proposition 6.6. Both expectations are asserted to be integrable.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The Cauchy estimate for expectations of Lipschitz observables of ordinary gaps in the proof
of Proposition 6.6. Both expectations are asserted to be integrable. -/
theorem ordinaryGapCauchy :
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
          C * (n : ℝ) ^ (-min p.val.2 1 / 2 + ζ) * blockDerivativeNorm G :=
  by exact Riesz2.Main.ordinaryGapCauchy

end Riesz2

end
end
