/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.PairGibbsNormalizer

/-!
# Gibbs law for general pair potentials: `Riesz2.pairGibbsMeasure`

The Gibbs law with weight exp(−H), for the pair potentials of Assumptions 3.1. Measurability
and a positive finite partition integral are explicit arguments. It agrees with
`Riesz1.hsQuotientGibbsProbability` under the fundamental-region identification.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The Gibbs law with weight exp(−H), for the pair potentials of Assumptions 3.1. Measurability
and a positive finite partition integral are explicit arguments. It agrees with
`Riesz1.hsQuotientGibbsProbability` under the fundamental-region identification. -/
def pairGibbsMeasure {N : ℕ+} (χ : ParticlePairData N)
    (_hMeas : Measurable (fun X : Riesz1.Configuration N =>
      ENNReal.ofReal (Real.exp (-particlePairEnergy χ (WithLp.toLp 2 X.val)))))
    (_hZ : 0 < pairGibbsNormalizer χ ∧ pairGibbsNormalizer χ < ⊤) :
    Measure (Riesz1.Configuration N) :=
  (pairGibbsNormalizer χ)⁻¹ • (Riesz1.configurationVolume N).withDensity
    (fun X => ENNReal.ofReal (Real.exp (-particlePairEnergy χ (WithLp.toLp 2 X.val))))

end Riesz2

end
end
