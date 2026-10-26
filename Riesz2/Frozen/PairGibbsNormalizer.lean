/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.ParticlePairEnergy
public import Riesz1.Frozen.ConfigurationVolume
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Partition integral for general pair potentials: `Riesz2.pairGibbsNormalizer`

The nonnegative partition integral Z = ∫ exp(−H) on the particle configuration chart, with
the pair energy H of Subsection 3.1.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The nonnegative partition integral Z = ∫ exp(−H) on the particle configuration chart, with
the pair energy H of Subsection 3.1. -/
def pairGibbsNormalizer {N : ℕ+} (χ : ParticlePairData N) : ℝ≥0∞ :=
  ∫⁻ X : Riesz1.Configuration N,
    ENNReal.ofReal (Real.exp (-particlePairEnergy χ (WithLp.toLp 2 X.val)))
      ∂Riesz1.configurationVolume N

end Riesz2

end
end
