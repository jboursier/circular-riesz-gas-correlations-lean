/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.ParticleChamber

/-!
# Pair potentials indexed by particle pairs: `Riesz2.ParticlePairData`

The potentials χ_ij for i < j in Assumptions 3.1. Their values on (0,1) determine the
particle energy. This encodes `Riesz1.HsPairPotentials` without redundant symmetric entries.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The potentials χ_ij for i < j in Assumptions 3.1. Their values on (0,1) determine the
particle energy. This encodes `Riesz1.HsPairPotentials` without redundant symmetric entries. -/
@[reducible] def ParticlePairData (N : ℕ+) :=
  {p : Fin (N : ℕ) × Fin (N : ℕ) // p.1 < p.2} → ℝ → ℝ

end Riesz2

end
end
