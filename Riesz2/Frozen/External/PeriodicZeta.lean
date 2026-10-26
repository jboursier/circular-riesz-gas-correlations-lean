/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.NumberTheory.LSeries.HurwitzZeta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Periodic-zeta connection formula: `Riesz2.External.PeriodicZeta`

The connection between the symmetrized Hurwitz zeta function and the cosine series ∑_{n≥1}
n^{-s} cos(2πnx), for 0 < s < 1 and 0 < x < 1. This is DLMF equation (25.13.3), added at x
and 1−x. The series is interpreted through ordered partial sums because it is conditionally
convergent. On this interval Mathlib’s unit-circle Hurwitz zeta agrees with the usual
Hurwitz zeta.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology BigOperators

namespace Riesz2.External

def PeriodicZeta : Prop :=
  ∀ s x : ℝ, 0 < s → s < 1 → 0 < x → x < 1 →
    ∃ L : ℝ,
      Tendsto (fun M : ℕ => ∑ n ∈ Finset.range M,
        ((n + 1 : ℕ) : ℝ) ^ (-s) * Real.cos (2 * Real.pi * (n + 1) * x))
        atTop (𝓝 L) ∧
      (HurwitzZeta.hurwitzZeta (x : UnitAddCircle) ((1 - s : ℝ) : ℂ)).re +
          (HurwitzZeta.hurwitzZeta ((1 - x : ℝ) : UnitAddCircle)
            ((1 - s : ℝ) : ℂ)).re =
        (4 * Real.Gamma s * Real.cos (Real.pi * s / 2) / (2 * Real.pi) ^ s) * L

end Riesz2.External

end
end
