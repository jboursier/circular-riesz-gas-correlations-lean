/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.InteriorCirclePoint
public import Riesz1.Frozen.RieszKernel
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Tactic

/-!
# Regularized sampled Riesz kernel: `Riesz2.sampledRieszKernel`

The sampled kernel g_{N,s} of Subsection 2.4, centered by c_{N,s} = N^{-s}g_s(floor(N/2)/N).
Its diagonal is the finite value 2 + 2N^{-s}ζ(s) − c_{N,s}. The circle kernel is evaluated
only away from zero.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The sampled kernel g_{N,s} of Subsection 2.4, centered by c_{N,s} = N^{-s}g_s(floor(N/2)/N).
Its diagonal is the finite value 2 + 2N^{-s}ζ(s) − c_{N,s}. The circle kernel is evaluated
only away from zero. -/
def sampledRieszKernel (s : Riesz1.RieszExponent) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (k : Fin (N : ℕ)) : ℝ :=
  let middle : {x : ℝ // 0 < x ∧ x < 1} :=
    ⟨((N : ℕ) / 2 : ℕ) / (N : ℝ), by
      have hpos : (0 : ℝ) < N := by exact_mod_cast N.pos
      have hhalf : 0 < (N : ℕ) / 2 := by omega
      have hlt : (N : ℕ) / 2 < (N : ℕ) := by omega
      constructor
      · exact div_pos (by exact_mod_cast hhalf) hpos
      · exact (div_lt_one hpos).mpr (by exact_mod_cast hlt)⟩
  let c := (N : ℝ) ^ (-s.val) * Riesz1.rieszKernel s (interiorCirclePoint middle)
  if hk : k.val = 0 then
    2 + 2 * (N : ℝ) ^ (-s.val) * (riemannZeta (s.val : ℂ)).re - c
  else
    (N : ℝ) ^ (-s.val) * Riesz1.rieszKernel s (interiorCirclePoint
      ⟨(k.val : ℝ) / (N : ℝ), by
        have hpos : (0 : ℝ) < N := by exact_mod_cast N.pos
        constructor
        · exact div_pos (by exact_mod_cast (Nat.pos_of_ne_zero hk)) hpos
        · exact (div_lt_one hpos).mpr (by exact_mod_cast k.isLt)⟩) - c

end Riesz2

end
end
