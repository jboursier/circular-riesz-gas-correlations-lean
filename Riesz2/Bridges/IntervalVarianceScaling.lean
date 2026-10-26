/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Bridges.IntervalFluctuations
public import Mathlib.Tactic

/-!
# Rescaling the companion interval variance

In Subsection 2.2, the companion interval variance `V(ξ)` of `Riesz2.intervalLineVariance` is `2^{-s}` times the constant
`σ²_{s,β} = cot(πs/2)/(2βπs)`, by `Riesz2.intervalLineVariance_eq_cot`. With `ℓ = 2R/N`, the scaling
factor `(Nℓ)^s = (2R)^s` cancels the factor `2^{-s}`, which gives `R^s σ²_{s,β}`.
-/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

namespace Riesz2

/-- See Subsection 2.2 of the paper. Let `0 < s < 1`, `β > 0`, `N ≥ 1` an integer, `0 < R ≤ N/2` and
`ℓ = 2R/N`. Then `(Nℓ)^s V(ξ) = R^s σ²_{s,β}`, where `σ²_{s,β} = cot(πs/2)/(2βπs)`. -/
theorem rescale_interval_variance (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (R ℓ : ℝ) (hR : 0 < R) (_hRN : R ≤ (N : ℝ) / 2) (hℓ : ℓ = 2 * R / N) :
    ENNReal.ofReal (((N : ℝ) * ℓ) ^ s.val) * intervalLineVariance β s =
      ENNReal.ofReal (R ^ s.val * (Real.cos (Real.pi * s.val / 2) /
        Real.sin (Real.pi * s.val / 2) / (2 * β.val * Real.pi * s.val))) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hNℓ : (N : ℝ) * ℓ = 2 * R := by
    rw [hℓ]
    field_simp
  have hpow : (0 : ℝ) ≤ ((N : ℝ) * ℓ) ^ s.val := Real.rpow_nonneg (by rw [hNℓ]; positivity) _
  rw [intervalLineVariance_eq_cot, ← ENNReal.ofReal_mul hpow]
  congr 1
  rw [hNℓ, Real.mul_rpow (by norm_num) hR.le]
  have h2 : (2 : ℝ) ^ s.val * (2 : ℝ) ^ (-s.val) = 1 := by
    rw [← Real.rpow_add (by norm_num)]
    simp
  linear_combination (R ^ s.val * (Real.cos (Real.pi * s.val / 2) /
    Real.sin (Real.pi * s.val / 2) / (2 * β.val * Real.pi * s.val))) * h2

end Riesz2

end
