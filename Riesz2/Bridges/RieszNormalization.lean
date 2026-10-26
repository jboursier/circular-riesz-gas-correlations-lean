/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.RieszConstant
public import Riesz1.Kernel.AdmissibilityRegularityVariance
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Tactic

/-!
# Equivalent normalization of the Riesz constant

The Riesz constant `c_s` of Subsection 2.2 is `Riesz1.rieszConstant`, a quotient of Gamma values. For
`0 < s < 1` it is positive, and it equals `2 Γ(1 - s) sin(π s / 2)`.

Positivity is `Riesz1.rieszConstant_pos`. The identity follows from the Legendre duplication
formula at `(1 - s)/2` and the reflection formula at `s/2`.
-/

public section

namespace Riesz2

/-- See Subsection 2.2 of the paper. Let `0 < s < 1`. Then the Riesz constant `Riesz1.rieszConstant` is
positive, and it equals `2 Γ(1 - s) sin(π s / 2)`. The value is a real number, so its finiteness
is part of the type, and both Gamma values in the quotient are positive. -/
theorem rieszConstant_pos_and_eq_sin (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    0 < Riesz1.rieszConstant ⟨s, hs0, hs1⟩ ∧
      Riesz1.rieszConstant ⟨s, hs0, hs1⟩ =
        2 * Real.Gamma (1 - s) * Real.sin (Real.pi * s / 2) := by
  refine ⟨Riesz1.rieszConstant_pos ⟨s, hs0, hs1⟩, ?_⟩
  -- Positive divisors and factors.
  have hGa : 0 < Real.Gamma ((1 - s) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hGb : 0 < Real.Gamma (s / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hGh : 0 < Real.Gamma (1 - s / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hSin : 0 < Real.sin (Real.pi * s / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (div_pos (mul_pos Real.pi_pos hs0) two_pos)
      (by nlinarith [Real.pi_pos])
  -- Legendre duplication at `(1 - s)/2`: `Γ((1 - s)/2) Γ(1 - s/2) = Γ(1 - s) 2^s √π`.
  have hdup : Real.Gamma ((1 - s) / 2) * Real.Gamma (1 - s / 2) =
      Real.Gamma (1 - s) * (2 : ℝ) ^ s * Real.sqrt Real.pi := by
    have h := Real.Gamma_mul_Gamma_add_half ((1 - s) / 2)
    rw [show 1 - 2 * ((1 - s) / 2) = s by ring, show 2 * ((1 - s) / 2) = 1 - s by ring,
      show (1 - s) / 2 + 1 / 2 = 1 - s / 2 by ring] at h
    exact h
  -- Euler reflection at `s/2`: `Γ(s/2) Γ(1 - s/2) sin(π s/2) = π`.
  have hrefl : Real.Gamma (s / 2) * Real.Gamma (1 - s / 2) * Real.sin (Real.pi * s / 2) =
      Real.pi := by
    have h := Real.Gamma_mul_Gamma_one_sub (s / 2)
    rw [show Real.pi * (s / 2) = Real.pi * s / 2 by ring] at h
    rw [h, div_mul_cancel₀ _ hSin.ne']
  -- The two power identities: `2^(1-s) 2^s = 2` and `√π √π = π`.
  have hpow : (2 : ℝ) ^ (1 - s) * (2 : ℝ) ^ s = 2 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hsqrt : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_pos.le
  -- Unfold the constant, then clear the denominator `Γ(s/2)` and the factor `Γ(1 - s/2)`.
  show (2 : ℝ) ^ (1 - s) * Real.sqrt Real.pi * Real.Gamma ((1 - s) / 2) / Real.Gamma (s / 2) =
    2 * Real.Gamma (1 - s) * Real.sin (Real.pi * s / 2)
  rw [div_eq_iff hGb.ne']
  apply mul_right_cancel₀ hGh.ne'
  linear_combination ((2 : ℝ) ^ (1 - s) * Real.sqrt Real.pi) * hdup
    - (2 * Real.Gamma (1 - s)) * hrefl
    + (Real.Gamma (1 - s) * Real.sqrt Real.pi * Real.sqrt Real.pi) * hpow
    + (2 * Real.Gamma (1 - s)) * hsqrt

end Riesz2

end
