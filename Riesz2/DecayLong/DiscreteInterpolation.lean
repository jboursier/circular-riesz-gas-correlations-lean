/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.FourierMultiplierKernels
public import Riesz2.Preliminaries.SymbolBounds
public import Riesz1.ToMathlib.Poincare.Circle
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Data.Nat.Log

/-!
# Frequency comparisons and dyadic scales

Shared ingredients for the angular proof of Lemma 5.9 of the paper:
dyadic scales and comparisons between angular distance and the sine radius.
The smooth angular blocks and their kernels are constructed in the angular modules.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped BigOperators ContDiff

namespace Riesz2.DiscreteInterpolation

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The sine radius used to construct angular-supported blocks in
Lemma 5.9 of the paper. It is compared with angular distance below. -/
def frequencyRadius (θ : ℝ) : ℝ := 2 * |Real.sin (θ / 2)|

/-- The number of dyadic steps in Subsection 5.2.
For an integer cycle size, `Nat.clog 2 N` is exactly `⌈log₂ N⌉`. -/
def dyadicDepth (N : ℕ+) : ℕ := Nat.clog 2 (N : ℕ) + 2

/-- The explicit scale `t_j = 2^(j-Q)` of Subsection 5.2. -/
def dyadicScale (N : ℕ+) (j : ℕ) : ℝ := (2 : ℝ) ^ ((j : ℤ) - dyadicDepth N)

theorem dyadicScale_pos (N : ℕ+) (j : ℕ) : 0 < dyadicScale N j := by
  unfold dyadicScale
  positivity

theorem dyadicScale_le_one (N : ℕ+) {j : ℕ} (hj : j ≤ dyadicDepth N) :
    dyadicScale N j ≤ 1 := by
  apply zpow_le_one_of_nonpos₀ (by norm_num : (1 : ℝ) ≤ 2)
  exact sub_nonpos.mpr (by exact_mod_cast hj)

theorem continuous_frequencyRadius : Continuous frequencyRadius := by
  unfold frequencyRadius
  fun_prop

/-- Angular distance to the seam is controlled by the frequency radius. -/
theorem endpointDistance_le_radius {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    min θ (2 * Real.pi - θ) ≤ Real.pi / 2 * frequencyRadius θ := by
  have hs : 0 ≤ Real.sin (θ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  unfold frequencyRadius
  rw [abs_of_nonneg hs]
  rcases le_total θ Real.pi with h | h
  · have hl := Real.mul_le_sin (x := θ / 2) (by linarith [hθ.1]) (by linarith)
    have hp : 0 < Real.pi := Real.pi_pos
    have hh := mul_le_mul_of_nonneg_left hl hp.le
    field_simp at hh
    exact (min_le_left _ _).trans (by nlinarith)
  · have hl := Real.mul_le_sin (x := Real.pi - θ / 2)
      (by linarith [hθ.2]) (by linarith)
    rw [Real.sin_pi_sub] at hl
    have hh := mul_le_mul_of_nonneg_left hl Real.pi_pos.le
    field_simp at hh
    exact (min_le_right _ _).trans (by nlinarith)

/-- The reverse, unit-constant comparison of the two frequency distances. -/
theorem radius_le_endpointDistance {θ : ℝ} (hθ : θ ∈ Icc 0 (2 * Real.pi)) :
    frequencyRadius θ ≤ min θ (2 * Real.pi - θ) := by
  have hs : 0 ≤ Real.sin (θ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  unfold frequencyRadius
  rw [abs_of_nonneg hs]
  apply le_min
  · have := Real.sin_le (x := θ / 2) (by linarith [hθ.1])
    linarith
  · have := Real.sin_le (x := Real.pi - θ / 2) (by linarith [hθ.2])
    rw [Real.sin_pi_sub] at this
    linarith


end Riesz2.DiscreteInterpolation
