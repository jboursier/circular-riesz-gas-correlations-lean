/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Probability.Moments.Covariance

/-!
# Covariance of two sums with a common third term

For square-integrable real functions `X, Y, Z` on a finite measure space, the covariance of `X`
and `Y` is half the signed combination `Cov(X+Y+Z) + Cov(Z) - Cov(X+Z) - Cov(Y+Z)`, where each
`Cov(W)` denotes the variance of `W`. This is the algebraic identity behind the negative
covariance of two separated blocks of gaps.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz2.ToMathlib

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- For `X, Y, Z` in `L²(μ)`, the covariance of `X` and `Y` satisfies
`2 Cov(X, Y) = Var(X+Y+Z) + Var(Z) - Var(X+Z) - Var(Y+Z)`, where `Var(W)` is
`Cov(W, W)`. Each side is finite because all five functions are square-integrable. -/
theorem two_covariance_eq_three_sum {X Y Z : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hZ : MemLp Z 2 μ) :
    2 * ProbabilityTheory.covariance X Y μ =
      ProbabilityTheory.covariance (X + Y + Z) (X + Y + Z) μ +
        ProbabilityTheory.covariance Z Z μ -
        ProbabilityTheory.covariance (X + Z) (X + Z) μ -
        ProbabilityTheory.covariance (Y + Z) (Y + Z) μ := by
  have hXY : MemLp (X + Y) 2 μ := hX.add hY
  have hXZ : MemLp (X + Z) 2 μ := hX.add hZ
  have hYZ : MemLp (Y + Z) 2 μ := hY.add hZ
  have hS : MemLp (X + Y + Z) 2 μ := hXY.add hZ
  have hSum : ProbabilityTheory.covariance (X + Y + Z) (X + Y + Z) μ =
      ProbabilityTheory.covariance X X μ + ProbabilityTheory.covariance Y Y μ +
        ProbabilityTheory.covariance Z Z μ + 2 * ProbabilityTheory.covariance X Y μ +
        2 * ProbabilityTheory.covariance X Z μ + 2 * ProbabilityTheory.covariance Y Z μ := by
    rw [ProbabilityTheory.covariance_add_left hXY hZ hS,
      ProbabilityTheory.covariance_add_left hX hY hS,
      ProbabilityTheory.covariance_add_right hX hXY hZ,
      ProbabilityTheory.covariance_add_right hX hX hY,
      ProbabilityTheory.covariance_add_right hY hXY hZ,
      ProbabilityTheory.covariance_add_right hY hX hY,
      ProbabilityTheory.covariance_add_right hZ hXY hZ,
      ProbabilityTheory.covariance_add_right hZ hX hY,
      ProbabilityTheory.covariance_comm Z X, ProbabilityTheory.covariance_comm Z Y,
      ProbabilityTheory.covariance_comm Y X]
    ring
  have hXZe : ProbabilityTheory.covariance (X + Z) (X + Z) μ =
      ProbabilityTheory.covariance X X μ + ProbabilityTheory.covariance Z Z μ +
        2 * ProbabilityTheory.covariance X Z μ := by
    rw [ProbabilityTheory.covariance_add_left hX hZ hXZ,
      ProbabilityTheory.covariance_add_right hX hX hZ,
      ProbabilityTheory.covariance_add_right hZ hX hZ,
      ProbabilityTheory.covariance_comm Z X]
    ring
  have hYZe : ProbabilityTheory.covariance (Y + Z) (Y + Z) μ =
      ProbabilityTheory.covariance Y Y μ + ProbabilityTheory.covariance Z Z μ +
        2 * ProbabilityTheory.covariance Y Z μ := by
    rw [ProbabilityTheory.covariance_add_left hY hZ hYZ,
      ProbabilityTheory.covariance_add_right hY hY hZ,
      ProbabilityTheory.covariance_add_right hZ hY hZ,
      ProbabilityTheory.covariance_comm Z Y]
    ring
  rw [hSum, hXZe, hYZe]
  ring

end Riesz2.ToMathlib

end
end
