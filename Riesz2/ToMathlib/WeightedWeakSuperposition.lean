/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.CoerciveSolutionMaps

/-!
# Finite superposition of full-domain weak solutions

The existing coercive inverse is linear on vector L² sources. Its literal
domain tuples therefore satisfy finite superposition. L² pairings
commute with the same finite sums, including the zero-source case.
-/

public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter
open scoped BigOperators

namespace Riesz2.WeightedWeakSuperposition

variable {X ι κ : Type*} [MeasurableSpace X] [Fintype ι] [DecidableEq ι]
    {ν : Measure X}

/-- Finite superposition on the entire matrix-energy domain.
Uniqueness identifies the resulting tuple with the coercive inverse of
the summed source. No smoothness of any scalar source is needed. -/
theorem finset_sum (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (M : X → Matrix ι ι ℝ) (S : Submodule ℝ (ι → ℝ))
    (hM : ∀ᵐ x ∂ν, (M x).PosSemidef)
    (a : ℝ) (ha : 0 < a)
    (hlower : ∀ᵐ x ∂ν, ∀ t ∈ S,
      a * (∑ i, t i ^ 2) ≤ ∑ i, ∑ j, t i * M x i j * t j)
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (J : Finset κ) (f : κ → ι → Lp ℝ 2 ν) (u : κ → ι → Q.1)
    (hu : ∀ k ∈ J, WeightedWeakSolution Q M S (f k) (u k)) :
    WeightedWeakSolution Q M S (∑ k ∈ J, f k) (∑ k ∈ J, u k) := by
  have he : (∑ k ∈ J, u k) = MatrixEnergy.tuple Q hQ M S hM
      (MatrixEnergy.solution Q hQ M S hM a ha hlower (WithLp.toLp 2 (∑ k ∈ J, f k))) := by
    calc
      _ = ∑ k ∈ J, MatrixEnergy.tuple Q hQ M S hM
          (MatrixEnergy.solution Q hQ M S hM a ha hlower (WithLp.toLp 2 (f k))) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact MatrixEnergy.weightedWeakSolution_unique Q hQ M S hM a ha hlower hMm (f k) (u k) (hu k hk)
      _ = _ := by rw [WithLp.toLp_sum, map_sum, map_sum]
  rw [he]
  exact MatrixEnergy.solution_weightedWeakSolution Q hQ M S hM a ha hlower hMm _

omit [DecidableEq ι] in
/-- Pairing a finite superposition with an L² coefficient vector is the
sum of the separate pairings. The integrability of each pairing follows
from L² Cauchy--Schwarz. -/
theorem pairing_finset_sum (J : Finset κ) (b : ι → Lp ℝ 2 ν)
    (u : κ → ι → Lp ℝ 2 ν) :
    (∫ x, ∑ j, b j x * (∑ k ∈ J, u k) j x ∂ν) =
      ∑ k ∈ J, ∫ x, ∑ j, b j x * u k j x ∂ν := by
  have hpair (v : ι → Lp ℝ 2 ν) :
      (∫ x, ∑ j, b j x * v j x ∂ν) = ∑ j, inner ℝ (b j) (v j) := by
    have hi (j : ι) : Integrable (fun x => b j x * v j x) ν :=
      (Lp.memLp (b j)).integrable_mul (Lp.memLp (v j))
    rw [integral_finsetSum _ fun j _ => hi j]
    apply Finset.sum_congr rfl
    intro j _
    simp only [L2.inner_def, Real.inner_apply]
  rw [hpair]
  simp_rw [hpair]
  simp only [Finset.sum_apply, inner_sum]
  exact Finset.sum_comm

end Riesz2.WeightedWeakSuperposition
