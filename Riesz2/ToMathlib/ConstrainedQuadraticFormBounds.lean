/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.MatrixEnergySpaces

/-!
# Zero-sum quadratic bounds in a nonnegative bilinear form

Finite real quadratic estimates transfer to any nonnegative symmetric
bilinear form. The zero-sum constraint is preserved by factoring its Gram
matrix. In particular no coordinate representation of a scalar Dirichlet
form, or existence of a pointwise gradient, is needed.
-/

public section
noncomputable section

open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace Riesz2.ConstrainedQuadraticFormBounds

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℝ V]

/-- A finite family in a nonnegative symmetric bilinear form has a real Gram
factorization preserving its zero-sum constraint. Degenerate forms and empty
index sets are included. -/
theorem gram_factor_zero_sum (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hs : ∀ u v, B u v = B v u) (hn : ∀ u, 0 ≤ B u u)
    (u : ι → V) (hu : ∑ i, u i = 0) :
    ∃ R : Matrix ι ι ℝ,
      (∀ i j, B (u i) (u j) = ∑ k, R k i * R k j) ∧
      ∀ k, ∑ i, R k i = 0 := by
  let G : Matrix ι ι ℝ := fun i j => B (u i) (u j)
  have hG : G.PosSemidef := by
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    refine ⟨?_, fun c => ?_⟩
    · ext i j
      exact hs _ _
    · have h := hn (∑ i, c i • u i)
      simpa only [G, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum,
        hs, mul_left_comm, mul_comm, mul_assoc] using h
  let R := CFC.sqrt G
  have hR : Rᵀ * R = G := MatrixEnergy.sqrt_factor G hG
  have he (i j) : B (u i) (u j) = ∑ k, R k i * R k j := by
    exact (congrArg (fun A => A i j) hR).symm
  have hz : (∑ k, (∑ i, R k i) ^ 2) = 0 := by
    calc
      _ = ∑ k, ∑ i, ∑ j, R k i * R k j := by
        apply Finset.sum_congr rfl
        intro k _
        rw [sq, Finset.sum_mul]
        simp_rw [Finset.mul_sum]
      _ = ∑ i, ∑ j, ∑ k, R k i * R k j := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = ∑ i, ∑ j, B (u i) (u j) := by simp_rw [← he]
      _ = B (∑ i, u i) (∑ j, u j) := by
        simp only [map_sum, LinearMap.sum_apply]
        rw [Finset.sum_comm]
      _ = 0 := by rw [hu]; simp
  refine ⟨R, he, fun k => ?_⟩
  exact sq_eq_zero_iff.mp ((Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => sq_nonneg (∑ j, R i j))).mp hz k (Finset.mem_univ k))

/-- Internal transfer principle for a quadratic estimate on zero-sum real
vectors. It applies directly to the scalar form of a zero-sum tuple and
retains the exact coefficient and weights. -/
theorem transfer (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hs : ∀ u v, B u v = B v u) (hn : ∀ u, 0 ≤ B u u)
    (K : Matrix ι ι ℝ) (w : ι → ℝ) (C : ℝ)
    (hb : ∀ g : ι → ℝ, ∑ i, g i = 0 →
      (∑ i, ∑ j, K i j * g i * g j) ≤ C * ∑ i, w i * (g i) ^ 2)
    (u : ι → V) (hu : ∑ i, u i = 0) :
    (∑ i, ∑ j, K i j * B (u i) (u j)) ≤ C * ∑ i, w i * B (u i) (u i) := by
  obtain ⟨R, he, hz⟩ := gram_factor_zero_sum B hs hn u hu
  calc
    _ = ∑ k, ∑ i, ∑ j, K i j * R k i * R k j := by
      simp_rw [he, Finset.mul_sum]
      calc
        _ = ∑ i, ∑ k, ∑ j, K i j * R k i * R k j := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = _ := Finset.sum_comm
    _ ≤ ∑ k, C * ∑ i, w i * (R k i) ^ 2 :=
      Finset.sum_le_sum (fun k _ => hb (R k) (hz k))
    _ = C * ∑ i, w i * B (u i) (u i) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.mul_sum, he i i]
      simp only [sq]

end Riesz2.ConstrainedQuadraticFormBounds
