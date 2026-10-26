/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.OperatorSchur

/-!
# Resolvent comparison over one scalar form

The two bounded coefficient operators use the same finite product of the
scalar domain. The residual is constructed from their difference.
No second scalar generator or comparison of two measures is introduced.
-/

@[expose] public section
noncomputable section
open MeasureTheory InnerProductSpace
open scoped BigOperators

namespace Riesz2.CommonScalarResolventComparison

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι] {ρ : Measure α}

/-- Internal same-form comparison used in Subsection 4.5.
The residual is the actual bounded operator difference applied to the
second solution. This is an abstract operator lemma, not the physical
inverse-power residual estimate. -/
theorem internal_comparison (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q)
    (R S : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ) →L[ℝ] PiLp 2 (fun _ : ι => Lp ℝ 2 ρ))
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hR : ∀ f, a * ‖f‖ ^ 2 ≤ inner ℝ (R f) f)
    (hS : ∀ f, b * ‖f‖ ^ 2 ≤ inner ℝ (S f) f)
    (f : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ)) :
    let u := OperatorSchur.vectorSolution Q hQ R a ha hR f
    let v := OperatorSchur.vectorSolution Q hQ S b hb hS f
    ‖OperatorSchur.vectorValues Q hQ (u - v)‖ +
      Real.sqrt (OperatorSchur.vectorEnergy Q hQ (u - v) (u - v)) ≤
        (a⁻¹ + (Real.sqrt a)⁻¹) *
          ‖(S - R) (OperatorSchur.vectorValues Q hQ v)‖ := by
  intro u v
  let g := (S - R) (OperatorSchur.vectorValues Q hQ v)
  let w := OperatorSchur.vectorSolution Q hQ R a ha hR g
  have heq : u - v = w := by
    apply OperatorSchur.vectorSolution_unique Q hQ R a ha hR g
    intro z
    have hu := OperatorSchur.vectorSolution_solves Q hQ R a ha hR f z
    have hv := OperatorSchur.vectorSolution_solves Q hQ S b hb hS f z
    change OperatorSchur.vectorForm Q hQ R u z = _ at hu
    change OperatorSchur.vectorForm Q hQ S v z = _ at hv
    rw [map_sub, sub_apply]
    simp only [OperatorSchur.vectorForm_apply] at hu hv ⊢
    dsimp only [g]
    rw [sub_apply, inner_sub_left]
    linarith
  have hn := OperatorSchur.vectorSolution_value_norm_le Q hQ R a ha hR g
  change ‖OperatorSchur.vectorValues Q hQ w‖ ≤ a⁻¹ * ‖g‖ at hn
  have hmass (z : MatrixEnergy.Vector (ι := ι) Q hQ) :
      a * ‖OperatorSchur.vectorValues Q hQ z‖ ^ 2 ≤
        OperatorSchur.vectorForm Q hQ R z z := by
    exact (hR _).trans (le_add_of_nonneg_left (OperatorSchur.vectorEnergy_nonneg Q hQ z))
  have henergy : OperatorSchur.vectorForm Q hQ R w w ≤ a⁻¹ * ‖g‖ ^ 2 := by
    exact CoerciveSolution.solution_energy_le (OperatorSchur.vectorForm Q hQ R)
      (min 1 a) (lt_min zero_lt_one ha) (OperatorSchur.vectorForm_coercive Q hQ R a hR)
      (OperatorSchur.vectorValues Q hQ) a ha hmass g
  have hgrad : OperatorSchur.vectorEnergy Q hQ w w ≤ a⁻¹ * ‖g‖ ^ 2 := by
    apply le_trans _ henergy
    exact le_add_of_nonneg_right ((mul_nonneg ha.le (sq_nonneg _)).trans (hR _))
  have hgrad' := Real.sqrt_le_sqrt hgrad
  rw [Real.sqrt_mul (inv_nonneg.mpr ha.le), Real.sqrt_inv, Real.sqrt_sq (norm_nonneg _)] at hgrad'
  rw [heq]
  exact (add_le_add hn hgrad').trans_eq (by ring)

end Riesz2.CommonScalarResolventComparison
