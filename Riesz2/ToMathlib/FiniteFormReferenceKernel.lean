/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.ScalarFormHalfGenerator
public import Mathlib.Topology.Instances.Matrix

/-!
# Finite reference inverses over an arbitrary real scalar form

A positive definite finite matrix is interpolated with the identity on the
compact bounded-transform interval. Its inverse consists of continuous
functions, which act by the proved real calculus. No scalar eigenbasis is
assumed. Infrastructure for the proof of Proposition 5.15.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Riesz2.FiniteFormReferenceKernel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The bounded-transform pencil on its entire compact parameter carrier. -/
def pencil (A : Matrix ι ι ℝ) (u : Set.Icc (0 : ℝ) 1) : Matrix ι ι ℝ :=
  (1 - u.val) • 1 + u.val • A

omit [Fintype ι] in
/-- Inversion is never evaluated at a singular matrix, even at either endpoint. -/
theorem pencil_posDef (A : Matrix ι ι ℝ) (hA : A.PosDef) (u : Set.Icc (0 : ℝ) 1) :
    (pencil A u).PosDef := by
  rcases eq_or_lt_of_le u.property.2 with hu | hu
  · have he : pencil A u = A := by simp only [pencil, hu, sub_self, zero_smul, one_smul, zero_add]
    rw [he]
    exact hA
  · exact (Matrix.PosDef.one.smul (sub_pos.mpr hu)).add_posSemidef (hA.posSemidef.smul u.property.1)

/-- The inverse pencil is continuous on the closed interval. -/
theorem continuous_inverse_pencil (A : Matrix ι ι ℝ) (hA : A.PosDef) :
    Continuous (fun u : Set.Icc (0 : ℝ) 1 => (pencil A u)⁻¹) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  have hp : Continuous (pencil A) := by unfold pencil; fun_prop
  apply (continuousAt_matrix_inv (pencil A u) ?_).comp hp.continuousAt
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ (pencil_posDef A hA u).det_pos.ne'

/-- Each inverse entry is a continuous function on the compact parameter interval. -/
def inverseEntry (A : Matrix ι ι ℝ) (hA : A.PosDef) (i j : ι) : C(Set.Icc (0 : ℝ) 1, ℝ) :=
  ⟨fun u => (pencil A u)⁻¹ i j, (continuous_apply j).comp
    ((continuous_apply i).comp (continuous_inverse_pencil A hA))⟩

/-- The coordinate function on the compact interval. -/
def coordinate : C(Set.Icc (0 : ℝ) 1, ℝ) := ⟨Subtype.val, continuous_subtype_val⟩

/-- The scalar value kernel in bounded-transform coordinates. -/
def valueEntry (A : Matrix ι ι ℝ) (hA : A.PosDef) (i j : ι) : C(Set.Icc (0 : ℝ) 1, ℝ) :=
  coordinate * inverseEntry A hA i j

/-- The scalar half-generator kernel in bounded-transform coordinates. -/
def halfEntry (A : Matrix ι ι ℝ) (hA : A.PosDef) (i j : ι) : C(Set.Icc (0 : ℝ) 1, ℝ) :=
  ⟨fun u => Real.sqrt u.val * Real.sqrt (1 - u.val), by fun_prop⟩ * inverseEntry A hA i j

/-- The exact scalar pencil identity, before applying functional calculus. -/
theorem inverseEntry_equation (A : Matrix ι ι ℝ) (hA : A.PosDef) (i k : ι) :
    (1 - coordinate) * inverseEntry A hA i k +
      ∑ j, A i j • valueEntry A hA j k = if i = k then 1 else 0 := by
  apply ContinuousMap.ext
  intro u
  have hm := Matrix.mul_nonsing_inv (pencil A u)
    (isUnit_iff_ne_zero.mpr (pencil_posDef A hA u).det_pos.ne')
  change ((1 - u.val) • 1 + u.val • A) * (pencil A u)⁻¹ = 1 at hm
  rw [add_mul, smul_mul_assoc, smul_mul_assoc, one_mul] at hm
  have he := congrArg (fun B : Matrix ι ι ℝ => B i k) hm
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.one_apply] at he
  simp only [ContinuousMap.add_apply, ContinuousMap.mul_apply, ContinuousMap.sub_apply,
    ContinuousMap.one_apply, ContinuousMap.sum_apply, ContinuousMap.smul_apply]
  have hrhs : ((if i = k then (1 : C(Set.Icc (0 : ℝ) 1, ℝ)) else 0) u) =
      (if i = k then (1 : ℝ) else 0) := by split_ifs <;> rfl
  rw [hrhs]
  change (1 - u.val) * (pencil A u)⁻¹ i k +
    ∑ j, A i j * (u.val * (pencil A u)⁻¹ j k) = if i = k then 1 else 0
  rw [Finset.mul_sum] at he
  have he' : (∑ j, A i j * (u.val * (pencil A u)⁻¹ j k)) =
      ∑ j, u.val * (A i j * (pencil A u)⁻¹ j k) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he']
  split_ifs at he ⊢ <;> exact he

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}
  (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)

/-- Continuous functional calculus of the actual scalar form's bounded transform. -/
def lift : C(Set.Icc (0 : ℝ) 1, ℝ) →ₐ[ℝ] (Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) :=
  RealL2ContinuousCalculus.intervalHom ν (ScalarFormResolvent.resolvent Q hQ 1 zero_lt_one)
    (ScalarFormResolvent.isSelfAdjoint Q hQ 1 zero_lt_one)

theorem lift_coordinate : lift Q hQ coordinate = ScalarFormResolvent.resolvent Q hQ 1 zero_lt_one :=
  RealL2ContinuousCalculus.intervalHom_coordinate ν _
    (ScalarFormResolvent.isPositive Q hQ 1 zero_lt_one)
    (ScalarFormResolvent.transform_positive_contraction Q hQ).2

/-- The actual bounded real L² value-kernel entry. -/
def valueKernel (A : Matrix ι ι ℝ) (hA : A.PosDef) (i j : ι) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  lift Q hQ (valueEntry A hA i j)

/-- The actual bounded real L² half-generator-kernel entry. -/
def halfKernel (A : Matrix ι ι ℝ) (hA : A.PosDef) (i j : ι) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  lift Q hQ (halfEntry A hA i j)

/-- The inverse kernel takes its values in the whole form domain. -/
def solutionKernel (A : Matrix ι ι ℝ) (hA : A.PosDef) (i j : ι) :
    Lp ℝ 2 ν →L[ℝ] ScalarFormHilbert.Space Q hQ :=
  (ScalarFormHilbert.shiftedSolution Q hQ 1 zero_lt_one).comp (lift Q hQ (inverseEntry A hA i j))

/-- The ambient value of the form-domain kernel is the bounded calculus kernel. -/
theorem solutionKernel_value (A : Matrix ι ι ℝ) (hA : A.PosDef) (i j : ι) (f : Lp ℝ 2 ν) :
    ScalarFormHilbert.value Q hQ (solutionKernel Q hQ A hA i j f) = valueKernel Q hQ A hA i j f := by
  have he : valueKernel Q hQ A hA i j =
      ScalarFormResolvent.resolvent Q hQ 1 zero_lt_one * lift Q hQ (inverseEntry A hA i j) := by
    unfold valueKernel valueEntry
    rw [map_mul, lift_coordinate]
  rw [he]
  rfl

/-- Any proved uniform scalar bound transfers to the real value operator. -/
theorem valueKernel_norm_le_internal (A : Matrix ι ι ℝ) (hA : A.PosDef) (i j : ι)
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ u, |valueEntry A hA i j u| ≤ C) :
    ‖valueKernel Q hQ A hA i j‖ ≤ C :=
  RealL2ContinuousCalculus.norm_intervalHom_le ν _ _ _ hC h

/-- The same transfer for the half-generator multiplier. -/
theorem halfKernel_norm_le_internal (A : Matrix ι ι ℝ) (hA : A.PosDef) (i j : ι)
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ u, |halfEntry A hA i j u| ≤ C) :
    ‖halfKernel Q hQ A hA i j‖ ≤ C :=
  RealL2ContinuousCalculus.norm_intervalHom_le ν _ _ _ hC h

/-- The exact lifted operator equation, including the component constant mode. -/
theorem kernel_equation (A : Matrix ι ι ℝ) (hA : A.PosDef) (i k : ι) :
    (1 - ScalarFormResolvent.resolvent Q hQ 1 zero_lt_one) *
        lift Q hQ (inverseEntry A hA i k) +
      ∑ j, A i j • valueKernel Q hQ A hA j k = if i = k then 1 else 0 := by
  have he := congrArg (lift Q hQ) (inverseEntry_equation A hA i k)
  simp only [map_add, map_mul, map_sub, map_one, map_sum, map_smul,
    lift_coordinate] at he
  change _ = _ at he
  split_ifs at he ⊢ <;> simpa only [map_one, map_zero, valueKernel] using he

/-- Identification with the unrestricted finite-vector weak inverse,
the proof of Proposition 5.15 (one source column). -/
theorem solutionKernel_solves (A : Matrix ι ι ℝ) (hA : A.PosDef) (i k : ι)
    (f : Lp ℝ 2 ν) (w : ScalarFormHilbert.Space Q hQ) :
    Q.2 (ScalarFormHilbert.equiv Q hQ (solutionKernel Q hQ A hA i k f))
        (ScalarFormHilbert.equiv Q hQ w) +
      ∑ j, A i j * inner ℝ (valueKernel Q hQ A hA j k f) (ScalarFormHilbert.value Q hQ w) =
        inner ℝ (if i = k then f else 0) (ScalarFormHilbert.value Q hQ w) := by
  have he := ScalarFormHilbert.shiftedSolution_solves Q hQ 1 zero_lt_one
    (lift Q hQ (inverseEntry A hA i k) f) w
  have hop := congrArg (fun B : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν =>
    inner ℝ (B f) (ScalarFormHilbert.value Q hQ w)) (kernel_equation Q hQ A hA i k)
  simp only [add_apply, mul_apply_eq_comp, sub_apply, one_apply_eq_self,
    sum_apply, smul_apply, inner_add_left, inner_sub_left, sum_inner, real_inner_smul_left] at hop
  change _ + 1 * inner ℝ (ScalarFormHilbert.value Q hQ (solutionKernel Q hQ A hA i k f)) _ = _ at he
  rw [solutionKernel_value, one_mul] at he
  have hv := solutionKernel_value Q hQ A hA i k f
  change ScalarFormResolvent.resolvent Q hQ 1 zero_lt_one
    (lift Q hQ (inverseEntry A hA i k) f) = _ at hv
  rw [hv] at hop
  change Q.2 (ScalarFormHilbert.equiv Q hQ (solutionKernel Q hQ A hA i k f))
    (ScalarFormHilbert.equiv Q hQ w) + _ = _ at he
  split_ifs at hop ⊢ <;> simp only [one_apply_eq_self, zero_apply, inner_zero_left] at hop ⊢ <;>
    linarith

/-- Square root of the coordinate on the compact interval. -/
def rootCoordinate : C(Set.Icc (0 : ℝ) 1, ℝ) :=
  ⟨fun u => Real.sqrt u.val, by fun_prop⟩

/-- Square root of the complementary coordinate on the compact interval. -/
def rootComplement : C(Set.Icc (0 : ℝ) 1, ℝ) :=
  ⟨fun u => Real.sqrt (1 - u.val), by fun_prop⟩

/-- The compact calculus gives the actual positive square root of the resolvent. -/
theorem lift_rootCoordinate :
    lift Q hQ rootCoordinate =
      RealL2ContinuousCalculus.sqrt ν (ScalarFormResolvent.resolvent Q hQ 1 zero_lt_one)
        (ScalarFormResolvent.isPositive Q hQ 1 zero_lt_one) := by
  apply RealL2ContinuousCalculus.sqrt_unique
  · apply RealL2ContinuousCalculus.positive_intervalHom
    intro u
    exact Real.sqrt_nonneg _
  · have hs : rootCoordinate * rootCoordinate = coordinate := by
      apply ContinuousMap.ext
      intro u
      exact Real.mul_self_sqrt u.property.1
    rw [← map_mul, hs, lift_coordinate]

/-- The complementary compact multiplier gives its actual positive square root. -/
theorem lift_rootComplement :
    lift Q hQ rootComplement =
      RealL2ContinuousCalculus.sqrt ν (1 - ScalarFormResolvent.resolvent Q hQ 1 zero_lt_one)
        (ScalarFormResolvent.transform_complement_positive Q hQ) := by
  apply RealL2ContinuousCalculus.sqrt_unique
  · apply RealL2ContinuousCalculus.positive_intervalHom
    intro u
    exact Real.sqrt_nonneg _
  · have hs : rootComplement * rootComplement = 1 - coordinate := by
      apply ContinuousMap.ext
      intro u
      exact Real.mul_self_sqrt (sub_nonneg.mpr u.property.2)
    rw [← map_mul, hs, map_sub, map_one, lift_coordinate]

/-- The half kernel is exactly the half-generator applied to the form solution kernel, the proof of Proposition 5.15. -/
theorem solutionKernel_half (A : Matrix ι ι ℝ) (hA : A.PosDef) (i j : ι) (f : Lp ℝ 2 ν) :
    ScalarFormHalfGenerator.halfGenerator Q hQ (solutionKernel Q hQ A hA i j f) =
      halfKernel Q hQ A hA i j f := by
  change ScalarFormHalfGenerator.halfGenerator Q hQ
    (ScalarFormHilbert.shiftedSolution Q hQ 1 zero_lt_one (lift Q hQ (inverseEntry A hA i j) f)) = _
  rw [ScalarFormHalfGenerator.halfGenerator_shiftedSolution,
    ← lift_rootCoordinate, ← lift_rootComplement]
  have he : halfEntry A hA i j = rootComplement * rootCoordinate * inverseEntry A hA i j := by
    apply ContinuousMap.ext
    intro u
    change (Real.sqrt u.val * Real.sqrt (1 - u.val)) * _ =
      (Real.sqrt (1 - u.val) * Real.sqrt u.val) * _
    ring
  unfold halfKernel
  rw [he, map_mul, map_mul]
  rfl

/-- Scalar row-sum bounds transfer directly, without taking absolute values
entry by entry and losing cancellation. -/
theorem valueKernel_mass_le_internal (A : Matrix ι ι ℝ) (hA : A.PosDef) (i : ι)
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ u, |∑ j, valueEntry A hA i j u| ≤ C) :
    ‖∑ j, valueKernel Q hQ A hA i j‖ ≤ C := by
  change ‖∑ j, lift Q hQ (valueEntry A hA i j)‖ ≤ C
  rw [← map_sum]
  apply RealL2ContinuousCalculus.norm_intervalHom_le ν _ _ _ hC
  intro u
  simpa only [ContinuousMap.sum_apply] using h u

/-- The same exact row-sum transfer for half-generator kernels. -/
theorem halfKernel_mass_le_internal (A : Matrix ι ι ℝ) (hA : A.PosDef) (i : ι)
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ u, |∑ j, halfEntry A hA i j u| ≤ C) :
    ‖∑ j, halfKernel Q hQ A hA i j‖ ≤ C := by
  change ‖∑ j, lift Q hQ (halfEntry A hA i j)‖ ≤ C
  rw [← map_sum]
  apply RealL2ContinuousCalculus.norm_intervalHom_le ν _ _ _ hC
  intro u
  simpa only [ContinuousMap.sum_apply] using h u

omit [DecidableEq ι] in
/-- Every constant finite-matrix pairing of L² tuples is integrable. -/
theorem integrable_constant_pair (A : Matrix ι ι ℝ) (v w : ι → Lp ℝ 2 ν) :
    Integrable (matrixFieldPair (fun _ => A) v w) ν := by
  unfold matrixFieldPair
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  have hh := (L2.integrable_inner (𝕜 := ℝ) (v i) (w j)).const_mul (A i j)
  convert hh using 1
  ext x
  simp only [RCLike.inner_apply, conj_trivial]
  ring

omit [DecidableEq ι] in
/-- The constant finite-matrix integral is exactly the corresponding L² inner sum. -/
theorem integral_constant_pair (A : Matrix ι ι ℝ) (v w : ι → Lp ℝ 2 ν) :
    (∫ x, matrixFieldPair (fun _ => A) v w x ∂ν) = ∑ i, ∑ j, A i j * inner ℝ (v i) (w j) := by
  have he : matrixFieldPair (fun _ => A) v w =
      fun x => ∑ i, ∑ j, A i j * inner ℝ (v i x) (w j x) := by
    funext x
    unfold matrixFieldPair
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [RCLike.inner_apply, conj_trivial]
    ring
  rw [he, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul, L2.inner_def]
    · intro j _
      exact (L2.integrable_inner (𝕜 := ℝ) (v i) (w j)).const_mul _
  · intro i _
    apply integrable_finsetSum
    intro j _
    exact (L2.integrable_inner (𝕜 := ℝ) (v i) (w j)).const_mul _

/-- The kernel column is a solution in the literal full-component
`WeightedWeakSolution` encoding, the proof of Proposition 5.15. -/
theorem solutionKernel_weightedWeakSolution (A : Matrix ι ι ℝ) (hA : A.PosDef)
    (k : ι) (f : Lp ℝ 2 ν) :
    WeightedWeakSolution Q (fun _ => A) ⊤ (fun i => if i = k then f else 0)
      (fun i => ScalarFormHilbert.equiv Q hQ (solutionKernel Q hQ A hA i k f)) := by
  let v := fun i => ScalarFormHilbert.equiv Q hQ (solutionKernel Q hQ A hA i k f)
  refine ⟨⟨Filter.Eventually.of_forall (fun _ => Submodule.mem_top),
    integrable_constant_pair A (fun i => (v i).val) (fun i => (v i).val)⟩, ?_⟩
  intro w _
  refine ⟨integrable_constant_pair A (fun i => (v i).val) (fun i => (w i).val), ?_⟩
  rw [integral_constant_pair]
  have he := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => solutionKernel_solves Q hQ A hA i k f ((ScalarFormHilbert.equiv Q hQ).symm (w i)))
  simp only [LinearEquiv.apply_symm_apply, Finset.sum_add_distrib] at he
  have hv (i : ι) : (v i).val = valueKernel Q hQ A hA i k f := solutionKernel_value Q hQ A hA i k f
  have hsym (i j : ι) : A j i = A i j := by
    simpa only [Matrix.conjTranspose_apply, star_trivial] using
      congrArg (fun B : Matrix ι ι ℝ => B i j) hA.isHermitian
  have hswap : (∑ i, ∑ j, A i j * inner ℝ (v i).val (w j).val) =
      ∑ i, ∑ j, A i j * inner ℝ (valueKernel Q hQ A hA j k f) (w i).val := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym, hv]
  rw [hswap]
  exact he

end Riesz2.FiniteFormReferenceKernel
