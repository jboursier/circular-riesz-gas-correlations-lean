/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.CoerciveSolutionMaps
public import Riesz2.HelfferSjostrand.MaximumPrinciple
public import Riesz2.Frozen.IsConservativeScalarForm

/-!
# Abstract long-range equations

Existence, energy and maximum bounds in Subsection 5.1. The coefficient
in the weak equation is `β • M`, so that the scalar diffusion coefficient
remains one. Scalar dimension and component dimension are independent. The
variational argument works for arbitrary measurable positive matrix fields,
including bounded fields.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace Riesz2.AbstractEquation

section Projection

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι] {ρ : Measure α}

/-- Orthogonal projection of an L² source onto the zero-sum component space.
The finite-dimensional projection is applied in the component index alone. -/
def centeredSource (f : ι → Lp ℝ 2 ρ) (i : ι) : Lp ℝ 2 ρ :=
  f i - (Fintype.card ι : ℝ)⁻¹ • ∑ j, f j

/-- The component projection takes values in the zero-sum L² subspace.
Together with `centeredSource_pair`, this identifies the orthogonal projection. -/
theorem sum_centeredSource [Nonempty ι] (f : ι → Lp ℝ 2 ρ) :
    ∑ i, centeredSource f i = 0 := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [centeredSource, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    mul_inv_cancel₀ hn, one_smul, sub_self]

/-- An a.e. zero-sum test has zero sum as an actual L² class. -/
theorem sum_values_eq_zero (h : ι → Lp ℝ 2 ρ)
    (hh : ∀ᵐ x ∂ρ, ∑ i, h i x = 0) : ∑ i, h i = 0 := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ h, hh,
    Lp.coeFn_zero ℝ 2 ρ] with x hx hy hz
  exact hx.trans (hy.trans hz.symm)

/-- Projecting the source leaves its pairing with every zero-sum test unchanged. -/
theorem centeredSource_pair (f h : ι → Lp ℝ 2 ρ)
    (hh : ∀ᵐ x ∂ρ, ∑ i, h i x = 0) :
    (∑ i, inner ℝ (centeredSource f i) (h i)) = ∑ i, inner ℝ (f i) (h i) := by
  simp only [centeredSource, inner_sub_left, real_inner_smul_left,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← inner_sum,
    sum_values_eq_zero h hh, inner_zero_right, mul_zero, sub_zero]

/-- The constrained equation depends only on the projected source. -/
theorem centeredSource_weak_iff (Q : ScalarFormData ρ) (M : α → Matrix ι ι ℝ)
    (f : ι → Lp ℝ 2 ρ) (u : ι → Q.1) :
    WeightedWeakSolution Q M (zeroSumComponents ι) (centeredSource f) u ↔
      WeightedWeakSolution Q M (zeroSumComponents ι) f u := by
  constructor <;> intro hu <;> refine ⟨hu.1, fun h hh => ?_⟩
  · obtain ⟨hi, he⟩ := hu.2 h hh
    exact ⟨hi, he.trans (centeredSource_pair f _ hh.1)⟩
  · obtain ⟨hi, he⟩ := hu.2 h hh
    exact ⟨hi, he.trans (centeredSource_pair f _ hh.1).symm⟩

/-- The one-component constrained source is zero, including on a scalar
probability space of dimension zero. -/
theorem centeredSource_fin_one (f : Fin 1 → Lp ℝ 2 ρ) : centeredSource f = 0 := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [centeredSource]

end Projection

section Equation

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι]
  {ρ : Measure α} (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q)
  (β : ℝ) (hβ : 0 < β) (M : α → Matrix ι ι ℝ)
  (hMm : ∀ i j, Measurable (fun x => M x i j))
  (a : ℝ) (ha : 0 < a)
  (hM : ∀ᵐ x ∂ρ, (∀ i j, M x i j = M x j i) ∧
    ∀ z : ι → ℝ, a * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j)

include hβ hM in
omit [DecidableEq ι] in
/-- Scaling the matrix changes the coercivity constant by exactly β. -/
theorem scaled_lower : ∀ᵐ x ∂ρ,
    (∀ i j, (β • M x) i j = (β • M x) j i) ∧
    ∀ z : ι → ℝ, (β * a) * (∑ i, z i ^ 2) ≤
      ∑ i, ∑ j, z i * (β • M x) i j * z j := by
  filter_upwards [hM] with x hx
  refine ⟨fun i j => by simp only [Matrix.smul_apply, smul_eq_mul, hx.1 i j], fun z => ?_⟩
  calc
    β * a * (∑ i, z i ^ 2) = β * (a * (∑ i, z i ^ 2)) := by ring
    _ ≤ β * (∑ i, ∑ j, z i * M x i j * z j) :=
      mul_le_mul_of_nonneg_left (hx.2 z) hβ.le
    _ = _ := by
      simp only [Finset.mul_sum, Matrix.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

include hβ ha hM in
omit [DecidableEq ι] in
/-- Positivity certificate for the existing natural matrix-energy graph. -/
theorem scaled_posSemidef : ∀ᵐ x ∂ρ, (β • M x).PosSemidef := by
  filter_upwards [scaled_lower β hβ M a hM] with x hx
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, fun z => ?_⟩
  · ext i j
    exact hx.1 j i
  · have hp : 0 ≤ β * a * ∑ i, z i ^ 2 :=
      mul_nonneg (mul_pos hβ ha).le (Finset.sum_nonneg (fun i _ => sq_nonneg _))
    simpa only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum, mul_assoc]
      using hp.trans (hx.2 z)

include hMm in
omit [DecidableEq ι] [Fintype ι] in
theorem scaled_measurable (i j : ι) : Measurable (fun x => (β • M x) i j) :=
  measurable_const.mul (hMm i j)

include hQ hβ hMm ha hM in
/-- See Subsection 5.1 of the paper, variational part: unique weak solvability and both
sharp energy bounds for every fixed component subspace. In particular `⊤` and
`zeroSumComponents` give the two equations in the statement. -/
theorem existence_energy (S : Submodule ℝ (ι → ℝ)) (f : ι → Lp ℝ 2 ρ) :
    (∃! u : ι → Q.1, WeightedWeakSolution Q (fun x => β • M x) S f u) ∧
    ∀ u : ι → Q.1, WeightedWeakSolution Q (fun x => β • M x) S f u →
      ‖(WithLp.toLp 2 (fun i => (u i).val) : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ))‖ ≤
        (β * a)⁻¹ * ‖(WithLp.toLp 2 f : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ))‖ ∧
      Real.sqrt (∑ i, Q.2 (u i) (u i)) ≤
        (Real.sqrt (β * a))⁻¹ * ‖(WithLp.toLp 2 f : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ))‖ := by
  let P := fun x => β • M x
  have hp := scaled_posSemidef β hβ M a ha hM
  have hl : ∀ᵐ x ∂ρ, ∀ z ∈ S, (β * a) * (∑ i, z i ^ 2) ≤
      ∑ i, ∑ j, z i * P x i j * z j :=
    (scaled_lower β hβ M a hM).mono (fun x hx z _ => hx.2 z)
  have hpm := scaled_measurable β M hMm
  refine ⟨MatrixEnergy.weightedWeakSolution_existsUnique Q hQ P S hp
    (β * a) (mul_pos hβ ha) hl hpm f, fun u hu => ?_⟩
  have he := MatrixEnergy.weightedWeakSolution_unique Q hQ P S hp
    (β * a) (mul_pos hβ ha) hl hpm f u hu
  rw [he]
  exact ⟨MatrixEnergy.solution_value_norm_le Q hQ P S hp (β * a)
    (mul_pos hβ ha) hl (WithLp.toLp 2 f),
    MatrixEnergy.solution_gradient_le Q hQ P S hp (β * a)
    (mul_pos hβ ha) hl (WithLp.toLp 2 f)⟩

end Equation

/-- See Subsection 5.1 of the paper: unique unrestricted and constrained solutions, their
L² and gradient bounds, and the two Euclidean essential-supremum bounds. The
constrained bound uses the orthogonal component projection of the source.
The variational statement is valid even without an upper bound on M. -/
theorem existence_energy_maximum (d : ℕ)
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ρ]
    (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q)
    (β : ℝ) (hβ : 0 < β) (m : ℕ+)
    (M : EuclideanSpace ℝ (Fin d) → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j)) (a : ℝ) (ha : 0 < a)
    (hM : ∀ᵐ x ∂ρ, (∀ i j, M x i j = M x j i) ∧
      ∀ z : Fin (m : ℕ) → ℝ,
        a * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j)
    (f : Fin (m : ℕ) → Lp ℝ 2 ρ) :
    (∃! u, WeightedWeakSolution Q (fun x => β • M x) ⊤ f u) ∧
    (∃! u, WeightedWeakSolution Q (fun x => β • M x)
      (zeroSumComponents (Fin (m : ℕ))) f u) ∧
    (∀ (S : Submodule ℝ (Fin (m : ℕ) → ℝ)) u,
      WeightedWeakSolution Q (fun x => β • M x) S f u →
      ‖(WithLp.toLp 2 (fun i => (u i).val) : PiLp 2 (fun _ : Fin (m : ℕ) => Lp ℝ 2 ρ))‖ ≤
        (β * a)⁻¹ * ‖(WithLp.toLp 2 f : PiLp 2 (fun _ : Fin (m : ℕ) => Lp ℝ 2 ρ))‖ ∧
      Real.sqrt (∑ i, Q.2 (u i) (u i)) ≤ (Real.sqrt (β * a))⁻¹ *
        ‖(WithLp.toLp 2 f : PiLp 2 (fun _ : Fin (m : ℕ) => Lp ℝ 2 ρ))‖) ∧
    (∀ u, WeightedWeakSolution Q (fun x => β • M x) ⊤ f u →
      eLpNorm (fun x => WithLp.toLp 2 (fun i => (u i).val x)) ∞ ρ ≤
        ENNReal.ofReal (β * a)⁻¹ * eLpNorm (fun x => WithLp.toLp 2 (fun i => f i x)) ∞ ρ) ∧
    (∀ u, WeightedWeakSolution Q (fun x => β • M x)
      (zeroSumComponents (Fin (m : ℕ))) f u →
      eLpNorm (fun x => WithLp.toLp 2 (fun i => (u i).val x)) ∞ ρ ≤
        ENNReal.ofReal (β * a)⁻¹ *
          eLpNorm (fun x => WithLp.toLp 2 (fun i => centeredSource f i x)) ∞ ρ) := by
  have he := existence_energy Q hQ β hβ M hMm a ha hM
  refine ⟨(he ⊤ f).1, (he (zeroSumComponents _) f).1,
    fun S u hu => (he S f).2 u hu, ?_, ?_⟩
  · intro u hu
    exact maximumPrinciple_closedForm d ρ inferInstance Q hQ m _
      (scaled_measurable β M hMm) (β * a) (mul_pos hβ ha)
      (scaled_lower β hβ M a hM) ⊤ f u hu
  · intro u hu
    exact maximumPrinciple_closedForm d ρ inferInstance Q hQ m _
      (scaled_measurable β M hMm) (β * a) (mul_pos hβ ha)
      (scaled_lower β hβ M a hM) (zeroSumComponents _) (centeredSource f) u
      ((centeredSource_weak_iff Q _ f u).mpr hu)

end Riesz2.AbstractEquation
