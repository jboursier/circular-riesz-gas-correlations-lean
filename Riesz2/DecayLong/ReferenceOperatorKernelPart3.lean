/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.ReferenceOperatorKernel
public import Riesz2.DecayLong.ReferenceOperatorKernelPart2
public import Riesz2.DecayLong.LocalizedBoundaryPart7
public import Riesz2.ToMathlib.FiniteFormReferenceKernel

/-!
# Real operator kernels for the full reference inverse

The scalar reference kernels act by the proved real L² calculus of the
actual scalar form. Both kernels take values in bounded operators.
The value kernel is identified with the unrestricted weak inverse, and the
half kernel with its actual full-domain half-generator. This is part 3 of
the proof of Proposition 5.15.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped BigOperators Fin.NatCast NNReal

universe u

namespace Riesz2.ReferenceOperatorKernelPart3

open FiniteFormReferenceKernel

/-- The reference matrix is strictly positive on the whole component space. -/
theorem reference_posDef (s : Riesz1.RieszExponent) (β : InverseTemperature)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    ((2 * β.val) • rieszMatrix s N hN).PosDef :=
  (rieszMatrix_posDef s N hN).smul (mul_pos two_pos β.property)

/-- The compact value multiplier is exactly the scalar spectral inverse
at `t=(1-u)/u`, with no loss of the zero spectral mode. -/
theorem valueEntry_eq_spectralInverse (s : Riesz1.RieszExponent) (β : InverseTemperature)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (u : Set.Icc (0 : ℝ) 1) (hu : 0 < u.val)
    (i j : Fin (N : ℕ)) :
    valueEntry ((2 * β.val) • rieszMatrix s N hN) (reference_posDef s β N hN) i j u =
      ReferenceOperatorKernel.spectralInverse s β N hN
        ⟨(1 - u.val) / u.val, div_nonneg (sub_nonneg.mpr u.property.2) hu.le⟩ i j := by
  let A := (2 * β.val) • rieszMatrix s N hN
  let t : ℝ≥0 := ⟨(1 - u.val) / u.val, div_nonneg (sub_nonneg.mpr u.property.2) hu.le⟩
  have hp : pencil A u = u.val • (A + (t : ℝ) • 1) := by
    ext k l
    simp only [pencil, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    change (1 - u.val) * (1 : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ) k l + u.val * A k l =
      u.val * (A k l + ((1 - u.val) / u.val) * (1 : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ) k l)
    field_simp [hu.ne']
    ring
  let : Invertible u.val := invertibleOfNonzero hu.ne'
  have hd : IsUnit (A + (t : ℝ) • 1).det := isUnit_iff_ne_zero.mpr
    (ReferenceOperatorKernel.spectralMatrix_posDef s β N hN t).det_pos.ne'
  change u.val * (pencil A u)⁻¹ i j = (A + (t : ℝ) • 1)⁻¹ i j
  have hi : (u.val • (A + (t : ℝ) • 1))⁻¹ = u.val⁻¹ • (A + (t : ℝ) • 1)⁻¹ := by
    simpa only [invOf_eq_inv] using Matrix.inv_smul (A := A + (t : ℝ) • 1) u.val hd
  rw [hp, hi, Matrix.smul_apply, smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ hu.ne', one_mul]

/-- The compact half multiplier is the actual scalar half-generator multiplier. -/
theorem halfEntry_eq_spectralInverse (s : Riesz1.RieszExponent) (β : InverseTemperature)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (u : Set.Icc (0 : ℝ) 1) (hu : 0 < u.val)
    (i j : Fin (N : ℕ)) :
    halfEntry ((2 * β.val) • rieszMatrix s N hN) (reference_posDef s β N hN) i j u =
      Real.sqrt ((1 - u.val) / u.val) *
        ReferenceOperatorKernel.spectralInverse s β N hN
          ⟨(1 - u.val) / u.val, div_nonneg (sub_nonneg.mpr u.property.2) hu.le⟩ i j := by
  rw [← valueEntry_eq_spectralInverse s β N hN u hu i j]
  change (Real.sqrt u.val * Real.sqrt (1 - u.val)) * _ =
    Real.sqrt ((1 - u.val) / u.val) * (u.val * _)
  have hs := Real.sq_sqrt hu.le
  rw [Real.sqrt_div (sub_nonneg.mpr u.property.2)]
  have hr : Real.sqrt u.val ≠ 0 := (Real.sqrt_pos.mpr hu).ne'
  field_simp [hr]
  rw [hs]

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}
  (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)

/-- The bounded real value-kernel entry of the full reference inverse. -/
def valueKernel (s : Riesz1.RieszExponent) (β : InverseTemperature) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (i j : Fin (N : ℕ)) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  FiniteFormReferenceKernel.valueKernel Q hQ _ (reference_posDef s β N hN) i j

/-- The bounded real half-generator-kernel entry of the full reference inverse. -/
def halfKernel (s : Riesz1.RieszExponent) (β : InverseTemperature) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (i j : Fin (N : ℕ)) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  FiniteFormReferenceKernel.halfKernel Q hQ _ (reference_posDef s β N hN) i j

/-- Value-kernel decay on arbitrary real scalar forms,
the proof of Proposition 5.15, case `σ=0`. -/
theorem valueKernel_decay (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (β : InverseTemperature) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (Ω : Type u) [MeasurableSpace Ω] (ν : Measure Ω)
      (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q) (h : Fin (N : ℕ)),
      ‖valueKernel Q hQ s β N hN 0 h‖ ≤
        C * (1 + (Riesz1.cyclicIndexDistance N h 0 : ℝ)) ^ (-(2 - s.val)) := by
  obtain ⟨C, hC, hb⟩ := ReferenceOperatorKernel.spectralInverse_decay hz s β
  refine ⟨C, hC, fun N hN Ω _ ν Q hQ h => ?_⟩
  apply FiniteFormReferenceKernel.valueKernel_norm_le_internal Q hQ _ _ _ _ (by positivity)
  intro u
  rcases eq_or_lt_of_le u.property.1 with hu | hu
  · simp only [valueEntry, coordinate, ContinuousMap.mul_apply, ContinuousMap.coe_mk, ← hu, zero_mul, abs_zero]
    positivity
  · rw [valueEntry_eq_spectralInverse s β N hN u hu]
    exact hb N hN
      ⟨(1 - u.val) / u.val, div_nonneg (sub_nonneg.mpr u.property.2) hu.le⟩ h

/-- Lifting the scalar half-decay estimate to an operator-valued kernel. -/
theorem halfKernel_decay_internal (s : Riesz1.RieszExponent) (β : InverseTemperature)
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (t : ℝ≥0) (h : Fin (N : ℕ)),
      Real.sqrt t * |ReferenceOperatorKernel.spectralInverse s β N hN t 0 h| ≤
        C * (1 + (Riesz1.cyclicIndexDistance N h 0 : ℝ)) ^ (-(1 + (1 - s.val) / 2)))
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (h : Fin (N : ℕ)) :
    ‖halfKernel Q hQ s β N hN 0 h‖ ≤
      C * (1 + (Riesz1.cyclicIndexDistance N h 0 : ℝ)) ^ (-(1 + (1 - s.val) / 2)) := by
  apply FiniteFormReferenceKernel.halfKernel_norm_le_internal Q hQ _ _ _ _ (by positivity)
  intro u
  rcases eq_or_lt_of_le u.property.1 with hu | hu
  · simp only [halfEntry, ContinuousMap.mul_apply, ContinuousMap.coe_mk, ← hu,
      Real.sqrt_zero, zero_mul, abs_zero]
    positivity
  · rw [halfEntry_eq_spectralInverse s β N hN u hu, abs_mul,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact hb N hN
      ⟨(1 - u.val) / u.val, div_nonneg (sub_nonneg.mpr u.property.2) hu.le⟩ h

/-- Exact row-sum norm bounds for both real kernels,
the proof of Proposition 5.15, both values of `σ`. -/
theorem kernel_mass_bounds (s : Riesz1.RieszExponent) (β : InverseTemperature) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (Ω : Type u) [MeasurableSpace Ω] (ν : Measure Ω)
      (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q) (i : Fin (N : ℕ)),
      ‖∑ j, valueKernel Q hQ s β N hN i j‖ ≤ C * (N : ℝ) ^ (-(1 - s.val)) ∧
      ‖∑ j, halfKernel Q hQ s β N hN i j‖ ≤ C * (N : ℝ) ^ (-(1 - s.val) / 2) := by
  obtain ⟨C, hC, hb⟩ := ReferenceOperatorKernel.spectralInverse_mass_bounds s β
  refine ⟨C, hC, fun N hN Ω _ ν Q hQ i => ⟨?_, ?_⟩⟩
  · apply FiniteFormReferenceKernel.valueKernel_mass_le_internal Q hQ _ _ i (by positivity)
    intro u
    rcases eq_or_lt_of_le u.property.1 with hu | hu
    · simp only [valueEntry, coordinate, ContinuousMap.mul_apply, ContinuousMap.coe_mk,
        ← hu, zero_mul, Finset.sum_const_zero, abs_zero]
      positivity
    · simp_rw [valueEntry_eq_spectralInverse s β N hN u hu]
      exact (hb N hN _ i).1
  · apply FiniteFormReferenceKernel.halfKernel_mass_le_internal Q hQ _ _ i (by positivity)
    intro u
    rcases eq_or_lt_of_le u.property.1 with hu | hu
    · simp only [halfEntry, ContinuousMap.mul_apply, ContinuousMap.coe_mk,
        ← hu, Real.sqrt_zero, zero_mul, Finset.sum_const_zero, abs_zero]
      positivity
    · simp_rw [halfEntry_eq_spectralInverse s β N hN u hu]
      rw [← Finset.mul_sum, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact (hb N hN
        ⟨(1 - u.val) / u.val, div_nonneg (sub_nonneg.mpr u.property.2) hu.le⟩ i).2

/-- Both real operator kernels are invariant under cyclic translations,
the proof of Proposition 5.15. -/
theorem kernel_translate (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (β : InverseTemperature) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (i j k : Fin (N : ℕ)) :
    valueKernel Q hQ s β N hN (i + k) (j + k) = valueKernel Q hQ s β N hN i j ∧
      halfKernel Q hQ s β N hN (i + k) (j + k) = halfKernel Q hQ s β N hN i j := by
  constructor
  · apply congrArg (lift Q hQ)
    apply ContinuousMap.ext
    intro u
    rcases eq_or_lt_of_le u.property.1 with hu | hu
    · simp only [valueEntry, coordinate, ContinuousMap.mul_apply, ContinuousMap.coe_mk, ← hu, zero_mul]
    · simp_rw [valueEntry_eq_spectralInverse s β N hN u hu]
      exact ReferenceOperatorKernel.spectralInverse_translate hz s β N hN _ i j k
  · apply congrArg (lift Q hQ)
    apply ContinuousMap.ext
    intro u
    rcases eq_or_lt_of_le u.property.1 with hu | hu
    · simp only [halfEntry, ContinuousMap.mul_apply, ContinuousMap.coe_mk, ← hu, Real.sqrt_zero, zero_mul]
    · simp_rw [halfEntry_eq_spectralInverse s β N hN u hu]
      exact congrArg (fun x => Real.sqrt ((1 - u.val) / u.val) * x)
        (ReferenceOperatorKernel.spectralInverse_translate hz s β N hN
          ⟨(1 - u.val) / u.val, div_nonneg (sub_nonneg.mpr u.property.2) hu.le⟩ i j k)

/-- A row gives the cyclic operator convolution kernels. -/
theorem convolution_entries (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (β : InverseTemperature) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (i h : Fin (N : ℕ)) :
    valueKernel Q hQ s β N hN i (i + h) = valueKernel Q hQ s β N hN 0 h ∧
      halfKernel Q hQ s β N hN i (i + h) = halfKernel Q hQ s β N hN 0 h := by
  simpa only [zero_add, add_comm h i] using kernel_translate Q hQ hz s β N hN 0 h i

/-- The real kernel solves the actual full-reference equation,
the proof of Proposition 5.15. No component projection is taken. -/
theorem referenceKernel_solves (s : Riesz1.RieszExponent) (β : InverseTemperature)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (i k : Fin (N : ℕ))
    (f : Lp ℝ 2 ν) (w : ScalarFormHilbert.Space Q hQ) :
    Q.2 (ScalarFormHilbert.equiv Q hQ
        (solutionKernel Q hQ _ (reference_posDef s β N hN) i k f))
      (ScalarFormHilbert.equiv Q hQ w) +
      ∑ j, (2 * β.val * referenceIntervalMatrix s N hN 1 i j) *
        inner ℝ (valueKernel Q hQ s β N hN j k f) (ScalarFormHilbert.value Q hQ w) =
      inner ℝ (if i = k then f else 0) (ScalarFormHilbert.value Q hQ w) := by
  have he := FiniteFormReferenceKernel.solutionKernel_solves Q hQ _
    (reference_posDef s β N hN) i k f w
  rw [← ReferenceOperatorKernel.reference_eq s N hN]
  simpa only [Matrix.smul_apply, smul_eq_mul, valueKernel] using he

/-- The bounded half kernel is precisely the whole-domain half-generator of
that reference solution, the proof of Proposition 5.15. -/
theorem referenceKernel_half (s : Riesz1.RieszExponent) (β : InverseTemperature)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (i j : Fin (N : ℕ)) (f : Lp ℝ 2 ν) :
    ScalarFormHalfGenerator.halfGenerator Q hQ
      (solutionKernel Q hQ _ (reference_posDef s β N hN) i j f) =
        halfKernel Q hQ s β N hN i j f :=
  FiniteFormReferenceKernel.solutionKernel_half Q hQ _ (reference_posDef s β N hN) i j f

/-- The kernel column solves the full-component weak equation,
the proof of Proposition 5.15. -/
theorem referenceKernel_weightedWeakSolution (s : Riesz1.RieszExponent) (β : InverseTemperature)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (k : Fin (N : ℕ)) (f : Lp ℝ 2 ν) :
    WeightedWeakSolution Q (fun _ => (2 * β.val) • referenceIntervalMatrix s N hN 1) ⊤
      (fun i => if i = k then f else 0)
      (fun i => ScalarFormHilbert.equiv Q hQ
        (solutionKernel Q hQ _ (reference_posDef s β N hN) i k f)) := by
  rw [← ReferenceOperatorKernel.reference_eq s N hN]
  exact FiniteFormReferenceKernel.solutionKernel_weightedWeakSolution Q hQ _
    (reference_posDef s β N hN) k f

/-- Finite kernel convolution gives the actual reference weak solution
for every L² source, the proof of Proposition 5.15. -/
theorem referenceInverse_weightedWeakSolution (s : Riesz1.RieszExponent) (β : InverseTemperature)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (f : Fin (N : ℕ) → Lp ℝ 2 ν) :
    WeightedWeakSolution Q (fun _ => (2 * β.val) • referenceIntervalMatrix s N hN 1) ⊤ f
      (fun i => ∑ k, ScalarFormHilbert.equiv Q hQ
        (solutionKernel Q hQ _ (reference_posDef s β N hN) i k (f k))) := by
  let A := (2 * β.val) • referenceIntervalMatrix s N hN 1
  have hMb : ∃ B : ℝ, ∀ᵐ _x ∂ν, ∀ i j, |A i j| ≤ B := by
    refine ⟨∑ i, ∑ j, |A i j|, Filter.Eventually.of_forall (fun _ i j => ?_)⟩
    exact (Finset.single_le_sum (fun j _ => abs_nonneg (A i j)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg (A i j)))
        (Finset.mem_univ i))
  have he := LocalizedBoundary.weak_sum_internal Q (fun _ => A) (fun _ _ => measurable_const) hMb
    (fun k i => if i = k then f k else 0)
    (fun k i => ScalarFormHilbert.equiv Q hQ
      (solutionKernel Q hQ _ (reference_posDef s β N hN) i k (f k)))
    (fun k => referenceKernel_weightedWeakSolution Q hQ s β N hN k (f k))
  have hsource : (fun i => ∑ k, if i = k then f k else 0) = f := by
    funext i
    simp
  simpa only [hsource, A] using he

/-- The values and half-generator of the finite form solution are finite
operator convolutions, as used in the proof of Proposition 5.15. -/
theorem referenceInverse_convolution (s : Riesz1.RieszExponent) (β : InverseTemperature)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (f : Fin (N : ℕ) → Lp ℝ 2 ν) (i : Fin (N : ℕ)) :
    ScalarFormHilbert.value Q hQ
      (∑ k, solutionKernel Q hQ _ (reference_posDef s β N hN) i k (f k)) =
        ∑ k, valueKernel Q hQ s β N hN i k (f k) ∧
    ScalarFormHalfGenerator.halfGenerator Q hQ
      (∑ k, solutionKernel Q hQ _ (reference_posDef s β N hN) i k (f k)) =
        ∑ k, halfKernel Q hQ s β N hN i k (f k) := by
  constructor
  · rw [map_sum]
    exact Finset.sum_congr rfl (fun k _ => solutionKernel_value Q hQ _ _ i k (f k))
  · rw [map_sum]
    exact Finset.sum_congr rfl (fun k _ => referenceKernel_half Q hQ s β N hN i k (f k))

/-- Half-generator-kernel decay on arbitrary real scalar forms,
the proof of Proposition 5.15, case `σ=1/2`. -/
theorem halfKernel_decay (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (β : InverseTemperature) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (Ω : Type u) [MeasurableSpace Ω] (ν : Measure Ω)
      (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q) (h : Fin (N : ℕ)),
      ‖halfKernel Q hQ s β N hN 0 h‖ ≤
        C * (1 + (Riesz1.cyclicIndexDistance N h 0 : ℝ)) ^ (-(1 + (1 - s.val) / 2)) := by
  obtain ⟨C, hC, hb⟩ := ReferenceOperatorKernel.spectralInverse_half_decay hz s β
  exact ⟨C, hC, fun N hN _ _ _ Q hQ h =>
    halfKernel_decay_internal Q hQ s β C hC.le hb N hN h⟩

/-- The operator kernel for the two exponents in the proof of Proposition 5.15. Its carrier contains exactly `0` and `1/2`. -/
def kernel (σ : {σ : ℝ // σ = 0 ∨ σ = 1 / 2}) (s : Riesz1.RieszExponent)
    (β : InverseTemperature) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (i j : Fin (N : ℕ)) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  if σ.val = 0 then valueKernel Q hQ s β N hN i j else halfKernel Q hQ s β N hN i j

/-- Complete operator bounds and whole-form-domain square-root identity of
the proof of Proposition 5.15. The kernels are identified with
the actual reference weak inverse by `referenceInverse_weightedWeakSolution`
and `referenceInverse_convolution`. Their cyclic convolution convention is
`convolution_entries`. The common constant precedes every measured scalar form. -/
theorem loc_reference_kernel (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (β : InverseTemperature) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (Ω : Type u) [MeasurableSpace Ω] (ν : Measure Ω)
      (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
      (σ : {σ : ℝ // σ = 0 ∨ σ = 1 / 2}),
      (∀ h : Fin (N : ℕ), ‖kernel Q hQ σ s β N hN 0 h‖ ≤
        C * (1 + (Riesz1.cyclicIndexDistance N h 0 : ℝ)) ^
          (-1 - (1 - σ.val) * (1 - s.val))) ∧
      ‖∑ h, kernel Q hQ σ s β N hN 0 h‖ ≤
        C * (N : ℝ) ^ (-(1 - σ.val) * (1 - s.val)) ∧
      (∀ v : Q.1, ‖ScalarFormHalfGenerator.halfGenerator Q hQ
          ((ScalarFormHilbert.equiv Q hQ).symm v)‖ = Real.sqrt (Q.2 v v)) := by
  obtain ⟨C₀, hC₀, h₀⟩ := valueKernel_decay hz s β
  obtain ⟨C₁, hC₁, h₁⟩ := halfKernel_decay hz s β
  obtain ⟨C₂, hC₂, h₂⟩ := kernel_mass_bounds s β
  let C := C₀ + C₁ + C₂
  have hc₀ : C₀ ≤ C := by dsimp [C]; linarith
  have hc₁ : C₁ ≤ C := by dsimp [C]; linarith
  have hc₂ : C₂ ≤ C := by dsimp [C]; linarith
  refine ⟨C, by dsimp [C]; positivity, fun N hN Ω _ ν Q hQ σ => ?_⟩
  refine ⟨?_, ?_, ScalarFormHalfGenerator.halfGenerator_norm Q hQ⟩
  · intro h
    rcases σ with ⟨σ, hσ⟩
    rcases hσ with rfl | rfl
    · simp only [kernel, ite_true]
      have he := (h₀ N hN Ω ν Q hQ h).trans
        (mul_le_mul_of_nonneg_right hc₀ (by positivity))
      convert he using 1
      congr 2
      ring
    · simp only [kernel, show (1 / 2 : ℝ) ≠ 0 by norm_num, ite_false]
      have he := (h₁ N hN Ω ν Q hQ h).trans
        (mul_le_mul_of_nonneg_right hc₁ (by positivity))
      convert he using 1
      congr 2
      ring
  · rcases σ with ⟨σ, hσ⟩
    rcases hσ with rfl | rfl
    · simp only [kernel, ite_true]
      have he := (h₂ N hN Ω ν Q hQ 0).1.trans
        (mul_le_mul_of_nonneg_right hc₂ (by positivity))
      convert he using 1
      congr 2
      ring
    · simp only [kernel, show (1 / 2 : ℝ) ≠ 0 by norm_num, ite_false]
      have he := (h₂ N hN Ω ν Q hQ 0).2.trans
        (mul_le_mul_of_nonneg_right hc₂ (by positivity))
      convert he using 1
      congr 2
      ring

/-- Strict positivity of the exact reference constant-mode eigenvalue. -/
theorem reference_mass_pos (s : Riesz1.RieszExponent) (β : InverseTemperature)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    0 < β.val * (2 * ∑ k, sampledRieszKernel s N hN k) := by
  obtain ⟨c, _, hc, _, hb⟩ := sampledRieszKernel_zero_mode_bounds s
  have hm : 0 < ∑ k, sampledRieszKernel s N hN k :=
    (mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)).trans_le (hb N hN).1
  exact mul_pos β.property (mul_pos two_pos hm)

/-- Exact operator-valued mass, with the full reference constant mode:
the value-kernel row sum is the scalar shifted resolvent.
See the proof of Proposition 5.15 in the paper. -/
theorem valueKernel_row_sum (s : Riesz1.RieszExponent) (β : InverseTemperature)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (i : Fin (N : ℕ)) :
    (∑ j, valueKernel Q hQ s β N hN i j) =
      ScalarFormResolvent.resolvent Q hQ (β.val * (2 * ∑ k, sampledRieszKernel s N hN k))
        (reference_mass_pos s β N hN) := by
  let ell := β.val * (2 * ∑ k, sampledRieszKernel s N hN k)
  have hell : 0 < ell := reference_mass_pos s β N hN
  let F : C(Set.Icc (0 : ℝ) 1, ℝ) :=
    ∑ j, valueEntry _ (reference_posDef s β N hN) i j
  let B : C(Set.Icc (0 : ℝ) 1, ℝ) := 1 + (ell - 1) • coordinate
  have hfun : B * F = coordinate := by
    apply ContinuousMap.ext
    intro u
    rcases eq_or_lt_of_le u.property.1 with hu | hu
    · simp only [B, F, ContinuousMap.mul_apply, ContinuousMap.add_apply, ContinuousMap.one_apply,
        ContinuousMap.smul_apply, ContinuousMap.sum_apply, valueEntry, coordinate,
        ContinuousMap.coe_mk, ← hu, smul_eq_mul, mul_zero, zero_mul, Finset.sum_const_zero]
    · simp only [B, F, ContinuousMap.mul_apply, ContinuousMap.add_apply, ContinuousMap.one_apply,
        ContinuousMap.smul_apply, ContinuousMap.sum_apply]
      simp_rw [valueEntry_eq_spectralInverse s β N hN u hu]
      let t : ℝ≥0 := ⟨(1 - u.val) / u.val, div_nonneg (sub_nonneg.mpr u.property.2) hu.le⟩
      change (1 + (ell - 1) * u.val) *
        (∑ j, ReferenceOperatorKernel.spectralInverse s β N hN t i j) = u.val
      rw [ReferenceOperatorKernel.spectralInverse_row_sum s β N hN t i]
      change (1 + (ell - 1) * u.val) * (ell + (1 - u.val) / u.val)⁻¹ = u.val
      have hd : 0 < ell + (1 - u.val) / u.val :=
        add_pos_of_pos_of_nonneg hell (div_nonneg (sub_nonneg.mpr u.property.2) hu.le)
      rw [← div_eq_mul_inv, div_eq_iff hd.ne']
      field_simp [hu.ne']
      ring
  have hmap : lift Q hQ B * lift Q hQ F = ScalarFormResolvent.resolvent Q hQ 1 zero_lt_one := by
    rw [← map_mul, hfun, lift_coordinate]
  have hB : lift Q hQ B = 1 + (ell - 1) • ScalarFormResolvent.resolvent Q hQ 1 zero_lt_one := by
    dsimp only [B]
    rw [map_add, map_one, map_smul, lift_coordinate]
  have hF : lift Q hQ F = ∑ j, valueKernel Q hQ s β N hN i j := by
    dsimp only [F]
    rw [map_sum]
    rfl
  rw [hB, hF] at hmap
  let V := 1 + (1 - ell) • ScalarFormResolvent.resolvent Q hQ ell hell
  have hv : V * (1 + (ell - 1) • ScalarFormResolvent.resolvent Q hQ 1 zero_lt_one) = 1 :=
    (ScalarFormResolvent.bounded_transform_inverse Q hQ ell hell).2
  have he := hmap.trans (ScalarFormResolvent.bounded_transform Q hQ ell hell).symm
  have hh := congrArg (fun A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν => V * A) he
  change (∑ j, valueKernel Q hQ s β N hN i j) = ScalarFormResolvent.resolvent Q hQ ell hell
  simpa only [← mul_assoc, hv, one_mul] using hh

/-- Exact half-generator mass: the row sum is the half-generator applied to
the same scalar shifted inverse. See the proof of Proposition 5.15 in the paper. -/
theorem halfKernel_row_sum (s : Riesz1.RieszExponent) (β : InverseTemperature)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (i : Fin (N : ℕ)) :
    (∑ j, halfKernel Q hQ s β N hN i j) =
      (ScalarFormHalfGenerator.halfGenerator Q hQ).comp
        (ScalarFormHilbert.shiftedSolution Q hQ (β.val * (2 * ∑ k, sampledRieszKernel s N hN k))
          (reference_mass_pos s β N hN)) := by
  apply ContinuousLinearMap.ext
  intro f
  have hu : (∑ j, solutionKernel Q hQ _ (reference_posDef s β N hN) i j f) =
      ScalarFormHilbert.shiftedSolution Q hQ (β.val * (2 * ∑ k, sampledRieszKernel s N hN k))
        (reference_mass_pos s β N hN) f := by
    apply ScalarFormHilbert.value_injective Q hQ
    rw [map_sum]
    simp_rw [solutionKernel_value]
    have he := congrArg (fun A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν => A f)
      (valueKernel_row_sum Q hQ s β N hN i)
    simpa only [sum_apply, valueKernel, ScalarFormResolvent.resolvent, ContinuousLinearMap.comp_apply] using he
  simp only [sum_apply, ContinuousLinearMap.comp_apply]
  calc
    _ = ∑ j, ScalarFormHalfGenerator.halfGenerator Q hQ
        (solutionKernel Q hQ _ (reference_posDef s β N hN) i j f) :=
      Finset.sum_congr rfl (fun j _ => (referenceKernel_half Q hQ s β N hN i j f).symm)
    _ = ScalarFormHalfGenerator.halfGenerator Q hQ
        (∑ j, solutionKernel Q hQ _ (reference_posDef s β N hN) i j f) := (map_sum _ _ _).symm
    _ = _ := congrArg (ScalarFormHalfGenerator.halfGenerator Q hQ) hu

end Riesz2.ReferenceOperatorKernelPart3
