/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.CoerciveSolutionMaps

/-!
# Arbitrary sources on the natural vector domain

See Subsection 3.5 of the paper. The component index and measured base
are independent. A fixed component subspace is imposed on the domain itself.

The dual equation is proved for every continuous functional on the natural
energy space, including restrictions of H⁻¹ sources. For L² sources the
equation is `WeightedWeakSolution`, with the two sharp norm estimates.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace Riesz2.AuxiliarySources

variable {α ι : Type*} [MeasurableSpace α] {ρ : Measure α}
  [Fintype ι] [DecidableEq ι]
  (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q)
  (M : α → Matrix ι ι ℝ) (S : Submodule ℝ (ι → ℝ))
  (hM : ∀ᵐ x ∂ρ, (M x).PosSemidef)
  (a : ℝ) (ha : 0 < a)
  (hlower : ∀ᵐ x ∂ρ, ∀ t ∈ S,
    a * (∑ i, t i ^ 2) ≤ ∑ i, ∑ j, t i * M x i j * t j)

open MatrixEnergy

include ha hlower in
/-- See Subsection 3.5 of the paper, dual-source existence and uniqueness on any fixed
component subspace. This holds for the full energy dual, and hence for H⁻¹ sources.
The displayed pairing is diffusion plus the actual matrix cross integral. -/
theorem natural_dual_sources (v : StrongDual ℝ (Natural Q hQ M S hM)) :
    ∃! u : Natural Q hQ M S hM, ∀ h : Natural Q hQ M S hM,
      (∑ i, Q.2 (tuple Q hQ M S hM u i) (tuple Q hQ M S hM h i)) +
        (∫ x, matrixFieldPair M (fun i => (tuple Q hQ M S hM u i).val)
          (fun i => (tuple Q hQ M S hM h i).val) x ∂ρ) = v h := by
  refine ⟨dualSolution Q hQ M S hM a ha hlower v, fun h => ?_, fun u hu => ?_⟩
  · rw [← weakForm_apply]
    exact dualSolution_solves Q hQ M S hM a ha hlower v h
  · apply dualSolution_unique Q hQ M S hM a ha hlower v u
    intro h
    rw [weakForm_apply]
    exact hu h

include ha hlower in
/-- See Subsection 3.5 of the paper, arbitrary H⁻¹ sources: a continuous functional
on the finite H¹ product restricts continuously to the natural energy domain.
The conclusion also applies to the intrinsic equation in an orthonormal affine chart.
Conservativity and a gradient realization are unnecessary for this variational result. -/
theorem hminusOne_sources (v : StrongDual ℝ (Vector (ι := ι) Q hQ)) :
    ∃! u : Natural Q hQ M S hM, ∀ h : Natural Q hQ M S hM,
      (∑ i, Q.2 (tuple Q hQ M S hM u i) (tuple Q hQ M S hM h i)) +
        (∫ x, matrixFieldPair M (fun i => (tuple Q hQ M S hM u i).val)
          (fun i => (tuple Q hQ M S hM h i).val) x ∂ρ) =
            v (base (κ := ι) (vectorValue (ι := ι) Q hQ)
              (fun x => CFC.sqrt (M x)) S h) :=
  natural_dual_sources Q hQ M S hM a ha hlower
    (v.comp (base (κ := ι) (vectorValue (ι := ι) Q hQ) (fun x => CFC.sqrt (M x)) S))

include hM ha hlower in
/-- See Subsection 3.5 of the paper, the H⁻¹ equation on tuples and every
finite-energy test. The source acts on the original H¹ product, not on a new
completion of smooth fields. Matrix cross terms are explicitly integrable. -/
theorem hminusOne_sources_frozen (hMmeas : ∀ i j, Measurable (fun x => M x i j))
    (v : StrongDual ℝ (Vector (ι := ι) Q hQ)) :
    ∃! u : ι → Q.1, WeightedFormDomain Q M S u ∧
      ∀ h : ι → Q.1, WeightedFormDomain Q M S h →
        Integrable (matrixFieldPair M (fun i => (u i).val) (fun i => (h i).val)) ρ ∧
        (∑ i, Q.2 (u i) (h i)) +
          (∫ x, matrixFieldPair M (fun i => (u i).val) (fun i => (h i).val) x ∂ρ) =
            v ((vectorEquiv Q hQ).symm h) := by
  let b := base (κ := ι) (vectorValue (ι := ι) Q hQ) (fun x => CFC.sqrt (M x)) S
  let f : StrongDual ℝ (Natural Q hQ M S hM) := v.comp b
  let z := dualSolution Q hQ M S hM a ha hlower f
  refine ⟨tuple Q hQ M S hM z, ⟨tuple_mem Q hQ M S hM z, ?_⟩, ?_⟩
  · intro h hh
    obtain ⟨w, rfl⟩ := exists_tuple Q hQ M S hM hMmeas h hh
    refine ⟨integrable_pair Q hQ M S hM z w, ?_⟩
    rw [← weakForm_apply]
    have he := dualSolution_solves Q hQ M S hM a ha hlower f w
    change weakForm Q hQ M S hM z w = v ((vectorEquiv Q hQ).symm
      (vectorEquiv Q hQ (WithLp.ofLp w.val).1))
    rw [LinearEquiv.symm_apply_apply]
    exact he
  · intro u hu
    obtain ⟨w, rfl⟩ := exists_tuple Q hQ M S hM hMmeas u hu.1
    apply congrArg (tuple Q hQ M S hM)
    apply dualSolution_unique Q hQ M S hM a ha hlower f w
    intro h
    have he := (hu.2 (tuple Q hQ M S hM h) (tuple_mem Q hQ M S hM h)).2
    rw [← weakForm_apply] at he
    change weakForm Q hQ M S hM w h = v ((vectorEquiv Q hQ).symm
      (vectorEquiv Q hQ (WithLp.ofLp h.val).1)) at he
    rw [LinearEquiv.symm_apply_apply] at he
    exact he

include hQ hM ha hlower in
/-- See Subsection 3.5 of the paper, L² sources, including both sharp estimates.
Uniqueness is equality of tuples in the scalar domain. Every finite-energy
test is included, and matrix cross-integrability is part of the predicate.
Taking `S = ⊤` gives the unrestricted equation. -/
theorem l2_sources (hMmeas : ∀ i j, Measurable (fun x => M x i j))
    (v : ι → Lp ℝ 2 ρ) :
    ∃ u : ι → Q.1,
      WeightedWeakSolution Q M S v u ∧
      (∀ w : ι → Q.1, WeightedWeakSolution Q M S v w → w = u) ∧
      ‖WithLp.toLp 2 (fun i => (u i).val)‖ ≤ a⁻¹ * ‖WithLp.toLp 2 v‖ ∧
      Real.sqrt (∑ i, Q.2 (u i) (u i)) ≤ (Real.sqrt a)⁻¹ * ‖WithLp.toLp 2 v‖ := by
  let z := solution Q hQ M S hM a ha hlower (WithLp.toLp 2 v)
  refine ⟨tuple Q hQ M S hM z,
    solution_weightedWeakSolution Q hQ M S hM a ha hlower hMmeas v,
    fun w hw => weightedWeakSolution_unique Q hQ M S hM a ha hlower hMmeas v w hw,
    ?_, solution_gradient_le Q hQ M S hM a ha hlower (WithLp.toLp 2 v)⟩
  exact solution_value_norm_le Q hQ M S hM a ha hlower (WithLp.toLp 2 v)

include hQ hM ha hlower in
/-- See Subsection 3.5 of the paper, all conclusions: arbitrary H⁻¹ sources have
unique solutions on the full natural domain. L² sources satisfy both sharp
bounds. The fixed subspace is arbitrary and the index type is independent of the
measured base. Conservativity is unnecessary for this variational result. -/
theorem arbitrary_sources (hMmeas : ∀ i j, Measurable (fun x => M x i j)) :
    (∀ v : StrongDual ℝ (Vector (ι := ι) Q hQ),
      ∃! u : ι → Q.1, WeightedFormDomain Q M S u ∧
        ∀ h : ι → Q.1, WeightedFormDomain Q M S h →
          Integrable (matrixFieldPair M (fun i => (u i).val) (fun i => (h i).val)) ρ ∧
          (∑ i, Q.2 (u i) (h i)) +
            (∫ x, matrixFieldPair M (fun i => (u i).val) (fun i => (h i).val) x ∂ρ) =
              v ((vectorEquiv Q hQ).symm h)) ∧
    (∀ v : ι → Lp ℝ 2 ρ, ∃ u : ι → Q.1,
      WeightedWeakSolution Q M S v u ∧
      (∀ w : ι → Q.1, WeightedWeakSolution Q M S v w → w = u) ∧
      ‖WithLp.toLp 2 (fun i => (u i).val)‖ ≤ a⁻¹ * ‖WithLp.toLp 2 v‖ ∧
      Real.sqrt (∑ i, Q.2 (u i) (u i)) ≤ (Real.sqrt a)⁻¹ * ‖WithLp.toLp 2 v‖) :=
  ⟨hminusOne_sources_frozen Q hQ M S hM a ha hlower hMmeas,
    l2_sources Q hQ M S hM a ha hlower hMmeas⟩

end Riesz2.AuxiliarySources
