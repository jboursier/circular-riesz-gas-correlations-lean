/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.SchurRestriction

/-!
# Perturbation on a natural matrix-energy domain

The first matrix may be unbounded. An L² realization of its discrepancy
on a bounded-matrix solution proves that this solution belongs to the
first natural energy domain. Both equations use the same scalar form
and the same fixed component subspace.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators

namespace Riesz2.NaturalMatrixPerturbation

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι]
  {ρ : Measure α}

omit [DecidableEq ι] in
/-- Internal pairing identity supporting Proposition 4.10.
The residual is an actual L² matrix action, rather than an estimate assumed
of the physical equation. -/
theorem internal_pair_difference
    (H M : α → Matrix ι ι ℝ)
    (hH : ∀ᵐ x ∂ρ, ∀ i j, H x i j = H x j i)
    (hM : ∀ᵐ x ∂ρ, ∀ i j, M x i j = M x j i)
    (v w g : ι → Lp ℝ 2 ρ)
    (hg : ∀ᵐ x ∂ρ, ∀ i, g i x = ∑ j, (H x i j - M x i j) * v j x) :
    matrixFieldPair H v w =ᵐ[ρ]
      fun x => matrixFieldPair M v w x + ∑ i, g i x * w i x := by
  filter_upwards [hH,hM,hg] with x hHx hMx hx
  simp only [matrixFieldPair]
  calc
    _ = ∑ i, ∑ j, (v i x * M x i j * w j x +
        v i x * (H x i j-M x i j) * w j x) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (∑ i, ∑ j, v i x * M x i j * w j x) +
        ∑ i, ∑ j, v i x * (H x i j-M x i j) * w j x := by
      simp only [Finset.sum_add_distrib]
    _ = _ := by
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [hx i,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [hHx j i,hMx j i]
      ring

omit [DecidableEq ι] in
/-- Internal domain inclusion for Proposition 4.10.
An L² discrepancy proves finite physical energy directly. In particular,
no projection into an unbounded matrix domain is required. -/
theorem internal_domain_of_residual
    (Q : ScalarFormData ρ) (H M : α → Matrix ι ι ℝ)
    (hH : ∀ᵐ x ∂ρ, ∀ i j, H x i j = H x j i)
    (hM : ∀ᵐ x ∂ρ, ∀ i j, M x i j = M x j i)
    (S : Submodule ℝ (ι → ℝ)) (v : ι → Q.1)
    (hv : WeightedFormDomain Q M S v) (g : ι → Lp ℝ 2 ρ)
    (hg : ∀ᵐ x ∂ρ, ∀ i, g i x = ∑ j, (H x i j - M x i j) * (v j).val x) :
    WeightedFormDomain Q H S v := by
  refine ⟨hv.1,?_⟩
  have hi : Integrable (fun x => ∑ i, g i x * (v i).val x) ρ :=
    integrable_finsetSum _ fun i _ => (Lp.memLp _).integrable_mul (Lp.memLp _)
  exact (hv.2.add hi).congr
    (internal_pair_difference H M hH hM (fun i => (v i).val)
      (fun i => (v i).val) g hg).symm

/-- Internal transfer of a bounded-coefficient equation to the physical
natural domain, supporting Proposition 4.10. The first
matrix is allowed to be unbounded and the component constraint arbitrary. -/
theorem internal_shifted_equation
    (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q)
    (H M : α → Matrix ι ι ℝ)
    (hHm : ∀ i j, Measurable (fun x => H x i j))
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hHb : ∀ᵐ x ∂ρ, (H x).PosSemidef)
    (hMb : ∃ B : ℝ, ∀ᵐ x ∂ρ, ∀ i j, |M x i j| ≤ B)
    (hMs : ∀ᵐ x ∂ρ, ∀ i j, M x i j = M x j i)
    (S : Submodule ℝ (ι → ℝ)) (f g : ι → Lp ℝ 2 ρ) (v : ι → Q.1)
    (hv : WeightedWeakSolution Q M S f v)
    (hg : ∀ᵐ x ∂ρ, ∀ i, g i x = ∑ j, (H x i j - M x i j) * (v j).val x) :
    WeightedWeakSolution Q H S (f + g) v := by
  have hHs : ∀ᵐ x ∂ρ, ∀ i j, H x i j = H x j i := by
    filter_upwards [hHb] with x hx i j
    simpa using congrFun (congrFun hx.1 j) i
  have hvH := internal_domain_of_residual Q H M hHs hMs S v hv.1 g hg
  refine ⟨hvH,fun w hw => ?_⟩
  have hwM : WeightedFormDomain Q M S w :=
    ⟨hw.1,BoundedMatrixForms.integrable_pair M hMm hMb
      (fun i => (w i).val) (fun i => (w i).val)⟩
  obtain ⟨z,hz⟩ := MatrixEnergy.exists_tuple Q hQ H S hHb hHm v hvH
  obtain ⟨t,ht⟩ := MatrixEnergy.exists_tuple Q hQ H S hHb hHm w hw
  have hiH : Integrable (matrixFieldPair H (fun i => (v i).val)
      (fun i => (w i).val)) ρ := by
    rw [← hz,← ht]
    exact MatrixEnergy.integrable_pair Q hQ H S hHb z t
  obtain ⟨hiM,he⟩ := hv.2 w hwM
  have hi : Integrable (fun x => ∑ i, g i x * (w i).val x) ρ :=
    integrable_finsetSum _ fun i _ => (Lp.memLp _).integrable_mul (Lp.memLp _)
  have hpair : (∫ x, matrixFieldPair H (fun i => (v i).val)
      (fun i => (w i).val) x ∂ρ) =
      (∫ x, matrixFieldPair M (fun i => (v i).val) (fun i => (w i).val) x ∂ρ) +
        ∑ i, inner ℝ (g i) (w i).val := by
    rw [integral_congr_ae (internal_pair_difference H M hHs hMs
      (fun i => (v i).val) (fun i => (w i).val) g hg),integral_add hiM hi,
      integral_finsetSum _ (fun i _ => (Lp.memLp _).integrable_mul (Lp.memLp _))]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simpa only [Real.inner_apply] using (L2.inner_def (𝕜 := ℝ) (g i) (w i).val).symm
  refine ⟨hiH,?_⟩
  simp only [Pi.add_apply,inner_add_left,Finset.sum_add_distrib]
  rw [hpair,← add_assoc,he]

/-- Internal physical-versus-auxiliary comparison for Proposition 4.10. The physical matrix may be unbounded. The residual
identity proves the required domain inclusion. The sharp L² and diffusion
bounds hold on every fixed component subspace. -/
theorem internal_comparison
    (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q)
    (H M : α → Matrix ι ι ℝ)
    (hHm : ∀ i j, Measurable (fun x => H x i j))
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hHb : ∀ᵐ x ∂ρ, (H x).PosSemidef)
    (hMb : ∃ B : ℝ, ∀ᵐ x ∂ρ, ∀ i j, |M x i j| ≤ B)
    (hMs : ∀ᵐ x ∂ρ, ∀ i j, M x i j = M x j i)
    (S : Submodule ℝ (ι → ℝ)) (a : ℝ) (ha : 0 < a)
    (hlower : ∀ᵐ x ∂ρ, ∀ t ∈ S,
      a * (∑ i, t i ^ 2) ≤ ∑ i, ∑ j, t i * H x i j * t j)
    (f g : ι → Lp ℝ 2 ρ) (u v : ι → Q.1)
    (hu : WeightedWeakSolution Q H S f u)
    (hv : WeightedWeakSolution Q M S f v)
    (hg : ∀ᵐ x ∂ρ, ∀ i, g i x = ∑ j, (H x i j - M x i j) * (v j).val x) :
    ‖WithLp.toLp 2 (fun i => (u i - v i).val)‖ ≤ a⁻¹ * ‖WithLp.toLp 2 g‖ ∧
      Real.sqrt (∑ i, Q.2 (u i-v i) (u i-v i)) ≤
        (Real.sqrt a)⁻¹ * ‖WithLp.toLp 2 g‖ := by
  have hv' := internal_shifted_equation Q hQ H M hHm hMm hHb hMb hMs S f g v hv hg
  have hu' := MatrixEnergy.weightedWeakSolution_unique Q hQ H S hHb a ha hlower hHm f u hu
  have hv'' := MatrixEnergy.weightedWeakSolution_unique Q hQ H S hHb a ha hlower hHm (f+g) v hv'
  let T := MatrixEnergy.solution Q hQ H S hHb a ha hlower
  let z := T (-WithLp.toLp 2 g)
  have hd : MatrixEnergy.tuple Q hQ H S hHb z = fun i => u i-v i := by
    rw [hu',hv'']
    have he : z = T (WithLp.toLp 2 f) - T (WithLp.toLp 2 (f+g)) := by
      dsimp only [z]
      rw [← map_sub]
      congr 1
      apply PiLp.ext
      intro i
      change -(g i) = f i - (f i+g i)
      abel
    rw [he,map_sub]
    rfl
  have hval : MatrixEnergy.values Q hQ H S hHb z =
      WithLp.toLp 2 (fun i => (u i-v i).val) := by
    apply PiLp.ext
    intro i
    rw [MatrixEnergy.values_apply,hd]
  have hn := MatrixEnergy.solution_value_norm_le Q hQ H S hHb a ha hlower (-WithLp.toLp 2 g)
  have he := MatrixEnergy.solution_gradient_le Q hQ H S hHb a ha hlower (-WithLp.toLp 2 g)
  change ‖MatrixEnergy.values Q hQ H S hHb z‖ ≤ _ at hn
  change Real.sqrt (∑ i, Q.2 (MatrixEnergy.tuple Q hQ H S hHb z i)
    (MatrixEnergy.tuple Q hQ H S hHb z i)) ≤ _ at he
  rw [hval,norm_neg] at hn
  rw [hd,norm_neg] at he
  exact ⟨hn,he⟩

end Riesz2.NaturalMatrixPerturbation
