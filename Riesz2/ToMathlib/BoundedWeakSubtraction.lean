/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.NaturalMatrixPerturbation

/-!
# Subtraction of bounded matrix weak equations

All equations use the same scalar form domain. The discrepancy is an actual
L² matrix product, specified by its almost-everywhere representative.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter
open scoped BigOperators

namespace Riesz2.BoundedWeakSubtraction

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {ν : Measure Ω}

/-- Subtract two unrestricted equations with the same bounded matrix. -/
theorem weak_sub (Q : ScalarFormData ν) (M : Ω → Matrix ι ι ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hMb : ∃ B : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ B)
    (f g : ι → Lp ℝ 2 ν) (u v : ι → Q.1)
    (hu : WeightedWeakSolution Q M ⊤ f u)
    (hv : WeightedWeakSolution Q M ⊤ g v) :
    WeightedWeakSolution Q M ⊤ (fun i => f i - g i) (fun i => u i - v i) := by
  refine ⟨(BoundedMatrixForms.domain_iff Q M hMm hMb ⊤ _).mpr
    (Eventually.of_forall fun _ => Submodule.mem_top), ?_⟩
  intro w hw
  obtain ⟨hiu, heu⟩ := hu.2 w hw
  obtain ⟨hiv, hev⟩ := hv.2 w hw
  have hp : matrixFieldPair M (fun i => (u i - v i).val) (fun i => (w i).val) =ᵐ[ν]
      fun x => matrixFieldPair M (fun i => (u i).val) (fun i => (w i).val) x -
        matrixFieldPair M (fun i => (v i).val) (fun i => (w i).val) x := by
    filter_upwards [ae_all_iff.mpr (fun i => Lp.coeFn_sub (u i).val (v i).val)] with x hx
    simp only [Submodule.coe_sub, hx, Pi.sub_apply, matrixFieldPair, sub_mul, Finset.sum_sub_distrib]
  refine ⟨BoundedMatrixForms.integrable_pair M hMm hMb _ _, ?_⟩
  rw [integral_congr_ae hp, integral_sub hiu hiv]
  simp only [map_sub, LinearMap.sub_apply, inner_sub_left, Finset.sum_sub_distrib]
  linarith

/-- Changing the bounded symmetric matrix changes only the L² source.
The sign is chosen so `g = (H - M)v` gives source `f - g` for matrix `M`. -/
theorem weak_change_matrix (Q : ScalarFormData ν)
    (M H : Ω → Matrix ι ι ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hHm : ∀ i j, Measurable (fun x => H x i j))
    (hMb : ∃ B : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ B)
    (hHb : ∃ B : ℝ, ∀ᵐ x ∂ν, ∀ i j, |H x i j| ≤ B)
    (hMs : ∀ᵐ x ∂ν, ∀ i j, M x i j = M x j i)
    (hHs : ∀ᵐ x ∂ν, ∀ i j, H x i j = H x j i)
    (f g : ι → Lp ℝ 2 ν) (v : ι → Q.1)
    (hv : WeightedWeakSolution Q H ⊤ f v)
    (hg : ∀ᵐ x ∂ν, ∀ i, g i x = ∑ j, (H x i j - M x i j) * (v j).val x) :
    WeightedWeakSolution Q M ⊤ (fun i => f i - g i) v := by
  refine ⟨(BoundedMatrixForms.domain_iff Q M hMm hMb ⊤ _).mpr
    (Eventually.of_forall fun _ => Submodule.mem_top), ?_⟩
  intro w hw
  have hwH := (BoundedMatrixForms.domain_iff Q H hHm hHb ⊤ w).mpr hw.1
  obtain ⟨hiH, he⟩ := hv.2 w hwH
  have hiM := BoundedMatrixForms.integrable_pair M hMm hMb
    (fun i => (v i).val) (fun i => (w i).val)
  have hig : Integrable (fun x => ∑ i, g i x * (w i).val x) ν :=
    integrable_finsetSum _ fun i _ => (Lp.memLp _).integrable_mul (Lp.memLp _)
  have hp := integral_congr_ae
    (NaturalMatrixPerturbation.internal_pair_difference H M hHs hMs
      (fun i => (v i).val) (fun i => (w i).val) g hg)
  rw [integral_add hiM hig,
    integral_finsetSum _ (fun i _ => (Lp.memLp _).integrable_mul (Lp.memLp _))] at hp
  have hinner (i : ι) : (∫ x, g i x * (w i).val x ∂ν) = inner ℝ (g i) (w i).val := by
    rw [L2.inner_def]
    simp only [Real.inner_apply]
  simp_rw [hinner] at hp
  refine ⟨hiM, ?_⟩
  simp only [inner_sub_left, Finset.sum_sub_distrib]
  linarith

/-- Exact comparison equation for `e = ψ - z - φ`, over one scalar form.
This is the subtraction step in the proof of Proposition 5.15. -/
theorem comparison_equation (Q : ScalarFormData ν)
    (M H : Ω → Matrix ι ι ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hHm : ∀ i j, Measurable (fun x => H x i j))
    (hMb : ∃ B : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ B)
    (hHb : ∃ B : ℝ, ∀ᵐ x ∂ν, ∀ i j, |H x i j| ≤ B)
    (hMs : ∀ᵐ x ∂ν, ∀ i j, M x i j = M x j i)
    (hHs : ∀ᵐ x ∂ν, ∀ i j, H x i j = H x j i)
    (f b g : ι → Lp ℝ 2 ν) (ψ z φ : ι → Q.1)
    (hψ : WeightedWeakSolution Q M ⊤ (fun i => f i + b i) ψ)
    (hz : WeightedWeakSolution Q M ⊤ b z)
    (hφ : WeightedWeakSolution Q H ⊤ f φ)
    (hg : ∀ᵐ x ∂ν, ∀ i, g i x = ∑ j, (H x i j - M x i j) * (φ j).val x) :
    WeightedWeakSolution Q M ⊤ g (fun i => ψ i - z i - φ i) := by
  have hu := weak_sub Q M hMm hMb _ _ ψ z hψ hz
  have hv := weak_change_matrix Q M H hMm hHm hMb hHb hMs hHs f g φ hφ hg
  have he := weak_sub Q M hMm hMb _ _ _ φ hu hv
  simpa only [add_sub_cancel_right, sub_sub_cancel] using he

end Riesz2.BoundedWeakSubtraction
