/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.MaximumPrincipleChainRule

/-!
# Maximum principle through the Neumann weak chain rule

For bounded Euclidean Neumann realizations, the radial test and its diffusion
sign come from the local weak differential, including locality on the cutoff
sphere. The residual argument is shared with the general closed-form theorem.
This follows Proposition 3.6 of the paper for the gradient
realizations used in Section 3 and the physical applications.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2.MaximumPrinciple

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
  {ρ : Measure E} [IsFiniteMeasure ρ] {Ω : Set E}

/-- The form-domain chain rule assumed in Proposition 3.6
and Assumptions 4.1 of the paper, for the bounded Neumann realization.
The differential is the unique gradient from the scalar graph. The existing
Neumann admissible-truncation theorem supplies domain membership. The Sobolev
chain rule identifies its gradient, including on the cutoff sphere. -/
theorem hasRadialChainRule_neumann
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hρ : ∀ᵐ x ∂ρ, x ∈ Ω)
    (Q : ScalarFormData ρ) (hQ : IsNeumannRealization Ω Q) :
    HasVectorRadialChainRule (ι := ι) (G := E) Q := by
  classical
  have hex (f : Q.1) : ∃ g : Lp E 2 ρ, (f.val, g) ∈ neumannSobolevGraph ρ Ω :=
    (hQ.1 f.val).mp f.property
  let D : Q.1 → Lp E 2 ρ := fun f => (hex f).choose
  have hD (f : Q.1) : (f.val, D f) ∈ neumannSobolevGraph ρ Ω := (hex f).choose_spec
  refine ⟨D, fun f g => hQ.2.2 f g (D f) (D g) (hD f) (hD g), ?_⟩
  intro R u
  -- The zero matrix imposes no additional energy-domain condition on H¹.
  have hzero : WeightedFormDomain Q (fun _ => (0 : Matrix ι ι ℝ)) ⊤ u := by
    refine ⟨ae_of_all _ fun _ => Submodule.mem_top, ?_⟩
    change Integrable (fun x : E => ∑ i, ∑ j, (u i).val x * (0 : ℝ) * (u j).val x) ρ
    simpa only [mul_zero, zero_mul, Finset.sum_const_zero] using (integrable_const (μ := ρ) (0 : ℝ))
  obtain ⟨h, hh, _, _, _⟩ := VectorRadial.admissible_truncation_neumann
    hΩ hb hρ Q hQ (fun _ => (0 : Matrix ι ι ℝ)) ⊤
    (fun _ _ => measurable_const) (ae_of_all _ fun _ => Matrix.PosSemidef.zero) R u hzero
  refine ⟨h, hh, fun i => ?_⟩
  have hFG (j : ι) : Riesz1.WeightedSobolev.IsWeightedH1 ρ Ω (u j).val (D (u j)) := by
    apply (VectorRadial.isWeightedH1_iff_neumannSobolevGraph hb hρ
      (Lp.memLp _) (Lp.memLp _)).mpr
    simpa only [Lp.toLp_coeFn] using hD (u j)
  let W : E → E := fun x => VectorRadial.weakDifferential R
    (WithLp.toLp 2 (fun j => (u j).val x)) (fun j => D (u j) x) i
  have ht := VectorRadial.sobolev_truncate hΩ hb hρ Q hQ hFG R i
  have hjet : (VectorRadial.truncateValues R (fun j => (u j).val) i,
      ht.2.1.toLp W) ∈ neumannSobolevGraph ρ Ω :=
    (VectorRadial.isWeightedH1_iff_neumannSobolevGraph hb hρ
      ht.1 ht.2.1).mp ht
  rw [← hh i] at hjet
  have he := hQ.2.1 (h i).val (D (h i)) (ht.2.1.toLp W) (hD (h i)) hjet
  rw [he]
  exact ht.2.1.coeFn_toLp

end Riesz2.MaximumPrinciple

namespace Riesz2

/-- Proposition 3.6 and equation (3.13) of the paper, for a
bounded open Euclidean Neumann realization, on any fixed component subspace.
The proof tests with the weak radial truncation, uses the displayed local
chain-rule sign, and forces the nonnegative residual integral to vanish.
The essential-supremum estimate also covers unbounded sources. -/
theorem maximumPrinciple_neumann
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
    {ρ : Measure E} [IsProbabilityMeasure ρ] {Ω : Set E}
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hρ : ∀ᵐ x ∂ρ, x ∈ Ω)
    (Q : ScalarFormData ρ) (hQ : IsNeumannRealization Ω Q)
    (M : E → Matrix ι ι ℝ) (hMmeas : ∀ i j, Measurable (fun x => M x i j))
    (c : ℝ) (hc : 0 < c)
    (hM : ∀ᵐ x ∂ρ, (∀ i j, M x i j = M x j i) ∧
      ∀ z : ι → ℝ, c * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j)
    (S : Submodule ℝ (ι → ℝ)) (v : ι → Lp ℝ 2 ρ) (u : ι → Q.1)
    (hu : WeightedWeakSolution Q M S v u) :
    eLpNorm (fun x => WithLp.toLp 2 (fun i => (u i).val x)) ∞ ρ ≤
      ENNReal.ofReal c⁻¹ * eLpNorm (fun x => WithLp.toLp 2 (fun i => v i x)) ∞ ρ := by
  exact maximumPrinciple_radialChainRule_subspace Q
    (MaximumPrinciple.hasRadialChainRule_neumann hΩ hb hρ Q hQ)
    M hMmeas c hc hM S v u hu

end Riesz2
