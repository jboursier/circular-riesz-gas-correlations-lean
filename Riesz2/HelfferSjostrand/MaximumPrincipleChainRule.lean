/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.MaximumPrinciple

/-!
# The maximum principle with the paper's chain-rule hypothesis

Proposition 3.6 of the paper assumes a radial chain rule on
H¹. The property below records the weak differential itself on the entire
form domain. Admissibility in the matrix-energy domain and the diffusion
sign are consequences, proved before testing the equation.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The form-domain chain rule assumed in Proposition 3.6
and Assumptions 4.1 of the paper. The real inner-product space `G` is the gradient's
codomain. A single differential realizes the scalar form on its whole domain. For every vector field and radius, the radial excess lies in that domain
and its differential is the Lipschitz radial differential, including sphere
locality. No weak equation, matrix, diffusion sign or supremum bound is part
of this property. -/
def HasVectorRadialChainRule {α ι G : Type*} [MeasurableSpace α] [Fintype ι]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    {ρ : Measure α} (Q : ScalarFormData ρ) : Prop :=
  ∃ D : Q.1 → Lp G 2 ρ,
    (∀ f g : Q.1, Q.2 f g = inner ℝ (D f) (D g)) ∧
    ∀ (R : ℝ≥0) (u : ι → Q.1), ∃ h : ι → Q.1,
      (∀ i, (h i).val = VectorRadial.truncateValues R (fun j => (u j).val) i) ∧
      ∀ i, ∀ᵐ x ∂ρ, D (h i) x = VectorRadial.weakDifferential R
        (WithLp.toLp 2 (fun j => (u j).val x)) (fun j => D (u j) x) i

/-- The dimension-independent form-domain hypothesis in
Proposition 3.6 and Assumptions 4.1 of the paper: the radial
chain rule holds for every finite number of components, before a matrix or
weak equation is chosen. -/
def HasRadialChainRule {α G : Type*} [MeasurableSpace α]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    {ρ : Measure α} (Q : ScalarFormData ρ) : Prop :=
  ∀ m : ℕ, HasVectorRadialChainRule (ι := Fin m) (G := G) Q

namespace MaximumPrinciple

/-- The chain rule in Proposition 3.6 implies the displayed
nonnegative Dirichlet term. This is a consequence of the derivative formula,
not an assumed sign for the solution of an equation. -/
theorem Internal.truncation_of_chainRule {α ι G : Type*}
    [MeasurableSpace α] [Fintype ι]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    {ρ : Measure α} (Q : ScalarFormData ρ)
    (hchain : HasVectorRadialChainRule (ι := ι) (G := G) Q)
    (R : ℝ≥0) (u : ι → Q.1) :
    ∃ h : ι → Q.1,
      (∀ i, (h i).val = VectorRadial.truncateValues R (fun j => (u j).val) i) ∧
      0 ≤ ∑ i, Q.2 (u i) (h i) := by
  classical
  obtain ⟨D, hD, hchain⟩ := hchain
  obtain ⟨h, hh, hd⟩ := hchain R u
  refine ⟨h, hh, ?_⟩
  simp only [hD, L2.inner_def]
  rw [← integral_finsetSum _ (fun i _ => L2.integrable_inner (𝕜 := ℝ) (D (u i)) (D (h i)))]
  apply integral_nonneg_of_ae
  filter_upwards [ae_all_iff.mpr hd] with x hx
  simp only [hx]
  exact VectorRadial.sum_inner_weakDifferential_nonneg R _ _

/-- The finite-radius step of Proposition 3.6 using its
form-domain chain rule. Radial multiplication preserves the fixed component
subspace and decreases the nonnegative matrix energy, so the test is legal
even for an unbounded matrix field. -/
theorem Internal.bound_of_source_bound_chainRule {α ι G : Type*}
    [MeasurableSpace α] [Fintype ι]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    {ρ : Measure α} (Q : ScalarFormData ρ)
    (hchain : HasVectorRadialChainRule (ι := ι) (G := G) Q)
    (M : α → Matrix ι ι ℝ) (hMmeas : ∀ i j, Measurable (fun x => M x i j))
    (c : ℝ) (hc : 0 < c)
    (hM : ∀ᵐ x ∂ρ, (∀ i j, M x i j = M x j i) ∧
      ∀ z : ι → ℝ, c * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j)
    (S : Submodule ℝ (ι → ℝ)) (v : ι → Lp ℝ 2 ρ) (u : ι → Q.1)
    (hu : WeightedWeakSolution Q M S v u) (R : ℝ≥0)
    (hv : ∀ᵐ x ∂ρ,
      ‖(WithLp.toLp 2 (fun i => v i x) : EuclideanSpace ℝ ι)‖ ≤ c * R) :
    ∀ᵐ x ∂ρ, ‖(WithLp.toLp 2 (fun i => (u i).val x) :
      EuclideanSpace ℝ ι)‖ ≤ R := by
  classical
  have hpsd : ∀ᵐ x ∂ρ, (M x).PosSemidef := by
    filter_upwards [hM] with x hx
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    refine ⟨?_, fun z => ?_⟩
    · ext i j
      exact hx.1 j i
    · have hp : 0 ≤ c * ∑ i, z i ^ 2 :=
        mul_nonneg hc.le (Finset.sum_nonneg (fun i _ => sq_nonneg _))
      simpa only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum, mul_assoc]
        using hp.trans (hx.2 z)
  obtain ⟨h, hh, hpos⟩ := Internal.truncation_of_chainRule Q hchain R u
  have hdom := VectorRadial.Internal.weightedFormDomain_of_truncateValues
    R Q M S hMmeas hpsd u h hu.1 hh
  exact Internal.bound_of_admissible_radial_test Q M c hc hM S v u hu R hv
    h hh hdom hpos

end MaximumPrinciple

/-- The proof of Proposition 3.6 on a fixed component
subspace, with the paper's form-domain radial chain rule. Closedness
and probability are unnecessary for this internal extension once the weak
solution and differential have been supplied. -/
theorem maximumPrinciple_radialChainRule_subspace {α ι G : Type*}
    [MeasurableSpace α] [Fintype ι]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    {ρ : Measure α} (Q : ScalarFormData ρ)
    (hchain : HasVectorRadialChainRule (ι := ι) (G := G) Q)
    (M : α → Matrix ι ι ℝ) (hMmeas : ∀ i j, Measurable (fun x => M x i j))
    (c : ℝ) (hc : 0 < c)
    (hM : ∀ᵐ x ∂ρ, (∀ i j, M x i j = M x j i) ∧
      ∀ z : ι → ℝ, c * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j)
    (S : Submodule ℝ (ι → ℝ)) (v : ι → Lp ℝ 2 ρ) (u : ι → Q.1)
    (hu : WeightedWeakSolution Q M S v u) :
    eLpNorm (fun x => WithLp.toLp 2 (fun i => (u i).val x)) ∞ ρ ≤
      ENNReal.ofReal c⁻¹ * eLpNorm (fun x => WithLp.toLp 2 (fun i => v i x)) ∞ ρ := by
  let V := fun x => (WithLp.toLp 2 (fun i => v i x) : EuclideanSpace ℝ ι)
  let U := fun x => (WithLp.toLp 2 (fun i => (u i).val x) : EuclideanSpace ℝ ι)
  have hVm : AEStronglyMeasurable V ρ := (VectorRadial.memLp_values v).aestronglyMeasurable
  have hUm : AEStronglyMeasurable U ρ :=
    (VectorRadial.memLp_values (fun i => (u i).val)).aestronglyMeasurable
  change eLpNorm U ∞ ρ ≤ ENNReal.ofReal c⁻¹ * eLpNorm V ∞ ρ
  by_cases htop : eLpNorm V ∞ ρ = ⊤
  · rw [htop, ENNReal.mul_top (by positivity)]
    exact le_top
  let B : ℝ := (eLpNorm V ∞ ρ).toReal
  let R : ℝ≥0 := ⟨c⁻¹ * B, mul_nonneg (inv_nonneg.mpr hc.le) ENNReal.toReal_nonneg⟩
  have hv : ∀ᵐ x ∂ρ, ‖V x‖ ≤ B := by
    have h := ae_le_eLpNormEssSup (f := V) (μ := ρ)
    rw [← eLpNorm_exponent_top hVm] at h
    filter_upwards [h] with x hx
    have ht := ENNReal.toReal_mono htop hx
    simpa only [enorm_eq_nnnorm, ENNReal.coe_toReal, coe_nnnorm, B] using ht
  have hvR : ∀ᵐ x ∂ρ, ‖V x‖ ≤ c * R := by
    have he : c * (R : ℝ) = B := by
      change c * (c⁻¹ * B) = B
      rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    simpa only [he] using hv
  have huR := MaximumPrinciple.Internal.bound_of_source_bound_chainRule
    Q hchain M hMmeas c hc hM S v u hu R hvR
  calc
    eLpNorm U ∞ ρ = eLpNormEssSup U ρ := eLpNorm_exponent_top hUm
    _ ≤ ENNReal.ofReal R := eLpNormEssSup_le_of_ae_bound huR
    _ = ENNReal.ofReal c⁻¹ * eLpNorm V ∞ ρ := by
      change ENNReal.ofReal (c⁻¹ * B) = _
      rw [ENNReal.ofReal_mul (inv_nonneg.mpr hc.le), ENNReal.ofReal_toReal htop]

/-- Proposition 3.6 of the paper, literally with probability,
a closed scalar Dirichlet form (whose generator is nonnegative), the radial
chain rule on H¹, a measurable symmetric coercive matrix, and the weak
finite-energy equation. The displayed equation (3.13) uses Euclidean essential
suprema and also covers sources with infinite essential supremum. The
parameter `G` records the codomain of ∇ in the scalar gradient form. -/
theorem maximumPrinciple_radialChainRule {α G : Type*} [MeasurableSpace α]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (ρ : Measure α) [IsProbabilityMeasure ρ]
    (Q : ScalarFormData ρ) (_hQ : IsClosedScalarDirichletForm Q)
    (hchain : HasRadialChainRule (G := G) Q) (m : ℕ+)
    (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hMmeas : ∀ i j, Measurable (fun x => M x i j)) (c : ℝ) (hc : 0 < c)
    (hM : ∀ᵐ x ∂ρ, (∀ i j, M x i j = M x j i) ∧
      ∀ z : Fin (m : ℕ) → ℝ,
        c * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j)
    (v : Fin (m : ℕ) → Lp ℝ 2 ρ) (u : Fin (m : ℕ) → Q.1)
    (hu : WeightedWeakSolution Q M ⊤ v u) :
    eLpNorm (fun x => WithLp.toLp 2 (fun i => (u i).val x)) ∞ ρ ≤
      ENNReal.ofReal c⁻¹ * eLpNorm (fun x => WithLp.toLp 2 (fun i => v i x)) ∞ ρ :=
  maximumPrinciple_radialChainRule_subspace Q (hchain m) M hMmeas c hc hM ⊤ v u hu

end Riesz2
