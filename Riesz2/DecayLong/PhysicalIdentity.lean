/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.MovingFibre
public import Riesz2.DecayLong.SchurRestriction
public import Riesz2.DecayLong.AbstractEquation
public import Riesz2.DecayShort.LocalLaw
public import Riesz2.HelfferSjostrand.MarginalCollision
public import Riesz2.HelfferSjostrand.PaperMarginalHessian
public import Riesz2.DecayLong.PhysicalFormDomainPart2

/-!
# Curvature and form comparison for the physical equation

Support for Subsection 5.1. The curvature estimate retains the
factor depending on `s` that is necessary when `s` is smaller than one.
The internal comparison lemmas operate on a single form domain and also
apply after compression to any fixed component subspace.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.PhysicalIdentity

/-- The nearest-pair curvature and the upper forcing give a common positive
quadratic lower bound, also for `0 < s < 1`. This is the scalar step in the
proof of Subsection 5.1. The minimum retains the small-`s` prefactor. -/
theorem scalar_curvature (θ : PhysicalCutoff) {s x R : ℝ}
    (hs : 0 < s) (hx : 0 < x) (hR : 1 ≤ R) :
    min 1 (s * (s + 1)) * R ^ (-s - 2) ≤ s * (s + 1) * x ^ (-s - 2) +
      deriv (deriv θ.val) (x / R) / R ^ 2 := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  obtain ⟨C, _, hθ, hθlarge⟩ := θ.property.2.2.2.2
  have hθnonneg := (hθ (x / R) (div_pos hx hR0)).1
  have hc : 0 ≤ s * (s + 1) := by positivity
  by_cases hsmall : x ≤ R
  · have hpow := Real.rpow_le_rpow_of_nonpos hx hsmall (show -s - 2 ≤ 0 by linarith)
    calc
      _ ≤ s * (s + 1) * R ^ (-s - 2) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg hR0.le _)
      _ ≤ s * (s + 1) * x ^ (-s - 2) := mul_le_mul_of_nonneg_left hpow hc
      _ ≤ _ := le_add_of_nonneg_right (div_nonneg hθnonneg (sq_nonneg R))
  · have hh := hθlarge (x / R) ((one_le_div hR0).mpr (le_of_not_ge hsmall))
    have hpow := Real.rpow_le_rpow_of_exponent_le hR (show -s - 2 ≤ -(2 : ℝ) by linarith)
    have he : R ^ (-(2 : ℝ)) = 1 / R ^ 2 := by
      rw [Real.rpow_neg hR0.le, Real.rpow_two, one_div]
    rw [he] at hpow
    calc
      _ ≤ R ^ (-s - 2) :=
        mul_le_of_le_one_left (Real.rpow_nonneg hR0.le _) (min_le_left _ _)
      _ ≤ 1 / R ^ 2 := hpow
      _ ≤ deriv (deriv θ.val) (x / R) / R ^ 2 :=
        div_le_div_of_nonneg_right hh (sq_nonneg R)
      _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hc (Real.rpow_nonneg hx.le _))

/-- See Subsection 5.1 of the paper, common quadratic before marginalization. The
realization is the ambient energy, and the estimate holds
for every selected active set and every ambient direction, including `N=2`.
The positive constant depends only on the exponent, not on volume or scale. -/
theorem full_curvature (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (θ : PhysicalCutoff)
    (R : {R : ℝ // 0 < R}) (hR : 1 ≤ (R : ℝ))
    (J : Finset (Fin (N : ℕ))) :
    let p := ofLong β s
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ∀ (y : Fin (N : ℕ) → ℝ), y ∈ Riesz1.gapSimplex N →
        ∀ u : EuclideanSpace ℝ (Fin (N : ℕ)),
          min 1 (s.val * (s.val + 1)) * (R : ℝ) ^ (-s.val - 2) *
              (∑ i ∈ J, (u i) ^ 2) ≤
            fderiv ℝ (fderiv ℝ (fun z => W z + ∑ i ∈ J, θ.val (z i / R)))
              (WithLp.toLp 2 y) u u := by
  classical
  intro p
  obtain ⟨W, hW, hval, _, _, hlow, _⟩ :=
    (PhysicalEnergy.restriction_and_derivatives p N hN).2.2
  refine ⟨W, hW, hval, ?_⟩
  intro y hy u
  let x : EuclideanSpace ℝ (Fin (N : ℕ)) := WithLp.toLp 2 y
  let F : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ := fun z => ∑ i ∈ J, θ.val (z i / R)
  have hx : x ∈ gapAmbientDomain N := PhysicalEnergy.simplex_subset_ambient N y hy
  have hW₂ : ContDiffAt ℝ 2 W x :=
    (hW.of_le (by norm_num)).contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hx)
  have hF₂ : ContDiffAt ℝ 2 F x := DecayShort.upperGapPenalty_contDiffAt θ R J x hy.1
  have he := PhysicalCollision.internal_hessian_add hW₂ hF₂ u u
  rw [DecayShort.upperGapPenalty_hessian θ R J x hy.1 u u] at he
  change _ ≤ fderiv ℝ (fderiv ℝ (fun z => W z + F z)) x u u
  rw [he]
  have hsub : (∑ i ∈ J, y i ^ (-s.val - 2) * (u i) ^ 2) ≤
      ∑ i, y i ^ (-s.val - 2) * (u i) ^ 2 :=
    Finset.sum_le_univ_sum_of_nonneg fun i =>
      mul_nonneg (Real.rpow_nonneg (hy.1 i).le _) (sq_nonneg _)
  have hc : 0 ≤ s.val * (s.val + 1) :=
    mul_nonneg s.property.1.le (by linarith [s.property.1])
  have hbase := (mul_le_mul_of_nonneg_left hsub hc).trans (hlow y hy u)
  have hscalar : min 1 (s.val * (s.val + 1)) * (R : ℝ) ^ (-s.val - 2) *
      (∑ i ∈ J, (u i) ^ 2) ≤
        s.val * (s.val + 1) * (∑ i ∈ J, y i ^ (-s.val - 2) * (u i) ^ 2) +
        ∑ i ∈ J, deriv (deriv θ.val) (y i / R) / (R : ℝ) ^ 2 * (u i) ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have h := mul_le_mul_of_nonneg_right
      (scalar_curvature θ s.property.1 (hy.1 i) hR) (sq_nonneg (u i))
    nlinarith only [h]
  simp only [x, ← pow_two]
  exact hscalar.trans (by linarith only [hbase])

/-- See Subsection 5.1 of the paper, uniform proper-marginal curvature step. The
positive constant depends only on `s`, and the scale is `R^(-s-2)`.
Taking `R=n^ε` gives the exponent `κ=s+2` independent of temperature.
The conclusion concerns the actual negative-log fibre potential, with
upper forcing, and covers every exterior dimension including zero. -/
theorem proper_curvature (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n m : ℕ) (hn : 1 ≤ n) (θ : PhysicalCutoff)
    (R : {R : ℝ // 0 < R}) (hR : 1 ≤ (R : ℝ)) :
    let p := ofLong β s
    let V := fun x : EuclideanSpace ℝ (Fin n) =>
      p.val.1 * ∑ i, θ.val (x i / R) - Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal)
    ContDiffOn ℝ ∞ V (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) ∧
      ∀ x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
        ∀ u : EuclideanSpace ℝ (Fin n),
          β.val * min 1 (s.val * (s.val + 1)) * (R : ℝ) ^ (-s.val - 2) * ‖u‖ ^ 2 ≤
            fderiv ℝ (fderiv ℝ V) x u u := by
  simpa only [ofLong, mul_assoc] using
    PaperMarginalHessian.paper_upper_potential_hessian
      (ofLong β s) n m hn (Equiv.refl _) θ R hR

/-- See Subsection 5.1 of the paper, curvature in the literal `n^(-ε)` forcing
convention of Section 5. The lower bound has `κ=s+2`, uniformly in
total volume and temperature. -/
theorem proper_scaled_curvature (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε : ℝ) (hε : 0 ≤ ε) :
    let p := ofLong β s
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      p.val.1 * ∑ i, θ.val ((n : ℝ) ^ (-ε) * x i) - Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal)
    ContDiffOn ℝ ∞ V (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) ∧
      ∀ x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
        ∀ u : EuclideanSpace ℝ (Fin (n : ℕ)),
          (β.val * min 1 (s.val * (s.val + 1)) * (n : ℝ) ^ (-(s.val + 2) * ε)) * ‖u‖ ^ 2 ≤
            fderiv ℝ (fderiv ℝ V) x u u := by
  have hn : (0 : ℝ) < n := by exact_mod_cast n.pos
  let R : {R : ℝ // 0 < R} := ⟨(n : ℝ) ^ ε, Real.rpow_pos_of_pos hn _⟩
  have hR : 1 ≤ (R : ℝ) := Real.one_le_rpow
    (by exact_mod_cast (show 1 ≤ (n : ℕ) from n.pos)) hε
  have hscale : (R : ℝ)⁻¹ = (n : ℝ) ^ (-ε) := (Real.rpow_neg hn.le ε).symm
  have hpow : (R : ℝ) ^ (-s.val - 2) = (n : ℝ) ^ (-(s.val + 2) * ε) := by
    rw [show (R : ℝ) = (n : ℝ) ^ ε from rfl, ← Real.rpow_mul hn.le]
    congr 1
    ring
  simpa only [div_eq_mul_inv, hscale, hpow, mul_comm] using
    proper_curvature β s n m n.pos θ R hR

/-- Physical solvability on the common Sobolev domain of Subsection 5.1,
for all L² sources and every fixed component compression. -/
theorem proper_physical_equation (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε : ℝ) (hε : 0 ≤ ε) :
    let p := ofLong β s
    let hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ) := by simp; omega
    let ρ := activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ ε false
    let Ω := AffineSimplex.chartDomain n ((n + m : ℕ) + 1)
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      p.val.1 * ∑ i, θ.val ((n : ℝ) ^ (-ε) * x i) - Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal)
    ∃ Q : ScalarFormData ρ, IsNeumannRealization Ω Q ∧
      IsClosedScalarDirichletForm Q ∧
      (∀ (S : Submodule ℝ (Fin (n : ℕ) → ℝ)) (u : Fin (n : ℕ) → Q.1),
        WeightedFormDomain Q (hessianMatrix V) S u ↔
          ∀ᵐ x ∂ρ, (fun i => (u i).val x) ∈ S) ∧
      ∀ (S : Submodule ℝ (Fin (n : ℕ) → ℝ)) (f : Fin (n : ℕ) → Lp ℝ 2 ρ),
        ∃! u, WeightedWeakSolution Q (hessianMatrix V) S f u := by
  intro p hn ρ Ω V
  obtain ⟨Q, hreal, hQ, _, hdom, _⟩ := PhysicalFormDomain.proper_form_domain β s n m θ ε
  refine ⟨Q, hreal, hQ, hdom, ?_⟩
  let a := β.val * min 1 (s.val * (s.val + 1)) * (n : ℝ) ^ (-(s.val + 2) * ε)
  have ha : 0 < a := by
    apply mul_pos (mul_pos β.property (lt_min zero_lt_one (mul_pos s.property.1 (by linarith [s.property.1]))))
      (Real.rpow_pos_of_pos (by exact_mod_cast n.pos) _)
  have hV := PhysicalFormDomain.proper_gibbs_potential β s n m θ ε
  have hcurv := (proper_scaled_curvature β s n m θ ε hε).2
  have hM : ∀ᵐ x ∂ρ, (∀ i j, hessianMatrix V x i j = hessianMatrix V x j i) ∧
      ∀ z : Fin (n : ℕ) → ℝ,
        a * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * hessianMatrix V x i j * z j := by
    filter_upwards [IntrinsicScalarCore.supported (AffineSimplex.isOpen_chartDomain n _) hV] with x hx
    have hsm := hV.1.contDiffAt ((AffineSimplex.isOpen_chartDomain n _).mem_nhds hx)
    refine ⟨fun i j => ?_, fun z => ?_⟩
    · rw [Intrinsic.hessianMatrix_eq_second hsm, Intrinsic.hessianMatrix_eq_second hsm]
      exact (hsm.isSymmSndFDerivAt (by norm_num)).eq _ _
    · have h := hcurv x hx (WithLp.toLp 2 z)
      rw [← PhysicalEnergy.hessianMatrix_quadratic (hsm.of_le (by norm_num)),
        EuclideanSpace.real_norm_sq_eq] at h
      exact h
  intro S f
  have he := (AbstractEquation.existence_energy Q hQ 1 zero_lt_one (hessianMatrix V)
    (fun i j => DifferentiatedPoisson.measurable_hessian_entries i j) a ha hM S f).1
  simpa only [one_smul] using he

namespace Internal

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Algebraic part of Subsection 5.1. When `A = S + T` and both
equations have the same right-hand side on the same form domain, the
difference is `A (v-ψ) = T v`. -/
theorem comparison_equation (A S T : H →L[ℝ] H →L[ℝ] ℝ)
    (hA : A = S + T) (f : H →L[ℝ] ℝ) (v ψ : H)
    (hv : ∀ z, S v z = f z) (hψ : ∀ z, A ψ z = f z) :
    ∀ z, A (v - ψ) z = T v z := by
  intro z
  rw [map_sub, sub_apply, hψ, hA]
  simp only [add_apply, hv]
  ring

/-- The physical energy estimate follows by testing with the actual
difference on that same domain. Specializing `H` to a constrained form
space gives exactly the compressed comparison, with no change of source. -/
theorem comparison_energy (A S T : H →L[ℝ] H →L[ℝ] ℝ)
    (hA : A = S + T) (f : H →L[ℝ] ℝ) (v ψ : H)
    (hv : ∀ z, S v z = f z) (hψ : ∀ z, A ψ z = f z)
    (E : H → ℝ) (hE : ∀ z, E z ≤ A z z) :
    E (v - ψ) ≤ T v (v - ψ) := by
  rw [← comparison_equation A S T hA f v ψ hv hψ (v - ψ)]
  exact hE (v - ψ)

end Internal
end Riesz2.PhysicalIdentity
