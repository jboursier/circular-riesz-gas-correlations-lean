/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.PhysicalIdentityPart2
public import Riesz2.DecayLong.PhysicalCorePart2

/-!
# Continuous physical core pairings on the ambient Sobolev domain

The core is defined on the open carrier, whereas the physical scalar form
lives in ambient L². Pulling back its values along the measure-preserving
inclusion identifies the actual multiplication forms, with no extension of
the core outside its carrier. This is a bridge for Subsection 5.1.
-/

public section
noncomputable section

open MeasureTheory Set
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.PhysicalIdentity.Internal

/-- Bounded coefficients on the open physical carrier give continuous
pairings on the original ambient scalar form domain. Only the values are
pulled back. The scalar energy and its component space are preserved. -/
theorem subtype_matrix_form (n : ℕ+) (m : ℕ)
    {ν : Measure (EuclideanSpace ℝ (Fin (n : ℕ)))}
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (hco : MeasurePreserving
      ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
      (ν.comap ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))) ν)
    (A : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (hm : ∀ i j, Measurable (fun x => A x i j))
    (hb : ∃ b : ℝ, 0 ≤ b ∧ ∀ x i j, |A x i j| ≤ b) :
    ∃ B : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ]
        MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ] ℝ,
      ∀ u v,
        let P := fun x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) =>
          ∑ i, ∑ j, (MatrixEnergy.vectorEquiv Q hQ u i).val x.val * A x i j *
            (MatrixEnergy.vectorEquiv Q hQ v j).val x.val
        Integrable P (ν.comap ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
          EuclideanSpace ℝ (Fin (n : ℕ)))) ∧
        B u v = ∫ x, P x ∂ν.comap ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
          EuclideanSpace ℝ (Fin (n : ℕ))) := by
  let Ω := AffineSimplex.chartDomain n ((n + m : ℕ) + 1)
  let μ := ν.comap ((↑) : Ω → EuclideanSpace ℝ (Fin (n : ℕ)))
  let J : ScalarFormHilbert.Space Q hQ →L[ℝ] Lp ℝ 2 μ :=
    (Lp.compMeasurePreservingₗᵢ ℝ ((↑) : Ω → EuclideanSpace ℝ (Fin (n : ℕ))) hco).toContinuousLinearMap.comp
      (ScalarFormHilbert.value Q hQ)
  obtain ⟨b, hb0, hb⟩ := hb
  have hs (f : ScalarFormHilbert.Space Q hQ) :
      Integrable (fun x => b * (J f x) ^ 2) μ ∧
        (∫ x, b * (J f x) ^ 2 ∂μ) ≤ b * ‖f‖ ^ 2 := by
    have hi : Integrable (fun x => (J f x) ^ 2) μ := by
      apply ((Lp.memLp (J f)).integrable_mul (Lp.memLp (J f))).congr
      exact ae_of_all μ fun x => (pow_two (J f x)).symm
    have he : (∫ x, (J f x) ^ 2 ∂μ) = ‖J f‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards with x
      simp only [Real.inner_apply, pow_two]
    have hn : ‖J f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
      have hnorm : ‖J f‖ = ‖(ScalarFormHilbert.equiv Q hQ f).val‖ :=
        Lp.norm_compMeasurePreserving _ hco
      rw [hnorm, ScalarFormHilbert.norm_sq]
      exact le_add_of_nonneg_right (hQ.2.2.1 _)
    refine ⟨hi.const_mul b, ?_⟩
    rw [integral_const_mul, he]
    exact mul_le_mul_of_nonneg_left hn hb0
  have hex (i j : Fin (n : ℕ)) := PhysicalFormDomain.Internal.exists_entry_form
    J (fun _ => b) (fun x => A x i j) (hm i j).aestronglyMeasurable
    (ae_of_all μ (fun x => hb x i j)) b hb0 hs
  choose E hE using hex
  let B : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ] ℝ :=
    ∑ i, ∑ j, (E i j).bilinearComp (PiLp.proj 2 _ i) (PiLp.proj 2 _ j)
  refine ⟨B, fun u v => ?_⟩
  have heq : (fun x : Ω => ∑ i, ∑ j, A x i j * J (u i) x * J (v j) x) =ᵐ[μ]
      (fun x : Ω => ∑ i, ∑ j,
        (MatrixEnergy.vectorEquiv Q hQ u i).val x.val * A x i j *
          (MatrixEnergy.vectorEquiv Q hQ v j).val x.val) := by
    filter_upwards [ae_all_iff.mpr (fun i => Lp.coeFn_compMeasurePreserving
        (ScalarFormHilbert.value Q hQ (u i)) hco),
      ae_all_iff.mpr (fun j => Lp.coeFn_compMeasurePreserving
        (ScalarFormHilbert.value Q hQ (v j)) hco)] with x hx hy
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change A x i j * (Lp.compMeasurePreserving _ hco (ScalarFormHilbert.value Q hQ (u i))) x *
      (Lp.compMeasurePreserving _ hco (ScalarFormHilbert.value Q hQ (v j))) x = _
    rw [hx i, hy j]
    change A x i j * (MatrixEnergy.vectorEquiv Q hQ u i).val x.val *
      (MatrixEnergy.vectorEquiv Q hQ v j).val x.val = _
    ring
  have hi : Integrable (fun x : Ω => ∑ i, ∑ j, A x i j * J (u i) x * J (v j) x) μ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hE i j (u i) (v j)).1
  refine ⟨hi.congr heq, ?_⟩
  rw [← integral_congr_ae heq, integral_finsetSum]
  · simp only [B, sum_apply, ContinuousLinearMap.bilinearComp_apply,
      PiLp.proj_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl fun j _ => (hE i j (u i) (v j)).2
    · exact fun j _ => (hE i j (u i) (v j)).1
  · exact fun i _ => integrable_finsetSum _ fun j _ => (hE i j (u i) (v j)).1

end Riesz2.PhysicalIdentity.Internal

namespace Riesz2.PhysicalIdentity

/-- See Subsection 5.1 of the paper (continuous multiplication forms): the physical
Hessian, the actual active core, and their combined signed difference
are continuous forms on the same ambient physical Sobolev product. The
coefficient difference is combined before integration. No coefficient field
is extended outside the open carrier, and no separate integrability of the
compensation or covariance terms is asserted. -/
theorem proper_core_forms (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ) :
    let p := ofLong β s
    let hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ) := by simp; omega
    let ν := activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ ε false
    let Ω := AffineSimplex.chartDomain n ((n + m : ℕ) + 1)
    let μ := ν.comap ((↑) : Ω → EuclideanSpace ℝ (Fin (n : ℕ)))
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      β.val * ∑ i, θ.val ((n : ℝ) ^ (-ε) * x i) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal)
    ∃ Q : ScalarFormData ν, IsNeumannRealization Ω Q ∧
      ∃ hQ : IsClosedScalarDirichletForm Q,
        (∀ (S : Submodule ℝ (Fin (n : ℕ) → ℝ)) (u : Fin (n : ℕ) → Q.1),
          WeightedFormDomain Q (hessianMatrix V) S u ↔
            ∀ᵐ x ∂ν, (fun i => (u i).val x) ∈ S) ∧
        ∃ H : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ]
            MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ] ℝ,
          (∀ u v, Integrable (matrixFieldPair (hessianMatrix V)
              (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val)
              (fun i => (MatrixEnergy.vectorEquiv Q hQ v i).val)) ν ∧
            H u v = ∫ x, matrixFieldPair (hessianMatrix V)
              (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val)
              (fun i => (MatrixEnergy.vectorEquiv Q hQ v i).val) x ∂ν) ∧
          ∀ (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ),
            ∃ B D : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ]
                MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ] ℝ,
              H = β.val • B + D ∧ ∀ u v,
                let A₀ := PhysicalCore.properActive β s n m M hM hnM K θ ε κ₀
                let U := fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val
                let W := fun i => (MatrixEnergy.vectorEquiv Q hQ v i).val
                let P := fun x : Ω => ∑ i, ∑ j, U i x.val * A₀ x i j * W j x.val
                let T := fun x : Ω => ∑ i, ∑ j,
                  U i x.val * (hessianMatrix V x.val i j - β.val * A₀ x i j) * W j x.val
                Integrable P μ ∧ B u v = ∫ x, P x ∂μ ∧
                Integrable T μ ∧ D u v = ∫ x, T x ∂μ := by
  intro p hn ν Ω μ V
  obtain ⟨Q, hreal, hQ, _, hdom, H₀, hH₀⟩ := PhysicalFormDomain.proper_form_domain β s n m θ ε
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n : ℕ) => ScalarFormHilbert.Space Q hQ)
  let H := H₀.bilinearComp e.toContinuousLinearMap e.toContinuousLinearMap
  have hH (u v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ) :
      Integrable (matrixFieldPair (hessianMatrix V)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ v i).val)) ν ∧
      H u v = ∫ x, matrixFieldPair (hessianMatrix V)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ v i).val) x ∂ν := by
    have h := hH₀ (MatrixEnergy.vectorEquiv Q hQ u) (MatrixEnergy.vectorEquiv Q hQ v)
    have hu : (fun i => (ScalarFormHilbert.equiv Q hQ).symm
        (MatrixEnergy.vectorEquiv Q hQ u i)) = e u := by
      funext i
      exact (ScalarFormHilbert.equiv Q hQ).symm_apply_apply (u i)
    have hv : (fun i => (ScalarFormHilbert.equiv Q hQ).symm
        (MatrixEnergy.vectorEquiv Q hQ v i)) = e v := by
      funext i
      exact (ScalarFormHilbert.equiv Q hQ).symm_apply_apply (v i)
    refine ⟨h.1, ?_⟩
    change H₀ (e u) (e v) = _
    rw [← hu, ← hv]
    exact h.2
  refine ⟨Q, hreal, hQ, hdom, H, hH, fun M hM hnM K => ?_⟩
  have hco : MeasurePreserving ((↑) : Ω → EuclideanSpace ℝ (Fin (n : ℕ))) μ ν := by
    refine ⟨measurable_subtype_coe, ?_⟩
    rw [map_comap_subtype_coe (AffineSimplex.isOpen_chartDomain n _).measurableSet]
    exact Measure.restrict_eq_self_of_ae_mem (IntrinsicScalarCore.supported
      (AffineSimplex.isOpen_chartDomain n _) (PhysicalFormDomain.proper_gibbs_potential β s n m θ ε))
  let A₀ := PhysicalCore.properActive β s n m M hM hnM K θ ε κ₀
  obtain ⟨B, hB⟩ := Internal.subtype_matrix_form n m Q hQ hco A₀
    (PhysicalCore.measurable_properActive β s n m M hM hnM K θ ε κ₀)
    (PhysicalCore.properActive_bounded β s n m M hM hnM K θ ε κ₀)
  let D := H - β.val • B
  refine ⟨B, D, by dsimp only [D]; abel, fun u v => ?_⟩
  intro A₀' U W P T
  have hBi := hB u v
  have hHi := hH u v
  let F := matrixFieldPair (hessianMatrix V) U W
  have hFc : Integrable (F ∘ ((↑) : Ω → EuclideanSpace ℝ (Fin (n : ℕ)))) μ :=
    hco.integrable_comp_of_integrable hHi.1
  have hT : T = fun x : Ω => F x.val - β.val * P x := by
    funext x
    simp only [T, P, F, matrixFieldPair, mul_sub, sub_mul,
      Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  refine ⟨hBi.1, hBi.2, ?_, ?_⟩
  · rw [hT]
    exact hFc.sub (hBi.1.const_mul _)
  · change H u v - β.val * B u v = _
    rw [hHi.2, hBi.2, hT]
    have hchange := hco.integral_comp (MeasurableEmbedding.subtype_coe
      (AffineSimplex.isOpen_chartDomain n _).measurableSet) F
    symm
    calc
      _ = (∫ x : Ω, F x.val ∂μ) - β.val * ∫ x, P x ∂μ := by
        simpa only [Function.comp_def, integral_const_mul] using
          integral_sub hFc (hBi.1.const_mul β.val)
      _ = _ := by rw [hchange]

end Riesz2.PhysicalIdentity
