/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.PhysicalCore
public import Riesz2.DecayShort.LocalLaw
public import Riesz2.DecayLong.SchurRestriction

/-!
# Bounds on the physical core at fixed volume

The coefficient cutoff in the actual good event bounds every internal
entry. Together with the bounded forcing curvature, this makes the whole
matrix bounded on its entire carrier. These are the fixed-volume
boundedness interfaces needed to construct the forms in Subsection 5.1.
The uniform entry profile in the proof of Lemma 5.4 is a further estimate.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped BigOperators ContDiff

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.PhysicalCore

/-- See Section 5 of the paper: every forcing Hessian entry is diagonal, with
the actual scale factor and the classical second derivative of the cutoff. -/
theorem forcingHessian_apply (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (a b : Fin (n : ℕ)) :
    forcingHessian n θ ε x.val a b =
      if a = b then deriv (deriv θ.val) ((n : ℝ) ^ (-ε) * x.val a) /
        ((n : ℝ) ^ ε) ^ 2 else 0 := by
  let R : {R : ℝ // 0 < R} :=
    ⟨(n : ℝ) ^ ε, Real.rpow_pos_of_pos (by exact_mod_cast n.pos) _⟩
  have hscale : (R : ℝ)⁻¹ = (n : ℝ) ^ (-ε) :=
    (Real.rpow_neg (by exact_mod_cast n.pos.le) ε).symm
  have heq : (fun z : EuclideanSpace ℝ (Fin (n : ℕ)) => ∑ i, θ.val (z i / R)) =
      (fun z => ∑ i, θ.val ((n : ℝ) ^ (-ε) * z i)) := by
    simp only [div_eq_mul_inv, hscale, mul_comm]
  have hs := (forcing_smooth n m θ ε).contDiffAt
    ((AffineSimplex.isOpen_chartDomain n _).mem_nhds x.property)
  have h := DecayShort.upperGapPenalty_hessian (N := n) θ R Finset.univ x.val x.property.1
    (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)
  rw [heq] at h
  rw [← Intrinsic.hessianMatrix_eq_second hs] at h
  by_cases hab : a = b
  · subst b
    simpa [forcingHessian, PiLp.single_apply, div_eq_mul_inv, hscale, mul_comm, R] using h
  · simpa [forcingHessian, PiLp.single_apply, div_eq_mul_inv, hscale, mul_comm, R,
      hab, Ne.symm hab] using h

/-- The forcing Hessian has a finite bound on the whole open physical
carrier. The scale is retained explicitly, and no good-event hypothesis
is needed. -/
theorem forcingHessian_bound (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
      (a b : Fin (n : ℕ)), 0 ≤ forcingHessian n θ ε x.val a b ∧
        |forcingHessian n θ ε x.val a b| ≤ C := by
  obtain ⟨C, hC, hb, _⟩ := θ.property.2.2.2.2
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  refine ⟨C / ((n : ℝ) ^ ε) ^ 2, div_nonneg hC0 (sq_nonneg _), fun x a b => ?_⟩
  rw [forcingHessian_apply n m θ ε x a b]
  split_ifs
  · have h := hb ((n : ℝ) ^ (-ε) * x.val a)
      (mul_pos (Real.rpow_pos_of_pos (by exact_mod_cast n.pos) _) (x.property.1 a))
    have hn := div_nonneg h.1 (sq_nonneg ((n : ℝ) ^ ε))
    exact ⟨hn, by rw [abs_of_nonneg hn]; exact div_le_div_of_nonneg_right h.2 (sq_nonneg _)⟩
  · exact ⟨le_rfl, by rw [abs_zero]; positivity⟩

/-- The physical internal entries on the good event are bounded by its
literal coefficient cutoff. This bound uses the physical period in the
distance, rather than silently substituting the reference period. -/
theorem physicalInternal_good_bound (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (θscale κ₀ : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (hx : x ∈ GoodBlocks.properGoodEvent β s n m θscale κ₀) (a b : Fin (n : ℕ)) :
    |BoundaryEntries.physicalInternal β s n m x a b| ≤ (n : ℝ) ^ (κ₀ * θscale) := by
  rw [abs_of_nonneg (BoundaryEntries.physicalInternal_nonneg β s n m x a b)]
  have hP := BoundaryEntries.physicalInternal_add_crossing β s n m x a b
  have hc := BoundaryEntries.physicalCrossing_nonneg β s n m x a b
  have hcut := hx.2 a b
  have hdist : (1 + (Riesz1.cyclicIndexDistance ((n : ℕ) + m).succPNat
      (a.castAdd m).castSucc (b.castAdd m).castSucc : ℝ)) ^ (-s.val) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos
      (le_add_of_nonneg_right (Nat.cast_nonneg _)) (by linarith [s.property.1])
  have hh := mul_le_mul_of_nonneg_left hdist
    (show 0 ≤ (n : ℝ) ^ (κ₀ * θscale) from Real.rpow_nonneg (by positivity) _)
  rw [mul_one] at hh
  exact (by linarith only [hP, hc] : BoundaryEntries.physicalInternal β s n m x a b ≤
    GoodBlocks.conditionalHessian β s n m a b x).trans (hcut.trans hh)

private theorem entry_le_sum_abs {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) (i j : ι) :
    |A i j| ≤ ∑ a, ∑ b, |A a b| := by
  classical
  exact (Finset.single_le_sum (fun b _ => abs_nonneg (A i b)) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun a _ => Finset.sum_nonneg fun b _ => abs_nonneg (A a b))
      (Finset.mem_univ i))

/-- See Subsection 5.1 of the paper, boundedness of the actual active block
on its entire carrier. This proves a fixed-volume bound, including both
freezing branches, without assuming any periodized-matrix conclusion. -/
theorem properActive_bounded (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
      (a b' : Fin (n : ℕ)), |properActive β s n m M hM hnM K θ ε κ₀ x a b'| ≤ b := by
  obtain ⟨C, hC, hF⟩ := forcingHessian_bound n m θ ε
  let A := BoundaryEntries.referenceInternal s M hM K n hnM
  let B := BoundaryEntries.referenceCrossing s M hM K n hnM
  let b := C + (n : ℝ) ^ (κ₀ * ε) + (∑ a, ∑ b, |A a b|) + ∑ a, ∑ b, |B a b|
  have hAn : 0 ≤ ∑ a, ∑ b, |A a b| :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => abs_nonneg _
  have hBn : 0 ≤ ∑ a, ∑ b, |B a b| :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => abs_nonneg _
  have hpow : 0 ≤ (n : ℝ) ^ (κ₀ * ε) := Real.rpow_nonneg (by positivity) _
  refine ⟨b, by dsimp only [b]; linarith, fun x a b' => ?_⟩
  have hA := entry_le_sum_abs A a b'
  have hB := entry_le_sum_abs B a b'
  by_cases hx : x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀
  · have hP := physicalInternal_good_bound β s n m ε κ₀ x hx a b'
    have hff := (hF x a b').2
    simp only [properActive, ite_eq_left hx, Matrix.add_apply]
    have htri := abs_add_le (forcingHessian n θ ε x.val a b' +
      BoundaryEntries.physicalInternal β s n m x a b') (B a b')
    have htri₂ := abs_add_le (forcingHessian n θ ε x.val a b')
      (BoundaryEntries.physicalInternal β s n m x a b')
    dsimp only [b]
    linarith only [htri, htri₂, hff, hP, hB, hAn]
  · simp only [properActive, ite_eq_right hx, Matrix.add_apply]
    have htri := abs_add_le (A a b') (B a b')
    dsimp only [b]
    linarith only [htri, hA, hB, hC, hpow]

/-- Every entry of the entire physical core is bounded at fixed parameters.
Together with its measurability this supplies the bounded
multiplication interface on the full scalar Sobolev product. -/
theorem properMatrix_bounded (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
      (a b' : Fin (M : ℕ)), |properMatrix β s n m M hM hnM K θ ε κ₀ x a b'| ≤ b := by
  obtain ⟨C, hC, hb⟩ := properActive_bounded β s n m M hM hnM K θ ε κ₀
  let H := (2 : ℝ) • referenceIntervalMatrix s M hM K
  have hH : 0 ≤ ∑ a, ∑ b, |H a b| :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => abs_nonneg _
  refine ⟨C + ∑ a, ∑ b, |H a b|, by linarith, fun x a b' => ?_⟩
  by_cases ha : a.val < (n : ℕ)
  · by_cases hb' : b'.val < (n : ℕ)
    · simp only [properMatrix, ha, hb', ↓reduceDIte]
      exact (hb x _ _).trans (le_add_of_nonneg_right hH)
    · rw [properMatrix_exterior β s n m M hM hnM K θ ε κ₀ x a b'
        (Or.inr (Nat.le_of_not_lt hb'))]
      exact (entry_le_sum_abs H a b').trans (le_add_of_nonneg_left hC)
  · rw [properMatrix_exterior β s n m M hM hnM K θ ε κ₀ x a b'
      (Or.inl (Nat.le_of_not_lt ha))]
    exact (entry_le_sum_abs H a b').trans (le_add_of_nonneg_left hC)

/-- See Subsection 5.1 of the paper, integrability of every active pairing
for arbitrary L² fields on the open carrier. No positivity, scalar
equation, or separate integrability of perturbation pieces is assumed. -/
theorem properActive_pair_integrable (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ)
    (ρ : Measure (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)))
    (u v : Fin (n : ℕ) → Lp ℝ 2 ρ) :
    Integrable (matrixFieldPair (properActive β s n m M hM hnM K θ ε κ₀) u v) ρ := by
  obtain ⟨b, _, hb⟩ := properActive_bounded β s n m M hM hnM K θ ε κ₀
  exact BoundedMatrixForms.integrable_pair _
    (measurable_properActive β s n m M hM hnM K θ ε κ₀)
    ⟨b, ae_of_all _ hb⟩ u v

/-- See Subsection 5.1 of the paper, integrability of the whole physical core
multiplication form on arbitrary L² component fields. -/
theorem properMatrix_pair_integrable (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ)
    (ρ : Measure (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)))
    (u v : Fin (M : ℕ) → Lp ℝ 2 ρ) :
    Integrable (matrixFieldPair (properMatrix β s n m M hM hnM K θ ε κ₀) u v) ρ := by
  obtain ⟨b, _, hb⟩ := properMatrix_bounded β s n m M hM hnM K θ ε κ₀
  exact BoundedMatrixForms.integrable_pair _
    (measurable_properMatrix β s n m M hM hnM K θ ε κ₀)
    ⟨b, ae_of_all _ hb⟩ u v

/-- See Subsection 5.1 of the paper, the signed multiplication difference on the
entire physical Sobolev domain. The finite signed sum is combined before
integration. Its integral is exactly the physical pairing minus the
core pairing. Neither compensation nor covariance is integrated
separately. The conditional coefficient expansion is supplied by
`PhysicalIdentity.proper_multiplication_defect`. -/
theorem proper_signed_pairing (β : InverseTemperature) (s : Riesz1.RieszExponent)
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
      IsClosedScalarDirichletForm Q ∧
      (∀ (S : Submodule ℝ (Fin (n : ℕ) → ℝ)) (u : Fin (n : ℕ) → Q.1),
        WeightedFormDomain Q (hessianMatrix V) S u ↔
          ∀ᵐ x ∂ν, (fun i => (u i).val x) ∈ S) ∧
      ∀ (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : (n : ℕ) ≤ (M : ℕ))
        (K : ℕ) (u v : Fin (n : ℕ) → Q.1),
        let A₀ := properActive β s n m M hM hnM K θ ε κ₀
        let B := fun x : Ω => ∑ i, ∑ j,
          (u i).val x.val * A₀ x i j * (v j).val x.val
        let D := fun x : Ω => ∑ i, ∑ j,
          (u i).val x.val * (hessianMatrix V x.val i j - β.val * A₀ x i j) * (v j).val x.val
        Integrable B μ ∧ Integrable D μ ∧
          (∫ x, D x ∂μ) =
            (∫ x, matrixFieldPair (hessianMatrix V) (fun i => (u i).val) (fun i => (v i).val) x ∂ν) -
              β.val * ∫ x, B x ∂μ := by
  intro p hn ν Ω μ V
  obtain ⟨Q, hreal, hQ, _, hdom, H, hH⟩ := PhysicalFormDomain.proper_form_domain β s n m θ ε
  refine ⟨Q, hreal, hQ, hdom, fun M hM hnM K u v => ?_⟩
  intro A₀ B D
  have hco : MeasurePreserving ((↑) : Ω → EuclideanSpace ℝ (Fin (n : ℕ))) μ ν := by
    refine ⟨measurable_subtype_coe, ?_⟩
    rw [map_comap_subtype_coe (AffineSimplex.isOpen_chartDomain n _).measurableSet]
    exact Measure.restrict_eq_self_of_ae_mem (IntrinsicScalarCore.supported
      (AffineSimplex.isOpen_chartDomain n _) (PhysicalFormDomain.proper_gibbs_potential β s n m θ ε))
  let u' := fun i => Lp.compMeasurePreserving _ hco (u i).val
  let v' := fun i => Lp.compMeasurePreserving _ hco (v i).val
  have hA := properActive_pair_integrable β s n m M hM hnM K θ ε κ₀ μ u' v'
  have hAB : matrixFieldPair A₀ u' v' =ᵐ[μ] B := by
    filter_upwards [ae_all_iff.mpr (fun i => Lp.coeFn_compMeasurePreserving (u i).val hco),
      ae_all_iff.mpr (fun i => Lp.coeFn_compMeasurePreserving (v i).val hco)] with x hx hy
    simp only [matrixFieldPair, u', v', hx, hy, Function.comp_def, B]
  have hB : Integrable B μ := hA.congr hAB
  let P := matrixFieldPair (hessianMatrix V) (fun i => (u i).val) (fun i => (v i).val)
  have hP : Integrable P ν := (hH u v).1
  have hPc : Integrable (P ∘ ((↑) : Ω → EuclideanSpace ℝ (Fin (n : ℕ)))) μ :=
    hco.integrable_comp_of_integrable hP
  have heq : D = fun x : Ω => P x.val - β.val * B x := by
    funext x
    simp only [D, B, P, matrixFieldPair, mul_sub, sub_mul,
      Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hD : Integrable D μ := by rw [heq]; exact hPc.sub (hB.const_mul _)
  refine ⟨hB, hD, ?_⟩
  rw [heq]
  calc
    _ = (∫ x : Ω, P x.val ∂μ) - β.val * ∫ x, B x ∂μ := by
      simpa only [Function.comp_def, integral_const_mul] using
        integral_sub hPc (hB.const_mul β.val)
    _ = _ := by
      rw [hco.integral_comp (MeasurableEmbedding.subtype_coe
        (AffineSimplex.isOpen_chartDomain n _).measurableSet) P]

end Riesz2.PhysicalCore
