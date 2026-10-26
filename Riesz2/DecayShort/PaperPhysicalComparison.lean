/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.PaperGoodEvent
import all Riesz2.DecayShort.ExceptionalEventPart4

/-!
# The two matrices of the paper's short-range comparison

The prescribed identity outside the good event is part of
equation (4.13). The matrices switch on the paper event itself.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal ContDiff Topology

namespace Riesz2.DecayShort
open PhysicalComparison

/-- Equation (4.13) and the following matrix verification.
 See Subsection 4.5 of the paper: the physical auxiliary matrix, on the entire
positive retained carrier. The potential is the exact negative logarithm
of the penalized marginal density, divided by beta, as in Lemma 4.7. -/
def paperFrozenPhysicalMatrix (p : Parameters) (n : ℕ+) (m : ℕ)
    (U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ)
    (θ : PhysicalCutoff) (h : ℝ) (b : Bool) (D : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ := by
  classical
  let F := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
    ∑ i, (θ.val (((n : ℝ) ^ h)⁻¹ * y i) +
      if b then θ.val (((n : ℝ) ^ h)⁻¹ * (y i)⁻¹) else 0)
  let K := fun y => p.val.1⁻¹ * (p.val.1 * F y -
    Real.log (∫ z : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,z)).toReal))
  exact if x ∈ paperProperGoodEvent p n m U h D
    then hessianMatrix K x.val else 1

/-- Equation (4.13) and the following matrix verification.
 See Subsection 4.5 of the paper: the auxiliary internal matrix, formed from
the same conditional interval weights and the actual active penalty. -/
def paperFrozenInteriorMatrix (p : Parameters) (n : ℕ+) (m : ℕ)
    (U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ)
    (θ : PhysicalCutoff) (h : ℝ) (b : Bool) (D : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ := by
  classical
  let F := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
    ∑ i, (θ.val (((n : ℝ) ^ h)⁻¹ * y i) +
      if b then θ.val (((n : ℝ) ^ h)⁻¹ * (y i)⁻¹) else 0)
  exact if x ∈ paperProperGoodEvent p n m U h D
    then hessianMatrix F x.val + IntervalBoundary.internalMatrix
      ((n : ℕ) + m).succPNat n (by simp only [Nat.succPNat_coe]; omega)
        (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
    else 1

/-- Equation (4.13) and the following matrix verification.
 Both auxiliary matrices have exactly the prescribed value away
from the good event (Subsection 4.5). -/
theorem paperFrozenMatrices_off_event (p : Parameters) (n : ℕ+) (m : ℕ)
    (U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ)
    (θ : PhysicalCutoff) (h : ℝ) (b : Bool) (D : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (hx : x ∉ paperProperGoodEvent p n m U h D) :
    paperFrozenPhysicalMatrix p n m U θ h b D x = 1 ∧
      paperFrozenInteriorMatrix p n m U θ h b D x = 1 := by
  simp only [paperFrozenPhysicalMatrix, paperFrozenInteriorMatrix, ite_eq_right hx, and_self]

set_option backward.isDefEq.respectTransparency false in
/-- Equation (4.13) and the following matrix verification.
 Measurability and symmetry clauses of Subsection 4.5 for both
auxiliary fields, on the entire positive retained carrier. -/
theorem paperFrozenMatrices_measurable_symmetric (p : Parameters) (hs : 1 < p.val.2)
    (n : ℕ+) (m : ℕ)
    (U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ) (θ : PhysicalCutoff) (h : ℝ) (hh : 0 < h) (b : Bool) (D : ℝ) :
    (∀ i j, Measurable (fun x => paperFrozenPhysicalMatrix p n m U θ h b D x i j)) ∧
    (∀ i j, Measurable (fun x => paperFrozenInteriorMatrix p n m U θ h b D x i j)) ∧
    (∀ x i j, paperFrozenPhysicalMatrix p n m U θ h b D x i j =
      paperFrozenPhysicalMatrix p n m U θ h b D x j i) ∧
    (∀ x i j, paperFrozenInteriorMatrix p n m U θ h b D x i j =
      paperFrozenInteriorMatrix p n m U θ h b D x j i) := by
  classical
  let F := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
    ∑ i, (θ.val (((n : ℝ) ^ h)⁻¹ * y i) +
      if b then θ.val (((n : ℝ) ^ h)⁻¹ * (y i)⁻¹) else 0)
  let K := fun y => p.val.1⁻¹ * (p.val.1 * F y -
    Real.log (∫ z : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,z)).toReal))
  have hF := (ExceptionalEvent.penalty_smooth_convex n ((n + m : ℕ) + 1) θ
    (inv_pos.mpr (Real.rpow_pos_of_pos (show (0 : ℝ) < n by exact_mod_cast n.pos) h)) b).1
  have hK := (PhysicalFibres.active_marginal_curvature p hs n m n.pos (Equiv.refl _) θ h hh b).1
  have hB := measurableSet_paperProperGoodEvent p n m U h D
  have hmI (i j : Fin (n : ℕ)) : Measurable (fun x => IntervalBoundary.internalMatrix
      ((n : ℕ) + m).succPNat n (by simp only [Nat.succPNat_coe]; omega)
      (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x) i j) := by
    apply Finset.measurable_sum
    intro t _
    split_ifs
    · exact (measurable_conditionalIntervalWeight p n m n.pos (Equiv.refl _) t).mul_const _
    · exact measurable_const
  refine ⟨fun i j => ?_, fun i j => ?_, fun x i j => ?_, fun x i j => ?_⟩
  · have hm : Measurable (fun x => if x ∈ paperProperGoodEvent p n m U h D then hessianMatrix K x.val i j
        else (1 : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ) i j) := Measurable.ite hB
      (measurable_hessianMatrix (AffineSimplex.isOpen_chartDomain _ _) hK i j)
      (measurable_const (a := (1 : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ) i j))
    convert hm using 1
    funext x
    by_cases hx : x ∈ paperProperGoodEvent p n m U h D
    · simp only [paperFrozenPhysicalMatrix, ite_eq_left hx, K, F]
    · simp only [paperFrozenPhysicalMatrix, ite_eq_right hx]
  · have hm : Measurable (fun x => if x ∈ paperProperGoodEvent p n m U h D then hessianMatrix F x.val i j +
        IntervalBoundary.internalMatrix ((n : ℕ) + m).succPNat n
          (by simp only [Nat.succPNat_coe]; omega)
          (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x) i j
        else (1 : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ) i j) := Measurable.ite hB
      ((measurable_hessianMatrix (AffineSimplex.isOpen_chartDomain _ _) hF i j).add (hmI i j))
      (measurable_const (a := (1 : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ) i j))
    convert hm using 1
    funext x
    by_cases hx : x ∈ paperProperGoodEvent p n m U h D
    · simp only [paperFrozenInteriorMatrix, ite_eq_left hx, Matrix.add_apply, F]
    · simp only [paperFrozenInteriorMatrix, ite_eq_right hx]
  · change (if x ∈ paperProperGoodEvent p n m U h D then hessianMatrix K x.val else 1) i j =
        (if x ∈ paperProperGoodEvent p n m U h D then hessianMatrix K x.val else 1) j i
    by_cases hx : x ∈ paperProperGoodEvent p n m U h D
    · simp only [ite_eq_left hx]
      exact hessianMatrix_symm ((hK.contDiffAt
        ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds x.property)).of_le (by norm_num)) i j
    · simp only [ite_eq_right hx]
      exact (Matrix.isSymm_one.apply i j).symm
  · change (if x ∈ paperProperGoodEvent p n m U h D then hessianMatrix F x.val + _ else 1) i j =
        (if x ∈ paperProperGoodEvent p n m U h D then hessianMatrix F x.val + _ else 1) j i
    by_cases hx : x ∈ paperProperGoodEvent p n m U h D
    · simp only [ite_eq_left hx, Matrix.add_apply]
      rw [hessianMatrix_symm ((hF.contDiffAt
        ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds x.property)).of_le (by norm_num)) i j,
        IntervalBoundary.internalMatrix_symm]
    · simp only [ite_eq_right hx]
      exact (Matrix.isSymm_one.apply i j).symm

/-- Equation (4.13) and the following matrix verification.
 Lower quadratic-form clause for the physical auxiliary matrix in
Subsection 4.5. It holds on its entire carrier, including the
exceptional set, with no probability or fibre hypothesis. -/
theorem paperFrozenPhysicalMatrix_lower (p : Parameters) (hs : 1 < p.val.2)
    (n : ℕ+) (m : ℕ)
    (U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ) (θ : PhysicalCutoff) (h : ℝ) (hh : 0 < h)
    (b : Bool) (D : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (z : Fin (n : ℕ) → ℝ) :
    (n : ℝ) ^ (-(p.val.2 + 2) * h) * (∑ i, z i ^ 2) ≤
      ∑ i, ∑ j, z i * paperFrozenPhysicalMatrix p n m U θ h b D x i j * z j := by
  classical
  let F := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
    ∑ i, (θ.val (((n : ℝ) ^ h)⁻¹ * y i) +
      if b then θ.val (((n : ℝ) ^ h)⁻¹ * (y i)⁻¹) else 0)
  let K := fun y => p.val.1⁻¹ * (p.val.1 * F y -
    Real.log (∫ w : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,w)).toReal))
  by_cases hx : x ∈ paperProperGoodEvent p n m U h D
  · have hK := PhysicalFibres.active_marginal_curvature p hs n m n.pos (Equiv.refl _) θ h hh b
    have hKx : ContDiffAt ℝ 2 K x.val := (hK.1.of_le (by norm_num)).contDiffAt
      ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds x.property)
    have hbound := hK.2 x.val x.property (WithLp.toLp 2 z)
    have hquad := PhysicalEnergy.hessianMatrix_quadratic hKx (WithLp.toLp 2 z)
    simp only [EuclideanSpace.real_norm_sq_eq] at hbound
    change _ ≤ ∑ i, ∑ j, z i * (if x ∈ paperProperGoodEvent p n m U h D then hessianMatrix K x.val else 1) i j * z j
    rw [ite_eq_left hx]
    exact hbound.trans_eq hquad.symm
  · rw [(paperFrozenMatrices_off_event p n m U θ h b D x hx).1]
    simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← sq]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
    have hpow : (n : ℝ) ^ (-(p.val.2 + 2) * h) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hn1 (by nlinarith [p.property.2.1])
    exact mul_le_of_le_one_left (Finset.sum_nonneg fun i _ => sq_nonneg _) hpow

set_option backward.isDefEq.respectTransparency false in
/-- Equation (4.13) and the following matrix verification.
 Lower quadratic-form clause for the internal auxiliary matrix in
Subsection 4.5. On the good event, singleton curvatures suffice. On its complement the prescribed identity gives the same lower bound. -/
theorem paperFrozenInteriorMatrix_lower (p : Parameters) (hs : 1 < p.val.2)
    (n : ℕ+) (m : ℕ)
    (U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ) (hN : 2 ≤ (n : ℕ) + m + 1)
    (θ : PhysicalCutoff) (h : ℝ) (hh : 0 < h) (b : Bool) (D : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (z : Fin (n : ℕ) → ℝ) :
    (n : ℝ) ^ (-(p.val.2 + 2) * h) * (∑ i, z i ^ 2) ≤
      ∑ i, ∑ j, z i * paperFrozenInteriorMatrix p n m U θ h b D x i j * z j := by
  classical
  let F := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
    ∑ i, (θ.val (((n : ℝ) ^ h)⁻¹ * y i) +
      if b then θ.val (((n : ℝ) ^ h)⁻¹ * (y i)⁻¹) else 0)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  by_cases hx : x ∈ paperProperGoodEvent p n m U h D
  · have hupper (i : Fin (n : ℕ)) : x.val i ≤ (n : ℝ) ^ h := hx.1.2.1 i |>.2
    have hl := IntervalBoundary.internalMatrix_singleton_lower ((n : ℕ) + m).succPNat n
      (by simp only [Nat.succPNat_coe]; omega) (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
      (conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x)
      (by simpa only [Nat.succPNat_coe] using hN)
      ((n : ℝ) ^ (-(p.val.2 + 2) * h)) (fun i => ?_) z
    · obtain ⟨hF,hconv⟩ := ExceptionalEvent.penalty_smooth_convex n ((n + m : ℕ) + 1) θ
        (inv_pos.mpr (Real.rpow_pos_of_pos hn0 h)) b
      have hFx := hF.contDiffAt ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds x.property)
      have hp : 0 ≤ ∑ i, ∑ j, z i * hessianMatrix F x.val i j * z j := by
        rw [PhysicalEnergy.hessianMatrix_quadratic (hFx.of_le (by norm_num)) (WithLp.toLp 2 z)]
        exact Riesz1.fderiv_fderiv_nonneg_of_convexOn (AffineSimplex.isOpen_chartDomain _ _)
          hconv.1 hconv (hF.of_le (by norm_num)) x.property _
      change _ ≤ ∑ i, ∑ j, z i * (if x ∈ paperProperGoodEvent p n m U h D then hessianMatrix F x.val + _ else 1) i j * z j
      rw [ite_eq_left hx]
      simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
      linarith
    · have hpow : (n : ℝ) ^ (-(p.val.2 + 2) * h) ≤ (x.val i) ^ (-p.val.2 - 2) := by
        have hhpow : ((n : ℝ) ^ h) ^ (-p.val.2 - 2) =
            (n : ℝ) ^ (-(p.val.2 + 2) * h) := by
          rw [← Real.rpow_mul hn0.le]
          congr 1
          ring
        rw [← hhpow]
        exact Real.rpow_le_rpow_of_nonpos (x.property.1 i) (hupper i) (by linarith)
      have hc : 1 ≤ p.val.2 * (p.val.2 + 1) := by nlinarith
      exact (hpow.trans (le_mul_of_one_le_left
        (Real.rpow_nonneg (x.property.1 i).le _) hc)).trans
          (internal_singleton_coefficient_lower p n m hN x i)
  · rw [(paperFrozenMatrices_off_event p n m U θ h b D x hx).2]
    simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← sq]
    exact mul_le_of_le_one_left (Finset.sum_nonneg fun i _ => sq_nonneg _) <|
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast n.pos)
        (by nlinarith [p.property.2.1])


/-- Both on-event identities of equation (4.13), with the interior
matrix written literally as the complete matrix minus its boundary part. -/
theorem paperFrozenMatrices_on_event (p : Parameters) (n : ℕ+) (m : ℕ)
    (U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ)
    (θ : PhysicalCutoff) (h : ℝ) (b : Bool) (D : ℝ)
    (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1))
    (hx : x ∈ paperProperGoodEvent p n m U h D) :
    let F := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      ∑ i, (θ.val (((n : ℝ)^h)⁻¹*y i) + if b then θ.val (((n : ℝ)^h)⁻¹*(y i)⁻¹) else 0)
    let K := fun y => p.val.1⁻¹*(p.val.1*F y-Real.log
      (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,z)).toReal))
    let N := ((n : ℕ)+m).succPNat
    let hn : (n : ℕ) ≤ (N : ℕ) := by simp only [N,Nat.succPNat_coe]; omega
    let A := conditionalIntervalWeight p n m n.pos (Equiv.refl _) x
    paperFrozenPhysicalMatrix p n m U θ h b D x = hessianMatrix K x.val ∧
    paperFrozenInteriorMatrix p n m U θ h b D x = hessianMatrix F x.val +
      (IntervalBoundary.intervalMatrix N n hn A-IntervalBoundary.boundaryMatrix N n hn A) := by
  classical
  intro F K N hn A
  constructor
  · simp only [paperFrozenPhysicalMatrix,ite_eq_left hx,K,F]
  · have he := physical_boundary_eq_sub p n m n.pos hn x
    simp only [paperFrozenInteriorMatrix,ite_eq_left hx]
    congr 1
    exact eq_sub_of_add_eq (IntervalBoundary.internal_add_boundary N n hn A)

/-- Independence of the ambient realization for the two matrices of
equation (4.13). Their only use of it is the invariant paper event. -/
theorem paperFrozenMatrices_extension_eq (p : Parameters) (n : ℕ+) (m : ℕ)
    (U W : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ)
    (he : ∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) //
      y ∈ gapAmbientDomain ((n : ℕ)+m).succPNat}, U y.val = W y.val)
    (θ : PhysicalCutoff) (h : ℝ) (b : Bool) (D : ℝ) :
    paperFrozenPhysicalMatrix p n m U θ h b D = paperFrozenPhysicalMatrix p n m W θ h b D ∧
    paperFrozenInteriorMatrix p n m U θ h b D = paperFrozenInteriorMatrix p n m W θ h b D := by
  have hevent := paperProperGoodEvent_extension_eq p n m U W he h D
  constructor <;> funext x <;> dsimp only [paperFrozenPhysicalMatrix,paperFrozenInteriorMatrix] <;> rw [hevent]

/-- Row and column sums used after equation (4.13) and in the
proof of Lemma 4.9, summed from the boundary profile. -/
theorem paper_boundary_schur_bounds (p : Parameters) (hs : 1 < p.val.2)
    (n : ℕ+) (m : ℕ) (U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ)
    (h D : ℝ) (hD : 0 ≤ D) (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1))
    (hx : x ∈ paperProperGoodEvent p n m U h D) :
    let B := IntervalBoundary.boundaryMatrix ((n : ℕ)+m).succPNat n (by simp; omega)
      (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
    let C := D*(2*∑' k : ℕ, (1+(k : ℝ))^(-p.val.2))
    (∀ i, ∑ j, |B i j| ≤ C) ∧ (∀ j, ∑ i, |B i j| ≤ C) := by
  classical
  intro B C
  have hleft : (∑ i : Fin (n : ℕ), (1+(i.val : ℝ))^(-p.val.2)) ≤
      ∑' k : ℕ, (1+(k : ℝ))^(-p.val.2) := by
    exact (Fin.sum_univ_eq_sum_range (fun k : ℕ => (1+(k : ℝ))^(-p.val.2)) n).trans_le
      ((summable_one_add_rpow_neg hs).sum_le_tsum _ (fun k _ => by positivity))
  have hright : (∑ i : Fin (n : ℕ), (((n : ℕ)-i.val : ℕ) : ℝ)^(-p.val.2)) =
      ∑ i : Fin (n : ℕ), (1+(i.val : ℝ))^(-p.val.2) := by
    rw [← (Equiv.sum_comp (Fin.revPerm (n := (n : ℕ))))
      (fun i : Fin (n : ℕ) => (1+(i.val : ℝ))^(-p.val.2))]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    have hi : (n : ℕ)-i.val = (Fin.rev i).val+1 := by simp only [Fin.val_rev]; omega
    rw [hi,Nat.cast_add,Nat.cast_one,add_comm,Fin.revPerm_apply]
  have hcol (j : Fin (n : ℕ)) : ∑ i, |B i j| ≤ C := by
    have hp (i : Fin (n : ℕ)) : paperBoundaryProfile p.val.2 i j ≤
        (1+(i.val : ℝ))^(-p.val.2)+(((n : ℕ)-i.val : ℕ) : ℝ)^(-p.val.2) := by
      unfold paperBoundaryProfile
      apply add_le_add
      · have hi : (i.val+1 : ℕ) ≤ max (i.val+1) (j.val+1) := le_max_left _ _
        have hi' : 1+(i.val : ℝ) ≤ (max (i.val+1) (j.val+1) : ℕ) := by
          simpa only [Nat.cast_add,Nat.cast_one,add_comm] using (Nat.cast_le (α := ℝ)).mpr hi
        exact Real.rpow_le_rpow_of_nonpos (by positivity) hi' (by linarith)
      · have hi : (n : ℕ)-i.val ≤ (n : ℕ)-min i.val j.val := Nat.sub_le_sub_left (min_le_left _ _) _
        exact Real.rpow_le_rpow_of_nonpos
          (by exact_mod_cast (show 0 < (n : ℕ)-i.val by have := i.isLt; omega))
          (by exact_mod_cast hi) (by linarith)
    calc
      _ ≤ ∑ i : Fin (n : ℕ), D*((1+(i.val : ℝ))^(-p.val.2)+(((n : ℕ)-i.val : ℕ) : ℝ)^(-p.val.2)) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_of_nonneg (IntervalBoundary.boundaryMatrix_nonneg ((n : ℕ)+m).succPNat n (by simp; omega)
          (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
          (conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x) i j)]
        exact (hx.2.2.2.1 i j).trans (mul_le_mul_of_nonneg_left (hp i) hD)
      _ = D*(2*∑ i : Fin (n : ℕ), (1+(i.val : ℝ))^(-p.val.2)) := by
        rw [← Finset.mul_sum,Finset.sum_add_distrib,hright]
        ring
      _ ≤ C := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hleft (by norm_num)) hD
  refine ⟨fun i => ?_,hcol⟩
  have he : (∑ j, |B i j|) = ∑ j, |B j i| := by
    apply Finset.sum_congr rfl
    intro j _
    rw [show B i j = B j i from IntervalBoundary.boundaryMatrix_symm _ _ _ _ i j]
  rw [he]
  exact hcol i

/-- Interior-column bound obtained directly from equation (4.10),
as used in Lemma 4.9. -/
theorem paper_boundary_bulk_entries (p : Parameters) (hs : 1 < p.val.2)
    (n : ℕ+) (m : ℕ) (U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ)
    (h D : ℝ) (hD : 0 ≤ D) (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1))
    (hx : x ∈ paperProperGoodEvent p n m U h D) (i j : Fin (n : ℕ))
    (hj : (n : ℝ)/8 ≤ (ConditionalScores.boundaryDistance j : ℝ)) :
    IntervalBoundary.boundaryMatrix ((n : ℕ)+m).succPNat n (by simp; omega)
      (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x) i j ≤
      (2*(8 : ℝ)^p.val.2)*D*(n : ℝ)^(-p.val.2) := by
  have hn0 : (0 : ℝ) < n := by positivity
  have h₁ : (n : ℝ)/8 ≤ (max (i.val+1) (j.val+1) : ℕ) := by
    apply hj.trans
    exact_mod_cast (show ConditionalScores.boundaryDistance j ≤ max (i.val+1) (j.val+1) from
      (min_le_left _ _).trans (le_max_right _ _))
  have h₂ : (n : ℝ)/8 ≤ ((n : ℕ)-min i.val j.val : ℕ) := by
    apply hj.trans
    exact_mod_cast (show ConditionalScores.boundaryDistance j ≤ (n : ℕ)-min i.val j.val from
      (min_le_right _ _).trans (Nat.sub_le_sub_left (min_le_right _ _) _))
  have hp : paperBoundaryProfile p.val.2 i j ≤ 2*((n : ℝ)/8)^(-p.val.2) := by
    unfold paperBoundaryProfile
    have hp₁ := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (n : ℝ)/8) h₁ (by linarith : -p.val.2 ≤ 0)
    have hp₂ := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (n : ℝ)/8) h₂ (by linarith : -p.val.2 ≤ 0)
    linarith
  apply (hx.2.2.2.1 i j).trans
  apply (mul_le_mul_of_nonneg_left hp hD).trans_eq
  rw [Real.div_rpow hn0.le (by norm_num),Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8),div_inv_eq_mul]
  ring

end Riesz2.DecayShort
