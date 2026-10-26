/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.ExceptionalEventPart4
import all Riesz2.DecayShort.ExceptionalEventPart4
public import Riesz2.DecayShort.ConditionalScoresPart3
public import Riesz2.DecayShort.OptimalDecay
public import Riesz2.ToMathlib.IntervalMatrixComparison
public import Riesz2.ToMathlib.CommonScalarResolventComparison

/-!
# Auxiliary physical matrix comparison

The auxiliary coefficients of Subsection 4.5 use the finer coefficient
event and the physical marginal Hessian. On the exceptional set
the prescribed auxiliary value is the identity matrix.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal ContDiff

namespace Riesz2.DecayShort.PhysicalComparison

/-- See Subsection 4.5 of the paper: the physical auxiliary matrix, on the entire
positive retained carrier. The potential is the exact negative logarithm
of the penalized marginal density, divided by beta, as in Lemma 4.7. -/
def frozenPhysicalMatrix (p : Parameters) (n : ℕ+) (m : ℕ)
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
  exact if x ∈ ExceptionalEvent.properGoodEvent p n m (by simp only [Nat.succPNat_coe]; omega) h D
    then hessianMatrix K x.val else 1

/-- See Subsection 4.5 of the paper: the auxiliary internal matrix, formed from
the same conditional interval weights and the actual active penalty. -/
def frozenInternalMatrix (p : Parameters) (n : ℕ+) (m : ℕ)
    (θ : PhysicalCutoff) (h : ℝ) (b : Bool) (D : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ := by
  classical
  let F := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
    ∑ i, (θ.val (((n : ℝ) ^ h)⁻¹ * y i) +
      if b then θ.val (((n : ℝ) ^ h)⁻¹ * (y i)⁻¹) else 0)
  exact if x ∈ ExceptionalEvent.properGoodEvent p n m (by simp only [Nat.succPNat_coe]; omega) h D
    then hessianMatrix F x.val + IntervalBoundary.internalMatrix
      ((n : ℕ) + m).succPNat n (by simp only [Nat.succPNat_coe]; omega)
        (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
    else 1

/-- Both auxiliary matrices have exactly the prescribed value away
from the good event (Subsection 4.5). -/
theorem frozenMatrices_off_event (p : Parameters) (n : ℕ+) (m : ℕ)
    (θ : PhysicalCutoff) (h : ℝ) (b : Bool) (D : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (hx : x ∉ ExceptionalEvent.properGoodEvent p n m (by simp only [Nat.succPNat_coe]; omega) h D) :
    frozenPhysicalMatrix p n m θ h b D x = 1 ∧
      frozenInternalMatrix p n m θ h b D x = 1 := by
  simp only [frozenPhysicalMatrix, frozenInternalMatrix, ite_eq_right hx, and_self]

/-- Internal domination step for Subsection 4.5. Both retained
submatrices preserve positivity and the complete coefficient profile. -/
theorem internal_interval_domination (p : Parameters) (n : ℕ+) (m : ℕ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    let N := ((n : ℕ) + m).succPNat
    let hn : (n : ℕ) ≤ (N : ℕ) := by change (n : ℕ) ≤ (n : ℕ) + m + 1; omega
    let A := conditionalIntervalWeight p n m n.pos (Equiv.refl _) x
    (IntervalBoundary.internalMatrix N n hn A).PosSemidef ∧
      (IntervalBoundary.boundaryMatrix N n hn A).PosSemidef ∧
      ∀ i j : Fin (n : ℕ),
        0 ≤ IntervalBoundary.internalMatrix N n hn A i j ∧
        IntervalBoundary.internalMatrix N n hn A i j ≤ IntervalBoundary.intervalMatrix N n hn A i j ∧
        0 ≤ IntervalBoundary.boundaryMatrix N n hn A i j ∧
        IntervalBoundary.boundaryMatrix N n hn A i j ≤ IntervalBoundary.intervalMatrix N n hn A i j := by
  intro N hn A
  have hA := conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x
  exact ⟨IntervalBoundary.internalMatrix_posSemidef N n hn A hA,
    IntervalBoundary.boundaryMatrix_posSemidef N n hn A hA, fun i j =>
      ⟨IntervalBoundary.internalMatrix_nonneg N n hn A hA i j,
       IntervalBoundary.internalMatrix_le_intervalMatrix N n hn A hA i j,
       IntervalBoundary.boundaryMatrix_nonneg N n hn A hA i j,
       IntervalBoundary.boundaryMatrix_le_intervalMatrix N n hn A hA i j⟩⟩

/-- Row and column clauses of Subsection 4.5, with an explicit
size-independent Schur constant. These are pointwise estimates on the
physical good event, so they remain valid on every fixed-length fibre. -/
theorem boundary_schur_bounds (p : Parameters) (hs : 1 < p.val.2)
    (n : ℕ+) (m : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (hx : x ∈ ExceptionalEvent.coefficientEvent p n m (by simp only [Nat.succPNat_coe]; omega) D) :
    let N := ((n : ℕ) + m).succPNat
    let hn : (n : ℕ) ≤ (N : ℕ) := by change (n : ℕ) ≤ (n : ℕ) + m + 1; omega
    let B := IntervalBoundary.boundaryMatrix N n hn
      (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
    let C := D * (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-p.val.2))
    (∀ i, ∑ j, |B i j| ≤ C) ∧ (∀ j, ∑ i, |B i j| ≤ C) := by
  classical
  intro N hn B C
  let g : ComponentGeometry (Fin (n : ℕ)) := Sum.inr ⟨N, Fin.castLEEmb hn⟩
  have hd (i j : Fin (n : ℕ)) : componentDistance g i j =
      (Riesz1.cyclicIndexDistance N (Fin.castLE hn i) (Fin.castLE hn j) : ℝ) := rfl
  have hA := conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x
  have hb (i j : Fin (n : ℕ)) : |B i j| ≤ D * (1 + componentDistance g i j) ^ (-p.val.2) := by
    rw [abs_of_nonneg (IntervalBoundary.boundaryMatrix_nonneg N n hn _ hA i j), hd]
    exact (IntervalBoundary.boundaryMatrix_le_intervalMatrix N n hn _ hA i j).trans (hx.1 i j)
  have hr (i : Fin (n : ℕ)) : ∑ j, |B i j| ≤ C := by
    calc
      _ ≤ ∑ j, D * (1 + componentDistance g i j) ^ (-p.val.2) :=
        Finset.sum_le_sum fun j _ => hb i j
      _ = D * ∑ j, (1 + componentDistance g i j) ^ (-p.val.2) := (Finset.mul_sum ..).symm
      _ ≤ C := mul_le_mul_of_nonneg_left (ComponentGeometryBounds.sum_power_le g i hs) hD
  refine ⟨hr, fun j => ?_⟩
  calc
    _ = ∑ i, |B j i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show B i j = B j i from IntervalBoundary.boundaryMatrix_symm N n hn _ i j]
    _ ≤ C := hr j

/-- Interior-column clause of Subsection 4.5. The constant is
explicit and independent of the ambient size and of the fibre length. -/
theorem boundary_bulk_entries (p : Parameters) (hs : 1 < p.val.2)
    (n : ℕ+) (m : ℕ) (hhalf : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (D : ℝ) (hD : 0 ≤ D)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (hx : x ∈ ExceptionalEvent.coefficientEvent p n m (by simp only [Nat.succPNat_coe]; omega) D)
    (i j : Fin (n : ℕ))
    (hj : (n : ℝ) / 8 ≤ (ConditionalScores.boundaryDistance j : ℝ)) :
    IntervalBoundary.boundaryMatrix ((n : ℕ) + m).succPNat n (by simp only [Nat.succPNat_coe]; omega)
      (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x) i j ≤
        (2 * (8 : ℝ) ^ (p.val.2 + 1) + 1) * D * (n : ℝ) ^ (-p.val.2) := by
  apply IntervalBoundary.boundaryMatrix_bulk_entry_le _ _ _ _ n.pos
    (by simpa only [Nat.succPNat_coe] using hhalf) (by linarith) hD
      (fun k hk => by
        obtain ⟨hk1,hkn⟩ := Finset.mem_Ico.mp hk
        have hk' : k - 1 + 1 = k := by omega
        simpa only [hk'] using hx.2.1 ⟨k - 1, by omega⟩)
      (fun k hk => by
        obtain ⟨hk1,hkn⟩ := Finset.mem_Ico.mp hk
        have hk' : k - 1 + 1 = k := by omega
        simpa only [hk'] using hx.2.2.1 ⟨k - 1, by omega⟩)
      hx.2.2.2.1 i j hj

/-- Lower quadratic-form clause for the physical auxiliary matrix in
Subsection 4.5. It holds on its entire carrier, including the
exceptional set, with no probability or fibre hypothesis. -/
theorem frozenPhysicalMatrix_lower (p : Parameters) (hs : 1 < p.val.2)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (h : ℝ) (hh : 0 < h)
    (b : Bool) (D : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (z : Fin (n : ℕ) → ℝ) :
    (n : ℝ) ^ (-(p.val.2 + 2) * h) * (∑ i, z i ^ 2) ≤
      ∑ i, ∑ j, z i * frozenPhysicalMatrix p n m θ h b D x i j * z j := by
  classical
  let F := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
    ∑ i, (θ.val (((n : ℝ) ^ h)⁻¹ * y i) +
      if b then θ.val (((n : ℝ) ^ h)⁻¹ * (y i)⁻¹) else 0)
  let K := fun y => p.val.1⁻¹ * (p.val.1 * F y -
    Real.log (∫ w : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,w)).toReal))
  by_cases hx : x ∈ ExceptionalEvent.properGoodEvent p n m (by simp only [Nat.succPNat_coe]; omega) h D
  · have hK := PhysicalFibres.active_marginal_curvature p hs n m n.pos (Equiv.refl _) θ h hh b
    have hKx : ContDiffAt ℝ 2 K x.val := (hK.1.of_le (by norm_num)).contDiffAt
      ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds x.property)
    have hbound := hK.2 x.val x.property (WithLp.toLp 2 z)
    have hquad := PhysicalEnergy.hessianMatrix_quadratic hKx (WithLp.toLp 2 z)
    simp only [EuclideanSpace.real_norm_sq_eq] at hbound
    change _ ≤ ∑ i, ∑ j, z i * (if x ∈ ExceptionalEvent.properGoodEvent p n m
      (by simp only [Nat.succPNat_coe]; omega) h D then hessianMatrix K x.val else 1) i j * z j
    rw [ite_eq_left hx]
    exact hbound.trans_eq hquad.symm
  · rw [(frozenMatrices_off_event p n m θ h b D x hx).1]
    simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← sq]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
    have hpow : (n : ℝ) ^ (-(p.val.2 + 2) * h) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hn1 (by nlinarith [p.property.2.1])
    exact mul_le_of_le_one_left (Finset.sum_nonneg fun i _ => sq_nonneg _) hpow

set_option backward.isDefEq.respectTransparency false in
/-- Singleton curvatures are retained by the actual conditional internal
matrix. No conditional expectation is replaced by a chosen representative. -/
theorem internal_singleton_coefficient_lower (p : Parameters) (n : ℕ+) (m : ℕ)
    (hN : 2 ≤ (n : ℕ) + m + 1)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (i : Fin (n : ℕ)) :
    p.val.2 * (p.val.2 + 1) * (x.val i) ^ (-p.val.2 - 2) ≤
      conditionalIntervalWeight p n m n.pos (Equiv.refl _) x
        (Fin.castLE (by omega) i, ⟨0, by simpa only [Nat.succPNat_coe] using Nat.div_pos hN (by norm_num : 0 < 2)⟩) := by
  classical
  let t : Fin (((n : ℕ) + m).succPNat : ℕ) × Fin ((((n : ℕ) + m).succPNat : ℕ) / 2) :=
    (Fin.castLE (by change (n : ℕ) ≤ (n : ℕ) + m + 1; omega) i, ⟨0, by simpa only [Nat.succPNat_coe] using Nat.div_pos hN (by norm_num : 0 < 2)⟩)
  let μ := PhysicalFibres.measure p n m n.pos (Equiv.refl _) x
  let : IsProbabilityMeasure μ := PhysicalFibres.measure_probability p n m n.pos (Equiv.refl _) x
  have hc (z) :
      p.val.2 * (p.val.2 + 1) * (x.val i) ^ (-p.val.2 - 2) ≤
        intervalWeight p ((n : ℕ) + m).succPNat t (PhysicalFibres.configuration n m (Equiv.refl _) x z) := by
    let y := PhysicalFibres.configuration n m (Equiv.refl _) x z
    have hy : y.val (Fin.castLE (by omega) i) = x.val i := by
      change RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z.val)
        ((i.castAdd m).castSucc) = _
      exact RetainedSimplex.chart_retained n m _ (Equiv.refl _) x.val z.val i
    have hl := PhysicalEnergy.intervalCoefficient_lower p ((n : ℕ) + m).succPNat
      ⟨cyclicGapSum ((n : ℕ) + m).succPNat t.1 (t.2.val + 1) (WithLp.ofLp y.val),
        y.property t.1 _ (by omega) (by have := t.2.isLt; omega)⟩
    change _ ≤ (2 - if 2 * (t.2.val + 1) = (((n : ℕ) + m).succPNat : ℕ) then (1 : ℝ) else 0) *
      PhysicalEnergy.intervalCoefficient p ((n : ℕ) + m).succPNat _
    apply le_trans _ (le_mul_of_one_le_left (PhysicalEnergy.intervalCoefficient_pos p ((n : ℕ) + m).succPNat _).le
      (by split_ifs <;> norm_num))
    convert hl using 1
    simp only [t, Nat.zero_add, PhysicalEnergy.gapSum_one, hy]
  have hm := integral_mono_ae (μ := μ) (integrable_const _)
    (integrable_intervalWeight p n m n.pos (Equiv.refl _) x t) (ae_of_all μ hc)
  simpa [conditionalIntervalWeight, μ, t] using hm

/-- Lower quadratic-form clause for the internal auxiliary matrix in
Subsection 4.5. On the good event, singleton curvatures suffice. On its complement the prescribed identity gives the same lower bound. -/
theorem frozenInternalMatrix_lower (p : Parameters) (hs : 1 < p.val.2)
    (n : ℕ+) (m : ℕ) (hN : 2 ≤ (n : ℕ) + m + 1)
    (θ : PhysicalCutoff) (h : ℝ) (hh : 0 < h) (b : Bool) (D : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (z : Fin (n : ℕ) → ℝ) :
    (n : ℝ) ^ (-(p.val.2 + 2) * h) * (∑ i, z i ^ 2) ≤
      ∑ i, ∑ j, z i * frozenInternalMatrix p n m θ h b D x i j * z j := by
  classical
  let F := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
    ∑ i, (θ.val (((n : ℝ) ^ h)⁻¹ * y i) +
      if b then θ.val (((n : ℝ) ^ h)⁻¹ * (y i)⁻¹) else 0)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  by_cases hx : x ∈ ExceptionalEvent.properGoodEvent p n m (by simp only [Nat.succPNat_coe]; omega) h D
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
      change _ ≤ ∑ i, ∑ j, z i * (if x ∈ ExceptionalEvent.properGoodEvent p n m
        (by simp only [Nat.succPNat_coe]; omega) h D then hessianMatrix F x.val + _ else 1) i j * z j
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
  · rw [(frozenMatrices_off_event p n m θ h b D x hx).2]
    simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← sq]
    exact mul_le_of_le_one_left (Finset.sum_nonneg fun i _ => sq_nonneg _) <|
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast n.pos)
        (by nlinarith [p.property.2.1])

end Riesz2.DecayShort.PhysicalComparison
