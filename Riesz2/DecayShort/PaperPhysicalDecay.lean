/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.PhysicalDecayPart5
import all Riesz2.DecayShort.PhysicalDecayPart4

/-!
# Tilt-scale coercivity for the full short-range equation

The full-cycle step in the paper's Proposition 4.10 uses
nearest-pair curvature together with the upper tilt at every gap. The bound
below retains that scale for every realization of the physical potential.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology ContDiff

namespace Riesz2.DecayShort.PhysicalDecay

set_option backward.isDefEq.respectTransparency false in
/-- The full tilted coercivity used in the proof of the paper's
Proposition 4.10. The temperature-weighted ambient Hessian is bounded
below by `β N^(-(s+2)h)` in every direction, for either active penalty.
The result applies to every realization of the physical value. -/
theorem full_physical_matrix_lower_scaled (p : Parameters) (hs : 1 < p.val.2)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (θ : PhysicalCutoff)
    (h : ℝ) (hh : 0 < h) (b : Bool)
    (W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ)
    (hval : ∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
      W y.val = fullPhysicalPotentialValue p N hN θ h b y) :
    ∀ z ∈ intrinsicGapDomain N, ∀ t : Fin (N : ℕ) → ℝ,
      (p.val.1 * (N : ℝ) ^ (-(p.val.2 + 2) * h)) * (∑ i, t i ^ 2) ≤
        ∑ i, ∑ j, t i * hessianMatrix W
          (WithLp.toLp 2 (fun i => 1 + z.val i)) i j * t j := by
  classical
  let R : {R : ℝ // 0 < R} := ⟨(N : ℝ) ^ h, by positivity⟩
  have hR : 1 ≤ (R : ℝ) := Real.one_le_rpow (by exact_mod_cast N.pos) hh.le
  obtain ⟨V,hV,hv,hcurv⟩ := upperGapPenalty_curvature p hs N hN θ R hR Finset.univ
  let a := (N : ℝ) ^ (-h)
  have ha : 0 < a := by dsimp only [a]; positivity
  let U := fun y : EuclideanSpace ℝ (Fin (N : ℕ)) =>
    V y + ∑ i, θ.val (a * y i)
  let I := fun y : EuclideanSpace ℝ (Fin (N : ℕ)) => ∑ i, θ.val (a * (y i)⁻¹)
  intro z hz t
  let x := WithLp.toLp 2 (fun i => 1 + z.val i)
  let u := WithLp.toLp 2 t
  have hy := PhysicalCollision.intrinsic_chart_mem_simplex N hz
  have hx : x ∈ gapAmbientDomain N := PhysicalEnergy.simplex_subset_ambient N _ hy
  have hpos (i) : 0 < x i := hz i
  have hRinv : (R : ℝ)⁻¹ = a := Real.rpow_neg (by positivity : (0 : ℝ) ≤ N) h |>.symm
  have hU : ContDiffAt ℝ 2 U x := by
    apply ((hV.of_le (by norm_num)).contDiffAt
      ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hx)).add
    simpa only [U, div_eq_mul_inv, hRinv, mul_comm] using
      upperGapPenalty_contDiffAt θ R Finset.univ x hpos
  have hIdata := PhysicalFibres.inverse_retained_penalty (N : ℕ) ((∑ i, x i) + 1) θ ha
  have hIx : x ∈ AffineSimplex.chartDomain (N : ℕ) ((∑ i, x i) + 1) := ⟨hpos, by linarith⟩
  have hI : ContDiffAt ℝ 2 I x := (hIdata.1.of_le (by norm_num)).contDiffAt
    ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds hIx)
  have hIpos : 0 ≤ fderiv ℝ (fderiv ℝ I) x u u :=
    Riesz1.fderiv_fderiv_nonneg_of_convexOn
      (AffineSimplex.isOpen_chartDomain _ _) (AffineSimplex.convex_chartDomain _ _)
      hIdata.2 (hIdata.1.of_le (by norm_num)) hIx u
  have hbase : (N : ℝ) ^ (-(p.val.2 + 2) * h) * (∑ i, t i ^ 2) ≤
      fderiv ℝ (fderiv ℝ U) x u u := by
    have hc := hcurv (fun i => 1 + z.val i) hy u
    have hpower : (R : ℝ) ^ (-p.val.2 - 2) = (N : ℝ) ^ (-(p.val.2 + 2) * h) := by
      dsimp only [R]
      rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ N)]
      congr 1
      ring
    simpa only [hpower, div_eq_mul_inv, hRinv, mul_comm] using hc
  have he : W =ᶠ[𝓝 x] (fun y => p.val.1 * (U y + if b then I y else 0)) := by
    filter_upwards [(PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hx] with y hy
    rw [hval ⟨y,hy⟩]
    dsimp only [fullPhysicalPotentialValue, U, I, a]
    rw [hv ⟨y,hy⟩]
    cases b <;> simp only [↓reduceIte, Bool.false_eq_true, add_zero, Finset.sum_add_distrib,
      add_assoc]
  have hdiff : ContDiffAt ℝ 2 (fun y => p.val.1 * (U y + if b then I y else 0)) x := by
    cases b
    · simpa only [Bool.false_eq_true, ↓reduceIte, add_zero] using contDiffAt_const.mul hU
    · simpa only [↓reduceIte] using contDiffAt_const.mul (hU.add hI)
  have hW : ContDiffAt ℝ 2 W x := hdiff.congr_of_eventuallyEq he
  rw [show (∑ i, ∑ j, t i * hessianMatrix W x i j * t j) =
    fderiv ℝ (fderiv ℝ W) x u u from PhysicalEnergy.hessianMatrix_quadratic hW u,
    he.fderiv.fderiv_eq]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
    rw [PhysicalCollision.internal_hessian_const_mul hU]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbase p.property.1.le
  · simp only [↓reduceIte]
    rw [PhysicalCollision.internal_hessian_const_mul (hU.add hI),
      PhysicalCollision.internal_hessian_add hU hI]
    simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left hbase p.property.1.le).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hIpos) p.property.1.le)

end Riesz2.DecayShort.PhysicalDecay
