/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.PhysicalCorePart6
public import Riesz2.DecayLong.PhysicalIdentityPart6

/-!
# Full-cycle physical matrix bounds

Full-cycle matrix bounds and the combined proper-window and full-cycle
conclusion in the proof of Lemma 5.4. The field, good event, reference and
forcing are the physical objects of Subsection 5.1.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped BigOperators Classical MatrixOrder

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.PhysicalCore

namespace Internal

/-- The summand of the existing ambient `GoodBlocks.gapHessian`, including
its antipodal multiplicity. This differential expression is defined on the
whole ambient space. The lemma `fullCoefficient_simplex` identifies its physical value. -/
def fullCoefficient (s : Riesz1.RieszExponent) (N : ℕ+)
    (i : Fin (N : ℕ)) (r : Fin ((N : ℕ)/2))
    (y : EuclideanSpace ℝ (Fin (N : ℕ))) : ℝ :=
  (2 - if 2*(r.val+1) = (N : ℕ) then (1 : ℝ) else 0) *
    ((N : ℝ)^(-s.val-2) *
      iteratedDeriv 2 (fun t : ℝ => Riesz1.rieszRepresentative s t)
        (cyclicGapSum N i (r.val+1) (WithLp.ofLp y)/(N : ℝ)))

/-- The differential coefficient is literally the physical interval weight
on the positive mass simplex (Subsection 5.1). -/
theorem fullCoefficient_simplex (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (i : Fin (N : ℕ)) (r : Fin ((N : ℕ)/2))
    (y : EuclideanSpace ℝ (Fin (N : ℕ))) (hy : WithLp.ofLp y ∈ Riesz1.gapSimplex N) :
    fullCoefficient s N i r y =
      (2 - if 2*(r.val+1) = (N : ℕ) then (1 : ℝ) else 0) *
        PhysicalEnergy.intervalCoefficient (ofLong β s) N
          ⟨cyclicGapSum N i (r.val+1) (WithLp.ofLp y),
            PhysicalEnergy.gapSum_mem N i (by omega) (by have := r.isLt; omega) _ hy⟩ := by
  simp only [fullCoefficient,PhysicalEnergy.intervalCoefficient,PhysicalEnergy.kernelDerivative,
    ofLong,s.property.2,↓reduceDIte,PhysicalEnergy.scaledSeparation,PNat.val_ofNat]

theorem measurable_fullCoefficient (s : Riesz1.RieszExponent) (N : ℕ+)
    (i : Fin (N : ℕ)) (r : Fin ((N : ℕ)/2)) : Measurable (fullCoefficient s N i r) := by
  unfold fullCoefficient
  apply Measurable.const_mul
  apply Measurable.const_mul
  simp only [iteratedDeriv_succ,iteratedDeriv_zero]
  apply (measurable_deriv (deriv (fun t : ℝ => Riesz1.rieszRepresentative s t))).comp
  simpa only [PhysicalEnergy.intervalLinear_apply] using
    ((PhysicalEnergy.intervalLinear N i (r.val+1)).continuous.div_const (N : ℝ)).measurable

/-- Lemma 5.4 of the paper: full-cycle endpoint bounds by the written
cutoff split. Short intervals have mass at most `N^(1/4)`. Above the cutoff
rigidity gives `r/2 ≤ L ≤ 3r/2`. -/
theorem full_gap_endpoints_paper (s : Riesz1.RieszExponent) (N : ℕ+)
    (ε κ₀ : ℝ) (hε : 0 ≤ ε) (hsmall : ε ≤ paperCutoffThreshold s)
    (hlarge : 8 ≤ (N : ℝ) ^ ε) (y : EuclideanSpace ℝ (Fin (N : ℕ)))
    (hy : y ∈ fullGapGoodSet s N ε κ₀)
    (i : Fin (N : ℕ)) (r : Fin ((N : ℕ) / 2)) :
    let L := cyclicGapSum N i (r.val + 1) (WithLp.ofLp y)
    (N : ℝ) ^ (-ε) * (r.val + 1 : ℝ) ≤ L ∧
      (N : ℝ) ^ (-ε) * (r.val + 1 : ℝ) ≤ (N : ℝ) - L := by
  let R : ℝ := r.val + 1
  let L := cyclicGapSum N i (r.val + 1) (WithLp.ofLp y)
  have hn0 : (0 : ℝ) < N := by positivity
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hR0 : 0 < R := by dsimp only [R]; positivity
  have hRN : 2 * R ≤ (N : ℝ) := by dsimp only [R]; exact_mod_cast (by have := r.isLt; omega : 2 * (r.val + 1) ≤ (N : ℕ))
  have ha : (N : ℝ) ^ (-ε) ≤ 1 / 2 := by
    rw [Real.rpow_neg hn0.le]
    exact inv_le_of_inv_le₀ (by norm_num) (by norm_num at *; linarith)
  have hgap := PhysicalEnergy.gapSum_bounds N i (r.val + 1) (WithLp.ofLp y) hy.2.1.1
  constructor
  · simpa only [L, R, Nat.cast_add, Nat.cast_one] using hgap.1
  · change (N : ℝ) ^ (-ε) * R ≤ (N : ℝ) - L
    by_cases hr : r.val + 1 < ⌊(N : ℝ) ^ ε⌋₊ ^ (paperReferenceCutoffExponent s : ℕ)
    · have hm := paper_cutoff_short_mass s N hε hsmall hr
      have hL : L ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
        apply hgap.2.trans
        simpa only [mul_comm] using hm.1.trans hm.2
      have hq : (N : ℝ) ^ ε ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le hn1
        have hd : 0 < 4 * ((paperReferenceCutoffExponent s : ℝ) + 1) := by positivity
        change ε ≤ 1 / (4 * ((paperReferenceCutoffExponent s : ℝ) + 1)) at hsmall
        have hh := (le_div_iff₀ hd).mp hsmall
        have hm0 : 0 ≤ (paperReferenceCutoffExponent s : ℝ) := by positivity
        nlinarith
      have hN4 : (4 : ℝ) ≤ N := by
        have hh := Real.rpow_le_self_of_one_le hn1 (by norm_num : (1 / 4 : ℝ) ≤ 1)
        linarith
      have hhalf : (2 : ℝ) ≤ (N : ℝ) ^ (3 / 4 : ℝ) := by
        have hh := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 4) hN4
          (by norm_num : (0 : ℝ) ≤ 1 / 2)
        have he : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by rw [← Real.sqrt_eq_rpow]; norm_num
        rw [he] at hh
        exact hh.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num))
      have he : (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (3 / 4 : ℝ) = (N : ℝ) := by
        rw [← Real.rpow_add hn0]
        norm_num
      have hh := mul_le_mul_of_nonneg_left hhalf (Real.rpow_nonneg hn0.le (1 / 4 : ℝ))
      rw [he] at hh
      have hhR := mul_le_mul_of_nonneg_right ha hR0.le
      linarith
    · have ht := paper_cutoff_taylor_condition s hlarge hR0
        (by dsimp only [R]; exact_mod_cast (by omega : ⌊(N : ℝ) ^ ε⌋₊ ^ (paperReferenceCutoffExponent s : ℕ) ≤ r.val + 1))
      have hd := hy.2.1.2 i ⟨r.val + 1, by have := r.isLt; omega⟩
        (by change 1 ≤ r.val + 1; omega) (by change r.val + 1 ≤ (N : ℕ) / 2; have := r.isLt; omega)
      have hL : L ≤ 3 / 2 * R := by
        change |L - ((r.val + 1 : ℕ) : ℝ)| ≤ _ at hd
        simp only [Nat.cast_add, Nat.cast_one] at hd
        change |L - R| ≤ (N : ℝ) ^ ε * R ^ (s.val / 2) at hd
        linarith [(abs_le.mp hd).2]
      have hh := mul_le_mul_of_nonneg_right ha hR0.le
      linarith

/-- Lemma 5.4 of the paper: the full-cycle coefficient upper bound
from the cutoff endpoint bounds and the positive image series. -/
theorem fullCoefficient_upper_paper (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (ε κ₀ : ℝ) (hε : 0 ≤ ε) (hsmall : ε ≤ paperCutoffThreshold s)
    (hlarge : 8 ≤ (N : ℝ) ^ ε) (y : EuclideanSpace ℝ (Fin (N : ℕ)))
    (hy : y ∈ fullGapGoodSet s N ε κ₀) (i : Fin (N : ℕ)) (r : Fin ((N : ℕ) / 2)) :
    fullCoefficient s N i r y ≤
      (2 * PhysicalEnergy.coefficientConstant s.val s.property.1) *
        (N : ℝ) ^ ((s.val + 2) * ε) * (r.val + 1 : ℝ) ^ (-s.val - 2) := by
  have hend := full_gap_endpoints_paper s N ε κ₀ hε hsmall hlarge y hy i r
  let L : {L : ℝ // 0 < L ∧ L < (N : ℝ)} :=
    ⟨cyclicGapSum N i (r.val + 1) (WithLp.ofLp y),
      PhysicalEnergy.gapSum_mem N i (by omega) (by have := r.isLt; omega) _ hy.1⟩
  have hu := PhysicalEnergy.intervalCoefficient_upper (ofLong β s) N L
    (mul_pos (Real.rpow_pos_of_pos (by positivity) (-ε))
      (by positivity : 0 < (r.val + 1 : ℝ))) hend.1 hend.2
  have hC : s.val * (s.val + 1) * PeriodicPower.bound (s.val + 2) (by linarith [s.property.1]) ≤
      PhysicalEnergy.coefficientConstant s.val s.property.1 := by
    unfold PhysicalEnergy.coefficientConstant
    have hs := s.property.1
    have hB := PeriodicPower.bound_pos (s.val + 3) (by linarith)
    have hh : 0 ≤ s.val * (s.val + 1) *
        (2 * (s.val + 2) * PeriodicPower.bound (s.val + 3) (by linarith [s.property.1])) *
        2 ^ (s.val + 3) := by positivity
    linarith
  change PhysicalEnergy.intervalCoefficient (ofLong β s) N L ≤
    s.val * (s.val + 1) * PeriodicPower.bound (s.val + 2) _ *
      ((N : ℝ) ^ (-ε) * (r.val + 1 : ℝ)) ^ (-s.val - 2) at hu
  rw [Real.mul_rpow (Real.rpow_nonneg (by positivity) _) (by positivity),
    ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ N),
    show -ε * (-s.val - 2) = (s.val + 2) * ε by ring] at hu
  have hu' := hu.trans (mul_le_mul_of_nonneg_right hC (mul_nonneg
    (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)))
  rw [fullCoefficient_simplex β s N i r y hy.1]
  have hw : (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) ≤ 2 := by split_ifs <;> norm_num
  have hc := (PhysicalEnergy.intervalCoefficient_pos (ofLong β s) N L).le
  exact (mul_le_mul_of_nonneg_right hw hc).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hu' (by norm_num : (0 : ℝ) ≤ 2))

/-- Full-cycle gap bounds control both ends of every short interval.
For the regime of Lemma 5.4 of the paper, the upper bound follows the
paper cutoff split. The unrestricted interface retains the gap bound. -/
theorem fullCoefficient_bounds (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (ε κ₀ : ℝ) (y : EuclideanSpace ℝ (Fin (N : ℕ)))
    (hy : y ∈ fullGapGoodSet s N ε κ₀) (i : Fin (N : ℕ)) (r : Fin ((N : ℕ)/2)) :
    s.val*(s.val+1)*(N : ℝ)^(-(s.val+2)*ε)*(r.val+1 : ℝ)^(-s.val-2) ≤
        fullCoefficient s N i r y ∧
    fullCoefficient s N i r y ≤
      (2*PhysicalEnergy.coefficientConstant s.val s.property.1)*
        (N : ℝ)^((s.val+2)*ε)*(r.val+1 : ℝ)^(-s.val-2) := by
  have h := PhysicalEnergy.coefficient_gap_bounds (ofLong β s) N i
    (r := r.val+1) (by omega) (by have := r.isLt; omega) _ hy.1
    (Real.rpow_pos_of_pos (by positivity) (-ε)) hy.2.1.1
  change s.val*(s.val+1)*((N : ℝ)^ε)^(-s.val-2)*
      ((r.val+1 : ℕ) : ℝ)^(-s.val-2) ≤ _ ∧
    _ ≤ PhysicalEnergy.coefficientConstant s.val s.property.1 *
      ((N : ℝ)^(-ε))^(-s.val-2)*((r.val+1 : ℕ) : ℝ)^(-s.val-2) at h
  have hp (a : ℝ) : ((N : ℝ)^a)^(-s.val-2) = (N : ℝ)^(a*(-s.val-2)) :=
    (Real.rpow_mul (by positivity) _ _).symm
  rw [hp ε,hp (-ε)] at h
  have he₁ : ε*(-s.val-2) = -(s.val+2)*ε := by ring
  have he₂ : -ε*(-s.val-2) = (s.val+2)*ε := by ring
  rw [he₁,he₂] at h
  rw [fullCoefficient_simplex β s N i r y hy.1]
  have hc := (PhysicalEnergy.intervalCoefficient_pos (ofLong β s) N
    ⟨cyclicGapSum N i (r.val+1) (WithLp.ofLp y),
      PhysicalEnergy.gapSum_mem N i (by omega) (by have := r.isLt; omega) _ hy.1⟩).le
  constructor
  · split_ifs <;> push_cast at h ⊢ <;> nlinarith only [h.1, hc]
  · by_cases hp : 0 ≤ ε ∧ ε ≤ paperCutoffThreshold s ∧ 8 ≤ (N : ℝ) ^ ε
    · simpa only [fullCoefficient_simplex β s N i r y hy.1] using
        fullCoefficient_upper_paper β s N ε κ₀ hp.1 hp.2.1 hp.2.2 y hy i r
    · split_ifs <;> push_cast at h ⊢ <;> nlinarith only [h.2, hc]

theorem fullCoefficient_nonneg (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (ε κ₀ : ℝ) (y : EuclideanSpace ℝ (Fin (N : ℕ)))
    (hy : y ∈ fullGapGoodSet s N ε κ₀) (i : Fin (N : ℕ)) (r : Fin ((N : ℕ)/2)) :
    0 ≤ fullCoefficient s N i r y :=
  (by have := s.property.1; positivity : 0 ≤ s.val*(s.val+1)*(N : ℝ)^(-(s.val+2)*ε)*
    (r.val+1 : ℝ)^(-s.val-2)).trans (fullCoefficient_bounds β s N ε κ₀ y hy i r).1

end Internal

/-- See Subsection 5.1 of the paper: the full field's actual interval weights.
On the good event these are physical weights with forcing at singletons.
On its complement they are the original reference weights. -/
def fullIntervalWeight (s : Riesz1.RieszExponent) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ)
    (i : Fin (N : ℕ)) (r : Fin ((N : ℕ)/2))
    (y : EuclideanSpace ℝ (Fin (N : ℕ))) : ℝ :=
  if y ∈ fullGapGoodSet s N ε κ₀ then
    Internal.fullCoefficient s N i r y +
      if r.val = 0 then forcingHessian N θ ε y i i else 0
  else BoundaryEntries.referenceWeight s N hN K (i,r)

theorem measurable_fullIntervalWeight (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ)
    (i : Fin (N : ℕ)) (r : Fin ((N : ℕ)/2)) :
    Measurable (fullIntervalWeight s N hN K θ ε κ₀ i r) := by
  unfold fullIntervalWeight
  apply Measurable.ite (measurableSet_fullGapGoodSet s N ε κ₀)
  · apply (Internal.measurable_fullCoefficient s N i r).add
    split_ifs
    · exact measurable_forcingHessian N θ ε i i
    · exact measurable_const
  · exact measurable_const

theorem fullIntervalWeight_nonneg (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ)
    (i : Fin (N : ℕ)) (r : Fin ((N : ℕ)/2)) (y : EuclideanSpace ℝ (Fin (N : ℕ))) :
    0 ≤ fullIntervalWeight s N hN K θ ε κ₀ i r y := by
  by_cases hy : y ∈ fullGapGoodSet s N ε κ₀
  · have hf := (forcingHessian_bound N 0 θ ε).choose_spec.2
      ⟨y,Internal.simplex_mem_forcing_chart N y hy.1⟩ i i
    simp only [fullIntervalWeight,ite_eq_left hy]
    apply add_nonneg (Internal.fullCoefficient_nonneg β s N ε κ₀ y hy i r)
    split_ifs
    · exact hf.1
    · exact le_rfl
  · simpa only [fullIntervalWeight,ite_eq_right hy] using
      BoundaryEntries.referenceWeight_nonneg s N hN K (i,r)

namespace Internal

/-- The forcing is exactly a sum over the singleton intervals, on a full cycle. -/
theorem full_forcing_singletons (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (θ : PhysicalCutoff)
    (ε : ℝ) (y : EuclideanSpace ℝ (Fin (N : ℕ)))
    (hy : WithLp.ofLp y ∈ Riesz1.gapSimplex N) (a b : Fin (N : ℕ)) :
    forcingHessian N θ ε y a b =
      ∑ i : Fin (N : ℕ), ∑ r : Fin ((N : ℕ)/2),
        (if r.val = 0 then forcingHessian N θ ε y i i else 0) *
          (if a ∈ cyclicIndexInterval N i (r.val+1) then 1 else 0) *
          (if b ∈ cyclicIndexInterval N i (r.val+1) then 1 else 0) := by
  let r₀ : Fin ((N : ℕ)/2) := ⟨0,by omega⟩
  have hs (i : Fin (N : ℕ)) : cyclicIndexInterval N i 1 = {i} := by
    simp only [cyclicIndexInterval,Finset.range_one,Finset.image_singleton,
      add_zero,Nat.mod_eq_of_lt i.isLt]
  have he (i : Fin (N : ℕ)) :
      (∑ r : Fin ((N : ℕ)/2), (if r.val = 0 then forcingHessian N θ ε y i i else 0) *
        (if a ∈ cyclicIndexInterval N i (r.val+1) then 1 else 0) *
        (if b ∈ cyclicIndexInterval N i (r.val+1) then 1 else 0)) =
      forcingHessian N θ ε y i i * (if a = i then 1 else 0) * (if b = i then 1 else 0) := by
    rw [Finset.sum_eq_single r₀]
    · simp only [r₀,ite_true,zero_add,hs,Finset.mem_singleton]
    · intro r _ hr
      have hr0 : r.val ≠ 0 := fun h => hr (Fin.ext h)
      simp only [ite_eq_right hr0,zero_mul]
    · simp only [Finset.mem_univ,not_true_eq_false,false_implies]
  simp_rw [he]
  rw [Finset.sum_eq_single a]
  · by_cases hab : a = b
    · subst b; simp only [ite_true,mul_one]
    · rw [forcingHessian_apply N 0 θ ε
        ⟨y,simplex_mem_forcing_chart N y hy⟩ a b,ite_eq_right hab]
      simp only [ite_true,mul_one,ite_eq_right (Ne.symm hab),mul_zero]
  · intro i _ hi
    simp only [ite_eq_right (Ne.symm hi),mul_zero,zero_mul]
  · simp only [Finset.mem_univ,not_true_eq_false,false_implies]

end Internal

/-- See the proof of Lemma 5.4 in the paper: the full matrix has exactly the physical
interval representation, including the forcing and antipodal intervals. -/
theorem fullMatrix_interval_entries (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ)
    (y : EuclideanSpace ℝ (Fin (N : ℕ))) (a b : Fin (N : ℕ)) :
    fullMatrix s N hN K θ ε κ₀ y a b =
      ∑ i, ∑ r, fullIntervalWeight s N hN K θ ε κ₀ i r y *
        (if a ∈ cyclicIndexInterval N i (r.val+1) then 1 else 0) *
        (if b ∈ cyclicIndexInterval N i (r.val+1) then 1 else 0) := by
  by_cases hy : y ∈ fullGapGoodSet s N ε κ₀
  · simp only [fullMatrix,fullIntervalWeight,ite_eq_left hy,Matrix.add_apply,Matrix.of_apply,
      add_mul,Finset.sum_add_distrib]
    rw [← Internal.full_forcing_singletons N hN θ ε y hy.1 a b]
    rw [add_comm,GoodBlocks.gapHessian,Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro r _
    unfold Internal.fullCoefficient
    split_ifs <;> simp_all
  · simpa only [fullMatrix,fullIntervalWeight,ite_eq_right hy,Matrix.smul_apply,smul_eq_mul] using
      Internal.referenceMatrix_sum s N hN K a b

/-- See the proof of Lemma 5.4 in the paper: the literal quadratic interval identity. -/
theorem fullMatrix_interval_quadratic (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ)
    (y : EuclideanSpace ℝ (Fin (N : ℕ))) (z : Fin (N : ℕ) → ℝ) :
    (∑ a, ∑ b, z a * fullMatrix s N hN K θ ε κ₀ y a b * z b) =
      ∑ i, ∑ r, fullIntervalWeight s N hN K θ ε κ₀ i r y *
        (cyclicGapSum N i (r.val+1) z)^2 := by
  have h := sum_quadratic_rankOne (κ := Fin (N : ℕ) × Fin ((N : ℕ)/2)) Finset.univ
    (fun t => fullIntervalWeight s N hN K θ ε κ₀ t.1 t.2 y)
    (fun t a => if a ∈ cyclicIndexInterval N t.1 (t.2.val+1) then (1 : ℝ) else 0) z
  simp only [Fintype.sum_prod_type] at h
  have hs (i : Fin (N : ℕ)) (r : Fin ((N : ℕ)/2)) :
      (∑ a : Fin (N : ℕ), (if a ∈ cyclicIndexInterval N i (r.val+1) then (1 : ℝ) else 0)*z a) =
        cyclicGapSum N i (r.val+1) z := by
    simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_mem,Finset.univ_inter]
    exact sum_cyclicIndexInterval_eq_cyclicGapSum N i (by have := r.isLt; omega) z
  simp only [hs] at h
  simp only [fullMatrix_interval_entries s N hN K θ ε κ₀ y]
  exact h

end Riesz2.PhysicalCore

namespace Riesz2.PhysicalCore

/-- See the proof of Lemma 5.4 in the paper: uniform upper interval bound on the full
cycle, including the forcing singletons and the reference branch. -/
theorem fullIntervalWeight_upper (s : Riesz1.RieszExponent) (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_β : InverseTemperature) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (K : ℕ) (ε κ₀ : ℝ), 0 ≤ ε →
      ∀ (y : EuclideanSpace ℝ (Fin (N : ℕ))) (i : Fin (N : ℕ)) (r : Fin ((N : ℕ)/2)),
        fullIntervalWeight s N hN K θ ε κ₀ i r y ≤
          C*(N : ℝ)^((s.val+2)*ε)*(r.val+1 : ℝ)^(-s.val-2) := by
  obtain ⟨F,hF,hforce⟩ := forcingHessian_uniform_bound θ
  obtain ⟨B,hB,href⟩ := BoundaryEntries.referenceWeight_bound s
  let D := 2*PhysicalEnergy.coefficientConstant s.val s.property.1
  have hD : 0 < D := by dsimp only [D]; exact mul_pos (by norm_num) (PhysicalEnergy.coefficientConstant_pos _ _)
  let C := B+D+F
  have hC : 0 < C := by dsimp only [C]; linarith
  refine ⟨C,hC,fun β N hN K ε κ₀ hε y i r => ?_⟩
  let v := (N : ℝ)^((s.val+2)*ε)
  let w := (r.val+1 : ℝ)^(-s.val-2)
  have hv : 1 ≤ v := Real.one_le_rpow (by exact_mod_cast N.pos)
    (by have := s.property.1; positivity)
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  by_cases hy : y ∈ fullGapGoodSet s N ε κ₀
  · have hp : Internal.fullCoefficient s N i r y ≤ D*v*w :=
      (Internal.fullCoefficient_bounds β s N ε κ₀ y hy i r).2
    have hf : (if r.val = 0 then forcingHessian N θ ε y i i else 0) ≤ F*v*w := by
      split_ifs with hr
      · have hw1 : w = 1 := by simp only [w,hr,Nat.cast_zero,zero_add,Real.one_rpow]
        rw [hw1,mul_one]
        exact (hforce N 0 ε hε ⟨y,Internal.simplex_mem_forcing_chart N y hy.1⟩ i i).trans
          (le_mul_of_one_le_right hF.le hv)
      · positivity
    simp only [fullIntervalWeight,ite_eq_left hy]
    have he := add_le_add hp hf
    have hDC : D+F ≤ C := by dsimp only [C]; linarith
    have he' : Internal.fullCoefficient s N i r y +
        (if r.val = 0 then forcingHessian N θ ε y i i else 0) ≤ (D+F)*v*w := by
      simpa only [← add_mul] using he
    exact he'.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDC (by linarith)) hw)
  · simp only [fullIntervalWeight,ite_eq_right hy]
    have hb : BoundaryEntries.referenceWeight s N hN K (i,r) ≤ B*w := by
      simpa only [w,Nat.cast_add,Nat.cast_one] using href N hN K (i,r)
    exact hb.trans (mul_le_mul_of_nonneg_right
      ((show B ≤ C by dsimp only [C]; linarith).trans (le_mul_of_one_le_right hC.le hv)) hw)

/-- See the proof of Lemma 5.4 in the paper: absolute coefficient lower bound at every
retained length, uniform in volume and temperature. -/
theorem fullIntervalWeight_lower (s : Riesz1.RieszExponent) :
    ∃ c : ℝ, 0 < c ∧ ∀ (_β : InverseTemperature) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ), 0 ≤ ε →
      ∀ (y : EuclideanSpace ℝ (Fin (N : ℕ))) (i : Fin (N : ℕ)) (r : Fin ((N : ℕ)/2)),
        K ≤ r.val+1 →
        c*(N : ℝ)^(-(s.val+2)*ε)*(r.val+1 : ℝ)^(-s.val-2) ≤
          fullIntervalWeight s N hN K θ ε κ₀ i r y := by
  obtain ⟨b,hb,href⟩ := referenceWeight_lower s
  let c := min b (s.val*(s.val+1))
  have hc : 0 < c := lt_min hb (by nlinarith [s.property.1])
  refine ⟨c,hc,fun β N hN K θ ε κ₀ hε y i r hK => ?_⟩
  let v := (N : ℝ)^(-(s.val+2)*ε)
  have hv : 0 ≤ v := by dsimp only [v]; positivity
  have hv1 : v ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast N.pos) (by nlinarith [s.property.1])
  have hw : 0 ≤ (r.val+1 : ℝ)^(-s.val-2) := by positivity
  by_cases hy : y ∈ fullGapGoodSet s N ε κ₀
  · have hf : 0 ≤ if r.val = 0 then forcingHessian N θ ε y i i else 0 := by
      split_ifs
      · exact ((forcingHessian_bound N 0 θ ε).choose_spec.2
          ⟨y,Internal.simplex_mem_forcing_chart N y hy.1⟩ i i).1
      · exact le_rfl
    simp only [fullIntervalWeight,ite_eq_left hy]
    exact ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_right b (s.val*(s.val+1))) hv) hw).trans
        (Internal.fullCoefficient_bounds β s N ε κ₀ y hy i r).1).trans (le_add_of_nonneg_right hf)
  · simp only [fullIntervalWeight,ite_eq_right hy]
    have hcb : c*v ≤ b := (mul_le_of_le_one_right hc.le hv1).trans (min_le_left _ _)
    exact (mul_le_mul_of_nonneg_right hcb hw).trans
      (by simpa only [Nat.cast_add,Nat.cast_one] using href N hN K i r hK)

/-- See the proof of Lemma 5.4 in the paper: the exact long-interval region in the
predicate lies above the floor cutoff. -/
theorem fullIntervalWeight_threshold_lower (s : Riesz1.RieszExponent) :
    ∃ c : ℝ, 0 < c ∧ ∀ (M₀ : ℕ) (γ : ℝ), (M₀ : ℝ) ≤ γ →
      ∀ (_β : InverseTemperature) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
        (θ : PhysicalCutoff) (ε κ₀ : ℝ), 0 ≤ ε →
      ∀ (y : EuclideanSpace ℝ (Fin (N : ℕ))) (i : Fin (N : ℕ)) (r : Fin ((N : ℕ)/2)),
        (N : ℝ)^(γ*ε) ≤ (r.val+1 : ℝ) →
        c*(N : ℝ)^(-(s.val+2)*ε)*(r.val+1 : ℝ)^(-s.val-2) ≤
          fullIntervalWeight s N hN (⌊(N : ℝ)^ε⌋₊^M₀) θ ε κ₀ i r y := by
  obtain ⟨c,hc,hl⟩ := fullIntervalWeight_lower s
  refine ⟨c,hc,fun M₀ γ hγ β N hN θ ε κ₀ hε y i r hr => ?_⟩
  apply hl β N hN _ θ ε κ₀ hε y i r
  have hh : ((⌊(N : ℝ)^ε⌋₊^M₀ : ℕ) : ℝ) ≤ (N : ℝ)^(γ*ε) := by
    calc
      _ = (⌊(N : ℝ)^ε⌋₊ : ℝ)^M₀ := by rw [Nat.cast_pow]
      _ ≤ ((N : ℝ)^ε)^M₀ := pow_le_pow_left₀ (Nat.cast_nonneg _)
        (Nat.floor_le (Real.rpow_nonneg (by positivity) _)) _
      _ = (N : ℝ)^((M₀ : ℝ)*ε) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity : (0 : ℝ) ≤ N)]
        congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast N.pos)
        (mul_le_mul_of_nonneg_right hγ hε)
  exact_mod_cast hh.trans hr

namespace Internal

/-- Full-cycle coefficient versus the sampled curvature at the same period.
The small-displacement condition belongs only to this internal Taylor helper. -/
theorem full_coefficient_sampled_error (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_β : InverseTemperature) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (ε κ₀ : ℝ) (y : EuclideanSpace ℝ (Fin (N : ℕ))),
      y ∈ fullGapGoodSet s N ε κ₀ →
      ∀ (i : Fin (N : ℕ)) (r : Fin ((N : ℕ)/2)),
      (N : ℝ)^ε*(r.val+1 : ℝ)^(s.val/2) ≤ (r.val+1 : ℝ)/2 →
      |fullCoefficient s N i r y -
        (2 - if 2*(r.val+1) = (N : ℕ) then (1 : ℝ) else 0)*
          sampledSecondDifference s N hN ⟨r.val+1,by have := r.isLt; omega⟩| ≤
        C*((N : ℝ)^ε*(r.val+1 : ℝ)^(-3-s.val/2)+(r.val+1 : ℝ)^(-s.val-4)) := by
  obtain ⟨C,hC,herror⟩ := physical_sampled_error s
  refine ⟨2*C,by positivity,fun β N hN ε κ₀ y hy i r hsmall => ?_⟩
  have hdev := hy.2.1.2 i ⟨r.val+1,by have := r.isLt; omega⟩ (by change 1 ≤ r.val+1; omega)
    (by change r.val+1 ≤ (N : ℕ)/2; have := r.isLt; omega)
  let L : {L : ℝ // 0 < L ∧ L < (N : ℝ)} :=
    ⟨cyclicGapSum N i (r.val+1) (WithLp.ofLp y),
      PhysicalEnergy.gapSum_mem N i (by omega) (by have := r.isLt; omega) _ hy.1⟩
  have he := herror β N N hN le_rfl (r.val+1) (by omega) (by have := r.isLt; omega)
    L ((N : ℝ)^ε) (by simpa only [L,Nat.cast_add,Nat.cast_one] using hdev)
    (by simpa only [Nat.cast_add,Nat.cast_one] using hsmall)
  simp only [ite_true,add_zero,Nat.cast_add,Nat.cast_one] at he
  rw [fullCoefficient_simplex β s N i r y hy.1,← mul_sub,abs_mul]
  have hw : 0 ≤ 2 - if 2*(r.val+1) = (N : ℕ) then (1 : ℝ) else 0 := by split_ifs <;> norm_num
  have hw2 : (2 - if 2*(r.val+1) = (N : ℕ) then (1 : ℝ) else 0) ≤ 2 := by split_ifs <;> norm_num
  rw [abs_of_nonneg hw]
  have he0 := (abs_nonneg _).trans he
  exact (mul_le_mul_of_nonneg_left he hw).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hw2 he0)

end Internal
end Riesz2.PhysicalCore

namespace Riesz2.PhysicalCore.Internal

/-- The proof of Lemma 5.4: the full-cycle
Taylor error uses uniform above-cutoff rigidity for the paper degree.
Bounded lengths absorb small forcing scales. Other cutoff powers use the general relative-deviation bound.
The result also covers zero epsilon. -/
theorem full_coefficient_same_period_error (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M₀ : ℕ) (_β : InverseTemperature)
      (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (ε κ₀ : ℝ), 0 ≤ ε →
      ∀ (y : EuclideanSpace ℝ (Fin (N : ℕ))), y ∈ fullGapGoodSet s N ε κ₀ →
      ∀ (i : Fin (N : ℕ)) (r : Fin ((N : ℕ)/2)),
        |fullCoefficient s N i r y - BoundaryEntries.referenceWeight s N hN
          (⌊(N : ℝ)^ε⌋₊^M₀) (i,r)| ≤
          C*(N : ℝ)^((s.val+3+(M₀ : ℝ))*ε)*(r.val+1 : ℝ)^(-3-s.val/2) := by
  obtain ⟨E,hE,htaylor⟩ := full_coefficient_sampled_error s
  obtain ⟨B,hB,href⟩ := BoundaryEntries.referenceWeight_bound s
  let D := 2*PhysicalEnergy.coefficientConstant s.val s.property.1
  have hD : 0 < D := mul_pos (by norm_num) (PhysicalEnergy.coefficientConstant_pos _ _)
  let C := 512*(D+B+E)
  have hC : 0 < C := by dsimp only [C]; linarith
  refine ⟨C,hC,fun M₀ β N hN ε κ₀ hε y hy i r => ?_⟩
  let R : ℝ := r.val+1
  let U := s.val+2
  let K := ⌊(N : ℝ)^ε⌋₊^M₀
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hn0 : (0 : ℝ) < N := by positivity
  have hR : 1 ≤ R := by dsimp only [R]; exact_mod_cast (show 1 ≤ r.val+1 by omega)
  have hR0 : 0 < R := by linarith
  have hU : 0 ≤ U := by dsimp only [U]; linarith [s.property.1]
  have hpow : 1 ≤ (N : ℝ)^(U*ε) := Real.one_le_rpow hn1 (mul_nonneg hU hε)
  have hq : 0 ≤ R^(-s.val-2) := Real.rpow_nonneg hR0.le _
  have hbase : |fullCoefficient s N i r y - BoundaryEntries.referenceWeight s N hN K (i,r)| ≤
      (D+B)*(N : ℝ)^(U*ε)*R^(-s.val-2) := by
    have hp := (fullCoefficient_bounds β s N ε κ₀ y hy i r).2
    have hb := href N hN K (i,r)
    have hb' := mul_le_mul_of_nonneg_left hpow hB.le
    have hb'' := mul_le_mul_of_nonneg_right hb' hq
    have hnP := fullCoefficient_nonneg β s N ε κ₀ y hy i r
    have hnB := BoundaryEntries.referenceWeight_nonneg s N hN K (i,r)
    have hab := abs_sub_le (fullCoefficient s N i r y) 0
      (BoundaryEntries.referenceWeight s N hN K (i,r))
    simp only [sub_zero,zero_sub,abs_neg,abs_of_nonneg hnP,abs_of_nonneg hnB] at hab
    change _ ≤ D*(N : ℝ)^(U*ε)*R^(-s.val-2) at hp
    change _ ≤ B*R^(-s.val-2) at hb
    nlinarith only [hab,hp,hb,hb'']
  have hmon (v : ℝ) (hv : v ≤ U + 1 + M₀) :
      (N : ℝ) ^ (v * ε) ≤ (N : ℝ) ^ ((U + 1 + M₀) * ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (mul_le_mul_of_nonneg_right hv hε)
  rw [show s.val + 3 + (M₀ : ℝ) = U + 1 + M₀ by dsimp only [U]; ring]
  change _ ≤ C * (N : ℝ) ^ ((U + 1 + M₀) * ε) * R ^ (-3 - s.val / 2)
  by_cases hK : K ≤ r.val + 1
  · have hcases : (N : ℝ) ^ ε * R ^ (s.val / 2) ≤ R / 2 ∨
        R ^ (1 - s.val / 2) ≤ 256 * (N : ℝ) ^ ε := by
      have hq : 1 ≤ (N : ℝ) ^ ε := Real.one_le_rpow hn1 hε
      by_cases hpaper : M₀ = (paperReferenceCutoffExponent s : ℕ)
      · have hcut : (⌊(N : ℝ) ^ ε⌋₊ ^ (paperReferenceCutoffExponent s : ℕ) : ℕ) ≤ R := by
          dsimp only [R]
          have hh : ⌊(N : ℝ) ^ ε⌋₊ ^ (paperReferenceCutoffExponent s : ℕ) ≤ r.val + 1 := by
            simpa only [K, hpaper] using hK
          exact_mod_cast hh
        rcases paper_cutoff_taylor_or_bounded s hq hR hcut with ht | hb
        · exact Or.inl ht
        · exact Or.inr (hb.trans (by linarith))
      · by_cases ht : (N : ℝ) ^ ε * R ^ (s.val / 2) ≤ R / 2
        · exact Or.inl ht
        · right
          have hmul : R ^ (1 - s.val / 2) * R ^ (s.val / 2) = R := by
            rw [← Real.rpow_add hR0]
            norm_num
          have hp := Real.rpow_pos_of_pos hR0 (s.val / 2)
          have hh : R ^ (1 - s.val / 2) ≤ 2 * (N : ℝ) ^ ε := by
            nlinarith only [lt_of_not_ge ht, hmul, hp]
          exact hh.trans (by linarith)
    rcases hcases with hsmall | hscale
    · have hh := htaylor β N hN ε κ₀ y hy i r hsmall
      have he : BoundaryEntries.referenceWeight s N hN K (i,r) =
          (2 - if 2*(r.val+1) = (N : ℕ) then (1 : ℝ) else 0)*
            sampledSecondDifference s N hN ⟨r.val+1,by have := r.isLt; omega⟩ := by
        simp only [BoundaryEntries.referenceWeight,hK,ite_true,
          Nat.mod_eq_of_lt (show r.val+1 < (N : ℕ) by have := r.isLt; omega)]
        split_ifs <;> ring
      rw [he]
      change |_| ≤ E*((N : ℝ)^ε*R^(-3-s.val/2)+R^(-s.val-4)) at hh
      have hdec : R ^ (-s.val - 4) ≤ R ^ (-3 - s.val / 2) :=
        Real.rpow_le_rpow_of_exponent_le hR (by linarith [s.property.1])
      have hnε : 1 ≤ (N : ℝ) ^ ε := Real.one_le_rpow hn1 hε
      have hpε := hmon 1 (by have := Nat.cast_nonneg M₀ (α := ℝ); linarith)
      simp only [one_mul] at hpε
      have hmajor : (N : ℝ) ^ ε * R ^ (-3 - s.val / 2) + R ^ (-s.val - 4) ≤
          2 * (N : ℝ) ^ ((U + 1 + M₀) * ε) * R ^ (-3 - s.val / 2) := by
        nlinarith only [hdec, mul_le_mul_of_nonneg_right hpε (Real.rpow_nonneg hR0.le (-3-s.val/2)),
          mul_le_mul_of_nonneg_right hnε (Real.rpow_nonneg hR0.le (-3-s.val/2))]
      apply hh.trans
      dsimp only [C]
      nlinarith [mul_le_mul_of_nonneg_left hmajor hE.le,
        mul_nonneg (show 0 ≤ D+B by linarith) (mul_nonneg
          (Real.rpow_nonneg hn0.le ((U+1+M₀)*ε)) (Real.rpow_nonneg hR0.le (-3-s.val/2)))]
    · have he : R ^ (1 - s.val / 2) * R ^ (-3 - s.val / 2) = R ^ (-s.val - 2) := by
        rw [← Real.rpow_add hR0]; congr 1; ring
      have hh := mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg hR0.le (-3-s.val/2))
      rw [he] at hh
      have hprod := mul_le_mul_of_nonneg_left hh
        (mul_nonneg (show 0 ≤ D+B by linarith) (Real.rpow_nonneg hn0.le (U*ε)))
      have heN : (N : ℝ) ^ (U * ε) * (N : ℝ) ^ ε = (N : ℝ) ^ ((U+1)*ε) := by
        rw [← Real.rpow_add hn0]; congr 1; ring
      have hprod' : (D+B) * (N : ℝ) ^ (U*ε) * R ^ (-s.val-2) ≤
          256*(D+B) * (N : ℝ) ^ ((U+1)*ε) * R ^ (-3-s.val/2) := by
        calc
          _ ≤ (D+B) * (N : ℝ) ^ (U*ε) * (256*(N : ℝ)^ε * R ^ (-3-s.val/2)) := hprod
          _ = _ := by rw [← heN]; ring
      apply hbase.trans (hprod'.trans _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hR0.le _)
      apply mul_le_mul (by dsimp only [C]; linarith) (hmon (U+1) (by have := Nat.cast_nonneg M₀ (α := ℝ); linarith))
        (Real.rpow_nonneg hn0.le _) hC.le
  · have hshort : R ≤ (N : ℝ) ^ ((M₀ : ℝ) * ε) := by
      have hh : (r.val + 1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (by omega : r.val+1 ≤ K)
      apply hh.trans
      dsimp only [K]
      rw [Nat.cast_pow]
      calc
        _ ≤ ((N : ℝ) ^ ε) ^ M₀ := pow_le_pow_left₀ (Nat.cast_nonneg _)
          (Nat.floor_le (Real.rpow_nonneg hn0.le _)) _
        _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; congr 1; ring
    have hscale : R ^ (1-s.val/2) ≤ (N : ℝ) ^ ((M₀ : ℝ)*ε) :=
      (Real.rpow_le_self_of_one_le hR (by linarith [s.property.1])).trans hshort
    have he : R ^ (1-s.val/2) * R ^ (-3-s.val/2) = R ^ (-s.val-2) := by
      rw [← Real.rpow_add hR0]; congr 1; ring
    have hh := mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg hR0.le (-3-s.val/2))
    rw [he] at hh
    have hm := mul_le_mul_of_nonneg_left hh
      (mul_nonneg (show 0 ≤ D+B by linarith) (Real.rpow_nonneg hn0.le (U*ε)))
    have heN : (N : ℝ) ^ (U*ε) * (N : ℝ) ^ ((M₀ : ℝ)*ε) =
        (N : ℝ) ^ ((U+M₀)*ε) := by rw [← Real.rpow_add hn0]; congr 1; ring
    apply hbase.trans
    calc
      _ ≤ (D+B) * (N : ℝ) ^ (U*ε) * ((N : ℝ) ^ ((M₀ : ℝ)*ε) * R ^ (-3-s.val/2)) := hm
      _ = (D+B) * (N : ℝ) ^ ((U+M₀)*ε) * R ^ (-3-s.val/2) := by rw [← heN]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hR0.le _)
        exact mul_le_mul (by dsimp only [C]; linarith) (hmon (U+M₀) (by linarith))
          (Real.rpow_nonneg hn0.le _) hC.le


end Riesz2.PhysicalCore.Internal

namespace Riesz2.PhysicalCore

/-- See the proof of Lemma 5.4 in the paper: freezing and the forcing singleton terms
preserve the improved coefficient error at the full physical period. -/
theorem fullIntervalWeight_error (s : Riesz1.RieszExponent) (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M₀ : ℕ) (_β : InverseTemperature)
      (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (ε κ₀ : ℝ), 0 ≤ ε →
      ∀ (y : EuclideanSpace ℝ (Fin (N : ℕ))) (i : Fin (N : ℕ)) (r : Fin ((N : ℕ)/2)),
        |fullIntervalWeight s N hN (⌊(N : ℝ)^ε⌋₊^M₀) θ ε κ₀ i r y -
          BoundaryEntries.referenceWeight s N hN (⌊(N : ℝ)^ε⌋₊^M₀) (i,r)| ≤
          C*(N : ℝ)^((s.val+3+(M₀ : ℝ))*ε)*(r.val+1 : ℝ)^(-3-s.val/2) := by
  obtain ⟨D,hD,herror⟩ := Internal.full_coefficient_same_period_error s
  obtain ⟨F,hF,hforce⟩ := forcingHessian_uniform_bound θ
  refine ⟨D+F,by positivity,fun M₀ β N hN ε κ₀ hε y i r => ?_⟩
  let v := (N : ℝ)^((s.val+3+(M₀ : ℝ))*ε)
  let w := (r.val+1 : ℝ)^(-3-s.val/2)
  have hv : 1 ≤ v := Real.one_le_rpow (by exact_mod_cast N.pos)
    (by have := s.property.1; have := Nat.cast_nonneg M₀ (α := ℝ); positivity)
  by_cases hy : y ∈ fullGapGoodSet s N ε κ₀
  · have hd : |Internal.fullCoefficient s N i r y -
        BoundaryEntries.referenceWeight s N hN (⌊(N : ℝ)^ε⌋₊^M₀) (i,r)| ≤ D*v*w :=
      herror M₀ β N hN ε κ₀ hε y hy i r
    have hf : |if r.val = 0 then forcingHessian N θ ε y i i else 0| ≤ F*v*w := by
      split_ifs with hr
      · have hw1 : w = 1 := by simp only [w,hr,Nat.cast_zero,zero_add,Real.one_rpow]
        rw [hw1,mul_one]
        have hn := ((forcingHessian_bound N 0 θ ε).choose_spec.2
          ⟨y,Internal.simplex_mem_forcing_chart N y hy.1⟩ i i).1
        rw [abs_of_nonneg hn]
        exact (hforce N 0 ε hε ⟨y,Internal.simplex_mem_forcing_chart N y hy.1⟩ i i).trans
          (le_mul_of_one_le_right hF.le hv)
      · rw [abs_zero]; dsimp only [w]; positivity
    simp only [fullIntervalWeight,ite_eq_left hy]
    rw [show Internal.fullCoefficient s N i r y +
        (if r.val = 0 then forcingHessian N θ ε y i i else 0) -
        BoundaryEntries.referenceWeight s N hN (⌊(N : ℝ)^ε⌋₊^M₀) (i,r) =
      (Internal.fullCoefficient s N i r y -
        BoundaryEntries.referenceWeight s N hN (⌊(N : ℝ)^ε⌋₊^M₀) (i,r)) +
        (if r.val = 0 then forcingHessian N θ ε y i i else 0) by ring]
    exact (abs_add_le _ _).trans (by change _ ≤ (D+F)*v*w; linarith only [hd,hf])
  · simp only [fullIntervalWeight,ite_eq_right hy,sub_self,abs_zero]
    positivity

/-- See the proof of Lemma 5.4 in the paper: the required full-cycle entry error,
with the exact cyclic distance and the actual cutoff. -/
theorem fullMatrix_entry_error (s : Riesz1.RieszExponent) (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M₀ : ℕ) (_β : InverseTemperature)
      (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (ε κ₀ : ℝ), 0 ≤ ε →
      ∀ (y : EuclideanSpace ℝ (Fin (N : ℕ))) (a b : Fin (N : ℕ)),
        |fullMatrix s N hN (⌊(N : ℝ)^ε⌋₊^M₀) θ ε κ₀ y a b -
          2*referenceIntervalMatrix s N hN (⌊(N : ℝ)^ε⌋₊^M₀) a b| ≤
          C*(N : ℝ)^((s.val+3+(M₀ : ℝ))*ε)*
            (1+(Riesz1.cyclicIndexDistance N a b : ℝ))^(-1-s.val/2) := by
  obtain ⟨D,hD,herror⟩ := fullIntervalWeight_error s θ
  refine ⟨D*(1+1/(1+s.val/2)),by have := s.property.1; positivity,
    fun M₀ β N hN ε κ₀ hε y a b => ?_⟩
  let K := ⌊(N : ℝ)^ε⌋₊^M₀
  let F := fun (i : Fin (N : ℕ)) (r : Fin ((N : ℕ)/2)) =>
    fullIntervalWeight s N hN K θ ε κ₀ i r y - BoundaryEntries.referenceWeight s N hN K (i,r)
  have hF (i) (r) : |F i r| ≤ (D*(N : ℝ)^((s.val+3+(M₀ : ℝ))*ε))*
      (r.val+1 : ℝ)^(-(1+s.val/2)-2) := by
    simpa only [show -(1+s.val/2)-2 = -3-s.val/2 by ring] using
      herror M₀ β N hN ε κ₀ hε y i r
  have hh := Internal.signed_interval_entry_bound N
    (by linarith [s.property.1] : 0 < 1+s.val/2) (by positivity) F hF a b
  have he : fullMatrix s N hN K θ ε κ₀ y a b - 2*referenceIntervalMatrix s N hN K a b =
      ∑ i, ∑ r, F i r * (if a ∈ cyclicIndexInterval N i (r.val+1) then 1 else 0) *
        (if b ∈ cyclicIndexInterval N i (r.val+1) then 1 else 0) := by
    rw [fullMatrix_interval_entries,Internal.referenceMatrix_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    dsimp only [F]
    ring
  rw [he]
  simpa only [show -(1+s.val/2) = -1-s.val/2 by ring,mul_assoc,mul_left_comm,mul_comm] using hh

/-- See the proof of Lemma 5.4 in the paper: a uniform positive power multiple of
all reference coefficients lies below the actual full-cycle coefficients. -/
theorem fullIntervalWeight_reference_lower (s : Riesz1.RieszExponent) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (_β : InverseTemperature) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ), 0 ≤ ε →
      ∀ (y : EuclideanSpace ℝ (Fin (N : ℕ))) (i : Fin (N : ℕ)) (r : Fin ((N : ℕ)/2)),
        c*(N : ℝ)^(-(s.val+2)*ε)*BoundaryEntries.referenceWeight s N hN K (i,r) ≤
          fullIntervalWeight s N hN K θ ε κ₀ i r y := by
  obtain ⟨B,hB,href⟩ := BoundaryEntries.referenceWeight_bound s
  let c := min 1 (s.val*(s.val+1)/B)
  have hc : 0 < c := lt_min zero_lt_one (div_pos (by nlinarith [s.property.1]) hB)
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcB : c*B ≤ s.val*(s.val+1) := (le_div_iff₀ hB).mp (min_le_right _ _)
  refine ⟨c,hc,hc1,fun β N hN K θ ε κ₀ hε y i r => ?_⟩
  let v := (N : ℝ)^(-(s.val+2)*ε)
  have hv : 0 ≤ v := by dsimp only [v]; positivity
  have hv1 : v ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast N.pos) (by nlinarith [s.property.1])
  have hq : c*v ≤ 1 := (mul_le_of_le_one_right hc.le hv1).trans hc1
  by_cases hy : y ∈ fullGapGoodSet s N ε κ₀
  · have hf : 0 ≤ if r.val = 0 then forcingHessian N θ ε y i i else 0 := by
      split_ifs
      · exact ((forcingHessian_bound N 0 θ ε).choose_spec.2
          ⟨y,Internal.simplex_mem_forcing_chart N y hy.1⟩ i i).1
      · exact le_rfl
    have hh : c*v*BoundaryEntries.referenceWeight s N hN K (i,r) ≤ Internal.fullCoefficient s N i r y := by
      calc
        _ ≤ c*v*(B*(r.val+1 : ℝ)^(-s.val-2)) := mul_le_mul_of_nonneg_left
          (by simpa only [Nat.cast_add,Nat.cast_one] using href N hN K (i,r)) (by positivity)
        _ = (c*B)*v*(r.val+1 : ℝ)^(-s.val-2) := by ring
        _ ≤ (s.val*(s.val+1))*v*(r.val+1 : ℝ)^(-s.val-2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcB hv) (by positivity)
        _ ≤ _ := (Internal.fullCoefficient_bounds β s N ε κ₀ y hy i r).1
    exact hh.trans (by simpa only [fullIntervalWeight,ite_eq_left hy] using le_add_of_nonneg_right hf)
  · simpa only [fullIntervalWeight,ite_eq_right hy] using
      mul_le_of_le_one_left (BoundaryEntries.referenceWeight_nonneg s N hN K (i,r)) hq

end Riesz2.PhysicalCore

namespace Riesz2.PhysicalCore

/-- See the proof of Lemma 5.4 in the paper: the actual full matrix dominates
a uniform positive power multiple of the exact truncated reference. -/
theorem fullMatrix_reference_lower (s : Riesz1.RieszExponent) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (_β : InverseTemperature)
      (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ), 0 ≤ ε →
      ∀ y : EuclideanSpace ℝ (Fin (N : ℕ)),
        (c*(N : ℝ)^(-(s.val+2)*ε)) • ((2 : ℝ) • referenceIntervalMatrix s N hN K) ≤
          fullMatrix s N hN K θ ε κ₀ y := by
  obtain ⟨c, hc, hc1, hb⟩ := fullIntervalWeight_reference_lower s
  refine ⟨c, hc, hc1, fun β N hN K θ ε κ₀ hε y => ?_⟩
  let q := c * (N : ℝ) ^ (-(s.val + 2) * ε)
  let v := fun (t : Fin (N : ℕ) × Fin ((N : ℕ) / 2)) (a : Fin (N : ℕ)) =>
    if a ∈ cyclicIndexInterval N t.1 (t.2.val + 1) then (1 : ℝ) else 0
  let w := fun t : Fin (N : ℕ) × Fin ((N : ℕ) / 2) =>
    fullIntervalWeight s N hN K θ ε κ₀ t.1 t.2 y -
      q * BoundaryEntries.referenceWeight s N hN K t
  have he : fullMatrix s N hN K θ ε κ₀ y -
      q • ((2 : ℝ) • referenceIntervalMatrix s N hN K) =
      ∑ t, w t • Matrix.vecMulVec (v t) (v t) := by
    ext a b
    change fullMatrix s N hN K θ ε κ₀ y a b -
      q * (2 * referenceIntervalMatrix s N hN K a b) = _
    rw [fullMatrix_interval_entries s N hN K θ ε κ₀ y,
      Internal.referenceMatrix_sum]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      smul_eq_mul, Fintype.sum_prod_type, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro r _
    dsimp only [w, v]
    ring
  apply Matrix.le_iff.mpr
  rw [he]
  exact FiniteMatrixOrder.posSemidef_rankOneSum Finset.univ w v
    (fun t _ => sub_nonneg.mpr (hb β N hN K θ ε κ₀ hε y t.1 t.2))


/-- See the proof of Lemma 5.4 in the paper: truncated-reference coercivity transfers
to the full physical matrix with a prefactor depending only on s. -/
theorem fullMatrix_truncated_coercivity (s : Riesz1.RieszExponent) :
    ∃ c : ℝ, 0 < c ∧ ∀ (_β : InverseTemperature)
      (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K : ℕ), 1 ≤ K → K ≤ (N : ℕ)/4 →
      ∀ (θ : PhysicalCutoff) (ε κ₀ : ℝ), 0 ≤ ε →
      ∀ y : EuclideanSpace ℝ (Fin (N : ℕ)),
        (c*(N : ℝ)^(-(s.val+2)*ε)*(K : ℝ)^(-1-s.val)) •
          (1 : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ) ≤ fullMatrix s N hN K θ ε κ₀ y := by
  obtain ⟨c, hc, _, hb⟩ := fullMatrix_reference_lower s
  obtain ⟨a, ha, href⟩ := referenceIntervalMatrix_truncated_coercivity s
  refine ⟨c * 2 * a, by positivity, fun β N hN K hK hKM θ ε κ₀ hε y => ?_⟩
  let q := c * (N : ℝ) ^ (-(s.val + 2) * ε)
  have hq : 0 ≤ q := mul_nonneg hc.le (Real.rpow_nonneg (by positivity) _)
  have hr := smul_le_smul_of_nonneg_left (href N hN K hK hKM).2.2
    (mul_nonneg hq (by norm_num : (0 : ℝ) ≤ 2))
  have hcompare := hb β N hN K θ ε κ₀ hε y
  have he : (c * 2 * a) * (N : ℝ) ^ (-(s.val + 2) * ε) * (K : ℝ) ^ (-1 - s.val) =
      (q * 2) * (a * (K : ℝ) ^ (-1 - s.val)) := by dsimp only [q]; ring
  rw [he]
  have hr' : ((q * 2) * (a * (K : ℝ) ^ (-1 - s.val))) •
      (1 : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ) ≤
      q • ((2 : ℝ) • referenceIntervalMatrix s N hN K) := by
    simpa only [smul_smul] using hr
  exact hr'.trans hcompare


/-- See the proof of Lemma 5.4 in the paper: the prescribed floor cutoff gives the
uniform coercivity exponent s+2+M₀(1+s), independent of beta and epsilon. -/
theorem fullMatrix_cutoff_coercivity (s : Riesz1.RieszExponent) :
    ∃ c : ℝ, 0 < c ∧ ∀ (M₀ : ℕ) (_β : InverseTemperature)
      (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (θ : PhysicalCutoff) (ε κ₀ : ℝ), 0 ≤ ε →
      let K := ⌊(N : ℝ)^ε⌋₊^M₀
      K ≤ (N : ℕ)/4 → ∀ y : EuclideanSpace ℝ (Fin (N : ℕ)),
        (c*(N : ℝ)^(-((s.val+2)+(M₀ : ℝ)*(1+s.val))*ε)) •
          (1 : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ) ≤ fullMatrix s N hN K θ ε κ₀ y := by
  obtain ⟨c, hc, hb⟩ := fullMatrix_truncated_coercivity s
  refine ⟨c, hc, ?_⟩
  intro M₀ β N hN θ ε κ₀ hε K hKM y
  have hn0 : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hfloor : 1 ≤ ⌊(N : ℝ) ^ ε⌋₊ :=
    (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hn1 hε)
  have hK : 1 ≤ K := one_le_pow₀ hfloor
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hupper : (K : ℝ) ≤ (N : ℝ) ^ ((M₀ : ℝ) * ε) := by
    calc
      _ = (⌊(N : ℝ) ^ ε⌋₊ : ℝ) ^ M₀ := by rw [Nat.cast_pow]
      _ ≤ ((N : ℝ) ^ ε) ^ M₀ :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (Real.rpow_nonneg hn0.le _)) M₀
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
        congr 1
        ring
  have hpow := Real.rpow_le_rpow_of_nonpos hK0 hupper
    (show -1 - s.val ≤ 0 by linarith [s.property.1])
  have he : (N : ℝ) ^ (-((s.val + 2) + (M₀ : ℝ) * (1 + s.val)) * ε) =
      (N : ℝ) ^ (-(s.val + 2) * ε) *
        ((N : ℝ) ^ ((M₀ : ℝ) * ε)) ^ (-1 - s.val) := by
    rw [← Real.rpow_mul hn0.le, ← Real.rpow_add hn0]
    congr 1
    ring
  have hscalar : c * (N : ℝ) ^ (-((s.val + 2) + (M₀ : ℝ) * (1 + s.val)) * ε) ≤
      c * (N : ℝ) ^ (-(s.val + 2) * ε) * (K : ℝ) ^ (-1 - s.val) := by
    rw [he, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have horder := smul_le_smul_of_nonneg_right hscalar
    (show (0 : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ) ≤ 1 by exact zero_le_one)
  exact horder.trans (hb β N hN K hK hKM θ ε κ₀ hε y)


end Riesz2.PhysicalCore

namespace Riesz2.PhysicalCore

/-- See the proof of Lemma 5.4 in the paper, complete full-cycle clause. The threshold
and exponents precede the cutoff function, temperature, epsilon, and volume.
Every part of the predicate holds on the whole ambient
carrier and therefore for every measure on that carrier. -/
theorem full_matrix_bounds (s : Riesz1.RieszExponent) (M₀ : ℕ) (κ₀ : ℝ) :
    ∃ ε₀ κ γ : ℝ, 0 < ε₀ ∧ 0 < κ ∧ 0 < γ ∧
      ∀ θ : PhysicalCutoff, ∀ _β : InverseTemperature, ∃ C : ℝ, 1 ≤ C ∧
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
        ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)),
        let K := ⌊(N : ℝ)^ε⌋₊^M₀
        K ≤ (N : ℕ)/4 →
        ∀ μ : Measure (EuclideanSpace ℝ (Fin (N : ℕ))),
          PeriodizedMatrixBounds (ν := μ) s N N hN K C κ γ ε
            (fullMatrix s N hN K θ ε κ₀) := by
  obtain ⟨c₁,hc₁,hcoerc⟩ := fullMatrix_cutoff_coercivity s
  obtain ⟨c₂,hc₂,hlower⟩ := fullIntervalWeight_threshold_lower s
  let kE := s.val+3+(M₀ : ℝ)
  let kC := s.val+2+(M₀ : ℝ)*(1+s.val)
  let κ := kE+kC
  let γ := (M₀ : ℝ)+1
  have hkE : 0 < kE := by dsimp only [kE]; have := Nat.cast_nonneg M₀ (α := ℝ); linarith [s.property.1]
  have hkC : 0 < kC := by dsimp only [kC]; have := s.property.1; positivity
  refine ⟨(1-s.val/2)/2,κ,γ,by linarith [s.property.2],by dsimp only [κ]; positivity,
    by dsimp only [γ]; positivity,fun θ β => ?_⟩
  obtain ⟨U,hU,hupper⟩ := fullIntervalWeight_upper s θ
  obtain ⟨E,hE,hentry⟩ := fullMatrix_entry_error s θ
  have hi₁ : 0 < c₁⁻¹ := inv_pos.mpr hc₁
  have hi₂ : 0 < c₂⁻¹ := inv_pos.mpr hc₂
  let C := 1+U+E+c₁⁻¹+c₂⁻¹
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hCU : U ≤ C := by dsimp only [C]; linarith
  have hCE : E ≤ C := by dsimp only [C]; linarith
  have hcC₁ : C⁻¹ ≤ c₁ := (inv_le_comm₀ hC0 hc₁).mpr (by dsimp only [C]; linarith)
  have hcC₂ : C⁻¹ ≤ c₂ := (inv_le_comm₀ hC0 hc₂).mpr (by dsimp only [C]; linarith)
  refine ⟨C,hC,?_⟩
  intro ε hε _hεa N hN K hKN μ
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hn0 : (0 : ℝ) < N := by positivity
  have lower (c l : ℝ) (hc : 0 < c) (hcl : C⁻¹ ≤ c) (hl : l ≤ κ) :
      C⁻¹*(N : ℝ)^(-κ*ε) ≤ c*(N : ℝ)^(-l*ε) :=
    mul_le_mul hcl (Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith only [hl,hε]))
      (Real.rpow_nonneg hn0.le _) hc.le
  have upper (c l : ℝ) (hcl : c ≤ C) (hl : l ≤ κ) :
      c*(N : ℝ)^(l*ε) ≤ C*(N : ℝ)^(κ*ε) :=
    mul_le_mul hcl (Real.rpow_le_rpow_of_exponent_le hn1
      (mul_le_mul_of_nonneg_right hl hε)) (Real.rpow_nonneg hn0.le _) hC0.le
  have hkEκ : kE ≤ κ := by dsimp only [κ]; linarith
  have hksκ : s.val+2 ≤ κ := by
    have hh : s.val+2 ≤ kC := by
      dsimp only [kC]
      have hp : 0 ≤ (M₀ : ℝ)*(1+s.val) := by have := s.property.1; positivity
      linarith
    dsimp only [κ]; linarith
  have hkCκ : kC ≤ κ := by dsimp only [κ]; linarith
  refine ⟨measurable_fullMatrix s N hN K θ ε κ₀,?_,?_⟩
  · apply ae_of_all
    intro y
    have hsym := fullMatrix_symmetric β s N hN K θ ε κ₀ y
    have hHerm : (fullMatrix s N hN K θ ε κ₀ y).IsHermitian := by
      ext a b
      simp only [Matrix.conjTranspose_apply,star_trivial,hsym]
    refine ⟨hsym,?_,?_,?_⟩
    · intro a b hab
      have := a.isLt
      have := b.isLt
      omega
    · intro z
      have hh := (FiniteMatrixOrder.smul_one_le_iff hHerm _).mp
        (hcoerc M₀ β N hN θ ε κ₀ hε hKN y) z
      have hh' : c₁*(N : ℝ)^(-kC*ε)*(∑ i,z i^2) ≤
          ∑ i,∑ j,z i*fullMatrix s N hN K θ ε κ₀ y i j*z j := by
        simpa only [kC,Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc,pow_two] using hh
      exact (mul_le_mul_of_nonneg_right (lower c₁ kC hc₁ hcC₁ hkCκ)
        (Finset.sum_nonneg (fun i _ => sq_nonneg (z i)))).trans hh'
    · intro a b _ha _hb
      have he := hentry M₀ β N hN ε κ₀ hε y a b
      exact he.trans (by
        simpa only [Matrix.smul_apply,smul_eq_mul] using mul_le_mul_of_nonneg_right
          (upper E kE hCE hkEκ)
          (Real.rpow_nonneg (by positivity : 0 ≤ 1+(Riesz1.cyclicIndexDistance N a b : ℝ)) (-1-s.val/2)))
  · refine ⟨fullIntervalWeight s N hN K θ ε κ₀,
      measurable_fullIntervalWeight s N hN K θ ε κ₀,ae_of_all _ (fun y => ?_)⟩
    refine ⟨fun i r => ⟨fullIntervalWeight_nonneg β s N hN K θ ε κ₀ i r y,?_,?_⟩,
      fullMatrix_interval_quadratic s N hN K θ ε κ₀ y⟩
    · simpa only [Nat.cast_add,Nat.cast_one] using
        (hupper β N hN K ε κ₀ hε y i r).trans
          (mul_le_mul_of_nonneg_right (upper U (s.val+2) hCU hksκ)
            (Real.rpow_nonneg (by positivity : 0 ≤ (r.val : ℝ)+1) (-s.val-2)))
    · intro hr
      simpa only [Nat.cast_add,Nat.cast_one] using
        (mul_le_mul_of_nonneg_right (lower c₂ (s.val+2) hc₂ hcC₂ hksκ)
          (Real.rpow_nonneg (by positivity : 0 ≤ (r.val : ℝ)+1) (-s.val-2))).trans
        (hlower M₀ γ (by dsimp only [γ]; linarith) β N hN θ ε κ₀ hε y i r
          (by simpa only [Nat.cast_add,Nat.cast_one] using hr))

end Riesz2.PhysicalCore

namespace Riesz2.PhysicalCore.Internal

/-- Enlarging the prefactor and structural losses preserves the matrix predicate. This internal helper only changes numerical parameters. -/
theorem matrix_bounds_mono {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Riesz1.RieszExponent) (n m : ℕ+) (hm : 2 ≤ (m : ℕ)) (K : ℕ)
    (C D κ κ' γ γ' ε : ℝ) (hC : 0 < C) (hCD : C ≤ D)
    (hκ : κ ≤ κ') (hγ : γ ≤ γ') (hε : 0 ≤ ε)
    (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (h : PeriodizedMatrixBounds (ν := μ) s n m hm K C κ γ ε M) :
    PeriodizedMatrixBounds (ν := μ) s n m hm K D κ' γ' ε M := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by positivity
  have hD : 0 < D := hC.trans_le hCD
  have hl : D⁻¹*(n : ℝ)^(-κ'*ε) ≤ C⁻¹*(n : ℝ)^(-κ*ε) :=
    mul_le_mul ((inv_le_inv₀ hD hC).mpr hCD)
      (Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith only [hκ,hε]))
      (Real.rpow_nonneg hn0.le _) (inv_nonneg.mpr hC.le)
  have hu : C*(n : ℝ)^(κ*ε) ≤ D*(n : ℝ)^(κ'*ε) :=
    mul_le_mul hCD (Real.rpow_le_rpow_of_exponent_le hn1
      (mul_le_mul_of_nonneg_right hκ hε)) (Real.rpow_nonneg hn0.le _) hD.le
  obtain ⟨hmeas,hmat,a,hameas,hcoeff⟩ := h
  refine ⟨hmeas,?_,a,hameas,?_⟩
  · filter_upwards [hmat] with x hx
    refine ⟨hx.1,hx.2.1,?_,?_⟩
    · intro z
      exact (mul_le_mul_of_nonneg_right hl (Finset.sum_nonneg fun i _ => sq_nonneg (z i))).trans
        (hx.2.2.1 z)
    · intro i j hi hj
      exact (hx.2.2.2 i j hi hj).trans (mul_le_mul_of_nonneg_right hu (by positivity))
  · filter_upwards [hcoeff] with x hx
    refine ⟨fun i r => ⟨(hx.1 i r).1,?_,?_⟩,hx.2⟩
    · exact (hx.1 i r).2.1.trans (mul_le_mul_of_nonneg_right hu (by positivity))
    · intro hr
      exact (mul_le_mul_of_nonneg_right hl (by positivity)).trans
        ((hx.1 i r).2.2 ((Real.rpow_le_rpow_of_exponent_le hn1
          (mul_le_mul_of_nonneg_right hγ hε)).trans hr))

end Riesz2.PhysicalCore.Internal

namespace Riesz2.PhysicalCore

/-- See the proof of Lemma 5.4 in the paper, both the proper-window
and full-cycle physical fields satisfy the matrix predicate,
with common structural constants chosen before temperature, epsilon and
volumes. The proper clause reuses `proper_matrix_bounds` without repeating
its coefficient or different-period argument. The result also covers
zero epsilon and every natural cutoff power, hence the paper's positive
small-parameter and sufficiently large power ranges. -/
theorem ident_core (s : Riesz1.RieszExponent) (θ : PhysicalCutoff)
    (M₀ : ℕ) (κ₀ : ℝ) (hκ₀ : 0 ≤ κ₀) :
    ∃ ε₀ κ γ : ℝ, 0 < ε₀ ∧ 0 < κ ∧ 0 < γ ∧
      ∀ β : InverseTemperature, ∃ C : ℝ, 1 ≤ C ∧
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
        (∀ (n : ℕ+) (m : ℕ) (hn : 2*(n : ℕ) ≤ (n : ℕ)+m+1),
          let N := ((n : ℕ)+m).succPNat
          let M := properReferencePeriod s n N
          let hM : 2 ≤ (M : ℕ) := by
            change 2 ≤ (properReferencePeriod s n N : ℕ)
            have := (properReferencePeriod_bounds s n N hn).1
            have := n.pos
            omega
          let hnM : (n : ℕ) ≤ (M : ℕ) := by
            change (n : ℕ) ≤ (properReferencePeriod s n N : ℕ)
            have := (properReferencePeriod_bounds s n N hn).1
            omega
          let K := ⌊(n : ℝ)^ε⌋₊^M₀
          K ≤ (M : ℕ)/4 →
          ∀ μ : Measure (AffineSimplex.chartDomain n ((n+m : ℕ)+1)),
            PeriodizedMatrixBounds (ν := μ) s n M hM K C κ γ ε
              (properMatrix β s n m M hM hnM K θ ε κ₀)) ∧
        (∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)),
          let K := ⌊(N : ℝ)^ε⌋₊^M₀
          K ≤ (N : ℕ)/4 →
          ∀ μ : Measure (EuclideanSpace ℝ (Fin (N : ℕ))),
            PeriodizedMatrixBounds (ν := μ) s N N hN K C κ γ ε
              (fullMatrix s N hN K θ ε κ₀)) := by
  obtain ⟨ep,kp,gp,hep,hkp,hgp,hproper⟩ := proper_matrix_bounds s θ M₀ κ₀ hκ₀
  obtain ⟨ef,kf,gf,hef,hkf,hgf,hfull⟩ := full_matrix_bounds s M₀ κ₀
  refine ⟨min ep ef,max kp kf,max gp gf,lt_min hep hef,
    hkp.trans_le (le_max_left _ _),hgp.trans_le (le_max_left _ _),fun β => ?_⟩
  obtain ⟨Cp,hCp,hp⟩ := hproper β
  obtain ⟨Cf,hCf,hf⟩ := hfull θ β
  refine ⟨max Cp Cf,hCp.trans (le_max_left _ _),fun ε hε hεa => ⟨?_,?_⟩⟩
  · intro n m hn N M hM hnM K hKM μ
    have hh := hp ε hε (hεa.trans (min_le_left _ _)) n m hn hKM μ
    exact Internal.matrix_bounds_mono s n M hM K Cp (max Cp Cf) kp (max kp kf) gp (max gp gf) ε
      (lt_of_lt_of_le zero_lt_one hCp) (le_max_left _ _) (le_max_left _ _) (le_max_left _ _)
      hε (properMatrix β s n m M hM hnM K θ ε κ₀) hh
  · intro N hN K hKN μ
    have hh := hf ε hε (hεa.trans (min_le_right _ _)) N hN hKN μ
    exact Internal.matrix_bounds_mono s N N hN K Cf (max Cp Cf) kf (max kp kf) gf (max gp gf) ε
      (lt_of_lt_of_le zero_lt_one hCf) (le_max_right _ _) (le_max_right _ _) (le_max_right _ _)
      hε (fullMatrix s N hN K θ ε κ₀) hh

end Riesz2.PhysicalCore
