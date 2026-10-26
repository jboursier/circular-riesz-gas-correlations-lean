/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.PaperPhysicalComparisonPart2

/-!
# Spectral upper bound for the paper's physical auxiliary matrix

The verification following equation (4.13) discards the
positive covariance matrix and uses the direct `P` and `Q` entry bounds.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal ContDiff Topology

namespace Riesz2.DecayShort
open PhysicalComparison ConditionalScores

set_option backward.isDefEq.respectTransparency false in
/-- Spectral upper bound in the paper's verification following
equation (4.13). Only the direct `P` and `Q` conditions are used. -/
theorem paperFrozenPhysicalMatrix_upper (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Parameters), 1 < p.val.2 → ∀ (n : ℕ+) (m : ℕ)
      (U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ),
      (∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) //
        y ∈ gapAmbientDomain ((n : ℕ)+m).succPNat},
        U y.val = p.val.1*physicalAmbientGapEnergy p ((n : ℕ)+m).succPNat y) →
      2 ≤ (n : ℕ)+m+1 → 2*(n : ℕ) ≤ (n : ℕ)+m+1 →
      ∀ h : ℝ, 0 < h → ∀ (b : Bool) (D : ℝ), 0 ≤ D →
      ∀ (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1)) (z : Fin (n : ℕ) → ℝ),
      (∑ i, ∑ j, z i*paperFrozenPhysicalMatrix p n m U θ h b D x i j*z j) ≤
        (1+C*(n : ℝ)^(4*h)+D*((2*∑' k : ℕ, (1+(k : ℝ))^(-p.val.2))+1))*∑ i, z i^2 := by
  classical
  obtain ⟨C,hC,hpen⟩ := internal_paper_penalty_bound θ
  refine ⟨C,hC,?_⟩
  intro p hs n m U hv hN hhalf h hh b D hD x z
  let F := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
    ∑ i, (θ.val (((n : ℝ)^h)⁻¹*y i)+if b then θ.val (((n : ℝ)^h)⁻¹*(y i)⁻¹) else 0)
  let K := fun y => p.val.1⁻¹*(p.val.1*F y-Real.log
    (∫ z : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,z)).toReal))
  let N := ((n : ℕ)+m).succPNat
  let hn : (n : ℕ) ≤ (N : ℕ) := by simp only [N,Nat.succPNat_coe]; omega
  let A := conditionalIntervalWeight p n m n.pos (Equiv.refl _) x
  let P := IntervalBoundary.intervalMatrix N n hn A
  let Q := fun i j => paperCompensationEntry p n m x i j
  let μ := ProperMarginalChart.conditionalMeasure p n m n.pos (Equiv.refl _) x
  let Xi := fun i => paperCompensatedScore p n m U x i
  let S := 2*∑' k : ℕ, (1+(k : ℝ))^(-p.val.2)
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hz0 : 0 ≤ ∑ i, z i^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_cases hx : x ∈ paperProperGoodEvent p n m U h D
  swap
  · rw [(paperFrozenMatrices_off_event p n m U θ h b D x hx).1]
    simp only [Matrix.one_apply,mul_ite,mul_one,mul_zero,ite_mul,zero_mul,
      Finset.sum_ite_eq,Finset.mem_univ,ite_true,← sq]
    nlinarith [mul_nonneg (show 0 ≤ C*(n : ℝ)^(4*h) by positivity) hz0,
      mul_nonneg (show 0 ≤ D*(S+1) by positivity) hz0]
  have hSchur (M : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ) (B : ℝ)
      (hr : ∀ i, ∑ j, |M i j| ≤ B) (hc : ∀ j, ∑ i, |M i j| ≤ B) :
      (∑ i, ∑ j, z i*M i j*z j) ≤ B*∑ i,z i^2 := by
    calc
      _ ≤ ∑ i, ∑ j, |z i| * |M i j| * |z j| := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        simpa only [abs_mul] using le_abs_self (z i*M i j*z j)
      _ ≤ _ := by
        simpa only [add_self_div_two] using InitialDecay.Internal.schur_quadratic_le
          (fun i j => |M i j|) (fun _ _ => abs_nonneg _) B B hr hc z
  have hProw (i) : ∑ j, |P i j| ≤ D*S := by
    let g : ComponentGeometry (Fin (n : ℕ)) := Sum.inr ⟨N,Fin.castLEEmb hn⟩
    have hb (j) : |P i j| ≤ D*(1+componentDistance g i j)^(-p.val.2) := by
      rw [abs_of_nonneg (IntervalBoundary.intervalMatrix_nonneg N n hn A
        (conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x) i j)]
      exact hx.2.1 i j
    exact (Finset.sum_le_sum (fun j _ => hb j)).trans
      (by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (ComponentGeometryBounds.sum_power_le g i hs) hD)
  have hPcol (j) : ∑ i, |P i j| ≤ D*S := by
    have he : (∑ i, |P i j|) = ∑ i, |P j i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show P i j=P j i from IntervalBoundary.intervalMatrix_symm N n hn A i j]
    rw [he]
    exact hProw j
  have hQsum : (n : ℝ)*(D/(N : ℝ)) ≤ D := by
    have hNN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn
    apply (mul_le_mul_of_nonneg_right hNN (by positivity : 0 ≤ D/(N : ℝ))).trans_eq
    field_simp
  have hQrow (i) : ∑ j, |Q i j| ≤ D := by
    apply (Finset.sum_le_sum (fun j _ => hx.2.2.1 i j)).trans
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,N,Nat.succPNat_coe] using hQsum
  have hQcol (j) : ∑ i, |Q i j| ≤ D := by
    apply (Finset.sum_le_sum (fun i _ => hx.2.2.1 i j)).trans
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,N,Nat.succPNat_coe] using hQsum
  have hFquad : (∑ i,∑ j,z i*hessianMatrix F x.val i j*z j) ≤ C*(n : ℝ)^(4*h)*∑ i,z i^2 := by
    have he (i) : (∑ j,z i*hessianMatrix F x.val i j*z j) = z i*hessianMatrix F x.val i i*z i := by
      apply Finset.sum_eq_single i
      · intro j _ hij
        rw [penalty_hessian_off_diagonal n θ
          (inv_pos.mpr (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < n) h)) b x.val x.property.1 i j (Ne.symm hij)]
        ring
      · simp
    simp_rw [he]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hb := (le_abs_self _).trans (hpen p n m U h hh b D x hx i)
    nlinarith [mul_le_mul_of_nonneg_right hb (sq_nonneg (z i))]
  have he := internal_paper_marginal_hessian_entries p n m θ h b U hv x
  have he' (i j) : hessianMatrix K x.val i j = hessianMatrix F x.val i j+P i j+Q i j-
      p.val.1*ProbabilityTheory.covariance (Xi i) (Xi j) μ := by
    have ht := he i j
    dsimp only [F,K,μ,Q,paperCompensationEntry,P,Xi,paperCompensatedScore,N,A,Nat.succPNat_coe] at ht ⊢
    rw [ht]
    delta paperCompensatedScore
    simp only [Nat.succ_eq_add_one]
    ring
  let _ := ProperMarginalChart.conditionalMeasure_probability p n m n.pos (Equiv.refl _) x
  have hcov := internal_covariance_quadratic_nonneg μ Xi
    (paperCompensatedScore_memLp p n m hN hhalf U hv x) z
  have hquad : (∑ i,∑ j,z i*hessianMatrix K x.val i j*z j) =
      (∑ i,∑ j,z i*hessianMatrix F x.val i j*z j)+(∑ i,∑ j,z i*P i j*z j)+
      (∑ i,∑ j,z i*Q i j*z j)-p.val.1*(∑ i,∑ j,z i*ProbabilityTheory.covariance (Xi i) (Xi j) μ*z j) := by
    simp_rw [he']
    simp only [mul_sub,sub_mul,mul_add,add_mul,Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.mul_sum,mul_assoc,mul_left_comm]
  rw [(paperFrozenMatrices_on_event p n m U θ h b D x hx).1,hquad]
  have hPquad := hSchur P (D*S) hProw hPcol
  have hQquad := hSchur Q D hQrow hQcol
  nlinarith [mul_nonneg p.property.1.le hcov]

end Riesz2.DecayShort
