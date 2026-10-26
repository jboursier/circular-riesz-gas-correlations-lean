/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.PaperGoodEventMoments
public import Riesz2.DecayShort.PaperPhysicalComparisonPart2
import all Riesz2.DecayShort.ExceptionalEventPart4

/-!
# The paper's fourth-moment argument

Step 4 of Lemma 4.8 estimates covariance entries by the two
compensated variances, before summing the entrywise fourth moments.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal ContDiff Topology

namespace Riesz2.DecayShort
open ConditionalScores PhysicalComparison ExceptionalEvent

/-- Internal entrywise covariance estimate in Step 4 of Lemma 4.8. -/
theorem internal_paper_covariance_le_variances {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F G : Ω → ℝ)
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    |ProbabilityTheory.covariance F G μ| ≤
      (∫ z, (F z-∫ y,F y ∂μ)^2 ∂μ)+(∫ z, (G z-∫ y,G y ∂μ)^2 ∂μ) := by
  have hf : 0 ≤ ∫ z, (F z-∫ y,F y ∂μ)^2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hg : 0 ≤ ∫ z, (G z-∫ y,G y ∂μ)^2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  apply (internal_abs_covariance_le hF hG).trans
  nlinarith [sq_nonneg (Real.sqrt (∫ z, (F z-∫ y,F y ∂μ)^2 ∂μ)-
    Real.sqrt (∫ z, (G z-∫ y,G y ∂μ)^2 ∂μ)),Real.sq_sqrt hf,Real.sq_sqrt hg,
    mul_nonneg (Real.sqrt_nonneg (∫ z, (F z-∫ y,F y ∂μ)^2 ∂μ))
      (Real.sqrt_nonneg (∫ z, (G z-∫ y,G y ∂μ)^2 ∂μ))]

set_option backward.isDefEq.respectTransparency false in
/-- Operator fourth moments from the entrywise compensated-variance argument
in Step 4 of the proof of Lemma 4.8. -/
theorem paper_hessian_fourth_moments (s : ℝ) (hs : 1 < s)
    (θ : PhysicalCutoff) (βlo βhi h : ℝ)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (hh : 0 < h) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ (n : ℕ+) (m : ℕ) (hn : (n : ℕ) ≤ (((n : ℕ)+m).succPNat : ℕ)),
      2 ≤ (n : ℕ)+m+1 → 2*(n : ℕ) ≤ (n : ℕ)+m+1 → ∀ b : Bool,
      let F := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
        ∑ i,(θ.val (((n : ℝ)^h)⁻¹*x i)+if b then θ.val (((n : ℝ)^h)⁻¹*(x i)⁻¹) else 0)
      let K := fun x => p.val.1⁻¹*(p.val.1*F x-Real.log
        (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal))
      let μ := (activeTiltedGapLaw p ((n : ℕ)+m).succPNat n hn θ h b).comap
        ((↑) : AffineSimplex.chartDomain n ((n+m : ℕ)+1) → EuclideanSpace ℝ (Fin (n : ℕ)))
      let T := fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) => ‖fderiv ℝ (fderiv ℝ K) x.val‖
      Measurable T ∧ MemLp T 4 μ ∧ eLpNorm T 4 μ ≤ ENNReal.ofReal (C*(n : ℝ)^2) := by
  classical
  obtain ⟨Cp,hCp,hpen⟩ := internal_penalty_diagonal θ
  obtain ⟨Ci,hCi,hinv⟩ := active_inverse_fourth_moments s hs θ βlo βhi h hlo hle hh
  obtain ⟨d,_,hm⟩ := interval_counting_coefficient_moments s hs
  obtain ⟨M,hM,hcoeff⟩ := hm θ βlo βhi h hlo hle hh
  obtain ⟨dv,_,hv⟩ := paper_compensated_variance_moments s hs
  obtain ⟨Mv,hMv,hvmom⟩ := hv θ βlo βhi h hlo hle hh
  let L := M*(4 : ℝ)^d
  let V := 2*Mv*(4 : ℝ)^dv
  let C := Cp*(1+Ci)+L+3*L+βhi*(V+V)
  have hL : 0 < L := by dsimp only [L]; positivity
  have hV : 0 < V := by dsimp only [V]; positivity
  have hβhi : 0 < βhi := hlo.trans_le hle
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro p hp hpl hph n m hn hN hhalf b F K μ T
  let _ : IsProbabilityMeasure μ := activeTilt_proper_probability p n m hn θ h b
  obtain ⟨U,_,hu,_⟩ := MarginalHessian.physical_energy_tensors p ((n : ℕ)+m).succPNat
  change (EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ) at U
  have hK := (PhysicalFibres.active_marginal_curvature p (by simpa only [hp] using hs)
    n m n.pos (Equiv.refl _) θ h hh b).1
  have hT : Measurable T := by
    apply Continuous.measurable
    apply continuous_iff_continuousAt.mpr
    intro x
    have hx := hK.contDiffAt ((AffineSimplex.isOpen_chartDomain n _).mem_nhds x.property)
    exact ((hx.fderiv_right (m := 2) (by norm_num)).continuousAt_fderiv (by norm_num)).norm.comp
      continuous_subtype_val.continuousAt
  let P := fun i j x => IntervalBoundary.intervalMatrix ((n : ℕ)+m).succPNat n hn
    (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x) i j
  let Q := fun i j x => paperCompensationEntry p n m x i j
  let B := fun i x => paperCompensatedVariance p n m U x i
  let G := fun (ij : Fin (n : ℕ) × Fin (n : ℕ))
    (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1)) =>
    Cp*(1+(x.val ij.2)⁻¹^4)+P ij.2 ij.1 x+|Q ij.2 ij.1 x|+p.val.1*(B ij.2 x+B ij.1 x)
  have hpoint (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1)) : T x ≤ ∑ ij, G ij x := by
    have hKx : ContDiffAt ℝ 2 K x.val := (hK.contDiffAt ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds x.property)).of_le (by norm_num)
    have ha : 0 < ((n : ℝ)^h)⁻¹ := by positivity
    have ha1 : ((n : ℝ)^h)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_rpow (by exact_mod_cast n.pos) hh.le)
    have hFx := penalty_contDiffAt n θ ha b x.val x.property.1
    have hFabs (i j) : |hessianMatrix F x.val i j| ≤ Cp*(1+(x.val i)⁻¹^4) := by
      by_cases hij : i=j
      · subst j
        have hconv := penalty_smooth_convex n ((n+m : ℕ)+1) θ ha b
        have hn : 0 ≤ hessianMatrix F x.val i i := by
          rw [hessianMatrix_entry hFx]
          exact Riesz1.fderiv_fderiv_nonneg_of_convexOn (AffineSimplex.isOpen_chartDomain _ _)
            hconv.2.1 hconv.2 (hconv.1.of_le (by norm_num)) x.property _
        rw [abs_of_nonneg hn,hessianMatrix_entry hFx]
        exact hpen n _ ha ha1 b x.val x.property.1 i
      · rw [penalty_hessian_off_diagonal n θ ha b x.val x.property.1 i j hij,abs_zero]
        positivity
    have he := internal_paper_marginal_hessian_entries p n m θ h b U hu x
    let ρ := ProperMarginalChart.conditionalMeasure p n m n.pos (Equiv.refl _) x
    let _ := ProperMarginalChart.conditionalMeasure_probability p n m n.pos (Equiv.refl _) x
    have hentry (i j) : |hessianMatrix K x.val i j| ≤
        Cp*(1+(x.val i)⁻¹^4)+P i j x+|Q i j x|+p.val.1*(B i x+B j x) := by
      have ht := he i j
      have he' : hessianMatrix K x.val i j = hessianMatrix F x.val i j+P i j x+Q i j x-
          p.val.1*ProbabilityTheory.covariance (paperCompensatedScore p n m U x i)
            (paperCompensatedScore p n m U x j) ρ := by
        dsimp only [F,K,Q,paperCompensationEntry,P,paperCompensatedScore,ρ,Nat.succPNat_coe] at ht ⊢
        rw [ht]
        delta paperCompensatedScore
        simp only [Nat.succ_eq_add_one]
        ring
      have hc := internal_paper_covariance_le_variances ρ _ _
        (paperCompensatedScore_memLp p n m hN hhalf U hu x i)
        (paperCompensatedScore_memLp p n m hN hhalf U hu x j)
      rw [he']
      apply (abs_sub _ _).trans
      rw [abs_mul,abs_of_pos p.property.1]
      have hP : 0 ≤ P i j x := IntervalBoundary.intervalMatrix_nonneg _ _ hn _
        (conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x) i j
      have hsmall := (abs_add_le (hessianMatrix F x.val i j+P i j x) (Q i j x)).trans
        (add_le_add ((abs_add_le _ _).trans (add_le_add (hFabs i j) (by rw [abs_of_nonneg hP]))) le_rfl)
      exact add_le_add hsmall (mul_le_mul_of_nonneg_left hc p.property.1.le)
    apply (norm_le_sum_entries (fderiv ℝ (fderiv ℝ K) x.val)).trans
    rw [Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    rw [← hessianMatrix_entry hKx j i]
    exact hentry j i
  have hG (ij : Fin (n : ℕ) × Fin (n : ℕ)) : eLpNorm (G ij) 4 μ ≤ ENNReal.ofReal C := by
    obtain ⟨hP,_,_,hbc⟩ := (hcoeff p hp hpl hph).1 n m hn hhalf b |>.2.2 4 (by norm_num)
    norm_num only [ENNReal.ofReal_ofNat] at hP hbc
    have hPbound (i j) : eLpNorm (P i j) 4 μ ≤ ENNReal.ofReal L := by
      apply (hP i j).2.trans
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_of_le_one_right hL.le (Real.rpow_le_one_of_one_le_of_nonpos
        (le_add_of_nonneg_right (Nat.cast_nonneg _)) (by simpa only [hp] using (show -s ≤ 0 by linarith)))
    have hBbound (i) : eLpNorm (B i) 4 μ ≤ ENNReal.ofReal V := by
      have ht := (hvmom p hp hpl hph n m hn hN hhalf b U hu 4 (by norm_num) i).2
      norm_num only [ENNReal.ofReal_ofNat] at ht
      apply ht.trans
      apply ENNReal.ofReal_le_ofReal
      have hw := Real.rpow_le_one_of_one_le_of_nonpos
        (show (1 : ℝ) ≤ (boundaryDistance i : ℝ) by exact_mod_cast boundaryDistance_pos i)
        (show 1-2*s ≤ 0 by linarith)
      have hn := inv_le_one_of_one_le₀ (show (1 : ℝ) ≤ ((n : ℕ)+m+1 : ℕ) by exact_mod_cast (show 1 ≤ (n : ℕ)+m+1 by omega))
      dsimp only [V]
      nlinarith [mul_nonneg hMv.le (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) dv)]
    let H := fun x => IntervalBoundary.intervalMatrix ((n : ℕ)+m).succPNat ((n : ℕ)+m+1) le_rfl
      (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
    let S := Finset.univ.filter (fun a : Fin ((n : ℕ)+m+1) => (n : ℕ) ≤ a.val)
    let bi := fun i x => (m+1 : ℝ)⁻¹*∑ a ∈ S,H x (Fin.castLE hn i) a
    let c := fun x => (m+1 : ℝ)⁻¹^2*∑ a ∈ S,∑ b ∈ S,H x a b
    have hbi (i) : eLpNorm (bi i) 4 μ ≤ ENNReal.ofReal L := by
      apply ((le_add_of_nonneg_right (by positivity)).trans (hbc i).2.2.1).trans
      exact ENNReal.ofReal_le_ofReal (div_le_self hL.le (by exact_mod_cast (show 1 ≤ (n : ℕ)+m+1 by omega)))
    have hc : eLpNorm c 4 μ ≤ ENNReal.ofReal L := by
      apply ((le_add_of_nonneg_left (by positivity)).trans (hbc ij.1).2.2.1).trans
      exact ENNReal.ofReal_le_ofReal (div_le_self hL.le (by exact_mod_cast (show 1 ≤ (n : ℕ)+m+1 by omega)))
    have hQ : eLpNorm (fun x => |Q ij.2 ij.1 x|) 4 μ ≤ ENNReal.ofReal (3*L) := by
      have he : Q ij.2 ij.1 = fun x => -bi ij.2 x-bi ij.1 x+c x := by
        funext x
        dsimp only [Q,paperCompensationEntry,bi,c,H,S]
        ring
      simp only [← Real.norm_eq_abs]
      rw [eLpNorm_norm _ (measurable_paperCompensationEntry p n m ij.2 ij.1).aestronglyMeasurable]
      change eLpNorm (Q ij.2 ij.1) 4 μ ≤ ENNReal.ofReal (3*L)
      rw [he]
      apply (eLpNorm_add_le (by norm_num)).trans
      apply (add_le_add ((eLpNorm_sub_le (by norm_num)).trans
        (add_le_add (by
          change eLpNorm (-bi ij.2) 4 μ ≤ ENNReal.ofReal L
          rw [eLpNorm_neg]
          exact hbi ij.2) (hbi ij.1))) hc).trans_eq
      rw [← ENNReal.ofReal_add hL.le hL.le,← ENNReal.ofReal_add (by positivity) hL.le]
      congr 1
      ring
    have hi := (internal_retained_inverse_norm p n m hn θ h b ij.2).trans
      (hinv p hp hpl hph ((n : ℕ)+m).succPNat n hn (by simp only [Nat.succPNat_coe]; omega) b ij.2.val)
    have hone : eLpNorm (fun _ : AffineSimplex.chartDomain n ((n+m : ℕ)+1) => (1 : ℝ)) 4 μ ≤ ENNReal.ofReal 1 := by
      simp [eLpNorm_const',(by norm_num : (4 : ℝ≥0∞) ≠ 0),(by norm_num : (4 : ℝ≥0∞) ≠ ⊤)]
    have hv : eLpNorm (fun x => p.val.1*(B ij.2 x+B ij.1 x)) 4 μ ≤ ENNReal.ofReal (βhi*(V+V)) := by
      apply (scale_four_norm_le μ _ p.property.1.le
        (add_four_norm_le μ _ _ hV.le hV.le (hBbound ij.2) (hBbound ij.1))).trans
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hph (by positivity))
    exact add_four_norm_le μ _ _ (by positivity) (by positivity)
      (add_four_norm_le μ _ _ (by positivity) (by positivity)
        (add_four_norm_le μ _ _ (by positivity) hL.le
          (scale_four_norm_le μ _ hCp.le (add_four_norm_le μ _ _ (by norm_num) hCi.le hone hi))
          (hPbound ij.2 ij.1)) hQ) hv
  have hnorm : eLpNorm T 4 μ ≤ ENNReal.ofReal (C*(n : ℝ)^2) := by
    apply (eLpNorm_mono_real hT.aestronglyMeasurable
      (g := fun x => ∑ ij, G ij x) (fun x => by
        have hTx : 0 ≤ T x := by dsimp only [T]; positivity
        rw [Real.norm_of_nonneg hTx]
        exact hpoint x)).trans
    apply (sum_four_norm_le μ G hC.le hG).trans_eq
    simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
    congr 1
    ring
  exact ⟨hT,hnorm.trans_lt ENNReal.ofReal_lt_top,hnorm⟩

end Riesz2.DecayShort
