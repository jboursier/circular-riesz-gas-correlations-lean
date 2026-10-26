/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.PaperGoodEventPart2

/-!
# Compensated variance moments for the short-range good event

Step 3 of Lemma 4.8 combines the two physical Brascamp–Lieb
bounds with the coefficient and exterior-energy moments.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal ContDiff Topology

namespace Riesz2.DecayShort
open ConditionalScores

set_option backward.isDefEq.respectTransparency false in
/-- The compensated-score variance moment display in Step 3 of
Lemma 4.8. The moment degree depends only on `s`. The prefactor
is common on each compact positive temperature interval and for both tilts. -/
theorem paper_compensated_variance_moments (s : ℝ) (hs : 1 < s) :
    ∃ d : ℝ, 0 < d ∧ ∀ (θ : PhysicalCutoff) (βlo βhi h : ℝ),
      0 < βlo → βlo ≤ βhi → 0 < h →
      ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (n : ℕ+) (m : ℕ)
      (hn : (n : ℕ) ≤ (((n : ℕ)+m).succPNat : ℕ)),
      2 ≤ (n : ℕ)+m+1 → 2*(n : ℕ) ≤ (n : ℕ)+m+1 → ∀ b : Bool,
      ∀ (U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ),
      (∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) //
        y ∈ gapAmbientDomain ((n : ℕ)+m).succPNat},
        U y.val = p.val.1 * physicalAmbientGapEnergy p ((n : ℕ)+m).succPNat y) →
      ∀ (q : ℝ), 1 ≤ q → ∀ i : Fin (n : ℕ),
      let μ := (activeTiltedGapLaw p ((n : ℕ)+m).succPNat n hn θ h b).comap
        ((↑) : AffineSimplex.chartDomain n ((n+m : ℕ)+1) → EuclideanSpace ℝ (Fin (n : ℕ)))
      MemLp (fun x => paperCompensatedVariance p n m U x i) (ENNReal.ofReal q) μ ∧
      eLpNorm (fun x => paperCompensatedVariance p n m U x i) (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal (C*q^d*((boundaryDistance i : ℝ)^(1-2*s)+
          (((n : ℕ)+m+1 : ℕ) : ℝ)⁻¹)) := by
  obtain ⟨d,hd,hmom⟩ := interval_counting_coefficient_moments s hs
  refine ⟨d,hd,fun θ βlo βhi h hlo hle hh => ?_⟩
  obtain ⟨C₀,hC₀,hmom⟩ := hmom θ βlo βhi h hlo hle hh
  let α := βlo*(2*(s*(s+1)))
  let K := 2*α⁻¹+2*βlo⁻¹
  have hα : 0 < α := by dsimp only [α]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K*C₀,mul_pos hK hC₀,?_⟩
  intro p hp hpl hph n m hn hN hhalf b U hv q hq i μ
  subst s
  let H := fun x => IntervalBoundary.intervalMatrix ((n : ℕ)+m).succPNat
    ((n : ℕ)+m+1) le_rfl (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
  let S := Finset.univ.filter (fun a : Fin ((n : ℕ)+m+1) => (n : ℕ) ≤ a.val)
  let c := fun x => (m+1 : ℝ)⁻¹^2*∑ a ∈ S, ∑ b ∈ S, H x a b
  let V := fun x => (PhysicalFibres.exteriorGradientEnergy p n m n.pos x i).toReal
  let f := fun x => paperCompensatedVariance p n m U x i
  have hf : Measurable f := measurable_paperCompensatedVariance p n m U i
  obtain ⟨_,_,_,hbcV⟩ := ((hmom p rfl hpl hph).1 n m hn hhalf b).2.2 q hq
  have hVnorm := (hbcV i).2.2.2.2
  have hcnorm := (le_add_of_nonneg_left (show (0 : ℝ≥0∞) ≤ _ from zero_le)).trans
    (hbcV i).2.2.1
  change eLpNorm c (ENNReal.ofReal q) μ ≤
    ENNReal.ofReal (C₀*q^d/(((n : ℕ)+m+1 : ℕ) : ℝ)) at hcnorm
  have hβinv := inv_anti₀ hlo hpl
  have hαinv := inv_anti₀ hα (mul_le_mul_of_nonneg_right hpl
    (by positivity : 0 ≤ 2*(p.val.2*(p.val.2+1))))
  have hpt (x) : ‖f x‖ ≤ ‖K*(V x+c x)‖ := by
    have hc : 0 ≤ c x := by
      apply mul_nonneg (sq_nonneg _)
      apply Finset.sum_nonneg
      intro a _
      apply Finset.sum_nonneg
      intro j _
      exact IntervalBoundary.intervalMatrix_nonneg ((n : ℕ)+m).succPNat ((n : ℕ)+m+1) le_rfl
        (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
        (conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x) a j
    have hV : 0 ≤ V x := ENNReal.toReal_nonneg
    have hfv : 0 ≤ f x := integral_nonneg fun _ => sq_nonneg _
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hfv,
      abs_of_nonneg (mul_nonneg hK.le (add_nonneg hV hc))]
    apply (internal_paper_compensated_variance_upper p n m hN hhalf U hv x i).trans
    have h₁ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hαinv (by norm_num : (0 : ℝ) ≤ 2)) hV
    have h₂ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hβinv (by norm_num : (0 : ℝ) ≤ 2)) hc
    have hK₁ : 2*α⁻¹ ≤ K := by dsimp only [K]; linarith [inv_nonneg.mpr hlo.le]
    have hK₂ : 2*βlo⁻¹ ≤ K := by dsimp only [K]; linarith [inv_nonneg.mpr hα.le]
    have h₃ := mul_le_mul_of_nonneg_right hK₁ hV
    have h₄ := mul_le_mul_of_nonneg_right hK₂ hc
    change _ ≤ K*(V x+c x)
    nlinarith only [h₁,h₂,h₃,h₄]
  have hnorm : eLpNorm f (ENNReal.ofReal q) μ ≤ ENNReal.ofReal
      ((K*C₀)*q^d*((boundaryDistance i : ℝ)^(1-2*p.val.2)+
        (((n : ℕ)+m+1 : ℕ) : ℝ)⁻¹)) := by
    apply (eLpNorm_mono hf.aestronglyMeasurable hpt).trans
    change eLpNorm (K • (fun x => V x+c x)) (ENNReal.ofReal q) μ ≤ _
    rw [eLpNorm_const_smul,Real.enorm_eq_ofReal_abs,abs_of_pos hK]
    have hqE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by simpa using ENNReal.ofReal_le_ofReal hq
    have ht := (eLpNorm_add_le hqE).trans (add_le_add hVnorm hcnorm)
    apply (mul_le_mul' le_rfl ht).trans_eq
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul hK.le]
    congr 1
    simp only [div_eq_mul_inv,boundaryDistance]
    ring
  exact ⟨internal_memLp_of_bound μ hf hnorm,hnorm⟩

end Riesz2.DecayShort
