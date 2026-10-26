/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.PhysicalComparisonPart3

/-!
# The paper's short-range good event

The event of equation (4.10) truncates the boundary entries,
compensation entries and variances of the compensated scores directly.
The smooth ambient realization is explicit. The event is independent of it
whenever the realizations agree with the physical energy.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal ContDiff Topology

namespace Riesz2.DecayShort
open ConditionalScores

/-- The physical compensated score `Xi_i` preceding Lemma 4.7
and used in equation (4.10). `U` realizes beta times the energy. -/
def paperCompensatedScore (p : Parameters) (n : ℕ+) (m : ℕ)
    (U : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (i : Fin (n : ℕ))
    (z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  p.val.1⁻¹ * fderiv ℝ U
    (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z))
    (EuclideanSpace.single (Fin.castLE (by omega) i) 1 -
      WithLp.toLp 2 (ConditionalForces.compensationVector n m))

/-- The conditional compensated-score variance of equation (4.10).
The finite conditional second moment is proved separately for physical realizations. -/
def paperCompensatedVariance (p : Parameters) (n : ℕ+) (m : ℕ)
    (U : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (i : Fin (n : ℕ)) : ℝ :=
  let μ := ProperMarginalChart.conditionalMeasure p n m n.pos (Equiv.refl _) x
  ∫ z, (paperCompensatedScore p n m U x i z -
    ∫ y, paperCompensatedScore p n m U x i y ∂μ) ^ 2 ∂μ

/-- The matrix entry `Q_ij` in equation (4.9) and in
equation (4.10), with the uniform exterior compensation vector. -/
def paperCompensationEntry (p : Parameters) (n : ℕ+) (m : ℕ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (i j : Fin (n : ℕ)) : ℝ :=
  let hn : (n : ℕ) ≤ ((n : ℕ) + m).succPNat := by simp; omega
  let H := IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat
    ((n : ℕ) + m + 1) le_rfl (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
  let S := Finset.univ.filter (fun a : Fin ((n : ℕ) + m + 1) => (n : ℕ) ≤ a.val)
  show ℝ from -(m + 1 : ℝ)⁻¹ * (∑ a ∈ S, H (Fin.castLE hn i) a) -
    (m + 1 : ℝ)⁻¹ * (∑ a ∈ S, H (Fin.castLE hn j) a) +
    (m + 1 : ℝ)⁻¹ ^ 2 * ∑ a ∈ S, ∑ b ∈ S, H a b

/-- The boundary-entry profile in equation (4.10), in zero-based
labels: `max(j,k)` in the paper becomes `max(j+1,k+1)`. -/
def paperBoundaryProfile (s : ℝ) {n : ℕ} (i j : Fin n) : ℝ :=
  (max (i.val + 1) (j.val + 1) : ℕ) ^ (-s) +
    (n - min i.val j.val : ℕ) ^ (-s)

/-- The proper-block good event of equation (4.10).
`D` denotes the paper's `C_n`. -/
def paperProperGoodEvent (p : Parameters) (n : ℕ+) (m : ℕ)
    (U : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ) (h D : ℝ) :
    Set (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :=
  let hn : (n : ℕ) ≤ ((n : ℕ) + m).succPNat := by simp; omega
  let A := fun x => conditionalIntervalWeight p n m n.pos (Equiv.refl _) x
  {x | WithLp.ofLp x.val ∈ goodBlockEvent p.val.2 n ((n : ℕ) + m).succPNat h} ∩
  {x | (∀ i j : Fin (n : ℕ),
      IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat n hn (A x) i j ≤
        D * (1 + (Riesz1.cyclicIndexDistance ((n : ℕ) + m).succPNat
          (Fin.castLE hn i) (Fin.castLE hn j) : ℝ)) ^ (-p.val.2)) ∧
    (∀ i j, |paperCompensationEntry p n m x i j| ≤ D / (((n : ℕ) + m + 1 : ℕ) : ℝ)) ∧
    (∀ i j, IntervalBoundary.boundaryMatrix ((n : ℕ) + m).succPNat n hn (A x) i j ≤
      D * paperBoundaryProfile p.val.2 i j) ∧
    (∀ i, paperCompensatedVariance p n m U x i ≤
      D * ((boundaryDistance i : ℝ) ^ (1 - 2 * p.val.2) +
        (((n : ℕ) + m + 1 : ℕ) : ℝ)⁻¹))}

/-- Measurability of `Q` in equation (4.10). -/
theorem measurable_paperCompensationEntry (p : Parameters) (n : ℕ+) (m : ℕ)
    (i j : Fin (n : ℕ)) : Measurable (fun x => paperCompensationEntry p n m x i j) := by
  classical
  unfold paperCompensationEntry
  have hm := measurable_conditional_intervalMatrix p n m n.pos _ le_rfl
  exact (((Finset.measurable_sum _ fun a _ => hm _ a).const_mul _).sub
    ((Finset.measurable_sum _ fun a _ => hm _ a).const_mul _)).add
    ((Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => hm a b).const_mul _)

/-- Joint measurability of the score used in equation (4.10). -/
theorem measurable_paperCompensatedScore (p : Parameters) (n : ℕ+) (m : ℕ)
    (U : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ) (i : Fin (n : ℕ)) :
    Measurable (fun q : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) ×
      EuclideanSpace ℝ (Fin m) => paperCompensatedScore p n m U q.1 i q.2) := by
  exact ((measurable_fderiv_apply_const ℝ U _).comp
    ((RetainedSimplex.continuous_chart n m _ _).measurable.comp
      ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd))).const_mul _

/-- Measurability of the conditional variance in equation (4.10).
This uses the conditional kernel, including its dependence on the retained point. -/
theorem measurable_paperCompensatedVariance (p : Parameters) (n : ℕ+) (m : ℕ)
    (U : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ) (i : Fin (n : ℕ)) :
    Measurable (fun x => paperCompensatedVariance p n m U x i) := by
  let K := ProperMarginalChart.conditionalKernel p n m n.pos (Equiv.refl _)
  have hscore := measurable_paperCompensatedScore p n m U i
  have hmean := (hscore.stronglyMeasurable.integral_kernel_prod_right' (κ := K)).measurable
  have hcent := (hscore.sub (hmean.comp measurable_fst)).pow_const 2
  exact (hcent.stronglyMeasurable.integral_kernel_prod_right' (κ := K)).measurable

set_option backward.isDefEq.respectTransparency false in
/-- Measurability of the event in equation (4.10). -/
theorem measurableSet_paperProperGoodEvent (p : Parameters) (n : ℕ+) (m : ℕ)
    (U : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ) (h D : ℝ) :
    MeasurableSet (paperProperGoodEvent p n m U h D) := by
  classical
  unfold paperProperGoodEvent
  simp only [ofPred_and]
  apply MeasurableSet.inter
  · exact (ExceptionalEvent.measurableSet_goodBlockEvent _ _ _ _).preimage
      (by fun_prop)
  · have hall {I : Type} [Countable I] {P : I →
        AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → Prop}
        (hm : ∀ i, MeasurableSet {x | P i x}) : MeasurableSet {x | ∀ i, P i x} := by
      simpa only [Set.ofPred_forall] using MeasurableSet.iInter hm
    apply MeasurableSet.inter
    · apply hall
      intro i
      apply hall
      intro j
      exact measurableSet_le
        (measurable_conditional_intervalMatrix p n m n.pos _ _ i j) measurable_const
    · apply MeasurableSet.inter
      · apply hall
        intro i
        apply hall
        intro j
        exact measurableSet_le ((measurable_paperCompensationEntry p n m i j).abs) measurable_const
      · apply MeasurableSet.inter
        · apply hall
          intro i
          apply hall
          intro j
          apply measurableSet_le _ measurable_const
          unfold IntervalBoundary.boundaryMatrix
          apply Finset.measurable_sum
          intro t _
          split_ifs
          · exact measurable_const
          · exact (measurable_conditionalIntervalWeight p n m n.pos (Equiv.refl _) t).mul_const _
        · exact hall fun i => measurableSet_le
            (measurable_paperCompensatedVariance p n m U i) measurable_const

/-- Independence of ambient realization for the scores in
equation (4.10), since derivatives agree on the open physical domain. -/
theorem paperCompensatedScore_ae_eq (p : Parameters) (n : ℕ+) (m : ℕ)
    (U W : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ)
    (he : ∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) //
      y ∈ gapAmbientDomain ((n : ℕ) + m).succPNat}, U y.val = W y.val)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (i : Fin (n : ℕ)) :
    paperCompensatedScore p n m U x i =ᵐ[
      ProperMarginalChart.conditionalMeasure p n m n.pos (Equiv.refl _) x]
      paperCompensatedScore p n m W x i :=
  PhysicalComparison.internal_score_extension_ae p n m n.pos U W he x _

/-- The event in equation (4.10) is independent of ambient realization. -/
theorem paperProperGoodEvent_extension_eq (p : Parameters) (n : ℕ+) (m : ℕ)
    (U W : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ)
    (he : ∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) //
      y ∈ gapAmbientDomain ((n : ℕ) + m).succPNat}, U y.val = W y.val) (h D : ℝ) :
    paperProperGoodEvent p n m U h D = paperProperGoodEvent p n m W h D := by
  have hv (x) (i) : paperCompensatedVariance p n m U x i =
      paperCompensatedVariance p n m W x i := by
    have hs := paperCompensatedScore_ae_eq p n m U W he x i
    have hm := integral_congr_ae hs
    dsimp only [paperCompensatedVariance]
    rw [hm]
    apply integral_congr_ae
    filter_upwards [hs] with z hz
    rw [hz]
  ext x
  simp only [paperProperGoodEvent, mem_inter_iff, mem_ofPred_eq, hv]

/-- Finite conditional second moments for the physical `Xi` in
equation (4.12), with an arbitrary realization of beta times the energy. -/
theorem paperCompensatedScore_memLp (p : Parameters) (n : ℕ+) (m : ℕ)
    (hN : 2 ≤ (n : ℕ) + m + 1) (hhalf : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (U : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ)
    (hv : ∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) //
      y ∈ gapAmbientDomain ((n : ℕ) + m).succPNat},
      U y.val = p.val.1 * physicalAmbientGapEnergy p ((n : ℕ) + m).succPNat y)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (i : Fin (n : ℕ)) :
    MemLp (paperCompensatedScore p n m U x i) 2
      (ProperMarginalChart.conditionalMeasure p n m n.pos (Equiv.refl _) x) := by
  by_cases hm0 : m=0
  · subst m
    rw [ProperMarginalChart.conditionalMeasure_point]
    exact memLp_dirac (by finiteness)
  have hm : 1 ≤ m := by omega
  obtain ⟨W,_,hw,hmem⟩ := physical_directional_score_variance p n m n.pos (by have := n.pos; omega) hm
  exact MemLp.ae_eq (paperCompensatedScore_ae_eq p n m W U
    (fun y => (hw y).trans (hv y).symm) x i) (hmem x _).1

/-- The compensated-score covariance estimate in equation (4.12).
It uses the variance condition of the paper event directly. -/
theorem paper_compensated_score_covariance (p : Parameters) (n : ℕ+) (m : ℕ)
    (hN : 2 ≤ (n : ℕ) + m + 1) (hhalf : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (U : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ)
    (hv : ∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) //
      y ∈ gapAmbientDomain ((n : ℕ) + m).succPNat},
      U y.val = p.val.1 * physicalAmbientGapEnergy p ((n : ℕ) + m).succPNat y)
    (h D : ℝ) (hD : 0 ≤ D) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (hx : x ∈ paperProperGoodEvent p n m U h D) (i j : Fin (n : ℕ)) :
    |ProbabilityTheory.covariance (paperCompensatedScore p n m U x i)
      (paperCompensatedScore p n m U x j)
      (ProperMarginalChart.conditionalMeasure p n m n.pos (Equiv.refl _) x)| ≤
      D * (weight p.val.2 i + (((n : ℕ) + m + 1 : ℕ) : ℝ) ^ (-(1/2 : ℝ))) *
        (weight p.val.2 j + (((n : ℕ) + m + 1 : ℕ) : ℝ) ^ (-(1/2 : ℝ))) := by
  let μ := ProperMarginalChart.conditionalMeasure p n m n.pos (Equiv.refl _) x
  let _ := ProperMarginalChart.conditionalMeasure_probability p n m n.pos (Equiv.refl _) x
  let a := (((n : ℕ) + m + 1 : ℕ) : ℝ) ^ (-(1/2 : ℝ))
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hasq : a ^ 2 = (((n : ℕ) + m + 1 : ℕ) : ℝ)⁻¹ := by
    dsimp only [a]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity :
      (0 : ℝ) ≤ ((n : ℕ) + m + 1 : ℕ))]
    norm_num only [Nat.cast_ofNat, show -(1/2 : ℝ) * 2 = -1 by ring, Real.rpow_neg_one]
  have hs (k : Fin (n : ℕ)) : Real.sqrt (paperCompensatedVariance p n m U x k) ≤
      Real.sqrt D * (weight p.val.2 k + a) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (weight_pos _ _).le ha), ?_⟩
    rw [mul_pow, Real.sq_sqrt hD]
    have hb := hx.2.2.2.2 k
    rw [← weight_sq, ← hasq] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left
      (by nlinarith [mul_nonneg (weight_pos p.val.2 k).le ha] :
        weight p.val.2 k ^ 2 + a ^ 2 ≤ (weight p.val.2 k + a) ^ 2) hD)
  have hc := internal_abs_covariance_le (paperCompensatedScore_memLp p n m hN hhalf U hv x i)
    (paperCompensatedScore_memLp p n m hN hhalf U hv x j)
  apply hc.trans
  have hb := mul_le_mul (hs i) (hs j) (Real.sqrt_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (add_nonneg (weight_pos _ _).le ha))
  apply hb.trans_eq
  calc
    _ = Real.sqrt D ^ 2 * (weight p.val.2 i + a) * (weight p.val.2 j + a) := by ring
    _ = _ := by rw [Real.sq_sqrt hD]

end Riesz2.DecayShort
