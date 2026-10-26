/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.PaperPhysicalComparison
import all Riesz2.HelfferSjostrand.MarginalHessianPart5
import all Riesz2.DecayShort.ExceptionalEventPart4

/-!
# The physical residual on the good event

The boundary, compensation and compensated-score covariance terms
in the proof of Lemma 4.9.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal ContDiff Topology

namespace Riesz2.DecayShort
open PhysicalComparison ConditionalScores
attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false in
/-- Internal all-point compensated Hessian identity for Lemma 4.7,
used in Step 4 of Lemma 4.8 and in Lemma 4.9. -/
theorem internal_paper_marginal_hessian_entries (p : Parameters) (n : ℕ+) (m : ℕ)
    (θ : PhysicalCutoff) (h : ℝ) (b : Bool)
    (W : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ)
    (hw : ∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) //
        y ∈ gapAmbientDomain ((n : ℕ) + m).succPNat},
      W y.val = p.val.1 * physicalAmbientGapEnergy p ((n : ℕ) + m).succPNat y)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    let F := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      ∑ i, (θ.val (((n : ℝ) ^ h)⁻¹ * y i) +
        if b then θ.val (((n : ℝ) ^ h)⁻¹ * (y i)⁻¹) else 0)
    let K := fun y => p.val.1⁻¹ * (p.val.1 * F y -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,z)).toReal))
    let N := ((n : ℕ) + m).succPNat
    let hn : (n : ℕ) ≤ (N : ℕ) := by change (n : ℕ) ≤ (n : ℕ) + m + 1; omega
    let A := conditionalIntervalWeight p n m n.pos (Equiv.refl _) x
    let H := IntervalBoundary.intervalMatrix N (N : ℕ) le_rfl A
    let S := Finset.univ.filter (fun a : Fin (N : ℕ) => (n : ℕ) ≤ a.val)
    let bi := fun i : Fin (n : ℕ) => (m + 1 : ℝ)⁻¹ * ∑ a ∈ S, H (Fin.castLE hn i) a
    let c := (m + 1 : ℝ)⁻¹ ^ 2 * ∑ a ∈ S, ∑ b ∈ S, H a b
    let μ := ProperMarginalChart.conditionalMeasure p n m n.pos (Equiv.refl _) x
    let q : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) :=
      WithLp.toLp 2 (ConditionalForces.compensationVector n m)
    let Xi := fun (i : Fin (n : ℕ)) z => p.val.1⁻¹ * fderiv ℝ W
      (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z))
        (EuclideanSpace.single (Fin.castLE hn i) 1 - q)
    ∀ i j, hessianMatrix K x.val i j = hessianMatrix F x.val i j +
      IntervalBoundary.intervalMatrix N n hn A i j-bi i-bi j+c-
      p.val.1*ProbabilityTheory.covariance (Xi i) (Xi j) μ := by
  classical
  intro F K N hn A H S bi c μ q Xi
  have ha := inv_pos.mpr (Real.rpow_pos_of_pos (show (0 : ℝ) < n by exact_mod_cast n.pos) h)
  obtain ⟨U,_,hv,hK,hm⟩ := PhysicalFibres.active_marginal_hessian p n m n.pos θ ha b
  obtain ⟨ρ,hρ,hmap,_,_,he⟩ := hm x
  let _ := hρ
  let e := fun i : Fin (n : ℕ) => EuclideanSpace.single (Fin.castLE hn i) (1 : ℝ)
  let q' : EuclideanSpace ℝ (Fin (N : ℕ)) := WithLp.toLp 2
    (Fin.append (fun _ : Fin (n : ℕ) => (0 : ℝ)) (fun _ : Fin (m + 1) => (m + 1 : ℝ)⁻¹))
  have hq' : q' = q := by
    apply PiLp.ext
    intro a
    exact Fin.addCases (m := (n : ℕ)) (n := m + 1)
      (fun i => by simp [q', q, ConditionalForces.compensationVector, i.isLt])
      (fun i => by simp [q', q, ConditionalForces.compensationVector, Fin.val_natAdd]) a
  have hq (a : Fin (N : ℕ)) : q a = if (n : ℕ) ≤ a.val then (m + 1 : ℝ)⁻¹ else 0 := by
    change (if a.val < (n : ℕ) then (0 : ℝ) else (m + 1 : ℝ)⁻¹) = _
    split_ifs <;> first | rfl | omega
  have hmean (u v) := ExceptionalEvent.internal_centred_hessian_mean
    p n m n.pos U hv x ρ hmap u v
  have hee (i j) : (∑ a, ∑ k, e i a * H a k * e j k) =
      IntervalBoundary.intervalMatrix N n hn A i j := by
    simp only [e, EuclideanSpace.single, PiLp.single_apply, mul_ite, mul_one, mul_zero,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact intervalMatrix_restrict N n hn A i j
  have heq (i) : (∑ a, ∑ k, e i a * H a k * q k) = bi i := by
    simp only [e, EuclideanSpace.single, PiLp.single_apply,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      Finset.sum_ite_irrel, Finset.sum_const_zero]
    simp only [hq, bi, S, Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> ring
  have hqq : (∑ a, ∑ k, q a * H a k * q k) = c := by
    simp only [hq, c, S, Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs
    · apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> ring
    · simp
  have hKx : ContDiffAt ℝ 2 K x.val :=
    (hK.contDiffAt ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds x.property)).of_le (by norm_num)
  have hFx := penalty_contDiffAt n θ ha b x.val x.property.1
  intro i j
  have hf := he i j
  rw [hmean, hmean, hmean, hmean] at hf
  change fderiv ℝ (fderiv ℝ K) x.val (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
    fderiv ℝ (fderiv ℝ F) x.val (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
    (∑ a, ∑ k, e i a * H a k * e j k) - (∑ a, ∑ k, e i a * H a k * q' k) -
    (∑ a, ∑ k, e j a * H a k * q' k) + (∑ a, ∑ k, q' a * H a k * q' k) -
    p.val.1 * ProbabilityTheory.covariance
      (fun z => p.val.1⁻¹ * (fderiv ℝ U
        (MarginalHessian.compensatedChart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) (e i) -
        fderiv ℝ U (MarginalHessian.compensatedChart n m ((n + m : ℕ) + 1)
          (Equiv.refl _) (x.val,z)) q'))
      (fun z => p.val.1⁻¹ * (fderiv ℝ U
        (MarginalHessian.compensatedChart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) (e j) -
        fderiv ℝ U (MarginalHessian.compensatedChart n m ((n + m : ℕ) + 1)
          (Equiv.refl _) (x.val,z)) q')) ρ at hf
  simp only [hq', hee, heq] at hf
  dsimp only [N, Nat.succPNat_coe] at hqq hf
  rw [hqq] at hf
  simp_rw [← map_sub] at hf
  rw [internal_shifted_score_covariance p n m n.pos U W
    (fun y => (hv y).trans (hw y).symm) x ρ hmap] at hf
  rw [hessianMatrix_entry hKx,hessianMatrix_entry hFx,
    hKx.isSymmSndFDerivAt (by norm_num) (EuclideanSpace.single j 1) (EuclideanSpace.single i 1),
    hFx.isSymmSndFDerivAt (by norm_num) (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)]
  exact hf

set_option backward.isDefEq.respectTransparency false in
/-- Exact boundary, compensation and covariance residual in the proof of
Lemma 4.9, using equation (4.13) literally. -/
theorem paper_frozen_difference_decomposition (p : Parameters) (n : ℕ+) (m : ℕ)
    (θ : PhysicalCutoff) (h : ℝ) (b : Bool) (D : ℝ)
    (W : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ)
    (hw : ∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) //
        y ∈ gapAmbientDomain ((n : ℕ) + m).succPNat},
      W y.val = p.val.1 * physicalAmbientGapEnergy p ((n : ℕ) + m).succPNat y)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    let N := ((n : ℕ) + m).succPNat
    let hn : (n : ℕ) ≤ (N : ℕ) := by change (n : ℕ) ≤ (n : ℕ) + m + 1; omega
    let A := conditionalIntervalWeight p n m n.pos (Equiv.refl _) x
    let B := IntervalBoundary.boundaryMatrix N n hn A
    let H := IntervalBoundary.intervalMatrix N (N : ℕ) le_rfl A
    let S := Finset.univ.filter (fun a : Fin (N : ℕ) => (n : ℕ) ≤ a.val)
    let bi := fun i : Fin (n : ℕ) => (m + 1 : ℝ)⁻¹ * ∑ a ∈ S, H (Fin.castLE hn i) a
    let c := (m + 1 : ℝ)⁻¹ ^ 2 * ∑ a ∈ S, ∑ b ∈ S, H a b
    let μ := ProperMarginalChart.conditionalMeasure p n m n.pos (Equiv.refl _) x
    let q : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) :=
      WithLp.toLp 2 (ConditionalForces.compensationVector n m)
    let Xi := fun (i : Fin (n : ℕ)) z => p.val.1⁻¹ * fderiv ℝ W
      (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z))
        (EuclideanSpace.single (Fin.castLE hn i) 1 - q)
    ∀ i j, (paperFrozenPhysicalMatrix p n m W θ h b D x -
      paperFrozenInteriorMatrix p n m W θ h b D x) i j =
      if x ∈ paperProperGoodEvent p n m W h D then
        B i j - bi i - bi j + c - p.val.1 * ProbabilityTheory.covariance (Xi i) (Xi j) μ
      else 0 := by
  classical
  intro N hn A B H S bi c μ q Xi
  let F := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
    ∑ i, (θ.val (((n : ℝ) ^ h)⁻¹ * y i) +
      if b then θ.val (((n : ℝ) ^ h)⁻¹ * (y i)⁻¹) else 0)
  let K := fun y => p.val.1⁻¹ * (p.val.1 * F y -
    Real.log (∫ z : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,z)).toReal))
  have he := internal_paper_marginal_hessian_entries p n m θ h b W hw x
  intro i j
  by_cases hx : x ∈ paperProperGoodEvent p n m W h D
  · rw [ite_eq_left hx]
    change (if x ∈ paperProperGoodEvent p n m W h D then hessianMatrix K x.val else 1) i j-
      (if x ∈ paperProperGoodEvent p n m W h D then
        hessianMatrix F x.val+IntervalBoundary.internalMatrix N n hn A else 1) i j = _
    rw [ite_eq_left hx,ite_eq_left hx,Matrix.add_apply,he i j,← IntervalBoundary.internal_add_boundary]
    simp only [Matrix.add_apply]
    ring
  · rw [ite_eq_right hx,(paperFrozenMatrices_off_event p n m W θ h b D x hx).1,
      (paperFrozenMatrices_off_event p n m W θ h b D x hx).2,sub_self,Matrix.zero_apply]

/-- The matrix verification following equation (4.13).
 Uniform diagonal penalty bound on the actual good event, with a
polynomial loss and no factor of the component cardinality (Subsection 4.5). -/
theorem internal_paper_penalty_bound (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Parameters) (n : ℕ+) (m : ℕ)
      (U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ) (h : ℝ), 0 < h →
      ∀ (b : Bool) (D : ℝ) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)),
      x ∈ paperProperGoodEvent p n m U h D → ∀ i : Fin (n : ℕ),
      let F := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
        ∑ k, (θ.val (((n : ℝ) ^ h)⁻¹ * y k) +
          if b then θ.val (((n : ℝ) ^ h)⁻¹ * (y k)⁻¹) else 0)
      |hessianMatrix F x.val i i| ≤ C * (n : ℝ) ^ (4 * h) := by
  obtain ⟨C,hC,hdiag⟩ := ExceptionalEvent.internal_penalty_diagonal θ
  refine ⟨2 * C, by positivity, ?_⟩
  intro p n m U h hh b D x hx i F
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have ha := inv_pos.mpr (Real.rpow_pos_of_pos hn0 h)
  have ha1 : ((n : ℝ) ^ h)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_rpow hn1 hh.le)
  have hFx := penalty_contDiffAt n θ ha b x.val x.property.1
  have hnonneg : 0 ≤ hessianMatrix F x.val i i := by
    rw [hessianMatrix_entry hFx]
    have hconv := (ExceptionalEvent.penalty_smooth_convex n ((n + m : ℕ) + 1) θ ha b).2
    exact Riesz1.fderiv_fderiv_nonneg_of_convexOn (AffineSimplex.isOpen_chartDomain _ _)
      hconv.1 hconv ((ExceptionalEvent.penalty_smooth_convex n ((n + m : ℕ) + 1) θ ha b).1.of_le
        (by norm_num)) x.property _
  rw [abs_of_nonneg hnonneg, hessianMatrix_entry hFx]
  have hlower : (n : ℝ) ^ (-h) ≤ x.val i := (hx.1.2.1 i).1
  have hi : (x.val i)⁻¹ ≤ (n : ℝ) ^ h := by
    have he : (n : ℝ) ^ (-h) = ((n : ℝ) ^ h)⁻¹ := Real.rpow_neg hn0.le h
    rw [he] at hlower
    have hb := inv_le_inv₀ (x.property.1 i) (inv_pos.mpr (Real.rpow_pos_of_pos hn0 h))
    simpa only [inv_inv] using hb.mpr hlower
  have h4 : (x.val i)⁻¹ ^ 4 ≤ (n : ℝ) ^ (4 * h) := by
    have hb := pow_le_pow_left₀ (inv_nonneg.mpr (x.property.1 i).le) hi 4
    calc
      _ ≤ ((n : ℝ) ^ h) ^ 4 := hb
      _ = (n : ℝ) ^ (4 * h) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
        congr 1
        ring
  have hpow : 1 ≤ (n : ℝ) ^ (4 * h) := Real.one_le_rpow hn1 (by linarith)
  exact (hdiag n _ ha ha1 b x.val x.property.1 i).trans (by nlinarith)

/-- The matrix verification following equation (4.13).
 Complete ordinary-distance entry estimate for the auxiliary internal
matrix in Subsection 4.5, including the diagonal penalty and the
prescribed exceptional value. The constant precedes all sizes and scales. -/
theorem paperFrozenInteriorMatrix_entry_bound (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Parameters) (n : ℕ+) (m : ℕ)
      (U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ),
      2 * (n : ℕ) ≤ (n : ℕ) + m + 1 → ∀ h : ℝ, 0 < h → ∀ (b : Bool) (D : ℝ),
      0 ≤ D → ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (i j : Fin (n : ℕ)),
        |paperFrozenInteriorMatrix p n m U θ h b D x i j| ≤
          (1 + D + C * (n : ℝ) ^ (4 * h)) *
            (1 + |(i.val : ℝ) - (j.val : ℝ)|) ^ (-p.val.2) := by
  classical
  obtain ⟨C,hC,hpen⟩ := internal_paper_penalty_bound θ
  refine ⟨C,hC,?_⟩
  intro p n m U hhalf h hh b D hD x i j
  let F := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
    ∑ k, (θ.val (((n : ℝ) ^ h)⁻¹ * y k) +
      if b then θ.val (((n : ℝ) ^ h)⁻¹ * (y k)⁻¹) else 0)
  let N := ((n : ℕ) + m).succPNat
  have hn : (n : ℕ) ≤ (N : ℕ) := by change (n : ℕ) ≤ (n : ℕ) + m + 1; omega
  let I := IntervalBoundary.internalMatrix N n hn
    (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
  let r := (1 + |(i.val : ℝ) - (j.val : ℝ)|) ^ (-p.val.2)
  have hr : 0 ≤ r := Real.rpow_nonneg (by positivity) _
  by_cases hx : x ∈ paperProperGoodEvent p n m U h D
  · have hIb : |I i j| ≤ D * r := by
      rw [abs_of_nonneg (IntervalBoundary.internalMatrix_nonneg N n hn _
        (conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x) i j)]
      apply (IntervalBoundary.internalMatrix_le_intervalMatrix N n hn _
        (conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x) i j).trans
      have he := hx.2.1 i j
      rw [properBlock_distance N n hn (by simpa only [N, Nat.succPNat_coe] using hhalf)] at he
      exact he
    have hFb : |hessianMatrix F x.val i j| ≤ C * (n : ℝ) ^ (4 * h) * r := by
      by_cases hij : i = j
      · subst j
        simpa only [r, sub_self, abs_zero, add_zero, Real.one_rpow, mul_one] using
          hpen p n m U h hh b D x hx i
      · rw [penalty_hessian_off_diagonal n θ
          (inv_pos.mpr (Real.rpow_pos_of_pos (show (0 : ℝ) < n by exact_mod_cast n.pos) h))
          b x.val x.property.1 i j hij, abs_zero]
        positivity
    change |(if x ∈ paperProperGoodEvent p n m U h D then
      hessianMatrix F x.val + I else 1) i j| ≤ _
    rw [ite_eq_left hx, Matrix.add_apply]
    calc
      _ ≤ |hessianMatrix F x.val i j| + |I i j| := abs_add_le _ _
      _ ≤ C * (n : ℝ) ^ (4 * h) * r + D * r := add_le_add hFb hIb
      _ ≤ (1 + D + C * (n : ℝ) ^ (4 * h)) * r := by nlinarith
  · rw [(paperFrozenMatrices_off_event p n m U θ h b D x hx).2]
    by_cases hij : i = j
    · subst j
      simp only [Matrix.one_apply_eq, sub_self, abs_zero, add_zero, Real.one_rpow, mul_one, abs_one]
      nlinarith [mul_nonneg hC.le (Real.rpow_nonneg (show (0 : ℝ) ≤ n by positivity) (4 * h))]
    · simp only [Matrix.one_apply_ne hij, abs_zero]
      positivity

end Riesz2.DecayShort
