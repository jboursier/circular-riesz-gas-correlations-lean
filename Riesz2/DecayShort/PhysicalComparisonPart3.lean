/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.PhysicalComparisonPart2
public import Riesz2.ToMathlib.FiniteSchurBounds
import all Riesz2.HelfferSjostrand.MarginalHessianPart5

/-!
# The physical residual in the short-range comparison

Entrywise decomposition of the actual difference in Subsection 4.5.
The shifted exterior law is transported to the existing conditional law. All scores differentiate realizations of the physical energy.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal ContDiff Topology

namespace Riesz2.DecayShort.PhysicalComparison

attribute [local instance] Classical.propDecidable

/-- Internal bridge for Subsection 4.5: two realizations of the ambient energy have the same conditional directional scores. -/
theorem internal_score_extension_ae (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (U W : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ)
    (hv : ∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
        y ∈ gapAmbientDomain (n + m).succPNat}, U y.val = W y.val)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (v : EuclideanSpace ℝ (Fin (n + m + 1))) :
    (fun z => p.val.1⁻¹ * fderiv ℝ U
      (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) v) =ᵐ[
        ProperMarginalChart.conditionalMeasure p n m hn (Equiv.refl _) x]
    (fun z => p.val.1⁻¹ * fderiv ℝ W
      (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) v) := by
  filter_upwards [ConditionalEnergyMoments.physical_conditional_support
    p n m hn (Equiv.refl _) x] with z hz
  let y := PhysicalFibres.configuration n m (Equiv.refl _) x ⟨z,hz⟩
  have he : U =ᶠ[𝓝 y.val] W := by
    filter_upwards [(PhysicalEnergy.isOpen_gapAmbientDomain _).mem_nhds y.property] with a ha
    exact hv ⟨a,ha⟩
  change p.val.1⁻¹ * fderiv ℝ U y.val v = p.val.1⁻¹ * fderiv ℝ W y.val v
  rw [he.fderiv_eq]

/-- Internal covariance bridge for Subsection 4.5. The physical shifted score
covariance equals the covariance of the unshifted conditional scores,
including a change between smooth realizations of the same energy. -/
theorem internal_shifted_score_covariance (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (U W : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ)
    (hv : ∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
        y ∈ gapAmbientDomain (n + m).succPNat}, U y.val = W y.val)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (ρ : Measure (EuclideanSpace ℝ (Fin m)))
    (hmap : ρ.map (fun z => z + AffineSimplex.coordinates m
      (AffineSimplex.centre m (((n + m : ℕ) + 1) - ∑ i, x.val i))) =
        ProperMarginalChart.conditionalMeasure p n m hn (Equiv.refl _) x)
    (v w : EuclideanSpace ℝ (Fin (n + m + 1))) :
    ProbabilityTheory.covariance
      (fun z => p.val.1⁻¹ * fderiv ℝ U
        (MarginalHessian.compensatedChart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) v)
      (fun z => p.val.1⁻¹ * fderiv ℝ U
        (MarginalHessian.compensatedChart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) w) ρ =
    ProbabilityTheory.covariance
      (fun z => p.val.1⁻¹ * fderiv ℝ W
        (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) v)
      (fun z => p.val.1⁻¹ * fderiv ℝ W
        (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) w)
      (ProperMarginalChart.conditionalMeasure p n m hn (Equiv.refl _) x) := by
  let c₀ := AffineSimplex.coordinates m
    (AffineSimplex.centre m (((n + m : ℕ) + 1) - ∑ i, x.val i))
  let μ := ProperMarginalChart.conditionalMeasure p n m hn (Equiv.refl _) x
  let S := fun (A : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ)
    (a : EuclideanSpace ℝ (Fin (n + m + 1))) z => p.val.1⁻¹ * fderiv ℝ A
      (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) a
  have hm (a) : Measurable (S U a) :=
    ((measurable_fderiv_apply_const ℝ U a).comp ((RetainedSimplex.continuous_chart n m _ _).measurable.comp
        (measurable_const.prodMk measurable_id))).const_mul _
  have he (a) : S U a =ᵐ[μ] S W a := internal_score_extension_ae p n m hn U W hv x a
  have hmean (a) : (∫ z, S U a z ∂μ) = ∫ z, S W a z ∂μ := integral_congr_ae (he a)
  have hc : ProbabilityTheory.covariance (S U v) (S U w) μ =
      ProbabilityTheory.covariance (S W v) (S W w) μ := by
    unfold ProbabilityTheory.covariance
    rw [hmean v, hmean w]
    apply integral_congr_ae
    filter_upwards [he v, he w] with z hv hw
    rw [hv, hw]
  have hpush := ProbabilityTheory.covariance_map_fun
    (μ := ρ) (X := S U v) (Y := S U w) (Z := fun z => z+c₀)
    (by rw [hmap]; exact (hm v).aestronglyMeasurable)
    (by rw [hmap]; exact (hm w).aestronglyMeasurable)
    (measurable_id.add_const c₀).aemeasurable
  rw [hmap] at hpush
  rw [← hc, hpush]
  congr 1 <;> funext z <;>
    simp only [S, MarginalHessian.compensatedChart_eq_shift,
      MarginalHessian.compensatedShift, c₀]
    <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- Entrywise physical residual decomposition for Subsection 4.5.
The boundary matrix, exterior coefficients and conditional covariance are
all the existing physical objects. Off the good event the difference is zero.
The supplied ambient realization is required to equal the energy. -/
theorem frozen_difference_decomposition (p : Parameters) (n : ℕ+) (m : ℕ)
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
    ∀ i j, (frozenPhysicalMatrix p n m θ h b D x -
      frozenInternalMatrix p n m θ h b D x) i j =
      if x ∈ ExceptionalEvent.properGoodEvent p n m hn h D then
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
  by_cases hx : x ∈ ExceptionalEvent.properGoodEvent p n m hn h D
  · rw [ite_eq_left hx]
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
    have hf' : hessianMatrix K x.val i j = hessianMatrix F x.val i j +
        IntervalBoundary.intervalMatrix N n hn A i j - bi i - bi j + c -
        p.val.1 * ProbabilityTheory.covariance (Xi i) (Xi j) μ := by
      rw [hessianMatrix_entry hKx, hessianMatrix_entry hFx,
        hKx.isSymmSndFDerivAt (by norm_num) (EuclideanSpace.single j 1) (EuclideanSpace.single i 1),
        hFx.isSymmSndFDerivAt (by norm_num) (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)]
      exact hf
    change (if x ∈ ExceptionalEvent.properGoodEvent p n m hn h D then hessianMatrix K x.val else 1) i j -
      (if x ∈ ExceptionalEvent.properGoodEvent p n m hn h D then
        hessianMatrix F x.val + IntervalBoundary.internalMatrix N n hn A else 1) i j = _
    rw [ite_eq_left hx, ite_eq_left hx, Matrix.add_apply, hf', ← IntervalBoundary.internal_add_boundary]
    simp only [Matrix.add_apply]
    ring
  · rw [ite_eq_right hx, (frozenMatrices_off_event p n m θ h b D x hx).1,
      (frozenMatrices_off_event p n m θ h b D x hx).2, sub_self, Matrix.zero_apply]


set_option backward.isDefEq.respectTransparency false in
/-- Deterministic entry envelope for the actual residual in Subsection 4.5. It retains the boundary matrix and all four score-covariance
profiles. It is valid for either penalty on the entire positive carrier. -/
theorem frozen_difference_entry_bound (p : Parameters) (hs : 1 < p.val.2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ+) (m : ℕ),
      4 ≤ (n : ℕ) + m + 1 → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (θ : PhysicalCutoff) (h : ℝ) (b : Bool) (D : ℝ), 0 ≤ D →
      ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (i j : Fin (n : ℕ)),
      let hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ) := by
        change (n : ℕ) ≤ (n : ℕ) + m + 1; omega
      let B := IntervalBoundary.boundaryMatrix ((n : ℕ) + m).succPNat n hn
        (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
      let N : ℝ := ((n : ℕ) + m + 1 : ℕ)
      let w := ConditionalScores.weight p.val.2
      |(frozenPhysicalMatrix p n m θ h b D x - frozenInternalMatrix p n m θ h b D x) i j -
        (if x ∈ ExceptionalEvent.properGoodEvent p n m hn h D then B i j else 0)| ≤
        3 * D / N + p.val.1 * C * D *
          (w i * w j + N ^ (-(1 / 2 : ℝ)) * (w i + w j) + N⁻¹) ∧
      |(frozenPhysicalMatrix p n m θ h b D x - frozenInternalMatrix p n m θ h b D x) i j| ≤
        (if x ∈ ExceptionalEvent.properGoodEvent p n m hn h D then B i j else 0) +
        3 * D / N + p.val.1 * C * D *
          (w i * w j + N ^ (-(1 / 2 : ℝ)) * (w i + w j) + N⁻¹) := by
  classical
  obtain ⟨C,hC,hscore⟩ := ConditionalScores.conditional_score_bounds p hs
  refine ⟨C,hC,?_⟩
  intro n m hN hhalf θ h b D hD x i j hn B N w
  have hN0 : 0 < N := by dsimp only [N]; positivity
  have hrest : 0 ≤ 3 * D / N + p.val.1 * C * D *
      (w i * w j + N ^ (-(1 / 2 : ℝ)) * (w i + w j) + N⁻¹) := by
    have hi := (ConditionalScores.weight_pos p.val.2 i).le
    have hj := (ConditionalScores.weight_pos p.val.2 j).le
    have hβ := p.property.1.le
    positivity
  by_cases hx : x ∈ ExceptionalEvent.properGoodEvent p n m hn h D
  swap
  · rw [(frozenMatrices_off_event p n m θ h b D x hx).1,
      (frozenMatrices_off_event p n m θ h b D x hx).2, sub_self, Matrix.zero_apply,
      abs_zero, ite_eq_right hx, zero_add]
    simpa only [sub_zero, abs_zero] using And.intro hrest hrest
  obtain ⟨U,_,hv,hsc⟩ := hscore n m hN hhalf
  let μ := ProperMarginalChart.conditionalMeasure p n m n.pos (Equiv.refl _) x
  let e : Fin (n : ℕ) → EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) :=
    fun k => EuclideanSpace.single (Fin.castLE hn k) (1 : ℝ)
  let q : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) :=
    WithLp.toLp 2 (ConditionalForces.compensationVector n m)
  let F := fun k z => p.val.1⁻¹ * fderiv ℝ U
    (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) (e k)
  let G := fun z => p.val.1⁻¹ * fderiv ℝ U
    (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) q
  let H := IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat ((n : ℕ) + m + 1) le_rfl
    (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
  let S := Finset.univ.filter (fun a : Fin ((n : ℕ) + m + 1) => (n : ℕ) ≤ a.val)
  let bi := fun k : Fin (n : ℕ) => (m + 1 : ℝ)⁻¹ * ∑ a ∈ S, H (Fin.castLE hn k) a
  let c := (m + 1 : ℝ)⁻¹ ^ 2 * ∑ a ∈ S, ∑ b ∈ S, H a b
  have hsc' := hsc x
  change (∀ k, MemLp (F k) 2 μ ∧ _) ∧ MemLp G 2 μ ∧ _ ∧ _ at hsc'
  obtain ⟨hF,hG,_,hb⟩ := hsc'
  obtain ⟨hFF,hFG,hGG⟩ := hb D hD hx.2
  let _ := ProperMarginalChart.conditionalMeasure_probability p n m n.pos (Equiv.refl _) x
  have hcov : |ProbabilityTheory.covariance (F i - G) (F j - G) μ| ≤
      C * D * (w i * w j + N ^ (-(1 / 2 : ℝ)) * (w i + w j) + N⁻¹) := by
    rw [ProbabilityTheory.covariance_sub_sub (hF i).1 hG (hF j).1 hG]
    have hgg : |ProbabilityTheory.covariance G G μ| ≤ C * D / N := by
      have hn : 0 ≤ ProbabilityTheory.covariance G G μ := by
        unfold ProbabilityTheory.covariance
        exact integral_nonneg fun _ => mul_self_nonneg _
      rw [abs_of_nonneg hn]
      simpa only [ProbabilityTheory.covariance, pow_two] using hGG
    have hgf : |ProbabilityTheory.covariance G (F j) μ| ≤ C * D * N ^ (-(1 / 2 : ℝ)) * w j := by
      rw [ProbabilityTheory.covariance_comm]
      exact hFG j
    have ht := (abs_add_le
      (ProbabilityTheory.covariance (F i) (F j) μ - ProbabilityTheory.covariance (F i) G μ -
        ProbabilityTheory.covariance G (F j) μ) (ProbabilityTheory.covariance G G μ)).trans
      (add_le_add ((abs_sub _ _).trans (add_le_add
        ((abs_sub _ _).trans (add_le_add (hFF i j) (hFG i))) hgf)) hgg)
    exact ht.trans_eq (by simp only [div_eq_mul_inv]; ring)
  have hHnn (a k) : 0 ≤ H a k := IntervalBoundary.intervalMatrix_nonneg
    ((n : ℕ) + m).succPNat ((n : ℕ) + m + 1) le_rfl _
    (conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x) a k
  have hbn (k) : 0 ≤ bi k := mul_nonneg (by positivity)
    (Finset.sum_nonneg fun a _ => hHnn _ a)
  have hcn : 0 ≤ c := mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun a _ =>
    Finset.sum_nonneg fun k _ => hHnn a k)
  have hbc (k) : bi k + c ≤ D / N := hx.2.2.2.2.2.1 k
  have hbi (k) : bi k ≤ D / N := (le_add_of_nonneg_right hcn).trans (hbc k)
  have hc : c ≤ D / N := (le_add_of_nonneg_left (hbn i)).trans (hbc i)
  have hQ : |-bi i - bi j + c| ≤ 3 * D / N := by
    calc
      _ ≤ |-bi i - bi j| + |c| := abs_add_le _ _
      _ ≤ |-bi i| + |bi j| + |c| := add_le_add (abs_sub _ _) le_rfl
      _ = bi i + bi j + c := by rw [abs_neg, abs_of_nonneg (hbn i),
          abs_of_nonneg (hbn j), abs_of_nonneg hcn]
      _ ≤ D / N + D / N + D / N := add_le_add (add_le_add (hbi i) (hbi j)) hc
      _ = 3 * D / N := by ring
  have he := frozen_difference_decomposition p n m θ h b D U hv x i j
  change _ = (if x ∈ ExceptionalEvent.properGoodEvent p n m hn h D then
    B i j - bi i - bi j + c - p.val.1 * ProbabilityTheory.covariance
      (fun z => p.val.1⁻¹ * fderiv ℝ U
        (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) (e i - q))
      (fun z => p.val.1⁻¹ * fderiv ℝ U
        (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) (e j - q)) μ else 0) at he
  simp only [ite_eq_left hx, map_sub, mul_sub] at he
  change _ = B i j - bi i - bi j + c -
    p.val.1 * ProbabilityTheory.covariance (F i - G) (F j - G) μ at he
  rw [he, ite_eq_left hx]
  have hBnn := IntervalBoundary.boundaryMatrix_nonneg ((n : ℕ) + m).succPNat n hn _
    (conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x) i j
  have hsmall : |(-bi i - bi j + c) -
      p.val.1 * ProbabilityTheory.covariance (F i - G) (F j - G) μ| ≤
      3 * D / N + p.val.1 * C * D *
        (w i * w j + N ^ (-(1 / 2 : ℝ)) * (w i + w j) + N⁻¹) := by
    have hp : |p.val.1 * ProbabilityTheory.covariance (F i - G) (F j - G) μ| ≤
        p.val.1 * (C * D * (w i * w j + N ^ (-(1 / 2 : ℝ)) * (w i + w j) + N⁻¹)) := by
      rw [abs_mul, abs_of_pos p.property.1]
      exact mul_le_mul_of_nonneg_left hcov p.property.1.le
    exact ((abs_sub _ _).trans (add_le_add hQ hp)).trans_eq (by ring)
  constructor
  · exact (congrArg abs (by ring :
      B i j - bi i - bi j + c - p.val.1 * ProbabilityTheory.covariance (F i - G) (F j - G) μ - B i j =
      (-bi i - bi j + c) - p.val.1 * ProbabilityTheory.covariance (F i - G) (F j - G) μ)).le.trans hsmall
  · calc
      _ = |B i j + ((-bi i - bi j + c) -
          p.val.1 * ProbabilityTheory.covariance (F i - G) (F j - G) μ)| := congrArg abs (by ring)
      _ ≤ |B i j| + |(-bi i - bi j + c) -
          p.val.1 * ProbabilityTheory.covariance (F i - G) (F j - G) μ| := abs_add_le _ _
      _ ≤ B i j + (3 * D / N + p.val.1 * C * D *
          (w i * w j + N ^ (-(1 / 2 : ℝ)) * (w i + w j) + N⁻¹)) := by
        rw [abs_of_nonneg hBnn]
        exact add_le_add le_rfl hsmall
      _ = _ := by ring

/-- Uniform squared boundary-weight mass in Subsection 4.5.
The exponent `2s-1` is summable for precisely the short-range assumption. -/
theorem boundary_weight_square_sum (s : ℝ) (hs : 1 < s) (n : ℕ) :
    ∑ i : Fin n, ConditionalScores.weight s i ^ 2 ≤
      2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(2 * s - 1)) := by
  classical
  let u := 2 * s - 1
  have hu : 1 < u := by dsimp only [u]; linarith
  have hleft : (∑ i : Fin n, (1 + (i.val : ℝ)) ^ (-u)) ≤
      ∑' k : ℕ, (1 + (k : ℝ)) ^ (-u) := by
    exact (Fin.sum_univ_eq_sum_range (fun k : ℕ => (1 + (k : ℝ)) ^ (-u)) n).trans_le
      ((Riesz2.summable_one_add_rpow_neg hu).sum_le_tsum _ (fun k _ => by positivity))
  have hright : (∑ i : Fin n, ((n - i.val : ℕ) : ℝ) ^ (-u)) =
      ∑ i : Fin n, (1 + (i.val : ℝ)) ^ (-u) := by
    rw [← (Equiv.sum_comp (Fin.revPerm (n := n))) (fun i : Fin n => (1 + (i.val : ℝ)) ^ (-u))]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    have hi : n - i.val = (Fin.rev i).val + 1 := by simp only [Fin.val_rev]; omega
    rw [hi, Nat.cast_add, Nat.cast_one, add_comm, Fin.revPerm_apply]
  calc
    _ ≤ ∑ i : Fin n, ((1 + (i.val : ℝ)) ^ (-u) + ((n - i.val : ℕ) : ℝ) ^ (-u)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [ConditionalScores.weight_sq]
      have hexp : 1 - 2 * s = -u := by dsimp [u]; ring
      rw [hexp]
      unfold ConditionalScores.boundaryDistance
      rw [min_def]
      split_ifs
      · simp only [Nat.cast_add, Nat.cast_one]
        rw [add_comm (i.val : ℝ) 1]
        exact le_add_of_nonneg_right (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      · exact le_add_of_nonneg_left (Real.rpow_nonneg (by positivity) _)
    _ ≤ 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-u) := by
      rw [Finset.sum_add_distrib, hright]
      linarith

/-- Bulk/boundary action estimate for the actual crossing matrix in
Subsection 4.5. The boundary part uses the finite Schur
estimate, while bulk columns use their stronger interior bound. -/
theorem boundary_matrix_action_norm (p : Parameters) (hs : 1 < p.val.2)
    (n : ℕ+) (m : ℕ) (hhalf : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (D : ℝ) (hD : 0 ≤ D)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (hx : x ∈ ExceptionalEvent.coefficientEvent p n m
      (by change (n : ℕ) ≤ (n : ℕ) + m + 1; omega) D)
    (z : Fin (n : ℕ) → ℝ) :
    let hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ) := by
      change (n : ℕ) ≤ (n : ℕ) + m + 1; omega
    let B := IntervalBoundary.boundaryMatrix ((n : ℕ) + m).succPNat n hn
      (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
    let S := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-p.val.2)
    let K := 2 * (8 : ℝ) ^ (p.val.2 + 1) + 1
    ‖(WithLp.toLp 2 (fun i => ∑ j, B i j * z j) : EuclideanSpace ℝ (Fin (n : ℕ)))‖ ≤
      K * D * (n : ℝ) ^ (-p.val.2) * (∑ j, |z j|) * Real.sqrt n +
        (D * S) * Real.sqrt (∑ j, if (ConditionalScores.boundaryDistance j : ℝ) < (n : ℝ) / 8
          then z j ^ 2 else 0) := by
  classical
  intro hn B S K
  let zb := fun i : Fin (n : ℕ) => if (n : ℝ) / 8 ≤ (ConditionalScores.boundaryDistance i : ℝ)
    then z i else 0
  let ze := fun i : Fin (n : ℕ) => if (ConditionalScores.boundaryDistance i : ℝ) < (n : ℝ) / 8
    then z i else 0
  let vb : EuclideanSpace ℝ (Fin (n : ℕ)) := WithLp.toLp 2 (fun i => ∑ j, B i j * zb j)
  let ve : EuclideanSpace ℝ (Fin (n : ℕ)) := WithLp.toLp 2 (fun i => ∑ j, B i j * ze j)
  have hz (i) : z i = zb i + ze i := by
    dsimp only [zb,ze]
    by_cases hi : (n : ℝ) / 8 ≤ (ConditionalScores.boundaryDistance i : ℝ)
    · rw [ite_eq_left hi, ite_eq_right (not_lt.mpr hi), add_zero]
    · rw [ite_eq_right hi, ite_eq_left (lt_of_not_ge hi), zero_add]
  have hB (i j) : 0 ≤ B i j := IntervalBoundary.boundaryMatrix_nonneg
    ((n : ℕ) + m).succPNat n hn _
      (conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x) i j
  let L := K * D * (n : ℝ) ^ (-p.val.2)
  let Z := ∑ j, |z j|
  have hL : 0 ≤ L := by dsimp only [L,K]; positivity
  have hZ : 0 ≤ Z := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hb (i : Fin (n : ℕ)) : |vb i| ≤ L * Z := by
    calc
      _ ≤ ∑ j, |B i j * zb j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, L * |z j| := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : (n : ℝ) / 8 ≤ (ConditionalScores.boundaryDistance j : ℝ)
        · simp only [zb, ite_eq_left hj, abs_mul, abs_of_nonneg (hB i j)]
          exact mul_le_mul_of_nonneg_right (boundary_bulk_entries p hs n m hhalf D hD x hx i j hj)
            (abs_nonneg _)
        · simp only [zb, ite_eq_right hj, mul_zero, abs_zero]
          exact mul_nonneg hL (abs_nonneg _)
      _ = L * Z := by rw [← Finset.mul_sum]
  have hbnorm : ‖vb‖ ≤ L * Z * Real.sqrt n := by
    have ht : ‖vb‖ ≤ ‖(WithLp.toLp 2 (fun _ : Fin (n : ℕ) => L * Z) :
        EuclideanSpace ℝ (Fin (n : ℕ)))‖ := by
      rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
        EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
      apply Finset.sum_le_sum
      intro i _
      apply sq_le_sq.mpr
      rw [abs_of_nonneg (mul_nonneg hL hZ)]
      exact hb i
    apply ht.trans_eq
    rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, sq_abs, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [mul_comm (n : ℝ), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hL hZ)]
  obtain ⟨hr,hc⟩ := boundary_schur_bounds p hs n m D hD x hx
  have hDS : 0 ≤ D * S := mul_nonneg hD
    (mul_nonneg (by norm_num) (tsum_nonneg fun _ => by positivity))
  have he := FiniteSchurBounds.sqrt_sum_sq_norm_le (fun i j => B i j) ze hDS hr hc
  have henorm : ‖ve‖ ≤ (D * S) * Real.sqrt (∑ j : Fin (n : ℕ),
      if (ConditionalScores.boundaryDistance j : ℝ) < (n : ℝ) / 8 then z j ^ 2 else 0) := by
    rw [EuclideanSpace.norm_eq]
    simpa only [ve,ze, smul_eq_mul, Real.norm_eq_abs, sq_abs, ite_pow, zero_pow two_ne_zero] using he
  have hsplit : (WithLp.toLp 2 (fun i => ∑ j, B i j * z j) :
      EuclideanSpace ℝ (Fin (n : ℕ))) = vb + ve := by
    apply PiLp.ext
    intro i
    change (∑ j, B i j * z j) = (∑ j, B i j * zb j) + ∑ j, B i j * ze j
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← mul_add, ← hz]
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add hbnorm henorm)

set_option backward.isDefEq.respectTransparency false in
/-- Norm-level contraction of the actual score and exterior remainder in
Subsection 4.5. The boundary matrix is retained separately. The two
terms displayed here contain all four covariance contributions and `Q`.
No probability or scalar-form assumption enters this pointwise estimate. -/
theorem frozen_remainder_action_norm (p : Parameters) (hs : 1 < p.val.2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ+) (m : ℕ),
      4 ≤ (n : ℕ) + m + 1 → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (θ : PhysicalCutoff) (h : ℝ) (b : Bool) (D : ℝ), 0 ≤ D →
      ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (z : Fin (n : ℕ) → ℝ),
      let hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ) := by
        change (n : ℕ) ≤ (n : ℕ) + m + 1; omega
      let B := IntervalBoundary.boundaryMatrix ((n : ℕ) + m).succPNat n hn
        (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
      let N : ℝ := ((n : ℕ) + m + 1 : ℕ)
      let a := N ^ (-(1 / 2 : ℝ))
      let W := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(2 * p.val.2 - 1))
      let Z := ∑ j, |z j|
      let ZW := ∑ j, ConditionalScores.weight p.val.2 j * |z j|
      let R := fun i j => (frozenPhysicalMatrix p n m θ h b D x -
        frozenInternalMatrix p n m θ h b D x) i j -
        (if x ∈ ExceptionalEvent.properGoodEvent p n m hn h D then B i j else 0)
      ‖(WithLp.toLp 2 (fun i => ∑ j, R i j * z j) : EuclideanSpace ℝ (Fin (n : ℕ)))‖ ≤
        (3 * D / N * Z + p.val.1 * C * D * (a * ZW + N⁻¹ * Z)) * Real.sqrt n +
          (p.val.1 * C * D * (ZW + a * Z)) * Real.sqrt W := by
  classical
  obtain ⟨C,hC,hentry⟩ := frozen_difference_entry_bound p hs
  refine ⟨C,hC,?_⟩
  intro n m hN hhalf θ h b D hD x z hn B N a W Z ZW R
  let w := ConditionalScores.weight p.val.2 (n := (n : ℕ))
  let U := 3 * D / N * Z + p.val.1 * C * D * (a * ZW + N⁻¹ * Z)
  let V := p.val.1 * C * D * (ZW + a * Z)
  have hw (i) : 0 ≤ w i := (ConditionalScores.weight_pos p.val.2 i).le
  have hZ : 0 ≤ Z := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hZW : 0 ≤ ZW := Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (abs_nonneg _)
  have hN0 : 0 < N := by dsimp only [N]; positivity
  have ha : 0 ≤ a := Real.rpow_nonneg hN0.le _
  have hU : 0 ≤ U := by dsimp only [U]; have hβ := p.property.1.le; positivity
  have hV : 0 ≤ V := by dsimp only [V]; have hβ := p.property.1.le; positivity
  have hpoint (i : Fin (n : ℕ)) : |∑ j, R i j * z j| ≤ U + V * w i := by
    calc
      _ ≤ ∑ j, |R i j * z j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |R i j| * |z j| := by simp only [abs_mul]
      _ ≤ ∑ j, (3 * D / N + p.val.1 * C * D *
          (w i * w j + a * (w i + w j) + N⁻¹)) * |z j| := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right
          (hentry n m hN hhalf θ h b D hD x i j).1 (abs_nonneg _)
      _ = U + V * w i := by
        dsimp only [U, V, Z, ZW]
        simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
  let wv : EuclideanSpace ℝ (Fin (n : ℕ)) := WithLp.toLp 2 w
  let onev : EuclideanSpace ℝ (Fin (n : ℕ)) := WithLp.toLp 2 (fun _ => 1)
  let y : EuclideanSpace ℝ (Fin (n : ℕ)) := WithLp.toLp 2 (fun i => ∑ j, R i j * z j)
  have hnorm : ‖y‖ ≤ ‖U • onev + V • wv‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
      EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    apply sq_le_sq.mpr
    change |∑ j, R i j * z j| ≤ |U * 1 + V * w i|
    rw [mul_one, abs_of_nonneg (add_nonneg hU (mul_nonneg hV (hw i)))]
    exact hpoint i
  have hones : ‖onev‖ = Real.sqrt n := by
    rw [EuclideanSpace.norm_eq]
    simp only [onev, Real.norm_eq_abs, abs_one, one_pow,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hweights : ‖wv‖ ≤ Real.sqrt W := by
    rw [EuclideanSpace.norm_eq]
    simp only [wv, Real.norm_eq_abs, sq_abs]
    exact Real.sqrt_le_sqrt (boundary_weight_square_sum p.val.2 hs n)
  calc
    _ ≤ ‖U • onev + V • wv‖ := hnorm
    _ ≤ ‖U • onev‖ + ‖V • wv‖ := norm_add_le _ _
    _ = U * Real.sqrt n + V * ‖wv‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hU, abs_of_nonneg hV, hones]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hweights hV)

set_option backward.isDefEq.respectTransparency false in
/-- Complete pointwise norm decomposition for Subsection 4.5.
This keeps the boundary Euclidean norm and the ordinary and score-weighted
absolute sums visible, ready for the L² Minkowski step. The matrix is the
physical difference and the estimate holds on both events. -/
theorem frozen_difference_action_norm (p : Parameters) (hs : 1 < p.val.2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ+) (m : ℕ),
      4 ≤ (n : ℕ) + m + 1 → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (θ : PhysicalCutoff) (h : ℝ) (b : Bool) (D : ℝ), 0 ≤ D →
      ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (z : Fin (n : ℕ) → ℝ),
      let M := frozenPhysicalMatrix p n m θ h b D x - frozenInternalMatrix p n m θ h b D x
      let N : ℝ := ((n : ℕ) + m + 1 : ℕ)
      let a := N ^ (-(1 / 2 : ℝ))
      let S := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-p.val.2)
      let W := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(2 * p.val.2 - 1))
      let K := 2 * (8 : ℝ) ^ (p.val.2 + 1) + 1
      let Z := ∑ j, |z j|
      let ZW := ∑ j, ConditionalScores.weight p.val.2 j * |z j|
      let E := Real.sqrt (∑ j, if (ConditionalScores.boundaryDistance j : ℝ) < (n : ℝ) / 8
        then z j ^ 2 else 0)
      ‖(WithLp.toLp 2 (fun i => ∑ j, M i j * z j) : EuclideanSpace ℝ (Fin (n : ℕ)))‖ ≤
        K * D * (n : ℝ) ^ (-p.val.2) * Z * Real.sqrt n + D * S * E +
        (3 * D / N * Z + p.val.1 * C * D * (a * ZW + N⁻¹ * Z)) * Real.sqrt n +
          (p.val.1 * C * D * (ZW + a * Z)) * Real.sqrt W := by
  classical
  obtain ⟨C,hC,hrem⟩ := frozen_remainder_action_norm p hs
  refine ⟨C,hC,?_⟩
  intro n m hN hhalf θ h b D hD x z M N a S W K Z ZW E
  let hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ) := by
    change (n : ℕ) ≤ (n : ℕ) + m + 1; omega
  let B := IntervalBoundary.boundaryMatrix ((n : ℕ) + m).succPNat n hn
    (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
  let Bf := fun i j => if x ∈ ExceptionalEvent.properGoodEvent p n m hn h D then B i j else 0
  let vb : EuclideanSpace ℝ (Fin (n : ℕ)) := WithLp.toLp 2 (fun i => ∑ j, Bf i j * z j)
  let vr : EuclideanSpace ℝ (Fin (n : ℕ)) := WithLp.toLp 2 (fun i => ∑ j, (M i j - Bf i j) * z j)
  have hb : ‖vb‖ ≤ K * D * (n : ℝ) ^ (-p.val.2) * Z * Real.sqrt n + D * S * E := by
    by_cases hx : x ∈ ExceptionalEvent.properGoodEvent p n m hn h D
    · simpa only [vb,Bf,ite_eq_left hx] using boundary_matrix_action_norm p hs n m hhalf D hD x hx.2 z
    · have hz : vb = 0 := by
        apply PiLp.ext
        intro i
        simp [vb,Bf,ite_eq_right hx]
      rw [hz,norm_zero]
      have hS : 0 ≤ S := mul_nonneg (by norm_num) (tsum_nonneg fun _ => by positivity)
      have hZ : 0 ≤ Z := Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hE : 0 ≤ E := Real.sqrt_nonneg _
      dsimp only [K]
      positivity
  have hr : ‖vr‖ ≤ (3 * D / N * Z + p.val.1 * C * D * (a * ZW + N⁻¹ * Z)) * Real.sqrt n +
      (p.val.1 * C * D * (ZW + a * Z)) * Real.sqrt W := hrem n m hN hhalf θ h b D hD x z
  have hsplit : (WithLp.toLp 2 (fun i => ∑ j, M i j * z j) : EuclideanSpace ℝ (Fin (n : ℕ))) =
      vb + vr := by
    apply PiLp.ext
    intro i
    change (∑ j, M i j * z j) = (∑ j, Bf i j * z j) + ∑ j, (M i j - Bf i j) * z j
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsplit]
  exact ((norm_add_le _ _).trans (add_le_add hb hr)).trans_eq (by ring)

/-- Geometry of the middle-half source in Subsection 4.5.
Labels in the source are one-based, hence the `+1` in both source bounds. -/
theorem boundary_source_separation {n : ℕ} (i₀ i : Fin n)
    (hlo : (n : ℝ) / 4 ≤ (i₀.val : ℝ) + 1)
    (hhi : (i₀.val : ℝ) + 1 ≤ 3 * (n : ℝ) / 4)
    (hi : (ConditionalScores.boundaryDistance i : ℝ) < (n : ℝ) / 8) :
    (n : ℝ) / 8 ≤ 1 + |(i.val : ℝ) - (i₀.val : ℝ)| := by
  have hsub : ((n - i.val : ℕ) : ℝ) = (n : ℝ) - i.val := by
    exact Nat.cast_sub (Nat.le_of_lt i.isLt)
  unfold ConditionalScores.boundaryDistance at hi
  rw [Nat.cast_min, Nat.cast_add, Nat.cast_one, hsub, min_lt_iff] at hi
  rcases hi with hi | hi
  · linarith [neg_le_abs ((i.val : ℝ) - (i₀.val : ℝ))]
  · linarith [le_abs_self ((i.val : ℝ) - (i₀.val : ℝ))]

/-- Boundary-index part of the auxiliary decay profile (Subsection 4.5). -/
theorem boundary_source_profile {n : ℕ} (hn : 0 < n) (s : ℝ) (hs : 0 ≤ s)
    (i₀ i : Fin n) (hlo : (n : ℝ) / 4 ≤ (i₀.val : ℝ) + 1)
    (hhi : (i₀.val : ℝ) + 1 ≤ 3 * (n : ℝ) / 4)
    (hi : (ConditionalScores.boundaryDistance i : ℝ) < (n : ℝ) / 8) :
    (1 + |(i.val : ℝ) - (i₀.val : ℝ)|) ^ (-s) ≤ (8 : ℝ) ^ s * (n : ℝ) ^ (-s) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ ≤ ((n : ℝ) / 8) ^ (-s) := Real.rpow_le_rpow_of_nonpos (by positivity)
      (boundary_source_separation i₀ i hlo hhi hi) (neg_nonpos.mpr hs)
    _ = _ := by rw [Real.div_rpow hn0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8),
        div_inv_eq_mul, mul_comm]

/-- Boundary part of the source profile in the Euclidean component norm,
as used in the Schur step of Subsection 4.5. -/
theorem boundary_source_profile_square_sum {n : ℕ} (hn : 0 < n) (s : ℝ) (hs : 0 ≤ s)
    (i₀ : Fin n) (hlo : (n : ℝ) / 4 ≤ (i₀.val : ℝ) + 1)
    (hhi : (i₀.val : ℝ) + 1 ≤ 3 * (n : ℝ) / 4) :
    Real.sqrt (∑ i : Fin n, if (ConditionalScores.boundaryDistance i : ℝ) < (n : ℝ) / 8
      then ((1 + |(i.val : ℝ) - (i₀.val : ℝ)|) ^ (-s)) ^ 2 else 0) ≤
        (8 : ℝ) ^ s * (n : ℝ) ^ (-(s - 1 / 2)) := by
  classical
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hsq (a : ℝ) : ((n : ℝ) ^ a) ^ 2 = (n : ℝ) ^ (a * 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    norm_num
  have hpow : (n : ℝ) * ((n : ℝ) ^ (-s)) ^ 2 =
      ((n : ℝ) ^ (-(s - 1 / 2))) ^ 2 := by
    rw [hsq, hsq]
    calc
      _ = (n : ℝ) ^ (1 + -s * 2) := by rw [Real.rpow_add hn0, Real.rpow_one]
      _ = _ := by congr 1; ring
  calc
    _ ≤ ∑ _i : Fin n, ((8 : ℝ) ^ s * (n : ℝ) ^ (-s)) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs with hi
      · exact pow_le_pow_left₀ (by positivity) (boundary_source_profile hn s hs i₀ i hlo hhi hi) 2
      · exact sq_nonneg _
    _ = (n : ℝ) * ((8 : ℝ) ^ s * (n : ℝ) ^ (-s)) ^ 2 := by simp
    _ = ((8 : ℝ) ^ s * (n : ℝ) ^ (-(s - 1 / 2))) ^ 2 := by
      rw [mul_pow, mul_pow]
      calc
        _ = ((8 : ℝ) ^ s) ^ 2 * ((n : ℝ) * ((n : ℝ) ^ (-s)) ^ 2) := by ring
        _ = _ := by rw [hpow]

/-- Summable auxiliary source profile in Subsection 4.5. -/
theorem source_profile_sum (s : ℝ) (hs : 1 < s) {n : ℕ} (i₀ : Fin n) :
    ∑ i : Fin n, (1 + |(i.val : ℝ) - (i₀.val : ℝ)|) ^ (-s) ≤
      2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s) := by
  let g : ComponentGeometry (Fin n) := Sum.inl
    ⟨fun i => (i.val : ℤ), fun i j hij => Fin.ext (Int.ofNat_inj.mp hij)⟩
  have h := ComponentGeometryBounds.sum_power_le g i₀ hs
  have hd (i) : componentDistance g i₀ i = |(i.val : ℝ) - (i₀.val : ℝ)| := by
    change |((i₀.val : ℤ) : ℝ) - ((i.val : ℤ) : ℝ)| = _
    rw [Int.cast_natCast, Int.cast_natCast, abs_sub_comm]
  simpa only [hd] using h


/-- Weighted source-profile contraction for Subsection 4.5.
Cauchy–Schwarz on the boundary uses the summable square of the score
weight, so no endpoint logarithm or extra power of the size is needed. -/
theorem weighted_source_profile_sum (s : ℝ) (hs : 1 < s) {n : ℕ} (hn : 0 < n)
    (i₀ : Fin n) (hlo : (n : ℝ) / 4 ≤ (i₀.val : ℝ) + 1)
    (hhi : (i₀.val : ℝ) + 1 ≤ 3 * (n : ℝ) / 4) :
    let S := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s)
    let W := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(2 * s - 1))
    ∑ i : Fin n, ConditionalScores.weight s i *
      (1 + |(i.val : ℝ) - (i₀.val : ℝ)|) ^ (-s) ≤
      ((8 : ℝ) ^ (s - 1 / 2) * S + (8 : ℝ) ^ s * Real.sqrt W) *
        (n : ℝ) ^ (-(s - 1 / 2)) := by
  classical
  intro S W
  let w := ConditionalScores.weight s (n := n)
  let r := fun i : Fin n => (1 + |(i.val : ℝ) - (i₀.val : ℝ)|) ^ (-s)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have ht : 0 < s - 1 / 2 := by linarith
  have hw (i) : 0 ≤ w i := (ConditionalScores.weight_pos s i).le
  have hW : 0 ≤ W := mul_nonneg (by norm_num) (tsum_nonneg fun _ => by positivity)
  have hwsq := boundary_weight_square_sum s hs n
  change ∑ i, w i ^ 2 ≤ W at hwsq
  have hsumw : ∑ i, w i ≤ Real.sqrt W * Real.sqrt n := by
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ w (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at hcs
    exact hcs.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hwsq) (Real.sqrt_nonneg _))
  have hbulk (i : Fin n) (hi : (n : ℝ) / 8 ≤ (ConditionalScores.boundaryDistance i : ℝ)) :
      w i ≤ (8 : ℝ) ^ (s - 1 / 2) * (n : ℝ) ^ (-(s - 1 / 2)) := by
    apply (Real.rpow_le_rpow_of_nonpos (by positivity) hi (neg_nonpos.mpr ht.le)).trans_eq
    rw [Real.div_rpow hn0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8),
      div_inv_eq_mul, mul_comm]
  have hpoint (i) : w i * r i ≤
      ((8 : ℝ) ^ (s - 1 / 2) * (n : ℝ) ^ (-(s - 1 / 2))) * r i +
      ((8 : ℝ) ^ s * (n : ℝ) ^ (-s)) * w i := by
    by_cases hi : (n : ℝ) / 8 ≤ (ConditionalScores.boundaryDistance i : ℝ)
    · exact (mul_le_mul_of_nonneg_right (hbulk i hi) (by dsimp [r]; positivity)).trans
        (le_add_of_nonneg_right (mul_nonneg (by positivity) (hw i)))
    · have hb := boundary_source_profile hn s (by linarith) i₀ i hlo hhi (lt_of_not_ge hi)
      exact (mul_le_mul_of_nonneg_left hb (hw i)).trans
        (by rw [mul_comm (w i)]; exact le_add_of_nonneg_left (by dsimp [r]; positivity))
  have hpower : (n : ℝ) ^ (-s) * Real.sqrt n = (n : ℝ) ^ (-(s - 1 / 2)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn0]
    congr 1
    ring
  calc
    _ ≤ ∑ i, (((8 : ℝ) ^ (s - 1 / 2) * (n : ℝ) ^ (-(s - 1 / 2))) * r i +
        ((8 : ℝ) ^ s * (n : ℝ) ^ (-s)) * w i) := Finset.sum_le_sum fun i _ => hpoint i
    _ = ((8 : ℝ) ^ (s - 1 / 2) * (n : ℝ) ^ (-(s - 1 / 2))) * (∑ i, r i) +
        ((8 : ℝ) ^ s * (n : ℝ) ^ (-s)) * (∑ i, w i) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ ((8 : ℝ) ^ (s - 1 / 2) * (n : ℝ) ^ (-(s - 1 / 2))) * S +
        ((8 : ℝ) ^ s * (n : ℝ) ^ (-s)) * (Real.sqrt W * Real.sqrt n) :=
      add_le_add (mul_le_mul_of_nonneg_left (source_profile_sum s hs i₀) (by positivity))
        (mul_le_mul_of_nonneg_left hsumw (by positivity))
    _ = _ := by
      have hp := congrArg (fun a => (8 : ℝ) ^ s * Real.sqrt W * a) hpower
      nlinarith only [hp]


/-- Internal scalar contraction of a point-source profile, used in
Subsection 4.5. The hypothesis is an internal component envelope. -/
theorem internal_profile_contractions (s : ℝ) (hs : 1 < s) {n : ℕ} (hn : 0 < n)
    (i₀ : Fin n) (hlo : (n : ℝ) / 4 ≤ (i₀.val : ℝ) + 1)
    (hhi : (i₀.val : ℝ) + 1 ≤ 3 * (n : ℝ) / 4) (V : ℝ) (hV : 0 ≤ V)
    (f : Fin n → ℝ)
    (hf : ∀ i, f i ≤ V * (1 + |(i.val : ℝ) - (i₀.val : ℝ)|) ^ (-s)) :
    let S := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s)
    let W := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(2 * s - 1))
    let L := (8 : ℝ) ^ (s - 1 / 2) * S + (8 : ℝ) ^ s * Real.sqrt W
    (∑ i : Fin n, f i) ≤ V * S ∧
      (∑ i : Fin n, ConditionalScores.weight s i * f i) ≤ V * (L * (n : ℝ) ^ (-(s - 1 / 2))) := by
  intro S W L
  constructor
  · calc
      _ ≤ ∑ i : Fin n, V * (1 + |(i.val : ℝ) - (i₀.val : ℝ)|) ^ (-s) :=
        Finset.sum_le_sum fun i _ => hf i
      _ = V * ∑ i : Fin n, (1 + |(i.val : ℝ) - (i₀.val : ℝ)|) ^ (-s) := by rw [Finset.mul_sum]
      _ ≤ V * S := mul_le_mul_of_nonneg_left (source_profile_sum s hs i₀) hV
  · have hw := weighted_source_profile_sum s hs hn i₀ hlo hhi
    change _ ≤ L * (n : ℝ) ^ (-(s - 1 / 2)) at hw
    calc
      _ ≤ ∑ i : Fin n, ConditionalScores.weight s i *
          (V * (1 + |(i.val : ℝ) - (i₀.val : ℝ)|) ^ (-s)) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hf i)
          (ConditionalScores.weight_pos _ _).le
      _ = V * ∑ i : Fin n, ConditionalScores.weight s i *
          (1 + |(i.val : ℝ) - (i₀.val : ℝ)|) ^ (-s) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hw hV

set_option backward.isDefEq.respectTransparency false in
/-- Actual auxiliary-solution contractions used in Subsection 4.5.
Both the ordinary component sum and the score-weighted sum hold uniformly
for every common scalar form and every measurable fibre restriction. -/
theorem internal_auxiliary_weighted_sums (p : Parameters) (hs : 1 < p.val.2)
    (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ (θ : PhysicalCutoff) (h : ℝ), 0 < h →
      ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, 1 ≤ C ∧ ∀ (n : ℕ+) (m : ℕ),
        4 ≤ (n : ℕ) + m + 1 → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 → ∀ (b : Bool)
        (α : Type*) [MeasurableSpace α]
        (τ : α → AffineSimplex.chartDomain n ((n + m : ℕ) + 1)), Measurable τ →
        ∀ (ν : Measure α) [IsProbabilityMeasure ν] (Q : ScalarFormData ν),
        IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
        ∀ (i₀ : Fin (n : ℕ)), (n : ℝ) / 4 ≤ (i₀.val : ℝ) + 1 →
          (i₀.val : ℝ) + 1 ≤ 3 * (n : ℝ) / 4 → ∀ (χ : Lp ℝ 2 ν)
        (u : Fin (n : ℕ) → Q.1),
        WeightedWeakSolution Q
          (fun x => p.val.1 • frozenInternalMatrix p n m θ h b
            (A * (n : ℝ) ^ (κ * h)) (τ x)) ⊤
          (fun i => if i = i₀ then χ else 0) u →
        (∑ i : Fin (n : ℕ), ‖(u i).val‖) ≤ C * (n : ℝ) ^ (r * h) * ‖χ‖ ∧
        (∑ i : Fin (n : ℕ), ConditionalScores.weight p.val.2 i * ‖(u i).val‖) ≤
          C * (n : ℝ) ^ (r * h) * (n : ℝ) ^ (-(p.val.2 - 1 / 2)) * ‖χ‖ := by
  classical
  obtain ⟨r,hr,hdecay⟩ := internal_auxiliary_point_source_decay p hs κ hκ
  refine ⟨r,hr,?_⟩
  intro θ h hh A hA
  obtain ⟨Cd,hCd,hdecay⟩ := hdecay θ h hh A hA
  let S := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-p.val.2)
  let W := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(2 * p.val.2 - 1))
  let L := (8 : ℝ) ^ (p.val.2 - 1 / 2) * S + (8 : ℝ) ^ p.val.2 * Real.sqrt W
  have hS : 0 ≤ S := mul_nonneg (by norm_num) (tsum_nonneg fun _ => by positivity)
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  let C := Cd * (1 + S + L)
  have hC : 1 ≤ C := one_le_mul_of_one_le_of_one_le hCd (by linarith)
  have hCdS : Cd * S ≤ C := by dsimp only [C]; nlinarith
  have hCdL : Cd * L ≤ C := by dsimp only [C]; nlinarith
  refine ⟨C,hC,?_⟩
  intro n m hN hhalf b α _ τ hτ ν _ Q hQ hcons i₀ hlo hhi χ u hu
  have hd := (hdecay n m hN hhalf b α τ hτ ν Q hQ hcons i₀ χ).2 u hu
  let P := Cd * (n : ℝ) ^ (r * h) * ‖χ‖
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hpoint (i) : ‖(u i).val‖ ≤ P * (1 + |(i.val : ℝ) - (i₀.val : ℝ)|) ^ (-p.val.2) := by
    exact (hd i).trans_eq (by dsimp only [P]; ring)
  have hc := internal_profile_contractions p.val.2 hs n.pos i₀ hlo hhi P hP
    (fun i => ‖(u i).val‖) hpoint
  change (∑ i : Fin (n : ℕ), ‖(u i).val‖) ≤ P * S ∧
    (∑ i : Fin (n : ℕ), ConditionalScores.weight p.val.2 i * ‖(u i).val‖) ≤
      P * (L * (n : ℝ) ^ (-(p.val.2 - 1 / 2))) at hc
  constructor
  · apply hc.1.trans
    calc
      _ = (Cd * S) * ((n : ℝ) ^ (r * h) * ‖χ‖) := by dsimp only [P]; ring
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hCdS (by positivity :
          0 ≤ (n : ℝ) ^ (r * h) * ‖χ‖)
  · apply hc.2.trans
    calc
      _ = (Cd * L) * ((n : ℝ) ^ (r * h) * (n : ℝ) ^ (-(p.val.2 - 1 / 2)) * ‖χ‖) := by
        dsimp only [P]; ring
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hCdL (by positivity :
          0 ≤ (n : ℝ) ^ (r * h) * (n : ℝ) ^ (-(p.val.2 - 1 / 2)) * ‖χ‖)

end Riesz2.DecayShort.PhysicalComparison
