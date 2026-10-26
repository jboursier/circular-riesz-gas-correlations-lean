/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.LocalLawPart3
public import Riesz2.HelfferSjostrand.MarginalHessianPart4
public import Riesz2.ToMathlib.DominatedFibreRegularity

/-!
# Smooth proper marginals and the complete short-range tilt lemma

The selected upper penalty factors out of each exterior fibre. The proved
smooth compactly supported physical density supplies two dominated fibre
derivatives, including across moving collision faces. Combining the resulting
C² marginal with its convex quadratic residual gives the classical lower
Hessian in every exterior dimension and completes the tilt comparison lemma.
-/

public section
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace Riesz2.DecayShort

set_option backward.isDefEq.respectTransparency false in
/-- See the proof of Lemma B.1 in the paper: the upper tilt adds precisely the
retained penalty to the negative logarithm of the actual physical fibre
mass. Both logarithms have positive finite arguments on the whole interior. -/
theorem upperTilt_marginal_potential (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff)
    (R : {R : ℝ // 0 < R}) :
    let J := Finset.univ.image (fun j : Fin n => σ (j.castAdd m).castSucc)
    let D := ProperMarginalChart.penalizedChartDensity p n m σ θ R.val⁻¹ J false
    ∀ x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
      -Real.log (AffineFibre.fibreMass volume D x).toReal =
        -Real.log (AffineFibre.fibreMass volume
          (ProperMarginalChart.chartDensity p n m σ) x).toReal +
          p.val.1 * ∑ i : Fin n, θ.val (x i / R) := by
  classical
  intro J D x hx
  have hJ : ∀ i ∈ J, ∃ j : Fin n, i = σ (j.castAdd m).castSucc := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨j, rfl⟩
  have hsum : (∑ i ∈ J,
      θ.val (R.val⁻¹ * RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ (x, 0) i)) =
      ∑ i : Fin n, θ.val (x i / R) := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro i _
      rw [RetainedSimplex.chart_retained]
      simp only [div_eq_mul_inv, mul_comm]
    · intro i _ j _ hij
      exact Fin.ext (congrArg (fun k : Fin (n + m + 1) => k.val) (σ.injective hij))
  have hmass : AffineFibre.fibreMass volume D x =
      ENNReal.ofReal (Real.exp (-p.val.1 * ∑ i : Fin n, θ.val (x i / R))) *
        AffineFibre.fibreMass volume (ProperMarginalChart.chartDensity p n m σ) x := by
    unfold AffineFibre.fibreMass
    dsimp only [D]
    simp_rw [ProperMarginalChart.penalizedChartDensity_eq_mul p n m σ θ R.val⁻¹ J false hJ]
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero, hsum]
    exact lintegral_const_mul _ ((ProperMarginalChart.measurable_chartDensity p n m σ).comp
      measurable_prodMk_left)
  obtain ⟨h0, ht⟩ := ProperMarginalChart.fibre_mass p n m hn σ hx
  have hp : 0 < (AffineFibre.fibreMass volume
      (ProperMarginalChart.chartDensity p n m σ) x).toReal :=
    ENNReal.toReal_pos h0 ht
  rw [hmass, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _),
    Real.log_mul (Real.exp_pos _).ne' hp.ne', Real.log_exp]
  ring

/-- See Appendix B of the paper: the retained upper penalty is smooth throughout
its entire positive-coordinate carrier, for every exterior dimension. -/
theorem upperTilt_retained_penalty_contDiff (p : Parameters) (n : ℕ)
    (θ : PhysicalCutoff) (R : {R : ℝ // 0 < R}) (L : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin n) => p.val.1 * ∑ i : Fin n, θ.val (x i / R))
      (AffineSimplex.chartDomain n L) := by
  apply contDiffOn_const.mul
  apply ContDiffOn.sum
  intro i _
  exact θ.property.1.comp
    ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.div_const R.val).contDiffOn
    (fun x hx => div_nonneg (hx.1 i).le R.property.le)

set_option backward.isDefEq.respectTransparency false in
/-- See the proof of Lemma B.1 in the paper: the difference of the actual tilted
and untilted marginal potentials is smooth, including positive-dimensional
exterior fibres. No differentiability of either potential is assumed. -/
theorem upperTilt_marginal_difference_contDiff (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff)
    (R : {R : ℝ // 0 < R}) :
    let J := Finset.univ.image (fun j : Fin n => σ (j.castAdd m).castSucc)
    let D := ProperMarginalChart.penalizedChartDensity p n m σ θ R.val⁻¹ J false
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x =>
      -Real.log (AffineFibre.fibreMass volume D x).toReal -
        -Real.log (AffineFibre.fibreMass volume
          (ProperMarginalChart.chartDensity p n m σ) x).toReal)
      (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) := by
  intro J D
  apply (upperTilt_retained_penalty_contDiff p n θ R _).congr
  intro x hx
  rw [upperTilt_marginal_potential p n m hn σ θ R x hx]
  ring

namespace LocalLawInternal

set_option backward.isDefEq.respectTransparency false in
/-- The upper penalty preserves and reflects C² regularity of the physical
marginal, as used in the proof of Lemma B.1. -/
theorem upperTilt_contDiff_iff (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff)
    (R : {R : ℝ // 0 < R}) :
    let J := Finset.univ.image (fun j : Fin n => σ (j.castAdd m).castSucc)
    let D := ProperMarginalChart.penalizedChartDensity p n m σ θ R.val⁻¹ J false
    ContDiffOn ℝ 2 (fun x => -Real.log (AffineFibre.fibreMass volume D x).toReal)
        (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) ↔
      ContDiffOn ℝ 2 (fun x => -Real.log (AffineFibre.fibreMass volume
        (ProperMarginalChart.chartDensity p n m σ) x).toReal)
        (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) := by
  intro J D
  have hP := (upperTilt_retained_penalty_contDiff p n θ R ((n + m : ℕ) + 1)).of_le
    (by norm_num : (2 : WithTop ℕ∞) ≤ (⊤ : ℕ∞))
  constructor
  · intro h
    apply (h.sub hP).congr
    intro x hx
    rw [upperTilt_marginal_potential p n m hn σ θ R x hx]
    ring
  · intro h
    apply (h.add hP).congr
    intro x hx
    exact upperTilt_marginal_potential p n m hn σ θ R x hx

end LocalLawInternal

set_option backward.isDefEq.respectTransparency false in
/-- See the proof of Lemma B.1 in the paper: the negative logarithm of the
actual retained marginal is C², for every proper retained set, including
all positive-dimensional exterior fibres. -/
theorem upperTilt_marginal_contDiff (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff)
    (R : {R : ℝ // 0 < R}) :
    let J := Finset.univ.image (fun j : Fin n => σ (j.castAdd m).castSucc)
    let D := ProperMarginalChart.penalizedChartDensity p n m σ θ R.val⁻¹ J false
    ContDiffOn ℝ 2 (fun x => -Real.log (AffineFibre.fibreMass volume D x).toReal)
      (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) := by
  apply (LocalLawInternal.upperTilt_contDiff_iff p n m hn σ θ R).mpr
  let E := EuclideanSpace ℝ (Fin n)
  let F := EuclideanSpace ℝ (Fin m)
  have hdom {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
      {μ : Measure F} [IsFiniteMeasure μ] {f : E × F → G}
      (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
      DominatedFibre.DominatedFDerivOn μ univ (fun x y => f (x, y))
        (fun x y => (fderiv ℝ f (x, y)).comp (ContinuousLinearMap.inl ℝ E F)) := by
    let L : E →L[ℝ] E × F := ContinuousLinearMap.inl ℝ E F
    have hd : Continuous (fderiv ℝ f) :=
      (hf.fderiv_right (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).continuous
    obtain ⟨B, hB⟩ := (hc.isCompact_range hf.continuous).bddAbove_image
      continuous_norm.continuousOn
    obtain ⟨C, hC⟩ := ((hc.fderiv ℝ).isCompact_range hd).bddAbove_image
      continuous_norm.continuousOn
    have hb (q) : ‖f q‖ ≤ max B 0 :=
      (hB ⟨f q, ⟨q, rfl⟩, rfl⟩).trans (le_max_left _ _)
    have hb' (q) : ‖(fderiv ℝ f q).comp L‖ ≤ max C 0 * ‖L‖ := by
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right
          ((hC ⟨fderiv ℝ f q, ⟨q, rfl⟩, rfl⟩).trans (le_max_left _ _)) (norm_nonneg _))
    refine ⟨?_, ?_, ?_⟩
    · intro x _
      apply (integrable_const (max B 0)).mono'
        ((hf.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      exact Eventually.of_forall fun y => hb (x, y)
    · intro x _
      exact (((ContinuousLinearMap.compL ℝ E (E × F) G).flip L).continuous.comp
        (hd.comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable
    · intro x _
      refine ⟨univ, univ_mem, subset_rfl, fun _ => max C 0 * ‖L‖,
        integrable_const _, Eventually.of_forall (fun y z _ => hb' (z, y)), ?_⟩
      apply Eventually.of_forall
      intro y z _
      have hpair : HasFDerivAt (fun t : E => (t, y)) L z := by
        have hL : L = (ContinuousLinearMap.id ℝ E).prod 0 := by ext u <;> rfl
        rw [hL]
        exact (hasFDerivAt_id z).prodMk (hasFDerivAt_const y z)
      exact ((hf.differentiable (by norm_num)) (z, y)).hasFDerivAt.comp z hpair
  let f : E × F → ℝ := fun q => (ProperMarginalChart.chartDensity p n m σ q).toReal
  obtain ⟨hfall, hc⟩ := MarginalHessian.physical_chart_density_smooth_compact p n m hn σ
  have hf : ContDiff ℝ 2 f := hfall.of_le (by norm_num)
  have hI : ContDiff ℝ 2 (fun x => ∫ y, f (x, y)) := by
    let L : E →L[ℝ] E × F := ContinuousLinearMap.inl ℝ E F
    let A : ((E × F) →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] ℝ :=
      (ContinuousLinearMap.compL ℝ E (E × F) ℝ).flip L
    let g : E × F → E →L[ℝ] ℝ := fun q => A (fderiv ℝ f q)
    have hg : ContDiff ℝ 1 g :=
      A.contDiff.comp (hf.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num))
    have hgc : HasCompactSupport g := (hc.fderiv ℝ).comp_left (by simp [A])
    let K : Set F := Prod.snd '' tsupport f
    have hK : IsCompact K := hc.isCompact.image continuous_snd
    let μ : Measure F := volume.restrict K
    have : IsFiniteMeasure μ := ⟨by simpa [μ] using hK.measure_lt_top (μ := volume)⟩
    have h₁ := hdom (μ := μ) (hf.of_le (by norm_num)) hc
    have h₂ := hdom (μ := μ) hg hgc
    have hreg : ContDiffOn ℝ 2 (fun x => ∫ y, f (x, y) ∂μ) univ := by
      apply DominatedFibre.contDiffOn_integral_two isOpen_univ h₁ h₂
      intro x _
      apply Eventually.of_forall
      intro y
      have hgd : Continuous (fderiv ℝ g) :=
        (hg.fderiv_right (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).continuous
      exact ((hgd.comp (continuous_id.prodMk continuous_const)).clm_comp
        (continuous_const (y := L))).continuousAt
    apply contDiffOn_univ.mp
    apply hreg.congr
    intro x _
    change (∫ y, f (x, y)) = ∫ y in K, f (x, y)
    rw [← integral_indicator hK.measurableSet]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro y
    by_cases hy : y ∈ K
    · rw [indicator_of_mem hy]
    · rw [indicator_of_notMem hy]
      apply Function.notMem_support.mp
      intro h
      exact hy ⟨(x, y), subset_tsupport f h, rfl⟩
  have hfinite (q : E × F) : ProperMarginalChart.chartDensity p n m σ q < ∞ := by
    by_cases hq : q ∈ RetainedSimplex.domain n m ((n + m : ℕ) + 1)
    · rw [ProperMarginalChart.chartDensity, indicator_of_mem hq]
      unfold ProperMarginalChart.density
      split_ifs <;> simp
    · simp only [ProperMarginalChart.chartDensity, indicator_of_notMem hq]
      exact ENNReal.zero_lt_top
  have he (x : E) : (AffineFibre.fibreMass volume
      (ProperMarginalChart.chartDensity p n m σ) x).toReal = ∫ y, f (x, y) := by
    exact (integral_toReal
      (((ProperMarginalChart.measurable_chartDensity p n m σ).comp
        measurable_prodMk_left).aemeasurable)
      (Eventually.of_forall fun y => hfinite (x, y))).symm
  have hp (x : E) (hx : x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
      (∫ y, f (x, y)) ≠ 0 := by
    rw [← he]
    obtain ⟨h0, ht⟩ := ProperMarginalChart.fibre_mass p n m hn σ hx
    exact (ENNReal.toReal_pos h0 ht).ne'
  apply ((hI.contDiffOn.log hp).neg).congr
  intro x _
  rw [he]

set_option backward.isDefEq.respectTransparency false in
/-- See the proof of Lemma B.1 in the paper, the classical marginal Hessian
bound for every proper retained set. C² regularity is concluded for the
actual physical fibre mass in every exterior dimension. -/
theorem upperTilt_marginal_hessian (p : Parameters) (hs : 1 < p.val.2)
    (n m : ℕ) (hn : 1 ≤ n) (σ : Equiv.Perm (Fin (n + m + 1)))
    (θ : PhysicalCutoff) (R : {R : ℝ // 0 < R}) (hR : 1 ≤ (R : ℝ)) :
    let J := Finset.univ.image (fun j : Fin n => σ (j.castAdd m).castSucc)
    let D := ProperMarginalChart.penalizedChartDensity p n m σ θ R.val⁻¹ J false
    let V := fun x => -Real.log (AffineFibre.fibreMass volume D x).toReal
    ContDiffOn ℝ 2 V (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) ∧
      ∀ x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
        ∀ v : EuclideanSpace ℝ (Fin n),
          p.val.1 * (R : ℝ) ^ (-p.val.2 - 2) * ‖v‖ ^ 2 ≤
            fderiv ℝ (fderiv ℝ V) x v v := by
  intro J D V
  let U := AffineSimplex.chartDomain n ((n + m : ℕ) + 1)
  let a := p.val.1 * (R : ℝ) ^ (-p.val.2 - 2)
  let Q := fun x : EuclideanSpace ℝ (Fin n) => a / 2 * ‖x‖ ^ 2
  have hV : ContDiffOn ℝ 2 V U := upperTilt_marginal_contDiff p n m hn σ θ R
  have hQ : ContDiff ℝ 2 Q := contDiff_const.mul (contDiff_norm_sq ℝ)
  have ho : IsOpen U := AffineSimplex.isOpen_chartDomain _ _
  refine ⟨hV, ?_⟩
  intro x hx v
  have hc : ConvexOn ℝ U (fun x => V x - Q x) :=
    upperTilt_marginal_residual_convex p hs n m hn σ θ R hR
  have hnonneg := Riesz1.fderiv_fderiv_nonneg_of_convexOn ho hc.1 hc
    (hV.sub hQ.contDiffOn) hx v
  have heq : fderiv ℝ (fun x => V x - Q x) =ᶠ[𝓝 x]
      fun z => fderiv ℝ V z - fderiv ℝ Q z := by
    filter_upwards [ho.mem_nhds hx] with z hz
    exact fderiv_fun_sub
      ((hV.differentiableOn (by norm_num)).differentiableAt (ho.mem_nhds hz))
      (hQ.differentiable (by norm_num)).differentiableAt
  have hVD : DifferentiableAt ℝ (fderiv ℝ V) x :=
    ((hV.fderiv_of_isOpen ho (by norm_num : 1 + 1 ≤ (2 : WithTop ℕ∞))).differentiableOn
      (by norm_num)).differentiableAt (ho.mem_nhds hx)
  have hQD : DifferentiableAt ℝ (fderiv ℝ Q) x :=
    (((hQ.contDiffOn (s := Set.univ)).fderiv_of_isOpen isOpen_univ
      (by norm_num : 1 + 1 ≤ (2 : WithTop ℕ∞))).differentiableOn
        (by norm_num)).differentiableAt (isOpen_univ.mem_nhds (Set.mem_univ x))
  rw [heq.fderiv_eq, fderiv_fun_sub hVD hQD] at hnonneg
  have hfirst : fderiv ℝ Q = fun z => a • innerSL ℝ z := by
    funext z
    rw [((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_mul (a / 2)).fderiv]
    ext u
    simp only [smul_apply, smul_eq_mul, two_smul, add_apply]
    ring
  have hsecond : fderiv ℝ (fderiv ℝ Q) x v v = a * ‖v‖ ^ 2 := by
    rw [hfirst]
    erw [((innerSL ℝ).hasFDerivAt (x := x) |>.const_smul a).fderiv]
    change a * innerSL ℝ v v = a * ‖v‖ ^ 2
    congr 1
    exact real_inner_self_eq_norm_sq v
  simp only [sub_apply, sub_nonneg] at hnonneg
  rw [hsecond] at hnonneg
  exact hnonneg


/-- See the proof of Lemma B.1 in the paper, all clauses. The constants precede
all volumes, retained sets, scales and temperatures in a compact positive
temperature interval. Proper marginals are indexed by arbitrary retained
charts, which enumerate every nonempty proper gap set. Their C² regularity
and classical lower Hessian are conclusions. Measure domination expresses
the almost everywhere density bound. -/
theorem shortRange_upperTilt_complete (s βlo βhi : ℝ) (hs : 1 < s)
    (_hβlo : 0 < βlo) (_hβhi : βlo ≤ βhi) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      (∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (θ : PhysicalCutoff)
        (R : {R : ℝ // 0 < R}), 1 ≤ (R : ℝ) → ∀ J : Finset (Fin (N : ℕ)),
        J.Nonempty →
        letI := gibbsMeasure_probability p N
        letI := upperTiltedParticleMeasure_probability p N θ R J
        letI : IsProbabilityMeasure (gapLaw p N) := by unfold gapLaw; infer_instance
        (gibbsMeasure p N) {X | upperGapPenalty θ R J X ≠ 0} ≤
          ENNReal.ofReal (C * J.card * Real.exp (-c * R)) ∧
        (C * J.card * Real.exp (-c * R) ≤ 1 / 2 →
          (1 / 2 : ℝ≥0∞) ≤ upperGapNormalizer p N θ R J ∧
          totalVariation (gapLaw p N)
              ((upperTiltedParticleMeasure p N θ R J).map gapVector) ≤
            ENNReal.ofReal (C * J.card * Real.exp (-c * R)) ∧
          (upperTiltedParticleMeasure p N θ R J).map gapVector ≤
            (2 : ℝ≥0∞) • gapLaw p N) ∧
        ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
          ContDiffOn ℝ (⊤ : ℕ∞) W (gapAmbientDomain N) ∧
          (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
            W y.val = physicalAmbientGapEnergy p N y) ∧
          ∀ (y : Fin (N : ℕ) → ℝ), y ∈ Riesz1.gapSimplex N →
            ∀ v : EuclideanSpace ℝ (Fin (N : ℕ)),
              c * (R : ℝ) ^ (-s - 2) * (∑ i ∈ J, (v i) ^ 2) ≤
                fderiv ℝ (fderiv ℝ (fun z => W z + ∑ i ∈ J, θ.val (z i / R)))
                  (WithLp.toLp 2 y) v v) ∧
      ∀ (n m : ℕ), 1 ≤ n → ∀ (σ : Equiv.Perm (Fin (n + m + 1)))
        (θ : PhysicalCutoff) (R : {R : ℝ // 0 < R}), 1 ≤ (R : ℝ) →
        let J := Finset.univ.image (fun j : Fin n => σ (j.castAdd m).castSucc)
        let D := ProperMarginalChart.penalizedChartDensity p n m σ θ R.val⁻¹ J false
        let V := fun x => -Real.log (AffineFibre.fibreMass volume D x).toReal
        ContDiffOn ℝ 2 V (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) ∧
          (upperTiltedParticleMeasure p (n + m).succPNat θ R J).map
            (fun X : Riesz1.Configuration (n + m).succPNat =>
              (RetainedSimplex.coordinates n m σ (WithLp.toLp 2 (gapVector X))).1) =
            (volume.restrict (AffineSimplex.chartDomain n ((n + m : ℕ) + 1))).tilted
              (fun x => -V x) ∧
          ∀ x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
            ∀ v : EuclideanSpace ℝ (Fin n),
              c * p.val.1 * (R : ℝ) ^ (-s - 2) * ‖v‖ ^ 2 ≤
                fderiv ℝ (fderiv ℝ V) x v v := by
  let c := min (Real.log 2 / 8) 1
  have hc : 0 < c := lt_min (div_pos (Real.log_pos one_lt_two) (by norm_num)) zero_lt_one
  have hc₁ : c ≤ 1 := min_le_right _ _
  have hca : c ≤ Real.log 2 / 8 := min_le_left _ _
  refine ⟨c, 3, hc, by norm_num, ?_⟩
  intro p hps _ _
  have hsp : 1 < p.val.2 := hps.symm ▸ hs
  have hb (N : ℕ+) (J : Finset (Fin (N : ℕ))) (R : {R : ℝ // 0 < R}) :
      3 * J.card * Real.exp (-(Real.log 2 / 8) * R) ≤
        3 * J.card * Real.exp (-c * R) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    nlinarith [R.property]
  constructor
  · intro N hN θ R hR J _
    let _ := gibbsMeasure_probability p N
    let _ := upperTiltedParticleMeasure_probability p N θ R J
    let _ : IsProbabilityMeasure (gapLaw p N) := by unfold gapLaw; infer_instance
    refine ⟨(upperGapPenalty_event_bound p N hN θ R J).trans
      (ENNReal.ofReal_le_ofReal (hb N J R)), ?_, ?_⟩
    · intro hsmall
      have hz := upperGapNormalizer_ge_half p N hN θ R J ((hb N J R).trans hsmall)
      refine ⟨hz, (upperTiltedGapLaw_totalVariation p N hN θ R J).trans
        (ENNReal.ofReal_le_ofReal (hb N J R)), ?_⟩
      have hm := Measure.map_mono (f := @gapVector N)
        (upperTiltedParticleMeasure_le_two p N θ R J hz)
        (Riesz1.measurable_gapVector N)
      rw [Measure.map_smul] at hm
      · exact hm
      · exact (Riesz1.measurable_gapVector N).aemeasurable
    · obtain ⟨W, hW, hval, hh⟩ := upperGapPenalty_curvature p hsp N hN θ R hR J
      refine ⟨W, hW, hval, fun y hy v => ?_⟩
      have hn : 0 ≤ (R : ℝ) ^ (-s - 2) * ∑ i ∈ J, (v i) ^ 2 := by positivity
      have hl := mul_le_mul_of_nonneg_right hc₁ hn
      simp only [one_mul, ← mul_assoc] at hl
      exact hl.trans (by simpa only [hps] using hh y hy v)
  · intro n m hn σ θ R hR
    obtain ⟨hV, hh⟩ := upperTilt_marginal_hessian p hsp n m hn σ θ R hR
    refine ⟨hV, (upperTilt_marginal_gibbs p hsp n m hn σ θ R hR).2, fun x hx v => ?_⟩
    have hn' : 0 ≤ p.val.1 * (R : ℝ) ^ (-s - 2) * ‖v‖ ^ 2 := by
      exact mul_nonneg (mul_nonneg p.property.1.le (Real.rpow_nonneg R.property.le _))
        (sq_nonneg _)
    have hl := mul_le_mul_of_nonneg_right hc₁ hn'
    simp only [one_mul, ← mul_assoc] at hl
    exact hl.trans (by simpa only [hps] using hh x hx v)

end Riesz2.DecayShort
