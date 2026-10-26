/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.DominatedFibreCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Compactly supported continuously differentiable fibre integrals

Uniform domination and first derivatives under an integral. The support and
regularity premises apply to the joint function, so the exceptional set and
integrable majorant are independent of the parameter.
-/

public section
noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Riesz2.CompactFibreC1

variable {X Y F : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  (μ : Measure Y) [IsFiniteMeasureOnCompacts μ]

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] [SecondCountableTopology Y]
  [NormedSpace ℝ F] [CompleteSpace F] in
/-- A single integrable majorant for all parameter slices of a continuous
function of compact support. -/
theorem bound {f : X × Y → F} (hf : Continuous f) (hs : HasCompactSupport f) :
    ∃ b : Y → ℝ, Integrable b μ ∧ ∀ x z, ‖f (x,z)‖ ≤ b z := by
  classical
  let K := Prod.snd '' tsupport f
  have hK : IsCompact K := hs.isCompact.image continuous_snd
  obtain ⟨C, hC⟩ := (hs.isCompact_range hf).bddAbove_image continuous_norm.continuousOn
  refine ⟨K.indicator (fun _ => max C 0), ?_, fun x z => ?_⟩
  · exact (integrable_indicator_iff hK.measurableSet).mpr
      (integrableOn_const (hK.measure_lt_top (μ := μ)).ne)
  · by_cases hz : z ∈ K
    · rw [indicator_of_mem hz]
      exact (hC ⟨f (x,z), ⟨(x,z), rfl⟩, rfl⟩).trans (le_max_left _ _)
    · rw [indicator_of_notMem hz, show f (x,z) = 0 from
        Function.notMem_support.mp (fun h => hz ⟨(x,z), subset_closure h, rfl⟩), norm_zero]

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] [NormedSpace ℝ F] [CompleteSpace F] in
/-- Every slice is integrable, including parameter values at which the
slice vanishes identically. -/
theorem integrable {f : X × Y → F} (hf : Continuous f) (hs : HasCompactSupport f)
    (x : X) : Integrable (fun z => f (x,z)) μ := by
  obtain ⟨b, hb, hbound⟩ := bound μ hf hs
  exact hb.mono' ((hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Eventually.of_forall (hbound x))

omit [CompleteSpace F] in
set_option backward.isDefEq.respectTransparency false in
/-- Compact support and C¹ joint regularity supply the fixed-fibre dominated
derivative contract, on any open parameter set. -/
theorem domination {f : X × Y → F} (hf : ContDiff ℝ 1 f)
    (hs : HasCompactSupport f) (U : Set X) (hU : IsOpen U) :
    DominatedFibre.DominatedFDerivOn μ U (fun x z => f (x,z))
      (fun x z => (fderiv ℝ f (x,z)).comp (ContinuousLinearMap.inl ℝ X Y)) := by
  let S := (ContinuousLinearMap.compL ℝ X (X × Y) F).flip
    (ContinuousLinearMap.inl ℝ X Y)
  let df : X × Y → X →L[ℝ] F := fun q => S (fderiv ℝ f q)
  have hd : Continuous df := S.continuous.comp (hf.continuous_fderiv (by norm_num))
  have hc : HasCompactSupport df := (hs.fderiv ℝ).comp_left S.map_zero
  obtain ⟨b, hb, hbound⟩ := bound μ hd hc
  constructor
  · intro x _
    exact integrable μ hf.continuous hs x
  · intro x _
    exact (hd.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · intro x hx
    refine ⟨U, hU.mem_nhds hx, Subset.rfl, b, hb,
      Eventually.of_forall (fun z y _ => hbound y z),
      Eventually.of_forall (fun z y _ => ?_)⟩
    have hp : HasFDerivAt (fun t : X => (t,z)) (ContinuousLinearMap.inl ℝ X Y) y := by
      convert (hasFDerivAt_id y).prodMk (hasFDerivAt_const z y) using 1 <;> rfl
    exact (hf.differentiable (by norm_num) (y,z)).hasFDerivAt.comp y hp

omit [CompleteSpace F] in
set_option backward.isDefEq.respectTransparency false in
/-- Integrating out a compactly supported C¹ joint density preserves C¹
regularity and compact support. -/
theorem integral {f : X × Y → F} (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    ContDiff ℝ 1 (fun x => ∫ z, f (x,z) ∂μ) ∧
      HasCompactSupport (fun x => ∫ z, f (x,z) ∂μ) := by
  let S := (ContinuousLinearMap.compL ℝ X (X × Y) F).flip
    (ContinuousLinearMap.inl ℝ X Y)
  let df : X × Y → X →L[ℝ] F := fun q => S (fderiv ℝ f q)
  have hd : Continuous df := S.continuous.comp (hf.continuous_fderiv (by norm_num))
  have hc : HasCompactSupport df := (hs.fderiv ℝ).comp_left S.map_zero
  obtain ⟨b, hb, hbound⟩ := bound μ hd hc
  refine ⟨contDiff_one_iff_hasFDerivAt.mpr ⟨fun x => ∫ z, df (x,z) ∂μ, ?_, ?_⟩, ?_⟩
  · apply continuous_iff_continuousAt.mpr
    intro x
    exact continuousAt_of_dominated
      (Eventually.of_forall (fun y => (hd.comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable))
      (Eventually.of_forall (fun y => Eventually.of_forall (hbound y))) hb
      (Eventually.of_forall (fun z => (hd.comp
        (continuous_id.prodMk continuous_const)).continuousAt))
  · intro x
    exact (domination μ hf hs univ isOpen_univ).hasFDerivAt_integral (mem_univ x)
  · apply HasCompactSupport.intro (hs.isCompact.image continuous_fst)
    intro x hx
    apply integral_eq_zero_of_ae
    exact Eventually.of_forall fun z => Function.notMem_support.mp
      (fun hz => hx ⟨(x,z), subset_closure hz, rfl⟩)

section Score

variable {A : Type*} [MeasurableSpace A] {ν : Measure A}
  {w g : ℝ → A → ℝ} {dw dn : ℝ → A → ℝ →L[ℝ] ℝ} {x : ℝ}

set_option backward.isDefEq.respectTransparency false in
/-- First derivative of a normalized expectation under L¹ score and
product integrability. Both integrabilities are concluded from the
dominated density and numerator derivatives, rather than supplied as
additional score hypotheses. -/
theorem normalized_hasDerivAt_score
    (hw : DominatedFibre.DominatedFDerivOn ν univ w dw)
    (hg : DominatedFibre.DominatedFDerivOn ν univ (fun t y => w t y * g t y) dn)
    (hn : ∀ y, 0 ≤ w x y) (hp : 0 < ∫ y, w x y ∂ν) (S D : A → ℝ)
    (hforce : ∀ᵐ y ∂ν, dw x y 1 = -w x y * S y)
    (hnum : ∀ᵐ y ∂ν, dn x y 1 = w x y * (D y - g x y * S y))
    (hD : Integrable (fun y => w x y * D y) ν) :
    let ρ := AffineFibre.normalizedMeasure ν (fun y => ENNReal.ofReal (w x y))
      (by rw [← ofReal_integral_eq_lintegral_ofReal (hw.integrable x (mem_univ x))
            (Eventually.of_forall hn)]
          exact ENNReal.ofReal_ne_zero_iff.mpr hp)
      (by rw [← ofReal_integral_eq_lintegral_ofReal (hw.integrable x (mem_univ x))
            (Eventually.of_forall hn)]
          exact ENNReal.ofReal_ne_top)
    Integrable S ρ ∧ Integrable (fun y => g x y * S y) ρ ∧
      HasDerivAt (fun t => (∫ y, w t y * g t y ∂ν) / ∫ y, w t y ∂ν)
        ((∫ y, D y ∂ρ) - ProbabilityTheory.covariance (g x) S ρ) x := by
  intro ρ
  have hwi := hw.integrable x (mem_univ x)
  have hdi := (hw.integrable_derivative (mem_univ x)).apply_continuousLinearMap 1
  have hni := (hg.integrable_derivative (mem_univ x)).apply_continuousLinearMap 1
  have hS : Integrable (fun y => w x y * S y) ν :=
    hdi.neg.congr (hforce.mono fun y hy => by dsimp only [Pi.neg_apply, Pi.sub_apply]; rw [hy]; ring)
  have hGS : Integrable (fun y => w x y * (g x y * S y)) ν :=
    (hD.sub hni).congr (hnum.mono fun y hy => by dsimp only [Pi.neg_apply, Pi.sub_apply]; rw [hy]; ring)
  have hSr : Integrable S ρ :=
    (DominatedFibre.integrable_normalizedMeasure_iff hwi hn hp S).mpr hS
  have hGSr : Integrable (fun y => g x y * S y) ρ :=
    (DominatedFibre.integrable_normalizedMeasure_iff hwi hn hp _).mpr hGS
  have hgr : Integrable (g x) ρ :=
    (DominatedFibre.integrable_normalizedMeasure_iff hwi hn hp _).mpr
      (hg.integrable x (mem_univ x))
  have : IsProbabilityMeasure ρ := by
    constructor
    dsimp only [ρ]
    rw [AffineFibre.normalizedMeasure_eq_smul, Measure.smul_apply,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, smul_eq_mul,
      ← ofReal_integral_eq_lintegral_ofReal hwi (Eventually.of_forall hn)]
    exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top
  have hcov : ProbabilityTheory.covariance (g x) S ρ =
      (∫ y, g x y * S y ∂ρ) - (∫ y, g x y ∂ρ) * ∫ y, S y ∂ρ := by
    simp_rw [ProbabilityTheory.covariance, sub_mul, mul_sub]
    repeat rw [integral_sub]
    · simp only [integral_mul_const, integral_const_mul, integral_const,
        probReal_univ, smul_eq_mul, one_mul]
      ring
    · exact hSr.const_mul _
    · exact integrable_const _
    · exact hGSr
    · exact hgr.mul_const _
    · exact hGSr.sub (hgr.mul_const _)
    · exact (hSr.const_mul _).sub (integrable_const _)
  have hd : (∫ y, dw x y 1 ∂ν) = -(∫ y, w x y * S y ∂ν) := by
    rw [← integral_neg]
    exact integral_congr_ae (hforce.mono fun y hy => by dsimp only [Pi.neg_apply, Pi.sub_apply]; rw [hy]; ring)
  have hdn : (∫ y, dn x y 1 ∂ν) =
      (∫ y, w x y * D y ∂ν) - ∫ y, w x y * (g x y * S y) ∂ν := by
    rw [← integral_sub hD hGS]
    exact integral_congr_ae (hnum.mono fun y hy => by dsimp only [Pi.neg_apply, Pi.sub_apply]; rw [hy]; ring)
  refine ⟨hSr, hGSr, ?_⟩
  have hquot := (DominatedFibre.hasFDerivAt_normalized_integral hw hg
    (mem_univ x) hp).hasDerivAt
  have heq : (fun t => (∫ y, w t y ∂ν)⁻¹ • ∫ y, w t y * g t y ∂ν) =
      fun t => (∫ y, w t y * g t y ∂ν) / ∫ y, w t y ∂ν := by
    funext t
    simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq] at hquot
  convert hquot using 1
  rw [hcov]
  dsimp only [ρ]
  simp_rw [DominatedFibre.integral_normalizedMeasure hwi hn hp]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul,
    ContinuousLinearMap.integral_apply (hw.integrable_derivative (mem_univ x)),
    ContinuousLinearMap.integral_apply (hg.integrable_derivative (mem_univ x))]
  rw [hd, hdn]
  ring

end Score

end Riesz2.CompactFibreC1
