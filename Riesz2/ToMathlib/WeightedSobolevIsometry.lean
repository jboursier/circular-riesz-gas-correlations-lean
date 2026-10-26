/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.WeightedSobolev.VariationalPairing
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Tactic

/-!
# Orthonormal changes of coordinates for weighted Sobolev spaces

The existing Riesz1 H¹ completion is preserved by linear isometries.
These bridges keep the intrinsic metric in Subsection 3.1 and
the proof of Proposition 3.3. They introduce no new Sobolev space.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Topology

namespace Riesz2.SobolevIsometry

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
/-- Gradient chain rule in an orthonormal chart (Subsection 3.1). -/
theorem gradient_comp_symm (e : E ≃ₗᵢ[ℝ] F) {f : E → ℝ} {x : F}
    (hf : DifferentiableAt ℝ f (e.symm x)) :
    gradient (f ∘ e.symm) x = e (gradient f (e.symm x)) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, _root_.fderiv_comp x hf e.symm.differentiableAt]
  have he : fderiv ℝ (e.symm : F → E) x =
      e.symm.toContinuousLinearEquiv.toContinuousLinearMap :=
    e.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.fderiv
  rw [he]
  change fderiv ℝ f (e.symm x) (e.symm v) = _
  rw [← inner_gradient_left]
  simpa using (e.inner_map_map (gradient f (e.symm x)) (e.symm v)).symm

omit [CompleteSpace E] [CompleteSpace F] in
/-- Density push-forward under an orthonormal chart, allowing merely
locally measurable densities as in the Gibbs convention. -/
theorem map_withDensity (e : E ≃ₗᵢ[ℝ] F) (μ : Measure E) (w : E → ENNReal) :
    (μ.withDensity w).map e = (μ.map e).withDensity (w ∘ e.symm) := by
  let em := e.toHomeomorph.toMeasurableEquiv
  ext A hA
  erw [Measure.map_apply em.measurable hA, withDensity_apply _ (em.measurable hA),
    withDensity_apply _ hA, em.measurableEmbedding.restrict_map,
    em.measurableEmbedding.lintegral_map]
  simp [em]

/-- The existing weighted H¹ predicate in orthonormal coordinates
(Subsection 3.1). The measure is pushed forward and the gradient is rotated. -/
theorem weightedH1 (e : E ≃ₗᵢ[ℝ] F) {μ : Measure E} {U : Set E}
    (hμ : ∀ᵐ x ∂μ, x ∈ U) {f : E → ℝ} {g : E → E}
    (hfg : Riesz1.WeightedSobolev.IsWeightedH1 μ U f g) :
    Riesz1.WeightedSobolev.IsWeightedH1 (μ.map e) (e '' U)
      (f ∘ e.symm) (fun y => e (g (e.symm y))) := by
  let em := e.toHomeomorph.toMeasurableEquiv
  have hs : MeasurePreserving e.symm (μ.map e) μ := by
    refine ⟨em.symm.measurable, ?_⟩
    exact em.map_symm_map
  obtain ⟨hf, hg, φ, hφ, hv, hd⟩ := hfg
  refine ⟨hf.comp_measurePreserving hs,
    e.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' (hg.comp_measurePreserving hs),
    fun k => φ k ∘ e.symm, fun k => ?_, ?_, ?_⟩
  · obtain ⟨W, ho, hUW, hsm⟩ := hφ k
    refine ⟨e '' W, e.toHomeomorph.isOpenMap W ho, ?_, ?_⟩
    · change closure (e.toHomeomorph '' U) ⊆ _
      rw [← e.toHomeomorph.image_closure]
      exact image_mono hUW
    · exact hsm.comp e.symm.contDiff.contDiffOn (by rintro y ⟨z, hz, rfl⟩; simpa using hz)
  · convert hv using 1
    funext k
    erw [em.measurableEmbedding.lintegral_map]
    simp [em]
  · convert hd using 1
    funext k
    erw [em.measurableEmbedding.lintegral_map]
    apply lintegral_congr_ae
    filter_upwards [hμ] with x hx
    have hfφ : DifferentiableAt ℝ (φ k) x := by
      obtain ⟨W, ho, hUW, hsm⟩ := hφ k
      exact (hsm.contDiffAt (ho.mem_nhds (hUW (subset_closure hx)))).differentiableAt (by simp)
    change ‖gradient (φ k ∘ e.symm) (e x) - e (g (e.symm (e x)))‖ₑ ^ 2 = _
    rw [gradient_comp_symm e (by simpa using hfφ)]
    simp only [LinearIsometryEquiv.symm_apply_apply, ← map_sub, e.enorm_map]

omit [CompleteSpace E] [CompleteSpace F] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
/-- Hessian chain rule in an orthonormal affine chart (Appendix A). -/
theorem hessian_comp_symm (e : E ≃ₗᵢ[ℝ] F) {U : Set E} (hU : IsOpen U)
    {f : E → ℝ} (hf : ContDiffOn ℝ 2 f U) {x : F} (hx : e.symm x ∈ U) (v w : F) :
    fderiv ℝ (fderiv ℝ (f ∘ e.symm)) x v w =
      fderiv ℝ (fderiv ℝ f) (e.symm x) (e.symm v) (e.symm w) := by
  let L := e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have heq : fderiv ℝ (f ∘ e.symm) =ᶠ[𝓝 x]
      fun y => (fderiv ℝ f (e.symm y)).comp L := by
    filter_upwards [(hU.preimage e.symm.continuous).mem_nhds hx] with y hy
    have hd := (hf.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)
    rw [_root_.fderiv_comp y hd e.symm.differentiableAt]
    rw [show fderiv ℝ (e.symm : F → E) y = L from L.hasFDerivAt.fderiv]
  have h₂ : DifferentiableAt ℝ (fderiv ℝ f) (e.symm x) :=
    ((hf.contDiffAt (hU.mem_nhds hx)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have hh := (h₂.hasFDerivAt.comp x L.hasFDerivAt).clm_comp (hasFDerivAt_const L x)
  simp only [Function.comp_apply] at hh
  rw [heq.fderiv_eq, hh.fderiv]
  simp [L]

end Riesz2.SobolevIsometry
