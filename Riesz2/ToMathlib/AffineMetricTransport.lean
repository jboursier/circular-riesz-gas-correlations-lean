/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Tactic

/-!
# Derivatives and distances under an affine metric change

General finite dimensional infrastructure for Subsection 3.2 and Lemma A.1.
-/

@[expose] public section

noncomputable section

namespace Riesz2.AffineMetricTransport

open Filter Set Metric
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The second derivative of an affine pullback is the bilinear pullback. -/
theorem hessian_comp_affine {f : E → ℝ} (A : F →L[ℝ] E) (v : E) {x : F}
    (hf : ContDiffAt ℝ 2 f (A x + v)) (u w : F) :
    fderiv ℝ (fderiv ℝ (fun z => f (A z + v))) x u w =
      fderiv ℝ (fderiv ℝ f) (A x + v) (A u) (A w) := by
  have hnear := ((A.continuous.add continuous_const).continuousAt.tendsto).eventually
    (hf.eventually (by norm_num))
  have hgrad : fderiv ℝ (fun z => f (A z + v)) =ᶠ[𝓝 x]
      fun z => (fderiv ℝ f (A z + v)).comp A := by
    filter_upwards [hnear] with z hz
    exact ((hz.differentiableAt (by norm_num)).hasFDerivAt.comp z
      (A.hasFDerivAt.add_const v)).fderiv
  rw [hgrad.fderiv_eq]
  have hc : HasFDerivAt (fun z => fderiv ℝ f (A z + v))
      ((fderiv ℝ (fderiv ℝ f) (A x + v)).comp A) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt.comp x (A.hasFDerivAt.add_const v)
  have hd := hc.clm_comp (hasFDerivAt_const A x)
  rw [hd.fderiv]
  simp

/-- Both boundary-distance comparisons, in terms of the map and inverse operator norms.
No positivity of either norm, and no nonzero-dimensional hypothesis, is needed. -/
theorem infDist_affine_image_bounds [ProperSpace E] [ProperSpace F]
    (e : E ≃L[ℝ] F) (v : F) {s : Set E} (hs : IsClosed s) (hne : s.Nonempty) (x : E) :
    infDist (e x + v) ((fun z => e z + v) '' s) ≤
        ‖e.toContinuousLinearMap‖ * infDist x s ∧
      infDist x s ≤ ‖e.symm.toContinuousLinearMap‖ *
        infDist (e x + v) ((fun z => e z + v) '' s) := by
  let T : E ≃ₜ F := e.toHomeomorph.trans (Homeomorph.addRight v)
  have hclosed : IsClosed ((fun z => e z + v) '' s) := T.isClosedMap s hs
  have hnonempty : ((fun z => e z + v) '' s).Nonempty := hne.image _
  constructor
  · obtain ⟨z, hz, hdist⟩ := hs.exists_infDist_eq_dist hne x
    calc
      infDist (e x + v) ((fun z => e z + v) '' s) ≤ dist (e x + v) (e z + v) :=
        infDist_le_dist_of_mem ⟨z, hz, rfl⟩
      _ = ‖e (x - z)‖ := by rw [dist_add_right, dist_eq_norm, map_sub]
      _ ≤ ‖e.toContinuousLinearMap‖ * ‖x - z‖ := e.toContinuousLinearMap.le_opNorm _
      _ = _ := by rw [← dist_eq_norm, ← hdist]
  · obtain ⟨y, ⟨z, hz, rfl⟩, hdist⟩ := hclosed.exists_infDist_eq_dist hnonempty (e x + v)
    calc
      infDist x s ≤ dist x z := infDist_le_dist_of_mem hz
      _ = ‖e.symm (e (x - z))‖ := by rw [e.symm_apply_apply, dist_eq_norm]
      _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e (x - z)‖ :=
        e.symm.toContinuousLinearMap.le_opNorm _
      _ = _ := by rw [hdist, dist_add_right, dist_eq_norm, map_sub]

end Riesz2.AffineMetricTransport
