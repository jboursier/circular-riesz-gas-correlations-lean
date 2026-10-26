/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.DominatedFibreCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Continuity of dominated fibre derivatives

Local domination of the second derivative and almost everywhere continuity
of its fibres imply C² regularity of the integral. The hypotheses
use the hypotheses in `DominatedFibreCalculus`.
-/

public section

open MeasureTheory Set Filter
open scoped Topology

namespace Riesz2.DominatedFibre

variable {A E F : Type*} [MeasurableSpace A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure A} {U : Set E} {f : E → A → F}
  {df : E → A → E →L[ℝ] F}
  {ddf : E → A → E →L[ℝ] E →L[ℝ] F}

/-- The integrated derivative is continuous wherever its fibres are almost
everywhere continuous and the fixed-fibre domination contract holds. -/
theorem DominatedFDerivOn.continuousAt_integral_derivative
    (h : DominatedFDerivOn μ U f df) {x : E} (hx : x ∈ U)
    (hc : ∀ᵐ y ∂μ, ContinuousAt (fun z => df z y) x) :
    ContinuousAt (fun z => ∫ y, df z y ∂μ) x := by
  obtain ⟨s, hs, hsU, b, hb, hbound, _⟩ := h.locally_dominated x hx
  exact continuousAt_of_dominated
    (mem_of_superset hs fun z hz => h.derivative_measurable z (hsU hz))
    (mem_of_superset hs fun z hz => hbound.mono fun y hy => hy z hz) hb hc

/-- C² regularity of a fibre integral from two dominated derivatives and
almost everywhere continuity of the second derivative at each parameter. -/
theorem contDiffOn_integral_two (hU : IsOpen U)
    (h : DominatedFDerivOn μ U f df) (h' : DominatedFDerivOn μ U df ddf)
    (hc : ∀ x ∈ U, ∀ᵐ y ∂μ, ContinuousAt (fun z => ddf z y) x) :
    ContDiffOn ℝ 2 (fun z => ∫ y, f z y ∂μ) U := by
  have heq : EqOn (fderiv ℝ (fun z => ∫ y, f z y ∂μ))
      (fun z => ∫ y, df z y ∂μ) U := fun x hx => h.fderiv_integral hx
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl,
    contDiffOn_succ_iff_fderiv_of_isOpen hU]
  refine ⟨fun x hx => (h.hasFDerivAt_integral hx).hasFDerivWithinAt.differentiableWithinAt,
    by norm_num, ?_⟩
  apply ContDiffOn.congr _ heq
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl,
    contDiffOn_succ_iff_fderiv_of_isOpen hU]
  refine ⟨fun x hx => (h'.hasFDerivAt_integral hx).hasFDerivWithinAt.differentiableWithinAt,
    by norm_num, ?_⟩
  rw [contDiffOn_zero]
  intro x hx
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.congr _
    (mem_of_superset (hU.mem_nhds hx) fun z hz => (h'.fderiv_integral hz).symm)
  exact h'.continuousAt_integral_derivative hx (hc x hx)

end Riesz2.DominatedFibre
