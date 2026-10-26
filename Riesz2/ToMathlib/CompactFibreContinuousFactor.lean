/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.CompactFibreC1
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Compact fibre integration with a continuous fixed factor

A factor depending only on the integrated variable need not be differentiable.
This permits changing total mass through a coordinate unused by an observable
in the proof of Lemma 6.5.
-/

public section
noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Riesz2.CompactFibreContinuousFactor

variable {X Y : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  (μ : Measure Y) [IsFiniteMeasureOnCompacts μ]

omit [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y] in
/-- A shear of a real parameter and a finite-dimensional fibre preserves
compact support and C¹ regularity. -/
theorem shear [FiniteDimensional ℝ Y] {w : ℝ × Y → ℝ}
    (hw : ContDiff ℝ 1 w) (hs : HasCompactSupport w) (a : Y) :
    ContDiff ℝ 1 (fun q : ℝ × Y => w (q.1, q.2 + q.1 • a)) ∧
      HasCompactSupport (fun q : ℝ × Y => w (q.1, q.2 + q.1 • a)) := by
  have : ContinuousSMul ℝ (ℝ × Y) := Prod.continuousSMul
  let T : (ℝ × Y) →L[ℝ] (ℝ × Y) :=
    (ContinuousLinearMap.fst ℝ ℝ Y).prod
      (ContinuousLinearMap.snd ℝ ℝ Y + (ContinuousLinearMap.fst ℝ ℝ Y).smulRight a)
  have hinj : Function.Injective T := by
    intro q r h
    change (q.1, q.2 + q.1 • a) = (r.1, r.2 + r.1 • a) at h
    obtain ⟨hL, hz⟩ := Prod.mk.inj h
    rw [hL] at hz
    exact Prod.ext hL (add_right_cancel hz)
  exact ⟨hw.comp T.contDiff,
    hs.comp_isClosedEmbedding
      (T.toLinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hinj))⟩

/-- A continuous fixed factor preserves C¹ regularity in a real parameter,
with the actual derivative integral. -/
theorem integral {w : ℝ × Y → ℝ} (hw : ContDiff ℝ 1 w)
    (hs : HasCompactSupport w) {g : Y → ℝ} (hg : Continuous g) :
    ContDiff ℝ 1 (fun x => ∫ z, w (x,z) * g z ∂μ) ∧
      ∀ x, HasDerivAt (fun t => ∫ z, w (t,z) * g z ∂μ)
        (∫ z, fderiv ℝ w (x,z) (1,0) * g z ∂μ) x := by
  have hw' : Continuous (fun q => fderiv ℝ w q (1,0)) :=
    (hw.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hs' : HasCompactSupport (fun q => fderiv ℝ w q (1,0)) :=
    (hs.fderiv ℝ).comp_left
      (g := fun T : (ℝ × Y) →L[ℝ] ℝ => T (1,0)) (by simp)
  have hn : Continuous (fun q : ℝ × Y => fderiv ℝ w q (1,0) * g q.2) :=
    hw'.mul (hg.comp continuous_snd)
  have hns : HasCompactSupport (fun q : ℝ × Y => fderiv ℝ w q (1,0) * g q.2) :=
    hs'.mul_right
  obtain ⟨b, hb, hbound⟩ := CompactFibreC1.bound μ hn hns
  have hd x : HasDerivAt (fun t => ∫ z, w (t,z) * g z ∂μ)
      (∫ z, fderiv ℝ w (x,z) (1,0) * g z ∂μ) x := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := x) (bound := b)
      (F := fun t z => w (t,z) * g z)
      (F' := fun t z => fderiv ℝ w (t,z) (1,0) * g z)
      (s := univ) univ_mem
      ?_ ?_ ?_ ?_ ?_ ?_).2
    · exact Eventually.of_forall fun t =>
        ((hw.continuous.comp (continuous_const.prodMk continuous_id)).mul hg).aestronglyMeasurable
    · exact CompactFibreC1.integrable μ (hw.continuous.mul (hg.comp continuous_snd))
        hs.mul_right x
    · exact (hn.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · exact Eventually.of_forall fun z t _ => hbound t z
    · exact hb
    · apply Eventually.of_forall
      intro z t _
      have hp : HasDerivAt (fun t : ℝ => (t,z)) (1,0) t :=
        (hasDerivAt_id t).prodMk (hasDerivAt_const t z)
      exact (((hw.differentiable (by norm_num) (t,z)).hasFDerivAt.comp_hasDerivAt t hp).mul_const (g z))
  refine ⟨contDiff_one_iff_deriv.mpr ⟨fun x => (hd x).differentiableAt, ?_⟩, hd⟩
  have he : deriv (fun t => ∫ z, w (t,z) * g z ∂μ) =
      fun t => ∫ z, fderiv ℝ w (t,z) (1,0) * g z ∂μ := funext fun x => (hd x).deriv
  rw [he]
  apply continuous_iff_continuousAt.mpr
  intro x
  exact continuousAt_of_dominated
    (Eventually.of_forall (fun t => (hn.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable))
    (Eventually.of_forall (fun t => Eventually.of_forall (hbound t))) hb
    (Eventually.of_forall (fun z => (hn.comp
      (continuous_id.prodMk continuous_const)).continuousAt))

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] in
/-- Pointwise convergence of continuous factors under a continuous envelope
passes through any continuous compactly supported weight. -/
theorem integral_tendsto {v : X × Y → ℝ} (hv : Continuous v)
    (hs : HasCompactSupport v) {g : ℕ → Y → ℝ} {g₀ H : Y → ℝ}
    (hg : ∀ k, Continuous (g k)) (hH : Continuous H)
    (hb : ∀ k z, ‖g k z‖ ≤ H z)
    (hp : ∀ z, Tendsto (fun k => g k z) atTop (𝓝 (g₀ z))) (x : X) :
    Tendsto (fun k => ∫ z, v (x,z) * g k z ∂μ) atTop
      (𝓝 (∫ z, v (x,z) * g₀ z ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun z => ‖v (x,z)‖ * H z)
  · intro k
    exact ((hv.comp (continuous_const.prodMk continuous_id)).mul (hg k)).aestronglyMeasurable
  · exact CompactFibreC1.integrable μ (hv.norm.mul (hH.comp continuous_snd)) hs.norm.mul_right x
  · intro k
    exact Eventually.of_forall fun z => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hb k z) (norm_nonneg _)
  · exact Eventually.of_forall fun z => tendsto_const_nhds.mul (hp z)

/-- The derivatives of normalized fibre integrals converge pointwise when
continuous fixed factors converge under a common continuous envelope.
Strict positivity excludes a zero normalizer. -/
theorem normalized_deriv_tendsto {w : ℝ × Y → ℝ} (hw : ContDiff ℝ 1 w)
    (hs : HasCompactSupport w) {g : ℕ → Y → ℝ} {g₀ H : Y → ℝ}
    (hg : ∀ k, Continuous (g k)) (hg₀ : Continuous g₀) (hH : Continuous H)
    (hb : ∀ k z, ‖g k z‖ ≤ H z)
    (hp : ∀ z, Tendsto (fun k => g k z) atTop (𝓝 (g₀ z)))
    (x : ℝ) (hx : 0 < ∫ z, w (x,z) ∂μ) :
    Tendsto (fun k => deriv (fun t => (∫ z, w (t,z) * g k z ∂μ) /
      ∫ z, w (t,z) ∂μ) x) atTop
      (𝓝 (deriv (fun t => (∫ z, w (t,z) * g₀ z ∂μ) / ∫ z, w (t,z) ∂μ) x)) := by
  let Z := fun t => ∫ z, w (t,z) ∂μ
  have hZ : HasDerivAt Z (deriv Z x) x :=
    ((CompactFibreC1.integral μ hw hs).1.differentiable (by norm_num) x).hasDerivAt
  have hformula (f : Y → ℝ) (hf : Continuous f) :
      deriv (fun t => (∫ z, w (t,z) * f z ∂μ) / Z t) x =
        ((∫ z, fderiv ℝ w (x,z) (1,0) * f z ∂μ) * Z x -
          (∫ z, w (x,z) * f z ∂μ) * deriv Z x) / (Z x)^2 :=
    (((integral μ hw hs hf).2 x).div hZ hx.ne').deriv
  change Tendsto (fun k => deriv (fun t => (∫ z, w (t,z) * g k z ∂μ) / Z t) x) atTop
    (𝓝 (deriv (fun t => (∫ z, w (t,z) * g₀ z ∂μ) / Z t) x))
  simp_rw [hformula _ (hg _), hformula g₀ hg₀]
  have hw' : Continuous (fun q => fderiv ℝ w q (1,0)) :=
    (hw.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hs' : HasCompactSupport (fun q => fderiv ℝ w q (1,0)) :=
    (hs.fderiv ℝ).comp_left
      (g := fun T : (ℝ × Y) →L[ℝ] ℝ => T (1,0)) (by simp)
  exact (((integral_tendsto μ hw' hs' hg hH hb hp x).mul_const (Z x)).sub
    ((integral_tendsto μ hw.continuous hs hg hH hb hp x).mul_const (deriv Z x))).div_const _

end Riesz2.CompactFibreContinuousFactor
