/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Preliminaries.FundamentalHeatContinuity
public import Riesz1.ToMathlib.CircleFourierL1Uniqueness
public import Riesz1.Kernel.FundamentalSolution
public import Riesz1.ToMathlib.HurwitzKernel.Regularity
public import Mathlib.MeasureTheory.Measure.OpenPos
import all Mathlib.Basic.Real.Basic
import all Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import all Riesz1.Kernel.FundamentalHeatIntegral

/-!
# The written heat-kernel route for the fundamental solution

Manuscript Lemma 2.3: first identify the heat integral by its Gamma/Fourier
coefficients and continuity, then insert the centered Gaussian images and apply
Fubini, evaluate the images, and pass to the renormalized symmetric sums.
The pointwise heat identity does not use an evaluated image series.
-/

public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace Riesz2

/-- Lemma 2.3, Fourier step: the heat time integral is spatially `L¹`.
This follows from product integrability of the centered heat kernel, proved
using its spatial `L¹` bound at small times and exponential decay at large times. -/
theorem fundamentalHeat_integrable (s : Riesz1.RieszExponent) :
    Integrable (Riesz1.heatIntegral s) := by
  have hp : Integrable (fun p : UnitAddCircle × ℝ =>
      (HurwitzZeta.cosKernel p.1 (4 * π * p.2) - 1) * p.2 ^ (-(1 + s.val) / 2))
      (AddCircle.haarAddCircle.prod (volume.restrict (Ioi 0))) := by
    simpa [fourier_zero] using (Riesz1.integrable_fourier_heatIntegrand s 0).re
  have hh := hp.integral_prod_left.const_mul
    (Riesz1.rieszConstant s / Real.Gamma ((1 - s.val) / 2))
  have hm : (AddCircle.haarAddCircle : Measure UnitAddCircle) = volume := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ))).symm
  unfold Riesz1.heatIntegral
  rw [← hm]
  exact hh

/-- Lemma 2.3, Fourier step: the Gamma computation of every Fourier
coefficient identifies the heat integral with the mean-zero solution in `L¹`.
No pointwise evaluation of centered images is used in this argument. -/
theorem fundamentalHeat_ae_eq (s : Riesz1.RieszExponent) :
    Riesz1.heatIntegral s =ᵐ[volume] Riesz1.rieszRepresentative s := by
  have hH := fundamentalHeat_integrable s
  have hG := Riesz1.integrable_rieszRepresentative s
  have hm : (AddCircle.haarAddCircle : Measure UnitAddCircle) = volume := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ))).symm
  have hzero := Riesz1.CircleFourier.ae_eq_zero_of_integrable_fourierCoeff_eq_zero
    (hH.sub hG) (fun k => by
      have hH' := (show Integrable (fun x => (Riesz1.heatIntegral s x : ℂ))
          AddCircle.haarAddCircle by rw [hm]; exact hH.ofReal).fourier_smul (-k)
      have hG' := (show Integrable (fun x => (Riesz1.rieszRepresentative s x : ℂ))
          AddCircle.haarAddCircle by rw [hm]; exact hG.ofReal).fourier_smul (-k)
      simp only [fourierCoeff, Pi.sub_apply, Complex.ofReal_sub, smul_sub]
      rw [integral_sub hH' hG']
      change fourierCoeff (fun x => (Riesz1.heatIntegral s x : ℂ)) k -
        fourierCoeff (fun x => (Riesz1.rieszRepresentative s x : ℂ)) k = 0
      rw [Riesz1.fourierCoeff_heatIntegral, Riesz1.fourierCoeff_rieszRepresentative, sub_self])
  filter_upwards [hzero] with x hx
  exact sub_eq_zero.mp hx

/-- Lemma 2.3, before Fubini on the images: the fundamental solution is
the heat integral. Gamma evaluation gives the Fourier coefficients, Fourier
uniqueness gives equality almost everywhere, and independent local dominated
continuity upgrades this equality at every `0 < x < 1`. -/
theorem fundamentalSolution_heat_representation (s : Riesz1.RieszExponent)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Riesz1.rieszRepresentative s (x : UnitAddCircle) =
      Riesz1.rieszConstant s / Real.Gamma ((1 - s.val) / 2) *
        ∫ t in Ioi (0 : ℝ),
          (HurwitzZeta.cosKernel (x : UnitAddCircle) (4 * π * t) - 1) *
            t ^ (-(1 + s.val) / 2) := by
  have hae := (AddCircle.measurePreserving_mk (1 : ℝ) 0).quasiMeasurePreserving.ae_eq_comp
    (fundamentalHeat_ae_eq s)
  have hae' : (fun y : ℝ => Riesz1.heatIntegral s (y : UnitAddCircle)) =ᵐ[
      volume.restrict (Ioo 0 1)] (fun y : ℝ => Riesz1.rieszRepresentative s y) := by
    have h : (fun y : ℝ => Riesz1.heatIntegral s (y : UnitAddCircle)) =ᵐ[
        volume.restrict (Ioc (0 : ℝ) 1)] (fun y : ℝ => Riesz1.rieszRepresentative s y) := by
      simpa only [zero_add, Function.comp_def] using hae
    exact ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioc_self h
  have hG : ContinuousOn (fun y : ℝ => Riesz1.rieszRepresentative s y) (Ioo 0 1) := by
    have h := (Riesz1.contDiffOn_hurwitzZetaEven_re s.val s.2.1 s.2.2).continuousOn.const_mul 2
    exact h.mono (fun y hy => Riesz1.coe_ne_zero_of_mem_Ioo hy.1 hy.2)
  exact (Measure.eqOn_open_of_ae_eq hae' isOpen_Ioo
    (fundamentalHeat_continuousOn s) hG ⟨hx0, hx1⟩).symm

/-- Lemma 2.3, centered images and Fubini: after the Fourier identification
of the heat integral, evaluate each centered image by the reciprocal-time Gamma
integral. The normalization factor is one, and the centered images sum to `g_s`. -/
theorem fundamentalSolution_centered_images (s : Riesz1.RieszExponent)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    HasSum (fun k : ℤ => |x - (k : ℝ)| ^ (-s.val) -
      ∫ y in (0 : ℝ)..1, |y - (k : ℝ)| ^ (-s.val))
      (Riesz1.rieszRepresentative s x) := by
  have hheat := fundamentalSolution_heat_representation s hx0 hx1
  have hseries : Riesz1.rieszRepresentative s (x : UnitAddCircle) =
      Riesz1.rieszConstant s / Real.Gamma ((1 - s.val) / 2) *
        ∫ t in Ioi (0 : ℝ),
          (∑' k : ℤ, Real.exp (-4 * π ^ 2 * (k : ℝ) ^ 2 * t) *
            Real.cos (2 * π * k * x) - 1) * t ^ (-(1 + s.val) / 2) := by
    rw [hheat]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : 0 < t := ht
    rw [Riesz1.cosKernel_four_pi_eq_circleHeatKernel ht0 x,
      Riesz1.circleHeatKernel_eq_series]
  have hfubini : Riesz1.rieszRepresentative s (x : UnitAddCircle) =
      Riesz1.rieszConstant s / (Real.Gamma ((1 - s.val) / 2) * Real.sqrt (4 * π)) *
        ∑' k : ℤ, ∫ t in Ioi (0 : ℝ), Riesz1.interchangeTerm s.val x k t := by
    rw [hseries, Riesz1.integral_heat_eq_interchange s.2.1 s.2.2 hx0 hx1]
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
    ring
  have habs := Riesz1.summable_integral_abs_interchangeTerm s.2.1 s.2.2 hx0 hx1
  have hsum : Summable (fun k : ℤ =>
      ∫ t in Ioi (0 : ℝ), Riesz1.interchangeTerm s.val x k t) :=
    Summable.of_norm_bounded habs (fun k => by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun t => Riesz1.interchangeTerm s.val x k t))
  have h := hsum.hasSum.mul_left
    (Riesz1.rieszConstant s / (Real.Gamma ((1 - s.val) / 2) * Real.sqrt (4 * π)))
  rw [← hfubini] at h
  refine h.congr_fun (fun k => ?_)
  rw [Riesz1.integral_interchangeTerm_riesz s.2.1 s.2.2 hx0 hx1,
    ← mul_assoc, Riesz1.riesz_constant_mul_eq_one, one_mul]

/-- Lemma 2.3, equation (2.3): the centered images give the
renormalized symmetric limit. The exact finite centering differs from
`2 M^(1-s)/(1-s)` by a term tending to zero. -/
theorem fundamentalSolution_heat_finitePart (s : Riesz1.RieszExponent)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto (fun M : ℕ =>
      (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |(k : ℝ) + x| ^ (-s.val)) -
        2 * (M : ℝ) ^ (1 - s.val) / (1 - s.val)) atTop
      (𝓝 (Riesz1.rieszRepresentative s x)) := by
  have hmono : Monotone (fun M : ℕ => Finset.Icc (-(M : ℤ)) (M : ℤ)) :=
    fun _ _ h => Finset.Icc_subset_Icc (by omega) (by omega)
  have hexh : ∀ k : ℤ, ∃ M : ℕ, k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) :=
    fun k => ⟨k.natAbs, by rw [Finset.mem_Icc]; omega⟩
  have hc := (fundamentalSolution_centered_images s hx0 hx1).comp
    (tendsto_atTop_finset_of_monotone hmono hexh)
  have he := (Riesz1.tendsto_rpow_succ_sub s.2.1 s.2.2).div_const (1 - s.val)
  have h := hc.add he
  simpa only [Function.comp_def, Riesz1.sum_centered_eq s.2.2,
    sub_add_cancel, zero_div, add_zero] using h

end Riesz2

end
