/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.External.PeriodicZeta
public import Riesz2.Frozen.External.ThermodynamicLogConcavity
public import Riesz2.Frozen.External.LogConcaveConvergence
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Tactic

/-!
# Checks for log-concave densities and periodic zeta

Concrete Gaussian and uniform densities check that the hypotheses have instances.
Constant sequences check both integral convergence conclusions without external input.
The zeta specialization checks the open parameter ranges and the coefficient at a half.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2.Sanity.External

theorem periodicZeta_half_domain :
    (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1 := by norm_num

theorem periodicZeta_first_term_half :
    (1 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.cos (2 * Real.pi * 1 * (1 / 2)) = -1 := by
  rw [show 2 * Real.pi * 1 * (1 / 2) = Real.pi by ring]
  simp

theorem periodicZeta_half (h : Riesz2.External.PeriodicZeta) :
    ∃ L : ℝ,
      Tendsto (fun M : ℕ => ∑ n ∈ Finset.range M,
        ((n + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) *
          Real.cos (2 * Real.pi * (n + 1) * (1 / 2))) atTop (𝓝 L) ∧
      2 * (HurwitzZeta.hurwitzZeta ((1 / 2 : ℝ) : UnitAddCircle)
        ((1 / 2 : ℝ) : ℂ)).re =
        (4 * Real.Gamma (1 / 2) * Real.cos (Real.pi * (1 / 2) / 2) /
          (2 * Real.pi) ^ (1 / 2 : ℝ)) * L := by
  simpa only [show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num, two_mul] using
    h (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem gaussian_logConcave :
    ConcaveOn ℝ {x | 0 < gaussianPDFReal 0 1 x}
      (fun x => Real.log (gaussianPDFReal 0 1 x)) := by
  have hs : {x | 0 < gaussianPDFReal 0 1 x} = (univ : Set ℝ) := by
    ext x
    simp [gaussianPDFReal_pos 0 1 x one_ne_zero]
  rw [hs]
  have hq : ConcaveOn ℝ univ (fun x : ℝ => -(x ^ 2)) := even_two.convexOn_pow.neg
  have hc := (hq.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)).add_const
    (Real.log (Real.sqrt (2 * Real.pi))⁻¹)
  apply hc.congr
  intro x _
  simp only [Pi.add_apply, smul_eq_mul, gaussianPDFReal,
    NNReal.coe_one, mul_one, sub_zero]
  rw [Real.log_mul (inv_ne_zero (Real.sqrt_ne_zero'.mpr (by positivity)))
    (Real.exp_ne_zero _), Real.log_exp]
  ring

theorem gaussian_density_hypotheses :
    Measurable (gaussianPDFReal 0 1) ∧
    (∀ x, 0 ≤ gaussianPDFReal 0 1 x) ∧
    ConcaveOn ℝ {x | 0 < gaussianPDFReal 0 1 x}
      (fun x => Real.log (gaussianPDFReal 0 1 x)) ∧
    (∫⁻ x, ENNReal.ofReal (gaussianPDFReal 0 1 x)) = 1 :=
  ⟨measurable_gaussianPDFReal 0 1, gaussianPDFReal_nonneg 0 1,
    gaussian_logConcave, lintegral_gaussianPDFReal_eq_one 0 one_ne_zero⟩

theorem gaussian_moment_hypotheses :
    let μ := volume.withDensity (fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x))
    Integrable (fun x : ℝ => x) μ ∧ (∫ x, x ∂μ) = 0 ∧
      (0 : ℝ) < 1 ∧ (∫⁻ x, ENNReal.ofReal ((x - 0) ^ 2) ∂μ) = ENNReal.ofReal 1 := by
  dsimp only
  have hμ : volume.withDensity (fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x)) =
      gaussianReal 0 1 := (gaussianReal_of_var_ne_zero 0 one_ne_zero).symm
  rw [hμ]
  refine ⟨(memLp_id_gaussianReal 1).integrable (by norm_num),
    integral_id_gaussianReal, zero_lt_one, ?_⟩
  have h := (memLp_id_gaussianReal (μ := 0) (v := 1) 2).ofReal_variance_eq
  rw [variance_id_gaussianReal] at h
  simpa only [evariance_eq_lintegral_ofReal, id_eq, integral_id_gaussianReal,
    NNReal.coe_one] using h.symm

theorem gaussian_constant_poincare :
    (∫⁻ x, ENNReal.ofReal (((fun _ : ℝ => (3 : ℝ)) x -
        ∫ _y, (3 : ℝ) ∂gaussianReal 0 1) ^ 2) ∂gaussianReal 0 1) ≤
      ENNReal.ofReal (12 * (1 : ℝ)) *
        ∫⁻ x, ENNReal.ofReal ((deriv (fun _ : ℝ => (3 : ℝ)) x) ^ 2)
          ∂gaussianReal 0 1 := by
  simp

/-- Uniform probability density on a Euclidean unit ball. Its volume is positive and finite,
so the real reciprocal in this definition is the ordinary normalization. -/
def unitBallDensity (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).indicator
    (fun _ => (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal⁻¹) x

theorem unitBall_volume_pos_finite (d : ℕ) :
    0 < volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) ∧
    volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) < ∞ :=
  ⟨Metric.measure_closedBall_pos volume 0 zero_lt_one, measure_closedBall_lt_top⟩

theorem unitBall_density_hypotheses (d : ℕ) :
    Measurable (unitBallDensity d) ∧ (∀ x, 0 ≤ unitBallDensity d x) ∧
    (∫⁻ x, ENNReal.ofReal (unitBallDensity d x)) = 1 ∧
    ConcaveOn ℝ {x | 0 < unitBallDensity d x}
      (fun x => Real.log (unitBallDensity d x)) := by
  let B := Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1
  have hB : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  have hv := unitBall_volume_pos_finite d
  have hc : 0 < (volume B).toReal⁻¹ :=
    inv_pos.mpr (ENNReal.toReal_pos hv.1.ne' hv.2.ne)
  have hpos : {x | 0 < unitBallDensity d x} = B := by
    ext x
    by_cases hx : x ∈ B <;> simp [unitBallDensity, B, hx, hc]
  refine ⟨measurable_const.indicator hB, fun x => ?_, ?_, ?_⟩
  · exact indicator_nonneg (fun _ _ => hc.le) x
  · have heq : (fun x => ENNReal.ofReal (unitBallDensity d x)) =
        B.indicator (fun _ => (volume B)⁻¹) := by
      ext x
      by_cases hx : x ∈ B
      · change ENNReal.ofReal (B.indicator (fun _ => (volume B).toReal⁻¹) x) =
          B.indicator (fun _ => (volume B)⁻¹) x
        rw [indicator_of_mem hx, indicator_of_mem hx,
          ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hv.1.ne' hv.2.ne),
          ENNReal.ofReal_toReal hv.2.ne]
      · simp [unitBallDensity, B, hx]
    rw [heq, lintegral_indicator hB]
    simpa only [lintegral_const, Measure.restrict_apply_univ] using
      ENNReal.inv_mul_cancel hv.1.ne' hv.2.ne
  · rw [hpos]
    apply (concaveOn_const (Real.log (volume B).toReal⁻¹)
      (convex_closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)).congr
    intro x hx
    simp [unitBallDensity, B, hx]

theorem unitBall_exponential_envelope (d : ℕ) :
    ∃ a : ℝ, 0 < a ∧ ∃ b : ℝ,
      ∀ x, unitBallDensity d x ≤ Real.exp (-a * ‖x‖ + b) := by
  let B := Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1
  have hv := unitBall_volume_pos_finite d
  have hc : 0 < (volume B).toReal⁻¹ :=
    inv_pos.mpr (ENNReal.toReal_pos hv.1.ne' hv.2.ne)
  refine ⟨1, zero_lt_one, 1 + Real.log (volume B).toReal⁻¹, fun x => ?_⟩
  by_cases hx : x ∈ B
  · change B.indicator (fun _ => (volume B).toReal⁻¹) x ≤ _
    rw [indicator_of_mem hx]
    have hn : ‖x‖ ≤ 1 := by simpa [B, Metric.mem_closedBall, dist_zero_right] using hx
    calc
      _ = Real.exp (Real.log (volume B).toReal⁻¹) := (Real.exp_log hc).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · have hz : unitBallDensity d x = 0 := indicator_of_notMem hx _
    rw [hz]
    exact (Real.exp_pos _).le

theorem constant_sequence_weak (d : ℕ) (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (φ : EuclideanSpace ℝ (Fin d) →ᵇ ℝ) :
    Tendsto (fun _ : ℕ => ∫ x, φ x ∂volume.withDensity (fun x => ENNReal.ofReal (g x)))
      atTop (𝓝 (∫ x, φ x ∂volume.withDensity (fun x => ENNReal.ofReal (g x)))) :=
  tendsto_const_nhds

theorem constant_sequence_integrals (d : ℕ) (g : EuclideanSpace ℝ (Fin d) → ℝ) :
    Tendsto (fun _ : ℕ => ∫⁻ x, ENNReal.ofReal |g x - g x|) atTop (𝓝 0) ∧
    (∀ a : ℝ, Tendsto (fun _ : ℕ =>
      ∫⁻ x, ENNReal.ofReal (Real.exp (a * ‖x‖) * |g x - g x|)) atTop (𝓝 0)) := by
  simp

theorem logConcaveConvergence_unitBall (h : Riesz2.External.LogConcaveConvergence) :
    ∃ g' : EuclideanSpace ℝ (Fin 1) → ℝ,
      Measurable g' ∧ (∀ x, 0 ≤ g' x) ∧
      (∫⁻ x, ENNReal.ofReal (g' x)) = 1 ∧
      ConcaveOn ℝ {x | 0 < g' x} (fun x => Real.log (g' x)) ∧
      g' =ᵐ[volume] unitBallDensity 1 := by
  have hd := unitBall_density_hypotheses 1
  have hr := (h 1 le_rfl).1 (fun _ => unitBallDensity 1) (unitBallDensity 1)
    (fun _ => ⟨⟨hd.1, hd.2.1, hd.2.2.1⟩, hd.2.2.2⟩)
    ⟨hd.1, hd.2.1, hd.2.2.1⟩ (constant_sequence_weak 1 (unitBallDensity 1))
  rcases hr.1 with ⟨g', ⟨hg', hn, hm⟩, hl, he⟩
  exact ⟨g', hg', hn, hm, hl, he⟩

end Riesz2.Sanity.External

end
end
