/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.External.LogConcaveExponentialTails

/-!
# Convergence of log-concave densities

The representative and unweighted L¹ convergence are proved in
`LogConcaveDensityLimits`. Exponential envelopes and uniform weighted tails
are proved in `LogConcaveExponentialTails`. Truncation on balls gives convergence
with every smaller exponential weight.
-/

public section

noncomputable section

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology BoundedContinuousFunction

namespace Riesz2.WeightedLIntegral

/-- Unweighted convergence and uniformly small weighted tails imply weighted
convergence when the weight is bounded by a finite value on each truncation set.
Neither the measure nor the early weighted integrals need be finite. -/
theorem tendsto_zero_of_uniform_tails {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {U : ℕ → α → ℝ≥0∞} {W : α → ℝ≥0∞} {s : ι → Set α}
    (hs : ∀ R, MeasurableSet (s R))
    (hlocal : ∀ R, ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ x ∈ s R, W x ≤ C)
    (hzero : Tendsto (fun n => ∫⁻ x, U n x ∂μ) atTop (𝓝 0))
    (htail : ∃ N : ℕ, ∀ ε : ℝ≥0∞, 0 < ε → ∃ R : ι, ∀ n, N ≤ n →
      (∫⁻ x in (s R)ᶜ, W x * U n x ∂μ) < ε) :
    Tendsto (fun n => ∫⁻ x, W x * U n x ∂μ) atTop (𝓝 0) := by
  obtain ⟨N, htail⟩ := htail
  refine ENNReal.tendsto_nhds_zero.mpr fun ε hε => ?_
  have hhalf : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨R, hR⟩ := htail (ε / 2) hhalf
  obtain ⟨C, hC, hbound⟩ := hlocal R
  have hscaled : Tendsto (fun n => C * ∫⁻ x, U n x ∂μ) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hzero (Or.inr hC)
  filter_upwards [eventually_ge_atTop N,
    ENNReal.tendsto_nhds_zero.mp hscaled (ε / 2) hhalf] with n hn hsmall
  have hinside : (∫⁻ x in s R, W x * U n x ∂μ) ≤ C * ∫⁻ x, U n x ∂μ := by
    calc
      (∫⁻ x in s R, W x * U n x ∂μ) ≤ ∫⁻ x in s R, C * U n x ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (hs R)] with x hx
        exact mul_le_mul' (hbound x hx) le_rfl
      _ = C * ∫⁻ x in s R, U n x ∂μ := lintegral_const_mul' C _ hC
      _ ≤ C * ∫⁻ x, U n x ∂μ :=
        mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)
  calc
    (∫⁻ x, W x * U n x ∂μ) =
        (∫⁻ x in s R, W x * U n x ∂μ) +
          ∫⁻ x in (s R)ᶜ, W x * U n x ∂μ := (lintegral_add_compl _ (hs R)).symm
    _ ≤ ε / 2 + ε / 2 := add_le_add (hinside.trans hsmall) (hR n hn).le
    _ = ε := ENNReal.add_halves ε

end Riesz2.WeightedLIntegral

namespace Riesz2.ExternalLogConcave

/-- Convergence of log-concave densities, weighted L¹ clause:
every prescribed exponential envelope of the supplied limit density permits every
strictly smaller positive weight rate. -/
theorem logConcaveDensity_weighted_convergence (d : ℕ) (hd : 1 ≤ d)
    (F : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (hF : ∀ n, (Measurable (F n) ∧ (∀ x, 0 ≤ F n x) ∧
      (∫⁻ x, ENNReal.ofReal (F n x)) = 1) ∧
      ConcaveOn ℝ {x | 0 < F n x} (fun x => Real.log (F n x)))
    (hg : Measurable g ∧ (∀ x, 0 ≤ g x) ∧ (∫⁻ x, ENNReal.ofReal (g x)) = 1)
    (hweak : ∀ φ : EuclideanSpace ℝ (Fin d) →ᵇ ℝ,
      Tendsto (fun n => ∫ x, φ x ∂volume.withDensity (fun x => ENNReal.ofReal (F n x)))
        atTop (𝓝 (∫ x, φ x ∂volume.withDensity (fun x => ENNReal.ofReal (g x)))))
    (a₀ b₀ : ℝ) (ha₀ : 0 < a₀) (hgenv : ∀ x, g x ≤ Real.exp (-a₀ * ‖x‖ + b₀))
    (a : ℝ) (ha : 0 < a) (haa : a < a₀) :
    Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (Real.exp (a * ‖x‖) * |F n x - g x|))
      atTop (𝓝 0) := by
  obtain ⟨b, N, _, _, htail⟩ := logConcaveDensity_uniform_weighted_tails
    d hd F g hF hg hweak a₀ b₀ ha₀ hgenv a ha haa
  simp_rw [ENNReal.ofReal_mul (Real.exp_pos _).le] at htail ⊢
  apply WeightedLIntegral.tendsto_zero_of_uniform_tails
    (s := fun R : ℕ => closedBall (0 : EuclideanSpace ℝ (Fin d)) (R : ℝ))
    (fun _ => isClosed_closedBall.measurableSet) _
    (logConcaveDensity_limits d hd F g hF hg hweak).2 ⟨N, htail⟩
  intro R
  refine ⟨ENNReal.ofReal (Real.exp (a * (R : ℝ))), ENNReal.ofReal_ne_top, ?_⟩
  intro x hx
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (by simpa only [mem_closedBall, dist_zero_right] using hx) ha.le

/-- Convergence of log-concave densities, including exponential envelopes
and weighted L¹ convergence. -/
theorem logConcaveConvergence_result : Riesz2.External.LogConcaveConvergence := by
  intro d hd
  constructor
  · intro F g hF hg hweak
    obtain ⟨hrep, hL1⟩ := logConcaveDensity_limits d hd F g hF hg hweak
    refine ⟨hrep, hL1, ?_⟩
    intro a₀ b₀ ha₀ hgenv a ha haa
    exact logConcaveDensity_weighted_convergence d hd F g hF hg hweak
      a₀ b₀ ha₀ hgenv a ha haa
  · exact logConcaveDensity_exponential_envelope d hd

end Riesz2.ExternalLogConcave

end
