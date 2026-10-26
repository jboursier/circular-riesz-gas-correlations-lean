/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Tactic

/-!
# Weak convergence tested against unbounded observables

Clipping a continuous observable gives bounded continuous tests. A uniform
second moment of that observable controls the clipping error. These are
internal analytic helpers for the proof of Theorem 1. Applications must
prove their moment bounds from the actual densities.
-/

public section

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction

namespace Riesz2.WeakMomentTruncation

/-- Clipping a real number at a positive threshold has a quadratic error
bound, with no restriction on the sign of the number. -/
theorem abs_sub_clip_le_sq_div (x : ℝ) {T : ℝ} (hT : 0 < T) :
    |x - max (-T) (min T x)| ≤ x ^ 2 / T := by
  apply (le_div_iff₀ hT).mpr
  by_cases hx : x ≤ -T
  · rw [min_eq_right (by linarith : x ≤ T), max_eq_left hx,
      abs_of_nonpos (by linarith : x - -T ≤ 0)]
    nlinarith [sq_nonneg (x + T)]
  by_cases hxT : T ≤ x
  · rw [min_eq_left hxT, max_eq_right (by linarith : -T ≤ T),
      abs_of_nonneg (by linarith : 0 ≤ x - T)]
    nlinarith [sq_nonneg (x - T)]
  · rw [min_eq_right (le_of_not_ge hxT), max_eq_right (le_of_not_ge hx),
      sub_self, abs_zero, zero_mul]
    exact sq_nonneg x

/-- Internal clipping helper at the generality of bounded continuous
tests on a topological probability space. The conclusion uses integrable functions. -/
theorem exists_clipped_test_internal {E : Type*} [TopologicalSpace E]
    {g : E → ℝ} (hg : Continuous g) {T : ℝ} (hT : 0 < T) :
    ∃ f : E →ᵇ ℝ, (∀ x, |g x - f x| ≤ (g x) ^ 2 / T) ∧
      ∀ [MeasurableSpace E] [OpensMeasurableSpace E] (μ : Measure E)
        [IsFiniteMeasure μ], MemLp g 2 μ →
        |(∫ x, g x ∂μ) - ∫ x, f x ∂μ| ≤ (∫ x, (g x) ^ 2 ∂μ) / T := by
  let f : E →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfBound
      ⟨fun x => max (-T) (min T (g x)), by fun_prop⟩ (2 * T) (by
        intro x y
        change dist (max (-T) (min T (g x))) (max (-T) (min T (g y))) ≤ 2 * T
        rw [Real.dist_eq, abs_le]
        have hlow (z : E) : -T ≤ max (-T) (min T (g z)) := le_max_left _ _
        have hupp (z : E) : max (-T) (min T (g z)) ≤ T :=
          max_le (by linarith) (min_le_left _ _)
        constructor <;> linarith [hlow x, hlow y, hupp x, hupp y])
  have hpoint : ∀ x, |g x - f x| ≤ (g x) ^ 2 / T :=
    fun x => abs_sub_clip_le_sq_div (g x) hT
  refine ⟨f, hpoint, ?_⟩
  intro _ _ μ _ hmem
  have hgint := hmem.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hfint := f.integrable μ
  rw [← integral_sub hgint hfint]
  calc |∫ x, g x - f x ∂μ| ≤ ∫ x, |g x - f x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, (g x) ^ 2 / T ∂μ :=
      integral_mono (hgint.sub hfint).abs (hmem.integrable_sq.div_const T) hpoint
    _ = _ := integral_div T _

/-- Internal moment-transfer theorem. Weak convergence together with a
uniform second moment of a continuous observable implies convergence of
its first moment. Apply this to `x` and `x²`
after establishing a uniform fourth moment from the log-concave tails. -/
theorem integral_tendsto_of_uniform_second_moment_internal
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {ι : Type*} {l : Filter ι} {μ : ι → Measure E} {ν : Measure E}
    [∀ i, IsProbabilityMeasure (μ i)] [IsProbabilityMeasure ν]
    (hweak : ∀ f : E →ᵇ ℝ,
      Tendsto (fun i => ∫ x, f x ∂μ i) l (𝓝 (∫ x, f x ∂ν)))
    {g : E → ℝ} (hg : Continuous g) (hmem : ∀ i, MemLp g 2 (μ i))
    (hν : MemLp g 2 ν) {C : ℝ}
    (hC : ∀ᶠ i in l, (∫ x, (g x) ^ 2 ∂μ i) ≤ C) :
    Tendsto (fun i => ∫ x, g x ∂μ i) l (𝓝 (∫ x, g x ∂ν)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let B := max 1 (max C (∫ x, (g x) ^ 2 ∂ν))
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let T := 6 * B / ε
  have hT : 0 < T := by dsimp [T]; positivity
  have hBT : B / T = ε / 6 := by dsimp [T]; field_simp
  obtain ⟨f, -, hf⟩ := exists_clipped_test_internal hg hT
  have hνbound := hf ν hν
  have hνsmall : |(∫ x, g x ∂ν) - ∫ x, f x ∂ν| ≤ ε / 6 := by
    calc _ ≤ (∫ x, (g x) ^ 2 ∂ν) / T := hνbound
      _ ≤ B / T := div_le_div_of_nonneg_right
        ((le_max_right C _).trans (le_max_right 1 _)) hT.le
      _ = ε / 6 := hBT
  filter_upwards [hC, (Metric.tendsto_nhds.mp (hweak f)) (ε / 3) (by positivity)] with i hi hif
  have hμsmall : |(∫ x, g x ∂μ i) - ∫ x, f x ∂μ i| ≤ ε / 6 := by
    calc _ ≤ (∫ x, (g x) ^ 2 ∂μ i) / T := hf (μ i) (hmem i)
      _ ≤ B / T := div_le_div_of_nonneg_right
        (hi.trans ((le_max_left _ _).trans (le_max_right _ _))) hT.le
      _ = ε / 6 := hBT
  rw [Real.dist_eq] at hif ⊢
  have htri : |(∫ x, g x ∂μ i) - ∫ x, g x ∂ν| ≤
      |(∫ x, g x ∂μ i) - ∫ x, f x ∂μ i| +
      |(∫ x, f x ∂μ i) - ∫ x, f x ∂ν| +
      |(∫ x, g x ∂ν) - ∫ x, f x ∂ν| := by
    simpa only [Real.dist_eq, dist_comm (∫ x, f x ∂ν) (∫ x, g x ∂ν)] using
      dist_triangle4 (∫ x, g x ∂μ i) (∫ x, f x ∂μ i)
        (∫ x, f x ∂ν) (∫ x, g x ∂ν)
  linarith

/-- Internal first- and second-moment transfer from an eventual uniform
fourth moment. All measures are probabilities and every displayed
moment is integrable. This isolates precisely the moment estimate to be
proved from log-concavity. -/
theorem first_second_moments_tendsto_of_uniform_fourth_internal
    {ι : Type*} {l : Filter ι} {μ : ι → Measure ℝ} {ν : Measure ℝ}
    [∀ i, IsProbabilityMeasure (μ i)] [IsProbabilityMeasure ν]
    (hweak : ∀ f : ℝ →ᵇ ℝ,
      Tendsto (fun i => ∫ x, f x ∂μ i) l (𝓝 (∫ x, f x ∂ν)))
    (hfourth : ∀ i, MemLp (fun x : ℝ => x ^ 2) 2 (μ i))
    (hνfourth : MemLp (fun x : ℝ => x ^ 2) 2 ν) {C : ℝ}
    (hC : ∀ᶠ i in l, (∫ x : ℝ, (x ^ 2) ^ 2 ∂μ i) ≤ C) :
    Tendsto (fun i => ∫ x : ℝ, x ∂μ i) l (𝓝 (∫ x : ℝ, x ∂ν)) ∧
      Tendsto (fun i => ∫ x : ℝ, x ^ 2 ∂μ i) l (𝓝 (∫ x : ℝ, x ^ 2 ∂ν)) := by
  have hsecond : ∀ i, MemLp (fun x : ℝ => x) 2 (μ i) := by
    intro i
    exact (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr
      ((hfourth i).integrable (by norm_num))
  have hνsecond : MemLp (fun x : ℝ => x) 2 ν :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mpr
      (hνfourth.integrable (by norm_num))
  have hsecondbound : ∀ᶠ i in l, (∫ x : ℝ, x ^ 2 ∂μ i) ≤ 1 + C := by
    filter_upwards [hC] with i hi
    have hb := integral_mono (hsecond i).integrable_sq
      ((integrable_const (1 : ℝ)).add (hfourth i).integrable_sq)
      (fun x : ℝ => show x ^ 2 ≤ 1 + (x ^ 2) ^ 2 by nlinarith [sq_nonneg (x ^ 2 - 1)])
    simp only [Pi.add_apply] at hb
    rw [integral_add (integrable_const (1 : ℝ)) (hfourth i).integrable_sq,
      integral_const, probReal_univ, smul_eq_mul, one_mul] at hb
    linarith
  exact ⟨integral_tendsto_of_uniform_second_moment_internal hweak continuous_id
      hsecond hνsecond hsecondbound,
    integral_tendsto_of_uniform_second_moment_internal hweak (continuous_id.pow 2)
      hfourth hνfourth hC⟩

end Riesz2.WeakMomentTruncation

end
