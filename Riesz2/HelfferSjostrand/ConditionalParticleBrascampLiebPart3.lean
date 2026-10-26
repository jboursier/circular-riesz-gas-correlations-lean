/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.ConditionalParticleBrascampLiebPart2
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Removing the rotation regularization

For Lemma 3.4, exponentially damp a probability by a nonnegative
penalty. The normalizers are strictly positive, the normalized laws admit
finite measure domination, and every integrable observable has convergent
expectations as the damping parameter decreases to zero. In particular the
observable need not be bounded: this applies to Sobolev functions, their
squares, and the tangent inverse energy.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology InnerProductSpace ContDiff ENNReal

namespace Riesz2.ConditionalParticleBrascampLieb

namespace Internal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
  {p : α → ℝ}

/-- The damping weights in Lemma 3.4 are integrable, even for
an unbounded nonnegative penalty. -/
theorem damping_integrable (hp : AEMeasurable p μ) (hp0 : ∀ᵐ x ∂μ, 0 ≤ p x)
    {ε : ℝ} (hε : 0 ≤ ε) : Integrable (fun x => Real.exp (-ε * p x)) μ := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    ((hp.const_mul (-ε)).exp.aestronglyMeasurable) ?_
  filter_upwards [hp0] with x hx
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hε) hx)

/-- Positive finite normalization and probability for the regularized laws
in Lemma 3.4. -/
theorem damping_probability (hp : AEMeasurable p μ) (hp0 : ∀ᵐ x ∂μ, 0 ≤ p x)
    {ε : ℝ} (hε : 0 ≤ ε) :
    0 < ∫ x, Real.exp (-ε * p x) ∂μ ∧
      (∫ x, Real.exp (-ε * p x) ∂μ) ≤ 1 ∧
      IsProbabilityMeasure (μ.tilted (fun x => -ε * p x)) := by
  have hi := damping_integrable hp hp0 hε
  refine ⟨integral_exp_pos hi, ?_, isProbabilityMeasure_tilted hi⟩
  calc
    _ ≤ ∫ _ : α, (1 : ℝ) ∂μ := integral_mono_ae hi (integrable_const _) (by
      filter_upwards [hp0] with x hx
      exact Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hε) hx))
    _ = 1 := by simp

omit [IsProbabilityMeasure μ] in
/-- Bounded normalized density change for Lemma 3.4. Its finite
constant suffices for transporting the entire completed H¹ approximation. -/
theorem damping_le_smul (hp0 : ∀ᵐ x ∂μ, 0 ≤ p x)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.tilted (fun x => -ε * p x) ≤
      ENNReal.ofReal ((∫ x, Real.exp (-ε * p x) ∂μ)⁻¹) • μ := by
  rw [Measure.tilted, ← withDensity_const]
  apply withDensity_mono
  filter_upwards [hp0] with x hx
  apply ENNReal.ofReal_le_ofReal
  rw [div_eq_mul_inv]
  exact mul_le_of_le_one_left (by positivity)
    (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hε) hx))

omit [IsProbabilityMeasure μ] in
/-- Dominated convergence of the unnormalized weighted moments in
Lemma 3.4, for an arbitrary integrable test. -/
theorem tendsto_damped_integral (hp : AEMeasurable p μ)
    (hp0 : ∀ᵐ x ∂μ, 0 ≤ p x) {f : α → ℝ} (hf : Integrable f μ) :
    Tendsto (fun ε : ℝ => ∫ x, Real.exp (-ε * p x) * f x ∂μ)
      (𝓝[≥] 0) (𝓝 (∫ x, f x ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖)
  · exact Eventually.of_forall fun ε =>
      ((hp.const_mul (-ε)).exp.aestronglyMeasurable).mul hf.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 ≤ ε)
    filter_upwards [hp0] with x hx
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hε) hx))
  · exact hf.norm
  · exact Eventually.of_forall fun x => by
      have hid : Tendsto (fun ε : ℝ => ε) (𝓝[≥] 0) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have ht := (Real.continuous_exp.tendsto (-(0 : ℝ) * p x)).comp
        (hid.neg.mul_const (p x))
      simpa using ht.mul_const (f x)

/-- The normalized density limit needed by Lemma 3.4, valid
for all integrable tests, including unbounded Sobolev observables. -/
theorem tendsto_damping_integral (hp : AEMeasurable p μ)
    (hp0 : ∀ᵐ x ∂μ, 0 ≤ p x) {f : α → ℝ} (hf : Integrable f μ) :
    Tendsto (fun ε : ℝ => ∫ x, f x ∂μ.tilted (fun y => -ε * p y))
      (𝓝[≥] 0) (𝓝 (∫ x, f x ∂μ)) := by
  have hZ := tendsto_damped_integral hp hp0 (integrable_const (1 : ℝ))
  simp only [mul_one, integral_const, probReal_univ, smul_eq_mul] at hZ
  have hq := (tendsto_damped_integral hp hp0 hf).div hZ one_ne_zero
  simp only [Riesz1.integral_tilted_eq_div]
  convert hq using 1
  simp

/-- The variance limit in Lemma 3.4 follows by passing the
first and second moments separately, with no boundedness assumption on `F`. -/
theorem tendsto_damping_variance (hp : AEMeasurable p μ)
    (hp0 : ∀ᵐ x ∂μ, 0 ≤ p x) {F : α → ℝ} (hF : MemLp F 2 μ) :
    Tendsto (fun ε : ℝ => ∫ x, (F x - ∫ y, F y ∂μ.tilted (fun z => -ε * p z)) ^ 2
      ∂μ.tilted (fun z => -ε * p z)) (𝓝[≥] 0)
      (𝓝 (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ)) := by
  have hlim := (tendsto_damping_integral hp hp0 hF.integrable_sq).sub
    ((tendsto_damping_integral hp hp0 (hF.integrable (by norm_num))).pow 2)
  rw [Riesz1.WeightedSobolev.integral_sub_mean_sq hF]
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 ≤ ε)
  have := (damping_probability hp hp0 hε).2.2
  have hFt : MemLp F 2 (μ.tilted (fun x => -ε * p x)) :=
    hF.of_measure_le_smul ENNReal.ofReal_ne_top (damping_le_smul hp0 hε)
  exact (Riesz1.WeightedSobolev.integral_sub_mean_sq hFt).symm

end Internal

end Riesz2.ConditionalParticleBrascampLieb
