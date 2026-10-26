/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.ConvergesInLawAlong
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Weak convergence under a vanishing error

A quantitative perturbation criterion allowing both the probability spaces and
the measures to vary. Bounded Lipschitz tests control the exceptional event.
-/

public section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BoundedContinuousFunction

namespace Riesz2

/-- Weak convergence survives an error bounded by a vanishing threshold outside
an event of vanishing probability, on arbitrary varying probability spaces. -/
theorem convergesInLawAlong_of_error_bound
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {l : Filter ι} [l.IsCountablyGenerated]
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (X Y : ∀ i, Ω i → ℝ) (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    (ν : Measure ℝ) (hweak : ConvergesInLawAlong l (fun i => (μ i).map (X i)) ν)
    (r b : ι → ℝ) (hr : Tendsto r l (𝓝 0)) (hb : Tendsto b l (𝓝 0))
    (herror : ∀ᶠ i in l, 0 ≤ r i ∧ 0 ≤ b i ∧
      μ i {ω | r i < |Y i ω - X i ω|} ≤ ENNReal.ofReal (b i)) :
    ConvergesInLawAlong l (fun i => (μ i).map (Y i)) ν := by
  have weakPerturbationLimitProbability : IsProbabilityMeasure ν := hweak.2.1
  let μY : ι → ProbabilityMeasure ℝ := fun i => ⟨(μ i).map (Y i), by infer_instance⟩
  let μX : ι → ProbabilityMeasure ℝ := fun i => ⟨(μ i).map (X i), hweak.1 i⟩
  let v : ProbabilityMeasure ℝ := ⟨ν, hweak.2.1⟩
  have htX : Tendsto μX l (𝓝 v) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr hweak.2.2
  have htY : Tendsto μY l (𝓝 v) := by
    apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
    intro f hf ⟨L, hL⟩
    let g : ℝ →ᵇ ℝ := ⟨⟨f, hL.continuous⟩, hf⟩
    have hfg (x : ℝ) : |f x| ≤ ‖g‖ := g.norm_coe_le_norm x
    have hi (i : ι) (Z : Ω i → ℝ) (hZ : Measurable Z) : Integrable (fun ω => f (Z ω)) (μ i) :=
      Integrable.of_bound (hL.continuous.measurable.comp hZ).aestronglyMeasurable ‖g‖
        (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hfg (Z ω))
    have hdiff : Tendsto (fun i =>
        (∫ ω, f (Y i ω) ∂μ i) - ∫ ω, f (X i ω) ∂μ i) l (𝓝 0) := by
      have hrate := (hr.const_mul (L : ℝ)).add (hb.const_mul (2 * ‖g‖))
      simp only [mul_zero, add_zero] at hrate
      apply squeeze_zero_norm' ?_ hrate
      filter_upwards [herror] with i he
      let E : Set (Ω i) := {ω | r i < |Y i ω - X i ω|}
      have hE : MeasurableSet E := measurableSet_lt measurable_const (continuous_abs.measurable.comp ((hY i).sub (hX i)))
      have hreal : (μ i).real E ≤ b i := ENNReal.toReal_le_of_le_ofReal he.2.1 he.2.2
      have hpoint (ω : Ω i) : |f (Y i ω) - f (X i ω)| ≤
          (L : ℝ) * r i + E.indicator (fun _ => 2 * ‖g‖) ω := by
        by_cases hω : ω ∈ E
        · rw [indicator_of_mem hω]
          have hh := (abs_sub (f (Y i ω)) (f (X i ω))).trans
            (add_le_add (hfg _) (hfg _))
          linarith only [hh, mul_nonneg L.coe_nonneg he.1]
        · rw [indicator_of_notMem hω, add_zero]
          have hh : |Y i ω - X i ω| ≤ r i := le_of_not_gt hω
          simpa only [Real.norm_eq_abs] using hL.norm_sub_le_of_le hh
      rw [← integral_sub (hi i _ (hY i)) (hi i _ (hX i)), Real.norm_eq_abs]
      calc
        _ ≤ ∫ ω, |f (Y i ω) - f (X i ω)| ∂μ i := abs_integral_le_integral_abs
        _ ≤ ∫ ω, ((L : ℝ) * r i + E.indicator (fun _ => 2 * ‖g‖) ω) ∂μ i :=
          integral_mono ((hi i _ (hY i)).sub (hi i _ (hX i))).abs
            ((integrable_const _).add ((integrable_const _).indicator hE)) hpoint
        _ = (L : ℝ) * r i + 2 * ‖g‖ * (μ i).real E := by
          rw [integral_add (integrable_const _) ((integrable_const _).indicator hE),
            integral_const, integral_indicator_const _ hE]
          simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul]
          ring
        _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hreal (show (0 : ℝ) ≤ 2 * ‖g‖ from mul_nonneg (by norm_num) (norm_nonneg g)))
    have ht := hdiff.add (tendsto_iff_forall_lipschitz_integral_tendsto.mp htX f hf ⟨L, hL⟩)
    simp only [zero_add] at ht
    change Tendsto (fun i => ∫ ω, f ω ∂(μ i).map (Y i)) l (𝓝 (∫ ω, f ω ∂ν))
    change Tendsto (fun i => (∫ ω, f (Y i ω) ∂μ i) - (∫ ω, f (X i ω) ∂μ i) +
      ∫ ω, f ω ∂(μ i).map (X i)) l (𝓝 (∫ ω, f ω ∂ν)) at ht
    simpa only [integral_map (hX _).aemeasurable hL.continuous.aestronglyMeasurable,
      integral_map (hY _).aemeasurable hL.continuous.aestronglyMeasurable,
      sub_add_cancel] using ht
  exact ⟨fun i => by dsimp only; infer_instance, hweak.2.1,
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp htY⟩

end Riesz2
