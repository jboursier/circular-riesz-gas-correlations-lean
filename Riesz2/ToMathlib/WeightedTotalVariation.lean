/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.TotalVariationMomentTransfer

/-!
# Weighted tests from total variation and second moments

The truncation step in Theorem 3 (Palm inversion) and
Corollary 1.1 in the manuscript. Clip the weight first, use ordinary
total variation for all bounded multipliers at once, then remove the tails.
-/

public section
noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Riesz2

/-- The Theorem 3 Palm-inversion truncation: the bounded part
costs `2 T TV`, and each law contributes its clipping tail. -/
theorem abs_weighted_integral_sub_le_totalVariation_tails_internal
    {E : Type*} [MeasurableSpace E] (μ ν : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {w F : E → ℝ} (hw : Measurable w) (hμ : Integrable w μ) (hν : Integrable w ν)
    (hF : Measurable F) (hb : ∀ x, |F x| ≤ 1) {T : ℝ} (hT : 0 < T) :
    |(∫ x, w x * F x ∂μ) - ∫ x, w x * F x ∂ν| ≤
      2 * T * (totalVariation μ ν).toReal +
        (∫ x, |w x - max (-T) (min T (w x))| ∂μ) +
        (∫ x, |w x - max (-T) (min T (w x))| ∂ν) := by
  let c := fun x => max (-T) (min T (w x))
  have hc : Measurable c := by dsimp [c]; fun_prop
  have hcb (x) : |c x| ≤ T := abs_le.mpr
    ⟨by dsimp [c]; linarith [le_max_left (-T) (min T (w x))],
      max_le (by linarith) (min_le_left _ _)⟩
  have hci (ρ : Measure E) [IsProbabilityMeasure ρ] : Integrable c ρ :=
    Integrable.of_bound hc.aestronglyMeasurable T
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hcb x)
  have hmul {ρ : Measure E} {g : E → ℝ} (hg : Integrable g ρ) :
      Integrable (fun x => g x * F x) ρ :=
    hg.mul_bdd hF.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb x)
  have herr (ρ : Measure E) [IsProbabilityMeasure ρ] (hi : Integrable w ρ) :
      |(∫ x, w x * F x ∂ρ) - ∫ x, c x * F x ∂ρ| ≤ ∫ x, |w x - c x| ∂ρ := by
    rw [← integral_sub (hmul hi) (hmul (hci ρ))]
    apply abs_integral_le_integral_abs.trans
    apply integral_mono (hmul hi |>.sub (hmul (hci ρ))).abs (hi.sub (hci ρ)).abs
    intro x
    change |w x * F x - c x * F x| ≤ |w x - c x|
    rw [← sub_mul, abs_mul]
    exact (mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)).trans_eq (mul_one _)
  have hbounded := Riesz1.abs_integral_sub_le_of_abs_le μ ν (hc.mul hF) hT.le
    (fun x => by change |c x * F x| ≤ T; rw [abs_mul]; nlinarith [hcb x, hb x, abs_nonneg (c x), abs_nonneg (F x)])
  rw [totalVariation_eq_ofReal_riesz1,
    ENNReal.toReal_ofReal (Riesz1.totalVariation_nonneg μ ν)]
  have ht := dist_triangle4 (∫ x, w x * F x ∂μ) (∫ x, c x * F x ∂μ)
    (∫ x, c x * F x ∂ν) (∫ x, w x * F x ∂ν)
  simp only [Real.dist_eq] at ht
  have hn := herr ν hν
  rw [abs_sub_comm] at hn
  change |(∫ x, w x * F x ∂μ) - ∫ x, w x * F x ∂ν| ≤
    2 * T * Riesz1.totalVariation μ ν + (∫ x, |w x - c x| ∂μ) + (∫ x, |w x - c x| ∂ν)
  change |(∫ x, c x * F x ∂μ) - ∫ x, c x * F x ∂ν| ≤ _ at hbounded
  linarith [herr μ hμ]

/-- Theorem 3 and Corollary 1.1: second moments bound
the two truncation tails, uniformly over every measurable multiplier. -/
theorem weighted_testSup_le_totalVariation_second_moments_internal
    {E : Type*} [MeasurableSpace E] (μ ν : Measure E)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {w : E → ℝ} (hw : Measurable w) (hμ : MemLp w 2 μ) (hν : MemLp w 2 ν)
    {T : ℝ} (hT : 0 < T) :
    (⨆ F : {F : E → ℝ // Measurable F ∧ ∀ x, |F x| ≤ 1},
      ENNReal.ofReal |(∫ x, w x * F.val x ∂μ) - ∫ x, w x * F.val x ∂ν|) ≤
      ENNReal.ofReal (2 * T * (totalVariation μ ν).toReal +
        (∫ x, w x ^ 2 ∂μ) / T + (∫ x, w x ^ 2 ∂ν) / T) := by
  have htail (ρ : Measure E) (hi : MemLp w 2 ρ) :
      (∫ x, |w x - max (-T) (min T (w x))| ∂ρ) ≤ (∫ x, w x ^ 2 ∂ρ) / T := by
    have hm : AEStronglyMeasurable (fun x => |w x - max (-T) (min T (w x))|) ρ := by
      apply Measurable.aestronglyMeasurable; fun_prop
    have hb := fun x => WeakMomentTruncation.abs_sub_clip_le_sq_div (w x) hT
    have hi' := (hi.integrable_sq.div_const T).mono' hm
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_abs]; exact hb x)
    exact (integral_mono hi' (hi.integrable_sq.div_const T) hb).trans_eq (integral_div T _)
  apply iSup_le
  intro F
  apply ENNReal.ofReal_le_ofReal
  exact (abs_weighted_integral_sub_le_totalVariation_tails_internal μ ν hw
    (hμ.integrable one_le_two) (hν.integrable one_le_two) F.property.1 F.property.2 hT).trans
      (add_le_add (add_le_add_right (htail μ hμ) _) (htail ν hν))

/-- Theorem 3, Palm inversion, and Corollary 1.1, fixed
span moments: ordinary TV and a uniform second moment give uniform convergence
of all weight-dominated measurable tests, by truncation. -/
theorem weighted_testSup_tendsto_of_totalVariation_and_second_moment_internal
    {E : Type*} [MeasurableSpace E] (μ : ℕ → Measure E) (ν : Measure E)
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    {w : E → ℝ} (hw : Measurable w) (hμ : ∀ n, MemLp w 2 (μ n)) (hν : MemLp w 2 ν)
    (hTV : Tendsto (fun n => totalVariation (μ n) ν) atTop (𝓝 0))
    {C : ℝ} (hC : ∀ᶠ n in atTop, (∫ x, w x ^ 2 ∂μ n) ≤ C) :
    Tendsto (fun n => ⨆ F : {F : E → ℝ // Measurable F ∧ ∀ x, |F x| ≤ 1},
      ENNReal.ofReal |(∫ x, w x * F.val x ∂μ n) - ∫ x, w x * F.val x ∂ν|)
      atTop (𝓝 0) := by
  have hreal : Tendsto (fun n => (totalVariation (μ n) ν).toReal) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp hTV
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨d, hd, hdε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
  let δ : ℝ := d
  have hδ : 0 < δ := by exact_mod_cast hd
  have hδε : ENNReal.ofReal δ < ε := by simpa only [δ, ENNReal.ofReal_coe_nnreal] using hdε
  let B := max 1 (max C (∫ x, w x ^ 2 ∂ν))
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let T := 8 * B / δ
  have hT : 0 < T := by dsimp [T]; positivity
  have hBT : B / T = δ / 8 := by dsimp [T]; field_simp
  have ht : Tendsto (fun n => 2 * T * (totalVariation (μ n) ν).toReal) atTop (𝓝 0) := by
    simpa using hreal.const_mul (2 * T)
  filter_upwards [hC, ht.eventually_lt_const (show 0 < δ / 2 by positivity)] with n hn hsmall
  apply le_trans (weighted_testSup_le_totalVariation_second_moments_internal
    (μ n) ν hw (hμ n) hν hT)
  apply le_trans (ENNReal.ofReal_le_ofReal (show
      2 * T * (totalVariation (μ n) ν).toReal +
        (∫ x, w x ^ 2 ∂μ n) / T + (∫ x, w x ^ 2 ∂ν) / T ≤ δ from ?_)) hδε.le
  have hf : (∫ x, w x ^ 2 ∂μ n) / T ≤ B / T := div_le_div_of_nonneg_right
    (hn.trans ((le_max_left _ _).trans (le_max_right 1 _))) hT.le
  have hg : (∫ x, w x ^ 2 ∂ν) / T ≤ B / T := div_le_div_of_nonneg_right
    ((le_max_right C _).trans (le_max_right 1 _)) hT.le
  change (∫ x, w x ^ 2 ∂μ n) / T ≤ B / T at hf
  change (∫ x, w x ^ 2 ∂ν) / T ≤ B / T at hg
  rw [hBT] at hf hg
  linarith

/-- Corollary 1.1: specialize the uniform truncation passage to the
constant multiplier one to pass an unbounded moment under total variation. -/
theorem integral_tendsto_of_totalVariation_and_second_moment_internal
    {E : Type*} [MeasurableSpace E] (μ : ℕ → Measure E) (ν : Measure E)
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    {w : E → ℝ} (hw : Measurable w) (hμ : ∀ n, MemLp w 2 (μ n)) (hν : MemLp w 2 ν)
    (hTV : Tendsto (fun n => totalVariation (μ n) ν) atTop (𝓝 0))
    {C : ℝ} (hC : ∀ᶠ n in atTop, (∫ x, w x ^ 2 ∂μ n) ≤ C) :
    Tendsto (fun n => ∫ x, w x ∂μ n) atTop (𝓝 (∫ x, w x ∂ν)) := by
  have ht := weighted_testSup_tendsto_of_totalVariation_and_second_moment_internal
    μ ν hw hμ hν hTV hC
  have hb (n) := le_iSup (fun F : {F : E → ℝ // Measurable F ∧ ∀ x, |F x| ≤ 1} =>
    ENNReal.ofReal |(∫ x, w x * F.val x ∂μ n) - ∫ x, w x * F.val x ∂ν|)
    ⟨fun _ => 1, measurable_const, fun _ => by norm_num⟩
  simp only [mul_one] at hb
  have hz := tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => bot_le) hb
  exact tendsto_iff_dist_tendsto_zero.mpr
    (by simpa only [Function.comp_def, ENNReal.toReal_zero, Real.dist_eq, ENNReal.toReal_ofReal (abs_nonneg _)] using
      (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp hz)

/-- Corollary 1.1: truncation under TV passes both span moments
once a uniform fourth moment has been established. -/
theorem first_second_moments_tendsto_of_totalVariation_fourth_internal
    {E : Type*} [MeasurableSpace E] (μ : ℕ → Measure E) (ν : Measure E)
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure ν]
    {w : E → ℝ} (hw : Measurable w)
    (hμ : ∀ n, MemLp (fun x => w x ^ 2) 2 (μ n))
    (hν : MemLp (fun x => w x ^ 2) 2 ν)
    (hTV : Tendsto (fun n => totalVariation (μ n) ν) atTop (𝓝 0))
    {C : ℝ} (hC : ∀ᶠ n in atTop, (∫ x, (w x ^ 2) ^ 2 ∂μ n) ≤ C) :
    Tendsto (fun n => ∫ x, w x ∂μ n) atTop (𝓝 (∫ x, w x ∂ν)) ∧
      Tendsto (fun n => ∫ x, w x ^ 2 ∂μ n) atTop (𝓝 (∫ x, w x ^ 2 ∂ν)) := by
  have hf (n) : MemLp w 2 (μ n) :=
    (memLp_two_iff_integrable_sq hw.aestronglyMeasurable).mpr ((hμ n).integrable one_le_two)
  have hg : MemLp w 2 ν :=
    (memLp_two_iff_integrable_sq hw.aestronglyMeasurable).mpr (hν.integrable one_le_two)
  have hb : ∀ᶠ n in atTop, (∫ x, w x ^ 2 ∂μ n) ≤ 1 + C := by
    filter_upwards [hC] with n hn
    have ht := integral_mono (hf n).integrable_sq
      ((integrable_const (1 : ℝ)).add (hμ n).integrable_sq)
      (fun x : E => show w x ^ 2 ≤ 1 + (w x ^ 2) ^ 2 by nlinarith [sq_nonneg (w x ^ 2 - 1)])
    simp only [Pi.add_apply] at ht
    rw [integral_add (integrable_const (1 : ℝ)) (hμ n).integrable_sq, integral_const,
      probReal_univ, smul_eq_mul, one_mul] at ht
    linarith
  exact ⟨integral_tendsto_of_totalVariation_and_second_moment_internal μ ν hw hf hg hTV hb,
    integral_tendsto_of_totalVariation_and_second_moment_internal μ ν (hw.pow_const 2)
      hμ hν hTV hC⟩

end Riesz2
