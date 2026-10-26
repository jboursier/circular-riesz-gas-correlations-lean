/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.TotalVariation
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Order.Basic

/-!
# Weighted measurable tests and event approximation

Bounded multipliers of a weight control every measurable test dominated by
the absolute value of that weight. Approximation of event masses then bounds
the event-supremum distance, with its actual normalization.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Riesz2

/-- The multiplier `H / w` is a bounded measurable test whenever `|H| ≤ |w|`.
At zeros of `w`, the bound forces `H = 0`, so multiplication recovers `H`
everywhere, without an almost-everywhere or positivity restriction. -/
theorem exists_bounded_multiplier_of_abs_le
    {α : Type*} [MeasurableSpace α] {w H : α → ℝ}
    (hw : Measurable w) (hH : Measurable H) (hb : ∀ x, |H x| ≤ |w x|) :
    ∃ F : α → ℝ, Measurable F ∧ (∀ x, |F x| ≤ 1) ∧ ∀ x, w x * F x = H x := by
  refine ⟨fun x => H x / w x, hH.div hw, fun x => ?_, fun x => ?_⟩
  · by_cases hx : w x = 0
    · simp only [hx, div_zero, abs_zero, zero_le_one]
    · rw [abs_div, div_le_iff₀ (abs_pos.mpr hx), one_mul]
      exact hb x
  · by_cases hx : w x = 0
    · have hHzero : H x = 0 := abs_eq_zero.mp (le_antisymm (by simpa [hx] using hb x) (abs_nonneg _))
      simp only [hx, hHzero, zero_div, mul_zero]
    · field_simp

/-- The bounded-multiplier supremum controls every measurable test dominated
by the weight. This does not use an integral's value to infer integrability. -/
theorem dominated_test_le_weightedTestSup
    {α : Type*} [MeasurableSpace α] (μ ν : Measure α) {w H : α → ℝ}
    (hw : Measurable w) (hH : Measurable H) (hb : ∀ x, |H x| ≤ |w x|) :
    ENNReal.ofReal |(∫ x, H x ∂μ) - ∫ x, H x ∂ν| ≤
      ⨆ F : {F : α → ℝ // Measurable F ∧ ∀ x, |F x| ≤ 1},
        ENNReal.ofReal |(∫ x, w x * F.val x ∂μ) - ∫ x, w x * F.val x ∂ν| := by
  obtain ⟨F, hF, hbF, he⟩ := exists_bounded_multiplier_of_abs_le hw hH hb
  have hfun : (fun x => w x * F x) = H := funext he
  have h := le_iSup (fun F : {F : α → ℝ // Measurable F ∧ ∀ x, |F x| ≤ 1} =>
    ENNReal.ofReal |(∫ x, w x * F.val x ∂μ) - ∫ x, w x * F.val x ∂ν|) ⟨F, hF, hbF⟩
  simpa only [hfun] using h

/-- Convergence of the bounded-multiplier supremum is uniform over all
measurable tests dominated by the absolute weight. -/
theorem dominated_testSup_tendsto_of_weightedTestSup_tendsto
    {α : Type*} [MeasurableSpace α] (μ : ℕ → Measure α) (ν : Measure α)
    (w : α → ℝ) (hw : Measurable w)
    (ht : Tendsto (fun n : ℕ =>
      ⨆ F : {F : α → ℝ // Measurable F ∧ ∀ x, |F x| ≤ 1},
        ENNReal.ofReal |(∫ x, w x * F.val x ∂μ n) - ∫ x, w x * F.val x ∂ν|)
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      ⨆ H : {H : α → ℝ // Measurable H ∧ ∀ x, |H x| ≤ |w x|},
        ENNReal.ofReal |(∫ x, H.val x ∂μ n) - ∫ x, H.val x ∂ν|)
      atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => bot_le)
  intro n
  apply iSup_le
  intro H
  exact dominated_test_le_weightedTestSup (μ n) ν hw H.property.1 H.property.2

/-- Domination by an integrable weight gives integrability of the test. -/
theorem integrable_of_abs_le_weight
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {w H : α → ℝ}
    (hw : Integrable w μ) (hH : Measurable H) (hb : ∀ x, |H x| ≤ |w x|) :
    Integrable H μ :=
  hw.mono hH.aestronglyMeasurable (ae_of_all _ fun x => by
    simpa only [Real.norm_eq_abs] using hb x)

/-- A finite event-mass difference is the absolute real-mass difference. -/
theorem event_difference_eq_ofReal_abs (a b : ℝ≥0∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    (a - b) + (b - a) = ENNReal.ofReal |a.toReal - b.toReal| := by
  rcases le_total a b with h | h
  · rw [tsub_eq_zero_of_le h, zero_add, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr (ENNReal.toReal_mono hb h))]
    exact (ENNReal.ofReal_toReal (ne_top_of_le_ne_top hb tsub_le_self)).symm.trans
      (congrArg ENNReal.ofReal (ENNReal.toReal_sub_of_le h hb))
  · rw [tsub_eq_zero_of_le h, add_zero,
      abs_of_nonneg (sub_nonneg.mpr (ENNReal.toReal_mono ha h))]
    exact (ENNReal.ofReal_toReal (ne_top_of_le_ne_top ha tsub_le_self)).symm.trans
      (congrArg ENNReal.ofReal (ENNReal.toReal_sub_of_le h ha))

/-- Approximating every event mass by the same dominated test bounds the event
distance by two approximation errors and the weighted test supremum. The
approximation errors are extended-valued and need not be finite. -/
theorem totalVariation_le_weightedTestSup_of_event_approximation
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ ν : Measure α) (P Q : Measure β) [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (w : α → ℝ) (hw : Measurable w) (eP eQ : ℝ≥0∞)
    (happrox : ∀ A : Set β, MeasurableSet A → ∃ H : α → ℝ,
      Measurable H ∧ (∀ x, |H x| ≤ |w x|) ∧
      ENNReal.ofReal |(P A).toReal - ∫ x, H x ∂μ| ≤ eP ∧
      ENNReal.ofReal |(Q A).toReal - ∫ x, H x ∂ν| ≤ eQ) :
    totalVariation P Q ≤ eP +
      (⨆ F : {F : α → ℝ // Measurable F ∧ ∀ x, |F x| ≤ 1},
        ENNReal.ofReal |(∫ x, w x * F.val x ∂μ) - ∫ x, w x * F.val x ∂ν|) + eQ := by
  apply iSup_le
  rintro ⟨A, hA⟩
  obtain ⟨H, hH, hb, hP, hQ⟩ := happrox A hA
  rw [event_difference_eq_ofReal_abs _ _ (measure_ne_top _ _) (measure_ne_top _ _)]
  have htriangle : |(P A).toReal - (Q A).toReal| ≤
      |(P A).toReal - ∫ x, H x ∂μ| +
        |(∫ x, H x ∂μ) - ∫ x, H x ∂ν| +
        |(Q A).toReal - ∫ x, H x ∂ν| := by
    have h := (abs_sub_le (P A).toReal (∫ x, H x ∂μ) (Q A).toReal).trans
      (add_le_add_right (abs_sub_le (∫ x, H x ∂μ) (∫ x, H x ∂ν) (Q A).toReal) _)
    rw [abs_sub_comm (∫ x, H x ∂ν) (Q A).toReal] at h
    linarith
  apply (ENNReal.ofReal_le_ofReal htriangle).trans
  rw [ENNReal.ofReal_add (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _),
    ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  exact add_le_add (add_le_add hP (dominated_test_le_weightedTestSup μ ν hw hH hb)) hQ

/-- A vanishing approximation error at a large fixed scale, followed by a
vanishing error along the sequence, gives convergence to zero. The sequence
bound need hold only eventually at each fixed scale. -/
theorem tendsto_zero_of_two_scale_bound
    {f a c : ℕ → ℝ≥0∞} {b : ℕ → ℕ → ℝ≥0∞}
    (ha : Tendsto a atTop (𝓝 0)) (hc : Tendsto c atTop (𝓝 0))
    (hb : ∀ m, Tendsto (b m) atTop (𝓝 0))
    (hbound : ∀ m, ∀ᶠ n in atTop, f n ≤ a m + b m n + c m) :
    Tendsto f atTop (𝓝 0) := by
  have hac : Tendsto (fun m => a m + c m) atTop (𝓝 0) := by
    simpa only [add_zero] using ha.add hc
  refine ENNReal.tendsto_nhds_zero.mpr fun ε hε => ?_
  have hhalf : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨m, hm⟩ := (ENNReal.tendsto_nhds_zero.mp hac (ε / 2) hhalf).exists
  filter_upwards [hbound m, ENNReal.tendsto_nhds_zero.mp (hb m) (ε / 2) hhalf]
    with n hn hb'
  calc
    f n ≤ a m + b m n + c m := hn
    _ = (a m + c m) + b m n := by ac_rfl
    _ ≤ ε / 2 + ε / 2 := add_le_add hm hb'
    _ = ε := ENNReal.add_halves ε

/-- Weighted test convergence at each fixed approximation scale and vanishing
event-mass approximation errors imply total variation convergence. The spaces
of finite coordinates may vary with the approximation scale. All approximation
tests are explicitly integrable under both input measures. -/
theorem totalVariation_tendsto_of_weighted_event_approximations
    {α : ℕ → Type*} [∀ m, MeasurableSpace (α m)]
    {β : Type*} [MeasurableSpace β]
    (μ : (m : ℕ) → ℕ → Measure (α m)) (ν : (m : ℕ) → Measure (α m))
    (P : ℕ → Measure β) (Q : Measure β)
    [∀ n, IsFiniteMeasure (P n)] [IsFiniteMeasure Q]
    (w : (m : ℕ) → α m → ℝ) (hw : ∀ m, Measurable (w m))
    (eP eQ : ℕ → ℝ≥0∞)
    (heP : Tendsto eP atTop (𝓝 0)) (heQ : Tendsto eQ atTop (𝓝 0))
    (hweighted : ∀ m, Tendsto (fun n : ℕ =>
      ⨆ F : {F : α m → ℝ // Measurable F ∧ ∀ x, |F x| ≤ 1},
        ENNReal.ofReal |(∫ x, w m x * F.val x ∂μ m n) -
          ∫ x, w m x * F.val x ∂ν m|) atTop (𝓝 0))
    (happrox : ∀ m, ∀ᶠ n in atTop, ∀ A : Set β, MeasurableSet A →
      ∃ H : α m → ℝ,
        Measurable H ∧ (∀ x, |H x| ≤ |w m x|) ∧
        Integrable H (μ m n) ∧ Integrable H (ν m) ∧
        ENNReal.ofReal |(P n A).toReal - ∫ x, H x ∂μ m n| ≤ eP m ∧
        ENNReal.ofReal |(Q A).toReal - ∫ x, H x ∂ν m| ≤ eQ m) :
    Tendsto (fun n => totalVariation (P n) Q) atTop (𝓝 0) := by
  apply tendsto_zero_of_two_scale_bound heP heQ hweighted
  intro m
  filter_upwards [happrox m] with n hn
  apply totalVariation_le_weightedTestSup_of_event_approximation
    (μ m n) (ν m) (P n) Q (w m) (hw m) (eP m) (eQ m)
  intro A hA
  obtain ⟨H, hH, hb, _, _, hP, hQ⟩ := hn A hA
  exact ⟨H, hH, hb, hP, hQ⟩

end Riesz2
