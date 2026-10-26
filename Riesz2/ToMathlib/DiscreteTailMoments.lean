/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Tactic

/-!
# Moments from tails at integer thresholds

A summable majorant for the integer tails controls every positive real
moment. The bounds are nonnegative integrals, without integrability premises.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Riesz2

/-- A discrete tail sum bounds a positive real power. The estimate works for
every nonnegative real value, without an integer-valued assumption. -/
theorem rpow_le_one_add_discrete_tails (x p : ℝ) (hx : 0 ≤ x) (hp : 0 < p) :
    ENNReal.ofReal (x ^ p) ≤ 1 + ∑' n : ℕ,
      {x : ℝ | (n : ℝ) + 1 < x}.indicator
        (fun _ => ENNReal.ofReal (((n : ℝ) + 2) ^ p)) x := by
  by_cases hx1 : x ≤ 1
  · apply (show ENNReal.ofReal (x ^ p) ≤ 1 from ?_).trans le_self_add
    simpa only [Real.one_rpow, ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hx hx1 hp.le)
  · have hx1 : 1 < x := lt_of_not_ge hx1
    let n := ⌈x⌉₊ - 2
    have hc : 2 ≤ ⌈x⌉₊ := by
      by_contra h
      have hle : (⌈x⌉₊ : ℝ) ≤ 1 := by exact_mod_cast (show ⌈x⌉₊ ≤ 1 by omega)
      linarith [Nat.le_ceil x]
    have hn : (n : ℝ) + 2 = (⌈x⌉₊ : ℝ) := by
      dsimp [n]
      exact_mod_cast Nat.sub_add_cancel hc
    have hnx : (n : ℝ) + 1 < x := by
      have hceil := Nat.ceil_lt_add_one hx
      linarith
    have hterm : ENNReal.ofReal (x ^ p) ≤
        {x : ℝ | (n : ℝ) + 1 < x}.indicator
          (fun _ => ENNReal.ofReal (((n : ℝ) + 2) ^ p)) x := by
      rw [indicator_of_mem (show x ∈ {x : ℝ | (n : ℝ) + 1 < x} from hnx)]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hx (hn ▸ Nat.le_ceil x) hp.le)
    apply hterm.trans
    apply le_trans (ENNReal.le_tsum (f := fun n : ℕ =>
      {x : ℝ | (n : ℝ) + 1 < x}.indicator
        (fun _ => ENNReal.ofReal (((n : ℝ) + 2) ^ p)) x) n)
    exact le_add_self

/-- Integer-threshold tails control the moment by an explicit nonnegative
series, also when either side is infinite. -/
theorem lintegral_rpow_le_discrete_tails
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (hfn : ∀ x, 0 ≤ f x)
    (p : ℝ) (hp : 0 < p) :
    (∫⁻ x, ENNReal.ofReal (f x ^ p) ∂μ) ≤ 1 + ∑' n : ℕ,
      ENNReal.ofReal (((n : ℝ) + 2) ^ p) * μ {x | (n : ℝ) + 1 < f x} := by
  have hE (n : ℕ) : MeasurableSet {x | (n : ℝ) + 1 < f x} :=
    measurableSet_lt measurable_const hf
  calc
    _ ≤ ∫⁻ x, (1 : ℝ≥0∞) + ∑' n : ℕ,
        {x | (n : ℝ) + 1 < f x}.indicator
          (fun _ => ENNReal.ofReal (((n : ℝ) + 2) ^ p)) x ∂μ := by
      apply lintegral_mono
      intro x
      simpa only [indicator_apply, mem_ofPred_eq] using rpow_le_one_add_discrete_tails (f x) p (hfn x) hp
    _ = _ := by
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
        lintegral_tsum (fun n => (measurable_const.indicator (hE n)).aemeasurable)]
      congr 1
      apply tsum_congr
      intro n
      rw [lintegral_indicator (hE n), lintegral_const, Measure.restrict_apply_univ]

/-- A polynomial tail of order strictly larger than `p + 1` controls the
`p`th moment uniformly. The same constant applies to every probability space
and observable satisfying the displayed tail bound. -/
theorem exists_moment_bound_of_polynomial_tails
    (p k B : ℝ) (hp : 0 < p) (hk : p + 1 < k) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ),
      Measurable f → (∀ x, 0 ≤ f x) →
      (∀ n : ℕ, μ {x | (n : ℝ) + 1 < f x} ≤
        ENNReal.ofReal (B / ((n : ℝ) + 1) ^ k)) →
      (∫⁻ x, ENNReal.ofReal (f x ^ p) ∂μ) ≤ ENNReal.ofReal C := by
  let g : ℕ → ℝ := fun n => 2 ^ p * B * ((n : ℝ) + 1) ^ (p - k)
  have hg : Summable g := by
    have hs := (Real.summable_nat_rpow.mpr (show p - k < -1 by linarith)).comp_injective
      (show Function.Injective (fun n : ℕ => n + 1) from fun _ _ h => Nat.add_right_cancel h)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, g] using hs.mul_left (2 ^ p * B)
  have hg0 (n : ℕ) : 0 ≤ g n := by dsimp [g]; positivity
  refine ⟨2 + ∑' n, g n, by positivity, ?_⟩
  intro Ω _ μ _ f hf hfn htail
  apply (lintegral_rpow_le_discrete_tails μ f hf hfn p hp).trans
  have hs : (∑' n : ℕ, ENNReal.ofReal (((n : ℝ) + 2) ^ p) *
      μ {x | (n : ℝ) + 1 < f x}) ≤ ENNReal.ofReal (∑' n, g n) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hg0 hg]
    apply ENNReal.tsum_le_tsum
    intro n
    apply (mul_le_mul' le_rfl (htail n)).trans
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hn : 0 < (n : ℝ) + 1 := by positivity
    have hbase : (n : ℝ) + 2 ≤ 2 * ((n : ℝ) + 1) := by linarith [Nat.cast_nonneg (α := ℝ) n]
    calc
      _ ≤ (2 * ((n : ℝ) + 1)) ^ p * (B / ((n : ℝ) + 1) ^ k) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity) hbase hp.le)
          (by positivity)
      _ = g n := by
        dsimp [g]
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hn.le,
          Real.rpow_sub hn]
        ring
  apply (add_le_add le_rfl hs).trans
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (tsum_nonneg hg0)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

end Riesz2
