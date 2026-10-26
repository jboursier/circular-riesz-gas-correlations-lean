/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.StretchedCutoffRates
public import Mathlib.Analysis.PSeries

/-!
# Summability of stretched exponential bounds

A positive stretched exponential decays faster than the summable inverse square.
-/

public section

open Filter
open scoped Topology

namespace Riesz2

/-- Every stretched exponential with positive rate and power is summable on the naturals. -/
theorem summable_nat_stretched_exponential (C : ℝ) {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    Summable (fun n : ℕ => C * Real.exp (-c * (n : ℝ) ^ δ)) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  apply hs.of_norm_bounded_eventually_nat
  have ht := ((StretchedCutoff.tendsto_power_mul_exp hδ hc 2).const_mul |C|).comp
    tendsto_natCast_atTop_atTop
  have he : ∀ᶠ n : ℕ in atTop,
      |C| * ((n : ℝ) ^ (2 : ℝ) * Real.exp (-c * (n : ℝ) ^ δ)) ≤ 1 :=
    (ht.eventually_lt_const (by simp : |C| * 0 < (1 : ℝ))).mono fun _ h => h.le
  filter_upwards [eventually_ge_atTop 1, he] with n hn he
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
    Real.rpow_neg hnR.le, Real.rpow_two, ← one_div]
  apply (le_div_iff₀ (sq_pos_of_pos hnR)).mpr
  rw [Real.rpow_two] at he
  nlinarith

end Riesz2
