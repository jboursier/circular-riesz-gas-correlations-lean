/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic

/-!
# Finite sums of a subcritical negative power

The integral comparison is made on the positive carrier. The possible endpoint
value at zero has measure zero and is never used in a monotonicity premise.
-/

public section

open Set MeasureTheory
open scoped BigOperators

namespace Riesz2

/-- Two-sided estimates for `∑_{r=1}^m r⁻ˢ` when `0 < s < 1`. -/
theorem subcritical_power_sum {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {m : ℕ} (hm : 1 ≤ m) :
    (m : ℝ) ^ (1 - s) ≤ ∑ r ∈ Finset.Icc 1 m, (r : ℝ) ^ (-s) ∧
      (∑ r ∈ Finset.Icc 1 m, (r : ℝ) ^ (-s)) ≤ (m : ℝ) ^ (1 - s) / (1 - s) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hsum : (∑ r ∈ Finset.Icc 1 m, (r : ℝ) ^ (-s)) =
      ∑ i ∈ Finset.range m, (((i + 1 : ℕ) : ℝ)) ^ (-s) := by
    have hset : Finset.Icc 1 m = Finset.Ico 1 (m + 1) := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hset, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, Nat.add_comm 1]
  constructor
  · have h := Finset.sum_le_sum (s := Finset.Icc (1 : ℕ) m)
      (f := fun _ => (m : ℝ) ^ (-s)) (g := fun r : ℕ => (r : ℝ) ^ (-s)) ?_
    · simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
        nsmul_eq_mul] at h
      have heq : (m : ℝ) * (m : ℝ) ^ (-s) = (m : ℝ) ^ (1 - s) := by
        simpa only [Real.rpow_one, sub_eq_add_neg] using
          (Real.rpow_add hmpos 1 (-s)).symm
      rwa [heq] at h
    · intro r hr
      have hr' := Finset.mem_Icc.mp hr
      exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (show 0 < r by omega))
        (by exact_mod_cast hr'.2) (by linarith)
  · have hanti : AntitoneOn (fun x : ℝ => x ^ (-s)) (Ioc 0 (0 + (m : ℝ))) := by
      intro x hx y _ hxy
      exact Real.rpow_le_rpow_of_nonpos hx.1 hxy (by linarith)
    have hint : IntegrableOn (fun x : ℝ => x ^ (-s)) (Icc 0 (0 + (m : ℝ))) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity)).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    have h := hanti.sum_le_integral_of_integrableOn hint
    rw [integral_rpow (Or.inl (by linarith)),
      show -s + 1 = 1 - s by ring, Real.zero_rpow (by linarith : 1 - s ≠ 0),
      sub_zero] at h
    simpa only [hsum, zero_add] using h

end Riesz2
