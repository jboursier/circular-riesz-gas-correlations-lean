/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.SubcriticalPowerSum
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.PSeries
public import Mathlib.Tactic

/-!
# Partial sums and tails of `(1 + k)^(-t)`

For `t > 0`, the terms `(1 + k)^(-t)` over `k ∈ ℕ` are the power weights of the cyclic shells
(the proof of Lemma 5.13). This file gives the bounds used there:

* the finite sums `∑_{k < K} (1 + k)^(-t)` for `K ≥ 1`, with the exponent `t < 1`, `t = 1` and
  `t > 1` (the last one by the full series).
* the tail `∑_{k : R ≤ 1 + k} (1 + k)^(-t)` for `t > 1` and `R ≥ 1`, by the integral test.
-/

@[expose] public section

open Finset Set MeasureTheory

namespace Riesz2

/-- The partial sums of `(1 + k)^(-t)` are the sums over `1 ≤ r ≤ K` of `r^(-t)`. -/
theorem sum_range_one_add_rpow_eq_sum_Icc (t : ℝ) (K : ℕ) :
    ∑ k ∈ range K, (1 + (k : ℝ)) ^ (-t) = ∑ r ∈ Icc 1 K, (r : ℝ) ^ (-t) := by
  induction K with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, sum_Icc_succ_top (by omega)]
    congr 1
    push_cast
    congr 1
    ring

/-- For `0 < t < 1` and `K ≥ 1`, the partial sum `∑_{k < K} (1 + k)^(-t)` is at most
`K^(1 - t) / (1 - t)`. -/
theorem sum_range_one_add_rpow_le_of_lt_one {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {K : ℕ}
    (hK : 1 ≤ K) :
    ∑ k ∈ range K, (1 + (k : ℝ)) ^ (-t) ≤ (K : ℝ) ^ (1 - t) / (1 - t) := by
  rw [sum_range_one_add_rpow_eq_sum_Icc]
  exact (subcritical_power_sum ht0 ht1 hK).2

/-- For `K ≥ 1`, the partial sum `∑_{k < K} (1 + k)⁻¹` is at most `1 + log K`. -/
theorem sum_range_one_add_inv_le_one_add_log {K : ℕ} :
    ∑ k ∈ range K, (1 + (k : ℝ))⁻¹ ≤ 1 + Real.log K := by
  have h := harmonic_le_one_add_log K
  have hsum : (harmonic K : ℝ) = ∑ k ∈ range K, (1 + (k : ℝ))⁻¹ := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    refine sum_congr rfl fun k _ => ?_
    push_cast
    ring
  rw [← hsum]
  exact h

/-- The series `∑_{k ∈ ℕ} (1 + k)^(-t)` is summable for `t > 1`. -/
theorem summable_one_add_rpow_neg {t : ℝ} (ht : 1 < t) :
    Summable fun k : ℕ => (1 + (k : ℝ)) ^ (-t) := by
  have h := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (show -t < -1 by linarith))
  refine h.congr fun k => ?_
  push_cast
  congr 1
  ring

/-- For `t > 1`, every partial sum of `(1 + k)^(-t)` is at most the full series. -/
theorem sum_range_one_add_rpow_le_tsum {t : ℝ} (ht : 1 < t) (K : ℕ) :
    ∑ k ∈ range K, (1 + (k : ℝ)) ^ (-t) ≤ ∑' k : ℕ, (1 + (k : ℝ)) ^ (-t) :=
  (summable_one_add_rpow_neg ht).sum_le_tsum _ fun k _ =>
    Real.rpow_nonneg (by positivity) _

/-- For `t > 1` and `R ≥ 1`, the tail of the series over the indices with `R ≤ 1 + k` is at most
`(1 + 1 / (t - 1)) R^(1 - t)`. The proof splits off the term at `k = ⌈R⌉ - 1`, and bounds the rest
by the integral test. -/
theorem tsum_tail_indicator_le {t : ℝ} (ht : 1 < t) {R : ℝ} (hR : 1 ≤ R) :
    ∑' k : ℕ, (if R ≤ 1 + (k : ℝ) then (1 + (k : ℝ)) ^ (-t) else 0) ≤
      (1 + 1 / (t - 1)) * R ^ (1 - t) := by
  set g : ℕ → ℝ := fun k => if R ≤ 1 + (k : ℝ) then (1 + (k : ℝ)) ^ (-t) else 0 with hg
  have hg0 : ∀ k, 0 ≤ g k := fun k => by
    simp only [hg]
    split_ifs
    · exact Real.rpow_nonneg (by positivity) _
    · exact le_rfl
  have hgs : Summable g := by
    refine Summable.of_nonneg_of_le hg0 (fun k => ?_) (summable_one_add_rpow_neg ht)
    simp only [hg]
    split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (by positivity) _
  set J : ℕ := ⌈R⌉₊ with hJ
  have hJ1 : 1 ≤ J := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by linarith)).ne'
  have hRJ : R ≤ (J : ℝ) := Nat.le_ceil R
  have hJR : (J : ℝ) < R + 1 := Nat.ceil_lt_add_one (by linarith)
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ1
  have hRpos : 0 < R := by linarith
  -- The terms with `k < J - 1` vanish, and the term `k = J - 1` equals `J^(-t)`.
  have hhead : ∑ k ∈ range J, g k ≤ (J : ℝ) ^ (-t) := by
    rw [sum_eq_single (J - 1)]
    · have hcast : (1 : ℝ) + ((J - 1 : ℕ) : ℝ) = J := by
        rw [Nat.cast_sub hJ1]
        push_cast
        ring
      have hcond : R ≤ 1 + ((J - 1 : ℕ) : ℝ) := by
        rw [hcast]
        exact hRJ
      have hval : g (J - 1) = (J : ℝ) ^ (-t) := by
        simp [hg, hcast, hRJ]
      rw [hval]
    · intro b hb hne
      have hbJ : b < J := Finset.mem_range.1 hb
      have hb2 : b + 2 ≤ J := by omega
      have hb2' : (b : ℝ) + 2 ≤ (J : ℝ) := by exact_mod_cast hb2
      have hcond : ¬ (R ≤ 1 + (b : ℝ)) := not_le.2 (by linarith)
      simp [hg, hcond]
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h
  -- The terms `k ≥ J` are `(1 + k)^(-t)`, and their sum is bounded by the integral test.
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-t)) (Ici (J : ℝ)) := by
    intro a ha b hb hab
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hJpos ha) hab (by linarith)
  have hintegrable : IntegrableOn (fun x : ℝ => x ^ (-t)) (Ioi (J : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hJpos
  have hnonneg : ∀ x ∈ Ioi (J : ℝ), 0 ≤ x ^ (-t) := fun x hx =>
    Real.rpow_nonneg (lt_trans hJpos hx).le _
  have htail_eq : ∀ k : ℕ, g (k + J) = (((k + J + 1 : ℕ) : ℝ)) ^ (-t) := by
    intro k
    have hcond : R ≤ 1 + ((k + J : ℕ) : ℝ) := by
      push_cast
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    simp only [hg, hcond, ↓reduceIte]
    push_cast
    congr 1
    ring
  have htail : ∑' k : ℕ, g (k + J) ≤ (J : ℝ) ^ (1 - t) / (t - 1) := by
    have hcomp := hanti.tsum_comp_add_le_integral J hintegrable hnonneg
    have hint : ∫ x in Ioi (J : ℝ), x ^ (-t) = (J : ℝ) ^ (1 - t) / (t - 1) := by
      have h1 : -t + 1 = -(t - 1) := by ring
      have h2 : 1 - t = -(t - 1) := by ring
      rw [integral_Ioi_rpow_of_lt (by linarith) hJpos, h1, h2, neg_div_neg_eq]
    rw [hint] at hcomp
    simp only [htail_eq]
    exact hcomp
  rw [← hgs.sum_add_tsum_nat_add J]
  -- The head is at most `J^(-t)`, and `J ≥ R` gives the bound by `R^(1 - t)`.
  have hJt : (J : ℝ) ^ (-t) ≤ R ^ (1 - t) := by
    calc (J : ℝ) ^ (-t) ≤ R ^ (-t) := Real.rpow_le_rpow_of_nonpos hRpos hRJ (by linarith)
      _ ≤ R ^ (1 - t) := Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  have hJt' : (J : ℝ) ^ (1 - t) ≤ R ^ (1 - t) :=
    Real.rpow_le_rpow_of_nonpos hRpos hRJ (by linarith)
  have hdiv : (J : ℝ) ^ (1 - t) / (t - 1) ≤ R ^ (1 - t) / (t - 1) :=
    div_le_div_of_nonneg_right hJt' (by linarith)
  calc ∑ k ∈ range J, g k + ∑' k : ℕ, g (k + J)
      ≤ (J : ℝ) ^ (-t) + (J : ℝ) ^ (1 - t) / (t - 1) := add_le_add hhead htail
    _ ≤ R ^ (1 - t) + R ^ (1 - t) / (t - 1) := add_le_add hJt hdiv
    _ = (1 + 1 / (t - 1)) * R ^ (1 - t) := by ring

end Riesz2

end
