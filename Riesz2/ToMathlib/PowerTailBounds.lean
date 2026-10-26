/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Bridges.CyclicLabels
public import Riesz2.ToMathlib.CyclicDistance
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# Quantified power sums on the cycle

This file proves the periodization bound used in the proof of Lemma 2.5, together with
finite shell bounds on the cycle.

For an exponent `p > 1` and an integer `N ≥ 2`, the periodized power sum
`∑_{ℓ ∈ ℤ} 1 / (1 + |n + ℓ N|^p)` of an integer `n` is summable and at most
`C / (1 + d_N(n, 0)^p)`, where `d_N(n, 0) = Riesz1.cyclicDist N n 0` is the integer cyclic distance
and the constant `C` depends only on `p`. The factor `N^{-p}` is at most `2 / (1 + d_N(n, 0)^p)`.

The finite shells `cyclicShell` of `Riesz2.ToMathlib.CyclicDistance` contain at most two labels
each. Hence a sum over the labels `j` of a nonnegative summable function of the cyclic distance
`d_N(i, j)` is at most twice the full sum of that function. In particular
`∑_j 1 / (1 + d_N(i, j)^p)` is bounded by a constant depending only on `p`, uniformly in `N`.
-/

@[expose] public section

open Finset

namespace Riesz2

/-- Every integer `n` is `x + ℓ N` for an integer `x` with `|x| = d_N(n, 0)` and `2 |x| ≤ N`. -/
theorem exists_rep_cyclicDist (N : ℕ+) (n : ℤ) :
    ∃ x ℓ : ℤ, n = x + ℓ * ((N : ℕ) : ℤ) ∧ |x| = Riesz1.cyclicDist N n 0 ∧
      2 * |x| ≤ ((N : ℕ) : ℤ) := by
  have hN : (0 : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast N.pos
  have hr0 : 0 ≤ n % ((N : ℕ) : ℤ) := Int.emod_nonneg n hN.ne'
  have hrN : n % ((N : ℕ) : ℤ) < ((N : ℕ) : ℤ) := Int.emod_lt_of_pos n hN
  have hdiv : ((N : ℕ) : ℤ) * (n / ((N : ℕ) : ℤ)) + n % ((N : ℕ) : ℤ) = n := by
    rw [add_comm, mul_comm]
    exact Int.emod_add_ediv_mul n _
  have hd : Riesz1.cyclicDist N n 0 =
      min (n % ((N : ℕ) : ℤ)) (((N : ℕ) : ℤ) - n % ((N : ℕ) : ℤ)) := by
    unfold Riesz1.cyclicDist
    rw [Int.zero_emod, sub_zero, abs_of_nonneg hr0]
  set r := n % ((N : ℕ) : ℤ) with hr
  set q := n / ((N : ℕ) : ℤ) with hq
  rcases le_total (2 * r) ((N : ℕ) : ℤ) with h | h
  · refine ⟨r, q, by linear_combination -hdiv, ?_, ?_⟩
    · rw [hd, abs_of_nonneg hr0, min_eq_left (show r ≤ ((N : ℕ) : ℤ) - r by linarith)]
    · rw [abs_of_nonneg hr0]
      exact h
  · have hxneg : r - ((N : ℕ) : ℤ) ≤ 0 := by linarith
    refine ⟨r - ((N : ℕ) : ℤ), q + 1, by linear_combination -hdiv, ?_, ?_⟩
    · rw [hd, abs_of_nonpos hxneg, min_eq_right (show ((N : ℕ) : ℤ) - r ≤ r by linarith)]
      ring
    · rw [abs_of_nonpos hxneg]
      linarith

/-- For `N ≥ 2`, `2 |x| ≤ N` and `1 ≤ |ℓ|`, the value `|x + ℓ N|` is at least `|ℓ| N / 2`. -/
theorem half_mul_le_abs_add {x ℓ N : ℝ} (hN : 2 ≤ N) (hx : 2 * |x| ≤ N) (hℓ : 1 ≤ |ℓ|) :
    |ℓ| * N / 2 ≤ |x + ℓ * N| := by
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hmul : |ℓ * N| = |ℓ| * N := by rw [abs_mul, abs_of_nonneg hN0]
  have h1 : |ℓ| * N ≤ |x + ℓ * N| + |x| := by
    have h := abs_sub (x + ℓ * N) x
    rw [add_sub_cancel_left, hmul] at h
    exact h
  nlinarith [mul_nonneg (sub_nonneg.2 hℓ) hN0]

/-- For `a, N > 0` and `a N / 2 ≤ |y|`, the term `1 / (1 + |y|^p)` is at most
`2^p N^{-p} a^{-p}`. -/
theorem inv_one_add_rpow_le {p a N y : ℝ} (hp : 0 < p) (ha : 0 < a) (hN : 0 < N)
    (hy : a * N / 2 ≤ |y|) :
    1 / (1 + |y| ^ p) ≤ 2 ^ p * N ^ (-p) * a ^ (-p) := by
  have hpos : 0 < a * N / 2 := div_pos (mul_pos ha hN) two_pos
  have hyp : 0 < |y| := lt_of_lt_of_le hpos hy
  have hyp' : 0 < |y| ^ p := Real.rpow_pos_of_pos hyp p
  have hpow : (a * N / 2) ^ p ≤ |y| ^ p := Real.rpow_le_rpow hpos.le hy hp.le
  have hpow' : 0 < (a * N / 2) ^ p := Real.rpow_pos_of_pos hpos p
  have heq : 1 / (a * N / 2) ^ p = 2 ^ p * N ^ (-p) * a ^ (-p) := by
    rw [Real.div_rpow (mul_nonneg ha.le hN.le) (by norm_num : (0 : ℝ) ≤ 2) p,
      Real.mul_rpow ha.le hN.le, Real.rpow_neg ha.le, Real.rpow_neg hN.le]
    have hap : 0 < a ^ p := Real.rpow_pos_of_pos ha p
    have hNp : 0 < N ^ p := Real.rpow_pos_of_pos hN p
    field_simp
  calc 1 / (1 + |y| ^ p) ≤ 1 / |y| ^ p := one_div_le_one_div_of_le hyp' (by linarith)
    _ ≤ 1 / (a * N / 2) ^ p := one_div_le_one_div_of_le hpow' hpow
    _ = 2 ^ p * N ^ (-p) * a ^ (-p) := heq

/-- For `p ≥ 0`, `1 ≤ N` and `2 d ≤ N`, the factor `N^{-p}` is at most `2 / (1 + d^p)`. -/
theorem rpow_neg_le_two_div_one_add {p N d : ℝ} (hp : 0 ≤ p) (hN : 1 ≤ N) (hd : 0 ≤ d)
    (hdN : 2 * d ≤ N) :
    N ^ (-p) ≤ 2 / (1 + d ^ p) := by
  have hN0 : 0 < N := by linarith
  have h1 : N ^ (-p) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
  have h2 : d ^ p * N ^ (-p) ≤ 1 := by
    rw [Real.rpow_neg hN0.le, ← div_eq_mul_inv, ← Real.div_rpow hd hN0.le]
    exact Real.rpow_le_one (div_nonneg hd hN0.le) (by rw [div_le_one hN0]; linarith) hp
  have hdp : 0 ≤ d ^ p := Real.rpow_nonneg hd p
  have hD : 0 < 1 + d ^ p := by linarith
  rw [le_div_iff₀ hD]
  nlinarith

/-- Let `p > 1`, let `N ≥ 2` and let `x` be an integer with `2 |x| ≤ N`. Then the periodized sum
`∑_{ℓ ∈ ℤ} 1 / (1 + |x + ℓ N|^p)` is summable, and it is at most
`(1 + 2^(p+1) S_p) / (1 + |x|^p)`, where `S_p = ∑_{ℓ ∈ ℤ} |ℓ|^{-p}` is finite. -/
theorem summable_and_tsum_le_of_rep {p : ℝ} (hp : 1 < p) {N : ℕ+} (hN : 2 ≤ (N : ℕ)) {x : ℤ}
    (hx : 2 * |x| ≤ ((N : ℕ) : ℤ)) :
    Summable (fun ℓ : ℤ => 1 / (1 + |(x : ℝ) + (ℓ : ℝ) * ((N : ℕ) : ℝ)| ^ p)) ∧
      ∑' ℓ : ℤ, 1 / (1 + |(x : ℝ) + (ℓ : ℝ) * ((N : ℕ) : ℝ)| ^ p) ≤
        (1 + 2 ^ (p + 1) * ∑' ℓ : ℤ, |(ℓ : ℝ)| ^ (-p)) / (1 + |(x : ℝ)| ^ p) := by
  have hp0 : 0 < p := by linarith
  have hp1 : -p ≠ 0 := neg_ne_zero.mpr hp0.ne'
  have hNR : (2 : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast hN
  have hxR : 2 * |(x : ℝ)| ≤ ((N : ℕ) : ℝ) := by exact_mod_cast hx
  have hS : 0 ≤ ∑' ℓ : ℤ, |(ℓ : ℝ)| ^ (-p) :=
    tsum_nonneg fun ℓ => Real.rpow_nonneg (abs_nonneg _) _
  -- The majorant: the term at `ℓ = 0` is `1 / (1 + |x|^p)`, and every other term is at most
  -- `2^p N^{-p} |ℓ|^{-p}`.
  have hterm : ∀ ℓ : ℤ, 1 / (1 + |(x : ℝ) + (ℓ : ℝ) * ((N : ℕ) : ℝ)| ^ p) ≤
      (if ℓ = 0 then 1 / (1 + |(x : ℝ)| ^ p) else 0) +
        2 ^ p * ((N : ℕ) : ℝ) ^ (-p) * |(ℓ : ℝ)| ^ (-p) := by
    intro ℓ
    by_cases h0 : ℓ = 0
    · subst h0
      simp [Real.zero_rpow hp1]
    · have hA : (1 : ℝ) ≤ |(ℓ : ℝ)| := by
        have h1 : (1 : ℤ) ≤ |ℓ| := Int.one_le_abs h0
        exact_mod_cast h1
      have hy := half_mul_le_abs_add hNR hxR hA
      have hbound := inv_one_add_rpow_le hp0 (by linarith) (by linarith) hy
      simp only [h0, ↓reduceIte, zero_add]
      exact hbound
  have hg1 : Summable (fun ℓ : ℤ => if ℓ = 0 then 1 / (1 + |(x : ℝ)| ^ p) else 0) :=
    (hasSum_ite_eq (0 : ℤ) (1 / (1 + |(x : ℝ)| ^ p))).summable
  have hg2 : Summable (fun ℓ : ℤ => 2 ^ p * ((N : ℕ) : ℝ) ^ (-p) * |(ℓ : ℝ)| ^ (-p)) :=
    (Real.summable_abs_int_rpow hp).mul_left _
  have hsum : Summable (fun ℓ : ℤ => 1 / (1 + |(x : ℝ) + (ℓ : ℝ) * ((N : ℕ) : ℝ)| ^ p)) :=
    Summable.of_nonneg_of_le (fun ℓ => by positivity) hterm (hg1.add hg2)
  refine ⟨hsum, ?_⟩
  have hD : 0 < 1 + |(x : ℝ)| ^ p := by
    have := Real.rpow_nonneg (abs_nonneg (x : ℝ)) p
    linarith
  have hNinv := rpow_neg_le_two_div_one_add hp0.le (by linarith : (1 : ℝ) ≤ ((N : ℕ) : ℝ))
    (abs_nonneg (x : ℝ)) hxR
  have h2p : (2 : ℝ) ^ (p + 1) = 2 ^ p * 2 := Real.rpow_add_one two_ne_zero p
  calc ∑' ℓ : ℤ, 1 / (1 + |(x : ℝ) + (ℓ : ℝ) * ((N : ℕ) : ℝ)| ^ p)
      ≤ ∑' ℓ : ℤ, ((if ℓ = 0 then 1 / (1 + |(x : ℝ)| ^ p) else 0) +
          2 ^ p * ((N : ℕ) : ℝ) ^ (-p) * |(ℓ : ℝ)| ^ (-p)) :=
        Summable.tsum_le_tsum hterm hsum (hg1.add hg2)
    _ = 1 / (1 + |(x : ℝ)| ^ p) + 2 ^ p * ((N : ℕ) : ℝ) ^ (-p) * ∑' ℓ : ℤ, |(ℓ : ℝ)| ^ (-p) := by
        rw [hg1.tsum_add hg2, tsum_ite_eq, tsum_mul_left]
    _ ≤ 1 / (1 + |(x : ℝ)| ^ p) + 2 ^ p * (2 / (1 + |(x : ℝ)| ^ p)) *
          ∑' ℓ : ℤ, |(ℓ : ℝ)| ^ (-p) := by
        have hmid : 2 ^ p * ((N : ℕ) : ℝ) ^ (-p) ≤ 2 ^ p * (2 / (1 + |(x : ℝ)| ^ p)) :=
          mul_le_mul_of_nonneg_left hNinv (Real.rpow_nonneg (by norm_num) p)
        have hmid' := mul_le_mul_of_nonneg_right hmid hS
        linarith [hmid', mul_assoc (2 ^ p * ((N : ℕ) : ℝ) ^ (-p)) (∑' ℓ : ℤ, |(ℓ : ℝ)| ^ (-p))
          (∑' ℓ : ℤ, |(ℓ : ℝ)| ^ (-p))]
    _ = (1 + 2 ^ (p + 1) * ∑' ℓ : ℤ, |(ℓ : ℝ)| ^ (-p)) / (1 + |(x : ℝ)| ^ p) := by
        rw [h2p]
        field_simp

/-- Let `p > 1`. Then there exists a constant `C > 0` such that, for every integer `N ≥ 2` and every
integer `n` (which represents a residue of the cycle `C_N`), the periodized sum
`∑_{ℓ ∈ ℤ} 1 / (1 + |n + ℓ N|^p)` is summable, at most `C / (1 + d_N(n, 0)^p)`, and
`N^{-p} ≤ 2 / (1 + d_N(n, 0)^p)`, where `d_N(n, 0) = Riesz1.cyclicDist N n 0`.

This bound is used in the proof of Lemma 2.5. The terms are nonnegative, so the inequality
in `[0, ∞]` already implies summability. The summability conjunct rules out the junk value of `tsum`. -/
theorem inverse_power_sum {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ n : ℤ,
      Summable (fun ℓ : ℤ => 1 / (1 + |(n : ℝ) + (ℓ : ℝ) * ((N : ℕ) : ℝ)| ^ p)) ∧
      ∑' ℓ : ℤ, 1 / (1 + |(n : ℝ) + (ℓ : ℝ) * ((N : ℕ) : ℝ)| ^ p) ≤
        C / (1 + ((Riesz1.cyclicDist N n 0 : ℤ) : ℝ) ^ p) ∧
      ((N : ℕ) : ℝ) ^ (-p) ≤ 2 / (1 + ((Riesz1.cyclicDist N n 0 : ℤ) : ℝ) ^ p) := by
  have hS : 0 ≤ ∑' ℓ : ℤ, |(ℓ : ℝ)| ^ (-p) :=
    tsum_nonneg fun ℓ => Real.rpow_nonneg (abs_nonneg _) _
  refine ⟨1 + 2 ^ (p + 1) * ∑' ℓ : ℤ, |(ℓ : ℝ)| ^ (-p), ?_, ?_⟩
  · have h2 : (0 : ℝ) < 2 ^ (p + 1) := Real.rpow_pos_of_pos two_pos _
    nlinarith
  · intro N hN n
    obtain ⟨x, ℓ0, hn, hd, hx⟩ := exists_rep_cyclicDist N n
    have hdR : ((Riesz1.cyclicDist N n 0 : ℤ) : ℝ) = |(x : ℝ)| := by
      rw [← hd, Int.cast_abs]
    have hxR : 2 * |(x : ℝ)| ≤ ((N : ℕ) : ℝ) := by exact_mod_cast hx
    have hNR : (1 : ℝ) ≤ ((N : ℕ) : ℝ) := by
      have : (2 : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast hN
      linarith
    obtain ⟨hsumx, hboundx⟩ := summable_and_tsum_le_of_rep hp hN hx
    -- The periodized sum of `n` is a reindexing of the periodized sum of `x`, shifted by `ℓ0`.
    have hfun : (fun ℓ : ℤ => 1 / (1 + |(n : ℝ) + (ℓ : ℝ) * ((N : ℕ) : ℝ)| ^ p)) =
        (fun ℓ : ℤ => 1 / (1 + |(x : ℝ) + (ℓ : ℝ) * ((N : ℕ) : ℝ)| ^ p)) ∘
          (Equiv.addRight ℓ0) := by
      funext ℓ
      have hnℓ : (n : ℝ) + (ℓ : ℝ) * ((N : ℕ) : ℝ) =
          (x : ℝ) + (((ℓ + ℓ0 : ℤ)) : ℝ) * ((N : ℕ) : ℝ) := by
        rw [hn]
        push_cast
        ring
      simp only [Function.comp_apply, Equiv.coe_addRight, hnℓ]
    have htsum : ∑' ℓ : ℤ, 1 / (1 + |(n : ℝ) + (ℓ : ℝ) * ((N : ℕ) : ℝ)| ^ p) =
        ∑' ℓ : ℤ, 1 / (1 + |(x : ℝ) + (ℓ : ℝ) * ((N : ℕ) : ℝ)| ^ p) := by
      rw [hfun]
      exact (Equiv.tsum_eq (Equiv.addRight ℓ0)
        (fun ℓ : ℤ => 1 / (1 + |(x : ℝ) + (ℓ : ℝ) * ((N : ℕ) : ℝ)| ^ p)))
    refine ⟨?_, ?_, ?_⟩
    · rw [hfun]
      exact (Equiv.addRight ℓ0).summable_iff.2 hsumx
    · rw [htsum, hdR]
      exact hboundx
    · rw [hdR]
      exact rpow_neg_le_two_div_one_add (by linarith : (0 : ℝ) ≤ p) hNR (abs_nonneg _) hxR

/-- Let `p > 1`. Then `∑_{k ∈ ℕ} 1 / (1 + k^p)` is summable. -/
theorem summable_inv_one_add_rpow_nat {p : ℝ} (hp : 1 < p) :
    Summable (fun k : ℕ => 1 / (1 + (k : ℝ) ^ p)) := by
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    ((summable_nat_add_iff 1).2 (Real.summable_nat_rpow_inv.2 hp))
  · positivity
  · have hk : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hpos : 0 < ((k + 1 : ℕ) : ℝ) ^ p := Real.rpow_pos_of_pos hk p
    calc 1 / (1 + ((k + 1 : ℕ) : ℝ) ^ p) ≤ 1 / ((k + 1 : ℕ) : ℝ) ^ p :=
          one_div_le_one_div_of_le hpos (by linarith)
      _ = (((k + 1 : ℕ) : ℝ) ^ p)⁻¹ := one_div _

/-- Let `i` be a label of the cycle of length `N`, and let `g : ℕ → ℝ` be nonnegative and
summable. Then the sum of `g(d_N(i, j))` over the labels `j` is at most `2 ∑_k g(k)`.

The proof groups the labels by their cyclic distance to `i`. Each shell has at most two labels,
and the shells with radius at most `N / 2` are the only nonempty ones. -/
theorem sum_le_two_mul_tsum_cyclicIndexDistance (N : ℕ+) (i : Fin (N : ℕ)) {g : ℕ → ℝ}
    (hg0 : ∀ k, 0 ≤ g k) (hg : Summable g) :
    ∑ j : Fin (N : ℕ), g (Riesz1.cyclicIndexDistance N i j) ≤ 2 * ∑' k, g k := by
  have hmap : ∀ j ∈ (univ : Finset (Fin (N : ℕ))),
      Riesz1.cyclicIndexDistance N i j ∈ range ((N : ℕ) + 1) := by
    intro j _
    have := Riesz1.APG.cyclicIndexDistance_le_half (N := N) i j
    rw [mem_range]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  calc ∑ k ∈ range ((N : ℕ) + 1),
        ∑ j ∈ univ.filter (fun j => Riesz1.cyclicIndexDistance N i j = k),
          g (Riesz1.cyclicIndexDistance N i j)
      ≤ ∑ k ∈ range ((N : ℕ) + 1), 2 * g k := by
        refine sum_le_sum fun k _ => ?_
        rw [Finset.sum_congr rfl (fun j hj => congrArg g (mem_filter.1 hj).2), sum_const,
          nsmul_eq_mul]
        have hc : ((univ.filter fun j => Riesz1.cyclicIndexDistance N i j = k).card : ℝ) ≤ 2 := by
          exact_mod_cast card_cyclicShell_le_two i k
        exact mul_le_mul_of_nonneg_right hc (hg0 k)
    _ = 2 * ∑ k ∈ range ((N : ℕ) + 1), g k := by rw [mul_sum]
    _ ≤ 2 * ∑' k, g k := by
        gcongr
        exact Summable.sum_le_tsum _ (fun k _ => hg0 k) hg

/-- Let `p > 1`. For every cycle length `N` and every label `i`, the finite sum
`∑_j 1 / (1 + d_N(i, j)^p)` is at most `2 ∑_{k ∈ ℕ} 1 / (1 + k^p)`. The constant depends only on
`p`, not on `N` or `i`. -/
theorem sum_inv_one_add_cyclicIndexDistance_pow_le {p : ℝ} (hp : 1 < p) (N : ℕ+)
    (i : Fin (N : ℕ)) :
    ∑ j : Fin (N : ℕ), 1 / (1 + ((Riesz1.cyclicIndexDistance N i j : ℕ) : ℝ) ^ p) ≤
      2 * ∑' k : ℕ, 1 / (1 + (k : ℝ) ^ p) :=
  sum_le_two_mul_tsum_cyclicIndexDistance N i (g := fun k : ℕ => 1 / (1 + (k : ℝ) ^ p))
    (fun k => by positivity) (summable_inv_one_add_rpow_nat hp)

end Riesz2

end
