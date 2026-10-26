/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.WeightedL2Interpolation
public import Riesz2.ToMathlib.RpowPartialSums
public import Riesz2.ToMathlib.PowerTailBounds
public import Riesz2.ToMathlib.CyclicDistance
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Tactic

/-!
# Finite sums and losses for the cyclic weights

See the proof of Lemma 5.13 in the paper, with the weights
`W_ρ = diag(r_i^ρ)` and the norms of Subsection 5.4. The weight radius of the label `i`
about `i₀` is `r_i = 1 + d_m(i, i₀)`, where `d_m` is the cyclic distance
`Riesz1.cyclicIndexDistance`.

The theorem `global_sums` combines cyclic shell sums, interpolation of
weighted norms, the logarithmic bound, and the exponential bound used in
the proof of Lemma 5.13.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset Set
open scoped ENNReal

namespace Riesz2

/-- The radius `r_i = 1 + d_m(i, i₀)` of the weight `W_ρ` of Subsection 5.4, on the cycle
of length `N`. -/
def weightRadius (N : ℕ+) (i i₀ : Fin (N : ℕ)) : ℝ :=
  1 + (Riesz1.cyclicIndexDistance N i i₀ : ℝ)

/-- The weighted norm `‖W_ρ f‖₂` of Subsection 5.4, for the diagonal weight
`W_ρ = diag(r_i^ρ)` with `r_i = 1 + d_m(i, i₀)`, on vector-valued functions `f`. -/
def weightedRadiusNorm {α : Type*} [MeasurableSpace α] (ν : Measure α) (N : ℕ+)
    (i₀ : Fin (N : ℕ)) (ρ : ℝ) (f : α → Fin (N : ℕ) → ℝ) : ℝ≥0∞ :=
  weightedNorm ν (fun i => weightRadius N i i₀) ρ f

/-- The cyclic distance is symmetric. -/
theorem cyclicIndexDistance_comm' (N : ℕ+) (i j : Fin (N : ℕ)) :
    Riesz1.cyclicIndexDistance N i j = Riesz1.cyclicIndexDistance N j i := by
  simp only [Riesz1.cyclicIndexDistance, Nat.dist_comm]

/-- The weight radius, with the distance taken from the fixed label `i₀`. -/
theorem weightRadius_eq_comm (N : ℕ+) (i i₀ : Fin (N : ℕ)) :
    weightRadius N i i₀ = 1 + (Riesz1.cyclicIndexDistance N i₀ i : ℝ) := by
  unfold weightRadius
  rw [cyclicIndexDistance_comm']

/-- The weight radius is at least one. -/
theorem one_le_weightRadius (N : ℕ+) (i i₀ : Fin (N : ℕ)) : 1 ≤ weightRadius N i i₀ := by
  unfold weightRadius
  have : (0 : ℝ) ≤ (Riesz1.cyclicIndexDistance N i i₀ : ℝ) := Nat.cast_nonneg _
  linarith

/-- A sum of powers of the weights over the labels, restricted by a condition on the weights, is
a sum over the cyclic distances from `i₀`. -/
theorem sum_filter_weightRadius (N : ℕ+) (i₀ : Fin (N : ℕ)) (t : ℝ) (P : ℝ → Prop)
    [DecidablePred P] :
    ∑ i ∈ univ.filter (fun i => P (weightRadius N i i₀)), weightRadius N i i₀ ^ (-t) =
      ∑ j : Fin (N : ℕ), (fun k : ℕ => if P (1 + (k : ℝ)) then (1 + (k : ℝ)) ^ (-t) else 0)
        (Riesz1.cyclicIndexDistance N i₀ j) := by
  rw [sum_filter]
  refine sum_congr rfl fun j _ => ?_
  rw [weightRadius_eq_comm]

/-- For `R ≥ 1` and every real `t`, the sum over the labels with `r_i ≤ R` is at most twice the
partial sum of `(1 + k)^(-t)` over `k < ⌊R⌋₊`. -/
theorem sum_weightRadius_le_range (N : ℕ+) (i₀ : Fin (N : ℕ)) {t R : ℝ} (hR : 1 ≤ R) :
    ∑ i ∈ univ.filter (fun i => weightRadius N i i₀ ≤ R), weightRadius N i i₀ ^ (-t) ≤
      2 * ∑ k ∈ range ⌊R⌋₊, (1 + (k : ℝ)) ^ (-t) := by
  rw [sum_filter_weightRadius N i₀ t (fun x => x ≤ R)]
  set g : ℕ → ℝ := fun k => if 1 + (k : ℝ) ≤ R then (1 + (k : ℝ)) ^ (-t) else 0 with hg
  have hg0 : ∀ k, 0 ≤ g k := fun k => by
    simp only [hg]
    split_ifs
    · exact Real.rpow_nonneg (by positivity) _
    · exact le_rfl
  have hfin : ∀ k ∉ range ⌊R⌋₊, g k = 0 := by
    intro k hk
    have hk' : ⌊R⌋₊ ≤ k := by
      simpa using hk
    have hlt : R < 1 + (k : ℝ) := by
      have h1 : (⌊R⌋₊ : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk'
      have h2 := Nat.lt_floor_add_one R
      linarith
    simp [hg, not_le.2 hlt]
  have hsum : Summable g := summable_of_ne_finset_zero hfin
  have htsum : ∑' k : ℕ, g k = ∑ k ∈ range ⌊R⌋₊, (1 + (k : ℝ)) ^ (-t) := by
    rw [tsum_eq_sum hfin]
    refine sum_congr rfl fun k hk => ?_
    have hk' : k < ⌊R⌋₊ := Finset.mem_range.1 hk
    have hK : ((⌊R⌋₊ : ℕ) : ℝ) ≤ R := Nat.floor_le (by linarith)
    have hkK : (k : ℝ) + 1 ≤ (⌊R⌋₊ : ℝ) := by
      have : k + 1 ≤ ⌊R⌋₊ := hk'
      exact_mod_cast this
    have hcond : 1 + (k : ℝ) ≤ R := by linarith
    simp [hg, hcond]
  have hbound := sum_le_two_mul_tsum_cyclicIndexDistance N i₀ hg0 hsum
  refine hbound.trans ?_
  rw [htsum]

/-- The sum over the labels with `R ≤ r_i`, for `t > 1`, is at most `2 (1 + 1/(t-1)) R^(1-t)`
through the cyclic shells and the tail bound of `RpowPartialSums`. -/
theorem sum_weightRadius_tail_le (N : ℕ+) (i₀ : Fin (N : ℕ)) {t R : ℝ} (ht : 1 < t)
    (hR : 1 ≤ R) :
    ∑ i ∈ univ.filter (fun i => R ≤ weightRadius N i i₀), weightRadius N i i₀ ^ (-t) ≤
      2 * (1 + 1 / (t - 1)) * R ^ (1 - t) := by
  rw [sum_filter_weightRadius N i₀ t (fun x => R ≤ x)]
  have hg0 : ∀ k : ℕ, 0 ≤ (if R ≤ 1 + (k : ℝ) then (1 + (k : ℝ)) ^ (-t) else 0) := fun k => by
    split_ifs
    · exact Real.rpow_nonneg (by positivity) _
    · exact le_rfl
  have hsum : Summable fun k : ℕ => (if R ≤ 1 + (k : ℝ) then (1 + (k : ℝ)) ^ (-t) else 0) := by
    refine Summable.of_nonneg_of_le hg0 (fun k => ?_) (summable_one_add_rpow_neg ht)
    split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (by positivity) _
  have hbound := sum_le_two_mul_tsum_cyclicIndexDistance N i₀ hg0 hsum
  refine hbound.trans ?_
  have htail := tsum_tail_indicator_le ht hR
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  calc 2 * ∑' k : ℕ, (if R ≤ 1 + (k : ℝ) then (1 + (k : ℝ)) ^ (-t) else 0)
      ≤ 2 * ((1 + 1 / (t - 1)) * R ^ (1 - t)) := mul_le_mul_of_nonneg_left htail h2
    _ = 2 * (1 + 1 / (t - 1)) * R ^ (1 - t) := by ring

/-- The floor `⌊R⌋₊` of `R ≥ 1` is at least one and at most `R`. -/
theorem one_le_floor_and_floor_le {R : ℝ} (hR : 1 ≤ R) :
    1 ≤ ⌊R⌋₊ ∧ ((⌊R⌋₊ : ℕ) : ℝ) ≤ R :=
  ⟨Nat.le_floor (by exact_mod_cast hR), Nat.floor_le (by linarith)⟩

/-- Part `t < 1` of the cyclic shell bound: for `0 < t < 1` and `R ≥ 1`, the sum over the labels
with `r_i ≤ R` is at most `2 / (1 - t) * R^(1 - t)`. -/
theorem sum_weightRadius_le_of_lt_one (N : ℕ+) (i₀ : Fin (N : ℕ)) {t R : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) (hR : 1 ≤ R) :
    ∑ i ∈ univ.filter (fun i => weightRadius N i i₀ ≤ R), weightRadius N i i₀ ^ (-t) ≤
      2 / (1 - t) * R ^ (1 - t) := by
  obtain ⟨hK, hKR⟩ := one_le_floor_and_floor_le hR
  have h1 := sum_range_one_add_rpow_le_of_lt_one ht0 ht1 hK
  have h2 : ((⌊R⌋₊ : ℕ) : ℝ) ^ (1 - t) ≤ R ^ (1 - t) :=
    Real.rpow_le_rpow (by positivity) hKR (by linarith)
  refine (sum_weightRadius_le_range N i₀ hR).trans ?_
  have hpos : (0 : ℝ) < 1 - t := by linarith
  calc 2 * ∑ k ∈ range ⌊R⌋₊, (1 + (k : ℝ)) ^ (-t)
      ≤ 2 * ((((⌊R⌋₊ : ℕ) : ℝ)) ^ (1 - t) / (1 - t)) :=
        mul_le_mul_of_nonneg_left h1 (by norm_num)
    _ ≤ 2 * (R ^ (1 - t) / (1 - t)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h2 hpos.le) (by norm_num)
    _ = 2 / (1 - t) * R ^ (1 - t) := by ring

/-- Part `t = 1` of the cyclic shell bound: the sum over `r_i ≤ R` is at most
`2 (1 + 1/log 2) log(2R)`. -/
theorem sum_weightRadius_le_of_one (N : ℕ+) (i₀ : Fin (N : ℕ)) {R : ℝ} (hR : 1 ≤ R) :
    ∑ i ∈ univ.filter (fun i => weightRadius N i i₀ ≤ R), weightRadius N i i₀ ^ (-(1 : ℝ)) ≤
      2 * (1 + 1 / Real.log 2) * Real.log (2 * R) := by
  obtain ⟨hK, hKR⟩ := one_le_floor_and_floor_le hR
  have hK' : (0 : ℝ) < ((⌊R⌋₊ : ℕ) : ℝ) := by exact_mod_cast hK
  have hpartial : ∑ k ∈ range ⌊R⌋₊, (1 + (k : ℝ)) ^ (-(1 : ℝ)) ≤
      1 + Real.log ((⌊R⌋₊ : ℕ) : ℝ) := by
    simp only [Real.rpow_neg_one]
    exact sum_range_one_add_inv_le_one_add_log
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL2 : Real.log 2 ≤ Real.log (2 * R) := Real.log_le_log (by norm_num) (by linarith)
  have hlogK : Real.log ((⌊R⌋₊ : ℕ) : ℝ) ≤ Real.log (2 * R) :=
    Real.log_le_log hK' (by linarith)
  have hone : 1 ≤ Real.log (2 * R) / Real.log 2 := (one_le_div hlog2).2 hL2
  refine (sum_weightRadius_le_range N i₀ hR).trans ?_
  have hsplit : (1 + 1 / Real.log 2) * Real.log (2 * R) =
      Real.log (2 * R) + Real.log (2 * R) / Real.log 2 := by ring
  have key : 1 + Real.log ((⌊R⌋₊ : ℕ) : ℝ) ≤ (1 + 1 / Real.log 2) * Real.log (2 * R) := by
    rw [hsplit]
    linarith
  calc 2 * ∑ k ∈ range ⌊R⌋₊, (1 + (k : ℝ)) ^ (-(1 : ℝ))
      ≤ 2 * (1 + Real.log ((⌊R⌋₊ : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left hpartial (by norm_num)
    _ ≤ 2 * ((1 + 1 / Real.log 2) * Real.log (2 * R)) :=
        mul_le_mul_of_nonneg_left key (by norm_num)
    _ = 2 * (1 + 1 / Real.log 2) * Real.log (2 * R) := by ring

/-- Part `t > 1` of the cyclic shell bound: the sum over `r_i ≤ R` is at most the full series
`2 ∑_k (1 + k)^(-t)`. -/
theorem sum_weightRadius_le_of_gt_one (N : ℕ+) (i₀ : Fin (N : ℕ)) {t R : ℝ} (ht : 1 < t)
    (hR : 1 ≤ R) :
    ∑ i ∈ univ.filter (fun i => weightRadius N i i₀ ≤ R), weightRadius N i i₀ ^ (-t) ≤
      2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-t) := by
  refine (sum_weightRadius_le_range N i₀ hR).trans ?_
  exact mul_le_mul_of_nonneg_left (sum_range_one_add_rpow_le_tsum ht _) (by norm_num)

/-- The interpolation part of the proof of Lemma 5.13, for the weights `r_i = 1 + d_m(i, i₀)`. -/
theorem weightedRadiusNorm_le_mul_rpow {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (N : ℕ+) (i₀ : Fin (N : ℕ)) {f : α → Fin (N : ℕ) → ℝ}
    (hf : ∀ i, Measurable fun a => f a i) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : 0 < v) :
    weightedRadiusNorm ν N i₀ u f ≤
      weightedRadiusNorm ν N i₀ 0 f ^ (1 - u / v) * weightedRadiusNorm ν N i₀ v f ^ (u / v) :=
  weightedNorm_le_mul_rpow ν (fun i => by linarith [one_le_weightRadius N i i₀]) hf hu huv hv

/-- Part `t > 1` of the tail bound, with the constant `2 (1 + 1/(t-1))`. -/
theorem sum_weightRadius_tail_le_constant (N : ℕ+) (i₀ : Fin (N : ℕ)) {t R : ℝ} (ht : 1 < t)
    (hR : 1 ≤ R) :
    ∑ i ∈ univ.filter (fun i => R ≤ weightRadius N i i₀), weightRadius N i i₀ ^ (-t) ≤
      2 * (1 + 1 / (t - 1)) * R ^ (1 - t) :=
  sum_weightRadius_tail_le N i₀ ht hR

/-- The logarithmic bound of the proof of Lemma 5.13: for `s ∈ (0,1)`, `D, ε > 0` and `A ≥ 0`,
`log(2m)^A ≤ C n^(Dε)` whenever `2 ≤ m ≤ 2 n^(1/2 + 1/s)` and `n ≥ 2`. -/
theorem log_bound_global (s D A ε : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hD : 0 < D) (hA : 0 ≤ A)
    (hε : 0 < ε) :
    ∃ C : ℝ, ∀ n m : ℕ, 2 ≤ n → 2 ≤ m → (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s) →
      Real.log (2 * (m : ℝ)) ^ A ≤ C * (n : ℝ) ^ (D * ε) := by
  set K₂ : ℝ := 1 / 2 + 1 / s with hK₂
  have hK₂pos : 0 < K₂ := by positivity
  set η : ℝ := D * ε / (A + 1) with hη
  have hηpos : 0 < η := by positivity
  set L : ℝ := Real.log 4 + K₂ / η with hL
  have hL0 : 0 ≤ L := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have : 0 ≤ K₂ / η := by positivity
    linarith
  refine ⟨L ^ A, fun n m hn hm hmn => ?_⟩
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hnη : (1 : ℝ) ≤ (n : ℝ) ^ η := Real.one_le_rpow hn1 hηpos.le
  have h2m : Real.log (2 * (m : ℝ)) ≤ Real.log 4 + K₂ * Real.log n := by
    have hpos : (0 : ℝ) < 2 * (m : ℝ) := by linarith
    have hle : 2 * (m : ℝ) ≤ 4 * (n : ℝ) ^ K₂ := by linarith
    calc Real.log (2 * (m : ℝ)) ≤ Real.log (4 * (n : ℝ) ^ K₂) := Real.log_le_log hpos hle
      _ = Real.log 4 + K₂ * Real.log n := by
        rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hn0 _).ne', Real.log_rpow hn0]
  have hlogn : Real.log n ≤ (n : ℝ) ^ η / η := Real.log_le_rpow_div hn0.le hηpos
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hbase : Real.log (2 * (m : ℝ)) ≤ L * (n : ℝ) ^ η := by
    have hK : K₂ * Real.log n ≤ K₂ / η * (n : ℝ) ^ η := by
      calc K₂ * Real.log n ≤ K₂ * ((n : ℝ) ^ η / η) := mul_le_mul_of_nonneg_left hlogn hK₂pos.le
        _ = K₂ / η * (n : ℝ) ^ η := by ring
    calc Real.log (2 * (m : ℝ)) ≤ Real.log 4 + K₂ * Real.log n := h2m
      _ ≤ Real.log 4 * (n : ℝ) ^ η + K₂ / η * (n : ℝ) ^ η := by
        have := mul_le_mul_of_nonneg_left hnη hlog4
        linarith
      _ = L * (n : ℝ) ^ η := by rw [hL]; ring
  have hlog0 : 0 ≤ Real.log (2 * (m : ℝ)) := Real.log_nonneg (by linarith)
  calc Real.log (2 * (m : ℝ)) ^ A ≤ (L * (n : ℝ) ^ η) ^ A :=
        Real.rpow_le_rpow hlog0 hbase hA
    _ = L ^ A * ((n : ℝ) ^ η) ^ A := Real.mul_rpow hL0 (Real.rpow_nonneg hn0.le _)
    _ = L ^ A * (n : ℝ) ^ (η * A) := by rw [← Real.rpow_mul hn0.le]
    _ ≤ L ^ A * (n : ℝ) ^ (D * ε) := by
        have hexp : η * A ≤ D * ε := by
          rw [hη, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
          nlinarith [mul_pos hD hε]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 hexp)
          (Real.rpow_nonneg hL0 _)

/-- The exponential bound of the proof of Lemma 5.13: for `c, δ > 0` and `A ≥ 0`, the bound
`n^A e^{-c n^δ} ≤ C e^{-c n^δ / 2}` holds for every real `n ≥ 2`. The constant `C` is the
factorial bound `q! / (c/2)^q` with `q ≥ A/δ`. -/
theorem exp_bound_global (c δ A : ℝ) (hc : 0 < c) (hδ : 0 < δ) (_hA : 0 ≤ A) :
    ∃ C : ℝ, ∀ n : ℝ, 2 ≤ n →
      n ^ A * Real.exp (-(c * n ^ δ)) ≤ C * Real.exp (-(c * n ^ δ / 2)) := by
  set b : ℝ := c / 2 with hb
  have hbpos : 0 < b := by positivity
  set p : ℝ := A / δ with hp
  set q : ℕ := ⌈p⌉₊ with hq
  have hpq : p ≤ (q : ℝ) := Nat.le_ceil p
  refine ⟨(q.factorial : ℝ) / b ^ q, fun n hn => ?_⟩
  have hn0 : 0 < n := by linarith
  set y : ℝ := n ^ δ with hy
  have hy1 : 1 ≤ y := Real.one_le_rpow (by linarith) hδ.le
  have hy0 : 0 < y := by linarith
  have hnA : n ^ A = y ^ p := by
    rw [hy, hp, ← Real.rpow_mul hn0.le]
    congr 1
    field_simp
  -- `exp(-(b y)) ≤ q! / (b y)^q`, from `(b y)^q / q! ≤ exp (b y)`.
  have hexp : Real.exp (-(b * y)) ≤ (q.factorial : ℝ) / (b * y) ^ q := by
    have h1 : (b * y) ^ q / (q.factorial : ℝ) ≤ Real.exp (b * y) :=
      Real.pow_div_factorial_le_exp (b * y) (by positivity) q
    rw [Real.exp_neg]
    calc (Real.exp (b * y))⁻¹ ≤ ((b * y) ^ q / (q.factorial : ℝ))⁻¹ :=
          inv_anti₀ (by positivity) h1
      _ = (q.factorial : ℝ) / (b * y) ^ q := by rw [inv_div]
  -- `y^p / y^q ≤ 1`, since `p ≤ q` and `y ≥ 1`.
  have hratio : y ^ p / y ^ q ≤ 1 := by
    have hsub : y ^ p / y ^ q = y ^ (p - (q : ℝ)) := by
      rw [Real.rpow_sub hy0, Real.rpow_natCast]
    rw [hsub]
    exact Real.rpow_le_one_of_one_le_of_nonpos hy1 (by linarith)
  have hmain : y ^ p * Real.exp (-(b * y)) ≤ (q.factorial : ℝ) / b ^ q := by
    calc y ^ p * Real.exp (-(b * y)) ≤ y ^ p * ((q.factorial : ℝ) / (b * y) ^ q) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = ((q.factorial : ℝ) / b ^ q) * (y ^ p / y ^ q) := by
          rw [mul_pow]
          field_simp
      _ ≤ ((q.factorial : ℝ) / b ^ q) * 1 :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = (q.factorial : ℝ) / b ^ q := mul_one _
  have e1 : Real.exp (-(c * y)) = Real.exp (-(b * y)) * Real.exp (-(b * y)) := by
    rw [← Real.exp_add, hb]
    congr 1
    ring
  have e2 : -(c * y / 2) = -(b * y) := by
    rw [hb]
    ring
  rw [hnA, e1, e2]
  calc y ^ p * (Real.exp (-(b * y)) * Real.exp (-(b * y)))
      = (y ^ p * Real.exp (-(b * y))) * Real.exp (-(b * y)) := by ring
    _ ≤ ((q.factorial : ℝ) / b ^ q) * Real.exp (-(b * y)) :=
        mul_le_mul_of_nonneg_right hmain (Real.exp_nonneg _)

/-- Part `t > 0` of the proof of Lemma 5.13, the cyclic shell sums with a constant `C(t) > 0`. -/
theorem weight_sums_bound (t : ℝ) (ht : 0 < t) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ R : ℝ, 1 ≤ R → R ≤ ((N : ℕ) : ℝ) →
      ∀ i₀ : Fin (N : ℕ),
        (t < 1 → ∑ i ∈ univ.filter (fun i => weightRadius N i i₀ ≤ R),
            weightRadius N i i₀ ^ (-t) ≤ C * R ^ (1 - t)) ∧
        (t = 1 → ∑ i ∈ univ.filter (fun i => weightRadius N i i₀ ≤ R),
            weightRadius N i i₀ ^ (-t) ≤ C * Real.log (2 * R)) ∧
        (1 < t → ∑ i ∈ univ.filter (fun i => weightRadius N i i₀ ≤ R),
            weightRadius N i i₀ ^ (-t) ≤ C ∧
          ∑ i ∈ univ.filter (fun i => R ≤ weightRadius N i i₀),
            weightRadius N i i₀ ^ (-t) ≤ C * R ^ (1 - t)) := by
  rcases lt_trichotomy t 1 with h | h | h
  · refine ⟨2 / (1 - t), div_pos two_pos (by linarith), fun N _ R hR _ i₀ => ⟨fun _ =>
      sum_weightRadius_le_of_lt_one N i₀ ht h hR, fun h' => absurd h' (ne_of_lt h),
      fun h' => absurd h' (not_lt.2 h.le)⟩⟩
  · subst h
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    refine ⟨2 * (1 + 1 / Real.log 2), by positivity, fun N _ R hR _ i₀ => ⟨fun h' =>
      absurd h' (lt_irrefl _), fun _ => sum_weightRadius_le_of_one N i₀ hR,
      fun h' => absurd h' (lt_irrefl _)⟩⟩
  · set S : ℝ := ∑' k : ℕ, (1 + (k : ℝ)) ^ (-t) with hS
    have hS0 : 0 ≤ S := tsum_nonneg fun k => Real.rpow_nonneg (by positivity) _
    have hT : 0 < 1 / (t - 1) := by
      apply div_pos one_pos
      linarith
    refine ⟨2 * S + 2 * (1 + 1 / (t - 1)), by positivity, fun N _ R hR _ i₀ => ⟨fun h' =>
      absurd h' (not_lt.2 h.le), fun h' => absurd h' (ne_of_gt h), fun _ => ⟨?_, ?_⟩⟩⟩
    · have h1 := sum_weightRadius_le_of_gt_one N i₀ h hR
      linarith
    · have h1 := sum_weightRadius_tail_le_constant N i₀ h hR
      have hR0 : 0 ≤ R ^ (1 - t) := Real.rpow_nonneg (by linarith) _
      have h2 : 2 * (1 + 1 / (t - 1)) ≤ 2 * S + 2 * (1 + 1 / (t - 1)) := by linarith
      exact h1.trans (mul_le_mul_of_nonneg_right h2 hR0)

/-- The proof of Lemma 5.13: the finite sums
over the cyclic shells, the interpolation of the weighted norms, the logarithmic bound and the
exponential bound. The constants depend only on the displayed parameters. -/
theorem global_sums {α : Type*} [MeasurableSpace α] :
    (∀ t : ℝ, 0 < t → ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ R : ℝ, 1 ≤ R →
        R ≤ ((N : ℕ) : ℝ) → ∀ i₀ : Fin (N : ℕ),
          (t < 1 → ∑ i ∈ univ.filter (fun i => weightRadius N i i₀ ≤ R),
              weightRadius N i i₀ ^ (-t) ≤ C * R ^ (1 - t)) ∧
          (t = 1 → ∑ i ∈ univ.filter (fun i => weightRadius N i i₀ ≤ R),
              weightRadius N i i₀ ^ (-t) ≤ C * Real.log (2 * R)) ∧
          (1 < t → ∑ i ∈ univ.filter (fun i => weightRadius N i i₀ ≤ R),
              weightRadius N i i₀ ^ (-t) ≤ C ∧
            ∑ i ∈ univ.filter (fun i => R ≤ weightRadius N i i₀),
              weightRadius N i i₀ ^ (-t) ≤ C * R ^ (1 - t))) ∧
    (∀ (ν : Measure α) (N : ℕ+) (i₀ : Fin (N : ℕ)) (f : α → Fin (N : ℕ) → ℝ),
      (∀ i, Measurable fun a => f a i) → ∀ u v : ℝ, 0 ≤ u → u ≤ v → 0 < v →
        weightedRadiusNorm ν N i₀ u f ≤
          weightedRadiusNorm ν N i₀ 0 f ^ (1 - u / v) *
            weightedRadiusNorm ν N i₀ v f ^ (u / v)) ∧
    (∀ s D A ε : ℝ, 0 < s → s < 1 → 0 < D → 0 ≤ A → 0 < ε → ∃ C : ℝ, ∀ n m : ℕ,
        2 ≤ n → 2 ≤ m → (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s) →
          Real.log (2 * (m : ℝ)) ^ A ≤ C * (n : ℝ) ^ (D * ε)) ∧
    (∀ c δ A : ℝ, 0 < c → 0 < δ → 0 ≤ A → ∃ C : ℝ, ∀ n : ℝ, 2 ≤ n →
        n ^ A * Real.exp (-(c * n ^ δ)) ≤ C * Real.exp (-(c * n ^ δ / 2))) :=
  ⟨fun t ht => weight_sums_bound t ht,
    fun ν N i₀ _ hf _ _ hu huv hv => weightedRadiusNorm_le_mul_rpow ν N i₀ hf hu huv hv,
    fun s D A ε hs0 hs1 hD hA hε => log_bound_global s D A ε hs0 hs1 hD hA hε,
    fun c δ A hc hδ hA => exp_bound_global c δ A hc hδ hA⟩

end Riesz2

end
end
