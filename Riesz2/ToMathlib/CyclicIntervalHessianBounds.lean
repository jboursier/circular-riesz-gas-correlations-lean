/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.CyclicIntervalPairCount
public import Riesz2.ToMathlib.RpowPartialSums
public import Riesz2.Frozen.CyclicGapSum
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Interval Hessian sums

Counting and norm estimates for the interval representation in Subsection 5.1. The distance always retains the ambient cycle.
-/

public section
noncomputable section

open MeasureTheory Finset
open scoped BigOperators ENNReal Fin.NatCast

namespace Riesz2

/-- A coordinate basis vector sums to its membership indicator on a short
cyclic interval. No residue occurs twice when the length is at most the period. -/
theorem cyclicGapSum_single (N : ℕ+) (i a : Fin (N : ℕ)) {r : ℕ}
    (hr : r ≤ (N : ℕ)) :
    cyclicGapSum N i r (fun j => if j = a then 1 else 0) =
      if a ∈ cyclicIndexInterval N i r then 1 else 0 := by
  classical
  have hinj : Set.InjOn
      (fun t : ℕ => (⟨(i.val + t) % (N : ℕ), Nat.mod_lt _ N.pos⟩ : Fin (N : ℕ)))
      (range r) := by
    intro t ht u hu he
    have ht' : t < (N : ℕ) := lt_of_lt_of_le (mem_range.mp ht) hr
    have hu' : u < (N : ℕ) := lt_of_lt_of_le (mem_range.mp hu) hr
    have hfin : i + (t : Fin (N : ℕ)) = i + (u : Fin (N : ℕ)) := by
      apply Fin.ext
      simpa only [Fin.val_add, Fin.val_natCast, Nat.add_mod_mod] using congrArg Fin.val he
    have htu := congrArg Fin.val (add_left_cancel hfin)
    simpa only [Fin.val_natCast, Nat.mod_eq_of_lt ht', Nat.mod_eq_of_lt hu'] using htu
  unfold cyclicGapSum
  have he := sum_image (f := fun j : Fin (N : ℕ) => if j = a then (1 : ℝ) else 0) hinj
  rw [← he]
  change (∑ j ∈ cyclicIndexInterval N i r, if j = a then (1 : ℝ) else 0) = _
  simp

/-- The triangular pair count summed against `r^(-s-2)` gives the sharp
`(1+d)^(-s)` entry weight, uniformly in the truncation length. -/
theorem interval_pair_weight_le {s : ℝ} (hs : 0 < s) (d K : ℕ) :
    (∑ r : Fin K, ((r.val + 1 - d : ℕ) : ℝ) * (r.val + 1 : ℝ) ^ (-s - 2)) ≤
      (1 + 1 / s) * (1 + (d : ℝ)) ^ (-s) := by
  let g : ℕ → ℝ := fun k =>
    if 1 + (d : ℝ) ≤ 1 + (k : ℝ) then (1 + (k : ℝ)) ^ (-(1 + s)) else 0
  have hg0 : ∀ k, 0 ≤ g k := by intro k; dsimp [g]; split_ifs <;> positivity
  have hgs : Summable g := by
    refine Summable.of_nonneg_of_le hg0 (fun k => ?_)
      (summable_one_add_rpow_neg (by linarith : 1 < 1 + s))
    dsimp [g]
    split_ifs
    · exact le_rfl
    · positivity
  have hle (r : Fin K) :
      ((r.val + 1 - d : ℕ) : ℝ) * (r.val + 1 : ℝ) ^ (-s - 2) ≤ g r.val := by
    by_cases hd : d ≤ r.val
    · have hr : 0 < (r.val + 1 : ℝ) := by positivity
      have he : (r.val + 1 : ℝ) * (r.val + 1 : ℝ) ^ (-s - 2) =
          (1 + (r.val : ℝ)) ^ (-(1 + s)) := by
        conv_lhs => lhs; rw [← Real.rpow_one (r.val + 1 : ℝ)]
        rw [← Real.rpow_add hr]
        congr 1 <;> ring
      have hcast : ((r.val + 1 - d : ℕ) : ℝ) ≤ (r.val + 1 : ℝ) := by
        exact_mod_cast Nat.sub_le (r.val + 1) d
      dsimp [g]
      rw [ite_eq_left (by exact_mod_cast (show 1 + d ≤ 1 + r.val by omega))]
      exact (mul_le_mul_of_nonneg_right hcast (by positivity)).trans_eq he
    · have hz : r.val + 1 - d = 0 := by omega
      rw [hz, Nat.cast_zero, zero_mul]
      exact hg0 _
  calc
    _ ≤ ∑ r : Fin K, g r.val := sum_le_sum fun r _ => hle r
    _ = ∑ r ∈ range K, g r := by rw [sum_range]
    _ ≤ ∑' r : ℕ, g r := hgs.sum_le_tsum _ (fun r _ => hg0 r)
    _ ≤ (1 + 1 / s) * (1 + (d : ℝ)) ^ (-s) := by
      simpa only [g, show (1 + s) - 1 = s by ring,
        show (1 : ℝ) - (1 + s) = -s by ring] using
        (tsum_tail_indicator_le (by linarith : 1 < 1 + s)
          (show 1 ≤ 1 + (d : ℝ) from le_add_of_nonneg_right (Nat.cast_nonneg d)))

/-- Internal norm estimate for an interval matrix. The hypothesis is a norm
bound for its individual coefficients, not an additional physical assumption.
The spatial decay is a consequence of the exact cyclic containment count. -/
theorem interval_matrix_eLpNorm_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : ℕ+) {s q B : ℝ} (hs : 0 < s) (hq : 1 ≤ q)
    (hB : 0 ≤ B) (F : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → Ω → ℝ)
    (hF : ∀ i r, eLpNorm (F i r) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (B * (r.val + 1 : ℝ) ^ (-s - 2)))
    (a b : Fin (N : ℕ)) :
    eLpNorm (fun x => ∑ r : Fin ((N : ℕ) / 2), ∑ i : Fin (N : ℕ),
      if a ∈ cyclicIndexInterval N i (r.val + 1) ∧
        b ∈ cyclicIndexInterval N i (r.val + 1) then F i r x else 0)
      (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal (B * (1 + 1 / s) *
          (1 + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-s)) := by
  classical
  have hqE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hq
  let w (i : Fin (N : ℕ)) (r : Fin ((N : ℕ) / 2)) : ℝ :=
    (if a ∈ cyclicIndexInterval N i (r.val + 1) then 1 else 0) *
      (if b ∈ cyclicIndexInterval N i (r.val + 1) then 1 else 0)
  have hw : ∀ i r, 0 ≤ w i r := by intro i r; dsimp [w]; positivity
  have he (r : Fin ((N : ℕ) / 2)) :
      (∑ i : Fin (N : ℕ), w i r) =
        ((r.val + 1 - Riesz1.cyclicIndexDistance N a b : ℕ) : ℝ) :=
    cyclicIndexInterval_pair_count N (by have := r.isLt; omega) a b
  have hi (i : Fin (N : ℕ)) (r : Fin ((N : ℕ) / 2)) :
      eLpNorm (fun x => if a ∈ cyclicIndexInterval N i (r.val + 1) ∧
        b ∈ cyclicIndexInterval N i (r.val + 1) then F i r x else 0)
        (ENNReal.ofReal q) μ ≤
          ENNReal.ofReal (w i r * (B * (r.val + 1 : ℝ) ^ (-s - 2))) := by
    by_cases ha : a ∈ cyclicIndexInterval N i (r.val + 1) <;>
      by_cases hb : b ∈ cyclicIndexInterval N i (r.val + 1)
    · simpa only [ha, hb, and_self, ↓reduceIte, w, one_mul] using hF i r
    all_goals simp [ha, hb, w]
  calc
    _ ≤ ∑ r : Fin ((N : ℕ) / 2), ∑ i : Fin (N : ℕ),
        eLpNorm (fun x => if a ∈ cyclicIndexInterval N i (r.val + 1) ∧
          b ∈ cyclicIndexInterval N i (r.val + 1) then F i r x else 0)
          (ENNReal.ofReal q) μ := by
      have ho := eLpNorm_sum_le (μ := μ) (p := ENNReal.ofReal q)
        (f := fun r x => ∑ i : Fin (N : ℕ),
          if a ∈ cyclicIndexInterval N i (r.val + 1) ∧
            b ∈ cyclicIndexInterval N i (r.val + 1) then F i r x else 0)
        (s := univ) hqE
      simp only [sum_fn] at ho
      refine ho.trans (sum_le_sum fun r _ => ?_)
      simpa only [sum_fn] using eLpNorm_sum_le (μ := μ) (p := ENNReal.ofReal q)
        (f := fun i x => if a ∈ cyclicIndexInterval N i (r.val + 1) ∧
          b ∈ cyclicIndexInterval N i (r.val + 1) then F i r x else 0)
        (s := univ) hqE
    _ ≤ ∑ r : Fin ((N : ℕ) / 2), ∑ i : Fin (N : ℕ),
        ENNReal.ofReal (w i r * (B * (r.val + 1 : ℝ) ^ (-s - 2))) :=
      sum_le_sum fun r _ => sum_le_sum fun i _ => hi i r
    _ = ENNReal.ofReal (B * ∑ r : Fin ((N : ℕ) / 2),
        ((r.val + 1 - Riesz1.cyclicIndexDistance N a b : ℕ) : ℝ) *
          (r.val + 1 : ℝ) ^ (-s - 2)) := by
      have hi' (r : Fin ((N : ℕ) / 2)) :
          (∑ i : Fin (N : ℕ), ENNReal.ofReal (w i r * (B * (r.val + 1 : ℝ) ^ (-s - 2)))) =
            ENNReal.ofReal (∑ i : Fin (N : ℕ), w i r * (B * (r.val + 1 : ℝ) ^ (-s - 2))) :=
        (ENNReal.ofReal_sum_of_nonneg (fun i _ =>
          mul_nonneg (hw i r) (mul_nonneg hB (by positivity)))).symm
      simp_rw [hi']
      rw [← ENNReal.ofReal_sum_of_nonneg (fun r _ =>
        sum_nonneg (fun i _ => mul_nonneg (hw i r) (mul_nonneg hB (by positivity))))]
      congr 1
      simp_rw [← sum_mul, he, mul_sum]
      apply sum_congr rfl
      intro r _
      ring
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (interval_pair_weight_le hs
          (Riesz1.cyclicIndexDistance N a b) ((N : ℕ) / 2)) hB

end Riesz2
