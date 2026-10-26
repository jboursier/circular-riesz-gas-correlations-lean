/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.RieszExponent
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Tactic

/-!
# The cutoff degree of Section 5

The integer prescribed in Lemma 5.4 of the paper is the smallest integer
`m` with `m * (1 - s/2) > 2`. Both physical comparison arguments use this
degree, including at the strict boundary `s = 2/3`.
-/

@[expose] public section
noncomputable section

namespace Riesz2

/-- The smallest positive integer prescribed in Lemma 5.4 of the paper. -/
def paperReferenceCutoffExponent (s : Riesz1.RieszExponent) : ℕ+ :=
  ⟨⌊2 / (1 - s.val / 2)⌋₊ + 1, Nat.succ_pos _⟩

/-- Minimality of the degree in Lemma 5.4 of the paper, including the
strict inequality when the quotient is itself an integer. -/
theorem paperReferenceCutoffExponent_le_iff (s : Riesz1.RieszExponent) (k : ℕ) :
    (paperReferenceCutoffExponent s : ℕ) ≤ k ↔ 2 < (k : ℝ) * (1 - s.val/2) := by
  have hd : 0 < 1 - s.val/2 := by linarith [s.property.2]
  change ⌊2 / (1 - s.val/2)⌋₊ + 1 ≤ k ↔ _
  rw [Nat.add_one_le_iff, Nat.floor_lt (by positivity : 0 ≤ 2 / (1 - s.val/2)),
    div_lt_iff₀ hd]

/-- The selected degree satisfies the strict requirement of Lemma 5.4
of the paper. -/
theorem paperReferenceCutoffExponent_large (s : Riesz1.RieszExponent) :
    2 < (paperReferenceCutoffExponent s : ℝ) * (1 - s.val/2) :=
  (paperReferenceCutoffExponent_le_iff s _).mp le_rfl

/-- Minimality among all integers, as stated in Lemma 5.4 of the paper.
An integer satisfying the strict inequality is automatically nonnegative. -/
theorem paperReferenceCutoffExponent_minimal (s : Riesz1.RieszExponent) (k : ℤ)
    (hk : 2 < (k : ℝ) * (1 - s.val/2)) :
    ((paperReferenceCutoffExponent s : ℕ) : ℤ) ≤ k := by
  have hd : 0 < 1 - s.val/2 := by linarith [s.property.2]
  have hk0 : 0 ≤ k := by
    by_contra h
    have hkR : (k : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge h))
    have hh := mul_nonpos_of_nonpos_of_nonneg hkR hd.le
    linarith
  have he : (k.toNat : ℝ) = (k : ℝ) := by
    exact_mod_cast (Int.toNat_of_nonneg hk0)
  have hn : 2 < (k.toNat : ℝ) * (1 - s.val/2) := by
    simpa only [he] using hk
  have hh := (paperReferenceCutoffExponent_le_iff s k.toNat).mpr hn
  have hi : ((paperReferenceCutoffExponent s : ℕ) : ℤ) ≤ (k.toNat : ℤ) := by
    exact_mod_cast hh
  simpa only [Int.toNat_of_nonneg hk0] using hi

/-- The literal smallest-integer statement of Lemma 5.4 of the paper. -/
theorem paperReferenceCutoffExponent_isLeast (s : Riesz1.RieszExponent) :
    IsLeast {k : ℤ | 2 < (k : ℝ) * (1 - s.val/2)}
      ((paperReferenceCutoffExponent s : ℕ) : ℤ) := by
  constructor
  · simpa only [Set.mem_ofPred_eq, Int.cast_natCast] using
      paperReferenceCutoffExponent_large s
  · intro k hk
    exact paperReferenceCutoffExponent_minimal s k hk

/-- The degree of Lemma 5.4 of the paper is at least three. -/
theorem paperReferenceCutoffExponent_ge_three (s : Riesz1.RieszExponent) :
    3 ≤ (paperReferenceCutoffExponent s : ℕ) := by
  by_contra h
  have hle : (paperReferenceCutoffExponent s : ℕ) ≤ 2 := by omega
  have hh := (paperReferenceCutoffExponent_le_iff s 2).mp hle
  norm_num at hh
  linarith [s.property.1]

/-- The degree of Lemma 5.4 of the paper is at most four. -/
theorem paperReferenceCutoffExponent_le_four (s : Riesz1.RieszExponent) :
    (paperReferenceCutoffExponent s : ℕ) ≤ 4 := by
  apply (paperReferenceCutoffExponent_le_iff s 4).mpr
  norm_num
  linarith [s.property.2]

/-- Below `s = 2/3`, the degree of Lemma 5.4 of the paper is three. -/
theorem paperReferenceCutoffExponent_eq_three (s : Riesz1.RieszExponent)
    (hs : s.val < 2/3) : paperReferenceCutoffExponent s = 3 := by
  apply PNat.coe_injective
  apply Nat.le_antisymm _ (paperReferenceCutoffExponent_ge_three s)
  apply (paperReferenceCutoffExponent_le_iff s 3).mpr
  norm_num
  linarith

/-- At and above `s = 2/3`, the degree of Lemma 5.4 of the paper is four. -/
theorem paperReferenceCutoffExponent_eq_four (s : Riesz1.RieszExponent)
    (hs : 2/3 ≤ s.val) : paperReferenceCutoffExponent s = 4 := by
  apply PNat.coe_injective
  apply Nat.le_antisymm (paperReferenceCutoffExponent_le_four s)
  by_contra h
  have hle : (paperReferenceCutoffExponent s : ℕ) ≤ 3 := by omega
  have hh := (paperReferenceCutoffExponent_le_iff s 3).mp hle
  norm_num at hh
  linarith

/-- The small forcing threshold in the proof of Proposition 5.18 and the full-cycle
branch of Theorem 1 of the paper. -/
def paperCutoffThreshold (s : Riesz1.RieszExponent) : ℝ :=
  1 / (4 * ((paperReferenceCutoffExponent s : ℝ) + 1))

/-- Positivity of the forcing threshold used in Proposition 5.18 of the paper. -/
theorem paperCutoffThreshold_pos (s : Riesz1.RieszExponent) :
    0 < paperCutoffThreshold s := by
  unfold paperCutoffThreshold
  positivity

/-- The forcing reduction in Proposition 5.18 of the paper implies the exponent
bound used to fit the powered cutoff inside a quarter of the reference cycle. -/
theorem paperCutoffThreshold_mul_degree_le_half (s : Riesz1.RieszExponent)
    {ε : ℝ} (hε : 0 ≤ ε) (hsmall : ε ≤ paperCutoffThreshold s) :
    ε * (paperReferenceCutoffExponent s : ℝ) ≤ 1/2 := by
  have hd : 0 < 4 * ((paperReferenceCutoffExponent s : ℝ) + 1) := by positivity
  have ht := (le_div_iff₀ hd).mp hsmall
  nlinarith

end Riesz2
