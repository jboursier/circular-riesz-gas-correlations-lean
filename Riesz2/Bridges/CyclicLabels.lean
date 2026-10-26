/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriGoodComparison
public import Riesz1.Rigidity.BlockAverageRepresentatives
public import Riesz2.Frozen.FiniteGapBlock
public import Riesz2.Frozen.GapVector
public import Riesz2.ToMathlib.CyclicDistance
public import Mathlib.Tactic

/-!
# Integer labels: paper labels, the integer cyclic distance and gap labels

The paper labels the particles `1, …, N`, while Riesz 1 labels them by `Fin N`, with the paper label
`i` at the index `i - 1`. `paperLabel N i` is the index of the paper label `i` for every integer
`i`, read modulo `N`.

The paper's integer cyclic distance `d_N` is `Riesz1.cyclicDist`. The lemmas below identify it with
the cyclic index distance of the two labels, and state its formula on the paper labels `1, …, N`.
The gap bridges express `Riesz2.gap` at an integer label through the gap vector at its residue.
-/

@[expose] public section

namespace Riesz2

/-- The index in `Fin N` of the paper label `i`, for an integer `i` read modulo `N`: the paper label
`1` has index `0`. -/
def paperLabel (N : ℕ+) (i : ℤ) : Fin (N : ℕ) := Riesz1.labelOf N (i - 1)

/-- The cyclic index distance of two integer labels is their integer cyclic distance
`Riesz1.cyclicDist`. -/
theorem cyclicIndexDistance_labelOf (N : ℕ+) (a b : ℤ) :
    ((Riesz1.cyclicIndexDistance N (Riesz1.labelOf N a) (Riesz1.labelOf N b) : ℕ) : ℤ) =
      Riesz1.cyclicDist N a b := by
  unfold Riesz1.cyclicIndexDistance Riesz1.cyclicDist
  have hx := (Riesz1.labelOf N a).isLt
  have hy := (Riesz1.labelOf N b).isLt
  have hle : Nat.dist (Riesz1.labelOf N a : ℕ) (Riesz1.labelOf N b : ℕ) ≤ (N : ℕ) := by
    unfold Nat.dist
    omega
  rw [Nat.cast_min, Nat.cast_sub hle, natCast_dist_eq_abs, Riesz1.APG.labelOf_val,
    Riesz1.APG.labelOf_val]

/-- The paper's integer distance: the cyclic index distance of the paper labels `i` and `j` is the
integer cyclic distance of `i - 1` and `j - 1`. -/
theorem cyclicIndexDistance_paperLabel (N : ℕ+) (i j : ℤ) :
    ((Riesz1.cyclicIndexDistance N (paperLabel N i) (paperLabel N j) : ℕ) : ℤ) =
      Riesz1.cyclicDist N (i - 1) (j - 1) :=
  cyclicIndexDistance_labelOf N (i - 1) (j - 1)

/-- For paper labels `1 ≤ i, j ≤ N`, the cyclic distance is `min (|i - j|, N - |i - j|)`. -/
theorem cyclicIndexDistance_paperLabel_of_mem (N : ℕ+) {i j : ℤ}
    (hi : 1 ≤ i ∧ i ≤ ((N : ℕ) : ℤ)) (hj : 1 ≤ j ∧ j ≤ ((N : ℕ) : ℤ)) :
    ((Riesz1.cyclicIndexDistance N (paperLabel N i) (paperLabel N j) : ℕ) : ℤ) =
      min |i - j| (((N : ℕ) : ℤ) - |i - j|) := by
  have h1 : (i - 1) % ((N : ℕ) : ℤ) = i - 1 := Int.emod_eq_of_lt (by omega) (by omega)
  have h2 : (j - 1) % ((N : ℕ) : ℤ) = j - 1 := Int.emod_eq_of_lt (by omega) (by omega)
  rw [cyclicIndexDistance_paperLabel]
  unfold Riesz1.cyclicDist
  rw [h1, h2, sub_sub_sub_cancel_right]

/-- The microscopic gap at an integer label is the gap vector entry at its residue:
`gap X j = gapVector X (labelOf N j)`. -/
theorem gap_eq_gapVector_labelOf {N : ℕ+} (X : Riesz1.Configuration N) (j : ℤ) :
    Riesz2.gap X j = Riesz2.gapVector X (Riesz1.labelOf N j) :=
  Riesz1.APG.gap_labelOf X j

/-- For `K ≤ N`, the `j`-th entry of the first `K` gaps is the `j`-th entry of the gap vector. -/
theorem finiteGapBlock_eq_gapVector {N K : ℕ+} (hK : (K : ℕ) ≤ (N : ℕ))
    (X : Riesz1.Configuration N) (j : Fin (K : ℕ)) :
    Riesz2.finiteGapBlock X j = Riesz2.gapVector X ⟨j.val, lt_of_lt_of_le j.isLt hK⟩ :=
  rfl

end Riesz2

end
