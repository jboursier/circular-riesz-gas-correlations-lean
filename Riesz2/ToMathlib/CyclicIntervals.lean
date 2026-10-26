/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.Window
public import Riesz1.Variance.APrioriGoodGradientCount
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic

/-!
# Cyclic intervals of labels

For an integer `a` and a length `r : ℕ`, the cyclic interval `cyclicInterval N a r` is the set of
labels `a, a + 1, …, a + r - 1` reduced modulo `N`. The label map is `Riesz1.labelOf`, which is
used as it stands, so the labels are the Riesz 1 indices. The paper's interval `I_{i,r}` with
labels `1, …, N` is `cyclicInterval N (i - 1) r`.

The interval has exactly `r` labels when `r ≤ N` (`card_cyclicInterval`). Its length-one case is
the singleton of `a` (`cyclicInterval_one`), and its full-cycle case is the whole label set
(`cyclicInterval_full`).
-/

@[expose] public section

open Finset

namespace Riesz2

variable {N : ℕ+}

/-- The cyclic interval of length `r` starting at the integer label `a`: the residues modulo `N`
of `a, a + 1, …, a + r - 1`. -/
def cyclicInterval (N : ℕ+) (a : ℤ) (r : ℕ) : Finset (Fin (N : ℕ)) :=
  (range r).image fun k : ℕ => Riesz1.labelOf N (a + k)

/-- A label lies in the cyclic interval when it is the residue of some `a + k` with `k < r`. -/
theorem mem_cyclicInterval {a : ℤ} {r : ℕ} {j : Fin (N : ℕ)} :
    j ∈ cyclicInterval N a r ↔ ∃ k < r, Riesz1.labelOf N (a + k) = j := by
  simp [cyclicInterval]

/-- The cyclic interval of length zero is empty. -/
theorem cyclicInterval_zero (a : ℤ) : cyclicInterval N a 0 = ∅ := by
  simp [cyclicInterval]

/-- The cyclic interval of length one is the label of `a`. -/
theorem cyclicInterval_one (a : ℤ) : cyclicInterval N a 1 = {Riesz1.labelOf N a} := by
  simp [cyclicInterval]

/-- For `r ≤ N` the labels `a, …, a + r - 1` are distinct, so the cyclic interval has `r`
labels. -/
theorem card_cyclicInterval (a : ℤ) {r : ℕ} (hr : r ≤ N) :
    (cyclicInterval N a r).card = r := by
  unfold cyclicInterval
  rw [card_image_of_injOn, card_range]
  intro k hk k' hk' h
  simp only [Finset.coe_range, Set.mem_Iio] at hk hk'
  simp only at h
  have hdvd : ((N : ℕ) : ℤ) ∣ (k' : ℤ) - k := by
    have := Riesz1.dvd_of_labelOf_eq N h
    rwa [show a + (k' : ℤ) - (a + k) = (k' : ℤ) - k by ring] at this
  have habs : |(k' : ℤ) - k| < ((N : ℕ) : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  have := Int.eq_zero_of_abs_lt_dvd hdvd habs
  omega

/-- The cyclic interval of length `N` is the whole label set. -/
theorem cyclicInterval_full (a : ℤ) : cyclicInterval N a N = univ := by
  apply Finset.eq_univ_of_card
  rw [card_cyclicInterval a le_rfl, Fintype.card_fin]

end Riesz2

end
