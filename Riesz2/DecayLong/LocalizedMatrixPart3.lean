/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.LocalizedMatrixPart2
public import Riesz2.Preliminaries.TruncatedCoercivity
public import Riesz2.ToMathlib.IntervalMatrixComparison

/-!
# Crossing reference estimates for localization

Quantitative reference-period comparison and boundary rows in the proof
of Proposition 5.15, using the period comparison from
`LocalizedMatrixPart2`.
-/

public section
noncomputable section

open MeasureTheory Finset Riesz2.IntervalBoundary
open scoped BigOperators Classical Fin.NatCast MatrixOrder

namespace Riesz2.LocalizedMatrix

/-- See the proof of Proposition 5.15 in the paper: sum the reference over its
lengths using the exact number of intervals containing the two labels.
The antipodal coefficient and the common cutoff are retained. -/
theorem reference_length_sum (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (K : ℕ) (i j : Fin (N : ℕ)) :
    2 * referenceIntervalMatrix s N hN K i j =
      ∑ r ∈ range ((N : ℕ) / 2),
        (if K ≤ r + 1 then
          (2 - if 2 * (r + 1) = (N : ℕ) then (1 : ℝ) else 0) *
            sampledSecondDifference s N hN (↑(r + 1) : Fin (N : ℕ)) else 0) *
          ((r + 1 - Riesz1.cyclicIndexDistance N i j : ℕ) : ℝ) := by
  rw [GlobalReferenceErrorInternal.reference_fin_lengths]
  simp_rw [mul_sum]
  rw [sum_comm]
  have he (r : Fin ((N : ℕ) / 2)) :
      (∑ k : Fin (N : ℕ), 2 *
        ((if K ≤ r.val + 1 then
          (1 - if 2 * (r.val + 1) = (N : ℕ) then (1 / 2 : ℝ) else 0) *
            sampledSecondDifference s N hN (↑(r.val + 1) : Fin (N : ℕ)) else 0) *
          (if i ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
          (if j ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0))) =
      (if K ≤ r.val + 1 then
        (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
          sampledSecondDifference s N hN (↑(r.val + 1) : Fin (N : ℕ)) else 0) *
        ((r.val + 1 - Riesz1.cyclicIndexDistance N i j : ℕ) : ℝ) := by
    have hcoef : 2 * (if K ≤ r.val + 1 then
        (1 - if 2 * (r.val + 1) = (N : ℕ) then (1 / 2 : ℝ) else 0) *
          sampledSecondDifference s N hN (↑(r.val + 1) : Fin (N : ℕ)) else 0) =
      (if K ≤ r.val + 1 then
        (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
          sampledSecondDifference s N hN (↑(r.val + 1) : Fin (N : ℕ)) else 0) := by
      split_ifs <;> ring
    simp_rw [mul_assoc]
    rw [← mul_sum, ← mul_sum, ← mul_assoc, hcoef,
      cyclicIndexInterval_pair_count N (by have := r.isLt; omega)]
  rw [sum_congr rfl (fun r _ => he r)]
  exact Fin.sum_univ_eq_sum_range (fun r : ℕ =>
    (if K ≤ r + 1 then
      (2 - if 2 * (r + 1) = (N : ℕ) then (1 : ℝ) else 0) *
        sampledSecondDifference s N hN (↑(r + 1) : Fin (N : ℕ)) else 0) *
      ((r + 1 - Riesz1.cyclicIndexDistance N i j : ℕ) : ℝ)) _

/-- See the proof of Proposition 5.15 in the paper: the ordered active distance
is independent of the ambient period when the block is shorter than a half-cycle. -/
theorem active_distance (N n : ℕ+) (hn : 2 * (n : ℕ) ≤ (N : ℕ))
    (i j : Fin (n : ℕ)) :
    Riesz1.cyclicIndexDistance N (i.castLE (by omega)) (j.castLE (by omega)) =
      Nat.dist i.val j.val := by
  simp only [Riesz1.cyclicIndexDistance, Fin.val_castLE]
  have hi := i.isLt
  have hj := j.isLt
  unfold Nat.dist
  omega

/-- Internal tail estimate in the proof of Proposition 5.15.
After counting starts, the coefficient envelope gains precisely one length
factor. The bound includes every remaining length, including the antipode. -/
theorem reference_length_tail_internal (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K L d : ℕ),
      1 ≤ L → L ≤ (N : ℕ) / 2 →
      |∑ r ∈ Ico L ((N : ℕ) / 2),
        (if K ≤ r + 1 then
          (2 - if 2 * (r + 1) = (N : ℕ) then (1 : ℝ) else 0) *
            sampledSecondDifference s N hN (↑(r + 1) : Fin (N : ℕ)) else 0) *
          ((r + 1 - d : ℕ) : ℝ)| ≤ C * (L : ℝ) ^ (-s.val) := by
  obtain ⟨C, hC, hb⟩ := BoundaryEntries.referenceWeight_bound s
  refine ⟨C * (1 + 1 / s.val), by positivity [s.property.1], ?_⟩
  intro N hN K L d hL hLN
  have hterm (r : ℕ) (hr : r < (N : ℕ) / 2) :
      |(if K ≤ r + 1 then
          (2 - if 2 * (r + 1) = (N : ℕ) then (1 : ℝ) else 0) *
            sampledSecondDifference s N hN (↑(r + 1) : Fin (N : ℕ)) else 0) *
          ((r + 1 - d : ℕ) : ℝ)| ≤ C * (r + 1 : ℝ) ^ (-(s.val + 1)) := by
    let t : Fin (N : ℕ) × Fin ((N : ℕ) / 2) := (0, ⟨r, hr⟩)
    have hcoef : (if K ≤ r + 1 then
        (2 - if 2 * (r + 1) = (N : ℕ) then (1 : ℝ) else 0) *
          sampledSecondDifference s N hN (↑(r + 1) : Fin (N : ℕ)) else 0) =
        BoundaryEntries.referenceWeight s N hN K t := by
      change _ = (if K ≤ r + 1 then
        2 * ((1 - if 2 * (r + 1) = (N : ℕ) then (1 / 2 : ℝ) else 0) *
          sampledSecondDifference s N hN (↑(r + 1) : Fin (N : ℕ))) else 0)
      split_ifs <;> ring
    rw [hcoef, abs_of_nonneg (mul_nonneg
      (BoundaryEntries.referenceWeight_nonneg s N hN K t) (by positivity))]
    calc
      _ ≤ (C * (r + 1 : ℝ) ^ (-s.val - 2)) * (r + 1 : ℝ) :=
        mul_le_mul (hb N hN K t) (by exact_mod_cast (Nat.sub_le (r + 1) d))
          (by positivity) (by positivity)
      _ = _ := by
        rw [mul_assoc, ← Real.rpow_add_one (by positivity : (r + 1 : ℝ) ≠ 0)]
        congr 2
        ring
  calc
    _ ≤ ∑ r ∈ Ico L ((N : ℕ) / 2), C * (r + 1 : ℝ) ^ (-(s.val + 1)) :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun r hr => hterm r (mem_Ico.mp hr).2)
    _ ≤ ∑ r ∈ range ((N : ℕ) / 2),
        if (L : ℝ) ≤ r + 1 then C * (r + 1 : ℝ) ^ (-(s.val + 1)) else 0 := by
      calc
        _ = ∑ r ∈ Ico L ((N : ℕ) / 2),
            if (L : ℝ) ≤ r + 1 then C * (r + 1 : ℝ) ^ (-(s.val + 1)) else 0 := by
          apply sum_congr rfl
          intro r hr
          rw [ite_eq_left (by exact_mod_cast (show L ≤ r + 1 by have := mem_Ico.mp hr; omega))]
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg
          (by intro r hr; exact mem_range.mpr (mem_Ico.mp hr).2)
          (fun r _ _ => by split_ifs <;> positivity)
    _ = C * ∑ r : Fin ((N : ℕ) / 2),
        if (L : ℝ) ≤ r.val + 1 then (r.val + 1 : ℝ) ^ (-(s.val + 1)) else 0 := by
      rw [Fin.sum_univ_eq_sum_range (fun r : ℕ =>
        if (L : ℝ) ≤ (r : ℝ) + 1 then ((r : ℝ) + 1) ^ (-(s.val + 1)) else 0)]
      simp only [mul_ite, mul_zero, mul_sum]
    _ ≤ C * ((1 + 1 / ((s.val + 1) - 1)) * (L : ℝ) ^ (1 - (s.val + 1))) :=
      mul_le_mul_of_nonneg_left
        (BoundaryEntries.finite_length_tail_internal (by linarith [s.property.1])
          (by exact_mod_cast hL) _) hC.le
    _ = _ := by rw [show (s.val + 1) - 1 = s.val by ring,
      show 1 - (s.val + 1) = -s.val by ring]; ring

/-- See the proof of Proposition 5.15 in the paper: comparison of the entire
truncated references at two periods, including all long and antipodal terms.
The cutoff is common and the constant precedes both periods and the block. -/
theorem reference_different_period (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m m₀ n₀ : ℕ+) (hm : 2 ≤ (m : ℕ))
      (hm₀ : 4 ≤ (m₀ : ℕ)) (hle : (m₀ : ℕ) ≤ (m : ℕ))
      (hn₀ : 2 * (n₀ : ℕ) < (m₀ : ℕ)) (K : ℕ) (i l : Fin (n₀ : ℕ)),
      |2 * referenceIntervalMatrix s m hm K (i.castLE (by omega)) (l.castLE (by omega)) -
        2 * referenceIntervalMatrix s m₀ (by omega) K
          (i.castLE (by omega)) (l.castLE (by omega))| ≤ C * (m₀ : ℝ) ^ (-s.val) := by
  obtain ⟨A, hA, ha⟩ := referenceWeight_different_period s
  obtain ⟨B, hB, hb⟩ := reference_length_tail_internal s
  refine ⟨A + 2 * B * (8 : ℝ) ^ s.val, by positivity, ?_⟩
  intro m m₀ n₀ hm hm₀ hle hn₀ K i l
  let L := (m₀ : ℕ) / 4
  let d := Nat.dist i.val l.val
  let q (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (r : ℕ) : ℝ :=
    (if K ≤ r + 1 then
      (2 - if 2 * (r + 1) = (N : ℕ) then (1 : ℝ) else 0) *
        sampledSecondDifference s N hN (↑(r + 1) : Fin (N : ℕ)) else 0) *
      ((r + 1 - d : ℕ) : ℝ)
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hLm : L ≤ (m : ℕ) / 2 := by dsimp [L]; omega
  have hLm₀ : L ≤ (m₀ : ℕ) / 2 := by dsimp [L]; omega
  have hshort : |(∑ r ∈ range L, q m hm r) -
      ∑ r ∈ range L, q m₀ (by omega) r| ≤ A * (m₀ : ℝ) ^ (-s.val) := by
    rw [← sum_sub_distrib]
    have hterm (r : ℕ) (hr : r ∈ range L) :
        |q m hm r - q m₀ (by omega) r| ≤
          A * (m₀ : ℝ) ^ (-s.val - 2) * (m₀ : ℝ) := by
      have hrL : r < L := mem_range.mp hr
      have hrhalf : 2 * (r + 1) < (m₀ : ℕ) := by dsimp [L] at hrL; omega
      have hridx : r < (m₀ : ℕ) / 2 := by omega
      have hcoef (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (hrN : r < (N : ℕ) / 2) :
          (if K ≤ r + 1 then
            (2 - if 2 * (r + 1) = (N : ℕ) then (1 : ℝ) else 0) *
              sampledSecondDifference s N hN (↑(r + 1) : Fin (N : ℕ)) else 0) =
            BoundaryEntries.referenceWeight s N hN K (0, ⟨r, hrN⟩) := by
        change _ = (if K ≤ r + 1 then
          2 * ((1 - if 2 * (r + 1) = (N : ℕ) then (1 / 2 : ℝ) else 0) *
            sampledSecondDifference s N hN (↑(r + 1) : Fin (N : ℕ))) else 0)
        split_ifs <;> ring
      dsimp only [q]
      rw [hcoef m hm (by omega), hcoef m₀ (by omega) hridx,
        ← sub_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (r + 1 - d : ℕ))]
      apply mul_le_mul
        (ha m m₀ hm (by omega) hle K 0 r (by have := m₀.pos; omega) hridx hrhalf)
        (by exact_mod_cast (show r + 1 - d ≤ (m₀ : ℕ) by omega)) (by positivity) (by positivity)
    calc
      _ ≤ ∑ r ∈ range L, A * (m₀ : ℝ) ^ (-s.val - 2) * (m₀ : ℝ) :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
      _ = (L : ℝ) * (A * (m₀ : ℝ) ^ (-s.val - 2) * (m₀ : ℝ)) := by
        rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ (m₀ : ℝ) * (A * (m₀ : ℝ) ^ (-s.val - 2) * (m₀ : ℝ)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast (show L ≤ (m₀ : ℕ) by dsimp [L]; omega))
          (by positivity)
      _ = _ := by
        have hp : (m₀ : ℝ) ^ (-s.val - 2) * (m₀ : ℝ) ^ (2 : ℝ) =
            (m₀ : ℝ) ^ (-s.val) := by
          rw [← Real.rpow_add (by positivity)]
          congr 1
          ring
        calc
          _ = A * ((m₀ : ℝ) ^ (-s.val - 2) * (m₀ : ℝ) ^ (2 : ℝ)) := by rw [Real.rpow_two]; ring
          _ = _ := by rw [hp]
  have htail₁ : |∑ r ∈ Ico L ((m : ℕ) / 2), q m hm r| ≤
      B * (L : ℝ) ^ (-s.val) := hb m hm K L d hL hLm
  have htail₂ : |∑ r ∈ Ico L ((m₀ : ℕ) / 2), q m₀ (by omega) r| ≤
      B * (L : ℝ) ^ (-s.val) := hb m₀ (by omega) K L d hL hLm₀
  have hscale : (L : ℝ) ^ (-s.val) ≤ (8 : ℝ) ^ s.val * (m₀ : ℝ) ^ (-s.val) := by
    have hLN : (m₀ : ℝ) ≤ 8 * (L : ℝ) := by
      exact_mod_cast (show (m₀ : ℕ) ≤ 8 * L by dsimp [L]; omega)
    have hp := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < m₀)
      hLN (by linarith [s.property.1] : -s.val ≤ 0)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) (by positivity)] at hp
    have hh := mul_le_mul_of_nonneg_left hp (by positivity : (0 : ℝ) ≤ (8 : ℝ) ^ s.val)
    have he : (8 : ℝ) ^ s.val * (8 : ℝ) ^ (-s.val) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 8), add_neg_cancel, Real.rpow_zero]
    rwa [← mul_assoc, he, one_mul] at hh
  rw [reference_length_sum, reference_length_sum, active_distance m n₀ (by omega),
    active_distance m₀ n₀ (by omega)]
  change |(∑ r ∈ range ((m : ℕ) / 2), q m hm r) -
    ∑ r ∈ range ((m₀ : ℕ) / 2), q m₀ (by omega) r| ≤ _
  rw [← sum_range_add_sum_Ico _ hLm, ← sum_range_add_sum_Ico _ hLm₀]
  have he := abs_add_le
    ((∑ r ∈ range L, q m hm r) - ∑ r ∈ range L, q m₀ (by omega) r)
    ((∑ r ∈ Ico L ((m : ℕ) / 2), q m hm r) - ∑ r ∈ Ico L ((m₀ : ℕ) / 2), q m₀ (by omega) r)
  have ht := abs_sub
    (∑ r ∈ Ico L ((m : ℕ) / 2), q m hm r)
    (∑ r ∈ Ico L ((m₀ : ℕ) / 2), q m₀ (by omega) r)
  have heq : (∑ r ∈ range L, q m hm r) + (∑ r ∈ Ico L ((m : ℕ) / 2), q m hm r) -
      ((∑ r ∈ range L, q m₀ (by omega) r) + (∑ r ∈ Ico L ((m₀ : ℕ) / 2), q m₀ (by omega) r)) =
      ((∑ r ∈ range L, q m hm r) - ∑ r ∈ range L, q m₀ (by omega) r) +
        ((∑ r ∈ Ico L ((m : ℕ) / 2), q m hm r) - ∑ r ∈ Ico L ((m₀ : ℕ) / 2), q m₀ (by omega) r) := by ring
  rw [heq]
  nlinarith only [he, ht, hshort, htail₁, htail₂,
    mul_le_mul_of_nonneg_left hscale hB.le]

/-- See the proof of Proposition 5.15 in the paper: the required crossing
reference period error. This includes the long intervals and antipodal
half-weight outside the retained-coefficient comparison. -/
theorem referenceCrossing_different_period (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m m₀ n₀ : ℕ+) (hm : 2 ≤ (m : ℕ))
      (hm₀ : 4 ≤ (m₀ : ℕ)) (hle : (m₀ : ℕ) ≤ (m : ℕ))
      (hn₀ : 2 * (n₀ : ℕ) < (m₀ : ℕ)) (K : ℕ) (i l : Fin (n₀ : ℕ)),
      |BoundaryEntries.referenceCrossing s m hm K n₀ (by omega) i l -
        BoundaryEntries.referenceCrossing s m₀ (by omega) K n₀ (by omega) i l| ≤
        C * ((m₀ : ℝ) ^ (-s.val) + (n₀ : ℝ) ^ 2 * (m₀ : ℝ) ^ (-s.val - 2)) := by
  obtain ⟨A, hA, ha⟩ := reference_different_period s
  obtain ⟨B, hB, hb⟩ := referenceInternal_different_period s
  refine ⟨A + B, by positivity, fun m m₀ n₀ hm hm₀ hle hn₀ K i l => ?_⟩
  have h₁ := ha m m₀ n₀ hm hm₀ hle hn₀ K i l
  have h₂ := hb m m₀ n₀ hm (by omega) hle hn₀ K i l
  have he₁ := BoundaryEntries.referenceInternal_add_crossing s m hm K n₀ (by omega) i l
  have he₂ := BoundaryEntries.referenceInternal_add_crossing s m₀ (by omega) K n₀ (by omega) i l
  have he : BoundaryEntries.referenceCrossing s m hm K n₀ (by omega) i l -
      BoundaryEntries.referenceCrossing s m₀ (by omega) K n₀ (by omega) i l =
      (2 * referenceIntervalMatrix s m hm K (i.castLE (by omega)) (l.castLE (by omega)) -
        2 * referenceIntervalMatrix s m₀ (by omega) K (i.castLE (by omega)) (l.castLE (by omega))) -
      (BoundaryEntries.referenceInternal s m hm K n₀ (by omega) i l -
        BoundaryEntries.referenceInternal s m₀ (by omega) K n₀ (by omega) i l) := by
    linarith only [he₁, he₂]
  rw [he]
  apply (abs_sub _ _).trans
  have hp : 0 ≤ (m₀ : ℝ) ^ (-s.val) := by positivity
  have hq : 0 ≤ (n₀ : ℝ) ^ 2 * (m₀ : ℝ) ^ (-s.val - 2) := by positivity
  nlinarith only [h₁, h₂, mul_nonneg hA.le hq, mul_nonneg hB.le hp]

/-- See the proof of Proposition 5.15 in the paper: at the chosen uncapped
period, both contributions to a reference crossing row have the required
boundary exponent. The loss from summing a row is exactly its square-root size. -/
theorem period_row_error_absorption (s : Riesz1.RieszExponent) (n₀ m₀ : ℕ+)
    (hscale : (n₀ : ℝ) ^ (1 / 2 + 1 / s.val) ≤ (m₀ : ℝ)) :
    Real.sqrt (n₀ : ℝ) * ((m₀ : ℝ) ^ (-s.val) +
      (n₀ : ℝ) ^ 2 * (m₀ : ℝ) ^ (-s.val - 2)) ≤
        2 * (n₀ : ℝ) ^ (-(1 + s.val) / 2) := by
  have hn : (0 : ℝ) < n₀ := by positivity
  have hn1 : (1 : ℝ) ≤ n₀ := by exact_mod_cast n₀.pos
  have hfirst : Real.sqrt (n₀ : ℝ) * (m₀ : ℝ) ^ (-s.val) ≤
      (n₀ : ℝ) ^ (-(1 + s.val) / 2) := by
    rw [Real.sqrt_eq_rpow]
    calc
      _ ≤ (n₀ : ℝ) ^ (1 / 2 : ℝ) *
          ((n₀ : ℝ) ^ (1 / 2 + 1 / s.val)) ^ (-s.val) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos
          (by positivity) hscale (by linarith [s.property.1])) (by positivity)
      _ = _ := by
        rw [← Real.rpow_mul hn.le, ← Real.rpow_add hn]
        congr 1
        field_simp [ne_of_gt s.property.1]
        ring
  have hsecond : Real.sqrt (n₀ : ℝ) *
      ((n₀ : ℝ) ^ 2 * (m₀ : ℝ) ^ (-s.val - 2)) ≤
        (n₀ : ℝ) ^ (-(1 + s.val) / 2) := by
    rw [Real.sqrt_eq_rpow]
    calc
      _ ≤ (n₀ : ℝ) ^ (1 / 2 : ℝ) *
          ((n₀ : ℝ) ^ (2 : ℝ) * ((n₀ : ℝ) ^ (1 / 2 + 1 / s.val)) ^ (-s.val - 2)) := by
        rw [Real.rpow_two]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos
            (by positivity) hscale (by linarith [s.property.1])) (by positivity)) (by positivity)
      _ = (n₀ : ℝ) ^ (1 / 2 + 2 + (1 / 2 + 1 / s.val) * (-s.val - 2)) := by
        rw [← Real.rpow_mul hn.le, ← Real.rpow_add hn, ← Real.rpow_add hn]
        congr 1
        ring
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le hn1
        have hs : 1 < 2 / s.val := (lt_div_iff₀ s.property.1).mpr (by linarith [s.property.2])
        have he : 1 / 2 + 2 + (1 / 2 + 1 / s.val) * (-s.val - 2) =
            1 / 2 - s.val / 2 - 2 / s.val := by
          field_simp [ne_of_gt s.property.1]
          ring
        rw [he]
        linarith
  nlinarith only [hfirst, hsecond]

/-- See the proof of Proposition 5.15 in the paper: the actual reference crossing
row error, with its square-root size and the correct period dependence. -/
theorem referenceCrossing_row_different_period (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m m₀ n₀ : ℕ+) (hm : 2 ≤ (m : ℕ))
      (hm₀ : 4 ≤ (m₀ : ℕ)) (hle : (m₀ : ℕ) ≤ (m : ℕ))
      (hn₀ : 2 * (n₀ : ℕ) < (m₀ : ℕ)) (K : ℕ) (l : Fin (n₀ : ℕ)),
      Real.sqrt (∑ i : Fin (n₀ : ℕ),
        (BoundaryEntries.referenceCrossing s m hm K n₀ (by omega) i l -
          BoundaryEntries.referenceCrossing s m₀ (by omega) K n₀ (by omega) i l) ^ 2) ≤
        C * Real.sqrt (n₀ : ℝ) * ((m₀ : ℝ) ^ (-s.val) +
          (n₀ : ℝ) ^ 2 * (m₀ : ℝ) ^ (-s.val - 2)) := by
  obtain ⟨C, hC, hb⟩ := referenceCrossing_different_period s
  refine ⟨C, hC, fun m m₀ n₀ hm hm₀ hle hn₀ K l => ?_⟩
  let B := C * ((m₀ : ℝ) ^ (-s.val) + (n₀ : ℝ) ^ 2 * (m₀ : ℝ) ^ (-s.val - 2))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hs : (∑ i : Fin (n₀ : ℕ),
      (BoundaryEntries.referenceCrossing s m hm K n₀ (by omega) i l -
        BoundaryEntries.referenceCrossing s m₀ (by omega) K n₀ (by omega) i l) ^ 2) ≤
      (n₀ : ℝ) * B ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin (n₀ : ℕ), B ^ 2 := by
        apply sum_le_sum
        intro i _
        have hh := hb m m₀ n₀ hm hm₀ hle hn₀ K i l
        have hh' := (sq_le_sq₀ (abs_nonneg _) hB).mpr hh
        simpa only [sq_abs] using hh'
      _ = _ := by simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  apply (Real.sqrt_le_sqrt hs).trans_eq
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hB]
  dsimp [B]
  ring

/-- Internal endpoint sum in the proof of Proposition 5.15:
a constant initial segment and its power tail have the same boundary order. -/
theorem endpoint_max_power_sum_internal {t : ℝ} (ht : 1 < t)
    (n : ℕ+) (k : Fin (n : ℕ)) :
    (∑ i : Fin (n : ℕ), ((max (i.val + 1) (k.val + 1) : ℕ) : ℝ) ^ (-t)) ≤
      (2 + 1 / (t - 1)) * (k.val + 1 : ℝ) ^ (1 - t) := by
  let L := k.val + 1
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hLn : L ≤ (n : ℕ) := by have := k.isLt; dsimp [L]; omega
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ((max (i + 1) L : ℕ) : ℝ) ^ (-t))]
  rw [← sum_range_add_sum_Ico _ hLn]
  have hhead : (∑ i ∈ range L, ((max (i + 1) L : ℕ) : ℝ) ^ (-t)) =
      (L : ℝ) ^ (1 - t) := by
    calc
      _ = ∑ _i ∈ range L, (L : ℝ) ^ (-t) := by
        apply sum_congr rfl
        intro i hi
        rw [max_eq_right (by have := mem_range.mp hi; omega)]
      _ = (L : ℝ) * (L : ℝ) ^ (-t) := by rw [sum_const, card_range, nsmul_eq_mul]
      _ = _ := by rw [show 1 - t = -t + 1 by ring, Real.rpow_add_one (by positivity : (L : ℝ) ≠ 0)]; ring
  have htail : (∑ i ∈ Ico L (n : ℕ), ((max (i + 1) L : ℕ) : ℝ) ^ (-t)) ≤
      (1 + 1 / (t - 1)) * (L : ℝ) ^ (1 - t) := by
    calc
      _ = ∑ i ∈ Ico L (n : ℕ),
          if (L : ℝ) ≤ i + 1 then (i + 1 : ℝ) ^ (-t) else 0 := by
        apply sum_congr rfl
        intro i hi
        have hLi : L ≤ i + 1 := by have := mem_Ico.mp hi; omega
        rw [max_eq_left hLi, Nat.cast_add, Nat.cast_one,
          ite_eq_left (by exact_mod_cast hLi)]
      _ ≤ ∑ i ∈ range (n : ℕ),
          if (L : ℝ) ≤ i + 1 then (i + 1 : ℝ) ^ (-t) else 0 :=
        sum_le_sum_of_subset_of_nonneg
          (fun i hi => mem_range.mpr (mem_Ico.mp hi).2)
          (fun i _ _ => by split_ifs <;> positivity)
      _ ≤ _ := by
        rw [← Fin.sum_univ_eq_sum_range (fun i : ℕ =>
          if (L : ℝ) ≤ (i : ℝ) + 1 then ((i : ℝ) + 1) ^ (-t) else 0)]
        exact BoundaryEntries.finite_length_tail_internal ht (by exact_mod_cast hL) _
  rw [hhead]
  have hcast : (k.val : ℝ) + 1 = (L : ℝ) := by dsimp [L]; push_cast; rfl
  rw [hcast]
  linarith only [htail]

/-- See the proof of Proposition 5.15 in the paper: endpoint control of a signed
crossing entry, before summing its row. This internal lemma assumes a parent
entry envelope. Final uses derive it from the matrix predicate. -/
theorem boundaryMatrix_entry_bound_internal (m n : ℕ+)
    (hn : 4 * (n : ℕ) ≤ (m : ℕ))
    (A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → ℝ)
    (C p : ℝ) (hC : 0 ≤ C) (hp : 0 ≤ p)
    (hE : ∀ a b, |intervalMatrix m m le_rfl A a b| ≤
      C * (1 + (Riesz1.cyclicIndexDistance m a b : ℝ)) ^ (-p))
    (i l : Fin (n : ℕ)) :
    |boundaryMatrix m n (by omega) A i l| ≤
      2 * C * (((max i.val l.val + 1 : ℕ) : ℝ) ^ (-p) +
        (((n : ℕ) - min i.val l.val : ℕ) : ℝ) ^ (-p)) := by
  have hi := i.isLt
  have hl := l.isLt
  have hordered (a b : Fin (n : ℕ)) (hab : a.val ≤ b.val) :
      |boundaryMatrix m n (by omega) A a b| ≤
        2 * C * ((b.val + 1 : ℝ) ^ (-p) + (((n : ℕ) - a.val : ℕ) : ℝ) ^ (-p)) := by
    let left : Fin (m : ℕ) := ⟨(m : ℕ) - 1, by have := m.pos; omega⟩
    let right : Fin (m : ℕ) := ⟨(n : ℕ), by omega⟩
    let E := intervalMatrix m m le_rfl A
    have ha := a.isLt
    have hb := b.isLt
    have hd₁ : Riesz1.cyclicIndexDistance m left (b.castLE (by omega)) = b.val + 1 := by
      dsimp [Riesz1.cyclicIndexDistance, left, Nat.dist]
      omega
    have hd₂ : Riesz1.cyclicIndexDistance m (a.castLE (by omega)) right = (n : ℕ) - a.val := by
      dsimp [Riesz1.cyclicIndexDistance, right, Nat.dist]
      omega
    have hd₃ : Riesz1.cyclicIndexDistance m left right = (n : ℕ) + 1 := by
      dsimp [Riesz1.cyclicIndexDistance, left, right, Nat.dist]
      omega
    have hb₁ : |E left (b.castLE (by omega))| ≤ C * (b.val + 1 : ℝ) ^ (-p) := by
      apply (hE _ _).trans
      rw [hd₁, Nat.cast_add, Nat.cast_one]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity)
        (by linarith) (by linarith)) hC
    have hb₂ : |E (a.castLE (by omega)) right| ≤ C * (((n : ℕ) - a.val : ℕ) : ℝ) ^ (-p) := by
      apply (hE _ _).trans
      rw [hd₂]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (show 0 < (n : ℕ) - a.val by omega))
        (by linarith) (by linarith)) hC
    have hbn : (b.val : ℝ) < n := by exact_mod_cast hb
    have hb₃ : |E left right| ≤ C * (b.val + 1 : ℝ) ^ (-p) := by
      apply (hE _ _).trans
      rw [hd₃, Nat.cast_add, Nat.cast_one]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity)
        (by linarith) (by linarith)) hC
    have he := boundaryMatrix_inclusion_exclusion m (n := (n : ℕ)) (by have := n.pos; omega) A a b hab
    dsimp only at he
    rw [he]
    have hs := abs_sub (E left (b.castLE (by omega)) + E (a.castLE (by omega)) right) (E left right)
    have ht := abs_add_le (E left (b.castLE (by omega))) (E (a.castLE (by omega)) right)
    have hnon : 0 ≤ C * (((n : ℕ) - a.val : ℕ) : ℝ) ^ (-p) := by positivity
    dsimp only [E, left, right] at *
    linarith only [hs, ht, hb₁, hb₂, hb₃, hnon]
  rcases le_total i.val l.val with hil | hli
  · simpa only [max_eq_right hil, min_eq_left hil, Nat.cast_add, Nat.cast_one] using hordered i l hil
  · have hsym : boundaryMatrix m n (by omega) A i l = boundaryMatrix m n (by omega) A l i := by
      simp only [boundaryMatrix, rankOne, and_comm]
    rw [hsym]
    simpa only [max_eq_left hli, min_eq_right hli, Nat.cast_add, Nat.cast_one] using hordered l i hli

/-- See the proof of Proposition 5.15 in the paper: square-summation of the
three parent endpoint terms gives the boundary row exponent. The coefficients
may be signed. The only internal input is their parent entry envelope. -/
theorem boundaryMatrix_row_bound_internal (s : Riesz1.RieszExponent)
    (m n : ℕ+) (hn : 4 * (n : ℕ) ≤ (m : ℕ))
    (A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hE : ∀ a b, |intervalMatrix m m le_rfl A a b| ≤
      C * (1 + (Riesz1.cyclicIndexDistance m a b : ℝ)) ^ (-1 - s.val / 2))
    (l : Fin (n : ℕ)) :
    Real.sqrt (∑ i : Fin (n : ℕ), (boundaryMatrix m n (by omega) A i l) ^ 2) ≤
      4 * Real.sqrt (2 + 1 / (1 + s.val)) * C *
        ((min (l.val + 1) ((n : ℕ) - l.val) : ℕ) : ℝ) ^ (-(1 + s.val) / 2) := by
  let T : ℝ := 2 + 1 / (1 + s.val)
  let δ := min (l.val + 1) ((n : ℕ) - l.val)
  let a (i : Fin (n : ℕ)) := (((max i.val l.val + 1 : ℕ) : ℝ)) ^ (-1 - s.val / 2)
  let b (i : Fin (n : ℕ)) := ((((n : ℕ) - min i.val l.val : ℕ) : ℝ)) ^ (-1 - s.val / 2)
  have hT : 0 ≤ T := by dsimp [T]; positivity [s.property.1]
  have hδ : (0 : ℝ) < δ := by
    exact_mod_cast (show 0 < δ by have := l.isLt; dsimp [δ]; omega)
  have hp (x : ℝ) (hx : 0 ≤ x) : (x ^ (-1 - s.val / 2)) ^ 2 = x ^ (-(2 + s.val)) := by
    rw [← Real.rpow_mul_natCast hx]
    congr 1
    ring
  have hsa : (∑ i : Fin (n : ℕ), (a i) ^ 2) ≤ T * (l.val + 1 : ℝ) ^ (-1 - s.val) := by
    have he (i : Fin (n : ℕ)) : (a i) ^ 2 =
        ((max (i.val + 1) (l.val + 1) : ℕ) : ℝ) ^ (-(2 + s.val)) := by
      dsimp only [a]
      rw [hp _ (by positivity)]
      congr 2
      omega
    simp_rw [he]
    simpa only [show 2 + s.val - 1 = 1 + s.val by ring,
      show 1 - (2 + s.val) = -1 - s.val by ring] using
      endpoint_max_power_sum_internal (by linarith [s.property.1] : 1 < 2 + s.val) n l
  have hsb : (∑ i : Fin (n : ℕ), (b i) ^ 2) ≤ T * (((n : ℕ) - l.val : ℕ) : ℝ) ^ (-1 - s.val) := by
    let f (i : Fin (n : ℕ)) :=
      ((max (i.val + 1) (l.rev.val + 1) : ℕ) : ℝ) ^ (-(2 + s.val))
    have he (i : Fin (n : ℕ)) : (b i) ^ 2 = f (Fin.revPerm i) := by
      dsimp only [b, f]
      rw [hp _ (by positivity)]
      congr 2
      simp only [Fin.revPerm_apply, Fin.val_rev]
      have := i.isLt
      have := l.isLt
      omega
    simp_rw [he]
    rw [Equiv.sum_comp Fin.revPerm f]
    have hlrev : l.rev.val + 1 = (n : ℕ) - l.val := by
      simp only [Fin.val_rev]
      have := l.isLt
      omega
    have hlrevR : (l.rev.val : ℝ) + 1 = (((n : ℕ) - l.val : ℕ) : ℝ) := by exact_mod_cast hlrev
    simpa only [f, hlrev, hlrevR, show 2 + s.val - 1 = 1 + s.val by ring,
      show 1 - (2 + s.val) = -1 - s.val by ring, Nat.cast_add, Nat.cast_one] using
      endpoint_max_power_sum_internal (by linarith [s.property.1] : 1 < 2 + s.val) n l.rev
  have hsum : (∑ i : Fin (n : ℕ), (boundaryMatrix m n (by omega) A i l) ^ 2) ≤
      16 * C ^ 2 * T * (δ : ℝ) ^ (-1 - s.val) := by
    have hterm (i : Fin (n : ℕ)) :
        (boundaryMatrix m n (by omega) A i l) ^ 2 ≤ 8 * C ^ 2 * ((a i) ^ 2 + (b i) ^ 2) := by
      have he := boundaryMatrix_entry_bound_internal m n hn A C (1 + s.val / 2)
        hC (by linarith [s.property.1]) (by simpa only [show -(1 + s.val / 2) = -1 - s.val / 2 by ring] using hE) i l
      have he' : |boundaryMatrix m n (by omega) A i l| ≤ 2 * C * (a i + b i) := by
        simpa only [a, b, show -(1 + s.val / 2) = -1 - s.val / 2 by ring] using he
      have hnon : 0 ≤ 2 * C * (a i + b i) := by dsimp [a, b]; positivity
      have hh := (sq_le_sq₀ (abs_nonneg _) hnon).mpr he'
      rw [sq_abs] at hh
      nlinarith only [hh, mul_nonneg (sq_nonneg C) (sq_nonneg (a i - b i))]
    have hleft : (l.val + 1 : ℝ) ^ (-1 - s.val) ≤ (δ : ℝ) ^ (-1 - s.val) :=
      Real.rpow_le_rpow_of_nonpos hδ
        (by exact_mod_cast (min_le_left (l.val + 1) ((n : ℕ) - l.val)))
        (by linarith [s.property.1])
    have hright : (((n : ℕ) - l.val : ℕ) : ℝ) ^ (-1 - s.val) ≤ (δ : ℝ) ^ (-1 - s.val) :=
      Real.rpow_le_rpow_of_nonpos hδ
        (by exact_mod_cast (min_le_right (l.val + 1) ((n : ℕ) - l.val)))
        (by linarith [s.property.1])
    calc
      _ ≤ ∑ i : Fin (n : ℕ), 8 * C ^ 2 * ((a i) ^ 2 + (b i) ^ 2) := sum_le_sum fun i _ => hterm i
      _ = 8 * C ^ 2 * ((∑ i, (a i) ^ 2) + ∑ i, (b i) ^ 2) := by rw [← sum_add_distrib, mul_sum]
      _ ≤ 8 * C ^ 2 * (2 * T * (δ : ℝ) ^ (-1 - s.val)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith only [hsa, hsb, mul_le_mul_of_nonneg_left hleft hT,
          mul_le_mul_of_nonneg_left hright hT]
      _ = _ := by ring
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hpow : ((δ : ℝ) ^ (-(1 + s.val) / 2)) ^ 2 = (δ : ℝ) ^ (-1 - s.val) := by
    rw [← Real.rpow_mul_natCast hδ.le]
    congr 1
    ring
  change _ ≤ (4 * Real.sqrt T * C * (δ : ℝ) ^ (-(1 + s.val) / 2)) ^ 2
  calc
    _ ≤ _ := hsum
    _ = _ := by rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hT, hpow]; ring

/-- See the proof of Proposition 5.15 in the paper: signed crossing retention
commutes with subtraction of the literal parent reference coefficients. -/
theorem boundaryMatrix_sub (m : ℕ+) (n : ℕ) (hn : n ≤ (m : ℕ))
    (A B : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → ℝ) :
    boundaryMatrix m n hn (A - B) = boundaryMatrix m n hn A - boundaryMatrix m n hn B := by
  ext i l
  simp only [boundaryMatrix, Matrix.sub_apply, ← sum_sub_distrib]
  apply sum_congr rfl
  intro t _
  simp only [Pi.sub_apply]
  split_ifs <;> ring

/-- See the proof of Proposition 5.15 in the paper: combine the parent endpoint
row and reference-period row into the full remainder estimate. The internal
entry-envelope input is supplied from the predicate by the window theorem. -/
theorem remainder_row_bound_internal (s : Riesz1.RieszExponent) :
    ∃ Cperiod : ℝ, 0 < Cperiod ∧
    ∀ (m m₀ n : ℕ+) (hm : 2 ≤ (m : ℕ)) (hm₀ : 4 ≤ (m₀ : ℕ))
      (hle : (m₀ : ℕ) ≤ (m : ℕ)) (hn : 4 * (n : ℕ) ≤ (m : ℕ))
      (hn₀ : 2 * (n : ℕ) < (m₀ : ℕ))
      (hscale : m₀ = m ∨ (n : ℝ) ^ (1 / 2 + 1 / s.val) ≤ (m₀ : ℝ))
      (K : ℕ) (A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → ℝ)
      (E : ℝ), 0 ≤ E →
      (∀ a b, |intervalMatrix m m le_rfl (A - BoundaryEntries.referenceWeight s m hm K) a b| ≤
        E * (1 + (Riesz1.cyclicIndexDistance m a b : ℝ)) ^ (-1 - s.val / 2)) →
      ∀ l : Fin (n : ℕ),
      Real.sqrt (∑ i : Fin (n : ℕ),
        (intervalMatrix m n (by omega) A i l - internalMatrix m n (by omega) A i l -
          BoundaryEntries.referenceCrossing s m₀ (by omega) K n (by omega) i l) ^ 2) ≤
      (4 * Real.sqrt (2 + 1 / (1 + s.val)) * E + Cperiod) *
        ((min (l.val + 1) ((n : ℕ) - l.val) : ℕ) : ℝ) ^ (-(1 + s.val) / 2) := by
  obtain ⟨C, hC, hb⟩ := referenceCrossing_row_different_period s
  refine ⟨2 * C, by positivity, fun m m₀ n hm hm₀ hle hn hn₀ hscale K A E hE henv l => ?_⟩
  let B := boundaryMatrix m n (by omega) (A - BoundaryEntries.referenceWeight s m hm K)
  let D := BoundaryEntries.referenceCrossing s m hm K n (by omega) -
    BoundaryEntries.referenceCrossing s m₀ (by omega) K n (by omega)
  let δ := min (l.val + 1) ((n : ℕ) - l.val)
  have hδ : (0 : ℝ) < δ := by
    exact_mod_cast (show 0 < δ by have := l.isLt; dsimp [δ]; omega)
  have hparent : Real.sqrt (∑ i, (B i l) ^ 2) ≤
      4 * Real.sqrt (2 + 1 / (1 + s.val)) * E * (δ : ℝ) ^ (-(1 + s.val) / 2) :=
    boundaryMatrix_row_bound_internal s m n hn _ E hE henv l
  have hperiod : Real.sqrt (∑ i, (D i l) ^ 2) ≤
      2 * C * (δ : ℝ) ^ (-(1 + s.val) / 2) := by
    rcases hscale with hsame | hlarge
    · subst m₀
      simp only [D, sub_self, Matrix.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, sum_const_zero, Real.sqrt_zero]
      positivity
    · have hh := hb m m₀ n hm hm₀ hle hn₀ K l
      change Real.sqrt (∑ i, (D i l) ^ 2) ≤ _ at hh
      have hsc := period_row_error_absorption s n m₀ hlarge
      have hd : (n : ℝ) ^ (-(1 + s.val) / 2) ≤ (δ : ℝ) ^ (-(1 + s.val) / 2) :=
        Real.rpow_le_rpow_of_nonpos hδ (by exact_mod_cast
          (show δ ≤ (n : ℕ) by have := l.isLt; dsimp [δ]; omega))
          (by linarith [s.property.1])
      calc
        _ ≤ _ := hh
        _ = C * (Real.sqrt (n : ℝ) * ((m₀ : ℝ) ^ (-s.val) +
            (n : ℝ) ^ 2 * (m₀ : ℝ) ^ (-s.val - 2))) := by ring
        _ ≤ C * (2 * (n : ℝ) ^ (-(1 + s.val) / 2)) := mul_le_mul_of_nonneg_left hsc hC.le
        _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hd hC.le]
  have he (i : Fin (n : ℕ)) :
      intervalMatrix m n (by omega) A i l - internalMatrix m n (by omega) A i l -
        BoundaryEntries.referenceCrossing s m₀ (by omega) K n (by omega) i l = B i l + D i l := by
    have hsplit := congrFun (congrFun (internal_add_boundary m n (by omega) A) i) l
    simp only [Matrix.add_apply] at hsplit
    dsimp only [B, D]
    rw [boundaryMatrix_sub, Matrix.sub_apply, Matrix.sub_apply,
      ← BoundaryEntries.referenceCrossing_eq_boundaryMatrix s m hm K n (by omega)]
    linarith only [hsplit]
  simp_rw [he]
  have htriangle : Real.sqrt (∑ i, (B i l + D i l) ^ 2) ≤
      Real.sqrt (∑ i, (B i l) ^ 2) + Real.sqrt (∑ i, (D i l) ^ 2) := by
    let v : EuclideanSpace ℝ (Fin (n : ℕ)) := WithLp.toLp 2 (fun i => B i l)
    let w : EuclideanSpace ℝ (Fin (n : ℕ)) := WithLp.toLp 2 (fun i => D i l)
    simpa only [EuclideanSpace.norm_eq, PiLp.add_apply, v, w, PiLp.toLp_apply,
      Real.norm_eq_abs, sq_abs] using norm_add_le v w
  linarith only [htriangle, hparent, hperiod]

/-- See the proof of Proposition 5.15 in the paper, equation (5.63):
the actual cyclic window's remainder has the required boundary row norm.
The measurable parent coefficient witness is supplied by the assumptions.
No entry estimate or localization conclusion is added as a hypothesis. -/
theorem window_remainder_row_bound {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (s : Riesz1.RieszExponent) :
    ∃ Cperiod : ℝ, 0 < Cperiod ∧
    ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ)) (K : ℕ) (C κ γ ε : ℝ), 1 ≤ C →
    ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M →
    ∃ A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → Ω → ℝ,
      (∀ t, Measurable (A t)) ∧ ∀ᵐ x ∂ν,
      (∀ t, 0 ≤ A t x) ∧ intervalMatrix m m le_rfl (fun t => A t x) = M x ∧
      ∀ (j i₀ : Fin (m : ℕ)) (hR : 16 ≤ Riesz1.cyclicIndexDistance m j i₀),
      let n₀ := windowSize m j i₀
      let m₀ := windowPeriod s m j i₀
      let hm₀ : 2 ≤ (m₀ : ℕ) := by
        have := two_windowSize_lt_period s m j i₀ hR
        have := (windowSize m j i₀).pos
        change 2 ≤ (windowPeriod s m j i₀ : ℕ)
        omega
      let hn : (n₀ : ℕ) ≤ (m : ℕ) := by
        have := (window_size_bounds m j i₀ hR).2.2.2
        change (windowSize m j i₀ : ℕ) ≤ (m : ℕ)
        omega
      let hn₀ : (n₀ : ℕ) ≤ (m₀ : ℕ) := by
        have := two_windowSize_lt_period s m j i₀ hR
        change (windowSize m j i₀ : ℕ) ≤ (windowPeriod s m j i₀ : ℕ)
        omega
      let b := j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ))
      let P := fun x (i l : Fin (n₀ : ℕ)) => M x (i.castLE hn + b) (l.castLE hn + b)
      ∀ l : Fin (n₀ : ℕ),
      Real.sqrt (∑ i : Fin (n₀ : ℕ),
        (remainder s m m₀ n₀ hm₀ hn hn₀ K (fun t => A (t.1 + b, t.2)) P x l i) ^ 2) ≤
      (4 * Real.sqrt (2 + 1 / (1 + s.val)) * (C * (n : ℝ) ^ (κ * ε)) + Cperiod) *
        ((min (l.val + 1) ((n₀ : ℕ) - l.val) : ℕ) : ℝ) ^ (-(1 + s.val) / 2) := by
  obtain ⟨Cperiod, hCperiod, hb⟩ := remainder_row_bound_internal s
  refine ⟨Cperiod, hCperiod, fun n m hm K C κ γ ε hC M hM => ?_⟩
  obtain ⟨a, ha, hrep⟩ := periodizedMatrixBounds_entry_representation s n m hm K C κ γ ε M hM
  refine ⟨fun t => a t.1 t.2, fun t => ha t.1 t.2, ?_⟩
  filter_upwards [hrep, periodizedMatrixBounds_truncated_error s n m hm K C κ γ ε
    (by linarith : 0 ≤ C) M hM] with x hx he
  let A := fun t : Fin (m : ℕ) × Fin ((m : ℕ) / 2) => a t.1 t.2 x
  have hmatrix : intervalMatrix m m le_rfl A = M x := by
    ext i l
    rw [intervalMatrix_entries]
    exact (hx.2 i l).symm
  refine ⟨fun t => (hx.1 t.1 t.2).1, hmatrix, fun j i₀ hR => ?_⟩
  dsimp only
  intro l
  let n₀ := windowSize m j i₀
  let m₀ := windowPeriod s m j i₀
  let b : Fin (m : ℕ) := j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ))
  have hn : 4 * (n₀ : ℕ) ≤ (m : ℕ) := (window_size_bounds m j i₀ hR).2.2.2
  have hn₀ : 2 * (n₀ : ℕ) < (m₀ : ℕ) := two_windowSize_lt_period s m j i₀ hR
  have hfive : 5 ≤ (n₀ : ℕ) := (window_size_bounds m j i₀ hR).1
  have hm₀ : 4 ≤ (m₀ : ℕ) := by omega
  have hle : (m₀ : ℕ) ≤ (m : ℕ) := windowPeriod_le_parent s m j i₀
  have hscale : m₀ = m ∨ (n₀ : ℝ) ^ (1 / 2 + 1 / s.val) ≤ (m₀ : ℝ) := by
    by_cases h : m₀ = m
    · exact Or.inl h
    · right
      have hlt : (m₀ : ℕ) < (m : ℕ) := by
        have hh : (m₀ : ℕ) ≠ (m : ℕ) := fun hh => h (Subtype.ext hh)
        omega
      exact power_le_windowPeriod_of_lt s m j i₀ hlt
  have henv (p w : Fin (m : ℕ)) :
      |intervalMatrix m m le_rfl
        ((fun t => A (t.1 + b, t.2)) - BoundaryEntries.referenceWeight s m hm K) p w| ≤
        (C * (n : ℝ) ^ (κ * ε)) *
          (1 + (Riesz1.cyclicIndexDistance m p w : ℝ)) ^ (-1 - s.val / 2) := by
    have hcoef : ((fun t => A (t.1 + b, t.2)) - BoundaryEntries.referenceWeight s m hm K) =
        (fun t => (A - BoundaryEntries.referenceWeight s m hm K) (t.1 + b, t.2)) := rfl
    rw [hcoef, intervalMatrix_translate, intervalMatrix_sub, hmatrix,
      intervalMatrix_referenceWeight, Matrix.sub_apply]
    simpa only [distance_add, show -(1 + s.val / 2) = -1 - s.val / 2 by ring] using he (p + b) (w + b)
  have hh := hb m m₀ n₀ hm hm₀ hle hn hn₀ hscale K (fun t => A (t.1 + b, t.2))
    (C * (n : ℝ) ^ (κ * ε)) (mul_nonneg (by linarith) (by positivity)) henv l
  have hprincipal (i k : Fin (n₀ : ℕ)) :
      M x (i.castLE (by omega : (n₀ : ℕ) ≤ (m : ℕ)) + b)
        (k.castLE (by omega : (n₀ : ℕ) ≤ (m : ℕ)) + b) =
        intervalMatrix m n₀ (by omega) (fun t => A (t.1 + b, t.2)) i k := by
    rw [intervalMatrix_restrict, intervalMatrix_translate, hmatrix]
  simp only [remainder, Matrix.sub_apply]
  convert hh using 1
  congr 1
  apply sum_congr rfl
  intro i _
  change (M x (l.castLE (by omega : (n₀ : ℕ) ≤ (m : ℕ)) + b)
      (i.castLE (by omega : (n₀ : ℕ) ≤ (m : ℕ)) + b) -
      internalMatrix m n₀ (by omega) (fun t => A (t.1 + b, t.2)) l i -
      BoundaryEntries.referenceCrossing s m₀ (by omega) K n₀ (by omega) l i) ^ 2 = _
  rw [hprincipal l i,
    intervalMatrix_symm m n₀ (by omega) (fun t => A (t.1 + b, t.2)) l i,
    internalMatrix_symm m n₀ (by omega) (fun t => A (t.1 + b, t.2)) l i,
    BoundaryEntries.referenceCrossing_eq_boundaryMatrix,
    boundaryMatrix_symm m₀ n₀ (by omega) (BoundaryEntries.referenceWeight s m₀ (by omega) K) l i]

/-- See the proof of Proposition 5.15 in the paper: every included reference
coefficient has the positive power lower bound, including the antipodal length.
The cutoff condition is necessary and is stated explicitly. -/
theorem referenceWeight_lower (s : Riesz1.RieszExponent) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K : ℕ)
      (t : Fin (N : ℕ) × Fin ((N : ℕ) / 2)), K ≤ t.2.val + 1 →
      c * (t.2.val + 1 : ℝ) ^ (-s.val - 2) ≤ BoundaryEntries.referenceWeight s N hN K t := by
  obtain ⟨c, C, hc, _, hb⟩ := sampledSecondDifference_bounds s
  refine ⟨c, hc, fun N hN K t hK => ?_⟩
  have hr := t.2.isLt
  have hrN : t.2.val + 1 < (N : ℕ) := by omega
  let k : Fin (N : ℕ) := ⟨(t.2.val + 1) % (N : ℕ), Nat.mod_lt _ N.pos⟩
  have hkval : k.val = t.2.val + 1 := Nat.mod_eq_of_lt hrN
  have hk : k ≠ 0 := by intro h; have hh := congrArg Fin.val h; simp only [hkval, Fin.val_zero] at hh; omega
  have hd : Riesz1.cyclicIndexDistance N k 0 = t.2.val + 1 := by
    simp only [Riesz1.cyclicIndexDistance, Fin.val_zero, Nat.dist_zero_right, hkval]
    omega
  have hlow := (hb N hN k hk).1
  rw [hd, Nat.cast_add, Nat.cast_one] at hlow
  have hpos := (sampledSecondDifference_pos s N hN hk).le
  simp only [BoundaryEntries.referenceWeight, hK, ite_true]
  dsimp only [k] at hlow hpos
  split_ifs <;> nlinarith only [hlow, hpos]

/-- See the proof of Proposition 5.15 in the paper: the parent witness
quantitatively dominates each new-period reference coefficient above the
parent lower cutoff. This is the retained-term input to localized coercivity.
It holds simultaneously for every rotation and every smaller period. -/
theorem retained_weight_domination {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (s : Riesz1.RieszExponent) :
    ∃ c : ℝ, 0 < c ∧
    ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ)) (K : ℕ) (C κ γ ε : ℝ), 1 ≤ C →
    ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M →
    ∃ A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → Ω → ℝ,
      (∀ t, Measurable (A t)) ∧ ∀ᵐ x ∂ν,
      (∀ t, 0 ≤ A t x) ∧ intervalMatrix m m le_rfl (fun t => A t x) = M x ∧
      ∀ (m₀ : ℕ+) (hm₀ : 2 ≤ (m₀ : ℕ)) (hle : (m₀ : ℕ) ≤ (m : ℕ))
        (b : Fin (m : ℕ)) (t : Fin (m₀ : ℕ) × Fin ((m₀ : ℕ) / 2)),
      (n : ℝ) ^ (γ * ε) ≤ (t.2.val + 1 : ℝ) →
      c * C⁻¹ * (n : ℝ) ^ (-κ * ε) * BoundaryEntries.referenceWeight s m₀ hm₀ K t ≤
        A (t.1.castLE hle + b, t.2.castLE (Nat.div_le_div_right hle)) x := by
  obtain ⟨B, hB, hb⟩ := BoundaryEntries.referenceWeight_bound s
  refine ⟨B⁻¹, inv_pos.mpr hB, fun n m hm K C κ γ ε hC M hM => ?_⟩
  obtain ⟨a, ha, hrep⟩ := periodizedMatrixBounds_entry_representation s n m hm K C κ γ ε M hM
  refine ⟨fun t => a t.1 t.2, fun t => ha t.1 t.2, ?_⟩
  filter_upwards [hrep] with x hx
  have hmatrix : intervalMatrix m m le_rfl (fun t => a t.1 t.2 x) = M x := by
    ext i l
    rw [intervalMatrix_entries]
    exact (hx.2 i l).symm
  refine ⟨fun t => (hx.1 t.1 t.2).1, hmatrix, fun m₀ hm₀ hle b t ht => ?_⟩
  have hlow := (hx.1 (t.1.castLE hle + b) (t.2.castLE (Nat.div_le_div_right hle))).2.2
    (by simpa only [Fin.val_castLE, Nat.cast_add, Nat.cast_one] using ht)
  have hbound := mul_le_mul_of_nonneg_left (hb m₀ hm₀ K t)
    (by positivity : 0 ≤ B⁻¹ * C⁻¹ * (n : ℝ) ^ (-κ * ε))
  calc
    _ ≤ (B⁻¹ * C⁻¹ * (n : ℝ) ^ (-κ * ε)) *
        (B * (t.2.val + 1 : ℝ) ^ (-s.val - 2)) := by simpa only [mul_assoc] using hbound
    _ = C⁻¹ * (n : ℝ) ^ (-κ * ε) * (t.2.val + 1 : ℝ) ^ (-s.val - 2) := by
      field_simp [hB.ne']
    _ ≤ _ := by simpa only [Fin.val_castLE, Nat.cast_add, Nat.cast_one] using hlow

/-- See Subsection 5.5 of the paper: the localized interval coefficients retain the
parent coefficient on every internal interval and use the literal new reference
on every other interval. Both branches specify actual interval terms. -/
@[expose] def localizedWeight (s : Riesz1.RieszExponent) (m m₀ : ℕ+)
    (hm₀ : 2 ≤ (m₀ : ℕ)) (hle : (m₀ : ℕ) ≤ (m : ℕ)) (n K : ℕ)
    (A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → ℝ)
    (t : Fin (m₀ : ℕ) × Fin ((m₀ : ℕ) / 2)) : ℝ :=
  if IsInternal m₀ n t then
    A (t.1.castLE hle, t.2.castLE (Nat.div_le_div_right hle))
  else BoundaryEntries.referenceWeight s m₀ hm₀ K t

/-- See the proof of Proposition 5.15 in the paper: the retained part of the
new coefficient family is exactly the existing parent internal block. -/
theorem localizedWeight_internal (s : Riesz1.RieszExponent) (m m₀ n : ℕ+)
    (hm₀ : 2 ≤ (m₀ : ℕ)) (hle : (m₀ : ℕ) ≤ (m : ℕ))
    (hn : 2 * (n : ℕ) < (m₀ : ℕ)) (K : ℕ)
    (A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → ℝ) :
    internalMatrix m₀ n (by omega) (localizedWeight s m m₀ hm₀ hle n K A) =
      internalMatrix m n (by omega) A := by
  ext i l
  rw [internalMatrix_eq_sum m₀ (by omega), internalMatrix_eq_sum m (by omega)]
  apply sum_congr rfl
  intro t _
  by_cases ht : t.1.val + t.2.val + 1 ≤ (n : ℕ)
  · rw [ite_eq_left ht, ite_eq_left ht]
    have hi : IsInternal m₀ n (⟨t.1.val, by have := t.1.isLt; omega⟩,
        ⟨t.2.val, by have := t.2.isLt; omega⟩) :=
      (isInternal_iff m₀ (by omega) _).mpr ht
    simp only [localizedWeight, hi, ite_true]
    rfl
  · simp only [ht, ite_false]

/-- See the proof of Proposition 5.15 in the paper: the crossing terms of the
replacement family are precisely the new reference crossing terms. -/
theorem localizedWeight_crossing (s : Riesz1.RieszExponent) (m m₀ n : ℕ+)
    (hm₀ : 2 ≤ (m₀ : ℕ)) (hle : (m₀ : ℕ) ≤ (m : ℕ))
    (hn : (n : ℕ) ≤ (m₀ : ℕ)) (K : ℕ)
    (A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → ℝ) :
    boundaryMatrix m₀ n hn (localizedWeight s m m₀ hm₀ hle n K A) =
      BoundaryEntries.referenceCrossing s m₀ hm₀ K n hn := by
  rw [BoundaryEntries.referenceCrossing_eq_boundaryMatrix]
  ext i l
  simp only [boundaryMatrix]
  apply sum_congr rfl
  intro t _
  by_cases ht : IsInternal m₀ n t <;> simp only [localizedWeight, ht, ite_true, ite_false]

/-- See the proof of Proposition 5.15 in the paper: the new coefficients
assemble to the actual localized matrix, on both the active and exterior blocks.
This gives an interval representation without identifying component labels with
configuration coordinates. -/
theorem localizedWeight_matrix {Ω : Type*} (s : Riesz1.RieszExponent) (m m₀ n : ℕ+)
    (hm₀ : 2 ≤ (m₀ : ℕ)) (hle : (m₀ : ℕ) ≤ (m : ℕ))
    (hn : 2 * (n : ℕ) < (m₀ : ℕ)) (K : ℕ)
    (A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → Ω → ℝ) (x : Ω) :
    intervalMatrix m₀ m₀ le_rfl (localizedWeight s m m₀ hm₀ hle n K (fun t => A t x)) =
      matrix s m m₀ n hm₀ (by omega) (by omega) K A x := by
  ext i l
  by_cases hi : i.val < (n : ℕ)
  · by_cases hl : l.val < (n : ℕ)
    · let a : Fin (n : ℕ) := ⟨i.val, hi⟩
      let b : Fin (n : ℕ) := ⟨l.val, hl⟩
      have ha : a.castLE (by omega : (n : ℕ) ≤ (m₀ : ℕ)) = i := Fin.ext rfl
      have hb : b.castLE (by omega : (n : ℕ) ≤ (m₀ : ℕ)) = l := Fin.ext rfl
      rw [← ha, ← hb, ← intervalMatrix_restrict]
      have hs := congrFun (congrFun (internal_add_boundary m₀ n (by omega)
        (localizedWeight s m m₀ hm₀ hle n K (fun t => A t x))) a) b
      rw [localizedWeight_internal s m m₀ n hm₀ hle hn,
        localizedWeight_crossing] at hs
      rw [matrix_active]
      exact hs.symm
    · rw [matrix_exterior s m m₀ n hm₀ (by omega) (by omega) K A x i l (Or.inr (by omega)),
        ← intervalMatrix_referenceWeight]
      simp only [intervalMatrix, rankOne, trace, mem_filter, mem_univ, true_and, Fin.castLE_refl]
      apply sum_congr rfl
      intro t _
      by_cases ht : IsInternal m₀ n t
      · have hnot : l ∉ cyclicIndexInterval m₀ t.1 (t.2.val + 1) := by
          intro h
          have := ht l h
          omega
        simp only [localizedWeight, ht, ite_true, hnot, and_false, ite_false, mul_zero]
      · simp only [localizedWeight, ht, ite_false]
  · rw [matrix_exterior s m m₀ n hm₀ (by omega) (by omega) K A x i l (Or.inl (by omega)),
      ← intervalMatrix_referenceWeight]
    simp only [intervalMatrix, rankOne, trace, mem_filter, mem_univ, true_and, Fin.castLE_refl]
    apply sum_congr rfl
    intro t _
    by_cases ht : IsInternal m₀ n t
    · have hnot : i ∉ cyclicIndexInterval m₀ t.1 (t.2.val + 1) := by
        intro h
        have := ht i h
        omega
      simp only [localizedWeight, ht, ite_true, hnot, false_and, ite_false, mul_zero]
    · simp only [localizedWeight, ht, ite_false]

/-- See the proof of Proposition 5.15 in the paper: nonnegative parent
coefficients give nonnegative replacement coefficients on their entire carrier. -/
theorem localizedWeight_nonneg (s : Riesz1.RieszExponent) (m m₀ : ℕ+)
    (hm₀ : 2 ≤ (m₀ : ℕ)) (hle : (m₀ : ℕ) ≤ (m : ℕ)) (n K : ℕ)
    (A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → ℝ) (hA : ∀ t, 0 ≤ A t)
    (t : Fin (m₀ : ℕ) × Fin ((m₀ : ℕ) / 2)) :
    0 ≤ localizedWeight s m m₀ hm₀ hle n K A t := by
  unfold localizedWeight
  split_ifs
  · exact hA _
  · exact BoundaryEntries.referenceWeight_nonneg s m₀ hm₀ K t

/-- See the proof of Proposition 5.15 in the paper: all replacement coefficients
have the required upper envelope. Retaining internal coefficients preserves their
lengths exactly. This is an internal coefficient interface. -/
theorem localizedWeight_upper_internal (s : Riesz1.RieszExponent) :
    ∃ B : ℝ, 0 < B ∧ ∀ (m m₀ : ℕ+) (hm₀ : 2 ≤ (m₀ : ℕ))
      (hle : (m₀ : ℕ) ≤ (m : ℕ)) (n K : ℕ)
      (A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → ℝ) (P : ℝ), 0 ≤ P →
      (∀ t, A t ≤ P * (t.2.val + 1 : ℝ) ^ (-s.val - 2)) →
      ∀ t, localizedWeight s m m₀ hm₀ hle n K A t ≤
        (P + B) * (t.2.val + 1 : ℝ) ^ (-s.val - 2) := by
  obtain ⟨B, hB, hb⟩ := BoundaryEntries.referenceWeight_bound s
  refine ⟨B, hB, fun m m₀ hm₀ hle n K A P hP hupper t => ?_⟩
  unfold localizedWeight
  split_ifs
  · have h := hupper (t.1.castLE hle, t.2.castLE (Nat.div_le_div_right hle))
    simp only [Fin.val_castLE] at h
    nlinarith only [h, mul_nonneg hB.le (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ t.2.val + 1) (-s.val - 2))]
  · have h := hb m₀ hm₀ K t
    nlinarith only [h, mul_nonneg hP (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ t.2.val + 1) (-s.val - 2))]

/-- See the proof of Proposition 5.15 in the paper: a long-interval lower
envelope on the retained parent coefficients implies domination by the
new truncated reference. This internal lemma retains the cutoff explicitly. -/
theorem localizedWeight_reference_domination_internal (s : Riesz1.RieszExponent) :
    ∃ B : ℝ, 0 < B ∧ ∀ (m m₀ : ℕ+) (hm₀ : 2 ≤ (m₀ : ℕ))
      (hle : (m₀ : ℕ) ≤ (m : ℕ)) (n K Kstar : ℕ), K ≤ Kstar →
      ∀ (A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → ℝ), (∀ t, 0 ≤ A t) →
      ∀ c : ℝ, 0 < c →
      (∀ t, Kstar ≤ t.2.val + 1 → c * (t.2.val + 1 : ℝ) ^ (-s.val - 2) ≤ A t) →
      ∀ t, min 1 (c / B) * BoundaryEntries.referenceWeight s m₀ hm₀ Kstar t ≤
        localizedWeight s m m₀ hm₀ hle n K A t := by
  obtain ⟨B, hB, hb⟩ := BoundaryEntries.referenceWeight_bound s
  refine ⟨B, hB, fun m m₀ hm₀ hle n K Kstar hK A hA c hc hlower t => ?_⟩
  have hq : 0 ≤ min 1 (c / B) := le_min (by norm_num) (div_nonneg hc.le hB.le)
  by_cases hlen : Kstar ≤ t.2.val + 1
  · have href := hb m₀ hm₀ Kstar t
    unfold localizedWeight
    split_ifs with ht
    · have hlow := hlower (t.1.castLE hle, t.2.castLE (Nat.div_le_div_right hle)) hlen
      simp only [Fin.val_castLE] at hlow
      calc
        _ ≤ min 1 (c / B) * (B * (t.2.val + 1 : ℝ) ^ (-s.val - 2)) :=
          mul_le_mul_of_nonneg_left href hq
        _ ≤ (c / B) * (B * (t.2.val + 1 : ℝ) ^ (-s.val - 2)) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
        _ = c * (t.2.val + 1 : ℝ) ^ (-s.val - 2) := by field_simp
        _ ≤ _ := hlow
    · have heq : BoundaryEntries.referenceWeight s m₀ hm₀ Kstar t =
          BoundaryEntries.referenceWeight s m₀ hm₀ K t := by
        simp only [BoundaryEntries.referenceWeight, hlen, hlen.trans' hK, ite_true]
      rw [heq]
      exact mul_le_of_le_one_left (BoundaryEntries.referenceWeight_nonneg s m₀ hm₀ K t) (min_le_left _ _)
  · have hz : BoundaryEntries.referenceWeight s m₀ hm₀ Kstar t = 0 := by
      simp only [BoundaryEntries.referenceWeight, hlen, ite_false]
    rw [hz, mul_zero]
    exact localizedWeight_nonneg s m m₀ hm₀ hle n K A hA t

/-- See the proof of Proposition 5.15 in the paper: the replacement matrix
is coercive whenever the retained lower cutoff is at most a quarter-period.
This internal interface keeps the parent lower envelope and the chosen cutoff
explicit. -/
theorem localized_coercivity_internal (s : Riesz1.RieszExponent) :
    ∃ B c₀ : ℝ, 0 < B ∧ 0 < c₀ ∧
    ∀ (m m₀ n : ℕ+) (hm₀ : 2 ≤ (m₀ : ℕ))
      (hle : (m₀ : ℕ) ≤ (m : ℕ)) (hn : 2 * (n : ℕ) < (m₀ : ℕ))
      (K Kstar : ℕ), K ≤ Kstar → 1 ≤ Kstar → Kstar ≤ (m₀ : ℕ) / 4 →
      ∀ (A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → ℝ), (∀ t, 0 ≤ A t) →
      ∀ c : ℝ, 0 < c →
      (∀ t, Kstar ≤ t.2.val + 1 → c * (t.2.val + 1 : ℝ) ^ (-s.val - 2) ≤ A t) →
      (c₀ * min 1 (c / B) * (Kstar : ℝ) ^ (-1 - s.val)) •
        (1 : Matrix (Fin (m₀ : ℕ)) (Fin (m₀ : ℕ)) ℝ) ≤
        matrix s m m₀ n hm₀ (by omega) (by omega) K (fun t (_ : Unit) => A t) () := by
  obtain ⟨B, hB, hb⟩ := localizedWeight_reference_domination_internal s
  obtain ⟨c₀, hc₀, hcoer⟩ := referenceIntervalMatrix_truncated_coercivity s
  refine ⟨B, 2 * c₀, hB, by positivity, fun m m₀ n hm₀ hle hn K Kstar hKK hK hKN A hA c hc hlower => ?_⟩
  let q := min 1 (c / B)
  let W := localizedWeight s m m₀ hm₀ hle n K A
  let V := BoundaryEntries.referenceWeight s m₀ hm₀ Kstar
  have hq : 0 ≤ q := le_min (by norm_num) (div_nonneg hc.le hB.le)
  have hdiff (t) : 0 ≤ (W - q • V) t := by
    have hh := hb m m₀ hm₀ hle n K Kstar hKK A hA c hc hlower t
    change 0 ≤ W t - q * V t
    linarith only [hh]
  have hpos := internalMatrix_posSemidef m₀ m₀ le_rfl (W - q • V) hdiff
  have hfull (F : Fin (m₀ : ℕ) × Fin ((m₀ : ℕ) / 2) → ℝ) :
      internalMatrix m₀ m₀ le_rfl F = intervalMatrix m₀ m₀ le_rfl F := by
    ext i l
    simp only [internalMatrix, intervalMatrix]
    apply sum_congr rfl
    intro t _
    rw [ite_eq_left (show IsInternal m₀ m₀ t from fun j _ => j.isLt)]
  rw [hfull] at hpos
  have hsmul : intervalMatrix m₀ m₀ le_rfl (q • V) = q • intervalMatrix m₀ m₀ le_rfl V := by
    ext i l
    simp only [intervalMatrix, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, mul_sum]
    apply sum_congr rfl
    intro t _
    ring
  rw [intervalMatrix_sub, hsmul] at hpos
  have hdom : q • ((2 : ℝ) • referenceIntervalMatrix s m₀ hm₀ Kstar) ≤
      intervalMatrix m₀ m₀ le_rfl W := by
    rw [← intervalMatrix_referenceWeight]
    exact sub_nonneg.mp (Matrix.nonneg_iff_posSemidef.mpr hpos)
  have hleft : (2 * c₀ * q * (Kstar : ℝ) ^ (-1 - s.val)) •
      (1 : Matrix (Fin (m₀ : ℕ)) (Fin (m₀ : ℕ)) ℝ) ≤
      q • ((2 : ℝ) • referenceIntervalMatrix s m₀ hm₀ Kstar) := by
    have hh := smul_le_smul_of_nonneg_left (hcoer m₀ hm₀ Kstar hK hKN).2.2 (mul_nonneg hq (by norm_num : (0 : ℝ) ≤ 2))
    simpa only [smul_smul, mul_assoc, mul_left_comm, mul_comm] using hh
  have heq := localizedWeight_matrix s m m₀ n hm₀ hle hn K (fun t (_ : Unit) => A t) ()
  rw [← heq]
  exact hleft.trans hdom

/-- See the proof of Proposition 5.15 in the paper: localized coercivity
from the parent matrix hypotheses, simultaneously for every rotated
retained block and every admissible lower cutoff. The cutoff conditions are
construction conditions. No coercivity conclusion is assumed. -/
theorem localized_matrix_coercivity {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (s : Riesz1.RieszExponent) :
    ∃ B c₀ : ℝ, 0 < B ∧ 0 < c₀ ∧
    ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ)) (K : ℕ) (C κ γ ε : ℝ), 1 ≤ C →
    ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M →
    ∃ A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → Ω → ℝ,
      (∀ t, Measurable (A t)) ∧ ∀ᵐ x ∂ν,
      (∀ t, 0 ≤ A t x) ∧ intervalMatrix m m le_rfl (fun t => A t x) = M x ∧
      ∀ (m₀ n₀ : ℕ+) (hm₀ : 2 ≤ (m₀ : ℕ)) (hle : (m₀ : ℕ) ≤ (m : ℕ))
        (hn₀ : 2 * (n₀ : ℕ) < (m₀ : ℕ)) (b : Fin (m : ℕ)) (Kstar : ℕ),
      K ≤ Kstar → 1 ≤ Kstar → Kstar ≤ (m₀ : ℕ) / 4 →
      (n : ℝ) ^ (γ * ε) ≤ (Kstar : ℝ) →
      (c₀ * min 1 (C⁻¹ * (n : ℝ) ^ (-κ * ε) / B) * (Kstar : ℝ) ^ (-1 - s.val)) •
        (1 : Matrix (Fin (m₀ : ℕ)) (Fin (m₀ : ℕ)) ℝ) ≤
        matrix s m m₀ n₀ hm₀ (by omega) (by omega) K (fun t => A (t.1 + b, t.2)) x := by
  obtain ⟨B, c₀, hB, hc₀, hb⟩ := localized_coercivity_internal s
  refine ⟨B, c₀, hB, hc₀, fun n m hm K C κ γ ε hC M hM => ?_⟩
  obtain ⟨a, ha, hrep⟩ := periodizedMatrixBounds_entry_representation s n m hm K C κ γ ε M hM
  refine ⟨fun t => a t.1 t.2, fun t => ha t.1 t.2, ?_⟩
  filter_upwards [hrep] with x hx
  have hmatrix : intervalMatrix m m le_rfl (fun t => a t.1 t.2 x) = M x := by
    ext i l
    rw [intervalMatrix_entries]
    exact (hx.2 i l).symm
  refine ⟨fun t => (hx.1 t.1 t.2).1, hmatrix, ?_⟩
  intro m₀ n₀ hm₀ hle hn₀ b Kstar hKK hK hKN hthreshold
  have hlower (t : Fin (m : ℕ) × Fin ((m : ℕ) / 2)) (ht : Kstar ≤ t.2.val + 1) :
      (C⁻¹ * (n : ℝ) ^ (-κ * ε)) * (t.2.val + 1 : ℝ) ^ (-s.val - 2) ≤ a (t.1 + b) t.2 x := by
    have hh : (n : ℝ) ^ (γ * ε) ≤ ((t.2.val + 1 : ℕ) : ℝ) :=
      hthreshold.trans (by exact_mod_cast ht)
    simpa only [Nat.cast_add, Nat.cast_one] using (hx.1 (t.1 + b) t.2).2.2 hh
  have hc : 0 < C⁻¹ * (n : ℝ) ^ (-κ * ε) := by
    exact mul_pos (inv_pos.mpr (by linarith)) (Real.rpow_pos_of_pos (by positivity) _)
  have hh := hb m m₀ n₀ hm₀ hle hn₀ K Kstar hKK hK hKN
    (fun t => a (t.1 + b) t.2 x) (fun t => (hx.1 (t.1 + b) t.2).1)
    (C⁻¹ * (n : ℝ) ^ (-κ * ε)) hc hlower
  convert hh using 1
  rfl

end Riesz2.LocalizedMatrix
