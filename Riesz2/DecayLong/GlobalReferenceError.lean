/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.PeriodizedMatrixBounds
public import Riesz2.Preliminaries.TruncatedCoercivity
public import Riesz2.ToMathlib.FiniteRankOneQuadratic
public import Riesz2.ToMathlib.PowerTailBounds
public import Riesz2.ToMathlib.RpowPartialSums

/-!
# Entrywise bridges for the global reference error

The periodized-matrix assumptions give the interval representation as an
equality of quadratic forms. Polarization identifies the entries, which permits
endpoint cancellation in the proof of Lemma 5.13.
-/

public section

noncomputable section

open MeasureTheory Matrix
open scoped BigOperators Fin.NatCast MatrixOrder

namespace Riesz2

/-- Symmetric real matrices with equal quadratic forms have equal entries. -/
theorem symmetric_matrix_eq_of_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : ∀ i j, A i j = A j i)
    (hB : ∀ i j, B i j = B j i)
    (hq : ∀ u : ι → ℝ, u ⬝ᵥ (A *ᵥ u) = u ⬝ᵥ (B *ᵥ u)) : A = B := by
  have hd (i : ι) : A i i = B i i := by
    simpa only [single_dotProduct, mulVec_single_one, Matrix.col_apply, one_mul] using hq (Pi.single i 1)
  ext i j
  have h := hq (Pi.single i 1 + Pi.single j 1)
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add] at h
  simp only [single_dotProduct, mulVec_single_one, Matrix.col_apply, one_mul] at h
  rw [hA j i, hB j i, hd i, hd j] at h
  linarith

/-- The entry representation implied by the interval quadratic form.
This is the polarization step in the proof of Lemma 5.13. -/
theorem periodizedMatrixBounds_entry_representation {α : Type*} [MeasurableSpace α]
    {ν : Measure α} (s : Riesz1.RieszExponent) (n m : ℕ+) (hm : 2 ≤ (m : ℕ))
    (K : ℕ) (C κ γ ε : ℝ)
    (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M) :
    ∃ a : Fin (m : ℕ) → Fin ((m : ℕ) / 2) → α → ℝ,
      (∀ i r, Measurable (a i r)) ∧ ∀ᵐ x ∂ν,
      (∀ i r, 0 ≤ a i r x ∧ a i r x ≤
        C * (n : ℝ) ^ (κ * ε) * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2) ∧
        ((n : ℝ) ^ (γ * ε) ≤ ((r.val + 1 : ℕ) : ℝ) →
          C⁻¹ * (n : ℝ) ^ (-κ * ε) * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2) ≤
            a i r x)) ∧
      ∀ i j, M x i j = ∑ k, ∑ r, a k r x *
        (if i ∈ cyclicIndexInterval m k (r.val + 1) then 1 else 0) *
        (if j ∈ cyclicIndexInterval m k (r.val + 1) then 1 else 0) := by
  obtain ⟨a, ha, hre⟩ := hM.2.2
  refine ⟨a, ha, ?_⟩
  filter_upwards [hM.2.1, hre] with x hx hax
  refine ⟨hax.1, ?_⟩
  let T : Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ := fun i j =>
    ∑ k, ∑ r, a k r x *
      (if i ∈ cyclicIndexInterval m k (r.val + 1) then 1 else 0) *
      (if j ∈ cyclicIndexInterval m k (r.val + 1) then 1 else 0)
  have hT : ∀ i j, T i j = T j i := by
    intro i j
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro r _
    ring
  have hquad (u : Fin (m : ℕ) → ℝ) :
      u ⬝ᵥ (T *ᵥ u) = ∑ k, ∑ r, a k r x * (cyclicGapSum m k (r.val + 1) u) ^ 2 := by
    have h := sum_quadratic_rankOne (Finset.univ : Finset
      (Fin (m : ℕ) × Fin ((m : ℕ) / 2)))
      (fun p => a p.1 p.2 x)
      (fun p i => if i ∈ cyclicIndexInterval m p.1 (p.2.val + 1) then 1 else 0) u
    simp only [Fintype.sum_prod_type] at h
    have heq (k : Fin (m : ℕ)) (r : Fin ((m : ℕ) / 2)) :
        (∑ i, (if i ∈ cyclicIndexInterval m k (r.val + 1) then (1 : ℝ) else 0) * u i) =
          cyclicGapSum m k (r.val + 1) u := by
      rw [← sum_cyclicIndexInterval_eq_cyclicGapSum m k (by omega)]
      simp only [ite_mul, one_mul, zero_mul, ← Finset.sum_filter]
      congr 1
      ext i
      simp
    simp_rw [heq] at h
    simpa only [T, dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul, mul_assoc] using h
  have heq : M x = T := symmetric_matrix_eq_of_quadratic hx.1 hT
    (fun u => by
      rw [hquad]
      simpa only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc] using hax.2 u)
  intro i j
  exact congrFun (congrFun heq i) j

/-- The active-block comparison extends to every entry since the exterior
blocks are exactly the truncated reference (the proof of Lemma 5.13). -/
theorem periodizedMatrixBounds_truncated_error {α : Type*} [MeasurableSpace α]
    {ν : Measure α} (s : Riesz1.RieszExponent) (n m : ℕ+) (hm : 2 ≤ (m : ℕ))
    (K : ℕ) (C κ γ ε : ℝ) (hC : 0 ≤ C)
    (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M) :
    ∀ᵐ x ∂ν, ∀ i j,
      |M x i j - ((2 : ℝ) • referenceIntervalMatrix s m hm K) i j| ≤
        C * (n : ℝ) ^ (κ * ε) *
          (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-1 - s.val / 2) := by
  filter_upwards [hM.2.1] with x hx
  intro i j
  by_cases hi : i.val < (n : ℕ)
  · by_cases hj : j.val < (n : ℕ)
    · exact hx.2.2.2 i j hi hj
    · rw [hx.2.1 i j (Or.inr (Nat.le_of_not_gt hj)), sub_self, abs_zero]
      positivity
  · rw [hx.2.1 i j (Or.inl (Nat.le_of_not_gt hi)), sub_self, abs_zero]
    positivity

/-- Coercivity in the quadratic-form convention is exactly the Loewner
lower bound used by the global factorization. -/
theorem periodizedMatrixBounds_coercive {α : Type*} [MeasurableSpace α]
    {ν : Measure α} (s : Riesz1.RieszExponent) (n m : ℕ+) (hm : 2 ≤ (m : ℕ))
    (K : ℕ) (C κ γ ε : ℝ)
    (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M) :
    ∀ᵐ x ∂ν, (C⁻¹ * (n : ℝ) ^ (-κ * ε)) •
      (1 : Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ) ≤ M x := by
  filter_upwards [hM.2.1] with x hx
  have hs : (M x).IsHermitian := Matrix.isHermitian_iff_isSymm.mpr (by
    ext i j
    exact hx.1 j i)
  rw [FiniteMatrixOrder.smul_one_le_iff hs]
  intro u
  simpa only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, pow_two] using hx.2.2.1 u

/-- A backward difference of a cyclic-interval indicator is the difference of
its two endpoint indicators. This includes intervals crossing zero and the
half-cycle lengths used in the proof of Lemma 5.13. -/
theorem cyclicIndexInterval_indicator_backward_difference (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (k i : Fin (N : ℕ)) {r : ℕ} (hr : 1 ≤ r) (hrN : r < (N : ℕ)) :
    (if i ∈ cyclicIndexInterval N k r then (1 : ℝ) else 0) -
      (if i - 1 ∈ cyclicIndexInterval N k r then (1 : ℝ) else 0) =
      (if i = k then 1 else 0) - (if i = k + (r : Fin (N : ℕ)) then 1 else 0) := by
  classical
  simp only [mem_cyclicIndexInterval_iff N k i hrN.le,
    mem_cyclicIndexInterval_iff N k (i - 1) hrN.le]
  have hstep : i - 1 - k = (i - k) - 1 := by abel
  rw [hstep]
  have hzero : i = k ↔ (i - k).val = 0 := by
    constructor
    · intro h
      simp [h]
    · intro h
      exact sub_eq_zero.mp (Fin.ext h)
  have hend : i = k + (r : Fin (N : ℕ)) ↔ (i - k).val = r := by
    constructor
    · intro h
      have hh : i - k = (r : Fin (N : ℕ)) := by rw [h]; abel
      rw [hh, Fin.val_natCast, Nat.mod_eq_of_lt hrN]
    · intro h
      have hh : i - k = (r : Fin (N : ℕ)) := Fin.ext (by
        simpa only [Fin.val_natCast, Nat.mod_eq_of_lt hrN] using h)
      calc i = (i - k) + k := by abel
           _ = k + (r : Fin (N : ℕ)) := by rw [hh]; abel
  simp only [hzero, hend]
  have hv : ((i - k) - 1).val = if (i - k).val = 0 then (N : ℕ) - 1 else (i - k).val - 1 := by
    rw [Fin.val_sub, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < (N : ℕ))]
    have hi := (i - k).isLt
    split_ifs with h
    · rw [h]
      simp [Nat.mod_eq_of_lt (by omega : (N : ℕ) - 1 < (N : ℕ))]
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
  rw [hv]
  split_ifs <;> norm_num <;> omega

/-- The first-difference endpoint cancellation in the proof of Lemma 5.13: exactly two starts survive at each length.
Coefficients may vary arbitrarily with the start. -/
theorem interval_matrix_first_difference (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (a : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → ℝ) (i j : Fin (N : ℕ)) :
    (∑ k, ∑ r, a k r * (if i ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
      (if j ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0)) -
    (∑ k, ∑ r, a k r * (if i - 1 ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
      (if j ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0)) =
    ∑ r, (a i r * (if j ∈ cyclicIndexInterval N i (r.val + 1) then 1 else 0) -
      a (i - ((r.val + 1 : ℕ) : Fin (N : ℕ))) r *
        (if j ∈ cyclicIndexInterval N (i - ((r.val + 1 : ℕ) : Fin (N : ℕ)))
          (r.val + 1) then 1 else 0)) := by
  classical
  calc
    _ = ∑ k, ∑ r, a k r *
      ((if i ∈ cyclicIndexInterval N k (r.val + 1) then (1 : ℝ) else 0) -
       (if i - 1 ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0)) *
        (if j ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) := by
      simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
    _ = ∑ r, ∑ k, a k r *
      ((if i = k then (1 : ℝ) else 0) -
       (if i = k + ((r.val + 1 : ℕ) : Fin (N : ℕ)) then 1 else 0)) *
        (if j ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) := by
      have hd (k : Fin (N : ℕ)) (r : Fin ((N : ℕ) / 2)) :=
        cyclicIndexInterval_indicator_backward_difference N hN k i (r := r.val + 1) (by omega)
          (by have := r.isLt; omega)
      simp_rw [hd]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      have heq (k : Fin (N : ℕ)) : i = k + ((r.val + 1 : ℕ) : Fin (N : ℕ)) ↔
          k = i - ((r.val + 1 : ℕ) : Fin (N : ℕ)) := by
        constructor <;> intro h
        · rw [h]; abel
        · rw [h]; abel
      have ht (k : Fin (N : ℕ)) :
          a k r * ((if i = k then (1 : ℝ) else 0) -
            (if i = k + ((r.val + 1 : ℕ) : Fin (N : ℕ)) then 1 else 0)) *
            (if j ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) =
          (if i = k then a k r *
            (if j ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) else 0) -
          (if k = i - ((r.val + 1 : ℕ) : Fin (N : ℕ)) then a k r *
            (if j ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) else 0) := by
        simp only [heq]
        split_ifs <;> ring
      simp_rw [ht, Finset.sum_sub_distrib]
      simp

/-- The mixed-difference endpoint cancellation in the proof of Lemma 5.13. Away from the diagonal each surviving term
prescribes both endpoints of its interval. -/
theorem interval_matrix_mixed_difference (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (a : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → ℝ) (i j : Fin (N : ℕ)) :
    ((∑ k, ∑ r, a k r * (if i ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
      (if j ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0)) -
    (∑ k, ∑ r, a k r * (if i - 1 ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
      (if j ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0))) -
    ((∑ k, ∑ r, a k r * (if i ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
      (if j - 1 ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0)) -
    (∑ k, ∑ r, a k r * (if i - 1 ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
      (if j - 1 ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0))) =
    ∑ r, (a i r * ((if j = i then 1 else 0) -
      (if j = i + ((r.val + 1 : ℕ) : Fin (N : ℕ)) then 1 else 0)) -
      a (i - ((r.val + 1 : ℕ) : Fin (N : ℕ))) r *
        ((if j = i - ((r.val + 1 : ℕ) : Fin (N : ℕ)) then 1 else 0) -
         (if j = i then 1 else 0))) := by
  rw [interval_matrix_first_difference N hN a i j,
    interval_matrix_first_difference N hN a i (j - 1), ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  have hd (k : Fin (N : ℕ)) :=
    cyclicIndexInterval_indicator_backward_difference N hN k j
      (r := r.val + 1) (by omega) (by have := r.isLt; omega)
  calc
    _ = a i r *
        ((if j ∈ cyclicIndexInterval N i (r.val + 1) then (1 : ℝ) else 0) -
         (if j - 1 ∈ cyclicIndexInterval N i (r.val + 1) then 1 else 0)) -
        a (i - ((r.val + 1 : ℕ) : Fin (N : ℕ))) r *
        ((if j ∈ cyclicIndexInterval N (i - ((r.val + 1 : ℕ) : Fin (N : ℕ)))
          (r.val + 1) then 1 else 0) -
         (if j - 1 ∈ cyclicIndexInterval N (i - ((r.val + 1 : ℕ) : Fin (N : ℕ)))
          (r.val + 1) then 1 else 0)) := by ring
    _ = _ := by simp only [hd, sub_add_cancel]

namespace GlobalReferenceErrorInternal

/-- The row/column summation step used in the proof of Lemma 5.13.
This estimate assumes an entry bound. -/
theorem row_column_sums_of_decay (N : ℕ+) (q : ℝ) (hq : 1 < q)
    (A : ℝ) (hA : 0 ≤ A) (E : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (hE : ∀ i j, |E i j| ≤ A *
      (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-q)) :
    (∀ i, ∑ j, |E i j| ≤ A * (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-q))) ∧
    (∀ j, ∑ i, |E i j| ≤ A * (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-q))) := by
  have hsum (i : Fin (N : ℕ)) :
      (∑ j, (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-q)) ≤
        2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-q) :=
    sum_le_two_mul_tsum_cyclicIndexDistance N i (fun _ => by positivity)
      (summable_one_add_rpow_neg hq)
  have hcomm (i j : Fin (N : ℕ)) :
      Riesz1.cyclicIndexDistance N i j = Riesz1.cyclicIndexDistance N j i := by
    simp only [Riesz1.cyclicIndexDistance, Nat.dist_comm]
  constructor
  · intro i
    calc ∑ j, |E i j| ≤ ∑ j, A *
          (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-q) :=
        Finset.sum_le_sum fun j _ => hE i j
      _ = A * ∑ j, (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-q) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hsum i) hA
  · intro j
    calc ∑ i, |E i j| ≤ ∑ i, A *
          (1 + (Riesz1.cyclicIndexDistance N j i : ℝ)) ^ (-q) := by
            apply Finset.sum_le_sum
            intro i _
            simpa only [hcomm i j] using hE i j
      _ = A * ∑ i, (1 + (Riesz1.cyclicIndexDistance N j i : ℝ)) ^ (-q) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hsum j) hA

end GlobalReferenceErrorInternal

end Riesz2
