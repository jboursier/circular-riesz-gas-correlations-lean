/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.GlobalSums
public import Riesz2.DecayLong.GlobalFactorization
public import Riesz2.Preliminaries.InverseRieszMatrix
public import Riesz2.Preliminaries.TruncatedCoercivity
public import Riesz2.Frozen.PeriodizedMatrixBounds
public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Derivative commutators and inverse rows

The interval split, row cutoff and cyclic translation of Subsection 5.3.
The radius is `weightRadius` and the intervals are `cyclicIndexInterval`.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Fin.NatCast Matrix ENNReal
open Finset

attribute [local instance] Classical.propDecidable

namespace Riesz2.DerivativeCommutators

/-- See Subsection 5.3 of the paper: an interval is retained precisely when its length
is at most `η r_j` for every label it contains. This is equivalent to the
minimum formulation, since the interval is nonempty. -/
def IsRetained (N : ℕ+) (i₀ : Fin (N : ℕ)) (η : ℝ)
    (i : Fin (N : ℕ)) (r : Fin ((N : ℕ) / 2)) : Prop :=
  ∀ j ∈ cyclicIndexInterval N i (r.val + 1),
    ((r.val + 1 : ℕ) : ℝ) ≤ η * weightRadius N j i₀

/-- See Subsection 5.3 of the paper: the retained positive interval matrix, with the
actual interval coefficients supplied explicitly. -/
def retainedMatrix (N : ℕ+) (i₀ : Fin (N : ℕ)) (η : ℝ)
    (α : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → ℝ) :
    Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ :=
  by
  classical
  exact fun a b => ∑ i, ∑ r,
    if IsRetained N i₀ η i r then
      α i r * (if a ∈ cyclicIndexInterval N i (r.val + 1) then 1 else 0) *
        (if b ∈ cyclicIndexInterval N i (r.val + 1) then 1 else 0)
    else 0

/-- See Subsection 5.3 of the paper: the discarded part is the difference from the
retained matrix. -/
def discardedMatrix (N : ℕ+) (i₀ : Fin (N : ℕ)) (η : ℝ)
    (α : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → ℝ)
    (M : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ) :
    Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ :=
  M - retainedMatrix N i₀ η α

/-- See Subsection 5.3 of the paper: the lower length cutoff `max(1, η r_i / 2)`. -/
def rowCutoff (N : ℕ+) (i₀ : Fin (N : ℕ)) (η : ℝ) (i : Fin (N : ℕ)) : ℝ :=
  max 1 (η * weightRadius N i i₀ / 2)

/-- Lemma 5.11, equation (5.39): the discarded-row
scale, including its additive one at small retention radii. -/
def paperRowScale (N : ℕ+) (i₀ : Fin (N : ℕ)) (η : ℝ) (i : Fin (N : ℕ)) : ℝ :=
  1 + η * weightRadius N i i₀

/-- Lemma 5.11: comparison of the length cutoff with the current row scale. -/
theorem rowCutoff_le_paperRowScale (N : ℕ+) (i₀ : Fin (N : ℕ))
    {η : ℝ} (hη : 0 ≤ η) (i : Fin (N : ℕ)) :
    rowCutoff N i₀ η i ≤ paperRowScale N i₀ η i := by
  have hz : 0 ≤ η * weightRadius N i i₀ :=
    mul_nonneg hη (le_trans zero_le_one (one_le_weightRadius N i i₀))
  dsimp [rowCutoff, paperRowScale]
  exact max_le (by linarith) (by linarith)

/-- Lemma 5.11: the two discarded-row scales differ by at most three. -/
theorem paperRowScale_le_three_rowCutoff (N : ℕ+) (i₀ : Fin (N : ℕ))
    (η : ℝ) (i : Fin (N : ℕ)) :
    paperRowScale N i₀ η i ≤ 3 * rowCutoff N i₀ η i := by
  have h1 : (1 : ℝ) ≤ rowCutoff N i₀ η i := le_max_left _ _
  have h2 : η * weightRadius N i i₀ / 2 ≤ rowCutoff N i₀ η i := le_max_right _ _
  dsimp [paperRowScale]
  linarith

/-- Lemma 5.11: the current row scale is at most the cycle size. -/
theorem paperRowScale_le_cycle (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (i₀ : Fin (N : ℕ)) {η : ℝ} (hη : η < 1 / 4) (i : Fin (N : ℕ)) :
    paperRowScale N i₀ η i ≤ (N : ℝ) := by
  have hd : Riesz1.cyclicIndexDistance N i i₀ + 1 ≤ (N : ℕ) := by
    have hi := i.isLt
    have hj := i₀.isLt
    unfold Riesz1.cyclicIndexDistance Nat.dist
    omega
  have hr : weightRadius N i i₀ ≤ (N : ℝ) := by
    dsimp [weightRadius]
    exact_mod_cast (show 1 + Riesz1.cyclicIndexDistance N i i₀ ≤ (N : ℕ) by omega)
  have hr0 : 0 ≤ weightRadius N i i₀ := le_trans zero_le_one (one_le_weightRadius N i i₀)
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  dsimp [paperRowScale]
  nlinarith [mul_nonneg (by linarith : 0 ≤ 1 / 4 - η) hr0]

/-- See Subsection 5.3 of the paper: `(τ_h v)_j = v_(j-h)`, with cyclic indices. -/
def cyclicTranslation (N : ℕ+) (h : ℤ) (v : Fin (N : ℕ) → ℝ) : Fin (N : ℕ) → ℝ :=
  fun j => v (j - Riesz1.labelOf N h)

/-- The cutoff is positive, including rows for which no interval is retained. -/
theorem one_le_rowCutoff (N : ℕ+) (i₀ : Fin (N : ℕ)) (η : ℝ) (i : Fin (N : ℕ)) :
    1 ≤ rowCutoff N i₀ η i := le_max_left _ _

/-- The retained interval matrix is symmetric. -/
theorem retainedMatrix_symm (N : ℕ+) (i₀ : Fin (N : ℕ)) (η : ℝ)
    (α : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → ℝ) (a b : Fin (N : ℕ)) :
    retainedMatrix N i₀ η α a b = retainedMatrix N i₀ η α b a := by
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro r _
  classical
  split_ifs <;> ring

/-- Algebraic identity in the proof of Lemma 5.11, valid for every
symmetric retained part and every real diagonal weight. -/
theorem weighted_commutator_identity {ι : Type*} [Fintype ι]
    (M R : Matrix ι ι ℝ) (hR : ∀ i j, R i j = R j i) (w u : ι → ℝ) :
    (∑ i, w i ^ 2 * u i * (M *ᵥ u) i) =
      (∑ i, (w i * u i) * (R *ᵥ (fun j => w j * u j)) i) +
        (1 / 2 : ℝ) * (∑ i, ∑ j, R i j * (w i - w j) ^ 2 * u i * u j) +
        ∑ i, w i ^ 2 * u i * ((M - R) *ᵥ u) i := by
  have hswap : (∑ i, ∑ j, R i j * w j ^ 2 * u i * u j) =
      ∑ i, ∑ j, R i j * w i ^ 2 * u i * u j := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [hR j i]
    ring
  have hpoly : (∑ i, ∑ j, R i j * (w i - w j) ^ 2 * u i * u j) =
      (∑ i, ∑ j, R i j * w i ^ 2 * u i * u j) +
      (∑ i, ∑ j, R i j * w j ^ 2 * u i * u j) -
      2 * (∑ i, ∑ j, (w i * u i) * (R i j * (w j * u j))) := by
    simp only [← sum_add_distrib, ← sum_sub_distrib, mul_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  have hweighted : (∑ i, (w i * u i) * (R *ᵥ (fun j => w j * u j)) i) =
      ∑ i, ∑ j, (w i * u i) * (R i j * (w j * u j)) := by
    simp only [Matrix.mulVec, dotProduct, mul_sum]
  have halign : (∑ i, w i ^ 2 * u i * (R *ᵥ u) i) =
      ∑ i, ∑ j, R i j * w i ^ 2 * u i * u j := by
    simp only [Matrix.mulVec, dotProduct, mul_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  have htail : (∑ i, w i ^ 2 * u i * ((M - R) *ᵥ u) i) =
      (∑ i, w i ^ 2 * u i * (M *ᵥ u) i) -
        ∑ i, w i ^ 2 * u i * (R *ᵥ u) i := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    change w i ^ 2 * u i * (∑ j, (M i j - R i j) * u j) =
      w i ^ 2 * u i * (∑ j, M i j * u j) -
        w i ^ 2 * u i * (∑ j, R i j * u j)
    simp only [sub_mul, sum_sub_distrib, mul_sub]
  rw [htail, hweighted, halign, hpoly, hswap]
  ring

/-- The identity part of the proof of Lemma 5.11, using the exact
retained and discarded matrices and the weight radius. -/
theorem retained_commutator_identity (N : ℕ+) (i₀ : Fin (N : ℕ)) (η t : ℝ)
    (α : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → ℝ)
    (M : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ) (u : Fin (N : ℕ) → ℝ) :
    (∑ i, weightRadius N i i₀ ^ (2 * t) * u i * (M *ᵥ u) i) =
      (∑ i, (weightRadius N i i₀ ^ t * u i) *
        (retainedMatrix N i₀ η α *ᵥ (fun j => weightRadius N j i₀ ^ t * u j)) i) +
      (1 / 2 : ℝ) * (∑ i, ∑ j, retainedMatrix N i₀ η α i j *
        (weightRadius N i i₀ ^ t - weightRadius N j i₀ ^ t) ^ 2 * u i * u j) +
      ∑ i, weightRadius N i i₀ ^ (2 * t) * u i *
        (discardedMatrix N i₀ η α M *ᵥ u) i := by
  have hpow (i : Fin (N : ℕ)) : (weightRadius N i i₀ ^ t) ^ 2 =
      weightRadius N i i₀ ^ (2 * t) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith [one_le_weightRadius N i i₀])]
    congr 1
    ring
  simpa only [hpow, discardedMatrix] using
    weighted_commutator_identity M (retainedMatrix N i₀ η α)
      (retainedMatrix_symm N i₀ η α) (fun i => weightRadius N i i₀ ^ t) u

/-- Two finite real symmetric matrices with the same quadratic form coincide. -/
private theorem symmetric_matrix_eq_of_quadratic_eq {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℝ) (hA : ∀ i j, A i j = A j i)
    (hB : ∀ i j, B i j = B j i)
    (h : ∀ u : ι → ℝ, (∑ i, ∑ j, u i * A i j * u j) =
      ∑ i, ∑ j, u i * B i j * u j) : A = B := by
  classical
  have hd (i : ι) : A i i = B i i := by
    have hi := h (Pi.single i 1)
    simpa only [Pi.single_apply, ite_mul, zero_mul, one_mul,
      mul_ite, mul_zero, mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hi
  ext i j
  have hij := h (Pi.single i 1 + Pi.single j 1)
  have hexp (M : Matrix ι ι ℝ) :
      (∑ a, ∑ b, ((Pi.single i 1 + Pi.single j 1 : ι → ℝ)) a * M a b *
        ((Pi.single i 1 + Pi.single j 1 : ι → ℝ)) b) =
      M i i + M i j + M j i + M j j := by
    simp only [Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib,
      Pi.single_apply, ite_mul, zero_mul, one_mul, mul_ite, mul_zero, mul_one,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  rw [hexp, hexp, hA j i, hB j i, hd i, hd j] at hij
  linarith


/-- The exact positive interval quadratic form of the retained matrix. -/
theorem retainedMatrix_quadratic (N : ℕ+) (i₀ : Fin (N : ℕ)) (η : ℝ)
    (α : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → ℝ) (u : Fin (N : ℕ) → ℝ) :
    (∑ a, ∑ b, u a * retainedMatrix N i₀ η α a b * u b) =
      ∑ i, ∑ r, if IsRetained N i₀ η i r then
        α i r * (cyclicGapSum N i (r.val + 1) u) ^ 2 else 0 := by
  classical
  let c := fun k : Fin (N : ℕ) × Fin ((N : ℕ) / 2) =>
    if IsRetained N i₀ η k.1 k.2 then α k.1 k.2 else 0
  let v := fun (k : Fin (N : ℕ) × Fin ((N : ℕ) / 2)) (a : Fin (N : ℕ)) =>
    if a ∈ cyclicIndexInterval N k.1 (k.2.val + 1) then (1 : ℝ) else 0
  have hc (a b : Fin (N : ℕ)) :
      (∑ k, c k * v k a * v k b) = retainedMatrix N i₀ η α a b := by
    rw [Fintype.sum_prod_type]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro r _
    dsimp only [c, v, retainedMatrix]
    split_ifs <;> ring
  have hs (k : Fin (N : ℕ) × Fin ((N : ℕ) / 2)) :
      (∑ a, v k a * u a) = cyclicGapSum N k.1 (k.2.val + 1) u := by
    rw [← sum_cyclicIndexInterval_eq_cyclicGapSum N k.1 (by have := k.2.isLt; omega)]
    simp only [v, ite_mul, one_mul, zero_mul, sum_ite_mem, univ_inter]
  have h := sum_quadratic_rankOne univ c v u
  simp only [hc, hs] at h
  rw [h, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro r _
  dsimp only [c]
  split_ifs <;> ring

/-- Positive retained coefficients give a positive semidefinite matrix. -/
theorem retainedMatrix_posSemidef (N : ℕ+) (i₀ : Fin (N : ℕ)) (η : ℝ)
    (α : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → ℝ) (hα : ∀ i r, 0 ≤ α i r) :
    (retainedMatrix N i₀ η α).PosSemidef := by
  classical
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.isHermitian_iff_isSymm.mpr
    exact Matrix.IsSymm.ext (fun i j => retainedMatrix_symm N i₀ η α j i)
  · intro u
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, mul_sum, ← mul_assoc]
    rw [retainedMatrix_quadratic]
    apply sum_nonneg
    intro i _
    apply sum_nonneg
    intro r _
    split_ifs
    · exact mul_nonneg (hα i r) (sq_nonneg _)
    · exact le_rfl

/-- Internal polarization bridge from the source interval quadratic form
to its entrywise matrix representation. -/
theorem interval_entries_of_quadratic (N : ℕ+)
    (M : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (α : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → ℝ)
    (hM : ∀ a b, M a b = M b a)
    (hquad : ∀ u : Fin (N : ℕ) → ℝ,
      (∑ a, ∑ b, u a * M a b * u b) =
        ∑ i, ∑ r, α i r * cyclicGapSum N i (r.val + 1) u ^ 2) :
    ∀ a b, M a b = ∑ i, ∑ r, α i r *
      (if a ∈ cyclicIndexInterval N i (r.val + 1) then 1 else 0) *
      (if b ∈ cyclicIndexInterval N i (r.val + 1) then 1 else 0) := by
  let F : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ := fun a b => ∑ i, ∑ r, α i r *
    (if a ∈ cyclicIndexInterval N i (r.val + 1) then 1 else 0) *
    (if b ∈ cyclicIndexInterval N i (r.val + 1) then 1 else 0)
  have hFsym : ∀ a b, F a b = F b a := by
    intro a b
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro r _
    ring
  have hFquad (u : Fin (N : ℕ) → ℝ) :
      (∑ a, ∑ b, u a * F a b * u b) =
        ∑ i, ∑ r, α i r * cyclicGapSum N i (r.val + 1) u ^ 2 := by
    let c := fun k : Fin (N : ℕ) × Fin ((N : ℕ) / 2) => α k.1 k.2
    let v := fun (k : Fin (N : ℕ) × Fin ((N : ℕ) / 2)) (a : Fin (N : ℕ)) =>
      if a ∈ cyclicIndexInterval N k.1 (k.2.val + 1) then (1 : ℝ) else 0
    have hc (a b : Fin (N : ℕ)) : (∑ k, c k * v k a * v k b) = F a b := by
      rw [Fintype.sum_prod_type]
    have hs (k : Fin (N : ℕ) × Fin ((N : ℕ) / 2)) :
        (∑ a, v k a * u a) = cyclicGapSum N k.1 (k.2.val + 1) u := by
      rw [← sum_cyclicIndexInterval_eq_cyclicGapSum N k.1 (by have := k.2.isLt; omega)]
      simp only [v, ite_mul, one_mul, zero_mul, sum_ite_mem, univ_inter]
    have h := sum_quadratic_rankOne univ c v u
    simp only [hc, hs] at h
    rw [h, Fintype.sum_prod_type]
  have hMF := symmetric_matrix_eq_of_quadratic_eq M F hM hFsym
    (fun u => (hquad u).trans (hFquad u).symm)
  intro a b
  exact congrArg (fun Q => Q a b) hMF

/-- The periodized bounds supply measurable interval
coefficients with the required entrywise reconstruction. -/
theorem periodized_interval_entries {X : Type*} [MeasurableSpace X]
    {ν : MeasureTheory.Measure X} (s : Riesz1.RieszExponent) (n N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (K : ℕ) (C κ γ ε : ℝ)
    (M : X → Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (hM : PeriodizedMatrixBounds (ν := ν) s n N hN K C κ γ ε M) :
    ∃ α : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → X → ℝ,
      (∀ i r, Measurable (α i r)) ∧ ∀ᵐ x ∂ν,
      (∀ i r, 0 ≤ α i r x ∧ α i r x ≤
        C * (n : ℝ) ^ (κ * ε) * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2) ∧
        ((n : ℝ) ^ (γ * ε) ≤ ((r.val + 1 : ℕ) : ℝ) →
          C⁻¹ * (n : ℝ) ^ (-κ * ε) * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2) ≤ α i r x)) ∧
      ∀ a b, M x a b = ∑ i, ∑ r, α i r x *
        (if a ∈ cyclicIndexInterval N i (r.val + 1) then 1 else 0) *
        (if b ∈ cyclicIndexInterval N i (r.val + 1) then 1 else 0) := by
  obtain ⟨_, hstr, α, hmeas, hα⟩ := hM
  refine ⟨α, hmeas, ?_⟩
  filter_upwards [hstr, hα] with x hx hax
  exact ⟨hax.1, interval_entries_of_quadratic N (M x) (fun i r => α i r x) hx.1 hax.2⟩

/-- Finite retained sums preserve measurability of the actual coefficients. -/
theorem measurable_retainedMatrix {X : Type*} [MeasurableSpace X]
    (N : ℕ+) (i₀ : Fin (N : ℕ)) (η : ℝ)
    (α : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → X → ℝ)
    (hα : ∀ i r, Measurable (α i r)) (a b : Fin (N : ℕ)) :
    Measurable (fun x => retainedMatrix N i₀ η (fun i r => α i r x) a b) := by
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro r _
  by_cases h : IsRetained N i₀ η i r
  · simp only [ite_eq_left h]
    exact ((hα i r).mul_const _).mul_const _
  · simpa only [ite_eq_right h] using measurable_const

/-- Internal entrywise realization of the discarded intervals, from the
actual interval representation of the matrix. -/
theorem discardedMatrix_entries (N : ℕ+) (i₀ : Fin (N : ℕ)) (η : ℝ)
    (α : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → ℝ)
    (M : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (hM : ∀ a b, M a b = ∑ i, ∑ r, α i r *
      (if a ∈ cyclicIndexInterval N i (r.val + 1) then 1 else 0) *
      (if b ∈ cyclicIndexInterval N i (r.val + 1) then 1 else 0))
    (a b : Fin (N : ℕ)) :
    discardedMatrix N i₀ η α M a b = ∑ i, ∑ r,
      if IsRetained N i₀ η i r then 0 else α i r *
        (if a ∈ cyclicIndexInterval N i (r.val + 1) then 1 else 0) *
        (if b ∈ cyclicIndexInterval N i (r.val + 1) then 1 else 0) := by
  change M a b - retainedMatrix N i₀ η α a b = _
  rw [hM]
  dsimp only [retainedMatrix]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro r _
  split_ifs <;> ring

/-- The discarded matrix is positive semidefinite, as asserted in Subsection 5.3. The entry representation is supplied by polarization above. -/
theorem discardedMatrix_posSemidef (N : ℕ+) (i₀ : Fin (N : ℕ)) (η : ℝ)
    (α : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → ℝ)
    (M : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (hα : ∀ i r, 0 ≤ α i r)
    (hM : ∀ a b, M a b = ∑ i, ∑ r, α i r *
      (if a ∈ cyclicIndexInterval N i (r.val + 1) then 1 else 0) *
      (if b ∈ cyclicIndexInterval N i (r.val + 1) then 1 else 0)) :
    (discardedMatrix N i₀ η α M).PosSemidef := by
  let c := fun k : Fin (N : ℕ) × Fin ((N : ℕ) / 2) =>
    if IsRetained N i₀ η k.1 k.2 then 0 else α k.1 k.2
  let v := fun (k : Fin (N : ℕ) × Fin ((N : ℕ) / 2)) (a : Fin (N : ℕ)) =>
    if a ∈ cyclicIndexInterval N k.1 (k.2.val + 1) then (1 : ℝ) else 0
  have hrep : discardedMatrix N i₀ η α M = ∑ k, c k • Matrix.vecMulVec (v k) (v k) := by
    ext a b
    rw [discardedMatrix_entries N i₀ η α M hM]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul,
      Fintype.sum_prod_type]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro r _
    dsimp only [c, v]
    split_ifs <;> ring
  rw [hrep]
  apply FiniteMatrixOrder.posSemidef_rankOneSum
  intro k _
  dsimp only [c]
  split_ifs
  · exact le_rfl
  · exact hα k.1 k.2

/-- Discarded sums also preserve measurability of the matrix field. -/
theorem measurable_discardedMatrix {X : Type*} [MeasurableSpace X]
    (N : ℕ+) (i₀ : Fin (N : ℕ)) (η : ℝ)
    (α : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → X → ℝ)
    (M : X → Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (hα : ∀ i r, Measurable (α i r)) (hM : ∀ a b, Measurable (fun x => M x a b))
    (a b : Fin (N : ℕ)) :
    Measurable (fun x => discardedMatrix N i₀ η (fun i r => α i r x) (M x) a b) :=
  (hM a b).sub (measurable_retainedMatrix N i₀ η α hα a b)

/-- The radius used in Subsection 5.2 is one-Lipschitz in cyclic distance. -/
theorem weightRadius_lipschitz (N : ℕ+) (i₀ i j : Fin (N : ℕ)) :
    |weightRadius N i i₀ - weightRadius N j i₀| ≤
      (Riesz1.cyclicIndexDistance N i j : ℝ) := by
  have h₁ := cyclicIndexDistance_triangle i j i₀
  have h₂ := cyclicIndexDistance_triangle j i i₀
  rw [cyclicIndexDistance_comm' N j i] at h₂
  have h₁' : (Riesz1.cyclicIndexDistance N i i₀ : ℝ) ≤
      (Riesz1.cyclicIndexDistance N i j : ℝ) + Riesz1.cyclicIndexDistance N j i₀ := by
    exact_mod_cast h₁
  have h₂' : (Riesz1.cyclicIndexDistance N j i₀ : ℝ) ≤
      (Riesz1.cyclicIndexDistance N i j : ℝ) + Riesz1.cyclicIndexDistance N i i₀ := by
    exact_mod_cast h₂
  rw [abs_sub_le_iff]
  dsimp [weightRadius]
  constructor <;> linarith

/-- Two labels of a cyclic interval shorter than half the cycle have distance
strictly smaller than its length, including the antipodal length. -/
theorem distance_lt_interval_length (N : ℕ+) (i : Fin (N : ℕ))
    {r : ℕ} (hr : 2 * r ≤ (N : ℕ)) (a b : Fin (N : ℕ))
    (ha : a ∈ cyclicIndexInterval N i r) (hb : b ∈ cyclicIndexInterval N i r) :
    Riesz1.cyclicIndexDistance N a b < r := by
  have h := single_le_sum (s := univ) (a := i)
    (f := fun j : Fin (N : ℕ) =>
      (if a ∈ cyclicIndexInterval N j r then (1 : ℝ) else 0) *
      (if b ∈ cyclicIndexInterval N j r then (1 : ℝ) else 0))
    (fun _ _ => by positivity) (mem_univ i)
  rw [ite_eq_left ha, ite_eq_left hb, mul_one, cyclicIndexInterval_pair_count N hr a b] at h
  have hn : 1 ≤ r - Riesz1.cyclicIndexDistance N a b := by exact_mod_cast h
  omega

/-- The support and comparable-radius facts in the proof of Lemma 5.11. -/
theorem retained_interval_comparability (N : ℕ+) (i₀ i : Fin (N : ℕ))
    (r : Fin ((N : ℕ) / 2)) {η : ℝ} (hret : IsRetained N i₀ η i r)
    (a b : Fin (N : ℕ)) (ha : a ∈ cyclicIndexInterval N i (r.val + 1))
    (hb : b ∈ cyclicIndexInterval N i (r.val + 1)) :
    (Riesz1.cyclicIndexDistance N a b : ℝ) ≤ η * weightRadius N a i₀ ∧
    (1 - η) * weightRadius N a i₀ ≤ weightRadius N b i₀ ∧
    weightRadius N b i₀ ≤ (1 + η) * weightRadius N a i₀ := by
  have hd := distance_lt_interval_length N i (by have := r.isLt; omega) a b ha hb
  have hd' : (Riesz1.cyclicIndexDistance N a b : ℝ) < ((r.val + 1 : ℕ) : ℝ) := by
    exact_mod_cast hd
  have hk := hret a ha
  have hw := weightRadius_lipschitz N i₀ a b
  rw [abs_sub_le_iff] at hw
  refine ⟨by linarith, ?_, ?_⟩ <;> nlinarith

/-- A discarded interval containing a label has the lower length bound
used in the proof of Lemma 5.11. -/
theorem discarded_interval_length_lower (N : ℕ+) (i₀ i : Fin (N : ℕ))
    (r : Fin ((N : ℕ) / 2)) {η : ℝ} (hη : 0 < η)
    (hdis : ¬ IsRetained N i₀ η i r) (a : Fin (N : ℕ))
    (ha : a ∈ cyclicIndexInterval N i (r.val + 1)) :
    η * weightRadius N a i₀ / (1 + η) < ((r.val + 1 : ℕ) : ℝ) := by
  obtain ⟨b, hb, hbad⟩ : ∃ b ∈ cyclicIndexInterval N i (r.val + 1),
      η * weightRadius N b i₀ < ((r.val + 1 : ℕ) : ℝ) := by
    simpa only [IsRetained, not_forall, not_le, exists_prop] using hdis
  have hd := distance_lt_interval_length N i (by have := r.isLt; omega) a b ha hb
  have hd' : (Riesz1.cyclicIndexDistance N a b : ℝ) < ((r.val + 1 : ℕ) : ℝ) := by
    exact_mod_cast hd
  have hw := weightRadius_lipschitz N i₀ a b
  rw [abs_sub_le_iff] at hw
  rw [div_lt_iff₀ (by linarith : 0 < 1 + η)]
  nlinarith [mul_lt_mul_of_pos_left (lt_of_le_of_lt hw.1 hd') hη]

section Translation

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- Counting-measure `ℓᵖ` norms are invariant under a cyclic shift. -/
theorem norm_shift (hp : 0 < p.toReal) (N : ℕ+) (h : Fin (N : ℕ))
    (v : Fin (N : ℕ) → ℝ) :
    ‖WithLp.toLp p (fun j => v (j - h))‖ = ‖WithLp.toLp p v‖ := by
  rw [PiLp.norm_eq_sum hp, PiLp.norm_eq_sum hp]
  congr 1
  exact (Equiv.subRight h).sum_comp (fun j => ‖v j‖ ^ p.toReal)

/-- Telescoping along `k` forward edges bounds a translation increment. -/
theorem norm_shift_sub_nat_le (hp : 0 < p.toReal) (N : ℕ+)
    (v : Fin (N : ℕ) → ℝ) (k : ℕ) :
    ‖WithLp.toLp p (fun j => v (j - (k : Fin (N : ℕ)))) - WithLp.toLp p v‖ ≤
      (k : ℝ) * ‖WithLp.toLp p (fun j => v (j - 1)) - WithLp.toLp p v‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hid : WithLp.toLp p (fun j => v (j - ((k + 1 : ℕ) : Fin (N : ℕ)))) -
        WithLp.toLp p v =
      WithLp.toLp p (fun j => (v (j - 1) - v j)) +
        (WithLp.toLp p (fun j => v (j - ((k + 1 : ℕ) : Fin (N : ℕ)))) -
          WithLp.toLp p (fun j => v (j - 1))) := by
      ext j
      simp only [PiLp.add_apply, PiLp.sub_apply]
      ring
    have hsecond :
        WithLp.toLp p (fun j => v (j - ((k + 1 : ℕ) : Fin (N : ℕ)))) -
          WithLp.toLp p (fun j => v (j - 1)) =
        WithLp.toLp p (fun j => v ((j - 1) - (k : Fin (N : ℕ))) - v (j - 1)) := by
      ext j
      simp only [PiLp.sub_apply, Nat.cast_add, Nat.cast_one]
      congr 2
      abel
    rw [hid]
    apply (norm_add_le _ _).trans
    rw [hsecond, show (fun j => v ((j - 1) - (k : Fin (N : ℕ))) - v (j - 1)) =
      (fun j => (fun l => v (l - (k : Fin (N : ℕ))) - v l) (j - 1)) from rfl,
      norm_shift hp N (1 : Fin (N : ℕ)) (fun l => v (l - (k : Fin (N : ℕ))) - v l)]
    change ‖WithLp.toLp p (fun j => v (j - 1)) - WithLp.toLp p v‖ +
      ‖WithLp.toLp p (fun j => v (j - (k : Fin (N : ℕ)))) - WithLp.toLp p v‖ ≤ _
    rw [Nat.cast_add, Nat.cast_one]
    nlinarith

/-- The increment of the opposite shift has the same norm. -/
theorem norm_neg_shift_sub (hp : 0 < p.toReal) (N : ℕ+) (h : Fin (N : ℕ))
    (v : Fin (N : ℕ) → ℝ) :
    ‖WithLp.toLp p (fun j => v (j - (-h))) - WithLp.toLp p v‖ =
      ‖WithLp.toLp p (fun j => v (j - h)) - WithLp.toLp p v‖ := by
  have hid : WithLp.toLp p (fun j => v (j - (-h))) - WithLp.toLp p v =
      WithLp.toLp p (fun j => -(v ((j - (-h)) - h) - v (j - (-h)))) := by
    ext j
    simp only [PiLp.sub_apply]
    simp only [sub_neg_eq_add, add_sub_cancel_right]
    ring
  rw [hid, show (fun j => -(v ((j - (-h)) - h) - v (j - (-h)))) =
    (fun j => (fun l => -(v (l - h) - v l)) (j - (-h))) from rfl,
    norm_shift hp N (-h) (fun l => -(v (l - h) - v l))]
  change ‖-(WithLp.toLp p (fun j => v (j - h)) - WithLp.toLp p v)‖ = _
  exact norm_neg _

/-- Translation differences telescope along a shortest cyclic arc. This
includes the antipodal and zero shifts. -/
theorem norm_shift_sub_le_distance (hp : 0 < p.toReal) (N : ℕ+)
    (v : Fin (N : ℕ) → ℝ) (h : Fin (N : ℕ)) :
    ‖WithLp.toLp p (fun j => v (j - h)) - WithLp.toLp p v‖ ≤
      (Riesz1.cyclicIndexDistance N h 0 : ℝ) *
        ‖WithLp.toLp p (fun j => v (j - 1)) - WithLp.toLp p v‖ := by
  have hf := norm_shift_sub_nat_le hp N v h.val
  rw [Fin.cast_val_eq_self] at hf
  have hb := norm_shift_sub_nat_le hp N v (-h).val
  rw [Fin.cast_val_eq_self, norm_neg_shift_sub hp] at hb
  by_cases hz : h = 0
  · subst h
    simp [Riesz1.cyclicIndexDistance]
  · have hneg : (-h).val = (N : ℕ) - h.val := by
      rw [Fin.val_neg, ite_eq_right hz]
    rw [hneg] at hb
    simp only [Riesz1.cyclicIndexDistance, Fin.val_zero, Nat.dist_zero_right]
    rcases le_total h.val ((N : ℕ) - h.val) with hh | hh
    · simpa only [min_eq_left hh] using hf
    · simpa only [min_eq_right hh] using hb

/-- Internal cancellation estimate for a cyclic convolution. The hypotheses
are kernel and input bounds. The application to the actual inverse below
supplies the kernel bounds from the inverse theorem. -/
theorem convolution_cancellation_bound (hp : 0 < p.toReal) (N : ℕ+)
    {b A B L : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 1 ≤ L) (hLN : L ≤ (N : ℝ))
    (k v : Fin (N : ℕ) → ℝ)
    (hk : ∀ h, |k h| ≤ B * weightRadius N h 0 ^ (-1 - b))
    (hmass : |∑ h, k h| ≤ B * (N : ℝ) ^ (-b))
    (hv : ‖WithLp.toLp p v‖ ≤ A * L ^ (b - 1))
    (hdv : ‖WithLp.toLp p (fun j => v (j - 1)) - WithLp.toLp p v‖ ≤
      A * L ^ (b - 2)) :
    ‖WithLp.toLp p (fun j => ∑ h, k h * v (j - h))‖ ≤
      (1 + 2 / (1 - b) + 4 * (1 + 1 / b)) * B * A * L ^ (-1 : ℝ) := by
  classical
  have hL0 : 0 < L := by linarith
  have hN0 : (0 : ℝ) < N := by positivity
  let V := WithLp.toLp p v
  let Δ := fun h : Fin (N : ℕ) =>
    WithLp.toLp p (fun j => v (j - h)) - V
  let S := univ.filter (fun h => weightRadius N h 0 ≤ L)
  have hdecomp : WithLp.toLp p (fun j => ∑ h, k h * v (j - h)) =
      (∑ h, k h) • V + ∑ h, k h • Δ h := by
    ext j
    simp only [PiLp.add_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
      PiLp.sub_apply, V, Δ, mul_sub, sum_sub_distrib, ← sum_mul]
    ring
  have hδshort (h : Fin (N : ℕ)) : ‖Δ h‖ ≤
      weightRadius N h 0 * (A * L ^ (b - 2)) := by
    have hd : (Riesz1.cyclicIndexDistance N h 0 : ℝ) ≤ weightRadius N h 0 := by
      unfold weightRadius
      linarith
    exact (norm_shift_sub_le_distance hp N v h).trans
      ((mul_le_mul_of_nonneg_left hdv (by positivity)).trans
        (mul_le_mul_of_nonneg_right hd (by positivity)))
  have hδlong (h : Fin (N : ℕ)) : ‖Δ h‖ ≤ 2 * (A * L ^ (b - 1)) := by
    calc ‖Δ h‖ ≤ ‖WithLp.toLp p (fun j => v (j - h))‖ + ‖V‖ := norm_sub_le _ _
      _ = 2 * ‖V‖ := by rw [norm_shift hp]; ring
      _ ≤ 2 * (A * L ^ (b - 1)) := mul_le_mul_of_nonneg_left hv (by norm_num)
  have hpow (h : Fin (N : ℕ)) :
      weightRadius N h 0 ^ (-1 - b) * weightRadius N h 0 =
        weightRadius N h 0 ^ (-b) := by
    have hr : 0 < weightRadius N h 0 := by linarith [one_le_weightRadius N h 0]
    conv_lhs => arg 2; rw [← Real.rpow_one (weightRadius N h 0)]
    rw [← Real.rpow_add hr]
    congr 1
    ring
  have hshort : (∑ h ∈ S, |k h| * ‖Δ h‖) ≤
      (2 / (1 - b)) * B * A * L ^ (-1 : ℝ) := by
    calc (∑ h ∈ S, |k h| * ‖Δ h‖) ≤
        ∑ h ∈ S, (B * A * L ^ (b - 2)) * weightRadius N h 0 ^ (-b) := by
          apply sum_le_sum
          intro h _
          have hr0 : 0 ≤ weightRadius N h 0 := le_trans zero_le_one (one_le_weightRadius N h 0)
          calc |k h| * ‖Δ h‖ ≤ (B * weightRadius N h 0 ^ (-1 - b)) *
              (weightRadius N h 0 * (A * L ^ (b - 2))) :=
            mul_le_mul (hk h) (hδshort h) (norm_nonneg _) (by positivity)
            _ = _ := by rw [← hpow h]; ring
      _ = (B * A * L ^ (b - 2)) * ∑ h ∈ S, weightRadius N h 0 ^ (-b) :=
        (mul_sum ..).symm
      _ ≤ (B * A * L ^ (b - 2)) * (2 / (1 - b) * L ^ (1 - b)) :=
        mul_le_mul_of_nonneg_left (sum_weightRadius_le_of_lt_one N 0 hb hb1 hL) (by positivity)
      _ = (2 / (1 - b)) * B * A * L ^ (-1 : ℝ) := by
        rw [show (B * A * L ^ (b - 2)) * (2 / (1 - b) * L ^ (1 - b)) =
          (2 / (1 - b)) * B * A * (L ^ (b - 2) * L ^ (1 - b)) by ring,
          ← Real.rpow_add hL0]
        congr 2
        ring
  have hlong : (∑ h ∈ univ \ S, |k h| * ‖Δ h‖) ≤
      (4 * (1 + 1 / b)) * B * A * L ^ (-1 : ℝ) := by
    have hsub : univ \ S ⊆ univ.filter (fun h => L ≤ weightRadius N h 0) := by
      intro h hh
      have hn := (mem_sdiff.mp hh).2
      have hn' : ¬weightRadius N h 0 ≤ L := by simpa only [S, mem_filter, mem_univ, true_and] using hn
      exact mem_filter.mpr ⟨mem_univ _, (lt_of_not_ge hn').le⟩
    calc (∑ h ∈ univ \ S, |k h| * ‖Δ h‖) ≤
        ∑ h ∈ univ.filter (fun h => L ≤ weightRadius N h 0),
          (2 * B * A * L ^ (b - 1)) * weightRadius N h 0 ^ (-(1 + b)) := by
          apply (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans
          apply sum_le_sum
          intro h _
          have hr0 : 0 ≤ weightRadius N h 0 := le_trans zero_le_one (one_le_weightRadius N h 0)
          calc |k h| * ‖Δ h‖ ≤ (B * weightRadius N h 0 ^ (-1 - b)) *
              (2 * (A * L ^ (b - 1))) :=
            mul_le_mul (hk h) (hδlong h) (norm_nonneg _) (by positivity)
            _ = _ := by rw [show -(1 + b) = -1 - b by ring]; ring
      _ = (2 * B * A * L ^ (b - 1)) *
          ∑ h ∈ univ.filter (fun h => L ≤ weightRadius N h 0),
            weightRadius N h 0 ^ (-(1 + b)) := (mul_sum ..).symm
      _ ≤ (2 * B * A * L ^ (b - 1)) *
          (2 * (1 + 1 / ((1 + b) - 1)) * L ^ (1 - (1 + b))) :=
        mul_le_mul_of_nonneg_left (sum_weightRadius_tail_le N 0 (by linarith : 1 < 1 + b) hL)
          (by positivity)
      _ = (4 * (1 + 1 / b)) * B * A * L ^ (-1 : ℝ) := by
        rw [show (2 * B * A * L ^ (b - 1)) *
            (2 * (1 + 1 / ((1 + b) - 1)) * L ^ (1 - (1 + b))) =
          (4 * (1 + 1 / b)) * B * A * (L ^ (b - 1) * L ^ (-b)) by
            rw [show (1 + b) - 1 = b by ring, show 1 - (1 + b) = -b by ring]
            ring,
          ← Real.rpow_add hL0]
        congr 2
        ring
  have hmass' : ‖(∑ h, k h) • V‖ ≤ B * A * L ^ (-1 : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |∑ h, k h| * ‖V‖ ≤ (B * (N : ℝ) ^ (-b)) * (A * L ^ (b - 1)) :=
        mul_le_mul hmass hv (norm_nonneg _) (by positivity)
      _ ≤ (B * L ^ (-b)) * (A * L ^ (b - 1)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hL0 hLN (by linarith)) hB)
          (by positivity)
      _ = B * A * L ^ (-1 : ℝ) := by
        rw [show (B * L ^ (-b)) * (A * L ^ (b - 1)) =
          B * A * (L ^ (-b) * L ^ (b - 1)) by ring, ← Real.rpow_add hL0]
        congr 2
        ring
  rw [hdecomp]
  calc ‖(∑ h, k h) • V + ∑ h, k h • Δ h‖ ≤
      ‖(∑ h, k h) • V‖ + ∑ h, ‖k h • Δ h‖ :=
        (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ = ‖(∑ h, k h) • V‖ + (∑ h ∈ S, |k h| * ‖Δ h‖) +
        ∑ h ∈ univ \ S, |k h| * ‖Δ h‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
      have hs := sum_sdiff (f := fun h => |k h| * ‖Δ h‖) (subset_univ S)
      linarith only [hs]
    _ ≤ B * A * L ^ (-1 : ℝ) + (2 / (1 - b)) * B * A * L ^ (-1 : ℝ) +
        (4 * (1 + 1 / b)) * B * A * L ^ (-1 : ℝ) :=
      add_le_add (add_le_add hmass' hshort) hlong
    _ = _ := by ring

/-- The inverse kernel is circulant, so row multiplication
is convolution with a fixed kernel. -/
theorem inverse_entry_sub (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (i j : Fin (N : ℕ)) :
    (rieszMatrix s N hN)⁻¹ i j = (rieszMatrix s N hN)⁻¹ 0 (j - i) := by
  apply Complex.ofReal_injective
  change ((Matrix.of (fun a b : Fin (N : ℕ) => sampledRieszKernel s N hN (b - a)))⁻¹ i j : ℂ) = _
  rw [sampledRieszMatrix_inverse_formula hz s N hN i j,
    show ((rieszMatrix s N hN)⁻¹ 0 (j - i) : ℂ) = _ from
      sampledRieszMatrix_inverse_formula hz s N hN 0 (j - i)]
  simp only [sub_zero]

/-- A convenient form of the inverse decay estimate with `(1 + d)` as
base. The numerical factor is independent of the exponent in `(0,1)`. -/
theorem inverse_kernel_radius_bound (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ B : ℝ, 0 < B ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)),
      (∀ h, |(rieszMatrix s N hN)⁻¹ 0 h| ≤ B * weightRadius N h 0 ^ (s.val - 2)) ∧
      |∑ h, (rieszMatrix s N hN)⁻¹ 0 h| ≤ B * (N : ℝ) ^ (s.val - 1) := by
  obtain ⟨C, hC, hc⟩ := sampledRieszMatrix_inverse_decay hz s
  refine ⟨4 * C, by positivity, ?_⟩
  intro N hN
  have hD := hc N hN
  constructor
  · intro h
    have hd := hD.2.1 0 h
    change |(rieszMatrix s N hN)⁻¹ 0 h| ≤ _ at hd
    rw [cyclicIndexDistance_comm' N 0 h] at hd
    let d := Riesz1.cyclicIndexDistance N h 0
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    have hp0 : 0 < 2 - s.val := by linarith [s.property.2]
    have hr : 0 < 1 + (d : ℝ) := by positivity
    have hcompare : (1 + (d : ℝ)) ^ (2 - s.val) ≤ 4 * (1 + (d : ℝ) ^ (2 - s.val)) := by
      by_cases hz : d = 0
      · simp only [hz, Nat.cast_zero, add_zero, Real.one_rpow, Real.zero_rpow hp0.ne']
        norm_num
      · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hz)
        calc (1 + (d : ℝ)) ^ (2 - s.val) ≤ (2 * (d : ℝ)) ^ (2 - s.val) :=
            Real.rpow_le_rpow (by positivity) (by linarith) hp0.le
          _ = (2 : ℝ) ^ (2 - s.val) * (d : ℝ) ^ (2 - s.val) := Real.mul_rpow (by norm_num) hd0
          _ ≤ (4 : ℝ) * (d : ℝ) ^ (2 - s.val) := by
            apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hd0 _)
            calc (2 : ℝ) ^ (2 - s.val) ≤ (2 : ℝ) ^ (2 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [s.property.1])
              _ = 4 := by norm_num
          _ ≤ _ := by linarith
    have hrp : 0 < (1 + (d : ℝ)) ^ (2 - s.val) := Real.rpow_pos_of_pos hr _
    have hdp : 0 < 1 + (d : ℝ) ^ (2 - s.val) := by positivity
    calc |(rieszMatrix s N hN)⁻¹ 0 h| ≤ C / (1 + (d : ℝ) ^ (2 - s.val)) := hd
      _ ≤ (4 * C) / (1 + (d : ℝ)) ^ (2 - s.val) := by
        apply (div_le_div_iff₀ hdp hrp).mpr
        nlinarith [mul_le_mul_of_nonneg_left hcompare hC.le]
      _ = (4 * C) * weightRadius N h 0 ^ (s.val - 2) := by
        rw [show s.val - 2 = -(2 - s.val) by ring, Real.rpow_neg (by linarith [one_le_weightRadius N h 0])]
        rfl
  · have hrow : (∑ h, (rieszMatrix s N hN)⁻¹ 0 h) =
        ∑ h, (rieszMatrix s N hN)⁻¹ h 0 := by
      calc (∑ h, (rieszMatrix s N hN)⁻¹ 0 h) =
          ∑ h, (rieszMatrix s N hN)⁻¹ 0 (-h) := (Equiv.sum_comp (Equiv.neg _) _).symm
        _ = _ := by
          apply sum_congr rfl
          intro h _
          rw [inverse_entry_sub hz s N hN h 0, zero_sub]
    rw [hrow]
    exact hD.2.2.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

/-- Cancellation for inverse rows, at an arbitrary finite counting-measure
exponent. Its constant is uniform in the cycle size and in the row scale. -/
theorem inverse_row_bound (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (hp : 0 < p.toReal) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (L A : ℝ) (v : Fin (N : ℕ) → ℝ), 1 ≤ L → L ≤ (N : ℝ) →
      ‖WithLp.toLp p v‖ ≤ A * L ^ (-s.val) →
      ‖WithLp.toLp p (fun j => v (j - 1)) - WithLp.toLp p v‖ ≤ A * L ^ (-1 - s.val) →
      ‖WithLp.toLp p (v ᵥ* (rieszMatrix s N hN)⁻¹)‖ ≤ C * A * L ^ (-1 : ℝ) := by
  obtain ⟨B, hB, hkernel⟩ := inverse_kernel_radius_bound hz s
  let b := 1 - s.val
  have hb : 0 < b := by dsimp [b]; linarith [s.property.2]
  have hb1 : b < 1 := by dsimp [b]; linarith [s.property.1]
  let D := 1 + 2 / (1 - b) + 4 * (1 + 1 / b)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D * B, mul_pos hD hB, ?_⟩
  intro N hN L A v hL hLN hv hdv
  have hL0 : 0 < L := by linarith
  have hA : 0 ≤ A := by
    have h := (norm_nonneg (WithLp.toLp p v)).trans hv
    exact nonneg_of_mul_nonneg_left h (Real.rpow_pos_of_pos hL0 _)
  let k := fun h => (rieszMatrix s N hN)⁻¹ 0 h
  have hconv : (v ᵥ* (rieszMatrix s N hN)⁻¹) = fun j => ∑ h, k h * v (j - h) := by
    ext j
    change (∑ i, v i * (rieszMatrix s N hN)⁻¹ i j) = _
    calc (∑ i, v i * (rieszMatrix s N hN)⁻¹ i j) =
        ∑ i, v i * (rieszMatrix s N hN)⁻¹ 0 (j - i) := by
          apply sum_congr rfl
          intro i _
          rw [inverse_entry_sub hz s N hN i j]
      _ = _ := by
        apply Fintype.sum_equiv (Equiv.subLeft j)
        intro i
        dsimp [k]
        simp only [Equiv.subLeft_apply, sub_sub_cancel]
        ring
  rw [hconv]
  have h := convolution_cancellation_bound hp N hb hb1 hA hB.le hL hLN k v
    (by simpa only [k, b, show -1 - (1 - s.val) = s.val - 2 by ring] using (hkernel N hN).1)
    (by simpa only [k, b, show -(1 - s.val) = s.val - 1 by ring] using (hkernel N hN).2)
    (by simpa only [b, show 1 - s.val - 1 = -s.val by ring] using hv)
    (by simpa only [b, show 1 - s.val - 2 = -1 - s.val by ring] using hdv)
  simpa only [D] using h

end Translation

/-- Lemma 5.10: optimization of the inverse-row estimate.
The small and large optimal scales are clamped at `1` and the cycle size. -/
theorem inverse_row_optimized (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 0 < p.toReal) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (A₀ A₁ : ℝ) (v : Fin (N : ℕ) → ℝ), 0 ≤ A₀ → 0 ≤ A₁ →
      ‖WithLp.toLp p v‖ ≤ A₀ →
      ‖WithLp.toLp p (fun j => v (j - 1)) - WithLp.toLp p v‖ ≤ A₁ →
      ‖WithLp.toLp p (v ᵥ* (rieszMatrix s N hN)⁻¹)‖ ≤
        C * ((N : ℝ) ^ (s.val - 1) * A₀ + A₀ ^ s.val * A₁ ^ (1 - s.val)) := by
  obtain ⟨C, hC, hc⟩ := DerivativeCommutators.inverse_row_bound (p := p) hz s hp
  refine ⟨2 * C, by positivity, ?_⟩
  intro N hN A₀ A₁ v hA₀ hA₁ hv hdv
  have hN0 : (0 : ℝ) < N := by positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hmass : 0 ≤ (N : ℝ) ^ (s.val - 1) * A₀ := by positivity
  have hinter : 0 ≤ A₀ ^ s.val * A₁ ^ (1 - s.val) := by positivity
  have hscale (L : ℝ) (hL : 0 < L) :
      (A₀ * L ^ s.val) * L ^ (-s.val) = A₀ ∧
      (A₀ * L ^ s.val) * L ^ (-1 - s.val) = A₀ / L ∧
      (A₀ * L ^ s.val) * L ^ (-1 : ℝ) = A₀ * L ^ (s.val - 1) := by
    constructor
    · rw [mul_assoc, ← Real.rpow_add hL]
      simp
    constructor
    · rw [mul_assoc, ← Real.rpow_add hL, show s.val + (-1 - s.val) = -1 by ring,
        Real.rpow_neg_one, div_eq_mul_inv]
    · rw [mul_assoc, ← Real.rpow_add hL]
      simp only [sub_eq_add_neg]
  by_cases hsmall : A₀ ≤ A₁
  · have hd : ‖WithLp.toLp p (fun j => v (j - 1)) - WithLp.toLp p v‖ ≤ 2 * A₀ := by
      calc _ ≤ ‖WithLp.toLp p (fun j => v (j - 1))‖ + ‖WithLp.toLp p v‖ := norm_sub_le _ _
           _ = 2 * ‖WithLp.toLp p v‖ := by rw [DerivativeCommutators.norm_shift hp]; ring
           _ ≤ 2 * A₀ := by linarith
    have h := hc N hN 1 (2 * A₀) v le_rfl hN1 (by simpa using hv.trans (by linarith))
      (by simpa using hd)
    simp only [Real.one_rpow, mul_one] at h
    have hi : A₀ ≤ A₀ ^ s.val * A₁ ^ (1 - s.val) := by
      calc
        A₀ = A₀ ^ s.val * A₀ ^ (1 - s.val) := by
          rw [← Real.rpow_add' hA₀ (by linarith),
            show s.val + (1 - s.val) = 1 by ring, Real.rpow_one]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hA₀ hsmall (by linarith [s.property.2])) (by positivity)
    nlinarith
  · have hA₀pos : 0 < A₀ := lt_of_le_of_lt hA₁ (lt_of_not_ge hsmall)
    by_cases hlarge : A₁ ≤ A₀ / (N : ℝ)
    · have h := hc N hN (N : ℝ) (A₀ * (N : ℝ) ^ s.val) v hN1 le_rfl
        (by rw [(hscale _ hN0).1]; exact hv)
        (by rw [(hscale _ hN0).2.1]; exact hdv.trans hlarge)
      rw [mul_assoc, (hscale _ hN0).2.2] at h
      nlinarith
    · have hA₁pos : 0 < A₁ := by
        have : 0 < A₀ / (N : ℝ) := div_pos hA₀pos hN0
        linarith
      let L := A₀ / A₁
      have hL0 : 0 < L := div_pos hA₀pos hA₁pos
      have hL1 : 1 ≤ L := (one_le_div hA₁pos).mpr (le_of_lt (lt_of_not_ge hsmall))
      have hLN : L ≤ (N : ℝ) := by
        dsimp only [L]
        apply (div_le_iff₀ hA₁pos).mpr
        have := (div_lt_iff₀ hN0).mp (lt_of_not_ge hlarge)
        linarith
      have hder : A₀ / L = A₁ := by dsimp [L]; field_simp
      have h := hc N hN L (A₀ * L ^ s.val) v hL1 hLN
        (by rw [(hscale _ hL0).1]; exact hv)
        (by rw [(hscale _ hL0).2.1, hder]; exact hdv)
      rw [mul_assoc, (hscale _ hL0).2.2] at h
      have hid : A₀ * L ^ (s.val - 1) = A₀ ^ s.val * A₁ ^ (1 - s.val) := by
        rw [show L = A₀ / A₁ from rfl, Real.div_rpow hA₀ hA₁,
          Real.rpow_sub hA₀pos, Real.rpow_one,
          show s.val - 1 = -(1 - s.val) by ring, Real.rpow_neg hA₁]
        field_simp
      rw [hid] at h
      nlinarith

end Riesz2.DerivativeCommutators
