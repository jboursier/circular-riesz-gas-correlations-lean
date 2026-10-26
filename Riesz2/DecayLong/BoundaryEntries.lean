/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.FiniteMatrixOrder
public import Riesz2.HelfferSjostrand.PhysicalEnergy
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Algebra of grouped crossing intervals

The proof of Lemma 5.6 groups crossing intervals into prefixes, suffixes,
and the full active interval. This file proves the entry and neighboring
increment identities for this grouping.
-/

@[expose] public section
noncomputable section

open Matrix
open scoped BigOperators

namespace Riesz2.BoundaryEntries

/-- The prefix/suffix expansion of Subsection 5.1, for the grouped
coefficients indexed by the n−1 cuts. At n = 1 both sums are empty. -/
def groupedBoundaryMatrix (n : ℕ) (u v : Fin (n - 1) → ℝ) (d : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  d • Matrix.vecMulVec (fun _ => 1) (fun _ => 1) +
    ∑ b : Fin (n - 1), u b • Matrix.vecMulVec
      (fun i : Fin n => if i.val ≤ b.val then 1 else 0)
      (fun i : Fin n => if i.val ≤ b.val then 1 else 0) +
    ∑ a : Fin (n - 1), v a • Matrix.vecMulVec
      (fun i : Fin n => if a.val < i.val then 1 else 0)
      (fun i : Fin n => if a.val < i.val then 1 else 0)

/-- Entry formula for the two grouped endpoint families, with zero-based labels. -/
theorem groupedBoundaryMatrix_apply (n : ℕ) (u v : Fin (n - 1) → ℝ) (d : ℝ)
    (i j : Fin n) :
    groupedBoundaryMatrix n u v d i j = d +
      (∑ b : Fin (n - 1), if i.val ≤ b.val ∧ j.val ≤ b.val then u b else 0) +
      ∑ a : Fin (n - 1), if a.val < i.val ∧ a.val < j.val then v a else 0 := by
  simp only [groupedBoundaryMatrix, Matrix.add_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, mul_one, Matrix.sum_apply]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp_all
  · apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp_all

/-- Positivity of the crossing block follows from its nonnegative grouped
coefficients, including the empty endpoint sums. -/
theorem groupedBoundaryMatrix_posSemidef (n : ℕ) (u v : Fin (n - 1) → ℝ) (d : ℝ)
    (hu : ∀ b, 0 ≤ u b) (hv : ∀ a, 0 ≤ v a) (hd : 0 ≤ d) :
    (groupedBoundaryMatrix n u v d).PosSemidef := by
  apply Matrix.PosSemidef.add
  · apply Matrix.PosSemidef.add
    · exact (FiniteMatrixOrder.posSemidef_vecMulVec_self _).smul hd
    · exact Matrix.posSemidef_sum _ (fun b _ =>
        (FiniteMatrixOrder.posSemidef_vecMulVec_self _).smul (hu b))
  · exact Matrix.posSemidef_sum _ (fun a _ =>
      (FiniteMatrixOrder.posSemidef_vecMulVec_self _).smul (hv a))

/-- Exact neighboring column difference in the grouped crossing expansion.
This is the prefix/suffix identity in the proof of Lemma 5.6. The two cases exhaust the active row labels. -/
theorem groupedBoundaryMatrix_increment (n : ℕ) (u v : Fin (n - 1) → ℝ) (d : ℝ)
    (i : Fin n) (j : Fin (n - 1)) :
    groupedBoundaryMatrix n u v d i ⟨j.val + 1, by omega⟩ -
      groupedBoundaryMatrix n u v d i ⟨j.val, by omega⟩ =
        if i.val ≤ j.val then -u j else v j := by
  rw [groupedBoundaryMatrix_apply, groupedBoundaryMatrix_apply]
  have hp (b : Fin (n - 1)) :
      (if i.val ≤ b.val ∧ j.val + 1 ≤ b.val then u b else 0) -
        (if i.val ≤ b.val ∧ j.val ≤ b.val then u b else 0) =
          if b = j then -(if i.val ≤ j.val then u j else 0) else 0 := by
    by_cases hb : b = j
    · subst b
      by_cases hi : i.val ≤ j.val <;> simp [hi]
    · have hne : b.val ≠ j.val := fun h => hb (Fin.ext h)
      have he : (j.val + 1 ≤ b.val) ↔ (j.val ≤ b.val) := by omega
      simp only [he, sub_self, hb, ↓reduceIte]
  have hs (a : Fin (n - 1)) :
      (if a.val < i.val ∧ a.val < j.val + 1 then v a else 0) -
        (if a.val < i.val ∧ a.val < j.val then v a else 0) =
          if a = j then (if j.val < i.val then v j else 0) else 0 := by
    by_cases ha : a = j
    · subst a
      by_cases hi : j.val < i.val <;> simp [hi]
    · have hne : a.val ≠ j.val := fun h => ha (Fin.ext h)
      have he : (a.val < j.val + 1) ↔ (a.val < j.val) := by omega
      simp only [he, sub_self, ha, ↓reduceIte]
  dsimp only
  have hsumP := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun b _ => hp b)
  have hsumS := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun a _ => hs a)
  rw [Finset.sum_sub_distrib] at hsumP hsumS
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hsumP hsumS
  by_cases hi : i.val ≤ j.val
  · have hj : ¬j.val < i.val := by omega
    simp only [hi, hj, ↓reduceIte] at hsumP hsumS ⊢
    linarith
  · have hj : j.val < i.val := by omega
    simp only [hi, hj, ↓reduceIte] at hsumP hsumS ⊢
    linarith

/-- The positive-block Cauchy–Schwarz step of Lemma 5.6, before applying the physical diagonal estimates. -/
theorem groupedBoundaryMatrix_entry_sq (n : ℕ) (u v : Fin (n - 1) → ℝ) (d : ℝ)
    (hu : ∀ b, 0 ≤ u b) (hv : ∀ a, 0 ≤ v a) (hd : 0 ≤ d) (i j : Fin n) :
    (groupedBoundaryMatrix n u v d i j) ^ 2 ≤
      groupedBoundaryMatrix n u v d i i * groupedBoundaryMatrix n u v d j j := by
  let S := groupedBoundaryMatrix n u v d
  have hS := groupedBoundaryMatrix_posSemidef n u v d hu hv hd
  have hpos (x : Fin n → ℝ) : 0 ≤ S.toBilin' x x := by
    simpa only [Matrix.toBilin'_apply', star_trivial] using hS.dotProduct_mulVec_nonneg x
  have hsym : S.toBilin'.IsSymm := by
    apply Matrix.isSymm_toBilin'_iff_isSymm.mpr
    simpa only [Matrix.IsSymm, conjTranspose_eq_transpose_of_trivial] using hS.isHermitian.eq
  have h := S.toBilin'.apply_sq_le_of_symm hpos (LinearMap.BilinForm.isSymm_iff.mp hsym) (Pi.single i 1) (Pi.single j 1)
  simpa only [Matrix.toBilin'_single] using h

/-- The pointwise shortening comparison used in the proof of Lemma 5.6. Shortening increases the positive-image
terms. The complementary-mass ratio controls every negative-image term.
This holds before taking any conditional expectation, for every exterior. -/
theorem intervalCoefficient_shortening (p : Parameters) (N : ℕ+)
    (L L' : {L : ℝ // 0 < L ∧ L < (N : ℝ)})
    (A : ℝ) (hA : 1 ≤ A) (hshort : L'.val ≤ L.val)
    (hcomp : (N : ℝ) - L'.val ≤ A * ((N : ℝ) - L.val)) :
    A ^ (-p.val.2 - 2) * PhysicalEnergy.intervalCoefficient p N L ≤
      PhysicalEnergy.intervalCoefficient p N L' := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hAp : 0 < A := by linarith
  have hexp : -p.val.2 - 2 ≤ 0 := by linarith [p.property.2.1]
  have habs (k : ℤ) : |L'.val + k * (N : ℝ)| ≤ A * |L.val + k * (N : ℝ)| := by
    by_cases hk : 0 ≤ k
    · have hkR : (0 : ℝ) ≤ k := by exact_mod_cast hk
      have h0 : 0 < L.val + k * (N : ℝ) :=
        add_pos_of_pos_of_nonneg L.property.1 (mul_nonneg hkR hN.le)
      have h1 : 0 < L'.val + k * (N : ℝ) :=
        add_pos_of_pos_of_nonneg L'.property.1 (mul_nonneg hkR hN.le)
      rw [abs_of_pos h0, abs_of_pos h1]
      calc
        _ ≤ L.val + k * (N : ℝ) := by linarith
        _ ≤ _ := le_mul_of_one_le_left h0.le hA
    · have hkR : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
      have h0 : L.val + k * (N : ℝ) < 0 := by nlinarith [L.property.2]
      have h1 : L'.val + k * (N : ℝ) < 0 := by nlinarith [L'.property.2]
      rw [abs_of_neg h0, abs_of_neg h1]
      have htail : 0 ≤ (-(k : ℝ) - 1) * (N : ℝ) :=
        mul_nonneg (by linarith) hN.le
      nlinarith [mul_nonneg (sub_nonneg.mpr hA) htail]
  have hterm (k : ℤ) :
      A ^ (-p.val.2 - 2) * |L.val + k * (N : ℝ)| ^ (-p.val.2 - 2) ≤
        |L'.val + k * (N : ℝ)| ^ (-p.val.2 - 2) := by
    have hbase : 0 < |L'.val + k * (N : ℝ)| := by
      apply abs_pos.mpr
      intro heq
      by_cases hk : 0 ≤ k
      · have hkR : (0 : ℝ) ≤ k := by exact_mod_cast hk
        have : 0 < L'.val + k * (N : ℝ) :=
          add_pos_of_pos_of_nonneg L'.property.1 (mul_nonneg hkR hN.le)
        linarith
      · have hkR : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
        nlinarith [L'.property.2]
    have h := Real.rpow_le_rpow_of_nonpos hbase (habs k) hexp
    rwa [Real.mul_rpow hAp.le (abs_nonneg _)] at h
  have hsum (T : {L : ℝ // 0 < L ∧ L < (N : ℝ)}) :
      Summable (fun k : ℤ => |T.val + k * (N : ℝ)| ^ (-p.val.2 - 2)) := by
    have ht := (PeriodicPower.summable_and_le
      (by linarith [p.property.2.1] : 1 < p.val.2 + 2)
      (lt_min T.property.1 (sub_pos.mpr T.property.2))
      (min_le_left T.val ((N : ℝ) - T.val))
      (min_le_right T.val ((N : ℝ) - T.val))).1
    simpa only [show -(p.val.2 + 2) = -p.val.2 - 2 by ring] using ht
  have h := (hsum L).mul_left (A ^ (-p.val.2 - 2))
  have hseries := h.tsum_le_tsum hterm (hsum L')
  rw [tsum_mul_left] at hseries
  rw [PhysicalEnergy.intervalCoefficient_images, PhysicalEnergy.intervalCoefficient_images]
  have hscale := mul_le_mul_of_nonneg_left hseries
    (mul_nonneg p.property.2.1.le (by linarith [p.property.2.1] : 0 ≤ p.val.2 + 1))
  convert hscale using 1
  ring

/-- The one-gap case consists exactly of the full-intersection coefficient. -/
theorem groupedBoundaryMatrix_one (u v : Fin (1 - 1) → ℝ) (d : ℝ) :
    groupedBoundaryMatrix 1 u v d 0 0 = d := by
  simp [groupedBoundaryMatrix_apply]

end Riesz2.BoundaryEntries
