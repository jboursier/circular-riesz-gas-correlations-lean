/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.ReferenceIntervalMatrix
public import Riesz2.Bridges.KernelIdentification
public import Riesz2.ToMathlib.DiscreteIntervalReconstruction
public import Riesz2.ToMathlib.FiniteRankOneQuadratic

/-!
# The sampled kernel and its interval curvature representation

All kernel values and curvatures refer to the literal definitions.
The elementary reconstruction does not require any Fourier or inverse-matrix assumption.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Fin.NatCast

namespace Riesz2

/-- The sampled kernel vanishes at the centering point, as in the proof of Lemma 2.5. This includes the sizes two and three. -/
theorem sampledRieszKernel_middle (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) :
    sampledRieszKernel s N hN
      ⟨(N : ℕ) / 2, by have := N.pos; omega⟩ = 0 := by
  have hhalf : (N : ℕ) / 2 ≠ 0 := by omega
  simp [sampledRieszKernel, hhalf]

/-- The off-diagonal branch of the sampled kernel, expressed through the
literal Riesz 1 real representative (Subsection 2.4). -/
theorem sampledRieszKernel_off_diagonal (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (k : Fin (N : ℕ)) (hk : k.val ≠ 0) :
    sampledRieszKernel s N hN k =
      (N : ℝ) ^ (-s.val) * Riesz1.rieszRepresentative s ((k.val : ℝ) / (N : ℝ)) -
        (N : ℝ) ^ (-s.val) *
          Riesz1.rieszRepresentative s ((((N : ℕ) / 2 : ℕ) : ℝ) / (N : ℝ)) := by
  simp only [sampledRieszKernel, hk, dite_false]
  rfl

/-- Evenness of the sampled kernel (the proof of Lemma 2.5). -/
theorem sampledRieszKernel_even (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (k : Fin (N : ℕ)) :
    sampledRieszKernel s N hN (-k) = sampledRieszKernel s N hN k := by
  by_cases hk : k = 0
  · subst k
    simp
  have hkval : k.val ≠ 0 := fun h => hk (Fin.ext (by simpa using h))
  have hkneg : (-k).val ≠ 0 := by
    rw [Fin.val_neg, ite_eq_right hk]
    have := k.isLt
    omega
  rw [sampledRieszKernel_off_diagonal s N hN (-k) hkneg,
    sampledRieszKernel_off_diagonal s N hN k hkval]
  congr 2
  have hratio : ((-k).val : ℝ) / (N : ℝ) = 1 + -((k.val : ℝ) / (N : ℝ)) := by
    rw [Fin.val_neg, ite_eq_right hk, Nat.cast_sub (Nat.le_of_lt k.isLt)]
    have hNne : (N : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [hratio, add_comm (1 : ℝ)]
  exact ((companionFundamentalRepresentation s).2.2.2.2.1
    (-((k.val : ℝ) / (N : ℝ)))).trans
      ((companionFundamentalRepresentation s).2.2.2.1 _)

/-- Rewrite the curvature at a positive natural index without cyclic
subtraction in the predecessor index. -/
theorem sampledSecondDifference_natCast (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) {r : ℕ} (hr : 1 ≤ r) :
    sampledSecondDifference s N hN (↑r : Fin (N : ℕ)) =
      sampledRieszKernel s N hN (↑(r + 1) : Fin (N : ℕ)) +
      sampledRieszKernel s N hN (↑(r - 1) : Fin (N : ℕ)) -
        2 * sampledRieszKernel s N hN (↑r : Fin (N : ℕ)) := by
  have hprev : (↑r : Fin (N : ℕ)) - 1 = ↑(r - 1) := by
    apply sub_eq_iff_eq_add.mpr
    change (↑r : Fin (N : ℕ)) = ↑(r - 1) + ↑(1 : ℕ)
    rw [← Nat.cast_add, Nat.sub_add_cancel hr]
  simp only [sampledSecondDifference, Nat.cast_add, Nat.cast_one, hprev]

/-- The endpoint first difference, including the antipodal half weight. This is
the boundary calculation in the proof of Lemma 2.5. -/
theorem sampledSecondDifference_middle_weight (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) :
    (1 - if 2 * ((N : ℕ) / 2) = (N : ℕ) then (1 / 2 : ℝ) else 0) *
        sampledSecondDifference s N hN (↑((N : ℕ) / 2) : Fin (N : ℕ)) =
      sampledRieszKernel s N hN (↑((N : ℕ) / 2 - 1) : Fin (N : ℕ)) -
        sampledRieszKernel s N hN (↑((N : ℕ) / 2) : Fin (N : ℕ)) := by
  have hm : 1 ≤ (N : ℕ) / 2 := by omega
  rw [sampledSecondDifference_natCast s N hN hm]
  by_cases heven : 2 * ((N : ℕ) / 2) = (N : ℕ)
  · rw [ite_eq_left heven]
    have hindex : (↑((N : ℕ) / 2 + 1) : Fin (N : ℕ)) =
        -(↑((N : ℕ) / 2 - 1) : Fin (N : ℕ)) := by
      apply Fin.ext
      simp only [Fin.val_natCast, Fin.val_neg']
      have hlt : (N : ℕ) / 2 - 1 < (N : ℕ) := by omega
      rw [Nat.mod_eq_of_lt hlt]
      congr 1
      omega
    rw [hindex, sampledRieszKernel_even]
    ring
  · rw [ite_eq_right heven]
    have hodd : (N : ℕ) = 2 * ((N : ℕ) / 2) + 1 := by omega
    have hindex : (↑((N : ℕ) / 2 + 1) : Fin (N : ℕ)) =
        -(↑((N : ℕ) / 2) : Fin (N : ℕ)) := by
      apply Fin.ext
      simp only [Fin.val_natCast, Fin.val_neg']
      have hlt : (N : ℕ) / 2 < (N : ℕ) := by omega
      rw [Nat.mod_eq_of_lt hlt]
      congr 1
      omega
    rw [hindex, sampledRieszKernel_even]
    ring

/-- The exact triangular identity in the proof of Lemma 2.5.
The nonnegativity consequence is separate from this algebraic reconstruction. -/
theorem sampledRieszKernel_interval_formula (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (d : ℕ) (hd : d ≤ (N : ℕ) / 2) :
    sampledRieszKernel s N hN (↑d : Fin (N : ℕ)) =
      ∑ r ∈ Finset.Icc (d + 1) ((N : ℕ) / 2),
        ((r : ℝ) - d) * (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) *
          sampledSecondDifference s N hN (↑r : Fin (N : ℕ)) := by
  have h := triangular_reconstruction
    (fun r => sampledRieszKernel s N hN (↑r : Fin (N : ℕ)))
    (fun r => (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) *
      sampledSecondDifference s N hN (↑r : Fin (N : ℕ))) hd ?_
    (sampledSecondDifference_middle_weight s N hN)
  · have hmiddle : sampledRieszKernel s N hN
        (↑((N : ℕ) / 2) : Fin (N : ℕ)) = 0 := by
      convert sampledRieszKernel_middle s N hN using 2
      apply Fin.ext
      simp only [Fin.val_natCast]
      exact Nat.mod_eq_of_lt (by omega)
    simp only [hmiddle, sub_zero] at h
    simpa only [mul_assoc] using h
  · intro r hdr hrm
    have hr : 1 ≤ r := by omega
    have hnot : 2 * r ≠ (N : ℕ) := by omega
    rw [ite_eq_right hnot, sub_zero, one_mul, sampledSecondDifference_natCast s N hN hr]
    ring

/-- The interval matrix has its defining quadratic form on actual cyclic
intervals. This is the bridge to the rank-one side of Subsection 2.5, and
works for every truncation `K`, including an empty truncation. It does not yet
identify the untruncated matrix with the sampled circulant. -/
theorem referenceIntervalMatrix_quadratic (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (K : ℕ) (u : Fin (N : ℕ) → ℝ) :
    (∑ a, ∑ b, u a * referenceIntervalMatrix s N hN K a b * u b) =
      ∑ i : Fin (N : ℕ),
        ∑ r ∈ (Finset.range ((N : ℕ) / 2 + 1)).filter (fun r => 1 ≤ r ∧ K ≤ r),
          (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) *
            sampledSecondDifference s N hN (↑r : Fin (N : ℕ)) *
            (∑ j ∈ cyclicIndexInterval N i r, u j) ^ 2 := by
  let lengths := (Finset.range ((N : ℕ) / 2 + 1)).filter (fun r => 1 ≤ r ∧ K ≤ r)
  have h := sum_quadratic_rankOne
    (κ := Fin (N : ℕ) × ℕ) (Finset.univ.product lengths)
    (fun p => (1 - if 2 * p.2 = (N : ℕ) then (1 / 2 : ℝ) else 0) *
      sampledSecondDifference s N hN (↑p.2 : Fin (N : ℕ)))
    (fun p j => if j ∈ cyclicIndexInterval N p.1 p.2 then (1 : ℝ) else 0) u
  simp only [Finset.product_eq_sprod, Finset.sum_product] at h
  have hinterval (i : Fin (N : ℕ)) (r : ℕ) :
      (∑ j : Fin (N : ℕ), (if j ∈ cyclicIndexInterval N i r then (1 : ℝ) else 0) * u j) =
        ∑ j ∈ cyclicIndexInterval N i r, u j := by
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
  simp only [hinterval] at h
  unfold referenceIntervalMatrix
  exact h

end Riesz2

end
end
