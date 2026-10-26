/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Preliminaries.SymbolBounds

/-!
# The constant mode and spectral positivity of the sampled kernel

The interval identity gives the size of the constant Fourier mode. All other
modes are the positive lattice symbol. Finite Fourier diagonalization then gives
positive definiteness, as in the manuscript proof of Lemma 2.5.
-/

public section

noncomputable section

open Filter Set
open scoped BigOperators Topology Fin.NatCast Fin.IntCast ComplexOrder

namespace Riesz2

/-- The uniform zero-mode estimates of Subsection 2.5, with constants
quantified before the cycle size. -/
theorem sampledRieszKernel_zero_mode_bounds (s : Riesz1.RieszExponent) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)),
      c * (N : ℝ) ^ (1 - s.val) ≤ ∑ k, sampledRieszKernel s N hN k ∧
      (∑ k, sampledRieszKernel s N hN k) ≤ C * (N : ℝ) ^ (1 - s.val) := by
  obtain ⟨c, C, hc, hC, hcurv⟩ := sampledSecondDifference_bounds s
  have hα : 0 < 1 - s.val := by linarith [s.property.2]
  refine ⟨c / 2 * (1 / 3 : ℝ) ^ (1 - s.val), C / (1 - s.val), by positivity,
    div_pos hC hα, ?_⟩
  intro N hN
  let m := (N : ℕ) / 2
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hNpos : (0 : ℝ) < N := by positivity
  have hterm (r : ℕ) (hr : r ∈ Finset.Icc 1 m) :
      (c / 2) * (r : ℝ) ^ (-s.val) ≤
        (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) * (r : ℝ) ^ 2 *
          sampledSecondDifference s N hN (↑r : Fin (N : ℕ)) ∧
      (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) * (r : ℝ) ^ 2 *
          sampledSecondDifference s N hN (↑r : Fin (N : ℕ)) ≤
        C * (r : ℝ) ^ (-s.val) := by
    have hr' := Finset.mem_Icc.mp hr
    have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
    have hrN : r < (N : ℕ) := by dsimp [m] at hr'; omega
    have hrv : (↑r : Fin (N : ℕ)) ≠ 0 := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_natCast, Fin.val_zero, Nat.mod_eq_of_lt hrN] at hv
      omega
    have hdist : Riesz1.cyclicIndexDistance N (↑r : Fin (N : ℕ)) 0 = r := by
      simp only [Riesz1.cyclicIndexDistance, Fin.val_natCast, Fin.val_zero,
        Nat.mod_eq_of_lt hrN, Nat.dist_zero_right]
      apply min_eq_left
      dsimp [m] at hr'
      omega
    have h := hcurv N hN (↑r : Fin (N : ℕ)) hrv
    rw [hdist] at h
    have hw : (1 / 2 : ℝ) ≤ (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) ∧
        (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) ≤ 1 := by
      split_ifs <;> norm_num
    have hid : (r : ℝ) ^ 2 * (r : ℝ) ^ (-s.val - 2) = (r : ℝ) ^ (-s.val) := by
      rw [← Real.rpow_two, ← Real.rpow_add hrpos]
      congr 1
      ring
    have hlow := mul_le_mul_of_nonneg_left h.1
      (mul_nonneg (by linarith : 0 ≤ (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0)) (sq_nonneg (r : ℝ)))
    have hupp := mul_le_mul_of_nonneg_left h.2
      (mul_nonneg (by linarith : 0 ≤ (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0)) (sq_nonneg (r : ℝ)))
    have heq (A : ℝ) :
        (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) * (r : ℝ) ^ 2 *
          (A * (r : ℝ) ^ (-s.val - 2)) =
        A * (r : ℝ) ^ (-s.val) * (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) := by
      rw [show _ * (r : ℝ) ^ 2 * (A * (r : ℝ) ^ (-s.val - 2)) =
        A * ((r : ℝ) ^ 2 * (r : ℝ) ^ (-s.val - 2)) *
          (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) by ring, hid]
    rw [heq] at hlow hupp
    have hpow : 0 ≤ (r : ℝ) ^ (-s.val) := Real.rpow_nonneg hrpos.le _
    constructor
    · have hweight := mul_le_mul_of_nonneg_left hw.1 (mul_nonneg hc.le hpow)
      exact (by nlinarith : c / 2 * (r : ℝ) ^ (-s.val) ≤
        c * (r : ℝ) ^ (-s.val) * (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0)).trans hlow
    · exact hupp.trans (mul_le_of_le_one_right (mul_nonneg hC.le hpow) hw.2)
  have hsums := subcritical_power_sum s.property.1 s.property.2 hm
  rw [sampledRieszKernel_zero_mode]
  have hlow := Finset.sum_le_sum (fun r hr => (hterm r hr).1)
  have hupp := Finset.sum_le_sum (fun r hr => (hterm r hr).2)
  rw [← Finset.mul_sum] at hlow hupp
  have hscale : (1 / 3 : ℝ) * (N : ℝ) ≤ (m : ℝ) := by
    have h : (N : ℕ) ≤ 3 * m := by dsimp [m]; omega
    have hR : (N : ℝ) ≤ 3 * (m : ℝ) := by exact_mod_cast h
    linarith
  have hsmall := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 1 / 3 * (N : ℝ)) hscale hα.le
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 3) hNpos.le] at hsmall
  have hlarge : (m : ℝ) ^ (1 - s.val) ≤ (N : ℝ) ^ (1 - s.val) := by
    apply Real.rpow_le_rpow hmpos.le _ hα.le
    exact_mod_cast (show m ≤ (N : ℕ) by dsimp [m]; omega)
  constructor
  · have h := (mul_le_mul_of_nonneg_left (hsmall.trans hsums.1) (by positivity : (0 : ℝ) ≤ c / 2)).trans hlow
    simpa only [mul_assoc] using h
  · have h := hupp.trans (mul_le_mul_of_nonneg_left hsums.2 hC.le)
    have h' := mul_le_mul_of_nonneg_left hlarge (div_nonneg hC.le hα.le)
    apply h.trans
    convert h' using 1
    ring

/-- Positive definiteness of the actual sampled circulant, Subsection 2.5.
The constant mode is positive by the interval formula, and every nonconstant mode
is the lattice symbol bounded below by discrete convexity. -/
theorem sampledRieszKernel_posDef (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) :
    (Matrix.of (fun a b : Fin (N : ℕ) => sampledRieszKernel s N hN (b - a))).PosDef := by
  have hcomplex : (cycleMatrix N (fun n => (sampledRieszKernel s N hN n : ℂ))).PosDef := by
    apply (cycleMatrix_posDef_iff _).mpr
    intro k
    by_cases hk : k = 0
    · subst k
      obtain ⟨c, _, hc, _, hb⟩ := sampledRieszKernel_zero_mode_bounds s
      have hp : 0 < ∑ n, sampledRieszKernel s N hN n :=
        lt_of_lt_of_le (mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)) (hb N hN).1
      simpa only [cycleFourier, cycleAngle, Fin.val_zero, Nat.cast_zero, mul_zero,
        zero_div, Complex.ofReal_zero, Complex.exp_zero, mul_one,
        ← Complex.ofReal_sum] using Complex.zero_lt_real.mpr hp
    · rw [sampledRieszKernel_nonzero_eigenvalue s N hN k hk]
      exact Complex.zero_lt_real.mpr (lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _)
        (latticeRieszSymbol_lower s _))
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    rw [show a - b = -(b - a) by abel, sampledRieszKernel_even]
  · intro u hu
    have hune : (fun i => (u i : ℂ)) ≠ 0 := by
      intro h
      apply hu
      funext i
      exact Complex.ofReal_injective (congrFun h i)
    have hp := hcomplex.dotProduct_mulVec_pos hune
    have hlabel (a b : Fin (N : ℕ)) :
        Riesz1.labelOf N ((b.val : ℤ) - a.val) = b - a := by
      apply Fin.ext
      apply Int.ofNat_inj.mp
      rw [Riesz1.APG.labelOf_val, Fin.val_sub]
      rw [Int.natCast_emod, Nat.cast_add, Nat.cast_sub (Nat.le_of_lt a.isLt)]
      rw [show ((N : ℕ) : ℤ) - a.val + b.val = ((b.val : ℤ) - a.val) + (N : ℕ) by ring]
      simp only [Int.add_emod, Int.emod_self, add_zero, Int.emod_emod]
    simp only [dotProduct, Matrix.mulVec, cycleMatrix, Matrix.of_apply, hlabel,
      Pi.star_apply, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      ← Complex.ofReal_sum] at hp
    exact (Complex.zero_lt_real.mp hp)

/-- The conclusions of Subsection 2.5: the interval quadratic form, the exact zero mode,
its uniform size estimates, and positive definiteness of the sampled circulant. -/
theorem sampledRieszKernel_interval_quadratic_and_zero_mode (s : Riesz1.RieszExponent) :
    (∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (u : Fin (N : ℕ) → ℝ),
      (∑ a, ∑ b, u a * sampledRieszKernel s N hN (b - a) * u b) =
        ∑ i : Fin (N : ℕ), ∑ r ∈ Finset.Icc 1 ((N : ℕ) / 2),
          (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) *
            sampledSecondDifference s N hN (↑r : Fin (N : ℕ)) *
            (∑ j ∈ cyclicIndexInterval N i r, u j) ^ 2) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)),
      (∑ k : Fin (N : ℕ), sampledRieszKernel s N hN k) =
        ∑ r ∈ Finset.Icc 1 ((N : ℕ) / 2),
          (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) * (r : ℝ) ^ 2 *
            sampledSecondDifference s N hN (↑r : Fin (N : ℕ)) ∧
      c * (N : ℝ) ^ (1 - s.val) ≤ ∑ k, sampledRieszKernel s N hN k ∧
      (∑ k, sampledRieszKernel s N hN k) ≤ C * (N : ℝ) ^ (1 - s.val)) ∧
    ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)),
      (Matrix.of (fun a b : Fin (N : ℕ) => sampledRieszKernel s N hN (b - a))).PosDef := by
  obtain ⟨c, C, hc, hC, hbound⟩ := sampledRieszKernel_zero_mode_bounds s
  exact ⟨sampledRieszKernel_quadratic s,
    ⟨c, C, hc, hC, fun N hN => ⟨sampledRieszKernel_zero_mode s N hN, hbound N hN⟩⟩,
    sampledRieszKernel_posDef s⟩

end Riesz2

end
