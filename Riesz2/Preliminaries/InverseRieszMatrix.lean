/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Preliminaries.ReciprocalSymbol
public import Riesz2.Preliminaries.InverseIntervalKernelPart2
public import Riesz2.ToMathlib.FourierMultiplierKernels

/-!
# Inverse of the sampled Riesz matrix

The matrix is the circulant of the sampled kernel. Its inverse has the
periodized reciprocal coefficients and the prescribed positive constant mode.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Fin.NatCast
open Filter Set

namespace Riesz2

private theorem labelOf_fin_sub (N : ℕ+) (a b : Fin (N : ℕ)) :
    Riesz1.labelOf N ((b.val : ℤ) - a.val) = b - a := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [Riesz1.APG.labelOf_val, Fin.val_sub]
  rw [Int.natCast_emod, Nat.cast_add, Nat.cast_sub (Nat.le_of_lt a.isLt)]
  rw [show ((N : ℕ) : ℤ) - a.val + b.val = ((b.val : ℤ) - a.val) + (N : ℕ) by ring]
  simp only [Int.add_emod, Int.emod_self, add_zero, Int.emod_emod]

/-- The exact inverse formula used in Lemma 2.5, including the
constant mode `1 / (N λ_N)`. The matrix is nonsingular by the positivity theorem. -/
theorem sampledRieszMatrix_inverse_formula (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (i j : Fin (N : ℕ)) :
    ((Matrix.of (fun a b : Fin (N : ℕ) => sampledRieszKernel s N hN (b - a)))⁻¹ i j : ℂ) =
      (∑' l : ℤ, inverseRieszCoefficient s (((j - i).val : ℤ) + l * (N : ℕ))) +
        1 / ((N : ℂ) * ((∑ k, sampledRieszKernel s N hN k : ℝ) : ℂ)) := by
  obtain ⟨_, _, _, hs, _, _, hf, _, _, _⟩ := inverseRieszCoefficient_properties hz s
  obtain ⟨c, _, hc, _, hb⟩ := sampledRieszKernel_zero_mode_bounds s
  have hlpos : 0 < ∑ k, sampledRieszKernel s N hN k :=
    lt_of_lt_of_le (mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)) (hb N hN).1
  have h0 : latticeFourier (inverseRieszCoefficient s) hs 0 = 0 := by
    rw [hf]
    simp only [AddCircle.coe_zero, reciprocalRieszSymbol_zero, Complex.ofReal_zero]
  have hinv (k : Fin (N : ℕ)) (hk : k ≠ 0) :
      latticeFourier (inverseRieszCoefficient s) hs (cycleAngle N k) =
        (cycleFourier N (fun n => (sampledRieszKernel s N hN n : ℂ)) k)⁻¹ := by
    rw [hf, sampledRieszKernel_nonzero_eigenvalue s N hN k hk,
      reciprocalRieszSymbol_coe s ⟨_, cycleAngle_mem_Ioo N k hk⟩, Complex.ofReal_inv]
  have hne (k : Fin (N : ℕ)) (hk : k ≠ 0) :
      cycleFourier N (fun n => (sampledRieszKernel s N hN n : ℂ)) k ≠ 0 := by
    rw [sampledRieszKernel_nonzero_eigenvalue s N hN k hk]
    exact Complex.ofReal_ne_zero.mpr (latticeRieszSymbol_pos s _).ne'
  have hlambda : cycleFourier N (fun n => (sampledRieszKernel s N hN n : ℂ)) 0 =
      ((∑ k, sampledRieszKernel s N hN k : ℝ) : ℂ) := by
    simp [cycleFourier, cycleAngle, Complex.ofReal_sum]
  have heven (x : ℤ) :
      sampledRieszKernel s N hN (Riesz1.labelOf N (-x)) =
        sampledRieszKernel s N hN (Riesz1.labelOf N x) := by
    have hlabel : Riesz1.labelOf N (-x) = -(Riesz1.labelOf N x) := by
      apply Fin.ext
      apply Int.ofNat_inj.mp
      rw [Riesz1.APG.labelOf_val, Fin.val_neg']
      rw [Int.natCast_emod, Nat.cast_sub (Nat.le_of_lt (Riesz1.labelOf N x).isLt),
        Riesz1.APG.labelOf_val]
      rw [Int.neg_emod_eq_sub_emod]
      simp only [Int.sub_emod, Int.emod_self, Int.emod_emod]
    rw [hlabel, sampledRieszKernel_even]
  have h := (inverse_aliasing_real N hN (inverseRieszCoefficient s) hs
    (sampledRieszKernel s N hN) heven _ hlambda hlpos.ne' h0 hinv hne).2 i j
  simpa only [labelOf_fin_sub, periodizeSequence] using h

/-- Every inverse column has exactly the positive mass `λ_N⁻¹`, as required by
the constant-mode assertion of Lemma 2.5. -/
theorem sampledRieszMatrix_inverse_column_sum (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (j : Fin (N : ℕ)) :
    (∑ i, (Matrix.of (fun a b : Fin (N : ℕ) => sampledRieszKernel s N hN (b - a)))⁻¹ i j) =
      (∑ k, sampledRieszKernel s N hN k)⁻¹ := by
  obtain ⟨_, _, _, hs, _, _, _, hzsum, _, _⟩ := inverseRieszCoefficient_properties hz s
  have hsum : (∑ i, ((Matrix.of (fun a b : Fin (N : ℕ) =>
      sampledRieszKernel s N hN (b - a)))⁻¹ i j : ℂ)) =
      ∑ i, (periodizeSequence N (inverseRieszCoefficient s) hs (j - i) +
        1 / ((N : ℂ) * ((∑ k, sampledRieszKernel s N hN k : ℝ) : ℂ))) := by
    exact Finset.sum_congr rfl fun i _ => sampledRieszMatrix_inverse_formula hz s N hN i j
  have hperm : (∑ i, periodizeSequence N (inverseRieszCoefficient s) hs (j - i)) = 0 := by
    have hp := (Equiv.subLeft j).sum_comp (periodizeSequence N (inverseRieszCoefficient s) hs)
    change (∑ i, periodizeSequence N (inverseRieszCoefficient s) hs (j - i)) = _ at hp
    rw [hp, ← tsum_eq_sum_periodizeSequence, hzsum]
  simp only [Finset.sum_add_distrib, ← Complex.ofReal_sum, hperm, zero_add,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast N.ne_zero
  have hcancel : (N : ℂ) * (1 / ((N : ℂ) * ((∑ k, sampledRieszKernel s N hN k : ℝ) : ℂ))) =
      (((∑ k, sampledRieszKernel s N hN k : ℝ) : ℂ))⁻¹ := by
    rw [one_div, mul_inv, ← mul_assoc, mul_inv_cancel₀ hN0, one_mul]
  rw [hcancel] at hsum
  exact Complex.ofReal_injective (hsum.trans (Complex.ofReal_inv _).symm)

/-- The finite inverse-transform formula in Lemma 2.5, Step 2, before
the generic multiplier estimate is applied. It follows directly from the
nonzero Fourier eigenvalues, including the positive constant mode. -/
theorem sampledRieszMatrix_inverse_kernel (s : Riesz1.RieszExponent)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (i j : Fin (N : ℕ)) :
    ((Matrix.of (fun a b : Fin (N : ℕ) => sampledRieszKernel s N hN (b - a)))⁻¹ i j : ℂ) =
      FourierMultiplierKernels.multiplierKernel N
        (fun θ : ℝ => (reciprocalRieszSymbol s (θ : AddCircle (2 * Real.pi)) : ℂ))
        (((∑ k, sampledRieszKernel s N hN k : ℝ)⁻¹ : ℝ) : ℂ) (j - i).val := by
  classical
  let A : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ :=
    Matrix.of fun a b => sampledRieszKernel s N hN (b - a)
  let f := fun n : Fin (N : ℕ) => (sampledRieszKernel s N hN n : ℂ)
  let Φ : Fin (N : ℕ) → ℂ := fun k => if k = 0 then
    (((∑ k, sampledRieszKernel s N hN k : ℝ)⁻¹ : ℝ) : ℂ) else
    (reciprocalRieszSymbol s ((cycleAngle N k : ℝ) : AddCircle (2 * Real.pi)) : ℂ)
  have hpos := sampledRieszKernel_posDef s N hN
  have hmul : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A
    (isUnit_iff_ne_zero.mpr hpos.det_pos.ne')
  have hmap : (A.map Complex.ofRealHom)⁻¹ = (A⁻¹).map Complex.ofRealHom := by
    apply Matrix.inv_eq_right_inv
    rw [← Matrix.map_mul, hmul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcycle : cycleMatrix N f = A.map Complex.ofRealHom := by
    ext a b
    simp only [cycleMatrix, A, f, Matrix.of_apply, Matrix.map_apply, labelOf_fin_sub,
      Complex.ofRealHom_eq_coe]
  have hlambda : 0 < ∑ k, sampledRieszKernel s N hN k := by
    obtain ⟨c, _, hc, _, hb⟩ := sampledRieszKernel_zero_mode_bounds s
    exact lt_of_lt_of_le (by positivity) (hb N hN).1
  have hinv (k : Fin (N : ℕ)) : (cycleFourier N f k)⁻¹ = Φ k := by
    by_cases hk : k = 0
    · subst k
      simp [Φ, f, cycleFourier, cycleAngle, Complex.ofReal_sum, Complex.ofReal_inv]
    · simp only [Φ, ite_eq_right hk]
      rw [sampledRieszKernel_nonzero_eigenvalue s N hN k hk,
        reciprocalRieszSymbol_coe s ⟨_, cycleAngle_mem_Ioo N k hk⟩, Complex.ofReal_inv]
  have hne (k : Fin (N : ℕ)) : cycleFourier N f k ≠ 0 := by
    by_cases hk : k = 0
    · subst k
      simpa only [f, cycleFourier, cycleAngle, Fin.val_zero, Nat.cast_zero,
        mul_zero, zero_div, Complex.ofReal_zero, Complex.exp_zero, mul_one,
        ← Complex.ofReal_sum] using Complex.ofReal_ne_zero.mpr hlambda.ne'
    · rw [sampledRieszKernel_nonzero_eigenvalue s N hN k hk]
      exact Complex.ofReal_ne_zero.mpr (latticeRieszSymbol_pos s _).ne'
  obtain ⟨g, hg, hgf⟩ := cycleMatrix_inv_circulant f hne
  have hge : g = cycleFourierInv N Φ := by
    apply cycleFourier_injective N
    funext k
    rw [hgf, cycleFourier_cycleFourierInv, hinv]
  have hentry : (A⁻¹ i j : ℂ) = (cycleMatrix N f)⁻¹ i j := by
    rw [hcycle, hmap]
    rfl
  change (A⁻¹ i j : ℂ) = _
  rw [hentry, hg, labelOf_fin_sub, hge,
    FourierMultiplierKernels.multiplierKernel_eq_cycleFourierInv, Riesz1.labelOf_natCast]

private theorem cyclicDist_sub_fin (N : ℕ+) (i j : Fin (N : ℕ)) :
    ((Riesz1.cyclicDist N ((j - i).val : ℤ) 0 : ℤ) : ℝ) =
      (Riesz1.cyclicIndexDistance N i j : ℝ) := by
  have h := cyclicIndexDistance_labelOf N ((j - i).val : ℤ) 0
  rw [Riesz1.labelOf_natCast, show Riesz1.labelOf N 0 = (0 : Fin (N : ℕ)) from
    (Riesz1.labelOf_natCast N 0)] at h
  have hd : Riesz1.cyclicIndexDistance N (j - i) 0 = Riesz1.cyclicIndexDistance N i j := by
    simp only [Riesz1.cyclicIndexDistance, Fin.val_zero, Fin.val_sub,
      Nat.dist]
    have hi := i.isLt
    have hj := j.isLt
    by_cases hij : i.val ≤ j.val
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [Nat.mod_eq_of_lt (by omega)]
      omega
  rw [hd] at h
  exact_mod_cast h.symm

/-- Lemma 2.5: positive definiteness, inverse-entry decay and the
column-sum bound. Step 2 applies Lemma 2.4 with `r = 2`,
`α = 1-s` and the reciprocal constant Fourier mode. -/
theorem sampledRieszMatrix_inverse_decay (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)),
      (Matrix.of (fun a b : Fin (N : ℕ) => sampledRieszKernel s N hN (b - a))).PosDef ∧
      (∀ i j : Fin (N : ℕ),
        |(Matrix.of (fun a b : Fin (N : ℕ) => sampledRieszKernel s N hN (b - a)))⁻¹ i j| ≤
          C / (1 + (Riesz1.cyclicIndexDistance N i j : ℝ) ^ (2 - s.val))) ∧
      |∑ i, (Matrix.of (fun a b : Fin (N : ℕ) => sampledRieszKernel s N hN (b - a)))⁻¹ i 0| ≤
        C * (N : ℝ) ^ (s.val - 1) := by
  classical
  obtain ⟨K, hK, hmult⟩ := FourierMultiplierKernels.fourierMultiplier_kernel 2
    (Or.inl rfl) (1 - s.val) (by linarith [s.property.2]) (by norm_num; linarith [s.property.1])
  obtain ⟨B, hB, hderiv⟩ := reciprocalRieszSymbol_complex_derivative_bounds hz s
  obtain ⟨c, _, hc, _, hmode⟩ := sampledRieszKernel_zero_mode_bounds s
  let m := fun θ : ℝ => (reciprocalRieszSymbol s (θ : AddCircle (2 * Real.pi)) : ℂ)
  have hmc : Continuous m :=
    Complex.continuous_ofReal.comp ((continuous_reciprocalRieszSymbol hz s).comp
      (AddCircle.continuous_mk' _))
  have hmp : Function.Periodic m (2 * Real.pi) := by
    intro θ
    dsimp only [m]
    rw [AddCircle.coe_add_period]
  have hm0 : m 0 = 0 := by simp [m, reciprocalRieszSymbol_zero]
  have hms : ContDiffOn ℝ 2 m (Ioo 0 (2 * Real.pi)) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((reciprocalRieszSymbol_contDiffOn hz s).of_le (by norm_num))
  have hmb : ∀ j : ℕ, j ≤ 2 → ∀ θ ∈ Ioo 0 (2 * Real.pi),
      ‖iteratedDeriv j m θ‖ ≤ B * FourierMultiplierKernels.angularRadius θ ^ (1 - s.val - j) := by
    intro j hj θ hθ
    rw [FourierMultiplierKernels.angularRadius_eq_min (Ioo_subset_Icc_self hθ)]
    exact hderiv j hj θ hθ
  refine ⟨2 * K * B + 2 / c + 1 / c, by positivity, ?_⟩
  intro N hN
  have hNpos : (0 : ℝ) < N := by positivity
  let lambda := ∑ k, sampledRieszKernel s N hN k
  have hlower : c * (N : ℝ) ^ (1 - s.val) ≤ lambda := (hmode N hN).1
  have hlambdapos : 0 < lambda := lt_of_lt_of_le (by positivity) hlower
  have hmass : lambda⁻¹ ≤ (1 / c) * (N : ℝ) ^ (s.val - 1) := by
    calc lambda⁻¹ ≤ (c * (N : ℝ) ^ (1 - s.val))⁻¹ := inv_anti₀ (by positivity) hlower
      _ = (1 / c) * (N : ℝ) ^ (s.val - 1) := by
        rw [mul_inv, ← Real.rpow_neg hNpos.le]
        congr 2 <;> ring
  obtain ⟨_, hdecay, hkmass⟩ := hmult B hB N hN m hmc hmp hm0 hms hmb ((lambda⁻¹ : ℝ) : ℂ)
  rw [show 1 + (1 - s.val) = 2 - s.val by ring] at hdecay
  refine ⟨sampledRieszKernel_posDef s N hN, ?_, ?_⟩
  · intro i j
    let d : ℝ := Riesz1.cyclicIndexDistance N i j
    let D := 1 + d ^ (2 - s.val)
    have hd : 0 ≤ d := by dsimp [d]; positivity
    have hD : 0 < D := by dsimp [D]; positivity
    have hdn : 2 * d ≤ (N : ℝ) := by
      dsimp only [d]
      exact_mod_cast Riesz1.APG.cyclicIndexDistance_le_half (N := N) i j
    have hnp := rpow_neg_le_two_div_one_add
      (show 0 ≤ 2 - s.val by linarith [s.property.2])
      (show (1 : ℝ) ≤ N by exact_mod_cast (hN.trans' (by omega : 1 ≤ 2))) hd hdn
    have hconst : lambda⁻¹ / (N : ℝ) ≤ (2 / c) / D := by
      calc lambda⁻¹ / (N : ℝ) = (N : ℝ)⁻¹ * lambda⁻¹ := by ring
           _ ≤ (N : ℝ)⁻¹ * ((1 / c) * (N : ℝ) ^ (s.val - 1)) :=
             mul_le_mul_of_nonneg_left hmass (inv_nonneg.mpr hNpos.le)
           _ = (1 / c) * (N : ℝ) ^ (-(2 - s.val)) := by
             rw [← Real.rpow_neg_one, mul_left_comm, ← Real.rpow_add hNpos]
             congr 2; ring
           _ ≤ (1 / c) * (2 / D) := mul_le_mul_of_nonneg_left hnp (by positivity)
           _ = (2 / c) / D := by ring
    have hbound := hdecay ((j - i).val : ℤ)
    rw [cyclicDist_sub_fin N i j, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hlambdapos)] at hbound
    have hden := (FractionalCuspFourier.cusp_denominator_comparison hd
      (show 0 ≤ 2 - s.val by linarith [s.property.2])).1
    have hmain : K * B / (1 + d) ^ (2 - s.val) ≤ 2 * K * B / D := by
      calc
        _ = (2 * K * B) / (2 * (1 + d) ^ (2 - s.val)) := by ring
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hD hden
    calc
      |(Matrix.of (fun a b : Fin (N : ℕ) => sampledRieszKernel s N hN (b - a)))⁻¹ i j| =
          ‖((Matrix.of (fun a b : Fin (N : ℕ) => sampledRieszKernel s N hN (b - a)))⁻¹ i j : ℂ)‖ :=
        (Complex.norm_real _).symm
      _ ≤ K * B / (1 + d) ^ (2 - s.val) + lambda⁻¹ / (N : ℝ) :=
        sampledRieszMatrix_inverse_kernel s N hN i j ▸ hbound
      _ ≤ (2 * K * B) / D + (2 / c) / D := add_le_add hmain hconst
      _ ≤ (2 * K * B + 2 / c + 1 / c) / D := by
        rw [← add_div]
        exact div_le_div_of_nonneg_right (by have := div_pos zero_lt_one hc; linarith) hD.le
  · have hsum : (∑ i, (Matrix.of (fun a b : Fin (N : ℕ) =>
        sampledRieszKernel s N hN (b - a)))⁻¹ i 0) = lambda⁻¹ := by
      apply Complex.ofReal_injective
      rw [Complex.ofReal_sum]
      calc
        _ = ∑ i : Fin (N : ℕ), FourierMultiplierKernels.multiplierKernel N m
            ((lambda⁻¹ : ℝ) : ℂ) (0 - i).val :=
          Finset.sum_congr rfl (fun i _ => sampledRieszMatrix_inverse_kernel s N hN i 0)
        _ = ∑ h : Fin (N : ℕ), FourierMultiplierKernels.multiplierKernel N m
            ((lambda⁻¹ : ℝ) : ℂ) h.val :=
          (Equiv.subLeft (0 : Fin (N : ℕ))).sum_comp
            (fun h => FourierMultiplierKernels.multiplierKernel N m ((lambda⁻¹ : ℝ) : ℂ) h.val)
        _ = ((lambda⁻¹ : ℝ) : ℂ) := hkmass
    rw [hsum, abs_of_pos (inv_pos.mpr hlambdapos)]
    apply hmass.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hNpos.le _)
    have := mul_pos hK hB
    have := div_pos (by norm_num : (0 : ℝ) < 2) hc
    linarith

end Riesz2
