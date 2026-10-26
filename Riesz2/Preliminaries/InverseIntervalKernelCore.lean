/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Preliminaries.InverseIntervalKernel
public import Riesz2.Preliminaries.LatticeSymbolPart2
public import Riesz2.ToMathlib.PowerTailBounds
public import Riesz2.ToMathlib.SymmetricSumShift
public import Riesz2.ToMathlib.CyclicIntervalPairCount
public import Riesz2.ToMathlib.CyclicIntervals
public import Riesz2.ToMathlib.SubcriticalPowerSum

/-!
# Finite-part periodization and interval identities for the sampled kernel

Analytic bridges for the proof of Lemma 2.5 and its interval consequences.
All sampled values are those of the definitions.
-/

public section

noncomputable section

open Filter Set
open scoped BigOperators Topology Fin.NatCast Fin.IntCast

namespace Riesz2

private theorem fin_intCast_nat (N : ℕ+) (n : ℕ) :
    (((n : ℤ)) : Fin (N : ℕ)) = (n : Fin (N : ℕ)) := by
  rw [Fin.intCast_def']
  simp only [Int.natCast_nonneg, ite_true, Int.natAbs_natCast]

private theorem fin_intCast_neg_one (N : ℕ+) :
    ((-1 : ℤ) : Fin (N : ℕ)) = -(1 : Fin (N : ℕ)) := by
  rw [Fin.intCast_def']
  norm_num

private theorem fin_intCast_zero (N : ℕ+) :
    ((0 : ℤ) : Fin (N : ℕ)) = 0 := by
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) by rfl, fin_intCast_nat]
  rfl

private theorem latticeRieszKernel_scaled (s : Riesz1.RieszExponent) (N : ℕ+)
    (k : ℤ) (hk : (k : ℝ) / (N : ℝ) ∈ Ioo (0 : ℝ) 1) (l : ℤ) :
    latticeRieszKernel s (k + l * (N : ℕ)) =
      (N : ℝ) ^ (-s.val) * |(l : ℝ) + (k : ℝ) / (N : ℝ)| ^ (-s.val) := by
  have hN : (0 : ℝ) < N := by positivity
  have hx : ((k : ℝ) / (N : ℝ) : UnitAddCircle) ≠ 0 :=
    Riesz1.coe_ne_zero_of_mem_Ioo_int 0 _ (by simpa using hk)
  have hne := Riesz1.add_int_ne_zero_of_nonInt hx l
  have heq : ((k + l * (N : ℕ) : ℤ) : ℝ) =
      (N : ℝ) * ((l : ℝ) + (k : ℝ) / (N : ℝ)) := by
    push_cast
    field_simp
    ring
  have hn : k + l * (N : ℕ) ≠ 0 := by
    intro h
    have hreal : ((k + l * (N : ℕ) : ℤ) : ℝ) = 0 := by rw [h]; norm_num
    rw [heq] at hreal
    exact hne ((mul_eq_zero.mp hreal).resolve_left hN.ne')
  rw [latticeRieszKernel, ite_eq_right hn, heq, abs_mul, abs_of_pos hN,
    Real.mul_rpow hN.le (abs_nonneg _)]

/-- The off-diagonal finite-part periodization used in the proof of Lemma 2.5. The normalizing term is kept inside the limit. -/
theorem latticeRieszKernel_finitePart_off_diagonal (s : Riesz1.RieszExponent) (N : ℕ+)
    {k : ℤ} (hk0 : 0 < k) (hkN : k < (N : ℕ)) :
    Tendsto (fun M : ℕ =>
      (∑ l ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), latticeRieszKernel s (k + l * (N : ℕ))) -
        2 * (N : ℝ) ^ (-s.val) * (M : ℝ) ^ (1 - s.val) / (1 - s.val)) atTop
      (𝓝 ((N : ℝ) ^ (-s.val) *
        Riesz1.rieszRepresentative s ((k : ℝ) / (N : ℝ)))) := by
  have hN : (0 : ℝ) < N := by positivity
  have hk : (k : ℝ) / (N : ℝ) ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (by exact_mod_cast hk0) hN,
      (div_lt_one hN).mpr (by exact_mod_cast hkN)⟩
  have hx : ((k : ℝ) / (N : ℝ) : UnitAddCircle) ≠ 0 :=
    Riesz1.coe_ne_zero_of_mem_Ioo_int 0 _ (by simpa using hk)
  have h := ((Riesz1.fundamental_series s).1 _ hx).const_mul ((N : ℝ) ^ (-s.val))
  convert h using 1
  ext M
  simp_rw [latticeRieszKernel_scaled s N k hk]
  rw [← Finset.mul_sum]
  ring

/-- The diagonal finite-part value in the proof of Lemma 2.5.
This uses the prescribed regularization `a_s(0)=2` and the finite-part zeta formula. -/
theorem latticeRieszKernel_finitePart_zero (s : Riesz1.RieszExponent) (N : ℕ+) :
    Tendsto (fun M : ℕ =>
      (∑ l ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), latticeRieszKernel s (l * (N : ℕ))) -
        2 * (N : ℝ) ^ (-s.val) * (M : ℝ) ^ (1 - s.val) / (1 - s.val)) atTop
      (𝓝 (2 + 2 * (N : ℝ) ^ (-s.val) * (riemannZeta (s.val : ℂ)).re)) := by
  have hN : (0 : ℝ) < N := by positivity
  have hz := hurwitzZetaPos_finitePart s.val s.property.1 s.property.2 1 zero_lt_one
  have hzeta : Riesz1.hurwitzZetaPos (s.val : ℂ) 1 = riemannZeta (s.val : ℂ) := by
    rw [Riesz1.hurwitzZetaPos_eq_hurwitzZeta_of_mem zero_lt_one le_rfl]
    rw [AddCircle.coe_period, HurwitzZeta.hurwitzZeta_zero]
  rw [hzeta] at hz
  have ht : Tendsto (fun M : ℕ => ((M : ℝ) + 1) ^ (-s.val)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop s.property.1).comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
    exact h
  have hz' : Tendsto (fun M : ℕ =>
      (∑ n ∈ Finset.range M, ((n : ℝ) + 1) ^ (-s.val)) -
        (M : ℝ) ^ (1 - s.val) / (1 - s.val)) atTop
      (𝓝 (riemannZeta (s.val : ℂ)).re) := by
    convert hz.sub ht using 1
    · ext M
      rw [Finset.sum_range_succ]
      ring
    · simp only [sub_zero]
  have heven : Function.Even (fun l : ℤ => latticeRieszKernel s (l * (N : ℕ))) := by
    intro l
    change latticeRieszKernel s ((-l) * (N : ℕ)) = _
    rw [neg_mul, latticeRieszKernel_even]
  have heq (M : ℕ) :
      (∑ l ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), latticeRieszKernel s (l * (N : ℕ))) =
        2 + 2 * (N : ℝ) ^ (-s.val) *
          ∑ n ∈ Finset.range M, ((n : ℝ) + 1) ^ (-s.val) := by
    rw [Finset.sum_Icc_of_even_eq_range heven, Finset.sum_range_succ']
    have hterm (n : ℕ) : latticeRieszKernel s (((n + 1 : ℕ) : ℤ) * (N : ℕ)) =
        (N : ℝ) ^ (-s.val) * ((n : ℝ) + 1) ^ (-s.val) := by
      have hn : ((n + 1 : ℕ) : ℤ) * (N : ℕ) ≠ 0 := by positivity
      rw [latticeRieszKernel, ite_eq_right hn]
      have hcast : ((((n + 1 : ℕ) : ℤ) * (N : ℕ) : ℤ) : ℝ) =
          ((n : ℝ) + 1) * (N : ℝ) := by push_cast; rfl
      rw [hcast, abs_of_nonneg (by positivity),
        Real.mul_rpow (by positivity : 0 ≤ (n : ℝ) + 1) hN.le]
      ring
    simp_rw [hterm]
    rw [← Finset.mul_sum]
    norm_num [latticeRieszKernel]
    ring
  convert ((hz'.const_mul (2 * (N : ℝ) ^ (-s.val))).const_add 2) using 1
  ext M
  rw [heq]
  ring

private theorem latticeRieszKernel_finitePart_period (s : Riesz1.RieszExponent) (N : ℕ+) :
    Tendsto (fun M : ℕ =>
      (∑ l ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        latticeRieszKernel s ((N : ℕ) + l * (N : ℕ))) -
        2 * (N : ℝ) ^ (-s.val) * (M : ℝ) ^ (1 - s.val) / (1 - s.val)) atTop
      (𝓝 (2 + 2 * (N : ℝ) ^ (-s.val) * (riemannZeta (s.val : ℂ)).re)) := by
  have ht : Tendsto (fun M : ℕ => latticeRieszKernel s ((M : ℤ) * (N : ℕ)))
      atTop (𝓝 0) := by
    have hmul : Tendsto (fun M : ℕ => M * (N : ℕ)) atTop atTop :=
      tendsto_atTop_mono (fun M => Nat.le_mul_of_pos_right M N.pos) tendsto_id
    simpa only [Function.comp_def, Nat.cast_mul] using (tendsto_latticeRieszKernel_nat s).comp hmul
  have ht' := ht.comp (Filter.tendsto_add_atTop_nat 1)
  have h := ((latticeRieszKernel_finitePart_zero s N).add ht').sub ht
  convert h using 1
  · ext M
    have hshift := sum_symmetric_shift
      (fun l : ℤ => latticeRieszKernel s (l * (N : ℕ))) M
    simp only [neg_mul, latticeRieszKernel_even] at hshift
    have heq (l : ℤ) : (N : ℕ) + l * (N : ℕ) = (l + 1) * (N : ℕ) := by ring
    simp_rw [heq]
    rw [hshift]
    simp only [Function.comp_def, Nat.cast_add, Nat.cast_one]
    ring
  · simp only [add_zero, sub_zero]

private theorem latticeRieszKernel_finitePart_neg_one (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) :
    Tendsto (fun M : ℕ =>
      (∑ l ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), latticeRieszKernel s (-1 + l * (N : ℕ))) -
        2 * (N : ℝ) ^ (-s.val) * (M : ℝ) ^ (1 - s.val) / (1 - s.val)) atTop
      (𝓝 ((N : ℝ) ^ (-s.val) * Riesz1.rieszRepresentative s ((1 : ℝ) / (N : ℝ)))) := by
  have h := latticeRieszKernel_finitePart_off_diagonal s N (k := 1) (by norm_num)
    (by exact_mod_cast hN)
  simp only [Int.cast_one] at h
  apply h.congr
  intro M
  congr 1
  symm
  apply Finset.sum_bij (fun l _ => -l)
  · intro l hl
    simp only [Finset.mem_Icc] at hl ⊢
    omega
  · intro a _ b _ hab
    exact neg_injective hab
  · intro b hb
    refine ⟨-b, ?_, by simp⟩
    simp only [Finset.mem_Icc] at hb ⊢
    omega
  · intro l _
    have heq : -1 + l * (N : ℕ) = -(1 + (-l) * (N : ℕ)) := by ring
    rw [heq, latticeRieszKernel_even]

/-- The finite-part identity at all lifts needed for taking a cyclic second difference,
including the regularized diagonal and both wraparound neighbors. This is the identity `g_{N,s}=A_N-c_{N,s}`
used in the proof of Lemma 2.5. -/
theorem sampledRieszKernel_finitePart (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) {k : ℤ} (hk0 : -1 ≤ k) (hkN : k ≤ (N : ℕ)) :
    Tendsto (fun M : ℕ =>
      (∑ l ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), latticeRieszKernel s (k + l * (N : ℕ))) -
        2 * (N : ℝ) ^ (-s.val) * (M : ℝ) ^ (1 - s.val) / (1 - s.val)) atTop
      (𝓝 (sampledRieszKernel s N hN (k : Fin (N : ℕ)) +
        (N : ℝ) ^ (-s.val) *
          Riesz1.rieszRepresentative s ((((N : ℕ) / 2 : ℕ) : ℝ) / (N : ℝ)))) := by
  have hzero : sampledRieszKernel s N hN 0 +
      (N : ℝ) ^ (-s.val) *
        Riesz1.rieszRepresentative s ((((N : ℕ) / 2 : ℕ) : ℝ) / (N : ℝ)) =
      2 + 2 * (N : ℝ) ^ (-s.val) * (riemannZeta (s.val : ℂ)).re := by
    unfold sampledRieszKernel
    simp only [Fin.val_zero]
    change (2 + 2 * (N : ℝ) ^ (-s.val) * (riemannZeta (s.val : ℂ)).re - _) + _ = _
    exact sub_add_cancel _ _
  by_cases hkneg : k = -1
  · subst k
    have hidx := fin_intCast_neg_one N
    rw [hidx, sampledRieszKernel_even,
      sampledRieszKernel_off_diagonal s N hN 1 (by
        change 1 % (N : ℕ) ≠ 0
        rw [Nat.mod_eq_of_lt (by omega : 1 < (N : ℕ))]
        omega)]
    simp only [sub_add_cancel]
    have hone : (1 : Fin (N : ℕ)).val = 1 := by
      change 1 % (N : ℕ) = 1
      exact Nat.mod_eq_of_lt (by omega)
    rw [hone]
    simpa only [Nat.cast_one] using latticeRieszKernel_finitePart_neg_one s N hN
  by_cases hkeq : k = (N : ℕ)
  · subst k
    have hidx : (((N : ℕ) : ℤ) : Fin (N : ℕ)) = 0 := by
      apply Fin.ext
      rw [Fin.val_intCast, Int.emod_self]
      rfl
    rw [hidx, hzero]
    exact latticeRieszKernel_finitePart_period s N
  by_cases hk : k = 0
  · subst k
    simpa only [fin_intCast_zero, zero_add, hzero] using latticeRieszKernel_finitePart_zero s N
  have hkpos : 0 < k := by omega
  have hklt : k < (N : ℕ) := by omega
  have hval : (k : Fin (N : ℕ)).val = k.toNat := by
    rw [Fin.val_intCast, Int.emod_eq_of_lt hkpos.le hklt]
  have hkreal : (k.toNat : ℝ) = (k : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hkpos.le
  rw [sampledRieszKernel_off_diagonal s N hN _ (by rw [hval]; omega), sub_add_cancel,
    hval, hkreal]
  exact latticeRieszKernel_finitePart_off_diagonal s N hkpos hklt

/-- Absolute convergence of the curvature image series at every integer lift,
as required by the proof of Lemma 2.5. -/
theorem summable_norm_latticeRieszCurvature_images (s : Riesz1.RieszExponent) (N : ℕ+)
    (k : ℤ) : Summable (fun l : ℤ => ‖latticeRieszCurvature s (k + l * (N : ℕ))‖) := by
  apply (summable_norm_latticeRieszCurvature s).comp_injective
  intro a b hab
  have hN : ((N : ℕ) : ℤ) ≠ 0 := by exact_mod_cast N.ne_zero
  exact mul_right_cancel₀ hN (add_left_cancel hab)

/-- Exact periodization of the cyclic curvature, the proof of Lemma 2.5. The series is absolutely convergent, including
at residue zero, where no positivity assertion is made. -/
theorem sampledSecondDifference_periodization (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (k : Fin (N : ℕ)) :
    sampledSecondDifference s N hN k =
      ∑' l : ℤ, latticeRieszCurvature s ((k.val : ℤ) + l * (N : ℕ)) := by
  have h0 := sampledRieszKernel_finitePart s N hN (k := k.val) (by omega) (by omega)
  have hp := sampledRieszKernel_finitePart s N hN (k := (k.val : ℤ) + 1)
    (by omega) (by omega)
  have hm := sampledRieszKernel_finitePart s N hN (k := (k.val : ℤ) - 1)
    (by omega) (by omega)
  have hlim : Tendsto (fun M : ℕ =>
      ∑ l ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        latticeRieszCurvature s ((k.val : ℤ) + l * (N : ℕ))) atTop
      (𝓝 (sampledSecondDifference s N hN k)) := by
    convert (hp.add hm).sub (h0.const_mul 2) using 1
    · ext M
      simp only [latticeRieszCurvature, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, ← Finset.mul_sum]
      have heq (l : ℤ) :
          (k.val : ℤ) + l * (N : ℕ) + 1 = (k.val : ℤ) + 1 + l * (N : ℕ) ∧
          (k.val : ℤ) + l * (N : ℕ) - 1 = (k.val : ℤ) - 1 + l * (N : ℕ) := by
        constructor <;> ring
      simp_rw [(heq _).1, (heq _).2]
      ring
    · have hc0 : (((k.val : ℤ)) : Fin (N : ℕ)) = k := by
        rw [fin_intCast_nat, Fin.cast_val_eq_self]
      have hcp : (((k.val : ℤ) + 1 : ℤ) : Fin (N : ℕ)) = k + 1 := by
        rw [show (k.val : ℤ) + 1 = ((k.val + 1 : ℕ) : ℤ) by omega,
          fin_intCast_nat, Nat.cast_add, Nat.cast_one, Fin.cast_val_eq_self]
      have hcm : (((k.val : ℤ) - 1 : ℤ) : Fin (N : ℕ)) = k - 1 := by
        by_cases hk : k.val = 0
        · have hk' : k = 0 := Fin.ext hk
          rw [hk, hk']
          norm_num only [Nat.cast_zero, zero_sub, fin_intCast_neg_one]
        · rw [show (k.val : ℤ) - 1 = ((k.val - 1 : ℕ) : ℤ) by omega,
            fin_intCast_nat]
          apply eq_sub_iff_add_eq.mpr
          change (↑(k.val - 1) : Fin (N : ℕ)) + ↑(1 : ℕ) = k
          rw [← Nat.cast_add, Nat.sub_add_cancel (by omega : 1 ≤ k.val), Fin.cast_val_eq_self]
      rw [hc0, hcp, hcm]
      congr 1
      unfold sampledSecondDifference
      ring
  have hs := (summable_norm_latticeRieszCurvature_images s N k.val).of_norm
  exact tendsto_nhds_unique hlim (hs.hasSum.comp Riesz1.tendsto_Icc_symm_atTop)

/-- Every nonzero lattice curvature is nonnegative, by symmetry and the
positive-site estimate of the proof of Lemma 2.5. -/
theorem latticeRieszCurvature_nonneg_of_ne_zero (s : Riesz1.RieszExponent)
    {k : ℤ} (hk : k ≠ 0) : 0 ≤ latticeRieszCurvature s k := by
  rcases lt_or_gt_of_ne hk with h | h
  · rw [← latticeRieszCurvature_even s k]
    exact latticeRieszCurvature_nonneg s (by omega)
  · exact latticeRieszCurvature_nonneg s (by omega)

/-- Curvature is positive at every nonzero residue. This is the sign consequence
of the proof of Lemma 2.5, before its uniform comparisons. -/
theorem sampledSecondDifference_pos (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) {k : Fin (N : ℕ)} (hk : k ≠ 0) :
    0 < sampledSecondDifference s N hN k := by
  have hkv : 1 ≤ k.val := by
    have : k.val ≠ 0 := fun h => hk (Fin.ext (by simpa using h))
    omega
  have hne (l : ℤ) : (k.val : ℤ) + l * (N : ℕ) ≠ 0 := by
    intro h
    have hdvd : ((N : ℕ) : ℤ) ∣ (k.val : ℤ) := by
      refine ⟨-l, ?_⟩
      linear_combination h
    have habs : |(k.val : ℤ)| < ((N : ℕ) : ℤ) := by
      rw [abs_of_nonneg (by positivity)]
      exact_mod_cast k.isLt
    have := Int.eq_zero_of_abs_lt_dvd hdvd habs
    omega
  rw [sampledSecondDifference_periodization]
  obtain ⟨c, C, hc, _, hbound⟩ := latticeRieszCurvature_bounds s
  have hb := hbound k.val (by exact_mod_cast hkv)
  have hs := (summable_norm_latticeRieszCurvature_images s N k.val).of_norm
  exact lt_of_lt_of_le (hb.1.trans_le hb.2.1)
    (by simpa only [zero_mul, add_zero] using
      hs.le_tsum 0 (fun l _ => latticeRieszCurvature_nonneg_of_ne_zero s (hne l)))

/-- The whole-cycle nonnegativity conclusion of the proof of Lemma 2.5. -/
theorem sampledRieszKernel_nonneg (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (k : Fin (N : ℕ)) : 0 ≤ sampledRieszKernel s N hN k := by
  have hhalf (d : ℕ) (hd : d ≤ (N : ℕ) / 2) :
      0 ≤ sampledRieszKernel s N hN (↑d : Fin (N : ℕ)) := by
    rw [sampledRieszKernel_interval_formula s N hN d hd]
    apply Finset.sum_nonneg
    intro r hr
    have hrange := Finset.mem_Icc.mp hr
    have hrv : (↑r : Fin (N : ℕ)) ≠ 0 := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_natCast, Fin.val_zero, Nat.mod_eq_of_lt (by omega : r < (N : ℕ))] at hv
      omega
    apply mul_nonneg
    · apply mul_nonneg
      · exact sub_nonneg.mpr (by exact_mod_cast (show d ≤ r by omega))
      · split_ifs <;> norm_num
    · exact (sampledSecondDifference_pos s N hN hrv).le
  by_cases hk : k.val ≤ (N : ℕ) / 2
  · simpa only [Fin.cast_val_eq_self] using hhalf k.val hk
  · have hkn : k ≠ 0 := by intro h; subst k; simp at hk
    have hneg : (-k).val ≤ (N : ℕ) / 2 := by
      rw [Fin.val_neg, ite_eq_right hkn]
      omega
    simpa only [Fin.cast_val_eq_self, sampledRieszKernel_even] using hhalf (-k).val hneg

/-- Conclusions from the proof of Lemma 2.5: the triangular identity, all empty
ranges included, and nonnegativity on the entire cycle. -/
theorem sampledRieszKernel_intervals (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) :
    (∀ d : ℕ, d ≤ (N : ℕ) / 2 →
      sampledRieszKernel s N hN (↑d : Fin (N : ℕ)) =
        ∑ r ∈ Finset.Icc (d + 1) ((N : ℕ) / 2),
          ((r : ℝ) - d) * (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) *
            sampledSecondDifference s N hN (↑r : Fin (N : ℕ))) ∧
    ∀ k : Fin (N : ℕ), 0 ≤ sampledRieszKernel s N hN k :=
  ⟨sampledRieszKernel_interval_formula s N hN, sampledRieszKernel_nonneg s N hN⟩

/-- The uniform two-sided cyclic distance comparison of the proof of Lemma 2.5. Constants depend only on the Riesz exponent. -/
theorem sampledSecondDifference_bounds (s : Riesz1.RieszExponent) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (k : Fin (N : ℕ)), k ≠ 0 →
      c * (Riesz1.cyclicIndexDistance N k 0 : ℝ) ^ (-s.val - 2) ≤
        sampledSecondDifference s N hN k ∧
      sampledSecondDifference s N hN k ≤
        C * (Riesz1.cyclicIndexDistance N k 0 : ℝ) ^ (-s.val - 2) := by
  let p := s.val + 2
  have hp : 1 < p := by dsimp [p]; linarith [s.property.1]
  obtain ⟨c, C, hc, hC, hb⟩ := latticeRieszCurvature_bounds s
  obtain ⟨T, hT, htail⟩ := inverse_power_sum hp
  have hbabs (z : ℤ) (hz : z ≠ 0) :
      c * |(z : ℝ)| ^ (-s.val - 2) ≤ latticeRieszCurvature s z ∧
      latticeRieszCurvature s z ≤ C * |(z : ℝ)| ^ (-s.val - 2) := by
    have h := (hb |z| (Int.one_le_abs hz)).2
    rw [Int.cast_abs] at h
    have heq : latticeRieszCurvature s |z| = latticeRieszCurvature s z := by
      rcases le_total 0 z with hz | hz
      · rw [abs_of_nonneg hz]
      · rw [abs_of_nonpos hz, latticeRieszCurvature_even]
    rwa [heq] at h
  refine ⟨c, 2 * C * T, hc, by positivity, ?_⟩
  intro N hN k hk
  let d := Riesz1.cyclicIndexDistance N k 0
  have hd : d = min k.val ((N : ℕ) - k.val) := by
    simp only [d, Riesz1.cyclicIndexDistance, Fin.val_zero, Nat.dist_zero_right]
  have hdpos : 0 < d := by
    have := (cyclicIndexDistance_eq_zero_iff k 0).not.mpr hk
    omega
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hdpos
  have hdint : ((Riesz1.cyclicDist N (k.val : ℤ) 0 : ℤ) : ℝ) = (d : ℝ) := by
    have h := cyclicIndexDistance_labelOf N (k.val : ℤ) 0
    have hlabel : Riesz1.labelOf N (k.val : ℤ) = k := by
      exact Riesz1.labelOf_natCast N k
    have hlabel0 : Riesz1.labelOf N 0 = (0 : Fin (N : ℕ)) := by
      simpa only [Fin.val_zero, Nat.cast_zero] using Riesz1.labelOf_natCast N (0 : Fin (N : ℕ))
    rw [hlabel, hlabel0] at h
    exact_mod_cast h.symm
  have hkv : 1 ≤ k.val := by
    have := (cyclicIndexDistance_eq_zero_iff k 0).not.mpr hk
    rw [Riesz1.cyclicIndexDistance] at this
    have : k.val ≠ 0 := fun h => hk (Fin.ext (by simpa using h))
    omega
  have hne (l : ℤ) : (k.val : ℤ) + l * (N : ℕ) ≠ 0 := by
    intro h
    have hdvd : ((N : ℕ) : ℤ) ∣ (k.val : ℤ) := ⟨-l, by linear_combination h⟩
    have habs : |(k.val : ℤ)| < ((N : ℕ) : ℤ) := by
      rw [abs_of_nonneg (by positivity)]
      exact_mod_cast k.isLt
    have := Int.eq_zero_of_abs_lt_dvd hdvd habs
    omega
  have hs := (summable_norm_latticeRieszCurvature_images s N k.val).of_norm
  rw [sampledSecondDifference_periodization]
  constructor
  · have hrep : ∃ l : ℤ, |(((k.val : ℤ) + l * (N : ℕ) : ℤ) : ℝ)| = (d : ℝ) := by
      by_cases hkd : k.val ≤ (N : ℕ) - k.val
      · refine ⟨0, ?_⟩
        rw [hd, min_eq_left hkd]
        simp
      · refine ⟨-1, ?_⟩
        rw [hd, min_eq_right (by omega)]
        push_cast
        have hltR : (k.val : ℝ) < (N : ℝ) := by exact_mod_cast k.isLt
        rw [abs_of_nonpos (by linarith)]
        rw [Nat.cast_sub k.isLt.le]
        ring
    obtain ⟨l, hl⟩ := hrep
    have h := (hbabs _ (hne l)).1
    rw [hl] at h
    exact h.trans (hs.le_tsum l (fun j _ => latticeRieszCurvature_nonneg_of_ne_zero s (hne j)))
  · obtain ⟨hS, hSbound, _⟩ := htail N hN k.val
    have hterm (l : ℤ) : latticeRieszCurvature s ((k.val : ℤ) + l * (N : ℕ)) ≤
        (2 * C) * (1 / (1 + |(k.val : ℝ) + (l : ℝ) * (N : ℝ)| ^ p)) := by
      have hz : (1 : ℝ) ≤ |(((k.val : ℤ) + l * (N : ℕ) : ℤ) : ℝ)| := by
        exact_mod_cast Int.one_le_abs (hne l)
      have hzpos : 0 < |(((k.val : ℤ) + l * (N : ℕ) : ℤ) : ℝ)| := by linarith
      have ha := Real.one_le_rpow hz (by linarith : 0 ≤ p)
      have hpow := Real.rpow_pos_of_pos hzpos p
      have hden : 0 < 1 + |(((k.val : ℤ) + l * (N : ℕ) : ℤ) : ℝ)| ^ p := by positivity
      have hinv : |(((k.val : ℤ) + l * (N : ℕ) : ℤ) : ℝ)| ^ (-s.val - 2) ≤
          2 / (1 + |(((k.val : ℤ) + l * (N : ℕ) : ℤ) : ℝ)| ^ p) := by
        rw [show -s.val - 2 = -p by dsimp [p]; ring, Real.rpow_neg (abs_nonneg _)]
        rw [← one_div]
        apply (div_le_div_iff₀ hpow hden).mpr
        linarith
      have h := (hbabs _ (hne l)).2.trans (mul_le_mul_of_nonneg_left hinv hC.le)
      convert h using 1
      push_cast
      ring
    calc
      (∑' l : ℤ, latticeRieszCurvature s ((k.val : ℤ) + l * (N : ℕ))) ≤
          ∑' l : ℤ, (2 * C) *
            (1 / (1 + |(k.val : ℝ) + (l : ℝ) * (N : ℝ)| ^ p)) :=
        hs.tsum_le_tsum hterm (hS.mul_left _)
      _ = (2 * C) * ∑' l : ℤ,
          1 / (1 + |(k.val : ℝ) + (l : ℝ) * (N : ℝ)| ^ p) := tsum_mul_left
      _ ≤ (2 * C) * (T / (1 + (d : ℝ) ^ p)) := by
        rw [hdint] at hSbound
        exact mul_le_mul_of_nonneg_left hSbound (by positivity)
      _ ≤ (2 * C * T) * (d : ℝ) ^ (-s.val - 2) := by
        rw [show -s.val - 2 = -p by dsimp [p]; ring, Real.rpow_neg hdR.le]
        have hpow := Real.rpow_pos_of_pos hdR p
        have hden : 0 < 1 + (d : ℝ) ^ p := by positivity
        have hdiv : 1 / (1 + (d : ℝ) ^ p) ≤ 1 / (d : ℝ) ^ p :=
          one_div_le_one_div_of_le hpow (by linarith)
        have h := mul_le_mul_of_nonneg_left hdiv (show 0 ≤ 2 * C * T by positivity)
        convert h using 1 <;> ring

/-- Conclusions from the proof of Lemma 2.5: symmetry, centering, the
absolutely convergent periodized curvature, and uniform distance comparisons. -/
theorem sampledRieszKernel_periodization (s : Riesz1.RieszExponent) :
    (∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)),
      (∀ k, sampledRieszKernel s N hN (-k) = sampledRieszKernel s N hN k) ∧
      sampledRieszKernel s N hN ⟨(N : ℕ) / 2, by omega⟩ = 0 ∧
      ∀ k : Fin (N : ℕ),
        Summable (fun l : ℤ => ‖latticeRieszCurvature s ((k.val : ℤ) + l * (N : ℕ))‖) ∧
        sampledSecondDifference s N hN k =
          ∑' l : ℤ, latticeRieszCurvature s ((k.val : ℤ) + l * (N : ℕ))) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (k : Fin (N : ℕ)), k ≠ 0 →
      c * (Riesz1.cyclicIndexDistance N k 0 : ℝ) ^ (-s.val - 2) ≤
        sampledSecondDifference s N hN k ∧
      sampledSecondDifference s N hN k ≤
        C * (Riesz1.cyclicIndexDistance N k 0 : ℝ) ^ (-s.val - 2)) := by
  refine ⟨fun N hN => ⟨sampledRieszKernel_even s N hN,
    sampledRieszKernel_middle s N hN, fun k => ⟨?_, ?_⟩⟩, sampledSecondDifference_bounds s⟩
  · exact summable_norm_latticeRieszCurvature_images s N k.val
  · exact sampledSecondDifference_periodization s N hN k

private theorem sampledRieszKernel_min (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (k : Fin (N : ℕ)) :
    sampledRieszKernel s N hN k =
      sampledRieszKernel s N hN (↑(min k.val ((N : ℕ) - k.val)) : Fin (N : ℕ)) := by
  by_cases hk : k.val ≤ (N : ℕ) - k.val
  · rw [min_eq_left hk, Fin.cast_val_eq_self]
  · rw [min_eq_right (by omega)]
    have hkn : k ≠ 0 := by intro h; subst k; simp at hk
    have hval : (-k).val = (N : ℕ) - k.val := by rw [Fin.val_neg, ite_eq_right hkn]
    rw [← hval, Fin.cast_val_eq_self, sampledRieszKernel_even]

/-- The full interval matrix is the sampled circulant. This proves the
entrywise identification in Subsection 2.5, including the antipodal case. -/
theorem referenceIntervalMatrix_full (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (a b : Fin (N : ℕ)) :
    referenceIntervalMatrix s N hN 1 a b = sampledRieszKernel s N hN (b - a) := by
  let d := min (b - a).val ((N : ℕ) - (b - a).val)
  have hd : d ≤ (N : ℕ) / 2 := by dsimp [d]; omega
  have hdist : Riesz1.cyclicIndexDistance N a b = d := by
    dsimp [d]
    simp only [Riesz1.cyclicIndexDistance, Nat.dist, Fin.val_sub]
    have ha := a.isLt
    have hb := b.isLt
    by_cases hab : a.val ≤ b.val
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [Nat.mod_eq_of_lt (by omega)]
      omega
  have hlengths : (Finset.range ((N : ℕ) / 2 + 1)).filter (fun r => 1 ≤ r ∧ 1 ≤ r) =
      Finset.Icc 1 ((N : ℕ) / 2) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  unfold referenceIntervalMatrix
  rw [hlengths, Finset.sum_comm]
  have hcount (r : ℕ) (hr : r ∈ Finset.Icc 1 ((N : ℕ) / 2)) :
      (∑ i : Fin (N : ℕ),
        (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) *
          sampledSecondDifference s N hN ⟨r % (N : ℕ), Nat.mod_lt _ N.pos⟩ *
          (if a ∈ cyclicIndexInterval N i r then 1 else 0) *
          (if b ∈ cyclicIndexInterval N i r then 1 else 0)) =
      (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) *
        sampledSecondDifference s N hN (↑r : Fin (N : ℕ)) * ((r - d : ℕ) : ℝ) := by
    have hr' := Finset.mem_Icc.mp hr
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, ← Finset.mul_sum,
      cyclicIndexInterval_pair_count N (by omega) a b, hdist]
    rfl
  rw [Finset.sum_congr rfl hcount, sampledRieszKernel_min s N hN (b - a),
    sampledRieszKernel_interval_formula s N hN d hd]
  have hsub : Finset.Icc (d + 1) ((N : ℕ) / 2) ⊆ Finset.Icc 1 ((N : ℕ) / 2) := by
    intro r hr
    simp only [Finset.mem_Icc] at hr ⊢
    omega
  let F := fun r : ℕ =>
    (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) *
      sampledSecondDifference s N hN (↑r : Fin (N : ℕ)) * ((r - d : ℕ) : ℝ)
  calc
    (∑ r ∈ Finset.Icc 1 ((N : ℕ) / 2), F r) =
        ∑ r ∈ Finset.Icc (d + 1) ((N : ℕ) / 2), F r := by
      symm
      apply Finset.sum_subset hsub
      intro r hr hn
      have hr' := Finset.mem_Icc.mp hr
      have hrd : r ≤ d := by
        have : ¬(d + 1 ≤ r ∧ r ≤ (N : ℕ) / 2) := by simpa only [Finset.mem_Icc] using hn
        omega
      simp only [F, Nat.sub_eq_zero_of_le hrd, Nat.cast_zero, mul_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      have hr' := Finset.mem_Icc.mp hr
      dsimp [F]
      rw [Nat.cast_sub (by omega : d ≤ r)]
      ring

/-- The sampled-circulant quadratic identity of Subsection 2.5, using the
literal intervals and their antipodal weights. -/
theorem sampledRieszKernel_quadratic (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (u : Fin (N : ℕ) → ℝ) :
    (∑ a, ∑ b, u a * sampledRieszKernel s N hN (b - a) * u b) =
      ∑ i : Fin (N : ℕ), ∑ r ∈ Finset.Icc 1 ((N : ℕ) / 2),
        (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) *
          sampledSecondDifference s N hN (↑r : Fin (N : ℕ)) *
          (∑ j ∈ cyclicIndexInterval N i r, u j) ^ 2 := by
  simp_rw [← referenceIntervalMatrix_full s N hN]
  rw [referenceIntervalMatrix_quadratic]
  have hlengths : (Finset.range ((N : ℕ) / 2 + 1)).filter (fun r => 1 ≤ r ∧ 1 ≤ r) =
      Finset.Icc 1 ((N : ℕ) / 2) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    omega
  rw [hlengths]

/-- The interval is the integer-label interval at its actual start.
This bridge preserves the original `Fin N` labels. -/
theorem cyclicIndexInterval_eq_cyclicInterval (N : ℕ+) (i : Fin (N : ℕ)) (r : ℕ) :
    cyclicIndexInterval N i r = cyclicInterval N (i.val : ℤ) r := by
  unfold cyclicIndexInterval cyclicInterval
  apply Finset.image_congr
  intro t _
  apply Fin.ext
  apply Int.ofNat_inj.mp
  change (((i.val + t) % (N : ℕ) : ℕ) : ℤ) =
    ((Riesz1.labelOf N ((i.val : ℤ) + t)).val : ℤ)
  rw [Riesz1.APG.labelOf_val]
  push_cast
  rfl

/-- Cardinality of an actual interval without repeated labels. -/
theorem card_cyclicIndexInterval (N : ℕ+) (i : Fin (N : ℕ)) {r : ℕ} (hr : r ≤ (N : ℕ)) :
    (cyclicIndexInterval N i r).card = r := by
  rw [cyclicIndexInterval_eq_cyclicInterval]
  exact card_cyclicInterval _ hr

/-- The exact zero-mode formula in Subsection 2.5. -/
theorem sampledRieszKernel_zero_mode (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) :
    (∑ k : Fin (N : ℕ), sampledRieszKernel s N hN k) =
      ∑ r ∈ Finset.Icc 1 ((N : ℕ) / 2),
        (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) * (r : ℝ) ^ 2 *
          sampledSecondDifference s N hN (↑r : Fin (N : ℕ)) := by
  have h := sampledRieszKernel_quadratic s N hN (fun _ => 1)
  simp only [one_mul, mul_one] at h
  have hrow (a : Fin (N : ℕ)) :
      (∑ b, sampledRieszKernel s N hN (b - a)) = ∑ k, sampledRieszKernel s N hN k :=
    (Equiv.subRight a).sum_comp _
  simp_rw [hrow] at h
  have hright (i : Fin (N : ℕ)) :
      (∑ r ∈ Finset.Icc 1 ((N : ℕ) / 2),
        (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) *
          sampledSecondDifference s N hN (↑r : Fin (N : ℕ)) *
          (∑ _j ∈ cyclicIndexInterval N i r, (1 : ℝ)) ^ 2) =
      ∑ r ∈ Finset.Icc 1 ((N : ℕ) / 2),
        (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) * (r : ℝ) ^ 2 *
          sampledSecondDifference s N hN (↑r : Fin (N : ℕ)) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hr' := Finset.mem_Icc.mp hr
    rw [Finset.sum_const, card_cyclicIndexInterval N i (by omega : r ≤ (N : ℕ))]
    simp only [nsmul_eq_mul, mul_one]
    ring
  simp_rw [hright] at h
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  exact mul_left_cancel₀ (by positivity : (N : ℝ) ≠ 0) h

end Riesz2

end
