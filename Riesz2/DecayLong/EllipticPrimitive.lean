/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.GlobalReferenceError
public import Riesz2.DecayLong.GlobalSums
public import Riesz2.DecayLong.EllipticKernelTranslation
public import Riesz2.ToMathlib.FiniteSchurBounds
public import Riesz2.ToMathlib.CoerciveSolutionMaps
public import Riesz2.DecayLong.DiscreteInterpolation

/-!
# Elliptic reference error and primitive estimates

The comparison is with twice the full sampled matrix. The matrix
assumptions themselves compare with the truncated interval matrix. The discarded
intervals are estimated separately.
-/

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset
open scoped BigOperators Fin.NatCast

namespace Riesz2.EllipticPrimitive

/-- The coefficient bounds used when restoring short reference intervals.
The antipodal coefficient retains its half weight. -/
theorem reference_coefficient_bounds (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (r : ℕ),
      1 ≤ r → r ≤ (N : ℕ) / 2 →
      let w := (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) *
        sampledSecondDifference s N hN (↑r : Fin (N : ℕ))
      0 ≤ w ∧ w ≤ C * (r : ℝ) ^ (-s.val - 2) := by
  obtain ⟨c, C, _, hC, hb⟩ := sampledSecondDifference_bounds s
  refine ⟨C, hC, fun N hN r hr hrN => ?_⟩
  have hrlt : r < (N : ℕ) := by omega
  have hne : (↑r : Fin (N : ℕ)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_natCast, Nat.mod_eq_of_lt hrlt, Fin.val_zero] at hv
    omega
  have hd : Riesz1.cyclicIndexDistance N (↑r : Fin (N : ℕ)) 0 = r := by
    simp only [Riesz1.cyclicIndexDistance, Fin.val_natCast, Nat.mod_eq_of_lt hrlt,
      Fin.val_zero, Nat.dist_zero_right]
    omega
  have hpos := (sampledSecondDifference_pos s N hN hne).le
  have hu := (hb N hN _ hne).2
  rw [hd] at hu
  dsimp only
  split_ifs <;> constructor <;> nlinarith

/-- Restoring intervals with length below `K`, entry by entry. This is the
full-reference bridge required by the proof of Lemma 5.9. -/
theorem reference_removed_entry (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (K : ℕ) (a b : Fin (N : ℕ)) :
    referenceIntervalMatrix s N hN 1 a b - referenceIntervalMatrix s N hN K a b =
      ∑ i : Fin (N : ℕ),
        ∑ r ∈ (Finset.range ((N : ℕ) / 2 + 1)).filter (fun r => 1 ≤ r ∧ r < K),
          (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) *
            sampledSecondDifference s N hN (↑r : Fin (N : ℕ)) *
            (if a ∈ cyclicIndexInterval N i r then 1 else 0) *
            (if b ∈ cyclicIndexInterval N i r then 1 else 0) := by
  unfold referenceIntervalMatrix
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  by_cases h1 : 1 ≤ r <;> by_cases hK : K ≤ r <;>
    simp [h1, hK, show (r < K) ↔ ¬K ≤ r by omega]; rfl

/-- The exact row mass of the discarded interval matrix. -/
theorem reference_removed_row (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (K : ℕ) (a : Fin (N : ℕ)) :
    (∑ b, (referenceIntervalMatrix s N hN 1 a b - referenceIntervalMatrix s N hN K a b)) =
      ∑ r ∈ (Finset.range ((N : ℕ) / 2 + 1)).filter (fun r => 1 ≤ r ∧ r < K),
        (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) *
          sampledSecondDifference s N hN (↑r : Fin (N : ℕ)) * (r : ℝ) ^ 2 := by
  simp_rw [reference_removed_entry]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; intro i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  have hr' := Finset.mem_filter.mp hr
  have hrN : r ≤ (N : ℕ) := by have := Finset.mem_range.mp hr'.1; omega
  have hrhalf : 2 * r ≤ (N : ℕ) := by have := Finset.mem_range.mp hr'.1; omega
  have hcard (i : Fin (N : ℕ)) :
      (∑ b : Fin (N : ℕ), if b ∈ cyclicIndexInterval N i r then (1 : ℝ) else 0) = r := by
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
      card_cyclicIndexInterval N i hrN, nsmul_eq_mul, mul_one]
  simp_rw [← Finset.mul_sum, hcard]
  have hcount := cyclicIndexInterval_pair_count N hrhalf a a
  have hid (i : Fin (N : ℕ)) :
      (if a ∈ cyclicIndexInterval N i r then (1 : ℝ) else 0) *
        (if a ∈ cyclicIndexInterval N i r then 1 else 0) =
      (if a ∈ cyclicIndexInterval N i r then 1 else 0) := by
    split_ifs <;> norm_num
  simp_rw [hid] at hcount
  have hd : Riesz1.cyclicIndexDistance N a a = 0 := by simp [Riesz1.cyclicIndexDistance]
  rw [hd, Nat.sub_zero] at hcount
  rw [← Finset.sum_mul, ← Finset.mul_sum, hcount]
  ring

/-- Discarded reference intervals are nonnegative entrywise. -/
theorem reference_removed_nonneg (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (K : ℕ) (a b : Fin (N : ℕ)) :
    0 ≤ referenceIntervalMatrix s N hN 1 a b - referenceIntervalMatrix s N hN K a b := by
  obtain ⟨C, _, hb⟩ := reference_coefficient_bounds s
  rw [reference_removed_entry]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro r hr
  have hr' := Finset.mem_filter.mp hr
  have hw := (hb N hN r hr'.2.1 (by have := Finset.mem_range.mp hr'.1; omega)).1
  exact mul_nonneg (mul_nonneg hw (by split_ifs <;> norm_num)) (by split_ifs <;> norm_num)

/-- The discarded short intervals have row mass `O(K^(1-s))`, uniformly in
cycle size. No comparison between `m` and `n` is used here. -/
theorem reference_removed_row_bound (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K : ℕ), 1 ≤ K →
      ∀ a : Fin (N : ℕ),
      (∑ b, |referenceIntervalMatrix s N hN 1 a b - referenceIntervalMatrix s N hN K a b|) ≤
        C * (K : ℝ) ^ (1 - s.val) := by
  obtain ⟨C, hC, hb⟩ := reference_coefficient_bounds s
  refine ⟨C / (1 - s.val), div_pos hC (by linarith [s.property.2]),
    fun N hN K hK a => ?_⟩
  simp_rw [abs_of_nonneg (reference_removed_nonneg s N hN K a _)]
  rw [reference_removed_row]
  calc
    _ ≤ ∑ r ∈ (Finset.range ((N : ℕ) / 2 + 1)).filter (fun r => 1 ≤ r ∧ r < K),
        C * (r : ℝ) ^ (-s.val) := by
      apply Finset.sum_le_sum
      intro r hr
      have hr' := Finset.mem_filter.mp hr
      have hr0 : (0 : ℝ) < r := by exact_mod_cast hr'.2.1
      have hw := (hb N hN r hr'.2.1 (by have := Finset.mem_range.mp hr'.1; omega)).2
      calc
        _ ≤ (C * (r : ℝ) ^ (-s.val - 2)) * (r : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hw (sq_nonneg _)
        _ = C * (r : ℝ) ^ (-s.val) := by
          rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hr0]
          congr 2
          ring
    _ ≤ ∑ r ∈ Finset.Icc 1 K, C * (r : ℝ) ^ (-s.val) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro r hr
        have hr' := (Finset.mem_filter.mp hr).2
        exact Finset.mem_Icc.mpr ⟨hr'.1, by omega⟩
      · intro r hr _
        exact mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = C * ∑ r ∈ Finset.Icc 1 K, (r : ℝ) ^ (-s.val) := by rw [Finset.mul_sum]
    _ ≤ C * ((K : ℝ) ^ (1 - s.val) / (1 - s.val)) :=
      mul_le_mul_of_nonneg_left (subcritical_power_sum s.property.1 s.property.2 hK).2 hC.le
    _ = _ := by ring

/-- The truncated error is summable on every cycle, with a constant
independent of the active and component sizes. -/
theorem truncated_error_sums (s : Riesz1.RieszExponent) :
    ∃ T : ℝ, 0 < T ∧ ∀ {α : Type*} [MeasurableSpace α] (ν : Measure α)
      (n m : ℕ+) (hm : 2 ≤ (m : ℕ)) (K : ℕ) (C κ γ ε : ℝ), 0 ≤ C →
      ∀ M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
      PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M →
      ∀ᵐ x ∂ν, ∀ i,
        (∑ j, |M x i j - ((2 : ℝ) • referenceIntervalMatrix s m hm K) i j|) ≤
          T * C * (n : ℝ) ^ (κ * ε) := by
  let g : ℕ → ℝ := fun k => (1 + (k : ℝ)) ^ (-1 - s.val / 2)
  have hg0 : ∀ k, 0 ≤ g k := fun k => by dsimp [g]; positivity
  have hgs : Summable g := by
    simpa only [g, show -(1 + s.val / 2) = -1 - s.val / 2 by ring] using
      summable_one_add_rpow_neg (by linarith [s.property.1] : 1 < 1 + s.val / 2)
  have hT : 0 < 2 * ∑' k, g k := by
    have h := hgs.le_tsum 0 (fun k _ => hg0 k)
    have hg : g 0 = 1 := by simp [g]
    rw [hg] at h
    linarith
  refine ⟨2 * ∑' k, g k, hT, fun {α} _ ν n m hm K C κ γ ε hC M hM => ?_⟩
  filter_upwards [periodizedMatrixBounds_truncated_error s n m hm K C κ γ ε hC M hM]
    with x hx
  intro i
  calc
    _ ≤ ∑ j, C * (n : ℝ) ^ (κ * ε) * g (Riesz1.cyclicIndexDistance m i j) :=
      Finset.sum_le_sum fun j _ => hx i j
    _ = C * (n : ℝ) ^ (κ * ε) * ∑ j, g (Riesz1.cyclicIndexDistance m i j) := by
      rw [Finset.mul_sum]
    _ ≤ C * (n : ℝ) ^ (κ * ε) * (2 * ∑' k, g k) :=
      mul_le_mul_of_nonneg_left (sum_le_two_mul_tsum_cyclicIndexDistance m i hg0 hgs)
        (by positivity)
    _ = _ := by ring

/-- Row and column bounds around the full reference, before substituting the
polynomial cutoff. This also makes the short-interval contribution explicit. -/
theorem full_reference_error_sums (s : Riesz1.RieszExponent) :
    ∃ T D : ℝ, 0 < T ∧ 0 < D ∧
      ∀ {α : Type*} [MeasurableSpace α] (ν : Measure α)
      (n m : ℕ+) (hm : 2 ≤ (m : ℕ)) (K : ℕ), 1 ≤ K →
      ∀ C κ γ ε : ℝ, 0 ≤ C →
      ∀ M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
      PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M →
      ∀ᵐ x ∂ν, ∀ i,
        (∑ j, |M x i j - 2 * sampledRieszKernel s m hm (j - i)|) ≤
          T * C * (n : ℝ) ^ (κ * ε) + 2 * D * (K : ℝ) ^ (1 - s.val) ∧
        (∑ j, |M x j i - 2 * sampledRieszKernel s m hm (i - j)|) ≤
          T * C * (n : ℝ) ^ (κ * ε) + 2 * D * (K : ℝ) ^ (1 - s.val) := by
  obtain ⟨T, hT, htrunc⟩ := truncated_error_sums s
  obtain ⟨D, hD, hshort⟩ := reference_removed_row_bound s
  refine ⟨T, D, hT, hD, fun {α} _ ν n m hm K hK C κ γ ε hC M hM => ?_⟩
  filter_upwards [htrunc ν n m hm K C κ γ ε hC M hM, hM.2.1] with x hx hsym
  have hrow (i : Fin (m : ℕ)) :
      (∑ j, |M x i j - 2 * sampledRieszKernel s m hm (j - i)|) ≤
        T * C * (n : ℝ) ^ (κ * ε) + 2 * D * (K : ℝ) ^ (1 - s.val) := by
    calc
      _ ≤ ∑ j, (|M x i j - 2 * referenceIntervalMatrix s m hm K i j| +
          2 * |referenceIntervalMatrix s m hm 1 i j - referenceIntervalMatrix s m hm K i j|) := by
        apply Finset.sum_le_sum
        intro j _
        rw [← referenceIntervalMatrix_full s m hm i j]
        have h := abs_sub (M x i j - 2 * referenceIntervalMatrix s m hm K i j)
          (2 * (referenceIntervalMatrix s m hm 1 i j - referenceIntervalMatrix s m hm K i j))
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
        convert h using 1; congr 1; ring
      _ = (∑ j, |M x i j - 2 * referenceIntervalMatrix s m hm K i j|) +
          2 * ∑ j, |referenceIntervalMatrix s m hm 1 i j - referenceIntervalMatrix s m hm K i j| := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left (hshort m hm K hK i) (by norm_num : (0 : ℝ) ≤ 2)
        have hi := hx i
        simp only [Matrix.smul_apply, smul_eq_mul] at hi
        nlinarith
  intro i
  refine ⟨hrow i, ?_⟩
  have he (j : Fin (m : ℕ)) :
      |M x j i - 2 * sampledRieszKernel s m hm (i - j)| =
        |M x i j - 2 * sampledRieszKernel s m hm (j - i)| := by
    rw [hsym.1 j i, show i - j = -(j - i) by abel, sampledRieszKernel_even]
  simpa only [he] using hrow i

/-- See the proof of Lemma 5.9 in the paper: the sum of the maximum row mass and
maximum column mass is polynomially bounded around twice the full sampled
reference, and the same bound controls `ℓ¹` and `ℓ²` on real or complex
sequences. The pair of arbitrary labels encodes the two finite suprema.
The exponent is chosen before `ε` and before all sizes. -/
theorem elliptic_error (s : Riesz1.RieszExponent) (Cstar κstar γstar : ℝ)
    (hCstar : 1 ≤ Cstar) (hκstar : 0 < κstar) (M₀ : ℕ) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧
      ∀ (ε : ℝ), 0 < ε →
      ∀ {α : Type*} [MeasurableSpace α] (ν : Measure α)
      (n m : ℕ+) (hm : 2 ≤ (m : ℕ)),
      let K := ⌊(n : ℝ) ^ ε⌋₊ ^ M₀
      1 ≤ K →
      ∀ M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
      PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M →
      ∀ᵐ x ∂ν,
        let E := fun i j => M x i j - 2 * sampledRieszKernel s m hm (j - i)
        (∀ i j, (∑ k, |E i k|) + (∑ k, |E k j|) ≤ C * (n : ℝ) ^ (κ * ε)) ∧
        (∀ u : Fin (m : ℕ) → ℝ,
          (∑ i, |∑ j, E i j * u j|) ≤ C * (n : ℝ) ^ (κ * ε) * ∑ j, |u j| ∧
          Real.sqrt (∑ i, (∑ j, E i j * u j) ^ 2) ≤
            C * (n : ℝ) ^ (κ * ε) * Real.sqrt (∑ j, u j ^ 2)) ∧
        (∀ u : Fin (m : ℕ) → ℂ,
          (∑ i, ‖∑ j, (E i j : ℂ) * u j‖) ≤ C * (n : ℝ) ^ (κ * ε) * ∑ j, ‖u j‖ ∧
          Real.sqrt (∑ i, ‖∑ j, (E i j : ℂ) * u j‖ ^ 2) ≤
            C * (n : ℝ) ^ (κ * ε) * Real.sqrt (∑ j, ‖u j‖ ^ 2)) := by
  obtain ⟨T, D, hT, hD, hb⟩ := full_reference_error_sums s
  let κ := κstar + M₀
  let A := T * Cstar + 2 * D
  have hC0 : 0 ≤ Cstar := by linarith
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨κ, 2 * A, by dsimp [κ]; positivity, by positivity,
    fun ε hε {α} _ ν n m hm hK M hM => ?_⟩
  let K := ⌊(n : ℝ) ^ ε⌋₊ ^ M₀
  have hn : 1 ≤ (n : ℝ) := by exact_mod_cast n.pos
  have hn0 : 0 < (n : ℝ) := by positivity
  have hfloor : (K : ℝ) ≤ (n : ℝ) ^ ((M₀ : ℝ) * ε) := by
    dsimp [K]
    rw [Nat.cast_pow, mul_comm (M₀ : ℝ), Real.rpow_mul_natCast hn0.le]
    exact pow_le_pow_left₀ (by positivity) (Nat.floor_le (by positivity)) _
  have hshort : (K : ℝ) ^ (1 - s.val) ≤ (n : ℝ) ^ (κ * ε) := by
    calc
      _ ≤ ((n : ℝ) ^ ((M₀ : ℝ) * ε)) ^ (1 - s.val) :=
        Real.rpow_le_rpow (by positivity) hfloor (by linarith [s.property.2])
      _ = (n : ℝ) ^ ((M₀ : ℝ) * ε * (1 - s.val)) := (Real.rpow_mul hn0.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn (by
        dsimp [κ]
        nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ M₀) hε.le,
          mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ M₀) hε.le) s.property.1.le])
  have hmain : (n : ℝ) ^ (κstar * ε) ≤ (n : ℝ) ^ (κ * ε) :=
    Real.rpow_le_rpow_of_exponent_le hn (by dsimp [κ]; nlinarith)
  filter_upwards [hb ν n m hm K hK Cstar κstar γstar ε hC0 M hM] with x hx
  let E := fun i j => M x i j - 2 * sampledRieszKernel s m hm (j - i)
  have hrow (i) : (∑ j, |E i j|) ≤ A * (n : ℝ) ^ (κ * ε) := by
    calc
      _ ≤ T * Cstar * (n : ℝ) ^ (κstar * ε) + 2 * D * (K : ℝ) ^ (1 - s.val) := (hx i).1
      _ ≤ T * Cstar * (n : ℝ) ^ (κ * ε) + 2 * D * (n : ℝ) ^ (κ * ε) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hmain (by positivity))
          (mul_le_mul_of_nonneg_left hshort (by positivity))
      _ = _ := by dsimp [A]; ring
  have hcol (i) : (∑ j, |E j i|) ≤ A * (n : ℝ) ^ (κ * ε) := by
    calc
      _ ≤ T * Cstar * (n : ℝ) ^ (κstar * ε) + 2 * D * (K : ℝ) ^ (1 - s.val) := (hx i).2
      _ ≤ T * Cstar * (n : ℝ) ^ (κ * ε) + 2 * D * (n : ℝ) ^ (κ * ε) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hmain (by positivity))
          (mul_le_mul_of_nonneg_left hshort (by positivity))
      _ = _ := by dsimp [A]; ring
  have hB : 0 ≤ (2 * A) * (n : ℝ) ^ (κ * ε) := by positivity
  have hrow' (i) : (∑ j, |E i j|) ≤ (2 * A) * (n : ℝ) ^ (κ * ε) :=
    (hrow i).trans (by nlinarith [Real.rpow_nonneg hn0.le (κ * ε)])
  have hcol' (i) : (∑ j, |E j i|) ≤ (2 * A) * (n : ℝ) ^ (κ * ε) :=
    (hcol i).trans (by nlinarith [Real.rpow_nonneg hn0.le (κ * ε)])
  refine ⟨fun i j => by dsimp only [E] at hrow hcol; linarith [hrow i, hcol j], ?_, ?_⟩
  · intro u
    constructor
    · simpa only [smul_eq_mul, Real.norm_eq_abs] using FiniteSchurBounds.sum_norm_le E u hcol'
    · simpa only [smul_eq_mul, Real.norm_eq_abs, sq_abs] using
        FiniteSchurBounds.sqrt_sum_sq_norm_le E u hB hrow' hcol'
  · intro u
    constructor
    · simpa only [Complex.real_smul] using FiniteSchurBounds.sum_norm_le E u hcol'
    · simpa only [Complex.real_smul] using
        FiniteSchurBounds.sqrt_sum_sq_norm_le E u hB hrow' hcol'

/-- Cyclic distance is the smaller of the two directed arc lengths. -/
theorem cyclicIndexDistance_min_residues (N : ℕ+) (a b : Fin (N : ℕ)) :
    Riesz1.cyclicIndexDistance N a b = min (b - a).val (a - b).val := by
  simp only [Riesz1.cyclicIndexDistance, Fin.val_sub, Nat.dist]
  have ha := a.isLt
  have hb := b.isLt
  by_cases h : a.val ≤ b.val
  · by_cases he : a.val = b.val
    · simp [he, Nat.mod_self]
    · rw [Nat.mod_eq_sub_mod (by omega : (N : ℕ) ≤ (N : ℕ) - a.val + b.val),
        Nat.mod_eq_of_lt (by omega : (N : ℕ) - a.val + b.val - (N : ℕ) < (N : ℕ)),
        Nat.mod_eq_of_lt (by omega : (N : ℕ) - b.val + a.val < (N : ℕ))]
      omega
  · rw [Nat.mod_eq_of_lt (by omega : (N : ℕ) - a.val + b.val < (N : ℕ)),
      Nat.mod_eq_sub_mod (by omega : (N : ℕ) ≤ (N : ℕ) - b.val + a.val),
      Nat.mod_eq_of_lt (by omega : (N : ℕ) - b.val + a.val - (N : ℕ) < (N : ℕ))]
    omega

/-- Uniform translation modulus of the full sampled kernel, obtained by
summing values near the two origins and telescoping first differences along
an oriented shortest arc on the complement. -/
theorem kernel_column_variation (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (a b : Fin (N : ℕ)),
      (∑ i, |sampledRieszKernel s N hN (b - i) - sampledRieszKernel s N hN (a - i)|) ≤
        C * (Riesz1.cyclicIndexDistance N a b : ℝ) ^ (1 - s.val) := by
  obtain ⟨A, D, hA, hD, hb⟩ := sampled_kernel_value_difference s
  let C := 4 * A / (1 - s.val) * 4 ^ (1 - s.val) +
    2 * D * 2 ^ (s.val + 1) * (1 + 1 / s.val)
  have hC : 0 < C := by dsimp [C]; positivity [sub_pos.mpr s.property.2, s.property.1]
  refine ⟨C, hC, fun N hN a b => ?_⟩
  by_cases hab : a = b
  · subst b
    simp only [sub_self, abs_zero, Finset.sum_const_zero]
    positivity
  have hR : 1 ≤ Riesz1.cyclicIndexDistance N a b := by
    have h := (cyclicIndexDistance_eq_zero_iff a b).not.mpr hab
    omega
  have harc (a b : Fin (N : ℕ)) (h : (b - a).val ≤ (a - b).val)
      (hR : 1 ≤ Riesz1.cyclicIndexDistance N a b) :
      (∑ i, |sampledRieszKernel s N hN (b - i) - sampledRieszKernel s N hN (a - i)|) ≤
        C * (Riesz1.cyclicIndexDistance N a b : ℝ) ^ (1 - s.val) := by
    have hd : Riesz1.cyclicIndexDistance N a b = (b - a).val := by
      rw [cyclicIndexDistance_min_residues, min_eq_left h]
    have hhalf : 2 * (b - a).val ≤ (N : ℕ) := by
      have := Riesz1.APG.cyclicIndexDistance_le_half (N := N) a b
      omega
    have hh := kernel_translation_arc_internal s N
      (fun i j => sampledRieszKernel s N hN (j - i)) hA.le hD.le
      (fun i j => (hb N hN i j).1) (fun i j => (hb N hN i j).2)
      a (b - a).val (by omega) hhalf
    have he : a + ((b - a).val : Fin (N : ℕ)) = b := by rw [Fin.cast_val_eq_self]; abel
    simpa only [he, hd, C] using hh
  rcases le_total (b - a).val (a - b).val with h | h
  · exact harc a b h hR
  · have hh := harc b a h (by rwa [cyclicIndexDistance_comm'])
    simpa only [abs_sub_comm, cyclicIndexDistance_comm' N b a] using hh

/-- The inverse distance has uniformly logarithmic counting mass. The
zero-distance term is explicitly the real-power value zero. -/
theorem distance_inverse_harmonic :
    ∃ H : ℝ, 0 < H ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ a : Fin (N : ℕ),
      (∑ j, (Riesz1.cyclicIndexDistance N j a : ℝ) ^ (-1 : ℝ)) ≤
        H * Real.log (2 * (N : ℝ)) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨4 * (1 + 1 / Real.log 2), by positivity, fun N hN a => ?_⟩
  have hle (j : Fin (N : ℕ)) :
      (Riesz1.cyclicIndexDistance N j a : ℝ) ^ (-1 : ℝ) ≤ 2 * weightRadius N j a ^ (-1 : ℝ) := by
    let d := Riesz1.cyclicIndexDistance N j a
    change (d : ℝ) ^ (-1 : ℝ) ≤ 2 * (1 + (d : ℝ)) ^ (-1 : ℝ)
    by_cases hd : d = 0
    · simp [hd]
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (Nat.pos_of_ne_zero hd)
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hd)
    change (d : ℝ) ^ (-1 : ℝ) ≤ 2 * (1 + (d : ℝ)) ^ (-1 : ℝ)
    rw [Real.rpow_neg_one, Real.rpow_neg_one]
    have h := (div_le_div_iff₀ hd0 (by positivity : (0 : ℝ) < 1 + d)).mpr
      (by linarith : 1 * (1 + (d : ℝ)) ≤ 2 * d)
    simpa only [one_div, div_eq_mul_inv, one_mul] using h
  have hall : Finset.univ.filter (fun j : Fin (N : ℕ) => weightRadius N j a ≤ (N : ℝ)) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro j _
    have hd := Riesz1.APG.cyclicIndexDistance_le_half (N := N) j a
    have hdR : (Riesz1.cyclicIndexDistance N j a : ℝ) ≤ ((N : ℕ) / 2 : ℕ) := by exact_mod_cast (show Riesz1.cyclicIndexDistance N j a ≤ (N : ℕ) / 2 by omega)
    have hhalf : (((N : ℕ) / 2 : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast (show (N : ℕ) / 2 + 1 ≤ (N : ℕ) by omega)
    dsimp [weightRadius]
    linarith
  have hh := sum_weightRadius_le_of_one N a (R := N) (by exact_mod_cast N.pos)
  rw [hall] at hh
  calc
    _ ≤ ∑ j, 2 * weightRadius N j a ^ (-1 : ℝ) := Finset.sum_le_sum fun j _ => hle j
    _ = 2 * ∑ j, weightRadius N j a ^ (-1 : ℝ) := by rw [Finset.mul_sum]
    _ ≤ 2 * (2 * (1 + 1 / Real.log 2) * Real.log (2 * (N : ℝ))) := mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = _ := by ring

/-- Zero sum permits subtraction of the reference column before taking
the kernel `ℓ¹` norm. -/
theorem kernel_zero_sum_l1 (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (u : Fin (N : ℕ) → ℝ), (∑ j, u j) = 0 → ∀ a : Fin (N : ℕ),
      (∑ i, |∑ j, sampledRieszKernel s N hN (j - i) * u j|) ≤
        C * ∑ j, (Riesz1.cyclicIndexDistance N j a : ℝ) ^ (1 - s.val) * |u j| := by
  obtain ⟨C, hC, hb⟩ := kernel_column_variation s
  refine ⟨C, hC, fun N hN u hu a => ?_⟩
  have he (i : Fin (N : ℕ)) :
      (∑ j, sampledRieszKernel s N hN (j - i) * u j) =
        ∑ j, (sampledRieszKernel s N hN (j - i) - sampledRieszKernel s N hN (a - i)) * u j := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hu, mul_zero, sub_zero]
  simp_rw [he]
  calc
    _ ≤ ∑ i, ∑ j, |sampledRieszKernel s N hN (j - i) - sampledRieszKernel s N hN (a - i)| * |u j| := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (s := Finset.univ)
        (f := fun j => (sampledRieszKernel s N hN (j - i) - sampledRieszKernel s N hN (a - i)) * u j)
    _ = ∑ j, (∑ i, |sampledRieszKernel s N hN (j - i) - sampledRieszKernel s N hN (a - i)|) * |u j| := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_mul]
    _ ≤ ∑ j, C * (Riesz1.cyclicIndexDistance N j a : ℝ) ^ (1 - s.val) * |u j| := by
      apply Finset.sum_le_sum
      intro j _
      have h := hb N hN a j
      rw [cyclicIndexDistance_comm'] at h
      exact mul_le_mul_of_nonneg_right h (abs_nonneg _)
    _ = _ := by simp_rw [mul_assoc]; rw [Finset.mul_sum]

/-- Full counting mass of the regularized inverse distance. -/
theorem radius_inverse_harmonic :
    ∃ H : ℝ, 0 < H ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ a : Fin (N : ℕ),
      (∑ j, (weightRadius N j a)⁻¹) ≤ H * Real.log (2 * (N : ℝ)) := by
  refine ⟨2 * (1 + 1 / Real.log 2), by positivity [Real.log_pos (by norm_num : (1 : ℝ) < 2)],
    fun N hN a => ?_⟩
  have hall : Finset.univ.filter (fun j : Fin (N : ℕ) => weightRadius N j a ≤ (N : ℝ)) =
      Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro j _
    have hd := Riesz1.APG.cyclicIndexDistance_le_half (N := N) j a
    have hdR : (Riesz1.cyclicIndexDistance N j a : ℝ) ≤ ((N : ℕ) / 2 : ℕ) := by
      exact_mod_cast (show Riesz1.cyclicIndexDistance N j a ≤ (N : ℕ) / 2 by omega)
    have hh : (((N : ℕ) / 2 : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by
      exact_mod_cast (show (N : ℕ) / 2 + 1 ≤ (N : ℕ) by omega)
    dsimp only [weightRadius]
    linarith
  have h := sum_weightRadius_le_of_one N a (R := N) (by exact_mod_cast N.pos)
  rw [hall] at h
  simpa only [Real.rpow_neg_one] using h

/-- The radius-weighted spatial Cauchy–Schwarz step in equation (5.32) and equation (5.33)
of the proof of Lemma 5.9 of the paper. -/
theorem radius_weight_cauchy (N : ℕ+) (a : Fin (N : ℕ)) (p : ℝ)
    (u : Fin (N : ℕ) → ℝ) :
    (∑ j, weightRadius N j a ^ (p - 1 / 2) * |u j|) ≤
      Real.sqrt (∑ j, (weightRadius N j a)⁻¹) *
        Real.sqrt (∑ j, (weightRadius N j a ^ p * u j) ^ 2) := by
  let r := fun j => weightRadius N j a
  have hr (j) : 0 < r j := lt_of_lt_of_le zero_lt_one (one_le_weightRadius N j a)
  have hp (j) : r j ^ (p - 1 / 2) * |u j| =
      r j ^ (-1 / 2 : ℝ) * (r j ^ p * |u j|) := by
    rw [← mul_assoc, ← Real.rpow_add (hr j)]
    congr 2
    ring
  have hs (j) : (r j ^ (-1 / 2 : ℝ)) ^ 2 = (r j)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hr j).le]
    norm_num [Real.rpow_neg_one]
  simp_rw [show weightRadius N _ a = r _ from rfl, hp]
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun j => r j ^ (-1 / 2 : ℝ)) (fun j => r j ^ p * |u j|)
  simpa only [hs, mul_pow, sq_abs] using h

/-- The exact paper weight in equation (5.33), in the proof of Lemma 5.9
of the paper, before the harmonic sum is bounded. -/
theorem distance_weight_cauchy_radius (s : Riesz1.RieszExponent) (N : ℕ+)
    (a : Fin (N : ℕ)) (u : Fin (N : ℕ) → ℝ) :
    (∑ j, (Riesz1.cyclicIndexDistance N j a : ℝ) ^ (1 - s.val) * |u j|) ≤
      Real.sqrt (∑ j, (weightRadius N j a)⁻¹) *
        Real.sqrt (∑ j, (weightRadius N j a ^ (3 / 2 - s.val) * u j) ^ 2) := by
  calc
    _ ≤ ∑ j, weightRadius N j a ^ ((3 / 2 - s.val) - 1 / 2) * |u j| := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      rw [show (3 / 2 - s.val) - 1 / 2 = 1 - s.val by ring]
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by dsimp [weightRadius]; linarith)
        (by linarith [s.property.2])
    _ ≤ _ := radius_weight_cauchy N a (3 / 2 - s.val) u

/-- Display equation (5.33) in the proof of Lemma 5.9 of the paper:
the full primitive has an ℓ¹ bound with exactly `W_(3/2-s)`. -/
theorem elliptic_lone_radius (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (u : Fin (N : ℕ) → ℝ), (∑ j, u j) = 0 → ∀ a : Fin (N : ℕ),
      let H := Matrix.of (fun i j : Fin (N : ℕ) => sampledRieszKernel s N hN (j - i))
      (∑ i, |(H *ᵥ u) i|) ≤ C * Real.sqrt (Real.log (2 * (N : ℝ))) *
        Real.sqrt (∑ j, (weightRadius N j a ^ (3 / 2 - s.val) * u j) ^ 2) := by
  obtain ⟨C, hC, hb⟩ := kernel_zero_sum_l1 s
  obtain ⟨H, hH, hh⟩ := radius_inverse_harmonic
  refine ⟨C * Real.sqrt H, by positivity, fun N hN u hu a => ?_⟩
  have hcs := distance_weight_cauchy_radius s N a u
  have hroot := Real.sqrt_le_sqrt (hh N hN a)
  rw [Real.sqrt_mul hH.le] at hroot
  dsimp only
  change (∑ i, |∑ j, sampledRieszKernel s N hN (j - i) * u j|) ≤ _
  calc
    _ ≤ C * ∑ j, (Riesz1.cyclicIndexDistance N j a : ℝ) ^ (1 - s.val) * |u j| := hb N hN u hu a
    _ ≤ C * (Real.sqrt (∑ j, (weightRadius N j a)⁻¹) *
        Real.sqrt (∑ j, (weightRadius N j a ^ (3 / 2 - s.val) * u j) ^ 2)) :=
      mul_le_mul_of_nonneg_left hcs hC.le
    _ ≤ C * ((Real.sqrt H * Real.sqrt (Real.log (2 * (N : ℝ)))) *
        Real.sqrt (∑ j, (weightRadius N j a ^ (3 / 2 - s.val) * u j) ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _)) hC.le
    _ = _ := by ring

/-- Compatibility form of equation (5.33) in the proof of Lemma 5.9
of the paper. The exact radius estimate supplies the bound. The weight is expressed using the sine multiplier. -/
theorem elliptic_lone (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (u : Fin (N : ℕ) → ℝ), (∑ j, u j) = 0 → ∀ a : Fin (N : ℕ),
      let H := Matrix.of (fun i j : Fin (N : ℕ) => sampledRieszKernel s N hN (j - i))
      (∑ i, |(H *ᵥ u) i|) ≤ C * Real.sqrt (Real.log (2 * (N : ℝ))) *
        Real.sqrt (∑ j, ((1 + (Riesz1.cyclicIndexDistance N j a : ℝ) ^ (3 / 2 - s.val)) * u j) ^ 2) := by
  obtain ⟨C, hC, hb⟩ := elliptic_lone_radius s
  let p := 3 / 2 - s.val
  have hp : 0 < p := by dsimp [p]; linarith [s.property.2]
  refine ⟨C * (2 : ℝ) ^ p, by positivity, fun N hN u hu a => ?_⟩
  have hw (j : Fin (N : ℕ)) : weightRadius N j a ^ p ≤
      (2 : ℝ) ^ p * (1 + (Riesz1.cyclicIndexDistance N j a : ℝ) ^ p) := by
    by_cases hz : (Riesz1.cyclicIndexDistance N j a : ℝ) = 0
    · simpa only [weightRadius, hz, add_zero, Real.one_rpow,
        Real.zero_rpow hp.ne', mul_one] using Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) hp.le
    have hd : (1 : ℝ) ≤ Riesz1.cyclicIndexDistance N j a := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hz))
    calc
      _ ≤ (2 * (Riesz1.cyclicIndexDistance N j a : ℝ)) ^ p :=
        Real.rpow_le_rpow (by positivity [one_le_weightRadius N j a])
          (by dsimp [weightRadius]; linarith) hp.le
      _ = (2 : ℝ) ^ p * (Riesz1.cyclicIndexDistance N j a : ℝ) ^ p :=
        Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (by positivity)
  have hnorm := Real.sqrt_le_sqrt (Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    pow_le_pow_left₀ (mul_nonneg (Real.rpow_nonneg (by positivity [one_le_weightRadius N j a]) _)
      (abs_nonneg (u j))) (mul_le_mul_of_nonneg_right (hw j) (abs_nonneg (u j))) 2))
  simp only [mul_assoc, mul_pow, sq_abs, ← Finset.mul_sum] at hnorm
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.rpow_nonneg (by norm_num) p)] at hnorm
  simp only [← mul_pow] at hnorm
  have h := (hb N hN u hu a).trans (mul_le_mul_of_nonneg_left hnorm
    (mul_nonneg hC.le (Real.sqrt_nonneg _)))
  convert h using 1
  dsimp only [p]
  ring

/-- Internal scalar step of the proof of Lemma 5.9: the
resolvent estimate holds for any weak solution on the form.
This reuses the coercive solution map and its uniqueness theorem. -/
theorem scalar_resolvent_bound_internal {α : Type*} [MeasurableSpace α] {ν : Measure α}
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    {b : ℝ} (hb : 0 < b) (f : Lp ℝ 2 ν) (u : Q.1)
    (hu : ∀ w : Q.1, Q.2 u w + b * inner ℝ u.val w.val = inner ℝ f w.val) :
    ‖u.val‖ ≤ b⁻¹ * ‖f‖ := by
  let v := (ScalarFormHilbert.equiv Q hQ).symm u
  have he : v = ScalarFormHilbert.shiftedSolution Q hQ b hb f := by
    apply ScalarFormHilbert.shiftedSolution_unique Q hQ b hb f v
    intro w
    simpa only [v, LinearEquiv.apply_symm_apply, ScalarFormHilbert.value_apply] using
      hu (ScalarFormHilbert.equiv Q hQ w)
  have hn := ScalarFormHilbert.shiftedSolution_value_norm_le Q hQ b hb f
  rw [← he] at hn
  simpa only [ScalarFormHilbert.value_apply, v, LinearEquiv.apply_symm_apply] using hn

/-- The sine frequency radius is at least four times the cyclic frequency
distance divided by the cycle size. -/
theorem frequencyRadius_distance_lower (N : ℕ+) (k : Fin (N : ℕ)) (hk : k ≠ 0) :
    4 * (Riesz1.cyclicIndexDistance N k 0 : ℝ) / (N : ℝ) ≤
      DiscreteInterpolation.frequencyRadius (cycleAngle N k) := by
  have hN : (0 : ℝ) < N := by positivity
  let d := Riesz1.cyclicIndexDistance N k 0
  have hd : d = min k.val ((N : ℕ) - k.val) := by
    simp only [d, Riesz1.cyclicIndexDistance, Fin.val_zero, Nat.dist_zero_right]
  have hd1 : (d : ℝ) ≤ k.val := by exact_mod_cast (hd.trans_le (min_le_left _ _))
  have hd2 : (d : ℝ) ≤ (N : ℝ) - k.val := by
    have h := hd.trans_le (min_le_right _ _)
    have hcast : (d : ℝ) ≤ (((N : ℕ) - k.val : ℕ) : ℝ) := by exact_mod_cast h
    rw [Nat.cast_sub (Nat.le_of_lt k.isLt)] at hcast
    exact hcast
  have he : 2 * Real.pi * d / (N : ℝ) ≤
      min (cycleAngle N k) (2 * Real.pi - cycleAngle N k) := by
    apply le_min
    · dsimp [cycleAngle]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd1 (by positivity)) hN.le
    · dsimp [cycleAngle]
      rw [le_sub_iff_add_le, ← add_div, div_le_iff₀ hN]
      nlinarith [Real.pi_pos]
  have hs := DiscreteInterpolation.endpointDistance_le_radius
    (Set.Ioo_subset_Icc_self (cycleAngle_mem_Ioo N k hk))
  rw [div_le_iff₀ hN] at he ⊢
  change 4 * (d : ℝ) ≤ _
  nlinarith [Real.pi_pos]

/-- The normalized inverse-frequency sum in the proof of Lemma 5.9 is logarithmic, uniformly in cycle size.
The zero frequency contributes zero. -/
theorem frequency_inverse_harmonic :
    ∃ H : ℝ, 0 < H ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) →
      (N : ℝ)⁻¹ * (∑ k : Fin (N : ℕ),
        (DiscreteInterpolation.frequencyRadius (cycleAngle N k))⁻¹) ≤
          H * Real.log (2 * (N : ℝ)) := by
  obtain ⟨H, hH, hh⟩ := distance_inverse_harmonic
  refine ⟨H / 4, by positivity, fun N hN => ?_⟩
  have hN0 : (0 : ℝ) < N := by positivity
  have hpoint (k : Fin (N : ℕ)) :
      (DiscreteInterpolation.frequencyRadius (cycleAngle N k))⁻¹ ≤
        (N : ℝ) / 4 * (Riesz1.cyclicIndexDistance N k 0 : ℝ) ^ (-1 : ℝ) := by
    by_cases hk : k = 0
    · subst k
      simp [DiscreteInterpolation.frequencyRadius, cycleAngle, Riesz1.cyclicIndexDistance]
    have hd : 0 < Riesz1.cyclicIndexDistance N k 0 := by
      have h := (cyclicIndexDistance_eq_zero_iff k 0).not.mpr hk
      omega
    have hdR : (0 : ℝ) < Riesz1.cyclicIndexDistance N k 0 := by exact_mod_cast hd
    have hlow := frequencyRadius_distance_lower N k hk
    have hρ : 0 < DiscreteInterpolation.frequencyRadius (cycleAngle N k) :=
      lt_of_lt_of_le (by positivity) hlow
    have h := one_div_le_one_div_of_le (by positivity : 0 < 4 * (Riesz1.cyclicIndexDistance N k 0 : ℝ) / (N : ℝ)) hlow
    rw [Real.rpow_neg_one, one_div] at *
    refine h.trans_eq ?_
    field_simp
  calc
    _ ≤ (N : ℝ)⁻¹ * ∑ k : Fin (N : ℕ),
        (N : ℝ) / 4 * (Riesz1.cyclicIndexDistance N k 0 : ℝ) ^ (-1 : ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hpoint k) (by positivity)
    _ = (1 / 4 : ℝ) * ∑ k : Fin (N : ℕ), (Riesz1.cyclicIndexDistance N k 0 : ℝ) ^ (-1 : ℝ) := by
      rw [← Finset.mul_sum, ← mul_assoc]
      congr 1
      field_simp
    _ ≤ (1 / 4 : ℝ) * (H * Real.log (2 * (N : ℝ))) :=
      mul_le_mul_of_nonneg_left (hh N hN 0) (by norm_num)
    _ = _ := by ring

end Riesz2.EllipticPrimitive
