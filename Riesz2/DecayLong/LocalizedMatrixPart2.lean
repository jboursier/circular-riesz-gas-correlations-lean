/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.PeriodicPowerTailComparison
public import Riesz2.DecayLong.LocalizedMatrix

/-!
# Reference-period comparison for localized matrices

See the proof of Proposition 5.15 in the paper: quantitative period comparison for
the curvature and the retained interval coefficients.
-/

public section
noncomputable section

open scoped BigOperators Fin.NatCast

namespace Riesz2.LocalizedMatrix

/-- A lattice sequence with a summable power envelope has a uniform principal-image
error. No positivity of the sequence, including its value at zero, is required. -/
private theorem principal_error_internal {p : ℝ} (hp : 1 < p) :
    ∃ T : ℝ, 0 < T ∧ ∀ (f : ℤ → ℝ) (C : ℝ), 0 ≤ C →
      Summable (fun z => ‖f z‖) →
      (∀ z ≠ 0, ‖f z‖ ≤ C * |(z : ℝ)| ^ (-p)) →
      ∀ (N r : ℕ), 2 ≤ N → 1 ≤ r → 2 * r ≤ N →
        |(∑' k : ℤ, f ((r : ℤ) + k * N)) - f r| ≤ T * C * (N : ℝ) ^ (-p) := by
  obtain ⟨T, hT, hb⟩ := PeriodicPower.principal_image_error hp
  refine ⟨T, hT, fun f C hC hf hbound N r hN hr hhalf => ?_⟩
  classical
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hrr : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hhalfr : 2 * (r : ℝ) ≤ N := by exact_mod_cast hhalf
  have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hs : Summable (fun k : ℤ => f ((r : ℤ) + k * N)) :=
    hf.of_norm.comp_injective (fun a b h => mul_right_cancel₀ hN0 (add_left_cancel h))
  let g := fun k : ℤ => if k = 0 then 0 else f ((r : ℤ) + k * N)
  let q := fun k : ℤ => if k = 0 then 0 else |(r : ℝ) + k * N| ^ (-p)
  have hg : Summable g := (hs.sub (hasSum_ite_eq (0 : ℤ) (f r)).summable).congr (by
    intro k
    by_cases hk : k = 0 <;> simp [g, hk])
  have hq : Summable q := ((hb hNr hrr hhalfr).1.sub
    (hasSum_ite_eq (0 : ℤ) ((r : ℝ) ^ (-p))).summable).congr (by
      intro k
      by_cases hk : k = 0 <;> simp [q, hk, abs_of_pos hrr])
  have hne (k : ℤ) : (r : ℤ) + k * N ≠ 0 := by
    intro h
    have hdvd : (N : ℤ) ∣ (r : ℤ) := ⟨-k, by linear_combination h⟩
    have hsmall : |(r : ℤ)| < (N : ℤ) := by
      rw [abs_of_nonneg (by positivity)]
      exact_mod_cast (show r < N by omega)
    have := Int.eq_zero_of_abs_lt_dvd hdvd hsmall
    omega
  have hle (k : ℤ) : ‖g k‖ ≤ C * q k := by
    by_cases hk : k = 0
    · simp only [g, q, hk, ite_true, norm_zero, mul_zero, le_refl]
    · simp only [g, q, hk, ite_false]
      convert hbound _ (hne k) using 1
      push_cast
      rfl
  have he : (∑' k : ℤ, f ((r : ℤ) + k * N)) - f r = ∑' k, g k := by
    rw [hs.tsum_eq_add_tsum_ite 0]
    simp only [Int.zero_mul, add_zero, add_sub_cancel_left, g]
  have hqe : (∑' k : ℤ, |(r : ℝ) + k * N| ^ (-p)) - (r : ℝ) ^ (-p) =
      ∑' k, q k := by
    rw [(hb hNr hrr hhalfr).1.tsum_eq_add_tsum_ite 0]
    simp only [Int.cast_zero, zero_mul, add_zero, abs_of_pos hrr,
      add_sub_cancel_left, q]
  rw [he, ← Real.norm_eq_abs]
  calc
    ‖∑' k, g k‖ ≤ ∑' k, ‖g k‖ := norm_tsum_le_tsum_norm hg.norm
    _ ≤ ∑' k, C * q k := hg.norm.tsum_le_tsum hle (hq.mul_left C)
    _ = C * ∑' k, q k := tsum_mul_left
    _ ≤ C * (T * (N : ℝ) ^ (-p)) := by
      rw [← hqe]
      exact mul_le_mul_of_nonneg_left (hb hNr hrr hhalfr).2.2 hC
    _ = T * C * (N : ℝ) ^ (-p) := by ring

/-- See the proof of Proposition 5.15 in the paper: changing the reference period
changes every retained curvature by at most the smaller period to power `-s-2`.
The constant precedes both periods and the interval length. -/
theorem curvature_different_period (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m m₀ : ℕ+) (hm : 2 ≤ (m : ℕ))
      (hm₀ : 2 ≤ (m₀ : ℕ)), (m₀ : ℕ) ≤ (m : ℕ) →
      ∀ r : ℕ, 1 ≤ r → 2 * r ≤ (m₀ : ℕ) →
        |sampledSecondDifference s m hm (r : Fin (m : ℕ)) -
          sampledSecondDifference s m₀ hm₀ (r : Fin (m₀ : ℕ))| ≤
            C * (m₀ : ℝ) ^ (-s.val - 2) := by
  obtain ⟨T, hT, ht⟩ := principal_error_internal (p := s.val + 2)
    (by linarith [s.property.1])
  obtain ⟨c, C, _, hC, hb⟩ := latticeRieszCurvature_bounds s
  have hbound (z : ℤ) (hz : z ≠ 0) :
      ‖latticeRieszCurvature s z‖ ≤ C * |(z : ℝ)| ^ (-(s.val + 2)) := by
    have hzabs := hb |z| (Int.one_le_abs hz)
    have he : latticeRieszCurvature s |z| = latticeRieszCurvature s z := by
      rcases le_total 0 z with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h, latticeRieszCurvature_even]
    rw [he, Int.cast_abs] at hzabs
    rw [Real.norm_eq_abs, abs_of_nonneg (latticeRieszCurvature_nonneg_of_ne_zero s hz)]
    simpa only [show -(s.val + 2) = -s.val - 2 by ring] using hzabs.2.2
  have he (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (r : ℕ)
      (hr : 1 ≤ r) (hrN : 2 * r ≤ (N : ℕ)) :
      |sampledSecondDifference s N hN (r : Fin (N : ℕ)) -
        latticeRieszCurvature s r| ≤ T * C * (N : ℝ) ^ (-s.val - 2) := by
    rw [sampledSecondDifference_periodization]
    simp only [Fin.val_natCast, Nat.mod_eq_of_lt (by omega : r < (N : ℕ))]
    simpa only [show -(s.val + 2) = -s.val - 2 by ring] using
      ht (latticeRieszCurvature s) C hC.le (summable_norm_latticeRieszCurvature s)
        hbound N r hN hr hrN
  refine ⟨2 * T * C, by positivity, fun m m₀ hm hm₀ hle r hr hrm₀ => ?_⟩
  have hparent := he m hm r hr (by omega)
  have hlocal := he m₀ hm₀ r hr hrm₀
  have hpow : (m : ℝ) ^ (-s.val - 2) ≤ (m₀ : ℝ) ^ (-s.val - 2) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast hle)
      (by linarith [s.property.1])
  calc
    _ ≤ |sampledSecondDifference s m hm (r : Fin (m : ℕ)) - latticeRieszCurvature s r| +
        |sampledSecondDifference s m₀ hm₀ (r : Fin (m₀ : ℕ)) - latticeRieszCurvature s r| :=
      by simpa only [abs_sub_comm (latticeRieszCurvature s r)] using
        abs_sub_le (sampledSecondDifference s m hm (r : Fin (m : ℕ)))
          (latticeRieszCurvature s r)
          (sampledSecondDifference s m₀ hm₀ (r : Fin (m₀ : ℕ)))
    _ ≤ T * C * (m : ℝ) ^ (-s.val - 2) + T * C * (m₀ : ℝ) ^ (-s.val - 2) :=
      add_le_add hparent hlocal
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hpow (mul_nonneg hT.le hC.le)]

/-- See the proof of Proposition 5.15 in the paper: the actual reference coefficients,
with their common cutoff, have the required different-period error away from the
antipodal length. -/
theorem referenceWeight_different_period (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m m₀ : ℕ+) (hm : 2 ≤ (m : ℕ))
      (hm₀ : 2 ≤ (m₀ : ℕ)) (hle : (m₀ : ℕ) ≤ (m : ℕ))
      (K a r : ℕ) (ha : a < (m₀ : ℕ)) (hr : r < (m₀ : ℕ) / 2)
      (hhalf : 2 * (r + 1) < (m₀ : ℕ)),
        |BoundaryEntries.referenceWeight s m hm K
            (⟨a, by omega⟩, ⟨r, by omega⟩) -
          BoundaryEntries.referenceWeight s m₀ hm₀ K
            (⟨a, by assumption⟩, ⟨r, by assumption⟩)| ≤
          C * (m₀ : ℝ) ^ (-s.val - 2) := by
  obtain ⟨C, hC, hb⟩ := curvature_different_period s
  refine ⟨2 * C, by positivity, fun m m₀ hm hm₀ hle K a r ha hr hhalf => ?_⟩
  simp only [BoundaryEntries.referenceWeight,
    show ¬2 * (r + 1) = (m : ℕ) by omega,
    show ¬2 * (r + 1) = (m₀ : ℕ) by omega, ite_false, sub_zero, one_mul]
  split_ifs with hK
  · rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact (mul_le_mul_of_nonneg_left (hb m m₀ hm hm₀ hle (r + 1) (by omega)
      (by omega)) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
  · simp only [sub_self, abs_zero]
    positivity

open IntervalBoundary
open scoped Classical

/-- See the proof of Proposition 5.15 in the paper: an internal interval has its
ordinary ordered membership criterion, uniformly in the surrounding period. -/
theorem mem_internal_trace_iff (m : ℕ+) {n : ℕ} (hn : 2 * n ≤ (m : ℕ))
    (a r : Fin n) (hi : a.val + r.val + 1 ≤ n) (i : Fin n) :
    i ∈ trace m n (by omega) ⟨a.val, by omega⟩ (r.val + 1) ↔
      a.val ≤ i.val ∧ i.val < a.val + r.val + 1 := by
  rw [mem_trace m n (by omega) _ _ (by omega)]
  have ha := a.isLt
  have hr := r.isLt
  have hii := i.isLt
  by_cases hai : a.val ≤ i.val
  · rw [show i.val + (m : ℕ) - a.val = (m : ℕ) + (i.val - a.val) by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : i.val - a.val < (m : ℕ))]
    omega
  · rw [Nat.mod_eq_of_lt (by omega : i.val + (m : ℕ) - a.val < (m : ℕ))]
    omega

/-- See the proof of Proposition 5.15 in the paper: enumerate the retained terms
by their initial label and length within the active block. This exact formula
allows comparison of two different periods without identifying their cycles. -/
theorem internalMatrix_eq_sum (m : ℕ+) {n : ℕ} (hn : 2 * n ≤ (m : ℕ))
    (A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → ℝ) (i l : Fin n) :
    internalMatrix m n (by omega) A i l =
      ∑ t : Fin n × Fin n, if t.1.val + t.2.val + 1 ≤ n then
        A (⟨t.1.val, by have := t.1.isLt; omega⟩,
          ⟨t.2.val, by have := t.2.isLt; omega⟩) *
          (if t.1.val ≤ i.val ∧ i.val < t.1.val + t.2.val + 1 ∧
            t.1.val ≤ l.val ∧ l.val < t.1.val + t.2.val + 1 then 1 else 0)
      else 0 := by
  classical
  have hnm : n < (m : ℕ) := by have := m.pos; omega
  simp only [internalMatrix, ← Finset.sum_filter]
  let S := Finset.univ.filter (IsInternal m n)
  let T := Finset.univ.filter (fun t : Fin n × Fin n => t.1.val + t.2.val + 1 ≤ n)
  have hb (t : Fin (m : ℕ) × Fin ((m : ℕ) / 2)) (ht : t ∈ S) :
      t.1.val + t.2.val + 1 ≤ n :=
    (isInternal_iff m hnm t).mp (Finset.mem_filter.mp ht).2
  let e : (t : Fin (m : ℕ) × Fin ((m : ℕ) / 2)) → t ∈ S → Fin n × Fin n := fun t ht =>
    (⟨t.1.val, by have := hb t ht; omega⟩,
      ⟨t.2.val, by have := hb t ht; omega⟩)
  apply Finset.sum_bij e
  · intro t ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb t ht⟩
  · intro a ha b hb he
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg (fun t : Fin n × Fin n => t.1.val) he
    · exact congrArg (fun t : Fin n × Fin n => t.2.val) he
  · intro t ht
    have ht' := (Finset.mem_filter.mp ht).2
    let a : Fin (m : ℕ) × Fin ((m : ℕ) / 2) :=
      (⟨t.1.val, by have := t.1.isLt; omega⟩,
        ⟨t.2.val, by have := t.2.isLt; omega⟩)
    have ha : a ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (isInternal_iff m hnm a).mpr ht'⟩
    exact ⟨a, ha, rfl⟩
  · intro t ht
    have ht' := hb t ht
    have htrace (j : Fin n) :
        j ∈ trace m n (by omega) t.1 (t.2.val + 1) ↔
          t.1.val ≤ j.val ∧ j.val < t.1.val + t.2.val + 1 :=
      mem_internal_trace_iff m hn (e t ht).1 (e t ht).2 ht' j
    dsimp only [e]
    simp only [rankOne, htrace, and_assoc]

/-- See the proof of Proposition 5.15 in the paper: the retained reference blocks
at two periods differ by at most `C n₀² m₀^(-s-2)` entrywise. This is an estimate
of the reference blocks with their common cutoff. -/
theorem referenceInternal_different_period (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m m₀ n₀ : ℕ+) (hm : 2 ≤ (m : ℕ))
      (hm₀ : 2 ≤ (m₀ : ℕ)) (hle : (m₀ : ℕ) ≤ (m : ℕ))
      (hn₀ : 2 * (n₀ : ℕ) < (m₀ : ℕ)) (K : ℕ) (i l : Fin (n₀ : ℕ)),
        |BoundaryEntries.referenceInternal s m hm K n₀ (by omega) i l -
          BoundaryEntries.referenceInternal s m₀ hm₀ K n₀ (by omega) i l| ≤
          C * (n₀ : ℝ) ^ 2 * (m₀ : ℝ) ^ (-s.val - 2) := by
  obtain ⟨C, hC, hb⟩ := referenceWeight_different_period s
  refine ⟨C, hC, fun m m₀ n₀ hm hm₀ hle hn₀ K i l => ?_⟩
  rw [← internalMatrix_referenceWeight s m hm K n₀ (by omega),
    ← internalMatrix_referenceWeight s m₀ hm₀ K n₀ (by omega),
    internalMatrix_eq_sum m (by omega), internalMatrix_eq_sum m₀ (by omega),
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ t : Fin (n₀ : ℕ) × Fin (n₀ : ℕ),
        |(if t.1.val + t.2.val + 1 ≤ (n₀ : ℕ) then
          BoundaryEntries.referenceWeight s m hm K
            (⟨t.1.val, by have := t.1.isLt; omega⟩,
              ⟨t.2.val, by have := t.2.isLt; omega⟩) *
            (if t.1.val ≤ i.val ∧ i.val < t.1.val + t.2.val + 1 ∧
              t.1.val ≤ l.val ∧ l.val < t.1.val + t.2.val + 1 then 1 else 0)
          else 0) -
        (if t.1.val + t.2.val + 1 ≤ (n₀ : ℕ) then
          BoundaryEntries.referenceWeight s m₀ hm₀ K
            (⟨t.1.val, by have := t.1.isLt; omega⟩,
              ⟨t.2.val, by have := t.2.isLt; omega⟩) *
            (if t.1.val ≤ i.val ∧ i.val < t.1.val + t.2.val + 1 ∧
              t.1.val ≤ l.val ∧ l.val < t.1.val + t.2.val + 1 then 1 else 0)
          else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t : Fin (n₀ : ℕ) × Fin (n₀ : ℕ), C * (m₀ : ℝ) ^ (-s.val - 2) := by
      apply Finset.sum_le_sum
      intro t _
      split_ifs <;> simp only [mul_one, mul_zero, sub_self, abs_zero]
      · exact hb m m₀ hm hm₀ hle K t.1.val t.2.val
          (by have := t.1.isLt; omega) (by have := t.2.isLt; omega)
          (by have := t.2.isLt; omega)
      all_goals positivity
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
      ring

/-- See the proof of Proposition 5.15 in the paper: the changed-period error is
smaller than the reference entry profile at the prescribed uncapped scale. -/
theorem period_error_absorption (s : Riesz1.RieszExponent) (n₀ m₀ : ℕ+)
    (hscale : (n₀ : ℝ) ^ (1 / 2 + 1 / s.val) ≤ (m₀ : ℝ))
    {d : ℕ} (hd : d < (n₀ : ℕ)) :
    (n₀ : ℝ) ^ 2 * (m₀ : ℝ) ^ (-s.val - 2) ≤
      (1 + (d : ℝ)) ^ (-1 - s.val / 2) := by
  have hn : (1 : ℝ) ≤ n₀ := by exact_mod_cast n₀.pos
  have hnp : (0 : ℝ) < n₀ := by positivity
  have hs : 0 < s.val := s.property.1
  have hs1 := s.property.2
  have hp := Real.rpow_le_rpow_of_nonpos
    (Real.rpow_pos_of_pos hnp (1 / 2 + 1 / s.val)) hscale
      (by linarith : -s.val - 2 ≤ 0)
  have hexp : 2 + (1 / 2 + 1 / s.val) * (-s.val - 2) ≤ -1 - s.val / 2 := by
    have hdiv : 1 ≤ 1 / s.val := (one_le_div hs).mpr (by linarith)
    have he : 2 + (1 / 2 + 1 / s.val) * (-s.val - 2) = -s.val / 2 - 2 / s.val := by
      field_simp
      ring
    rw [he]
    simp only [div_eq_mul_inv, one_mul] at hdiv ⊢
    linarith
  calc
    _ ≤ (n₀ : ℝ) ^ 2 * ((n₀ : ℝ) ^ (1 / 2 + 1 / s.val)) ^ (-s.val - 2) :=
      mul_le_mul_of_nonneg_left hp (sq_nonneg _)
    _ = (n₀ : ℝ) ^ (2 + (1 / 2 + 1 / s.val) * (-s.val - 2)) := by
      rw [← Real.rpow_mul hnp.le, Real.rpow_add hnp]
      norm_num
    _ ≤ (n₀ : ℝ) ^ (-1 - s.val / 2) := Real.rpow_le_rpow_of_exponent_le hn hexp
    _ ≤ (1 + (d : ℝ)) ^ (-1 - s.val / 2) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by exact_mod_cast (show 1 + d ≤ (n₀ : ℕ) by omega))
        (by linarith)

section EntryComparison

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

/-- See the proof of Proposition 5.15 in the paper, reference-entry clause in
initial-block coordinates. The measurable nonnegative parent witness is
extracted from the assumptions. The new period is either capped at the
parent or satisfies the prescribed power lower bound. -/
theorem initial_block_entry_comparison (s : Riesz1.RieszExponent) :
    ∃ Cperiod : ℝ, 0 < Cperiod ∧
    ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ)) (K : ℕ) (C κ γ ε : ℝ), 1 ≤ C →
    ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M →
    ∃ A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → Ω → ℝ,
      (∀ t, Measurable (A t)) ∧ ∀ᵐ x ∂ν,
      (∀ t, 0 ≤ A t x) ∧ intervalMatrix m m le_rfl (fun t => A t x) = M x ∧
      ∀ (n₀ m₀ : ℕ+) (hm₀ : 2 ≤ (m₀ : ℕ))
        (hn : 4 * (n₀ : ℕ) ≤ (m : ℕ)) (hn₀ : 2 * (n₀ : ℕ) < (m₀ : ℕ)),
        (m₀ : ℕ) ≤ (m : ℕ) →
        (m₀ = m ∨ (n₀ : ℝ) ^ (1 / 2 + 1 / s.val) ≤ (m₀ : ℝ)) →
        ∀ i l : Fin (n₀ : ℕ), i.val ≤ l.val →
        |matrix s m m₀ n₀ hm₀ (by omega) (by omega) K A x
            (i.castLE (by omega)) (l.castLE (by omega)) -
          ((2 : ℝ) • referenceIntervalMatrix s m₀ hm₀ K)
            (i.castLE (by omega)) (l.castLE (by omega))| ≤
        (4 * (C * (n : ℝ) ^ (κ * ε)) + Cperiod) *
          (1 + ((l.val - i.val : ℕ) : ℝ)) ^ (-1 - s.val / 2) := by
  obtain ⟨Cperiod, hCperiod, hperiod⟩ := referenceInternal_different_period s
  refine ⟨Cperiod, hCperiod, fun n m hm K C κ γ ε hC M hM => ?_⟩
  obtain ⟨A, hA, hb⟩ := parent_internal_comparison s n m hm K C κ γ ε hC M hM
  refine ⟨A, hA, ?_⟩
  filter_upwards [hb] with x hx
  refine ⟨hx.1, hx.2.1, fun n₀ m₀ hm₀ hn hn₀ hle hscale i l hil => ?_⟩
  rw [matrix_reference_error]
  have hparent := hx.2.2 n₀ hn i l hil
  have hdiff :
      |BoundaryEntries.referenceInternal s m hm K n₀ (by omega) i l -
        BoundaryEntries.referenceInternal s m₀ hm₀ K n₀ (by omega) i l| ≤
      Cperiod * (1 + ((l.val - i.val : ℕ) : ℝ)) ^ (-1 - s.val / 2) := by
    rcases hscale with rfl | hscale
    · simp only [sub_self, abs_zero]
      positivity
    · have hp := hperiod m m₀ n₀ hm hm₀ hle hn₀ K i l
      have ha := mul_le_mul_of_nonneg_left
        (period_error_absorption s n₀ m₀ hscale
          (d := l.val - i.val) (by have := l.isLt; omega)) hCperiod.le
      exact hp.trans (by simpa only [mul_assoc] using ha)
  calc
    _ ≤ |internalMatrix m n₀ (by omega) (fun t => A t x) i l -
          BoundaryEntries.referenceInternal s m hm K n₀ (by omega) i l| +
        |BoundaryEntries.referenceInternal s m hm K n₀ (by omega) i l -
          BoundaryEntries.referenceInternal s m₀ hm₀ K n₀ (by omega) i l| :=
      abs_sub_le _ _ _
    _ ≤ _ := by linarith only [hparent, hdiff]

end EntryComparison

/-- See Subsection 5.5 of the paper: the actual window is one cyclic interval, starting
one radius to the left of its center. This includes zero separation. -/
theorem window_eq_cyclicIndexInterval (m : ℕ+) (j i₀ : Fin (m : ℕ)) :
    window m j i₀ = cyclicIndexInterval m
      (j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ)))
      (2 * (Riesz1.cyclicIndexDistance m j i₀ / 8) + 1) := by
  let R := Riesz1.cyclicIndexDistance m j i₀
  let k := R / 8
  have hR : 2 * R ≤ (m : ℕ) := by
    dsimp only [R, Riesz1.cyclicIndexDistance]
    have hi := i₀.isLt
    have hj := j.isLt
    unfold Nat.dist
    omega
  have hlen : 2 * k + 1 ≤ (m : ℕ) := by have := m.pos; dsimp [k]; omega
  have hk : k < (m : ℕ) := by omega
  ext i
  rw [mem_cyclicIndexInterval_iff m _ _ hlen]
  have he : i - (j - (k : Fin (m : ℕ))) = (i - j) + (k : Fin (m : ℕ)) := by abel
  simp only [window, Finset.mem_filter, Finset.mem_univ, true_and]
  change 8 * Riesz1.cyclicIndexDistance m i j ≤ R ↔
    (i - (j - (k : Fin (m : ℕ)))).val < 2 * k + 1
  rw [he, Fin.val_add, Fin.val_natCast, Nat.mod_eq_of_lt hk,
    GlobalReferenceErrorInternal.distance_eq_min]
  have hdist : (j - i).val = if (i - j).val = 0 then 0 else (m : ℕ) - (i - j).val := by
    rw [show j - i = -(i - j) by abel, Fin.val_neg]
    simp only [Fin.ext_iff, Fin.val_zero]
  rw [hdist]
  have hi := (i - j).isLt
  dsimp only [k]
  split_ifs with hzero
  · simp only [hzero, zero_add, Nat.zero_min, Nat.mod_eq_of_lt (by omega : R / 8 < (m : ℕ))]
    omega
  · by_cases hwrap : (i - j).val + R / 8 < (m : ℕ)
    · rw [Nat.mod_eq_of_lt hwrap]
      omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega

/-- See Subsection 5.5 of the paper: the ordered inclusion of the local window into the
parent cycle. Its definition fixes the cyclic starting point explicitly. -/
def windowEmbedding (m : ℕ+) (j i₀ : Fin (m : ℕ)) :
    Fin (windowSize m j i₀ : ℕ) ↪ Fin (m : ℕ) where
  toFun i := j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ)) +
    i.castLE (by
      change (window m j i₀).card ≤ (m : ℕ)
      have h := Finset.card_le_card (Finset.subset_univ (window m j i₀))
      simpa only [Finset.card_univ, Fintype.card_fin] using h)
  inj' := by
    intro i l h
    apply Fin.ext
    let start : Fin (m : ℕ) :=
      j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ))
    have he := congrArg (fun z : Fin (m : ℕ) => z - start) h
    simpa only [start, add_sub_cancel_left, Fin.val_castLE] using congrArg Fin.val he

/-- See Subsection 5.5 of the paper: the ordered embedding translates the initial block by the
window's starting point. -/
theorem windowEmbedding_apply (m : ℕ+) (j i₀ : Fin (m : ℕ))
    (l : Fin (windowSize m j i₀ : ℕ)) (hn : (windowSize m j i₀ : ℕ) ≤ (m : ℕ)) :
    windowEmbedding m j i₀ l =
      j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ)) + l.castLE hn := by
  simp only [windowEmbedding]
  rfl


/-- See Subsection 5.5 of the paper: the ordered embedding has exactly the prescribed
window as its image, including at separation zero. -/
theorem mem_window_iff_exists_embedding (m : ℕ+) (j i₀ i : Fin (m : ℕ)) :
    i ∈ window m j i₀ ↔ ∃ a, windowEmbedding m j i₀ a = i := by
  have hn : (windowSize m j i₀ : ℕ) ≤ (m : ℕ) := by
    change (window m j i₀).card ≤ (m : ℕ)
    have h := Finset.card_le_card (Finset.subset_univ (window m j i₀))
    simpa only [Finset.card_univ, Fintype.card_fin] using h
  rw [window_eq_cyclicIndexInterval,
    mem_cyclicIndexInterval_iff m _ _ (by
      rw [← window_card m j i₀]
      exact hn)]
  rw [← window_card m j i₀]
  let start : Fin (m : ℕ) :=
    j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ))
  change (i - start).val < (windowSize m j i₀ : ℕ) ↔ _
  constructor
  · intro hi
    refine ⟨⟨(i - start).val, hi⟩, ?_⟩
    change start + Fin.castLE hn ⟨(i - start).val, hi⟩ = i
    have he : Fin.castLE hn ⟨(i - start).val, hi⟩ = i - start := by
      apply Fin.ext
      rfl
    rw [he]
    abel
  · rintro ⟨a, rfl⟩
    change ((start + a.castLE hn) - start).val < (windowSize m j i₀ : ℕ)
    rw [add_sub_cancel_left, Fin.val_castLE]
    exact a.isLt

/-- See Subsection 5.5 of the paper: the source target is the central local label. -/
theorem windowEmbedding_center (m : ℕ+) (j i₀ : Fin (m : ℕ)) :
    windowEmbedding m j i₀
      ⟨Riesz1.cyclicIndexDistance m j i₀ / 8, by
        have h := window_card m j i₀
        change _ < (window m j i₀).card
        omega⟩ = j := by
  let a : Fin (windowSize m j i₀ : ℕ) :=
    ⟨Riesz1.cyclicIndexDistance m j i₀ / 8, by
      have h := window_card m j i₀
      change _ < (window m j i₀).card
      omega⟩
  have hn : (windowSize m j i₀ : ℕ) ≤ (m : ℕ) := by
    change (window m j i₀).card ≤ (m : ℕ)
    have h := Finset.card_le_card (Finset.subset_univ (window m j i₀))
    simpa only [Finset.card_univ, Fintype.card_fin] using h
  have he : a.castLE hn =
      ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ)) := by
    apply Fin.ext
    rw [Fin.val_castLE, Fin.val_natCast, Nat.mod_eq_of_lt (a.isLt.trans_le hn)]
  change j - _ + a.castLE hn = j
  rw [he]
  exact sub_add_cancel _ _

/-- See Subsection 5.5 of the paper: local ordered distances are the original parent
distances. This prevents replacing them by the distance on the retained cycle. -/
theorem windowEmbedding_distance (m : ℕ+) (j i₀ : Fin (m : ℕ))
    (hR : 16 ≤ Riesz1.cyclicIndexDistance m j i₀)
    (a b : Fin (windowSize m j i₀ : ℕ)) :
    Riesz1.cyclicIndexDistance m (windowEmbedding m j i₀ a)
      (windowEmbedding m j i₀ b) = Nat.dist a.val b.val := by
  have hn := (window_size_bounds m j i₀ hR).2.2.2
  rw [GlobalReferenceErrorInternal.distance_eq_min]
  have he : windowEmbedding m j i₀ b - windowEmbedding m j i₀ a =
      b.castLE (by omega : (windowSize m j i₀ : ℕ) ≤ (m : ℕ)) -
        a.castLE (by omega) := by
    change (j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ)) + b.castLE _) -
      (j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ)) + a.castLE _) = _
    abel
  rw [he, Fin.val_sub, Fin.val_castLE, Fin.val_castLE]
  have ha := a.isLt
  have hb := b.isLt
  unfold Nat.dist
  by_cases hab : a.val ≤ b.val
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- See Subsection 5.5 of the paper: in the admitted separation range, the new cycle
has strictly more than twice as many labels as the window. Thus no retained
interval has the new cycle's antipodal half-weight. -/
theorem two_windowSize_lt_period (s : Riesz1.RieszExponent) (m : ℕ+)
    (j i₀ : Fin (m : ℕ)) (hR : 16 ≤ Riesz1.cyclicIndexDistance m j i₀) :
    2 * (windowSize m j i₀ : ℕ) < (windowPeriod s m j i₀ : ℕ) := by
  obtain ⟨hfive, _, _, hquarter⟩ := window_size_bounds m j i₀ hR
  let n₀ := windowSize m j i₀
  have hn : (4 : ℝ) < n₀ := by
    change (4 : ℝ) < (windowSize m j i₀ : ℝ)
    exact_mod_cast (show 4 < (windowSize m j i₀ : ℕ) by omega)
  have hnp : (0 : ℝ) < n₀ := by positivity
  have hs : 1 ≤ 1 / s.val := (one_le_div s.property.1).mpr s.property.2.le
  have hsqrt : 2 < (n₀ : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 4) hn
    norm_num at h
    exact h
  have hp : 2 * (n₀ : ℝ) < (n₀ : ℝ) ^ (1 / 2 + 1 / s.val) := by
    calc
      _ < (n₀ : ℝ) * (n₀ : ℝ) ^ (1 / 2 : ℝ) := by nlinarith
      _ = (n₀ : ℝ) ^ (1 + 1 / 2 : ℝ) := by
        rw [Real.rpow_add hnp, Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  change 2 * (n₀ : ℕ) < min (m : ℕ)
    (max (2 * (n₀ : ℕ)) ⌈(n₀ : ℝ) ^ (1 / 2 + 1 / s.val)⌉₊)
  apply lt_min
  · have := n₀.pos
    dsimp only [n₀] at *
    omega
  · apply lt_of_lt_of_le _ (le_max_right _ _)
    have hceil := hp.trans_le (Nat.le_ceil ((n₀ : ℝ) ^ (1 / 2 + 1 / s.val)))
    exact_mod_cast hceil

/-- See the proof of Proposition 5.15 in the paper: rotation of both endpoints
preserves membership in the cyclic interval. -/
theorem interval_mem_add_iff (m : ℕ+) (a i b : Fin (m : ℕ)) {r : ℕ}
    (hr : r ≤ (m : ℕ)) :
    i + b ∈ cyclicIndexInterval m (a + b) r ↔ i ∈ cyclicIndexInterval m a r := by
  rw [mem_cyclicIndexInterval_iff m _ _ hr, mem_cyclicIndexInterval_iff m _ _ hr,
    show (i + b) - (a + b) = i - a by abel]

/-- See the proof of Proposition 5.15 in the paper: cyclic relabeling preserves
the parent distance, including across its seam. -/
theorem distance_add (m : ℕ+) (i l b : Fin (m : ℕ)) :
    Riesz1.cyclicIndexDistance m (i + b) (l + b) = Riesz1.cyclicIndexDistance m i l := by
  rw [GlobalReferenceErrorInternal.distance_eq_min, GlobalReferenceErrorInternal.distance_eq_min,
    show (l + b) - (i + b) = l - i by abel]

/-- See the proof of Proposition 5.15 in the paper: rotate the actual parent
coefficient family, rather than introducing a second interval representation. -/
theorem intervalMatrix_translate (m : ℕ+)
    (A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → ℝ) (b i l : Fin (m : ℕ)) :
    intervalMatrix m m le_rfl (fun t => A (t.1 + b, t.2)) i l =
      intervalMatrix m m le_rfl A (i + b) (l + b) := by
  rw [intervalMatrix_entries, intervalMatrix_entries]
  have he := Equiv.sum_comp (Equiv.addRight b)
    (fun a : Fin (m : ℕ) => ∑ r : Fin ((m : ℕ) / 2), A (a, r) *
      (if i + b ∈ cyclicIndexInterval m a (r.val + 1) then 1 else 0) *
      (if l + b ∈ cyclicIndexInterval m a (r.val + 1) then 1 else 0))
  rw [← he]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro r _
  have hr : r.val + 1 ≤ (m : ℕ) := by have := r.isLt; omega
  simp only [Equiv.coe_addRight, interval_mem_add_iff m a i b hr,
    interval_mem_add_iff m a l b hr]

section RotatedComparison

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

/-- See the proof of Proposition 5.15 in the paper: parent-period comparison
for every rotated initial block. This transports the literal coefficient
witness to the actual window's cyclic order without requiring the rotated
parent to have an initial exterior block. -/
theorem rotated_parent_internal_comparison
    (s : Riesz1.RieszExponent) (n m : ℕ+) (hm : 2 ≤ (m : ℕ))
    (K : ℕ) (C κ γ ε : ℝ) (hC : 1 ≤ C)
    (M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M) :
    ∃ A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → Ω → ℝ,
      (∀ t, Measurable (A t)) ∧ ∀ᵐ x ∂ν,
      (∀ t, 0 ≤ A t x) ∧ intervalMatrix m m le_rfl (fun t => A t x) = M x ∧
      ∀ (b : Fin (m : ℕ)) (n₀ : ℕ+) (hn₀ : 4 * (n₀ : ℕ) ≤ (m : ℕ))
        (i l : Fin (n₀ : ℕ)), i.val ≤ l.val →
        |internalMatrix m n₀ (by omega) (fun t => A (t.1 + b, t.2) x) i l -
          BoundaryEntries.referenceInternal s m hm K n₀ (by omega) i l| ≤
        4 * (C * (n : ℝ) ^ (κ * ε)) *
          (1 + ((l.val - i.val : ℕ) : ℝ)) ^ (-1 - s.val / 2) := by
  obtain ⟨a, ha, hrep⟩ := periodizedMatrixBounds_entry_representation s n m hm K C κ γ ε M hM
  refine ⟨fun t => a t.1 t.2, fun t => ha t.1 t.2, ?_⟩
  filter_upwards [hrep, periodizedMatrixBounds_truncated_error s n m hm K C κ γ ε
    (by linarith : 0 ≤ C) M hM] with x hx he
  let A := fun t : Fin (m : ℕ) × Fin ((m : ℕ) / 2) => a t.1 t.2 x
  have hmatrix : intervalMatrix m m le_rfl A = M x := by
    ext i l
    rw [intervalMatrix_entries]
    exact (hx.2 i l).symm
  refine ⟨fun t => (hx.1 t.1 t.2).1, hmatrix, fun b n₀ hn₀ i l hil => ?_⟩
  let B := A - BoundaryEntries.referenceWeight s m hm K
  have hB (p w : Fin (m : ℕ)) :
      |intervalMatrix m m le_rfl (fun t => B (t.1 + b, t.2)) p w| ≤
      (C * (n : ℝ) ^ (κ * ε)) *
        (1 + (Riesz1.cyclicIndexDistance m p w : ℝ)) ^ (-(1 + s.val / 2)) := by
    rw [intervalMatrix_translate]
    rw [show intervalMatrix m m le_rfl B = M x - (2 : ℝ) • referenceIntervalMatrix s m hm K by
      rw [show B = A - BoundaryEntries.referenceWeight s m hm K from rfl,
        intervalMatrix_sub, hmatrix, intervalMatrix_referenceWeight], Matrix.sub_apply]
    simpa only [distance_add, show -(1 + s.val / 2) = -1 - s.val / 2 by ring]
      using he (p + b) (w + b)
  have hbound := internalMatrix_entry_bound_internal m hn₀
    (fun t => B (t.1 + b, t.2)) (C * (n : ℝ) ^ (κ * ε)) (1 + s.val / 2)
    (mul_nonneg (by linarith) (by positivity)) (by linarith [s.property.1]) hB i l hil
  have hcoef : (fun t => B (t.1 + b, t.2)) =
      (fun t => A (t.1 + b, t.2)) - BoundaryEntries.referenceWeight s m hm K := rfl
  rw [hcoef, internalMatrix_sub, internalMatrix_referenceWeight, Matrix.sub_apply] at hbound
  simpa only [show -(1 + s.val / 2) = -1 - s.val / 2 by ring] using hbound

/-- See the proof of Proposition 5.15 in the paper: the full reference-entry
estimate for the actual window and its actual capped period. The coefficient
witness is transported in the window's cyclic order. -/
theorem window_localized_entry_comparison (s : Riesz1.RieszExponent) :
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
      ∀ i l : Fin (n₀ : ℕ), i.val ≤ l.val →
      |matrix s m m₀ n₀ hm₀ hn hn₀ K (fun t => A (t.1 + b, t.2)) x
          (i.castLE hn₀) (l.castLE hn₀) -
        ((2 : ℝ) • referenceIntervalMatrix s m₀ hm₀ K) (i.castLE hn₀) (l.castLE hn₀)| ≤
      (4 * (C * (n : ℝ) ^ (κ * ε)) + Cperiod) *
        (1 + ((l.val - i.val : ℕ) : ℝ)) ^ (-1 - s.val / 2) := by
  obtain ⟨Cperiod, hCperiod, hp⟩ := referenceInternal_different_period s
  refine ⟨Cperiod, hCperiod, fun n m hm K C κ γ ε hC M hM => ?_⟩
  obtain ⟨A, hA, hb⟩ := rotated_parent_internal_comparison s n m hm K C κ γ ε hC M hM
  refine ⟨A, hA, ?_⟩
  filter_upwards [hb] with x hx
  refine ⟨hx.1, hx.2.1, ?_⟩
  intro j i₀ hR
  dsimp only
  intro i l hil
  rw [matrix_reference_error]
  let n₀ := windowSize m j i₀
  let m₀ := windowPeriod s m j i₀
  have hquarter : 4 * (n₀ : ℕ) ≤ (m : ℕ) := (window_size_bounds m j i₀ hR).2.2.2
  have hstrict : 2 * (n₀ : ℕ) < (m₀ : ℕ) := two_windowSize_lt_period s m j i₀ hR
  have hle : (m₀ : ℕ) ≤ (m : ℕ) := windowPeriod_le_parent s m j i₀
  have hm₀ : 2 ≤ (m₀ : ℕ) := by have := n₀.pos; omega
  have hn : (n₀ : ℕ) ≤ (m : ℕ) := by omega
  have hn₀ : (n₀ : ℕ) ≤ (m₀ : ℕ) := by omega
  have hl : l.val < (n₀ : ℕ) := l.isLt
  have hparent := hx.2.2
    (j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ)))
    n₀ hquarter i l hil
  have hdiff :
      |BoundaryEntries.referenceInternal s m hm K n₀ hn i l -
        BoundaryEntries.referenceInternal s m₀ hm₀ K n₀ hn₀ i l| ≤
        Cperiod * (1 + ((l.val - i.val : ℕ) : ℝ)) ^ (-1 - s.val / 2) := by
    by_cases hc : (m₀ : ℕ) = (m : ℕ)
    · have heq : m₀ = m := Subtype.ext hc
      simp only [heq, sub_self, abs_zero]
      positivity
    · have hcap : (m₀ : ℕ) < (m : ℕ) := by omega
      have hscale := power_le_windowPeriod_of_lt s m j i₀ hcap
      have h₁ := hp m m₀ n₀ hm hm₀ hle hstrict K i l
      have h₂ := mul_le_mul_of_nonneg_left
        (period_error_absorption s n₀ m₀ hscale
          (d := l.val - i.val) (by omega)) hCperiod.le
      exact h₁.trans (by simpa only [mul_assoc] using h₂)
  calc
    _ ≤ |internalMatrix m n₀ hn
          (fun t => A (t.1 + (j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ))), t.2) x) i l -
          BoundaryEntries.referenceInternal s m hm K n₀ hn i l| +
        |BoundaryEntries.referenceInternal s m hm K n₀ hn i l -
          BoundaryEntries.referenceInternal s m₀ hm₀ K n₀ hn₀ i l| := abs_sub_le _ _ _
    _ ≤ _ := by linarith only [hparent, hdiff]

end RotatedComparison

/-- See Subsection 5.5 of the paper: rotation by the window's left endpoint sends the
initial block exactly onto the window. -/
theorem window_translate_mem_iff (m : ℕ+) (j i₀ w : Fin (m : ℕ)) :
    w + (j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ))) ∈
      window m j i₀ ↔ w.val < (windowSize m j i₀ : ℕ) := by
  let b : Fin (m : ℕ) := j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ))
  have hn : (windowSize m j i₀ : ℕ) ≤ (m : ℕ) := by
    change (window m j i₀).card ≤ (m : ℕ)
    have h := Finset.card_le_card (Finset.subset_univ (window m j i₀))
    simpa only [Finset.card_univ, Fintype.card_fin] using h
  rw [mem_window_iff_exists_embedding]
  constructor
  · rintro ⟨a, ha⟩
    change b + a.castLE hn = w + b at ha
    rw [add_comm w b] at ha
    have he := congrArg Fin.val (add_left_cancel ha : a.castLE hn = w)
    simp only [Fin.val_castLE] at he
    exact he ▸ a.isLt
  · intro hw
    refine ⟨⟨w.val, hw⟩, ?_⟩
    change b + Fin.castLE hn ⟨w.val, hw⟩ = w + b
    have he : (Fin.castLE hn ⟨w.val, hw⟩ : Fin (m : ℕ)) = w := by
      apply Fin.ext
      rfl
    rw [he, add_comm]

/-- See Subsection 5.5 of the paper: rotation transports precisely the intervals whose
entire support is retained. Thus the rotated coefficients in the initial-block
constructor are the actual window's retained coefficients. -/
theorem interval_subset_window_iff (m : ℕ+) (j i₀ a : Fin (m : ℕ))
    (r : Fin ((m : ℕ) / 2)) :
    let b := j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ))
    cyclicIndexInterval m (a + b) (r.val + 1) ⊆ window m j i₀ ↔
      IsInternal m (windowSize m j i₀ : ℕ) (a, r) := by
  dsimp only
  let b : Fin (m : ℕ) := j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ))
  have hr : r.val + 1 ≤ (m : ℕ) := by have := r.isLt; omega
  constructor
  · intro h w hw
    exact (window_translate_mem_iff m j i₀ w).mp
      (h ((interval_mem_add_iff m a w b hr).mpr hw))
  · intro h w hw
    have hmem : w - b ∈ cyclicIndexInterval m a (r.val + 1) := by
      apply (interval_mem_add_iff m a (w - b) b hr).mp
      simpa only [sub_add_cancel] using hw
    have hval := h (w - b) hmem
    have hm := (window_translate_mem_iff m j i₀ (w - b)).mpr hval
    change w - b + b ∈ window m j i₀ at hm
    simpa only [sub_add_cancel] using hm

end Riesz2.LocalizedMatrix
