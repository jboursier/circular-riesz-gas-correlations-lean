/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.LocalizedBoundaryPart8
public import Riesz2.ToMathlib.FiniteZeroSumBounds
public import Riesz2.ToMathlib.SubcriticalPowerSum

/-!
# Estimates for the localized exterior field

The centered row identities and interval bounds used in the proof of Proposition 5.15. The scalar space and component indices stay separate.
The source vectors are the existing L² classes and the matrix assumptions are
`PeriodizedMatrixBounds`.
-/

@[expose] public section
noncomputable section

open MeasureTheory Finset
open Riesz2.GlobalReferenceErrorInternal
open scoped BigOperators Classical Fin.NatCast

namespace Riesz2.LocalizedField

/-- See the proof of Proposition 5.15 in the paper: entry decay from the actual interval
coefficient envelope. Unlike a diagonal bound, this retains the separation
of the two labels. -/
theorem interval_entry_decay_internal (m : ℕ+) {t A : ℝ}
    (ht : 2 < t) (hA : 0 ≤ A)
    (a : Fin (m : ℕ) → Fin ((m : ℕ) / 2) → ℝ)
    (ha : ∀ k r, |a k r| ≤ A * ((r.val + 1 : ℕ) : ℝ) ^ (-t))
    (i j : Fin (m : ℕ)) :
    |∑ k, ∑ r, a k r *
      (if i ∈ cyclicIndexInterval m k (r.val + 1) then 1 else 0) *
      (if j ∈ cyclicIndexInterval m k (r.val + 1) then 1 else 0)| ≤
      A * ((1 + 1 / (t - 2)) * 2 ^ (t - 2)) *
        (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (2 - t) := by
  let d := Riesz1.cyclicIndexDistance m i j
  have hlen (r : Fin ((m : ℕ) / 2)) :
      (∑ k, |a k r *
        (if i ∈ cyclicIndexInterval m k (r.val + 1) then 1 else 0) *
        (if j ∈ cyclicIndexInterval m k (r.val + 1) then 1 else 0)|) ≤
      A * (if d ≤ r.val + 1 then ((r.val + 1 : ℕ) : ℝ) ^ (-(t - 1)) else 0) := by
    have hr := r.isLt
    by_cases hd : d ≤ r.val + 1
    · rw [ite_eq_left hd]
      calc
        _ ≤ ∑ k : Fin (m : ℕ),
            (A * ((r.val + 1 : ℕ) : ℝ) ^ (-t)) *
              (if i ∈ cyclicIndexInterval m k (r.val + 1) then 1 else 0) *
              (if i ∈ cyclicIndexInterval m k (r.val + 1) then 1 else 0) := by
          apply sum_le_sum
          intro k _
          split_ifs
          · simpa only [mul_one] using ha k r
          · simp only [mul_zero, abs_zero]; positivity
          · norm_num only [mul_one, mul_zero, zero_mul, abs_zero]
          · norm_num only [mul_one, mul_zero, zero_mul, abs_zero]
        _ = (A * ((r.val + 1 : ℕ) : ℝ) ^ (-t)) * (r.val + 1) := by
          simp_rw [mul_assoc]
          rw [← mul_sum, ← mul_sum, cyclicIndexInterval_pair_count m (by omega) i i,
            cyclicIndexDistance_self, Nat.sub_zero, Nat.cast_add, Nat.cast_one]
        _ = _ := by
          rw [show -(t - 1) = -t + 1 by ring,
            Real.rpow_add_one (by positivity : ((r.val + 1 : ℕ) : ℝ) ≠ 0)]
          push_cast
          ring
    · have hz (k : Fin (m : ℕ)) :
          a k r * (if i ∈ cyclicIndexInterval m k (r.val + 1) then 1 else 0) *
            (if j ∈ cyclicIndexInterval m k (r.val + 1) then 1 else 0) = 0 := by
        by_cases hi : i ∈ cyclicIndexInterval m k (r.val + 1)
        · have hj : j ∉ cyclicIndexInterval m k (r.val + 1) := by
            intro hj
            have hh := distance_lt_length_of_mem m (by omega) k i j hi hj
            exact hd (Nat.le_of_lt hh)
          simp only [hj, ite_false, mul_zero]
        · simp only [hi, ite_false, mul_zero, zero_mul]
      simp only [hz, abs_zero, sum_const_zero, hd, ite_false, mul_zero, le_refl]
  rw [sum_comm]
  calc
    _ ≤ ∑ r : Fin ((m : ℕ) / 2), ∑ k : Fin (m : ℕ),
        |a k r * (if i ∈ cyclicIndexInterval m k (r.val + 1) then 1 else 0) *
          (if j ∈ cyclicIndexInterval m k (r.val + 1) then 1 else 0)| :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun r _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ r : Fin ((m : ℕ) / 2), A *
        (if d ≤ r.val + 1 then ((r.val + 1 : ℕ) : ℝ) ^ (-(t - 1)) else 0) :=
      sum_le_sum fun r _ => hlen r
    _ ≤ A * ((1 + 1 / (t - 2)) * 2 ^ (t - 2) *
        (1 + (d : ℝ)) ^ (2 - t)) := by
      rw [← mul_sum]
      simpa only [show t - 1 - 1 = t - 2 by ring,
        show 1 - (t - 1) = 2 - t by ring] using
        mul_le_mul_of_nonneg_left (length_tail_le (by linarith : 1 < t - 1)
          ((m : ℕ) / 2) d) hA
    _ = _ := by ring

/-- See the proof of Proposition 5.15 in the paper: simultaneous entry and neighboring-row
bounds for the matrix. The constants depend only on `s` and
the given coefficient prefactor. -/
theorem periodized_entry_and_difference (s : Riesz1.RieszExponent)
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (n m : ℕ+) (hm : 2 ≤ (m : ℕ)) (K : ℕ) (C κ γ ε : ℝ)
    (hC : 0 ≤ C) (M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M) :
    ∀ᵐ x ∂ν, ∀ i j,
      |M x i j| ≤ C * (n : ℝ) ^ (κ * ε) * ((1 + 1 / s.val) * 2 ^ s.val) *
        (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-s.val) ∧
      |M x i j - M x (i - 1) j| ≤
        (2 * (C * (n : ℝ) ^ (κ * ε)) * (1 + 1 / (s.val + 1)) * 2 ^ (s.val + 1)) *
          (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-1 - s.val) := by
  obtain ⟨a, _, ha⟩ := periodizedMatrixBounds_entry_representation s n m hm K C κ γ ε M hM
  filter_upwards [ha] with x hx
  intro i j
  have hab (k : Fin (m : ℕ)) (r : Fin ((m : ℕ) / 2)) :
      |a k r x| ≤ (C * (n : ℝ) ^ (κ * ε)) * ((r.val + 1 : ℕ) : ℝ) ^ (-(s.val + 2)) := by
    simpa only [abs_of_nonneg (hx.1 k r).1, show -(s.val + 2) = -s.val - 2 by ring]
      using (hx.1 k r).2.1
  have hA : 0 ≤ C * (n : ℝ) ^ (κ * ε) := mul_nonneg hC (Real.rpow_nonneg (by positivity) _)
  constructor
  · rw [hx.2 i j]
    simpa only [show s.val + 2 - 2 = s.val by ring,
      show 2 - (s.val + 2) = -s.val by ring] using
      interval_entry_decay_internal m (by linarith [s.property.1] : 2 < s.val + 2) hA
        (fun k r => a k r x) hab i j
  · rw [hx.2 i j, hx.2 (i - 1) j]
    simpa only [show s.val + 2 - 1 = s.val + 1 by ring,
      show 1 - (s.val + 2) = -1 - s.val by ring] using
      interval_first_difference_bound m hm (by linarith [s.property.1] : 1 < s.val + 2)
        hA (fun k r => a k r x) hab i j

/-- See the proof of Proposition 5.15 in the paper: mixed neighboring differences of
the literal interval matrix, including the diagonal. -/
theorem periodized_mixed_difference (s : Riesz1.RieszExponent)
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (n m : ℕ+) (hm : 2 ≤ (m : ℕ)) (K : ℕ) (C κ γ ε : ℝ)
    (hC : 0 ≤ C) (M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M) :
    ∀ᵐ x ∂ν, ∀ i j,
      |(M x i j - M x (i - 1) j) - (M x i (j - 1) - M x (i - 1) (j - 1))| ≤
        (2 * (C * (n : ℝ) ^ (κ * ε)) *
          ((∑' k : ℕ, (1 + (k : ℝ)) ^ (-(s.val + 2))) + 2 ^ (s.val + 2))) *
            (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-(s.val + 2)) := by
  obtain ⟨a, _, ha⟩ := periodizedMatrixBounds_entry_representation s n m hm K C κ γ ε M hM
  filter_upwards [ha] with x hx
  intro i j
  have hab (k : Fin (m : ℕ)) (r : Fin ((m : ℕ) / 2)) :
      |a k r x| ≤ (C * (n : ℝ) ^ (κ * ε)) * ((r.val + 1 : ℕ) : ℝ) ^ (-(s.val + 2)) := by
    simpa only [abs_of_nonneg (hx.1 k r).1, show -(s.val + 2) = -s.val - 2 by ring]
      using (hx.1 k r).2.1
  simp_rw [hx.2]
  exact interval_mixed_difference_bound m hm (by linarith [s.property.1] : 1 < s.val + 2)
    (mul_nonneg hC (Real.rpow_nonneg (by positivity) _)) (fun k r => a k r x) hab i j

/-- See the proof of Proposition 5.15 in the paper: centering a column along a short
arc gains the source distance. Applying the same argument to a row
increment gives the second gain needed for neighboring exterior fields.
The conditional matrix envelopes are internal inputs, supplied above from
the interval representation. -/
theorem centered_column_oscillation_internal (s : Riesz1.RieszExponent) (m : ℕ+)
    (hm : 2 ≤ (m : ℕ)) (M : Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hsym : ∀ i j, M i j = M j i)
    (hfirst : ∀ i j, |M i j - M (i - 1) j| ≤ A * weightRadius m i j ^ (-(1 + s.val)))
    (hmixed : ∀ i j, |(M i j - M (i - 1) j) - (M i (j - 1) - M (i - 1) (j - 1))| ≤
      B * weightRadius m i j ^ (-(2 + s.val)))
    (l i₀ i : Fin (m : ℕ))
    (hi : (Riesz1.cyclicIndexDistance m i₀ i : ℝ) ≤ weightRadius m i₀ l / 2) :
    |M l i - M l i₀| ≤ (A * 2 ^ (1 + s.val)) * 2 ^ (1 + s.val) *
      weightRadius m i₀ l ^ (-(1 + s.val)) * (Riesz1.cyclicIndexDistance m i₀ i : ℝ) ∧
    |(M l i - M (l - 1) i) - (M l i₀ - M (l - 1) i₀)| ≤
      (B * 2 ^ (2 + s.val)) * 2 ^ (2 + s.val) *
        weightRadius m i₀ l ^ (-(2 + s.val)) * (Riesz1.cyclicIndexDistance m i₀ i : ℝ) := by
  have hs : 0 < s.val := s.property.1
  constructor
  · apply GlobalCommutators.Internal.spatial_localized_increment m i₀ l i
      (1 + s.val) (A * 2 ^ (1 + s.val)) (by linarith) (by positivity)
      (fun k => M l k) _ hi
    intro k
    have hh := hfirst (k + 1) l
    simp only [add_sub_cancel_right, ← hsym l] at hh
    have hd := forward_distance_power m hm k l (by linarith : 0 ≤ 1 + s.val)
    change weightRadius m (k + 1) l ^ (-(1 + s.val)) ≤
      2 ^ (1 + s.val) * weightRadius m k l ^ (-(1 + s.val)) at hd
    exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_left hd hA])
  · apply GlobalCommutators.Internal.spatial_localized_increment m i₀ l i
      (2 + s.val) (B * 2 ^ (2 + s.val)) (by linarith) (by positivity)
      (fun k => M l k - M (l - 1) k) _ hi
    intro k
    have hh := hmixed l (k + 1)
    simp only [add_sub_cancel_right] at hh
    have hd := forward_distance_power m hm k l (by linarith : 0 ≤ 2 + s.val)
    change weightRadius m (k + 1) l ^ (-(2 + s.val)) ≤
      2 ^ (2 + s.val) * weightRadius m k l ^ (-(2 + s.val)) at hd
    rw [weightRadius_eq_comm] at hh
    have hw : 1 + (Riesz1.cyclicIndexDistance m (k + 1) l : ℝ) = weightRadius m (k + 1) l := rfl
    rw [hw] at hh
    exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_left hd hB])

section Centering

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  {ν : Measure Ω}

/-- See the proof of Proposition 5.15 in the paper: exact exterior cancellation, as an
identity of representatives almost everywhere. The correction on `J` is
retained, including when either side of the partition is empty. -/
theorem exterior_cancellation_internal (J : Finset ι) (r c : Ω → ι → ℝ)
    (v : ι → Lp ℝ 2 ν) (hv : ∀ᵐ x ∂ν, ∑ i, v i x = 0) :
    ∀ᵐ x ∂ν, ∀ l,
      (∑ i ∈ Jᶜ, r x i * v i x) =
        (∑ i ∈ Jᶜ, (r x i - c x l) * v i x) - c x l * ∑ i ∈ J, v i x := by
  filter_upwards [hv] with x hx
  intro l
  simpa only [compl_compl] using
    FiniteZeroSumBounds.centered_subset Jᶜ (r x) (fun i => v i x) (c x l) hx

/-- See the proof of Proposition 5.15 in the paper: the same cancellation for a difference
of two exterior rows. This includes the subtracted interior sum. -/
theorem exterior_increment_cancellation_internal (J : Finset ι)
    (r₀ r₁ : Ω → ι → ℝ) (c₀ c₁ : Ω → ℝ)
    (v : ι → Lp ℝ 2 ν) (hv : ∀ᵐ x ∂ν, ∑ i, v i x = 0) :
    ∀ᵐ x ∂ν,
      (∑ i ∈ Jᶜ, r₁ x i * v i x) - (∑ i ∈ Jᶜ, r₀ x i * v i x) =
        (∑ i ∈ Jᶜ, ((r₁ x i - c₁ x) - (r₀ x i - c₀ x)) * v i x) -
          (c₁ x - c₀ x) * ∑ i ∈ J, v i x := by
  filter_upwards [hv] with x hx
  have hc := FiniteZeroSumBounds.centered_subset Jᶜ
    (fun i => r₁ x i - r₀ x i) (fun i => v i x) (c₁ x - c₀ x) hx
  simp only [compl_compl, sub_mul, sum_sub_distrib] at hc ⊢
  convert hc using 1; ring

/-- See the proof of Proposition 5.15 in the paper: weighted L² control of a centered
exterior row. This internal estimate keeps both coefficient energies. Their
geometric bounds must be proved for the matrix under consideration. -/
theorem centered_exterior_row_internal (J : Finset ι) (r : Ω → ι → ℝ)
    (hr : ∀ i, Measurable (fun x => r x i)) (c : Ω → ℝ)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (U V : ℝ)
    (hU : ∀ᵐ x ∂ν, Real.sqrt (∑ i ∈ Jᶜ, ((r x i - c x) / w i) ^ 2) ≤ U)
    (hV : ∀ᵐ x ∂ν, |c x| * Real.sqrt (∑ i ∈ J, (1 / w i) ^ 2) ≤ V)
    (v : ι → Lp ℝ 2 ν) (hv : ∀ᵐ x ∂ν, ∑ i, v i x = 0) :
    ∃ f : Lp ℝ 2 ν, (∀ᵐ x ∂ν, f x = ∑ i ∈ Jᶜ, r x i * v i x) ∧
      ‖f‖ ≤ (U + V) * Real.sqrt (∑ i, (w i * ‖v i‖) ^ 2) := by
  let E := fun x => Real.sqrt (∑ i, (w i * v i x) ^ 2)
  have hE : MemLp E 2 ν := FiniteMixedL2.weighted_memLp w v
  have hpt : ∀ᵐ x ∂ν, ‖∑ i ∈ Jᶜ, r x i * v i x‖ ≤ (U + V) * ‖E x‖ := by
    filter_upwards [hU, hV, hv] with x hx hy hz
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), E, compl_compl] using
      FiniteZeroSumBounds.centered_subset_bound Jᶜ (r x) (fun i => v i x) w (c x)
        U V hz hw hx (by simpa only [compl_compl] using hy)
  have hf : MemLp (fun x => ∑ i ∈ Jᶜ, r x i * v i x) 2 ν :=
    hE.of_le_mul (Jᶜ.aestronglyMeasurable_fun_sum (fun i _ =>
      (hr i).aestronglyMeasurable.mul (Lp.aestronglyMeasurable (v i)))) hpt
  have hn : ‖hf.toLp _‖ ≤ (U + V) * ‖hE.toLp E‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hf.coeFn_toLp, hE.coeFn_toLp, hpt] with x hx hy hz
    simpa only [hx, hy] using hz
  have he : ‖hE.toLp E‖ = Real.sqrt (∑ i, (w i * ‖v i‖) ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg (hE.toLp E)), ← CyclicFourierL2.integral_sq]
    rw [integral_congr_ae (hE.coeFn_toLp.mono (fun x hx => congrArg (fun y : ℝ => y ^ 2) hx))]
    exact congrArg Real.sqrt (FiniteMixedL2.weighted_sq_integral w v)
  exact ⟨hf.toLp _, hf.coeFn_toLp, by simpa only [he] using hn⟩

omit [DecidableEq ι] in
/-- See Subsection 5.5 of the paper: a finite measurable row with separate entry
envelopes defines an L² source. This estimate preserves the envelopes of
the individual entries, rather than bounding them by their maximum. -/
theorem bounded_row_source_internal (S : Finset ι) (r : Ω → ι → ℝ)
    (hr : ∀ i, Measurable (fun x => r x i)) (B : ι → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hb : ∀ᵐ x ∂ν, ∀ i, |r x i| ≤ B i) (v : ι → Lp ℝ 2 ν) :
    ∃ f : Lp ℝ 2 ν, (∀ᵐ x ∂ν, f x = ∑ i ∈ S, r x i * v i x) ∧
      ‖f‖ ≤ ∑ i ∈ S, B i * ‖v i‖ := by
  have hp (i : ι) := BoundedMatrixModes.exists_multiplier (fun x => r x i)
    (hr i) (B i) (hB i) (hb.mono (fun _ hx => hx i)) (v i)
  choose g hg hgn using hp
  refine ⟨∑ i ∈ S, g i, ?_, (norm_sum_le _ _).trans (sum_le_sum fun i _ => hgn i)⟩
  filter_upwards [Lp.coeFn_fun_finsetSum S g, ae_all_iff.mpr hg] with x hx hy
  rw [hx]
  exact sum_congr rfl (fun i _ => hy i)

/-- See the proof of Proposition 5.15 in the paper: an existing L² row representative
satisfies every proved centered coefficient-energy bound. This permits the
same source to be used with several partitions or weights. -/
theorem centered_exterior_norm_internal (J : Finset ι) (r : Ω → ι → ℝ)
    (hr : ∀ i, Measurable (fun x => r x i)) (c : Ω → ℝ)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (U V : ℝ)
    (hU : ∀ᵐ x ∂ν, Real.sqrt (∑ i ∈ Jᶜ, ((r x i - c x) / w i) ^ 2) ≤ U)
    (hV : ∀ᵐ x ∂ν, |c x| * Real.sqrt (∑ i ∈ J, (1 / w i) ^ 2) ≤ V)
    (v : ι → Lp ℝ 2 ν) (hv : ∀ᵐ x ∂ν, ∑ i, v i x = 0)
    (f : Lp ℝ 2 ν) (hf : ∀ᵐ x ∂ν, f x = ∑ i ∈ Jᶜ, r x i * v i x) :
    ‖f‖ ≤ (U + V) * Real.sqrt (∑ i, (w i * ‖v i‖) ^ 2) := by
  obtain ⟨g, hg, hgn⟩ := centered_exterior_row_internal J r hr c w hw U V hU hV v hv
  have he : f = g := by
    apply Lp.ext
    filter_upwards [hf, hg] with x hx hy
    exact hx.trans hy.symm
  simpa only [he] using hgn

end Centering

/-- See the proof of Proposition 5.15 in the paper: the first absolute source moment
on a ball is bounded by `R^s` times the global weighted norm. Factoring its
coefficient square as `r^s r^(s-1)` handles the entire exponent range. -/
theorem weighted_first_moment_internal (s : Riesz1.RieszExponent) (m : ℕ+)
    (i₀ : Fin (m : ℕ)) (R : ℝ) (hR : 1 ≤ R)
    {V : Type*} [NormedAddCommGroup V] (v : Fin (m : ℕ) → V) :
    (∑ i ∈ univ.filter (fun i => weightRadius m i i₀ ≤ R), weightRadius m i i₀ * ‖v i‖) ≤
      Real.sqrt (2 / s.val) * R ^ s.val *
        Real.sqrt (∑ i, (weightRadius m i i₀ ^ (3 / 2 - s.val) * ‖v i‖) ^ 2) := by
  let S := univ.filter (fun i => weightRadius m i i₀ ≤ R)
  let r := fun i => weightRadius m i i₀
  have hr (i) : 0 < r i := by dsimp only [r]; linarith [one_le_weightRadius m i i₀]
  have hRp : 0 < R := by linarith
  have he (i : Fin (m : ℕ)) :
      (r i / r i ^ (3 / 2 - s.val)) ^ 2 = r i ^ s.val * r i ^ (-(1 - s.val)) := by
    have hid : r i / r i ^ (3 / 2 - s.val) = r i ^ (1 - (3 / 2 - s.val)) := by
      simpa only [Real.rpow_one] using (Real.rpow_sub (hr i) 1 (3 / 2 - s.val)).symm
    rw [hid,
      ← Real.rpow_natCast, ← Real.rpow_mul (hr i).le, ← Real.rpow_add (hr i)]
    congr 1
    norm_num
    ring
  have hcoeff : (∑ i ∈ S, (r i / r i ^ (3 / 2 - s.val)) ^ 2) ≤
      (2 / s.val) * R ^ (2 * s.val) := by
    calc
      _ = ∑ i ∈ S, r i ^ s.val * r i ^ (-(1 - s.val)) := sum_congr rfl (fun i _ => he i)
      _ ≤ ∑ i ∈ S, R ^ s.val * r i ^ (-(1 - s.val)) := by
        apply sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (hr i).le (mem_filter.mp hi).2 s.property.1.le)
          (Real.rpow_nonneg (hr i).le _)
      _ ≤ R ^ s.val * ((2 / s.val) * R ^ s.val) := by
        rw [← mul_sum]
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hRp.le _)
        simpa only [S, r, show 1 - (1 - s.val) = s.val by ring] using
          sum_weightRadius_le_of_lt_one m i₀ (sub_pos.mpr s.property.2)
            (by linarith [s.property.1] : 1 - s.val < 1) hR
      _ = _ := by
        rw [show 2 * s.val = s.val + s.val by ring, Real.rpow_add hRp]
        ring
  have hcs := FiniteZeroSumBounds.weighted_cauchy_subset S
    (fun i => r i ^ (3 / 2 - s.val)) r (fun i => ‖v i‖)
    (fun i => Real.rpow_pos_of_pos (hr i) _)
  have habs (i : Fin (m : ℕ)) : |r i * ‖v i‖| = r i * ‖v i‖ :=
    abs_of_nonneg (mul_nonneg (hr i).le (norm_nonneg _))
  simp_rw [habs] at hcs
  have hroot := Real.sqrt_le_sqrt hcoeff
  have hnr : Real.sqrt (R ^ (2 * s.val)) = R ^ s.val := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hRp.le]
    congr 1
    ring
  rw [Real.sqrt_mul (div_nonneg (by norm_num) s.property.1.le), hnr] at hroot
  simpa only [S, r, mul_assoc] using
    hcs.trans (mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _))

/-- See the proof of Proposition 5.15 in the paper: the exterior rows of the actual
constrained solution are L² classes, obey the interval entry and increment
envelopes, and satisfy the exact centered cancellation. This is the exterior
part before the weighted geometric sums and the Schur correction. -/
theorem exterior_rows (s : Riesz1.RieszExponent)
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (n m : ℕ+) (hm : 2 ≤ (m : ℕ)) (K : ℕ) (C κ γ ε β : ℝ)
    (hC : 0 ≤ C) (Q : ScalarFormData ν)
    (M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M)
    (f : Fin (m : ℕ) → Lp ℝ 2 ν) (u : Fin (m : ℕ) → Q.1)
    (hu : WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _) f u)
    (J : Finset (Fin (m : ℕ))) (i₀ : Fin (m : ℕ)) :
    let A := C * (n : ℝ) ^ (κ * ε) * ((1 + 1 / s.val) * 2 ^ s.val)
    let B := 2 * (C * (n : ℝ) ^ (κ * ε)) * (1 + 1 / (s.val + 1)) * 2 ^ (s.val + 1)
    ∃ q : Fin (m : ℕ) → Lp ℝ 2 ν, ∀ l,
      (∀ᵐ x ∂ν, q l x = ∑ i ∈ Jᶜ, M x l i * (u i).val x) ∧
      (∀ᵐ x ∂ν, q l x =
        (∑ i ∈ Jᶜ, (M x l i - M x l i₀) * (u i).val x) -
          M x l i₀ * ∑ i ∈ J, (u i).val x) ∧
      ‖q l‖ ≤ A * ∑ i ∈ Jᶜ,
        (1 + (Riesz1.cyclicIndexDistance m l i : ℝ)) ^ (-s.val) * ‖(u i).val‖ ∧
      ‖q l - q (l - 1)‖ ≤ B * ∑ i ∈ Jᶜ,
        (1 + (Riesz1.cyclicIndexDistance m l i : ℝ)) ^ (-1 - s.val) * ‖(u i).val‖ := by
  dsimp only
  let A := C * (n : ℝ) ^ (κ * ε) * ((1 + 1 / s.val) * 2 ^ s.val)
  let B := 2 * (C * (n : ℝ) ^ (κ * ε)) * (1 + 1 / (s.val + 1)) * 2 ^ (s.val + 1)
  have hs : 0 < s.val := s.property.1
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hb := periodized_entry_and_difference s n m hm K C κ γ ε hC M hM
  have hp (l : Fin (m : ℕ)) := bounded_row_source_internal Jᶜ
    (fun x i => M x l i) (fun i => hM.1 l i)
    (fun i => A * (1 + (Riesz1.cyclicIndexDistance m l i : ℝ)) ^ (-s.val))
    (fun i => mul_nonneg hA (Real.rpow_nonneg (by positivity) _))
    (hb.mono (fun _ hx i => by simpa only [A] using (hx l i).1)) (fun i => (u i).val)
  choose q hq hqn using hp
  refine ⟨q, fun l => ⟨hq l, ?_, ?_, ?_⟩⟩
  · have hz : ∀ᵐ x ∂ν, ∑ i, (u i).val x = 0 := hu.1.1
    have he := exterior_cancellation_internal J (fun x i => M x l i)
      (fun x _ => M x l i₀) (fun i => (u i).val) hz
    filter_upwards [hq l, he] with x hx hy
    exact hx.trans (hy l)
  · simpa only [A, mul_assoc, mul_sum] using hqn l
  · obtain ⟨g, hg, hgn⟩ := bounded_row_source_internal Jᶜ
      (fun x i => M x l i - M x (l - 1) i)
      (fun i => (hM.1 l i).sub (hM.1 (l - 1) i))
      (fun i => B * (1 + (Riesz1.cyclicIndexDistance m l i : ℝ)) ^ (-1 - s.val))
      (fun i => mul_nonneg hB (Real.rpow_nonneg (by positivity) _))
      (hb.mono (fun _ hx i => (hx l i).2)) (fun i => (u i).val)
    have he : q l - q (l - 1) = g := by
      apply Lp.ext
      filter_upwards [hq l, hq (l - 1), hg, Lp.coeFn_sub (q l) (q (l - 1))] with x hx hy hz hs
      rw [hs, Pi.sub_apply, hx, hy, hz]
      simp only [sub_mul, sum_sub_distrib]
    rw [he]
    simpa only [B, mul_assoc, mul_sum] using hgn

/-- See the proof of Proposition 5.15 in the paper: the power sum appearing in the
exterior row bound, uniformly across `s = 1/2`. Splitting each square into
two powers avoids a separate logarithmic case. -/
theorem truncated_square_power_sum_internal (s : Riesz1.RieszExponent)
    (δ R : ℕ) (hδ : 1 ≤ δ) (hR : 1 ≤ R) :
    (∑ k ∈ Icc δ R, (k : ℝ) ^ (-2 * s.val)) ≤
      (1 / (1 - s.val)) * (R : ℝ) ^ (1 - s.val) * (δ : ℝ) ^ (-s.val) := by
  have hδp : (0 : ℝ) < δ := by exact_mod_cast hδ
  calc
    _ ≤ ∑ k ∈ Icc δ R, (δ : ℝ) ^ (-s.val) * (k : ℝ) ^ (-s.val) := by
      apply sum_le_sum
      intro k hk
      have hkδ : (δ : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
      have hkp : (0 : ℝ) < k := hδp.trans_le hkδ
      rw [show -2 * s.val = -s.val + -s.val by ring, Real.rpow_add hkp]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hδp hkδ (by linarith [s.property.1]))
        (Real.rpow_nonneg hkp.le _)
    _ ≤ (δ : ℝ) ^ (-s.val) * ∑ k ∈ Icc 1 R, (k : ℝ) ^ (-s.val) := by
      rw [← mul_sum]
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hδp.le _)
      exact sum_le_sum_of_subset_of_nonneg
        (Icc_subset_Icc hδ le_rfl) (fun k _ _ => Real.rpow_nonneg (Nat.cast_nonneg k) _)
    _ ≤ (δ : ℝ) ^ (-s.val) * ((R : ℝ) ^ (1 - s.val) / (1 - s.val)) :=
      mul_le_mul_of_nonneg_left (subcritical_power_sum s.property.1 s.property.2 hR).2
        (Real.rpow_nonneg hδp.le _)
    _ = _ := by ring

section EndpointSummation

variable {V : Type*} [NormedAddCommGroup V]

/-- See the proof of Proposition 5.15 in the paper: summing the entry estimate on the
active block gives its ℓ¹ mass. No regularity of the values is required. -/
theorem active_mass_internal (n : ℕ+) (a A : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hA : 0 ≤ A) (f : Fin (n : ℕ) → V)
    (hf : ∀ i, ‖f i‖ ≤ A *
      ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-a)) :
    (∑ i, ‖f i‖) ≤ A * (2 / (1 - a)) * (n : ℝ) ^ (1 - a) := by
  calc
    _ ≤ ∑ i : Fin (n : ℕ), A *
        ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-a) :=
      sum_le_sum fun i _ => hf i
    _ ≤ A * (2 / (1 - a) * (n : ℝ) ^ (1 - a)) := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left
        (LocalizedBoundary.boundary_weight_sum_internal n a ha ha1) hA
    _ = _ := by ring

/-- See the proof of Proposition 5.15 in the paper: zero extension to the new cycle
preserves the mass estimate of the retained interval. -/
theorem extended_mass_internal (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
    (a A : ℝ) (ha : 0 < a) (ha1 : a < 1) (hA : 0 ≤ A)
    (f : Fin (m : ℕ) → V) (hsupport : ∀ i, (n : ℕ) ≤ i.val → f i = 0)
    (hf : ∀ i : Fin (n : ℕ), ‖f (i.castLE hnm)‖ ≤ A *
      ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-a)) :
    (∑ i, ‖f i‖) ≤ A * (2 / (1 - a)) * (n : ℝ) ^ (1 - a) := by
  rw [LocalizedBoundary.sum_active_internal n m hnm (fun i => ‖f i‖)
    (fun i hi => by rw [hsupport i hi, norm_zero])]
  exact active_mass_internal n a A ha ha1 hA (fun i => f (i.castLE hnm)) hf

/-- See the proof of Proposition 5.15 in the paper: the mass in scale-normalized form.
The source factor and the parent separation are retained explicitly. -/
theorem scaled_extended_mass_internal (s : Riesz1.RieszExponent)
    (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ)) (R A : ℝ)
    (hR : 0 < R) (hnR : (n : ℝ) ≤ R) (hA : 0 ≤ A)
    (f : Fin (m : ℕ) → V) (hsupport : ∀ i, (n : ℕ) ≤ i.val → f i = 0)
    (hf : ∀ i : Fin (n : ℕ), ‖f (i.castLE hnm)‖ ≤ A * R ^ (-1 + s.val / 2) *
      ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val / 2)) :
    (∑ i, ‖f i‖) ≤ (2 / (1 - s.val / 2)) * A := by
  have hs : 0 < s.val := s.property.1
  have hs1 : s.val < 1 := s.property.2
  have hb : 0 < 1 - s.val / 2 := by linarith
  have hn : (n : ℝ) ^ (1 - s.val / 2) ≤ R ^ (1 - s.val / 2) :=
    Real.rpow_le_rpow (by positivity) hnR hb.le
  have he : R ^ (-1 + s.val / 2) * R ^ (1 - s.val / 2) = 1 := by
    rw [← Real.rpow_add hR, show (-1 + s.val / 2) + (1 - s.val / 2) = 0 by ring,
      Real.rpow_zero]
  calc
    _ ≤ (A * R ^ (-1 + s.val / 2)) * (2 / (1 - s.val / 2)) *
        (n : ℝ) ^ (1 - s.val / 2) :=
      extended_mass_internal n m hnm (s.val / 2) _ (by linarith) (by linarith)
        (by positivity) f hsupport (by simpa only [neg_div] using hf)
    _ ≤ (A * R ^ (-1 + s.val / 2)) * (2 / (1 - s.val / 2)) *
        R ^ (1 - s.val / 2) := mul_le_mul_of_nonneg_left hn (by positivity)
    _ = _ := by
      calc
        _ = (2 / (1 - s.val / 2)) * A *
            (R ^ (-1 + s.val / 2) * R ^ (1 - s.val / 2)) := by ring
        _ = _ := by rw [he, mul_one]

end EndpointSummation

/-- See the proof of Proposition 5.15 in the paper: the weighted source sum for the
Schur term. This is Cauchy–Schwarz followed by the subcritical endpoint
power sum. The range `0 < s < 1` is literal. -/
theorem schur_source_weight_internal (s : Riesz1.RieszExponent) (n : ℕ+)
    {V : Type*} [NormedAddCommGroup V] (v : Fin (n : ℕ) → V) :
    (∑ i, ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val / 2) * ‖v i‖) ≤
      Real.sqrt (2 / (1 - s.val)) * (n : ℝ) ^ ((1 - s.val) / 2) *
        Real.sqrt (∑ i, ‖v i‖ ^ 2) := by
  let d := fun i : Fin (n : ℕ) => ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ)
  have hd (i : Fin (n : ℕ)) : 0 < d i := by
    dsimp only [d]
    have hi := i.isLt
    exact_mod_cast (show 0 < min (i.val + 1) ((n : ℕ) - i.val) by omega)
  have hsq (i : Fin (n : ℕ)) : (d i ^ (-s.val / 2)) ^ 2 = d i ^ (-s.val) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hd i).le]
    congr 1
    norm_num
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt univ
    (fun i : Fin (n : ℕ) => d i ^ (-s.val / 2)) (fun i => ‖v i‖)
  simp_rw [hsq] at hcs
  have hb := LocalizedBoundary.boundary_weight_sum_internal n s.val s.property.1 s.property.2
  have hroot := Real.sqrt_le_sqrt hb
  have hnr : Real.sqrt ((n : ℝ) ^ (1 - s.val)) = (n : ℝ) ^ ((1 - s.val) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (show (0 : ℝ) ≤ n by positivity)]
    congr 1
    ring
  rw [Real.sqrt_mul (div_nonneg (by norm_num) (sub_pos.mpr s.property.2).le), hnr] at hroot
  simpa only [d, mul_assoc] using
    hcs.trans (mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _))

section Duality

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- See the proof of Proposition 5.15 in the paper: the L² duality step which turns
the bilinear Schur estimates into operator bounds. Testing with the output
itself handles every real Hilbert space, without a completeness assumption. -/
theorem norm_of_pairing_bound_internal (y : H) (A : ℝ) (hA : 0 ≤ A)
    (hy : ∀ η : H, |inner ℝ η y| ≤ A * ‖η‖) : ‖y‖ ≤ A := by
  have hh := hy y
  rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at hh
  nlinarith [norm_nonneg y]

/-- See the proof of Proposition 5.15 in the paper: source-by-source Schur superposition
after L² duality. The conditional hypotheses are internal operator bounds,
to be supplied by Lemma 5.5 for the actual exterior resolvent. -/
theorem schur_superposition_internal {ι : Type*} [Fintype ι]
    (T : ι → H →L[ℝ] H) (a : ι → ℝ) (B : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hB : 0 ≤ B)
    (hT : ∀ i (η φ : H), |inner ℝ η (T i φ)| ≤ B * a i * ‖η‖ * ‖φ‖)
    (u : ι → H) :
    ‖∑ i, T i (u i)‖ ≤ B * ∑ i, a i * ‖u i‖ := by
  calc
    _ ≤ ∑ i, ‖T i (u i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, B * a i * ‖u i‖ := by
      apply sum_le_sum
      intro i _
      apply norm_of_pairing_bound_internal _ _
        (mul_nonneg (mul_nonneg hB (ha i)) (norm_nonneg _))
      intro η
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hT i η (u i)
    _ = _ := by simp only [mul_assoc, mul_sum]

/-- See the proof of Proposition 5.15 in the paper: insertion of the endpoint source
sum in the Schur operator estimate. The source power is `(1-s)/2`, with
no artificial restriction at `s = 1/2`. -/
theorem schur_endpoint_superposition_internal (s : Riesz1.RieszExponent)
    (n : ℕ+) (T : Fin (n : ℕ) → H →L[ℝ] H) (B : ℝ) (hB : 0 ≤ B)
    (hT : ∀ i (η φ : H), |inner ℝ η (T i φ)| ≤ B *
      ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val / 2) * ‖η‖ * ‖φ‖)
    (u : Fin (n : ℕ) → H) :
    ‖∑ i, T i (u i)‖ ≤ B * Real.sqrt (2 / (1 - s.val)) *
      (n : ℝ) ^ ((1 - s.val) / 2) * Real.sqrt (∑ i, ‖u i‖ ^ 2) := by
  calc
    _ ≤ B * ∑ i, ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^
        (-s.val / 2) * ‖u i‖ :=
      schur_superposition_internal T _ B (fun i => Real.rpow_nonneg (by positivity) _) hB hT u
    _ ≤ B * (Real.sqrt (2 / (1 - s.val)) * (n : ℝ) ^ ((1 - s.val) / 2) *
        Real.sqrt (∑ i, ‖u i‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (schur_source_weight_internal s n u) hB
    _ = _ := by ring

end Duality

section Translation

variable {V : Type*} [NormedAddCommGroup V]

/-- See the proof of Proposition 5.15 in the paper: counting-measure ℓ¹ mass of
normed-group-valued sequences is invariant under cyclic translation. -/
theorem sum_norm_shift_internal (m : ℕ+) (f : Fin (m : ℕ) → V) (h : Fin (m : ℕ)) :
    (∑ i, ‖f (i - h)‖) = ∑ i, ‖f i‖ :=
  (Equiv.subRight h).sum_comp (fun i => ‖f i‖)

/-- See the proof of Proposition 5.15 in the paper: telescoping by a nonnegative
number of edges, for values in any normed additive group. -/
theorem shift_variation_nat_internal (m : ℕ+) (f : Fin (m : ℕ) → V) (k : ℕ) :
    (∑ i, ‖f (i - (k : Fin (m : ℕ))) - f i‖) ≤
      (k : ℝ) * ∑ i, ‖f (i - 1) - f i‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he (i : Fin (m : ℕ)) : i - ((k + 1 : ℕ) : Fin (m : ℕ)) =
        (i - (k : Fin (m : ℕ))) - 1 := by
      push_cast
      abel
    calc
      _ ≤ ∑ i : Fin (m : ℕ),
          (‖f ((i - (k : Fin (m : ℕ))) - 1) - f (i - (k : Fin (m : ℕ)))‖ +
            ‖f (i - (k : Fin (m : ℕ))) - f i‖) := by
        apply sum_le_sum
        intro i _
        rw [he]
        simpa only [dist_eq_norm] using dist_triangle
          (f ((i - (k : Fin (m : ℕ))) - 1)) (f (i - (k : Fin (m : ℕ)))) (f i)
      _ = (∑ i, ‖f (i - 1) - f i‖) +
          ∑ i, ‖f (i - (k : Fin (m : ℕ))) - f i‖ := by
        rw [sum_add_distrib]
        congr 1
        exact (Equiv.subRight (k : Fin (m : ℕ))).sum_comp
          (fun i => ‖f (i - 1) - f i‖)
      _ ≤ (∑ i, ‖f (i - 1) - f i‖) + (k : ℝ) * ∑ i, ‖f (i - 1) - f i‖ :=
        add_le_add le_rfl ih
      _ = _ := by push_cast; ring

/-- See the proof of Proposition 5.15 in the paper: the two orientations of a
translation have equal ℓ¹ increment mass. -/
theorem sum_norm_neg_shift_internal (m : ℕ+) (f : Fin (m : ℕ) → V) (h : Fin (m : ℕ)) :
    (∑ i, ‖f (i - -h) - f i‖) = ∑ i, ‖f (i - h) - f i‖ := by
  have he := (Equiv.subRight (-h)).sum_comp (fun i => ‖f (i - h) - f i‖)
  rw [← he]
  apply sum_congr rfl
  intro i _
  change ‖f (i - -h) - f i‖ = ‖f ((i - -h) - h) - f (i - -h)‖
  simp only [sub_neg_eq_add, add_sub_cancel_right]
  exact norm_sub_rev _ _

/-- See the proof of Proposition 5.15 in the paper: translation along a shortest cyclic
arc costs its length times the full nearest-neighbor variation. Both zero
and antipodal translations are included. -/
theorem shift_variation_internal (m : ℕ+) (f : Fin (m : ℕ) → V) (h : Fin (m : ℕ)) :
    (∑ i, ‖f (i - h) - f i‖) ≤
      (Riesz1.cyclicIndexDistance m h 0 : ℝ) * ∑ i, ‖f (i - 1) - f i‖ := by
  have hf := shift_variation_nat_internal m f h.val
  rw [Fin.cast_val_eq_self] at hf
  have hb := shift_variation_nat_internal m f (-h).val
  rw [Fin.cast_val_eq_self, sum_norm_neg_shift_internal] at hb
  by_cases hz : h = 0
  · subst h
    simp [Riesz1.cyclicIndexDistance]
  · have hneg : (-h).val = (m : ℕ) - h.val := by rw [Fin.val_neg, ite_eq_right hz]
    rw [hneg] at hb
    simp only [Riesz1.cyclicIndexDistance, Fin.val_zero, Nat.dist_zero_right]
    rcases le_total h.val ((m : ℕ) - h.val) with hh | hh
    · simpa only [min_eq_left hh] using hf
    · simpa only [min_eq_right hh] using hb

/-- See the proof of Proposition 5.15 in the paper: a truncated interior approximation
controls the translation by its discarded mass and its total variation.
This is the internal form of the boundary-strip/telescoping argument. -/
theorem shift_approximation_internal (m : ℕ+) (f g : Fin (m : ℕ) → V)
    (h : Fin (m : ℕ)) :
    (∑ i, ‖f (i - h) - f i‖) ≤ 2 * (∑ i, ‖f i - g i‖) +
      (Riesz1.cyclicIndexDistance m h 0 : ℝ) * ∑ i, ‖g (i - 1) - g i‖ := by
  have hp (i : Fin (m : ℕ)) : ‖f (i - h) - f i‖ ≤
      ‖f (i - h) - g (i - h)‖ + ‖g (i - h) - g i‖ + ‖f i - g i‖ := by
    have h₁ := dist_triangle (f (i - h)) (g (i - h)) (f i)
    have h₂ := dist_triangle (g (i - h)) (g i) (f i)
    simp only [dist_eq_norm, norm_sub_rev (g i) (f i)] at h₁ h₂
    linarith
  calc
    _ ≤ ∑ i : Fin (m : ℕ),
        (‖f (i - h) - g (i - h)‖ + ‖g (i - h) - g i‖ + ‖f i - g i‖) :=
      sum_le_sum fun i _ => hp i
    _ = 2 * (∑ i, ‖f i - g i‖) + ∑ i, ‖g (i - h) - g i‖ := by
      rw [sum_add_distrib, sum_add_distrib,
        sum_norm_shift_internal m (fun i => f i - g i) h]
      ring
    _ ≤ _ := add_le_add le_rfl (shift_variation_internal m g h)

end Translation

end Riesz2.LocalizedField
