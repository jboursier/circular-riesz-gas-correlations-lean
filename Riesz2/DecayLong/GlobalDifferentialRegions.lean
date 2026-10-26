/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.GlobalCommutators
public import Riesz2.ToMathlib.FiniteZeroSumBounds

/-!
# Regional differential commutator estimates

The comparable-radius and separated-radius estimates in Step 3 of the
proof of Lemma 5.13, equation (5.49).
-/

@[expose] public section

noncomputable section

open Matrix Finset
open scoped BigOperators Fin.NatCast

namespace Riesz2.GlobalCommutators

namespace Internal

/-- Lemma 5.13, Step 3 (equation (5.49)): telescoping on a shortest cyclic
arc uses only increments inside its
closed ball. Both orientations, including wraparound, are retained. -/
theorem oscillation_on_short_arc (N : ℕ+) (c j : Fin (N : ℕ))
    (f : Fin (N : ℕ) → ℝ) (U : ℝ) (hU : 0 ≤ U)
    (hinc : ∀ k, Riesz1.cyclicIndexDistance N c k ≤
      Riesz1.cyclicIndexDistance N c j → |f (k + 1) - f k| ≤ U) :
    |f j - f c| ≤ (Riesz1.cyclicIndexDistance N c j : ℝ) * U := by
  let L := Riesz1.cyclicIndexDistance N c j
  have hhalf : 2 * L ≤ (N : ℕ) := by
    have := Riesz1.APG.cyclicIndexDistance_le_half (N := N) c j
    omega
  have hf : ∀ k : ℕ, k ≤ L →
      |f (c + (k : Fin (N : ℕ))) - f c| ≤ (k : ℝ) * U := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hd := GlobalReferenceErrorInternal.distance_add_length N c
        (r := k) (by omega)
      have hi := hinc (c + (k : Fin (N : ℕ))) (by dsimp [L] at hk ⊢; omega)
      calc
        _ ≤ |f (c + (k : Fin (N : ℕ)) + 1) - f (c + (k : Fin (N : ℕ)))| +
            |f (c + (k : Fin (N : ℕ))) - f c| := by
          simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
            abs_sub_le (f (c + (k : Fin (N : ℕ)) + 1))
              (f (c + (k : Fin (N : ℕ)))) (f c)
        _ ≤ U + (k : ℝ) * U := add_le_add hi (ih (by omega))
        _ = _ := by push_cast; ring
  have hb : ∀ k : ℕ, k ≤ L →
      |f (c - (k : Fin (N : ℕ))) - f c| ≤ (k : ℝ) * U := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hd : Riesz1.cyclicIndexDistance N c
          (c - ((k + 1 : ℕ) : Fin (N : ℕ))) = k + 1 := by
        have hh := GlobalReferenceErrorInternal.distance_add_length N
          (c - ((k + 1 : ℕ) : Fin (N : ℕ))) (r := k + 1) (by omega)
        rw [sub_add_cancel, cyclicIndexDistance_comm'] at hh
        exact hh
      have hi := hinc (c - ((k + 1 : ℕ) : Fin (N : ℕ))) (by
        rw [hd]; exact hk)
      have heq : c - ((k + 1 : ℕ) : Fin (N : ℕ)) + 1 =
          c - (k : Fin (N : ℕ)) := by push_cast; abel
      rw [heq, abs_sub_comm] at hi
      calc
        _ ≤ |f (c - ((k + 1 : ℕ) : Fin (N : ℕ))) - f (c - (k : Fin (N : ℕ)))| +
            |f (c - (k : Fin (N : ℕ))) - f c| := abs_sub_le _ _ _
        _ ≤ U + (k : ℝ) * U := add_le_add hi (ih (by omega))
        _ = _ := by push_cast; ring
  have hdist := GlobalReferenceErrorInternal.distance_eq_min N c j
  by_cases hj : (j - c).val ≤ (N : ℕ) - (j - c).val
  · have he : L = (j - c).val := by dsimp [L]; rw [hdist, min_eq_left hj]
    have hh := hf L le_rfl
    change |f j - f c| ≤ (L : ℝ) * U
    simpa only [he, Fin.cast_val_eq_self, add_sub_cancel] using hh
  · by_cases hz : j - c = 0
    · have : j = c := sub_eq_zero.mp hz
      subst j
      simp only [sub_self, abs_zero]
      positivity
    · have he : L = (-(j - c)).val := by
        dsimp [L]
        rw [hdist, min_eq_right (by omega), Fin.val_neg, ite_eq_right hz]
      have hh := hb L le_rfl
      change |f j - f c| ≤ (L : ℝ) * U
      simpa only [he, Fin.cast_val_eq_self, sub_neg_eq_add, add_sub_cancel] using hh

/-- Lemma 5.13, Step 3 (equation (5.49)): the shortest-arc estimate for the
small-radius rows of the proof of Lemma 5.13. The factor is uniform in the cycle.
There is no loss at the cyclic seam. -/
theorem localized_kernel_increment (N : ℕ+) (i₀ i j : Fin (N : ℕ))
    (t C : ℝ) (ht : 0 ≤ t) (hC : 0 ≤ C) (f : Fin (N : ℕ) → ℝ)
    (hinc : ∀ k, |f (k + 1) - f k| ≤
      C * (1 + (Riesz1.cyclicIndexDistance N i k : ℝ)) ^ (-t))
    (hj : weightRadius N j i₀ < weightRadius N i i₀ / 2) :
    |f j - f i₀| ≤ C * 2 ^ t * weightRadius N i i₀ ^ (-t) *
      (Riesz1.cyclicIndexDistance N i₀ j : ℝ) := by
  let r := weightRadius N i i₀
  have hr : 0 < r := by dsimp [r]; linarith [one_le_weightRadius N i i₀]
  have hb (k : Fin (N : ℕ)) (hk : Riesz1.cyclicIndexDistance N i₀ k ≤
      Riesz1.cyclicIndexDistance N i₀ j) :
      |f (k + 1) - f k| ≤ C * 2 ^ t * r ^ (-t) := by
    have htri : (Riesz1.cyclicIndexDistance N i i₀ : ℝ) ≤
        (Riesz1.cyclicIndexDistance N i k : ℝ) +
          (Riesz1.cyclicIndexDistance N k i₀ : ℝ) := by
      exact_mod_cast cyclicIndexDistance_triangle i k i₀
    have hk' : (Riesz1.cyclicIndexDistance N k i₀ : ℝ) ≤
        (Riesz1.cyclicIndexDistance N j i₀ : ℝ) := by
      simpa only [cyclicIndexDistance_comm' N i₀] using
        (show (Riesz1.cyclicIndexDistance N i₀ k : ℝ) ≤
          (Riesz1.cyclicIndexDistance N i₀ j : ℝ) by exact_mod_cast hk)
    have hgeom : r / 2 ≤ 1 + (Riesz1.cyclicIndexDistance N i k : ℝ) := by
      dsimp [weightRadius] at hj
      dsimp [r, weightRadius]
      linarith
    calc
      _ ≤ C * (1 + (Riesz1.cyclicIndexDistance N i k : ℝ)) ^ (-t) := hinc k
      _ ≤ C * (r / 2) ^ (-t) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by positivity) hgeom (by linarith)) hC
      _ = _ := by
        rw [Real.div_rpow hr.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        simp only [inv_inv, div_eq_mul_inv]
        ring
  have hh := oscillation_on_short_arc N i₀ j f
    (C * 2 ^ t * r ^ (-t)) (by positivity) hb
  nlinarith only [hh]

end Internal

/-- Lemma 5.13, Step 3 (equation (5.49)): the actual factorization kernel
obeys the centered small-radius bound
used in the proof of Lemma 5.13, with a constant
linear in its shift. -/
theorem factorization_centered_entry_bound (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (a : ℝ) (ha : 0 < a) (B : ℝ) (i₀ i j : Fin (N : ℕ)),
      weightRadius N j i₀ < weightRadius N i i₀ / 2 →
      |factorizationMatrix s N hN a ha B i j -
        factorizationMatrix s N hN a ha B i i₀| ≤
        C * (a + B ^ 2 / a) * weightRadius N i i₀ ^ (-(3 - s.val)) *
          weightRadius N j i₀ := by
  obtain ⟨C, hC, hb⟩ := factorizationMatrix_increment_decay hz s
  refine ⟨C * 2 ^ (3 - s.val), by positivity, ?_⟩
  intro N hN a ha B i₀ i j hj
  have hh := Internal.localized_kernel_increment N i₀ i j (3 - s.val)
    (C * (a + B ^ 2 / a)) (by linarith [s.property.2]) (by
      exact mul_nonneg hC.le (factorization_shift_pos ha B).le)
    (fun j => factorizationMatrix s N hN a ha B i j) (fun k => ?_) hj
  · have hd : (Riesz1.cyclicIndexDistance N i₀ j : ℝ) ≤ weightRadius N j i₀ := by
      rw [weightRadius_eq_comm]
      linarith
    exact hh.trans (by
      convert mul_le_mul_of_nonneg_left hd (show 0 ≤
        C * (a + B ^ 2 / a) * 2 ^ (3 - s.val) *
          weightRadius N i i₀ ^ (-(3 - s.val)) by
            have hr : 0 < weightRadius N i i₀ := by linarith [one_le_weightRadius N i i₀]
            positivity) using 1; ring)
  · rw [factorizationMatrix_kernel s N hN a ha B i (k + 1),
      factorizationMatrix_kernel s N hN a ha B i k]
    have heq : k + 1 - i = (k - i) + 1 := by abel
    rw [heq]
    have hd : Riesz1.cyclicIndexDistance N (k - i) 0 =
        Riesz1.cyclicIndexDistance N i k := by
      rw [← GlobalReferenceErrorInternal.distance_translate N (k - i) 0 i]
      simpa only [sub_add_cancel, zero_add] using cyclicIndexDistance_comm' N k i
    simpa only [hd] using hb N hN a ha B (k - i)


namespace Internal

/-- Lemma 5.13, Step 3 (equation (5.49)): the unnormalized comparable-radius
kernel, before the row and column Schur estimates. -/
theorem comparable_raw {s x y D C A : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hy : 0 < y) (hyx : y ≤ x)
    (hnear : x ≤ 2 * y) (hD : 0 < D) (hgeom : |x - y| ≤ D)
    (hupper : D ≤ x + y) (hC : 0 ≤ C)
    (hA : |A| ≤ C * D ^ (-(2 - s))) :
    |A| * (x ^ (3 / 2 - s) - y ^ (3 / 2 - s)) ^ 2 ≤
      16 * C * y ^ (1 - s) := by
  have hpowerDifference {x y a : ℝ} (hy : 0 < y) (hyx : y ≤ x)
      (ha : 0 ≤ a) (ha2 : a ≤ 2) :
      |x ^ a - y ^ a| ≤ 2 * x ^ (a - 1) * (x - y) := by
    have hx : 0 < x := hy.trans_le hyx
    let t := y / x
    have ht : 0 < t := div_pos hy hx
    have ht1 : t ≤ 1 := (div_le_one hx).mpr hyx
    have hpow := Real.rpow_le_rpow_of_exponent_ge ht ht1 ha2
    rw [Real.rpow_two] at hpow
    have hlin : 1 - t ^ a ≤ 2 * (1 - t) := by nlinarith [sq_nonneg (1 - t)]
    have hyid : y ^ a = x ^ a * t ^ a := by
      dsimp [t]
      rw [Real.div_rpow hy.le hx.le]
      field_simp
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.rpow_le_rpow hy.le hyx ha))]
    calc
      _ = x ^ a * (1 - t ^ a) := by rw [hyid]; ring
      _ ≤ x ^ a * (2 * (1 - t)) := mul_le_mul_of_nonneg_left hlin (by positivity)
      _ = _ := by
        have hxa : x ^ a = x ^ (a - 1) * x := by
          rw [← Real.rpow_add_one hx.ne']
          congr 1
          ring
        rw [hxa]
        dsimp [t]
        field_simp
  have htwo {x y e : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
      (he0 : 0 ≤ e) (he1 : e ≤ 1) (hxy : x ≤ 2 * y) :
      x ^ e ≤ 2 * y ^ e := by
    calc
      _ ≤ (2 * y) ^ e := Real.rpow_le_rpow hx hxy he0
      _ = 2 ^ e * y ^ e := Real.mul_rpow (by norm_num) hy
      _ ≤ 2 * y ^ e := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hy _)
        have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he1
        simpa only [Real.rpow_one] using hh
  have hx : 0 < x := hy.trans_le hyx
  have hdiff := hpowerDifference hy hyx
    (show 0 ≤ 3 / 2 - s by linarith) (show 3 / 2 - s ≤ (2 : ℝ) by linarith)
  have hdx : 0 ≤ x - y := sub_nonneg.mpr hyx
  rw [abs_of_nonneg hdx] at hgeom
  have hdiff' : (x ^ (3 / 2 - s) - y ^ (3 / 2 - s)) ^ 2 ≤
      4 * x ^ (2 * ((3 / 2 - s) - 1)) * D ^ 2 := by
    have hroot : |x ^ (3 / 2 - s) - y ^ (3 / 2 - s)| ≤
        2 * x ^ ((3 / 2 - s) - 1) * D :=
      hdiff.trans (mul_le_mul_of_nonneg_left hgeom (by positivity))
    have hh := mul_self_le_mul_self (abs_nonneg _) hroot
    simp only [← pow_two, sq_abs] at hh
    have hpow : x ^ (2 * ((3 / 2 - s) - 1)) = (x ^ ((3 / 2 - s) - 1)) ^ 2 := by
      rw [mul_comm, Real.rpow_mul hx.le, Real.rpow_two]
    rw [hpow]
    nlinarith only [hh]
  have hDs : D ^ s ≤ 2 * x ^ s :=
    htwo hD.le hx.le hs0.le hs1.le (by linarith)
  have hxy : x ^ (1 - s) ≤ 2 * y ^ (1 - s) :=
    htwo hx.le hy.le (by linarith) (by linarith) hnear
  have hraw : |A| * (x ^ (3 / 2 - s) - y ^ (3 / 2 - s)) ^ 2 ≤
      16 * C * y ^ (1 - s) := by
    calc
      _ ≤ (C * D ^ (-(2 - s))) *
          (4 * x ^ (2 * ((3 / 2 - s) - 1)) * D ^ 2) :=
        mul_le_mul hA hdiff' (sq_nonneg _) (by positivity)
      _ = 4 * C * x ^ (2 * ((3 / 2 - s) - 1)) * D ^ s := by
        have hh : D ^ (-(2 - s)) * D ^ (2 : ℕ) = D ^ s := by
          rw [← Real.rpow_two, ← Real.rpow_add hD]
          congr 1
          ring
        calc
          _ = 4 * C * x ^ (2 * ((3 / 2 - s) - 1)) *
              (D ^ (-(2 - s)) * D ^ (2 : ℕ)) := by ring
          _ = _ := by rw [hh]
      _ ≤ 4 * C * x ^ (2 * ((3 / 2 - s) - 1)) * (2 * x ^ s) :=
        mul_le_mul_of_nonneg_left hDs (by positivity)
      _ = 8 * C * x ^ (1 - s) := by
        rw [show 4 * C * x ^ (2 * ((3 / 2 - s) - 1)) * (2 * x ^ s) =
          8 * C * (x ^ (2 * ((3 / 2 - s) - 1)) * x ^ s) by ring,
          ← Real.rpow_add hx, show 2 * ((3 / 2 - s) - 1) + s = 1 - s by ring]
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hxy (show 0 ≤ 8 * C by positivity)]
  exact hraw

/-- Lemma 5.13, Step 3 (equation (5.49)): a positive-power shell sum,
including the count of the comparable and smaller-radius regions. -/
theorem sum_positive_power (N : ℕ+) (i₀ : Fin (N : ℕ))
    {R e : ℝ} (hR : 1 ≤ R) (he : 0 ≤ e) :
    (∑ j ∈ univ.filter (fun j => weightRadius N j i₀ ≤ R),
      weightRadius N j i₀ ^ e) ≤ 4 * R ^ (e + 1) := by
  have hRp : 0 < R := by linarith
  calc
    _ ≤ ∑ j ∈ univ.filter (fun j => weightRadius N j i₀ ≤ R),
        R ^ (e + 1 / 2) * weightRadius N j i₀ ^ (-(1 / 2 : ℝ)) := by
      apply sum_le_sum
      intro j hj
      have hr : 0 < weightRadius N j i₀ := by linarith [one_le_weightRadius N j i₀]
      have hjR := (mem_filter.mp hj).2
      calc
        _ = weightRadius N j i₀ ^ (e + 1 / 2) *
            weightRadius N j i₀ ^ (-(1 / 2 : ℝ)) := by
          rw [← Real.rpow_add hr]; congr 1; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hr.le hjR (by linarith)) (by positivity)
    _ = R ^ (e + 1 / 2) * ∑ j ∈ univ.filter
        (fun j => weightRadius N j i₀ ≤ R), weightRadius N j i₀ ^ (-(1 / 2 : ℝ)) :=
      (mul_sum ..).symm
    _ ≤ R ^ (e + 1 / 2) * (4 * R ^ (1 / 2 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      convert sum_weightRadius_le_of_lt_one N i₀
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) hR using 1; norm_num
    _ = _ := by
      rw [show R ^ (e + 1 / 2) * (4 * R ^ (1 / 2 : ℝ)) =
        4 * (R ^ (e + 1 / 2) * R ^ (1 / 2 : ℝ)) by ring, ← Real.rpow_add hRp]
      congr 2
      ring

/-- Lemma 5.13, Step 3 (equation (5.49)): the complementary shell tail at
half a radius. The maximum with one handles the smallest cycles. -/
theorem tail_half (N : ℕ+) (i₀ : Fin (N : ℕ)) {R t : ℝ}
    (hR : 1 ≤ R) (ht : 1 < t) :
    (∑ j ∈ univ.filter (fun j => R / 2 ≤ weightRadius N j i₀),
      weightRadius N j i₀ ^ (-t)) ≤
      (2 * (1 + 1 / (t - 1)) * 2 ^ (t - 1)) * R ^ (1 - t) := by
  have hRp : 0 < R := by linarith
  have heq : univ.filter (fun j => R / 2 ≤ weightRadius N j i₀) =
      univ.filter (fun j => max 1 (R / 2) ≤ weightRadius N j i₀) := by
    ext j
    simp only [mem_filter, mem_univ, true_and, max_le_iff]
    exact ⟨fun h => ⟨one_le_weightRadius N j i₀, h⟩, And.right⟩
  rw [heq]
  calc
    _ ≤ 2 * (1 + 1 / (t - 1)) * (max 1 (R / 2)) ^ (1 - t) :=
      sum_weightRadius_tail_le N i₀ ht (le_max_left ..)
    _ ≤ 2 * (1 + 1 / (t - 1)) * (R / 2) ^ (1 - t) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity)
        (le_max_right ..) (by linarith)) (by positivity)
    _ = _ := by
      rw [Real.div_rpow hRp.le (by norm_num),
        show (1 - t) = -(t - 1) by ring,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      simp only [div_eq_mul_inv, inv_inv]
      ring

/-- Lemma 5.13, Step 3 (equation (5.49)): weighted Cauchy–Schwarz on a
smaller-radius row with a monomial coefficient envelope. -/
theorem small_row (N : ℕ+) (i₀ : Fin (N : ℕ)) {R L u v γ : ℝ}
    (hR : 1 ≤ R) (hL : 0 ≤ L) (he : 0 ≤ 2 * (v - γ))
    (f g : Fin (N : ℕ) → ℝ)
    (hf : ∀ j, weightRadius N j i₀ < R / 2 →
      |f j| ≤ L * R ^ u * weightRadius N j i₀ ^ v) :
    |∑ j ∈ univ.filter (fun j => weightRadius N j i₀ < R / 2), f j * g j| ≤
      2 * L * R ^ (u + v - γ + 1 / 2) *
        Real.sqrt (∑ j, (weightRadius N j i₀ ^ γ * g j) ^ 2) := by
  classical
  let S := univ.filter (fun j => weightRadius N j i₀ < R / 2)
  have hRp : 0 < R := by linarith
  have hr (j) : 0 < weightRadius N j i₀ := by linarith [one_le_weightRadius N j i₀]
  have hsq : (∑ j ∈ S, (f j / weightRadius N j i₀ ^ γ) ^ 2) ≤
      (2 * L * R ^ (u + v - γ + 1 / 2)) ^ 2 := by
    calc
      _ ≤ ∑ j ∈ S, (L * R ^ u) ^ 2 * weightRadius N j i₀ ^ (2 * (v - γ)) := by
        apply sum_le_sum
        intro j hj
        have hj' := (mem_filter.mp hj).2
        have hb : |f j / weightRadius N j i₀ ^ γ| ≤
            L * R ^ u * weightRadius N j i₀ ^ (v - γ) := by
          rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos (hr j) _), Real.rpow_sub (hr j)]
          exact (div_le_div_of_nonneg_right (hf j hj') (Real.rpow_pos_of_pos (hr j) γ).le).trans_eq (by ring)
        have hh := mul_self_le_mul_self (abs_nonneg _) hb
        simp only [← pow_two, sq_abs] at hh
        convert hh using 1
        simp only [mul_pow]
        rw [show (weightRadius N j i₀ ^ (v - γ)) ^ (2 : ℕ) =
          weightRadius N j i₀ ^ (2 * (v - γ)) by
            rw [mul_comm, Real.rpow_mul (hr j).le, Real.rpow_two]]
      _ = (L * R ^ u) ^ 2 * ∑ j ∈ S, weightRadius N j i₀ ^ (2 * (v - γ)) :=
        (mul_sum ..).symm
      _ ≤ (L * R ^ u) ^ 2 * (4 * R ^ (2 * (v - γ) + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact (sum_le_sum_of_subset_of_nonneg
          (fun j hj => mem_filter.mpr ⟨mem_univ _, by
            have := (mem_filter.mp hj).2; linarith⟩)
          (fun j _ _ => Real.rpow_nonneg (hr j).le _)).trans
            (sum_positive_power N i₀ hR he)
      _ = _ := by
        have hp (e : ℝ) : (R ^ e) ^ (2 : ℕ) = R ^ (2 * e) := by
          rw [mul_comm, Real.rpow_mul hRp.le, Real.rpow_two]
        simp only [mul_pow, hp]
        rw [show L ^ 2 * R ^ (2 * u) * (4 * R ^ (2 * (v - γ) + 1)) =
          4 * L ^ 2 * (R ^ (2 * u) * R ^ (2 * (v - γ) + 1)) by ring,
          ← Real.rpow_add hRp]
        rw [show 2 * u + (2 * (v - γ) + 1) =
          2 * (u + v - γ + 1 / 2) by ring]
        ring
  have hb := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (by positivity : 0 ≤ 2 * L * R ^ (u + v - γ + 1 / 2))] at hb
  exact (abs_sum_le_sum_abs ..).trans
    ((FiniteZeroSumBounds.weighted_cauchy_subset S
      (fun j => weightRadius N j i₀ ^ γ) f g (fun j => Real.rpow_pos_of_pos (hr j) γ)).trans
      (mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg _)))

/-- Lemma 5.13, Step 3 (equation (5.49)): the normalized kernel on the
comparable-radius region is bounded by the reciprocal larger radius. -/
theorem comparable_normalized {s x y D C A : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hx : 0 < x) (hy : 0 < y)
    (hxy : x / 2 ≤ y) (hyx : y ≤ 2 * x)
    (hD : 0 < D) (hgeom : |x - y| ≤ D) (hupper : D ≤ x + y)
    (hC : 0 ≤ C) (hA : |A| ≤ C * D ^ (-(2 - s))) :
    |A * (x ^ (3 / 2 - s) - y ^ (3 / 2 - s)) ^ 2 /
      (x ^ (1 - s / 2) * y ^ (1 - s / 2))| ≤ 32 * C / x := by
  have ordered (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
      (hyx : y ≤ x) (hxy : x ≤ 2 * y) (hgeom : |x - y| ≤ D)
      (hupper : D ≤ x + y) :
      |A * (x ^ (3 / 2 - s) - y ^ (3 / 2 - s)) ^ 2 /
        (x ^ (1 - s / 2) * y ^ (1 - s / 2))| ≤ 32 * C / x := by
    let γ := 1 - s / 2
    have hg0 : 0 ≤ γ := by dsimp [γ]; linarith
    have hg1 : γ ≤ 1 := by dsimp [γ]; linarith
    have hraw := comparable_raw hs0 hs1 hy hyx hxy hD hgeom hupper hC hA
    have hpow : x ^ γ ≤ 2 * y ^ γ := by
      calc
        _ ≤ (2 * y) ^ γ := Real.rpow_le_rpow hx.le hxy hg0
        _ = 2 ^ γ * y ^ γ := Real.mul_rpow (by norm_num) hy.le
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (by simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hg1)
          (Real.rpow_nonneg hy.le _)
    have hident : x ^ (1 - s) = x ^ γ * x ^ γ / x := by
      rw [← Real.rpow_add hx, div_eq_mul_inv, ← Real.rpow_neg_one,
        ← Real.rpow_add hx]
      congr 1
      dsimp [γ]
      ring
    rw [abs_div, abs_mul, abs_pow, sq_abs,
      abs_of_pos (mul_pos (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hy _))]
    calc
      _ ≤ 16 * C * y ^ (1 - s) / (x ^ γ * y ^ γ) :=
        div_le_div_of_nonneg_right hraw (by positivity)
      _ ≤ 16 * C * x ^ (1 - s) / (x ^ γ * y ^ γ) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hy.le hyx (by linarith)) (by positivity)
      _ = 16 * C / x * (x ^ γ / y ^ γ) := by
        rw [hident]
        field_simp [(Real.rpow_pos_of_pos hx γ).ne', (Real.rpow_pos_of_pos hy γ).ne']
      _ ≤ 16 * C / x * 2 := mul_le_mul_of_nonneg_left
        ((div_le_iff₀ (Real.rpow_pos_of_pos hy _)).mpr hpow) (by positivity)
      _ = _ := by ring
  rcases le_total y x with h | h
  · exact ordered x y hx hy h (by linarith) hgeom hupper
  · have hh := ordered y x hy hx h hyx (by simpa only [abs_sub_comm] using hgeom)
      (by linarith)
    rw [sub_sq_comm, mul_comm (y ^ (1 - s / 2))] at hh
    exact hh.trans (div_le_div_of_nonneg_left (by positivity) hx h)

/-- Lemma 5.13, Step 3 (equation (5.49)): the quadratic Schur estimate used
only on comparable radii, before treating any separated-radius monomial. -/
theorem quadratic_schur {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (v : ι → ℝ) (B : ℝ)
    (hrow : ∀ i, ∑ j, |K i j| ≤ B) (hcol : ∀ j, ∑ i, |K i j| ≤ B) :
    |∑ i, ∑ j, K i j * v i * v j| ≤ B * ∑ i, v i ^ 2 := by
  calc
    _ ≤ ∑ i, ∑ j, |K i j| * |v i| * |v j| := by
      exact (abs_sum_le_sum_abs ..).trans (sum_le_sum fun i _ => by
        simpa only [abs_mul] using abs_sum_le_sum_abs (fun j => K i j * v i * v j) univ)
    _ ≤ ∑ i, ∑ j, |K i j| * (v i ^ 2 + v j ^ 2) / 2 := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro j _
      have hh : |v i| * |v j| ≤ (v i ^ 2 + v j ^ 2) / 2 := by
        nlinarith [sq_nonneg (|v i| - |v j|), sq_abs (v i), sq_abs (v j)]
      nlinarith only [mul_le_mul_of_nonneg_left hh (abs_nonneg (K i j))]
    _ = ((∑ i, v i ^ 2 * ∑ j, |K i j|) +
        ∑ j, v j ^ 2 * ∑ i, |K i j|) / 2 := by
      simp only [mul_add, add_div, sum_add_distrib, ← sum_div]
      rw [sum_comm (f := fun i j => |K i j| * v j ^ 2)]
      simp only [mul_sum]
      congr 2 <;> apply sum_congr rfl <;> intro i _ <;>
        apply sum_congr rfl <;> intro j _ <;> ring
    _ ≤ ((∑ i, v i ^ 2 * B) + ∑ j, v j ^ 2 * B) / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact add_le_add (sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg _))
        (sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hcol j) (sq_nonneg _))
    _ = _ := by rw [← sum_mul]; ring

end Internal

/-- Lemma 5.13, Step 3 (equation (5.49)): the comparable-radius contribution
has a bound independent of the cycle size, by row and column Schur sums. -/
theorem differential_comparable_region (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (a : ℝ) (ha : 0 < a) (B : ℝ) (i₀ : Fin (N : ℕ)) (g : Fin (N : ℕ) → ℝ),
      let A := factorizationMatrix s N hN a ha B
      let r := fun i => weightRadius N i i₀
      let α := 3 / 2 - s.val
      |∑ i, ∑ j ∈ univ.filter (fun j => r i / 2 ≤ r j ∧ r j ≤ 2 * r i),
        A i j * (r i ^ α - r j ^ α) ^ 2 * g i * g j| ≤
        C * (a + B ^ 2 / a) * ∑ i, (r i ^ (1 - s.val / 2) * g i) ^ 2 := by
  classical
  obtain ⟨C, hC, hb⟩ := factorization_entry_bound hz s
  refine ⟨256 * C, by positivity, ?_⟩
  intro N hN a ha B i₀ g
  dsimp only
  let A := factorizationMatrix s N hN a ha B
  let r := fun i => weightRadius N i i₀
  let α := 3 / 2 - s.val
  let γ := 1 - s.val / 2
  let L := C * (a + B ^ 2 / a)
  let K := fun i j => if r i / 2 ≤ r j ∧ r j ≤ 2 * r i then
    A i j * (r i ^ α - r j ^ α) ^ 2 / (r i ^ γ * r j ^ γ) else 0
  have hr (i) : 0 < r i := by dsimp [r]; linarith [one_le_weightRadius N i i₀]
  have hL : 0 ≤ L := mul_nonneg hC.le (factorization_shift_pos ha B).le
  have hs : ∀ i j, A i j = A j i := by
    have hh := Matrix.isHermitian_iff_isSymm.mp
      (factorizationMatrix_posDef s N hN a ha B).isHermitian
    intro i j
    exact congrFun (congrFun hh j) i
  have hsym : ∀ i j, K i j = K j i := by
    intro i j
    have hc : (r i / 2 ≤ r j ∧ r j ≤ 2 * r i) ↔
        (r j / 2 ≤ r i ∧ r i ≤ 2 * r j) := by constructor <;> rintro ⟨h, h'⟩ <;> constructor <;> linarith
    simp only [K, hc, hs i j, sub_sq_comm, mul_comm (r i ^ γ)]
  have hrow (i) : (∑ j, |K i j|) ≤ 256 * L := by
    have hpoint (j) : |K i j| ≤ if r j ≤ 2 * r i then 32 * L / r i else 0 := by
      dsimp only [K]
      split_ifs with h h' h'
      · have htri : (Riesz1.cyclicIndexDistance N i j : ℝ) ≤
            (Riesz1.cyclicIndexDistance N i i₀ : ℝ) +
              (Riesz1.cyclicIndexDistance N i₀ j : ℝ) := by
          exact_mod_cast cyclicIndexDistance_triangle i i₀ j
        exact Internal.comparable_normalized s.property.1 s.property.2 (hr i) (hr j)
          h.1 h.2 (by positivity)
          ((DerivativeCommutators.weightRadius_lipschitz N i₀ i j).trans (by linarith))
          (by dsimp [r, weightRadius]; rw [cyclicIndexDistance_comm' N j i₀]; linarith)
          hL (hb N hN a ha B i j)
      · exact False.elim (h' h.2)
      · simp only [abs_zero]; exact div_nonneg (by positivity) (hr i).le
      · simp only [abs_zero, le_refl]
    have hcount := Internal.sum_positive_power N i₀
      (R := 2 * r i) (by have := one_le_weightRadius N i i₀; dsimp [r]; linarith)
      (e := 0) le_rfl
    simp only [Real.rpow_zero, zero_add, Real.rpow_one] at hcount
    calc
      _ ≤ ∑ j, if r j ≤ 2 * r i then 32 * L / r i else 0 := sum_le_sum (fun j _ => hpoint j)
      _ = (∑ j ∈ univ.filter (fun j => r j ≤ 2 * r i), (1 : ℝ)) * (32 * L / r i) := by
        rw [sum_filter, sum_mul]; simp only [one_mul, ite_mul, zero_mul]
      _ ≤ (4 * (2 * r i)) * (32 * L / r i) :=
        mul_le_mul_of_nonneg_right hcount (div_nonneg (by positivity) (hr i).le)
      _ = _ := by field_simp [(hr i).ne']; ring
  have hh := Internal.quadratic_schur K (fun i => r i ^ γ * g i) (256 * L) hrow
    (fun j => by simpa only [hsym] using hrow j)
  have heq : (∑ i, ∑ j, K i j * (r i ^ γ * g i) * (r j ^ γ * g j)) =
      ∑ i, ∑ j ∈ univ.filter (fun j => r i / 2 ≤ r j ∧ r j ≤ 2 * r i),
        A i j * (r i ^ α - r j ^ α) ^ 2 * g i * g j := by
    apply sum_congr rfl
    intro i _
    rw [sum_filter]
    apply sum_congr rfl
    intro j _
    dsimp only [K]
    split_ifs
    · field_simp [(Real.rpow_pos_of_pos (hr i) γ).ne', (Real.rpow_pos_of_pos (hr j) γ).ne']
    · ring
  rw [heq] at hh
  convert hh using 1
  dsimp [L]
  ring

end Riesz2.GlobalCommutators
