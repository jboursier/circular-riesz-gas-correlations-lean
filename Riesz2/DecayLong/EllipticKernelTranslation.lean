/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.GlobalReferenceErrorPart2
public import Riesz2.DecayLong.GlobalSums

/-!
# Near and far estimates for translations of the sampled kernel

The column modulus used in the proof of Lemma 5.9 follows the paper:
sum kernel values near the two origins, and telescope first differences
along a shortest arc on the complement.
-/

@[expose] public section
noncomputable section

open Finset
open scoped BigOperators Fin.NatCast

namespace Riesz2.EllipticPrimitive

open GlobalReferenceErrorInternal

/-- Kernel values and backward column differences, with constants uniform in
the cycle size. The value bound uses the triangular formula. The difference
bound is the existing endpoint estimate for interval matrices. -/
theorem sampled_kernel_value_difference (s : Riesz1.RieszExponent) :
    ∃ A D : ℝ, 0 < A ∧ 0 < D ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (i j : Fin (N : ℕ)),
      |sampledRieszKernel s N hN (j - i)| ≤ A * weightRadius N i j ^ (-s.val) ∧
      |sampledRieszKernel s N hN (j - i) -
        sampledRieszKernel s N hN (j - 1 - i)| ≤
        D * weightRadius N i j ^ (-s.val - 1) := by
  obtain ⟨C, hC, hc⟩ := reference_coefficient_bound s
  let A := C * ((1 + 1 / s.val) * 2 ^ s.val)
  let D := 2 * C * (1 + 1 / (s.val + 1)) * 2 ^ (s.val + 1)
  refine ⟨A, D, by dsimp [A]; positivity [s.property.1],
    by dsimp [D]; positivity [s.property.1], fun N hN i j => ?_⟩
  let d := Riesz1.cyclicIndexDistance N i j
  let w := fun r : Fin ((N : ℕ) / 2) =>
    (1 - if 2 * (r.val + 1) = (N : ℕ) then (1 / 2 : ℝ) else 0) *
      sampledSecondDifference s N hN (↑(r.val + 1) : Fin (N : ℕ))
  have hw (r) : |w r| ≤ C * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2) := by
    simpa only [show 1 ≤ r.val + 1 by omega, ↓reduceIte] using hc N hN 1 r
  have hrep (i j : Fin (N : ℕ)) : sampledRieszKernel s N hN (j - i) =
      ∑ k, ∑ r, w r *
        (if i ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
        (if j ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) := by
    rw [← referenceIntervalMatrix_full s N hN, reference_fin_lengths]
    simp only [show ∀ r : Fin ((N : ℕ) / 2), 1 ≤ r.val + 1 by intro r; omega,
      ↓reduceIte, w]
  constructor
  · have hdhalf : d ≤ (N : ℕ) / 2 := by
      have := Riesz1.APG.cyclicIndexDistance_le_half (N := N) i j
      omega
    have hkernel : sampledRieszKernel s N hN (j - i) =
        sampledRieszKernel s N hN (↑d : Fin (N : ℕ)) := by
      have he : d = min (j - i).val ((N : ℕ) - (j - i).val) := distance_eq_min N i j
      rcases le_total (j - i).val ((N : ℕ) - (j - i).val) with h | h
      · rw [he, min_eq_left h, Fin.cast_val_eq_self]
      · rw [he, min_eq_right h]
        by_cases hz : j - i = 0
        · simp only [hz, Fin.val_zero, Nat.sub_zero] at h ⊢
          omega
        · have hn : (-(j - i)).val = (N : ℕ) - (j - i).val := by
            rw [Fin.val_neg, ite_eq_right hz]
          rw [← hn, Fin.cast_val_eq_self, sampledRieszKernel_even]
    have hterm (r : ℕ) (hr : r ∈ Icc (d + 1) ((N : ℕ) / 2)) :
        ((r : ℝ) - d) * (1 - if 2 * r = (N : ℕ) then (1 / 2 : ℝ) else 0) *
          sampledSecondDifference s N hN (↑r : Fin (N : ℕ)) ≤
            C * (r : ℝ) ^ (-(s.val + 1)) := by
      have hr' := mem_Icc.mp hr
      let q : Fin ((N : ℕ) / 2) := ⟨r - 1, by omega⟩
      have hq : q.val + 1 = r := by dsimp [q]; omega
      have hb := hw q
      dsimp only [w] at hb
      rw [hq] at hb
      have hdR : (0 : ℝ) ≤ r - d := by
        apply sub_nonneg.mpr
        exact_mod_cast (show d ≤ r by omega)
      have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
      calc
        _ ≤ ((r : ℝ) - d) * (C * (r : ℝ) ^ (-s.val - 2)) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans hb) hdR
        _ ≤ (r : ℝ) * (C * (r : ℝ) ^ (-s.val - 2)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
          linarith
        _ = _ := by
          rw [mul_left_comm]
          congr 1
          calc
            (r : ℝ) * (r : ℝ) ^ (-s.val - 2) =
                (r : ℝ) ^ (1 : ℝ) * (r : ℝ) ^ (-s.val - 2) := by rw [Real.rpow_one]
            _ = _ := by rw [← Real.rpow_add hr0]; congr 1; ring
    rw [abs_of_nonneg (sampledRieszKernel_nonneg s N hN _), hkernel,
      sampledRieszKernel_interval_formula s N hN d hdhalf]
    calc
      _ ≤ ∑ r ∈ Icc (d + 1) ((N : ℕ) / 2), C * (r : ℝ) ^ (-(s.val + 1)) :=
        sum_le_sum hterm
      _ ≤ C * ∑ r : Fin ((N : ℕ) / 2),
          if d ≤ r.val + 1 then ((r.val + 1 : ℕ) : ℝ) ^ (-(s.val + 1)) else 0 := by
        rw [mul_sum, Fin.sum_univ_eq_sum_range (fun r : ℕ => C *
          (if d ≤ r + 1 then ((r + 1 : ℕ) : ℝ) ^ (-(s.val + 1)) else 0))]
        rw [← Nat.Ico_zero_eq_range, sum_Ico_add'
          (fun r : ℕ => C * (if d ≤ r then (r : ℝ) ^ (-(s.val + 1)) else 0)) 0
          ((N : ℕ) / 2) 1]
        calc
          _ = ∑ r ∈ Icc (d + 1) ((N : ℕ) / 2), C *
              (if d ≤ r then (r : ℝ) ^ (-(s.val + 1)) else 0) := by
            apply sum_congr rfl
            intro r hr
            rw [ite_eq_left (by have := mem_Icc.mp hr; omega)]
          _ ≤ _ := by
            apply sum_le_sum_of_subset_of_nonneg
            · intro r hr
              simp only [mem_Icc, mem_Ico] at hr ⊢
              omega
            · intro r _ _
              split_ifs <;> positivity
      _ ≤ _ := by
        have ht := length_tail_le (t := s.val + 1) (by linarith [s.property.1])
          ((N : ℕ) / 2) d
        have hh := mul_le_mul_of_nonneg_left ht hC.le
        simpa only [add_sub_cancel_right, show 1 - (s.val + 1) = -s.val by ring,
          A, weightRadius, d, mul_assoc] using hh
  · have hb := interval_first_difference_bound N hN (t := s.val + 2)
      (by linarith [s.property.1]) hC.le (fun _ r => w r)
      (fun _ r => by simpa only [show -(s.val + 2) = -s.val - 2 by ring] using hw r) j i
    simp_rw [← hrep] at hb
    have he (x y : Fin (N : ℕ)) :
        sampledRieszKernel s N hN (x - y) = sampledRieszKernel s N hN (y - x) := by
      rw [← sampledRieszKernel_even s N hN (y - x), neg_sub]
    rw [he i j, he i (j - 1), cyclicIndexDistance_comm'] at hb
    simpa only [D, weightRadius, show s.val + 2 - 1 = s.val + 1 by ring,
      show 1 - (s.val + 2) = -s.val - 1 by ring] using hb

/-- Internal near/far estimate along an arc of length at most half a cycle.
The kernel hypotheses are supplied by `sampled_kernel_value_difference`. -/
theorem kernel_translation_arc_internal (s : Riesz1.RieszExponent)
    (N : ℕ+) (G : Fin (N : ℕ) → Fin (N : ℕ) → ℝ)
    {A D : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hval : ∀ i j, |G i j| ≤ A * weightRadius N i j ^ (-s.val))
    (hdiff : ∀ i j, |G i j - G i (j - 1)| ≤
      D * weightRadius N i j ^ (-s.val - 1))
    (a : Fin (N : ℕ)) (R : ℕ) (hR : 1 ≤ R) (hhalf : 2 * R ≤ (N : ℕ)) :
    (∑ i, |G i (a + (R : Fin (N : ℕ))) - G i a|) ≤
      (4 * A / (1 - s.val) * 4 ^ (1 - s.val) +
        2 * D * 2 ^ (s.val + 1) * (1 + 1 / s.val)) * (R : ℝ) ^ (1 - s.val) := by
  classical
  let b := a + (R : Fin (N : ℕ))
  let near := fun i => Riesz1.cyclicIndexDistance N i a ≤ 2 * R ∨
    Riesz1.cyclicIndexDistance N i b ≤ 2 * R
  let U : ℝ := 1 + 3 * R
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hU : 1 ≤ U := by dsimp [U]; linarith
  have hab : Riesz1.cyclicIndexDistance N a b = R := distance_add_length N a hhalf
  have hba : Riesz1.cyclicIndexDistance N b a = R := by
    rw [cyclicIndexDistance_comm', hab]
  have hnear_radius (i) (hi : near i) :
      weightRadius N i a ≤ U ∧ weightRadius N i b ≤ U := by
    have hia := cyclicIndexDistance_triangle i b a
    have hib := cyclicIndexDistance_triangle i a b
    rw [hba] at hia
    rw [hab] at hib
    have hna : Riesz1.cyclicIndexDistance N i a ≤ 3 * R := by rcases hi with hi | hi <;> omega
    have hnb : Riesz1.cyclicIndexDistance N i b ≤ 3 * R := by rcases hi with hi | hi <;> omega
    constructor <;> dsimp [weightRadius, U] <;> exact_mod_cast (by omega : _)
  have hnear_sum (j : Fin (N : ℕ))
      (hj : ∀ i, near i → weightRadius N i j ≤ U) :
      (∑ i ∈ univ.filter near, weightRadius N i j ^ (-s.val)) ≤
        2 / (1 - s.val) * U ^ (1 - s.val) := by
    refine le_trans ?_ (sum_weightRadius_le_of_lt_one N j s.property.1 s.property.2 hU)
    apply sum_le_sum_of_subset_of_nonneg
    · intro i hi
      exact mem_filter.mpr ⟨mem_univ _, hj i (mem_filter.mp hi).2⟩
    · intro i _ _
      exact Real.rpow_nonneg (by have := one_le_weightRadius N i j; linarith) _
  have hnear : (∑ i ∈ univ.filter near, |G i b - G i a|) ≤
      4 * A / (1 - s.val) * 4 ^ (1 - s.val) * (R : ℝ) ^ (1 - s.val) := by
    have hsum := add_le_add (hnear_sum b (fun i hi => (hnear_radius i hi).2))
      (hnear_sum a (fun i hi => (hnear_radius i hi).1))
    have hpow : U ^ (1 - s.val) ≤ 4 ^ (1 - s.val) * (R : ℝ) ^ (1 - s.val) := by
      calc
        _ ≤ (4 * (R : ℝ)) ^ (1 - s.val) :=
          Real.rpow_le_rpow (by dsimp [U]; positivity)
            (by dsimp [U]; linarith)
            (by linarith [s.property.2])
        _ = _ := Real.mul_rpow (by norm_num) hR0.le
    calc
      _ ≤ ∑ i ∈ univ.filter near, (A * weightRadius N i b ^ (-s.val) +
          A * weightRadius N i a ^ (-s.val)) :=
        sum_le_sum fun i _ => (abs_sub _ _).trans (add_le_add (hval i b) (hval i a))
      _ = A * ((∑ i ∈ univ.filter near, weightRadius N i b ^ (-s.val)) +
          ∑ i ∈ univ.filter near, weightRadius N i a ^ (-s.val)) := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum, mul_add]
      _ ≤ A * (2 / (1 - s.val) * U ^ (1 - s.val) +
          2 / (1 - s.val) * U ^ (1 - s.val)) := mul_le_mul_of_nonneg_left hsum hA
      _ = (4 * A / (1 - s.val)) * U ^ (1 - s.val) := by ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hpow
          (show 0 ≤ 4 * A / (1 - s.val) by positivity [sub_pos.mpr s.property.2])
        simpa only [mul_assoc] using hh
  have hfar_point (i) (hi : ¬near i) : |G i b - G i a| ≤
      (R : ℝ) * (D * 2 ^ (s.val + 1) * weightRadius N i a ^ (-s.val - 1)) := by
    have hia : 2 * R < Riesz1.cyclicIndexDistance N i a := by
      dsimp [near] at hi
      omega
    have hstep (t : ℕ) (ht : t < R) :
        |G i (a + (t : Fin (N : ℕ)) + 1) - G i (a + (t : Fin (N : ℕ)))| ≤
          D * 2 ^ (s.val + 1) * weightRadius N i a ^ (-s.val - 1) := by
      let c := a + ((t + 1 : ℕ) : Fin (N : ℕ))
      have hac : Riesz1.cyclicIndexDistance N a c = t + 1 :=
        distance_add_length N a (by omega)
      have htri := cyclicIndexDistance_triangle i c a
      rw [cyclicIndexDistance_comm' N c a, hac] at htri
      have hradius : weightRadius N i a / 2 ≤ weightRadius N i c := by
        have htriR : (Riesz1.cyclicIndexDistance N i a : ℝ) ≤
            (Riesz1.cyclicIndexDistance N i c : ℝ) + (t + 1 : ℕ) := by exact_mod_cast htri
        have hiaR : 2 * (R : ℝ) < Riesz1.cyclicIndexDistance N i a := by exact_mod_cast hia
        have htR : ((t + 1 : ℕ) : ℝ) ≤ R := by exact_mod_cast (show t + 1 ≤ R by omega)
        dsimp [weightRadius]
        linarith
      have hpow : weightRadius N i c ^ (-s.val - 1) ≤
          2 ^ (s.val + 1) * weightRadius N i a ^ (-s.val - 1) := by
        calc
          _ ≤ (weightRadius N i a / 2) ^ (-s.val - 1) :=
            Real.rpow_le_rpow_of_nonpos (by have := one_le_weightRadius N i a; positivity)
              hradius (by linarith [s.property.1])
          _ = _ := by
            rw [Real.div_rpow (by have := one_le_weightRadius N i a; positivity) (by norm_num),
              show -s.val - 1 = -(s.val + 1) by ring,
              Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
      have he : c - 1 = a + (t : Fin (N : ℕ)) := by dsimp [c]; push_cast; abel
      have hh := (hdiff i c).trans (mul_le_mul_of_nonneg_left hpow hD)
      rw [he] at hh
      simpa only [c, Nat.cast_add, Nat.cast_one, ← add_assoc, mul_assoc] using hh
    have htel (k : ℕ) (hk : k ≤ R) :
        |G i (a + (k : Fin (N : ℕ))) - G i a| ≤
          (k : ℝ) * (D * 2 ^ (s.val + 1) * weightRadius N i a ^ (-s.val - 1)) := by
      induction k with
      | zero => simp
      | succ k ih =>
        have hh := (abs_sub_le (G i (a + (k : Fin (N : ℕ)) + 1))
          (G i (a + (k : Fin (N : ℕ)))) (G i a)).trans
            (add_le_add (hstep k (by omega)) (ih (by omega)))
        simpa only [Nat.cast_add, Nat.cast_one, ← add_assoc, add_mul, one_mul,
          add_comm] using hh
    exact htel R le_rfl
  have hfar : (∑ i ∈ univ.filter (fun i => ¬near i), |G i b - G i a|) ≤
      2 * D * 2 ^ (s.val + 1) * (1 + 1 / s.val) * (R : ℝ) ^ (1 - s.val) := by
    have htail : (∑ i ∈ univ.filter (fun i => ¬near i),
        weightRadius N i a ^ (-s.val - 1)) ≤
          2 * (1 + 1 / s.val) * (R : ℝ) ^ (-s.val) := by
      have hh := sum_weightRadius_tail_le N a (t := s.val + 1) (R := R)
        (by linarith [s.property.1]) (by exact_mod_cast hR)
      refine le_trans ?_ (by simpa only [add_sub_cancel_right,
        show -(s.val + 1) = -s.val - 1 by ring,
        show 1 - (s.val + 1) = -s.val by ring] using hh)
      apply sum_le_sum_of_subset_of_nonneg
      · intro i hi
        have hi' := (mem_filter.mp hi).2
        have hd : R ≤ Riesz1.cyclicIndexDistance N i a := by dsimp [near] at hi'; omega
        apply mem_filter.mpr ⟨mem_univ _, ?_⟩
        dsimp [weightRadius]
        have : (R : ℝ) ≤ Riesz1.cyclicIndexDistance N i a := by exact_mod_cast hd
        linarith
      · intro i _ _
        exact Real.rpow_nonneg (by have := one_le_weightRadius N i a; linarith) _
    have hpower : (R : ℝ) * (R : ℝ) ^ (-s.val) = (R : ℝ) ^ (1 - s.val) := by
      calc
        _ = (R : ℝ) ^ (1 : ℝ) * (R : ℝ) ^ (-s.val) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hR0]; congr 1
    calc
      _ ≤ ∑ i ∈ univ.filter (fun i => ¬near i), (R : ℝ) *
          (D * 2 ^ (s.val + 1) * weightRadius N i a ^ (-s.val - 1)) :=
        sum_le_sum fun i hi => hfar_point i (mem_filter.mp hi).2
      _ = ((R : ℝ) * (D * 2 ^ (s.val + 1))) *
          ∑ i ∈ univ.filter (fun i => ¬near i), weightRadius N i a ^ (-s.val - 1) := by
        simp_rw [← mul_assoc]
        rw [← mul_sum]
      _ ≤ ((R : ℝ) * (D * 2 ^ (s.val + 1))) *
          (2 * (1 + 1 / s.val) * (R : ℝ) ^ (-s.val)) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ = (2 * D * 2 ^ (s.val + 1) * (1 + 1 / s.val)) *
          ((R : ℝ) * (R : ℝ) ^ (-s.val)) := by ring
      _ = _ := by rw [hpower]
  change (∑ i, |G i b - G i a|) ≤ _
  rw [← sum_filter_add_sum_filter_not univ near]
  exact (add_le_add hnear hfar).trans_eq (by ring)

end Riesz2.EllipticPrimitive
