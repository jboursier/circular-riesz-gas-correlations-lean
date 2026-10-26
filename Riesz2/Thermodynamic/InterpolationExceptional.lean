/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.InterpolationCoefficientsPart2
public import Riesz2.Thermodynamic.InterpolationCoercivity
public import Riesz2.ToMathlib.CyclicIntervalHessianBounds

/-!
# Whole-simplex interaction estimates

The exceptional interaction-entry bound in Subsection 6.1 uses exterior rank control and
cyclic containment counting. The estimates are independent of the ambient periods.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff Topology

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.InterpolationExceptional

/-- Internal geometry for Subsection 6.1: an interval meeting the
active block contains an exterior prefix or suffix of at least half its
exterior rank. This is a lower-length counterpart to the cover. -/
theorem exterior_piece_internal (N : ℕ+) (n : ℕ) (hn : n < (N : ℕ))
    (i : Fin (N : ℕ)) (r : ℕ) (hr : r ≤ (N : ℕ))
    (hmeet : ∃ j ∈ cyclicIndexInterval N i r, j.val < n) :
    ∃ p : ℕ, p ≤ (N : ℕ) - n ∧ r ≤ n + 2 * p ∧
      ((Finset.univ.filter (fun j : Fin (N : ℕ) => n ≤ j.val ∧ j.val < n + p)) ⊆
        cyclicIndexInterval N i r ∨
       (Finset.univ.filter (fun j : Fin (N : ℕ) => (N : ℕ) - p ≤ j.val)) ⊆
        cyclicIndexInterval N i r) := by
  have hi := i.isLt
  have member (j : Fin (N : ℕ)) :
      j ∈ cyclicIndexInterval N i r ↔
        (if i.val ≤ j.val then j.val - i.val else j.val + (N : ℕ) - i.val) < r := by
    rw [mem_cyclicIndexInterval_iff N i j hr, Fin.val_sub]
    by_cases hij : i.val ≤ j.val
    · rw [ite_eq_left hij, show (N : ℕ) - i.val + j.val = (j.val - i.val) + (N : ℕ) by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by have := j.isLt; omega)]
    · rw [ite_eq_right hij, Nat.mod_eq_of_lt (by have := j.isLt; omega)]
      omega
  by_cases hw : (N : ℕ) < i.val + r
  · let p := i.val + r - (N : ℕ) - n
    let q := (N : ℕ) - max n i.val
    have hp : p ≤ (N : ℕ) - n := by dsimp [p]; omega
    have hq : q ≤ (N : ℕ) - n := by dsimp [q]; omega
    have hpq : r ≤ n + p + q := by dsimp [p, q]; omega
    by_cases hqp : q ≤ p
    · refine ⟨p, hp, by omega, Or.inl ?_⟩
      intro j hj
      have hj' := (Finset.mem_filter.mp hj).2
      have hjN := j.isLt
      rw [member]
      dsimp [p] at hj'
      split_ifs <;> omega
    · refine ⟨q, hq, by omega, Or.inr ?_⟩
      intro j hj
      have hj' := (Finset.mem_filter.mp hj).2
      have hjN := j.isLt
      rw [member]
      dsimp [q] at hj'
      split_ifs <;> omega
  · obtain ⟨j, hj, hjn⟩ := hmeet
    rw [member] at hj
    have hjN := j.isLt
    have hin : i.val < n := by split_ifs at hj <;> omega
    refine ⟨i.val + r - n, by omega, by omega, Or.inl ?_⟩
    intro k hk
    have hk' := (Finset.mem_filter.mp hk).2
    rw [member, ite_eq_left (by omega : i.val ≤ k.val)]
    omega

/-- Internal rank split for Subsection 6.1. A deviation-controlled
piece starting at an exterior endpoint has half its rank beyond the explicit threshold. -/
theorem exterior_rank_lower_internal {A γ Y : ℝ} (hA : 0 < A) (hγ : γ < 1)
    {p : ℕ} (hY0 : 0 ≤ Y)
    (hY : |Y - (p : ℝ)| ≤ 4 * A * (p : ℝ) ^ γ) :
    (p : ℝ) / 2 - (16 * A) ^ (1 / (1 - γ)) ≤ Y := by
  by_cases hp : (16 * A) ^ (1 / (1 - γ)) ≤ (p : ℝ)
  · have hh := (InterpolantLocalLaws.internal_large_rank_geometry hA hγ hp hY).2
    have hT : 0 < (16 * A) ^ (1 / (1 - γ)) := by positivity
    linarith
  · linarith [Real.rpow_pos_of_pos (by positivity : 0 < 16 * A) (1 / (1 - γ))]

/-- Internal lower-length estimate for Subsection 6.1: one exterior prefix or suffix
suffices. Its size is independent of the total period. -/
theorem interval_rank_lower_internal (N : ℕ+) (n : ℕ) (hn : n < (N : ℕ))
    (x : Fin (N : ℕ) → ℝ) (hx : ∀ j, 0 ≤ x j) (T : ℝ)
    (hR : ∀ p : ℕ, p ≤ (N : ℕ) - n →
      (p : ℝ) / 2 - T ≤
        ∑ j ∈ Finset.univ.filter (fun j : Fin (N : ℕ) => n ≤ j.val ∧ j.val < n + p), x j)
    (hL : ∀ p : ℕ, p ≤ (N : ℕ) - n →
      (p : ℝ) / 2 - T ≤
        ∑ j ∈ Finset.univ.filter (fun j : Fin (N : ℕ) => (N : ℕ) - p ≤ j.val), x j)
    (i : Fin (N : ℕ)) (r : ℕ) (hr : r ≤ (N : ℕ))
    (hmeet : ∃ j ∈ cyclicIndexInterval N i r, j.val < n) :
    ((r : ℝ) - n) / 4 - T ≤ cyclicGapSum N i r x := by
  obtain ⟨p, hp, hpr, hsub | hsub⟩ := exterior_piece_internal N n hn i r hr hmeet
  all_goals
    have hpr' : (r : ℝ) ≤ (n : ℝ) + 2 * p := by exact_mod_cast hpr
    rw [← sum_cyclicIndexInterval_eq_cyclicGapSum N i hr]
  · have hh := (hR p hp).trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hx j))
    linarith
  · have hh := (hL p hp).trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hx j))
    linarith

/-- See Subsection 6.1 of the paper: whole-simplex lower interval lengths from the
literal exterior geometry. The cutoff is polynomial in the active size. -/
theorem physical_interval_rank_lower (s ε : ℝ) (hγ : min s 1 / 2 + ε < 1)
    (e a : ℕ) (he : 0 < e) (y : AffineSimplex.chartDomain e ((e + a : ℕ) + 1))
    (hgeom : InterpolantLocalLaws.exteriorGeometry s ε e a y.val)
    (u : EuclideanSpace ℝ (Fin (a + 1)))
    (hu : u ∈ AffineSimplex.massSimplex a (((e + a : ℕ) + 1 : ℝ) - ∑ k, y.val k))
    (i : Fin (e + a + 1)) (r : ℕ) (hr : r ≤ e + a + 1)
    (hmeet : ∃ j ∈ cyclicIndexInterval (e + a).succPNat i r, j.val < a + 1) :
    ((r : ℝ) - (a + 1)) / 4 -
        (16 * (a + 1 : ℝ) ^ ε) ^ (1 / (1 - (min s 1 / 2 + ε))) ≤
      cyclicGapSum (e + a).succPNat i r
        (WithLp.ofLp (RetainedSimplex.assemble e a
          (InterpolatingDensities.exteriorPermutation e a) y.val u)) := by
  let N := (e + a).succPNat
  let x := WithLp.ofLp (RetainedSimplex.assemble e a
    (InterpolatingDensities.exteriorPermutation e a) y.val u)
  have hx := InterpolatingDensities.assemble_exterior_mem e a y u hu
  have hh := interval_rank_lower_internal N (a + 1) (by dsimp [N]; omega) x
    (fun j => (hx.1 j).le)
    ((16 * (a + 1 : ℝ) ^ ε) ^ (1 / (1 - (min s 1 / 2 + ε)))) ?_ ?_ i r hr hmeet
  · simpa only [Nat.cast_add, Nat.cast_one] using hh
  all_goals
    intro p hp
    have hpe : p ≤ e := by dsimp only [N, Nat.succPNat_coe] at hp; omega
    dsimp only [N, x, Nat.succPNat_coe]
  · rw [(InterpolationCoefficients.assembled_exterior_filters e a p hpe y.val u).1]
    apply exterior_rank_lower_internal (by positivity) hγ
      (Finset.sum_nonneg fun k _ => (y.property.1 k).le)
    by_cases hp0 : p = 0
    · subst p; simp only [not_lt_zero, Finset.filter_false, Finset.sum_empty, Nat.cast_zero, sub_self, abs_zero]; positivity
    · simpa only [Nat.cast_add, Nat.cast_one] using (hgeom.2 p (by omega) hpe).1
  · rw [(InterpolationCoefficients.assembled_exterior_filters e a p hpe y.val u).2]
    apply exterior_rank_lower_internal (by positivity) hγ
      (Finset.sum_nonneg fun k _ => (y.property.1 k).le)
    by_cases hp0 : p = 0
    · subst p
      have hh : (Finset.univ.filter (fun k : Fin e => e - 0 ≤ k.val)) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro k _
        exact Nat.not_le.mpr k.isLt
      simp only [hh, Finset.sum_empty, Nat.cast_zero, sub_self, abs_zero]
      positivity
    · simpa only [Nat.cast_add, Nat.cast_one] using (hgeom.2 p (by omega) hpe).2

/-- Internal near/far split of Subsection 6.1. The selected active
gap controls short ranks. Exterior prefix and suffix mass controls long ranks. -/
theorem near_far_length_internal {n T r ℓ d : ℝ} (hn : 0 ≤ n) (hT : 0 ≤ T)
    (hr : 0 < r) (hd : 0 < d) (hdℓ : d ≤ ℓ)
    (hfar : (r - n) / 4 - T ≤ ℓ) :
    r * min d 1 / (8 * (n + T + 1)) ≤ ℓ := by
  have hD : 0 < 8 * (n + T + 1) := by positivity
  rw [div_le_iff₀ hD]
  by_cases hnear : r ≤ 8 * (n + T + 1)
  · have hh := mul_le_mul_of_nonneg_right hnear (lt_min hd zero_lt_one).le
    nlinarith [mul_le_mul_of_nonneg_left ((min_le_left d 1).trans hdℓ) hD.le]
  · have hh := mul_le_mul_of_nonneg_left (min_le_right d 1) hr.le
    have hℓ : r / 8 ≤ ℓ := by linarith
    have h8 : (8 : ℝ) ≤ 8 * (n + T + 1) := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h8 (by linarith : 0 ≤ ℓ)]

/-- Internal image estimate of Subsection 6.1: the rank profile
retains the included active gap and is therefore summable after counting. -/
theorem coefficient_profile_internal (p : Parameters) (N : ℕ+)
    (L : {L : ℝ // 0 < L ∧ L < (N : ℝ)}) {r D d : ℝ}
    (hr : 0 < r) (hD : 8 ≤ D) (hd : 0 < d)
    (hL : r * min d 1 / D ≤ L.val) (hrN : r ≤ N)
    (hc : (N : ℝ) / 8 ≤ (N : ℝ) - L.val) :
    PhysicalEnergy.intervalCoefficient p N L ≤
      (p.val.2 * (p.val.2 + 1) *
        PeriodicPower.bound (p.val.2 + 2) (by linarith [p.property.2.1])) *
      D ^ (p.val.2 + 2) * (1 + d ^ (-p.val.2 - 2)) * r ^ (-p.val.2 - 2) := by
  have hD0 : 0 < D := by linarith
  have hm : 0 < min d 1 := lt_min hd zero_lt_one
  have hcomp : r * min d 1 / D ≤ (N : ℝ) - L.val := by
    have ha : r * min d 1 / D ≤ r / 8 := by
      apply (div_le_div_iff₀ hD0 (by norm_num : (0 : ℝ) < 8)).mpr
      nlinarith [mul_le_mul_of_nonneg_left (min_le_right d 1) hr.le]
    exact ha.trans ((div_le_div_of_nonneg_right hrN (by norm_num)).trans hc)
  have hh := PhysicalEnergy.intervalCoefficient_upper p N L (by positivity) hL hcomp
  have hp : (min d 1) ^ (-p.val.2 - 2) ≤ 1 + d ^ (-p.val.2 - 2) := by
    by_cases hd1 : d ≤ 1
    · rw [min_eq_left hd1]; linarith
    · rw [min_eq_right (le_of_not_ge hd1), Real.one_rpow]
      exact le_add_of_nonneg_right (Real.rpow_nonneg hd.le _)
  have he : (r * min d 1 / D) ^ (-p.val.2 - 2) =
      D ^ (p.val.2 + 2) * (min d 1) ^ (-p.val.2 - 2) * r ^ (-p.val.2 - 2) := by
    rw [Real.div_rpow (by positivity) hD0.le, Real.mul_rpow hr.le hm.le,
      div_eq_mul_inv, ← Real.rpow_neg hD0.le]
    rw [show -(-p.val.2 - 2) = p.val.2 + 2 by ring]
    ring
  rw [he] at hh
  have hB : 0 ≤ p.val.2 * (p.val.2 + 1) *
      PeriodicPower.bound (p.val.2 + 2) (by linarith [p.property.2.1]) :=
    mul_nonneg (mul_nonneg p.property.2.1.le (by linarith [p.property.2.1]))
      (PeriodicPower.bound_pos (p.val.2 + 2) (by linarith [p.property.2.1])).le
  have hm := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (mul_nonneg hB (Real.rpow_nonneg hD0.le (p.val.2 + 2)))
      (Real.rpow_nonneg hr.le (-p.val.2 - 2)))
  apply hh.trans
  convert hm using 1 <;> ring

/-- Internal counting step for Subsection 6.1. A summable rank
profile for intervals containing the selected row gives a period-uniform
bound for the entire entry, rather than just one interval coefficient. -/
theorem interval_entry_bound_internal (N : ℕ+) {s B : ℝ} (hs : 0 < s) (hB : 0 ≤ B)
    (F : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → ℝ) (a b : Fin (N : ℕ))
    (hF : ∀ i r, a ∈ cyclicIndexInterval N i (r.val + 1) →
      0 ≤ F i r ∧ F i r ≤ B * (r.val + 1 : ℝ) ^ (-s - 2)) :
    |∑ i, ∑ r, if a ∈ cyclicIndexInterval N i (r.val + 1) ∧
        b ∈ cyclicIndexInterval N i (r.val + 1) then F i r else 0| ≤
      B * (1 + 1 / s) := by
  classical
  have hterm (i : Fin (N : ℕ)) (r : Fin ((N : ℕ) / 2)) :
      0 ≤ if a ∈ cyclicIndexInterval N i (r.val + 1) ∧
        b ∈ cyclicIndexInterval N i (r.val + 1) then F i r else 0 := by
    split_ifs with h
    · exact (hF i r h.1).1
    · exact le_rfl
  rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun r _ => hterm i r),
    Finset.sum_comm]
  calc
    _ ≤ ∑ r : Fin ((N : ℕ) / 2), ∑ i : Fin (N : ℕ),
        ((if a ∈ cyclicIndexInterval N i (r.val + 1) then 1 else 0) *
          (if b ∈ cyclicIndexInterval N i (r.val + 1) then 1 else 0)) *
        (B * (r.val + 1 : ℝ) ^ (-s - 2)) := by
      apply Finset.sum_le_sum
      intro r _
      apply Finset.sum_le_sum
      intro i _
      by_cases ha : a ∈ cyclicIndexInterval N i (r.val + 1) <;>
        by_cases hb : b ∈ cyclicIndexInterval N i (r.val + 1)
      · simpa only [ha, hb, and_self, ↓reduceIte, one_mul] using (hF i r ha).2
      all_goals simp only [ha, hb, ↓reduceIte, false_and, and_false, zero_mul, mul_zero, le_refl]
    _ = B * ∑ r : Fin ((N : ℕ) / 2),
        ((r.val + 1 - Riesz1.cyclicIndexDistance N a b : ℕ) : ℝ) *
          (r.val + 1 : ℝ) ^ (-s - 2) := by
      have hp (r : Fin ((N : ℕ) / 2)) := cyclicIndexInterval_pair_count N
        (r := r.val + 1) (by have := r.isLt; omega) a b
      simp_rw [← Finset.sum_mul, hp]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ ≤ B * ((1 + 1 / s) * (1 + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-s)) :=
      mul_le_mul_of_nonneg_left (interval_pair_weight_le hs _ _) hB
    _ ≤ _ := by
      have hp := Real.rpow_le_one_of_one_le_of_nonpos
        (show (1 : ℝ) ≤ 1 + (Riesz1.cyclicIndexDistance N a b : ℝ) by
          have := Nat.cast_nonneg (Riesz1.cyclicIndexDistance N a b) (α := ℝ)
          linarith)
        (by linarith : -s ≤ 0)
      have hc : 0 ≤ B * (1 + 1 / s) := by positivity
      simpa only [mul_assoc, mul_one] using mul_le_mul_of_nonneg_left hp hc

/-- See Subsection 6.1 of the paper: physical coefficients on the whole simplex
have a summable rank envelope depending on one included active gap. -/
theorem physical_coefficient_profile (s ε : ℝ) (hs : 0 < s)
    (hε : 0 ≤ ε) (hσε : min s 1 / 2 + 2 * ε < 1) :
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ p : Parameters, p.val.2 = s → ∀ (e a : ℕ), n₀ ≤ a + 1 →
      4 * (a + 1) ≤ e + a + 1 →
      ∀ y : AffineSimplex.chartDomain e ((e + a : ℕ) + 1),
      InterpolantLocalLaws.exteriorGeometry s ε e a y.val →
      ∀ u : EuclideanSpace ℝ (Fin (a + 1)),
      u ∈ AffineSimplex.massSimplex a (((e + a : ℕ) + 1 : ℝ) - ∑ k, y.val k) →
      ∀ (i : Fin (e + a + 1)) (r : ℕ), 0 < r → 2 * r ≤ e + a + 1 →
      ∀ j : Fin (a + 1),
      j.castLE (show a + 1 ≤ e + a + 1 by omega) ∈ cyclicIndexInterval (e + a).succPNat i r →
      let N := (e + a).succPNat
      let x := WithLp.ofLp (RetainedSimplex.assemble e a
        (InterpolatingDensities.exteriorPermutation e a) y.val u)
      let T := (16 * (a + 1 : ℝ) ^ ε) ^ (1 / (1 - (min s 1 / 2 + ε)))
      let B := s * (s + 1) *
        PeriodicPower.bound (s + 2) (by linarith)
      ∃ hℓ : 0 < cyclicGapSum N i r x ∧ cyclicGapSum N i r x < (N : ℝ),
        PhysicalEnergy.intervalCoefficient p N ⟨cyclicGapSum N i r x, hℓ⟩ ≤
          B * (8 * ((a + 1 : ℝ) + T + 1)) ^ (s + 2) *
            (1 + (u j) ^ (-s - 2)) * (r : ℝ) ^ (-s - 2) := by
  obtain ⟨n₀, hn₀, hb⟩ := InterpolationCoefficients.physical_crossing_complement_lower
    s ε hs.le hε hσε
  refine ⟨n₀, hn₀, ?_⟩
  intro p hp e a hnn hsize y hgeom u hu i r hr hrN j hj N x T B
  have hx := InterpolatingDensities.assemble_exterior_mem e a y u hu
  have hxs : x ∈ Riesz1.gapSimplex N := ⟨hx.1, by
    simpa only [N, Nat.succPNat_coe, Nat.cast_succ] using hx.2⟩
  have hℓ := PhysicalEnergy.gapSum_mem N i hr (by dsimp [N]; omega) x hxs
  have hmeet : ∃ k ∈ cyclicIndexInterval N i r, k.val < a + 1 :=
    ⟨j.castLE (show a + 1 ≤ e + a + 1 by omega), hj, j.isLt⟩
  have hc := hb e a hnn hsize y hgeom u hu i r hrN hmeet
  have hfar := physical_interval_rank_lower s ε (by linarith) e a (by omega)
    y hgeom u hu i r (by omega) hmeet
  have hs := (Finset.single_le_sum (s := cyclicIndexInterval N i r) (f := x)
    (fun k _ => (hxs.1 k).le) hj).trans_eq
    (sum_cyclicIndexInterval_eq_cyclicGapSum N i (r := r) (by dsimp [N]; omega) x)
  have hdℓ : u j ≤ cyclicGapSum N i r x := by
    rw [show x (j.castLE (show a + 1 ≤ e + a + 1 by omega)) = u j from
      InterpolatingDensities.assemble_exterior_active e a y.val u j (by omega)] at hs
    exact hs
  have hlo := near_far_length_internal (by positivity : 0 ≤ (a + 1 : ℝ))
    (by dsimp [T]; positivity : 0 ≤ T) (by exact_mod_cast hr) (hu.1 j) hdℓ hfar
  have hcomp : (N : ℝ) / 8 ≤ (N : ℝ) - cyclicGapSum N i r x := by
    simpa only [N, Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using hc
  refine ⟨hℓ, ?_⟩
  have hh := coefficient_profile_internal p N ⟨_, hℓ⟩ (by exact_mod_cast hr)
    (by
      have hT : 0 ≤ T := by dsimp [T]; positivity
      have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      linarith) (hu.1 j) hlo (by exact_mod_cast (show r ≤ e + a + 1 by omega)) hcomp
  simpa only [hp] using hh

/-- See Subsection 6.1 of the paper: the exterior rank cutoff is bounded by a power
of the active size, with constants preceding the size and both periods. -/
theorem cutoff_polynomial_internal {n ε γ s : ℝ} (hn : 1 ≤ n)
    (hε : 0 ≤ ε) (hγ : γ < 1) (hs : 0 < s) :
    (8 * (n + (16 * n ^ ε) ^ (1 / (1 - γ)) + 1)) ^ (s + 2) ≤
      (8 * (2 + (16 : ℝ) ^ (1 / (1 - γ)))) ^ (s + 2) *
        n ^ ((1 + ε / (1 - γ)) * (s + 2)) := by
  have hn0 : 0 < n := by linarith
  have hb : 0 ≤ ε / (1 - γ) := div_nonneg hε (by linarith)
  have hk : 1 ≤ 1 + ε / (1 - γ) := by linarith
  have hnle : n ≤ n ^ (1 + ε / (1 - γ)) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn hk
  have hone : 1 ≤ n ^ (1 + ε / (1 - γ)) := Real.one_le_rpow hn (by linarith)
  have hT : (16 * n ^ ε) ^ (1 / (1 - γ)) ≤
      (16 : ℝ) ^ (1 / (1 - γ)) * n ^ (1 + ε / (1 - γ)) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 16) (Real.rpow_nonneg hn0.le _),
      ← Real.rpow_mul hn0.le]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le hn (by simp only [div_eq_mul_inv, one_mul]; linarith)
  have hD : 8 * (n + (16 * n ^ ε) ^ (1 / (1 - γ)) + 1) ≤
      (8 * (2 + (16 : ℝ) ^ (1 / (1 - γ)))) * n ^ (1 + ε / (1 - γ)) := by
    nlinarith
  have hh := Real.rpow_le_rpow (by positivity) hD (by linarith : 0 ≤ s + 2)
  rwa [Real.mul_rpow (by positivity : 0 ≤ 8 * (2 + (16 : ℝ) ^ (1 / (1 - γ))))
    (Real.rpow_nonneg hn0.le _), ← Real.rpow_mul hn0.le] at hh

/-- See Subsection 6.1 of the paper: insertion of an active
coordinate vector into the existing exterior-first assembly. -/
theorem assemble_single (e a : ℕ) (j : Fin (a + 1)) :
    RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) 0
      (EuclideanSpace.single j 1) =
        EuclideanSpace.single (j.castLE (show a + 1 ≤ e + a + 1 by omega)) 1 := by
  ext k
  by_cases hk : k.val < a + 1
  · let l : Fin (a + 1) := ⟨k.val, hk⟩
    have hkl : k = l.castLE (show a + 1 ≤ e + a + 1 by omega) := by apply Fin.ext; rfl
    rw [hkl, InterpolatingDensities.assemble_exterior_active]
    simp only [EuclideanSpace.single, PiLp.single_apply]
    have heq : (l.castLE (show a + 1 ≤ e + a + 1 by omega) =
      j.castLE (show a + 1 ≤ e + a + 1 by omega)) ↔ l = j := Fin.castLE_inj
    simp only [heq]
  · let l : Fin e := ⟨k.val - (a + 1), by have := k.isLt; omega⟩
    have hkl : k = (⟨a + 1 + l.val, by have := l.isLt; omega⟩ : Fin (e + a + 1)) := by
      apply Fin.ext; dsimp [l]; omega
    rw [hkl, InterpolantLocalLaws.assemble_exterior_retained]
    have hne : (⟨a + 1 + l.val, by have := l.isLt; omega⟩ : Fin (e + a + 1)) ≠
        j.castLE (show a + 1 ≤ e + a + 1 by omega) := by
      intro hh
      have hh' := congrArg Fin.val hh
      have := j.isLt
      dsimp at hh'
      omega
    simp [EuclideanSpace.single, hne]

/-- Internal calculus bridge for Subsection 6.1. The unrestricted
Hessian of the actual assembly pullback is the active ambient block. -/
theorem hessian_assembly_internal (e a : ℕ) (y : EuclideanSpace ℝ (Fin e))
    (W : EuclideanSpace ℝ (Fin (e + a + 1)) → ℝ)
    (u : EuclideanSpace ℝ (Fin (a + 1)))
    (hW : ContDiffAt ℝ ∞ W (RetainedSimplex.assemble e a
      (InterpolatingDensities.exteriorPermutation e a) y u)) (i j : Fin (a + 1)) :
    hessianMatrix (fun v => W (RetainedSimplex.assemble e a
      (InterpolatingDensities.exteriorPermutation e a) y v)) u i j =
      fderiv ℝ (fderiv ℝ W) (RetainedSimplex.assemble e a
        (InterpolatingDensities.exteriorPermutation e a) y u)
        (EuclideanSpace.single (i.castLE (show a + 1 ≤ e + a + 1 by omega)) 1)
        (EuclideanSpace.single (j.castLE (show a + 1 ≤ e + a + 1 by omega)) 1) := by
  let σ := InterpolatingDensities.exteriorPermutation e a
  let E := EuclideanSpace ℝ (Fin e)
  let F := EuclideanSpace ℝ (Fin (a + 1))
  let A : F →L[ℝ] EuclideanSpace ℝ (Fin (e + a + 1)) :=
    LinearMap.toContinuousLinearMap
      ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ).toLinearEquiv.toLinearMap.comp
        ((RetainedSimplex.join e (a + 1)).toLinearMap.comp (LinearMap.inr ℝ E F)))
  let z := RetainedSimplex.assemble e a σ y 0
  have hY (x : F) : A x + z = RetainedSimplex.assemble e a σ y x := by
    change RetainedSimplex.assemble e a σ 0 x + RetainedSimplex.assemble e a σ y 0 = _
    simp only [RetainedSimplex.assemble, ← map_add]
    congr 1
    rw [← (RetainedSimplex.join e (a + 1)).map_add]
    congr 1
    exact Prod.ext (zero_add _) (add_zero _)
  have hcomp : (fun v => W (RetainedSimplex.assemble e a σ y v)) = fun v => W (A v + z) :=
    funext fun v => congrArg W (hY v).symm
  have hs : ContDiffAt ℝ ∞ (fun v => W (A v + z)) u :=
    (hY u ▸ hW).comp u (A.contDiff.add contDiff_const).contDiffAt
  rw [hcomp, Intrinsic.hessianMatrix_eq_second hs,
    AffineMetricTransport.hessian_comp_affine A z ((hY u ▸ hW).of_le (by simp)), hY]
  have hsingle (k : Fin (a + 1)) : A (EuclideanSpace.single k 1) =
      EuclideanSpace.single (k.castLE (show a + 1 ≤ e + a + 1 by omega)) 1 :=
    assemble_single e a k
  rw [hsingle, hsingle]

/-- See Subsection 6.1 of the paper, whole-simplex interaction clause at one
endpoint. The energy is realized on the entire open assembly preimage. The bound concerns its unrestricted ambient active Hessian. Constants
precede the active size, ambient period, exterior, and simplex point. -/
theorem physical_endpoint_sq (s ε : ℝ) (hs : 0 < s)
    (hε : 0 ≤ ε) (hσε : min s 1 / 2 + 2 * ε < 1) :
    ∃ (n₀ : ℕ) (C q : ℝ), 2 ≤ n₀ ∧ 0 < C ∧ 0 < q ∧
      ∀ p : Parameters, p.val.2 = s → ∀ (e a : ℕ), n₀ ≤ a + 1 → 4 * (a + 1) ≤ e + a + 1 →
      ∀ y : AffineSimplex.chartDomain e ((e + a : ℕ) + 1),
      InterpolantLocalLaws.exteriorGeometry s ε e a y.val →
      let Y := RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val
      let D := Y ⁻¹' gapAmbientDomain (e + a).succPNat
      ∃ K : EuclideanSpace ℝ (Fin (a + 1)) → ℝ,
        ContDiffOn ℝ ∞ K D ∧
        (∀ u (hu : u ∈ D), K u = physicalAmbientGapEnergy p (e + a).succPNat ⟨Y u, hu⟩) ∧
        ∀ u ∈ AffineSimplex.massSimplex a (((e + a : ℕ) + 1 : ℝ) - ∑ k, y.val k),
        ∀ i j : Fin (a + 1),
          |hessianMatrix K u i j| ^ 2 ≤ C * (a + 1 : ℝ) ^ q *
            InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s (WithLp.ofLp u) := by
  classical
  obtain ⟨n₀, hn₀, hprofile⟩ := physical_coefficient_profile s ε hs hε hσε
  let γ := min s 1 / 2 + ε
  let B := s * (s + 1) * PeriodicPower.bound (s + 2) (by linarith)
  let A := 2 * B * (8 * (2 + (16 : ℝ) ^ (1 / (1 - γ)))) ^ (s + 2) * (1 + 1 / s)
  let k := (1 + ε / (1 - γ)) * (s + 2)
  have hγ : γ < 1 := by dsimp [γ]; linarith
  have hB : 0 < B := mul_pos (mul_pos hs (by linarith)) (PeriodicPower.bound_pos _ (by linarith))
  have hA : 0 < A := by dsimp [A]; positivity
  have hk : 0 < k := by dsimp [k]; positivity
  refine ⟨n₀, 4 * A ^ 2, 2 * k, hn₀, by positivity, by positivity, ?_⟩
  intro p hps e a hnn hsize y hgeom Y D
  let N := (e + a).succPNat
  obtain ⟨W, hW, hval, hjet⟩ := PhysicalEnergy.ambient_derivatives p N
  let K := fun u => W (Y u)
  have hK : ContDiffOn ℝ ∞ K D := hW.comp
    (InterpolantLocalLaws.contDiff_exterior_assembly e a y.val).contDiffOn (fun _ h => h)
  refine ⟨K, hK, fun u hu => hval ⟨Y u, hu⟩, ?_⟩
  intro u hu i j
  have hxs := InterpolatingDensities.assemble_exterior_mem e a y u hu
  have hx : WithLp.ofLp (Y u) ∈ Riesz1.gapSimplex N := ⟨hxs.1, by
    simpa only [N, Nat.succPNat_coe, Nat.cast_succ] using hxs.2⟩
  have hxD : Y u ∈ gapAmbientDomain N := PhysicalEnergy.simplex_subset_ambient N _ hx
  have hWat := hW.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hxD)
  let ai := i.castLE (show a + 1 ≤ e + a + 1 by omega)
  let aj := j.castLE (show a + 1 ≤ e + a + 1 by omega)
  let T := (16 * (a + 1 : ℝ) ^ ε) ^ (1 / (1 - γ))
  let D₀ := 8 * ((a + 1 : ℝ) + T + 1)
  let F (l : Fin (N : ℕ)) (r : Fin ((N : ℕ) / 2)) :=
    (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
      PhysicalEnergy.intervalCoefficient p N
        ⟨cyclicGapSum N l (r.val + 1) (WithLp.ofLp (Y u)),
          hxD l (r.val + 1) (by omega) (by have := r.isLt; omega)⟩
  have hmat : hessianMatrix K u i j = ∑ l, ∑ r,
      if ai ∈ cyclicIndexInterval N l (r.val + 1) ∧
        aj ∈ cyclicIndexInterval N l (r.val + 1) then F l r else 0 := by
    trans fderiv ℝ (fderiv ℝ W) (Y u) (EuclideanSpace.single ai 1) (EuclideanSpace.single aj 1)
    · exact hessian_assembly_internal e a y.val W u hWat i j
    rw [(hjet ⟨Y u, hxD⟩ (EuclideanSpace.single ai 1) (EuclideanSpace.single aj 1)).2]
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro r _
    have hr : r.val + 1 ≤ (N : ℕ) := by have := r.isLt; omega
    have hsingle (b : Fin (N : ℕ)) :
        cyclicGapSum N l (r.val + 1) (WithLp.ofLp (EuclideanSpace.single b 1)) =
          if b ∈ cyclicIndexInterval N l (r.val + 1) then 1 else 0 := by
      convert cyclicGapSum_single N l b hr using 1
      congr 1
      ext t
      simp [EuclideanSpace.single, PiLp.single_apply, eq_comm]
    rw [hsingle, hsingle]
    by_cases hi : ai ∈ cyclicIndexInterval N l (r.val + 1) <;>
      by_cases hj : aj ∈ cyclicIndexInterval N l (r.val + 1) <;>
      simp only [F, hi, hj, true_and, false_and, and_false, ↓reduceIte, mul_one, mul_zero]
  have hF : ∀ l r, ai ∈ cyclicIndexInterval N l (r.val + 1) →
      0 ≤ F l r ∧ F l r ≤
        (2 * B * D₀ ^ (s + 2) * (1 + u i ^ (-s - 2))) * (r.val + 1 : ℝ) ^ (-s - 2) := by
    intro l r hi
    obtain ⟨hℓ, hh⟩ := hprofile p hps e a hnn hsize y hgeom u hu l (r.val + 1)
      (by omega) (by have := r.isLt; dsimp [N] at *; omega) i hi
    simp only [Nat.cast_add, Nat.cast_one] at hh
    have hnonneg := (PhysicalEnergy.intervalCoefficient_pos p N
      ⟨cyclicGapSum N l (r.val + 1) (WithLp.ofLp (Y u)), hℓ⟩).le
    have hm : 0 ≤ (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) ∧
        (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) ≤ 2 := by
      split_ifs <;> norm_num
    constructor
    · exact mul_nonneg hm.1 hnonneg
    · have hh' := mul_le_mul hm.2 hh hnonneg (by norm_num : (0 : ℝ) ≤ 2)
      convert hh' using 1; dsimp only [F, B, D₀, T, γ]; ring
  have hinv : 0 ≤ u i ^ (-s - 2) := Real.rpow_nonneg (hu.1 i).le _
  have hb := interval_entry_bound_internal N hs (by positivity) F ai aj hF
  rw [← hmat] at hb
  have hpoly := cutoff_polynomial_internal
    (show (1 : ℝ) ≤ a + 1 by have := Nat.cast_nonneg a (α := ℝ); linarith) hε hγ hs
  have hupper : |hessianMatrix K u i j| ≤
      A * (a + 1 : ℝ) ^ k * (1 + u i ^ (-s - 2)) := by
    have hmult := mul_le_mul_of_nonneg_left hpoly
      (show 0 ≤ 2 * B * (1 + u i ^ (-s - 2)) * (1 + 1 / s) by positivity)
    apply hb.trans
    convert hmult using 1 <;> dsimp only [A, D₀, T, k] <;> ring
  have hsq := mul_self_le_mul_self (abs_nonneg _) hupper
  have hweight := InterpolationCoefficients.curvature_power_sq_le_weight s hs a
    (WithLp.ofLp u) hu.1 i
  have hpower : ((a + 1 : ℝ) ^ k) ^ 2 = (a + 1 : ℝ) ^ (2 * k) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ (a + 1 : ℝ))]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have hlast := mul_le_mul_of_nonneg_left hweight
    (show 0 ≤ A ^ 2 * ((a + 1 : ℝ) ^ k) ^ 2 by positivity)
  calc
    _ ≤ A ^ 2 * ((a + 1 : ℝ) ^ k) ^ 2 * (1 + u i ^ (-s - 2)) ^ 2 := by
      nlinarith only [hsq]
    _ ≤ A ^ 2 * ((a + 1 : ℝ) ^ k) ^ 2 *
        (4 * InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s (WithLp.ofLp u)) := hlast
    _ = _ := by rw [hpower]; ring

/-- Internal convexity step for Subsection 6.1: the square of a
convex combination inherits a common endpoint square envelope. -/
theorem convex_sq_internal {a b B t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (ha : |a| ^ 2 ≤ B) (hb : |b| ^ 2 ≤ B) :
    |(1 - t) * a + t * b| ^ 2 ≤ B := by
  have hprod := mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2)) (sq_nonneg (a - b))
  have hle := add_le_add (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr ht.2))
    (mul_le_mul_of_nonneg_left hb ht.1)
  calc
    _ = (1 - t) * |a| ^ 2 + t * |b| ^ 2 - t * (1 - t) * (a - b) ^ 2 := by
      simp only [sq_abs]
      ring
    _ ≤ (1 - t) * |a| ^ 2 + t * |b| ^ 2 := sub_le_self _ hprod
    _ ≤ (1 - t) * B + t * B := hle
    _ = B := by ring

/-- See Subsection 6.1 of the paper, whole-simplex interaction-entry clause.
Above a threshold depending only on the exponent and tolerance, the
actual two-endpoint interaction Hessian has square bounded by `C n^C W`,
uniformly in both periods, geometrically admissible exteriors, the
interpolation parameter, and the entire active simplex. The unrestricted
ambient energy realizations agree on open neighborhoods. The constants
also precede temperature. -/
theorem physical_interaction_sq_internal (s ε : ℝ) (hs : 0 < s)
    (hε : 0 ≤ ε) (hσε : min s 1 / 2 + 2 * ε < 1) :
    ∃ (n₀ : ℕ) (C : ℝ), 2 ≤ n₀ ∧ 0 < C ∧
      ∀ p : Parameters, p.val.2 = s → ∀ (e f a : ℕ), n₀ ≤ a + 1 →
      4 * (a + 1) ≤ e + a + 1 → 4 * (a + 1) ≤ f + a + 1 →
      ∀ (y : AffineSimplex.chartDomain e ((e + a : ℕ) + 1))
        (z : AffineSimplex.chartDomain f ((f + a : ℕ) + 1)),
      InterpolantLocalLaws.exteriorGeometry s ε e a y.val →
      InterpolantLocalLaws.exteriorGeometry s ε f a z.val →
      ∀ L : ℝ,
      ((e + a : ℕ) + 1 : ℝ) - ∑ k, y.val k = L →
      ((f + a : ℕ) + 1 : ℝ) - ∑ k, z.val k = L →
      let Y := RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val
      let Z := RetainedSimplex.assemble f a (InterpolatingDensities.exteriorPermutation f a) z.val
      let Dy := Y ⁻¹' gapAmbientDomain (e + a).succPNat
      let Dz := Z ⁻¹' gapAmbientDomain (f + a).succPNat
      ∃ Ky Kz : EuclideanSpace ℝ (Fin (a + 1)) → ℝ,
        ContDiffOn ℝ ∞ Ky Dy ∧ ContDiffOn ℝ ∞ Kz Dz ∧
        (∀ u (hu : u ∈ Dy), Ky u = physicalAmbientGapEnergy p (e + a).succPNat ⟨Y u, hu⟩) ∧
        (∀ u (hu : u ∈ Dz), Kz u = physicalAmbientGapEnergy p (f + a).succPNat ⟨Z u, hu⟩) ∧
        ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ AffineSimplex.massSimplex a L,
        ∀ i j : Fin (a + 1),
          |(1 - t) * hessianMatrix Ky u i j + t * hessianMatrix Kz u i j| ^ 2 ≤
            C * (a + 1 : ℝ) ^ C *
              InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s (WithLp.ofLp u) := by
  obtain ⟨n₀, C₀, q, hn₀, hC₀, hq, hbound⟩ := physical_endpoint_sq s ε hs hε hσε
  let C := C₀ + q + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hC₀C : C₀ ≤ C := by dsimp [C]; linarith
  have hqC : q ≤ C := by dsimp [C]; linarith
  refine ⟨n₀, C, hn₀, hC, ?_⟩
  intro p hps e f a hnn hNy hNz y z hgy hgz L hyL hzL Y Z Dy Dz
  obtain ⟨Ky, hKy, hky, hby⟩ := hbound p hps e a hnn hNy y hgy
  obtain ⟨Kz, hKz, hkz, hbz⟩ := hbound p hps f a hnn hNz z hgz
  refine ⟨Ky, Kz, hKy, hKz, hky, hkz, ?_⟩
  intro t ht u hu i j
  have huy : u ∈ AffineSimplex.massSimplex a (((e + a : ℕ) + 1 : ℝ) - ∑ k, y.val k) :=
    hyL ▸ hu
  have huz : u ∈ AffineSimplex.massSimplex a (((f + a : ℕ) + 1 : ℝ) - ∑ k, z.val k) :=
    hzL ▸ hu
  have hb := convex_sq_internal ht (hby u huy i j) (hbz u huz i j)
  have hn : (1 : ℝ) ≤ a + 1 := by have := Nat.cast_nonneg a (α := ℝ); linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hn hqC
  have hweight : 0 ≤ InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s (WithLp.ofLp u) :=
    le_trans zero_le_one (InterpolantLocalLaws.one_le_exceptionalWeight s _ (fun i => (hu.1 i).le))
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul hC₀C hpow (by positivity) hC.le) hweight)

/-- Internal realization-independence bridge for Subsection 6.1.
Agreement on an open ambient neighborhood fixes the unrestricted
Hessian, so the interaction estimate transfers to realizations constructed
by other packages. Agreement merely on the mass hyperplane is insufficient. -/
theorem hessian_eqOn_internal {n : ℕ}
    {V W : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hVW : EqOn V W U) {u : EuclideanSpace ℝ (Fin n)} (hu : u ∈ U) :
    hessianMatrix V u = hessianMatrix W u := by
  have h : V =ᶠ[𝓝 u] W := by
    filter_upwards [hU.mem_nhds hu] with x hx
    exact hVW hx
  have hd := h.gradient.fderiv_eq (𝕜 := ℝ)
  funext i j
  exact congrArg (fun T => (T (EuclideanSpace.single j 1)) i) hd

end Riesz2.InterpolationExceptional
