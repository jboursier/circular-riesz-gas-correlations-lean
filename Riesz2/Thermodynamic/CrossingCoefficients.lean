/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.InterpolationCoefficientsPart2
public import Riesz2.DecayLong.PhysicalCorePart6
public import Riesz2.DecayLong.BoundaryEntriesPart4

/-!
# Rank bounds for fixed-exterior crossing intervals

Deterministic ingredients of Subsection 6.1. The active block, exterior geometry and
image coefficients are the existing objects. All constants are independent of
temperature and physical volume.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical ContDiff

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.CrossingCoefficients

/-- Internal cyclic geometry for Subsection 6.1: the two exterior pieces covering a crossing interval are also contained in it. -/
theorem crossing_pieces_internal (N : ℕ+) (n : ℕ) (hn : n < (N : ℕ))
    (i : Fin (N : ℕ)) (r : ℕ) (hr : r ≤ (N : ℕ))
    (hmeet : ∃ j ∈ cyclicIndexInterval N i r, j.val < n) :
    ∃ p q : ℕ, p ≤ (N : ℕ) - n ∧ q ≤ (N : ℕ) - n ∧
      (∀ j ∈ cyclicIndexInterval N i r,
        j.val < n ∨ (n ≤ j.val ∧ j.val < n + p) ∨ (N : ℕ) - q ≤ j.val) ∧
      (∀ j : Fin (N : ℕ), n ≤ j.val → j.val < n + p →
        j ∈ cyclicIndexInterval N i r) ∧
      (∀ j : Fin (N : ℕ), (N : ℕ) - q ≤ j.val →
        j ∈ cyclicIndexInterval N i r) := by
  have hi := i.isLt
  have hm (j : Fin (N : ℕ)) :
      j ∈ cyclicIndexInterval N i r ↔
      (if i.val ≤ j.val then j.val - i.val else j.val + (N : ℕ) - i.val) < r := by
    rw [mem_cyclicIndexInterval_iff N i j hr, Fin.val_sub]
    by_cases hij : i.val ≤ j.val
    · rw [ite_eq_left hij]
      rw [show (N : ℕ) - i.val + j.val = (j.val - i.val) + (N : ℕ) by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by have := j.isLt; omega)]
    · rw [ite_eq_right hij, Nat.mod_eq_of_lt (by have := j.isLt; omega)]
      omega
  by_cases hw : (N : ℕ) < i.val + r
  · refine ⟨i.val + r - (N : ℕ) - n, (N : ℕ) - max n i.val,
      by omega, by omega, ?_, ?_, ?_⟩
    · intro j hj
      have hh := (hm j).mp hj
      have hjN := j.isLt
      split_ifs at hh <;> omega
    · intro j hj hj'
      apply (hm j).mpr
      have hjN := j.isLt
      split_ifs <;> omega
    · intro j hj
      apply (hm j).mpr
      have hjN := j.isLt
      split_ifs <;> omega
  · obtain ⟨j, hj, hjn⟩ := hmeet
    have hh := (hm j).mp hj
    have hjN := j.isLt
    have hin : i.val < n := by split_ifs at hh <;> omega
    refine ⟨i.val + r - n, 0, by omega, by omega, ?_, ?_, ?_⟩
    · intro k hk
      have hhk := (hm k).mp hk
      have hkN := k.isLt
      split_ifs at hhk <;> omega
    · intro k hk hk'
      apply (hm k).mpr
      split_ifs <;> omega
    · intro k hk
      have := k.isLt
      omega

/-- Internal scalar rank split in Subsection 6.1. The threshold is
written using an exponent chosen before ε. -/
theorem anchored_rank_internal {σ ε n r m : ℝ}
    (hσ : σ < 1) (_hε : 0 ≤ ε) (hε' : σ + 2 * ε ≤ 1)
    (hn : 1 ≤ n) (hr : 1 ≤ r) (hm0 : 0 ≤ m)
    (hm : |m - r| ≤ 4 * n ^ ε * r ^ (σ + ε)) :
    r ≤ 2 * m + 8 ^ (2 / (1 - σ)) * n ^ ((2 / (1 - σ)) * ε) := by
  let b := 2 / (1 - σ)
  have hb : 0 < b := by dsimp [b]; positivity
  have hn0 : 0 < n := by linarith
  have hr0 : 0 < r := by linarith
  have hinv : 1 / b = (1 - σ) / 2 := by
    dsimp [b]
    field_simp
  have hexp : σ + ε - 1 ≤ -1 / b := by
    rw [neg_div, hinv]
    linarith
  let T := (8 * n ^ ε) ^ b
  have hT : T = 8 ^ b * n ^ (b * ε) := by
    change (8 * n ^ ε) ^ b = _
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hn0.le, mul_comm ε b]
  by_cases hlarge : T ≤ r
  · have hpow : r ^ (-1 / b) ≤ (8 * n ^ ε)⁻¹ := by
      have h := Real.rpow_le_rpow_of_nonpos (by dsimp [T]; positivity) hlarge
        (div_nonpos_of_nonpos_of_nonneg (show (-1 : ℝ) ≤ 0 by norm_num) hb.le)
      dsimp only [T] at h
      rw [← Real.rpow_mul (by positivity : 0 ≤ 8 * n ^ ε),
        show b * (-1 / b) = -1 by field_simp, Real.rpow_neg_one] at h
      exact h
    have hpow' := (Real.rpow_le_rpow_of_exponent_le hr hexp).trans hpow
    have he : r ^ (σ + ε) = r * r ^ (σ + ε - 1) := by
      conv_rhs => lhs; rw [← Real.rpow_one r]
      rw [← Real.rpow_add hr0]
      congr 1
      ring
    have he' : 4 * n ^ ε * r ^ (σ + ε) ≤ r / 2 := by
      rw [he]
      have hh := mul_le_mul_of_nonneg_left hpow' (by positivity : 0 ≤ 4 * n ^ ε * r)
      have hz : n ^ ε ≠ 0 := (Real.rpow_pos_of_pos hn0 ε).ne'
      field_simp at hh
      nlinarith
    have hlow := (abs_le.mp hm).1
    rw [← hT]
    have hT0 : 0 ≤ T := by dsimp [T]; positivity
    linarith
  · rw [← hT]
    linarith

/-- Internal rank estimate in Subsection 6.1: positivity, an active
cutoff and the exterior prefix and suffix estimates give a rank-proportional
mass bound. The exponent `2/(1-σ)` is chosen before the tolerance. -/
theorem crossing_mass_lower_internal (N : ℕ+) (n : ℕ) (hn : n < (N : ℕ))
    (σ ε d : ℝ) (hσ : σ < 1) (hε : 0 ≤ ε) (hε' : σ + 2 * ε ≤ 1)
    (hn1 : 1 ≤ n) (hd : 0 < d) (hd1 : d ≤ 1)
    (x : Fin (N : ℕ) → ℝ) (hx : ∀ j, 0 ≤ x j)
    (hactive : ∀ j : Fin (N : ℕ), j.val < n → d ≤ x j)
    (hR : ∀ p : ℕ, 1 ≤ p → p ≤ (N : ℕ) - n →
      |(∑ j ∈ Finset.univ.filter (fun j : Fin (N : ℕ) =>
        n ≤ j.val ∧ j.val < n + p), x j) - p| ≤
          4 * (n : ℝ) ^ ε * (p : ℝ) ^ (σ + ε))
    (hL : ∀ q : ℕ, 1 ≤ q → q ≤ (N : ℕ) - n →
      |(∑ j ∈ Finset.univ.filter (fun j : Fin (N : ℕ) =>
        (N : ℕ) - q ≤ j.val), x j) - q| ≤
          4 * (n : ℝ) ^ ε * (q : ℝ) ^ (σ + ε))
    (i : Fin (N : ℕ)) (r : ℕ) (hr : r ≤ (N : ℕ))
    (hmeet : ∃ j ∈ cyclicIndexInterval N i r, j.val < n) :
    d / (5 + 2 * 8 ^ (2 / (1 - σ)) * (n : ℝ) ^ ((2 / (1 - σ)) * ε)) * r ≤
      cyclicGapSum N i r x := by
  obtain ⟨p, q, hp, hq, hcover, hP, hQ⟩ :=
    crossing_pieces_internal N n hn i r hr hmeet
  let J := cyclicIndexInterval N i r
  let A := J.filter (fun j => j.val < n)
  let P := Finset.univ.filter (fun j : Fin (N : ℕ) => n ≤ j.val ∧ j.val < n + p)
  let Q := Finset.univ.filter (fun j : Fin (N : ℕ) => (N : ℕ) - q ≤ j.val)
  let m := ∑ j ∈ J, x j
  let T := 8 ^ (2 / (1 - σ)) * (n : ℝ) ^ ((2 / (1 - σ)) * ε)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hm : 0 ≤ m := Finset.sum_nonneg (fun j _ => hx j)
  have hPS : P ⊆ J := by
    intro j hj
    exact hP j (Finset.mem_filter.mp hj).2.1 (Finset.mem_filter.mp hj).2.2
  have hQS : Q ⊆ J := by
    intro j hj
    exact hQ j (Finset.mem_filter.mp hj).2
  have hPmass : (∑ j ∈ P, x j) ≤ m :=
    Finset.sum_le_sum_of_subset_of_nonneg hPS (fun j _ _ => hx j)
  have hQmass : (∑ j ∈ Q, x j) ≤ m :=
    Finset.sum_le_sum_of_subset_of_nonneg hQS (fun j _ _ => hx j)
  have hA : d * (A.card : ℝ) ≤ m := by
    calc
      _ = ∑ _j ∈ A, d := by simp [mul_comm]
      _ ≤ ∑ j ∈ A, x j := Finset.sum_le_sum (fun j hj =>
        hactive j (Finset.mem_filter.mp hj).2)
      _ ≤ m := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun j _ _ => hx j)
  have hmeetmass : d ≤ m := by
    obtain ⟨j, hj, hjn⟩ := hmeet
    exact (hactive j hjn).trans (Finset.single_le_sum (fun k _ => hx k) hj)
  have hPc : (P.card : ℝ) = p := by
    have h := InterpolationCoefficients.cyclicGapSum_filter N n p (by omega) (by omega)
      (fun _ => (1 : ℝ))
    simpa [P, cyclicGapSum] using h.symm
  have hQc : (Q.card : ℝ) = q := by
    by_cases hq0 : q = 0
    · have hQ0 : Q = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro j _
        simp [hq0]
      simp [hQ0, hq0]
    have h := InterpolationCoefficients.cyclicGapSum_filter N ((N : ℕ) - q) q
      (by omega) (by omega) (fun _ => (1 : ℝ))
    have he : (Finset.univ.filter (fun j : Fin (N : ℕ) =>
        (N : ℕ) - q ≤ j.val ∧ j.val < (N : ℕ) - q + q)) = Q := by
      ext j
      have hj := j.isLt
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Q]
      omega
    rw [he] at h
    simpa [cyclicGapSum] using h.symm
  have hcard : (r : ℝ) ≤ (A.card : ℝ) + p + q := by
    rw [← hPc, ← hQc, ← card_cyclicIndexInterval N i hr]
    have hpoint (j : Fin (N : ℕ)) (hj : j ∈ J) :
        (1 : ℝ) ≤ (if j ∈ A then 1 else 0) + (if j ∈ P then 1 else 0) +
          (if j ∈ Q then 1 else 0) := by
      rcases hcover j hj with h | h | h
      · have ha : j ∈ A := Finset.mem_filter.mpr ⟨hj, h⟩
        simp only [ha, ↓reduceIte]
        split_ifs <;> norm_num
      · have hp' : j ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
        simp only [hp', ↓reduceIte]
        split_ifs <;> norm_num
      · have hq' : j ∈ Q := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
        simp only [hq', ↓reduceIte]
        split_ifs <;> norm_num
    have hh := Finset.sum_le_sum hpoint
    simp only [Finset.sum_add_distrib] at hh
    have hs (S : Finset (Fin (N : ℕ))) (hS : S ⊆ J) :
        (∑ j ∈ J, if j ∈ S then (1 : ℝ) else 0) = S.card := by
      rw [← Finset.sum_filter]
      have he : J.filter (fun j => j ∈ S) = S := by
        ext j
        simp only [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
      rw [he]
      simp
    rw [hs A (Finset.filter_subset _ _), hs P hPS, hs Q hQS] at hh
    simpa [J] using hh
  have hpr : (p : ℝ) ≤ 2 * m + T := by
    by_cases hp0 : p = 0
    · simp only [hp0, Nat.cast_zero]
      positivity
    · exact (anchored_rank_internal hσ hε hε' (by exact_mod_cast hn1)
        (by exact_mod_cast (show 1 ≤ p by omega))
        (Finset.sum_nonneg (fun j _ => hx j)) (hR p (by omega) hp)).trans
          (by dsimp only [T, P] at *; linarith)
  have hqr : (q : ℝ) ≤ 2 * m + T := by
    by_cases hq0 : q = 0
    · simp only [hq0, Nat.cast_zero]
      positivity
    · exact (anchored_rank_internal hσ hε hε' (by exact_mod_cast hn1)
        (by exact_mod_cast (show 1 ≤ q by omega))
        (Finset.sum_nonneg (fun j _ => hx j)) (hL q (by omega) hq)).trans
          (by dsimp only [T, Q] at *; linarith)
  have hdr : d * (r : ℝ) ≤ (5 + 2 * T) * m := by
    have hp' := mul_le_mul_of_nonneg_left hpr hd.le
    have hq' := mul_le_mul_of_nonneg_left hqr hd.le
    have hc := mul_le_mul_of_nonneg_left hcard hd.le
    have hdm : d * m ≤ m := mul_le_of_le_one_left hm hd1
    have ht := mul_le_mul_of_nonneg_left hmeetmass hT
    nlinarith
  rw [← sum_cyclicIndexInterval_eq_cyclicGapSum N i hr]
  have hden : 5 + 2 * 8 ^ (2 / (1 - σ)) * (n : ℝ) ^ ((2 / (1 - σ)) * ε) =
      5 + 2 * T := by dsimp [T]; ring
  rw [hden]
  change d / (5 + 2 * T) * r ≤ m
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity : 0 < 5 + 2 * T)).mpr
  nlinarith

/-- Internal power bookkeeping for Subsection 6.1: the geometric
rank prefactor has a fixed loss exponent, chosen before ε. -/
theorem rank_prefactor_internal {n b K ε : ℝ} (hn : 1 ≤ n)
    (hb : 0 ≤ b) (_hK : 0 ≤ K) (hε : 0 ≤ ε) :
    (1 / (5 + 2 * 8 ^ b)) * n ^ (-(K + b) * ε) ≤
      n ^ (-(K * ε)) / (5 + 2 * 8 ^ b * n ^ (b * ε)) := by
  have hn0 : 0 < n := by linarith
  have hp : 1 ≤ n ^ (b * ε) := Real.one_le_rpow hn (mul_nonneg hb hε)
  have hD : 0 < 5 + 2 * (8 : ℝ) ^ b := by positivity
  have hden : 5 + 2 * (8 : ℝ) ^ b * n ^ (b * ε) ≤
      (5 + 2 * 8 ^ b) * n ^ (b * ε) := by nlinarith
  have he : (1 / (5 + 2 * (8 : ℝ) ^ b)) * n ^ (-(K + b) * ε) =
      n ^ (-(K * ε)) / ((5 + 2 * 8 ^ b) * n ^ (b * ε)) := by
    rw [show -(K + b) * ε = -(K * ε) + -(b * ε) by ring,
      Real.rpow_add hn0]
    simp_rw [Real.rpow_neg hn0.le]
    field_simp
  rw [he]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden

/-- See Subsection 6.1 of the paper: every interval meeting the active block has
mass bounded below by its rank on the good event. The
explicit constants depend only on `s` and the prescribed rigidity factor
`K`. The estimate holds at all active sizes. -/
theorem physical_crossing_rank_lower (s K ε : ℝ)
    (_hs : 0 ≤ s) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hε' : min s 1 / 2 + 2 * ε ≤ 1)
    (e a : ℕ) (he : 0 < e)
    (y : AffineSimplex.chartDomain e ((e + a : ℕ) + 1))
    (hgeom : InterpolantLocalLaws.exteriorGeometry s ε e a y.val)
    (u : EuclideanSpace ℝ (Fin (a + 1)))
    (hu : u ∈ AffineSimplex.massSimplex a (((e + a : ℕ) + 1 : ℝ) - ∑ k, y.val k))
    (hgood : WithLp.ofLp u ∈ goodBlockEvent s a.succPNat (e + a).succPNat (K * ε))
    (i : Fin (e + a + 1)) (r : ℕ) (hr : r ≤ e + a + 1)
    (hmeet : ∃ j ∈ cyclicIndexInterval (e + a).succPNat i r, j.val < a + 1) :
    (1 / (5 + 2 * 8 ^ (2 / (1 - min s 1 / 2)))) *
      (a + 1 : ℝ) ^ (-(K + 2 / (1 - min s 1 / 2)) * ε) * r ≤
        cyclicGapSum (e + a).succPNat i r
          (WithLp.ofLp (RetainedSimplex.assemble e a
            (InterpolatingDensities.exteriorPermutation e a) y.val u)) := by
  let σ := min s 1 / 2
  have hσ : σ < 1 := by dsimp [σ]; have := min_le_right s (1 : ℝ); linarith
  have hb : 0 ≤ 2 / (1 - σ) := by positivity
  let N := (e + a).succPNat
  let x := WithLp.ofLp (RetainedSimplex.assemble e a
    (InterpolatingDensities.exteriorPermutation e a) y.val u)
  have hx := InterpolatingDensities.assemble_exterior_mem e a y u hu
  have hn1 : (1 : ℝ) ≤ a + 1 := by have := Nat.cast_nonneg (α := ℝ) a; linarith
  have hd : 0 < (a + 1 : ℝ) ^ (-(K * ε)) := by positivity
  have hd1 : (a + 1 : ℝ) ^ (-(K * ε)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (neg_nonpos.mpr (mul_nonneg hK hε))
  have hact (j : Fin (e + a + 1)) (hj : j.val < a + 1) :
      (a + 1 : ℝ) ^ (-(K * ε)) ≤ x j := by
    let k : Fin (a + 1) := ⟨j.val, hj⟩
    have heq : j = Fin.castLE (show a + 1 ≤ e + a + 1 by omega) k := Fin.ext rfl
    rw [heq]
    dsimp only [x]
    rw [InterpolatingDensities.assemble_exterior_active e a y.val u k (by omega)]
    simpa only [Nat.succPNat_coe, Nat.cast_succ] using (hgood.2.1 k).1
  have hp := rank_prefactor_internal hn1 hb hK hε
  have hh := crossing_mass_lower_internal N (a + 1) (by dsimp [N]; omega)
    σ ε ((a + 1 : ℝ) ^ (-(K * ε))) hσ hε hε' (by omega) hd hd1 x
    (fun j => (hx.1 j).le) hact ?_ ?_ i r hr hmeet
  · apply (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg r)).trans
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  · intro p hp1 hpe
    have hpe' : p ≤ e := by dsimp [N] at hpe; omega
    dsimp only [N, Nat.succPNat_coe, x]
    rw [(InterpolationCoefficients.assembled_exterior_filters e a p hpe' y.val u).1]
    simpa only [Nat.cast_add, Nat.cast_one, σ] using (hgeom.2 p hp1 hpe').1
  · intro q hq1 hqe
    have hqe' : q ≤ e := by dsimp [N] at hqe; omega
    dsimp only [N, Nat.succPNat_coe, x]
    rw [(InterpolationCoefficients.assembled_exterior_filters e a q hqe' y.val u).2]
    simpa only [Nat.cast_add, Nat.cast_one, σ] using (hgeom.2 q hq1 hqe').2

/-- Internal image-sum step of Subsection 6.1: a rank lower
bound and the complementary distance control the physical coefficient. -/
theorem coefficient_rank_bound_internal (p : Parameters) (N : ℕ+)
    {c κ ε n r : ℝ} (hc : 0 < c) (hc' : c ≤ 1 / 8)
    (hκ : 0 ≤ κ) (hε : 0 ≤ ε) (hn : 1 ≤ n) (hr : 0 < r) (hrN : r ≤ N)
    (L : {L : ℝ // 0 < L ∧ L < (N : ℝ)})
    (hmass : c * n ^ (-κ * ε) * r ≤ L.val)
    (hcomp : (N : ℝ) / 8 ≤ (N : ℝ) - L.val) :
    PhysicalEnergy.intervalCoefficient p N L ≤
      (p.val.2 * (p.val.2 + 1) *
        PeriodicPower.bound (p.val.2 + 2) (by linarith [p.property.2.1]) *
          c ^ (-p.val.2 - 2)) * n ^ ((κ * (p.val.2 + 2)) * ε) * r ^ (-p.val.2 - 2) := by
  have hn0 : 0 < n := by linarith
  have hn' : n ^ (-κ * ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn (by nlinarith)
  have hδ : 0 < c * n ^ (-κ * ε) * r := by positivity
  have hδN : c * n ^ (-κ * ε) * r ≤ (N : ℝ) / 8 := by
    have h1 : c * n ^ (-κ * ε) ≤ 1 / 8 :=
      (mul_le_of_le_one_right hc.le hn').trans hc'
    have hh := mul_le_mul_of_nonneg_right h1 hr.le
    linarith
  have hh := PhysicalEnergy.intervalCoefficient_upper p N L hδ hmass (hδN.trans hcomp)
  have he : (c * n ^ (-κ * ε) * r) ^ (-p.val.2 - 2) =
      c ^ (-p.val.2 - 2) * n ^ ((κ * (p.val.2 + 2)) * ε) * r ^ (-p.val.2 - 2) := by
    rw [Real.mul_rpow (by positivity) hr.le,
      Real.mul_rpow hc.le (by positivity), ← Real.rpow_mul hn0.le]
    rw [show (-κ * ε) * (-p.val.2 - 2) = (κ * (p.val.2 + 2)) * ε by ring]
  rw [he] at hh
  simpa only [mul_assoc] using hh

/-- See Subsection 6.1 of the paper, uniform crossing coefficient profile.
The loss exponent and positive prefactor precede ε and temperature. Only
the size threshold depends on ε. Intervals wholly inside the active block
are included, since the hypothesis is merely that the interval meets it. -/
theorem physical_crossing_coefficient_bound (s K : ℝ) (hs : 0 < s) (hK : 0 ≤ K) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ ε : ℝ, 0 ≤ ε →
      min s 1 / 2 + 2 * ε < 1 → ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ (p : Parameters), p.val.2 = s → ∀ e a : ℕ,
      n₀ ≤ a + 1 → 4 * (a + 1) ≤ e + a + 1 →
      ∀ y : AffineSimplex.chartDomain e ((e + a : ℕ) + 1),
      InterpolantLocalLaws.exteriorGeometry s ε e a y.val →
      ∀ u : EuclideanSpace ℝ (Fin (a + 1)),
      u ∈ AffineSimplex.massSimplex a (((e + a : ℕ) + 1 : ℝ) - ∑ k, y.val k) →
      WithLp.ofLp u ∈ goodBlockEvent s a.succPNat (e + a).succPNat (K * ε) →
      ∀ (i : Fin (e + a + 1)) (r : ℕ), 0 < r → 2 * r ≤ e + a + 1 →
      (∃ j ∈ cyclicIndexInterval (e + a).succPNat i r, j.val < a + 1) →
      let x := WithLp.ofLp (RetainedSimplex.assemble e a
        (InterpolatingDensities.exteriorPermutation e a) y.val u)
      ∃ hL : 0 < cyclicGapSum (e + a).succPNat i r x ∧
          cyclicGapSum (e + a).succPNat i r x < ((e + a).succPNat : ℝ),
        PhysicalEnergy.intervalCoefficient p (e + a).succPNat
          ⟨cyclicGapSum (e + a).succPNat i r x, hL⟩ ≤
            C * (a + 1 : ℝ) ^ (κ * ε) * (r : ℝ) ^ (-s - 2) := by
  let σ := min s 1 / 2
  have hσ : σ < 1 := by dsimp [σ]; have := min_le_right s (1 : ℝ); linarith
  let b := 2 / (1 - σ)
  have hb : 0 < b := by dsimp [b]; positivity
  let c := 1 / (5 + 2 * (8 : ℝ) ^ b)
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by
    dsimp [c]
    apply (div_le_one (by positivity)).mpr
    have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 8) b
    linarith
  let κ := (K + b) * (s + 2)
  have hκ : 0 < κ := by dsimp [κ]; positivity
  let C := s * (s + 1) * PeriodicPower.bound (s + 2) (by linarith) * (c / 8) ^ (-s - 2)
  have hC : 0 < C := by
    have := PeriodicPower.bound_pos (s + 2) (by linarith)
    dsimp [C]
    positivity
  refine ⟨C, κ, hC, hκ, fun ε hε hε' => ?_⟩
  obtain ⟨n₀, hn₀, hcomp⟩ :=
    InterpolationCoefficients.physical_crossing_complement_lower s ε hs.le hε hε'
  refine ⟨n₀, hn₀, ?_⟩
  intro p hps e a hnn hsize y hgeom u hu hgood i r hr hrN hmeet x
  have hx := InterpolatingDensities.assemble_exterior_mem e a y u hu
  have hx' : x ∈ Riesz1.gapSimplex (e + a).succPNat :=
    ⟨hx.1, by simpa only [Nat.succPNat_coe, Nat.cast_succ] using hx.2⟩
  have hL := PhysicalEnergy.gapSum_mem (e + a).succPNat i hr (by
    change r < e + a + 1
    omega) x hx'
  refine ⟨hL, ?_⟩
  have hm := physical_crossing_rank_lower s K ε hs.le hK hε hε'.le
    e a (by omega) y hgeom u hu hgood i r (by omega) hmeet
  have hcc := hcomp e a hnn hsize y hgeom u hu i r hrN hmeet
  have hmass : (c / 8) * (a + 1 : ℝ) ^ (-(K + b) * ε) * r ≤
      cyclicGapSum (e + a).succPNat i r x := by
    apply le_trans _ hm
    change (c / 8) * (a + 1 : ℝ) ^ (-(K + b) * ε) * r ≤
      c * (a + 1 : ℝ) ^ (-(K + b) * ε) * r
    gcongr
    linarith
  have hh := coefficient_rank_bound_internal p (e + a).succPNat
    (by positivity : 0 < c / 8) (by linarith : c / 8 ≤ 1 / 8)
    (by positivity : 0 ≤ K + b) hε
    (by have := Nat.cast_nonneg (α := ℝ) a; linarith : (1 : ℝ) ≤ a + 1)
    (by exact_mod_cast hr) (by exact_mod_cast (show r ≤ e + a + 1 by omega))
    ⟨_, hL⟩ hmass (by simpa only [Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add] using hcc)
  simpa only [hps, C, κ] using hh

/-- Internal interval summation step of Subsection 6.1. A bound
is needed only for intervals that meet the active block. The resulting
matrix is the existing general active interval matrix. -/
theorem active_entry_bound_internal (N : ℕ+) (n : ℕ+)
    (hn : (n : ℕ) ≤ (N : ℕ)) (s B : ℝ) (hs : 0 < s) (hB : 0 ≤ B)
    (F : Fin (N : ℕ) × Fin ((N : ℕ) / 2) → ℝ)
    (hF : ∀ t, (∃ j ∈ cyclicIndexInterval N t.1 (t.2.val + 1), j.val < (n : ℕ)) →
      |F t| ≤ B * (t.2.val + 1 : ℝ) ^ (-s - 2))
    (a b : Fin (n : ℕ)) :
    |IntervalBoundary.intervalMatrix N n hn F a b| ≤
      B * (1 + 1 / s) *
        (1 + (Riesz1.cyclicIndexDistance N (a.castLE hn) (b.castLE hn) : ℝ)) ^ (-s) := by
  let G := fun (i : Fin (N : ℕ)) (r : Fin ((N : ℕ) / 2)) =>
    if a.castLE hn ∈ cyclicIndexInterval N i (r.val + 1) then F (i, r) else 0
  have hG (i) (r) : |G i r| ≤ B * (r.val + 1 : ℝ) ^ (-s - 2) := by
    dsimp only [G]
    split_ifs with h
    · exact hF (i, r) ⟨a.castLE hn, h, a.isLt⟩
    · simp only [abs_zero]
      positivity
  have hh := PhysicalCore.Internal.signed_interval_entry_bound N hs hB G hG
    (a.castLE hn) (b.castLE hn)
  apply le_trans (le_of_eq ?_) hh
  simp only [IntervalBoundary.intervalMatrix, Fintype.sum_prod_type,
    IntervalBoundary.rankOne, IntervalBoundary.trace, Finset.mem_filter,
    Finset.mem_univ, true_and]
  apply congrArg abs
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro r _
  dsimp only [G]
  split_ifs <;> simp_all

/-- See Subsection 6.1 of the paper, the full fixed-exterior physical entry
bound in both exponent regimes. This uses the literal physical coefficient
and antipodal multiplicity in the existing active interval matrix.
The loss and prefactor precede ε, temperature and both sizes. -/
theorem physical_interval_entry_bound (s K : ℝ) (hs : 0 < s) (hK : 0 ≤ K) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ ε : ℝ, 0 ≤ ε →
      min s 1 / 2 + 2 * ε < 1 → ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ (p : Parameters), p.val.2 = s → ∀ e a : ℕ,
      n₀ ≤ a + 1 → 4 * (a + 1) ≤ e + a + 1 →
      ∀ y : AffineSimplex.chartDomain e ((e + a : ℕ) + 1),
      InterpolantLocalLaws.exteriorGeometry s ε e a y.val →
      ∀ u : EuclideanSpace ℝ (Fin (a + 1)),
      u ∈ AffineSimplex.massSimplex a (((e + a : ℕ) + 1 : ℝ) - ∑ k, y.val k) →
      WithLp.ofLp u ∈ goodBlockEvent s a.succPNat (e + a).succPNat (K * ε) →
      let N := (e + a).succPNat
      let x := WithLp.ofLp (RetainedSimplex.assemble e a
        (InterpolatingDensities.exteriorPermutation e a) y.val u)
      ∃ H : ∀ t : Fin (e + a + 1) × Fin ((e + a + 1) / 2),
          0 < cyclicGapSum N t.1 (t.2.val + 1) x ∧
          cyclicGapSum N t.1 (t.2.val + 1) x < (N : ℝ),
      ∀ i j : Fin (a + 1),
        |IntervalBoundary.intervalMatrix N a.succPNat (by change a + 1 ≤ e + a + 1; omega)
          (fun t => (2 - if 2 * (t.2.val + 1) = e + a + 1 then (1 : ℝ) else 0) *
            PhysicalEnergy.intervalCoefficient p N
              ⟨cyclicGapSum N t.1 (t.2.val + 1) x, H t⟩) i j| ≤
        C * (a + 1 : ℝ) ^ (κ * ε) * (1 + (Nat.dist i.val j.val : ℝ)) ^ (-s) := by
  obtain ⟨C, κ, hC, hκ, hcoeff⟩ := physical_crossing_coefficient_bound s K hs hK
  refine ⟨2 * C * (1 + 1 / s), κ, by positivity, hκ, fun ε hε hε' => ?_⟩
  obtain ⟨n₀, hn₀, hh⟩ := hcoeff ε hε hε'
  refine ⟨n₀, hn₀, ?_⟩
  intro p hps e a hnn hsize y hgeom u hu hgood N x
  have hx := InterpolatingDensities.assemble_exterior_mem e a y u hu
  have hx' : x ∈ Riesz1.gapSimplex N :=
    ⟨hx.1, by simpa only [N, Nat.succPNat_coe, Nat.cast_succ] using hx.2⟩
  let H := fun t : Fin (e + a + 1) × Fin ((e + a + 1) / 2) =>
    PhysicalEnergy.gapSum_mem N t.1 (by omega : 0 < t.2.val + 1)
      (by change t.2.val + 1 < e + a + 1; have := t.2.isLt; omega) x hx'
  refine ⟨H, fun i j => ?_⟩
  let F := fun t : Fin (e + a + 1) × Fin ((e + a + 1) / 2) =>
    (2 - if 2 * (t.2.val + 1) = e + a + 1 then (1 : ℝ) else 0) *
      PhysicalEnergy.intervalCoefficient p N ⟨cyclicGapSum N t.1 (t.2.val + 1) x, H t⟩
  have hF (t) (hmeet : ∃ j ∈ cyclicIndexInterval N t.1 (t.2.val + 1), j.val < a + 1) :
      |F t| ≤ (2 * C * (a + 1 : ℝ) ^ (κ * ε)) * (t.2.val + 1 : ℝ) ^ (-s - 2) := by
    obtain ⟨hL, hb⟩ := hh p hps e a hnn hsize y hgeom u hu hgood
      t.1 (t.2.val + 1) (by omega) (by have := t.2.isLt; omega) hmeet
    have hc := (PhysicalEnergy.intervalCoefficient_pos p N
      ⟨cyclicGapSum N t.1 (t.2.val + 1) x, H t⟩).le
    change (PhysicalEnergy.intervalCoefficient p N
      ⟨cyclicGapSum N t.1 (t.2.val + 1) x, H t⟩) ≤ _ at hb
    dsimp only [F]
    split_ifs <;> norm_num only [sub_zero, sub_self, show (2 : ℝ) - 1 = 1 by norm_num,
      one_mul, abs_mul, abs_of_nonneg hc, abs_of_pos (by norm_num : (0 : ℝ) < 2)] <;>
      push_cast at hb ⊢ <;> nlinarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ a + 1) (κ * ε),
        Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ t.2.val + 1) (-s - 2)]
  have hb := active_entry_bound_internal N a.succPNat (by change a + 1 ≤ e + a + 1; omega)
    s (2 * C * (a + 1 : ℝ) ^ (κ * ε)) hs (by positivity) F hF i j
  have hd := PhysicalCore.Internal.active_distance N a.succPNat
    (by change 2 * (a + 1) ≤ e + a + 1; omega) i j
  rw [hd] at hb
  calc
    _ ≤ (2 * C * (a + 1 : ℝ) ^ (κ * ε)) * (1 + 1 / s) *
        (1 + (Nat.dist i.val j.val : ℝ)) ^ (-s) := hb
    _ = _ := by ring

/-- Internal boundary estimate for Subsection 6.1. Comparison with
the positive untruncated reference coefficients supplies all endpoint
bounds. The grouping and telescoping theorem then gives arbitrary
column increments. -/
theorem boundary_rank_profiles_internal (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ)),
      2 * (n : ℕ) ≤ (N : ℕ) → ∀ B : ℝ, 0 ≤ B →
      ∀ F : Fin (N : ℕ) × Fin ((N : ℕ) / 2) → ℝ,
      (∀ t, 0 ≤ F t) →
      (∀ t, F t ≤ B * (t.2.val + 1 : ℝ) ^ (-s.val - 2)) →
      (∀ i j : Fin (n : ℕ),
        |IntervalBoundary.boundaryMatrix N n hn F i j| ≤
          C * B * Real.log (2 * (n : ℝ)) *
            ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val / 2) *
            ((min (j.val + 1) ((n : ℕ) - j.val) : ℕ) : ℝ) ^ (-s.val / 2)) ∧
      (∀ i j l : Fin (n : ℕ),
        |IntervalBoundary.boundaryMatrix N n hn F i j -
          IntervalBoundary.boundaryMatrix N n hn F i l| ≤
          C * B * (Nat.dist j.val l.val : ℝ) *
            ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val / 2) *
            (min (((min (j.val + 1) ((n : ℕ) - j.val) : ℕ) : ℝ))
              (((min (l.val + 1) ((n : ℕ) - l.val) : ℕ) : ℝ))) ^ (-1 - s.val / 2)) := by
  obtain ⟨c, hc, href⟩ := PhysicalCore.referenceWeight_lower s
  obtain ⟨Cr, hCr, hr⟩ := BoundaryEntries.reference_endpoint_bounds s
  let Z := 5 / Real.log 2 + 4
  have hZ : 1 ≤ Z := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hdiv : 0 ≤ 5 / Real.log 2 := by positivity
    dsimp [Z]
    linarith
  refine ⟨Cr * Z / c, by have := hc; have := hCr; dsimp [Z]; positivity, ?_⟩
  intro N n hn hhalf B hB F hF0 hF
  have hN : 2 ≤ (N : ℕ) := by have := n.pos; omega
  let R := BoundaryEntries.referenceWeight s N hN 0
  let D := B / c
  have hD : 0 ≤ D := div_nonneg hB hc.le
  have hFR (t) : F t ≤ D * R t := by
    have hh := href N hN 0 t.1 t.2 (by omega)
    push_cast at hh
    have hscale := mul_le_mul_of_nonneg_left hh hD
    have he : D * c = B := by dsimp [D]; exact div_mul_cancel₀ _ hc.ne'
    rw [← mul_assoc, he] at hscale
    exact (hF t).trans hscale
  let U := fun b : Fin ((n : ℕ) - 1) =>
    IntervalBoundary.prefixCoefficient N n hn F (b.val + 1)
  let V := fun b : Fin ((n : ℕ) - 1) =>
    IntervalBoundary.suffixCoefficient N n hn F (b.val + 1)
  let d := IntervalBoundary.fullCoefficient N n hn F
  let S := BoundaryEntries.groupedBoundaryMatrix n U V d
  have hS : IntervalBoundary.boundaryMatrix N n hn F = S :=
    BoundaryEntries.boundaryMatrix_grouped_internal N n hn hhalf F
  have hU (b) : 0 ≤ U b := by
    apply Finset.sum_nonneg
    intro t _
    split_ifs <;> first | exact hF0 t | exact le_rfl
  have hV (b) : 0 ≤ V b := by
    apply Finset.sum_nonneg
    intro t _
    split_ifs <;> first | exact hF0 t | exact le_rfl
  have hd : 0 ≤ d := by
    apply Finset.sum_nonneg
    intro t _
    split_ifs <;> first | exact hF0 t | exact le_rfl
  have hprefix (b) : U b ≤ D * IntervalBoundary.prefixCoefficient N n hn R (b.val + 1) := by
    simp only [U, IntervalBoundary.prefixCoefficient]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t _
    split_ifs <;> first | exact hFR t | simp
  have hsuffix (b) : V b ≤ D * IntervalBoundary.suffixCoefficient N n hn R (b.val + 1) := by
    simp only [V, IntervalBoundary.suffixCoefficient]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t _
    split_ifs <;> first | exact hFR t | simp
  have hfull : d ≤ D * IntervalBoundary.fullCoefficient N n hn R := by
    simp only [d, IntervalBoundary.fullCoefficient]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t _
    split_ifs <;> first | exact hFR t | simp
  have hdiag (i) : S i i ≤ D * BoundaryEntries.referenceCrossing s N hN 0 n hn i i := by
    rw [← hS, BoundaryEntries.referenceCrossing_eq_boundaryMatrix s N hN 0 n hn]
    simp only [IntervalBoundary.boundaryMatrix]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t _
    by_cases ht : IntervalBoundary.IsInternal N n t
    · simp [ht]
    · simp only [ht, ↓reduceIte]
      have hh := mul_le_mul_of_nonneg_right (hFR t)
        (show 0 ≤ IntervalBoundary.rankOne (R := ℝ)
          (IntervalBoundary.trace N n hn t.1 (t.2.val + 1)) i i by
            unfold IntervalBoundary.rankOne; split_ifs <;> norm_num)
      simpa only [mul_assoc] using hh
  obtain ⟨he, _, hdiagR⟩ := hr N hN 0 n hn hhalf
  have hfullR := (hr N hN 0 n hn hhalf).2.1
  let E := D * Cr * Z
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hDC : D * Cr ≤ E := by
    dsimp [E]
    exact le_mul_of_one_le_right (mul_nonneg hD hCr.le) hZ
  have hends : BoundaryEntries.EndpointBounds s n E S U V d := by
    refine ⟨fun b => ⟨?_, ?_⟩, ?_, fun i => ?_⟩
    · apply (hprefix b).trans
      apply (mul_le_mul_of_nonneg_left (he b).1 hD).trans
      calc
        _ = (D * Cr) * (b.val + 1 : ℝ) ^ (-s.val) *
            ((min (b.val + 1) ((n : ℕ) - b.val) : ℕ) : ℝ)⁻¹ := by ring
        _ ≤ _ := by gcongr
    · have hbcast : (b.val + 1 : ℝ) ≤ n := by
        exact_mod_cast (show b.val + 1 ≤ (n : ℕ) by have := b.isLt; omega)
      have hbase : 0 ≤ (n : ℝ) - b.val - 1 := by linarith
      apply (hsuffix b).trans
      apply (mul_le_mul_of_nonneg_left (he b).2 hD).trans
      calc
        _ = (D * Cr) * ((n : ℝ) - b.val - 1) ^ (-s.val) *
            ((min (b.val + 2) ((n : ℕ) - (b.val + 1)) : ℕ) : ℝ)⁻¹ := by ring
        _ ≤ _ := by
          gcongr
    · apply hfull.trans
      apply (mul_le_mul_of_nonneg_left hfullR hD).trans
      calc
        _ = (D * Cr) * (n : ℝ) ^ (-s.val) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hDC (by positivity)
    · apply (hdiag i).trans
      have hh := mul_le_mul_of_nonneg_left (hdiagR i) hD
      convert hh using 1; dsimp [E, Z]; ring
  have hCE : E = Cr * Z / c * B := by dsimp [E, D]; ring
  constructor
  · intro i j
    rw [hS]
    have hh := BoundaryEntries.grouped_entry_bound_internal s n E hE U V d hU hV hd hends i j
    simpa only [hCE] using hh
  · intro i j l
    rw [hS]
    have hh := BoundaryEntries.grouped_increment_bound_internal s n E hE U V d hU hV hends i j l
    simpa only [hCE] using hh

/-- Internal restriction identity: intervals with empty active trace make
no contribution to the already defined boundary matrix. -/
theorem boundary_restrict_active_internal (N n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ))
    (F : Fin (N : ℕ) × Fin ((N : ℕ) / 2) → ℝ) :
    IntervalBoundary.boundaryMatrix N n hn
      (fun t => if ∃ j ∈ cyclicIndexInterval N t.1 (t.2.val + 1), j.val < (n : ℕ)
        then F t else 0) = IntervalBoundary.boundaryMatrix N n hn F := by
  ext i j
  apply Finset.sum_congr rfl
  intro t _
  by_cases hint : IntervalBoundary.IsInternal N n t
  · simp only [hint, ↓reduceIte]
  · simp only [hint, ↓reduceIte]
    by_cases hm : ∃ k ∈ cyclicIndexInterval N t.1 (t.2.val + 1), k.val < (n : ℕ)
    · simp only [hm, ↓reduceIte]
    · have hi : i ∉ IntervalBoundary.trace N n hn t.1 (t.2.val + 1) := by
        intro hi
        exact hm ⟨i.castLE hn, (Finset.mem_filter.mp hi).2, i.isLt⟩
      simp only [hm, ↓reduceIte, IntervalBoundary.rankOne, hi, false_and, mul_zero]

/-- See Subsection 6.1 of the paper, physical boundary entries and arbitrary
column increments for the long-range fixed-exterior Hessian. The matrix
is exactly its noninternal interval contribution. Its coefficient and
increment losses precede ε and temperature. The logarithm in the entry
profile is left explicit for the subsequent power-loss conversion. -/
theorem physical_boundary_profiles (s : Riesz1.RieszExponent) (K : ℝ) (hK : 0 ≤ K) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ ε : ℝ, 0 ≤ ε →
      s.val / 2 + 2 * ε < 1 → ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ (p : Parameters), p.val.2 = s.val → ∀ e a : ℕ,
      n₀ ≤ a + 1 → 4 * (a + 1) ≤ e + a + 1 →
      ∀ y : AffineSimplex.chartDomain e ((e + a : ℕ) + 1),
      InterpolantLocalLaws.exteriorGeometry s.val ε e a y.val →
      ∀ u : EuclideanSpace ℝ (Fin (a + 1)),
      u ∈ AffineSimplex.massSimplex a (((e + a : ℕ) + 1 : ℝ) - ∑ k, y.val k) →
      WithLp.ofLp u ∈ goodBlockEvent s.val a.succPNat (e + a).succPNat (K * ε) →
      let N := (e + a).succPNat
      let x := WithLp.ofLp (RetainedSimplex.assemble e a
        (InterpolatingDensities.exteriorPermutation e a) y.val u)
      ∃ H : ∀ t : Fin (e + a + 1) × Fin ((e + a + 1) / 2),
          0 < cyclicGapSum N t.1 (t.2.val + 1) x ∧
          cyclicGapSum N t.1 (t.2.val + 1) x < (N : ℝ),
      let P₂ := IntervalBoundary.boundaryMatrix N a.succPNat
        (by change a + 1 ≤ e + a + 1; omega)
        (fun t => (2 - if 2 * (t.2.val + 1) = e + a + 1 then (1 : ℝ) else 0) *
          PhysicalEnergy.intervalCoefficient p N
            ⟨cyclicGapSum N t.1 (t.2.val + 1) x, H t⟩)
      (∀ i j : Fin (a + 1), |P₂ i j| ≤
        C * (a + 1 : ℝ) ^ (κ * ε) * Real.log (2 * (a + 1 : ℝ)) *
          ((min (i.val + 1) (a + 1 - i.val) : ℕ) : ℝ) ^ (-s.val / 2) *
          ((min (j.val + 1) (a + 1 - j.val) : ℕ) : ℝ) ^ (-s.val / 2)) ∧
      (∀ i j l : Fin (a + 1), |P₂ i j - P₂ i l| ≤
        C * (a + 1 : ℝ) ^ (κ * ε) * (Nat.dist j.val l.val : ℝ) *
          ((min (i.val + 1) (a + 1 - i.val) : ℕ) : ℝ) ^ (-s.val / 2) *
          (min (((min (j.val + 1) (a + 1 - j.val) : ℕ) : ℝ))
            (((min (l.val + 1) (a + 1 - l.val) : ℕ) : ℝ))) ^ (-1 - s.val / 2)) := by
  obtain ⟨C, κ, hC, hκ, hcoeff⟩ := physical_crossing_coefficient_bound s.val K s.property.1 hK
  obtain ⟨D, hD, hprofiles⟩ := boundary_rank_profiles_internal s
  refine ⟨D * (2 * C), κ, by positivity, hκ, fun ε hε hε' => ?_⟩
  obtain ⟨n₀, hn₀, hh⟩ := hcoeff ε hε (by simpa only [min_eq_left s.property.2.le] using hε')
  refine ⟨n₀, hn₀, ?_⟩
  intro p hps e a hnn hsize y hgeom u hu hgood N x
  have hx := InterpolatingDensities.assemble_exterior_mem e a y u hu
  have hx' : x ∈ Riesz1.gapSimplex N :=
    ⟨hx.1, by simpa only [N, Nat.succPNat_coe, Nat.cast_succ] using hx.2⟩
  let H := fun t : Fin (e + a + 1) × Fin ((e + a + 1) / 2) =>
    PhysicalEnergy.gapSum_mem N t.1 (by omega : 0 < t.2.val + 1)
      (by change t.2.val + 1 < e + a + 1; have := t.2.isLt; omega) x hx'
  refine ⟨H, ?_⟩
  let F := fun t : Fin (e + a + 1) × Fin ((e + a + 1) / 2) =>
    (2 - if 2 * (t.2.val + 1) = e + a + 1 then (1 : ℝ) else 0) *
      PhysicalEnergy.intervalCoefficient p N ⟨cyclicGapSum N t.1 (t.2.val + 1) x, H t⟩
  let G := fun t => if ∃ j ∈ cyclicIndexInterval N t.1 (t.2.val + 1), j.val < a + 1
    then F t else 0
  have hF0 (t) : 0 ≤ F t := by
    have hc := (PhysicalEnergy.intervalCoefficient_pos p N
      ⟨cyclicGapSum N t.1 (t.2.val + 1) x, H t⟩).le
    dsimp [F]
    split_ifs <;> norm_num <;> positivity
  have hG0 (t) : 0 ≤ G t := by dsimp [G]; split_ifs; exact hF0 t; exact le_rfl
  have hG (t) : G t ≤ (2 * C * (a + 1 : ℝ) ^ (κ * ε)) *
      (t.2.val + 1 : ℝ) ^ (-s.val - 2) := by
    dsimp only [G]
    split_ifs with hmeet
    · obtain ⟨hL, hb⟩ := hh p hps e a hnn hsize y hgeom u hu hgood
        t.1 (t.2.val + 1) (by omega) (by have := t.2.isLt; omega) hmeet
      change PhysicalEnergy.intervalCoefficient p N
        ⟨cyclicGapSum N t.1 (t.2.val + 1) x, H t⟩ ≤ _ at hb
      have hc := (PhysicalEnergy.intervalCoefficient_pos p N
        ⟨cyclicGapSum N t.1 (t.2.val + 1) x, H t⟩).le
      dsimp only [F]
      split_ifs <;> norm_num only [sub_zero, show (2 : ℝ) - 1 = 1 by norm_num, one_mul] <;>
        push_cast at hb ⊢ <;> nlinarith
    · positivity
  have hp := hprofiles N a.succPNat (by change a + 1 ≤ e + a + 1; omega)
    (by change 2 * (a + 1) ≤ e + a + 1; omega)
    (2 * C * (a + 1 : ℝ) ^ (κ * ε)) (by positivity) G hG0 hG
  have hrestrict := boundary_restrict_active_internal N a.succPNat
    (by change a + 1 ≤ e + a + 1; omega) F
  change IntervalBoundary.boundaryMatrix N a.succPNat _ G = _ at hrestrict
  rw [hrestrict] at hp
  constructor
  · intro i j
    convert hp.1 i j using 1 <;>
      simp only [F, Nat.succPNat_coe, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] <;>
      first | rfl | ring
  · intro i j l
    convert hp.2 i j l using 1 <;>
      simp only [F, Nat.succPNat_coe, Nat.succ_eq_add_one] <;>
      first | rfl | ring

/-- See Subsection 6.1 of the paper: the physical crossing block has the
required entry and increment power bounds. The loss exponent is chosen
before ε. The positive prefactor precedes temperature and every size. -/
theorem physical_boundary_power_profiles (s : Riesz1.RieszExponent) (K : ℝ) (hK : 0 ≤ K) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε →
      s.val / 2 + 2 * ε < 1 → ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ (p : Parameters), p.val.2 = s.val → ∀ e a : ℕ,
      n₀ ≤ a + 1 → 4 * (a + 1) ≤ e + a + 1 →
      ∀ y : AffineSimplex.chartDomain e ((e + a : ℕ) + 1),
      InterpolantLocalLaws.exteriorGeometry s.val ε e a y.val →
      ∀ u : EuclideanSpace ℝ (Fin (a + 1)),
      u ∈ AffineSimplex.massSimplex a (((e + a : ℕ) + 1 : ℝ) - ∑ k, y.val k) →
      WithLp.ofLp u ∈ goodBlockEvent s.val a.succPNat (e + a).succPNat (K * ε) →
      let N := (e + a).succPNat
      let x := WithLp.ofLp (RetainedSimplex.assemble e a
        (InterpolatingDensities.exteriorPermutation e a) y.val u)
      ∃ H : ∀ t : Fin (e + a + 1) × Fin ((e + a + 1) / 2),
          0 < cyclicGapSum N t.1 (t.2.val + 1) x ∧
          cyclicGapSum N t.1 (t.2.val + 1) x < (N : ℝ),
      let P₂ := IntervalBoundary.boundaryMatrix N a.succPNat
        (by change a + 1 ≤ e + a + 1; omega)
        (fun t => (2 - if 2 * (t.2.val + 1) = e + a + 1 then (1 : ℝ) else 0) *
          PhysicalEnergy.intervalCoefficient p N
            ⟨cyclicGapSum N t.1 (t.2.val + 1) x, H t⟩)
      (∀ i j : Fin (a + 1), |P₂ i j| ≤
        C * (a + 1 : ℝ) ^ (κ * ε) *
          ((min (i.val + 1) (a + 1 - i.val) : ℕ) : ℝ) ^ (-s.val / 2) *
          ((min (j.val + 1) (a + 1 - j.val) : ℕ) : ℝ) ^ (-s.val / 2)) ∧
      (∀ i j l : Fin (a + 1), |P₂ i j - P₂ i l| ≤
        C * (a + 1 : ℝ) ^ (κ * ε) * (Nat.dist j.val l.val : ℝ) *
          ((min (i.val + 1) (a + 1 - i.val) : ℕ) : ℝ) ^ (-s.val / 2) *
          (min (((min (j.val + 1) (a + 1 - j.val) : ℕ) : ℝ))
            (((min (l.val + 1) (a + 1 - l.val) : ℕ) : ℝ))) ^ (-1 - s.val / 2)) := by
  obtain ⟨C, κ, hC, hκ, hprofile⟩ := physical_boundary_profiles s K hK
  refine ⟨κ + 1, by linarith, fun ε hε hε' => ?_⟩
  obtain ⟨n₀, hn₀, hp⟩ := hprofile ε hε.le hε'
  let A := 1 + Real.log 2 + 1 / ε
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 1 ≤ A := by
    have hi : 0 ≤ 1 / ε := by positivity
    dsimp [A]
    linarith
  have hA0 : 0 < A := by linarith
  refine ⟨C * A, by positivity, n₀, hn₀, ?_⟩
  intro p hps e a hnn hsize y hgeom u hu hgood N x
  obtain ⟨H, hends⟩ := hp p hps e a hnn hsize y hgeom u hu hgood
  refine ⟨H, ?_⟩
  have hn0 : (0 : ℝ) < a + 1 := by positivity
  have hn1 : (1 : ℝ) ≤ a + 1 := by have := Nat.cast_nonneg (α := ℝ) a; linarith
  have hnε : 1 ≤ (a + 1 : ℝ) ^ ε := Real.one_le_rpow hn1 hε.le
  have hlog : Real.log (2 * (a + 1 : ℝ)) ≤ A * (a + 1 : ℝ) ^ ε := by
    have hh := Real.log_le_rpow_div hn0.le hε
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0.ne']
    dsimp only [A]
    rw [div_eq_mul_inv] at hh ⊢
    nlinarith [mul_le_mul_of_nonneg_left hnε hlog2.le]
  have hpow : (a + 1 : ℝ) ^ (κ * ε) * (a + 1 : ℝ) ^ ε =
      (a + 1 : ℝ) ^ ((κ + 1) * ε) := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  have hfac : C * (a + 1 : ℝ) ^ (κ * ε) * Real.log (2 * (a + 1 : ℝ)) ≤
      C * A * (a + 1 : ℝ) ^ ((κ + 1) * ε) := by
    calc
      _ ≤ C * (a + 1 : ℝ) ^ (κ * ε) * (A * (a + 1 : ℝ) ^ ε) := by gcongr
      _ = _ := by rw [← hpow]; ring
  have hfac' : C * (a + 1 : ℝ) ^ (κ * ε) ≤
      C * A * (a + 1 : ℝ) ^ ((κ + 1) * ε) := by
    have hh : (a + 1 : ℝ) ^ (κ * ε) ≤ (a + 1 : ℝ) ^ ((κ + 1) * ε) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    calc
      _ ≤ C * (a + 1 : ℝ) ^ ((κ + 1) * ε) := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_right hC.le hA) (by positivity)
  constructor
  · intro i j
    apply (hends.1 i j).trans
    gcongr
  · intro i j l
    apply (hends.2 i j l).trans
    gcongr

/-- Internal finite identity for Subsection 6.1: the general
interval matrix evaluated at basis vectors is its cyclic-sum expansion. -/
theorem intervalMatrix_coefficient_sum_internal (N n : ℕ+)
    (hn : (n : ℕ) ≤ (N : ℕ))
    (F : Fin (N : ℕ) × Fin ((N : ℕ) / 2) → ℝ) (i j : Fin (n : ℕ)) :
    IntervalBoundary.intervalMatrix N n hn F i j =
      ∑ a : Fin (N : ℕ), ∑ r : Fin ((N : ℕ) / 2),
        F (a, r) * (cyclicGapSum N a (r.val + 1) (Pi.single (i.castLE hn) 1) *
          cyclicGapSum N a (r.val + 1) (Pi.single (j.castLE hn) 1)) := by
  simp only [IntervalBoundary.intervalMatrix, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro r _
  have hsingle (b : Fin (N : ℕ)) : (Pi.single b (1 : ℝ) : Fin (N : ℕ) → ℝ) =
      (fun k => if k = b then (1 : ℝ) else 0) := by
    funext k
    simp [Pi.single_apply, eq_comm]
  rw [hsingle, hsingle,
    cyclicGapSum_single N a (i.castLE hn) (by have := r.isLt; omega),
    cyclicGapSum_single N a (j.castLE hn) (by have := r.isLt; omega)]
  simp only [IntervalBoundary.rankOne, IntervalBoundary.trace,
    Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hi : i.castLE hn ∈ cyclicIndexInterval N a (r.val + 1) <;>
    by_cases hj : j.castLE hn ∈ cyclicIndexInterval N a (r.val + 1) <;>
    simp only [hi, hj, and_self, and_false, false_and, ↓reduceIte, mul_zero, mul_one]

/-- See Subsection 6.1 of the paper: the coefficient matrix in the
estimates above is exactly the active block of the Hessian of a smooth
realization of the short-interval ambient energy. This holds in
both exponent regimes on its entire ambient carrier. -/
theorem ambient_hessian_intervalMatrix_internal (p : Parameters) (N : ℕ+) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ x : {x : EuclideanSpace ℝ (Fin (N : ℕ)) // x ∈ gapAmbientDomain N},
        W x.val = physicalAmbientGapEnergy p N x) ∧
      ∀ (x : {x : EuclideanSpace ℝ (Fin (N : ℕ)) // x ∈ gapAmbientDomain N})
        (n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ)) (i j : Fin (n : ℕ)),
        fderiv ℝ (fderiv ℝ W) x.val
          (WithLp.toLp 2 (Pi.single (i.castLE hn) 1))
          (WithLp.toLp 2 (Pi.single (j.castLE hn) 1)) =
        IntervalBoundary.intervalMatrix N n hn
          (fun t => (2 - if 2 * (t.2.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
            PhysicalEnergy.intervalCoefficient p N
              ⟨cyclicGapSum N t.1 (t.2.val + 1) (WithLp.ofLp x.val),
                x.property t.1 (t.2.val + 1) (by omega) (by have := t.2.isLt; omega)⟩) i j := by
  obtain ⟨W, hWs, hWv, hd⟩ := PhysicalEnergy.ambient_derivatives p N
  refine ⟨W, hWs, hWv, fun x n hn i j => ?_⟩
  rw [intervalMatrix_coefficient_sum_internal]
  exact (hd x (WithLp.toLp 2 (Pi.single (i.castLE hn) 1))
    (WithLp.toLp 2 (Pi.single (j.castLE hn) 1))).2

/-- Internal scalar interpolation step for Subsection 6.1. -/
theorem convex_abs_le_internal {a b W t : ℝ} (ha : |a| ≤ W) (hb : |b| ≤ W)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : |(1 - t) * a + t * b| ≤ W := by
  calc
    _ ≤ |(1 - t) * a| + |t * b| := abs_add_le _ _
    _ = (1 - t) * |a| + t * |b| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr ht.2), abs_of_nonneg ht.1]
    _ ≤ (1 - t) * W + t * W := add_le_add
      (mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr ht.2))
      (mul_le_mul_of_nonneg_left hb ht.1)
    _ = W := by ring

/-- Internal interpolation step of Subsection 6.1. Both physical
endpoint matrices may have different exterior volumes. A common entry
majorant and a common increment majorant survive the actual convex
interpolation with no change of constants. -/
theorem convex_matrix_profiles_internal {ι : Type*} (P Q : Matrix ι ι ℝ)
    (E : ι → ι → ℝ) (D : ι → ι → ι → ℝ)
    (hPE : ∀ i j, |P i j| ≤ E i j) (hQE : ∀ i j, |Q i j| ≤ E i j)
    (hPD : ∀ i j l, |P i j - P i l| ≤ D i j l)
    (hQD : ∀ i j l, |Q i j - Q i l| ≤ D i j l)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∀ i j, |((1 - t) • P + t • Q) i j| ≤ E i j) ∧
    (∀ i j l, |((1 - t) • P + t • Q) i j -
      ((1 - t) • P + t • Q) i l| ≤ D i j l) := by
  have hconv {a b W : ℝ} (ha : |a| ≤ W) (hb : |b| ≤ W) :
      |(1 - t) * a + t * b| ≤ W := convex_abs_le_internal ha hb ht
  constructor
  · intro i j
    exact hconv (hPE i j) (hQE i j)
  · intro i j l
    have hh := hconv (hPD i j l) (hQD i j l)
    convert hh using 1
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    congr 1
    ring

/-- See Subsection 6.1 of the paper, entry bound for the actual convex
interpolation of the two fixed-exterior physical matrices, in both
exponent regimes. The active point lies on their common mass simplex. -/
theorem physical_interpolant_entry_bound (s K : ℝ) (hs : 0 < s) (hK : 0 ≤ K) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ ε : ℝ, 0 ≤ ε →
      min s 1 / 2 + 2 * ε < 1 → ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ (p : Parameters), p.val.2 = s → ∀ e d a : ℕ,
      e ≤ d → n₀ ≤ a + 1 → 4 * (a + 1) ≤ e + a + 1 →
      ∀ y : AffineSimplex.chartDomain e ((e + a : ℕ) + 1),
      ∀ z : AffineSimplex.chartDomain d ((d + a : ℕ) + 1),
      InterpolantLocalLaws.exteriorGeometry s ε e a y.val →
      InterpolantLocalLaws.exteriorGeometry s ε d a z.val →
      ∀ u : EuclideanSpace ℝ (Fin (a + 1)),
      u ∈ AffineSimplex.massSimplex a (((e + a : ℕ) + 1 : ℝ) - ∑ k, y.val k) →
      u ∈ AffineSimplex.massSimplex a (((d + a : ℕ) + 1 : ℝ) - ∑ k, z.val k) →
      WithLp.ofLp u ∈ goodBlockEvent s a.succPNat (e + a).succPNat (K * ε) →
      let N := (e + a).succPNat
      let M := (d + a).succPNat
      let x := WithLp.ofLp (RetainedSimplex.assemble e a
        (InterpolatingDensities.exteriorPermutation e a) y.val u)
      let v := WithLp.ofLp (RetainedSimplex.assemble d a
        (InterpolatingDensities.exteriorPermutation d a) z.val u)
      ∃ H : ∀ t : Fin (e + a + 1) × Fin ((e + a + 1) / 2),
          0 < cyclicGapSum N t.1 (t.2.val + 1) x ∧
          cyclicGapSum N t.1 (t.2.val + 1) x < (N : ℝ),
      ∃ J : ∀ t : Fin (d + a + 1) × Fin ((d + a + 1) / 2),
          0 < cyclicGapSum M t.1 (t.2.val + 1) v ∧
          cyclicGapSum M t.1 (t.2.val + 1) v < (M : ℝ),
      let Py := IntervalBoundary.intervalMatrix N a.succPNat
        (by change a + 1 ≤ e + a + 1; omega)
        (fun t => (2 - if 2 * (t.2.val + 1) = e + a + 1 then (1 : ℝ) else 0) *
          PhysicalEnergy.intervalCoefficient p N ⟨cyclicGapSum N t.1 (t.2.val + 1) x, H t⟩)
      let Pz := IntervalBoundary.intervalMatrix M a.succPNat
        (by change a + 1 ≤ d + a + 1; omega)
        (fun t => (2 - if 2 * (t.2.val + 1) = d + a + 1 then (1 : ℝ) else 0) *
          PhysicalEnergy.intervalCoefficient p M ⟨cyclicGapSum M t.1 (t.2.val + 1) v, J t⟩)
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i j : Fin (a + 1),
        |((1 - t) • Py + t • Pz) i j| ≤
          C * (a + 1 : ℝ) ^ (κ * ε) * (1 + (Nat.dist i.val j.val : ℝ)) ^ (-s) := by
  obtain ⟨C, κ, hC, hκ, hentry⟩ := physical_interval_entry_bound s K hs hK
  refine ⟨C, κ, hC, hκ, fun ε hε hε' => ?_⟩
  obtain ⟨n₀, hn₀, hp⟩ := hentry ε hε hε'
  refine ⟨n₀, hn₀, ?_⟩
  intro p hps e d a hed hnn hsize y z hgy hgz u huy huz hgood N M x v
  have hNM : (N : ℝ) ≤ M := by
    dsimp only [N, M, Nat.succPNat_coe]
    exact_mod_cast (show e + a + 1 ≤ d + a + 1 by omega)
  have hgoodz : WithLp.ofLp u ∈ goodBlockEvent s a.succPNat M (K * ε) :=
    ⟨hgood.1.trans_le hNM, hgood.2⟩
  obtain ⟨H, hy⟩ := hp p hps e a hnn hsize y hgy u huy hgood
  obtain ⟨J, hz⟩ := hp p hps d a hnn (by omega) z hgz u huz hgoodz
  refine ⟨H, J, fun t ht i j => ?_⟩
  exact convex_abs_le_internal (hy i j) (hz i j) ht

/-- See Subsection 6.1 of the paper: the actual interpolated crossing block
has both required boundary power profiles. The structural exponent is
chosen before ε, and the prefactor and threshold before temperature,
periods and exteriors. -/
theorem physical_interpolant_boundary_profiles (s : Riesz1.RieszExponent)
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → s.val / 2 + 2 * ε < 1 →
      ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ (p : Parameters), p.val.2 = s.val → ∀ e d a : ℕ,
      e ≤ d → n₀ ≤ a + 1 → 4 * (a + 1) ≤ e + a + 1 →
      ∀ y : AffineSimplex.chartDomain e ((e + a : ℕ) + 1),
      ∀ z : AffineSimplex.chartDomain d ((d + a : ℕ) + 1),
      InterpolantLocalLaws.exteriorGeometry s.val ε e a y.val →
      InterpolantLocalLaws.exteriorGeometry s.val ε d a z.val →
      ∀ u : EuclideanSpace ℝ (Fin (a + 1)),
      u ∈ AffineSimplex.massSimplex a (((e + a : ℕ) + 1 : ℝ) - ∑ k, y.val k) →
      u ∈ AffineSimplex.massSimplex a (((d + a : ℕ) + 1 : ℝ) - ∑ k, z.val k) →
      WithLp.ofLp u ∈ goodBlockEvent s.val a.succPNat (e + a).succPNat (K * ε) →
      let N := (e + a).succPNat
      let M := (d + a).succPNat
      let x := WithLp.ofLp (RetainedSimplex.assemble e a
        (InterpolatingDensities.exteriorPermutation e a) y.val u)
      let v := WithLp.ofLp (RetainedSimplex.assemble d a
        (InterpolatingDensities.exteriorPermutation d a) z.val u)
      ∃ H : ∀ t : Fin (e + a + 1) × Fin ((e + a + 1) / 2),
          0 < cyclicGapSum N t.1 (t.2.val + 1) x ∧
          cyclicGapSum N t.1 (t.2.val + 1) x < (N : ℝ),
      ∃ J : ∀ t : Fin (d + a + 1) × Fin ((d + a + 1) / 2),
          0 < cyclicGapSum M t.1 (t.2.val + 1) v ∧
          cyclicGapSum M t.1 (t.2.val + 1) v < (M : ℝ),
      let Py := IntervalBoundary.boundaryMatrix N a.succPNat
        (by change a + 1 ≤ e + a + 1; omega)
        (fun t => (2 - if 2 * (t.2.val + 1) = e + a + 1 then (1 : ℝ) else 0) *
          PhysicalEnergy.intervalCoefficient p N ⟨cyclicGapSum N t.1 (t.2.val + 1) x, H t⟩)
      let Pz := IntervalBoundary.boundaryMatrix M a.succPNat
        (by change a + 1 ≤ d + a + 1; omega)
        (fun t => (2 - if 2 * (t.2.val + 1) = d + a + 1 then (1 : ℝ) else 0) *
          PhysicalEnergy.intervalCoefficient p M ⟨cyclicGapSum M t.1 (t.2.val + 1) v, J t⟩)
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
      let P₂ := (1 - t) • Py + t • Pz
      (∀ i j : Fin (a + 1), |P₂ i j| ≤
        C * (a + 1 : ℝ) ^ (κ * ε) *
          ((min (i.val + 1) (a + 1 - i.val) : ℕ) : ℝ) ^ (-s.val / 2) *
          ((min (j.val + 1) (a + 1 - j.val) : ℕ) : ℝ) ^ (-s.val / 2)) ∧
      (∀ i j l : Fin (a + 1), |P₂ i j - P₂ i l| ≤
        C * (a + 1 : ℝ) ^ (κ * ε) * (Nat.dist j.val l.val : ℝ) *
          ((min (i.val + 1) (a + 1 - i.val) : ℕ) : ℝ) ^ (-s.val / 2) *
          (min (((min (j.val + 1) (a + 1 - j.val) : ℕ) : ℝ))
            (((min (l.val + 1) (a + 1 - l.val) : ℕ) : ℝ))) ^ (-1 - s.val / 2)) := by
  obtain ⟨κ, hκ, hprofile⟩ := physical_boundary_power_profiles s K hK
  refine ⟨κ, hκ, fun ε hε hε' => ?_⟩
  obtain ⟨C, hC, n₀, hn₀, hp⟩ := hprofile ε hε hε'
  refine ⟨C, hC, n₀, hn₀, ?_⟩
  intro p hps e d a hed hnn hsize y z hgy hgz u huy huz hgood N M x v
  have hNM : (N : ℝ) ≤ M := by
    dsimp only [N, M, Nat.succPNat_coe]
    exact_mod_cast (show e + a + 1 ≤ d + a + 1 by omega)
  have hgoodz : WithLp.ofLp u ∈ goodBlockEvent s.val a.succPNat M (K * ε) :=
    ⟨hgood.1.trans_le hNM, hgood.2⟩
  obtain ⟨H, hy⟩ := hp p hps e a hnn hsize y hgy u huy hgood
  obtain ⟨J, hz⟩ := hp p hps d a hnn (by omega) z hgz u huz hgoodz
  refine ⟨H, J, fun t ht => ?_⟩
  exact convex_matrix_profiles_internal _ _ _ _ hy.1 hz.1 hy.2 hz.2 t ht

end Riesz2.CrossingCoefficients
