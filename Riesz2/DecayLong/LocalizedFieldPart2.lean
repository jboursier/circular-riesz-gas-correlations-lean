/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.LocalizedField

/-!
# Geometry of centered exterior rows

Supporting estimates for the proof of Proposition 5.15, using the actual
window and its ordered embedding from Subsection 5.5.
-/

@[expose] public section
noncomputable section

open MeasureTheory Finset
open Riesz2.GlobalReferenceErrorInternal
open scoped BigOperators Classical Fin.NatCast

namespace Riesz2.LocalizedField

/-- See the proof of Proposition 5.15 in the paper: the distance from a label in an initial
block to any exterior label is at least its distance to the nearer endpoint. -/
theorem initial_block_exterior_distance (m : ℕ+) {n : ℕ}
    (hn : n ≤ (m : ℕ)) (l : Fin n) (i : Fin (m : ℕ)) (hi : n ≤ i.val) :
    min (l.val + 1) (n - l.val) ≤
      Riesz1.cyclicIndexDistance m (l.castLE hn) i := by
  have hl := l.isLt
  have him := i.isLt
  simp only [Riesz1.cyclicIndexDistance, Fin.val_castLE, Nat.dist]
  omega

/-- See the proof of Proposition 5.15 in the paper: the complement of the actual window
is exactly the exterior of its translated initial block. -/
theorem not_mem_window_iff_offset (m : ℕ+) (j i₀ i : Fin (m : ℕ)) :
    i ∉ LocalizedMatrix.window m j i₀ ↔
      (LocalizedMatrix.windowSize m j i₀ : ℕ) ≤
        (i - (j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ)))).val := by
  rw [LocalizedMatrix.window_eq_cyclicIndexInterval,
    mem_cyclicIndexInterval_iff m _ _ (by
      rw [← LocalizedMatrix.window_card m j i₀]
      simpa only [Fintype.card_fin] using (card_le_univ (LocalizedMatrix.window m j i₀)))]
  rw [← LocalizedMatrix.window_card m j i₀]
  exact not_lt

/-- See the proof of Proposition 5.15 in the paper: the endpoint lower bound is derived
for the actual embedding and complement, from the window geometry. -/
theorem window_exterior_distance (m : ℕ+) (j i₀ : Fin (m : ℕ))
    (l : Fin (LocalizedMatrix.windowSize m j i₀ : ℕ))
    (i : Fin (m : ℕ)) (hi : i ∉ LocalizedMatrix.window m j i₀) :
    min (l.val + 1) ((LocalizedMatrix.windowSize m j i₀ : ℕ) - l.val) ≤
      Riesz1.cyclicIndexDistance m (LocalizedMatrix.windowEmbedding m j i₀ l) i := by
  have hn : (LocalizedMatrix.windowSize m j i₀ : ℕ) ≤ (m : ℕ) := by
    change (LocalizedMatrix.window m j i₀).card ≤ (m : ℕ)
    simpa only [Fintype.card_fin] using (card_le_univ (LocalizedMatrix.window m j i₀))
  let start := j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ))
  have he := initial_block_exterior_distance m hn l (i - start)
    ((not_mem_window_iff_offset m j i₀ i).mp hi)
  rw [LocalizedMatrix.windowEmbedding_apply m j i₀ l hn]
  have ht := LocalizedMatrix.distance_add m (l.castLE hn) (i - start) start
  rw [sub_add_cancel] at ht
  simpa only [add_comm] using he.trans_eq ht.symm

/-- See the proof of Proposition 5.15 in the paper: ordered adjacent labels remain
adjacent in the parent cycle, including when the window crosses its seam. -/
theorem windowEmbedding_predecessor (m : ℕ+) (j i₀ : Fin (m : ℕ))
    (l : Fin (LocalizedMatrix.windowSize m j i₀ : ℕ)) (hl : 0 < l.val) :
    LocalizedMatrix.windowEmbedding m j i₀
      ⟨l.val - 1, by have := l.isLt; omega⟩ =
        LocalizedMatrix.windowEmbedding m j i₀ l - 1 := by
  have hn : (LocalizedMatrix.windowSize m j i₀ : ℕ) ≤ (m : ℕ) := by
    change (LocalizedMatrix.window m j i₀).card ≤ (m : ℕ)
    simpa only [Fintype.card_fin] using (card_le_univ (LocalizedMatrix.window m j i₀))
  rw [LocalizedMatrix.windowEmbedding_apply m j i₀ _ hn,
    LocalizedMatrix.windowEmbedding_apply m j i₀ _ hn]
  have he : (Fin.castLE hn ⟨l.val - 1, by have := l.isLt; omega⟩ : Fin (m : ℕ)) =
      l.castLE hn - 1 := by
    apply Fin.ext
    rw [Fin.val_sub, Fin.val_castLE]
    have hm : 1 < (m : ℕ) := by have := l.isLt; omega
    have hone : (1 : Fin (m : ℕ)).val = 1 := by
      change 1 % (m : ℕ) = 1
      exact Nat.mod_eq_of_lt hm
    rw [hone]
    change l.val - 1 = ((m : ℕ) - 1 + l.val) % (m : ℕ)
    have := l.isLt
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  rw [he]
  abel

/-- See the proof of Proposition 5.15 in the paper: parent separation and upper radius
bounds for every actual local label. -/
theorem window_source_radius (m : ℕ+) (j i₀ : Fin (m : ℕ))
    (hR : 16 ≤ Riesz1.cyclicIndexDistance m j i₀)
    (l : Fin (LocalizedMatrix.windowSize m j i₀ : ℕ)) :
    (Riesz1.cyclicIndexDistance m j i₀ : ℝ) / 2 ≤
        weightRadius m (LocalizedMatrix.windowEmbedding m j i₀ l) i₀ ∧
      weightRadius m (LocalizedMatrix.windowEmbedding m j i₀ l) i₀ ≤
        2 * (Riesz1.cyclicIndexDistance m j i₀ : ℝ) := by
  have hl : LocalizedMatrix.windowEmbedding m j i₀ l ∈ LocalizedMatrix.window m j i₀ :=
    (LocalizedMatrix.mem_window_iff_exists_embedding m j i₀ _).mpr ⟨l, rfl⟩
  have hlow := LocalizedMatrix.window_separation m j i₀ _ hl
  have hnear := (LocalizedMatrix.mem_window_iff m j i₀ _).mp hl
  have htri := cyclicIndexDistance_triangle (LocalizedMatrix.windowEmbedding m j i₀ l) j i₀
  have htri' : (Riesz1.cyclicIndexDistance m (LocalizedMatrix.windowEmbedding m j i₀ l) i₀ : ℝ) ≤
      (Riesz1.cyclicIndexDistance m (LocalizedMatrix.windowEmbedding m j i₀ l) j : ℝ) +
        (Riesz1.cyclicIndexDistance m j i₀ : ℝ) := by exact_mod_cast htri
  have hlow' : 7 * (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ≤
      8 * (Riesz1.cyclicIndexDistance m (LocalizedMatrix.windowEmbedding m j i₀ l) i₀ : ℝ) :=
    by exact_mod_cast hlow
  have hR' : (16 : ℝ) ≤ Riesz1.cyclicIndexDistance m j i₀ := by exact_mod_cast hR
  dsimp only [weightRadius]
  constructor <;> linarith

/-- See the proof of Proposition 5.15 in the paper: near-source labels satisfy the
short-arc hypothesis of the column oscillation estimate. -/
theorem window_near_source_arc (m : ℕ+) (j i₀ : Fin (m : ℕ))
    (hR : 16 ≤ Riesz1.cyclicIndexDistance m j i₀)
    (l : Fin (LocalizedMatrix.windowSize m j i₀ : ℕ)) (i : Fin (m : ℕ))
    (hi : weightRadius m i i₀ ≤ (Riesz1.cyclicIndexDistance m j i₀ : ℝ) / 4) :
    (Riesz1.cyclicIndexDistance m i₀ i : ℝ) ≤
      weightRadius m i₀ (LocalizedMatrix.windowEmbedding m j i₀ l) / 2 := by
  have hl := (window_source_radius m j i₀ hR l).1
  dsimp only [weightRadius] at hi hl ⊢
  rw [cyclicIndexDistance_comm' m i₀ i,
    cyclicIndexDistance_comm' m i₀ (LocalizedMatrix.windowEmbedding m j i₀ l)]
  linarith

/-- See the proof of Proposition 5.15 in the paper: beyond four row-source radii the
two distance weights are comparable, so their powers can be summed together. -/
theorem far_radius_comparison (m : ℕ+) (l i₀ i : Fin (m : ℕ)) (R : ℝ)
    (hl : weightRadius m l i₀ ≤ 2 * R) (hi : 4 * R ≤ weightRadius m i l) :
    weightRadius m i l / 2 ≤ weightRadius m i i₀ := by
  have ht := cyclicIndexDistance_triangle i i₀ l
  have ht' : (Riesz1.cyclicIndexDistance m i l : ℝ) ≤
      (Riesz1.cyclicIndexDistance m i i₀ : ℝ) +
        (Riesz1.cyclicIndexDistance m i₀ l : ℝ) := by exact_mod_cast ht
  rw [weightRadius_eq_comm] at hl
  dsimp only [weightRadius] at hl hi ⊢
  linarith

/-- See the proof of Proposition 5.15 in the paper: summing any real power on an annulus
costs at most two copies of the corresponding integer power sum. -/
theorem annulus_power_sum (m : ℕ+) (l : Fin (m : ℕ)) (δ H : ℕ) (t : ℝ)
    (S : Finset (Fin (m : ℕ)))
    (hS : ∀ i ∈ S, δ ≤ 1 + Riesz1.cyclicIndexDistance m l i ∧
      1 + Riesz1.cyclicIndexDistance m l i ≤ H) :
    (∑ i ∈ S, weightRadius m i l ^ (-t)) ≤
      2 * ∑ k ∈ Icc δ H, (k : ℝ) ^ (-t) := by
  let rad := fun i => 1 + Riesz1.cyclicIndexDistance m l i
  have hmaps : ∀ i ∈ S, rad i ∈ Icc δ H := fun i hi => mem_Icc.mpr (hS i hi)
  rw [← sum_fiberwise_of_maps_to hmaps]
  calc
    _ ≤ ∑ k ∈ Icc δ H, 2 * (k : ℝ) ^ (-t) := by
      apply sum_le_sum
      intro k hk
      have hcard : (S.filter (fun i => rad i = k)).card ≤ 2 := by
        have hsub : S.filter (fun i => rad i = k) ⊆ cyclicShell m l (k - 1) := by
          intro i hi
          simp only [cyclicShell, mem_filter, mem_univ, true_and]
          have hh := (mem_filter.mp hi).2
          dsimp only [rad] at hh
          omega
        exact (card_le_card hsub).trans (card_cyclicShell_le_two l (k - 1))
      have he : ∀ i ∈ S.filter (fun i => rad i = k),
          weightRadius m i l ^ (-t) = (k : ℝ) ^ (-t) := by
        intro i hi
        have hh := (mem_filter.mp hi).2
        rw [weightRadius_eq_comm]
        congr 1
        exact_mod_cast hh
      rw [sum_congr rfl he, sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := (mul_sum ..).symm

/-- Algebraic normalization for the weighted row energies in the proof of Proposition 5.15. -/
theorem rpow_ratio_square_internal {q r : ℝ} (hq : 0 < q) (hr : 0 < r) (p α : ℝ) :
    (q ^ (-p) / r ^ α) ^ 2 = q ^ (-2 * p) * r ^ (-2 * α) := by
  rw [div_pow, ← Real.rpow_mul_natCast hq.le (-p) 2,
    ← Real.rpow_mul_natCast hr.le α 2, div_eq_mul_inv, ← Real.rpow_neg hr.le]
  simp only [Nat.cast_ofNat, neg_mul, mul_comm p 2, mul_comm α 2]

/-- See the proof of Proposition 5.15 in the paper: weighted coefficient energy in the
intermediate annulus. The shell count retains the boundary cutoff exactly. -/
theorem weighted_annulus_energy_internal (m : ℕ+) (l i₀ : Fin (m : ℕ))
    (S : Finset (Fin (m : ℕ))) (α p R : ℝ) (hα : 0 ≤ α) (hR : 0 < R)
    (δ H : ℕ) (hS : ∀ i ∈ S, R ≤ weightRadius m i i₀ ∧
      δ ≤ 1 + Riesz1.cyclicIndexDistance m l i ∧
        1 + Riesz1.cyclicIndexDistance m l i ≤ H) :
    (∑ i ∈ S, (weightRadius m i l ^ (-p) / weightRadius m i i₀ ^ α) ^ 2) ≤
      R ^ (-2 * α) * (2 * ∑ k ∈ Icc δ H, (k : ℝ) ^ (-2 * p)) := by
  have hr (i) : 0 < weightRadius m i i₀ := by linarith [one_le_weightRadius m i i₀]
  have hq (i) : 0 < weightRadius m i l := by linarith [one_le_weightRadius m i l]
  calc
    _ = ∑ i ∈ S, weightRadius m i i₀ ^ (-2 * α) * weightRadius m i l ^ (-2 * p) := by
      apply sum_congr rfl
      intro i _
      rw [rpow_ratio_square_internal (hq i) (hr i), mul_comm]
    _ ≤ ∑ i ∈ S, R ^ (-2 * α) * weightRadius m i l ^ (-2 * p) := by
      apply sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hR (hS i hi).1 (by linarith)) (by dsimp only [weightRadius]; positivity)
    _ ≤ _ := by
      rw [← mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [show -(2 * p) = -2 * p by ring] using
        annulus_power_sum m l δ H (2 * p) S (fun i hi => (hS i hi).2)

/-- See the proof of Proposition 5.15 in the paper: in the far region the two weights
combine into one summable power. This is the estimate before centering. -/
theorem weighted_far_energy_internal (m : ℕ+) (l i₀ : Fin (m : ℕ))
    (S : Finset (Fin (m : ℕ))) (α p R : ℝ) (hα : 0 ≤ α)
    (hp : 1 < 2 * (p + α)) (hR : 1 ≤ R)
    (hS : ∀ i ∈ S, R ≤ weightRadius m i l ∧
      weightRadius m i l / 2 ≤ weightRadius m i i₀) :
    (∑ i ∈ S, (weightRadius m i l ^ (-p) / weightRadius m i i₀ ^ α) ^ 2) ≤
      2 ^ (2 * α) * (2 * (1 + 1 / (2 * (p + α) - 1))) *
        R ^ (1 - 2 * (p + α)) := by
  have hr (i) : 0 < weightRadius m i i₀ := by linarith [one_le_weightRadius m i i₀]
  have hq (i) : 0 < weightRadius m i l := by linarith [one_le_weightRadius m i l]
  have hpt (i) (hi : i ∈ S) :
      (weightRadius m i l ^ (-p) / weightRadius m i i₀ ^ α) ^ 2 ≤
        2 ^ (2 * α) * weightRadius m i l ^ (-(2 * (p + α))) := by
    have hh := Real.rpow_le_rpow_of_nonpos (div_pos (hq i) (by norm_num))
      (hS i hi).2 (show -2 * α ≤ 0 by linarith)
    calc
      _ = weightRadius m i l ^ (-2 * p) * weightRadius m i i₀ ^ (-2 * α) := by
        exact rpow_ratio_square_internal (hq i) (hr i) p α
      _ ≤ weightRadius m i l ^ (-2 * p) * (weightRadius m i l / 2) ^ (-2 * α) :=
        mul_le_mul_of_nonneg_left hh (by dsimp only [weightRadius]; positivity)
      _ = _ := by
        rw [Real.div_rpow (hq i).le (by norm_num),
          show -2 * α = -(2 * α) by ring,
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv, inv_inv]
        calc
          _ = 2 ^ (2 * α) * (weightRadius m i l ^ (-2 * p) *
              weightRadius m i l ^ (-(2 * α))) := by ring
          _ = _ := by rw [← Real.rpow_add (hq i)]; congr 2; ring
  calc
    _ ≤ ∑ i ∈ S, 2 ^ (2 * α) * weightRadius m i l ^ (-(2 * (p + α))) :=
      sum_le_sum fun i hi => hpt i hi
    _ ≤ 2 ^ (2 * α) * ∑ i ∈ univ.filter (fun i => R ≤ weightRadius m i l),
        weightRadius m i l ^ (-(2 * (p + α))) := by
      rw [← mul_sum]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact sum_le_sum_of_subset_of_nonneg
        (fun i hi => mem_filter.mpr ⟨mem_univ _, (hS i hi).1⟩) (fun i _ _ => by dsimp only [weightRadius]; positivity)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (sum_weightRadius_tail_le m l hp hR)
        (show 0 ≤ (2 : ℝ) ^ (2 * α) by positivity)
      simpa only [mul_assoc] using hh

/-- See the proof of Proposition 5.15 in the paper: the constant column subtraction
on any source-separated set has the required tail energy. -/
theorem constant_tail_energy_internal (m : ℕ+) (i₀ : Fin (m : ℕ))
    (S : Finset (Fin (m : ℕ))) (α c R : ℝ) (hα : 1 < 2 * α) (hR : 1 ≤ R)
    (hS : ∀ i ∈ S, R ≤ weightRadius m i i₀) :
    (∑ i ∈ S, (c / weightRadius m i i₀ ^ α) ^ 2) ≤
      c ^ 2 * (2 * (1 + 1 / (2 * α - 1))) * R ^ (1 - 2 * α) := by
  have he (i) : (c / weightRadius m i i₀ ^ α) ^ 2 =
      c ^ 2 * weightRadius m i i₀ ^ (-(2 * α)) := by
    have hr : 0 < weightRadius m i i₀ := by linarith [one_le_weightRadius m i i₀]
    rw [div_pow, ← Real.rpow_mul_natCast hr.le α 2,
      div_eq_mul_inv, ← Real.rpow_neg hr.le]
    norm_num only [Nat.cast_ofNat]
    congr 2
    ring
  simp_rw [he]
  rw [← mul_sum]
  calc
    _ ≤ c ^ 2 * ∑ i ∈ univ.filter (fun i => R ≤ weightRadius m i i₀),
        weightRadius m i i₀ ^ (-(2 * α)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact sum_le_sum_of_subset_of_nonneg
        (fun i hi => mem_filter.mpr ⟨mem_univ _, hS i hi⟩) (fun i _ _ => by dsimp only [weightRadius]; positivity)
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (sum_weightRadius_tail_le m i₀ hα hR) (sq_nonneg c)

/-- See the proof of Proposition 5.15 in the paper: squared first-moment coefficient
energy on a source ball, for the full range `0 < s < 1`. -/
theorem near_moment_energy_internal (s : Riesz1.RieszExponent) (m : ℕ+)
    (i₀ : Fin (m : ℕ)) (S : Finset (Fin (m : ℕ))) (R : ℝ) (hR : 1 ≤ R)
    (hS : ∀ i ∈ S, weightRadius m i i₀ ≤ R) :
    (∑ i ∈ S, (weightRadius m i i₀ / weightRadius m i i₀ ^ (3 / 2 - s.val)) ^ 2) ≤
      (2 / s.val) * R ^ (2 * s.val) := by
  have hr (i) : 0 < weightRadius m i i₀ := by linarith [one_le_weightRadius m i i₀]
  have he (i) :
      (weightRadius m i i₀ / weightRadius m i i₀ ^ (3 / 2 - s.val)) ^ 2 =
        weightRadius m i i₀ ^ s.val * weightRadius m i i₀ ^ (-(1 - s.val)) := by
    have hid : weightRadius m i i₀ / weightRadius m i i₀ ^ (3 / 2 - s.val) =
        weightRadius m i i₀ ^ (1 - (3 / 2 - s.val)) := by
      simpa only [Real.rpow_one] using (Real.rpow_sub (hr i) 1 (3 / 2 - s.val)).symm
    rw [hid, ← Real.rpow_mul_natCast (hr i).le _ 2,
      ← Real.rpow_add (hr i)]
    congr 1
    norm_num
    ring
  calc
    _ = ∑ i ∈ S, weightRadius m i i₀ ^ s.val *
        weightRadius m i i₀ ^ (-(1 - s.val)) := sum_congr rfl (fun i _ => he i)
    _ ≤ R ^ s.val * ∑ i ∈ univ.filter (fun i => weightRadius m i i₀ ≤ R),
        weightRadius m i i₀ ^ (-(1 - s.val)) := by
      calc
        _ ≤ ∑ i ∈ S, R ^ s.val * weightRadius m i i₀ ^ (-(1 - s.val)) := by
          apply sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow (hr i).le (hS i hi) s.property.1.le)
            (Real.rpow_nonneg (hr i).le _)
        _ ≤ _ := by
          rw [← mul_sum]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact sum_le_sum_of_subset_of_nonneg
            (fun i hi => mem_filter.mpr ⟨mem_univ _, hS i hi⟩)
            (fun i _ _ => Real.rpow_nonneg (hr i).le _)
    _ ≤ R ^ s.val * ((2 / s.val) * R ^ s.val) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [show 1 - (1 - s.val) = s.val by ring] using
        sum_weightRadius_le_of_lt_one m i₀ (sub_pos.mpr s.property.2)
          (by linarith [s.property.1] : 1 - s.val < 1) hR
    _ = _ := by
      rw [show 2 * s.val = s.val + s.val by ring, Real.rpow_add (by linarith : 0 < R)]
      ring

/-- See the proof of Proposition 5.15 in the paper: the actual matrix and its row
increment gain a source distance when centered at the source column. -/
theorem periodized_window_near_oscillation (s : Riesz1.RieszExponent)
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (n m : ℕ+) (hm : 2 ≤ (m : ℕ)) (K : ℕ) (C κ γ ε : ℝ)
    (hC : 0 ≤ C) (M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M) :
    let B := 2 * (C * (n : ℝ) ^ (κ * ε)) * (1 + 1 / (s.val + 1)) * 2 ^ (s.val + 1)
    let T := 2 * (C * (n : ℝ) ^ (κ * ε)) *
      ((∑' k : ℕ, (1 + (k : ℝ)) ^ (-(s.val + 2))) + 2 ^ (s.val + 2))
    ∀ᵐ x ∂ν, ∀ (j i₀ : Fin (m : ℕ)), 16 ≤ Riesz1.cyclicIndexDistance m j i₀ →
      ∀ (l : Fin (LocalizedMatrix.windowSize m j i₀ : ℕ)) (i : Fin (m : ℕ)),
      weightRadius m i i₀ ≤ (Riesz1.cyclicIndexDistance m j i₀ : ℝ) / 4 →
      let row := LocalizedMatrix.windowEmbedding m j i₀ l
      let R := (Riesz1.cyclicIndexDistance m j i₀ : ℝ)
      |M x row i - M x row i₀| ≤ B * 2 ^ (3 * (1 + s.val)) *
          R ^ (-(1 + s.val)) * weightRadius m i i₀ ∧
      |(M x row i - M x (row - 1) i) - (M x row i₀ - M x (row - 1) i₀)| ≤
        T * 2 ^ (3 * (2 + s.val)) * R ^ (-(2 + s.val)) * weightRadius m i i₀ := by
  intro B T
  have hs0 := s.property.1
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hT : 0 ≤ T := by
    have hh : 0 ≤ ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(s.val + 2)) :=
      tsum_nonneg (fun k => by positivity)
    dsimp only [T]
    positivity
  filter_upwards [periodized_entry_and_difference s n m hm K C κ γ ε hC M hM,
    periodized_mixed_difference s n m hm K C κ γ ε hC M hM, hM.2.1] with x hx hy hz
  intro j i₀ hR l i hi row R
  have hs := centered_column_oscillation_internal s m hm (M x) B T hB hT hz.1
    (fun i k => by simpa only [B, weightRadius, show -(1 + s.val) = -1 - s.val by ring]
      using (hx i k).2)
    (fun i k => by simpa only [T, weightRadius, add_comm s.val 2] using hy i k)
    row i₀ i (window_near_source_arc m j i₀ hR l i hi)
  have hRp : 0 < R := by dsimp only [R]; exact_mod_cast (show 0 < Riesz1.cyclicIndexDistance m j i₀ by omega)
  have hrad : R / 2 ≤ weightRadius m i₀ row := by
    have hh := (window_source_radius m j i₀ hR l).1
    simpa only [row, weightRadius, cyclicIndexDistance_comm' m i₀] using hh
  have hp (p : ℝ) (hp : 0 ≤ p) :
      weightRadius m i₀ row ^ (-p) ≤ 2 ^ p * R ^ (-p) := by
    calc
      _ ≤ (R / 2) ^ (-p) := Real.rpow_le_rpow_of_nonpos (by positivity) hrad (by linarith)
      _ = _ := by
        rw [Real.div_rpow hRp.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
          div_eq_mul_inv, inv_inv, mul_comm]
  have hd : (Riesz1.cyclicIndexDistance m i₀ i : ℝ) ≤ weightRadius m i i₀ := by
    rw [weightRadius_eq_comm]
    linarith
  have hpow (p : ℝ) : (2 : ℝ) ^ (3 * p) = 2 ^ p * 2 ^ p * 2 ^ p := by
    rw [show 3 * p = (p + p) + p by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2) (p + p) p,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2) p p]
  constructor
  · calc
      _ ≤ (B * 2 ^ (1 + s.val)) * 2 ^ (1 + s.val) *
          (2 ^ (1 + s.val) * R ^ (-(1 + s.val))) * weightRadius m i i₀ := by
        apply hs.1.trans
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hp _ (by linarith [s.property.1])) (by positivity))
          hd (by positivity) (by positivity)
      _ = _ := by rw [hpow]; ring
  · calc
      _ ≤ (T * 2 ^ (2 + s.val)) * 2 ^ (2 + s.val) *
          (2 ^ (2 + s.val) * R ^ (-(2 + s.val))) * weightRadius m i i₀ := by
        apply hs.2.trans
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hp _ (by linarith [s.property.1])) (by positivity))
          hd (by positivity) (by positivity)
      _ = _ := by rw [hpow]; ring

/-- See the proof of Proposition 5.15 in the paper: a coefficient majorant transfers to
the squared weighted row energy on an arbitrary finite set. -/
theorem coefficient_energy_mono_internal {ι : Type*} (S : Finset ι)
    (f a w : ι → ℝ) (A : ℝ) (hA : 0 ≤ A) (ha : ∀ i ∈ S, 0 ≤ a i)
    (hf : ∀ i ∈ S, |f i| ≤ A * a i) :
    (∑ i ∈ S, (f i / w i) ^ 2) ≤ A ^ 2 * ∑ i ∈ S, (a i / w i) ^ 2 := by
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  have hh := (sq_le_sq₀ (abs_nonneg (f i)) (mul_nonneg hA (ha i hi))).mpr (hf i hi)
  rw [sq_abs, mul_pow] at hh
  simpa only [div_pow, mul_div_assoc] using
    div_le_div_of_nonneg_right hh (sq_nonneg (w i))

/-- See the proof of Proposition 5.15 in the paper: the centered coefficient energy is
controlled by its near-source, intermediate, far, and constant-tail energies.
The partition is exhaustive even at its cutoff equalities. -/
theorem centered_partition_energy_internal {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (r q f w : ι → ℝ) (c R : ℝ) :
    (∑ i ∈ S, ((f i - c) / w i) ^ 2) ≤
      (∑ i ∈ S.filter (fun i => r i ≤ R / 4), ((f i - c) / w i) ^ 2) +
      2 * (∑ i ∈ S.filter (fun i => R / 4 ≤ r i ∧ q i ≤ 4 * R), (f i / w i) ^ 2) +
      2 * (∑ i ∈ S.filter (fun i => 4 * R ≤ q i), (f i / w i) ^ 2) +
      2 * ∑ i ∈ S.filter (fun i => R / 4 ≤ r i), (c / w i) ^ 2 := by
  simp only [sum_filter, mul_sum]
  rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_le_sum
  intro i _
  have hsquare : ((f i - c) / w i) ^ 2 ≤ 2 * (f i / w i) ^ 2 + 2 * (c / w i) ^ 2 := by
    rw [sub_div]
    nlinarith only [sq_nonneg (f i / w i + c / w i)]
  by_cases hn : r i ≤ R / 4
  · simp only [hn, ite_true]
    split_ifs <;> nlinarith only [sq_nonneg (f i / w i), sq_nonneg (c / w i)]
  · have hr : R / 4 ≤ r i := (not_le.mp hn).le
    by_cases hq : q i ≤ 4 * R
    · simp only [hn, ite_false, hr, hq, and_self, ite_true]
      split_ifs <;> nlinarith only [hsquare, sq_nonneg (f i / w i)]
    · have hq' : 4 * R ≤ q i := (not_le.mp hq).le
      simpa only [hn, ite_false, hr, hq, and_false, hq', ite_true, mul_zero, zero_add] using hsquare

/-- See the proof of Proposition 5.15 in the paper: the intermediate coefficient-energy
estimate is instantiated on the actual window complement. -/
theorem window_annulus_energy (m : ℕ+) (j i₀ : Fin (m : ℕ))
    (hR : 16 ≤ Riesz1.cyclicIndexDistance m j i₀)
    (l : Fin (LocalizedMatrix.windowSize m j i₀ : ℕ)) (α p : ℝ) (hα : 0 ≤ α) :
    let R := Riesz1.cyclicIndexDistance m j i₀
    let row := LocalizedMatrix.windowEmbedding m j i₀ l
    let δ := min (l.val + 1) ((LocalizedMatrix.windowSize m j i₀ : ℕ) - l.val)
    let S := (LocalizedMatrix.window m j i₀)ᶜ.filter (fun i =>
      (R : ℝ) / 4 ≤ weightRadius m i i₀ ∧ weightRadius m i row ≤ 4 * (R : ℝ))
    (∑ i ∈ S, (weightRadius m i row ^ (-p) / weightRadius m i i₀ ^ α) ^ 2) ≤
      ((R : ℝ) / 4) ^ (-2 * α) * (2 * ∑ k ∈ Icc δ (4 * R), (k : ℝ) ^ (-2 * p)) := by
  intro R row δ S
  have hRp : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by dsimp only [R]; omega)
  apply weighted_annulus_energy_internal m row i₀ S α p ((R : ℝ) / 4) hα (by positivity)
  intro i hi
  have hh := mem_filter.mp hi
  refine ⟨hh.2.1, ?_, ?_⟩
  · have hd := window_exterior_distance m j i₀ l i (mem_compl.mp hh.1)
    change δ ≤ 1 + Riesz1.cyclicIndexDistance m (LocalizedMatrix.windowEmbedding m j i₀ l) i
    omega
  · have hu := hh.2.2
    dsimp only [weightRadius] at hu
    rw [cyclicIndexDistance_comm' m i row] at hu
    exact_mod_cast hu

/-- See the proof of Proposition 5.15 in the paper: the far coefficient-energy estimate
uses the actual source/window geometry, rather than an assumed separation. -/
theorem window_far_energy (m : ℕ+) (j i₀ : Fin (m : ℕ))
    (hR : 16 ≤ Riesz1.cyclicIndexDistance m j i₀)
    (l : Fin (LocalizedMatrix.windowSize m j i₀ : ℕ)) (α p : ℝ)
    (hα : 0 ≤ α) (hp : 1 < 2 * (p + α)) :
    let R := (Riesz1.cyclicIndexDistance m j i₀ : ℝ)
    let row := LocalizedMatrix.windowEmbedding m j i₀ l
    let S := (LocalizedMatrix.window m j i₀)ᶜ.filter (fun i => 4 * R ≤ weightRadius m i row)
    (∑ i ∈ S, (weightRadius m i row ^ (-p) / weightRadius m i i₀ ^ α) ^ 2) ≤
      2 ^ (2 * α) * (2 * (1 + 1 / (2 * (p + α) - 1))) *
        (4 * R) ^ (1 - 2 * (p + α)) := by
  intro R row S
  have hR' : (16 : ℝ) ≤ R := by
    change (16 : ℝ) ≤ (Riesz1.cyclicIndexDistance m j i₀ : ℝ)
    exact_mod_cast hR
  apply weighted_far_energy_internal m row i₀ S α p (4 * R) hα hp (by linarith)
  intro i hi
  have hh := (mem_filter.mp hi).2
  exact ⟨hh, far_radius_comparison m row i₀ i R (window_source_radius m j i₀ hR l).2 hh⟩

/-- See the proof of Proposition 5.15 in the paper: the interior correction in the exact
centering identity has a source-separated inverse-weight energy. -/
theorem window_interior_correction_energy (s : Riesz1.RieszExponent)
    (m : ℕ+) (j i₀ : Fin (m : ℕ))
    (hR : 16 ≤ Riesz1.cyclicIndexDistance m j i₀) (c : ℝ) :
    (∑ i ∈ LocalizedMatrix.window m j i₀,
      (c / weightRadius m i i₀ ^ (3 / 2 - s.val)) ^ 2) ≤
      c ^ 2 * (2 * (1 + 1 / (2 - 2 * s.val))) *
        ((Riesz1.cyclicIndexDistance m j i₀ : ℝ) / 2) ^ (-2 + 2 * s.val) := by
  have hR' : (16 : ℝ) ≤ Riesz1.cyclicIndexDistance m j i₀ := by exact_mod_cast hR
  have hh := constant_tail_energy_internal m i₀ (LocalizedMatrix.window m j i₀)
    (3 / 2 - s.val) c ((Riesz1.cyclicIndexDistance m j i₀ : ℝ) / 2)
    (by linarith [s.property.2]) (by linarith) ?_
  · simpa only [show 2 * (3 / 2 - s.val) - 1 = 2 - 2 * s.val by ring,
      show 1 - 2 * (3 / 2 - s.val) = -2 + 2 * s.val by ring] using hh
  · intro i hi
    have hl := LocalizedMatrix.window_separation m j i₀ i hi
    have hl' : 7 * (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ≤
        8 * (Riesz1.cyclicIndexDistance m i i₀ : ℝ) := by exact_mod_cast hl
    dsimp only [weightRadius]
    linarith

/-- See the proof of Proposition 5.15 in the paper: all four geometric regions and the
interior correction are assembled at the level of squared coefficient energies.
The two kernel envelopes are internal inputs. The window is the actual window. -/
theorem window_centered_energy_internal (s : Riesz1.RieszExponent)
    (m : ℕ+) (j i₀ : Fin (m : ℕ)) (hR : 16 ≤ Riesz1.cyclicIndexDistance m j i₀)
    (l : Fin (LocalizedMatrix.windowSize m j i₀ : ℕ))
    (p A B : ℝ) (hp : s.val ≤ p) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (f : Fin (m : ℕ) → ℝ) (c : ℝ)
    (he : ∀ i, |f i| ≤ A * weightRadius m i (LocalizedMatrix.windowEmbedding m j i₀ l) ^ (-p))
    (ho : ∀ i, weightRadius m i i₀ ≤ (Riesz1.cyclicIndexDistance m j i₀ : ℝ) / 4 →
      |f i - c| ≤ B * (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (-(p + 1)) * weightRadius m i i₀) :
    let R := (Riesz1.cyclicIndexDistance m j i₀ : ℝ)
    let δ := min (l.val + 1) ((LocalizedMatrix.windowSize m j i₀ : ℕ) - l.val)
    let α := 3 / 2 - s.val
    let T := 2 * (1 + 1 / (2 * (p + α) - 1))
    let Q := 2 * (1 + 1 / (2 * α - 1))
    (∑ i ∈ (LocalizedMatrix.window m j i₀)ᶜ, ((f i - c) / weightRadius m i i₀ ^ α) ^ 2) +
      (∑ i ∈ LocalizedMatrix.window m j i₀, (c / weightRadius m i i₀ ^ α) ^ 2) ≤
      (B * R ^ (-(p + 1))) ^ 2 * ((2 / s.val) * R ^ (2 * s.val)) +
      2 * A ^ 2 * ((R / 4) ^ (-2 * α) *
        (2 * ∑ k ∈ Icc δ (4 * Riesz1.cyclicIndexDistance m j i₀), (k : ℝ) ^ (-2 * p))) +
      2 * A ^ 2 * (2 ^ (2 * α) * T * (4 * R) ^ (1 - 2 * (p + α))) +
      2 * c ^ 2 * Q * (R / 4) ^ (1 - 2 * α) +
      c ^ 2 * Q * (R / 2) ^ (1 - 2 * α) := by
  intro R δ α T Q
  let J := LocalizedMatrix.window m j i₀
  let row := LocalizedMatrix.windowEmbedding m j i₀ l
  let w := fun i => weightRadius m i i₀ ^ α
  let N := Jᶜ.filter (fun i => weightRadius m i i₀ ≤ R / 4)
  let I := Jᶜ.filter (fun i => R / 4 ≤ weightRadius m i i₀ ∧ weightRadius m i row ≤ 4 * R)
  let F := Jᶜ.filter (fun i => 4 * R ≤ weightRadius m i row)
  let C₀ := Jᶜ.filter (fun i => R / 4 ≤ weightRadius m i i₀)
  have hR' : (16 : ℝ) ≤ R := by dsimp only [R]; exact_mod_cast hR
  have hα : 0 ≤ α := by dsimp only [α]; linarith [s.property.2]
  have hα2 : 1 < 2 * α := by dsimp only [α]; linarith [s.property.2]
  have hpα : 1 < 2 * (p + α) := by dsimp only [α]; linarith
  have hN : (∑ i ∈ N, ((f i - c) / w i) ^ 2) ≤
      (B * R ^ (-(p + 1))) ^ 2 * ((2 / s.val) * R ^ (2 * s.val)) := by
    have hn := coefficient_energy_mono_internal N (fun i => f i - c)
      (fun i => weightRadius m i i₀) w (B * R ^ (-(p + 1))) (by positivity)
      (fun i _ => by linarith [one_le_weightRadius m i i₀])
      (fun i hi => ho i (mem_filter.mp hi).2)
    apply hn.trans
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact near_moment_energy_internal s m i₀ N R (by linarith)
      (fun i hi => ((mem_filter.mp hi).2).trans (by linarith))
  have hI : (∑ i ∈ I, (f i / w i) ^ 2) ≤
      A ^ 2 * ((R / 4) ^ (-2 * α) *
        (2 * ∑ k ∈ Icc δ (4 * Riesz1.cyclicIndexDistance m j i₀), (k : ℝ) ^ (-2 * p))) := by
    apply (coefficient_energy_mono_internal I f (fun i => weightRadius m i row ^ (-p)) w A hA
      (fun i _ => by dsimp only [weightRadius]; positivity) (fun i _ => he i)).trans
    exact mul_le_mul_of_nonneg_left (window_annulus_energy m j i₀ hR l α p hα) (sq_nonneg A)
  have hF : (∑ i ∈ F, (f i / w i) ^ 2) ≤
      A ^ 2 * (2 ^ (2 * α) * T * (4 * R) ^ (1 - 2 * (p + α))) := by
    apply (coefficient_energy_mono_internal F f (fun i => weightRadius m i row ^ (-p)) w A hA
      (fun i _ => by dsimp only [weightRadius]; positivity) (fun i _ => he i)).trans
    exact mul_le_mul_of_nonneg_left (window_far_energy m j i₀ hR l α p hα hpα) (sq_nonneg A)
  have hC₀ : (∑ i ∈ C₀, (c / w i) ^ 2) ≤ c ^ 2 * Q * (R / 4) ^ (1 - 2 * α) :=
    constant_tail_energy_internal m i₀ C₀ α c (R / 4) hα2 (by linarith)
      (fun i hi => (mem_filter.mp hi).2)
  have hJ : (∑ i ∈ J, (c / w i) ^ 2) ≤ c ^ 2 * Q * (R / 2) ^ (1 - 2 * α) := by
    simpa only [α, Q, show 2 * (3 / 2 - s.val) - 1 = 2 - 2 * s.val by ring,
      show 1 - 2 * (3 / 2 - s.val) = -2 + 2 * s.val by ring] using
      window_interior_correction_energy s m j i₀ hR c
  have hsplit := centered_partition_energy_internal Jᶜ
    (fun i => weightRadius m i i₀) (fun i => weightRadius m i row) f w c R
  change (∑ i ∈ Jᶜ, ((f i - c) / w i) ^ 2) + (∑ i ∈ J, (c / w i) ^ 2) ≤ _
  linarith only [hsplit, hN, hI, hF, hC₀, hJ]

/-- Power bookkeeping for the geometric energy estimate in the proof of Proposition 5.15. Its constant is independent of the radius and rows. -/
theorem geometric_energy_normalization_internal (s : Riesz1.RieszExponent)
    (p : ℝ) (hp : s.val ≤ p) :
    ∃ K : ℝ, 0 < K ∧ ∀ (R A B c S : ℝ), 0 < R → 0 ≤ A → 0 ≤ B → 0 ≤ S →
      |c| ≤ A * (R / 2) ^ (-p) →
      let α := 3 / 2 - s.val
      let T := 2 * (1 + 1 / (2 * (p + α) - 1))
      let Q := 2 * (1 + 1 / (2 * α - 1))
      (B * R ^ (-(p + 1))) ^ 2 * ((2 / s.val) * R ^ (2 * s.val)) +
      2 * A ^ 2 * ((R / 4) ^ (-2 * α) * (2 * S)) +
      2 * A ^ 2 * (2 ^ (2 * α) * T * (4 * R) ^ (1 - 2 * (p + α))) +
      2 * c ^ 2 * Q * (R / 4) ^ (1 - 2 * α) +
      c ^ 2 * Q * (R / 2) ^ (1 - 2 * α) ≤
        K * (A + B) ^ 2 * (R ^ (2 * (s.val - p - 1)) + R ^ (-2 * α) * S) := by
  let α := 3 / 2 - s.val
  let T := 2 * (1 + 1 / (2 * (p + α) - 1))
  let Q := 2 * (1 + 1 / (2 * α - 1))
  let kN := 2 / s.val
  let kM : ℝ := 4 * 4 ^ (2 * α)
  let kF := 2 * 2 ^ (2 * α) * T * 4 ^ (1 - 2 * (p + α))
  let kC := 2 * 2 ^ (2 * p) * Q * 4 ^ (2 * α - 1)
  let kJ := 2 ^ (2 * p) * Q * 2 ^ (2 * α - 1)
  let K := kN + kM + kF + kC + kJ + 1
  have hs := s.property.1
  have hs1 := s.property.2
  have hQ : 0 < Q := by
    have hh : 0 < 2 * α - 1 := by dsimp only [α]; linarith
    dsimp only [Q]; positivity
  have hT : 0 < T := by
    have hh : 0 < 2 * (p + α) - 1 := by dsimp only [α]; linarith
    dsimp only [T]; positivity
  have hn : 0 ≤ kN := by dsimp only [kN]; positivity
  have hm : 0 ≤ kM := by dsimp only [kM]; positivity
  have hf : 0 ≤ kF := by dsimp only [kF]; positivity
  have hc : 0 ≤ kC := by dsimp only [kC]; positivity
  have hj : 0 ≤ kJ := by dsimp only [kJ]; positivity
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro R A B c S hR hA hB hS hcb α' T' Q'
  change _ ≤ K * (A + B) ^ 2 * (R ^ (2 * (s.val - p - 1)) + R ^ (-2 * α) * S)
  change (B * R ^ (-(p + 1))) ^ 2 * ((2 / s.val) * R ^ (2 * s.val)) +
      2 * A ^ 2 * ((R / 4) ^ (-2 * α) * (2 * S)) +
      2 * A ^ 2 * (2 ^ (2 * α) * T * (4 * R) ^ (1 - 2 * (p + α))) +
      2 * c ^ 2 * Q * (R / 4) ^ (1 - 2 * α) +
      c ^ 2 * Q * (R / 2) ^ (1 - 2 * α) ≤ _
  have hscale (d e : ℝ) (hd : 0 < d) : (R / d) ^ e = d ^ (-e) * R ^ e := by
    rw [Real.div_rpow hR.le hd.le, Real.rpow_neg hd.le, div_eq_mul_inv, mul_comm]
  have hmul (d e : ℝ) (hd : 0 < d) : (d * R) ^ e = d ^ e * R ^ e :=
    Real.mul_rpow hd.le hR.le
  have hnear : (B * R ^ (-(p + 1))) ^ 2 * ((2 / s.val) * R ^ (2 * s.val)) =
      B ^ 2 * kN * R ^ (2 * (s.val - p - 1)) := by
    rw [mul_pow, ← Real.rpow_mul_natCast hR.le _ 2]
    norm_num only [Nat.cast_ofNat]
    calc
      _ = B ^ 2 * kN * (R ^ (-(p + 1) * 2) * R ^ (2 * s.val)) := by dsimp only [kN]; ring
      _ = _ := by
        rw [← Real.rpow_add hR]
        rw [show -(p + 1) * 2 + 2 * s.val = 2 * (s.val - p - 1) by ring]
  have hmiddle : 2 * A ^ 2 * ((R / 4) ^ (-2 * α) * (2 * S)) =
      A ^ 2 * kM * (R ^ (-2 * α) * S) := by
    rw [hscale 4 _ (by norm_num)]
    dsimp only [kM]
    rw [show -(-2 * α) = 2 * α by ring]
    ring
  have hfar : 2 * A ^ 2 * (2 ^ (2 * α) * T * (4 * R) ^ (1 - 2 * (p + α))) =
      A ^ 2 * kF * R ^ (2 * (s.val - p - 1)) := by
    rw [hmul 4 _ (by norm_num)]
    have he : 1 - 2 * (p + α) = 2 * (s.val - p - 1) := by dsimp only [α]; ring
    rw [he]
    dsimp only [kF]
    rw [he]
    ring
  have hcsq : c ^ 2 ≤ A ^ 2 * (R / 2) ^ (-2 * p) := by
    have hh := (sq_le_sq₀ (abs_nonneg c) (by positivity : 0 ≤ A * (R / 2) ^ (-p))).mpr hcb
    rw [sq_abs, mul_pow, ← Real.rpow_mul_natCast (by positivity : 0 ≤ R / 2) (-p) 2] at hh
    simpa only [Nat.cast_ofNat, show -p * (2 : ℝ) = -2 * p by ring] using hh
  have hct : 2 * c ^ 2 * Q * (R / 4) ^ (1 - 2 * α) ≤
      A ^ 2 * kC * R ^ (2 * (s.val - p - 1)) := by
    calc
      _ ≤ 2 * (A ^ 2 * (R / 2) ^ (-2 * p)) * Q * (R / 4) ^ (1 - 2 * α) := by gcongr
      _ = _ := by
        rw [hscale 2 _ (by norm_num), hscale 4 _ (by norm_num)]
        calc
          _ = A ^ 2 * (2 * 2 ^ (2 * p) * Q * 4 ^ (2 * α - 1)) *
              (R ^ (-2 * p) * R ^ (1 - 2 * α)) := by
            rw [show -(-2 * p) = 2 * p by ring, show -(1 - 2 * α) = 2 * α - 1 by ring]
            ring
          _ = _ := by rw [← Real.rpow_add hR]; congr 2; dsimp only [α]; ring
  have hjt : c ^ 2 * Q * (R / 2) ^ (1 - 2 * α) ≤
      A ^ 2 * kJ * R ^ (2 * (s.val - p - 1)) := by
    calc
      _ ≤ (A ^ 2 * (R / 2) ^ (-2 * p)) * Q * (R / 2) ^ (1 - 2 * α) := by gcongr
      _ = _ := by
        rw [hscale 2 _ (by norm_num), hscale 2 _ (by norm_num)]
        calc
          _ = A ^ 2 * (2 ^ (2 * p) * Q * 2 ^ (2 * α - 1)) *
              (R ^ (-2 * p) * R ^ (1 - 2 * α)) := by
            rw [show -(-2 * p) = 2 * p by ring, show -(1 - 2 * α) = 2 * α - 1 by ring]
            ring
          _ = _ := by rw [← Real.rpow_add hR]; congr 2; dsimp only [α]; ring
  rw [hnear, hmiddle, hfar]
  have habA : A ^ 2 ≤ (A + B) ^ 2 := by nlinarith
  have habB : B ^ 2 ≤ (A + B) ^ 2 := by nlinarith
  have hX : 0 ≤ R ^ (2 * (s.val - p - 1)) := by positivity
  have hY : 0 ≤ R ^ (-2 * α) * S := by positivity
  have hXcoeff : B ^ 2 * kN + A ^ 2 * kF + A ^ 2 * kC + A ^ 2 * kJ ≤ K * (A + B) ^ 2 := by
    have hh := add_le_add (add_le_add (mul_le_mul_of_nonneg_right habB hn)
      (mul_le_mul_of_nonneg_right habA hf))
      (add_le_add (mul_le_mul_of_nonneg_right habA hc) (mul_le_mul_of_nonneg_right habA hj))
    dsimp only [K]
    nlinarith only [hh, mul_nonneg hm (sq_nonneg (A + B)), sq_nonneg (A + B)]
  have hYcoeff : A ^ 2 * kM ≤ K * (A + B) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right habA hm
    dsimp only [K]
    nlinarith only [hh, mul_nonneg hn (sq_nonneg (A + B)), mul_nonneg hf (sq_nonneg (A + B)),
      mul_nonneg hc (sq_nonneg (A + B)), mul_nonneg hj (sq_nonneg (A + B)), sq_nonneg (A + B)]
  have hh := add_le_add (mul_le_mul_of_nonneg_right hXcoeff hX)
    (mul_le_mul_of_nonneg_right hYcoeff hY)
  nlinarith only [hh, hct, hjt]

/-- See the proof of Proposition 5.15 in the paper: the two coefficient norms of a
centered row have the required radius profile. This is an internal kernel
estimate. Final uses establish its envelopes from the interval bounds. -/
theorem window_centered_coefficient_bound_internal (s : Riesz1.RieszExponent)
    (p : ℝ) (hp : s.val ≤ p) :
    ∃ D : ℝ, 0 < D ∧ ∀ (m : ℕ+) (j i₀ : Fin (m : ℕ))
      (_hR : 16 ≤ Riesz1.cyclicIndexDistance m j i₀)
      (l : Fin (LocalizedMatrix.windowSize m j i₀ : ℕ))
      (A B : ℝ), 0 ≤ A → 0 ≤ B → ∀ (f : Fin (m : ℕ) → ℝ) (c : ℝ),
      (∀ i, |f i| ≤ A * weightRadius m i (LocalizedMatrix.windowEmbedding m j i₀ l) ^ (-p)) →
      |c| ≤ A * ((Riesz1.cyclicIndexDistance m j i₀ : ℝ) / 2) ^ (-p) →
      (∀ i, weightRadius m i i₀ ≤ (Riesz1.cyclicIndexDistance m j i₀ : ℝ) / 4 →
        |f i - c| ≤ B * (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (-(p + 1)) * weightRadius m i i₀) →
      let R := (Riesz1.cyclicIndexDistance m j i₀ : ℝ)
      let δ := min (l.val + 1) ((LocalizedMatrix.windowSize m j i₀ : ℕ) - l.val)
      let w := fun i => weightRadius m i i₀ ^ (3 / 2 - s.val)
      Real.sqrt (∑ i ∈ (LocalizedMatrix.window m j i₀)ᶜ, ((f i - c) / w i) ^ 2) +
        Real.sqrt (∑ i ∈ LocalizedMatrix.window m j i₀, (c / w i) ^ 2) ≤
        D * (A + B) * (R ^ (s.val - p - 1) + R ^ (-(3 / 2 - s.val)) *
          Real.sqrt (∑ k ∈ Icc δ (4 * Riesz1.cyclicIndexDistance m j i₀), (k : ℝ) ^ (-2 * p))) := by
  obtain ⟨K, hK, hnorm⟩ := geometric_energy_normalization_internal s p hp
  refine ⟨2 * Real.sqrt K, by positivity, ?_⟩
  intro m j i₀ hR l A B hA hB f c he hc ho R δ w
  let X := ∑ i ∈ (LocalizedMatrix.window m j i₀)ᶜ, ((f i - c) / w i) ^ 2
  let Y := ∑ i ∈ LocalizedMatrix.window m j i₀, (c / w i) ^ 2
  let S := ∑ k ∈ Icc δ (4 * Riesz1.cyclicIndexDistance m j i₀), (k : ℝ) ^ (-2 * p)
  let u := R ^ (s.val - p - 1)
  let v := R ^ (-(3 / 2 - s.val)) * Real.sqrt S
  have hRp : 0 < R := by dsimp only [R]; exact_mod_cast (show 0 < Riesz1.cyclicIndexDistance m j i₀ by omega)
  have hX : 0 ≤ X := sum_nonneg (fun _ _ => sq_nonneg _)
  have hY : 0 ≤ Y := sum_nonneg (fun _ _ => sq_nonneg _)
  have hS : 0 ≤ S := sum_nonneg (fun k _ => Real.rpow_nonneg (Nat.cast_nonneg k) _)
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have hv : 0 ≤ v := by dsimp only [v]; positivity
  have hbound := (window_centered_energy_internal s m j i₀ hR l p A B hp hA hB f c he ho).trans
    (hnorm R A B c S hRp hA hB hS hc)
  change X + Y ≤ K * (A + B) ^ 2 *
    (R ^ (2 * (s.val - p - 1)) + R ^ (-2 * (3 / 2 - s.val)) * S) at hbound
  have hpow (t : ℝ) : R ^ (2 * t) = (R ^ t) ^ 2 := by
    simpa only [Nat.cast_ofNat, mul_comm 2 t] using (Real.rpow_mul_natCast hRp.le t 2)
  have hvsq : R ^ (-2 * (3 / 2 - s.val)) * S = v ^ 2 := by
    dsimp only [v]
    rw [mul_pow, Real.sq_sqrt hS, ← Real.rpow_mul_natCast hRp.le _ 2]
    congr 2
    norm_num
    ring
  rw [hpow, hvsq] at hbound
  have hsum : X + Y ≤ (Real.sqrt K * (A + B) * (u + v)) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left
      (show u ^ 2 + v ^ 2 ≤ (u + v) ^ 2 by nlinarith [mul_nonneg hu hv])
      (show 0 ≤ K * (A + B) ^ 2 by positivity)
    rw [mul_pow, mul_pow, Real.sq_sqrt hK.le]
    exact hbound.trans hh
  have hroot := (Real.sqrt_le_iff).mpr ⟨by positivity, hsum⟩
  have hx := (Real.sqrt_le_sqrt (show X ≤ X + Y by linarith)).trans hroot
  have hy := (Real.sqrt_le_sqrt (show Y ≤ X + Y by linarith)).trans hroot
  change Real.sqrt X + Real.sqrt Y ≤ _
  change Real.sqrt X + Real.sqrt Y ≤ 2 * Real.sqrt K * (A + B) * (u + v)
  linarith

/-- See the proof of Proposition 5.15 in the paper: the joint centered coefficient
bounds for the actual periodized matrix. Both constants precede every size,
window, coefficient prefactor and small parameter. -/
theorem periodized_window_coefficient_bounds (s : Riesz1.RieszExponent) :
    ∃ P₀ P₁ : ℝ, 0 < P₀ ∧ 0 < P₁ ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
      (n m : ℕ+) (hm : 2 ≤ (m : ℕ)) (K : ℕ) (C κ γ ε : ℝ), 0 ≤ C →
    ∀ (M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ),
      PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M →
    ∀ᵐ x ∂ν, ∀ (j i₀ : Fin (m : ℕ)), 16 ≤ Riesz1.cyclicIndexDistance m j i₀ →
    ∀ l : Fin (LocalizedMatrix.windowSize m j i₀ : ℕ),
      let R := (Riesz1.cyclicIndexDistance m j i₀ : ℝ)
      let row := LocalizedMatrix.windowEmbedding m j i₀ l
      let δ := min (l.val + 1) ((LocalizedMatrix.windowSize m j i₀ : ℕ) - l.val)
      let J := LocalizedMatrix.window m j i₀
      let w := fun i => weightRadius m i i₀ ^ (3 / 2 - s.val)
      let c₀ := M x row i₀
      let c₁ := M x row i₀ - M x (row - 1) i₀
      (Real.sqrt (∑ i ∈ Jᶜ, ((M x row i - c₀) / w i) ^ 2) +
        Real.sqrt (∑ i ∈ J, (c₀ / w i) ^ 2) ≤
          P₀ * (C * (n : ℝ) ^ (κ * ε)) * (R ^ (-1 : ℝ) + R ^ (-(3 / 2 - s.val)) *
            Real.sqrt (∑ k ∈ Icc δ (4 * Riesz1.cyclicIndexDistance m j i₀), (k : ℝ) ^ (-2 * s.val)))) ∧
      (Real.sqrt (∑ i ∈ Jᶜ, (((M x row i - M x (row - 1) i) - c₁) / w i) ^ 2) +
        Real.sqrt (∑ i ∈ J, (c₁ / w i) ^ 2) ≤
          P₁ * (C * (n : ℝ) ^ (κ * ε)) * (R ^ (-2 : ℝ) + R ^ (-(3 / 2 - s.val)) *
            Real.sqrt (∑ k ∈ Icc δ (4 * Riesz1.cyclicIndexDistance m j i₀), (k : ℝ) ^ (-2 * (1 + s.val))))) := by
  obtain ⟨D₀, hD₀, hd₀⟩ := window_centered_coefficient_bound_internal s s.val le_rfl
  obtain ⟨D₁, hD₁, hd₁⟩ := window_centered_coefficient_bound_internal s (1 + s.val) (by linarith)
  let a := (1 + 1 / s.val) * 2 ^ s.val
  let b := 2 * (1 + 1 / (s.val + 1)) * 2 ^ (s.val + 1)
  let t := 2 * ((∑' k : ℕ, (1 + (k : ℝ)) ^ (-(s.val + 2))) + 2 ^ (s.val + 2))
  let P₀ := D₀ * (a + b * 2 ^ (3 * (1 + s.val)))
  let P₁ := D₁ * (b + t * 2 ^ (3 * (2 + s.val)))
  have hs := s.property.1
  have ha : 0 < a := by dsimp only [a]; positivity
  have hb : 0 < b := by dsimp only [b]; positivity
  have ht : 0 < t := by
    have hh : 0 ≤ ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(s.val + 2)) := tsum_nonneg (fun k => by positivity)
    dsimp only [t]; positivity
  refine ⟨P₀, P₁, by dsimp only [P₀]; positivity, by dsimp only [P₁]; positivity, ?_⟩
  intro Ω _ ν n m hm K C κ γ ε hC M hM
  filter_upwards [periodized_entry_and_difference s n m hm K C κ γ ε hC M hM,
    periodized_window_near_oscillation s n m hm K C κ γ ε hC M hM] with x hx ho
  intro j i₀ hR l R row δ J w c₀ c₁
  let e := C * (n : ℝ) ^ (κ * ε)
  have he : 0 ≤ e := by dsimp only [e]; positivity
  have hr (i) : 0 < weightRadius m i row := by linarith [one_le_weightRadius m i row]
  have hRp : 0 < R := by dsimp only [R]; exact_mod_cast (show 0 < Riesz1.cyclicIndexDistance m j i₀ by omega)
  have hrad : R / 2 ≤ weightRadius m i₀ row := by
    have hh := (window_source_radius m j i₀ hR l).1
    simpa only [row, weightRadius, cyclicIndexDistance_comm' m i₀] using hh
  have hentry (i) : |M x row i| ≤ (e * a) * weightRadius m i row ^ (-s.val) := by
    simpa only [e, a, weightRadius_eq_comm] using (hx row i).1
  have hdiff (i) : |M x row i - M x (row - 1) i| ≤
      (e * b) * weightRadius m i row ^ (-(1 + s.val)) := by
    simpa only [e, b, weightRadius_eq_comm, show -(1 + s.val) = -1 - s.val by ring, mul_assoc, mul_left_comm, mul_comm] using
      (hx row i).2
  have hconst₀ : |c₀| ≤ (e * a) * (R / 2) ^ (-s.val) :=
    (hentry i₀).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by positivity) hrad (by linarith)) (by positivity))
  have hconst₁ : |c₁| ≤ (e * b) * (R / 2) ^ (-(1 + s.val)) :=
    (hdiff i₀).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by positivity) hrad (by linarith)) (by positivity))
  have hnear₀ : ∀ i, weightRadius m i i₀ ≤ R / 4 →
      |M x row i - c₀| ≤ (e * (b * 2 ^ (3 * (1 + s.val)))) *
        R ^ (-(s.val + 1)) * weightRadius m i i₀ := by
    intro i hi
    simpa only [row, c₀, R, e, b, mul_assoc, mul_left_comm, mul_comm, add_comm s.val 1] using (ho j i₀ hR l i hi).1
  have hnear₁ : ∀ i, weightRadius m i i₀ ≤ R / 4 →
      |(M x row i - M x (row - 1) i) - c₁| ≤ (e * (t * 2 ^ (3 * (2 + s.val)))) *
        R ^ (-((1 + s.val) + 1)) * weightRadius m i i₀ := by
    intro i hi
    simpa only [row, c₁, R, e, t, mul_assoc, mul_left_comm, mul_comm, show (1 + s.val) + 1 = 2 + s.val by ring] using
      (ho j i₀ hR l i hi).2
  constructor
  · have hh := hd₀ m j i₀ hR l (e * a) (e * (b * 2 ^ (3 * (1 + s.val))))
      (by positivity) (by positivity) (fun i => M x row i) c₀ hentry hconst₀ hnear₀
    convert hh using 1
    dsimp only [P₀, R, δ, e]
    rw [show s.val - s.val - 1 = (-1 : ℝ) by ring]
    ring
  · have hh := hd₁ m j i₀ hR l (e * b) (e * (t * 2 ^ (3 * (2 + s.val))))
      (by positivity) (by positivity) (fun i => M x row i - M x (row - 1) i) c₁ hdiff hconst₁ hnear₁
    convert hh using 1
    dsimp only [P₁, R, δ, e]
    rw [show s.val - (1 + s.val) - 1 = (-2 : ℝ) by ring]
    ring

/-- See the proof of Proposition 5.15 in the paper: the derivative square sum is
bounded by its summable positive tail, including an empty finite interval. -/
theorem square_increment_tail (s : Riesz1.RieszExponent) (δ H : ℕ) (hδ : 1 ≤ δ) :
    Real.sqrt (∑ k ∈ Icc δ H, (k : ℝ) ^ (-2 * (1 + s.val))) ≤
      Real.sqrt (1 + 1 / (1 + 2 * s.val)) * (δ : ℝ) ^ (-(1 / 2 + s.val)) := by
  have hδp : (0 : ℝ) < δ := by exact_mod_cast (show 0 < δ by omega)
  have ht : 1 < 2 * (1 + s.val) := by linarith [s.property.1]
  have he : (∑ k ∈ Icc δ H, (k : ℝ) ^ (-2 * (1 + s.val))) =
      ∑ k : Fin H, if (δ : ℝ) ≤ (k.val + 1 : ℝ) then
        (k.val + 1 : ℝ) ^ (-(2 * (1 + s.val))) else 0 := by
    have hsets : (Icc 1 H).filter (fun k => δ ≤ k) = Icc δ H := by
      ext k
      simp only [mem_filter, mem_Icc]
      omega
    rw [← hsets, sum_filter]
    rw [show Icc 1 H = Ico 1 (H + 1) by ext k; simp only [mem_Icc, mem_Ico]; omega,
      sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => if (δ : ℝ) ≤ (k : ℝ) + 1 then
      ((k : ℝ) + 1) ^ (-(2 * (1 + s.val))) else 0) H]
    apply sum_congr rfl
    intro k _
    have hc : δ ≤ 1 + k ↔ (δ : ℝ) ≤ (k : ℝ) + 1 := by
      rw [show (k : ℝ) + 1 = ((1 + k : ℕ) : ℝ) by push_cast; ring]
      exact_mod_cast (Iff.rfl : δ ≤ 1 + k ↔ δ ≤ 1 + k)
    simp only [Nat.cast_add, Nat.cast_one, add_comm 1] at hc ⊢
    simp only [hc, show -(2 * (1 + s.val)) = -2 * (1 + s.val) by ring]
  have hh := BoundaryEntries.finite_length_tail_internal (R := (δ : ℝ)) ht (by exact_mod_cast hδ) H
  rw [← he] at hh
  have hsqrt := Real.sqrt_le_sqrt hh
  rw [Real.sqrt_mul (by positivity : 0 ≤ 1 + 1 / (2 * (1 + s.val) - 1))] at hsqrt
  have hpow : Real.sqrt ((δ : ℝ) ^ (1 - 2 * (1 + s.val))) =
      (δ : ℝ) ^ (-(1 / 2 + s.val)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hδp.le]
    congr 1
    ring
  simpa only [hpow, show 2 * (1 + s.val) - 1 = 1 + 2 * s.val by ring] using hsqrt

/-- See the proof of Proposition 5.15 in the paper: a joint centered coefficient bound
controls any L² representative of the actual exterior row. -/
theorem centered_exterior_norm_joint_internal {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] {ν : Measure Ω}
    (J : Finset ι) (r : Ω → ι → ℝ) (c : Ω → ℝ)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (B : ℝ)
    (hB : ∀ᵐ x ∂ν, Real.sqrt (∑ i ∈ Jᶜ, ((r x i - c x) / w i) ^ 2) +
      Real.sqrt (∑ i ∈ J, (c x / w i) ^ 2) ≤ B)
    (v : ι → Lp ℝ 2 ν) (hv : ∀ᵐ x ∂ν, ∑ i, v i x = 0)
    (f : Lp ℝ 2 ν) (hf : ∀ᵐ x ∂ν, f x = ∑ i ∈ Jᶜ, r x i * v i x) :
    ‖f‖ ≤ B * Real.sqrt (∑ i, (w i * ‖v i‖) ^ 2) := by
  let E := fun x => Real.sqrt (∑ i, (w i * v i x) ^ 2)
  have hE : MemLp E 2 ν := FiniteMixedL2.weighted_memLp w v
  have hscalar (c : ℝ) : Real.sqrt (∑ i ∈ J, (c / w i) ^ 2) =
      |c| * Real.sqrt (∑ i ∈ J, (1 / w i) ^ 2) := by
    simp_rw [show ∀ i, (c / w i) ^ 2 = c ^ 2 * (1 / w i) ^ 2 by intro i; ring]
    rw [← mul_sum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  have hpt : ∀ᵐ x ∂ν, ‖f x‖ ≤ B * ‖hE.toLp E x‖ := by
    filter_upwards [hB, hv, hf, hE.coeFn_toLp] with x hx hz hf he
    have hh := FiniteZeroSumBounds.centered_subset_bound Jᶜ (r x) (fun i => v i x) w (c x)
      (Real.sqrt (∑ i ∈ Jᶜ, ((r x i - c x) / w i) ^ 2))
      (Real.sqrt (∑ i ∈ J, (c x / w i) ^ 2)) hz hw le_rfl
      (by rw [compl_compl, hscalar (c x)])
    rw [hf, he]
    simp only [Real.norm_eq_abs, E, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact hh.trans (mul_le_mul_of_nonneg_right hx (Real.sqrt_nonneg _))
  have hn := Lp.norm_le_mul_norm_of_ae_le_mul (f := f) (g := hE.toLp E) hpt
  have he : ‖hE.toLp E‖ = Real.sqrt (∑ i, (w i * ‖v i‖) ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg (hE.toLp E)), ← CyclicFourierL2.integral_sq]
    rw [integral_congr_ae (hE.coeFn_toLp.mono (fun x hx => congrArg (fun y : ℝ => y ^ 2) hx))]
    exact congrArg Real.sqrt (FiniteMixedL2.weighted_sq_integral w v)
  simpa only [he] using hn

/-- See the proof of Proposition 5.15 in the paper, the centered exterior row geometry:
for the actual window, the two displayed bounds on `U` hold with the global
weighted L² norm on the right. -/
theorem exterior_window_rows (s : Riesz1.RieszExponent) :
    ∃ P₀ P₁ : ℝ, 0 < P₀ ∧ 0 < P₁ ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
      (n m : ℕ+) (hm : 2 ≤ (m : ℕ)) (K : ℕ) (C κ γ ε β : ℝ), 0 ≤ C →
    ∀ (Q : ScalarFormData ν) (M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ),
      PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M →
    ∀ (f : Fin (m : ℕ) → Lp ℝ 2 ν) (u : Fin (m : ℕ) → Q.1),
      WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _) f u →
    ∀ (j i₀ : Fin (m : ℕ)), 16 ≤ Riesz1.cyclicIndexDistance m j i₀ →
    ∃ U : Fin (m : ℕ) → Lp ℝ 2 ν,
      (∀ row, ∀ᵐ x ∂ν, U row x = ∑ i ∈ (LocalizedMatrix.window m j i₀)ᶜ, M x row i * (u i).val x) ∧
      ∀ l : Fin (LocalizedMatrix.windowSize m j i₀ : ℕ),
        let row := LocalizedMatrix.windowEmbedding m j i₀ l
        let R := (Riesz1.cyclicIndexDistance m j i₀ : ℝ)
        let δ := (min (l.val + 1) ((LocalizedMatrix.windowSize m j i₀ : ℕ) - l.val) : ℕ)
        let E := Real.sqrt (∑ i, (weightRadius m i i₀ ^ (3 / 2 - s.val) * ‖(u i).val‖) ^ 2)
        ‖U row‖ ≤ P₀ * (C * (n : ℝ) ^ (κ * ε)) * E *
          (R ^ (-1 : ℝ) + R ^ (-(3 / 2 - s.val)) *
            Real.sqrt (∑ k ∈ Icc δ (4 * Riesz1.cyclicIndexDistance m j i₀), (k : ℝ) ^ (-2 * s.val))) ∧
        ‖U row - U (row - 1)‖ ≤ P₁ * (C * (n : ℝ) ^ (κ * ε)) * E *
          (R ^ (-2 : ℝ) + R ^ (-(3 / 2 - s.val)) * (δ : ℝ) ^ (-(1 / 2 + s.val))) := by
  obtain ⟨P₀, P₁, hP₀, hP₁, hp⟩ := periodized_window_coefficient_bounds s
  let T := Real.sqrt (1 + 1 / (1 + 2 * s.val))
  have hT : 0 ≤ T := Real.sqrt_nonneg _
  refine ⟨P₀, P₁ * (1 + T), hP₀, by positivity, ?_⟩
  intro Ω _ ν n m hm K C κ γ ε β hC Q M hM f u hu j i₀ hR
  let J := LocalizedMatrix.window m j i₀
  obtain ⟨U, hU⟩ := exterior_rows s n m hm K C κ γ ε β hC Q M hM f u hu J i₀
  refine ⟨U, fun row => (hU row).1, ?_⟩
  intro l row R δ E
  let w := fun i => weightRadius m i i₀ ^ (3 / 2 - s.val)
  have hw (i) : 0 < w i := Real.rpow_pos_of_pos (by linarith [one_le_weightRadius m i i₀]) _
  have hz : ∀ᵐ x ∂ν, ∑ i, (u i).val x = 0 := hu.1.1
  have hc := hp ν n m hm K C κ γ ε hC M hM
  have hvalue := centered_exterior_norm_joint_internal J (fun x i => M x row i)
    (fun x => M x row i₀) w hw
    (P₀ * (C * (n : ℝ) ^ (κ * ε)) * (R ^ (-1 : ℝ) + R ^ (-(3 / 2 - s.val)) *
      Real.sqrt (∑ k ∈ Icc δ (4 * Riesz1.cyclicIndexDistance m j i₀), (k : ℝ) ^ (-2 * s.val))))
    (hc.mono (fun x hx => (hx j i₀ hR l).1)) (fun i => (u i).val) hz (U row) (hU row).1
  have hrep : ∀ᵐ x ∂ν, (U row - U (row - 1)) x =
      ∑ i ∈ Jᶜ, (M x row i - M x (row - 1) i) * (u i).val x := by
    filter_upwards [(hU row).1, (hU (row - 1)).1, Lp.coeFn_sub (U row) (U (row - 1))] with x hx hy he
    rw [he, Pi.sub_apply, hx, hy]
    simp only [sub_mul, sum_sub_distrib]
  have hdiff := centered_exterior_norm_joint_internal J
    (fun x i => M x row i - M x (row - 1) i)
    (fun x => M x row i₀ - M x (row - 1) i₀) w hw
    (P₁ * (C * (n : ℝ) ^ (κ * ε)) * (R ^ (-2 : ℝ) + R ^ (-(3 / 2 - s.val)) *
      Real.sqrt (∑ k ∈ Icc δ (4 * Riesz1.cyclicIndexDistance m j i₀), (k : ℝ) ^ (-2 * (1 + s.val)))))
    (hc.mono (fun x hx => (hx j i₀ hR l).2)) (fun i => (u i).val) hz (U row - U (row - 1)) hrep
  have hδ : 1 ≤ δ := by dsimp only [δ]; have := l.isLt; omega
  have htail := square_increment_tail s δ (4 * Riesz1.cyclicIndexDistance m j i₀) hδ
  have hRp : 0 < R := by dsimp only [R]; exact_mod_cast (show 0 < Riesz1.cyclicIndexDistance m j i₀ by omega)
  have hE : 0 ≤ E := Real.sqrt_nonneg _
  have he : 0 ≤ C * (n : ℝ) ^ (κ * ε) := by positivity
  constructor
  · convert hvalue using 1
    ring
  · apply hdiff.trans
    change P₁ * (C * (n : ℝ) ^ (κ * ε)) *
      (R ^ (-2 : ℝ) + R ^ (-(3 / 2 - s.val)) *
        Real.sqrt (∑ k ∈ Icc δ (4 * Riesz1.cyclicIndexDistance m j i₀), (k : ℝ) ^ (-2 * (1 + s.val)))) * E ≤ _
    have hstep := mul_le_mul_of_nonneg_left htail
      (show 0 ≤ R ^ (-(3 / 2 - s.val)) by positivity)
    have hbase : R ^ (-2 : ℝ) + R ^ (-(3 / 2 - s.val)) *
        Real.sqrt (∑ k ∈ Icc δ (4 * Riesz1.cyclicIndexDistance m j i₀), (k : ℝ) ^ (-2 * (1 + s.val))) ≤
      (1 + T) * (R ^ (-2 : ℝ) + R ^ (-(3 / 2 - s.val)) * (δ : ℝ) ^ (-(1 / 2 + s.val))) := by
      have hδp : (0 : ℝ) < δ := by exact_mod_cast (show 0 < δ by omega)
      have hpos := mul_nonneg hT (show 0 ≤ R ^ (-2 : ℝ) by positivity)
      have hpos' : 0 ≤ R ^ (-(3 / 2 - s.val)) * (δ : ℝ) ^ (-(1 / 2 + s.val)) := by positivity
      nlinarith only [hstep, hpos, hpos']
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbase
      (mul_nonneg hP₁.le he)) hE
    convert hh using 1
    ring

/-- See the proof of Proposition 5.15, equation (5.65): the two
exterior-row bounds for a constrained point-source solution, with the common
polynomial loss and compact-temperature uniformity. The ordered increment uses
the minimum of the two endpoint distances and never wraps around the window. -/
theorem constrained_exterior_bounds (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ)
    (hκstar : 0 < κstar) (hγstar : 0 < γstar) (M₀ : ℕ+) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε →
    ∀ Cstar : ℝ, 1 ≤ Cstar →
    ∀ βlo : ℝ, 0 < βlo → ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
      (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
    ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ)),
    2 ≤ (n : ℕ) → (n : ℕ) ≤ (m : ℕ) →
    (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
    let K := ⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ)
    1 ≤ K → 4 * K ≤ (m : ℕ) →
    ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M →
    ∀ β : ℝ, βlo ≤ β → β ≤ βhi →
    ∀ (χ : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _)
      (fun i => if i = i₀ then χ else 0) u →
    ∀ j : Fin (m : ℕ), 16 ≤ Riesz1.cyclicIndexDistance m j i₀ →
    ∃ U : Fin (LocalizedMatrix.windowSize m j i₀ : ℕ) → Lp ℝ 2 ν,
      (∀ l, ∀ᵐ x ∂ν, U l x = ∑ i ∈ (LocalizedMatrix.window m j i₀)ᶜ,
        M x (LocalizedMatrix.windowEmbedding m j i₀ l) i * (u i).val x) ∧
      ∀ l : Fin (LocalizedMatrix.windowSize m j i₀ : ℕ),
        let R := (Riesz1.cyclicIndexDistance m j i₀ : ℝ)
        let δ := min (l.val + 1) ((LocalizedMatrix.windowSize m j i₀ : ℕ) - l.val)
        ‖U l‖ ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ *
          (R ^ (-1 : ℝ) + R ^ (-(3 / 2 - s.val)) *
            Real.sqrt (∑ k ∈ Icc δ (4 * Riesz1.cyclicIndexDistance m j i₀), (k : ℝ) ^ (-2 * s.val))) ∧
        ∀ hl : 0 < l.val,
          let prev : Fin (LocalizedMatrix.windowSize m j i₀ : ℕ) := ⟨l.val - 1, by have := l.isLt; omega⟩
          let δpair := min δ (min (prev.val + 1) ((LocalizedMatrix.windowSize m j i₀ : ℕ) - prev.val))
          ‖U l - U prev‖ ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ *
            (R ^ (-2 : ℝ) + R ^ (-(3 / 2 - s.val)) * (δpair : ℝ) ^ (-(1 / 2 + s.val))) := by
  obtain ⟨κg, hκg, hg⟩ := GlobalDecay.global_decay_bounds hzeta s κstar γstar hκstar hγstar M₀
  obtain ⟨P₀, P₁, hP₀, hP₁, hp⟩ := exterior_window_rows s
  refine ⟨κg + κstar, by positivity, fun ε hε Cstar hCstar βlo hβlo βhi hβhi => ?_⟩
  obtain ⟨Cg, hCg, hg⟩ := hg ε hε Cstar hCstar βlo hβlo βhi hβhi
  refine ⟨(P₀ + P₁) * Cstar * Cg, by positivity, ?_⟩
  intro Ω _ ν _ Q hQ hQc n m hm hn hnm hmn K hK hKm M hM β hβloβ hββhi χ i₀ u hu j hR
  obtain ⟨lam, _, _, henergy, _, _⟩ := hg ν Q hQ hQc n m hm hn hnm hmn hK hKm M hM β hβloβ hββhi χ i₀ u hu
  let E := Real.sqrt (∑ i, (weightRadius m i i₀ ^ (3 / 2 - s.val) * ‖(u i).val‖) ^ 2)
  have hE : E ≤ Cg * (n : ℝ) ^ (κg * ε) * ‖χ‖ :=
    (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans henergy
  obtain ⟨U, hU, hbound⟩ := hp ν n m hm K Cstar κstar γstar ε β (by linarith) Q M hM
    (fun i => if i = i₀ then χ else 0) u hu j i₀ hR
  refine ⟨fun l => U (LocalizedMatrix.windowEmbedding m j i₀ l), fun l => hU _, ?_⟩
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast n.pos
  have hmult (P profile : ℝ) (hP : 0 ≤ P) (hPsum : P ≤ P₀ + P₁) (hprofile : 0 ≤ profile) :
      P * (Cstar * (n : ℝ) ^ (κstar * ε)) * E * profile ≤
        ((P₀ + P₁) * Cstar * Cg) * (n : ℝ) ^ ((κg + κstar) * ε) * ‖χ‖ * profile := by
    calc
      _ ≤ P * (Cstar * (n : ℝ) ^ (κstar * ε)) *
          (Cg * (n : ℝ) ^ (κg * ε) * ‖χ‖) * profile := by gcongr
      _ = P * Cstar * Cg * (n : ℝ) ^ ((κg + κstar) * ε) * ‖χ‖ * profile := by
        rw [show (κg + κstar) * ε = κstar * ε + κg * ε by ring, Real.rpow_add hnreal]
        ring
      _ ≤ _ := by gcongr
  intro l R δ
  have hb := hbound l
  have hRp : 0 < R := by dsimp only [R]; exact_mod_cast (show 0 < Riesz1.cyclicIndexDistance m j i₀ by omega)
  constructor
  · apply hb.1.trans
    exact hmult P₀ _ hP₀.le (by linarith) (by positivity)
  · intro hl prev δpair
    have hprev := windowEmbedding_predecessor m j i₀ l hl
    change LocalizedMatrix.windowEmbedding m j i₀ prev = LocalizedMatrix.windowEmbedding m j i₀ l - 1 at hprev
    change ‖U (LocalizedMatrix.windowEmbedding m j i₀ l) - U (LocalizedMatrix.windowEmbedding m j i₀ prev)‖ ≤ _
    rw [hprev]
    apply hb.2.trans
    have hδpair : 1 ≤ δpair := by dsimp only [δpair, δ, prev]; have := l.isLt; omega
    have hδ : 1 ≤ δ := by dsimp only [δ]; have := l.isLt; omega
    have hδle : (δpair : ℝ) ≤ δ := by exact_mod_cast (min_le_left δ _)
    have hδp : (0 : ℝ) < δpair := by exact_mod_cast (show 0 < δpair by omega)
    have hpower := Real.rpow_le_rpow_of_nonpos hδp hδle
      (show -(1 / 2 + s.val) ≤ 0 by linarith [s.property.1])
    have hh := hmult P₁
      (R ^ (-2 : ℝ) + R ^ (-(3 / 2 - s.val)) * (δ : ℝ) ^ (-(1 / 2 + s.val)))
      hP₁.le (by linarith) (by positivity)
    apply hh.trans
    have hprofile : R ^ (-2 : ℝ) + R ^ (-(3 / 2 - s.val)) * (δ : ℝ) ^ (-(1 / 2 + s.val)) ≤
        R ^ (-2 : ℝ) + R ^ (-(3 / 2 - s.val)) * (δpair : ℝ) ^ (-(1 / 2 + s.val)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hpower
        (show 0 ≤ R ^ (-(3 / 2 - s.val)) by positivity))
    exact mul_le_mul_of_nonneg_left hprofile (by positivity)

end Riesz2.LocalizedField
