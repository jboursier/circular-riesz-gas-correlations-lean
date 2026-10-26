/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.BoundaryEntriesPart2
public import Riesz2.ToMathlib.RpowPartialSums

/-!
# Physical endpoint and diagonal estimates

The endpoint averaging argument in the proof of Lemma 5.6 uses ordinary
endpoints for cyclic intervals. This file proves the physical prefix,
suffix and logarithmic diagonal bounds for the conditional coefficients.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped BigOperators Classical

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.BoundaryEntries

/-- See the proof of Lemma 5.6 in the paper, prefix geometry: a proper
prefix crossing interval starts in the exterior and has the specified ordinary
endpoint after one turn around the ambient cycle. Here `j` is one-based. -/
theorem prefix_crossing_iff (N : ℕ+) {n j r : ℕ}
    (hn : 2 * n ≤ (N : ℕ)) (hj : 0 < j) (hjn : j < n)
    (hr : 2 * r ≤ (N : ℕ)) (i : Fin (N : ℕ)) :
    (¬cyclicIndexInterval N i r ⊆ activeIndices N n ∧
      cyclicIndexInterval N i r ∩ activeIndices N n = activeIndices N j) ↔
      n ≤ i.val ∧ i.val + r = (N : ℕ) + j := by
  constructor
  · rintro ⟨hc, ht⟩
    have hzero : (⟨0, N.pos⟩ : Fin (N : ℕ)) ∈ cyclicIndexInterval N i r := by
      have h := ht.symm ▸ (show (⟨0, N.pos⟩ : Fin (N : ℕ)) ∈ activeIndices N j by
        simp [activeIndices, hj])
      exact (Finset.mem_inter.mp h).1
    have hlast : (⟨j - 1, by omega⟩ : Fin (N : ℕ)) ∈ cyclicIndexInterval N i r := by
      have h := ht.symm ▸ (show (⟨j - 1, by omega⟩ : Fin (N : ℕ)) ∈ activeIndices N j by
        simp only [activeIndices, Finset.mem_filter, Finset.mem_univ, true_and]; omega)
      exact (Finset.mem_inter.mp h).1
    have hnext : (⟨j, by omega⟩ : Fin (N : ℕ)) ∉ cyclicIndexInterval N i r := by
      intro h
      have h' : (⟨j, by omega⟩ : Fin (N : ℕ)) ∈ activeIndices N j :=
        ht ▸ Finset.mem_inter.mpr ⟨h, by simp [activeIndices, hjn]⟩
      simp [activeIndices] at h'
    have hi : n ≤ i.val := by
      by_contra hi
      have hi' : i.val < n := by omega
      have hc' := crossing_active_start N hn hr i hi' hc
      rw [mem_interval_active N hn hr i ⟨0, N.pos⟩ (by simp; omega), ite_eq_left hi'] at hzero
      rw [mem_interval_active N hn hr i ⟨j, by omega⟩ hjn, ite_eq_left hi'] at hnext
      dsimp only at hzero hnext
      omega
    have hi' : ¬i.val < n := by omega
    rw [mem_interval_active N hn hr i ⟨j - 1, by omega⟩ (by simp; omega), ite_eq_right hi'] at hlast
    rw [mem_interval_active N hn hr i ⟨j, by omega⟩ hjn, ite_eq_right hi'] at hnext
    dsimp only at hlast hnext
    exact ⟨hi, by omega⟩
  · rintro ⟨hi, he⟩
    constructor
    · intro hsub
      have hstart : i ∈ cyclicIndexInterval N i r := by
        rw [mem_cyclicIndexInterval_iff N i i (by omega)]
        simp only [sub_self, Fin.val_zero]
        omega
      have h := hsub hstart
      simp only [activeIndices, Finset.mem_filter, Finset.mem_univ, true_and] at h
      omega
    · ext a
      simp only [Finset.mem_inter, activeIndices, Finset.mem_filter,
        Finset.mem_univ, true_and]
      by_cases ha : a.val < n
      · rw [mem_interval_active N hn hr i a ha, ite_eq_right (by omega)]
        omega
      · constructor
        · exact fun h => False.elim (ha h.2)
        · intro h
          omega

/-- See the proof of Lemma 5.6 in the paper: shortening the right
endpoint preserves the prefix crossing family and the short-length carrier.
The start is fixed, so for each target endpoint the map is injective. -/
theorem prefix_shorten_geometry (N : ℕ+) {n j k r : ℕ}
    (hn : 2 * n ≤ (N : ℕ)) (hk : 0 < k) (hkj : k ≤ j) (hjn : j < n)
    (hr : 2 * r ≤ (N : ℕ)) (i : Fin (N : ℕ))
    (hi : n ≤ i.val) (he : i.val + r = (N : ℕ) + j) :
    0 < r - (j - k) ∧ 2 * (r - (j - k)) ≤ (N : ℕ) ∧
      ¬cyclicIndexInterval N i (r - (j - k)) ⊆ activeIndices N n ∧
      cyclicIndexInterval N i (r - (j - k)) ∩ activeIndices N n = activeIndices N k := by
  have hiN := i.isLt
  have hpos : 0 < r - (j - k) := by omega
  have hr' : 2 * (r - (j - k)) ≤ (N : ℕ) := by omega
  exact ⟨hpos, hr', (prefix_crossing_iff N hn hk (by omega) hr' i).mpr
    ⟨hi, by omega⟩⟩

/-- Injectivity of endpoint shortening on the actual interval labels. -/
theorem prefix_shorten_injective (N : ℕ+) {j k : ℕ} (_hkj : k ≤ j) :
    Set.InjOn (fun q : ℕ × Fin (N : ℕ) => (q.1 - (j - k), q.2))
      {q | q.2.val + q.1 = (N : ℕ) + j} := by
  intro a ha b hb hab
  have hi := congrArg Prod.snd hab
  have hr := congrArg Prod.fst hab
  have hai := a.2.isLt
  have hbi := b.2.isLt
  simp only [Set.mem_ofPred_eq] at ha hb
  simp only at hi hr
  apply Prod.ext
  · have hie := congrArg Fin.val hi
    omega
  · exact hi

/-- The cyclic sum is the sum over its actual interval, when no
label repeats. This identity is used before comparing complementary masses. -/
theorem gapSum_eq_interval_sum (N : ℕ+) (i : Fin (N : ℕ)) {r : ℕ}
    (hr : r ≤ (N : ℕ)) (y : Fin (N : ℕ) → ℝ) :
    cyclicGapSum N i r y = ∑ a ∈ cyclicIndexInterval N i r, y a := by
  apply Eq.symm
  apply Finset.sum_image
  intro a ha b hb hab
  have hm : Nat.ModEq (N : ℕ) (i.val + a) (i.val + b) := congrArg Fin.val hab
  have hc := Nat.ModEq.add_left_cancel' i.val hm
  change a % (N : ℕ) = b % (N : ℕ) at hc
  simpa only [Nat.mod_eq_of_lt (lt_of_lt_of_le (Finset.mem_range.mp ha) hr),
    Nat.mod_eq_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hb) hr)] using hc

/-- See the proof of Lemma 5.6 in the paper, removed-mass estimate.
The deleted part is precisely the active segment from `k` through `j-1`,
so exterior gaps need no upper or lower bounds. -/
theorem prefix_removed_mass (N : ℕ+) {n j k r : ℕ}
    (hn : n ≤ (N : ℕ)) (hk : 0 < k) (hkj : k ≤ j) (hjn : j < n)
    (i : Fin (N : ℕ)) (he : i.val + r = (N : ℕ) + j)
    (y : Fin (N : ℕ) → ℝ) (B : ℝ)
    (hy : ∀ a, a.val < n → y a ≤ B) :
    cyclicGapSum N i r y - cyclicGapSum N i (r - (j - k)) y ≤ (j - k : ℕ) * B := by
  have hiN := i.isLt
  have he' : r - (j - k) + (j - k) = r := by omega
  have hsum := Finset.sum_range_add
    (fun t : ℕ => y ⟨(i.val + t) % (N : ℕ), Nat.mod_lt _ N.pos⟩)
    (r - (j - k)) (j - k)
  rw [he'] at hsum
  change cyclicGapSum N i r y = cyclicGapSum N i (r - (j - k)) y + _ at hsum
  rw [hsum, add_sub_cancel_left]
  calc
    _ ≤ ∑ _t ∈ Finset.range (j - k), B := by
      apply Finset.sum_le_sum
      intro t ht
      have ht' := Finset.mem_range.mp ht
      have hmod : (i.val + (r - (j - k) + t)) % (N : ℕ) = k + t := by
        have ha : i.val + (r - (j - k) + t) = (N : ℕ) + (k + t) := by omega
        rw [ha, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      exact hy _ (by simp only [hmod]; omega)
    _ = _ := by simp

/-- See the proof of Lemma 5.6 in the paper, complementary-mass
estimate. A prefix crossing interval misses all the last `n-j` active gaps. -/
theorem prefix_complement_mass (N : ℕ+) {n j r : ℕ}
    (hn : 2 * n ≤ (N : ℕ)) (hjn : j < n) (hr : 2 * r ≤ (N : ℕ))
    (i : Fin (N : ℕ)) (hi : n ≤ i.val) (he : i.val + r = (N : ℕ) + j)
    (y : Fin (N : ℕ) → ℝ) (hy : y ∈ Riesz1.gapSimplex N)
    (b : ℝ) (hb : ∀ a, a.val < n → b ≤ y a) :
    (n - j : ℕ) * b ≤ (N : ℝ) - cyclicGapSum N i r y := by
  let J := cyclicIndexInterval N i r
  have hlow : (n - j : ℕ) * b ≤ ∑ a ∈ Jᶜ, y a := by
    calc
      _ = ∑ _t ∈ Finset.range (n - j), b := by simp
      _ ≤ ∑ a ∈ Jᶜ, y a := by
        apply Finset.sum_le_sum_of_injOn
          (fun t : ℕ => (⟨(j + t) % (N : ℕ), Nat.mod_lt _ N.pos⟩ : Fin (N : ℕ)))
        · intro t ht u hu htu
          have ht' := Finset.mem_range.mp ht
          have hu' := Finset.mem_range.mp hu
          have h := congrArg Fin.val htu
          simp only [Nat.mod_eq_of_lt (show j + t < (N : ℕ) by omega),
            Nat.mod_eq_of_lt (show j + u < (N : ℕ) by omega)] at h
          omega
        · intro a ha
          obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ha
          have ht' := Finset.mem_range.mp ht
          rw [Finset.mem_compl]
          change _ ∉ cyclicIndexInterval N i r
          rw [mem_interval_active N hn hr i _ (by
            simp only [Nat.mod_eq_of_lt (show j + t < (N : ℕ) by omega)]
            omega), ite_eq_right (by omega)]
          simp only [Nat.mod_eq_of_lt (show j + t < (N : ℕ) by omega)]
          omega
        · intro t ht
          apply hb
          have ht' := Finset.mem_range.mp ht
          simp only [Nat.mod_eq_of_lt (show j + t < (N : ℕ) by omega)]
          omega
        · intro a _ _
          exact (hy.1 a).le
  have htotal := Finset.sum_add_sum_compl J y
  rw [hy.2] at htotal
  rw [gapSum_eq_interval_sum N i (by omega)]
  change _ ≤ (N : ℝ) - ∑ a ∈ J, y a
  linarith

/-- Internal form of the uniform complementary-mass comparison used in
the proof of Lemma 5.6. It uses cutoffs only on the
active coordinates, and holds for every positive exterior. -/
theorem prefix_mass_ratio (N : ℕ+) {n j k r : ℕ}
    (hn : 2 * n ≤ (N : ℕ)) (hk : 0 < k) (hkj : k ≤ j) (hjn : j < n)
    (hq : j - k ≤ n - j) (hr : 2 * r ≤ (N : ℕ))
    (i : Fin (N : ℕ)) (hi : n ≤ i.val) (he : i.val + r = (N : ℕ) + j)
    (ε : ℝ) (y : Fin (N : ℕ) → ℝ) (hy : y ∈ Riesz1.gapSimplex N)
    (hb : ∀ a, a.val < n → (n : ℝ) ^ (-ε) ≤ y a ∧ y a ≤ (n : ℝ) ^ ε) :
    (N : ℝ) - cyclicGapSum N i (r - (j - k)) y ≤
      (1 + (n : ℝ) ^ (2 * ε)) * ((N : ℝ) - cyclicGapSum N i r y) := by
  apply complementary_mass_ratio (q := (j - k : ℕ)) (by exact_mod_cast (show 0 < n by omega))
  · exact prefix_removed_mass N (by omega) hk hkj hjn i he y _ (fun a ha => (hb a ha).2)
  · calc
      _ ≤ (n - j : ℕ) * (n : ℝ) ^ (-ε) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hq) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ ≤ _ := prefix_complement_mass N hn hjn hr i hi he y hy _ (fun a ha => (hb a ha).1)

/-- See the proof of Lemma 5.6 in the paper, the actual good-event
shortening comparison, after conditional expectation. The mass comparison follows from the good event. -/
theorem conditional_prefix_shortening (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (ε κ₀ : ℝ) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (hx : x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀)
    {j k : ℕ} (hk : 0 < k) (hkj : k ≤ j) (hjn : j < (n : ℕ))
    (hq : j - k ≤ (n : ℕ) - j)
    (r : Fin (((n : ℕ) + m + 1) / 2)) (i : Fin ((n : ℕ) + m + 1))
    (hi : (n : ℕ) ≤ i.val) (he : i.val + (r.val + 1) = (n : ℕ) + m + 1 + j) :
    (1 + (n : ℝ) ^ (2 * ε)) ^ (-s.val - 2) * conditionalIntervalWeight β s n m r i x ≤
      2 * conditionalIntervalWeight β s n m ⟨r.val - (j - k), by omega⟩ i x := by
  apply conditionalIntervalWeight_shortening β s n m x r _ i _
    (by have := Real.rpow_nonneg (show (0 : ℝ) ≤ n by positivity) (2 * ε); linarith)
    (by dsimp; omega)
  intro z hz
  have hb (a : Fin ((n : ℕ) + m + 1)) (ha : a.val < (n : ℕ)) :
      (n : ℝ) ^ (-ε) ≤ RetainedSimplex.chart n m ((n + m : ℕ) + 1)
          (Equiv.refl _) (x.val, z) a ∧
        RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val, z) a ≤ (n : ℝ) ^ ε := by
    let b : Fin (n : ℕ) := ⟨a.val, ha⟩
    have hemb : a = (b.castAdd m).castSucc := Fin.ext rfl
    have hc := RetainedSimplex.chart_retained n m ((n + m : ℕ) + 1) (Equiv.refl _) x.val z b
    simp only [Equiv.refl_apply] at hc
    rw [hemb, hc]
    exact hx.1.1 b
  have hh := prefix_mass_ratio ((n : ℕ) + m).succPNat hn hk hkj hjn hq
    (by have := r.isLt; simp only [Nat.succPNat_coe]; omega) i hi he ε _ hz hb
  have hl : r.val - (j - k) + 1 = r.val + 1 - (j - k) := by
    have hiN := i.isLt
    omega
  simpa only [Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, hl] using hh

/-- Internal finite-sum step of endpoint averaging. The shortening injection
compares sums over the prefix interval families. -/
theorem prefix_sum_shortening_internal (N : ℕ+) {n j k : ℕ}
    (hn : 2 * n ≤ (N : ℕ)) (hk : 0 < k) (hkj : k ≤ j) (hjn : j < n)
    (w : Fin ((N : ℕ) / 2) → Fin (N : ℕ) → ℝ) (hw : ∀ r i, 0 ≤ w r i)
    (A : ℝ)
    (hcmp : ∀ (r : Fin ((N : ℕ) / 2)) (i : Fin (N : ℕ)),
      n ≤ i.val → i.val + (r.val + 1) = (N : ℕ) + j →
        A * w r i ≤ 2 * w ⟨r.val - (j - k), by omega⟩ i) :
    A * (∑ r, ∑ i, if n ≤ i.val ∧ i.val + (r.val + 1) = (N : ℕ) + j then w r i else 0) ≤
      2 * (∑ r, ∑ i, if n ≤ i.val ∧ i.val + (r.val + 1) = (N : ℕ) + k then w r i else 0) := by
  let S : Finset (Fin ((N : ℕ) / 2) × Fin (N : ℕ)) :=
    Finset.univ.filter fun q => n ≤ q.2.val ∧ q.2.val + (q.1.val + 1) = (N : ℕ) + j
  let T : Finset (Fin ((N : ℕ) / 2) × Fin (N : ℕ)) :=
    Finset.univ.filter fun q => n ≤ q.2.val ∧ q.2.val + (q.1.val + 1) = (N : ℕ) + k
  let e : Fin ((N : ℕ) / 2) × Fin (N : ℕ) → Fin ((N : ℕ) / 2) × Fin (N : ℕ) :=
    fun q => (⟨q.1.val - (j - k), by have := q.1.isLt; omega⟩, q.2)
  have hh : (∑ q ∈ S, A * w q.1 q.2) ≤ ∑ q ∈ T, 2 * w q.1 q.2 := by
    apply Finset.sum_le_sum_of_injOn e
    · intro a ha b hb hab
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      have hi := congrArg (fun q => q.2.val) hab
      dsimp only [e] at hi
      apply Prod.ext
      · apply Fin.ext
        omega
      · simpa only [e] using congrArg Prod.snd hab
    · intro a ha
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
      have hq' := (Finset.mem_filter.mp hq).2
      have hiN := q.2.isLt
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, e]
      exact ⟨hq'.1, by omega⟩
    · intro q hq
      have hq' := (Finset.mem_filter.mp hq).2
      exact hcmp q.1 q.2 hq'.1 hq'.2
    · intro a _ _
      exact mul_nonneg (by norm_num) (hw a.1 a.2)
  simpa only [S, T, Finset.sum_filter, ← Finset.mul_sum, Fintype.sum_prod_type,
    mul_ite, mul_zero] using hh

/-- See the proof of Lemma 5.6 in the paper, summed physical prefix
comparison on the actual good event, uniformly over all positive exterior fibres. -/
theorem physicalPrefix_shortening (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (ε κ₀ : ℝ) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (hx : x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀)
    (j k : Fin ((n : ℕ) - 1)) (hkj : k.val ≤ j.val)
    (hq : j.val - k.val ≤ (n : ℕ) - (j.val + 1)) :
    (1 + (n : ℝ) ^ (2 * ε)) ^ (-s.val - 2) * physicalPrefix β s n m x j ≤
      2 * physicalPrefix β s n m x k := by
  have hp (a : Fin ((n : ℕ) - 1)) (r : Fin (((n : ℕ) + m + 1) / 2))
      (i : Fin ((n : ℕ) + m + 1)) :
      (¬cyclicIndexInterval ((n : ℕ) + m).succPNat i (r.val + 1) ⊆
          activeIndices ((n : ℕ) + m).succPNat n ∧
        cyclicIndexInterval ((n : ℕ) + m).succPNat i (r.val + 1) ∩
          activeIndices ((n : ℕ) + m).succPNat n =
            activeIndices ((n : ℕ) + m).succPNat (a.val + 1)) ↔
        (n : ℕ) ≤ i.val ∧ i.val + (r.val + 1) = (n : ℕ) + m + 1 + (a.val + 1) :=
    prefix_crossing_iff ((n : ℕ) + m).succPNat hn (by omega)
      (by have := a.isLt; omega) (by have := r.isLt; simp only [Nat.succPNat_coe]; omega) i
  unfold physicalPrefix physicalGroup
  simp_rw [hp]
  apply prefix_sum_shortening_internal ((n : ℕ) + m).succPNat hn
    (by omega : 0 < k.val + 1) (by omega : k.val + 1 ≤ j.val + 1)
    (by have := j.isLt; omega)
    (fun r i => conditionalIntervalWeight β s n m r i x)
    (fun r i => conditionalIntervalWeight_nonneg β s n m r i x)
  intro r i hi he
  exact conditional_prefix_shortening β s n m hn ε κ₀ x hx (by omega)
    (by omega) (by have := j.isLt; omega) (by omega) r i hi he

/-- See the proof of Lemma 5.6 in the paper, positivity step in the
prefix averaging argument. All the distinct shortened prefixes contribute to
the entry between the first label and the shortest endpoint. -/
theorem physicalPrefix_segment_le_hessian (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (j : Fin ((n : ℕ) - 1)) {h : ℕ} (hh : h ≤ j.val) :
    (∑ t : Fin (h + 1), physicalPrefix β s n m x ⟨j.val - t.val, by omega⟩) ≤
      GoodBlocks.conditionalHessian β s n m ⟨0, n.pos⟩ ⟨j.val - h, by omega⟩ x := by
  let u := physicalPrefix β s n m x
  have hsum : (∑ t : Fin (h + 1), u ⟨j.val - t.val, by omega⟩) ≤
      ∑ a : Fin ((n : ℕ) - 1), if j.val - h ≤ a.val then u a else 0 := by
    apply Finset.sum_le_sum_of_injOn (fun t : Fin (h + 1) =>
      (⟨j.val - t.val, by omega⟩ : Fin ((n : ℕ) - 1)))
    · intro a _ b _ hab
      have ha := a.isLt
      have hb := b.isLt
      have he := congrArg Fin.val hab
      apply Fin.ext
      dsimp only at he
      omega
    · exact Finset.subset_univ _
    · intro t _
      rw [ite_eq_left (by have := t.isLt; dsimp; omega)]
    · intro a _ _
      split_ifs
      · exact physicalGroup_nonneg β s n m x _
      · exact le_rfl
  have hcross := physicalCrossing_le_hessian β s n m x
    ⟨0, n.pos⟩ ⟨j.val - h, by omega⟩
  rw [physicalCrossing_grouped β s n m hn x, groupedBoundaryMatrix_apply] at hcross
  simp only [Nat.zero_le, true_and, Nat.not_lt_zero, false_and,
    ↓reduceIte, Finset.sum_const_zero, add_zero] at hcross
  exact hsum.trans ((le_add_of_nonneg_left (physicalGroup_nonneg β s n m x (activeIndices ((n : ℕ) + m).succPNat n))).trans hcross)

/-- See the proof of Lemma 5.6 in the paper, averaged prefix estimate
before the elementary power bookkeeping. This is on the literal good event
and uses its actual conditional Hessian entry bound. -/
theorem physicalPrefix_averaged (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (ε κ₀ : ℝ) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (hx : x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀)
    (j : Fin ((n : ℕ) - 1)) {h : ℕ} (hh : h ≤ j.val)
    (hh' : h ≤ (n : ℕ) - (j.val + 1)) :
    (h + 1 : ℝ) * ((1 + (n : ℝ) ^ (2 * ε)) ^ (-s.val - 2) * physicalPrefix β s n m x j) ≤
      2 * ((n : ℝ) ^ (κ₀ * ε) * (j.val - h + 1 : ℝ) ^ (-s.val)) := by
  have hav : (h + 1 : ℝ) * ((1 + (n : ℝ) ^ (2 * ε)) ^ (-s.val - 2) *
      physicalPrefix β s n m x j) ≤
      2 * (∑ t : Fin (h + 1), physicalPrefix β s n m x ⟨j.val - t.val, by omega⟩) := by
    calc
      _ = ∑ _t : Fin (h + 1), (1 + (n : ℝ) ^ (2 * ε)) ^ (-s.val - 2) *
          physicalPrefix β s n m x j := by simp
      _ ≤ ∑ t : Fin (h + 1), 2 * physicalPrefix β s n m x ⟨j.val - t.val, by omega⟩ := by
        apply Finset.sum_le_sum
        intro t _
        exact physicalPrefix_shortening β s n m hn ε κ₀ x hx j ⟨j.val - t.val, by omega⟩ (by dsimp; omega)
          (by have := t.isLt; dsimp; omega)
      _ = _ := (Finset.mul_sum ..).symm
  have hdist : Riesz1.cyclicIndexDistance ((n : ℕ) + m).succPNat
      ((⟨0, n.pos⟩ : Fin (n : ℕ)).castAdd m).castSucc
      ((⟨j.val - h, by omega⟩ : Fin (n : ℕ)).castAdd m).castSucc = j.val - h := by
    simp only [Riesz1.cyclicIndexDistance, Fin.val_castSucc, Fin.val_castAdd,
      Nat.dist, Nat.zero_sub, Nat.sub_zero, zero_add, Nat.succPNat_coe]
    have := j.isLt
    omega
  have hentry := hx.2 (⟨0, n.pos⟩ : Fin (n : ℕ)) ⟨j.val - h, by omega⟩
  rw [hdist] at hentry
  have hcast : 1 + ((j.val - h : ℕ) : ℝ) = (j.val : ℝ) - h + 1 := by
    rw [Nat.cast_sub hh]
    ring
  rw [hcast] at hentry
  exact hav.trans (mul_le_mul_of_nonneg_left
    ((physicalPrefix_segment_le_hessian β s n m hn x j hh).trans hentry) (by norm_num))

/-- Internal power bookkeeping for the proof of Lemma 5.6. On `0<s<1` the shortening cost is at
most `8 n^(6ε)`, so its loss exponent is independent of temperature and ε. -/
theorem prefix_averaging_power_internal (s : Riesz1.RieszExponent) (n : ℕ+)
    (ε κ₀ U : ℝ) (hε : 0 ≤ ε) (hU : 0 ≤ U) (j : Fin ((n : ℕ) - 1))
    (hav : ∀ h : ℕ, h ≤ j.val → h ≤ (n : ℕ) - (j.val + 1) →
      (h + 1 : ℝ) * ((1 + (n : ℝ) ^ (2 * ε)) ^ (-s.val - 2) * U) ≤
        2 * ((n : ℝ) ^ (κ₀ * ε) * (j.val - h + 1 : ℝ) ^ (-s.val))) :
    U ≤ 128 * (n : ℝ) ^ ((κ₀ + 6) * ε) * (j.val + 1 : ℝ) ^ (-s.val) *
      ((min (j.val + 1) ((n : ℕ) - j.val) : ℕ) : ℝ)⁻¹ := by
  let h := min j.val ((n : ℕ) - (j.val + 1)) / 4
  have hj := j.isLt
  have hh : h ≤ j.val := by dsimp [h]; omega
  have hh' : h ≤ (n : ℕ) - (j.val + 1) := by dsimp [h]; omega
  have hsmall : 2 * h ≤ j.val + 1 := by dsimp [h]; omega
  have hdepth : min (j.val + 1) ((n : ℕ) - j.val) ≤ 4 * (h + 1) := by dsimp [h]; omega
  have hn : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hB : 1 ≤ (n : ℝ) ^ (2 * ε) := Real.one_le_rpow hn1 (by linarith)
  let A := 1 + (n : ℝ) ^ (2 * ε)
  have hA : 1 ≤ A := by dsimp [A]; linarith
  have hAp : 0 < A := by linarith
  have hcost : A ^ (s.val + 2) ≤ 8 * (n : ℝ) ^ (6 * ε) := by
    calc
      _ ≤ A ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le hA (by linarith [s.property.2])
      _ = A ^ (3 : ℕ) := Real.rpow_natCast A 3
      _ ≤ 8 * ((n : ℝ) ^ (2 * ε)) ^ (3 : ℕ) := by dsimp [A]; nlinarith [sq_nonneg ((n : ℝ) ^ (2 * ε) - 1)]
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
        congr 2
        ring
  have hc : A ^ (s.val + 2) * A ^ (-s.val - 2) = 1 := by
    rw [← Real.rpow_add hAp, show s.val + 2 + (-s.val - 2) = 0 by ring, Real.rpow_zero]
  have hJ : 0 < (j.val + 1 : ℝ) := by positivity
  have hM : 0 < (j.val : ℝ) - h + 1 := by exact_mod_cast (show (0 : ℤ) < (j.val : ℤ) - h + 1 by omega)
  have hspatial : (j.val - h + 1 : ℝ) ^ (-s.val) ≤ 2 * (j.val + 1 : ℝ) ^ (-s.val) := by
    have hr : (j.val + 1 : ℝ) / 2 ≤ (j.val : ℝ) - h + 1 := by
      have hhR : (2 : ℝ) * h ≤ j.val + 1 := by exact_mod_cast hsmall
      linarith
    have hhpow := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (j.val + 1 : ℝ) / 2)
      hr (by linarith [s.property.1] : -s.val ≤ 0)
    have htwo : (2 : ℝ) ^ s.val ≤ 2 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 2) s.property.2.le
    rw [Real.div_rpow hJ.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      div_inv_eq_mul] at hhpow
    exact hhpow.trans (by simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left htwo (Real.rpow_nonneg hJ.le (-s.val)))
  have ha := mul_le_mul_of_nonneg_left (hav h hh hh')
    (Real.rpow_nonneg hAp.le (s.val + 2))
  change A ^ (s.val + 2) * ((h + 1 : ℝ) * (A ^ (-s.val - 2) * U)) ≤ _ at ha
  have heleft : A ^ (s.val + 2) * ((h + 1 : ℝ) * (A ^ (-s.val - 2) * U)) = (h + 1 : ℝ) * U := by
    calc
      _ = (h + 1 : ℝ) * (A ^ (s.val + 2) * A ^ (-s.val - 2)) * U := by ring
      _ = _ := by rw [hc]; ring
  rw [heleft] at ha
  have hnexp : (n : ℝ) ^ (6 * ε) * (n : ℝ) ^ (κ₀ * ε) =
      (n : ℝ) ^ ((κ₀ + 6) * ε) := by rw [← Real.rpow_add hn]; congr 1; ring
  have hbound : (h + 1 : ℝ) * U ≤
      32 * (n : ℝ) ^ ((κ₀ + 6) * ε) * (j.val + 1 : ℝ) ^ (-s.val) := by
    calc
      _ ≤ A ^ (s.val + 2) * (2 * ((n : ℝ) ^ (κ₀ * ε) * (j.val - h + 1 : ℝ) ^ (-s.val))) := ha
      _ ≤ (8 * (n : ℝ) ^ (6 * ε)) *
          (2 * ((n : ℝ) ^ (κ₀ * ε) * (2 * (j.val + 1 : ℝ) ^ (-s.val)))) := by
        apply mul_le_mul hcost ?_ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hspatial (by positivity)) (by norm_num)
      _ = _ := by rw [show (8 * (n : ℝ) ^ (6 * ε)) *
          (2 * ((n : ℝ) ^ (κ₀ * ε) * (2 * (j.val + 1 : ℝ) ^ (-s.val)))) =
            32 * ((n : ℝ) ^ (6 * ε) * (n : ℝ) ^ (κ₀ * ε)) * (j.val + 1 : ℝ) ^ (-s.val) by ring, hnexp]
  have hdR : (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) ≤ (4 : ℝ) * (h + 1) := by
    exact_mod_cast hdepth
  have hδ : (0 : ℝ) < (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) := by
    exact_mod_cast (show 0 < min (j.val + 1) ((n : ℕ) - j.val) by omega)
  rw [← div_eq_mul_inv, le_div_iff₀ hδ]
  nlinarith [mul_le_mul_of_nonneg_right hdR hU]

/-- The physical prefix clause of the proof of Lemma 5.6. The explicit loss `κ₀+6` precedes ε
and is independent of inverse temperature. -/
theorem physical_prefix_bound (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (ε κ₀ : ℝ) (hε : 0 ≤ ε) (n : ℕ+) (m : ℕ)
    (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (hx : x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀) (j : Fin ((n : ℕ) - 1)) :
    physicalPrefix β s n m x j ≤
      128 * (n : ℝ) ^ ((κ₀ + 6) * ε) * (j.val + 1 : ℝ) ^ (-s.val) *
        ((min (j.val + 1) ((n : ℕ) - j.val) : ℕ) : ℝ)⁻¹ := by
  exact prefix_averaging_power_internal s n ε κ₀ _ hε
    (physicalGroup_nonneg β s n m x _) j
    (fun h hh hh' => physicalPrefix_averaged β s n m hn ε κ₀ x hx j hh hh')

/-- See the proof of Lemma 5.6 in the paper, suffix geometry. A proper
suffix crossing interval starts at its first active label and extends past
the active window. Half-cycle lengths prevent wraparound. -/
theorem suffix_crossing_iff (N : ℕ+) {n j r : ℕ}
    (hn : 2 * n ≤ (N : ℕ)) (hj : 0 < j) (hjn : j < n)
    (hr : 2 * r ≤ (N : ℕ)) (i : Fin (N : ℕ)) :
    (¬cyclicIndexInterval N i r ⊆ activeIndices N n ∧
      cyclicIndexInterval N i r ∩ activeIndices N n =
        (activeIndices N n).filter (fun a : Fin (N : ℕ) => j ≤ a.val)) ↔
      i.val = j ∧ n < i.val + r := by
  constructor
  · rintro ⟨hc, ht⟩
    have hjmem : (⟨j, by omega⟩ : Fin (N : ℕ)) ∈ cyclicIndexInterval N i r := by
      have h := ht.symm ▸ (show (⟨j, by omega⟩ : Fin (N : ℕ)) ∈
        (activeIndices N n).filter (fun a : Fin (N : ℕ) => j ≤ a.val) by simp [activeIndices, hjn])
      exact (Finset.mem_inter.mp h).1
    have hprev : (⟨j - 1, by omega⟩ : Fin (N : ℕ)) ∉ cyclicIndexInterval N i r := by
      intro h
      have hh := ht ▸ Finset.mem_inter.mpr ⟨h,
        show (⟨j - 1, by omega⟩ : Fin (N : ℕ)) ∈ activeIndices N n by
          simp only [activeIndices, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩
      simp only [Finset.mem_filter] at hh
      omega
    have hi : i.val < n := by
      by_contra hi
      rw [mem_interval_active N hn hr i _ hjn, ite_eq_right (by omega)] at hjmem
      rw [mem_interval_active N hn hr i ⟨j - 1, by omega⟩ (by dsimp; omega),
        ite_eq_right (by omega)] at hprev
      dsimp only at hjmem hprev
      omega
    have hext := crossing_active_start N hn hr i hi hc
    rw [mem_interval_active N hn hr i _ hjn, ite_eq_left hi] at hjmem
    rw [mem_interval_active N hn hr i ⟨j - 1, by omega⟩ (by dsimp; omega),
      ite_eq_left hi] at hprev
    dsimp only at hjmem hprev
    exact ⟨by omega, hext⟩
  · rintro ⟨hi, hext⟩
    have hc : ¬cyclicIndexInterval N i r ⊆ activeIndices N n := by
      intro hs
      have hnN : n < (N : ℕ) := by omega
      have hm : (⟨n, hnN⟩ : Fin (N : ℕ)) ∈ cyclicIndexInterval N i r := by
        rw [mem_cyclicIndexInterval_iff N i _ (by omega), Fin.val_sub]
        have hmod : ((N : ℕ) - i.val + n) % (N : ℕ) = n - i.val := by
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
        dsimp only
        rw [hmod]
        omega
      have hh := hs hm
      simp [activeIndices] at hh
    exact ⟨hc, by simpa only [hi] using crossing_active_trace N hn hr i (by omega) hc⟩

/-- Splitting a cyclic sum at a specified new start, without changing its
ambient period. This is used to shorten a suffix from the left. -/
theorem gapSum_split_start (N : ℕ+) (i i' : Fin (N : ℕ)) {q r : ℕ}
    (he : i'.val = i.val + q) (y : Fin (N : ℕ) → ℝ) :
    cyclicGapSum N i (q + r) y = cyclicGapSum N i q y + cyclicGapSum N i' r y := by
  unfold cyclicGapSum
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  apply Fin.ext
  dsimp only
  rw [he, Nat.add_assoc]

/-- See the proof of Lemma 5.6 in the paper, suffix removed-mass
estimate: only the active initial `q` gaps are deleted. -/
theorem suffix_removed_mass (N : ℕ+) {n r q : ℕ}
    (_hn : n ≤ (N : ℕ)) (hq : q ≤ r) (i i' : Fin (N : ℕ))
    (hi' : i'.val < n) (he : i'.val = i.val + q)
    (y : Fin (N : ℕ) → ℝ) (B : ℝ) (hy : ∀ a, a.val < n → y a ≤ B) :
    cyclicGapSum N i r y - cyclicGapSum N i' (r - q) y ≤ q * B := by
  have hsplit := gapSum_split_start N i i' he (r := r - q) y
  rw [Nat.add_sub_of_le hq] at hsplit
  rw [hsplit, add_sub_cancel_right]
  calc
    _ ≤ ∑ _t ∈ Finset.range q, B := by
      apply Finset.sum_le_sum
      intro t ht
      apply hy
      have ht' := Finset.mem_range.mp ht
      dsimp only
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    _ = _ := by simp

/-- See the proof of Lemma 5.6 in the paper, suffix complement bound:
all the active labels preceding its start are outside the interval. -/
theorem suffix_complement_mass (N : ℕ+) {n r : ℕ}
    (hn : 2 * n ≤ (N : ℕ)) (hr : 2 * r ≤ (N : ℕ))
    (i : Fin (N : ℕ)) (hi : i.val < n)
    (y : Fin (N : ℕ) → ℝ) (hy : y ∈ Riesz1.gapSimplex N)
    (b : ℝ) (hb : ∀ a, a.val < n → b ≤ y a) :
    (i.val : ℝ) * b ≤ (N : ℝ) - cyclicGapSum N i r y := by
  let J := cyclicIndexInterval N i r
  have hlow : (i.val : ℝ) * b ≤ ∑ a ∈ Jᶜ, y a := by
    calc
      _ = ∑ _t ∈ Finset.range i.val, b := by simp
      _ ≤ ∑ a ∈ Jᶜ, y a := by
        apply Finset.sum_le_sum_of_injOn
          (fun t : ℕ => (⟨t % (N : ℕ), Nat.mod_lt _ N.pos⟩ : Fin (N : ℕ)))
        · intro t ht u hu htu
          have ht' := Finset.mem_range.mp ht
          have hu' := Finset.mem_range.mp hu
          have h := congrArg Fin.val htu
          simp only [Nat.mod_eq_of_lt (show t < (N : ℕ) by omega),
            Nat.mod_eq_of_lt (show u < (N : ℕ) by omega)] at h
          exact h
        · intro a ha
          obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ha
          have ht' := Finset.mem_range.mp ht
          rw [Finset.mem_compl]
          change _ ∉ cyclicIndexInterval N i r
          rw [mem_interval_active N hn hr i _ (by
            dsimp only; rw [Nat.mod_eq_of_lt (by omega)]; omega), ite_eq_left hi]
          simp only [Nat.mod_eq_of_lt (show t < (N : ℕ) by omega)]
          omega
        · intro t ht
          apply hb
          have ht' := Finset.mem_range.mp ht
          dsimp only
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        · intro a _ _
          exact (hy.1 a).le
  have htotal := Finset.sum_add_sum_compl J y
  rw [hy.2] at htotal
  rw [gapSum_eq_interval_sum N i (by omega)]
  change _ ≤ (N : ℝ) - ∑ a ∈ J, y a
  linarith

/-- Internal complementary-mass comparison for left shortening of a suffix,
the reflected geometric step in the proof of Lemma 5.6. -/
theorem suffix_mass_ratio (N : ℕ+) {n r q : ℕ}
    (hn : 2 * n ≤ (N : ℕ)) (hr : 2 * r ≤ (N : ℕ)) (hq : q ≤ r)
    (i i' : Fin (N : ℕ)) (hi' : i'.val < n) (he : i'.val = i.val + q)
    (hqi : q ≤ i.val) (ε : ℝ) (y : Fin (N : ℕ) → ℝ)
    (hy : y ∈ Riesz1.gapSimplex N)
    (hb : ∀ a, a.val < n → (n : ℝ) ^ (-ε) ≤ y a ∧ y a ≤ (n : ℝ) ^ ε) :
    (N : ℝ) - cyclicGapSum N i' (r - q) y ≤
      (1 + (n : ℝ) ^ (2 * ε)) * ((N : ℝ) - cyclicGapSum N i r y) := by
  apply complementary_mass_ratio (q := (q : ℝ)) (by exact_mod_cast (show 0 < n by omega))
  · exact suffix_removed_mass N (by omega) hq i i' hi' he y _ (fun a ha => (hb a ha).2)
  · calc
      _ ≤ (i.val : ℝ) * (n : ℝ) ^ (-ε) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hqi) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ ≤ _ := suffix_complement_mass N hn hr i (by omega) y hy _ (fun a ha => (hb a ha).1)

/-- Internal two-start version of physical shortening. Interval coefficients
depend on their masses, and their multiplicities remain between one and two.
This permits deletion at either endpoint in the proof of Lemma 5.6. -/
theorem intervalWeight_shortening_mass_internal (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (N : ℕ+) (r r' : Fin ((N : ℕ) / 2))
    (i i' : Fin (N : ℕ)) (y : EuclideanSpace ℝ (Fin (N : ℕ)))
    (hy : WithLp.ofLp y ∈ Riesz1.gapSimplex N) (A : ℝ) (hA : 1 ≤ A)
    (hshort : cyclicGapSum N i' (r'.val + 1) (WithLp.ofLp y) ≤
      cyclicGapSum N i (r.val + 1) (WithLp.ofLp y))
    (hcomp : (N : ℝ) - cyclicGapSum N i' (r'.val + 1) (WithLp.ofLp y) ≤
      A * ((N : ℝ) - cyclicGapSum N i (r.val + 1) (WithLp.ofLp y))) :
    A ^ (-s.val - 2) * intervalWeight s N r i y ≤ 2 * intervalWeight s N r' i' y := by
  let L : {L : ℝ // 0 < L ∧ L < (N : ℝ)} :=
    ⟨cyclicGapSum N i (r.val + 1) (WithLp.ofLp y),
      PhysicalEnergy.gapSum_mem N i (by omega)
        (lt_of_le_of_lt (Nat.succ_le_of_lt r.isLt)
          (Nat.div_lt_self N.pos (by norm_num))) _ hy⟩
  let L' : {L : ℝ // 0 < L ∧ L < (N : ℝ)} :=
    ⟨cyclicGapSum N i' (r'.val + 1) (WithLp.ofLp y),
      PhysicalEnergy.gapSum_mem N i' (by omega)
        (lt_of_le_of_lt (Nat.succ_le_of_lt r'.isLt)
          (Nat.div_lt_self N.pos (by norm_num))) _ hy⟩
  have h := intervalCoefficient_shortening (ofLong β s) N L L' A hA hshort hcomp
  change A ^ (-s.val - 2) * PhysicalEnergy.intervalCoefficient (ofLong β s) N L ≤
    PhysicalEnergy.intervalCoefficient (ofLong β s) N L' at h
  rw [intervalWeight_physical β s N r i y hy, intervalWeight_physical β s N r' i' y hy]
  have hp := (PhysicalEnergy.intervalCoefficient_pos (ofLong β s) N L).le
  have hp' := (PhysicalEnergy.intervalCoefficient_pos (ofLong β s) N L').le
  have hpow : 0 ≤ A ^ (-s.val - 2) := Real.rpow_nonneg (by linarith) _
  split_ifs <;> nlinarith [mul_nonneg hpow hp]

/-- See the proof of Lemma 5.6 in the paper: the actual conditional
coefficient comparison for suffix shortening, with its mass hypotheses
discharged by the good event for every positive exterior. -/
theorem conditional_suffix_shortening (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (ε κ₀ : ℝ) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (hx : x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀)
    (r : Fin (((n : ℕ) + m + 1) / 2)) (i i' : Fin ((n : ℕ) + m + 1))
    (q : ℕ) (hi' : i'.val < (n : ℕ)) (he : i'.val = i.val + q)
    (hqi : q ≤ i.val) (hext : (n : ℕ) < i.val + (r.val + 1)) :
    (1 + (n : ℝ) ^ (2 * ε)) ^ (-s.val - 2) * conditionalIntervalWeight β s n m r i x ≤
      2 * conditionalIntervalWeight β s n m ⟨r.val - q, by omega⟩ i' x := by
  have hlen : r.val - q + 1 = r.val + 1 - q := by omega
  unfold conditionalIntervalWeight
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_mono_ae
    ((integrable_intervalWeight β s n m x r i).const_mul _)
    ((integrable_intervalWeight β s n m x ⟨r.val - q, by omega⟩ i').const_mul _)
  filter_upwards [ConditionalEnergyMoments.physical_conditional_support
    (ofLong β s) n m n.pos (Equiv.refl _) x] with z hz
  let y := RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val, z)
  have hy : WithLp.ofLp y ∈ Riesz1.gapSimplex ((n : ℕ) + m).succPNat := by
    have hd := (Set.ext_iff.mp (RetainedSimplex.fibre_domain n m _ x.property) z).mpr hz
    have h := (RetainedSimplex.chart_mem_simplex n m _ (Equiv.refl _) _).mpr hd
    exact ⟨h.1, by simpa only [Nat.succPNat_coe, Nat.cast_succ] using h.2⟩
  have hb (a : Fin ((n : ℕ) + m + 1)) (ha : a.val < (n : ℕ)) :
      (n : ℝ) ^ (-ε) ≤ y a ∧ y a ≤ (n : ℝ) ^ ε := by
    let b : Fin (n : ℕ) := ⟨a.val, ha⟩
    have hemb : a = (b.castAdd m).castSucc := Fin.ext rfl
    have hc := RetainedSimplex.chart_retained n m ((n + m : ℕ) + 1) (Equiv.refl _) x.val z b
    simp only [Equiv.refl_apply] at hc
    change (n : ℝ) ^ (-ε) ≤ y a ∧ y a ≤ (n : ℝ) ^ ε
    simpa only [hemb, y, hc] using hx.1.1 b
  apply intervalWeight_shortening_mass_internal β s ((n : ℕ) + m).succPNat r _ i i' y hy _
    (by have := Real.rpow_nonneg (show (0 : ℝ) ≤ n by positivity) (2 * ε); linarith)
  · have hsplit := gapSum_split_start ((n : ℕ) + m).succPNat i i' he
      (r := r.val + 1 - q) (WithLp.ofLp y)
    rw [Nat.add_sub_of_le (show q ≤ r.val + 1 by omega)] at hsplit
    change cyclicGapSum ((n : ℕ) + m).succPNat i' (r.val - q + 1) _ ≤
      cyclicGapSum ((n : ℕ) + m).succPNat i (r.val + 1) _
    rw [hlen, hsplit]
    exact le_add_of_nonneg_left (Finset.sum_nonneg (fun t _ => (hy.1 _).le))
  · have hh := suffix_mass_ratio ((n : ℕ) + m).succPNat hn
      (by have := r.isLt; simp only [Nat.succPNat_coe]; omega)
      (by omega : q ≤ r.val + 1) i i' hi' he hqi ε _ hy hb
    simpa only [Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, hlen] using hh

/-- The actual suffix family is a single start for each admissible length
(Subsection 5.1 and the proof of Lemma 5.6). -/
theorem physicalSuffix_eq_sum (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (j : Fin ((n : ℕ) - 1)) :
    physicalSuffix β s n m x j = ∑ r : Fin (((n : ℕ) + m + 1) / 2),
      if (n : ℕ) < j.val + 1 + (r.val + 1) then
        conditionalIntervalWeight β s n m r ⟨j.val + 1, by omega⟩ x else 0 := by
  unfold physicalSuffix physicalGroup
  apply Finset.sum_congr rfl
  intro r _
  have ht : ((activeIndices ((n : ℕ) + m).succPNat n).filter fun a => j.val < a.val) =
      (activeIndices ((n : ℕ) + m).succPNat n).filter (fun a => j.val + 1 ≤ a.val) := by
    apply Finset.filter_congr
    intro a _
    exact Nat.lt_iff_add_one_le
  have hshape (i : Fin ((n : ℕ) + m + 1)) :
      (¬cyclicIndexInterval ((n : ℕ) + m).succPNat i (r.val + 1) ⊆
          activeIndices ((n : ℕ) + m).succPNat n ∧
        cyclicIndexInterval ((n : ℕ) + m).succPNat i (r.val + 1) ∩
          activeIndices ((n : ℕ) + m).succPNat n =
            (activeIndices ((n : ℕ) + m).succPNat n).filter (fun a => j.val < a.val)) ↔
        i.val = j.val + 1 ∧ (n : ℕ) < i.val + (r.val + 1) := by
    rw [ht]
    exact suffix_crossing_iff ((n : ℕ) + m).succPNat hn
      (by omega : 0 < j.val + 1) (by have := j.isLt; omega)
      (by have := r.isLt; simp only [Nat.succPNat_coe]; omega) i
  rw [Finset.sum_eq_single (⟨j.val + 1, by omega⟩ : Fin ((n : ℕ) + m + 1))]
  · have hc := hshape (⟨j.val + 1, by omega⟩ : Fin ((n : ℕ) + m + 1))
    simp only [true_and] at hc
    exact ite_congr (propext hc) (fun _ => rfl) (fun _ => rfl)
  · intro b _ hb
    have hb' : b.val ≠ j.val + 1 := fun h => hb (Fin.ext h)
    exact ite_eq_right (fun hc => hb' ((hshape b).mp hc).1)
  · simp

/-- Summed suffix shortening on the actual good event. Its injection fixes
the ordinary far endpoint and deletes active gaps at the start, as required
by the proof of Lemma 5.6. -/
theorem physicalSuffix_shortening (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (ε κ₀ : ℝ) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (hx : x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀)
    (j k : Fin ((n : ℕ) - 1)) (hjk : j.val ≤ k.val) (hq : k.val - j.val ≤ j.val + 1) :
    (1 + (n : ℝ) ^ (2 * ε)) ^ (-s.val - 2) * physicalSuffix β s n m x j ≤
      2 * physicalSuffix β s n m x k := by
  rw [physicalSuffix_eq_sum β s n m hn x, physicalSuffix_eq_sum β s n m hn x]
  let S : Finset (Fin (((n : ℕ) + m + 1) / 2)) :=
    Finset.univ.filter fun r => (n : ℕ) < j.val + 1 + (r.val + 1)
  let T : Finset (Fin (((n : ℕ) + m + 1) / 2)) :=
    Finset.univ.filter fun r => (n : ℕ) < k.val + 1 + (r.val + 1)
  let e : Fin (((n : ℕ) + m + 1) / 2) → Fin (((n : ℕ) + m + 1) / 2) :=
    fun r => ⟨r.val - (k.val - j.val), by have := r.isLt; omega⟩
  have hh : (∑ r ∈ S, (1 + (n : ℝ) ^ (2 * ε)) ^ (-s.val - 2) *
      conditionalIntervalWeight β s n m r ⟨j.val + 1, by omega⟩ x) ≤
      ∑ r ∈ T, 2 * conditionalIntervalWeight β s n m r ⟨k.val + 1, by omega⟩ x := by
    apply Finset.sum_le_sum_of_injOn e
    · intro a ha b hb hab
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      have hk := k.isLt
      have he := congrArg Fin.val hab
      dsimp only [e] at he
      apply Fin.ext
      omega
    · intro a ha
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ha
      have hr' := (Finset.mem_filter.mp hr).2
      have hk := k.isLt
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, e]
      omega
    · intro r hr
      have hr' := (Finset.mem_filter.mp hr).2
      apply conditional_suffix_shortening β s n m hn ε κ₀ x hx r
        ⟨j.val + 1, by omega⟩ ⟨k.val + 1, by omega⟩ (k.val - j.val)
      · have := k.isLt; dsimp; omega
      · dsimp; omega
      · exact hq
      · exact hr'
    · intro r _ _
      exact mul_nonneg (by norm_num) (conditionalIntervalWeight_nonneg β s n m r _ x)
  simpa only [S, T, Finset.sum_filter, mul_ite, mul_zero, Finset.mul_sum] using hh

/-- Positivity step in suffix averaging: every shortened suffix contributes
to the entry between the last active label and the shortest suffix start. -/
theorem physicalSuffix_segment_le_hessian (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (j : Fin ((n : ℕ) - 1)) {h : ℕ} (hh : j.val + h < (n : ℕ) - 1) :
    (∑ t : Fin (h + 1), physicalSuffix β s n m x ⟨j.val + t.val, by omega⟩) ≤
      GoodBlocks.conditionalHessian β s n m ⟨(n : ℕ) - 1, by have := n.pos; omega⟩
        ⟨j.val + h + 1, by omega⟩ x := by
  let v := physicalSuffix β s n m x
  have hsum : (∑ t : Fin (h + 1), v ⟨j.val + t.val, by omega⟩) ≤
      ∑ a : Fin ((n : ℕ) - 1), if a.val < j.val + h + 1 then v a else 0 := by
    apply Finset.sum_le_sum_of_injOn (fun t : Fin (h + 1) =>
      (⟨j.val + t.val, by omega⟩ : Fin ((n : ℕ) - 1)))
    · intro a _ b _ hab
      have he := congrArg Fin.val hab
      apply Fin.ext
      dsimp only at he
      omega
    · exact Finset.subset_univ _
    · intro t _
      rw [ite_eq_left (by have := t.isLt; dsimp; omega)]
    · intro a _ _
      split_ifs
      · exact physicalGroup_nonneg β s n m x _
      · exact le_rfl
  have hcross := physicalCrossing_le_hessian β s n m x
    ⟨(n : ℕ) - 1, by have := n.pos; omega⟩ ⟨j.val + h + 1, by omega⟩
  rw [physicalCrossing_grouped β s n m hn x, groupedBoundaryMatrix_apply] at hcross
  have hp (a : Fin ((n : ℕ) - 1)) : ¬(n : ℕ) - 1 ≤ a.val := by have := a.isLt; omega
  have hs (a : Fin ((n : ℕ) - 1)) : a.val < (n : ℕ) - 1 := a.isLt
  simp only [hp, false_and, hs, true_and, ↓reduceIte, Finset.sum_const_zero, add_zero] at hcross
  exact hsum.trans ((le_add_of_nonneg_left
    (physicalGroup_nonneg β s n m x (activeIndices ((n : ℕ) + m).succPNat n))).trans hcross)

/-- The physical suffix clause of the proof of Lemma 5.6, with an explicit temperature-independent
loss exponent. The denominator is the depth of the label after the cut. -/
theorem physical_suffix_bound (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (ε κ₀ : ℝ) (hε : 0 ≤ ε) (n : ℕ+) (m : ℕ)
    (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (hx : x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀) (j : Fin ((n : ℕ) - 1)) :
    physicalSuffix β s n m x j ≤
      128 * (n : ℝ) ^ ((κ₀ + 6) * ε) * ((n : ℝ) - j.val - 1) ^ (-s.val) *
        ((min (j.val + 2) ((n : ℕ) - (j.val + 1)) : ℕ) : ℝ)⁻¹ := by
  let b : Fin ((n : ℕ) - 1) := ⟨(n : ℕ) - (j.val + 2), by have := j.isLt; omega⟩
  have hb : (b.val + 1 : ℝ) = (n : ℝ) - j.val - 1 := by
    have hj := j.isLt
    dsimp [b]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hδ : min (b.val + 1) ((n : ℕ) - b.val) =
      min (j.val + 2) ((n : ℕ) - (j.val + 1)) := by
    have hj := j.isLt
    dsimp [b]
    omega
  rw [← hb, ← hδ]
  apply prefix_averaging_power_internal s n ε κ₀ _ hε
    (physicalGroup_nonneg β s n m x _) b
  intro h hh hh'
  have hj := j.isLt
  have hcut : j.val + h < (n : ℕ) - 1 := by dsimp [b] at hh; omega
  have hq : h ≤ j.val + 1 := by dsimp [b] at hh'; omega
  have hav : (h + 1 : ℝ) * ((1 + (n : ℝ) ^ (2 * ε)) ^ (-s.val - 2) *
      physicalSuffix β s n m x j) ≤
      2 * GoodBlocks.conditionalHessian β s n m ⟨(n : ℕ) - 1, by have := n.pos; omega⟩
        ⟨j.val + h + 1, by omega⟩ x := by
    calc
      _ = ∑ _t : Fin (h + 1), (1 + (n : ℝ) ^ (2 * ε)) ^ (-s.val - 2) *
          physicalSuffix β s n m x j := by simp
      _ ≤ ∑ t : Fin (h + 1), 2 * physicalSuffix β s n m x ⟨j.val + t.val, by omega⟩ := by
        apply Finset.sum_le_sum
        intro t _
        exact physicalSuffix_shortening β s n m hn ε κ₀ x hx j
          ⟨j.val + t.val, by omega⟩ (by dsimp; omega) (by have := t.isLt; dsimp; omega)
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left
          (physicalSuffix_segment_le_hessian β s n m hn x j hcut) (by norm_num)
  have hd : Riesz1.cyclicIndexDistance ((n : ℕ) + m).succPNat
      ((⟨(n : ℕ) - 1, by have := n.pos; omega⟩ : Fin (n : ℕ)).castAdd m).castSucc
      ((⟨j.val + h + 1, by omega⟩ : Fin (n : ℕ)).castAdd m).castSucc =
        (n : ℕ) - (j.val + h + 2) := by
    simp only [Riesz1.cyclicIndexDistance, Fin.val_castSucc, Fin.val_castAdd,
      Nat.dist, Nat.succPNat_coe]
    omega
  have hentry := hx.2 (⟨(n : ℕ) - 1, by have := n.pos; omega⟩ : Fin (n : ℕ))
    ⟨j.val + h + 1, by omega⟩
  have heq : 1 + (((n : ℕ) - (j.val + h + 2) : ℕ) : ℝ) = (b.val : ℝ) - h + 1 := by
    dsimp [b]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hd, heq] at hentry
  exact hav.trans (mul_le_mul_of_nonneg_left hentry (by norm_num))

/-- Internal logarithmic endpoint sum for
the proof of Lemma 5.6. All depths are positive, including at
the two boundary labels and for a one-label window. -/
theorem sum_boundary_depth_inv_le (n : ℕ+) :
    (∑ i : Fin (n : ℕ), ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ)⁻¹) ≤
      2 * (1 + Real.log (n : ℝ)) := by
  let H := ∑ i : Fin (n : ℕ), (1 + (i.val : ℝ))⁻¹
  have hs : (∑ i : Fin (n : ℕ), ((n : ℝ) - i.val)⁻¹) ≤ H := by
    apply Finset.sum_le_sum_of_injOn (fun i : Fin (n : ℕ) => i.rev)
    · intro a _ b _ hab
      have hh := congrArg Fin.val hab
      simp only [Fin.val_rev] at hh
      apply Fin.ext
      have ha := a.isLt
      have hb := b.isLt
      omega
    · exact Finset.subset_univ _
    · intro i _
      have he : 1 + (i.rev.val : ℝ) = (n : ℝ) - i.val := by
        simp only [Fin.val_rev]
        rw [Nat.cast_sub (by have := i.isLt; omega)]
        push_cast
        ring
      rw [he]
    · intro a _ _
      positivity
  have hH : H ≤ 1 + Real.log (n : ℝ) := by
    simpa only [H, Finset.sum_range] using (sum_range_one_add_inv_le_one_add_log (K := (n : ℕ)))
  calc
    _ ≤ ∑ i : Fin (n : ℕ), ((1 + (i.val : ℝ))⁻¹ + ((n : ℝ) - i.val)⁻¹) := by
      apply Finset.sum_le_sum
      intro i _
      have hi := i.isLt
      have hc : ((n - i.val : ℕ) : ℝ) = (n : ℝ) - i.val := by
        exact Nat.cast_sub (by omega)
      rcases le_total (i.val + 1) ((n : ℕ) - i.val) with h | h
      · rw [Nat.min_eq_left h, Nat.cast_add, Nat.cast_one]
        simpa only [add_comm] using le_add_of_nonneg_right
          (inv_nonneg.mpr (sub_nonneg.mpr (by exact_mod_cast hi.le)))
      · rw [Nat.min_eq_right h, hc]
        exact le_add_of_nonneg_left (by positivity)
    _ ≤ 2 * H := by rw [Finset.sum_add_distrib]; linarith
    _ ≤ _ := by linarith

/-- Internal summation step of the proof of Lemma 5.6. The
endpoint coefficient bounds imply the diagonal bound by summing reciprocal
boundary depths. -/
theorem grouped_diagonal_bound_internal (s : Riesz1.RieszExponent) (n : ℕ+)
    (u v : Fin ((n : ℕ) - 1) → ℝ) (d E : ℝ) (hE : 0 ≤ E)
    (hu : ∀ b, u b ≤ E * (b.val + 1 : ℝ) ^ (-s.val) *
      ((min (b.val + 1) ((n : ℕ) - b.val) : ℕ) : ℝ)⁻¹)
    (hv : ∀ b, v b ≤ E * ((n : ℝ) - b.val - 1) ^ (-s.val) *
      ((min (b.val + 2) ((n : ℕ) - (b.val + 1)) : ℕ) : ℝ)⁻¹)
    (hd : d ≤ E * (n : ℝ) ^ (-s.val)) (i : Fin (n : ℕ)) :
    groupedBoundaryMatrix n u v d i i ≤ E * (5 + 4 * Real.log (n : ℝ)) *
      ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val) := by
  let D (a : Fin (n : ℕ)) : ℝ := ((min (a.val + 1) ((n : ℕ) - a.val) : ℕ) : ℝ)
  have hDp (a : Fin (n : ℕ)) : 0 < D a := by
    dsimp [D]
    exact_mod_cast (show 0 < min (a.val + 1) ((n : ℕ) - a.val) by have := a.isLt; omega)
  let Q := E * (D i) ^ (-s.val)
  have hQ : 0 ≤ Q := mul_nonneg hE (Real.rpow_nonneg (hDp i).le _)
  have hpre : (∑ b : Fin ((n : ℕ) - 1), if i.val ≤ b.val then u b else 0) ≤
      Q * ∑ a : Fin (n : ℕ), (D a)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum_of_injOn
      (fun b : Fin ((n : ℕ) - 1) => (⟨b.val, by omega⟩ : Fin (n : ℕ)))
    · intro a _ b _ hab
      have he := congrArg Fin.val hab
      exact Fin.ext he
    · exact Finset.subset_univ _
    · intro b _
      by_cases hi : i.val ≤ b.val
      · rw [ite_eq_left hi]
        have hpow : (b.val + 1 : ℝ) ^ (-s.val) ≤ (D i) ^ (-s.val) := by
          apply Real.rpow_le_rpow_of_nonpos (hDp i)
          · dsimp [D]
            exact_mod_cast (show min (i.val + 1) ((n : ℕ) - i.val) ≤ b.val + 1 by omega)
          · linarith [s.property.1]
        exact (hu b).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow hE) (inv_nonneg.mpr (hDp (⟨b.val, by omega⟩ : Fin (n : ℕ))).le))
      · rw [ite_eq_right hi]
        exact mul_nonneg hQ (inv_nonneg.mpr (hDp _).le)
    · intro a _ _
      exact mul_nonneg hQ (inv_nonneg.mpr (hDp _).le)
  have hsuf : (∑ b : Fin ((n : ℕ) - 1), if b.val < i.val then v b else 0) ≤
      Q * ∑ a : Fin (n : ℕ), (D a)⁻¹ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum_of_injOn
      (fun b : Fin ((n : ℕ) - 1) => (⟨b.val + 1, by omega⟩ : Fin (n : ℕ)))
    · intro a _ b _ hab
      have hh := congrArg Fin.val hab
      apply Fin.ext
      dsimp only at hh
      omega
    · exact Finset.subset_univ _
    · intro b _
      by_cases hi : b.val < i.val
      · rw [ite_eq_left hi]
        have hpow : ((n : ℝ) - b.val - 1) ^ (-s.val) ≤ (D i) ^ (-s.val) := by
          apply Real.rpow_le_rpow_of_nonpos (hDp i)
          · have hh : min (i.val + 1) ((n : ℕ) - i.val) + b.val + 1 ≤ (n : ℕ) := by
              have := i.isLt
              omega
            have hhR : D i + b.val + 1 ≤ (n : ℝ) := by dsimp [D]; exact_mod_cast hh
            linarith
          · linarith [s.property.1]
        exact (hv b).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow hE) (inv_nonneg.mpr (hDp (⟨b.val + 1, by omega⟩ : Fin (n : ℕ))).le))
      · rw [ite_eq_right hi]
        exact mul_nonneg hQ (inv_nonneg.mpr (hDp _).le)
    · intro a _ _
      exact mul_nonneg hQ (inv_nonneg.mpr (hDp _).le)
  have hd' : d ≤ Q := by
    apply hd.trans
    apply mul_le_mul_of_nonneg_left _ hE
    apply Real.rpow_le_rpow_of_nonpos (hDp i)
    · dsimp [D]
      exact_mod_cast (show min (i.val + 1) ((n : ℕ) - i.val) ≤ (n : ℕ) by have := i.isLt; omega)
    · linarith [s.property.1]
  have hsum := mul_le_mul_of_nonneg_left (sum_boundary_depth_inv_le n) hQ
  rw [groupedBoundaryMatrix_apply]
  simp only [and_self]
  change _ ≤ E * (5 + 4 * Real.log (n : ℝ)) * (D i) ^ (-s.val)
  have he : E * (5 + 4 * Real.log (n : ℝ)) * (D i) ^ (-s.val) =
      Q * (5 + 4 * Real.log (n : ℝ)) := by dsimp [Q]; ring
  rw [he]
  linarith

/-- The full physical diagonal clause of the proof of Lemma 5.6, including `n=1`. This uses the actual
good event and the density-defined crossing block, with loss `κ₀+6`. -/
theorem physical_diagonal_bound (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (ε κ₀ : ℝ) (hε : 0 ≤ ε) (n : ℕ+) (m : ℕ)
    (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (hx : x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀) (i : Fin (n : ℕ)) :
    physicalCrossing β s n m x i i ≤
      (128 * (5 / Real.log 2 + 4)) * (n : ℝ) ^ ((κ₀ + 6) * ε) *
        Real.log (2 * (n : ℝ)) *
          ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  let E := 128 * (n : ℝ) ^ ((κ₀ + 6) * ε)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hfull : physicalFull β s n m x ≤ E * (n : ℝ) ^ (-s.val) := by
    apply (physical_full_bound β s n m hn ε κ₀ x hx).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hn0.le _)
    have he : (n : ℝ) ^ (κ₀ * ε) ≤ (n : ℝ) ^ ((κ₀ + 6) * ε) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith)
    exact he.trans (le_mul_of_one_le_left (Real.rpow_nonneg hn0.le _) (by norm_num))
  have hdiag := grouped_diagonal_bound_internal s n _ _ _ E hE
    (physical_prefix_bound β s ε κ₀ hε n m hn x hx)
    (physical_suffix_bound β s ε κ₀ hε n m hn x hx) hfull i
  rw [← physicalCrossing_grouped β s n m hn x] at hdiag
  have hlog : 5 + 4 * Real.log (n : ℝ) ≤
      (5 / Real.log 2 + 4) * Real.log (2 * (n : ℝ)) := by
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0.ne']
    have hc : 5 / Real.log 2 * Real.log 2 = 5 := div_mul_cancel₀ _ h2.ne'
    nlinarith [mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 5) h2.le) hln]
  apply hdiag.trans
  calc
    _ ≤ E * ((5 / Real.log 2 + 4) * Real.log (2 * (n : ℝ))) *
        ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hE) (by positivity)
    _ = _ := by dsimp [E]; ring

end Riesz2.BoundaryEntries
