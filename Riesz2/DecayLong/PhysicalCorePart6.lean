/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.PhysicalCorePart5
public import Riesz2.DecayLong.LocalizedMatrixPart2

/-!
# Active entry errors for the physical core

Coefficient and entry estimates for the proof of Lemma 5.4, retaining
both physical and reference antipodal multiplicities.
-/

public section
noncomputable section

open MeasureTheory Set
open scoped BigOperators Classical MatrixOrder

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.PhysicalCore.Internal

/-- A short-interval signed sum has the entry decay obtained by counting
all cyclic intervals containing the pair. Restrictions on its starts can
only decrease the positive majorant. -/
theorem signed_interval_entry_bound (N : ℕ+) {t B : ℝ} (ht : 0 < t) (hB : 0 ≤ B)
    (F : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → ℝ)
    (hF : ∀ i r, |F i r| ≤ B * (r.val + 1 : ℝ) ^ (-t - 2))
    (a b : Fin (N : ℕ)) :
    |∑ i, ∑ r, F i r * (if a ∈ cyclicIndexInterval N i (r.val + 1) then 1 else 0) *
        (if b ∈ cyclicIndexInterval N i (r.val + 1) then 1 else 0)| ≤
      B * (1 + 1 / t) * (1 + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-t) := by
  let w (i : Fin (N : ℕ)) (r : Fin ((N : ℕ) / 2)) : ℝ :=
    (if a ∈ cyclicIndexInterval N i (r.val + 1) then 1 else 0) *
      (if b ∈ cyclicIndexInterval N i (r.val + 1) then 1 else 0)
  have hw (i) (r) : 0 ≤ w i r := by dsimp only [w]; positivity
  have he (r : Fin ((N : ℕ) / 2)) :
      (∑ i, w i r) = ((r.val + 1 - Riesz1.cyclicIndexDistance N a b : ℕ) : ℝ) :=
    cyclicIndexInterval_pair_count N (by have := r.isLt; omega) a b
  calc
    _ = |∑ r, ∑ i, F i r * w i r| := by
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [w]
      ring
    _ ≤ ∑ r, ∑ i, |F i r| * w i r := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro r _
      exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by
        simp only [abs_mul, abs_of_nonneg (hw _ _)])
    _ ≤ ∑ r, ∑ i, (B * (r.val + 1 : ℝ) ^ (-t - 2)) * w i r :=
      Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (hF i r) (hw i r)
    _ = B * ∑ r : Fin ((N : ℕ) / 2),
        ((r.val + 1 - Riesz1.cyclicIndexDistance N a b : ℕ) : ℝ) *
          (r.val + 1 : ℝ) ^ (-t - 2) := by
      simp_rw [← Finset.mul_sum, he]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (interval_pair_weight_le ht (Riesz1.cyclicIndexDistance N a b) ((N : ℕ) / 2)) hB

/-- The proof of Lemma 5.4: at equal
periods, the paper degree first supplies rigidity uniformly above the
cutoff, then Taylor and the unit-gap comparison give the improved profile.
Bounded lengths cover the remaining forcing scales uniformly in epsilon.
Other degrees use the general relative-deviation bound. -/
theorem internal_same_period_error (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M₀ : ℕ) (β : InverseTemperature)
      (n : ℕ+) (m : ℕ) (_hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
      (ε κ₀ : ℝ), 0 ≤ ε → ε ≤ (1 - s.val / 2) / 2 → 0 ≤ κ₀ →
      ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)),
        x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀ →
        ∀ (i : Fin ((n : ℕ) + m + 1)) (r : Fin (((n : ℕ) + m + 1) / 2)),
          IntervalBoundary.IsInternal ((n : ℕ) + m).succPNat n (i,r) →
          |BoundaryEntries.conditionalIntervalWeight β s n m r i x -
            BoundaryEntries.referenceWeight s ((n : ℕ) + m).succPNat (by have := n.pos; dsimp only [Nat.succPNat_coe]; omega)
              (⌊(n : ℝ) ^ ε⌋₊ ^ M₀) (i,r)| ≤
            C * (n : ℝ) ^ ((κ₀ + s.val + 3 + (M₀ : ℝ)) * ε) *
              (r.val + 1 : ℝ) ^ (-3 - s.val / 2) := by
  obtain ⟨D,hD,hphys⟩ := internal_coefficient_good_upper s
  obtain ⟨E,hE,htaylor⟩ := internal_coefficient_sampled_error s
  obtain ⟨B,hB,href⟩ := BoundaryEntries.referenceWeight_bound s
  let C := 512 * (D + B + E)
  have hC : 0 < C := by dsimp only [C]; linarith
  refine ⟨C,hC,fun M₀ β n m hn ε κ₀ hε hεa hκ₀ x hx i r hi => ?_⟩
  let N := ((n : ℕ) + m).succPNat
  let R : ℝ := r.val + 1
  let U := κ₀ + s.val + 2
  let K := ⌊(n : ℝ) ^ ε⌋₊ ^ M₀
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by positivity
  have hR : 1 ≤ R := by dsimp only [R]; exact_mod_cast (show 1 ≤ r.val+1 by omega)
  have hR0 : 0 < R := by linarith
  have hU : 0 ≤ U := by dsimp only [U]; linarith [s.property.1]
  have hpow : 1 ≤ (n : ℝ) ^ (U * ε) := Real.one_le_rpow hn1 (mul_nonneg hU hε)
  have hq : 0 ≤ R ^ (-s.val - 2) := Real.rpow_nonneg hR0.le _
  have hbase : |BoundaryEntries.conditionalIntervalWeight β s n m r i x -
      BoundaryEntries.referenceWeight s N (by have := n.pos; dsimp only [N,Nat.succPNat_coe]; omega) K (i,r)| ≤
      (D + B) * (n : ℝ) ^ (U * ε) * R ^ (-s.val - 2) := by
    have hp := hphys β n m hn ε κ₀ hε hεa hκ₀ x hx r i hi
    have hb := href N (by have := n.pos; dsimp only [N,Nat.succPNat_coe]; omega) K (i,r)
    have hb' := (mul_le_mul_of_nonneg_left hpow hB.le)
    have hb'' := mul_le_mul_of_nonneg_right hb' hq
    have hnP := BoundaryEntries.conditionalIntervalWeight_nonneg β s n m r i x
    have hnB := BoundaryEntries.referenceWeight_nonneg s N (by have := n.pos; dsimp only [N,Nat.succPNat_coe]; omega) K (i,r)
    have hab := abs_sub_le (BoundaryEntries.conditionalIntervalWeight β s n m r i x) 0
      (BoundaryEntries.referenceWeight s N (by have := n.pos; dsimp only [N,Nat.succPNat_coe]; omega) K (i,r))
    simp only [sub_zero, zero_sub, abs_neg, abs_of_nonneg hnP, abs_of_nonneg hnB] at hab
    simp only [Nat.cast_add,Nat.cast_one] at hp
    change _ ≤ D * (n : ℝ) ^ (U * ε) * R ^ (-s.val - 2) at hp
    change _ ≤ B * R ^ (-s.val - 2) at hb
    nlinarith only [hab,hp,hb,hb'']
  have hmon (v : ℝ) (hv : v ≤ U + 1 + M₀) :
      (n : ℝ) ^ (v * ε) ≤ (n : ℝ) ^ ((U + 1 + M₀) * ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (mul_le_mul_of_nonneg_right hv hε)
  rw [show κ₀ + s.val + 3 + (M₀ : ℝ) = U + 1 + M₀ by dsimp only [U]; ring]
  change _ ≤ C * (n : ℝ) ^ ((U + 1 + M₀) * ε) * R ^ (-3 - s.val / 2)
  by_cases hK : K ≤ r.val + 1
  · have hcases : (n : ℝ) ^ ε * R ^ (s.val / 2) ≤ R / 2 ∨
        R ^ (1 - s.val / 2) ≤ 256 * (n : ℝ) ^ ε := by
      have hq : 1 ≤ (n : ℝ) ^ ε := Real.one_le_rpow hn1 hε
      by_cases hpaper : M₀ = (paperReferenceCutoffExponent s : ℕ)
      · have hcut : (⌊(n : ℝ) ^ ε⌋₊ ^ (paperReferenceCutoffExponent s : ℕ) : ℕ) ≤ R := by
          dsimp only [R]
          have hh : ⌊(n : ℝ) ^ ε⌋₊ ^ (paperReferenceCutoffExponent s : ℕ) ≤ r.val + 1 := by
            simpa only [K, hpaper] using hK
          exact_mod_cast hh
        rcases paper_cutoff_taylor_or_bounded s hq hR hcut with ht | hb
        · exact Or.inl ht
        · exact Or.inr (hb.trans (by linarith))
      · by_cases ht : (n : ℝ) ^ ε * R ^ (s.val / 2) ≤ R / 2
        · exact Or.inl ht
        · right
          have hmul : R ^ (1 - s.val / 2) * R ^ (s.val / 2) = R := by
            rw [← Real.rpow_add hR0]
            norm_num
          have hp := Real.rpow_pos_of_pos hR0 (s.val / 2)
          have hh : R ^ (1 - s.val / 2) ≤ 2 * (n : ℝ) ^ ε := by
            nlinarith only [lt_of_not_ge ht, hmul, hp]
          exact hh.trans (by linarith)
    rcases hcases with hsmall | hscale
    · have hh := htaylor β n m hn N (by have := n.pos; dsimp only [N,Nat.succPNat_coe]; omega) (by simp only [N,Nat.succPNat_coe]; omega) ε κ₀ x hx r i hi
        (by have := r.isLt; simp only [N,Nat.succPNat_coe]; omega) (by simpa only [Nat.cast_add,Nat.cast_one] using hsmall)
      have he : BoundaryEntries.referenceWeight s N (by have := n.pos; dsimp only [N,Nat.succPNat_coe]; omega) K (i,r) =
          (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
            sampledSecondDifference s N (by have := n.pos; dsimp only [N,Nat.succPNat_coe]; omega) ⟨r.val + 1, by
              have := r.isLt; simp only [N,Nat.succPNat_coe]; omega⟩ := by
        simp only [BoundaryEntries.referenceWeight, hK, ite_true,
          Nat.mod_eq_of_lt (show r.val+1 < (N : ℕ) by have := r.isLt; dsimp only [N,Nat.succPNat_coe]; omega)]
        split_ifs <;> ring
      rw [he]
      simp only [Nat.cast_add,Nat.cast_one,show ((n : ℕ)+m).succPNat = N from rfl,ite_true] at hh
      change |_| ≤ E * ((n : ℝ) ^ ε * R ^ (-3 - s.val / 2) + R ^ (-s.val - 4) + 0) at hh
      have hdec : R ^ (-s.val - 4) ≤ R ^ (-3 - s.val / 2) :=
        Real.rpow_le_rpow_of_exponent_le hR (by linarith [s.property.1])
      have hnε : 1 ≤ (n : ℝ) ^ ε := Real.one_le_rpow hn1 hε
      have hpε := hmon 1 (by have := Nat.cast_nonneg M₀ (α := ℝ); linarith)
      simp only [one_mul] at hpε
      have hmajor : (n : ℝ) ^ ε * R ^ (-3 - s.val / 2) + R ^ (-s.val - 4) ≤
          2 * (n : ℝ) ^ ((U + 1 + M₀) * ε) * R ^ (-3 - s.val / 2) := by
        nlinarith only [hdec, mul_le_mul_of_nonneg_right hpε (Real.rpow_nonneg hR0.le (-3-s.val/2)),
          mul_le_mul_of_nonneg_right hnε (Real.rpow_nonneg hR0.le (-3-s.val/2))]
      apply hh.trans
      dsimp only [C]
      nlinarith [mul_le_mul_of_nonneg_left hmajor hE.le,
        mul_nonneg (show 0 ≤ D+B by linarith) (mul_nonneg
          (Real.rpow_nonneg hn0.le ((U+1+M₀)*ε)) (Real.rpow_nonneg hR0.le (-3-s.val/2)))]
    · have he : R ^ (1 - s.val / 2) * R ^ (-3 - s.val / 2) = R ^ (-s.val - 2) := by
        rw [← Real.rpow_add hR0]; congr 1; ring
      have hh := mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg hR0.le (-3-s.val/2))
      rw [he] at hh
      have hprod := mul_le_mul_of_nonneg_left hh
        (mul_nonneg (show 0 ≤ D+B by linarith) (Real.rpow_nonneg hn0.le (U*ε)))
      have heN : (n : ℝ) ^ (U * ε) * (n : ℝ) ^ ε = (n : ℝ) ^ ((U+1)*ε) := by
        rw [← Real.rpow_add hn0]; congr 1; ring
      have hprod' : (D+B) * (n : ℝ) ^ (U*ε) * R ^ (-s.val-2) ≤
          256*(D+B) * (n : ℝ) ^ ((U+1)*ε) * R ^ (-3-s.val/2) := by
        calc
          _ ≤ (D+B) * (n : ℝ) ^ (U*ε) * (256*(n : ℝ)^ε * R ^ (-3-s.val/2)) := hprod
          _ = _ := by rw [← heN]; ring
      apply hbase.trans (hprod'.trans _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hR0.le _)
      apply mul_le_mul (by dsimp only [C]; linarith) (hmon (U+1) (by have := Nat.cast_nonneg M₀ (α := ℝ); linarith))
        (Real.rpow_nonneg hn0.le _) hC.le
  · have hshort : R ≤ (n : ℝ) ^ ((M₀ : ℝ) * ε) := by
      have hh : (r.val + 1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (by omega : r.val+1 ≤ K)
      apply hh.trans
      dsimp only [K]
      rw [Nat.cast_pow]
      calc
        _ ≤ ((n : ℝ) ^ ε) ^ M₀ := pow_le_pow_left₀ (Nat.cast_nonneg _)
          (Nat.floor_le (Real.rpow_nonneg hn0.le _)) _
        _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; congr 1; ring
    have hscale : R ^ (1-s.val/2) ≤ (n : ℝ) ^ ((M₀ : ℝ)*ε) :=
      (Real.rpow_le_self_of_one_le hR (by linarith [s.property.1])).trans hshort
    have he : R ^ (1-s.val/2) * R ^ (-3-s.val/2) = R ^ (-s.val-2) := by
      rw [← Real.rpow_add hR0]; congr 1; ring
    have hh := mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg hR0.le (-3-s.val/2))
    rw [he] at hh
    have hm := mul_le_mul_of_nonneg_left hh
      (mul_nonneg (show 0 ≤ D+B by linarith) (Real.rpow_nonneg hn0.le (U*ε)))
    have heN : (n : ℝ) ^ (U*ε) * (n : ℝ) ^ ((M₀ : ℝ)*ε) =
        (n : ℝ) ^ ((U+M₀)*ε) := by rw [← Real.rpow_add hn0]; congr 1; ring
    apply hbase.trans
    calc
      _ ≤ (D+B) * (n : ℝ) ^ (U*ε) * ((n : ℝ) ^ ((M₀ : ℝ)*ε) * R ^ (-3-s.val/2)) := hm
      _ = (D+B) * (n : ℝ) ^ ((U+M₀)*ε) * R ^ (-3-s.val/2) := by rw [← heN]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hR0.le _)
        exact mul_le_mul (by dsimp only [C]; linarith) (hmon (U+M₀) (by linarith))
          (Real.rpow_nonneg hn0.le _) hC.le

end Riesz2.PhysicalCore.Internal

namespace Riesz2.PhysicalCore.Internal

/-- The actual reference internal block has a uniform entry bound, including
all cutoffs and the half-cycle endpoint. -/
theorem referenceInternal_entry_bound (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (K : ℕ)
      (n : ℕ+) (hnM : (n : ℕ) ≤ (M : ℕ)) (a b : Fin (n : ℕ)),
      |BoundaryEntries.referenceInternal s M hM K n hnM a b| ≤
        C * (1 + (Riesz1.cyclicIndexDistance M (a.castLE hnM) (b.castLE hnM) : ℝ)) ^ (-s.val) := by
  obtain ⟨B,hB,hbound⟩ := BoundaryEntries.referenceWeight_bound s
  refine ⟨B*(1+1/s.val),by have := s.property.1; positivity,fun M hM K n hnM a b => ?_⟩
  rw [BoundaryEntries.referenceInternal,referenceIntervalBlock_sum]
  let F := fun (i : Fin (M : ℕ)) (r : Fin ((M : ℕ)/2)) =>
    if IntervalBoundary.IsInternal M n (i,r) then BoundaryEntries.referenceWeight s M hM K (i,r) else 0
  have hF (i) (r) : |F i r| ≤ B * (r.val+1 : ℝ)^(-s.val-2) := by
    dsimp only [F]
    split_ifs
    · rw [abs_of_nonneg (BoundaryEntries.referenceWeight_nonneg s M hM K (i,r))]
      exact hbound M hM K (i,r)
    · rw [abs_zero]; positivity
  have he := signed_interval_entry_bound M s.property.1 hB.le F hF (a.castLE hnM) (b.castLE hnM)
  convert he using 1
  apply congrArg abs
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro r _
  dsimp only [F,IntervalBoundary.IsInternal]
  have heq : (cyclicIndexInterval M i (r.val+1) ⊆ BoundaryEntries.activeIndices M n) ↔
      ∀ j ∈ cyclicIndexInterval M i (r.val+1), j.val < (n : ℕ) := by
    simp only [Finset.subset_iff,BoundaryEntries.activeIndices,Finset.mem_filter,
      Finset.mem_univ,true_and]
  rw [heq]
  split_ifs <;> simp

/-- See the proof of Lemma 5.4 in the paper: summing the equal-period coefficient
errors yields the sharp entry profile on the complete active block. -/
theorem physicalInternal_same_period_entry_error (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M₀ : ℕ) (β : InverseTemperature)
      (n : ℕ+) (m : ℕ) (_hn : 2 * (n : ℕ) ≤ (n : ℕ)+m+1)
      (ε κ₀ : ℝ), 0 ≤ ε → ε ≤ (1-s.val/2)/2 → 0 ≤ κ₀ →
      ∀ (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1)),
        x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀ → ∀ a b : Fin (n : ℕ),
        |BoundaryEntries.physicalInternal β s n m x a b -
          BoundaryEntries.referenceInternal s ((n : ℕ)+m).succPNat
            (by have := n.pos; simp only [Nat.succPNat_coe]; omega)
            (⌊(n : ℝ)^ε⌋₊^M₀) n (by simp only [Nat.succPNat_coe]; omega) a b| ≤
          C * (n : ℝ)^((κ₀+s.val+3+(M₀ : ℝ))*ε) *
            (1+(Riesz1.cyclicIndexDistance ((n : ℕ)+m).succPNat
              (a.castAdd m).castSucc (b.castAdd m).castSucc : ℝ))^(-1-s.val/2) := by
  obtain ⟨B,hB,hbound⟩ := internal_same_period_error s
  refine ⟨B*(1+1/(1+s.val/2)),by have := s.property.1; positivity,fun M₀ β n m hn ε κ₀ hε hεa hκ₀ x hx a b => ?_⟩
  let N := ((n : ℕ)+m).succPNat
  have hN : 2 ≤ (N : ℕ) := by have := n.pos; dsimp only [N,Nat.succPNat_coe]; omega
  have hnN : (n : ℕ) ≤ (N : ℕ) := by dsimp only [N,Nat.succPNat_coe]; omega
  let K := ⌊(n : ℝ)^ε⌋₊^M₀
  let F := fun (i : Fin (N : ℕ)) (r : Fin ((N : ℕ)/2)) =>
    if IntervalBoundary.IsInternal N n (i,r) then
      BoundaryEntries.conditionalIntervalWeight β s n m r i x - BoundaryEntries.referenceWeight s N hN K (i,r)
    else 0
  have hF (i) (r) : |F i r| ≤ (B*(n : ℝ)^((κ₀+s.val+3+(M₀ : ℝ))*ε)) *
      (r.val+1 : ℝ)^(-(1+s.val/2)-2) := by
    dsimp only [F]
    split_ifs with hi
    · simpa only [show -(1+s.val/2)-2 = -3-s.val/2 by ring] using
        hbound M₀ β n m hn ε κ₀ hε hεa hκ₀ x hx i r hi
    · rw [abs_zero]; positivity
  have hb := signed_interval_entry_bound N (by linarith [s.property.1] : 0 < 1+s.val/2)
    (by positivity : 0 ≤ B*(n : ℝ)^((κ₀+s.val+3+(M₀ : ℝ))*ε)) F hF
    (a.castLE hnN) (b.castLE hnN)
  have he : BoundaryEntries.physicalInternal β s n m x a b -
      BoundaryEntries.referenceInternal s N hN K n hnN a b =
      ∑ i, ∑ r, F i r * (if a.castLE hnN ∈ cyclicIndexInterval N i (r.val+1) then 1 else 0) *
        (if b.castLE hnN ∈ cyclicIndexInterval N i (r.val+1) then 1 else 0) := by
    rw [physicalInternal_reference_intervals β s n m hn N hn x a b,
      BoundaryEntries.referenceInternal,referenceIntervalBlock_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    have hsub : cyclicIndexInterval N i (r.val+1) ⊆ BoundaryEntries.activeIndices N n ↔
        IntervalBoundary.IsInternal N n (i,r) := by
      simp only [IntervalBoundary.IsInternal,Finset.subset_iff,BoundaryEntries.activeIndices,
        Finset.mem_filter,Finset.mem_univ,true_and]
    simp only [hsub,F]
    by_cases hi : IntervalBoundary.IsInternal N n (i,r)
    · simp only [hi,ite_true,dite_true]
      by_cases ha : a.castLE hnN ∈ cyclicIndexInterval N i (r.val+1) <;>
        by_cases hc : b.castLE hnN ∈ cyclicIndexInterval N i (r.val+1) <;>
        simp only [ha,hc,and_self,and_false,false_and,ite_true,ite_false,mul_one,mul_zero,sub_self]
      all_goals rfl
    · simp only [hi,ite_false,dite_false,zero_mul,sub_zero]
  rw [he]
  simpa only [show a.castLE hnN = (a.castAdd m).castSucc from Fin.ext rfl,
    show b.castLE hnN = (b.castAdd m).castSucc from Fin.ext rfl,
    show -(1+s.val/2) = -1-s.val/2 by ring,mul_assoc,mul_left_comm,mul_comm] using hb

end Riesz2.PhysicalCore.Internal

namespace Riesz2.PhysicalCore

/-- See Subsection 5.1 of the paper: the actual reference period for a proper active
window. This is the capped polynomial period, defined for every positive
physical period and active size. -/
def properReferencePeriod (s : Riesz1.RieszExponent) (n N : ℕ+) : ℕ+ :=
  ⟨min (N : ℕ) (max (2*(n : ℕ)) ⌈(n : ℝ)^(1/2+1/s.val)⌉₊),
    lt_min N.pos (lt_of_lt_of_le (by have := n.pos; omega) (le_max_left _ _))⟩

/-- See Subsection 5.1 of the paper: the reference contains the half-window, is at
most the physical period, and either equals that period or has the prescribed
polynomial size. -/
theorem properReferencePeriod_bounds (s : Riesz1.RieszExponent) (n N : ℕ+)
    (hn : 2*(n : ℕ) ≤ (N : ℕ)) :
    2*(n : ℕ) ≤ (properReferencePeriod s n N : ℕ) ∧
    (properReferencePeriod s n N : ℕ) ≤ (N : ℕ) ∧
    (properReferencePeriod s n N = N ∨
      (n : ℝ)^(1/2+1/s.val) ≤ (properReferencePeriod s n N : ℝ)) := by
  refine ⟨le_min hn (le_max_left _ _),min_le_left _ _,?_⟩
  by_cases h : (N : ℕ) ≤ max (2*(n : ℕ)) ⌈(n : ℝ)^(1/2+1/s.val)⌉₊
  · left
    apply Subtype.ext
    exact min_eq_left h
  · right
    have he : (properReferencePeriod s n N : ℕ) =
        max (2*(n : ℕ)) ⌈(n : ℝ)^(1/2+1/s.val)⌉₊ := min_eq_right (by omega)
    change (n : ℝ)^(1/2+1/s.val) ≤ ((properReferencePeriod s n N : ℕ) : ℝ)
    rw [he]
    exact (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right (2*(n : ℕ)) ⌈(n : ℝ)^(1/2+1/s.val)⌉₊))

namespace Internal

/-- Active distances in any cycle containing a half-window are ordinary
index distances. This bridges the different physical and reference periods. -/
theorem active_distance (M n : ℕ+) (hn : 2*(n : ℕ) ≤ (M : ℕ)) (a b : Fin (n : ℕ)) :
    Riesz1.cyclicIndexDistance M (a.castLE (by omega)) (b.castLE (by omega)) =
      Nat.dist a.val b.val := by
  simp only [Riesz1.cyclicIndexDistance,Fin.val_castLE]
  have ha := a.isLt
  have hb := b.isLt
  unfold Nat.dist
  omega

/-- In the polynomial regime the reference half-cycle endpoint cannot be
an internal interval once the active size exceeds four. -/
theorem two_n_lt_polynomial_period (s : Riesz1.RieszExponent) (n M : ℕ+)
    (hn : 4 < (n : ℕ)) (hscale : (n : ℝ)^(1/2+1/s.val) ≤ (M : ℝ)) :
    2*(n : ℕ) < (M : ℕ) := by
  have hnR : (4 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hs : 1 ≤ 1/s.val := (one_le_div s.property.1).mpr s.property.2.le
  have hsqrt : 2 < (n : ℝ)^(1/2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 4) hnR
    norm_num at h
    exact h
  have hp : 2*(n : ℝ) < (n : ℝ)^(1/2+1/s.val) := by
    calc
      _ < (n : ℝ)*(n : ℝ)^(1/2 : ℝ) := by nlinarith
      _ = (n : ℝ)^(1+1/2 : ℝ) := by rw [Real.rpow_add hn0,Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  exact_mod_cast hp.trans_le hscale

/-- Equal periods give equal literal internal reference blocks, with any
proofs of their dimension constraints. -/
theorem referenceInternal_period_congr (s : Riesz1.RieszExponent) (n N M : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (hM : 2 ≤ (M : ℕ)) (hnN : (n : ℕ) ≤ (N : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (h : M = N) (a b : Fin (n : ℕ)) :
    BoundaryEntries.referenceInternal s N hN K n hnN a b =
      BoundaryEntries.referenceInternal s M hM K n hnM a b := by
  subst M
  rfl

/-- See the proof of Lemma 5.4 in the paper: the active internal entry error for the
actual proper reference period, including bounded active sizes and different
antipodal conventions. -/
theorem proper_internal_entry_error (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M₀ : ℕ) (β : InverseTemperature)
      (n : ℕ+) (m : ℕ) (hn : 2*(n : ℕ) ≤ (n : ℕ)+m+1)
      (ε κ₀ : ℝ), 0 ≤ ε → ε ≤ (1-s.val/2)/2 → 0 ≤ κ₀ →
      let N := ((n : ℕ)+m).succPNat
      let M := properReferencePeriod s n N
      let hM : 2 ≤ (M : ℕ) := by
        change 2 ≤ (properReferencePeriod s n N : ℕ)
        have := (properReferencePeriod_bounds s n N hn).1
        have := n.pos
        omega
      ∀ (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1)),
        x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀ → ∀ a b : Fin (n : ℕ),
        |BoundaryEntries.physicalInternal β s n m x a b -
          BoundaryEntries.referenceInternal s M hM (⌊(n : ℝ)^ε⌋₊^M₀) n
            (by change (n : ℕ) ≤ (properReferencePeriod s n N : ℕ); have := (properReferencePeriod_bounds s n N hn).1; omega) a b| ≤
          C*(n : ℝ)^((κ₀+s.val+3+(M₀ : ℝ))*ε) *
            (1+(Nat.dist a.val b.val : ℝ))^(-1-s.val/2) := by
  obtain ⟨B,hB,hsame⟩ := physicalInternal_same_period_entry_error s
  obtain ⟨D,hD,hperiod⟩ := LocalizedMatrix.referenceInternal_different_period s
  obtain ⟨E,hE,href⟩ := referenceInternal_entry_bound s
  let T := (1+E)*(5 : ℝ)^(1+s.val/2)
  have hT : 0 < T := by dsimp only [T]; positivity
  refine ⟨B+D+T,by positivity,?_⟩
  intro M₀ β n m hn ε κ₀ hε hεa hκ₀ N M hM x hx a b
  have hgeo : 2*(n : ℕ) ≤ (M : ℕ) ∧ (M : ℕ) ≤ (N : ℕ) ∧
      (M = N ∨ (n : ℝ)^(1/2+1/s.val) ≤ (M : ℝ)) :=
    properReferencePeriod_bounds s n N hn
  have hN : 2 ≤ (N : ℕ) := by have := n.pos; dsimp only [N,Nat.succPNat_coe]; omega
  have hnN : (n : ℕ) ≤ (N : ℕ) := by omega
  have hnM : (n : ℕ) ≤ (M : ℕ) := by have := hgeo.1; omega
  let K := ⌊(n : ℝ)^ε⌋₊^M₀
  let v := (n : ℝ)^((κ₀+s.val+3+(M₀ : ℝ))*ε)
  let w := (1+(Nat.dist a.val b.val : ℝ))^(-1-s.val/2)
  have hv : 1 ≤ v := Real.one_le_rpow (by exact_mod_cast n.pos)
    (by have := Nat.cast_nonneg M₀ (α := ℝ); nlinarith [s.property.1])
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hd : Nat.dist a.val b.val < (n : ℕ) := by have := a.isLt; have := b.isLt; unfold Nat.dist; omega
  by_cases hlarge : 4 < (n : ℕ)
  · have hh := hsame M₀ β n m hn ε κ₀ hε hεa hκ₀ x hx a b
    have hdist : Riesz1.cyclicIndexDistance N (a.castAdd m).castSucc (b.castAdd m).castSucc =
        Nat.dist a.val b.val := by
      simpa only [show a.castLE hnN = (a.castAdd m).castSucc from Fin.ext rfl,
        show b.castLE hnN = (b.castAdd m).castSucc from Fin.ext rfl] using active_distance N n hn a b
    rw [hdist] at hh
    have hp : |BoundaryEntries.referenceInternal s N hN K n hnN a b -
        BoundaryEntries.referenceInternal s M hM K n hnM a b| ≤ D*w := by
      rcases hgeo.2.2 with he | hscale
      · have heM : M = N := he
        have heq := referenceInternal_period_congr s n N M hN hM hnN hnM K heM a b
        rw [heq,sub_self,abs_zero]
        exact mul_nonneg hD.le hw
      · have hstrict := two_n_lt_polynomial_period s n M hlarge hscale
        exact (hperiod N M n hN hM hgeo.2.1 hstrict K a b).trans (by
          simpa only [w,mul_assoc] using mul_le_mul_of_nonneg_left
            (LocalizedMatrix.period_error_absorption s n M hscale hd) hD.le)
    have htri := abs_sub_le (BoundaryEntries.physicalInternal β s n m x a b)
      (BoundaryEntries.referenceInternal s N hN K n hnN a b)
      (BoundaryEntries.referenceInternal s M hM K n hnM a b)
    have hDv := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hD.le) hw
    change _ ≤ B*v*w at hh
    change _ ≤ (B+D+T)*v*w
    nlinarith only [htri,hh,hp,hDv,mul_nonneg hT.le (mul_nonneg (le_trans zero_le_one hv) hw)]
  · have hsmall : (n : ℕ) ≤ 4 := by omega
    have hP := physicalInternal_good_bound β s n m ε κ₀ x hx a b
    have hR := href M hM K n hnM a b
    have hR' : |BoundaryEntries.referenceInternal s M hM K n hnM a b| ≤ E := by
      apply hR.trans
      exact mul_le_of_le_one_right hE.le (Real.rpow_le_one_of_one_le_of_nonpos
        (le_add_of_nonneg_right (Nat.cast_nonneg _)) (by linarith [s.property.1]))
    have hPv : (n : ℝ)^(κ₀*ε) ≤ v := Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast n.pos) (by have := Nat.cast_nonneg M₀ (α := ℝ); nlinarith [s.property.1])
    have hweight : 1 ≤ (5 : ℝ)^(1+s.val/2)*w := by
      have hp : (5 : ℝ)^(-1-s.val/2) ≤ w := Real.rpow_le_rpow_of_nonpos
        (by positivity) (by exact_mod_cast (by omega : 1+Nat.dist a.val b.val ≤ 5))
        (by linarith [s.property.1])
      have he : (5 : ℝ)^(1+s.val/2)*(5 : ℝ)^(-1-s.val/2) = 1 := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 5)]
        norm_num
      nlinarith only [mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 5) (1+s.val/2)),he]
    have htri := abs_sub_le (BoundaryEntries.physicalInternal β s n m x a b) 0
      (BoundaryEntries.referenceInternal s M hM K n hnM a b)
    simp only [sub_zero,zero_sub,abs_neg] at htri
    have hEv := mul_le_mul_of_nonneg_left hv hE.le
    have hTv := mul_le_mul_of_nonneg_left hweight
      (mul_nonneg (show 0 ≤ 1+E by linarith) (le_trans zero_le_one hv))
    change _ ≤ (B+D+T)*v*w
    dsimp only [T] at *
    nlinarith only [hP,hPv,hR',htri,hEv,hTv,
      mul_nonneg (show 0 ≤ B+D by linarith) (mul_nonneg (le_trans zero_le_one hv) hw)]

end Internal
end Riesz2.PhysicalCore

namespace Riesz2.PhysicalCore

/-- See the proof of Lemma 5.4 in the paper, proper active entry clause: the actual
core differs from the actual reference with the improved spatial profile,
on both branches of the good event and at every admissible active size. -/
theorem properActive_entry_error (s : Riesz1.RieszExponent) (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M₀ : ℕ) (β : InverseTemperature)
      (n : ℕ+) (m : ℕ) (hn : 2*(n : ℕ) ≤ (n : ℕ)+m+1)
      (ε κ₀ : ℝ), 0 ≤ ε → ε ≤ (1-s.val/2)/2 → 0 ≤ κ₀ →
      let N := ((n : ℕ)+m).succPNat
      let M := properReferencePeriod s n N
      let hM : 2 ≤ (M : ℕ) := by
        change 2 ≤ (properReferencePeriod s n N : ℕ)
        have := (properReferencePeriod_bounds s n N hn).1
        have := n.pos
        omega
      let hnM : (n : ℕ) ≤ (M : ℕ) := by
        change (n : ℕ) ≤ (properReferencePeriod s n N : ℕ)
        have := (properReferencePeriod_bounds s n N hn).1
        omega
      ∀ (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1)) (a b : Fin (n : ℕ)),
        |properActive β s n m M hM hnM (⌊(n : ℝ)^ε⌋₊^M₀) θ ε κ₀ x a b -
          2*referenceIntervalMatrix s M hM (⌊(n : ℝ)^ε⌋₊^M₀) (a.castLE hnM) (b.castLE hnM)| ≤
          C*(n : ℝ)^((κ₀+s.val+3+(M₀ : ℝ))*ε) *
            (1+(Riesz1.cyclicIndexDistance M (a.castLE hnM) (b.castLE hnM) : ℝ))^(-1-s.val/2) := by
  obtain ⟨D,hD,hentry⟩ := Internal.proper_internal_entry_error s
  obtain ⟨F,hF,hforce⟩ := forcingHessian_uniform_bound θ
  refine ⟨D+F,by positivity,?_⟩
  intro M₀ β n m hn ε κ₀ hε hεa hκ₀ N M hM hnM x a b
  have hgeo : 2*(n : ℕ) ≤ (M : ℕ) := (properReferencePeriod_bounds s n N hn).1
  let K := ⌊(n : ℝ)^ε⌋₊^M₀
  let v := (n : ℝ)^((κ₀+s.val+3+(M₀ : ℝ))*ε)
  let w := (1+(Riesz1.cyclicIndexDistance M (a.castLE hnM) (b.castLE hnM) : ℝ))^(-1-s.val/2)
  have hv : 1 ≤ v := Real.one_le_rpow (by exact_mod_cast n.pos)
    (by have := Nat.cast_nonneg M₀ (α := ℝ); nlinarith [s.property.1])
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  by_cases hx : x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀
  · have he := hentry M₀ β n m hn ε κ₀ hε hεa hκ₀ x hx a b
    rw [← Internal.active_distance M n hgeo a b] at he
    have hf : |forcingHessian n θ ε x.val a b| ≤ F*v*w := by
      by_cases hab : a = b
      · subst b
        have hw1 : w = 1 := by
          simp only [w,Riesz1.cyclicIndexDistance,Nat.dist_self,Nat.sub_zero,
            Nat.zero_min,Nat.cast_zero,add_zero,Real.one_rpow]
        rw [hw1,mul_one]
        have hp := (forcingHessian_bound n m θ ε).choose_spec.2 x a a
        rw [abs_of_nonneg hp.1]
        exact (hforce n m ε hε x a a).trans (le_mul_of_one_le_right hF.le hv)
      · rw [forcingHessian_apply n m θ ε x a b,ite_eq_right hab,abs_zero]
        positivity
    have href := BoundaryEntries.referenceInternal_add_crossing s M hM K n hnM a b
    have halg : properActive β s n m M hM hnM K θ ε κ₀ x a b -
        2*referenceIntervalMatrix s M hM K (a.castLE hnM) (b.castLE hnM) =
        forcingHessian n θ ε x.val a b + (BoundaryEntries.physicalInternal β s n m x a b -
          BoundaryEntries.referenceInternal s M hM K n hnM a b) := by
      simp only [properActive,ite_eq_left hx,Matrix.add_apply]
      linarith only [href]
    rw [halg]
    change _ ≤ (D+F)*v*w
    change _ ≤ D*v*w at he
    exact (abs_add_le _ _).trans (by linarith only [hf,he])
  · rw [properActive_of_not_mem β s n m M hM hnM K θ ε κ₀ x hx,sub_self,abs_zero]
    positivity

end Riesz2.PhysicalCore

namespace Riesz2.PhysicalCore

/-- See the proof of Lemma 5.4 in the paper, complete proper-window clause. The
threshold and both structural exponents are chosen before temperature,
epsilon and size. The single constant witnesses `PeriodizedMatrixBounds`, for the prescribed period and admissible cutoff.
The result holds for every measure on the physical carrier. -/
theorem proper_matrix_bounds (s : Riesz1.RieszExponent) (θ : PhysicalCutoff)
    (M₀ : ℕ) (κ₀ : ℝ) (hκ₀ : 0 ≤ κ₀) :
    ∃ ε₀ κ γ : ℝ, 0 < ε₀ ∧ 0 < κ ∧ 0 < γ ∧
      ∀ β : InverseTemperature, ∃ C : ℝ, 1 ≤ C ∧
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
        ∀ (n : ℕ+) (m : ℕ) (hn : 2*(n : ℕ) ≤ (n : ℕ)+m+1),
        let N := ((n : ℕ)+m).succPNat
        let M := properReferencePeriod s n N
        let hM : 2 ≤ (M : ℕ) := by
          change 2 ≤ (properReferencePeriod s n N : ℕ)
          have := (properReferencePeriod_bounds s n N hn).1
          have := n.pos
          omega
        let hnM : (n : ℕ) ≤ (M : ℕ) := by
          change (n : ℕ) ≤ (properReferencePeriod s n N : ℕ)
          have := (properReferencePeriod_bounds s n N hn).1
          omega
        let K := ⌊(n : ℝ)^ε⌋₊^M₀
        K ≤ (M : ℕ)/4 →
        ∀ μ : Measure (AffineSimplex.chartDomain n ((n+m : ℕ)+1)),
          PeriodizedMatrixBounds (ν := μ) s n M hM K C κ γ ε
            (properMatrix β s n m M hM hnM K θ ε κ₀) := by
  obtain ⟨c₁,hc₁,hcoerc⟩ := properMatrix_cutoff_coercivity s
  obtain ⟨c₂,hc₂,hlower⟩ := properIntervalWeight_threshold_lower s
  obtain ⟨U,hU,hupper⟩ := properIntervalWeight_upper s θ
  obtain ⟨E,hE,hentry⟩ := properActive_entry_error s θ
  let kE := κ₀+s.val+3+(M₀ : ℝ)
  let kC := s.val+2+(M₀ : ℝ)*(1+s.val)
  let κ := kE+kC
  let γ := (M₀ : ℝ)+1
  have hkE : 0 < kE := by dsimp only [kE]; have := Nat.cast_nonneg M₀ (α := ℝ); linarith [s.property.1]
  have hkC : 0 < kC := by dsimp only [kC]; have := s.property.1; positivity
  refine ⟨(1-s.val/2)/2,κ,γ,by linarith [s.property.2],by dsimp only [κ]; positivity,
    by dsimp only [γ]; positivity,fun β => ?_⟩
  have hi₁ : 0 < c₁⁻¹ := inv_pos.mpr hc₁
  have hi₂ : 0 < c₂⁻¹ := inv_pos.mpr hc₂
  let C := 1+U+E+c₁⁻¹+c₂⁻¹
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hCU : U ≤ C := by dsimp only [C]; linarith
  have hCE : E ≤ C := by dsimp only [C]; linarith
  have hcC₁ : C⁻¹ ≤ c₁ := (inv_le_comm₀ hC0 hc₁).mpr (by dsimp only [C]; linarith)
  have hcC₂ : C⁻¹ ≤ c₂ := (inv_le_comm₀ hC0 hc₂).mpr (by dsimp only [C]; linarith)
  refine ⟨C,hC,?_⟩
  intro ε hε hεa n m hn N M hM hnM K hKM μ
  have hhalf : 2*(n : ℕ) ≤ (M : ℕ) := (properReferencePeriod_bounds s n N hn).1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by positivity
  have lower (c l : ℝ) (hc : 0 < c) (hcl : C⁻¹ ≤ c) (hl : l ≤ κ) :
      C⁻¹*(n : ℝ)^(-κ*ε) ≤ c*(n : ℝ)^(-l*ε) := by
    exact mul_le_mul hcl (Real.rpow_le_rpow_of_exponent_le hn1
      (by nlinarith only [hl,hε])) (Real.rpow_nonneg hn0.le _) hc.le
  have upper (c l : ℝ) (hc : 0 ≤ c) (hcl : c ≤ C) (hl : l ≤ κ) :
      c*(n : ℝ)^(l*ε) ≤ C*(n : ℝ)^(κ*ε) :=
    mul_le_mul hcl (Real.rpow_le_rpow_of_exponent_le hn1
      (mul_le_mul_of_nonneg_right hl hε)) (Real.rpow_nonneg hn0.le _) hC0.le
  have hkEκ : kE ≤ κ := by dsimp only [κ]; linarith
  have hkCκ : kC ≤ κ := by dsimp only [κ]; linarith
  have hkUκ : κ₀+s.val+2 ≤ κ := by dsimp only [kE] at hkEκ; have := Nat.cast_nonneg M₀ (α := ℝ); linarith
  have hksκ : s.val+2 ≤ κ := by linarith
  refine ⟨measurable_properMatrix β s n m M hM hnM K θ ε κ₀,?_,?_⟩
  · apply ae_of_all
    intro x
    have hsym := properMatrix_symmetric β s n m M hM hnM K θ ε κ₀ x
    have hHerm : (properMatrix β s n m M hM hnM K θ ε κ₀ x).IsHermitian := by
      ext a b
      simp only [Matrix.conjTranspose_apply,star_trivial,hsym]
    refine ⟨hsym,properMatrix_exterior β s n m M hM hnM K θ ε κ₀ x,?_,?_⟩
    · intro z
      have hh := (FiniteMatrixOrder.smul_one_le_iff hHerm _).mp
        (hcoerc M₀ β n m hn M hM hhalf θ ε κ₀ hε hKM x) z
      have hh' : c₁*(n : ℝ)^(-kC*ε)*(∑ i,z i^2) ≤
          ∑ i,∑ j,z i*properMatrix β s n m M hM hnM K θ ε κ₀ x i j*z j := by
        simpa only [kC,Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc,pow_two] using hh
      exact (mul_le_mul_of_nonneg_right (lower c₁ kC hc₁ hcC₁ hkCκ)
        (Finset.sum_nonneg (fun i _ => sq_nonneg (z i)))).trans hh'
    · intro a b ha hb
      let a' : Fin (n : ℕ) := ⟨a.val,ha⟩
      let b' : Fin (n : ℕ) := ⟨b.val,hb⟩
      have ha' : a'.castLE hnM = a := Fin.ext rfl
      have hb' : b'.castLE hnM = b := Fin.ext rfl
      have he := hentry M₀ β n m hn ε κ₀ hε hεa hκ₀ x a' b'
      rw [← properMatrix_active β s n m M hM hnM K θ ε κ₀ x a' b',ha',hb'] at he
      exact he.trans (by
        simpa only [Matrix.smul_apply,smul_eq_mul] using mul_le_mul_of_nonneg_right
          (upper E kE hE.le hCE hkEκ)
          (Real.rpow_nonneg (by positivity : 0 ≤ 1+(Riesz1.cyclicIndexDistance M a b : ℝ)) (-1-s.val/2)))
  · refine ⟨properIntervalWeight β s n m hn M hM hhalf K θ ε κ₀,
      measurable_properIntervalWeight β s n m hn M hM hhalf K θ ε κ₀,ae_of_all _ (fun x => ?_)⟩
    refine ⟨fun i r => ⟨properIntervalWeight_nonneg β s n m hn M hM hhalf K θ ε κ₀ i r x,?_,?_⟩,
      properMatrix_interval_quadratic β s n m hn M hM hhalf K θ ε κ₀ x⟩
    · exact (hupper β n m hn M hM hhalf K ε κ₀ hε hεa hκ₀ x i r).trans
        (mul_le_mul_of_nonneg_right (upper U (κ₀+s.val+2) hU.le hCU hkUκ) (by positivity))
    · intro hr
      exact (mul_le_mul_of_nonneg_right (lower c₂ (s.val+2) hc₂ hcC₂ hksκ) (by positivity)).trans
        (hlower M₀ γ (by dsimp only [γ]; linarith) β n m hn M hM hhalf θ ε κ₀ hε x i r hr)

end Riesz2.PhysicalCore
