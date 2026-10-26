/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.PhysicalCorePart4
public import Riesz2.DecayLong.PhysicalCoreCutoff

/-!
# Long-interval lower bounds for the actual physical core

The absolute coefficient lower bound in the proof of Lemma 5.4, on
the precise length carrier of the periodized predicate.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped BigOperators MatrixOrder

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.PhysicalCore

/-- See the proof of Lemma 5.4 in the paper: retained reference weights have an
absolute lower bound uniform in the period, including antipodal lengths. -/
theorem referenceWeight_lower (s : Riesz1.RieszExponent) :
    ∃ c : ℝ, 0 < c ∧ ∀ (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (K : ℕ)
      (i : Fin (M : ℕ)) (r : Fin ((M : ℕ) / 2)), K ≤ r.val + 1 →
        c * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2) ≤
          BoundaryEntries.referenceWeight s M hM K (i,r) := by
  obtain ⟨c, C, hc, _, hb⟩ := sampledSecondDifference_bounds s
  refine ⟨c, hc, fun M hM K i r hK => ?_⟩
  have hrM : r.val + 1 < (M : ℕ) := by have := r.isLt; omega
  let k : Fin (M : ℕ) := ⟨(r.val + 1) % (M : ℕ), Nat.mod_lt _ M.pos⟩
  have hkv : k.val = r.val + 1 := Nat.mod_eq_of_lt hrM
  have hk : k ≠ 0 := by
    intro he
    have := congrArg Fin.val he
    simp only [hkv, Fin.val_zero] at this
    omega
  have hd : Riesz1.cyclicIndexDistance M k 0 = r.val + 1 := by
    simp only [Riesz1.cyclicIndexDistance, Fin.val_zero, Nat.dist_zero_right, hkv]
    have := r.isLt
    omega
  have hl := (hb M hM k hk).1
  rw [hd] at hl
  have hp := (sampledSecondDifference_pos s M hM hk).le
  unfold BoundaryEntries.referenceWeight
  rw [ite_eq_left hK]
  split_ifs <;> dsimp only [k] at hp hl <;> push_cast at hl ⊢ <;> linarith

/-- See the proof of Lemma 5.4 in the paper: the actual physical coefficients satisfy
the absolute lower bound above the actual cutoff. The prefactor depends
only on `s`, before every physical and reference parameter. -/
theorem properIntervalWeight_lower (s : Riesz1.RieszExponent) :
    ∃ c : ℝ, 0 < c ∧ ∀ (β : InverseTemperature)
      (n : ℕ+) (m : ℕ) (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
      (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : 2 * (n : ℕ) ≤ (M : ℕ))
      (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ), 0 ≤ ε →
      ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
        (i : Fin (M : ℕ)) (r : Fin ((M : ℕ) / 2)), K ≤ r.val + 1 →
        c * (n : ℝ) ^ (-(s.val + 2) * ε) * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2) ≤
          properIntervalWeight β s n m hn M hM hnM K θ ε κ₀ i r x := by
  obtain ⟨c, hc, _, hphys⟩ := properIntervalWeight_reference_lower s
  obtain ⟨b, hb, href⟩ := referenceWeight_lower s
  refine ⟨c * b, mul_pos hc hb, fun β n m hn M hM hnM K θ ε κ₀ hε x i r hK => ?_⟩
  have hh := mul_le_mul_of_nonneg_left (href M hM K i r hK)
    (mul_nonneg hc.le (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n) (-(s.val + 2) * ε)))
  have he : c * (n : ℝ) ^ (-(s.val + 2) * ε) *
      (b * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2)) =
      (c * b) * (n : ℝ) ^ (-(s.val + 2) * ε) *
        ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2) := by ring
  rw [he] at hh
  exact hh.trans (hphys β n m hn M hM hnM K θ ε κ₀ hε x i r)

/-- See the proof of Lemma 5.4 in the paper: for the prescribed cutoff, the absolute
coefficient lower bound holds on exactly the long-interval region of the
predicate. Structural `γ` may be chosen before temperature and size. -/
theorem properIntervalWeight_threshold_lower (s : Riesz1.RieszExponent) :
    ∃ c : ℝ, 0 < c ∧ ∀ (M₀ : ℕ) (γ : ℝ), (M₀ : ℝ) ≤ γ →
      ∀ (β : InverseTemperature)
        (n : ℕ+) (m : ℕ) (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
        (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : 2 * (n : ℕ) ≤ (M : ℕ))
        (θ : PhysicalCutoff) (ε κ₀ : ℝ), 0 ≤ ε →
        ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
          (i : Fin (M : ℕ)) (r : Fin ((M : ℕ) / 2)),
          (n : ℝ) ^ (γ * ε) ≤ ((r.val + 1 : ℕ) : ℝ) →
          c * (n : ℝ) ^ (-(s.val + 2) * ε) * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2) ≤
            properIntervalWeight β s n m hn M hM hnM
              (⌊(n : ℝ) ^ ε⌋₊ ^ M₀) θ ε κ₀ i r x := by
  obtain ⟨c, hc, hl⟩ := properIntervalWeight_lower s
  refine ⟨c, hc, fun M₀ γ hγ β n m hn M hM hnM θ ε κ₀ hε x i r hr => ?_⟩
  apply hl β n m hn M hM hnM _ θ ε κ₀ hε x i r
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hh : ((⌊(n : ℝ) ^ ε⌋₊ ^ M₀ : ℕ) : ℝ) ≤ (n : ℝ) ^ (γ * ε) := by
    calc
      _ = (⌊(n : ℝ) ^ ε⌋₊ : ℝ) ^ M₀ := by rw [Nat.cast_pow]
      _ ≤ ((n : ℝ) ^ ε) ^ M₀ :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (Real.rpow_nonneg hn0.le _)) M₀
      _ = (n : ℝ) ^ ((M₀ : ℝ) * ε) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (mul_le_mul_of_nonneg_right hγ hε)
  exact_mod_cast hh.trans hr

end Riesz2.PhysicalCore

namespace Riesz2.PhysicalCore.Internal

/-- Lemma 5.4 of the paper: on the actual proper good event, the
mass of an internal interval below the paper cutoff is at most `n^(1/4)`.
The first inequality retains the intermediate `r n^ε` of the written proof. -/
theorem proper_short_gap_mass (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (ε κ₀ : ℝ) (hε : 0 ≤ ε) (hsmall : ε ≤ paperCutoffThreshold s)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (hx : x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀)
    (r : Fin (((n : ℕ) + m + 1) / 2)) (i : Fin ((n : ℕ) + m + 1))
    (hi : IntervalBoundary.IsInternal ((n : ℕ) + m).succPNat n (i, r))
    (hr : r.val + 1 < ⌊(n : ℝ) ^ ε⌋₊ ^ (paperReferenceCutoffExponent s : ℕ)) :
    let L := cyclicGapSum ((n : ℕ) + m).succPNat i (r.val + 1)
      (WithLp.ofLp (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val, 0)))
    L ≤ (r.val + 1 : ℝ) * (n : ℝ) ^ ε ∧ L ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
  have hend := (internal_iff_end_le ((n : ℕ) + m).succPNat n hn i r).mp hi
  let j : Fin (n : ℕ) := ⟨i.val, by omega⟩
  have hgap := (PhysicalEnergy.gapSum_bounds n j (r.val + 1)
    (WithLp.ofLp x.val) hx.1.1).2
  dsimp only
  rw [internal_gapSum_active n m hn x.val r i hi]
  have hh : cyclicGapSum n j (r.val + 1) (WithLp.ofLp x.val) ≤
      (r.val + 1 : ℝ) * (n : ℝ) ^ ε := by
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using hgap
  refine ⟨hh, hh.trans ?_⟩
  simpa only [Nat.cast_add, Nat.cast_one] using
    (paper_cutoff_short_mass s n hε hsmall hr).1.trans
      (paper_cutoff_short_mass s n hε hsmall hr).2

/-- Lemma 5.4 of the paper: rigidity uniformly above the paper cutoff
places every proper internal gap sum between `r/2` and `2r` at large sizes. -/
theorem proper_long_gap_rigidity (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (ε κ₀ : ℝ) (hlarge : 8 ≤ (n : ℝ) ^ ε)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (hx : x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀)
    (r : Fin (((n : ℕ) + m + 1) / 2)) (i : Fin ((n : ℕ) + m + 1))
    (hi : IntervalBoundary.IsInternal ((n : ℕ) + m).succPNat n (i, r))
    (hr : ⌊(n : ℝ) ^ ε⌋₊ ^ (paperReferenceCutoffExponent s : ℕ) ≤ r.val + 1) :
    let L := cyclicGapSum ((n : ℕ) + m).succPNat i (r.val + 1)
      (WithLp.ofLp (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val, 0)))
    (r.val + 1 : ℝ) / 2 ≤ L ∧ L ≤ 3 / 2 * (r.val + 1 : ℝ) := by
  have hend := (internal_iff_end_le ((n : ℕ) + m).succPNat n hn i r).mp hi
  let j : Fin (n : ℕ) := ⟨i.val, by omega⟩
  let k : Fin ((n : ℕ) + 1) := ⟨r.val + 1, by omega⟩
  have hd := hx.1.2 j k (by dsimp only [k]; omega)
    (by dsimp only [k]; have := r.isLt; omega) (by dsimp only [j, k]; omega)
  have ht := paper_cutoff_taylor_condition s hlarge (by positivity : 0 < (r.val + 1 : ℝ))
    (by exact_mod_cast hr)
  dsimp only
  rw [internal_gapSum_active n m hn x.val r i hi]
  simp only [k, Nat.cast_add, Nat.cast_one] at hd
  exact ⟨by linarith [(abs_le.mp hd).1], by linarith [(abs_le.mp hd).2]⟩

/-- On the actual good event, each internal interval coefficient is bounded
by the diagonal cutoff. This bound is independent of the exterior dimension. -/
theorem internal_coefficient_diagonal_bound (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1) (ε κ₀ : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (hx : x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀)
    (r : Fin (((n : ℕ) + m + 1) / 2)) (i : Fin ((n : ℕ) + m + 1))
    (hi : IntervalBoundary.IsInternal ((n : ℕ) + m).succPNat n (i,r)) :
    BoundaryEntries.conditionalIntervalWeight β s n m r i x ≤ (n : ℝ) ^ (κ₀ * ε) := by
  classical
  let N := ((n : ℕ) + m).succPNat
  have hend := (internal_iff_end_le N n hn i r).mp hi
  let a : Fin (n : ℕ) := ⟨i.val, by omega⟩
  have ha : (a.castAdd m).castSucc ∈ cyclicIndexInterval N i (r.val + 1) := by
    have he : (a.castAdd m).castSucc = i := Fin.ext rfl
    rw [he, mem_cyclicIndexInterval_iff N i i (by have := r.isLt; omega)]
    simp only [sub_self, Fin.val_zero]
    omega
  have hnon (r' : Fin (((n : ℕ) + m + 1) / 2)) (i' : Fin ((n : ℕ) + m + 1)) :
      0 ≤ if (a.castAdd m).castSucc ∈ cyclicIndexInterval N i' (r'.val + 1) ∧
          (a.castAdd m).castSucc ∈ cyclicIndexInterval N i' (r'.val + 1) then
        BoundaryEntries.conditionalIntervalWeight β s n m r' i' x else 0 := by
    split_ifs
    · exact BoundaryEntries.conditionalIntervalWeight_nonneg β s n m r' i' x
    · exact le_rfl
  have hsingle := (Finset.single_le_sum (fun j _ => hnon r j) (Finset.mem_univ i)).trans
    (Finset.single_le_sum (fun q _ => Finset.sum_nonneg (fun j _ => hnon q j)) (Finset.mem_univ r))
  rw [ite_eq_left (And.intro ha ha), ← BoundaryEntries.conditionalHessian_intervalWeight] at hsingle
  have hcut := hx.2 a a
  simpa only [Riesz1.cyclicIndexDistance, Nat.dist_self, Nat.sub_zero, min_self,
    Nat.min_zero, Nat.zero_min, Nat.cast_zero, add_zero, Real.one_rpow, mul_one] using hsingle.trans hcut

end Riesz2.PhysicalCore.Internal

namespace Riesz2.PhysicalCore.Internal

/-- Internal large-size estimate. The whole active interval's rigidity scale
keeps every internal coefficient away from the far physical collision. -/
theorem internal_coefficient_upper_of_size (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : InverseTemperature)
      (n : ℕ+) (m : ℕ) (_hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
      (ε κ₀ : ℝ), 0 ≤ ε →
      (n : ℝ) ^ ε * (n : ℝ) ^ (s.val / 2) ≤ (n : ℝ) / 2 →
      ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
        (_hx : x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀)
        (r : Fin (((n : ℕ) + m + 1) / 2)) (i : Fin ((n : ℕ) + m + 1)),
        IntervalBoundary.IsInternal ((n : ℕ) + m).succPNat n (i,r) →
        BoundaryEntries.conditionalIntervalWeight β s n m r i x ≤
          C * (n : ℝ) ^ ((s.val + 2) * ε) * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2) := by
  let B := s.val * (s.val + 1) * PeriodicPower.bound (s.val + 2) (by linarith [s.property.1])
  have hB : 0 < B := by
    dsimp only [B]
    exact mul_pos (mul_pos s.property.1 (by linarith [s.property.1])) (PeriodicPower.bound_pos _ _)
  refine ⟨2 * B * (2 : ℝ) ^ (s.val + 2), by positivity, ?_⟩
  intro β n m hn ε κ₀ hε hsize x hx r i hi
  let N := ((n : ℕ) + m).succPNat
  have hend := (internal_iff_end_le N n hn i r).mp hi
  let j : Fin (n : ℕ) := ⟨i.val, by omega⟩
  let k : Fin ((n : ℕ) + 1) := ⟨r.val + 1, by omega⟩
  let L := cyclicGapSum N i (r.val + 1)
    (WithLp.ofLp (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,0)))
  have hLmem := internal_gapSum_mem β s n m x r i hi
  have hdev : |L - ((r.val + 1 : ℕ) : ℝ)| ≤
      (n : ℝ) ^ ε * ((r.val + 1 : ℕ) : ℝ) ^ (s.val / 2) := by
    have h := hx.1.2 j k (by dsimp only [k]; omega)
      (by dsimp only [k]; have := r.isLt; omega) (by dsimp only [j,k]; omega)
    dsimp only [L]
    rw [internal_gapSum_active n m hn x.val r i hi]
    exact h
  have hrn : ((r.val + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : r.val + 1 ≤ n)
  have hr0 : (0 : ℝ) < ((r.val + 1 : ℕ) : ℝ) := by positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hne : (n : ℝ) ^ (-ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (neg_nonpos.mpr hε)
  have hLp : L ≤ (3 / 2 : ℝ) * n := by
    have hp := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hr0.le hrn (by linarith [s.property.1] : 0 ≤ s.val / 2))
      (Real.rpow_nonneg hn0.le ε)
    have hh := le_abs_self (L - ((r.val + 1 : ℕ) : ℝ))
    linarith only [hdev, hp, hsize, hh, hrn]
  let δ := ((r.val + 1 : ℕ) : ℝ) * (n : ℝ) ^ (-ε) / 2
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hL : δ ≤ L := by
    have hh := (PhysicalEnergy.gapSum_bounds n j (r.val + 1) (WithLp.ofLp x.val) hx.1.1).1
    have he : L = cyclicGapSum n j (r.val + 1) (WithLp.ofLp x.val) :=
      internal_gapSum_active n m hn x.val r i hi
    rw [← he] at hh
    dsimp only [δ]
    nlinarith only [hh, mul_pos hr0 (Real.rpow_pos_of_pos hn0 (-ε))]
  have hNL : δ ≤ (N : ℝ) - L := by
    have hN : (2 : ℝ) * n ≤ (N : ℝ) := by exact_mod_cast hn
    have hh := mul_le_mul_of_nonneg_left hne hr0.le
    dsimp only [δ]
    nlinarith only [hLp, hN, hh, hrn]
  have hu := PhysicalEnergy.intervalCoefficient_upper (ofLong β s) N ⟨L,hLmem⟩ hδ hL hNL
  change PhysicalEnergy.intervalCoefficient (ofLong β s) N ⟨L,hLmem⟩ ≤ B * δ ^ (-s.val - 2) at hu
  have hδpow : δ ^ (-s.val - 2) = (2 : ℝ) ^ (s.val + 2) *
      (n : ℝ) ^ ((s.val + 2) * ε) * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2) := by
    dsimp only [δ]
    rw [Real.div_rpow (mul_nonneg hr0.le (Real.rpow_nonneg hn0.le _)) (by norm_num),
      Real.mul_rpow hr0.le (Real.rpow_nonneg hn0.le _), ← Real.rpow_mul hn0.le]
    have he : -ε * (-s.val - 2) = (s.val + 2) * ε := by ring
    rw [he, show -s.val - 2 = -(s.val + 2) by ring, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    simp only [div_inv_eq_mul]
    ring
  have hw : (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) ≤ 2 := by split_ifs <;> norm_num
  have hp := (PhysicalEnergy.intervalCoefficient_pos (ofLong β s) N ⟨L,hLmem⟩).le
  rw [internal_coefficient_formula β s n m x r i hi]
  change (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
    PhysicalEnergy.intervalCoefficient (ofLong β s) N ⟨L,hLmem⟩ ≤ _
  calc
    _ ≤ 2 * PhysicalEnergy.intervalCoefficient (ofLong β s) N ⟨L,hLmem⟩ := mul_le_mul_of_nonneg_right hw hp
    _ ≤ 2 * (B * δ ^ (-s.val - 2)) := mul_le_mul_of_nonneg_left hu (by norm_num)
    _ = _ := by rw [hδpow]; ring


/-- Lemma 5.4 of the paper: the proper coefficient upper bound by
splitting at the paper cutoff. Short intervals use their total gap mass.
Long intervals use the above-cutoff rigidity before the image-series bound. -/
theorem internal_coefficient_upper_paper_cutoff (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : InverseTemperature)
      (n : ℕ+) (m : ℕ) (_hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
      (ε κ₀ : ℝ), 0 ≤ ε →
      ε ≤ paperCutoffThreshold s → 8 ≤ (n : ℝ) ^ ε →
      ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
        (_hx : x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀)
        (r : Fin (((n : ℕ) + m + 1) / 2)) (i : Fin ((n : ℕ) + m + 1)),
        IntervalBoundary.IsInternal ((n : ℕ) + m).succPNat n (i,r) →
        BoundaryEntries.conditionalIntervalWeight β s n m r i x ≤
          C * (n : ℝ) ^ ((s.val + 2) * ε) * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2) := by
  let B := s.val * (s.val + 1) * PeriodicPower.bound (s.val + 2) (by linarith [s.property.1])
  have hB : 0 < B := by
    dsimp only [B]
    exact mul_pos (mul_pos s.property.1 (by linarith [s.property.1])) (PeriodicPower.bound_pos _ _)
  refine ⟨2 * B * (2 : ℝ) ^ (s.val + 2), by positivity, ?_⟩
  intro β n m hn ε κ₀ hε hεsmall hlarge x hx r i hi
  let N := ((n : ℕ) + m).succPNat
  have hend := (internal_iff_end_le N n hn i r).mp hi
  let j : Fin (n : ℕ) := ⟨i.val, by omega⟩
  let L := cyclicGapSum N i (r.val + 1)
    (WithLp.ofLp (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,0)))
  have hLmem := internal_gapSum_mem β s n m x r i hi
  have hrn : ((r.val + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : r.val + 1 ≤ n)
  have hr0 : (0 : ℝ) < ((r.val + 1 : ℕ) : ℝ) := by positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hne : (n : ℝ) ^ (-ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (neg_nonpos.mpr hε)
  have hLp : L ≤ (3 / 2 : ℝ) * n := by
    by_cases hr : r.val + 1 < ⌊(n : ℝ) ^ ε⌋₊ ^ (paperReferenceCutoffExponent s : ℕ)
    · have hh := (proper_short_gap_mass β s n m hn ε κ₀ hε hεsmall x hx r i hi hr).2
      have hp := Real.rpow_le_self_of_one_le hn1 (by norm_num : (1 / 4 : ℝ) ≤ 1)
      change L ≤ (n : ℝ) ^ (1 / 4 : ℝ) at hh
      linarith
    · have hh := (proper_long_gap_rigidity β s n m hn ε κ₀ hlarge x hx r i hi
        (by omega)).2
      change L ≤ 3 / 2 * (r.val + 1 : ℝ) at hh
      simp only [Nat.cast_add, Nat.cast_one] at hrn
      linarith
  let δ := ((r.val + 1 : ℕ) : ℝ) * (n : ℝ) ^ (-ε) / 2
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hL : δ ≤ L := by
    have hh := (PhysicalEnergy.gapSum_bounds n j (r.val + 1) (WithLp.ofLp x.val) hx.1.1).1
    have he : L = cyclicGapSum n j (r.val + 1) (WithLp.ofLp x.val) :=
      internal_gapSum_active n m hn x.val r i hi
    rw [← he] at hh
    dsimp only [δ]
    nlinarith only [hh, mul_pos hr0 (Real.rpow_pos_of_pos hn0 (-ε))]
  have hNL : δ ≤ (N : ℝ) - L := by
    have hN : (2 : ℝ) * n ≤ (N : ℝ) := by exact_mod_cast hn
    have hh := mul_le_mul_of_nonneg_left hne hr0.le
    dsimp only [δ]
    nlinarith only [hLp, hN, hh, hrn]
  have hu := PhysicalEnergy.intervalCoefficient_upper (ofLong β s) N ⟨L,hLmem⟩ hδ hL hNL
  change PhysicalEnergy.intervalCoefficient (ofLong β s) N ⟨L,hLmem⟩ ≤ B * δ ^ (-s.val - 2) at hu
  have hδpow : δ ^ (-s.val - 2) = (2 : ℝ) ^ (s.val + 2) *
      (n : ℝ) ^ ((s.val + 2) * ε) * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2) := by
    dsimp only [δ]
    rw [Real.div_rpow (mul_nonneg hr0.le (Real.rpow_nonneg hn0.le _)) (by norm_num),
      Real.mul_rpow hr0.le (Real.rpow_nonneg hn0.le _), ← Real.rpow_mul hn0.le]
    have he : -ε * (-s.val - 2) = (s.val + 2) * ε := by ring
    rw [he, show -s.val - 2 = -(s.val + 2) by ring, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    simp only [div_inv_eq_mul]
    ring
  have hw : (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) ≤ 2 := by split_ifs <;> norm_num
  have hp := (PhysicalEnergy.intervalCoefficient_pos (ofLong β s) N ⟨L,hLmem⟩).le
  rw [internal_coefficient_formula β s n m x r i hi]
  change (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
    PhysicalEnergy.intervalCoefficient (ofLong β s) N ⟨L,hLmem⟩ ≤ _
  calc
    _ ≤ 2 * PhysicalEnergy.intervalCoefficient (ofLong β s) N ⟨L,hLmem⟩ := mul_le_mul_of_nonneg_right hw hp
    _ ≤ 2 * (B * δ ^ (-s.val - 2)) := mul_le_mul_of_nonneg_left hu (by norm_num)
    _ = _ := by rw [hδpow]; ring

end Riesz2.PhysicalCore.Internal

namespace Riesz2.PhysicalCore

/-- See the proof of Lemma 5.4 in the paper: all actual internal physical coefficients
have a uniform upper power bound. The prefactor depends only on `s` and is
chosen before temperature, epsilon, cutoff exponent and both volumes.
Bounded active sizes use the diagonal cutoff, with no bound on the total
physical period. -/
theorem internal_coefficient_good_upper (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : InverseTemperature)
      (n : ℕ+) (m : ℕ) (_hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
      (ε κ₀ : ℝ), 0 ≤ ε → ε ≤ (1 - s.val / 2) / 2 → 0 ≤ κ₀ →
      ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
        (_hx : x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀)
        (r : Fin (((n : ℕ) + m + 1) / 2)) (i : Fin ((n : ℕ) + m + 1)),
        IntervalBoundary.IsInternal ((n : ℕ) + m).succPNat n (i,r) →
        BoundaryEntries.conditionalIntervalWeight β s n m r i x ≤
          C * (n : ℝ) ^ ((κ₀ + s.val + 2) * ε) * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2) := by
  obtain ⟨D₀, hD₀, hl⟩ := Internal.internal_coefficient_upper_of_size s
  obtain ⟨P, hP, hpaper⟩ := Internal.internal_coefficient_upper_paper_cutoff s
  let D := max D₀ P
  have hD : 0 < D := hD₀.trans_le (le_max_left _ _)
  let a := (1 - s.val / 2) / 2
  have ha : 0 < a := by dsimp only [a]; linarith [s.property.2]
  let B := (2 : ℝ) ^ (1 / a)
  have hB : 0 < B := Real.rpow_pos_of_pos (by norm_num) _
  have hBa : B ^ a = 2 := by
    dsimp only [B]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), one_div_mul_cancel ha.ne', Real.rpow_one]
  refine ⟨max D (B ^ (s.val + 2)), lt_of_lt_of_le hD (le_max_left _ _), ?_⟩
  intro β n m hn ε κ₀ hε hεa hκ₀ x hx r i hi
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hr0 : (0 : ℝ) < ((r.val + 1 : ℕ) : ℝ) := by positivity
  have hend := (Internal.internal_iff_end_le ((n : ℕ) + m).succPNat n hn i r).mp hi
  have hrn : ((r.val + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : r.val + 1 ≤ n)
  have hpow₁ : (n : ℝ) ^ ((s.val + 2) * ε) ≤ (n : ℝ) ^ ((κ₀ + s.val + 2) * ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith only [hκ₀, hε])
  have hpow₂ : (n : ℝ) ^ (κ₀ * ε) ≤ (n : ℝ) ^ ((κ₀ + s.val + 2) * ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith [s.property.1])
  by_cases hlarge : B ≤ (n : ℝ)
  · have hna : (2 : ℝ) ≤ (n : ℝ) ^ a := by
      rw [← hBa]
      exact Real.rpow_le_rpow hB.le hlarge ha.le
    have hsize : (n : ℝ) ^ ε * (n : ℝ) ^ (s.val / 2) ≤ (n : ℝ) / 2 := by
      calc
        _ = (n : ℝ) ^ (ε + s.val / 2) := (Real.rpow_add hn0 _ _).symm
        _ ≤ (n : ℝ) ^ (1 - a) := Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp only [a] at *; linarith)
        _ = (n : ℝ) / (n : ℝ) ^ a := by rw [Real.rpow_sub hn0, Real.rpow_one]
        _ ≤ _ := div_le_div_of_nonneg_left hn0.le (by norm_num) hna
    have hu : BoundaryEntries.conditionalIntervalWeight β s n m r i x ≤
        D * (n : ℝ) ^ ((s.val + 2) * ε) * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2) := by
      by_cases hp : ε ≤ paperCutoffThreshold s ∧ 8 ≤ (n : ℝ) ^ ε
      · exact (hpaper β n m hn ε κ₀ hε hp.1 hp.2 x hx r i hi).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _)
            (Real.rpow_nonneg hn0.le _)) (Real.rpow_nonneg hr0.le _))
      · exact (hl β n m hn ε κ₀ hε hsize x hx r i hi).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
            (Real.rpow_nonneg hn0.le _)) (Real.rpow_nonneg hr0.le _))
    apply hu.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hr0.le _)
    exact mul_le_mul (le_max_left _ _) hpow₁ (Real.rpow_nonneg hn0.le _) (le_trans hD.le (le_max_left _ _))
  · have hsmall : (n : ℝ) ≤ B := le_of_not_ge hlarge
    have hrv : ((r.val + 1 : ℕ) : ℝ) ^ (s.val + 2) ≤ B ^ (s.val + 2) :=
      Real.rpow_le_rpow hr0.le (hrn.trans hsmall) (by linarith [s.property.1])
    have hrprod : ((r.val + 1 : ℕ) : ℝ) ^ (s.val + 2) *
        ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2) = 1 := by
      rw [← Real.rpow_add hr0]
      norm_num
    have hweight : 1 ≤ max D (B ^ (s.val + 2)) * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2) := by
      calc
        1 = ((r.val + 1 : ℕ) : ℝ) ^ (s.val + 2) * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2) := hrprod.symm
        _ ≤ _ := mul_le_mul_of_nonneg_right (hrv.trans (le_max_right _ _)) (Real.rpow_nonneg hr0.le _)
    have hu := Internal.internal_coefficient_diagonal_bound β s n m hn ε κ₀ x hx r i hi
    calc
      _ ≤ (n : ℝ) ^ (κ₀ * ε) := hu
      _ ≤ (n : ℝ) ^ ((κ₀ + s.val + 2) * ε) := hpow₂
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hweight
          (Real.rpow_nonneg hn0.le ((κ₀ + s.val + 2) * ε))
        simpa only [mul_one, one_mul, mul_assoc, mul_left_comm, mul_comm] using hh

end Riesz2.PhysicalCore

namespace Riesz2.PhysicalCore

/-- The forcing Hessian is bounded uniformly in both volumes and every
nonnegative epsilon. The constant is chosen from the cutoff data. -/
theorem forcingHessian_uniform_bound (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ+) (m : ℕ) (ε : ℝ), 0 ≤ ε →
      ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (i j : Fin (n : ℕ)),
        forcingHessian n θ ε x.val i j ≤ C := by
  obtain ⟨C, hC, hb, _⟩ := θ.property.2.2.2.2
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  refine ⟨C,hC0,fun n m ε hε x i j => ?_⟩
  rw [forcingHessian_apply n m θ ε x i j]
  split_ifs
  · have ht := hb ((n : ℝ) ^ (-ε) * x.val i)
      (mul_pos (Real.rpow_pos_of_pos (by exact_mod_cast n.pos) _) (x.property.1 i))
    have hp : 1 ≤ (n : ℝ) ^ ε := Real.one_le_rpow (by exact_mod_cast n.pos) hε
    have hden : 1 ≤ ((n : ℝ) ^ ε) ^ 2 := one_le_pow₀ hp
    exact (div_le_self ht.1 hden).trans ht.2
  · exact hC0.le

/-- See the proof of Lemma 5.4 in the paper: the whole actual coefficient family has
the upper bound in the periodized predicate, on both freezing
branches, including the forcing singletons. Its exponent is independent of
temperature and epsilon. -/
theorem properIntervalWeight_upper (s : Riesz1.RieszExponent) (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : InverseTemperature)
      (n : ℕ+) (m : ℕ) (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
      (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : 2 * (n : ℕ) ≤ (M : ℕ))
      (K : ℕ) (ε κ₀ : ℝ), 0 ≤ ε → ε ≤ (1 - s.val / 2) / 2 → 0 ≤ κ₀ →
      ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
        (i : Fin (M : ℕ)) (r : Fin ((M : ℕ) / 2)),
        properIntervalWeight β s n m hn M hM hnM K θ ε κ₀ i r x ≤
          C * (n : ℝ) ^ ((κ₀ + s.val + 2) * ε) * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2) := by
  obtain ⟨D,hD,hphys⟩ := internal_coefficient_good_upper s
  obtain ⟨F,hF,hforce⟩ := forcingHessian_uniform_bound θ
  obtain ⟨B,hB,href⟩ := BoundaryEntries.referenceWeight_bound s
  let C := max B (D + F)
  have hC : 0 < C := lt_of_lt_of_le hB (le_max_left _ _)
  refine ⟨C,hC,fun β n m hn M hM hnM K ε κ₀ hε hεa hκ₀ x i r => ?_⟩
  let v := (n : ℝ) ^ ((κ₀ + s.val + 2) * ε)
  let w := ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2)
  have hv : 1 ≤ v := Real.one_le_rpow (by exact_mod_cast n.pos) (by nlinarith [s.property.1])
  have hw : 0 ≤ w := Real.rpow_nonneg (by positivity) _
  have hreference : BoundaryEntries.referenceWeight s M hM K (i,r) ≤ C * v * w := by
    have hh := href M hM K (i,r)
    change _ ≤ C * v * w
    have hh' : BoundaryEntries.referenceWeight s M hM K (i,r) ≤ B * w := by
      simpa only [w,Nat.cast_add,Nat.cast_one] using hh
    apply hh'.trans
    apply mul_le_mul_of_nonneg_right _ hw
    exact (le_max_left B (D + F)).trans (le_mul_of_one_le_right hC.le hv)
  by_cases hx : x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀
  · by_cases hi : IntervalBoundary.IsInternal M n (i,r)
    · have hend := (Internal.internal_iff_end_le M n hnM i r).mp hi
      let r' : Fin (((n : ℕ) + m + 1) / 2) := ⟨r.val,by omega⟩
      let i' : Fin ((n : ℕ) + m + 1) := ⟨i.val,by omega⟩
      have hip : IntervalBoundary.IsInternal ((n : ℕ) + m).succPNat n (i',r') :=
        (Internal.internal_iff_end_le ((n : ℕ) + m).succPNat n hn i' r').mpr hend
      have hh : BoundaryEntries.conditionalIntervalWeight β s n m r' i' x ≤ D * v * w :=
        hphys β n m hn ε κ₀ hε hεa hκ₀ x hx r' i' hip
      have hf : (if r.val = 0 then forcingHessian n θ ε x.val
          ⟨i.val,by omega⟩ ⟨i.val,by omega⟩ else 0) ≤ F * v * w := by
        split_ifs with hr
        · have he : w = 1 := by simp only [w,hr,Nat.zero_add,Nat.cast_one,Real.one_rpow]
          rw [he,mul_one]
          exact (hforce n m ε hε x _ _).trans (le_mul_of_one_le_right hF.le hv)
        · exact mul_nonneg (mul_nonneg hF.le (le_trans zero_le_one hv)) hw
      have hs := add_le_add hh hf
      apply (show properIntervalWeight β s n m hn M hM hnM K θ ε κ₀ i r x ≤
        (D + F) * v * w from by
          simpa only [properIntervalWeight,ite_eq_left hx,dite_eq_left hi,← add_mul,r',i'] using hs).trans
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (le_trans zero_le_one hv)) hw
    · simpa only [properIntervalWeight,ite_eq_left hx,dite_eq_right hi] using hreference
  · simpa only [properIntervalWeight,ite_eq_right hx] using hreference

end Riesz2.PhysicalCore
