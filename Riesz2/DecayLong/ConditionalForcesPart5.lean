/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.ConditionalForcesPart4

/-!
# Pinned particle estimates for conditional force differences

Physical geometry and differential identities for equation (5.28) in
the proof of Lemma 5.8.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology BigOperators Fin.NatCast

namespace Riesz2.ConditionalForces

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- Internal cumulative-position bounds from the coordinate part of the
literal good event Subsection 5.1. They apply to every pinned particle,
including the two end particles. -/
theorem good_pinned_positions_internal (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ) (ε κ₀ : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (hx : x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀) :
    let t := fun r : Fin ((n : ℕ) + 1) => ∑ i : Fin (n : ℕ) with i.val < r.val, x.val i
    (∀ r, (r.val : ℝ) * (n : ℝ) ^ (-ε) ≤ t r ∧
      t r ≤ (r.val : ℝ) * (n : ℝ) ^ ε) ∧
    ∀ r q, r ≤ q →
      ((q.val - r.val : ℕ) : ℝ) * (n : ℝ) ^ (-ε) ≤ t q - t r ∧
      t q - t r ≤ ((q.val - r.val : ℕ) : ℝ) * (n : ℝ) ^ ε := by
  classical
  intro t
  have hc := hx.1.1
  have hcard (r : Fin ((n : ℕ) + 1)) :
      (Finset.univ.filter (fun i : Fin (n : ℕ) => i.val < r.val)).card = r.val := by
    have he : Finset.univ.filter (fun i : Fin (n : ℕ) => i.val < r.val) =
        (Finset.range r.val).attach.map
          ⟨(fun i => (⟨i.val, by have := (Finset.mem_range.mp i.property); omega⟩ : Fin (n : ℕ))),
            fun i j h => Subtype.ext (congrArg Fin.val h)⟩ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Finset.mem_attach, true_and, Subtype.exists, Finset.mem_range]
      constructor
      · intro h
        exact ⟨i.val, h, Fin.ext rfl⟩
      · rintro ⟨a, ha, he⟩
        have := congrArg Fin.val he
        change a = i.val at this
        omega
    rw [he, Finset.card_map, Finset.card_attach, Finset.card_range]
  have hb (r q : Fin ((n : ℕ) + 1)) (hrq : r ≤ q) :
      t q - t r = ∑ i : Fin (n : ℕ) with r.val ≤ i.val ∧ i.val < q.val, x.val i := by
    have hsub : Finset.univ.filter (fun i : Fin (n : ℕ) => i.val < r.val) ⊆
        Finset.univ.filter (fun i : Fin (n : ℕ) => i.val < q.val) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact lt_of_lt_of_le hi hrq
    rw [show t q - t r =
        (∑ i ∈ Finset.univ.filter (fun i : Fin (n : ℕ) => i.val < q.val), x.val i) -
          ∑ i ∈ Finset.univ.filter (fun i : Fin (n : ℕ) => i.val < r.val), x.val i from rfl,
      ← Finset.sum_sdiff hsub, add_sub_cancel_right]
    apply Finset.sum_congr
    · ext i
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
      tauto
    · intro _ _
      rfl
  have hsegcard (r q : Fin ((n : ℕ) + 1)) (hrq : r ≤ q) :
      (Finset.univ.filter (fun i : Fin (n : ℕ) => r.val ≤ i.val ∧ i.val < q.val)).card =
        q.val - r.val := by
    have he : Finset.univ.filter (fun i : Fin (n : ℕ) => r.val ≤ i.val ∧ i.val < q.val) =
        (Finset.univ.filter (fun i : Fin (n : ℕ) => i.val < q.val)) \
          (Finset.univ.filter (fun i : Fin (n : ℕ) => i.val < r.val)) := by
      ext i
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
      tauto
    rw [he, Finset.card_sdiff_of_subset]
    · rw [hcard, hcard]
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact lt_of_lt_of_le hi hrq
  constructor
  · intro r
    constructor
    · calc
        _ = ∑ i ∈ Finset.univ.filter (fun i : Fin (n : ℕ) => i.val < r.val), (n : ℝ) ^ (-ε) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
        _ ≤ t r := Finset.sum_le_sum (fun i _ => (hc i).1)
    · calc
        _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin (n : ℕ) => i.val < r.val), (n : ℝ) ^ ε :=
          Finset.sum_le_sum (fun i _ => (hc i).2)
        _ = _ := by rw [Finset.sum_const, hcard, nsmul_eq_mul]
  · intro r q hrq
    rw [hb r q hrq]
    constructor
    · calc
        _ = ∑ i ∈ Finset.univ.filter (fun i : Fin (n : ℕ) => r.val ≤ i.val ∧ i.val < q.val),
            (n : ℝ) ^ (-ε) := by rw [Finset.sum_const, hsegcard r q hrq, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum (fun i _ => (hc i).1)
    · calc
        _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin (n : ℕ) => r.val ≤ i.val ∧ i.val < q.val),
            (n : ℝ) ^ ε := Finset.sum_le_sum (fun i _ => (hc i).2)
        _ = _ := by rw [Finset.sum_const, hsegcard r q hrq, nsmul_eq_mul]

/-- The good-event geometry in the proof of Lemma 5.8:
the actual pinned diagonal dominates the coupling to the particle moved by
an adjacent force. The displayed loss is independent of temperature and ε.
Positions are the literal sums of the retained gaps, in microscopic units. -/
theorem good_pinned_diagonal_internal (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ) (ε κ₀ : ℝ) (hε : 0 ≤ ε)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (hx : x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀)
    (j : Fin ((n : ℕ) - 1)) (Z : ℝ)
    (hZ : (∑ i, x.val i) < Z ∧ Z < ((n : ℝ) + m + 1)) :
    let N := ((n : ℕ) + m).succPNat
    let t := fun r : Fin ((n : ℕ) + 1) => ∑ i : Fin (n : ℕ) with i.val < r.val, x.val i
    ∃ hsep : ∀ r, 0 < Z - t r ∧ Z - t r < (N : ℝ),
      (2 : ℝ) ^ (-s.val - 3) * (n : ℝ) ^ (-(2 * (s.val + 2)) * ε) *
          (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) *
          (2 * PhysicalEnergy.intervalCoefficient (ofLong β s) N
            ⟨Z - t ⟨j.val + 1, by have := j.isLt; omega⟩,
              hsep ⟨j.val + 1, by have := j.isLt; omega⟩⟩) ≤
        ∑ r, 2 * PhysicalEnergy.intervalCoefficient (ofLong β s) N ⟨Z - t r, hsep r⟩ := by
  classical
  intro N t
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  let p : Fin ((n : ℕ) + 1) := ⟨j.val + 1, by have := j.isLt; omega⟩
  let d : ℕ := min (j.val + 1) ((n : ℕ) - (j.val + 1))
  let δ : ℕ := min (j.val + 1) ((n : ℕ) - j.val)
  have hd0 : 0 < d := by dsimp [d]; have := j.isLt; omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have hδ : (δ : ℝ) ≤ 2 * (d : ℝ) := by
    exact_mod_cast (show δ ≤ 2 * d by dsimp [δ, d]; have := j.isLt; omega)
  have ht := good_pinned_positions_internal β s n m ε κ₀ x hx
  change (∀ r, (r.val : ℝ) * (n : ℝ) ^ (-ε) ≤ t r ∧
      t r ≤ (r.val : ℝ) * (n : ℝ) ^ ε) ∧
    (∀ r q, r ≤ q → ((q.val - r.val : ℕ) : ℝ) * (n : ℝ) ^ (-ε) ≤ t q - t r ∧
      t q - t r ≤ ((q.val - r.val : ℕ) : ℝ) * (n : ℝ) ^ ε) at ht
  have hlast : t (Fin.last (n : ℕ)) = ∑ i, x.val i := by
    dsimp only [t]
    simp only [Fin.val_last, Fin.is_lt, Finset.sum_filter,
      ↓reduceIte]
  have ht0 (r) : 0 ≤ t r := by
    exact (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hn0.le _)).trans (ht.1 r).1
  have htlast (r) : t r ≤ ∑ i, x.val i := by
    have h := (ht.2 r (Fin.last _) (Fin.le_last _)).1
    rw [hlast] at h
    have hp : 0 ≤ ((n : ℕ) - (r : Fin ((n : ℕ) + 1)).val : ℕ) * (n : ℝ) ^ (-ε) := by
      positivity
    exact le_of_sub_nonneg (hp.trans h)
  have hsep (r) : 0 < Z - t r ∧ Z - t r < (N : ℝ) := by
    have hN : (N : ℝ) = (n : ℝ) + m + 1 := by simp [N, Nat.cast_add]
    constructor
    · linarith [htlast r, hZ.1]
    · rw [hN]
      linarith [ht0 r, hZ.2]
  refine ⟨hsep, ?_⟩
  let L : {L : ℝ // 0 < L ∧ L < (N : ℝ)} := ⟨Z - t p, hsep p⟩
  let R : Fin ((n : ℕ) + 1) → {L : ℝ // 0 < L ∧ L < (N : ℝ)} :=
    fun r => ⟨Z - t r, hsep r⟩
  let e : Fin d → Fin ((n : ℕ) + 1) := fun b =>
    ⟨p.val + b.val, by dsimp [p, d] at *; have := b.isLt; omega⟩
  have heinj : Function.Injective e := by
    intro a b he
    have he := congrArg Fin.val he
    exact Fin.ext (Nat.add_left_cancel he)
  let S := Finset.univ.image e
  have hcard : S.card = d := by
    rw [Finset.card_image_of_injective _ heinj, Finset.card_univ, Fintype.card_fin]
  let a : ℝ := (d : ℝ) * (n : ℝ) ^ (-ε)
  let D : ℝ := (d : ℝ) * (n : ℝ) ^ ε
  have ha : 0 < a := by dsimp [a]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hlower : a ≤ L.val ∧ a ≤ (N : ℝ) - L.val := by
    have hl := (ht.2 p (Fin.last _) (Fin.le_last _)).1
    rw [hlast] at hl
    simp only [Fin.val_last] at hl
    have hdleft : (d : ℝ) ≤ p.val := by exact_mod_cast (min_le_left _ _)
    have hdright : (d : ℝ) ≤ ((n : ℕ) - p.val : ℕ) := by
      exact_mod_cast (min_le_right _ _)
    have hleft := mul_le_mul_of_nonneg_right hdright (Real.rpow_nonneg hn0.le (-ε))
    have hright := mul_le_mul_of_nonneg_right hdleft (Real.rpow_nonneg hn0.le (-ε))
    have hp := (ht.1 p).1
    have hN : (N : ℝ) = (n : ℝ) + m + 1 := by simp [N, Nat.cast_add]
    dsimp only [a, L]
    rw [hN]
    constructor <;> linarith [hZ.1, hZ.2]
  have hnear (r) (hr : r ∈ S) : |(R r).val - L.val| ≤ D := by
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hr
    have hp : p ≤ e b := by change p.val ≤ p.val + b.val; omega
    have hseg := ht.2 p (e b) hp
    have hnum : ((e b).val - p.val : ℕ) = b.val := by dsimp [e]; omega
    rw [hnum] at hseg
    have hnon : 0 ≤ t (e b) - t p :=
      (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hn0.le _)).trans hseg.1
    have hbd : (b.val : ℝ) ≤ d := by exact_mod_cast b.isLt.le
    have hmul := mul_le_mul_of_nonneg_right hbd (Real.rpow_nonneg hn0.le ε)
    dsimp only [R, L, D]
    rw [show Z - t (e b) - (Z - t p) = -(t (e b) - t p) by ring,
      abs_neg, abs_of_nonneg hnon]
    exact hseg.2.trans hmul
  have hcomp := pinned_diagonal_comparison_internal (ofLong β s) N L R S a D
    (d : ℝ) ha hD (by rw [hcard]) hlower.1 hlower.2 hnear
  have hquot : D / a = (n : ℝ) ^ (2 * ε) := by
    dsimp only [D, a]
    rw [mul_div_mul_left _ _ hdR.ne', ← Real.rpow_sub hn0]
    congr 1
    ring
  have hnε : 1 ≤ (n : ℝ) ^ (2 * ε) :=
    Real.one_le_rpow hn1 (by positivity)
  have hpow : (2 : ℝ) ^ (-s.val - 2) * (n : ℝ) ^ (-(2 * (s.val + 2)) * ε) ≤
      (1 + D / a) ^ (-s.val - 2) := by
    rw [hquot]
    have h := Real.rpow_le_rpow_of_nonpos
      (by positivity : 0 < 1 + (n : ℝ) ^ (2 * ε))
      (show 1 + (n : ℝ) ^ (2 * ε) ≤ 2 * (n : ℝ) ^ (2 * ε) by linarith)
      (by linarith [s.property.1] : -s.val - 2 ≤ 0)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity),
      ← Real.rpow_mul hn0.le] at h
    convert h using 1
    congr 2
    ring
  have htwo : (2 : ℝ) ^ (-s.val - 3) * 2 = (2 : ℝ) ^ (-s.val - 2) := by
    calc
      _ = (2 : ℝ) ^ (-s.val - 3) * (2 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (2 : ℝ) ^ ((-s.val - 3) + 1) := (Real.rpow_add (by norm_num) _ _).symm
      _ = _ := by congr 1; ring
  have hfac : (2 : ℝ) ^ (-s.val - 3) * (n : ℝ) ^ (-(2 * (s.val + 2)) * ε) * (δ : ℝ) ≤
      (d : ℝ) * (1 + D / a) ^ (-s.val - 2) := by
    calc
      _ ≤ (2 : ℝ) ^ (-s.val - 3) * (n : ℝ) ^ (-(2 * (s.val + 2)) * ε) * (2 * (d : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hδ (by positivity)
      _ = (d : ℝ) * ((2 : ℝ) ^ (-s.val - 2) * (n : ℝ) ^ (-(2 * (s.val + 2)) * ε)) := by
        rw [← htwo]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow hdR.le
  have hcouple : 0 ≤ 2 * PhysicalEnergy.intervalCoefficient (ofLong β s) N L :=
    mul_nonneg (by norm_num) (PhysicalEnergy.intervalCoefficient_pos _ _ _).le
  exact (mul_le_mul_of_nonneg_right hfac hcouple).trans hcomp

/-- Cyclic telescoping used in the pinned chart of
the proof of Lemma 5.8. Particle displacements produce consecutive
gap differences. The interval sum is exactly the difference of the
two endpoint displacements, including intervals that cross the period. -/
theorem particle_displacement_interval_internal (N : ℕ+) (H : Fin (N : ℕ) → ℝ)
    (i : Fin (N : ℕ)) (r : ℕ) :
    cyclicGapSum N i r (fun a => H (a + 1) - H a) = H (i + (r : Fin (N : ℕ))) - H i := by
  have hi (a : ℕ) : (⟨(i.val + a) % (N : ℕ), Nat.mod_lt _ N.pos⟩ : Fin (N : ℕ)) =
      i + (a : Fin (N : ℕ)) := by
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_natCast, Nat.add_mod_mod]
  unfold cyclicGapSum
  simp_rw [hi]
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    have he : (i + (r : Fin (N : ℕ))) + 1 = i + ((r + 1 : ℕ) : Fin (N : ℕ)) := by
      rw [Nat.cast_add, Nat.cast_one, add_assoc]
    rw [he]
    ring

/-- The actual ambient Hessian in particle displacement coordinates, from
the proof of Lemma 5.8. This is an identity with the physical
interval coefficients, including the antipodal multiplicity. -/
theorem physical_hessian_particle_displacements_internal (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (N : ℕ+)
    (U : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ)
    (hU : ∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
      U y.val = β.val * physicalAmbientGapEnergy (ofLong β s) N y)
    (y : EuclideanSpace ℝ (Fin (N : ℕ)))
    (hy : WithLp.ofLp y ∈ Riesz1.gapSimplex N) (H K : Fin (N : ℕ) → ℝ) :
    fderiv ℝ (fderiv ℝ U) y
        (WithLp.toLp 2 (fun a => H (a + 1) - H a))
        (WithLp.toLp 2 (fun a => K (a + 1) - K a)) =
      β.val * ∑ r : Fin ((N : ℕ) / 2), ∑ i : Fin (N : ℕ),
        BoundaryEntries.intervalWeight s N r i y *
          ((H (i + ((r.val + 1 : ℕ) : Fin (N : ℕ))) - H i) *
            (K (i + ((r.val + 1 : ℕ) : Fin (N : ℕ))) - K i)) := by
  rw [physical_hessian_intervals_internal β s N U hU y hy]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  rw [← BoundaryEntries.gapSum_eq_interval_sum N i
      ((Nat.succ_le_of_lt r.isLt).trans (Nat.div_le_self _ _)),
    ← BoundaryEntries.gapSum_eq_interval_sum N i
      ((Nat.succ_le_of_lt r.isLt).trans (Nat.div_le_self _ _))]
  rw [particle_displacement_interval_internal, particle_displacement_interval_internal]

/-- An adjacent active gap difference moves exactly one pinned particle,
as used in the proof of Lemma 5.8. The sign convention is positive
on the gap preceding that particle and negative on the following gap. -/
theorem adjacent_particle_displacement_internal (n : ℕ+) (m : ℕ)
    (j : Fin ((n : ℕ) - 1)) :
    let N := ((n : ℕ) + m).succPNat
    let p : Fin (N : ℕ) := ⟨j.val + 1, by have := j.isLt; simp only [N, Nat.succPNat_coe]; omega⟩
    let i : Fin (N : ℕ) := ⟨j.val, by have := j.isLt; simp only [N, Nat.succPNat_coe]; omega⟩
    WithLp.toLp 2 (fun a : Fin (N : ℕ) =>
      (if a + 1 = p then (1 : ℝ) else 0) - (if a = p then (1 : ℝ) else 0)) =
        EuclideanSpace.single i 1 - EuclideanSpace.single p 1 := by
  intro N p i
  have hpi : i + 1 = p := by
    apply Fin.ext
    rw [Fin.val_add_one_of_lt' (by dsimp [i, N]; have := j.isLt; omega)]
  ext a
  have he : a + 1 = p ↔ a = i := by rw [← hpi]; exact add_right_cancel_iff
  simp only [PiLp.sub_apply, EuclideanSpace.single, PiLp.single_apply,
    he]

/-- The original exterior gap directions have pinned particle
primitives. They give test directions in the variational Brascamp–Lieb formula
in the proof of Lemma 5.8. -/
theorem exterior_particle_primitive_internal (n : ℕ+) (m : ℕ)
    (h : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)))
    (hsum : ∑ a, h a = 0)
    (hactive : ∀ a : Fin (n : ℕ), h (a.castAdd m).castSucc = 0) :
    let H := fun a : Fin ((n : ℕ) + m + 1) => Fin.partialSum (WithLp.ofLp h) a.castSucc
    (∀ a, a.val ≤ (n : ℕ) → H a = 0) ∧
      h = WithLp.toLp 2 (fun a => H (a + 1) - H a) := by
  intro H
  have hpinned (a : Fin ((n : ℕ) + m + 1)) (ha : a.val ≤ (n : ℕ)) : H a = 0 := by
    rw [show H a = Fin.partialSum (WithLp.ofLp h) a.castSucc from rfl,
      Riesz1.partialSum_eq_sum_filter_real]
    apply Finset.sum_eq_zero
    intro b hb
    have hb : b.val < a.val := (Finset.mem_filter.mp hb).2
    let b' : Fin (n : ℕ) := ⟨b.val, by omega⟩
    have he : b = (b'.castAdd m).castSucc := Fin.ext rfl
    exact he ▸ hactive b'
  refine ⟨hpinned, ?_⟩
  ext a
  have hstep := Fin.partialSum_succ (WithLp.ofLp h) a
  change Fin.partialSum (WithLp.ofLp h) a.succ = H a + h a at hstep
  by_cases ha : a.val + 1 < (n : ℕ) + m + 1
  · have he : (a + 1).castSucc = a.succ := by
      apply Fin.ext
      simpa only [Fin.val_castSucc, Fin.val_succ] using Fin.val_add_one_of_lt' ha
    change h a = H (a + 1) - H a
    change h a = Fin.partialSum (WithLp.ofLp h) (a + 1).castSucc - H a
    rw [he, hstep]
    ring
  · have ha' : a.val + 1 = (n : ℕ) + m + 1 := by have := a.isLt; omega
    have he : a.succ = Fin.last ((n : ℕ) + m + 1) := Fin.ext ha'
    have hz : a + 1 = 0 := by
      have halast : a = Fin.last ((n : ℕ) + m) := by
        apply Fin.ext
        simp only [Fin.val_last]
        omega
      simp [halast]
    rw [he, Riesz1.partialSum_last_real, hsum] at hstep
    change h a = H (a + 1) - H a
    rw [hz, hpinned 0 (by simp)]
    linarith

/-- In particle displacement coordinates the actual conditional Hessian
dominates the sum of pinned-to-exterior squares. The discarded terms are
the nonnegative exterior interaction graph (the proof of Lemma 5.8).
This formulation works in the original chart and retains every physical
interval multiplicity. -/
theorem physical_pinned_hessian_lower_internal (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (U : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ)
    (hU : ∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) //
        y ∈ gapAmbientDomain ((n : ℕ) + m).succPNat},
      U y.val = β.val * physicalAmbientGapEnergy (ofLong β s) ((n : ℕ) + m).succPNat y)
    (y : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)))
    (hy : WithLp.ofLp y ∈ Riesz1.gapSimplex ((n : ℕ) + m).succPNat)
    (H : Fin ((n : ℕ) + m + 1) → ℝ) (hH : ∀ a, a.val ≤ (n : ℕ) → H a = 0) :
    let N := ((n : ℕ) + m).succPNat
    β.val * (∑ r : Fin (((n : ℕ) + m + 1) / 2), ∑ i : Fin ((n : ℕ) + m + 1),
      let e := i + ((r.val + 1 : ℕ) : Fin ((n : ℕ) + m + 1))
      BoundaryEntries.intervalWeight s N r i y *
        (if i.val ≤ (n : ℕ) ∧ (n : ℕ) < e.val then (H e) ^ 2
          else if (n : ℕ) < i.val ∧ e.val ≤ (n : ℕ) then (H i) ^ 2 else 0)) ≤
      fderiv ℝ (fderiv ℝ U) y
        (WithLp.toLp 2 (fun a => H (a + 1) - H a))
        (WithLp.toLp 2 (fun a => H (a + 1) - H a)) := by
  intro N
  erw [physical_hessian_particle_displacements_internal β s N U hU y hy H H]
  apply mul_le_mul_of_nonneg_left _ β.property.le
  apply Finset.sum_le_sum
  intro r _
  apply Finset.sum_le_sum
  intro i _
  let e := i + ((r.val + 1 : ℕ) : Fin ((n : ℕ) + m + 1))
  have hw := BoundaryEntries.intervalWeight_nonneg β s N r i y hy
  dsimp only
  change BoundaryEntries.intervalWeight s N r i y *
    (if i.val ≤ (n : ℕ) ∧ (n : ℕ) < e.val then H e ^ 2
      else if (n : ℕ) < i.val ∧ e.val ≤ (n : ℕ) then H i ^ 2 else 0) ≤
    BoundaryEntries.intervalWeight s N r i y * ((H e - H i) * (H e - H i))
  apply mul_le_mul_of_nonneg_left _ hw
  split_ifs with h₁ h₂
  · rw [hH i h₁.1, sub_zero, pow_two]
  · rw [hH e h₂.2, zero_sub, neg_mul_neg, pow_two]
  · exact (sq_nonneg (H e - H i)).trans_eq (pow_two _)

/-- The mixed physical Hessian for an adjacent force, in the same pinned
particle directions. Its coefficients are precisely the negative couplings
to the moved particle. The compensation cancels (the proof of Lemma 5.8). -/
theorem physical_adjacent_mixed_internal (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (U : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ)
    (hU : ∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) //
        y ∈ gapAmbientDomain ((n : ℕ) + m).succPNat},
      U y.val = β.val * physicalAmbientGapEnergy (ofLong β s) ((n : ℕ) + m).succPNat y)
    (y : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)))
    (hy : WithLp.ofLp y ∈ Riesz1.gapSimplex ((n : ℕ) + m).succPNat)
    (j : Fin ((n : ℕ) - 1))
    (H : Fin ((n : ℕ) + m + 1) → ℝ) (hH : ∀ a, a.val ≤ (n : ℕ) → H a = 0) :
    let N := ((n : ℕ) + m).succPNat
    let p : Fin (N : ℕ) := ⟨j.val + 1, by have := j.isLt; simp only [N, Nat.succPNat_coe]; omega⟩
    let i : Fin (N : ℕ) := ⟨j.val, by have := j.isLt; simp only [N, Nat.succPNat_coe]; omega⟩
    fderiv ℝ (fderiv ℝ U) y
        (EuclideanSpace.single i 1 - EuclideanSpace.single p 1)
        (WithLp.toLp 2 (fun a => H (a + 1) - H a)) =
      -β.val * ∑ r : Fin (((n : ℕ) + m + 1) / 2), ∑ a : Fin ((n : ℕ) + m + 1),
        let e := a + ((r.val + 1 : ℕ) : Fin ((n : ℕ) + m + 1))
        BoundaryEntries.intervalWeight s N r a y *
          (if a = p then H e else if e = p then H a else 0) := by
  intro N p i
  let P : Fin ((n : ℕ) + m + 1) → ℝ := fun a => if a = p then 1 else 0
  have hp : H p = 0 := hH p (by dsimp [p]; have := j.isLt; omega)
  erw [← adjacent_particle_displacement_internal n m j]
  change fderiv ℝ (fderiv ℝ U) y (WithLp.toLp 2 (fun a => P (a + 1) - P a))
    (WithLp.toLp 2 (fun a => H (a + 1) - H a)) = _
  erw [physical_hessian_particle_displacements_internal β s N U hU y hy P H]
  rw [neg_mul, ← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  let e := a + ((r.val + 1 : ℕ) : Fin (N : ℕ))
  change BoundaryEntries.intervalWeight s N r a y *
      ((P e - P a) * (H e - H a)) =
    -(BoundaryEntries.intervalWeight s N r a y *
      (if a = p then H e else if e = p then H a else 0))
  by_cases ha : a = p
  · subst a
    by_cases he : e = p <;> simp [P, he, hp]
  · by_cases he : e = p <;> simp [P, ha, he, hp]

/-- Exact adjacent crossing energy from the endpoint representation of
the proof of Lemma 5.8. The four entries are the quadratic form on
`e_j-e_(j+1)`. This avoids any ambient Hessian contribution from intervals
entirely inside the active block. -/
theorem physical_adjacent_crossing_identity_internal (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (j : Fin ((n : ℕ) - 1)) :
    let a : Fin (n : ℕ) := ⟨j.val, by have := j.isLt; omega⟩
    let b : Fin (n : ℕ) := ⟨j.val + 1, by have := j.isLt; omega⟩
    let S := BoundaryEntries.physicalCrossing β s n m x
    S a a - S a b - S b a + S b b =
      BoundaryEntries.physicalPrefix β s n m x j +
        BoundaryEntries.physicalSuffix β s n m x j := by
  intro a b S
  have ha := BoundaryEntries.physicalCrossing_increment β s n m hn x a j
  have hb := BoundaryEntries.physicalCrossing_increment β s n m hn x b j
  change S a b - S a a = _ at ha
  change S b b - S b a = _ at hb
  rw [ite_eq_left (by dsimp [a]; omega)] at ha
  rw [ite_eq_right (by dsimp [b]; omega)] at hb
  linarith only [ha, hb]

/-- Elementary endpoint-profile comparison in
the proof of Lemma 5.8: the two neighboring depths differ by at most
a factor two, including the last admissible adjacent pair. -/
theorem adjacent_endpoint_profiles_internal (s : Riesz1.RieszExponent)
    (n : ℕ+) (j : Fin ((n : ℕ) - 1)) :
    let δ : ℕ := min (j.val + 1) ((n : ℕ) - j.val)
    (j.val + 1 : ℝ) ^ (-s.val) * (δ : ℝ)⁻¹ +
        ((n : ℝ) - j.val - 1) ^ (-s.val) *
          ((min (j.val + 2) ((n : ℕ) - (j.val + 1)) : ℕ) : ℝ)⁻¹ ≤
      (1 + (2 : ℝ) ^ (s.val + 1)) * (δ : ℝ) ^ (-1 - s.val) := by
  intro δ
  let δ' : ℕ := min (j.val + 2) ((n : ℕ) - (j.val + 1))
  have hj := j.isLt
  have hδ : (0 : ℝ) < δ := by exact_mod_cast (show 0 < δ by dsimp [δ]; omega)
  have hδ' : (0 : ℝ) < δ' := by exact_mod_cast (show 0 < δ' by dsimp [δ']; omega)
  have hleft : (δ : ℝ) ≤ j.val + 1 := by exact_mod_cast (min_le_left _ _)
  have hright : (δ : ℝ) ≤ 2 * ((n : ℝ) - j.val - 1) := by
    have h : δ ≤ 2 * ((n : ℕ) - j.val - 1) := by dsimp [δ]; omega
    have he : (((n : ℕ) - j.val - 1 : ℕ) : ℝ) = (n : ℝ) - j.val - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
    have hR : (δ : ℝ) ≤ 2 * (((n : ℕ) - j.val - 1 : ℕ) : ℝ) := by exact_mod_cast h
    rwa [he] at hR
  have hdepth : (δ : ℝ) ≤ 2 * (δ' : ℝ) := by
    exact_mod_cast (show δ ≤ 2 * δ' by dsimp [δ, δ']; omega)
  have hpowleft := Real.rpow_le_rpow_of_nonpos hδ hleft
    (neg_nonpos.mpr s.property.1.le)
  have hpowright := Real.rpow_le_rpow_of_nonpos
    (by positivity : (0 : ℝ) < (δ : ℝ) / 2)
    (show (δ : ℝ) / 2 ≤ (n : ℝ) - j.val - 1 from
      (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by linarith [hright]))
    (neg_nonpos.mpr s.property.1.le)
  rw [Real.div_rpow hδ.le (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul] at hpowright
  have hinv : (δ' : ℝ)⁻¹ ≤ 2 * (δ : ℝ)⁻¹ := by
    rw [inv_le_iff_one_le_mul₀ hδ']
    have h := mul_le_mul_of_nonneg_right hdepth (inv_nonneg.mpr hδ.le)
    rw [mul_inv_cancel₀ hδ.ne'] at h
    nlinarith only [h]
  have hprod := mul_le_mul hpowright hinv (inv_nonneg.mpr hδ'.le)
    (by positivity : 0 ≤ (δ : ℝ) ^ (-s.val) * 2 ^ s.val)
  have hprodleft := mul_le_mul_of_nonneg_right hpowleft (inv_nonneg.mpr hδ.le)
  have hid : (δ : ℝ) ^ (-s.val) * (δ : ℝ)⁻¹ = (δ : ℝ) ^ (-1 - s.val) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hδ]
    congr 1
    ring
  have htwo : (2 : ℝ) ^ s.val * 2 = (2 : ℝ) ^ (s.val + 1) := by
    calc
      _ = (2 : ℝ) ^ s.val * (2 : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := (Real.rpow_add (by norm_num) _ _).symm
  calc
    _ ≤ (δ : ℝ) ^ (-s.val) * (δ : ℝ)⁻¹ +
        ((δ : ℝ) ^ (-s.val) * 2 ^ s.val) * (2 * (δ : ℝ)⁻¹) :=
      add_le_add hprodleft hprod
    _ = _ := by rw [← hid, ← htwo]; ring

/-- The endpoint energy bound required by equation (5.28), on the literal
good event. This is the size-uniform expectation bound for the adjacent
crossing quadratic form. -/
theorem physical_adjacent_crossing_bound_internal (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ) (ε κ₀ : ℝ) (hε : 0 ≤ ε)
    (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (hx : x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀)
    (j : Fin ((n : ℕ) - 1)) :
    let a : Fin (n : ℕ) := ⟨j.val, by have := j.isLt; omega⟩
    let b : Fin (n : ℕ) := ⟨j.val + 1, by have := j.isLt; omega⟩
    let S := BoundaryEntries.physicalCrossing β s n m x
    S a a - S a b - S b a + S b b ≤
      (128 * (1 + (2 : ℝ) ^ (s.val + 1))) * (n : ℝ) ^ ((κ₀ + 6) * ε) *
        (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) ^ (-1 - s.val) := by
  dsimp only
  rw [physical_adjacent_crossing_identity_internal β s n m hn x j]
  have hp := BoundaryEntries.physical_prefix_bound β s ε κ₀ hε n m hn x hx j
  have hs := BoundaryEntries.physical_suffix_bound β s ε κ₀ hε n m hn x hx j
  have he := adjacent_endpoint_profiles_internal s n j
  have hE : 0 ≤ 128 * (n : ℝ) ^ ((κ₀ + 6) * ε) := by
    have hn0 : (0 : ℝ) ≤ n := by exact_mod_cast n.pos.le
    positivity
  have hb := mul_le_mul_of_nonneg_left he hE
  nlinarith only [hp, hs, hb]

/-- Physical incident-edge coefficients have exactly the prefix/suffix
expectation used in the proof of Lemma 5.8. The two pinned boundary
particles are excluded from the exterior vertex set. The antipodal case is
retained through the existing interval weights. -/
theorem conditional_incident_edges_internal (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (j : Fin ((n : ℕ) - 1)) :
    let p : Fin ((n : ℕ) + m + 1) := ⟨j.val + 1, by have := j.isLt; omega⟩
    (∑ r : Fin (((n : ℕ) + m + 1) / 2), ∑ a : Fin ((n : ℕ) + m + 1),
      let e := a + ((r.val + 1 : ℕ) : Fin ((n : ℕ) + m + 1))
      if (a = p ∧ (n : ℕ) < e.val) ∨ (e = p ∧ (n : ℕ) < a.val) then
        BoundaryEntries.conditionalIntervalWeight β s n m r a x else 0) =
      BoundaryEntries.physicalPrefix β s n m x j +
        BoundaryEntries.physicalSuffix β s n m x j := by
  classical
  intro p
  let N := ((n : ℕ) + m).succPNat
  unfold BoundaryEntries.physicalPrefix BoundaryEntries.physicalSuffix BoundaryEntries.physicalGroup
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  let e := a + ((r.val + 1 : ℕ) : Fin ((n : ℕ) + m + 1))
  have hr : 2 * (r.val + 1) ≤ (n : ℕ) + m + 1 := by have := r.isLt; omega
  have hj := j.isLt
  have hmod : e.val = if a.val + (r.val + 1) < (n : ℕ) + m + 1 then
      a.val + (r.val + 1) else a.val + (r.val + 1) - ((n : ℕ) + m + 1) := by
    simp only [e, Fin.val_add, Fin.val_natCast, Nat.add_mod_mod]
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by have := a.isLt; omega)]
  have hpref :
      (¬cyclicIndexInterval N a (r.val + 1) ⊆ BoundaryEntries.activeIndices N n ∧
        cyclicIndexInterval N a (r.val + 1) ∩ BoundaryEntries.activeIndices N n =
          BoundaryEntries.activeIndices N (j.val + 1)) ↔ e = p ∧ (n : ℕ) < a.val := by
    rw [BoundaryEntries.prefix_crossing_iff N hn (by omega) (by omega) hr]
    rw [Fin.ext_iff]
    change ((n : ℕ) ≤ a.val ∧ a.val + (r.val + 1) = (n : ℕ) + m + 1 + (j.val + 1)) ↔
      e.val = j.val + 1 ∧ (n : ℕ) < a.val
    rw [hmod]
    split_ifs <;> omega
  have htrace : ((BoundaryEntries.activeIndices N n).filter fun a => j.val < a.val) =
      (BoundaryEntries.activeIndices N n).filter (fun a => j.val + 1 ≤ a.val) := by
    apply Finset.filter_congr
    intro a _
    exact Nat.lt_iff_add_one_le
  have hsuff :
      (¬cyclicIndexInterval N a (r.val + 1) ⊆ BoundaryEntries.activeIndices N n ∧
        cyclicIndexInterval N a (r.val + 1) ∩ BoundaryEntries.activeIndices N n =
          (BoundaryEntries.activeIndices N n).filter (fun a => j.val < a.val)) ↔
      a = p ∧ (n : ℕ) < e.val := by
    rw [htrace, BoundaryEntries.suffix_crossing_iff N hn (by omega) (by omega) hr]
    rw [Fin.ext_iff]
    change (a.val = j.val + 1 ∧ (n : ℕ) < a.val + (r.val + 1)) ↔
      a.val = j.val + 1 ∧ (n : ℕ) < e.val
    rw [hmod]
    split_ifs <;> omega
  change (if (a = p ∧ (n : ℕ) < e.val) ∨ (e = p ∧ (n : ℕ) < a.val) then _ else _) = _
  erw [ite_congr (propext hpref) (fun _ => rfl) (fun _ => rfl),
    ite_congr (propext hsuff) (fun _ => rfl) (fun _ => rfl)]
  have hdis : ¬((a = p ∧ (n : ℕ) < e.val) ∧ (e = p ∧ (n : ℕ) < a.val)) := by
    rintro ⟨⟨ha, _⟩, _, hn'⟩
    rw [ha] at hn'
    dsimp [p] at hn'
    omega
  by_cases h₁ : a = p ∧ (n : ℕ) < e.val
  · have h₂ : ¬(e = p ∧ (n : ℕ) < a.val) := fun h₂ => hdis ⟨h₁, h₂⟩
    rw [ite_eq_left (Or.inl h₁), ite_eq_right h₂, ite_eq_left h₁, zero_add]
  · by_cases h₂ : e = p ∧ (n : ℕ) < a.val
    · rw [ite_eq_left (Or.inr h₂), ite_eq_left h₂, ite_eq_right h₁, add_zero]
    · rw [ite_eq_right (not_or.mpr ⟨h₁, h₂⟩), ite_eq_right h₂, ite_eq_right h₁, zero_add]

/-- The literal conditional incident-edge energy is integrable and its
expectation is exactly the adjacent crossing quadratic form in
the proof of Lemma 5.8. This is the finite-expectation identification
needed before applying the endpoint bound. -/
theorem physical_incident_edges_integral_internal (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (j : Fin ((n : ℕ) - 1)) :
    let N := ((n : ℕ) + m).succPNat
    let p : Fin ((n : ℕ) + m + 1) := ⟨j.val + 1, by have := j.isLt; omega⟩
    let B := fun z => ∑ r : Fin (((n : ℕ) + m + 1) / 2), ∑ a : Fin ((n : ℕ) + m + 1),
      let e := a + ((r.val + 1 : ℕ) : Fin ((n : ℕ) + m + 1))
      if (a = p ∧ (n : ℕ) < e.val) ∨ (e = p ∧ (n : ℕ) < a.val) then
        BoundaryEntries.intervalWeight s N r a
          (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) else 0
    let μ := ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x
    let a : Fin (n : ℕ) := ⟨j.val, by have := j.isLt; omega⟩
    let b : Fin (n : ℕ) := ⟨j.val + 1, by have := j.isLt; omega⟩
    let S := BoundaryEntries.physicalCrossing β s n m x
    Integrable B μ ∧ (∫ z, B z ∂μ) = S a a - S a b - S b a + S b b := by
  classical
  intro N p B μ a b S
  let c := fun (r : Fin (((n : ℕ) + m + 1) / 2)) (a : Fin ((n : ℕ) + m + 1)) =>
    let e := a + ((r.val + 1 : ℕ) : Fin ((n : ℕ) + m + 1))
    if (a = p ∧ (n : ℕ) < e.val) ∨ (e = p ∧ (n : ℕ) < a.val) then (1 : ℝ) else 0
  have hi := integral_interval_sum_internal β s n m x c
  have he : B = fun z => ∑ r, ∑ a,
      BoundaryEntries.intervalWeight s N r a
        (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) * c r a := by
    funext z
    simp only [B, c, mul_ite, mul_one, mul_zero]
    rfl
  refine ⟨he ▸ hi.1, ?_⟩
  rw [he, hi.2]
  simp only [c, mul_ite, mul_one, mul_zero]
  erw [conditional_incident_edges_internal β s n m hn x j]
  exact (physical_adjacent_crossing_identity_internal β s n m hn x j).symm

end Riesz2.ConditionalForces
