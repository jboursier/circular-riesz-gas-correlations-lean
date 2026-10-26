/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.ConditionalForcesPart5
public import Riesz1.ToMathlib.LipschitzExpectationL2

/-!
# Conditional force differences

Finite particle regrouping and variance estimates for the proof of Lemma 5.8.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology BigOperators Fin.NatCast

namespace Riesz2.ConditionalForces

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

private theorem reflect_lengths_internal {N : ℕ} (hN : 2 ≤ N) (A : Fin (N - 1) → ℝ)
    (hA : ∀ r, A ⟨N - 2 - r.val, by have := r.isLt; omega⟩ = A r) :
    (∑ r, A r) = ∑ r : Fin (N / 2),
      (2 - if 2 * (r.val + 1) = N then (1 : ℝ) else 0) *
        A ⟨r.val, by have := r.isLt; omega⟩ := by
  classical
  let s := Finset.univ.filter (fun r : Fin (N - 1) => r.val + 1 ≤ N / 2)
  let t := Finset.univ.filter (fun r : Fin (N - 1) => N / 2 < r.val + 1)
  have hsplit : Finset.univ = s ∪ t := by
    ext r
    simp only [s, t, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      le_or_gt]
  have hdisjoint : Disjoint s t := by
    apply Finset.disjoint_left.mpr
    intro r hr hs
    simp only [s, t, Finset.mem_filter, Finset.mem_univ, true_and] at hr hs
    omega
  have hreflect : (∑ r ∈ t, A r) =
      ∑ r ∈ s with 2 * (r.val + 1) ≠ N, A r := by
    apply Finset.sum_bij (fun r _ => (⟨N - 2 - r.val,
      by have := r.isLt; omega⟩ : Fin (N - 1)))
    · intro r hr
      have := r.isLt
      simp only [t, Finset.mem_filter, Finset.mem_univ, true_and] at hr
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · intro r hr q hq heq
      have := r.isLt
      have := q.isLt
      have := congrArg Fin.val heq
      apply Fin.ext
      dsimp at this
      omega
    · intro r hr
      have := r.isLt
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hr
      refine ⟨⟨N - 2 - r.val, by omega⟩, ?_, ?_⟩
      · simp only [t, Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      · apply Fin.ext
        dsimp
        omega
    · intro r _
      exact (hA r).symm
  rw [hsplit, Finset.sum_union hdisjoint, hreflect]
  have hterm (r : Fin (N - 1)) :
      (2 - if 2 * (r.val + 1) = N then (1 : ℝ) else 0) * A r =
        A r + if 2 * (r.val + 1) ≠ N then A r else 0 := by
    split_ifs <;> simp_all <;> ring
  have hweight : (∑ r ∈ s, A r) + (∑ r ∈ s with 2 * (r.val + 1) ≠ N, A r) =
      ∑ r ∈ s, (2 - if 2 * (r.val + 1) = N then (1 : ℝ) else 0) * A r := by
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_filter]
  rw [hweight]
  apply Finset.sum_bij (fun r hr => (⟨r.val, by
    have : r.val + 1 ≤ N / 2 := (Finset.mem_filter.mp hr).2
    omega⟩ : Fin (N / 2)))
  · intro r _
    exact Finset.mem_univ _
  · intro r _ q _ heq
    exact Fin.ext (congrArg (fun k : Fin (N / 2) => k.val) heq)
  · intro r _
    refine ⟨⟨r.val, by have := r.isLt; omega⟩, ?_, rfl⟩
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Nat.succ_le_of_lt r.isLt
  · intro r _
    rfl

/-- Internal finite regrouping for the proof of Lemma 5.8.
A symmetric pair form with zero diagonal is exactly its short-arc sum,
with the original antipodal multiplicity. -/
theorem short_pair_sum_internal (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (F : Fin (N : ℕ) → Fin (N : ℕ) → ℝ)
    (hF : ∀ i j, F i j = F j i) (hdiag : ∀ i, F i i = 0) :
    (∑ r : Fin ((N : ℕ) / 2), ∑ i : Fin (N : ℕ),
      (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
        F i (i + ((r.val + 1 : ℕ) : Fin (N : ℕ)))) = ∑ i, ∑ j, F i j := by
  have hrow (i : Fin (N : ℕ)) :
      (∑ j, F i j) = ∑ r : Fin ((N : ℕ) - 1), F i (i + ((r.val + 1 : ℕ) : Fin (N : ℕ))) := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hdiag, add_zero]
    symm
    apply Finset.sum_bij (fun r _ => i + ((r.val + 1 : ℕ) : Fin (N : ℕ)))
    · intro r _
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      intro he
      have hz : ((r.val + 1 : ℕ) : Fin (N : ℕ)) = 0 :=
        add_left_cancel (he.trans (add_zero i).symm)
      have := congrArg Fin.val hz
      rw [Fin.val_natCast, Nat.mod_eq_of_lt (by have := r.isLt; omega)] at this
      simp only [Fin.val_zero] at this
      omega
    · intro r _ q _ he
      have he := congrArg Fin.val (add_left_cancel he)
      change (r.val + 1) % (N : ℕ) = (q.val + 1) % (N : ℕ) at he
      rw [Nat.mod_eq_of_lt (by have := r.isLt; omega),
        Nat.mod_eq_of_lt (by have := q.isLt; omega)] at he
      exact Fin.ext (by omega)
    · intro j hj
      have hne := (Finset.mem_erase.mp hj).1
      let d := j - i
      have hd : d ≠ 0 := sub_ne_zero.mpr hne
      have hdv : 0 < d.val := Nat.pos_of_ne_zero (fun h => hd (Fin.ext h))
      refine ⟨⟨d.val - 1, by have := d.isLt; omega⟩, Finset.mem_univ _, ?_⟩
      rw [show d.val - 1 + 1 = d.val by omega,
        show ((d.val : ℕ) : Fin (N : ℕ)) = d from Fin.ext (Nat.mod_eq_of_lt d.isLt)]
      exact add_sub_cancel _ _
    · intro _ _
      rfl
  rw [show (∑ i, ∑ j, F i j) = ∑ r : Fin ((N : ℕ) - 1),
      ∑ i, F i (i + ((r.val + 1 : ℕ) : Fin (N : ℕ))) by
        simp_rw [hrow]; rw [Finset.sum_comm], reflect_lengths_internal hN]
  · simp only [Finset.mul_sum]
  · intro r
    let q : Fin ((N : ℕ) - 1) := ⟨(N : ℕ) - 2 - r.val, by have := r.isLt; omega⟩
    have hd : ((q.val + 1 : ℕ) : Fin (N : ℕ)) +
        ((r.val + 1 : ℕ) : Fin (N : ℕ)) = 0 := by
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_natCast, Nat.add_mod_mod, Nat.mod_add_mod]
      rw [show q.val + 1 + (r.val + 1) = (N : ℕ) by dsimp [q]; have := r.isLt; omega]
      exact Nat.mod_self _
    apply Finset.sum_bij (fun i _ => i + ((q.val + 1 : ℕ) : Fin (N : ℕ)))
    · intro _ _
      exact Finset.mem_univ _
    · intro i _ j _ he
      exact add_right_cancel he
    · intro i _
      refine ⟨i + ((r.val + 1 : ℕ) : Fin (N : ℕ)), Finset.mem_univ _, ?_⟩
      rw [add_assoc, add_comm ((r.val + 1 : ℕ) : Fin (N : ℕ)), hd, add_zero]
    · intro i _
      rw [hF]
      congr 1
      rw [add_assoc, hd, add_zero]

/-- Cumulative positions recover each actual cyclic separation in
the proof of Lemma 5.8, including an interval crossing the period. -/
theorem cumulative_cyclic_separation_internal (N : ℕ+) (y : Fin (N : ℕ) → ℝ)
    (hmass : ∑ a, y a = (N : ℝ)) (i : Fin (N : ℕ)) (r : ℕ)
    (hr : 0 < r) (hrN : r < (N : ℕ)) :
    let T := fun a : Fin (N : ℕ) => Fin.partialSum y a.castSucc
    let e := i + (r : Fin (N : ℕ))
    cyclicGapSum N i r y = T e - T i + if i.val < e.val then 0 else (N : ℝ) := by
  intro T e
  have he : e.val = if i.val + r < (N : ℕ) then i.val + r else i.val + r - (N : ℕ) := by
    simp only [e, Fin.val_add, Fin.val_natCast, Nat.add_mod_mod]
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by have := i.isLt; omega)]
  have hsub (a : Fin (N : ℕ)) :
      (a - i).val = if i.val ≤ a.val then a.val - i.val else (N : ℕ) + a.val - i.val := by
    rw [Fin.val_sub]
    split_ifs with h
    · rw [show (N : ℕ) - i.val + a.val = (N : ℕ) + (a.val - i.val) by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt (by have := a.isLt; omega)]
    · rw [Nat.mod_eq_of_lt (by have := a.isLt; have := i.isLt; omega)]
      omega
  rw [← sum_cyclicIndexInterval_eq_cyclicGapSum N i hrN.le,
    show T e = ∑ a : Fin (N : ℕ) with a.val < e.val, y a from
      Riesz1.partialSum_eq_sum_filter_real y e.castSucc,
    show T i = ∑ a : Fin (N : ℕ) with a.val < i.val, y a from
      Riesz1.partialSum_eq_sum_filter_real y i.castSucc]
  have hsum : (∑ j ∈ cyclicIndexInterval N i r, y j) =
      ∑ a : Fin (N : ℕ), if a ∈ cyclicIndexInterval N i r then y a else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext a
    simp
  rw [Finset.sum_filter, Finset.sum_filter, hsum]
  split_ifs at he with hi
  all_goals split_ifs with hwrap
  all_goals try (exfalso; omega)
  · rw [add_zero, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    simp only [mem_cyclicIndexInterval_iff N i a hrN.le, hsub]
    split_ifs <;> (first | omega | ring)
  · rw [← hmass, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    simp only [mem_cyclicIndexInterval_iff N i a hrN.le, hsub]
    split_ifs <;> (first | omega | ring)
/-- Reflection of a physical pair coefficient, used only off collisions
in the particle regrouping of the proof of Lemma 5.8. -/
theorem interval_coefficient_reflection_internal (p : Parameters) (N : ℕ+)
    (L : {L : ℝ // 0 < L ∧ L < (N : ℝ)}) :
    PhysicalEnergy.intervalCoefficient p N ⟨(N : ℝ) - L.val,
      sub_pos.mpr L.property.2, by linarith [L.property.1]⟩ =
      PhysicalEnergy.intervalCoefficient p N L := by
  rw [PhysicalEnergy.intervalCoefficient_images, PhysicalEnergy.intervalCoefficient_images]
  congr 1
  let e : ℤ ≃ ℤ := (Equiv.neg ℤ).trans (Equiv.addRight (-1))
  have h := e.tsum_eq (fun k : ℤ => |L.val + k * (N : ℝ)| ^ (-p.val.2 - 2))
  rw [← h]
  apply tsum_congr
  intro k
  have he : (e k : ℝ) = -(k : ℝ) - 1 := by simp [e]; ring
  rw [he]
  congr 1
  rw [show L.val + (-(k : ℝ) - 1) * (N : ℝ) =
    -((N : ℝ) - L.val + k * (N : ℝ)) by ring, abs_neg]

/-- Physical interval weights expressed in the actual cumulative particle
positions, with the antipodal factor retained (the proof of Lemma 5.8). -/
theorem interval_weight_positions_internal (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (N : ℕ+)
    (y : EuclideanSpace ℝ (Fin (N : ℕ)))
    (hy : WithLp.ofLp y ∈ Riesz1.gapSimplex N)
    (r : Fin ((N : ℕ) / 2)) (i : Fin (N : ℕ)) :
    let T := fun a : Fin (N : ℕ) => Fin.partialSum (WithLp.ofLp y) a.castSucc
    let e := i + ((r.val + 1 : ℕ) : Fin (N : ℕ))
    BoundaryEntries.intervalWeight s N r i y =
      (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
        (s.val * (s.val + 1) *
          ∑' k : ℤ, |T e - T i + k * (N : ℝ)| ^ (-s.val - 2)) := by
  intro T e
  rw [BoundaryEntries.intervalWeight_physical β s N r i y hy,
    PhysicalEnergy.intervalCoefficient_images]
  congr 2
  have hsep := cumulative_cyclic_separation_internal N (WithLp.ofLp y) hy.2 i
    (r.val + 1) (by omega)
    (lt_of_le_of_lt (Nat.succ_le_of_lt r.isLt) (Nat.div_lt_self N.pos (by norm_num)))
  change cyclicGapSum N i (r.val + 1) (WithLp.ofLp y) =
    T e - T i + if i.val < e.val then 0 else (N : ℝ) at hsep
  simp only [ofLong]
  rw [hsep]
  split_ifs
  · simp only [add_zero]
  · let shift : ℤ ≃ ℤ := Equiv.addRight 1
    have he := shift.tsum_eq (fun k : ℤ => |T e - T i + k * (N : ℝ)| ^ (-s.val - 2))
    rw [← he]
    apply tsum_congr
    intro k
    congr 2
    simp only [shift, Equiv.coe_addRight, Int.cast_add, Int.cast_one]
    ring

/-- Exact regrouping of the physical Hessian as the full ordered particle
pair sum (the proof of Lemma 5.8). Self-pairs vanish because their
displacement difference is zero. -/
theorem physical_hessian_positions_internal (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (U : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ)
    (hU : ∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
      U y.val = β.val * physicalAmbientGapEnergy (ofLong β s) N y)
    (y : EuclideanSpace ℝ (Fin (N : ℕ)))
    (hy : WithLp.ofLp y ∈ Riesz1.gapSimplex N) (H K : Fin (N : ℕ) → ℝ) :
    let T := fun a : Fin (N : ℕ) => Fin.partialSum (WithLp.ofLp y) a.castSucc
    fderiv ℝ (fderiv ℝ U) y
        (WithLp.toLp 2 (fun a => H (a + 1) - H a))
        (WithLp.toLp 2 (fun a => K (a + 1) - K a)) =
      β.val * ∑ i, ∑ a,
        (s.val * (s.val + 1) * ∑' k : ℤ,
          |T a - T i + k * (N : ℝ)| ^ (-s.val - 2)) *
            ((H a - H i) * (K a - K i)) := by
  intro T
  rw [physical_hessian_particle_displacements_internal β s N U hU y hy H K]
  simp_rw [interval_weight_positions_internal β s N y hy]
  have hsym (i a : Fin (N : ℕ)) :
      (∑' k : ℤ, |T a - T i + k * (N : ℝ)| ^ (-s.val - 2)) =
        ∑' k : ℤ, |T i - T a + k * (N : ℝ)| ^ (-s.val - 2) := by
    rw [← (Equiv.neg ℤ).tsum_eq (fun k : ℤ =>
      |T i - T a + k * (N : ℝ)| ^ (-s.val - 2))]
    apply tsum_congr
    intro k
    simp only [Equiv.neg_apply, Int.cast_neg]
    rw [show T i - T a + -(k : ℝ) * (N : ℝ) =
      -(T a - T i + k * (N : ℝ)) by ring, abs_neg]
  let F := fun i a : Fin (N : ℕ) =>
    (s.val * (s.val + 1) * ∑' k : ℤ, |T a - T i + k * (N : ℝ)| ^ (-s.val - 2)) *
      ((H a - H i) * (K a - K i))
  have hs : ∀ i a, F i a = F a i := by
    intro i a
    dsimp only [F]
    rw [hsym i a]
    ring
  have hd : ∀ i, F i i = 0 := by intro i; simp [F]
  have he := short_pair_sum_internal N hN F hs hd
  rw [← he]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [F, T]
  ring

/-- Finite regrouping of the pinned/exterior graph in
the proof of Lemma 5.8. Each undirected edge is counted twice in
the full ordered pair sum. -/
theorem pinned_pair_sum_internal {ι : Type*} [Fintype ι]
    (C : ι → ι → ℝ) (hC : ∀ i a, C i a = C a i)
    (P : ι → Prop) [DecidablePred P] (f : ι → ℝ) :
    (∑ i, ∑ a, C i a *
      (if P i ∧ ¬P a then f a else if ¬P i ∧ P a then f i else 0)) =
      2 * ∑ a, if ¬P a then (∑ i, if P i then C i a else 0) * f a else 0 := by
  classical
  have ht (i a : ι) : C i a *
      (if P i ∧ ¬P a then f a else if ¬P i ∧ P a then f i else 0) =
      (if P i ∧ ¬P a then C i a * f a else 0) +
        (if P a ∧ ¬P i then C a i * f i else 0) := by
    rw [hC a i]
    by_cases hi : P i <;> by_cases ha : P a <;> simp [hi, ha]
  simp_rw [ht, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i a => if P a ∧ ¬P i then C a i * f i else 0)]
  have he : (∑ i, ∑ a, if P i ∧ ¬P a then C i a * f a else 0) =
      ∑ a, if ¬P a then (∑ i, if P i then C i a else 0) * f a else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : P a
    · simp [ha]
    · simp only [ha, not_false_eq_true, and_true, ↓reduceIte, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp
  rw [he]
  ring

/-- Deleting the exterior interaction graph is legitimate before applying
BL (the proof of Lemma 5.8). This is the ordered-pair version of
Part 5's interval lower bound. -/
theorem pinned_pair_lower_internal {ι : Type*} [Fintype ι]
    (C : ι → ι → ℝ) (hC : ∀ i a, C i a = C a i)
    (hpos : ∀ i a, 0 ≤ C i a) (P : ι → Prop) [DecidablePred P]
    (H : ι → ℝ) (hH : ∀ i, P i → H i = 0) :
    (2 * ∑ a, if ¬P a then (∑ i, if P i then C i a else 0) * (H a) ^ 2 else 0) ≤
      ∑ i, ∑ a, C i a * ((H a - H i) * (H a - H i)) := by
  rw [← pinned_pair_sum_internal C hC P (fun a => H a ^ 2)]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_left _ (hpos i a)
  split_ifs with hi ha
  · rw [hH i hi.1, sub_zero, pow_two]
  · rw [hH a ha.2, zero_sub, neg_mul_neg, pow_two]
  · exact (sq_nonneg (H a - H i)).trans_eq (pow_two _)

/-- The exact mixed pinned-particle graph identity in
the proof of Lemma 5.8. Moving one pinned particle produces minus
twice its coupling to each exterior displacement. -/
theorem moved_particle_pair_internal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ι → ι → ℝ) (hC : ∀ i a, C i a = C a i)
    (H : ι → ℝ) (p : ι) (hp : H p = 0) :
    (∑ i, ∑ a, C i a *
      (((if a = p then (1 : ℝ) else 0) - (if i = p then (1 : ℝ) else 0)) *
        (H a - H i))) = -2 * ∑ a, C p a * H a := by
  have ht (i a : ι) : C i a *
      (((if a = p then (1 : ℝ) else 0) - (if i = p then (1 : ℝ) else 0)) *
        (H a - H i)) =
      -(if i = p then C p a * H a else 0) -
        (if a = p then C p i * H i else 0) := by
    by_cases hi : i = p <;> by_cases ha : a = p
    all_goals simp [hi, ha, hp, hC i p]
  simp_rw [ht, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [Finset.sum_comm (f := fun i a => if i = p then C p a * H a else 0)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  ring

/-- The actual cumulative positions are strictly ordered inside one
period (the proof of Lemma 5.8). -/
theorem cumulative_positions_bounds_internal (N : ℕ+)
    (y : Fin (N : ℕ) → ℝ) (hy : y ∈ Riesz1.gapSimplex N) :
    let T := fun a : Fin (N : ℕ) => Fin.partialSum y a.castSucc
    (∀ a, 0 ≤ T a ∧ T a < (N : ℝ)) ∧
      ∀ i a, i < a → 0 < T a - T i ∧ T a - T i < (N : ℝ) := by
  intro T
  have hT (a) : T a = ∑ b : Fin (N : ℕ) with b.val < a.val, y b :=
    Riesz1.partialSum_eq_sum_filter_real y a.castSucc
  have hb (a) : 0 ≤ T a ∧ T a < (N : ℝ) := by
    rw [hT]
    constructor
    · exact Finset.sum_nonneg (fun b _ => (hy.1 b).le)
    · rw [← hy.2]
      apply Finset.sum_lt_sum_of_subset (Finset.subset_univ _)
        (Finset.mem_univ a) (by simp) (hy.1 a) (fun b _ _ => (hy.1 b).le)
  refine ⟨hb, fun i a hia => ?_⟩
  constructor
  · rw [show T a - T i = ∑ b ∈ Finset.Ico i a, y b from
      Riesz1.partialSum_sub_eq_sum_Ico y i a hia.le]
    exact Finset.sum_pos (fun b _ => hy.1 b)
      ⟨i, Finset.mem_Ico.mpr ⟨le_rfl, hia⟩⟩
  · linarith [(hb a).2, (hb i).1]

/-- The cumulative pinned positions in the physical chart are precisely
the retained-gap sums used by Part 5 (the proof of Lemma 5.8). -/
theorem cumulative_retained_positions_internal (n : ℕ+) (m : ℕ)
    (x : EuclideanSpace ℝ (Fin (n : ℕ))) (z : EuclideanSpace ℝ (Fin m))
    (r : Fin ((n : ℕ) + 1)) :
    Fin.partialSum
      (WithLp.ofLp (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x,z)))
      (⟨r.val, by have := r.isLt; omega⟩ : Fin ((n : ℕ) + m + 1)).castSucc =
        ∑ i : Fin (n : ℕ) with i.val < r.val, x i := by
  rw [Riesz1.partialSum_eq_sum_filter_real]
  symm
  apply Finset.sum_bij (fun i _ => (i.castAdd m).castSucc)
  · intro i hi
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc,
      Fin.val_castAdd] using hi
  · intro i _ j _ he
    apply Fin.ext
    exact congrArg (fun a : Fin ((n : ℕ) + m + 1) => a.val) he
  · intro a ha
    have ha : a.val < r.val := (Finset.mem_filter.mp ha).2
    let i : Fin (n : ℕ) := ⟨a.val, by have := r.isLt; omega⟩
    refine ⟨i, ?_, Fin.ext rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
  · intro i _
    exact (RetainedSimplex.chart_retained n m _ (Equiv.refl _) x z i).symm

/-- Internal square completion on the pinned graph for
the proof of Lemma 5.8. The diagonal comparison supplies the
additional boundary-depth factor. -/
theorem pinned_pair_variational_internal {ι : Type*} [Fintype ι]
    (C : ι → ι → ℝ) (hC : ∀ i a, C i a = C a i)
    (hpos : ∀ i a, 0 ≤ C i a) (P : ι → Prop) [DecidablePred P]
    (H : ι → ℝ) (hH : ∀ i, P i → H i = 0)
    (p : ι) (β ρ : ℝ) (hβ : 0 < β) (hρ : 0 < ρ)
    (hcomp : ∀ a, ¬P a → ρ * C p a ≤ ∑ i, if P i then C i a else 0) :
    -4 * (∑ a, C p a * H a) -
        β * (∑ i, ∑ a, C i a * ((H a - H i) * (H a - H i))) ≤
      β⁻¹ * ρ⁻¹ * (2 * ∑ a, if ¬P a then C p a else 0) := by
  classical
  have hlow := pinned_pair_lower_internal C hC hpos P H hH
  have hβρ : 0 < β * ρ := mul_pos hβ hρ
  have hterm (a : ι) :
      -4 * (C p a * H a) -
          β * (2 * (if ¬P a then (∑ i, if P i then C i a else 0) * H a ^ 2 else 0)) ≤
        β⁻¹ * ρ⁻¹ * (2 * (if ¬P a then C p a else 0)) := by
    by_cases ha : P a
    · simp [ha, hH a ha]
    · simp only [ha, not_false_eq_true, ↓reduceIte]
      have hc := mul_le_mul_of_nonneg_right (hcomp a ha) (sq_nonneg (H a))
      have hscalar : -2 * H a - (β * ρ) * H a ^ 2 ≤ (β * ρ)⁻¹ := by
        apply (mul_le_mul_iff_right₀ hβρ).mp
        have hinv := mul_inv_cancel₀ hβρ.ne'
        nlinarith only [sq_nonneg (β * ρ * H a + 1), hinv]
      have hh := mul_le_mul_of_nonneg_left hscalar (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hpos p a))
      rw [mul_inv_rev] at hh
      have hcc := mul_le_mul_of_nonneg_left hc hβ.le
      nlinarith only [hh, hcc]
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset ι)) => hterm a)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  have hm := mul_le_mul_of_nonneg_left hlow hβ.le
  linarith only [hs, hm]

/-- Exact incident-edge regrouping in the proof of Lemma 5.8.
The interval sum has twice the full position coupling to each exterior
particle, including the two antipodal orientations. -/
theorem incident_pair_sum_internal (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (C : Fin (N : ℕ) → Fin (N : ℕ) → ℝ)
    (hC : ∀ i a, C i a = C a i)
    (P : Fin (N : ℕ) → Prop) [DecidablePred P] (p : Fin (N : ℕ)) (hp : P p) :
    (∑ r : Fin ((N : ℕ) / 2), ∑ i : Fin (N : ℕ),
      let a := i + ((r.val + 1 : ℕ) : Fin (N : ℕ))
      if (i = p ∧ ¬P a) ∨ (a = p ∧ ¬P i) then
        (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) * C i a else 0) =
      2 * ∑ a, if ¬P a then C p a else 0 := by
  classical
  let F := fun i a => if (i = p ∧ ¬P a) ∨ (a = p ∧ ¬P i) then C i a else 0
  have hs : ∀ i a, F i a = F a i := by
    intro i a
    dsimp only [F]
    simp only [or_comm, hC i a]
  have hd : ∀ i, F i i = 0 := by
    intro i
    by_cases hi : i = p
    · subst i
      simp [F, hp]
    · simp [F, hi]
  have he := short_pair_sum_internal N hN F hs hd
  have ht (i a : Fin (N : ℕ)) : F i a =
      (if i = p then (if ¬P a then C p a else 0) else 0) +
        (if a = p then (if ¬P i then C p i else 0) else 0) := by
    by_cases hi : i = p <;> by_cases ha : a = p
    all_goals simp [F, hi, ha, hp, hC i p]
  have heF : (∑ i, ∑ a, F i a) = 2 * ∑ a, if ¬P a then C p a else 0 := by
    simp_rw [ht, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i a =>
      if i = p then (if ¬P a then C p a else 0) else 0)]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    ring
  rw [← heF, ← he]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  simp only [F, mul_ite, mul_zero]

/-- Part 5's pinned diagonal estimate on the literal full particle
positions of the physical chart (the proof of Lemma 5.8). -/
theorem good_position_diagonal_internal (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ) (ε κ₀ : ℝ) (hε : 0 ≤ ε)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (hx : x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀)
    (z : EuclideanSpace ℝ (Fin m))
    (hy : WithLp.ofLp (RetainedSimplex.chart n m ((n + m : ℕ) + 1)
      (Equiv.refl _) (x.val,z)) ∈ Riesz1.gapSimplex ((n : ℕ) + m).succPNat)
    (j : Fin ((n : ℕ) - 1)) (a : Fin ((n : ℕ) + m + 1)) (ha : (n : ℕ) < a.val) :
    let N := ((n : ℕ) + m).succPNat
    let y := RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)
    let T := fun b : Fin (N : ℕ) => Fin.partialSum (WithLp.ofLp y) b.castSucc
    let C := fun i b => s.val * (s.val + 1) *
      ∑' k : ℤ, |T b - T i + k * (N : ℝ)| ^ (-s.val - 2)
    let p : Fin (N : ℕ) := ⟨j.val + 1, by have := j.isLt; simp only [N, Nat.succPNat_coe]; omega⟩
    (2 : ℝ) ^ (-s.val - 3) * (n : ℝ) ^ (-(2 * (s.val + 2)) * ε) *
        (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) * C p a ≤
      ∑ i, if i.val ≤ (n : ℕ) then C i a else 0 := by
  intro N y T C p
  let t := fun r : Fin ((n : ℕ) + 1) => ∑ i : Fin (n : ℕ) with i.val < r.val, x.val i
  have hT (r : Fin ((n : ℕ) + 1)) :
      T ⟨r.val, by dsimp [N]; have := r.isLt; omega⟩ = t r :=
    cumulative_retained_positions_internal n m x.val z r
  have hb := cumulative_positions_bounds_internal N (WithLp.ofLp y) hy
  let last : Fin (N : ℕ) := ⟨n, by dsimp [N]; omega⟩
  have hlast : T last = ∑ i, x.val i := by
    calc
      T last = t (Fin.last (n : ℕ)) := hT (Fin.last (n : ℕ))
      _ = _ := by simp [t]
  change (∀ a, 0 ≤ T a ∧ T a < (N : ℝ)) ∧
    (∀ i a, i < a → 0 < T a - T i ∧ T a - T i < (N : ℝ)) at hb
  have hNcast : (N : ℝ) = (n : ℝ) + m + 1 := by
    simp [N, Nat.cast_add, Nat.cast_succ]
  have hZ : (∑ i, x.val i) < T a ∧ T a < ((n : ℝ) + m + 1) := by
    constructor
    · have h := (hb.2 last a (by exact ha)).1
      change 0 < T a - T last at h
      rw [hlast] at h
      linarith only [h]
    · exact (hb.1 a).2.trans_eq hNcast
  obtain ⟨hsep, hdiag⟩ := good_pinned_diagonal_internal β s n m ε κ₀ hε x hx j (T a) hZ
  have he (r : Fin ((n : ℕ) + 1)) :
      PhysicalEnergy.intervalCoefficient (ofLong β s) N ⟨T a - t r, hsep r⟩ =
        C ⟨r.val, by dsimp [N]; have := r.isLt; omega⟩ a := by
    rw [PhysicalEnergy.intervalCoefficient_images]
    dsimp only [C]
    rw [hT r]
    rfl
  have hdiag' := hdiag
  change (2 : ℝ) ^ (-s.val - 3) * (n : ℝ) ^ (-(2 * (s.val + 2)) * ε) *
      (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) *
      (2 * PhysicalEnergy.intervalCoefficient (ofLong β s) N
        ⟨T a - t ⟨j.val + 1, by have := j.isLt; omega⟩, hsep _⟩) ≤
      ∑ r, 2 * PhysicalEnergy.intervalCoefficient (ofLong β s) N ⟨T a - t r, hsep r⟩ at hdiag'
  simp_rw [he] at hdiag'
  have hsum : (∑ r : Fin ((n : ℕ) + 1), C ⟨r.val, by dsimp [N]; have := r.isLt; omega⟩ a) =
      ∑ i, if i.val ≤ (n : ℕ) then C i a else 0 := by
    rw [← Finset.sum_filter]
    apply Finset.sum_bij (fun r _ => (⟨r.val, by dsimp [N]; have := r.isLt; omega⟩ : Fin (N : ℕ)))
    · intro r _
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, show r.val ≤ (n : ℕ) by have := r.isLt; omega⟩
    · intro r _ q _ he
      apply Fin.ext
      exact congrArg (fun i : Fin (N : ℕ) => i.val) he
    · intro i hi
      exact ⟨⟨i.val, by have := (Finset.mem_filter.mp hi).2; omega⟩,
        Finset.mem_univ _, Fin.ext rfl⟩
    · intro _ _
      rfl
  rw [← Finset.mul_sum, hsum] at hdiag'
  change _ * (2 * C p a) ≤ 2 * _ at hdiag'
  nlinarith only [hdiag']

/-- Physical adjacent-force square completion on the original exterior
chart (the proof of Lemma 5.8). -/
theorem physical_adjacent_variational_internal (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ) (ε κ₀ : ℝ) (hε : 0 ≤ ε)
    (U : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ)
    (hU : ∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) //
        y ∈ gapAmbientDomain ((n : ℕ) + m).succPNat},
      U y.val = β.val * physicalAmbientGapEnergy (ofLong β s) ((n : ℕ) + m).succPNat y)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (hx : x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀)
    (z : EuclideanSpace ℝ (Fin m))
    (hy : WithLp.ofLp (RetainedSimplex.chart n m ((n + m : ℕ) + 1)
      (Equiv.refl _) (x.val,z)) ∈ Riesz1.gapSimplex ((n : ℕ) + m).succPNat)
    (j : Fin ((n : ℕ) - 1))
    (h : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)))
    (hsum : ∑ a, h a = 0)
    (hactive : ∀ a : Fin (n : ℕ), h (a.castAdd m).castSucc = 0) :
    let N := ((n : ℕ) + m).succPNat
    let y := RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)
    let p : Fin (N : ℕ) := ⟨j.val + 1, by have := j.isLt; simp only [N, Nat.succPNat_coe]; omega⟩
    let i : Fin (N : ℕ) := ⟨j.val, by have := j.isLt; simp only [N, Nat.succPNat_coe]; omega⟩
    let ρ := (2 : ℝ) ^ (-s.val - 3) * (n : ℝ) ^ (-(2 * (s.val + 2)) * ε) *
      (min (j.val + 1) ((n : ℕ) - j.val) : ℕ)
    let B := ∑ r : Fin (((n : ℕ) + m + 1) / 2), ∑ a : Fin ((n : ℕ) + m + 1),
      let e := a + ((r.val + 1 : ℕ) : Fin ((n : ℕ) + m + 1))
      if (a = p ∧ (n : ℕ) < e.val) ∨ (e = p ∧ (n : ℕ) < a.val) then
        BoundaryEntries.intervalWeight s N r a y else 0
    2 * β.val⁻¹ * fderiv ℝ (fderiv ℝ U) y
        (EuclideanSpace.single i 1 - EuclideanSpace.single p 1) h -
        fderiv ℝ (fderiv ℝ U) y h h ≤ β.val⁻¹ * ρ⁻¹ * B := by
  classical
  intro N y p i ρ B
  let T := fun a : Fin (N : ℕ) => Fin.partialSum (WithLp.ofLp y) a.castSucc
  let C := fun i a : Fin (N : ℕ) => s.val * (s.val + 1) *
    ∑' k : ℤ, |T a - T i + k * (N : ℝ)| ^ (-s.val - 2)
  have hC (i a) : C i a = C a i := by
    dsimp only [C]
    congr 1
    rw [← (Equiv.neg ℤ).tsum_eq (fun k : ℤ =>
      |T i - T a + k * (N : ℝ)| ^ (-s.val - 2))]
    apply tsum_congr
    intro k
    simp only [Equiv.neg_apply, Int.cast_neg]
    rw [show T i - T a + -(k : ℝ) * (N : ℝ) =
      -(T a - T i + k * (N : ℝ)) by ring, abs_neg]
  have hpos (i a) : 0 ≤ C i a :=
    mul_nonneg (mul_nonneg s.property.1.le (by linarith [s.property.1]))
      (tsum_nonneg (fun _ => Real.rpow_nonneg (abs_nonneg _) _))
  let H := fun a : Fin (N : ℕ) => Fin.partialSum (WithLp.ofLp h) a.castSucc
  obtain ⟨hH, heH⟩ := exterior_particle_primitive_internal n m h hsum hactive
  change (∀ a, a.val ≤ (n : ℕ) → H a = 0) at hH
  change h = WithLp.toLp 2 (fun a : Fin (N : ℕ) => H (a + 1) - H a) at heH
  let P := fun a : Fin (N : ℕ) => if a = p then (1 : ℝ) else 0
  have hNp : 2 ≤ (N : ℕ) := by dsimp [N]; have := n.pos; omega
  have hp : H p = 0 := hH p (by dsimp [p]; have := j.isLt; omega)
  have hm := physical_hessian_positions_internal β s N hNp U hU y hy P H
  change fderiv ℝ (fderiv ℝ U) y
    (WithLp.toLp 2 (fun a : Fin (N : ℕ) => P (a + 1) - P a))
    (WithLp.toLp 2 (fun a : Fin (N : ℕ) => H (a + 1) - H a)) =
      β.val * ∑ b, ∑ a, C b a * ((P a - P b) * (H a - H b)) at hm
  rw [show WithLp.toLp 2 (fun a : Fin (N : ℕ) => P (a + 1) - P a) =
      EuclideanSpace.single i 1 - EuclideanSpace.single p 1 from
        adjacent_particle_displacement_internal n m j, ← heH] at hm
  have hmove := moved_particle_pair_internal C hC H p hp
  change (∑ b, ∑ a, C b a * ((P a - P b) * (H a - H b))) = _ at hmove
  rw [hmove] at hm
  have hq := physical_hessian_positions_internal β s N hNp U hU y hy H H
  change fderiv ℝ (fderiv ℝ U) y
    (WithLp.toLp 2 (fun a : Fin (N : ℕ) => H (a + 1) - H a))
    (WithLp.toLp 2 (fun a : Fin (N : ℕ) => H (a + 1) - H a)) =
      β.val * ∑ b, ∑ a, C b a * ((H a - H b) * (H a - H b)) at hq
  rw [← heH] at hq
  have hρ : 0 < ρ := by
    dsimp only [ρ]
    have hd : (0 : ℝ) < (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) := by
      exact_mod_cast (show 0 < min (j.val + 1) ((n : ℕ) - j.val) by have := j.isLt; omega)
    have hn : (0 : ℝ) < n := by exact_mod_cast n.pos
    positivity
  have hcomp (a : Fin (N : ℕ)) (ha : ¬a.val ≤ (n : ℕ)) :
      ρ * C p a ≤ ∑ b, if b.val ≤ (n : ℕ) then C b a else 0 :=
    good_position_diagonal_internal β s n m ε κ₀ hε x hx z hy j a (Nat.lt_of_not_ge ha)
  have hv := pinned_pair_variational_internal C hC hpos (fun a => a.val ≤ (n : ℕ))
    H hH p β.val ρ β.property hρ hcomp
  have hB : B = 2 * ∑ a, if ¬a.val ≤ (n : ℕ) then C p a else 0 := by
    have he := incident_pair_sum_internal N hNp C hC (fun a => a.val ≤ (n : ℕ)) p
      (by dsimp [p]; have := j.isLt; omega)
    rw [← he]
    dsimp only [B]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro a _
    simp only [not_le]
    rw [interval_weight_positions_internal β s N y hy r a]
  rw [hm, hq, hB]
  have hβ := mul_inv_cancel₀ β.property.ne'
  have he : 2 * β.val⁻¹ * (β.val * (-2 * ∑ a, C p a * H a)) =
      -4 * ∑ a, C p a * H a := by
    field_simp [β.property.ne']
    ring
  rw [he]
  exact hv

/-- The physical adjacent Brascamp–Lieb application for the proof of Lemma 5.8.
This internal assembly takes the H¹ certificate separately. The theorem below supplies it from Part 3. -/
theorem physical_adjacent_variance_internal (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ) (ε κ₀ : ℝ) (hε : 0 ≤ ε)
    (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (U : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ)
    (hUs : ContDiffOn ℝ ∞ U (gapAmbientDomain ((n : ℕ) + m).succPNat))
    (hUv : ∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) //
        y ∈ gapAmbientDomain ((n : ℕ) + m).succPNat},
      U y.val = β.val * physicalAmbientGapEnergy (ofLong β s) ((n : ℕ) + m).succPNat y)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (hx : x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀) (j : Fin ((n : ℕ) - 1))
    (hF : let i : Fin ((n : ℕ) + m + 1) := ⟨j.val, by have := j.isLt; omega⟩
      let p : Fin ((n : ℕ) + m + 1) := ⟨j.val + 1, by have := j.isLt; omega⟩
      let d := EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single p 1
      let F := fun z => β.val⁻¹ * fderiv ℝ U
        (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) d
      Riesz1.WeightedSobolev.IsWeightedH1
        (ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x)
        (AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ a, x.val a)) F (gradient F)) :
    let i : Fin ((n : ℕ) + m + 1) := ⟨j.val, by have := j.isLt; omega⟩
    let p : Fin ((n : ℕ) + m + 1) := ⟨j.val + 1, by have := j.isLt; omega⟩
    let d := EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single p 1
    let F := fun z => β.val⁻¹ * fderiv ℝ U
      (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) d
    let μ := ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x
    let a : Fin (n : ℕ) := ⟨j.val, by have := j.isLt; omega⟩
    let b : Fin (n : ℕ) := ⟨j.val + 1, by have := j.isLt; omega⟩
    let S := BoundaryEntries.physicalCrossing β s n m x
    let ρ := (2 : ℝ) ^ (-s.val - 3) * (n : ℝ) ^ (-(2 * (s.val + 2)) * ε) *
      (min (j.val + 1) ((n : ℕ) - j.val) : ℕ)
    (∫ z, (F z - ∫ y, F y ∂μ) ^ 2 ∂μ) ≤
      β.val⁻¹ * ρ⁻¹ * (S a a - S a b - S b a + S b b) := by
  classical
  intro i p d F μ a b S ρ
  have hm : 1 ≤ m := by have := j.isLt; have := n.pos; omega
  let N := ((n : ℕ) + m).succPNat
  let Q := AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ a, x.val a)
  let c := fun z => RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)
  let V := fun z => U (c z)
  have hQ : IsOpen Q := AffineSimplex.isOpen_chartDomain _ _
  have hs (z) (hz : z ∈ Q) : WithLp.ofLp (c z) ∈ Riesz1.gapSimplex N := by
    have hd := (Set.ext_iff.mp (RetainedSimplex.fibre_domain n m _ x.property) z).mpr hz
    have hy := (RetainedSimplex.chart_mem_simplex n m _ (Equiv.refl _) _).mpr hd
    exact ⟨hy.1, by simpa only [N, c, Nat.succPNat_coe, Nat.cast_succ] using hy.2⟩
  have hA (z) (hz : z ∈ Q) : c z ∈ gapAmbientDomain N :=
    PhysicalEnergy.simplex_subset_ambient N _ (hs z hz)
  obtain ⟨A, hc, hactive, hnorm⟩ := exterior_chart_affine_internal n m ((n + m : ℕ) + 1) x.val
  have hce : c = fun z => A z + c 0 := funext hc
  have hcmass (z) : ∑ a, c z a = ((n + m : ℕ) + 1) := by
    have he (v : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1))) :
        LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.refl _) v = v := by ext k; rfl
    simp only [c, RetainedSimplex.chart, he, AffineSimplex.sum_chart]
  have hsumA (h) : ∑ a, A h a = 0 := by
    have he := congrArg (fun v : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) => ∑ a, v a) (hc h)
    change (∑ a, c h a) = ∑ a, (A h + c 0) a at he
    simp only [PiLp.add_apply, Finset.sum_add_distrib, hcmass] at he
    linarith only [he]
  have hUat (z) (hz : z ∈ Q) : ContDiffAt ℝ 2 U (A z + c 0) := by
    rw [← hc]
    exact (hUs.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds
      (hA z hz))).of_le (by norm_num)
  have hV : ContDiffOn ℝ 2 V Q := by
    apply (hUs.of_le (by norm_num)).comp _ hA
    rw [hce]
    exact (A.contDiff.add contDiff_const).contDiffOn
  have hH (z) (hz : z ∈ Q) (h) : fderiv ℝ (fderiv ℝ V) z h h =
      fderiv ℝ (fderiv ℝ U) (c z) (A h) (A h) := by
    dsimp only [V]
    rw [hce]
    exact AffineMetricTransport.hessian_comp_affine A (c 0) (hUat z hz) h h
  let κ := β.val * (s.val * (s.val + 1)) * (N : ℝ) ^ (-s.val - 2)
  have hκ : 0 < κ := by
    have hβ := β.property
    have hsp := s.property.1
    have hNp : (0 : ℝ) < N := by exact_mod_cast N.pos
    dsimp only [κ]
    positivity
  have hlow (z) (hz : z ∈ Q) (h) : κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) z h h := by
    rw [hH z hz]
    exact (mul_le_mul_of_nonneg_left (hnorm h) hκ.le).trans
      (physical_hessian_lower_internal β s N (by dsimp [N]; have := n.pos; omega)
        U hUv (c z) (hs z hz) (A h))
  have hne : Q.Nonempty := by
    have hximage : x.val ∈ Prod.fst '' RetainedSimplex.domain n m ((n + m : ℕ) + 1) := by
      rw [RetainedSimplex.fst_image_domain]
      exact x.property
    obtain ⟨⟨a,z⟩, hz, he⟩ := hximage
    change a = x.val at he
    subst a
    exact ⟨z, (Set.ext_iff.mp (RetainedSimplex.fibre_domain n m _ x.property) z).mp hz⟩
  have hμ := physical_conditional_density_internal (ofLong β s) n m n.pos U hUv x
  have hBL := euclidean_brascamp_lieb hm (AffineSimplex.isBounded_chartDomain m _) hQ hne
    (AffineSimplex.convex_chartDomain m _) hV hκ hlow μ hμ
  obtain ⟨hvar, hint, _⟩ := hBL.2.2.2.1 F (gradient F) hF
  let B := fun z => ∑ r : Fin (((n : ℕ) + m + 1) / 2), ∑ a : Fin ((n : ℕ) + m + 1),
    let e := a + ((r.val + 1 : ℕ) : Fin ((n : ℕ) + m + 1))
    if (a = p ∧ (n : ℕ) < e.val) ∨ (e = p ∧ (n : ℕ) < a.val) then
      BoundaryEntries.intervalWeight s N r a (c z) else 0
  have hBi := physical_incident_edges_integral_internal β s n m hn x j
  change Integrable B μ ∧ (∫ z, B z ∂μ) = _ at hBi
  have hgrad (z) (hz : z ∈ Q) (h) : inner ℝ (gradient F z) h =
      β.val⁻¹ * fderiv ℝ (fderiv ℝ U) (c z) d (A h) := by
    have heF : F = fun z => β.val⁻¹ * fderiv ℝ U (A z + c 0) d := by
      funext z
      rw [← hc]
    rw [heF, show c z = A z + c 0 from hc z]
    exact affine_score_gradient_internal A (c 0) d β.val⁻¹ U z h (hUat z hz)
  have hbound : ∀ᵐ z ∂μ,
      sSup (Set.range fun h => 2 * inner ℝ (gradient F z) h -
        fderiv ℝ (fderiv ℝ V) z h h) ≤ β.val⁻¹ * ρ⁻¹ * B z := by
    filter_upwards [ConditionalEnergyMoments.physical_conditional_support
      (ofLong β s) n m n.pos (Equiv.refl _) x] with z hz
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨h,rfl⟩
    dsimp only
    erw [hgrad z hz h, hH z hz h]
    have hv := physical_adjacent_variational_internal β s n m ε κ₀ hε U hUv
      x hx z (hs z hz) j (A h) (hsumA h) (hactive h)
    change 2 * β.val⁻¹ * fderiv ℝ (fderiv ℝ U) (c z) d (A h) -
      fderiv ℝ (fderiv ℝ U) (c z) (A h) (A h) ≤ β.val⁻¹ * ρ⁻¹ * B z at hv
    simpa only [mul_assoc] using hv
  have hmono := integral_mono_ae hint (hBi.1.const_mul (β.val⁻¹ * ρ⁻¹)) hbound
  rw [integral_const_mul, hBi.2] at hmono
  exact hvar.trans hmono

/-- Explicit power bookkeeping for the adjacent-force estimate in
the proof of Lemma 5.8. The loss exponent contains no temperature
or ε dependence. -/
theorem adjacent_profile_algebra_internal (β s ε κ₀ n δ : ℝ)
    (hn : 0 < n) (hδ : 0 < δ) :
    β⁻¹ * ((2 : ℝ) ^ (-s - 3) * n ^ (-(2 * (s + 2)) * ε) * δ)⁻¹ *
        ((128 * (1 + (2 : ℝ) ^ (s + 1))) * n ^ ((κ₀ + 6) * ε) * δ ^ (-1 - s)) =
      (128 * (2 : ℝ) ^ (s + 3) * (1 + (2 : ℝ) ^ (s + 1)) * β⁻¹) *
        n ^ ((κ₀ + 2 * s + 10) * ε) * δ ^ (-2 - s) := by
  have htwo : ((2 : ℝ) ^ (-s - 3))⁻¹ = (2 : ℝ) ^ (s + 3) := by
    rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hnp : (n ^ (-(2 * (s + 2)) * ε))⁻¹ = n ^ ((2 * (s + 2)) * ε) := by
    rw [← Real.rpow_neg hn.le]
    congr 1
    ring
  have hnprod : n ^ ((2 * (s + 2)) * ε) * n ^ ((κ₀ + 6) * ε) =
      n ^ ((κ₀ + 2 * s + 10) * ε) := by
    rw [← Real.rpow_add hn]
    congr 1
    ring
  have hδprod : δ⁻¹ * δ ^ (-1 - s) = δ ^ (-2 - s) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hδ]
    congr 1
    ring
  calc
    _ = (128 * (2 : ℝ) ^ (s + 3) * (1 + (2 : ℝ) ^ (s + 1)) * β⁻¹) *
        (n ^ ((2 * (s + 2)) * ε) * n ^ ((κ₀ + 6) * ε)) *
        (δ⁻¹ * δ ^ (-1 - s)) := by rw [mul_inv_rev, mul_inv_rev, htwo, hnp]; ring
    _ = _ := by rw [hnprod, hδprod]

/-- Centered L² telescoping in the proof of Lemma 5.8, with finite
second moments and exactly the minimum of the two endpoint depths. -/
theorem centered_variance_telescoping_internal {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ+) (f : Fin (n : ℕ) → Ω → ℝ)
    (hf : ∀ i, MemLp (f i) 2 μ) (K a t : ℝ) (hK : 0 ≤ K) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (hstep : ∀ k : Fin (n : ℕ), k.val + 1 < (n : ℕ) →
      let F := fun z => f k z - f (k + 1) z
      (∫ z, (F z - ∫ w, F w ∂μ) ^ 2 ∂μ) ≤
        K * (n : ℝ) ^ a * (min (k.val + 1) ((n : ℕ) - k.val) : ℕ) ^ (-2 * t))
    (j l : Fin (n : ℕ)) :
    let F := fun z => f j z - f l z
    MemLp F 2 μ ∧ Real.sqrt (∫ z, (F z - ∫ w, F w ∂μ) ^ 2 ∂μ) ≤
      (K + 1) * (n : ℝ) ^ a * (Nat.dist j.val l.val : ℝ) *
        (min (min (j.val + 1) ((n : ℕ) - j.val))
          (min (l.val + 1) ((n : ℕ) - l.val)) : ℕ) ^ (-t) := by
  intro F
  let g := fun i z => f i z - ∫ w, f i w ∂μ
  have hg (i) : MemLp (g i) 2 μ := (hf i).sub (memLp_const _)
  have hcenter (i b : Fin (n : ℕ)) :
      (fun z => (f i z - f b z) - ∫ w, (f i w - f b w) ∂μ) =
        fun z => g i z - g b z := by
    rw [integral_sub ((hf i).integrable (by norm_num)) ((hf b).integrable (by norm_num))]
    funext z
    dsimp only [g]
    ring
  have hc (i b : Fin (n : ℕ)) (z : Ω) :
      (f i z - f b z) - ∫ w, (f i w - f b w) ∂μ = g i z - g b z :=
    congrFun (hcenter i b) z
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hna : 1 ≤ (n : ℝ) ^ a := Real.one_le_rpow hn1 ha
  let M := (K + 1) * (n : ℝ) ^ a
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hKM : K * (n : ℝ) ^ a ≤ M ^ 2 := by
    have hleft : K ≤ (K + 1) ^ 2 := by nlinarith only [sq_nonneg K]
    have hright : (n : ℝ) ^ a ≤ ((n : ℝ) ^ a) ^ 2 := by nlinarith only [hna]
    have h := mul_le_mul hleft hright (by positivity) (sq_nonneg (K + 1))
    simpa only [M, mul_pow] using h
  have hnorm (k : Fin (n : ℕ)) (hk : k.val + 1 < (n : ℕ)) :
      eLpNorm (fun z => g (k + 1) z - g k z) 2 μ ≤
        ENNReal.ofReal (M * (min (k.val + 1) ((n : ℕ) - k.val) : ℕ) ^ (-t)) := by
    let δ : ℝ := (min (k.val + 1) ((n : ℕ) - k.val) : ℕ)
    have hδ : 0 < δ := by
      dsimp only [δ]
      exact_mod_cast (show 0 < min (k.val + 1) ((n : ℕ) - k.val) by have := k.isLt; omega)
    have hpow : δ ^ (-2 * t) = (δ ^ (-t)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
      congr 1
      ring
    have hbd := (hstep k hk).trans (mul_le_mul_of_nonneg_right hKM
      (Real.rpow_nonneg hδ.le (-2 * t)))
    change (∫ z, ((f k z - f (k + 1) z) - ∫ w, (f k w - f (k + 1) w) ∂μ) ^ 2 ∂μ) ≤
      M ^ 2 * δ ^ (-2 * t) at hbd
    rw [hpow, ← mul_pow] at hbd
    simp_rw [hc] at hbd
    have hdiff : MemLp (fun z => g k z - g (k + 1) z) 2 μ := (hg k).sub (hg _)
    have hreal := Riesz1.eLpNorm_two_toReal_le_add_of_integral_sq_le hdiff
      (mul_nonneg hM (Real.rpow_nonneg hδ.le _)) (le_refl (0 : ℝ))
      (by simpa only [zero_pow (by norm_num : 2 ≠ 0), add_zero] using hbd)
    simp only [add_zero] at hreal
    have hneg : (fun z => g (k + 1) z - g k z) = -(fun z => g k z - g (k + 1) z) := by
      funext z; simp only [Pi.neg_apply]; ring
    rw [hneg, eLpNorm_neg, ← ENNReal.ofReal_toReal hdiff.eLpNorm_ne_top]
    exact ENNReal.ofReal_le_ofReal hreal
  have htel := block_moment_telescoping_internal μ n g (p := 2) (by norm_num) hM ht
    (by simpa only [ENNReal.ofReal_ofNat] using hnorm) j l
  have hdiff : MemLp (fun z => g j z - g l z) 2 μ := (hg j).sub (hg l)
  refine ⟨(hf j).sub (hf l), ?_⟩
  change Real.sqrt (∫ z, ((f j z - f l z) - ∫ w, (f j w - f l w) ∂μ) ^ 2 ∂μ) ≤ _
  simp_rw [hc]
  rw [← Riesz1.eLpNorm_two_toReal_eq_sqrt_integral_sq hdiff]
  apply ENNReal.toReal_le_of_le_ofReal (by positivity)
  simpa only [M, ENNReal.ofReal_ofNat] using htel

/-- See the proof of Lemma 5.8 in the paper, all of equation (5.24) and
equation (5.28). The observables are the literal compensated derivatives
of the physical energy. The loss exponent precedes β and ε,
and both positive constants precede the volume and retained-block size.
All variances have their finite second-moment certificates. -/
theorem conditional_force_variances (s : Riesz1.RieszExponent)
    (κ₀ : ℝ) (hκ₀ : 0 < κ₀) :
    ∃ κ > 0, ∀ (β : InverseTemperature) (ε : ℝ), 0 < ε →
      ∃ C > 0, ∀ (n : ℕ+) (m : ℕ), 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∃ U : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ,
        ContDiffOn ℝ ∞ U (gapAmbientDomain ((n : ℕ) + m).succPNat) ∧
        (∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) //
            y ∈ gapAmbientDomain ((n : ℕ) + m).succPNat},
          U y.val = β.val * physicalAmbientGapEnergy (ofLong β s) ((n : ℕ) + m).succPNat y) ∧
        ∀ x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
          let q := WithLp.toLp 2 (compensationVector n m)
          let Xi := fun (i : Fin (n : ℕ)) z => β.val⁻¹ *
            (fderiv ℝ U (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z))
                (EuclideanSpace.single (i.castAdd m).castSucc 1) -
              fderiv ℝ U (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) q)
          let μ := ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x
          (∀ i : Fin (n : ℕ),
            Riesz1.WeightedSobolev.IsWeightedH1 μ
              (AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ a, x.val a)) (Xi i) (gradient (Xi i)) ∧
            (∫ z, (Xi i z - ∫ w, Xi i w ∂μ) ^ 2 ∂μ) ≤
              β.val⁻¹ * (BoundaryEntries.physicalCrossing β s n m x i i -
                2 * compensationB β s n m i x + compensationC β s n m x) ∧
            β.val⁻¹ * (BoundaryEntries.physicalCrossing β s n m x i i -
                2 * compensationB β s n m i x + compensationC β s n m x) ≤
              β.val⁻¹ * (BoundaryEntries.physicalCrossing β s n m x i i + compensationC β s n m x)) ∧
          (x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀ → ∀ j l : Fin (n : ℕ),
            let F := fun z => Xi j z - Xi l z
            MemLp F 2 μ ∧ Real.sqrt (∫ z, (F z - ∫ w, F w ∂μ) ^ 2 ∂μ) ≤
              C * (n : ℝ) ^ (κ * ε) * (Nat.dist j.val l.val : ℝ) *
                (min (min (j.val + 1) ((n : ℕ) - j.val))
                  (min (l.val + 1) ((n : ℕ) - l.val)) : ℕ) ^ (-1 - s.val / 2)) := by
  classical
  let κ := κ₀ + 2 * s.val + 10
  have hκ : 0 < κ := by dsimp only [κ]; linarith [s.property.1]
  refine ⟨κ, hκ, fun β ε hε => ?_⟩
  let K := 128 * (2 : ℝ) ^ (s.val + 3) * (1 + (2 : ℝ) ^ (s.val + 1)) * β.val⁻¹
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (by positivity) (inv_nonneg.mpr β.property.le)
  refine ⟨K + 1, by linarith only [hK], fun n m hn => ?_⟩
  obtain ⟨U, hUs, hUv, hg⟩ := physical_tangent_scores_H1 (ofLong β s) n m n.pos
  refine ⟨U, hUs, hUv, fun x => ?_⟩
  intro q Xi μ
  have : IsProbabilityMeasure μ :=
    ProperMarginalChart.conditionalMeasure_probability (ofLong β s) n m n.pos (Equiv.refl _) x
  let c := fun z => RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)
  let Q := AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ a, x.val a)
  have hXi (i : Fin (n : ℕ)) :
      Riesz1.WeightedSobolev.IsWeightedH1 μ Q (Xi i) (gradient (Xi i)) := by
    let e := EuclideanSpace.single (i.castAdd m).castSucc (1 : ℝ)
    let d := β.val⁻¹ • (e - q)
    have hsum : (∑ a, d a) = 0 := by
      simp only [d, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, ← Finset.mul_sum,
        Finset.sum_sub_distrib]
      have he : (∑ a, e a) = 1 := by simp [e, EuclideanSpace.single, PiLp.single_apply]
      rw [he, show (∑ a, q a) = 1 from compensationVector_sum n m, sub_self, mul_zero]
    have hgraph := hg (Equiv.refl _) x d hsum
    have heq : (fun z => fderiv ℝ U (c z) d) = Xi i := by
      funext z
      simp only [d, map_smul, map_sub, smul_eq_mul]
      rfl
    change Riesz1.WeightedSobolev.IsWeightedH1 μ Q
      (fun z => fderiv ℝ U (c z) d) (gradient (fun z => fderiv ℝ U (c z) d)) at hgraph
    rw [heq] at hgraph
    exact hgraph
  refine ⟨fun i => ⟨hXi i, ?_, compensated_crossing_le β s n m i x⟩, fun hx j l => ?_⟩
  · have hh := physical_force_variance_internal β s n m U hUs hUv x i
    have heq : (fun z => β.val⁻¹ * fderiv ℝ U (c z)
        (EuclideanSpace.single (i.castAdd m).castSucc 1 - q)) = Xi i := by
      funext z
      simp only [map_sub]
      rfl
    have hi := hXi i
    rw [← heq] at hi
    exact heq ▸ hh hi
  · have hstep (k : Fin (n : ℕ)) (hk : k.val + 1 < (n : ℕ)) :
        let F := fun z => Xi k z - Xi (k + 1) z
        (∫ z, (F z - ∫ w, F w ∂μ) ^ 2 ∂μ) ≤
          K * (n : ℝ) ^ (κ * ε) *
            (min (k.val + 1) ((n : ℕ) - k.val) : ℕ) ^ (-2 * (1 + s.val / 2)) := by
      let j : Fin ((n : ℕ) - 1) := ⟨k.val, by omega⟩
      let i : Fin ((n : ℕ) + m + 1) := ⟨j.val, by have := j.isLt; omega⟩
      let p : Fin ((n : ℕ) + m + 1) := ⟨j.val + 1, by have := j.isLt; omega⟩
      let d := EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single p 1
      let A := fun z => β.val⁻¹ * fderiv ℝ U (c z) d
      have hsum : ∑ a, (β.val⁻¹ • d) a = 0 := by
        simp only [PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum, d, PiLp.sub_apply,
          Finset.sum_sub_distrib]
        simp [EuclideanSpace.single, PiLp.single_apply]
      have hgraph := hg (Equiv.refl _) x (β.val⁻¹ • d) hsum
      have heA : (fun z => fderiv ℝ U (c z) (β.val⁻¹ • d)) = A := by
        funext z
        simp only [map_smul, smul_eq_mul]
        rfl
      change Riesz1.WeightedSobolev.IsWeightedH1 μ Q
        (fun z => fderiv ℝ U (c z) (β.val⁻¹ • d))
        (gradient (fun z => fderiv ℝ U (c z) (β.val⁻¹ • d))) at hgraph
      rw [heA] at hgraph
      have hvar := physical_adjacent_variance_internal β s n m ε κ₀ hε.le hn U hUs hUv x hx j hgraph
      let ρ := (2 : ℝ) ^ (-s.val - 3) * (n : ℝ) ^ (-(2 * (s.val + 2)) * ε) *
        (min (j.val + 1) ((n : ℕ) - j.val) : ℕ)
      let a : Fin (n : ℕ) := ⟨j.val, by have := j.isLt; omega⟩
      let b : Fin (n : ℕ) := ⟨j.val + 1, by have := j.isLt; omega⟩
      let S := BoundaryEntries.physicalCrossing β s n m x
      change (∫ z, (A z - ∫ w, A w ∂μ) ^ 2 ∂μ) ≤
        β.val⁻¹ * ρ⁻¹ * (S a a - S a b - S b a + S b b) at hvar
      have hρ : 0 ≤ ρ := by dsimp only [ρ]; positivity
      have hbound := mul_le_mul_of_nonneg_left
        (physical_adjacent_crossing_bound_internal β s n m ε κ₀ hε.le hn x hx j)
        (mul_nonneg (inv_nonneg.mpr β.property.le) (inv_nonneg.mpr hρ))
      have hfinal := hvar.trans hbound
      have hδ : (0 : ℝ) < (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) := by
        exact_mod_cast (show 0 < min (j.val + 1) ((n : ℕ) - j.val) by have := j.isLt; omega)
      have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
      change (∫ z, (A z - ∫ w, A w ∂μ) ^ 2 ∂μ) ≤
        β.val⁻¹ * ((2 : ℝ) ^ (-s.val - 3) * (n : ℝ) ^ (-(2 * (s.val + 2)) * ε) *
          (min (j.val + 1) ((n : ℕ) - j.val) : ℕ))⁻¹ *
          ((128 * (1 + (2 : ℝ) ^ (s.val + 1))) * (n : ℝ) ^ ((κ₀ + 6) * ε) *
            (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) ^ (-1 - s.val)) at hfinal
      rw [adjacent_profile_algebra_internal β.val s.val ε κ₀ (n : ℝ)
        (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) hn0 hδ] at hfinal
      have hp : ((k + 1).castAdd m).castSucc = p := by
        apply Fin.ext
        exact Fin.val_add_one_of_lt' hk
      have hi : (k.castAdd m).castSucc = i := Fin.ext rfl
      have heq : (fun z => Xi k z - Xi (k + 1) z) = A := by
        funext z
        dsimp only [Xi, A, d, c]
        rw [map_sub, hi, hp]
        ring
      intro F
      rw [show F = A from heq]
      have hexp : -2 * (1 + s.val / 2) = -2 - s.val := by ring
      rw [hexp]
      exact hfinal
    have ht : 0 ≤ 1 + s.val / 2 := by linarith [s.property.1]
    have hh := centered_variance_telescoping_internal μ n Xi (fun i => (hXi i).1)
      K (κ * ε) (1 + s.val / 2) hK (mul_nonneg hκ.le hε.le) ht hstep j l
    have hexp : -(1 + s.val / 2) = -1 - s.val / 2 := by ring
    simpa only [hexp] using hh

end Riesz2.ConditionalForces
