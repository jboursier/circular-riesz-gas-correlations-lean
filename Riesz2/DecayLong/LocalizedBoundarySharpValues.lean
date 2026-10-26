/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.LocalizedBoundarySourceCore

/-!
# Sharp values of the localization boundary correction

The proof of Proposition 5.15, Step 1, retains the two value
powers in the display preceding equation (5.64). Value and
gradient sources use their separate global exponents throughout.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Fin.NatCast
namespace Riesz2.LocalizedBoundary
open LocalizedMatrix IntervalBoundary
variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

/-- Proposition 5.15, Step 1: extract the value and gradient
components without weakening the value exponent. -/
theorem component_bounds_separate_internal (s : Riesz1.RieszExponent) (m : ℕ+)
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (i₀ j : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1) (A : ℝ)
    (hu : Real.sqrt (∑ i, (weightRadius m i i₀ ^ (3 / 2 - s.val) * ‖(u i).val‖) ^ 2) +
      Real.sqrt (∑ i, weightRadius m i i₀ ^ (2 * (1 - s.val / 2)) * Q.2 (u i) (u i)) ≤ A) :
    ‖(u j).val‖ ≤ weightRadius m j i₀ ^ (-(3 / 2 - s.val)) * A ∧
      Real.sqrt (Q.2 (u j) (u j)) ≤ weightRadius m j i₀ ^ (-(1 - s.val / 2)) * A := by
  let w := weightRadius m j i₀
  have hw1 : 1 ≤ w := one_le_weightRadius m j i₀
  have hw : 0 < w := by linarith
  have hjv : w ^ (3 / 2 - s.val) * ‖(u j).val‖ ≤
      Real.sqrt (∑ i, (weightRadius m i i₀ ^ (3 / 2 - s.val) * ‖(u i).val‖) ^ 2) := by
    have hh := Real.sqrt_le_sqrt (Finset.single_le_sum (fun i _ => sq_nonneg
      (weightRadius m i i₀ ^ (3 / 2 - s.val) * ‖(u i).val‖)) (Finset.mem_univ j))
    change Real.sqrt ((w ^ (3 / 2 - s.val) * ‖(u j).val‖) ^ 2) ≤ _ at hh
    rwa [Real.sqrt_sq (by positivity : 0 ≤ w ^ (3 / 2 - s.val) * ‖(u j).val‖)] at hh
  have hjg : w ^ (1 - s.val / 2) * Real.sqrt (Q.2 (u j) (u j)) ≤
      Real.sqrt (∑ i, weightRadius m i i₀ ^ (2 * (1 - s.val / 2)) * Q.2 (u i) (u i)) := by
    have hh := Real.sqrt_le_sqrt (Finset.single_le_sum (fun (i : Fin (m : ℕ)) _ =>
      mul_nonneg (Real.rpow_nonneg (by linarith [one_le_weightRadius m i i₀] : 0 ≤ weightRadius m i i₀) (2 * (1 - s.val / 2)))
        (hQ.2.2.1 (u i))) (Finset.mem_univ j))
    have hp : w ^ (2 * (1 - s.val / 2)) = (w ^ (1 - s.val / 2)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hw.le]
      congr 1
      ring
    change Real.sqrt (w ^ (2 * (1 - s.val / 2)) * Q.2 (u j) (u j)) ≤ _ at hh
    rwa [hp, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.rpow_nonneg hw.le _)] at hh
  have hv : w ^ (3 / 2 - s.val) * ‖(u j).val‖ ≤ A := by
    linarith only [hjv, hu, Real.sqrt_nonneg
      (∑ i, weightRadius m i i₀ ^ (2 * (1 - s.val / 2)) * Q.2 (u i) (u i))]
  have hg : w ^ (1 - s.val / 2) * Real.sqrt (Q.2 (u j) (u j)) ≤ A := by
    linarith only [hjg, hu, Real.sqrt_nonneg
      (∑ i, (weightRadius m i i₀ ^ (3 / 2 - s.val) * ‖(u i).val‖) ^ 2)]
  constructor
  · have hh := mul_le_mul_of_nonneg_left hv
      (Real.rpow_nonneg hw.le (-(3 / 2 - s.val)))
    rwa [← mul_assoc, ← Real.rpow_add hw, neg_add_cancel, Real.rpow_zero, one_mul] at hh
  · have hh := mul_le_mul_of_nonneg_left hg
      (Real.rpow_nonneg hw.le (-(1 - s.val / 2)))
    rwa [← mul_assoc, ← Real.rpow_add hw, neg_add_cancel, Real.rpow_zero, one_mul] at hh

/-- Proposition 5.15, Step 1: superpose each source coordinate
with value exponent `3/2-s` and gradient exponent `1-s/2`. -/
theorem unrestricted_superposition_separate (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ)
    (hκstar : 0 < κstar) (hγstar : 0 < γstar) (M₀ : ℕ+) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ εmin : ℝ, 0 < εmin →
    ∀ Cstar : ℝ, 1 ≤ Cstar →
    ∀ βlo : ℝ, 0 < βlo → ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, εmin ≤ ε →
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
    ∀ f : Fin (m : ℕ) → Lp ℝ 2 ν,
    ∃! u : Fin (m : ℕ) → Q.1,
      WeightedWeakSolution Q (fun x => β • M x) ⊤ f u ∧
      ∀ j, (‖(u j).val‖ ≤ C * (n : ℝ) ^ (κ * ε) *
          ∑ l, weightRadius m j l ^ (-(3 / 2 - s.val)) * ‖f l‖) ∧
        (Real.sqrt (Q.2 (u j) (u j)) ≤ C * (n : ℝ) ^ (κ * ε) *
          ∑ l, weightRadius m j l ^ (-(1 - s.val / 2)) * ‖f l‖) := by
  obtain ⟨κ, hκ, hb⟩ := LocalizedMatrix.Analytic.global_bis hzeta s κstar γstar
    hκstar hγstar M₀
  refine ⟨κ, hκ, fun εmin hεmin Cstar hCstar βlo hβlo βhi hβhi => ?_⟩
  obtain ⟨C, hC, hb⟩ := hb εmin hεmin Cstar hCstar βlo hβlo βhi hβhi
  refine ⟨C, hC, ?_⟩
  intro ε hε Ω _ ν _ Q hQ hQc n m hm hn hnm hmn K hK hKm M hM β hβl hβu f
  have hp : ∀ l, ∃ u : Fin (m : ℕ) → Q.1,
      WeightedWeakSolution Q (fun x => β • M x) ⊤ (fun i => if i = l then f l else 0) u ∧
      ∀ j, (‖(u j).val‖ ≤
        weightRadius m j l ^ (-(3 / 2 - s.val)) * (C * (n : ℝ) ^ (κ * ε) * ‖f l‖)) ∧
        (Real.sqrt (Q.2 (u j) (u j)) ≤
        weightRadius m j l ^ (-(1 - s.val / 2)) * (C * (n : ℝ) ^ (κ * ε) * ‖f l‖)) := by
    intro l
    obtain ⟨u, ⟨hu, hbound⟩, _⟩ := hb ε hε ν Q hQ hQc n m hm hn hnm hmn hK hKm
      M hM β hβl hβu (f l) l
    exact ⟨u, hu, fun j => component_bounds_separate_internal s m Q hQ l j u _ hbound⟩
  choose u hu hub using hp
  let z := fun i => ∑ l, u l i
  have hz : WeightedWeakSolution Q (fun x => β • M x) ⊤ f z := by
    simpa only [Finset.sum_ite_eq, Finset.mem_univ, ite_true] using
      weak_sum_internal Q (fun x => β • M x)
        (SchurRestriction.periodized_scaled_measurable β hM)
        (SchurRestriction.periodized_scaled_bounded β hM) _ u hu
  have huniq := (AbstractEquation.existence_energy Q hQ β (hβlo.trans_le hβl)
    M hM.1 _ (SchurRestriction.periodized_mass_pos hCstar)
    (hM.2.1.mono (fun _ hx => ⟨hx.1, hx.2.2.1⟩)) ⊤ f).1
  refine ⟨z, ⟨hz, fun j => ?_⟩, fun v hv => huniq.unique hv.1 hz⟩
  have hv : ‖(z j).val‖ ≤ ∑ l, ‖(u l j).val‖ := by
    simpa only [z, Submodule.coe_sum] using norm_sum_le Finset.univ (fun l => (u l j).val)
  have hg := energy_sqrt_sum_internal Q hQ Finset.univ (fun l => u l j)
  constructor
  · calc
      _ ≤ ∑ l, ‖(u l j).val‖ := hv
      _ ≤ ∑ l, weightRadius m j l ^ (-(3 / 2 - s.val)) *
          (C * (n : ℝ) ^ (κ * ε) * ‖f l‖) := Finset.sum_le_sum (fun l _ => (hub l j).1)
      _ = _ := by simp only [Finset.mul_sum]; congr 1; funext l; ring
  · calc
      _ ≤ ∑ l, Real.sqrt (Q.2 (u l j) (u l j)) := hg
      _ ≤ ∑ l, weightRadius m j l ^ (-(1 - s.val / 2)) *
          (C * (n : ℝ) ^ (κ * ε) * ‖f l‖) := Finset.sum_le_sum (fun l _ => (hub l j).2)
      _ = _ := by simp only [Finset.mul_sum]; congr 1; funext l; ring

/-- Proposition 5.15, Step 1: count the active distance shells
before distinguishing the three value-exponent regimes. -/
theorem active_weight_sum_filter_internal (n m : ℕ+) (hn : 2 * (n : ℕ) ≤ (m : ℕ))
    (j : Fin (n : ℕ)) (b : ℝ) :
    (∑ i : Fin (n : ℕ),
      weightRadius m (j.castLE (by omega)) (i.castLE (by omega)) ^ (-b)) ≤
        ∑ i ∈ Finset.univ.filter (fun i =>
          weightRadius m i (j.castLE (by omega)) ≤ (n : ℝ)),
            weightRadius m i (j.castLE (by omega)) ^ (-b) := by
  let e : Fin (n : ℕ) ↪ Fin (m : ℕ) := ⟨Fin.castLE (by omega), Fin.castLE_injective _⟩
  let c := j.castLE (by omega : (n : ℕ) ≤ (m : ℕ))
  have hs : Finset.univ.map e ⊆ Finset.univ.filter (fun i => weightRadius m i c ≤ (n : ℝ)) := by
    intro i hi
    obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    change 1 + (Riesz1.cyclicIndexDistance m (k.castLE (by omega)) (j.castLE (by omega)) : ℝ) ≤ _
    rw [LocalizedMatrix.active_distance m n hn]
    have hdist : 1 + Nat.dist k.val j.val ≤ (n : ℕ) := by
      have := k.isLt
      have := j.isLt
      unfold Nat.dist
      omega
    exact_mod_cast hdist
  have hh := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun i => weightRadius m i c ^ (-b)) hs
    (fun i _ _ => Real.rpow_nonneg (by linarith [one_le_weightRadius m i c]) (-b))
  simpa only [Finset.sum_map, e, c, Function.Embedding.coeFn_mk, weightRadius,
    cyclicIndexDistance_comm'] using hh

/-- Proposition 5.15, Step 1: the three cases `a<1`, `a=1`
and `a>1` in the value convolution, with a common logarithmic envelope. -/
theorem active_weight_sum_log_internal (a : ℝ) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ+) (hn : 2 * (n : ℕ) ≤ (m : ℕ))
      (j : Fin (n : ℕ)),
      (∑ i : Fin (n : ℕ),
        weightRadius m (j.castLE (by omega)) (i.castLE (by omega)) ^ (-a)) ≤
        C * Real.log (2 * (n : ℝ)) * (1 + (n : ℝ) ^ (1 - a)) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rcases lt_trichotomy a 1 with h | rfl | h
  · refine ⟨(2 / (1 - a)) / Real.log 2, by positivity, ?_⟩
    intro n m hn j
    have hl : Real.log 2 ≤ Real.log (2 * (n : ℝ)) :=
      Real.log_le_log (by norm_num) (by
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
        linarith)
    apply (active_weight_sum_internal n m hn j a ha h).trans
    have hh := mul_le_mul_of_nonneg_right hl
      (show 0 ≤ (2 / (1 - a)) / Real.log 2 by positivity)
    have he : Real.log 2 * ((2 / (1 - a)) / Real.log 2) = 2 / (1 - a) := by
      field_simp
    rw [he] at hh
    rw [mul_comm (Real.log (2 * (n : ℝ)))] at hh
    exact mul_le_mul hh (le_add_of_nonneg_left (show (0 : ℝ) ≤ 1 by norm_num))
      (Real.rpow_nonneg (by positivity) _) (hh.trans' (by positivity))
  · refine ⟨2 * (1 + 1 / Real.log 2), by positivity, ?_⟩
    intro n m hn j
    apply (active_weight_sum_filter_internal n m hn j 1).trans
    apply (sum_weightRadius_le_of_one m (j.castLE (by omega))
      (show (1 : ℝ) ≤ n by exact_mod_cast n.pos)).trans
    simp only [sub_self, Real.rpow_zero]
    have hl : 0 ≤ Real.log (2 * (n : ℝ)) := Real.log_nonneg (by
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
      linarith)
    nlinarith only [mul_nonneg (show 0 ≤ 2 * (1 + 1 / Real.log 2) by positivity) hl]
  · let T := ∑' k : ℕ, (1 + (k : ℝ)) ^ (-a)
    have hT : 0 ≤ T := tsum_nonneg (fun _ => Real.rpow_nonneg (by positivity) _)
    refine ⟨2 * (T + 1) / Real.log 2, by positivity, ?_⟩
    intro n m hn j
    apply (active_weight_sum_filter_internal n m hn j a).trans
    apply (sum_weightRadius_le_of_gt_one m (j.castLE (by omega)) h
      (show (1 : ℝ) ≤ n by exact_mod_cast n.pos)).trans
    have hl : Real.log 2 ≤ Real.log (2 * (n : ℝ)) :=
      Real.log_le_log (by norm_num) (by
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
        linarith)
    have hh := mul_le_mul_of_nonneg_left hl
      (show 0 ≤ 2 * (T + 1) / Real.log 2 by positivity)
    have he : 2 * (T + 1) / Real.log 2 * Real.log 2 = 2 * (T + 1) := by field_simp
    rw [he] at hh
    apply (show 2 * T ≤ 2 * (T + 1) by linarith).trans
    exact hh.trans (le_mul_of_one_le_right (mul_nonneg (by positivity) (hlog.le.trans hl))
      (le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _)))

/-- Proposition 5.15, Step 1: the central/boundary split with
value exponent `3/2-s`, before comparison with the localization target. -/
theorem boundary_convolution_sharp (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ+) (hn : 2 * (n : ℕ) ≤ (m : ℕ))
      (q : ℕ) (hq : (n : ℕ) = 2 * q + 1) (j : Fin (n : ℕ)) (hj : j.val = q),
      (∑ i : Fin (n : ℕ),
        weightRadius m (j.castLE (by omega)) (i.castLE (by omega)) ^ (-(3 / 2 - s.val)) *
          ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-(1 + s.val) / 2)) ≤
        C * Real.log (2 * (n : ℝ)) *
          ((n : ℝ) ^ (-(1 + s.val) / 2) + (n : ℝ) ^ (s.val / 2 - 1)) := by
  let a := 3 / 2 - s.val
  let t := (1 + s.val) / 2
  have ha : 0 < a := by dsimp [a]; linarith [s.property.2]
  have ht : 0 < t := by dsimp [t]; linarith [s.property.1]
  have ht1 : t < 1 := by dsimp [t]; linarith [s.property.2]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨C, hC, hsum⟩ := active_weight_sum_log_internal a ha
  let B := 4 ^ a * (2 / (1 - t))
  refine ⟨4 ^ t * C + B / Real.log 2, by dsimp [B]; positivity, ?_⟩
  intro n m hn q hq j hj
  let r := fun i : Fin (n : ℕ) => weightRadius m (j.castLE (by omega)) (i.castLE (by omega))
  let d := fun i : Fin (n : ℕ) => ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ)
  have hnp : (0 : ℝ) < n := by positivity
  have hr (i) : 0 < r i := by dsimp [r]; linarith [one_le_weightRadius m (j.castLE (by omega)) (i.castLE (by omega))]
  have hd (i : Fin (n : ℕ)) : 0 < d i := by
    dsimp [d]
    exact_mod_cast (show 0 < min (i.val + 1) ((n : ℕ) - i.val) by have := i.isLt; omega)
  have hsep (i : Fin (n : ℕ)) : (n : ℝ) / 4 ≤ d i ∨ (n : ℝ) / 4 ≤ r i := by
    have he : d i + r i = (q : ℝ) + 2 := by
      dsimp [d, r, weightRadius]
      rw [LocalizedMatrix.active_distance m n hn, hj]
      have he : min (i.val + 1) ((n : ℕ) - i.val) + Nat.dist q i.val = q + 1 := by
        have := i.isLt
        unfold Nat.dist
        omega
      exact_mod_cast (show min (i.val + 1) ((n : ℕ) - i.val) +
        (1 + Nat.dist q i.val) = q + 2 by omega)
    have hnq : (n : ℝ) = 2 * (q : ℝ) + 1 := by exact_mod_cast hq
    by_cases hh : (n : ℝ) / 4 ≤ d i
    · exact Or.inl hh
    · exact Or.inr (by linarith)
  have hpt (i : Fin (n : ℕ)) : r i ^ (-a) * d i ^ (-t) ≤
      ((n : ℝ) / 4) ^ (-t) * r i ^ (-a) + ((n : ℝ) / 4) ^ (-a) * d i ^ (-t) := by
    rcases hsep i with h | h
    · have hh := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < (n : ℝ) / 4) h (neg_nonpos.mpr ht.le)
      nlinarith only [mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg (hr i).le (-a)),
        mul_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ (n : ℝ) / 4) (-a))
          (Real.rpow_nonneg (hd i).le (-t))]
    · have hh := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < (n : ℝ) / 4) h (neg_nonpos.mpr ha.le)
      nlinarith only [mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg (hd i).le (-t)),
        mul_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ (n : ℝ) / 4) (-t))
          (Real.rpow_nonneg (hr i).le (-a))]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpt i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  have hsr := hsum n m hn j
  have hsd := boundary_weight_sum_internal n t ht ht1
  have hp (b : ℝ) : ((n : ℝ) / 4) ^ (-b) = 4 ^ b * (n : ℝ) ^ (-b) := by
    rw [Real.div_rpow hnp.le (by norm_num), div_eq_mul_inv,
      ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), neg_neg, mul_comm]
  have hpa : (n : ℝ) ^ (-t) * (n : ℝ) ^ (1 - a) = (n : ℝ) ^ (s.val / 2 - 1) := by
    rw [← Real.rpow_add hnp]; congr 1; dsimp [a, t]; ring
  have hpb : (n : ℝ) ^ (-a) * (n : ℝ) ^ (1 - t) = (n : ℝ) ^ (s.val / 2 - 1) := by
    rw [← Real.rpow_add hnp]; congr 1; dsimp [a, t]; ring
  have hl : Real.log 2 ≤ Real.log (2 * (n : ℝ)) := Real.log_le_log (by norm_num) (by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
    linarith)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hh := mul_le_mul_of_nonneg_left hl (div_nonneg hB hl2.le)
  rw [div_mul_cancel₀ _ hl2.ne'] at hh
  have heq : ((n : ℝ) / 4) ^ (-t) *
      (C * Real.log (2 * (n : ℝ)) * (1 + (n : ℝ) ^ (1 - a))) +
      ((n : ℝ) / 4) ^ (-a) * (2 / (1 - t) * (n : ℝ) ^ (1 - t)) =
      (4 ^ t * C) * Real.log (2 * (n : ℝ)) *
        ((n : ℝ) ^ (-t) + (n : ℝ) ^ (s.val / 2 - 1)) +
        B * (n : ℝ) ^ (s.val / 2 - 1) := by
    rw [hp t, hp a]
    dsimp only [B]
    linear_combination (4 ^ t * C * Real.log (2 * (n : ℝ))) * hpa +
      (4 ^ a * (2 / (1 - t))) * hpb
  simp only [show -(1 + s.val) / 2 = -((1 + s.val) / 2) by ring]
  change (∑ i, r i ^ (-a) * d i ^ (-t)) ≤
    (4 ^ t * C + B / Real.log 2) * Real.log (2 * (n : ℝ)) *
      ((n : ℝ) ^ (-t) + (n : ℝ) ^ (s.val / 2 - 1))
  apply hs.trans
    ((add_le_add (mul_le_mul_of_nonneg_left hsr (by positivity))
      (mul_le_mul_of_nonneg_left hsd (by positivity))).trans ?_)
  rw [heq]
  change _ ≤ (4 ^ t * C + B / Real.log 2) * Real.log (2 * (n : ℝ)) *
    ((n : ℝ) ^ (-t) + (n : ℝ) ^ (s.val / 2 - 1))
  have hm := mul_le_mul_of_nonneg_right hh
    (Real.rpow_nonneg hnp.le (s.val / 2 - 1))
  have he := mul_nonneg (mul_nonneg (div_nonneg hB hl2.le)
    ((hl2.le).trans hl)) (Real.rpow_nonneg hnp.le (-t))
  nlinarith only [hm, he]

/-- Proposition 5.15, Step 1: construct the boundary source
and retain its separate value and gradient convolutions. The convolution
premise is internal and is supplied by `boundary_convolution_sharp`. -/
theorem boundary_source_solution_sharp_internal (s : Riesz1.RieszExponent) (n m : ℕ+)
    (hn : 2 * (n : ℕ) ≤ (m : ℕ)) (q : ℕ) (hq : (n : ℕ) = 2 * q + 1)
    (j : Fin (n : ℕ)) (hj : j.val = q)
    (Q : ScalarFormData ν) (M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (A β E Cs : ℝ) (hA : 0 ≤ A) (hβ : 0 ≤ β) (hE : 0 ≤ E)
    (solve : ∀ f : Fin (m : ℕ) → Lp ℝ 2 ν, ∃! z : Fin (m : ℕ) → Q.1,
      WeightedWeakSolution Q (fun x => β • M x) ⊤ f z ∧
      ∀ k, (‖(z k).val‖ ≤ A * ∑ l, weightRadius m k l ^ (-(3 / 2 - s.val)) * ‖f l‖) ∧
        (Real.sqrt (Q.2 (z k) (z k)) ≤ A * ∑ l, weightRadius m k l ^ (-(1 - s.val / 2)) * ‖f l‖))
    (unique : ∀ (f : Fin (m : ℕ) → Lp ℝ 2 ν) (z y : Fin (m : ℕ) → Q.1),
      WeightedWeakSolution Q (fun x => β • M x) ⊤ f z →
      WeightedWeakSolution Q (fun x => β • M x) ⊤ f y → z = y)
    (R : Ω → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (hRm : ∀ l i, Measurable (fun x => R x l i))
    (hR : ∀ᵐ x ∂ν, ∀ l, Real.sqrt (∑ i, R x l i ^ 2) ≤
      E * ((min (l.val + 1) ((n : ℕ) - l.val) : ℕ) : ℝ) ^ (-(1 + s.val) / 2))
    (hconv : (∑ i : Fin (n : ℕ),
      weightRadius m (j.castLE (by omega)) (i.castLE (by omega)) ^ (-(3 / 2 - s.val)) *
        ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-(1 + s.val) / 2)) ≤
        Cs * Real.log (2 * (n : ℝ)) *
          ((n : ℝ) ^ (-(1 + s.val) / 2) + (n : ℝ) ^ (s.val / 2 - 1)))
    (v : Fin (n : ℕ) → Lp ℝ 2 ν) :
    ∃ g : Fin (n : ℕ) → Lp ℝ 2 ν,
      (∀ l, ∀ᵐ x ∂ν, g l x = -β * ∑ i, R x l i * v i x) ∧
      (∀ l, ‖g l‖ ≤ β * E *
        ((min (l.val + 1) ((n : ℕ) - l.val) : ℕ) : ℝ) ^ (-(1 + s.val) / 2) *
          Real.sqrt (∑ i, ‖v i‖ ^ 2)) ∧
      ∃! z : Fin (m : ℕ) → Q.1,
        WeightedWeakSolution Q (fun x => β • M x) ⊤
          (fun i => ∑ l : Fin (n : ℕ), if i = l.castLE (by omega) then g l else 0) z ∧
        (‖(z (j.castLE (by omega))).val‖ ≤
          A * β * E * Real.sqrt (∑ i, ‖v i‖ ^ 2) * Cs * Real.log (2 * (n : ℝ)) *
            ((n : ℝ) ^ (-(1 + s.val) / 2) + (n : ℝ) ^ (s.val / 2 - 1))) ∧
        (Real.sqrt (Q.2 (z (j.castLE (by omega))) (z (j.castLE (by omega)))) ≤
          A * β * E * Real.sqrt (∑ i, ‖v i‖ ^ 2) *
            (4 ^ ((1 + s.val) / 2) * (2 / (s.val / 2)) +
              4 ^ (1 - s.val / 2) * (2 / ((1 - s.val) / 2))) *
                (n : ℝ) ^ (-(1 / 2 : ℝ))) := by
  let δ := fun l : Fin (n : ℕ) => ((min (l.val + 1) ((n : ℕ) - l.val) : ℕ) : ℝ)
  let V := Real.sqrt (∑ i, ‖v i‖ ^ 2)
  have hg : ∀ l : Fin (n : ℕ), ∃ g : Lp ℝ 2 ν,
      (∀ᵐ x ∂ν, g x = -β * ∑ i, R x l i * v i x) ∧
      ‖g‖ ≤ β * E * δ l ^ (-(1 + s.val) / 2) * V := by
    intro l
    obtain ⟨f, hf, hfn⟩ := row_source_internal (fun i x => R x l i) (hRm l)
      (E * δ l ^ (-(1 + s.val) / 2)) (mul_nonneg hE (by positivity))
      (hR.mono (fun _ hx => hx l)) v
    refine ⟨-β • f, ?_, ?_⟩
    · filter_upwards [Lp.coeFn_smul (-β) f, hf] with x hx hy
      simp only [hx, Pi.smul_apply, smul_eq_mul, hy]
    · rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hβ]
      calc
        β * ‖f‖ ≤ β * (E * δ l ^ (-(1 + s.val) / 2) * V) :=
          mul_le_mul_of_nonneg_left hfn hβ
        _ = _ := by ring
  choose g hg hgn using hg
  let f := fun i : Fin (m : ℕ) => ∑ l : Fin (n : ℕ),
    if i = l.castLE (by omega : (n : ℕ) ≤ (m : ℕ)) then g l else 0
  obtain ⟨z, ⟨hz, hzb⟩, _⟩ := solve f
  have hbound (e Z : ℝ)
      (hzZ : Z ≤ A * ∑ l, weightRadius m (j.castLE (by omega)) l ^ (-e) * ‖f l‖) :
      Z ≤ A * β * E * V * (∑ l : Fin (n : ℕ),
        weightRadius m (j.castLE (by omega)) (l.castLE (by omega)) ^ (-e) * δ l ^ (-(1 + s.val) / 2)) := by
    let c := j.castLE (by omega : (n : ℕ) ≤ (m : ℕ))
    let w := fun i : Fin (m : ℕ) => weightRadius m c i ^ (-e)
    have hw (i) : 0 ≤ w i := Real.rpow_nonneg (by linarith [one_le_weightRadius m c i]) _
    have hsum : (∑ i, w i * ‖f i‖) ≤ ∑ l : Fin (n : ℕ), w (l.castLE (by omega)) * ‖g l‖ := by
      calc
        _ ≤ ∑ i, w i * ∑ l : Fin (n : ℕ),
            ‖if i = l.castLE (by omega) then g l else 0‖ :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (norm_sum_le _ _) (hw i))
        _ = _ := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro l _
          simp only [apply_ite, norm_zero, mul_zero, Finset.sum_ite_eq',
            Finset.mem_univ, ite_true]
    have hsum' : (∑ l : Fin (n : ℕ), w (l.castLE (by omega)) * ‖g l‖) ≤
        β * E * V * (∑ l : Fin (n : ℕ), w (l.castLE (by omega)) * δ l ^ (-(1 + s.val) / 2)) := by
      calc
        _ ≤ ∑ l : Fin (n : ℕ), w (l.castLE (by omega)) *
            (β * E * δ l ^ (-(1 + s.val) / 2) * V) :=
          Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_left (hgn l) (hw _))
        _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro l _; ring
    calc
      _ ≤ A * ∑ i, w i * ‖f i‖ := hzZ
      _ ≤ A * (β * E * V *
          (∑ l : Fin (n : ℕ), w (l.castLE (by omega)) * δ l ^ (-(1 + s.val) / 2))) :=
        mul_le_mul_of_nonneg_left (hsum.trans hsum') hA
      _ = _ := by ring
  have hv := (hbound (3 / 2 - s.val) _ (hzb _).1).trans
    (mul_le_mul_of_nonneg_left hconv (by positivity : 0 ≤ A * β * E * V))
  have hgrad := (hbound (1 - s.val / 2) _ (hzb _).2).trans
    (mul_le_mul_of_nonneg_left (boundary_convolution_internal s n m hn q hq j hj)
      (by positivity : 0 ≤ A * β * E * V))
  refine ⟨g, hg, hgn, z, ⟨hz, ?_, ?_⟩, ?_⟩
  · exact hv.trans_eq (by ring)
  · exact hgrad.trans_eq (by ring)
  · intro y hy
    exact unique f y z hy.1 hz

/-- Proposition 5.15, Step 1: change the boundary scale from
`n₀` to `R`, keeping an arbitrary nonpositive convolution power. -/
theorem boundary_scale_power_internal (R N e : ℝ) (hR : 0 < R) (_hN : 0 < N)
    (hRN : R / 8 ≤ N) (he : e ≤ 0) : N ^ e ≤ 8 ^ (-e) * R ^ e := by
  have hh := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < R / 8) hRN he
  have hp : (R / 8) ^ e = 8 ^ (-e) * R ^ e := by
    rw [Real.div_rpow hR.le (by norm_num), div_eq_mul_inv,
      ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8), mul_comm]
  exact hh.trans_eq hp

/-- Proposition 5.15, Step 1: the two sharper value powers
and the gradient power obtained by multiplying the source's parent norm. -/
theorem boundary_sharp_scaling_internal (s : Riesz1.RieszExponent)
    (R N A G F V Z Y Cv H : ℝ) (hR : 1 ≤ R) (hN : 1 ≤ N)
    (hRN : R / 8 ≤ N) (hNR : N ≤ R)
    (hA : 0 ≤ A) (hG : 0 ≤ G) (hF : 0 ≤ F) (_hV : 0 ≤ V)
    (hCv : 0 ≤ Cv) (hH : 0 ≤ H)
    (hv : R ^ (3 / 2 - s.val) * V ≤ G * F)
    (hz : Z ≤ A * V * Cv * Real.log (2 * N) *
      (N ^ (-(1 + s.val) / 2) + N ^ (s.val / 2 - 1)))
    (hy : Y ≤ A * V * H * N ^ (-(1 / 2 : ℝ))) :
    Z ≤ (Cv * (8 ^ ((1 + s.val) / 2) + 8 ^ (1 - s.val / 2))) * A * G * F *
      Real.log (2 * R) * (R ^ (s.val / 2 - 2) + R ^ (3 * s.val / 2 - 5 / 2)) ∧
    Y ≤ (H * 8 ^ (1 / 2 : ℝ)) * A * G * F * R ^ (s.val - 2) := by
  have hRp : 0 < R := by linarith
  have hNp : 0 < N := by linarith
  have hlN : 0 ≤ Real.log (2 * N) := Real.log_nonneg (by linarith)
  have hv' : V ≤ R ^ (-(3 / 2 - s.val)) * (G * F) := by
    have hh := mul_le_mul_of_nonneg_left hv
      (Real.rpow_nonneg hRp.le (-(3 / 2 - s.val)))
    rwa [← mul_assoc, ← Real.rpow_add hRp, neg_add_cancel, Real.rpow_zero, one_mul] at hh
  have hp := boundary_scale_power_internal R N (-(1 + s.val) / 2) hRp hNp hRN
    (by linarith [s.property.1])
  have hq := boundary_scale_power_internal R N (s.val / 2 - 1) hRp hNp hRN
    (by linarith [s.property.2])
  have hg := boundary_scale_power_internal R N (-(1 / 2 : ℝ)) hRp hNp hRN (by norm_num)
  simp only [neg_neg] at hg
  have hl : Real.log (2 * N) ≤ Real.log (2 * R) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlR : 0 ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
  have hsum : N ^ (-(1 + s.val) / 2) + N ^ (s.val / 2 - 1) ≤
      (8 ^ ((1 + s.val) / 2) + 8 ^ (1 - s.val / 2)) *
        (R ^ (-(1 + s.val) / 2) + R ^ (s.val / 2 - 1)) := by
    have h8p : -( -(1 + s.val) / 2) = (1 + s.val) / 2 := by ring
    have h8q : -(s.val / 2 - 1) = 1 - s.val / 2 := by ring
    rw [h8p] at hp
    rw [h8q] at hq
    have hcross1 := mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 8) ((1 + s.val) / 2))
      (Real.rpow_nonneg hRp.le (s.val / 2 - 1))
    have hcross2 := mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 8) (1 - s.val / 2))
      (Real.rpow_nonneg hRp.le (-(1 + s.val) / 2))
    nlinarith only [hp, hq, hcross1, hcross2]
  have hpa : R ^ (-(3 / 2 - s.val)) * R ^ (-(1 + s.val) / 2) = R ^ (s.val / 2 - 2) := by
    rw [← Real.rpow_add hRp]; congr 1; ring
  have hpb : R ^ (-(3 / 2 - s.val)) * R ^ (s.val / 2 - 1) = R ^ (3 * s.val / 2 - 5 / 2) := by
    rw [← Real.rpow_add hRp]; congr 1; ring
  constructor
  · apply hz.trans
    calc
      _ ≤ A * (R ^ (-(3 / 2 - s.val)) * (G * F)) * Cv * Real.log (2 * R) *
          ((8 ^ ((1 + s.val) / 2) + 8 ^ (1 - s.val / 2)) *
            (R ^ (-(1 + s.val) / 2) + R ^ (s.val / 2 - 1))) := by
        apply mul_le_mul _ hsum (by positivity) (by positivity)
        apply mul_le_mul _ hl (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv' hA) hCv
      _ = _ := by
        linear_combination
          (Cv * A * G * F * Real.log (2 * R) *
            (8 ^ ((1 + s.val) / 2) + 8 ^ (1 - s.val / 2))) * hpa +
          (Cv * A * G * F * Real.log (2 * R) *
            (8 ^ ((1 + s.val) / 2) + 8 ^ (1 - s.val / 2))) * hpb
  · apply hy.trans
    calc
      _ ≤ A * (R ^ (-(3 / 2 - s.val)) * (G * F)) * H *
          (8 ^ (1 / 2 : ℝ) * R ^ (-(1 / 2 : ℝ))) := by gcongr
      _ = _ := by
        have he : R ^ (-(3 / 2 - s.val)) * R ^ (-(1 / 2 : ℝ)) = R ^ (s.val - 2) := by
          rw [← Real.rpow_add hRp]; congr 1; ring
        calc
          _ = (H * 8 ^ (1 / 2 : ℝ)) * A * G * F *
            (R ^ (-(3 / 2 - s.val)) * R ^ (-(1 / 2 : ℝ))) := by ring
          _ = _ := by rw [he]

/-- Proposition 5.15, equation (5.64): each of the
strictly positive value gaps absorbs its logarithm. The gradient gap is
positive as well. -/
theorem boundary_sharp_to_target_internal (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R B Z Y : ℝ), 1 ≤ R → 0 ≤ B →
      Z ≤ B * Real.log (2 * R) *
        (R ^ (s.val / 2 - 2) + R ^ (3 * s.val / 2 - 5 / 2)) →
      Y ≤ B * R ^ (s.val - 2) →
      R ^ (2 - s.val) * Z + R ^ ((3 - s.val) / 2) * Y ≤ C * B := by
  let q := min (s.val / 2) ((1 - s.val) / 2)
  have hq : 0 < q := lt_min (by linarith [s.property.1]) (by linarith [s.property.2])
  let L := Real.log 2 + 1 / q
  have hL : 0 < L := by dsimp [L]; have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  refine ⟨2 * L + 1, by positivity, ?_⟩
  intro R B Z Y hR hB hZ hY
  have hRp : 0 < R := by linarith
  have hl : Real.log (2 * R) * R ^ (-q) ≤ L := by
    have hlog := Real.log_le_rpow_div hRp.le hq
    have hp := Real.rpow_le_rpow_of_exponent_le hR (neg_nonpos.mpr hq.le)
    rw [Real.rpow_zero] at hp
    have hh := mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg hRp.le (-q))
    have he : R ^ q / q * R ^ (-q) = 1 / q := by
      rw [div_mul_eq_mul_div, ← Real.rpow_add hRp, add_neg_cancel, Real.rpow_zero]
    rw [he] at hh
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hRp.ne']
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    dsimp only [L]
    nlinarith only [hh, mul_le_mul_of_nonneg_left hp hlog2]
  have hsmall (e : ℝ) (he : e ≤ -q) : Real.log (2 * R) * R ^ e ≤ L :=
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hR he)
      (Real.log_nonneg (by linarith))).trans hl
  have hp := hsmall (-s.val / 2) (by dsimp only [q]; linarith only [min_le_left (s.val / 2) ((1 - s.val) / 2)])
  have hq' := hsmall (-(1 - s.val) / 2) (by dsimp only [q]; linarith only [min_le_right (s.val / 2) ((1 - s.val) / 2)])
  have hg : R ^ ((s.val - 1) / 2) ≤ 1 := by
    apply (Real.rpow_le_rpow_of_exponent_le hR (by linarith [s.property.2] : (s.val - 1) / 2 ≤ 0)).trans_eq
    exact Real.rpow_zero _
  have hval : R ^ (2 - s.val) * Z ≤ 2 * L * B := by
    have hh := mul_le_mul_of_nonneg_left hZ (Real.rpow_nonneg hRp.le (2 - s.val))
    have he : R ^ (2 - s.val) *
        (B * Real.log (2 * R) * (R ^ (s.val / 2 - 2) + R ^ (3 * s.val / 2 - 5 / 2))) =
        B * (Real.log (2 * R) * R ^ (-s.val / 2) +
          Real.log (2 * R) * R ^ (-(1 - s.val) / 2)) := by
      have he1 : R ^ (2 - s.val) * R ^ (s.val / 2 - 2) = R ^ (-s.val / 2) := by
        rw [← Real.rpow_add hRp]; congr 1; ring
      have he2 : R ^ (2 - s.val) * R ^ (3 * s.val / 2 - 5 / 2) = R ^ (-(1 - s.val) / 2) := by
        rw [← Real.rpow_add hRp]; congr 1; ring
      linear_combination (B * Real.log (2 * R)) * he1 + (B * Real.log (2 * R)) * he2
    rw [he] at hh
    nlinarith only [hh, mul_le_mul_of_nonneg_left hp hB, mul_le_mul_of_nonneg_left hq' hB]
  have hgrad : R ^ ((3 - s.val) / 2) * Y ≤ B := by
    have hh := mul_le_mul_of_nonneg_left hY (Real.rpow_nonneg hRp.le ((3 - s.val) / 2))
    have he : R ^ ((3 - s.val) / 2) * (B * R ^ (s.val - 2)) = B * R ^ ((s.val - 1) / 2) := by
      rw [mul_left_comm, ← Real.rpow_add hRp]; congr 1; congr 1; ring
    rw [he] at hh
    exact hh.trans ((mul_le_mul_of_nonneg_left hg hB).trans_eq (mul_one B))
  linarith only [hval, hgrad]

/-- Proposition 5.15, equation (5.64): assemble
the two sharp displays before weakening to the final weighted estimate. -/
theorem boundary_decay_scaling_sharp_internal (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R N A G F V Z Y Cv H : ℝ),
      1 ≤ R → 1 ≤ N → R / 8 ≤ N → N ≤ R →
      0 ≤ A → 0 ≤ G → 0 ≤ F → 0 ≤ V → 0 ≤ Cv → 0 ≤ H →
      R ^ (3 / 2 - s.val) * V ≤ G * F →
      Z ≤ A * V * Cv * Real.log (2 * N) *
        (N ^ (-(1 + s.val) / 2) + N ^ (s.val / 2 - 1)) →
      Y ≤ A * V * H * N ^ (-(1 / 2 : ℝ)) →
      R ^ (2 - s.val) * Z + R ^ ((3 - s.val) / 2) * Y ≤
        C * (Cv * (8 ^ ((1 + s.val) / 2) + 8 ^ (1 - s.val / 2)) +
          H * 8 ^ (1 / 2 : ℝ)) * A * G * F := by
  obtain ⟨C, hC, ht⟩ := boundary_sharp_to_target_internal s
  refine ⟨C, hC, ?_⟩
  intro R N A G F V Z Y Cv H hR hN hRN hNR hA hG hF hV hCv hH hv hz hy
  obtain ⟨hZ, hY⟩ := boundary_sharp_scaling_internal s R N A G F V Z Y Cv H
    hR hN hRN hNR hA hG hF hV hCv hH hv hz hy
  let L := Cv * (8 ^ ((1 + s.val) / 2) + 8 ^ (1 - s.val / 2)) + H * 8 ^ (1 / 2 : ℝ)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hlR : 0 ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
  have hZ' : Z ≤ (L * A * G * F) * Real.log (2 * R) *
      (R ^ (s.val / 2 - 2) + R ^ (3 * s.val / 2 - 5 / 2)) := by
    apply hZ.trans
    have hc : Cv * (8 ^ ((1 + s.val) / 2) + 8 ^ (1 - s.val / 2)) ≤ L :=
      le_add_of_nonneg_right (mul_nonneg hH (Real.rpow_nonneg (by norm_num) _))
    gcongr
  have hY' : Y ≤ (L * A * G * F) * R ^ (s.val - 2) := by
    apply hY.trans
    have hc : H * 8 ^ (1 / 2 : ℝ) ≤ L :=
      le_add_of_nonneg_left (mul_nonneg hCv (by positivity))
    gcongr
  exact (ht R (L * A * G * F) Z Y hR (by positivity) hZ' hY').trans_eq (by dsimp [L]; ring)

end Riesz2.LocalizedBoundary
