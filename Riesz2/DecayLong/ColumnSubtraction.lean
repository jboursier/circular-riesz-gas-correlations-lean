/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.L2Space
public import Riesz2.DecayLong.GlobalSums
public import Riesz1.Frozen.RieszExponent

/-!
# General column subtraction

The arbitrary probability-space operator in Lemma 5.17 of
the paper. Vector fields are actual `Lp` equivalence classes with the
Euclidean norm on their values. No continuity of the operator is assumed.
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace Riesz2.ColumnSubtraction

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} {n : ℕ}

/-- Coordinate projection for the fields in Lemma 5.17. -/
def coordinate (p : ℝ≥0∞) (i : Fin n) :
    Lp (EuclideanSpace ℝ (Fin n)) p ν →ₗ[ℝ] Lp ℝ p ν :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).compLpₗ p ν

/-- The field `φ eᵢ` in Lemma 5.17. -/
def injection (p : ℝ≥0∞) (i : Fin n) :
    Lp ℝ p ν →ₗ[ℝ] Lp (EuclideanSpace ℝ (Fin n)) p ν :=
  (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i 1)).compLpₗ p ν

/-- The coordinate sum `1_I · v` in Lemma 5.17. -/
def coordinateSum (p : ℝ≥0∞) :
    Lp (EuclideanSpace ℝ (Fin n)) p ν →ₗ[ℝ] Lp ℝ p ν :=
  ∑ i, coordinate p i

/-- The coordinate interpretation of Lemma 5.17. -/
theorem coordinate_ae (p : ℝ≥0∞) (i : Fin n)
    (v : Lp (EuclideanSpace ℝ (Fin n)) p ν) :
    coordinate p i v =ᵐ[ν] fun x => v x i := by
  unfold coordinate
  filter_upwards [(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).coeFn_compLp v] with x hx
  exact hx

/-- The source-column interpretation of Lemma 5.17. -/
theorem injection_ae (p : ℝ≥0∞) (i : Fin n) (φ : Lp ℝ p ν) :
    injection p i φ =ᵐ[ν] fun x => φ x • EuclideanSpace.single i 1 :=
  (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single i 1)).coeFn_compLp φ

/-- Expansion into source columns, used in equation (5.74) of
Lemma 5.17. -/
theorem sum_injection_coordinate (p : ℝ≥0∞)
    (v : Lp (EuclideanSpace ℝ (Fin n)) p ν) :
    (∑ k, injection p k (coordinate p k v)) = v := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      (fun k => injection p k (coordinate p k v)),
    ae_all_iff.mpr (fun k => injection_ae p k (coordinate p k v)),
    ae_all_iff.mpr (fun k => coordinate_ae p k v)] with x hsum hinj hcoord
  rw [hsum]
  apply PiLp.ext
  intro i
  simp [hinj, hcoord, Pi.single_apply, mul_ite]

/-- The vector identity equation (5.74) in the proof of
Lemma 5.17, in the operator's actual output space. -/
theorem column_subtraction_identity
    (M : Lp (EuclideanSpace ℝ (Fin n)) ∞ ν →ₗ[ℝ]
      Lp (EuclideanSpace ℝ (Fin n)) 1 ν)
    (v : Lp (EuclideanSpace ℝ (Fin n)) ∞ ν) (i₀ : Fin n) :
    M v = (∑ k, M (injection ∞ k (coordinate ∞ k v) -
      injection ∞ i₀ (coordinate ∞ k v))) +
        M (injection ∞ i₀ (coordinateSum ∞ v)) := by
  rw [← map_sum, Finset.sum_sub_distrib, ← map_sum]
  have hs : (∑ k, coordinate ∞ k v) = coordinateSum ∞ v := by
    simp [coordinateSum, LinearMap.sum_apply]
  rw [sum_injection_coordinate, hs, map_sub]
  abel

/-- Ordinary index distance in the auxiliary double interval used for the
finite profile sums of Lemma 5.17. -/
theorem active_distance_internal (N n : ℕ+) (hn : 2*(n : ℕ) ≤ (N : ℕ))
    (i j : Fin (n : ℕ)) :
    Riesz1.cyclicIndexDistance N (i.castLE (by omega)) (j.castLE (by omega)) =
      Nat.dist i.val j.val := by
  simp only [Riesz1.cyclicIndexDistance, Fin.val_castLE]
  have hi := i.isLt
  have hj := j.isLt
  unfold Nat.dist
  omega

/-- The subcritical depth-power sum in Lemma 5.17. -/
theorem boundary_weight_sum_internal (n : ℕ+) (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    (∑ i : Fin (n : ℕ),
      ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-t)) ≤
      2 / (1 - t) * (n : ℝ) ^ (1 - t) := by
  have hmin (i : Fin (n : ℕ)) :
      ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-t) ≤
        (1 + (i.val : ℝ)) ^ (-t) + (1 + (i.rev.val : ℝ)) ^ (-t) := by
    have hrev : (1 + (i.rev.val : ℝ)) = ((n : ℕ) - i.val : ℕ) := by
      have hi := i.isLt
      have he : 1 + i.rev.val = (n : ℕ) - i.val := by simp only [Fin.val_rev]; omega
      exact_mod_cast he
    rw [hrev]
    rcases le_total (i.val + 1) ((n : ℕ) - i.val) with h | h
    · rw [min_eq_left h]
      have he : ((i.val + 1 : ℕ) : ℝ) = 1 + (i.val : ℝ) := by push_cast; ring
      rw [he]
      exact le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _)
    · rw [min_eq_right h]
      exact le_add_of_nonneg_left (Real.rpow_nonneg (by positivity) _)
  have hr : (∑ i : Fin (n : ℕ), (1 + (i.rev.val : ℝ)) ^ (-t)) =
      ∑ i : Fin (n : ℕ), (1 + (i.val : ℝ)) ^ (-t) :=
    Equiv.sum_comp Fin.revPerm (fun i : Fin (n : ℕ) => (1 + (i.val : ℝ)) ^ (-t))
  have hb : (∑ i : Fin (n : ℕ), (1 + (i.val : ℝ)) ^ (-t)) ≤
      (n : ℝ) ^ (1 - t) / (1 - t) := by
    have hh := sum_range_one_add_rpow_le_of_lt_one ht ht1 n.pos
    simpa only [← Fin.sum_univ_eq_sum_range] using hh
  calc
    _ ≤ ∑ i : Fin (n : ℕ), ((1 + (i.val : ℝ)) ^ (-t) +
        (1 + (i.rev.val : ℝ)) ^ (-t)) := Finset.sum_le_sum (fun i _ => hmin i)
    _ = 2 * ∑ i : Fin (n : ℕ), (1 + (i.val : ℝ)) ^ (-t) := by
      rw [Finset.sum_add_distrib, hr]; ring
    _ ≤ 2 * ((n : ℝ) ^ (1 - t) / (1 - t)) := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by ring

/-- Lemma 5.17 of the paper: the cyclic weight sum over an
embedded half-cycle interval has the usual subcritical bound. -/
theorem active_weight_sum_internal (n m : ℕ+) (hn : 2 * (n : ℕ) ≤ (m : ℕ))
    (j : Fin (n : ℕ)) (b : ℝ) (hb : 0 < b) (hb1 : b < 1) :
    (∑ i : Fin (n : ℕ),
      weightRadius m (j.castLE (by omega)) (i.castLE (by omega)) ^ (-b)) ≤
        2 / (1 - b) * (n : ℝ) ^ (1 - b) := by
  let e : Fin (n : ℕ) ↪ Fin (m : ℕ) := ⟨Fin.castLE (by omega), Fin.castLE_injective _⟩
  let c := j.castLE (by omega : (n : ℕ) ≤ (m : ℕ))
  have hs : Finset.univ.map e ⊆ Finset.univ.filter (fun i => weightRadius m i c ≤ (n : ℝ)) := by
    intro i hi
    obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    change 1 + (Riesz1.cyclicIndexDistance m (k.castLE (by omega)) (j.castLE (by omega)) : ℝ) ≤ _
    rw [active_distance_internal m n hn]
    have hdist : 1 + Nat.dist k.val j.val ≤ (n : ℕ) := by
      have := k.isLt
      have := j.isLt
      unfold Nat.dist
      omega
    exact_mod_cast hdist
  have hh := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun i => weightRadius m i c ^ (-b)) hs
    (fun i _ _ => Real.rpow_nonneg (by linarith [one_le_weightRadius m i c]) (-b))
  have hbound := sum_weightRadius_le_of_lt_one m c hb hb1
    (show (1 : ℝ) ≤ n by exact_mod_cast n.pos)
  have he : (∑ i ∈ Finset.univ.map e, weightRadius m i c ^ (-b)) =
      ∑ i : Fin (n : ℕ), weightRadius m (j.castLE (by omega)) (i.castLE (by omega)) ^ (-b) := by
    simp only [Finset.sum_map, e, c, Function.Embedding.coeFn_mk, weightRadius,
      cyclicIndexDistance_comm']
  rw [he] at hh
  exact hh.trans hbound

/-- The first moment of the written value profile in
Lemma 5.17 costs n^s. -/
theorem first_moment_profile_internal (s : Riesz1.RieszExponent)
    (n m : ℕ+) (hnm : 2 * (n : ℕ) ≤ (m : ℕ)) (i₀ : Fin (n : ℕ)) :
    (∑ k : Fin (n : ℕ), (Nat.dist k.val i₀.val : ℝ) *
      (1 + (Nat.dist k.val i₀.val : ℝ)) ^ (-(2 - s.val))) ≤
      (2 / s.val) * (n : ℝ) ^ s.val := by
  have hp (k : Fin (n : ℕ)) :
      (Nat.dist k.val i₀.val : ℝ) * (1 + (Nat.dist k.val i₀.val : ℝ)) ^ (-(2-s.val)) ≤
        (1 + (Nat.dist k.val i₀.val : ℝ)) ^ (-(1-s.val)) := by
    have hr : (0 : ℝ) < 1 + (Nat.dist k.val i₀.val : ℝ) := by positivity
    calc
      _ ≤ (1 + (Nat.dist k.val i₀.val : ℝ)) *
          (1 + (Nat.dist k.val i₀.val : ℝ)) ^ (-(2-s.val)) := by gcongr; linarith
      _ = _ := by
        rw [show -(1-s.val) = 1 + (-(2-s.val)) by ring, Real.rpow_add hr, Real.rpow_one]
  calc
    _ ≤ ∑ k : Fin (n : ℕ), (1 + (Nat.dist k.val i₀.val : ℝ)) ^ (-(1-s.val)) :=
      Finset.sum_le_sum (fun k _ => hp k)
    _ = ∑ k : Fin (n : ℕ),
        weightRadius m (i₀.castLE (by omega)) (k.castLE (by omega)) ^ (-(1-s.val)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [weightRadius, active_distance_internal m n hnm, Nat.dist_comm]
    _ ≤ _ := by
      have hh := active_weight_sum_internal n m hnm i₀ (1-s.val)
        (by linarith [s.property.2]) (by linarith [s.property.1])
      have he : 1 - (1-s.val) = s.val := by ring
      simpa only [he] using hh

/-- The depth-only boundary separation in Lemma 5.17.
This includes the reflected endpoint allowed by the paper. -/
theorem boundary_separation_internal (n : ℕ+) (i₀ k : Fin (n : ℕ))
    (hdepth : (n : ℝ) / 4 ≤
      ((min (i₀.val + 1) ((n : ℕ) - i₀.val) : ℕ) : ℝ))
    (hk : ((min (k.val + 1) ((n : ℕ) - k.val) : ℕ) : ℝ) ≤ (n : ℝ) / 8) :
    (n : ℝ) / 8 ≤ (Nat.dist k.val i₀.val : ℝ) := by
  have hkn := k.isLt
  have hin := i₀.isLt
  rw [Nat.cast_min, Nat.cast_add, Nat.cast_one, Nat.cast_sub (by omega)] at hdepth
  have hlo := hdepth.trans (min_le_left _ _)
  have hhi := hdepth.trans (min_le_right _ _)
  rw [Nat.cast_min, Nat.cast_add, Nat.cast_one, Nat.cast_sub (by omega)] at hk
  have hd : (Nat.dist k.val i₀.val : ℝ) = |(k.val : ℝ) - (i₀.val : ℝ)| := by
    rcases le_total k.val i₀.val with h | h
    · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h, abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h))]; ring
    · rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]
  rw [hd]
  rcases le_total ((k.val : ℝ) + 1) ((n : ℝ) - k.val) with h | h
  · rw [min_eq_left h] at hk
    have hh : (n : ℝ) / 8 ≤ -((k.val : ℝ) - i₀.val) := by linarith
    exact hh.trans (neg_le_abs _)
  · rw [min_eq_right h] at hk
    exact (by linarith : (n : ℝ) / 8 ≤ (k.val : ℝ) - i₀.val).trans (le_abs_self _)


/-- The boundary source sum in Lemma 5.17 of the paper. -/
theorem boundary_source_sum_internal (s : Riesz1.RieszExponent) (n : ℕ+)
    (i₀ : Fin (n : ℕ))
    (hdepth : (n : ℝ) / 4 ≤
      ((min (i₀.val + 1) ((n : ℕ) - i₀.val) : ℕ) : ℝ))
    (a : Fin (n : ℕ) → ℝ) (D F : ℝ) (hD : 0 ≤ D) (hF : 0 ≤ F)
    (ha : ∀ k, a k ≤ D * F * (1 + (Nat.dist k.val i₀.val : ℝ)) ^ (-(2-s.val))) :
    let d := fun k : Fin (n : ℕ) => ((min (k.val + 1) ((n : ℕ) - k.val) : ℕ) : ℝ)
    let B := Finset.univ.filter (fun k : Fin (n : ℕ) => d k ≤ (n : ℝ) / 8)
    (∑ k ∈ B, ((d k) ^ (-s.val/2) + (d i₀) ^ (-s.val/2)) * a k) ≤
      (2 * 8 ^ (2-s.val) * (2 / (1-s.val/2))) * D * F *
        (n : ℝ) ^ (-1+s.val/2) := by
  intro d B
  have hn : (0 : ℝ) < n := by exact_mod_cast n.pos
  have ht : -(2-s.val) ≤ 0 := by linarith [s.property.2]
  have hscale : ((n : ℝ)/8) ^ (-(2-s.val)) =
      8 ^ (2-s.val) * (n : ℝ) ^ (-(2-s.val)) := by
    rw [Real.div_rpow hn.le (by norm_num : (0 : ℝ) ≤ 8), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8)]
    simp only [div_inv_eq_mul, mul_comm]
  have hb (k) (hk : k ∈ B) :
      ((d k) ^ (-s.val/2) + (d i₀) ^ (-s.val/2)) * a k ≤
        2 * (d k) ^ (-s.val/2) * (D * F *
          (8 ^ (2-s.val) * (n : ℝ) ^ (-(2-s.val)))) := by
    have hk' := (Finset.mem_filter.mp hk).2
    have hsep := boundary_separation_internal n i₀ k hdepth hk'
    have hd : d k ≤ d i₀ := by dsimp only [d] at *; linarith
    have hdpos : 0 < d k := by
      have hh := k.isLt
      dsimp only [d]; exact_mod_cast (by omega : 0 < min (k.val+1) ((n : ℕ)-k.val))
    have hdw : (d i₀) ^ (-s.val/2) ≤ (d k) ^ (-s.val/2) :=
      Real.rpow_le_rpow_of_nonpos hdpos hd (by linarith [s.property.1])
    have hv := (ha k).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < (n : ℝ)/8)
        (by linarith : (n : ℝ)/8 ≤ 1 + (Nat.dist k.val i₀.val : ℝ)) ht)
        (mul_nonneg hD hF))
    rw [hscale] at hv
    calc
      _ ≤ ((d k) ^ (-s.val/2) + (d i₀) ^ (-s.val/2)) *
          (D * F * (8 ^ (2-s.val) * (n : ℝ) ^ (-(2-s.val)))) :=
        mul_le_mul_of_nonneg_left hv (by dsimp [d]; positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hs : (∑ k ∈ B, (d k) ^ (-s.val/2)) ≤
      (2 / (1-s.val/2)) * (n : ℝ) ^ (1-s.val/2) := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => by dsimp [d]; positivity)).trans
    have hh := boundary_weight_sum_internal n (s.val/2)
      (by linarith [s.property.1]) (by linarith [s.property.2])
    simpa only [neg_div] using hh
  calc
    _ ≤ ∑ k ∈ B, 2 * (d k) ^ (-s.val/2) *
        (D * F * (8 ^ (2-s.val) * (n : ℝ) ^ (-(2-s.val)))) := Finset.sum_le_sum hb
    _ = (2 * D * F * 8 ^ (2-s.val) * (n : ℝ) ^ (-(2-s.val))) *
        (∑ k ∈ B, (d k) ^ (-s.val/2)) := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
    _ ≤ (2 * D * F * 8 ^ (2-s.val) * (n : ℝ) ^ (-(2-s.val))) *
        ((2 / (1-s.val/2)) * (n : ℝ) ^ (1-s.val/2)) := by gcongr
    _ = _ := by
      have he : (n : ℝ) ^ (-(2-s.val)) * (n : ℝ) ^ (1-s.val/2) =
          (n : ℝ) ^ (-1+s.val/2) := by rw [← Real.rpow_add hn]; congr 1; ring
      calc
        _ = (2 * 8 ^ (2-s.val) * (2 / (1-s.val/2))) * D * F *
            ((n : ℝ) ^ (-(2-s.val)) * (n : ℝ) ^ (1-s.val/2)) := by ring
        _ = _ := by rw [he]

/-- Lemma 5.17 of the paper: the bulk column increments use
the first moment of the value profile, rather than the sum of entries. -/
theorem bulk_source_sum_internal (s : Riesz1.RieszExponent)
    (n m : ℕ+) (hnm : 2 * (n : ℕ) ≤ (m : ℕ)) (i₀ : Fin (n : ℕ))
    (hdepth : (n : ℝ) / 4 ≤
      ((min (i₀.val + 1) ((n : ℕ) - i₀.val) : ℕ) : ℝ))
    (a : Fin (n : ℕ) → ℝ) (D F : ℝ) (hD : 0 ≤ D) (hF : 0 ≤ F)
    (ha : ∀ k, a k ≤ D * F * (1 + (Nat.dist k.val i₀.val : ℝ)) ^ (-(2-s.val))) :
    let d := fun k : Fin (n : ℕ) => ((min (k.val + 1) ((n : ℕ) - k.val) : ℕ) : ℝ)
    let U := Finset.univ.filter (fun k : Fin (n : ℕ) => (n : ℝ) / 8 < d k)
    (∑ k ∈ U, (Nat.dist k.val i₀.val : ℝ) *
      (min (d k) (d i₀)) ^ (-1-s.val/2) * a k) ≤
      (8 ^ (1+s.val/2) * (2 / s.val)) * D * F * (n : ℝ) ^ (-1+s.val/2) := by
  intro d U
  have hn : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hscale : ((n : ℝ)/8) ^ (-1-s.val/2) =
      8 ^ (1+s.val/2) * (n : ℝ) ^ (-1-s.val/2) := by
    rw [Real.div_rpow hn.le (by norm_num : (0 : ℝ) ≤ 8),
      show -1-s.val/2 = -(1+s.val/2) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8)]
    simp only [div_inv_eq_mul, mul_comm]
  have hb (k) (hk : k ∈ U) :
      (Nat.dist k.val i₀.val : ℝ) * (min (d k) (d i₀)) ^ (-1-s.val/2) * a k ≤
        (8 ^ (1+s.val/2) * (n : ℝ) ^ (-1-s.val/2) * D * F) *
          ((Nat.dist k.val i₀.val : ℝ) * (1 + (Nat.dist k.val i₀.val : ℝ)) ^ (-(2-s.val))) := by
    have hk' := (Finset.mem_filter.mp hk).2
    have hmin : (n : ℝ)/8 ≤ min (d k) (d i₀) := by
      exact le_min hk'.le (by dsimp only [d] at *; linarith)
    have hp := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < (n : ℝ)/8)
      hmin (by linarith [s.property.1] : -1-s.val/2 ≤ 0)
    rw [hscale] at hp
    calc
      _ ≤ (Nat.dist k.val i₀.val : ℝ) * (min (d k) (d i₀)) ^ (-1-s.val/2) *
          (D * F * (1 + (Nat.dist k.val i₀.val : ℝ)) ^ (-(2-s.val))) :=
        mul_le_mul_of_nonneg_left (ha k) (by dsimp [d]; positivity)
      _ ≤ (Nat.dist k.val i₀.val : ℝ) *
          (8 ^ (1+s.val/2) * (n : ℝ) ^ (-1-s.val/2)) *
          (D * F * (1 + (Nat.dist k.val i₀.val : ℝ)) ^ (-(2-s.val))) := by gcongr
      _ = _ := by ring
  have hs : (∑ k ∈ U, (Nat.dist k.val i₀.val : ℝ) *
      (1 + (Nat.dist k.val i₀.val : ℝ)) ^ (-(2-s.val))) ≤ (2/s.val) * (n : ℝ) ^ s.val := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => by positivity)).trans
    exact first_moment_profile_internal s n m hnm i₀
  calc
    _ ≤ ∑ k ∈ U, (8 ^ (1+s.val/2) * (n : ℝ) ^ (-1-s.val/2) * D * F) *
        ((Nat.dist k.val i₀.val : ℝ) * (1 + (Nat.dist k.val i₀.val : ℝ)) ^ (-(2-s.val))) :=
      Finset.sum_le_sum hb
    _ = (8 ^ (1+s.val/2) * (n : ℝ) ^ (-1-s.val/2) * D * F) *
        (∑ k ∈ U, (Nat.dist k.val i₀.val : ℝ) *
          (1 + (Nat.dist k.val i₀.val : ℝ)) ^ (-(2-s.val))) := (Finset.mul_sum _ _ _).symm
    _ ≤ (8 ^ (1+s.val/2) * (n : ℝ) ^ (-1-s.val/2) * D * F) *
        ((2/s.val) * (n : ℝ) ^ s.val) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by
      have he : (n : ℝ) ^ (-1-s.val/2) * (n : ℝ) ^ s.val =
          (n : ℝ) ^ (-1+s.val/2) := by rw [← Real.rpow_add hn]; congr 1; ring
      calc
        _ = (8 ^ (1+s.val/2) * (2/s.val)) * D * F *
            ((n : ℝ) ^ (-1-s.val/2) * (n : ℝ) ^ s.val) := by ring
        _ = _ := by rw [he]

/-- Lemma 5.17 of the paper: the remaining source column
uses the interior mean bound with its full power `n^{-(1-s)}`. -/
theorem mean_source_column_internal (s : Riesz1.RieszExponent)
    (n : ℕ+) (i₀ : Fin (n : ℕ))
    (hdepth : (n : ℝ) / 4 ≤
      ((min (i₀.val + 1) ((n : ℕ) - i₀.val) : ℕ) : ℝ))
    (aS D F : ℝ) (hD : 0 ≤ D) (hF : 0 ≤ F)
    (hS : aS ≤ D * (n : ℝ) ^ (-(1-s.val)) * F) :
    ((min (i₀.val + 1) ((n : ℕ) - i₀.val) : ℕ) : ℝ) ^ (-s.val/2) * aS ≤
      4 ^ (s.val/2) * D * F * (n : ℝ) ^ (-1+s.val/2) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hp := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < (n : ℝ)/4)
    hdepth (by linarith [s.property.1] : -s.val/2 ≤ 0)
  have he : ((n : ℝ)/4) ^ (-s.val/2) = 4 ^ (s.val/2) * (n : ℝ) ^ (-s.val/2) := by
    rw [Real.div_rpow hn.le (by norm_num : (0 : ℝ) ≤ 4), neg_div,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
    simp only [div_inv_eq_mul, mul_comm]
  rw [he] at hp
  calc
    _ ≤ ((min (i₀.val + 1) ((n : ℕ) - i₀.val) : ℕ) : ℝ) ^ (-s.val/2) *
        (D * (n : ℝ) ^ (-(1-s.val)) * F) := mul_le_mul_of_nonneg_left hS (by positivity)
    _ ≤ (4 ^ (s.val/2) * (n : ℝ) ^ (-s.val/2)) *
        (D * (n : ℝ) ^ (-(1-s.val)) * F) := mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by
      have hpow : (n : ℝ) ^ (-s.val/2) * (n : ℝ) ^ (-(1-s.val)) =
          (n : ℝ) ^ (-1+s.val/2) := by rw [← Real.rpow_add hn]; congr 1; ring
      calc
        _ = 4 ^ (s.val/2) * D * F * ((n : ℝ) ^ (-s.val/2) * (n : ℝ) ^ (-(1-s.val))) := by ring
        _ = _ := by rw [hpow]



/-- The actual bounded/integrable pairing of Lemma 5.17. -/
def pairing : Lp (EuclideanSpace ℝ (Fin n)) ∞ ν →L[ℝ]
    Lp (EuclideanSpace ℝ (Fin n)) 1 ν →L[ℝ] ℝ :=
  (innerSL ℝ).lpPairing ν ∞ 1

/-- The expectation interpretation in Lemma 5.17. -/
theorem pairing_eq_integral
    (u : Lp (EuclideanSpace ℝ (Fin n)) ∞ ν)
    (w : Lp (EuclideanSpace ℝ (Fin n)) 1 ν) :
    pairing u w = ∫ x, inner ℝ (u x) (w x) ∂ν :=
  ContinuousLinearMap.lpPairing_eq_integral (innerSL ℝ) u w

/-- Bounded tests against integrable outputs in
Lemma 5.17 always have an integrable dot product. -/
theorem pairing_integrable
    (u : Lp (EuclideanSpace ℝ (Fin n)) ∞ ν)
    (w : Lp (EuclideanSpace ℝ (Fin n)) 1 ν) :
    Integrable (fun x => inner ℝ (u x) (w x)) ν :=
  memLp_one_iff_integrable.mp
    ((innerSL ℝ).memLp_of_bilin 1 (Lp.memLp u) (Lp.memLp w))

/-- Coordinate projections contract the essential supremum in
Lemma 5.17. -/
theorem coordinate_norm_le (p : ℝ≥0∞) (i : Fin n)
    (v : Lp (EuclideanSpace ℝ (Fin n)) p ν) :
    ‖coordinate p i v‖ ≤ ‖v‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [coordinate_ae p i v] with x hx
  rw [hx]
  exact PiLp.norm_apply_le (v x) i

/-- The sum field in Lemma 5.17 is the sum of
its coordinates, including at the level of representatives. -/
theorem coordinateSum_ae (p : ℝ≥0∞)
    (v : Lp (EuclideanSpace ℝ (Fin n)) p ν) :
    coordinateSum p v =ᵐ[ν] fun x => ∑ i, v x i := by
  have he : coordinateSum p v = ∑ i, coordinate p i v := by
    simp [coordinateSum, LinearMap.sum_apply]
  rw [he]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => coordinate p i v),
    ae_all_iff.mpr (fun i => coordinate_ae p i v)] with x hx hi
  simp only [hx, hi]

/-- The `√n` bound on `1_I · v` used in Lemma 5.17. -/
theorem coordinateSum_norm_le (p : ℝ≥0∞)
    (v : Lp (EuclideanSpace ℝ (Fin n)) p ν) :
    ‖coordinateSum p v‖ ≤ Real.sqrt n * ‖v‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coordinateSum_ae p v] with x hx
  rw [hx]
  let e : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun _ => 1)
  have he : ‖e‖ = Real.sqrt n := by simp [e, EuclideanSpace.norm_eq]
  have hi : inner ℝ e (v x) = ∑ i, v x i := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, e]
  rw [← hi, Real.norm_eq_abs]
  simpa only [he] using abs_real_inner_le_norm e (v x)

/-- `L²` representatives of the bounded fields of
Lemma 5.17, on a finite measure space. -/
def toL2 {E : Type*} [NormedAddCommGroup E] [IsFiniteMeasure ν]
    (v : Lp E ∞ ν) : Lp E 2 ν :=
  ((Lp.memLp v).mono_exponent (by simp : (2 : ℝ≥0∞) ≤ ∞)).toLp v

/-- The inclusion in `L²` in Lemma 5.17 preserves
representatives almost everywhere. -/
theorem toL2_ae {E : Type*} [NormedAddCommGroup E] [IsFiniteMeasure ν]
    (v : Lp E ∞ ν) : toL2 v =ᵐ[ν] v := MemLp.coeFn_toLp _

/-- The `L²` norm of the test field in Lemma 5.17 is
exactly the square sum of the coordinate `L²` norms. -/
theorem sum_coordinate_norm_sq [IsFiniteMeasure ν]
    (v : Lp (EuclideanSpace ℝ (Fin n)) ∞ ν) :
    (∑ i, ‖toL2 (coordinate ∞ i v)‖ ^ 2) = ‖toL2 v‖ ^ 2 := by
  have hcoord (i : Fin n) : coordinate 2 i (toL2 v) =
      toL2 (coordinate ∞ i v) := by
    apply Lp.ext
    filter_upwards [coordinate_ae 2 i (toL2 v), toL2_ae v,
      toL2_ae (coordinate ∞ i v), coordinate_ae ∞ i v] with x h₁ h₂ h₃ h₄
    simp only [h₁, h₂, h₃, h₄]
  simp_rw [← hcoord, ← real_inner_self_eq_norm_sq, L2.inner_def]
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr (fun i => coordinate_ae 2 i (toL2 v))] with x hx
    simp only [hx, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
      star_trivial, Pi.star_apply, RCLike.inner_apply, conj_trivial]
  · intro i _
    exact L2.integrable_inner _ _

end Riesz2.ColumnSubtraction
