/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.PerturbationBoundsPart3
public import Riesz2.DecayLong.LocalizedBoundaryPart7
public import Riesz2.HelfferSjostrand.MaximumPrinciple

/-!
# Column cancellation in the physical perturbation

Column cancellation estimates in the proof of Proposition 5.18, using
the boundary depths, component distances and scalar form domains of the
physical perturbation.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical NNReal ENNReal

namespace Riesz2.PhysicalPerturbation

/-- See the proof of Proposition 5.18 in the paper: a middle-half source has depth
at least `n/4`, including the one-based endpoint convention. -/
theorem middle_depth_internal (n : ℕ+) (i₀ : Fin (n : ℕ))
    (hlo : (n : ℝ) / 4 ≤ (i₀.val : ℝ) + 1)
    (hhi : (i₀.val : ℝ) + 1 ≤ 3 * (n : ℝ) / 4) :
    (n : ℝ) / 4 ≤ ((min (i₀.val + 1) ((n : ℕ) - i₀.val) : ℕ) : ℝ) := by
  have hi := i₀.isLt
  rw [Nat.cast_min, Nat.cast_add, Nat.cast_one, Nat.cast_sub (by omega), le_min_iff]
  exact ⟨hlo, by linarith⟩

/-- See the proof of Proposition 5.18 in the paper: the boundary eighths are separated
from a middle-half source by `n/8`. Empty boundary eighths cause no exception. -/
theorem boundary_separation_internal (n : ℕ+) (i₀ k : Fin (n : ℕ))
    (hlo : (n : ℝ) / 4 ≤ (i₀.val : ℝ) + 1)
    (hhi : (i₀.val : ℝ) + 1 ≤ 3 * (n : ℝ) / 4)
    (hk : ((min (k.val + 1) ((n : ℕ) - k.val) : ℕ) : ℝ) ≤ (n : ℝ) / 8) :
    (n : ℝ) / 8 ≤ (Nat.dist k.val i₀.val : ℝ) := by
  have hkn := k.isLt
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

/-- See the proof of Proposition 5.18 in the paper: summing one distance times the
value profile costs exactly `n^s`, with no logarithmic loss. -/
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
      rw [weightRadius, LocalizedMatrix.active_distance m n hnm, Nat.dist_comm]
    _ ≤ _ := by
      have hh := LocalizedBoundary.active_weight_sum_internal n m hnm i₀ (1-s.val)
        (by linarith [s.property.2]) (by linarith [s.property.1])
      have he : 1 - (1-s.val) = s.val := by ring
      simpa only [he] using hh

/-- See the proof of Proposition 5.18 in the paper: boundary columns retain both
entry weights. The profile estimate is used only on separated columns. -/
theorem boundary_source_sum_internal (s : Riesz1.RieszExponent) (n : ℕ+)
    (i₀ : Fin (n : ℕ))
    (hlo : (n : ℝ) / 4 ≤ (i₀.val : ℝ) + 1)
    (hhi : (i₀.val : ℝ) + 1 ≤ 3 * (n : ℝ) / 4)
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
    have hsep := boundary_separation_internal n i₀ k hlo hhi hk'
    have hdepth := middle_depth_internal n i₀ hlo hhi
    have hd : d k ≤ d i₀ := by dsimp only [d] at *; linarith
    have hdpos : 0 < d k := by
      have hh := PerturbationBounds.depth_bounds n k
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
    have hh := LocalizedBoundary.boundary_weight_sum_internal n (s.val/2)
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

/-- See the proof of Proposition 5.18 in the paper: the bulk column increments use
the first moment of the value profile, rather than the sum of entries. -/
theorem bulk_source_sum_internal (s : Riesz1.RieszExponent)
    (n m : ℕ+) (hnm : 2 * (n : ℕ) ≤ (m : ℕ)) (i₀ : Fin (n : ℕ))
    (hlo : (n : ℝ) / 4 ≤ (i₀.val : ℝ) + 1)
    (hhi : (i₀.val : ℝ) + 1 ≤ 3 * (n : ℝ) / 4)
    (a : Fin (n : ℕ) → ℝ) (D F : ℝ) (hD : 0 ≤ D) (hF : 0 ≤ F)
    (ha : ∀ k, a k ≤ D * F * (1 + (Nat.dist k.val i₀.val : ℝ)) ^ (-(2-s.val))) :
    let d := fun k : Fin (n : ℕ) => ((min (k.val + 1) ((n : ℕ) - k.val) : ℕ) : ℝ)
    let U := Finset.univ.filter (fun k : Fin (n : ℕ) => (n : ℝ) / 8 < d k)
    (∑ k ∈ U, (Nat.dist k.val i₀.val : ℝ) *
      (min (d k) (d i₀)) ^ (-1-s.val/2) * a k) ≤
      (8 ^ (1+s.val/2) * (2 / s.val)) * D * F * (n : ℝ) ^ (-1+s.val/2) := by
  intro d U
  have hn : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hdepth := middle_depth_internal n i₀ hlo hhi
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

/-- See the proof of Proposition 5.18 in the paper: the remaining source column
uses the interior mean bound with its full power `n^{-(1-s)}`. -/
theorem mean_source_column_internal (s : Riesz1.RieszExponent)
    (n : ℕ+) (i₀ : Fin (n : ℕ))
    (hlo : (n : ℝ) / 4 ≤ (i₀.val : ℝ) + 1)
    (hhi : (i₀.val : ℝ) + 1 ≤ 3 * (n : ℝ) / 4)
    (aS D F : ℝ) (hD : 0 ≤ D) (hF : 0 ≤ F)
    (hS : aS ≤ D * (n : ℝ) ^ (-(1-s.val)) * F) :
    ((min (i₀.val + 1) ((n : ℕ) - i₀.val) : ℕ) : ℝ) ^ (-s.val/2) * aS ≤
      4 ^ (s.val/2) * D * F * (n : ℝ) ^ (-1+s.val/2) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hp := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < (n : ℝ)/4)
    (middle_depth_internal n i₀ hlo hhi) (by linarith [s.property.1] : -s.val/2 ≤ 0)
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

section ColumnAssembly

variable {E : Type*} [AddCommGroup E]

/-- See the proof of Proposition 5.18 in the paper, internal assembly before power
bookkeeping. Boundary columns use the two entry estimates. Bulk columns
use their difference. The final column is the actual sum of the sources. -/
theorem row_bound_internal (s : Riesz1.RieszExponent) (n : ℕ+)
    (i₀ : Fin (n : ℕ)) (b : Fin (n : ℕ) → E → ℝ) (v : Fin (n : ℕ) → E)
    (hsumb : (∑ k, b i₀ (v k)) = b i₀ (∑ k, v k))
    (a : Fin (n : ℕ) → ℝ) (aS P Err ErrS : ℝ) (_hP : 0 ≤ P)
    (hErr : 0 ≤ Err)
    (hentry : ∀ k l,
      |b l (v k)| ≤ P *
        ((min (l.val + 1) ((n : ℕ) - l.val) : ℕ) : ℝ) ^ (-s.val/2) * a k + Err)
    (hincrement : ∀ k,
      |b k (v k) - b i₀ (v k)| ≤ P * (Nat.dist k.val i₀.val : ℝ) *
        (min (((min (k.val + 1) ((n : ℕ) - k.val) : ℕ) : ℝ))
          (((min (i₀.val + 1) ((n : ℕ) - i₀.val) : ℕ) : ℝ))) ^ (-1-s.val/2) * a k + Err)
    (hmean : |b i₀ (∑ k, v k)| ≤ P *
      ((min (i₀.val + 1) ((n : ℕ) - i₀.val) : ℕ) : ℝ) ^ (-s.val/2) * aS + ErrS) :
    let d := fun k : Fin (n : ℕ) => ((min (k.val + 1) ((n : ℕ) - k.val) : ℕ) : ℝ)
    let B := Finset.univ.filter (fun k : Fin (n : ℕ) => d k ≤ (n : ℝ)/8)
    let U := Finset.univ.filter (fun k : Fin (n : ℕ) => (n : ℝ)/8 < d k)
    |∑ k, b k (v k)| ≤
      P * ((∑ k ∈ B, ((d k) ^ (-s.val/2) + (d i₀) ^ (-s.val/2)) * a k) +
        (∑ k ∈ U, (Nat.dist k.val i₀.val : ℝ) *
          (min (d k) (d i₀)) ^ (-1-s.val/2) * a k) + (d i₀) ^ (-s.val/2) * aS) +
        2 * (n : ℝ) * Err + ErrS := by
  intro d B U
  let t := fun k => b k (v k) - b i₀ (v k)
  let q := fun k => if k ∈ B then ((d k) ^ (-s.val/2) + (d i₀) ^ (-s.val/2)) * a k
    else (Nat.dist k.val i₀.val : ℝ) * (min (d k) (d i₀)) ^ (-1-s.val/2) * a k
  have hb (k) : |t k| ≤ P * q k + 2 * Err := by
    by_cases hk : k ∈ B
    · have hh := (abs_sub (b k (v k)) (b i₀ (v k))).trans
        (add_le_add (hentry k k) (hentry k i₀))
      dsimp only [t, q]
      rw [ite_eq_left hk]
      change |b k (v k) - b i₀ (v k)| ≤ _
      dsimp only [d]
      nlinarith only [hh]
    · have hh := hincrement k
      dsimp only [t, q]
      rw [ite_eq_right hk]
      exact hh.trans (by dsimp only [d]; linarith only [hErr])
  have hq : (∑ k, q k) = (∑ k ∈ B, ((d k) ^ (-s.val/2) + (d i₀) ^ (-s.val/2)) * a k) +
      (∑ k ∈ U, (Nat.dist k.val i₀.val : ℝ) * (min (d k) (d i₀)) ^ (-1-s.val/2) * a k) := by
    simp only [q, B, U, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : d k ≤ (n : ℝ)/8 <;> simp [hk]
  have hsub : (∑ k, b k (v k)) = (∑ k, (b k (v k) - b i₀ (v k))) + b i₀ (∑ k, v k) := by
    rw [Finset.sum_sub_distrib, hsumb]
    ring
  rw [hsub]
  calc
    _ ≤ |∑ k, t k| + |b i₀ (∑ k, v k)| := abs_add_le _ _
    _ ≤ (∑ k, |t k|) + |b i₀ (∑ k, v k)| :=
      add_le_add (Finset.abs_sum_le_sum_abs _ _) le_rfl
    _ ≤ (∑ k, (P * q k + 2 * Err)) +
        (P * (d i₀) ^ (-s.val/2) * aS + ErrS) := add_le_add (Finset.sum_le_sum (fun k _ => hb k)) hmean
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin, hq]
      ring

/-- See the proof of Proposition 5.18 in the paper, internal composition of the three
source sums. Here `D` is the common prefactor in the lifted value and mean
estimates. The test factor is the separate variable `P`. -/
theorem cancellation_from_source_bounds_internal (s : Riesz1.RieszExponent)
    (n m : ℕ+) (hnm : 2 * (n : ℕ) ≤ (m : ℕ)) (i₀ : Fin (n : ℕ))
    (hlo : (n : ℝ) / 4 ≤ (i₀.val : ℝ) + 1)
    (hhi : (i₀.val : ℝ) + 1 ≤ 3 * (n : ℝ) / 4)
    (b : Fin (n : ℕ) → E → ℝ) (v : Fin (n : ℕ) → E)
    (hsumb : (∑ k, b i₀ (v k)) = b i₀ (∑ k, v k))
    (a : Fin (n : ℕ) → ℝ) (aS D F P Err ErrS : ℝ)
    (hD : 0 ≤ D) (hF : 0 ≤ F) (hP : 0 ≤ P) (hErr : 0 ≤ Err)
    (hvalue : ∀ k, a k ≤ D * F * (1 + (Nat.dist k.val i₀.val : ℝ)) ^ (-(2-s.val)))
    (hsum : aS ≤ D * (n : ℝ) ^ (-(1-s.val)) * F)
    (hentry : ∀ k l,
      |b l (v k)| ≤ P *
        ((min (l.val + 1) ((n : ℕ) - l.val) : ℕ) : ℝ) ^ (-s.val/2) * a k + Err)
    (hincrement : ∀ k,
      |b k (v k) - b i₀ (v k)| ≤ P * (Nat.dist k.val i₀.val : ℝ) *
        (min (((min (k.val + 1) ((n : ℕ) - k.val) : ℕ) : ℝ))
          (((min (i₀.val + 1) ((n : ℕ) - i₀.val) : ℕ) : ℝ))) ^ (-1-s.val/2) * a k + Err)
    (hmean : |b i₀ (∑ k, v k)| ≤ P *
      ((min (i₀.val + 1) ((n : ℕ) - i₀.val) : ℕ) : ℝ) ^ (-s.val/2) * aS + ErrS) :
    |∑ k, b k (v k)| ≤ P *
      ((2 * 8 ^ (2-s.val) * (2 / (1-s.val/2))) +
        (8 ^ (1+s.val/2) * (2/s.val)) + 4 ^ (s.val/2)) * D * F *
        (n : ℝ) ^ (-1+s.val/2) + 2 * (n : ℝ) * Err + ErrS := by
  have hh := row_bound_internal s n i₀ b v hsumb a aS P Err ErrS hP hErr hentry hincrement hmean
  have hb := boundary_source_sum_internal s n i₀ hlo hhi a D F hD hF hvalue
  have hu := bulk_source_sum_internal s n m hnm i₀ hlo hhi a D F hD hF hvalue
  have hs := mean_source_column_internal s n i₀ hlo hhi aS D F hD hF hsum
  apply hh.trans
  calc
    _ ≤ P * ((2 * 8 ^ (2-s.val) * (2 / (1-s.val/2))) * D * F * (n : ℝ) ^ (-1+s.val/2) +
        (8 ^ (1+s.val/2) * (2/s.val)) * D * F * (n : ℝ) ^ (-1+s.val/2) +
        4 ^ (s.val/2) * D * F * (n : ℝ) ^ (-1+s.val/2)) + 2 * (n : ℝ) * Err + ErrS := by
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hb hu) hs) hP) le_rfl) le_rfl
    _ = _ := by ring

end ColumnAssembly

section PhysicalRows

variable {X ι κ : Type*} [MeasurableSpace X] [Fintype ι] [Fintype κ]
  {ν : Measure X}

/-- See the proof of Proposition 5.18 in the paper: the actual L² sum has the
polynomial essential bound used for its exceptional column. -/
theorem sum_ae_bound_internal (v : ι → Lp ℝ 2 ν) (B : ℝ)
    (hv : ∀ k, ∀ᵐ x ∂ν, |v k x| ≤ B) :
    ∀ᵐ x ∂ν, |(∑ k, v k : Lp ℝ 2 ν) x| ≤ (Fintype.card ι : ℝ) * B := by
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ v, ae_all_iff.mpr hv] with x hx hb
  rw [hx]
  calc
    _ ≤ ∑ k, |v k x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : ι, B := Finset.sum_le_sum (fun k _ => hb k)
    _ = _ := by simp

end PhysicalRows

section ExceptionalTerms

variable {X ι : Type*} [MeasurableSpace X]
  {ν : Measure X}

/-- See the proof of Proposition 5.18 in the paper: the maximum principle gives
component bounds for a point source on any closed scalar form. It applies
also to an unbounded physical Hessian, on its natural matrix domain. -/
theorem point_source_component_bound_internal [Fintype ι] [DecidableEq ι]
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (M : X → Matrix ι ι ℝ) (hMm : ∀ i j, Measurable (fun x => M x i j))
    (c : ℝ) (hc : 0 < c)
    (hM : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
      ∀ z : ι → ℝ, c * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j)
    (i₀ : ι) (χ : Lp ℝ 2 ν) (B : ℝ) (hB : 0 ≤ B)
    (hχ : ∀ᵐ x ∂ν, |χ x| ≤ B)
    (u : ι → Q.1)
    (hu : WeightedWeakSolution Q M ⊤ (fun i => if i=i₀ then χ else 0) u) :
    ∀ᵐ x ∂ν, ∀ i, |(u i).val x| ≤ c⁻¹ * B := by
  let R : ℝ≥0 := ⟨c⁻¹ * B, mul_nonneg (inv_nonneg.mpr hc.le) hB⟩
  have hsource : ∀ᵐ x ∂ν,
      ‖(WithLp.toLp 2 (fun i => (if i=i₀ then χ else 0 : Lp ℝ 2 ν) x) :
        EuclideanSpace ℝ ι)‖ ≤ c * R := by
    filter_upwards [hχ, Lp.coeFn_zero ℝ 2 ν] with x hx hz
    change (0 : Lp ℝ 2 ν) x = 0 at hz
    have hsingle : (WithLp.toLp 2 (fun i => (if i=i₀ then χ else 0 : Lp ℝ 2 ν) x) :
        EuclideanSpace ℝ ι) = PiLp.single 2 i₀ (χ x) := by
      ext i
      by_cases hi : i=i₀
      · simp only [hi, ite_true, PiLp.single_apply]
      · simpa only [ite_eq_right hi, PiLp.toLp_apply, PiLp.single_apply, ite_eq_right hi] using hz
    rw [hsingle, PiLp.norm_single, Real.norm_eq_abs]
    have he : c * (R : ℝ) = B := by
      change c * (c⁻¹ * B) = B
      rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    rwa [he]
  have hb := MaximumPrinciple.Internal.bound_of_source_bound Q hQ M hMm c hc hM ⊤
    (fun i => if i=i₀ then χ else 0) u hu R hsource
  filter_upwards [hb] with x hx
  intro i
  have hi : |(u i).val x| ≤ ‖(WithLp.toLp 2 (fun j => (u j).val x) : EuclideanSpace ℝ ι)‖ := by
    simpa only [Real.norm_eq_abs] using
      (PiLp.norm_apply_le (WithLp.toLp 2 (fun j => (u j).val x) : EuclideanSpace ℝ ι) i)
  exact hi.trans hx

end ExceptionalTerms

end Riesz2.PhysicalPerturbation
