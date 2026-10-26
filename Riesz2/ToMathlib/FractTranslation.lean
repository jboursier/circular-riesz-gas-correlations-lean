/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Translation modulo one on `[0,1)`

Lebesgue measure restricted to `[0,1)` is invariant under `x ↦ Int.fract (x + t)` for every real
`t`. This is the rotation of the first particle of a configuration on the circle.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz2
namespace FractTranslation

/-- For `0 ≤ t < 1`, the reduction modulo one of `x + t` on `[0,1)` splits into the two
translations `x ↦ x + t` on `[0,1-t)` and `x ↦ x + (t - 1)` on `[1-t,1)`. -/
theorem map_fract_add_restrict_Ico_of_mem {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (volume.restrict (Ico (0 : ℝ) 1)).map (fun x : ℝ => Int.fract (x + t)) =
      volume.restrict (Ico (0 : ℝ) 1) := by
  have hmeas : Measurable (fun x : ℝ => Int.fract (x + t)) :=
    measurable_fract.comp (measurable_id.add_const t)
  have hsplit : Ico (0 : ℝ) 1 = Ico 0 (1 - t) ∪ Ico (1 - t) 1 :=
    (Ico_union_Ico_eq_Ico (by linarith) (by linarith)).symm
  have hsplit' : Ico (0 : ℝ) 1 = Ico 0 t ∪ Ico t 1 :=
    (Ico_union_Ico_eq_Ico (by linarith) (by linarith)).symm
  -- The first piece is a translation by `t`.
  have hfirst : (volume.restrict (Ico (0 : ℝ) (1 - t))).map (fun x : ℝ => Int.fract (x + t)) =
      volume.restrict (Ico t 1) := by
    have hcongr : (fun x : ℝ => Int.fract (x + t)) =ᵐ[volume.restrict (Ico (0 : ℝ) (1 - t))]
        (fun x : ℝ => x + t) := by
      filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
      obtain ⟨hx0, hx1⟩ := hx
      rw [Int.fract, Int.floor_eq_zero_iff.mpr ⟨by linarith, by linarith⟩]
      simp
    rw [Measure.map_congr hcongr]
    have hpm := (measurePreserving_add_right volume t).restrict_preimage
      (μa := volume) (f := fun x : ℝ => x + t) (s := Ico t 1) measurableSet_Ico
    have hset : (fun x : ℝ => x + t) ⁻¹' Ico t 1 = Ico 0 (1 - t) := by
      ext x
      simp only [mem_preimage, mem_Ico]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    rw [hset] at hpm
    exact hpm.map_eq
  -- The second piece is a translation by `t - 1`.
  have hsecond : (volume.restrict (Ico (1 - t) 1)).map (fun x : ℝ => Int.fract (x + t)) =
      volume.restrict (Ico 0 t) := by
    have hcongr : (fun x : ℝ => Int.fract (x + t)) =ᵐ[volume.restrict (Ico (1 - t) 1)]
        (fun x : ℝ => x + (t - 1)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
      obtain ⟨hx0, hx1⟩ := hx
      have hfl : Int.floor (x + t) = 1 := by
        rw [Int.floor_eq_iff]
        constructor <;> push_cast <;> linarith
      rw [Int.fract, hfl]
      push_cast
      ring
    rw [Measure.map_congr hcongr]
    have hpm := (measurePreserving_add_right volume (t - 1)).restrict_preimage
      (μa := volume) (f := fun x : ℝ => x + (t - 1)) (s := Ico 0 t) measurableSet_Ico
    have hset : (fun x : ℝ => x + (t - 1)) ⁻¹' Ico 0 t = Ico (1 - t) 1 := by
      ext x
      simp only [mem_preimage, mem_Ico]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    rw [hset] at hpm
    exact hpm.map_eq
  have hL : (volume.restrict (Ico (0 : ℝ) 1)).map (fun x : ℝ => Int.fract (x + t)) =
      volume.restrict (Ico t 1) + volume.restrict (Ico 0 t) := by
    rw [hsplit, Measure.restrict_union Ico_disjoint_Ico_same measurableSet_Ico,
      Measure.map_add _ _ hmeas, hfirst, hsecond]
  have hR : volume.restrict (Ico (0 : ℝ) 1) = volume.restrict (Ico t 1) + volume.restrict (Ico 0 t) := by
    rw [hsplit', Measure.restrict_union Ico_disjoint_Ico_same measurableSet_Ico, add_comm]
  rw [hL, ← hR]

/-- Translation by any real `t`, reduced modulo one, preserves Lebesgue measure on `[0,1)`. -/
theorem map_fract_add_restrict_Ico (t : ℝ) :
    (volume.restrict (Ico (0 : ℝ) 1)).map (fun x : ℝ => Int.fract (x + t)) =
      volume.restrict (Ico (0 : ℝ) 1) := by
  have hreduce : (fun x : ℝ => Int.fract (x + t)) = fun x : ℝ => Int.fract (x + Int.fract t) := by
    funext x
    have hx : x + t = (x + Int.fract t) + ((⌊t⌋ : ℤ) : ℝ) := by
      rw [Int.fract]
      ring
    rw [hx, Int.fract_add_intCast]
  rw [hreduce]
  exact map_fract_add_restrict_Ico_of_mem (Int.fract_nonneg t) (Int.fract_lt_one t)

end FractTranslation
end Riesz2
end
end
