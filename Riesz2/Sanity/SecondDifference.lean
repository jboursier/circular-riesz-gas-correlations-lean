/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.ReferenceIntervalMatrix
public import Riesz1.ToMathlib.HurwitzKernel.Derivatives

/-! # A strictly positive off-zero sampled second difference -/

@[expose] public section
open Set
namespace Riesz2.DefinitionSanity

theorem sampled_second_difference_four_pos (s : Riesz1.RieszExponent) :
    0 < sampledSecondDifference s 4 (by norm_num) 2 := by
  have hconv := Riesz1.strictConvexOn_hurwitzKernel s.val s.property.1 s.property.2 0
  have hc : Riesz1.hurwitzKernel s.val ((1 / 2 : ℝ) • (1 / 4 : ℝ) +
      (1 / 2 : ℝ) • (3 / 4 : ℝ)) < (1 / 2 : ℝ) • Riesz1.hurwitzKernel s.val (1 / 4) +
      (1 / 2 : ℝ) • Riesz1.hurwitzKernel s.val (3 / 4) :=
    hconv.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [smul_eq_mul] at hc
  have hpow : 0 < (4 : ℝ) ^ (-s.val) := Real.rpow_pos_of_pos (by norm_num) _
  norm_num [sampledSecondDifference, sampledRieszKernel, Riesz1.rieszKernel,
    Riesz1.rieszRepresentative, interiorCirclePoint, Riesz1.hurwitzKernel] at hc ⊢
  nlinarith [mul_pos hpow (sub_pos.mpr hc)]

theorem reference_four_antipodal_coefficient_pos (s : Riesz1.RieszExponent) :
    0 < (1 - (1 / 2 : ℝ)) * sampledSecondDifference s 4 (by norm_num) 2 := by
  exact mul_pos (by norm_num) (sampled_second_difference_four_pos s)

theorem reference_four_lengths :
    ((Finset.range (((4 : ℕ+) : ℕ) / 2 + 1)).filter (fun r => 1 ≤ r ∧ 1 ≤ r)) = {1, 2} := by
  ext r
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  norm_num
  omega

/-- The actual K=1 reference matrix has a strictly positive adjacent entry. -/
theorem reference_four_adjacent_pos (s : Riesz1.RieszExponent) :
    0 < referenceIntervalMatrix s 4 (by norm_num) 1 0 1 := by
  unfold referenceIntervalMatrix
  change 0 < ∑ i : Fin 4, ∑ r ∈ (Finset.range (2 + 1)).filter (fun r => 1 ≤ r ∧ 1 ≤ r),
    (1 - if 2 * r = 4 then (1 / 2 : ℝ) else 0) *
      sampledSecondDifference s 4 (by norm_num) ⟨r % 4, by change r % 4 < 4; omega⟩ *
      (if (0 : Fin (4 : ℕ+)) ∈ cyclicIndexInterval 4 i r then 1 else 0) *
      (if (1 : Fin (4 : ℕ+)) ∈ cyclicIndexInterval 4 i r then 1 else 0)
  norm_num [Fin.sum_univ_succ, Finset.sum_range_succ, Finset.sum_filter, cyclicIndexInterval, Fin.ext_iff, Nat.le_one_iff_eq_zero_or_eq_one]
  have hp := reference_four_antipodal_coefficient_pos s
  norm_num at hp
  convert hp using 1; rfl

end Riesz2.DefinitionSanity
