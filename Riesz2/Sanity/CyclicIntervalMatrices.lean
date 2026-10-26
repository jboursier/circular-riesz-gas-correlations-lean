/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.PeriodizedMatrixBounds
public import Mathlib
/-! # A coercive cyclic-interval matrix satisfying the periodized bounds -/

@[expose] public section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
namespace Riesz2.DefinitionSanity

/-- The identity plus the four rank-one matrices of length-two cyclic intervals. -/
def intervalMatrixFour : Matrix (Fin (4 : ℕ+)) (Fin (4 : ℕ+)) ℝ :=
  fun i j => if i.val = j.val then 3 else
    if (i.val + 1) % 4 = j.val ∨ (j.val + 1) % 4 = i.val then 1 else 0

theorem interval_matrix_four_quadratic (z : Fin (4 : ℕ+) → ℝ) :
    (∑ i, ∑ j, z i * intervalMatrixFour i j * z j) =
      ∑ i : Fin (4 : ℕ+), ∑ r : Fin 2, (cyclicGapSum 4 i (r.val + 1) z) ^ 2 := by
  change (∑ i : Fin 4, ∑ j : Fin 4, z i * intervalMatrixFour i j * z j) =
    ∑ i : Fin 4, ∑ r : Fin 2, (cyclicGapSum 4 i (r.val + 1) z) ^ 2
  have hcyc (i : Fin 4) (r : Fin 2) :
      cyclicGapSum 4 i (r.val + 1) z =
        ∑ a ∈ Finset.range (r.val + 1), z ⟨(i.val + a) % 4, by change (i.val + a) % 4 < 4; omega⟩ := rfl
  simp only [hcyc]
  norm_num [Fin.sum_univ_succ, Finset.sum_range_succ, intervalMatrixFour]
  have h1 : (⟨1, by norm_num⟩ : Fin (4 : ℕ+)) = 1 := rfl
  have h2 : (⟨2, by norm_num⟩ : Fin (4 : ℕ+)) = 2 := rfl
  have h3 : (⟨3, by norm_num⟩ : Fin (4 : ℕ+)) = 3 := rfl
  simp only [h1, h2, h3]
  have hpoly (a b c d : ℝ) :
      a * 3 * a + (a * b + a * d) + (b * a + (b * 3 * b + b * c) +
        (c * b + (c * 3 * c + c * d) + (d * a + (d * c + d * 3 * d)))) =
      a ^ 2 + (a + b) ^ 2 + (b ^ 2 + (b + c) ^ 2 +
        (c ^ 2 + (c + d) ^ 2 + (d ^ 2 + (d + a) ^ 2))) := by ring
  convert hpoly (z 0) (z 1) (z 2) (z 3) using 1; rfl

theorem interval_matrix_four_coercive (z : Fin (4 : ℕ+) → ℝ) :
    (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * intervalMatrixFour i j * z j := by
  change (∑ i : Fin 4, z i ^ 2) ≤ ∑ i : Fin 4, ∑ j : Fin 4, z i * intervalMatrixFour i j * z j
  norm_num [Fin.sum_univ_succ, intervalMatrixFour]
  have hpoly (a b c d : ℝ) : a ^ 2 + (b ^ 2 + (c ^ 2 + d ^ 2)) ≤
      a * 3 * a + (a * b + a * d) + (b * a + (b * 3 * b + b * c) +
        (c * b + (c * 3 * c + c * d) + (d * a + (d * c + d * 3 * d)))) := by
    nlinarith [sq_nonneg (a + b), sq_nonneg (b + c),
      sq_nonneg (c + d), sq_nonneg (d + a)]
  convert hpoly (z 0) (z 1) (z 2) (z 3) using 1 <;> rfl

/-- A four-component admissible instance with K=1 and both interval lengths present.
The prefactor controls the actual reference error. The lower coefficient bound holds
for every length, including the length-two threshold. -/
theorem periodized_matrix_four_nonempty (s : Riesz1.RieszExponent)
    {α : Type*} [MeasurableSpace α] (ν : Measure α) :
    ∃ C : ℝ, 1 ≤ C ∧ PeriodizedMatrixBounds (ν := ν) s 4 4 (by norm_num) 1 C 4 2 (1 / 4)
      (fun _ => intervalMatrixFour) := by
  let H := (2 : ℝ) • referenceIntervalMatrix s 4 (by norm_num) 1
  let w (i j : Fin (4 : ℕ+)) :=
    (1 + (Riesz1.cyclicIndexDistance 4 i j : ℝ)) ^ (-1 - s.val / 2)
  have hw (i j : Fin (4 : ℕ+)) : 0 < w i j := by
    apply Real.rpow_pos_of_pos
    positivity
  let D := ∑ i : Fin (4 : ℕ+), ∑ j : Fin (4 : ℕ+),
    |intervalMatrixFour i j - H i j| / w i j
  have hD : 0 ≤ D := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    div_nonneg (abs_nonneg _) (hw i j).le
  let C := 1 + (2 : ℝ) ^ (s.val + 2) + D
  have hC : 1 ≤ C := by dsimp [C]; linarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (s.val + 2)]
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hCp : (2 : ℝ) ^ (s.val + 2) ≤ C := by dsimp [C]; linarith
  have hCi : C⁻¹ ≤ 1 := (inv_le_one₀ hC0).mpr hC
  have hweight : (2 : ℝ) ^ (-s.val - 2) = ((2 : ℝ) ^ (s.val + 2))⁻¹ := by
    rw [show -s.val - 2 = -(s.val + 2) by ring, Real.rpow_neg (by norm_num)]
  have hpow : 0 < (2 : ℝ) ^ (s.val + 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hupper : 1 ≤ C * (2 : ℝ) ^ (-s.val - 2) := by
    rw [hweight, ← div_eq_mul_inv]
    exact (le_div_iff₀ hpow).mpr (by simpa using hCp)
  refine ⟨C, hC, ?_⟩
  refine ⟨fun _ _ => measurable_const, Filter.Eventually.of_forall (fun _ => ?_),
    fun _ _ _ => 1, fun _ _ => measurable_const, Filter.Eventually.of_forall (fun _ => ?_)⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro i j
      change (intervalMatrixFour : Matrix (Fin 4) (Fin 4) ℝ) i j = intervalMatrixFour j i
      fin_cases i <;> fin_cases j <;> norm_num [intervalMatrixFour]
    · intro i j hij
      have hi : i.val < 4 := i.isLt
      have hj : j.val < 4 := j.isLt
      change 4 ≤ i.val ∨ 4 ≤ j.val at hij
      omega
    · intro z
      change C⁻¹ * (4 : ℝ) ^ (-4 * (1 / 4)) * (∑ i, z i ^ 2) ≤ _
      norm_num only [show (-4 * (1 / 4) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
      calc
        _ ≤ (1 : ℝ) * (∑ i, z i ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun i _ => sq_nonneg _)
          nlinarith [inv_nonneg.mpr hC0.le]
        _ ≤ _ := by simpa only [one_mul] using interval_matrix_four_coercive z
    · intro i j _ _
      have hsingle : |intervalMatrixFour i j - H i j| / w i j ≤ D := by
        apply le_trans (Finset.single_le_sum
          (f := fun j => |intervalMatrixFour i j - H i j| / w i j)
          (fun j _ => div_nonneg (abs_nonneg _) (hw i j).le) (Finset.mem_univ j))
        exact Finset.single_le_sum (f := fun i => ∑ j, |intervalMatrixFour i j - H i j| / w i j)
          (fun i _ => Finset.sum_nonneg fun j _ =>
            div_nonneg (abs_nonneg _) (hw i j).le) (Finset.mem_univ i)
      have hDC : D ≤ C * 4 := by dsimp [C]; nlinarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (s.val + 2)]
      have herr := (div_le_iff₀ (hw i j)).mp (hsingle.trans hDC)
      change |intervalMatrixFour i j - H i j| ≤ C * (4 : ℝ) ^ (4 * (1 / 4)) * w i j
      simpa only [show (4 * (1 / 4) : ℝ) = 1 by norm_num, Real.rpow_one] using herr
  · constructor
    · intro i r
      refine ⟨by norm_num, ?_, ?_⟩
      · fin_cases r
        · norm_num
          linarith
        · norm_num
          nlinarith
      · intro _
        have hrpow : ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith [s.property.1])
        have hnonneg : 0 ≤ ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2) := by positivity
        change C⁻¹ * (4 : ℝ) ^ (-4 * (1 / 4)) * _ ≤ 1
        norm_num only [show (-4 * (1 / 4) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
        have hprod := mul_le_mul hCi hrpow hnonneg (by norm_num : (0 : ℝ) ≤ 1)
        nlinarith [mul_nonneg (inv_nonneg.mpr hC0.le) hnonneg]
    · intro z
      change (∑ i : Fin (4 : ℕ+), ∑ j : Fin (4 : ℕ+), z i * intervalMatrixFour i j * z j) =
        ∑ i : Fin (4 : ℕ+), ∑ r : Fin 2, 1 * (cyclicGapSum 4 i (r.val + 1) z) ^ 2
      simpa only [one_mul] using interval_matrix_four_quadratic z

/-- The constructed cutoff is allowed by the long auxiliary size convention. -/
theorem matrix_four_cutoff : (Nat.floor ((4 : ℝ) ^ (1 / 4 : ℝ))) ^ (1 : ℕ) = 1 := by
  rw [pow_one]
  apply (Nat.floor_eq_iff (by positivity)).mpr
  constructor
  · simpa only [Nat.cast_one] using Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 4) (by norm_num : 0 ≤ (1 / 4 : ℝ))
  · have hp := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 4)
      (by norm_num : (1 / 4 : ℝ) < 1 / 2)
    have hs : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by norm_num [Real.rpow_div_two_eq_sqrt]
    norm_num only [Nat.cast_one, hs] at hp ⊢
    exact hp
/-- Length two reaches the lower-coefficient threshold. -/
theorem matrix_four_lower_threshold : (4 : ℝ) ^ ((2 : ℝ) * (1 / 4)) = 2 := by
  norm_num [Real.rpow_div_two_eq_sqrt]

end Riesz2.DefinitionSanity
