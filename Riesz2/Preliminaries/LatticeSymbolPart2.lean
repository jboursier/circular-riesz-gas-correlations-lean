/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Preliminaries.LatticeSymbol
public import Riesz2.ToMathlib.CenteredSecondDifference

/-!
# Quantitative lattice curvature

The power comparison completing the proof of Lemma 2.5.
The exceptional first site uses its actual regularized value.
-/

public section

open scoped BigOperators

namespace Riesz2

private theorem power_centered_bounds (s : Riesz1.RieszExponent) {x : ℝ} (hx : 2 ≤ x) :
    s.val * (s.val + 1) * (2 : ℝ) ^ (-s.val - 2) * x ^ (-s.val - 2) ≤
        (x + 1) ^ (-s.val) + (x - 1) ^ (-s.val) - 2 * x ^ (-s.val) ∧
      (x + 1) ^ (-s.val) + (x - 1) ^ (-s.val) - 2 * x ^ (-s.val) ≤
        s.val * (s.val + 1) * (1 / 2 : ℝ) ^ (-s.val - 2) * x ^ (-s.val - 2) := by
  have hs : 0 < s.val := s.property.1
  have hcoef : 0 ≤ s.val * (s.val + 1) := by positivity
  have hxp : 0 < x := by linarith
  apply centeredSecondDifference_bounds (f := fun y : ℝ => y ^ (-s.val)) (x := x)
    (f' := fun y => -s.val * y ^ (-s.val - 1))
    (f'' := fun y => s.val * (s.val + 1) * y ^ (-s.val - 2))
  · exact fun y hy => (Real.continuousAt_rpow_const y (-s.val)
      (Or.inl (by linarith [hy.1]))).continuousWithinAt
  · intro y hy
    exact Real.hasDerivAt_rpow_const (Or.inl (by linarith [hy.1]))
  · intro y hy
    convert (Real.hasDerivAt_rpow_const (x := y) (p := -s.val - 1)
      (Or.inl (by linarith [hy.1]))).const_mul (-s.val) using 1
    rw [show -s.val - 1 - 1 = -s.val - 2 by ring]
    ring
  · intro y hy
    rw [mul_assoc (s.val * (s.val + 1)), ← Real.mul_rpow (by norm_num) hxp.le]
    apply mul_le_mul_of_nonneg_left _ hcoef
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hy.1])
      (by linarith [hy.2]) (by linarith [s.property.1])
  · intro y hy
    rw [mul_assoc (s.val * (s.val + 1)), ← Real.mul_rpow (by norm_num) hxp.le]
    apply mul_le_mul_of_nonneg_left _ hcoef
    exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (by linarith [hy.1]) (by linarith [s.property.1])

/-- The quantitative curvature assertion of the proof of Lemma 2.5.
The constants precede the integer site and work uniformly for every `r ≥ 1`. -/
theorem latticeRieszCurvature_bounds (s : Riesz1.RieszExponent) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ r : ℤ, 1 ≤ r →
      0 < c * (r : ℝ) ^ (-s.val - 2) ∧
      c * (r : ℝ) ^ (-s.val - 2) ≤ latticeRieszCurvature s r ∧
      latticeRieszCurvature s r ≤ C * (r : ℝ) ^ (-s.val - 2) := by
  let b := (2 : ℝ) ^ (-s.val)
  let c := min b (s.val * (s.val + 1) * (2 : ℝ) ^ (-s.val - 2))
  let C := max b (s.val * (s.val + 1) * (1 / 2 : ℝ) ^ (-s.val - 2))
  have hs : 0 < s.val := s.property.1
  have hb : 0 < b := Real.rpow_pos_of_pos (by norm_num) _
  have hc : 0 < c := lt_min hb (by positivity)
  have hC : 0 < C := lt_of_lt_of_le hb (le_max_left _ _)
  refine ⟨c, C, hc, hC, fun r hr => ⟨mul_pos hc
    (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < r by omega)) _), ?_⟩⟩
  by_cases hr1 : r = 1
  · subst r
    simpa only [Int.cast_one, Real.one_rpow, mul_one, latticeRieszCurvature_one] using
      (show c ≤ b ∧ b ≤ C from ⟨min_le_left _ _, le_max_left _ _⟩)
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast (show (2 : ℤ) ≤ r by omega)
  have h := power_centered_bounds s hr2
  have heq : latticeRieszCurvature s r =
      ((r : ℝ) + 1) ^ (-s.val) + ((r : ℝ) - 1) ^ (-s.val) -
        2 * (r : ℝ) ^ (-s.val) := by
    simp only [latticeRieszCurvature, latticeRieszKernel,
      show r + 1 ≠ 0 by omega, show r - 1 ≠ 0 by omega,
      show r ≠ 0 by omega, ite_false, Int.cast_add, Int.cast_sub, Int.cast_one,
      abs_of_pos (show (0 : ℝ) < r by linarith),
      abs_of_pos (show (0 : ℝ) < r + 1 by linarith),
      abs_of_pos (show (0 : ℝ) < r - 1 by linarith)]
  rw [heq]
  exact ⟨(mul_le_mul_of_nonneg_right (min_le_right _ _)
    (Real.rpow_nonneg (by linarith) _)).trans h.1,
    h.2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_nonneg (by linarith) _))⟩

/-- Conclusions from the proof of Lemma 2.5, with the ordered convergence,
curvature representation and uniform quantitative curvature comparison together. -/
theorem latticeRiesz_positive_symbol (s : Riesz1.RieszExponent) :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ r : ℤ, 1 ≤ r →
      0 < c * (r : ℝ) ^ (-s.val - 2) ∧
      c * (r : ℝ) ^ (-s.val - 2) ≤ latticeRieszCurvature s r ∧
      latticeRieszCurvature s r ≤ C * (r : ℝ) ^ (-s.val - 2)) ∧
    ∀ θ : ℝ, 0 < θ → θ < 2 * Real.pi → ∃ S : ℝ,
      Filter.Tendsto (fun M : ℕ => 2 + 2 *
        ∑ r ∈ Finset.range M, (((r + 1 : ℕ) : ℝ) ^ (-s.val)) *
          Real.cos (((r + 1 : ℕ) : ℝ) * θ)) Filter.atTop (nhds S) ∧
      S = ∑' r : ℕ, latticeRieszCurvature s ((r : ℤ) + 1) *
        ((1 - Real.cos (((r + 1 : ℕ) : ℝ) * θ)) / (1 - Real.cos θ)) ∧
      (2 : ℝ) ^ (-s.val) ≤ S ∧ 0 < S :=
  ⟨latticeRieszCurvature_bounds s, latticeRieszSymbol_ordered s⟩

end Riesz2
