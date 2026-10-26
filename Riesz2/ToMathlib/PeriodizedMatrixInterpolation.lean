/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.PeriodizedMatrixBounds
public import Mathlib.Tactic

/-!
# Interpolation of interval matrix bounds

The literal matrix predicate is stable under convex combinations
over the same scalar carrier and measure. This is an internal algebraic
interface. Physical coefficient estimates must be proved separately.
-/

public section
noncomputable section
open MeasureTheory
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.PeriodizedMatrixInterpolation

/-- Convex interpolation preserves every clause of the `PeriodizedMatrixBounds`, including its measurable interval representation
and its exact reference exterior blocks. -/
theorem convex_combination {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Riesz1.RieszExponent) (n m : ℕ+) (hm : 2 ≤ (m : ℕ))
    (K : ℕ) (C κ γ ε t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (M₀ M₁ : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (h₀ : PeriodizedMatrixBounds (ν := μ) s n m hm K C κ γ ε M₀)
    (h₁ : PeriodizedMatrixBounds (ν := μ) s n m hm K C κ γ ε M₁) :
    PeriodizedMatrixBounds (ν := μ) s n m hm K C κ γ ε
      (fun x => (1 - t) • M₀ x + t • M₁ x) := by
  have ht0 : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  obtain ⟨hm₀, hmat₀, a₀, ha₀, hcoeff₀⟩ := h₀
  obtain ⟨hm₁, hmat₁, a₁, ha₁, hcoeff₁⟩ := h₁
  refine ⟨fun i j => ((hm₀ i j).const_mul (1 - t)).add ((hm₁ i j).const_mul t), ?_,
    (fun i r x => (1 - t) * a₀ i r x + t * a₁ i r x),
    (fun i r => ((ha₀ i r).const_mul (1 - t)).add ((ha₁ i r).const_mul t)), ?_⟩
  · filter_upwards [hmat₀, hmat₁] with x h₀ h₁
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    refine ⟨fun i j => by rw [h₀.1 i j, h₁.1 i j], ?_, ?_, ?_⟩
    · intro i j hij
      rw [h₀.2.1 i j hij, h₁.2.1 i j hij]
      simp only [Matrix.smul_apply, smul_eq_mul]
      ring
    · intro z
      have he : (∑ i, ∑ j, z i * ((1 - t) * M₀ x i j + t * M₁ x i j) * z j) =
          (1 - t) * (∑ i, ∑ j, z i * M₀ x i j * z j) +
            t * (∑ i, ∑ j, z i * M₁ x i j * z j) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [he]
      have hh₀ := mul_le_mul_of_nonneg_left (h₀.2.2.1 z) ht0
      have hh₁ := mul_le_mul_of_nonneg_left (h₁.2.2.1 z) ht
      nlinarith only [hh₀, hh₁]
    · intro i j hi hj
      let H := (2 : ℝ) • referenceIntervalMatrix s m hm K
      have he : (1 - t) * M₀ x i j + t * M₁ x i j - H i j =
          (1 - t) * (M₀ x i j - H i j) + t * (M₁ x i j - H i j) := by ring
      change |(1 - t) * M₀ x i j + t * M₁ x i j - H i j| ≤ _
      rw [he]
      calc
        _ ≤ |(1 - t) * (M₀ x i j - H i j)| + |t * (M₁ x i j - H i j)| := abs_add_le _ _
        _ = (1 - t) * |M₀ x i j - H i j| + t * |M₁ x i j - H i j| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ht0, abs_of_nonneg ht]
        _ ≤ (1 - t) * (C * (n : ℝ) ^ (κ * ε) *
            (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-1 - s.val / 2)) +
            t * (C * (n : ℝ) ^ (κ * ε) *
              (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-1 - s.val / 2)) :=
          add_le_add (mul_le_mul_of_nonneg_left (h₀.2.2.2 i j hi hj) ht0)
            (mul_le_mul_of_nonneg_left (h₁.2.2.2 i j hi hj) ht)
        _ = _ := by ring
  · filter_upwards [hcoeff₀, hcoeff₁] with x h₀ h₁
    refine ⟨fun i r => ⟨add_nonneg (mul_nonneg ht0 (h₀.1 i r).1)
      (mul_nonneg ht (h₁.1 i r).1), ?_, ?_⟩, ?_⟩
    · have hh₀ := mul_le_mul_of_nonneg_left (h₀.1 i r).2.1 ht0
      have hh₁ := mul_le_mul_of_nonneg_left (h₁.1 i r).2.1 ht
      nlinarith only [hh₀, hh₁]
    · intro hr
      have hh₀ := mul_le_mul_of_nonneg_left ((h₀.1 i r).2.2 hr) ht0
      have hh₁ := mul_le_mul_of_nonneg_left ((h₁.1 i r).2.2 hr) ht
      nlinarith only [hh₀, hh₁]
    · intro z
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      have he : (∑ i, ∑ j, z i * ((1 - t) * M₀ x i j + t * M₁ x i j) * z j) =
          (1 - t) * (∑ i, ∑ j, z i * M₀ x i j * z j) +
            t * (∑ i, ∑ j, z i * M₁ x i j * z j) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [he, h₀.2 z, h₁.2 z]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro r _
      ring

end Riesz2.PeriodizedMatrixInterpolation
