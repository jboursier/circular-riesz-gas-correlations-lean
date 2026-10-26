/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.GlobalCommutatorsPart2

/-!
# Retained spatial commutator rows

Estimates for the retained convolution in the proof of Lemma 5.13, using
the cyclic distances, resolvent and two smooth cutoffs. All sums use
counting measure.
-/

@[expose] public section
noncomputable section

open Matrix Finset
open scoped BigOperators Fin.NatCast

namespace Riesz2.GlobalCommutators
namespace Internal

/-- Shortest-arc transport away from the observed column, for the first
and mixed differences in the proof of Lemma 5.13. -/
theorem spatial_localized_increment (N : ℕ+) (i j l : Fin (N : ℕ))
    (t C : ℝ) (ht : 0 ≤ t) (hC : 0 ≤ C) (f : Fin (N : ℕ) → ℝ)
    (hinc : ∀ k, |f (k + 1) - f k| ≤ C * weightRadius N k j ^ (-t))
    (hl : (Riesz1.cyclicIndexDistance N i l : ℝ) ≤ weightRadius N i j / 2) :
    |f l - f i| ≤ C * 2 ^ t * weightRadius N i j ^ (-t) *
      (Riesz1.cyclicIndexDistance N i l : ℝ) := by
  let D := weightRadius N i j
  have hD : 0 < D := by dsimp [D]; linarith [one_le_weightRadius N i j]
  have hb (k : Fin (N : ℕ)) (hk : Riesz1.cyclicIndexDistance N i k ≤
      Riesz1.cyclicIndexDistance N i l) :
      |f (k + 1) - f k| ≤ C * 2 ^ t * D ^ (-t) := by
    have htri : (Riesz1.cyclicIndexDistance N i j : ℝ) ≤
        (Riesz1.cyclicIndexDistance N i k : ℝ) +
        (Riesz1.cyclicIndexDistance N k j : ℝ) := by
      exact_mod_cast cyclicIndexDistance_triangle i k j
    have hk' : (Riesz1.cyclicIndexDistance N i k : ℝ) ≤
        (Riesz1.cyclicIndexDistance N i l : ℝ) := by exact_mod_cast hk
    have hgeom : D / 2 ≤ weightRadius N k j := by
      dsimp [weightRadius, D] at *
      linarith
    calc
      _ ≤ C * weightRadius N k j ^ (-t) := hinc k
      _ ≤ C * (D / 2) ^ (-t) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos (by positivity) hgeom (by linarith)) hC
      _ = _ := by
        rw [Real.div_rpow hD.le (by norm_num),
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        simp only [div_eq_mul_inv, inv_inv]
        ring
  have hh := oscillation_on_short_arc N i l f
    (C * 2 ^ t * D ^ (-t)) (by positivity) hb
  nlinarith only [hh]

/-- The split at `D^(s/2)` in the proof of Lemma 5.13. This is an internal scalar summation
lemma. Applications establish both bounds for the actual increments. -/
theorem spatial_split_sum (s : Riesz1.RieszExponent) (N : ℕ+)
    (i : Fin (N : ℕ)) (D A L : ℝ) (hD : 1 ≤ D) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (c u : Fin (N : ℕ) → ℝ)
    (hc : ∀ l, |c l| ≤ A * weightRadius N l i ^ (-(2 - s.val)))
    (hu₀ : ∀ l, |c l * u l| ≤ |c l| * L * D ^ (-(1 + s.val / 2)))
    (hu₁ : ∀ l, |c l * u l| ≤
      |c l| * L * weightRadius N l i * D ^ (-(1 + s.val))) :
    (∑ l, |c l * u l|) ≤
      (2 / s.val + 2 * (1 + 1 / (1 - s.val))) * A * L *
        D ^ (-(1 + s.val - s.val ^ 2 / 2)) := by
  classical
  let S := D ^ (s.val / 2)
  let J := univ.filter (fun l => weightRadius N l i ≤ S)
  have hDpos : 0 < D := by linarith
  have hS : 1 ≤ S := Real.one_le_rpow hD (by linarith [s.property.1])
  have hr (l) : 0 < weightRadius N l i := by linarith [one_le_weightRadius N l i]
  have hshort : (∑ l ∈ J, |c l * u l|) ≤
      A * L * D ^ (-(1 + s.val)) * (2 / s.val * S ^ s.val) := by
    calc
      _ ≤ ∑ l ∈ J, (A * L * D ^ (-(1 + s.val))) *
          weightRadius N l i ^ (-(1 - s.val)) := by
        apply sum_le_sum
        intro l _
        calc
          _ ≤ |c l| * L * weightRadius N l i * D ^ (-(1 + s.val)) := hu₁ l
          _ ≤ (A * weightRadius N l i ^ (-(2 - s.val))) * L *
              weightRadius N l i * D ^ (-(1 + s.val)) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hc l) hL)
                (hr l).le) (by positivity)
          _ = _ := by
            rw [show -(2 - s.val) = -(1 - s.val) - 1 by ring,
              Real.rpow_sub (hr l), Real.rpow_one]
            field_simp [(hr l).ne']
      _ = (A * L * D ^ (-(1 + s.val))) *
          ∑ l ∈ J, weightRadius N l i ^ (-(1 - s.val)) := (mul_sum ..).symm
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [sub_sub_cancel, show 1 - (1 - s.val) = s.val by ring] using
          sum_weightRadius_le_of_lt_one N i (t := 1 - s.val)
            (by linarith [s.property.2]) (by linarith [s.property.1]) hS
  have hlong : (∑ l ∈ Jᶜ, |c l * u l|) ≤
      A * L * D ^ (-(1 + s.val / 2)) *
        (2 * (1 + 1 / (1 - s.val)) * S ^ (-(1 - s.val))) := by
    calc
      _ ≤ ∑ l ∈ Jᶜ, (A * L * D ^ (-(1 + s.val / 2))) *
          weightRadius N l i ^ (-(2 - s.val)) := by
        apply sum_le_sum
        intro l _
        exact (hu₀ l).trans (by
          have hh := mul_le_mul_of_nonneg_right (hc l)
            (show 0 ≤ L * D ^ (-(1 + s.val / 2)) by positivity)
          nlinarith only [hh])
      _ = (A * L * D ^ (-(1 + s.val / 2))) *
          ∑ l ∈ Jᶜ, weightRadius N l i ^ (-(2 - s.val)) := (mul_sum ..).symm
      _ ≤ (A * L * D ^ (-(1 + s.val / 2))) *
          ∑ l ∈ univ.filter (fun l => S ≤ weightRadius N l i),
            weightRadius N l i ^ (-(2 - s.val)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply sum_le_sum_of_subset_of_nonneg
        · intro l hl
          have hl' : S < weightRadius N l i := by simpa [J] using hl
          simp only [mem_filter, mem_univ, true_and]
          exact hl'.le
        · intro l _ _; exact Real.rpow_nonneg (hr l).le _
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [show 2 - s.val - 1 = 1 - s.val by ring,
          show 1 - (2 - s.val) = -(1 - s.val) by ring] using
          sum_weightRadius_tail_le N i (t := 2 - s.val)
            (by linarith [s.property.2]) hS
  have hp₀ : D ^ (-(1 + s.val)) * S ^ s.val =
      D ^ (-(1 + s.val - s.val ^ 2 / 2)) := by
    dsimp [S]
    rw [← Real.rpow_mul hDpos.le, ← Real.rpow_add hDpos]
    congr 1; ring
  have hp₁ : D ^ (-(1 + s.val / 2)) * S ^ (-(1 - s.val)) =
      D ^ (-(1 + s.val - s.val ^ 2 / 2)) := by
    dsimp [S]
    rw [← Real.rpow_mul hDpos.le, ← Real.rpow_add hDpos]
    congr 1; ring
  rw [← sum_add_sum_compl J]
  calc
    _ ≤ A * L * D ^ (-(1 + s.val)) * (2 / s.val * S ^ s.val) +
        A * L * D ^ (-(1 + s.val / 2)) *
          (2 * (1 + 1 / (1 - s.val)) * S ^ (-(1 - s.val))) := add_le_add hshort hlong
    _ = _ := by
      calc
        _ = (2 / s.val) * A * L * (D ^ (-(1 + s.val)) * S ^ s.val) +
            (2 * (1 + 1 / (1 - s.val))) * A * L *
              (D ^ (-(1 + s.val / 2)) * S ^ (-(1 - s.val))) := by ring
        _ = _ := by rw [hp₀, hp₁]; ring

/-- First and mixed differences transported along the retained arc in
the proof of Lemma 5.13. -/
theorem spatial_error_oscillation (s : Riesz1.RieszExponent) (N : ℕ+)
    (E : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hE : ∀ i j, |E i j| ≤ L * weightRadius N i j ^ (-(1 + s.val / 2)))
    (hΔ : ∀ i j, |E i j - E (i + 1) j| + |E i j - E i (j + 1)| ≤
      L * weightRadius N i j ^ (-(1 + s.val)))
    (hΔ₂ : ∀ i j, |(E i j - E (i + 1) j) -
      (E i (j + 1) - E (i + 1) (j + 1))| ≤
        L * weightRadius N i j ^ (-(2 + s.val)))
    (i j l : Fin (N : ℕ))
    (hl : (Riesz1.cyclicIndexDistance N i l : ℝ) ≤ weightRadius N i j / 2) :
    let M := 1 + 2 ^ (2 + s.val)
    |E l j - E i j| ≤ M * L * weightRadius N i j ^ (-(1 + s.val / 2)) ∧
    |E l j - E i j| ≤ M * L *
      (Riesz1.cyclicIndexDistance N i l : ℝ) * weightRadius N i j ^ (-(1 + s.val)) ∧
    |(E l (j + 1) - E l j) - (E i (j + 1) - E i j)| ≤ M * L *
      (Riesz1.cyclicIndexDistance N i l : ℝ) * weightRadius N i j ^ (-(2 + s.val)) := by
  let D := weightRadius N i j
  let M := 1 + (2 : ℝ) ^ (2 + s.val)
  have hD : 0 < D := by dsimp [D]; linarith [one_le_weightRadius N i j]
  have htri : (Riesz1.cyclicIndexDistance N i j : ℝ) ≤
      (Riesz1.cyclicIndexDistance N i l : ℝ) +
      (Riesz1.cyclicIndexDistance N l j : ℝ) := by
    exact_mod_cast cyclicIndexDistance_triangle i l j
  have hgeom : D / 2 ≤ weightRadius N l j := by
    dsimp [D, weightRadius] at *
    linarith
  have hp₀ : (2 : ℝ) ^ (1 + s.val / 2) ≤ (2 : ℝ) ^ (2 + s.val) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [s.property.1])
  have hp₁ : (2 : ℝ) ^ (1 + s.val) ≤ M := by
    dsimp [M]
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show 1 + s.val ≤ 2 + s.val by linarith)
    linarith
  have hp₂ : (2 : ℝ) ^ (2 + s.val) ≤ M := by dsimp [M]; linarith
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ |E l j| + |E i j| := abs_sub _ _
      _ ≤ L * weightRadius N l j ^ (-(1 + s.val / 2)) +
          L * D ^ (-(1 + s.val / 2)) := add_le_add (hE l j) (hE i j)
      _ ≤ L * (D / 2) ^ (-(1 + s.val / 2)) +
          L * D ^ (-(1 + s.val / 2)) := by
        exact add_le_add (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by positivity) hgeom (by linarith [s.property.1])) hL)
          (le_refl _)
      _ = (1 + (2 : ℝ) ^ (1 + s.val / 2)) * L * D ^ (-(1 + s.val / 2)) := by
        rw [Real.div_rpow hD.le (by norm_num),
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        simp only [div_eq_mul_inv, inv_inv]
        ring
      _ ≤ _ := by
        have hsum : 1 + (2 : ℝ) ^ (1 + s.val / 2) ≤ M := by
          dsimp [M]; linarith only [hp₀]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hsum hL) (by positivity)
  · have hh := spatial_localized_increment N i j l (1 + s.val) L
      (by linarith [s.property.1]) hL (fun k => E k j) (fun k => by
        rw [abs_sub_comm]
        exact (le_add_of_nonneg_right (abs_nonneg _)).trans (hΔ k j)) hl
    exact hh.trans (by
      have hh' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp₁ hL)
        (show 0 ≤ D ^ (-(1 + s.val)) * (Riesz1.cyclicIndexDistance N i l : ℝ) by positivity)
      nlinarith only [hh'])
  · have hh := spatial_localized_increment N i j l (2 + s.val) L
      (by linarith [s.property.1]) hL (fun k => E k (j + 1) - E k j)
      (fun k => by
        convert hΔ₂ k j using 1
        congr 1; ring) hl
    exact hh.trans (by
      have hh' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp₂ hL)
        (show 0 ≤ D ^ (-(2 + s.val)) * (Riesz1.cyclicIndexDistance N i l : ℝ) by positivity)
      nlinarith only [hh'])

/-- Entry envelope, signed mass and first absolute moment of the actual
retained resolvent in the proof of Lemma 5.13. -/
theorem spatial_retained_coefficient_bounds (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (a : ℝ) (ha : 0 < a) (B : ℝ) (i₀ i : Fin (N : ℕ)),
      let r := weightRadius N i i₀
      let μ := a + B ^ 2 / a
      let c := fun l => factorizationMatrix s N hN a ha B i l *
        CutoffApproximation.scalarCutoff (16 * (Riesz1.cyclicIndexDistance N i l : ℝ) / r)
      16 ≤ r →
      (∀ l, |c l| ≤ C * μ * weightRadius N l i ^ (-(2 - s.val))) ∧
      |∑ l, c l| ≤ C * μ * r ^ (s.val - 1) ∧
      (∑ l, |c l| * (Riesz1.cyclicIndexDistance N i l : ℝ)) ≤ C * μ * r ^ s.val := by
  obtain ⟨C₀, hC₀, hb⟩ := factorization_entry_bound hz s
  obtain ⟨C₁, hC₁, hm⟩ := spatial_smooth_retained_mass hz s
  let C := C₀ + C₁ + C₀ * (2 / s.val)
  have hprod : 0 ≤ C₀ * (2 / s.val) := by have := s.property.1; positivity
  have hCf : C₀ ≤ C := by dsimp [C]; linarith
  have hCm : C₁ ≤ C := by dsimp [C]; linarith
  have hCp : C₀ * (2 / s.val) ≤ C := by dsimp [C]; linarith
  refine ⟨C, by dsimp [C]; have := s.property.1; positivity, ?_⟩
  intro N hN a ha B i₀ i r μ c hri
  have hr : 0 < r := by linarith
  have hμ : 0 < μ := factorization_shift_pos ha B
  have hbound (l) : |c l| ≤ C₀ * μ * weightRadius N l i ^ (-(2 - s.val)) := by
    have hζ := CutoffApproximation.scalarCutoff_nonneg
      (16 * (Riesz1.cyclicIndexDistance N i l : ℝ) / r)
    have hζ' := CutoffApproximation.scalarCutoff_le_one
      (16 * (Riesz1.cyclicIndexDistance N i l : ℝ) / r)
    change |factorizationMatrix s N hN a ha B i l *
      CutoffApproximation.scalarCutoff (16 * (Riesz1.cyclicIndexDistance N i l : ℝ) / r)| ≤ _
    rw [abs_mul, abs_of_nonneg hζ]
    exact (mul_le_mul_of_nonneg_left hζ' (abs_nonneg _)).trans (by
      simpa only [mul_one, weightRadius_eq_comm] using hb N hN a ha B i l)
  have hzero (l) (hl : r / 8 ≤ (Riesz1.cyclicIndexDistance N i l : ℝ)) : c l = 0 := by
    have hh : 2 ≤ 16 * (Riesz1.cyclicIndexDistance N i l : ℝ) / r :=
      (le_div_iff₀ hr).mpr (by linarith)
    simp only [c, CutoffApproximation.scalarCutoff_eq_zero hh, mul_zero]
  refine ⟨fun l => (hbound l).trans (by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCf hμ.le)
      (Real.rpow_nonneg (by linarith [one_le_weightRadius N l i]) _)),
    (hm N hN a ha B i₀ i hri).trans (by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCm hμ.le) (by positivity)), ?_⟩
  let J := univ.filter (fun l => weightRadius N l i ≤ r)
  have hsupport : ∑ l, |c l| * (Riesz1.cyclicIndexDistance N i l : ℝ) =
      ∑ l ∈ J, |c l| * (Riesz1.cyclicIndexDistance N i l : ℝ) := by
    symm
    apply sum_subset (subset_univ _)
    intro l _ hl
    have hh : r < weightRadius N l i := by simpa only [J, mem_filter, mem_univ,
      true_and, not_le] using hl
    rw [weightRadius_eq_comm] at hh
    rw [hzero l (by linarith), abs_zero, zero_mul]
  rw [hsupport]
  calc
    _ ≤ (C₀ * μ) * ∑ l ∈ J, weightRadius N l i ^ (-(1 - s.val)) := by
      rw [mul_sum]
      apply sum_le_sum
      intro l _
      have hl : 0 < weightRadius N l i := by linarith [one_le_weightRadius N l i]
      calc
        _ ≤ (C₀ * μ * weightRadius N l i ^ (-(2 - s.val))) * weightRadius N l i := by
          apply mul_le_mul (hbound l) _ (by positivity) (by positivity)
          rw [weightRadius_eq_comm]; linarith
        _ = _ := by
          rw [show -(2 - s.val) = -(1 - s.val) - 1 by ring,
            Real.rpow_sub hl, Real.rpow_one]
          field_simp [hl.ne']
    _ ≤ (C₀ * μ) * (2 / s.val * r ^ s.val) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [sub_sub_cancel, show 1 - (1 - s.val) = s.val by ring] using
        sum_weightRadius_le_of_lt_one N i (t := 1 - s.val)
          (by linarith [s.property.2]) (by linarith [s.property.1]) (by linarith : 1 ≤ r)
    _ ≤ C * μ * r ^ s.val := by
      have hh := mul_le_mul_of_nonneg_right hCp (show 0 ≤ μ * r ^ s.val by positivity)
      nlinarith only [hh]

/-- The two pointwise estimates before the outer cutoff in the proof of Lemma 5.13. The matrix hypotheses are internal
input interfaces, discharged from the structural assumptions below. -/
theorem spatial_retained_error_rows (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (a : ℝ) (ha : 0 < a) (B : ℝ) (i₀ i : Fin (N : ℕ)) (L : ℝ),
      0 ≤ L → ∀ E : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ,
      (∀ k j, |E k j| ≤ L * weightRadius N k j ^ (-(1 + s.val / 2))) →
      (∀ k j, |E k j - E (k + 1) j| + |E k j - E k (j + 1)| ≤
        L * weightRadius N k j ^ (-(1 + s.val))) →
      (∀ k j, |(E k j - E (k + 1) j) -
        (E k (j + 1) - E (k + 1) (j + 1))| ≤
          L * weightRadius N k j ^ (-(2 + s.val))) →
      let r := weightRadius N i i₀
      let μ := a + B ^ 2 / a
      let c := fun l => factorizationMatrix s N hN a ha B i l *
        CutoffApproximation.scalarCutoff (16 * (Riesz1.cyclicIndexDistance N i l : ℝ) / r)
      let F := fun j => ∑ l, c l * E l j
      16 ≤ r → ∀ j, r / 4 ≤ weightRadius N i j →
      |F j| ≤ C * μ * L * (r ^ (s.val - 1) * weightRadius N i j ^ (-(1 + s.val / 2)) +
        weightRadius N i j ^ (-(1 + s.val - s.val ^ 2 / 2))) ∧
      |F (j + 1) - F j| ≤ C * μ * L *
        (r ^ (s.val - 1) * weightRadius N i j ^ (-(1 + s.val)) +
          r ^ s.val * weightRadius N i j ^ (-(2 + s.val))) := by
  obtain ⟨C₀, hC₀, hb⟩ := spatial_retained_coefficient_bounds hz s
  let M := 1 + (2 : ℝ) ^ (2 + s.val)
  let H := 2 / s.val + 2 * (1 + 1 / (1 - s.val))
  let C := C₀ * (1 + M * H + M)
  have hM : 0 < M := by dsimp [M]; positivity
  have hH : 0 < H := by dsimp [H]; have := s.property.1; have := s.property.2; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hC₀ : C₀ ≤ C := by
    have := mul_nonneg (show 0 ≤ C₀ by positivity) (show 0 ≤ M * H + M by positivity)
    dsimp [C]; nlinarith only [this]
  have hCM : C₀ * M ≤ C := by
    have := mul_nonneg (show 0 ≤ C₀ by positivity) (show 0 ≤ 1 + M * H by positivity)
    dsimp [C]; nlinarith only [this]
  have hCH : H * C₀ * M ≤ C := by
    have := mul_nonneg (show 0 ≤ C₀ by positivity) (show 0 ≤ 1 + M by positivity)
    dsimp [C]; nlinarith only [this]
  refine ⟨C, hC, ?_⟩
  intro N hN a ha B i₀ i L hL E hE hΔ hΔ₂ r μ c F hri j hj
  have hr : 0 < r := by linarith
  have hμ : 0 < μ := factorization_shift_pos ha B
  let D := weightRadius N i j
  have hD : 1 ≤ D := one_le_weightRadius N i j
  have hDpos : 0 < D := by linarith
  obtain ⟨hc, hm, hmoment⟩ := hb N hN a ha B i₀ i hri
  change (∀ l, |c l| ≤ C₀ * μ * weightRadius N l i ^ (-(2 - s.val))) at hc
  change |∑ l, c l| ≤ C₀ * μ * r ^ (s.val - 1) at hm
  change (∑ l, |c l| * (Riesz1.cyclicIndexDistance N i l : ℝ)) ≤ C₀ * μ * r ^ s.val at hmoment
  have hzero (l) (hl : r / 8 ≤ (Riesz1.cyclicIndexDistance N i l : ℝ)) : c l = 0 := by
    have hh : 2 ≤ 16 * (Riesz1.cyclicIndexDistance N i l : ℝ) / r :=
      (le_div_iff₀ hr).mpr (by linarith)
    simp only [c, CutoffApproximation.scalarCutoff_eq_zero hh, mul_zero]
  have hosc (l) (hl : (Riesz1.cyclicIndexDistance N i l : ℝ) < r / 8) :=
    spatial_error_oscillation s N E L hL hE hΔ hΔ₂ i j l (by linarith)
  have hshort (l) : |c l * (E l j - E i j)| ≤
      |c l| * (M * L) * weightRadius N l i * D ^ (-(1 + s.val)) := by
    by_cases hl : r / 8 ≤ (Riesz1.cyclicIndexDistance N i l : ℝ)
    · simp only [hzero l hl, zero_mul, abs_zero, le_refl]
    · have hh := (hosc l (lt_of_not_ge hl)).2.1
      have hdist : (Riesz1.cyclicIndexDistance N i l : ℝ) ≤ weightRadius N l i := by
        rw [weightRadius_eq_comm]; linarith
      rw [abs_mul]
      calc
        _ ≤ |c l| * (M * L * (Riesz1.cyclicIndexDistance N i l : ℝ) * D ^ (-(1 + s.val))) :=
          mul_le_mul_of_nonneg_left hh (abs_nonneg _)
        _ ≤ _ := by
          have hh' := mul_le_mul_of_nonneg_right hdist
            (show 0 ≤ |c l| * M * L * D ^ (-(1 + s.val)) by positivity)
          nlinarith only [hh']
  have hcoarse (l) : |c l * (E l j - E i j)| ≤
      |c l| * (M * L) * D ^ (-(1 + s.val / 2)) := by
    by_cases hl : r / 8 ≤ (Riesz1.cyclicIndexDistance N i l : ℝ)
    · simp only [hzero l hl, zero_mul, abs_zero, le_refl]
    · rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hosc l (lt_of_not_ge hl)).1
        (abs_nonneg _)).trans_eq (by ring)
  have hrem := spatial_split_sum s N i D (C₀ * μ) (M * L) hD
    (by positivity) (by positivity) c (fun l => E l j - E i j) hc hcoarse hshort
  have hrem' : (∑ l, |c l * (E l j - E i j)|) ≤
      C * μ * L * D ^ (-(1 + s.val - s.val ^ 2 / 2)) := by
    calc
      _ ≤ H * (C₀ * μ) * (M * L) * D ^ (-(1 + s.val - s.val ^ 2 / 2)) := hrem
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hCH
          (show 0 ≤ μ * L * D ^ (-(1 + s.val - s.val ^ 2 / 2)) by positivity)
        nlinarith only [hh]
  have hmass (f : Fin (N : ℕ) → ℝ) :
      |∑ l, c l * f l| ≤ |∑ l, c l| * |f i| + ∑ l, |c l * (f l - f i)| := by
    have hid : (∑ l, c l * f l) = (∑ l, c l) * f i + ∑ l, c l * (f l - f i) := by
      simp only [mul_sub, sum_sub_distrib, ← sum_mul]; ring
    rw [hid]
    exact (abs_add_le ..).trans (add_le_add (le_of_eq (abs_mul ..)) (abs_sum_le_sum_abs ..))
  refine ⟨?_, ?_⟩
  · calc
      _ ≤ |∑ l, c l| * |E i j| + ∑ l, |c l * (E l j - E i j)| := hmass (fun l => E l j)
      _ ≤ (C₀ * μ * r ^ (s.val - 1)) * (L * D ^ (-(1 + s.val / 2))) +
          C * μ * L * D ^ (-(1 + s.val - s.val ^ 2 / 2)) := by
        exact add_le_add (mul_le_mul hm (hE i j) (abs_nonneg _) (by positivity)) hrem'
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hC₀
          (show 0 ≤ μ * r ^ (s.val - 1) * L * D ^ (-(1 + s.val / 2)) by positivity)
        nlinarith only [hh]
  · have hΔi : |E i (j + 1) - E i j| ≤ L * D ^ (-(1 + s.val)) := by
      rw [abs_sub_comm]
      exact (le_add_of_nonneg_left (abs_nonneg _)).trans (hΔ i j)
    have hrem₂ : (∑ l, |c l * ((E l (j + 1) - E l j) - (E i (j + 1) - E i j))|) ≤
        C * μ * L * r ^ s.val * D ^ (-(2 + s.val)) := by
      calc
        _ ≤ ∑ l, (M * L * D ^ (-(2 + s.val))) *
            (|c l| * (Riesz1.cyclicIndexDistance N i l : ℝ)) := by
          apply sum_le_sum
          intro l _
          by_cases hl : r / 8 ≤ (Riesz1.cyclicIndexDistance N i l : ℝ)
          · simp only [hzero l hl, zero_mul, abs_zero, mul_zero, le_refl]
          · rw [abs_mul]
            exact (mul_le_mul_of_nonneg_left (hosc l (lt_of_not_ge hl)).2.2
              (abs_nonneg _)).trans_eq (by ring)
        _ = (M * L * D ^ (-(2 + s.val))) *
            ∑ l, |c l| * (Riesz1.cyclicIndexDistance N i l : ℝ) := (mul_sum ..).symm
        _ ≤ (M * L * D ^ (-(2 + s.val))) * (C₀ * μ * r ^ s.val) :=
          mul_le_mul_of_nonneg_left hmoment (by positivity)
        _ ≤ _ := by
          have hh := mul_le_mul_of_nonneg_right hCM
            (show 0 ≤ μ * L * r ^ s.val * D ^ (-(2 + s.val)) by positivity)
          nlinarith only [hh]
    have heq : F (j + 1) - F j = ∑ l, c l * (E l (j + 1) - E l j) := by
      simp only [F, mul_sub, sum_sub_distrib]
    rw [heq]
    calc
      _ ≤ |∑ l, c l| * |E i (j + 1) - E i j| +
          ∑ l, |c l * ((E l (j + 1) - E l j) - (E i (j + 1) - E i j))| :=
        hmass (fun l => E l (j + 1) - E l j)
      _ ≤ (C₀ * μ * r ^ (s.val - 1)) * (L * D ^ (-(1 + s.val))) +
          C * μ * L * r ^ s.val * D ^ (-(2 + s.val)) :=
        add_le_add (mul_le_mul hm hΔi (abs_nonneg _) (by positivity)) hrem₂
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hC₀
          (show 0 ≤ μ * r ^ (s.val - 1) * L * D ^ (-(1 + s.val)) by positivity)
        nlinarith only [hh]

/-- On rows of radius at least `16K`, the two spatial cutoffs force
every retained entry beyond the first tail cutoff. This exact identity
avoids differentiating that cutoff in the far-row estimates of the proof of Lemma 5.13. -/
theorem spatial_far_tail_identity (N : ℕ+) (i : Fin (N : ℕ))
    (r K : ℝ) (hr : 0 < r) (hK : 0 < K) (hKr : 16 * K ≤ r)
    (A E : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ) (j : Fin (N : ℕ)) :
    let ζ := fun j => 1 - CutoffApproximation.scalarCutoff
      (4 * (Riesz1.cyclicIndexDistance N i j : ℝ) / r)
    let c := fun l => A i l * CutoffApproximation.scalarCutoff
      (16 * (Riesz1.cyclicIndexDistance N i l : ℝ) / r)
    ζ j * (∑ l, c l * ((1 - CutoffApproximation.scalarCutoff
      ((Riesz1.cyclicIndexDistance N l j : ℝ) / K)) * E l j)) =
      ζ j * (∑ l, c l * E l j) := by
  intro ζ c
  by_cases hj : (Riesz1.cyclicIndexDistance N i j : ℝ) ≤ r / 4
  · have hz : ζ j = 0 := by
      have hh : 4 * (Riesz1.cyclicIndexDistance N i j : ℝ) / r ≤ 1 :=
        (div_le_one hr).mpr (by linarith)
      simp only [ζ, CutoffApproximation.scalarCutoff_eq_one hh, sub_self]
    simp only [hz, zero_mul]
  · congr 1
    apply sum_congr rfl
    intro l _
    by_cases hl : r / 8 ≤ (Riesz1.cyclicIndexDistance N i l : ℝ)
    · have hc : c l = 0 := by
        have hh : 2 ≤ 16 * (Riesz1.cyclicIndexDistance N i l : ℝ) / r :=
          (le_div_iff₀ hr).mpr (by linarith)
        simp only [c, CutoffApproximation.scalarCutoff_eq_zero hh, mul_zero]
      simp only [hc, zero_mul]
    · have htri : (Riesz1.cyclicIndexDistance N i j : ℝ) ≤
          (Riesz1.cyclicIndexDistance N i l : ℝ) +
          (Riesz1.cyclicIndexDistance N l j : ℝ) := by
        exact_mod_cast cyclicIndexDistance_triangle i l j
      have hh : 2 ≤ (Riesz1.cyclicIndexDistance N l j : ℝ) / K :=
        (le_div_iff₀ hK).mpr (by linarith)
      rw [CutoffApproximation.scalarCutoff_eq_zero hh, sub_zero, one_mul]

/-- Size, support and first increment of the actual outer cutoff in
the proof of Lemma 5.13. The increment support includes
the adjacent index, including wraparound. -/
theorem spatial_outer_cutoff :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (_hN : 2 ≤ (N : ℕ))
      (i : Fin (N : ℕ)) (r : ℝ), 16 ≤ r →
      let ζ := fun j => 1 - CutoffApproximation.scalarCutoff
        (4 * (Riesz1.cyclicIndexDistance N i j : ℝ) / r)
      (∀ j, 0 ≤ ζ j ∧ ζ j ≤ 1) ∧
      (∀ j, |ζ (j + 1) - ζ j| ≤ C / r) ∧
      (∀ j, ζ j ≠ 0 ∨ ζ (j + 1) ≠ 0 → r / 4 ≤ weightRadius N i j) ∧
      (∀ j, ζ (j + 1) - ζ j ≠ 0 → weightRadius N i j ≤ r) := by
  obtain ⟨C, hC, hb⟩ := CutoffApproximation.scalarCutoff_derivative_bound 1
  have hLip (x y : ℝ) : |CutoffApproximation.scalarCutoff y -
      CutoffApproximation.scalarCutoff x| ≤ C * |y - x| := by
    have hh := Convex.norm_image_sub_le_of_norm_deriv_le
      (s := Set.univ) (f := CutoffApproximation.scalarCutoff)
      (fun z _ => CutoffApproximation.scalarCutoff_contDiff.differentiable
        (by simp) z) (fun z _ => by simpa only [iteratedDeriv_one, Real.norm_eq_abs] using hb z)
      convex_univ (Set.mem_univ x) (Set.mem_univ y)
    simpa only [Real.norm_eq_abs] using hh
  refine ⟨4 * C, by positivity, ?_⟩
  intro N hN i r hr ζ
  have hrpos : 0 < r := by linarith
  have hd (j : Fin (N : ℕ)) :
      |(Riesz1.cyclicIndexDistance N i (j + 1) : ℝ) -
        (Riesz1.cyclicIndexDistance N i j : ℝ)| ≤ 1 := by
    have hadj : Riesz1.cyclicIndexDistance N j (j + 1) = 1 := by
      simpa only [Nat.cast_one] using
        GlobalReferenceErrorInternal.distance_add_length N j (r := 1) (by omega)
    have hh := DerivativeCommutators.weightRadius_lipschitz N i (j + 1) j
    rw [cyclicIndexDistance_comm' N (j + 1) j, hadj] at hh
    simpa only [weightRadius_eq_comm, add_sub_add_left_eq_sub, Nat.cast_one] using hh
  have hzero (j) (hj : (Riesz1.cyclicIndexDistance N i j : ℝ) ≤ r / 4) : ζ j = 0 := by
    have hh : 4 * (Riesz1.cyclicIndexDistance N i j : ℝ) / r ≤ 1 :=
      (div_le_one hrpos).mpr (by linarith)
    simp only [ζ, CutoffApproximation.scalarCutoff_eq_one hh, sub_self]
  have hone (j) (hj : r / 2 ≤ (Riesz1.cyclicIndexDistance N i j : ℝ)) : ζ j = 1 := by
    have hh : 2 ≤ 4 * (Riesz1.cyclicIndexDistance N i j : ℝ) / r :=
      (le_div_iff₀ hrpos).mpr (by linarith)
    simp only [ζ, CutoffApproximation.scalarCutoff_eq_zero hh, sub_zero]
  have hbounds (j) : 0 ≤ ζ j ∧ ζ j ≤ 1 := by
    have h0 := CutoffApproximation.scalarCutoff_nonneg
      (4 * (Riesz1.cyclicIndexDistance N i j : ℝ) / r)
    have h1 := CutoffApproximation.scalarCutoff_le_one
      (4 * (Riesz1.cyclicIndexDistance N i j : ℝ) / r)
    dsimp [ζ]
    constructor <;> linarith
  refine ⟨hbounds, ?_, ?_, ?_⟩
  · intro j
    have hh := hLip (4 * (Riesz1.cyclicIndexDistance N i j : ℝ) / r)
      (4 * (Riesz1.cyclicIndexDistance N i (j + 1) : ℝ) / r)
    have hid : |4 * (Riesz1.cyclicIndexDistance N i (j + 1) : ℝ) / r -
        4 * (Riesz1.cyclicIndexDistance N i j : ℝ) / r| =
        4 / r * |(Riesz1.cyclicIndexDistance N i (j + 1) : ℝ) -
          (Riesz1.cyclicIndexDistance N i j : ℝ)| := by
      rw [show 4 * (Riesz1.cyclicIndexDistance N i (j + 1) : ℝ) / r -
        4 * (Riesz1.cyclicIndexDistance N i j : ℝ) / r =
        (4 / r) * ((Riesz1.cyclicIndexDistance N i (j + 1) : ℝ) -
          (Riesz1.cyclicIndexDistance N i j : ℝ)) by ring,
        abs_mul, abs_of_pos (by positivity : 0 < 4 / r)]
    rw [hid] at hh
    have heq : |ζ (j + 1) - ζ j| =
        |CutoffApproximation.scalarCutoff (4 * (Riesz1.cyclicIndexDistance N i (j + 1) : ℝ) / r) -
          CutoffApproximation.scalarCutoff (4 * (Riesz1.cyclicIndexDistance N i j : ℝ) / r)| := by
      dsimp [ζ]
      rw [show (1 - CutoffApproximation.scalarCutoff
        (4 * (Riesz1.cyclicIndexDistance N i (j + 1) : ℝ) / r)) -
        (1 - CutoffApproximation.scalarCutoff (4 * (Riesz1.cyclicIndexDistance N i j : ℝ) / r)) =
        -(CutoffApproximation.scalarCutoff (4 * (Riesz1.cyclicIndexDistance N i (j + 1) : ℝ) / r) -
          CutoffApproximation.scalarCutoff (4 * (Riesz1.cyclicIndexDistance N i j : ℝ) / r)) by ring,
        abs_neg]
    rw [heq]
    exact hh.trans (by
      have hh' := mul_le_mul_of_nonneg_left (hd j) (show 0 ≤ C * (4 / r) by positivity)
      convert hh' using 1 <;> ring)
  · intro j hj
    have hh := (abs_le.mp (hd j)).2
    dsimp [weightRadius]
    rcases hj with hj | hj
    · have := mt (hzero j) hj; linarith
    · have := mt (hzero (j + 1)) hj; linarith
  · intro j hj
    have hh := (abs_le.mp (hd j)).1
    by_contra h
    have hj' : r < weightRadius N i j := lt_of_not_ge h
    rw [weightRadius] at hj'
    have hz₀ := hone j (by linarith)
    have hz₁ := hone (j + 1) (by linarith)
    exact hj (by rw [hz₀, hz₁, sub_self])

/-- Power bookkeeping for the localized rows in the proof of Lemma 5.13. -/
theorem spatial_row_profiles (s : Riesz1.RieszExponent) (r D : ℝ)
    (hr : 1 ≤ r) (hD : r / 4 ≤ D) :
    let q := 1 + s.val / 2
    let t := 1 + s.val - s.val ^ 2 / 2
    let H := 1 + (4 : ℝ) ^ (t - q)
    (r ^ (s.val - 1) * D ^ (-q) + D ^ (-t) ≤ H * r ^ (q - t) * D ^ (-q)) ∧
    (r ^ (s.val - 1) * D ^ (-(1 + s.val)) + r ^ s.val * D ^ (-(2 + s.val)) ≤
      5 * r ^ (s.val - 1) * D ^ (-(1 + s.val))) ∧
    (D ≤ r → r ^ (q - t) * D ^ (-q) / r ≤ r ^ (s.val - 1) * D ^ (-(1 + s.val))) := by
  intro q t H
  have hrp : 0 < r := by linarith
  have hDp : 0 < D := by linarith
  have hqt : q ≤ t := by
    have := mul_nonneg s.property.1.le (sub_nonneg.mpr s.property.2.le)
    dsimp [q, t]; nlinarith only [this]
  have ht : 1 ≤ t := by
    have := mul_nonneg s.property.1.le (show 0 ≤ 1 - s.val / 2 by linarith [s.property.2])
    dsimp [t]; nlinarith only [this]
  have hmass : r ^ (s.val - 1) ≤ r ^ (q - t) := by
    apply Real.rpow_le_rpow_of_exponent_le hr
    have := mul_nonneg (sub_nonneg.mpr s.property.2.le)
      (show 0 ≤ 1 - s.val / 2 by linarith [s.property.2])
    dsimp [q, t]; nlinarith only [this]
  have hpow : D ^ (-t) ≤ (4 : ℝ) ^ (t - q) * r ^ (q - t) * D ^ (-q) := by
    calc
      _ = D ^ (q - t) * D ^ (-q) := by rw [← Real.rpow_add hDp]; congr 1; ring
      _ ≤ (r / 4) ^ (q - t) * D ^ (-q) := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos (by positivity) hD (by linarith)) (by positivity)
      _ = _ := by
        rw [Real.div_rpow hrp.le (by norm_num),
          show q - t = -(t - q) by ring, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
        simp only [div_eq_mul_inv, inv_inv]
        ring
  have hderiv : r ^ s.val * D ^ (-(2 + s.val)) ≤
      4 * r ^ (s.val - 1) * D ^ (-(1 + s.val)) := by
    have hh : r / D ≤ 4 := (div_le_iff₀ hDp).mpr (by linarith)
    have hrs : r ^ s.val = r ^ (s.val - 1) * r := by
      calc
        _ = r ^ ((s.val - 1) + 1) := by congr 1; ring
        _ = _ := by rw [Real.rpow_add hrp, Real.rpow_one]
    calc
      _ = (r ^ (s.val - 1) * D ^ (-(1 + s.val))) * (r / D) := by
        rw [hrs,
          show -(2 + s.val) = -(1 + s.val) - 1 by ring, Real.rpow_sub hDp, Real.rpow_one]
        ring
      _ ≤ (r ^ (s.val - 1) * D ^ (-(1 + s.val))) * 4 :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by ring
  refine ⟨?_, by linarith only [hderiv], ?_⟩
  · have hh := add_le_add (mul_le_mul_of_nonneg_right hmass
      (show 0 ≤ D ^ (-q) by positivity)) hpow
    exact hh.trans_eq (by dsimp [H]; ring)
  · intro hDr
    have hh := Real.rpow_le_rpow hDp.le hDr (show 0 ≤ s.val / 2 by linarith [s.property.1])
    have heq : D ^ (-q) = D ^ (s.val / 2) * D ^ (-(1 + s.val)) := by
      rw [← Real.rpow_add hDp]; congr 1; dsimp [q]; ring
    rw [heq]
    calc
      _ ≤ r ^ (q - t) * (r ^ (s.val / 2) * D ^ (-(1 + s.val))) / r := by gcongr
      _ = r ^ (s.val - t) * D ^ (-(1 + s.val)) := by
        have hid : r ^ (q - t) * r ^ (s.val / 2) / r = r ^ (s.val - t) := by
          calc
            _ = r ^ (q - t + s.val / 2) / r ^ (1 : ℝ) := by
              rw [Real.rpow_one, Real.rpow_add hrp]
            _ = r ^ ((q - t + s.val / 2) - 1) := (Real.rpow_sub hrp _ _).symm
            _ = _ := by congr 1; dsimp [q]; ring
        calc
          _ = (r ^ (q - t) * r ^ (s.val / 2) / r) * D ^ (-(1 + s.val)) := by ring
          _ = _ := by rw [hid]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hr (by linarith only [ht])) (by positivity)

/-- Counting-measure norm of a far-row profile, for the two exponents
used in the proof of Lemma 5.13. -/
theorem spatial_profile_norm (N : ℕ+) (i : Fin (N : ℕ))
    (r b t q L : ℝ) (hr : 4 ≤ r) (hq : 0 < q) (hbq : 1 < b * q)
    (hL : 0 ≤ L) (F : Fin (N : ℕ) → ℝ)
    (hzero : ∀ j, weightRadius N i j < r / 4 → F j = 0)
    (hF : ∀ j, r / 4 ≤ weightRadius N i j →
      |F j| ≤ L * r ^ (b - t) * weightRadius N i j ^ (-b)) :
    (∑ j, |F j| ^ q) ^ (1 / q) ≤
      ((2 * (1 + 1 / (b * q - 1))) ^ (1 / q) * (4 : ℝ) ^ (b - 1 / q)) *
        L * r ^ (-t + 1 / q) := by
  classical
  let J := univ.filter (fun j => r / 4 ≤ weightRadius N i j)
  let T := 2 * (1 + 1 / (b * q - 1))
  have hrp : 0 < r := by linarith
  have hT : 0 < T := by dsimp [T]; positivity
  have hR : 1 ≤ r / 4 := by linarith
  have hsum : (∑ j, |F j| ^ q) ≤
      (L * r ^ (b - t)) ^ q * T * (r / 4) ^ (1 - b * q) := by
    calc
      _ = ∑ j ∈ J, |F j| ^ q := by
        symm
        apply sum_subset (subset_univ _)
        intro j _ hj
        have hh : weightRadius N i j < r / 4 := by
          simpa only [J, mem_filter, mem_univ, true_and, not_le] using hj
        rw [hzero j hh, abs_zero, Real.zero_rpow hq.ne']
      _ ≤ ∑ j ∈ J, (L * r ^ (b - t)) ^ q * weightRadius N i j ^ (-(b * q)) := by
        apply sum_le_sum
        intro j hj
        have hj' : r / 4 ≤ weightRadius N i j := (mem_filter.mp hj).2
        have hh := Real.rpow_le_rpow (abs_nonneg _) (hF j hj') hq.le
        rw [Real.mul_rpow (by positivity : 0 ≤ L * r ^ (b - t))
          (Real.rpow_nonneg (by linarith [one_le_weightRadius N i j]) _),
          ← Real.rpow_mul (by linarith [one_le_weightRadius N i j]),
          show -b * q = -(b * q) by ring] at hh
        exact hh
      _ = (L * r ^ (b - t)) ^ q * ∑ j ∈ J, weightRadius N i j ^ (-(b * q)) := (mul_sum ..).symm
      _ ≤ _ := by
        have hh := sum_weightRadius_tail_le N i hbq hR
        simp only [weightRadius_eq_comm N _ i] at hh
        have hh' := mul_le_mul_of_nonneg_left hh
          (show 0 ≤ (L * r ^ (b - t)) ^ q by positivity)
        exact hh'.trans_eq (by dsimp [T, J]; ring)
  have hh := Real.rpow_le_rpow
    (sum_nonneg (fun j _ => Real.rpow_nonneg (abs_nonneg _) _)) hsum
    (show 0 ≤ 1 / q by positivity)
  have hid : ((L * r ^ (b - t)) ^ q * T * (r / 4) ^ (1 - b * q)) ^ (1 / q) =
      (T ^ (1 / q) * (4 : ℝ) ^ (b - 1 / q)) * L * r ^ (-t + 1 / q) := by
    rw [Real.mul_rpow (by positivity : 0 ≤ (L * r ^ (b - t)) ^ q * T)
      (Real.rpow_nonneg (by positivity : 0 ≤ r / 4) _),
      Real.mul_rpow (by positivity : 0 ≤ (L * r ^ (b - t)) ^ q) hT.le,
      ← Real.rpow_mul (by positivity : 0 ≤ L * r ^ (b - t)),
      show q * (1 / q) = 1 by field_simp [hq.ne'],
      Real.rpow_one, ← Real.rpow_mul (by positivity : 0 ≤ r / 4),
      show (1 - b * q) * (1 / q) = -(b - 1 / q) by field_simp [hq.ne']; ring,
      Real.div_rpow hrp.le (by norm_num),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
    rw [div_inv_eq_mul]
    calc
      _ = (T ^ (1 / q) * (4 : ℝ) ^ (b - 1 / q)) * L *
          (r ^ (b - t) * r ^ (-(b - 1 / q))) := by ring
      _ = _ := by rw [← Real.rpow_add hrp]; congr 2; ring
  exact hh.trans_eq hid

/-- The actual second cutoff preserves the two row profiles in the proof of Lemma 5.13, including its discrete product rule. -/
theorem spatial_cutoff_profiles (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (_hN : 2 ≤ (N : ℕ))
      (i : Fin (N : ℕ)) (r L : ℝ), 16 ≤ r → 0 ≤ L →
      ∀ G : Fin (N : ℕ) → ℝ,
      (∀ j, r / 4 ≤ weightRadius N i j →
        |G j| ≤ L * (r ^ (s.val - 1) * weightRadius N i j ^ (-(1 + s.val / 2)) +
          weightRadius N i j ^ (-(1 + s.val - s.val ^ 2 / 2))) ∧
        |G (j + 1) - G j| ≤ L *
          (r ^ (s.val - 1) * weightRadius N i j ^ (-(1 + s.val)) +
            r ^ s.val * weightRadius N i j ^ (-(2 + s.val)))) →
      let F := fun j => (1 - CutoffApproximation.scalarCutoff
        (4 * (Riesz1.cyclicIndexDistance N i j : ℝ) / r)) * G j
      (∀ j, weightRadius N i j < r / 4 → F j = 0 ∧ F (j + 1) - F j = 0) ∧
      (∀ j, r / 4 ≤ weightRadius N i j →
        |F j| ≤ C * L * r ^ ((1 + s.val / 2) - (1 + s.val - s.val ^ 2 / 2)) *
          weightRadius N i j ^ (-(1 + s.val / 2)) ∧
        |F (j + 1) - F j| ≤ C * L * r ^ (s.val - 1) *
          weightRadius N i j ^ (-(1 + s.val))) := by
  obtain ⟨Cζ, hCζ, hb⟩ := spatial_outer_cutoff
  let q := 1 + s.val / 2
  let t := 1 + s.val - s.val ^ 2 / 2
  let H := 1 + (4 : ℝ) ^ (t - q)
  let C := H + 5 + Cζ * H
  have hH : 0 < H := by dsimp [H]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hHC : H ≤ C := by
    have : 0 ≤ Cζ * H := by positivity
    dsimp [C]; linarith
  have hζC : 5 + Cζ * H ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro N hN i r L hr hL G hG F
  let ζ := fun j => 1 - CutoffApproximation.scalarCutoff
    (4 * (Riesz1.cyclicIndexDistance N i j : ℝ) / r)
  have hrp : 0 < r := by linarith
  obtain ⟨hz, hΔz, hsupp, htrans⟩ := hb N hN i r hr
  change (∀ j, 0 ≤ ζ j ∧ ζ j ≤ 1) at hz
  change (∀ j, |ζ (j + 1) - ζ j| ≤ Cζ / r) at hΔz
  change (∀ j, ζ j ≠ 0 ∨ ζ (j + 1) ≠ 0 → r / 4 ≤ weightRadius N i j) at hsupp
  change (∀ j, ζ (j + 1) - ζ j ≠ 0 → weightRadius N i j ≤ r) at htrans
  have hFdef (j) : F j = ζ j * G j := rfl
  have hprof (j) (hj : r / 4 ≤ weightRadius N i j) :
      |G j| ≤ H * L * r ^ (q - t) * weightRadius N i j ^ (-q) ∧
      |G (j + 1) - G j| ≤ 5 * L * r ^ (s.val - 1) * weightRadius N i j ^ (-(1 + s.val)) := by
    obtain ⟨h₀, h₁, _⟩ := spatial_row_profiles s r (weightRadius N i j) (by linarith) hj
    exact ⟨((hG j hj).1.trans (mul_le_mul_of_nonneg_left h₀ hL)).trans_eq (by ring),
      ((hG j hj).2.trans (mul_le_mul_of_nonneg_left h₁ hL)).trans_eq (by ring)⟩
  refine ⟨?_, ?_⟩
  · intro j hj
    have hj₀ : ζ j = 0 := by
      by_contra hh
      exact (not_le.mpr hj) (hsupp j (Or.inl hh))
    have hj₁ : ζ (j + 1) = 0 := by
      by_contra hh
      exact (not_le.mpr hj) (hsupp j (Or.inr hh))
    simp only [hFdef, hj₀, hj₁, zero_mul, sub_self, and_self]
  · intro j hj
    have h := hprof j hj
    have hF : |F j| ≤ H * L * r ^ (q - t) * weightRadius N i j ^ (-q) := by
      rw [hFdef, abs_mul, abs_of_nonneg (hz j).1]
      exact (mul_le_mul_of_nonneg_right (hz j).2 (abs_nonneg _)).trans (by simpa using h.1)
    refine ⟨hF.trans (by
      have hh := mul_le_mul_of_nonneg_right hHC
        (show 0 ≤ L * r ^ (q - t) * weightRadius N i j ^ (-q) by
          have := one_le_weightRadius N i j; positivity)
      nlinarith only [hh]), ?_⟩
    have hcut : |ζ (j + 1) - ζ j| * |G j| ≤
        Cζ * H * L * r ^ (s.val - 1) * weightRadius N i j ^ (-(1 + s.val)) := by
      by_cases he : ζ (j + 1) - ζ j = 0
      · rw [he, abs_zero, zero_mul]
        have := one_le_weightRadius N i j
        positivity
      · have hDr := htrans j he
        have hh := (spatial_row_profiles s r (weightRadius N i j) (by linarith) hj).2.2 hDr
        calc
          _ ≤ (Cζ / r) * (H * L * r ^ (q - t) * weightRadius N i j ^ (-q)) :=
            mul_le_mul (hΔz j) h.1 (abs_nonneg _) (by positivity)
          _ = (Cζ * H * L) *
              (r ^ (q - t) * weightRadius N i j ^ (-q) / r) := by ring
          _ ≤ (Cζ * H * L) * (r ^ (s.val - 1) * weightRadius N i j ^ (-(1 + s.val))) :=
            mul_le_mul_of_nonneg_left hh (by positivity)
          _ = _ := by ring
    have hid : F (j + 1) - F j =
        ζ (j + 1) * (G (j + 1) - G j) + (ζ (j + 1) - ζ j) * G j := by
      simp only [hFdef]; ring
    calc
      _ ≤ |ζ (j + 1)| * |G (j + 1) - G j| + |ζ (j + 1) - ζ j| * |G j| := by
        rw [hid]
        simpa only [abs_mul] using abs_add_le
          (ζ (j + 1) * (G (j + 1) - G j)) ((ζ (j + 1) - ζ j) * G j)
      _ ≤ 5 * L * r ^ (s.val - 1) * weightRadius N i j ^ (-(1 + s.val)) +
          Cζ * H * L * r ^ (s.val - 1) * weightRadius N i j ^ (-(1 + s.val)) := by
        apply add_le_add _ hcut
        rw [abs_of_nonneg (hz (j + 1)).1]
        exact (mul_le_mul_of_nonneg_right (hz (j + 1)).2 (abs_nonneg _)).trans
          (by simpa using h.2)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hζC
          (show 0 ≤ L * r ^ (s.val - 1) * weightRadius N i j ^ (-(1 + s.val)) by
            have := one_le_weightRadius N i j; positivity)
        nlinarith only [hh]

/-- Both localized counting norms, and their fractional interpolation,
for the actual resolvent and error row in the proof of Lemma 5.13. This estimate assumes entry and difference bounds. -/
theorem spatial_retained_row_norms (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    let t := 1 + s.val - s.val ^ 2 / 2
    let δ := s.val ^ 2 * (2 - s.val) / 4
    let q := 2 / s.val
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (a : ℝ) (ha : 0 < a) (B : ℝ) (i₀ i : Fin (N : ℕ)) (L : ℝ),
      0 ≤ L → ∀ E : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ,
      (∀ k j, |E k j| ≤ L * weightRadius N k j ^ (-(1 + s.val / 2))) →
      (∀ k j, |E k j - E (k + 1) j| + |E k j - E k (j + 1)| ≤
        L * weightRadius N k j ^ (-(1 + s.val))) →
      (∀ k j, |(E k j - E (k + 1) j) -
        (E k (j + 1) - E (k + 1) (j + 1))| ≤
          L * weightRadius N k j ^ (-(2 + s.val))) →
      let r := weightRadius N i i₀
      let μ := a + B ^ 2 / a
      let F := fun j => (1 - CutoffApproximation.scalarCutoff
        (4 * (Riesz1.cyclicIndexDistance N i j : ℝ) / r)) *
        ∑ l, (factorizationMatrix s N hN a ha B i l *
          CutoffApproximation.scalarCutoff (16 * (Riesz1.cyclicIndexDistance N i l : ℝ) / r)) * E l j
      16 ≤ r →
      (∑ j, |F j| ^ q) ^ (1 / q) ≤ C * μ * L * r ^ (-t + s.val / 2) ∧
      (∑ j, |F (j + 1) - F j| ^ q) ^ (1 / q) ≤ C * μ * L * r ^ (-2 + s.val / 2) ∧
      (∑ j, |(F ᵥ* (rieszMatrix sh N hN)⁻¹) j| ^ q) ^ (1 / q) ≤
        C * μ * L * r ^ (-(2 - s.val) - δ) := by
  intro sh t δ q
  obtain ⟨C₀, hC₀, hraw⟩ := spatial_retained_error_rows hz s
  obtain ⟨C₁, hC₁, hcut⟩ := spatial_cutoff_profiles s
  obtain ⟨_, C₂, hC₂, hfrac⟩ := spatial_far_row_of_norm_bounds hz s
  have hs : 0 < s.val := s.property.1
  have hq : 2 < q := (lt_div_iff₀ hs).mpr (by linarith [s.property.2])
  have hqi : 1 / q = s.val / 2 := by dsimp [q]; field_simp
  let b₀ := 1 + s.val / 2
  let b₁ := 1 + s.val
  have hb₀ : 1 < b₀ * q := by dsimp [b₀]; nlinarith
  have hb₁ : 1 < b₁ * q := by dsimp [b₁]; nlinarith
  let N₀ := (2 * (1 + 1 / (b₀ * q - 1))) ^ (1 / q) * (4 : ℝ) ^ (b₀ - 1 / q)
  let N₁ := (2 * (1 + 1 / (b₁ * q - 1))) ^ (1 / q) * (4 : ℝ) ^ (b₁ - 1 / q)
  have hN₀ : 0 < N₀ := by dsimp [N₀]; positivity
  have hN₁ : 0 < N₁ := by dsimp [N₁]; positivity
  let C₃ := (N₀ + N₁) * C₁ * C₀
  let C := (1 + C₂) * C₃
  have hC₃ : 0 < C₃ := by dsimp [C₃]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hCC : C₃ ≤ C := by
    have := mul_nonneg hC₂.le hC₃.le
    dsimp [C]; nlinarith only [this]
  have hC₂C : C₂ * C₃ ≤ C := by dsimp [C]; nlinarith only [hC₃]
  refine ⟨C, hC, ?_⟩
  intro N hN a ha B i₀ i L hL E hE hΔ hΔ₂ r μ F hr
  have hrp : 0 < r := by linarith
  have hμ : 0 < μ := factorization_shift_pos ha B
  let G := fun j => ∑ l, (factorizationMatrix s N hN a ha B i l *
    CutoffApproximation.scalarCutoff (16 * (Riesz1.cyclicIndexDistance N i l : ℝ) / r)) * E l j
  obtain ⟨hsupp, hprof⟩ := hcut N hN i r (C₀ * μ * L) hr (by positivity)
    G (hraw N hN a ha B i₀ i L hL E hE hΔ hΔ₂ hr)
  have hnorm₀ : (∑ j, |F j| ^ q) ^ (1 / q) ≤ C₃ * μ * L * r ^ (-t + s.val / 2) := by
    have hh := spatial_profile_norm N i r b₀ t q (C₁ * (C₀ * μ * L))
      (by linarith) (by linarith) hb₀ (by positivity) F
      (fun j hj => (hsupp j hj).1) (fun j hj => (hprof j hj).1)
    rw [hqi] at hh
    have hconst : N₀ * C₁ * C₀ ≤ C₃ := by
      have := mul_nonneg hN₁.le (show 0 ≤ C₁ * C₀ by positivity)
      dsimp [C₃]; nlinarith only [this]
    change _ ≤ _ at hh
    calc
      _ ≤ N₀ * (C₁ * (C₀ * μ * L)) * r ^ (-t + s.val / 2) := by
        simpa only [N₀, hqi, b₀] using hh
      _ ≤ _ := by
        have hh' := mul_le_mul_of_nonneg_right hconst
          (show 0 ≤ μ * L * r ^ (-t + s.val / 2) by positivity)
        nlinarith only [hh']
  have hnorm₁ : (∑ j, |F (j + 1) - F j| ^ q) ^ (1 / q) ≤
      C₃ * μ * L * r ^ (-2 + s.val / 2) := by
    have hh := spatial_profile_norm N i r b₁ 2 q (C₁ * (C₀ * μ * L))
      (by linarith) (by linarith) hb₁ (by positivity) (fun j => F (j + 1) - F j)
      (fun j hj => (hsupp j hj).2) (fun j hj => by
        simpa only [b₁, show (1 + s.val) - 2 = s.val - 1 by ring] using (hprof j hj).2)
    rw [hqi] at hh
    have hconst : N₁ * C₁ * C₀ ≤ C₃ := by
      have := mul_nonneg hN₀.le (show 0 ≤ C₁ * C₀ by positivity)
      dsimp [C₃]; nlinarith only [this]
    calc
      _ ≤ N₁ * (C₁ * (C₀ * μ * L)) * r ^ (-2 + s.val / 2) := by
        simpa only [N₁, hqi, b₁] using hh
      _ ≤ _ := by
        have hh' := mul_le_mul_of_nonneg_right hconst
          (show 0 ≤ μ * L * r ^ (-2 + s.val / 2) by positivity)
        nlinarith only [hh']
  have hrN : r ≤ (N : ℝ) := by
    have hd := Riesz1.APG.cyclicIndexDistance_le_half (N := N) i i₀
    have hn : 1 + Riesz1.cyclicIndexDistance N i i₀ ≤ (N : ℕ) := by omega
    dsimp [r, weightRadius]
    exact_mod_cast hn
  have hlast := hfrac N hN r (C₃ * μ * L) (by linarith) hrN (by positivity) F hnorm₀ hnorm₁
  refine ⟨hnorm₀.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC hμ.le) hL) (by positivity)),
    hnorm₁.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC hμ.le) hL) (by positivity)), ?_⟩
  exact hlast.trans (by
    have hh := mul_le_mul_of_nonneg_right hC₂C
      (show 0 ≤ μ * L * r ^ (-(2 - s.val) - δ) by positivity)
    nlinarith only [hh])

end Internal

/-- The actual doubly localized tail row of the proof of Lemma 5.13, under the periodized matrix
assumptions. Both input norms to fractional interpolation are proved here.
The constants and loss exponent precede the sizes, measure, matrix, shift,
cutoff and indices. This is the large-radius far-row contribution. -/
theorem spatial_far_error_row_norms (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κₛ γₛ : ℝ) (hκₛ : 0 ≤ κₛ) (hγₛ : 0 ≤ γₛ) (M₀ : ℕ) :
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    let t := 1 + s.val - s.val ^ 2 / 2
    let δ := s.val ^ 2 * (2 - s.val) / 4
    let q := 2 / s.val
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ∀ Cₛ : ℝ, 1 ≤ Cₛ →
      ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ))
        (_hn : 2 ≤ (n : ℕ)) (_hnm : (n : ℕ) ≤ (m : ℕ))
        (_hmn : (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val)),
        let K₀ := ⌊(n : ℝ) ^ ε⌋₊ ^ M₀
        1 ≤ K₀ → 4 * K₀ ≤ (m : ℕ) →
        ∀ {α : Type*} [MeasurableSpace α] (ν : MeasureTheory.Measure α)
          (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ),
        PeriodizedMatrixBounds (ν := ν) s n m hm K₀ Cₛ κₛ γₛ ε M →
        ∀ᵐ x ∂ν, ∀ (a : ℝ) (ha : 0 < a) (B R : ℝ), 1 ≤ R →
          ∀ i₀ i : Fin (m : ℕ),
          let r := weightRadius m i i₀
          let μ := a + B ^ 2 / a
          let E := M x - (2 : ℝ) • rieszMatrix s m hm
          let F := fun j => (1 - CutoffApproximation.scalarCutoff
            (4 * (Riesz1.cyclicIndexDistance m i j : ℝ) / r)) *
            ∑ l, (factorizationMatrix s m hm a ha B i l *
              CutoffApproximation.scalarCutoff (16 * (Riesz1.cyclicIndexDistance m i l : ℝ) / r)) *
              ((1 - CutoffApproximation.scalarCutoff
                ((Riesz1.cyclicIndexDistance m l j : ℝ) / R)) * E l j)
          16 ≤ r → 16 * R ≤ r →
          (∑ j, |F j| ^ q) ^ (1 / q) ≤ C * μ * (n : ℝ) ^ (κ * ε) * r ^ (-t + s.val / 2) ∧
          (∑ j, |F (j + 1) - F j| ^ q) ^ (1 / q) ≤
            C * μ * (n : ℝ) ^ (κ * ε) * r ^ (-2 + s.val / 2) ∧
          (∑ j, |(F ᵥ* (rieszMatrix sh m hm)⁻¹) j| ^ q) ^ (1 / q) ≤
            C * μ * (n : ℝ) ^ (κ * ε) * r ^ (-(2 - s.val) - δ) := by
  intro sh t δ q
  obtain ⟨κ, hκ, herr⟩ := global_error_differences s κₛ γₛ hκₛ hγₛ M₀
  obtain ⟨C₁, hC₁, hrows⟩ := Internal.spatial_retained_row_norms hz s
  refine ⟨κ, hκ, ?_⟩
  intro ε hε Cₛ hCₛ
  obtain ⟨C₀, hC₀, herr⟩ := herr ε hε Cₛ hCₛ
  have hC₀pos : 0 < C₀ := by linarith
  refine ⟨C₁ * C₀, mul_pos hC₁ hC₀pos, ?_⟩
  intro n m hm hn hnm hmn K₀ hK₀ hK₀m α _ ν M hM
  obtain ⟨_, _, _, _, _, _, he⟩ := herr n m hm hn hnm hmn hK₀ hK₀m ν M hM
  filter_upwards [he] with x hx
  intro a ha B R hR i₀ i r μ E F hr hRr
  have hL : 0 ≤ C₀ * (n : ℝ) ^ (κ * ε) := by positivity
  have hE (k j) : |E k j| ≤ C₀ * (n : ℝ) ^ (κ * ε) *
      weightRadius m k j ^ (-(1 + s.val / 2)) := by
    simpa only [weightRadius, show -(1 + s.val / 2) = -1 - s.val / 2 by ring] using hx.1 k j
  have hΔ (k j) : |E k j - E (k + 1) j| + |E k j - E k (j + 1)| ≤
      C₀ * (n : ℝ) ^ (κ * ε) * weightRadius m k j ^ (-(1 + s.val)) := by
    simpa only [weightRadius, show -(1 + s.val) = -1 - s.val by ring] using hx.2.1 k j
  have hΔ₂ (k j) : |(E k j - E (k + 1) j) - (E k (j + 1) - E (k + 1) (j + 1))| ≤
      C₀ * (n : ℝ) ^ (κ * ε) * weightRadius m k j ^ (-(2 + s.val)) := by
    simpa only [weightRadius, show -(2 + s.val) = -2 - s.val by ring] using hx.2.2.1 k j
  have hF (j) : F j = (1 - CutoffApproximation.scalarCutoff
      (4 * (Riesz1.cyclicIndexDistance m i j : ℝ) / r)) *
      ∑ l, (factorizationMatrix s m hm a ha B i l *
        CutoffApproximation.scalarCutoff (16 * (Riesz1.cyclicIndexDistance m i l : ℝ) / r)) * E l j :=
    Internal.spatial_far_tail_identity m i r R (by linarith) (by linarith) hRr
      (factorizationMatrix s m hm a ha B) E j
  have hFeq : F = fun j => (1 - CutoffApproximation.scalarCutoff
      (4 * (Riesz1.cyclicIndexDistance m i j : ℝ) / r)) *
      ∑ l, (factorizationMatrix s m hm a ha B i l *
        CutoffApproximation.scalarCutoff (16 * (Riesz1.cyclicIndexDistance m i l : ℝ) / r)) * E l j :=
    funext hF
  rw [hFeq]
  have hh := hrows m hm a ha B i₀ i (C₀ * (n : ℝ) ^ (κ * ε)) hL E hE hΔ hΔ₂ hr
  dsimp only [r, μ, sh, t, δ, q]
  exact ⟨hh.1.trans_eq (by ring), hh.2.1.trans_eq (by ring), hh.2.2.trans_eq (by ring)⟩

end Riesz2.GlobalCommutators
