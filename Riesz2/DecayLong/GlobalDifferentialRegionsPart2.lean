/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.GlobalDifferentialRegions

/-!
# The separated-radius differential commutator

Step 3 of Lemma 5.13, equation (5.49): the leading far monomial
uses the zero-sum row cancellation. The two remaining monomials use
weighted Cauchy–Schwarz. See the proof of Lemma 5.13 in the paper.
-/

@[expose] public section

noncomputable section

open Matrix Finset
open scoped BigOperators Fin.NatCast

namespace Riesz2.GlobalCommutators

namespace Internal

/-- Lemma 5.13, Step 3 (equation (5.49)): weighted Cauchy–Schwarz on the
complement of a smaller-radius row, including thresholds below one. -/
theorem complementary_row (N : ℕ+) (i₀ : Fin (N : ℕ)) (s : Riesz1.RieszExponent)
    {R : ℝ} (hR : 1 ≤ R) (g : Fin (N : ℕ) → ℝ) :
    (∑ j ∈ univ.filter (fun j => R / 2 ≤ weightRadius N j i₀), |g j|) ≤
      Real.sqrt (2 * (1 + 1 / (1 - s.val)) * 2 ^ (1 - s.val)) *
        R ^ ((s.val - 1) / 2) *
          Real.sqrt (∑ j, (weightRadius N j i₀ ^ (1 - s.val / 2) * g j) ^ 2) := by
  classical
  have hRp : 0 < R := by linarith
  have hr (j) : 0 < weightRadius N j i₀ := by linarith [one_le_weightRadius N j i₀]
  have heq (j) : (1 / weightRadius N j i₀ ^ (1 - s.val / 2)) ^ 2 =
      weightRadius N j i₀ ^ (-(2 - s.val)) := by
    rw [one_div, inv_pow, ← Real.rpow_two, ← Real.rpow_mul (hr j).le,
      ← Real.rpow_neg (hr j).le]
    congr 1
    ring
  have hh := FiniteZeroSumBounds.weighted_cauchy_subset
    (univ.filter (fun j => R / 2 ≤ weightRadius N j i₀))
    (fun j => weightRadius N j i₀ ^ (1 - s.val / 2)) (fun _ => 1) g
    (fun j => Real.rpow_pos_of_pos (hr j) _)
  simp only [one_mul, heq] at hh
  have hb := Real.sqrt_le_sqrt (tail_half N i₀ hR
    (t := 2 - s.val) (by linarith [s.property.2]))
  rw [show (2 - s.val) - 1 = 1 - s.val by ring,
    show 1 - (2 - s.val) = s.val - 1 by ring,
    Real.sqrt_mul (by have := s.property.2; positivity), show Real.sqrt (R ^ (s.val - 1)) = R ^ ((s.val - 1) / 2) by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hRp.le]; congr 1; ring] at hb
  exact hh.trans (mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg _))

/-- Lemma 5.13, Step 3 (equation (5.49)): the final row-index
Cauchy–Schwarz inequality costs exactly a reciprocal-radius square sum. -/
theorem radial_cauchy (N : ℕ+) (i₀ : Fin (N : ℕ)) (γ : ℝ)
    (g : Fin (N : ℕ) → ℝ) :
    (∑ i, weightRadius N i i₀ ^ (γ - 1 / 2) * |g i|) ≤
      Real.sqrt (∑ i, (weightRadius N i i₀)⁻¹) *
        Real.sqrt (∑ i, (weightRadius N i i₀ ^ γ * g i) ^ 2) := by
  have hr (i) : 0 < weightRadius N i i₀ := by linarith [one_le_weightRadius N i i₀]
  have heq (i) : (weightRadius N i i₀ ^ (γ - 1 / 2) /
      weightRadius N i i₀ ^ γ) ^ 2 = (weightRadius N i i₀)⁻¹ := by
    rw [← Real.rpow_sub (hr i), ← Real.rpow_two, ← Real.rpow_mul (hr i).le,
      show (γ - 1 / 2 - γ) * 2 = (-1 : ℝ) by ring, Real.rpow_neg_one]
  have hh := FiniteZeroSumBounds.weighted_cauchy_subset univ
    (fun i => weightRadius N i i₀ ^ γ) (fun i => weightRadius N i i₀ ^ (γ - 1 / 2)) g
    (fun i => Real.rpow_pos_of_pos (hr i) γ)
  simpa only [heq, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (hr _) _)] using hh

/-- Lemma 5.13, Step 3 (equation (5.49)): assembling one monomial after
its smaller-radius row bound. The displayed exponent identity is the
one that produces the square root of the logarithm. -/
theorem logarithmic_rows (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (i₀ : Fin (N : ℕ))
    (g F : Fin (N : ℕ) → ℝ) {L t e γ : ℝ} (hL : 0 ≤ L)
    (he : t + e = γ - 1 / 2)
    (hF : ∀ i, |F i| ≤ L * weightRadius N i i₀ ^ e *
      Real.sqrt (∑ j, (weightRadius N j i₀ ^ γ * g j) ^ 2)) :
    |∑ i, weightRadius N i i₀ ^ t * g i * F i| ≤
      L * Real.sqrt (2 * (1 + 1 / Real.log 2)) *
        Real.sqrt (Real.log (2 * (N : ℝ))) *
          ∑ j, (weightRadius N j i₀ ^ γ * g j) ^ 2 := by
  let E := ∑ j, (weightRadius N j i₀ ^ γ * g j) ^ 2
  have hE : 0 ≤ E := sum_nonneg (fun _ _ => sq_nonneg _)
  have hr (i) : 0 < weightRadius N i i₀ := by linarith [one_le_weightRadius N i i₀]
  have hroot := Real.sqrt_le_sqrt (GlobalCancellation.sum_inverse_radius N hN i₀)
  rw [Real.sqrt_mul (by have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity)] at hroot
  calc
    _ ≤ ∑ i, |weightRadius N i i₀ ^ t * g i * F i| := abs_sum_le_sum_abs ..
    _ ≤ ∑ i, weightRadius N i i₀ ^ t * |g i| *
        (L * weightRadius N i i₀ ^ e * Real.sqrt E) := by
      apply sum_le_sum
      intro i _
      rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (hr i) _)]
      exact mul_le_mul_of_nonneg_left (hF i) (mul_nonneg (Real.rpow_nonneg (hr i).le _) (abs_nonneg _))
    _ = L * (∑ i, weightRadius N i i₀ ^ (γ - 1 / 2) * |g i|) * Real.sqrt E := by
      rw [mul_sum, sum_mul]
      apply sum_congr rfl
      intro i _
      rw [show weightRadius N i i₀ ^ t * |g i| *
        (L * weightRadius N i i₀ ^ e * Real.sqrt E) =
        L * (weightRadius N i i₀ ^ t * weightRadius N i i₀ ^ e) * |g i| * Real.sqrt E by ring,
        ← Real.rpow_add (hr i), he]
      ring
    _ ≤ L * (Real.sqrt (∑ i, (weightRadius N i i₀)⁻¹) * Real.sqrt E) * Real.sqrt E := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (radial_cauchy N i₀ γ g) hL) (Real.sqrt_nonneg _)
    _ = L * Real.sqrt (∑ i, (weightRadius N i i₀)⁻¹) * E := by
      rw [mul_assoc, mul_assoc, Real.mul_self_sqrt hE]
      ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hroot hL) hE
      simpa only [mul_assoc] using hh

end Internal

/-- Lemma 5.13, Step 3 (equation (5.49)): the leading far row is centered
using the zero sum, whereas the mixed and smaller-radius monomial rows
use weighted Cauchy–Schwarz directly. The constants precede the cycle. -/
theorem differential_far_rows (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (a : ℝ) (ha : 0 < a) (B : ℝ) (i₀ : Fin (N : ℕ))
      (g : Fin (N : ℕ) → ℝ), (∑ j, g j) = 0 → ∀ i,
      let A := factorizationMatrix s N hN a ha B
      let r := fun j => weightRadius N j i₀
      let S := univ.filter (fun j => r j < r i / 2)
      let α := 3 / 2 - s.val
      let E := ∑ j, (r j ^ (1 - s.val / 2) * g j) ^ 2
      (|∑ j ∈ S, A i j * g j| ≤
        C * (a + B ^ 2 / a) * r i ^ (-(5 - 3 * s.val) / 2) * Real.sqrt E) ∧
      (|∑ j ∈ S, (A i j * r j ^ α) * g j| ≤
        C * (a + B ^ 2 / a) * r i ^ (-1 + s.val / 2) * Real.sqrt E) ∧
      (|∑ j ∈ S, (A i j * r j ^ (2 * α)) * g j| ≤
        C * (a + B ^ 2 / a) * r i ^ ((1 - s.val) / 2) * Real.sqrt E) := by
  classical
  obtain ⟨C₀, hC₀, hb⟩ := factorization_entry_bound hz s
  obtain ⟨C₁, hC₁, hd⟩ := factorization_centered_entry_bound hz s
  let T := Real.sqrt (2 * (1 + 1 / (1 - s.val)) * 2 ^ (1 - s.val))
  let C := 2 * C₁ + C₀ * T + 8 * C₀
  have hT : 0 ≤ T := Real.sqrt_nonneg _
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N hN a ha B i₀ g hg i
  dsimp only
  let A := factorizationMatrix s N hN a ha B
  let r := fun j => weightRadius N j i₀
  let S := univ.filter (fun j => r j < r i / 2)
  let μ := a + B ^ 2 / a
  let α := 3 / 2 - s.val
  let γ := 1 - s.val / 2
  let e := -(5 - 3 * s.val) / 2
  let E := ∑ j, (r j ^ γ * g j) ^ 2
  have hr (j) : 0 < r j := by dsimp [r]; linarith [one_le_weightRadius N j i₀]
  have hri : 0 < r i := hr i
  have hμ : 0 < μ := factorization_shift_pos ha B
  have hE : 0 ≤ E := sum_nonneg (fun _ _ => sq_nonneg _)
  have hfar (j) (hj : r j < r i / 2) : |A i j| ≤ 4 * C₀ * μ * r i ^ (-(2 - s.val)) := by
    let D := 1 + (Riesz1.cyclicIndexDistance N i j : ℝ)
    have hD : r i / 2 ≤ D := by
      have hh := DerivativeCommutators.weightRadius_lipschitz N i₀ i j
      have hh' : r i - r j ≤ (Riesz1.cyclicIndexDistance N i j : ℝ) :=
        (le_abs_self _).trans hh
      dsimp [D]
      linarith
    have hpow : D ^ (-(2 - s.val)) ≤ 4 * r i ^ (-(2 - s.val)) := by
      calc
        _ ≤ (r i / 2) ^ (-(2 - s.val)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hD (by linarith [s.property.2])
        _ = 2 ^ (2 - s.val) * r i ^ (-(2 - s.val)) := by
          rw [Real.div_rpow (hr i).le (by norm_num),
            Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
          simp only [div_eq_mul_inv, inv_inv]
          ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
            (show 2 - s.val ≤ 2 by linarith [s.property.1])
          convert hh using 1; norm_num
    exact (hb N hN a ha B i j).trans
      ((mul_le_mul_of_nonneg_left hpow (mul_nonneg hC₀.le hμ.le)).trans_eq (by ring))
  have hlead : |∑ j ∈ S, A i j * g j| ≤
      (2 * C₁ + C₀ * T) * μ * r i ^ e * Real.sqrt E := by
    have hsmall := Internal.small_row N i₀ (one_le_weightRadius N i i₀)
      (L := C₁ * μ) (u := -(3 - s.val)) (v := 1) (γ := γ)
      (mul_nonneg hC₁.le hμ.le) (by dsimp [γ]; linarith [s.property.1])
      (fun j => A i j - A i i₀) g (fun j hj => by simpa only [Real.rpow_one] using hd N hN a ha B i₀ i j hj)
    have hexp : -(3 - s.val) + 1 - γ + 1 / 2 = e := by dsimp [γ, e]; ring
    rw [hexp] at hsmall
    have htail := Internal.complementary_row N i₀ s (one_le_weightRadius N i i₀) g
    have hrow : |A i i₀| ≤ C₀ * μ * r i ^ (-(2 - s.val)) := hb N hN a ha B i i₀
    have hc : |A i i₀ * ∑ j ∈ univ.filter (fun j => r i / 2 ≤ r j), g j| ≤
        C₀ * T * μ * r i ^ e * Real.sqrt E := by
      rw [abs_mul]
      calc
        _ ≤ (C₀ * μ * r i ^ (-(2 - s.val))) *
            (T * r i ^ ((s.val - 1) / 2) * Real.sqrt E) :=
          mul_le_mul hrow ((abs_sum_le_sum_abs ..).trans htail) (abs_nonneg _) (by positivity)
        _ = _ := by
          rw [show (C₀ * μ * r i ^ (-(2 - s.val))) *
            (T * r i ^ ((s.val - 1) / 2) * Real.sqrt E) =
            C₀ * T * μ * (r i ^ (-(2 - s.val)) * r i ^ ((s.val - 1) / 2)) * Real.sqrt E by ring,
            ← Real.rpow_add (hr i), show -(2 - s.val) + (s.val - 1) / 2 = e by dsimp [e]; ring]
    rw [differential_small_radius_cancellation s N hN a ha B i₀ i g hg]
    exact (abs_sub _ _).trans ((add_le_add hsmall hc).trans_eq (by ring))
  have hother (v : ℝ) (hv : 0 ≤ 2 * (v - γ)) :
      |∑ j ∈ S, (A i j * r j ^ v) * g j| ≤
        8 * C₀ * μ * r i ^ (-(2 - s.val) + v - γ + 1 / 2) * Real.sqrt E := by
    have hh := Internal.small_row N i₀ (one_le_weightRadius N i i₀)
      (L := 4 * C₀ * μ) (u := -(2 - s.val)) (v := v) (γ := γ)
      (by positivity) hv (fun j => A i j * r j ^ v) g (fun j hj => by
        have hrj : 0 < r j := hr j
        rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (hr j) _)]
        exact mul_le_mul_of_nonneg_right (hfar j hj) (by positivity))
    convert hh using 1; ring
  have hmono : 2 * C₁ + C₀ * T ≤ C := by dsimp [C]; linarith
  have hmono' : 8 * C₀ ≤ C := by dsimp [C]; nlinarith [mul_nonneg hC₀.le hT]
  refine ⟨hlead.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmono hμ.le)
      (Real.rpow_nonneg (hr i).le _)) (Real.sqrt_nonneg _)), ?_, ?_⟩
  · have hh := hother α (by dsimp [α, γ]; linarith [s.property.2])
    rw [show -(2 - s.val) + α - γ + 1 / 2 = -1 + s.val / 2 by dsimp [α, γ]; ring] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmono' hμ.le)
        (Real.rpow_nonneg hri.le _)) (Real.sqrt_nonneg _))
  · have hh := hother (2 * α) (by dsimp [α, γ]; linarith [s.property.2])
    rw [show -(2 - s.val) + 2 * α - γ + 1 / 2 = (1 - s.val) / 2 by dsimp [α, γ]; ring] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmono' hμ.le)
        (Real.rpow_nonneg hri.le _)) (Real.sqrt_nonneg _))

namespace Internal

/-- Lemma 5.13, Step 3 (equation (5.49)): symmetry partitions a quadratic
kernel into the comparable region and twice the smaller-radius region.
Threshold equalities belong to the comparable region. -/
theorem regional_split {ι : Type*} [Fintype ι] (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) (F : ι → ι → ℝ) (hF : ∀ i j, F i j = F j i) :
    (∑ i, ∑ j, F i j) =
      (∑ i, ∑ j ∈ univ.filter (fun j => r i / 2 ≤ r j ∧ r j ≤ 2 * r i), F i j) +
        2 * ∑ i, ∑ j ∈ univ.filter (fun j => r j < r i / 2), F i j := by
  classical
  have hpoint (i j) : F i j =
      (if r i / 2 ≤ r j ∧ r j ≤ 2 * r i then F i j else 0) +
        (if r j < r i / 2 then F i j else 0) +
        (if r i < r j / 2 then F i j else 0) := by
    have hi := hr i
    have hj := hr j
    by_cases hsmall : r j < r i / 2
    · have hn : ¬(r i / 2 ≤ r j ∧ r j ≤ 2 * r i) := fun h => (not_lt.mpr h.1) hsmall
      have hb : ¬r i < r j / 2 := by linarith
      simp only [hsmall, hn, hb, ↓reduceIte, zero_add, add_zero]
    · by_cases hbig : r i < r j / 2
      · have hn : ¬(r i / 2 ≤ r j ∧ r j ≤ 2 * r i) := by rintro ⟨_, h⟩; linarith
        simp only [hsmall, hbig, hn, ↓reduceIte, zero_add, add_zero]
      · have hn : r i / 2 ≤ r j ∧ r j ≤ 2 * r i := by constructor <;> linarith
        simp only [hsmall, hbig, hn, and_self, ↓reduceIte, add_zero]
  have hreflect : (∑ i, ∑ j, if r i < r j / 2 then F i j else 0) =
      ∑ i, ∑ j, if r j < r i / 2 then F i j else 0 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [hF j i]
  calc
    _ = ∑ i, ∑ j,
        ((if r i / 2 ≤ r j ∧ r j ≤ 2 * r i then F i j else 0) +
          (if r j < r i / 2 then F i j else 0) +
          (if r i < r j / 2 then F i j else 0)) := by
      apply sum_congr rfl
      intro i _
      exact sum_congr rfl (fun j _ => hpoint i j)
    _ = _ := by
      simp only [sum_add_distrib, hreflect, sum_filter]
      ring

end Internal

/-- Lemma 5.13, Step 3 (equation (5.49)): the three separated-radius
monomials are bounded individually by weighted Cauchy–Schwarz. Only
the leading monomial calls the centered, zero-sum row estimate. -/
theorem differential_far_region (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (a : ℝ) (ha : 0 < a) (B : ℝ) (i₀ : Fin (N : ℕ))
      (g : Fin (N : ℕ) → ℝ), (∑ j, g j) = 0 →
      let A := factorizationMatrix s N hN a ha B
      let r := fun j => weightRadius N j i₀
      let α := 3 / 2 - s.val
      |∑ i, ∑ j ∈ univ.filter (fun j => r j < r i / 2),
        A i j * (r i ^ α - r j ^ α) ^ 2 * g i * g j| ≤
        C * (a + B ^ 2 / a) * Real.sqrt (Real.log (2 * (N : ℝ))) *
          ∑ j, (r j ^ (1 - s.val / 2) * g j) ^ 2 := by
  classical
  obtain ⟨C, hC, hb⟩ := differential_far_rows hz s
  let H := Real.sqrt (2 * (1 + 1 / Real.log 2))
  have hH : 0 < H := by
    have hh : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [H]
    positivity
  refine ⟨4 * C * H, by positivity, ?_⟩
  intro N hN a ha B i₀ g hg
  dsimp only
  let A := factorizationMatrix s N hN a ha B
  let r := fun j => weightRadius N j i₀
  let S := fun i => univ.filter (fun j => r j < r i / 2)
  let α := 3 / 2 - s.val
  let γ := 1 - s.val / 2
  let μ := a + B ^ 2 / a
  let E := ∑ j, (r j ^ γ * g j) ^ 2
  let leading := ∑ i, r i ^ (2 * α) * g i * ∑ j ∈ S i, A i j * g j
  let mixed := ∑ i, r i ^ α * g i * ∑ j ∈ S i, (A i j * r j ^ α) * g j
  let smaller := ∑ i, g i * ∑ j ∈ S i, (A i j * r j ^ (2 * α)) * g j
  let U := C * μ * H * Real.sqrt (Real.log (2 * (N : ℝ))) * E
  have hL : 0 ≤ C * μ := mul_nonneg hC.le (factorization_shift_pos ha B).le
  have hr (j) : 0 < r j := by dsimp [r]; linarith [one_le_weightRadius N j i₀]
  have hl : |leading| ≤ U := by
    exact Internal.logarithmic_rows N hN i₀ g
      (fun i => ∑ j ∈ S i, A i j * g j) hL
      (t := 2 * α) (e := -(5 - 3 * s.val) / 2) (γ := γ)
      (by dsimp [α, γ]; ring) (fun i => (hb N hN a ha B i₀ g hg i).1)
  have hm : |mixed| ≤ U := by
    exact Internal.logarithmic_rows N hN i₀ g
      (fun i => ∑ j ∈ S i, (A i j * r j ^ α) * g j) hL
      (t := α) (e := -1 + s.val / 2) (γ := γ)
      (by dsimp [α, γ]; ring) (fun i => (hb N hN a ha B i₀ g hg i).2.1)
  have hs : |smaller| ≤ U := by
    have hh := Internal.logarithmic_rows N hN i₀ g
      (fun i => ∑ j ∈ S i, (A i j * r j ^ (2 * α)) * g j) hL
      (t := 0) (e := (1 - s.val) / 2) (γ := γ)
      (by dsimp [γ]; ring) (fun i => (hb N hN a ha B i₀ g hg i).2.2)
    simpa only [Real.rpow_zero, one_mul] using hh
  have hexpand : (∑ i, ∑ j ∈ S i,
      A i j * (r i ^ α - r j ^ α) ^ 2 * g i * g j) = leading - 2 * mixed + smaller := by
    dsimp only [leading, mixed, smaller]
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    have hp (k) : r k ^ (2 * α) = (r k ^ α) ^ (2 : ℕ) := by
      rw [mul_comm, Real.rpow_mul (hr k).le, Real.rpow_two]
    rw [hp i, hp j]
    ring
  rw [hexpand]
  calc
    _ ≤ |leading| + 2 * |mixed| + |smaller| := by
      have hh := abs_add_le (leading - 2 * mixed) smaller
      have hh' := abs_sub leading (2 * mixed)
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh'
      linarith
    _ ≤ 4 * U := by linarith
    _ = _ := by dsimp [U]; ring

/-- Lemma 5.13, Step 3 (equation (5.49)), by the written regional route:
symmetry, the comparable-radius Schur bound, and the three far monomials.
The constants are uniform before the size and the factorization shift. -/
theorem differential_regional_bound (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (a : ℝ) (ha : 0 < a) (B : ℝ) (i₀ : Fin (N : ℕ))
      (g : Fin (N : ℕ) → ℝ), (∑ j, g j) = 0 →
      let A := factorizationMatrix s N hN a ha B
      let α := 3 / 2 - s.val
      let γ := 1 - s.val / 2
      let r := fun i => weightRadius N i i₀
      |∑ i, (r i ^ α * g i) * (r i ^ α * (A *ᵥ g) i -
        (A *ᵥ (fun j => r j ^ α * g j)) i)| ≤
          C * (a + B ^ 2 / a) * Real.sqrt (Real.log (2 * (N : ℝ))) *
            ∑ i, (r i ^ γ * g i) ^ 2 := by
  classical
  obtain ⟨C₀, hC₀, hnear⟩ := differential_comparable_region hz s
  obtain ⟨C₁, hC₁, hfar⟩ := differential_far_region hz s
  let c := Real.sqrt (Real.log 2)
  have hc : 0 < c := Real.sqrt_pos.mpr (Real.log_pos (by norm_num))
  refine ⟨C₀ / c + C₁, by positivity, ?_⟩
  intro N hN a ha B i₀ g hg
  dsimp only
  let A := factorizationMatrix s N hN a ha B
  let α := 3 / 2 - s.val
  let γ := 1 - s.val / 2
  let r := fun i => weightRadius N i i₀
  let E := ∑ i, (r i ^ γ * g i) ^ 2
  let μ := a + B ^ 2 / a
  let L := Real.sqrt (Real.log (2 * (N : ℝ)))
  let F := fun i j => A i j * (r i ^ α - r j ^ α) ^ 2 * g i * g j
  let near := ∑ i, ∑ j ∈ univ.filter (fun j => r i / 2 ≤ r j ∧ r j ≤ 2 * r i), F i j
  let far := ∑ i, ∑ j ∈ univ.filter (fun j => r j < r i / 2), F i j
  have hE : 0 ≤ E := sum_nonneg (fun _ _ => sq_nonneg _)
  have hμ : 0 < μ := factorization_shift_pos ha B
  have hL : c ≤ L := by
    have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
    exact Real.sqrt_le_sqrt (Real.log_le_log (by norm_num) (by linarith))
  have hs : ∀ i j, F i j = F j i := by
    have hh := Matrix.isHermitian_iff_isSymm.mp
      (factorizationMatrix_posDef s N hN a ha B).isHermitian
    intro i j
    have hij : A i j = A j i := congrFun (congrFun hh j) i
    dsimp [F]
    rw [hij, sub_sq_comm]
    ring
  have hsplit : (∑ i, ∑ j, F i j) = near + 2 * far :=
    Internal.regional_split r (fun i => by dsimp [r]; linarith [one_le_weightRadius N i i₀]) F hs
  have hn : |near| ≤ C₀ * μ * E := hnear N hN a ha B i₀ g
  have hf : |far| ≤ C₁ * μ * L * E := hfar N hN a ha B i₀ g hg
  have hn' : C₀ * μ * E ≤ (C₀ / c) * μ * L * E := by
    have hh := mul_le_mul_of_nonneg_left hL (show 0 ≤ C₀ / c * μ * E by positivity)
    have heq : C₀ / c * μ * E * c = C₀ * μ * E := by field_simp
    rw [heq] at hh
    exact hh.trans_eq (by ring)
  rw [differential_identity s N hN a ha B i₀ g]
  change |(1 / 2 : ℝ) * ∑ i, ∑ j, F i j| ≤ _
  rw [hsplit, mul_add]
  have hh := abs_add_le ((1 / 2 : ℝ) * near) ((1 / 2 : ℝ) * (2 * far))
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
    show (1 / 2 : ℝ) * (2 * far) = far by ring] at hh
  have hbound : |(1 / 2 : ℝ) * near + (1 / 2 : ℝ) * (2 * far)| ≤
      (C₀ / c + C₁) * μ * L * E := by
    have hn0 : 0 ≤ C₀ * μ * E := by positivity
    rw [show (1 / 2 : ℝ) * (2 * far) = far by ring]
    nlinarith [hn.trans hn']
  exact hbound

end Riesz2.GlobalCommutators
