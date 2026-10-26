/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.GlobalDifferentialRegionsPart2
public import Riesz2.ToMathlib.CutoffApproximation

/-!
# Regional global commutator estimates

Continuation of the proof of Lemma 5.13, using the actual factorization matrix.
-/

@[expose] public section

noncomputable section

open Matrix Finset
open scoped BigOperators Fin.NatCast

namespace Riesz2.GlobalCommutators

/-- Lemma 5.13, Step 3 (equation (5.49)), by its regional estimates. The constant
precedes the size, center, factorization parameters and zero-sum vector.
Its dependence on the prescribed shift is bounded by the linear polynomial
`C * (1 + μ)`. -/
theorem global_differential_commutator (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (a : ℝ) (ha : 0 < a), a ≤ 1 → ∀ B : ℝ, 1 ≤ B →
      ∀ (i₀ : Fin (N : ℕ)) (g : Fin (N : ℕ) → ℝ), (∑ i, g i) = 0 →
      let A := factorizationMatrix s N hN a ha B
      let α := 3 / 2 - s.val
      let γ := 1 - s.val / 2
      let r := fun i => weightRadius N i i₀
      |∑ i, (r i ^ α * g i) * (r i ^ α * (A *ᵥ g) i -
        (A *ᵥ (fun j => r j ^ α * g j)) i)| ≤
          C * (1 + (a + B ^ 2 / a)) * Real.sqrt (Real.log (2 * (N : ℝ))) *
            ∑ i, (r i ^ γ * g i) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := differential_regional_bound hz s
  refine ⟨C, hC, ?_⟩
  intro N hN a ha _ B _ i₀ g hg
  have hh := hb N hN a ha B i₀ g hg
  dsimp only at hh ⊢
  have hE : 0 ≤ ∑ i, (weightRadius N i i₀ ^ (1 - s.val / 2) * g i) ^ 2 :=
    sum_nonneg (fun _ _ => sq_nonneg _)
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith : a + B ^ 2 / a ≤ 1 + (a + B ^ 2 / a)) hC.le)
      (Real.sqrt_nonneg _)) hE)


/-- Signed mass of any retained resolvent row for the proof of Lemma 5.13. The cutoff may be smooth or sharp.
Its complement has size at most one and starts at radius `R`. The exact
constant mode and the discarded absolute tail are both retained. -/
theorem spatial_retained_signed_mass (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (a : ℝ) (ha : 0 < a) (B : ℝ) (i : Fin (N : ℕ)) (R : ℝ),
      1 ≤ R → R ≤ (N : ℝ) → ∀ ζ : Fin (N : ℕ) → ℝ,
      (∀ j, |1 - ζ j| ≤ 1) → (∀ j, weightRadius N j i ≤ R → ζ j = 1) →
      |∑ j, factorizationMatrix s N hN a ha B i j * ζ j| ≤
        C * (a + B ^ 2 / a) * R ^ (s.val - 1) := by
  obtain ⟨c, _, hc, _, hmass⟩ := global_reference_mass_bounds s
  obtain ⟨C₀, hC₀, he⟩ := factorization_entry_bound hz s
  let T := 2 * (1 + 1 / (1 - s.val))
  have hT : 0 < T := by dsimp [T]; have hs := s.property.2; positivity
  refine ⟨1 / c + C₀ * T, by positivity, ?_⟩
  intro N hN a ha B i R hR hRN ζ hζ hkeep
  let A := factorizationMatrix s N hN a ha B
  let μ := a + B ^ 2 / a
  let ℓ := ∑ j, ((2 : ℝ) • rieszMatrix s N hN) i j
  have hμ : 0 < μ := factorization_shift_pos ha B
  have hNpos : (0 : ℝ) < N := by positivity
  have hRpos : 0 < R := by linarith
  have hlo : c * (N : ℝ) ^ (1 - s.val) ≤ ℓ := (hmass N hN i).1
  have hlpos : 0 < ℓ := (by positivity : 0 < c * (N : ℝ) ^ (1 - s.val)).trans_le hlo
  have hsum : ∑ j, A i j = μ / (ℓ + μ) := by
    have hh := congrFun (factorizationMatrix_constant_mode s N hN a ha B) i
    simp only [Matrix.mulVec, dotProduct, mul_one, Pi.smul_apply, smul_eq_mul] at hh
    have heq : ℓ = 2 * ∑ k, sampledRieszKernel s N hN k := by
      dsimp [ℓ]
      simp only [← mul_sum, rieszMatrix_row_sum]
    simpa only [← heq] using hh
  have hm : |∑ j, A i j| ≤ (1 / c) * μ * R ^ (s.val - 1) := by
    rw [hsum, abs_of_pos (div_pos hμ (add_pos hlpos hμ))]
    calc
      _ ≤ μ / (c * (N : ℝ) ^ (1 - s.val)) :=
        div_le_div_of_nonneg_left hμ.le (by positivity) (by linarith)
      _ = (1 / c) * μ * (N : ℝ) ^ (s.val - 1) := by
        rw [show s.val - 1 = -(1 - s.val) by ring, Real.rpow_neg hNpos.le]
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hRpos hRN (by linarith [s.property.2])) (by positivity)
  let S := univ.filter (fun j => R ≤ weightRadius N j i)
  have htail : (∑ j, |A i j * (1 - ζ j)|) ≤ C₀ * μ * T * R ^ (s.val - 1) := by
    have hp : 1 < 2 - s.val := by linarith [s.property.2]
    have hpoint (j) : |A i j * (1 - ζ j)| ≤
        if j ∈ S then C₀ * μ * weightRadius N j i ^ (-(2 - s.val)) else 0 := by
      by_cases hj : j ∈ S
      · simp only [hj, ↓reduceIte, abs_mul]
        have hh := he N hN a ha B i j
        rw [← weightRadius_eq_comm N j i] at hh
        exact (mul_le_mul_of_nonneg_left (hζ j) (abs_nonneg _)).trans (by simpa only [mul_one] using hh)
      · have hle : weightRadius N j i ≤ R := by
          have hn : ¬R ≤ weightRadius N j i := by simpa only [S, mem_filter, mem_univ, true_and] using hj
          linarith
        simp only [hj, ↓reduceIte, hkeep j hle, sub_self, mul_zero, abs_zero, le_refl]
    calc
      _ ≤ ∑ j, if j ∈ S then C₀ * μ * weightRadius N j i ^ (-(2 - s.val)) else 0 :=
        sum_le_sum (fun j _ => hpoint j)
      _ = (C₀ * μ) * ∑ j ∈ S, weightRadius N j i ^ (-(2 - s.val)) := by
        rw [← sum_filter, filter_mem_eq_inter, univ_inter, mul_sum]
      _ ≤ (C₀ * μ) * (2 * (1 + 1 / ((2 - s.val) - 1)) * R ^ (1 - (2 - s.val))) :=
        mul_le_mul_of_nonneg_left (sum_weightRadius_tail_le N i hp hR) (by positivity)
      _ = _ := by
        dsimp [T]
        rw [show (2 - s.val) - 1 = 1 - s.val by ring,
          show 1 - (2 - s.val) = s.val - 1 by ring]
        ring
  have hidentity : (∑ j, A i j * ζ j) = (∑ j, A i j) - ∑ j, A i j * (1 - ζ j) := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro j _
    ring
  rw [hidentity]
  have hh := abs_sub_le (∑ j, A i j) 0 (∑ j, A i j * (1 - ζ j))
  simp only [sub_zero, zero_sub, abs_neg] at hh
  exact hh.trans ((add_le_add hm ((abs_sum_le_sum_abs ..).trans htail)).trans_eq (by ring))


/-- The signed-mass estimate for the actual first smooth cutoff in the
retained resolvent row of the proof of Lemma 5.13.
It equals one through distance `rᵢ/16` and vanishes from `rᵢ/8` onward. -/
theorem spatial_smooth_retained_mass (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (a : ℝ) (ha : 0 < a) (B : ℝ) (i₀ i : Fin (N : ℕ)),
      16 ≤ weightRadius N i i₀ →
      |∑ j, factorizationMatrix s N hN a ha B i j *
        CutoffApproximation.scalarCutoff
          (16 * (Riesz1.cyclicIndexDistance N i j : ℝ) / weightRadius N i i₀)| ≤
        C * (a + B ^ 2 / a) * weightRadius N i i₀ ^ (s.val - 1) := by
  obtain ⟨C, hC, hb⟩ := spatial_retained_signed_mass hz s
  refine ⟨C * 16 ^ (1 - s.val), by positivity, ?_⟩
  intro N hN a ha B i₀ i hri
  let r := weightRadius N i i₀
  have hr : 0 < r := by dsimp [r]; linarith
  have hR : 1 ≤ r / 16 := by dsimp [r]; linarith
  have hRN : r / 16 ≤ (N : ℝ) := by
    have hd := Riesz1.APG.cyclicIndexDistance_le_half (N := N) i i₀
    have hh : 1 + Riesz1.cyclicIndexDistance N i i₀ ≤ (N : ℕ) := by omega
    have hx : r ≤ (N : ℝ) := by dsimp [r, weightRadius]; exact_mod_cast hh
    linarith
  have hh := hb N hN a ha B i (r / 16) hR hRN
    (fun j => CutoffApproximation.scalarCutoff
      (16 * (Riesz1.cyclicIndexDistance N i j : ℝ) / r))
    (fun j => by
      have h0 := CutoffApproximation.scalarCutoff_nonneg
        (16 * (Riesz1.cyclicIndexDistance N i j : ℝ) / r)
      have h1 := CutoffApproximation.scalarCutoff_le_one
        (16 * (Riesz1.cyclicIndexDistance N i j : ℝ) / r)
      rw [abs_of_nonneg (by linarith)]
      linarith)
    (fun j hj => by
      apply CutoffApproximation.scalarCutoff_eq_one
      apply (div_le_one hr).mpr
      rw [weightRadius_eq_comm] at hj
      linarith)
  have hpower : (r / 16) ^ (s.val - 1) = 16 ^ (1 - s.val) * r ^ (s.val - 1) := by
    rw [Real.div_rpow hr.le (by norm_num)]
    have he : (16 : ℝ) ^ (s.val - 1) = (16 ^ (1 - s.val))⁻¹ := by
      rw [show s.val - 1 = -(1 - s.val) by ring, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 16)]
    rw [he, div_eq_mul_inv, inv_inv]
    ring
  rw [hpower] at hh
  convert hh using 1; ring

namespace Internal

/-- Internal application of the fractional row theorem to the two
localized row norms in the proof of Lemma 5.13.
Applications must establish these norms for their actual cutoff row. The
result keeps the strict gain `δ = s²(2-s)/4`, with no loss depending on size. -/
theorem spatial_far_row_of_norm_bounds (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    let t := 1 + s.val - s.val ^ 2 / 2
    let δ := s.val ^ 2 * (2 - s.val) / 4
    let q := 2 / s.val
    0 < δ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (R L : ℝ), 1 ≤ R → R ≤ (N : ℝ) → 0 ≤ L →
      ∀ F : Fin (N : ℕ) → ℝ,
      (∑ j, |F j| ^ q) ^ (1 / q) ≤ L * R ^ (-t + s.val / 2) →
      (∑ j, |F (j + 1) - F j| ^ q) ^ (1 / q) ≤ L * R ^ (-2 + s.val / 2) →
      (∑ j, |(F ᵥ* (rieszMatrix sh N hN)⁻¹) j| ^ q) ^ (1 / q) ≤
        C * L * R ^ (-(2 - s.val) - δ) := by
  dsimp only
  let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
    constructor <;> linarith [s.property.1, s.property.2]⟩
  let t := 1 + s.val - s.val ^ 2 / 2
  let δ := s.val ^ 2 * (2 - s.val) / 4
  let b := 1 - s.val / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    exact div_pos (mul_pos (sq_pos_of_pos s.property.1) (by linarith [s.property.2])) (by norm_num)
  refine ⟨hδ, ?_⟩
  obtain ⟨C, hC, hb⟩ := GlobalCancellation.global_row_cancellation hz s
  refine ⟨2 * C, by positivity, ?_⟩
  intro N hN R L hR hRN hL F hF hΔ
  have hRpos : 0 < R := by linarith
  have hNpos : (0 : ℝ) < N := by positivity
  let A₀ := L * R ^ (-t + s.val / 2)
  let A₁ := L * R ^ (-2 + s.val / 2)
  have hA₀ : 0 ≤ A₀ := mul_nonneg hL (Real.rpow_nonneg hRpos.le _)
  have hA₁ : 0 ≤ A₁ := mul_nonneg hL (Real.rpow_nonneg hRpos.le _)
  have hh := (hb N hN F A₀ A₁ hA₀ hA₁ hF hΔ).1
  have hmass : (N : ℝ) ^ (-b) * A₀ ≤ L * R ^ (-(2 - s.val) - δ) := by
    calc
      _ ≤ R ^ (-b) * A₀ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hRpos hRN (by dsimp [b]; linarith [s.property.2])) hA₀
      _ = L * R ^ (-2 + s.val ^ 2 / 2) := by
        dsimp only [A₀]
        rw [show R ^ (-b) * (L * R ^ (-t + s.val / 2)) =
          L * (R ^ (-b) * R ^ (-t + s.val / 2)) by ring, ← Real.rpow_add hRpos]
        congr 2
        dsimp [b, t]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hL
        apply Real.rpow_le_rpow_of_exponent_le hR
        have hgap : 0 ≤ (-(2 - s.val) - δ) - (-2 + s.val ^ 2 / 2) := by
          have hg := add_nonneg
            (mul_nonneg s.property.1.le (sub_nonneg.mpr s.property.2.le))
            (div_nonneg (pow_nonneg s.property.1.le 3) (by norm_num : (0 : ℝ) ≤ 4))
          convert hg using 1
          dsimp [δ]
          ring
        linarith
  have hinter : A₀ ^ (1 - b) * A₁ ^ b = L * R ^ (-(2 - s.val) - δ) := by
    dsimp only [A₀, A₁]
    rw [Real.mul_rpow hL (Real.rpow_nonneg hRpos.le _),
      Real.mul_rpow hL (Real.rpow_nonneg hRpos.le _)]
    calc
      _ = (L ^ (1 - b) * L ^ b) *
          ((R ^ (-t + s.val / 2)) ^ (1 - b) * (R ^ (-2 + s.val / 2)) ^ b) := by ring
      _ = _ := by
        rw [← Real.rpow_add' hL (by ring_nf; norm_num : (1 - b) + b ≠ 0),
          show (1 - b) + b = 1 by ring, Real.rpow_one,
          ← Real.rpow_mul hRpos.le, ← Real.rpow_mul hRpos.le, ← Real.rpow_add hRpos]
        congr 2
        dsimp [b, t, δ]
        ring
  change (∑ j, |(F ᵥ* (rieszMatrix sh N hN)⁻¹) j| ^ (2 / s.val)) ^ (1 / (2 / s.val)) ≤ _
  change (∑ j, |(F ᵥ* (rieszMatrix sh N hN)⁻¹) j| ^ (2 / s.val)) ^ (1 / (2 / s.val)) ≤
    C * ((N : ℝ) ^ (-b) * A₀ + A₀ ^ (1 - b) * A₁ ^ b) at hh
  rw [hinter] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left (add_le_add hmass (le_refl _)) hC.le).trans_eq (by ring))

end Internal

end Riesz2.GlobalCommutators
