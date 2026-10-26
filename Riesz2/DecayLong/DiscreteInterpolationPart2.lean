/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.DiscreteInterpolation
public import Riesz2.Preliminaries.ReciprocalSymbol
public import Riesz2.ToMathlib.FiniteNormInterpolation
public import Riesz2.ToMathlib.CutoffApproximation
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-!
# Shared estimates for angular interpolation

The symbol-ratio derivatives, dyadic scales, Fourier identities, and finite
norm inequalities used by the angular blocks in Lemma 5.9 of the paper.
The periodic-zeta input is explicit throughout.
-/

public section
noncomputable section

open Set Filter
open scoped Topology BigOperators ContDiff

namespace Riesz2.DiscreteInterpolation

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The symbol-ratio derivative step of the proof of Lemma 5.9:
one smooth representative and one positive constant control all three
derivative orders on the entire open angular interval. -/
theorem symbol_ratio_derivative_bounds (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    ∃ F : ℝ → ℝ, ContDiffOn ℝ ∞ F (Ioo 0 (2 * Real.pi)) ∧
      (∀ θ : Ioo (0 : ℝ) (2 * Real.pi),
        F θ.val = latticeRieszSymbol sh θ / latticeRieszSymbol s θ) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, j ≤ 2 →
        ∀ θ : Ioo (0 : ℝ) (2 * Real.pi),
          |iteratedDeriv j F θ.val| ≤
            C * symbolEndpointDistance θ ^ (-s.val / 2 - (j : ℝ)) := by
  dsimp only
  let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
    constructor <;> linarith [s.property.1, s.property.2]⟩
  let G : ℝ → ℝ := fun y => 2 + symbolZetaFactor sh *
    Riesz1.hurwitzKernel (1 - sh.val) (y / (2 * Real.pi))
  let H : ℝ → ℝ := fun y => reciprocalRieszSymbol s (y : AddCircle (2 * Real.pi))
  have hG : ContDiffOn ℝ ∞ G (Ioo 0 (2 * Real.pi)) := symbol_hurwitz_contDiff sh
  have hH : ContDiffOn ℝ ∞ H (Ioo 0 (2 * Real.pi)) :=
    reciprocalRieszSymbol_contDiffOn hz s
  obtain ⟨B₀, hB₀, hb₀⟩ := latticeRieszSymbol_all_derivatives hz sh 0
  obtain ⟨B₁, hB₁, hb₁⟩ := latticeRieszSymbol_all_derivatives hz sh 1
  obtain ⟨B₂, hB₂, hb₂⟩ := latticeRieszSymbol_all_derivatives hz sh 2
  let B := B₀ + B₁ + B₂
  have hB : 0 < B := by dsimp [B]; positivity
  have hb (j : ℕ) (hj : j ≤ 2) (θ : Ioo (0 : ℝ) (2 * Real.pi)) :
      |iteratedDeriv j G θ.val| ≤
        B * symbolEndpointDistance θ ^ (sh.val - 1 - (j : ℝ)) := by
    have hr (a : ℝ) : 0 ≤ symbolEndpointDistance θ ^ a :=
      Real.rpow_nonneg (symbolEndpointDistance_pos θ).le _
    interval_cases j
    · exact (hb₀ θ).trans (mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) (hr _))
    · exact (hb₁ θ).trans (mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) (hr _))
    · exact (hb₂ θ).trans (mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) (hr _))
  obtain ⟨D, hD, hd⟩ := reciprocalRieszSymbol_derivative_bounds hz s
  refine ⟨G * H, hG.mul hH, ?_, 4 * B * D, by positivity, ?_⟩
  · intro θ
    change G θ.val * H θ.val = _
    rw [show G θ.val = latticeRieszSymbol sh θ from
      (latticeRieszSymbol_eq_hurwitzKernel hz sh θ).symm,
      show H θ.val = (latticeRieszSymbol s θ)⁻¹ from reciprocalRieszSymbol_coe s θ]
    rfl
  · intro j hj θ
    have hρ := symbolEndpointDistance_pos θ
    have hG' : ContDiffAt ℝ j G θ.val :=
      (hG.of_le (by simp)).contDiffAt (isOpen_Ioo.mem_nhds θ.property)
    have hH' : ContDiffAt ℝ j H θ.val :=
      (hH.of_le (by simp)).contDiffAt (isOpen_Ioo.mem_nhds θ.property)
    rw [iteratedDeriv_mul hG' hH']
    have hterm (i : ℕ) (hi : i ∈ Finset.range (j + 1)) :
        |(j.choose i : ℝ) * iteratedDeriv i G θ.val * iteratedDeriv (j - i) H θ.val| ≤
          (j.choose i : ℝ) * (B * D * symbolEndpointDistance θ ^ (-s.val / 2 - (j : ℝ))) := by
      have hij : i ≤ j := by have := Finset.mem_range.mp hi; omega
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      calc
        _ ≤ ((j.choose i : ℝ) *
              (B * symbolEndpointDistance θ ^ (sh.val - 1 - (i : ℝ)))) *
            (D * symbolEndpointDistance θ ^ (1 - s.val - ((j - i : ℕ) : ℝ))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hb i (hij.trans hj) θ)
            (Nat.cast_nonneg _)) (hd (j - i) (by omega) θ)
              (abs_nonneg _) (by positivity)
        _ = _ := by
          rw [Nat.cast_sub hij]
          have he : (sh.val - 1 - (i : ℝ)) + (1 - s.val - ((j : ℝ) - i)) =
              -s.val / 2 - j := by dsimp [sh]; ring
          calc
            _ = ((j.choose i : ℝ) * B * D) *
                (symbolEndpointDistance θ ^ (sh.val - 1 - (i : ℝ)) *
                  symbolEndpointDistance θ ^ (1 - s.val - ((j : ℝ) - i))) := by ring
            _ = _ := by rw [← Real.rpow_add hρ, he]; ring
    calc
      _ ≤ ∑ i ∈ Finset.range (j + 1),
          |(j.choose i : ℝ) * iteratedDeriv i G θ.val * iteratedDeriv (j - i) H θ.val| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          (B * D * symbolEndpointDistance θ ^ (-s.val / 2 - (j : ℝ))) :=
        Finset.sum_le_sum hterm
      _ = (2 : ℝ) ^ j * (B * D * symbolEndpointDistance θ ^ (-s.val / 2 - (j : ℝ))) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose j
      _ ≤ 4 * (B * D * symbolEndpointDistance θ ^ (-s.val / 2 - (j : ℝ))) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj).trans_eq (by norm_num)
      _ = _ := by ring

/-- The annular symbol-ratio derivative step of the proof of Lemma 5.9.
The same representative and constant work for every positive scale. -/
theorem symbol_ratio_annular_derivative_bounds (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    ∃ F : ℝ → ℝ, ContDiffOn ℝ ∞ F (Ioo 0 (2 * Real.pi)) ∧
      (∀ θ : Ioo (0 : ℝ) (2 * Real.pi),
        F θ.val = latticeRieszSymbol sh θ / latticeRieszSymbol s θ) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ), 0 < t → ∀ j : ℕ, j ≤ 2 →
        ∀ θ : Ioo (0 : ℝ) (2 * Real.pi), t ≤ frequencyRadius θ.val →
          |iteratedDeriv j F θ.val| ≤ C * t ^ (-s.val / 2 - (j : ℝ)) := by
  dsimp only
  obtain ⟨F, hF, heq, C, hC, hb⟩ := symbol_ratio_derivative_bounds hz s
  refine ⟨F, hF, heq, C, hC, fun t ht j hj θ hθ => (hb j hj θ).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow_of_nonpos ht
  · exact hθ.trans (radius_le_endpointDistance ⟨θ.property.1.le, θ.property.2.le⟩)
  · have : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    linarith [s.property.1]

/-! ## The explicit frequency partition -/

/-- The frequency radius has angular period `2π`. -/
theorem periodic_frequencyRadius : Function.Periodic frequencyRadius (2 * Real.pi) := by
  intro θ
  simp only [frequencyRadius, show (θ + 2 * Real.pi) / 2 = θ / 2 + Real.pi by ring,
    Real.sin_add_pi, abs_neg]

/-- The scale formula agrees exactly with the geometric scale family used
by the shell telescoping theorem. -/
theorem dyadicScale_eq_pow_mul (N : ℕ+) (j : ℕ) :
    dyadicScale N j = (2 : ℝ) ^ j * dyadicScale N 0 := by
  simp only [dyadicScale, Nat.cast_zero, zero_sub, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0),
    zpow_natCast, zpow_neg, zpow_natCast, div_eq_mul_inv]

/-- The smallest dyadic scale is at most `1/(4N)`, as in Subsection 5.2. -/
theorem dyadicScale_zero_le (N : ℕ+) : dyadicScale N 0 ≤ 1 / (4 * (N : ℝ)) := by
  have hpow : (N : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 (N : ℕ) := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) (N : ℕ)
  have hN : (0 : ℝ) < N := by positivity
  simp only [dyadicScale, Nat.cast_zero, zero_sub, zpow_neg, zpow_natCast,
    dyadicDepth, pow_add, pow_two]
  rw [one_div]
  apply inv_anti₀ (by positivity)
  nlinarith

/-- The top geometric cutoff is at radius two. -/
theorem dyadicScale_top (N : ℕ+) :
    (2 : ℝ) ^ (dyadicDepth N + 1) * dyadicScale N 0 = 2 := by
  simp only [dyadicScale, Nat.cast_zero, zero_sub, zpow_neg, zpow_natCast,
    pow_succ]
  have hne : (2 : ℝ) ^ dyadicDepth N ≠ 0 := by positivity
  field_simp

/-- Nonzero grid frequencies have radius at least `4/N`. In particular the
lowest cutoff never removes a nonzero mode (Subsection 5.2). -/
theorem cycle_frequencyRadius_lower (N : ℕ+) (k : Fin (N : ℕ)) (hk : k ≠ 0) :
    4 / (N : ℝ) ≤ frequencyRadius (cycleAngle N k) := by
  have hN : (0 : ℝ) < N := by positivity
  have hk1 : (1 : ℝ) ≤ k.val := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hk (Fin.ext h))
  have hkN : (k.val : ℝ) + 1 ≤ N := by exact_mod_cast k.isLt
  have hd : 2 * Real.pi / (N : ℝ) ≤
      min (cycleAngle N k) (2 * Real.pi - cycleAngle N k) := by
    apply le_min
    · dsimp [cycleAngle]
      exact div_le_div_of_nonneg_right (by nlinarith [Real.pi_pos]) hN.le
    · dsimp [cycleAngle]
      rw [le_sub_iff_add_le, ← add_div, div_le_iff₀ hN]
      nlinarith [Real.pi_pos]
  have hs := endpointDistance_le_radius
    (Ioo_subset_Icc_self (cycleAngle_mem_Ioo N k hk))
  rw [div_le_iff₀ hN] at hd ⊢
  nlinarith [Real.pi_pos]

/-- The block-count step of the proof of Lemma 5.9, with the
explicit absolute constant `5 / log 2`. -/
theorem dyadicDepth_log_bound (N : ℕ+) :
    ((dyadicDepth N + 1 : ℕ) : ℝ) ≤ (5 / Real.log 2) * Real.log (2 * (N : ℝ)) := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hN0 : (0 : ℝ) < N := by positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc := Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hN)
  have he := Real.natCeil_logb_natCast 2 (N : ℕ)
  norm_num only [Nat.cast_ofNat] at he
  rw [he] at hc
  have hlo : Real.log 2 ≤ Real.log (2 * (N : ℝ)) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hhi : Real.log (N : ℝ) ≤ Real.log (2 * (N : ℝ)) :=
    Real.log_le_log hN0 (by linarith)
  rw [Real.logb] at hc
  have hc' : ((Nat.clog 2 (N : ℕ) : ℕ) : ℝ) * Real.log 2 < Real.log (N : ℝ) + Real.log 2 := by
    have hh := mul_lt_mul_of_pos_right hc hlog2
    rw [add_mul, div_mul_cancel₀ _ hlog2.ne', one_mul] at hh
    exact hh
  rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
  simp only [dyadicDepth, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  nlinarith

/-! ## The localized ratio across the angular seam -/

/-- On the open angular cell the radius has its smooth sine formula. -/
theorem frequencyRadius_eq_sin {x : ℝ} (hx : x ∈ Ioo 0 (2 * Real.pi)) :
    frequencyRadius x = 2 * Real.sin (x / 2) := by
  rw [frequencyRadius, abs_of_pos (Real.sin_pos_of_pos_of_lt_pi
    (by linarith [hx.1]) (by linarith [hx.2]))]

/-- A cyclic multiplier is convolution with its inverse transform. -/
theorem multiplier_eq_convolution (N : ℕ+) (b u : Fin (N : ℕ) → ℂ) :
    cycleFourierInv N (fun k => b k * cycleFourier N u k) =
      cycleConvolution N (cycleFourierInv N b) u := by
  funext i
  rw [← cycleFourierInv_cycleFourier (cycleConvolution N (cycleFourierInv N b) u) i]
  congr 1
  funext k
  rw [cycleFourier_convolution, cycleFourier_cycleFourierInv]

/-- Young's counting-measure `ℓ¹` bound for the cyclic convolution. -/
theorem cycleConvolution_l1 (N : ℕ+) (f u : Fin (N : ℕ) → ℂ) :
    (∑ i, ‖cycleConvolution N f u i‖) ≤ (∑ i, ‖f i‖) * (∑ i, ‖u i‖) := by
  have hs (j : Fin (N : ℕ)) :
      (∑ i : Fin (N : ℕ), ‖f (Riesz1.labelOf N ((i.val : ℤ) - j.val))‖) = ∑ i, ‖f i‖ :=
    Fintype.sum_bijective _ (bijective_labelOf_sub j) _ _ (fun _ => rfl)
  calc
    _ ≤ ∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ), ‖f (Riesz1.labelOf N ((i.val : ℤ) - j.val))‖ * ‖u j‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact (norm_sum_le _ _).trans_eq (by simp only [norm_mul])
    _ = ∑ j : Fin (N : ℕ), (∑ i : Fin (N : ℕ), ‖f (Riesz1.labelOf N ((i.val : ℤ) - j.val))‖) * ‖u j‖ := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = _ := by
      simp_rw [hs]
      rw [← Finset.mul_sum]

/-- The sampled Riesz matrix is precisely convolution with the sampled kernel: this proves the sign/evenness bridge for Subsection 2.4. -/
theorem sampledRieszMatrix_eq_convolution (s : Riesz1.RieszExponent)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (u : Fin (N : ℕ) → ℝ) :
    (fun i => ((Matrix.of (fun a b : Fin (N : ℕ) =>
      sampledRieszKernel s N hN (b - a))).mulVec u i : ℂ)) =
      cycleConvolution N (fun i => (sampledRieszKernel s N hN i : ℂ)) (fun i => (u i : ℂ)) := by
  have hlabel (a b : Fin (N : ℕ)) : Riesz1.labelOf N ((b.val : ℤ) - a.val) = b - a := by
    apply Fin.ext
    apply Int.ofNat_inj.mp
    rw [Riesz1.APG.labelOf_val, Fin.val_sub]
    rw [Int.natCast_emod, Nat.cast_add, Nat.cast_sub (Nat.le_of_lt a.isLt)]
    rw [show ((N : ℕ) : ℤ) - a.val + b.val = ((b.val : ℤ) - a.val) + (N : ℕ) by ring]
    simp only [Int.add_emod, Int.emod_self, add_zero, Int.emod_emod]
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Complex.ofReal_sum,
    Complex.ofReal_mul, cycleConvolution, hlabel]
  apply Finset.sum_congr rfl
  intro j _
  rw [show j - i = -(i - j) by abel, sampledRieszKernel_even]

/-- Parseval gives the counting-measure squared `ℓ²` multiplier estimate. -/
theorem multiplier_l2_sq (N : ℕ+) (b u : Fin (N : ℕ) → ℂ)
    {B : ℝ} (_hB : 0 ≤ B) (hb : ∀ k, ‖b k‖ ≤ B) :
    (∑ i, ‖cycleFourierInv N (fun k => b k * cycleFourier N u k) i‖ ^ 2) ≤
      B ^ 2 * (∑ i, ‖u i‖ ^ 2) := by
  rw [sum_norm_sq_cycleFourier, sum_norm_sq_cycleFourier u]
  simp only [cycleFourier_cycleFourierInv, norm_mul, mul_pow]
  rw [mul_left_comm (B ^ 2)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hb k) 2) (sq_nonneg _)

/-- Minkowski for a finite family of complex sequences, expressed in
ordinary counting-measure power sums. -/
theorem finite_sum_lp {ι κ : Type*} [Fintype ι] (S : Finset κ)
    (v : κ → ι → ℂ) {p : ℝ} (hp : 1 ≤ p) :
    (∑ i, ‖∑ j ∈ S, v j i‖ ^ p) ^ (1 / p) ≤
      ∑ j ∈ S, (∑ i, ‖v j i‖ ^ p) ^ (1 / p) := by
  classical
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, norm_zero, Real.zero_rpow hp0.ne',
      Finset.sum_const_zero, Real.zero_rpow (by positivity : (1 / p : ℝ) ≠ 0), le_refl]
  | @insert j S hj ih =>
    simp only [Finset.sum_insert hj]
    calc
      _ ≤ (∑ i, (‖v j i‖ + ‖∑ k ∈ S, v k i‖) ^ p) ^ (1 / p) := by
        apply Real.rpow_le_rpow (Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _))
          _ (by positivity)
        apply Finset.sum_le_sum
        intro i _
        exact Real.rpow_le_rpow (norm_nonneg _) (norm_add_le _ _) hp0.le
      _ ≤ (∑ i, ‖v j i‖ ^ p) ^ (1 / p) +
          (∑ i, ‖∑ k ∈ S, v k i‖ ^ p) ^ (1 / p) := by
        exact Real.Lp_add_le_of_nonneg (f := fun i => ‖v j i‖)
          (g := fun i => ‖∑ k ∈ S, v k i‖) Finset.univ hp
          (fun _ _ => norm_nonneg _) (fun _ _ => norm_nonneg _)
      _ ≤ _ := add_le_add_right ih _

/-- Deterministic block interpolation with exact scale cancellation.
This is an internal assembly lemma for the proof of Lemma 5.9. -/
theorem block_interpolation {ι : Type*} [Fintype ι]
    (s : Riesz1.RieszExponent) (v : ι → ℂ) {t A B C D : ℝ}
    (ht : 0 < t) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (h₁ : (∑ i, ‖v i‖) ≤ C * t ^ (-s.val / 2) * A)
    (h₂ : (∑ i, ‖v i‖ ^ 2) ^ (1 / 2 : ℝ) ≤ D * t ^ ((1 - s.val) / 2) * B) :
    (∑ i, ‖v i‖ ^ (1 - s.val / 2)⁻¹) ^ (1 - s.val / 2) ≤
      C ^ (1 - s.val) * D ^ s.val * A ^ (1 - s.val) * B ^ s.val := by
  have hs := s.property
  have hsum : 0 ≤ ∑ i, ‖v i‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hi := FiniteNormInterpolation.l1_l2_interpolation_theta Finset.univ hs.1 hs.2
    (fun i => ‖v i‖) (fun _ => norm_nonneg _)
  have he : (∑ i, ‖v i‖ ^ 2) ^ (s.val / 2) =
      ((∑ i, ‖v i‖ ^ 2) ^ (1 / 2 : ℝ)) ^ s.val := by
    rw [← Real.rpow_mul hsum]
    congr 1
    ring
  rw [he] at hi
  apply hi.trans
  calc
    _ ≤ (C * t ^ (-s.val / 2) * A) ^ (1 - s.val) *
        (D * t ^ ((1 - s.val) / 2) * B) ^ s.val :=
      mul_le_mul (Real.rpow_le_rpow (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) h₁ (by linarith))
        (Real.rpow_le_rpow (Real.rpow_nonneg hsum _) h₂ hs.1.le)
        (by positivity) (by positivity)
    _ = _ := by
      rw [mul_assoc C, mul_assoc D,
        Real.mul_rpow hC (by positivity), Real.mul_rpow hD (by positivity)]
      calc
        _ = (C ^ (1 - s.val) * D ^ s.val) *
            ((t ^ (-s.val / 2) * A) ^ (1 - s.val) *
              (t ^ ((1 - s.val) / 2) * B) ^ s.val) := by ring
        _ = _ := by rw [FiniteNormInterpolation.block_scale_cancellation ht hA hB]; ring


end Riesz2.DiscreteInterpolation
