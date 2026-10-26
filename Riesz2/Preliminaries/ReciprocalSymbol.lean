/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Preliminaries.SymbolBounds
public import Riesz2.ToMathlib.FractionalCuspFourier
public import Riesz2.ToMathlib.ReciprocalCusp
public import Riesz2.ToMathlib.RealEvenFourier

/-!
# Reciprocal lattice symbol and its Fourier coefficients

The value at the origin of the angular circle is the continuous extension of the
reciprocal on the punctured circle, as in Subsection 2.4. The divergent
symbol is never evaluated at an endpoint.
-/

@[expose] public section
noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ComplexConjugate

namespace Riesz2

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- See Subsection 2.4 of the paper: the reciprocal on the angular circle. The separate
origin value is justified by `continuous_reciprocalRieszSymbol` below. Every
nonzero point uses its unique representative in the open angular interval. -/
def reciprocalRieszSymbol (s : Riesz1.RieszExponent)
    (x : AddCircle (2 * Real.pi)) : ℝ :=
  let θ := AddCircle.equivIco (2 * Real.pi) 0 x
  if h : θ.val = 0 then 0 else
    (latticeRieszSymbol s ⟨θ.val, lt_of_le_of_ne θ.property.1 (Ne.symm h),
      by simpa using θ.property.2⟩)⁻¹

/-- The specified cusp value in Subsection 2.4. -/
theorem reciprocalRieszSymbol_zero (s : Riesz1.RieszExponent) :
    reciprocalRieszSymbol s 0 = 0 := by
  have hz : (AddCircle.equivIco (2 * Real.pi) 0 (0 : AddCircle (2 * Real.pi))).val = 0 := by
    simpa using AddCircle.equivIco_coe_of_mem (p := 2 * Real.pi)
      (a := 0) (y := (0 : ℝ)) (by constructor <;> linarith [Real.pi_pos])
  simp [reciprocalRieszSymbol, hz]

/-- Agreement with the reciprocal of the symbol on its exact domain. -/
theorem reciprocalRieszSymbol_coe (s : Riesz1.RieszExponent)
    (θ : Ioo (0 : ℝ) (2 * Real.pi)) :
    reciprocalRieszSymbol s (θ.val : AddCircle (2 * Real.pi)) =
      (latticeRieszSymbol s θ)⁻¹ := by
  have he := AddCircle.equivIco_coe_eq (p := 2 * Real.pi) (a := 0)
    (x := θ.val) (by simpa using And.intro θ.property.1.le θ.property.2)
  simp only [reciprocalRieszSymbol, he]
  rw [dite_eq_right θ.property.1.ne']

/-- Positivity of the symbol, with no external hypothesis. -/
theorem latticeRieszSymbol_pos (s : Riesz1.RieszExponent)
    (θ : Ioo (0 : ℝ) (2 * Real.pi)) : 0 < latticeRieszSymbol s θ :=
  lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) (latticeRieszSymbol_lower s θ)

/-- The reciprocal equals a smooth ambient representative locally on the open
interval. No value of this representative at a singular endpoint is used. -/
theorem reciprocalRieszSymbol_eventuallyEq (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) {θ : ℝ} (hθ : θ ∈ Ioo 0 (2 * Real.pi)) :
    (fun y : ℝ => reciprocalRieszSymbol s (y : AddCircle (2 * Real.pi))) =ᶠ[𝓝 θ]
      (fun y : ℝ => (2 + symbolZetaFactor s *
        Riesz1.hurwitzKernel (1 - s.val) (y / (2 * Real.pi)))⁻¹) := by
  filter_upwards [isOpen_Ioo.mem_nhds hθ] with y hy
  rw [reciprocalRieszSymbol_coe s ⟨y, hy⟩,
    latticeRieszSymbol_eq_hurwitzKernel hz s ⟨y, hy⟩]

/-- Smoothness away from the origin, part of the proof of Lemma 2.5. -/
theorem reciprocalRieszSymbol_contDiffOn (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ContDiffOn ℝ ∞
      (fun y : ℝ => reciprocalRieszSymbol s (y : AddCircle (2 * Real.pi)))
        (Ioo 0 (2 * Real.pi)) := by
  have hF := (symbol_hurwitz_contDiff s).inv (fun y hy => by
    rw [← latticeRieszSymbol_eq_hurwitzKernel hz s ⟨y, hy⟩]
    exact (latticeRieszSymbol_pos s _).ne')
  exact hF.congr (fun y hy => (reciprocalRieszSymbol_eventuallyEq hz s hy).eq_of_nhds)

/-- The zeroth-order cusp estimate, part of the proof of Lemma 2.5. -/
theorem reciprocalRieszSymbol_power_bound (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ : Ioo (0 : ℝ) (2 * Real.pi),
      |reciprocalRieszSymbol s (θ.val : AddCircle (2 * Real.pi))| ≤
        C * symbolEndpointDistance θ ^ (1 - s.val) := by
  obtain ⟨c, _, hc, _, hb⟩ := latticeRieszSymbol_power_bounds hz s
  refine ⟨c⁻¹, inv_pos.mpr hc, fun θ => ?_⟩
  rw [reciprocalRieszSymbol_coe, abs_of_pos (inv_pos.mpr (latticeRieszSymbol_pos s θ))]
  have h := one_div_le_one_div_of_le
    (mul_pos hc (Real.rpow_pos_of_pos (symbolEndpointDistance_pos θ) _)) (hb θ).1
  simpa only [one_div, mul_inv_rev, show s.val - 1 = -(1 - s.val) by ring,
    Real.rpow_neg (symbolEndpointDistance_pos θ).le, inv_inv, mul_comm] using h

/-- Continuity on the entire angular circle, including the prescribed zero cusp
value (the proof of Lemma 2.5). -/
theorem continuous_reciprocalRieszSymbol (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) : Continuous (reciprocalRieszSymbol s) := by
  let H := fun y : ℝ => reciprocalRieszSymbol s (y : AddCircle (2 * Real.pi))
  obtain ⟨C, hC, hb⟩ := reciprocalRieszSymbol_power_bound hz s
  have hη : 0 < 1 - s.val := sub_pos.mpr s.property.2
  have h0 : H 0 = 0 := by simpa [H] using reciprocalRieszSymbol_zero s
  have hT : H (2 * Real.pi) = 0 := by
    change reciprocalRieszSymbol s (↑(2 * Real.pi) : AddCircle (2 * Real.pi)) = 0
    rw [AddCircle.coe_period, reciprocalRieszSymbol_zero]
  have hbound : ∀ y ∈ Icc 0 (2 * Real.pi),
      ‖H y‖ ≤ C * (min y (2 * Real.pi - y)) ^ (1 - s.val) := by
    intro y hy
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hy with rfl | rfl | hy
    · simp [h0, min_eq_left (by linarith [Real.pi_pos] : (0 : ℝ) ≤ 2 * Real.pi),
        Real.zero_rpow hη.ne']
    · simp [hT, min_eq_right (by linarith [Real.pi_pos] : (0 : ℝ) ≤ 2 * Real.pi),
        Real.zero_rpow hη.ne']
    · exact hb ⟨y, hy⟩
  have henv : Continuous (fun y : ℝ => C * (min y (2 * Real.pi - y)) ^ (1 - s.val)) :=
    continuous_const.mul ((Real.continuous_rpow_const hη.le).comp
      (continuous_id.min (continuous_const.sub continuous_id)))
  have hends (a : ℝ) (ha : a = 0 ∨ a = 2 * Real.pi) :
      ContinuousWithinAt H (Icc 0 (2 * Real.pi)) a := by
    have hHa : H a = 0 := by rcases ha with rfl | rfl <;> assumption
    rw [ContinuousWithinAt, hHa]
    apply squeeze_zero_norm' (by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact hbound y hy)
    convert henv.continuousAt.continuousWithinAt.tendsto using 1
    rcases ha with rfl | rfl <;>
      simp [Real.zero_rpow hη.ne', min_eq_left (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
        min_eq_right (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  have hcc : ContinuousOn H (Icc 0 (2 * Real.pi)) := by
    intro y hy
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hy with rfl | rfl | hy
    · exact hends 0 (Or.inl rfl)
    · exact hends _ (Or.inr rfl)
    · exact ((reciprocalRieszSymbol_contDiffOn hz s).contDiffAt
        (isOpen_Ioo.mem_nhds hy)).continuousAt.continuousWithinAt
  have he : AddCircle.liftIco (2 * Real.pi) 0 H = reciprocalRieszSymbol s := by
    funext x
    exact congrArg (reciprocalRieszSymbol s) AddCircle.coe_equivIco
  rw [← he]
  exact AddCircle.liftIco_zero_continuous (h0.trans hT.symm) hcc

/-- The three derivative estimates with one common constant, as required by
the proof of Lemma 2.5. -/
theorem reciprocalRieszSymbol_derivative_bounds (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, j ≤ 2 →
      ∀ θ : Ioo (0 : ℝ) (2 * Real.pi),
        |iteratedDeriv j
          (fun y : ℝ => reciprocalRieszSymbol s (y : AddCircle (2 * Real.pi))) θ.val| ≤
            C * symbolEndpointDistance θ ^ (1 - s.val - (j : ℝ)) := by
  let F := fun y : ℝ => 2 + symbolZetaFactor s *
    Riesz1.hurwitzKernel (1 - s.val) (y / (2 * Real.pi))
  obtain ⟨c, _, hc, _, hlower⟩ := latticeRieszSymbol_power_bounds hz s
  obtain ⟨D, hD, hder1⟩ := latticeRieszSymbol_all_derivatives hz s 1
  obtain ⟨E, hE, hder2⟩ := latticeRieszSymbol_all_derivatives hz s 2
  let C := c⁻¹ + D * c⁻¹ ^ 2 + (2 * D ^ 2 * c⁻¹ ^ 3 + E * c⁻¹ ^ 2)
  have hci : 0 < c⁻¹ := inv_pos.mpr hc
  have hb1 : 0 ≤ D * c⁻¹ ^ 2 := by positivity
  have hb2 : 0 ≤ 2 * D ^ 2 * c⁻¹ ^ 3 + E * c⁻¹ ^ 2 := by positivity
  have hB0 : c⁻¹ ≤ C := by dsimp [C]; linarith
  have hB1 : D * c⁻¹ ^ 2 ≤ C := by dsimp [C]; linarith
  have hB2 : 2 * D ^ 2 * c⁻¹ ^ 3 + E * c⁻¹ ^ 2 ≤ C := by dsimp [C]; linarith
  refine ⟨C, by dsimp [C]; positivity, fun j hj θ => ?_⟩
  have hρ := symbolEndpointDistance_pos θ
  have hlo : c * symbolEndpointDistance θ ^ (s.val - 1) ≤ F θ.val := by
    simpa only [F, ← latticeRieszSymbol_eq_hurwitzKernel hz s θ] using (hlower θ).1
  have hd1 : |deriv F θ.val| ≤ D * symbolEndpointDistance θ ^ (s.val - 1 - 1) := by
    simpa only [F, iteratedDeriv_succ, iteratedDeriv_zero, Nat.cast_one] using hder1 θ
  have hd2 : |deriv (deriv F) θ.val| ≤
      E * symbolEndpointDistance θ ^ (s.val - 1 - 2) := by
    simpa only [F, iteratedDeriv_succ, iteratedDeriv_zero, Nat.cast_ofNat] using hder2 θ
  rw [(reciprocalRieszSymbol_eventuallyEq hz s θ.property).iteratedDeriv_eq j]
  have hF : ContDiffOn ℝ 2 F (Ioo 0 (2 * Real.pi)) :=
    (symbol_hurwitz_contDiff s).of_le (by norm_num)
  have hne : ∀ y ∈ Ioo 0 (2 * Real.pi), F y ≠ 0 := by
    intro y hy
    dsimp only [F]
    rw [← latticeRieszSymbol_eq_hurwitzKernel hz s ⟨y, hy⟩]
    exact (latticeRieszSymbol_pos s _).ne'
  interval_cases j
  · simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero]
    have hb := ReciprocalCusp.inv_bound hc hρ hlo
    rw [show -(s.val - 1) = 1 - s.val by ring] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right hB0 (Real.rpow_nonneg hρ.le _))
  · simp only [iteratedDeriv_succ, iteratedDeriv_zero, Nat.cast_one]
    rw [deriv_fun_inv'' ((hF.contDiffAt (isOpen_Ioo.mem_nhds θ.property)).differentiableAt
      (by norm_num)) (hne θ θ.property)]
    have hb := ReciprocalCusp.first_bound hc hD.le hρ hlo hd1
    rw [show -(s.val - 1) - 1 = 1 - s.val - 1 by ring] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right hB1 (Real.rpow_nonneg hρ.le _))
  · simp only [iteratedDeriv_succ, iteratedDeriv_zero, Nat.cast_ofNat]
    rw [ReciprocalCusp.second_derivative isOpen_Ioo hF hne θ.property]
    have hb := ReciprocalCusp.second_bound hc hD.le hE.le hρ hlo hd1 hd2
    rw [show -(s.val - 1) - 2 = 1 - s.val - 2 by ring] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right hB2 (Real.rpow_nonneg hρ.le _))

/-- Reflection of the lattice symbol, used for the evenness clause of
the proof of Lemma 2.5. -/
theorem latticeRieszSymbol_reflection (s : Riesz1.RieszExponent)
    (θ : Ioo (0 : ℝ) (2 * Real.pi)) :
    latticeRieszSymbol s ⟨2 * Real.pi - θ.val,
      by constructor <;> linarith [θ.property.1, θ.property.2]⟩ =
      latticeRieszSymbol s θ := by
  unfold latticeRieszSymbol
  apply tsum_congr
  intro r
  simp only
  rw [Real.cos_two_pi_sub, mul_sub, Real.cos_nat_mul_two_pi_sub]

/-- Evenness on the whole circle, including the cusp (the proof of Lemma 2.5). -/
theorem reciprocalRieszSymbol_neg (s : Riesz1.RieszExponent)
    (x : AddCircle (2 * Real.pi)) :
    reciprocalRieszSymbol s (-x) = reciprocalRieszSymbol s x := by
  let θ := AddCircle.equivIco (2 * Real.pi) 0 x
  have hx : (θ.val : AddCircle (2 * Real.pi)) = x := AddCircle.coe_equivIco
  by_cases hθ : θ.val = 0
  · have hx0 : x = 0 := by rw [← hx, hθ, AddCircle.coe_zero]
    simp [hx0]
  · have hmem : θ.val ∈ Ioo 0 (2 * Real.pi) :=
      ⟨lt_of_le_of_ne θ.property.1 (Ne.symm hθ), by simpa using θ.property.2⟩
    have hneg : ((2 * Real.pi - θ.val : ℝ) : AddCircle (2 * Real.pi)) = -x := by
      rw [AddCircle.coe_sub, AddCircle.coe_period, hx, zero_sub]
    rw [← hneg, ← hx]
    rw [reciprocalRieszSymbol_coe s ⟨θ.val, hmem⟩,
      reciprocalRieszSymbol_coe s
        ⟨2 * Real.pi - θ.val, by constructor <;> linarith [hmem.1, hmem.2]⟩,
      latticeRieszSymbol_reflection s ⟨θ.val, hmem⟩]

/-- Boundedness on the whole circle, from the proved continuous extension. -/
theorem reciprocalRieszSymbol_bounded (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : AddCircle (2 * Real.pi),
      |reciprocalRieszSymbol s x| ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_univ.bddAbove_image
    (continuous_reciprocalRieszSymbol hz s).abs.continuousOn
  refine ⟨|B| + 1, by positivity, fun x => ?_⟩
  have hx : |reciprocalRieszSymbol s x| ≤ B := hB ⟨x, mem_univ x, rfl⟩
  linarith [le_abs_self B]

/-- Every defining coefficient integral in Subsection 2.4 is integrable. -/
theorem reciprocalRieszSymbol_intervalIntegrable (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (n : ℤ) :
    IntervalIntegrable (fun y : ℝ =>
      (reciprocalRieszSymbol s (y : AddCircle (2 * Real.pi)) : ℂ) *
        Complex.exp (-(n : ℂ) * Complex.I * (y : ℂ))) volume 0 (2 * Real.pi) := by
  have hc := Complex.continuous_ofReal.comp
    ((continuous_reciprocalRieszSymbol hz s).comp (AddCircle.continuous_mk' _))
  exact (hc.mul (by fun_prop)).intervalIntegrable 0 (2 * Real.pi)

/-- See the proof of Lemma 2.5 in the paper, including continuity at the cusp,
evenness, smoothness off zero, the common three-order estimate, boundedness and
integrability. Realness is expressed by the real codomain of the symbol. -/
theorem reciprocalRieszSymbol_regularity (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    Continuous (reciprocalRieszSymbol s) ∧
    (∀ x : AddCircle (2 * Real.pi), reciprocalRieszSymbol s (-x) = reciprocalRieszSymbol s x) ∧
    ContDiffOn ℝ ∞ (fun y : ℝ => reciprocalRieszSymbol s (y : AddCircle (2 * Real.pi)))
      (Ioo 0 (2 * Real.pi)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, j ≤ 2 → ∀ θ : Ioo (0 : ℝ) (2 * Real.pi),
      |iteratedDeriv j
        (fun y : ℝ => reciprocalRieszSymbol s (y : AddCircle (2 * Real.pi))) θ.val| ≤
          C * symbolEndpointDistance θ ^ (1 - s.val - (j : ℝ))) ∧
    (∃ B : ℝ, 0 < B ∧ ∀ x : AddCircle (2 * Real.pi), |reciprocalRieszSymbol s x| ≤ B) ∧
    ∀ n : ℤ, IntervalIntegrable (fun y : ℝ =>
      (reciprocalRieszSymbol s (y : AddCircle (2 * Real.pi)) : ℂ) *
        Complex.exp (-(n : ℂ) * Complex.I * (y : ℂ))) volume 0 (2 * Real.pi) := by
  exact ⟨continuous_reciprocalRieszSymbol hz s, reciprocalRieszSymbol_neg s,
    reciprocalRieszSymbol_contDiffOn hz s, reciprocalRieszSymbol_derivative_bounds hz s,
    reciprocalRieszSymbol_bounded hz s, reciprocalRieszSymbol_intervalIntegrable hz s⟩

/-- See Subsection 2.4 of the paper: the infinite inverse coefficients, using Mathlib's
Fourier coefficients with normalized angular Haar measure. The next theorem
identifies this definition with the exact inverse-transform integral. -/
def inverseRieszCoefficient (s : Riesz1.RieszExponent) (n : ℤ) : ℂ :=
  fourierCoeff (fun x : AddCircle (2 * Real.pi) => (reciprocalRieszSymbol s x : ℂ)) n

/-- The normalized negative-sign coefficient integral of Subsection 2.4. -/
theorem inverseRieszCoefficient_eq_integral (s : Riesz1.RieszExponent) (n : ℤ) :
    inverseRieszCoefficient s n = (1 / (2 * Real.pi)) •
      ∫ y in (0 : ℝ)..(2 * Real.pi),
        (reciprocalRieszSymbol s (y : AddCircle (2 * Real.pi)) : ℂ) *
          Complex.exp (-(n : ℂ) * Complex.I * (y : ℂ)) :=
  FractionalCuspFourier.fourierCoeff_angular _ n

/-- Evenness of the infinite inverse coefficients (the proof of Lemma 2.5). -/
theorem inverseRieszCoefficient_neg (s : Riesz1.RieszExponent) (n : ℤ) :
    inverseRieszCoefficient s (-n) = inverseRieszCoefficient s n :=
  CircleFourier.coefficient_neg_of_even _
    (fun x => congrArg Complex.ofReal (reciprocalRieszSymbol_neg s x)) n

/-- Realness of the infinite inverse coefficients (the proof of Lemma 2.5). -/
theorem inverseRieszCoefficient_im (s : Riesz1.RieszExponent) (n : ℤ) :
    (inverseRieszCoefficient s n).im = 0 :=
  CircleFourier.coefficient_im_of_real_even _ (reciprocalRieszSymbol_neg s) n

/-- Complexification preserves all three cusp estimates. -/
theorem reciprocalRieszSymbol_complex_derivative_bounds (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, j ≤ 2 → ∀ θ ∈ Ioo (0 : ℝ) (2 * Real.pi),
      ‖iteratedDeriv j (fun y : ℝ =>
        (reciprocalRieszSymbol s (y : AddCircle (2 * Real.pi)) : ℂ)) θ‖ ≤
          C * (min θ (2 * Real.pi - θ)) ^ (1 - s.val - (j : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := reciprocalRieszSymbol_derivative_bounds hz s
  refine ⟨C, hC, fun j _ θ hθ => ?_⟩
  have hs : ContDiffAt ℝ j
      (fun y : ℝ => reciprocalRieszSymbol s (y : AddCircle (2 * Real.pi))) θ :=
    ((reciprocalRieszSymbol_contDiffOn hz s).contDiffAt
      (isOpen_Ioo.mem_nhds hθ)).of_le (by simp)
  have he := iteratedDeriv_smul_const hs (1 : ℂ)
  simp only [Complex.real_smul, mul_one] at he
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  exact hb j ‹j ≤ 2› ⟨θ, hθ⟩

/-- Decay, absolute summability and uniform reconstruction of the reciprocal
coefficients, by the fractional-cusp theorem. This supplies the analytic
parts of the proof of Lemma 2.5. -/
theorem inverseRieszCoefficient_fourier (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧
      (∀ n : ℤ, ‖inverseRieszCoefficient s n‖ ≤ C / (1 + |(n : ℝ)| ^ (2 - s.val))) ∧
      ∃ hs : Summable (fun n : ℤ => ‖inverseRieszCoefficient s n‖),
        (∀ θ : ℝ, latticeFourier (inverseRieszCoefficient s) hs θ =
          (reciprocalRieszSymbol s (θ : AddCircle (2 * Real.pi)) : ℂ)) ∧
        TendstoUniformly
          (fun a : Finset ℤ => fun θ : ℝ =>
            ∑ n ∈ a, inverseRieszCoefficient s n * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ)))
          (fun θ : ℝ => (reciprocalRieszSymbol s (θ : AddCircle (2 * Real.pi)) : ℂ)) atTop ∧
        TendstoUniformly
          (fun a : Finset ℤ => fun θ : ℝ =>
            ∑ n ∈ a, ‖inverseRieszCoefficient s n * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))‖)
          (fun _ : ℝ => ∑' n : ℤ, ‖inverseRieszCoefficient s n‖) atTop := by
  let H : C(AddCircle (2 * Real.pi), ℂ) :=
    ⟨fun x => (reciprocalRieszSymbol s x : ℂ),
      Complex.continuous_ofReal.comp (continuous_reciprocalRieszSymbol hz s)⟩
  obtain ⟨A, hA, hAb⟩ := reciprocalRieszSymbol_complex_derivative_bounds hz s
  obtain ⟨K, hK, hb⟩ := FractionalCuspFourier.fractional_cusp_fourier
    (sub_pos.mpr s.property.2) (by linarith [s.property.1] : 1 - s.val < 1)
  have hH0 : H 0 = 0 := by simp [H, reciprocalRieszSymbol_zero]
  have hHs : ContDiffOn ℝ 2 (fun y : ℝ => H (y : AddCircle (2 * Real.pi)))
      (Ioo 0 (2 * Real.pi)) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      ((reciprocalRieszSymbol_contDiffOn hz s).of_le (by norm_num))
  have hHb : ∀ j : ℕ, j ≤ 2 → ∀ y ∈ Ioo 0 (2 * Real.pi),
      ‖iteratedDeriv j (fun t : ℝ => H (t : AddCircle (2 * Real.pi))) y‖ ≤
        A * (min y (2 * Real.pi - y)) ^ (1 - s.val - (j : ℝ)) := hAb
  obtain ⟨hdec, hs, hre, hu, hua⟩ := hb A hA H hH0 hHs hHb
  refine ⟨K * A, mul_pos hK hA, ?_, hs, hre, hu, hua⟩
  intro n
  simpa only [H, ContinuousMap.coe_mk, inverseRieszCoefficient,
    show 1 + (1 - s.val) = 2 - s.val by ring] using hdec n

/-- The absolutely convergent coefficient sum is the cusp value zero,
part of the proof of Lemma 2.5. -/
theorem tsum_inverseRieszCoefficient (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) : (∑' n : ℤ, inverseRieszCoefficient s n) = 0 := by
  obtain ⟨_, _, _, hs, hre, _, _⟩ := inverseRieszCoefficient_fourier hz s
  have h := hre 0
  simpa only [latticeFourier, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    mul_one, AddCircle.coe_zero, reciprocalRieszSymbol_zero] using h

/-- See the proof of Lemma 2.5 in the paper, with every conclusion: the decay
constant is chosen before the frequency. The coefficients are absolutely
summable, real and even. Their lattice Fourier transform is the reciprocal
everywhere. Their sum is zero. The final clauses retain uniform convergence
and uniform absolute convergence for downstream periodization arguments. -/
theorem inverseRieszCoefficient_properties (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧
      (∀ n : ℤ, ‖inverseRieszCoefficient s n‖ ≤ C / (1 + |(n : ℝ)| ^ (2 - s.val))) ∧
      ∃ hs : Summable (fun n : ℤ => ‖inverseRieszCoefficient s n‖),
        (∀ n : ℤ, (inverseRieszCoefficient s n).im = 0) ∧
        (∀ n : ℤ, inverseRieszCoefficient s (-n) = inverseRieszCoefficient s n) ∧
        (∀ θ : ℝ, latticeFourier (inverseRieszCoefficient s) hs θ =
          (reciprocalRieszSymbol s (θ : AddCircle (2 * Real.pi)) : ℂ)) ∧
        (∑' n : ℤ, inverseRieszCoefficient s n) = 0 ∧
        TendstoUniformly
          (fun a : Finset ℤ => fun θ : ℝ =>
            ∑ n ∈ a, inverseRieszCoefficient s n * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ)))
          (fun θ : ℝ => (reciprocalRieszSymbol s (θ : AddCircle (2 * Real.pi)) : ℂ)) atTop ∧
        TendstoUniformly
          (fun a : Finset ℤ => fun θ : ℝ =>
            ∑ n ∈ a, ‖inverseRieszCoefficient s n * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))‖)
          (fun _ : ℝ => ∑' n : ℤ, ‖inverseRieszCoefficient s n‖) atTop := by
  obtain ⟨C, hC, hb, hs, hre, hu, hua⟩ := inverseRieszCoefficient_fourier hz s
  exact ⟨C, hC, hb, hs, inverseRieszCoefficient_im s, inverseRieszCoefficient_neg s,
    hre, tsum_inverseRieszCoefficient hz s, hu, hua⟩

end Riesz2
