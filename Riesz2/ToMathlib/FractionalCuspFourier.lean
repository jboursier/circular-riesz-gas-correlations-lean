/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Preliminaries.LatticeSymbol
public import Riesz2.ToMathlib.PowerTailBounds
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.RealDeriv
public import Riesz2.ToMathlib.EndpointCuspEnvelope

/-!
# Fourier decay and reconstruction at a fractional cusp

See the proof of Lemma 2.5 in the paper, using the semi-discrete convention of Subsection 2.3
and the endpoint distance of Subsection 2.4. The smooth seam cutoff and repeated
integration by parts follow Lemma 2.4, Step 1, through the
whole range of cusp exponents below the integration order minus one.
Mathlib's Fourier coefficients and continuous reconstruction theorem then give
absolute summability and uniform, everywhere reconstruction through the landed
`Riesz2.latticeFourier`. No new Fourier transform or endpoint-distance definition
is introduced.
-/

public section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz2.FractionalCuspFourier

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- An imaginary exponential has unit norm. -/
theorem norm_oscillation (n : ℤ) (x : ℝ) :
    ‖Complex.exp (-(n : ℂ) * Complex.I * (x : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- The derivative of the negative Fourier character in angular coordinates. -/
theorem hasDerivAt_oscillation (n : ℤ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (-(n : ℂ) * Complex.I * (t : ℂ)))
      ((-(n : ℂ) * Complex.I) *
        Complex.exp (-(n : ℂ) * Complex.I * (x : ℂ))) x := by
  have hd : HasDerivAt (fun t : ℝ => -(n : ℂ) * Complex.I * (t : ℂ))
      (-(n : ℂ) * Complex.I) x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (-(n : ℂ) * Complex.I)
  simpa only [mul_comm (Complex.exp _) (-(n : ℂ) * Complex.I)] using hd.cexp

/-- The existing circle Fourier character has the positive angular sign used
by the semi-discrete transform in Subsection 2.3. -/
theorem fourier_angular (n : ℤ) (x : ℝ) :
    fourier n (x : AddCircle (2 * Real.pi)) =
      Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- The inverse semi-discrete transform integral is Mathlib's existing Fourier
coefficient, with normalized arclength and the negative angular sign (Subsection 2.3). -/
theorem fourierCoeff_angular (h : AddCircle (2 * Real.pi) → ℂ) (n : ℤ) :
    fourierCoeff h n = (1 / (2 * Real.pi)) •
      ∫ x in (0 : ℝ)..(2 * Real.pi), h (x : AddCircle (2 * Real.pi)) *
        Complex.exp (-(n : ℂ) * Complex.I * (x : ℂ)) := by
  rw [fourierCoeff_eq_intervalIntegral h n 0]
  simp only [zero_add, smul_eq_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [fourier_angular, Int.cast_neg]
  have he : Complex.I * -(n : ℂ) * (x : ℂ) = -(n : ℂ) * Complex.I * (x : ℂ) := by ring
  rw [he, mul_comm]

/-- The coefficient estimate of Lemma 2.4, Step 1, proved by
the smooth seam cutoff for every finite `r` and `0 < α < r-1`. In particular,
the whole written range `r ∈ {2,3}`, including `r = 3, α = 1`, is covered.
The constant is chosen before the amplitude and the continuous circle symbol. -/
theorem fourierCoeff_decay_of_endpoint_bounds (r : ℕ) (α : ℝ)
    (hα : 0 < α) (hαr : α < (r : ℝ) - 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 0 < B →
      ∀ m : C(AddCircle (2 * Real.pi), ℂ), m 0 = 0 →
      ContDiffOn ℝ r (fun x : ℝ => m (x : AddCircle (2 * Real.pi)))
        (Ioo 0 (2 * Real.pi)) →
      (∀ j : ℕ, j ≤ r → ∀ x ∈ Ioo 0 (2 * Real.pi),
        ‖iteratedDeriv j (fun y : ℝ => m (y : AddCircle (2 * Real.pi))) x‖ ≤
          B * (min x (2 * Real.pi - x)) ^ (α - j)) →
      ∀ n : ℤ, ‖fourierCoeff m n‖ ≤ C * B / (1 + |(n : ℝ)|) ^ (1 + α) := by
  obtain ⟨D, hD, hb⟩ := EndpointCuspFourier.integral_decay_of_endpoint_bounds r α hα hαr
  let E := D / (2 * Real.pi)
  have hE : 0 < E := by dsimp [E]; positivity
  refine ⟨E * 2 ^ (1 + α) + Real.pi ^ α, by positivity, ?_⟩
  intro B hB m hm0 hms hmb n
  let F := fun x : ℝ => m (x : AddCircle (2 * Real.pi))
  have hF : Continuous F := m.continuous.comp (AddCircle.continuous_mk' _)
  have hFbound : ∀ x ∈ Icc 0 (2 * Real.pi),
      ‖F x‖ ≤ B * (min x (2 * Real.pi - x)) ^ α := by
    intro x hx
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hx with rfl | rfl | hx
    · simp only [F, AddCircle.coe_zero, hm0, norm_zero]
      apply mul_nonneg hB.le
      apply Real.rpow_nonneg
      apply le_min <;> linarith [Real.pi_pos]
    · dsimp only [F]
      rw [AddCircle.coe_period, hm0, norm_zero]
      apply mul_nonneg hB.le
      apply Real.rpow_nonneg
      apply le_min <;> linarith [Real.pi_pos]
    · simpa only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] using hmb 0 (by omega) x hx
  have hnorm : ‖fourierCoeff m n‖ = (1 / (2 * Real.pi)) *
      ‖∫ x in (0 : ℝ)..(2 * Real.pi), F x *
        Complex.exp (-(n : ℂ) * Complex.I * (x : ℂ))‖ := by
    rw [fourierCoeff_angular, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  by_cases hn : n = 0
  · subst n
    have hz : ‖fourierCoeff m 0‖ ≤ Real.pi ^ α * B := by
      have hi := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := 0) (b := 2 * Real.pi) (f := F) (C := B * Real.pi ^ α) (fun x hx => by
          rw [uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)] at hx
          apply (hFbound x ⟨hx.1.le, hx.2⟩).trans
          apply mul_le_mul_of_nonneg_left _ hB.le
          apply Real.rpow_le_rpow (le_min hx.1.le (by linarith [hx.2])) _ hα.le
          have := min_le_left x (2 * Real.pi - x)
          have := min_le_right x (2 * Real.pi - x)
          linarith)
      rw [hnorm]
      simp only [Int.cast_zero, neg_zero, zero_mul, Complex.exp_zero, mul_one]
      simp only [sub_zero, abs_of_pos (by positivity : 0 < 2 * Real.pi)] at hi
      calc
        _ ≤ (1 / (2 * Real.pi)) * (B * Real.pi ^ α * (2 * Real.pi)) :=
          mul_le_mul_of_nonneg_left hi (by positivity)
        _ = Real.pi ^ α * B := by field_simp
    simp only [Int.cast_zero, abs_zero, add_zero, Real.one_rpow, div_one]
    exact hz.trans (by nlinarith [mul_nonneg (mul_nonneg hE.le
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (1 + α))) hB.le])
  · have hq1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
    have hq : 0 < |(n : ℝ)| := zero_lt_one.trans_le hq1
    have hraw : ‖fourierCoeff m n‖ ≤ E * B / |(n : ℝ)| ^ (1 + α) := by
      rw [hnorm]
      convert mul_le_mul_of_nonneg_left
        (hb B hB.le F hF hms hFbound hmb n hn)
        (by positivity : 0 ≤ 1 / (2 * Real.pi)) using 1
      dsimp only [E]
      ring
    have hden : (1 + |(n : ℝ)|) ^ (1 + α) ≤
        2 ^ (1 + α) * |(n : ℝ)| ^ (1 + α) := by
      calc
        _ ≤ (2 * |(n : ℝ)|) ^ (1 + α) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
        _ = _ := Real.mul_rpow (by norm_num) hq.le
    have hpow : (0 : ℝ) < 2 ^ (1 + α) := by positivity
    calc
      _ ≤ E * B / |(n : ℝ)| ^ (1 + α) := hraw
      _ = (E * 2 ^ (1 + α) * B) /
          (2 ^ (1 + α) * |(n : ℝ)| ^ (1 + α)) := by field_simp
      _ ≤ (E * 2 ^ (1 + α) * B) / (1 + |(n : ℝ)|) ^ (1 + α) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      _ ≤ _ := div_le_div_of_nonneg_right (by
          have := mul_nonneg (Real.rpow_nonneg Real.pi_pos.le α) hB.le
          nlinarith) (by positivity)

/-- The two denominator conventions used for Lemma 2.4 and
the older inverse-cusp API are comparable uniformly for nonnegative radii. -/
theorem cusp_denominator_comparison {x p : ℝ} (hx : 0 ≤ x) (hp : 0 ≤ p) :
    1 + x ^ p ≤ 2 * (1 + x) ^ p ∧
      (1 + x) ^ p ≤ 2 ^ p * (1 + x ^ p) := by
  have h1 : 1 ≤ (1 + x) ^ p := Real.one_le_rpow (by linarith) hp
  have h2 : x ^ p ≤ (1 + x) ^ p := Real.rpow_le_rpow hx (by linarith) hp
  refine ⟨by linarith, ?_⟩
  by_cases hsmall : x ≤ 1
  · calc
      _ ≤ (2 : ℝ) ^ p := Real.rpow_le_rpow (by positivity) (by linarith) hp
      _ ≤ _ := le_mul_of_one_le_right (by positivity)
        (by linarith [Real.rpow_nonneg hx p])
  · calc
      _ ≤ (2 * x) ^ p := Real.rpow_le_rpow (by positivity) (by linarith) hp
      _ = 2 ^ p * x ^ p := Real.mul_rpow (by norm_num) hx
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- Coefficient-decay part of the proof of Lemma 2.5. The constant is
chosen before the amplitude and the continuous periodic complex function. The
minimum is exactly the endpoint distance of Subsection 2.4. -/
theorem exists_cusp_coefficient_bound {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : ℝ), 0 < A →
      ∀ h : C(AddCircle (2 * Real.pi), ℂ), h 0 = 0 →
      ContDiffOn ℝ 2 (fun x : ℝ => h (x : AddCircle (2 * Real.pi)))
        (Ioo 0 (2 * Real.pi)) →
      (∀ (j : ℕ), j ≤ 2 → ∀ x ∈ Ioo 0 (2 * Real.pi),
        ‖iteratedDeriv j (fun t : ℝ => h (t : AddCircle (2 * Real.pi))) x‖ ≤
          A * (min x (2 * Real.pi - x)) ^ (η - j)) →
      ∀ n : ℤ, ‖fourierCoeff h n‖ ≤ C * A / (1 + |(n : ℝ)| ^ (1 + η)) := by
  obtain ⟨C, hC, hb⟩ := fourierCoeff_decay_of_endpoint_bounds 2 η hη (by norm_num; exact hη1)
  refine ⟨2 * C, by positivity, fun A hA h hh0 hhs hhb n => ?_⟩
  have h := hb A hA h hh0 hhs hhb n
  have hd := (cusp_denominator_comparison (abs_nonneg (n : ℝ))
    (show 0 ≤ 1 + η by linarith)).1
  calc
    _ ≤ C * A / (1 + |(n : ℝ)|) ^ (1 + η) := h
    _ = (2 * C * A) / (2 * (1 + |(n : ℝ)|) ^ (1 + η)) := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hd

/-- A power bound of exponent greater than one gives absolute summability of
integer-indexed coefficients, including the zero coefficient. -/
theorem summable_norm_of_coefficient_bound {φ : ℤ → ℂ} {B p : ℝ}
    (hp : 1 < p) (hb : ∀ n : ℤ, ‖φ n‖ ≤ B / (1 + |(n : ℝ)| ^ p)) :
    Summable (fun n : ℤ => ‖φ n‖) := by
  have hs : Summable (fun n : ℤ => 1 / (1 + |(n : ℝ)| ^ p)) := by
    apply Summable.of_nat_of_neg
    · simpa only [Int.cast_natCast, Nat.abs_cast] using
        (Riesz2.summable_inv_one_add_rpow_nat hp)
    · simpa only [Int.cast_neg, abs_neg, Int.cast_natCast, Nat.abs_cast] using
        (Riesz2.summable_inv_one_add_rpow_nat hp)
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb
  simpa only [div_eq_mul_inv, one_mul] using hs.mul_left B

/-- Everywhere reconstruction through the semi-discrete transform
(Subsection 2.3), using Mathlib's continuous Fourier-series reconstruction. -/
theorem latticeFourier_fourierCoeff (h : C(AddCircle (2 * Real.pi), ℂ))
    (hs : Summable (fun n : ℤ => ‖fourierCoeff h n‖)) (θ : ℝ) :
    latticeFourier (fourierCoeff h) hs θ = h (θ : AddCircle (2 * Real.pi)) := by
  have ht := has_pointwise_sum_fourier_series_of_summable (f := h) hs.of_norm
    (θ : AddCircle (2 * Real.pi))
  simpa only [latticeFourier, fourier_angular, smul_eq_mul] using ht.tsum_eq

/-- Absolute summability gives uniform convergence on the entire angular line. -/
theorem uniform_latticeFourier_fourierCoeff (h : C(AddCircle (2 * Real.pi), ℂ))
    (hs : Summable (fun n : ℤ => ‖fourierCoeff h n‖)) :
    TendstoUniformly
      (fun s : Finset ℤ => fun θ : ℝ =>
        ∑ n ∈ s, fourierCoeff h n * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ)))
      (fun θ : ℝ => h (θ : AddCircle (2 * Real.pi))) atTop := by
  have hu := tendstoUniformly_tsum hs
    (f := fun n : ℤ => fun θ : ℝ =>
      fourierCoeff h n * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ)))
    (fun n θ => by rw [norm_mul, Complex.norm_exp]; simp)
  have he : (fun θ : ℝ => ∑' n : ℤ,
      fourierCoeff h n * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))) =
      fun θ : ℝ => h (θ : AddCircle (2 * Real.pi)) := by
    funext θ
    exact latticeFourier_fourierCoeff h hs θ
  rwa [he] at hu

/-- Uniform absolute convergence: the series of the norms converges uniformly
on the whole angular line to the coefficient norm sum. -/
theorem uniform_absolute_fourierCoeff (h : C(AddCircle (2 * Real.pi), ℂ))
    (hs : Summable (fun n : ℤ => ‖fourierCoeff h n‖)) :
    TendstoUniformly
      (fun s : Finset ℤ => fun θ : ℝ =>
        ∑ n ∈ s, ‖fourierCoeff h n * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))‖)
      (fun _ : ℝ => ∑' n : ℤ, ‖fourierCoeff h n‖) atTop := by
  have he (n : ℤ) (θ : ℝ) :
      ‖fourierCoeff h n * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))‖ =
        ‖fourierCoeff h n‖ := by
    rw [norm_mul, Complex.norm_exp]
    simp
  simp_rw [he]
  exact tendstoUniformly_tsum hs (fun n _ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)])

/-- See the proof of Lemma 2.5 in the paper, with all conclusions: a constant depending
only on the cusp exponent bounds every coefficient. The coefficients are
absolutely summable. Their existing lattice Fourier transform reconstructs the
function everywhere. Both the complex series and its absolute-value series
converge uniformly on the entire angular line. Continuity and periodicity are
encoded by a continuous map on the angular circle. -/
theorem fractional_cusp_fourier {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : ℝ), 0 < A →
      ∀ h : C(AddCircle (2 * Real.pi), ℂ), h 0 = 0 →
      ContDiffOn ℝ 2 (fun x : ℝ => h (x : AddCircle (2 * Real.pi)))
        (Ioo 0 (2 * Real.pi)) →
      (∀ (j : ℕ), j ≤ 2 → ∀ x ∈ Ioo 0 (2 * Real.pi),
        ‖iteratedDeriv j (fun t : ℝ => h (t : AddCircle (2 * Real.pi))) x‖ ≤
          A * (min x (2 * Real.pi - x)) ^ (η - j)) →
      (∀ n : ℤ, ‖fourierCoeff h n‖ ≤ C * A / (1 + |(n : ℝ)| ^ (1 + η))) ∧
      ∃ hs : Summable (fun n : ℤ => ‖fourierCoeff h n‖),
        (∀ θ : ℝ, latticeFourier (fourierCoeff h) hs θ =
          h (θ : AddCircle (2 * Real.pi))) ∧
        TendstoUniformly
          (fun s : Finset ℤ => fun θ : ℝ =>
            ∑ n ∈ s, fourierCoeff h n * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ)))
          (fun θ : ℝ => h (θ : AddCircle (2 * Real.pi))) atTop ∧
        TendstoUniformly
          (fun s : Finset ℤ => fun θ : ℝ =>
            ∑ n ∈ s, ‖fourierCoeff h n * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))‖)
          (fun _ : ℝ => ∑' n : ℤ, ‖fourierCoeff h n‖) atTop := by
  obtain ⟨C, hC, hb⟩ := exists_cusp_coefficient_bound hη hη1
  refine ⟨C, hC, ?_⟩
  intro A hA h hh0 hhs hhb
  have hc := hb A hA h hh0 hhs hhb
  have hs := summable_norm_of_coefficient_bound (by linarith : 1 < 1 + η) hc
  exact ⟨hc, hs, latticeFourier_fourierCoeff h hs,
    uniform_latticeFourier_fourierCoeff h hs, uniform_absolute_fourierCoeff h hs⟩

/-- See the proof of Lemma 2.5 in the paper for an unbundled continuous periodic function,
with the coefficient integral in the paper's Fourier convention. This is the
real-line interface to `fractional_cusp_fourier`. The periodic quotient is the
existing `Function.Periodic.lift`, and the series uses `Riesz2.latticeFourier`. -/
theorem fractional_cusp_fourier_periodic {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : ℝ), 0 < A → ∀ h : ℝ → ℂ,
      Continuous h → Function.Periodic h (2 * Real.pi) → h 0 = 0 →
      ContDiffOn ℝ 2 h (Ioo 0 (2 * Real.pi)) →
      (∀ (j : ℕ), j ≤ 2 → ∀ x ∈ Ioo 0 (2 * Real.pi),
        ‖iteratedDeriv j h x‖ ≤ A * (min x (2 * Real.pi - x)) ^ (η - j)) →
      let φ : ℤ → ℂ := fun n => (1 / (2 * Real.pi)) •
        ∫ x in (0 : ℝ)..(2 * Real.pi), h x *
          Complex.exp (-(n : ℂ) * Complex.I * (x : ℂ))
      (∀ n : ℤ, ‖φ n‖ ≤ C * A / (1 + |(n : ℝ)| ^ (1 + η))) ∧
      ∃ hs : Summable (fun n : ℤ => ‖φ n‖),
        (∀ θ : ℝ, latticeFourier φ hs θ = h θ) ∧
        TendstoUniformly
          (fun s : Finset ℤ => fun θ : ℝ =>
            ∑ n ∈ s, φ n * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))) h atTop ∧
        TendstoUniformly
          (fun s : Finset ℤ => fun θ : ℝ =>
            ∑ n ∈ s, ‖φ n * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))‖)
          (fun _ : ℝ => ∑' n : ℤ, ‖φ n‖) atTop := by
  obtain ⟨C, hC, hb⟩ := fractional_cusp_fourier hη hη1
  refine ⟨C, hC, ?_⟩
  intro A hA h hhc hhp hh0 hhs hhb
  have hqc : Continuous hhp.lift :=
    (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (2 * Real.pi))).continuous_iff.mpr
      (by
        change Continuous (fun x : ℝ => hhp.lift (x : AddCircle (2 * Real.pi)))
        simpa only [hhp.lift_coe] using hhc)
  let H : C(AddCircle (2 * Real.pi), ℂ) := ⟨hhp.lift, hqc⟩
  have he : (fun x : ℝ => H (x : AddCircle (2 * Real.pi))) = h := by
    funext x
    exact hhp.lift_coe x
  have hH0 : H 0 = 0 := by
    have h0 := congrFun he 0
    simpa only [AddCircle.coe_zero, hh0] using h0
  have hHs : ContDiffOn ℝ 2 (fun x : ℝ => H (x : AddCircle (2 * Real.pi)))
      (Ioo 0 (2 * Real.pi)) := by rwa [he]
  have hHb : ∀ (j : ℕ), j ≤ 2 → ∀ x ∈ Ioo 0 (2 * Real.pi),
      ‖iteratedDeriv j (fun t : ℝ => H (t : AddCircle (2 * Real.pi))) x‖ ≤
        A * (min x (2 * Real.pi - x)) ^ (η - j) := by rwa [he]
  have hc := hb A hA H hH0 hHs hHb
  have hcoeff (n : ℤ) : fourierCoeff H n = (1 / (2 * Real.pi)) •
      ∫ x in (0 : ℝ)..(2 * Real.pi), h x *
        Complex.exp (-(n : ℂ) * Complex.I * (x : ℂ)) := by
    rw [fourierCoeff_angular]
    simp only [show ∀ x : ℝ, H (x : AddCircle (2 * Real.pi)) = h x from congrFun he]
  have hcoefffun := funext hcoeff
  rw [hcoefffun] at hc
  simpa only [H, ContinuousMap.coe_mk, hhp.lift_coe] using hc

end Riesz2.FractionalCuspFourier
