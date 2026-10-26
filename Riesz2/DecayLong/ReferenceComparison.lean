/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.LocalizedFieldPart4
public import Riesz2.DecayLong.ReferenceOperatorKernelPart3
public import Riesz2.ToMathlib.CyclicOperatorCancellation

/-!
# The reference response to the embedded exterior field

See the proof of Proposition 5.15. The reference
response uses the full component cycle and the original scalar form.
-/

@[expose] public section
noncomputable section

open MeasureTheory Finset
open scoped BigOperators Fin.NatCast NNReal

namespace Riesz2.ReferenceComparison

open ReferenceOperatorKernelPart3

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
  (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)

/-- See Subsection 5.5 of the paper: the full reference response to an arbitrary L²
field, as a vector in the actual scalar form domain. -/
def referenceSolution (s : Riesz1.RieszExponent) (β : InverseTemperature)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (f : Fin (N : ℕ) → Lp ℝ 2 ν)
    (i : Fin (N : ℕ)) : Q.1 :=
  ScalarFormHilbert.equiv Q hQ (∑ k, FiniteFormReferenceKernel.solutionKernel Q hQ
    _ (reference_posDef s β N hN) i k (f k))

/-- The zero-field boundary case of Subsection 5.5. -/
theorem referenceSolution_zero (s : Riesz1.RieszExponent) (β : InverseTemperature)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (i : Fin (N : ℕ)) :
    referenceSolution Q hQ s β N hN (fun _ => 0) i = 0 := by
  simp only [referenceSolution, map_zero, sum_const_zero]

/-- The response satisfies the unrestricted weak equation. -/
theorem referenceSolution_solves (s : Riesz1.RieszExponent) (β : InverseTemperature)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (f : Fin (N : ℕ) → Lp ℝ 2 ν) :
    WeightedWeakSolution Q (fun _ => (2 * β.val) • referenceIntervalMatrix s N hN 1)
      ⊤ f (referenceSolution Q hQ s β N hN f) := by
  unfold referenceSolution
  simp_rw [map_sum]
  exact referenceInverse_weightedWeakSolution Q hQ s β N hN f

/-- The value and the half-generator of the response are its two kernel sums. -/
theorem referenceSolution_convolution (s : Riesz1.RieszExponent) (β : InverseTemperature)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (f : Fin (N : ℕ) → Lp ℝ 2 ν) (i : Fin (N : ℕ)) :
    (referenceSolution Q hQ s β N hN f i).val =
      ∑ k, valueKernel Q hQ s β N hN i k (f k) ∧
    ScalarFormHalfGenerator.halfGenerator Q hQ ((ScalarFormHilbert.equiv Q hQ).symm
      (referenceSolution Q hQ s β N hN f i)) =
      ∑ k, halfKernel Q hQ s β N hN i k (f k) := by
  obtain ⟨hv, hh⟩ := referenceInverse_convolution Q hQ s β N hN f i
  constructor
  · exact hv
  · simpa only [referenceSolution, LinearEquiv.symm_apply_apply] using hh

/-- Cyclic convolution convention for both parts of the reference response. -/
theorem referenceSolution_cyclic (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (β : InverseTemperature)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (f : Fin (N : ℕ) → Lp ℝ 2 ν) (i : Fin (N : ℕ)) :
    (referenceSolution Q hQ s β N hN f i).val =
      ∑ h, valueKernel Q hQ s β N hN 0 h (f (i + h)) ∧
    ScalarFormHalfGenerator.halfGenerator Q hQ ((ScalarFormHilbert.equiv Q hQ).symm
      (referenceSolution Q hQ s β N hN f i)) =
      ∑ h, halfKernel Q hQ s β N hN 0 h (f (i + h)) := by
  obtain ⟨hv, hh⟩ := referenceSolution_convolution Q hQ s β N hN f i
  constructor
  · rw [hv, ← Equiv.sum_comp (Equiv.addLeft i) (fun k => valueKernel Q hQ s β N hN i k (f k))]
    exact sum_congr rfl fun h _ => congrArg (fun T => T (f (i + h)))
      (convolution_entries Q hQ hz s β N hN i h).1
  · rw [hh, ← Equiv.sum_comp (Equiv.addLeft i) (fun k => halfKernel Q hQ s β N hN i k (f k))]
    exact sum_congr rfl fun h _ => congrArg (fun T => T (f (i + h)))
      (convolution_entries Q hQ hz s β N hN i h).2

/-- Positive rescaling of the actual finite spectral inverse. -/
theorem spectralInverse_rescale (s : Riesz1.RieszExponent) (β β₀ : InverseTemperature)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (t : ℝ≥0) :
    ReferenceOperatorKernel.spectralInverse s β N hN t = (β₀.val / β.val) •
      ReferenceOperatorKernel.spectralInverse s β₀ N hN
        ⟨(t : ℝ) * (β₀.val / β.val), mul_nonneg t.property (div_pos β₀.property β.property).le⟩ := by
  let r := β.val / β₀.val
  let t₀ : ℝ≥0 := ⟨(t : ℝ) * (β₀.val / β.val), mul_nonneg t.property (div_pos β₀.property β.property).le⟩
  have hr : r ≠ 0 := (div_pos β.property β₀.property).ne'
  let : Invertible r := invertibleOfNonzero hr
  have he : (2 * β.val) • rieszMatrix s N hN + (t : ℝ) • 1 =
      r • ((2 * β₀.val) • rieszMatrix s N hN + (t₀ : ℝ) • 1) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    change (2 * β.val) * rieszMatrix s N hN i j + (t : ℝ) * (1 : Matrix _ _ ℝ) i j =
      (β.val / β₀.val) * ((2 * β₀.val) * rieszMatrix s N hN i j +
        ((t : ℝ) * (β₀.val / β.val)) * (1 : Matrix _ _ ℝ) i j)
    field_simp [β.property.ne', β₀.property.ne']
  unfold ReferenceOperatorKernel.spectralInverse
  rw [he, Matrix.inv_smul _ r (isUnit_iff_ne_zero.mpr
    (ReferenceOperatorKernel.spectralMatrix_posDef s β₀ N hN t₀).det_pos.ne')]
  simp only [invOf_eq_inv, r, inv_div]
  rfl

/-- The scalar kernel estimates hold uniformly for all temperatures above
a fixed positive lower bound. Both the pointwise decay and the exact row
mass are retained. -/
theorem uniform_value_kernel_bounds (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (βlo : ℝ) (hβlo : 0 < βlo) :
    ∃ B : ℝ, 0 < B ∧ ∀ β : InverseTemperature, βlo ≤ β.val →
      ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
        {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
        (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q),
        (∀ h, ‖valueKernel Q hQ s β N hN 0 h‖ ≤
          B * weightRadius N h 0 ^ (-(2 - s.val))) ∧
        ‖∑ h, valueKernel Q hQ s β N hN 0 h‖ ≤ B * (N : ℝ) ^ (-(1 - s.val)) := by
  let β₀ : InverseTemperature := ⟨βlo, hβlo⟩
  obtain ⟨B₁, hB₁, hb₁⟩ := ReferenceOperatorKernel.spectralInverse_decay hz s β₀
  obtain ⟨B₂, hB₂, hb₂⟩ := ReferenceOperatorKernel.spectralInverse_mass_bounds s β₀
  refine ⟨B₁ + B₂, by positivity, ?_⟩
  intro β hβ N hN Ω _ ν Q hQ
  have hr : 0 ≤ β₀.val / β.val := (div_pos hβlo β.property).le
  have hr1 : β₀.val / β.val ≤ 1 := (div_le_one β.property).mpr hβ
  have hpoint (t : ℝ≥0) (h : Fin (N : ℕ)) :
      |ReferenceOperatorKernel.spectralInverse s β N hN t 0 h| ≤
        B₁ * weightRadius N h 0 ^ (-(2 - s.val)) := by
    rw [spectralInverse_rescale s β β₀ N hN t, Matrix.smul_apply, smul_eq_mul,
      abs_mul, abs_of_nonneg hr]
    exact (mul_le_of_le_one_left (abs_nonneg _) hr1).trans (hb₁ N hN _ h)
  have hmass (t : ℝ≥0) : |∑ h, ReferenceOperatorKernel.spectralInverse s β N hN t 0 h| ≤
      B₂ * (N : ℝ) ^ (-(1 - s.val)) := by
    rw [spectralInverse_rescale s β β₀ N hN t]
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_sum, abs_mul, abs_of_nonneg hr]
    exact (mul_le_of_le_one_left (abs_nonneg _) hr1).trans (hb₂ N hN _ 0).1
  constructor
  · intro h
    apply FiniteFormReferenceKernel.valueKernel_norm_le_internal Q hQ _ _ 0 h
      (mul_nonneg (by positivity) (Real.rpow_nonneg (by dsimp [weightRadius]; positivity) _))
    intro u
    rcases eq_or_lt_of_le u.property.1 with hu | hu
    · simp only [FiniteFormReferenceKernel.valueEntry, FiniteFormReferenceKernel.coordinate,
        ContinuousMap.mul_apply, ContinuousMap.coe_mk, ← hu, zero_mul, abs_zero]
      exact mul_nonneg (by positivity) (Real.rpow_nonneg (by dsimp [weightRadius]; positivity) _)
    · rw [valueEntry_eq_spectralInverse s β N hN u hu]
      exact (hpoint _ h).trans (mul_le_mul_of_nonneg_right (show B₁ ≤ B₁ + B₂ by linarith) (by dsimp [weightRadius]; positivity))
  · apply FiniteFormReferenceKernel.valueKernel_mass_le_internal Q hQ _ _ 0 (by positivity)
    intro u
    rcases eq_or_lt_of_le u.property.1 with hu | hu
    · simp only [FiniteFormReferenceKernel.valueEntry, FiniteFormReferenceKernel.coordinate,
        ContinuousMap.mul_apply, ContinuousMap.coe_mk, ← hu, zero_mul, sum_const_zero, abs_zero]
      positivity
    · simp_rw [valueEntry_eq_spectralInverse s β N hN u hu]
      exact (hmass _).trans (mul_le_mul_of_nonneg_right (show B₂ ≤ B₁ + B₂ by linarith) (by positivity))

/-- The scalar half-kernel rescaling gains a square root of the temperature
ratio, which is at most one above a fixed lower temperature bound. -/
theorem spectralInverse_half_rescale_le (s : Riesz1.RieszExponent)
    (β β₀ : InverseTemperature) (hβ : β₀.val ≤ β.val)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (t : ℝ≥0) (i j : Fin (N : ℕ)) :
    Real.sqrt t * |ReferenceOperatorKernel.spectralInverse s β N hN t i j| ≤
      Real.sqrt ((t : ℝ) * (β₀.val / β.val)) *
        |ReferenceOperatorKernel.spectralInverse s β₀ N hN
          ⟨(t : ℝ) * (β₀.val / β.val), mul_nonneg t.property
            (div_pos β₀.property β.property).le⟩ i j| := by
  have hr : 0 ≤ β₀.val / β.val := (div_pos β₀.property β.property).le
  have hr1 : β₀.val / β.val ≤ 1 := (div_le_one β.property).mpr hβ
  have hroot : Real.sqrt (β₀.val / β.val) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hr1
  rw [spectralInverse_rescale s β β₀ N hN t, Matrix.smul_apply, smul_eq_mul,
    abs_mul, abs_of_nonneg hr]
  have he : Real.sqrt t * (β₀.val / β.val) =
      Real.sqrt (β₀.val / β.val) * Real.sqrt ((t : ℝ) * (β₀.val / β.val)) := by
    rw [Real.sqrt_mul (x := (t : ℝ)) t.property (β₀.val / β.val)]
    calc
      _ = Real.sqrt t * (Real.sqrt (β₀.val / β.val)) ^ 2 :=
        congrArg (fun x : ℝ => Real.sqrt t * x) (Real.sq_sqrt hr).symm
      _ = _ := by ring
  rw [← mul_assoc, he, mul_assoc]
  exact mul_le_of_le_one_left (by positivity) hroot

/-- Uniform half-generator kernel decay and row mass on a positive
temperature half-line, hence on every compact positive temperature interval. -/
theorem uniform_half_kernel_bounds (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (βlo : ℝ) (hβlo : 0 < βlo) :
    ∃ B : ℝ, 0 < B ∧ ∀ β : InverseTemperature, βlo ≤ β.val →
      ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
        {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
        (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q),
        (∀ h, ‖halfKernel Q hQ s β N hN 0 h‖ ≤
          B * weightRadius N h 0 ^ (-(1 + (1 - s.val) / 2))) ∧
        ‖∑ h, halfKernel Q hQ s β N hN 0 h‖ ≤ B * (N : ℝ) ^ (-(1 - s.val) / 2) := by
  let β₀ : InverseTemperature := ⟨βlo, hβlo⟩
  obtain ⟨B₁, hB₁, hb₁⟩ := ReferenceOperatorKernel.spectralInverse_half_decay hz s β₀
  obtain ⟨B₂, hB₂, hb₂⟩ := ReferenceOperatorKernel.spectralInverse_mass_bounds s β₀
  refine ⟨B₁ + B₂, by positivity, ?_⟩
  intro β hβ N hN Ω _ ν Q hQ
  have hr : 0 ≤ β₀.val / β.val := (div_pos hβlo β.property).le
  have hr1 : β₀.val / β.val ≤ 1 := (div_le_one β.property).mpr hβ
  have hpoint (t : ℝ≥0) (h : Fin (N : ℕ)) :
      Real.sqrt t * |ReferenceOperatorKernel.spectralInverse s β N hN t 0 h| ≤
        B₁ * weightRadius N h 0 ^ (-(1 + (1 - s.val) / 2)) :=
    (spectralInverse_half_rescale_le s β β₀ hβ N hN t 0 h).trans (hb₁ N hN ⟨(t : ℝ) * (β₀.val / β.val), mul_nonneg t.property hr⟩ h)
  have hmass (t : ℝ≥0) : Real.sqrt t * |∑ h, ReferenceOperatorKernel.spectralInverse s β N hN t 0 h| ≤
      B₂ * (N : ℝ) ^ (-(1 - s.val) / 2) := by
    have hm : 0 < 2 * ∑ k, sampledRieszKernel s N hN k := by
      have hp := reference_mass_pos s β₀ N hN
      change 0 < β₀.val * (2 * ∑ k, sampledRieszKernel s N hN k) at hp
      exact (mul_pos_iff.mp hp).resolve_right (by intro hh; linarith [β₀.property]) |>.2
    have hd₀ : 0 < β₀.val * (2 * ∑ k, sampledRieszKernel s N hN k) + (t : ℝ) :=
      add_pos_of_pos_of_nonneg (mul_pos hβlo hm) t.property
    have hd : 0 < β.val * (2 * ∑ k, sampledRieszKernel s N hN k) + (t : ℝ) :=
      add_pos_of_pos_of_nonneg (mul_pos β.property hm) t.property
    rw [ReferenceOperatorKernel.spectralInverse_row_sum, abs_of_pos (inv_pos.mpr hd)]
    have hb := (hb₂ N hN t 0).2
    rw [ReferenceOperatorKernel.spectralInverse_row_sum, abs_of_pos (inv_pos.mpr hd₀)] at hb
    refine le_trans (mul_le_mul_of_nonneg_left (inv_anti₀ hd₀ ?_) (Real.sqrt_nonneg _)) hb
    nlinarith only [hβ, hm]
  constructor
  · intro h
    apply FiniteFormReferenceKernel.halfKernel_norm_le_internal Q hQ _ _ 0 h
      (mul_nonneg (by positivity) (Real.rpow_nonneg (by dsimp [weightRadius]; positivity) _))
    intro u
    rcases eq_or_lt_of_le u.property.1 with hu | hu
    · simp only [FiniteFormReferenceKernel.halfEntry, ContinuousMap.mul_apply,
        ContinuousMap.coe_mk, ← hu, Real.sqrt_zero, zero_mul, abs_zero]
      exact mul_nonneg (by positivity) (Real.rpow_nonneg (by dsimp [weightRadius]; positivity) _)
    · rw [halfEntry_eq_spectralInverse s β N hN u hu, abs_mul,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      exact (hpoint ⟨(1-u.val)/u.val, div_nonneg (sub_nonneg.mpr u.property.2) hu.le⟩ h).trans (mul_le_mul_of_nonneg_right
        (show B₁ ≤ B₁ + B₂ by linarith) (by dsimp [weightRadius]; positivity))
  · apply FiniteFormReferenceKernel.halfKernel_mass_le_internal Q hQ _ _ 0 (by positivity)
    intro u
    rcases eq_or_lt_of_le u.property.1 with hu | hu
    · simp only [FiniteFormReferenceKernel.halfEntry, ContinuousMap.mul_apply,
        ContinuousMap.coe_mk, ← hu, Real.sqrt_zero, zero_mul, sum_const_zero, abs_zero]
      positivity
    · simp_rw [halfEntry_eq_spectralInverse s β N hN u hu]
      rw [← mul_sum, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact (hmass ⟨(1-u.val)/u.val, div_nonneg (sub_nonneg.mpr u.property.2) hu.le⟩).trans (mul_le_mul_of_nonneg_right
        (show B₂ ≤ B₁ + B₂ by linarith) (by positivity))

/-- The real and natural descriptions of the smaller central ball agree.
The endpoints of the retained interval stay at distance at least `R/16`. -/
theorem central_geometry_internal (N : ℕ+) (r : ℕ) (hr : 16 ≤ r)
    (hN : 2 * (2 * (r / 8) + 1) ≤ (N : ℕ)) (i : Fin (N : ℕ))
    (hi : 16 * Riesz1.cyclicIndexDistance N i
      ⟨r / 8, by have := i.isLt; omega⟩ ≤ r) :
    i.val < 2 * (r / 8) + 1 ∧
      r ≤ 16 * min (i.val + 1) ((2 * (r / 8) + 1) - i.val) := by
  have hil := i.isLt
  simp only [Riesz1.cyclicIndexDistance] at hi
  unfold Nat.dist at hi
  omega

/-- Comparison of a negative period power with the parent separation. -/
theorem period_power_internal (N : ℕ+) (R c : ℝ) (hR : 0 < R)
    (hN : R ≤ 4 * (N : ℝ)) (hc : 0 ≤ c) :
    (N : ℝ) ^ (-c) ≤ 4 ^ c * R ^ (-c) := by
  have hh := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < R / 4)
    (show R / 4 ≤ (N : ℝ) by linarith) (neg_nonpos.mpr hc)
  convert hh using 1
  rw [Real.div_rpow hR.le (by norm_num), div_eq_mul_inv,
    ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), neg_neg]
  ring

/-- The interval profile becomes a uniform bound away from the endpoints. -/
theorem boundary_power_internal (R δ p t : ℝ) (hR : 0 < R)
    (hδ : R / 16 ≤ δ) (ht : 0 ≤ t) :
    R ^ p * δ ^ (-t) ≤ 16 ^ t * R ^ (p - t) := by
  have hh := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < R / 16) hδ (neg_nonpos.mpr ht)
  calc
    _ ≤ R ^ p * (R / 16) ^ (-t) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by
      rw [Real.div_rpow hR.le (by norm_num), div_eq_mul_inv,
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 16), neg_neg]
      calc
        _ = 16 ^ t * (R ^ p * R ^ (-t)) := by ring
        _ = _ := by rw [← Real.rpow_add hR]; rfl

/-- Central values and short translations of the literal zero extension.
This internal bridge proves, rather than assumes, the local Lipschitz
property required by the reference-kernel cancellation estimate. -/
theorem central_field_internal (s : Riesz1.RieszExponent) (n N : ℕ+)
    (hnN : 2 * (n : ℕ) ≤ (N : ℕ)) (r : ℕ) (hr : 16 ≤ r)
    (hn : (n : ℕ) = 2 * (r / 8) + 1) (A : ℝ) (hA : 0 ≤ A)
    (V : Fin (n : ℕ) → Lp ℝ 2 ν)
    (hV : ∀ l, ‖V l‖ ≤ A * (r : ℝ) ^ (-1 + s.val / 2) *
      ((min (l.val + 1) ((n : ℕ) - l.val) : ℕ) : ℝ) ^ (-s.val / 2))
    (hinc : ∀ (l : Fin (n : ℕ)) (hl : 0 < l.val),
      let prev : Fin (n : ℕ) := ⟨l.val - 1, by have := l.isLt; omega⟩
      ‖V l - V prev‖ ≤ A * (r : ℝ) ^ (-1 + s.val / 2) *
        ((min (min (l.val + 1) ((n : ℕ) - l.val))
          (min (prev.val + 1) ((n : ℕ) - prev.val)) : ℕ) : ℝ) ^ (-1 - s.val / 2)) :
    let f := (SchurRestriction.extendSource n N (by omega) (WithLp.toLp 2 V)).ofLp
    let center : Fin (N : ℕ) := ⟨r / 8, by omega⟩
    ∀ i : Fin (N : ℕ), (Riesz1.cyclicIndexDistance N i center : ℝ) ≤ (r : ℝ) / 32 →
      ‖f i‖ ≤ (16 ^ (1 + s.val / 2) * A) * (r : ℝ) ^ (-1 : ℝ) ∧
      ∀ h, (Riesz1.cyclicIndexDistance N h 0 : ℝ) ≤ (r : ℝ) / 32 →
        ‖f (i + h) - f i‖ ≤ (16 ^ (1 + s.val / 2) * A) *
          (Riesz1.cyclicIndexDistance N h 0 : ℝ) * (r : ℝ) ^ (-2 : ℝ) := by
  intro f center i hi
  have hRp : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hgeom (k : Fin (N : ℕ)) (hk : (Riesz1.cyclicIndexDistance N k center : ℝ) ≤ (r : ℝ) / 16) :
      k.val < (n : ℕ) ∧ (r : ℝ) / 16 ≤ ((min (k.val + 1) ((n : ℕ) - k.val) : ℕ) : ℝ) := by
    have hk' : 16 * Riesz1.cyclicIndexDistance N k center ≤ r := by
      have he : (16 : ℝ) * Riesz1.cyclicIndexDistance N k center ≤ r := by linarith
      exact_mod_cast he
    obtain ⟨hk₁, hk₂⟩ := central_geometry_internal N r hr (by omega) k hk'
    refine ⟨by omega, ?_⟩
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 16)] at hk
    have he : (r : ℝ) ≤ 16 * ((min (k.val + 1) ((n : ℕ) - k.val) : ℕ) : ℝ) := by
      rw [hn]
      exact_mod_cast hk₂
    linarith
  have hfi (k : Fin (N : ℕ)) (hk : k.val < (n : ℕ)) : f k = V ⟨k.val, hk⟩ := by
    exact (LocalizedFieldPart4.extendSource_apply_internal n N (by omega) V k).trans (dite_eq_left hk)
  have hival := hgeom i (by linarith)
  let li : Fin (n : ℕ) := ⟨i.val, hival.1⟩
  constructor
  · rw [hfi i hival.1]
    have hpow := boundary_power_internal (r : ℝ) _ (-1 + s.val / 2) (s.val / 2)
      hRp hival.2 (by linarith [s.property.1])
    have hscale : 16 ^ (s.val / 2) ≤ (16 : ℝ) ^ (1 + s.val / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    calc
      _ ≤ A * (r : ℝ) ^ (-1 + s.val / 2) *
          ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val / 2) := hV li
      _ ≤ A * (16 ^ (s.val / 2) * (r : ℝ) ^ (-1 : ℝ)) := by
        rw [show -1 + s.val / 2 - s.val / 2 = (-1 : ℝ) by ring] at hpow
        have hh := mul_le_mul_of_nonneg_left hpow hA
        convert hh using 1
        all_goals ring_nf
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale hA)
          (Real.rpow_nonneg hRp.le (-1))
        convert hh using 1 <;> ring
  · intro h hh
    have hdist : Riesz1.cyclicIndexDistance N (i + h) i = Riesz1.cyclicIndexDistance N h 0 := by
      simpa only [zero_add, add_comm h i] using LocalizedMatrix.distance_add N h 0 i
    have htri := cyclicIndexDistance_triangle (i + h) i center
    rw [hdist] at htri
    have htriR : (Riesz1.cyclicIndexDistance N (i + h) center : ℝ) ≤ (r : ℝ) / 16 := by
      have he : (Riesz1.cyclicIndexDistance N (i + h) center : ℝ) ≤
          (Riesz1.cyclicIndexDistance N h 0 : ℝ) + (Riesz1.cyclicIndexDistance N i center : ℝ) := by
        exact_mod_cast htri
      linarith
    obtain ⟨hkval, hkδ⟩ := hgeom (i+h) htriR
    let lk : Fin (n : ℕ) := ⟨(i+h).val, hkval⟩
    rw [hfi (i+h) hkval, hfi i hival.1]
    have hδends : (r : ℝ) / 16 ≤
        ((min (min (li.val + 1) ((n : ℕ) - li.val))
          (min (lk.val + 1) ((n : ℕ) - lk.val)) : ℕ) : ℝ) := by
      exact_mod_cast le_min hival.2 hkδ
    have hb := CyclicOperatorCancellation.interval_difference_le_internal n V lk li
      ((16 : ℝ) ^ (1 + s.val / 2) * A * (r : ℝ) ^ (-2 : ℝ))
      (fun k hk₁ hk₂ => ?_)
    · have hdd := LocalizedMatrix.active_distance N n hnN lk li
      change Riesz1.cyclicIndexDistance N (i+h) i = Nat.dist lk.val li.val at hdd
      rw [← hdd, hdist] at hb
      convert hb using 1
      ring
    · let l : Fin (n : ℕ) := ⟨k+1, by have := li.isLt; have := lk.isLt; omega⟩
      let prev : Fin (n : ℕ) := ⟨k, by have := li.isLt; have := lk.isLt; omega⟩
      have hd : min (min (li.val + 1) ((n : ℕ) - li.val)) (min (lk.val + 1) ((n : ℕ) - lk.val)) ≤
          min (min (l.val + 1) ((n : ℕ) - l.val)) (min (prev.val + 1) ((n : ℕ) - prev.val)) := by
        dsimp only [l, prev]
        omega
      have hdR : (r : ℝ) / 16 ≤
          ((min (min (l.val + 1) ((n : ℕ) - l.val)) (min (prev.val + 1) ((n : ℕ) - prev.val)) : ℕ) : ℝ) :=
        hδends.trans (by exact_mod_cast hd)
      have hp := boundary_power_internal (r : ℝ) _ (-1 + s.val / 2) (1 + s.val / 2)
        hRp hdR (by linarith [s.property.1])
      have hs := hinc l (by dsimp only [l]; omega)
      change ‖V l - V prev‖ ≤ _ at hs
      calc
        _ ≤ _ := hs
        _ ≤ _ := by
          rw [show -1 + s.val / 2 - (1 + s.val / 2) = (-2 : ℝ) by ring] at hp
          have hh := mul_le_mul_of_nonneg_left hp hA
          simp only [l, prev, Nat.add_sub_cancel] at hh ⊢
          convert hh using 1 <;> ring_nf

/-- The pointwise cancellation estimate with the period mass converted to
the separation scale. All kernel/source assumptions are internal inputs. -/
theorem pointwise_scaled_internal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ+) (K : Fin (N : ℕ) → E →L[ℝ] E) (f : Fin (N : ℕ) → E)
    (i : Fin (N : ℕ)) (A B c R : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hc : 0 < c) (hc1 : c < 1) (hR : 16 ≤ R) (hN : R ≤ 4 * (N : ℝ))
    (hK : ∀ h, ‖K h‖ ≤ B * weightRadius N h 0 ^ (-(1+c)))
    (hM : ‖∑ h, K h‖ ≤ B * (N : ℝ) ^ (-c))
    (hf : (∑ j, ‖f j‖) ≤ A) (hi : ‖f i‖ ≤ A * R ^ (-1 : ℝ))
    (hlocal : ∀ h, (Riesz1.cyclicIndexDistance N h 0 : ℝ) ≤ R / 32 →
      ‖f (i+h) - f i‖ ≤ A * (Riesz1.cyclicIndexDistance N h 0 : ℝ) * R ^ (-2 : ℝ)) :
    ‖∑ h, K h (f (i+h))‖ ≤
      (B * (4 ^ c + 2 / (1-c) + 32 ^ (1+c) + 2 * (1+1/c) * 32 ^ c)) * A * R ^ (-1-c) := by
  have hRp : 0 < R := by linarith
  have hp := period_power_internal N R c hRp hN hc.le
  have hm : (B * (N : ℝ) ^ (-c)) * A * R ^ (-1 : ℝ) ≤
      (B * 4 ^ c) * A * R ^ (-1-c) := by
    calc
      _ ≤ (B * (4 ^ c * R ^ (-c))) * A * R ^ (-1 : ℝ) := by gcongr
      _ = _ := by
        have he : R ^ (-c) * R ^ (-1 : ℝ) = R ^ (-1-c) := by
          rw [← Real.rpow_add hRp]; congr 1; ring
        calc
          _ = (B * 4 ^ c * A) * (R ^ (-c) * R ^ (-1 : ℝ)) := by ring
          _ = _ := by rw [he]
  have hb := CyclicOperatorCancellation.pointwise_le_internal N K f i A B
    (B * (N : ℝ) ^ (-c)) c R hA hB hc hc1 hR hK hM hf hi hlocal
  linarith only [hb, hm]

/-- Analytic assembly for the proof of Proposition 5.15.
The inputs are precisely the proved field profiles and translation modulus.
The final theorem below supplies them from the original equation. -/
theorem field_reference_estimates_internal (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (βlo : ℝ) (hβlo : 0 < βlo) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : InverseTemperature), βlo ≤ β.val →
    ∀ {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω)
      (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
      (n N : ℕ+) (hN : 2 ≤ (N : ℕ)) (hnN : 2 * (n : ℕ) ≤ (N : ℕ))
      (r : ℕ) (_hr : 16 ≤ r) (hn : (n : ℕ) = 2 * (r / 8) + 1)
      (_hNr : (r : ℝ) ≤ 4 * (N : ℝ)),
    ∀ A : ℝ, 0 ≤ A → ∀ V : Fin (n : ℕ) → Lp ℝ 2 ν,
    (∀ l, ‖V l‖ ≤ A * (r : ℝ) ^ (-1 + s.val / 2) *
      ((min (l.val + 1) ((n : ℕ) - l.val) : ℕ) : ℝ) ^ (-s.val / 2)) →
    (∀ (l : Fin (n : ℕ)) (hl : 0 < l.val),
      let prev : Fin (n : ℕ) := ⟨l.val - 1, by have := l.isLt; omega⟩
      ‖V l - V prev‖ ≤ A * (r : ℝ) ^ (-1 + s.val / 2) *
        ((min (min (l.val + 1) ((n : ℕ) - l.val))
          (min (prev.val + 1) ((n : ℕ) - prev.val)) : ℕ) : ℝ) ^ (-1 - s.val / 2)) →
    let f := (SchurRestriction.extendSource n N (by omega) (WithLp.toLp 2 V)).ofLp
    (∑ i, ‖f i‖) ≤ A →
    (∀ h, (∑ i, ‖f (i-h) - f i‖) ≤
      A * min 1 (((Riesz1.cyclicIndexDistance N h 0 : ℝ) / (r : ℝ)) ^ (1 - s.val / 2))) →
    let φ := referenceSolution Q hQ s β N hN f
    (∑ i, ‖(φ i).val‖) ≤ C * A * (r : ℝ) ^ (-(1-s.val)) ∧
    ∀ i : Fin (N : ℕ),
      (Riesz1.cyclicIndexDistance N i ⟨r/8, by omega⟩ : ℝ) ≤ (r : ℝ) / 32 →
      ‖(φ i).val‖ ≤ C * A * (r : ℝ) ^ (-(2-s.val)) ∧
      Real.sqrt (Q.2 (φ i) (φ i)) ≤ C * A * (r : ℝ) ^ (-(3-s.val)/2) := by
  obtain ⟨B₀, hB₀, hb₀⟩ := uniform_value_kernel_bounds hz s βlo hβlo
  obtain ⟨B₁, hB₁, hb₁⟩ := uniform_half_kernel_bounds hz s βlo hβlo
  let a := 1 - s.val
  let b := 1 - s.val / 2
  let c := (1 - s.val) / 2
  let P := (16 : ℝ) ^ (1 + s.val / 2)
  let T := fun t : ℝ => 4 ^ t + 2 / (1-t) + 32 ^ (1+t) + 2 * (1+1/t) * 32 ^ t
  let Cm := B₀ * (4 ^ a + 2 / (b-a) + 2 * (1+1/a))
  let Cv := B₀ * T a * P
  let Cg := B₁ * T c * P
  have ha : 0 < a := by dsimp [a]; linarith [s.property.2]
  have ha1 : a < 1 := by dsimp [a]; linarith [s.property.1]
  have hc : 0 < c := by dsimp [c]; linarith [s.property.2]
  have hc1 : c < 1 := by dsimp [c]; linarith [s.property.1]
  have hab : a < b := by dsimp [a,b]; linarith [s.property.1]
  have hb : b < 1+a := by dsimp [a,b]; linarith [s.property.2]
  have hP : 1 ≤ P := Real.one_le_rpow (by norm_num) (by linarith [s.property.1])
  have hT (t : ℝ) (ht : 0 < t) (ht1 : t < 1) : 0 < T t := by dsimp [T]; positivity
  have hCm : 0 < Cm := by dsimp [Cm]; positivity
  have hCv : 0 < Cv := mul_pos (mul_pos hB₀ (hT a ha ha1)) (lt_of_lt_of_le zero_lt_one hP)
  have hCg : 0 < Cg := mul_pos (mul_pos hB₁ (hT c hc hc1)) (lt_of_lt_of_le zero_lt_one hP)
  refine ⟨Cm + Cv + Cg, by positivity, ?_⟩
  intro β hβ Ω _ ν Q hQ n N hN hnN r hr hn hNr A hA V hV hinc f hf hmod φ
  have hR : (16 : ℝ) ≤ r := by exact_mod_cast hr
  have hRp : (0 : ℝ) < r := by linarith
  obtain ⟨hk₀, hm₀⟩ := hb₀ β hβ N hN ν Q hQ
  obtain ⟨hk₁, hm₁⟩ := hb₁ β hβ N hN ν Q hQ
  have hcyc (i : Fin (N : ℕ)) := referenceSolution_cyclic Q hQ hz s β N hN f i
  have hmodplus (h : Fin (N : ℕ)) : (∑ i, ‖f (i+h)-f i‖) ≤
      A * min 1 (((Riesz1.cyclicIndexDistance N h 0 : ℝ) / (r : ℝ)) ^ b) := by
    have he : (∑ i, ‖f (i+h) - f i‖) = ∑ i, ‖f (i - -h) - f i‖ := by
      apply sum_congr rfl
      intro i _
      rw [sub_neg_eq_add]
    rw [he]
    exact (LocalizedField.sum_norm_neg_shift_internal N f h).trans_le (hmod h)
  have hmass := CyclicOperatorCancellation.mass_le_internal N
    (valueKernel Q hQ s β N hN 0) f A B₀ (B₀ * (N : ℝ) ^ (-a)) a b (r : ℝ)
    hA hB₀.le ha hab hb (by linarith) (by simpa only [a, show 1+(1-s.val)=2-s.val by ring] using hk₀)
    hm₀ hf hmodplus
  have hperiod := period_power_internal N (r : ℝ) a hRp hNr ha.le
  have hmass' : (∑ i, ‖(φ i).val‖) ≤ Cm * A * (r : ℝ) ^ (-a) := by
    simp_rw [show ∀ i, (φ i).val = ∑ h, valueKernel Q hQ s β N hN 0 h (f (i+h))
      from fun i => (hcyc i).1]
    exact hmass.trans (by dsimp only [Cm]; nlinarith only [mul_le_mul_of_nonneg_left hperiod (mul_nonneg hA hB₀.le)])
  have hfP : (∑ i, ‖f i‖) ≤ P*A := hf.trans (by nlinarith only [hP, hA])
  constructor
  · exact hmass'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : Cm ≤ Cm+Cv+Cg) hA) (by positivity))
  · intro i hi
    obtain ⟨hfi, hlocal⟩ := central_field_internal s n N hnN r hr hn A hA V hV hinc i hi
    have hvalue := pointwise_scaled_internal N (valueKernel Q hQ s β N hN 0) f i (P*A) B₀ a
      (r : ℝ) (by positivity) hB₀.le ha ha1 hR hNr
      (by simpa only [a, show 1+(1-s.val)=2-s.val by ring] using hk₀) hm₀ hfP hfi hlocal
    have hgrad := pointwise_scaled_internal N (halfKernel Q hQ s β N hN 0) f i (P*A) B₁ c
      (r : ℝ) (by positivity) hB₁.le hc hc1 hR hNr hk₁ (by simpa only [c, neg_div] using hm₁) hfP hfi hlocal
    rw [← (hcyc i).1] at hvalue
    rw [← (hcyc i).2, ScalarFormHalfGenerator.halfGenerator_norm] at hgrad
    constructor
    · have he : -1-a = -(2-s.val) := by dsimp [a]; ring
      rw [he] at hvalue
      have hv : ‖(φ i).val‖ ≤ Cv*A*(r : ℝ)^(-(2-s.val)) := by
        convert hvalue using 1
        dsimp only [Cv,T]
        ring
      exact hv.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : Cv ≤ Cm+Cv+Cg) hA) (by positivity))
    · have he : -1-c = -(3-s.val)/2 := by dsimp [c]; ring
      rw [he] at hgrad
      have hg : Real.sqrt (Q.2 (φ i) (φ i)) ≤ Cg*A*(r : ℝ)^(-(3-s.val)/2) := by
        convert hgrad using 1
        dsimp only [Cg,T]
        ring
      exact hg.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : Cg ≤ Cm+Cv+Cg) hA) (by positivity))

/-- See the proof of Proposition 5.15 in the paper, all three estimates for
the actual exterior field of Subsection 5.5. The reference solution is the full
unrestricted inverse of Subsection 5.5. The center is relabelled in cyclic order.
Loss exponents precede ε and prefactors, and the latter are uniform on compact
positive temperature intervals. -/
theorem loc_reference_solution (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ)
    (hκstar : 0 < κstar) (hγstar : 0 < γstar) (M₀ : ℕ+) :
    ∃ κ D : ℝ, 0 < κ ∧ 0 < D ∧ ∀ ε : ℝ, 0 < ε →
    ∀ Cstar : ℝ, 1 ≤ Cstar →
    ∀ (βlo : ℝ) (hβlo : 0 < βlo), ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
      (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q), IsConservativeScalarForm Q →
    ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ)),
    2 ≤ (n : ℕ) → (n : ℕ) ≤ (m : ℕ) →
    (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
    let K := ⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ)
    1 ≤ K → 4 * K ≤ (m : ℕ) →
    ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M →
    ∀ (β : ℝ) (hβl : βlo ≤ β) (_hβu : β ≤ βhi),
    ∀ (χ : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _)
      (fun i => if i = i₀ then χ else 0) u →
    ∀ (j : Fin (m : ℕ)) (hR : 16 ≤ Riesz1.cyclicIndexDistance m j i₀),
    (n : ℝ) ^ (D * ε) ≤ (Riesz1.cyclicIndexDistance m j i₀ : ℝ) →
    let n₀ := LocalizedMatrix.windowSize m j i₀
    let m₀ := LocalizedMatrix.windowPeriod s m j i₀
    let hn₀ : (n₀ : ℕ) ≤ (m₀ : ℕ) := by
      have := LocalizedMatrix.two_windowSize_lt_period s m j i₀ hR
      dsimp only [n₀, m₀]
      omega
    let hm₀ : 2 ≤ (m₀ : ℕ) := by
      have := n₀.pos
      have := LocalizedMatrix.two_windowSize_lt_period s m j i₀ hR
      dsimp only [n₀, m₀] at *
      omega
    let pv := (MatrixEnergy.vectorEquiv Q hQ).symm (fun i => u (LocalizedMatrix.windowEmbedding m j i₀ i))
    let J := SchurRestriction.assemble Q hQ n₀ m₀ hn₀
    let H := fun _ : Ω => (2 : ℝ) • referenceIntervalMatrix s m₀ hm₀ K
    ∃ lam : Lp ℝ 2 ν,
      (∀ᵐ x ∂ν, lam x = gapMultiplierField m Q (fun x => β • M x)
        (fun i => if i = i₀ then χ else 0) u x) ∧
    ∃ U : Fin (n₀ : ℕ) → Lp ℝ 2 ν,
      (∀ l, ∀ᵐ x ∂ν, U l x = ∑ i ∈ (LocalizedMatrix.window m j i₀)ᶜ,
        M x (LocalizedMatrix.windowEmbedding m j i₀ l) i * (u i).val x) ∧
    ∃ w : MatrixEnergy.Vector (ι := Fin ((m₀ : ℕ) - (n₀ : ℕ))) Q hQ,
      (∀ v : MatrixEnergy.Vector (ι := Fin ((m₀ : ℕ) - (n₀ : ℕ))) Q hQ,
        β⁻¹ * (∑ i, Q.2 (MatrixEnergy.vectorEquiv Q hQ w i) (MatrixEnergy.vectorEquiv Q hQ v i)) +
          (∫ x, matrixFieldPair H (fun i => (MatrixEnergy.vectorEquiv Q hQ (J (0,w)) i).val)
            (fun i => (MatrixEnergy.vectorEquiv Q hQ (J (0,v)) i).val) x ∂ν) =
          ∫ x, matrixFieldPair H (fun i => (MatrixEnergy.vectorEquiv Q hQ (J (pv,0)) i).val)
            (fun i => (MatrixEnergy.vectorEquiv Q hQ (J (0,v)) i).val) x ∂ν) ∧
    ∃ V : Fin (n₀ : ℕ) → Lp ℝ 2 ν,
      (∀ l, V l = (-β) • U l - β • LocalizedFieldPart3.referenceRow Q hQ s n₀ m₀ hm₀ K
        (LocalizedFieldPart3.exteriorReindex Q hQ n₀ m₀ hn₀ w) (l.castLE hn₀) + lam) ∧
      (let f := (SchurRestriction.extendSource n₀ m₀ hn₀ (WithLp.toLp 2 V)).ofLp
       let φ := referenceSolution Q hQ s ⟨β, hβlo.trans_le hβl⟩ m₀ hm₀ f
       (∑ i, ‖(φ i).val‖) ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ *
         (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (-(1-s.val)) ∧
       ∀ i : Fin (m₀ : ℕ),
         (Riesz1.cyclicIndexDistance m₀ i
           ⟨Riesz1.cyclicIndexDistance m j i₀ / 8, by
             change Riesz1.cyclicIndexDistance m j i₀ / 8 <
               (LocalizedMatrix.windowPeriod s m j i₀ : ℕ)
             have hcard := LocalizedMatrix.window_card m j i₀
             have htwo := LocalizedMatrix.two_windowSize_le_period s m j i₀ hR
             change (LocalizedMatrix.windowSize m j i₀ : ℕ) = 2 * (Riesz1.cyclicIndexDistance m j i₀ / 8) + 1 at hcard
             omega⟩ : ℝ) ≤ (Riesz1.cyclicIndexDistance m j i₀ : ℝ) / 32 →
         ‖(φ i).val‖ ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ *
           (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (-(2-s.val)) ∧
         Real.sqrt (Q.2 (φ i) (φ i)) ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ *
           (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (-(3-s.val)/2)) := by
  obtain ⟨κ, D, hκ, hD, hfield⟩ := LocalizedFieldPart4.loc_field
    hzeta s κstar γstar hκstar hγstar M₀
  refine ⟨κ, D, hκ, hD, ?_⟩
  intro ε hε Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Cf, hCf, hf⟩ := hfield ε hε Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Cr, hCr, he⟩ := field_reference_estimates_internal hzeta s βlo hβlo
  refine ⟨Cr * Cf, mul_pos hCr hCf, ?_⟩
  intro Ω _ ν _ Q hQ hQc n m hm hn hnm hmn K hK hKm M hM β hβl hβu χ i₀ u husol j hR hsep
    n₀ m₀ hn₀ hm₀ pv J H
  obtain ⟨lam, hlam, U, hU, w, hw, V, hV, hentry, hinc, hmod⟩ :=
    hf ν Q hQ hQc n m hm hn hnm hmn hK hKm M hM β hβl hβu χ i₀ u husol j hR hsep
  have htwo : 2 * (n₀ : ℕ) ≤ (m₀ : ℕ) :=
    LocalizedMatrix.two_windowSize_le_period s m j i₀ hR
  have hcard : (n₀ : ℕ) = 2 * (Riesz1.cyclicIndexDistance m j i₀ / 8) + 1 :=
    LocalizedMatrix.window_card m j i₀
  have hperiod : (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ≤ 4 * (m₀ : ℝ) := by
    have hl := (LocalizedMatrix.window_size_bounds m j i₀ hR).2.1
    change (Riesz1.cyclicIndexDistance m j i₀ : ℝ) / 8 ≤ (n₀ : ℝ) at hl
    have ht : 2 * (n₀ : ℝ) ≤ (m₀ : ℝ) := by exact_mod_cast htwo
    linarith
  have hbounds := he ⟨β, hβlo.trans_le hβl⟩ hβl ν Q hQ n₀ m₀ hm₀ htwo
    (Riesz1.cyclicIndexDistance m j i₀) hR hcard hperiod
    (Cf * (n : ℝ) ^ (κ * ε) * ‖χ‖) (by positivity) V hentry hinc hmod.1 hmod.2
  refine ⟨lam, hlam, U, hU, w, hw, V, hV, ?_⟩
  dsimp only at hbounds ⊢
  constructor
  · convert hbounds.1 using 1
    all_goals ring
  · intro i hi
    obtain ⟨hv, hg⟩ := hbounds.2 i hi
    constructor
    · convert hv using 1
      all_goals ring
    · convert hg using 1
      all_goals ring

end Riesz2.ReferenceComparison
