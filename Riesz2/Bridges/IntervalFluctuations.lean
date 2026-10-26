/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Bridges.IndicatorArc
public import Riesz1.CLT.GapsDiscStripsArc
public import Riesz1.Frozen.ArcIndicator
public import Riesz1.Frozen.CentralLimitTheorem
public import Riesz1.Frozen.CentralRep
public import Riesz1.Frozen.CircleSobolevSq
public import Riesz1.Frozen.CircleVariance
public import Riesz1.Frozen.ConvergesInLaw
public import Riesz1.Frozen.Fluctuation
public import Riesz1.Frozen.LineSobolevSq
public import Riesz1.Frozen.LineVariance
public import Riesz1.Frozen.NormalizedStatistic
public import Riesz1.Frozen.ParticleNumber
public import Riesz1.Frozen.QuantitativeVariance
public import Riesz1.Frozen.RieszConstant
public import Riesz1.Frozen.RieszExponent
public import Riesz1.Frozen.TestAtScale
public import Riesz1.Frozen.Variance
public import Riesz1.Frozen.ZeroExtension
public import Riesz1.Gibbs.WellDefined
public import Riesz1.Kernel.AdmissibilityRegularityVariance
public import Riesz1.Kernel.AdmissibleExamplesCompact
public import Riesz1.Kernel.ExplicitFormulasIndicator
public import Riesz1.Kernel.PeriodicZeta
public import Riesz1.Kernel.SeminormScalingFourier
public import Riesz1.ToMathlib.AddCircleNullSingleton
public import Riesz2.Bridges.GapRigidity
public import Riesz2.Frozen.ConvergesInLawAlong
public import Riesz2.Frozen.GibbsMeasure
public import Riesz2.Frozen.InverseTemperature
public import Riesz2.Frozen.LongParameters
public import Riesz2.Frozen.OfLong
public import Mathlib.Tactic

/-!
# Companion interval variance and central limit theorem

The companion interval variance and central limit theorem for
`ξ = 𝟙_{(-1/4,1/4]}` follow from `Riesz1.quantitative_variance`,
`Riesz1.central_limit_theorem`, `Riesz1.explicit_formulas_indicator`
and `Riesz1.periodicZeta_asymptotic`.

The definitions `intervalCircleVariance` and `intervalLineVariance` use the
Fourier sum of the periodized profile `f_ℓ` and the Fourier integral of `ξ`.
They agree with `Riesz1.circleVariance` and `Riesz1.lineVariance`.

The profile `f_ℓ` is one on the half-open arc `(-ℓ/4, ℓ/4]`.
The open-arc profile `Riesz1.arcIndicator` differs only at `ℓ/4`.
The Gibbs law almost surely has no particle there, so the centered statistics
agree almost surely.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal FourierTransform

namespace Riesz2

/-- The fixed real-line profile `ξ = 𝟙_{(-1/4,1/4]}`, Subsection 2.2. -/
def intervalIndicator (t : ℝ) : ℝ :=
  (Set.Ioc (-(1 / 4 : ℝ)) (1 / 4)).indicator (fun _ => (1 : ℝ)) t

/-- The periodization `ξ_ℓ(t) = ∑_{m ∈ ℤ} ξ(t + m/ℓ)` of `intervalIndicator`, Subsection 2.2. -/
def periodizedInterval (ℓ : Riesz1.Scale) (t : ℝ) : ℝ :=
  ∑' m : ℤ, intervalIndicator (t + m / ℓ.val)

/-- The profile `f_ℓ(x) = ξ_ℓ(x/ℓ)` on the circle, Subsection 2.2. The real lift of `x` is
its central representative. -/
def intervalProfile (ℓ : Riesz1.Scale) (x : UnitAddCircle) : ℝ :=
  periodizedInterval ℓ (Riesz1.centralRep Riesz1.unitLength x / ℓ.val)

/-- The centred finite statistic `F_{N,ℓ} = ∑_{i} f_ℓ(x_i) - Nℓ/2` on configurations, Subsection 2.2. -/
def intervalFluctuation (ℓ : Riesz1.Scale) (N : ℕ+) (X : Riesz1.Configuration N) : ℝ :=
  ∑ i : Fin (N : ℕ), intervalProfile ℓ ((X.val i : ℝ) : UnitAddCircle) - (N : ℝ) * ℓ.val / 2

/-- The circle variance `σ_ℓ²(ξ) = (2βc_s)⁻¹ ℓ^{-s} ∑_{k ≠ 0} (2π|k|)^{1-s} |f̂_ℓ(k)|²`, an
extended quantity, Subsection 2.2. -/
def intervalCircleVariance (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (ℓ : Riesz1.Scale) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (2 * β.val * Riesz1.rieszConstant s)) * ENNReal.ofReal (ℓ.val ^ (-s.val)) *
    ∑' k : ℤ, if k = 0 then 0 else ENNReal.ofReal ((2 * Real.pi * |(k : ℝ)|) ^ (1 - s.val) *
      ‖fourierCoeff (fun x : UnitAddCircle => (intervalProfile ℓ x : ℂ)) k‖ ^ 2)

/-- The complex-valued indicator `ξ`, as a bounded measurable function on the line. -/
lemma intervalIndicator_complex_eq :
    (fun t : ℝ => (intervalIndicator t : ℂ)) =
      (Set.Ioc (-(1 / 4 : ℝ)) (1 / 4)).indicator (fun _ => (1 : ℂ)) := by
  funext t
  unfold intervalIndicator
  by_cases ht : t ∈ Set.Ioc (-(1 / 4 : ℝ)) (1 / 4)
  · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]; simp
  · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]; simp

/-- The indicator `ξ` is square integrable on the line. -/
lemma memLp_intervalIndicator :
    MemLp (fun t : ℝ => (intervalIndicator t : ℂ)) 2 volume := by
  rw [intervalIndicator_complex_eq]
  exact memLp_indicator_const 2 measurableSet_Ioc.nullMeasurableSet _ (Or.inr (by simp))

/-- The indicator `ξ` is integrable on the line. -/
lemma integrable_intervalIndicator :
    Integrable (fun t : ℝ => (intervalIndicator t : ℂ)) := by
  rw [intervalIndicator_complex_eq, integrable_indicator_iff measurableSet_Ioc]
  exact integrableOn_const (by simp)

/-- The profile `ξ` as an element of `L²(ℝ)`. -/
def intervalL2 : Lp ℂ 2 (volume : Measure ℝ) :=
  memLp_intervalIndicator.toLp _

/-- The Riesz 1 profile `𝟙_{(-1/4,1/4)}` on the circle, the arc about the origin of half-width
`1/4`. -/
def arcProfile : Riesz1.Profile :=
  ⟨Riesz1.arcIndicator ((0 : ℝ) : UnitAddCircle) (1 / 4), Riesz1.memLp_arcIndicator _ _⟩

lemma arcIndicator_zero_apply (a : ℝ) (x : UnitAddCircle) :
    Riesz1.arcIndicator ((0 : ℝ) : UnitAddCircle) a x =
      if |Riesz1.centralRep Riesz1.unitLength x| < a then 1 else 0 := by
  unfold Riesz1.arcIndicator
  have h0 : ((0 : ℝ) : UnitAddCircle) = 0 := rfl
  rw [h0, Riesz1.dist_zero_eq_abs_centralRep]

lemma centralRep_mem_Ico_unit (x : UnitAddCircle) :
    Riesz1.centralRep Riesz1.unitLength x ∈ Set.Ico (-(1 / 2 : ℝ)) (1 / 2) := by
  have h := Riesz1.centralRep_mem_Ico Riesz1.unitLength x
  simpa [Riesz1.unitLength] using h

lemma abs_div_lt_iff_scale (ℓ : Riesz1.Scale) (c : ℝ) :
    |c / ℓ.val| < 1 / 4 ↔ |c| < ℓ.val / 4 := by
  have hℓ : 0 < ℓ.val := ℓ.property.1
  rw [abs_div, abs_of_pos hℓ, div_lt_iff₀ hℓ]
  constructor <;> intro h <;> linarith

/-- The periodization at a point of `[-1/2, 1/2)` reduces to its term at `m = 0`, since every other
translate lies outside `(-1/4, 1/4]`. -/
lemma periodizedInterval_eq_self (ℓ : Riesz1.Scale) {c : ℝ}
    (hc : c ∈ Set.Ico (-(1 / 2 : ℝ)) (1 / 2)) :
    periodizedInterval ℓ (c / ℓ.val) = intervalIndicator (c / ℓ.val) := by
  have hℓ : 0 < ℓ.val := ℓ.property.1
  have hℓ1 : ℓ.val ≤ 1 := ℓ.property.2
  unfold periodizedInterval
  rw [tsum_eq_single 0]
  · simp
  · intro m hm
    have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have hcm : 1 / 2 ≤ |c + m| := by
      rcases lt_or_gt_of_ne hm with h | h
      · have h' : (m : ℝ) ≤ -1 := by exact_mod_cast (show m ≤ -1 by omega)
        rw [show c + m = -(-c - m) by ring]
        rw [abs_neg]
        rw [abs_of_nonneg (by linarith [hc.2, hc.1])]
        linarith [hc.2]
      · have h' : (1 : ℝ) ≤ m := by exact_mod_cast (show (1 : ℤ) ≤ m by omega)
        rw [abs_of_nonneg (by linarith [hc.1])]
        linarith [hc.1]
    have hsum : c / ℓ.val + m / ℓ.val = (c + m) / ℓ.val := by ring
    rw [hsum, intervalIndicator, Set.indicator_of_notMem]
    intro hmem
    have hlt : |(c + m) / ℓ.val| ≤ 1 / 4 := by
      rw [abs_le]
      exact ⟨by linarith [hmem.1], hmem.2⟩
    have hge : 1 / 2 ≤ |(c + m) / ℓ.val| := by
      rw [abs_div, abs_of_pos hℓ, le_div_iff₀ hℓ]
      nlinarith
    linarith

/-- The periodized profile is the indicator of `(-ℓ/4, ℓ/4]` at the central representative. -/
lemma intervalProfile_eq_indicator (ℓ : Riesz1.Scale) (x : UnitAddCircle) :
    intervalProfile ℓ x =
      (Set.Ioc (-(ℓ.val / 4)) (ℓ.val / 4)).indicator (fun _ => (1 : ℝ))
        (Riesz1.centralRep Riesz1.unitLength x) := by
  have hℓ : 0 < ℓ.val := ℓ.property.1
  unfold intervalProfile
  rw [periodizedInterval_eq_self ℓ (centralRep_mem_Ico_unit x)]
  unfold intervalIndicator
  have hiff : Riesz1.centralRep Riesz1.unitLength x / ℓ.val ∈ Set.Ioc (-(1 / 4 : ℝ)) (1 / 4) ↔
      Riesz1.centralRep Riesz1.unitLength x ∈ Set.Ioc (-(ℓ.val / 4)) (ℓ.val / 4) := by
    rw [Set.mem_Ioc, Set.mem_Ioc, lt_div_iff₀ hℓ, div_le_iff₀ hℓ]
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; constructor <;> linarith
  simp only [Set.indicator_apply, hiff]

/-- The Riesz 1 rescaled arc profile is the open arc indicator of half-width `ℓ/4`. -/
lemma testAtScale_arcProfile (ℓ : Riesz1.Scale) (x : UnitAddCircle) :
    Riesz1.testAtScale arcProfile ℓ x = Riesz1.arcIndicator 0 (ℓ.val / 4) x := by
  have h0 : ((0 : ℝ) : UnitAddCircle) = 0 := rfl
  rw [← h0, arcIndicator_zero_apply]
  unfold Riesz1.testAtScale
  by_cases h1 : ℓ.val = 1
  · simp only [h1, ↓reduceIte]
    change Riesz1.arcIndicator ((0 : ℝ) : UnitAddCircle) (1 / 4) x = _
    rw [arcIndicator_zero_apply]
  · simp only [h1, ↓reduceIte]
    unfold Riesz1.rescaledProfile
    have hz : Riesz1.zeroExtension arcProfile (Riesz1.centralRep Riesz1.unitLength x / ℓ.val) =
        (Set.Ioo ((0 : ℝ) - 1 / 4) (0 + 1 / 4)).indicator (fun _ => (1 : ℝ))
          (Riesz1.centralRep Riesz1.unitLength x / ℓ.val) :=
      Riesz1.zeroExtension_arcIndicator (c := 0) (a := 1 / 4) (by norm_num) (by norm_num) _
    rw [hz]
    set c := Riesz1.centralRep Riesz1.unitLength x with hc
    by_cases h : |c / ℓ.val| < 1 / 4
    · have hm : c / ℓ.val ∈ Set.Ioo ((0 : ℝ) - 1 / 4) (0 + 1 / 4) := by
        rw [Set.mem_Ioo]
        constructor <;> linarith [(abs_lt.1 h).1, (abs_lt.1 h).2]
      have hc' : |c| < ℓ.val / 4 := (abs_div_lt_iff_scale ℓ c).1 h
      rw [Set.indicator_of_mem hm]
      simp only [hc', ↓reduceIte]
    · have hm : c / ℓ.val ∉ Set.Ioo ((0 : ℝ) - 1 / 4) (0 + 1 / 4) := by
        rw [Set.mem_Ioo]
        intro hc'
        apply h
        rw [abs_lt]
        constructor <;> linarith [hc'.1, hc'.2]
      have hc' : ¬ |c| < ℓ.val / 4 := fun h' => h ((abs_div_lt_iff_scale ℓ c).2 h')
      rw [Set.indicator_of_notMem hm]
      simp only [hc', ↓reduceIte]

/-- The periodized profile agrees with the Riesz 1 arc indicator off the endpoint `ℓ/4`. -/
lemma intervalProfile_eq_arcIndicator_of_ne (ℓ : Riesz1.Scale) (x : UnitAddCircle)
    (hne : Riesz1.centralRep Riesz1.unitLength x ≠ ℓ.val / 4) :
    intervalProfile ℓ x = Riesz1.arcIndicator 0 (ℓ.val / 4) x := by
  have h0 : ((0 : ℝ) : UnitAddCircle) = 0 := rfl
  rw [intervalProfile_eq_indicator, ← h0, arcIndicator_zero_apply]
  set c := Riesz1.centralRep Riesz1.unitLength x with hc
  by_cases h : |c| < ℓ.val / 4
  · have hm : c ∈ Set.Ioc (-(ℓ.val / 4)) (ℓ.val / 4) :=
      ⟨by linarith [(abs_lt.1 h).1], by linarith [(abs_lt.1 h).2]⟩
    rw [Set.indicator_of_mem hm]
    simp only [h, ↓reduceIte]
  · have hm : c ∉ Set.Ioc (-(ℓ.val / 4)) (ℓ.val / 4) := by
      intro hm'
      apply h
      rw [abs_lt]
      exact ⟨by linarith [hm'.1], lt_of_le_of_ne hm'.2 hne⟩
    rw [Set.indicator_of_notMem hm]
    simp only [h, ↓reduceIte]

/-- The periodized profile agrees with the Riesz 1 arc indicator almost everywhere on the circle,
since the endpoint `ℓ/4` is a null set. -/
lemma intervalProfile_ae_arcIndicator (ℓ : Riesz1.Scale) :
    ∀ᵐ x ∂(volume : Measure UnitAddCircle),
      intervalProfile ℓ x = Riesz1.arcIndicator 0 (ℓ.val / 4) x := by
  have hsub : {x : UnitAddCircle | Riesz1.centralRep Riesz1.unitLength x = ℓ.val / 4} ⊆
      {((ℓ.val / 4 : ℝ) : UnitAddCircle)} := by
    intro x hx
    obtain ⟨x0, rfl⟩ := Riesz1.exists_real_coe x
    obtain ⟨n, hn⟩ := Riesz1.centralRep_coe_eq Riesz1.unitLength x0
    simp only [Set.mem_ofPred_eq, Riesz1.unitLength, mul_one] at hx hn
    rw [Set.mem_singleton_iff]
    have hx0 : x0 = ℓ.val / 4 + n := by linarith
    rw [hx0]
    simp
  have hnull : volume {x : UnitAddCircle | Riesz1.centralRep Riesz1.unitLength x = ℓ.val / 4} = 0 :=
    measure_mono_null hsub (Riesz1.addCircle_volume_singleton 1 _)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with x hx
  exact intervalProfile_eq_arcIndicator_of_ne ℓ x hx

/-- The integral of the periodized profile is `ℓ/2`, the mass of the arc of half-width `ℓ/4`. -/
lemma integral_intervalProfile (ℓ : Riesz1.Scale) :
    ∫ x : UnitAddCircle, intervalProfile ℓ x = ℓ.val / 2 := by
  have hℓ : 0 < ℓ.val := ℓ.property.1
  have hℓ1 : ℓ.val ≤ 1 := ℓ.property.2
  rw [integral_congr_ae (intervalProfile_ae_arcIndicator ℓ),
    Riesz1.integral_arcIndicator 0 (by positivity) (by linarith)]
  ring

/-- The line variance `V(ξ) = (2βc_s)⁻¹ ∫_ℝ (2π|u|)^{1-s} |ξ̂(u)|² du`, an extended quantity,
Subsection 2.2. The Fourier transform `𝓕` is the integral `∫ ξ(x) e^{-2πixu} dx`. -/
def intervalLineVariance (β : InverseTemperature) (s : Riesz1.RieszExponent) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (2 * β.val * Riesz1.rieszConstant s)) *
    ∫⁻ u : ℝ, ENNReal.ofReal ((2 * Real.pi * |u|) ^ (1 - s.val) *
      ‖𝓕 (fun t : ℝ => (intervalIndicator t : ℂ)) u‖ ^ 2)

/-- The periodized profile's Fourier sum is the Riesz 1 circle Sobolev seminorm of the rescaled
arc profile, since the two profiles agree almost everywhere. -/
lemma fourierCoeff_testAtScale_arcProfile (ℓ : Riesz1.Scale) (k : ℤ) :
    fourierCoeff (fun x : UnitAddCircle => (Riesz1.testAtScale arcProfile ℓ x : ℂ)) k =
      fourierCoeff (fun x : UnitAddCircle => (intervalProfile ℓ x : ℂ)) k := by
  apply Riesz1.fourierCoeff_congr_ae
  filter_upwards [intervalProfile_ae_arcIndicator ℓ] with x hx
  simp only [testAtScale_arcProfile, hx]

/-- The circle variance `σ_ℓ²(ξ)` is the Riesz 1 circle variance of the arc profile at scale `ℓ`.
This identifies the Fourier-sum form of Subsection 2.2 with `Riesz1.circleVariance`. -/
theorem intervalCircleVariance_eq (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (ℓ : Riesz1.Scale) :
    intervalCircleVariance β s ℓ = Riesz1.circleVariance (longParameters β s) arcProfile ℓ := by
  have hden : 0 < 2 * β.val * Riesz1.rieszConstant s :=
    mul_pos (mul_pos two_pos β.property) (Riesz1.rieszConstant_pos s)
  have hden' : 0 ≤ 1 / (2 * β.val * Riesz1.rieszConstant s) := div_nonneg zero_le_one hden.le
  have hsum : ∑' k : ℤ, (if k = 0 then 0 else ENNReal.ofReal ((2 * Real.pi * |(k : ℝ)|) ^ (1 - s.val) *
      ‖fourierCoeff (fun x : UnitAddCircle => (intervalProfile ℓ x : ℂ)) k‖ ^ 2)) =
      ENNReal.ofReal ((2 * Real.pi) ^ (1 - s.val)) * ∑' k : ℤ, (if k = 0 then 0 else
        ENNReal.ofReal (|(k : ℝ)| ^ (1 - s.val) *
          ‖fourierCoeff (fun x : UnitAddCircle => (intervalProfile ℓ x : ℂ)) k‖ ^ 2)) := by
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun k => ?_
    split_ifs
    · simp
    · rw [← ENNReal.ofReal_mul (by positivity), Real.mul_rpow (by positivity) (abs_nonneg _)]
      congr 1
      ring
  have hcs : Riesz1.circleSobolevSq ((1 - s.val) / 2)
      ⟨fun x => (Riesz1.testAtScale arcProfile ℓ x : ℂ), Riesz1.testAtScaleL2 arcProfile ℓ⟩ =
      ∑' k : ℤ, (if k = 0 then 0 else ENNReal.ofReal (|(k : ℝ)| ^ (1 - s.val) *
        ‖fourierCoeff (fun x : UnitAddCircle => (intervalProfile ℓ x : ℂ)) k‖ ^ 2)) := by
    unfold Riesz1.circleSobolevSq
    refine tsum_congr fun k => ?_
    rw [fourierCoeff_testAtScale_arcProfile, show 2 * ((1 - s.val) / 2) = 1 - s.val by ring]
  have hD : ENNReal.ofReal ((2 * Real.pi) ^ (1 - s.val) / (2 * β.val * Riesz1.rieszConstant s) *
      ℓ.val ^ (-s.val)) = ENNReal.ofReal (1 / (2 * β.val * Riesz1.rieszConstant s)) *
      ENNReal.ofReal (ℓ.val ^ (-s.val)) * ENNReal.ofReal ((2 * Real.pi) ^ (1 - s.val)) := by
    rw [← ENNReal.ofReal_mul hden', ← ENNReal.ofReal_mul (mul_nonneg hden'
      (Real.rpow_nonneg ℓ.property.1.le _))]
    congr 1
    ring
  unfold intervalCircleVariance Riesz1.circleVariance
  rw [show Riesz1.parametersExponent (longParameters β s) = s from rfl]
  dsimp only [longParameters]
  rw [hD, hcs, hsum]
  ring

/-- The line variance `V(ξ)` is the Riesz 1 line variance of `ξ`. The `L²` Fourier transform
agrees almost everywhere with the pointwise Fourier integral, by `Riesz1.fourier_toLp_ae`. -/
theorem intervalLineVariance_eq (β : InverseTemperature) (s : Riesz1.RieszExponent) :
    intervalLineVariance β s = Riesz1.lineVariance (longParameters β s) intervalL2 := by
  have hden : 0 < 2 * β.val * Riesz1.rieszConstant s :=
    mul_pos (mul_pos two_pos β.property) (Riesz1.rieszConstant_pos s)
  have hden' : 0 ≤ 1 / (2 * β.val * Riesz1.rieszConstant s) := div_nonneg zero_le_one hden.le
  have hae := Riesz1.fourier_toLp_ae integrable_intervalIndicator memLp_intervalIndicator
  have hpt : ∀ u : ℝ, ENNReal.ofReal ((2 * Real.pi * |u|) ^ (1 - s.val) *
      ‖𝓕 (fun t : ℝ => (intervalIndicator t : ℂ)) u‖ ^ 2) =
      ENNReal.ofReal ((2 * Real.pi) ^ (1 - s.val)) *
        ENNReal.ofReal (|u| ^ (1 - s.val) * ‖𝓕 (fun t : ℝ => (intervalIndicator t : ℂ)) u‖ ^ 2) := by
    intro u
    rw [← ENNReal.ofReal_mul (by positivity), Real.mul_rpow (by positivity) (abs_nonneg _)]
    congr 1
    ring
  have hLHS : ∫⁻ u : ℝ, ENNReal.ofReal ((2 * Real.pi * |u|) ^ (1 - s.val) *
      ‖𝓕 (fun t : ℝ => (intervalIndicator t : ℂ)) u‖ ^ 2) =
      ENNReal.ofReal ((2 * Real.pi) ^ (1 - s.val)) *
        ∫⁻ u : ℝ, ENNReal.ofReal (|u| ^ (1 - s.val) *
          ‖𝓕 (fun t : ℝ => (intervalIndicator t : ℂ)) u‖ ^ 2) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_congr hpt
  have hint : ∫⁻ η : ℝ, ENNReal.ofReal (|η| ^ (2 * ((1 - s.val) / 2)) *
      ‖Lp.fourierTransformₗᵢ ℝ ℂ intervalL2 η‖ ^ 2) =
      ∫⁻ u : ℝ, ENNReal.ofReal (|u| ^ (1 - s.val) *
        ‖𝓕 (fun t : ℝ => (intervalIndicator t : ℂ)) u‖ ^ 2) := by
    apply lintegral_congr_ae
    filter_upwards [hae] with η hη
    rw [show 2 * ((1 - s.val) / 2) = 1 - s.val by ring]
    have hη' : ((Lp.fourierTransformₗᵢ ℝ ℂ intervalL2 : Lp ℂ 2 volume) : ℝ → ℂ) η =
        𝓕 (fun t : ℝ => (intervalIndicator t : ℂ)) η := hη
    rw [hη']
  have hc : ENNReal.ofReal ((2 * Real.pi) ^ (1 - s.val) /
      (2 * β.val * Riesz1.rieszConstant s)) =
      ENNReal.ofReal (1 / (2 * β.val * Riesz1.rieszConstant s)) *
        ENNReal.ofReal ((2 * Real.pi) ^ (1 - s.val)) := by
    rw [← ENNReal.ofReal_mul hden']
    congr 1
    ring
  unfold intervalLineVariance Riesz1.lineVariance Riesz1.lineSobolevSq
  rw [show Riesz1.parametersExponent (longParameters β s) = s from rfl]
  dsimp only [longParameters]
  rw [hLHS, hint, hc]
  ring

/-- The Riesz 1 zero extension of the arc profile is the open-interval indicator, and it agrees
with `ξ` almost everywhere (they differ only at the endpoint `1/4`). -/
lemma zeroExtension_arcProfile_ae :
    ∀ᵐ x : ℝ, (Riesz1.zeroExtension arcProfile x : ℂ) = (intervalIndicator x : ℂ) := by
  have hsing : volume ({(1 / 4 : ℝ)} : Set ℝ) = 0 := Real.volume_singleton
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hsing] with x hx
  have hne : x ≠ 1 / 4 := hx
  have hz : Riesz1.zeroExtension arcProfile x =
      (Set.Ioo ((0 : ℝ) - 1 / 4) (0 + 1 / 4)).indicator (fun _ => (1 : ℝ)) x :=
    Riesz1.zeroExtension_arcIndicator (c := 0) (a := 1 / 4) (by norm_num) (by norm_num) x
  rw [hz]
  unfold intervalIndicator
  by_cases h : x ∈ Set.Ioc (-(1 / 4 : ℝ)) (1 / 4)
  · have hlt : x < 1 / 4 := lt_of_le_of_ne (Set.mem_Ioc.1 h).2 hne
    have hx' : x ∈ Set.Ioo ((0 : ℝ) - 1 / 4) (0 + 1 / 4) := by
      rw [Set.mem_Ioo]
      exact ⟨by linarith [(Set.mem_Ioc.1 h).1], by linarith⟩
    rw [Set.indicator_of_mem hx', Set.indicator_of_mem h]
  · have hx' : x ∉ Set.Ioo ((0 : ℝ) - 1 / 4) (0 + 1 / 4) := by
      intro hm
      apply h
      rw [Set.mem_Ioc]
      exact ⟨by linarith [hm.1], by linarith [hm.2]⟩
    rw [Set.indicator_of_notMem hx', Set.indicator_of_notMem h]

/-- The explicit Riesz 1 formula for the circle variance of the arc profile at scale `ℓ`, whose real value is `ℓ^{-s} κ_s ζ_s(ℓ/2)`, where
`κ_s = cot(πs/2)/(2πβs)` and `ζ_s` is `Riesz1.periodicZeta`. -/
theorem circleVariance_arcProfile_toReal (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (ℓ : Riesz1.Scale) :
    (Riesz1.circleVariance (longParameters β s) arcProfile ℓ).toReal =
      ℓ.val ^ (-s.val) * (Real.cos (Real.pi * s.val / 2) / Real.sin (Real.pi * s.val / 2) /
        (2 * Real.pi * β.val * s.val)) * Riesz1.periodicZeta s ((ℓ.val / 2 : ℝ) : UnitAddCircle) := by
  have hℓ : 0 < ℓ.val := ℓ.property.1
  have hℓ4 : ℓ.val / 4 < 1 / 2 := by linarith [ℓ.property.2]
  obtain ⟨-, -, ⟨hfin, hform⟩, -, hcs4⟩ :=
    Riesz1.explicit_formulas_indicator s β.val β.property (ℓ.val / 4) (by positivity) hℓ4
  have hfun : (fun x : UnitAddCircle => (Riesz1.testAtScale arcProfile ℓ x : ℂ)) =
      (fun t : UnitAddCircle => (Riesz1.indicatorArc (ℓ.val / 4) t : ℂ)) := by
    funext x
    rw [testAtScale_arcProfile, Riesz1.indicatorArc_eq_arcIndicator (by linarith)]
  have hsub : (⟨fun x : UnitAddCircle => (Riesz1.testAtScale arcProfile ℓ x : ℂ),
      Riesz1.testAtScaleL2 arcProfile ℓ⟩ : {f : UnitAddCircle → ℂ // MemLp f 2 volume}) =
      ⟨fun t : UnitAddCircle => (Riesz1.indicatorArc (ℓ.val / 4) t : ℂ),
        Riesz1.memLp_indicatorArc (ℓ.val / 4)⟩ :=
    Subtype.ext hfun
  have hA : 0 ≤ (2 * Real.pi) ^ (1 - s.val) / (2 * β.val * Riesz1.rieszConstant s) *
      ℓ.val ^ (-s.val) := by
    have hc : 0 < 2 * β.val * Riesz1.rieszConstant s :=
      mul_pos (mul_pos two_pos β.property) (Riesz1.rieszConstant_pos s)
    have h1 : 0 ≤ (2 * Real.pi) ^ (1 - s.val) / (2 * β.val * Riesz1.rieszConstant s) :=
      div_nonneg (Real.rpow_nonneg (by positivity) _) hc.le
    exact mul_nonneg h1 (Real.rpow_nonneg hℓ.le _)
  unfold Riesz1.circleVariance
  rw [show Riesz1.parametersExponent (longParameters β s) = s from rfl]
  dsimp only [longParameters]
  rw [hsub, hcs4, ENNReal.toReal_mul, ENNReal.toReal_ofReal hA]
  have h2 : (2 * Real.pi) ^ (1 - s.val) / (2 * β.val * Riesz1.rieszConstant s) *
      ℓ.val ^ (-s.val) *
      (Riesz1.circleSobolevSq ((1 - s.val) / 2)
        ⟨fun t : UnitAddCircle => (Riesz1.centeredIndicatorArc (ℓ.val / 4) t : ℂ),
          Riesz1.memLp_centeredIndicatorArc (ℓ.val / 4)⟩).toReal =
      ℓ.val ^ (-s.val) * ((2 * Real.pi) ^ (1 - s.val) / (2 * β.val * Riesz1.rieszConstant s) *
      (Riesz1.circleSobolevSq ((1 - s.val) / 2)
        ⟨fun t : UnitAddCircle => (Riesz1.centeredIndicatorArc (ℓ.val / 4) t : ℂ),
          Riesz1.memLp_centeredIndicatorArc (ℓ.val / 4)⟩).toReal) := by ring
  rw [h2, hform, show 2 * (ℓ.val / 4) = ℓ.val / 2 by ring]
  ring

/-- The scale `1/N` at the particle number `N`, used to instantiate the admissibility of the arc
profile. -/
def inverseScale (N : ℕ+) : Riesz1.Scale :=
  ⟨1 / (N : ℝ), one_div_pos.2 (by exact_mod_cast N.pos),
    (div_le_one (by exact_mod_cast N.pos)).2 (by exact_mod_cast N.pos)⟩

/-- The scales `1/N` tend to zero along the particle numbers `n + 1`. -/
lemma tendsto_inverseScale :
    Tendsto (fun n : ℕ => (inverseScale ⟨n + 1, Nat.succ_pos n⟩).val) atTop (𝓝 0) := by
  refine (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).congr fun n => ?_
  simp [inverseScale]

/-- The arc profile is compactly supported, with margin `1/4`. -/
lemma compactProfile_arcProfile : Riesz1.CompactProfile arcProfile := by
  refine ⟨1 / 4, by norm_num, by norm_num, Filter.Eventually.of_forall fun x hx => ?_⟩
  have hz : Riesz1.zeroExtension arcProfile x =
      (Set.Ioo ((0 : ℝ) - 1 / 4) (0 + 1 / 4)).indicator (fun _ => (1 : ℝ)) x :=
    Riesz1.zeroExtension_arcIndicator (c := 0) (a := 1 / 4) (by norm_num) (by norm_num) x
  rw [hz, Set.indicator_of_notMem]
  intro hm
  rw [Set.mem_Ioo] at hm
  have : |x| < 1 / 4 := abs_lt.2 ⟨by linarith [hm.1], by linarith [hm.2]⟩
  linarith

/-- The zero extension of `ξ`'s Riesz 1 representative is `ξ` almost everywhere, so every
representative of the zero extension has the class `intervalL2`. -/
lemma eq_intervalL2_of_representsZeroExtension (f : Lp ℂ 2 (volume : Measure ℝ))
    (hf : Riesz1.RepresentsZeroExtension arcProfile f) : f = intervalL2 := by
  refine Lp.ext ?_
  have hf' : (fun x => f x) =ᵐ[volume] (fun x => (Riesz1.zeroExtension arcProfile x : ℂ)) := hf
  have hint : (fun x => (Riesz1.zeroExtension arcProfile x : ℂ)) =ᵐ[volume]
      (fun x => (intervalIndicator x : ℂ)) := zeroExtension_arcProfile_ae
  exact hf'.trans (hint.trans memLp_intervalIndicator.coeFn_toLp.symm)

/-- A small-scale bound with exponent `e > 0` forces a nonnegative quantity to vanish. -/
lemma eq_zero_of_le_mul_rpow {D K e δ : ℝ} (hD : 0 ≤ D) (he : 0 < e) (hδ : 0 < δ)
    (h : ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ δ → D ≤ K * ℓ ^ e) : D = 0 := by
  have hc : Tendsto (fun ℓ : ℝ => K * ℓ ^ e) (𝓝[>] 0) (𝓝 0) := by
    have hcont : ContinuousAt (fun ℓ : ℝ => ℓ ^ e) 0 :=
      Real.continuousAt_rpow_const 0 e (Or.inr he.le)
    have hlim : Tendsto (fun ℓ : ℝ => K * ℓ ^ e) (𝓝 0) (𝓝 (K * (0 : ℝ) ^ e)) :=
      (continuousAt_const.mul hcont).tendsto
    rw [Real.zero_rpow he.ne', mul_zero] at hlim
    exact hlim.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ ℓ in 𝓝[>] (0 : ℝ), D ≤ K * ℓ ^ e :=
    Filter.eventually_of_mem (Ioo_mem_nhdsGT hδ) fun ℓ hℓ => h ℓ hℓ.1 hℓ.2.le
  have hle : D ≤ 0 := ge_of_tendsto hc hev
  linarith

/-- See Corollary 1.1 of the paper: the constant `σ²_{s,β} = cot(πs/2)/(2βπs)` is `Riesz1.countVariance`. -/
theorem countVariance_longParameters (β : InverseTemperature) (s : Riesz1.RieszExponent) :
    Riesz1.countVariance (longParameters β s) =
      Real.cos (Real.pi * s.val / 2) / Real.sin (Real.pi * s.val / 2) /
        (2 * β.val * Real.pi * s.val) :=
  rfl

/-- The line variance of `ξ` is `2^{-s}` times the circle constant `σ²_{s,β} = cot(πs/2)/(2βπs)`.
The circle variance at scale `ℓ` is
`ℓ^{-s} κ ζ_s(ℓ/2)` with `κ = σ²_{s,β}`, and `ζ_s(t) = t^s + O(t²)` for small `t`. Letting `ℓ → 0`
in the Riesz 1 bound `|σ_ℓ² - V| ≤ C₁ ℓ^{2-s}` gives the value of `V`. -/
theorem intervalLineVariance_eq_cot (β : InverseTemperature) (s : Riesz1.RieszExponent) :
    intervalLineVariance β s = ENNReal.ofReal ((2 : ℝ) ^ (-s.val) *
      (Real.cos (Real.pi * s.val / 2) / Real.sin (Real.pi * s.val / 2) /
        (2 * β.val * Real.pi * s.val))) := by
  obtain ⟨d, hd⟩ := Riesz1.admissible_compact_arcIndicator (longParameters β s) (c := 0)
    (a := 1 / 4) (by norm_num) (by norm_num)
  have Q := Riesz1.quantitative_variance β.val s.val β.property s.property.1 s.property.2
    arcProfile 0 d
  obtain ⟨f0, hrep, -, hlt, C1, hC1, hall⟩ :=
    Q.2.2 ⟨inverseScale, hd inverseScale tendsto_inverseScale⟩ compactProfile_arcProfile
  have hV : intervalLineVariance β s = Riesz1.lineVariance (longParameters β s) f0 := by
    rw [intervalLineVariance_eq, eq_intervalL2_of_representsZeroExtension f0 hrep]
  have hfin : Riesz1.lineVariance (longParameters β s) f0 ≠ ⊤ := hlt.ne
  obtain ⟨C, hC, t₀, ht₀, hasym⟩ := Riesz1.periodicZeta_asymptotic s
  set κ := Real.cos (Real.pi * s.val / 2) / Real.sin (Real.pi * s.val / 2) /
    (2 * Real.pi * β.val * s.val) with hκdef
  have hκ0 : 0 ≤ κ := by
    have hs0 : 0 < s.val := s.property.1
    have hs1 : s.val < 1 := s.property.2
    have hcos : 0 ≤ Real.cos (Real.pi * s.val / 2) :=
      Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
    have hsin : 0 < Real.sin (Real.pi * s.val / 2) :=
      Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
    have hden : 0 < 2 * Real.pi * β.val * s.val :=
      mul_pos (mul_pos (mul_pos two_pos Real.pi_pos) β.property) hs0
    exact div_nonneg (div_nonneg hcos hsin.le) hden.le
  set δ := min 1 (2 * t₀) with hδdef
  have hδ0 : 0 < δ := lt_min one_pos (by linarith)
  have hbound : ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ δ →
      |(Riesz1.lineVariance (longParameters β s) f0).toReal - (2 : ℝ) ^ (-s.val) * κ| ≤
        (C1 + κ * C / 4) * ℓ ^ (2 - s.val) := by
    intro ℓ hℓ hℓδ
    have hℓ1 : ℓ ≤ 1 := hℓδ.trans (min_le_left _ _)
    have hℓt : ℓ ≤ 2 * t₀ := hℓδ.trans (min_le_right _ _)
    let ℓS : Riesz1.Scale := ⟨ℓ, hℓ, hℓ1⟩
    have hb : |(Riesz1.circleVariance (longParameters β s) arcProfile ℓS).toReal -
        (Riesz1.lineVariance (longParameters β s) f0).toReal| ≤ C1 * ℓ ^ (2 - s.val) :=
      (hall ℓS).2.2
    have hcirc : (Riesz1.circleVariance (longParameters β s) arcProfile ℓS).toReal =
        ℓ ^ (-s.val) * κ * Riesz1.periodicZeta s ((ℓ / 2 : ℝ) : UnitAddCircle) :=
      circleVariance_arcProfile_toReal β s ℓS
    have hasy := hasym (ℓ / 2) (by positivity) (by linarith)
    have hkey : ℓ ^ (-s.val) * (ℓ / 2) ^ s.val = (2 : ℝ) ^ (-s.val) := by
      rw [Real.div_rpow hℓ.le (by norm_num), Real.rpow_neg hℓ.le,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      have hp : ℓ ^ s.val ≠ 0 := (Real.rpow_pos_of_pos hℓ _).ne'
      have h2 : (2 : ℝ) ^ s.val ≠ 0 := (Real.rpow_pos_of_pos two_pos _).ne'
      field_simp
    have hpow : ℓ ^ (2 - s.val) = ℓ ^ (-s.val) * ℓ ^ 2 := by
      rw [show (2 : ℝ) - s.val = -s.val + 2 by ring, Real.rpow_add hℓ, Real.rpow_two]
    have ha0 : 0 ≤ ℓ ^ (-s.val) := Real.rpow_nonneg hℓ.le _
    have hdiff : |(Riesz1.circleVariance (longParameters β s) arcProfile ℓS).toReal -
        (2 : ℝ) ^ (-s.val) * κ| ≤ κ * C / 4 * ℓ ^ (2 - s.val) := by
      have e1 : (Riesz1.circleVariance (longParameters β s) arcProfile ℓS).toReal -
          (2 : ℝ) ^ (-s.val) * κ = κ * ℓ ^ (-s.val) *
            (Riesz1.periodicZeta s ((ℓ / 2 : ℝ) : UnitAddCircle) - (ℓ / 2) ^ s.val) := by
        rw [hcirc]
        linear_combination κ * hkey
      rw [e1, abs_mul, abs_mul, abs_of_nonneg hκ0, abs_of_nonneg ha0]
      have hmul : 0 ≤ κ * ℓ ^ (-s.val) := mul_nonneg hκ0 ha0
      calc κ * ℓ ^ (-s.val) * |Riesz1.periodicZeta s ((ℓ / 2 : ℝ) : UnitAddCircle) - (ℓ / 2) ^ s.val|
          ≤ κ * ℓ ^ (-s.val) * (C * (ℓ / 2) ^ 2) :=
            mul_le_mul_of_nonneg_left hasy hmul
        _ = κ * C / 4 * ℓ ^ (2 - s.val) := by rw [hpow]; ring
    calc |(Riesz1.lineVariance (longParameters β s) f0).toReal - (2 : ℝ) ^ (-s.val) * κ|
        ≤ |(Riesz1.lineVariance (longParameters β s) f0).toReal -
            (Riesz1.circleVariance (longParameters β s) arcProfile ℓS).toReal| +
          |(Riesz1.circleVariance (longParameters β s) arcProfile ℓS).toReal -
            (2 : ℝ) ^ (-s.val) * κ| := abs_sub_le _ _ _
      _ ≤ C1 * ℓ ^ (2 - s.val) + κ * C / 4 * ℓ ^ (2 - s.val) := by
          rw [abs_sub_comm]
          exact add_le_add hb hdiff
      _ = (C1 + κ * C / 4) * ℓ ^ (2 - s.val) := by ring
  have hzero : |(Riesz1.lineVariance (longParameters β s) f0).toReal - (2 : ℝ) ^ (-s.val) * κ| = 0 :=
    eq_zero_of_le_mul_rpow (abs_nonneg _) (by linarith [s.property.2, s.property.1] : (0 : ℝ) < 2 - s.val)
      hδ0 hbound
  have hVr : (Riesz1.lineVariance (longParameters β s) f0).toReal = (2 : ℝ) ^ (-s.val) * κ :=
    sub_eq_zero.1 (abs_eq_zero.1 hzero)
  rw [hV, ← ENNReal.ofReal_toReal hfin, hVr]
  congr 1
  rw [hκdef]
  ring_nf

/-- A real `t` whose central representative is `a` lies in the lattice `a + ℤ`. -/
lemma mem_range_of_centralRep_eq (a : ℝ) (t : ℝ)
    (h : Riesz1.centralRep Riesz1.unitLength (t : UnitAddCircle) = a) :
    t ∈ Set.range (fun n : ℤ => a + n) := by
  obtain ⟨n, hn⟩ := Riesz1.centralRep_coe_eq Riesz1.unitLength t
  simp only [Riesz1.unitLength, mul_one] at hn
  have h2 : a = t - n := h.symm.trans hn
  exact ⟨n, by linarith⟩

/-- The configurations with a particle on the endpoints `ℓ/4 + ℤ` of the arc. -/
def endpointBad (ℓ : Riesz1.Scale) (N : ℕ+) : Set (Riesz1.Configuration N) :=
  ⋃ i : Fin (N : ℕ), {X | X.val i ∈ Set.range (fun n : ℤ => ℓ.val / 4 + n)}

/-- A coordinate of a configuration lies in a Lebesgue-null set with probability zero under the
configuration volume. -/
lemma configurationVolume_coord_null (N : ℕ+) (i : Fin (N : ℕ)) {A : Set ℝ}
    (hA : volume A = 0) :
    Riesz1.configurationVolume N {X : Riesz1.Configuration N | X.val i ∈ A} = 0 := by
  have hT : volume ((fun x : Fin (N : ℕ) → ℝ => x i) ⁻¹' A) = 0 := by
    rw [volume_pi]
    exact Measure.pi_eval_preimage_null (fun _ : Fin (N : ℕ) => volume) hA
  unfold Riesz1.configurationVolume
  rw [(MeasurableEmbedding.subtype_coe (Riesz1.measurableSet_orderedDomain N)).comap_apply]
  refine measure_mono_null ?_ hT
  rintro _ ⟨X, hX, rfl⟩
  exact hX

/-- A configuration volume-null set carries no Gibbs mass. -/
lemma gibbsMeasure_null_of_configurationVolume_null (P : Riesz1.Parameters) (N : ℕ+)
    {S : Set (Riesz1.Configuration N)} (hS : Riesz1.configurationVolume N S = 0) :
    Riesz1.gibbsMeasure P N S = 0 := by
  unfold Riesz1.gibbsMeasure Riesz1.gibbsWeight
  rw [Measure.smul_apply, smul_eq_mul, mul_eq_zero]
  exact Or.inr (withDensity_absolutelyContinuous _ _ hS)

/-- The Gibbs law gives no mass to configurations with a particle at an endpoint `ℓ/4 + ℤ`. -/
lemma gibbsMeasure_endpointBad_null (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (ℓ : Riesz1.Scale) (N : ℕ+) :
    gibbsMeasure (ofLong β s) N (endpointBad ℓ N) = 0 := by
  rw [gibbsMeasure_ofLong]
  refine gibbsMeasure_null_of_configurationVolume_null _ N ?_
  unfold endpointBad
  refine measure_iUnion_null fun i => ?_
  exact configurationVolume_coord_null N i ((Set.countable_range _).measure_zero volume)

/-- Off the endpoint configurations, the Riesz 2 centred statistic equals the Riesz 1 fluctuation of
the open-arc profile. -/
lemma intervalFluctuation_eq_fluctuation_of_not_bad (ℓ : Riesz1.Scale) (N : ℕ+)
    (X : Riesz1.Configuration N) (hX : X ∉ endpointBad ℓ N) :
    intervalFluctuation ℓ N X =
      Riesz1.fluctuation ⟨Riesz1.testAtScale arcProfile ℓ, Riesz1.testAtScaleL1 arcProfile ℓ⟩ X := by
  have hint : ∫ x : UnitAddCircle, Riesz1.testAtScale arcProfile ℓ x = ℓ.val / 2 := by
    have hfun : Riesz1.testAtScale arcProfile ℓ = Riesz1.arcIndicator 0 (ℓ.val / 4) := by
      funext x
      exact testAtScale_arcProfile ℓ x
    have hℓ1 : ℓ.val ≤ 1 := ℓ.property.2
    have hℓ : 0 < ℓ.val := ℓ.property.1
    rw [hfun, Riesz1.integral_arcIndicator 0 (by positivity) (by linarith)]
    ring
  have hsum : ∑ i : Fin (N : ℕ), intervalProfile ℓ ((X.val i : ℝ) : UnitAddCircle) =
      ∑ i : Fin (N : ℕ), Riesz1.testAtScale arcProfile ℓ ((X.val i : ℝ) : UnitAddCircle) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [testAtScale_arcProfile, intervalProfile_eq_arcIndicator_of_ne]
    intro hc
    apply hX
    unfold endpointBad
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨i, mem_range_of_centralRep_eq _ _ hc⟩
  unfold intervalFluctuation Riesz1.fluctuation Riesz1.linearStatistic
  simp only
  rw [hsum, hint]
  ring

/-- The Riesz 2 centred statistic agrees with the Riesz 1 fluctuation almost surely under the Gibbs
law. -/
lemma intervalFluctuation_ae_eq_fluctuation (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (ℓ : Riesz1.Scale) (N : ℕ+) :
    intervalFluctuation ℓ N =ᵐ[gibbsMeasure (ofLong β s) N]
      Riesz1.fluctuation ⟨Riesz1.testAtScale arcProfile ℓ, Riesz1.testAtScaleL1 arcProfile ℓ⟩ := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (gibbsMeasure_endpointBad_null β s ℓ N)]
    with X hX
  exact intervalFluctuation_eq_fluctuation_of_not_bad ℓ N X hX

/-- The Riesz 1 admissibility data of the arc profile, valid along every scale sequence tending to
zero. -/
lemma exists_admissible_data (β : InverseTemperature) (s : Riesz1.RieszExponent) :
    ∃ d : Riesz1.TestData, ∀ ell : Riesz1.Scales,
      Tendsto (fun n : ℕ => (ell ⟨n + 1, Nat.succ_pos n⟩).val) atTop (𝓝 0) →
        Riesz1.Admissible (longParameters β s) arcProfile ell 0 d := by
  obtain ⟨d, hd⟩ := Riesz1.admissible_compact_arcIndicator (longParameters β s) (c := 0)
    (a := 1 / 4) (by norm_num) (by norm_num)
  exact ⟨d, hd⟩

/-- The scale sequence with value `ℓ` at the particle number `N` and value `1/M` at `M ≠ N`. -/
def scaleAt (ℓ : Riesz1.Scale) (N : ℕ+) : Riesz1.Scales :=
  fun M => if M = N then ℓ else inverseScale M

/-- The scale sequence `scaleAt ℓ N` tends to zero, since it differs from `1/M` at finitely many
particle numbers. -/
lemma tendsto_scaleAt (ℓ : Riesz1.Scale) (N : ℕ+) :
    Tendsto (fun n : ℕ => (scaleAt ℓ N ⟨n + 1, Nat.succ_pos n⟩).val) atTop (𝓝 0) := by
  refine Tendsto.congr' ?_ tendsto_inverseScale
  filter_upwards [eventually_ge_atTop (N : ℕ)] with n hn
  have hne : (⟨n + 1, Nat.succ_pos n⟩ : ℕ+) ≠ N := by
    intro h
    have := congrArg PNat.val h
    simp only [PNat.mk_coe] at this
    omega
  unfold scaleAt
  split_ifs with h
  · exact absurd h hne
  · rfl

lemma scaleAt_self (ℓ : Riesz1.Scale) (N : ℕ+) : scaleAt ℓ N N = ℓ := by
  simp [scaleAt]

/-- The Riesz 1 variance is unchanged when the centred statistic changes on a null set. -/
lemma variance_congr_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {F G : Ω → ℝ}
    (h : F =ᵐ[μ] G) (hF : Integrable F μ) (hG : Integrable G μ) :
    Riesz1.variance μ F hF = Riesz1.variance μ G hG := by
  unfold Riesz1.variance
  rw [integral_congr_ae h]
  refine lintegral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]

/-- The companion variance expansion. For every `η > 0` there is
`C` such that, for every `N` and `ℓ` with `Nℓ ≥ 1`, the variance of `F_{N,ℓ}` differs from
`(Nℓ)^s σ_ℓ²(ξ)` by at most `C (Nℓ)^{max(2s-1,0)+η}`. -/
theorem intervalVariance_expansion (β : InverseTemperature) (s : Riesz1.RieszExponent) :
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ : Riesz1.Scale), 1 ≤ (N : ℝ) * ℓ.val →
      ∃ hF : Integrable (intervalFluctuation ℓ N) (gibbsMeasure (ofLong β s) N),
        Riesz1.variance (gibbsMeasure (ofLong β s) N) (intervalFluctuation ℓ N) hF < ⊤ ∧
        |(Riesz1.variance (gibbsMeasure (ofLong β s) N) (intervalFluctuation ℓ N) hF).toReal -
            ((N : ℝ) * ℓ.val) ^ s.val * (intervalCircleVariance β s ℓ).toReal| ≤
          C * ((N : ℝ) * ℓ.val) ^ (max (2 * s.val - 1) 0 + η) := by
  intro η hη
  obtain ⟨d, hd⟩ := exists_admissible_data β s
  have Q := Riesz1.quantitative_variance β.val s.val β.property s.property.1 s.property.2
    arcProfile 0 d
  obtain ⟨C, hC, hb⟩ := Q.2.1 η hη
  refine ⟨C, hC, fun N ℓ hN => ?_⟩
  have hae := intervalFluctuation_ae_eq_fluctuation β s ℓ N
  rw [gibbsMeasure_ofLong] at hae ⊢
  have hadm := hd (scaleAt ℓ N) (tendsto_scaleAt ℓ N)
  have h := hb (scaleAt ℓ N) hadm N (by rw [scaleAt_self]; exact hN)
  rw [scaleAt_self] at h
  obtain ⟨hF, hfin, hbd⟩ := h
  have hF' : Integrable (intervalFluctuation ℓ N) _ := hF.congr hae.symm
  refine ⟨hF', ?_, ?_⟩
  · rw [variance_congr_ae hae hF' hF]
    exact hfin
  · rw [variance_congr_ae hae hF' hF, intervalCircleVariance_eq]
    rw [mul_zero] at hbd
    exact hbd

/-- The Riesz 1 quantitative variance bounds of the arc profile: the circle variances are finite and
approach the line variance at rate `ℓ^{2-s}`. -/
lemma arc_quantitative_bounds (β : InverseTemperature) (s : Riesz1.RieszExponent) :
    ∃ C1 : ℝ, 0 < C1 ∧ ∀ ℓ : Riesz1.Scale,
      Riesz1.circleVariance (longParameters β s) arcProfile ℓ < ⊤ ∧
      |(Riesz1.circleVariance (longParameters β s) arcProfile ℓ).toReal -
          (intervalLineVariance β s).toReal| ≤ C1 * ℓ.val ^ (2 - s.val) := by
  obtain ⟨d, hd⟩ := exists_admissible_data β s
  have Q := Riesz1.quantitative_variance β.val s.val β.property s.property.1 s.property.2
    arcProfile 0 d
  obtain ⟨f0, hrep, -, -, C1, hC1, hall⟩ :=
    Q.2.2 ⟨inverseScale, hd inverseScale tendsto_inverseScale⟩ compactProfile_arcProfile
  have hV : intervalLineVariance β s = Riesz1.lineVariance (longParameters β s) f0 := by
    rw [intervalLineVariance_eq, eq_intervalL2_of_representsZeroExtension f0 hrep]
  refine ⟨C1, hC1, fun ℓ => ?_⟩
  obtain ⟨-, h1, h2⟩ := hall ℓ
  rw [hV]
  exact ⟨h1, h2⟩

/-- The natural-number index of particle numbers `N ↦ N - 1` tends to infinity. -/
lemma tendsto_natPred_atTop : Tendsto (fun N : ℕ+ => N.natPred) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun b => ⟨(b + 1).succPNat, fun N hN => ?_⟩
  have h : (b + 1).succ ≤ (N : ℕ) := hN
  show b ≤ (N : ℕ) - 1
  omega

/-- The particle numbers `n + 1` tend to infinity along the natural numbers. -/
lemma tendsto_particleNumber_atTop : Tendsto (fun n : ℕ => Riesz1.particleNumber n) atTop atTop := by
  refine tendsto_atTop_atTop.2 fun b => ⟨b, fun n hn => ?_⟩
  have h : (b : ℕ) ≤ n := hn
  show (b : ℕ) ≤ n + 1
  omega

/-- Riesz 1's particle number of `N - 1` is `N`. -/
lemma particleNumber_natPred (N : ℕ+) : Riesz1.particleNumber N.natPred = N := by
  apply PNat.eq
  simp [Riesz1.particleNumber, PNat.natPred_add_one]

/-- The Riesz 2 normalized centred statistics are the Riesz 1 statistic laws, almost surely. -/
lemma map_normalized_eq_statisticLaws (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (ℓ : Riesz1.Scales) (N : ℕ+) :
    (gibbsMeasure (ofLong β s) N).map
        (fun X => ((N : ℝ) * (ℓ N).val) ^ (-s.val / 2) * intervalFluctuation (ℓ N) N X) =
      Riesz1.statisticLaws (longParameters β s) arcProfile ℓ N.natPred := by
  unfold Riesz1.statisticLaws
  rw [particleNumber_natPred, gibbsMeasure_ofLong]
  refine Measure.map_congr ?_
  have hae := intervalFluctuation_ae_eq_fluctuation β s (ℓ N) N
  rw [gibbsMeasure_ofLong] at hae
  filter_upwards [hae] with X hX
  unfold Riesz1.normalizedStatistic
  rw [hX]
  rfl

/-- The companion central limit theorem. For every
sequence of scales `ℓ_N ∈ (0,1]` with `ℓ_N → 0` and `Nℓ_N → ∞`, the normalized centred statistics
`(Nℓ_N)^{-s/2} F_{N,ℓ_N}` converge in law to the centred Gaussian of variance `V(ξ)`. -/
theorem intervalCLT (β : InverseTemperature) (s : Riesz1.RieszExponent) (ℓ : Riesz1.Scales)
    (hℓ0 : Tendsto (fun N : ℕ+ => (ℓ N).val) atTop (𝓝 0))
    (hℓN : Tendsto (fun N : ℕ+ => (N : ℝ) * (ℓ N).val) atTop atTop) :
    ConvergesInLawAlong atTop
      (fun N : ℕ+ => (gibbsMeasure (ofLong β s) N).map
        (fun X => ((N : ℝ) * (ℓ N).val) ^ (-s.val / 2) * intervalFluctuation (ℓ N) N X))
      (ProbabilityTheory.gaussianReal 0 (intervalLineVariance β s).toNNReal) := by
  obtain ⟨d, hd⟩ := exists_admissible_data β s
  have hℓ0' : Tendsto (fun n : ℕ => (ℓ (Riesz1.particleNumber n)).val) atTop (𝓝 0) :=
    hℓ0.comp tendsto_particleNumber_atTop
  have hmes : Riesz1.Mesoscopic ℓ := by
    have h := hℓN.comp (tendsto_particleNumber_atTop)
    exact h
  have Q := Riesz1.central_limit_theorem β.val s.val β.property s.property.1 s.property.2
    arcProfile 0 d
  obtain ⟨f0, hrep, -, hlt, hconv⟩ :=
    (Q.1 ℓ (hd ℓ hℓ0') hmes).2.2.2 ⟨compactProfile_arcProfile, hℓ0'⟩
  have hf0 : f0 = intervalL2 := eq_intervalL2_of_representsZeroExtension f0 hrep
  have hV : Riesz1.lineVariance ⟨(β.val, s.val), β.property, s.property.1, s.property.2⟩ f0 =
      intervalLineVariance β s := by
    rw [hf0]
    exact (intervalLineVariance_eq β s).symm
  rw [hV] at hconv
  unfold Riesz1.normalLaw at hconv
  obtain ⟨hprob, hlimprob, hT⟩ := hconv
  refine ⟨fun N => ?_, hlimprob, fun f => ?_⟩
  · dsimp only
    rw [map_normalized_eq_statisticLaws]
    exact hprob _
  · have hfun : (fun N : ℕ+ => ∫ x, f x ∂((gibbsMeasure (ofLong β s) N).map
        (fun X => ((N : ℝ) * (ℓ N).val) ^ (-s.val / 2) * intervalFluctuation (ℓ N) N X))) =
        (fun N : ℕ+ => ∫ x, f x ∂(Riesz1.statisticLaws (longParameters β s) arcProfile ℓ N.natPred)) := by
      funext N
      rw [map_normalized_eq_statisticLaws]
    rw [hfun]
    exact (hT f).comp tendsto_natPred_atTop

/-- The companion interval variance and central limit theorem for `ξ = 𝟙_{(-1/4,1/4]}` with `0 < s < 1` and `β > 0`. It collects the finiteness of
`σ_ℓ²(ξ)` and `V(ξ)`, the variance expansion, the rate `|σ_ℓ² - V| ≤ C ℓ^{2-s}`, the identity
`V(ξ) = 2^{-s} σ²_{s,β}` with `σ²_{s,β} = cot(πs/2)/(2βπs)`, and the central limit theorem. -/
theorem companion_interval_fluctuations (β : InverseTemperature) (s : Riesz1.RieszExponent) :
    (∀ ℓ : Riesz1.Scale, intervalCircleVariance β s ℓ < ⊤) ∧
    intervalLineVariance β s < ⊤ ∧
    (∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ : Riesz1.Scale), 1 ≤ (N : ℝ) * ℓ.val →
      ∃ hF : Integrable (intervalFluctuation ℓ N) (gibbsMeasure (ofLong β s) N),
        Riesz1.variance (gibbsMeasure (ofLong β s) N) (intervalFluctuation ℓ N) hF < ⊤ ∧
        |(Riesz1.variance (gibbsMeasure (ofLong β s) N) (intervalFluctuation ℓ N) hF).toReal -
            ((N : ℝ) * ℓ.val) ^ s.val * (intervalCircleVariance β s ℓ).toReal| ≤
          C * ((N : ℝ) * ℓ.val) ^ (max (2 * s.val - 1) 0 + η)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ ℓ : Riesz1.Scale,
      |(intervalCircleVariance β s ℓ).toReal - (intervalLineVariance β s).toReal| ≤
        C * ℓ.val ^ (2 - s.val)) ∧
    intervalLineVariance β s = ENNReal.ofReal ((2 : ℝ) ^ (-s.val) *
      (Real.cos (Real.pi * s.val / 2) / Real.sin (Real.pi * s.val / 2) /
        (2 * β.val * Real.pi * s.val))) ∧
    (∀ ℓ : Riesz1.Scales, Tendsto (fun N : ℕ+ => (ℓ N).val) atTop (𝓝 0) →
      Tendsto (fun N : ℕ+ => (N : ℝ) * (ℓ N).val) atTop atTop →
      ConvergesInLawAlong atTop
        (fun N : ℕ+ => (gibbsMeasure (ofLong β s) N).map
          (fun X => ((N : ℝ) * (ℓ N).val) ^ (-s.val / 2) * intervalFluctuation (ℓ N) N X))
        (ProbabilityTheory.gaussianReal 0 (intervalLineVariance β s).toNNReal)) := by
  obtain ⟨C1, hC1, hb⟩ := arc_quantitative_bounds β s
  refine ⟨fun ℓ => ?_, ?_, intervalVariance_expansion β s, ⟨C1, hC1, fun ℓ => ?_⟩,
    intervalLineVariance_eq_cot β s, fun ℓ h0 hN => intervalCLT β s ℓ h0 hN⟩
  · rw [intervalCircleVariance_eq]
    exact (hb ℓ).1
  · rw [intervalLineVariance_eq_cot]
    exact ENNReal.ofReal_lt_top
  · rw [intervalCircleVariance_eq]
    exact (hb ℓ).2

end Riesz2

end
end