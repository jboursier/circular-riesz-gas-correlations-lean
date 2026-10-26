/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.NonnegativeGibbsTilt
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Normalized overlap of probability densities

The minimum of two densities gives a common probability after normalization.
Domination by either original law costs the inverse square root of the overlap
mass in a centered L² estimate.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz2.DensityOverlap

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- The mass common to two real densities relative to `μ`. -/
def mass (f g : X → ℝ) : ℝ := ∫ x, min (f x) (g x) ∂μ

/-- The normalized common density on the carrier of pairs with positive
overlap mass. This is the literal minimum divided by its integral. -/
def density (f g : X → ℝ) (_ha : 0 < mass μ f g) (x : X) : ℝ := min (f x) (g x) / mass μ f g

/-- The overlap is integrable and at most either original density. -/
theorem integrable_min {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun x => min (f x) (g x)) μ := hf.inf hg

/-- Normalization and both pointwise domination bounds for the common
density. No almost-everywhere representative is selected. -/
theorem density_properties {f g : X → ℝ} (hf : Integrable f μ)
    (hg : Integrable g μ) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (ha : 0 < mass μ f g) :
    Integrable (density μ f g ha) μ ∧ (∀ x, 0 ≤ density μ f g ha x) ∧
      (∫ x, density μ f g ha x ∂μ) = 1 ∧
      (∀ x, density μ f g ha x ≤ (mass μ f g)⁻¹ * f x) ∧
      (∀ x, density μ f g ha x ≤ (mass μ f g)⁻¹ * g x) := by
  refine ⟨(hf.inf hg).div_const _, fun x => div_nonneg (le_min (hf0 x) (hg0 x)) ha.le,
    ?_, fun x => ?_, fun x => ?_⟩
  · change (∫ x, min (f x) (g x) / mass μ f g ∂μ) = 1
    simp only [div_eq_mul_inv, integral_mul_const]
    change mass μ f g * (mass μ f g)⁻¹ = 1
    exact mul_inv_cancel₀ ha.ne'
  · simpa only [density, div_eq_mul_inv, mul_comm] using
      div_le_div_of_nonneg_right (min_le_left (f x) (g x)) ha.le
  · simpa only [density, div_eq_mul_inv, mul_comm] using
      div_le_div_of_nonneg_right (min_le_right (f x) (g x)) ha.le

/-- A normalized common density defines a probability measure. -/
theorem probability {f g : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (ha : 0 < mass μ f g) :
    IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (density μ f g ha x))) := by
  obtain ⟨hi, h0, hn, _, _⟩ := density_properties μ hf hg hf0 hg0 ha
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all μ h0), hn, ENNReal.ofReal_one]

/-- Domination by the first density, in the measure order. -/
theorem measure_le_left {f g : X → ℝ} (hf : Measurable f) (_hg : Measurable g)
    (ha : 0 < mass μ f g) :
    μ.withDensity (fun x => ENNReal.ofReal (density μ f g ha x)) ≤
      ENNReal.ofReal (mass μ f g)⁻¹ • μ.withDensity (fun x => ENNReal.ofReal (f x)) := by
  rw [← withDensity_smul _ (hf.ennreal_ofReal)]
  apply withDensity_mono
  apply ae_of_all
  intro x
  change ENNReal.ofReal (density μ f g ha x) ≤ ENNReal.ofReal (mass μ f g)⁻¹ * ENNReal.ofReal (f x)
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr ha.le)]
  apply ENNReal.ofReal_le_ofReal
  change min (f x) (g x) / mass μ f g ≤ _
  simpa only [div_eq_mul_inv, mul_comm] using
    div_le_div_of_nonneg_right (min_le_left (f x) (g x)) ha.le

/-- Centered L² transfer under domination by a finite multiple of a
probability law. The observable's second moment is explicit. -/
theorem mean_sub_le {ν ρ : Measure X} [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    {A : ℝ} (hA : 0 ≤ A) (hρ : ρ ≤ ENNReal.ofReal A • ν)
    {H : X → ℝ} (hH : MemLp H 2 ν) :
    |(∫ x, H x ∂ρ) - ∫ x, H x ∂ν| ≤
      Real.sqrt A * Real.sqrt (∫ x, (H x - ∫ y, H y ∂ν) ^ 2 ∂ν) := by
  have hHρ := hH.of_measure_le_smul ENNReal.ofReal_ne_top hρ
  have hc := hH.sub (memLp_const (∫ y, H y ∂ν))
  have hcρ := hHρ.sub (memLp_const (∫ y, H y ∂ν))
  have hs := hc.integrable_sq.smul_measure (c := ENNReal.ofReal A) ENNReal.ofReal_ne_top
  have hb := integral_mono_measure hρ
    (ae_of_all _ fun x => sq_nonneg (H x - ∫ y, H y ∂ν)) hs
  rw [integral_smul_measure, ENNReal.toReal_ofReal hA, smul_eq_mul] at hb
  have hcs := NonnegativeTilt.abs_integral_le_sqrt_integral_sq hcρ
  change |∫ x, (H x - ∫ y, H y ∂ν) ∂ρ| ≤ _ at hcs
  rw [integral_sub (hHρ.integrable (by norm_num)) (integrable_const _), integral_const,
    probReal_univ, one_smul] at hcs
  exact hcs.trans ((Real.sqrt_le_sqrt hb).trans_eq (Real.sqrt_mul hA _))

/-- A common lower bound on an interval gives a lower bound for the
overlap mass. Endpoints do not affect the Lebesgue integral. -/
theorem mass_lower_of_interval {f g : ℝ → ℝ} (hf : Integrable f volume)
    (hg : Integrable g volume) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    {t r d : ℝ} (hr : 0 ≤ r)
    (hb : ∀ x, |x-t| ≤ r → d ≤ f x ∧ d ≤ g x) :
    2*r*d ≤ mass volume f g := by
  have hi := hf.inf hg
  have hconst : IntegrableOn (fun _ : ℝ => d) (Icc (t-r) (t+r)) volume :=
    integrableOn_const (by simp) (by simp)
  have hle : (∫ x in Icc (t-r) (t+r), d) ≤
      ∫ x in Icc (t-r) (t+r), min (f x) (g x) := by
    apply integral_mono_ae hconst hi.integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have hdist : |x-t| ≤ r := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact le_min (hb x hdist).1 (hb x hdist).2
  have he : (∫ x in Icc (t-r) (t+r), d) = 2*r*d := by
    rw [integral_const, Measure.real, Measure.restrict_apply_univ,
      Real.volume_Icc, ENNReal.toReal_ofReal (by linarith : 0 ≤ (t+r)-(t-r)), smul_eq_mul]
    ring
  rw [he] at hle
  exact hle.trans (integral_mono_measure Measure.restrict_le_self
    (ae_of_all _ fun x => le_min (hf0 x) (hg0 x)) hi)

/-- The central-density bound yields a common interval for two
log-concave densities whose means are near the same point. The explicit
standard-deviation bounds are internal analytic inputs. -/
theorem central_mass_lower_internal
    {c : ℝ} (hc : 0 < c)
    (hcentral : ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) →
      ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) →
      (∫⁻ x, ENNReal.ofReal (f x)) = 1 →
      ∀ a v : ℝ, Integrable (fun x => x) (volume.withDensity (fun x => ENNReal.ofReal (f x))) →
      (∫ x, x ∂volume.withDensity (fun x => ENNReal.ofReal (f x))) = a → 0 < v →
      (∫⁻ x, ENNReal.ofReal ((x-a)^2) ∂volume.withDensity (fun x => ENNReal.ofReal (f x))) =
        ENNReal.ofReal v → ∀ x, |x-a| ≤ c*Real.sqrt v → c/Real.sqrt v ≤ f x)
    {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f volume) (hgi : Integrable g volume)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hflog : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    (hglog : ConcaveOn ℝ {x | 0 < g x} (fun x => Real.log (g x)))
    (hfn : (∫⁻ x, ENNReal.ofReal (f x)) = 1)
    (hgn : (∫⁻ x, ENNReal.ofReal (g x)) = 1)
    {a b v w t lo hi : ℝ} (hlo : 0 < lo) (_hhi : 0 < hi)
    (hfm : Integrable (fun x => x) (volume.withDensity (fun x => ENNReal.ofReal (f x))))
    (hgm : Integrable (fun x => x) (volume.withDensity (fun x => ENNReal.ofReal (g x))))
    (hfa : (∫ x, x ∂volume.withDensity (fun x => ENNReal.ofReal (f x))) = a)
    (hga : (∫ x, x ∂volume.withDensity (fun x => ENNReal.ofReal (g x))) = b)
    (hv : 0 < v) (hw : 0 < w)
    (hfv : (∫⁻ x, ENNReal.ofReal ((x-a)^2) ∂volume.withDensity (fun x => ENNReal.ofReal (f x))) = ENNReal.ofReal v)
    (hgv : (∫⁻ x, ENNReal.ofReal ((x-b)^2) ∂volume.withDensity (fun x => ENNReal.ofReal (g x))) = ENNReal.ofReal w)
    (hvl : lo ≤ Real.sqrt v) (hwl : lo ≤ Real.sqrt w)
    (hvu : Real.sqrt v ≤ hi) (hwu : Real.sqrt w ≤ hi)
    (hat : |a-t| ≤ c*lo/2) (hbt : |b-t| ≤ c*lo/2) :
    c^2*lo/hi ≤ mass volume f g := by
  have hfc := hcentral f hf hf0 hflog hfn a v hfm hfa hv hfv
  have hgc := hcentral g hg hg0 hglog hgn b w hgm hga hw hgv
  have hbound : ∀ x, |x-t| ≤ c*lo/2 → c/hi ≤ f x ∧ c/hi ≤ g x := by
    intro x hx
    have hdist (a : ℝ) (ha : |a-t| ≤ c*lo/2) : |x-a| ≤ c*lo := by
      calc
        |x-a| ≤ |x-t| + |a-t| := by
          simpa only [abs_sub_comm] using abs_sub_le x t a
        _ ≤ c*lo := by linarith
    exact ⟨(div_le_div_of_nonneg_left hc.le (Real.sqrt_pos.mpr hv) hvu).trans
        (hfc x ((hdist a hat).trans (mul_le_mul_of_nonneg_left hvl hc.le))),
      (div_le_div_of_nonneg_left hc.le (Real.sqrt_pos.mpr hw) hwu).trans
        (hgc x ((hdist b hbt).trans (mul_le_mul_of_nonneg_left hwl hc.le)))⟩
  have hb := mass_lower_of_interval hfi hgi hf0 hg0
    (show 0 ≤ c*lo/2 by positivity) hbound
  convert hb using 1; ring

/-- Both centered expectations under the normalized minimum are bounded
by the sum of their original standard deviations, with overlap loss
`a₀⁻¹ᐟ²`. The two observables may differ. -/
theorem pair_mean_sub_le {f g H K : X → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f μ) (hgi : Integrable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (ha : 0 < mass μ f g)
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x)))]
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (g x)))]
    (hH : MemLp H 2 (μ.withDensity (fun x => ENNReal.ofReal (f x))))
    (hK : MemLp K 2 (μ.withDensity (fun x => ENNReal.ofReal (g x)))) :
    let ν := μ.withDensity (fun x => ENNReal.ofReal (f x))
    let ν' := μ.withDensity (fun x => ENNReal.ofReal (g x))
    let ρ := μ.withDensity (fun x => ENNReal.ofReal (density μ f g ha x))
    |(∫ x, H x ∂ρ) - ∫ x, H x ∂ν| +
      |(∫ x, K x ∂ρ) - ∫ x, K x ∂ν'| ≤
      Real.sqrt (mass μ f g)⁻¹ *
        (Real.sqrt (∫ x, (H x - ∫ y, H y ∂ν)^2 ∂ν) +
          Real.sqrt (∫ x, (K x - ∫ y, K y ∂ν')^2 ∂ν')) := by
  intro ν ν' ρ
  have : IsProbabilityMeasure ρ := probability μ hfi hgi hf0 hg0 ha
  have he : mass μ g f = mass μ f g := by simp only [mass, min_comm]
  have hd : density μ g f (he ▸ ha) = density μ f g ha := by
    funext x
    simp only [density, he, min_comm]
  have hleft := mean_sub_le (inv_nonneg.mpr ha.le)
    (measure_le_left μ hf hg ha) hH
  have hright := mean_sub_le (inv_nonneg.mpr ha.le)
    (show ρ ≤ ENNReal.ofReal (mass μ f g)⁻¹ • ν' from by
      simpa only [he, hd] using measure_le_left μ hg hf (he ▸ ha)) hK
  calc
    _ ≤ Real.sqrt (mass μ f g)⁻¹ * Real.sqrt (∫ x, (H x - ∫ y, H y ∂ν)^2 ∂ν) +
        Real.sqrt (mass μ f g)⁻¹ * Real.sqrt (∫ x, (K x - ∫ y, K y ∂ν')^2 ∂ν') :=
      add_le_add hleft hright
    _ = _ := by ring

/-- Polynomial overlap loss is absorbed into the averaging loss and
the stretched-exponential rate. This scalar helper keeps the final
constant bookkeeping separate from the measure comparison. -/
theorem averaging_rate_internal {a x ε κo κa τ A B c δ Q DA DB V W E : ℝ}
    (hx : 1 ≤ x) (hε : 0 < ε) (hκo : 0 < κo) (hA : 0 < A) (hB : 0 < B)
    (hQ : 0 ≤ Q) (hDA : 0 ≤ DA) (hDB : 0 ≤ DB)
    (_ha : 0 < a) (hmass : B⁻¹*x^(-κo*ε) ≤ a)
    (hE : E ≤ Real.sqrt a⁻¹*(V+W))
    (hV : V ≤ A*x^(κa*ε-τ/2)*DA + A*Real.exp (-c*x^δ)*DB)
    (hW : W ≤ A*x^(κa*ε-τ/2)*DA + A*Real.exp (-c*x^δ)*DB)
    (htail : x^(κo*ε/2)*Real.exp (-c*x^δ) ≤ Q*Real.exp (-(c/2)*x^δ)) :
    E ≤ (2*Real.sqrt B*A*(1+Q))*x^((κa+κo)*ε-τ/2)*DA +
      (2*Real.sqrt B*A*(1+Q))*Real.exp (-(c/2)*x^δ)*DB := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hmass0 : 0 < B⁻¹*x^(-κo*ε) := by positivity
  have hinv : a⁻¹ ≤ B*x^(κo*ε) := by
    have hh := one_div_le_one_div_of_le hmass0 hmass
    simp only [one_div] at hh
    rw [show -κo*ε = -(κo*ε) by ring, mul_inv_rev, Real.rpow_neg hx0.le, inv_inv, inv_inv] at hh
    simpa only [mul_comm] using hh
  have hsqrt : Real.sqrt a⁻¹ ≤ Real.sqrt B*x^(κo*ε/2) := by
    convert Real.sqrt_le_sqrt hinv using 1
    rw [Real.sqrt_mul hB.le, Real.sqrt_eq_rpow (x^(κo*ε)), ← Real.rpow_mul hx0.le]
    congr 2
    ring
  have hsum : V+W ≤ 2*(A*x^(κa*ε-τ/2)*DA + A*Real.exp (-c*x^δ)*DB) := by linarith
  have hmul : x^(κo*ε/2)*x^(κa*ε-τ/2) ≤ x^((κa+κo)*ε-τ/2) := by
    rw [← Real.rpow_add hx0]
    apply Real.rpow_le_rpow_of_exponent_le hx
    nlinarith
  let P := 2*Real.sqrt B*A
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hP' : P ≤ P*(1+Q) := by nlinarith
  have hPQ : P*Q ≤ P*(1+Q) := by nlinarith
  calc
    E ≤ Real.sqrt a⁻¹ * (2*(A*x^(κa*ε-τ/2)*DA + A*Real.exp (-c*x^δ)*DB)) :=
      hE.trans (mul_le_mul_of_nonneg_left hsum (Real.sqrt_nonneg _))
    _ ≤ (Real.sqrt B*x^(κo*ε/2)) * (2*(A*x^(κa*ε-τ/2)*DA + A*Real.exp (-c*x^δ)*DB)) :=
      mul_le_mul_of_nonneg_right hsqrt (by positivity)
    _ = P*(x^(κo*ε/2)*x^(κa*ε-τ/2))*DA +
        P*(x^(κo*ε/2)*Real.exp (-c*x^δ))*DB := by dsimp only [P]; ring
    _ ≤ P*x^((κa+κo)*ε-τ/2)*DA + P*(Q*Real.exp (-(c/2)*x^δ))*DB :=
      add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmul hP) hDA)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htail hP) hDB)
    _ = P*x^((κa+κo)*ε-τ/2)*DA + (P*Q)*Real.exp (-(c/2)*x^δ)*DB := by ring
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hP' (by positivity)) hDA)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPQ (Real.exp_pos _).le) hDB)

end Riesz2.DensityOverlap
