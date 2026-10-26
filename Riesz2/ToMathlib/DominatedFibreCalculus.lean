/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.AffineFibreDisintegration
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Probability.Moments.Covariance

/-!
# Dominated calculus on a fixed fibre

Differentiation under the integral gives the formulas used in Lemma 3.5,
Appendix A, Lemma 4.7 and Subsection 5.1. A moving fibre is first pulled back
to a fixed measure, with its Jacobian included in the integrand. The hypotheses
give domination, integrability and collision flatness.
The conditional law is `AffineFibre.normalizedMeasure`.

The parameter and fibre spaces may have dimension zero. Fréchet derivatives
give mixed coordinate derivatives after choosing a chart.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Riesz2
namespace DominatedFibre

variable {A E F : Type*} [MeasurableSpace A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Analytic input for differentiation on a fixed fibre. Local bounds use a
common neighbourhood and exceptional null set, independently of the parameter.
This is an internal calculus contract, not a physical-model assumption. -/
structure DominatedFDerivOn (μ : Measure A) (U : Set E)
    (f : E → A → F) (df : E → A → E →L[ℝ] F) : Prop where
  integrable : ∀ x ∈ U, Integrable (f x) μ
  derivative_measurable : ∀ x ∈ U, AEStronglyMeasurable (df x) μ
  locally_dominated : ∀ x ∈ U, ∃ s ∈ 𝓝 x, s ⊆ U ∧ ∃ b : A → ℝ,
    Integrable b μ ∧ (∀ᵐ y ∂μ, ∀ z ∈ s, ‖df z y‖ ≤ b y) ∧
      (∀ᵐ y ∂μ, ∀ z ∈ s, HasFDerivAt (fun t => f t y) (df z y) z)

variable {μ : Measure A} {U : Set E} {f : E → A → F}
  {df : E → A → E →L[ℝ] F}

omit [CompleteSpace F] in
/-- First fibre derivative, with integrability of the derivative established. -/
theorem DominatedFDerivOn.integrable_derivative
    (h : DominatedFDerivOn μ U f df) {x : E} (hx : x ∈ U) :
    Integrable (df x) μ := by
  obtain ⟨s, hs, hsU, b, hb, hbound, _⟩ := h.locally_dominated x hx
  exact hb.mono' (h.derivative_measurable x hx)
    (hbound.mono fun y hy => hy x (mem_of_mem_nhds hs))

omit [CompleteSpace F] in
/-- Dominated first derivative under a fixed fibre integral. -/
theorem DominatedFDerivOn.hasFDerivAt_integral
    (h : DominatedFDerivOn μ U f df) {x : E} (hx : x ∈ U) :
    HasFDerivAt (fun z => ∫ y, f z y ∂μ) (∫ y, df x y ∂μ) x := by
  obtain ⟨s, hs, hsU, b, hb, hbound, hdiff⟩ := h.locally_dominated x hx
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le hs
    (mem_of_superset hs fun z hz => (h.integrable z (hsU hz)).aestronglyMeasurable)
    (h.integrable x hx) (h.derivative_measurable x hx) hbound hb hdiff

omit [CompleteSpace F] in
/-- Identify the actual Fréchet derivative, rather than a chosen representative. -/
theorem DominatedFDerivOn.fderiv_integral
    (h : DominatedFDerivOn μ U f df) {x : E} (hx : x ∈ U) :
    fderiv ℝ (fun z => ∫ y, f z y ∂μ) x = ∫ y, df x y ∂μ :=
  (h.hasFDerivAt_integral hx).fderiv

omit [CompleteSpace F] in
/-- Second fibre derivative as the derivative of the actual first derivative.
The two domination contracts can have different local envelopes. -/
theorem hasFDerivAt_fderiv_integral
    {ddf : E → A → E →L[ℝ] E →L[ℝ] F}
    (hU : IsOpen U) (h : DominatedFDerivOn μ U f df)
    (h' : DominatedFDerivOn μ U df ddf) {x : E} (hx : x ∈ U) :
    HasFDerivAt (fun z => fderiv ℝ (fun t => ∫ y, f t y ∂μ) z)
      (∫ y, ddf x y ∂μ) x := by
  apply (h'.hasFDerivAt_integral hx).congr_of_eventuallyEq
  exact mem_of_superset (hU.mem_nhds hx) fun z hz => h.fderiv_integral hz

omit [CompleteSpace F] in
/-- A mixed second derivative is the integral of the mixed derivative. -/
theorem fderiv_fderiv_integral_apply
    {ddf : E → A → E →L[ℝ] E →L[ℝ] F}
    (hU : IsOpen U) (h : DominatedFDerivOn μ U f df)
    (h' : DominatedFDerivOn μ U df ddf) {x : E} (hx : x ∈ U) (u v : E) :
    fderiv ℝ (fun z => fderiv ℝ (fun t => ∫ y, f t y ∂μ) z) x u v =
      ∫ y, ddf x y u v ∂μ := by
  rw [(hasFDerivAt_fderiv_integral hU h h' hx).fderiv,
    ContinuousLinearMap.integral_apply (h'.integrable_derivative hx),
    ContinuousLinearMap.integral_apply
      ((h'.integrable_derivative hx).apply_continuousLinearMap u)]

section Normalization

variable {w : A → ℝ}

omit [CompleteSpace F] in
/-- Bochner integration against the explicit normalized measure. Positive
finite mass is proved from an integrable nonnegative real weight. -/
theorem integral_normalizedMeasure (hw : Integrable w μ) (hn : ∀ y, 0 ≤ w y)
    (hp : 0 < ∫ y, w y ∂μ) (g : A → F) :
    ∫ y, g y ∂AffineFibre.normalizedMeasure μ (fun y => ENNReal.ofReal (w y))
      (by rw [← ofReal_integral_eq_lintegral_ofReal hw (Eventually.of_forall hn)]
          exact ENNReal.ofReal_ne_zero_iff.mpr hp)
      (by rw [← ofReal_integral_eq_lintegral_ofReal hw (Eventually.of_forall hn)]
          exact ENNReal.ofReal_ne_top) =
      (∫ y, w y ∂μ)⁻¹ • ∫ y, w y • g y ∂μ := by
  rw [AffineFibre.normalizedMeasure_eq_smul, integral_smul_measure,
    ← ofReal_integral_eq_lintegral_ofReal hw (Eventually.of_forall hn),
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hp.le,
    integral_withDensity_eq_integral_toReal_smul₀
      hw.aestronglyMeasurable.aemeasurable.ennreal_ofReal (Eventually.of_forall fun _ =>
        ENNReal.ofReal_lt_top)]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by simp only [ENNReal.toReal_ofReal (hn y)]

omit [CompleteSpace F] in
/-- Integrability under the explicit conditional law is exactly weighted
integrability on the fixed fibre. This prevents junk Bochner expectations. -/
theorem integrable_normalizedMeasure_iff (hw : Integrable w μ) (hn : ∀ y, 0 ≤ w y)
    (hp : 0 < ∫ y, w y ∂μ) (g : A → F) :
    Integrable g (AffineFibre.normalizedMeasure μ (fun y => ENNReal.ofReal (w y))
      (by rw [← ofReal_integral_eq_lintegral_ofReal hw (Eventually.of_forall hn)]
          exact ENNReal.ofReal_ne_zero_iff.mpr hp)
      (by rw [← ofReal_integral_eq_lintegral_ofReal hw (Eventually.of_forall hn)]
          exact ENNReal.ofReal_ne_top)) ↔ Integrable (fun y => w y • g y) μ := by
  rw [AffineFibre.normalizedMeasure_eq_smul,
    integrable_smul_measure (ENNReal.inv_ne_zero.mpr
      (by rw [← ofReal_integral_eq_lintegral_ofReal hw (Eventually.of_forall hn)]
          exact ENNReal.ofReal_ne_top))
      (ENNReal.inv_ne_top.mpr
        (by rw [← ofReal_integral_eq_lintegral_ofReal hw (Eventually.of_forall hn)]
            exact ENNReal.ofReal_ne_zero_iff.mpr hp)),
    integrable_withDensity_iff_integrable_smul₀'
      hw.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hn _)]

end Normalization

section Logarithm

variable {Z : E → ℝ} {dZ : E → E →L[ℝ] ℝ}

/-- The derivative of minus the logarithm of a positive mass. -/
theorem hasFDerivAt_neg_log {x : E} {L : E →L[ℝ] ℝ}
    (hZ : HasFDerivAt Z L x) (hp : 0 < Z x) :
    HasFDerivAt (fun z => -Real.log (Z z)) (-(Z x)⁻¹ • L) x := by
  convert (hZ.log hp.ne').neg using 1
  ext u
  simp

/-- Differentiate the normalized score of a positive mass. This bilinear form
has the order: derivative direction first, score argument second. -/
theorem hasFDerivAt_neg_log_score {x : E} {L : E →L[ℝ] ℝ}
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hZ : HasFDerivAt Z L x)
    (hdZ : HasFDerivAt dZ B x) (hp : 0 < Z x) :
    HasFDerivAt (fun z => -(Z z)⁻¹ • dZ z)
      (-(Z x)⁻¹ • B + ((Z x ^ 2)⁻¹ • L).smulRight (dZ x)) x := by
  convert ((hasDerivAt_inv hp.ne').comp_hasFDerivAt x hZ).neg.smul hdZ using 1 <;>
    ext u v <;> simp

end Logarithm

section Marginal

variable {w : E → A → ℝ} {dw : E → A → E →L[ℝ] ℝ}
  {ddw : E → A → E →L[ℝ] E →L[ℝ] ℝ}

/-- Gradient of the marginal potential on the open positive-mass carrier. -/
theorem hasFDerivAt_neg_log_integral
    (h : DominatedFDerivOn μ U w dw) {x : E} (hx : x ∈ U)
    (hp : 0 < ∫ y, w x y ∂μ) :
    HasFDerivAt (fun z => -Real.log (∫ y, w z y ∂μ))
      (-(∫ y, w x y ∂μ)⁻¹ • ∫ y, dw x y ∂μ) x :=
  hasFDerivAt_neg_log (h.hasFDerivAt_integral hx) hp

/-- Hessian of minus the logarithm of a fibre integral. This differentiates the
actual Fréchet gradient and therefore can be used in any coordinate chart. -/
theorem hasFDerivAt_fderiv_neg_log_integral
    (hU : IsOpen U) (h : DominatedFDerivOn μ U w dw)
    (h' : DominatedFDerivOn μ U dw ddw)
    (hp : ∀ z ∈ U, 0 < ∫ y, w z y ∂μ) {x : E} (hx : x ∈ U) :
    HasFDerivAt (fun z => fderiv ℝ (fun t => -Real.log (∫ y, w t y ∂μ)) z)
      (-(∫ y, w x y ∂μ)⁻¹ • (∫ y, ddw x y ∂μ) +
        (((∫ y, w x y ∂μ) ^ 2)⁻¹ • (∫ y, dw x y ∂μ)).smulRight
          (∫ y, dw x y ∂μ)) x := by
  apply (hasFDerivAt_neg_log_score (h.hasFDerivAt_integral hx)
    (h'.hasFDerivAt_integral hx) (hp x hx)).congr_of_eventuallyEq
  exact mem_of_superset (hU.mem_nhds hx) fun z hz =>
    (hasFDerivAt_neg_log_integral h hz (hp z hz)).fderiv

/-- The mixed marginal Hessian in terms of three integrable fibre derivatives.
This formula fixes the sign of the covariance term. -/
theorem fderiv_fderiv_neg_log_integral_apply
    (hU : IsOpen U) (h : DominatedFDerivOn μ U w dw)
    (h' : DominatedFDerivOn μ U dw ddw)
    (hp : ∀ z ∈ U, 0 < ∫ y, w z y ∂μ) {x : E} (hx : x ∈ U) (u v : E) :
    fderiv ℝ (fun z => fderiv ℝ (fun t => -Real.log (∫ y, w t y ∂μ)) z) x u v =
      (∫ y, dw x y u ∂μ) * (∫ y, dw x y v ∂μ) / (∫ y, w x y ∂μ) ^ 2 -
        (∫ y, ddw x y u v ∂μ) / (∫ y, w x y ∂μ) := by
  rw [(hasFDerivAt_fderiv_neg_log_integral hU h h' hp hx).fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul,
    ContinuousLinearMap.integral_apply (h.integrable_derivative hx),
    ContinuousLinearMap.integral_apply (h'.integrable_derivative hx),
    ContinuousLinearMap.integral_apply
      ((h'.integrable_derivative hx).apply_continuousLinearMap u)]
  ring

omit [CompleteSpace F] in
/-- Derivative of a normalized vector-valued fibre integral. For observables
depending on the parameter, use the derivative of the whole weighted numerator. -/
theorem hasFDerivAt_normalized_integral
    (hw : DominatedFDerivOn μ U w dw) (hf : DominatedFDerivOn μ U f df)
    {x : E} (hx : x ∈ U) (hp : 0 < ∫ y, w x y ∂μ) :
    HasFDerivAt (fun z => (∫ y, w z y ∂μ)⁻¹ • ∫ y, f z y ∂μ)
      ((∫ y, w x y ∂μ)⁻¹ • (∫ y, df x y ∂μ) +
        (-((∫ y, w x y ∂μ) ^ 2)⁻¹ • (∫ y, dw x y ∂μ)).smulRight
          (∫ y, f x y ∂μ)) x := by
  exact ((hasDerivAt_inv hp.ne').comp_hasFDerivAt x
    (hw.hasFDerivAt_integral hx)).smul (hf.hasFDerivAt_integral hx)

/-- Logarithmic score of a normalized positive fibre density. The positive
pointwise weight assumption is needed only at this fibre point. -/
theorem fderiv_log_normalized_density
    (h : DominatedFDerivOn μ U w dw) {x : E} (hx : x ∈ U)
    (hp : 0 < ∫ y, w x y ∂μ) {y : A} (hy : 0 < w x y)
    (hwy : HasFDerivAt (fun z => w z y) (dw x y) x) :
    fderiv ℝ (fun z => Real.log (w z y / ∫ a, w z a ∂μ)) x =
      (w x y)⁻¹ • dw x y - (∫ a, w x a ∂μ)⁻¹ • ∫ a, dw x a ∂μ := by
  have heq : (fun z => Real.log (w z y / ∫ a, w z a ∂μ)) =ᶠ[𝓝 x]
      fun z => Real.log (w z y) - Real.log (∫ a, w z a ∂μ) := by
    filter_upwards [hwy.continuousAt.eventually_ne hy.ne',
      (h.hasFDerivAt_integral hx).continuousAt.eventually_ne hp.ne'] with z hz hz'
    exact Real.log_div hz hz'
  rw [heq.fderiv_eq]
  exact ((hwy.log hy.ne').sub ((h.hasFDerivAt_integral hx).log hp.ne')).fderiv

end Marginal

section Gibbs

variable {H : E → ℝ} {dH : E → E →L[ℝ] ℝ}

/-- First derivative of a Gibbs weight, before any zero extension. -/
theorem hasFDerivAt_exp_neg {x : E} {S : E →L[ℝ] ℝ}
    (hH : HasFDerivAt H S x) :
    HasFDerivAt (fun z => Real.exp (-H z)) (-Real.exp (-H x) • S) x := by
  convert hH.neg.exp using 1
  ext u
  simp

/-- Second derivative of a Gibbs weight as a bilinear map. Applications may
prove the same formula for a collision-flat zero extension separately. -/
theorem hasFDerivAt_exp_neg_derivative {x : E} {S : E →L[ℝ] ℝ}
    {T : E →L[ℝ] E →L[ℝ] ℝ} (hH : HasFDerivAt H S x)
    (hdH : HasFDerivAt dH T x) :
    HasFDerivAt (fun z => -Real.exp (-H z) • dH z)
      (Real.exp (-H x) • (S.smulRight (dH x) - T)) x := by
  convert (hasFDerivAt_exp_neg hH).neg.smul hdH using 1
  ext u v
  simp
  ring

/-- The score of a positive Gibbs fibre is the centered negative energy force.
The centering is with respect to the explicit conditional law. -/
theorem gibbs_log_normalized_density_apply
    {w : E → A → ℝ} {dw : E → A → E →L[ℝ] ℝ}
    (h : DominatedFDerivOn μ U w dw) {x : E} (hx : x ∈ U)
    (hn : ∀ y, 0 ≤ w x y) (hp : 0 < ∫ y, w x y ∂μ)
    (S : A → E →L[ℝ] ℝ)
    (hforce : ∀ᵐ a ∂μ, dw x a = -w x a • S a)
    {y : A} (hy : 0 < w x y) (hwy : HasFDerivAt (fun z => w z y) (dw x y) x)
    (hyforce : dw x y = -w x y • S y) (u : E) :
    let ρ := AffineFibre.normalizedMeasure μ (fun a => ENNReal.ofReal (w x a))
      (by rw [← ofReal_integral_eq_lintegral_ofReal (h.integrable x hx)
            (Eventually.of_forall hn)]
          exact ENNReal.ofReal_ne_zero_iff.mpr hp)
      (by rw [← ofReal_integral_eq_lintegral_ofReal (h.integrable x hx)
            (Eventually.of_forall hn)]
          exact ENNReal.ofReal_ne_top)
    fderiv ℝ (fun z => Real.log (w z y / ∫ a, w z a ∂μ)) x u =
      -S y u + ∫ a, S a u ∂ρ := by
  dsimp only
  rw [fderiv_log_normalized_density h hx hp hy hwy,
    integral_normalizedMeasure (h.integrable x hx) hn hp]
  simp only [sub_apply, smul_apply]
  rw [ContinuousLinearMap.integral_apply (h.integrable_derivative hx)]
  have hd : (∫ a, dw x a u ∂μ) = -(∫ a, w x a * S a u ∂μ) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [hforce] with a ha
    simp [ha]
  simp only [smul_apply, smul_eq_mul, hyforce] at *
  rw [hd]
  field_simp [hy.ne', hp.ne']
  ring

/-- A dominated density derivative supplies integrability of its force
under the conditional law, including where the weight vanishes. -/
theorem integrable_gibbs_force
    {w : E → A → ℝ} {dw : E → A → E →L[ℝ] ℝ}
    (h : DominatedFDerivOn μ U w dw) {x : E} (hx : x ∈ U)
    (hn : ∀ y, 0 ≤ w x y) (hp : 0 < ∫ y, w x y ∂μ)
    (S : A → E →L[ℝ] ℝ)
    (hforce : ∀ᵐ y ∂μ, dw x y = -w x y • S y) (u : E) :
    Integrable (fun y => S y u)
      (AffineFibre.normalizedMeasure μ (fun y => ENNReal.ofReal (w x y))
        (by rw [← ofReal_integral_eq_lintegral_ofReal (h.integrable x hx)
              (Eventually.of_forall hn)]
            exact ENNReal.ofReal_ne_zero_iff.mpr hp)
        (by rw [← ofReal_integral_eq_lintegral_ofReal (h.integrable x hx)
              (Eventually.of_forall hn)]
            exact ENNReal.ofReal_ne_top)) := by
  apply (integrable_normalizedMeasure_iff (h.integrable x hx) hn hp _).mpr
  apply ((h.integrable_derivative hx).apply_continuousLinearMap u).neg.congr
  filter_upwards [hforce] with y hy
  simp [hy]

/-- Differentiation of an observable expectation: mean derivative minus the
covariance with the energy force. The weighted observable is differentiated
as a whole, so the observable can depend on the parameter. -/
theorem gibbs_expectation_derivative_apply
    {w g : E → A → ℝ} {dw dn : E → A → E →L[ℝ] ℝ}
    (hw : DominatedFDerivOn μ U w dw)
    (hg : DominatedFDerivOn μ U (fun z y => w z y * g z y) dn)
    {x : E} (hx : x ∈ U) (hn : ∀ y, 0 ≤ w x y)
    (hp : 0 < ∫ y, w x y ∂μ) (S Dg : A → E →L[ℝ] ℝ)
    (hforce : ∀ᵐ y ∂μ, dw x y = -w x y • S y)
    (hnum : ∀ᵐ y ∂μ, dn x y = w x y • (Dg y - g x y • S y))
    (u : E) (hDg : Integrable (fun y => w x y * Dg y u) μ) :
    let ρ := AffineFibre.normalizedMeasure μ (fun y => ENNReal.ofReal (w x y))
      (by rw [← ofReal_integral_eq_lintegral_ofReal (hw.integrable x hx)
            (Eventually.of_forall hn)]
          exact ENNReal.ofReal_ne_zero_iff.mpr hp)
      (by rw [← ofReal_integral_eq_lintegral_ofReal (hw.integrable x hx)
            (Eventually.of_forall hn)]
          exact ENNReal.ofReal_ne_top)
    MemLp (g x) 2 ρ → MemLp (fun y => S y u) 2 ρ →
    fderiv ℝ (fun z => (∫ y, w z y * g z y ∂μ) / ∫ y, w z y ∂μ) x u =
      (∫ y, Dg y u ∂ρ) - ProbabilityTheory.covariance (g x) (fun y => S y u) ρ := by
  intro ρ hgu hSu
  have : IsProbabilityMeasure ρ := by
    constructor
    dsimp only [ρ]
    rw [AffineFibre.normalizedMeasure_eq_smul, Measure.smul_apply,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, smul_eq_mul,
      ← ofReal_integral_eq_lintegral_ofReal (hw.integrable x hx) (Eventually.of_forall hn)]
    exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hp)
      ENNReal.ofReal_ne_top
  have hgS : Integrable (fun y => w x y * (g x y * S y u)) μ :=
    (integrable_normalizedMeasure_iff (hw.integrable x hx) hn hp _).mp
      (hgu.integrable_mul hSu)
  have hd : (∫ y, dw x y u ∂μ) = -(∫ y, w x y * S y u ∂μ) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [hforce] with y hy
    simp [hy]
  have hdn : (∫ y, dn x y u ∂μ) =
      (∫ y, w x y * Dg y u ∂μ) - ∫ y, w x y * (g x y * S y u) ∂μ := by
    rw [← integral_sub hDg hgS]
    apply integral_congr_ae
    filter_upwards [hnum] with y hy
    simp [hy, mul_sub]
  have heq : (fun z => (∫ y, w z y * g z y ∂μ) / ∫ y, w z y ∂μ) =
      fun z => (∫ y, w z y ∂μ)⁻¹ • ∫ y, w z y * g z y ∂μ := by
    funext z
    simp [div_eq_mul_inv, mul_comm]
  rw [heq, (hasFDerivAt_normalized_integral hw hg hx hp).fderiv,
    ProbabilityTheory.covariance_eq_sub hgu hSu]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    smul_eq_mul, ContinuousLinearMap.integral_apply (hw.integrable_derivative hx),
    ContinuousLinearMap.integral_apply (hg.integrable_derivative hx)]
  change _ = (∫ y, Dg y u ∂ρ) -
    ((∫ y, g x y * S y u ∂ρ) - (∫ y, g x y ∂ρ) * ∫ y, S y u ∂ρ)
  dsimp only [ρ]
  simp_rw [integral_normalizedMeasure (hw.integrable x hx) hn hp]
  rw [hd, hdn]
  simp only [smul_eq_mul]
  ring

/-- Marginal Hessian equals mean energy Hessian minus force covariance.
This internal fixed-fibre theorem assumes the two density derivative formulas
and their domination. It asserts no physical collision estimate. The energy
may already include inverse temperature and affine compensation. -/
theorem gibbs_marginal_hessian_apply
    {w : E → A → ℝ} {dw : E → A → E →L[ℝ] ℝ}
    {ddw : E → A → E →L[ℝ] E →L[ℝ] ℝ}
    (hU : IsOpen U) (h : DominatedFDerivOn μ U w dw)
    (h' : DominatedFDerivOn μ U dw ddw)
    (hp : ∀ z ∈ U, 0 < ∫ y, w z y ∂μ) {x : E} (hx : x ∈ U)
    (hn : ∀ y, 0 ≤ w x y) (S : A → E →L[ℝ] ℝ)
    (T : A → E →L[ℝ] E →L[ℝ] ℝ)
    (hforce : ∀ᵐ y ∂μ, dw x y = -w x y • S y)
    (hsecond : ∀ᵐ y ∂μ, ddw x y = w x y • ((S y).smulRight (S y) - T y))
    (u v : E) (hT : Integrable (fun y => w x y * T y u v) μ) :
    let ρ := AffineFibre.normalizedMeasure μ (fun y => ENNReal.ofReal (w x y))
      (by rw [← ofReal_integral_eq_lintegral_ofReal (h.integrable x hx)
            (Eventually.of_forall hn)]
          exact ENNReal.ofReal_ne_zero_iff.mpr (hp x hx))
      (by rw [← ofReal_integral_eq_lintegral_ofReal (h.integrable x hx)
            (Eventually.of_forall hn)]
          exact ENNReal.ofReal_ne_top)
    MemLp (fun y => S y u) 2 ρ → MemLp (fun y => S y v) 2 ρ →
    fderiv ℝ (fun z => fderiv ℝ (fun t => -Real.log (∫ y, w t y ∂μ)) z) x u v =
      (∫ y, T y u v ∂ρ) -
        ProbabilityTheory.covariance (fun y => S y u) (fun y => S y v) ρ := by
  intro ρ hSu hSv
  have : IsProbabilityMeasure ρ := by
    constructor
    dsimp only [ρ]
    rw [AffineFibre.normalizedMeasure_eq_smul, Measure.smul_apply,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, smul_eq_mul]
    rw [← ofReal_integral_eq_lintegral_ofReal (h.integrable x hx)
      (Eventually.of_forall hn)]
    exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (hp x hx))
      ENNReal.ofReal_ne_top
  have hSS : Integrable (fun y => w x y * (S y u * S y v)) μ := by
    exact (integrable_normalizedMeasure_iff (h.integrable x hx) hn (hp x hx)
      (fun y => S y u * S y v)).mp (hSu.integrable_mul hSv)
  have hd (a : E) : (∫ y, dw x y a ∂μ) = -(∫ y, w x y * S y a ∂μ) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [hforce] with y hy
    simp [hy]
  have hdd : (∫ y, ddw x y u v ∂μ) =
      (∫ y, w x y * (S y u * S y v) ∂μ) - ∫ y, w x y * T y u v ∂μ := by
    rw [← integral_sub hSS hT]
    apply integral_congr_ae
    filter_upwards [hsecond] with y hy
    simp [hy, mul_sub]
  rw [fderiv_fderiv_neg_log_integral_apply hU h h' hp hx,
    ProbabilityTheory.covariance_eq_sub hSu hSv]
  change _ = (∫ y, T y u v ∂ρ) -
    ((∫ y, S y u * S y v ∂ρ) - (∫ y, S y u ∂ρ) * ∫ y, S y v ∂ρ)
  dsimp only [ρ]
  simp_rw [integral_normalizedMeasure (h.integrable x hx) hn (hp x hx)]
  rw [hd u, hd v, hdd]
  simp only [smul_eq_mul]
  ring

end Gibbs

end DominatedFibre
end Riesz2
