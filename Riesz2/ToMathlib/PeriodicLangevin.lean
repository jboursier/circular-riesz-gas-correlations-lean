/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.IntrinsicLangevin
public import Riesz1.ToMathlib.Chamber.PeriodizationIntegral
public import Riesz1.ToMathlib.Chamber.PeriodizationDerivative

/-!
# Local Langevin calculus across a periodic seam

Unfolding a compact test and a periodic weight proves integration by parts
without imposing a zero trace at the cut of a fundamental strip. The potential
is arbitrary and locally smooth on the invariant open domain.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz2.Intrinsic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (σ : Measure E) [σ.IsAddHaarMeasure]
  {v : E} (hv : v ≠ 0) (ℓ : E →L[ℝ] ℝ) (hℓ : ℓ v = 1)
  {U : Set E} (hU : IsOpen U)
  (hUp : ∀ (k : ℤ) x, x + (k : ℝ) • v ∈ U ↔ x ∈ U)
  {V : E → ℝ} (hV : ContDiffOn ℝ ∞ V U)
  (hVp : ∀ (k : ℤ) x, V (x + (k : ℝ) • v) = V x)

include hU hV in
/-- Unnormalized exponential-weight integration by parts with an interior test. -/
theorem exponential_directional_integrationByParts {ψ h : E → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U)
    (hh : ContDiffOn ℝ ∞ h U) (a : E) :
    (∫ x, ψ x * (Real.exp (-V x) * fderiv ℝ h x a) ∂σ) =
      ∫ x, (ψ x * fderiv ℝ V x a - fderiv ℝ ψ x a) *
        (Real.exp (-V x) * h x) ∂σ := by
  have he := Riesz1.WeightedSobolev.integral_weighted_fderiv_of_compact_test
    (μ := σ) hU hψ hψc hψU hh hV.neg.exp a
  have hs : tsupport (fun x => fderiv ℝ (fun y => ψ y * Real.exp (-V y)) x a) ⊆ U :=
    (tsupport_fderiv_apply_subset ℝ a).trans (tsupport_mul_subset_left.trans hψU)
  calc
    _ = ∫ x, (ψ x * Real.exp (-V x)) * fderiv ℝ h x a ∂σ :=
      integral_congr_ae (Eventually.of_forall fun x => by ring)
    _ = -∫ x, h x * fderiv ℝ (fun y => ψ y * Real.exp (-V y)) x a ∂σ := he
    _ = _ := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ U
      · have hdV := (hV.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
        have hdw : DifferentiableAt ℝ (fun y => Real.exp (-V y)) x := hdV.neg.exp
        rw [fderiv_fun_mul (hψ.differentiable (by simp) x) hdw]
        have hdwe : fderiv ℝ (fun y => Real.exp (-V y)) x =
            Real.exp (-V x) • (-fderiv ℝ V x) := hdV.hasFDerivAt.neg.exp.fderiv
        rw [hdwe]
        simp only [add_apply, smul_apply, smul_eq_mul, neg_apply]
        ring
      · have hψ0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hψU h))
        have hdψ := fderiv_of_notMem_tsupport ℝ (fun h => hx (hψU h))
        have hd0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
        simp [hψ0, hdψ, hd0]

include hℓ hU hUp hV hVp in
omit [FiniteDimensional ℝ E] in
/-- Weighted unfolding for an arbitrary locally smooth periodic potential.
The normalized law is defined on the half-open fundamental strip. -/
theorem integral_periodic_test {ψ b : E → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U)
    (hb : ContinuousOn b U) (hbp : ∀ (k : ℤ) x, b (x + (k : ℝ) • v) = b x) :
    let C := U ∩ ℓ ⁻¹' Ico (0 : ℝ) 1
    let μ := (σ.restrict C).tilted (fun x => -V x)
    (∫ x, Riesz1.vectorPeriodize v hv ψ hψc x * b x ∂μ) =
      (∫ x in C, Real.exp (-V x) ∂σ)⁻¹ *
        ∫ x, ψ x * (Real.exp (-V x) * b x) ∂σ := by
  dsimp only
  let P := Riesz1.vectorPeriodize v hv ψ hψc
  let w := fun x => Real.exp (-V x) * b x
  have hp0 (x : E) (hx : x ∉ U) : P x = 0 :=
    Riesz1.vectorPeriodize_eq_zero_of_not_mem hv hψc hUp (subset_closure.trans hψU) hx
  have hi : Integrable (fun x => ψ x * w x) σ :=
    (Riesz1.WeightedSobolev.continuous_cutoff_mul hU hψ hψU
      (hV.neg.exp.continuousOn.mul hb)).integrable_of_hasCompactSupport hψc.mul_right
  have hwp (k : ℤ) (x : E) : w (x + (k : ℝ) • v) = w x := by
    dsimp only [w]
    rw [hVp, hbp]
  rw [integral_tilted]
  simp only [smul_eq_mul]
  have he : (fun x => Real.exp (-V x) / (∫ y in U ∩ ℓ ⁻¹' Ico 0 1, Real.exp (-V y) ∂σ) *
      (P x * b x)) = fun x =>
      (∫ y in U ∩ ℓ ⁻¹' Ico 0 1, Real.exp (-V y) ∂σ)⁻¹ * (P x * w x) := by
    ext x
    dsimp only [w]
    rw [div_eq_mul_inv]
    ring
  rw [he, integral_const_mul]
  congr 1
  rw [← Measure.restrict_restrict hU.measurableSet]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hp0 x hx])]
  exact Riesz1.integral_vectorPeriodize_mul_periodic hv ℓ hℓ hψc hwp hi

include hℓ hU hUp hV hVp in
/-- Local integration by parts after periodization. A compact test may cross
the cut: only the actual boundary of the invariant domain is excluded. -/
theorem periodized_integrationByParts {ψ h : E → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U)
    (hh : ContDiffOn ℝ ∞ h U) (hhp : ∀ (k : ℤ) x, h (x + (k : ℝ) • v) = h x)
    (a : E) :
    let μ := (σ.restrict (U ∩ ℓ ⁻¹' Ico (0 : ℝ) 1)).tilted (fun x => -V x)
    let P := Riesz1.vectorPeriodize v hv ψ hψc
    (∫ x, P x * fderiv ℝ h x a ∂μ) =
      ∫ x, h x * (P x * fderiv ℝ V x a - fderiv ℝ P x a) ∂μ := by
  dsimp only
  let P := Riesz1.vectorPeriodize v hv ψ hψc
  let q := fun x => ψ x * fderiv ℝ V x a - fderiv ℝ ψ x a
  have hqc : HasCompactSupport q := hψc.mul_right.sub (hψc.fderiv_apply ℝ a)
  have hqU : tsupport q ⊆ U := by
    apply (show tsupport q ⊆ tsupport ψ from ?_).trans hψU
    apply closure_minimal _ (isClosed_tsupport ψ)
    intro x hx
    by_contra hxs
    exact hx (by simp [q, image_eq_zero_of_notMem_tsupport hxs, fderiv_of_notMem_tsupport ℝ hxs])
  have hq : Continuous q :=
    (Riesz1.WeightedSobolev.continuous_cutoff_mul hU hψ.continuous hψU
      ((hV.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const)).sub
      ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hdVp (k : ℤ) (x : E) : fderiv ℝ V (x + (k : ℝ) • v) = fderiv ℝ V x :=
    Riesz1.fderiv_periodic_vector hVp k x
  have hdhp (k : ℤ) (x : E) : fderiv ℝ h (x + (k : ℝ) • v) a = fderiv ℝ h x a :=
    congrArg (fun A : E →L[ℝ] ℝ => A a) (Riesz1.fderiv_periodic_vector hhp k x)
  have hPq (x : E) : Riesz1.vectorPeriodize v hv q hqc x =
      P x * fderiv ℝ V x a - fderiv ℝ P x a := by
    rw [Riesz1.fderiv_vectorPeriodize_apply hv (hψ.differentiable (by simp)) hψc]
    change (∑ᶠ k : ℤ, q (x + (k : ℝ) • v)) = _
    simp only [q, hdVp]
    have hfin : Function.HasFiniteSupport
        (fun k : ℤ => ψ (x + (k : ℝ) • v) * fderiv ℝ V x a) := by
      simpa only [Pi.mul_apply, hdVp] using
        (Riesz1.vectorPeriodize_finite_support hv
          (hψc.mul_right : HasCompactSupport (fun y => ψ y * fderiv ℝ V y a)) x)
    rw [finsum_sub_distrib hfin
      (Riesz1.vectorPeriodize_finite_support hv (hψc.fderiv_apply ℝ a) x), ← finsum_mul]
    rfl
  have hl := integral_periodic_test σ hv ℓ hℓ hU hUp hV hVp hψ.continuous hψc hψU
    ((hh.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const) hdhp
  have hr := integral_periodic_test σ hv ℓ hℓ hU hUp hV hVp hq hqc hqU hh.continuousOn hhp
  calc
    _ = _ := hl
    _ = _ := congrArg (fun r : ℝ =>
      (∫ x in U ∩ ℓ ⁻¹' Ico (0 : ℝ) 1, Real.exp (-V x) ∂σ)⁻¹ * r)
        (exponential_directional_integrationByParts σ hU hV hψ hψc hψU hh a)
    _ = _ := hr.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hPq]
      ring

end Riesz2.Intrinsic
