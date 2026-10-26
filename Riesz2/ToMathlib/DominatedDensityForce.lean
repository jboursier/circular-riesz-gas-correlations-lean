/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.DominatedFibreCalculus
public import Riesz2.ToMathlib.NonnegativeDerivativeBound

/-!
# Square integrability of dominated density scores

Nonnegativity of a density and local domination of its first two derivatives
control the square of its logarithmic derivative. This justifies separating
the Hessian and covariance in a marginal Hessian formula.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Riesz2.DominatedFibre

variable {A E : Type*} [MeasurableSpace A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure A} {U : Set E} {w : E → A → ℝ}
  {dw : E → A → E →L[ℝ] ℝ}
  {ddw : E → A → E →L[ℝ] E →L[ℝ] ℝ}

/-- Two locally dominated density derivatives imply integrability of the
weighted square of any directional score. This includes zeros of the weight.
No continuity of the second derivative is needed. -/
theorem integrable_weighted_force_sq
    (h : DominatedFDerivOn μ U w dw) (h' : DominatedFDerivOn μ U dw ddw)
    (hn : ∀ z ∈ U, ∀ y, 0 ≤ w z y) {x : E} (hx : x ∈ U)
    (S : A → E →L[ℝ] ℝ) (hforce : ∀ᵐ y ∂μ, dw x y = -w x y • S y)
    (u : E) : Integrable (fun y => w x y * (S y u) ^ 2) μ := by
  obtain ⟨s, hs, hsU, b, hb, hbound, hd⟩ := h.locally_dominated x hx
  obtain ⟨s', hs', _, b', hb', hbound', hd'⟩ := h'.locally_dominated x hx
  have hline : Continuous (fun t : ℝ => x + t • u) := by fun_prop
  have hev : ∀ᶠ t : ℝ in 𝓝 0, x + t • u ∈ s ∩ s' := by
    have ht := hline.tendsto (0 : ℝ)
    simp only [zero_smul, add_zero] at ht
    exact ht (inter_mem hs hs')
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp hev
  let r := ε / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have htmem (t : ℝ) (ht : t ∈ Icc (-r) r) : x + t • u ∈ s ∩ s' := by
    apply hεs
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact lt_of_le_of_lt (abs_le.mpr ht) (by dsimp [r]; linarith)
  have hmeas : AEStronglyMeasurable (fun y => w x y * (S y u) ^ 2) μ := by
    have hm : AEStronglyMeasurable (fun y => (dw x y u) ^ 2 / w x y) μ :=
      ((((h.integrable_derivative hx).apply_continuousLinearMap u).aestronglyMeasurable.aemeasurable.pow_const 2).div
        (h.integrable x hx).aemeasurable).aestronglyMeasurable
    apply hm.congr
    filter_upwards [hforce] with y hy
    by_cases hw : w x y = 0
    · simp [hw, hy]
    · simp only [hy, smul_apply, smul_eq_mul]
      field_simp
  apply Integrable.mono'
    (((hb'.abs.mul_const (‖u‖ * ‖u‖)).add
      ((hb.abs.mul_const ‖u‖).div_const r)).const_mul 2) hmeas
  change ∀ᵐ y ∂μ, ‖w x y * (S y u) ^ 2‖ ≤
    2 * (|b' y| * (‖u‖ * ‖u‖) + |b y| * ‖u‖ / r)
  filter_upwards [hbound, hd, hbound', hd', hforce] with y hy hyd hy' hyd' hyforce
  have hp : |dw x y u| ≤ |b y| * ‖u‖ := by
    calc
      |dw x y u| ≤ ‖dw x y‖ * ‖u‖ := (dw x y).le_opNorm u
      _ ≤ |b y| * ‖u‖ := mul_le_mul_of_nonneg_right
        ((hy x (mem_of_mem_nhds hs)).trans (le_abs_self _)) (norm_nonneg _)
  have hb2 (t : ℝ) (ht : t ∈ Icc (-r) r) :
      ddw (x + t • u) y u u ≤ |b' y| * (‖u‖ * ‖u‖) := by
    calc
      ddw (x + t • u) y u u ≤ ‖ddw (x + t • u) y u u‖ := le_abs_self _
      _ ≤ ‖ddw (x + t • u) y u‖ * ‖u‖ := (ddw (x + t • u) y u).le_opNorm u
      _ ≤ (‖ddw (x + t • u) y‖ * ‖u‖) * ‖u‖ := by
        gcongr; exact (ddw (x + t • u) y).le_opNorm u
      _ ≤ |b' y| * (‖u‖ * ‖u‖) := by
        rw [← mul_assoc]
        gcongr
        exact (hy' _ (htmem t ht).2).trans (le_abs_self _)
  have hlineD (t : ℝ) : HasDerivAt (fun t : ℝ => x + t • u) u t := by
    simpa using ((hasDerivAt_id t).smul_const u).const_add x
  have hdline (t : ℝ) (ht : t ∈ Icc (-r) r) :
      HasDerivAt (fun t => w (x + t • u) y) (dw (x + t • u) y u) t :=
    HasFDerivAt.comp_hasDerivAt (l := fun z => w z y)
      (f := fun t : ℝ => x + t • u) t (hyd (x + t • u) (htmem t ht).1) (hlineD t)
  have hddline (t : ℝ) (ht : t ∈ Icc (-r) r) :
      HasDerivAt (fun t => dw (x + t • u) y u) (ddw (x + t • u) y u u) t :=
    by
      simpa using (HasFDerivAt.comp_hasDerivAt (l := fun z => dw z y)
        (f := fun t : ℝ => x + t • u) t (hyd' (x + t • u) (htmem t ht).2) (hlineD t)).clm_apply
        (hasDerivAt_const t u)
  have hineq := derivative_sq_le_of_nonnegative_on_interval
    (f := fun t => w (x + t • u) y)
    (g := fun t => dw (x + t • u) y u)
    (h := fun t => ddw (x + t • u) y u u) hr
    (mul_nonneg (abs_nonneg (b' y)) (mul_self_nonneg ‖u‖))
    (fun t ht => hn _ (hsU (htmem t ht).1) y)
    hdline hddline hb2
  simp only [zero_smul, add_zero] at hineq
  have hin : (dw x y u) ^ 2 ≤
      2 * (|b' y| * (‖u‖ * ‖u‖) + |b y| * ‖u‖ / r) * w x y := by
    apply hineq.trans
    gcongr
    exact hn x hx y
  have hw := hn x hx y
  rw [Real.norm_of_nonneg (mul_nonneg hw (sq_nonneg _))]
  by_cases hw0 : w x y = 0
  · simp only [hw0, zero_mul]
    positivity
  · have hpw : 0 < w x y := lt_of_le_of_ne hw (Ne.symm hw0)
    have he : (dw x y u) ^ 2 = w x y * (w x y * (S y u) ^ 2) := by
      simp only [hyforce, smul_apply, smul_eq_mul]
      ring
    rw [he, mul_comm (2 * _) (w x y)] at hin
    exact (mul_le_mul_iff_right₀ hpw).mp hin

/-- Under a positive finite normalizer, the conditional score belongs to L².
Its measurability follows from the integrable first density derivative. -/
theorem memLp_gibbs_force
    (h : DominatedFDerivOn μ U w dw) (h' : DominatedFDerivOn μ U dw ddw)
    (hn : ∀ z ∈ U, ∀ y, 0 ≤ w z y) {x : E} (hx : x ∈ U)
    (hp : 0 < ∫ y, w x y ∂μ) (S : A → E →L[ℝ] ℝ)
    (hforce : ∀ᵐ y ∂μ, dw x y = -w x y • S y) (u : E) :
    MemLp (fun y => S y u) 2
      (AffineFibre.normalizedMeasure μ (fun y => ENNReal.ofReal (w x y))
        (by rw [← ofReal_integral_eq_lintegral_ofReal (h.integrable x hx)
              (Eventually.of_forall (hn x hx))]
            exact ENNReal.ofReal_ne_zero_iff.mpr hp)
        (by rw [← ofReal_integral_eq_lintegral_ofReal (h.integrable x hx)
              (Eventually.of_forall (hn x hx))]
            exact ENNReal.ofReal_ne_top)) := by
  apply (memLp_two_iff_integrable_sq
    (integrable_gibbs_force h hx (hn x hx) hp S hforce u).aestronglyMeasurable).mpr
  exact (integrable_normalizedMeasure_iff (h.integrable x hx) (hn x hx) hp _).mpr
    (integrable_weighted_force_sq h h' hn hx S hforce u)

/-- Two dominated Gibbs density derivatives also give integrability of the
weighted energy Hessian, after the force product has been shown integrable. -/
theorem integrable_weighted_gibbs_hessian
    (h : DominatedFDerivOn μ U w dw) (h' : DominatedFDerivOn μ U dw ddw)
    (hn : ∀ z ∈ U, ∀ y, 0 ≤ w z y) {x : E} (hx : x ∈ U)
    (hp : 0 < ∫ y, w x y ∂μ) (S : A → E →L[ℝ] ℝ)
    (T : A → E →L[ℝ] E →L[ℝ] ℝ)
    (hforce : ∀ᵐ y ∂μ, dw x y = -w x y • S y)
    (hsecond : ∀ᵐ y ∂μ, ddw x y = w x y • ((S y).smulRight (S y) - T y))
    (u v : E) : Integrable (fun y => w x y * T y u v) μ := by
  have hprod := (memLp_gibbs_force h h' hn hx hp S hforce u).integrable_mul
    (memLp_gibbs_force h h' hn hx hp S hforce v)
  have hi := (integrable_normalizedMeasure_iff (h.integrable x hx) (hn x hx) hp _).mp hprod
  apply (hi.sub (((h'.integrable_derivative hx).apply_continuousLinearMap u).apply_continuousLinearMap v)).congr
  filter_upwards [hsecond] with y hy
  change w x y * (S y u * S y v) - ddw x y u v = w x y * T y u v
  simp only [hy, smul_apply, smul_eq_mul, sub_apply, ContinuousLinearMap.smulRight_apply]
  ring

/-- The separated Gibbs marginal Hessian follows from domination alone:
conditional L² forces and the energy-Hessian integrability are conclusions
of the preceding results, rather than additional analytic premises. -/
theorem gibbs_marginal_hessian_apply_of_domination
    (hU : IsOpen U) (h : DominatedFDerivOn μ U w dw)
    (h' : DominatedFDerivOn μ U dw ddw)
    (hn : ∀ z ∈ U, ∀ y, 0 ≤ w z y) (hp : ∀ z ∈ U, 0 < ∫ y, w z y ∂μ)
    {x : E} (hx : x ∈ U) (S : A → E →L[ℝ] ℝ)
    (T : A → E →L[ℝ] E →L[ℝ] ℝ)
    (hforce : ∀ᵐ y ∂μ, dw x y = -w x y • S y)
    (hsecond : ∀ᵐ y ∂μ, ddw x y = w x y • ((S y).smulRight (S y) - T y))
    (u v : E) :
    let ρ := AffineFibre.normalizedMeasure μ (fun y => ENNReal.ofReal (w x y))
      (by rw [← ofReal_integral_eq_lintegral_ofReal (h.integrable x hx)
            (Eventually.of_forall (hn x hx))]
          exact ENNReal.ofReal_ne_zero_iff.mpr (hp x hx))
      (by rw [← ofReal_integral_eq_lintegral_ofReal (h.integrable x hx)
            (Eventually.of_forall (hn x hx))]
          exact ENNReal.ofReal_ne_top)
    fderiv ℝ (fderiv ℝ (fun t => -Real.log (∫ y, w t y ∂μ))) x u v =
      (∫ y, T y u v ∂ρ) -
        ProbabilityTheory.covariance (fun y => S y u) (fun y => S y v) ρ := by
  exact gibbs_marginal_hessian_apply hU h h' hp hx (hn x hx) S T hforce hsecond u v
    (integrable_weighted_gibbs_hessian h h' hn hx (hp x hx) S T hforce hsecond u v)
    (memLp_gibbs_force h h' hn hx (hp x hx) S hforce u)
    (memLp_gibbs_force h h' hn hx (hp x hx) S hforce v)

end Riesz2.DominatedFibre
