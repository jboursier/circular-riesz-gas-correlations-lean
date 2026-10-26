/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.FundamentalSolution
public import Riesz1.Kernel.FundamentalSeries
public import Riesz1.Frozen.RieszKernel
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Basic.Real.Sign

/-!
# Identification of the companion periodic Riesz kernel

Library bridges for the companion kernel identification and the companion kernel representation.
The kernel, its representative, its Fourier normalization and its zeta function are
literally those of Riesz 1. The additional signed derivative formula follows from
the library's positive-half-line formula, reflection, and convergent derivative series.
All pointwise lattice formulas exclude collisions.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace Riesz2

/-- The coefficient in the signed image formula (the companion kernel identification). -/
theorem prod_neg_sub_eq (s : ℝ) (p : ℕ) :
    (∏ j ∈ Finset.range p, (-s - (j : ℝ))) =
      (-1 : ℝ) ^ p * ∏ j ∈ Finset.range p, (s + (j : ℝ)) := by
  simp_rw [show ∀ j : ℕ, -s - (j : ℝ) = -(s + (j : ℝ)) by intro j; ring]
  rw [Finset.prod_neg, Finset.card_range]

/-- Signed version of the library's absolute-power derivative formula, used in
the companion kernel identification. This holds for every real exponent and every derivative order. -/
theorem iteratedDeriv_abs_rpow_signed (s : ℝ) (p : ℕ) {x : ℝ} (hx : x ≠ 0) :
    iteratedDeriv p (fun y : ℝ => |y| ^ (-s)) x =
      ((-1 : ℝ) ^ p * ∏ j ∈ Finset.range p, (s + (j : ℝ))) *
        (Real.sign x ^ p / |x| ^ (s + (p : ℝ))) := by
  have hpow : |x| ^ (-s - (p : ℝ)) = (|x| ^ (s + (p : ℝ)))⁻¹ := by
    rw [show -s - (p : ℝ) = -(s + (p : ℝ)) by ring, Real.rpow_neg (abs_nonneg x)]
  rcases lt_or_gt_of_ne hx with hn | hp
  · have href := iteratedDeriv_comp_neg p (fun y : ℝ => |y| ^ (-s)) x
    simp only [abs_neg] at href
    rw [href, smul_eq_mul,
      Riesz1.iteratedDeriv_abs_rpow_pos s p (neg_pos.mpr hn),
      prod_neg_sub_eq, ← abs_of_neg hn, hpow, Real.sign_of_neg hn]
    ring
  · rw [Riesz1.iteratedDeriv_abs_rpow_pos s p hp, prod_neg_sub_eq,
      Real.sign_of_pos hp, one_pow, abs_of_pos hp, div_eq_mul_inv, one_mul]
    congr 1
    simpa only [abs_of_pos hp] using hpow

/-- Closed derivative of one image term (the companion kernel identification). -/
theorem iteratedDeriv_abs_rpow_add_int (s : ℝ) (p : ℕ) (k : ℤ) {x : ℝ}
    (hx : (x : UnitAddCircle) ≠ 0) :
    iteratedDeriv p (fun y : ℝ => |(k : ℝ) + y| ^ (-s)) x =
      ((-1 : ℝ) ^ p * ∏ j ∈ Finset.range p, (s + (j : ℝ))) *
        (Real.sign (x + k) ^ p / |x + k| ^ (s + (p : ℝ))) := by
  have hfun : (fun y : ℝ => |(k : ℝ) + y| ^ (-s)) =
      fun y : ℝ => (fun t : ℝ => |t| ^ (-s)) (y + k) := by
    funext y
    rw [add_comm]
  rw [hfun, congrFun (iteratedDeriv_comp_add_const p
    (fun t : ℝ => |t| ^ (-s)) (k : ℝ)) x]
  exact iteratedDeriv_abs_rpow_signed s p
    (by simpa only [add_comm] using Riesz1.add_int_ne_zero_of_nonInt hx k)

/-- Absolute convergence of the closed derivative image series
(the companion kernel identification, also used by Lemma 2.3). -/
theorem summable_norm_kernel_images (s : Riesz1.RieszExponent) {p : ℕ} (hp : 1 ≤ p)
    {x : ℝ} (hx : (x : UnitAddCircle) ≠ 0) :
    Summable (fun k : ℤ =>
      ‖Real.sign (x + k) ^ p / |x + k| ^ (s.val + (p : ℝ))‖) := by
  have he : -s.val - (p : ℝ) < -1 := by
    have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith [s.property.1]
  refine (Riesz1.summable_abs_add_int_rpow hx he).congr fun k => ?_
  have hn : x + (k : ℝ) ≠ 0 := by
    simpa only [add_comm] using Riesz1.add_int_ne_zero_of_nonInt hx k
  have hsign : |Real.sign (x + k)| = 1 := by
    rcases Real.sign_apply_eq_of_ne_zero _ hn with h | h <;> simp [h]
  rw [Real.norm_eq_abs, abs_div, abs_pow, hsign,
    one_pow, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _),
    one_div, ← Real.rpow_neg (abs_nonneg _)]
  rw [add_comm (k : ℝ) x,
    show -s.val - (p : ℝ) = -(s.val + (p : ℝ)) by ring]

/-- The closed all-order derivative formula of the companion kernel identification.
It identifies the imported derivative series without differentiating an infinite sum anew. -/
theorem iteratedDeriv_rieszRepresentative (s : Riesz1.RieszExponent) {p : ℕ} (hp : 1 ≤ p)
    {x : ℝ} (hx : (x : UnitAddCircle) ≠ 0) :
    iteratedDeriv p (fun y : ℝ => Riesz1.rieszRepresentative s y) x =
      ((-1 : ℝ) ^ p * ∏ j ∈ Finset.range p, (s.val + (j : ℝ))) *
        ∑' k : ℤ, Real.sign (x + k) ^ p / |x + k| ^ (s.val + (p : ℝ)) := by
  change iteratedDeriv p (Riesz1.hurwitzKernel s.val) x = _
  rw [Riesz1.iteratedDeriv_hurwitzKernel_eq_tsum s.val s.property.1 s.property.2 hp x hx,
    ← tsum_mul_left]
  exact tsum_congr fun k => iteratedDeriv_abs_rpow_add_int s.val p k hx

/-- The signed image series in the companion kernel identification converges locally uniformly
as a sum over arbitrary finite subsets of the integers, hence in particular in symmetric order. -/
theorem hasSumLocallyUniformlyOn_kernel_images (s : Riesz1.RieszExponent) {p : ℕ}
    (hp : 1 ≤ p) :
    HasSumLocallyUniformlyOn
      (fun (k : ℤ) (x : ℝ) => Real.sign (x + k) ^ p / |x + k| ^ (s.val + (p : ℝ)))
      (fun x : ℝ => ∑' k : ℤ, Real.sign (x + k) ^ p / |x + k| ^ (s.val + (p : ℝ)))
      {x : ℝ | (x : UnitAddCircle) ≠ 0} := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have he : -s.val - (p : ℝ) < -1 := by linarith [s.property.1]
  refine hasSumLocallyUniformlyOn_of_of_forall_exists_nhds fun x hx => ?_
  have hδ : 0 < |x - round x| / 2 := by linarith [Riesz1.abs_sub_round_pos hx]
  refine ⟨Metric.ball x (|x - round x| / 2),
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hδ),
    HasSumUniformlyOn.of_norm_le_summable
      (Riesz1.summable_half_abs_add_int_rpow hx he) ?_⟩
  intro k z hz
  rw [Metric.mem_ball, Real.dist_eq] at hz
  have hzU := Riesz1.nonInt_of_dist_lt hx hz
  have hn : z + (k : ℝ) ≠ 0 := by
    simpa only [add_comm] using Riesz1.add_int_ne_zero_of_nonInt hzU k
  have hsign : |Real.sign (z + k)| = 1 := by
    rcases Real.sign_apply_eq_of_ne_zero _ hn with h | h <;> simp [h]
  rw [Real.norm_eq_abs, abs_div, abs_pow, hsign, one_pow,
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _), one_div,
    ← Real.rpow_neg (abs_nonneg _), show -(s.val + (p : ℝ)) = -s.val - p by ring,
    add_comm z (k : ℝ)]
  apply Real.rpow_le_rpow_of_nonpos _ (Riesz1.half_abs_add_int_le_of_dist_lt hz k)
    (by linarith)
  have := Riesz1.abs_sub_round_le_abs_add_int x k
  linarith

private theorem locallyUniformlyOn_of_derivatives {ι : Type*} {l : Filter ι}
    [NeBot l]
    {F F' : ι → ℝ → ℝ} {g g' : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hF' : TendstoLocallyUniformlyOn F' g' l U)
    (hF : ∀ n x, x ∈ U → HasDerivAt (F n) (F' n x) x)
    (hg : ∀ x ∈ U, Tendsto (fun n => F n x) l (𝓝 (g x))) :
    TendstoLocallyUniformlyOn F g l U := by
  rw [tendstoLocallyUniformlyOn_iff_filter]
  intro x hx
  rw [hU.nhdsWithin_eq hx]
  have hD : TendstoUniformlyOnFilter
      (fun n z => (1 : ℝ →L[ℝ] ℝ).smulRight (F' n z))
      (fun z => (1 : ℝ →L[ℝ] ℝ).smulRight (g' z)) l (𝓝 x) :=
    (ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1).uniformContinuous.comp_tendstoUniformlyOnFilter
      (by simpa only [hU.nhdsWithin_eq hx] using
        (tendstoLocallyUniformlyOn_iff_filter.mp hF') x hx)
  have hD' : ∀ᶠ nz : ι × ℝ in l ×ˢ 𝓝 x,
      HasFDerivAt (F nz.1) ((1 : ℝ →L[ℝ] ℝ).smulRight (F' nz.1 nz.2)) nz.2 := by
    exact eventually_prod_iff.mpr ⟨fun _ => True, Eventually.of_forall (fun _ => trivial),
      (· ∈ U), hU.mem_nhds hx, fun {_} _ {_} hy => (hF _ _ hy).hasFDerivAt⟩
  exact (uniformCauchySeqOnFilter_of_fderiv hD.uniformCauchySeqOnFilter hD'
    (hg x hx).cauchy_map).tendstoUniformlyOnFilter_of_tendsto
      (Filter.eventually_of_mem (hU.mem_nhds hx) fun y hy => hg y hy)

/-- Locally uniform convergence of the undifferentiated renormalized lattice sums,
as required by the companion kernel identification. Derivative convergence and pointwise convergence
are imported from Riesz 1. The uniform Cauchy theorem for primitives joins them. -/
theorem tendstoLocallyUniformlyOn_rieszPartialSum (s : Riesz1.RieszExponent) :
    TendstoLocallyUniformlyOn
      (fun (M : ℕ) (x : ℝ) =>
        (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |(k : ℝ) + x| ^ (-s.val)) -
          2 * (M : ℝ) ^ (1 - s.val) / (1 - s.val))
      (fun x : ℝ => Riesz1.rieszRepresentative s x) atTop
      {x : ℝ | (x : UnitAddCircle) ≠ 0} := by
  apply locallyUniformlyOn_of_derivatives Riesz1.isOpen_nonInt
    (Riesz1.tendstoLocallyUniformlyOn_partialSum_iteratedDeriv
      s.val s.property.1 s.property.2 (j := 1) le_rfl)
  · intro M x hx
    have h : DifferentiableAt ℝ (fun y : ℝ =>
        (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |(k : ℝ) + y| ^ (-s.val)) -
          2 * (M : ℝ) ^ (1 - s.val) / (1 - s.val)) x := by
      apply DifferentiableAt.sub_const
      apply DifferentiableAt.fun_sum
      intro k _
      exact ((Riesz1.contDiffAt_abs_rpow s.val
        (Riesz1.add_int_ne_zero_of_nonInt hx k)).comp x
          (contDiffAt_const.add contDiffAt_id)).differentiableAt (by simp)
    simpa only [iteratedDeriv_one] using h.hasDerivAt
  · exact (Riesz1.fundamental_series s).1

/-- The real finite-part identity for all positive Hurwitz arguments in
the companion kernel representation. The complex identity is the imported `fundamental_zeta`. -/
theorem hurwitzZetaPos_finitePart (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (x : ℝ) (hx : 0 < x) :
    Tendsto (fun M : ℕ =>
      (∑ n ∈ Finset.range (M + 1), ((n : ℝ) + x) ^ (-t)) -
        (M : ℝ) ^ (1 - t) / (1 - t)) atTop
      (𝓝 (Riesz1.hurwitzZetaPos (t : ℂ) x).re) := by
  have htC : (t : ℂ) ≠ 1 := by exact_mod_cast ht1.ne
  have h := (Complex.continuous_re.tendsto _).comp
    ((Riesz1.fundamental_zeta.1 x hx (t : ℂ) ht0 htC).1)
  apply h.congr
  intro M
  change ((∑ n ∈ Finset.range (M + 1), ((n : ℂ) + x) ^ (-(t : ℂ))) -
    (M : ℂ) ^ (1 - (t : ℂ)) / (1 - (t : ℂ))).re = _
  have hsum : (∑ n ∈ Finset.range (M + 1), ((n : ℂ) + x) ^ (-(t : ℂ))) =
      ((∑ n ∈ Finset.range (M + 1), ((n : ℝ) + x) ^ (-t) : ℝ) : ℂ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro n _
    rw [Complex.ofReal_cpow (by positivity : 0 ≤ (n : ℝ) + x)]
    simp only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_neg]
  rw [hsum, Complex.sub_re, Complex.ofReal_re]
  congr 1
  have hc : ((M : ℂ) ^ (1 - (t : ℂ)) / (1 - (t : ℂ))) =
      (((M : ℝ) ^ (1 - t) / (1 - t) : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg M)]
    push_cast
    rfl
  rw [hc, Complex.ofReal_re]

/-- Positive second derivative, the convexity consequence needed by Lemma 2.3. -/
theorem iteratedDeriv_two_rieszRepresentative_pos (s : Riesz1.RieszExponent)
    {x : ℝ} (hx : (x : UnitAddCircle) ≠ 0) :
    0 < iteratedDeriv 2 (fun y : ℝ => Riesz1.rieszRepresentative s y) x := by
  have h := (Riesz1.fundamental_series s).2.2.2.2.2.2.2.2.2.1 x hx
  rw [h.1]
  exact h.2

/-- Strict convexity on `(0,1)`, for consumers of the companion kernel identification and Lemma 2.3.
This is the library's strict convexity theorem specialized to its zero-th unit interval. -/
theorem strictConvexOn_rieszRepresentative (s : Riesz1.RieszExponent) :
    StrictConvexOn ℝ (Ioo (0 : ℝ) 1) (fun x : ℝ => Riesz1.rieszRepresentative s x) := by
  change StrictConvexOn ℝ (Ioo (0 : ℝ) 1) (Riesz1.hurwitzKernel s.val)
  simpa only [Int.cast_zero, zero_add] using
    Riesz1.strictConvexOn_hurwitzKernel s.val s.property.1 s.property.2 0

/-- Identification of the companion kernel.
The representative is the literal Riesz 1 object. The image series is absolutely
convergent and locally uniformly convergent over arbitrary finite index sets. -/
theorem companionKernelIdentification (s : Riesz1.RieszExponent) :
    ContDiffOn ℝ ∞ (fun x : ℝ => Riesz1.rieszRepresentative s x)
      {x : ℝ | (x : UnitAddCircle) ≠ 0} ∧
    Function.Even (fun x : ℝ => Riesz1.rieszRepresentative s x) ∧
    Function.Periodic (fun x : ℝ => Riesz1.rieszRepresentative s x) 1 ∧
    TendstoLocallyUniformlyOn
      (fun (M : ℕ) (x : ℝ) =>
        (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |(k : ℝ) + x| ^ (-s.val)) -
          2 * (M : ℝ) ^ (1 - s.val) / (1 - s.val))
      (fun x : ℝ => Riesz1.rieszRepresentative s x) atTop
      {x : ℝ | (x : UnitAddCircle) ≠ 0} ∧
    Integrable (fun x : UnitAddCircle => Riesz1.rieszRepresentative s x) ∧
    (∫ x : UnitAddCircle, Riesz1.rieszRepresentative s x) = 0 ∧
    (∃ B : ℝ, ∀ x : ℝ, (x : UnitAddCircle) ≠ 0 →
      B ≤ Riesz1.rieszRepresentative s x) ∧
    Tendsto (fun x : ℝ => Riesz1.rieszRepresentative s x) (𝓝[≠] 0) atTop ∧
    (∀ k : ℤ, fourierCoeff (fun x : UnitAddCircle =>
        (Riesz1.rieszRepresentative s x : ℂ)) k =
      if k = 0 then 0 else
        ((Riesz1.rieszConstant s * (2 * Real.pi * |(k : ℝ)|) ^ (s.val - 1) : ℝ) : ℂ)) ∧
    (∀ k : ℤ, Riesz1.fractionalLaplacianCoeffs Riesz1.unitLength ((1 - s.val) / 2)
        (fun j : ℤ => fourierCoeff (fun x : UnitAddCircle =>
          (Riesz1.rieszRepresentative s x : ℂ)) j) k =
      (Riesz1.rieszConstant s : ℂ) * ((1 : ℂ) - if k = 0 then 1 else 0)) ∧
    (∀ p : ℕ, 1 ≤ p →
      (∀ x : ℝ, (x : UnitAddCircle) ≠ 0 →
        iteratedDeriv p (fun y : ℝ => Riesz1.rieszRepresentative s y) x =
          ((-1 : ℝ) ^ p * ∏ j ∈ Finset.range p, (s.val + (j : ℝ))) *
            ∑' k : ℤ, Real.sign (x + k) ^ p / |x + k| ^ (s.val + (p : ℝ))) ∧
      (∀ x : ℝ, (x : UnitAddCircle) ≠ 0 → Summable (fun k : ℤ =>
        ‖Real.sign (x + k) ^ p / |x + k| ^ (s.val + (p : ℝ))‖)) ∧
      HasSumLocallyUniformlyOn
        (fun (k : ℤ) (x : ℝ) => Real.sign (x + k) ^ p / |x + k| ^ (s.val + (p : ℝ)))
        (fun x : ℝ => ∑' k : ℤ, Real.sign (x + k) ^ p / |x + k| ^ (s.val + (p : ℝ)))
        {x : ℝ | (x : UnitAddCircle) ≠ 0}) ∧
    (∀ x : {x : UnitAddCircle // x ≠ 0},
      Riesz1.rieszKernel s x = Riesz1.rieszRepresentative s x.val) := by
  obtain ⟨_, hsmooth, heven, hperiodic, _, hint, hmean, _, _, _, _, hlower, hcollision⟩ :=
    Riesz1.fundamental_series s
  exact ⟨hsmooth, heven, hperiodic, tendstoLocallyUniformlyOn_rieszPartialSum s,
    hint, hmean, hlower, hcollision, (Riesz1.fundamental s).1,
    (Riesz1.fundamental s).2.1, fun _ hp =>
      ⟨fun _ hx => iteratedDeriv_rieszRepresentative s hp hx,
        fun _ hx => summable_norm_kernel_images s hp hx,
        hasSumLocallyUniformlyOn_kernel_images s hp⟩, fun _ => rfl⟩

/-- The companion finite-part formula and real representative. Fourier coefficients specify the mean-zero distribution.
Pointwise values use its real representative off the integers. -/
theorem companionFundamentalRepresentation (s : Riesz1.RieszExponent) :
    (∀ k : ℤ, fourierCoeff (fun x : UnitAddCircle =>
        (Riesz1.rieszRepresentative s x : ℂ)) k =
      if k = 0 then 0 else
        ((Riesz1.rieszConstant s * (2 * Real.pi * |(k : ℝ)|) ^ (s.val - 1) : ℝ) : ℂ)) ∧
    Integrable (fun x : UnitAddCircle => Riesz1.rieszRepresentative s x) ∧
    ContDiffOn ℝ ∞ (fun x : ℝ => Riesz1.rieszRepresentative s x)
      {x : ℝ | (x : UnitAddCircle) ≠ 0} ∧
    Function.Even (fun x : ℝ => Riesz1.rieszRepresentative s x) ∧
    Function.Periodic (fun x : ℝ => Riesz1.rieszRepresentative s x) 1 ∧
    (∀ x : ℝ, 0 < x → x < 1 →
      Riesz1.rieszRepresentative s x = (Riesz1.hurwitzZetaPos (s.val : ℂ) x).re +
        (Riesz1.hurwitzZetaPos (s.val : ℂ) (1 - x)).re) ∧
    (∀ x : ℝ, (x : UnitAddCircle) ≠ 0 →
      Tendsto (fun M : ℕ =>
        (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |(k : ℝ) + x| ^ (-s.val)) -
          2 * (M : ℝ) ^ (1 - s.val) / (1 - s.val)) atTop
        (𝓝 (Riesz1.rieszRepresentative s x))) ∧
    (∫ x : UnitAddCircle, Riesz1.rieszRepresentative s x) = 0 ∧
    (∀ p : ℕ, 1 ≤ p → TendstoLocallyUniformlyOn
      (fun (M : ℕ) (x : ℝ) => iteratedDeriv p (fun y : ℝ =>
        (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |(k : ℝ) + y| ^ (-s.val)) -
          2 * (M : ℝ) ^ (1 - s.val) / (1 - s.val)) x)
      (iteratedDeriv p (fun x : ℝ => Riesz1.rieszRepresentative s x)) atTop
      {x : ℝ | (x : UnitAddCircle) ≠ 0}) ∧
    (∀ t : ℝ, 0 < t → t < 1 → ∀ x : ℝ, 0 < x →
      Tendsto (fun M : ℕ =>
        (∑ n ∈ Finset.range (M + 1), ((n : ℝ) + x) ^ (-t)) -
          (M : ℝ) ^ (1 - t) / (1 - t)) atTop
        (𝓝 (Riesz1.hurwitzZetaPos (t : ℂ) x).re)) := by
  obtain ⟨hlimit, hsmooth, heven, hperiodic, _, hint, hmean, _, hderiv, _⟩ :=
    Riesz1.fundamental_series s
  exact ⟨(Riesz1.fundamental s).1, hint, hsmooth, heven, hperiodic,
    (Riesz1.fundamental s).2.2.2, hlimit, hmean, hderiv, hurwitzZetaPos_finitePart⟩

end Riesz2
