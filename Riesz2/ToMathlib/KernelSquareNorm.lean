/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.GoodSetL2Comparison
public import Riesz1.ToMathlib.LipschitzExpectationL2
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.MeasurableIntegral
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Second moments over an explicit probability kernel

The square root of the conditional second moment has the same second norm
as the original bounded observable. A first-plus-second moment bound for
a nonnegative error controls the second norm of its square root plus itself.
All real integrals used below are proved integrable before estimating them.
-/

public section
noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Riesz2.KernelSquareNorm

variable {B X : Type*} [MeasurableSpace B] [MeasurableSpace X]

/-- The conditional second moment of a bounded measurable observable is
integrable, and its integral is the unconditional second moment. -/
theorem integral_square (μ : Measure B) [IsProbabilityMeasure μ]
    (κ : Kernel B X) [IsMarkovKernel κ] {f : X → ℝ} (hf : Measurable f)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |f x| ≤ M) :
    Integrable (fun b => ∫ x, f x ^ 2 ∂κ b) μ ∧
      (∫ b, ∫ x, f x ^ 2 ∂κ b ∂μ) = ∫ x, f x ^ 2 ∂(κ ∘ₘ μ) := by
  have hi : Integrable (fun x => f x ^ 2) (κ ∘ₘ μ) :=
    (integrable_const (M ^ 2)).mono' (hf.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_sq]
        nlinarith [hb x, abs_nonneg (f x), sq_abs (f x)])
  rw [Measure.comp_eq_comp_const_apply] at hi ⊢
  exact ⟨hi.integral_comp, (Kernel.integral_comp hi).symm⟩

/-- The square root of the conditional second moment is an L²
function. Its real second norm is exactly the unconditional second norm. -/
theorem conditional_norm (μ : Measure B) [IsProbabilityMeasure μ]
    (κ : Kernel B X) [IsMarkovKernel κ] {f : X → ℝ} (hf : Measurable f)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |f x| ≤ M) :
    MemLp (fun b => Real.sqrt (∫ x, f x ^ 2 ∂κ b)) 2 μ ∧
      (eLpNorm (fun b => Real.sqrt (∫ x, f x ^ 2 ∂κ b)) 2 μ).toReal =
        (eLpNorm f 2 (κ ∘ₘ μ)).toReal := by
  have hmeas : Measurable (fun b => ∫ x, f x ^ 2 ∂κ b) :=
    ((hf.pow_const 2).stronglyMeasurable.comp_measurable measurable_snd).integral_kernel_prod_right'.measurable
  have hs : ∀ b, Real.sqrt (∫ x, f x ^ 2 ∂κ b) ^ 2 = ∫ x, f x ^ 2 ∂κ b :=
    fun b => Real.sq_sqrt (integral_nonneg fun x => sq_nonneg (f x))
  have hi := integral_square μ κ hf hM hb
  have hF : MemLp (fun b => Real.sqrt (∫ x, f x ^ 2 ∂κ b)) 2 μ :=
    (memLp_two_iff_integrable_sq hmeas.sqrt.aestronglyMeasurable).mpr
      (by simpa only [hs] using hi.1)
  have hf2 : MemLp f 2 (κ ∘ₘ μ) := MemLp.of_bound hf.aestronglyMeasurable M
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb x)
  refine ⟨hF, ?_⟩
  rw [Riesz1.eLpNorm_two_toReal_eq_sqrt_integral_sq hF,
    Riesz1.eLpNorm_two_toReal_eq_sqrt_integral_sq hf2]
  simp_rw [hs]
  rw [hi.2]

/-- Essential bounds on a good event and a global bound control the
integrated conditional source norm, with the square root of the actual
exceptional probability. No conditional rare-event estimate is assumed. -/
theorem conditional_norm_good_set (μ : Measure B) [IsProbabilityMeasure μ]
    (κ : Kernel B X) [IsMarkovKernel κ] {f : X → ℝ} (hf : Measurable f)
    {G : Set X} (hG : MeasurableSet G) {A M : ℝ} (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hgood : ∀ᵐ x ∂(κ ∘ₘ μ).restrict G, |f x| ≤ A)
    (hb : ∀ x, |f x| ≤ M) :
    (eLpNorm (fun b => Real.sqrt (∫ x, f x ^ 2 ∂κ b)) 2 μ).toReal ≤
      A + M * Real.sqrt ((κ ∘ₘ μ).real Gᶜ) := by
  rw [(conditional_norm μ κ hf hM hb).2]
  have hf2 : MemLp f 2 (κ ∘ₘ μ) := MemLp.of_bound hf.aestronglyMeasurable M
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb x)
  have he := hf2.coeFn_toLp
  have hg : ∀ᵐ x ∂(κ ∘ₘ μ).restrict G, |hf2.toLp f x| ≤ A := by
    filter_upwards [ae_restrict_of_ae he, hgood] with x hx hg
    rwa [hx]
  have hb' : ∀ᵐ x ∂(κ ∘ₘ μ), |hf2.toLp f x| ≤ M := by
    filter_upwards [he] with x hx
    rw [hx]
    exact hb x
  have hn := GoodSetL2Comparison.source_norm_le (hf2.toLp f) hG hA hM hg hb'
  simpa only [Lp.norm_toLp] using hn

/-- A nonnegative error with integrable first and second moments has
`sqrt e + e` in L², with its norm controlled by those same moments. -/
theorem sqrt_add_self (μ : Measure B) {e : B → ℝ} (he : Measurable e)
    (he0 : ∀ b, 0 ≤ e b) {R : ℝ} (hR : 0 ≤ R)
    (hmoment : (∫⁻ b, ENNReal.ofReal (e b + e b ^ 2) ∂μ) ≤ ENNReal.ofReal R) :
    MemLp (fun b => Real.sqrt (e b) + e b) 2 μ ∧
      (eLpNorm (fun b => Real.sqrt (e b) + e b) 2 μ).toReal ≤
        2 * Real.sqrt R := by
  have hm0 : ∀ᵐ b ∂μ, 0 ≤ e b + e b ^ 2 :=
    ae_of_all _ fun b => add_nonneg (he0 b) (sq_nonneg _)
  have hi : Integrable (fun b => e b + e b ^ 2) μ :=
    ⟨(he.add (he.pow_const 2)).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hm0).mpr (hmoment.trans_lt ENNReal.ofReal_lt_top)⟩
  have hbound (b) : (Real.sqrt (e b) + e b) ^ 2 ≤ 4 * (e b + e b ^ 2) := by
    nlinarith [Real.sq_sqrt (he0 b), sq_nonneg (Real.sqrt (e b) - e b)]
  have hs := (hi.const_mul 4).mono' ((he.sqrt.add he).pow_const 2).aestronglyMeasurable
    (ae_of_all _ fun b => by simpa only [Real.norm_eq_abs, abs_sq, Pi.add_apply] using hbound b)
  have hmem : MemLp (fun b => Real.sqrt (e b) + e b) 2 μ :=
    (memLp_two_iff_integrable_sq (he.sqrt.add he).aestronglyMeasurable).mpr hs
  refine ⟨hmem, ?_⟩
  have hreal : (∫ b, e b + e b ^ 2 ∂μ) ≤ R := by
    apply (ENNReal.ofReal_le_ofReal_iff hR).mp
    rwa [ofReal_integral_eq_lintegral_ofReal hi hm0]
  rw [Riesz1.eLpNorm_two_toReal_eq_sqrt_integral_sq hmem]
  have hb := (integral_mono hs (hi.const_mul 4) hbound).trans
    (by rw [integral_const_mul]; linarith :
      (∫ b, 4 * (e b + e b ^ 2) ∂μ) ≤ 4 * R)
  change (∫ b, (Real.sqrt (e b) + e b) ^ 2 ∂μ) ≤ 4 * R at hb
  have hn := integral_nonneg (μ := μ) (fun b => sq_nonneg (Real.sqrt (e b) + e b))
  nlinarith [Real.sq_sqrt hR, Real.sq_sqrt hn,
    Real.sqrt_nonneg R, Real.sqrt_nonneg (∫ b, (Real.sqrt (e b) + e b) ^ 2 ∂μ)]

/-- The extended-valued exceptional remainder is finite almost everywhere
as a consequence of its moment bound. Its real square-root error has a
finite second norm. No infinite value is silently replaced by zero. -/
theorem sqrt_add_toReal (μ : Measure B) {e : B → ℝ≥0∞} (he : Measurable e)
    {R : ℝ} (hR : 0 ≤ R)
    (hmoment : (∫⁻ b, e b + e b ^ 2 ∂μ) ≤ ENNReal.ofReal R) :
    (∀ᵐ b ∂μ, e b < ⊤) ∧
    MemLp (fun b => Real.sqrt (e b).toReal + (e b).toReal) 2 μ ∧
    (eLpNorm (fun b => Real.sqrt (e b).toReal + (e b).toReal) 2 μ).toReal ≤
      2 * Real.sqrt R := by
  have hf : (∫⁻ b, e b ∂μ) < ⊤ :=
    (lintegral_mono fun b => le_add_right le_rfl).trans_lt
      (hmoment.trans_lt ENNReal.ofReal_lt_top)
  have hfinite := ae_lt_top he hf.ne
  refine ⟨hfinite, ?_⟩
  apply sqrt_add_self μ he.ennreal_toReal (fun _ => ENNReal.toReal_nonneg) hR
  apply le_trans _ hmoment
  apply le_of_eq
  apply lintegral_congr_ae
  filter_upwards [hfinite] with b hb
  rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (sq_nonneg _),
    ENNReal.ofReal_toReal hb.ne,
    ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hb.ne]

/-- Finite summation of second norms under an a.e. pointwise envelope.
Finiteness is concluded along with the real norm estimate. -/
theorem sum_envelope {ι : Type*} [Fintype ι] (μ : Measure B)
    {d : B → ℝ} (hd : AEStronglyMeasurable d μ)
    (f : ι → B → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (hbound : ∀ᵐ b ∂μ, |d b| ≤ ∑ i, f i b) :
    MemLp d 2 μ ∧
      (eLpNorm d 2 μ).toReal ≤ ∑ i, (eLpNorm (f i) 2 μ).toReal := by
  have hi := memLp_finsetSum Finset.univ (fun i _ => hf i)
  have hnorm : ∀ᵐ b ∂μ, ‖d b‖ ≤ ‖∑ i, f i b‖ :=
    hbound.mono fun b hb => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      exact hb.trans (le_abs_self _)
  refine ⟨hi.mono hd hnorm, ?_⟩
  apply (ENNReal.toReal_mono hi.eLpNorm_ne_top (eLpNorm_mono_ae hd hnorm)).trans
  have hsum : (fun b => ∑ i, f i b) = ∑ i, f i := by
    funext b
    simp only [Finset.sum_apply]
  rw [hsum]
  exact lpNorm_sum_le (s := Finset.univ) (fun i _ => hf i) (by norm_num)

/-- Integrate a finite family of conditional multiplier bounds. The source
norms are localized on the unconditional good set, and the exceptional
error uses exactly its first-plus-second moment. -/
theorem multiplier_bound (μ : Measure B) [IsProbabilityMeasure μ]
    (κ : Kernel B X) [IsMarkovKernel κ] {ι : Type*} [Fintype ι]
    (f : ι → X → ℝ) (hf : ∀ i, Measurable (f i))
    {G : Set X} (hG : MeasurableSet G) (A M : ι → ℝ)
    (hA : ∀ i, 0 ≤ A i) (hM : ∀ i, 0 ≤ M i)
    (hgood : ∀ i, ∀ᵐ x ∂(κ ∘ₘ μ).restrict G, |f i x| ≤ A i)
    (hb : ∀ i x, |f i x| ≤ M i)
    {e : B → ℝ≥0∞} (he : Measurable e) {R : ℝ} (hR : 0 ≤ R)
    (hmoment : (∫⁻ b, e b + e b ^ 2 ∂μ) ≤ ENNReal.ofReal R)
    {a C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    {d : B → ℝ} (hd : AEStronglyMeasurable d μ)
    (hbound : ∀ᵐ b ∂μ, |d b| ≤ ∑ i,
      (a * Real.sqrt (∫ x, f i x ^ 2 ∂κ b) +
        C * M i * (Real.sqrt (e b).toReal + (e b).toReal))) :
    MemLp d 2 μ ∧ (eLpNorm d 2 μ).toReal ≤
      a * (∑ i, A i) +
        (a * Real.sqrt ((κ ∘ₘ μ).real Gᶜ) + 2 * C * Real.sqrt R) * ∑ i, M i := by
  have herr := sqrt_add_toReal μ he hR hmoment
  let F (i : ι) (b : B) := Real.sqrt (∫ x, f i x ^ 2 ∂κ b)
  let E (b : B) := Real.sqrt (e b).toReal + (e b).toReal
  have hF (i) : MemLp (F i) 2 μ := (conditional_norm μ κ (hf i) (hM i) (hb i)).1
  have hFnorm (i) : (eLpNorm (F i) 2 μ).toReal ≤
      A i + M i * Real.sqrt ((κ ∘ₘ μ).real Gᶜ) :=
    conditional_norm_good_set μ κ (hf i) hG (hA i) (hM i) (hgood i) (hb i)
  have henv (i) : MemLp (fun b => a * F i b + C * M i * E b) 2 μ :=
    ((hF i).const_mul a).add (herr.2.1.const_mul (C * M i))
  have hn (i) : (eLpNorm (fun b => a * F i b + C * M i * E b) 2 μ).toReal ≤
      a * (A i + M i * Real.sqrt ((κ ∘ₘ μ).real Gᶜ)) +
        C * M i * (2 * Real.sqrt R) := by
    have hh := lpNorm_add_le ((hF i).const_mul a)
      (g := fun b => C * M i * E b) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    change lpNorm (a • F i + (C * M i) • E) 2 μ ≤
      lpNorm (a • F i) 2 μ + lpNorm ((C * M i) • E) 2 μ at hh
    rw [lpNorm_const_smul, lpNorm_const_smul] at hh
    change lpNorm (a • F i + (C * M i) • E) 2 μ ≤
      ‖a‖ * lpNorm (F i) 2 μ + ‖C * M i‖ * lpNorm E 2 μ at hh
    rw [Real.norm_eq_abs, abs_of_nonneg ha,
      Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC (hM i))] at hh
    exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left (hFnorm i) ha)
      (mul_le_mul_of_nonneg_left herr.2.2 (mul_nonneg hC (hM i))))
  have hh := sum_envelope μ hd (fun i b => a * F i b + C * M i * E b) henv hbound
  refine ⟨hh.1, hh.2.trans ((Finset.sum_le_sum fun i _ => hn i).trans_eq ?_)⟩
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- The exceptional coefficient in `multiplier_bound` remains stretched
exponential after the source power and both square roots. The constant is
chosen before the size and the two actual exceptional masses. -/
theorem exponential_tail_coefficient {C Q R c δ loss : ℝ}
    (hC : 0 ≤ C) (hQ : 0 ≤ Q) (hR : 0 ≤ R) (hc : 0 < c) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 1 ≤ x → ∀ q r : ℝ,
      q ≤ Q * Real.exp (-c * x ^ δ) → r ≤ R * Real.exp (-c * x ^ δ) →
      C * x ^ loss * Real.sqrt q + 2 * C * Real.sqrt r ≤
        K * Real.exp (-(c / 4) * x ^ δ) := by
  obtain ⟨A, hA, ha⟩ := GoodSetL2Comparison.sqrt_tail_absorption
    (a := loss) hQ hc hδ
  obtain ⟨B, hB, hb⟩ := GoodSetL2Comparison.sqrt_tail_absorption
    (a := 0) hR hc hδ
  refine ⟨C * (A + 2 * B) + 1, by positivity, fun x hx q r hq hr => ?_⟩
  have h₁ := ha x hx
  have h₂ := hb x hx
  rw [Real.rpow_zero, one_mul] at h₂
  calc
    _ ≤ C * (x ^ loss * Real.sqrt (Q * Real.exp (-c * x ^ δ))) +
        2 * C * Real.sqrt (R * Real.exp (-c * x ^ δ)) := by
      rw [mul_assoc]
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hq) (by positivity)) hC)
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hr) (by positivity))
    _ ≤ C * (A * Real.exp (-(c / 4) * x ^ δ)) +
        2 * C * (B * Real.exp (-(c / 4) * x ^ δ)) :=
      add_le_add (mul_le_mul_of_nonneg_left h₁ hC)
        (mul_le_mul_of_nonneg_left h₂ (by positivity))
    _ ≤ _ := by nlinarith [Real.exp_pos (-(c / 4) * x ^ δ)]

end Riesz2.KernelSquareNorm
