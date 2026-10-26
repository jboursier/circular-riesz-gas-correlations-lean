/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.LogConcave.EventSecondMoment
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# Moment and event bounds

This file gives the moment and event estimates used by the exceptional-set estimates of the paper.

* Conversions. A lintegral bound or an `eLpNorm` bound on `f` gives integrability of `|f|^p` and
  a real bound on its integral.
* Markov bounds. A moment bound on `|f|^p` bounds the event `{t ≤ |f|}`, with the optimized
  exponential form.
* Weighted events. A bounded factor times `Y` on an event is bounded by Cauchy–Schwarz.
* Truncation. The integral of `g Y` differs from its integral over `{|Y| < T}` by a weighted event
  term.
* Absorption. A polynomial factor is absorbed into a stretched exponential by lowering its rate.

Every conversion from a lintegral or `eLpNorm` bound also concludes integrability. A finite
expectation is therefore never read off from the Bochner value of a non-integrable function, which
is `0`. The event probabilities are real measures `μ.real`.
-/

public section

noncomputable section

open MeasureTheory Set

namespace Riesz2.MomentEvent

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A lintegral bound on `|f|^p` gives integrability of `|f|^p` and the bound `K` on its
integral, for every `K ≥ 0`. -/
theorem integrable_rpow_abs_and_integral_le_of_lintegral_le {f : Ω → ℝ} (hf : Measurable f)
    {p K : ℝ} (hK : 0 ≤ K) (h : ∫⁻ x, ENNReal.ofReal (|f x| ^ p) ∂μ ≤ ENNReal.ofReal K) :
    Integrable (fun x => |f x| ^ p) μ ∧ ∫ x, |f x| ^ p ∂μ ≤ K := by
  have hnn : ∀ x, 0 ≤ |f x| ^ p := fun x => Real.rpow_nonneg (abs_nonneg _) p
  have habs : Measurable fun x => |f x| := continuous_abs.measurable.comp hf
  have hmeas : Measurable fun x => |f x| ^ p := habs.pow_const p
  have hfin : HasFiniteIntegral (fun x => |f x| ^ p) μ :=
    (hasFiniteIntegral_iff_ofReal (ae_of_all μ hnn)).2 (h.trans_lt ENNReal.ofReal_lt_top)
  have hint : Integrable (fun x => |f x| ^ p) μ := ⟨hmeas.aestronglyMeasurable, hfin⟩
  have heq := ofReal_integral_eq_lintegral_ofReal hint (ae_of_all μ hnn)
  have h2 : ENNReal.ofReal (∫ x, |f x| ^ p ∂μ) ≤ ENNReal.ofReal K := heq.trans_le h
  exact ⟨hint, (ENNReal.ofReal_le_ofReal_iff hK).1 h2⟩

/-- An `eLpNorm` bound `‖f‖_p ≤ M` in `L^p`, for `0 < p`, gives integrability of `|f|^p` and the
bound `M^p` on its integral. The bound `‖Y‖_p ≤ C p^A h` of
the proof of Lemma 5.8 is read through this conversion. -/
theorem integrable_rpow_abs_and_integral_le_of_eLpNorm_le {f : Ω → ℝ} (hf : Measurable f)
    {p M : ℝ} (hp : 0 < p) (hM : 0 ≤ M)
    (h : eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal M) :
    Integrable (fun x => |f x| ^ p) μ ∧ ∫ x, |f x| ^ p ∂μ ≤ M ^ p := by
  have hp0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp).ne'
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp.le, one_div] at h
  have hpow := ENNReal.rpow_le_rpow h hp.le
  rw [ENNReal.rpow_inv_rpow hp.ne'] at hpow
  have hl : ∫⁻ x, ENNReal.ofReal (|f x| ^ p) ∂μ = ∫⁻ x, ‖f x‖ₑ ^ p ∂μ :=
    lintegral_congr fun x => by
      rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le]
  have hbound : ∫⁻ x, ENNReal.ofReal (|f x| ^ p) ∂μ ≤ ENNReal.ofReal (M ^ p) := by
    rw [hl, ← ENNReal.ofReal_rpow_of_nonneg hM hp.le]
    exact hpow
  exact integrable_rpow_abs_and_integral_le_of_lintegral_le hf (Real.rpow_nonneg hM p) hbound

/-- Markov's inequality for `|f|^p` in lintegral form. Let `0 < p` and `0 < t`. Then
`t^p μ(t ≤ |f|)` is at most the lintegral of `|f|^p`. No integrability is assumed. -/
theorem ofReal_mul_measure_le_lintegral_rpow_abs {f : Ω → ℝ} (hf : Measurable f) {p t : ℝ}
    (hp : 0 < p) (ht : 0 < t) :
    ENNReal.ofReal (t ^ p) * μ {x | t ≤ |f x|} ≤ ∫⁻ x, ENNReal.ofReal (|f x| ^ p) ∂μ := by
  have hmeas : Measurable fun x => ENNReal.ofReal (|f x| ^ p) :=
    ((continuous_abs.measurable.comp hf).pow_const p).ennreal_ofReal
  have hset : {x | ENNReal.ofReal (t ^ p) ≤ ENNReal.ofReal (|f x| ^ p)} = {x | t ≤ |f x|} := by
    ext x
    show ENNReal.ofReal (t ^ p) ≤ ENNReal.ofReal (|f x| ^ p) ↔ t ≤ |f x|
    rw [ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg (abs_nonneg _) p)]
    exact Real.rpow_le_rpow_iff ht.le (abs_nonneg _) hp
  have h : ENNReal.ofReal (t ^ p) * μ {x | ENNReal.ofReal (t ^ p) ≤ ENNReal.ofReal (|f x| ^ p)} ≤
      ∫⁻ x, ENNReal.ofReal (|f x| ^ p) ∂μ :=
    mul_meas_ge_le_lintegral₀ hmeas.aemeasurable _
  rwa [hset] at h

/-- Markov's inequality for `|f|^p`, in real form. Let `0 < p` and `0 < t`. If `|f|^p` is
integrable, then `t^p μ(t ≤ |f|)` is at most the integral of `|f|^p`. -/
theorem mul_measureReal_le_integral_rpow_abs {f : Ω → ℝ} {p t : ℝ} (hp : 0 < p) (ht : 0 < t)
    (hi : Integrable (fun x => |f x| ^ p) μ) :
    t ^ p * μ.real {x | t ≤ |f x|} ≤ ∫ x, |f x| ^ p ∂μ := by
  have hset : {x | t ^ p ≤ |f x| ^ p} = {x | t ≤ |f x|} := by
    ext x
    exact Real.rpow_le_rpow_iff ht.le (abs_nonneg _) hp
  have h : t ^ p * μ.real {x | t ^ p ≤ |f x| ^ p} ≤ ∫ x, |f x| ^ p ∂μ :=
    mul_meas_ge_le_integral_of_nonneg (ae_of_all μ fun x => Real.rpow_nonneg (abs_nonneg _) p)
      hi (t ^ p)
  rwa [hset] at h

/-- A moment bound gives a power tail bound. Let `0 < p`, `0 ≤ M` and `0 < t`. If `∫ |f|^p ≤ M^p`,
then `μ(t ≤ |f|) ≤ (M/t)^p`. -/
theorem measureReal_abs_ge_le_div_rpow_of_integral_le {f : Ω → ℝ} {p M t : ℝ} (hp : 0 < p)
    (hM : 0 ≤ M) (ht : 0 < t) (hi : Integrable (fun x => |f x| ^ p) μ)
    (hint : ∫ x, |f x| ^ p ∂μ ≤ M ^ p) :
    μ.real {x | t ≤ |f x|} ≤ (M / t) ^ p := by
  have h := mul_measureReal_le_integral_rpow_abs hp ht hi
  have htp : 0 < t ^ p := Real.rpow_pos_of_pos ht p
  rw [Real.div_rpow hM ht.le, le_div_iff₀ htp]
  calc μ.real {x | t ≤ |f x|} * t ^ p = t ^ p * μ.real {x | t ≤ |f x|} := mul_comm _ _
    _ ≤ ∫ x, |f x| ^ p ∂μ := h
    _ ≤ M ^ p := hint

/-- The optimized exponential tail. Let `0 < p`, `0 ≤ M`, `0 < t` and `M ≤ exp(-1) t`. If
`∫ |f|^p ≤ M^p`, then `μ(t ≤ |f|) ≤ exp(-p)`. In the proof of Lemma 5.8, take `t = n^{κε} h` and `M = C p^A h`, so `M ≤ exp(-1) t` holds once `C p^A ≤ exp(-1) n^{κε}`. -/
theorem measureReal_abs_ge_le_exp_neg_of_integral_le {f : Ω → ℝ} {p M t : ℝ} (hp : 0 < p)
    (hM : 0 ≤ M) (ht : 0 < t) (hi : Integrable (fun x => |f x| ^ p) μ)
    (hint : ∫ x, |f x| ^ p ∂μ ≤ M ^ p) (hMt : M ≤ Real.exp (-1) * t) :
    μ.real {x | t ≤ |f x|} ≤ Real.exp (-p) := by
  refine (measureReal_abs_ge_le_div_rpow_of_integral_le hp hM ht hi hint).trans ?_
  have hr : M / t ≤ Real.exp (-1) := (div_le_iff₀ ht).2 hMt
  calc (M / t) ^ p ≤ Real.exp (-1) ^ p := Real.rpow_le_rpow (div_nonneg hM ht.le) hr hp.le
    _ = Real.exp (-p) := by rw [← Real.exp_mul, neg_one_mul]

/-- The optimized exponential tail from an `eLpNorm` bound `‖f‖_p ≤ M`. The hypotheses are those of
`measureReal_abs_ge_le_exp_neg_of_integral_le`, with the moment bound written as an `eLpNorm`. -/
theorem measureReal_abs_ge_le_exp_neg_of_eLpNorm_le {f : Ω → ℝ} (hf : Measurable f) {p M t : ℝ}
    (hp : 0 < p) (hM : 0 ≤ M) (ht : 0 < t)
    (h : eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal M) (hMt : M ≤ Real.exp (-1) * t) :
    μ.real {x | t ≤ |f x|} ≤ Real.exp (-p) := by
  obtain ⟨hi, hint⟩ := integrable_rpow_abs_and_integral_le_of_eLpNorm_le hf hp hM h
  exact measureReal_abs_ge_le_exp_neg_of_integral_le hp hM ht hi hint hMt

/-- An integrable function on a finite measure is integrable once its square is. -/
theorem integrable_of_integrable_sq [IsFiniteMeasure μ] {Y : Ω → ℝ} (hY : Measurable Y)
    (hi : Integrable (fun x => Y x ^ 2) μ) : Integrable Y μ :=
  ((memLp_two_iff_integrable_sq hY.aestronglyMeasurable).mpr hi).integrable one_le_two

/-- A product of a bounded measurable function with an integrable function is integrable. Let
`|g| ≤ M` pointwise. -/
theorem integrable_mul_of_abs_le {g Y : Ω → ℝ} {M : ℝ} (hg : Measurable g)
    (hY : Integrable Y μ) (hgM : ∀ x, |g x| ≤ M) : Integrable (fun x => g x * Y x) μ := by
  refine (hY.abs.const_mul M).mono' (hg.aestronglyMeasurable.mul hY.aestronglyMeasurable)
    (ae_of_all μ fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hgM x) (abs_nonneg _)

/-- Weighted Cauchy–Schwarz on an event. Let `μ` be finite, `|g| ≤ M` with `0 ≤ M`, and let
`Y` be square integrable. For every measurable set `E`, the integral of `g Y` over `E` is at most
`M ‖Y‖_2 μ(E)^{1/2}` in absolute value, where `‖Y‖_2` is `(∫ Y^2)^{1/2}`. This is used for the exceptional-set bounds in the proof of Lemma 5.8. -/
theorem abs_integral_mul_le_sqrt_mul_sqrt [IsFiniteMeasure μ] {g Y : Ω → ℝ} {M : ℝ}
    (hg : Measurable g) (hY : Measurable Y) (hM : 0 ≤ M) (hgM : ∀ x, |g x| ≤ M)
    (hi : Integrable (fun x => Y x ^ 2) μ) {E : Set Ω} (hE : MeasurableSet E) :
    |∫ x in E, g x * Y x ∂μ| ≤ M * Real.sqrt (∫ x, Y x ^ 2 ∂μ) * Real.sqrt (μ.real E) := by
  have hL1 : Integrable Y μ := integrable_of_integrable_sq hY hi
  have hYabs : Integrable (fun x => M * |Y x|) μ := hL1.abs.const_mul M
  have hgY_le : ∀ x, |g x * Y x| ≤ M * |Y x| := fun x => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hgM x) (abs_nonneg _)
  have hstep1 : |∫ x in E, g x * Y x ∂μ| ≤ ∫ x in E, M * |Y x| ∂μ :=
    abs_integral_le_integral_abs.trans
      (setIntegral_mono_on (integrable_mul_of_abs_le hg hL1 hgM).abs.integrableOn
        hYabs.integrableOn hE fun x _ => hgY_le x)
  have hstep2 : (∫ x in E, M * |Y x| ∂μ) = M * ∫ x in E, |Y x| ∂μ := integral_const_mul M _
  have hYabs_meas : Measurable fun x => |Y x| := continuous_abs.measurable.comp hY
  have hCS : (∫ x in E, |Y x| ∂μ) ≤
      (∫ x, |Y x| ^ 2 ∂μ) ^ (1 / (2 : ℝ)) * μ.real E ^ (1 / (2 : ℝ)) :=
    Riesz1.integral_on_event_le_second_moment hYabs_meas.aestronglyMeasurable
      (fun x => abs_nonneg (Y x)) (by simpa only [sq_abs] using hi) hE
  have hsq : (∫ x, |Y x| ^ 2 ∂μ) = ∫ x, Y x ^ 2 ∂μ := by simp only [sq_abs]
  rw [hsq, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hCS
  calc |∫ x in E, g x * Y x ∂μ| ≤ M * ∫ x in E, |Y x| ∂μ := (hstep1.trans_eq hstep2)
    _ ≤ M * (Real.sqrt (∫ x, Y x ^ 2 ∂μ) * Real.sqrt (μ.real E)) :=
        mul_le_mul_of_nonneg_left hCS hM
    _ = M * Real.sqrt (∫ x, Y x ^ 2 ∂μ) * Real.sqrt (μ.real E) := by ring

/-- Truncation interface for a coefficient. Let `μ` be finite, let `|g| ≤ M` with `0 ≤ M`, and let
`Y` be square integrable. Let `T` be a real threshold. Then the integral of `g Y` differs from its
truncated part `∫_{|Y| < T} g Y` by at most `M ‖Y‖_2 μ(T ≤ |Y|)^{1/2}`. The proof of Lemma 5.8 uses this bound with its chosen threshold and moment power. -/
theorem abs_integral_sub_truncated_le [IsFiniteMeasure μ] {g Y : Ω → ℝ} {M T : ℝ}
    (hg : Measurable g) (hY : Measurable Y) (hM : 0 ≤ M) (hgM : ∀ x, |g x| ≤ M)
    (hi : Integrable (fun x => Y x ^ 2) μ) :
    |(∫ x, g x * Y x ∂μ) - ∫ x in {x | |Y x| < T}, g x * Y x ∂μ| ≤
      M * Real.sqrt (∫ x, Y x ^ 2 ∂μ) * Real.sqrt (μ.real {x | T ≤ |Y x|}) := by
  have hS : MeasurableSet {x | |Y x| < T} :=
    measurableSet_lt (continuous_abs.measurable.comp hY) measurable_const
  have hgY : Integrable (fun x => g x * Y x) μ :=
    integrable_mul_of_abs_le hg (integrable_of_integrable_sq hY hi) hgM
  have hsplit := integral_add_compl hS hgY
  have hcompl : {x | |Y x| < T}ᶜ = {x | T ≤ |Y x|} := by
    ext x
    simp
  have hC := abs_integral_mul_le_sqrt_mul_sqrt hg hY hM hgM hi hS.compl
  rw [hcompl] at hC hsplit
  have hdiff : (∫ x, g x * Y x ∂μ) - ∫ x in {x | |Y x| < T}, g x * Y x ∂μ =
      ∫ x in {x | T ≤ |Y x|}, g x * Y x ∂μ := by
    rw [← hsplit]
    ring
  rw [hdiff]
  exact hC

/-- Cauchy–Schwarz for two square integrable factors. Let `φ` and `η` be measurable with `φ^2` and
`η^2` integrable. Then `φ η` is integrable, and `∫ |φ η|` is at most `‖φ‖_2 ‖η‖_2`, where
`‖φ‖_2 = (∫ φ^2)^{1/2}`. -/
theorem integrable_mul_and_integral_abs_mul_le {φ η : Ω → ℝ} (hφ : Measurable φ)
    (hη : Measurable η) (hiφ : Integrable (fun x => φ x ^ 2) μ)
    (hiη : Integrable (fun x => η x ^ 2) μ) :
    Integrable (fun x => φ x * η x) μ ∧
      ∫ x, |φ x * η x| ∂μ ≤ Real.sqrt (∫ x, φ x ^ 2 ∂μ) * Real.sqrt (∫ x, η x ^ 2 ∂μ) := by
  have hf : MemLp φ 2 μ := (memLp_two_iff_integrable_sq hφ.aestronglyMeasurable).mpr hiφ
  have hg : MemLp η 2 μ := (memLp_two_iff_integrable_sq hη.aestronglyMeasurable).mpr hiη
  refine ⟨hf.integrable_mul hg, ?_⟩
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all μ fun x => abs_nonneg (φ x)) (ae_of_all μ fun x => abs_nonneg (η x))
    (by rw [ENNReal.ofReal_ofNat]; exact hf.abs)
    (by rw [ENNReal.ofReal_ofNat]; exact hg.abs)
  simpa only [abs_mul, Real.rpow_two, sq_abs, Real.sqrt_eq_rpow] using hh

/-- The truncated coefficient bound. Let `φ` and `η` be measurable with `φ^2` and `η^2`
integrable, let `Y` be measurable, and let `T ≥ 0`. Then the integral of `φ η Y` over
`{|Y| < T}` is at most `T ‖φ‖_2 ‖η‖_2` in absolute value. This bounds the truncated term in the proof of Lemma 5.8. -/
theorem abs_integral_truncated_mul_le {φ η Y : Ω → ℝ} {T : ℝ} (hφ : Measurable φ)
    (hη : Measurable η) (hY : Measurable Y) (hT : 0 ≤ T)
    (hiφ : Integrable (fun x => φ x ^ 2) μ) (hiη : Integrable (fun x => η x ^ 2) μ) :
    |∫ x in {x | |Y x| < T}, φ x * η x * Y x ∂μ| ≤
      T * (Real.sqrt (∫ x, φ x ^ 2 ∂μ) * Real.sqrt (∫ x, η x ^ 2 ∂μ)) := by
  obtain ⟨hint, hCS⟩ := integrable_mul_and_integral_abs_mul_le hφ hη hiφ hiη
  have hS : MeasurableSet {x | |Y x| < T} :=
    measurableSet_lt (continuous_abs.measurable.comp hY) measurable_const
  have hbound : ∀ x, |Y x| < T → |φ x * η x * Y x| ≤ T * |φ x * η x| := fun x hx => by
    rw [abs_mul (φ x * η x) (Y x), mul_comm T]
    exact mul_le_mul_of_nonneg_left hx.le (abs_nonneg _)
  have hgS : IntegrableOn (fun x => T * |φ x * η x|) {x | |Y x| < T} μ :=
    (hint.abs.const_mul T).integrableOn
  have hae : ∀ᵐ x ∂μ.restrict {x | |Y x| < T}, |φ x * η x * Y x| ≤ T * |φ x * η x| :=
    (ae_restrict_iff' hS).2 (ae_of_all μ fun x hx => hbound x hx)
  have hfS : IntegrableOn (fun x => φ x * η x * Y x) {x | |Y x| < T} μ := by
    refine Integrable.mono' hgS ((hφ.mul hη).mul hY).aestronglyMeasurable ?_
    exact hae.mono fun x hx => by rwa [Real.norm_eq_abs]
  have hstep1 : |∫ x in {x | |Y x| < T}, φ x * η x * Y x ∂μ| ≤
      ∫ x in {x | |Y x| < T}, T * |φ x * η x| ∂μ :=
    abs_integral_le_integral_abs.trans (integral_mono_ae hfS.abs hgS hae)
  have hstep2 : (∫ x in {x | |Y x| < T}, T * |φ x * η x| ∂μ) =
      T * ∫ x in {x | |Y x| < T}, |φ x * η x| ∂μ := integral_const_mul T _
  have hstep3 : (∫ x in {x | |Y x| < T}, |φ x * η x| ∂μ) ≤ ∫ x, |φ x * η x| ∂μ :=
    setIntegral_le_integral hint.abs (ae_of_all μ fun x => abs_nonneg _)
  calc |∫ x in {x | |Y x| < T}, φ x * η x * Y x ∂μ|
      ≤ T * ∫ x in {x | |Y x| < T}, |φ x * η x| ∂μ := hstep1.trans_eq hstep2
    _ ≤ T * ∫ x, |φ x * η x| ∂μ := mul_le_mul_of_nonneg_left hstep3 hT
    _ ≤ T * (Real.sqrt (∫ x, φ x ^ 2 ∂μ) * Real.sqrt (∫ x, η x ^ 2 ∂μ)) :=
        mul_le_mul_of_nonneg_left hCS hT

/-- Polynomial absorption into a stretched exponential. Let `a ∈ ℝ`, `0 < δ` and `c' < c`. Then
there is `C ≥ 0` such that `x^a exp(-c x^δ) ≤ C exp(-c' x^δ)` for every real `x ≥ 1`. A polynomial
factor in the length is absorbed by lowering the exponential rate from `c` to `c'`. The constant
depends only on `a`, `c`, `c'` and `δ`. -/
theorem exists_rpow_mul_exp_neg_le {a c c' δ : ℝ} (hδ : 0 < δ) (hcc : c' < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      x ^ a * Real.exp (-c * x ^ δ) ≤ C * Real.exp (-c' * x ^ δ) := by
  have hl : 0 < c - c' := sub_pos.2 hcc
  obtain ⟨m, hm⟩ := exists_nat_ge (a / δ)
  have ham : a ≤ δ * m := by
    have h := (div_le_iff₀ hδ).1 hm
    linarith [mul_comm (m : ℝ) δ]
  refine ⟨(Nat.factorial m : ℝ) / (c - c') ^ m,
    div_nonneg (Nat.cast_nonneg _) (pow_nonneg hl.le m), fun x hx => ?_⟩
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hy0 : 0 ≤ x ^ δ := Real.rpow_nonneg hx0 δ
  -- The power `x^a` is at most `(x^δ)^m`, since `x ≥ 1` and `a ≤ δ m`.
  have h1 : x ^ a ≤ (x ^ δ) ^ m := by
    calc x ^ a ≤ x ^ (δ * m) := Real.rpow_le_rpow_of_exponent_le hx ham
      _ = (x ^ δ) ^ m := by rw [Real.rpow_mul hx0, Real.rpow_natCast]
  -- The exponential series gives `y^m ≤ m! exp y` for `y = (c - c') x^δ ≥ 0`.
  have h2 : ((c - c') * x ^ δ) ^ m ≤ Real.exp ((c - c') * x ^ δ) * (Nat.factorial m : ℝ) := by
    have h := Real.pow_div_factorial_le_exp ((c - c') * x ^ δ) (mul_nonneg hl.le hy0) m
    have hfac : (0 : ℝ) < Nat.factorial m := Nat.cast_pos.2 (Nat.factorial_pos m)
    rwa [div_le_iff₀ hfac] at h
  have h3 : Real.exp (-((c - c') * x ^ δ)) * ((c - c') * x ^ δ) ^ m ≤ Nat.factorial m := by
    calc Real.exp (-((c - c') * x ^ δ)) * ((c - c') * x ^ δ) ^ m
        ≤ Real.exp (-((c - c') * x ^ δ)) *
          (Real.exp ((c - c') * x ^ δ) * (Nat.factorial m : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = (Real.exp (-((c - c') * x ^ δ)) * Real.exp ((c - c') * x ^ δ)) *
          (Nat.factorial m : ℝ) := by ring
      _ = Nat.factorial m := by
          rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  have h4 : x ^ a * Real.exp (-((c - c') * x ^ δ)) ≤
      (Nat.factorial m : ℝ) / (c - c') ^ m := by
    rw [le_div_iff₀ (pow_pos hl m)]
    calc x ^ a * Real.exp (-((c - c') * x ^ δ)) * (c - c') ^ m
        ≤ (x ^ δ) ^ m * Real.exp (-((c - c') * x ^ δ)) * (c - c') ^ m := by gcongr
      _ = Real.exp (-((c - c') * x ^ δ)) * ((c - c') * x ^ δ) ^ m := by
          rw [mul_pow]
          ring
      _ ≤ Nat.factorial m := h3
  have hsplit : Real.exp (-c * x ^ δ) =
      Real.exp (-((c - c') * x ^ δ)) * Real.exp (-c' * x ^ δ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit]
  calc x ^ a * (Real.exp (-((c - c') * x ^ δ)) * Real.exp (-c' * x ^ δ))
      = (x ^ a * Real.exp (-((c - c') * x ^ δ))) * Real.exp (-c' * x ^ δ) := by ring
    _ ≤ ((Nat.factorial m : ℝ) / (c - c') ^ m) * Real.exp (-c' * x ^ δ) :=
        mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le

end Riesz2.MomentEvent
