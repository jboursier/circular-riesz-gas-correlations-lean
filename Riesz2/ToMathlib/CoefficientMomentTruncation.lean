/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.MomentEventBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Tactic

/-!
# Truncation of moment-controlled coefficients

These are the truncation estimates used in the proof of Lemma 5.8.
They hold for an arbitrary probability measure `ν` on a measurable space `Ω`.

* `Riesz2.CoefficientMomentTruncation.moment_truncation` truncates `Y` at
  `n^{κε} h`. Cauchy–Schwarz bounds the truncated part. Markov's inequality
  for the `p`-th moment, with `p = n^δ`, bounds the tail.
* `Riesz2.CoefficientMomentTruncation.exceptional_set_bound` uses the second
  moment of `Y` and the probability of the exceptional event.

Pointwise bounds `Mφ` and `Mη` encode the sup-norms of `φ` and `η`.
Essential bounds give the same conclusion by replacing the functions on null
sets. The integrals and `L²` norms are unchanged.
The estimates use `Riesz2.MomentEvent` in `MomentEventBounds.lean`.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology

namespace Riesz2.CoefficientMomentTruncation

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A measurable function bounded by `M` in absolute value has integrable square on a finite
measure. -/
theorem integrable_sq_of_abs_le {μ : Measure Ω} [IsFiniteMeasure μ] {g : Ω → ℝ} {M : ℝ}
    (hg : Measurable g) (hgM : ∀ x, |g x| ≤ M) : Integrable (fun x => g x ^ 2) μ := by
  refine Integrable.mono' (integrable_const (M ^ 2)) (hg.pow_const 2).aestronglyMeasurable
    (ae_of_all μ fun x => ?_)
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hgM x) 2

/-- The `L²` bound `‖Y‖_2 ≤ M` of a measurable `Y` gives integrability of `Y²` and the bound `M²`
on its integral. -/
theorem sq_integrable_and_integral_le {μ : Measure Ω} {Y : Ω → ℝ} (hY : Measurable Y) {M : ℝ}
    (hM : 0 ≤ M) (h : eLpNorm Y (ENNReal.ofReal 2) μ ≤ ENNReal.ofReal M) :
    Integrable (fun x => Y x ^ 2) μ ∧ ∫ x, Y x ^ 2 ∂μ ≤ M ^ 2 := by
  obtain ⟨hi, hint⟩ :=
    Riesz2.MomentEvent.integrable_rpow_abs_and_integral_le_of_eLpNorm_le hY (by norm_num) hM h
  simp only [Real.rpow_two, sq_abs] at hi hint
  exact ⟨hi, hint⟩

/-- First assertion of the proof of Lemma 5.8. Let `A`, `ε`, `κ` be positive, and let
`δ = κ ε / (2 A)`. For every `C ≥ 1` there are `c, C₁ > 0`, depending only on `C`, `A`, `ε`, `κ`,
such that for every `n ≥ 2`, every probability measure `ν`, every `0 < h ≤ 1`, every measurable `Y`
with `‖Y‖_p ≤ C p^A h` for all `p ≥ 1`, and every measurable `φ`, `η` with `|φ| ≤ Mφ` and
`|η| ≤ Mη`, the function `φ η Y` is integrable and
`|∫ φ η Y dν| ≤ C₁ n^{κ ε} h ‖φ‖_2 ‖η‖_2 + C₁ e^{-c n^δ} Mφ Mη`. -/
theorem moment_truncation {A ε κ C : ℝ} (hA : 0 < A) (hε : 0 < ε) (hκ : 0 < κ) (hC : 1 ≤ C) :
    ∃ c C₁ : ℝ, 0 < c ∧ 0 < C₁ ∧ ∀ (n : ℕ), 2 ≤ n → ∀ (ν : Measure Ω) [IsProbabilityMeasure ν]
      (h : ℝ), 0 < h → h ≤ 1 → ∀ (Y φ η : Ω → ℝ) (Mφ Mη : ℝ),
      Measurable Y → Measurable φ → Measurable η → 0 ≤ Mφ → 0 ≤ Mη →
      (∀ x, |φ x| ≤ Mφ) → (∀ x, |η x| ≤ Mη) →
      (∀ p : ℝ, 1 ≤ p → eLpNorm Y (ENNReal.ofReal p) ν ≤ ENNReal.ofReal (C * p ^ A * h)) →
      Integrable (fun x => φ x * η x * Y x) ν ∧
        |∫ x, φ x * η x * Y x ∂ν| ≤
          C₁ * (n : ℝ) ^ (κ * ε) * h * (Real.sqrt (∫ x, φ x ^ 2 ∂ν) * Real.sqrt (∫ x, η x ^ 2 ∂ν)) +
            C₁ * Real.exp (-c * (n : ℝ) ^ (κ * ε / (2 * A))) * (Mφ * Mη) := by
  have hC0 : 0 ≤ C := by linarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = κ * ε / (2 * A) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδA : δ * A = κ * ε / 2 := by rw [hδ]; field_simp
  -- The threshold `N` gives `e C ≤ n^{κ ε / 2}` for `n ≥ N`.
  have hpos : 0 < κ * ε / 2 := by positivity
  have hev : ∀ᶠ n : ℕ in atTop, Real.exp 1 * C ≤ (n : ℝ) ^ (κ * ε / 2) :=
    ((tendsto_rpow_atTop hpos).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, K₀ = Real.exp ((N : ℝ) ^ δ / 2) := ⟨_, rfl⟩
  have hK₀pos : 0 < K₀ := by rw [hK₀]; exact Real.exp_pos _
  have hK₀1 : 1 ≤ K₀ := by
    rw [hK₀]
    apply Real.one_le_exp
    have : (0 : ℝ) ≤ (N : ℝ) ^ δ := Real.rpow_nonneg (Nat.cast_nonneg N) δ
    linarith
  have hC2 : 0 ≤ C * (2 : ℝ) ^ A := mul_nonneg hC0 (Real.rpow_nonneg (by norm_num) A)
  refine ⟨1 / 2, 1 + C * 2 ^ A * K₀, by norm_num,
    add_pos_of_pos_of_nonneg one_pos (mul_nonneg hC2 hK₀pos.le), ?_⟩
  intro n hn ν hν h hh0 hh1 Y φ η Mφ Mη hY hφ hη hMφ0 hMη0 hφM hηM hYp
  rw [← hδ]
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (n : ℝ) ^ (κ * ε / 2) := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = (n : ℝ) ^ δ := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = (n : ℝ) ^ (κ * ε) * h := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; exact Real.rpow_pos_of_pos hn0 _
  have hp1 : 1 ≤ p := by rw [hp]; exact Real.one_le_rpow hn1 hδpos.le
  have hpA : p ^ A = s := by rw [hp, hs, ← Real.rpow_mul hn0.le, hδA]
  have hnk : (n : ℝ) ^ (κ * ε) = s ^ 2 := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    congr 1
    push_cast
    ring
  have hT0 : 0 < T := by rw [hTdef]; exact mul_pos (Real.rpow_pos_of_pos hn0 _) hh0
  have hM0 : 0 ≤ C * p ^ A * h :=
    mul_nonneg (mul_nonneg hC0 (Real.rpow_nonneg (by linarith) A)) hh0.le
  -- Markov bound for the tail event `{T ≤ |Y|}`, and the square root of its probability.
  have hsq : Real.sqrt (ν.real {x | T ≤ |Y x|}) ≤ K₀ * Real.exp (-(1 / 2) * p) := by
    have hE : 0 ≤ Real.exp (-(1 / 2) * p) := (Real.exp_pos _).le
    have hsq_eq : Real.exp (-(1 / 2) * p) ^ 2 = Real.exp (-p) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hbound : ν.real {x | T ≤ |Y x|} ≤ (K₀ * Real.exp (-(1 / 2) * p)) ^ 2 := by
      by_cases hNn : N ≤ n
      · have hsN : Real.exp 1 * C ≤ s := by rw [hs]; exact hN n hNn
        have hMt : C * p ^ A * h ≤ Real.exp (-1) * T := by
          rw [hpA, hTdef, hnk]
          have hkey : C ≤ Real.exp (-1) * s := by
            have h1 := mul_le_mul_of_nonneg_left hsN (Real.exp_pos (-1)).le
            have h2 : Real.exp (-1) * (Real.exp 1 * C) = C := by
              rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
            linarith
          calc C * s * h = C * (s * h) := by ring
            _ ≤ (Real.exp (-1) * s) * (s * h) :=
                mul_le_mul_of_nonneg_right hkey (mul_pos hs0 hh0).le
            _ = Real.exp (-1) * (s ^ 2 * h) := by ring
        have htail : ν.real {x | T ≤ |Y x|} ≤ Real.exp (-p) :=
          Riesz2.MomentEvent.measureReal_abs_ge_le_exp_neg_of_eLpNorm_le hY (by linarith) hM0 hT0
            (hYp p hp1) hMt
        calc ν.real {x | T ≤ |Y x|} ≤ Real.exp (-p) := htail
          _ = Real.exp (-(1 / 2) * p) ^ 2 := hsq_eq.symm
          _ ≤ (K₀ * Real.exp (-(1 / 2) * p)) ^ 2 :=
              pow_le_pow_left₀ hE (le_mul_of_one_le_left hE hK₀1) 2
      · have hpN : p ≤ (N : ℝ) ^ δ := by
          rw [hp]
          exact Real.rpow_le_rpow hn0.le (by exact_mod_cast (not_le.1 hNn).le) hδpos.le
        have hge : 1 ≤ K₀ * Real.exp (-(1 / 2) * p) := by
          rw [hK₀, ← Real.exp_add]
          apply Real.one_le_exp
          linarith
        calc ν.real {x | T ≤ |Y x|} ≤ 1 := measureReal_le_one
          _ ≤ (K₀ * Real.exp (-(1 / 2) * p)) ^ 2 := one_le_pow₀ hge
    calc Real.sqrt (ν.real {x | T ≤ |Y x|})
        ≤ Real.sqrt ((K₀ * Real.exp (-(1 / 2) * p)) ^ 2) := Real.sqrt_le_sqrt hbound
      _ = K₀ * Real.exp (-(1 / 2) * p) := Real.sqrt_sq (mul_nonneg hK₀pos.le hE)
  -- Second moment of `Y`.
  have hM2 : 0 ≤ C * (2 : ℝ) ^ A * h := mul_nonneg hC2 hh0.le
  obtain ⟨hiY2, hintY2⟩ :=
    sq_integrable_and_integral_le hY hM2 (hYp 2 (by norm_num))
  have hYs : Real.sqrt (∫ x, Y x ^ 2 ∂ν) ≤ C * 2 ^ A * h :=
    (Real.sqrt_le_sqrt hintY2).trans_eq (Real.sqrt_sq hM2)
  -- Bounded coefficients.
  have hMM : 0 ≤ Mφ * Mη := mul_nonneg hMφ0 hMη0
  have hiφ := integrable_sq_of_abs_le (μ := ν) hφ hφM
  have hiη := integrable_sq_of_abs_le (μ := ν) hη hηM
  have hgM : ∀ x, |φ x * η x| ≤ Mφ * Mη := fun x => by
    rw [abs_mul]
    exact mul_le_mul (hφM x) (hηM x) (abs_nonneg _) hMφ0
  have hgY : Integrable (fun x => φ x * η x * Y x) ν :=
    Riesz2.MomentEvent.integrable_mul_of_abs_le (hφ.mul hη)
      (Riesz2.MomentEvent.integrable_of_integrable_sq hY hiY2) hgM
  refine ⟨hgY, ?_⟩
  -- Truncation at `T` splits the expectation into a truncated part and a tail part.
  have hJ : |∫ x in {x | |Y x| < T}, φ x * η x * Y x ∂ν| ≤
      T * (Real.sqrt (∫ x, φ x ^ 2 ∂ν) * Real.sqrt (∫ x, η x ^ 2 ∂ν)) :=
    Riesz2.MomentEvent.abs_integral_truncated_mul_le hφ hη hY hT0.le hiφ hiη
  have hIJ : |(∫ x, φ x * η x * Y x ∂ν) - ∫ x in {x | |Y x| < T}, φ x * η x * Y x ∂ν| ≤
      (Mφ * Mη) * Real.sqrt (∫ x, Y x ^ 2 ∂ν) * Real.sqrt (ν.real {x | T ≤ |Y x|}) :=
    Riesz2.MomentEvent.abs_integral_sub_truncated_le (hφ.mul hη) hY hMM hgM hiY2
  have htri : |∫ x, φ x * η x * Y x ∂ν| ≤
      |(∫ x, φ x * η x * Y x ∂ν) - ∫ x in {x | |Y x| < T}, φ x * η x * Y x ∂ν| +
        |∫ x in {x | |Y x| < T}, φ x * η x * Y x ∂ν| := by
    calc |∫ x, φ x * η x * Y x ∂ν|
        = |((∫ x, φ x * η x * Y x ∂ν) - ∫ x in {x | |Y x| < T}, φ x * η x * Y x ∂ν) +
            ∫ x in {x | |Y x| < T}, φ x * η x * Y x ∂ν| := by rw [sub_add_cancel]
      _ ≤ _ := abs_add_le _ _
  -- The tail term.
  have hIJ2 : |(∫ x, φ x * η x * Y x ∂ν) - ∫ x in {x | |Y x| < T}, φ x * η x * Y x ∂ν| ≤
      (1 + C * 2 ^ A * K₀) * Real.exp (-(1 / 2) * p) * (Mφ * Mη) := by
    have hXe : 0 ≤ C * 2 ^ A * K₀ * Real.exp (-(1 / 2) * p) * (Mφ * Mη) :=
      mul_nonneg (mul_nonneg (mul_nonneg hC2 hK₀pos.le) (Real.exp_pos _).le) hMM
    calc |(∫ x, φ x * η x * Y x ∂ν) - ∫ x in {x | |Y x| < T}, φ x * η x * Y x ∂ν|
        ≤ (Mφ * Mη) * Real.sqrt (∫ x, Y x ^ 2 ∂ν) * Real.sqrt (ν.real {x | T ≤ |Y x|}) := hIJ
      _ ≤ (Mφ * Mη) * (C * 2 ^ A * h) * (K₀ * Real.exp (-(1 / 2) * p)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hYs hMM) hsq (Real.sqrt_nonneg _)
            (mul_nonneg hMM hM2)
      _ = C * 2 ^ A * K₀ * Real.exp (-(1 / 2) * p) * (Mφ * Mη) * h := by ring
      _ ≤ C * 2 ^ A * K₀ * Real.exp (-(1 / 2) * p) * (Mφ * Mη) * 1 :=
          mul_le_mul_of_nonneg_left hh1 hXe
      _ ≤ (1 + C * 2 ^ A * K₀) * Real.exp (-(1 / 2) * p) * (Mφ * Mη) := by
          have hem : 0 ≤ Real.exp (-(1 / 2) * p) * (Mφ * Mη) :=
            mul_nonneg (Real.exp_pos _).le hMM
          nlinarith
  -- The truncated term.
  have hX : 0 ≤ C * 2 ^ A * K₀ := mul_nonneg hC2 hK₀pos.le
  have hC1 : 1 ≤ 1 + C * 2 ^ A * K₀ := by linarith
  have hJ2 : |∫ x in {x | |Y x| < T}, φ x * η x * Y x ∂ν| ≤
      (1 + C * 2 ^ A * K₀) * (n : ℝ) ^ (κ * ε) * h *
        (Real.sqrt (∫ x, φ x ^ 2 ∂ν) * Real.sqrt (∫ x, η x ^ 2 ∂ν)) := by
    have hP : 0 ≤ (n : ℝ) ^ (κ * ε) * h *
        (Real.sqrt (∫ x, φ x ^ 2 ∂ν) * Real.sqrt (∫ x, η x ^ 2 ∂ν)) :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg hn0.le _) hh0.le)
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    calc |∫ x in {x | |Y x| < T}, φ x * η x * Y x ∂ν|
        ≤ T * (Real.sqrt (∫ x, φ x ^ 2 ∂ν) * Real.sqrt (∫ x, η x ^ 2 ∂ν)) := hJ
      _ = (n : ℝ) ^ (κ * ε) * h *
          (Real.sqrt (∫ x, φ x ^ 2 ∂ν) * Real.sqrt (∫ x, η x ^ 2 ∂ν)) := by rw [hTdef]
      _ ≤ (1 + C * 2 ^ A * K₀) * ((n : ℝ) ^ (κ * ε) * h *
          (Real.sqrt (∫ x, φ x ^ 2 ∂ν) * Real.sqrt (∫ x, η x ^ 2 ∂ν))) :=
          le_mul_of_one_le_left hP hC1
      _ = (1 + C * 2 ^ A * K₀) * (n : ℝ) ^ (κ * ε) * h *
          (Real.sqrt (∫ x, φ x ^ 2 ∂ν) * Real.sqrt (∫ x, η x ^ 2 ∂ν)) := by ring
  rw [← hp]
  calc |∫ x, φ x * η x * Y x ∂ν|
      ≤ |(∫ x, φ x * η x * Y x ∂ν) - ∫ x in {x | |Y x| < T}, φ x * η x * Y x ∂ν| +
          |∫ x in {x | |Y x| < T}, φ x * η x * Y x ∂ν| := htri
    _ ≤ (1 + C * 2 ^ A * K₀) * Real.exp (-(1 / 2) * p) * (Mφ * Mη) +
          (1 + C * 2 ^ A * K₀) * (n : ℝ) ^ (κ * ε) * h *
            (Real.sqrt (∫ x, φ x ^ 2 ∂ν) * Real.sqrt (∫ x, η x ^ 2 ∂ν)) :=
        add_le_add hIJ2 hJ2
    _ = (1 + C * 2 ^ A * K₀) * (n : ℝ) ^ (κ * ε) * h *
          (Real.sqrt (∫ x, φ x ^ 2 ∂ν) * Real.sqrt (∫ x, η x ^ 2 ∂ν)) +
        (1 + C * 2 ^ A * K₀) * Real.exp (-(1 / 2) * p) * (Mφ * Mη) := add_comm _ _

/-- Second assertion of the proof of Lemma 5.8. Let `C₂`, `c₂`, `δ₂` be positive and
let `B ≥ 0`. There are `C₃, c₃ > 0`, depending only on `C₂`, `c₂`, `δ₂`, `B`, such that for every
`n ≥ 2`, every probability measure `ν`, every measurable event `E` with
`ν(E) ≤ C₂ e^{-c₂ n^{δ₂}}`, every measurable `Y` with `‖Y‖_2 ≤ C₂ n^B`, and every measurable `φ`,
`η` with `|φ| ≤ Mφ` and `|η| ≤ Mη`, the function `φ η Y` is integrable and
`|∫_E φ η Y dν| ≤ C₃ e^{-c₃ n^{δ₂}} Mφ Mη`. No moment beyond the second is assumed. -/
theorem exceptional_set_bound {C₂ c₂ δ₂ B : ℝ} (hC₂ : 0 < C₂) (hc₂ : 0 < c₂) (hδ₂ : 0 < δ₂)
    (_hB : 0 ≤ B) :
    ∃ C₃ c₃ : ℝ, 0 < C₃ ∧ 0 < c₃ ∧ ∀ (n : ℕ), 2 ≤ n → ∀ (ν : Measure Ω) [IsProbabilityMeasure ν]
      (E : Set Ω) (Y φ η : Ω → ℝ) (Mφ Mη : ℝ), MeasurableSet E → Measurable Y →
      Measurable φ → Measurable η → 0 ≤ Mφ → 0 ≤ Mη →
      (∀ x, |φ x| ≤ Mφ) → (∀ x, |η x| ≤ Mη) →
      ν.real E ≤ C₂ * Real.exp (-c₂ * (n : ℝ) ^ δ₂) →
      eLpNorm Y (ENNReal.ofReal 2) ν ≤ ENNReal.ofReal (C₂ * (n : ℝ) ^ B) →
      Integrable (fun x => φ x * η x * Y x) ν ∧
        |∫ x in E, φ x * η x * Y x ∂ν| ≤
          C₃ * Real.exp (-c₃ * (n : ℝ) ^ δ₂) * (Mφ * Mη) := by
  obtain ⟨K, hK0, hK⟩ := Riesz2.MomentEvent.exists_rpow_mul_exp_neg_le (a := B) (c := c₂ / 2)
    (c' := c₂ / 4) hδ₂ (by linarith)
  refine ⟨C₂ * Real.sqrt C₂ * (K + 1), c₂ / 4,
    mul_pos (mul_pos hC₂ (Real.sqrt_pos.2 hC₂)) (by linarith), by linarith, ?_⟩
  intro n hn ν hν E Y φ η Mφ Mη hE hY hφ hη hMφ0 hMη0 hφM hηM hνE hYL
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hMY : 0 ≤ C₂ * (n : ℝ) ^ B := mul_nonneg hC₂.le (Real.rpow_nonneg (by linarith) B)
  obtain ⟨hiY2, hintY2⟩ := sq_integrable_and_integral_le hY hMY hYL
  have hYs : Real.sqrt (∫ x, Y x ^ 2 ∂ν) ≤ C₂ * (n : ℝ) ^ B :=
    (Real.sqrt_le_sqrt hintY2).trans_eq (Real.sqrt_sq hMY)
  have hMM : 0 ≤ Mφ * Mη := mul_nonneg hMφ0 hMη0
  have hgM : ∀ x, |φ x * η x| ≤ Mφ * Mη := fun x => by
    rw [abs_mul]
    exact mul_le_mul (hφM x) (hηM x) (abs_nonneg _) hMφ0
  have hgY : Integrable (fun x => φ x * η x * Y x) ν :=
    Riesz2.MomentEvent.integrable_mul_of_abs_le (hφ.mul hη)
      (Riesz2.MomentEvent.integrable_of_integrable_sq hY hiY2) hgM
  refine ⟨hgY, ?_⟩
  -- The square root of the probability of `E`.
  have hsE : Real.sqrt (ν.real E) ≤
      Real.sqrt C₂ * Real.exp (-(c₂ / 2) * (n : ℝ) ^ δ₂) := by
    have hsq : (Real.sqrt C₂ * Real.exp (-(c₂ / 2) * (n : ℝ) ^ δ₂)) ^ 2 =
        C₂ * Real.exp (-c₂ * (n : ℝ) ^ δ₂) := by
      rw [mul_pow, Real.sq_sqrt hC₂.le, ← Real.exp_nat_mul,
        show ((2 : ℕ) : ℝ) * (-(c₂ / 2) * (n : ℝ) ^ δ₂) = -c₂ * (n : ℝ) ^ δ₂ by push_cast; ring]
    calc Real.sqrt (ν.real E)
        ≤ Real.sqrt ((Real.sqrt C₂ * Real.exp (-(c₂ / 2) * (n : ℝ) ^ δ₂)) ^ 2) :=
          Real.sqrt_le_sqrt (by rw [hsq]; exact hνE)
      _ = Real.sqrt C₂ * Real.exp (-(c₂ / 2) * (n : ℝ) ^ δ₂) := Real.sqrt_sq (by positivity)
  -- Cauchy–Schwarz on the event `E`.
  have hmain := Riesz2.MomentEvent.abs_integral_mul_le_sqrt_mul_sqrt (μ := ν)
    (g := fun x => φ x * η x) (M := Mφ * Mη) (hφ.mul hη) hY hMM hgM hiY2 hE
  have hK' : (n : ℝ) ^ B * Real.exp (-(c₂ / 2) * (n : ℝ) ^ δ₂) ≤
      K * Real.exp (-(c₂ / 4) * (n : ℝ) ^ δ₂) := hK (n : ℝ) hn1
  have hexp4 : 0 ≤ Real.exp (-(c₂ / 4) * (n : ℝ) ^ δ₂) := (Real.exp_pos _).le
  calc |∫ x in E, φ x * η x * Y x ∂ν|
      ≤ Mφ * Mη * (C₂ * (n : ℝ) ^ B) *
          (Real.sqrt C₂ * Real.exp (-(c₂ / 2) * (n : ℝ) ^ δ₂)) :=
        hmain.trans (mul_le_mul (mul_le_mul_of_nonneg_left hYs hMM) hsE (Real.sqrt_nonneg _)
          (mul_nonneg hMM hMY))
    _ = Mφ * Mη * (C₂ * Real.sqrt C₂) *
          ((n : ℝ) ^ B * Real.exp (-(c₂ / 2) * (n : ℝ) ^ δ₂)) := by ring
    _ ≤ Mφ * Mη * (C₂ * Real.sqrt C₂) * (K * Real.exp (-(c₂ / 4) * (n : ℝ) ^ δ₂)) :=
        mul_le_mul_of_nonneg_left hK' (mul_nonneg hMM (mul_nonneg hC₂.le (Real.sqrt_nonneg _)))
    _ ≤ Mφ * Mη * (C₂ * Real.sqrt C₂) * ((K + 1) * Real.exp (-(c₂ / 4) * (n : ℝ) ^ δ₂)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hexp4)
          (mul_nonneg hMM (mul_nonneg hC₂.le (Real.sqrt_nonneg _)))
    _ = C₂ * Real.sqrt C₂ * (K + 1) * Real.exp (-(c₂ / 4) * (n : ℝ) ^ δ₂) * (Mφ * Mη) := by ring

end Riesz2.CoefficientMomentTruncation
