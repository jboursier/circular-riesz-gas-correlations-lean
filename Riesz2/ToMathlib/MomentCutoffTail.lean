/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.MomentEventBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Stretched exponential tails from polynomial moment growth

The norm exponent can be any real number. Thus the optimal choice does
not require a floor, and the tail power is fixed before the moment prefactor.
-/

public section
noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace Riesz2.MomentEvent

/-- Internal optimization used by Subsection 5.1: a moment degree
`A` yields tail power `ε/(2*A)`, with constants uniform over all probability
spaces, functions and positive spatial weights satisfying the moment bound. -/
theorem moment_cutoff_tail {A ε C : ℝ} (hA : 0 < A) (hε : 0 < ε) (hC : 0 < C) :
    ∃ D : ℝ, 0 < D ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (Y : Ω → ℝ), Measurable Y → ∀ (h κ : ℝ), 0 < h → 1 ≤ κ →
        (∀ q : ℝ, 1 ≤ q → eLpNorm Y (ENNReal.ofReal q) μ ≤
          ENNReal.ofReal (C * q ^ A * h)) →
        μ {x | (n : ℝ) ^ (κ * ε) * h < |Y x|} ≤
          ENNReal.ofReal (D * Real.exp (-(n : ℝ) ^ (ε / (2 * A)))) := by
  have hδ : 0 < ε / (2 * A) := by positivity
  have hev : ∀ᶠ n : ℕ in atTop, Real.exp 1 * C ≤ (n : ℝ) ^ (ε / 2) :=
    ((tendsto_rpow_atTop (show 0 < ε / 2 by positivity)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  obtain ⟨T, hT⟩ := eventually_atTop.mp hev
  let D := Real.exp ((T : ℝ) ^ (ε / (2 * A)))
  have hD : 0 < D := Real.exp_pos _
  have hD1 : 1 ≤ D := Real.one_le_exp (by positivity)
  refine ⟨D, hD, ?_⟩
  intro n hn Ω _ μ _ Y hY h κ hh hκ hnorm
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by positivity
  by_cases hnT : T ≤ n
  · let q := (n : ℝ) ^ (ε / (2 * A))
    have hq : 1 ≤ q := Real.one_le_rpow hn1 hδ.le
    have hq0 : 0 < q := by positivity
    have heq : q ^ A = (n : ℝ) ^ (ε / 2) := by
      rw [← Real.rpow_mul hn0.le]
      congr 1
      field_simp
    have hscale : C * q ^ A ≤ Real.exp (-1) * (n : ℝ) ^ (κ * ε) := by
      have ht := hT n hnT
      have hm : C ≤ Real.exp (-1) * (n : ℝ) ^ (ε / 2) := by
        have hh' := mul_le_mul_of_nonneg_left ht (Real.exp_pos (-1)).le
        have hex : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
        simpa only [← mul_assoc, hex, one_mul] using hh'
      calc
        C * q ^ A ≤ (Real.exp (-1) * (n : ℝ) ^ (ε / 2)) * (n : ℝ) ^ (ε / 2) := by
          rw [heq]
          exact mul_le_mul_of_nonneg_right hm (by positivity)
        _ = Real.exp (-1) * (n : ℝ) ^ ε := by
          rw [mul_assoc, ← Real.rpow_add hn0]
          congr 2
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith)) (Real.exp_pos _).le
    have hb := measureReal_abs_ge_le_exp_neg_of_eLpNorm_le hY hq0
      (show 0 ≤ C * q ^ A * h by positivity)
      (show 0 < (n : ℝ) ^ (κ * ε) * h by positivity)
      (hnorm q hq) (by nlinarith [mul_le_mul_of_nonneg_right hscale hh.le])
    have hbE : μ {x | (n : ℝ) ^ (κ * ε) * h ≤ |Y x|} ≤
        ENNReal.ofReal (Real.exp (-q)) := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
      exact ENNReal.ofReal_le_ofReal hb
    refine (measure_mono (show {x | (n : ℝ) ^ (κ * ε) * h < |Y x|} ⊆
      {x | (n : ℝ) ^ (κ * ε) * h ≤ |Y x|} from by
        intro x hx
        change (n : ℝ) ^ (κ * ε) * h < |Y x| at hx
        change (n : ℝ) ^ (κ * ε) * h ≤ |Y x|
        exact hx.le)).trans
        (hbE.trans ?_)
    apply ENNReal.ofReal_le_ofReal
    exact le_mul_of_one_le_left (Real.exp_pos _).le hD1
  · have hnT' : (n : ℝ) ≤ T := by exact_mod_cast (Nat.lt_of_not_ge hnT).le
    have hp := Real.rpow_le_rpow hn0.le hnT' hδ.le
    have he : 1 ≤ D * Real.exp (-(n : ℝ) ^ (ε / (2 * A))) := by
      dsimp [D]
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    exact (prob_le_one (μ := μ)).trans
      (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal he)

/-- Internal simultaneous cutoff bound for at most `n²` coefficients. The
stretched exponential power is independent of the probability space and of
the moment prefactor. -/
theorem finite_moment_cutoffs {A ε C : ℝ} (hA : 0 < A) (hε : 0 < ε) (hC : 0 < C) :
    ∃ D c : ℝ, 0 < D ∧ 0 < c ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
        (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : ι → Ω → ℝ)
        (h : ι → ℝ) (κ : ℝ), Fintype.card ι ≤ n ^ 2 →
        (∀ i, Measurable (Y i)) → (∀ i, 0 < h i) → 1 ≤ κ →
        (∀ i q, 1 ≤ q → eLpNorm (Y i) (ENNReal.ofReal q) μ ≤
          ENNReal.ofReal (C * q ^ A * h i)) →
        μ {x | ∃ i, (n : ℝ) ^ (κ * ε) * h i < |Y i x|} ≤
          ENNReal.ofReal (D * Real.exp (-c * (n : ℝ) ^ (ε / (2 * A)))) := by
  classical
  obtain ⟨D, hD, ht⟩ := moment_cutoff_tail hA hε hC
  have hδ : 0 < ε / (2 * A) := by positivity
  obtain ⟨K, hK, hAbsorb⟩ := exists_rpow_mul_exp_neg_le
    (a := 2) hδ (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨D * (K + 1), 1 / 2, by positivity, by norm_num, ?_⟩
  intro n hn Ω ι _ _ μ _ Y h κ hcard hY hh hκ hnorm
  have hunion : {x | ∃ i, (n : ℝ) ^ (κ * ε) * h i < |Y i x|} =
      ⋃ i, {x | (n : ℝ) ^ (κ * ε) * h i < |Y i x|} := by ext x; simp
  rw [hunion]
  calc
    _ ≤ ∑ i, μ {x | (n : ℝ) ^ (κ * ε) * h i < |Y i x|} := measure_iUnion_fintype_le μ _
    _ ≤ ∑ _i : ι, ENNReal.ofReal (D * Real.exp (-(n : ℝ) ^ (ε / (2 * A)))) :=
      Finset.sum_le_sum fun i _ => ht n hn μ (Y i) (hY i) (h i) κ (hh i) hκ (hnorm i)
    _ = ENNReal.ofReal ((Fintype.card ι : ℝ) *
        (D * Real.exp (-(n : ℝ) ^ (ε / (2 * A))))) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hcard' : (Fintype.card ι : ℝ) ≤ (n : ℝ) ^ (2 : ℝ) := by
        rw [Real.rpow_two]
        exact_mod_cast hcard
      have ha := hAbsorb (n : ℝ) hn1
      have hstart := mul_le_mul_of_nonneg_right hcard'
        (show 0 ≤ D * Real.exp (-(n : ℝ) ^ (ε / (2 * A))) by positivity)
      have hh' := mul_le_mul_of_nonneg_left ha hD.le
      simp only [neg_one_mul] at hh'
      nlinarith [Real.exp_pos (-(1 / 2) * (n : ℝ) ^ (ε / (2 * A)))]

/-- The fourth-moment Hölder step used in Subsection 5.1. The
restricted norm is the norm of the observable on the exceptional event. -/
theorem restricted_two_norm_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Y : Ω → ℝ} (hY : Measurable Y) (E : Set Ω)
    {M C t : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hmom : eLpNorm Y 4 μ ≤ ENNReal.ofReal M)
    (hprob : μ E ≤ ENNReal.ofReal (C * Real.exp (-t))) :
    eLpNorm Y 2 (μ.restrict E) ≤
      ENNReal.ofReal (M * C ^ (1 / 4 : ℝ) * Real.exp (-t / 4)) := by
  have hholder := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := μ.restrict E) (f := Y) (p := 2) (q := 4) (by norm_num)
    hY.aestronglyMeasurable.restrict
  have hex : (1 / (2 : ℝ≥0∞).toReal - 1 / (4 : ℝ≥0∞).toReal) = (1 / 4 : ℝ) := by
    norm_num
  rw [hex, Measure.restrict_apply_univ] at hholder
  have hnorm := (eLpNorm_restrict_le Y 4 μ E).trans hmom
  have hp : μ E ^ (1 / 4 : ℝ) ≤ ENNReal.ofReal (C * Real.exp (-t)) ^ (1 / 4 : ℝ) :=
    ENNReal.rpow_le_rpow hprob (by norm_num)
  refine hholder.trans ((mul_le_mul hnorm hp (by positivity) (by positivity)).trans_eq ?_)
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ← ENNReal.ofReal_mul hM, Real.mul_rpow hC (Real.exp_pos _).le,
    ← Real.exp_mul]
  congr 1
  rw [show -t * (1 / 4 : ℝ) = -t / 4 by ring]
  ring

end Riesz2.MomentEvent
