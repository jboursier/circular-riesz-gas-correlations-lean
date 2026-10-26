/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.ObservableTransfer
public import Riesz2.Frozen.CorrelationFactor
public import Riesz2.Frozen.GapCorrelation
public import Riesz2.Frozen.OfShort
public import Riesz2.ToMathlib.CyclicDistance
public import Riesz1.Rigidity.NoExplosionDensity
public import Riesz1.Rigidity.NoExplosionIntegration

/-!
# Finite-size cases for short-range gap correlations

Supporting steps for Theorem 2: second moments for all finite sizes,
the one-particle case for every derivative representative, and covariance
bounds for bounded sizes.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace Riesz2.DecayShort.ShortRangeResult

/-- The factors in Theorem 2 are nonnegative,
including derivative representatives with exceptional values. -/
theorem internal_correlationFactor_nonneg (p : Parameters) (N : ℕ+) (i : ℤ)
    (f : GapObservable) (c δ : ℝ) (d : ℕ) : 0 ≤ correlationFactor p N i f c δ d :=
  add_nonneg ENNReal.toReal_nonneg
    (mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)

/-- The one-particle second-moment clause of Theorem 2.
No bound on the value of a derivative representative at one is required. -/
theorem internal_gapSecondMoments_one (p : Parameters) (i j : ℤ) (f g : GapObservable) :
    GapSecondMoments p 1 i j f g := by
  have := gibbsMeasure_probability p 1
  have hg (X : Riesz1.Configuration 1) (k : ℤ) : gap X k = 1 :=
    Riesz1.gap_one_particle X k
  simp only [GapSecondMoments, hg]
  exact ⟨memLp_const _, memLp_const _, memLp_const _, memLp_const _⟩

/-- The second-moment clause of Theorem 2, independently
of the decay estimate. It also applies in the long-range regime. -/
theorem internal_gapSecondMoments (p : Parameters) (N : ℕ+)
    (i j : Fin (N : ℕ)) (f g : GapObservable) :
    GapSecondMoments p N i.val j.val f g := by
  by_cases hN : 2 ≤ (N : ℕ)
  · have := gibbsMeasure_probability p N
    have hg (k : ℤ) : MemLp (fun X : Riesz1.Configuration N => gap X k) 2
        (gibbsMeasure p N) := by
      apply MemLp.of_bound (Riesz1.measurable_gap k).aestronglyMeasurable (N : ℝ)
      exact ae_of_all _ fun X => by
        rw [Real.norm_of_nonneg (Riesz1.gap_pos X k).le]
        exact (Riesz1.gap_lt_particle_number hN X k).le
    exact gapSecondMoments_observable p N hN f g i j
      ((memLp_two_iff_integrable_sq (Riesz1.measurable_gap _).aestronglyMeasurable).mp
        (hg i.val) |>.congr (ae_of_all _ fun X => (Real.rpow_two (gap X i.val)).symm))
      ((memLp_two_iff_integrable_sq (Riesz1.measurable_gap _).aestronglyMeasurable).mp
        (hg j.val) |>.congr (ae_of_all _ fun X => (Real.rpow_two (gap X j.val)).symm))
  · have he : N = 1 := PNat.eq (by change (N : ℕ) = 1; have := N.pos; omega)
    subst N
    exact internal_gapSecondMoments_one p _ _ f g

/-- The zero covariance in the one-particle clause of Theorem 2, using the covariance and its finiteness witnesses. -/
theorem internal_gapCorrelation_one (p : Parameters) (i j : ℤ) (f g : GapObservable)
    (hMom : GapSecondMoments p 1 i j f g) :
    gapCorrelation p 1 i j f.val.1 g.val.1 hMom.1 hMom.2.1 = 0 := by
  have := gibbsMeasure_probability p 1
  unfold gapCorrelation
  simp only [show ∀ (X : Riesz1.Configuration 1) (k : ℤ), gap X k = 1 from
    fun X k => Riesz1.gap_one_particle X k, covariance_const_left]

/-- Exactly the one-particle inequality of Theorem 2,
for arbitrary positive decay parameters and all allowed observables. -/
theorem internal_shortRange_one (s : ShortExponent) (β : InverseTemperature)
    (ε C c δ : ℝ) (hC : 0 ≤ C) (i j : Fin (1 : ℕ)) (f g : GapObservable) :
    let p := ofShort β s
    let d := Riesz1.cyclicIndexDistance 1 i j
    ∃ hMom : GapSecondMoments p 1 i.val j.val f g,
      |gapCorrelation p 1 i.val j.val f.val.1 g.val.1 hMom.1 hMom.2.1| ≤
        C * ((1 + (d : ℝ)) ^ (-s.val + ε) + (1 : ℝ) ^ (-1 + ε)) *
          correlationFactor p 1 i.val f c δ d * correlationFactor p 1 j.val g c δ d := by
  intro p d
  refine ⟨internal_gapSecondMoments_one p _ _ f g, ?_⟩
  rw [internal_gapCorrelation_one p _ _ f g (internal_gapSecondMoments_one p _ _ f g),
    abs_zero]
  exact mul_nonneg
    (mul_nonneg (mul_nonneg hC (add_nonneg (Real.rpow_nonneg (by positivity) _)
      (Real.rpow_nonneg zero_le_one _))) (internal_correlationFactor_nonneg ..))
    (internal_correlationFactor_nonneg ..)

/-- Internal bounded-size estimate for Theorem 2.
It uses the exact observable class and proves finiteness separately. -/
theorem internal_covariance_bound (p : Parameters) (N : ℕ+)
    (i j : Fin (N : ℕ)) (f g : GapObservable) :
    |covariance (fun X => f.val.1 (gap X i.val))
        (fun X => g.val.1 (gap X j.val)) (gibbsMeasure p N)| ≤
      2 * ((N : ℝ) + 1) ^ 2 * derivativeSup f * derivativeSup g := by
  have := gibbsMeasure_probability p N
  have hMom := internal_gapSecondMoments p N i j f g
  let F := fun X : Riesz1.Configuration N => f.val.1 (gap X i.val) - f.val.1 1
  let G := fun X : Riesz1.Configuration N => g.val.1 (gap X j.val) - g.val.1 1
  have hF : MemLp F 2 (gibbsMeasure p N) := hMom.1.sub (memLp_const _)
  have hG : MemLp G 2 (gibbsMeasure p N) := hMom.2.1.sub (memLp_const _)
  have hgap (X : Riesz1.Configuration N) (k : ℤ) : gap X k ≤ (N : ℝ) := by
    by_cases hN : 2 ≤ (N : ℕ)
    · exact (Riesz1.gap_lt_particle_number hN X k).le
    · have he : N = 1 := PNat.eq (by change (N : ℕ) = 1; have := N.pos; omega)
      subst N
      rw [show gap X k = 1 from Riesz1.gap_one_particle X k]
      norm_num
  have hbound (f : GapObservable) (k : ℤ) (X : Riesz1.Configuration N) :
      |f.val.1 (gap X k) - f.val.1 1| ≤ derivativeSup f * ((N : ℝ) + 1) := by
    apply (CenteredObservable.abs_observable_sub_le f 1 (gap X k)).trans
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    exact (abs_sub (gap X k) 1).trans (by
      rw [abs_of_pos (show 0 < gap X k from Riesz1.gap_pos X k), abs_one]
      linarith [hgap X k])
  have hFi : |∫ X, F X ∂gibbsMeasure p N| ≤ derivativeSup f * ((N : ℝ) + 1) := by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := gibbsMeasure p N)
        (f := F) (C := derivativeSup f * ((N : ℝ) + 1))
        (ae_of_all _ fun X => by simpa only [Real.norm_eq_abs] using hbound f i.val X)
  have hGi : |∫ X, G X ∂gibbsMeasure p N| ≤ derivativeSup g * ((N : ℝ) + 1) := by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := gibbsMeasure p N)
        (f := G) (C := derivativeSup g * ((N : ℝ) + 1))
        (ae_of_all _ fun X => by simpa only [Real.norm_eq_abs] using hbound g j.val X)
  have hFG : |∫ X, F X * G X ∂gibbsMeasure p N| ≤
      (derivativeSup f * ((N : ℝ) + 1)) * (derivativeSup g * ((N : ℝ) + 1)) := by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := gibbsMeasure p N)
        (f := fun X => F X * G X)
        (C := (derivativeSup f * ((N : ℝ) + 1)) * (derivativeSup g * ((N : ℝ) + 1)))
        (ae_of_all _ fun X => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hbound f i.val X) (hbound g j.val X) (abs_nonneg _)
            (mul_nonneg ENNReal.toReal_nonneg (by positivity)))
  have hc : covariance F G (gibbsMeasure p N) = covariance
      (fun X => f.val.1 (gap X i.val)) (fun X => g.val.1 (gap X j.val))
      (gibbsMeasure p N) := by
    rw [covariance_sub_const_left (hMom.1.integrable one_le_two),
      covariance_sub_const_right (hMom.2.1.integrable one_le_two)]
  rw [← hc, covariance_eq_sub hF hG]
  calc
    _ ≤ |∫ X, F X * G X ∂gibbsMeasure p N| +
        |(∫ X, F X ∂gibbsMeasure p N) * (∫ X, G X ∂gibbsMeasure p N)| := abs_sub _ _
    _ ≤ (derivativeSup f * ((N : ℝ) + 1)) * (derivativeSup g * ((N : ℝ) + 1)) +
        (derivativeSup f * ((N : ℝ) + 1)) * (derivativeSup g * ((N : ℝ) + 1)) := by
      rw [abs_mul]
      exact add_le_add hFG (mul_le_mul hFi hGi (abs_nonneg _)
        (mul_nonneg ENNReal.toReal_nonneg (by positivity)))
    _ = _ := by ring

end Riesz2.DecayShort.ShortRangeResult
