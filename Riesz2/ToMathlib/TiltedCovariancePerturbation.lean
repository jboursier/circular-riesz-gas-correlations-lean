/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Probability.Moments.Covariance
public import Riesz2.ToMathlib.NonnegativeGibbsTilt
public import Mathlib.Tactic

/-!
# Covariance under a perturbation of the law

Let `μ` and `Q` be probability measures and `A`, `B` be `L²` functions for both. If the means
of `A`, `B` and `A B` change from `μ` to `Q` by at most `K` times their `L²(μ)` norms, then the
covariance changes by at most `K (√∫(AB)² + (2 + K) √∫A² √∫B²)`. The first estimate is a
real inequality, and the second applies it to `covariance_eq_sub`.
-/

public section

open MeasureTheory ProbabilityTheory

namespace Riesz2.TiltedCovariance

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The real inequality behind the covariance comparison. The differences of the means are
controlled by `K` times the scales `sA`, `sB`, `sAB`. -/
theorem real_perturb {a a' b b' p p' sA sB sAB K : ℝ} (hK : 0 ≤ K) (hsA : 0 ≤ sA)
    (ha : |a| ≤ sA) (hb : |b| ≤ sB) (h_a : |a' - a| ≤ K * sA)
    (h_b : |b' - b| ≤ K * sB) (hp : |p' - p| ≤ K * sAB) :
    |(p - a * b) - (p' - a' * b')| ≤ K * sAB + K * (2 + K) * (sA * sB) := by
  have ha' : |a'| ≤ (1 + K) * sA := by
    have h : |a'| ≤ |a| + |a' - a| := by
      calc
        |a'| = |a + (a' - a)| := by ring_nf
        _ ≤ |a| + |a' - a| := abs_add_le _ _
    nlinarith
  have hdecomp : (p - a * b) - (p' - a' * b') =
      (p - p') - ((a - a') * b + a' * (b - b')) := by ring
  rw [hdecomp]
  have h1 : |a - a'| * |b| ≤ K * sA * sB := by
    rw [abs_sub_comm]
    exact mul_le_mul h_a hb (abs_nonneg _) (mul_nonneg hK hsA)
  have h2 : |a'| * |b' - b| ≤ (1 + K) * sA * (K * sB) :=
    mul_le_mul ha' h_b (abs_nonneg _) (mul_nonneg (by linarith) hsA)
  calc
    |(p - p') - ((a - a') * b + a' * (b - b'))|
        ≤ |p - p'| + |(a - a') * b + a' * (b - b')| := abs_sub _ _
    _ ≤ |p - p'| + (|(a - a') * b| + |a' * (b - b')|) := by
        gcongr
        exact abs_add_le _ _
    _ = |p' - p| + (|a - a'| * |b| + |a'| * |b' - b|) := by
        rw [abs_mul, abs_mul, abs_sub_comm p p', abs_sub_comm b' b]
    _ ≤ K * sAB + (K * sA * sB + (1 + K) * sA * (K * sB)) :=
        add_le_add hp (add_le_add h1 h2)
    _ = K * sAB + K * (2 + K) * (sA * sB) := by ring

/-- Covariance comparison under a perturbation of the law. For probability measures `μ`, `Q`
and `L²` functions `A`, `B` with respect to both, if each of `A`, `B`, `A B` has mean change at
most `K` times its `L²(μ)` norm, then
`|cov_μ(A,B) - cov_Q(A,B)| ≤ K (√∫(AB)² + (2 + K) √∫A² √∫B²)`. -/
theorem abs_covariance_sub_covariance_le (μ Q : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure Q] {A B : Ω → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hA : MemLp A 2 μ) (hB : MemLp B 2 μ) (hAQ : MemLp A 2 Q) (hBQ : MemLp B 2 Q)
    (hA' : |∫ ω, A ω ∂Q - ∫ ω, A ω ∂μ| ≤ K * Real.sqrt (∫ ω, A ω ^ 2 ∂μ))
    (hB' : |∫ ω, B ω ∂Q - ∫ ω, B ω ∂μ| ≤ K * Real.sqrt (∫ ω, B ω ^ 2 ∂μ))
    (hAB' : |∫ ω, A ω * B ω ∂Q - ∫ ω, A ω * B ω ∂μ| ≤
      K * Real.sqrt (∫ ω, (A ω * B ω) ^ 2 ∂μ)) :
    |cov[A, B; μ] - cov[A, B; Q]| ≤
      K * (Real.sqrt (∫ ω, (A ω * B ω) ^ 2 ∂μ) +
        (2 + K) * (Real.sqrt (∫ ω, A ω ^ 2 ∂μ) * Real.sqrt (∫ ω, B ω ^ 2 ∂μ))) := by
  rw [covariance_eq_sub hA hB, covariance_eq_sub hAQ hBQ]
  simp only [Pi.mul_apply]
  have ha := NonnegativeTilt.abs_integral_le_sqrt_integral_sq (μ := μ) hA
  have hb := NonnegativeTilt.abs_integral_le_sqrt_integral_sq (μ := μ) hB
  refine le_of_le_of_eq (real_perturb hK (Real.sqrt_nonneg _) ha hb hA'
    hB' hAB') ?_
  ring

end Riesz2.TiltedCovariance
