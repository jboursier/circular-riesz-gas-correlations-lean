/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# One-dimensional log-concavity estimates: `Riesz2.External.ThermodynamicLogConcavity`

For a one-dimensional log-concave probability density with mean a and variance v > 0, the
density is at least c/√v when |x−a| ≤ c√v, for a universal c > 0. The associated law
satisfies the smooth Poincaré inequality with coefficient 12v. These are the estimates of
Eldan–Klartag, arXiv:1110.6584v2, Section 2, Lemma 2.1 and Lemma 2.2(b). The density is
relative to Lebesgue measure. Log-concavity is concavity of log on the convex positive
support, with zero allowed elsewhere. Variance and Dirichlet integrals take extended values.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal ContDiff

namespace Riesz2.External

def ThermodynamicLogConcavity : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ f : ℝ → ℝ,
      Measurable f → (∀ x, 0 ≤ f x) →
      ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) →
      (∫⁻ x, ENNReal.ofReal (f x)) = 1 →
      let μ := volume.withDensity (fun x => ENNReal.ofReal (f x))
      ∀ a v : ℝ, Integrable (fun x => x) μ →
        (∫ x, x ∂μ) = a → 0 < v →
        (∫⁻ x, ENNReal.ofReal ((x - a) ^ 2) ∂μ) = ENNReal.ofReal v →
        (∀ x, |x - a| ≤ c * Real.sqrt v → c / Real.sqrt v ≤ f x) ∧
        (∀ h : ℝ → ℝ, ContDiff ℝ ∞ h → MemLp h 2 μ → MemLp (deriv h) 2 μ →
          (∫⁻ x, ENNReal.ofReal ((h x - ∫ y, h y ∂μ) ^ 2) ∂μ) ≤
            ENNReal.ofReal (12 * v) * ∫⁻ x, ENNReal.ofReal ((deriv h x) ^ 2) ∂μ)

end Riesz2.External

end
end
