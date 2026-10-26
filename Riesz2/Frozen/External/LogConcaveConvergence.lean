/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Convergence of log-concave densities: `Riesz2.External.LogConcaveConvergence`

Weak convergence of log-concave probability densities on ℝᵈ gives a log-concave
representative of the limit and convergence in L¹. If the limit has an exponential envelope
with rate a₀, convergence also holds with weight exp(a‖x‖) for 0 < a < a₀. Every log-concave
probability density has an exponential envelope. These are the results of Cule–Samworth,
Section 2, Lemma 1 and Proposition 2(a),(c). Densities are relative to Euclidean Lebesgue
measure, and weak convergence is tested against bounded continuous real functions.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology BoundedContinuousFunction

namespace Riesz2.External

def LogConcaveConvergence : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    let E := EuclideanSpace ℝ (Fin d)
    let Density := fun f : E → ℝ =>
      Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∫⁻ x, ENNReal.ofReal (f x)) = 1
    let LogConcave := fun f : E → ℝ =>
      ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x))
    ((∀ (f : ℕ → E → ℝ) (g : E → ℝ),
      (∀ j, Density (f j) ∧ LogConcave (f j)) → Density g →
      (∀ φ : E →ᵇ ℝ,
        Tendsto (fun j => ∫ x, φ x ∂volume.withDensity (fun x => ENNReal.ofReal (f j x)))
          atTop (𝓝 (∫ x, φ x ∂volume.withDensity (fun x => ENNReal.ofReal (g x))))) →
      (∃ g' : E → ℝ, Density g' ∧ LogConcave g' ∧ g' =ᵐ[volume] g) ∧
      Tendsto (fun j => ∫⁻ x, ENNReal.ofReal |f j x - g x|) atTop (𝓝 0) ∧
      (∀ a₀ b₀ : ℝ, 0 < a₀ → (∀ x, g x ≤ Real.exp (-a₀ * ‖x‖ + b₀)) →
        ∀ a : ℝ, 0 < a → a < a₀ →
          Tendsto (fun j => ∫⁻ x, ENNReal.ofReal (Real.exp (a * ‖x‖) * |f j x - g x|))
            atTop (𝓝 0))) ∧
    (∀ f : E → ℝ, Density f → LogConcave f →
      ∃ a : ℝ, 0 < a ∧ ∃ b : ℝ, ∀ x, f x ≤ Real.exp (-a * ‖x‖ + b)))

end Riesz2.External

end
end
