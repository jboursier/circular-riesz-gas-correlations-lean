/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.FullIntrinsicTiltedGapLaw
public import Riesz2.Frozen.ProperMarginalDomain
public import Riesz2.Frozen.IntrinsicGapDomain
public import Riesz2.Frozen.FullPhysicalPotentialValue
public import Riesz2.Frozen.GapAmbientDomain
public import Riesz2.Frozen.HessianMatrix
public import Riesz2.Frozen.IsEuclideanGibbsPotential
public import Riesz2.Frozen.IsClosedScalarDirichletForm
public import Riesz2.Frozen.IsConservativeScalarForm
public import Riesz2.Frozen.WeightedWeakSolution
public import Riesz2.Frozen.ZeroSumComponents
public import Riesz2.Frozen.OfShort
public import Riesz1.Frozen.CyclicIndexDistance
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Riesz2.Main.ShortPhysicalDecay

/-!
# Decay for short-range physical gap laws: `Riesz2.shortPhysicalDecay`

The short-range decay estimate for proper marginals and constrained full cycles, with either
gap penalty. Each law admits a smooth potential and a closed intrinsic form. Every bounded
L² source has a unique finite-energy weak solution. The full ambient potential W agrees with
the extension of equation (3.8) on U_N. See Proposition 4.10.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The short-range decay estimate for proper marginals and constrained full cycles, with either
gap penalty. Each law admits a smooth potential and a closed intrinsic form. Every bounded
L² source has a unique finite-energy weak solution. The full ambient potential W agrees with
the extension of equation (3.8) on U_N. See Proposition 4.10. -/
theorem shortPhysicalDecay :
  ∀ s : ShortExponent, ∃ q : ℝ, 0 < q ∧
  ∀ h : ℝ, 0 < h → ∃ δ : ℝ, 0 < δ ∧
  ∀ θ : PhysicalCutoff, ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
  ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
  let p := ofShort β s
  (∀ (N n : ℕ+) (_ : 4 ≤ (N : ℕ)) (_ : 2 ≤ (n : ℕ)),
    2 * (n : ℕ) ≤ (N : ℕ) → ∀ hn : (n : ℕ) ≤ (N : ℕ), ∀ b : Bool,
    let ν := activeTiltedGapLaw p N n hn θ h b
    0 < tiltNormalizer p N n hn θ h b ∧ tiltNormalizer p N n hn θ h b < ⊤ ∧
    IsProbabilityMeasure ν ∧
    ∃ (V : EuclideanSpace ℝ (Fin (n : ℕ)) → ℝ) (Q : ScalarFormData ν),
      IsEuclideanGibbsPotential volume ν (properMarginalDomain n N) V ∧
      IsNeumannRealization (properMarginalDomain n N) Q ∧
      IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
      ∀ i₀ : Fin (n : ℕ), (n : ℕ) ≤ 4 * (i₀.val + 1) →
        4 * (i₀.val + 1) ≤ 3 * (n : ℕ) →
        ∀ χ : Lp ℝ 2 ν, eLpNorm χ ∞ ν < ⊤ →
        (∃! u : Fin (n : ℕ) → Q.1,
          WeightedWeakSolution Q (hessianMatrix V) ⊤ (fun i => if i = i₀ then χ else 0) u) ∧
        (∀ u : Fin (n : ℕ) → Q.1,
          WeightedWeakSolution Q (hessianMatrix V) ⊤ (fun i => if i = i₀ then χ else 0) u →
          ∀ j : Fin (n : ℕ), ENNReal.ofReal ‖(u j).val‖ ≤
            ENNReal.ofReal (A * (n : ℝ) ^ (q * h) *
              ((1 + |(j.val : ℝ) - (i₀.val : ℝ)|) ^ (-s.val) +
                (n : ℝ) ^ (-(s.val - 1 / 2)) + (N : ℝ) ^ (-(1 / 2 : ℝ)))) *
              (ENNReal.ofReal ‖χ‖ + ENNReal.ofReal (Real.exp (-c * (n : ℝ) ^ δ)) *
                eLpNorm χ ∞ ν))) ∧
  (∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (b : Bool),
    let ν := fullIntrinsicTiltedGapLaw p N θ h b
    0 < tiltNormalizer p N N (le_refl _) θ h b ∧
    tiltNormalizer p N N (le_refl _) θ h b < ⊤ ∧ IsProbabilityMeasure ν ∧
    ∃ (W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ) (Q : ScalarFormData ν),
      ContDiffOn ℝ (⊤ : ℕ∞) W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = fullPhysicalPotentialValue p N hN θ h b y) ∧
      IsEuclideanGibbsPotential volume ν (intrinsicGapDomain N)
        (fun z => W (WithLp.toLp 2 (fun i => 1 + z.val i))) ∧
      IsNeumannRealization (intrinsicGapDomain N) Q ∧
      IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
      ∀ (i₀ : Fin (N : ℕ)) (χ : Lp ℝ 2 ν), eLpNorm χ ∞ ν < ⊤ →
      let M := fun z : gapTangentSpace N =>
        hessianMatrix W (WithLp.toLp 2 (fun i => 1 + z.val i))
      (∃! u : Fin (N : ℕ) → Q.1, WeightedWeakSolution Q M
        (zeroSumComponents _) (fun i => if i = i₀ then χ else 0) u) ∧
      (∀ u : Fin (N : ℕ) → Q.1, WeightedWeakSolution Q M
          (zeroSumComponents _) (fun i => if i = i₀ then χ else 0) u →
        ∀ j : Fin (N : ℕ), ENNReal.ofReal ‖(u j).val‖ ≤
          ENNReal.ofReal (A * (N : ℝ) ^ (q * h) *
            ((1 + (Riesz1.cyclicIndexDistance N j i₀ : ℝ)) ^ (-s.val) + (N : ℝ)⁻¹)) *
            (ENNReal.ofReal ‖χ‖ + ENNReal.ofReal (Real.exp (-c * (N : ℝ) ^ δ)) *
              eLpNorm χ ∞ ν))) :=
  by exact Riesz2.Main.shortPhysicalDecay

end Riesz2

end
end
