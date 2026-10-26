/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.AdmissibleParticlePairs
public import Riesz2.Frozen.PairGibbsMeasure
public import Riesz2.Frozen.PairAmbientGapPotential
public import Riesz2.Frozen.IntrinsicGapLaw
public import Riesz2.Frozen.IntrinsicGapDomain
public import Riesz2.Frozen.HessianMatrix
public import Riesz2.Frozen.IsEuclideanGibbsPotential
public import Riesz2.Frozen.IsClosedScalarDirichletForm
public import Riesz2.Frozen.IsConservativeScalarForm
public import Riesz2.Frozen.ScalarPoissonSolution
public import Riesz2.Frozen.WeightedWeakSolution
public import Riesz2.Frozen.ZeroSumComponents
public import Riesz2.Frozen.GapMultiplierField
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Riesz2.HelfferSjostrand.GapRepresentationPart3

/-!
# Proof of helffer–Sjöstrand representation in gap coordinates

Under Assumptions 3.1, the intrinsic gap law admits a mean-zero scalar Poisson solution and
a unique tangent finite-energy gradient solving the Helffer–Sjöstrand equation. The
statement includes covariance and variance identities, the variational characterization over
tangent fields, and the Hessian form on gradients. The ambient multiplier is tested against
smooth compactly supported functions, with local integrability asserted. See Proposition 3.3
and Appendix A. The proof is `Riesz2.GapRepresentation.gap_representation`.
-/

public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2.Main

/-- Under Assumptions 3.1, the intrinsic gap law admits a mean-zero scalar Poisson solution and
a unique tangent finite-energy gradient solving the Helffer–Sjöstrand equation. The
statement includes covariance and variance identities, the variational characterization over
tangent fields, and the Hessian form on gradients. The ambient multiplier is tested against
smooth compactly supported functions, with local integrability asserted. See Proposition 3.3
and Appendix A. -/
theorem gapRepresentation :
  ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (c : ℝ), 0 < c →
  ∀ χ : ParticlePairData N, AdmissibleParticlePairs hN χ c →
  ∃ (hMeas : Measurable (fun X : Riesz1.Configuration N =>
      ENNReal.ofReal (Real.exp (-particlePairEnergy χ (WithLp.toLp 2 X.val)))))
    (hZ : 0 < pairGibbsNormalizer χ ∧ pairGibbsNormalizer χ < ⊤),
  let μ := pairGibbsMeasure χ hMeas hZ
  let ν := intrinsicGapLaw μ
  let Ω := intrinsicGapDomain N
  let M := fun z : gapTangentSpace N =>
    hessianMatrix (pairAmbientGapPotential χ) (WithLp.toLp 2 (fun i => 1 + z.val i))
  IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧
  ∃ Q : ScalarFormData ν,
    IsEuclideanGibbsPotential volume ν Ω
      (fun z => pairAmbientGapPotential χ (WithLp.toLp 2 (fun i => 1 + z.val i))) ∧
    IsNeumannRealization Ω Q ∧ IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
    ∀ G : Q.1, ∃ (gG : Lp (gapTangentSpace N) 2 ν) (v : Fin (N : ℕ) → Lp ℝ 2 ν),
      (G.val, gG) ∈ neumannSobolevGraph ν Ω ∧
      (∀ᵐ z ∂ν, ∀ i, v i z = (gG z).val i) ∧
      (∃! ψ : Q.1, ScalarPoissonSolution Q G ψ) ∧
      ∀ ψ : Q.1, ScalarPoissonSolution Q G ψ →
      ∃ (u : Fin (N : ℕ) → Q.1) (gψ : Lp (gapTangentSpace N) 2 ν),
        WeightedWeakSolution Q M (zeroSumComponents _) v u ∧
        (∀ w : Fin (N : ℕ) → Q.1,
          WeightedWeakSolution Q M (zeroSumComponents _) v w → w = u) ∧
        (ψ.val, gψ) ∈ neumannSobolevGraph ν Ω ∧
        (∀ᵐ z ∂ν, ∀ i, (u i).val z = (gψ z).val i) ∧
        MemLp (fun X : Riesz1.Configuration N =>
          G.val (centeredGapChart N (WithLp.toLp 2 (gapVector X)))) 2 μ ∧
        ProbabilityTheory.variance (fun X : Riesz1.Configuration N =>
          G.val (centeredGapChart N (WithLp.toLp 2 (gapVector X)))) μ =
            ∑ i, inner ℝ (v i) (u i).val ∧
        (∀ (K : Q.1) (gK : Lp (gapTangentSpace N) 2 ν),
          (K.val, gK) ∈ neumannSobolevGraph ν Ω →
          Integrable K.val ν ∧
          ProbabilityTheory.covariance G.val K.val ν = inner ℝ gK gψ) ∧
        (∀ w : Fin (N : ℕ) → Q.1, WeightedFormDomain Q M (zeroSumComponents _) w →
          let Ju := (∑ i, Q.2 (u i) (u i)) +
            (∫ z, matrixFieldPair M (fun i => (u i).val) (fun i => (u i).val) z ∂ν) -
              2 * (∑ i, inner ℝ (v i) (u i).val)
          let Jw := (∑ i, Q.2 (w i) (w i)) +
            (∫ z, matrixFieldPair M (fun i => (w i).val) (fun i => (w i).val) z ∂ν) -
              2 * (∑ i, inner ℝ (v i) (w i).val)
          Ju ≤ Jw ∧ (Jw = Ju → w = u)) ∧
        (∃ du : Fin (N : ℕ) → Lp (gapTangentSpace N) 2 ν,
          (∀ i, ((u i).val, du i) ∈ neumannSobolevGraph ν Ω) ∧
          (∑ i, Q.2 (u i) (u i)) = ∑ i, ‖du i‖ ^ 2) ∧
        (∀ φ : gapTangentSpace N → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Ω → Integrable (fun z => gapMultiplierField N Q M v u z * φ z) ν) ∧
        (∀ h : Fin (N : ℕ) → gapTangentSpace N → ℝ,
          (∀ i, ContDiff ℝ (⊤ : ℕ∞) (h i) ∧ HasCompactSupport (h i) ∧ tsupport (h i) ⊆ Ω) →
          ∃ k : Fin (N : ℕ) → Q.1,
            (∀ᵐ z ∂ν, ∀ i, (k i).val z = h i z) ∧
            Integrable (matrixFieldPair M (fun i => (u i).val) (fun i => (k i).val)) ν ∧
            (∑ i, Q.2 (u i) (k i)) +
              (∫ z, matrixFieldPair M (fun i => (u i).val) (fun i => (k i).val) z ∂ν) =
                (∑ i, inner ℝ (v i) (k i).val) +
                  ∫ z, gapMultiplierField N Q M v u z * (∑ i, h i z) ∂ν) :=
  Riesz2.GapRepresentation.gap_representation

end Riesz2.Main
