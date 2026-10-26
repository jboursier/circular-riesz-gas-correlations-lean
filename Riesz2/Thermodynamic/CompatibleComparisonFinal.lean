/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.CompatibleComparisonPart10
public import Riesz2.Thermodynamic.CompatibleComparisonPart11

/-!
# Compatible conditional comparison

The compatible comparison in the proof of Proposition 6.6 follows from the comparison of
`CompatibleComparisonPart11` and the physical differential bounds of
`CompatibleComparisonPart10`.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal ContDiff Topology
namespace Riesz2.CompatibleComparison

/-- See the proof of Proposition 6.6 in the paper: for admissible compatible exteriors `y, z`
of sizes `N ≤ N'` with the same residual length, the conditional laws of the active
block satisfy `|E G - E' G| ≤ C n^(κε-τ/2) (D_A + exp(-c n^δ) D_∞)` for every Lipschitz
observable supported in the middle half. The loss `κ` precedes `ε`, and the tail power
`δ` precedes the compact temperature interval. -/
theorem compatible_conditional_comparison (hzeta : External.PeriodicZeta)
    (hRig : External.LongRangeRigidityLocallyUniform) (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ A K ε₀ κ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧ 0 < κ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    K*ε+min s 1/2 ≤ 1 ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
    ∀ a d e : ℕ, 1 ≤ a → 4*(a+1) ≤ d+1+a+1 → d ≤ e →
      (a+1 : ℝ)^(2/s) ≤ (d+1+a+1 : ℝ) →
    ∀ (L : ℝ), 0 < L →
    ∀ (y : AffineSimplex.chartDomain (d+1) ((d+1+a : ℕ)+1))
      (z : AffineSimplex.chartDomain (e+1) ((e+1+a : ℕ)+1)),
      InterpolantLocalLaws.admissibleExterior p (d+1) a (by omega) θ ε A K y →
      InterpolantLocalLaws.admissibleExterior p (e+1) a (by omega) θ ε A K z →
      ((d+1+a : ℕ)+1 : ℝ)-∑ i, y.val i = L →
      ((e+1+a : ℕ)+1 : ℝ)-∑ i, z.val i = L →
    (∀ x : Fin (a+1) → ℝ,
      x ∈ goodBlockEvent s a.succPNat (d+1+a).succPNat (K*ε) ↔
      (∀ i, (a+1 : ℝ)^(-(K*ε)) ≤ x i ∧ x i ≤ (a+1 : ℝ)^(K*ε)) ∧
      ∀ l r : ℕ, l < r → r ≤ a+1 →
        |(∑ i ∈ Finset.univ.filter (fun i : Fin (a+1) => l ≤ i.val ∧ i.val < r), x i)-
          (r-l : ℕ)| ≤ (a+1 : ℝ)^(K*ε)*(r-l : ℕ)^(min s 1/2)) ∧
    ∃ Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ,
      (∀ u (hu : RetainedSimplex.assemble (d+1) a
        (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u ∈
          gapAmbientDomain (d+1+a).succPNat),
        Ky u = physicalAmbientGapEnergy p (d+1+a).succPNat
          ⟨RetainedSimplex.assemble (d+1) a
            (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u,hu⟩) ∧
      (∀ u (hu : RetainedSimplex.assemble (e+1) a
        (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u ∈
          gapAmbientDomain (e+1+a).succPNat),
        Kz u = physicalAmbientGapEnergy p (e+1+a).succPNat
          ⟨RetainedSimplex.assemble (e+1) a
            (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u,hu⟩) ∧
    let σ := (AffineSimplex.simplexVolume a L).comap Subtype.val
    let P := fun u : AffineSimplex.massSimplex a L =>
      ∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u.val i)+θ.val ((a+1 : ℝ)^(-ε)*(u.val i)⁻¹))
    let w := fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal (Real.exp (-(p.val.1*(P u+Ky u.val))))
    let z' := fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal (Real.exp (-(p.val.1*(P u+Kz u.val))))
    ∃ (hw0 : (∫⁻ u, w u ∂σ) ≠ 0) (hwt : (∫⁻ u, w u ∂σ) ≠ ⊤)
      (hz0 : (∫⁻ u, z' u ∂σ) ≠ 0) (hzt : (∫⁻ u, z' u ∂σ) ≠ ⊤),
    let ρy := AffineFibre.normalizedMeasure σ w hw0 hwt
    let ρz := AffineFibre.normalizedMeasure σ z' hz0 hzt
    ∀ (G : BlockObservable a.succPNat) (J : Finset (Fin (a+1))),
      DependsOnBlockCoordinates G J →
      (∀ i ∈ J, |(i.val : ℝ)+1-(a+1 : ℝ)/2| ≤ (a+1 : ℝ)/4) →
      Integrable (fun u => G.val (WithLp.ofLp u.val)) ρy ∧
      Integrable (fun u => G.val (WithLp.ofLp u.val)) ρz ∧
      |(∫ u, G.val (WithLp.ofLp u.val) ∂ρy)-(∫ u, G.val (WithLp.ofLp u.val) ∂ρz)| ≤
        C*(a+1 : ℝ)^(κ*ε-min s 1/2)*
          (restrictedBlockDerivativeNorm G J (goodBlockEvent s a.succPNat (d+1+a).succPNat (K*ε))+
            Real.exp (-c*(a+1 : ℝ)^δ)*blockDerivativeNorm G) :=
  compatible_conditional_comparison_internal hzeta hRig s hs hs1
    (fun K hK => physical_differential_bounds_uniform_internal s hs hs1 K hK)

end Riesz2.CompatibleComparison
