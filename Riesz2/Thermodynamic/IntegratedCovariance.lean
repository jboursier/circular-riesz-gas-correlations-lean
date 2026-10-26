/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.ConditionalWellPosednessPart2

/-!
# Intrinsic equations along the common-simplex interpolation

The analytic clause of Subsection 6.1 is specialized to the two-sided penalty at scale
`n⁻ε`. Every energy is identified with the ambient physical energy on the common
simplex.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff ENNReal

namespace Riesz2.IntegratedCovariance

/-- Analytic clause of Subsection 6.1: the common-simplex
interpolants with the exact penalty of Subsection 6.1 have smooth normalized
Gibbs realizations, strictly positive tangent Hessians, a uniform collision
barrier, and the intrinsic scalar/vector covariance and weak equations.
Here the active block has `n+1 ≥ 2` gaps and both exteriors are nonempty.
No typicality or admissibility premise is imposed on the exteriors. -/
theorem conditional_intrinsic_equations (p : Parameters) (n m r : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin ((n + 1) + m + 1)))
    (τ : Equiv.Perm (Fin ((n + 1) + r + 1))) {L : ℝ} (hL : 0 < L)
    (y : EuclideanSpace ℝ (Fin (m + 1))) (hy : ∀ j, 0 < y j)
    (z : EuclideanSpace ℝ (Fin (r + 1))) (hz : ∀ j, 0 < z j)
    (hcompatY : L + ∑ j, y j = ((n + 1 + m : ℕ) + 1 : ℝ))
    (hcompatZ : L + ∑ j, z j = ((n + 1 + r : ℕ) + 1 : ℝ))
    (θ : PhysicalCutoff) (ε : ℝ) (_hε : 0 < ε) :
    let Ω := AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L
    let P := fun w : AffineSimplex.Tangent n => ∑ i,
      (θ.val (((n + 1 : ℕ) : ℝ) ^ (-ε) * AffineSimplex.centredChart n L w i) +
        θ.val (((n + 1 : ℕ) : ℝ) ^ (-ε) * (AffineSimplex.centredChart n L w i)⁻¹))
    ∃ Ky Kz : AffineSimplex.Tangent n → ℝ,
      (∀ w (hw : w ∈ Ω), Ky w = physicalAmbientGapEnergy p (n + 1 + m).succPNat
        ⟨RetainedSimplex.assemble (n + 1) m σ (AffineSimplex.centredChart n L w) y,
          PhysicalEnergy.simplex_subset_ambient _ _ (by
            have hh := ConditionalWellPosedness.assemble_fixed_exterior_mem n m σ y hy hcompatY hw
            rw [AffineSimplex.massSimplex_physical] at hh
            exact hh)⟩) ∧
      (∀ w (hw : w ∈ Ω), Kz w = physicalAmbientGapEnergy p (n + 1 + r).succPNat
        ⟨RetainedSimplex.assemble (n + 1) r τ (AffineSimplex.centredChart n L w) z,
          PhysicalEnergy.simplex_subset_ambient _ _ (by
            have hh := ConditionalWellPosedness.assemble_fixed_exterior_mem n r τ z hz hcompatZ hw
            rw [AffineSimplex.massSimplex_physical] at hh
            exact hh)⟩) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) 1,
        let V := fun w => p.val.1 * (P w + (1 - t) * Ky w + t * Kz w)
        ∃ ρ : Measure (AffineSimplex.Tangent n),
        IsEuclideanGibbsPotential volume ρ Ω V ∧
          (∀ w ∈ Ω, ∀ u : AffineSimplex.Tangent n,
            (2 * p.val.1 * (p.val.2 * (p.val.2 + 1)) * L ^ (-p.val.2 - 2)) * ‖u‖ ^ 2 ≤
              fderiv ℝ (fderiv ℝ V) w u u) ∧
          (∀ w ∈ Ω, (Metric.infDist w (frontier Ω))⁻¹ ^ 2 - B ≤
            ‖gradient V w‖ ^ 2 / 4 - Laplacian.laplacian V w / 2) ∧
          ∀ e : AffineSimplex.Tangent n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
            let ρ' := ρ.map e
            let U := e '' Ω
            let W := V ∘ e.symm
            ∃ hW : IsEuclideanGibbsPotential volume ρ' U W,
            let hU := e.toHomeomorph.isOpenMap Ω (ConditionalWellPosedness.fibre_isOpen n L)
            let hB := e.isometry.lipschitzWith.isBounded_image (ConditionalWellPosedness.fibre_isBounded n L)
            ConditionalWellPosedness.EuclideanWellPosed hU hB hW := by
  simpa only [ite_true] using
    ConditionalWellPosedness.compatible_conditionals_wellposed p n m r hn σ τ hL
      y hy z hz hcompatY hcompatZ θ
      (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)) (-ε))
      Finset.univ true

end Riesz2.IntegratedCovariance
