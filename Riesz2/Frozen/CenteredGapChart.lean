/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.GapTangentSpace

/-!
# Centering gap coordinates: `Riesz2.centeredGapChart`

The orthogonal projection y ↦ y − N⁻¹(∑ᵢ yᵢ)1 onto the zero-sum subspace. On the mass-N
hyperplane this is the intrinsic chart y ↦ y − 1 for the simplex 𝓜_N of Subsection 3.2.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The orthogonal projection y ↦ y − N⁻¹(∑ᵢ yᵢ)1 onto the zero-sum subspace. On the mass-N
hyperplane this is the intrinsic chart y ↦ y − 1 for the simplex 𝓜_N of Subsection 3.2. -/
def centeredGapChart (N : ℕ+) (y : EuclideanSpace ℝ (Fin (N : ℕ))) : gapTangentSpace N :=
  ⟨WithLp.toLp 2 (fun i => y i - (∑ j, y j) / (N : ℝ)), by
    change (∑ i, (y i - (∑ j, y j) / (N : ℝ))) = 0
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt N.pos)
    field_simp
    ring⟩

end Riesz2

end
end
