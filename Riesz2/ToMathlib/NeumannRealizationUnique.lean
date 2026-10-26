/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.IsNeumannRealization
public import Riesz2.ToMathlib.ScalarFormEmbeddingInverse

/-!
# Uniqueness of the scalar Neumann realization

The full gradient graph determines both the scalar domain and every mixed
energy pairing. Thus two realizations of that graph are equal as scalar
forms, including their domains.
-/

public section
noncomputable section

open MeasureTheory

namespace Riesz2.NeumannRealization

/-- The literal Neumann graph determines the whole scalar form. -/
theorem unique {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] {μ : Measure E} {U : Set E}
    (P Q : ScalarFormData μ)
    (hP : IsNeumannRealization U P) (hQ : IsNeumannRealization U Q) : P = Q := by
  have hD : P.1 = Q.1 := by
    ext f
    exact (hP.1 f).trans (hQ.1 f).symm
  apply ScalarFormEmbedding.formData_ext P Q hD
  intro f g
  obtain ⟨df, hdf⟩ := (hP.1 f.val).mp f.property
  obtain ⟨dg, hdg⟩ := (hP.1 g.val).mp g.property
  rw [hP.2.2 f g df dg hdf hdg]
  exact (hQ.2.2 _ _ df dg hdf hdg).symm

end Riesz2.NeumannRealization
