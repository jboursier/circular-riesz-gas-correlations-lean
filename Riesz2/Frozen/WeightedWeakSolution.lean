/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.WeightedFormDomain

/-!
# Finite-energy weak Helffer–Sjöstrand equation: `Riesz2.WeightedWeakSolution`

The equation (M + L)u = v tested on the full finite-energy domain of S-valued fields. The
source v belongs to L², and each matrix cross pairing is integrable. In the particle setting
it agrees with `Riesz1.hsNonGradientFullBilinear`. See Subsection 3.5, Lemma 4.4 and
Subsection 5.1.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The equation (M + L)u = v tested on the full finite-energy domain of S-valued fields. The
source v belongs to L², and each matrix cross pairing is integrable. In the particle setting
it agrees with `Riesz1.hsNonGradientFullBilinear`. See Subsection 3.5, Lemma 4.4 and
Subsection 5.1. -/
def WeightedWeakSolution {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {ρ : Measure α} (Q : ScalarFormData ρ) (M : α → Matrix ι ι ℝ)
    (S : Submodule ℝ (ι → ℝ)) (v : ι → Lp ℝ 2 ρ) (u : ι → Q.1) : Prop :=
  WeightedFormDomain Q M S u ∧
  ∀ h : ι → Q.1, WeightedFormDomain Q M S h →
    Integrable (matrixFieldPair M (fun i => (u i).val) (fun i => (h i).val)) ρ ∧
    (∑ i, Q.2 (u i) (h i)) +
      (∫ x, matrixFieldPair M (fun i => (u i).val) (fun i => (h i).val) x ∂ρ) =
        ∑ i, inner ℝ (v i) (h i).val

end Riesz2

end
end
