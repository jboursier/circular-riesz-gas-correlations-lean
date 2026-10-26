/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.GapTangentSpace
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Hessian of a Euclidean potential: `Riesz2.hessianMatrix`

The matrix ∇²V in Euclidean coordinates, used in Subsections 3.1 and 3.2. The physical
statements evaluate it on open sets where V is smooth.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The matrix ∇²V in Euclidean coordinates, used in Subsections 3.1 and 3.2. The physical
statements evaluate it on open sets where V is smooth. -/
def hessianMatrix {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (fderiv ℝ (gradient V) x (EuclideanSpace.single j 1)) i

end Riesz2

end
end
