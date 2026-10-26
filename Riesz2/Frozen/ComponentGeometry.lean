/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Fin.Basic

/-!
# Geometry of component labels: `Riesz2.ComponentGeometry`

A finite component set embedded in the integer line or an ambient cycle, for the estimates
of Section 4. A subset retains its ambient labels and the distance between them.
-/

@[expose] public section

noncomputable section


namespace Riesz2

/-- A finite component set embedded in the integer line or an ambient cycle, for the estimates
of Section 4. A subset retains its ambient labels and the distance between them. -/
@[reducible] def ComponentGeometry (ι : Type*) :=
  (ι ↪ ℤ) ⊕ (Σ m : ℕ+, ι ↪ Fin (m : ℕ))

end Riesz2

end
end
