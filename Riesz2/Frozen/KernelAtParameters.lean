/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.Parameters
public import Riesz2.Frozen.ShortKernel
public import Riesz1.Frozen.RieszKernel

/-!
# Periodic Riesz kernel in both regimes: `Riesz2.kernelAtParameters`

The noncollision circle kernel g_s for either 0 < s < 1 or s > 1, using the corresponding
long-range or short-range definition. See Subsection 1.1 and Subsection 3.2.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The noncollision circle kernel g_s for either 0 < s < 1 or s > 1, using the corresponding
long-range or short-range definition. See Subsection 1.1 and Subsection 3.2. -/
def kernelAtParameters (p : Parameters) (x : {x : UnitAddCircle // x ≠ 0}) : ℝ :=
  if h : p.val.2 < 1 then Riesz1.rieszKernel ⟨p.val.2, p.property.2.1, h⟩ x
  else shortKernel ⟨p.val.2,
    lt_of_le_of_ne (le_of_not_gt h) (Ne.symm p.property.2.2)⟩ x

end Riesz2

end
end
