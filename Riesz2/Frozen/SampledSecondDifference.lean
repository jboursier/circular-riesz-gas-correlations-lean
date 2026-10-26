/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.SampledRieszKernel

/-!
# Cyclic second difference of the sampled kernel: `Riesz2.sampledSecondDifference`

The difference g_{N,s}''(k) = g_{N,s}(k+1) + g_{N,s}(k−1) − 2g_{N,s}(k), with cyclic
indices. See equation (2.8).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

/-- The difference g_{N,s}''(k) = g_{N,s}(k+1) + g_{N,s}(k−1) − 2g_{N,s}(k), with cyclic
indices. See equation (2.8). -/
def sampledSecondDifference (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (k : Fin (N : ℕ)) : ℝ :=
  sampledRieszKernel s N hN (k + 1) + sampledRieszKernel s N hN (k - 1) -
    2 * sampledRieszKernel s N hN k

end Riesz2

end
end
