/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.External.LongRangeRigidityLocallyUniform
import Riesz2.Main.External.LongRangeRigidityLocallyUniform

/-!
# Locally uniform long-range gap rigidity: `Riesz2.External.longRangeRigidityLocallyUniform`

The gap rigidity estimate of Theorem 1(1) of the companion paper, with constants uniform for
β in compact subsets of (0,+∞). For 0 < b < (1−s/2)/2, the probability that
|N(x_{i+k}−x_i)−k| ≥ k^{s/2+b} is at most C exp(−c k^{b/(4(s+2))}), uniformly in the volume,
label and 1 ≤ k ≤ floor(N/2). Compact-temperature uniformity follows from the proof of the
companion theorem. See also Lemma 2.2 of the paper. The theorem is proved in
`Riesz2.Main.External.LongRangeRigidityLocallyUniform`.
-/

@[expose] public section

namespace Riesz2.External

theorem longRangeRigidityLocallyUniform : Riesz2.External.LongRangeRigidityLocallyUniform :=
  by exact Riesz2.Main.External.longRangeRigidityLocallyUniform

end Riesz2.External

end
