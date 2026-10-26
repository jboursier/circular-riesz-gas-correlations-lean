/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.External.PeriodicZeta
import Riesz2.Main.External.PeriodicZeta

/-!
# Periodic-zeta connection formula: `Riesz2.External.periodicZeta`

The connection between the symmetrized Hurwitz zeta function and the cosine series ∑_{n≥1}
n^{-s} cos(2πnx), for 0 < s < 1 and 0 < x < 1. This is DLMF equation (25.13.3), added at x
and 1−x. The series is interpreted through ordered partial sums because it is conditionally
convergent. On this interval Mathlib’s unit-circle Hurwitz zeta agrees with the usual
Hurwitz zeta. The theorem is proved in `Riesz2.Main.External.PeriodicZeta`.
-/

@[expose] public section

namespace Riesz2.External

theorem periodicZeta : Riesz2.External.PeriodicZeta :=
  by exact Riesz2.Main.External.periodicZeta

end Riesz2.External

end
