/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.External.ThermodynamicLogConcavity
import Riesz2.Main.External.ThermodynamicLogConcavity

/-!
# One-dimensional log-concavity estimates: `Riesz2.External.thermodynamicLogConcavity`

For a one-dimensional log-concave probability density with mean a and variance v > 0, the
density is at least c/√v when |x−a| ≤ c√v, for a universal c > 0. The associated law
satisfies the smooth Poincaré inequality with coefficient 12v. These are the estimates of
Eldan–Klartag, arXiv:1110.6584v2, Section 2, Lemma 2.1 and Lemma 2.2(b). The density is
relative to Lebesgue measure. Log-concavity is concavity of log on the convex positive
support, with zero allowed elsewhere. Variance and Dirichlet integrals take extended values.
The theorem is proved in `Riesz2.Main.External.ThermodynamicLogConcavity`.
-/

@[expose] public section

namespace Riesz2.External

theorem thermodynamicLogConcavity : Riesz2.External.ThermodynamicLogConcavity :=
  by exact Riesz2.Main.External.thermodynamicLogConcavity

end Riesz2.External

end
