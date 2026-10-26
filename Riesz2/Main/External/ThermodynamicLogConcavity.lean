/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.External.ThermodynamicLogConcavity
public import Riesz2.ToMathlib.External.LogConcavityResult

/-!
# Proof of one-dimensional log-concavity estimates

For a one-dimensional log-concave probability density with mean a and variance v > 0, the
density is at least c/√v when |x−a| ≤ c√v, for a universal c > 0. The associated law
satisfies the smooth Poincaré inequality with coefficient 12v. These are the estimates of
Eldan–Klartag, arXiv:1110.6584v2, Section 2, Lemma 2.1 and Lemma 2.2(b). The density is
relative to Lebesgue measure. Log-concavity is concavity of log on the convex positive
support, with zero allowed elsewhere. Variance and Dirichlet integrals take extended values.
-/

public section

namespace Riesz2.Main.External

/-- For a one-dimensional log-concave probability density with mean a and variance v > 0, the
density is at least c/√v when |x−a| ≤ c√v, for a universal c > 0. The associated law
satisfies the smooth Poincaré inequality with coefficient 12v. These are the estimates of
Eldan–Klartag, arXiv:1110.6584v2, Section 2, Lemma 2.1 and Lemma 2.2(b). The density is
relative to Lebesgue measure. Log-concavity is concavity of log on the convex positive
support, with zero allowed elsewhere. Variance and Dirichlet integrals take extended values. -/
theorem thermodynamicLogConcavity : Riesz2.External.ThermodynamicLogConcavity :=
  Riesz2.ExternalLogConcavity.thermodynamicLogConcavity_result

end Riesz2.Main.External

end
