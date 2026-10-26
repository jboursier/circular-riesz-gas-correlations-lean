/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.External.ThermodynamicLogConcavity
public import Riesz2.ToMathlib.External.LogConcaveCentralDensity
public import Riesz2.ToMathlib.External.LogConcavePoincarePart2

/-!
# One-dimensional log-concavity estimates

A universal central-density lower bound and a smooth Poincaré inequality with
coefficient `12 * v`. Both use the supplied density and the same extended
variance. The proofs are in `LogConcaveCentralDensity` and
`LogConcavePoincarePart2`.
-/

public section

namespace Riesz2.ExternalLogConcavity

/-- One-dimensional log-concavity estimates: the central-density lower
bound and smooth Poincaré inequality, with one universal positive constant
chosen before the density. -/
theorem thermodynamicLogConcavity_result : Riesz2.External.ThermodynamicLogConcavity := by
  obtain ⟨c, hc, hlower⟩ := LogConcaveCentralDensity.exists_central_density_lower
  refine ⟨c, hc, ?_⟩
  intro f hf hnn hlog hmass
  dsimp only
  intro a v hi hmean hv hvar
  exact ⟨hlower f hf hnn hlog hmass a v hi hmean hv hvar,
    LogConcavePoincare.smooth_poincare f hf hnn hlog hmass a v hi hmean hv hvar⟩

end Riesz2.ExternalLogConcavity
