/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.External.LogConcaveConvergence
import Riesz2.Main.External.LogConcaveConvergence

/-!
# Convergence of log-concave densities: `Riesz2.External.logConcaveConvergence`

Weak convergence of log-concave probability densities on ℝᵈ gives a log-concave
representative of the limit and convergence in L¹. If the limit has an exponential envelope
with rate a₀, convergence also holds with weight exp(a‖x‖) for 0 < a < a₀. Every log-concave
probability density has an exponential envelope. These are the results of Cule–Samworth,
Section 2, Lemma 1 and Proposition 2(a),(c). Densities are relative to Euclidean Lebesgue
measure, and weak convergence is tested against bounded continuous real functions. The
theorem is proved in `Riesz2.Main.External.LogConcaveConvergence`.
-/

@[expose] public section

namespace Riesz2.External

theorem logConcaveConvergence : Riesz2.External.LogConcaveConvergence :=
  by exact Riesz2.Main.External.logConcaveConvergence

end Riesz2.External

end
