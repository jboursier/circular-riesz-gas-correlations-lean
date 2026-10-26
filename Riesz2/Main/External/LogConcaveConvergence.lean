/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.External.LogConcaveConvergence
public import Riesz2.ToMathlib.External.LogConcaveConvergenceResult

/-!
# Proof of convergence of log-concave densities

Weak convergence of log-concave probability densities on ℝᵈ gives a log-concave
representative of the limit and convergence in L¹. If the limit has an exponential envelope
with rate a₀, convergence also holds with weight exp(a‖x‖) for 0 < a < a₀. Every log-concave
probability density has an exponential envelope. These are the results of Cule–Samworth,
Section 2, Lemma 1 and Proposition 2(a),(c). Densities are relative to Euclidean Lebesgue
measure, and weak convergence is tested against bounded continuous real functions.
-/

public section

namespace Riesz2.Main.External

/-- Weak convergence of log-concave probability densities on ℝᵈ gives a log-concave
representative of the limit and convergence in L¹. If the limit has an exponential envelope
with rate a₀, convergence also holds with weight exp(a‖x‖) for 0 < a < a₀. Every log-concave
probability density has an exponential envelope. These are the results of Cule–Samworth,
Section 2, Lemma 1 and Proposition 2(a),(c). Densities are relative to Euclidean Lebesgue
measure, and weak convergence is tested against bounded continuous real functions. -/
theorem logConcaveConvergence : Riesz2.External.LogConcaveConvergence :=
  Riesz2.ExternalLogConcave.logConcaveConvergence_result

end Riesz2.Main.External

end
