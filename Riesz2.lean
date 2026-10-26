/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.LongRangeGapCorrelations
public import Riesz2.Frozen.ShortRangeGapCorrelations
public import Riesz2.Frozen.Convergence
public import Riesz2.Frozen.QuantitativeConvergence
public import Riesz2.Frozen.Hyperuniformity
public import Riesz2.Frozen.Repulsion

/-!
# Decay of correlations and thermodynamic limit for the circular Riesz gas

Lean formalization of J. Boursier, *Decay of correlations and thermodynamic limit for the
circular Riesz gas* (arXiv:2209.00396). Importing this module gives the six main results:

* `Riesz2.longRangeGapCorrelations`: Theorem 1, decay of gap correlations for `0 < s < 1`.
* `Riesz2.shortRangeGapCorrelations`: Theorem 2, decay of gap correlations for `s > 1`.
* `Riesz2.convergence`: Theorem 3, convergence of the gas to the `Riesz_{s,β}` process.
* `Riesz2.quantitativeConvergence`: Theorem 4, a rate for this convergence.
* `Riesz2.hyperuniformity`: Corollary 1.1, hyperuniformity of the `Riesz_{s,β}` process.
* `Riesz2.repulsion`: Proposition 1.2, repulsion of neighbouring particles.

Each statement lives in its own file under `Riesz2/Frozen/`, together with the definitions it
uses. The formalization builds on that of the companion paper (arXiv:2112.05881), imported as
the package `Riesz1`.
-/
