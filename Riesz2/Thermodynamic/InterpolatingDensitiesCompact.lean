/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.LengthVariancePart2

/-!
# Compatibility import for compact-temperature penalty estimates

The fixed-power expectation estimate following equation (6.27) in Proposition 6.6 of the
paper is proved in `Riesz2.Thermodynamic.OrdinaryGapCauchyCompact`. This compatibility
module retains the import of its supporting compact-temperature estimates.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Riesz2.InterpolatingDensities

end Riesz2.InterpolatingDensities
