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
# Axiom report of the main results

Prints the axioms on which each of the six main results depends. `scripts/check_axioms.py`
checks that each report lists exactly `propext`, `Classical.choice` and `Quot.sound`:

```bash
lake env lean Riesz2/Meta/AxiomsAudit.lean 2>&1 | tee .lake/axioms-audit.log
python3 scripts/check_axioms.py .lake/axioms-audit.log
```

The root module `Riesz2` does not import this file, because its `#print axioms` commands run
again whenever the module is rebuilt.
-/

#print axioms Riesz2.longRangeGapCorrelations
#print axioms Riesz2.shortRangeGapCorrelations
#print axioms Riesz2.convergence
#print axioms Riesz2.quantitativeConvergence
#print axioms Riesz2.hyperuniformity
#print axioms Riesz2.repulsion
