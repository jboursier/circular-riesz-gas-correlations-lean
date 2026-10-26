/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.MesoscopicGapLimitsPart3
public import Riesz2.Frozen.IsMesoscopicSequence

/-!
# Mesoscopic finite-gap variance

The variance limit of Lemma 5.19. The density theorem for a proper block
supplies the hypothesis of the moment convergence argument in
`MesoscopicVariancePart2`. The limit is then expressed for sequences indexed
by the particle number.
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Riesz2.MesoscopicVariance

/-- See Lemma 5.19:
for every volume-indexed mesoscopic sequence with `1 ≤ K N ≤ N`, the variance
of the finite gap block divided by `K N ^ s` converges to the strictly
positive constant `cot (π s / 2) / (2 β π s)`, namely the existing
`Riesz1.countVariance (longParameters β s)`.

The extended variance is finite by `finiteGapBlock_variance_finite`, including
singleton systems and full blocks at initial indices. Mesoscopicity makes
blocks proper eventually, when their actual log-concave densities supply the
moment limit. -/
theorem mesoscopic_variance (s : Riesz1.RieszExponent) (β : InverseTemperature)
    (K : ℕ+ → ℕ+) (hK : IsMesoscopicSequence K)
    (_hKN : ∀ N : ℕ+, K N ≤ N) :
    Tendsto (fun m : ℕ =>
      let N := Riesz1.particleNumber m
      let S := fun X : Riesz1.Configuration N =>
        ∑ i : Fin (K N : ℕ), finiteGapBlock X i
      let h := integrable_finiteGapBlock_sum (ofLong β s) N (K N)
      (Riesz1.variance (gibbsMeasure (ofLong β s) N) S h).toReal /
        (K N : ℝ) ^ s.val) atTop
      (𝓝 (Riesz1.countVariance (longParameters β s))) ∧
      0 < Riesz1.countVariance (longParameters β s) := by
  exact ⟨mesoscopic_finiteGapBlock_variance_limit β s Riesz1.particleNumber
    (fun m => K (Riesz1.particleNumber m)) hK.1 hK.2,
    limiting_variance_pos β s⟩

end Riesz2.MesoscopicVariance

end
