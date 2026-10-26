/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.AlmostOptimalRigidity
public import Riesz2.Frozen.GibbsMeasure
public import Riesz2.Frozen.OfLong
public import Riesz2.Frozen.InverseTemperature
public import Mathlib.Tactic

/-!
# Gap rigidity from the companion paper

The gap part of Theorem 1(1) of the companion paper follows from
`Riesz1.almost_optimal_rigidity`. It yields Lemma 2.2 of the paper,
with the statement encoded by `Riesz2.nearOptimalRigidity`.

For `s < 1`, the long-range Gibbs law `Riesz2.gibbsMeasure` is the Riesz 1 law
on `Riesz1.Configuration N` by definition.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz2

/-- For `s < 1`, the Gibbs law `Riesz2.gibbsMeasure` at `Riesz2.ofLong β s` is the Riesz 1 Gibbs
law with parameters `(β, s)` on the configurations of `N` labels. -/
theorem gibbsMeasure_ofLong (β : InverseTemperature) (s : Riesz1.RieszExponent) (N : ℕ+) :
    gibbsMeasure (ofLong β s) N =
      Riesz1.gibbsMeasure ⟨(β.val, s.val), β.property, s.property.1, s.property.2⟩ N := by
  have h : (ofLong β s).val.2 < 1 := s.property.2
  unfold gibbsMeasure
  simp only [h, ↓reduceDIte]
  rfl

/-- The gap estimate from Theorem 1(1) of the companion paper.
Let `0 < s < 1` and `β > 0`. Then there exists `ε₀ > 0` such that, for every `0 < ε < ε₀`, there
exist `C, c > 0`, depending only on `β, s, ε`, such that for every integer `N ≥ 2`, every label
`i ∈ {1, …, N}` and every integer `1 ≤ k ≤ ⌊N/2⌋`, the Gibbs probability of
`|N(x_{i+k} - x_i) - k| ≥ k^{s/2 + ε}` is at most `C exp(-c k^{ε/(4(s+2))})`. The labels are
zero-based through `Riesz1.cyclicLift`, so `x_{i+N} = x_i + 1`. -/
theorem companionGapRigidity (β : InverseTemperature) (s : Riesz1.RieszExponent) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ (N : ℕ+) (_ : 2 ≤ (N : ℕ)) (i : Fin (N : ℕ)) (k : ℕ),
          1 ≤ k → k ≤ (N : ℕ) / 2 →
          gibbsMeasure (ofLong β s) N {X |
            |(N : ℝ) * (Riesz1.cyclicLift X ((i.val : ℤ) + k) -
                Riesz1.cyclicLift X i.val) - k| ≥ (k : ℝ) ^ (s.val / 2 + ε)} ≤
            ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ (ε / (4 * (s.val + 2))))) := by
  obtain ⟨ε₀, hε₀, hrigid⟩ :=
    (Riesz1.almost_optimal_rigidity β.val s.val β.property s.property.1 s.property.2).2
  refine ⟨ε₀, hε₀, fun ε hε hεε₀ => ?_⟩
  obtain ⟨c, C, hc, hC, hN⟩ := hrigid ε hε hεε₀
  refine ⟨C, c, hC, hc, fun N _ i k hk₁ hk₂ => ?_⟩
  rw [gibbsMeasure_ofLong]
  exact (hN N).1 i k hk₁ hk₂

/-- See Lemma 2.2 of the paper, near-optimal rigidity with constants chosen
before the volume, label and span. Let `0 < s < 1` and `β > 0`. Then there exists `ε₀ > 0` such
that, for every `0 < ε < ε₀`, there exist `C, c > 0`, depending only on `β, s, ε`, such that for
every integer `N ≥ 2`, every label `i ∈ {1, …, N}` and every integer `1 ≤ k ≤ ⌊N/2⌋`, the Gibbs
probability of `|N(x_{i+k} - x_i) - k| ≥ k^{s/2 + ε}` is at most `C e^{-c k^{ε/(4(s+2))}}`.
Its proof applies `companionGapRigidity`. -/
theorem companionNearOptimalRigidity :
  ∀ (s : Riesz1.RieszExponent) (β : InverseTemperature),
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ (N : ℕ+) (_ : 2 ≤ (N : ℕ)) (i : Fin (N : ℕ)) (k : ℕ),
          1 ≤ k → k ≤ (N : ℕ) / 2 →
          gibbsMeasure (ofLong β s) N {X |
            |(N : ℝ) * (Riesz1.cyclicLift X ((i.val : ℤ) + k) -
                Riesz1.cyclicLift X i.val) - k| ≥ (k : ℝ) ^ (s.val / 2 + ε)} ≤
            ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ (ε / (4 * (s.val + 2))))) :=
  fun s β => companionGapRigidity β s

end Riesz2

end
end
