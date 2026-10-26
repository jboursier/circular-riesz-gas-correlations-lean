/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.UpperCorrelations
public import Riesz2.DecayLong.LowerCorrelations

/-!
# Long-range gap correlations

See Theorem 1 of the paper: combine the upper decay
estimate and separated-block lower bound, retaining their different constant
scopes. The single-particle case reuses the constant-gap moment and covariance
identities, which allow every measurable derivative representative.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2.DecayLong.LongRangeResult

open Riesz2.DecayShort.ShortRangeResult

/-- See Theorem 1 of the paper, both conclusions with their
moment assertions. The upper exceptional power precedes temperature. The lower
constant precedes the mesoscopic sequence and is independent of epsilon. -/
theorem decay_gap_correlations (hzeta : External.PeriodicZeta)
    (hRig : External.LongRangeRigidityLocallyUniform) :
  ∀ s : Riesz1.RieszExponent,
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ β : InverseTemperature, ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ (N : ℕ+) (i j : Fin (N : ℕ)) (f g : GapObservable),
          let p := ofLong β s
          let d := Riesz1.cyclicIndexDistance N i j
          ∃ hMom : GapSecondMoments p N i.val j.val f g,
          |gapCorrelation p N i.val j.val f.val.1 g.val.1 hMom.1 hMom.2.1| ≤
            C / (1 + (d : ℝ)) ^ (2 - s.val - ε) *
              correlationFactor p N i.val f c δ d * correlationFactor p N j.val g c δ d) ∧
    (∀ β : InverseTemperature, ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ n : ℕ+ → ℕ+, IsMesoscopicSequence n → ∃ m₀ : ℕ,
        ∀ m : ℕ, m₀ ≤ m →
          let N := Riesz1.particleNumber m
          ∃ i j : Fin (N : ℕ),
            (n N : ℝ) / 2 ≤ (Riesz1.cyclicIndexDistance N i j : ℝ) ∧
            (Riesz1.cyclicIndexDistance N i j : ℝ) ≤ (n N : ℝ) ∧
            ∃ hi : MemLp (fun X => gap X i.val) 2 (gibbsMeasure (ofLong β s) N),
            ∃ hj : MemLp (fun X => gap X j.val) 2 (gibbsMeasure (ofLong β s) N),
            gapCorrelation (ofLong β s) N i.val j.val id id hi hj ≤
              -c₀ * (Riesz1.cyclicIndexDistance N i j : ℝ) ^ (s.val - 2)) := by
  intro s
  constructor
  · intro ε hε
    obtain ⟨δ, hδ, hupper⟩ :=
      UpperCorrelations.decay_gap_correlations_upper hzeta hRig s ε hε
    refine ⟨δ, hδ, ?_⟩
    intro β
    obtain ⟨C, c, hC, hc, hupper⟩ := hupper β
    refine ⟨C, c, hC, hc, ?_⟩
    intro N i j f g
    by_cases hN : 2 ≤ (N : ℕ)
    · obtain ⟨hMom, hbound⟩ := hupper N hN i j f g
      refine ⟨hMom, ?_⟩
      have hexp : -(2 - s.val) + ε = -(2 - s.val - ε) := by ring
      simpa only [hexp, Real.rpow_neg (by positivity :
        (0 : ℝ) ≤ 1 + (Riesz1.cyclicIndexDistance N i j : ℝ)), div_eq_mul_inv] using hbound
    · have he : N = 1 := PNat.eq (by change (N : ℕ) = 1; have := N.pos; omega)
      subst N
      refine ⟨internal_gapSecondMoments_one (ofLong β s) _ _ f g, ?_⟩
      rw [internal_gapCorrelation_one (ofLong β s) _ _ f g
        (internal_gapSecondMoments_one (ofLong β s) _ _ f g), abs_zero]
      exact mul_nonneg
        (mul_nonneg (div_nonneg hC.le (Real.rpow_nonneg (by positivity) _))
          (internal_correlationFactor_nonneg ..))
        (internal_correlationFactor_nonneg ..)
  · intro β
    obtain ⟨c₀, hc₀, hlower⟩ := LowerCorrelations.separated_block_covariance_lower β s
    refine ⟨c₀, hc₀, ?_⟩
    intro n hn
    have htop : Tendsto (fun m => (n (Riesz1.particleNumber m) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_iff.mpr hn.1
    obtain ⟨m₀, hm₀⟩ := eventually_atTop.1
      (hlower (fun m => (n (Riesz1.particleNumber m) : ℕ)) htop hn.2)
    refine ⟨m₀, ?_⟩
    intro m hm
    obtain ⟨i, j, hdlo, hdhi, hcov⟩ := hm₀ m hm
    refine ⟨i, j, hdlo, hdhi,
      LowerCorrelations.gap_memLp (ofLong β s) _ _,
      LowerCorrelations.gap_memLp (ofLong β s) _ _, ?_⟩
    exact hcov

end Riesz2.DecayLong.LongRangeResult

end
end
