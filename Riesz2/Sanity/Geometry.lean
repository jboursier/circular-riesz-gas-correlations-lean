/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.GibbsMeasure
public import Riesz2.Frozen.OfLong
public import Riesz1.Frozen.CyclicLift
public import Riesz2.Frozen.FiniteGapBlock
public import Riesz2.Frozen.BlockDerivativeNorm
public import Riesz2.Frozen.DependsOnBlockCoordinates
public import Riesz2.Frozen.MiddleConsecutiveBlock
public import Riesz2.Frozen.ActiveTiltedGapLaw
public import Riesz2.Frozen.SymmetricMiddleBlock
public import Riesz2.Frozen.GoodBlockEvent
public import Riesz2.Frozen.RestrictedBlockDerivativeNorm
public import Riesz2.Frozen.FullIntrinsicTiltedGapLaw
public import Riesz2.Frozen.ProperMarginalDomain
public import Riesz2.Frozen.IntrinsicGapDomain
public import Riesz2.Frozen.FullPhysicalPotentialValue
public import Riesz2.Frozen.GapAmbientDomain
public import Riesz2.Frozen.HessianMatrix
public import Riesz2.Frozen.IsEuclideanGibbsPotential
public import Riesz2.Frozen.IsClosedScalarDirichletForm
public import Riesz2.Frozen.IsConservativeScalarForm
public import Riesz2.Frozen.WeightedWeakSolution
public import Riesz2.Frozen.ZeroSumComponents
public import Riesz2.Frozen.OfShort
public import Riesz1.Frozen.CyclicIndexDistance
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Riesz2.Frozen.PeriodizedMatrixBounds
public import Riesz2.Frozen.InverseTemperature
public import Riesz2.Frozen.AdmissibleParticlePairs
public import Riesz2.Frozen.PairGibbsMeasure
public import Riesz2.Frozen.PairAmbientGapPotential
public import Riesz2.Frozen.IntrinsicGapLaw
public import Riesz2.Frozen.ScalarPoissonSolution
public import Riesz2.Frozen.GapMultiplierField
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Riesz2.Frozen.IsNeumannRealization
public import Riesz2.Frozen.SummableCoerciveMatrix
public import Mathlib.Analysis.Convex.Basic
public import Mathlib

/-! # Geometry and finite-value checks -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace Riesz2.DefinitionSanity

/-- Constant observables are legitimate global Lipschitz tests. -/
def constantObservable (n : ℕ+) (c : ℝ) : BlockObservable n :=
  ⟨fun _ => c, ⟨0, LipschitzWith.const c⟩⟩

theorem constant_depends (n : ℕ+) (c : ℝ) (J : Finset (Fin (n : ℕ))) :
    DependsOnBlockCoordinates (constantObservable n c) J := by
  intro x y _
  rfl

theorem middle_empty (n : ℕ+) : MiddleConsecutiveBlock n ∅ := by
  refine ⟨0, 0, Nat.zero_le _, Nat.zero_le _, ?_, ?_⟩
  · simp
  · simp

theorem middle_four : MiddleConsecutiveBlock 4 {⟨1, by norm_num⟩} := by
  refine ⟨1, 1, by norm_num, by norm_num, ?_, ?_⟩
  · ext i
    simp only [Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      subst i
      exact ⟨by norm_num, by norm_num⟩
    · intro h
      apply Fin.ext
      change i.val = 1
      omega
  · intro i hi
    simp only [Finset.mem_singleton] at hi
    subst i
    norm_num

theorem restricted_constant (n : ℕ+) (c : ℝ) (J : Finset (Fin (n : ℕ)))
    (A : Set (Fin (n : ℕ) → ℝ)) :
    restrictedBlockDerivativeNorm (constantObservable n c) J A = 0 := by
  have h (j : Fin (n : ℕ)) :
      sInf {L : ℝ≥0 | ∀ (x : Fin (n : ℕ) → ℝ) (t : ℝ),
        x ∈ A → Function.update x j t ∈ A →
        |(constantObservable n c).val (Function.update x j t) -
          (constantObservable n c).val x| ≤ (L : ℝ) * |t - x j|} = 0 := by
    apply le_antisymm
    · apply csInf_le (OrderBot.bddBelow _)
      intro x t _ _
      simp [constantObservable]
    · exact bot_le
  simp only [restrictedBlockDerivativeNorm, h, NNReal.coe_zero, Finset.sum_const_zero]

theorem symmetric_middle_eight : symmetricMiddleBlock 8 1 = {⟨2, by norm_num⟩, ⟨3, by norm_num⟩, ⟨4, by norm_num⟩} := by
  ext i
  simp only [symmetricMiddleBlock, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
  norm_num
  omega

theorem good_block_two : (fun _ : Fin (2 : ℕ) => (1 : ℝ)) ∈ goodBlockEvent 2 ⟨2, by norm_num⟩ ⟨8, by norm_num⟩ 1 := by
  constructor
  · norm_num [Fin.sum_univ_succ]
  constructor
  · intro i
    norm_num
  · intro a b hab hb
    change b ≤ 2 at hb
    rw [Finset.sum_filter]
    change |(∑ i : Fin 2, if a ≤ i.val ∧ i.val < b then (1 : ℝ) else 0) -
      ((b - a : ℕ) : ℝ)| ≤ (2 : ℝ) ^ (1 : ℝ) *
        ((b - a : ℕ) : ℝ) ^ (min (2 : ℝ) 1 / 2)
    interval_cases b
    all_goals interval_cases a
    all_goals rw [Fin.sum_univ_two]
    all_goals norm_num
    all_goals positivity

theorem cyclic_sum_zero (N : ℕ+) (i : Fin (N : ℕ)) (y : Fin (N : ℕ) → ℝ) :
    cyclicGapSum N i 0 y = 0 := by
  simp [cyclicGapSum]

theorem cyclic_sum_one (N : ℕ+) (i : Fin (N : ℕ)) (r : ℕ) :
    cyclicGapSum N i r (fun _ => 1) = r := by
  simp [cyclicGapSum]

theorem cyclic_interval_empty (N : ℕ+) (i : Fin (N : ℕ)) :
    cyclicIndexInterval N i 0 = ∅ := by
  simp [cyclicIndexInterval]

theorem ambient_ones (N : ℕ+) (_hN : 2 ≤ (N : ℕ)) :
    WithLp.toLp 2 (fun _ : Fin (N : ℕ) => (1 : ℝ)) ∈ gapAmbientDomain N := by
  intro i r hr hrN
  change 0 < cyclicGapSum N i r (fun _ => 1) ∧ cyclicGapSum N i r (fun _ => 1) < (N : ℝ)
  rw [cyclic_sum_one]
  constructor
  · exact_mod_cast hr
  · exact_mod_cast (show r < (N : ℕ) by omega)

theorem proper_ones : WithLp.toLp 2 (fun _ : Fin (2 : ℕ) => (1 : ℝ)) ∈ properMarginalDomain 2 8 := by
  constructor
  · intro i
    norm_num
  · norm_num [Fin.sum_univ_succ]

theorem intrinsic_zero (N : ℕ+) : (0 : gapTangentSpace N) ∈ intrinsicGapDomain N := by
  intro i
  change (0 : ℝ) < 1 + 0
  norm_num

theorem centered_ones (N : ℕ+) :
    centeredGapChart N (WithLp.toLp 2 (fun _ : Fin (N : ℕ) => (1 : ℝ))) = 0 := by
  apply Subtype.ext
  ext i
  change 1 - (∑ _ : Fin (N : ℕ), (1 : ℝ)) / (N : ℝ) = 0
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt N.pos)
  simp [hN]

theorem interval_point_nonzero (x : {x : ℝ // 0 < x ∧ x < 1}) :
    (interiorCirclePoint x).val ≠ 0 := (interiorCirclePoint x).property

theorem reference_symmetric (s : Riesz1.RieszExponent) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (K : ℕ) (i j : Fin (N : ℕ)) :
    referenceIntervalMatrix s N hN K i j = referenceIntervalMatrix s N hN K j i := by
  unfold referenceIntervalMatrix
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem reference_empty (s : Riesz1.RieszExponent) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (K : ℕ) (hK : (N : ℕ) / 2 < K) : referenceIntervalMatrix s N hN K = 0 := by
  ext a b
  unfold referenceIntervalMatrix
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro r hr
  simp only [Finset.mem_filter, Finset.mem_range] at hr
  omega

theorem component_line_self {ι : Type*} (e : ι ↪ ℤ) (i : ι) :
    componentDistance (Sum.inl e) i i = 0 := by
  simp [componentDistance]

theorem component_cycle_self (N : ℕ+) (i : Fin (N : ℕ)) :
    componentDistance (Sum.inr ⟨N, Function.Embedding.refl _⟩) i i = 0 := by
  simp [componentDistance, Riesz1.cyclicIndexDistance]

theorem zero_sum_zero (ι : Type*) [Fintype ι] : (0 : ι → ℝ) ∈ zeroSumComponents ι := by
  simp [zeroSumComponents]

theorem particle_chamber_two :
    WithLp.toLp 2 (fun i : Fin (2 : ℕ) => (i.val : ℝ) / 2) ∈ particleChamber 2 := by
  constructor
  · intro i j hij
    change (i.val : ℝ) / 2 < (j.val : ℝ) / 2
    exact div_lt_div_of_pos_right (by exact_mod_cast hij) (by norm_num)
  · intro i
    change (i.val : ℝ) / 2 < ((⟨0, PNat.pos 2⟩ : Fin (2 : ℕ)).val : ℝ) / 2 + 1
    norm_num only [zero_div, zero_add]
    exact (div_lt_one (by norm_num : (0 : ℝ) < 2)).mpr (by exact_mod_cast i.isLt)

theorem pair_energy_translation (N : ℕ+) (χ : ParticlePairData N)
    (x : EuclideanSpace ℝ (Fin (N : ℕ))) (t : ℝ) :
    particlePairEnergy χ (WithLp.toLp 2 (fun i => x i + t)) = particlePairEnergy χ x := by
  unfold particlePairEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  change (x p.val.2 + t) - (x p.val.1 + t) = x p.val.2 - x p.val.1
  ring

theorem sampled_antipode_zero (s : Riesz1.RieszExponent) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    sampledRieszKernel s N hN ⟨(N : ℕ) / 2, by omega⟩ = 0 := by
  simp only [sampledRieszKernel]
  rw [dite_eq_right (show ¬(N : ℕ) / 2 = 0 by omega)]
  simp

theorem kernel_ofLong (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (x : {x : UnitAddCircle // x ≠ 0}) :
    kernelAtParameters (ofLong β s) x = Riesz1.rieszKernel s x := by
  simp [kernelAtParameters, ofLong, s.property.2]

theorem kernel_ofShort (β : InverseTemperature) (s : ShortExponent)
    (x : {x : UnitAddCircle // x ≠ 0}) :
    kernelAtParameters (ofShort β s) x = shortKernel s x := by
  have hs : ¬s.val < 1 := not_lt.mpr (le_of_lt s.property)
  simp [kernelAtParameters, ofShort, hs]

theorem penalty_two_sided_difference (N n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ) (X : Riesz1.Configuration N) :
    physicalGapPenalty N n hn θ ε true X - physicalGapPenalty N n hn θ ε false X =
      ∑ i : Fin (n : ℕ), θ.val ((n : ℝ) ^ (-ε) * (gap X i.val)⁻¹) := by
  simp only [physicalGapPenalty, Bool.false_eq_true, ↓reduceIte,
    add_zero, Finset.sum_add_distrib, add_sub_cancel_left]

theorem full_potential_two_sided_difference (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ)
    (y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N}) :
    fullPhysicalPotentialValue p N hN θ ε true y - fullPhysicalPotentialValue p N hN θ ε false y =
      p.val.1 * ∑ i : Fin (N : ℕ), θ.val ((N : ℝ) ^ (-ε) * (y.val i)⁻¹) := by
  simp only [fullPhysicalPotentialValue, Bool.false_eq_true, ↓reduceIte,
    add_zero, Finset.sum_add_distrib]
  ring

/-- Nonempty simultaneous size ranges for both physical marginal claims and the comparison. -/
theorem physical_comparison_ranges_nonempty :
    ∃ (n N N' : ℕ+) (i₀ : Fin (n : ℕ)),
      2 ≤ (n : ℕ) ∧ 4 ≤ (N : ℕ) ∧ 4 * (n : ℕ) ≤ (N : ℕ) ∧
      (N : ℕ) ≤ (N' : ℕ) ∧ (n : ℝ) ^ (2 / (2 : ℝ)) ≤ (N : ℝ) ∧
      (n : ℕ) ≤ 4 * (i₀.val + 1) ∧ 4 * (i₀.val + 1) ≤ 3 * (n : ℕ) := by
  exact ⟨4, 16, 16, ⟨1, by norm_num⟩, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num⟩

end Riesz2.DefinitionSanity
end
end
