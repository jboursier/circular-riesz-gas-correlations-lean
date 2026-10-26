/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Preliminaries.GapSymmetries

/-!
# Densities of individual finite gaps

See Theorem 1 of the paper: every coordinate of the gap law has a Lebesgue density, vanishing
outside `(0, N)`.

The first gap is `N` times the first offset of the coordinates relative to the first particle, so a Lebesgue-null set
of gap values pulls back to a configuration volume-null set. Every other gap is the first gap of
a cyclically relabelled configuration, and the configuration volume is invariant under that
relabelling. The density is the Radon–Nikodym derivative, restricted to `(0, N)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz2
namespace GapDensities

open GapSymmetries

variable {m : ℕ}

/-- The first gap is `N` times the first offset of the coordinates relative to the first particle. -/
theorem gap_zero_eq_anchor (X : Riesz1.Configuration (m + 1).succPNat) :
    Riesz2.gap X 0 = (((m + 1).succPNat : ℕ) : ℝ) * (Riesz1.anchorCoords (m + 1) X.val).2 0 := by
  have h1 : Riesz1.cyclicLift X 1 = X.val (Fin.succ 0) := by
    simpa using Riesz1.cyclicLift_natCast X (Fin.succ 0)
  have h0 : Riesz1.cyclicLift X 0 = X.val 0 := by
    simpa using Riesz1.cyclicLift_natCast X 0
  unfold Riesz2.gap
  rw [show ((0 : ℤ) + 1) = 1 by norm_num, h1, h0]
  rfl

/-- The first gap pulls back a Lebesgue-null set of values to a configuration volume-null set. -/
theorem configurationVolume_gap_zero_eq_zero (A : Set ℝ) (hvol : volume A = 0) :
    Riesz1.configurationVolume (m + 1).succPNat {X | Riesz2.gap X 0 ∈ A} = 0 := by
  have hΦ := measurableEmbedding_anchorCoords (m := m)
  have hN : (((m + 1).succPNat : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (m + 1).succPNat.ne_zero
  set B : Set (Fin (m + 1) → ℝ) := Function.eval 0 ⁻¹'
    ((fun t : ℝ => (((m + 1).succPNat : ℕ) : ℝ) * t) ⁻¹' A) with hB
  have hset : {X : Riesz1.Configuration (m + 1).succPNat | Riesz2.gap X 0 ∈ A} =
      (fun X : Riesz1.Configuration (m + 1).succPNat => Riesz1.anchorCoords (m + 1) X.val) ⁻¹'
        (univ ×ˢ B) := by
    ext X
    simp only [mem_preimage, mem_prod, mem_univ, true_and]
    show Riesz2.gap X 0 ∈ A ↔
      (((m + 1).succPNat : ℕ) : ℝ) * (Riesz1.anchorCoords (m + 1) X.val).2 0 ∈ A
    rw [gap_zero_eq_anchor X]
  have hBnull : volume B = 0 := by
    have hC : volume ((fun t : ℝ => (((m + 1).succPNat : ℕ) : ℝ) * t) ⁻¹' A) = 0 := by
      rw [Real.volume_preimage_mul_left hN, hvol, mul_zero]
    rw [volume_pi]
    exact Measure.pi_eval_preimage_null (fun _ : Fin (m + 1) => volume) hC
  rw [hset, ← hΦ.map_apply, Riesz1.map_anchorCoords_configurationVolume, Measure.prod_prod]
  have hle : volume.restrict (Riesz1.anchoredDomain (m + 1)) ≤ volume := Measure.restrict_le_self
  have hD : (volume.restrict (Riesz1.anchoredDomain (m + 1))) B = 0 :=
    le_antisymm ((Measure.le_iff'.mp hle B).trans hBnull.le) zero_le
  rw [hD, mul_zero]

/-- Iterating the cyclic relabelling shifts the gap index. -/
theorem gap_cycleConfig_iterate (k : ℕ) (j : ℤ) (X : Riesz1.Configuration (m + 1).succPNat) :
    Riesz2.gap ((cycleConfig (N := (m + 1).succPNat))^[k] X) j = Riesz2.gap X (j + k) := by
  induction k generalizing j with
  | zero => rw [Function.iterate_zero_apply, Nat.cast_zero, add_zero]
  | succ k ih =>
    rw [Function.iterate_succ_apply', gap_cycleConfig, ih]
    congr 1
    push_cast
    ring

/-- Every gap pulls back a Lebesgue-null set of values to a configuration volume-null set. -/
theorem configurationVolume_gap_eq_zero (A : Set ℝ) (hA : MeasurableSet A) (hvol : volume A = 0)
    (i : Fin ((m + 1).succPNat : ℕ)) :
    Riesz1.configurationVolume (m + 1).succPNat {X | Riesz2.gap X (i : ℕ) ∈ A} = 0 := by
  have hgap : Measurable (fun X : Riesz1.Configuration (m + 1).succPNat => Riesz2.gap X 0) := by
    unfold Riesz2.gap
    exact measurable_const.mul ((Riesz1.measurable_cyclicLift _).sub (Riesz1.measurable_cyclicLift _))
  have hpre : {X : Riesz1.Configuration (m + 1).succPNat | Riesz2.gap X (i : ℕ) ∈ A} =
      (cycleConfig (N := (m + 1).succPNat))^[(i : ℕ)] ⁻¹'
        {X : Riesz1.Configuration (m + 1).succPNat | Riesz2.gap X 0 ∈ A} := by
    ext X
    simp only [mem_preimage, gap_cycleConfig_iterate, zero_add, mem_ofPred_eq]
  have hS : NullMeasurableSet {X : Riesz1.Configuration (m + 1).succPNat | Riesz2.gap X 0 ∈ A}
      (Riesz1.configurationVolume (m + 1).succPNat) :=
    (hgap hA).nullMeasurableSet
  rw [hpre, (MeasurePreserving.iterate
    ⟨measurable_cycleConfig, configurationVolume_map_cycleConfig⟩ (i : ℕ)).measure_preimage hS]
  exact configurationVolume_gap_zero_eq_zero A hvol

/-- The coordinates of the gap law are absolutely continuous with respect to Lebesgue measure. -/
theorem gapLaw_marginal_absolutelyContinuous (p : Parameters) (m : ℕ)
    (i : Fin ((m + 1).succPNat : ℕ)) :
    (gapLaw p (m + 1).succPNat).map (fun g : Fin ((m + 1).succPNat : ℕ) → ℝ => g i) ≪ volume := by
  have := gibbsMeasure_probability p (m + 1).succPNat
  have hVm : Measurable (Riesz2.gapVector (N := (m + 1).succPNat)) :=
    Riesz1.measurable_gapVector _
  have hcoord : Measurable (fun g : Fin ((m + 1).succPNat : ℕ) → ℝ => g i) :=
    measurable_pi_apply i
  refine Measure.AbsolutelyContinuous.mk fun A hA hvol => ?_
  rw [Measure.map_apply hcoord hA]
  unfold Riesz2.gapLaw
  rw [Measure.map_apply hVm (hcoord hA)]
  have hSm : MeasurableSet (Riesz2.gapVector (N := (m + 1).succPNat) ⁻¹'
      ((fun g : Fin ((m + 1).succPNat : ℕ) → ℝ => g i) ⁻¹' A)) := hVm (hcoord hA)
  have hS : Riesz1.configurationVolume (m + 1).succPNat
      (Riesz2.gapVector (N := (m + 1).succPNat) ⁻¹'
        ((fun g : Fin ((m + 1).succPNat : ℕ) → ℝ => g i) ⁻¹' A)) = 0 :=
    configurationVolume_gap_eq_zero A hA hvol i
  rw [GapChart.gibbsMeasure_eq_withDensity, Measure.smul_apply, withDensity_apply _ hSm,
    setLIntegral_measure_zero _ _ hS, smul_zero]

/-- See Theorem 1 of the paper. For `s ∈ (0,1) ∪ (1,∞)`, `β > 0` and `N ≥ 2`, each coordinate
`Y_i` of the gap law has a Lebesgue density: a measurable, nonnegative, real-valued function `f`
vanishing outside `(0, N)`, with the image of the gap law under `g ↦ g i` equal to `f dx`. -/
theorem gapLaw_marginal_density (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (i : Fin (N : ℕ)) :
    ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, x ∉ Ioo (0 : ℝ) (N : ℕ) → f x = 0) ∧
      (gapLaw p N).map (fun g : Fin (N : ℕ) → ℝ => g i) =
        volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, N = (m + 1).succPNat :=
    ⟨(N : ℕ) - 2, PNat.eq (by simp only [Nat.succPNat_coe]; omega)⟩
  have := gibbsMeasure_probability p (m + 1).succPNat
  have hVm : Measurable (Riesz2.gapVector (N := (m + 1).succPNat)) :=
    Riesz1.measurable_gapVector _
  have hcoord : Measurable (fun g : Fin ((m + 1).succPNat : ℕ) → ℝ => g i) :=
    measurable_pi_apply i
  have hprob : IsProbabilityMeasure (gapLaw p (m + 1).succPNat) := by
    unfold Riesz2.gapLaw
    infer_instance
  set ν := (gapLaw p (m + 1).succPNat).map (fun g : Fin ((m + 1).succPNat : ℕ) → ℝ => g i)
    with hν
  have hprobν : IsProbabilityMeasure ν := inferInstance
  have hac : ν ≪ volume := gapLaw_marginal_absolutelyContinuous p m i
  set r := ν.rnDeriv volume with hr
  have hνr : volume.withDensity r = ν := Measure.withDensity_rnDeriv_eq ν volume hac
  have hrm : Measurable r := Measure.measurable_rnDeriv ν volume
  have hIoo : MeasurableSet (Ioo (0 : ℝ) (((m + 1).succPNat : ℕ) : ℝ)) := measurableSet_Ioo
  have hsupp : ν (Ioo (0 : ℝ) (((m + 1).succPNat : ℕ) : ℝ))ᶜ = 0 := by
    rw [hν, Measure.map_apply hcoord hIoo.compl]
    unfold Riesz2.gapLaw
    rw [Measure.map_apply hVm (hcoord hIoo.compl)]
    have hempty : Riesz2.gapVector (N := (m + 1).succPNat) ⁻¹'
        ((fun g : Fin ((m + 1).succPNat : ℕ) → ℝ => g i) ⁻¹'
          (Ioo (0 : ℝ) (((m + 1).succPNat : ℕ) : ℝ))ᶜ) = ∅ := by
      ext X
      exact ⟨fun hX => (hX ⟨gapVector_pos X i, gapVector_lt X i⟩).elim, fun hX => hX.elim⟩
    rw [hempty, measure_empty]
  have hae : ∀ᵐ x ∂volume, x ∉ Ioo (0 : ℝ) (((m + 1).succPNat : ℕ) : ℝ) → r x = 0 := by
    have h0 : ∫⁻ x in (Ioo (0 : ℝ) (((m + 1).succPNat : ℕ) : ℝ))ᶜ, r x ∂volume = 0 := by
      rw [← withDensity_apply _ hIoo.compl, hνr, hsupp]
    exact (setLIntegral_eq_zero_iff hIoo.compl hrm).mp h0
  have hrfin : ∀ᵐ x ∂volume, r x < ⊤ := Measure.rnDeriv_lt_top ν volume
  refine ⟨fun x => (Set.indicator (Ioo (0 : ℝ) (((m + 1).succPNat : ℕ) : ℝ)) r x).toReal,
    ?_, fun x => ENNReal.toReal_nonneg, ?_, ?_⟩
  · exact (hrm.indicator hIoo).ennreal_toReal
  · intro x hx
    dsimp only
    rw [Set.indicator_of_notMem hx]
    simp
  · rw [← hνr]
    refine withDensity_congr_ae ?_
    filter_upwards [hae, hrfin] with x h0 hfin
    by_cases hx : x ∈ Ioo (0 : ℝ) (((m + 1).succPNat : ℕ) : ℝ)
    · rw [Set.indicator_of_mem hx, ENNReal.ofReal_toReal hfin.ne]
    · rw [Set.indicator_of_notMem hx, h0 hx]
      simp

end GapDensities
end Riesz2
end
end
