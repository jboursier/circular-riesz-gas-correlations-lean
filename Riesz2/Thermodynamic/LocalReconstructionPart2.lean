/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.LocalReconstruction
public import Riesz2.Thermodynamic.PalmInversionPart2
public import Mathlib.MeasureTheory.Function.FactorsThrough
public import Riesz1.Kernel.AdmissibleExamplesCompactPrimitive

/-!
# Concrete local reconstruction

The reconstruction and finite-label restriction in the proof of Theorem 3, using the gap
positions throughout.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace Riesz2

local notation "Gaps" => (ℤ → Ioi (0 : ℝ))
local instance localReconstructionPart2ConfigurationMeasurableSpace : MeasurableSpace LineConfiguration := configurationMeasurableSpace

/-- See the proof of Theorem 3 in the paper: the actual reconstructed
configuration on a closed window depends only on the indicated gap block. -/
theorem reconstructConfiguration_local_eq (y y' : reconstructibleGapSequences)
    (m : ℕ) (hm : 2 ≤ m) (R u : ℝ)
    (hy : y.val ∈ localReconstructionEvent m R)
    (hu : 0 ≤ u) (huy : u ≤ (y.val 0 : ℝ))
    (heq : ∀ j ∈ Finset.Ico (-(m : ℤ)) (m : ℤ), y.val j = y'.val j) :
    restrictConfiguration (Icc (-R) R) (translateConfiguration u (reconstructConfiguration y)) =
      restrictConfiguration (Icc (-R) R) (translateConfiguration u (reconstructConfiguration y')) :=
  convergence_local_block_determination_internal y.val y'.val _ _ _ _ rfl rfl
    (gapPosition_zero _) (gapPosition_zero _) (gapPosition_add_one _)
    (gapPosition_add_one _) m hm R u hy hu huy heq

/-- The finite subconfiguration of reconstructed labels strictly between `-m`
and `m`. This is a literal finite restriction of the existing position map,
including for positive sequences that accumulate outside this finite block. -/
def gapBlockConfiguration (m : ℕ) (y : Gaps) : LineConfiguration :=
  ⟨gapPosition y '' (Finset.Ioo (-(m : ℤ)) (m : ℤ) : Set ℤ), fun _ _ =>
    ((Finset.Ioo (-(m : ℤ)) (m : ℤ)).finite_toSet.image _).subset inter_subset_left⟩

/-- Strict bracketing identifies the finite-label configuration with the actual
reconstruction on the closed window, including the two offset endpoints. -/
theorem restrict_gapBlockConfiguration (m : ℕ) (hm : 2 ≤ m) (R u : ℝ)
    (y : reconstructibleGapSequences) (hy : y.val ∈ localReconstructionEvent m R)
    (hu : 0 ≤ u) (huy : u ≤ (y.val 0 : ℝ)) :
    restrictConfiguration (Icc (-R) R) (translateConfiguration u (reconstructConfiguration y)) =
      restrictConfiguration (Icc (-R) R) (translateConfiguration u (gapBlockConfiguration m y.val)) := by
  have hl := gapSequenceSpan_eq_position_sub_internal y.val (gapPosition y.val)
    (gapPosition_add_one _) (-(m : ℤ)) m
  have hr := gapSequenceSpan_eq_position_sub_internal y.val (gapPosition y.val)
    (gapPosition_add_one _) 1 (m - 1)
  rw [neg_add_cancel, gapPosition_zero, zero_sub] at hl
  rw [show (1 : ℤ) + ((m - 1 : ℕ) : ℤ) = (m : ℤ) by omega] at hr
  have h1 : gapPosition y.val 1 = (y.val 0 : ℝ) := by
    simpa only [gapPosition_zero, zero_add] using gapPosition_add_one y.val 0
  have hleft : gapPosition y.val (-(m : ℤ)) - u < -R := by
    have h := hy.1; rw [hl] at h; linarith
  have hright : R < gapPosition y.val (m : ℤ) - u := by
    have h := hy.2; rw [hr, h1] at h; linarith
  apply Subtype.ext
  ext x
  rw [mem_translated_window_iff_finite_labels _ _ (gapPosition_strictMono _).monotone
    rfl _ _ _ _ hleft hright]
  change (∃ i ∈ Finset.Ioo (-(m : ℤ)) (m : ℤ),
    gapPosition y.val i - u = x ∧ x ∈ Icc (-R) R) ↔
      (x + u ∈ gapPosition y.val '' (Finset.Ioo (-(m : ℤ)) (m : ℤ) : Set ℤ) ∧
        x ∈ Icc (-R) R)
  constructor
  · rintro ⟨i, hi, he, hx⟩
    exact ⟨⟨i, hi, by linarith⟩, hx⟩
  · rintro ⟨⟨i, hi, he⟩, hx⟩
    exact ⟨i, hi, by linarith, hx⟩

/-- Finite-label counts have no multiplicities, since positive gaps make all
positions distinct. -/
theorem count_gapBlockConfiguration (m : ℕ) (y : Gaps) (B : Set ℝ) :
    count (gapBlockConfiguration m y) B =
      ∑ i : (Finset.Ioo (-(m : ℤ)) (m : ℤ) : Set ℤ),
        B.indicator (fun _ => (1 : ℝ≥0∞)) (gapPosition y i.val) := by
  classical
  rw [← tsum_fintype (L := SummationFilter.unconditional _)]
  have he : (fun i : (Finset.Ioo (-(m : ℤ)) (m : ℤ) : Set ℤ) =>
      B.indicator (fun _ => (1 : ℝ≥0∞)) (gapPosition y i.val)) =
      {i : (Finset.Ioo (-(m : ℤ)) (m : ℤ) : Set ℤ) | gapPosition y i.val ∈ B}.indicator
        (fun _ => (1 : ℝ≥0∞)) := by
    ext i; by_cases h : gapPosition y i.val ∈ B <;> simp [h]
  rw [he, ← tsum_subtype, ENNReal.tsum_one]
  unfold count
  congr 1
  symm
  apply ENat.card_congr
  exact Equiv.ofBijective
    (fun i : {i : (Finset.Ioo (-(m : ℤ)) (m : ℤ) : Set ℤ) | gapPosition y i.val ∈ B} =>
      (⟨gapPosition y i.val.val, ⟨i.val.val, i.val.property, rfl⟩, i.property⟩ :
        {x : ℝ // x ∈ (gapBlockConfiguration m y).val ∩ B}))
    ⟨fun i j h => Subtype.ext (Subtype.ext ((gapPosition_strictMono y).injective
      (congrArg Subtype.val h))), fun ⟨x, ⟨i, hi, he⟩, hx⟩ =>
        ⟨⟨⟨i, hi⟩, by change gapPosition y i ∈ B; rw [he]; exact hx⟩, Subtype.ext he⟩⟩

/-- The finite-label configuration is measurable whenever its finitely many
positions are measurable. This also applies to the sigma algebra of a block. -/
theorem measurable_gapBlockConfiguration_of_positions (m : ℕ) (M : MeasurableSpace Gaps)
    (h : ∀ i ∈ Finset.Ioo (-(m : ℤ)) (m : ℤ),
      @Measurable Gaps ℝ M _ (fun y => gapPosition y i)) :
    @Measurable Gaps LineConfiguration M configurationMeasurableSpace (gapBlockConfiguration m) := by
  let _ := M
  apply measurable_configuration_of_counts
  intro B hB _
  simp_rw [count_gapBlockConfiguration]
  exact Finset.measurable_sum _ fun i _ => (measurable_const.indicator hB).comp (h i.val i.property)

local notation "blockProj" => (fun (m : ℕ) (y : Gaps) =>
  (WithLp.toLp 2 (fun j : Fin (2 * m) =>
    (y (-(m : ℤ) + (Fin.val j : ℤ)) : ℝ)) : EuclideanSpace ℝ (Fin (2 * m))))

/-- Each coordinate in the chosen block is measurable for exactly the sigma
algebra generated by the Euclidean block projection. -/
theorem measurable_gapCoordinate_block (m : ℕ) (j : ℤ)
    (hj : j ∈ Finset.Ico (-(m : ℤ)) (m : ℤ)) :
    Measurable[(inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin (2 * m)))).comap
      (blockProj m)] (fun y : Gaps => (y j : ℝ)) := by
  have hj' := Finset.mem_Ico.mp hj
  let i : Fin (2 * m) := ⟨(j + (m : ℤ)).toNat, by omega⟩
  have he : -(m : ℤ) + (i.val : ℤ) = j := by dsimp [i]; omega
  have hm : Measurable (fun x : EuclideanSpace ℝ (Fin (2 * m)) => x i) := by fun_prop
  convert hm.comp (comap_measurable (blockProj m)) using 1
  ext y
  change (y j : ℝ) = (y (-(m : ℤ) + (i.val : ℤ)) : ℝ)
  rw [he]

/-- All positions from `-m` through `m` are finite sums in the chosen block. -/
theorem measurable_gapPosition_block (m : ℕ) (i : ℤ)
    (hi : -(m : ℤ) ≤ i) (hi' : i ≤ (m : ℤ)) :
    Measurable[(inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin (2 * m)))).comap
      (blockProj m)] (fun y : Gaps => gapPosition y i) := by
  unfold gapPosition
  apply Measurable.sub
  · apply Finset.measurable_sum
    intro j hj
    apply measurable_gapCoordinate_block
    simp only [Finset.mem_Ico] at hj ⊢
    omega
  · apply Finset.measurable_sum
    intro j hj
    apply measurable_gapCoordinate_block
    simp only [Finset.mem_Ico] at hj ⊢
    omega

/-- The finite subconfiguration is measurable already for its finite block. -/
theorem measurable_gapBlockConfiguration_block (m : ℕ) :
    Measurable[(inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin (2 * m)))).comap
      (blockProj m)] (gapBlockConfiguration m) := by
  apply measurable_gapBlockConfiguration_of_positions
  intro i hi
  have h := Finset.mem_Ioo.mp hi
  exact measurable_gapPosition_block m i h.1.le h.2.le

/-- The bracketing event itself is a measurable event of the finite block. -/
theorem measurableSet_localReconstructionEvent_block (m : ℕ) (hm : 2 ≤ m) (R : ℝ) :
    @MeasurableSet Gaps ((inferInstance :
      MeasurableSpace (EuclideanSpace ℝ (Fin (2 * m)))).comap (blockProj m))
      (localReconstructionEvent m R) := by
  have he : localReconstructionEvent m R =
      {y : Gaps | R < -gapPosition y (-(m : ℤ)) ∧
        R < gapPosition y (m : ℤ) - (y 0 : ℝ)} := by
    ext y
    have hl := gapSequenceSpan_eq_position_sub_internal y (gapPosition y)
      (gapPosition_add_one _) (-(m : ℤ)) m
    have hr := gapSequenceSpan_eq_position_sub_internal y (gapPosition y)
      (gapPosition_add_one _) 1 (m - 1)
    rw [neg_add_cancel, gapPosition_zero, zero_sub] at hl
    rw [show (1 : ℤ) + ((m - 1 : ℕ) : ℤ) = (m : ℤ) by omega] at hr
    have h1 : gapPosition y 1 = (y 0 : ℝ) := by
      simpa only [gapPosition_zero, zero_add] using gapPosition_add_one y 0
    simp only [localReconstructionEvent, mem_ofPred_eq, hl, hr, h1]
  rw [he]
  exact (measurableSet_lt measurable_const
    (measurable_gapPosition_block m _ le_rfl (by omega)).neg).inter
      (measurableSet_lt measurable_const
        ((measurable_gapPosition_block m _ (by omega) le_rfl).sub
          (measurable_gapCoordinate_block m 0 (by simp only [Finset.mem_Ico]; omega))))

/-- Reconstruction and both weighted tails in the proof of Theorem 3,
assuming the ordinary-gap Cauchy estimate. -/
theorem convergence_local_block_from_cauchy_internal
    (hcomparison :
  ∀ (p : Parameters) (ζ : ℝ), 0 < ζ → ∃ C : ℝ, 0 < C ∧
    ∀ (n N N' : ℕ+) (_ : 2 ≤ (n : ℕ)),
      (N : ℕ) ≤ (N' : ℕ) → 4 * (n : ℕ) ≤ (N : ℕ) →
      (n : ℝ) ^ (2 / p.val.2) ≤ (N : ℝ) →
      ∀ (G : BlockObservable n) (J : Finset (Fin (n : ℕ))),
        MiddleConsecutiveBlock n J → DependsOnBlockCoordinates G J →
        Integrable (fun X : Riesz1.Configuration N => G.val (finiteGapBlock X))
          (gibbsMeasure p N) ∧
        Integrable (fun X : Riesz1.Configuration N' => G.val (finiteGapBlock X))
          (gibbsMeasure p N') ∧
        |(∫ X : Riesz1.Configuration N, G.val (finiteGapBlock X) ∂gibbsMeasure p N) -
          (∫ X : Riesz1.Configuration N', G.val (finiteGapBlock X) ∂gibbsMeasure p N')| ≤
          C * (n : ℝ) ^ (-min p.val.2 1 / 2 + ζ) * blockDerivativeNorm G)
    (p : Parameters) (R : ℝ) (_hR : 0 < R) :
    ∃! q : ProbabilityMeasure Gaps,
      Tendsto (fun n : ℕ => periodicGapLaw p n.succPNat) atTop (𝓝 q) ∧
      (∀ (m : ℕ), 2 ≤ m → ∀ (y y' : reconstructibleGapSequences) (u : ℝ),
        y.val ∈ localReconstructionEvent m R → 0 ≤ u → u ≤ (y.val 0 : ℝ) →
        (∀ j ∈ Finset.Ico (-(m : ℤ)) (m : ℤ), y.val j = y'.val j) →
        restrictConfiguration (Icc (-R) R) (translateConfiguration u (reconstructConfiguration y)) =
          restrictConfiguration (Icc (-R) R) (translateConfiguration u (reconstructConfiguration y'))) ∧
      Tendsto (fun m : ℕ => ⨆ N : {N : ℕ+ // 2 * m ≤ (N : ℕ)},
        ∫⁻ y in (localReconstructionEvent m R)ᶜ,
          ENNReal.ofReal (y 0 : ℝ) ∂periodicGapLaw p N.val) atTop (𝓝 0) ∧
      Tendsto (fun m : ℕ => ∫⁻ y in (localReconstructionEvent m R)ᶜ,
        ENNReal.ofReal (y 0 : ℝ) ∂q) atTop (𝓝 0) := by
  obtain ⟨q, hq, _⟩ := convergence_gap_limit_from_cauchy_internal hcomparison p
  exact ⟨q, ⟨hq.1, fun m hm y y' u hy hu huy he =>
    reconstructConfiguration_local_eq y y' m hm R u hy hu huy he,
    convergence_local_block_finite_weighted_tails p R,
    convergence_local_block_limit_weighted_tails_from_gap_limit_internal p q hq.1 R⟩,
    fun q' hq' => tendsto_nhds_unique hq'.1 hq.1⟩

/-- See the proof of Theorem 3 in the paper: on a closed window
strictly inside the quarter-period cutoff, the periodic and microscopic
configurations coincide pointwise, including the window endpoints. -/
theorem periodicSpatialConfiguration_restrict_eq_microscopic {N : ℕ+}
    (X : Riesz1.Configuration N) (R : ℝ) (hN : 4 * R < (N : ℝ)) :
    restrictConfiguration (Icc (-R) R) (periodicSpatialConfiguration X) =
      restrictConfiguration (Icc (-R) R) (microscopicConfiguration 0 X) := by
  have hpos : 0 < (N : ℝ) := by exact_mod_cast N.pos
  apply Subtype.ext
  ext x
  change (x ∈ (periodicSpatialConfiguration X).val ∧ x ∈ Icc (-R) R) ↔
    (x ∈ (microscopicConfiguration 0 X).val ∧ x ∈ Icc (-R) R)
  rw [periodicSpatialConfiguration_atoms]
  constructor
  · rintro ⟨⟨j, hj⟩, hx⟩
    obtain ⟨i, hi, q, he⟩ := Riesz1.exists_nat_add_mul (N := N) j
    subst j
    dsimp only at hj
    rw [Riesz1.cyclicLift_add_mul X hi q] at hj
    have hb : |(X.val ⟨i, hi⟩ : ℝ) + q| < 1 / 4 := by
      have hx' := abs_le.mpr hx
      rw [← hj, abs_mul, abs_of_pos hpos] at hx'
      nlinarith
    have hcircle : (((X.val ⟨i, hi⟩ : ℝ) + q : ℝ) : UnitAddCircle) =
        (X.val ⟨i, hi⟩ : UnitAddCircle) := by
      simp
    have hrep : Riesz1.centralRep Riesz1.unitLength (X.val ⟨i, hi⟩ : UnitAddCircle) =
        (X.val ⟨i, hi⟩ : ℝ) + q := by
      rw [← hcircle]
      apply Riesz1.centralRep_coe_of_mem
      change -(1 / 2 : ℝ) ≤ _ ∧ _ < 1 / 2
      exact ⟨by linarith [(abs_lt.mp hb).1], by linarith [(abs_lt.mp hb).2]⟩
    refine ⟨?_, hx⟩
    change ∃ i, |Riesz1.centralRep Riesz1.unitLength ((X.val i : UnitAddCircle) - (0 : UnitAddCircle))| < 1 / 4 ∧
      x = (N : ℝ) * Riesz1.centralRep Riesz1.unitLength ((X.val i : UnitAddCircle) - (0 : UnitAddCircle))
    exact ⟨⟨i, hi⟩, by simpa only [sub_zero, hrep] using hb,
      by simpa only [sub_zero, hrep] using hj.symm⟩
  · rintro ⟨hx, hxR⟩
    change ∃ i, |Riesz1.centralRep Riesz1.unitLength ((X.val i : UnitAddCircle) - (0 : UnitAddCircle))| < 1 / 4 ∧
      x = (N : ℝ) * Riesz1.centralRep Riesz1.unitLength ((X.val i : UnitAddCircle) - (0 : UnitAddCircle)) at hx
    obtain ⟨i, _, he⟩ := hx
    simp only [sub_zero] at he
    obtain ⟨q, hq⟩ := Riesz1.centralRep_coe_eq Riesz1.unitLength (X.val i : ℝ)
    have hq' : Riesz1.centralRep Riesz1.unitLength (X.val i : UnitAddCircle) = (X.val i : ℝ) - q := by
      simpa [Riesz1.unitLength] using hq
    refine ⟨⟨(i.val : ℤ) + (N : ℕ) * (-q), ?_⟩, hxR⟩
    dsimp only
    rw [Riesz1.cyclicLift_add_mul X i.isLt (-q), Int.cast_neg, he, hq']
    ring

/-- The spatial cutoff is exactly the strict quarter-period
restriction of the periodic configuration, on the whole carrier. -/
theorem microscopicConfiguration_zero_eq_restrict_periodic {N : ℕ+}
    (X : Riesz1.Configuration N) :
    microscopicConfiguration 0 X =
      restrictConfiguration (Ioo (-(N : ℝ) / 4) ((N : ℝ) / 4)) (periodicSpatialConfiguration X) := by
  have hpos : 0 < (N : ℝ) := by exact_mod_cast N.pos
  apply Subtype.ext
  ext x
  change x ∈ (microscopicConfiguration 0 X).val ↔
    (x ∈ (periodicSpatialConfiguration X).val ∧ -(N : ℝ) / 4 < x ∧ x < (N : ℝ) / 4)
  have hcut : x ∈ (microscopicConfiguration 0 X).val → |x| < (N : ℝ) / 4 := by
    rintro ⟨i, hi, he⟩
    rw [he, abs_mul, abs_of_pos hpos]
    nlinarith
  constructor
  · intro hx
    have hb := hcut hx
    have he := congrArg Subtype.val
      (periodicSpatialConfiguration_restrict_eq_microscopic X |x| (by linarith))
    have hx' : x ∈ Icc (-|x|) |x| := ⟨neg_abs_le _, le_abs_self _⟩
    have ht : x ∈ (restrictConfiguration (Icc (-|x|) |x|) (periodicSpatialConfiguration X)).val := by
      rw [he]
      exact ⟨hx, hx'⟩
    exact ⟨ht.1, by linarith [(abs_lt.mp hb).1], (abs_lt.mp hb).2⟩
  · rintro ⟨hx, hlo, hhi⟩
    have hb : |x| < (N : ℝ) / 4 := abs_lt.mpr ⟨by linarith, hhi⟩
    have he := congrArg Subtype.val
      (periodicSpatialConfiguration_restrict_eq_microscopic X |x| (by linarith))
    have ht : x ∈ (restrictConfiguration (Icc (-|x|) |x|) (microscopicConfiguration 0 X)).val := by
      rw [← he]
      exact ⟨hx, neg_abs_le _, le_abs_self _⟩
    exact ht.1

/-- Measurability of the actual microscopic cutoff follows from periodic
reconstruction and Borel restriction. It includes the one-particle volume. -/
theorem measurable_microscopicConfiguration_zero (N : ℕ+) :
    Measurable (@microscopicConfiguration N 0) := by
  have he : (@microscopicConfiguration N 0) =
      restrictConfiguration (Ioo (-(N : ℝ) / 4) ((N : ℝ) / 4)) ∘ periodicSpatialConfiguration :=
    funext microscopicConfiguration_zero_eq_restrict_periodic
  rw [he]
  exact (measurable_restrictConfiguration _ measurableSet_Ioo).comp
    (measurable_periodicSpatialConfiguration N)

/-- The actual finite microscopic law is a probability. -/
theorem microscopicLaw_probability (p : Parameters) (N : ℕ+) :
    IsProbabilityMeasure (microscopicLaw p N) := by
  have _ := gibbsMeasure_probability p N
  unfold microscopicLaw
  infer_instance

/-- The strict-quarter-circle law and the periodic law have exactly the same
closed-window pushforward as soon as `N > 4*R`. -/
theorem periodicSpatialLaw_restrict_eq_microscopicLaw (p : Parameters) (N : ℕ+)
    (R : ℝ) (hN : 4 * R < (N : ℝ)) :
    (periodicSpatialLaw p N).map (restrictConfiguration (Icc (-R) R)) =
      (microscopicLaw p N).map (restrictConfiguration (Icc (-R) R)) := by
  rw [periodicSpatialLaw, microscopicLaw,
    Measure.map_map (measurable_restrictConfiguration _ measurableSet_Icc)
      (measurable_periodicSpatialConfiguration N),
    Measure.map_map (measurable_restrictConfiguration _ measurableSet_Icc)
      (measurable_microscopicConfiguration_zero N)]
  congr 1
  funext X
  exact periodicSpatialConfiguration_restrict_eq_microscopic X R hN

end Riesz2
