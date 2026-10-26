/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.LocalReconstructionPart2
public import Riesz2.Thermodynamic.LocalTotalVariation
public import Riesz1.Kernel.AdmissibleExamplesCompactPrimitive

/-!
# Local total variation through finite reconstruction

Measurable finite-block suspension integrals for the proof of Theorem 3.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace Riesz2

local notation "Gaps" => (ℤ → Ioi (0 : ℝ))
local notation "blockProj" => (fun (m : ℕ) (y : Gaps) =>
  (WithLp.toLp 2 (fun j : Fin (2 * m) =>
    (y (-(m : ℤ) + (Fin.val j : ℤ)) : ℝ)) : EuclideanSpace ℝ (Fin (2 * m))))
local instance localTotalVariationPart2ConfigurationMeasurableSpace : MeasurableSpace LineConfiguration := configurationMeasurableSpace

/-- The truncated suspension integral of an event, using the literal finite
subconfiguration. It is defined on all positive sequences and all scales. -/
def localBlockEventIntegral (m : ℕ) (R : ℝ) (A : Set LineConfiguration) (y : Gaps) : ℝ≥0∞ :=
  (localReconstructionEvent m R).indicator (fun y =>
    ∫⁻ u in Ico (0 : ℝ) (y 0 : ℝ),
      A.indicator (fun _ => (1 : ℝ≥0∞))
        (restrictConfiguration (Icc (-R) R)
          (translateConfiguration u (gapBlockConfiguration m y)))) y

/-- The truncated event integral is measurable for the sigma algebra of the
finite Euclidean block, rather than just the full sequence sigma algebra. -/
theorem measurable_localBlockEventIntegral_block (m : ℕ) (hm : 2 ≤ m)
    (R : ℝ) (A : Set LineConfiguration) (hA : MeasurableSet A) :
    Measurable[(inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin (2 * m)))).comap
      (blockProj m)] (localBlockEventIntegral m R A) := by
  let M := (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin (2 * m)))).comap (blockProj m)
  let _ : MeasurableSpace Gaps := M
  have h0 : Measurable (fun y : Gaps => (y 0 : ℝ)) :=
    measurable_gapCoordinate_block m 0 (by simp only [Finset.mem_Ico]; omega)
  have hstrip : MeasurableSet {z : Gaps × ℝ | 0 ≤ z.2 ∧ z.2 < (z.1 0 : ℝ)} :=
    (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (h0.comp measurable_fst))
  have hmap : Measurable (fun z : Gaps × ℝ =>
      restrictConfiguration (Icc (-R) R)
        (translateConfiguration z.2 (gapBlockConfiguration m z.1))) :=
    (measurable_restrictConfiguration _ measurableSet_Icc).comp
      (measurable_translateConfiguration.comp
        (measurable_snd.prodMk ((measurable_gapBlockConfiguration_block m).comp measurable_fst)))
  have htest : Measurable (A.indicator (fun _ => (1 : ℝ≥0∞))) := measurable_const.indicator hA
  have h := ((htest.comp hmap).indicator hstrip).lintegral_prod_right'
    (ν := volume)
  have hi : Measurable (fun y : Gaps => ∫⁻ u in Ico (0 : ℝ) (y 0 : ℝ),
      A.indicator (fun _ => (1 : ℝ≥0∞))
        (restrictConfiguration (Icc (-R) R)
          (translateConfiguration u (gapBlockConfiguration m y)))) := by
    convert h using 1
    ext y
    exact (lintegral_indicator measurableSet_Ico _).symm
  exact hi.indicator (measurableSet_localReconstructionEvent_block m hm R)

/-- A suspension event integral is bounded by the length of its integration
interval, before taking any real-valued integral. -/
theorem localBlockEventIntegral_le (m : ℕ) (R : ℝ) (A : Set LineConfiguration) (y : Gaps) :
    localBlockEventIntegral m R A y ≤ ENNReal.ofReal (y 0 : ℝ) := by
  classical
  unfold localBlockEventIntegral
  by_cases hy : y ∈ localReconstructionEvent m R
  · rw [indicator_of_mem hy]
    calc
      _ ≤ ∫⁻ _u in Ico (0 : ℝ) (y 0 : ℝ), (1 : ℝ≥0∞) :=
        lintegral_mono fun u => by
          by_cases h : restrictConfiguration (Icc (-R) R)
            (translateConfiguration u (gapBlockConfiguration m y)) ∈ A <;> simp [h]
      _ = ENNReal.ofReal (y 0 : ℝ) := by simp
  · rw [indicator_of_notMem hy]
    exact bot_le

/-- See the proof of Theorem 3 in the paper: the actual truncated
event integral factors measurably through the specified finite block, with
the required pointwise gap envelope on the whole Euclidean carrier. -/
theorem localBlockEventIntegral_factor (m : ℕ) (hm : 2 ≤ m) (R : ℝ)
    (A : Set LineConfiguration) (hA : MeasurableSet A) :
    ∃ H : EuclideanSpace ℝ (Fin (2 * m)) → ℝ,
      Measurable H ∧ (∀ x, |H x| ≤ |x ⟨m, by omega⟩|) ∧
      ∀ y : Gaps, H (blockProj m y) = (localBlockEventIntegral m R A y).toReal := by
  obtain ⟨H, hH, he⟩ := Measurable.exists_eq_measurable_comp
    (measurable_localBlockEventIntegral_block m hm R A hA).ennreal_toReal
  let i : Fin (2 * m) := ⟨m, by omega⟩
  have hw : Measurable (fun x : EuclideanSpace ℝ (Fin (2 * m)) => |x i|) := by fun_prop
  refine ⟨fun x => max (-|x i|) (min (|x i|) (H x)), hw.neg.max (hw.min hH), ?_, ?_⟩
  · intro x
    exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith [abs_nonneg (x i)]) (min_le_left _ _)⟩
  · intro y
    have he' : H (blockProj m y) = (localBlockEventIntegral m R A y).toReal :=
      (congrFun he y).symm
    have hi : (blockProj m y) i = (y 0 : ℝ) := by
      change (y (-(m : ℤ) + (m : ℤ)) : ℝ) = _
      rw [neg_add_cancel]
    have hb := ENNReal.toReal_le_of_le_ofReal (y 0).property.le (localBlockEventIntegral_le m R A y)
    change max (-|(blockProj m y) i|) (min (|(blockProj m y) i|) (H (blockProj m y))) = _
    rw [he', hi, abs_of_pos (y 0).property, min_eq_right hb,
      max_eq_right (by linarith [ENNReal.toReal_nonneg (a := localBlockEventIntegral m R A y)])]

/-- The finite integral agrees with the actual suspension integrand on the
bracketing event. -/
theorem localBlockEventIntegral_reconstruction (m : ℕ) (hm : 2 ≤ m) (R : ℝ)
    (A : Set LineConfiguration) (y : reconstructibleGapSequences) :
    localBlockEventIntegral m R A y.val =
      {z : reconstructibleGapSequences | z.val ∈ localReconstructionEvent m R}.indicator
        (fun z => ∫⁻ u in Ico (0 : ℝ) (z.val 0 : ℝ),
          A.indicator (fun _ => (1 : ℝ≥0∞))
            (restrictConfiguration (Icc (-R) R)
              (translateConfiguration u (reconstructConfiguration z)))) y := by
  classical
  by_cases hy : y.val ∈ localReconstructionEvent m R
  · simp only [localBlockEventIntegral, indicator_of_mem hy,
      indicator_of_mem (show y ∈ {z : reconstructibleGapSequences |
        z.val ∈ localReconstructionEvent m R} from hy)]
    apply setLIntegral_congr_fun measurableSet_Ico
    intro u hu
    dsimp only
    rw [restrict_gapBlockConfiguration m hm R u y hy hu.1 hu.2.le]
  · simp only [localBlockEventIntegral, indicator_of_notMem hy,
      indicator_of_notMem (show y ∉ {z : reconstructibleGapSequences |
        z.val ∈ localReconstructionEvent m R} from hy)]

/-- See the proof of Theorem 3 in the paper: the measurable block
factor approximates every actual suspension event mass with precisely the
length-weighted exceptional-event error. -/
theorem localBlockEventIntegral_mass_approximation_internal
    (m : ℕ) (hm : 2 ≤ m) (R : ℝ) (A : Set LineConfiguration) (hA : MeasurableSet A)
    (H : EuclideanSpace ℝ (Fin (2 * m)) → ℝ) (hH : Measurable H)
    (he : ∀ y : Gaps, H (blockProj m y) = (localBlockEventIntegral m R A y).toReal)
    (μ : ProbabilityMeasure Gaps) (hs : ∀ᵐ y ∂μ.toMeasure, y ∈ reconstructibleGapSequences)
    (h0 : Integrable (fun y : Gaps => (y 0 : ℝ)) μ) :
    Integrable H (μ.map (blockProj m)) ∧
      ENNReal.ofReal |(((gapSuspensionMeasure (reconstructionGapMeasure μ.toMeasure)).map
        (restrictConfiguration (Icc (-R) R))) A).toReal -
          ∫ x, H x ∂(μ.map (blockProj m))| ≤
        ∫⁻ y in (localReconstructionEvent m R)ᶜ, ENNReal.ofReal (y 0 : ℝ) ∂μ := by
  let S := reconstructionGapMeasure μ.toMeasure
  have _ : IsProbabilityMeasure S := reconstructionGapMeasure_probability μ.toMeasure hs
  have hmap : S.map Subtype.val = μ.toMeasure := map_reconstructionGapMeasure μ.toMeasure hs
  have hproj : Measurable (blockProj m) := (continuous_gap_block_projection_internal (2 * m) _).measurable
  have hmF : Measurable (localBlockEventIntegral m R A) := by
    have ht := (measurable_localBlockEventIntegral_block m hm R A hA)
    exact ht.mono hproj.comap_le le_rfl
  have hfinite (y : Gaps) : localBlockEventIntegral m R A y ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (localBlockEventIntegral_le m R A y)
  have hi : Integrable (fun y : Gaps => H (blockProj m y)) μ := by
    apply h0.mono' (hH.comp hproj).aestronglyMeasurable
    exact ae_of_all _ fun y => by
      change ‖H (blockProj m y)‖ ≤ _
      rw [he, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.toReal_le_of_le_ofReal (y 0).property.le (localBlockEventIntegral_le m R A y)
  have hiH : Integrable H (μ.map (blockProj m)) :=
    (integrable_map_measure hH.aestronglyMeasurable hproj.aemeasurable).mpr hi
  refine ⟨hiH, ?_⟩
  have hreal : (∫ x, H x ∂μ.map (blockProj m)) =
      (∫⁻ y, localBlockEventIntegral m R A y ∂μ).toReal := by
    rw [ProbabilityMeasure.toMeasure_map, integral_map hproj.aemeasurable hH.aestronglyMeasurable]
    simp_rw [he]
    exact integral_toReal hmF.aemeasurable (ae_of_all _ fun y => lt_top_iff_ne_top.mpr (hfinite y))
  let J : reconstructibleGapSequences → ℝ≥0∞ := fun y =>
    ∫⁻ u in Ico (0 : ℝ) (y.val 0 : ℝ),
      A.indicator (fun _ => (1 : ℝ≥0∞))
        (restrictConfiguration (Icc (-R) R) (translateConfiguration u (reconstructConfiguration y)))
  let E : Set reconstructibleGapSequences := {y | y.val ∈ localReconstructionEvent m R}
  have hE : MeasurableSet E := (measurableSet_localReconstructionEvent m R).preimage measurable_subtype_coe
  have hJle (y : reconstructibleGapSequences) : J y ≤ ENNReal.ofReal (y.val 0 : ℝ) := by
    calc
      _ ≤ ∫⁻ _u in Ico (0 : ℝ) (y.val 0 : ℝ), (1 : ℝ≥0∞) := by
        apply lintegral_mono
        intro u
        by_cases h : restrictConfiguration (Icc (-R) R)
          (translateConfiguration u (reconstructConfiguration y)) ∈ A <;> simp [h]
      _ = _ := by simp
  have hmass : (((gapSuspensionMeasure S).map
      (restrictConfiguration (Icc (-R) R))) A) = ∫⁻ y, J y ∂S := by
    rw [Measure.map_apply (measurable_restrictConfiguration _ measurableSet_Icc) hA,
      ← lintegral_indicator_one ((measurable_restrictConfiguration _ measurableSet_Icc) hA)]
    change (∫⁻ C, (restrictConfiguration (Icc (-R) R) ⁻¹' A).indicator
      (fun _ => (1 : ℝ≥0∞)) C ∂gapSuspensionMeasure S) = _
    rw [lintegral_gapSuspensionMeasure S _
      (measurable_const.indicator ((measurable_restrictConfiguration _ measurableSet_Icc) hA))]
    rfl
  have htrunc : (∫⁻ y, localBlockEventIntegral m R A y ∂μ) = ∫⁻ y in E, J y ∂S := by
    rw [← hmap, lintegral_map hmF measurable_subtype_coe]
    simp_rw [localBlockEventIntegral_reconstruction m hm R]
    exact lintegral_indicator hE _
  have htail : (∫⁻ y in Eᶜ, ENNReal.ofReal (y.val 0 : ℝ) ∂S) =
      ∫⁻ y in (localReconstructionEvent m R)ᶜ, ENNReal.ofReal (y 0 : ℝ) ∂μ := by
    have hw : Measurable (fun y : Gaps => ENNReal.ofReal (y 0 : ℝ)) :=
      (measurable_subtype_coe.comp (measurable_pi_apply 0)).ennreal_ofReal
    rw [← lintegral_indicator hE.compl,
      ← lintegral_indicator (measurableSet_localReconstructionEvent m R).compl, ← hmap]
    rw [lintegral_map (hw.indicator (measurableSet_localReconstructionEvent m R).compl)
      measurable_subtype_coe]
    rfl
  have htotal : (∫⁻ y, J y ∂S) ≠ ⊤ := by
    have hbound := lintegral_mono hJle (μ := S)
    have hlen : (∫⁻ y, ENNReal.ofReal (y.val 0 : ℝ) ∂S) =
        ∫⁻ y : Gaps, ENNReal.ofReal (y 0 : ℝ) ∂μ := by
      have hw : Measurable (fun y : Gaps => ENNReal.ofReal (y 0 : ℝ)) :=
        (measurable_subtype_coe.comp (measurable_pi_apply 0)).ennreal_ofReal
      rw [← hmap, lintegral_map hw measurable_subtype_coe]
    rw [hlen] at hbound
    have hlenfinite : (∫⁻ y : Gaps, ENNReal.ofReal (y 0 : ℝ) ∂μ) ≠ ⊤ := by
      rw [← ofReal_integral_eq_lintegral_ofReal h0 (ae_of_all _ fun y => (y 0).property.le)]
      exact ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top hlenfinite hbound
  rw [hreal, hmass, htrunc]
  have hle : (∫⁻ y in E, J y ∂S) ≤ ∫⁻ y, J y ∂S := lintegral_mono' Measure.restrict_le_self le_rfl
  rw [← event_difference_eq_ofReal_abs _ _ htotal (ne_top_of_le_ne_top htotal hle),
    tsub_eq_zero_of_le hle, add_zero]
  apply tsub_le_iff_right.mpr
  rw [← lintegral_add_compl J hE, ← htail]
  rw [add_comm (∫⁻ y in Eᶜ, ENNReal.ofReal (y.val 0 : ℝ) ∂S)]
  exact add_le_add_right (lintegral_mono hJle) _

/-- See the proof of Theorem 3 in the paper: the complete spatial
transfer from the gap-limit and weighted block-convergence clauses. The block total variation convergence is a hypothesis. -/
theorem convergence_local_total_variation_from_gap_predecessors_internal
    (p : Parameters) (q : ProbabilityMeasure Gaps)
    (hq : Tendsto (fun n : ℕ => periodicGapLaw p n.succPNat) atTop (𝓝 q))
    (hs : ∀ᵐ y ∂q.toMeasure, y ∈ reconstructibleGapSequences)
    (hmean : Integrable (fun y : Gaps => (y 0 : ℝ)) q ∧ (∫ y : Gaps, (y 0 : ℝ) ∂q) = 1)
    (hweighted : ∀ (m : ℕ) (hm : 2 ≤ m),
      Tendsto (fun n : ℕ => ⨆ F : {F : EuclideanSpace ℝ (Fin (2 * m)) → ℝ //
          Measurable F ∧ ∀ x, |F x| ≤ 1},
        ENNReal.ofReal |(∫ x, x ⟨m, by omega⟩ * F.val x
          ∂((periodicGapLaw p n.succPNat).map (blockProj m))) -
            (∫ x, x ⟨m, by omega⟩ * F.val x ∂(q.map (blockProj m)))|) atTop (𝓝 0))
    (R : ℝ) :
    letI (N : ℕ+) := microscopicLaw_probability p N
    letI := reconstructionGapMeasure_probability q.toMeasure hs
    let hm := reconstructionGapMeasure_mean q.toMeasure hs 0 hmean.1 hmean.2
    letI := gapSuspensionMeasure_probability _ hm.1 hm.2
    Tendsto (fun n : ℕ => totalVariation
      ((microscopicLaw p n.succPNat).map (restrictConfiguration (Icc (-R) R)))
      ((gapSuspensionMeasure (reconstructionGapMeasure q.toMeasure)).map
        (restrictConfiguration (Icc (-R) R)))) atTop (𝓝 0) := by
  have hqprob := reconstructionGapMeasure_probability q.toMeasure hs
  have hqmean := reconstructionGapMeasure_mean q.toMeasure hs 0 hmean.1 hmean.2
  have _ := gapSuspensionMeasure_probability _ hqmean.1 hqmean.2
  have hp (N : ℕ+) := periodicSpatialLaw_probability p N
  let _ (N : ℕ+) := hp N
  let P : ℕ → Measure LineConfiguration := fun n =>
    (periodicSpatialLaw p n.succPNat).map (restrictConfiguration (Icc (-R) R))
  let Q : Measure LineConfiguration :=
    (gapSuspensionMeasure (reconstructionGapMeasure q.toMeasure)).map
      (restrictConfiguration (Icc (-R) R))
  have hpmap (n : ℕ) : IsProbabilityMeasure (P n) := by
    dsimp [P]; infer_instance
  let _ (n : ℕ) := hpmap n
  have _ : IsProbabilityMeasure Q := by
    dsimp [Q]; infer_instance
  let eP : ℕ → ℝ≥0∞ := fun m => ⨆ N : {N : ℕ+ // 2 * (m + 2) ≤ (N : ℕ)},
    ∫⁻ y in (localReconstructionEvent (m + 2) R)ᶜ,
      ENNReal.ofReal (y 0 : ℝ) ∂periodicGapLaw p N.val
  let eQ : ℕ → ℝ≥0∞ := fun m => ∫⁻ y in (localReconstructionEvent (m + 2) R)ᶜ,
    ENNReal.ofReal (y 0 : ℝ) ∂q
  have heP : Tendsto eP atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 2).mpr (convergence_local_block_finite_weighted_tails p R)
  have heQ : Tendsto eQ atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 2).mpr
      (convergence_local_block_limit_weighted_tails_from_gap_limit_internal p q hq R)
  let V : ℕ → ℕ+ := fun n => (n + 1).succPNat
  have hV : ∀ n, 2 ≤ (V n : ℕ) := by intro n; simp [V]
  have hqV : Tendsto (fun n => periodicGapLaw p (V n)) atTop (𝓝 q) :=
    (tendsto_add_atTop_iff_nat 1).mpr hq
  obtain ⟨D, _, hfinite, _⟩ := periodicGapLaw_limit_all_moments p V hV q hqV 2 (by norm_num)
  have h0 (N : ℕ+) : Integrable (fun y : Gaps => (y 0 : ℝ)) (periodicGapLaw p N) :=
    (gapCoordinate_memLp_two_internal _ 0
      (((le_add_right le_rfl).trans (hfinite N 0)).trans_lt ENNReal.ofReal_lt_top)).integrable
        (by norm_num)
  have hsN (N : ℕ+) : ∀ᵐ y ∂(periodicGapLaw p N).toMeasure,
      y ∈ reconstructibleGapSequences := by
    rw [periodicGapLaw_toMeasure]
    exact (ae_map_iff (measurable_periodicGapSequence N).aemeasurable
      measurableSet_reconstructibleGapSequences).mpr
        (ae_of_all _ fun X => finite_configuration_mem_reconstructibleGapSequences X)
  have hperiodic : Tendsto (fun n => totalVariation (P n) Q) atTop (𝓝 0) := by
    apply totalVariation_tendsto_of_weighted_event_approximations
      (fun m n => ((periodicGapLaw p n.succPNat).map (blockProj (m + 2))).toMeasure)
      (fun m => (q.map (blockProj (m + 2))).toMeasure) P Q
      (fun m x => x ⟨m + 2, by omega⟩) (fun _ => by fun_prop)
      eP eQ heP heQ (fun m => hweighted (m + 2) (by omega))
    intro m
    filter_upwards [eventually_ge_atTop (2 * (m + 2))] with n hn
    intro A hA
    obtain ⟨H, hH, hb, he⟩ := localBlockEventIntegral_factor (m + 2) (by omega) R A hA
    obtain ⟨hiN, hN⟩ := localBlockEventIntegral_mass_approximation_internal
      (m + 2) (by omega) R A hA H hH he (periodicGapLaw p n.succPNat)
        (hsN _) (h0 _)
    obtain ⟨hiq, hq'⟩ := localBlockEventIntegral_mass_approximation_internal
      (m + 2) (by omega) R A hA H hH he q hs hmean.1
    refine ⟨H, hH, hb, hiN, hiq, ?_, hq'⟩
    rw [reconstructionGapMeasure_periodicGapLaw, gapSuspensionMeasure_finite] at hN
    exact hN.trans (le_iSup_of_le (⟨n.succPNat, by simp only [Nat.succPNat_coe]; omega⟩ :
      {N : ℕ+ // 2 * (m + 2) ≤ (N : ℕ)}) le_rfl)
  apply hperiodic.congr'
  have hlarge : ∀ᶠ n : ℕ in atTop, 4 * R < (n.succPNat : ℝ) :=
    ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).eventually
      (eventually_gt_atTop (4 * R)))
  filter_upwards [hlarge] with n hn
  simp only [totalVariation, Q, show P n = (microscopicLaw p n.succPNat).map (restrictConfiguration (Icc (-R) R)) from
    periodicSpatialLaw_restrict_eq_microscopicLaw p _ R hn]

end Riesz2
