/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.IntervalCoefficientsPart2
public import Riesz2.DecayShort.ObservableTransfer
public import Riesz2.ToMathlib.PowerTailBounds
public import Mathlib.MeasureTheory.Function.Holder

/-!
# Coefficient moments for both physical active tilts

See Subsection 4.5 of the paper: uniform normalization, actual conditional disintegration,
and coefficient moments including the optional inverse-gap penalty.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff ENNReal ProbabilityTheory Classical

namespace Riesz2.DecayShort

/-- See Subsection 4.5 of the paper, normalization input: a strictly positive uniform
lower bound for both active tilts, on any compact positive temperature range.
The bound also covers full-cycle tilts and every bounded active size. -/
theorem activeTilt_normalizer_uniform_lower (s βlo βhi h Cθ : ℝ) (hs : 1 < s)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (hh : 0 < h) (hCθ : 1 ≤ Cθ) :
    ∃ z : ℝ, 0 < z ∧ z ≤ 1 / 2 ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (N n : ℕ+), 2 ≤ (N : ℕ) →
      ∀ (hn : (n : ℕ) ≤ (N : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ ι : Bool, ENNReal.ofReal z ≤ tiltNormalizer p N n hn θ h ι := by
  obtain ⟨A, hA, hInv⟩ := SingleGapTails.inverse_exponential_moment s βlo βhi
    (by linarith) hlo hle
  obtain ⟨D, hD, hmom⟩ := SingleGapTails.single_gap_moment_integrals s βlo βhi
    (by linarith) (ne_of_gt hs) hlo hle 2 (by norm_num)
  let c := min (Real.log 2 / 8) (βlo / 2 ^ s)
  have hc : 0 < c := lt_min (div_pos (Real.log_pos one_lt_two) (by norm_num))
    (div_pos hlo (by positivity))
  obtain ⟨K, hK, hdec⟩ := MomentEvent.exists_rpow_mul_exp_neg_le (a := 1)
    (c := c) (c' := c / 2) (δ := h) hh (by linarith)
  obtain ⟨n₀, hlarge⟩ := exists_threshold_exp (Kq := (3 + A) * K)
    (c := c / 2) (δ := h) hh (by linarith)
  let z := min (1 / 2) (Real.exp (-βhi * ((n₀ : ℝ) * (Cθ * D))))
  refine ⟨z, lt_min (by norm_num) (Real.exp_pos _), min_le_left _ _, ?_⟩
  intro p hp hpl hph N n hN hn θ hcurv ι
  let I := Finset.univ.map (Fin.castLEEmb hn)
  have hcard : I.card = (n : ℕ) := by simp [I]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hR : 1 ≤ (n : ℝ) ^ h := Real.one_le_rpow hn1 hh.le
  have := gibbsMeasure_probability p N
  have hm (j : ℤ) : Integrable (fun X : Riesz1.Configuration N => gap X j ^ (2 : ℝ))
      (gibbsMeasure p N) ∧
      Integrable (fun X : Riesz1.Configuration N => gap X j ^ (-(2 : ℝ))) (gibbsMeasure p N) ∧
      (∫ X, gap X j ^ (2 : ℝ) ∂gibbsMeasure p N) +
        (∫ X, gap X j ^ (-(2 : ℝ)) ∂gibbsMeasure p N) ≤ D := by
    obtain ⟨h₁, h₂, h₃⟩ := hmom p hp hpl hph N hN j
    refine ⟨h₁, h₂, ?_⟩
    have he (t : ℝ) : ∫ X, gap X j ^ t ∂gibbsMeasure p N =
        (∫⁻ X, ENNReal.ofReal (gap X j ^ t) ∂gibbsMeasure p N).toReal :=
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun X =>
        Real.rpow_nonneg (Riesz1.gap_pos X j).le t)
        ((Riesz1.measurable_gap j).pow_const t).aestronglyMeasurable
    rw [he, he, ← ENNReal.toReal_add
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((le_add_of_nonneg_right (by positivity)).trans h₃))
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((le_add_of_nonneg_left (by positivity)).trans h₃))]
    exact ENNReal.toReal_le_of_le_ofReal hD.le h₃
  have hbound : z ≤ NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (activeGapPenalty θ ((n : ℝ) ^ h) ι I) := by
    by_cases hnlarge : n₀ ≤ (n : ℕ)
    · have htail (j : ℤ) (u : ℝ) :
          gibbsMeasure p N {X | u ≤ gap X j ^ (-s)} ≤
            ENNReal.ofReal (A * Real.exp (-βlo * u)) := by
        have hi := hInv p hp hpl hph N hN j
        exact ExponentialPower.closed_tail hlo hi.1 hi.2 u
      have hmass := activeGap_mass_le_exp p hN θ hs hlo hA.le hR
        (min_le_left _ _) (min_le_right _ _) htail ι I
      rw [hcard] at hmass
      have hd := hdec (n : ℝ) hn1
      rw [Real.rpow_one] at hd
      have hmhalf : (gibbsMeasure p N).real
          {X | activeGapPenalty θ ((n : ℝ) ^ h) ι I X ≠ 0} ≤ 1 / 2 := by
        calc
          _ ≤ (n : ℝ) * ((3 + A) * Real.exp (-c * (n : ℝ) ^ h)) := hmass
          _ = (3 + A) * ((n : ℝ) * Real.exp (-c * (n : ℝ) ^ h)) := by ring
          _ ≤ (3 + A) * (K * Real.exp (-(c / 2) * (n : ℝ) ^ h)) :=
            mul_le_mul_of_nonneg_left hd (by linarith)
          _ = ((3 + A) * K) * Real.exp (-(c / 2) * (n : ℝ) ^ h) := by ring
          _ ≤ 1 / 2 := hlarge n hnlarge
      have hone := NonnegativeTilt.one_sub_expTiltNormalizer_le
        (μ := gibbsMeasure p N) (activeGapPenalty_measurable θ (R := (n : ℝ) ^ h) (by positivity) ι I)
        p.property.1.le (activeGapPenalty_nonneg θ (R := (n : ℝ) ^ h) (by positivity) ι I)
      have hzhalf : z ≤ 1 / 2 := min_le_left _ _
      exact hzhalf.trans (by linarith)
    · have hjen := expTiltNormalizer_ge_of_card p θ (by linarith : 0 ≤ Cθ)
        (GoodBlocks.cutoff_quadratic θ hCθ hcurv) hR hm ι I
      rw [hcard] at hjen
      refine (min_le_right _ _).trans ((Real.exp_le_exp.mpr ?_).trans hjen)
      have hnsmall : (n : ℝ) ≤ n₀ := by exact_mod_cast (show (n : ℕ) ≤ n₀ by omega)
      have hmul := mul_le_mul hph
        (mul_le_mul_of_nonneg_right hnsmall (mul_nonneg (by linarith : 0 ≤ Cθ) hD.le))
        (by positivity : 0 ≤ (n : ℝ) * (Cθ * D)) (by linarith : 0 ≤ βhi)
      linarith
  have he := NonnegativeTilt.lintegral_normalizer_eq
    (μ := gibbsMeasure p N) (activeGapPenalty_measurable θ (R := (n : ℝ) ^ h) (by positivity) ι I)
    p.property.1.le (activeGapPenalty_nonneg θ (R := (n : ℝ) ^ h) (by positivity) ι I)
  rw [activeGapPenalty_firstGapSet hn θ h ι] at he hbound
  exact (ENNReal.ofReal_le_ofReal hbound).trans_eq he.symm

/-- Internal density-to-norm transport for either active tilt. -/
theorem internal_activeTilt_norm_le {p : Parameters} {N n : ℕ+}
    {hn : (n : ℕ) ≤ (N : ℕ)} {θ : PhysicalCutoff} {h z : ℝ} {ι : Bool}
    (hz : 0 < z) (hz1 : z ≤ 1)
    (hZ : ENNReal.ofReal z ≤ tiltNormalizer p N n hn θ h ι)
    (f : Riesz1.Configuration N → ℝ) {q : ℝ} (hq : 1 ≤ q) :
    eLpNorm f (ENNReal.ofReal q) (tiltedParticleMeasure p N n hn θ h ι) ≤
      ENNReal.ofReal z⁻¹ * eLpNorm f (ENNReal.ofReal q) (gibbsMeasure p N) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hmeasure : tiltedParticleMeasure p N n hn θ h ι ≤
      ENNReal.ofReal z⁻¹ • gibbsMeasure p N := by
    have hden : (gibbsMeasure p N).withDensity (fun X =>
        ENNReal.ofReal (Real.exp (-p.val.1 * physicalGapPenalty N n hn θ h ι X))) ≤
          gibbsMeasure p N := by
      refine (withDensity_mono (ae_of_all _ (fun X => ?_))).trans_eq withDensity_one
      exact ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (by linarith [p.property.1])
          (DefinitionSanity.penalty_nonneg N n hn θ h ι X)))
    have hinv := ENNReal.inv_le_inv.mpr hZ
    rw [← ENNReal.ofReal_inv_of_pos hz] at hinv
    change (tiltNormalizer p N n hn θ h ι)⁻¹ • _ ≤ _
    calc
      _ ≤ (tiltNormalizer p N n hn θ h ι)⁻¹ • gibbsMeasure p N := by gcongr
      _ ≤ _ := by gcongr
  have hnorm := (eLpNorm_mono_measure f hmeasure).trans
    (eLpNorm_smul_measure_le (ENNReal.ofReal z⁻¹) f (ENNReal.ofReal q) (gibbsMeasure p N))
  simp only [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal hq0.le, smul_eq_mul] at hnorm
  refine hnorm.trans (mul_le_mul_left ?_ _)
  rw [ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr hz.le) (inv_nonneg.mpr hq0.le)]
  apply ENNReal.ofReal_le_ofReal
  calc
    z⁻¹ ^ q⁻¹ ≤ z⁻¹ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le
      ((one_le_inv₀ hz).mpr hz1) ((inv_le_one₀ hq0).mpr hq)
    _ = z⁻¹ := Real.rpow_one _

/-- See Subsection 4.5 of the paper, the interval coefficient estimate for both tilts,
including a full active cycle. The degree depends only on `s`. -/
theorem activeTilt_interval_moments (s βlo βhi h Cθ : ℝ) (hs : 1 < s)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (hh : 0 < h) (hCθ : 1 ≤ Cθ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (N n : ℕ+), 2 ≤ (N : ℕ) →
      ∀ (hn : (n : ℕ) ≤ (N : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ (ι : Bool) (t : Fin (N : ℕ) × Fin ((N : ℕ) / 2)) (q : ℝ), 1 ≤ q →
        eLpNorm (fun X : Riesz1.Configuration N => intervalWeight p N t
          ⟨WithLp.toLp 2 (gapVector X), GapChart.gapVector_mem_gapAmbientDomain X⟩)
          (ENNReal.ofReal q) (tiltedParticleMeasure p N n hn θ h ι) ≤
            ENNReal.ofReal (C * q ^ ((s + 2) / s) * (t.2.val + 1 : ℝ) ^ (-s - 2)) := by
  obtain ⟨D, hD, hcoeff⟩ := GoodBlocks.particleCoefficient_moments s βlo βhi
    (by linarith) hlo hle
  obtain ⟨z, hz, hzhalf, hnorm⟩ := activeTilt_normalizer_uniform_lower
    s βlo βhi h Cθ hs hlo hle hh hCθ
  refine ⟨z⁻¹ * D, by positivity, ?_⟩
  intro p hp hpl hph N n hN hn θ hcurv ι t q hq
  simp_rw [intervalWeight_gapVector]
  have hdom := internal_activeTilt_norm_le hz (by linarith)
    (hnorm p hp hpl hph N n hN hn θ hcurv ι)
    (GoodBlocks.particleCoefficient p N t.1.val (t.2.val + 1) (by omega)
      (by have := t.2.isLt; omega)) hq
  refine hdom.trans ((mul_le_mul_right (hcoeff p hp hpl hph N hN t.1.val
    (t.2.val + 1) (by omega) (by have := t.2.isLt; omega) q hq) _).trans_eq ?_)
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hz.le)]
  congr 1
  push_cast
  ring

/-- See Subsection 4.5 of the paper, disintegration input: the actual retained marginal and the physical conditional kernel for either active tilt. -/
theorem activeTilt_proper_disintegration (p : Parameters) (n : ℕ+) (m : ℕ)
    (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (θ : PhysicalCutoff) (ε : ℝ) (ι : Bool) :
    (tiltedParticleMeasure p ((n : ℕ) + m).succPNat n hn θ ε ι).map
      (fun X : Riesz1.Configuration ((n : ℕ) + m).succPNat =>
        RetainedSimplex.coordinates n m (Equiv.refl _) (WithLp.toLp 2 (gapVector X))) =
      (((activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ ε ι).comap
        ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
          EuclideanSpace ℝ (Fin (n : ℕ)))) ⊗ₘ
        ProperMarginalChart.conditionalKernel p n m n.pos (Equiv.refl _)).map
          (fun q => (q.1.val, q.2)) := by
  let K := ProperMarginalChart.conditionalKernel p n m n.pos (Equiv.refl _)
  let B := AffineSimplex.chartDomain n ((n + m : ℕ) + 1)
  let μ₀ : Measure B :=
    (tiltNormalizer p ((n : ℕ) + m).succPNat n hn θ ε ι)⁻¹ •
      (partitionFunction p ((n : ℕ) + m).succPNat)⁻¹ •
        ENNReal.ofReal ((n + m + 1 : ℝ) ^ ((n : ℕ) + m))⁻¹ •
          (((volume : Measure (EuclideanSpace ℝ (Fin (n : ℕ)))).comap
            ((↑) : B → EuclideanSpace ℝ (Fin (n : ℕ)))).withDensity
              (fun x => AffineFibre.fibreMass volume
                (ProperMarginalChart.penalizedChartDensity p n m (Equiv.refl _) θ
                  ((n : ℝ) ^ (-ε)) (Finset.univ.map (Fin.castLEEmb hn)) ι) x.val))
  have hj := ProperMarginalChart.tilted_coordinates_disintegration p n m n.pos
    (Equiv.refl _) n hn θ ε ι (fun i hi => by
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
      exact ⟨j, Fin.ext rfl⟩)
  have hinc : Measurable (fun q : B × EuclideanSpace ℝ (Fin m) => (q.1.val, q.2)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  have hj' : (tiltedParticleMeasure p ((n : ℕ) + m).succPNat n hn θ ε ι).map
      (fun X : Riesz1.Configuration ((n : ℕ) + m).succPNat =>
        RetainedSimplex.coordinates n m (Equiv.refl _) (WithLp.toLp 2 (gapVector X))) =
      (μ₀ ⊗ₘ K).map (fun q => (q.1.val, q.2)) := by
    simpa only [μ₀, Measure.compProd_smul_left,
      Measure.map_smul _ hinc.aemeasurable] using hj
  have hbase : activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ ε ι =
      μ₀.map ((↑) : B → EuclideanSpace ℝ (Fin (n : ℕ))) := by
    have he := congrArg (Measure.map Prod.fst) hj'
    have hc : Measurable (fun X : Riesz1.Configuration ((n : ℕ) + m).succPNat =>
        RetainedSimplex.coordinates n m (Equiv.refl _) (WithLp.toLp 2 (gapVector X))) :=
      (RetainedSimplex.continuous_coordinates n m (Equiv.refl _)).measurable.comp
        ((PiLp.volume_preserving_toLp _).measurable.comp (Riesz1.measurable_gapVector _))
    rw [Measure.map_map measurable_fst hc, Measure.map_map measurable_fst hinc] at he
    have hcoords : (fun X : Riesz1.Configuration ((n : ℕ) + m).succPNat =>
        (RetainedSimplex.coordinates n m (Equiv.refl _) (WithLp.toLp 2 (gapVector X))).1) =
        fun X => WithLp.toLp 2 (finiteGapBlock X) := by
      funext X
      ext i
      rw [RetainedSimplex.coordinates_retained]
      rfl
    simp only [Function.comp_def] at he
    rw [hcoords] at he
    change activeTiltedGapLaw p _ n hn θ ε ι = _ at he
    refine he.trans ?_
    change (μ₀ ⊗ₘ K).map (Subtype.val ∘ Prod.fst) = _
    rw [← Measure.map_map measurable_subtype_coe measurable_fst]
    change ((μ₀ ⊗ₘ K).fst).map _ = _
    rw [Measure.fst_compProd]
  rw [hbase, (MeasurableEmbedding.subtype_coe
    (AffineSimplex.isOpen_chartDomain n _).measurableSet).comap_map]
  exact hj'

/-- See Subsection 4.5 of the paper, probability input on the retained
carrier, for both active tilts. -/
theorem activeTilt_proper_probability (p : Parameters) (n : ℕ+) (m : ℕ)
    (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (θ : PhysicalCutoff) (ε : ℝ) (ι : Bool) :
    IsProbabilityMeasure ((activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ ε ι).comap
      ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
        EuclideanSpace ℝ (Fin (n : ℕ)))) := by
  have : IsProbabilityMeasure (tiltedParticleMeasure p ((n : ℕ) + m).succPNat n hn θ ε ι) :=
    DefinitionSanity.tilted_probability _ _ _ _ _ _ _
  have : IsProbabilityMeasure (activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ ε ι) :=
    DefinitionSanity.active_tilted_probability _ _ _ _ _ _ _
  have hc : Measurable (fun X : Riesz1.Configuration ((n : ℕ) + m).succPNat =>
      RetainedSimplex.coordinates n m (Equiv.refl _) (WithLp.toLp 2 (gapVector X))) :=
    (RetainedSimplex.continuous_coordinates n m (Equiv.refl _)).measurable.comp
      ((PiLp.volume_preserving_toLp _).measurable.comp (Riesz1.measurable_gapVector _))
  have hi : Measurable (fun q : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) ×
      EuclideanSpace ℝ (Fin m) => (q.1.val, q.2)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  have hh := congrArg (fun μ => μ univ) (activeTilt_proper_disintegration p n m hn θ ε ι)
  simp only [Measure.map_apply hc MeasurableSet.univ,
    Measure.map_apply hi MeasurableSet.univ, preimage_univ, measure_univ,
    Measure.compProd_apply MeasurableSet.univ, measure_univ,
    lintegral_one] at hh
  exact ⟨hh.symm⟩

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 4.5 of the paper, sharp conditional interval moments for either
tilt under the retained marginal. -/
theorem activeTilt_conditional_interval_moments (s βlo βhi h Cθ : ℝ) (hs : 1 < s)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (hh : 0 < h) (hCθ : 1 ≤ Cθ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (n : ℕ+) (m : ℕ)
      (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ (ι : Bool) (t : Fin ((n : ℕ) + m + 1) × Fin (((n : ℕ) + m + 1) / 2)) (q : ℝ), 1 ≤ q →
        eLpNorm (fun x => conditionalIntervalWeight p n m n.pos (Equiv.refl _) x t)
          (ENNReal.ofReal q)
          ((activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ h ι).comap
            ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
              EuclideanSpace ℝ (Fin (n : ℕ)))) ≤
            ENNReal.ofReal (C * q ^ ((s + 2) / s) * (t.2.val + 1 : ℝ) ^ (-s - 2)) := by
  obtain ⟨C, hC, hb⟩ := activeTilt_interval_moments s βlo βhi h Cθ hs hlo hle hh hCθ
  refine ⟨C, hC, fun p hp hpl hph n m hn θ hcurv ι t q hq => ?_⟩
  let μ := (activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ h ι).comap
    ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
  let K := ProperMarginalChart.conditionalKernel p n m n.pos (Equiv.refl _)
  let f := fun w : EuclideanSpace ℝ (Fin (n : ℕ)) × EuclideanSpace ℝ (Fin m) =>
    (2 - if 2 * (t.2.val + 1) = (n : ℕ) + m + 1 then (1 : ℝ) else 0) *
      (p.val.2 * (p.val.2 + 1) * ∑' k : ℤ,
        |PhysicalEnergy.intervalLinear ((n : ℕ) + m).succPNat t.1 (t.2.val + 1)
          (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) w) +
          k * (((n : ℕ) + m + 1 : ℕ) : ℝ)| ^ (-p.val.2 - 2))
  have hf : Measurable f := by
    apply Measurable.const_mul
    apply Measurable.const_mul
    apply Measurable.tsum
    intro k
    exact (((PhysicalEnergy.intervalLinear ((n : ℕ) + m).succPNat t.1 (t.2.val + 1)).continuous.measurable.comp
      (RetainedSimplex.continuous_chart n m _ (Equiv.refl _)).measurable).add_const _).abs.pow_const _
  let inc := fun w : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) ×
    EuclideanSpace ℝ (Fin m) => (w.1.val,w.2)
  have hi : Measurable inc :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  let : IsProbabilityMeasure μ := activeTilt_proper_probability p n m hn θ h ι
  have hJ := activeTilt_proper_disintegration p n m hn θ h ι
  change _ = (μ ⊗ₘ K).map inc at hJ
  have hc : Measurable (fun X : Riesz1.Configuration ((n : ℕ) + m).succPNat =>
      RetainedSimplex.coordinates n m (Equiv.refl _) (WithLp.toLp 2 (gapVector X))) :=
    (RetainedSimplex.continuous_coordinates n m (Equiv.refl _)).measurable.comp
      ((PiLp.volume_preserving_toLp _).measurable.comp (Riesz1.measurable_gapVector _))
  have htN : t.2.val + 1 ≤ (((n : ℕ) + m).succPNat : ℕ) / 2 := by
    simpa only [Nat.succPNat_coe, Nat.succ_eq_add_one] using Nat.succ_le_of_lt t.2.isLt
  have hnorm : eLpNorm (f ∘ inc) (ENNReal.ofReal q) (μ ⊗ₘ K) =
      eLpNorm (GoodBlocks.particleCoefficient p ((n : ℕ) + m).succPNat t.1.val
        (t.2.val + 1) (by omega) htN) (ENNReal.ofReal q)
        (tiltedParticleMeasure p ((n : ℕ) + m).succPNat n hn θ h ι) := by
    rw [← eLpNorm_map_measure hf.aestronglyMeasurable hi.aemeasurable, ← hJ,
      eLpNorm_map_measure hf.aestronglyMeasurable hc.aemeasurable]
    apply eLpNorm_congr_ae
    apply ae_of_all
    intro X
    dsimp only [Function.comp_def, f]
    rw [GoodBlocks.retained_chart_gapVector, PhysicalEnergy.intervalLinear_apply,
      GapChart.cyclicGapSum_gapVector, GoodBlocks.particleCoefficient_images]
    simp only [Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add]
  have hj := eLpNorm_integral_kernel_le μ K (hf.comp hi) hq
  have he : (fun x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) =>
      ∫ z, (f ∘ inc) (x,z) ∂K x) =
      fun x => conditionalIntervalWeight p n m n.pos (Equiv.refl _) x t := by
    funext x
    exact (conditionalIntervalWeight_images p n m n.pos (Equiv.refl _) x t).symm
  rw [he, hnorm] at hj
  apply hj.trans
  have hb' := hb p hp hpl hph ((n : ℕ) + m).succPNat n
    (by simp only [Nat.succPNat_coe]; have := n.pos; omega) hn θ hcurv ι t q hq
  simp_rw [intervalWeight_gapVector] at hb'
  exact hb'

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 4.5 of the paper, sharp conditional `P` moments for both active
tilts, with degree depending only on `s` and compact-temperature uniformity. -/
theorem activeTilt_conditional_P_moments (s βlo βhi h Cθ : ℝ) (hs : 1 < s)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (hh : 0 < h) (hCθ : 1 ≤ Cθ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (n : ℕ+) (m : ℕ)
      (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ (ι : Bool) (i j : Fin (n : ℕ)) (q : ℝ), 1 ≤ q →
        eLpNorm (fun x => IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat n hn
          (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x) i j)
          (ENNReal.ofReal q)
          ((activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ h ι).comap
            ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
              EuclideanSpace ℝ (Fin (n : ℕ)))) ≤
            ENNReal.ofReal (C * q ^ ((s + 2) / s) *
              (1 + (Riesz1.cyclicIndexDistance ((n : ℕ) + m).succPNat
                (Fin.castLE hn i) (Fin.castLE hn j) : ℝ)) ^ (-s)) := by
  obtain ⟨C, hC, hb⟩ := activeTilt_conditional_interval_moments s βlo βhi h Cθ hs hlo hle hh hCθ
  have hs0 : 0 < s := by linarith
  refine ⟨C * (1 + 1 / s), mul_pos hC (by positivity), ?_⟩
  intro p hp hpl hph n m hn θ hcurv ι i j q hq
  let μ := (activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ h ι).comap
    ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
  let A := fun a r x => conditionalIntervalWeight p n m n.pos (Equiv.refl _) x (a,r)
  have hcoeff (a : Fin ((n : ℕ) + m + 1)) (r : Fin (((n : ℕ) + m + 1) / 2)) :
      eLpNorm (A a r) (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal ((C * q ^ ((s + 2) / s)) * (r.val + 1 : ℝ) ^ (-s - 2)) :=
    hb p hp hpl hph n m hn θ hcurv ι (a,r) q hq
  have hnorm := interval_matrix_eLpNorm_le μ ((n : ℕ) + m).succPNat
    (by linarith : 0 < s) hq (by positivity : 0 ≤ C * q ^ ((s + 2) / s))
    A hcoeff (Fin.castLE hn i) (Fin.castLE hn j)
  have he : (fun x => IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat n hn
      (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x) i j) =
      fun x => ∑ r : Fin (((n : ℕ) + m + 1) / 2), ∑ a : Fin ((n : ℕ) + m + 1),
        if Fin.castLE hn i ∈ cyclicIndexInterval ((n : ℕ) + m).succPNat a (r.val + 1) ∧
          Fin.castLE hn j ∈ cyclicIndexInterval ((n : ℕ) + m).succPNat a (r.val + 1)
        then A a r x else 0 := by
    classical
    funext x
    rw [IntervalBoundary.intervalMatrix, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro a _
    dsimp only [IntervalBoundary.rankOne, IntervalBoundary.trace, A]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hi : Fin.castLE hn i ∈ cyclicIndexInterval ((n : ℕ) + m).succPNat a (r.val + 1) <;>
      by_cases hj : Fin.castLE hn j ∈ cyclicIndexInterval ((n : ℕ) + m).succPNat a (r.val + 1) <;>
      simp only [hi, hj, and_self, and_false, false_and, ↓reduceIte, mul_one, mul_zero]
  rw [he]
  refine hnorm.trans_eq ?_
  congr 1
  ring

/-- See Subsection 4.5 of the paper, unconditional full-cycle Hessian entry
profile for both tilts. It also holds before marginalization for any active size. -/
theorem activeTilt_hessian_moments (s βlo βhi ε Cθ : ℝ) (hs : 1 < s)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (hε : 0 < ε) (hCθ : 1 ≤ Cθ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Parameters), p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (N n : ℕ+), 2 ≤ (N : ℕ) →
      ∀ (hn : (n : ℕ) ≤ (N : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ (ι : Bool) (a b : Fin (N : ℕ)) (q : ℝ), 1 ≤ q →
        eLpNorm (GoodBlocks.particleHessian p N a b) (ENNReal.ofReal q)
          (tiltedParticleMeasure p N n hn θ ε ι) ≤ ENNReal.ofReal
            (C * q ^ ((s + 2) / s) *
              (1 + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-s)) := by
  obtain ⟨D, hD, hcoeff⟩ := activeTilt_interval_moments s βlo βhi ε Cθ hs hlo hle hε hCθ
  refine ⟨D * (1 + 1 / s), by positivity, ?_⟩
  intro p hps hpl hph N n hN hn θ hcurv ι a b q hq
  have hh := interval_matrix_eLpNorm_le
    (tiltedParticleMeasure p N n hn θ ε ι) N (by linarith : 0 < s) hq
    (show 0 ≤ D * q ^ ((s + 2) / s) by positivity)
    (fun i r => GoodBlocks.particleCoefficient p N i.val (r.val + 1) (by omega)
      (by have := r.isLt; omega))
    (fun i r => by
      have hb := hcoeff p hps hpl hph N n hN hn θ hcurv ι (i,r) q hq
      simp_rw [intervalWeight_gapVector] at hb
      exact hb) a b
  calc
    _ ≤ ENNReal.ofReal ((D * q ^ ((s + 2) / s)) * (1 + 1 / s) *
        (1 + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-s)) := hh
    _ = _ := by congr 1; ring


/-- Internal geometry for Subsection 4.5: a boundary prefix of
proper length `k` has a unique start at every fixed interval length. -/
theorem internal_prefix_endpoint (N : ℕ+) {n r k : ℕ} (hn : 1 ≤ n)
    (hhalf : 2 * n ≤ (N : ℕ)) (hr : 1 ≤ r) (hrhalf : 2 * r ≤ (N : ℕ))
    (hk : 1 ≤ k) (hkn : k < n) (a : Fin (N : ℕ))
    (hb : ¬ ∀ j ∈ cyclicIndexInterval N a r, j.val < n)
    (ht : IntervalBoundary.trace N n (by omega) a r = IntervalBoundary.initialSegment n k) :
    a.val + r = (N : ℕ) + k ∧ k < r := by
  have ha := a.isLt
  have hm (i : Fin n) : i ∈ IntervalBoundary.trace N n (by omega) a r ↔
      (if a.val ≤ i.val then i.val - a.val else i.val + (N : ℕ) - a.val) < r := by
    rw [IntervalBoundary.mem_trace N n (by omega) a r (by omega)]
    have hi := i.isLt
    split_ifs with hai
    · rw [show i.val + (N : ℕ) - a.val = (i.val - a.val) + (N : ℕ) by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · rw [Nat.mod_eq_of_lt (by omega)]
  have h0 : (⟨0, by omega⟩ : Fin n) ∈ IntervalBoundary.trace N n (by omega) a r := by
    rw [ht]; simp [IntervalBoundary.initialSegment]; omega
  have hknot : (⟨k, hkn⟩ : Fin n) ∉ IntervalBoundary.trace N n (by omega) a r := by
    rw [ht]; simp [IntervalBoundary.initialSegment]
  have hkm : (⟨k - 1, by omega⟩ : Fin n) ∈ IntervalBoundary.trace N n (by omega) a r := by
    rw [ht]; simp [IntervalBoundary.initialSegment]; omega
  rw [hm] at h0 hknot hkm
  by_cases ha0 : a.val = 0
  · have hrk : r = k := by simp only [ha0, Nat.zero_le, ↓reduceIte, Nat.sub_zero] at *; omega
    exfalso
    apply hb
    intro j hj
    have hj' : (j - a).val < r :=
      (mem_cyclicIndexInterval_iff N a j (by omega)).mp hj
    have haz : a = 0 := Fin.ext ha0
    rw [haz, sub_zero] at hj'
    omega
  · have hwrap : (N : ℕ) < a.val + r := by
      simp only [show ¬ a.val ≤ 0 by omega, ↓reduceIte, zero_add] at h0
      omega
    have han : n ≤ a.val := by omega
    simp only [show ¬ a.val ≤ k by omega, show ¬ a.val ≤ k - 1 by omega,
      ↓reduceIte] at hknot hkm
    omega

/-- Internal geometry for Subsection 4.5: a proper suffix has its
start at its first active label, and must extend beyond the block. -/
theorem internal_suffix_start (N : ℕ+) {n r k : ℕ} (hn : 1 ≤ n)
    (hhalf : 2 * n ≤ (N : ℕ)) (hr : 1 ≤ r) (hrhalf : 2 * r ≤ (N : ℕ))
    (hk : 1 ≤ k) (hkn : k < n) (a : Fin (N : ℕ))
    (hb : ¬ ∀ j ∈ cyclicIndexInterval N a r, j.val < n)
    (ht : IntervalBoundary.trace N n (by omega) a r = IntervalBoundary.terminalSegment n k) :
    a.val = k ∧ n - k < r := by
  have ha := a.isLt
  have hm (i : Fin n) : i ∈ IntervalBoundary.trace N n (by omega) a r ↔
      (if a.val ≤ i.val then i.val - a.val else i.val + (N : ℕ) - a.val) < r := by
    rw [IntervalBoundary.mem_trace N n (by omega) a r (by omega)]
    have hi := i.isLt
    split_ifs with hai
    · rw [show i.val + (N : ℕ) - a.val = (i.val - a.val) + (N : ℕ) by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · rw [Nat.mod_eq_of_lt (by omega)]
  have h0 : (⟨0, by omega⟩ : Fin n) ∉ IntervalBoundary.trace N n (by omega) a r := by
    rw [ht]; simp [IntervalBoundary.terminalSegment]; omega
  have hkm : (⟨k - 1, by omega⟩ : Fin n) ∉ IntervalBoundary.trace N n (by omega) a r := by
    rw [ht]; simp [IntervalBoundary.terminalSegment]; omega
  have hk' : (⟨k, hkn⟩ : Fin n) ∈ IntervalBoundary.trace N n (by omega) a r := by
    rw [ht]; simp [IntervalBoundary.terminalSegment]
  rw [hm] at h0 hkm hk'
  change ¬ (if a.val ≤ 0 then 0 - a.val else 0 + (N : ℕ) - a.val) < r at h0
  change ¬ (if a.val ≤ k - 1 then k - 1 - a.val else k - 1 + (N : ℕ) - a.val) < r at hkm
  change (if a.val ≤ k then k - a.val else k + (N : ℕ) - a.val) < r at hk'
  have hnowrap : a.val + r ≤ (N : ℕ) := by split_ifs at h0 <;> omega
  have hak : a.val = k := by split_ifs at hkm hk' <;> omega
  refine ⟨hak, ?_⟩
  by_contra hlen
  apply hb
  intro j hj
  have hj' : (j - a).val < r :=
    (mem_cyclicIndexInterval_iff N a j (by omega)).mp hj
  rw [Fin.val_sub] at hj'
  have hjN := j.isLt
  by_cases haj : a.val ≤ j.val
  · rw [show (N : ℕ) - a.val + j.val = (j.val - a.val) + (N : ℕ) by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at hj'
    omega
  · rw [Nat.mod_eq_of_lt (by omega)] at hj'
    omega


/-- Internal norm estimate for one proper boundary shape. The two geometry
premises are discharged by the endpoint lemmas for the physical coefficients. -/
theorem internal_boundary_group_norm_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : ℕ+) (n : ℕ) (hn : n ≤ (N : ℕ))
    {s q B : ℝ} (hs : 0 < s) (hq : 1 ≤ q) (hB : 0 ≤ B)
    (A : (Fin (N : ℕ) × Fin ((N : ℕ) / 2)) → Ω → ℝ)
    (hA : ∀ t, eLpNorm (A t) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (B * (t.2.val + 1 : ℝ) ^ (-s - 2)))
    (T : Finset (Fin n)) (R : ℕ) (hR : 1 ≤ R)
    (hsize : ∀ (a : Fin (N : ℕ)) (r : Fin ((N : ℕ) / 2)),
      ¬ IntervalBoundary.IsInternal N n (a,r) →
      IntervalBoundary.trace N n hn a (r.val + 1) = T → R ≤ r.val + 1)
    (hunique : ∀ (r : Fin ((N : ℕ) / 2)) (a b : Fin (N : ℕ)),
      ¬ IntervalBoundary.IsInternal N n (a,r) →
      IntervalBoundary.trace N n hn a (r.val + 1) = T →
      ¬ IntervalBoundary.IsInternal N n (b,r) →
      IntervalBoundary.trace N n hn b (r.val + 1) = T → a = b) :
    eLpNorm (fun x => ∑ t, if IntervalBoundary.IsInternal N n t then 0 else
      if IntervalBoundary.trace N n hn t.1 (t.2.val + 1) = T then A t x else 0)
      (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal (B * (1 + 1 / (s + 1)) * (R : ℝ) ^ (-s - 1)) := by
  classical
  let P := fun (r : Fin ((N : ℕ) / 2)) (a : Fin (N : ℕ)) =>
    ¬ IntervalBoundary.IsInternal N n (a,r) ∧
      IntervalBoundary.trace N n hn a (r.val + 1) = T
  have he : (fun x => ∑ t, if IntervalBoundary.IsInternal N n t then 0 else
      if IntervalBoundary.trace N n hn t.1 (t.2.val + 1) = T then A t x else 0) =
      fun x => ∑ r : Fin ((N : ℕ) / 2), ∑ a : Fin (N : ℕ),
        if P r a then A (a,r) x else 0 := by
    funext x
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro a _
    dsimp only [P]
    split_ifs <;> simp_all
  have hqE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hq
  have hi (r : Fin ((N : ℕ) / 2)) :
      eLpNorm (fun x => ∑ a : Fin (N : ℕ), if P r a then A (a,r) x else 0)
        (ENNReal.ofReal q) μ ≤
          ENNReal.ofReal (B * (if (R : ℝ) ≤ 1 + (r.val : ℝ)
            then (1 + (r.val : ℝ)) ^ (-(s + 2)) else 0)) := by
    by_cases hp : ∃ a, P r a
    · obtain ⟨a, ha⟩ := hp
      have hsum : (fun x => ∑ b : Fin (N : ℕ), if P r b then A (b,r) x else 0) = A (a,r) := by
        funext x
        rw [Finset.sum_eq_single a]
        · exact ite_eq_left ha
        · intro b _ hba
          exact ite_eq_right (fun hb => hba (hunique r b a hb.1 hb.2 ha.1 ha.2))
        · simp
      rw [hsum, ite_eq_left (by
        have hnat := hsize a r ha.1 ha.2
        have hcast : (R : ℝ) ≤ (r.val : ℝ) + 1 := by exact_mod_cast hnat
        linarith)]
      simpa only [show -(s + 2) = -s - 2 by ring, add_comm] using hA (a,r)
    · have hz : ∀ a, ¬ P r a := not_exists.mp hp
      simp only [hz, ↓reduceIte, Finset.sum_const_zero]
      simp
  let g := fun k : ℕ => if (R : ℝ) ≤ 1 + (k : ℝ) then (1 + (k : ℝ)) ^ (-(s + 2)) else 0
  have hg0 : ∀ k, 0 ≤ g k := by intro k; dsimp [g]; split_ifs <;> positivity
  have hgs : Summable g := Summable.of_nonneg_of_le hg0
    (fun k => by dsimp [g]; split_ifs <;> first | exact le_rfl | positivity)
    (summable_one_add_rpow_neg (by linarith : 1 < s + 2))
  rw [he]
  calc
    _ ≤ ∑ r : Fin ((N : ℕ) / 2),
        eLpNorm (fun x => ∑ a : Fin (N : ℕ), if P r a then A (a,r) x else 0)
          (ENNReal.ofReal q) μ := by
      simpa only [Finset.sum_fn] using eLpNorm_sum_le (μ := μ) (s := Finset.univ) hqE
        (f := fun r x => ∑ a : Fin (N : ℕ), if P r a then A (a,r) x else 0)
    _ ≤ ∑ r : Fin ((N : ℕ) / 2), ENNReal.ofReal (B * g r.val) :=
      Finset.sum_le_sum fun r _ => hi r
    _ = ENNReal.ofReal (B * ∑ r ∈ Finset.range ((N : ℕ) / 2), g r) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun r _ => mul_nonneg hB (hg0 r.val)),
        ← Finset.mul_sum, Finset.sum_range]
    _ ≤ ENNReal.ofReal (B * ∑' r, g r) := ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (hgs.sum_le_tsum _ (fun r _ => hg0 r)) hB)
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have ht := tsum_tail_indicator_le (by linarith : 1 < s + 2)
        (show 1 ≤ (R : ℝ) by exact_mod_cast hR)
      have he₁ : (s + 2) - 1 = s + 1 := by ring
      have he₂ : 1 - (s + 2) = -s - 1 := by ring
      rw [he₁, he₂] at ht
      simpa only [g, mul_assoc] using mul_le_mul_of_nonneg_left ht hB


/-- See Subsection 4.5 of the paper, sharp proper-prefix and proper-suffix moments
under either active tilt. The suffix starts at the zero-based label `k`,
so its distance to the source is `n-k`. Empty families at `n=1` are included. -/
theorem activeTilt_boundary_moments (s βlo βhi h Cθ : ℝ) (hs : 1 < s)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (hh : 0 < h) (hCθ : 1 ≤ Cθ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (n : ℕ+) (m : ℕ)
      (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)),
      2 * (n : ℕ) ≤ (n : ℕ) + m + 1 → ∀ (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ (ι : Bool) (q : ℝ), 1 ≤ q → ∀ k : ℕ, 1 ≤ k → k < (n : ℕ) →
        let μ := (activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ h ι).comap
          ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
            EuclideanSpace ℝ (Fin (n : ℕ)))
        (eLpNorm (fun x => IntervalBoundary.prefixCoefficient ((n : ℕ) + m).succPNat n hn
          (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x) k)
          (ENNReal.ofReal q) μ ≤
            ENNReal.ofReal (C * q ^ ((s + 2) / s) * (k : ℝ) ^ (-s - 1))) ∧
        (eLpNorm (fun x => IntervalBoundary.suffixCoefficient ((n : ℕ) + m).succPNat n hn
          (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x) k)
          (ENNReal.ofReal q) μ ≤
            ENNReal.ofReal (C * q ^ ((s + 2) / s) * ((n : ℕ) - k : ℕ) ^ (-s - 1))) := by
  obtain ⟨C, hC, hb⟩ := activeTilt_conditional_interval_moments s βlo βhi h Cθ
    hs hlo hle hh hCθ
  refine ⟨C * (1 + 1 / (s + 1)), by positivity, ?_⟩
  intro p hp hpl hph n m hn hhalf θ hcurv ι q hq k hk hkn μ
  let A := fun t x => conditionalIntervalWeight p n m n.pos (Equiv.refl _) x t
  have hcoeff (t) : eLpNorm (A t) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal ((C * q ^ ((s + 2) / s)) * (t.2.val + 1 : ℝ) ^ (-s - 2)) :=
    hb p hp hpl hph n m hn θ hcurv ι t q hq
  have hpref (a : Fin ((n : ℕ) + m + 1)) (r : Fin (((n : ℕ) + m + 1) / 2))
      (ha : ¬ IntervalBoundary.IsInternal ((n : ℕ) + m).succPNat n (a,r))
      (ht : IntervalBoundary.trace ((n : ℕ) + m).succPNat n hn a (r.val + 1) =
        IntervalBoundary.initialSegment n k) : a.val + (r.val + 1) = (n : ℕ) + m + 1 + k ∧
          k < r.val + 1 := by
    have he := internal_prefix_endpoint ((n : ℕ) + m).succPNat n.pos hhalf
      (by omega : 1 ≤ r.val + 1)
      (by change 2 * (r.val + 1) ≤ (n : ℕ) + m + 1; have := r.isLt; omega) hk hkn a
    exact he (by simpa only [IntervalBoundary.IsInternal] using ha) ht
  have hsuff (a : Fin ((n : ℕ) + m + 1)) (r : Fin (((n : ℕ) + m + 1) / 2))
      (ha : ¬ IntervalBoundary.IsInternal ((n : ℕ) + m).succPNat n (a,r))
      (ht : IntervalBoundary.trace ((n : ℕ) + m).succPNat n hn a (r.val + 1) =
        IntervalBoundary.terminalSegment n k) : a.val = k ∧ (n : ℕ) - k < r.val + 1 := by
    have he := internal_suffix_start ((n : ℕ) + m).succPNat n.pos hhalf
      (by omega : 1 ≤ r.val + 1)
      (by change 2 * (r.val + 1) ≤ (n : ℕ) + m + 1; have := r.isLt; omega) hk hkn a
    exact he (by simpa only [IntervalBoundary.IsInternal] using ha) ht
  constructor
  · have hg := internal_boundary_group_norm_le μ ((n : ℕ) + m).succPNat n hn
      (by linarith : 0 < s) hq (by positivity : 0 ≤ C * q ^ ((s + 2) / s)) A hcoeff
      (IntervalBoundary.initialSegment n k) k hk
      (fun a r ha ht => (hpref a r ha ht).2.le)
      (fun r a b ha hta hb htb => Fin.ext (by
        have he₁ := (hpref a r ha hta).1
        have he₂ := (hpref b r hb htb).1
        omega))
    refine hg.trans_eq ?_
    congr 1
    ring
  · have hg := internal_boundary_group_norm_le μ ((n : ℕ) + m).succPNat n hn
      (by linarith : 0 < s) hq (by positivity : 0 ≤ C * q ^ ((s + 2) / s)) A hcoeff
      (IntervalBoundary.terminalSegment n k) ((n : ℕ) - k) (by omega)
      (fun a r ha ht => (hsuff a r ha ht).2.le)
      (fun r a b ha hta hb htb => Fin.ext
        ((hsuff a r ha hta).1.trans (hsuff b r hb htb).1.symm))
    refine hg.trans_eq ?_
    congr 1
    ring


/-- See Subsection 4.5 of the paper, sharp full-block boundary coefficient moments
for both active tilts. The singleton block is covered by the diagonal entry. -/
theorem activeTilt_full_boundary_moments (s βlo βhi h Cθ : ℝ) (hs : 1 < s)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (hh : 0 < h) (hCθ : 1 ≤ Cθ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (n : ℕ+) (m : ℕ)
      (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)),
      2 * (n : ℕ) ≤ (n : ℕ) + m + 1 → ∀ (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ (ι : Bool) (q : ℝ), 1 ≤ q →
        eLpNorm (fun x => IntervalBoundary.fullCoefficient ((n : ℕ) + m).succPNat n hn
          (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x))
          (ENNReal.ofReal q)
          ((activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ h ι).comap
            ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
              EuclideanSpace ℝ (Fin (n : ℕ)))) ≤
            ENNReal.ofReal (C * q ^ ((s + 2) / s) * (n : ℝ) ^ (-s)) := by
  classical
  obtain ⟨C, hC, hb⟩ := activeTilt_conditional_P_moments s βlo βhi h Cθ
    hs hlo hle hh hCθ
  refine ⟨C, hC, ?_⟩
  intro p hp hpl hph n m hn hhalf θ hcurv ι q hq
  let i : Fin (n : ℕ) := ⟨0, n.pos⟩
  let j : Fin (n : ℕ) := ⟨(n : ℕ) - 1, by have := n.pos; omega⟩
  have he : Riesz1.cyclicIndexDistance ((n : ℕ) + m).succPNat
      (Fin.castLE hn i) (Fin.castLE hn j) = (n : ℕ) - 1 := by
    change min (Nat.dist 0 ((n : ℕ) - 1))
      ((n : ℕ) + m + 1 - Nat.dist 0 ((n : ℕ) - 1)) = (n : ℕ) - 1
    simp only [Nat.dist, Nat.zero_sub, Nat.sub_zero, zero_add]
    omega
  have hnorm := hb p hp hpl hph n m hn θ hcurv ι i j q hq
  rw [he] at hnorm
  have hcast : 1 + (((n : ℕ) - 1 : ℕ) : ℝ) = (n : ℝ) := by
    have := n.pos
    rw [Nat.cast_sub (by omega : 1 ≤ (n : ℕ)), Nat.cast_one]
    ring
  rw [hcast] at hnorm
  refine (eLpNorm_mono_real
    (measurable_physical_boundary_coefficients p n m n.pos hn).2.2.aestronglyMeasurable
    (fun x => ?_)).trans hnorm
  rw [Real.norm_eq_abs, abs_of_nonneg
    (physical_boundary_coefficients_nonneg p n m n.pos hn x).2.2]
  unfold IntervalBoundary.fullCoefficient IntervalBoundary.intervalMatrix
  apply Finset.sum_le_sum
  intro t _
  have hA := conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x t
  by_cases ht : IntervalBoundary.IsInternal ((n : ℕ) + m).succPNat n t
  · simp only [ht, ↓reduceIte]
    exact mul_nonneg hA (by unfold IntervalBoundary.rankOne; split_ifs <;> positivity)
  · simp only [ht, ↓reduceIte]
    by_cases htrace : IntervalBoundary.trace ((n : ℕ) + m).succPNat n hn t.1
        (t.2.val + 1) = Finset.univ
    · simp only [htrace, ↓reduceIte, IntervalBoundary.rankOne, Finset.mem_univ,
        and_self, mul_one]
      exact le_rfl
    · simp only [htrace, ↓reduceIte]
      exact mul_nonneg hA (by unfold IntervalBoundary.rankOne; split_ifs <;> positivity)

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 4.5 of the paper, full ambient conditional mean Hessian profile,
including both exterior indices. This supplies the exterior contractions. -/
theorem activeTilt_conditional_ambient_moments (s βlo βhi h Cθ : ℝ) (hs : 1 < s)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (hh : 0 < h) (hCθ : 1 ≤ Cθ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (n : ℕ+) (m : ℕ)
      (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ (ι : Bool) (i j : Fin ((n : ℕ) + m + 1)) (q : ℝ), 1 ≤ q →
        eLpNorm (fun x => IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat ((n : ℕ) + m + 1) le_rfl
          (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x) i j)
          (ENNReal.ofReal q)
          ((activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ h ι).comap
            ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
              EuclideanSpace ℝ (Fin (n : ℕ)))) ≤
            ENNReal.ofReal (C * q ^ ((s + 2) / s) *
              (1 + (Riesz1.cyclicIndexDistance ((n : ℕ) + m).succPNat
                (i) (j) : ℝ)) ^ (-s)) := by
  obtain ⟨C, hC, hb⟩ := activeTilt_conditional_interval_moments s βlo βhi h Cθ hs hlo hle hh hCθ
  have hs0 : 0 < s := by linarith
  refine ⟨C * (1 + 1 / s), mul_pos hC (by positivity), ?_⟩
  intro p hp hpl hph n m hn θ hcurv ι i j q hq
  let μ := (activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ h ι).comap
    ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
  let A := fun a r x => conditionalIntervalWeight p n m n.pos (Equiv.refl _) x (a,r)
  have hcoeff (a : Fin ((n : ℕ) + m + 1)) (r : Fin (((n : ℕ) + m + 1) / 2)) :
      eLpNorm (A a r) (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal ((C * q ^ ((s + 2) / s)) * (r.val + 1 : ℝ) ^ (-s - 2)) :=
    hb p hp hpl hph n m hn θ hcurv ι (a,r) q hq
  have hnorm := interval_matrix_eLpNorm_le μ ((n : ℕ) + m).succPNat
    (by linarith : 0 < s) hq (by positivity : 0 ≤ C * q ^ ((s + 2) / s))
    A hcoeff (i) (j)
  have he : (fun x => IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat ((n : ℕ) + m + 1) le_rfl
      (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x) i j) =
      fun x => ∑ r : Fin (((n : ℕ) + m + 1) / 2), ∑ a : Fin ((n : ℕ) + m + 1),
        if i ∈ cyclicIndexInterval ((n : ℕ) + m).succPNat a (r.val + 1) ∧
          j ∈ cyclicIndexInterval ((n : ℕ) + m).succPNat a (r.val + 1)
        then A a r x else 0 := by
    classical
    funext x
    rw [IntervalBoundary.intervalMatrix, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro a _
    dsimp only [IntervalBoundary.rankOne, IntervalBoundary.trace, A]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hii : Fin.castLE (le_rfl : (n : ℕ) + m + 1 ≤ (n : ℕ) + m + 1) i = i := Fin.ext rfl
    have hjj : Fin.castLE (le_rfl : (n : ℕ) + m + 1 ≤ (n : ℕ) + m + 1) j = j := Fin.ext rfl
    rw [hii, hjj]
    by_cases hi : i ∈ cyclicIndexInterval ((n : ℕ) + m).succPNat a (r.val + 1) <;>
      by_cases hj : j ∈ cyclicIndexInterval ((n : ℕ) + m).succPNat a (r.val + 1) <;>
      simp only [hi, hj, and_self, and_false, false_and, ↓reduceIte, mul_one, mul_zero]
  rw [he]
  refine hnorm.trans_eq ?_
  congr 1
  ring

/-- Internal row estimate for Subsection 4.5: summable ambient
entry profiles control every selected exterior row, uniformly in the cycle. -/
theorem internal_selected_row_norm_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : ℕ+) {s q B : ℝ} (hs : 1 < s) (hq : 1 ≤ q) (hB : 0 ≤ B)
    (H : Fin (N : ℕ) → Fin (N : ℕ) → Ω → ℝ)
    (hH : ∀ a b, eLpNorm (H a b) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (B * (1 + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-s)))
    (S : Finset (Fin (N : ℕ))) (a : Fin (N : ℕ)) :
    eLpNorm (fun x => ∑ b ∈ S, H a b x) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (B * (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s))) := by
  have hqE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hq
  calc
    _ ≤ ∑ b ∈ S, eLpNorm (H a b) (ENNReal.ofReal q) μ := by
      simpa only [Finset.sum_fn] using eLpNorm_sum_le (μ := μ) (s := S) hqE (f := H a)
    _ ≤ ∑ b ∈ S, ENNReal.ofReal (B *
        (1 + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-s)) :=
      Finset.sum_le_sum fun b _ => hH a b
    _ ≤ ∑ b : Fin (N : ℕ), ENNReal.ofReal (B *
        (1 + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-s)) :=
      Finset.sum_le_univ_sum_of_nonneg (fun _ => bot_le)
    _ = ENNReal.ofReal (B * ∑ b : Fin (N : ℕ),
        (1 + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-s)) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity), Finset.mul_sum]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (sum_le_two_mul_tsum_cyclicIndexDistance N a (fun _ => by positivity)
        (summable_one_add_rpow_neg hs)) hB)

/-- Internal exterior contractions for Subsection 4.5. These are
exact finite contractions with the uniform exterior vector. The hypothesis
on `H` is supplied by the physical coefficient theorem. -/
theorem internal_exterior_contraction_norms {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : ℕ+) {n : ℕ} (hhalf : 2 * n ≤ (N : ℕ))
    {s q B : ℝ} (hs : 1 < s) (hq : 1 ≤ q) (hB : 0 ≤ B)
    (H : Fin (N : ℕ) → Fin (N : ℕ) → Ω → ℝ)
    (hH : ∀ a b, eLpNorm (H a b) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (B * (1 + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-s)))
    (i : Fin (N : ℕ)) :
    let S := Finset.univ.filter (fun a : Fin (N : ℕ) => n ≤ a.val)
    let M : ℝ := ((N : ℕ) - n : ℕ)
    eLpNorm (fun x => M⁻¹ * ∑ a ∈ S, H i a x) (ENNReal.ofReal q) μ +
      eLpNorm (fun x => M⁻¹ ^ 2 * ∑ a ∈ S, ∑ b ∈ S, H a b x) (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal (B * (12 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s)) / (N : ℝ)) := by
  classical
  intro S M
  let K := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s)
  have hK : 0 ≤ K := mul_nonneg (by norm_num) (tsum_nonneg fun _ => by positivity)
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hMn : 0 < (N : ℕ) - n := by have := N.pos; omega
  have hM : 0 < M := by dsimp only [M]; exact_mod_cast hMn
  have hNM : (N : ℝ) ≤ 2 * M := by
    dsimp [M]
    exact_mod_cast (show (N : ℕ) ≤ 2 * ((N : ℕ) - n) by omega)
  have hscale : M⁻¹ ≤ 2 / (N : ℝ) := by
    rw [inv_eq_one_div, div_le_div_iff₀ hM hN]
    linarith
  have hscale₂ : M⁻¹ ^ 2 * (N : ℝ) ≤ 4 / (N : ℝ) := by
    calc
      _ ≤ (2 / (N : ℝ)) ^ 2 * (N : ℝ) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (inv_nonneg.mpr hM.le) hscale 2) hN.le
      _ = _ := by field_simp; ring
  have hrow (a) : eLpNorm (fun x => ∑ b ∈ S, H a b x) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (B * K) := internal_selected_row_norm_le μ N hs hq hB H hH S a
  have hqE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hq
  have hsum : eLpNorm (fun x => ∑ a ∈ S, ∑ b ∈ S, H a b x) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal ((N : ℝ) * (B * K)) := by
    calc
      _ ≤ ∑ a ∈ S, eLpNorm (fun x => ∑ b ∈ S, H a b x) (ENNReal.ofReal q) μ := by
        simpa only [Finset.sum_fn] using eLpNorm_sum_le (μ := μ) (s := S) hqE
          (f := fun a x => ∑ b ∈ S, H a b x)
      _ ≤ ∑ _a ∈ S, ENNReal.ofReal (B * K) := Finset.sum_le_sum fun a _ => hrow a
      _ ≤ ∑ _a : Fin (N : ℕ), ENNReal.ofReal (B * K) :=
        Finset.sum_le_univ_sum_of_nonneg (fun _ => bot_le)
      _ = _ := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => mul_nonneg hB hK)]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h₁ : eLpNorm (fun x => M⁻¹ * ∑ a ∈ S, H i a x) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (2 * (B * K) / (N : ℝ)) := by
    change eLpNorm (M⁻¹ • (fun x => ∑ a ∈ S, H i a x)) _ _ ≤ _
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_pos (inv_pos.mpr hM)]
    refine (mul_le_mul' le_rfl (hrow i)).trans ?_
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hM.le)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (2 / (N : ℝ)) * (B * K) := mul_le_mul_of_nonneg_right hscale (mul_nonneg hB hK)
      _ = _ := by ring
  have h₂ : eLpNorm (fun x => M⁻¹ ^ 2 * ∑ a ∈ S, ∑ b ∈ S, H a b x)
      (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (4 * (B * K) / (N : ℝ)) := by
    change eLpNorm ((M⁻¹ ^ 2) • (fun x => ∑ a ∈ S, ∑ b ∈ S, H a b x)) _ _ ≤ _
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg _)]
    refine (mul_le_mul' le_rfl hsum).trans ?_
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ = (M⁻¹ ^ 2 * (N : ℝ)) * (B * K) := by ring
      _ ≤ (4 / (N : ℝ)) * (B * K) := mul_le_mul_of_nonneg_right hscale₂ (mul_nonneg hB hK)
      _ = _ := by ring
  refine (add_le_add h₁ h₂).trans_eq ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  dsimp [K]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 4.5 of the paper, uniform exterior-vector contractions of the
actual conditional ambient interval matrix. The two terms are `b_i` and `c`
from Subsection 4.4, in their finite interval representation. -/
theorem activeTilt_exterior_contraction_moments (s βlo βhi h Cθ : ℝ) (hs : 1 < s)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (hh : 0 < h) (hCθ : 1 ≤ Cθ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (n : ℕ+) (m : ℕ)
      (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)),
      2 * (n : ℕ) ≤ (n : ℕ) + m + 1 → ∀ (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ (ι : Bool) (q : ℝ), 1 ≤ q → ∀ i : Fin (n : ℕ),
        let μ := (activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ h ι).comap
          ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
            EuclideanSpace ℝ (Fin (n : ℕ)))
        let H := fun x => IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat
          ((n : ℕ) + m + 1) le_rfl (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
        let S := Finset.univ.filter (fun a : Fin ((n : ℕ) + m + 1) => (n : ℕ) ≤ a.val)
        let M : ℝ := m + 1
        eLpNorm (fun x => M⁻¹ * ∑ a ∈ S, H x (Fin.castLE hn i) a) (ENNReal.ofReal q) μ +
          eLpNorm (fun x => M⁻¹ ^ 2 * ∑ a ∈ S, ∑ b ∈ S, H x a b) (ENNReal.ofReal q) μ ≤
            ENNReal.ofReal (C * q ^ ((s + 2) / s) / ((n : ℕ) + m + 1 : ℕ)) := by
  obtain ⟨C, hC, hb⟩ := activeTilt_conditional_ambient_moments s βlo βhi h Cθ
    hs hlo hle hh hCθ
  let T := ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s)
  have hT : 0 ≤ T := tsum_nonneg fun _ => by positivity
  refine ⟨C * (1 + 12 * T), by positivity, ?_⟩
  intro p hp hpl hph n m hn hhalf θ hcurv ι q hq i μ H S M
  have hH (a b : Fin ((n : ℕ) + m + 1)) :
      eLpNorm (fun x => H x a b) (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal ((C * q ^ ((s + 2) / s)) *
          (1 + (Riesz1.cyclicIndexDistance ((n : ℕ) + m).succPNat a b : ℝ)) ^ (-s)) :=
    hb p hp hpl hph n m hn θ hcurv ι a b q hq
  have he := internal_exterior_contraction_norms μ ((n : ℕ) + m).succPNat hhalf hs hq
    (by positivity : 0 ≤ C * q ^ ((s + 2) / s)) (fun a b x => H x a b) hH (Fin.castLE hn i)
  dsimp only at he
  have hM : ((((n : ℕ) + m).succPNat : ℕ) - (n : ℕ) : ℕ) = m + 1 := by
    simp only [Nat.succPNat_coe]; omega
  rw [hM] at he
  simp only [Nat.cast_add, Nat.cast_one] at he
  dsimp only [M, S]
  refine he.trans (ENNReal.ofReal_le_ofReal ?_)
  have hN : (0 : ℝ) < ((n : ℕ) + m + 1 : ℕ) := by positivity
  apply div_le_div_of_nonneg_right _ hN.le
  have hq0 : 0 ≤ q ^ ((s + 2) / s) := Real.rpow_nonneg (by linarith) _
  dsimp only [T] at *
  nlinarith [mul_nonneg hC.le hq0]


/-- Internal Hölder step for Subsection 4.5, with real norm exponents. -/
theorem internal_weighted_square_norm_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (F G : Ω → ℝ) {q : ℝ} (hq : 1 ≤ q) :
    eLpNorm (fun x => F x * (G x) ^ 2) (ENNReal.ofReal q) μ ≤
      eLpNorm F (ENNReal.ofReal (2 * q)) μ * eLpNorm G (ENNReal.ofReal (4 * q)) μ ^ 2 := by
  have hq0 : 0 < q := by linarith
  have hT (t : ℝ) (ht : 0 < t) : Real.HolderTriple (2 * t) (2 * t) t :=
    ⟨by field_simp; ring, by positivity, by positivity⟩
  have := (hT q hq0).ennrealOfReal
  have := (hT (2 * q) (by positivity)).ennrealOfReal
  have hsq : eLpNorm (G • G) (ENNReal.ofReal (2 * q)) μ ≤
      eLpNorm G (ENNReal.ofReal (4 * q)) μ * eLpNorm G (ENNReal.ofReal (4 * q)) μ := by
    have he := eLpNorm_smul_le_mul_eLpNorm_of_pos (μ := μ) (φ := G) (f := G)
      (p := ENNReal.ofReal (2 * (2 * q))) (q := ENNReal.ofReal (2 * (2 * q)))
      (r := ENNReal.ofReal (2 * q)) (ENNReal.ofReal_pos.mpr (by positivity))
    simpa only [show 2 * (2 * q) = 4 * q by ring] using he
  have he : (fun x => F x * (G x) ^ 2) = F • (G • G) := by
    funext x
    change F x * (G x) ^ 2 = F x * (G x * G x)
    rw [pow_two]
  rw [he]
  exact (eLpNorm_smul_le_mul_eLpNorm_of_pos (μ := μ) (φ := F) (f := G • G)
    (p := ENNReal.ofReal (2 * q)) (q := ENNReal.ofReal (2 * q))
    (r := ENNReal.ofReal q) (ENNReal.ofReal_pos.mpr hq0)).trans
      ((mul_le_mul' le_rfl hsq).trans_eq (by simp only [pow_two]))

/-- See Subsection 4.5 of the paper, the unconditional weighted Hessian-square
input to the exterior gradient estimate. The moment degree depends only on `s`. Both tilts and all ambient labels are included. -/
theorem activeTilt_weighted_hessian_square_moments (s βlo βhi h Cθ : ℝ) (hs : 1 < s)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (hh : 0 < h) (hCθ : 1 ≤ Cθ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (N n : ℕ+), 2 ≤ (N : ℕ) →
      ∀ (hn : (n : ℕ) ≤ (N : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ (ι : Bool) (i a : Fin (N : ℕ)) (q : ℝ), 1 ≤ q →
        eLpNorm (fun X => gap X a.val ^ (s + 2) * (GoodBlocks.particleHessian p N i a X) ^ 2)
          (ENNReal.ofReal q) (tiltedParticleMeasure p N n hn θ h ι) ≤
            ENNReal.ofReal (C * q ^ ((s + 2) + 2 * ((s + 2) / s)) *
              (1 + (Riesz1.cyclicIndexDistance N i a : ℝ)) ^ (-2 * s)) := by
  obtain ⟨A, hA, hgap⟩ := SingleGapTails.single_gap_moments s βlo βhi
    (by linarith) (ne_of_gt hs) hlo hle (s + 2) (by linarith)
  obtain ⟨B, hB, hHess⟩ := activeTilt_hessian_moments s βlo βhi h Cθ hs hlo hle hh hCθ
  obtain ⟨z, hz, hzhalf, hZ⟩ := activeTilt_normalizer_uniform_lower s βlo βhi h Cθ hs hlo hle hh hCθ
  let r := s + 2
  let d := (s + 2) / s
  let C := (z⁻¹ * (2 * A)) * B ^ 2 * 2 ^ r * 4 ^ (2 * d)
  have hr : 0 < r := by dsimp [r]; linarith
  have hd : 0 < d := by dsimp [d]; positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro p hp hpl hph N n hN hn θ hcurv ι i a q hq
  let μ := tiltedParticleMeasure p N n hn θ h ι
  let F := fun X : Riesz1.Configuration N => gap X a.val ^ r
  let G := GoodBlocks.particleHessian p N i a
  have hq0 : 0 < q := by linarith
  have hq₂ : 1 ≤ 2 * q := by linarith
  have hq₄ : 1 ≤ 4 * q := by linarith
  have hgap₀ : eLpNorm F (ENNReal.ofReal (2 * q)) (gibbsMeasure p N) ≤
      ENNReal.ofReal ((2 * A) * (2 * q) ^ r) := by
    have he := hgap p hp hpl hph N hN a.val (2 * q) hq₂
    have hmax : max r (r / s) = r := max_eq_left (div_le_self hr.le hs.le)
    have he₂ := he.2
    rw [hmax] at he₂
    exact ((le_add_of_nonneg_right (by positivity)).trans he.1).trans
      (ENNReal.ofReal_le_ofReal he₂)
  have hgap₁ : eLpNorm F (ENNReal.ofReal (2 * q)) μ ≤
      ENNReal.ofReal ((z⁻¹ * (2 * A)) * (2 * q) ^ r) := by
    have he := internal_activeTilt_norm_le hz (by linarith)
      (hZ p hp hpl hph N n hN hn θ hcurv ι) F hq₂
    refine he.trans ((mul_le_mul' le_rfl hgap₀).trans_eq ?_)
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hz.le)]
    congr 1
    ring
  have hH : eLpNorm G (ENNReal.ofReal (4 * q)) μ ≤
      ENNReal.ofReal (B * (4 * q) ^ d *
        (1 + (Riesz1.cyclicIndexDistance N i a : ℝ)) ^ (-s)) :=
    hHess p hp hpl hph N n hN hn θ hcurv ι i a (4 * q) hq₄
  have ht : 0 < 1 + (Riesz1.cyclicIndexDistance N i a : ℝ) := by positivity
  have he := internal_weighted_square_norm_le μ F G hq
  refine he.trans ((mul_le_mul' hgap₁ (pow_le_pow_left' hH 2)).trans_eq ?_)
  rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hq0.le,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hq0.le]
  have heq (x : ℝ) (hx : 0 ≤ x) (t : ℝ) : (x ^ t) ^ 2 = x ^ (2 * t) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hx]
    congr 1
    ring
  simp only [mul_pow, heq 4 (by norm_num), heq q hq0.le, heq _ ht.le]
  have hqpow : q ^ r * q ^ (2 * d) = q ^ (r + 2 * d) := (Real.rpow_add hq0 r (2 * d)).symm
  dsimp only [C, r, d] at *
  rw [show 2 * -s = -2 * s by ring]
  linear_combination (z⁻¹ * (2 * A) * B ^ 2 * 2 ^ (s + 2) * 4 ^ (2 * ((s + 2) / s)) *
    (1 + (Riesz1.cyclicIndexDistance N i a : ℝ)) ^ (-2 * s)) * hqpow

/-- Internal shell count in Subsection 4.5: summing a power over
exterior labels gives the boundary-distance profile. -/
theorem internal_exterior_power_tail (N : ℕ+) (n : ℕ) (hn : n ≤ (N : ℕ))
    (i : Fin n) {t : ℝ} (ht : 1 < t) :
    let S := Finset.univ.filter (fun a : Fin (N : ℕ) => n ≤ a.val)
    let δ := min (i.val + 1) (n - i.val)
    (∑ a ∈ S, (1 + (Riesz1.cyclicIndexDistance N (Fin.castLE hn i) a : ℝ)) ^ (-t)) ≤
      2 * (1 + 1 / (t - 1)) * (δ : ℝ) ^ (1 - t) := by
  classical
  intro S δ
  have hδ : 1 ≤ δ := by have := i.isLt; dsimp [δ]; omega
  have hd (a : Fin (N : ℕ)) (ha : a ∈ S) :
      δ ≤ Riesz1.cyclicIndexDistance N (Fin.castLE hn i) a := by
    have hi := i.isLt
    have haN := a.isLt
    have hae : n ≤ a.val := (Finset.mem_filter.mp ha).2
    simp only [Riesz1.cyclicIndexDistance, Nat.dist, Fin.val_castLE]
    dsimp only [δ]
    omega
  let g := fun k : ℕ => if (δ : ℝ) ≤ 1 + (k : ℝ) then (1 + (k : ℝ)) ^ (-t) else 0
  have hg0 : ∀ k, 0 ≤ g k := by intro k; dsimp [g]; split_ifs <;> positivity
  have hgs : Summable g := Summable.of_nonneg_of_le hg0
    (fun k => by dsimp [g]; split_ifs <;> first | exact le_rfl | positivity)
    (summable_one_add_rpow_neg ht)
  calc
    _ = ∑ a ∈ S, g (Riesz1.cyclicIndexDistance N (Fin.castLE hn i) a) := by
      apply Finset.sum_congr rfl
      intro a ha
      dsimp only [g]
      rw [ite_eq_left (by
        have he : (δ : ℝ) ≤ (Riesz1.cyclicIndexDistance N (Fin.castLE hn i) a : ℝ) :=
          by exact_mod_cast hd a ha
        linarith)]
    _ ≤ ∑ a : Fin (N : ℕ), g (Riesz1.cyclicIndexDistance N (Fin.castLE hn i) a) :=
      Finset.sum_le_univ_sum_of_nonneg (fun _ => hg0 _)
    _ ≤ 2 * ∑' k, g k := sum_le_two_mul_tsum_cyclicIndexDistance N _ hg0 hgs
    _ ≤ _ := by
      have he := tsum_tail_indicator_le ht (show 1 ≤ (δ : ℝ) by exact_mod_cast hδ)
      simpa only [g, mul_assoc] using mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 2)

/-- See Subsection 4.5 of the paper, unconditional exterior gradient-energy moments
on particle gaps, before integrating against the conditional kernel.
The distance is `min(i+1,n-i)` for zero-based labels. -/
theorem activeTilt_particle_exterior_energy_moments (s βlo βhi h Cθ : ℝ) (hs : 1 < s)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (hh : 0 < h) (hCθ : 1 ≤ Cθ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (N n : ℕ+), 2 ≤ (N : ℕ) →
      ∀ (hn : (n : ℕ) ≤ (N : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ (ι : Bool) (i : Fin (n : ℕ)) (q : ℝ), 1 ≤ q →
        eLpNorm (fun X => ∑ a : Fin (N : ℕ), if (n : ℕ) ≤ a.val then
          gap X a.val ^ (s + 2) * (GoodBlocks.particleHessian p N (Fin.castLE hn i) a X) ^ 2 else 0)
          (ENNReal.ofReal q) (tiltedParticleMeasure p N n hn θ h ι) ≤
            ENNReal.ofReal (C * q ^ ((s + 2) + 2 * ((s + 2) / s)) *
              (min (i.val + 1) ((n : ℕ) - i.val) : ℕ) ^ (1 - 2 * s)) := by
  classical
  obtain ⟨C, hC, hb⟩ := activeTilt_weighted_hessian_square_moments s βlo βhi h Cθ
    hs hlo hle hh hCθ
  have hden : 0 < 2 * s - 1 := by linarith
  refine ⟨C * (2 * (1 + 1 / (2 * s - 1))), by positivity, ?_⟩
  intro p hp hpl hph N n hN hn θ hcurv ι i q hq
  let S := Finset.univ.filter (fun a : Fin (N : ℕ) => (n : ℕ) ≤ a.val)
  let B := C * q ^ ((s + 2) + 2 * ((s + 2) / s))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hqE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hq
  have he : (fun X => ∑ a : Fin (N : ℕ), if (n : ℕ) ≤ a.val then
      gap X a.val ^ (s + 2) * (GoodBlocks.particleHessian p N (Fin.castLE hn i) a X) ^ 2 else 0) =
      fun X => ∑ a ∈ S,
        gap X a.val ^ (s + 2) * (GoodBlocks.particleHessian p N (Fin.castLE hn i) a X) ^ 2 := by
    funext X
    exact (Finset.sum_filter _ _).symm
  rw [he]
  calc
    _ ≤ ∑ a ∈ S, eLpNorm (fun X =>
        gap X a.val ^ (s + 2) * (GoodBlocks.particleHessian p N (Fin.castLE hn i) a X) ^ 2)
        (ENNReal.ofReal q) (tiltedParticleMeasure p N n hn θ h ι) := by
      simpa only [Finset.sum_fn] using eLpNorm_sum_le (μ := tiltedParticleMeasure p N n hn θ h ι)
        (s := S) hqE (f := fun a X =>
          gap X a.val ^ (s + 2) * (GoodBlocks.particleHessian p N (Fin.castLE hn i) a X) ^ 2)
    _ ≤ ∑ a ∈ S, ENNReal.ofReal (B *
        (1 + (Riesz1.cyclicIndexDistance N (Fin.castLE hn i) a : ℝ)) ^ (-2 * s)) :=
      Finset.sum_le_sum fun a _ => hb p hp hpl hph N n hN hn θ hcurv ι (Fin.castLE hn i) a q hq
    _ = ENNReal.ofReal (B * ∑ a ∈ S,
        (1 + (Riesz1.cyclicIndexDistance N (Fin.castLE hn i) a : ℝ)) ^ (-2 * s)) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity), Finset.mul_sum]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have ht := internal_exterior_power_tail N n hn i (by linarith : 1 < 2 * s)
      dsimp only at ht
      have ht' := mul_le_mul_of_nonneg_left ht hB
      calc
        _ ≤ B * (2 * (1 + 1 / (2 * s - 1)) *
            (min (i.val + 1) ((n : ℕ) - i.val) : ℕ) ^ (1 - 2 * s)) := by
          simpa only [S, show -(2 * s) = -2 * s by ring] using ht'
        _ = _ := by dsimp only [B]; ring

end Riesz2.DecayShort
