/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.GapNondegeneracy
import Riesz2.Sanity.SmoothCutoff
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Ordinary-law score identities and finite-block nondegeneracy

See the proof of Theorem 3 in the paper, finite-volume part. All expectations use the
Gibbs law. Collision-flat integration by parts uses the affine density theorem with an
empty penalty set.
-/

public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter
open scoped ContDiff ENNReal Topology BigOperators

namespace Riesz2.GapNondegeneracy

/-- Positive and inverse gap powers are square integrable under the ordinary
law, as needed in the proof of Theorem 3. -/
theorem gap_power_memLp (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    {r : ℝ} (hr : 0 < r) (j : ℤ) :
    MemLp (fun X : Riesz1.Configuration N => gap X j ^ r) 2 (gibbsMeasure p N) ∧
    MemLp (fun X : Riesz1.Configuration N => gap X j ^ (-r)) 2 (gibbsMeasure p N) := by
  obtain ⟨D, _, hb⟩ := SingleGapTails.single_gap_moment_integrals
    p.val.2 p.val.1 p.val.1 p.property.2.1 p.property.2.2 p.property.1 le_rfl
    (2 * r) (by positivity)
  have h := hb p rfl le_rfl le_rfl N hN j
  have hi (a : ℝ) (ha : Integrable (fun X : Riesz1.Configuration N =>
      gap X j ^ (2 * a)) (gibbsMeasure p N)) :
      MemLp (fun X : Riesz1.Configuration N => gap X j ^ a) 2 (gibbsMeasure p N) := by
    have hm : AEStronglyMeasurable (fun X : Riesz1.Configuration N => gap X j ^ a)
        (gibbsMeasure p N) := ((Riesz1.measurable_gap j).pow_const a).aestronglyMeasurable
    apply (memLp_two_iff_integrable_sq hm).mpr
    have he (X : Riesz1.Configuration N) : (gap X j ^ a) ^ 2 = gap X j ^ (2 * a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (show 0 ≤ gap X j from (Riesz1.gap_pos X j).le)]
      congr 1
      ring
    simpa only [he] using ha
  exact ⟨hi r h.1, hi (-r) (by simpa only [mul_neg] using h.2.1)⟩

/-- Every ambient energy score is square integrable under the ordinary law
(the proof of Theorem 3). -/
theorem energy_direction_memLp (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ∀ w : EuclideanSpace ℝ (Fin (N : ℕ)),
        MemLp (fun X => fderiv ℝ W (WithLp.toLp 2 (gapVector X)) w) 2
          (gibbsMeasure p N) := by
  classical
  let μ := gibbsMeasure p N
  obtain ⟨U, hU, hv, ht⟩ := MarginalHessian.physical_energy_tensors p N
  obtain ⟨C, hC, hb⟩ := ht 1
  let W := fun y => p.val.1⁻¹ * U y
  have hW : ContDiffOn ℝ ∞ W (gapAmbientDomain N) := contDiffOn_const.mul hU
  have hder (y : EuclideanSpace ℝ (Fin (N : ℕ))) (hy : y ∈ gapAmbientDomain N) :
      fderiv ℝ W y = p.val.1⁻¹ • fderiv ℝ U y :=
    (((hU.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hy)).differentiableAt
      (by simp)).hasFDerivAt.const_mul _).fderiv
  refine ⟨W, hW, fun y => ?_, fun w => ?_⟩
  · dsimp only [W]
    rw [hv y, ← mul_assoc, inv_mul_cancel₀ p.property.1.ne', one_mul]
  · let F := fun X : Riesz1.Configuration N =>
      ∑ i : Fin (N : ℕ), gap X i.val ^ (-(p.val.2 + 1))
    have hF : MemLp F 2 μ := memLp_finsetSum _ fun i _ =>
      (gap_power_memLp p N hN
        (show 0 < p.val.2 + 1 by linarith [p.property.2.1]) i.val).2
    have hm : Measurable (fun X : Riesz1.Configuration N =>
        fderiv ℝ W (WithLp.toLp 2 (gapVector X)) w) :=
      (measurable_fderiv_apply_const ℝ W w).comp
        ((WithLp.measurable_toLp 2 _).comp (Riesz1.measurable_gapVector N))
    apply (hF.const_mul (p.val.1⁻¹ * C * ‖w‖)).of_le hm.aestronglyMeasurable
    apply Eventually.of_forall
    intro X
    let y := WithLp.toLp 2 (gapVector X)
    have hy : gapVector X ∈ Riesz1.gapSimplex N := by
      rw [← Riesz1.range_gapVector_eq_gapSimplex]
      exact Set.mem_range_self X
    obtain ⟨i, hi⟩ := ElementaryBarriers.exists_iInf_eq_apply (fun i : Fin (N : ℕ) => y i)
    let δ := y i
    have hδ : 0 < δ := hy.1 i
    have hgap (j : Fin (N : ℕ)) : δ ≤ y j := by
      change y i ≤ y j
      rw [← hi]
      exact ciInf_le (Finite.bddBelow_range _) j
    have hnorm : ‖fderiv ℝ U y‖ ≤ C * δ ^ (-p.val.2 - 1) := by
      simpa only [PNat.val_ofNat, Nat.cast_one, norm_iteratedFDeriv_one] using hb y hy δ hδ hgap
    have hsum : δ ^ (-p.val.2 - 1) ≤ F X := by
      have hh := Finset.single_le_sum (s := Finset.univ)
        (fun j _ => Real.rpow_nonneg (hy.1 j).le (-(p.val.2 + 1))) (Finset.mem_univ i)
      convert hh using 1 <;> congr 1; ring
    have hF0 : 0 ≤ F X := Finset.sum_nonneg fun j _ =>
      Real.rpow_nonneg (Riesz1.gap_pos X j.val).le _
    have hβinv : 0 ≤ p.val.1⁻¹ := inv_nonneg.mpr p.property.1.le
    rw [Real.norm_of_nonneg (show 0 ≤ p.val.1⁻¹ * C * ‖w‖ * F X by
      dsimp [F]; positivity), hder y (GapChart.gapVector_mem_gapAmbientDomain X),
      smul_apply, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr p.property.1.le)]
    calc
      _ ≤ p.val.1⁻¹ * (‖fderiv ℝ U y‖ * ‖w‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (by positivity)
      _ ≤ p.val.1⁻¹ * (C * F X * ‖w‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (hnorm.trans (mul_le_mul_of_nonneg_left hsum hC.le)) (norm_nonneg _)) hβinv
      _ = _ := by ring

/-- The ordinary Gibbs law in the full free-coordinate simplex chart, with
its exact partition and Jacobian factors. Internal support for the proof of Theorem 3. -/
theorem chart_density_law_internal (p : Parameters) (k : ℕ) (hk : 1 ≤ k) :
    (gibbsMeasure p k.succPNat).map
      (fun X : Riesz1.Configuration k.succPNat =>
        AffineSimplex.coordinates k (WithLp.toLp 2 (gapVector X))) =
      (partitionFunction p k.succPNat)⁻¹ •
          ENNReal.ofReal ((k + 1 : ℝ) ^ k)⁻¹ •
            volume.withDensity (fun x => ProperMarginalChart.density p k
                (AffineSimplex.chart k (k + 1) x)) := by
  classical
  let ρ := ProperMarginalChart.density p k
  have hρ : Measurable ρ := ProperMarginalChart.measurable_density p k
  have hcoord := (AffineSimplex.continuous_coordinates k).measurable
  have hchart := (AffineSimplex.continuous_chart k (k + 1)).measurable
  have hpush : ((AffineSimplex.simplexVolume k (k + 1)).withDensity ρ).map
      (AffineSimplex.coordinates k) = ENNReal.ofReal (Real.sqrt (k + 1)) •
        volume.withDensity (fun x => ρ (AffineSimplex.chart k (k + 1) x)) := by
    rw [AffineSimplex.simplexVolume_eq, withDensity_smul_measure,
      Measure.map_smul _ hcoord.aemeasurable,
      ← Riesz1.map_withDensity_comp _ hchart hρ, Measure.map_map hcoord hchart]
    have hid : AffineSimplex.coordinates k ∘ AffineSimplex.chart k (k + 1) = id :=
      funext (AffineSimplex.coordinates_chart k (k + 1))
    rw [hid, Measure.map_id]
    congr 1
    rw [← withDensity_indicator (AffineSimplex.isOpen_chartDomain k (k + 1)).measurableSet]
    congr 1
    funext x
    by_cases hx : x ∈ AffineSimplex.chartDomain k (k + 1)
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx]
      have hnot : AffineSimplex.chart k (k + 1) x ∉ AffineSimplex.massSimplex k (k + 1) :=
        fun h => hx ((AffineSimplex.chart_mem_simplex_iff k (k + 1) x).mp h)
      simp only [ρ, ProperMarginalChart.density,
        dite_eq_right hnot]
  have he := congrArg (Measure.map (AffineSimplex.coordinates k))
    (ProperMarginalChart.map_gibbsMeasure_full p k hk)
  have hm : Measurable (fun X : Riesz1.Configuration k.succPNat =>
      WithLp.toLp 2 (gapVector X)) := (WithLp.measurable_toLp 2 _).comp
        (Riesz1.measurable_gapVector k.succPNat)
  rw [Measure.map_map hcoord hm, Measure.map_smul _ hcoord.aemeasurable,
    Measure.map_smul _ hcoord.aemeasurable, Measure.map_smul _ hcoord.aemeasurable,
    hpush] at he
  simp only [smul_smul, ENNReal.inv_mul_cancel
    (ENNReal.ofReal_ne_zero_iff.mpr (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < k + 1)))
      ENNReal.ofReal_ne_top, mul_one] at he ⊢
  convert he using 1
  rfl

/-- See the proof of Theorem 3 in the paper: internal specialization
of the collision-flat score derivatives to the
ordinary Gibbs factor. The empty penalty set removes every cutoff term. -/
theorem affine_density_score_derivatives_internal (p : Parameters) (k : ℕ) (hk : 1 ≤ k)
    (d : ℕ) (A : EuclideanSpace ℝ (Fin d) →ᴬ[ℝ] EuclideanSpace ℝ (Fin (k + 1)))
    (hmass : ∀ x, ∑ i, A x i = (k + 1 : ℝ))
    (U : EuclideanSpace ℝ (Fin (k + 1)) → ℝ)
    (hU : ContDiffOn ℝ ∞ U (gapAmbientDomain k.succPNat))
    (hval : ∀ y : {y : EuclideanSpace ℝ (Fin (k + 1)) // y ∈ gapAmbientDomain k.succPNat},
      U y.val = physicalAmbientGapEnergy p k.succPNat y)
    (v : EuclideanSpace ℝ (Fin d)) :
    let g := fun x => (ProperMarginalChart.density p k (A x)).toReal
    let w := A.contLinear v
    let T := fun x => fderiv ℝ U (A x) w
    let H := fun x => fderiv ℝ (fderiv ℝ U) (A x) w w
    Differentiable ℝ g ∧ Differentiable ℝ (fun x => fderiv ℝ g x v) ∧
      (∀ x, fderiv ℝ g x v = -p.val.1 * g x * T x) ∧
      (∀ x, fderiv ℝ (fun y => fderiv ℝ g y v) x v =
        p.val.1 * g x * (p.val.1 * T x ^ 2 - H x)) := by
  obtain ⟨θ⟩ := DefinitionSanity.physicalCutoff_nonempty
  have hv : ∀ y : {y : EuclideanSpace ℝ (Fin (k + 1)) // y ∈ gapAmbientDomain k.succPNat},
      U y.val = physicalAmbientGapEnergy p k.succPNat y +
        ∑ i ∈ (∅ : Finset (Fin (k + 1))), (θ.val (1 * y.val i) + θ.val (1 / y.val i)) := by
    simpa only [Finset.sum_empty, add_zero] using hval
  simpa only [ProperMarginalChart.penalizedDensity, Finset.sum_empty,
    mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one, mul_one] using
    LengthVariance.Internal.affine_density_score_derivatives p k hk d A hmass θ
      zero_lt_one ∅ U hU hv v

/-- See the proof of Theorem 3 in the paper: internal ordinary-law
score theorem for a linear observable with nonzero
directional derivative. The physical realization and integrable Hessian are
supplied by `expected_compensated_curvature` in the finite-volume theorem. -/
theorem score_identities_internal (p : Parameters) (k : ℕ) (hk : 1 ≤ k)
    (U : EuclideanSpace ℝ (Fin (k + 1)) → ℝ)
    (hU : ContDiffOn ℝ ∞ U (gapAmbientDomain k.succPNat))
    (hval : ∀ y : {y : EuclideanSpace ℝ (Fin (k + 1)) // y ∈ gapAmbientDomain k.succPNat},
      U y.val = physicalAmbientGapEnergy p k.succPNat y)
    (w : EuclideanSpace ℝ (Fin (k + 1))) (hw : (∑ i, w i) = 0)
    (ℓ : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] ℝ) (hℓ : ℓ w ≠ 0)
    (hH : Integrable (fun X : Riesz1.Configuration k.succPNat => fderiv ℝ (fderiv ℝ U) (WithLp.toLp 2 (gapVector X)) w w)
      (gibbsMeasure p k.succPNat)) :
    let μ := gibbsMeasure p k.succPNat
    let S := fun X : Riesz1.Configuration k.succPNat => ℓ (WithLp.toLp 2 (gapVector X))
    let T := fun X : Riesz1.Configuration k.succPNat => fderiv ℝ U (WithLp.toLp 2 (gapVector X)) w
    MemLp T 2 μ ∧ p.val.1 * ProbabilityTheory.covariance S T μ = ℓ w ∧
      (∫ X, T X ^ 2 ∂μ) = p.val.1⁻¹ *
        ∫ X, fderiv ℝ (fderiv ℝ U) (WithLp.toLp 2 (gapVector X)) w w ∂μ := by
  classical
  intro μ S T
  have hN : 2 ≤ (k.succPNat : ℕ) := by simp only [Nat.succPNat_coe]; omega
  have : IsProbabilityMeasure μ := gibbsMeasure_probability p k.succPNat
  obtain ⟨U₀, hU₀, hv₀, hmem₀⟩ := energy_direction_memLp p k.succPNat hN
  have hT : MemLp T 2 μ := by
    apply (memLp_congr_ae (Eventually.of_forall fun X => ?_)).mpr (hmem₀ w)
    let y := WithLp.toLp 2 (gapVector X)
    have hy := GapChart.gapVector_mem_gapAmbientDomain X
    have heq : U =ᶠ[𝓝 y] U₀ := eventuallyEq_of_mem
      ((PhysicalEnergy.isOpen_gapAmbientDomain _).mem_nhds hy) fun z hz =>
        (hval ⟨z, hz⟩).trans (hv₀ ⟨z, hz⟩).symm
    exact congrArg (fun D : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] ℝ => D w) (heq.fderiv_eq (𝕜 := ℝ))
  let L := (AffineSimplex.tangentMap k).toContinuousLinearMap
  let A : EuclideanSpace ℝ (Fin k) →ᴬ[ℝ] EuclideanSpace ℝ (Fin (k + 1)) :=
    L.toContinuousAffineMap + ContinuousAffineMap.const ℝ _ (AffineSimplex.chart k (k + 1) 0)
  have hAL : A.contLinear = L := by
    ext z i
    simp [A]
  have hA (x) : A x = AffineSimplex.chart k (k + 1) x :=
    (AffineSimplex.chart_eq_tangentMap_add k (k + 1) x).symm
  have hmass (x) : ∑ i, A x i = (k + 1 : ℝ) := by rw [hA]; exact AffineSimplex.sum_chart _ _ _
  let v := AffineSimplex.coordinates k w
  have hLv : L v = w := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have hh := hw
      rw [Fin.sum_univ_castSucc] at hh
      change AffineSimplex.chart k 0 v (Fin.last k) = w (Fin.last k)
      rw [AffineSimplex.chart_last]
      change 0 - ∑ j : Fin k, w j.castSucc = w (Fin.last k)
      linarith
    · change AffineSimplex.chart k 0 v j.castSucc = w j.castSucc
      rw [AffineSimplex.chart_castSucc]
      rfl
  let π := fun X : Riesz1.Configuration k.succPNat =>
    AffineSimplex.coordinates k (WithLp.toLp 2 (gapVector X))
  have hπ : Measurable π := (AffineSimplex.continuous_coordinates k).measurable.comp
    ((WithLp.measurable_toLp 2 _).comp (Riesz1.measurable_gapVector k.succPNat))
  have hAπ (X : Riesz1.Configuration k.succPNat) : A (π X) = WithLp.toLp 2 (gapVector X) := by
    rw [hA]
    apply AffineSimplex.chart_coordinates
    have hy : gapVector X ∈ Riesz1.gapSimplex k.succPNat := by
      rw [← Riesz1.range_gapVector_eq_gapSimplex]
      exact Set.mem_range_self X
    change (∑ i : Fin (k + 1), gapVector X i) = k + 1
    simpa only [Nat.succPNat_coe, Nat.cast_succ] using hy.2
  let ρ := ProperMarginalChart.density p k
  let g := fun x => (ρ (A x)).toReal
  let Tc := fun x => fderiv ℝ U (A x) w
  let Hc := fun x => fderiv ℝ (fderiv ℝ U) (A x) w w
  let Sc := fun x : EuclideanSpace ℝ (Fin k) => (ℓ w)⁻¹ * ℓ (A x)
  let c := (partitionFunction p k.succPNat)⁻¹ * ENNReal.ofReal ((k + 1 : ℝ) ^ k)⁻¹
  let ν := μ.map π
  have hρ : Measurable ρ := ProperMarginalChart.measurable_density p k
  have hρt (y) : ρ y ≠ ⊤ := by
    dsimp only [ρ, ProperMarginalChart.density]
    split_ifs <;> finiteness
  have hν : ν = c • volume.withDensity (fun x => ENNReal.ofReal (g x)) := by
    have hh := chart_density_law_internal p k hk
    change ν = _ at hh
    rw [hh]
    simp only [smul_smul]
    congr 2
    funext x
    rw [ENNReal.ofReal_toReal (hρt _), hA]
  have hc0 : c ≠ 0 := by
    exact mul_ne_zero (ENNReal.inv_ne_zero.mpr (finiteModel_valid p k.succPNat).2.2.2.ne)
      (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))
  have hct : c ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.inv_ne_top.mpr (finiteModel_valid p k.succPNat).2.2.1.ne') ENNReal.ofReal_ne_top
  have hgm : Measurable g := ENNReal.measurable_toReal.comp (hρ.comp A.continuous.measurable)
  have hTcm : Measurable Tc := (measurable_fderiv_apply_const ℝ U w).comp A.continuous.measurable
  have hHcm : Measurable Hc := ((ContinuousLinearMap.measurable_apply w).comp
    (measurable_fderiv_apply_const ℝ (fderiv ℝ U) w)).comp A.continuous.measurable
  have hScd : Differentiable ℝ Sc := (ℓ.differentiable.comp A.differentiable).const_mul _
  have hScv (x) : fderiv ℝ Sc x v = 1 := by
    have hd := (ℓ.hasFDerivAt.comp x A.hasFDerivAt).const_mul (ℓ w)⁻¹
    change HasFDerivAt Sc _ x at hd
    rw [hd.fderiv]
    simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply, hAL, hLv]
    exact inv_mul_cancel₀ hℓ
  have hScπ (X) : Sc (π X) = (ℓ w)⁻¹ * S X := by
    dsimp only [Sc, S]
    rw [hAπ]
  have hTcπ (X) : Tc (π X) = T X := by dsimp only [Tc]; rw [hAπ]
  have hHcπ (X) : Hc (π X) = fderiv ℝ (fderiv ℝ U) (WithLp.toLp 2 (gapVector X)) w w := by dsimp only [Hc]; rw [hAπ]
  have hgap : MemLp (fun X : Riesz1.Configuration k.succPNat =>
      WithLp.toLp 2 (gapVector X)) 2 μ := by
    apply memLp_piLp_iff.mpr
    intro i
    change MemLp (fun X : Riesz1.Configuration k.succPNat => gap X i.val) 2
      (gibbsMeasure p k.succPNat)
    simpa only [Real.rpow_one] using (gap_power_memLp p k.succPNat hN
      (r := 1) zero_lt_one i.val).1
  have hS : MemLp S 2 μ := ℓ.comp_memLp' hgap
  have hTc : MemLp Tc 2 ν := (memLp_map_measure_iff hTcm.aestronglyMeasurable hπ.aemeasurable).mpr
    ((memLp_congr_ae (Eventually.of_forall hTcπ)).mpr hT)
  have hSc : MemLp Sc 2 ν := (memLp_map_measure_iff hScd.continuous.measurable.aestronglyMeasurable hπ.aemeasurable).mpr
    ((memLp_congr_ae (Eventually.of_forall hScπ)).mpr (hS.const_mul _))
  have hHc : Integrable Hc ν := (integrable_map_measure hHcm.aestronglyMeasurable hπ.aemeasurable).mpr
    (hH.congr (Eventually.of_forall fun X => (hHcπ X).symm))
  obtain ⟨hg, hflux, hd, hdd⟩ := affine_density_score_derivatives_internal p k hk k A hmass U hU hval v
  rw [hAL, hLv] at hd hdd
  have : IsProbabilityMeasure ν := inferInstance
  have hident := LengthVariance.Internal.normalized_density_score_identities hc0 hct hgm
    (fun x => ENNReal.toReal_nonneg) hg v hflux hScd hScv p.property.1 hd hdd
    (hν ▸ (inferInstance : IsProbabilityMeasure ν))
    (hν ▸ hSc) (hν ▸ hTc) (hν ▸ hHc)
  dsimp only at hident
  rw [← hν] at hident
  refine ⟨hT, ?_, ?_⟩
  · have hc := ProbabilityTheory.covariance_map_fun hSc.aestronglyMeasurable
      hTc.aestronglyMeasurable hπ.aemeasurable
    change ProbabilityTheory.covariance Sc Tc ν = _ at hc
    simp only [hScπ, hTcπ] at hc
    rw [hc] at hident
    rw [ProbabilityTheory.covariance_const_mul_left] at hident
    have hh := congrArg (fun z : ℝ => ℓ w * z) hident.1
    simpa only [← mul_assoc, mul_left_comm (ℓ w) p.val.1,
      mul_inv_cancel₀ hℓ, mul_one] using hh
  · have hleft : (∫ x, Tc x ^ 2 ∂ν) = ∫ X, T X ^ 2 ∂μ := by
      rw [integral_map hπ.aemeasurable (hTcm.pow_const 2).aestronglyMeasurable]
      simp only [hTcπ]
    have hright : (∫ x, Hc x ∂ν) = ∫ X,
        fderiv ℝ (fderiv ℝ U) (WithLp.toLp 2 (gapVector X)) w w ∂μ := by
      rw [integral_map hπ.aemeasurable hHcm.aestronglyMeasurable]
      simp only [hHcπ]
    calc
      _ = ∫ x, Tc x ^ 2 ∂ν := hleft.symm
      _ = p.val.1⁻¹ * ∫ x, Hc x ∂ν := hident.2
      _ = _ := by rw [hright]

/-- See the proof of Theorem 3 in the paper: the ordinary-law
score is in L², its covariance pairing equals the squared block norm,
and its square expectation equals the expected directional curvature divided
by β. The expected curvature has one bound uniform in the volume and direction.
The zero direction is included. -/
theorem compensated_score_identities (p : Parameters) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 2 ≤ k + m + 1 →
      ∃ U : EuclideanSpace ℝ (Fin (k + m + 1)) → ℝ,
        ContDiffOn ℝ ∞ U (gapAmbientDomain (k + m).succPNat) ∧
        (∀ y : {y : EuclideanSpace ℝ (Fin (k + m + 1)) //
            y ∈ gapAmbientDomain (k + m).succPNat},
          U y.val = physicalAmbientGapEnergy p (k + m).succPNat y) ∧
        ∀ u : EuclideanSpace ℝ (Fin k),
          let N := (k + m).succPNat
          let w := MarginalHessian.compensatedDirection k m (Equiv.refl _) u
          let A := fun X : Riesz1.Configuration N => ∑ i : Fin k, u i * gap X i.val
          let T := fun X : Riesz1.Configuration N => fderiv ℝ U (WithLp.toLp 2 (gapVector X)) w
          let H := fun X : Riesz1.Configuration N =>
            fderiv ℝ (fderiv ℝ U) (WithLp.toLp 2 (gapVector X)) w w
          MemLp T 2 (gibbsMeasure p N) ∧ Integrable H (gibbsMeasure p N) ∧
            p.val.1 * ProbabilityTheory.covariance A T (gibbsMeasure p N) = ‖u‖ ^ 2 ∧
            (∫ X, T X ^ 2 ∂gibbsMeasure p N) = p.val.1⁻¹ * ∫ X, H X ∂gibbsMeasure p N ∧
            (∫ X, H X ∂gibbsMeasure p N) ≤ C * ‖u‖ ^ 2 := by
  classical
  obtain ⟨C, hC, hcurv⟩ := expected_compensated_curvature p k
  refine ⟨C, hC, fun m hN => ?_⟩
  obtain ⟨U, hU, hv, hUb⟩ := hcurv m hN
  refine ⟨U, hU, hv, fun u => ?_⟩
  intro N w A T H
  by_cases hu : u = 0
  · have hw : w = 0 := by simp only [w, hu, map_zero]
    have hA : A = 0 := by ext X; simp [A, hu]
    have hT : T = 0 := by ext X; simp [T, hw]
    have hH : H = 0 := by ext X; simp [H, hw]
    simp only [hA, hT, hH, hu, MemLp.zero, integrable_zero, Pi.zero_apply,
      ProbabilityTheory.covariance_zero_left, mul_zero, norm_zero,
      zero_pow (by norm_num : 2 ≠ 0), integral_zero, le_refl, and_self]
  · let μ := gibbsMeasure p N
    have hq : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
    have hw : (∑ j, w j) = 0 := (compensated_direction_bounds k m u).1
    let ℓ : EuclideanSpace ℝ (Fin (k + m + 1)) →L[ℝ] ℝ :=
      ∑ i : Fin k, u i • EuclideanSpace.proj (𝕜 := ℝ) (i.castAdd (m + 1))
    have hℓ (y) : ℓ y = ∑ i : Fin k, u i * y (i.castAdd (m + 1)) := by
      simp only [ℓ, sum_apply, smul_apply, smul_eq_mul]
      rfl
    have hℓw : ℓ w = ‖u‖ ^ 2 := by
      rw [hℓ]
      have hret (i : Fin k) : w (i.castAdd (m + 1)) = u i :=
        (compensated_direction_bounds k m u).2.1 i
      simp_rw [hret]
      rw [EuclideanSpace.real_norm_sq_eq]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hℓA (X : Riesz1.Configuration N) : ℓ (WithLp.toLp 2 (gapVector X)) = A X := by
      rw [hℓ]
      rfl
    obtain ⟨hT, hpair, hscore⟩ := score_identities_internal p (k + m) (by omega)
      U hU hv w hw ℓ (by rw [hℓw]; exact hq.ne') (hUb u).1
    change MemLp T 2 μ at hT
    change p.val.1 * ProbabilityTheory.covariance (fun X : Riesz1.Configuration N => ℓ (WithLp.toLp 2 (gapVector X))) T μ = ℓ w at hpair
    simp_rw [hℓA, hℓw] at hpair
    exact ⟨hT, (hUb u).1, hpair, hscore, (hUb u).2⟩

/-- See the proof of Theorem 3 in the paper, finite-volume covariance
lower bound on the particle Gibbs law. The constant precedes the
volume and the prescribed block direction. The second moment is concluded. -/
theorem finite_gibbs_covariance_lower_bound (p : Parameters) (k : ℕ) (hk : 1 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ+), 2 * k + 2 ≤ (N : ℕ) →
      ∀ u : EuclideanSpace ℝ (Fin k),
        let A := fun X : Riesz1.Configuration N => ∑ i : Fin k, u i * gap X i.val
        MemLp A 2 (gibbsMeasure p N) ∧
          c * ‖u‖ ^ 2 ≤ ∫ X, (A X - ∫ Z, A Z ∂gibbsMeasure p N) ^ 2 ∂gibbsMeasure p N := by
  classical
  obtain ⟨C, hC, hcurv⟩ := compensated_score_identities p k
  refine ⟨(p.val.1 * C)⁻¹, inv_pos.mpr (mul_pos p.property.1 hC), fun N hN u => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, N = (k + m).succPNat :=
    ⟨(N : ℕ) - k - 1, PNat.eq (by simp only [Nat.succPNat_coe]; omega)⟩
  let N := (k + m).succPNat
  let μ := gibbsMeasure p N
  let A := fun X : Riesz1.Configuration N => ∑ i : Fin k, u i * gap X i.val
  have hN₂ : 2 ≤ (N : ℕ) := by dsimp [N]; omega
  have : IsProbabilityMeasure μ := gibbsMeasure_probability p N
  have hA : MemLp A 2 μ := memLp_finsetSum _ fun i _ => by
    have hh := ((gap_power_memLp p N hN₂ (r := 1) zero_lt_one i.val).1).const_mul (u i)
    simpa only [Real.rpow_one] using hh
  refine ⟨hA, ?_⟩
  change (p.val.1 * C)⁻¹ * ‖u‖ ^ 2 ≤ ∫ X, (A X - ∫ Z, A Z ∂μ) ^ 2 ∂μ
  by_cases hu : u = 0
  · subst u
    simpa only [norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero] using
      (integral_nonneg (μ := μ) fun X => sq_nonneg (A X - ∫ Z, A Z ∂μ))
  have hq : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
  obtain ⟨U, hU, hv, hUb⟩ := hcurv m (by dsimp [N] at hN₂; omega)
  obtain ⟨hT, hH, hpair, hscore, hcurvb⟩ := hUb u
  let w := MarginalHessian.compensatedDirection k m (Equiv.refl _) u
  let T := fun X : Riesz1.Configuration N => fderiv ℝ U (WithLp.toLp 2 (gapVector X)) w
  change MemLp T 2 μ at hT
  change p.val.1 * ProbabilityTheory.covariance A T μ = ‖u‖ ^ 2 at hpair
  have hscoreb : (∫ X, T X ^ 2 ∂μ) ≤ p.val.1⁻¹ * (C * ‖u‖ ^ 2) := by
    change (∫ X, T X ^ 2 ∂μ) = _ at hscore
    rw [hscore]
    exact mul_le_mul_of_nonneg_left hcurvb (inv_nonneg.mpr p.property.1.le)
  have hCS := CovarianceCauchySchwarz.abs_covariance_le hA hT
  have hCSsq := pow_le_pow_left₀ (abs_nonneg _) hCS 2
  rw [sq_abs, mul_pow,
    Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _),
    Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)] at hCSsq
  have hVT : (∫ X, (T X - ∫ Z, T Z ∂μ) ^ 2 ∂μ) ≤ ∫ X, T X ^ 2 ∂μ := by
    rw [← ProbabilityTheory.variance_eq_integral hT.aemeasurable]
    exact ProbabilityTheory.variance_le_expectation_sq hT.aestronglyMeasurable
  let V := ∫ X, (A X - ∫ Z, A Z ∂μ) ^ 2 ∂μ
  have hV : 0 ≤ V := integral_nonneg fun _ => sq_nonneg _
  have hb := mul_le_mul_of_nonneg_left
    (hCSsq.trans (mul_le_mul_of_nonneg_left (hVT.trans hscoreb) hV)) (sq_nonneg p.val.1)
  have he : p.val.1 ^ 2 * (ProbabilityTheory.covariance A T μ) ^ 2 = (‖u‖ ^ 2) ^ 2 := by
    rw [← mul_pow, hpair]
  rw [he] at hb
  have he₂ : p.val.1 ^ 2 * (V * (p.val.1⁻¹ * (C * ‖u‖ ^ 2))) =
      (p.val.1 * C * V) * ‖u‖ ^ 2 := by
    field_simp
  change (‖u‖ ^ 2) ^ 2 ≤ p.val.1 ^ 2 * (V * (p.val.1⁻¹ * (C * ‖u‖ ^ 2))) at hb
  rw [he₂, pow_two] at hb
  have hlin : ‖u‖ ^ 2 ≤ p.val.1 * C * V := (mul_le_mul_iff_left₀ hq).mp hb
  apply (mul_le_mul_iff_right₀ (mul_pos p.property.1 hC)).mp
  calc
    _ = ‖u‖ ^ 2 := by field_simp [p.property.1.ne', hC.ne']
    _ ≤ p.val.1 * C * V := hlin
    _ = _ := by ring

/-- See the proof of Theorem 3 in the paper, the complete finite-volume
claim on the periodic laws of Subsection 6.3. Square integrability makes the
real variance finite before the lower bound is used. -/
theorem finite_volume_covariance_lower_bound (p : Parameters) (k : ℕ) (hk : 1 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ+), 2 * k + 2 ≤ (N : ℕ) →
      ∀ u : EuclideanSpace ℝ (Fin k),
        let A := fun y : ℤ → Ioi (0 : ℝ) => ∑ i : Fin k, u i * (y i.val : ℝ)
        MemLp A 2 (periodicGapLaw p N).toMeasure ∧
          c * ‖u‖ ^ 2 ≤ ∫ y, (A y - ∫ z, A z ∂periodicGapLaw p N) ^ 2
            ∂periodicGapLaw p N := by
  obtain ⟨c, hc, hb⟩ := finite_gibbs_covariance_lower_bound p k hk
  refine ⟨c, hc, fun N hN u => ?_⟩
  let A := fun y : ℤ → Ioi (0 : ℝ) => ∑ i : Fin k, u i * (y i.val : ℝ)
  have hm : Measurable A := Finset.measurable_sum _ fun i _ =>
    (measurable_subtype_coe.comp (measurable_pi_apply _)).const_mul _
  obtain ⟨hA, hlow⟩ := hb N hN u
  have hAp : MemLp A 2 (periodicGapLaw p N).toMeasure := by
    rw [periodicGapLaw_toMeasure]
    exact (memLp_map_measure_iff hm.aestronglyMeasurable
      (measurable_periodicGapSequence N).aemeasurable).mpr hA
  refine ⟨hAp, ?_⟩
  rw [integral_periodicGapLaw p N ((hm.sub_const _).pow_const 2),
    integral_periodicGapLaw p N hm]
  exact hlow

/-- The same finite-volume conclusion in the extended-variance
convention of Theorem 1. The L² witness is part of the conclusion. -/
theorem finite_volume_covariance_lower_bound_extended (p : Parameters) (k : ℕ) (hk : 1 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ+), 2 * k + 2 ≤ (N : ℕ) →
      ∀ u : EuclideanSpace ℝ (Fin k),
        let A := fun y : ℤ → Ioi (0 : ℝ) => ∑ i : Fin k, u i * (y i.val : ℝ)
        ∃ hA : MemLp A 2 (periodicGapLaw p N).toMeasure,
          ENNReal.ofReal (c * ‖u‖ ^ 2) ≤
            Riesz1.variance (periodicGapLaw p N).toMeasure A (hA.integrable one_le_two) := by
  obtain ⟨c, hc, hb⟩ := finite_volume_covariance_lower_bound p k hk
  refine ⟨c, hc, fun N hN u => ?_⟩
  obtain ⟨hA, hlow⟩ := hb N hN u
  refine ⟨hA, ?_⟩
  rw [Riesz1.variance_eq_ofReal_integral_sq _ _ hA]
  exact ENNReal.ofReal_le_ofReal hlow

end Riesz2.GapNondegeneracy
