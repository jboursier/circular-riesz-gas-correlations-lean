/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.GapLimit
public import Riesz2.Thermodynamic.LengthVariancePart4
public import Riesz2.ToMathlib.CyclicIndicatorConvolution
public import Riesz2.ToMathlib.RpowPartialSums

/-!
# Fixed-block nondegeneracy

Supporting estimates for the proof of Theorem 3. The compensated displacement is the
existing `MarginalHessian.compensatedDirection`. Its cyclic convolution bound is uniform
in the ambient volume.
-/

public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter Set Finset
open scoped ENNReal Topology BigOperators ContDiff

namespace Riesz2.GapNondegeneracy

/-- The finite Young estimate used in the proof of Theorem 3, before specializing the displacement.
Each coordinate occurs exactly `r` times. No sign assumption is imposed. -/
theorem sum_sq_cyclicGapSum_le (N : ℕ+) (r : ℕ) (hr : r ≤ (N : ℕ))
    (v : Fin (N : ℕ) → ℝ) :
    (∑ i, (cyclicGapSum N i r v) ^ 2) ≤ (r : ℝ) * (∑ j, |v j|) ^ 2 := by
  let A := fun i => cyclicGapSum N i r (fun j => |v j|)
  let L := ∑ j, |v j|
  have hA0 (i) : 0 ≤ A i := sum_nonneg fun j _ => abs_nonneg _
  have habs (i) : |cyclicGapSum N i r v| ≤ A i := abs_sum_le_sum_abs _ _
  have hAle (i) : A i ≤ L := by
    rw [show A i = ∑ j ∈ cyclicIndexInterval N i r, |v j| from
      (sum_cyclicIndexInterval_eq_cyclicGapSum N i hr _).symm]
    exact sum_le_univ_sum_of_nonneg (fun j => abs_nonneg _)
  have hsq (i) : (cyclicGapSum N i r v) ^ 2 ≤ L * A i := by
    have h1 := habs i
    have h2 := hAle i
    have h3 := hA0 i
    nlinarith [sq_abs (cyclicGapSum N i r v),
      mul_nonneg (sub_nonneg.mpr h2) h3,
      mul_nonneg (sub_nonneg.mpr h1) (add_nonneg h3 (abs_nonneg (cyclicGapSum N i r v)))]
  calc
    _ ≤ ∑ i, L * A i := sum_le_sum fun i _ => hsq i
    _ = L * ((r : ℝ) * L) := by rw [← mul_sum, sum_cyclicGapSum]
    _ = _ := by ring

/-- The existing compensated direction has total mass zero, agrees with
the prescribed block vector, and has at most twice its block ℓ¹ norm. -/
theorem compensated_direction_bounds (k m : ℕ) (u : EuclideanSpace ℝ (Fin k)) :
    let w := MarginalHessian.compensatedDirection k m (Equiv.refl _) u
    (∑ j, w j) = 0 ∧
      (∀ i : Fin k, w (i.castAdd (m + 1)) = u i) ∧
      (∑ j, |w j|) ≤ 2 * ∑ i, |u i| := by
  intro w
  have hret (i : Fin k) : w (i.castAdd (m + 1)) = u i := by
    change MarginalHessian.compensatedDirection k m (Equiv.refl _) u
      ((i.castAdd m).castSucc) = u i
    exact MarginalHessian.compensatedDirection_retained k m (Equiv.refl _) u i
  have hext (i : Fin (m + 1)) : w (i.natAdd k) = -(∑ j, u j) / (m + 1 : ℝ) := by
    simpa only [Equiv.refl_apply] using
      MarginalHessian.compensatedDirection_exterior k m (Equiv.refl _) u i
  have hm : (0 : ℝ) < m + 1 := by positivity
  constructor
  · change (∑ j : Fin (k + (m + 1)), w j) = 0
    rw [Fin.sum_univ_add]
    simp only [hret, hext, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
    ring
  refine ⟨hret, ?_⟩
  change (∑ j : Fin (k + (m + 1)), |w j|) ≤ _
  rw [Fin.sum_univ_add]
  simp only [hret, hext, abs_div, abs_neg, abs_of_pos hm,
    sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  rw [mul_div_cancel₀ _ hm.ne']
  linarith [abs_sum_le_sum_abs (fun i : Fin k => u i) univ]

/-- See the proof of Theorem 3 in the paper, the displayed block
convolution estimate with constant `4k`, valid also at the zero vector. -/
theorem compensated_convolution_bound (k m r : ℕ)
    (hr : r ≤ k + m + 1) (u : EuclideanSpace ℝ (Fin k)) :
    let N := (k + m).succPNat
    let w := MarginalHessian.compensatedDirection k m (Equiv.refl _) u
    (∑ i : Fin (N : ℕ), (cyclicGapSum N i r (WithLp.ofLp w)) ^ 2) ≤
      4 * (k : ℝ) * r * ‖u‖ ^ 2 := by
  intro N w
  have hb := (compensated_direction_bounds k m u).2.2
  have hL0 : 0 ≤ ∑ i, |u i| := sum_nonneg fun i _ => abs_nonneg _
  have hw0 : 0 ≤ ∑ j, |w j| := sum_nonneg fun j _ => abs_nonneg _
  have hsq : (∑ j, |w j|) ^ 2 ≤ 4 * (∑ i, |u i|) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) (add_nonneg hw0 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hL0))]
  have hc : (∑ i, |u i|) ^ 2 ≤ (k : ℝ) * ‖u‖ ^ 2 := by
    have h := sum_mul_sq_le_sq_mul_sq (s := univ) (fun _ : Fin k => (1 : ℝ))
      (fun i => |u i|)
    simpa only [one_mul, one_pow, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, sq_abs, EuclideanSpace.real_norm_sq_eq] using h
  calc
    _ ≤ (r : ℝ) * (∑ j, |w j|) ^ 2 :=
      sum_sq_cyclicGapSum_le N r hr (WithLp.ofLp w)
    _ ≤ (r : ℝ) * (4 * ((k : ℝ) * ‖u‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (hsq.trans (mul_le_mul_of_nonneg_left hc (by norm_num)))
        (Nat.cast_nonneg _)
    _ = _ := by ring

/-- The coefficient moments already proved from inverse-gap moments give
an integrable expected interval curvature under the ordinary Gibbs law. -/
theorem expected_interval_curvature (p : Parameters) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ+, 2 ≤ (N : ℕ) →
      ∀ (j : ℤ) (r : ℕ) (hr : 0 < r) (hrN : r ≤ (N : ℕ) / 2),
        Integrable (GoodBlocks.particleCoefficient p N j r hr hrN) (gibbsMeasure p N) ∧
          (∫ X, GoodBlocks.particleCoefficient p N j r hr hrN X ∂gibbsMeasure p N) ≤
            C * (r : ℝ) ^ (-p.val.2 - 2) := by
  obtain ⟨C, hC, hb⟩ := GoodBlocks.particleCoefficient_moments p.val.2 p.val.1 p.val.1
    p.property.2.1 p.property.1 le_rfl
  refine ⟨C, hC, fun N hN j r hr hrN => ?_⟩
  let f := GoodBlocks.particleCoefficient p N j r hr hrN
  have hf := GoodBlocks.measurable_particleCoefficient p N j r hr hrN
  have hf0 (X) : 0 ≤ f X := (GoodBlocks.particleCoefficient_pos p N j r hr hrN X).le
  have hh := hb p rfl le_rfl le_rfl N hN j r hr hrN 1 le_rfl
  simp only [ENNReal.ofReal_one, Real.one_rpow, mul_one] at hh
  have hi : Integrable f (gibbsMeasure p N) := memLp_one_iff_integrable.mp
    (hh.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨hi, ?_⟩
  rw [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable] at hh
  have he (X) : ‖f X‖ₑ = ENNReal.ofReal (f X) := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_pos (GoodBlocks.particleCoefficient_pos p N j r hr hrN X)]
  change (∫⁻ X, ‖f X‖ₑ ∂gibbsMeasure p N) ≤ _ at hh
  simp_rw [he] at hh
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hf0)]
  exact hh

/-- See the proof of Theorem 3 in the paper, uniform expected
Hamiltonian curvature for every compensated fixed-block direction.
The realizing function agrees with the energy on the entire
ambient domain, and integrability precedes the expectation bound. -/
theorem expected_compensated_curvature (p : Parameters) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 2 ≤ k + m + 1 →
      let N := (k + m).succPNat
      ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
        ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
        (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
          W y.val = physicalAmbientGapEnergy p N y) ∧
        ∀ u : EuclideanSpace ℝ (Fin k),
          let w := MarginalHessian.compensatedDirection k m (Equiv.refl _) u
          Integrable (fun X => fderiv ℝ (fderiv ℝ W) (WithLp.toLp 2 (gapVector X)) w w)
            (gibbsMeasure p N) ∧
          (∫ X, fderiv ℝ (fderiv ℝ W) (WithLp.toLp 2 (gapVector X)) w w ∂gibbsMeasure p N) ≤
            C * ‖u‖ ^ 2 := by
  classical
  obtain ⟨B, hB, hcoeff⟩ := expected_interval_curvature p
  let D := ∑' j : ℕ, (1 + (j : ℝ)) ^ (-(p.val.2 + 1))
  have hD : 0 ≤ D := tsum_nonneg fun _ => Real.rpow_nonneg (by positivity) _
  refine ⟨4 * B * (k + 1) * (D + 1), by positivity, fun m hN => ?_⟩
  intro N
  obtain ⟨W, hW, hval, hd⟩ := PhysicalEnergy.ambient_derivatives p N
  refine ⟨W, hW, hval, fun u => ?_⟩
  intro w
  let F := fun (i : Fin (N : ℕ)) (r : Fin ((N : ℕ) / 2)) =>
    GoodBlocks.particleCoefficient p N i.val (r.val + 1) (by omega) (by have := r.isLt; omega)
  let q := fun (i : Fin (N : ℕ)) (r : Fin ((N : ℕ) / 2)) =>
    (cyclicGapSum N i (r.val + 1) (WithLp.ofLp w)) ^ 2
  have hFi (i) (r) : Integrable (F i r) (gibbsMeasure p N) :=
    (hcoeff N hN i.val (r.val + 1) (by omega) (by have := r.isLt; omega)).1
  have hFb (i) (r) : (∫ X, F i r X ∂gibbsMeasure p N) ≤ B * (r.val + 1 : ℝ) ^ (-p.val.2 - 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (hcoeff N hN i.val (r.val + 1) (by omega) (by have := r.isLt; omega)).2
  have hquad (X : Riesz1.Configuration N) :
      fderiv ℝ (fderiv ℝ W) (WithLp.toLp 2 (gapVector X)) w w = ∑ i, ∑ r, F i r X * q i r := by
    rw [(hd ⟨WithLp.toLp 2 (gapVector X), GapChart.gapVector_mem_gapAmbientDomain X⟩ w w).2]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro r _
    dsimp only [F, q]
    rw [GoodBlocks.particleCoefficient_gapVector, pow_two]
  have hsum : Integrable (fun X => ∑ i, ∑ r, F i r X * q i r) (gibbsMeasure p N) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun r _ => (hFi i r).mul_const _
  refine ⟨hsum.congr (Eventually.of_forall fun X => (hquad X).symm), ?_⟩
  have hp : (∑ r : Fin ((N : ℕ) / 2), (r.val + 1 : ℝ) ^ (-p.val.2 - 2) *
      ∑ i : Fin (N : ℕ), q i r) ≤ 4 * (k : ℝ) * ‖u‖ ^ 2 * D := by
    calc
      _ ≤ ∑ r : Fin ((N : ℕ) / 2), (r.val + 1 : ℝ) ^ (-p.val.2 - 2) *
          (4 * (k : ℝ) * (r.val + 1) * ‖u‖ ^ 2) := by
        apply sum_le_sum
        intro r _
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [Nat.cast_add, Nat.cast_one] using
          compensated_convolution_bound k m (r.val + 1) (by have := r.isLt; dsimp [N] at *; omega) u
      _ = (4 * (k : ℝ) * ‖u‖ ^ 2) *
          ∑ r : Fin ((N : ℕ) / 2), (1 + (r.val : ℝ)) ^ (-(p.val.2 + 1)) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro r _
        have hr : 0 < (r.val + 1 : ℝ) := by positivity
        have he : (r.val + 1 : ℝ) ^ (-p.val.2 - 2) * (r.val + 1) =
            (r.val + 1 : ℝ) ^ (-(p.val.2 + 1)) := by
          nth_rw 2 [← Real.rpow_one (r.val + 1 : ℝ)]
          rw [← Real.rpow_add hr]
          congr 1
          ring
        calc
          _ = 4 * (k : ℝ) * ‖u‖ ^ 2 *
              ((r.val + 1 : ℝ) ^ (-p.val.2 - 2) * (r.val + 1)) := by ring
          _ = _ := by rw [he]; congr 2; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [← Fin.sum_univ_eq_sum_range] using
          sum_range_one_add_rpow_le_tsum (show 1 < p.val.2 + 1 by linarith [p.property.2.1]) ((N : ℕ) / 2)
  calc
    _ = ∑ i, ∑ r, (∫ X, F i r X ∂gibbsMeasure p N) * q i r := by
      rw [integral_congr_ae (Eventually.of_forall hquad)]
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun r _ => (hFi i r).mul_const _)]
      apply sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun r _ => (hFi i r).mul_const _)]
      simp_rw [integral_mul_const]
    _ ≤ ∑ i, ∑ r, (B * (r.val + 1 : ℝ) ^ (-p.val.2 - 2)) * q i r :=
      sum_le_sum fun i _ => sum_le_sum fun r _ => mul_le_mul_of_nonneg_right (hFb i r) (sq_nonneg _)
    _ = B * ∑ r : Fin ((N : ℕ) / 2), (r.val + 1 : ℝ) ^ (-p.val.2 - 2) * ∑ i, q i r := by
      rw [sum_comm, mul_sum]
      apply sum_congr rfl
      intro r _
      rw [← mul_sum]
      ring
    _ ≤ B * (4 * (k : ℝ) * ‖u‖ ^ 2 * D) := mul_le_mul_of_nonneg_left hp hB.le
    _ ≤ _ := by nlinarith [sq_nonneg ‖u‖, mul_nonneg hD (sq_nonneg ‖u‖),
      mul_nonneg (show 0 ≤ (k : ℝ) by positivity) (sq_nonneg ‖u‖)]

/-- See the proof of Theorem 3 in the paper, the log-concavity
clause: every proper finite block has a normalized Borel log-concave
Lebesgue density, including the single exterior-gap case `m = 0`. -/
theorem finite_block_logConcave_density (p : Parameters) (k m : ℕ) (hk : 1 ≤ k) :
    ∃ f : EuclideanSpace ℝ (Fin k) → ℝ,
      Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∫⁻ x, ENNReal.ofReal (f x)) = 1 ∧
      ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) ∧
      (gibbsMeasure p (k + m).succPNat).map
        (fun X => WithLp.toLp 2 (fun i : Fin k => gap X i.val)) =
          volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
  classical
  let N := (k + m).succPNat
  let σ := Equiv.refl (Fin (k + m + 1))
  let Ω := AffineSimplex.chartDomain k ((k + m : ℕ) + 1)
  let ρ := ProperMarginalChart.chartDensity p k m σ
  let h := AffineFibre.fibreMass volume ρ
  have hhm : Measurable h := AffineFibre.measurable_fibreMass volume
    (ProperMarginalChart.measurable_chartDensity p k m σ)
  have hzero (x) (hx : x ∉ Ω) : h x = 0 := by
    have hz (z) : ρ (x, z) = 0 := by
      apply indicator_of_notMem
      intro hq
      exact hx (by
        change x ∈ AffineSimplex.chartDomain k ((k + m : ℕ) + 1)
        rw [← RetainedSimplex.fst_image_domain]
        exact ⟨(x, z), hq, rfl⟩)
    exact lintegral_eq_zero_of_ae_eq_zero (Eventually.of_forall hz)
  have hfin (x) : h x ≠ ⊤ := by
    by_cases hx : x ∈ Ω
    · exact (ProperMarginalChart.fibre_mass p k m hk σ hx).2
    · rw [hzero x hx]; exact ENNReal.zero_ne_top
  have hpos (x) : 0 < (h x).toReal ↔ x ∈ Ω := by
    constructor
    · intro hx
      by_contra hn
      rw [hzero x hn, ENNReal.toReal_zero] at hx
      exact hx.false
    · intro hx
      exact ENNReal.toReal_pos (ProperMarginalChart.fibre_mass p k m hk σ hx).1 (hfin x)
  let c : ℝ≥0∞ := (partitionFunction p N)⁻¹ *
    ENNReal.ofReal ((k + m + 1 : ℝ) ^ (k + m))⁻¹
  have hc0 : c ≠ 0 := by
    apply mul_ne_zero
    · exact ENNReal.inv_ne_zero.mpr (finiteModel_valid p N).2.2.2.ne
    · exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hct : c ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.inv_ne_top.mpr (finiteModel_valid p N).2.2.1.ne'
    · exact ENNReal.ofReal_ne_top
  have hc : 0 < c.toReal := ENNReal.toReal_pos hc0 hct
  let f := fun x => c.toReal * (h x).toReal
  have hfm : Measurable f := hhm.ennreal_toReal.const_mul _
  have hf0 (x) : 0 ≤ f x := mul_nonneg hc.le ENNReal.toReal_nonneg
  have hπ : (fun X : Riesz1.Configuration N =>
      (RetainedSimplex.coordinates k m σ (WithLp.toLp 2 (gapVector X))).1) =
        fun X => WithLp.toLp 2 (fun i : Fin k => gap X i.val) := by
    funext X
    ext i
    rfl
  have hlaw := ProperMarginalChart.map_gibbsMeasure_retained p k m hk σ
  rw [hπ, smul_smul, ← withDensity_smul] at hlaw
  · have he (x) : c * h x = ENNReal.ofReal (f x) := by
      rw [ENNReal.ofReal_mul hc.le, ENNReal.ofReal_toReal hct, ENNReal.ofReal_toReal (hfin x)]
    change (gibbsMeasure p N).map _ = volume.withDensity (fun x => c * h x) at hlaw
    simp_rw [he] at hlaw
    have hprob : IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (f x))) := by
      rw [← hlaw]
      have := gibbsMeasure_probability p N
      infer_instance
    refine ⟨f, hfm, hf0, ?_, ?_, hlaw⟩
    · have hh := hprob.measure_univ
      simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hh
    · obtain ⟨W, _, hv, _, _, hW⟩ := RemovableGapBarrier.selected_gap_barrier_convex p N (by dsimp [N]; omega)
      let H := fun q => p.val.1 * W (RetainedSimplex.chart k m ((k + m : ℕ) + 1) σ q)
      have hH : ConvexOn ℝ (RetainedSimplex.domain k m ((k + m : ℕ) + 1)) H := by
        refine ⟨RetainedSimplex.convex_domain _ _ _, ?_⟩
        intro x hx y hy a b ha hb hab
        have hS (x) (hx : x ∈ RetainedSimplex.domain k m ((k + m : ℕ) + 1)) :
            WithLp.ofLp (RetainedSimplex.chart k m ((k + m : ℕ) + 1) σ x) ∈ Riesz1.gapSimplex N := by
          have hh := (RetainedSimplex.chart_mem_simplex k m _ σ x).mpr hx
          exact ⟨hh.1, by simpa only [N, Nat.succPNat_coe, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using hh.2⟩
        change p.val.1 * W (RetainedSimplex.chart k m ((k + m : ℕ) + 1) σ (a • x + b • y)) ≤ _
        rw [RetainedSimplex.chart_convex_combination _ _ _ _ _ _ hab]
        exact (hW.smul p.property.1.le).2 (hS x hx) (hS y hy) ha hb hab
      have hconv := (convexLocalization (RetainedSimplex.isOpen_domain k m _)
        hH.1 (RetainedSimplex.isBounded_domain k m _) hH (fun _ => 0)).2
      rw [RetainedSimplex.fst_image_domain] at hconv
      have hρfin (q : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin m)) :
          ProperMarginalChart.chartDensity p k m σ q < ⊤ := by
        dsimp only [ProperMarginalChart.chartDensity]
        by_cases hq : q ∈ RetainedSimplex.domain k m ((k + m : ℕ) + 1)
        · rw [indicator_of_mem hq]
          dsimp only [ProperMarginalChart.density]
          split_ifs <;> finiteness
        · rw [indicator_of_notMem hq]
          exact ENNReal.zero_lt_top
      have hreal (x) : (h x).toReal = ∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity p k m σ (x, z)).toReal := by
        exact (integral_toReal ((ProperMarginalChart.measurable_chartDensity p k m σ).comp
          measurable_prodMk_left).aemeasurable
          (Eventually.of_forall fun z => hρfin (x, z))).symm
      have hposset : {x | 0 < f x} = Ω := by
        ext x
        exact (mul_pos_iff_of_pos_left hc).trans (hpos x)
      rw [hposset]
      have hlog : ConcaveOn ℝ Ω (fun x => Real.log ((h x).toReal)) := by
        apply hconv.neg.congr
        intro x _
        dsimp only [Pi.neg_apply]
        rw [hreal]
        simp_rw [MarginalCollision.internal_chart_density_real p k m σ hv]
        simp only [zero_sub, sub_zero, neg_neg, H, neg_mul]
      apply (hlog.add_const (Real.log c.toReal)).congr
      intro x hx
      dsimp only [f]
      dsimp only [Pi.add_apply]
      rw [Real.log_mul hc.ne' ((hpos x).mpr hx).ne']
      ring
  · exact hhm

/-- See the proof of Theorem 3 in the paper, the full finite-density
clause on the periodic laws of Subsection 6.3, for every `N > k`. This
identifies the density with the periodic extension and its gap coordinates rather than introducing a separate gap law. -/
theorem periodicGapLaw_block_logConcave_density (p : Parameters) (N : ℕ+)
    (k : ℕ) (hk : 1 ≤ k) (hNk : k < (N : ℕ)) :
    ∃ f : EuclideanSpace ℝ (Fin k) → ℝ,
      Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∫⁻ x, ENNReal.ofReal (f x)) = 1 ∧
      ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) ∧
      (periodicGapLaw p N).toMeasure.map
        (fun y : ℤ → Ioi (0 : ℝ) => WithLp.toLp 2 (fun i : Fin k => (y i.val : ℝ))) =
          volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, N = (k + m).succPNat :=
    ⟨(N : ℕ) - k - 1, PNat.eq (by simp only [Nat.succPNat_coe]; omega)⟩
  obtain ⟨f, hfm, hf0, hf1, hlog, hlaw⟩ := finite_block_logConcave_density p k m hk
  refine ⟨f, hfm, hf0, hf1, hlog, ?_⟩
  rw [periodicGapLaw_toMeasure, Measure.map_map]
  · exact hlaw
  · exact (WithLp.measurable_toLp 2 _).comp
      (Measurable.of_eval fun i => measurable_subtype_coe.comp (measurable_pi_apply _))
  · exact measurable_periodicGapSequence _

end Riesz2.GapNondegeneracy
