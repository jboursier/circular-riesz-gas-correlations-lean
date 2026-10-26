/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.PhysicalCollisionPart2
public import Riesz2.ToMathlib.AffinePullbackEstimates
public import Riesz2.Frozen.OfShort
public import Riesz1.Variance.ConvexificationPotential
import Riesz2.Sanity.SmoothCutoff
import Riesz2.Sanity.TiltedLaws

/-!
# Physical collision estimates in the particle quotient

Continuation of Appendix A. The derivative transport below is
independent of particle admissibility, which is a conclusion of the physical
verification rather than an input to the metric change.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators ContDiff

namespace Riesz2.PhysicalCollision

variable (N : ℕ+)

local notation "Y(" z ")" =>
  (WithLp.toLp 2 (fun i => 1 + (Subtype.val z) i) : EuclideanSpace ℝ (Fin (N : ℕ)))
local notation "T(" z ")" => AffineMetric.intrinsicParticleGapMap N z

/-- Internal Hessian form of the penalized physical estimates in Appendix A.
The quadratic bound is retained before taking a trace, so it can be transported. -/
theorem internal_penalized_hessian_bounds (p : Parameters) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (I : Finset (Fin (N : ℕ))) (twoSided : Bool) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧ ∀ z ∈ intrinsicGapDomain N,
        let V := fun w : gapTangentSpace N => p.val.1 * W Y(w) + p.val.1 *
          ∑ i ∈ I, (θ.val (a * (1 + w.val i)) +
            if twoSided then θ.val (a / (1 + w.val i)) else 0)
        ContDiffAt ℝ ∞ V z ∧ ∀ u : gapTangentSpace N,
          κ * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) z u u ∧
          fderiv ℝ (fderiv ℝ V) z u u ≤ C *
            (1 + (⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-p.val.2 - 2) +
              if twoSided then ∑ i ∈ I, (1 + z.val i)⁻¹ ^ 4 else 0) * ‖u‖ ^ 2 := by
  obtain ⟨W, hW, hval, κ, Cw, hκ, hCw, hH⟩ := unforced_hessian_bounds N p hN
  obtain ⟨Cp, hCp, hP⟩ := selected_penalty_hessian_upper N θ ha I twoSided
  obtain ⟨hPs, hPc⟩ := selected_penalty_smooth_convex N θ ha I twoSided
  let P : gapTangentSpace N → ℝ := fun w => ∑ i ∈ I,
    (θ.val (a * (1 + w.val i)) + if twoSided then θ.val (a / (1 + w.val i)) else 0)
  refine ⟨W, hW, hval, κ, Cw + p.val.1 * Cp, hκ,
    add_pos hCw (mul_pos p.property.1 hCp), fun z hz => ?_⟩
  let F : gapTangentSpace N → ℝ := fun w => p.val.1 * W Y(w)
  have hFs : ContDiffAt ℝ ∞ F z :=
    ((contDiffOn_const.mul (contDiffOn_intrinsic_pullback N hW)) z hz).contDiffAt
      ((AffineMetric.intrinsicGapDomain_isOpen N).mem_nhds hz)
  have hPz : ContDiffAt ℝ ∞ P z := (hPs z hz).contDiffAt
    ((AffineMetric.intrinsicGapDomain_isOpen N).mem_nhds hz)
  have hPβ : ContDiffAt ℝ ∞ (fun w => p.val.1 * P w) z := contDiffAt_const.mul hPz
  refine ⟨hFs.add hPβ, fun u => ?_⟩
  have hadd := internal_hessian_add (hFs.of_le (by simp)) (hPβ.of_le (by simp)) u u
  have hmul := internal_hessian_const_mul (hPz.of_le (by simp)) p.val.1 u u
  change fderiv ℝ (fderiv ℝ (fun w => F w + p.val.1 * P w)) z u u = _ at hadd
  change _ ≤ fderiv ℝ (fderiv ℝ (fun w => F w + p.val.1 * P w)) z u u ∧
    fderiv ℝ (fderiv ℝ (fun w => F w + p.val.1 * P w)) z u u ≤ _
  rw [hadd, hmul]
  have hn := Riesz1.fderiv_fderiv_nonneg_of_convexOn (AffineMetric.intrinsicGapDomain_isOpen N)
    (intrinsicGapDomain_convex N) hPc (hPs.of_le (by simp)) hz u
  have hp := mul_le_mul_of_nonneg_left (hP z hz u) p.property.1.le
  have hδ : 0 ≤ (⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-p.val.2 - 2) :=
    Real.rpow_nonneg (minimum_gap_pos N hz).le _
  have hq : 0 ≤ if twoSided then ∑ i ∈ I, (1 + z.val i)⁻¹ ^ 4 else 0 := by
    split_ifs
    · exact Finset.sum_nonneg (fun i _ => pow_nonneg (inv_nonneg.mpr (hz i).le) _)
    · exact le_rfl
  constructor
  · have h := mul_nonneg p.property.1.le hn
    linarith only [(hH z hz u).1, h]
  · have h₀ := mul_nonneg hCw.le (by linarith : 0 ≤ 1 +
        if twoSided then ∑ i ∈ I, (1 + z.val i)⁻¹ ^ 4 else 0)
    have h₁ := mul_nonneg (mul_nonneg p.property.1.le hCp.le) hδ
    have hh := mul_nonneg (add_nonneg h₀ h₁) (sq_nonneg ‖u‖)
    nlinarith only [(hH z hz u).2, hp, hh]

/-- See Appendix A of the paper: simultaneous gradient, trace and strict-curvature
estimates in the orthogonal particle quotient, for every active set and both
allowed penalties. The gap minimum and the active sums are those of the actual
cyclic gap map. -/
theorem particle_quotient_differential_estimates (p : Parameters) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (I : Finset (Fin (N : ℕ))) (twoSided : Bool) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ∃ c C κ : ℝ, 0 < c ∧ 0 < C ∧ 0 < κ ∧
      ∀ z : gapTangentSpace N, z.val ∈ particleChamber N →
        let V := fun w : gapTangentSpace N => p.val.1 * W Y(T(w)) + p.val.1 *
          ∑ i ∈ I, (θ.val (a * Riesz1.hsGap w.val i) +
            if twoSided then θ.val (a / Riesz1.hsGap w.val i) else 0)
        ContDiffAt ℝ ∞ V z ∧
        c * ((⨅ i : Fin (N : ℕ), Riesz1.hsGap z.val i) ^ (-p.val.2 - 1) +
          if twoSided then ∑ i ∈ I, (Riesz1.hsGap z.val i)⁻¹ ^ 3 else 0) - C ≤
            ‖gradient V z‖ ∧
        Laplacian.laplacian V z ≤ C *
          (1 + (⨅ i : Fin (N : ℕ), Riesz1.hsGap z.val i) ^ (-p.val.2 - 2) +
            if twoSided then ∑ i ∈ I, (Riesz1.hsGap z.val i)⁻¹ ^ 4 else 0) ∧
        ∀ u : gapTangentSpace N, κ * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) z u u := by
  obtain ⟨W, hW, hval, κ, Ch, hκ, hCh, hH⟩ :=
    internal_penalized_hessian_bounds N p hN θ ha I twoSided
  obtain ⟨Wg, _, hvalg, c, Cg, hc, hCg, hg⟩ := penalized_gradient_lower N p hN θ ha I twoSided
  let V : gapTangentSpace N → ℝ := fun w => p.val.1 * W Y(w) + p.val.1 *
    ∑ i ∈ I, (θ.val (a * (1 + w.val i)) + if twoSided then θ.val (a / (1 + w.val i)) else 0)
  let e := AffineMetric.gapLinearEquiv N
  let b := AffineMetric.gapOffset N
  let M := max ‖e.symm.toContinuousLinearMap‖ 1
  let L := max (‖e.toContinuousLinearMap‖ ^ 2) 1
  let D := (Module.finrank ℝ (gapTangentSpace N) : ℝ) * Ch * L
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨W, hW, hval, c / M, max (Cg / M) D, κ / M ^ 2,
    div_pos hc hM, lt_of_lt_of_le (div_pos hCg hM) (le_max_left _ _), by positivity,
    fun z hz => ?_⟩
  have hzT := (AffineMetric.intrinsicParticleGapMap_mem_iff N z).mpr hz
  have hez : e z + b = T(z) := (AffineMetric.intrinsicParticleGapMap_eq N z).symm
  have hez' : e.toContinuousLinearMap z + b = T(z) := hez
  have hgap (w : gapTangentSpace N) (i : Fin (N : ℕ)) :
      1 + T(w).val i = Riesz1.hsGap w.val i := by
    rw [AffineMetric.intrinsicParticleGapMap_apply]
    ring
  have hcomp : (fun w => V (e w + b)) =
      (fun w : gapTangentSpace N => p.val.1 * W Y(T(w)) + p.val.1 *
        ∑ i ∈ I, (θ.val (a * Riesz1.hsGap w.val i) +
          if twoSided then θ.val (a / Riesz1.hsGap w.val i) else 0)) := by
    funext w
    change V (AffineMetric.gapLinearEquiv N w + AffineMetric.gapOffset N) = _
    rw [← AffineMetric.intrinsicParticleGapMap_eq]
    simp only [V, hgap]
  have hVz : ContDiffAt ℝ ∞ V (e z + b) := by
    change ContDiffAt ℝ ∞ V (AffineMetric.gapLinearEquiv N z + AffineMetric.gapOffset N)
    rw [← AffineMetric.intrinsicParticleGapMap_eq]
    exact (hH _ hzT).1
  have hQ : ContDiffAt ℝ ∞ (fun w => V (e w + b)) z :=
    hVz.comp z ((e.contDiff.add contDiff_const).contDiffAt)
  rw [← hcomp]
  refine ⟨hQ, ?_, ?_, ?_⟩
  · have heq : (fun w : gapTangentSpace N => p.val.1 * Wg Y(w) + p.val.1 *
        ∑ i ∈ I, (θ.val (a * (1 + w.val i)) +
          if twoSided then θ.val (a / (1 + w.val i)) else 0)) =ᶠ[𝓝 T(z)] V := by
      filter_upwards [(AffineMetric.intrinsicGapDomain_isOpen N).mem_nhds hzT] with w hw
      have hy := PhysicalEnergy.simplex_subset_ambient N _ (intrinsic_chart_mem_simplex N hw)
      dsimp only [V]
      rw [hvalg ⟨Y(w), hy⟩, hval ⟨Y(w), hy⟩]
    have hG := hg _ hzT
    change _ ≤ ‖gradient _ T(z)‖ at hG
    rw [heq.gradient_eq] at hG
    have ht := AffinePullback.gradient_norm_le e b (hVz.differentiableAt (by simp))
    have htM := mul_le_mul_of_nonneg_right (le_max_left ‖e.symm.toContinuousLinearMap‖ 1)
      (norm_nonneg (gradient (fun w => V (e w + b)) z))
    rw [hez] at ht
    simp only [hgap] at hG
    have hh : (c * ((⨅ i : Fin (N : ℕ), Riesz1.hsGap z.val i) ^ (-p.val.2 - 1) +
        if twoSided then ∑ i ∈ I, (Riesz1.hsGap z.val i)⁻¹ ^ 3 else 0) - Cg) / M ≤
          ‖gradient (fun w => V (e w + b)) z‖ :=
      (div_le_iff₀ hM).mpr (by linarith only [hG, ht, htM])
    rw [sub_div, mul_div_right_comm] at hh
    linarith only [hh, le_max_left (Cg / M) D]
  · let S := 1 + (⨅ i : Fin (N : ℕ), Riesz1.hsGap z.val i) ^ (-p.val.2 - 2) +
      if twoSided then ∑ i ∈ I, (Riesz1.hsGap z.val i)⁻¹ ^ 4 else 0
    have hS : 0 ≤ S := by
      have hr := Real.rpow_nonneg (minimum_gap_pos N hzT).le (-p.val.2 - 2)
      have hsum : 0 ≤ if twoSided then ∑ i ∈ I, (Riesz1.hsGap z.val i)⁻¹ ^ 4 else 0 := by
        split_ifs
        · exact Finset.sum_nonneg (fun i _ =>
            pow_nonneg (inv_nonneg.mpr ((Riesz1.hsGap_mem_gapSimplex hz).1 i).le) _)
        · exact le_rfl
      simp only [hgap] at hr
      dsimp only [S]
      linarith only [hr, hsum]
    have hupper (u : gapTangentSpace N) := AffinePullback.hessian_upper
      e.toContinuousLinearMap b (hVz.of_le (by simp)) (mul_nonneg hCh.le hS)
      (by simpa only [hez', V, S, hgap] using
        (fun v => (hH _ hzT).2 v |>.2)) u
    have hlap := internal_laplacian_le (fun w => V (e w + b)) z _ hupper
    have hmax := mul_le_mul_of_nonneg_left (le_max_left (‖e.toContinuousLinearMap‖ ^ 2) 1)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ (gapTangentSpace N)))
        hCh.le) hS)
    have hmax' := mul_le_mul_of_nonneg_right (le_max_right (Cg / M) D) hS
    change Laplacian.laplacian (fun w => V (e w + b)) z ≤ _ * S
    dsimp only [D] at hmax'
    nlinarith only [hlap, hmax, hmax']
  · intro u
    exact AffinePullback.hessian_lower e b (hVz.of_le (by simp)) hκ.le hM
      (le_max_left _ _) (by simpa only [hez, V] using
        (fun v => (hH _ hzT).2 v |>.1)) u

/-- Collision absorption in the quotient, using the differential estimates above. -/
theorem internal_quotient_collision (hN : 2 ≤ (N : ℕ)) {s : ℝ} (hs : 0 < s)
    (I : Finset (Fin (N : ℕ))) (twoSided : Bool) (V : gapTangentSpace N → ℝ)
    {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hg : ∀ z : gapTangentSpace N, z.val ∈ particleChamber N →
      c * ((⨅ i : Fin (N : ℕ), Riesz1.hsGap z.val i) ^ (-s - 1) +
        if twoSided then ∑ i ∈ I, (Riesz1.hsGap z.val i)⁻¹ ^ 3 else 0) - C ≤ ‖gradient V z‖)
    (hΔ : ∀ z : gapTangentSpace N, z.val ∈ particleChamber N →
      Laplacian.laplacian V z ≤ C *
        (1 + (⨅ i : Fin (N : ℕ), Riesz1.hsGap z.val i) ^ (-s - 2) +
          if twoSided then ∑ i ∈ I, (Riesz1.hsGap z.val i)⁻¹ ^ 4 else 0)) :
    ∀ A K : ℝ, 0 < A → 0 < K → ∃ D : ℝ, 0 ≤ D ∧
      ∀ z : gapTangentSpace N, z.val ∈ particleChamber N →
        K * (Metric.infDist z.val (particleChamber N)ᶜ)⁻¹ ^ 2 - D ≤
          A * ‖gradient V z‖ ^ 2 - Laplacian.laplacian V z := by
  have := tangent_nontrivial N hN
  intro A K hA hK
  let α := A * c ^ 2 / 4
  have hα : 0 < α := by positivity
  obtain ⟨G, hG, hlip⟩ := AffinePolytope.exists_lipschitz (gapFace N)
  let M := max ‖(AffineMetric.gapLinearEquiv N).toContinuousLinearMap‖ 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨D₀, hD₀⟩ := RpowDomination.exists_bound hs hα hC.le
    (show 0 ≤ K * (G * M) ^ 2 by positivity)
  obtain ⟨D₁, hD₁⟩ := internal_inverse_sum_absorption I hα hC.le
  let E := D₀ + (if twoSided then D₁ else 0) + A * C ^ 2
  refine ⟨max E 0, le_max_right _ _, fun z hz => ?_⟩
  have hzT := (AffineMetric.intrinsicParticleGapMap_mem_iff N z).mpr hz
  have hgap (i : Fin (N : ℕ)) : 1 + T(z).val i = Riesz1.hsGap z.val i := by
    rw [AffineMetric.intrinsicParticleGapMap_apply]
    ring
  let δ := ⨅ i : Fin (N : ℕ), Riesz1.hsGap z.val i
  let X := δ ^ (-s - 1)
  let Y := if twoSided then ∑ i ∈ I, (Riesz1.hsGap z.val i)⁻¹ ^ 3 else 0
  let Z := if twoSided then ∑ i ∈ I, (Riesz1.hsGap z.val i)⁻¹ ^ 4 else 0
  have hδ : 0 < δ := by simpa only [hgap] using minimum_gap_pos N hzT
  have hX : 0 ≤ X := Real.rpow_nonneg hδ.le _
  have hY : 0 ≤ Y := by
    cases twoSided
    · exact le_rfl
    · exact Finset.sum_nonneg (fun i _ => pow_nonneg
        (inv_nonneg.mpr ((Riesz1.hsGap_mem_gapSimplex hz).1 i).le) _)
  have hinv : C * Z ≤ α * Y ^ 2 + if twoSided then D₁ else 0 := by
    cases twoSided
    · simp only [Y, Z, Bool.false_eq_true, ↓reduceIte, mul_zero, zero_pow,
        ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, add_zero, le_refl]
    · exact hD₁ (Riesz1.hsGap z.val) (fun i _ => (Riesz1.hsGap_mem_gapSimplex hz).1 i)
  have hd := AffinePolytope.div_le_infDist_frontier (gapFace N)
    (Ω := intrinsicGapDomain N) rfl (intrinsicGapDomain_bounded N) hG hlip hzT
  simp only [gapFace_apply, hgap] at hd
  rw [infDist_frontier_eq_infDist_compl (AffineMetric.intrinsicGapDomain_isOpen N) hzT
    (AffineMetric.intrinsicGapDomain_compl_nonempty hN)] at hd
  have hdist := (AffineMetric.intrinsicGap_boundary_distances hN z).1
  have hdistM := mul_le_mul_of_nonneg_right
    (le_max_left ‖(AffineMetric.gapLinearEquiv N).toContinuousLinearMap‖ 1)
    (Metric.infDist_nonneg : 0 ≤ Metric.infDist z.val (particleChamber N)ᶜ)
  have hδdp : δ / (G * M) ≤ Metric.infDist z.val (particleChamber N)ᶜ := by
    apply (div_le_iff₀ (mul_pos hG hM)).mpr
    have hh := (div_le_iff₀ hG).mp (hd.trans (hdist.trans hdistM))
    nlinarith only [hh]
  have hdsq := pow_le_pow_left₀ (div_pos hδ (mul_pos hG hM)).le hδdp 2
  have hdinv : (Metric.infDist z.val (particleChamber N)ᶜ)⁻¹ ^ 2 ≤
      (G * M) ^ 2 * (δ ^ 2)⁻¹ := by
    have hh := inv_anti₀ (pow_pos (div_pos hδ (mul_pos hG hM)) 2) hdsq
    have he : ((δ / (G * M)) ^ 2)⁻¹ = (G * M) ^ 2 * (δ ^ 2)⁻¹ := by field_simp
    simpa only [he, inv_pow] using hh
  have hdom := hD₀ δ hδ
  have hKdist := mul_le_mul_of_nonneg_left hdinv hK.le
  have hgrad := ElementaryBarriers.sq_half_sub_le_sq
    (show 0 ≤ c * (X + Y) from mul_nonneg hc.le (add_nonneg hX hY)) (hg z hz)
  have hAgrad := mul_le_mul_of_nonneg_left hgrad hA.le
  have hxy : 0 ≤ α * X * Y := mul_nonneg (mul_nonneg hα.le hX) hY
  have hlead : α * X ^ 2 + α * Y ^ 2 ≤ A * (c * (X + Y)) ^ 2 / 2 := by
    dsimp only [α] at hxy ⊢
    nlinarith only [hxy, sq_nonneg X, sq_nonneg Y,
      mul_nonneg (mul_nonneg hA.le (sq_nonneg c)) (sq_nonneg X),
      mul_nonneg (mul_nonneg hA.le (sq_nonneg c)) (sq_nonneg Y)]
  have htrace := hΔ z hz
  change Laplacian.laplacian V z ≤ C * (1 + δ ^ (-s - 2) + Z) at htrace
  change C * (1 + δ ^ (-s - 2)) + K * (G * M) ^ 2 * (δ ^ 2)⁻¹ ≤ α * X ^ 2 + D₀ at hdom
  have hE : E ≤ max E 0 := le_max_left _ _
  dsimp only [E] at hE
  linarith only [hdom, hinv, hKdist, hAgrad, hlead, htrace, hE]

/-- See Appendix A of the paper: strict quotient curvature and the collision criterion
for every positive coefficient and every allowed selected penalty. This proof
does not use `AdmissibleParticlePairs`. -/
theorem particle_quotient_collision_criterion (p : Parameters) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (I : Finset (Fin (N : ℕ))) (twoSided : Bool) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ∃ κ : ℝ, 0 < κ ∧
      (∀ z : gapTangentSpace N, z.val ∈ particleChamber N →
        let V := fun w : gapTangentSpace N => p.val.1 * W Y(T(w)) + p.val.1 *
          ∑ i ∈ I, (θ.val (a * Riesz1.hsGap w.val i) +
            if twoSided then θ.val (a / Riesz1.hsGap w.val i) else 0)
        ContDiffAt ℝ ∞ V z ∧ ∀ u : gapTangentSpace N,
          κ * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) z u u) ∧
      ∀ A K : ℝ, 0 < A → 0 < K → ∃ D : ℝ, 0 ≤ D ∧
        ∀ z : gapTangentSpace N, z.val ∈ particleChamber N →
          let V := fun w : gapTangentSpace N => p.val.1 * W Y(T(w)) + p.val.1 *
            ∑ i ∈ I, (θ.val (a * Riesz1.hsGap w.val i) +
              if twoSided then θ.val (a / Riesz1.hsGap w.val i) else 0)
          K * (Metric.infDist z.val (particleChamber N)ᶜ)⁻¹ ^ 2 - D ≤
            A * ‖gradient V z‖ ^ 2 - Laplacian.laplacian V z := by
  obtain ⟨W, hW, hval, c, C, κ, hc, hC, hκ, hest⟩ :=
    particle_quotient_differential_estimates N p hN θ ha I twoSided
  refine ⟨W, hW, hval, κ, hκ, fun z hz => ⟨(hest z hz).1, (hest z hz).2.2.2⟩, ?_⟩
  exact internal_quotient_collision N hN p.property.2.1 I twoSided _ hc hC
    (fun z hz => (hest z hz).2.1) (fun z hz => (hest z hz).2.2.1)

/-- The smallest microscopic gap is at most the mean gap one. -/
theorem minimum_gap_le_one (z : gapTangentSpace N) :
    (⨅ i : Fin (N : ℕ), 1 + z.val i) ≤ 1 := by
  have hmin (i : Fin (N : ℕ)) : (⨅ j : Fin (N : ℕ), 1 + z.val j) ≤ 1 + z.val i :=
    ciInf_le (Finite.bddBelow_range _) i
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hmin i)
  rw [Finset.sum_add_distrib, z.property] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, add_zero] at hsum
  exact (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < N)).mp (by simpa only [mul_one] using hsum)

/-- See Appendix A of the paper: the displayed unforced estimates in the orthogonal
particle quotient, with no additive one in the trace bound. -/
theorem unforced_particle_quotient_estimates (p : Parameters) (hN : 2 ≤ (N : ℕ)) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ z : gapTangentSpace N, z.val ∈ particleChamber N →
        let V := fun w : gapTangentSpace N => p.val.1 * W Y(T(w))
        c * (⨅ i : Fin (N : ℕ), Riesz1.hsGap z.val i) ^ (-p.val.2 - 1) - C ≤ ‖gradient V z‖ ∧
        Laplacian.laplacian V z ≤
          C * (⨅ i : Fin (N : ℕ), Riesz1.hsGap z.val i) ^ (-p.val.2 - 2) := by
  obtain ⟨θ⟩ := DefinitionSanity.physicalCutoff_nonempty
  obtain ⟨W, hW, hval, c, C, _, hc, hC, _, hest⟩ :=
    particle_quotient_differential_estimates N p hN θ (a := 1) zero_lt_one ∅ false
  refine ⟨W, hW, hval, c, 2 * C, hc, by positivity, fun z hz => ?_⟩
  have h := hest z hz
  simp only [Finset.sum_empty, mul_zero, add_zero, Bool.false_eq_true, ↓reduceIte] at h
  have hzT := (AffineMetric.intrinsicParticleGapMap_mem_iff N z).mpr hz
  have hgap (i : Fin (N : ℕ)) : 1 + T(z).val i = Riesz1.hsGap z.val i := by
    rw [AffineMetric.intrinsicParticleGapMap_apply]
    ring
  have hδ : 0 < ⨅ i : Fin (N : ℕ), Riesz1.hsGap z.val i := by
    simpa only [hgap] using minimum_gap_pos N hzT
  have hδ1 : (⨅ i : Fin (N : ℕ), Riesz1.hsGap z.val i) ≤ 1 := by
    simpa only [hgap] using minimum_gap_le_one N T(z)
  have hr := Real.rpow_le_rpow_of_nonpos hδ hδ1
    (by linarith [p.property.2.1] : -p.val.2 - 2 ≤ 0)
  rw [Real.one_rpow] at hr
  have hh := mul_le_mul_of_nonneg_left hr hC.le
  exact ⟨by linarith only [h.2.1, hC], by nlinarith only [h.2.2.1, hh]⟩

/-- See Appendix A of the paper: the displayed quotient estimates with the minimum
over a nonempty set of active inverse-penalty gaps. -/
theorem penalized_particle_quotient_minimum_estimates (p : Parameters) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (I : Finset (Fin (N : ℕ))) (hI : I.Nonempty) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ z : gapTangentSpace N, z.val ∈ particleChamber N →
        let d := ⨅ i : Fin (N : ℕ), Riesz1.hsGap z.val i
        let dI := ⨅ i : I, Riesz1.hsGap z.val i.val
        let V := fun w : gapTangentSpace N => p.val.1 * W Y(T(w)) + p.val.1 *
          ∑ i ∈ I, (θ.val (a * Riesz1.hsGap w.val i) + θ.val (a / Riesz1.hsGap w.val i))
        0 < dI ∧ c * (d ^ (-p.val.2 - 1) + dI⁻¹ ^ 3) - C ≤ ‖gradient V z‖ ∧
          Laplacian.laplacian V z ≤ C * (1 + d ^ (-p.val.2 - 2) + dI⁻¹ ^ 4) := by
  classical
  have : Nonempty I := hI.coe_sort
  obtain ⟨W, hW, hval, c, C, _, hc, hC, _, hest⟩ :=
    particle_quotient_differential_estimates N p hN θ ha I true
  let D := C * ((I.card : ℝ) + 1)
  have hDC : C ≤ D := by
    have hh := mul_nonneg hC.le (Nat.cast_nonneg (α := ℝ) I.card)
    dsimp only [D]
    nlinarith only [hh]
  refine ⟨W, hW, hval, c, D, hc, lt_of_lt_of_le hC hDC, fun z hz => ?_⟩
  dsimp only
  obtain ⟨j, hj⟩ := ElementaryBarriers.exists_iInf_eq_apply (fun i : I => Riesz1.hsGap z.val i.val)
  have hpos (i : Fin (N : ℕ)) := (Riesz1.hsGap_mem_gapSimplex hz).1 i
  have hdI : 0 < ⨅ i : I, Riesz1.hsGap z.val i.val := by rw [hj]; exact hpos j.val
  have hsmall : (⨅ i : I, Riesz1.hsGap z.val i.val)⁻¹ ^ 3 ≤
      ∑ i ∈ I, (Riesz1.hsGap z.val i)⁻¹ ^ 3 := by
    rw [hj]
    exact Finset.single_le_sum (fun i _ => pow_nonneg (inv_nonneg.mpr (hpos i).le) _) j.property
  have hsum : (∑ i ∈ I, (Riesz1.hsGap z.val i)⁻¹ ^ 4) ≤
      (I.card : ℝ) * (⨅ i : I, Riesz1.hsGap z.val i.val)⁻¹ ^ 4 := by
    calc
      _ ≤ ∑ _i ∈ I, (⨅ i : I, Riesz1.hsGap z.val i.val)⁻¹ ^ 4 := by
        apply Finset.sum_le_sum
        intro i hi
        have hle := ciInf_le (Finite.bddBelow_range (fun i : I => Riesz1.hsGap z.val i.val)) ⟨i, hi⟩
        exact pow_le_pow_left₀ (inv_nonneg.mpr (hpos i).le) (inv_anti₀ hdI hle) 4
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have h := hest z hz
  simp only [↓reduceIte] at h
  refine ⟨hdI, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_left hsmall hc.le
    linarith only [h.2.1, hh, hDC]
  · have hδ : 0 ≤ (⨅ i : Fin (N : ℕ), Riesz1.hsGap z.val i) ^ (-p.val.2 - 2) := by
      exact Real.rpow_nonneg (le_of_lt (by
        obtain ⟨i, hi⟩ := ElementaryBarriers.exists_iInf_eq_apply (Riesz1.hsGap z.val)
        rw [hi]
        exact hpos i)) _
    have hq : 0 ≤ (⨅ i : I, Riesz1.hsGap z.val i.val)⁻¹ ^ 4 := by positivity
    have h₀ := mul_le_mul_of_nonneg_left hsum hC.le
    have h₁ := mul_nonneg (Nat.cast_nonneg (α := ℝ) I.card)
      (by linarith : 0 ≤ 1 + (⨅ i : Fin (N : ℕ), Riesz1.hsGap z.val i) ^ (-p.val.2 - 2))
    dsimp only [D]
    have hh := mul_nonneg hC.le h₁
    nlinarith only [h.2.2.1, h₀, hh, mul_nonneg hC.le hq]

/-- The unordered nearest pair carrying a cyclic gap. The last gap is assigned
to the reflected pair `(0,N-1)`. At `N=2` the two gaps have the same pair. -/
def nearestGapPair (hN : 2 ≤ (N : ℕ)) (i : Fin (N : ℕ)) :
    {p : Fin (N : ℕ) × Fin (N : ℕ) // p.1 < p.2} :=
  if hi : i.val + 1 < (N : ℕ) then
    ⟨(i, ⟨i.val + 1, hi⟩), by change i.val < i.val + 1; omega⟩
  else ⟨(⟨0, N.pos⟩, i), by change 0 < i.val; have := i.isLt; omega⟩

/-- The forward or reflected separation of the assigned pair is the actual
microscopic cyclic gap, including the last gap. -/
theorem nearestGapPair_gap (hN : 2 ≤ (N : ℕ)) (i : Fin (N : ℕ))
    (x : EuclideanSpace ℝ (Fin (N : ℕ))) :
    (if i.val + 1 < (N : ℕ) then
        (N : ℝ) * (x (nearestGapPair N hN i).val.2 - x (nearestGapPair N hN i).val.1)
      else (N : ℝ) * (1 -
        (x (nearestGapPair N hN i).val.2 - x (nearestGapPair N hN i).val.1))) =
      Riesz1.hsGap x i := by
  by_cases hi : i.val + 1 < (N : ℕ)
  · simp only [hi, ↓reduceIte, nearestGapPair, ↓reduceDIte, Riesz1.hsGap,
      Riesz1.hsCyclicLift_nat x hi, Riesz1.hsCyclicLift_nat x i.isLt]
  · have heq : i.val + 1 = (N : ℕ) := by have := i.isLt; omega
    simp only [nearestGapPair, Riesz1.hsGap, heq, lt_self_iff_false, ↓reduceIte, ↓reduceDIte,
      Riesz1.hsCyclicLift_card, Riesz1.hsCyclicLift_nat x i.isLt]
    ring

/-- Half of each selected gap penalty assigned to its unordered particle pair.
The incidence sum adds both contributions at `N=2`, as required by the energy
convention `H = 2 ∑ χ`. Values are the displayed scalar expressions on all of ℝ. -/
def selectedPairPenalty (hN : 2 ≤ (N : ℕ)) (β : ℝ) (θ : PhysicalCutoff)
    (a : ℝ) (I : Finset (Fin (N : ℕ))) (twoSided : Bool)
    (i j : Fin (N : ℕ)) (r : ℝ) : ℝ :=
  β / 2 * ∑ k ∈ I with (nearestGapPair N hN k).val = (i, j),
    let d := if k.val + 1 < (N : ℕ) then (N : ℝ) * r else (N : ℝ) * (1 - r)
    θ.val (a * d) + if twoSided then θ.val (a / d) else 0

/-- See Appendix A of the paper, the exact nearest-pair penalty allocation. Every
selected cyclic gap occurs once before the outer factor two. No gap is lost
when the first and last pairs coincide. -/
theorem selectedPairPenalty_energy (hN : 2 ≤ (N : ℕ)) (β : ℝ) (θ : PhysicalCutoff)
    (a : ℝ) (I : Finset (Fin (N : ℕ))) (twoSided : Bool)
    (x : EuclideanSpace ℝ (Fin (N : ℕ))) :
    particlePairEnergy (fun p => selectedPairPenalty N hN β θ a I twoSided p.val.1 p.val.2) x =
      β * ∑ k ∈ I, (θ.val (a * Riesz1.hsGap x k) +
        if twoSided then θ.val (a / Riesz1.hsGap x k) else 0) := by
  classical
  let f := fun (k : Fin (N : ℕ)) (r : ℝ) =>
    let d := if k.val + 1 < (N : ℕ) then (N : ℝ) * r else (N : ℝ) * (1 - r)
    θ.val (a * d) + if twoSided then θ.val (a / d) else 0
  have he : (∑ p : {p : Fin (N : ℕ) × Fin (N : ℕ) // p.1 < p.2},
      ∑ k ∈ I with (nearestGapPair N hN k).val = p.val, f k (x p.val.2 - x p.val.1)) =
      ∑ k ∈ I, f k (x (nearestGapPair N hN k).val.2 - x (nearestGapPair N hN k).val.1) := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_eq_single (nearestGapPair N hN k)]
    · simp
    · intro q _ hq
      have hne : (nearestGapPair N hN k).val ≠ q.val := by
        intro he
        exact hq (Subtype.ext he.symm)
      simp only [hne, ↓reduceIte]
    · simp
  unfold particlePairEnergy selectedPairPenalty
  change 2 * (∑ p : {p : Fin (N : ℕ) × Fin (N : ℕ) // p.1 < p.2},
    β / 2 * ∑ k ∈ I with (nearestGapPair N hN k).val = p.val,
      f k (x p.val.2 - x p.val.1)) = _
  rw [← Finset.mul_sum, he]
  simp only [f, nearestGapPair_gap]
  ring

/-- Internal scalar regularity of the allowed selected gap penalty. -/
theorem internal_scalar_penalty_regular (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (twoSided : Bool) :
    ContDiffOn ℝ ∞ (fun d : ℝ => θ.val (a * d) + if twoSided then θ.val (a / d) else 0)
      (Ioi 0) ∧
    ConvexOn ℝ (Ioi (0 : ℝ))
      (fun d : ℝ => θ.val (a * d) + if twoSided then θ.val (a / d) else 0) := by
  constructor
  · intro d hd
    have hu : ContDiffAt ℝ ∞ (fun d : ℝ => θ.val (a * d)) d :=
      (cutoff_contDiffAt θ (mul_pos ha hd)).comp d (contDiffAt_const.mul contDiffAt_id)
    have hi : ContDiffAt ℝ ∞ (fun d : ℝ => θ.val (a / d)) d :=
      (cutoff_contDiffAt θ (div_pos ha hd)).comp d
        (contDiffAt_const.div contDiffAt_id (ne_of_gt hd))
    cases twoSided
    · simpa only [Bool.false_eq_true, ↓reduceIte, add_zero] using hu.contDiffWithinAt
    · simpa only [↓reduceIte] using (hu.add hi).contDiffWithinAt
  · cases twoSided
    · simpa only [Bool.false_eq_true, ↓reduceIte, add_zero] using upper_penalty_convex θ ha
    · exact (upper_penalty_convex θ ha).add (inverse_penalty_convex θ ha)

/-- See Appendix A of the paper: each allocated unordered-pair penalty is smooth
and convex on the full separation interval. Incidence multiplicities are summed. -/
theorem selectedPairPenalty_regular (hN : 2 ≤ (N : ℕ)) {β : ℝ} (hβ : 0 < β)
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (I : Finset (Fin (N : ℕ))) (twoSided : Bool) (i j : Fin (N : ℕ)) :
    ContDiffOn ℝ ∞ (selectedPairPenalty N hN β θ a I twoSided i j) (Ioo 0 1) ∧
    ConvexOn ℝ (Ioo (0 : ℝ) 1) (selectedPairPenalty N hN β θ a I twoSided i j) := by
  classical
  let S := I.filter (fun k => (nearestGapPair N hN k).val = (i, j))
  let f : ℝ → ℝ := fun d => θ.val (a * d) + if twoSided then θ.val (a / d) else 0
  have hreg := internal_scalar_penalty_regular θ ha twoSided
  let l : Fin (N : ℕ) → ℝ →ᵃ[ℝ] ℝ := fun k =>
    if k.val + 1 < (N : ℕ) then AffineMap.lineMap 0 (N : ℝ)
      else AffineMap.lineMap (N : ℝ) 0
  have hl (k : Fin (N : ℕ)) (r : ℝ) : l k r =
      if k.val + 1 < (N : ℕ) then (N : ℝ) * r else (N : ℝ) * (1 - r) := by
    dsimp only [l]
    split_ifs <;> simp only [AffineMap.lineMap_apply_ring] <;> ring
  have hlpos (k : Fin (N : ℕ)) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) : 0 < l k r := by
    rw [hl]
    split_ifs
    · exact mul_pos (by positivity) hr.1
    · exact mul_pos (by positivity) (sub_pos.mpr hr.2)
  have hlc (k : Fin (N : ℕ)) : ContDiff ℝ ∞ (l k) := by
    dsimp only [l]
    split_ifs <;> simp only [AffineMap.coe_lineMap, vsub_eq_sub, vadd_eq_add, smul_eq_mul] <;> fun_prop
  have he : selectedPairPenalty N hN β θ a I twoSided i j =
      fun r => β / 2 * ∑ k ∈ S, f (l k r) := by
    funext r
    simp only [selectedPairPenalty, S, f, hl]
  rw [he]
  constructor
  · exact contDiffOn_const.mul (ContDiffOn.sum (fun k _ =>
      (hreg.1.comp (hlc k).contDiffOn (fun r hr => hlpos k hr))))
  · apply ConvexOn.smul (by positivity : 0 ≤ β / 2)
    have hc (k : Fin (N : ℕ)) : ConvexOn ℝ (Ioo (0 : ℝ) 1) (fun r => f (l k r)) :=
      (hreg.2.comp_affineMap (l k)).subset (fun r hr => hlpos k hr) (convex_Ioo _ _)
    refine ⟨convex_Ioo _ _, fun x hx y hy α γ hα hγ hsum => ?_⟩
    have ht := Finset.sum_le_sum (s := S) (fun k _ => (hc k).2 hx hy hα hγ hsum)
    simpa only [smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum] using ht

/-- The actual short-range image series supplies smooth, strictly convex pair
data with both endpoint singularities. It uses the existing short kernel. -/
theorem short_physical_base_pairs (s : ShortExponent) {β : ℝ} (hβ : 0 < β) :
    ∃ χ : Riesz1.HsPairPotentials N
        (β * (N : ℝ) ^ (-s.val) * (s.val * (s.val + 1))),
      (∀ i j r, χ.potential i j r = β * (N : ℝ) ^ (-s.val) *
        ∑' k : ℤ, |(k : ℝ) + r| ^ (-s.val)) ∧
      ∀ X : Riesz1.Configuration N,
        Riesz1.hsPairExpression χ (WithLp.toLp 2 X.val) = β * shortEnergy s X := by
  let F : ℝ → ℝ := fun r => ∑' k : ℤ, |(k : ℝ) + r| ^ (-s.val)
  let B := β * (N : ℝ) ^ (-s.val)
  have hB : 0 < B := mul_pos hβ (Real.rpow_pos_of_pos (by positivity) _)
  have hs : 0 < s.val := lt_trans zero_lt_one s.property
  have hnon {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) : (r : UnitAddCircle) ≠ 0 :=
    Riesz1.coe_ne_zero_of_mem_Ioo_int 0 r (by simpa using hr)
  have hcurv {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
      s.val * (s.val + 1) ≤ deriv (deriv F) r := by
    let p := ofShort ⟨1, zero_lt_one⟩ s
    have hb := PhysicalEnergy.intervalCoefficient_lower p 1 ⟨r, by simpa using hr⟩
    have hnot : ¬s.val < 1 := not_lt.mpr s.property.le
    have hbc : s.val * (s.val + 1) * r ^ (-s.val - 2) ≤ deriv (deriv F) r := by
      simpa only [PhysicalEnergy.intervalCoefficient, PhysicalEnergy.kernelDerivative,
        PhysicalEnergy.scaledSeparation, p, ofShort, hnot, ↓reduceDIte, PNat.val_ofNat,
        Nat.cast_one, Real.one_rpow, one_mul, div_one, iteratedDeriv_succ,
        iteratedDeriv_zero] using hb
    have hrpow := Real.rpow_le_rpow_of_nonpos hr.1 hr.2.le (by linarith : -s.val - 2 ≤ 0)
    rw [Real.one_rpow] at hrpow
    exact (le_mul_of_one_le_right (by positivity : 0 ≤ s.val * (s.val + 1)) hrpow).trans hbc
  have hleft : Tendsto F (𝓝[>] 0) atTop := by
    apply (tendsto_short_images_collision s).mono_left
    have he : ∀ᶠ (r : ℝ) in 𝓝[>] (0 : ℝ), (r : UnitAddCircle) ≠ 0 := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with r hr0 hr1
      exact hnon ⟨hr0, hr1⟩
    exact le_inf nhdsWithin_le_nhds (le_principal_iff.mpr he)
  have hreflect (r : ℝ) : F (1 - r) = F r := by
    calc
      F (1 - r) = F (-r + 1) := by congr 1; ring
      _ = F (-r) := short_images_periodic s (-r)
      _ = F r := short_images_even s r
  have hright : Tendsto F (𝓝[<] 1) atTop := by
    have hm : Tendsto (fun r : ℝ => 1 - r) (𝓝[<] 1) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, ?_⟩
      · have hc : Continuous (fun r : ℝ => 1 - r) := continuous_const.sub continuous_id
        simpa only [sub_self] using (hc.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact sub_pos.mpr hr
    simpa only [Function.comp_def, hreflect] using hleft.comp hm
  let χ : Riesz1.HsPairPotentials N (B * (s.val * (s.val + 1))) :=
    { potential := fun _ _ r => B * F r
      symmetric := fun _ _ => rfl
      smooth := fun _ _ _ => contDiffOn_const.mul ((contDiffOn_short_images s).mono
        (fun _ hr => hnon hr))
      curvature := fun _ _ _ r hr => by
        rw [deriv_const_mul_field', deriv_const_mul_field]
        exact mul_le_mul_of_nonneg_left (hcurv hr) hB.le
      leftBoundary := fun _ _ _ => hleft.const_mul_atTop hB
      rightBoundary := fun _ _ _ => hright.const_mul_atTop hB }
  refine ⟨χ, fun _ _ _ => rfl, fun X => ?_⟩
  have hsym (i j : Fin (N : ℕ)) : F (X.val j - X.val i) = F (X.val i - X.val j) := by
    rw [show X.val j - X.val i = -(X.val i - X.val j) by ring]
    exact short_images_even s _
  have he : shortEnergy s X = (N : ℝ) ^ (-s.val) *
      ∑ i : Fin (N : ℕ), ∑ j ∈ Finset.univ.erase i, F (X.val i - X.val j) := by
    unfold shortEnergy
    simp_rw [shortKernelLift_eq_tsum_rpow]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact (Finset.sum_subtype (Finset.univ.erase i) (p := fun j => j ≠ i) (by simp)
      (fun j => F (X.val i - X.val j))).symm
  rw [he, Riesz1.sum_erase_eq_two_mul_sum_lt _ _ hsym]
  simp only [Riesz1.hsPairExpression, χ, ← Finset.mul_sum]
  have hsum : (∑ i : Fin (N : ℕ), ∑ j ∈ Finset.univ.filter (i < ·), F (X.val j - X.val i)) =
      ∑ i : Fin (N : ℕ), ∑ j ∈ Finset.univ.filter (i < ·), F (X.val i - X.val j) := by
    simp_rw [hsym]
  rw [hsum]
  dsimp only [B]
  ring

/-- See Appendix A of the paper: both physical exponent regimes have pair data, with the temperature and ordered-pair normalization of the law. -/
theorem physical_base_pairs (p : Parameters) :
    ∃ χ : Riesz1.HsPairPotentials N
        (p.val.1 * (N : ℝ) ^ (-p.val.2) * (p.val.2 * (p.val.2 + 1))),
      ∀ X : Riesz1.Configuration N,
        Riesz1.hsPairExpression χ (WithLp.toLp 2 X.val) = p.val.1 * energy p X := by
  by_cases hs : p.val.2 < 1
  · refine ⟨Riesz1.hsRieszPairPotentials N p.val.1 p.property.1
      ⟨p.val.2, p.property.2.1, hs⟩, fun X => ?_⟩
    simp only [energy, hs, ↓reduceDIte]
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n.succPNat :=
      ⟨N.natPred, (PNat.succPNat_natPred N).symm⟩
    exact (Riesz1.beta_energy_eq_pairExpression _ p.property.1 _ n X).symm
  · obtain ⟨χ, _, hχ⟩ := short_physical_base_pairs N
      ⟨p.val.2, lt_of_le_of_ne (le_of_not_gt hs) (Ne.symm p.property.2.2)⟩ p.property.1
    refine ⟨χ, fun X => ?_⟩
    simpa only [energy, hs, ↓reduceDIte] using hχ X

/-- Restriction of library pair data to the unordered-pair index type.
This is an index adapter. It changes no pair function. -/
def upperPairs {c : ℝ} (χ : Riesz1.HsPairPotentials N c) : ParticlePairData N :=
  fun p => χ.potential p.val.1 p.val.2

/-- The index adapter preserves the ambient energy on its whole carrier. -/
theorem upperPairs_energy {c : ℝ} (χ : Riesz1.HsPairPotentials N c) :
    particlePairEnergy (upperPairs N χ) = Riesz1.hsPairExpression χ := by
  funext x
  unfold particlePairEnergy upperPairs Riesz1.hsPairExpression
  rw [AffineMetric.sum_pairs_eval (fun i j => χ.potential i j (x j - x i))]

/-- See Appendix A of the paper: add all selected nearest-gap penalties to the
actual physical pair family, preserving smoothness, strict pair curvature,
and both endpoint singularities in both exponent regimes. -/
theorem physical_penalized_pairs (p : Parameters) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (I : Finset (Fin (N : ℕ))) (twoSided : Bool) :
    ∃ χ : Riesz1.HsPairPotentials N
        (p.val.1 * (N : ℝ) ^ (-p.val.2) * (p.val.2 * (p.val.2 + 1))),
      ∀ X : Riesz1.Configuration N,
        Riesz1.hsPairExpression χ (WithLp.toLp 2 X.val) =
          p.val.1 * energy p X + p.val.1 * ∑ k ∈ I,
            (θ.val (a * gapVector X k) + if twoSided then θ.val (a / gapVector X k) else 0) := by
  obtain ⟨χ, hχ⟩ := physical_base_pairs N p
  let ψ := selectedPairPenalty N hN p.val.1 θ a I twoSided
  have hψ i j (_ : i < j) := (selectedPairPenalty_regular N hN p.property.1 θ ha I twoSided i j).1
  have hcψ i j (_ : i < j) := (selectedPairPenalty_regular N hN p.property.1 θ ha I twoSided i j).2
  refine ⟨χ.addConvex ψ hψ hcψ, fun X => ?_⟩
  rw [Riesz1.hsPairExpression_addConvex, hχ]
  have hpen := selectedPairPenalty_energy N hN p.val.1 θ a I twoSided (WithLp.toLp 2 X.val)
  unfold particlePairEnergy at hpen
  change 2 * (∑ q : {q : Fin (N : ℕ) × Fin (N : ℕ) // q.1 < q.2},
    ψ q.val.1 q.val.2 ((WithLp.toLp 2 X.val) q.val.2 - (WithLp.toLp 2 X.val) q.val.1)) = _ at hpen
  rw [AffineMetric.sum_pairs_eval (fun i j => ψ i j
    ((WithLp.toLp 2 X.val) j - (WithLp.toLp 2 X.val) i))] at hpen
  rw [hpen]
  rw [Riesz1.hsGap_eq_gapVector]
  rfl

/-- Internal identity on the quotient chamber, obtained from actual configurations
by the library's canonical representative. -/
theorem internal_pairs_quotient_realization (p : Parameters) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) (a : ℝ) (I : Finset (Fin (N : ℕ))) (twoSided : Bool)
    {c : ℝ} (χ : Riesz1.HsPairPotentials N c)
    (hχ : ∀ X : Riesz1.Configuration N,
      Riesz1.hsPairExpression χ (WithLp.toLp 2 X.val) =
        p.val.1 * energy p X + p.val.1 * ∑ k ∈ I,
          (θ.val (a * gapVector X k) + if twoSided then θ.val (a / gapVector X k) else 0))
    (W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ)
    (hval : ∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
      W y.val = physicalAmbientGapEnergy p N y)
    (z : gapTangentSpace N) (hz : z.val ∈ particleChamber N) :
    Riesz1.hsPairExpression χ z.val = p.val.1 * W Y(T(z)) + p.val.1 *
      ∑ k ∈ I, (θ.val (a * Riesz1.hsGap z.val k) +
        if twoSided then θ.val (a / Riesz1.hsGap z.val k) else 0) := by
  let X := Riesz1.hsRepresentative ⟨z.val, hz⟩
  have hrep : WithLp.toLp 2 X.val =
      Riesz1.hsTranslate (-(⌊z.val ⟨0, N.pos⟩⌋ : ℤ)) z.val := by
    ext i
    simp only [X, Riesz1.hsRepresentative_apply, Riesz1.hsTranslate_apply]
    rfl
  have hgap : gapVector X = Riesz1.hsGap z.val := by
    change Riesz1.gapVector X = _
    rw [← Riesz1.hsGap_eq_gapVector, hrep, Riesz1.hsGap_translate]
  have hy : Y(T(z)) = WithLp.toLp 2 (gapVector X) := by
    ext i
    rw [hgap]
    change 1 + T(z).val i = Riesz1.hsGap z.val i
    rw [AffineMetric.intrinsicParticleGapMap_apply]
    ring
  rw [hy, hval ⟨_, GapChart.gapVector_mem_gapAmbientDomain X⟩,
    GapChart.physicalAmbientGapEnergy_gapVector p N hN X, ← hgap,
    ← hχ, hrep, Riesz1.hsPairExpression_translate]

/-- Internal index/metric bridge: the quotient gradient is the same tangent
vector as the ambient gradient. Only the library's pair regularity is used. -/
theorem internal_library_quotient_gradient {c : ℝ} (χ : Riesz1.HsPairPotentials N c)
    {z : gapTangentSpace N} (hz : z.val ∈ particleChamber N) :
    (gradient (fun w : gapTangentSpace N => Riesz1.hsPairExpression χ w.val) z).val =
      gradient (Riesz1.hsPairExpression χ) z.val := by
  let g : gapTangentSpace N :=
    ⟨gradient (Riesz1.hsPairExpression χ) z.val, Riesz1.boundaryCore_gradient_sum χ hz⟩
  have he : gradient (fun w : gapTangentSpace N => Riesz1.hsPairExpression χ w.val) z = g := by
    apply ext_inner_right ℝ
    intro u
    rw [inner_gradient_left]
    have hd := ((Riesz1.hasFDerivAt_hsPairExpression χ hz).differentiableAt.hasFDerivAt.comp z
      (gapTangentSpace N).subtypeL.hasFDerivAt).fderiv
    simp only [Function.comp_def] at hd
    rw [hd]
    change fderiv ℝ (Riesz1.hsPairExpression χ) z.val u.val = inner ℝ g.val u.val
    exact inner_gradient_left.symm
  exact congrArg Subtype.val he

/-- Internal index/metric bridge: the rotation direction contributes zero to
the particle trace, so the quotient trace equals the ambient trace. -/
theorem internal_library_quotient_laplacian {c : ℝ} (χ : Riesz1.HsPairPotentials N c)
    {z : gapTangentSpace N} (hz : z.val ∈ particleChamber N) :
    Laplacian.laplacian (fun w : gapTangentSpace N => Riesz1.hsPairExpression χ w.val) z =
      Laplacian.laplacian (Riesz1.hsPairExpression χ) z.val := by
  let b := stdOrthonormalBasis ℝ (gapTangentSpace N)
  have hsmooth := (Riesz1.hsPairExpression_contDiffOn χ).contDiffAt
    ((Riesz1.isOpen_hsChamber N).mem_nhds hz)
  have hh (u : gapTangentSpace N) :
      fderiv ℝ (fderiv ℝ (fun w : gapTangentSpace N => Riesz1.hsPairExpression χ w.val)) z u u =
        fderiv ℝ (fderiv ℝ (Riesz1.hsPairExpression χ)) z.val u.val u.val := by
    simpa only [Submodule.subtypeL_apply, add_zero] using
      AffineMetricTransport.hessian_comp_affine (gapTangentSpace N).subtypeL 0
        (by simpa only [Submodule.subtypeL_apply, add_zero] using
          hsmooth.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ (⊤ : ℕ∞))) u u
  have hparseval (i j : Fin (N : ℕ)) (hij : i < j) :
      (∑ k, ((b k).val j - (b k).val i) ^ 2) = 2 := by
    obtain ⟨r, hrnorm, hr⟩ := AffineMetric.exists_pairSeparationVector i j hij
    calc
      _ = ∑ k, inner ℝ r (b k) ^ 2 := by simp only [hr]
      _ = ‖r‖ ^ 2 := b.sum_sq_inner_left r
      _ = 2 := hrnorm
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b,
    Riesz1.laplacian_hsPairExpression χ hz]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hh,
    Riesz1.hessian_hsPairExpression_self χ hz]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ.filter _), ← Finset.mul_sum]
  have he : (∑ i : Fin (N : ℕ), ∑ j ∈ Finset.univ.filter (i < ·),
      deriv (deriv (χ.potential i j)) (z.val j - z.val i) *
        ∑ k, ((b k).val j - (b k).val i) ^ 2) =
      ∑ i : Fin (N : ℕ), ∑ j ∈ Finset.univ.filter (i < ·),
        deriv (deriv (χ.potential i j)) (z.val j - z.val i) * 2 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j hj
    rw [hparseval i j (Finset.mem_filter.mp hj).2]
  rw [he]
  simp only [← Finset.sum_mul]
  ring

/-- Internal translation bridge, before collision admissibility is known. -/
theorem internal_library_centering {c : ℝ} (χ : Riesz1.HsPairPotentials N c)
    {x : EuclideanSpace ℝ (Fin (N : ℕ))} (hx : x ∈ particleChamber N) :
    gradient (Riesz1.hsPairExpression χ) (centeredGapChart N x).val =
        gradient (Riesz1.hsPairExpression χ) x ∧
      Laplacian.laplacian (Riesz1.hsPairExpression χ) (centeredGapChart N x).val =
        Laplacian.laplacian (Riesz1.hsPairExpression χ) x := by
  have hz := (AffineMetric.centeredGapChart_mem_chamber_iff x).mpr hx
  have hsep (i j : Fin (N : ℕ)) :
      (centeredGapChart N x).val j - (centeredGapChart N x).val i = x j - x i := by
    change (x j - (∑ k, x k) / N) - (x i - (∑ k, x k) / N) = _
    ring
  constructor
  · unfold gradient
    congr 1
    rw [(Riesz1.hasFDerivAt_hsPairExpression χ hz).fderiv,
      (Riesz1.hasFDerivAt_hsPairExpression χ hx).fderiv]
    simp only [Riesz1.hsPairGradient, hsep]
  · rw [Riesz1.laplacian_hsPairExpression χ hz, Riesz1.laplacian_hsPairExpression χ hx]
    simp only [hsep]

/-- See Appendix A of the paper: admissible particle pairs realizing
every allowed physical potential. Pair curvature, both endpoint singularities,
and the collision criterion for every positive coefficient are all conclusions. -/
theorem admissible_physical_particle_pairs (p : Parameters) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (I : Finset (Fin (N : ℕ))) (twoSided : Bool) :
    ∃ c : ℝ, 0 < c ∧ ∃ χ : ParticlePairData N,
      AdmissibleParticlePairs hN χ c ∧
      ∀ X : Riesz1.Configuration N,
        particlePairEnergy χ (WithLp.toLp 2 X.val) =
          p.val.1 * energy p X + p.val.1 * ∑ k ∈ I,
            (θ.val (a * gapVector X k) + if twoSided then θ.val (a / gapVector X k) else 0) := by
  obtain ⟨χ, hχ⟩ := physical_penalized_pairs N p hN θ ha I twoSided
  obtain ⟨W, _, hval, _, _, _, hcoll⟩ := particle_quotient_collision_criterion N p hN θ ha I twoSided
  have hc : 0 < p.val.1 * (N : ℝ) ^ (-p.val.2) * (p.val.2 * (p.val.2 + 1)) :=
    mul_pos (mul_pos p.property.1 (Real.rpow_pos_of_pos (by positivity) _))
      (mul_pos p.property.2.1 (by linarith [p.property.2.1]))
  refine ⟨_, hc, upperPairs N χ, ⟨?_, ?_⟩, ?_⟩
  · intro q
    exact ⟨χ.smooth _ _ q.property, χ.curvature _ _ q.property,
      χ.leftBoundary _ _ q.property, χ.rightBoundary _ _ q.property⟩
  · intro A hA
    obtain ⟨D, hD, hb⟩ := hcoll A 1 hA zero_lt_one
    refine ⟨D, hD, fun x hx => ?_⟩
    let z := centeredGapChart N x
    have hz : z.val ∈ particleChamber N := (AffineMetric.centeredGapChart_mem_chamber_iff x).mpr hx
    have heq : (fun w : gapTangentSpace N => Riesz1.hsPairExpression χ w.val) =ᶠ[𝓝 z]
        (fun w : gapTangentSpace N => p.val.1 * W Y(T(w)) + p.val.1 * ∑ k ∈ I,
          (θ.val (a * Riesz1.hsGap w.val k) +
            if twoSided then θ.val (a / Riesz1.hsGap w.val k) else 0)) := by
      filter_upwards [((Riesz1.isOpen_hsChamber N).preimage continuous_subtype_val).mem_nhds hz] with w hw
      exact internal_pairs_quotient_realization N p hN θ a I twoSided χ hχ W hval w hw
    have hgrad := congrArg norm (internal_library_quotient_gradient N χ hz)
    rw [Submodule.norm_coe] at hgrad
    have htrace := internal_library_quotient_laplacian N χ hz
    have hcenter := internal_library_centering N χ hx
    have hd : Metric.infDist z.val (particleChamber N)ᶜ = Metric.infDist x (particleChamber N)ᶜ := by
      rw [AffineMetric.centeredGapChart_val_eq_translate]
      exact Riesz1.hsBoundaryDistance_translate N hN _ x
    have hh := hb z hz
    simp only [one_mul] at hh
    have hΔeq := (InnerProductSpace.laplacian_congr_nhds heq).eq_of_nhds
    rw [← heq.gradient_eq, ← hΔeq, hgrad, htrace, hcenter.1, hcenter.2, hd] at hh
    rw [upperPairs_energy]
    exact hh
  · intro X
    rw [upperPairs_energy]
    exact hχ X

/-- Internal equality of normalized laws from the particle
energy, with both normalization certificates explicit. -/
theorem internal_pair_eq_tiltedParticleMeasure (p : Parameters) (n : ℕ+)
    (hn : (n : ℕ) ≤ (N : ℕ)) (θ : PhysicalCutoff) (ε : ℝ) (twoSided : Bool)
    (χ : ParticlePairData N)
    (hm : Measurable (fun X : Riesz1.Configuration N =>
      ENNReal.ofReal (Real.exp (-particlePairEnergy χ (WithLp.toLp 2 X.val)))))
    (hZ : 0 < pairGibbsNormalizer χ ∧ pairGibbsNormalizer χ < ⊤)
    (hχ : ∀ X : Riesz1.Configuration N,
      particlePairEnergy χ (WithLp.toLp 2 X.val) =
        p.val.1 * energy p X + p.val.1 * physicalGapPenalty N n hn θ ε twoSided X) :
    pairGibbsMeasure χ hm hZ = tiltedParticleMeasure p N n hn θ ε twoSided := by
  let q := (tiltNormalizer p N n hn θ ε twoSided)⁻¹ * (partitionFunction p N)⁻¹
  let w : Riesz1.Configuration N → ℝ≥0∞ := fun X =>
    ENNReal.ofReal (Real.exp (-particlePairEnergy χ (WithLp.toLp 2 X.val)))
  have hf : Measurable (fun X : Riesz1.Configuration N =>
      ENNReal.ofReal (Real.exp (-p.val.1 * energy p X))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (measurable_energy p N)))
  have hg : Measurable (fun X : Riesz1.Configuration N =>
      ENNReal.ofReal (Real.exp (-p.val.1 * physicalGapPenalty N n hn θ ε twoSided X))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (DefinitionSanity.penalty_measurable N n hn θ ε twoSided)))
  have hw : (fun X : Riesz1.Configuration N => ENNReal.ofReal (Real.exp (-p.val.1 * energy p X))) *
      (fun X => ENNReal.ofReal (Real.exp (-p.val.1 * physicalGapPenalty N n hn θ ε twoSided X))) = w := by
    funext X
    simp only [Pi.mul_apply, w, hχ, neg_add, Real.exp_add,
      ENNReal.ofReal_mul (Real.exp_pos _).le, neg_mul]
  have hd : tiltedParticleMeasure p N n hn θ ε twoSided =
      q • (Riesz1.configurationVolume N).withDensity w := by
    rw [tiltedParticleMeasure, GapChart.gibbsMeasure_eq_withDensity,
      withDensity_smul_measure, ← withDensity_mul _ hf hg, hw, smul_smul]
  have hmass : q * pairGibbsNormalizer χ = 1 := by
    have : IsProbabilityMeasure (tiltedParticleMeasure p N n hn θ ε twoSided) :=
      DefinitionSanity.tilted_probability p N n hn θ ε twoSided
    have hh : tiltedParticleMeasure p N n hn θ ε twoSided univ = 1 := measure_univ
    rw [hd, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hh
    exact hh
  rw [hd, ENNReal.eq_inv_of_mul_eq_one_left hmass]
  rfl

/-- See Appendix A of the paper: the normalized physical tilt, for every
active prefix size and scale exponent, is the law of actual admissible pairs.
The measurable weight and positive finite particle partition are concluded. -/
theorem tiltedParticleMeasure_admissible_pairs (p : Parameters) (hN : 2 ≤ (N : ℕ))
    (n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ)) (θ : PhysicalCutoff) (ε : ℝ) (twoSided : Bool) :
    ∃ c : ℝ, 0 < c ∧ ∃ χ : ParticlePairData N,
      AdmissibleParticlePairs hN χ c ∧
      (∀ X : Riesz1.Configuration N,
        particlePairEnergy χ (WithLp.toLp 2 X.val) = p.val.1 * energy p X +
          p.val.1 * physicalGapPenalty N n hn θ ε twoSided X) ∧
      ∃ hm : Measurable (fun X : Riesz1.Configuration N =>
          ENNReal.ofReal (Real.exp (-particlePairEnergy χ (WithLp.toLp 2 X.val)))),
      ∃ hZ : 0 < pairGibbsNormalizer χ ∧ pairGibbsNormalizer χ < ⊤,
        pairGibbsMeasure χ hm hZ = tiltedParticleMeasure p N n hn θ ε twoSided := by
  classical
  let e : Fin (n : ℕ) → Fin (N : ℕ) := Fin.castLE hn
  let I := Finset.univ.image e
  let a := (n : ℝ) ^ (-ε)
  have ha : 0 < a := Real.rpow_pos_of_pos (by positivity) _
  have hI (X : Riesz1.Configuration N) :
      (∑ k ∈ I, (θ.val (a * gapVector X k) +
        if twoSided then θ.val (a / gapVector X k) else 0)) =
        physicalGapPenalty N n hn θ ε twoSided X := by
    have he : Function.Injective e := Fin.castLE_injective hn
    rw [Finset.sum_image (fun i _ j _ hij => he hij)]
    simp only [physicalGapPenalty, gapVector, e, a, Fin.val_castLE, div_eq_mul_inv]
  obtain ⟨c, hc, χ, hχ, henergy⟩ := admissible_physical_particle_pairs N p hN θ ha I twoSided
  have hactual (X : Riesz1.Configuration N) : particlePairEnergy χ (WithLp.toLp 2 X.val) =
      p.val.1 * energy p X + p.val.1 * physicalGapPenalty N n hn θ ε twoSided X := by
    rw [henergy X, hI X]
  let hm := pairGibbsWeight_measurable hχ
  let hZ := (particle_hessian_normalization hN c hc χ hχ).1
  exact ⟨c, hc, χ, hχ, hactual, hm, hZ,
    internal_pair_eq_tiltedParticleMeasure N p n hn θ ε twoSided χ hm hZ hactual⟩

/-- See Appendix A of the paper: in the unforced case the actual physical Gibbs
measure also has an admissible pair realization, in both exponent regimes. -/
theorem gibbsMeasure_admissible_pairs (p : Parameters) (hN : 2 ≤ (N : ℕ)) :
    ∃ c : ℝ, 0 < c ∧ ∃ χ : ParticlePairData N,
      AdmissibleParticlePairs hN χ c ∧
      (∀ X : Riesz1.Configuration N,
        particlePairEnergy χ (WithLp.toLp 2 X.val) = p.val.1 * energy p X) ∧
      ∃ hm : Measurable (fun X : Riesz1.Configuration N =>
          ENNReal.ofReal (Real.exp (-particlePairEnergy χ (WithLp.toLp 2 X.val)))),
      ∃ hZ : 0 < pairGibbsNormalizer χ ∧ pairGibbsNormalizer χ < ⊤,
        pairGibbsMeasure χ hm hZ = gibbsMeasure p N := by
  obtain ⟨θ⟩ := DefinitionSanity.physicalCutoff_nonempty
  obtain ⟨c, hc, χ, hχ, henergy⟩ := admissible_physical_particle_pairs N p hN θ
    (a := 1) zero_lt_one ∅ false
  simp only [Finset.sum_empty, mul_zero, add_zero] at henergy
  let hm := pairGibbsWeight_measurable hχ
  let hZ := (particle_hessian_normalization hN c hc χ hχ).1
  have hw : (fun X : Riesz1.Configuration N =>
      ENNReal.ofReal (Real.exp (-particlePairEnergy χ (WithLp.toLp 2 X.val)))) =
      (fun X => ENNReal.ofReal (Real.exp (-p.val.1 * energy p X))) := by
    funext X
    rw [henergy X, neg_mul]
  have hd : gibbsMeasure p N = (partitionFunction p N)⁻¹ •
      (Riesz1.configurationVolume N).withDensity
        (fun X => ENNReal.ofReal (Real.exp (-particlePairEnergy χ (WithLp.toLp 2 X.val)))) := by
    rw [hw]
    exact GapChart.gibbsMeasure_eq_withDensity p N
  have hmass : (partitionFunction p N)⁻¹ * pairGibbsNormalizer χ = 1 := by
    have : IsProbabilityMeasure (gibbsMeasure p N) := DefinitionSanity.particle_law_probability p N
    have hh : gibbsMeasure p N univ = 1 := measure_univ
    rw [hd, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hh
    exact hh
  refine ⟨c, hc, χ, hχ, henergy, hm, hZ, ?_⟩
  rw [hd, ENNReal.eq_inv_of_mul_eq_one_left hmass]
  rfl

/-- Internal identification of the pair gap potential with the physical
potential on the whole intrinsic simplex. -/
theorem internal_intrinsic_physical_potential_eq (p : Parameters) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) (a : ℝ) (I : Finset (Fin (N : ℕ))) (twoSided : Bool)
    {c : ℝ} (χ : ParticlePairData N) (hχ : AdmissibleParticlePairs hN χ c)
    (henergy : ∀ X : Riesz1.Configuration N,
      particlePairEnergy χ (WithLp.toLp 2 X.val) =
        p.val.1 * energy p X + p.val.1 * ∑ k ∈ I,
          (θ.val (a * gapVector X k) + if twoSided then θ.val (a / gapVector X k) else 0))
    (W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ)
    (hval : ∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
      W y.val = physicalAmbientGapEnergy p N y)
    {y : gapTangentSpace N} (hy : y ∈ intrinsicGapDomain N) :
    pairAmbientGapPotential χ Y(y) = p.val.1 * W Y(y) + p.val.1 *
      ∑ k ∈ I, (θ.val (a * (1 + y.val k)) +
        if twoSided then θ.val (a / (1 + y.val k)) else 0) := by
  let z := (AffineMetric.gapLinearEquiv N).symm (y - AffineMetric.gapOffset N)
  have hT : T(z) = y := by
    rw [AffineMetric.intrinsicParticleGapMap_eq, ContinuousLinearEquiv.apply_symm_apply, sub_add_cancel]
  have hz := (AffineMetric.intrinsicParticleGapMap_mem_iff N z).mp (hT.symm ▸ hy)
  have hgap (i : Fin (N : ℕ)) : Riesz1.hsGap z.val i = 1 + y.val i := by
    rw [← hT, AffineMetric.intrinsicParticleGapMap_apply]
    ring
  have he := internal_pairs_quotient_realization N p hN θ a I twoSided
    (AffineMetric.libraryPairs hχ) (fun X => by
      rw [AffineMetric.libraryPairs_energy hχ]
      exact henergy X) W hval z hz
  rw [AffineMetric.libraryPairs_energy hχ, hT] at he
  simp only [hgap] at he
  calc
    pairAmbientGapPotential χ Y(y) = pairAmbientGapPotential χ Y(T(z)) := by rw [hT]
    _ = particlePairEnergy χ z.val := AffineMetric.pairPotential_intrinsicParticleGapMap χ z
    _ = _ := he

/-- See Appendix A of the paper, well-posedness assembly for every allowed selected
physical penalty. The actual normalized particle law has admissible pair data. Its intrinsic gap law has the physical Gibbs potential, strict curvature, and
the collision criterion for every pair of positive coefficients. Taking the
empty active set gives the unforced case. The displayed differential estimates
are `unforced_collision_estimates`, `penalized_minimum_gap_estimates`, and their
particle-quotient companions in this module. -/
theorem physical_collision_estimates (p : Parameters) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (I : Finset (Fin (N : ℕ))) (twoSided : Bool) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ∃ c : ℝ, 0 < c ∧ ∃ χ : ParticlePairData N,
      AdmissibleParticlePairs hN χ c ∧
      (∀ X : Riesz1.Configuration N,
        particlePairEnergy χ (WithLp.toLp 2 X.val) = p.val.1 * energy p X + p.val.1 *
          ∑ k ∈ I, (θ.val (a * gapVector X k) +
            if twoSided then θ.val (a / gapVector X k) else 0)) ∧
      ∃ hm : Measurable (fun X : Riesz1.Configuration N =>
        ENNReal.ofReal (Real.exp (-particlePairEnergy χ (WithLp.toLp 2 X.val)))),
      ∃ hZ : 0 < pairGibbsNormalizer χ ∧ pairGibbsNormalizer χ < ⊤,
      let V := fun w : gapTangentSpace N => p.val.1 * W Y(w) + p.val.1 *
        ∑ k ∈ I, (θ.val (a * (1 + w.val k)) +
          if twoSided then θ.val (a / (1 + w.val k)) else 0)
      IsEuclideanGibbsPotential volume (intrinsicGapLaw (pairGibbsMeasure χ hm hZ))
        (intrinsicGapDomain N) V ∧
      (∃ κ : ℝ, 0 < κ ∧ ∀ z ∈ intrinsicGapDomain N, ∀ u : gapTangentSpace N,
        κ * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) z u u) ∧
      ∀ A K : ℝ, 0 < A → 0 < K → ∃ D : ℝ, 0 ≤ D ∧ ∀ z ∈ intrinsicGapDomain N,
        K * (Metric.infDist z (frontier (intrinsicGapDomain N)))⁻¹ ^ 2 - D ≤
          A * ‖gradient V z‖ ^ 2 - Laplacian.laplacian V z := by
  obtain ⟨W, hW, hval, κ, hκ, hcurv, hcoll⟩ :=
    penalized_collision_criterion N p hN θ ha I twoSided
  obtain ⟨c, hc, χ, hχ, henergy⟩ := admissible_physical_particle_pairs N p hN θ ha I twoSided
  let hm := pairGibbsWeight_measurable hχ
  let hZ := (particle_hessian_normalization hN c hc χ hχ).1
  let V : gapTangentSpace N → ℝ := fun w => p.val.1 * W Y(w) + p.val.1 *
    ∑ k ∈ I, (θ.val (a * (1 + w.val k)) + if twoSided then θ.val (a / (1 + w.val k)) else 0)
  have heq (y : gapTangentSpace N) (hy : y ∈ intrinsicGapDomain N) :
      pairAmbientGapPotential χ Y(y) = V y :=
    internal_intrinsic_physical_potential_eq N p hN θ a I twoSided χ hχ henergy W hval hy
  have hVs : ContDiffOn ℝ ∞ V (intrinsicGapDomain N) :=
    (contDiffOn_const.mul (contDiffOn_intrinsic_pullback N hW)).add
      (contDiffOn_const.mul (selected_penalty_smooth_convex N θ ha I twoSided).1)
  have hG := AffineMetric.intrinsicGapLaw_gibbsPotential hN c hc χ hχ
  obtain ⟨_, h0, ht, hlaw⟩ := hG
  have hw : (fun y : gapTangentSpace N => ENNReal.ofReal (Real.exp (-pairAmbientGapPotential χ Y(y))))
      =ᵐ[volume.restrict (intrinsicGapDomain N)] (fun y => ENNReal.ofReal (Real.exp (-V y))) := by
    filter_upwards [ae_restrict_mem (AffineMetric.intrinsicGapDomain_isOpen N).measurableSet] with y hy
    rw [heq y hy]
  have hnorm := lintegral_congr_ae hw
  rw [hnorm] at h0 ht hlaw
  rw [withDensity_congr_ae hw] at hlaw
  exact ⟨W, hW, hval, c, hc, χ, hχ, henergy, hm, hZ, ⟨hVs, h0, ht, hlaw⟩,
    ⟨κ, hκ, hcurv⟩, hcoll⟩

end Riesz2.PhysicalCollision
