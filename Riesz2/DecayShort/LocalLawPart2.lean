/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.ProperMarginalChart
public import Riesz2.HelfferSjostrand.ConvexLocalization
public import Riesz2.ToMathlib.ConvexTangentHessian
public import Riesz1.ToMathlib.ConvexPotentialConcentration
public import Riesz1.Frozen.External.BakryEmeryProof
public import Mathlib.Probability.Moments.Basic
public import Riesz2.ToMathlib.MomentEventBounds
import Riesz2.Sanity.SmoothCutoff
import all Riesz2.HelfferSjostrand.ProperMarginalChart
import all Riesz2.HelfferSjostrand.SingleGapTails

/-!
# Quadratic residuals of short-range upper tilts

Subtracting the selected quadratic from the physical ambient energy before
integrating out the exterior coordinates gives marginal strong convexity.
-/

public section
noncomputable section

open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal NNReal

namespace Riesz2.DecayShort

private theorem selected_quadratic_hessian {N : ℕ+}
    (J : Finset (Fin (N : ℕ))) (a : ℝ)
    (x u : EuclideanSpace ℝ (Fin (N : ℕ))) :
    fderiv ℝ (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin (N : ℕ)) =>
      a / 2 * ∑ i ∈ J, (z i) ^ 2)) x u u = a * ∑ i ∈ J, (u i) ^ 2 := by
  classical
  have he : (fun z : EuclideanSpace ℝ (Fin (N : ℕ)) => a / 2 * ∑ i ∈ J, (z i) ^ 2) =
      fun z => ∑ i, (if i ∈ J then a / 2 else 0) * (z i) ^ 2 := by
    funext z
    simp [Finset.mul_sum]
  rw [he]
  have hd : deriv (deriv (fun t : ℝ => t ^ 2)) = fun _ => 2 := by
    have hfirst : deriv (fun t : ℝ => t ^ 2) = fun t => 2 * t := by
      ext t
      simpa only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] using
        (deriv_pow_field (x := t) 2)
    rw [hfirst]
    ext t
    simp
  have h := (finite_linear_potential_derivatives
    (fun i : Fin (N : ℕ) => if i ∈ J then a / 2 else 0)
    (fun _ (t : ℝ) => t ^ 2) (fun i => EuclideanSpace.proj i)
    (fun _ => univ) (fun _ => isOpen_univ)
    (fun _ => (contDiff_id.pow 2).contDiffOn) x (fun _ => mem_univ _) u u).2
  simp only [EuclideanSpace.coe_proj] at h
  rw [h]
  simp only [hd, ite_mul, zero_mul,
    Finset.sum_ite_mem, Finset.univ_inter, ← pow_two]
  simp [Finset.mul_sum]

/-- See the proof of Lemma B.1 in the paper, quadratic subtraction on the full
simplex. The realization agrees with the energy on its entire ambient
domain, and the conclusion includes every selected set and `N = 2`. -/
theorem upperGapPenalty_sub_quadratic_convex (p : Parameters) (hs : 1 < p.val.2)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (θ : PhysicalCutoff)
    (R : {R : ℝ // 0 < R}) (hR : 1 ≤ (R : ℝ))
    (J : Finset (Fin (N : ℕ))) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ConvexOn ℝ (WithLp.ofLp ⁻¹' Riesz1.gapSimplex N)
        (fun y => W y + ∑ i ∈ J, θ.val (y i / R) -
          (R : ℝ) ^ (-p.val.2 - 2) / 2 * ∑ i ∈ J, (y i) ^ 2) := by
  classical
  obtain ⟨W, hW, hval, hcurv⟩ := upperGapPenalty_curvature p hs N hN θ R hR J
  let F : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ :=
    fun y => W y + ∑ i ∈ J, θ.val (y i / R)
  let Q : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ :=
    fun y => (R : ℝ) ^ (-p.val.2 - 2) / 2 * ∑ i ∈ J, (y i) ^ 2
  have hQ : ContDiff ℝ 2 Q := by
    apply ContDiff.mul contDiff_const
    apply ContDiff.sum
    intro i _
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.pow 2
  have hF (y : EuclideanSpace ℝ (Fin (N : ℕ)))
      (hy : y ∈ WithLp.ofLp ⁻¹' Riesz1.gapSimplex N) : ContDiffAt ℝ 2 F y := by
    have hyU := PhysicalEnergy.simplex_subset_ambient N (WithLp.ofLp y) hy
    exact ((hW.of_le (by norm_num)).contDiffAt
      ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hyU)).add
        (upperGapPenalty_contDiffAt θ R J y hy.1)
  have hc : Convex ℝ (WithLp.ofLp ⁻¹' Riesz1.gapSimplex N) :=
    (Riesz1.convex_gapSimplex N).linear_preimage
      (WithLp.linearEquiv 2 ℝ (Fin (N : ℕ) → ℝ)).toLinearMap
  refine ⟨W, hW, hval, convexOn_of_tangent_hessian_nonneg hc
    (fun y hy => ((hF y hy).sub hQ.contDiffAt).differentiableAt (by norm_num))
    (fun y hy => (((hF y hy).sub hQ.contDiffAt).fderiv_right
      (by norm_num : 1 + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt (by norm_num)) ?_⟩
  intro y hy z _ w _
  have he : fderiv ℝ (fun y => F y - Q y) =ᶠ[𝓝 y]
      fun y => fderiv ℝ F y - fderiv ℝ Q y := by
    filter_upwards [(hF y hy).eventually (by norm_num)] with t ht
    exact fderiv_fun_sub (ht.differentiableAt (by norm_num))
      (hQ.differentiable (by norm_num)).differentiableAt
  rw [he.fderiv_eq, fderiv_fun_sub
    (((hF y hy).fderiv_right (by norm_num : 1 + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
      (by norm_num))
    ((hQ.contDiffAt.fderiv_right (by norm_num : 1 + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
      (by norm_num))]
  change 0 ≤ fderiv ℝ (fderiv ℝ F) y (w - z) (w - z) -
    fderiv ℝ (fderiv ℝ Q) y (w - z) (w - z)
  rw [show fderiv ℝ (fderiv ℝ Q) y (w - z) (w - z) =
      (R : ℝ) ^ (-p.val.2 - 2) * ∑ i ∈ J, ((w - z) i) ^ 2 from
    selected_quadratic_hessian J _ y (w - z)]
  exact sub_nonneg.mpr (hcurv (WithLp.ofLp y) hy (w - z))

private theorem retained_sum {n m : ℕ} (σ : Equiv.Perm (Fin (n + m + 1)))
    (f : ℝ → ℝ) (L : ℝ)
    (q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :
    ∑ i ∈ Finset.univ.image (fun j : Fin n => σ (j.castAdd m).castSucc),
      f (RetainedSimplex.chart n m L σ q i) = ∑ i, f (q.1 i) := by
  classical
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i _
    rw [RetainedSimplex.chart_retained]
  · intro i _ j _ hij
    exact Fin.ext (congrArg (fun k : Fin (n + m + 1) => k.val) (σ.injective hij))

set_option backward.isDefEq.respectTransparency false in
/-- See the proof of Lemma B.1 in the paper, the retained affine-chart residual.
The Gibbs factor is exactly the density of the actual upper tilt.
The retained labels are arbitrary, and the exterior dimension may be zero. -/
theorem upperTilt_chart_residual (p : Parameters) (hs : 1 < p.val.2)
    (n m : ℕ) (hn : 1 ≤ n) (σ : Equiv.Perm (Fin (n + m + 1)))
    (θ : PhysicalCutoff) (R : {R : ℝ // 0 < R}) (hR : 1 ≤ (R : ℝ)) :
    let J := Finset.univ.image (fun j : Fin n => σ (j.castAdd m).castSucc)
    let Ω := RetainedSimplex.domain n m ((n + m : ℕ) + 1)
    ∃ A : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) → ℝ,
      ConvexOn ℝ Ω (fun q => A q -
        (p.val.1 * (R : ℝ) ^ (-p.val.2 - 2)) / 2 * ‖q.1‖ ^ 2) ∧
      ProperMarginalChart.penalizedChartDensity p n m σ θ R.val⁻¹ J false =
        fun q => ENNReal.ofReal (Ω.indicator (fun q => Real.exp (-A q)) q) := by
  classical
  intro J Ω
  let N : ℕ+ := ⟨n + m + 1, by omega⟩
  let T := RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ
  obtain ⟨W, _, hval, hc⟩ := upperGapPenalty_sub_quadratic_convex p hs N
    (by change 2 ≤ n + m + 1; omega) θ R hR J
  change EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ at W
  let A := fun q => p.val.1 * (W (T q) + ∑ i : Fin n, θ.val (q.1 i / R))
  have hsimplex (q) (hq : q ∈ Ω) :
      WithLp.ofLp (T q) ∈ Riesz1.gapSimplex N := by
    have h := (RetainedSimplex.chart_mem_simplex n m _ σ q).mpr hq
    refine ⟨h.1, ?_⟩
    change (∑ i, T q i) = ((n + m + 1 : ℕ) : ℝ)
    simpa only [T, Nat.cast_add, Nat.cast_one] using h.2
  have hsum (q) : ∑ i ∈ J, θ.val (T q i / R) = ∑ i : Fin n, θ.val (q.1 i / R) :=
    retained_sum σ (fun t => θ.val (t / R)) _ q
  have hsq (q) : (∑ i ∈ J, (T q i) ^ 2) = ‖q.1‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact retained_sum σ (fun t => t ^ 2) _ q
  have he (q) : p.val.1 * (W (T q) + ∑ i ∈ J, θ.val (T q i / R) -
      (R : ℝ) ^ (-p.val.2 - 2) / 2 * ∑ i ∈ J, (T q i) ^ 2) =
      A q - (p.val.1 * (R : ℝ) ^ (-p.val.2 - 2)) / 2 * ‖q.1‖ ^ 2 := by
    rw [hsum, hsq]
    dsimp only [A]
    ring
  refine ⟨A, ⟨RetainedSimplex.convex_domain n m _, ?_⟩, ?_⟩
  · intro u hu v hv a b ha hb hab
    have h := (hc.smul p.property.1.le).2 (hsimplex u hu) (hsimplex v hv) ha hb hab
    have hT : T (a • u + b • v) = a • T u + b • T v :=
      RetainedSimplex.chart_convex_combination n m _ σ u v hab
    rw [← hT] at h
    dsimp only at h
    simp only [smul_eq_mul] at h
    erw [he (a • u + b • v), he u, he v] at h
    exact h
  · funext q
    by_cases hq : q ∈ Ω
    · have hq' := hsimplex q hq
      have hamb := PhysicalEnergy.simplex_subset_ambient N (WithLp.ofLp (T q)) hq'
      have hmass := (RetainedSimplex.chart_mem_simplex n m _ σ q).mpr hq
      change T q ∈ AffineSimplex.massSimplex (n + m) ((n + m : ℕ) + 1) at hmass
      change Ω.indicator (fun q => ProperMarginalChart.penalizedDensity p (n + m)
        θ R.val⁻¹ J false (T q)) q = _
      rw [indicator_of_mem hq, indicator_of_mem hq]
      simp only [ProperMarginalChart.penalizedDensity, ProperMarginalChart.density,
        Bool.false_eq_true, ↓reduceIte, add_zero]
      rw [dite_eq_left hmass]
      erw [← hval ⟨T q, hamb⟩]
      have hpen : (∑ i ∈ J, θ.val (R.val⁻¹ * T q i)) =
          ∑ i : Fin n, θ.val (q.1 i / R) := by
        simpa only [div_eq_mul_inv, mul_comm] using hsum q
      rw [hpen, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      dsimp only [A]
      ring
    · change Ω.indicator (fun q => ProperMarginalChart.penalizedDensity p (n + m)
        θ R.val⁻¹ J false (T q)) q = _
      rw [indicator_of_notMem hq, indicator_of_notMem hq, ENNReal.ofReal_zero]

set_option backward.isDefEq.respectTransparency false in
/-- See the proof of Lemma B.1 in the paper, strong convexity of the negative
logarithm of the actual retained fibre density. This proves the nonsmooth
curvature statement without assuming any marginal regularity. -/
theorem upperTilt_marginal_residual_convex (p : Parameters) (hs : 1 < p.val.2)
    (n m : ℕ) (hn : 1 ≤ n) (σ : Equiv.Perm (Fin (n + m + 1)))
    (θ : PhysicalCutoff) (R : {R : ℝ // 0 < R}) (hR : 1 ≤ (R : ℝ)) :
    let J := Finset.univ.image (fun j : Fin n => σ (j.castAdd m).castSucc)
    let D := ProperMarginalChart.penalizedChartDensity p n m σ θ R.val⁻¹ J false
    ConvexOn ℝ (AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
      (fun x => -Real.log (AffineFibre.fibreMass volume D x).toReal -
        (p.val.1 * (R : ℝ) ^ (-p.val.2 - 2)) / 2 * ‖x‖ ^ 2) := by
  classical
  intro J D
  let Ω := RetainedSimplex.domain n m ((n + m : ℕ) + 1)
  let Q := fun x : EuclideanSpace ℝ (Fin n) =>
    (p.val.1 * (R : ℝ) ^ (-p.val.2 - 2)) / 2 * ‖x‖ ^ 2
  obtain ⟨A, hc, hD⟩ := upperTilt_chart_residual p hs n m hn σ θ R hR
  let B := fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) => A q - Q q.1
  have hB : ConvexOn ℝ Ω B := hc
  have hm := convexLocalization (RetainedSimplex.isOpen_domain n m _)
    (RetainedSimplex.convex_domain n m _) (RetainedSimplex.isBounded_domain n m _)
    hB (fun _ => 0)
  rw [RetainedSimplex.fst_image_domain] at hm
  have hw (x : EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin m)) :
      Ω.indicator (fun q => Real.exp (-A q)) (x, z) =
        Real.exp (-Q x) * Ω.indicator (fun q => Real.exp (-B q)) (x, z) := by
    by_cases hq : (x, z) ∈ Ω
    · rw [indicator_of_mem hq, indicator_of_mem hq, ← Real.exp_add]
      congr 1
      dsimp only [B]
      ring
    · rw [indicator_of_notMem hq, indicator_of_notMem hq, mul_zero]
  have he (x) (hx : x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
      -Real.log (AffineFibre.fibreMass volume D x).toReal - Q x =
        -Real.log (∫ z, Ω.indicator (fun q => Real.exp (-B q)) (x, z)) := by
    obtain ⟨hi, hp⟩ := hm.1 x hx
    have hiA : Integrable (fun z => Ω.indicator (fun q => Real.exp (-A q)) (x, z)) := by
      simp_rw [hw]
      exact hi.const_mul _
    have hnonneg : ∀ z, 0 ≤ Ω.indicator (fun q => Real.exp (-A q)) (x, z) :=
      fun z => indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
    have hreal : (AffineFibre.fibreMass volume D x).toReal =
        Real.exp (-Q x) * ∫ z, Ω.indicator (fun q => Real.exp (-B q)) (x, z) := by
      change (∫⁻ z, D (x, z)).toReal = _
      rw [show D = fun q => ENNReal.ofReal
        (Ω.indicator (fun q => Real.exp (-A q)) q) from hD,
        ← ofReal_integral_eq_lintegral_ofReal hiA (Eventually.of_forall hnonneg),
        ENNReal.toReal_ofReal (integral_nonneg hnonneg)]
      simp_rw [hw]
      exact integral_const_mul _ _
    rw [hreal, Real.log_mul (Real.exp_pos _).ne' hp.ne', Real.log_exp]
    ring
  have hconv : ConvexOn ℝ (AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
      (fun x => -Real.log (∫ z, Ω.indicator (fun q => Real.exp (-B q)) (x, z))) := by
    simpa only [zero_sub, sub_zero] using hm.2
  exact hconv.congr (fun x hx => (he x hx).symm)

private theorem probability_smul_unique {E : Type*} [MeasurableSpace E]
    {μ ν ρ : Measure E} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {c d : ℝ≥0∞} (hμ : μ = c • ρ) (hν : ν = d • ρ) : μ = ν := by
  have hc : c * ρ univ = 1 := by
    rw [← smul_eq_mul, ← Measure.smul_apply, ← hμ, measure_univ]
  have hd : d * ρ univ = 1 := by
    rw [← smul_eq_mul, ← Measure.smul_apply, ← hν, measure_univ]
  rw [hμ, hν, ENNReal.eq_inv_of_mul_eq_one_left hc,
    ENNReal.eq_inv_of_mul_eq_one_left hd]

set_option backward.isDefEq.respectTransparency false in
/-- See the proof of Lemma B.1 in the paper: the actual retained marginal is
the Gibbs probability of its physical negative log fibre density, and that
potential has the asserted convex quadratic residual. This normalization
identity also permits Herbst without assuming classical differentiability. -/
theorem upperTilt_marginal_gibbs (p : Parameters) (hs : 1 < p.val.2)
    (n m : ℕ) (hn : 1 ≤ n) (σ : Equiv.Perm (Fin (n + m + 1)))
    (θ : PhysicalCutoff) (R : {R : ℝ // 0 < R}) (hR : 1 ≤ (R : ℝ)) :
    let J := Finset.univ.image (fun j : Fin n => σ (j.castAdd m).castSucc)
    let U := AffineSimplex.chartDomain n ((n + m : ℕ) + 1)
    let D := ProperMarginalChart.penalizedChartDensity p n m σ θ R.val⁻¹ J false
    let V := fun x => -Real.log (AffineFibre.fibreMass volume D x).toReal
    ConvexOn ℝ U (fun x => V x -
        (p.val.1 * (R : ℝ) ^ (-p.val.2 - 2)) / 2 * ‖x‖ ^ 2) ∧
      (upperTiltedParticleMeasure p (n + m).succPNat θ R J).map
        (fun X : Riesz1.Configuration (n + m).succPNat =>
          (RetainedSimplex.coordinates n m σ (WithLp.toLp 2 (gapVector X))).1) =
        (volume.restrict U).tilted (fun x => -V x) := by
  classical
  intro J U D V
  have hc := upperTilt_marginal_residual_convex p hs n m hn σ θ R hR
  refine ⟨hc, ?_⟩
  have hκ : 0 < p.val.1 * (R : ℝ) ^ (-p.val.2 - 2) :=
    mul_pos p.property.1 (Real.rpow_pos_of_pos R.property _)
  have hne : U.Nonempty := by
    let x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun _ => (1 : ℝ))
    refine ⟨x, (show ∀ i, 0 < x i from fun _ => zero_lt_one), ?_⟩
    change (∑ _i : Fin n, (1 : ℝ)) < _
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    linarith
  have hτ := (Riesz1.Internal.convex_potential_lipschitz_concentration
    Riesz1.External.bakry_emery (AffineSimplex.isOpen_chartDomain n _)
    (AffineSimplex.convex_chartDomain n _) (AffineSimplex.isBounded_chartDomain n _)
    hne hκ hc (F := fun _ => (0 : ℝ)) (L := 0) (LipschitzWith.const 0).lipschitzOnWith 0).1
  have hM := AffineFibre.measurable_fibreMass volume
    (ProperMarginalChart.measurable_penalizedChartDensity p n m σ θ
      (inv_pos.mpr R.property) J false)
  have hJ : ∀ i ∈ J, ∃ j : Fin n, i = σ (j.castAdd m).castSucc := by
    intro i hi
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
    exact ⟨j, hj.symm⟩
  have hMf (x) (hx : x ∈ U) := ProperMarginalChart.penalized_fibre_mass p n m hn σ
    θ R.val⁻¹ J false hJ hx
  have hMz (x) (hx : x ∉ U) : AffineFibre.fibreMass volume D x = 0 := by
    have hout (z : EuclideanSpace ℝ (Fin m)) :
        (x, z) ∉ RetainedSimplex.domain n m ((n + m : ℕ) + 1) := by
      intro h
      apply hx
      change x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1)
      rw [← RetainedSimplex.fst_image_domain n m _]
      exact ⟨(x, z), h, rfl⟩
    change (∫⁻ z, D (x, z)) = 0
    apply lintegral_eq_zero_of_ae_eq_zero
    exact Eventually.of_forall (fun z => indicator_of_notMem (hout z) _)
  have hweight : U.indicator (fun x => ENNReal.ofReal (Real.exp (-V x))) =
      AffineFibre.fibreMass volume D := by
    funext x
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx]
      have hp : 0 < (AffineFibre.fibreMass volume D x).toReal :=
        ENNReal.toReal_pos (hMf x hx).1 (hMf x hx).2
      simp only [V, neg_neg, Real.exp_log hp]
      exact ENNReal.ofReal_toReal (hMf x hx).2
    · rw [indicator_of_notMem hx, hMz x hx]
  let d := ENNReal.ofReal (∫ x in U, Real.exp (-V x))⁻¹
  have ht : (volume.restrict U).tilted (fun x => -V x) =
      d • volume.withDensity (AffineFibre.fibreMass volume D) := by
    rw [Measure.tilted, ← withDensity_indicator (AffineSimplex.isOpen_chartDomain n _).measurableSet,
      ← withDensity_smul _ hM]
    congr 1
    funext x
    change U.indicator (fun x => ENNReal.ofReal (Real.exp (-V x) /
      ∫ y in U, Real.exp (-V y))) x = d * AffineFibre.fibreMass volume D x
    rw [← hweight]
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx, indicator_of_mem hx, div_eq_mul_inv,
        ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]
  have hp := upperTiltedParticleMeasure_probability p (n + m).succPNat θ R J
  have : IsProbabilityMeasure ((upperTiltedParticleMeasure p (n + m).succPNat θ R J).map
      (fun X : Riesz1.Configuration (n + m).succPNat =>
        (RetainedSimplex.coordinates n m σ (WithLp.toLp 2 (gapVector X))).1)) := by
    infer_instance
  have hμ := ProperMarginalChart.map_upperTiltedParticleMeasure_retained p n m hn σ θ R J
  simp only [smul_smul] at hμ
  exact probability_smul_unique hμ ht

set_option backward.isDefEq.respectTransparency false in
/-- See Lemma B.1 of the paper, the Herbst estimate for every Lipschitz
observable of the actual tilted retained gaps. The curvature is explicit,
uniform in the volume and the retained labels. Integrability is concluded. -/
theorem upperTilt_marginal_herbst (p : Parameters) (hs : 1 < p.val.2)
    (n m : ℕ) (hn : 1 ≤ n) (σ : Equiv.Perm (Fin (n + m + 1)))
    (θ : PhysicalCutoff) (R : {R : ℝ // 0 < R}) (hR : 1 ≤ (R : ℝ))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ≥0)
    (hF : LipschitzOnWith L F (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)))
    (t : ℝ) :
    let J := Finset.univ.image (fun j : Fin n => σ (j.castAdd m).castSucc)
    let μ := (upperTiltedParticleMeasure p (n + m).succPNat θ R J).map
      (fun X : Riesz1.Configuration (n + m).succPNat =>
        (RetainedSimplex.coordinates n m σ (WithLp.toLp 2 (gapVector X))).1)
    Integrable F μ ∧ Integrable (fun x => Real.exp (t * F x)) μ ∧
      Real.log (∫ x, Real.exp (t * F x) ∂μ) ≤
        t * ∫ x, F x ∂μ + t ^ 2 * (L : ℝ) ^ 2 /
          (2 * (p.val.1 * (R : ℝ) ^ (-p.val.2 - 2))) := by
  intro J μ
  obtain ⟨hc, hμ⟩ := upperTilt_marginal_gibbs p hs n m hn σ θ R hR
  have hκ : 0 < p.val.1 * (R : ℝ) ^ (-p.val.2 - 2) :=
    mul_pos p.property.1 (Real.rpow_pos_of_pos R.property _)
  have hne : (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)).Nonempty := by
    refine ⟨WithLp.toLp 2 (fun _ => (1 : ℝ)), (fun _ => zero_lt_one), ?_⟩
    change (∑ _i : Fin n, (1 : ℝ)) < _
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    linarith
  rw [show μ = _ from hμ]
  exact (Riesz1.Internal.convex_potential_lipschitz_concentration
    Riesz1.External.bakry_emery (AffineSimplex.isOpen_chartDomain n _)
    (AffineSimplex.convex_chartDomain n _) (AffineSimplex.isBounded_chartDomain n _)
    hne hκ hc hF t).2

set_option backward.isDefEq.respectTransparency false in
/-- See Lemma B.1 of the paper, the closed two-sided Gaussian tail under
the actual upper tilt. It applies to arbitrary retained sets, including a
single exterior gap, with no smoothness hypothesis on the marginal. -/
theorem upperTilt_marginal_concentration (p : Parameters) (hs : 1 < p.val.2)
    (n m : ℕ) (hn : 1 ≤ n) (σ : Equiv.Perm (Fin (n + m + 1)))
    (θ : PhysicalCutoff) (R : {R : ℝ // 0 < R}) (hR : 1 ≤ (R : ℝ))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ≥0) (hL : 0 < L)
    (hF : LipschitzOnWith L F (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)))
    (u : ℝ) (hu : 0 < u) :
    let J := Finset.univ.image (fun j : Fin n => σ (j.castAdd m).castSucc)
    let μ := (upperTiltedParticleMeasure p (n + m).succPNat θ R J).map
      (fun X : Riesz1.Configuration (n + m).succPNat =>
        (RetainedSimplex.coordinates n m σ (WithLp.toLp 2 (gapVector X))).1)
    μ {x | u ≤ |F x - ∫ y, F y ∂μ|} ≤
      ENNReal.ofReal (2 * Real.exp (-(p.val.1 * (R : ℝ) ^ (-p.val.2 - 2)) * u ^ 2 /
        (2 * (L : ℝ) ^ 2))) := by
  intro J μ
  have hp := upperTiltedParticleMeasure_probability p (n + m).succPNat θ R J
  have : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let κ := p.val.1 * (R : ℝ) ^ (-p.val.2 - 2)
  have hκ : 0 < κ := mul_pos p.property.1 (Real.rpow_pos_of_pos R.property _)
  have hL0 : 0 < (L : ℝ) := hL
  let t := κ * u / (L : ℝ) ^ 2
  have ht : 0 < t := div_pos (mul_pos hκ hu) (sq_pos_of_pos hL0)
  have H (t : ℝ) := upperTilt_marginal_herbst p hs n m hn σ θ R hR F L hF t
  have hupper := ProbabilityTheory.measure_ge_le_exp_cgf (μ := μ) (X := F)
    ((∫ y, F y ∂μ) + u) ht.le (H t).2.1
  have hlower := ProbabilityTheory.measure_le_le_exp_cgf (μ := μ) (X := F)
    ((∫ y, F y ∂μ) - u) (neg_nonpos.mpr ht.le) (H (-t)).2.1
  have hupper' : μ.real {x | (∫ y, F y ∂μ) + u ≤ F x} ≤
      Real.exp (-κ * u ^ 2 / (2 * (L : ℝ) ^ 2)) := by
    refine hupper.trans (Real.exp_le_exp.mpr ?_)
    have hh := (H t).2.2
    change Real.log (∫ x, Real.exp (t * F x) ∂μ) ≤
      t * ∫ x, F x ∂μ + t ^ 2 * (L : ℝ) ^ 2 / (2 * κ) at hh
    change -t * ((∫ y, F y ∂μ) + u) + Real.log (∫ x, Real.exp (t * F x) ∂μ) ≤ _
    calc
      _ ≤ -t * ((∫ y, F y ∂μ) + u) +
          (t * ∫ x, F x ∂μ + t ^ 2 * (L : ℝ) ^ 2 / (2 * κ)) := add_le_add le_rfl hh
      _ = _ := by dsimp only [t]; field_simp; ring
  have hlower' : μ.real {x | F x ≤ (∫ y, F y ∂μ) - u} ≤
      Real.exp (-κ * u ^ 2 / (2 * (L : ℝ) ^ 2)) := by
    refine hlower.trans (Real.exp_le_exp.mpr ?_)
    have hh := (H (-t)).2.2
    change Real.log (∫ x, Real.exp (-t * F x) ∂μ) ≤
      -t * ∫ x, F x ∂μ + (-t) ^ 2 * (L : ℝ) ^ 2 / (2 * κ) at hh
    change -(-t) * ((∫ y, F y ∂μ) - u) + Real.log (∫ x, Real.exp (-t * F x) ∂μ) ≤ _
    calc
      _ ≤ -(-t) * ((∫ y, F y ∂μ) - u) +
          (-t * ∫ x, F x ∂μ + (-t) ^ 2 * (L : ℝ) ^ 2 / (2 * κ)) := add_le_add le_rfl hh
      _ = _ := by dsimp only [t]; field_simp; ring
  have he : {x | u ≤ |F x - ∫ y, F y ∂μ|} =
      {x | (∫ y, F y ∂μ) + u ≤ F x} ∪ {x | F x ≤ (∫ y, F y ∂μ) - u} := by
    ext x
    simp only [mem_ofPred_eq, mem_union, le_abs]
    constructor <;> rintro (h | h)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hb : μ.real {x | u ≤ |F x - ∫ y, F y ∂μ|} ≤
      2 * Real.exp (-κ * u ^ 2 / (2 * (L : ℝ) ^ 2)) := by
    rw [he]
    exact (measureReal_union_le _ _).trans (by linarith)
  simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top μ _)] using
    ENNReal.ofReal_le_ofReal hb

set_option backward.isDefEq.respectTransparency false in
/-- See Lemma B.1 of the paper, concentration of the sum of the retained
gaps about its tilted mean, with the exact squared Lipschitz constant `n`.
This applies to any proper retained set, and hence to every allowed block. -/
theorem upperTilt_sum_concentration (p : Parameters) (hs : 1 < p.val.2)
    (n m : ℕ) (hn : 1 ≤ n) (σ : Equiv.Perm (Fin (n + m + 1)))
    (θ : PhysicalCutoff) (R : {R : ℝ // 0 < R}) (hR : 1 ≤ (R : ℝ))
    (u : ℝ) (hu : 0 < u) :
    let J := Finset.univ.image (fun j : Fin n => σ (j.castAdd m).castSucc)
    let μ := (upperTiltedParticleMeasure p (n + m).succPNat θ R J).map
      (fun X : Riesz1.Configuration (n + m).succPNat =>
        (RetainedSimplex.coordinates n m σ (WithLp.toLp 2 (gapVector X))).1)
    μ {x | u ≤ |(∑ i, x i) - ∫ y, (∑ i, y i) ∂μ|} ≤
      ENNReal.ofReal (2 * Real.exp (-(p.val.1 * (R : ℝ) ^ (-p.val.2 - 2)) * u ^ 2 /
        (2 * n))) := by
  intro J μ
  let one : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun _ => (1 : ℝ))
  let l := innerSL ℝ one
  have hl : ⇑l = fun x : EuclideanSpace ℝ (Fin n) => ∑ i, x i := by
    funext x
    simp [l, innerSL_apply_apply, PiLp.inner_apply, one, RCLike.inner_apply]
  have hnorm : ‖l‖ ^ 2 = (n : ℝ) := by
    rw [innerSL_apply_norm, EuclideanSpace.real_norm_sq_eq]
    simp [one]
  have hlpos : 0 < ‖l‖₊ := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hp : 0 < ‖l‖ := by nlinarith [norm_nonneg l]
    exact hp
  have h := upperTilt_marginal_concentration p hs n m hn σ θ R hR
    (fun x => ∑ i, x i) ‖l‖₊ hlpos
    (by rw [← hl]; exact l.lipschitzWith.lipschitzOnWith) u hu
  simpa only [NNReal.coe_mk, coe_nnnorm, hnorm] using h

namespace LocalLawInternal

set_option backward.isDefEq.respectTransparency false in
/-- Integration against the existing actual upper tilt, for integrable tests.
Both integrability and the normalized weighted formula are proved. -/
theorem upperTilt_integral (p : Parameters) (N : ℕ+) (θ : PhysicalCutoff)
    (R : {R : ℝ // 0 < R}) (J : Finset (Fin (N : ℕ)))
    (Y : Riesz1.Configuration N → ℝ) (hY : Integrable Y (gibbsMeasure p N)) :
    Integrable Y (upperTiltedParticleMeasure p N θ R J) ∧
      (∫ X, Y X ∂upperTiltedParticleMeasure p N θ R J) =
        (∫ X, Real.exp (-p.val.1 * upperGapPenalty θ R J X) ∂gibbsMeasure p N)⁻¹ *
          ∫ X, Real.exp (-p.val.1 * upperGapPenalty θ R J X) * Y X ∂gibbsMeasure p N := by
  have := gibbsMeasure_probability p N
  let w := fun X => Real.exp (-p.val.1 * upperGapPenalty θ R J X)
  have hw : Measurable w := ((upperGapPenalty_measurable θ R J).const_mul _).exp
  have hw0 (X) : 0 ≤ w X := (Real.exp_pos _).le
  have hw1 (X) : w X ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr p.property.1.le)
      (upperGapPenalty_nonneg θ R J X))
  have hwi := integrable_upperGapWeight p N θ R J
  have hz : 0 < ∫ X, w X ∂gibbsMeasure p N := integral_exp_pos hwi
  have hi := MomentEvent.integrable_mul_of_abs_le hw hY
    (fun X => (abs_of_nonneg (hw0 X)).trans_le (hw1 X))
  rw [upperTiltedParticleMeasure_eq_withDensity]
  have hd : Measurable (fun X => ENNReal.ofReal
      ((∫ X, w X ∂gibbsMeasure p N)⁻¹ * w X)) := (hw.const_mul _).ennreal_ofReal
  have hdn (X) : 0 ≤ (∫ X, w X ∂gibbsMeasure p N)⁻¹ * w X :=
    mul_nonneg (inv_nonneg.mpr hz.le) (hw0 X)
  constructor
  · rw [integrable_withDensity_iff_integrable_smul' hd
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hdn _), smul_eq_mul]
    simpa only [mul_assoc] using hi.const_mul (∫ X, w X ∂gibbsMeasure p N)⁻¹
  · rw [integral_withDensity_eq_integral_toReal_smul hd
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    simp only [ENNReal.toReal_ofReal (hdn _), smul_eq_mul, mul_assoc]
    exact integral_const_mul _ _

set_option backward.isDefEq.respectTransparency false in
/-- The exceptional-set Cauchy–Schwarz mean comparison used in Lemma B.1. The hypotheses concern only the test's measurability
and second-moment integrability, and normalization is never totalized. -/
theorem upperTilt_mean_transfer (p : Parameters) (N : ℕ+) (θ : PhysicalCutoff)
    (R : {R : ℝ // 0 < R}) (J : Finset (Fin (N : ℕ)))
    (Y : Riesz1.Configuration N → ℝ) (hY : Measurable Y)
    (hY2 : Integrable (fun X => Y X ^ 2) (gibbsMeasure p N)) :
    let w := fun X => Real.exp (-p.val.1 * upperGapPenalty θ R J X)
    let z := ∫ X, w X ∂gibbsMeasure p N
    let E := {X | upperGapPenalty θ R J X ≠ 0}
    Integrable Y (upperTiltedParticleMeasure p N θ R J) ∧
      |(∫ X, Y X ∂upperTiltedParticleMeasure p N θ R J) - ∫ X, Y X ∂gibbsMeasure p N| ≤
        z⁻¹ * (Real.sqrt (∫ X, Y X ^ 2 ∂gibbsMeasure p N) *
          Real.sqrt ((gibbsMeasure p N).real E) +
          |∫ X, Y X ∂gibbsMeasure p N| * (gibbsMeasure p N).real E) := by
  have := gibbsMeasure_probability p N
  intro w z E
  have hw : Measurable w := ((upperGapPenalty_measurable θ R J).const_mul _).exp
  have hw0 (X) : 0 ≤ w X := (Real.exp_pos _).le
  have hw1 (X) : w X ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr p.property.1.le)
      (upperGapPenalty_nonneg θ R J X))
  have hwi := integrable_upperGapWeight p N θ R J
  have hz : 0 < z := integral_exp_pos hwi
  have hE : MeasurableSet E :=
    (measurableSet_eq_fun (upperGapPenalty_measurable θ R J) measurable_const).compl
  have hYi := MomentEvent.integrable_of_integrable_sq hY hY2
  obtain ⟨hYt, hformula⟩ := upperTilt_integral p N θ R J Y hYi
  have hg : Measurable (fun X => 1 - w X) := measurable_const.sub hw
  have hg1 (X) : |1 - w X| ≤ 1 := by rw [abs_of_nonneg (by linarith [hw1 X])]; linarith [hw0 X]
  have hzero (X) (hX : X ∉ E) : 1 - w X = 0 := by
    have he : upperGapPenalty θ R J X = 0 := by simpa only [E, mem_ofPred_eq, not_not] using hX
    simp [w, he]
  have hCS := MomentEvent.abs_integral_mul_le_sqrt_mul_sqrt hg hY
    (by norm_num : (0 : ℝ) ≤ 1) hg1 hY2 hE
  have hrare : |∫ X, (1 - w X) * Y X ∂gibbsMeasure p N| ≤
      Real.sqrt (∫ X, Y X ^ 2 ∂gibbsMeasure p N) *
        Real.sqrt ((gibbsMeasure p N).real E) := by
    have he : (fun X => (1 - w X) * Y X) = E.indicator (fun X => (1 - w X) * Y X) := by
      funext X
      by_cases hX : X ∈ E
      · exact (indicator_of_mem hX (fun X => (1 - w X) * Y X)).symm
      · rw [indicator_of_notMem hX (fun X => (1 - w X) * Y X), hzero X hX, zero_mul]
    rw [he, integral_indicator hE]
    simpa only [one_mul] using hCS
  have hzrare : 0 ≤ 1 - z ∧ 1 - z ≤ (gibbsMeasure p N).real E := by
    have hle : ∀ X, 1 - w X ≤ E.indicator (fun _ => (1 : ℝ)) X := by
      intro X
      by_cases hX : X ∈ E
      · rw [indicator_of_mem hX]; linarith [hw0 X]
      · rw [indicator_of_notMem hX, hzero X hX]
    have hi : Integrable (fun X => 1 - w X) (gibbsMeasure p N) :=
      (integrable_const (1 : ℝ)).sub hwi
    have he : (∫ X, 1 - w X ∂gibbsMeasure p N) = 1 - z := by
      rw [integral_sub (integrable_const _) hwi, integral_const, probReal_univ]
      simp only [smul_eq_mul, mul_one]
      rfl
    refine ⟨?_, ?_⟩
    · rw [← he]
      exact integral_nonneg (fun X => sub_nonneg.mpr (hw1 X))
    · rw [← he]
      have h := integral_mono hi ((integrable_const (1 : ℝ)).indicator hE) hle
      simpa only [integral_indicator hE, setIntegral_const, smul_eq_mul, mul_one] using h
  have hdiff : (∫ X, Y X ∂upperTiltedParticleMeasure p N θ R J) -
      ∫ X, Y X ∂gibbsMeasure p N = z⁻¹ *
        (-(∫ X, (1 - w X) * Y X ∂gibbsMeasure p N) +
          (1 - z) * ∫ X, Y X ∂gibbsMeasure p N) := by
    have hi := MomentEvent.integrable_mul_of_abs_le hw hYi
      (fun X => (abs_of_nonneg (hw0 X)).trans_le (hw1 X))
    have he : (∫ X, (1 - w X) * Y X ∂gibbsMeasure p N) =
        (∫ X, Y X ∂gibbsMeasure p N) - ∫ X, w X * Y X ∂gibbsMeasure p N := by
      simp_rw [sub_mul, one_mul]
      exact integral_sub hYi hi
    rw [hformula, he]
    change z⁻¹ * (∫ X, w X * Y X ∂gibbsMeasure p N) -
      (∫ X, Y X ∂gibbsMeasure p N) = _
    field_simp [hz.ne']
    ring
  refine ⟨hYt, ?_⟩
  rw [hdiff, abs_mul, abs_of_pos (inv_pos.mpr hz)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hz.le)
  calc
    _ ≤ |∫ X, (1 - w X) * Y X ∂gibbsMeasure p N| +
        |(1 - z) * ∫ X, Y X ∂gibbsMeasure p N| := by
      simpa only [abs_neg] using abs_add_le (-(∫ X, (1 - w X) * Y X ∂gibbsMeasure p N)) _
    _ ≤ _ := by
      rw [abs_mul, abs_of_nonneg hzrare.1]
      nlinarith [mul_le_mul_of_nonneg_right hzrare.2
        (abs_nonneg (∫ X, Y X ∂gibbsMeasure p N))]

set_option backward.isDefEq.respectTransparency false in
/-- Uniform second moments of sums of selected physical gaps. The numerical
constant comes from the one-gap exponential moment, so it is independent
of temperature, exponent, volume and selected labels. -/
theorem gap_sum_second_moment :
    ∃ B : ℝ, 0 < B ∧ ∀ (p : Parameters) (N : ℕ+), 2 ≤ (N : ℕ) →
      ∀ J : Finset (Fin (N : ℕ)),
        Integrable (fun X : Riesz1.Configuration N => (∑ i ∈ J, gap X i.val) ^ 2)
          (gibbsMeasure p N) ∧
        (∫ X : Riesz1.Configuration N, (∑ i ∈ J, gap X i.val) ^ 2 ∂gibbsMeasure p N) ≤
          B * (J.card : ℝ) ^ 2 := by
  let c := Real.log 2 / 4
  have hc : 0 < c := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  let B := 3 * ((2 : ℝ) / Real.exp 1) ^ 2 / c ^ 2
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  intro p N hN J
  have hgap (i : Fin (N : ℕ)) :
      Integrable (fun X : Riesz1.Configuration N => gap X i.val ^ 2) (gibbsMeasure p N) ∧
        (∫ X : Riesz1.Configuration N, gap X i.val ^ 2 ∂gibbsMeasure p N) ≤ B := by
    have he := SingleGapTails.exponential_moment p N hN i.val
    have hh := Riesz1.moment_le_of_exp_moment_le hc
      (fun X : Riesz1.Configuration N => gap X i.val) (Riesz1.measurable_gap _)
      (fun X => (Riesz1.gap_pos X _).le) he.1 he.2 2 (by norm_num)
    simpa only [Real.rpow_two] using hh
  have henv : Integrable (fun X : Riesz1.Configuration N =>
      (J.card : ℝ) * ∑ i ∈ J, gap X i.val ^ 2) (gibbsMeasure p N) :=
    (integrable_finsetSum J (fun i _ => (hgap i).1)).const_mul _
  have hbound (X : Riesz1.Configuration N) :
      (∑ i ∈ J, gap X i.val) ^ 2 ≤ (J.card : ℝ) * ∑ i ∈ J, gap X i.val ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hi : Integrable (fun X : Riesz1.Configuration N =>
      (∑ i ∈ J, gap X i.val) ^ 2) (gibbsMeasure p N) := by
    refine henv.mono' ((Finset.measurable_sum J (fun i _ =>
      Riesz1.measurable_gap (i.val : ℤ))).pow_const 2).aestronglyMeasurable ?_
    exact Eventually.of_forall (fun X => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hbound X)
  refine ⟨hi, (integral_mono hi henv hbound).trans ?_⟩
  rw [integral_const_mul, integral_finsetSum J (fun i _ => (hgap i).1)]
  calc
    _ ≤ (J.card : ℝ) * ∑ _i ∈ J, B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => (hgap i).2)) (by positivity)
    _ = _ := by simp [pow_two]; ring

set_option backward.isDefEq.respectTransparency false in
/-- See Lemma B.1 of the paper, the uniform tilted-mean comparison.
The constant precedes every model parameter, volume, set and cutoff scale. -/
theorem gap_sum_upperTilt_mean :
    ∃ B : ℝ, 0 < B ∧ ∀ (p : Parameters) (N : ℕ+), 2 ≤ (N : ℕ) →
      ∀ (θ : PhysicalCutoff) (R : {R : ℝ // 0 < R}) (J : Finset (Fin (N : ℕ))),
        let E := 3 * J.card * Real.exp (-(Real.log 2 / 8) * R)
        E ≤ 1 / 2 →
          Integrable (fun X : Riesz1.Configuration N => ∑ i ∈ J, gap X i.val)
            (upperTiltedParticleMeasure p N θ R J) ∧
          |(∫ X : Riesz1.Configuration N, (∑ i ∈ J, gap X i.val)
              ∂upperTiltedParticleMeasure p N θ R J) - (J.card : ℝ)| ≤
            B * J.card * Real.sqrt E := by
  classical
  obtain ⟨B, hB, hmoment⟩ := gap_sum_second_moment
  refine ⟨2 * (Real.sqrt B + 1), by positivity, ?_⟩
  intro p N hN θ R J E hE
  have := gibbsMeasure_probability p N
  let Y := fun X : Riesz1.Configuration N => ∑ i ∈ J, gap X i.val
  have hY : Measurable Y := Finset.measurable_sum J (fun i _ => Riesz1.measurable_gap _)
  have hYi := integrable_finsetSum J (fun i _ => (SingleGapTails.gap_mean p N hN i.val).1)
  have hmean : ∫ X, Y X ∂gibbsMeasure p N = (J.card : ℝ) := by
    rw [integral_finsetSum J (fun i _ => (SingleGapTails.gap_mean p N hN i.val).1)]
    simp only [(SingleGapTails.gap_mean p N hN _).2, Finset.sum_const,
      nsmul_eq_mul, mul_one]
  obtain ⟨hY2, hsecond⟩ := hmoment p N hN J
  obtain ⟨ht, hm⟩ := upperTilt_mean_transfer p N θ R J Y hY hY2
  refine ⟨ht, ?_⟩
  change |(∫ X, Y X ∂upperTiltedParticleMeasure p N θ R J) - _| ≤ _
  rw [← hmean]
  apply hm.trans
  let z := ∫ X, Real.exp (-p.val.1 * upperGapPenalty θ R J X) ∂gibbsMeasure p N
  let q := (gibbsMeasure p N).real {X | upperGapPenalty θ R J X ≠ 0}
  have hq : q ≤ E := by
    have hh := upperGapPenalty_event_bound p N hN θ R J
    have hh' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
    change q ≤ (ENNReal.ofReal E).toReal at hh'
    rwa [ENNReal.toReal_ofReal (show 0 ≤ E by dsimp [E]; positivity)] at hh'
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hEsqrt : E ≤ Real.sqrt E := by
    nlinarith [Real.sq_sqrt hE0, Real.sqrt_nonneg E]
  have hqsqrt : Real.sqrt q ≤ Real.sqrt E := Real.sqrt_le_sqrt hq
  have hz : (1 / 2 : ℝ) ≤ z := by
    have hh := upperGapNormalizer_ge_half p N hN θ R J hE
    rw [upperGapNormalizer_eq_ofReal_integral] at hh
    have hz0 : 0 ≤ z := integral_nonneg (fun X => (Real.exp_pos _).le)
    have hh' : ENNReal.ofReal (1 / 2 : ℝ) ≤ ENNReal.ofReal z := by
      have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
        simp only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
      rw [hhalf]
      exact hh
    exact (ENNReal.ofReal_le_ofReal_iff hz0).mp hh'
  have hzinv : z⁻¹ ≤ 2 := by
    calc
      _ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hz
      _ = 2 := by norm_num
  have hsqrt : Real.sqrt (∫ X, Y X ^ 2 ∂gibbsMeasure p N) ≤ Real.sqrt B * J.card := by
    have hh := Real.sqrt_le_sqrt hsecond
    rw [Real.sqrt_mul hB.le, Real.sqrt_sq (by positivity)] at hh
    exact hh
  rw [hmean, abs_of_nonneg (by positivity)]
  change z⁻¹ * (Real.sqrt (∫ X, Y X ^ 2 ∂gibbsMeasure p N) * Real.sqrt q +
    (J.card : ℝ) * q) ≤ _
  calc
    _ ≤ 2 * (Real.sqrt B * J.card * Real.sqrt E + (J.card : ℝ) * Real.sqrt E) := by
      gcongr
      exact hq.trans hEsqrt
    _ = _ := by ring

private theorem retained_sum_coordinates {n m : ℕ} (σ : Equiv.Perm (Fin (n + m + 1)))
    (g : Fin (n + m + 1) → ℝ) :
    (∑ i ∈ Finset.univ.image (fun j : Fin n => σ (j.castAdd m).castSucc), g i) =
      ∑ i, (RetainedSimplex.coordinates n m σ (WithLp.toLp 2 g)).1 i := by
  classical
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i _
    rw [RetainedSimplex.coordinates_retained]
  · intro i _ j _ hij
    exact Fin.ext (congrArg (fun k : Fin (n + m + 1) => k.val) (σ.injective hij))

set_option backward.isDefEq.respectTransparency false in
/-- The retained Gaussian bound written directly on the actual tilted particle
law and the microscopic gaps, with the same tilted expectation. -/
theorem upperTilt_gap_sum_concentration (p : Parameters) (hs : 1 < p.val.2)
    (n m : ℕ) (hn : 1 ≤ n) (σ : Equiv.Perm (Fin (n + m + 1)))
    (θ : PhysicalCutoff) (R : {R : ℝ // 0 < R}) (hR : 1 ≤ (R : ℝ))
    (u : ℝ) (hu : 0 < u) :
    let J := Finset.univ.image (fun j : Fin n => σ (j.castAdd m).castSucc)
    let μ := upperTiltedParticleMeasure p (n + m).succPNat θ R J
    let Y := fun X : Riesz1.Configuration (n + m).succPNat => ∑ i ∈ J, gap X i.val
    μ {X | u ≤ |Y X - ∫ X, Y X ∂μ|} ≤
      ENNReal.ofReal (2 * Real.exp (-(p.val.1 * (R : ℝ) ^ (-p.val.2 - 2)) * u ^ 2 /
        (2 * n))) := by
  classical
  intro J μ Y
  let T := fun X : Riesz1.Configuration (n + m).succPNat =>
    (RetainedSimplex.coordinates n m σ (WithLp.toLp 2 (gapVector X))).1
  let F := fun x : EuclideanSpace ℝ (Fin n) => ∑ i, x i
  have hT : Measurable T := measurable_fst.comp
    ((RetainedSimplex.continuous_coordinates n m σ).measurable.comp
      ((PiLp.volume_preserving_toLp _).measurable.comp
        (Riesz1.measurable_gapVector (n + m).succPNat)))
  have hF : Measurable F := Finset.measurable_sum _ (fun i _ =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable)
  have hY (X) : Y X = F (T X) := retained_sum_coordinates σ (gapVector X)
  have hmean : (∫ x, F x ∂μ.map T) = ∫ X, Y X ∂μ := by
    rw [integral_map hT.aemeasurable hF.aestronglyMeasurable]
    exact integral_congr_ae (Eventually.of_forall (fun X => (hY X).symm))
  have hA : MeasurableSet {x | u ≤ |F x - ∫ y, F y ∂μ.map T|} :=
    measurableSet_le measurable_const ((hF.sub measurable_const).abs)
  have h := upperTilt_sum_concentration p hs n m hn σ θ R hR u hu
  change (μ.map T) {x | u ≤ |F x - ∫ y, F y ∂μ.map T|} ≤ _ at h
  rw [Measure.map_apply hT hA, hmean] at h
  simpa only [preimage_ofPred_eq, ← hY] using h

private theorem measure_le_add_of_totalVariation {E : Type*} [MeasurableSpace E]
    (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {b : ℝ≥0∞} (h : totalVariation μ ν ≤ b)
    {A : Set E} (hA : MeasurableSet A) : μ A ≤ b + ν A := by
  have hd : (μ A - ν A) + (ν A - μ A) ≤ totalVariation μ ν := by
    exact le_iSup (fun B : {B : Set E // MeasurableSet B} =>
      (μ B.val - ν B.val) + (ν B.val - μ B.val)) ⟨A, hA⟩
  apply tsub_le_iff_right.mp
  exact (le_add_of_nonneg_right zero_le).trans (hd.trans h)

set_option backward.isDefEq.respectTransparency false in
/-- See Lemma B.1 of the paper, the finite-scale untilted estimate.
The two numerical conditions are on the explicit cutoff error and scale. -/
theorem shortRange_finite_scale :
    ∃ B : ℝ, 0 < B ∧ ∀ (p : Parameters), 1 < p.val.2 →
      ∀ (n m : ℕ), 1 ≤ n → ∀ (σ : Equiv.Perm (Fin (n + m + 1)))
      (R : {R : ℝ // 0 < R}), 1 ≤ (R : ℝ) →
      ∀ t : ℝ, 0 < t →
        let J := Finset.univ.image (fun j : Fin n => σ (j.castAdd m).castSucc)
        let E := 3 * n * Real.exp (-(Real.log 2 / 8) * R)
        E ≤ 1 / 2 → B * n * Real.sqrt E ≤ t / 2 →
          (gibbsMeasure p (n + m).succPNat)
            {X | t ≤ |(∑ i ∈ J, gap X i.val) - (n : ℝ)|} ≤
              ENNReal.ofReal (2 * Real.exp
                (-(p.val.1 * (R : ℝ) ^ (-p.val.2 - 2)) * t ^ 2 / (8 * n)) + E) := by
  classical
  obtain ⟨B, hB, hmean⟩ := gap_sum_upperTilt_mean
  refine ⟨B, hB, ?_⟩
  intro p hs n m hn σ R hR t ht J E hE hsize
  obtain ⟨θ⟩ := DefinitionSanity.physicalCutoff_nonempty
  let N := (n + m).succPNat
  let Y := fun X : Riesz1.Configuration N => ∑ i ∈ J, gap X i.val
  let ν := upperTiltedParticleMeasure p N θ R J
  have := gibbsMeasure_probability p N
  have := upperTiltedParticleMeasure_probability p N θ R J
  have hN : 2 ≤ (N : ℕ) := by change 2 ≤ n + m + 1; omega
  have hJn : J.card = n := by
    change (Finset.univ.image (fun j : Fin n => σ (j.castAdd m).castSucc)).card = n
    have hinj : Function.Injective (fun j : Fin n => σ (j.castAdd m).castSucc) :=
      fun i j hij => Fin.ext (congrArg (fun k : Fin (n + m + 1) => k.val) (σ.injective hij))
    rw [Finset.card_image_of_injective _ hinj]
    exact Finset.card_fin n
  have hE' : 3 * (J.card : ℝ) * Real.exp (-(Real.log 2 / 8) * R) = E := by rw [hJn]
  have hmean' := (hmean p N hN θ R J (by rw [hE']; exact hE)).2
  rw [hJn] at hmean'
  have hm : |(∫ X, Y X ∂ν) - (n : ℝ)| ≤ t / 2 := hmean'.trans hsize
  have hc := upperTilt_gap_sum_concentration p hs n m hn σ θ R hR (t / 2) (by linarith)
  change ν {X | t / 2 ≤ |Y X - ∫ X, Y X ∂ν|} ≤ _ at hc
  have hsub : {X | t ≤ |Y X - (n : ℝ)|} ⊆
      {X | t / 2 ≤ |Y X - ∫ X, Y X ∂ν|} := by
    intro X hX
    have htri := abs_sub_le (Y X) (∫ X, Y X ∂ν) (n : ℝ)
    change t ≤ |Y X - (n : ℝ)| at hX
    change t / 2 ≤ |Y X - ∫ X, Y X ∂ν|
    linarith
  have hY : Measurable Y := Finset.measurable_sum J (fun i _ => Riesz1.measurable_gap _)
  have hA : MeasurableSet {X | t ≤ |Y X - (n : ℝ)|} :=
    measurableSet_le measurable_const ((hY.sub measurable_const).abs)
  have htv := (upperTiltedParticleMeasure_totalVariation p N θ R J).trans
    (upperGapPenalty_event_bound p N hN θ R J)
  rw [hE'] at htv
  have he := measure_le_add_of_totalVariation (gibbsMeasure p N) ν htv hA
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  calc
    _ ≤ ENNReal.ofReal E + ν {X | t / 2 ≤ |Y X - ∫ X, Y X ∂ν|} :=
      he.trans (add_le_add le_rfl (measure_mono hsub))
    _ ≤ ENNReal.ofReal E + ENNReal.ofReal (2 * Real.exp
        (-(p.val.1 * (R : ℝ) ^ (-p.val.2 - 2)) * (t / 2) ^ 2 / (2 * n))) :=
      add_le_add le_rfl hc
    _ = _ := by
      rw [← ENNReal.ofReal_add hE0 (by positivity)]
      congr 1
      rw [show -(p.val.1 * (R : ℝ) ^ (-p.val.2 - 2)) * (t / 2) ^ 2 / (2 * n) =
        -(p.val.1 * (R : ℝ) ^ (-p.val.2 - 2)) * t ^ 2 / (8 * n) by ring]
      ring

end LocalLawInternal

end Riesz2.DecayShort
