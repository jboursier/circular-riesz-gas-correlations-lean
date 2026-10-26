/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.LocalLawPart4
public import Riesz2.HelfferSjostrand.MarginalHessianPart5
import all Riesz2.HelfferSjostrand.ProperMarginalChart

/-!
# Quadratic subtraction before marginalization in both exponent regimes

The coercivity argument of Lemma 4.7 of the paper: nearest
pairs and the upper forcing control the same quadratic before Prékopa is
applied to the affine retained/exterior chart `RetainedSimplex.chart`.
The inverse penalty is convex.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators ContDiff
namespace Riesz2.PaperMarginalHessian
open Riesz2.DecayShort
set_option backward.isDefEq.respectTransparency false

/-- Nearest-pair plus forcing curvature in Lemma 4.7 of the paper. -/
theorem paper_scalar_curvature (θ : PhysicalCutoff) {s x R : ℝ}
    (hs : 0 < s) (hx : 0 < x) (hR : 1 ≤ R) :
    min 1 (s * (s + 1)) * R ^ (-s - 2) ≤ s * (s + 1) * x ^ (-s - 2) +
      deriv (deriv θ.val) (x / R) / R ^ 2 := by
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  obtain ⟨C, _, hθ, hθlarge⟩ := θ.property.2.2.2.2
  have hθnonneg := (hθ (x / R) (div_pos hx hR0)).1
  have hc : 0 ≤ s * (s + 1) := by positivity
  by_cases hsmall : x ≤ R
  · have hpow := Real.rpow_le_rpow_of_nonpos hx hsmall (show -s - 2 ≤ 0 by linarith)
    calc
      _ ≤ s * (s + 1) * R ^ (-s - 2) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.rpow_nonneg hR0.le _)
      _ ≤ s * (s + 1) * x ^ (-s - 2) := mul_le_mul_of_nonneg_left hpow hc
      _ ≤ _ := le_add_of_nonneg_right (div_nonneg hθnonneg (sq_nonneg R))
  · have hh := hθlarge (x / R) ((one_le_div hR0).mpr (le_of_not_ge hsmall))
    have hpow := Real.rpow_le_rpow_of_exponent_le hR (show -s - 2 ≤ -(2 : ℝ) by linarith)
    have he : R ^ (-(2 : ℝ)) = 1 / R ^ 2 := by
      rw [Real.rpow_neg hR0.le, Real.rpow_two, one_div]
    rw [he] at hpow
    calc
      _ ≤ R ^ (-s - 2) :=
        mul_le_of_le_one_left (Real.rpow_nonneg hR0.le _) (min_le_left _ _)
      _ ≤ 1 / R ^ 2 := hpow
      _ ≤ deriv (deriv θ.val) (x / R) / R ^ 2 :=
        div_le_div_of_nonneg_right hh (sq_nonneg R)
      _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hc (Real.rpow_nonneg hx.le _))

/-- Joint curvature before integration in Lemma 4.7 of the paper. -/
theorem paper_full_curvature (p : Parameters)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (θ : PhysicalCutoff)
    (R : {R : ℝ // 0 < R}) (hR : 1 ≤ (R : ℝ))
    (J : Finset (Fin (N : ℕ))) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ∀ (y : Fin (N : ℕ) → ℝ), y ∈ Riesz1.gapSimplex N →
        ∀ u : EuclideanSpace ℝ (Fin (N : ℕ)),
          min 1 (p.val.2 * (p.val.2 + 1)) * (R : ℝ) ^ (-p.val.2 - 2) *
              (∑ i ∈ J, (u i) ^ 2) ≤
            fderiv ℝ (fderiv ℝ (fun z => W z + ∑ i ∈ J, θ.val (z i / R)))
              (WithLp.toLp 2 y) u u := by
  classical
  obtain ⟨W, hW, hval, _, _, hlow, _⟩ :=
    (PhysicalEnergy.restriction_and_derivatives p N hN).2.2
  refine ⟨W, hW, hval, ?_⟩
  intro y hy u
  let x : EuclideanSpace ℝ (Fin (N : ℕ)) := WithLp.toLp 2 y
  let F : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ := fun z => ∑ i ∈ J, θ.val (z i / R)
  have hx : x ∈ gapAmbientDomain N := PhysicalEnergy.simplex_subset_ambient N y hy
  have hW₂ : ContDiffAt ℝ 2 W x :=
    (hW.of_le (by norm_num)).contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hx)
  have hF₂ : ContDiffAt ℝ 2 F x := DecayShort.upperGapPenalty_contDiffAt θ R J x hy.1
  have he := PhysicalCollision.internal_hessian_add hW₂ hF₂ u u
  rw [DecayShort.upperGapPenalty_hessian θ R J x hy.1 u u] at he
  change _ ≤ fderiv ℝ (fderiv ℝ (fun z => W z + F z)) x u u
  rw [he]
  have hsub : (∑ i ∈ J, y i ^ (-p.val.2 - 2) * (u i) ^ 2) ≤
      ∑ i, y i ^ (-p.val.2 - 2) * (u i) ^ 2 :=
    Finset.sum_le_univ_sum_of_nonneg fun i =>
      mul_nonneg (Real.rpow_nonneg (hy.1 i).le _) (sq_nonneg _)
  have hc : 0 ≤ p.val.2 * (p.val.2 + 1) :=
    mul_nonneg p.property.2.1.le (by linarith [p.property.2.1])
  have hbase := (mul_le_mul_of_nonneg_left hsub hc).trans (hlow y hy u)
  have hscalar : min 1 (p.val.2 * (p.val.2 + 1)) * (R : ℝ) ^ (-p.val.2 - 2) *
      (∑ i ∈ J, (u i) ^ 2) ≤
        p.val.2 * (p.val.2 + 1) * (∑ i ∈ J, y i ^ (-p.val.2 - 2) * (u i) ^ 2) +
        ∑ i ∈ J, deriv (deriv θ.val) (y i / R) / (R : ℝ) ^ 2 * (u i) ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have h := mul_le_mul_of_nonneg_right
      (paper_scalar_curvature θ p.property.2.1 (hy.1 i) hR) (sq_nonneg (u i))
    nlinarith only [h]
  simp only [x, ← pow_two]
  exact hscalar.trans (by linarith only [hbase])

/-- Active quadratic Hessian in Lemma 4.7 of the paper. -/
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

/-- Subtract the common active quadratic before integration, as in Lemma 4.7. -/
theorem paper_tilted_joint_quadratic_convex (p : Parameters)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (θ : PhysicalCutoff)
    (R : {R : ℝ // 0 < R}) (hR : 1 ≤ (R : ℝ))
    (J : Finset (Fin (N : ℕ))) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ConvexOn ℝ (WithLp.ofLp ⁻¹' Riesz1.gapSimplex N)
        (fun y => W y + ∑ i ∈ J, θ.val (y i / R) -
          (min 1 (p.val.2*(p.val.2+1)) * (R : ℝ) ^ (-p.val.2 - 2)) / 2 * ∑ i ∈ J, (y i) ^ 2) := by
  classical
  obtain ⟨W, hW, hval, hcurv⟩ := paper_full_curvature p N hN θ R hR J
  let F : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ :=
    fun y => W y + ∑ i ∈ J, θ.val (y i / R)
  let Q : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ :=
    fun y => (min 1 (p.val.2*(p.val.2+1)) * (R : ℝ) ^ (-p.val.2 - 2)) / 2 * ∑ i ∈ J, (y i) ^ 2
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
      (min 1 (p.val.2*(p.val.2+1)) * (R : ℝ) ^ (-p.val.2 - 2)) * ∑ i ∈ J, ((w - z) i) ^ 2 from
    selected_quadratic_hessian J _ y (w - z)]
  exact sub_nonneg.mpr (hcurv (WithLp.ofLp y) hy (w - z))

/-- The affine retained/exterior chart retains active sums in Lemma 4.7. -/
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
/-- The affine-chart residual in Lemma 4.7 of the paper.
The Gibbs factor is exactly the density of the actual upper tilt.
The retained labels are arbitrary, and the exterior dimension may be zero. -/
theorem paper_tilted_chart_residual (p : Parameters)
    (n m : ℕ) (hn : 1 ≤ n) (σ : Equiv.Perm (Fin (n + m + 1)))
    (θ : PhysicalCutoff) (R : {R : ℝ // 0 < R}) (hR : 1 ≤ (R : ℝ)) :
    let J := Finset.univ.image (fun j : Fin n => σ (j.castAdd m).castSucc)
    let Ω := RetainedSimplex.domain n m ((n + m : ℕ) + 1)
    ∃ A : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) → ℝ,
      ConvexOn ℝ Ω (fun q => A q -
        (p.val.1 * (min 1 (p.val.2*(p.val.2+1)) * (R : ℝ) ^ (-p.val.2 - 2))) / 2 * ‖q.1‖ ^ 2) ∧
      ProperMarginalChart.penalizedChartDensity p n m σ θ R.val⁻¹ J false =
        fun q => ENNReal.ofReal (Ω.indicator (fun q => Real.exp (-A q)) q) := by
  classical
  intro J Ω
  let N : ℕ+ := ⟨n + m + 1, by omega⟩
  let T := RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ
  obtain ⟨W, _, hval, hc⟩ := paper_tilted_joint_quadratic_convex p N
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
      (min 1 (p.val.2*(p.val.2+1)) * (R : ℝ) ^ (-p.val.2 - 2)) / 2 * ∑ i ∈ J, (T q i) ^ 2) =
      A q - (p.val.1 * (min 1 (p.val.2*(p.val.2+1)) * (R : ℝ) ^ (-p.val.2 - 2))) / 2 * ‖q.1‖ ^ 2 := by
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
/-- Lemma 4.7 of the paper: strong convexity of the negative
logarithm of the actual retained fibre density. This proves the nonsmooth
curvature statement without assuming any marginal regularity. -/
theorem paper_marginal_residual_convex (p : Parameters)
    (n m : ℕ) (hn : 1 ≤ n) (σ : Equiv.Perm (Fin (n + m + 1)))
    (θ : PhysicalCutoff) (R : {R : ℝ // 0 < R}) (hR : 1 ≤ (R : ℝ)) :
    let J := Finset.univ.image (fun j : Fin n => σ (j.castAdd m).castSucc)
    let D := ProperMarginalChart.penalizedChartDensity p n m σ θ R.val⁻¹ J false
    ConvexOn ℝ (AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
      (fun x => -Real.log (AffineFibre.fibreMass volume D x).toReal -
        (p.val.1 * (min 1 (p.val.2*(p.val.2+1)) * (R : ℝ) ^ (-p.val.2 - 2))) / 2 * ‖x‖ ^ 2) := by
  classical
  intro J D
  let Ω := RetainedSimplex.domain n m ((n + m : ℕ) + 1)
  let Q := fun x : EuclideanSpace ℝ (Fin n) =>
    (p.val.1 * (min 1 (p.val.2*(p.val.2+1)) * (R : ℝ) ^ (-p.val.2 - 2))) / 2 * ‖x‖ ^ 2
  obtain ⟨A, hc, hD⟩ := paper_tilted_chart_residual p n m hn σ θ R hR
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

/-- Restore the quadratic after Prékopa, as in Lemma 4.7 of the paper. -/
theorem paper_upper_marginal_hessian (p : Parameters)
    (n m : ℕ) (hn : 1 ≤ n) (σ : Equiv.Perm (Fin (n + m + 1)))
    (θ : PhysicalCutoff) (R : {R : ℝ // 0 < R}) (hR : 1 ≤ (R : ℝ)) :
    let J := Finset.univ.image (fun j : Fin n => σ (j.castAdd m).castSucc)
    let D := ProperMarginalChart.penalizedChartDensity p n m σ θ R.val⁻¹ J false
    let V := fun x => -Real.log (AffineFibre.fibreMass volume D x).toReal
    ContDiffOn ℝ 2 V (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) ∧
      ∀ x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
        ∀ v : EuclideanSpace ℝ (Fin n),
          p.val.1 * (min 1 (p.val.2*(p.val.2+1)) * (R : ℝ) ^ (-p.val.2 - 2)) * ‖v‖ ^ 2 ≤
            fderiv ℝ (fderiv ℝ V) x v v := by
  intro J D V
  let U := AffineSimplex.chartDomain n ((n + m : ℕ) + 1)
  let a := p.val.1 * (min 1 (p.val.2*(p.val.2+1)) * (R : ℝ) ^ (-p.val.2 - 2))
  let Q := fun x : EuclideanSpace ℝ (Fin n) => a / 2 * ‖x‖ ^ 2
  have hV : ContDiffOn ℝ 2 V U := upperTilt_marginal_contDiff p n m hn σ θ R
  have hQ : ContDiff ℝ 2 Q := contDiff_const.mul (contDiff_norm_sq ℝ)
  have ho : IsOpen U := AffineSimplex.isOpen_chartDomain _ _
  refine ⟨hV, ?_⟩
  intro x hx v
  have hc : ConvexOn ℝ U (fun x => V x - Q x) :=
    paper_marginal_residual_convex p n m hn σ θ R hR
  have hnonneg := Riesz1.fderiv_fderiv_nonneg_of_convexOn ho hc.1 hc
    (hV.sub hQ.contDiffOn) hx v
  have heq : fderiv ℝ (fun x => V x - Q x) =ᶠ[𝓝 x]
      fun z => fderiv ℝ V z - fderiv ℝ Q z := by
    filter_upwards [ho.mem_nhds hx] with z hz
    exact fderiv_fun_sub
      ((hV.differentiableOn (by norm_num)).differentiableAt (ho.mem_nhds hz))
      (hQ.differentiable (by norm_num)).differentiableAt
  have hVD : DifferentiableAt ℝ (fderiv ℝ V) x :=
    ((hV.fderiv_of_isOpen ho (by norm_num : 1 + 1 ≤ (2 : WithTop ℕ∞))).differentiableOn
      (by norm_num)).differentiableAt (ho.mem_nhds hx)
  have hQD : DifferentiableAt ℝ (fderiv ℝ Q) x :=
    (((hQ.contDiffOn (s := Set.univ)).fderiv_of_isOpen isOpen_univ
      (by norm_num : 1 + 1 ≤ (2 : WithTop ℕ∞))).differentiableOn
        (by norm_num)).differentiableAt (isOpen_univ.mem_nhds (Set.mem_univ x))
  rw [heq.fderiv_eq, fderiv_fun_sub hVD hQD] at hnonneg
  have hfirst : fderiv ℝ Q = fun z => a • innerSL ℝ z := by
    funext z
    rw [((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_mul (a / 2)).fderiv]
    ext u
    simp only [smul_apply, smul_eq_mul, two_smul, add_apply]
    ring
  have hsecond : fderiv ℝ (fderiv ℝ Q) x v v = a * ‖v‖ ^ 2 := by
    rw [hfirst]
    erw [((innerSL ℝ).hasFDerivAt (x := x) |>.const_smul a).fderiv]
    change a * innerSL ℝ v v = a * ‖v‖ ^ 2
    congr 1
    exact real_inner_self_eq_norm_sq v
  simp only [sub_apply, sub_nonneg] at hnonneg
  rw [hsecond] at hnonneg
  exact hnonneg


/-- The upper-tilted potential in Lemma 4.7 of the paper,
with its quadratic subtracted before integration. This is also the proper
long-range curvature input, for any positive forcing scale `R ≥ 1`. -/
theorem paper_upper_potential_hessian (p : Parameters)
    (n m : ℕ) (hn : 1 ≤ n) (σ : Equiv.Perm (Fin (n + m + 1)))
    (θ : PhysicalCutoff) (R : {R : ℝ // 0 < R}) (hR : 1 ≤ (R : ℝ)) :
    let V := fun x : EuclideanSpace ℝ (Fin n) =>
      p.val.1 * ∑ i, θ.val (x i / R) - Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p n m σ (x,z)).toReal)
    ContDiffOn ℝ ∞ V (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) ∧
      ∀ x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
        ∀ v : EuclideanSpace ℝ (Fin n),
          p.val.1 * min 1 (p.val.2*(p.val.2+1)) * R.val^(-p.val.2-2) * ‖v‖^2 ≤
            fderiv ℝ (fderiv ℝ V) x v v := by
  intro V
  have hsm : ContDiffOn ℝ ∞ V (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) := by
    simpa only [V,div_eq_mul_inv,mul_comm,Bool.false_eq_true,↓reduceIte,add_zero] using
      MarginalHessian.physical_penalized_marginal_potential_smooth p n m hn σ θ
        (inv_pos.mpr R.property) Finset.univ false
  refine ⟨hsm,fun x hx v => ?_⟩
  obtain ⟨_,hH⟩ := paper_upper_marginal_hessian p n m hn σ θ R hR
  let J := Finset.univ.image (fun i : Fin n => σ (i.castAdd m).castSucc)
  let D := ProperMarginalChart.penalizedChartDensity p n m σ θ R.val⁻¹ J false
  have he : (fun y => -Real.log (AffineFibre.fibreMass volume D y).toReal) =ᶠ[𝓝 x] V := by
    filter_upwards [(AffineSimplex.isOpen_chartDomain n _).mem_nhds hx] with y hy
    rw [upperTilt_marginal_potential p n m hn σ θ R y hy,
      ← (MarginalHessian.physical_marginal_normalizer p n m hn σ hy).1]
    dsimp only [V]
    ring
  rw [← he.fderiv.fderiv_eq]
  simpa only [mul_assoc] using hH x hx v

/-- Convexity of the optional inverse penalty in Lemma 4.7. -/
theorem paper_inverse_retained_penalty (n : ℕ) (L : ℝ) (θ : PhysicalCutoff)
    {a : ℝ} (ha : 0 < a) :
    ContDiffOn ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) =>
      ∑ i, θ.val (a * (x i)⁻¹)) (AffineSimplex.chartDomain n L) ∧
    ConvexOn ℝ (AffineSimplex.chartDomain n L)
      (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, θ.val (a * (x i)⁻¹)) := by
  constructor
  · apply ContDiffOn.sum
    intro i _ x hx
    exact ((PhysicalCollision.cutoff_contDiffAt θ (mul_pos ha (inv_pos.mpr (hx.1 i)))).comp x
      (contDiffAt_const.mul ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt.inv
        (hx.1 i).ne'))).contDiffWithinAt
  · have hterm (i : Fin n) : ConvexOn ℝ (AffineSimplex.chartDomain n L)
        (fun x : EuclideanSpace ℝ (Fin n) => θ.val (a * (x i)⁻¹)) := by
      refine ⟨AffineSimplex.convex_chartDomain n L, fun x hx y hy α β hα hβ hab => ?_⟩
      simpa only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, div_eq_mul_inv] using
        (PhysicalCollision.inverse_penalty_convex θ ha).2 (hx.1 i) (hy.1 i) hα hβ hab
    refine ⟨AffineSimplex.convex_chartDomain n L, fun x hx y hy α β hα hβ hab => ?_⟩
    have ht := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => (hterm i).2 hx hy hα hβ hab)
    simpa only [smul_eq_mul, Finset.mul_sum, Finset.sum_add_distrib] using ht

/-- The two-regime, two-penalty coercivity conclusion of Lemma 4.7 of the paper. -/
theorem paper_marginal_hessian (p : Parameters)
    (n m : ℕ) (hn : 1 ≤ n) (σ : Equiv.Perm (Fin (n + m + 1)))
    (θ : PhysicalCutoff) (h : ℝ) (hh : 0 < h) (b : Bool) :
    let a := ((n : ℝ) ^ h)⁻¹
    let P := fun x : EuclideanSpace ℝ (Fin n) =>
      ∑ i, (θ.val (a * x i) + if b then θ.val (a * (x i)⁻¹) else 0)
    let K := fun x => p.val.1⁻¹ * (p.val.1 * P x -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p n m σ (x,z)).toReal))
    ContDiffOn ℝ ∞ K (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) ∧
      ∀ x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
        ∀ v : EuclideanSpace ℝ (Fin n),
          min 1 (p.val.2*(p.val.2+1)) * (n : ℝ) ^ (-(p.val.2 + 2) * h) * ‖v‖ ^ 2 ≤
            fderiv ℝ (fderiv ℝ K) x v v := by
  intro a P K
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  let R : {R : ℝ // 0 < R} := ⟨(n : ℝ) ^ h, Real.rpow_pos_of_pos hnpos h⟩
  have ha : 0 < a := inv_pos.mpr R.property
  have hR : 1 ≤ (R : ℝ) := Real.one_le_rpow hnR hh.le
  have hsm := MarginalHessian.physical_penalized_marginal_potential_smooth
    p n m hn σ θ ha Finset.univ b
  refine ⟨contDiffOn_const.mul hsm, fun x hx v => ?_⟩
  let P₀ := fun x : EuclideanSpace ℝ (Fin n) => ∑ i, θ.val (a * x i)
  let I := fun x : EuclideanSpace ℝ (Fin n) => ∑ i, θ.val (a * (x i)⁻¹)
  let V₀ := fun x => p.val.1 * P₀ x - Real.log (∫ z : EuclideanSpace ℝ (Fin m),
    (ProperMarginalChart.chartDensity p n m σ (x,z)).toReal)
  let J := Finset.univ.image (fun i : Fin n => σ (i.castAdd m).castSucc)
  let D := ProperMarginalChart.penalizedChartDensity p n m σ θ R.val⁻¹ J false
  let V := fun x => -Real.log (AffineFibre.fibreMass volume D x).toReal
  obtain ⟨hV, hH⟩ := paper_upper_marginal_hessian p n m hn σ θ R hR
  have hsame : V =ᶠ[𝓝 x] V₀ := by
    filter_upwards [(AffineSimplex.isOpen_chartDomain n _).mem_nhds hx] with y hy
    change -Real.log (AffineFibre.fibreMass volume D y).toReal = V₀ y
    rw [upperTilt_marginal_potential p n m hn σ θ R y hy]
    rw [← (MarginalHessian.physical_marginal_normalizer p n m hn σ hy).1]
    dsimp only [V₀, P₀, a, R]
    have he : (∑ i : Fin n, θ.val (y i / (n : ℝ) ^ h)) =
        ∑ i : Fin n, θ.val (((n : ℝ) ^ h)⁻¹ * y i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg θ.val (by ring)
    rw [he]
    ring
  have hV₀ : ContDiffAt ℝ 2 V₀ x :=
    (hV.contDiffAt ((AffineSimplex.isOpen_chartDomain n _).mem_nhds hx)).congr_of_eventuallyEq
      hsame.symm
  obtain ⟨hI, hcI⟩ := paper_inverse_retained_penalty n ((n + m : ℕ) + 1) θ ha
  have hIx : ContDiffAt ℝ 2 I x := (hI.of_le (by norm_num)).contDiffAt
    ((AffineSimplex.isOpen_chartDomain n _).mem_nhds hx)
  have hInonneg : 0 ≤ fderiv ℝ (fderiv ℝ I) x v v :=
    Riesz1.fderiv_fderiv_nonneg_of_convexOn (AffineSimplex.isOpen_chartDomain n _)
      hcI.1 hcI (hI.of_le (by norm_num)) hx v
  have hbase : p.val.1 * (min 1 (p.val.2*(p.val.2+1)) * R.val ^ (-p.val.2 - 2)) * ‖v‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ V₀) x v v := by
    rw [← hsame.fderiv.fderiv_eq]
    exact hH x hx v
  have he : p.val.1⁻¹ * (p.val.1 * (min 1 (p.val.2*(p.val.2+1)) * R.val ^ (-p.val.2 - 2)) * ‖v‖ ^ 2) =
      min 1 (p.val.2*(p.val.2+1)) * (n : ℝ) ^ (-(p.val.2 + 2) * h) * ‖v‖ ^ 2 := by
    rw [← mul_assoc, inv_mul_cancel_left₀ p.property.1.ne']
    dsimp only [R]
    rw [← Real.rpow_mul hnpos.le]
    ring_nf
  have hK : K = fun y => p.val.1⁻¹ * (V₀ y + if b then p.val.1 * I y else 0) := by
    funext y
    cases b <;> simp only [K, P, V₀, P₀, I, Bool.false_eq_true, ↓reduceIte, add_zero,
      Finset.sum_add_distrib]; ring
  rw [hK]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
    rw [PhysicalCollision.internal_hessian_const_mul hV₀]
    exact he ▸ mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr p.property.1.le)
  · simp only [↓reduceIte]
    rw [PhysicalCollision.internal_hessian_const_mul (hV₀.add (contDiffAt_const.mul hIx)),
      PhysicalCollision.internal_hessian_add hV₀ (contDiffAt_const.mul hIx),
      PhysicalCollision.internal_hessian_const_mul hIx]
    rw [← he]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr p.property.1.le)
    exact hbase.trans (le_add_of_nonneg_right (mul_nonneg p.property.1.le hInonneg))


end Riesz2.PaperMarginalHessian
