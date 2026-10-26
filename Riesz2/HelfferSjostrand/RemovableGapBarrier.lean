/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.PhysicalEnergy
public import Riesz2.ToMathlib.ConvexTangentHessian
public import Riesz2.ToMathlib.LogConcaveSurvivalSupport
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Riesz1.ToMathlib.LogConcave.NegativePower
public import Riesz2.Preliminaries.GapSymmetries
public import Riesz1.Rigidity.NoExplosionMarginalPotential
public import Riesz1.Rigidity.GapLawMoments
public import Riesz2.Frozen.OfLong

/-!
# Removing nearest-gap barriers

The convexity assertion of the proof of Lemma 2.1
holds intrinsically on the mass simplex, in both exponent regimes. In
particular, the two-particle case uses the doubled tangent Hessian bound,
rather than an ambient doubled bound.
-/

public section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

namespace Riesz2.RemovableGapBarrier

private theorem rpow_second_deriv (s x : ℝ) :
    deriv (deriv (fun t : ℝ => t ^ (-s))) x =
      s * (s + 1) * x ^ (-s - 2) := by
  have he : deriv (fun t : ℝ => t ^ (-s)) = fun t => -s * t ^ (-s - 1) :=
    funext (fun t => Real.deriv_rpow_const t (-s))
  rw [he, deriv_const_mul_field, Real.deriv_rpow_const]
  rw [show -s - 1 - 1 = -s - 2 by ring]
  ring

private theorem barrier_smooth {N : ℕ+} (s : ℝ)
    {y : EuclideanSpace ℝ (Fin (N : ℕ))} (hy : ∀ i, 0 < y i) :
    ContDiffAt ℝ 2 (fun z : EuclideanSpace ℝ (Fin (N : ℕ)) =>
      ∑ i, 2 * (z i) ^ (-s)) y := by
  apply ContDiffAt.sum
  intro i _
  have hi : ContDiffAt ℝ 2 (fun z : EuclideanSpace ℝ (Fin (N : ℕ)) => z i) y :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (N : ℕ)) i).contDiff.contDiffAt
  exact contDiffAt_const.mul (hi.rpow_const_of_ne (hy i).ne')

private theorem barrier_hessian {N : ℕ+} (s : ℝ)
    {y : EuclideanSpace ℝ (Fin (N : ℕ))} (hy : ∀ i, 0 < y i)
    (u : EuclideanSpace ℝ (Fin (N : ℕ))) :
    fderiv ℝ (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin (N : ℕ)) =>
      ∑ i, 2 * (z i) ^ (-s))) y u u =
      2 * (s * (s + 1)) * ∑ i, (y i) ^ (-s - 2) * (u i) ^ 2 := by
  have hK : ContDiffOn ℝ 2 (fun t : ℝ => t ^ (-s)) (Ioi (0 : ℝ)) :=
    contDiffOn_id.rpow_const_of_ne (fun t ht => ht.ne')
  have he := (finite_linear_potential_derivatives (fun _ : Fin (N : ℕ) => 2)
    (fun (_ : Fin (N : ℕ)) (t : ℝ) => t ^ (-s)) (fun i => EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (N : ℕ)) i)
    (fun _ => Ioi (0 : ℝ)) (fun _ => isOpen_Ioi) (fun _ => hK)
    y hy u u).2
  simp only [rpow_second_deriv, EuclideanSpace.coe_proj, ← pow_two] at he
  rw [he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem euclidean_simplex_convex (N : ℕ+) :
    Convex ℝ ((WithLp.ofLp : EuclideanSpace ℝ (Fin (N : ℕ)) → _) ⁻¹' Riesz1.gapSimplex N) := by
  exact (Riesz1.convex_gapSimplex N).linear_preimage
    (WithLp.linearEquiv 2 ℝ (Fin (N : ℕ) → ℝ)).toLinearMap

/-- See the proof of Lemma 2.1 in the paper, the convex removability clause
in both exponent regimes. The realizing function agrees with the ambient energy on its whole domain. Its residual after removing all
nearest-gap barriers is convex on the positive mass simplex, including
`N = 2`. No temperature or curvature hypothesis is added. -/
theorem nearest_gap_barrier_convex (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ConvexOn ℝ (WithLp.ofLp ⁻¹' Riesz1.gapSimplex N)
        (fun y => W y - 2 * ∑ i, (y i) ^ (-p.val.2)) := by
  obtain ⟨_, _, W, hW, hval, _, _, _, _, htangent⟩ :=
    PhysicalEnergy.restriction_and_derivatives p N hN
  let B : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ := fun y => ∑ i, 2 * (y i) ^ (-p.val.2)
  have hdiff (y : EuclideanSpace ℝ (Fin (N : ℕ)))
      (hy : y ∈ WithLp.ofLp ⁻¹' Riesz1.gapSimplex N) : ContDiffAt ℝ 2 (W - B) y := by
    have hyU := PhysicalEnergy.simplex_subset_ambient N (WithLp.ofLp y) hy
    have hWy := (hW y hyU).contDiffAt (PhysicalEnergy.isOpen_gapAmbientDomain N |>.mem_nhds hyU)
    exact (hWy.of_le (by simp)).sub (barrier_smooth p.val.2 hy.1)
  have hH (y : EuclideanSpace ℝ (Fin (N : ℕ)))
      (hy : y ∈ WithLp.ofLp ⁻¹' Riesz1.gapSimplex N)
      (u : EuclideanSpace ℝ (Fin (N : ℕ))) (hu : ∑ i, u i = 0) :
      0 ≤ fderiv ℝ (fderiv ℝ (W - B)) y u u := by
    have hyU := PhysicalEnergy.simplex_subset_ambient N (WithLp.ofLp y) hy
    have hWy : ContDiffAt ℝ 2 W y :=
      ((hW y hyU).contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hyU)).of_le
        (by simp)
    have hBy : ContDiffAt ℝ 2 B y := barrier_smooth p.val.2 hy.1
    have he : fderiv ℝ (W - B) =ᶠ[𝓝 y] (fun z => fderiv ℝ W z - fderiv ℝ B z) := by
      filter_upwards [hWy.eventually (by norm_num),
        hBy.eventually (by norm_num)] with z hzW hzB
      exact fderiv_sub (hzW.differentiableAt (by norm_num))
        (hzB.differentiableAt (by norm_num))
    have hdW := (hWy.fderiv_right (by norm_num : 1 + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
      (by norm_num)
    have hdB := (hBy.fderiv_right (by norm_num : 1 + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt
      (by norm_num)
    rw [he.fderiv_eq, fderiv_fun_sub hdW hdB]
    change 0 ≤ fderiv ℝ (fderiv ℝ W) y u u - fderiv ℝ (fderiv ℝ B) y u u
    rw [show fderiv ℝ (fderiv ℝ B) y u u =
      2 * (p.val.2 * (p.val.2 + 1)) * ∑ i, (y i) ^ (-p.val.2 - 2) * (u i) ^ 2 from
        barrier_hessian p.val.2 hy.1 u]
    exact sub_nonneg.mpr (htangent (WithLp.ofLp y) hy u hu)
  refine ⟨W, hW, hval, ?_⟩
  have hc := convexOn_of_tangent_hessian_nonneg (euclidean_simplex_convex N)
    (fun y hy => (hdiff y hy).differentiableAt (by norm_num))
    (fun y hy => ((hdiff y hy).fderiv_right (by norm_num : 1 + 1 ≤ (2 : WithTop ℕ∞))).differentiableAt (by norm_num))
    (fun y hy z hz w hw => hH y hy (w - z) (by
      change (∑ i, (w i - z i)) = 0
      rw [Finset.sum_sub_distrib, hw.2, hz.2, sub_self]))
  convert hc using 1
  funext y
  simp only [Pi.sub_apply, B, Finset.mul_sum]

private theorem inverse_power_sum_convex (N : ℕ+) {s : ℝ} (hs : 0 < s)
    (I : Finset (Fin (N : ℕ))) :
    ConvexOn ℝ (WithLp.ofLp ⁻¹' Riesz1.gapSimplex N)
      (fun y : EuclideanSpace ℝ (Fin (N : ℕ)) => ∑ i ∈ I, 2 * (y i) ^ (-s)) := by
  refine ⟨euclidean_simplex_convex N, fun y hy z hz a b ha hb hab => ?_⟩
  have h := Finset.sum_le_sum (s := I) (fun i _ =>
    mul_le_mul_of_nonneg_left ((Riesz1.convexOn_rpow_neg_Ioi hs).2
      (hy.1 i) (hz.1 i) ha hb hab) (by norm_num : (0 : ℝ) ≤ 2))
  simpa only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum, Finset.sum_add_distrib, mul_add, mul_left_comm] using h

/-- See the proof of Lemma 2.1 in the paper, convexity with any selected
nearest-gap barrier removed. The same realization supplies the simultaneous
all-gap removal and convexity of the original energy. All labels and both
exponent regimes are included, with no added analytic hypotheses. -/
theorem selected_gap_barrier_convex (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ConvexOn ℝ (WithLp.ofLp ⁻¹' Riesz1.gapSimplex N)
        (fun y => W y - 2 * ∑ i, (y i) ^ (-p.val.2)) ∧
      (∀ i : Fin (N : ℕ), ConvexOn ℝ (WithLp.ofLp ⁻¹' Riesz1.gapSimplex N)
        (fun y => W y - 2 * (y i) ^ (-p.val.2))) ∧
      ConvexOn ℝ (WithLp.ofLp ⁻¹' Riesz1.gapSimplex N) W := by
  classical
  obtain ⟨W, hW, hval, hc⟩ := nearest_gap_barrier_convex p N hN
  refine ⟨W, hW, hval, hc, ?_, ?_⟩
  · intro i
    have ht := hc.add (inverse_power_sum_convex N p.property.2.1 (Finset.univ.erase i))
    convert ht using 1
    funext y
    change W y - 2 * (y i) ^ (-p.val.2) =
      W y - 2 * ∑ j, (y j) ^ (-p.val.2) + ∑ j ∈ Finset.univ.erase i, 2 * (y j) ^ (-p.val.2)
    rw [← Finset.mul_sum, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    ring
  · have ht := hc.add (inverse_power_sum_convex N p.property.2.1 Finset.univ)
    convert ht using 1
    funext y
    change W y = W y - 2 * ∑ j, (y j) ^ (-p.val.2) + ∑ j, 2 * (y j) ^ (-p.val.2)
    rw [← Finset.mul_sum]
    ring

/-- See the proof of Lemma 2.1 in the paper, the mean-one clause for the
gap law in both exponent regimes. Integrability is included
before the real expectation is used. -/
theorem gap_mean_one (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (i : Fin (N : ℕ)) :
    Integrable (fun y : Fin (N : ℕ) → ℝ => y i) (gapLaw p N) ∧
      (∫ y, y i ∂gapLaw p N) = 1 :=
  (GapSymmetries.finite_symmetries_and_first_gap_moments p N hN).2.2.2.1 i

/-- See the proof of Lemma 2.1 in the paper, the positive density,
singularity factorization and two log-concavity clauses in the long-range
regime. This is a bridge to the companion library, includes `N=2`,
and uses an explicit Prékopa–Leindler hypothesis. The short-range
regime is not identified with the companion model. -/
theorem long_range_gap_density (hPL : Riesz1.External.PrekopaLeindler)
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (n : ℕ) (j : ℤ) :
    ∃ f h : ℝ → ℝ,
      (gibbsMeasure (ofLong β s) (n + 1).succPNat).map (fun X => Riesz1.gap X j) =
        (volume.restrict (Ioo (0 : ℝ) (n + 2 : ℝ))).withDensity
          (fun t => ENNReal.ofReal (f t)) ∧
      ContinuousOn f (Ioo (0 : ℝ) (n + 2 : ℝ)) ∧
      (∀ t ∈ Ioo (0 : ℝ) (n + 2 : ℝ), 0 < f t ∧ 0 < h t) ∧
      (∀ t ∈ Ioo (0 : ℝ) (n + 2 : ℝ),
        f t = Real.exp (-(2 * β.val) * t ^ (-s.val)) * h t) ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) (n + 2 : ℝ)) (fun t => Real.log (f t)) ∧
      ConcaveOn ℝ (Ioo (0 : ℝ) (n + 2 : ℝ)) (fun t => Real.log (h t)) := by
  let P : Riesz1.Parameters := ⟨(β.val, s.val), β.property, s.property⟩
  let f := Riesz1.gapMarginalProbabilityDensity P n
  let h : ℝ → ℝ := fun t => Real.exp (2 * β.val * t ^ (-s.val)) * f t
  have hpos (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) (n + 2 : ℝ)) : 0 < f t :=
    Riesz1.gapMarginalProbabilityDensity_pos P n ht
  refine ⟨f, h, ?_, Riesz1.continuousOn_gapMarginalProbabilityDensity P n,
    fun t ht => ⟨hpos t ht, mul_pos (Real.exp_pos _) (hpos t ht)⟩, ?_,
    Riesz1.concaveOn_log_gapMarginalProbabilityDensity hPL P n, ?_⟩
  · have hμ : gibbsMeasure (ofLong β s) (n + 1).succPNat =
        Riesz1.gibbsMeasure P (n + 1).succPNat := by
      simp only [gibbsMeasure, ofLong, s.property.2, ↓reduceDIte, P]
    rw [hμ]
    exact Riesz1.map_gap_gibbsMeasure_marginal_density P n j
  · intro t _ht
    change f t = Real.exp (-(2 * β.val) * t ^ (-s.val)) *
      (Real.exp (2 * β.val * t ^ (-s.val)) * f t)
    rw [← mul_assoc, ← Real.exp_add]
    simp only [show -(2 * β.val) * t ^ (-s.val) + 2 * β.val * t ^ (-s.val) = 0 by ring,
      Real.exp_zero, one_mul]
  · have hc := (Riesz1.convexOn_gapPotential hPL P n).neg
    apply hc.congr
    intro t ht
    change -(-Real.log (f t) - 2 * β.val * t ^ (-s.val)) = Real.log (h t)
    rw [show Real.log (h t) = 2 * β.val * t ^ (-s.val) + Real.log (f t) by
      dsimp only [h]
      rw [Real.log_mul (Real.exp_ne_zero _) (hpos t ht).ne', Real.log_exp]]
    ring

/-- See the proof of Lemma 2.1 in the paper, the survival clause in the
long-range regime on its entire positive support `(-∞,N)`. The function
inside the logarithm is the actual gap probability, with the real conversion
justified by the probability measure and the integrable density bridge. -/
theorem long_range_gap_survival (hPL : Riesz1.External.PrekopaLeindler)
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (n : ℕ) (j : ℤ) :
    ConcaveOn ℝ (Iio (n + 2 : ℝ)) (fun u => Real.log
      ((((gibbsMeasure (ofLong β s) (n + 1).succPNat).map
        (fun X => Riesz1.gap X j)) (Ici u)).toReal)) := by
  obtain ⟨f, _, hν, hf, hp, _, hc, _⟩ := long_range_gap_density hPL β s n j
  have := gibbsMeasure_probability (ofLong β s) (n + 1).succPNat
  exact interval_density_log_survival (by positivity) hf
    (fun t ht => (hp t ht).1) hc hν

end Riesz2.RemovableGapBarrier
