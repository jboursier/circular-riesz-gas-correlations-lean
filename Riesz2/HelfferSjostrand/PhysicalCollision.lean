/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.ElementaryBarriers
public import Riesz2.HelfferSjostrand.RemovableGapBarrier
public import Riesz2.HelfferSjostrand.AffineMetricPart2
public import Riesz2.Frozen.FullPhysicalPotentialValue
public import Riesz2.Frozen.PhysicalGapPenalty
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Riesz1.ToMathlib.Calculus.ConvexLineHessian

/-!
# Physical collision estimates

Analytic estimates for Appendix A, using the physical energy and cutoff. All constants here may depend on the volume
and on the fixed penalty data.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology BigOperators ContDiff

namespace Riesz2.PhysicalCollision

/-- A positive argument of the cutoff has an ordinary smooth germ. -/
theorem cutoff_contDiffAt (θ : PhysicalCutoff) {t : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ ∞ θ.val t :=
  (θ.property.1 t ht.le).contDiffAt (Ici_mem_nhds ht)

/-- The cutoff is locally zero at a strictly interior point of its zero interval. -/
theorem cutoff_deriv_quarter (θ : PhysicalCutoff) : deriv θ.val (1 / 4) = 0 := by
  have he : θ.val =ᶠ[𝓝 (1 / 4 : ℝ)] (fun _ => (0 : ℝ)) := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1 / 2)] with t ht
    exact θ.property.2.2.2.1 t ⟨ht.1.le, ht.2.le⟩
  rw [he.deriv_eq, deriv_const]

/-- See Appendix A of the paper: convexity and the zero interval force a
nonnegative cutoff slope throughout the positive half-line. -/
theorem cutoff_deriv_nonneg (θ : PhysicalCutoff) {t : ℝ} (ht : 0 < t) :
    0 ≤ deriv θ.val t := by
  by_cases h : t ≤ 1 / 4
  · have he : θ.val =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
      filter_upwards [Ioo_mem_nhds ht (by linarith : t < 1 / 2)] with u hu
      exact θ.property.2.2.2.1 u ⟨hu.1.le, hu.2.le⟩
    rw [he.deriv_eq, deriv_const]
  · have hc : ConvexOn ℝ (Ioi (0 : ℝ)) θ.val :=
      θ.property.2.1.subset Ioi_subset_Ici_self (convex_Ioi 0)
    have hm := hc.monotoneOn_deriv (fun u hu =>
      (cutoff_contDiffAt θ hu).differentiableAt (by simp))
    have hh := hm (by norm_num : (1 / 4 : ℝ) ∈ Ioi 0) ht (le_of_not_ge h)
    rwa [cutoff_deriv_quarter] at hh

/-- See Appendix A of the paper: a uniform upper curvature bound also bounds
the slope by `C t`. The slope at zero need not be evaluated. -/
theorem cutoff_deriv_bounds (θ : PhysicalCutoff) :
    ∃ C : ℝ, 1 ≤ C ∧
      (∀ t : ℝ, 0 < t → 0 ≤ deriv θ.val t ∧ deriv θ.val t ≤ C * t) ∧
      (∀ t : ℝ, 1 ≤ t → t - 1 ≤ deriv θ.val t) := by
  obtain ⟨C, hC, hcurv, htail⟩ := θ.property.2.2.2.2
  have hdiff (t : ℝ) (ht : 0 < t) : DifferentiableAt ℝ (deriv θ.val) t :=
    ((cutoff_contDiffAt θ ht).derivWithin (m := 1) (by simp)).differentiableAt (by simp)
  have hlin (t : ℝ) : DifferentiableAt ℝ (fun t : ℝ => C * t) t :=
    (hasDerivAt_id t).const_mul C |>.differentiableAt
  have hm : MonotoneOn (fun t => C * t - deriv θ.val t) (Ioi (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    · exact fun t ht => ((hlin t).sub
        (hdiff t ht)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ioi] at ht
      exact ((hlin t).sub (hdiff t ht)).differentiableWithinAt
    · intro t ht
      rw [interior_Ioi] at ht
      rw [deriv_fun_sub (hlin t) (hdiff t ht)]
      simp only [deriv_const_mul_id]
      linarith [(hcurv t ht).2]
  have hml : MonotoneOn (fun t => deriv θ.val t - t) (Ici (1 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · intro t ht
      change 1 ≤ t at ht
      exact ((hdiff t (by linarith)).sub (hasDerivAt_id t).differentiableAt).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      change 1 < t at ht
      exact ((hdiff t (by linarith)).sub (hasDerivAt_id t).differentiableAt).differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      change 1 < t at ht
      have he := ((hdiff t (by linarith)).hasDerivAt.sub (hasDerivAt_id t)).deriv
      change deriv (fun u => deriv θ.val u - u) t = _ at he
      rw [he]
      linarith [htail t ht.le]
  refine ⟨C, hC, ?_, ?_⟩
  · intro t ht
    refine ⟨cutoff_deriv_nonneg θ ht, ?_⟩
    by_cases htq : t ≤ 1 / 4
    · have he : θ.val =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
        filter_upwards [Ioo_mem_nhds ht (by linarith : t < 1 / 2)] with u hu
        exact θ.property.2.2.2.1 u ⟨hu.1.le, hu.2.le⟩
      rw [he.deriv_eq, deriv_const]
      positivity
    · have hh := hm (by norm_num : (1 / 4 : ℝ) ∈ Ioi 0) ht (le_of_not_ge htq)
      dsimp only at hh
      rw [cutoff_deriv_quarter] at hh
      nlinarith
  · intro t ht
    have hh := hml (by simp : (1 : ℝ) ∈ Ici 1) ht ht
    have hp := cutoff_deriv_nonneg θ (by norm_num : (0 : ℝ) < 1)
    linarith

/-- See Appendix A of the paper: first derivative of the inverse penalty on its
whole positive carrier. -/
theorem inverse_penalty_hasDerivAt (θ : PhysicalCutoff) {a x : ℝ}
    (ha : 0 < a) (hx : 0 < x) :
    HasDerivAt (fun t => θ.val (a / t))
      (-(a * x⁻¹ ^ 2) * deriv θ.val (a / x)) x := by
  have hθ := ((cutoff_contDiffAt θ (div_pos ha hx)).differentiableAt (by simp)).hasDerivAt
  have hi := (hasDerivAt_inv hx.ne').const_mul a
  convert hθ.comp x hi using 1
  · funext t; rfl
  · simp only [inv_pow]; ring

/-- See Appendix A of the paper: the inverse-penalty Hessian formula. -/
theorem inverse_penalty_second_deriv (θ : PhysicalCutoff) {a x : ℝ}
    (ha : 0 < a) (hx : 0 < x) :
    deriv (deriv (fun t => θ.val (a / t))) x =
      a ^ 2 * x⁻¹ ^ 4 * deriv (deriv θ.val) (a / x) +
        2 * a * x⁻¹ ^ 3 * deriv θ.val (a / x) := by
  have he : deriv (fun t => θ.val (a / t)) =ᶠ[𝓝 x]
      (fun t => -(a * t⁻¹ ^ 2) * deriv θ.val (a / t)) := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    exact (inverse_penalty_hasDerivAt θ ha ht).deriv
  have hθ := (((cutoff_contDiffAt θ (div_pos ha hx)).derivWithin
    (m := 1) (by simp)).differentiableAt (by simp)).hasDerivAt
  have hi := (hasDerivAt_inv hx.ne').const_mul a
  have h1 : HasDerivAt (fun t : ℝ => -(a * t⁻¹ ^ 2)) (2 * a * x⁻¹ ^ 3) x := by
    convert (((hasDerivAt_inv hx.ne').pow 2).const_mul a).neg using 1
    simp only [inv_pow, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    ring
  have h2 : HasDerivAt (fun t => deriv θ.val (a / t))
      (-(a * x⁻¹ ^ 2) * deriv (deriv θ.val) (a / x)) x := by
    convert hθ.comp x hi using 1
    · funext t; rfl
    · simp only [inv_pow]; ring
  rw [he.deriv_eq]
  have hp := (h1.mul h2).deriv
  change deriv (fun t => -(a * t⁻¹ ^ 2) * deriv θ.val (a / t)) x = _ at hp
  rw [hp]
  ring

/-- See Appendix A of the paper: inverse penalties are convex, and their second
derivatives are bounded by a fixed multiple of `a² x⁻⁴` on all of `(0,∞)`. -/
theorem inverse_penalty_curvature (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ a x : ℝ, 0 < a → 0 < x →
      0 ≤ deriv (deriv (fun t => θ.val (a / t))) x ∧
      deriv (deriv (fun t => θ.val (a / t))) x ≤ C * a ^ 2 * x⁻¹ ^ 4 := by
  obtain ⟨C₁, hC₁, hslope, _⟩ := cutoff_deriv_bounds θ
  obtain ⟨C₂, hC₂, hcurv, _⟩ := θ.property.2.2.2.2
  refine ⟨C₂ + 2 * C₁, by linarith, ?_⟩
  intro a x ha hx
  rw [inverse_penalty_second_deriv θ ha hx]
  have ht := div_pos ha hx
  have hc := hcurv (a / x) ht
  have hp := hslope (a / x) ht
  constructor
  · exact add_nonneg (mul_nonneg (by positivity) hc.1)
      (mul_nonneg (by positivity) hp.1)
  · have h1 := mul_le_mul_of_nonneg_left hc.2
      (show 0 ≤ a ^ 2 * x⁻¹ ^ 4 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hp.2
      (show 0 ≤ 2 * a * x⁻¹ ^ 3 by positivity)
    simp only [div_eq_mul_inv] at h1 h2 ⊢
    nlinarith

/-- See Appendix A of the paper: convexity of an allowed inverse penalty,
without a bound on its first derivative near zero. -/
theorem inverse_penalty_convex (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a) :
    ConvexOn ℝ (Ioi (0 : ℝ)) (fun t => θ.val (a / t)) := by
  have hdiff (x : ℝ) (hx : 0 < x) : ContDiffAt ℝ ∞ (fun t => θ.val (a / t)) x :=
    (cutoff_contDiffAt θ (div_pos ha hx)).comp x
      (contDiffAt_const.div contDiffAt_id hx.ne')
  apply convexOn_of_deriv2_nonneg (convex_Ioi 0)
  · exact fun x hx => (hdiff x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact (hdiff x hx).differentiableAt (by simp) |>.differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    exact ((hdiff x hx).derivWithin (m := 1) (by simp)).differentiableAt (by simp)
      |>.differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    obtain ⟨C, _, hC⟩ := inverse_penalty_curvature θ
    exact (hC a x ha hx).1

/-- See Appendix A of the paper: the radial derivative of an inverse penalty
has the cubic lower bound needed to prevent cancellation at an active
collision. The centre `b` is any fixed positive coordinate. -/
theorem inverse_penalty_radial (θ : PhysicalCutoff) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, 0 < x →
      c * x⁻¹ ^ 3 - C ≤ deriv (fun t => θ.val (a / t)) x * (x - b) := by
  obtain ⟨M, hM, hslope, htail⟩ := cutoff_deriv_bounds θ
  let η := min (a / 2) (b / 2)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  let c := a ^ 2 * b / 4
  have hc : 0 < c := by positivity
  refine ⟨c, c * η⁻¹ ^ 3 + M * a ^ 2 * η⁻¹ ^ 2 + 1, hc, by positivity, ?_⟩
  intro x hx
  rw [(inverse_penalty_hasDerivAt θ ha hx).deriv]
  have hinv : 0 < x⁻¹ := inv_pos.mpr hx
  have hpx : 0 ≤ deriv θ.val (a / x) := cutoff_deriv_nonneg θ (div_pos ha hx)
  by_cases hsmall : x ≤ η
  · have hxa : x ≤ a / 2 := hsmall.trans (min_le_left _ _)
    have hxb : x ≤ b / 2 := hsmall.trans (min_le_right _ _)
    have ht : 1 ≤ a / x := (le_div_iff₀ hx).mpr (by linarith)
    have hp : a / (2 * x) ≤ deriv θ.val (a / x) := by
      have ht' := htail (a / x) ht
      have hh : a / (2 * x) ≤ a / x - 1 := by
        apply (div_le_iff₀ (show 0 < 2 * x by positivity)).mpr
        nlinarith [div_mul_cancel₀ a hx.ne']
      exact hh.trans ht'
    have hprod := mul_le_mul hp (show b / 2 ≤ b - x by linarith)
      (by positivity : 0 ≤ b / 2) hpx
    have hprod' := mul_le_mul_of_nonneg_left hprod (show 0 ≤ a * x⁻¹ ^ 2 by positivity)
    have he : a * x⁻¹ ^ 2 * (a / (2 * x) * (b / 2)) = c * x⁻¹ ^ 3 := by
      dsimp only [c]
      field_simp
      ring
    rw [he] at hprod'
    have hC : 0 ≤ c * η⁻¹ ^ 3 + M * a ^ 2 * η⁻¹ ^ 2 + 1 := by positivity
    nlinarith only [hprod', hC]
  · have hηx := le_of_not_ge hsmall
    have hi : x⁻¹ ≤ η⁻¹ := inv_anti₀ hη hηx
    have hi2 : x⁻¹ ^ 2 ≤ η⁻¹ ^ 2 := pow_le_pow_left₀ hinv.le hi 2
    have hi3 : x⁻¹ ^ 3 ≤ η⁻¹ ^ 3 := pow_le_pow_left₀ hinv.le hi 3
    have hp := (hslope (a / x) (div_pos ha hx)).2
    have h1 := mul_le_mul_of_nonneg_left hp (show 0 ≤ a * x⁻¹ by positivity)
    have h2 := mul_le_mul_of_nonneg_left hi2 (show 0 ≤ M * a ^ 2 by positivity)
    have h3 := mul_le_mul_of_nonneg_left hi3 hc.le
    have he : a * x⁻¹ ^ 2 * deriv θ.val (a / x) * x = a * x⁻¹ * deriv θ.val (a / x) := by
      field_simp
    have h4 : -(a * x⁻¹ ^ 2) * deriv θ.val (a / x) * (x - b) ≥
        -(a * x⁻¹ * deriv θ.val (a / x)) := by
      have ht : 0 ≤ a * x⁻¹ ^ 2 * deriv θ.val (a / x) * b := by positivity
      nlinarith only [he, ht]
    have he' : a * x⁻¹ * (M * (a / x)) = M * a ^ 2 * x⁻¹ ^ 2 := by
      field_simp
    rw [he'] at h1
    linarith

section GapGeometry

variable (N : ℕ+)

local notation "Y(" z ")" =>
  (WithLp.toLp 2 (fun i => 1 + (Subtype.val z) i) : EuclideanSpace ℝ (Fin (N : ℕ)))

/-- The affine face coordinates of the intrinsic gap domain. -/
def gapFace (i : Fin (N : ℕ)) : gapTangentSpace N →ᵃ[ℝ] ℝ :=
  AffineMap.const ℝ (gapTangentSpace N) 1 +
    ((EuclideanSpace.proj (𝕜 := ℝ) i).comp (gapTangentSpace N).subtypeL).toLinearMap.toAffineMap

theorem gapFace_apply (i : Fin (N : ℕ)) (z : gapTangentSpace N) :
    gapFace N i z = 1 + z.val i := rfl

/-- The positive mass simplex, in the isometric chart. -/
theorem intrinsic_chart_mem_simplex {z : gapTangentSpace N}
    (hz : z ∈ intrinsicGapDomain N) : WithLp.ofLp Y(z) ∈ Riesz1.gapSimplex N := by
  refine ⟨hz, ?_⟩
  change (∑ i, (1 + z.val i)) = (N : ℝ)
  rw [Finset.sum_add_distrib, z.property]
  simp

/-- Each positive gap is at most the fixed total mass. -/
theorem gap_le_mass {z : gapTangentSpace N} (hz : z ∈ intrinsicGapDomain N)
    (i : Fin (N : ℕ)) : 1 + z.val i ≤ (N : ℝ) := by
  have hy := intrinsic_chart_mem_simplex N hz
  rw [← hy.2]
  exact Finset.single_le_sum (fun j _ => (hy.1 j).le) (Finset.mem_univ i)

/-- Boundedness uses the actual intrinsic domain, rather than an ambient
extension of the energy domain. -/
theorem intrinsicGapDomain_bounded : Bornology.IsBounded (intrinsicGapDomain N) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨(N : ℝ) * ((N : ℝ) + 1), fun z hz => ?_⟩
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hzsq : ‖z‖ ^ 2 ≤ (N : ℝ) * ((N : ℝ) + 1) ^ 2 := by
    rw [← Submodule.norm_coe, EuclideanSpace.real_norm_sq_eq]
    calc
      (∑ i, z.val i ^ 2) ≤ ∑ _i : Fin (N : ℕ), ((N : ℝ) + 1) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hi := gap_le_mass N hz i
        have hp := hz i
        nlinarith
      _ = _ := by simp
  have hC : 0 ≤ (N : ℝ) * ((N : ℝ) + 1) := by positivity
  nlinarith [norm_nonneg z]

/-- Smoothness of the inverse of the centering chart. -/
theorem intrinsic_chart_contDiff : ContDiff ℝ ∞ (fun z : gapTangentSpace N => Y(z)) := by
  have he : (fun z : gapTangentSpace N => Y(z)) =
      (fun z => (gapTangentSpace N).subtypeL z + WithLp.toLp 2 (fun _ => (1 : ℝ))) := by
    funext z
    ext i
    change 1 + z.val i = z.val i + 1
    ring
  rw [he]
  exact (gapTangentSpace N).subtypeL.contDiff.add contDiff_const

/-- The full simplex has positive intrinsic dimension as soon as `N≥2`. -/
theorem tangent_nontrivial (hN : 2 ≤ (N : ℕ)) : Nontrivial (gapTangentSpace N) := by
  let v : EuclideanSpace ℝ (Fin (N : ℕ)) :=
    EuclideanSpace.single ⟨0, by omega⟩ 1 - EuclideanSpace.single ⟨1, by omega⟩ 1
  have hv : v ∈ gapTangentSpace N := by
    change (∑ i, (EuclideanSpace.single (⟨0, by omega⟩ : Fin (N : ℕ)) (1 : ℝ) -
      EuclideanSpace.single (⟨1, by omega⟩ : Fin (N : ℕ)) (1 : ℝ)) i) = 0
    simp [PiLp.sub_apply]
  refine ⟨⟨⟨v, hv⟩, 0, ?_⟩⟩
  intro he
  have hi := congrArg (fun z : gapTangentSpace N => z.val ⟨0, by omega⟩) he
  norm_num [v, EuclideanSpace.single] at hi

/-- Positivity of the smallest gap is witnessed by a label attaining it. -/
theorem minimum_gap_pos {z : gapTangentSpace N} (hz : z ∈ intrinsicGapDomain N) :
    0 < ⨅ i : Fin (N : ℕ), 1 + z.val i := by
  obtain ⟨i, hi⟩ := ElementaryBarriers.exists_iInf_eq_apply (fun i => 1 + z.val i)
  rw [hi]
  exact hz i

end GapGeometry

section PhysicalGradient

variable (N : ℕ+)

local notation "Y(" z ")" =>
  (WithLp.toLp 2 (fun i => 1 + (Subtype.val z) i) : EuclideanSpace ℝ (Fin (N : ℕ)))

/-- Convexity on the physical simplex pulls back to the intrinsic
domain. The chart is isometric and affine. -/
theorem convexOn_intrinsic_pullback {W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ}
    (hW : ConvexOn ℝ (WithLp.ofLp ⁻¹' Riesz1.gapSimplex N) W) :
    ConvexOn ℝ (intrinsicGapDomain N) (fun z => W Y(z)) := by
  let T : gapTangentSpace N →ᵃ[ℝ] EuclideanSpace ℝ (Fin (N : ℕ)) :=
    AffineMap.const ℝ _ (WithLp.toLp 2 (fun _ => (1 : ℝ))) +
      (gapTangentSpace N).subtype.toAffineMap
  have hT (z : gapTangentSpace N) : T z = Y(z) := by ext i; rfl
  have he : T ⁻¹' (WithLp.ofLp ⁻¹' Riesz1.gapSimplex N) = intrinsicGapDomain N := by
    ext z
    constructor
    · intro hz
      exact fun i => by simpa only [hT] using hz.1 i
    · intro hz
      rw [Set.mem_preimage, hT]
      exact intrinsic_chart_mem_simplex N hz
  simpa only [he, Function.comp_def, hT] using hW.comp_affineMap T

/-- A smooth ambient realization is smooth intrinsically on the entire
positive simplex. -/
theorem contDiffOn_intrinsic_pullback {W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ}
    (hW : ContDiffOn ℝ ∞ W (gapAmbientDomain N)) :
    ContDiffOn ℝ ∞ (fun z : gapTangentSpace N => W Y(z)) (intrinsicGapDomain N) :=
  hW.comp (intrinsic_chart_contDiff N).contDiffOn (fun _z hz =>
    PhysicalEnergy.simplex_subset_ambient N _ (intrinsic_chart_mem_simplex N hz))

/-- See Appendix A of the paper, the unforced intrinsic gradient estimate. The
potential agrees with the physical energy on its whole ambient
domain, and constants are chosen before the interior configuration. -/
theorem unforced_gradient_lower (p : Parameters) (hN : 2 ≤ (N : ℕ)) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z ∈ intrinsicGapDomain N,
        c * (⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-p.val.2 - 1) - C ≤
          ‖gradient (fun z : gapTangentSpace N => p.val.1 * W Y(z)) z‖ := by
  have := tangent_nontrivial N hN
  obtain ⟨W, hW, hval, hconv⟩ := RemovableGapBarrier.nearest_gap_barrier_convex p N hN
  have hp := p.property.1
  let R : gapTangentSpace N → ℝ := fun z =>
    p.val.1 * (W Y(z) - 2 * ∑ i, (1 + z.val i) ^ (-p.val.2))
  have hRc : ConvexOn ℝ (intrinsicGapDomain N) R :=
    (convexOn_intrinsic_pullback N hconv).smul hp.le
  have hRs : ContDiffOn ℝ ∞ R (intrinsicGapDomain N) := by
    apply contDiffOn_const.mul
    apply (contDiffOn_intrinsic_pullback N hW).sub
    apply contDiffOn_const.mul
    apply ContDiffOn.sum
    intro i _
    have hi : ContDiff ℝ ∞ (fun z : gapTangentSpace N => 1 + z.val i) :=
      contDiff_const.add ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp
        (gapTangentSpace N).subtypeL.contDiff)
    exact hi.contDiffOn.rpow_const_of_ne (fun z hz => (hz i).ne')
  have hV (z : gapTangentSpace N) (_hz : z ∈ intrinsicGapDomain N) :
      p.val.1 * W Y(z) =
        ∑ i, (2 * p.val.1) * (gapFace N i z) ^ (-p.val.2) + R z := by
    simp only [gapFace_apply, ← Finset.mul_sum, R]
    ring
  obtain ⟨c, C, hc, hC, hbound⟩ := ElementaryBarriers.radial_gradient_lower
    (gapFace N) (fun _ => 2 * p.val.1) (fun _ => by positivity) p.property.2.1
    (Ω := intrinsicGapDomain N) rfl (intrinsicGapDomain_bounded N) R hRc hRs
    (fun z => p.val.1 * W Y(z)) hV
  exact ⟨W, hW, hval, c, C, hc, hC, hbound⟩

end PhysicalGradient

section Hessian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Internal calculus helper: multiplying a potential multiplies its
bilinear Hessian by the same scalar. -/
theorem internal_hessian_const_mul {W : E → ℝ} {z : E}
    (hW : ContDiffAt ℝ 2 W z) (a : ℝ) (u v : E) :
    fderiv ℝ (fderiv ℝ (fun x => a * W x)) z u v =
      a * fderiv ℝ (fderiv ℝ W) z u v := by
  have he := congrArg (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ =>
    T ![u, v]) (iteratedFDeriv_const_smul_apply (a := a) hW)
  simpa only [Pi.smul_def, smul_eq_mul, smul_apply,
    iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using he

/-- Internal trace helper, valid even if the second derivative is defined
by Mathlib's total derivative convention. -/
theorem internal_laplacian_le [FiniteDimensional ℝ E] (W : E → ℝ) (z : E) (D : ℝ)
    (hD : ∀ u : E, fderiv ℝ (fderiv ℝ W) z u u ≤ D * ‖u‖ ^ 2) :
    Laplacian.laplacian W z ≤ (Module.finrank ℝ E : ℝ) * D := by
  let b := stdOrthonormalBasis ℝ E
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis W b]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  calc
    (∑ i, fderiv ℝ (fderiv ℝ W) z (b i) (b i)) ≤ ∑ _i : Fin (Module.finrank ℝ E), D := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [b.norm_eq_one, one_pow, mul_one] using hD (b i)
    _ = _ := by simp

end Hessian

section PhysicalHessian

variable (N : ℕ+)

local notation "Y(" z ")" =>
  (WithLp.toLp 2 (fun i => 1 + (Subtype.val z) i) : EuclideanSpace ℝ (Fin (N : ℕ)))

/-- See Appendix A of the paper, strict curvature and the Hessian upper estimate
for the unforced physical potential in the intrinsic Euclidean metric. -/
theorem unforced_hessian_bounds (p : Parameters) (hN : 2 ≤ (N : ℕ)) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧ ∀ z ∈ intrinsicGapDomain N, ∀ u : gapTangentSpace N,
        κ * ‖u‖ ^ 2 ≤
          fderiv ℝ (fderiv ℝ (fun z : gapTangentSpace N => p.val.1 * W Y(z))) z u u ∧
        fderiv ℝ (fderiv ℝ (fun z : gapTangentSpace N => p.val.1 * W Y(z))) z u u ≤
          C * (⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-p.val.2 - 2) * ‖u‖ ^ 2 := by
  classical
  have hp := p.property.1
  have hs := p.property.2.1
  have hNpos : (0 : ℝ) < N := by positivity
  obtain ⟨_, _, W, hW, hval, hd, _, hlow, _, _⟩ :=
    PhysicalEnergy.restriction_and_derivatives p N hN
  let K := p.val.2 * (p.val.2 + 1) *
    PeriodicPower.bound (p.val.2 + 2) (by linarith [p.property.2.1])
  have hK : 0 < K := mul_pos (mul_pos p.property.2.1 (by linarith [p.property.2.1]))
    (PeriodicPower.bound_pos _ _)
  let S := ∑ i : Fin (N : ℕ), ∑ r : Fin ((N : ℕ) / 2),
    ‖PhysicalEnergy.intervalLinear N i (r.val + 1)‖ ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  refine ⟨W, hW, hval, p.val.1 * (p.val.2 * (p.val.2 + 1) * (N : ℝ) ^ (-p.val.2 - 2)),
    p.val.1 * (2 * K * S + 1), by positivity, by positivity, ?_⟩
  intro z hz u
  have hy := intrinsic_chart_mem_simplex N hz
  have hyU := PhysicalEnergy.simplex_subset_ambient N _ hy
  have hWy : ContDiffAt ℝ 2 W Y(z) :=
    ((hW _ hyU).contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hyU)).of_le (by simp)
  have hchart : (gapTangentSpace N).subtypeL z + WithLp.toLp 2 (fun _ => (1 : ℝ)) = Y(z) := by
    ext i
    change z.val i + 1 = 1 + z.val i
    ring
  have hh : fderiv ℝ (fderiv ℝ (fun z : gapTangentSpace N => p.val.1 * W Y(z))) z u u =
      p.val.1 * fderiv ℝ (fderiv ℝ W) Y(z) u.val u.val := by
    have hcomp := AffineMetricTransport.hessian_comp_affine
      (gapTangentSpace N).subtypeL (WithLp.toLp 2 (fun _ => (1 : ℝ)))
      (f := fun x => p.val.1 * W x)
      (by rw [hchart]; exact contDiffAt_const.mul hWy) u u
    have he : (fun z : gapTangentSpace N => p.val.1 *
        W ((gapTangentSpace N).subtypeL z + WithLp.toLp 2 (fun _ => (1 : ℝ)))) =
        (fun z : gapTangentSpace N => p.val.1 * W Y(z)) := by
      funext z
      congr 2
      ext i
      change z.val i + 1 = 1 + z.val i
      ring
    rw [he, hchart, internal_hessian_const_mul hWy] at hcomp
    exact hcomp
  rw [hh]
  have hδ := minimum_gap_pos N hz
  have hδi (i : Fin (N : ℕ)) : (⨅ i : Fin (N : ℕ), 1 + z.val i) ≤ 1 + z.val i :=
    ciInf_le (Finite.bddBelow_range _) i
  constructor
  · have hpow (i : Fin (N : ℕ)) : (N : ℝ) ^ (-p.val.2 - 2) ≤
        (1 + z.val i) ^ (-p.val.2 - 2) :=
      Real.rpow_le_rpow_of_nonpos (hz i) (gap_le_mass N hz i) (by linarith [p.property.2.1])
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_right (hpow i) (sq_nonneg (u.val i)))
    rw [← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq] at hsum
    have hlo := hlow _ hy u.val
    have h1 := mul_le_mul_of_nonneg_left hsum
      (show 0 ≤ p.val.2 * (p.val.2 + 1) by positivity)
    have h2 := mul_le_mul_of_nonneg_left (h1.trans hlo) p.property.1.le
    simpa only [Submodule.norm_coe, mul_assoc] using h2
  · rw [(hd ⟨Y(z), hyU⟩ u.val u.val).2]
    have hupper (i : Fin (N : ℕ)) (r : Fin ((N : ℕ) / 2)) :
        (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
          PhysicalEnergy.intervalCoefficient p N
            ⟨cyclicGapSum N i (r.val + 1) (WithLp.ofLp Y(z)),
              hyU i _ (Nat.succ_le_succ (Nat.zero_le _)) (Nat.succ_le_of_lt r.isLt)⟩ *
            (cyclicGapSum N i (r.val + 1) (WithLp.ofLp u.val) *
              cyclicGapSum N i (r.val + 1) (WithLp.ofLp u.val)) ≤
          2 * K * (⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-p.val.2 - 2) *
            (‖PhysicalEnergy.intervalLinear N i (r.val + 1)‖ ^ 2 * ‖u‖ ^ 2) := by
      let δ := ⨅ i : Fin (N : ℕ), 1 + z.val i
      have hr : (1 : ℝ) ≤ ((r.val + 1 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.succ_le_succ (Nat.zero_le r.val))
      have hL := (PhysicalEnergy.gapSum_bounds N i (r.val + 1) (WithLp.ofLp Y(z))
        (fun j => ⟨hδi j, gap_le_mass N hz j⟩)).1
      have hNL := PhysicalEnergy.gapSum_complement_lower N i
        ((Nat.succ_le_of_lt r.isLt).trans (Nat.div_le_self _ _)) (WithLp.ofLp Y(z)) hδi hy.2
      have hrN : (1 : ℝ) ≤ (N : ℝ) - ((r.val + 1 : ℕ) : ℝ) := by
        have hh : r.val + 2 ≤ (N : ℕ) := Nat.succ_le_of_lt
          ((Nat.succ_le_of_lt r.isLt).trans_lt (Nat.div_lt_self N.pos (by norm_num)))
        have hh' : ((r.val + 2 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hh
        push_cast at hh' ⊢
        linarith
      have hc := PhysicalEnergy.intervalCoefficient_upper p N
        ⟨cyclicGapSum N i (r.val + 1) (WithLp.ofLp Y(z)),
          hyU i _ (Nat.succ_le_succ (Nat.zero_le _)) (Nat.succ_le_of_lt r.isLt)⟩ hδ
        ((le_mul_of_one_le_right hδ.le hr).trans hL)
        ((le_mul_of_one_le_right hδ.le hrN).trans hNL)
      have hcpos := (PhysicalEnergy.intervalCoefficient_pos p N
        ⟨cyclicGapSum N i (r.val + 1) (WithLp.ofLp Y(z)),
          hyU i _ (Nat.succ_le_succ (Nat.zero_le _)) (Nat.succ_le_of_lt r.isLt)⟩).le
      have hw : 0 ≤ (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) ∧
          (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) ≤ 2 := by
        split_ifs <;> norm_num
      have hlin := (PhysicalEnergy.intervalLinear N i (r.val + 1)).le_opNorm u.val
      rw [PhysicalEnergy.intervalLinear_apply, Real.norm_eq_abs] at hlin
      have hsq := sq_le_sq₀ (abs_nonneg _) (by positivity) |>.2 hlin
      rw [sq_abs, mul_pow, Submodule.norm_coe] at hsq
      have hcoeff : (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
          PhysicalEnergy.intervalCoefficient p N
            ⟨cyclicGapSum N i (r.val + 1) (WithLp.ofLp Y(z)),
              hyU i _ (Nat.succ_le_succ (Nat.zero_le _)) (Nat.succ_le_of_lt r.isLt)⟩ ≤
          2 * K * δ ^ (-p.val.2 - 2) := by
        calc
          _ ≤ 2 * PhysicalEnergy.intervalCoefficient p N
            ⟨cyclicGapSum N i (r.val + 1) (WithLp.ofLp Y(z)),
              hyU i _ (Nat.succ_le_succ (Nat.zero_le _)) (Nat.succ_le_of_lt r.isLt)⟩ :=
            mul_le_mul_of_nonneg_right hw.2 hcpos
          _ ≤ _ := by simpa only [K, δ, mul_assoc] using
            mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 2)
      simpa only [pow_two] using mul_le_mul hcoeff hsq (sq_nonneg _)
        (by positivity : 0 ≤ 2 * K * δ ^ (-p.val.2 - 2))
    have hsums := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      Finset.sum_le_sum (s := Finset.univ) (fun r _ => hupper i r))
    have he : (∑ i : Fin (N : ℕ), ∑ r : Fin ((N : ℕ) / 2),
        2 * K * (⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-p.val.2 - 2) *
          (‖PhysicalEnergy.intervalLinear N i (r.val + 1)‖ ^ 2 * ‖u‖ ^ 2)) =
        2 * K * S * (⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-p.val.2 - 2) * ‖u‖ ^ 2 := by
      simp only [S, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro r _
      ring
    rw [he] at hsums
    have hsums' := mul_le_mul_of_nonneg_left hsums p.property.1.le
    apply hsums'.trans
    have hnonneg : 0 ≤ p.val.1 *
        (⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-p.val.2 - 2) * ‖u‖ ^ 2 := by positivity
    nlinarith only [hnonneg]

end PhysicalHessian

section UnforcedCollision

variable (N : ℕ+)

local notation "Y(" z ")" =>
  (WithLp.toLp 2 (fun i => 1 + (Subtype.val z) i) : EuclideanSpace ℝ (Fin (N : ℕ)))

/-- Internal application of the radial criterion. Its trace premise is
discharged by the physical Hessian estimate in `unforced_collision_estimates`. -/
theorem internal_unforced_collision (p : Parameters) (hN : 2 ≤ (N : ℕ))
    (W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ)
    (hW : ContDiffOn ℝ ∞ W (gapAmbientDomain N))
    (hval : ∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
      W y.val = physicalAmbientGapEnergy p N y)
    (C₀ : ℝ) (hΔ : ∀ z ∈ intrinsicGapDomain N,
      Laplacian.laplacian (fun z : gapTangentSpace N => p.val.1 * W Y(z)) z ≤
        C₀ * (⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-p.val.2 - 2)) :
    ∀ A K : ℝ, 0 < A → 0 < K → ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ intrinsicGapDomain N,
      K * (Metric.infDist z (frontier (intrinsicGapDomain N)))⁻¹ ^ 2 - C ≤
        A * ‖gradient (fun z : gapTangentSpace N => p.val.1 * W Y(z)) z‖ ^ 2 -
          Laplacian.laplacian (fun z : gapTangentSpace N => p.val.1 * W Y(z)) z := by
  have := tangent_nontrivial N hN
  have hp := p.property.1
  obtain ⟨W₀, _, hval₀, hconv₀⟩ := RemovableGapBarrier.nearest_gap_barrier_convex p N hN
  have hconv : ConvexOn ℝ (WithLp.ofLp ⁻¹' Riesz1.gapSimplex N)
      (fun y => W y - 2 * ∑ i, (y i) ^ (-p.val.2)) := by
    apply hconv₀.congr
    intro y hy
    have hyU := PhysicalEnergy.simplex_subset_ambient N _ hy
    dsimp only
    rw [hval₀ ⟨y, hyU⟩, hval ⟨y, hyU⟩]
  let R : gapTangentSpace N → ℝ := fun z =>
    p.val.1 * (W Y(z) - 2 * ∑ i, (1 + z.val i) ^ (-p.val.2))
  have hRc : ConvexOn ℝ (intrinsicGapDomain N) R :=
    (convexOn_intrinsic_pullback N hconv).smul hp.le
  have hRs : ContDiffOn ℝ ∞ R (intrinsicGapDomain N) := by
    apply contDiffOn_const.mul
    apply (contDiffOn_intrinsic_pullback N hW).sub
    apply contDiffOn_const.mul
    apply ContDiffOn.sum
    intro i _
    have hi : ContDiff ℝ ∞ (fun z : gapTangentSpace N => 1 + z.val i) :=
      contDiff_const.add ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp
        (gapTangentSpace N).subtypeL.contDiff)
    exact hi.contDiffOn.rpow_const_of_ne (fun z hz => (hz i).ne')
  have hV (z : gapTangentSpace N) (_hz : z ∈ intrinsicGapDomain N) :
      p.val.1 * W Y(z) =
        ∑ i, (2 * p.val.1) * (gapFace N i z) ^ (-p.val.2) + R z := by
    simp only [gapFace_apply, ← Finset.mul_sum, R]
    ring
  have hΔ' (z : gapTangentSpace N) (hz : z ∈ intrinsicGapDomain N) :
      Laplacian.laplacian (fun z : gapTangentSpace N => p.val.1 * W Y(z)) z ≤
        max C₀ 0 * (1 + (⨅ i, gapFace N i z) ^ (-p.val.2 - 2)) := by
    have h := hΔ z hz
    have ht : 0 ≤ (⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-p.val.2 - 2) :=
      Real.rpow_nonneg (minimum_gap_pos N hz).le _
    have hh := mul_le_mul_of_nonneg_right (le_max_left C₀ 0) ht
    simp only [gapFace_apply]
    nlinarith [le_max_right C₀ 0]
  intro A K hA hK
  obtain ⟨C, hC⟩ := ElementaryBarriers.radial_laplacian_lower
    (gapFace N) (fun _ => 2 * p.val.1) (fun _ => by positivity) p.property.2.1
    (Ω := intrinsicGapDomain N) rfl (intrinsicGapDomain_bounded N) R hRc hRs
    (fun z => p.val.1 * W Y(z)) hV (max C₀ 0) hΔ' A K hA hK
  refine ⟨max C 0, le_max_right _ _, fun z hz => ?_⟩
  have h := hC z hz
  simp only [← inv_pow] at h
  linarith [le_max_left C 0]

/-- See Appendix A of the paper, all unforced full-gap assertions: the gradient
and trace bounds, positive uniform intrinsic curvature, and the collision
criterion for every positive coefficient. -/
theorem unforced_collision_estimates (p : Parameters) (hN : 2 ≤ (N : ℕ)) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ∃ c C κ : ℝ, 0 < c ∧ 0 < C ∧ 0 < κ ∧
      (∀ z ∈ intrinsicGapDomain N,
        c * (⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-p.val.2 - 1) - C ≤
          ‖gradient (fun z : gapTangentSpace N => p.val.1 * W Y(z)) z‖ ∧
        Laplacian.laplacian (fun z : gapTangentSpace N => p.val.1 * W Y(z)) z ≤
          C * (⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-p.val.2 - 2) ∧
        ∀ u : gapTangentSpace N, κ * ‖u‖ ^ 2 ≤
          fderiv ℝ (fderiv ℝ (fun z : gapTangentSpace N => p.val.1 * W Y(z))) z u u) ∧
      (∀ A K : ℝ, 0 < A → 0 < K → ∃ D : ℝ, 0 ≤ D ∧ ∀ z ∈ intrinsicGapDomain N,
        K * (Metric.infDist z (frontier (intrinsicGapDomain N)))⁻¹ ^ 2 - D ≤
          A * ‖gradient (fun z : gapTangentSpace N => p.val.1 * W Y(z)) z‖ ^ 2 -
            Laplacian.laplacian (fun z : gapTangentSpace N => p.val.1 * W Y(z)) z) := by
  obtain ⟨W, hW, hval, κ, C₀, hκ, hC₀, hH⟩ := unforced_hessian_bounds N p hN
  obtain ⟨W₁, _, hval₁, c, C₁, hc, hC₁, hG⟩ := unforced_gradient_lower N p hN
  let D := (Module.finrank ℝ (gapTangentSpace N) : ℝ) * C₀
  have hD : 0 ≤ D := by positivity
  have hΔ (z : gapTangentSpace N) (hz : z ∈ intrinsicGapDomain N) :
      Laplacian.laplacian (fun z : gapTangentSpace N => p.val.1 * W Y(z)) z ≤
        D * (⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-p.val.2 - 2) := by
    have ht := internal_laplacian_le (fun z : gapTangentSpace N => p.val.1 * W Y(z)) z
      (C₀ * (⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-p.val.2 - 2))
      (fun u => (hH z hz u).2)
    simpa only [D, mul_assoc] using ht
  refine ⟨W, hW, hval, c, max C₁ D, κ, hc, lt_of_lt_of_le hC₁ (le_max_left _ _), hκ, ?_,
    internal_unforced_collision N p hN W hW hval D hΔ⟩
  intro z hz
  have he : (fun z : gapTangentSpace N => p.val.1 * W₁ Y(z)) =ᶠ[𝓝 z]
      (fun z : gapTangentSpace N => p.val.1 * W Y(z)) := by
    filter_upwards [(AffineMetric.intrinsicGapDomain_isOpen N).mem_nhds hz] with w hw
    have hwU := PhysicalEnergy.simplex_subset_ambient N _ (intrinsic_chart_mem_simplex N hw)
    rw [hval₁ ⟨Y(w), hwU⟩, hval ⟨Y(w), hwU⟩]
  have hg := hG z hz
  rw [he.gradient_eq] at hg
  refine ⟨by linarith [le_max_left C₁ D], ?_, fun u => (hH z hz u).1⟩
  exact (hΔ z hz).trans (mul_le_mul_of_nonneg_right (le_max_right C₁ D)
    (Real.rpow_nonneg (minimum_gap_pos N hz).le _))

end UnforcedCollision

section SelectedPenalties

/-- See Appendix A of the paper: upper penalties are convex on the whole
positive half-line. -/
theorem upper_penalty_convex (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a) :
    ConvexOn ℝ (Ioi (0 : ℝ)) (fun x => θ.val (a * x)) := by
  refine ⟨convex_Ioi 0, fun x hx y hy α β hα hβ hsum => ?_⟩
  have h := θ.property.2.1.2 (show a * x ∈ Ici 0 from mul_nonneg ha.le hx.le)
    (show a * y ∈ Ici 0 from mul_nonneg ha.le hy.le) hα hβ hsum
  simpa only [smul_eq_mul, mul_add, mul_left_comm a] using h

variable (N : ℕ+)

/-- Convexity of the intrinsic domain, with no change of metric. -/
theorem intrinsicGapDomain_convex : Convex ℝ (intrinsicGapDomain N) := by
  intro x hx y hy α β hα hβ hsum i
  have ht := ElementaryBarriers.pos_of_convex_comb (hx i) (hy i) hα hβ hsum
  change 0 < 1 + (α • x + β • y).val i
  change 0 < 1 + (α * x.val i + β * y.val i)
  nlinarith

/-- See Appendix A of the paper, smoothness and convexity of both allowed
penalties on every selected label set, including the empty set. -/
theorem selected_penalty_smooth_convex (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (I : Finset (Fin (N : ℕ))) (twoSided : Bool) :
    ContDiffOn ℝ ∞ (fun z : gapTangentSpace N =>
      ∑ i ∈ I, (θ.val (a * (1 + z.val i)) +
        if twoSided then θ.val (a / (1 + z.val i)) else 0)) (intrinsicGapDomain N) ∧
    ConvexOn ℝ (intrinsicGapDomain N) (fun z : gapTangentSpace N =>
      ∑ i ∈ I, (θ.val (a * (1 + z.val i)) +
        if twoSided then θ.val (a / (1 + z.val i)) else 0)) := by
  have hφ : ConvexOn ℝ (Ioi (0 : ℝ)) (fun x => θ.val (a * x) +
      if twoSided then θ.val (a / x) else 0) := by
    cases twoSided
    · simpa only [Bool.false_eq_true, ↓reduceIte, add_zero] using upper_penalty_convex θ ha
    · simpa only [↓reduceIte, Pi.add_def] using
        (upper_penalty_convex θ ha).add (inverse_penalty_convex θ ha)
  have hterm (i : Fin (N : ℕ)) : ConvexOn ℝ (intrinsicGapDomain N)
      (fun z : gapTangentSpace N => θ.val (a * (1 + z.val i)) +
        if twoSided then θ.val (a / (1 + z.val i)) else 0) := by
    have h := (hφ.comp_affineMap (gapFace N i)).subset
      (fun z (hz : z ∈ intrinsicGapDomain N) => hz i) (intrinsicGapDomain_convex N)
    simpa only [Function.comp_def, gapFace_apply] using h
  constructor
  · apply ContDiffOn.sum
    intro i _ z hz
    have hi : ContDiffAt ℝ ∞ (fun z : gapTangentSpace N => 1 + z.val i) z :=
      (contDiff_const.add ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp
        (gapTangentSpace N).subtypeL.contDiff)).contDiffAt
    have hup := (cutoff_contDiffAt θ (mul_pos ha (hz i))).comp z (contDiffAt_const.mul hi)
    cases twoSided
    · simpa only [Bool.false_eq_true, ↓reduceIte, add_zero, Function.comp_def] using hup.contDiffWithinAt
    · have hinv := (cutoff_contDiffAt θ (div_pos ha (hz i))).comp z
        (contDiffAt_const.div hi (hz i).ne')
      simpa only [↓reduceIte, Function.comp_def, Pi.div_apply] using (hup.add hinv).contDiffWithinAt
  · refine ⟨intrinsicGapDomain_convex N, fun x hx y hy α β hα hβ hsum => ?_⟩
    have ht := Finset.sum_le_sum (s := I) (fun i _ => (hterm i).2 hx hy hα hβ hsum)
    simpa only [smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum] using ht

end SelectedPenalties

section HessianAddition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Internal calculus helper for adding the physical energy and a smooth
penalty. -/
theorem internal_hessian_add {F G : E → ℝ} {z : E}
    (hF : ContDiffAt ℝ 2 F z) (hG : ContDiffAt ℝ 2 G z) (u v : E) :
    fderiv ℝ (fderiv ℝ (fun x => F x + G x)) z u v =
      fderiv ℝ (fderiv ℝ F) z u v + fderiv ℝ (fderiv ℝ G) z u v := by
  have he := congrArg (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ =>
    T ![u, v]) (iteratedFDeriv_add_apply hF hG)
  simpa only [Pi.add_def, add_apply,
    iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using he

end HessianAddition

section PenalizedCurvature

variable (N : ℕ+)

local notation "Y(" z ")" =>
  (WithLp.toLp 2 (fun i => 1 + (Subtype.val z) i) : EuclideanSpace ℝ (Fin (N : ℕ)))

/-- See Appendix A of the paper, strict curvature for every allowed penalty.
All active sets and positive scales are allowed. Taking the active set
empty gives the unforced law. -/
theorem penalized_strict_curvature (p : Parameters) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (I : Finset (Fin (N : ℕ))) (twoSided : Bool) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ∃ κ : ℝ, 0 < κ ∧ ∀ z ∈ intrinsicGapDomain N, ∀ u : gapTangentSpace N,
        κ * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (fun z : gapTangentSpace N =>
          p.val.1 * W Y(z) + p.val.1 * ∑ i ∈ I,
            (θ.val (a * (1 + z.val i)) +
              if twoSided then θ.val (a / (1 + z.val i)) else 0))) z u u := by
  obtain ⟨W, hW, hval, κ, C, hκ, _, hH⟩ := unforced_hessian_bounds N p hN
  let P : gapTangentSpace N → ℝ := fun z => ∑ i ∈ I,
    (θ.val (a * (1 + z.val i)) + if twoSided then θ.val (a / (1 + z.val i)) else 0)
  obtain ⟨hPs, hPc⟩ := selected_penalty_smooth_convex N θ ha I twoSided
  have hPsm : ContDiffOn ℝ ∞ (fun z => p.val.1 * P z) (intrinsicGapDomain N) :=
    contDiffOn_const.mul hPs
  have hPcv : ConvexOn ℝ (intrinsicGapDomain N) (fun z => p.val.1 * P z) :=
    hPc.smul p.property.1.le
  refine ⟨W, hW, hval, κ, hκ, fun z hz u => ?_⟩
  have hopen := AffineMetric.intrinsicGapDomain_isOpen N
  have hFs : ContDiffAt ℝ ∞ (fun z : gapTangentSpace N => p.val.1 * W Y(z)) z :=
    ((contDiffOn_const.mul (contDiffOn_intrinsic_pullback N hW)) z hz).contDiffAt
      (hopen.mem_nhds hz)
  have hPz := (hPsm z hz).contDiffAt (hopen.mem_nhds hz)
  have hadd := internal_hessian_add (hFs.of_le (by simp)) (hPz.of_le (by simp)) u u
  have hnonneg := Riesz1.fderiv_fderiv_nonneg_of_convexOn hopen
    (intrinsicGapDomain_convex N) hPcv (hPsm.of_le (by simp)) hz u
  change κ * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ
    (fun z : gapTangentSpace N => p.val.1 * W Y(z) + p.val.1 * P z)) z u u
  rw [hadd]
  linarith [(hH z hz u).1]

end PenalizedCurvature

section FrozenBridge

variable (N : ℕ+)

local notation "Y(" z ")" =>
  (WithLp.toLp 2 (fun i => 1 + (Subtype.val z) i) : EuclideanSpace ℝ (Fin (N : ℕ)))

/-- See Appendix A of the paper, strict-curvature bridge to the full physical potential. The realizing function agrees on all of `U_N`,
so its normal derivatives also use the ambient extension. -/
theorem fullPhysicalPotential_strict_curvature (p : Parameters) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ) (twoSided : Bool) :
    ∃ V : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ V (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        V y.val = fullPhysicalPotentialValue p N hN θ ε twoSided y) ∧
      ∃ κ : ℝ, 0 < κ ∧ ∀ z ∈ intrinsicGapDomain N, ∀ u : gapTangentSpace N,
        κ * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (fun z : gapTangentSpace N => V Y(z))) z u u := by
  classical
  let a := (N : ℝ) ^ (-ε)
  have ha : 0 < a := Real.rpow_pos_of_pos (by positivity) _
  obtain ⟨W, hW, hval, κ, hκ, hcurv⟩ :=
    penalized_strict_curvature N p hN θ ha Finset.univ twoSided
  let V : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ := fun y =>
    p.val.1 * W y + p.val.1 * ∑ i : Fin (N : ℕ),
      (θ.val (a * y i) + if twoSided then θ.val (a / y i) else 0)
  have hpos (y : EuclideanSpace ℝ (Fin (N : ℕ))) (hy : y ∈ gapAmbientDomain N)
      (i : Fin (N : ℕ)) : 0 < y i := by
    simpa only [PhysicalEnergy.gapSum_one] using (hy i 1 (by omega) (by omega)).1
  refine ⟨V, ?_, ?_, κ, hκ, ?_⟩
  · apply (contDiffOn_const.mul hW).add
    apply contDiffOn_const.mul
    apply ContDiffOn.sum
    intro i _ y hy
    have hi : ContDiffAt ℝ ∞ (fun y : EuclideanSpace ℝ (Fin (N : ℕ)) => y i) y :=
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (N : ℕ)) i).contDiff.contDiffAt
    have hup := (cutoff_contDiffAt θ (mul_pos ha (hpos y hy i))).comp y
      (contDiffAt_const.mul hi)
    cases twoSided
    · simpa only [Bool.false_eq_true, ↓reduceIte, add_zero, Function.comp_def,
        EuclideanSpace.coe_proj] using hup.contDiffWithinAt
    · have hinv := (cutoff_contDiffAt θ (div_pos ha (hpos y hy i))).comp y
        (contDiffAt_const.div hi (hpos y hy i).ne')
      simpa only [↓reduceIte, Function.comp_def, Pi.div_apply,
        EuclideanSpace.coe_proj] using (hup.add hinv).contDiffWithinAt
  · intro y
    change p.val.1 * W y.val + p.val.1 * (∑ i,
      (θ.val (a * y.val i) + if twoSided then θ.val (a / y.val i) else 0)) = _
    rw [hval y]
    dsimp only [fullPhysicalPotentialValue]
    simp only [a, div_eq_mul_inv]
    ring
  · intro z hz u
    simpa only [V] using hcurv z hz u

end FrozenBridge

end Riesz2.PhysicalCollision

end
