/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.PhysicalCollision
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Riesz2.Frozen.FullIntrinsicTiltedGapLaw
import Riesz2.Sanity.TiltedLaws

/-!
# Physical collision estimates with simultaneous singularities

Continuation of Appendix A. Radial derivatives are added before
passing to a gradient norm, so physical and inverse-penalty singularities
cannot cancel.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators ContDiff

namespace Riesz2.PhysicalCollision

/-- Internal scalar estimate for the physical radial derivative about gap one. -/
theorem internal_power_radial {s b : ℝ} (hs : 0 < s) (hb : 0 < b) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : ℝ, 0 < x →
      c * x ^ (-s - 1) - C ≤ b * (-s) * x ^ (-s - 1) * (x - 1) := by
  let c := b * s / 2
  let C := c * (1 / 2 : ℝ) ^ (-s - 1) + s * b * (1 / 2 : ℝ) ^ (-s) + 1
  have hc : 0 < c := by positivity
  have hC : 0 < C := by positivity
  refine ⟨c, C, hc, hC, fun x hx => ?_⟩
  by_cases h : x ≤ 1 / 2
  · have ht := mul_le_mul_of_nonneg_left (show (1 : ℝ) / 2 ≤ 1 - x by linarith)
      (show 0 ≤ b * s * x ^ (-s - 1) by positivity)
    have hCn : 0 ≤ C := hC.le
    dsimp only [c]
    nlinarith only [ht, hCn]
  · have ht := ElementaryBarriers.term_lower_bound hs hb one_pos hx
    have hp : x ^ (-s - 1) ≤ (1 / 2 : ℝ) ^ (-s - 1) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) (le_of_not_ge h) (by linarith)
    have hcp := mul_le_mul_of_nonneg_left hp hc.le
    dsimp only [C]
    nlinarith only [ht, hcp]

variable (N : ℕ+)

local notation "Y(" z ")" =>
  (WithLp.toLp 2 (fun i => 1 + (Subtype.val z) i) : EuclideanSpace ℝ (Fin (N : ℕ)))

/-- Internal chain rule for selected inverse penalties, in the radial direction
about the equally spaced configuration. -/
theorem internal_inverse_radial_derivative (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (I : Finset (Fin (N : ℕ))) {z : gapTangentSpace N} (hz : z ∈ intrinsicGapDomain N) :
    fderiv ℝ (fun w : gapTangentSpace N => ∑ i ∈ I, θ.val (a / (1 + w.val i))) z z =
      ∑ i ∈ I, deriv (fun t => θ.val (a / t)) (1 + z.val i) * z.val i := by
  let L (i : Fin (N : ℕ)) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).comp (gapTangentSpace N).subtypeL
  have hi (i : Fin (N : ℕ)) : HasFDerivAt (fun w : gapTangentSpace N =>
      θ.val (a / (1 + w.val i)))
      ((deriv (fun t => θ.val (a / t)) (1 + z.val i)) • L i) z := by
    have h := (inverse_penalty_hasDerivAt θ ha (hz i))
    rw [h.deriv]
    have hh := h.comp_hasFDerivAt (f := fun w : gapTangentSpace N => 1 + w.val i)
      z ((L i).hasFDerivAt.const_add 1)
    simpa only [Function.comp_def] using hh
  rw [(HasFDerivAt.fun_sum (u := I) (fun i _ => hi i)).fderiv]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  rfl

/-- Lemma A.1, Step 2, first bound of equation (A.2) in
the paper: the intrinsic gradient paired with the displacement from unit gaps.
The Boolean selects the inverse penalty, and the active set may be empty. -/
theorem penalized_radial_lower (p : Parameters) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (I : Finset (Fin (N : ℕ))) (twoSided : Bool) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z ∈ intrinsicGapDomain N,
        c * ((⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-p.val.2 - 1) +
          if twoSided then ∑ i ∈ I, (1 + z.val i)⁻¹ ^ 3 else 0) - C ≤
        inner ℝ (gradient (fun z : gapTangentSpace N => p.val.1 * W Y(z) + p.val.1 *
          ∑ i ∈ I, (θ.val (a * (1 + z.val i)) +
            if twoSided then θ.val (a / (1 + z.val i)) else 0)) z) z := by
  classical
  obtain ⟨W, hW, hval, hconv⟩ := RemovableGapBarrier.nearest_gap_barrier_convex p N hN
  have hp := p.property.1
  let R₀ : gapTangentSpace N → ℝ := fun z =>
    p.val.1 * (W Y(z) - 2 * ∑ i, (1 + z.val i) ^ (-p.val.2))
  have hR₀c : ConvexOn ℝ (intrinsicGapDomain N) R₀ :=
    (convexOn_intrinsic_pullback N hconv).smul hp.le
  have hR₀s : ContDiffOn ℝ ∞ R₀ (intrinsicGapDomain N) := by
    apply contDiffOn_const.mul
    apply (contDiffOn_intrinsic_pullback N hW).sub
    apply contDiffOn_const.mul
    apply ContDiffOn.sum
    intro i _
    have hi : ContDiff ℝ ∞ (fun z : gapTangentSpace N => 1 + z.val i) :=
      contDiff_const.add ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp
        (gapTangentSpace N).subtypeL.contDiff)
    exact hi.contDiffOn.rpow_const_of_ne (fun z hz => (hz i).ne')
  let U : gapTangentSpace N → ℝ := fun z => ∑ i ∈ I, θ.val (a * (1 + z.val i))
  have hUc : ConvexOn ℝ (intrinsicGapDomain N) U := by
    simpa only [Bool.false_eq_true, ↓reduceIte, add_zero] using
      (selected_penalty_smooth_convex N θ ha I false).2
  have hUs : ContDiffOn ℝ ∞ U (intrinsicGapDomain N) := by
    simpa only [Bool.false_eq_true, ↓reduceIte, add_zero] using
      (selected_penalty_smooth_convex N θ ha I false).1
  let R : gapTangentSpace N → ℝ := fun z => R₀ z + p.val.1 * U z
  have hRc : ConvexOn ℝ (intrinsicGapDomain N) R := hR₀c.add (hUc.smul hp.le)
  have hRs : ContDiffOn ℝ ∞ R (intrinsicGapDomain N) :=
    hR₀s.add (contDiffOn_const.mul hUs)
  have hopen := AffineMetric.intrinsicGapDomain_isOpen N
  have hdiff (z : gapTangentSpace N) (hz : z ∈ intrinsicGapDomain N) :
      DifferentiableAt ℝ R z := (hRs.contDiffAt (hopen.mem_nhds hz)).differentiableAt (by simp)
  have hzero : (0 : gapTangentSpace N) ∈ intrinsicGapDomain N := by
    intro i
    norm_num
  obtain ⟨r, hr⟩ := (intrinsicGapDomain_bounded N).subset_closedBall 0
  let D := max r 1
  have hD : 0 < D := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hnorm (z : gapTangentSpace N) (hz : z ∈ intrinsicGapDomain N) : ‖z‖ ≤ D := by
    have hh := Metric.mem_closedBall.mp (hr hz)
    simpa only [dist_zero_right] using hh.trans (le_max_left r 1)
  obtain ⟨c₀, C₀, hc₀, hC₀, hpower⟩ := internal_power_radial p.property.2.1
    (show 0 < 2 * p.val.1 by positivity)
  obtain ⟨c₁, C₁, hc₁, hC₁, hinverse⟩ := inverse_penalty_radial θ ha one_pos
  let c₂ := min c₀ (p.val.1 * c₁)
  have hc₂ : 0 < c₂ := lt_min hc₀ (mul_pos hp hc₁)
  let B := (N : ℝ) * C₀ + p.val.1 * (I.card : ℝ) * C₁ + ‖fderiv ℝ R 0‖ * D + 1
  have hB : 0 < B := by positivity
  refine ⟨W, hW, hval, c₂, B, hc₂, hB, fun z hz => ?_⟩
  let T : gapTangentSpace N → ℝ := fun w => ∑ i, (2 * p.val.1) *
    (gapFace N i w) ^ (-p.val.2) + R w
  let J : gapTangentSpace N → ℝ := fun w => ∑ i ∈ I, θ.val (a / (1 + w.val i))
  let V : gapTangentSpace N → ℝ := fun w => p.val.1 * W Y(w) + p.val.1 *
    ∑ i ∈ I, (θ.val (a * (1 + w.val i)) +
      if twoSided then θ.val (a / (1 + w.val i)) else 0)
  have he : V = fun w => T w + if twoSided then p.val.1 * J w else 0 := by
    funext w
    simp only [V, T, R, R₀, U, J, gapFace_apply, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    cases twoSided <;> simp only [Bool.false_eq_true, ↓reduceIte, Finset.sum_const_zero] <;> ring
  have hT : DifferentiableAt ℝ T z := by
    apply DifferentiableAt.add _ (hdiff z hz)
    apply DifferentiableAt.fun_sum
    intro i _
    have hi := ((EuclideanSpace.proj (𝕜 := ℝ) i).comp
      (gapTangentSpace N).subtypeL).hasFDerivAt (x := z) |>.const_add 1
    exact ((hi.rpow_const (p := -p.val.2) (Or.inl (hz i).ne')).const_mul _).differentiableAt
  have hJ : DifferentiableAt ℝ J z := by
    apply DifferentiableAt.fun_sum
    intro i _
    have hi := ((EuclideanSpace.proj (𝕜 := ℝ) i).comp
      (gapTangentSpace N).subtypeL).hasFDerivAt (x := z) |>.const_add 1
    exact ((inverse_penalty_hasDerivAt θ ha (hz i)).hasFDerivAt.comp z hi).differentiableAt
  have hfdT : fderiv ℝ T z z =
      ∑ i, (2 * p.val.1 * (-p.val.2) * (1 + z.val i) ^ (-p.val.2 - 1)) * z.val i +
        fderiv ℝ R z z := by
    have hh := ElementaryBarriers.fderiv_potential_apply
      (a := fun _ => 2 * p.val.1) (s := p.val.2) (ℓ := gapFace N)
      (fun i => (hz i).ne') (hdiff z hz) z
    have hl (i : Fin (N : ℕ)) :
        (LinearMap.toContinuousLinearMap (gapFace N i).linear) z = z.val i := by
      have ht := ElementaryBarriers.linear_sub_eq (gapFace N i) z 0
      simpa only [sub_zero, gapFace_apply, ZeroMemClass.coe_zero, PiLp.zero_apply,
        add_zero, add_sub_cancel_left] using ht
    simpa only [T, hl, gapFace_apply] using hh
  have hR := ElementaryBarriers.convex_fderiv_sub_lower hRc hz hzero
    (hdiff z hz) (hdiff 0 hzero) (by simpa only [sub_zero] using hnorm z hz)
  simp only [sub_zero] at hR
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpower _ (hz i))
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  have hfdTlow : c₀ * (∑ i, (1 + z.val i) ^ (-p.val.2 - 1)) -
      (N : ℝ) * C₀ - ‖fderiv ℝ R 0‖ * D ≤ fderiv ℝ T z z := by
    rw [hfdT]
    rw [Finset.mul_sum]
    have heq : (∑ i, 2 * p.val.1 * -p.val.2 * (1 + z.val i) ^ (-p.val.2 - 1) *
        (1 + z.val i - 1)) =
        ∑ i, 2 * p.val.1 * -p.val.2 * (1 + z.val i) ^ (-p.val.2 - 1) * z.val i := by
      simp only [add_sub_cancel_left]
    rw [heq] at hsum
    linarith
  have hinvsum := Finset.sum_le_sum (s := I) (fun i _ => hinverse _ (hz i))
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    add_sub_cancel_left, ← Finset.mul_sum] at hinvsum
  have hfdJlow : p.val.1 * c₁ * (∑ i ∈ I, (1 + z.val i)⁻¹ ^ 3) -
      p.val.1 * (I.card : ℝ) * C₁ ≤ p.val.1 * fderiv ℝ J z z := by
    rw [internal_inverse_radial_derivative N θ ha I hz]
    have hh := mul_le_mul_of_nonneg_left hinvsum hp.le
    nlinarith only [hh]
  obtain ⟨j, hj⟩ := ElementaryBarriers.exists_iInf_eq_apply (fun i : Fin (N : ℕ) => 1 + z.val i)
  have hmin : (⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-p.val.2 - 1) ≤
      ∑ i, (1 + z.val i) ^ (-p.val.2 - 1) := by
    rw [hj]
    exact Finset.single_le_sum (fun i _ => Real.rpow_nonneg (hz i).le _) (Finset.mem_univ j)
  have hphysical := mul_le_mul_of_nonneg_left hmin hc₂.le
  have hcoeff := mul_le_mul_of_nonneg_right (min_le_left c₀ (p.val.1 * c₁))
    (show 0 ≤ ∑ i, (1 + z.val i) ^ (-p.val.2 - 1) from
      Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hz i).le _))
  have hinvcoeff := mul_le_mul_of_nonneg_right (min_le_right c₀ (p.val.1 * c₁))
    (show 0 ≤ ∑ i ∈ I, (1 + z.val i)⁻¹ ^ 3 from
      Finset.sum_nonneg (fun i _ => pow_nonneg (inv_nonneg.mpr (hz i).le) _))
  have hlow : c₂ * ((⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-p.val.2 - 1) +
      if twoSided then ∑ i ∈ I, (1 + z.val i)⁻¹ ^ 3 else 0) - B ≤ fderiv ℝ V z z := by
    rw [he]
    cases twoSided
    · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
      dsimp only [B]
      have hnonneg : 0 ≤ p.val.1 * (I.card : ℝ) * C₁ := by positivity
      linarith only [hfdTlow, hphysical, hcoeff, hnonneg]
    · simp only [↓reduceIte]
      have hadd := (hT.hasFDerivAt.fun_add (hJ.hasFDerivAt.const_mul p.val.1)).fderiv
      rw [hadd]
      simp only [add_apply, smul_apply, smul_eq_mul]
      dsimp only [B]
      linarith only [hfdTlow, hfdJlow, hphysical, hcoeff, hinvcoeff]
  simpa only [inner_gradient_left] using hlow

/-- See Appendix A of the paper: the simultaneous physical and inverse-penalty
gradient bound, for every active set, including the empty set. The active
sum is stronger than its smallest-gap term and avoids an empty minimum. -/
theorem penalized_gradient_lower (p : Parameters) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (I : Finset (Fin (N : ℕ))) (twoSided : Bool) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z ∈ intrinsicGapDomain N,
        c * ((⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-p.val.2 - 1) +
          if twoSided then ∑ i ∈ I, (1 + z.val i)⁻¹ ^ 3 else 0) - C ≤
        ‖gradient (fun z : gapTangentSpace N => p.val.1 * W Y(z) + p.val.1 *
          ∑ i ∈ I, (θ.val (a * (1 + z.val i)) +
            if twoSided then θ.val (a / (1 + z.val i)) else 0)) z‖ := by
  obtain ⟨W, hW, hval, c, C, hc, hC, hrad⟩ :=
    penalized_radial_lower N p hN θ ha I twoSided
  obtain ⟨r, hr⟩ := (intrinsicGapDomain_bounded N).subset_closedBall 0
  let D := max r 1
  have hD : 0 < D := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨W, hW, hval, c / D, C / D, by positivity, by positivity, fun z hz => ?_⟩
  have hnorm : ‖z‖ ≤ D := by
    simpa only [dist_zero_right] using (Metric.mem_closedBall.mp (hr hz)).trans
      (le_max_left r 1)
  have hlow := hrad z hz
  rw [div_mul_eq_mul_div, ← sub_div, div_le_iff₀ hD]
  exact hlow.trans ((real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)))

/-- The scalar second Fréchet derivative, including its total-derivative convention. -/
theorem internal_scalar_hessian (f : ℝ → ℝ) (x u v : ℝ) :
    fderiv ℝ (fderiv ℝ f) x u v = deriv (deriv f) x * u * v := by
  have hh := iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod
    (n := 2) (f := f) (x := x) (m := ![u, v])
  simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.prod_univ_two, smul_eq_mul, iteratedDeriv_succ, iteratedDeriv_zero,
    mul_assoc, mul_left_comm, mul_comm] using hh

/-- Internal affine chain rule for a scalar Hessian. -/
theorem internal_scalar_affine_hessian {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → ℝ) (L : E →L[ℝ] ℝ) (b : ℝ) {z : E}
    (hf : ContDiffAt ℝ 2 f (L z + b)) (u : E) :
    fderiv ℝ (fderiv ℝ (fun w => f (L w + b))) z u u =
      deriv (deriv f) (L z + b) * (L u) ^ 2 := by
  rw [AffineMetricTransport.hessian_comp_affine L b hf, internal_scalar_hessian]
  ring

/-- Internal finite-sum Hessian identity. -/
theorem internal_hessian_sum {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : Finset ι) (f : ι → E → ℝ) {z : E} (hf : ∀ i ∈ I, ContDiffAt ℝ 2 (f i) z) (u : E) :
    fderiv ℝ (fderiv ℝ (fun w => ∑ i ∈ I, f i w)) z u u =
      ∑ i ∈ I, fderiv ℝ (fderiv ℝ (f i)) z u u := by
  have hh := congrArg (fun T : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ => T ![u,u])
    (iteratedFDeriv_fun_sum_apply hf)
  simpa only [sum_apply, iteratedFDeriv_two_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] using hh

/-- See Appendix A of the paper: the upper penalty has globally
bounded second derivative on the positive half-line. -/
theorem upper_penalty_curvature (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ a x : ℝ, 0 < a → 0 < x →
      0 ≤ deriv (deriv (fun t => θ.val (a * t))) x ∧
      deriv (deriv (fun t => θ.val (a * t))) x ≤ C * a ^ 2 := by
  obtain ⟨C, hC, hc, _⟩ := θ.property.2.2.2.2
  refine ⟨C, by linarith, fun a x ha hx => ?_⟩
  let L : ℝ →L[ℝ] ℝ := a • ContinuousLinearMap.id ℝ ℝ
  have hs : ContDiffAt ℝ 2 θ.val (L x + 0) := by
    simpa only [L, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, add_zero] using
      (cutoff_contDiffAt θ (mul_pos ha hx)).of_le (by simp)
  have hh := internal_scalar_affine_hessian θ.val L 0 hs 1
  simp only [L, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, add_zero,
    mul_one, internal_scalar_hessian] at hh
  have hn := (hc (a * x) (mul_pos ha hx)).1
  have hu := (hc (a * x) (mul_pos ha hx)).2
  rw [hh]
  exact ⟨mul_nonneg hn (sq_nonneg a), by nlinarith only [mul_le_mul_of_nonneg_right hu (sq_nonneg a)]⟩

/-- See Appendix A of the paper: selected penalty Hessians have the claimed
fourth-order upper bound, on every positive gap and for every active set. -/
theorem selected_penalty_hessian_upper (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (I : Finset (Fin (N : ℕ))) (twoSided : Bool) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ intrinsicGapDomain N, ∀ u : gapTangentSpace N,
      fderiv ℝ (fderiv ℝ (fun w : gapTangentSpace N => ∑ i ∈ I,
        (θ.val (a * (1 + w.val i)) +
          if twoSided then θ.val (a / (1 + w.val i)) else 0))) z u u ≤
        C * (1 + if twoSided then ∑ i ∈ I, (1 + z.val i)⁻¹ ^ 4 else 0) * ‖u‖ ^ 2 := by
  classical
  obtain ⟨C₀, hC₀, hup⟩ := upper_penalty_curvature θ
  obtain ⟨C₁, hC₁, hinv⟩ := inverse_penalty_curvature θ
  let C := C₀ * a ^ 2 * (I.card : ℝ) + C₁ * a ^ 2 + 1
  have hC : 0 < C := by positivity
  refine ⟨C, hC, fun z hz u => ?_⟩
  let φ : ℝ → ℝ := fun t => θ.val (a * t) + if twoSided then θ.val (a / t) else 0
  have hφ (t : ℝ) (ht : 0 < t) : ContDiffAt ℝ ∞ φ t := by
    have hu := (cutoff_contDiffAt θ (mul_pos ha ht)).comp t (contDiffAt_const.mul contDiffAt_id)
    cases twoSided
    · simpa only [φ, Bool.false_eq_true, ↓reduceIte, add_zero, Function.comp_def] using hu
    · have hi := (cutoff_contDiffAt θ (div_pos ha ht)).comp t
        (contDiffAt_const.div contDiffAt_id ht.ne')
      simpa only [φ, ↓reduceIte, Function.comp_def, Pi.div_apply] using hu.add hi
  have hφ'' (t : ℝ) (ht : 0 < t) : deriv (deriv φ) t ≤
      C₀ * a ^ 2 + if twoSided then C₁ * a ^ 2 * t⁻¹ ^ 4 else 0 := by
    cases twoSided
    · simpa only [φ, Bool.false_eq_true, ↓reduceIte, add_zero] using (hup a t ha ht).2
    · have hu := (cutoff_contDiffAt θ (mul_pos ha ht)).comp t
          (contDiffAt_const.mul contDiffAt_id)
      have hi := (cutoff_contDiffAt θ (div_pos ha ht)).comp t
          (contDiffAt_const.div contDiffAt_id ht.ne')
      have hh := internal_hessian_add (hu.of_le (by simp)) (hi.of_le (by simp)) 1 1
      simp only [internal_scalar_hessian, mul_one] at hh
      change deriv (deriv (fun t => θ.val (a * t) + θ.val (a / t))) t =
        deriv (deriv (fun t => θ.val (a * t))) t +
          deriv (deriv (fun t => θ.val (a / t))) t at hh
      change deriv (deriv (fun t => θ.val (a * t) + θ.val (a / t))) t ≤ _
      rw [hh]
      exact add_le_add (hup a t ha ht).2 (hinv a t ha ht).2
  let L (i : Fin (N : ℕ)) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).comp (gapTangentSpace N).subtypeL
  have hL (i : Fin (N : ℕ)) (w : gapTangentSpace N) : L i w = w.val i := rfl
  have hi (i : Fin (N : ℕ)) : ContDiffAt ℝ 2
      (fun w : gapTangentSpace N => φ (1 + w.val i)) z :=
    ((hφ _ (hz i)).comp z (contDiff_const.add (L i).contDiff).contDiffAt).of_le (by simp)
  have hterm (i : Fin (N : ℕ)) : fderiv ℝ (fderiv ℝ
      (fun w : gapTangentSpace N => φ (1 + w.val i))) z u u ≤
      (C₀ * a ^ 2 + if twoSided then C₁ * a ^ 2 * (1 + z.val i)⁻¹ ^ 4 else 0) * ‖u‖ ^ 2 := by
    have hh := internal_scalar_affine_hessian φ (L i) 1
      (show ContDiffAt ℝ 2 φ (L i z + 1) from by
        simpa only [hL, add_comm] using (hφ _ (hz i)).of_le (by simp)) u
    have he : (fun w : gapTangentSpace N => φ (1 + w.val i)) = fun w => φ (L i w + 1) := by
      funext w
      congr 1
      exact add_comm _ _
    rw [he, hh]
    have hsq : (L i u) ^ 2 ≤ ‖u‖ ^ 2 := by
      have ht := PiLp.norm_apply_le (p := (2 : ENNReal)) u.val i
      rw [Real.norm_eq_abs, Submodule.norm_coe] at ht
      simpa only [hL, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) ht 2
    have hnn : 0 ≤ C₀ * a ^ 2 + if twoSided then C₁ * a ^ 2 * (1 + z.val i)⁻¹ ^ 4 else 0 := by
      cases twoSided <;> simp only [Bool.false_eq_true, ↓reduceIte, add_zero] <;> positivity
    exact mul_le_mul (by simpa only [hL, add_comm] using hφ'' _ (hz i)) hsq
      (sq_nonneg _) hnn
  have hsum := Finset.sum_le_sum (s := I) (fun i _ => hterm i)
  rw [internal_hessian_sum I _ (fun i _ => hi i) u]
  apply hsum.trans
  rw [← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg ‖u‖)
  have h₀ : C₀ * a ^ 2 * (I.card : ℝ) ≤ C := by
    dsimp only [C]
    have hh : 0 ≤ C₁ * a ^ 2 := by positivity
    linarith
  have h₁ : C₁ * a ^ 2 ≤ C := by
    dsimp only [C]
    have hh : 0 ≤ C₀ * a ^ 2 * (I.card : ℝ) :=
      mul_nonneg (mul_nonneg hC₀.le (sq_nonneg a)) (Nat.cast_nonneg I.card)
    linarith
  cases twoSided
  · simp only [Bool.false_eq_true, ↓reduceIte, add_zero, Finset.sum_const,
      nsmul_eq_mul, mul_one]
    nlinarith only [h₀]
  · simp only [↓reduceIte, Finset.sum_add_distrib, Finset.sum_const,
      nsmul_eq_mul, ← Finset.mul_sum]
    have hs : 0 ≤ ∑ i ∈ I, (1 + z.val i)⁻¹ ^ 4 :=
      Finset.sum_nonneg (fun i _ => pow_nonneg (inv_nonneg.mpr (hz i).le) _)
    nlinarith only [h₀, mul_le_mul_of_nonneg_right h₁ hs]

/-- See Appendix A of the paper: simultaneous intrinsic gradient, trace and
strict-curvature estimates for all allowed penalties. All parameters of
an allowed penalty are arbitrary, and all analytic estimates are conclusions. -/
theorem penalized_differential_estimates (p : Parameters) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (I : Finset (Fin (N : ℕ))) (twoSided : Bool) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ∃ c C κ : ℝ, 0 < c ∧ 0 < C ∧ 0 < κ ∧ ∀ z ∈ intrinsicGapDomain N,
        let V := fun w : gapTangentSpace N => p.val.1 * W Y(w) + p.val.1 *
          ∑ i ∈ I, (θ.val (a * (1 + w.val i)) +
            if twoSided then θ.val (a / (1 + w.val i)) else 0)
        c * ((⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-p.val.2 - 1) +
          if twoSided then ∑ i ∈ I, (1 + z.val i)⁻¹ ^ 3 else 0) - C ≤ ‖gradient V z‖ ∧
        Laplacian.laplacian V z ≤ C * (1 +
          (⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-p.val.2 - 2) +
          if twoSided then ∑ i ∈ I, (1 + z.val i)⁻¹ ^ 4 else 0) ∧
        ∀ u : gapTangentSpace N, κ * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) z u u := by
  obtain ⟨W, hW, hval, κ, Cw, hκ, hCw, hH⟩ := unforced_hessian_bounds N p hN
  obtain ⟨W₁, _, hval₁, c, Cg, hc, hCg, hG⟩ := penalized_gradient_lower N p hN θ ha I twoSided
  obtain ⟨Cp, hCp, hP⟩ := selected_penalty_hessian_upper N θ ha I twoSided
  let P : gapTangentSpace N → ℝ := fun w => ∑ i ∈ I,
    (θ.val (a * (1 + w.val i)) + if twoSided then θ.val (a / (1 + w.val i)) else 0)
  obtain ⟨hPs, hPc⟩ := selected_penalty_smooth_convex N θ ha I twoSided
  let D := (Module.finrank ℝ (gapTangentSpace N) : ℝ) * (Cw + p.val.1 * Cp)
  have hD : 0 ≤ D := mul_nonneg (Nat.cast_nonneg _)
    (add_nonneg hCw.le (mul_nonneg p.property.1.le hCp.le))
  refine ⟨W, hW, hval, c, max Cg D, κ, hc, lt_of_lt_of_le hCg (le_max_left _ _), hκ, ?_⟩
  intro z hz
  let V : gapTangentSpace N → ℝ := fun w => p.val.1 * W Y(w) + p.val.1 * P w
  have hopen := AffineMetric.intrinsicGapDomain_isOpen N
  have hFs : ContDiffAt ℝ ∞ (fun w : gapTangentSpace N => p.val.1 * W Y(w)) z :=
    ((contDiffOn_const.mul (contDiffOn_intrinsic_pullback N hW)) z hz).contDiffAt (hopen.mem_nhds hz)
  have hPz : ContDiffAt ℝ ∞ P z := (hPs z hz).contDiffAt (hopen.mem_nhds hz)
  have hPβ : ContDiffAt ℝ ∞ (fun w => p.val.1 * P w) z := contDiffAt_const.mul hPz
  have hadd (u : gapTangentSpace N) := internal_hessian_add
    (hFs.of_le (by simp)) (hPβ.of_le (by simp)) u u
  have hmul (u : gapTangentSpace N) := internal_hessian_const_mul (hPz.of_le (by simp)) p.val.1 u u
  have hY : 0 ≤ if twoSided then ∑ i ∈ I, (1 + z.val i)⁻¹ ^ 4 else 0 := by
    split_ifs
    · exact Finset.sum_nonneg (fun i _ => pow_nonneg (inv_nonneg.mpr (hz i).le) _)
    · exact le_rfl
  have hδ : 0 ≤ (⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-p.val.2 - 2) :=
    Real.rpow_nonneg (minimum_gap_pos N hz).le _
  have hupper (u : gapTangentSpace N) : fderiv ℝ (fderiv ℝ V) z u u ≤
      (Cw * (⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-p.val.2 - 2) +
        p.val.1 * Cp * (1 + if twoSided then ∑ i ∈ I, (1 + z.val i)⁻¹ ^ 4 else 0)) * ‖u‖ ^ 2 := by
    change fderiv ℝ (fderiv ℝ (fun w => p.val.1 * W Y(w) + p.val.1 * P w)) z u u ≤ _
    rw [hadd, hmul]
    have hh := mul_le_mul_of_nonneg_left (hP z hz u) p.property.1.le
    change p.val.1 * fderiv ℝ (fderiv ℝ P) z u u ≤ _ at hh
    nlinarith only [(hH z hz u).2, hh]
  have htrace := internal_laplacian_le V z _ hupper
  have htrace' : Laplacian.laplacian V z ≤ D * (1 +
      (⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-p.val.2 - 2) +
      if twoSided then ∑ i ∈ I, (1 + z.val i)⁻¹ ^ 4 else 0) := by
    apply htrace.trans
    dsimp only [D]
    simp only [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have h₀ : 0 ≤ Cw * (1 + if twoSided then ∑ i ∈ I, (1 + z.val i)⁻¹ ^ 4 else 0) :=
      mul_nonneg hCw.le (by linarith)
    have h₁ : 0 ≤ p.val.1 * Cp * (⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-p.val.2 - 2) :=
      mul_nonneg (mul_nonneg p.property.1.le hCp.le) hδ
    nlinarith only [h₀, h₁]
  have he : (fun w : gapTangentSpace N => p.val.1 * W₁ Y(w) + p.val.1 * P w) =ᶠ[𝓝 z] V := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    have hwU := PhysicalEnergy.simplex_subset_ambient N _ (intrinsic_chart_mem_simplex N hw)
    dsimp only [V]
    rw [hval₁ ⟨Y(w), hwU⟩, hval ⟨Y(w), hwU⟩]
  have hg := hG z hz
  change _ ≤ ‖gradient (fun w : gapTangentSpace N => p.val.1 * W₁ Y(w) + p.val.1 * P w) z‖ at hg
  rw [he.gradient_eq] at hg
  refine ⟨by linarith [le_max_left Cg D], htrace'.trans ?_, fun u => ?_⟩
  · exact mul_le_mul_of_nonneg_right (le_max_right Cg D) (by linarith)
  · change κ * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ
        (fun w : gapTangentSpace N => p.val.1 * W Y(w) + p.val.1 * P w)) z u u
    rw [hadd, hmul]
    have hn := Riesz1.fderiv_fderiv_nonneg_of_convexOn hopen (intrinsicGapDomain_convex N)
      hPc (hPs.of_le (by simp)) hz u
    change 0 ≤ fderiv ℝ (fderiv ℝ P) z u u at hn
    have hh := mul_nonneg p.property.1.le hn
    linarith only [(hH z hz u).1, hh]

/-- Internal absorption of a finite family of fourth-order singularities.
The leading cubic sum is squared only after the contributions are added. -/
theorem internal_inverse_sum_absorption {ι : Type*} (I : Finset ι) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 ≤ β) :
    ∃ D : ℝ, ∀ y : ι → ℝ, (∀ i ∈ I, 0 < y i) →
      β * (∑ i ∈ I, (y i)⁻¹ ^ 4) ≤ α * (∑ i ∈ I, (y i)⁻¹ ^ 3) ^ 2 + D := by
  obtain ⟨D, hD⟩ := RpowDomination.exists_bound (s := 2) (α := α) (β := β) (γ := 0)
    (by norm_num) hα hβ le_rfl
  refine ⟨(I.card : ℝ) * D, fun y hy => ?_⟩
  have hterm (i : ι) (hi : i ∈ I) : β * (y i)⁻¹ ^ 4 ≤ α * ((y i)⁻¹ ^ 3) ^ 2 + D := by
    have hh := hD (y i) (hy i hi)
    norm_num [Real.rpow_neg, inv_pow] at hh
    simp only [← inv_pow] at hh
    linarith only [hh, hβ]
  have hsum := Finset.sum_le_sum hterm
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum] at hsum
  have hsq := Finset.sum_sq_le_sq_sum_of_nonneg
    (fun i hi => pow_nonneg (inv_nonneg.mpr (hy i hi).le) 3)
  exact hsum.trans (by linarith only [mul_le_mul_of_nonneg_left hsq hα.le])

/-- Internal mixed-power collision criterion. Its gradient and trace
premises are supplied by `penalized_differential_estimates`. -/
theorem internal_mixed_collision (hN : 2 ≤ (N : ℕ)) {s : ℝ} (hs : 0 < s)
    (I : Finset (Fin (N : ℕ))) (twoSided : Bool) (V : gapTangentSpace N → ℝ)
    {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hg : ∀ z ∈ intrinsicGapDomain N,
      c * ((⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-s - 1) +
        if twoSided then ∑ i ∈ I, (1 + z.val i)⁻¹ ^ 3 else 0) - C ≤ ‖gradient V z‖)
    (hΔ : ∀ z ∈ intrinsicGapDomain N, Laplacian.laplacian V z ≤ C *
      (1 + (⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-s - 2) +
        if twoSided then ∑ i ∈ I, (1 + z.val i)⁻¹ ^ 4 else 0)) :
    ∀ A K : ℝ, 0 < A → 0 < K → ∃ D : ℝ, 0 ≤ D ∧ ∀ z ∈ intrinsicGapDomain N,
      K * (Metric.infDist z (frontier (intrinsicGapDomain N)))⁻¹ ^ 2 - D ≤
        A * ‖gradient V z‖ ^ 2 - Laplacian.laplacian V z := by
  have := tangent_nontrivial N hN
  intro A K hA hK
  let α := A * c ^ 2 / 4
  have hα : 0 < α := by positivity
  obtain ⟨G, hG, hlip⟩ := AffinePolytope.exists_lipschitz (gapFace N)
  obtain ⟨D₀, hD₀⟩ := RpowDomination.exists_bound hs hα hC.le
    (show 0 ≤ K * G ^ 2 by positivity)
  obtain ⟨D₁, hD₁⟩ := internal_inverse_sum_absorption I hα hC.le
  let E := D₀ + (if twoSided then D₁ else 0) + A * C ^ 2
  refine ⟨max E 0, le_max_right _ _, fun z hz => ?_⟩
  let δ := ⨅ i : Fin (N : ℕ), 1 + z.val i
  let X := δ ^ (-s - 1)
  let Y := if twoSided then ∑ i ∈ I, (1 + z.val i)⁻¹ ^ 3 else 0
  let Z := if twoSided then ∑ i ∈ I, (1 + z.val i)⁻¹ ^ 4 else 0
  have hδ : 0 < δ := minimum_gap_pos N hz
  have hX : 0 ≤ X := Real.rpow_nonneg hδ.le _
  have hY : 0 ≤ Y := by
    cases twoSided
    · exact le_rfl
    · exact Finset.sum_nonneg (fun i _ => pow_nonneg (inv_nonneg.mpr (hz i).le) _)
  have hinv : C * Z ≤ α * Y ^ 2 + if twoSided then D₁ else 0 := by
    cases twoSided
    · simp only [Y, Z, Bool.false_eq_true, ↓reduceIte, mul_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, add_zero, le_refl]
    · exact hD₁ (fun i => 1 + z.val i) (fun i _ => hz i)
  have hdom := hD₀ δ hδ
  have hd := AffinePolytope.div_le_infDist_frontier (gapFace N) (Ω := intrinsicGapDomain N) rfl
    (intrinsicGapDomain_bounded N) hG hlip hz
  simp only [gapFace_apply] at hd
  have hdpos : 0 < δ / G := div_pos hδ hG
  have hdsq := pow_le_pow_left₀ hdpos.le hd 2
  have hdist : (Metric.infDist z (frontier (intrinsicGapDomain N)))⁻¹ ^ 2 ≤ G ^ 2 * (δ ^ 2)⁻¹ := by
    have hh := inv_anti₀ (pow_pos hdpos 2) hdsq
    have he : ((δ / G) ^ 2)⁻¹ = G ^ 2 * (δ ^ 2)⁻¹ := by field_simp
    simpa only [he, inv_pow] using hh
  have hKdist := mul_le_mul_of_nonneg_left hdist hK.le
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
  change C * (1 + δ ^ (-s - 2)) + K * G ^ 2 * (δ ^ 2)⁻¹ ≤ α * X ^ 2 + D₀ at hdom
  have hE : E ≤ max E 0 := le_max_left _ _
  dsimp only [E] at hE
  linarith only [hdom, hinv, hKdist, hAgrad, hlead, htrace, hE]

/-- See Appendix A of the paper: every allowed penalized intrinsic physical
potential satisfies the collision criterion for all positive coefficients.
No gradient, trace, or admissibility hypothesis is assumed. -/
theorem penalized_collision_criterion (p : Parameters) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (I : Finset (Fin (N : ℕ))) (twoSided : Bool) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ∃ κ : ℝ, 0 < κ ∧
      (∀ z ∈ intrinsicGapDomain N, ∀ u : gapTangentSpace N,
        κ * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (fun w : gapTangentSpace N =>
          p.val.1 * W Y(w) + p.val.1 * ∑ i ∈ I,
            (θ.val (a * (1 + w.val i)) +
              if twoSided then θ.val (a / (1 + w.val i)) else 0))) z u u) ∧
      ∀ A K : ℝ, 0 < A → 0 < K → ∃ D : ℝ, 0 ≤ D ∧ ∀ z ∈ intrinsicGapDomain N,
        let V := fun w : gapTangentSpace N => p.val.1 * W Y(w) + p.val.1 * ∑ i ∈ I,
          (θ.val (a * (1 + w.val i)) + if twoSided then θ.val (a / (1 + w.val i)) else 0)
        K * (Metric.infDist z (frontier (intrinsicGapDomain N)))⁻¹ ^ 2 - D ≤
          A * ‖gradient V z‖ ^ 2 - Laplacian.laplacian V z := by
  obtain ⟨W, hW, hval, c, C, κ, hc, hC, hκ, hest⟩ :=
    penalized_differential_estimates N p hN θ ha I twoSided
  refine ⟨W, hW, hval, κ, hκ, fun z hz => (hest z hz).2.2, ?_⟩
  exact internal_mixed_collision N hN p.property.2.1 I twoSided _ hc hC
    (fun z hz => (hest z hz).1) (fun z hz => (hest z hz).2.1)

/-- See Appendix A of the paper: the displayed estimates using the smallest
active gap, for a nonempty active set with inverse forcing. -/
theorem penalized_minimum_gap_estimates (p : Parameters) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (I : Finset (Fin (N : ℕ))) (hI : I.Nonempty) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z ∈ intrinsicGapDomain N,
        let d := ⨅ i : Fin (N : ℕ), 1 + z.val i
        let dI := ⨅ i : I, 1 + z.val i.val
        let V := fun w : gapTangentSpace N => p.val.1 * W Y(w) + p.val.1 * ∑ i ∈ I,
          (θ.val (a * (1 + w.val i)) + θ.val (a / (1 + w.val i)))
        0 < dI ∧ c * (d ^ (-p.val.2 - 1) + dI⁻¹ ^ 3) - C ≤ ‖gradient V z‖ ∧
          Laplacian.laplacian V z ≤ C * (1 + d ^ (-p.val.2 - 2) + dI⁻¹ ^ 4) := by
  classical
  have : Nonempty I := hI.coe_sort
  obtain ⟨W, hW, hval, c, C, κ, hc, hC, _, hest⟩ :=
    penalized_differential_estimates N p hN θ ha I true
  let D := C * ((I.card : ℝ) + 1)
  have hDC : C ≤ D := by
    have hh := mul_nonneg hC.le (Nat.cast_nonneg (α := ℝ) I.card)
    dsimp only [D]
    nlinarith only [hh]
  refine ⟨W, hW, hval, c, D, hc, lt_of_lt_of_le hC hDC, fun z hz => ?_⟩
  dsimp only
  obtain ⟨j, hj⟩ := ElementaryBarriers.exists_iInf_eq_apply (fun i : I => 1 + z.val i.val)
  have hdI : 0 < ⨅ i : I, 1 + z.val i.val := by rw [hj]; exact hz j.val
  have hsmall : (⨅ i : I, 1 + z.val i.val)⁻¹ ^ 3 ≤ ∑ i ∈ I, (1 + z.val i)⁻¹ ^ 3 := by
    rw [hj]
    exact Finset.single_le_sum (fun i _ => pow_nonneg (inv_nonneg.mpr (hz i).le) _) j.property
  have hsum : (∑ i ∈ I, (1 + z.val i)⁻¹ ^ 4) ≤
      (I.card : ℝ) * (⨅ i : I, 1 + z.val i.val)⁻¹ ^ 4 := by
    calc
      _ ≤ ∑ _i ∈ I, (⨅ i : I, 1 + z.val i.val)⁻¹ ^ 4 := by
        apply Finset.sum_le_sum
        intro i hi
        have hle := ciInf_le (Finite.bddBelow_range (fun i : I => 1 + z.val i.val)) ⟨i, hi⟩
        exact pow_le_pow_left₀ (inv_nonneg.mpr (hz i).le) (inv_anti₀ hdI hle) 4
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have h := hest z hz
  simp only [↓reduceIte] at h
  refine ⟨hdI, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_left hsmall hc.le
    linarith only [h.1, hh, hDC]
  · have hδ : 0 ≤ (⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-p.val.2 - 2) :=
      Real.rpow_nonneg (minimum_gap_pos N hz).le _
    have hq : 0 ≤ (⨅ i : I, 1 + z.val i.val)⁻¹ ^ 4 := by positivity
    have h₀ := mul_le_mul_of_nonneg_left hsum hC.le
    have h₁ := mul_nonneg (Nat.cast_nonneg (α := ℝ) I.card) (by linarith : 0 ≤ 1 +
      (⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-p.val.2 - 2))
    dsimp only [D]
    have hh := mul_nonneg hC.le h₁
    nlinarith only [h.2.1, h₀, hh, mul_nonneg hC.le hq]

/-- See Appendix A of the paper: the full physical potential has
strict intrinsic curvature and satisfies every collision criterion. The
ambient realization agrees on all of the ambient domain. -/
theorem fullPhysicalPotential_collision_criterion (p : Parameters) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ) (twoSided : Bool) :
    ∃ V : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ V (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        V y.val = fullPhysicalPotentialValue p N hN θ ε twoSided y) ∧
      ∃ κ : ℝ, 0 < κ ∧
      (∀ z ∈ intrinsicGapDomain N, ∀ u : gapTangentSpace N,
        κ * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (fun z : gapTangentSpace N => V Y(z))) z u u) ∧
      ∀ A K : ℝ, 0 < A → 0 < K → ∃ D : ℝ, 0 ≤ D ∧ ∀ z ∈ intrinsicGapDomain N,
        K * (Metric.infDist z (frontier (intrinsicGapDomain N)))⁻¹ ^ 2 - D ≤
          A * ‖gradient (fun z : gapTangentSpace N => V Y(z)) z‖ ^ 2 -
            Laplacian.laplacian (fun z : gapTangentSpace N => V Y(z)) z := by
  classical
  let a := (N : ℝ) ^ (-ε)
  have ha : 0 < a := Real.rpow_pos_of_pos (by positivity) _
  obtain ⟨W, hW, hval, κ, hκ, hcurv, hcoll⟩ :=
    penalized_collision_criterion N p hN θ ha Finset.univ twoSided
  let V : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ := fun y =>
    p.val.1 * W y + p.val.1 * ∑ i : Fin (N : ℕ),
      (θ.val (a * y i) + if twoSided then θ.val (a / y i) else 0)
  have hpos (y : EuclideanSpace ℝ (Fin (N : ℕ))) (hy : y ∈ gapAmbientDomain N)
      (i : Fin (N : ℕ)) : 0 < y i := by
    simpa only [PhysicalEnergy.gapSum_one] using (hy i 1 (by omega) (by omega)).1
  refine ⟨V, ?_, ?_, κ, hκ, ?_, ?_⟩
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
  · simpa only [V] using hcoll

/-- See Subsection 3.2 of the paper: the centering map inverts the intrinsic chart. -/
theorem centered_chart_inverse (z : gapTangentSpace N) : centeredGapChart N Y(z) = z := by
  have hsum : (∑ i : Fin (N : ℕ), (1 + z.val i)) = (N : ℝ) := by
    rw [Finset.sum_add_distrib, z.property]
    simp
  apply Subtype.ext
  ext i
  change 1 + z.val i - (∑ j : Fin (N : ℕ), (1 + z.val j)) / (N : ℝ) = z.val i
  rw [hsum, div_self (show (N : ℝ) ≠ 0 by exact_mod_cast N.pos.ne')]
  ring
/-- See Subsection 1.7 and Appendix A of the paper: intrinsic configuration-volume
identity, including the fixed finite-dimensional Jacobian. -/
theorem configurationVolume_intrinsic (n : ℕ) :
    (Riesz1.configurationVolume n.succPNat).map
      (fun X => centeredGapChart n.succPNat (WithLp.toLp 2 (gapVector X))) =
      (ENNReal.ofReal ((n + 1 : ℝ) ^ n))⁻¹ •
        (ENNReal.ofReal (Real.sqrt (n + 1)))⁻¹ •
          (volume.restrict (intrinsicGapDomain n.succPNat)) := by
  let raw : Riesz1.Configuration n.succPNat → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun X => WithLp.toLp 2 (gapVector X)
  let yChart : gapTangentSpace n.succPNat → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun z => WithLp.toLp 2 (fun i => 1 + z.val i)
  have hchartMeas : Measurable yChart := by fun_prop
  have hchartEmb : MeasurableEmbedding yChart := DefinitionSanity.full_chart_embedding n.succPNat
  have : SFinite (AffineSimplex.simplexVolume n (n + 1)) := by
    rw [AffineSimplex.simplexVolume_eq]
    infer_instance
  have hmraw : Measurable raw := (WithLp.measurable_toLp 2 _).comp
    (Measurable.of_eval (fun i => DefinitionSanity.gap_measurable i.val))
  have hraw := congrArg (Measure.map Prod.snd) (GapChart.map_configurationVolume_intrinsic n)
  have hmjoint : Measurable (fun X : Riesz1.Configuration n.succPNat => (X.val 0, raw X)) :=
    (show Measurable (fun X : Riesz1.Configuration n.succPNat => X.val 0) from
      (measurable_pi_apply 0).comp measurable_subtype_coe).prodMk hmraw
  rw [Measure.map_map measurable_snd hmjoint, Measure.map_snd_prod] at hraw
  have hrot : (volume.restrict (Ico (0 : ℝ) 1)) univ = 1 := by simp
  rw [hrot, one_smul] at hraw
  change (Riesz1.configurationVolume n.succPNat).map raw = _ at hraw
  let e := AffineMetric.orthTangentEquiv n.succPNat
  have hY : (fun z : AffineSimplex.Tangent n => yChart (e z)) =
      AffineSimplex.centredChart n (n + 1) := by
    funext z
    ext i
    change 1 + z.val i = z.val i + (n + 1 : ℝ) / (n + 1)
    rw [div_self (by positivity : (n + 1 : ℝ) ≠ 0)]
    ring
  have hYv : (volume : Measure (gapTangentSpace n.succPNat)).map
      (fun z : gapTangentSpace n.succPNat => yChart z) =
      AffineSimplex.hyperplaneVolume n (n + 1) := by
    erw [← e.measurePreserving.map_eq, Measure.map_map hchartMeas
      e.continuous.measurable]
    change Measure.map (fun z => yChart (e z)) volume = _
    erw [hY]
    exact AffineSimplex.map_volume_centredChart n (n + 1)
  have hpre : (fun z : gapTangentSpace n.succPNat => yChart z) ⁻¹'
      AffineSimplex.massSimplex n (n + 1) = intrinsicGapDomain n.succPNat := by
    ext z
    change ((∀ i, 0 < 1 + z.val i) ∧ (∑ i, (1 + z.val i)) = (n + 1 : ℝ)) ↔ _
    have hsum : (∑ i, (1 + z.val i)) = (n + 1 : ℝ) := by
      rw [Finset.sum_add_distrib, z.property]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one, add_zero]
      change ((Finset.univ : Finset (Fin (n + 1))).card : ℝ) = (n + 1 : ℝ)
      simp
    simp only [hsum, and_true]
    rfl
  have hsimplex : AffineSimplex.simplexVolume n (n + 1) =
      (volume.restrict (intrinsicGapDomain n.succPNat)).map
        (fun z : gapTangentSpace n.succPNat => yChart z) := by
    erw [AffineSimplex.simplexVolume_eq_restrict, ← hYv,
      hchartEmb.restrict_map, hpre]
  change (Riesz1.configurationVolume n.succPNat).map (centeredGapChart n.succPNat ∘ raw) = _
  erw [← Measure.map_map (DefinitionSanity.centered_chart_continuous n.succPNat).measurable hmraw,
    hraw, Measure.map_smul _ (DefinitionSanity.centered_chart_continuous n.succPNat).measurable.aemeasurable,
    Measure.map_smul _ (DefinitionSanity.centered_chart_continuous n.succPNat).measurable.aemeasurable,
    hsimplex, Measure.map_map (DefinitionSanity.centered_chart_continuous n.succPNat).measurable
      hchartMeas]
  have hleft : centeredGapChart n.succPNat ∘ yChart = id :=
    funext (centered_chart_inverse n.succPNat)
  erw [hleft, Measure.map_id]
  rw [ENNReal.ofReal_inv_of_pos (pow_pos (by positivity : (0 : ℝ) < n + 1) _)]
/-- Internal density-identification bridge. Its smooth realization is supplied
by `fullPhysicalPotential_wellposed`, and is never an extra hypothesis there. -/
theorem internal_full_gap_gibbs (p : Parameters) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ) (twoSided : Bool)
    (V : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ)
    (hV : ContDiffOn ℝ ∞ V (gapAmbientDomain N))
    (hval : ∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
      V y.val = fullPhysicalPotentialValue p N hN θ ε twoSided y) :
    IsEuclideanGibbsPotential volume (fullIntrinsicTiltedGapLaw p N θ ε twoSided)
      (intrinsicGapDomain N) (fun z : gapTangentSpace N => V Y(z)) := by
  classical
  let T : Riesz1.Configuration N → gapTangentSpace N :=
    fun X => centeredGapChart N (WithLp.toLp 2 (gapVector X))
  have hT : Measurable T := DefinitionSanity.intrinsic_projection_measurable N
  have hraw (X : Riesz1.Configuration N) : Y(T X) = WithLp.toLp 2 (gapVector X) := by
    ext i
    change 1 + (gap X i.val - (∑ j : Fin (N : ℕ), gap X j.val) / (N : ℝ)) = gap X i.val
    rw [DefinitionSanity.actual_gap_sum, div_self (show (N : ℝ) ≠ 0 by exact_mod_cast N.pos.ne')]
    ring
  have hmem (X : Riesz1.Configuration N) : T X ∈ intrinsicGapDomain N := by
    intro i
    have he := congrArg (fun y : EuclideanSpace ℝ (Fin (N : ℕ)) => y i) (hraw X)
    change 1 + (T X).val i = gap X i.val at he
    rw [he]
    exact DefinitionSanity.gap_positive X i.val
  have hlaw : fullIntrinsicTiltedGapLaw p N θ ε twoSided =
      (tiltedParticleMeasure p N N (le_refl _) θ ε twoSided).map T := by
    change ((tiltedParticleMeasure p N N (le_refl _) θ ε twoSided).map
      (fun X => WithLp.toLp 2 (gapVector X))).comap (fun z : gapTangentSpace N => Y(z)) = _
    have he : (fun X : Riesz1.Configuration N => WithLp.toLp 2 (gapVector X)) =
        (fun z : gapTangentSpace N => Y(z)) ∘ T := funext (fun X => (hraw X).symm)
    rw [he, ← Measure.map_map (DefinitionSanity.full_chart_embedding N).measurable hT,
      (DefinitionSanity.full_chart_embedding N).comap_map]
  have hVY := contDiffOn_intrinsic_pullback N hV
  let w : gapTangentSpace N → ℝ≥0∞ := (intrinsicGapDomain N).indicator
    (fun z => ENNReal.ofReal (Real.exp (-V Y(z))))
  have hw : Measurable w := by
    have hh : ContinuousOn (fun z : gapTangentSpace N => ENNReal.ofReal (Real.exp (-V Y(z))))
        (intrinsicGapDomain N) := ENNReal.continuous_ofReal.comp_continuousOn hVY.neg.exp.continuousOn
    exact hh.measurable_piecewise continuousOn_const (AffineMetric.intrinsicGapDomain_isOpen N).measurableSet
  let Je : ℝ≥0∞ := (ENNReal.ofReal ((N.natPred + 1 : ℝ) ^ N.natPred))⁻¹ *
    (ENNReal.ofReal (Real.sqrt (N.natPred + 1)))⁻¹
  have hvol : (Riesz1.configurationVolume N).map T = Je • volume.restrict (intrinsicGapDomain N) := by
    have hall (M : ℕ+) : (Riesz1.configurationVolume M).map
        (fun X => centeredGapChart M (WithLp.toLp 2 (gapVector X))) =
        ((ENNReal.ofReal ((M.natPred + 1 : ℝ) ^ M.natPred))⁻¹ *
          (ENNReal.ofReal (Real.sqrt (M.natPred + 1)))⁻¹) •
            volume.restrict (intrinsicGapDomain M) := by
      obtain ⟨n, he⟩ : ∃ n : ℕ, M = n.succPNat :=
        ⟨M.natPred, (PNat.succPNat_natPred M).symm⟩
      subst M
      simpa only [Nat.natPred_succPNat, smul_smul] using configurationVolume_intrinsic n
    exact hall N
  have hwT (X : Riesz1.Configuration N) : w (T X) =
      ENNReal.ofReal (Real.exp (-p.val.1 * energy p X)) *
        ENNReal.ofReal (Real.exp (-p.val.1 * physicalGapPenalty N N (le_refl _) θ ε twoSided X)) := by
    rw [show w (T X) = ENNReal.ofReal (Real.exp (-V Y(T X))) from indicator_of_mem (hmem X) _]
    rw [hraw X, hval ⟨WithLp.toLp 2 (gapVector X), GapChart.gapVector_mem_gapAmbientDomain X⟩]
    rw [fullPhysicalPotentialValue, GapChart.physicalAmbientGapEnergy_gapVector p N hN X]
    simp only [physicalGapPenalty, gapVector]
    rw [mul_add, neg_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 3 <;> ring
  let q := (tiltNormalizer p N N (le_refl _) θ ε twoSided)⁻¹ * (partitionFunction p N)⁻¹ * Je
  have hdensity : fullIntrinsicTiltedGapLaw p N θ ε twoSided =
      q • (volume.restrict (intrinsicGapDomain N)).withDensity
        (fun z : gapTangentSpace N => ENNReal.ofReal (Real.exp (-V Y(z)))) := by
    have hf : Measurable (fun X : Riesz1.Configuration N => ENNReal.ofReal
        (Real.exp (-p.val.1 * energy p X))) := ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul (measurable_energy p N)))
    have hg : Measurable (fun X : Riesz1.Configuration N => ENNReal.ofReal
        (Real.exp (-p.val.1 * physicalGapPenalty N N (le_refl _) θ ε twoSided X))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (measurable_const.mul (DefinitionSanity.penalty_measurable N N (le_refl _) θ ε twoSided)))
    rw [hlaw, tiltedParticleMeasure, GapChart.gibbsMeasure_eq_withDensity,
      withDensity_smul_measure, ← withDensity_mul _ hf hg]
    have he : (fun X => ENNReal.ofReal (Real.exp (-p.val.1 * energy p X))) *
        (fun X => ENNReal.ofReal (Real.exp (-p.val.1 * physicalGapPenalty N N (le_refl _) θ ε twoSided X))) =
        fun X => w (T X) := funext (fun X => (hwT X).symm)
    rw [he, Measure.map_smul _ hT.aemeasurable, Measure.map_smul _ hT.aemeasurable,
      Riesz1.map_withDensity_comp _ hT hw, hvol, withDensity_smul_measure,
      smul_smul, smul_smul]
    congr 1
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem (AffineMetric.intrinsicGapDomain_isOpen N).measurableSet] with z hz
    exact indicator_of_mem hz _
  let Z := ∫⁻ z in intrinsicGapDomain N, ENNReal.ofReal (Real.exp (-V Y(z)))
  have hmass : q * Z = 1 := by
    have : IsProbabilityMeasure (fullIntrinsicTiltedGapLaw p N θ ε twoSided) :=
      DefinitionSanity.full_intrinsic_tilted_probability p N θ ε twoSided
    have hh : fullIntrinsicTiltedGapLaw p N θ ε twoSided univ = 1 := measure_univ
    rw [hdensity, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hh
    exact hh
  have hZ0 : Z ≠ 0 := right_ne_zero_of_mul_eq_one hmass
  have hq0 : q ≠ 0 := left_ne_zero_of_mul_eq_one hmass
  have hZtop : Z ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top hq0] at hmass
    exact ENNReal.top_ne_one hmass
  refine ⟨hVY, pos_iff_ne_zero.mpr hZ0, lt_top_iff_ne_top.mpr hZtop, ?_⟩
  rw [hdensity, ENNReal.eq_inv_of_mul_eq_one_left hmass]

/-- See Appendix A of the paper: intrinsic well-posedness for the full tilted physical law. In particular the Gibbs normalizer is positive
and finite. The collision estimate holds for every positive coefficient. -/
theorem fullPhysicalPotential_wellposed (p : Parameters) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ) (twoSided : Bool) :
    ∃ V : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ V (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        V y.val = fullPhysicalPotentialValue p N hN θ ε twoSided y) ∧
      IsEuclideanGibbsPotential volume (fullIntrinsicTiltedGapLaw p N θ ε twoSided)
        (intrinsicGapDomain N) (fun z : gapTangentSpace N => V Y(z)) ∧
      ∃ κ : ℝ, 0 < κ ∧
      (∀ z ∈ intrinsicGapDomain N, ∀ u : gapTangentSpace N,
        κ * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (fun z : gapTangentSpace N => V Y(z))) z u u) ∧
      ∀ A K : ℝ, 0 < A → 0 < K → ∃ D : ℝ, 0 ≤ D ∧ ∀ z ∈ intrinsicGapDomain N,
        K * (Metric.infDist z (frontier (intrinsicGapDomain N)))⁻¹ ^ 2 - D ≤
          A * ‖gradient (fun z : gapTangentSpace N => V Y(z)) z‖ ^ 2 -
            Laplacian.laplacian (fun z : gapTangentSpace N => V Y(z)) z := by
  obtain ⟨V, hV, hval, κ, hκ, hcurv, hcoll⟩ :=
    fullPhysicalPotential_collision_criterion N p hN θ ε twoSided
  exact ⟨V, hV, hval, internal_full_gap_gibbs N p hN θ ε twoSided V hV hval,
    κ, hκ, hcurv, hcoll⟩

end Riesz2.PhysicalCollision

end
