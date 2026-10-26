/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.InterpolationCoefficientsPart2
public import Riesz2.HelfferSjostrand.PhysicalCollisionPart2
public import Riesz2.HelfferSjostrand.IntrinsicIntegrationByParts

/-!
# Two-sided forcing in fixed-exterior interpolation

Curvature and exceptional-weight estimates for the penalty of Subsection 6.1. The
formulas hold on positive coordinates, including points outside the fine rigidity event.
-/

public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ContDiff Topology

attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.InterpolationCoercivity

/-- See Subsection 6.1 of the paper: smoothness of one two-sided forcing summand. -/
theorem penalty_smooth (θ : PhysicalCutoff) {b x : ℝ} (hb : 0 < b) (hx : 0 < x) :
    ContDiffAt ℝ ∞ (fun t => θ.val (b * t) + θ.val (b * t⁻¹)) x := by
  have hu := (PhysicalCollision.cutoff_contDiffAt θ (mul_pos hb hx)).comp x
    (contDiffAt_const.mul contDiffAt_id)
  have hi := (PhysicalCollision.cutoff_contDiffAt θ (mul_pos hb (inv_pos.mpr hx))).comp x
    (contDiffAt_const.mul (contDiffAt_id.inv hx.ne'))
  exact hu.add hi

/-- See Subsection 6.1 of the paper: nonnegative scalar curvature and its global
fourth-order upper bound, with a constant depending only on the cutoff. -/
theorem penalty_curvature (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ b x : ℝ, 0 < b → 0 < x →
      0 ≤ deriv (deriv (fun t => θ.val (b * t) + θ.val (b * t⁻¹))) x ∧
      deriv (deriv (fun t => θ.val (b * t) + θ.val (b * t⁻¹))) x ≤
        C * b ^ 2 * (1 + x⁻¹ ^ 4) := by
  obtain ⟨C₀, hC₀, hu⟩ := PhysicalCollision.upper_penalty_curvature θ
  obtain ⟨C₁, hC₁, hi⟩ := PhysicalCollision.inverse_penalty_curvature θ
  refine ⟨C₀ + C₁, by positivity, fun b x hb hx => ?_⟩
  have hu' := (PhysicalCollision.cutoff_contDiffAt θ (mul_pos hb hx)).comp x
    (contDiffAt_const.mul contDiffAt_id)
  have hi' := (PhysicalCollision.cutoff_contDiffAt θ (div_pos hb hx)).comp x
    (contDiffAt_const.div contDiffAt_id hx.ne')
  have he := PhysicalCollision.internal_hessian_add
    (hu'.of_le (by simp)) (hi'.of_le (by simp)) (1 : ℝ) 1
  simp only [PhysicalCollision.internal_scalar_hessian, mul_one] at he
  simp only [Function.comp_def, div_eq_mul_inv] at he hi
  rw [he]
  obtain ⟨hu0, hu1⟩ := hu b x hb hx
  obtain ⟨hi0, hi1⟩ := hi b x hb hx
  refine ⟨add_nonneg hu0 hi0, ?_⟩
  nlinarith [mul_nonneg hC₀.le (mul_nonneg (sq_nonneg b) (pow_nonneg (inv_nonneg.mpr hx.le) 4)),
    mul_nonneg hC₁.le (sq_nonneg b)]

/-- See Subsection 6.1 of the paper: the upper part supplies curvature `b²` once
`b*x ≥ 1`. The inverse part preserves this lower bound. -/
theorem penalty_curvature_lower (θ : PhysicalCutoff) {b x : ℝ}
    (hb : 0 < b) (hx : 0 < x) (hbx : 1 ≤ b * x) :
    b ^ 2 ≤ deriv (deriv (fun t => θ.val (b * t) + θ.val (b * t⁻¹))) x := by
  have hu := (PhysicalCollision.cutoff_contDiffAt θ (mul_pos hb hx)).comp x
    (contDiffAt_const.mul contDiffAt_id)
  have hi := (PhysicalCollision.cutoff_contDiffAt θ (div_pos hb hx)).comp x
    (contDiffAt_const.div contDiffAt_id hx.ne')
  have hadd := PhysicalCollision.internal_hessian_add
    (hu.of_le (by simp)) (hi.of_le (by simp)) (1 : ℝ) 1
  simp only [PhysicalCollision.internal_scalar_hessian, mul_one, Function.comp_def, div_eq_mul_inv] at hadd
  rw [hadd]
  obtain ⟨C, hC, hinv⟩ := PhysicalCollision.inverse_penalty_curvature θ
  have hinv0 := (hinv b x hb hx).1
  simp only [div_eq_mul_inv] at hinv0
  let B : ℝ →L[ℝ] ℝ := b • ContinuousLinearMap.id ℝ ℝ
  have hh := PhysicalCollision.internal_scalar_affine_hessian θ.val B 0
    (show ContDiffAt ℝ 2 θ.val (B x + 0) from by
      simpa [B] using (PhysicalCollision.cutoff_contDiffAt θ (mul_pos hb hx)).of_le (by simp)) 1
  simp only [B, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, add_zero,
    mul_one, PhysicalCollision.internal_scalar_hessian] at hh
  rw [hh]
  obtain ⟨D, hD, hcurv, hlarge⟩ := θ.property.2.2.2.2
  have hm := mul_le_mul_of_nonneg_right (hlarge (b * x) hbx) (sq_nonneg b)
  nlinarith

/-- See Subsection 6.1 of the paper: finite forcing is smooth on all positive
ambient coordinates. This is the displayed two-sided penalty, without
any extension of its values on the simplex. -/
theorem forcing_smooth (θ : PhysicalCutoff) {b : ℝ} (hb : 0 < b) {n : ℕ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : ∀ i, 0 < x i) :
    ContDiffAt ℝ ∞ (fun u : EuclideanSpace ℝ (Fin n) =>
      ∑ i, (θ.val (b * u i) + θ.val (b * (u i)⁻¹))) x := by
  apply ContDiffAt.sum
  intro i _
  exact (penalty_smooth θ hb (hx i)).comp x
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt

/-- See Subsection 6.1 of the paper: the two-sided penalty has its exact diagonal
ambient Hessian. In particular no mixed forcing entries are discarded. -/
theorem forcing_hessian (θ : PhysicalCutoff) {b : ℝ} (hb : 0 < b) {n : ℕ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : ∀ i, 0 < x i) (i j : Fin n) :
    hessianMatrix (fun u : EuclideanSpace ℝ (Fin n) =>
      ∑ k, (θ.val (b * u k) + θ.val (b * (u k)⁻¹))) x i j =
      if i = j then deriv (deriv (fun t => θ.val (b * t) + θ.val (b * t⁻¹))) (x i)
      else 0 := by
  classical
  let f : ℝ → ℝ := fun t => θ.val (b * t) + θ.val (b * t⁻¹)
  have hf (k : Fin n) : ContDiffAt ℝ 2
      (fun u : EuclideanSpace ℝ (Fin n) => f (u k)) x :=
    ((penalty_smooth θ hb (hx k)).comp x
      (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.contDiffAt).of_le (by simp)
  rw [Intrinsic.hessianMatrix_eq_second (forcing_smooth θ hb hx)]
  have he := congrArg (fun T : ContinuousMultilinearMap ℝ
      (fun _ : Fin 2 => EuclideanSpace ℝ (Fin n)) ℝ =>
      T ![EuclideanSpace.single i 1, EuclideanSpace.single j 1])
    (iteratedFDeriv_fun_sum_apply (fun k (_ : k ∈ Finset.univ) => hf k))
  simp only [sum_apply, iteratedFDeriv_two_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] at he
  change fderiv ℝ (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) => ∑ k, f (u k))) x _ _ = _
  rw [he]
  have hterm (k : Fin n) : fderiv ℝ (fderiv ℝ
      (fun u : EuclideanSpace ℝ (Fin n) => f (u k))) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      deriv (deriv f) (x k) * (if k = i then 1 else 0) * (if k = j then 1 else 0) := by
    have hh := AffineMetricTransport.hessian_comp_affine (EuclideanSpace.proj (𝕜 := ℝ) k) 0
      (show ContDiffAt ℝ 2 f ((EuclideanSpace.proj (𝕜 := ℝ) k) x + 0) from by
        simpa only [EuclideanSpace.coe_proj, add_zero, f] using
          (penalty_smooth θ hb (hx k)).of_le (by simp))
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    simp only [add_zero, PhysicalCollision.internal_scalar_hessian] at hh
    change _ = deriv (deriv f) (x k) *
      (EuclideanSpace.single i 1 k) * (EuclideanSpace.single j 1 k) at hh
    simpa only [PiLp.single_apply, EuclideanSpace.coe_proj] using hh
  simp_rw [hterm]
  by_cases hij : i = j
  · subst j
    simp [f]
  · rw [ite_eq_right hij]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hki : k = i
    · subst k; simp [hij]
    · simp [hki]

/-- See Subsection 6.1 of the paper: the exceptional weight dominates the square
of the inverse fourth-order penalty curvature, in both exponent ranges. -/
theorem inverse_fourth_sq_le_weight (s : ℝ) (hs : 0 < s) (a : ℕ)
    (x : Fin (a + 1) → ℝ) (hx : ∀ i, 0 < x i) (i : Fin (a + 1)) :
    (1 + (x i)⁻¹ ^ 4) ^ 2 ≤
      4 * InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s x := by
  have hW := InterpolantLocalLaws.one_le_exceptionalWeight (n := a.succPNat) s x
    (fun i => (hx i).le)
  have hterm : x i ^ (-4 * s - 12) ≤ ∑ k, x k ^ (-4 * s - 12) :=
    Finset.single_le_sum (fun k _ => Real.rpow_nonneg (hx k).le _) (Finset.mem_univ i)
  have hsq : ((x i)⁻¹ ^ 4) ^ 2 ≤
      InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s x := by
    rw [← pow_mul, show 4 * 2 = 8 by rfl, ← Real.rpow_natCast, ← Real.rpow_neg_eq_inv_rpow]
    change x i ^ (-(8 : ℝ)) ≤ 1 + ∑ k, x k ^ (-4 * s - 12)
    by_cases hi : x i ≤ 1
    · have hh := Real.rpow_le_rpow_of_exponent_ge (hx i) hi
        (by linarith : -4 * s - 12 ≤ -(8 : ℝ))
      linarith
    · have hh := Real.rpow_le_one_of_one_le_of_nonpos (le_of_not_ge hi)
        (by norm_num : -(8 : ℝ) ≤ 0)
      have hsum := Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) =>
        Real.rpow_nonneg (hx k).le (-4 * s - 12))
      linarith
  nlinarith [sq_nonneg ((x i)⁻¹ ^ 4 - 1)]

/-- See Subsection 6.1 of the paper, whole-simplex forcing clause: the square of
each literal two-sided penalty Hessian entry is bounded by the actual
exceptional weight. The bound is uniform in the tolerance and size. -/
theorem forcing_sq_le_weight (θ : PhysicalCutoff) (s : ℝ) (hs : 0 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ) (ε : ℝ), 0 ≤ ε →
      ∀ x : EuclideanSpace ℝ (Fin (a + 1)), (∀ i, 0 < x i) → ∀ i j,
      |hessianMatrix (fun u : EuclideanSpace ℝ (Fin (a + 1)) =>
        ∑ k, (θ.val ((a + 1 : ℝ) ^ (-ε) * u k) +
          θ.val ((a + 1 : ℝ) ^ (-ε) * (u k)⁻¹))) x i j| ^ 2 ≤
        C * InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s (WithLp.ofLp x) := by
  obtain ⟨B, hB, hb⟩ := penalty_curvature θ
  refine ⟨4 * B ^ 2, by positivity, fun a ε hε x hx i j => ?_⟩
  have hn : (1 : ℝ) ≤ a + 1 := by have := Nat.cast_nonneg a (α := ℝ); linarith
  have hn0 : (0 : ℝ) < a + 1 := by positivity
  have hb0 := Real.rpow_pos_of_pos hn0 (-ε)
  have hb1 : (a + 1 : ℝ) ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn (by linarith)
  rw [forcing_hessian θ hb0 hx]
  split_ifs with hij
  · have hc := hb _ (x i) hb0 (hx i)
    have hbsq : ((a + 1 : ℝ) ^ (-ε)) ^ 2 ≤ 1 := by nlinarith
    have hcurv := hc.2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hbsq hB.le)
      (by positivity : 0 ≤ 1 + (x i)⁻¹ ^ 4))
    rw [abs_of_nonneg hc.1]
    have hsquare := mul_self_le_mul_self hc.1 hcurv
    have hw := inverse_fourth_sq_le_weight s hs a (WithLp.ofLp x) hx i
    have hm := mul_le_mul_of_nonneg_left hw (sq_nonneg B)
    nlinarith only [hsquare, hm]
  · simp only [abs_zero, zero_pow (by norm_num : 2 ≠ 0)]
    exact mul_nonneg (by positivity)
      (zero_le_one.trans (InterpolantLocalLaws.one_le_exceptionalWeight s _ (fun i => (hx i).le)))

/-- See Subsection 6.1 of the paper: exact quadratic form of the two-sided forcing. -/
theorem forcing_quadratic (θ : PhysicalCutoff) {b : ℝ} (hb : 0 < b) {n : ℕ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : ∀ i, 0 < x i)
    (v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fderiv ℝ (fun u : EuclideanSpace ℝ (Fin n) =>
      ∑ k, (θ.val (b * u k) + θ.val (b * (u k)⁻¹)))) x v v =
      ∑ k, deriv (deriv (fun t => θ.val (b * t) + θ.val (b * t⁻¹))) (x k) * (v k) ^ 2 := by
  classical
  rw [← PhysicalEnergy.hessianMatrix_quadratic ((forcing_smooth θ hb hx).of_le (by simp))]
  simp_rw [forcing_hessian θ hb hx]
  simp only [mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Internal scalar absorption in Subsection 6.1: the nearest-gap
curvature below the upper cutoff and the forcing above it give a common
positive lower bound at every positive coordinate. -/
theorem nearest_plus_forcing_lower (θ : PhysicalCutoff) {s n ε x : ℝ}
    (hs : 0 < s) (hn : 1 ≤ n) (hε : 0 ≤ ε) (hx : 0 < x) :
    min 1 (s * (s + 1)) * n ^ (-(s + 2) * ε) ≤
      s * (s + 1) * x ^ (-s - 2) +
        deriv (deriv (fun t => θ.val (n ^ (-ε) * t) + θ.val (n ^ (-ε) * t⁻¹))) x := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hb := Real.rpow_pos_of_pos hn0 (-ε)
  obtain ⟨C, hC, hc⟩ := penalty_curvature θ
  have hnonneg := (hc _ x hb hx).1
  have hbase : 0 ≤ s * (s + 1) * x ^ (-s - 2) := by positivity
  by_cases hcut : x ≤ n ^ ε
  · have hp := Real.rpow_le_rpow_of_nonpos hx hcut (by linarith : -s - 2 ≤ 0)
    rw [← Real.rpow_mul hn0.le] at hp
    have he : ε * (-s - 2) = -(s + 2) * ε := by ring
    rw [he] at hp
    have hh := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ s * (s + 1))
    have hm := mul_le_mul_of_nonneg_right (min_le_right 1 (s * (s + 1)))
      (Real.rpow_nonneg hn0.le (-(s + 2) * ε))
    linarith
  · have hbx : 1 ≤ n ^ (-ε) * x := by
      have he : n ^ (-ε) * n ^ ε = 1 := by rw [← Real.rpow_add hn0]; simp
      rw [← he]
      exact mul_le_mul_of_nonneg_left (le_of_not_ge hcut) hb.le
    have hl := penalty_curvature_lower θ hb hx hbx
    have hp : n ^ (-(s + 2) * ε) ≤ (n ^ (-ε)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
      exact Real.rpow_le_rpow_of_exponent_le hn (by
        norm_num only [Nat.cast_ofNat]
        nlinarith [mul_nonneg hs.le hε])
    have hm := mul_le_mul_of_nonneg_right (min_le_left 1 (s * (s + 1)))
      (Real.rpow_nonneg hn0.le (-(s + 2) * ε))
    linarith

/-- See Subsection 6.1 of the paper, all-size nearest-gap bridge: a smooth ambient
realization of the physical energy, restricted to the actual
exterior-first assembly, has the unrestricted active nearest-gap barrier.
The realization and its analytic estimates are conclusions. -/
theorem assembled_energy_realization (p : Parameters) (e a : ℕ)
    (hN : 2 ≤ e + a + 1) (y : AffineSimplex.chartDomain e ((e + a : ℕ) + 1)) :
    let Y := RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val
    let D := Y ⁻¹' gapAmbientDomain (e + a).succPNat
    ∃ K : EuclideanSpace ℝ (Fin (a + 1)) → ℝ,
      ContDiffOn ℝ ∞ K D ∧
      (∀ x (hx : x ∈ D), K x = physicalAmbientGapEnergy p (e + a).succPNat ⟨Y x, hx⟩) ∧
      ∀ x ∈ AffineSimplex.massSimplex a (((e + a : ℕ) + 1 : ℝ) - ∑ k, y.val k),
      ∀ v : EuclideanSpace ℝ (Fin (a + 1)),
        p.val.2 * (p.val.2 + 1) * (∑ i, (x i) ^ (-p.val.2 - 2) * (v i) ^ 2) ≤
          fderiv ℝ (fderiv ℝ K) x v v := by
  classical
  intro Y D
  let N := (e + a).succPNat
  let σ := InterpolatingDensities.exteriorPermutation e a
  let E := EuclideanSpace ℝ (Fin e)
  let F := EuclideanSpace ℝ (Fin (a + 1))
  let A : F →L[ℝ] EuclideanSpace ℝ (Fin (e + a + 1)) :=
    LinearMap.toContinuousLinearMap
      ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ).toLinearEquiv.toLinearMap.comp
        ((RetainedSimplex.join e (a + 1)).toLinearMap.comp (LinearMap.inr ℝ E F)))
  let z := RetainedSimplex.assemble e a σ y.val 0
  have hY (x : F) : A x + z = Y x := by
    change RetainedSimplex.assemble e a σ 0 x + RetainedSimplex.assemble e a σ y.val 0 = _
    simp only [RetainedSimplex.assemble, ← map_add]
    congr 1
    rw [← (RetainedSimplex.join e (a + 1)).map_add]
    congr 1
    exact Prod.ext (zero_add _) (add_zero _)
  obtain ⟨W, hW, hw, _, _, hl, _, _⟩ :=
    (PhysicalEnergy.restriction_and_derivatives p N hN).2.2
  let K := fun x : F => W (A x + z)
  refine ⟨K, ?_, ?_, ?_⟩
  · exact hW.comp (A.contDiff.add contDiff_const).contDiffOn (fun x hx => by rwa [hY])
  · intro x hx
    exact (congrArg W (hY x)).trans (hw ⟨Y x, hx⟩)
  · intro x hx v
    have hxs := InterpolantLocalLaws.assembled_physical_simplex e a y.val x y.property.1 hx.1 (by
      rw [hx.2]; push_cast; ring)
    have hxD : Y x ∈ gapAmbientDomain N := PhysicalEnergy.simplex_subset_ambient N _ hxs
    have hs : ContDiffAt ℝ 2 W (A x + z) := by
      rw [hY]
      exact (hW.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hxD)).of_le (by simp)
    change _ ≤ fderiv ℝ (fderiv ℝ (fun x : F => W (A x + z))) x v v
    rw [AffineMetricTransport.hessian_comp_affine A z hs, hY]
    have hh := hl (WithLp.ofLp (Y x)) hxs (A v)
    have hsum : (∑ i : Fin (e + a + 1), (Y x i) ^ (-p.val.2 - 2) * (A v i) ^ 2) =
        ∑ i, (x i) ^ (-p.val.2 - 2) * (v i) ^ 2 := by
      change (∑ i, (RetainedSimplex.join e (a + 1) (y.val, x) (σ.symm i)) ^
        (-p.val.2 - 2) * (RetainedSimplex.join e (a + 1) (0, v) (σ.symm i)) ^ 2) = _
      calc
        _ = ∑ i, (RetainedSimplex.join e (a + 1) (y.val, x) i) ^ (-p.val.2 - 2) *
            (RetainedSimplex.join e (a + 1) (0, v) i) ^ 2 :=
          Equiv.sum_comp σ.symm (fun i =>
            (RetainedSimplex.join e (a + 1) (y.val, x) i) ^ (-p.val.2 - 2) *
              (RetainedSimplex.join e (a + 1) (0, v) i) ^ 2)
        _ = _ := ?_
      rw [Fin.sum_univ_add]
      simp only [RetainedSimplex.join_left, RetainedSimplex.join_right,
        PiLp.zero_apply, zero_pow (by norm_num : 2 ≠ 0), mul_zero, Finset.sum_const_zero, zero_add]
    dsimp only [N, Nat.succPNat_coe] at hh
    rw [hsum] at hh
    exact hh

/-- See Subsection 6.1 of the paper, all-size physical coercivity in both exponent
ranges. The endpoint functions realize the short-interval energy
on open ambient neighborhoods. Their interpolation includes the exact
two-sided forcing. No rigidity or exterior typicality is needed. The
lower bound acts on every ambient active vector, before tangent restriction. -/
theorem physical_interpolant_coercivity (p : Parameters) (θ : PhysicalCutoff)
    (ε : ℝ) (hε : 0 ≤ ε) (e f a : ℕ) (ha : 1 ≤ a)
    (y : AffineSimplex.chartDomain e ((e + a : ℕ) + 1))
    (z : AffineSimplex.chartDomain f ((f + a : ℕ) + 1)) (L : ℝ)
    (hyL : ((e + a : ℕ) + 1 : ℝ) - ∑ k, y.val k = L)
    (hzL : ((f + a : ℕ) + 1 : ℝ) - ∑ k, z.val k = L) :
    let Y := RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val
    let Z := RetainedSimplex.assemble f a (InterpolatingDensities.exteriorPermutation f a) z.val
    let Dy := Y ⁻¹' gapAmbientDomain (e + a).succPNat
    let Dz := Z ⁻¹' gapAmbientDomain (f + a).succPNat
    let c := min 1 (p.val.2 * (p.val.2 + 1))
    0 < c ∧ ∃ Ky Kz : EuclideanSpace ℝ (Fin (a + 1)) → ℝ,
      ContDiffOn ℝ ∞ Ky Dy ∧ ContDiffOn ℝ ∞ Kz Dz ∧
      (∀ x (hx : x ∈ Dy), Ky x = physicalAmbientGapEnergy p (e + a).succPNat ⟨Y x, hx⟩) ∧
      (∀ x (hx : x ∈ Dz), Kz x = physicalAmbientGapEnergy p (f + a).succPNat ⟨Z x, hx⟩) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ AffineSimplex.massSimplex a L,
      let H := fun u : EuclideanSpace ℝ (Fin (a + 1)) =>
        (∑ k, (θ.val ((a + 1 : ℝ) ^ (-ε) * u k) +
          θ.val ((a + 1 : ℝ) ^ (-ε) * (u k)⁻¹))) + (1 - t) * Ky u + t * Kz u
      ContDiffAt ℝ ∞ H x ∧ ∀ v : EuclideanSpace ℝ (Fin (a + 1)),
        c * (a + 1 : ℝ) ^ (-(p.val.2 + 2) * ε) * (∑ i, (v i) ^ 2) ≤
          ∑ i, ∑ j, v i * hessianMatrix H x i j * v j := by
  intro Y Z Dy Dz c
  have hc : 0 < c := lt_min zero_lt_one (by have := p.property.2.1; positivity)
  obtain ⟨Ky, hKy, hky, hly⟩ := assembled_energy_realization p e a (by omega) y
  obtain ⟨Kz, hKz, hkz, hlz⟩ := assembled_energy_realization p f a (by omega) z
  refine ⟨hc, Ky, Kz, hKy, hKz, hky, hkz, ?_⟩
  intro t ht x hx H
  have hxy : x ∈ AffineSimplex.massSimplex a (((e + a : ℕ) + 1 : ℝ) - ∑ k, y.val k) :=
    hyL ▸ hx
  have hxz : x ∈ AffineSimplex.massSimplex a (((f + a : ℕ) + 1 : ℝ) - ∑ k, z.val k) :=
    hzL ▸ hx
  have hxDy : x ∈ Dy := PhysicalEnergy.simplex_subset_ambient _ _
    (InterpolantLocalLaws.assembled_physical_simplex e a y.val x y.property.1 hx.1 (by
      rw [hx.2, ← hyL]; push_cast; ring))
  have hxDz : x ∈ Dz := PhysicalEnergy.simplex_subset_ambient _ _
    (InterpolantLocalLaws.assembled_physical_simplex f a z.val x z.property.1 hx.1 (by
      rw [hx.2, ← hzL]; push_cast; ring))
  have hDy : IsOpen Dy := (PhysicalEnergy.isOpen_gapAmbientDomain _).preimage
    (InterpolantLocalLaws.contDiff_exterior_assembly e a y.val).continuous
  have hDz : IsOpen Dz := (PhysicalEnergy.isOpen_gapAmbientDomain _).preimage
    (InterpolantLocalLaws.contDiff_exterior_assembly f a z.val).continuous
  have hsy := hKy.contDiffAt (hDy.mem_nhds hxDy)
  have hsz := hKz.contDiffAt (hDz.mem_nhds hxDz)
  have hb := Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < a + 1) (-ε)
  have hsp := forcing_smooth θ hb hx.1
  have hH : ContDiffAt ℝ ∞ H x :=
    (hsp.add (contDiffAt_const.mul hsy)).add (contDiffAt_const.mul hsz)
  refine ⟨hH, fun v => ?_⟩
  rw [PhysicalEnergy.hessianMatrix_quadratic (hH.of_le (by simp))]
  change _ ≤ fderiv ℝ (fderiv ℝ (fun u =>
    ((∑ k, (θ.val ((a + 1 : ℝ) ^ (-ε) * u k) + θ.val ((a + 1 : ℝ) ^ (-ε) * (u k)⁻¹))) +
      (1 - t) * Ky u) + t * Kz u)) x v v
  rw [PhysicalCollision.internal_hessian_add
      ((hsp.add (contDiffAt_const.mul hsy)).of_le (by simp))
      ((contDiffAt_const.mul hsz).of_le (by simp)),
    PhysicalCollision.internal_hessian_add (hsp.of_le (by simp))
      ((contDiffAt_const.mul hsy).of_le (by simp)),
    PhysicalCollision.internal_hessian_const_mul (hsy.of_le (by simp)),
    PhysicalCollision.internal_hessian_const_mul (hsz.of_le (by simp)),
    forcing_quadratic θ hb hx.1]
  have hy := mul_le_mul_of_nonneg_left (hly x hxy v) (sub_nonneg.mpr ht.2)
  have hz := mul_le_mul_of_nonneg_left (hlz x hxz v) ht.1
  have hn : (1 : ℝ) ≤ a + 1 := by have := Nat.cast_nonneg a (α := ℝ); linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_right
      (nearest_plus_forcing_lower θ p.property.2.1 hn hε (hx.1 i)) (sq_nonneg (v i)))
  simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc] at hsum
  dsimp only [c]
  nlinarith only [hsum, hy, hz]

/-- See Subsection 6.1 of the paper: on the fine lower cutoff, the literal forcing
has entry bound `C n^(4η)`. Off the diagonal it is exactly zero. -/
theorem forcing_entry_bound (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ) (ε η : ℝ), 0 ≤ ε → 0 ≤ η →
      ∀ x : EuclideanSpace ℝ (Fin (a + 1)),
      (∀ i, (a + 1 : ℝ) ^ (-η) ≤ x i) → ∀ i j,
      |hessianMatrix (fun u : EuclideanSpace ℝ (Fin (a + 1)) =>
        ∑ k, (θ.val ((a + 1 : ℝ) ^ (-ε) * u k) +
          θ.val ((a + 1 : ℝ) ^ (-ε) * (u k)⁻¹))) x i j| ≤
        if i = j then C * (a + 1 : ℝ) ^ (4 * η) else 0 := by
  obtain ⟨B, hB, hb⟩ := penalty_curvature θ
  refine ⟨2 * B, by positivity, fun a ε η hε hη x hx i j => ?_⟩
  have hn : (1 : ℝ) ≤ a + 1 := by have := Nat.cast_nonneg a (α := ℝ); linarith
  have hn0 : (0 : ℝ) < a + 1 := by positivity
  have hb0 := Real.rpow_pos_of_pos hn0 (-ε)
  have hb1 : (a + 1 : ℝ) ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn (by linarith)
  have hx0 : ∀ i, 0 < x i := fun i => (Real.rpow_pos_of_pos hn0 (-η)).trans_le (hx i)
  rw [forcing_hessian θ hb0 hx0]
  split_ifs with hij
  · obtain ⟨hc0, hc1⟩ := hb _ _ hb0 (hx0 i)
    rw [abs_of_nonneg hc0]
    have hpow : (x i)⁻¹ ^ 4 ≤ (a + 1 : ℝ) ^ (4 * η) := by
      have hh := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hn0 (-η)) (hx i)
        (by norm_num : -(4 : ℝ) ≤ 0)
      rw [← Real.rpow_mul hn0.le, show -η * -(4 : ℝ) = 4 * η by ring] at hh
      simpa only [Real.rpow_neg_eq_inv_rpow, Real.rpow_ofNat] using hh
    have hone : 1 ≤ (a + 1 : ℝ) ^ (4 * η) := Real.one_le_rpow hn (by positivity)
    have hbsq : ((a + 1 : ℝ) ^ (-ε)) ^ 2 ≤ 1 := by nlinarith
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbsq hB.le)
      (show 0 ≤ 1 + (x i)⁻¹ ^ 4 by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hpow hB.le,
      mul_le_mul_of_nonneg_left hone hB.le]
  · simp

/-- Internal exact Hessian assembly for Subsection 6.1 and
Subsection 6.1, on the open ambient realizations used above. -/
theorem interpolant_hessian_internal (θ : PhysicalCutoff) {n : ℕ} {b t : ℝ}
    (hb : 0 < b) {Ky Kz : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : ∀ i, 0 < x i)
    (hy : ContDiffAt ℝ ∞ Ky x) (hz : ContDiffAt ℝ ∞ Kz x) (i j : Fin n) :
    hessianMatrix (fun u : EuclideanSpace ℝ (Fin n) =>
      (∑ k, (θ.val (b * u k) + θ.val (b * (u k)⁻¹))) + (1 - t) * Ky u + t * Kz u) x i j =
      hessianMatrix (fun u : EuclideanSpace ℝ (Fin n) =>
        ∑ k, (θ.val (b * u k) + θ.val (b * (u k)⁻¹))) x i j +
        ((1 - t) * hessianMatrix Ky x i j + t * hessianMatrix Kz x i j) := by
  have hp := forcing_smooth θ hb hx
  rw [Intrinsic.hessianMatrix_eq_second
      ((hp.add (contDiffAt_const.mul hy)).add (contDiffAt_const.mul hz)),
    PhysicalCollision.internal_hessian_add
      ((hp.add (contDiffAt_const.mul hy)).of_le (by simp))
      ((contDiffAt_const.mul hz).of_le (by simp)),
    PhysicalCollision.internal_hessian_add (hp.of_le (by simp))
      ((contDiffAt_const.mul hy).of_le (by simp)),
    PhysicalCollision.internal_hessian_const_mul (hy.of_le (by simp)),
    PhysicalCollision.internal_hessian_const_mul (hz.of_le (by simp)),
    ← Intrinsic.hessianMatrix_eq_second hp, ← Intrinsic.hessianMatrix_eq_second hy,
    ← Intrinsic.hessianMatrix_eq_second hz]
  ring

/-- The short-range entry clause of Subsection 6.1 assumes the crossing
entry envelope for `P(t)`. The conclusion includes two-sided forcing and
the identity off the fine event. -/
theorem short_range_entry_internal (θ : PhysicalCutoff) :
    ∃ F : ℝ, 0 < F ∧ ∀ (a : ℕ) (ε η ρ s B t : ℝ),
      0 ≤ ε → 0 ≤ η → 0 ≤ ρ → 1 < s → 0 ≤ B →
      ∀ (A : Set (EuclideanSpace ℝ (Fin (a + 1))))
      (Ky Kz : EuclideanSpace ℝ (Fin (a + 1)) → ℝ),
      (∀ x ∈ A, ∀ i, (a + 1 : ℝ) ^ (-η) ≤ x i) →
      (∀ x ∈ A, ContDiffAt ℝ ∞ Ky x ∧ ContDiffAt ℝ ∞ Kz x) →
      (∀ x ∈ A, ∀ i j,
        |(1 - t) * hessianMatrix Ky x i j + t * hessianMatrix Kz x i j| ≤
          B * (a + 1 : ℝ) ^ ρ * (1 + |(i.val : ℝ) - j.val|) ^ (-s)) →
      let H := fun u : EuclideanSpace ℝ (Fin (a + 1)) =>
        (∑ k, (θ.val ((a + 1 : ℝ) ^ (-ε) * u k) +
          θ.val ((a + 1 : ℝ) ^ (-ε) * (u k)⁻¹))) + (1 - t) * Ky u + t * Kz u
      ∀ (x : EuclideanSpace ℝ (Fin (a + 1))) (i j : Fin (a + 1)),
        |(if x ∈ A then hessianMatrix H x else (1 : Matrix (Fin (a + 1)) (Fin (a + 1)) ℝ)) i j| ≤
          (1 + F + B) * (a + 1 : ℝ) ^ (max (4 * η) ρ) *
            (1 + |(i.val : ℝ) - j.val|) ^ (-s) := by
  classical
  obtain ⟨F, hF, hf⟩ := forcing_entry_bound θ
  refine ⟨F, hF, ?_⟩
  intro a ε η ρ s B t hε hη hρ _hs hB A Ky Kz hcut hsm hcross H x i j
  have hn : (1 : ℝ) ≤ a + 1 := by have := Nat.cast_nonneg a (α := ℝ); linarith
  have hn0 : (0 : ℝ) < a + 1 := by positivity
  have hd : 0 < (1 + |(i.val : ℝ) - j.val|) ^ (-s) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hpow : 1 ≤ (a + 1 : ℝ) ^ (max (4 * η) ρ) :=
    Real.one_le_rpow hn (hρ.trans (le_max_right _ _))
  by_cases hx : x ∈ A
  · rw [ite_eq_left hx]
    rw [interpolant_hessian_internal θ (Real.rpow_pos_of_pos hn0 (-ε))
      (fun i => (Real.rpow_pos_of_pos hn0 (-η)).trans_le (hcut x hx i))
      (hsm x hx).1 (hsm x hx).2]
    have hforce := hf a ε η hε hη x (hcut x hx) i j
    have hforce' : (if i = j then F * (a + 1 : ℝ) ^ (4 * η) else 0) ≤
        F * (a + 1 : ℝ) ^ (4 * η) * (1 + |(i.val : ℝ) - j.val|) ^ (-s) := by
      by_cases hij : i = j
      · subst j; simp
      · rw [ite_eq_right hij]; positivity
    have hsum := (abs_add_le _ _).trans (add_le_add (hforce.trans hforce') (hcross x hx i j))
    have hp₁ := Real.rpow_le_rpow_of_exponent_le hn (le_max_left (4 * η) ρ)
    have hp₂ := Real.rpow_le_rpow_of_exponent_le hn (le_max_right (4 * η) ρ)
    have hh₁ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp₁ hF.le) hd.le
    have hh₂ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp₂ hB) hd.le
    have hpos : 0 ≤ (a + 1 : ℝ) ^ (max (4 * η) ρ) *
        (1 + |(i.val : ℝ) - j.val|) ^ (-s) := by positivity
    nlinarith only [hsum, hh₁, hh₂, hpos]
  · rw [ite_eq_right hx]
    by_cases hij : i = j
    · subst j
      simp only [Matrix.one_apply_eq, abs_one, sub_self, abs_zero, add_zero, Real.one_rpow, mul_one]
      have hFB : 1 ≤ 1 + F + B := by linarith
      exact one_le_mul_of_one_le_of_one_le hFB hpow
    · rw [Matrix.one_apply_ne hij, abs_zero]
      positivity

/-- Internal coercivity clause of Subsection 6.1: replacing an
already coercive physical Hessian by the identity off the fine event
retains the same power loss, with prefactor `min c 1`. -/
theorem identity_cutoff_coercivity_internal {n : ℕ} (S A : Set (EuclideanSpace ℝ (Fin n)))
    (H : EuclideanSpace ℝ (Fin n) → ℝ) {c w : ℝ} (hc : 0 < c)
    (hw : 0 < w) (hw1 : w ≤ 1)
    (hlower : ∀ x ∈ S, ∀ v : Fin n → ℝ,
      c * w * (∑ i, (v i) ^ 2) ≤ ∑ i, ∑ j, v i * hessianMatrix H x i j * v j) :
    0 < min c 1 * w ∧ ∀ x ∈ S, ∀ v : Fin n → ℝ,
      min c 1 * w * (∑ i, (v i) ^ 2) ≤
        ∑ i, ∑ j, v i *
          (if x ∈ A then hessianMatrix H x else (1 : Matrix (Fin n) (Fin n) ℝ)) i j * v j := by
  classical
  refine ⟨mul_pos (lt_min hc zero_lt_one) hw, fun x hx v => ?_⟩
  have hsum : 0 ≤ ∑ i, (v i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (v i))
  by_cases hA : x ∈ A
  · rw [ite_eq_left hA]
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_left c 1) hw.le) hsum).trans (hlower x hx v)
  · rw [ite_eq_right hA]
    have hid : (∑ i, ∑ j, v i * (1 : Matrix (Fin n) (Fin n) ℝ) i j * v j) = ∑ i, (v i) ^ 2 := by
      simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, ← pow_two]
    rw [hid]
    have hcw : min c 1 * w ≤ 1 :=
      (mul_le_mul_of_nonneg_right (min_le_right c 1) hw.le).trans (by simpa using hw1)
    exact (mul_le_mul_of_nonneg_right hcw hsum).trans_eq (one_mul _)

/-- See Subsection 6.1 of the paper, physical lower bound for the short-range
matrix with the identity off the fine event. This holds at every active
size and for any choice of the fine event, with the same explicit
prefactor and exponent as the full physical Hessian. -/
theorem physical_identity_cutoff_coercivity (p : Parameters) (θ : PhysicalCutoff)
    (ε : ℝ) (hε : 0 ≤ ε) (e f a : ℕ) (ha : 1 ≤ a)
    (y : AffineSimplex.chartDomain e ((e + a : ℕ) + 1))
    (z : AffineSimplex.chartDomain f ((f + a : ℕ) + 1)) (L : ℝ)
    (hyL : ((e + a : ℕ) + 1 : ℝ) - ∑ k, y.val k = L)
    (hzL : ((f + a : ℕ) + 1 : ℝ) - ∑ k, z.val k = L) :
    let Y := RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val
    let Z := RetainedSimplex.assemble f a (InterpolatingDensities.exteriorPermutation f a) z.val
    let Dy := Y ⁻¹' gapAmbientDomain (e + a).succPNat
    let Dz := Z ⁻¹' gapAmbientDomain (f + a).succPNat
    let c := min 1 (p.val.2 * (p.val.2 + 1))
    0 < c ∧ ∃ Ky Kz : EuclideanSpace ℝ (Fin (a + 1)) → ℝ,
      ContDiffOn ℝ ∞ Ky Dy ∧ ContDiffOn ℝ ∞ Kz Dz ∧
      (∀ x (hx : x ∈ Dy), Ky x = physicalAmbientGapEnergy p (e + a).succPNat ⟨Y x, hx⟩) ∧
      (∀ x (hx : x ∈ Dz), Kz x = physicalAmbientGapEnergy p (f + a).succPNat ⟨Z x, hx⟩) ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
      let H := fun u : EuclideanSpace ℝ (Fin (a + 1)) =>
        (∑ k, (θ.val ((a + 1 : ℝ) ^ (-ε) * u k) +
          θ.val ((a + 1 : ℝ) ^ (-ε) * (u k)⁻¹))) + (1 - t) * Ky u + t * Kz u
      ∀ (A : Set (EuclideanSpace ℝ (Fin (a + 1)))) x,
      x ∈ AffineSimplex.massSimplex a L → ∀ v : Fin (a + 1) → ℝ,
        c * (a + 1 : ℝ) ^ (-(p.val.2 + 2) * ε) * (∑ i, (v i) ^ 2) ≤
          ∑ i, ∑ j, v i *
            (if x ∈ A then hessianMatrix H x else (1 : Matrix (Fin (a + 1)) (Fin (a + 1)) ℝ)) i j * v j := by
  intro Y Z Dy Dz c
  obtain ⟨hc, Ky, Kz, hKy, hKz, hky, hkz, hphys⟩ :=
    physical_interpolant_coercivity p θ ε hε e f a ha y z L hyL hzL
  refine ⟨hc, Ky, Kz, hKy, hKz, hky, hkz, ?_⟩
  intro t ht H A x hx v
  have hn : (1 : ℝ) ≤ a + 1 := by have := Nat.cast_nonneg a (α := ℝ); linarith
  have hw := Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < a + 1) (-(p.val.2 + 2) * ε)
  have hw1 : (a + 1 : ℝ) ^ (-(p.val.2 + 2) * ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn
      (mul_nonpos_of_nonpos_of_nonneg (by linarith [p.property.2.1]) hε)
  have hh := (identity_cutoff_coercivity_internal (AffineSimplex.massSimplex a L) A H hc hw hw1
    (fun u hu w => (hphys t ht u hu).2 (WithLp.toLp 2 w))).2 x hx v
  have hc1 : c ≤ 1 := min_le_left _ _
  change min c 1 * (a + 1 : ℝ) ^ (-(p.val.2 + 2) * ε) * (∑ i, (v i) ^ 2) ≤ _ at hh
  rwa [min_eq_left hc1] at hh

end Riesz2.InterpolationCoercivity
