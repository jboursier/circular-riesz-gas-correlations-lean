/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.AffinePullbackEstimates
public import Riesz2.ToMathlib.InfDistFrontier
public import Riesz1.ToMathlib.Calculus.ConvexLineHessian

/-!
# Collision criteria under an invertible affine change

The change of metric in Step 1 of Lemma A.1 of the paper.
The trace comparison uses positivity of the full Hessian, independently
of any pair-potential representation.
-/

@[expose] public section
noncomputable section

open Set Metric
open scoped ContDiff

namespace Riesz2

/-- The all-coefficient collision condition of Lemma A.1, Step 1,
for the intrinsic Euclidean metric on an open domain. -/
def allCoefficientCollisionCriterion {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (U : Set E) (f : E → ℝ) : Prop :=
  ∀ a : ℝ, 0 < a → ∃ C : ℝ, 0 < C ∧ ∀ x ∈ U,
    (infDist x (frontier U))⁻¹ ^ 2 - C ≤
      a * ‖gradient f x‖ ^ 2 - Laplacian.laplacian f x

namespace AffineCollision

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Internal trace positivity used in Lemma A.1, Step 1, of the paper. -/
theorem internal_laplacian_nonneg {f : E → ℝ} {x : E}
    (hp : ∀ u : E, 0 ≤ fderiv ℝ (fderiv ℝ f) x u u) :
    0 ≤ Laplacian.laplacian f x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (stdOrthonormalBasis ℝ E)]
  simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using
    Finset.sum_nonneg (fun i _ => hp (stdOrthonormalBasis ℝ E i))

/-- Internal positive-Hessian trace bound for Lemma A.1, Step 1.
Extend a unit vector to an orthonormal basis. -/
theorem internal_hessian_le_trace {f : E → ℝ} {x : E}
    (hp : ∀ u : E, 0 ≤ fderiv ℝ (fderiv ℝ f) x u u) (u : E) :
    fderiv ℝ (fderiv ℝ f) x u u ≤ Laplacian.laplacian f x * ‖u‖ ^ 2 := by
  classical
  by_cases hu : u = 0
  · simp [hu]
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  let v : E := ‖u‖⁻¹ • u
  have hv : ‖v‖ = 1 := by simp [v, norm_smul, hn]
  have ho : Orthonormal ℝ ((↑) : ({v} : Set E) → E) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    simpa only [Set.mem_singleton_iff.mp i.property] using hv
  obtain ⟨w, b, hsub, hb⟩ := ho.exists_orthonormalBasis_extension
  let j : w := ⟨v, hsub (mem_singleton v)⟩
  have hj : b j = v := congrFun hb j
  have ht : fderiv ℝ (fderiv ℝ f) x v v ≤ Laplacian.laplacian f x := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← hj]
    exact Finset.single_le_sum (fun i _ => hp (b i)) (Finset.mem_univ j)
  have hu' : ‖u‖ • v = u := by
    dsimp only [v]
    rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
  have hscale := congrArg (fun z => fderiv ℝ (fderiv ℝ f) x z z) hu'
  simp only [map_smul, smul_apply, smul_eq_mul] at hscale
  nlinarith only [mul_le_mul_of_nonneg_left ht (sq_nonneg ‖u‖), hscale]

/-- Internal affine trace comparison in Lemma A.1, Step 1.
A dimension factor suffices for the metric comparison. -/
theorem internal_laplacian_pullback_le (e : E ≃L[ℝ] F) (v : F)
    {f : F → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f (e x + v))
    (hp : ∀ u : F, 0 ≤ fderiv ℝ (fderiv ℝ f) (e x + v) u u) :
    Laplacian.laplacian (fun z => f (e z + v)) x ≤
      ((Module.finrank ℝ E : ℝ) * ‖e.toContinuousLinearMap‖ ^ 2) *
        Laplacian.laplacian f (e x + v) := by
  let b := stdOrthonormalBasis ℝ E
  have ht := internal_laplacian_nonneg hp
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hi (i : Fin (Module.finrank ℝ E)) :
      fderiv ℝ (fderiv ℝ (fun z => f (e z + v))) x (b i) (b i) ≤
        Laplacian.laplacian f (e x + v) * ‖e.toContinuousLinearMap‖ ^ 2 := by
    change fderiv ℝ (fderiv ℝ (fun z => f (e.toContinuousLinearMap z + v))) x
      (b i) (b i) ≤ _
    rw [AffineMetricTransport.hessian_comp_affine e.toContinuousLinearMap v hf]
    apply (internal_hessian_le_trace hp _).trans
    apply mul_le_mul_of_nonneg_left _ ht
    apply pow_le_pow_left₀ (norm_nonneg _)
    simpa only [b.norm_eq_one, mul_one] using e.toContinuousLinearMap.le_opNorm (b i)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_assoc, mul_comm, mul_left_comm] using hsum

/-- Internal transport used in Lemma A.1, Step 1, of the paper.
The coefficient is divided by the fourth power of a common metric bound,
then the collision inequality is multiplied by its square. -/
theorem internal_pullback (e : E ≃L[ℝ] F) (v : F) {U : Set E}
    (hU : IsOpen U) (hne : Uᶜ.Nonempty) {f : F → ℝ}
    (hf : ContDiffOn ℝ 2 f ((fun x => e x + v) '' U))
    (hp : ∀ y ∈ (fun x => e x + v) '' U, ∀ u : F,
      0 ≤ fderiv ℝ (fderiv ℝ f) y u u)
    (h : allCoefficientCollisionCriterion ((fun x => e x + v) '' U) f) :
    allCoefficientCollisionCriterion U (fun x => f (e x + v)) := by
  let T : E ≃ₜ F := e.toHomeomorph.trans (Homeomorph.addRight v)
  let V := T '' U
  have hV : IsOpen V := T.isOpenMap U hU
  have hVc : Vᶜ.Nonempty := by rw [← T.image_compl]; exact hne.image T
  let D := (Module.finrank ℝ E : ℝ) * ‖e.toContinuousLinearMap‖ ^ 2
  let C := 1 + ‖e.toContinuousLinearMap‖ + ‖e.symm.toContinuousLinearMap‖ + D
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hC : 1 ≤ C := by dsimp only [C]; linarith [norm_nonneg e.toContinuousLinearMap, norm_nonneg e.symm.toContinuousLinearMap]
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hA : ‖e.toContinuousLinearMap‖ ≤ C := by dsimp only [C]; linarith [norm_nonneg e.toContinuousLinearMap, norm_nonneg e.symm.toContinuousLinearMap]
  have hB : ‖e.symm.toContinuousLinearMap‖ ≤ C := by dsimp only [C]; linarith [norm_nonneg e.toContinuousLinearMap, norm_nonneg e.symm.toContinuousLinearMap]
  have hDC : D ≤ C ^ 2 := by
    have hDC : D ≤ C := by dsimp only [C]; linarith [norm_nonneg e.toContinuousLinearMap, norm_nonneg e.symm.toContinuousLinearMap]
    nlinarith
  intro a ha
  obtain ⟨K, hK, hb⟩ := h (a / C ^ 4) (by positivity)
  refine ⟨C ^ 2 * K, by positivity, fun x hx => ?_⟩
  have hy : e x + v ∈ V := ⟨x, hx, rfl⟩
  have hsm : ContDiffAt ℝ 2 f (e x + v) := hf.contDiffAt (hV.mem_nhds hy)
  have hpos := hp _ hy
  have hlap := internal_laplacian_nonneg hpos
  have hl := internal_laplacian_pullback_le e v hsm hpos
  have hl' : Laplacian.laplacian (fun z => f (e z + v)) x ≤
      C ^ 2 * Laplacian.laplacian f (e x + v) :=
    hl.trans (mul_le_mul_of_nonneg_right hDC hlap)
  have hg := (AffinePullback.gradient_norm_le e v (hsm.differentiableAt (by norm_num))).trans
    (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  have hg2 := pow_le_pow_left₀ (norm_nonneg _) hg 2
  have hg' : (a / C ^ 2) * ‖gradient f (e x + v)‖ ^ 2 ≤
      a * ‖gradient (fun z => f (e z + v)) x‖ ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hg2 (by positivity : 0 ≤ a / C ^ 2)
    have heq : a / C ^ 2 * (C * ‖gradient (fun z => f (e z + v)) x‖) ^ 2 =
        a * ‖gradient (fun z => f (e z + v)) x‖ ^ 2 := by field_simp
    rw [heq] at hh
    exact hh
  have hdist := (AffineMetricTransport.infDist_affine_image_bounds e v
    hU.isClosed_compl hne x).1
  change infDist (e x + v) (T '' Uᶜ) ≤ _ at hdist
  rw [T.image_compl] at hdist
  have hdist' : infDist (e x + v) Vᶜ ≤ C * infDist x Uᶜ :=
    hdist.trans (mul_le_mul_of_nonneg_right hA infDist_nonneg)
  have hxpos : 0 < infDist x Uᶜ :=
    (hU.isClosed_compl.notMem_iff_infDist_pos hne).mp (not_not.mpr hx)
  have hypos : 0 < infDist (e x + v) Vᶜ :=
    (hV.isClosed_compl.notMem_iff_infDist_pos hVc).mp (not_not.mpr hy)
  have hdinv : (infDist x Uᶜ)⁻¹ ^ 2 ≤ C ^ 2 * (infDist (e x + v) Vᶜ)⁻¹ ^ 2 := by
    have hd2 := pow_le_pow_left₀ hypos.le hdist' 2
    rw [inv_pow, inv_pow, inv_eq_one_div, inv_eq_one_div, mul_one_div]
    apply (div_le_div_iff₀ (sq_pos_of_pos hxpos) (sq_pos_of_pos hypos)).mpr
    simpa only [mul_pow, one_mul] using hd2
  have hbound := mul_le_mul_of_nonneg_left (hb _ hy) (sq_nonneg C)
  change C ^ 2 * ((infDist (e x + v) (frontier V))⁻¹ ^ 2 - K) ≤ _ at hbound
  rw [infDist_frontier_eq_infDist_compl hV hy hVc] at hbound
  have heq : C ^ 2 * (a / C ^ 4) = a / C ^ 2 := by field_simp
  simp only [mul_sub, ← mul_assoc, heq] at hbound
  rw [infDist_frontier_eq_infDist_compl hU hx hne]
  nlinarith only [hbound, hg', hl', hdinv]

end AffineCollision

/-- Lemma Lemma A.1, Step 1, of the paper: for a smooth convex
potential, the collision condition for every positive coefficient is
equivalent in two Euclidean metrics related by an invertible affine map.
The proper open domain need not be bounded. -/
theorem allCoefficientCollisionCriterion_affine_iff
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (e : E ≃L[ℝ] F) (v : F) {U : Set E}
    (hU : IsOpen U) (hne : Uᶜ.Nonempty) {f : F → ℝ}
    (hf : ContDiffOn ℝ 2 f ((fun x => e x + v) '' U))
    (hc : ConvexOn ℝ ((fun x => e x + v) '' U) f) :
    allCoefficientCollisionCriterion U (fun x => f (e x + v)) ↔
      allCoefficientCollisionCriterion ((fun x => e x + v) '' U) f := by
  let T : E ≃ₜ F := e.toHomeomorph.trans (Homeomorph.addRight v)
  let V := T '' U
  have hV : IsOpen V := T.isOpenMap U hU
  have hVc : Vᶜ.Nonempty := by rw [← T.image_compl]; exact hne.image T
  have hp (y) (hy : y ∈ V) (u : F) : 0 ≤ fderiv ℝ (fderiv ℝ f) y u u :=
    Riesz1.fderiv_fderiv_nonneg_of_convexOn hV hc.1 hc hf hy u
  constructor
  · intro h
    let g : E → ℝ := fun x => f (e x + v)
    have hmap : (fun y => e.symm y + -e.symm v) '' V = U := by
      ext x
      constructor
      · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        change e.symm (e z + v) + -e.symm v ∈ U
        simpa only [map_add, e.symm_apply_apply, add_neg_cancel_right] using hz
      · intro hx
        refine ⟨e x + v, ⟨x, hx, rfl⟩, ?_⟩
        simp
    have hgs : ContDiffOn ℝ 2 g U := by
      intro x hx
      have hy : e x + v ∈ V := ⟨x, hx, rfl⟩
      exact ((hf.contDiffAt (hV.mem_nhds hy)).comp x
        (e.contDiff.add contDiff_const).contDiffAt).contDiffWithinAt
    have hgp (x) (hx : x ∈ U) (u : E) : 0 ≤ fderiv ℝ (fderiv ℝ g) x u u := by
      change 0 ≤ fderiv ℝ (fderiv ℝ (fun z => f (e.toContinuousLinearMap z + v))) x u u
      rw [AffineMetricTransport.hessian_comp_affine e.toContinuousLinearMap v
        (hf.contDiffAt (hV.mem_nhds ⟨x, hx, rfl⟩))]
      exact hp _ ⟨x, hx, rfl⟩ _
    have hback := AffineCollision.internal_pullback e.symm (-e.symm v) hV hVc
      (hmap.symm ▸ hgs) (hmap.symm ▸ hgp) (hmap.symm ▸ h)
    have heq : (fun y => g (e.symm y + -e.symm v)) = f := by
      funext y
      simp [g]
    rwa [heq] at hback
  · exact AffineCollision.internal_pullback e v hU hne hf hp

/-- Lemma Lemma A.1, Step 1, of the paper, with convexity stated
for the original potential `H = f ∘ T`, as in the paper. -/
theorem allCoefficientCollisionCriterion_affine_iff_of_convex_pullback
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (e : E ≃L[ℝ] F) (v : F) {U : Set E}
    (hU : IsOpen U) (hne : Uᶜ.Nonempty) {f : F → ℝ}
    (hf : ContDiffOn ℝ 2 f ((fun x => e x + v) '' U))
    (hc : ConvexOn ℝ U (fun x => f (e x + v))) :
    allCoefficientCollisionCriterion U (fun x => f (e x + v)) ↔
      allCoefficientCollisionCriterion ((fun x => e x + v) '' U) f := by
  let A : F →ᵃ[ℝ] E := e.symm.toLinearEquiv.toLinearMap.toAffineMap +
    AffineMap.const ℝ F (-e.symm v)
  have hA (y : F) : A y = e.symm (y - v) := by simp [A, sub_eq_add_neg]
  have hpre : A ⁻¹' U = (fun x => e x + v) '' U := by
    ext y
    constructor
    · intro hy
      refine ⟨A y, hy, ?_⟩
      simp [hA]
    · rintro ⟨x, hx, rfl⟩
      simpa [hA] using hx
  have hfun : (fun x => f (e x + v)) ∘ A = f := by
    funext y
    simp [hA]
  have htarget := hc.comp_affineMap A
  rw [hpre, hfun] at htarget
  exact allCoefficientCollisionCriterion_affine_iff e v hU hne hf htarget

end Riesz2
