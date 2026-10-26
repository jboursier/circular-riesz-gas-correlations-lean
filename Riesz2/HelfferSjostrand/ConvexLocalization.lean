/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.AffineFibreDisintegration
public import Riesz2.ToMathlib.DominatedFibreCalculus
public import Riesz1.ToMathlib.LogConcave.PrekopaMarginalConvex
public import Riesz1.ToMathlib.LogConcave.ConvexDistributionalHessian
public import Riesz1.ToMathlib.Calculus.ConvexLineHessian
public import Riesz1.Frozen.External.PrekopaLeindlerProof

/-!
# Convexity under localization

The negative logarithm of the fibre mass is convex on the open projection,
including when the fibre has dimension zero. The fibre integrals and
conditional probabilities use the affine marginal construction.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace Riesz2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {m : ℕ} {Ω : Set (E × EuclideanSpace ℝ (Fin m))}
  {H₂ : E × EuclideanSpace ℝ (Fin m) → ℝ}

/-- See Lemma 3.5 of the paper, mass and convexity conclusions.
The positive finite mass and the convex remainder are obtained for every point
of the projected interior, including null base points and zero-dimensional
fibres. In the notation of Subsection 3.4, the last function is `H̃ - H₁`. -/
theorem convexLocalization (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hΩb : Bornology.IsBounded Ω) (hH₂ : ConvexOn ℝ Ω H₂) (H₁ : E → ℝ) :
    (∀ x ∈ Prod.fst '' Ω,
      Integrable (fun y => Ω.indicator (fun p => Real.exp (-H₂ p)) (x, y)) ∧
      0 < ∫ y, Ω.indicator (fun p => Real.exp (-H₂ p)) (x, y)) ∧
    ConvexOn ℝ (Prod.fst '' Ω)
      (fun x => (H₁ x - Real.log (∫ y,
        Ω.indicator (fun p => Real.exp (-H₂ p)) (x, y))) - H₁ x) := by
  refine ⟨fun x hx => ⟨Riesz1.integrable_fiber_exp_indicator hΩo hΩb hH₂ x,
    Riesz1.marginal_exp_indicator_pos hΩo hΩb hH₂
      (Riesz1.exists_fiber_of_mem_fst_image hx)⟩, ?_⟩
  suffices hc : ConvexOn ℝ (Prod.fst '' Ω)
      (fun x => -Real.log (∫ y, Ω.indicator (fun p => Real.exp (-H₂ p)) (x, y))) by
    convert hc using 1
    funext x
    ring
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hval : ∀ x ∈ Prod.fst '' Ω,
        -Real.log (∫ y : EuclideanSpace ℝ (Fin 0),
          Ω.indicator (fun p => Real.exp (-H₂ p)) (x, y)) = H₂ (x, 0) := by
      intro x hx
      obtain ⟨y, hy⟩ := Riesz1.exists_fiber_of_mem_fst_image hx
      have hy0 : y = 0 := Subsingleton.elim _ _
      subst hy0
      rw [volume_euclideanSpace_eq_dirac, integral_dirac, indicator_of_mem hy,
        Real.log_exp, neg_neg]
    refine (show ConvexOn ℝ (Prod.fst '' Ω) (fun x => H₂ (x, 0)) from ?_).congr
      (fun x hx => (hval x hx).symm)
    refine ⟨Riesz1.convex_fst_image_prod hΩc, fun x hx y hy a b ha hb hab => ?_⟩
    have hx' : (x, (0 : EuclideanSpace ℝ (Fin 0))) ∈ Ω := by
      obtain ⟨w, hw⟩ := Riesz1.exists_fiber_of_mem_fst_image hx
      simpa only [Subsingleton.elim w 0] using hw
    have hy' : (y, (0 : EuclideanSpace ℝ (Fin 0))) ∈ Ω := by
      obtain ⟨w, hw⟩ := Riesz1.exists_fiber_of_mem_fst_image hy
      simpa only [Subsingleton.elim w 0] using hw
    simpa using hH₂.2 hx' hy' ha hb hab
  · exact Riesz1.convexOn_neg_log_marginal_exp_of_bounded
      Riesz1.External.prekopa_leindler hm hΩo hΩc hΩb hH₂

/-- See Lemma 3.5 of the paper: the distributional lower Hessian
bound, tested in any direction against nonnegative compactly supported C²
tests. No differentiability of the marginal is assumed. -/
theorem convexLocalization_distributional {n m : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))}
    {H₂ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) → ℝ}
    (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω) (hΩb : Bornology.IsBounded Ω)
    (hH₂ : ConvexOn ℝ Ω H₂) (H₁ : EuclideanSpace ℝ (Fin n) → ℝ)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (hφΩ : tsupport φ ⊆ Prod.fst '' Ω)
    (hφ0 : ∀ x, 0 ≤ φ x) (v : EuclideanSpace ℝ (Fin n)) :
    0 ≤ ∫ x, ((H₁ x - Real.log (∫ y,
      Ω.indicator (fun p => Real.exp (-H₂ p)) (x, y))) - H₁ x) *
        fderiv ℝ (fderiv ℝ φ) x v v := by
  exact Riesz1.convexOn_distributional_hessian_nonneg (isOpenMap_fst _ hΩo)
    (Riesz1.convex_fst_image_prod hΩc)
    (convexLocalization hΩo hΩc hΩb hH₂ H₁).2 hφ hφc hφΩ hφ0 v

namespace ConvexLocalizationInternal

/-- Classical lower Hessian bound from the convexity part of Lemma 3.5,
assuming C² regularity. -/
theorem hessian_lower_of_contDiff {n m : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))}
    {H₂ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) → ℝ}
    (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω) (hΩb : Bornology.IsBounded Ω)
    (hH₂ : ConvexOn ℝ Ω H₂) (H₁ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hH₁ : ContDiffOn ℝ 2 H₁ (Prod.fst '' Ω))
    (hHm : ContDiffOn ℝ 2 (fun x => H₁ x - Real.log (∫ y,
      Ω.indicator (fun p => Real.exp (-H₂ p)) (x, y))) (Prod.fst '' Ω))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Prod.fst '' Ω)
    (v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fderiv ℝ H₁) x v v ≤
      fderiv ℝ (fderiv ℝ (fun z => H₁ z - Real.log (∫ y,
        Ω.indicator (fun p => Real.exp (-H₂ p)) (z, y)))) x v v := by
  have ho : IsOpen (Prod.fst '' Ω) := isOpenMap_fst _ hΩo
  have hnonneg := Riesz1.fderiv_fderiv_nonneg_of_convexOn ho
    (Riesz1.convex_fst_image_prod hΩc)
    (convexLocalization hΩo hΩc hΩb hH₂ H₁).2 (hHm.sub hH₁) hx v
  have heq : fderiv ℝ (fun z =>
      (H₁ z - Real.log (∫ y, Ω.indicator (fun p => Real.exp (-H₂ p)) (z, y))) - H₁ z) =ᶠ[𝓝 x]
      fun z => fderiv ℝ (fun z => H₁ z - Real.log (∫ y,
        Ω.indicator (fun p => Real.exp (-H₂ p)) (z, y))) z - fderiv ℝ H₁ z := by
    filter_upwards [ho.mem_nhds hx] with z hz
    exact fderiv_sub
      ((hHm.differentiableOn (by norm_num)).differentiableAt (ho.mem_nhds hz))
      ((hH₁.differentiableOn (by norm_num)).differentiableAt (ho.mem_nhds hz))
  rw [heq.fderiv_eq, fderiv_fun_sub
    (((hHm.fderiv_of_isOpen ho (by norm_num : 1 + 1 ≤ (2 : WithTop ℕ∞))).differentiableOn
      (by norm_num)).differentiableAt (ho.mem_nhds hx))
    (((hH₁.fderiv_of_isOpen ho (by norm_num : 1 + 1 ≤ (2 : WithTop ℕ∞))).differentiableOn
      (by norm_num)).differentiableAt (ho.mem_nhds hx))] at hnonneg
  simpa only [sub_apply, sub_nonneg] using hnonneg

end ConvexLocalizationInternal

/-- See Lemma 3.5 of the paper, the first derivative identity
under the stated local fixed-fibre domination. The conditional force is proved
integrable. The hypothesis differentiates the zero-extended density itself,
so it includes the boundary requirement in Lemma 3.5. -/
theorem convexLocalization_gradient (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hH₂ : ConvexOn ℝ Ω H₂) (H₁ : E → ℝ)
    (hH₁ : DifferentiableOn ℝ H₁ (Prod.fst '' Ω))
    (hdom : DominatedFibre.DominatedFDerivOn
      (volume : Measure (EuclideanSpace ℝ (Fin m))) (Prod.fst '' Ω)
      (fun x y => Ω.indicator (fun p => Real.exp (-H₂ p)) (x, y))
      (fun x y => -Ω.indicator (fun p => Real.exp (-H₂ p)) (x, y) •
        fderiv ℝ (fun z => H₂ (z, y)) x))
    {x : E} (hx : x ∈ Prod.fst '' Ω) (u : E) :
    let ρ := AffineFibre.convexConditionalMeasure hΩo hΩb hH₂ ⟨x, hx⟩
    Integrable (fun y => fderiv ℝ (fun z => H₂ (z, y)) x u) ρ ∧
      fderiv ℝ (fun z => H₁ z - Real.log (∫ y,
        Ω.indicator (fun p => Real.exp (-H₂ p)) (z, y))) x u =
        fderiv ℝ H₁ x u + ∫ y, fderiv ℝ (fun z => H₂ (z, y)) x u ∂ρ := by
  intro ρ
  have hp : 0 < ∫ y, Ω.indicator (fun p => Real.exp (-H₂ p)) (x, y) :=
    Riesz1.marginal_exp_indicator_pos hΩo hΩb hH₂
      (Riesz1.exists_fiber_of_mem_fst_image hx)
  have hn : ∀ y, 0 ≤ Ω.indicator (fun p => Real.exp (-H₂ p)) (x, y) :=
    fun y => indicator_nonneg (fun p _ => (Real.exp_pos _).le) _
  have hi : Integrable (fun y => fderiv ℝ (fun z => H₂ (z, y)) x u) ρ := by
    exact DominatedFibre.integrable_gibbs_force hdom hx hn hp
      (fun y => fderiv ℝ (fun z => H₂ (z, y)) x)
      (Filter.Eventually.of_forall fun y => by module) u
  refine ⟨hi, ?_⟩
  have hh := (hdom.hasFDerivAt_integral hx).log hp.ne'
  have h₁ := (hH₁.differentiableAt ((isOpenMap_fst _ hΩo).mem_nhds hx)).hasFDerivAt
  rw [(h₁.fun_sub hh).fderiv]
  have he : (∫ y, (-Ω.indicator (fun p => Real.exp (-H₂ p)) (x, y) •
      fderiv ℝ (fun z => H₂ (z, y)) x) u) =
        -(∫ y, Ω.indicator (fun p => Real.exp (-H₂ p)) (x, y) *
          fderiv ℝ (fun z => H₂ (z, y)) x u) := by
    simp only [smul_apply, smul_eq_mul, neg_mul, integral_neg]
  change _ = _ + ∫ y, fderiv ℝ (fun z => H₂ (z, y)) x u ∂ρ
  dsimp only [ρ, AffineFibre.convexConditionalMeasure]
  rw [DominatedFibre.integral_normalizedMeasure (hdom.integrable x hx) hn hp]
  simp only [sub_apply, smul_apply, smul_eq_mul]
  rw [ContinuousLinearMap.integral_apply (hdom.integrable_derivative hx), he]
  ring

end Riesz2

end
