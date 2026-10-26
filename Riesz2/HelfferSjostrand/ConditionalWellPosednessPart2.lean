/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.ConditionalWellPosedness
public import Riesz2.HelfferSjostrand.GapRepresentationPart3
public import Riesz2.HelfferSjostrand.AuxiliarySources

/-!
# Conditional and interpolating well-posedness

Intrinsic collision estimates and well-posedness for Appendix A.
The laws use the physical affine simplex, penalties and marginal density.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal

namespace Riesz2.ConditionalWellPosedness

/-- Internal scalar radial bound about any positive centre. -/
theorem internal_power_radial_at {s c d : ℝ} (hs : 0 < s) (hc : 0 < c)
    (hd : 0 < d) :
    ∃ α C : ℝ, 0 < α ∧ 0 < C ∧ ∀ x : ℝ, 0 < x →
      α * x ^ (-s - 1) - C ≤ c * (-s) * x ^ (-s - 1) * (x - d) := by
  let α := c * s * (d / 2)
  let C := α * (d / 2) ^ (-s - 1) + s * c * (d / 2) ^ (-s) + 1
  have hα : 0 < α := by positivity
  have hC : 0 < C := by positivity
  refine ⟨α, C, hα, hC, fun x hx => ?_⟩
  by_cases h : x ≤ d / 2
  · have ht := mul_le_mul_of_nonneg_left (show d / 2 ≤ d - x by linarith)
      (show 0 ≤ c * s * x ^ (-s - 1) by positivity)
    dsimp only [α]
    nlinarith only [ht, hC.le]
  · have ht := ElementaryBarriers.term_lower_bound hs hc hd hx
    have hp : x ^ (-s - 1) ≤ (d / 2) ^ (-s - 1) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (le_of_not_ge h) (by linarith)
    have hcp := mul_le_mul_of_nonneg_left hp hα.le
    dsimp only [C]
    nlinarith only [ht, hcp]

/-- Internal chain rule for inverse penalties in arbitrary affine coordinates. -/
theorem internal_inverse_faces_derivative {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Fintype ι] (ℓ : ι → E →ᵃ[ℝ] ℝ) (θ : PhysicalCutoff)
    {a : ℝ} (ha : 0 < a) (J : Finset ι) (z : E) (hz : ∀ i, 0 < ℓ i z) :
    HasFDerivAt (fun w => ∑ i ∈ J, θ.val (a / ℓ i w))
      (∑ i ∈ J, deriv (fun u => θ.val (a / u)) (ℓ i z) •
        LinearMap.toContinuousLinearMap (ℓ i).linear) z := by
  apply HasFDerivAt.fun_sum
  intro i _
  have hi := (PhysicalCollision.inverse_penalty_hasDerivAt θ ha (hz i)).differentiableAt.hasDerivAt
  have hlin : HasFDerivAt (fun w => ℓ i w)
      (LinearMap.toContinuousLinearMap (ℓ i).linear) z := by
    have he : (fun w => ℓ i w) = fun w =>
        (LinearMap.toContinuousLinearMap (ℓ i).linear) w + ℓ i 0 := by
      funext w
      simpa using congrFun (AffineMap.decomp (ℓ i)) w
    rw [he]
    exact (LinearMap.toContinuousLinearMap (ℓ i).linear).hasFDerivAt.add_const _
  exact HasDerivAt.comp_hasFDerivAt (h₂ := fun u : ℝ => θ.val (a / u))
    (f := fun w => ℓ i w) z hi hlin

/-- Internal uniform radial estimate. The remainder is convex and its
centre derivative is bounded over the parameter family. Radial contributions
are combined before estimating the norm, including selected inverse penalties. -/
theorem internal_fibre_gradient_lower {T : Type*} (n : ℕ) {L s c β : ℝ}
    (hL : 0 < L) (hs : 0 < s) (hc : 0 < c) (hβ : 0 < β)
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (J : Finset (Fin (n + 1))) (b : Bool)
    (R V : T → AffineSimplex.Tangent n → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hRs : ∀ t, ContDiffOn ℝ ∞ (R t)
      (AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L))
    (hRc : ∀ t, ConvexOn ℝ
      (AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L) (R t))
    (hRM : ∀ t, ‖fderiv ℝ (R t) 0‖ ≤ M)
    (hV : ∀ t z, z ∈ AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L →
      V t z = (∑ i, c * (AffineSimplex.centredChart n L z i) ^ (-s)) + R t z +
        if b then β * ∑ i ∈ J, θ.val (a / AffineSimplex.centredChart n L z i) else 0) :
    ∃ α C : ℝ, 0 < α ∧ 0 < C ∧ ∀ t z,
      z ∈ AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L →
      α * ((⨅ i, AffineSimplex.centredChart n L z i) ^ (-s - 1) +
        if b then ∑ i ∈ J, (AffineSimplex.centredChart n L z i)⁻¹ ^ 3 else 0) - C ≤
        ‖gradient (V t) z‖ := by
  classical
  let Ω := AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L
  let d := L / (n + 1)
  have hd : 0 < d := by dsimp only [d]; positivity
  have hzero : (0 : AffineSimplex.Tangent n) ∈ Ω := by
    simpa only [Ω, mem_preimage, AffineSimplex.centredChart, Submodule.coe_zero, zero_add]
      using AffineSimplex.centre_mem_simplex n hL
  let F := AffineSimplex.centredChart n L
  let A : AffineSimplex.Tangent n →ᵃ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    (AffineSimplex.Tangent n).subtype.toAffineMap +
      AffineMap.const ℝ _ (AffineSimplex.centre n L)
  let ℓ : Fin (n + 1) → AffineSimplex.Tangent n →ᵃ[ℝ] ℝ := fun i =>
    (EuclideanSpace.proj i).toLinearMap.toAffineMap.comp A
  have hℓ (i) (z : AffineSimplex.Tangent n) : ℓ i z = F z i := rfl
  have hℓ0 (i) : ℓ i 0 = d := by simp [ℓ, A, d, AffineSimplex.centre]
  have hlin (i) (z : AffineSimplex.Tangent n) :
      (LinearMap.toContinuousLinearMap (ℓ i).linear) z = F z i - d := by
    rw [← hℓ, ← hℓ0 i, ← ElementaryBarriers.linear_sub_eq]
    simp only [sub_zero]
  have hRd (t) (z) (hz : z ∈ Ω) : DifferentiableAt ℝ (R t) z :=
    ((hRs t).contDiffAt ((fibre_isOpen n L).mem_nhds hz)).differentiableAt (by simp)
  obtain ⟨r, hr⟩ := (fibre_isBounded n L).subset_closedBall 0
  let D := max r 1
  have hD : 0 < D := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hnorm (z) (hz : z ∈ Ω) : ‖z‖ ≤ D := by
    have hh := hr hz
    simpa only [Metric.mem_closedBall, dist_zero_right] using hh.trans (le_max_left r 1)
  obtain ⟨c₀, C₀, hc₀, hC₀, hp⟩ := internal_power_radial_at hs hc hd
  obtain ⟨c₁, C₁, hc₁, hC₁, hq⟩ := PhysicalCollision.inverse_penalty_radial θ ha hd
  let c₂ := min c₀ (β * c₁)
  have hc₂ : 0 < c₂ := lt_min hc₀ (mul_pos hβ hc₁)
  let B := (n + 1 : ℕ) * C₀ + β * J.card * C₁ + M * D + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨c₂ / D, B / D, div_pos hc₂ hD, div_pos hB hD, fun t z hz => ?_⟩
  let Q := fun w : AffineSimplex.Tangent n => ∑ i ∈ J, θ.val (a / F w i)
  let W := fun w => (∑ i, c * (ℓ i w) ^ (-s)) + R t w
  have hnear : V t =ᶠ[𝓝 z] fun w => W w + if b then β * Q w else 0 := by
    filter_upwards [(fibre_isOpen n L).mem_nhds hz] with w hw
    exact hV t w hw
  have hQd := internal_inverse_faces_derivative ℓ θ ha J z (fun i => hz.1 i)
  change HasFDerivAt Q _ z at hQd
  have hBs : ContDiffOn ℝ ∞ (fun w => ∑ i, c * (ℓ i w) ^ (-s)) Ω := by
    have he : Ω = {w | ∀ i, 0 < ℓ i w} := by
      ext w; exact and_iff_left (AffineSimplex.sum_centredChart n L w)
    rw [he]
    exact MarginalCollision.internal_barrier_smooth ℓ (fun _ => c) s
  have hWd : DifferentiableAt ℝ W z :=
    ((hBs.contDiffAt ((fibre_isOpen n L).mem_nhds hz)).differentiableAt (by simp)).add (hRd t z hz)
  have hfdW := ElementaryBarriers.fderiv_potential_apply
    (ℓ := ℓ) (a := fun _ => c) (s := s) (fun i => (hz.1 i).ne') (hRd t z hz) z
  change fderiv ℝ W z z = _ at hfdW
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hp (F z i) (hz.1 i))
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum] at hsum
  have hR := ElementaryBarriers.convex_fderiv_sub_lower (hRc t) hz hzero
    (hRd t z hz) (hRd t 0 hzero) (by simpa only [sub_zero] using hnorm z hz)
  have hRM' := mul_le_mul_of_nonneg_right (hRM t) hD.le
  simp only [sub_zero] at hR
  have hQ := Finset.sum_le_sum (s := J) (fun i _ => hq (F z i) (hz.1 i))
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hQ
  have hfdQ : fderiv ℝ Q z z = ∑ i ∈ J,
      deriv (fun u => θ.val (a / u)) (F z i) * (F z i - d) := by
    rw [hQd.fderiv]
    simp only [sum_apply, smul_apply, smul_eq_mul, hlin, hℓ]
  rw [← hfdQ] at hQ
  have hfdV : fderiv ℝ (V t) z z = fderiv ℝ W z z +
      if b then β * fderiv ℝ Q z z else 0 := by
    rw [hnear.fderiv_eq]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
    · simp only [↓reduceIte]
      rw [fderiv_fun_add hWd (hQd.differentiableAt.const_mul β), fderiv_const_mul hQd.differentiableAt]
      rfl
  obtain ⟨i, hi⟩ := ElementaryBarriers.exists_iInf_eq_apply (fun i => F z i)
  have hmin : (⨅ i, F z i) ^ (-s - 1) ≤ ∑ i, (F z i) ^ (-s - 1) := by
    rw [hi]
    exact Finset.single_le_sum (fun j _ => Real.rpow_nonneg (hz.1 j).le _) (Finset.mem_univ i)
  have hcoeff := mul_le_mul_of_nonneg_left hmin hc₂.le
  have hcoef₀ := mul_le_mul_of_nonneg_right (min_le_left c₀ (β * c₁))
    (show 0 ≤ ∑ i, (F z i) ^ (-s - 1) from
      Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hz.1 i).le _)
  have hcoef₁ := mul_le_mul_of_nonneg_right (min_le_right c₀ (β * c₁))
    (show 0 ≤ ∑ i ∈ J, (F z i)⁻¹ ^ 3 from
      Finset.sum_nonneg fun i _ => pow_nonneg (inv_nonneg.mpr (hz.1 i).le) 3)
  have hlow : c₂ * ((⨅ i, F z i) ^ (-s - 1) +
      if b then ∑ i ∈ J, (F z i)⁻¹ ^ 3 else 0) - B ≤ fderiv ℝ (V t) z z := by
    rw [hfdV, hfdW]
    simp only [hlin, hℓ]
    have hQβ := mul_le_mul_of_nonneg_left hQ hβ.le
    have hβC : 0 ≤ β * J.card * C₁ := by positivity
    dsimp only [B]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, add_zero] <;>
      linarith only [hsum, hR, hRM', hQβ, hcoeff, hcoef₀, hcoef₁, hβC]
  have hop := (fderiv ℝ (V t) z).le_opNorm z
  rw [Real.norm_eq_abs] at hop
  have hgn : ‖gradient (V t) z‖ = ‖fderiv ℝ (V t) z‖ := by
    rw [gradient, LinearIsometryEquiv.norm_map]
  have hupper : fderiv ℝ (V t) z z ≤ ‖gradient (V t) z‖ * D := by
    rw [← hgn] at hop
    exact (le_abs_self _).trans (hop.trans
      (mul_le_mul_of_nonneg_left (hnorm z hz) (norm_nonneg _)))
  change c₂ / D * _ - B / D ≤ ‖gradient (V t) z‖
  rw [div_mul_eq_mul_div, ← sub_div, div_le_iff₀ hD]
  linarith only [hlow, hupper]

/-- Internal mixed-power absorption, uniform over a parameter family.
The two lower-order singularities are absorbed by the square of the combined
radial gradient bound. -/
theorem internal_fibre_mixed_collision {T : Type*} (n : ℕ) (hn : 1 ≤ n) (L : ℝ) {s : ℝ} (hs : 0 < s)
    (J : Finset (Fin (n + 1))) (b : Bool) (V : T → AffineSimplex.Tangent n → ℝ)
    {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hg : ∀ t x, x ∈ AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L →
      c * ((⨅ j, AffineSimplex.centredChart n L x j) ^ (-s - 1) + if b then ∑ i ∈ J, (AffineSimplex.centredChart n L x i)⁻¹ ^ 3 else 0) - C ≤
        ‖gradient (V t) x‖)
    (hΔ : ∀ t x, x ∈ AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L →
      Laplacian.laplacian (V t) x ≤ C *
        (1 + (⨅ j, AffineSimplex.centredChart n L x j) ^ (-s - 2) + if b then ∑ i ∈ J, (AffineSimplex.centredChart n L x i)⁻¹ ^ 4 else 0)) :
    ∀ A K : ℝ, 0 < A → 0 < K → ∃ D : ℝ, 0 ≤ D ∧
      ∀ t x, x ∈ AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L →
        K * (Metric.infDist x (frontier (AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L)))⁻¹ ^ 2 - D ≤
          A * ‖gradient (V t) x‖ ^ 2 - Laplacian.laplacian (V t) x := by
  let : Nontrivial (AffineSimplex.Tangent n) := Module.nontrivial_of_finrank_pos
    (R := ℝ) (by rw [AffineSimplex.finrank_tangent]; omega)
  intro A K hA hK
  let α := A * c ^ 2 / 4
  have hα : 0 < α := by positivity
  let Ω := AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L
  let F := AffineSimplex.centredChart n L
  let Taff : AffineSimplex.Tangent n →ᵃ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    (AffineSimplex.Tangent n).subtype.toAffineMap + AffineMap.const ℝ _ (AffineSimplex.centre n L)
  let ℓ : Fin (n + 1) → AffineSimplex.Tangent n →ᵃ[ℝ] ℝ := fun i =>
    (EuclideanSpace.proj i).toLinearMap.toAffineMap.comp Taff
  have hΩ : Ω = {z | ∀ i, 0 < ℓ i z} := by
    ext z; exact and_iff_left (AffineSimplex.sum_centredChart n L z)
  obtain ⟨G, hG, hlip⟩ := AffinePolytope.exists_lipschitz ℓ
  obtain ⟨D₀, hD₀⟩ := RpowDomination.exists_bound hs hα hC.le
    (show 0 ≤ K * G ^ 2 by positivity)
  obtain ⟨D₁, hD₁⟩ := PhysicalCollision.internal_inverse_sum_absorption J hα hC.le
  let E := D₀ + (if b then D₁ else 0) + A * C ^ 2
  refine ⟨max E 0, le_max_right _ _, fun t x hx => ?_⟩
  let δ := ⨅ j, AffineSimplex.centredChart n L x j
  let X := δ ^ (-s - 1)
  let Y := if b then ∑ i ∈ J, (AffineSimplex.centredChart n L x i)⁻¹ ^ 3 else 0
  let Z := if b then ∑ i ∈ J, (AffineSimplex.centredChart n L x i)⁻¹ ^ 4 else 0
  have hδ : 0 < δ := by
    obtain ⟨i, hi⟩ := ElementaryBarriers.exists_iInf_eq_apply (fun i => F x i)
    change 0 < ⨅ i, F x i
    rw [hi]
    exact hx.1 i
  have hX : 0 ≤ X := Real.rpow_nonneg hδ.le _
  have hY : 0 ≤ Y := by
    cases b
    · exact le_rfl
    · exact Finset.sum_nonneg fun i _ => pow_nonneg (inv_nonneg.mpr (hx.1 i).le) _
  have hinv : C * Z ≤ α * Y ^ 2 + if b then D₁ else 0 := by
    cases b
    · simp only [Y, Z, Bool.false_eq_true, ↓reduceIte, mul_zero, zero_pow, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, add_zero, le_refl]
    · exact hD₁ (fun i => F x i) (fun i _ => hx.1 i)
  have hdom := hD₀ δ hδ
  have hd := AffinePolytope.div_le_infDist_frontier ℓ hΩ
    (fibre_isBounded n L) hG hlip hx
  have hdpos : 0 < δ / G := div_pos hδ hG
  have hdsq := pow_le_pow_left₀ hdpos.le hd 2
  have hdist : (Metric.infDist x (frontier (AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L)))⁻¹ ^ 2 ≤ G ^ 2 * (δ ^ 2)⁻¹ := by
    have hh := inv_anti₀ (pow_pos hdpos 2) hdsq
    have he : ((δ / G) ^ 2)⁻¹ = G ^ 2 * (δ ^ 2)⁻¹ := by field_simp
    simpa only [he, inv_pow] using hh
  have hKdist := mul_le_mul_of_nonneg_left hdist hK.le
  have hgrad := ElementaryBarriers.sq_half_sub_le_sq
    (show 0 ≤ c * (X + Y) from mul_nonneg hc.le (add_nonneg hX hY)) (hg t x hx)
  have hAgrad := mul_le_mul_of_nonneg_left hgrad hA.le
  have hxy : 0 ≤ α * X * Y := mul_nonneg (mul_nonneg hα.le hX) hY
  have hlead : α * X ^ 2 + α * Y ^ 2 ≤ A * (c * (X + Y)) ^ 2 / 2 := by
    dsimp only [α] at hxy ⊢
    nlinarith only [hxy, sq_nonneg X, sq_nonneg Y,
      mul_nonneg (mul_nonneg hA.le (sq_nonneg c)) (sq_nonneg X),
      mul_nonneg (mul_nonneg hA.le (sq_nonneg c)) (sq_nonneg Y)]
  have htrace := hΔ t x hx
  change Laplacian.laplacian (V t) x ≤ C * (1 + δ ^ (-s - 2) + Z) at htrace
  change C * (1 + δ ^ (-s - 2)) + K * G ^ 2 * (δ ^ 2)⁻¹ ≤ α * X ^ 2 + D₀ at hdom
  have hE : E ≤ max E 0 := le_max_left _ _
  dsimp only [E] at hE
  linarith only [hdom, hinv, hKdist, hAgrad, hlead, htrace, hE]


/-- The active penalty Hessian on the isometric fibre chart has order four
at inverse-penalty faces. Appendix A. -/
theorem fibre_penalty_hessian_upper (n : ℕ) (L : ℝ) (θ : PhysicalCutoff)
    {a : ℝ} (ha : 0 < a) (J : Finset (Fin (n + 1))) (b : Bool) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L,
      ∀ u : AffineSimplex.Tangent n,
      fderiv ℝ (fderiv ℝ (fun w : AffineSimplex.Tangent n => ∑ i ∈ J,
        (θ.val (a * AffineSimplex.centredChart n L w i) +
          if b then θ.val (a * (AffineSimplex.centredChart n L w i)⁻¹) else 0))) z u u ≤
        C * (1 + if b then ∑ i ∈ J, (AffineSimplex.centredChart n L z i)⁻¹ ^ 4 else 0) * ‖u‖ ^ 2 := by
  obtain ⟨C, hC, hu⟩ := MarginalCollision.internal_penalty_hessian_upper (n + 1) (L + 1) θ ha J b
  refine ⟨C, hC, fun z hz u => ?_⟩
  have hx := fibre_subset_marginal n (by linarith : L < L + 1) hz
  have hP2 := ((MarginalCollision.active_penalty_smooth_convex (n + 1) (L + 1) θ ha J b).1.contDiffAt
    ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds hx)).of_le
      (by norm_num : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  change fderiv ℝ (fderiv ℝ (fun w : AffineSimplex.Tangent n => ∑ i ∈ J,
    (θ.val (a * ((AffineSimplex.Tangent n).subtypeL w + AffineSimplex.centre n L) i) +
      if b then θ.val (a * (((AffineSimplex.Tangent n).subtypeL w + AffineSimplex.centre n L) i)⁻¹) else 0))) z u u ≤ _
  rw [AffineMetricTransport.hessian_comp_affine (AffineSimplex.Tangent n).subtypeL
    (AffineSimplex.centre n L) hP2]
  exact hu _ hx u.val

/-- Combined active tangent radial bound for every allowed penalized marginal. Appendix A. Constants are chosen after the fixed length. -/
theorem penalized_marginal_fibre_gradient_lower (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin ((n + 1) + m + 1)))
    {L : ℝ} (hL0 : 0 < L) (hL : L < ((n + 1 + m : ℕ) + 1 : ℝ))
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a) (J : Finset (Fin (n + 1))) (b : Bool) :
    let V := fun z : AffineSimplex.Tangent n =>
      p.val.1 * ∑ i ∈ J, (θ.val (a * AffineSimplex.centredChart n L z i) +
        if b then θ.val (a * (AffineSimplex.centredChart n L z i)⁻¹) else 0) -
      Real.log (∫ y : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n + 1) m σ (AffineSimplex.centredChart n L z, y)).toReal)
    ∃ α C : ℝ, 0 < α ∧ 0 < C ∧
      ∀ z ∈ AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L,
      α * ((⨅ i, AffineSimplex.centredChart n L z i) ^ (-p.val.2 - 1) +
        if b then ∑ i ∈ J, (AffineSimplex.centredChart n L z i)⁻¹ ^ 3 else 0) - C ≤ ‖gradient V z‖ := by
  intro V
  obtain ⟨R₀, hR₀s, hR₀c, he⟩ := marginal_fibre_barrier p n m σ hL
  let P := fun z : AffineSimplex.Tangent n => ∑ i ∈ J, θ.val (a * AffineSimplex.centredChart n L z i)
  let R := fun z => R₀ z + p.val.1 * P z
  have hPs : ContDiffOn ℝ ∞ P
      (AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L) := by
    simpa only [Bool.false_eq_true, ↓reduceIte, add_zero] using fibre_penalty_smooth n L θ ha J false
  have hPc : ConvexOn ℝ (AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L) P := by
    simpa only [Bool.false_eq_true, ↓reduceIte, add_zero] using
      convexOn_fibre_pullback n (by linarith : L < L + 1)
        (MarginalCollision.active_penalty_smooth_convex (n + 1) (L + 1) θ ha J false).2
  obtain ⟨α, C, hα, hC, hg⟩ := internal_fibre_gradient_lower (T := Unit) n hL0 p.property.2.1
    (show 0 < 2 * p.val.1 by have := p.property.1; positivity) p.property.1 θ ha J b
    (fun _ => R) (fun _ => V) (norm_nonneg (fderiv ℝ R 0))
    (fun _ => hR₀s.add (contDiffOn_const.mul hPs))
    (fun _ => hR₀c.add (hPc.smul p.property.1.le)) (fun _ => le_rfl) (by
      intro _ z hz
      have hh := he z hz
      dsimp only [V, R, P]
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, add_zero,
        Finset.sum_add_distrib, div_eq_mul_inv] <;> linarith only [hh])
  exact ⟨α, C, hα, hC, hg ()⟩

/-- Tangent trace upper bound for every allowed penalized marginal. Appendix A. -/
theorem penalized_marginal_fibre_laplacian_upper (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin ((n + 1) + m + 1)))
    {L : ℝ} (hL : L < ((n + 1 + m : ℕ) + 1 : ℝ))
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a) (J : Finset (Fin (n + 1))) (b : Bool) :
    let V := fun z : AffineSimplex.Tangent n =>
      p.val.1 * ∑ i ∈ J, (θ.val (a * AffineSimplex.centredChart n L z i) +
        if b then θ.val (a * (AffineSimplex.centredChart n L z i)⁻¹) else 0) -
      Real.log (∫ y : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n + 1) m σ (AffineSimplex.centredChart n L z, y)).toReal)
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L,
      Laplacian.laplacian V z ≤ C * (1 +
        (⨅ i, AffineSimplex.centredChart n L z i) ^ (-p.val.2 - 2) +
        if b then ∑ i ∈ J, (AffineSimplex.centredChart n L z i)⁻¹ ^ 4 else 0) := by
  intro V
  obtain ⟨C₀, hC₀, hu⟩ := marginal_fibre_hessian_upper p n m σ hL
  obtain ⟨Cp, hCp, hp⟩ := fibre_penalty_hessian_upper n L θ ha J b
  let C := n * (C₀ + p.val.1 * Cp) + 1
  have hC : 0 < C := by dsimp only [C]; have := p.property.1; positivity
  refine ⟨C, hC, fun z hz => ?_⟩
  let P := fun w : AffineSimplex.Tangent n => ∑ i ∈ J,
    (θ.val (a * AffineSimplex.centredChart n L w i) +
      if b then θ.val (a * (AffineSimplex.centredChart n L w i)⁻¹) else 0)
  let W := fun w : AffineSimplex.Tangent n => -Real.log (∫ y : EuclideanSpace ℝ (Fin m),
    (ProperMarginalChart.chartDensity p (n + 1) m σ (AffineSimplex.centredChart n L w, y)).toReal)
  let X := (⨅ i, AffineSimplex.centredChart n L z i) ^ (-p.val.2 - 2)
  let Y := if b then ∑ i ∈ J, (AffineSimplex.centredChart n L z i)⁻¹ ^ 4 else 0
  have hX : 0 ≤ X := by
    obtain ⟨i, hi⟩ := ElementaryBarriers.exists_iInf_eq_apply (fun i => AffineSimplex.centredChart n L z i)
    dsimp only [X]; rw [hi]; exact Real.rpow_nonneg (hz.1 i).le _
  have hY : 0 ≤ Y := by
    cases b
    · exact le_rfl
    · exact Finset.sum_nonneg fun i _ => pow_nonneg (inv_nonneg.mpr (hz.1 i).le) _
  have hP2 : ContDiffAt ℝ 2 P z :=
    ((fibre_penalty_smooth n L θ ha J b).contDiffAt ((fibre_isOpen n L).mem_nhds hz)).of_le (by simp)
  have hW2 : ContDiffAt ℝ 2 W z :=
    ((marginal_fibre_smooth p n m σ hL).contDiffAt ((fibre_isOpen n L).mem_nhds hz)).of_le (by simp)
  have hH (u : AffineSimplex.Tangent n) : fderiv ℝ (fderiv ℝ V) z u u ≤
      (C₀ + p.val.1 * Cp) * (1 + X + Y) * ‖u‖ ^ 2 := by
    change fderiv ℝ (fderiv ℝ (fun w => p.val.1 * P w + W w)) z u u ≤ _
    have hadd := PhysicalCollision.internal_hessian_add (hP2.const_smul p.val.1) hW2 u u
    simp only [smul_eq_mul] at hadd
    rw [hadd, PhysicalCollision.internal_hessian_const_mul hP2]
    have h₀ := hu z hz u
    have h₁ := mul_le_mul_of_nonneg_left (hp z hz u) p.property.1.le
    have hcross₀ : 0 ≤ C₀ * Y * ‖u‖ ^ 2 := by positivity
    have hcross₁ : 0 ≤ p.val.1 * Cp * X * ‖u‖ ^ 2 := by have := p.property.1; positivity
    change _ ≤ C₀ * (1 + X) * ‖u‖ ^ 2 at h₀
    change p.val.1 * _ ≤ p.val.1 * (Cp * (1 + Y) * ‖u‖ ^ 2) at h₁
    nlinarith only [h₀, h₁, hcross₀, hcross₁]
  have ht := PhysicalCollision.internal_laplacian_le V z _ hH
  simp only [AffineSimplex.finrank_tangent] at ht
  apply ht.trans
  change _ ≤ C * (1 + X + Y)
  dsimp only [C]
  nlinarith only [hX, hY]

/-- Every allowed penalized fixed-length marginal satisfies the amplified
intrinsic collision criterion. Appendix A. -/
theorem penalized_marginal_fibre_collision (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin ((n + 1) + m + 1)))
    {L : ℝ} (hL0 : 0 < L) (hL : L < ((n + 1 + m : ℕ) + 1 : ℝ))
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a) (J : Finset (Fin (n + 1))) (b : Bool) :
    let Ω := AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L
    let V := fun z : AffineSimplex.Tangent n =>
      p.val.1 * ∑ i ∈ J, (θ.val (a * AffineSimplex.centredChart n L z i) +
        if b then θ.val (a * (AffineSimplex.centredChart n L z i)⁻¹) else 0) -
      Real.log (∫ y : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n + 1) m σ (AffineSimplex.centredChart n L z, y)).toReal)
    ∀ A K : ℝ, 0 < A → 0 < K → ∃ D : ℝ, 0 ≤ D ∧ ∀ z ∈ Ω,
      K * (Metric.infDist z (frontier Ω))⁻¹ ^ 2 - D ≤
        A * ‖gradient V z‖ ^ 2 - Laplacian.laplacian V z := by
  intro Ω V
  obtain ⟨c, Cg, hc, hCg, hg⟩ := penalized_marginal_fibre_gradient_lower p n m σ hL0 hL θ ha J b
  obtain ⟨CΔ, hCΔ, hΔ⟩ := penalized_marginal_fibre_laplacian_upper p n m σ hL θ ha J b
  let C := max Cg CΔ
  have hC : 0 < C := lt_of_lt_of_le hCg (le_max_left _ _)
  have hh := internal_fibre_mixed_collision (T := Unit) n hn L p.property.2.1 J b
    (fun _ => V) hc hC (fun _ z hz => (sub_le_sub_left (le_max_left Cg CΔ) _).trans (hg z hz)) (by
      intro _ z hz
      apply (hΔ z hz).trans
      apply mul_le_mul_of_nonneg_right (le_max_right Cg CΔ)
      have hpow : 0 ≤ (⨅ i, AffineSimplex.centredChart n L z i) ^ (-p.val.2 - 2) := by
        obtain ⟨i, hi⟩ := ElementaryBarriers.exists_iInf_eq_apply (fun i => AffineSimplex.centredChart n L z i)
        rw [hi]; exact Real.rpow_nonneg (hz.1 i).le _
      have hsum : 0 ≤ if b then ∑ i ∈ J, (AffineSimplex.centredChart n L z i)⁻¹ ^ 4 else 0 := by
        cases b
        · exact le_rfl
        · exact Finset.sum_nonneg fun i _ => pow_nonneg (inv_nonneg.mpr (hz.1 i).le) _
      linarith)
  intro A K hA hK
  obtain ⟨D, hD, hd⟩ := hh A K hA hK
  exact ⟨D, hD, hd ()⟩

/-- Internal fixed-exterior envelope for any realization of the physical endpoint. Only equality on the open physical fibre is needed. -/
theorem internal_fixed_exterior_hessian_upper (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin ((n + 1) + m + 1))) {L : ℝ}
    (y : EuclideanSpace ℝ (Fin (m + 1))) (hy : ∀ j, 0 < y j)
    (hcompat : L + ∑ j, y j = ((n + 1 + m : ℕ) + 1 : ℝ))
    (K : AffineSimplex.Tangent n → ℝ)
    (hK : ∀ w (hw : w ∈ AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L),
      K w = physicalAmbientGapEnergy p (n + 1 + m).succPNat
        ⟨RetainedSimplex.assemble (n + 1) m σ (AffineSimplex.centredChart n L w) y,
          PhysicalEnergy.simplex_subset_ambient _ _ (by
            have hh := assemble_fixed_exterior_mem n m σ y hy hcompat hw
            rw [AffineSimplex.massSimplex_physical] at hh
            exact hh)⟩) :
    ∃ C : ℝ, 0 < C ∧ ∀ w ∈ AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L,
      ∀ u : AffineSimplex.Tangent n,
      fderiv ℝ (fderiv ℝ (fun w => p.val.1 * K w)) w u u ≤
        C * (1 + (⨅ i, AffineSimplex.centredChart n L w i) ^ (-p.val.2 - 2)) * ‖u‖ ^ 2 := by
  let N := (n + 1 + m).succPNat
  let E := EuclideanSpace ℝ (Fin (n + 1))
  let F := EuclideanSpace ℝ (Fin (m + 1))
  let H := EuclideanSpace ℝ (Fin ((n + 1) + m + 1))
  let B : AffineSimplex.Tangent n →L[ℝ] H :=
    LinearMap.toContinuousLinearMap
      ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ).toLinearEquiv.toLinearMap.comp
        ((RetainedSimplex.join (n + 1) (m + 1)).toLinearMap.comp
          ((LinearMap.inl ℝ E F).comp (AffineSimplex.Tangent n).subtype)))
  let v : H := RetainedSimplex.assemble (n + 1) m σ (AffineSimplex.centre n L) y
  have hF (w : AffineSimplex.Tangent n) : B w + v =
      RetainedSimplex.assemble (n + 1) m σ (AffineSimplex.centredChart n L w) y := by
    change RetainedSimplex.assemble (n + 1) m σ w.val 0 +
      RetainedSimplex.assemble (n + 1) m σ (AffineSimplex.centre n L) y = _
    simp only [RetainedSimplex.assemble, ← map_add]
    congr 1
    rw [← (RetainedSimplex.join (n + 1) (m + 1)).map_add]
    congr 1
    exact Prod.ext rfl (zero_add y)
  obtain ⟨U, hUs, hUv, _⟩ := MarginalHessian.physical_energy_tensors p N
  obtain ⟨C₀, hC₀, hbound⟩ := MarginalCollision.internal_physical_hessian_envelope p N
  let S := ∑ j, (y j) ^ (-p.val.2 - 2)
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => Real.rpow_nonneg (hy j).le _
  let C := C₀ * ((n + 1 : ℕ) + S + 1) * (‖B‖ ^ 2 + 1)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, fun w hw u => ?_⟩
  have hmem := assemble_fixed_exterior_mem n m σ y hy hcompat hw
  rw [AffineSimplex.massSimplex_physical] at hmem
  have hambient := PhysicalEnergy.simplex_subset_ambient N _ hmem
  have hU2 := (hUs.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hambient)).of_le
    (by norm_num : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  have hnear : (fun z => p.val.1 * K z) =ᶠ[𝓝 w] fun z => U (B z + v) := by
    filter_upwards [(fibre_isOpen n L).mem_nhds hw] with z hz
    rw [hF, hK z hz]
    exact (hUv ⟨_, PhysicalEnergy.simplex_subset_ambient _ _ (by
      have hh := assemble_fixed_exterior_mem n m σ y hy hcompat hz
      rw [AffineSimplex.massSimplex_physical] at hh
      exact hh)⟩).symm
  rw [hnear.fderiv.fderiv_eq]
  have hU2' : ContDiffAt ℝ 2 U (B w + v) := by rwa [hF]
  rw [AffineMetricTransport.hessian_comp_affine B v hU2']
  have hh := hbound U hUv _ hmem (B u)
  have hsum : (∑ j, (RetainedSimplex.assemble (n + 1) m σ
      (AffineSimplex.centredChart n L w) y j) ^ (-p.val.2 - 2)) =
      (∑ i, (AffineSimplex.centredChart n L w i) ^ (-p.val.2 - 2)) + S := by
    change (∑ j, (RetainedSimplex.join (n + 1) (m + 1)
      (AffineSimplex.centredChart n L w, y) (σ.symm j)) ^ (-p.val.2 - 2)) = _
    have he := σ.symm.sum_comp (fun j =>
      (RetainedSimplex.join (n + 1) (m + 1) (AffineSimplex.centredChart n L w, y) j) ^ (-p.val.2 - 2))
    rw [he]
    change (∑ j : Fin ((n + 1) + (m + 1)),
      (RetainedSimplex.join (n + 1) (m + 1) (AffineSimplex.centredChart n L w, y) j) ^ (-p.val.2 - 2)) = _
    rw [Fin.sum_univ_add]
    simp only [RetainedSimplex.join_left, RetainedSimplex.join_right]
    rfl
  dsimp only [N, Nat.succPNat_coe] at hh
  rw [hsum] at hh
  rw [hF]
  let δ := ⨅ i, AffineSimplex.centredChart n L w i
  obtain ⟨i, hi⟩ := ElementaryBarriers.exists_iInf_eq_apply (fun i => AffineSimplex.centredChart n L w i)
  have hδ : 0 < δ := by dsimp only [δ]; rw [hi]; exact hw.1 i
  have hp : 0 ≤ δ ^ (-p.val.2 - 2) := Real.rpow_nonneg hδ.le _
  have hactive : (∑ i, (AffineSimplex.centredChart n L w i) ^ (-p.val.2 - 2)) ≤
      (n + 1 : ℕ) * δ ^ (-p.val.2 - 2) := by
    calc
      _ ≤ ∑ _i : Fin (n + 1), δ ^ (-p.val.2 - 2) := by
        apply Finset.sum_le_sum
        intro j _
        exact Real.rpow_le_rpow_of_nonpos hδ (ciInf_le (Finite.bddBelow_range _) j)
          (by linarith [p.property.2.1])
      _ = _ := by simp
  have hn : ‖B u‖ ^ 2 ≤ ‖B‖ ^ 2 * ‖u‖ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg (B u)) (B.le_opNorm u) 2
  have hcoef : C₀ * ((∑ i, (AffineSimplex.centredChart n L w i) ^ (-p.val.2 - 2)) + S) ≤
      C₀ * ((n + 1 : ℕ) + S + 1) * (1 + δ ^ (-p.val.2 - 2)) := by
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hC₀.le
    nlinarith only [hactive, hp, hS, mul_nonneg hS hp,
      show (0 : ℝ) ≤ (n + 1 : ℕ) by positivity]
  have hnn : 0 ≤ C₀ * ((∑ i, (AffineSimplex.centredChart n L w i) ^ (-p.val.2 - 2)) + S) := by
    apply mul_nonneg hC₀.le
    exact add_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hw.1 i).le _) hS
  apply hh.trans
  calc
    _ ≤ (C₀ * ((n + 1 : ℕ) + S + 1) * (1 + δ ^ (-p.val.2 - 2))) *
        (‖B‖ ^ 2 * ‖u‖ ^ 2) := mul_le_mul hcoef hn (sq_nonneg _) (by positivity)
    _ ≤ C * (1 + δ ^ (-p.val.2 - 2)) * ‖u‖ ^ 2 := by
      dsimp only [C]
      nlinarith only [show 0 ≤ C₀ * ((n + 1 : ℕ) + S + 1) *
        (1 + δ ^ (-p.val.2 - 2)) * ‖u‖ ^ 2 by positivity]

/-- Internal derivative bound for a fixed term plus a convex segment. -/
theorem internal_segment_derivative_norm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {P Y Z : E → ℝ} {x : E}
    (hP : DifferentiableAt ℝ P x) (hY : DifferentiableAt ℝ Y x)
    (hZ : DifferentiableAt ℝ Z x) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖fderiv ℝ (fun w => P w + (1 - t) * Y w + t * Z w) x‖ ≤
      ‖fderiv ℝ P x‖ + ‖fderiv ℝ Y x‖ + ‖fderiv ℝ Z x‖ := by
  have h1t : 0 ≤ 1 - t := by linarith only [ht.2]
  have hd : HasFDerivAt (fun w => P w + (1 - t) * Y w + t * Z w)
      ((fderiv ℝ P x + (1 - t) • fderiv ℝ Y x) + t • fderiv ℝ Z x) x :=
    (hP.hasFDerivAt.add (hY.hasFDerivAt.const_mul (1 - t))).add (hZ.hasFDerivAt.const_mul t)
  rw [hd.fderiv]
  have hYbound : ‖(1 - t) • fderiv ℝ Y x‖ ≤ ‖fderiv ℝ Y x‖ := by
    rw [norm_smul, Real.norm_of_nonneg h1t]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith only [ht.1])
  have hZbound : ‖t • fderiv ℝ Z x‖ ≤ ‖fderiv ℝ Z x‖ := by
    rw [norm_smul, Real.norm_of_nonneg ht.1]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add le_rfl hYbound)) hZbound)

/-- Internal second derivative identity for a fixed term and a segment. -/
theorem internal_segment_hessian {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {P Y Z : E → ℝ} {x : E}
    (hP : ContDiffAt ℝ 2 P x) (hY : ContDiffAt ℝ 2 Y x)
    (hZ : ContDiffAt ℝ 2 Z x) (t : ℝ) (u : E) :
    fderiv ℝ (fderiv ℝ (fun w => P w + (1 - t) * Y w + t * Z w)) x u u =
      fderiv ℝ (fderiv ℝ P) x u u +
        (1 - t) * fderiv ℝ (fderiv ℝ Y) x u u + t * fderiv ℝ (fderiv ℝ Z) x u u := by
  have h₁ := PhysicalCollision.internal_hessian_add hP (hY.const_smul (1 - t)) u u
  have h₂ := PhysicalCollision.internal_hessian_add (hP.add (hY.const_smul (1 - t)))
    (hZ.const_smul t) u u
  simp only [smul_eq_mul] at h₁ h₂
  rw [h₂, h₁, PhysicalCollision.internal_hessian_const_mul hY,
    PhysicalCollision.internal_hessian_const_mul hZ]

/-- Internal common-centre estimate for interpolants with a common active
barrier. The constants precede the interpolation parameter. -/
theorem internal_interpolation_gradient_lower (p : Parameters) (n : ℕ)
    {L : ℝ} (hL : 0 < L) (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (J : Finset (Fin (n + 1))) (b : Bool) (Ky Kz : AffineSimplex.Tangent n → ℝ)
    (hKys : ContDiffOn ℝ ∞ Ky (AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L))
    (hKzs : ContDiffOn ℝ ∞ Kz (AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L))
    (hKyc : ConvexOn ℝ (AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L)
      (fun w => Ky w - 2 * ∑ i, (AffineSimplex.centredChart n L w i) ^ (-p.val.2)))
    (hKzc : ConvexOn ℝ (AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L)
      (fun w => Kz w - 2 * ∑ i, (AffineSimplex.centredChart n L w i) ^ (-p.val.2))) :
    let P := fun w : AffineSimplex.Tangent n => ∑ i ∈ J,
      (θ.val (a * AffineSimplex.centredChart n L w i) +
        if b then θ.val (a * (AffineSimplex.centredChart n L w i)⁻¹) else 0)
    ∃ α C : ℝ, 0 < α ∧ 0 < C ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ w ∈ AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L,
      α * ((⨅ i, AffineSimplex.centredChart n L w i) ^ (-p.val.2 - 1) +
        if b then ∑ i ∈ J, (AffineSimplex.centredChart n L w i)⁻¹ ^ 3 else 0) - C ≤
      ‖gradient (fun w => p.val.1 * (P w + (1 - t) * Ky w + t * Kz w)) w‖ := by
  intro P
  let Ω := AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L
  let B := fun w : AffineSimplex.Tangent n => 2 * ∑ i, (AffineSimplex.centredChart n L w i) ^ (-p.val.2)
  let Y := fun w => p.val.1 * (Ky w - B w)
  let Z := fun w => p.val.1 * (Kz w - B w)
  let Q := fun w : AffineSimplex.Tangent n => p.val.1 * ∑ i ∈ J,
    θ.val (a * AffineSimplex.centredChart n L w i)
  let R := fun t : Icc (0 : ℝ) 1 => fun w => Q w + (1 - t.val) * Y w + t.val * Z w
  let V := fun t : Icc (0 : ℝ) 1 => fun w => p.val.1 * (P w + (1 - t.val) * Ky w + t.val * Kz w)
  have hBs := (fibre_barrier_smooth_convex n L p.property.2.1).1
  have hYs : ContDiffOn ℝ ∞ Y Ω := contDiffOn_const.mul (hKys.sub hBs)
  have hZs : ContDiffOn ℝ ∞ Z Ω := contDiffOn_const.mul (hKzs.sub hBs)
  have hQs : ContDiffOn ℝ ∞ Q Ω := by
    have hh := (fibre_penalty_smooth n L θ ha J false).const_smul p.val.1
    simpa only [Q, Ω, Pi.smul_apply, smul_eq_mul, Bool.false_eq_true, ↓reduceIte, add_zero] using hh
  have hQc : ConvexOn ℝ Ω Q := by
    have hh := (convexOn_fibre_pullback n (by linarith : L < L + 1)
      (MarginalCollision.active_penalty_smooth_convex (n + 1) (L + 1) θ ha J false).2).smul p.property.1.le
    simpa only [Q, Ω, Pi.smul_apply, smul_eq_mul, Bool.false_eq_true, ↓reduceIte, add_zero] using hh
  have hzero : (0 : AffineSimplex.Tangent n) ∈ Ω := by
    simpa only [Ω, mem_preimage, AffineSimplex.centredChart, Submodule.coe_zero, zero_add]
      using AffineSimplex.centre_mem_simplex n hL
  have hdQ := (hQs.contDiffAt ((fibre_isOpen n L).mem_nhds hzero)).differentiableAt (by simp)
  have hdY := (hYs.contDiffAt ((fibre_isOpen n L).mem_nhds hzero)).differentiableAt (by simp)
  have hdZ := (hZs.contDiffAt ((fibre_isOpen n L).mem_nhds hzero)).differentiableAt (by simp)
  obtain ⟨α, C, hα, hC, hg⟩ := internal_fibre_gradient_lower n hL p.property.2.1
    (show 0 < 2 * p.val.1 by have := p.property.1; positivity) p.property.1 θ ha J b R V
    (show 0 ≤ ‖fderiv ℝ Q 0‖ + ‖fderiv ℝ Y 0‖ + ‖fderiv ℝ Z 0‖ by positivity)
    (fun t => (hQs.add (contDiffOn_const.mul hYs)).add (contDiffOn_const.mul hZs))
    (fun t => (hQc.add ((hKyc.smul p.property.1.le).smul (by linarith [t.property.2]))).add
      ((hKzc.smul p.property.1.le).smul t.property.1))
    (fun t => internal_segment_derivative_norm hdQ hdY hdZ t.property) (by
      intro t w _
      dsimp only [V, R, Y, Z, Q, B, P]
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, add_zero,
        Finset.sum_add_distrib, ← Finset.mul_sum, div_eq_mul_inv] <;> ring)
  exact ⟨α, C, hα, hC, fun t ht => hg ⟨t, ht⟩⟩

/-- Internal interpolation trace estimate with constants uniform in `t`.
The endpoint envelopes concern tangent Hessians, rather than restrictions
of ambient gradient or Laplacian estimates. -/
theorem internal_interpolation_laplacian_upper (p : Parameters) (n : ℕ)
    (L : ℝ) (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (J : Finset (Fin (n + 1))) (b : Bool) (Ky Kz : AffineSimplex.Tangent n → ℝ)
    (hKys : ContDiffOn ℝ ∞ Ky (AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L))
    (hKzs : ContDiffOn ℝ ∞ Kz (AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L))
    {Cy Cz : ℝ} (hCy : 0 < Cy) (hCz : 0 < Cz)
    (hHy : ∀ w ∈ AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L,
      ∀ u : AffineSimplex.Tangent n, fderiv ℝ (fderiv ℝ (fun w => p.val.1 * Ky w)) w u u ≤
        Cy * (1 + (⨅ i, AffineSimplex.centredChart n L w i) ^ (-p.val.2 - 2)) * ‖u‖ ^ 2)
    (hHz : ∀ w ∈ AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L,
      ∀ u : AffineSimplex.Tangent n, fderiv ℝ (fderiv ℝ (fun w => p.val.1 * Kz w)) w u u ≤
        Cz * (1 + (⨅ i, AffineSimplex.centredChart n L w i) ^ (-p.val.2 - 2)) * ‖u‖ ^ 2) :
    let P := fun w : AffineSimplex.Tangent n => ∑ i ∈ J,
      (θ.val (a * AffineSimplex.centredChart n L w i) +
        if b then θ.val (a * (AffineSimplex.centredChart n L w i)⁻¹) else 0)
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ w ∈ AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L,
      Laplacian.laplacian (fun w => p.val.1 * (P w + (1 - t) * Ky w + t * Kz w)) w ≤
        C * (1 + (⨅ i, AffineSimplex.centredChart n L w i) ^ (-p.val.2 - 2) +
          if b then ∑ i ∈ J, (AffineSimplex.centredChart n L w i)⁻¹ ^ 4 else 0) := by
  intro P
  obtain ⟨Cp, hCp, hp⟩ := fibre_penalty_hessian_upper n L θ ha J b
  let C := n * (p.val.1 * Cp + Cy + Cz) + 1
  have hC : 0 < C := by dsimp only [C]; have := p.property.1; positivity
  refine ⟨C, hC, fun t ht w hw => ?_⟩
  let X := (⨅ i, AffineSimplex.centredChart n L w i) ^ (-p.val.2 - 2)
  let Y := if b then ∑ i ∈ J, (AffineSimplex.centredChart n L w i)⁻¹ ^ 4 else 0
  have hX : 0 ≤ X := by
    obtain ⟨i, hi⟩ := ElementaryBarriers.exists_iInf_eq_apply (fun i => AffineSimplex.centredChart n L w i)
    dsimp only [X]; rw [hi]; exact Real.rpow_nonneg (hw.1 i).le _
  have hY : 0 ≤ Y := by
    cases b
    · exact le_rfl
    · exact Finset.sum_nonneg fun i _ => pow_nonneg (inv_nonneg.mpr (hw.1 i).le) _
  have hP2 := ((fibre_penalty_smooth n L θ ha J b).contDiffAt
    ((fibre_isOpen n L).mem_nhds hw)).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  have hKy2 := (hKys.contDiffAt ((fibre_isOpen n L).mem_nhds hw)).of_le
    (by norm_num : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  have hKz2 := (hKzs.contDiffAt ((fibre_isOpen n L).mem_nhds hw)).of_le
    (by norm_num : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  have he : (fun w => p.val.1 * (P w + (1 - t) * Ky w + t * Kz w)) =
      fun w => (p.val.1 * P w) + (1 - t) * (p.val.1 * Ky w) + t * (p.val.1 * Kz w) := by
    funext w; ring
  have hH (u : AffineSimplex.Tangent n) :
      fderiv ℝ (fderiv ℝ (fun w => p.val.1 * (P w + (1 - t) * Ky w + t * Kz w))) w u u ≤
        (p.val.1 * Cp + Cy + Cz) * (1 + X + Y) * ‖u‖ ^ 2 := by
    rw [he, internal_segment_hessian (contDiffAt_const.mul hP2)
      (contDiffAt_const.mul hKy2) (contDiffAt_const.mul hKz2),
      PhysicalCollision.internal_hessian_const_mul hP2]
    have hb₀ := mul_le_mul_of_nonneg_left (hp w hw u) p.property.1.le
    have hb₁ := (mul_le_mul_of_nonneg_left (hHy w hw u)
      (by linarith only [ht.2] : 0 ≤ 1 - t)).trans
        (mul_le_of_le_one_left (by positivity) (by linarith only [ht.1] : 1 - t ≤ 1))
    have hb₂ := (mul_le_mul_of_nonneg_left (hHz w hw u) ht.1).trans
      (mul_le_of_le_one_left (by positivity) ht.2)
    change p.val.1 * _ ≤ p.val.1 * (Cp * (1 + Y) * ‖u‖ ^ 2) at hb₀
    change _ ≤ Cy * (1 + X) * ‖u‖ ^ 2 at hb₁
    change _ ≤ Cz * (1 + X) * ‖u‖ ^ 2 at hb₂
    have hcross₀ : 0 ≤ p.val.1 * Cp * X * ‖u‖ ^ 2 := by have := p.property.1; positivity
    have hcross₁ : 0 ≤ (Cy + Cz) * Y * ‖u‖ ^ 2 := by positivity
    nlinarith only [hb₀, hb₁, hb₂, hcross₀, hcross₁]
  have hh := PhysicalCollision.internal_laplacian_le _ w _ hH
  simp only [AffineSimplex.finrank_tangent] at hh
  apply hh.trans
  change _ ≤ C * (1 + X + Y)
  dsimp only [C]
  nlinarith only [hX, hY]

/-- See Appendix A of the paper: compatible interpolants have smoothness, strict
curvature, finite positive normalization and the amplified intrinsic collision
criterion, with all collision constants uniform over `0 ≤ t ≤ 1`.
The endpoint realizations agree with the physical energies. -/
theorem compatible_interpolation_collision_regular (p : Parameters) (n m r : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin ((n + 1) + m + 1)))
    (τ : Equiv.Perm (Fin ((n + 1) + r + 1))) {L : ℝ} (hL : 0 < L)
    (y : EuclideanSpace ℝ (Fin (m + 1))) (hy : ∀ j, 0 < y j)
    (z : EuclideanSpace ℝ (Fin (r + 1))) (hz : ∀ j, 0 < z j)
    (hcompatY : L + ∑ j, y j = ((n + 1 + m : ℕ) + 1 : ℝ))
    (hcompatZ : L + ∑ j, z j = ((n + 1 + r : ℕ) + 1 : ℝ))
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (J : Finset (Fin (n + 1))) (b : Bool) :
    let Ω := AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L
    let P := fun w : AffineSimplex.Tangent n => ∑ i ∈ J,
      (θ.val (a * AffineSimplex.centredChart n L w i) +
        if b then θ.val (a * (AffineSimplex.centredChart n L w i)⁻¹) else 0)
    ∃ Ky Kz : AffineSimplex.Tangent n → ℝ,
      (∀ w (hw : w ∈ Ω), Ky w = physicalAmbientGapEnergy p (n + 1 + m).succPNat
        ⟨RetainedSimplex.assemble (n + 1) m σ (AffineSimplex.centredChart n L w) y,
          PhysicalEnergy.simplex_subset_ambient _ _ (by
            have hh := assemble_fixed_exterior_mem n m σ y hy hcompatY hw
            rw [AffineSimplex.massSimplex_physical] at hh
            exact hh)⟩) ∧
      (∀ w (hw : w ∈ Ω), Kz w = physicalAmbientGapEnergy p (n + 1 + r).succPNat
        ⟨RetainedSimplex.assemble (n + 1) r τ (AffineSimplex.centredChart n L w) z,
          PhysicalEnergy.simplex_subset_ambient _ _ (by
            have hh := assemble_fixed_exterior_mem n r τ z hz hcompatZ hw
            rw [AffineSimplex.massSimplex_physical] at hh
            exact hh)⟩) ∧
      (∀ A K : ℝ, 0 < A → 0 < K → ∃ D : ℝ, 0 ≤ D ∧
        ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Ω,
          K * (Metric.infDist w (frontier Ω))⁻¹ ^ 2 - D ≤
            A * ‖gradient (fun w => p.val.1 * (P w + (1 - t) * Ky w + t * Kz w)) w‖ ^ 2 -
              Laplacian.laplacian (fun w => p.val.1 * (P w + (1 - t) * Ky w + t * Kz w)) w) ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        let V := fun w => p.val.1 * (P w + (1 - t) * Ky w + t * Kz w)
        ContDiffOn ℝ ∞ V Ω ∧
        (∀ w ∈ Ω, ∀ u : AffineSimplex.Tangent n,
          (2 * p.val.1 * (p.val.2 * (p.val.2 + 1)) * L ^ (-p.val.2 - 2)) * ‖u‖ ^ 2 ≤
            fderiv ℝ (fderiv ℝ V) w u u) ∧
        ConvexOn ℝ Ω (fun w => V w - 2 * p.val.1 *
          ∑ i, (AffineSimplex.centredChart n L w i) ^ (-p.val.2)) ∧
        (0 < ∫⁻ w in Ω, ENNReal.ofReal (Real.exp (-V w))) ∧
          (∫⁻ w in Ω, ENNReal.ofReal (Real.exp (-V w))) < ⊤ := by
  intro Ω P
  obtain ⟨Ky, hKys, hKy, hKyc⟩ := fixed_exterior_barrier p n m σ y hy hcompatY
  obtain ⟨Kz, hKzs, hKz, hKzc⟩ := fixed_exterior_barrier p n r τ z hz hcompatZ
  have hPs := fibre_penalty_smooth n L θ ha J b
  have hPc := convexOn_fibre_pullback n (show L < L + 1 by linarith)
    (MarginalCollision.active_penalty_smooth_convex (n + 1) (L + 1) θ ha J b).2
  obtain ⟨hBs, hBc⟩ := fibre_barrier_smooth_convex n L p.property.2.1
  obtain ⟨Cy, hCy, hHy⟩ := internal_fixed_exterior_hessian_upper p n m σ y hy hcompatY Ky hKy
  obtain ⟨Cz, hCz, hHz⟩ := internal_fixed_exterior_hessian_upper p n r τ z hz hcompatZ Kz hKz
  obtain ⟨c, Cg, hc, hCg, hg⟩ := internal_interpolation_gradient_lower p n hL θ ha J b Ky Kz hKys hKzs hKyc hKzc
  obtain ⟨CΔ, hCΔ, hΔ⟩ := internal_interpolation_laplacian_upper p n L θ ha J b Ky Kz hKys hKzs hCy hCz hHy hHz
  let C := max Cg CΔ
  have hC : 0 < C := lt_of_lt_of_le hCg (le_max_left _ _)
  have hcoll := internal_fibre_mixed_collision n hn L p.property.2.1 J b
    (fun t : Icc (0 : ℝ) 1 => fun w => p.val.1 * (P w + (1 - t.val) * Ky w + t.val * Kz w)) hc hC
    (fun t w hw => (sub_le_sub_left (le_max_left Cg CΔ) _).trans (hg t.val t.property w hw)) (by
      intro t w hw
      apply (hΔ t.val t.property w hw).trans
      apply mul_le_mul_of_nonneg_right (le_max_right Cg CΔ)
      have hpow : 0 ≤ (⨅ i, AffineSimplex.centredChart n L w i) ^ (-p.val.2 - 2) := by
        obtain ⟨i, hi⟩ := ElementaryBarriers.exists_iInf_eq_apply (fun i => AffineSimplex.centredChart n L w i)
        rw [hi]; exact Real.rpow_nonneg (hw.1 i).le _
      have hsum : 0 ≤ if b then ∑ i ∈ J, (AffineSimplex.centredChart n L w i)⁻¹ ^ 4 else 0 := by
        cases b
        · exact le_rfl
        · exact Finset.sum_nonneg fun i _ => pow_nonneg (inv_nonneg.mpr (hw.1 i).le) _
      linarith)
  refine ⟨Ky, Kz, hKy, hKz, ?_, fun t ht => ?_⟩
  · intro A K hA hK
    obtain ⟨D, hD, hd⟩ := hcoll A K hA hK
    exact ⟨D, hD, fun t ht => hd ⟨t, ht⟩⟩
  · intro V
    have hVs : ContDiffOn ℝ ∞ V Ω := contDiffOn_const.mul
      ((hPs.add (contDiffOn_const.mul hKys)).add (contDiffOn_const.mul hKzs))
    have hRc := (hPc.add ((hKyc.smul (by linarith only [ht.2] : 0 ≤ 1 - t)).add
      (hKzc.smul ht.1))).smul p.property.1.le
    have hVc : ConvexOn ℝ Ω (fun w => V w - 2 * p.val.1 *
        ∑ i, (AffineSimplex.centredChart n L w i) ^ (-p.val.2)) := by
      apply hRc.congr
      intro w _
      dsimp only [V, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hVconvex : ConvexOn ℝ Ω V := by
      apply (hVc.add (hBc.smul p.property.1.le)).congr
      intro w _
      dsimp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hne : Ω.Nonempty := by
      refine ⟨0, ?_⟩
      change AffineSimplex.centredChart n L 0 ∈ AffineSimplex.massSimplex n L
      simpa only [AffineSimplex.centredChart, Submodule.coe_zero, zero_add] using
        AffineSimplex.centre_mem_simplex n hL
    have hcurv := internal_fibre_strict_curvature n hL p.property.2.1
      (mul_pos (by norm_num : (0 : ℝ) < 2) p.property.1) hVs hVc
    exact ⟨hVs, hcurv, hVc, internal_convex_normalizer (fibre_isOpen n L)
      (fibre_isBounded n L) hne hVconvex hVs.continuousOn⟩

/-- The penalized fibre potential is the logarithm of the actual penalized
marginal density, with retained labels embedded by the existing chart. Appendix A. -/
theorem penalized_marginal_fibre_density (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin ((n + 1) + m + 1)))
    {L : ℝ} (hL : L < ((n + 1 + m : ℕ) + 1 : ℝ))
    (θ : PhysicalCutoff) (a : ℝ) (J : Finset (Fin (n + 1))) (b : Bool)
    {z : AffineSimplex.Tangent n}
    (hz : z ∈ AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L) :
    ENNReal.ofReal (Real.exp (-(p.val.1 * ∑ i ∈ J,
      (θ.val (a * AffineSimplex.centredChart n L z i) +
        if b then θ.val (a * (AffineSimplex.centredChart n L z i)⁻¹) else 0) -
      Real.log (∫ y : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n + 1) m σ (AffineSimplex.centredChart n L z, y)).toReal)))) =
      AffineFibre.fibreMass volume (ProperMarginalChart.penalizedChartDensity p (n + 1) m σ θ a
        (J.image (fun i => σ (i.castAdd m).castSucc)) b) (AffineSimplex.centredChart n L z) := by
  classical
  let x := AffineSimplex.centredChart n L z
  let J' := J.image (fun i => σ (i.castAdd m).castSucc)
  have hJ : ∀ i ∈ J', ∃ j : Fin (n + 1), i = σ (j.castAdd m).castSucc := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨j, rfl⟩
  have hinj : Function.Injective (fun i : Fin (n + 1) => σ (i.castAdd m).castSucc) := by
    intro i j hij
    have hh := congrArg (fun k : Fin ((n + 1) + m + 1) => k.val) (σ.injective hij)
    exact Fin.ext hh
  have hsum : (∑ i ∈ J', (θ.val (a * RetainedSimplex.chart (n + 1) m
      ((n + 1 + m : ℕ) + 1) σ (x, 0) i) + if b then θ.val
      (a * (RetainedSimplex.chart (n + 1) m ((n + 1 + m : ℕ) + 1) σ (x, 0) i)⁻¹) else 0)) =
      ∑ i ∈ J, (θ.val (a * x i) + if b then θ.val (a * (x i)⁻¹) else 0) := by
    rw [Finset.sum_image (fun i _ j _ hij => hinj hij)]
    simp only [RetainedSimplex.chart_retained]
  change _ = ∫⁻ y, ProperMarginalChart.penalizedChartDensity p (n + 1) m σ θ a J' b (x, y)
  simp_rw [ProperMarginalChart.penalizedChartDensity_eq_mul p (n + 1) m σ θ a J' b hJ, hsum]
  rw [lintegral_const_mul _ (show Measurable (fun y : EuclideanSpace ℝ (Fin m) =>
    ProperMarginalChart.chartDensity p (n + 1) m σ (x, y)) from
      (ProperMarginalChart.measurable_chartDensity p (n + 1) m σ).comp measurable_prodMk_left)]
  have he : -(p.val.1 * ∑ i ∈ J, (θ.val (a * x i) +
      if b then θ.val (a * (x i)⁻¹) else 0) -
      Real.log (∫ y : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n + 1) m σ (x,y)).toReal)) =
      -p.val.1 * (∑ i ∈ J, (θ.val (a * x i) +
        if b then θ.val (a * (x i)⁻¹) else 0)) +
      -(-Real.log (∫ y : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n + 1) m σ (x,y)).toReal)) := by ring
  rw [he, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le,
    marginal_fibre_density p n m σ hL hz]

/-- Every allowed penalized marginal has positive finite Hausdorff fibre
mass at every interior length. Appendix A. -/
theorem penalized_marginal_simplex_normalizer (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin ((n + 1) + m + 1)))
    {L : ℝ} (hL0 : 0 < L) (hL : L < ((n + 1 + m : ℕ) + 1 : ℝ))
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a) (J : Finset (Fin (n + 1))) (b : Bool) :
    let w := AffineFibre.fibreMass volume (ProperMarginalChart.penalizedChartDensity p (n + 1) m σ θ a
      (J.image (fun i => σ (i.castAdd m).castSucc)) b)
    0 < ∫⁻ x, w x ∂AffineSimplex.simplexVolume n L ∧
      (∫⁻ x, w x ∂AffineSimplex.simplexVolume n L) < ⊤ := by
  classical
  intro w
  rw [AffineSimplex.lintegral_centredChart]
  have he : (∫⁻ z in AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L,
      w (AffineSimplex.centredChart n L z)) =
      ∫⁻ z in AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L,
        ENNReal.ofReal (Real.exp (-(p.val.1 * ∑ i ∈ J,
          (θ.val (a * AffineSimplex.centredChart n L z i) +
            if b then θ.val (a * (AffineSimplex.centredChart n L z i)⁻¹) else 0) -
          Real.log (∫ y : EuclideanSpace ℝ (Fin m),
            (ProperMarginalChart.chartDensity p (n + 1) m σ (AffineSimplex.centredChart n L z, y)).toReal)))) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (fibre_isOpen n L).measurableSet] with z hz
    exact (penalized_marginal_fibre_density p n m σ hL θ a J b hz).symm
  rw [he]
  exact penalized_marginal_fibre_normalizer p n m σ hL0 hL θ ha J b

/-- The coarea conditional-density formula for every allowed penalized
marginal, at every interior length, with the exact constant Jacobian. Appendix A. -/
theorem penalized_marginal_length_disintegration (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin ((n + 1) + m + 1)))
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a) (J : Finset (Fin (n + 1))) (b : Bool) :
    let I := Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)
    let w := AffineFibre.fibreMass volume (ProperMarginalChart.penalizedChartDensity p (n + 1) m σ θ a
      (J.image (fun i => σ (i.castAdd m).castSucc)) b)
    ∃ (h0 : ∀ L : I, (∫⁻ x, w x ∂AffineSimplex.simplexVolume n L.val) ≠ 0)
      (ht : ∀ L : I, (∫⁻ x, w x ∂AffineSimplex.simplexVolume n L.val) ≠ ⊤),
      ∀ f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞, Measurable f →
        ∫⁻ x in {x | (∑ i, x i) ∈ I} ∩ {x | ∀ i, 0 < x i}, w x * f x =
          (ENNReal.ofReal (Real.sqrt (n + 1)))⁻¹ *
            ∫⁻ L : I, (∫⁻ x, w x ∂AffineSimplex.simplexVolume n L.val) *
              (∫⁻ x, f x ∂AffineFibre.normalizedMeasure
                (AffineSimplex.simplexVolume n L.val) w (h0 L) (ht L))
              ∂(volume.comap ((↑) : I → ℝ)) := by
  classical
  intro I w
  have hm (L : I) := penalized_marginal_simplex_normalizer p n m σ L.property.1 L.property.2 θ ha J b
  let h0 := fun L : I => (hm L).1.ne'
  let ht := fun L : I => (hm L).2.ne
  refine ⟨h0, ht, fun f hf => ?_⟩
  exact AffineFibre.SumChart.lintegral_simplex_disintegration n measurableSet_Ioo
    (AffineFibre.measurable_fibreMass volume (ProperMarginalChart.measurable_penalizedChartDensity
      p (n + 1) m σ θ ha _ b)) h0 ht hf

/-- The full analytic conclusion in an orthonormal chart: H¹ covariance
representation by the differentiated scalar solution, unique tangent L²
solutions, and unique H⁻¹ solutions on the finite-energy domain.
This predicate only groups conclusions. All laws, forms, gradients and vector
domains are the existing ones. See Appendix A of the paper. -/
def EuclideanWellPosed {d : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin d))} {ρ : Measure (EuclideanSpace ℝ (Fin d))}
    {V : EuclideanSpace ℝ (Fin d) → ℝ}
    (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) : Prop :=
    let Q := IntrinsicScalarCore.form hU hB hV
    let J := IntrinsicScalarCore.jet hU hB hV
    let hQ := IntrinsicScalarCore.closed_dirichlet hU hB hV
    (∀ G : ScalarForm.Domain J, ∃ ψ : ScalarForm.Domain J, ∃ u : Fin d → Q.1,
      (∫ x, ScalarForm.value J ψ x ∂ρ) = 0 ∧
      (ψ, @Riesz1.poissonCenter _ _ ρ (IntrinsicScalarCore.probability hV) (ScalarForm.value J G)) ∈
        ScalarForm.neumannGraph J ∧
      WeightedWeakSolution Q (hessianMatrix V) ⊤
        (fun i => DifferentiatedPoisson.coordinateLp i (ScalarForm.deriv J G)) u ∧
      (∀ i, (u i).val = DifferentiatedPoisson.coordinateLp i (ScalarForm.deriv J ψ)) ∧
      ∀ K : ScalarForm.Domain J,
        Integrable (fun x => inner ℝ (ScalarForm.deriv J ψ x) (ScalarForm.deriv J K x)) ρ ∧
        ProbabilityTheory.covariance (ScalarForm.value J G) (ScalarForm.value J K) ρ =
          ∫ x, inner ℝ (ScalarForm.deriv J ψ x) (ScalarForm.deriv J K x) ∂ρ) ∧
    (∀ v : Fin d → Lp ℝ 2 ρ, ∃! u : Fin d → Q.1,
      WeightedWeakSolution Q (hessianMatrix V) ⊤ v u) ∧
    (∀ v : StrongDual ℝ (MatrixEnergy.Vector (ι := Fin d) Q hQ),
      ∃! u : Fin d → Q.1, WeightedFormDomain Q (hessianMatrix V) ⊤ u ∧
        ∀ h : Fin d → Q.1, WeightedFormDomain Q (hessianMatrix V) ⊤ h →
          Integrable (matrixFieldPair (hessianMatrix V) (fun i => (u i).val) (fun i => (h i).val)) ρ ∧
          (∑ i, Q.2 (u i) (h i)) +
            (∫ x, matrixFieldPair (hessianMatrix V) (fun i => (u i).val) (fun i => (h i).val) x ∂ρ) =
              v ((MatrixEnergy.vectorEquiv Q hQ).symm h))

/-- Application of the scalar and vector theory to the conditional laws. -/
theorem internal_euclidean_wellposed {d : ℕ} (hd : 1 ≤ d)
    {U : Set (EuclideanSpace ℝ (Fin d))} {ρ : Measure (EuclideanSpace ℝ (Fin d))}
    {V : EuclideanSpace ℝ (Fin d) → ℝ}
    (hU : IsOpen U) (hB : Bornology.IsBounded U) (hc : Convex ℝ U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) {κ D : ℝ} (hκ : 0 < κ) (hD : 0 ≤ D)
    (hH : ∀ x ∈ U, ∀ u, κ * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x u u)
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹ ^ 2 - D ≤
      ‖gradient V x‖ ^ 2 / 4 - Laplacian.laplacian V x / 2) :
    EuclideanWellPosed hU hB hV := by
  let : NeZero d := ⟨by omega⟩
  unfold EuclideanWellPosed
  intro Q J hQ
  have hM := (IntrinsicScalarCore.supported hU hV).mono (fun x hx =>
    DifferentiatedPoisson.hessian_posSemidef_on hU hV (fun x hx u =>
      (mul_nonneg hκ.le (sq_nonneg ‖u‖)).trans (hH x hx u)) x hx)
  have hlower : ∀ᵐ x ∂ρ, ∀ t ∈ (⊤ : Submodule ℝ (Fin d → ℝ)),
      κ * (∑ i, t i ^ 2) ≤ ∑ i, ∑ j, t i * hessianMatrix V x i j * t j :=
    (IntrinsicScalarCore.supported hU hV).mono (fun x hx t _ =>
      DifferentiatedPoisson.hessian_coordinate_lower hU hV hH x hx t)
  refine ⟨?_, ?_, ?_⟩
  · intro G
    obtain ⟨ψ, u, hmean, hgraph, hweak, hcoord, hcov, _⟩ :=
      DifferentiatedPoisson.exists_differentiated_poisson hU hB hV hd hc hκ hH hD hbar G
    exact ⟨ψ, u, hmean, hgraph, hweak, hcoord, hcov⟩
  · intro v
    obtain ⟨u, hu, huniq, _, _⟩ := AuxiliarySources.l2_sources Q hQ
      (hessianMatrix V) ⊤ hM κ hκ hlower DifferentiatedPoisson.measurable_hessian_entries v
    exact ⟨u, hu, huniq⟩
  · exact AuxiliarySources.hminusOne_sources_frozen Q hQ (hessianMatrix V) ⊤ hM κ hκ hlower
      DifferentiatedPoisson.measurable_hessian_entries

/-- Internal normalization bridge to the Gibbs predicate. -/
theorem internal_normalized_gibbs {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Set E} {V : E → ℝ} (hs : ContDiffOn ℝ ∞ V Ω)
    (h0 : 0 < ∫⁻ x in Ω, ENNReal.ofReal (Real.exp (-V x)))
    (ht : (∫⁻ x in Ω, ENNReal.ofReal (Real.exp (-V x))) < ⊤) :
    IsEuclideanGibbsPotential volume (AffineFibre.normalizedMeasure (volume.restrict Ω)
      (fun x => ENNReal.ofReal (Real.exp (-V x))) h0.ne' ht.ne) Ω V := by
  exact ⟨hs, h0, ht, AffineFibre.normalizedMeasure_eq_smul _ _ _ _⟩

/-- Internal normalization commutes with the existing Hausdorff-volume chart.
Agreement of the two densities is required only on the physical simplex. -/
theorem internal_simplex_normalized_chart (n : ℕ) (L : ℝ)
    (w : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞) (hw : Measurable w)
    (V : AffineSimplex.Tangent n → ℝ)
    (he : ∀ z ∈ AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L,
      w (AffineSimplex.centredChart n L z) = ENNReal.ofReal (Real.exp (-V z)))
    (h0 : 0 < ∫⁻ z in AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L,
      ENNReal.ofReal (Real.exp (-V z)))
    (ht : (∫⁻ z in AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L,
      ENNReal.ofReal (Real.exp (-V z))) < ⊤) :
    ∃ h0' ht', AffineFibre.normalizedMeasure (AffineSimplex.simplexVolume n L) w h0' ht' =
      (AffineFibre.normalizedMeasure
        (volume.restrict (AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L))
        (fun z => ENNReal.ofReal (Real.exp (-V z))) h0.ne' ht.ne).map (AffineSimplex.centredChart n L) := by
  let Ω := AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L
  have hae : (fun z => w (AffineSimplex.centredChart n L z)) =ᵐ[volume.restrict Ω]
      fun z => ENNReal.ofReal (Real.exp (-V z)) := by
    filter_upwards [ae_restrict_mem (fibre_isOpen n L).measurableSet] with z hz
    exact he z hz
  have hm : (∫⁻ x, w x ∂AffineSimplex.simplexVolume n L) =
      ∫⁻ z in Ω, ENNReal.ofReal (Real.exp (-V z)) := by
    rw [AffineSimplex.lintegral_centredChart]
    exact lintegral_congr_ae hae
  refine ⟨by rw [hm]; exact h0.ne', by rw [hm]; exact ht.ne, ?_⟩
  have h0c : (∫⁻ z in Ω, w (AffineSimplex.centredChart n L z)) ≠ 0 := by
    rw [lintegral_congr_ae hae]; exact h0.ne'
  have htc : (∫⁻ z in Ω, w (AffineSimplex.centredChart n L z)) ≠ ⊤ := by
    rw [lintegral_congr_ae hae]; exact ht.ne
  have hc := AffineFibre.normalizedMeasure_map (volume.restrict Ω)
    (AffineSimplex.isometry_centredChart n L).isClosedEmbedding.measurableEmbedding hw h0c htc
  simp only [AffineFibre.normalizedMeasure_eq_smul] at hc ⊢
  rw [← AffineSimplex.simplexVolume_eq_centredChart_map] at hc
  rw [hc]
  congr 1
  rw [lintegral_congr_ae hae, withDensity_congr_ae hae]

/-- See Appendix A of the paper, positive-dimensional branch: the actual
penalized Hausdorff conditional is the isometric image of a smooth Gibbs law
satisfying exactly the intrinsic curvature and ground-state hypotheses.
The length disintegration is `penalized_marginal_length_disintegration`. The point branch and full-law branch use the one-gap and physical APIs. -/
theorem fixed_length_marginal_fibres (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin ((n + 1) + m + 1)))
    {L : ℝ} (hL0 : 0 < L) (hL : L < ((n + 1 + m : ℕ) + 1 : ℝ))
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a) (J : Finset (Fin (n + 1))) (b : Bool) :
    let Ω := AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L
    let V := fun z : AffineSimplex.Tangent n =>
      p.val.1 * ∑ i ∈ J, (θ.val (a * AffineSimplex.centredChart n L z i) +
        if b then θ.val (a * (AffineSimplex.centredChart n L z i)⁻¹) else 0) -
      Real.log (∫ y : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n + 1) m σ (AffineSimplex.centredChart n L z, y)).toReal)
    let w := AffineFibre.fibreMass volume (ProperMarginalChart.penalizedChartDensity p (n + 1) m σ θ a
      (J.image (fun i => σ (i.castAdd m).castSucc)) b)
    ∃ ρ : Measure (AffineSimplex.Tangent n), IsEuclideanGibbsPotential volume ρ Ω V ∧
      (∃ h0 ht, AffineFibre.normalizedMeasure (AffineSimplex.simplexVolume n L) w h0 ht =
        ρ.map (AffineSimplex.centredChart n L)) ∧
      ∃ κ D : ℝ, 0 < κ ∧ 0 ≤ D ∧
        (∀ z ∈ Ω, ∀ u : AffineSimplex.Tangent n,
          κ * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) z u u) ∧
        ∀ z ∈ Ω, (Metric.infDist z (frontier Ω))⁻¹ ^ 2 - D ≤
          ‖gradient V z‖ ^ 2 / 4 - Laplacian.laplacian V z / 2 := by
  classical
  intro Ω V w
  obtain ⟨hs, κ, hκ, hH⟩ := penalized_marginal_fibre_regular p n m σ hL θ ha J b
  obtain ⟨h0, ht⟩ := penalized_marginal_fibre_normalizer p n m σ hL0 hL θ ha J b
  obtain ⟨D, hD, hbar⟩ := penalized_marginal_fibre_collision p n m hn σ hL0 hL θ ha J b
    (1 / 2) 2 (by norm_num) (by norm_num)
  let ρ := AffineFibre.normalizedMeasure (volume.restrict Ω)
    (fun z => ENNReal.ofReal (Real.exp (-V z))) h0.ne' ht.ne
  have hV := internal_normalized_gibbs hs h0 ht
  refine ⟨ρ, hV, ?_, κ, D / 2, hκ, div_nonneg hD (by norm_num), hH, fun z hz => ?_⟩
  · exact internal_simplex_normalized_chart n L w
      (AffineFibre.measurable_fibreMass volume
        (ProperMarginalChart.measurable_penalizedChartDensity p (n + 1) m σ θ ha _ b)) V
      (fun z hz => (penalized_marginal_fibre_density p n m σ hL θ a J b hz).symm) h0 ht
  · have hh := hbar z hz
    change 2 * (Metric.infDist z (frontier Ω))⁻¹ ^ 2 - D ≤
      (1 / 2 : ℝ) * ‖gradient V z‖ ^ 2 - Laplacian.laplacian V z at hh
    linarith only [hh]

/-- Internal orthonormal transport of the full scalar/vector conclusion. -/
theorem internal_orthonormal_wellposed (n : ℕ) (hn : 1 ≤ n) (L : ℝ)
    {ρ : Measure (AffineSimplex.Tangent n)} {V : AffineSimplex.Tangent n → ℝ}
    (hV : IsEuclideanGibbsPotential volume ρ
      (AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L) V)
    {κ D : ℝ} (hκ : 0 < κ) (hD : 0 ≤ D)
    (hH : ∀ w ∈ AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L,
      ∀ u : AffineSimplex.Tangent n, κ * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) w u u)
    (hb : ∀ w ∈ AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L,
      (Metric.infDist w (frontier (AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L)))⁻¹ ^ 2 - D ≤
        ‖gradient V w‖ ^ 2 / 4 - Laplacian.laplacian V w / 2) :
    let Ω := AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L
    ∀ e : AffineSimplex.Tangent n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      let ρ' := ρ.map e
      let U := e '' Ω
      let W := V ∘ e.symm
      ∃ hW : IsEuclideanGibbsPotential volume ρ' U W,
      let hU := e.toHomeomorph.isOpenMap Ω (fibre_isOpen n L)
      let hB := e.isometry.lipschitzWith.isBounded_image (fibre_isBounded n L)
      EuclideanWellPosed hU hB hW := by
  intro Ω e
  dsimp only
  have hW := IntrinsicScalarPoisson.gibbs_isometry e hV
  refine ⟨hW, ?_⟩
  have hHW : ∀ x ∈ e '' Ω, ∀ u,
      κ * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (V ∘ e.symm)) x u u := by
    rintro x ⟨w, hw, rfl⟩ u
    rw [SobolevIsometry.hessian_comp_symm e (fibre_isOpen n L) (hV.1.of_le (by norm_num))
      (by simpa only [e.symm_apply_apply] using hw), e.symm_apply_apply]
    simpa only [e.symm.norm_map] using hH w hw (e.symm u)
  exact internal_euclidean_wellposed hn
    (e.toHomeomorph.isOpenMap Ω (fibre_isOpen n L))
    (e.isometry.lipschitzWith.isBounded_image (fibre_isBounded n L))
    ((fibre_convex n L).linear_image e.toLinearEquiv.toLinearMap) hW hκ
    hD hHW
    (NeumannIsometryTransport.barrier_map e (fibre_isOpen n L) (hV.1.of_le (by norm_num)) hb)

/-- See Appendix A of the paper, positive-dimensional branch. Every compatible
conditional and interpolant has the intrinsic Gibbs realization, curvature
and ground-state barrier with constants uniform in `t`. In every orthonormal
chart its H¹ covariance is represented by the differentiated solution, and
every tangent H⁻¹ non-gradient source has a unique full-energy weak solution.
The one-gap branch is the `one_gap_law`, `one_gap_covariance` and
`one_gap_tangent`. -/
theorem compatible_conditionals_wellposed (p : Parameters) (n m r : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin ((n + 1) + m + 1)))
    (τ : Equiv.Perm (Fin ((n + 1) + r + 1))) {L : ℝ} (hL : 0 < L)
    (y : EuclideanSpace ℝ (Fin (m + 1))) (hy : ∀ j, 0 < y j)
    (z : EuclideanSpace ℝ (Fin (r + 1))) (hz : ∀ j, 0 < z j)
    (hcompatY : L + ∑ j, y j = ((n + 1 + m : ℕ) + 1 : ℝ))
    (hcompatZ : L + ∑ j, z j = ((n + 1 + r : ℕ) + 1 : ℝ))
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (J : Finset (Fin (n + 1))) (b : Bool) :
    let Ω := AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L
    let P := fun w : AffineSimplex.Tangent n => ∑ i ∈ J,
      (θ.val (a * AffineSimplex.centredChart n L w i) +
        if b then θ.val (a * (AffineSimplex.centredChart n L w i)⁻¹) else 0)
    ∃ Ky Kz : AffineSimplex.Tangent n → ℝ,
      (∀ w (hw : w ∈ Ω), Ky w = physicalAmbientGapEnergy p (n + 1 + m).succPNat
        ⟨RetainedSimplex.assemble (n + 1) m σ (AffineSimplex.centredChart n L w) y,
          PhysicalEnergy.simplex_subset_ambient _ _ (by
            have hh := assemble_fixed_exterior_mem n m σ y hy hcompatY hw
            rw [AffineSimplex.massSimplex_physical] at hh
            exact hh)⟩) ∧
      (∀ w (hw : w ∈ Ω), Kz w = physicalAmbientGapEnergy p (n + 1 + r).succPNat
        ⟨RetainedSimplex.assemble (n + 1) r τ (AffineSimplex.centredChart n L w) z,
          PhysicalEnergy.simplex_subset_ambient _ _ (by
            have hh := assemble_fixed_exterior_mem n r τ z hz hcompatZ hw
            rw [AffineSimplex.massSimplex_physical] at hh
            exact hh)⟩) ∧
      ∃ D : ℝ, 0 ≤ D ∧ ∀ t ∈ Icc (0 : ℝ) 1,
        let V := fun w => p.val.1 * (P w + (1 - t) * Ky w + t * Kz w)
        ∃ ρ : Measure (AffineSimplex.Tangent n),
        IsEuclideanGibbsPotential volume ρ Ω V ∧
          (∀ w ∈ Ω, ∀ u : AffineSimplex.Tangent n,
            (2 * p.val.1 * (p.val.2 * (p.val.2 + 1)) * L ^ (-p.val.2 - 2)) * ‖u‖ ^ 2 ≤
              fderiv ℝ (fderiv ℝ V) w u u) ∧
          (∀ w ∈ Ω, (Metric.infDist w (frontier Ω))⁻¹ ^ 2 - D ≤
            ‖gradient V w‖ ^ 2 / 4 - Laplacian.laplacian V w / 2) ∧
          ∀ e : AffineSimplex.Tangent n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
            let ρ' := ρ.map e
            let U := e '' Ω
            let W := V ∘ e.symm
            ∃ hW : IsEuclideanGibbsPotential volume ρ' U W,
            let hU := e.toHomeomorph.isOpenMap Ω (fibre_isOpen n L)
            let hB := e.isometry.lipschitzWith.isBounded_image (fibre_isBounded n L)
            EuclideanWellPosed hU hB hW := by
  intro Ω P
  obtain ⟨Ky, Kz, hKy, hKz, hcoll, hreg⟩ :=
    compatible_interpolation_collision_regular p n m r hn σ τ hL y hy z hz hcompatY hcompatZ θ ha J b
  obtain ⟨D, hD, hbar⟩ := hcoll (1 / 2) 2 (by norm_num) (by norm_num)
  refine ⟨Ky, Kz, hKy, hKz, D / 2, div_nonneg hD (by norm_num), fun t ht => ?_⟩
  intro V
  obtain ⟨hs, hH, _, h0, htop⟩ := hreg t ht
  let ρ := AffineFibre.normalizedMeasure (volume.restrict Ω)
    (fun w => ENNReal.ofReal (Real.exp (-V w))) h0.ne' htop.ne
  have hV := internal_normalized_gibbs hs h0 htop
  have hb : ∀ w ∈ Ω, (Metric.infDist w (frontier Ω))⁻¹ ^ 2 - D / 2 ≤
      ‖gradient V w‖ ^ 2 / 4 - Laplacian.laplacian V w / 2 := by
    intro w hw
    have hh := hbar t ht w hw
    change 2 * (Metric.infDist w (frontier Ω))⁻¹ ^ 2 - D ≤
      (1 / 2 : ℝ) * ‖gradient V w‖ ^ 2 - Laplacian.laplacian V w at hh
    linarith only [hh]
  have hκ : 0 < 2 * p.val.1 * (p.val.2 * (p.val.2 + 1)) * L ^ (-p.val.2 - 2) := by
    have hβ := p.property.1
    have hs := p.property.2.1
    positivity
  exact ⟨ρ, hV, hH, hb, internal_orthonormal_wellposed n hn L hV hκ
    (div_nonneg hD (by norm_num)) hH hb⟩


/-- The complete zero-dimensional branch of Appendix A. It holds for every potential, hence for every allowed
conditional and interpolant, without a positive-dimensional PDE assertion. -/
theorem one_gap_wellposed {L : ℝ} (hL : 0 < L)
    (V G H : EuclideanSpace ℝ (Fin 1) → ℝ) :
    (∃ h0 ht, AffineFibre.normalizedMeasure (AffineSimplex.simplexVolume 0 L)
      (fun x => ENNReal.ofReal (Real.exp (-V x))) h0 ht =
        Measure.dirac (AffineSimplex.chart 0 L 0)) ∧
    ProbabilityTheory.covariance G H (Measure.dirac (AffineSimplex.chart 0 L 0)) = 0 ∧
    (∀ u : AffineSimplex.Tangent 0, u = 0) :=
  ⟨one_gap_law hL V, one_gap_covariance L G H, one_gap_tangent⟩

/-- See Appendix A of the paper, full-law clause, for every allowed
selected-coordinate penalty. This assembles the full physical
collision theorem with positive finite normalization and the Gibbs
predicate. No physical collision estimate is proved again. -/
theorem full_law_admissible (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a) (J : Finset (Fin (N : ℕ))) (b : Bool) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      let V := fun w : gapTangentSpace N =>
        p.val.1 * W (WithLp.toLp 2 (fun i => 1 + w.val i)) + p.val.1 * ∑ i ∈ J,
          (θ.val (a * (1 + w.val i)) + if b then θ.val (a / (1 + w.val i)) else 0)
      ∃ ρ : Measure (gapTangentSpace N),
        IsEuclideanGibbsPotential volume ρ (intrinsicGapDomain N) V ∧
        ∃ κ D : ℝ, 0 < κ ∧ 0 ≤ D ∧
          (∀ w ∈ intrinsicGapDomain N, ∀ u : gapTangentSpace N,
            κ * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) w u u) ∧
          ∀ w ∈ intrinsicGapDomain N,
            (Metric.infDist w (frontier (intrinsicGapDomain N)))⁻¹ ^ 2 - D ≤
              ‖gradient V w‖ ^ 2 / 4 - Laplacian.laplacian V w / 2 := by
  obtain ⟨W, hWs, hW, κ, hκ, hH, hcoll⟩ :=
    PhysicalCollision.penalized_collision_criterion N p hN θ ha J b
  refine ⟨W, hW, ?_⟩
  intro V
  have hs : ContDiffOn ℝ ∞ V (intrinsicGapDomain N) :=
    (contDiffOn_const.mul (PhysicalCollision.contDiffOn_intrinsic_pullback N hWs)).add
      (contDiffOn_const.mul (PhysicalCollision.selected_penalty_smooth_convex N θ ha J b).1)
  have hc : ConvexOn ℝ (intrinsicGapDomain N) V := by
    apply convexOn_of_tangent_hessian_nonneg (PhysicalCollision.intrinsicGapDomain_convex N)
      (fun x hx => (hs.contDiffAt ((AffineMetric.intrinsicGapDomain_isOpen N).mem_nhds hx)).differentiableAt (by simp))
      (fun x hx => ((hs.contDiffAt ((AffineMetric.intrinsicGapDomain_isOpen N).mem_nhds hx)).fderiv_right
        (m := 1) (by simp)).differentiableAt (by simp))
    intro x hx y _ z _
    exact (mul_nonneg hκ.le (sq_nonneg ‖z - y‖)).trans (hH x hx (z - y))
  have hne : (intrinsicGapDomain N).Nonempty := by
    refine ⟨0, ?_⟩
    intro i
    simp
  obtain ⟨h0, ht⟩ := internal_convex_normalizer (AffineMetric.intrinsicGapDomain_isOpen N)
    (PhysicalCollision.intrinsicGapDomain_bounded N) hne hc hs.continuousOn
  obtain ⟨D, hD, hbar⟩ := hcoll (1 / 2) 2 (by norm_num) (by norm_num)
  refine ⟨_, internal_normalized_gibbs hs h0 ht, κ, D / 2,
    hκ, div_nonneg hD (by norm_num), hH, fun w hw => ?_⟩
  have hh := hbar w hw
  change 2 * (Metric.infDist w (frontier (intrinsicGapDomain N)))⁻¹ ^ 2 - D ≤
    (1 / 2 : ℝ) * ‖gradient V w‖ ^ 2 - Laplacian.laplacian V w at hh
  linarith only [hh]

/-- The full-law clause of Appendix A on the tilted gap law. The existing physical-law identification supplies the
Gibbs realization. The amplified bound gives the exact ground-state bound. -/
theorem full_frozen_law_admissible (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ) (b : Bool) :
    ∃ V : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ V (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        V y.val = fullPhysicalPotentialValue p N hN θ ε b y) ∧
      IsEuclideanGibbsPotential volume (fullIntrinsicTiltedGapLaw p N θ ε b)
        (intrinsicGapDomain N) (fun w : gapTangentSpace N =>
          V (WithLp.toLp 2 (fun i => 1 + w.val i))) ∧
      ∃ κ D : ℝ, 0 < κ ∧ 0 ≤ D ∧
        (∀ w ∈ intrinsicGapDomain N, ∀ u : gapTangentSpace N,
          κ * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (fun w : gapTangentSpace N =>
            V (WithLp.toLp 2 (fun i => 1 + w.val i)))) w u u) ∧
        ∀ w ∈ intrinsicGapDomain N,
          (Metric.infDist w (frontier (intrinsicGapDomain N)))⁻¹ ^ 2 - D ≤
            ‖gradient (fun w : gapTangentSpace N => V (WithLp.toLp 2 (fun i => 1 + w.val i))) w‖ ^ 2 / 4 -
              Laplacian.laplacian (fun w : gapTangentSpace N => V (WithLp.toLp 2 (fun i => 1 + w.val i))) w / 2 := by
  obtain ⟨V, hs, hv, hV, κ, hκ, hH, hcoll⟩ :=
    PhysicalCollision.fullPhysicalPotential_wellposed N p hN θ ε b
  obtain ⟨D, hD, hb⟩ := hcoll (1 / 2) 2 (by norm_num) (by norm_num)
  refine ⟨V, hs, hv, hV, κ, D / 2, hκ, div_nonneg hD (by norm_num), hH, fun w hw => ?_⟩
  have hh := hb w hw
  linarith only [hh]

end Riesz2.ConditionalWellPosedness
