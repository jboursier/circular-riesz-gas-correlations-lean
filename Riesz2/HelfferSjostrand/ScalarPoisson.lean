/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.IntrinsicScalarCore
public import Riesz2.ToMathlib.CoerciveSolutionMaps
public import Riesz2.Bridges.ConvexMeasureInputs
public import Riesz2.ToMathlib.WeightedSobolevIsometry
public import Riesz2.ToMathlib.LogSobolevPoincare

/-!
# Intrinsic scalar Poisson equation

See the proof of Proposition 3.3 in the paper, on an arbitrary finite-dimensional
real inner product space, including the intrinsic gap tangent space.
The generator and the form are exactly those constructed in `IntrinsicScalarCore`.
Logarithmic Sobolev supplies Poincaré for the completed Neumann jets. The abstract
probability-space Poisson theorem of Riesz1 then applies to every L² source.
Strict curvature suffices: the collision barrier and polytope restriction are
unnecessary for this scalar variational assertion.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Topology

namespace Riesz2.IntrinsicScalarPoisson

open IntrinsicScalarCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {U : Set E} {ρ : Measure E} {V : E → ℝ}

/-- See Subsection 3.1 of the paper: the Gibbs normalizer agrees with the real
normalizer in the companion library's tilted law. -/
theorem gibbs_eq_tilted (hU : IsOpen U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) :
    ρ = (volume.restrict U).tilted (fun x => -V x) := by
  let Z := ∫⁻ x in U, ENNReal.ofReal (Real.exp (-V x))
  have hZ : 0 < Z.toReal := ENNReal.toReal_pos hV.2.1.ne' hV.2.2.1.ne
  have hi : (∫ x in U, Real.exp (-V x)) = Z.toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => (Real.exp_pos _).le)
      (hV.1.neg.exp.continuousOn.aestronglyMeasurable hU.measurableSet)
  rw [Measure.tilted, hi, hV.2.2.2,
    ← withDensity_smul' _ _ (ENNReal.inv_ne_top.mpr hV.2.1.ne')]
  congr 1
  funext x
  rw [div_eq_mul_inv, ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_inv_of_pos hZ, ENNReal.ofReal_toReal hV.2.2.1.ne, mul_comm]
  rfl

/-- See Subsection 3.1 of the paper: a completed intrinsic jet is literally an H¹
value–gradient pair in the Riesz1 convention used by Brascamp–Lieb. -/
theorem weightedH1 (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V)
    (u : ScalarForm.Domain (jet hU hB hV)) :
    Riesz1.WeightedSobolev.IsWeightedH1 ρ U
      (ScalarForm.value (jet hU hB hV) u) (ScalarForm.deriv (jet hU hB hV) u) := by
  have := probability hV
  have hf := Lp.memLp (ScalarForm.value (jet hU hB hV) u)
  have hg := Lp.memLp (ScalarForm.deriv (jet hU hB hV) u)
  apply (EuclideanScalarForm.mem_completion_iff hU hB (supported hU hV) _ _ hf hg).mp
  simp only [Lp.toLp_coeFn]
  exact u.property

/-- See Appendix A of the paper: an orthonormal chart preserves the Gibbs potential and its law, including its positive finite normalizer. -/
theorem gibbs_isometry {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (e : E ≃ₗᵢ[ℝ] F)
    (hV : IsEuclideanGibbsPotential volume ρ U V) :
    IsEuclideanGibbsPotential volume (ρ.map e) (e '' U) (V ∘ e.symm) := by
  let em := e.toHomeomorph.toMeasurableEquiv
  have hr : (volume.restrict U).map e = volume.restrict (e '' U) := by
    have ht := em.measurableEmbedding.restrict_map (volume : Measure E) (e '' U)
    have he : (volume : Measure E).map e = volume := e.measurePreserving.map_eq
    change ((volume : Measure E).map e).restrict (e '' U) =
      (volume.restrict (e ⁻¹' (e '' U))).map e at ht
    rw [preimage_image_eq _ e.injective, he] at ht
    exact ht.symm
  have hZ : (∫⁻ y in e '' U, ENNReal.ofReal (Real.exp (-(V ∘ e.symm) y))) =
      ∫⁻ x in U, ENNReal.ofReal (Real.exp (-V x)) := by
    rw [← hr]
    erw [em.measurableEmbedding.lintegral_map]
    simp [em]
  refine ⟨hV.1.comp e.symm.contDiff.contDiffOn
    (by rintro y ⟨x, hx, rfl⟩; simpa using hx), ?_⟩
  dsimp only
  rw [hZ]
  refine ⟨hV.2.1, hV.2.2.1, ?_⟩
  rw [hV.2.2.2, Measure.map_smul _ e.continuous.measurable.aemeasurable, SobolevIsometry.map_withDensity, hr]
  rfl

/-- Variational assembly for the proof of Proposition 3.3.
The Poincaré inequality is supplied by `poincare`. -/
theorem existsUnique_of_poincare (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) {C : ℝ} (hC : 0 ≤ C)
    (hP : ∀ u : ScalarForm.Domain (jet hU hB hV),
      ‖ScalarForm.value (jet hU hB hV) u‖ ^ 2 -
          (∫ x, ScalarForm.value (jet hU hB hV) u x ∂ρ) ^ 2 ≤
        C * ScalarForm.energy (jet hU hB hV) u u)
    (G : Lp ℝ 2 ρ) :
    letI := probability hV
    ∃! ψ : Lp ℝ 2 ρ, (∫ x, ψ x ∂ρ) = 0 ∧
      (ψ, Riesz1.poissonCenter ρ G) ∈ (operator hU hB hV).graph := by
  have := probability hV
  let J := jet hU hB hV
  let one := EuclideanScalarForm.constant hU hB (supported hU hV) 1
  have hone : ScalarForm.value J one = Lp.const 2 ρ (1 : ℝ) := by
    apply Lp.ext
    exact (EuclideanScalarForm.value_constant hU hB (supported hU hV) 1).trans
      (Lp.coeFn_const 2 ρ (1 : ℝ)).symm
  have hdone : ScalarForm.deriv J one = 0 :=
    EuclideanScalarForm.deriv_constant hU hB (supported hU hV) 1
  have hn (u : ScalarForm.Domain J) :
      ‖u‖ ^ 2 = ‖ScalarForm.value J u‖ ^ 2 + ‖ScalarForm.deriv J u‖ ^ 2 := by
    rw [ScalarForm.norm_sq, ScalarForm.energy, real_inner_self_eq_norm_sq]
  have hp (u : ScalarForm.Domain J) :
      ‖ScalarForm.value J u‖ ^ 2 - (Riesz1.poissonMean ρ (ScalarForm.value J u)) ^ 2 ≤
        C * ‖ScalarForm.deriv J u‖ ^ 2 := by
    simpa only [Riesz1.poissonMean_eq_integral, ScalarForm.energy,
      real_inner_self_eq_norm_sq] using hP u
  obtain ⟨u, hm, hu, huniq, _⟩ := Riesz1.Internal.probability_poisson ρ
    (ScalarForm.value J) (ScalarForm.deriv J) one hone hdone hn C hC hp G
  refine ⟨ScalarForm.value J u, ⟨(Riesz1.poissonMean_eq_integral ρ _).symm.trans hm, ?_⟩, ?_⟩
  · rw [operator, ScalarForm.l2Operator_graph, ScalarForm.mem_l2Graph_iff]
    exact ⟨u, rfl, hu⟩
  · rintro ψ ⟨hmψ, hψ⟩
    rw [operator, ScalarForm.l2Operator_graph, ScalarForm.mem_l2Graph_iff] at hψ
    obtain ⟨v, hv, he⟩ := hψ
    have hmv : Riesz1.poissonMean ρ (ScalarForm.value J v) = 0 := by
      rw [hv, Riesz1.poissonMean_eq_integral, hmψ]
    exact hv.symm.trans (congrArg (ScalarForm.value J) (huniq v hmv he))

/-- See Subsection 3.1 of the paper, all weak identities for an arbitrary L² source.
Every cross term is integrable and every test belongs to the full form domain. This identifies generator membership with its weak meaning. -/
theorem weak_identities (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) (G ψ : Lp ℝ 2 ρ)
    (hψ : (ψ, @Riesz1.poissonCenter E _ ρ (probability hV) G) ∈ (operator hU hB hV).graph) :
    Integrable G ρ ∧ Integrable ψ ρ ∧
      ∃ hdom : ψ ∈ (form hU hB hV).1, ∀ h : (form hU hB hV).1,
        Integrable (fun x => (G x - ∫ y, G y ∂ρ) * h.val x) ρ ∧
        (form hU hB hV).2 ⟨ψ, hdom⟩ h =
          ∫ x, (G x - ∫ y, G y ∂ρ) * h.val x ∂ρ := by
  have := probability hV
  obtain ⟨hdom, he⟩ := (graph_iff hU hB hV ψ _).mp hψ
  refine ⟨(Lp.memLp G).integrable one_le_two,
    (Lp.memLp ψ).integrable one_le_two, hdom, fun h => ?_⟩
  have hae := (Riesz1.poissonCenter_ae ρ G).mono
    (fun x hx => congrArg (· * h.val x) hx)
  exact ⟨((Lp.memLp (Riesz1.poissonCenter ρ G)).integrable_mul (Lp.memLp h.val)).congr hae,
    (he h).trans ((Riesz1.poisson_inner_eq_integral ρ _ _).trans (integral_congr_ae hae))⟩

section Intrinsic

variable [Nontrivial E]

/-- The Poincaré step of Proposition 3.3 through Lemma 3.7,
on the actual intrinsic Neumann completion. An orthonormal chart preserves
the entropy, gradient energy and reciprocal-curvature constant. -/
theorem poincare_of_logSobolev (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (_hne : U.Nonempty) (hc : Convex ℝ U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) {κ : ℝ} (hκ : 0 < κ)
    (hH : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h)
    (u : ScalarForm.Domain (jet hU hB hV)) :
    ‖ScalarForm.value (jet hU hB hV) u‖ ^ 2 -
        (∫ x, ScalarForm.value (jet hU hB hV) u x ∂ρ) ^ 2 ≤
      κ⁻¹ * ScalarForm.energy (jet hU hB hV) u u := by
  have := probability hV
  let e := (stdOrthonormalBasis ℝ E).repr
  let em := e.toHomeomorph.toMeasurableEquiv
  let f := ScalarForm.value (jet hU hB hV) u
  let g := ScalarForm.deriv (jet hU hB hV) u
  have ho : IsOpen (e '' U) := e.toHomeomorph.isOpenMap _ hU
  have hV' := gibbs_isometry e hV
  have hH' : ∀ y ∈ e '' U, ∀ h,
      κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (V ∘ e.symm)) y h h := by
    rintro y ⟨x, hx, rfl⟩ h
    rw [SobolevIsometry.hessian_comp_symm e hU (hV.1.of_le (by norm_num))
      (by simpa using hx)]
    simpa only [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.norm_map] using
      hH x hx (e.symm h)
  have hfg := SobolevIsometry.weightedH1 e (supported hU hV) (weightedH1 hU hB hV u)
  have hb := LogSobolevPoincare.poincare_of_gibbsPotential
    (Module.finrank_pos (R := ℝ) (M := E)) (e.isometry.lipschitzWith.isBounded_image hB)
    ho (hc.linear_image e.toLinearEquiv.toLinearMap) hV' hκ hH' hfg
  have hm : (∫ y, f (e.symm y) ∂ρ.map e) = ∫ x, f x ∂ρ := by
    erw [em.measurableEmbedding.integral_map]
    simp [em]
  have hv : (∫ y, (f (e.symm y) - ∫ z, f (e.symm z) ∂ρ.map e) ^ 2 ∂ρ.map e) =
      ‖f‖ ^ 2 - (∫ x, f x ∂ρ) ^ 2 := by
    rw [hm]
    erw [em.measurableEmbedding.integral_map]
    simpa [em, Riesz1.poissonMean_eq_integral] using Riesz1.poisson_variance_eq ρ f
  have hg : (∫ y, ‖e (g (e.symm y))‖ ^ 2 ∂ρ.map e) =
      ScalarForm.energy (jet hU hB hV) u u := by
    erw [em.measurableEmbedding.integral_map]
    have hn : (∫ x, ‖g x‖ ^ 2 ∂ρ) = ‖g‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      simp only [real_inner_self_eq_norm_sq]
    simpa [em, g, ScalarForm.energy] using hn
  change (∫ y, (f (e.symm y) - ∫ z, f (e.symm z) ∂ρ.map e) ^ 2 ∂ρ.map e) ≤
    κ⁻¹ * ∫ y, ‖e (g (e.symm y))‖ ^ 2 ∂ρ.map e at hb
  rw [hv, hg] at hb
  exact hb

/-- The Poincaré step of Proposition 3.3, using the logarithmic Sobolev inequality
and the scalar Poisson solver. -/
theorem poincare (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hne : U.Nonempty) (hc : Convex ℝ U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) {κ : ℝ} (hκ : 0 < κ)
    (hH : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h)
    (u : ScalarForm.Domain (jet hU hB hV)) :
    ‖ScalarForm.value (jet hU hB hV) u‖ ^ 2 -
        (∫ x, ScalarForm.value (jet hU hB hV) u x ∂ρ) ^ 2 ≤
      κ⁻¹ * ScalarForm.energy (jet hU hB hV) u u :=
  poincare_of_logSobolev hU hB hne hc hV hκ hH u

/-- See the proof of Proposition 3.3 in the paper: every L² source has a
unique mean-zero solution in the intrinsic Neumann generator domain.
The result holds on every bounded open convex domain in arbitrary
positive dimension, with the intrinsic affine metric. -/
theorem poisson_existsUnique (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hc : Convex ℝ U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) {κ : ℝ} (hκ : 0 < κ)
    (hH : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h)
    (G : Lp ℝ 2 ρ) :
    letI := probability hV
    ∃! ψ : Lp ℝ 2 ρ, (∫ x, ψ x ∂ρ) = 0 ∧
      (ψ, Riesz1.poissonCenter ρ G) ∈ (operator hU hB hV).graph := by
  have hne : U.Nonempty := by
    by_contra h
    have he : U = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have hz := hV.2.1
    simp only [he, Measure.restrict_empty, lintegral_zero_measure, lt_self_iff_false] at hz
  exact existsUnique_of_poincare hU hB hV (inv_nonneg.mpr hκ.le)
    (poincare hU hB hne hc hV hκ hH) G

/-- See the proof of Proposition 3.3 in the paper, as the `ScalarPoissonSolution` predicate when the source is also in the form domain.
The all-L² statement is `poisson_existsUnique`. No H¹ restriction is made there. -/
theorem scalarPoissonSolution_existsUnique (hU : IsOpen U)
    (hB : Bornology.IsBounded U) (hc : Convex ℝ U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) {κ : ℝ} (hκ : 0 < κ)
    (hH : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h)
    (G : (form hU hB hV).1) :
    ∃! ψ : (form hU hB hV).1, ScalarPoissonSolution (form hU hB hV) G ψ := by
  have := probability hV
  obtain ⟨ψ, ⟨hm, hs⟩, huniq⟩ := poisson_existsUnique hU hB hc hV hκ hH G.val
  obtain ⟨hG, hψ, hdom, hw⟩ := weak_identities hU hB hV G.val ψ hs
  refine ⟨⟨ψ, hdom⟩, ⟨hG, hψ, hm, hw⟩, fun φ hφ => ?_⟩
  apply Subtype.ext
  apply huniq φ.val
  refine ⟨hφ.2.2.1, (graph_iff hU hB hV φ.val _).mpr ⟨φ.property, fun h => ?_⟩⟩
  have hae := (Riesz1.poissonCenter_ae ρ G.val).mono
    (fun x hx => congrArg (· * h.val x) hx)
  exact (hφ.2.2.2 h).2.trans
    ((integral_congr_ae hae).symm.trans (Riesz1.poisson_inner_eq_integral ρ _ _).symm)

end Intrinsic

end Riesz2.IntrinsicScalarPoisson
