/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.ConditionalParticleBrascampLieb
public import Riesz2.HelfferSjostrand.PhysicalCollision
public import Riesz2.Bridges.ConvexMeasureInputs
public import Riesz1.ToMathlib.WeightedSobolev.GraphTransport
public import Riesz1.ToMathlib.WeightedSobolev.VariationalPairing

/-!
# Sobolev pullback and restriction for conditional particle Brascamp–Lieb

The nonisometric microscopic gap map has differential of norm at most `2N`.
Its adjoint takes intrinsic gap gradients to particle gradients in `1⊥`.
These identities pass to weighted H¹ by smooth approximation. Bounded measure
domination then permits restriction to a conditioning domain without assuming
that the domain is a gap event. These are steps of Lemma 3.4 in the
paper.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology InnerProductSpace ContDiff ENNReal

namespace Riesz2.ConditionalParticleBrascampLieb

open AffineMetric Riesz1.WeightedSobolev

variable {N : ℕ+}

/-- The ambient-to-intrinsic differential of the microscopic gap map in
Lemma 3.4. It is a difference operator, not an isometry. -/
def gapDerivative (N : ℕ+) :
    EuclideanSpace ℝ (Fin (N : ℕ)) →L[ℝ] gapTangentSpace N :=
  (LinearMap.codRestrict (gapTangentSpace N) (cyclicGapLinear N)
    (sum_cyclicGapLinear N)).toContinuousLinearMap

/-- The microscopic gap map on the whole particle lift in Lemma 3.4,
written in the isometric chart `y = 1 + z`. -/
def liftedGapMap (N : ℕ+) (x : EuclideanSpace ℝ (Fin (N : ℕ))) : gapTangentSpace N :=
  centeredGapChart N (WithLp.toLp 2 (Riesz1.hsGap x))

/-- The affine gap formula used by Lemma 3.4 holds on the entire lift. -/
theorem liftedGapMap_eq (N : ℕ+) (x : EuclideanSpace ℝ (Fin (N : ℕ))) :
    liftedGapMap N x = gapDerivative N x + gapOffset N := by
  apply Subtype.ext
  ext i
  have he := congrArg (fun y : EuclideanSpace ℝ (Fin (N : ℕ)) => y i)
    (hsGap_eq_linear_add x)
  change Riesz1.hsGap x i - (∑ j, Riesz1.hsGap x j) / (N : ℝ) =
    cyclicGapLinear N x i +
      (Riesz1.hsGap 0 i - (∑ j, Riesz1.hsGap 0 j) / (N : ℝ))
  rw [Riesz1.sum_hsGap, Riesz1.sum_hsGap]
  change Riesz1.hsGap x i = cyclicGapLinear N x i + Riesz1.hsGap 0 i at he
  linarith

/-- The gap differential has norm at most `2N`, as used in
Lemma 3.4. -/
theorem norm_gapDerivative_le (N : ℕ+) : ‖gapDerivative N‖ ≤ 2 * (N : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact norm_cyclicGapLinear_le N

/-- Common rotation is in the kernel of the gap differential in
Lemma 3.4. -/
theorem gapDerivative_unit (N : ℕ+) : gapDerivative N (Riesz1.hsUnitVector N) = 0 := by
  apply Subtype.ext
  ext i
  simp [gapDerivative, cyclicGapLinear_apply, Riesz1.hsUnitVector, Riesz1.hsRotationVector]

/-- The adjoint gap differential produces a tangent particle gradient in
Lemma 3.4. -/
theorem adjoint_gapDerivative_tangent (g : gapTangentSpace N) :
    (gapDerivative N).adjoint g ∈ gapTangentSpace N := by
  have hmem (u : EuclideanSpace ℝ (Fin (N : ℕ))) :
      u ∈ gapTangentSpace N ↔ u ∈ Riesz1.hsOrthSubspace N := by
    rw [gapTangentSpace_eq_orth]
  apply (hmem _).mpr
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left,
    ContinuousLinearMap.adjoint_inner_left, gapDerivative_unit]
  simp

/-- The quantitative gap chain rule in Lemma 3.4. -/
theorem norm_adjoint_gapDerivative_le (g : gapTangentSpace N) :
    ‖(gapDerivative N).adjoint g‖ ≤ 2 * (N : ℝ) * ‖g‖ := by
  calc
    _ ≤ ‖(gapDerivative N).adjoint‖ * ‖g‖ := (gapDerivative N).adjoint.le_opNorm g
    _ = ‖gapDerivative N‖ * ‖g‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ _ := mul_le_mul_of_nonneg_right (norm_gapDerivative_le N) (norm_nonneg g)

/-- Smooth gap chain rule in the full particle metric for
Lemma 3.4. -/
theorem gradient_gap_pullback {f : gapTangentSpace N → ℝ}
    {x : EuclideanSpace ℝ (Fin (N : ℕ))}
    (hf : DifferentiableAt ℝ f (liftedGapMap N x)) :
    gradient (fun y => f (liftedGapMap N y)) x =
      (gapDerivative N).adjoint (gradient f (liftedGapMap N x)) := by
  have ht : HasFDerivAt (liftedGapMap N) (gapDerivative N) x := by
    simpa only [← liftedGapMap_eq] using
      (gapDerivative N).hasFDerivAt.add_const (gapOffset N)
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, ContinuousLinearMap.adjoint_inner_left, inner_gradient_left]
  exact congrArg (fun L => L v) (hf.hasFDerivAt.comp x ht).fderiv

/-- The affine microscopic gap map sends the particle chamber to the intrinsic
gap domain in Lemma 3.4. -/
theorem liftedGapMap_mem {x : EuclideanSpace ℝ (Fin (N : ℕ))}
    (hx : x ∈ particleChamber N) : liftedGapMap N x ∈ intrinsicGapDomain N := by
  intro i
  change 0 < 1 + (Riesz1.hsGap x i - (∑ j, Riesz1.hsGap x j) / (N : ℝ))
  rw [Riesz1.sum_hsGap, div_self (by positivity : (N : ℝ) ≠ 0)]
  simpa using (Riesz1.hsGap_mem_gapSimplex hx).1 i

namespace Internal

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E']

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E'] in
/-- Smooth approximation under the affine pullback used in
Lemma 3.4. This helper does not assume the map is isometric. -/
theorem affine_smoothNearClosure (A : E →L[ℝ] E') (a : E') {U : Set E} {V : Set E'}
    (hUV : MapsTo (fun x => A x + a) U V) {f : E' → ℝ} (hf : SmoothNearClosure V f) :
    SmoothNearClosure U (fun x => f (A x + a)) := by
  obtain ⟨W, hW, hVW, hfW⟩ := hf
  refine ⟨(fun x => A x + a) ⁻¹' W, hW.preimage (A.continuous.add_const a), ?_, ?_⟩
  · exact fun x hx => hVW ((hUV.closure (A.continuous.add_const a)) hx)
  · exact hfW.comp (A.contDiff.add contDiff_const).contDiffOn (fun _ hx => hx)

/-- Weighted H¹ affine pullback by smooth approximation for
Lemma 3.4, with the actual adjoint differential. -/
theorem affine_weightedH1_pullback (A : E →L[ℝ] E') (a : E')
    {μ : Measure E} [IsFiniteMeasure μ] {U : Set E} {V : Set E'}
    (hVb : Bornology.IsBounded V) (hVm : MeasurableSet V)
    (hμ : ∀ᵐ x ∂μ, x ∈ U) (hUV : MapsTo (fun x => A x + a) U V)
    {F : E' → ℝ} {G : E' → E'}
    (hFG : IsWeightedH1 (μ.map (fun x => A x + a)) V F G) :
    IsWeightedH1 μ U (fun x => F (A x + a)) (fun x => A.adjoint (G (A x + a))) := by
  let T := fun x => A x + a
  have hT : Measurable T := (A.continuous.add_const a).measurable
  have hν : ∀ᵐ y ∂μ.map T, y ∈ V :=
    (ae_map_iff hT.aemeasurable hVm).mpr (hμ.mono fun x hx => hUV hx)
  have hm (f : E' → ℝ) (hf : SmoothNearClosure V f) :=
    memLp_of_smoothNearClosure hVb hν hf
  have hbase : IsGraphH1 (μ.map T) (SmoothNearClosure V) id gradient F G := hFG
  have hp : IsGraphH1 μ (SmoothNearClosure V) (fun f x => f (T x))
      (fun f x => gradient f (T x)) (fun x => F (T x)) (fun x => G (T x)) :=
    hbase.comp_measurePreserving (fun f hf => (hm f hf).1)
      (fun f hf => (hm f hf).2) ⟨hT, rfl⟩
  have hg : IsGraphH1 μ (SmoothNearClosure V) (fun f x => f (T x))
      (fun f x => A.adjoint (gradient f (T x))) (fun x => F (T x))
      (fun x => A.adjoint (G (T x))) :=
    hp.map_derivative (fun f hf => (hm f hf).2.comp_measurePreserving ⟨hT, rfl⟩) A.adjoint
  obtain ⟨hF, hG, φ, hφ, hv, hd⟩ := hg
  refine ⟨hF, hG, fun k x => φ k (T x),
    fun k => affine_smoothNearClosure A a hUV (hφ k), hv, ?_⟩
  convert hd using 1
  funext k
  apply lintegral_congr_ae
  filter_upwards [hμ] with x hx
  have hdiff : DifferentiableAt ℝ (φ k) (T x) := by
    obtain ⟨W, hW, hVW, hfW⟩ := hφ k
    exact (hfW.contDiffAt (hW.mem_nhds (hVW (subset_closure (hUV hx))))).differentiableAt
      (by simp)
  have he : gradient (fun y => φ k (T y)) x = A.adjoint (gradient (φ k) (T x)) := by
    apply ext_inner_right ℝ
    intro v
    rw [inner_gradient_left, ContinuousLinearMap.adjoint_inner_left, inner_gradient_left]
    exact congrArg (fun L => L v) (hdiff.hasFDerivAt.comp x (A.hasFDerivAt.add_const a)).fderiv
  simp only [he, T]

omit [BorelSpace E] in
/-- Bounded measure domination preserves completed H¹ and allows a smaller
domain. This is the restriction/density-change step in Lemma 3.4. -/
theorem weightedH1_of_measure_le_smul {μ ν : Measure E} {C : ℝ≥0∞}
    (hC : C ≠ ⊤) (hν : ν ≤ C • μ) {U V : Set E} (hVU : V ⊆ U)
    {F : E → ℝ} {G : E → E} (hFG : IsWeightedH1 μ U F G) :
    IsWeightedH1 ν V F G := by
  obtain ⟨hF, hG, φ, hφ, hv, hg⟩ := hFG
  have hlim {H : ℕ → E → ℝ≥0∞}
      (hH : Tendsto (fun k => ∫⁻ x, H k x ∂μ) atTop (𝓝 0)) :
      Tendsto (fun k => ∫⁻ x, H k x ∂ν) atTop (𝓝 0) := by
    have hb k : (∫⁻ x, H k x ∂ν) ≤ C * ∫⁻ x, H k x ∂μ := by
      calc
        _ ≤ ∫⁻ x, H k x ∂C • μ := lintegral_mono' hν le_rfl
        _ = _ := lintegral_smul_measure C _
    have hl := ENNReal.Tendsto.const_mul hH (Or.inr hC)
    simp only [mul_zero] at hl
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl
      (fun _ => bot_le) hb
  refine ⟨hF.of_measure_le_smul hC hν, hG.of_measure_le_smul hC hν, φ, ?_, hlim hv, hlim hg⟩
  intro k
  obtain ⟨W, hW, hUW, hfW⟩ := hφ k
  exact ⟨W, hW, (closure_mono hVU).trans hUW, hfW⟩

end Internal

/-- The microscopic-gap H¹ pullback and tangency step of Lemma 3.4
on an arbitrary finite particle lift law. The weak gradient is the adjoint
cyclic difference of the intrinsic gradient. -/
theorem gap_weightedH1_pullback {μ : Measure (EuclideanSpace ℝ (Fin (N : ℕ)))}
    [IsFiniteMeasure μ] {Ω : Set (EuclideanSpace ℝ (Fin (N : ℕ)))}
    (hΩ : Ω ⊆ particleChamber N) (hμ : ∀ᵐ x ∂μ, x ∈ Ω)
    {F : gapTangentSpace N → ℝ} {G : gapTangentSpace N → gapTangentSpace N}
    (hFG : IsWeightedH1 (μ.map (liftedGapMap N)) (intrinsicGapDomain N) F G) :
    IsWeightedH1 μ Ω (fun x => F (liftedGapMap N x))
      (fun x => (gapDerivative N).adjoint (G (liftedGapMap N x))) ∧
      (∀ x, (gapDerivative N).adjoint (G (liftedGapMap N x)) ∈ gapTangentSpace N) ∧
      ∀ x, ‖(gapDerivative N).adjoint (G (liftedGapMap N x))‖ ≤
        2 * (N : ℝ) * ‖G (liftedGapMap N x)‖ := by
  refine ⟨?_, fun x => adjoint_gapDerivative_tangent _, fun x => norm_adjoint_gapDerivative_le _⟩
  have he : liftedGapMap N = fun x => gapDerivative N x + gapOffset N :=
    funext (liftedGapMap_eq N)
  rw [he] at hFG ⊢
  apply Internal.affine_weightedH1_pullback (gapDerivative N) (gapOffset N)
    (PhysicalCollision.intrinsicGapDomain_bounded N) (intrinsicGapDomain_isOpen N).measurableSet
    hμ _ hFG
  intro x hx
  dsimp only
  rw [← liftedGapMap_eq]
  exact liftedGapMap_mem (hΩ hx)

/-- Restriction and normalization in Lemma 3.4 preserve weighted
H¹. No assumption that the conditioning event depends only on gaps is made. -/
theorem conditional_weightedH1 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    {μ : Measure E} {Ω A : Set E} (hA : A ⊆ Ω) (hmass : μ A ≠ 0)
    {F : E → ℝ} {G : E → E} (hFG : IsWeightedH1 μ Ω F G) :
    IsWeightedH1 ((μ A)⁻¹ • μ.restrict A) A F G := by
  apply Internal.weightedH1_of_measure_le_smul (ENNReal.inv_ne_top.mpr hmass) _ hA hFG
  exact _root_.smul_le_smul_left _ Measure.restrict_le_self

/-- The quantitative restriction bound in the proof of Lemma 3.4:
the conditional L² norm costs at most the inverse square root of the mass. -/
theorem conditional_eLpNorm_le {E : Type*} [MeasurableSpace E]
    {V : Type*} [NormedAddCommGroup V] {μ : Measure E} (A : Set E) (F : E → V) :
    eLpNorm F 2 ((μ A)⁻¹ • μ.restrict A) ≤
      ((μ A)⁻¹) ^ (1 / 2 : ℝ) * eLpNorm F 2 μ := by
  have hd : (μ A)⁻¹ • μ.restrict A ≤ (μ A)⁻¹ • μ :=
    _root_.smul_le_smul_left _ Measure.restrict_le_self
  simpa using (eLpNorm_le_of_measure_le_smul (f := F) (p := 2) hd)

/-- The H¹ pullback followed by conditioning in Lemma 3.4,
for an arbitrary positive-mass particle event inside the lift domain. -/
theorem conditional_gap_weightedH1_pullback
    {μ : Measure (EuclideanSpace ℝ (Fin (N : ℕ)))}
    [IsFiniteMeasure μ] {Ω A : Set (EuclideanSpace ℝ (Fin (N : ℕ)))}
    (hΩ : Ω ⊆ particleChamber N) (hμ : ∀ᵐ x ∂μ, x ∈ Ω)
    (hA : A ⊆ Ω) (hmass : μ A ≠ 0)
    {F : gapTangentSpace N → ℝ} {G : gapTangentSpace N → gapTangentSpace N}
    (hFG : IsWeightedH1 (μ.map (liftedGapMap N)) (intrinsicGapDomain N) F G) :
    IsWeightedH1 ((μ A)⁻¹ • μ.restrict A) A (fun x => F (liftedGapMap N x))
      (fun x => (gapDerivative N).adjoint (G (liftedGapMap N x))) :=
  conditional_weightedH1 hA hmass (gap_weightedH1_pullback hΩ hμ hFG).1

namespace Internal

/-- The Euclidean Brascamp–Lieb inequality on the convex conditioning domain
in the proof of Lemma 3.4. The H¹ premise concerns the regularized law.
Its inverse energy on tangent vectors equals that of the original
particle Hessian. -/
theorem regularized_particle_brascamp_lieb
    (hN : 2 ≤ (N : ℕ)) {c : ℝ} (hc : 0 < c) {χ : ParticlePairData N}
    (hχ : AdmissibleParticlePairs hN χ c)
    {Ω : Set (EuclideanSpace ℝ (Fin (N : ℕ)))}
    (hΩb : Bornology.IsBounded Ω) (hΩo : IsOpen Ω) (hΩne : Ω.Nonempty)
    (hΩc : Convex ℝ Ω) (hΩ : Ω ⊆ particleChamber N)
    {ε : ℝ} (hε : 0 < ε)
    (ρ : Measure (EuclideanSpace ℝ (Fin (N : ℕ))))
    (hρ : ρ = (volume.restrict Ω).withDensity (fun x =>
      ENNReal.ofReal (Real.exp (-regularizedPotential χ ε x) /
        ∫ y in Ω, Real.exp (-regularizedPotential χ ε y))))
    {F : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (N : ℕ)) → gapTangentSpace N}
    (hFG : IsWeightedH1 ρ Ω F (fun x => (G x).val)) :
    IsProbabilityMeasure ρ ∧
      (∫ x, (F x - ∫ y, F y ∂ρ) ^ 2 ∂ρ) ≤
        ∫ x, sSup (Set.range fun u : gapTangentSpace N =>
          2 * ⟪G x, u⟫_ℝ - tangentHessian χ x u u) ∂ρ ∧
      Integrable (fun x => sSup (Set.range fun u : gapTangentSpace N =>
        2 * ⟪G x, u⟫_ℝ - tangentHessian χ x u u)) ρ ∧
      (∀ (x) (hx : x ∈ Ω), sSup (Set.range fun u : gapTangentSpace N =>
        2 * ⟪G x, u⟫_ℝ - tangentHessian χ x u u) =
          ⟪G x, (tangentHessian_coercive hc hχ (hΩ hx)).continuousLinearEquivOfBilin.symm
            (G x)⟫_ℝ) := by
  obtain ⟨_, _, hp, hv, _⟩ := euclidean_brascamp_lieb (by omega) hΩb hΩo hΩne hΩc
    ((regularizedPotential_contDiffOn hχ ε).of_le (by simp) |>.mono hΩ)
    (lt_min (by positivity) hε)
    (fun x hx u => regularized_hessian_lower hc hχ (hΩ hx) u) ρ hρ
  obtain ⟨hb, hi, _⟩ := hv F (fun x => (G x).val) hFG
  have ht x (hx : x ∈ Ω) :
      sSup (Set.range fun u : gapTangentSpace N =>
        2 * ⟪G x, u⟫_ℝ - tangentHessian χ x u u) =
          ⟪G x, (tangentHessian_coercive hc hχ (hΩ hx)).continuousLinearEquivOfBilin.symm
            (G x)⟫_ℝ :=
    Riesz1.bl_quadratic_sSup_eq_inverse (tangentHessian_coercive hc hχ (hΩ hx))
      (tangentHessian_symm hχ (hΩ hx)) (G x)
  have hae : ∀ᵐ x ∂ρ, x ∈ Ω := by
    rw [hρ]
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hΩo.measurableSet)
  have he : (fun x => sSup (Set.range fun u : EuclideanSpace ℝ (Fin (N : ℕ)) =>
      2 * ⟪(G x).val, u⟫_ℝ - fderiv ℝ (fderiv ℝ (regularizedPotential χ ε)) x u u)) =ᵐ[ρ]
      fun x => sSup (Set.range fun u : gapTangentSpace N =>
        2 * ⟪G x, u⟫_ℝ - tangentHessian χ x u u) := by
    filter_upwards [hae] with x hx
    exact (regularized_variational_eq_tangent_inverse hc hχ hε.le (hΩ hx) (G x)).trans
      (ht x hx).symm
  exact ⟨hp, (integral_congr_ae he) ▸ hb, hi.congr he, ht⟩

end Internal

end Riesz2.ConditionalParticleBrascampLieb
