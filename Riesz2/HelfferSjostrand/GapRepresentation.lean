/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.AffineMetricPart2
public import Riesz2.HelfferSjostrand.DifferentiatedPoissonPart3
public import Riesz2.Frozen.GapMultiplierField
public import Riesz2.Frozen.ZeroSumComponents
public import Mathlib.Probability.Moments.Covariance

/-!
# Intrinsic gap Poisson representation

Bridges for Proposition 3.3, using the intrinsic gap law, scalar form and ambient component conventions.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped BigOperators RealInnerProductSpace ContDiff

namespace Riesz2.GapRepresentation

open AffineMetric IntrinsicScalarCore

variable {N : ℕ+}

/-- Convexity of the domain used in Proposition 3.3.
The affine gap map transports the existing convex quotient chamber. -/
theorem domain_convex (N : ℕ+) : Convex ℝ (intrinsicGapDomain N) := by
  have hQ : Convex ℝ {z : gapTangentSpace N | z.val ∈ particleChamber N} :=
    (Riesz1.convex_hsChamber N).linear_preimage (gapTangentSpace N).subtype
  have hh := (hQ.linear_image (gapLinearEquiv N).toLinearEquiv.toLinearMap).translate
    (gapOffset N)
  convert hh using 1
  have he : (fun z : gapTangentSpace N =>
      gapOffset N + (gapLinearEquiv N) z) = intrinsicParticleGapMap N := by
    funext z
    rw [intrinsicParticleGapMap_eq, add_comm]
  simp only [image_image]
  change intrinsicGapDomain N = (fun z => gapOffset N + gapLinearEquiv N z) '' _
  rw [he]
  exact (intrinsicParticleGapMap_bijOn N).image_eq.symm

/-- Boundedness of the domain used in Proposition 3.3.
This uses the actual affine gap map, without choosing a nonisometric chart. -/
theorem domain_bounded (N : ℕ+) : Bornology.IsBounded (intrinsicGapDomain N) := by
  have hQ : Bornology.IsBounded {z : gapTangentSpace N | z.val ∈ particleChamber N} := by
    have hh := (orthTangentEquiv N).isometry.lipschitzWith.isBounded_image
      (Riesz1.isBounded_hsRadialDomain N)
    convert hh using 1
    ext z
    constructor
    · intro hz
      exact ⟨(orthTangentEquiv N).symm z, hz, (orthTangentEquiv N).apply_symm_apply z⟩
    · rintro ⟨w, hw, rfl⟩
      exact hw
  have hh := (gapLinearEquiv N).toContinuousLinearMap.lipschitzWith.isBounded_image hQ
  have ht := (isometry_add_right (gapOffset N)).lipschitzWith.isBounded_image hh
  convert ht using 1
  rw [image_image]
  change intrinsicGapDomain N = (fun z => gapLinearEquiv N z + gapOffset N) '' _
  simp only [← intrinsicParticleGapMap_eq]
  exact (intrinsicParticleGapMap_bijOn N).image_eq.symm

/-- Positive intrinsic dimension in Proposition 3.3 follows
from `N ≥ 2`. It is not an extra assumption on the gap law. -/
theorem tangent_nontrivial (hN : 2 ≤ (N : ℕ)) : Nontrivial (gapTangentSpace N) := by
  let i : Fin (N : ℕ) := ⟨0, by omega⟩
  let j : Fin (N : ℕ) := ⟨1, by omega⟩
  obtain ⟨r, hr, _⟩ := exists_pairSeparationVector i j (by change 0 < 1; omega)
  have hr0 : r ≠ 0 := by
    intro he
    rw [he, norm_zero, zero_pow (by omega)] at hr
    norm_num at hr
  exact ⟨⟨r, 0, hr0⟩⟩

/-- The actual centered microscopic gap map in Proposition 3.3
is measurable. Its law is exactly the `intrinsicGapLaw`. -/
theorem measurable_gap_chart (N : ℕ+) :
    Measurable (fun X : Riesz1.Configuration N =>
      centeredGapChart N (WithLp.toLp 2 (gapVector X))) := by
  have hc : Continuous (centeredGapChart N) := by
    exact Continuous.subtype_mk (by
      change Continuous (fun x : EuclideanSpace ℝ (Fin (N : ℕ)) =>
        WithLp.toLp 2 (fun i => x i - (∑ j, x j) / (N : ℝ)))
      fun_prop) _
  exact hc.measurable.comp
    ((WithLp.measurable_toLp 2 _).comp (Riesz1.measurable_gapVector N))

/-- Pullback preserves L² for the exact gap law, as used in Proposition 3.3. No chosen representative needs to be everywhere measurable. -/
theorem memLp_pullback {μ : Measure (Riesz1.Configuration N)}
    (G : Lp ℝ 2 (intrinsicGapLaw μ)) :
    MemLp (fun X : Riesz1.Configuration N =>
      G (centeredGapChart N (WithLp.toLp 2 (gapVector X)))) 2 μ := by
  exact (Lp.memLp G).comp_measurePreserving
    ⟨measurable_gap_chart N, rfl⟩

/-- Variance is preserved by the gap pushforward in Proposition 3.3, for every L² observable. -/
theorem variance_pullback {μ : Measure (Riesz1.Configuration N)}
    (G : Lp ℝ 2 (intrinsicGapLaw μ)) :
    ProbabilityTheory.variance (fun X : Riesz1.Configuration N =>
      G (centeredGapChart N (WithLp.toLp 2 (gapVector X)))) μ =
      ProbabilityTheory.variance G (intrinsicGapLaw μ) :=
  (ProbabilityTheory.variance_map (Lp.aestronglyMeasurable G).aemeasurable
    (measurable_gap_chart N).aemeasurable).symm

/-- Extract an ambient component of an intrinsic L² field for Proposition 3.3. This is the existing continuous linear L² functor
applied to the canonical tangent inclusion and coordinate projection. -/
def tangentCoordinateLp {ρ : Measure (gapTangentSpace N)} (i : Fin (N : ℕ)) :
    Lp (gapTangentSpace N) 2 ρ →L[ℝ] Lp ℝ 2 ρ :=
  ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (N : ℕ) => ℝ) i).comp
    (gapTangentSpace N).subtypeL).compLpL 2 ρ

/-- The component map used in Proposition 3.3 has precisely
the pointwise coordinates of the original intrinsic gradient, modulo null sets. -/
theorem tangentCoordinateLp_ae {ρ : Measure (gapTangentSpace N)}
    (i : Fin (N : ℕ)) (g : Lp (gapTangentSpace N) 2 ρ) :
    tangentCoordinateLp i g =ᵐ[ρ] fun x => (g x).val i :=
  ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (N : ℕ) => ℝ) i).comp
    (gapTangentSpace N).subtypeL).coeFn_compLpL g

/-- The ambient component tuple of every intrinsic L² field is tangent,
as required in Proposition 3.3. -/
theorem tangentCoordinateLp_zeroSum {ρ : Measure (gapTangentSpace N)}
    (g : Lp (gapTangentSpace N) 2 ρ) :
    ∀ᵐ x ∂ρ, (fun i => tangentCoordinateLp i g x) ∈ zeroSumComponents (Fin (N : ℕ)) := by
  filter_upwards [ae_all_iff.mpr (fun i => tangentCoordinateLp_ae i g)] with x hx
  change (∑ i, tangentCoordinateLp i g x) = 0
  simp only [hx]
  exact (g x).property

/-- The ambient sum of component pairings is the intrinsic L² pairing,
Proposition 3.3. No dimension-dependent scale occurs. -/
theorem tangentCoordinateLp_inner {ρ : Measure (gapTangentSpace N)}
    (g h : Lp (gapTangentSpace N) 2 ρ) :
    (∑ i, inner ℝ (tangentCoordinateLp i g) (tangentCoordinateLp i h)) = inner ℝ g h := by
  have hi (i : Fin (N : ℕ)) : Integrable
      (fun x => tangentCoordinateLp i g x * tangentCoordinateLp i h x) ρ :=
    (Lp.memLp (tangentCoordinateLp i g)).integrable_mul (Lp.memLp (tangentCoordinateLp i h))
  simp_rw [L2.inner_def, Real.inner_apply]
  rw [← integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr (fun i => tangentCoordinateLp_ae i g),
    ae_all_iff.mpr (fun i => tangentCoordinateLp_ae i h)] with x hx hy
  change (∑ i, tangentCoordinateLp i g x * tangentCoordinateLp i h x) =
    inner ℝ (g x).val (h x).val
  simp only [hx, hy, PiLp.inner_apply, Real.inner_apply]

/-- Every pair-separation argument of the ambient gap potential is strictly
inside `(0,1)` on the simplex, Proposition 3.3.
In particular no totalized derivative at a collision is used. -/
theorem pair_argument_mem (z : gapTangentSpace N) (hz : z ∈ intrinsicGapDomain N)
    (p : {p : Fin (N : ℕ) × Fin (N : ℕ) // p.1 < p.2}) :
    ((∑ a ∈ Finset.univ.filter
      (fun a : Fin (N : ℕ) => p.val.1.val ≤ a.val ∧ a.val < p.val.2.val),
      (1 + z.val a)) / (N : ℝ)) ∈ Ioo (0 : ℝ) 1 := by
  classical
  let S := Finset.univ.filter (fun a : Fin (N : ℕ) =>
    p.val.1.val ≤ a.val ∧ a.val < p.val.2.val)
  have hs : (∑ a, (1 + z.val a)) = (N : ℝ) := by
    rw [Finset.sum_add_distrib, show ∑ a, z.val a = 0 from z.property]
    simp
  have hpos : 0 < ∑ a ∈ S, (1 + z.val a) := by
    apply Finset.sum_pos (fun i _ => hz i)
    exact ⟨p.val.1, by simp [S, p.property]⟩
  have hlt : (∑ a ∈ S, (1 + z.val a)) < N := by
    rw [← hs]
    apply Finset.sum_lt_sum_of_subset (Finset.filter_subset _ _) (Finset.mem_univ p.val.2)
      (by simp) (hz p.val.2) (fun a _ _ => (hz a).le)
  exact ⟨div_pos hpos (by positivity), (div_lt_one (by positivity)).mpr hlt⟩

/-- Smoothness at every actual simplex point of the ambient extension,
Proposition 3.3. This assertion is stronger than smoothness
of its restriction to the tangent space and is needed for normal distributions. -/
theorem ambientPotential_contDiffAt {hN : 2 ≤ (N : ℕ)}
    {χ : ParticlePairData N} {c : ℝ} (hχ : AdmissibleParticlePairs hN χ c)
    {z : gapTangentSpace N} (hz : z ∈ intrinsicGapDomain N) :
    ContDiffAt ℝ (⊤ : ℕ∞) (pairAmbientGapPotential χ)
      (WithLp.toLp 2 (fun i => 1 + z.val i)) := by
  unfold pairAmbientGapPotential
  refine contDiffAt_const.mul ?_
  apply ContDiffAt.sum
  intro p _
  let a : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ := fun y =>
    (∑ i ∈ Finset.univ.filter
      (fun i : Fin (N : ℕ) => p.val.1.val ≤ i.val ∧ i.val < p.val.2.val), y i) / (N : ℝ)
  have ha : ContDiff ℝ (⊤ : ℕ∞) a := by
    dsimp only [a]
    apply ContDiff.div_const
    apply ContDiff.sum
    intro i _
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (N : ℕ) => ℝ) i).contDiff
  change ContDiffAt ℝ ∞ (χ p ∘ a) (WithLp.toLp 2 (fun i => 1 + z.val i))
  exact ContDiffAt.comp (f := a) _
    ((hχ.1 p).1.contDiffAt (isOpen_Ioo.mem_nhds (pair_argument_mem z hz p))) ha.contDiffAt

/-- The actual ambient Hessian entries vary continuously on the intrinsic
simplex, Proposition 3.3. This gives exactly the local
coefficient regularity required for compact-test multiplier integrability. -/
theorem ambientHessian_continuousOn {hN : 2 ≤ (N : ℕ)}
    {χ : ParticlePairData N} {c : ℝ} (hχ : AdmissibleParticlePairs hN χ c)
    (i j : Fin (N : ℕ)) :
    ContinuousOn (fun z : gapTangentSpace N =>
      hessianMatrix (pairAmbientGapPotential χ) (WithLp.toLp 2 (fun k => 1 + z.val k)) i j)
      (intrinsicGapDomain N) := by
  intro z hz
  let y : EuclideanSpace ℝ (Fin (N : ℕ)) := WithLp.toLp 2 (fun k => 1 + z.val k)
  have hs := ambientPotential_contDiffAt hχ hz
  have hg : ContDiffAt ℝ (⊤ : ℕ∞) (gradient (pairAmbientGapPotential χ)) y :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin (N : ℕ)))).symm.contDiff.contDiffAt.comp y
      (hs.fderiv_right (m := ∞) (by simp))
  have hd := ((hg.fderiv_right (m := ∞) (by simp)).clm_apply
    (contDiffAt_const (c := EuclideanSpace.single j 1))).continuousAt
  have hp : ContinuousAt (fun x : EuclideanSpace ℝ (Fin (N : ℕ)) =>
      (fderiv ℝ (gradient (pairAmbientGapPotential χ)) x (EuclideanSpace.single j 1)) i) y :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (N : ℕ) => ℝ) i).continuous.continuousAt.comp hd
  have hl : Continuous (fun z : gapTangentSpace N =>
      (WithLp.toLp 2 (fun k => 1 + z.val k) : EuclideanSpace ℝ (Fin (N : ℕ)))) := by
    fun_prop
  have he : ContinuousAt (fun z : gapTangentSpace N =>
      (fderiv ℝ (gradient (pairAmbientGapPotential χ))
        (WithLp.toLp 2 (fun k => 1 + z.val k)) (EuclideanSpace.single j 1)) i) z :=
    ContinuousAt.comp (f := fun z : gapTangentSpace N =>
      (WithLp.toLp 2 (fun k => 1 + z.val k) : EuclideanSpace ℝ (Fin (N : ℕ))))
      (g := fun x : EuclideanSpace ℝ (Fin (N : ℕ)) =>
        (fderiv ℝ (gradient (pairAmbientGapPotential χ)) x (EuclideanSpace.single j 1)) i)
      hp hl.continuousAt
  exact he.continuousWithinAt

/-- The ambient Hessian restricts to the intrinsic Hessian, Proposition 3.3. The affine chart has isometric linear part given by
the canonical tangent inclusion. -/
theorem ambientHessian_tangent_pair {hN : 2 ≤ (N : ℕ)}
    {χ : ParticlePairData N} {c : ℝ} (hχ : AdmissibleParticlePairs hN χ c)
    {z : gapTangentSpace N} (hz : z ∈ intrinsicGapDomain N)
    (u v : gapTangentSpace N) :
    fderiv ℝ (fderiv ℝ (fun z : gapTangentSpace N =>
      pairAmbientGapPotential χ (WithLp.toLp 2 (fun i => 1 + z.val i)))) z u v =
      ∑ i, ∑ j, u.val i *
        hessianMatrix (pairAmbientGapPotential χ) (WithLp.toLp 2 (fun k => 1 + z.val k)) i j *
          v.val j := by
  let a : EuclideanSpace ℝ (Fin (N : ℕ)) := WithLp.toLp 2 (fun _ => 1)
  have hs : ContDiffAt ℝ 2 (pairAmbientGapPotential χ)
      ((gapTangentSpace N).subtypeL z + a) := by
    convert (ambientPotential_contDiffAt hχ hz).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ ∞) using 1
    ext i
    simp only [Submodule.subtypeL_apply, PiLp.add_apply, a]
    ring
  have he := AffineMetricTransport.hessian_comp_affine (gapTangentSpace N).subtypeL a hs u v
  have hf : (fun z : gapTangentSpace N =>
      pairAmbientGapPotential χ ((gapTangentSpace N).subtypeL z + a)) =
      (fun z => pairAmbientGapPotential χ (WithLp.toLp 2 (fun i => 1 + z.val i))) := by
    funext z
    congr 1
    ext i
    simp only [Submodule.subtypeL_apply, PiLp.add_apply, a]
    ring
  rw [hf] at he
  have ha : (gapTangentSpace N).subtypeL z + a = WithLp.toLp 2 (fun i => 1 + z.val i) := by
    ext i
    simp only [Submodule.subtypeL_apply, PiLp.add_apply, a]
    ring
  rw [he, ha]
  exact Intrinsic.hessianMatrix_bilinear (ambientPotential_contDiffAt hχ hz) u.val v.val

/-- The ambient matrix on the actual gap domain is symmetric, Proposition 3.3. This is the symmetry required by the normal multiplier
formula with the left-vector matrix-pairing convention. -/
theorem ambientHessian_symmetric {hN : 2 ≤ (N : ℕ)}
    {χ : ParticlePairData N} {c : ℝ} (hχ : AdmissibleParticlePairs hN χ c)
    {z : gapTangentSpace N} (hz : z ∈ intrinsicGapDomain N)
    (i j : Fin (N : ℕ)) :
    hessianMatrix (pairAmbientGapPotential χ) (WithLp.toLp 2 (fun k => 1 + z.val k)) i j =
      hessianMatrix (pairAmbientGapPotential χ) (WithLp.toLp 2 (fun k => 1 + z.val k)) j i := by
  have hs := ambientPotential_contDiffAt hχ hz
  simp only [Intrinsic.hessianMatrix_eq_second hs]
  exact hs.isSymmSndFDerivAt (by simp) _ _

/-- Strict positivity of the actual compressed ambient matrix, Proposition 3.3, with the exact curvature scale `c/(2N)`. -/
theorem ambientHessian_tangent_lower {hN : 2 ≤ (N : ℕ)}
    {χ : ParticlePairData N} {c : ℝ} (hc : 0 < c)
    (hχ : AdmissibleParticlePairs hN χ c)
    {z : gapTangentSpace N} (hz : z ∈ intrinsicGapDomain N) (u : gapTangentSpace N) :
    c / (2 * (N : ℝ)) * ‖u‖ ^ 2 ≤
      ∑ i, ∑ j, u.val i *
        hessianMatrix (pairAmbientGapPotential χ) (WithLp.toLp 2 (fun k => 1 + z.val k)) i j *
          u.val j := by
  rw [← ambientHessian_tangent_pair hχ hz]
  exact intrinsicGapPotential_curvature hc hχ hz u

section Scalar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ρ : Measure E} {Ω : Set E} {V : E → ℝ}

omit [BorelSpace E] in
/-- Internal covariance bridge for Proposition 3.3.
The scalar Poisson predicate and Neumann realization imply
covariance against every Sobolev test and every representative of its gradient. -/
theorem covariance_of_scalar_solution [IsProbabilityMeasure ρ]
    (Q : ScalarFormData ρ) (hQ : IsNeumannRealization Ω Q)
    (G ψ : Q.1) (hψ : ScalarPoissonSolution Q G ψ)
    (gψ : Lp E 2 ρ) (hgψ : (ψ.val, gψ) ∈ neumannSobolevGraph ρ Ω)
    (K : Q.1) (gK : Lp E 2 ρ) (hgK : (K.val, gK) ∈ neumannSobolevGraph ρ Ω) :
    Integrable K.val ρ ∧ ProbabilityTheory.covariance G.val K.val ρ = inner ℝ gK gψ := by
  refine ⟨(Lp.memLp K.val).integrable one_le_two, ?_⟩
  rw [DifferentiatedPoisson.covariance_eq_centered_inner,
    Riesz1.poisson_inner_eq_integral]
  have hae := (Riesz1.poissonCenter_ae ρ G.val).mono
    (fun x hx => congrArg (· * K.val x) hx)
  rw [integral_congr_ae hae, ← (hψ.2.2.2 K).2,
    hQ.2.2 ψ K gψ gK hgψ hgK, real_inner_comm]

/-- Scalar-form characterization for Proposition 3.3:
scalar Poisson solutions are exactly mean-zero pairs in the existing generator
graph. This is used when applying differentiated graph-limit results. -/
theorem scalar_solution_iff_graph (hΩ : IsOpen Ω) (hB : Bornology.IsBounded Ω)
    (hV : IsEuclideanGibbsPotential volume ρ Ω V)
    (G ψ : (form hΩ hB hV).1) :
    ScalarPoissonSolution (form hΩ hB hV) G ψ ↔
      (∫ x, ψ.val x ∂ρ) = 0 ∧
      (ψ.val, @Riesz1.poissonCenter E _ ρ (probability hV) G.val) ∈
        (operator hΩ hB hV).graph := by
  have := probability hV
  constructor
  · intro hψ
    refine ⟨hψ.2.2.1, (graph_iff hΩ hB hV _ _).mpr ⟨ψ.property, fun h => ?_⟩⟩
    rw [(hψ.2.2.2 h).2, Riesz1.poisson_inner_eq_integral]
    apply integral_congr_ae
    exact (Riesz1.poissonCenter_ae ρ G.val).symm.mono
      (fun x hx => congrArg (· * h.val x) hx)
  · rintro ⟨hm, hψ⟩
    obtain ⟨hG, hi, hdom, hw⟩ :=
      IntrinsicScalarPoisson.weak_identities hΩ hB hV G.val ψ.val hψ
    exact ⟨hG, hi, hm, hw⟩

/-- Every smooth compact ambient test tuple has representatives in the native
scalar form carrier, Proposition 3.3. Their gradients are
also supplied in the graph. Thus constructing the ambient tests
does not require any extra regularity hypothesis on a vector solution. -/
theorem compact_test_representatives {ι : Type*} [Fintype ι]
    (hΩ : IsOpen Ω) (hB : Bornology.IsBounded Ω)
    (hV : IsEuclideanGibbsPotential volume ρ Ω V) (h : ι → E → ℝ)
    (hh : ∀ i, ContDiff ℝ ∞ (h i) ∧ HasCompactSupport (h i) ∧ tsupport (h i) ⊆ Ω) :
    ∃ k : ι → (form hΩ hB hV).1,
      (∀ᵐ x ∂ρ, ∀ i, (k i).val x = h i x) ∧
      ∀ i, ∃ g : Lp E 2 ρ, ((k i).val, g) ∈ neumannSobolevGraph ρ Ω ∧
        g =ᵐ[ρ] gradient (h i) := by
  have := probability hV
  let J := jet hΩ hB hV
  let f : ι → compactTests Ω := fun i =>
    ⟨⟨h i, univ, isOpen_univ, subset_univ _, (hh i).1.contDiffOn⟩, hh i⟩
  let k : ι → (form hΩ hB hV).1 := fun i =>
    ScalarForm.valueEquiv J (value_injective hΩ hB hV) (ScalarForm.ofCore J (f i).val)
  have hk (i) : (k i).val =ᵐ[ρ] h i := (Riesz1.WeightedSobolev.memLp_of_smoothNearClosure hB
    (supported hΩ hV) (f i).val.property).1.coeFn_toLp
  refine ⟨k, ae_all_iff.mpr hk, fun i => ?_⟩
  let g := ScalarForm.deriv J (ScalarForm.ofCore J (f i).val)
  refine ⟨g, ?_, (Riesz1.WeightedSobolev.memLp_of_smoothNearClosure hB
    (supported hΩ hV) (f i).val.property).2.coeFn_toLp⟩
  apply (EuclideanScalarForm.mem_neumannSobolevGraph_iff hΩ hB (supported hΩ hV) _ _).mpr
  exact (ScalarForm.ofCore J (f i).val).property

end Scalar

/-- The scalar part of Proposition 3.3 for the stated pair-potential class.
The gap law has a conservative intrinsic Neumann realization. Every H¹
source has a unique centered scalar solution with tangent weak gradient,
covariance against every H¹ test, and the particle variance representation. -/
theorem scalar_gap_representation
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (c : ℝ) (hc : 0 < c)
    (χ : ParticlePairData N) (hχ : AdmissibleParticlePairs hN χ c) :
    ∃ (hMeas : Measurable (fun X : Riesz1.Configuration N =>
        ENNReal.ofReal (Real.exp (-particlePairEnergy χ (WithLp.toLp 2 X.val)))))
      (hZ : 0 < pairGibbsNormalizer χ ∧ pairGibbsNormalizer χ < ⊤),
      let μ := pairGibbsMeasure χ hMeas hZ
      let ν := intrinsicGapLaw μ
      let Ω := intrinsicGapDomain N
      IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧
      ∃ Q : ScalarFormData ν,
        IsEuclideanGibbsPotential volume ν Ω
          (fun z => pairAmbientGapPotential χ (WithLp.toLp 2 (fun i => 1 + z.val i))) ∧
        IsNeumannRealization Ω Q ∧ IsConservativeScalarForm Q ∧
        ∀ G : Q.1, ∃ (gG : Lp (gapTangentSpace N) 2 ν)
          (v : Fin (N : ℕ) → Lp ℝ 2 ν),
          (G.val, gG) ∈ neumannSobolevGraph ν Ω ∧
          (∀ᵐ z ∂ν, ∀ i, v i z = (gG z).val i) ∧
          (∀ᵐ z ∂ν, (fun i => v i z) ∈ zeroSumComponents (Fin (N : ℕ))) ∧
          (∃! ψ : Q.1, ScalarPoissonSolution Q G ψ) ∧
          ∀ ψ : Q.1, ScalarPoissonSolution Q G ψ →
          ∃ gψ : Lp (gapTangentSpace N) 2 ν,
            (ψ.val, gψ) ∈ neumannSobolevGraph ν Ω ∧
            MemLp (fun X : Riesz1.Configuration N =>
              G.val (centeredGapChart N (WithLp.toLp 2 (gapVector X)))) 2 μ ∧
            ProbabilityTheory.variance (fun X : Riesz1.Configuration N =>
              G.val (centeredGapChart N (WithLp.toLp 2 (gapVector X)))) μ =
                ∑ i, inner ℝ (v i) (tangentCoordinateLp i gψ) ∧
            ∀ (K : Q.1) (gK : Lp (gapTangentSpace N) 2 ν),
              (K.val, gK) ∈ neumannSobolevGraph ν Ω →
              Integrable K.val ν ∧
              ProbabilityTheory.covariance G.val K.val ν = inner ℝ gK gψ := by
  have := tangent_nontrivial hN
  let hm := pairGibbsWeight_measurable hχ
  let hZ := (particle_hessian_normalization hN c hc χ hχ).1
  let μ := pairGibbsMeasure χ hm hZ
  let ν := intrinsicGapLaw μ
  have hp : IsProbabilityMeasure μ := by
    rw [show μ = (Riesz1.hsGibbsProbability (libraryPairs hχ) hc : Measure _) from
      pairGibbsMeasure_eq_library hc hχ]
    infer_instance
  have hV := intrinsicGapLaw_gibbsPotential hN c hc χ hχ
  have hν : IsProbabilityMeasure ν := probability hV
  have := hν
  let hΩ := intrinsicGapDomain_isOpen N
  let hB := domain_bounded N
  let Q := form hΩ hB hV
  have hQ : IsNeumannRealization (intrinsicGapDomain N) Q := realization hΩ hB hV
  refine ⟨hm, hZ, hp, hν, Q, hV, hQ, conservative hΩ hB hV, fun G => ?_⟩
  obtain ⟨gG, hgG⟩ := (hQ.1 G.val).mp G.property
  have hκ : 0 < c / (2 * (N : ℝ)) := div_pos hc (by positivity)
  have hsol := IntrinsicScalarPoisson.scalarPoissonSolution_existsUnique hΩ hB
    (domain_convex N) hV hκ (fun _ hy => intrinsicGapPotential_curvature hc hχ hy) G
  refine ⟨gG, fun i => tangentCoordinateLp i gG, hgG,
    ae_all_iff.mpr (fun i => tangentCoordinateLp_ae i gG),
    tangentCoordinateLp_zeroSum gG, hsol, fun ψ hψ => ?_⟩
  obtain ⟨gψ, hgψ⟩ := (hQ.1 ψ.val).mp ψ.property
  have hcov := covariance_of_scalar_solution Q hQ G ψ hψ gψ hgψ
  refine ⟨gψ, hgψ, memLp_pullback G.val, ?_, hcov⟩
  rw [variance_pullback G.val, tangentCoordinateLp_inner]
  exact (ProbabilityTheory.covariance_self (Lp.aestronglyMeasurable G.val).aemeasurable).symm.trans (hcov G gG hgG).2

end Riesz2.GapRepresentation
