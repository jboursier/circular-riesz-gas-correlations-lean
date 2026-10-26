/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.CutoffApproximation
public import Riesz2.ToMathlib.VectorRadialComposition
public import Riesz2.HelfferSjostrand.GapRepresentationPart3
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Scalar observables of affine coordinates

The a.e. derivative of a real Lipschitz function pulls back to its actual
weighted Sobolev gradient when the affine coordinate has an absolutely
continuous marginal. This is the chain rule used in Theorem 2. No smoothness of the scalar observable is required.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set
open scoped NNReal
open scoped BigOperators

namespace Riesz2.AffineObservableSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsFiniteMeasure μ] {U : Set E}

omit [IsFiniteMeasure μ] in
/-- Affine-coordinate chain rule for the a.e. derivative representative in
Theorem 2. Absolute continuity is needed only for the
one-dimensional coordinate marginal. -/
theorem gradient_comp_ae (ℓ : E →L[ℝ] ℝ) (a : ℝ) {f f' : ℝ → ℝ}
    (hd : ∀ᵐ t ∂volume, HasDerivAt f (f' t) t)
    (hcoord : μ.map (fun x => ℓ x + a) ≪ volume) :
    gradient (fun x => f (ℓ x + a)) =ᵐ[μ]
      fun x => f' (ℓ x + a) • (InnerProductSpace.toDual ℝ E).symm ℓ := by
  have hm : Measurable (fun x => ℓ x + a) := (ℓ.continuous.add_const a).measurable
  have hp := ae_of_ae_map hm.aemeasurable (hcoord.ae_le hd)
  filter_upwards [hp] with x hx
  have hh := hx.comp_hasFDerivAt x (ℓ.hasFDerivAt.add_const a)
  simpa only [map_smul, Function.comp_def] using hh.hasGradientAt.gradient

/-- A Lipschitz scalar observable of an affine coordinate belongs to the
weighted H¹ space with its selected a.e. derivative, as required in the last
paragraph of Theorem 2. -/
theorem weightedH1_comp (hU : Bornology.IsBounded U)
    (hμ : ∀ᵐ x ∂μ, x ∈ U) (hac : μ ≪ volume)
    (ℓ : E →L[ℝ] ℝ) (a : ℝ) {f f' : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f)
    (hd : ∀ᵐ t ∂volume, HasDerivAt f (f' t) t)
    (hcoord : μ.map (fun x => ℓ x + a) ≪ volume) :
    Riesz1.WeightedSobolev.IsWeightedH1 μ U (fun x => f (ℓ x + a))
      (fun x => f' (ℓ x + a) • (InnerProductSpace.toDual ℝ E).symm ℓ) := by
  have hℓ : LipschitzWith ‖ℓ‖₊ (fun x => ℓ x + a) := fun x y => by
    simpa only [edist_add_right] using ℓ.lipschitzWith x y
  have hF : LipschitzWith (L * ‖ℓ‖₊) (fun x => f (ℓ x + a)) := hf.comp hℓ
  exact (Riesz1.WeightedSobolev.isWeightedH1_of_lipschitz hU hμ hac hF).congr
    EventuallyEq.rfl (gradient_comp_ae ℓ a hd hcoord)

/-- The affine-coordinate chain rule as membership in the literal Neumann graph (Subsection 4.1, used by Theorem 2). -/
theorem neumannGraph_comp (hU : Bornology.IsBounded U)
    (hμ : ∀ᵐ x ∂μ, x ∈ U) (hac : μ ≪ volume)
    (ℓ : E →L[ℝ] ℝ) (a : ℝ) {f f' : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f)
    (hd : ∀ᵐ t ∂volume, HasDerivAt f (f' t) t)
    (hcoord : μ.map (fun x => ℓ x + a) ≪ volume) :
    ∃ (hF : MemLp (fun x => f (ℓ x + a)) 2 μ)
      (hD : MemLp (fun x => f' (ℓ x + a) •
        (InnerProductSpace.toDual ℝ E).symm ℓ) 2 μ),
      (hF.toLp _, hD.toLp _) ∈ neumannSobolevGraph μ U := by
  have hh := weightedH1_comp hU hμ hac ℓ a hf hd hcoord
  exact ⟨hh.1, hh.2.1,
    (VectorRadial.isWeightedH1_iff_neumannSobolevGraph hU hμ hh.1 hh.2.1).mp hh⟩

end Riesz2.AffineObservableSobolev

namespace Riesz2.AffineObservableSobolev

open IntrinsicScalarCore

variable {d : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))}
  {μ : Measure (EuclideanSpace ℝ (Fin d))} {V : EuclideanSpace ℝ (Fin d) → ℝ}

/-- The Riesz representative of a Euclidean coordinate is its unit vector.
This identifies the point source used in Theorem 2. -/
theorem coordinate_dual (i : Fin d) :
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm
      (EuclideanSpace.proj i) = EuclideanSpace.single i 1 := by
  apply (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  ext x
  change x i = inner ℝ (EuclideanSpace.single i 1) x
  simp only [EuclideanSpace.inner_single_left, map_one, one_mul]

/-- Internal covariance representation for a Euclidean coordinate observable
in Theorem 2. The analytic premises are the established
Gibbs, curvature and collision-barrier interfaces, rather than a covariance
bound. The conclusion gives the actual point-source weak equation. -/
theorem internal_coordinate_covariance (hdim : 1 ≤ d)
    (hU : IsOpen U) (hB : Bornology.IsBounded U) (hc : Convex ℝ U)
    (hV : IsEuclideanGibbsPotential volume μ U V) {κ : ℝ} (hκ : 0 < κ)
    (hH : ∀ x ∈ U, ∀ e, κ * ‖e‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x e e)
    {C : ℝ} (hC : 0 ≤ C)
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹ ^ 2 - C ≤
      ‖gradient V x‖ ^ 2 / 4 - Laplacian.laplacian V x / 2)
    (i j : Fin d) {f f' g g' : ℝ → ℝ} {Lf Lg : ℝ≥0}
    (hf : LipschitzWith Lf f) (hg : LipschitzWith Lg g)
    (hfd : ∀ᵐ t ∂volume, HasDerivAt f (f' t) t)
    (hgd : ∀ᵐ t ∂volume, HasDerivAt g (g' t) t)
    (hi : μ.map (fun x => x i) ≪ volume) (hj : μ.map (fun x => x j) ≪ volume) :
    ∃ (χ η : Lp ℝ 2 μ),
      χ =ᵐ[μ] (fun x => f' (x i)) ∧ η =ᵐ[μ] (fun x => g' (x j)) ∧
      MemLp (fun x => f (x i)) 2 μ ∧ MemLp (fun x => g (x j)) 2 μ ∧
      ∃ u : Fin d → (form hU hB hV).1,
        WeightedWeakSolution (form hU hB hV) (hessianMatrix V) ⊤
          (fun k => if k = i then χ else 0) u ∧
        ProbabilityTheory.covariance (fun x => f (x i)) (fun x => g (x j)) μ =
          inner ℝ η (u j).val := by
  have : NeZero d := ⟨by omega⟩
  have := probability hV
  have hac : μ ≪ volume := by
    have ha : μ ≪ volume.restrict U := by
      rw [hV.2.2.2]
      exact Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
    exact ha.trans (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  obtain ⟨hF, hDF, hgraphF⟩ := neumannGraph_comp hB (supported hU hV) hac
    (EuclideanSpace.proj i) 0 hf hfd (by simpa only [PiLp.proj_apply, add_zero] using hi)
  obtain ⟨hG, hDG, hgraphG⟩ := neumannGraph_comp hB (supported hU hV) hac
    (EuclideanSpace.proj j) 0 hg hgd (by simpa only [PiLp.proj_apply, add_zero] using hj)
  simp only [PiLp.proj_apply, add_zero, coordinate_dual] at hF hDF hgraphF hG hDG hgraphG
  let DF : Lp (EuclideanSpace ℝ (Fin d)) 2 μ :=
    hDF.toLp (fun x => f' (x i) • EuclideanSpace.single i 1)
  let DG : Lp (EuclideanSpace ℝ (Fin d)) 2 μ :=
    hDG.toLp (fun x => g' (x j) • EuclideanSpace.single j 1)
  let Q := form hU hB hV
  have hQ : IsNeumannRealization U Q := realization hU hB hV
  let F : Q.1 := ⟨hF.toLp _, hQ.1 _ |>.mpr ⟨DF, hgraphF⟩⟩
  let G : Q.1 := ⟨hG.toLp _, hQ.1 _ |>.mpr ⟨DG, hgraphG⟩⟩
  obtain ⟨ψ, hψ, _⟩ := IntrinsicScalarPoisson.scalarPoissonSolution_existsUnique
    hU hB hc hV hκ hH F
  obtain ⟨Dψ, hDψ⟩ := (hQ.1 ψ.val).mp ψ.property
  obtain ⟨u, hu, hcoord⟩ := NeumannDifferentiatedTransport.realized_gradient_equation
    hdim hU hB hV hκ hH hC hbar F ψ hψ DF Dψ hgraphF hDψ
  let χ := DifferentiatedPoisson.coordinateLp i DF
  let η := DifferentiatedPoisson.coordinateLp j DG
  have hχ : χ =ᵐ[μ] (fun x => f' (x i)) := by
    filter_upwards [DifferentiatedPoisson.coordinateLp_ae i DF, hDF.coeFn_toLp] with x hx hy
    change χ x = f' (x i)
    rw [hx, hy]
    simp only [PiLp.smul_apply, PiLp.single_apply, ite_true, smul_eq_mul, mul_one]
  have hη : η =ᵐ[μ] (fun x => g' (x j)) := by
    filter_upwards [DifferentiatedPoisson.coordinateLp_ae j DG, hDG.coeFn_toLp] with x hx hy
    change η x = g' (x j)
    rw [hx, hy]
    simp only [PiLp.smul_apply, PiLp.single_apply, ite_true, smul_eq_mul, mul_one]
  have hv : (fun k => DifferentiatedPoisson.coordinateLp k DF) =
      (fun k => if k = i then χ else 0) := by
    funext k
    by_cases hki : k = i
    · subst k
      simp only [ite_true]
      rfl
    · apply Lp.ext
      filter_upwards [DifferentiatedPoisson.coordinateLp_ae k DF, hDF.coeFn_toLp,
        Lp.coeFn_zero ℝ 2 μ] with x hx hy hz
      simp only [ite_eq_right hki]
      rw [hx, hy, hz]
      simp only [PiLp.smul_apply, PiLp.single_apply, ite_eq_right hki,
        smul_eq_mul, mul_zero, Pi.zero_apply]
  refine ⟨χ, η, hχ, hη, hF, hG, u, ?_, ?_⟩
  · simpa only [hv] using hu
  · have he := (GapRepresentation.covariance_of_scalar_solution Q hQ F ψ hψ
      Dψ hDψ G DG hgraphG).2
    have hcov : ProbabilityTheory.covariance F.val G.val μ =
        ProbabilityTheory.covariance (fun x => f (x i)) (fun x => g (x j)) μ := by
      unfold ProbabilityTheory.covariance
      rw [integral_congr_ae hF.coeFn_toLp, integral_congr_ae hG.coeFn_toLp]
      apply integral_congr_ae
      filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with x hx hy
      rw [hx, hy]
    rw [← hcov, he, L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hDG.coeFn_toLp, hη,
      DifferentiatedPoisson.coordinateLp_ae j Dψ] with x hx hy hz
    rw [hx, inner_smul_left, EuclideanSpace.inner_single_left, map_one, one_mul,
      Real.inner_apply, hy, hcoord j, hz]
    simp only [conj_trivial]

end Riesz2.AffineObservableSobolev
