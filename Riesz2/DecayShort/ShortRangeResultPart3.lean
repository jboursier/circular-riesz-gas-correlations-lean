/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.PhysicalDecayPart7
public import Riesz2.ToMathlib.AffineObservableSobolev
public import Riesz2.DecayShort.ObservableTransfer

/-!
# Constrained physical covariance representation

The full-cycle representation used in Theorem 2.
The Hessian is that of the physical ambient extension, and the
coordinate source is identified on the complete zero-sum test domain.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators RealInnerProductSpace Topology ContDiff ENNReal

namespace Riesz2.DecayShort.ShortRangeResultPart3

open IntrinsicScalarCore GapRepresentation AffineMetric
open NeumannDifferentiatedTransport RectangularFormTransport

/-- Internal uniqueness of the scalar realization, used in Theorem 2 to retain the physical decay theorem's scalar carrier. -/
theorem internal_realization_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E]
    {ν : Measure E} {U : Set E} {Q R : ScalarFormData ν}
    (hQ : IsNeumannRealization U Q) (hR : IsNeumannRealization U R) : Q = R := by
  obtain ⟨D, B⟩ := Q
  obtain ⟨D', B'⟩ := R
  have hD : D = D' := by
    ext f
    exact (hQ.1 f).trans (hR.1 f).symm
  subst D'
  congr 1
  ext f h
  obtain ⟨g, hg⟩ := (hQ.1 f.val).mp f.property
  obtain ⟨k, hk⟩ := (hQ.1 h.val).mp h.property
  exact (hQ.2.2 f h g k hg hk).trans (hR.2.2 f h g k hg hk).symm

variable {N : ℕ+} {d : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- Internal Hessian compression for Theorem 2, for
any smooth ambient potential on the physical domain. -/
theorem internal_hessian_compression
    (b : OrthonormalBasis (Fin d) ℝ (gapTangentSpace N))
    {W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ}
    (hW : ContDiffOn ℝ ∞ W (gapAmbientDomain N))
    {z : gapTangentSpace N} (hz : z ∈ intrinsicGapDomain N) :
    (tangentBasisMatrix b).transpose *
        hessianMatrix W (WithLp.toLp 2 (fun i => 1 + z.val i)) * tangentBasisMatrix b =
      hessianMatrix ((fun z : gapTangentSpace N =>
        W (WithLp.toLp 2 (fun i => 1 + z.val i))) ∘ b.repr.symm) (b.repr z) := by
  let Y := fun z : gapTangentSpace N => WithLp.toLp 2 (fun i => 1 + z.val i)
  let V := W ∘ Y
  have hx := PhysicalEnergy.simplex_subset_ambient N _
    (PhysicalCollision.intrinsic_chart_mem_simplex N hz)
  have hWs : ContDiffAt ℝ 2 W (Y z) :=
    (hW.of_le (by simp)).contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hx)
  have hVs : ContDiffOn ℝ ∞ V (intrinsicGapDomain N) := by
    exact hW.comp
      (PhysicalCollision.intrinsic_chart_contDiff N).contDiffOn
      (fun x hx => PhysicalEnergy.simplex_subset_ambient N _
        (PhysicalCollision.intrinsic_chart_mem_simplex N hx))
  have hchart : (fun x : gapTangentSpace N =>
      (gapTangentSpace N).subtypeL x + WithLp.toLp 2 (fun _ => (1 : ℝ))) = Y := by
    funext x
    ext i
    change x.val i + 1 = 1 + x.val i
    ring
  have hpair (u v : gapTangentSpace N) :
      fderiv ℝ (fderiv ℝ V) z u v =
        fderiv ℝ (fderiv ℝ W) (Y z) u.val v.val := by
    have hh := AffineMetricTransport.hessian_comp_affine
      (gapTangentSpace N).subtypeL (WithLp.toLp 2 (fun _ => (1 : ℝ)))
      (f := W) (x := z) (by rw [congrFun hchart z]; exact hWs) u v
    have hf : (fun x : gapTangentSpace N => W
        ((gapTangentSpace N).subtypeL x + WithLp.toLp 2 (fun _ => (1 : ℝ)))) = V :=
      congrArg (fun T => W ∘ T) hchart
    rw [hf, congrFun hchart z] at hh
    exact hh
  have hcomp : ContDiffAt ℝ ∞ (V ∘ b.repr.symm) (b.repr z) :=
    (hVs.contDiffAt (by simpa using (intrinsicGapDomain_isOpen N).mem_nhds hz)).comp _
      b.repr.symm.contDiff.contDiffAt
  ext a k
  change ((tangentBasisMatrix b).transpose * hessianMatrix W (Y z) * tangentBasisMatrix b) a k =
    hessianMatrix (V ∘ b.repr.symm) (b.repr z) a k
  rw [Intrinsic.hessianMatrix_eq_second hcomp,
    SobolevIsometry.hessian_comp_symm b.repr (intrinsicGapDomain_isOpen N) (hVs.of_le (by simp))
      (by simpa using hz), b.repr.symm_apply_apply,
    b.repr_symm_single, b.repr_symm_single, hpair]
  rw [Intrinsic.hessianMatrix_bilinear
    (hW.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hx))]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, tangentBasisMatrix, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The physical curvature and collision criterion apply to every realization
of the exact ambient value, including the witness supplied by physical decay.
This is the analytic application step of Theorem 2. -/
theorem internal_physical_criteria (p : Parameters) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) (h : ℝ) (b : Bool)
    (W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ)
    (hval : ∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
      W y.val = fullPhysicalPotentialValue p N hN θ h b y) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 ≤ C ∧
      (∀ z ∈ intrinsicGapDomain N, ∀ u : gapTangentSpace N,
        κ * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (fun z : gapTangentSpace N =>
          W (WithLp.toLp 2 (fun i => 1 + z.val i)))) z u u) ∧
      ∀ z ∈ intrinsicGapDomain N,
        (Metric.infDist z (frontier (intrinsicGapDomain N)))⁻¹ ^ 2 - C ≤
          ‖gradient (fun z : gapTangentSpace N =>
            W (WithLp.toLp 2 (fun i => 1 + z.val i))) z‖ ^ 2 / 4 -
          Laplacian.laplacian (fun z : gapTangentSpace N =>
            W (WithLp.toLp 2 (fun i => 1 + z.val i))) z / 2 := by
  obtain ⟨V, _, hv, κ, hκ, hcurv, hbar⟩ :=
    PhysicalCollision.fullPhysicalPotential_collision_criterion N p hN θ h b
  obtain ⟨D, hD, hd⟩ := hbar (1/2) 2 (by norm_num) (by norm_num)
  have he (z : gapTangentSpace N) (hz : z ∈ intrinsicGapDomain N) :
      (fun z : gapTangentSpace N => W (WithLp.toLp 2 (fun i => 1 + z.val i))) =ᶠ[𝓝 z]
        (fun z : gapTangentSpace N => V (WithLp.toLp 2 (fun i => 1 + z.val i))) := by
    filter_upwards [(intrinsicGapDomain_isOpen N).mem_nhds hz] with x hx
    have hy := PhysicalEnergy.simplex_subset_ambient N _
      (PhysicalCollision.intrinsic_chart_mem_simplex N hx)
    exact (hval ⟨_, hy⟩).trans (hv ⟨_, hy⟩).symm
  refine ⟨κ, D/2, hκ, by positivity, ?_, ?_⟩
  · intro z hz u
    rw [(he z hz).fderiv.fderiv_eq]
    exact hcurv z hz u
  · intro z hz
    rw [(he z hz).gradient_eq,
      (InnerProductSpace.laplacian_congr_nhds (he z hz)).eq_of_nhds]
    linarith [hd z hz]

/-- Internal differentiated equation for an arbitrary physical ambient
extension, Theorem 2. The full zero-sum test domain and
the given scalar realization are retained. -/
theorem internal_ambient_gradient (hN : 2 ≤ (N : ℕ))
    {ν : Measure (gapTangentSpace N)}
    {W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ}
    (hW : ContDiffOn ℝ ∞ W (gapAmbientDomain N))
    (hV : IsEuclideanGibbsPotential volume ν (intrinsicGapDomain N)
      (fun z => W (WithLp.toLp 2 (fun i => 1 + z.val i))))
    {κ C : ℝ} (hκ : 0 < κ) (hC : 0 ≤ C)
    (hH : ∀ z ∈ intrinsicGapDomain N, ∀ u : gapTangentSpace N,
      κ * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (fun z : gapTangentSpace N =>
        W (WithLp.toLp 2 (fun i => 1 + z.val i)))) z u u)
    (hbar : ∀ z ∈ intrinsicGapDomain N,
      (Metric.infDist z (frontier (intrinsicGapDomain N)))⁻¹ ^ 2 - C ≤
        ‖gradient (fun z : gapTangentSpace N =>
          W (WithLp.toLp 2 (fun i => 1 + z.val i))) z‖ ^ 2 / 4 -
        Laplacian.laplacian (fun z : gapTangentSpace N =>
          W (WithLp.toLp 2 (fun i => 1 + z.val i))) z / 2)
    (Q : ScalarFormData ν) (hQ : IsNeumannRealization (intrinsicGapDomain N) Q)
    (F ψ : Q.1) (hψ : ScalarPoissonSolution Q F ψ)
    (DF Dψ : Lp (gapTangentSpace N) 2 ν)
    (hDF : (F.val, DF) ∈ neumannSobolevGraph ν (intrinsicGapDomain N))
    (hDψ : (ψ.val, Dψ) ∈ neumannSobolevGraph ν (intrinsicGapDomain N)) :
    ∃ u : Fin (N : ℕ) → Q.1,
      WeightedWeakSolution Q (fun z => hessianMatrix W
        (WithLp.toLp 2 (fun i => 1 + z.val i))) (zeroSumComponents _)
        (fun i => tangentCoordinateLp i DF) u ∧
      ∀ i, (u i).val = tangentCoordinateLp i Dψ := by
  have hQeq := internal_realization_eq hQ
    (realization (intrinsicGapDomain_isOpen N) (domain_bounded N) hV)
  subst Q
  have := probability hV
  have := tangent_nontrivial hN
  let b := stdOrthonormalBasis ℝ (gapTangentSpace N)
  let Q := form (intrinsicGapDomain_isOpen N) (domain_bounded N) hV
  let M := fun z : gapTangentSpace N => hessianMatrix W
    (WithLp.toLp 2 (fun i => 1 + z.val i))
  let V := fun z : gapTangentSpace N => W (WithLp.toLp 2 (fun i => 1 + z.val i))
  obtain ⟨u, hu, hv⟩ := native_gradient_equation b.repr
    (Module.finrank_pos (R := ℝ) (M := gapTangentSpace N))
    (intrinsicGapDomain_isOpen N) (domain_bounded N) hV hκ hH hC hbar F ψ hψ DF Dψ hDF hDψ
  have hcomp : (fun z => (tangentBasisMatrix b).transpose * M z * tangentBasisMatrix b) =ᵐ[ν]
      fun z => hessianMatrix (V ∘ b.repr.symm) (b.repr z) :=
    (supported (intrinsicGapDomain_isOpen N) hV).mono
      (fun z hz => internal_hessian_compression b hW hz)
  have hut : WeightedWeakSolution Q (fun z => (tangentBasisMatrix b).transpose * M z * tangentBasisMatrix b)
      ⊤ (fun i => coordinateValue b.repr i DF) u :=
    (MatrixFieldTransport.weak_congr Q hcomp ⊤ _ u).mpr hu
  have hua := (weightedWeakSolution_tupleMap Q (tangentBasisMatrix b)
    (tangentBasisMatrix_orthonormal b) M (fun i => coordinateValue b.repr i DF) u).mpr hut
  refine ⟨tupleMap (tangentBasisMatrix b) u, ?_, ?_⟩
  · simpa only [tangentBasisMatrix_range, coordinateValue, tangentBasisMatrix_native_components] using hua
  · intro i
    rw [tupleMap_value]
    simp_rw [hv]
    exact congrFun (tangentBasisMatrix_native_components b ν Dψ) i

/-- Individual coordinates of the actual full tilted intrinsic law have
Lebesgue densities, as required for the derivative representatives in
Theorem 2. This includes `N=2`. -/
theorem full_coordinate_absolutelyContinuous (p : Parameters) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) (h : ℝ) (b : Bool) (i : Fin (N : ℕ)) :
    (fullIntrinsicTiltedGapLaw p N θ h b).map
      (fun z => 1 + z.val i) ≪ volume := by
  have hm : Measurable (fun X : Riesz1.Configuration N => gap X i.val) :=
    Riesz1.measurable_gap _
  have hg : (gibbsMeasure p N).map (fun X => gap X i.val) ≪ volume := by
    obtain ⟨f, _, _, _, hf⟩ := GapDensities.gapLaw_marginal_density p N hN i
    have he : (gibbsMeasure p N).map (fun X => gap X i.val) =
        (gapLaw p N).map (fun y => y i) := by
      have hvec : Measurable (gapVector (N := N)) := Riesz1.measurable_gapVector N
      rw [gapLaw, Measure.map_map (measurable_pi_apply i) hvec]
      rfl
    rw [he, hf]
    exact withDensity_absolutelyContinuous _ _
  have ht : tiltedParticleMeasure p N N le_rfl θ h b ≪ gibbsMeasure p N := by
    exact Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
  rw [PhysicalDecay.full_intrinsic_tilted_eq_map,
    Measure.map_map (by fun_prop) (DefinitionSanity.intrinsic_projection_measurable N)]
  have he : (fun X : Riesz1.Configuration N =>
      1 + (centeredGapChart N (WithLp.toLp 2 (gapVector X))).val i) =
      (fun X => gap X i.val) := by
    funext X
    exact congrArg (fun y : EuclideanSpace ℝ (Fin (N : ℕ)) => y i)
      (PhysicalDecay.internal_full_chart_gap N X)
  change (tiltedParticleMeasure p N N le_rfl θ h b).map
    (fun X => 1 + (centeredGapChart N (WithLp.toLp 2 (gapVector X))).val i) ≪ volume
  rw [he]
  exact (ht.map hm).trans hg

/-- Internal derivative L² membership and essential bound after affine
pullback, Theorem 2. -/
theorem internal_derivative_memLp {E : Type*} [MeasurableSpace E]
    {ν : Measure E} [IsFiniteMeasure ν] {a : E → ℝ}
    (ha : Measurable a) (hac : ν.map a ≪ volume) (f : GapObservable) :
    MemLp (fun x => f.val.2 (a x)) 2 ν ∧
      eLpNorm (fun x => f.val.2 (a x)) ∞ ν ≤ ENNReal.ofReal (derivativeSup f) := by
  have hm := (f.property.2.1.mono_ac hac).comp_measurable ha
  have hb : ∀ᵐ x ∂ν, ‖f.val.2 (a x)‖ ≤ derivativeSup f := by
    filter_upwards [ae_of_ae_map ha.aemeasurable
      (hac.ae_le (CenteredObservable.ae_abs_derivative_le f))] with x hx
    simpa only [Real.norm_eq_abs] using hx
  refine ⟨MemLp.of_bound hm _ hb, ?_⟩
  simpa only [ENNReal.toReal_top, inv_zero, ENNReal.rpow_zero, one_mul, Function.comp_def] using
    (eLpNorm_le_of_ae_bound (p := ∞) hm hb)

/-- On every zero-sum L² test, the intrinsic coordinate gradient has the
same pairing as the ambient point source. This proves the normal-component
cancellation in Theorem 2 without changing the Hessian. -/
theorem internal_coordinate_pairing {ν : Measure (gapTangentSpace N)}
    (i : Fin (N : ℕ)) (χ : Lp ℝ 2 ν) (DF : Lp (gapTangentSpace N) 2 ν)
    (hDF : DF =ᵐ[ν] fun z => χ z •
      (InnerProductSpace.toDual ℝ (gapTangentSpace N)).symm
        ((EuclideanSpace.proj i).comp (gapTangentSpace N).subtypeL))
    (w : Fin (N : ℕ) → Lp ℝ 2 ν)
    (hw : ∀ᵐ z ∂ν, (fun k => w k z) ∈ zeroSumComponents (Fin (N : ℕ))) :
    (∑ k, inner ℝ (tangentCoordinateLp k DF) (w k)) = inner ℝ χ (w i) := by
  have hi (k : Fin (N : ℕ)) : Integrable
      (fun z => inner ℝ (tangentCoordinateLp k DF z) (w k z)) ν :=
    L2.integrable_inner _ _
  simp_rw [L2.inner_def]
  rw [← integral_finsetSum Finset.univ (fun k _ => hi k)]
  apply integral_congr_ae
  filter_upwards [hDF, hw, ae_all_iff.mpr (fun k => tangentCoordinateLp_ae k DF)]
    with z hD hwz hc
  let wz : gapTangentSpace N := ⟨WithLp.toLp 2 (fun k => w k z), hwz⟩
  calc
    _ = inner ℝ (DF z) wz := by
      simp only [hc, Submodule.coe_inner, PiLp.inner_apply, Real.inner_apply, wz]
    _ = inner ℝ (χ z) (w i z) := by
      rw [hD]
      have ht := real_inner_smul_left
        ((InnerProductSpace.toDual ℝ (gapTangentSpace N)).symm
          ((EuclideanSpace.proj i).comp (gapTangentSpace N).subtypeL)) wz (χ z)
      simpa only [InnerProductSpace.toDual_symm_apply, ContinuousLinearMap.comp_apply,
        PiLp.proj_apply, Submodule.subtypeL_apply, Real.inner_apply, wz, WithLp.ofLp_toLp,
        mul_comm] using ht

/-- Actual scalar Sobolev graph and derivative class on the full physical
law, supporting Theorem 2. -/
theorem internal_full_observable_sobolev (p : Parameters) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) (h : ℝ) (b : Bool) (i : Fin (N : ℕ)) (f : GapObservable) :
    let ν := fullIntrinsicTiltedGapLaw p N θ h b
    ∃ (hF : MemLp (fun z => f.val.1 (1 + z.val i)) 2 ν)
      (χ : Lp ℝ 2 ν) (DF : Lp (gapTangentSpace N) 2 ν),
      (χ =ᵐ[ν] fun z => f.val.2 (1 + z.val i)) ∧
      eLpNorm χ ∞ ν ≤ ENNReal.ofReal (derivativeSup f) ∧
      (DF =ᵐ[ν] fun z => χ z •
        (InnerProductSpace.toDual ℝ (gapTangentSpace N)).symm
          ((EuclideanSpace.proj i).comp (gapTangentSpace N).subtypeL)) ∧
      (hF.toLp _, DF) ∈ neumannSobolevGraph ν (intrinsicGapDomain N) := by
  intro ν
  have := DefinitionSanity.full_intrinsic_tilted_probability p N θ h b
  obtain ⟨W, _, _, hV, _⟩ := PhysicalDecay.full_physical_matrix_lower p N hN θ h b
  have hac : ν ≪ volume := by
    have ha : ν ≪ volume.restrict (intrinsicGapDomain N) := by
      dsimp only [ν]
      rw [hV.2.2.2]
      exact Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
    exact ha.trans (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  let ℓ := (EuclideanSpace.proj i).comp (gapTangentSpace N).subtypeL
  have hi := full_coordinate_absolutelyContinuous p hN θ h b i
  obtain ⟨Lf, hf⟩ := f.property.1
  have he : (fun z : gapTangentSpace N => ℓ z + 1) = fun z => 1 + z.val i := by
    funext z; dsimp [ℓ]; ring
  obtain ⟨hF, hDF, hgraph⟩ := AffineObservableSobolev.neumannGraph_comp
    (domain_bounded N) (supported (intrinsicGapDomain_isOpen N) hV) hac
    ℓ 1 hf f.property.2.2.1 (by rwa [he])
  simp only [ℓ, ContinuousLinearMap.comp_apply, PiLp.proj_apply,
    Submodule.subtypeL_apply, add_comm] at hF hDF hgraph
  obtain ⟨hf', hfb⟩ := internal_derivative_memLp (ν := ν) (by fun_prop) hi f
  let χ := hf'.toLp (fun z : gapTangentSpace N => f.val.2 (1 + z.val i))
  let DF := hDF.toLp (fun z : gapTangentSpace N => f.val.2 (1 + z.val i) •
    (InnerProductSpace.toDual ℝ (gapTangentSpace N)).symm ℓ)
  have hχ : χ =ᵐ[ν] fun z => f.val.2 (1 + z.val i) := hf'.coeFn_toLp
  refine ⟨hF, χ, DF, hχ, ?_, ?_, hgraph⟩
  · rwa [eLpNorm_congr_ae hχ]
  · filter_upwards [hDF.coeFn_toLp, hχ] with z hx hy
    exact hx.trans (by rw [hy])

/-- Internal full-cycle covariance representation for Theorem 2, on the particular ambient potential and scalar form
supplied by physical decay. The analytic premises follow from the physical estimates. -/
theorem internal_full_coordinate_covariance (p : Parameters) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) (h : ℝ) (b : Bool)
    (W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ)
    (hW : ContDiffOn ℝ ∞ W (gapAmbientDomain N))
    (hval : ∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
      W y.val = fullPhysicalPotentialValue p N hN θ h b y)
    (Q : ScalarFormData (fullIntrinsicTiltedGapLaw p N θ h b))
    (hV : IsEuclideanGibbsPotential volume (fullIntrinsicTiltedGapLaw p N θ h b)
      (intrinsicGapDomain N) (fun z => W (WithLp.toLp 2 (fun i => 1 + z.val i))))
    (hQ : IsNeumannRealization (intrinsicGapDomain N) Q)
    (i j : Fin (N : ℕ)) (f g : GapObservable) :
    let ν := fullIntrinsicTiltedGapLaw p N θ h b
    ∃ χ η : Lp ℝ 2 ν,
      (χ =ᵐ[ν] fun z => f.val.2 (1 + z.val i)) ∧
      (η =ᵐ[ν] fun z => g.val.2 (1 + z.val j)) ∧
      eLpNorm χ ∞ ν ≤ ENNReal.ofReal (derivativeSup f) ∧
      eLpNorm η ∞ ν ≤ ENNReal.ofReal (derivativeSup g) ∧
      MemLp (fun z => f.val.1 (1 + z.val i)) 2 ν ∧
      MemLp (fun z => g.val.1 (1 + z.val j)) 2 ν ∧
      ∃ u : Fin (N : ℕ) → Q.1,
        WeightedWeakSolution Q (fun z => hessianMatrix W
          (WithLp.toLp 2 (fun k => 1 + z.val k))) (zeroSumComponents _)
          (fun k => if k = i then χ else 0) u ∧
        ProbabilityTheory.covariance (fun z => f.val.1 (1 + z.val i))
          (fun z => g.val.1 (1 + z.val j)) ν = inner ℝ η (u j).val := by
  classical
  intro ν
  have := probability hV
  obtain ⟨hF, χ, DF, hχ, hχb, hDFχ, hgraphF⟩ :=
    internal_full_observable_sobolev p hN θ h b i f
  obtain ⟨hG, η, DG, hη, hηb, hDGη, hgraphG⟩ :=
    internal_full_observable_sobolev p hN θ h b j g
  let F : Q.1 := ⟨hF.toLp _, (hQ.1 _).mpr ⟨DF, hgraphF⟩⟩
  let G : Q.1 := ⟨hG.toLp _, (hQ.1 _).mpr ⟨DG, hgraphG⟩⟩
  obtain ⟨κ, C, hκ, hC, hH, hbar⟩ := internal_physical_criteria p hN θ h b W hval
  have hQeq := internal_realization_eq hQ
    (realization (intrinsicGapDomain_isOpen N) (domain_bounded N) hV)
  have hscalar : ∃ ψ : Q.1, ScalarPoissonSolution Q F ψ := by
    subst Q
    have := tangent_nontrivial hN
    exact (IntrinsicScalarPoisson.scalarPoissonSolution_existsUnique
      (intrinsicGapDomain_isOpen N) (domain_bounded N) (domain_convex N) hV hκ hH F).exists
  obtain ⟨ψ, hψ⟩ := hscalar
  obtain ⟨Dψ, hDψ⟩ := (hQ.1 ψ.val).mp ψ.property
  obtain ⟨u, hu, huv⟩ := internal_ambient_gradient hN hW hV hκ hC hH hbar
    Q hQ F ψ hψ DF Dψ hgraphF hDψ
  refine ⟨χ, η, hχ, hη, hχb, hηb, hF, hG, u, ?_, ?_⟩
  · refine ⟨hu.1, fun w hw => ?_⟩
    obtain ⟨hint, heq⟩ := hu.2 w hw
    refine ⟨hint, heq.trans ?_⟩
    rw [internal_coordinate_pairing i χ DF hDFχ (fun k => (w k).val) hw.1]
    have hp (k : Fin (N : ℕ)) : inner ℝ (if k = i then χ else 0) (w k).val =
        if k = i then inner ℝ χ (w k).val else 0 := by split_ifs <;> simp
    simp_rw [hp]
    simp
  · have hcov := (covariance_of_scalar_solution Q hQ F ψ hψ Dψ hDψ G DG hgraphG).2
    have hcov' : ProbabilityTheory.covariance F.val G.val ν =
        ProbabilityTheory.covariance (fun z => f.val.1 (1 + z.val i))
          (fun z => g.val.1 (1 + z.val j)) ν := by
      unfold ProbabilityTheory.covariance
      rw [integral_congr_ae hF.coeFn_toLp, integral_congr_ae hG.coeFn_toLp]
      apply integral_congr_ae
      filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with z hx hy
      rw [hx, hy]
    rw [← hcov', hcov, ← tangentCoordinateLp_inner,
      internal_coordinate_pairing j η DG hDGη _ (tangentCoordinateLp_zeroSum Dψ), huv j]

/-- Exact covariance transport from the intrinsic full law to the particle
tilt, Theorem 2. The chart is the centered gap map. -/
theorem full_covariance_pullback (p : Parameters) (θ : PhysicalCutoff) (h : ℝ)
    (b : Bool) (i j : Fin (N : ℕ)) (f g : GapObservable) :
    ProbabilityTheory.covariance (fun z : gapTangentSpace N => f.val.1 (1 + z.val i))
      (fun z : gapTangentSpace N => g.val.1 (1 + z.val j))
      (fullIntrinsicTiltedGapLaw p N θ h b) =
    ProbabilityTheory.covariance (fun X : Riesz1.Configuration N => f.val.1 (gap X i.val))
      (fun X => g.val.1 (gap X j.val)) (tiltedParticleMeasure p N N le_rfl θ h b) := by
  rw [PhysicalDecay.full_intrinsic_tilted_eq_map]
  have hfc : Continuous f.val.1 := f.property.1.choose_spec.continuous
  have hgc : Continuous g.val.1 := g.property.1.choose_spec.continuous
  have hf : Continuous (fun z : gapTangentSpace N => f.val.1 (1 + z.val i)) := by fun_prop
  have hg : Continuous (fun z : gapTangentSpace N => g.val.1 (1 + z.val j)) := by fun_prop
  have hcov := ProbabilityTheory.covariance_map_fun hf.aestronglyMeasurable
    hg.aestronglyMeasurable (DefinitionSanity.intrinsic_projection_measurable N).aemeasurable
    (μ := tiltedParticleMeasure p N N le_rfl θ h b)
  have he (X : Riesz1.Configuration N) (k : Fin (N : ℕ)) :
      1 + (centeredGapChart N (WithLp.toLp 2 (gapVector X))).val k = gap X k.val :=
    congrArg (fun y : EuclideanSpace ℝ (Fin (N : ℕ)) => y k)
      (PhysicalDecay.internal_full_chart_gap N X)
  simpa only [he] using hcov

/-- Internal L² change of variables for a scalar gap observable, supporting
Theorem 2. This applies to a.e. derivative representatives. -/
theorem internal_coordinate_memLp_pullback (p : Parameters) (θ : PhysicalCutoff)
    (h : ℝ) (b : Bool) (i : Fin (N : ℕ)) (F : ℝ → ℝ)
    (hF : MemLp (fun z : gapTangentSpace N => F (1 + z.val i)) 2
      (fullIntrinsicTiltedGapLaw p N θ h b)) :
    MemLp (fun X : Riesz1.Configuration N => F (gap X i.val)) 2
      (tiltedParticleMeasure p N N le_rfl θ h b) := by
  let T := fun X : Riesz1.Configuration N => centeredGapChart N (WithLp.toLp 2 (gapVector X))
  have hp : MeasurePreserving T (tiltedParticleMeasure p N N le_rfl θ h b)
      (fullIntrinsicTiltedGapLaw p N θ h b) :=
    ⟨DefinitionSanity.intrinsic_projection_measurable N,
      (PhysicalDecay.full_intrinsic_tilted_eq_map p N θ h b).symm⟩
  have he (X : Riesz1.Configuration N) : 1 + (T X).val i = gap X i.val :=
    congrArg (fun y : EuclideanSpace ℝ (Fin (N : ℕ)) => y i)
      (PhysicalDecay.internal_full_chart_gap N X)
  simpa only [Function.comp_def, he] using hF.comp_measurePreserving hp

/-- Full-cycle physical covariance representation in Theorem 2. The potential, scalar form, derivative L² classes and
point-source tangent solution are all conclusions, including for `N=2`.
The derivative representatives may be arbitrary on Lebesgue null sets. -/
theorem full_cycle_covariance (p : Parameters) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) (h : ℝ) (b : Bool) (i j : Fin (N : ℕ)) (f g : GapObservable) :
    let ν := fullIntrinsicTiltedGapLaw p N θ h b
    ∃ (W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ) (Q : ScalarFormData ν),
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = fullPhysicalPotentialValue p N hN θ h b y) ∧
      IsEuclideanGibbsPotential volume ν (intrinsicGapDomain N)
        (fun z => W (WithLp.toLp 2 (fun k => 1 + z.val k))) ∧
      IsNeumannRealization (intrinsicGapDomain N) Q ∧
      IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
      ∃ χ η : Lp ℝ 2 ν,
        (χ =ᵐ[ν] fun z => f.val.2 (1 + z.val i)) ∧
        (η =ᵐ[ν] fun z => g.val.2 (1 + z.val j)) ∧
        eLpNorm χ ∞ ν ≤ ENNReal.ofReal (derivativeSup f) ∧
        eLpNorm η ∞ ν ≤ ENNReal.ofReal (derivativeSup g) ∧
        MemLp (fun z => f.val.1 (1 + z.val i)) 2 ν ∧
        MemLp (fun z => g.val.1 (1 + z.val j)) 2 ν ∧
        MemLp (fun X : Riesz1.Configuration N => f.val.1 (gap X i.val)) 2
          (tiltedParticleMeasure p N N le_rfl θ h b) ∧
        MemLp (fun X : Riesz1.Configuration N => g.val.1 (gap X j.val)) 2
          (tiltedParticleMeasure p N N le_rfl θ h b) ∧
        MemLp (fun X : Riesz1.Configuration N => f.val.2 (gap X i.val)) 2
          (tiltedParticleMeasure p N N le_rfl θ h b) ∧
        MemLp (fun X : Riesz1.Configuration N => g.val.2 (gap X j.val)) 2
          (tiltedParticleMeasure p N N le_rfl θ h b) ∧
        ∃ u : Fin (N : ℕ) → Q.1,
          WeightedWeakSolution Q (fun z => hessianMatrix W
            (WithLp.toLp 2 (fun k => 1 + z.val k))) (zeroSumComponents _)
            (fun k => if k = i then χ else 0) u ∧
          ProbabilityTheory.covariance (fun z => f.val.1 (1 + z.val i))
            (fun z => g.val.1 (1 + z.val j)) ν = inner ℝ η (u j).val ∧
          ProbabilityTheory.covariance (fun X : Riesz1.Configuration N => f.val.1 (gap X i.val))
            (fun X => g.val.1 (gap X j.val)) (tiltedParticleMeasure p N N le_rfl θ h b) =
              inner ℝ η (u j).val := by
  intro ν
  obtain ⟨_, _, _, W, Q, hW, hval, hV, hQ, hclosed, hcons, _⟩ :=
    PhysicalDecay.full_physical_wellposed p N hN θ h b
  obtain ⟨χ, η, hχ, hη, hχb, hηb, hF, hG, u, hu, hcov⟩ :=
    internal_full_coordinate_covariance p hN θ h b W hW hval Q hV hQ i j f g
  exact ⟨W, Q, hW, hval, hV, hQ, hclosed, hcons, χ, η, hχ, hη, hχb, hηb, hF, hG,
    internal_coordinate_memLp_pullback p θ h b i f.val.1 hF,
    internal_coordinate_memLp_pullback p θ h b j g.val.1 hG,
    internal_coordinate_memLp_pullback p θ h b i f.val.2 ((memLp_congr_ae hχ).mp (Lp.memLp χ)),
    internal_coordinate_memLp_pullback p θ h b j g.val.2 ((memLp_congr_ae hη).mp (Lp.memLp η)),
    u, hu, hcov, (full_covariance_pullback p θ h b i j f g).symm.trans hcov⟩

end Riesz2.DecayShort.ShortRangeResultPart3
