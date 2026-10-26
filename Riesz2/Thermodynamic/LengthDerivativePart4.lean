/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.LengthDerivativePart2
public import Riesz2.Thermodynamic.LengthAveragingFibresPart4
public import Riesz2.Thermodynamic.CompatibleComparisonPart3
public import Riesz2.ToMathlib.GradientSquareIntegrability

/-!
# Normal scores on marginal length fibres

Supporting results for the proof of Lemma 6.5. The scalar potential is the actual
penalized marginal potential, and all fibre laws and transported forms are the intrinsic
constructions.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped ENNReal Topology ContDiff

namespace Riesz2.LengthDerivative

open AffineSimplex LengthAveragingFibres

/-- See the proof of Lemma 6.5 in the paper: scaling the normal
direction in `β K` gives the score of `K`. Thus the all-direction form-domain
theorem also applies literally to `D₀ K`, using `β⁻¹ • d₀`. -/
theorem score_rescale_internal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : E → ℝ} {x : E} (hP : DifferentiableAt ℝ P x) (a : ℝ) (d : E) :
    fderiv ℝ (fun y => a*P y) x d = fderiv ℝ P x (a • d) := by
  rw [(hP.hasFDerivAt.const_mul a).fderiv,map_smul]
  rfl

/-- See the proof of Lemma 6.5 in the paper: the actual retained
marginal fibre has its orthonormal Gibbs realization, strict curvature,
collision barrier and full covariance theory at every interior length. -/
theorem retained_fibre_analytic (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (θ : PhysicalCutoff) (ε : ℝ)
    (L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ))
    (frame : Tangent n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    let P := fun x : EuclideanSpace ℝ (Fin (n+1)) =>
      p.val.1 * ∑ i, (θ.val ((n+1 : ℝ)^(-ε)*x i) +
        θ.val ((n+1 : ℝ)^(-ε)*(x i)⁻¹)) -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n+1) m (Equiv.refl _) (x,z)).toReal)
    let U := frame '' (centredChart n L.val ⁻¹' massSimplex n L.val)
    let V := fun z => P (centredChart n L.val (frame.symm z))
    let hU : IsOpen U := frame.toHomeomorph.isOpenMap _ (ConditionalWellPosedness.fibre_isOpen n L.val)
    let hB : Bornology.IsBounded U := frame.isometry.lipschitzWith.isBounded_image
      (ConditionalWellPosedness.fibre_isBounded n L.val)
    ∃ ν : Measure (EuclideanSpace ℝ (Fin n)),
      ∃ hV : IsEuclideanGibbsPotential volume ν U V,
        (ν.comap (Subtype.val : U → _)).map
          (InterpolationTransport.orthonormalInclusion n L.val _ L.property.2 frame) =
            retainedKernel p n m θ ε L ∧
        ConditionalWellPosedness.EuclideanWellPosed (U := U) (V := V) (ρ := ν) hU hB hV ∧
        ∃ κ C : ℝ, 0 < κ ∧ 0 ≤ C ∧
          (∀ z ∈ U, ∀ u, κ*‖u‖^2 ≤ fderiv ℝ (fderiv ℝ V) z u u) ∧
          ∀ z ∈ U, (Metric.infDist z (frontier U))⁻¹^2-C ≤
            ‖gradient V z‖^2/4-Laplacian.laplacian V z/2 := by
  intro P U V hU hB
  obtain ⟨ν,hV,hlaw,_⟩ := retained_intrinsic_scalar_internal p n m θ ε L frame
  have ha : 0 < (n+1 : ℝ)^(-ε) := Real.rpow_pos_of_pos (by positivity) _
  obtain ⟨ρ,hρ,_hmap,κ,C,hκ,hC,hH,hbar⟩ :=
    ConditionalWellPosedness.fixed_length_marginal_fibres p n m hn (Equiv.refl _)
      L.property.1 L.property.2 θ ha Finset.univ true
  let W := fun w : Tangent n => P (centredChart n L.val w)
  have hρ' : IsEuclideanGibbsPotential volume ρ
      (centredChart n L.val ⁻¹' massSimplex n L.val) W := by
    simpa only [W, P, ite_true] using hρ
  have hH' : ∀ w ∈ centredChart n L.val ⁻¹' massSimplex n L.val,
      ∀ u : Tangent n, κ*‖u‖^2 ≤ fderiv ℝ (fderiv ℝ W) w u u := by
    simpa only [W, P, ite_true] using hH
  have hbar' : ∀ w ∈ centredChart n L.val ⁻¹' massSimplex n L.val,
      (Metric.infDist w (frontier (centredChart n L.val ⁻¹' massSimplex n L.val)))⁻¹^2-C ≤
        ‖gradient W w‖^2/4-Laplacian.laplacian W w/2 := by
    simpa only [W, P, ite_true] using hbar
  have hHV : ∀ z ∈ U, ∀ u, κ*‖u‖^2 ≤ fderiv ℝ (fderiv ℝ V) z u u := by
    rintro z ⟨w,hw,rfl⟩ u
    change _ ≤ fderiv ℝ (fderiv ℝ (W ∘ frame.symm)) (frame w) u u
    rw [SobolevIsometry.hessian_comp_symm frame
      (ConditionalWellPosedness.fibre_isOpen n L.val) (hρ'.1.of_le (by norm_num))
      (by simpa only [frame.symm_apply_apply] using hw), frame.symm_apply_apply]
    simpa only [frame.symm.norm_map] using hH' w hw (frame.symm u)
  have hbV : ∀ z ∈ U, (Metric.infDist z (frontier U))⁻¹^2-C ≤
      ‖gradient V z‖^2/4-Laplacian.laplacian V z/2 :=
    NeumannIsometryTransport.barrier_map frame
      (ConditionalWellPosedness.fibre_isOpen n L.val) (hρ'.1.of_le (by norm_num)) hbar'
  refine ⟨ν,hV,hlaw,?_,κ,C,hκ,hC,hHV,hbV⟩
  exact ConditionalWellPosedness.internal_euclidean_wellposed hn hU hB
    ((ConditionalWellPosedness.fibre_convex n L.val).linear_image frame.toLinearEquiv.toLinearMap)
    hV hκ hC hHV hbV

/-- See the proof of Lemma 6.5 in the paper: the derivative of the
normal score is the actual mixed Hessian, in the order tangent then normal.
This identity includes the physical penalty and compensated marginal terms. -/
theorem normal_score_hasFDerivAt_internal (n : ℕ) (L : ℝ)
    (frame : Tangent n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (P : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (d : EuclideanSpace ℝ (Fin (n+1))) (x : EuclideanSpace ℝ (Fin n))
    (hP : ContDiffAt ℝ 2 P (centredChart n L (frame.symm x))) :
    let B := (Tangent n).subtypeL.comp frame.symm.toContinuousLinearEquiv.toContinuousLinearMap
    HasFDerivAt (fun z => fderiv ℝ P (centredChart n L (frame.symm z)) d)
      (((ContinuousLinearMap.apply ℝ ℝ d).comp
        (fderiv ℝ (fderiv ℝ P) (centredChart n L (frame.symm x)))).comp B) x := by
  intro B
  have hd := ((hP.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt
  have hg := B.hasFDerivAt.add_const (centre n L) (x := x)
  convert (hd.comp x hg).clm_apply (hasFDerivAt_const d x) using 1
  · rfl
  · ext v
    simp only [ContinuousLinearMap.comp_apply, _root_.add_apply, _root_.zero_apply, map_zero,
      zero_add, ContinuousLinearMap.flip_apply, ContinuousLinearMap.apply_apply]

/-- See the proof of Lemma 6.5 in the paper: finite Hessian norm on a
physical fibre puts every constant-direction score in its full intrinsic
scalar domain. Poincaré supplies the score value norm. -/
theorem score_jet_of_hessian_internal (n : ℕ) (hn : 1 ≤ n) (m : ℕ)
    (L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ))
    (frame : Tangent n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (P : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (hP : ContDiffOn ℝ ∞ P (chartDomain (n+1) ((n+1+m : ℕ)+1)))
    (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hV : IsEuclideanGibbsPotential volume ν
      (frame '' (centredChart n L.val ⁻¹' massSimplex n L.val))
      (fun z => P (centredChart n L.val (frame.symm z))))
    (κ C : ℝ) (hκ : 0 < κ) (hC : 0 ≤ C)
    (hcurv : ∀ z ∈ frame '' (centredChart n L.val ⁻¹' massSimplex n L.val),
      ∀ u, κ*‖u‖^2 ≤ fderiv ℝ (fderiv ℝ
        (fun z => P (centredChart n L.val (frame.symm z)))) z u u)
    (hbar : ∀ z ∈ frame '' (centredChart n L.val ⁻¹' massSimplex n L.val),
      (Metric.infDist z (frontier (frame '' (centredChart n L.val ⁻¹' massSimplex n L.val))))⁻¹^2-C ≤
        ‖gradient (fun z => P (centredChart n L.val (frame.symm z))) z‖^2/4-
          Laplacian.laplacian (fun z => P (centredChart n L.val (frame.symm z))) z/2)
    (hH : MemLp (fun z => ‖fderiv ℝ (fderiv ℝ P)
      (centredChart n L.val (frame.symm z))‖) 2 ν)
    (d : EuclideanSpace ℝ (Fin (n+1))) :
    let U := frame '' (centredChart n L.val ⁻¹' massSimplex n L.val)
    let hU : IsOpen U := frame.toHomeomorph.isOpenMap _ (ConditionalWellPosedness.fibre_isOpen n L.val)
    let hB : Bornology.IsBounded U := frame.isometry.lipschitzWith.isBounded_image
      (ConditionalWellPosedness.fibre_isBounded n L.val)
    ∃ F : ScalarForm.Domain (IntrinsicScalarCore.jet hU hB hV),
      ScalarForm.value _ F =ᵐ[ν] (fun z => fderiv ℝ P (centredChart n L.val (frame.symm z)) d) ∧
      ScalarForm.deriv _ F =ᵐ[ν]
        gradient (fun z => fderiv ℝ P (centredChart n L.val (frame.symm z)) d) := by
  intro U hU hB
  let g := fun z => centredChart n L.val (frame.symm z)
  let f := fun z => fderiv ℝ P (g z) d
  let B := (Tangent n).subtypeL.comp frame.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hg : ContDiff ℝ ∞ g :=
    (B.contDiff.add contDiff_const)
  have hgU : ∀ z ∈ U, g z ∈ chartDomain (n+1) ((n+1+m : ℕ)+1) := by
    rintro z ⟨w,hw,rfl⟩
    refine ⟨?_, ?_⟩
    · simpa only [g, frame.symm_apply_apply] using hw.1
    · rw [show g (frame w) = centredChart n L.val w by simp only [g,frame.symm_apply_apply],
        sum_centredChart]
      exact L.property.2
  have hs : ContDiffOn ℝ ∞ f U :=
    (((hP.fderiv_of_isOpen (isOpen_chartDomain _ _) (by simp)).clm_apply
      contDiffOn_const).comp hg.contDiffOn hgU)
  have hm : Measurable f := (measurable_fderiv_apply_const ℝ P d).comp hg.continuous.measurable
  have hnorm : ∀ᵐ z ∂ν, ‖gradient f z‖ ≤
      ‖fderiv ℝ (fderiv ℝ P) (g z)‖*(‖B‖*‖d‖) := by
    filter_upwards [IntrinsicScalarCore.supported hU hV] with z hz
    have hsz : ContDiffAt ℝ 2 P (g z) :=
      (hP.contDiffAt ((isOpen_chartDomain _ _).mem_nhds (hgU z hz))).of_le (by norm_num)
    have hd := normal_score_hasFDerivAt_internal n L.val frame P d z hsz
    rw [gradient, LinearIsometryEquiv.norm_map, hd.fderiv]
    exact GradientSquareIntegrability.mixed_derivative_norm _ B d
  have hdf : MemLp (gradient f) 2 ν :=
    (hH.mul_const (‖B‖*‖d‖)).mono'
      (((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.measurable.comp
        (measurable_fderiv ℝ f)).aestronglyMeasurable) hnorm
  have hne : U.Nonempty := by
    refine ⟨frame 0, ⟨0, ?_, rfl⟩⟩
    simpa only [mem_preimage, centredChart, Submodule.coe_zero, zero_add]
      using centre_mem_simplex n L.property.1
  have hf := GradientSquareIntegrability.memLp_of_gradient hn hU hB hne
    ((ConditionalWellPosedness.fibre_convex n L.val).linear_image frame.toLinearEquiv.toLinearMap)
    hV hC hκ hcurv hbar f hm hs hdf
  exact CompatibleComparison.interior_jet_internal hn hU hB hV hC hbar f hs hf hdf

/-- See the proof of Lemma 6.5 in the paper: the existing common
envelope has finite second moment on almost every retained fibre in either
exponent regime. The null set is independent of the normal direction. -/
theorem marginal_envelope_memLp_two_ae (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε C₀ : ℝ) (hε : 0 < ε)
    (hhalf : 2*(n+1) ≤ n+1+m+1) :
    ∀ᵐ (L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ)) ∂lengthMeasure p n m θ ε,
      MemLp (shortEnvelope p n.succPNat m θ ε C₀) 2 (retainedKernel p n m θ ε L) := by
  by_cases hs : p.val.2 < 1
  · let β : InverseTemperature := ⟨p.val.1,p.property.1⟩
    let s : Riesz1.RieszExponent := ⟨p.val.2,p.property.2.1,hs⟩
    have hp : ofLong β s = p := Subtype.ext (Prod.ext rfl rfl)
    have hh := longEnvelope_memLp_two_ae β s n m θ ε C₀ hε hhalf
    have he := longEnvelope_eq_shortEnvelope β s n.succPNat m θ ε C₀
    rw [funext he] at hh
    exact hp ▸ hh
  · exact shortEnvelope_memLp_two_ae p (lt_of_le_of_ne (le_of_not_gt hs)
      (Ne.symm p.property.2.2)) n m θ ε C₀ hε hhalf

/-- See the proof of Lemma 6.5 in the paper: the actual dimensionless
marginal Hessian has a finite L² operator norm on almost every fibre, with
the same physical two-sided penalty. -/
theorem marginal_hessian_memLp_two_ae (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) (hε : 0 < ε)
    (hhalf : 2*(n+1) ≤ n+1+m+1) :
    let P := fun x : EuclideanSpace ℝ (Fin (n+1)) =>
      p.val.1 * ∑ i, (θ.val ((n+1 : ℝ)^(-ε)*x i) +
        θ.val ((n+1 : ℝ)^(-ε)*(x i)⁻¹)) -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n+1) m (Equiv.refl _) (x,z)).toReal)
    ∀ᵐ (L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ)) ∂lengthMeasure p n m θ ε,
      MemLp (fun x => ‖fderiv ℝ (fderiv ℝ P) x.val‖) 2 (retainedKernel p n m θ ε L) := by
  intro P
  let K := fun x => p.val.1⁻¹*P x
  have hP : ContDiffOn ℝ ∞ P (chartDomain (n+1) ((n+1+m : ℕ)+1)) := by
    simpa only [P,ite_true] using MarginalHessian.physical_penalized_marginal_potential_smooth
      p (n+1) m (by omega) (Equiv.refl _) θ
      (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < n+1) (-ε)) Finset.univ true
  have hK : ContDiffOn ℝ ∞ K (chartDomain (n+1) ((n+1+m : ℕ)+1)) := contDiffOn_const.mul hP
  have he : (fun x => p.val.1*K x) = P := by
    funext x
    dsimp only [K]
    rw [← mul_assoc, mul_inv_cancel₀ p.property.1.ne', one_mul]
  have hbound (x : chartDomain (n+1) ((n+1+m : ℕ)+1)) :
      ‖fderiv ℝ (fderiv ℝ P) x.val‖ ≤
        (p.val.1*(n+1 : ℝ)^(2 : ℝ))*shortEnvelope p n.succPNat m θ ε 0 x := by
    have hs : ContDiffAt ℝ 2 K x.val :=
      (hK.contDiffAt ((isOpen_chartDomain _ _).mem_nhds x.property)).of_le (by norm_num)
    have hrel : fderiv ℝ (fderiv ℝ P) x.val = p.val.1 • fderiv ℝ (fderiv ℝ K) x.val := by
      conv_lhs => rw [← he]
      ext u v
      exact PhysicalCollision.internal_hessian_const_mul hs p.val.1 u v
    have hb := marginal_hessian_envelope p n.succPNat m θ ε 0 hε x
    have hb' : ‖fderiv ℝ (fderiv ℝ K) x.val‖ ≤
        (n+1 : ℝ)^(2 : ℝ)*shortEnvelope p n.succPNat m θ ε 0 x := by
      simpa only [Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one,
        Real.rpow_neg (by positivity : (0 : ℝ) ≤ n+1), sub_zero, K, P] using hb
    rw [hrel]
    apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
    rw [Real.norm_of_nonneg p.property.1.le]
    exact (mul_le_mul_of_nonneg_left hb' p.property.1.le).trans_eq (by ring)
  filter_upwards [marginal_envelope_memLp_two_ae p n m θ ε 0 hε hhalf] with L hL
  apply (hL.const_mul (p.val.1*(n+1 : ℝ)^(2 : ℝ))).mono'
    (((measurable_fderiv ℝ (fderiv ℝ P)).norm.comp measurable_subtype_coe).aestronglyMeasurable)
  exact ae_of_all _ fun x => by simpa only [Function.comp_def, norm_norm] using hbound x

/-- See the proof of Lemma 6.5 in the paper: on almost every literal
marginal fibre, every constant-direction marginal score belongs to the full
intrinsic scalar form domain with its gradient. In particular choose
`d = (n+1)⁻¹ • 1` for the normal score `β D₀ K`. -/
theorem normal_score_form_domain (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (θ : PhysicalCutoff) (ε : ℝ) (hε : 0 < ε)
    (hhalf : 2*(n+1) ≤ n+1+m+1)
    (frame : Tangent n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    let P := fun x : EuclideanSpace ℝ (Fin (n+1)) =>
      p.val.1 * ∑ i, (θ.val ((n+1 : ℝ)^(-ε)*x i) +
        θ.val ((n+1 : ℝ)^(-ε)*(x i)⁻¹)) -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n+1) m (Equiv.refl _) (x,z)).toReal)
    ∀ᵐ (L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ)) ∂lengthMeasure p n m θ ε,
      let U := frame '' (centredChart n L.val ⁻¹' massSimplex n L.val)
      let V := fun z => P (centredChart n L.val (frame.symm z))
      let hU : IsOpen U := frame.toHomeomorph.isOpenMap _ (ConditionalWellPosedness.fibre_isOpen n L.val)
      let hB : Bornology.IsBounded U := frame.isometry.lipschitzWith.isBounded_image
        (ConditionalWellPosedness.fibre_isBounded n L.val)
      ∃ ν : Measure (EuclideanSpace ℝ (Fin n)),
        ∃ hV : IsEuclideanGibbsPotential volume ν U V,
          (ν.comap (Subtype.val : U → _)).map
            (InterpolationTransport.orthonormalInclusion n L.val _ L.property.2 frame) =
              retainedKernel p n m θ ε L ∧
          ConditionalWellPosedness.EuclideanWellPosed (U := U) (V := V) (ρ := ν) hU hB hV ∧
          MemLp (fun z => ‖fderiv ℝ (fderiv ℝ P) (centredChart n L.val (frame.symm z))‖) 2 ν ∧
          ∀ d : EuclideanSpace ℝ (Fin (n+1)),
            ∃ F : ScalarForm.Domain (IntrinsicScalarCore.jet hU hB hV),
              ScalarForm.value _ F =ᵐ[ν]
                (fun z => fderiv ℝ P (centredChart n L.val (frame.symm z)) d) ∧
              ScalarForm.deriv _ F =ᵐ[ν]
                gradient (fun z => fderiv ℝ P (centredChart n L.val (frame.symm z)) d) := by
  intro P
  have hP : ContDiffOn ℝ ∞ P (chartDomain (n+1) ((n+1+m : ℕ)+1)) := by
    simpa only [P,ite_true] using MarginalHessian.physical_penalized_marginal_potential_smooth
      p (n+1) m (by omega) (Equiv.refl _) θ
      (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < n+1) (-ε)) Finset.univ true
  filter_upwards [marginal_hessian_memLp_two_ae p n m θ ε hε hhalf] with L hL
  intro U V hU hB
  obtain ⟨ν,hV,hlaw,hwell,κ,C,hκ,hC,hcurv,hbar⟩ :=
    retained_fibre_analytic p n m hn θ ε L frame
  have hH : MemLp (fun z => ‖fderiv ℝ (fderiv ℝ P) (centredChart n L.val (frame.symm z))‖) 2 ν := by
    let ξ : Measure U := ν.comap Subtype.val
    let j := InterpolationTransport.orthonormalInclusion n L.val _ L.property.2 frame
    have hj := InterpolationTransport.measurableEmbedding_orthonormalInclusion n L.val _ L.property.2 frame
    have hv := MeasurableEmbedding.subtype_coe hU.measurableSet
    have heν : ξ.map Subtype.val = ν :=
      (InterpolationTransport.orthonormal_law n L.val _ L.property.2 frame ν V hV).1
    have ht : MemLp (fun x : U => ‖fderiv ℝ (fderiv ℝ P) (j x).val‖) 2 ξ := by
      have hh : MemLp (fun x : chartDomain (n+1) ((n+1+m : ℕ)+1) =>
          ‖fderiv ℝ (fderiv ℝ P) x.val‖) 2 (ξ.map j) := by rwa [hlaw]
      exact hj.memLp_map_measure_iff.mp hh
    rw [← heν]
    exact hv.memLp_map_measure_iff.mpr ht
  refine ⟨ν,hV,hlaw,hwell,hH,fun d => ?_⟩
  exact score_jet_of_hessian_internal n hn m L frame P hP ν hV κ C hκ hC hcurv hbar hH d

/-- See the proof of Lemma 6.5 in the paper: the ambient gradient
of a constant-direction score is the corresponding Hessian contraction. -/
theorem score_gradient_internal (a : ℕ) (P : EuclideanSpace ℝ (Fin (a+1)) → ℝ)
    (d x : EuclideanSpace ℝ (Fin (a+1))) (hs : ContDiffAt ℝ ∞ P x)
    (j : Fin (a+1)) :
    gradient (fun y => fderiv ℝ P y d) x j = ∑ i, d i*hessianMatrix P x i j := by
  have hd := ((hs.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have he := (hd.clm_apply (hasFDerivAt_const d x)).fderiv
  have hh : gradient (fun y => fderiv ℝ P y d) x j =
      fderiv ℝ (fderiv ℝ P) x (EuclideanSpace.single j 1) d := by
    have hn : inner ℝ (gradient (fun y => fderiv ℝ P y d) x) (EuclideanSpace.single j 1) =
        fderiv ℝ (fun y => fderiv ℝ P y d) x (EuclideanSpace.single j 1) := inner_gradient_left
    rw [he] at hn
    simpa only [EuclideanSpace.inner_single_right, conj_trivial, one_mul, _root_.add_apply,
      ContinuousLinearMap.comp_apply, _root_.zero_apply, map_zero, zero_add,
      ContinuousLinearMap.flip_apply] using hn
  rw [hh, hs.isSymmSndFDerivAt (by simp) _ _, Intrinsic.hessianMatrix_bilinear hs]
  simp only [PiLp.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- See the proof of Lemma 6.5 in the paper: the score's derivative
classes in an orthonormal chart are the transpose compression of the actual
ambient Hessian contraction. No bounded-score premise is used. -/
theorem score_derivative_classes_internal (n m : ℕ)
    (L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ))
    (frame : Tangent n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (A : Matrix (Fin (n+1)) (Fin n) ℝ)
    (hA : ∀ t : Fin n → ℝ, A *ᵥ t = (frame.symm (WithLp.toLp 2 t)).val)
    (P : EuclideanSpace ℝ (Fin (n+1)) → ℝ)
    (hP : ContDiffOn ℝ ∞ P (chartDomain (n+1) ((n+1+m : ℕ)+1)))
    (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hV : IsEuclideanGibbsPotential volume ν
      (frame '' (centredChart n L.val ⁻¹' massSimplex n L.val))
      (fun z => P (centredChart n L.val (frame.symm z))))
    (d : EuclideanSpace ℝ (Fin (n+1)))
    (hH : MemLp (fun z => ‖fderiv ℝ (fderiv ℝ P)
      (centredChart n L.val (frame.symm z))‖) 2 ν) :
    let U := frame '' (centredChart n L.val ⁻¹' massSimplex n L.val)
    let hU : IsOpen U := frame.toHomeomorph.isOpenMap _ (ConditionalWellPosedness.fibre_isOpen n L.val)
    let hB : Bornology.IsBounded U := frame.isometry.lipschitzWith.isBounded_image
      (ConditionalWellPosedness.fibre_isBounded n L.val)
    ∀ F : ScalarForm.Domain (IntrinsicScalarCore.jet hU hB hV),
      ScalarForm.deriv _ F =ᵐ[ν]
        gradient (fun z => fderiv ℝ P (centredChart n L.val (frame.symm z)) d) →
      ∃ b : Fin (n+1) → Lp ℝ 2 ν,
        (∀ j, b j =ᵐ[ν] fun z => ∑ i, d i*hessianMatrix P (centredChart n L.val (frame.symm z)) i j) ∧
        RectangularFormTransport.tupleMap A.transpose b = fun k =>
          DifferentiatedPoisson.coordinateLp k (ScalarForm.deriv _ F) := by
  intro U hU hB F hDF
  let g := fun z => centredChart n L.val (frame.symm z)
  let D := fun x => fderiv ℝ P x d
  have hg : Continuous g := (isometry_centredChart n L.val).continuous.comp frame.symm.continuous
  have hgU : ∀ z ∈ U, g z ∈ chartDomain (n+1) ((n+1+m : ℕ)+1) := by
    rintro z ⟨w,hw,rfl⟩
    refine ⟨by simpa only [g,frame.symm_apply_apply] using hw.1, ?_⟩
    simpa only [g,frame.symm_apply_apply,sum_centredChart] using L.property.2
  have hsm : ∀ᵐ z ∂ν, ContDiffAt ℝ ∞ P (g z) :=
    (IntrinsicScalarCore.supported hU hV).mono fun z hz =>
      hP.contDiffAt ((isOpen_chartDomain _ _).mem_nhds (hgU z hz))
  have hm (j : Fin (n+1)) : MemLp (fun z => gradient D (g z) j) 2 ν := by
    apply (hH.mul_const (‖d‖)).mono'
      ((((PiLp.continuous_apply 2 (fun _ : Fin (n+1) => ℝ) j).measurable.comp
        ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin (n+1)))).symm.continuous.measurable.comp
          (measurable_fderiv ℝ D))).comp hg.measurable).aestronglyMeasurable)
    filter_upwards [hsm] with z hz
    have he : gradient D (g z) j = fderiv ℝ (fderiv ℝ P) (g z)
        (EuclideanSpace.single j 1) d := by
      rw [score_gradient_internal n P d (g z) hz]
      rw [hz.isSymmSndFDerivAt (by simp) _ _, Intrinsic.hessianMatrix_bilinear hz]
      simp only [PiLp.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    change ‖gradient D (g z) j‖ ≤ ‖fderiv ℝ (fderiv ℝ P) (g z)‖*‖d‖
    rw [he]
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ P) (g z) (EuclideanSpace.single j 1)‖*‖d‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ _ := by
        gcongr
        simpa only [PiLp.norm_single, norm_one, mul_one] using
          (fderiv ℝ (fderiv ℝ P) (g z)).le_opNorm (EuclideanSpace.single j 1)
  let b : Fin (n+1) → Lp ℝ 2 ν := fun j => (hm j).toLp _
  have hb (j : Fin (n+1)) : b j =ᵐ[ν] fun z => gradient D (g z) j := (hm j).coeFn_toLp
  refine ⟨b,fun j => ?_,?_⟩
  · filter_upwards [hb j,hsm] with z hz hs
    exact hz.trans (score_gradient_internal n P d (g z) hs j)
  · funext k
    apply Lp.ext
    filter_upwards [RectangularFormTransport.tupleMap_lp_ae A.transpose b,
      ae_all_iff.mpr hb,hDF,hsm,DifferentiatedPoisson.coordinateLp_ae k (ScalarForm.deriv _ F)]
      with z hz hbz hdz hsz hkz
    rw [hz,hkz,hdz]
    simp only [Matrix.transpose_apply,hbz]
    exact (CompatibleComparison.frame_gradient_internal n L.val frame A hA D z
      (((hsz.fderiv_right (m := 1) (by simp)).clm_apply contDiffAt_const).differentiableAt
        (by simp)) k).symm

/-- See the proof of Lemma 6.5 in the paper: the dimensionless
physical marginal Hessian is positive and strictly coercive on the retained
carrier in both exponent regimes. This is used only for uniqueness and
superposition. No uniform-in-size lower constant is asserted here. -/
theorem marginal_matrix_coercivity (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) :
    let P := fun x : EuclideanSpace ℝ (Fin (n+1)) =>
      p.val.1 * ∑ i, (θ.val ((n+1 : ℝ)^(-ε)*x i) +
        θ.val ((n+1 : ℝ)^(-ε)*(x i)⁻¹)) -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n+1) m (Equiv.refl _) (x,z)).toReal)
    ∃ c : ℝ, 0 < c ∧ ∀ x : chartDomain (n+1) ((n+1+m : ℕ)+1),
      (hessianMatrix P x.val).PosSemidef ∧ ∀ t : Fin (n+1) → ℝ,
        c*(∑ i, t i^2) ≤ ∑ i, ∑ j, t i*hessianMatrix P x.val i j*t j := by
  intro P
  have ha := Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < n+1) (-ε)
  have hP : ContDiffOn ℝ ∞ P (chartDomain (n+1) ((n+1+m : ℕ)+1)) := by
    simpa only [P,ite_true] using MarginalHessian.physical_penalized_marginal_potential_smooth
      p (n+1) m (by omega) (Equiv.refl _) θ ha Finset.univ true
  obtain ⟨c,hc,hlower⟩ := MarginalCollision.penalized_marginal_strict_curvature
    p (n+1) m (by omega) (Equiv.refl _) θ ha Finset.univ true
  have hl : ∀ x ∈ chartDomain (n+1) ((n+1+m : ℕ)+1), ∀ u,
      c*‖u‖^2 ≤ fderiv ℝ (fderiv ℝ P) x u u := by
    simpa only [P,ite_true] using hlower
  refine ⟨c,hc,fun x => ?_⟩
  have hx : ContDiffAt ℝ 2 P x.val :=
    (hP.contDiffAt ((isOpen_chartDomain _ _).mem_nhds x.property)).of_le (by norm_num)
  have ht (t : Fin (n+1) → ℝ) :
      c*(∑ i, t i^2) ≤ ∑ i, ∑ j, t i*hessianMatrix P x.val i j*t j := by
    have hh := hl x.val x.property (WithLp.toLp 2 t)
    rw [← PhysicalEnergy.hessianMatrix_quadratic hx] at hh
    simpa only [EuclideanSpace.real_norm_sq_eq] using hh
  refine ⟨Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_,?_⟩,ht⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply,star_trivial]
    exact DecayShort.PhysicalComparison.hessianMatrix_symm hx j i
  · intro t
    have hh := (show 0 ≤ c*(∑ i, t i^2) by positivity).trans (ht t)
    simpa only [dotProduct,Matrix.mulVec,star_trivial,Finset.mul_sum,mul_assoc] using hh

/-- See the proof of Lemma 6.5 in the paper: covariance against the
normal marginal score is represented by the sum of the tangent
point-source solutions on the orthonormal realization of the physical fibre.
All score, source and pairing integrabilities are conclusions. -/
theorem marginal_score_chart_covariance (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (θ : PhysicalCutoff) (ε : ℝ) (hε : 0 < ε)
    (hhalf : 2*(n+1) ≤ n+1+m+1)
    (frame : Tangent n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    let P := fun x : EuclideanSpace ℝ (Fin (n+1)) =>
      p.val.1 * ∑ i, (θ.val ((n+1 : ℝ)^(-ε)*x i) +
        θ.val ((n+1 : ℝ)^(-ε)*(x i)⁻¹)) -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n+1) m (Equiv.refl _) (x,z)).toReal)
    ∀ᵐ (L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ)) ∂lengthMeasure p n m θ ε,
      let U := frame '' (centredChart n L.val ⁻¹' massSimplex n L.val)
      let g := fun z => centredChart n L.val (frame.symm z)
      let V := P ∘ g
      let hU : IsOpen U := frame.toHomeomorph.isOpenMap _ (ConditionalWellPosedness.fibre_isOpen n L.val)
      let hB : Bornology.IsBounded U := frame.isometry.lipschitzWith.isBounded_image
        (ConditionalWellPosedness.fibre_isBounded n L.val)
      ∃ ν : Measure (EuclideanSpace ℝ (Fin n)),
        ∃ hV : IsEuclideanGibbsPotential volume ν U V,
          (ν.comap (Subtype.val : U → _)).map
            (InterpolationTransport.orthonormalInclusion n L.val _ L.property.2 frame) =
              retainedKernel p n m θ ε L ∧
          ∀ (G : BlockObservable n.succPNat)
            (_hs : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin (n+1)) => G.val (WithLp.ofLp y)))
            (J : Finset (Fin (n+1))) (_hJ : DependsOnBlockCoordinates G J)
            (d : EuclideanSpace ℝ (Fin (n+1))),
            let Q := IntrinsicScalarCore.form hU hB hV
            let M := fun z => hessianMatrix P (g z)
            ∃ χ b : Fin (n+1) → Lp ℝ 2 ν,
              (∀ i, χ i =ᵐ[ν] fun z => gradient (fun y => G.val (WithLp.ofLp y)) (g z) i) ∧
              (∀ j, b j =ᵐ[ν] fun z => ∑ i, d i*M z i j) ∧
              ∃ ψ : Fin (n+1) → Fin (n+1) → Q.1,
                (∀ i, WeightedWeakSolution Q M (zeroSumComponents (Fin (n+1)))
                  (fun j => if j = i then χ i else 0) (ψ i)) ∧
                WeightedWeakSolution Q M (zeroSumComponents (Fin (n+1)))
                  (fun j => if j ∈ J then χ j else 0) (∑ i ∈ J, ψ i) ∧
                Integrable (fun z => ∑ j, b j z*(∑ i ∈ J, ψ i j).val z) ν ∧
                covariance (fun z => G.val (WithLp.ofLp (g z)))
                  (fun z => fderiv ℝ P (g z) d) ν =
                    ∑ i ∈ J, ∫ z, ∑ j, b j z*(ψ i j).val z ∂ν := by
  intro P
  have hP : ContDiffOn ℝ ∞ P (chartDomain (n+1) ((n+1+m : ℕ)+1)) := by
    simpa only [P,ite_true] using MarginalHessian.physical_penalized_marginal_potential_smooth
      p (n+1) m (by omega) (Equiv.refl _) θ
      (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < n+1) (-ε)) Finset.univ true
  obtain ⟨c,hc,hcoerc⟩ := marginal_matrix_coercivity p n m θ ε
  obtain ⟨A,hA,hrange,hact⟩ := CompatibleComparison.frame_matrix_internal n frame
  filter_upwards [normal_score_form_domain p n m hn θ ε hε hhalf frame] with L hL
  intro U g V hU hB
  obtain ⟨ν,hV,hlaw,hwell,hH,hscore⟩ := hL
  refine ⟨ν,hV,hlaw,fun G hs J hJ d => ?_⟩
  intro Q M
  obtain ⟨FG,hFG,χ,hχ,hsource⟩ :=
    CompatibleComparison.smooth_block_source_internal n L.val frame A hact ν V hV G hs J hJ
  obtain ⟨FK,hFK,hDFK⟩ := hscore d
  obtain ⟨b,hb,hscorederiv⟩ := score_derivative_classes_internal n m L frame A hact P hP ν hV d hH FK hDFK
  have hgU : ∀ z ∈ U, g z ∈ chartDomain (n+1) ((n+1+m : ℕ)+1) := by
    rintro z ⟨w,hw,rfl⟩
    refine ⟨by simpa only [g,frame.symm_apply_apply] using hw.1, ?_⟩
    simpa only [g,frame.symm_apply_apply,sum_centredChart] using L.property.2
  have hg : Measurable g := (isometry_centredChart n L.val).continuous.measurable.comp frame.symm.continuous.measurable
  have hM : (fun z => A.transpose*M z*A) =ᵐ[ν] hessianMatrix V :=
    (IntrinsicScalarCore.supported hU hV).mono fun z hz =>
      CompatibleComparison.frame_hessian_internal n L.val frame A hact P z
        (hP.contDiffAt ((isOpen_chartDomain _ _).mem_nhds (hgU z hz)))
  have hpos : ∀ᵐ z ∂ν, (M z).PosSemidef :=
    (IntrinsicScalarCore.supported hU hV).mono fun z hz => (hcoerc ⟨g z,hgU z hz⟩).1
  have hlower : ∀ᵐ z ∂ν, ∀ t ∈ zeroSumComponents (Fin (n+1)),
      c*(∑ i, t i^2) ≤ ∑ i, ∑ j, t i*M z i j*t j :=
    (IntrinsicScalarCore.supported hU hV).mono fun z hz t _ => (hcoerc ⟨g z,hgU z hz⟩).2 t
  have hm (i j : Fin (n+1)) : Measurable (fun z => M z i j) :=
    (DifferentiatedPoisson.measurable_hessian_entries (V := P) i j).comp hg
  have hclosed := IntrinsicScalarCore.closed_dirichlet hU hB hV
  have hex (i : Fin (n+1)) : ∃ ψ : Fin (n+1) → Q.1,
      WeightedWeakSolution Q M (zeroSumComponents (Fin (n+1)))
        (fun j => if j = i then χ i else 0) ψ :=
    (MatrixEnergy.weightedWeakSolution_existsUnique Q hclosed M _ hpos c hc hlower hm _).exists
  choose ψ hψ using hex
  obtain ⟨u,hu,_hint,_hcov⟩ := CompatibleComparison.ambient_covariance_lift_internal hU hB hV hwell
    A hA M hM FG FK (fun j => if j ∈ J then χ j else 0) b hsource hscorederiv
  rw [hrange] at hu
  have hsum := CompatibleComparison.point_sources_superpose_internal Q hclosed n.succPNat M
    hpos hm c hc hlower J χ ψ (fun i _ => hψ i) u hu
  have hcovsum := CompatibleComparison.ambient_covariance_point_sources_internal n.succPNat
    hU hB hV hwell A hA hrange M hM hpos hm c hc hlower FG FK J χ b hsource hscorederiv ψ
      (fun i _ => hψ i)
  refine ⟨χ,b,hχ,hb,ψ,hψ,hsum ▸ hu,?_,?_⟩
  · exact integrable_finsetSum Finset.univ fun j _ =>
      (Lp.memLp (b j)).integrable_mul (Lp.memLp ((∑ i ∈ J, ψ i j).val))
  · have he : covariance (ScalarForm.value _ FG) (ScalarForm.value _ FK) ν =
        covariance (fun z => G.val (WithLp.ofLp (g z))) (fun z => fderiv ℝ P (g z) d) ν := by
      unfold covariance
      rw [integral_congr_ae hFG,integral_congr_ae hFK]
      exact integral_congr_ae ((hFG.sub (EventuallyEq.rfl)).mul (hFK.sub (EventuallyEq.rfl)))
    exact he.symm.trans hcovsum

/-- See the proof of Lemma 6.5 in the paper: transport all the
point sources, their solutions and mixed pairings through the same two
measurable embeddings. The form is the literal transported closed form. -/
theorem point_source_transport_internal {X Y Z : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (f : X → Y) (hf : MeasurableEmbedding f)
    (j : X → Z) (hj : MeasurableEmbedding j)
    (Q₀ : ScalarFormData (μ.map f)) (hQ₀ : IsClosedScalarDirichletForm Q₀)
    (hc₀ : IsConservativeScalarForm Q₀) (a : ℕ+)
    (M : Z → Matrix (Fin (a : ℕ)) (Fin (a : ℕ)) ℝ)
    (M₀ : Y → Matrix (Fin (a : ℕ)) (Fin (a : ℕ)) ℝ)
    (hfield : M ∘ j =ᵐ[μ] M₀ ∘ f) :
    let Qr := ScalarFormEmbedding.restriction μ f hf Q₀
    let Q := ScalarFormEmbedding.form μ j hj Qr
    let Tf := ScalarFormEmbedding.pullback μ f hf
    let Tj := ScalarFormEmbedding.pullback μ j hj
    IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
    ∀ (χ₀ b₀ : Fin (a : ℕ) → Lp ℝ 2 (μ.map f))
      (ψ₀ : Fin (a : ℕ) → Fin (a : ℕ) → Q₀.1),
      (∀ i, WeightedWeakSolution Q₀ M₀ (zeroSumComponents (Fin (a : ℕ)))
        (fun k => if k = i then χ₀ i else 0) (ψ₀ i)) →
      ∃ χ b : Fin (a : ℕ) → Lp ℝ 2 (μ.map j),
        (∀ i, Tf.symm (Tj (χ i)) = χ₀ i) ∧
        (∀ i, Tf.symm (Tj (b i)) = b₀ i) ∧
        ∃ ψ : Fin (a : ℕ) → Fin (a : ℕ) → Q.1,
          (∀ i, WeightedWeakSolution Q M (zeroSumComponents (Fin (a : ℕ)))
            (fun k => if k = i then χ i else 0) (ψ i)) ∧
          ∀ i, (∫ z, ∑ k, b k z*(ψ i k).val z ∂μ.map j) =
            ∫ y, ∑ k, b₀ k y*(ψ₀ i k).val y ∂μ.map f := by
  intro Qr Q Tf Tj
  have hQr := ScalarFormEmbedding.restriction_closed_dirichlet μ f hf Q₀ hQ₀
  have hcQr := ScalarFormEmbedding.restriction_conservative μ f hf Q₀ hc₀
  refine ⟨ScalarFormEmbedding.closed_dirichlet μ j hj Qr hQr,
    ScalarFormEmbedding.conservative μ j hj Qr hcQr,?_⟩
  intro χ₀ b₀ ψ₀ hψ₀
  let R := ScalarFormEmbedding.restrictionEquiv μ f hf Q₀
  let Dj := ScalarFormEmbedding.domainEquiv μ j hj Qr
  let χ := fun i => Tj.symm (Tf (χ₀ i))
  let b := fun i => Tj.symm (Tf (b₀ i))
  let ψ := fun i k => Dj.symm (R.symm (ψ₀ i k))
  have he (i k) : R (Dj (ψ i k)) = ψ₀ i k := by simp only [ψ,LinearEquiv.apply_symm_apply]
  have hχ (i) : Tf.symm (Tj (χ i)) = χ₀ i := by simp only [χ,LinearIsometryEquiv.apply_symm_apply,LinearIsometryEquiv.symm_apply_apply]
  have hb (i) : Tf.symm (Tj (b i)) = b₀ i := by simp only [b,LinearIsometryEquiv.apply_symm_apply,LinearIsometryEquiv.symm_apply_apply]
  refine ⟨χ,b,hχ,hb,ψ,fun i => ?_,fun i => ?_⟩
  · apply (CompatibleComparison.consecutive_weak_equation_internal μ f hf j hj Q₀ M M₀ hfield
      (zeroSumComponents (Fin (a : ℕ))) (fun k => if k = i then χ i else 0) (ψ i)).mpr
    have hs : (fun k => Tf.symm (Tj (if k = i then χ i else 0))) =
        (fun k => if k = i then χ₀ i else 0) := by
      funext k
      by_cases hk : k = i
      · simp only [ite_eq_left hk,hχ]
      · simp only [ite_eq_right hk,map_zero]
    rw [hs]
    simpa only [ψ,Dj,R,Qr,LinearEquiv.apply_symm_apply] using hψ₀ i
  · simpa only [b,Tf,Tj,ψ,Dj,R,Qr,LinearEquiv.apply_symm_apply,
      LinearIsometryEquiv.apply_symm_apply,LinearIsometryEquiv.symm_apply_apply] using
      (CompatibleComparison.consecutive_pairing_integral_internal μ f hf j hj Q₀ b (ψ i))


/-- Representatives transported through two embeddings agree on their
common carrier, a scalar-class step for the score covariance bridge. -/
theorem consecutive_class_ae_internal {X Y Z : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (f : X → Y) (hf : MeasurableEmbedding f)
    (j : X → Z) (hj : MeasurableEmbedding j)
    (u : Lp ℝ 2 (μ.map j)) (v : Lp ℝ 2 (μ.map f))
    (h : (ScalarFormEmbedding.pullback μ f hf).symm
      (ScalarFormEmbedding.pullback μ j hj u) = v) :
    (fun x => u (j x)) =ᵐ[μ] fun x => v (f x) := by
  have he : ScalarFormEmbedding.pullback μ j hj u = ScalarFormEmbedding.pullback μ f hf v := by
    rw [← h,LinearIsometryEquiv.apply_symm_apply]
  filter_upwards [ScalarFormEmbedding.pullback_ae μ j hj u,
    ScalarFormEmbedding.pullback_ae μ f hf v] with x hx hy
  exact hx.symm.trans ((congrArg (fun w : Lp ℝ 2 μ => w x) he).trans hy)

/-- Internal fixed-length transport of the proved chart covariance data.
The public theorem below supplies that data from the physical score theorem. -/
theorem retained_covariance_of_chart_internal (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ)
    (frame : Tangent n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ)) :
    let P := fun x : EuclideanSpace ℝ (Fin (n+1)) =>
      p.val.1 * ∑ i, (θ.val ((n+1 : ℝ)^(-ε)*x i) +
        θ.val ((n+1 : ℝ)^(-ε)*(x i)⁻¹)) -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n+1) m (Equiv.refl _) (x,z)).toReal)
    (let U := frame '' (centredChart n L.val ⁻¹' massSimplex n L.val)
    let g := fun z => centredChart n L.val (frame.symm z)
    let V := P ∘ g
    let hU : IsOpen U := frame.toHomeomorph.isOpenMap _ (ConditionalWellPosedness.fibre_isOpen n L.val)
    let hB : Bornology.IsBounded U := frame.isometry.lipschitzWith.isBounded_image
      (ConditionalWellPosedness.fibre_isBounded n L.val)
    ∃ ν : Measure (EuclideanSpace ℝ (Fin n)),
      ∃ hV : IsEuclideanGibbsPotential volume ν U V,
        (ν.comap (Subtype.val : U → _)).map
          (InterpolationTransport.orthonormalInclusion n L.val _ L.property.2 frame) =
            retainedKernel p n m θ ε L ∧
        ∀ (G : BlockObservable n.succPNat)
          (_hs : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin (n+1)) => G.val (WithLp.ofLp y)))
          (J : Finset (Fin (n+1))) (_hJ : DependsOnBlockCoordinates G J)
          (d : EuclideanSpace ℝ (Fin (n+1))),
          let Q := IntrinsicScalarCore.form hU hB hV
          let M := fun z => hessianMatrix P (g z)
          ∃ χ b : Fin (n+1) → Lp ℝ 2 ν,
            (∀ i, χ i =ᵐ[ν] fun z => gradient (fun y => G.val (WithLp.ofLp y)) (g z) i) ∧
            (∀ j, b j =ᵐ[ν] fun z => ∑ i, d i*M z i j) ∧
            ∃ ψ : Fin (n+1) → Fin (n+1) → Q.1,
              (∀ i, WeightedWeakSolution Q M (zeroSumComponents (Fin (n+1)))
                (fun j => if j = i then χ i else 0) (ψ i)) ∧
              WeightedWeakSolution Q M (zeroSumComponents (Fin (n+1)))
                (fun j => if j ∈ J then χ j else 0) (∑ i ∈ J, ψ i) ∧
              Integrable (fun z => ∑ j, b j z*(∑ i ∈ J, ψ i j).val z) ν ∧
              covariance (fun z => G.val (WithLp.ofLp (g z)))
                (fun z => fderiv ℝ P (g z) d) ν =
                  ∑ i ∈ J, ∫ z, ∑ j, b j z*(ψ i j).val z ∂ν) →
    let ρ : Measure (chartDomain (n+1) ((n+1+m : ℕ)+1)) := retainedKernel p n m θ ε L
    let M := fun x : chartDomain (n+1) ((n+1+m : ℕ)+1) => hessianMatrix P x.val
    ∃ Q : ScalarFormData ρ, IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
      InterpolationCoefficientBounds.IsIntrinsicFibreForm n L.val ((n+1+m : ℕ)+1) L.property.2 frame ρ Q ∧
      ∀ (G : BlockObservable n.succPNat)
        (_hs : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin (n+1)) => G.val (WithLp.ofLp y)))
        (J : Finset (Fin (n+1))) (_hJ : DependsOnBlockCoordinates G J)
        (d : EuclideanSpace ℝ (Fin (n+1))),
        ∃ χ b : Fin (n+1) → Lp ℝ 2 ρ,
          (∀ i, χ i =ᵐ[ρ] fun x => gradient (fun y => G.val (WithLp.ofLp y)) x.val i) ∧
          (∀ j, b j =ᵐ[ρ] fun x => ∑ i, d i*M x i j) ∧
          ∃ ψ : Fin (n+1) → Fin (n+1) → Q.1,
            (∀ i, WeightedWeakSolution Q M (zeroSumComponents (Fin (n+1)))
              (fun j => if j = i then χ i else 0) (ψ i)) ∧
            WeightedWeakSolution Q M (zeroSumComponents (Fin (n+1)))
              (fun j => if j ∈ J then χ j else 0) (∑ i ∈ J, ψ i) ∧
            covariance (fun x : chartDomain (n+1) ((n+1+m : ℕ)+1) => G.val (WithLp.ofLp x.val))
              (fun x : chartDomain (n+1) ((n+1+m : ℕ)+1) => fderiv ℝ P x.val d) ρ =
                ∑ i ∈ J, ∫ x, ∑ j, b j x*(ψ i j).val x ∂ρ := by
  intro P hL
  obtain ⟨c,hc,hcoerc⟩ := marginal_matrix_coercivity p n m θ ε
  intro ρ M
  let U := frame '' (centredChart n L.val ⁻¹' massSimplex n L.val)
  let g := fun z => centredChart n L.val (frame.symm z)
  let V := P ∘ g
  let hU : IsOpen U := frame.toHomeomorph.isOpenMap _ (ConditionalWellPosedness.fibre_isOpen n L.val)
  let hB : Bornology.IsBounded U := frame.isometry.lipschitzWith.isBounded_image
    (ConditionalWellPosedness.fibre_isBounded n L.val)
  obtain ⟨ν,hV,hlaw,hdata⟩ := hL
  generalize hξ : ν.comap (Subtype.val : U → _) = ξ at hlaw
  let f := (Subtype.val : U → EuclideanSpace ℝ (Fin n))
  let j := InterpolationTransport.orthonormalInclusion n L.val _ L.property.2 frame
  have hf : MeasurableEmbedding f := MeasurableEmbedding.subtype_coe hU.measurableSet
  have hj := InterpolationTransport.measurableEmbedding_orthonormalInclusion n L.val _ L.property.2 frame
  have heν : ξ.map f = ν := by
    rw [← hξ]
    exact (InterpolationTransport.orthonormal_law n L.val _ L.property.2 frame ν V hV).1
  subst ν
  have hV' : IsEuclideanGibbsPotential volume (ξ.map f) U V := hV
  let Q₀ := IntrinsicScalarCore.form hU hB hV'
  let Qr := ScalarFormEmbedding.restriction ξ f hf Q₀
  let Q := ScalarFormEmbedding.form ξ j hj Qr
  let M₀ := fun z => hessianMatrix P (g z)
  have hfield : M ∘ j =ᵐ[ξ] M₀ ∘ f := ae_of_all _ fun _ => rfl
  obtain ⟨hclosed,hcons,htransport⟩ := point_source_transport_internal ξ f hf j hj Q₀
    (IntrinsicScalarCore.closed_dirichlet hU hB hV') (IntrinsicScalarCore.conservative hU hB hV')
    n.succPNat M M₀ hfield
  change ∃ Q : ScalarFormData ρ, _
  have hlaw' : ξ.map j = ρ := hlaw
  rw [← hlaw']
  have hcert : InterpolationCoefficientBounds.IsIntrinsicFibreForm n L.val
      ((n+1+m : ℕ)+1) L.property.2 frame (ξ.map j) Q := by
    refine ⟨ξ.map f,V,hV',?_⟩
    change ∃ Q₁ : ScalarFormData (((ξ.map f).comap (Subtype.val : U → _)).map Subtype.val), _
    have heξ : (ξ.map f).comap (Subtype.val : U → _) = ξ := hξ
    rw [heξ]
    exact ⟨Q₀,IntrinsicScalarCore.realization hU hB hV',
      IntrinsicScalarCore.closed_dirichlet hU hB hV',IntrinsicScalarCore.conservative hU hB hV',
      rfl,HEq.rfl⟩
  refine ⟨Q,hclosed,hcons,hcert,fun G hs J hJ d => ?_⟩
  have hd := hdata G hs J hJ d
  obtain ⟨χ₀,b₀,hχ₀,hb₀,ψ₀,hψ₀,_hsum₀,_hint₀,hcov₀⟩ := hd
  change Fin (n+1) → Lp ℝ 2 (ξ.map f) at χ₀ b₀
  change Fin (n+1) → Fin (n+1) → Q₀.1 at ψ₀
  change (∀ i, WeightedWeakSolution Q₀ M₀ (zeroSumComponents (Fin (n+1)))
    (fun k => if k = i then χ₀ i else 0) (ψ₀ i)) at hψ₀
  have ht := htransport χ₀ b₀ ψ₀
  have ht' := ht hψ₀
  obtain ⟨χ,b,hχ,hb,ψ,hψ,hpair⟩ := ht'
  change Fin (n+1) → Lp ℝ 2 (ξ.map j) at χ b
  change Fin (n+1) → Fin (n+1) → Q.1 at ψ
  change MeasurableEmbedding j at hj

  have hχrep (i : Fin (n+1)) : χ i =ᵐ[ξ.map j] fun x =>
      gradient (fun y => G.val (WithLp.ofLp y)) x.val i := by
    apply hj.ae_map_iff.mpr
    filter_upwards [consecutive_class_ae_internal ξ f hf j hj (χ i) (χ₀ i) (hχ i),
      hf.ae_map_iff.mp (hχ₀ i)] with x hx hy
    exact hx.trans hy
  have hbrep (k : Fin (n+1)) : b k =ᵐ[ξ.map j] fun x => ∑ i, d i*M x i k := by
    apply hj.ae_map_iff.mpr
    filter_upwards [consecutive_class_ae_internal ξ f hf j hj (b k) (b₀ k) (hb k),
      hf.ae_map_iff.mp (hb₀ k)] with x hx hy
    exact hx.trans hy
  have hpos : ∀ᵐ x ∂ξ.map j, (M x).PosSemidef := ae_of_all _ fun x => (hcoerc x).1
  have hlower : ∀ᵐ x ∂ξ.map j, ∀ t ∈ zeroSumComponents (Fin (n+1)),
      c*(∑ i, t i^2) ≤ ∑ i, ∑ k, t i*M x i k*t k :=
    ae_of_all _ fun x t _ => (hcoerc x).2 t
  have hm (i k : Fin (n+1)) : Measurable (fun x => M x i k) :=
    (DifferentiatedPoisson.measurable_hessian_entries (V := P) i k).comp measurable_subtype_coe
  have hsum := WeightedWeakSuperposition.finset_sum Q hclosed M _ hpos c hc hlower hm J
    (fun i k => if k = i then χ i else 0) ψ (fun i _ => hψ i)
  have hsource : (∑ i ∈ J, fun k => if k = i then χ i else 0) =
      (fun k => if k ∈ J then χ k else 0) := by
    funext k
    simp only [Finset.sum_apply,eq_comm,Finset.sum_ite_eq]
  rw [hsource] at hsum
  refine ⟨χ,b,hχrep,hbrep,ψ,hψ,hsum,?_⟩
  have hgret : Measurable (fun x : chartDomain (n+1) ((n+1+m : ℕ)+1) => G.val (WithLp.ofLp x.val)) :=
    hs.continuous.measurable.comp measurable_subtype_coe
  have hdret : Measurable (fun x : chartDomain (n+1) ((n+1+m : ℕ)+1) => fderiv ℝ P x.val d) :=
    (measurable_fderiv_apply_const ℝ P d).comp measurable_subtype_coe
  have hgc : Measurable (fun z => G.val (WithLp.ofLp (g z))) :=
    hs.continuous.measurable.comp
      ((isometry_centredChart n L.val).continuous.measurable.comp frame.symm.continuous.measurable)
  have hdc : Measurable (fun z => fderiv ℝ P (g z) d) :=
    (measurable_fderiv_apply_const ℝ P d).comp
      ((isometry_centredChart n L.val).continuous.measurable.comp frame.symm.continuous.measurable)
  rw [covariance_map hgret.aestronglyMeasurable hdret.aestronglyMeasurable hj.measurable.aemeasurable]
  have hmap := covariance_map (μ := ξ) hgc.aestronglyMeasurable hdc.aestronglyMeasurable hf.measurable.aemeasurable
  change covariance (fun x : U => G.val (WithLp.ofLp (g (f x))))
    (fun x : U => fderiv ℝ P (g (f x)) d) ξ = _
  exact hmap.symm.trans (hcov₀.trans (Finset.sum_congr rfl fun i _ => (hpair i).symm))

/-- See the proof of Lemma 6.5 in the paper: the covariance on the
literal marginal fibre is the sum of the point-source pairings on its
transported retained form. The source is the actual coordinate derivative. The score differential is the full compensated marginal Hessian contraction.
The closed conservative form is chosen before the observable and direction. -/
theorem marginal_score_retained_covariance (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (θ : PhysicalCutoff) (ε : ℝ) (hε : 0 < ε)
    (hhalf : 2*(n+1) ≤ n+1+m+1)
    (frame : Tangent n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    let P := fun x : EuclideanSpace ℝ (Fin (n+1)) =>
      p.val.1 * ∑ i, (θ.val ((n+1 : ℝ)^(-ε)*x i) +
        θ.val ((n+1 : ℝ)^(-ε)*(x i)⁻¹)) -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n+1) m (Equiv.refl _) (x,z)).toReal)
    ∀ᵐ (L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ)) ∂lengthMeasure p n m θ ε,
      let ρ : Measure (chartDomain (n+1) ((n+1+m : ℕ)+1)) := retainedKernel p n m θ ε L
      let M := fun x : chartDomain (n+1) ((n+1+m : ℕ)+1) => hessianMatrix P x.val
      ∃ Q : ScalarFormData ρ, IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
      InterpolationCoefficientBounds.IsIntrinsicFibreForm n L.val ((n+1+m : ℕ)+1) L.property.2 frame ρ Q ∧
        ∀ (G : BlockObservable n.succPNat)
          (_hs : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin (n+1)) => G.val (WithLp.ofLp y)))
          (J : Finset (Fin (n+1))) (_hJ : DependsOnBlockCoordinates G J)
          (d : EuclideanSpace ℝ (Fin (n+1))),
          ∃ χ b : Fin (n+1) → Lp ℝ 2 ρ,
            (∀ i, χ i =ᵐ[ρ] fun x => gradient (fun y => G.val (WithLp.ofLp y)) x.val i) ∧
            (∀ j, b j =ᵐ[ρ] fun x => ∑ i, d i*M x i j) ∧
            ∃ ψ : Fin (n+1) → Fin (n+1) → Q.1,
              (∀ i, WeightedWeakSolution Q M (zeroSumComponents (Fin (n+1)))
                (fun j => if j = i then χ i else 0) (ψ i)) ∧
              WeightedWeakSolution Q M (zeroSumComponents (Fin (n+1)))
                (fun j => if j ∈ J then χ j else 0) (∑ i ∈ J, ψ i) ∧
              covariance (fun x : chartDomain (n+1) ((n+1+m : ℕ)+1) => G.val (WithLp.ofLp x.val))
                (fun x : chartDomain (n+1) ((n+1+m : ℕ)+1) => fderiv ℝ P x.val d) ρ =
                  ∑ i ∈ J, ∫ x, ∑ j, b j x*(ψ i j).val x ∂ρ := by
  intro P
  filter_upwards [marginal_score_chart_covariance p n m hn θ ε hε hhalf frame] with L hL
  exact retained_covariance_of_chart_internal p n m θ ε frame L hL

/-- See the proof of Lemma 6.5 in the paper: all global physical
Hessian pairings on the retained carrier are integrable. The exceptional
null set precedes every scalar form and every choice of solution field. -/
theorem marginal_global_pairings (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) (hε : 0 < ε)
    (hhalf : 2*(n+1) ≤ n+1+m+1) :
    let P := fun x : EuclideanSpace ℝ (Fin (n+1)) =>
      p.val.1 * ∑ i, (θ.val ((n+1 : ℝ)^(-ε)*x i) +
        θ.val ((n+1 : ℝ)^(-ε)*(x i)⁻¹)) -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n+1) m (Equiv.refl _) (x,z)).toReal)
    ∀ᵐ (L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ)) ∂lengthMeasure p n m θ ε,
      ∀ i j : Fin (n+1), ∀ u : Lp ℝ 2 (retainedKernel p n m θ ε L),
        Integrable (fun x => hessianMatrix P x.val i j*u x) (retainedKernel p n m θ ε L) := by
  intro P
  have hP : ContDiffOn ℝ ∞ P (chartDomain (n+1) ((n+1+m : ℕ)+1)) := by
    simpa only [P,ite_true] using MarginalHessian.physical_penalized_marginal_potential_smooth
      p (n+1) m (by omega) (Equiv.refl _) θ
      (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < n+1) (-ε)) Finset.univ true
  filter_upwards [marginal_hessian_memLp_two_ae p n m θ ε hε hhalf] with L hL
  intro i j u
  have hm : Measurable (fun x : chartDomain (n+1) ((n+1+m : ℕ)+1) => hessianMatrix P x.val i j) :=
    (DifferentiatedPoisson.measurable_hessian_entries (V := P) i j).comp measurable_subtype_coe
  have hM : MemLp (fun x => hessianMatrix P x.val i j) 2 (retainedKernel p n m θ ε L) := by
    apply hL.mono' hm.aestronglyMeasurable
    apply ae_of_all
    intro x
    rw [DecayShort.PhysicalComparison.hessianMatrix_entry
      ((hP.contDiffAt ((isOpen_chartDomain _ _).mem_nhds x.property)).of_le (by norm_num))]
    exact ((fderiv ℝ (fderiv ℝ P) x.val (EuclideanSpace.single j 1)).unit_le_opNorm
      (EuclideanSpace.single i 1) (by simp)).trans
      ((fderiv ℝ (fderiv ℝ P) x.val).unit_le_opNorm (EuclideanSpace.single j 1) (by simp))
  exact hM.integrable_mul (Lp.memLp u)

/-- See the proof of Lemma 6.5 in the paper: finite point-source
covariance and the exact normal multipliers give the negative sign.
This internal identity concerns the score term, without assuming a moving
length derivative. All matrix pairings must be integrable. -/
theorem point_source_multiplier_sign_internal {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν] (N : ℕ+)
    (Q : ScalarFormData ν) (M : X → Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (J : Finset (Fin (N : ℕ))) (χ b : Fin (N : ℕ) → Lp ℝ 2 ν)
    (ψ : Fin (N : ℕ) → Fin (N : ℕ) → Q.1)
    (hb : ∀ j, b j =ᵐ[ν] fun x => (N : ℝ)⁻¹*∑ k, M x k j)
    (hpair : ∀ i ∈ J, ∀ k j, Integrable (fun x => M x k j*(ψ i j).val x) ν)
    (C : ℝ) (hcov : C = ∑ i ∈ J, ∫ x, ∑ j, b j x*(ψ i j).val x ∂ν) :
    (N : ℝ)⁻¹*(∑ i ∈ J, ∫ x, χ i x ∂ν)-C =
      -∑ i ∈ J, ∫ x, gapMultiplierField N Q M
        (fun j => if j = i then χ i else 0) (ψ i) x ∂ν := by
  have hi (i : Fin (N : ℕ)) (hi : i ∈ J) :
      (N : ℝ)⁻¹*(∫ x, χ i x ∂ν) - (∫ x, ∑ j, b j x*(ψ i j).val x ∂ν) =
        -(∫ x, gapMultiplierField N Q M (fun j => if j = i then χ i else 0) (ψ i) x ∂ν) := by
    have hm := (multiplier_mean_internal N Q M (fun j => if j = i then χ i else 0)
      (ψ i) (hpair i hi)).2
    have hs : (∑ j, ∫ x, (if j = i then χ i else (0 : Lp ℝ 2 ν)) x ∂ν) = ∫ x, χ i x ∂ν := by
      have he : (fun j => ∫ x, (if j = i then χ i else (0 : Lp ℝ 2 ν)) x ∂ν) =
          (fun j => if j = i then ∫ x, χ i x ∂ν else 0) := by
        funext j
        split_ifs <;> simp
      rw [he]
      simp
    rw [hs] at hm
    have he : (∫ x, ∑ j, b j x*(ψ i j).val x ∂ν) =
        (N : ℝ)⁻¹*(∑ k, ∑ j, ∫ x, M x k j*(ψ i j).val x ∂ν) := by
      calc
        _ = ∫ x, (N : ℝ)⁻¹*∑ k, ∑ j, M x k j*(ψ i j).val x ∂ν := by
          apply integral_congr_ae
          filter_upwards [ae_all_iff.mpr hb] with x hx
          simp only [hx,Finset.mul_sum,Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = _ := by
          rw [integral_const_mul]
          congr 1
          rw [integral_finsetSum Finset.univ (fun k _ =>
            integrable_finsetSum Finset.univ fun j _ => hpair i hi k j)]
          exact Finset.sum_congr rfl fun k _ =>
            integral_finsetSum Finset.univ (fun j _ => hpair i hi k j)
    rw [he,hm]
    ring
  rw [hcov,Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl hi

/-- See the proof of Lemma 6.5 in the paper: the expectation of
the normal observable derivative is the sum of the supported
coordinate sources. Support is the dependence predicate. -/
theorem normal_observable_mean_internal {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν] (n : ℕ)
    (x : X → EuclideanSpace ℝ (Fin (n+1))) (G : BlockObservable n.succPNat)
    (hs : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin (n+1)) => G.val (WithLp.ofLp y)))
    (J : Finset (Fin (n+1))) (hJ : DependsOnBlockCoordinates G J)
    (χ : Fin (n+1) → Lp ℝ 2 ν)
    (hχ : ∀ i, χ i =ᵐ[ν] fun z => gradient (fun y => G.val (WithLp.ofLp y)) (x z) i) :
    (∫ z, fderiv ℝ (fun y => G.val (WithLp.ofLp y)) (x z)
      (WithLp.toLp 2 (fun _ : Fin (n+1) => (n+1 : ℝ)⁻¹)) ∂ν) =
      (n+1 : ℝ)⁻¹*∑ i ∈ J, ∫ z, χ i z ∂ν := by
  have he (z : X) : fderiv ℝ (fun y => G.val (WithLp.ofLp y)) (x z)
      (WithLp.toLp 2 (fun _ : Fin (n+1) => (n+1 : ℝ)⁻¹)) =
        (n+1 : ℝ)⁻¹*∑ i ∈ J, gradient (fun y => G.val (WithLp.ofLp y)) (x z) i := by
    rw [Riesz1.hsCommutator_linear_coordinates]
    simp only [← inner_gradient_left,EuclideanSpace.inner_single_right,conj_trivial,one_mul]
    change (∑ i, gradient (fun y => G.val (WithLp.ofLp y)) (x z) i*(n+1 : ℝ)⁻¹) = _
    rw [← Finset.sum_mul,mul_comm]
    congr 1
    symm
    apply Finset.sum_subset (Finset.subset_univ J)
    intro i _ hi
    exact CompatibleComparison.gradient_zero_off_block_internal n G J hJ (x z)
      (hs.differentiable (by simp) _) i hi
  calc
    _ = ∫ z, (n+1 : ℝ)⁻¹*∑ i ∈ J, χ i z ∂ν := by
      apply integral_congr_ae
      filter_upwards [ae_all_iff.mpr hχ] with z hz
      rw [he]
      simp only [hz]
    _ = _ := by
      rw [integral_const_mul,integral_finsetSum J (fun i _ => (Lp.memLp (χ i)).integrable (by norm_num))]

/-- See the proof of Lemma 6.5 in the paper: the complete smooth
score/multiplier sign identity on the physical marginal fibre, independently
of moving-length differentiation and of the quantitative fibre estimate.
Every multiplier in the finite sum is globally integrable. -/
theorem normal_covariance_multiplier (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (θ : PhysicalCutoff) (ε : ℝ) (hε : 0 < ε)
    (hhalf : 2*(n+1) ≤ n+1+m+1)
    (frame : Tangent n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    let P := fun x : EuclideanSpace ℝ (Fin (n+1)) =>
      p.val.1 * ∑ i, (θ.val ((n+1 : ℝ)^(-ε)*x i) +
        θ.val ((n+1 : ℝ)^(-ε)*(x i)⁻¹)) -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n+1) m (Equiv.refl _) (x,z)).toReal)
    let d₀ := WithLp.toLp 2 (fun _ : Fin (n+1) => (n+1 : ℝ)⁻¹)
    ∀ᵐ (L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ)) ∂lengthMeasure p n m θ ε,
      let ρ : Measure (chartDomain (n+1) ((n+1+m : ℕ)+1)) := retainedKernel p n m θ ε L
      let M := fun x : chartDomain (n+1) ((n+1+m : ℕ)+1) => hessianMatrix P x.val
      ∃ Q : ScalarFormData ρ, IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
        InterpolationCoefficientBounds.IsIntrinsicFibreForm n L.val ((n+1+m : ℕ)+1) L.property.2 frame ρ Q ∧
        ∀ (G : BlockObservable n.succPNat)
          (_hs : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin (n+1)) => G.val (WithLp.ofLp y)))
          (J : Finset (Fin (n+1))) (_hJ : DependsOnBlockCoordinates G J),
          ∃ χ : Fin (n+1) → Lp ℝ 2 ρ,
            (∀ i, χ i =ᵐ[ρ] fun x => gradient (fun y => G.val (WithLp.ofLp y)) x.val i) ∧
            ∃ ψ : Fin (n+1) → Fin (n+1) → Q.1,
              (∀ i, WeightedWeakSolution Q M (zeroSumComponents (Fin (n+1)))
                (fun j => if j = i then χ i else 0) (ψ i)) ∧
              (∀ i, Integrable (gapMultiplierField n.succPNat Q M
                (fun j => if j = i then χ i else 0) (ψ i)) ρ) ∧
              (∫ x, fderiv ℝ (fun y => G.val (WithLp.ofLp y)) x.val d₀ ∂ρ) -
                covariance (fun x : chartDomain (n+1) ((n+1+m : ℕ)+1) => G.val (WithLp.ofLp x.val))
                  (fun x : chartDomain (n+1) ((n+1+m : ℕ)+1) => fderiv ℝ P x.val d₀) ρ =
                  -∑ i ∈ J, ∫ x, gapMultiplierField n.succPNat Q M
                    (fun j => if j = i then χ i else 0) (ψ i) x ∂ρ := by
  intro P d₀
  filter_upwards [marginal_score_retained_covariance p n m hn θ ε hε hhalf frame,
    marginal_global_pairings p n m θ ε hε hhalf] with L hL hpairs
  intro ρ M
  obtain ⟨Q,hQ,hc,hcert,hdata⟩ := hL
  refine ⟨Q,hQ,hc,hcert,fun G hs J hJ => ?_⟩
  obtain ⟨χ,b,hχ,hb,ψ,hψ,_hsum,hcov⟩ := hdata G hs J hJ d₀
  have hb' : ∀ j, b j =ᵐ[ρ] fun x => (n+1 : ℝ)⁻¹*∑ k, M x k j := by
    intro j
    filter_upwards [hb j] with x hx
    calc
      b j x = ∑ i, (n+1 : ℝ)⁻¹*M x i j := hx
      _ = _ := (Finset.mul_sum Finset.univ (fun i => M x i j) (n+1 : ℝ)⁻¹).symm
  have hpair (i k j : Fin (n+1)) : Integrable (fun x => M x k j*(ψ i j).val x) ρ :=
    hpairs k j (ψ i j).val
  have hbN : ∀ j : Fin (n.succPNat : ℕ), b j =ᵐ[ρ] fun x =>
      (n.succPNat : ℝ)⁻¹*∑ k, M x k j := by
    simpa only [Nat.succPNat_coe,Nat.cast_succ] using hb'
  have hsign := point_source_multiplier_sign_internal n.succPNat Q M J χ b ψ hbN
    (fun i _ k j => hpair i k j) _ hcov
  refine ⟨χ,hχ,ψ,hψ,fun i => ?_,?_⟩
  · exact (multiplier_mean_internal n.succPNat Q M (fun j => if j = i then χ i else 0)
      (ψ i) (hpair i)).1
  · rw [normal_observable_mean_internal n (fun x => x.val) G hs J hJ χ hχ]
    simpa only [Nat.succPNat_coe,Nat.cast_succ] using hsign

end Riesz2.LengthDerivative


