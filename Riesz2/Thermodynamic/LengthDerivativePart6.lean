/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.LengthDerivativePart3
public import Riesz2.Thermodynamic.LengthDerivativePart4
public import Riesz2.Thermodynamic.CompatibleComparisonPart4

/-!
# C¹ length derivatives and the conditional multiplier estimate

Steps in the proof of Lemma 6.5. The every-length moving derivative is joined to the
intrinsic point-source covariance. The quantitative estimates assume the conditional
fibre sums, multiplier bounds and error moments.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set Filter Matrix
open scoped ENNReal Topology ContDiff

namespace Riesz2.LengthDerivative

open AffineSimplex LengthAveragingFibres RectangularFormTransport

/-- See the proof of Lemma 6.5 in the paper: the literal supported
coordinate source classes require only C¹ regularity. -/
theorem c1_block_source_internal (a : ℕ) (L : ℝ)
    (frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
    (A : Matrix (Fin (a+1)) (Fin a) ℝ)
    (hA : ∀ t : Fin a → ℝ, A *ᵥ t = (frame.symm (WithLp.toLp 2 t)).val)
    (μ : Measure (EuclideanSpace ℝ (Fin a))) (V : EuclideanSpace ℝ (Fin a) → ℝ)
    (hV : IsEuclideanGibbsPotential volume μ
      (frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)) V)
    (G : BlockObservable (⟨a+1, Nat.succ_pos a⟩ : ℕ+))
    (hs : ContDiff ℝ 1 (fun y : EuclideanSpace ℝ (Fin (a+1)) => G.val (WithLp.ofLp y)))
    (J : Finset (Fin (a+1))) (hJ : DependsOnBlockCoordinates G J) :
    let hU := frame.toHomeomorph.isOpenMap _ (ConditionalWellPosedness.fibre_isOpen a L)
    let hB := frame.isometry.lipschitzWith.isBounded_image
      (ConditionalWellPosedness.fibre_isBounded a L)
    let g := fun x => G.val (WithLp.ofLp (AffineSimplex.centredChart a L (frame.symm x)))
    ∃ F : ScalarForm.Domain (IntrinsicScalarCore.jet hU hB hV),
      ScalarForm.value _ F =ᵐ[μ] g ∧
      ∃ χ : Fin (a+1) → Lp ℝ 2 μ,
        (∀ j, χ j =ᵐ[μ] fun x =>
          gradient (fun y => G.val (WithLp.ofLp y))
            (AffineSimplex.centredChart a L (frame.symm x)) j) ∧
        tupleMap A.transpose (fun j => if j ∈ J then χ j else 0) =
          fun k => DifferentiatedPoisson.coordinateLp k (ScalarForm.deriv _ F) := by
  intro hU hB g
  have := IntrinsicScalarCore.probability hV
  obtain ⟨F,hF,hDF⟩ := CompatibleComparison.block_jet_internal a L frame μ V hV G
  have hg : Continuous (fun x => AffineSimplex.centredChart a L (frame.symm x)) :=
    (AffineSimplex.isometry_centredChart a L).continuous.comp frame.symm.continuous
  have hdg : Continuous (gradient (fun y : EuclideanSpace ℝ (Fin (a+1)) => G.val (WithLp.ofLp y))) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin (a+1)))).symm.continuous.comp
      (hs.continuous_fderiv (by norm_num))
  have hm (i : Fin (a+1)) : MemLp (fun x =>
      gradient (fun y => G.val (WithLp.ofLp y))
        (AffineSimplex.centredChart a L (frame.symm x)) i) 2 μ := by
    exact Riesz1.WeightedSobolev.memLp_of_continuousOn_closure hB
      (IntrinsicScalarCore.supported hU hV)
      (((PiLp.continuous_apply 2 (fun _ : Fin (a+1) => ℝ) i).comp (hdg.comp hg)).continuousOn)
  let χ : Fin (a+1) → Lp ℝ 2 μ := fun i => (hm i).toLp _
  have hχ (i : Fin (a+1)) : χ i =ᵐ[μ] fun x =>
      gradient (fun y => G.val (WithLp.ofLp y))
        (AffineSimplex.centredChart a L (frame.symm x)) i := (hm i).coeFn_toLp
  refine ⟨F,hF,χ,hχ,?_⟩
  apply CompatibleComparison.supported_source_lp_internal a L frame A hA μ
    (fun y => G.val (WithLp.ofLp y))
    (ae_of_all _ fun x => hs.differentiable (by simp) _) J χ ?_ _ hDF
  intro i
  by_cases hi : i ∈ J
  · rw [ite_eq_left hi]
    exact hχ i
  · simp only [ite_eq_right hi]
    filter_upwards [Lp.coeFn_zero ℝ 2 μ] with x hx
    exact hx.trans (CompatibleComparison.gradient_zero_off_block_internal a G J hJ _
      (hs.differentiable (by simp) _) i hi).symm

/-- See the proof of Lemma 6.5 in the paper: C¹ version of the
marginal_score_chart_covariance interface. -/
theorem marginal_score_chart_covariance_c1 (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
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
          ∀ (G : BlockObservable (⟨n+1, Nat.succ_pos n⟩ : ℕ+))
            (_hs : ContDiff ℝ 1 (fun y : EuclideanSpace ℝ (Fin (n+1)) => G.val (WithLp.ofLp y)))
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
    c1_block_source_internal n L.val frame A hact ν V hV G hs J hJ
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

/-- See the proof of Lemma 6.5 in the paper: C¹ version of the
retained_covariance_of_chart_internal interface. -/
theorem retained_covariance_of_chart_internal_c1 (p : Parameters) (n m : ℕ)
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
        ∀ (G : BlockObservable (⟨n+1, Nat.succ_pos n⟩ : ℕ+))
          (_hs : ContDiff ℝ 1 (fun y : EuclideanSpace ℝ (Fin (n+1)) => G.val (WithLp.ofLp y)))
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
      ∀ (G : BlockObservable (⟨n+1, Nat.succ_pos n⟩ : ℕ+))
        (_hs : ContDiff ℝ 1 (fun y : EuclideanSpace ℝ (Fin (n+1)) => G.val (WithLp.ofLp y)))
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

/-- See the proof of Lemma 6.5 in the paper: C¹ version of the
normal_observable_mean_internal interface. -/
theorem normal_observable_mean_internal_c1 {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν] (n : ℕ)
    (x : X → EuclideanSpace ℝ (Fin (n+1))) (G : BlockObservable (⟨n+1, Nat.succ_pos n⟩ : ℕ+))
    (hs : ContDiff ℝ 1 (fun y : EuclideanSpace ℝ (Fin (n+1)) => G.val (WithLp.ofLp y)))
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

/-- See the proof of Lemma 6.5 in the paper: C¹ source superposition
on the retained physical law, with its intrinsic form certificate. -/
theorem marginal_score_retained_covariance_c1 (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
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
        ∀ (G : BlockObservable (⟨n+1, Nat.succ_pos n⟩ : ℕ+))
          (_hs : ContDiff ℝ 1 (fun y : EuclideanSpace ℝ (Fin (n+1)) => G.val (WithLp.ofLp y)))
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
  filter_upwards [marginal_score_chart_covariance_c1 p n m hn θ ε hε hhalf frame] with L hL
  exact retained_covariance_of_chart_internal_c1 p n m θ ε frame L hL

/-- See the proof of Lemma 6.5 in the paper: C¹ score/multiplier
identity, retaining the negative sign and actual multipliers. -/
theorem normal_covariance_multiplier_c1 (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
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
        ∀ (G : BlockObservable (⟨n+1, Nat.succ_pos n⟩ : ℕ+))
          (_hs : ContDiff ℝ 1 (fun y : EuclideanSpace ℝ (Fin (n+1)) => G.val (WithLp.ofLp y)))
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
  filter_upwards [marginal_score_retained_covariance_c1 p n m hn θ ε hε hhalf frame,
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
  · rw [normal_observable_mean_internal_c1 n (fun x => x.val) G hs J hJ χ hχ]
    simpa only [Nat.succPNat_coe,Nat.cast_succ] using hsign

/-- See the proof of Lemma 6.5 in the paper: join the every-point
moving-length derivative to the C¹ intrinsic covariance and finite source
superposition. The derivative is minus the sum of the literal multiplier
means. The form and its certificate precede the observable. -/
theorem c1_averagedObservable_multiplier (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (θ : PhysicalCutoff) (ε : ℝ) (hε : 0 < ε)
    (hhalf : 2*(n+1) ≤ n+1+m+1)
    (frame : Tangent n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (G : BlockObservable (⟨n+1, Nat.succ_pos n⟩ : ℕ+))
    (hG : ContDiff ℝ 1 (fun y : EuclideanSpace ℝ (Fin (n+1)) => G.val (WithLp.ofLp y)))
    (J : Finset (Fin (n+1))) (hJ : DependsOnBlockCoordinates G J) :
    let P := fun x : EuclideanSpace ℝ (Fin (n+1)) =>
      p.val.1 * ∑ i, (θ.val ((n+1 : ℝ)^(-ε)*x i) +
        θ.val ((n+1 : ℝ)^(-ε)*(x i)⁻¹)) -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n+1) m (Equiv.refl _) (x,z)).toReal)
    ∃ H : ℝ → ℝ,
      (∀ L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ),
        H L.val = averagedObservable p n m θ ε G L) ∧
      ContDiffOn ℝ 1 H (Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ)) ∧
      ∀ᵐ L ∂lengthMeasure p n m θ ε,
        let ρ := retainedKernel p n m θ ε L
        let M := fun x : chartDomain (n+1) ((n+1+m : ℕ)+1) => hessianMatrix P x.val
        ∃ Q : ScalarFormData ρ, IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
          InterpolationCoefficientBounds.IsIntrinsicFibreForm n L.val ((n+1+m : ℕ)+1)
            L.property.2 frame ρ Q ∧
          ∃ χ : Fin (n+1) → Lp ℝ 2 ρ,
            (∀ i, χ i =ᵐ[ρ] fun x => gradient (fun y => G.val (WithLp.ofLp y)) x.val i) ∧
            ∃ ψ : Fin (n+1) → Fin (n+1) → Q.1,
              (∀ i, WeightedWeakSolution Q M (zeroSumComponents (Fin (n+1)))
                (fun j => if j = i then χ i else 0) (ψ i)) ∧
              (∀ i, Integrable (gapMultiplierField n.succPNat Q M
                (fun j => if j = i then χ i else 0) (ψ i)) ρ) ∧
              HasDerivAt H (-∑ i ∈ J, ∫ x, gapMultiplierField n.succPNat Q M
                (fun j => if j = i then χ i else 0) (ψ i) x ∂ρ) L.val := by
  intro P
  obtain ⟨H,hH,hs,hd⟩ := smooth_averagedObservable_differentiation p n m θ ε G hG
  refine ⟨H,hH,hs,?_⟩
  have hc : centre n 1 = WithLp.toLp 2 (fun _ : Fin (n+1) => (n+1 : ℝ)⁻¹) := by
    ext i
    simp [centre,div_eq_mul_inv]
  have hscore : (fun x => fderiv ℝ (fun y => p.val.1⁻¹ * P y) x (centre n 1)) =
      fun x => p.val.1⁻¹ * fderiv ℝ P x (centre n 1) := by
    have hh := fderiv_const_smul_field (𝕜 := ℝ) (f := P) p.val.1⁻¹
    exact congrArg (fun D => fun x => D x (centre n 1)) hh
  filter_upwards [normal_covariance_multiplier_c1 p n m hn θ ε hε hhalf frame] with L hL
  intro ρ M
  obtain ⟨Q,hQ,hcons,hcert,hdata⟩ := hL
  obtain ⟨χ,hχ,ψ,hψ,hint,hsign⟩ := hdata G hG J hJ
  refine ⟨Q,hQ,hcons,hcert,χ,hχ,ψ,hψ,hint,?_⟩
  have hdL := (hd L).2.2
  change HasDerivAt H ((∫ x, fderiv ℝ (fun y => G.val (WithLp.ofLp y)) x (centre n 1)
    ∂fibreKernel p n m θ ε L) - p.val.1 * covariance
      (fun x => G.val (WithLp.ofLp x))
      (fun x => fderiv ℝ (fun y => p.val.1⁻¹ * P y) x (centre n 1))
      (fibreKernel p n m θ ε L)) L.val at hdL
  simp only [Nat.succPNat_coe] at hdL hsign
  simp_rw [congrFun hscore] at hdL
  rw [covariance_const_mul_right, ← mul_assoc, mul_inv_cancel₀ p.property.1.ne',
    one_mul, hc, ← map_retainedKernel p n m θ ε L] at hdL
  have hg : Measurable (fun x : EuclideanSpace ℝ (Fin (n+1)) => G.val (WithLp.ofLp x)) :=
    hG.continuous.measurable
  have hdg := measurable_fderiv_apply_const ℝ (fun x : EuclideanSpace ℝ (Fin (n+1)) =>
    G.val (WithLp.ofLp x)) (WithLp.toLp 2 (fun _ : Fin (n+1) => (n+1 : ℝ)⁻¹))
  have hdP := measurable_fderiv_apply_const ℝ P
    (WithLp.toLp 2 (fun _ : Fin (n+1) => (n+1 : ℝ)⁻¹))
  erw [integral_map measurable_subtype_coe.aemeasurable hdg.aestronglyMeasurable,
    covariance_map hg.aestronglyMeasurable hdP.aestronglyMeasurable
      measurable_subtype_coe.aemeasurable] at hdL
  exact hdL.congr_deriv hsign

/-- See Theorem 4 and the proof of Lemma 6.5 of the paper: the actual
Euclidean gradient coordinate is the partial derivative used by the coordinate norms. The coordinate change is a continuous linear equivalence. -/
theorem c1_gradient_partial_internal (n : ℕ) (G : BlockObservable (⟨n+1, Nat.succ_pos n⟩ : ℕ+))
    (hG : ContDiff ℝ 1 (fun y : EuclideanSpace ℝ (Fin (n+1)) => G.val (WithLp.ofLp y))) :
    ContDiff ℝ 1 G.val ∧ ∀ (x : EuclideanSpace ℝ (Fin (n+1))) (i : Fin (n+1)),
      gradient (fun y => G.val (WithLp.ofLp y)) x i =
        fderiv ℝ G.val (WithLp.ofLp x) (Pi.single i 1) := by
  let e := EuclideanSpace.equiv (Fin (n+1)) ℝ
  have hs : ContDiff ℝ 1 G.val := hG.comp e.symm.contDiff
  refine ⟨hs,fun x i => ?_⟩
  have hh := congrArg (fun D : EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] ℝ =>
    D (EuclideanSpace.single i 1))
    (((hs.differentiable (by norm_num) (WithLp.ofLp x)).hasFDerivAt.comp x e.hasFDerivAt).fderiv)
  rw [← inner_gradient_left] at hh
  have he : e (EuclideanSpace.single i 1) = Pi.single i 1 := PiLp.ofLp_single 2 i 1
  simp only [EuclideanSpace.inner_single_right,conj_trivial,one_mul,
    ContinuousLinearMap.comp_apply] at hh
  change gradient (fun y => G.val (WithLp.ofLp y)) x i =
    fderiv ℝ G.val (WithLp.ofLp x) (e (EuclideanSpace.single i 1)) at hh
  exact hh.trans (congrArg (fderiv ℝ G.val (WithLp.ofLp x)) he)

/-- See Theorem 4 and Lemma 6.5 of the paper: coordinates outside the specified
support have zero coordinate norm. Thus the global norm is
the sum over supported coordinates. -/
theorem supported_blockDerivativeNorm_internal {N : ℕ+} (G : BlockObservable N)
    (J : Finset (Fin (N : ℕ))) (hJ : DependsOnBlockCoordinates G J) :
    blockDerivativeNorm G = ∑ i ∈ J, (coordinateDerivativeNorm G i : ℝ) := by
  classical
  have hz (i : Fin (N : ℕ)) (hi : i ∉ J) : coordinateDerivativeNorm G i = 0 := by
    apply le_antisymm _ bot_le
    apply csInf_le (OrderBot.bddBelow _)
    intro x t
    have he : G.val (Function.update x i t) = G.val x := by
      apply hJ
      intro j hj
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      exact Function.update_of_ne hji t x
    simp [he]
  unfold blockDerivativeNorm
  symm
  apply Finset.sum_subset (Finset.subset_univ J)
  intro i _ hi
  simp only [hz i hi,NNReal.coe_zero]

/-- See Lemma 6.5 and the proof of Lemma 6.5 of the paper: C¹ partials
are bounded on the full good event by the exact restricted coordinate
infima, including its boundary, and globally by the coordinate norms. -/
theorem c1_source_bounds_internal (n : ℕ) (G : BlockObservable (⟨n+1, Nat.succ_pos n⟩ : ℕ+))
    (hG : ContDiff ℝ 1 (fun y : EuclideanSpace ℝ (Fin (n+1)) => G.val (WithLp.ofLp y)))
    (A : Set (Fin (n+1) → ℝ)) (hA : Convex ℝ A) (hne : (interior A).Nonempty) :
    ∀ i : Fin (n+1),
      (∀ x : EuclideanSpace ℝ (Fin (n+1)),
        |gradient (fun y => G.val (WithLp.ofLp y)) x i| ≤ (coordinateDerivativeNorm G i : ℝ)) ∧
      ∀ x : EuclideanSpace ℝ (Fin (n+1)), WithLp.ofLp x ∈ A →
        |gradient (fun y => G.val (WithLp.ofLp y)) x i| ≤
          restrictedBlockDerivativeNorm G {i} A := by
  obtain ⟨hs,hpartial⟩ := c1_gradient_partial_internal n G hG
  intro i
  refine ⟨fun x => ?_,fun x hx => ?_⟩
  · rw [hpartial]
    exact CompatibleComparison.coordinate_partial_bound G i (hs.differentiable (by norm_num) _)
  · rw [hpartial]
    simpa only [Finset.sum_singleton] using
      CompatibleComparison.smooth_derivative_sum_le_restricted G hs {i} A hA hne hx

/-- See the proof of Lemma 6.5 in the paper: integrate the complete
conditional conclusion of the proof of Lemma 6.5 for a C¹ observable.
This internal helper keeps its first-plus-second error moment explicit.
Its good-set term uses the restricted derivative norm. -/
theorem c1_weighted_derivative_of_fibres_internal (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (θ : PhysicalCutoff) (ε : ℝ) (hε : 0 < ε)
    (hhalf : 2*(n+1) ≤ n+1+m+1)
    (frame : Tangent n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (κ C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (e : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ) → ℝ≥0∞) (he : Measurable e)
    (hmoment : (∫⁻ L, e L + e L^2 ∂lengthMeasure p n m θ ε) ≤ ENNReal.ofReal R)
    (G : BlockObservable (⟨n+1, Nat.succ_pos n⟩ : ℕ+))
    (hG : ContDiff ℝ 1 (fun y : EuclideanSpace ℝ (Fin (n+1)) => G.val (WithLp.ofLp y)))
    (J : Finset (Fin (n+1))) (hJ : DependsOnBlockCoordinates G J)
    (hmiddle : ∀ i ∈ J, |(i.val : ℝ)+1-(n+1 : ℝ)/2| ≤ (n+1 : ℝ)/4)
    (A : Set (Fin (n+1) → ℝ)) (hA : MeasurableSet A) (hconv : Convex ℝ A)
    (hne : (interior A).Nonempty) :
    let P := fun x : EuclideanSpace ℝ (Fin (n+1)) =>
      p.val.1 * ∑ i, (θ.val ((n+1 : ℝ)^(-ε)*x i) +
        θ.val ((n+1 : ℝ)^(-ε)*(x i)⁻¹)) -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n+1) m (Equiv.refl _) (x,z)).toReal)
    (∀ᵐ L ∂lengthMeasure p n m θ ε,
      let ρ := retainedKernel p n m θ ε L
      let M := fun x : chartDomain (n+1) ((n+1+m : ℕ)+1) => hessianMatrix P x.val
      e L < ⊤ ∧ ∀ (Q : ScalarFormData ρ), IsClosedScalarDirichletForm Q →
        IsConservativeScalarForm Q →
        InterpolationCoefficientBounds.IsIntrinsicFibreForm n L.val ((n+1+m : ℕ)+1)
          L.property.2 frame ρ Q →
        ∀ i : Fin (n+1), |(i.val : ℝ)+1-(n+1 : ℝ)/2| ≤ (n+1 : ℝ)/4 →
        ∀ (χ : Lp ℝ 2 ρ) (B : ℝ), 0 ≤ B → (∀ᵐ x ∂ρ, |χ x| ≤ B) →
        ∀ ψ : Fin (n+1) → Q.1,
          WeightedWeakSolution Q M (zeroSumComponents (Fin (n+1)))
            (fun j => if j = i then χ else 0) ψ →
          (∑ j, ‖(ψ j).val‖) ≤ C*(n+1 : ℝ)^(κ*ε)*‖χ‖+C*B*Real.sqrt (e L).toReal ∧
          (∑ j, InteractionDifferential.boundaryWeight p.val.2 n.succPNat j*‖(ψ j).val‖) ≤
            C*(n+1 : ℝ)^(κ*ε-min p.val.2 1/2)*‖χ‖+C*B*Real.sqrt (e L).toReal ∧
          Integrable (gapMultiplierField n.succPNat Q M (fun j => if j = i then χ else 0) ψ) ρ ∧
          |∫ x, gapMultiplierField n.succPNat Q M (fun j => if j = i then χ else 0) ψ x ∂ρ| ≤
            C*(n+1 : ℝ)^(κ*ε-min p.val.2 1)*‖χ‖+
              C*B*(Real.sqrt (e L).toReal+(e L).toReal)) →
    ∃ H : ℝ → ℝ,
      (∀ L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ),
        H L.val = averagedObservable p n m θ ε G L) ∧
      ContDiffOn ℝ 1 H (Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ)) ∧
      MemLp (fun L => deriv H L.val) 2 (lengthMeasure p n m θ ε) ∧
      (eLpNorm (fun L => deriv H L.val) 2 (lengthMeasure p n m θ ε)).toReal ≤
        C*(n+1 : ℝ)^(κ*ε-min p.val.2 1)*restrictedBlockDerivativeNorm G J A +
          (C*(n+1 : ℝ)^(κ*ε-min p.val.2 1)*
            Real.sqrt ((activeMeasure p n m θ ε).real (WithLp.ofLp ⁻¹' A)ᶜ)+
            2*C*Real.sqrt R)*blockDerivativeNorm G := by
  classical
  intro P hfib
  obtain ⟨H,hmean,hHs,hd⟩ := c1_averagedObservable_multiplier p n m hn θ ε hε hhalf frame G hG J hJ
  let χ₀ := fun (i : Fin (n+1)) (x : EuclideanSpace ℝ (Fin (n+1))) =>
    gradient (fun y => G.val (WithLp.ofLp y)) x i
  let D := fun i : J => restrictedBlockDerivativeNorm G {i.val} A
  let B := fun i : J => (coordinateDerivativeNorm G i.val : ℝ)
  let a := C*(n+1 : ℝ)^(κ*ε-min p.val.2 1)
  have hχ₀ (i : Fin (n+1)) : Measurable (χ₀ i) :=
    (PiLp.continuous_apply 2 _ i).measurable.comp
      ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin (n+1)))).symm.continuous.measurable.comp
        (measurable_fderiv ℝ (fun y : EuclideanSpace ℝ (Fin (n+1)) => G.val (WithLp.ofLp y))))
  have hsource := c1_source_bounds_internal n G hG A hconv hne
  have hD (i : J) : 0 ≤ D i := by simp only [D,restrictedBlockDerivativeNorm,Finset.sum_singleton]; positivity
  have hB (i : J) : 0 ≤ B i := NNReal.coe_nonneg _
  have hgood (i : J) : ∀ᵐ x ∂(activeMeasure p n m θ ε).restrict (WithLp.ofLp ⁻¹' A),
      |χ₀ i.val x| ≤ D i := by
    filter_upwards [ae_restrict_mem (hA.preimage (WithLp.measurable_ofLp 2 _))] with x hx
    exact (hsource i.val).2 x hx
  have hb (i : J) (x) : |χ₀ i.val x| ≤ B i := (hsource i.val).1 x
  have henv : ∀ᵐ L ∂lengthMeasure p n m θ ε, |deriv H L.val| ≤ ∑ i : J,
      (a*Real.sqrt (∫ x, χ₀ i.val x^2 ∂fibreKernel p n m θ ε L)+
        C*B i*(Real.sqrt (e L).toReal+(e L).toReal)) := by
    filter_upwards [hd,hfib] with L hdL hfL
    obtain ⟨Q,hQ,hcons,hcert,χ,hχ,ψ,hψ,_hint,hsign⟩ := hdL
    rw [hsign.deriv,abs_neg]
    have hsum := Finset.abs_sum_le_sum_abs (s := J)
      (fun i => ∫ x, gapMultiplierField n.succPNat Q
        (fun x : chartDomain (n+1) ((n+1+m : ℕ)+1) => hessianMatrix P x.val)
        (fun j => if j = i then χ i else 0) (ψ i) x ∂retainedKernel p n m θ ε L)
    apply hsum.trans
    trans ∑ i : J, |∫ x, gapMultiplierField n.succPNat Q
      (fun x : chartDomain (n+1) ((n+1+m : ℕ)+1) => hessianMatrix P x.val)
      (fun j => if j = i.val then χ i.val else 0) (ψ i.val) x ∂retainedKernel p n m θ ε L|
    · exact (Finset.sum_coe_sort J _).symm.le
    apply Finset.sum_le_sum
    intro i _
    have hχB : ∀ᵐ x ∂retainedKernel p n m θ ε L, |χ i.val x| ≤ B i := by
      filter_upwards [hχ i.val] with x hx
      rw [hx]
      exact hb i x.val
    have hbound := (hfL.2 Q hQ hcons hcert i.val (hmiddle _ i.property)
      (χ i.val) (B i) (hB i) hχB (ψ i.val) (hψ i.val)).2.2.2
    have hnorm : ‖χ i.val‖ = Real.sqrt (∫ x, χ₀ i.val x^2 ∂fibreKernel p n m θ ε L) := by
      rw [← map_retainedKernel p n m θ ε L,
        integral_map measurable_subtype_coe.aemeasurable ((hχ₀ i.val).pow_const 2).aestronglyMeasurable]
      have hi := integral_congr_ae ((hχ i.val).fun_comp (fun t : ℝ => t^2))
      change (∫ x, (χ i.val x)^2 ∂retainedKernel p n m θ ε L) =
        ∫ x, χ₀ i.val x.val^2 ∂retainedKernel p n m θ ε L at hi
      rw [CyclicFourierL2.integral_sq] at hi
      rw [← hi,Real.sqrt_sq (norm_nonneg _)]
    simpa only [hnorm] using hbound
  have hi := integrated_multiplier_internal p n m θ ε (fun i : J => χ₀ i.val)
    (fun i => hχ₀ i.val) (hA.preimage (WithLp.measurable_ofLp 2 _)) D B hD hB hgood hb
    he hR hmoment (by dsimp [a]; positivity) hC
    ((measurable_deriv H).comp measurable_subtype_coe).aestronglyMeasurable henv
  refine ⟨H,hmean,hHs,hi.1,hi.2.trans ?_⟩
  have hDsum : (∑ i : J, D i) = restrictedBlockDerivativeNorm G J A := by
    calc
      (∑ i : J, D i) = ∑ i ∈ J, restrictedBlockDerivativeNorm G {i} A :=
        Finset.sum_coe_sort J (fun i : Fin (n+1) => restrictedBlockDerivativeNorm G {i} A)
      _ = _ := by
        simp only [restrictedBlockDerivativeNorm,Finset.sum_singleton]
        rfl
  have hBsum : (∑ i : J, B i) ≤ blockDerivativeNorm G := by
    change (∑ i : J, (coordinateDerivativeNorm G i.val : ℝ)) ≤
      ∑ i, (coordinateDerivativeNorm G i : ℝ)
    exact (Finset.sum_coe_sort J (fun i => (coordinateDerivativeNorm G i : ℝ))).le.trans
      (Finset.sum_le_univ_sum_of_nonneg (fun i => NNReal.coe_nonneg _))
  rw [hDsum]
  change a * restrictedBlockDerivativeNorm G J A +
    (a*Real.sqrt ((activeMeasure p n m θ ε).real (WithLp.ofLp ⁻¹' A)ᶜ)+2*C*Real.sqrt R)*(∑ i, B i) ≤
      a * restrictedBlockDerivativeNorm G J A +
        (a*Real.sqrt ((activeMeasure p n m θ ε).real (WithLp.ofLp ⁻¹' A)ᶜ)+2*C*Real.sqrt R)*blockDerivativeNorm G
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hcoef : 0 ≤ a*Real.sqrt ((activeMeasure p n m θ ε).real (WithLp.ofLp ⁻¹' A)ᶜ)+2*C*Real.sqrt R := by positivity
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hBsum hcoef)

/-- See Appendix C in the paper, as used in
the proof of Lemma 6.5: the actual active good event has a
stretched-exponentially small complement, uniformly on compact temperature
intervals. The tail power is fixed before temperature and cutoff. -/
theorem active_good_event_probability (hRig : External.LongRangeRigidityLocallyUniform)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ ηstar astar : ℝ, 0 < ηstar ∧ 0 < astar ∧
      ∀ η : ℝ, 0 < η → η ≤ ηstar → ∀ ε : ℝ, 0 < ε →
      ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
        ∀ n m : ℕ, 1 ≤ n → 4*(n+1) ≤ n+1+m+1 →
          (n+1 : ℝ)^(2/s) ≤ ((n+1+m : ℕ)+1 : ℝ) →
          (activeMeasure p n m θ ε).real
            (WithLp.ofLp ⁻¹' goodBlockEvent s n.succPNat (n+1+m).succPNat η)ᶜ ≤
              C*Real.exp (-c*(n+1 : ℝ)^(astar*η)) := by
  obtain ⟨ηstar,astar,hηstar,hastar,hlocal⟩ :=
    InterpolantLocalLaws.compact_full_law_weighted_rigidity hRig s hs hs1
  refine ⟨ηstar,astar,hηstar,hastar,fun η hη hηstar ε hε βlo βhi hlo hle θ => ?_⟩
  obtain ⟨C,c,hC,hc,hbound⟩ := hlocal η hη hηstar ε hε βlo βhi hlo hle θ
  refine ⟨C,c,hC,hc,fun p hps hpl hph n m hn hsize hscale => ?_⟩
  let N := (n+1+m).succPNat
  let a := n.succPNat
  let hnN : (a : ℕ) ≤ (N : ℕ) := by simp only [a,N,Nat.succPNat_coe]; omega
  let μ := tiltedParticleMeasure p N a hnN θ ε true
  let A : Set (EuclideanSpace ℝ (Fin (n+1))) := WithLp.ofLp ⁻¹' goodBlockEvent s a N η
  have hA : MeasurableSet A :=
    (InterpolantLocalLaws.measurableSet_goodBlockEvent s a N η).preimage
      (WithLp.measurable_ofLp 2 _)
  have hm : Measurable (fun X : Riesz1.Configuration N =>
      WithLp.toLp 2 (finiteGapBlock (K := a) X)) :=
    (WithLp.measurable_toLp 2 _).comp
      (measurable_pi_iff.mpr fun i => Riesz1.measurable_gap i.val)
  have hprob : activeMeasure p n m θ ε Aᶜ ≤
      ENNReal.ofReal (C*Real.exp (-c*(n+1 : ℝ)^(astar*η))) := by
    have hscl : (a : ℝ)^(2/s) ≤ (N : ℝ) := by
      simpa only [a,N,Nat.succPNat_coe,Nat.cast_add,Nat.cast_one,Nat.cast_succ] using hscale
    have ht := hbound p hps hpl hph N a (by simp only [a,Nat.succPNat_coe]; omega)
      hsize hscl hnN
    simp only [a,Nat.succPNat_coe,Nat.cast_succ] at ht
    change (μ.map (fun X => WithLp.toLp 2 (finiteGapBlock (K := a) X))) Aᶜ ≤ _
    rw [Measure.map_apply hm hA.compl]
    apply le_trans _ ht
    calc
      _ = ∫⁻ _X in {X : Riesz1.Configuration N | finiteGapBlock (K := a) X ∉
          goodBlockEvent s a N η}, (1 : ℝ≥0∞) ∂μ := by
            rw [lintegral_one,Measure.restrict_apply_univ]
            rfl
      _ ≤ _ := by
        apply lintegral_mono
        intro X
        have hw := InterpolantLocalLaws.one_le_exceptionalWeight s (finiteGapBlock (K := a) X)
          (fun i => (Riesz1.gap_pos X i.val).le)
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hw
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hprob

/-- The C¹ stage of the proof of Lemma 6.5 assumes the conditional sums,
multiplier bounds and error moments. The weighted derivative has the stated
rate and good-set norm. The loss is supplied before epsilon. The output
tail power precedes the compact temperature interval. -/
theorem c1_length_averaging_derivative_internal
    (hRig : External.LongRangeRigidityLocallyUniform)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) (κ : ℝ) :
    ∃ ηstar astar : ℝ, 0 < ηstar ∧ 0 < astar ∧
      ∀ ε η : ℝ, 0 < ε → 0 < η → η ≤ ηstar →
      ∀ δf : ℝ, 0 < δf → ∃ δ : ℝ, 0 < δ ∧
      ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
      ∀ Cf cf : ℝ, 0 < Cf → 0 < cf → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ n m : ℕ, 1 ≤ n → 4*(n+1) ≤ n+1+m+1 →
        (n+1 : ℝ)^(2/s) ≤ ((n+1+m : ℕ)+1 : ℝ) →
      ∀ e : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ) → ℝ≥0∞, Measurable e →
      (∫⁻ L, e L+e L^2 ∂lengthMeasure p n m θ ε) ≤
        ENNReal.ofReal (Cf*Real.exp (-cf*(n+1 : ℝ)^δf)) →
    let P := fun x : EuclideanSpace ℝ (Fin (n+1)) =>
      p.val.1 * ∑ i, (θ.val ((n+1 : ℝ)^(-ε)*x i) +
        θ.val ((n+1 : ℝ)^(-ε)*(x i)⁻¹)) -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n+1) m (Equiv.refl _) (x,z)).toReal)
    (∀ frame : Tangent n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ᵐ L ∂lengthMeasure p n m θ ε,
      let ρ := retainedKernel p n m θ ε L
      let M := fun x : chartDomain (n+1) ((n+1+m : ℕ)+1) => hessianMatrix P x.val
      e L < ⊤ ∧ ∀ (Q : ScalarFormData ρ), IsClosedScalarDirichletForm Q →
        IsConservativeScalarForm Q →
        InterpolationCoefficientBounds.IsIntrinsicFibreForm n L.val ((n+1+m : ℕ)+1)
          L.property.2 frame ρ Q →
        ∀ i : Fin (n+1), |(i.val : ℝ)+1-(n+1 : ℝ)/2| ≤ (n+1 : ℝ)/4 →
        ∀ (χ : Lp ℝ 2 ρ) (B : ℝ), 0 ≤ B → (∀ᵐ x ∂ρ, |χ x| ≤ B) →
        ∀ ψ : Fin (n+1) → Q.1,
          WeightedWeakSolution Q M (zeroSumComponents (Fin (n+1)))
            (fun j => if j = i then χ else 0) ψ →
          (∑ j, ‖(ψ j).val‖) ≤ Cf*(n+1 : ℝ)^(κ*ε)*‖χ‖+Cf*B*Real.sqrt (e L).toReal ∧
          (∑ j, InteractionDifferential.boundaryWeight p.val.2 n.succPNat j*‖(ψ j).val‖) ≤
            Cf*(n+1 : ℝ)^(κ*ε-min p.val.2 1/2)*‖χ‖+Cf*B*Real.sqrt (e L).toReal ∧
          Integrable (gapMultiplierField n.succPNat Q M (fun j => if j = i then χ else 0) ψ) ρ ∧
          |∫ x, gapMultiplierField n.succPNat Q M (fun j => if j = i then χ else 0) ψ x ∂ρ| ≤
            Cf*(n+1 : ℝ)^(κ*ε-min p.val.2 1)*‖χ‖+
              Cf*B*(Real.sqrt (e L).toReal+(e L).toReal)) →
    ∀ G : BlockObservable (⟨n+1, Nat.succ_pos n⟩ : ℕ+),
      ContDiff ℝ 1 (fun y : EuclideanSpace ℝ (Fin (n+1)) => G.val (WithLp.ofLp y)) →
      ∀ J : Finset (Fin (n+1)), DependsOnBlockCoordinates G J →
        (∀ i ∈ J, |(i.val : ℝ)+1-(n+1 : ℝ)/2| ≤ (n+1 : ℝ)/4) →
      ∃ H : ℝ → ℝ,
        (∀ L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ),
          H L.val = averagedObservable p n m θ ε G L) ∧
        ContDiffOn ℝ 1 H (Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ)) ∧
        MemLp (fun L => deriv H L.val) 2 (lengthMeasure p n m θ ε) ∧
        (eLpNorm (fun L => deriv H L.val) 2 (lengthMeasure p n m θ ε)).toReal ≤
          C*(n+1 : ℝ)^(κ*ε-min p.val.2 1)*
            restrictedBlockDerivativeNorm G J
              (goodBlockEvent p.val.2 n.succPNat (n+1+m).succPNat η) +
          C*Real.exp (-c*(n+1 : ℝ)^δ)*blockDerivativeNorm G := by
  obtain ⟨ηstar,astar,hηstar,hastar,hbad⟩ := active_good_event_probability hRig s hs hs1
  refine ⟨ηstar,astar,hηstar,hastar,fun ε η hε hη hηstar δf hδf => ?_⟩
  let δ := min δf (astar*η)
  have hδ : 0 < δ := lt_min hδf (mul_pos hastar hη)
  refine ⟨δ,hδ,fun βlo βhi hlo hle θ Cf cf hCf hcf => ?_⟩
  obtain ⟨Q,q,hQ,hq,hprob⟩ := hbad η hη hηstar ε hε βlo βhi hlo hle θ
  let c₀ := min cf q
  have hc₀ : 0 < c₀ := lt_min hcf hq
  obtain ⟨K,hK,habsorb⟩ := KernelSquareNorm.exponential_tail_coefficient
    (loss := κ*ε-min s 1) hCf.le hQ.le hCf.le hc₀ hδ
  refine ⟨Cf+K,c₀/4,by positivity,by positivity,?_⟩
  intro p hps hpl hph n m hn hsize hpower e he hmoment P hfib G hG J hJ hmiddle
  let frame : Tangent n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    ((stdOrthonormalBasis ℝ (Tangent n)).reindex (finCongr (finrank_tangent n))).repr
  let A := goodBlockEvent p.val.2 n.succPNat (n+1+m).succPNat η
  let R := Cf*Real.exp (-cf*(n+1 : ℝ)^δf)
  have hA : MeasurableSet A := InterpolantLocalLaws.measurableSet_goodBlockEvent _ _ _ _
  have hconv : Convex ℝ A := InterpolantLocalLaws.convex_goodBlockEvent _ _ _ _
  have hne : (interior A).Nonempty := ⟨_,
    CompatibleComparison.one_mem_interior_fine_event p.val.2 η hη n.succPNat
      (n+1+m).succPNat (by simp only [Nat.succPNat_coe]; omega)
      (by simp only [Nat.succPNat_coe]; omega)⟩
  obtain ⟨H,hmean,hHs,hmem,hbound⟩ := c1_weighted_derivative_of_fibres_internal
    p n m hn θ ε hε (by omega) frame κ Cf R hCf.le (by dsimp [R]; positivity)
    e he hmoment G hG J hJ hmiddle A hA hconv hne (hfib frame)
  refine ⟨H,hmean,hHs,hmem,hbound.trans ?_⟩
  have hx : 1 ≤ (n+1 : ℝ) := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have htail {d b : ℝ} (hd : δ ≤ d) (hb : c₀ ≤ b) :
      Real.exp (-b*(n+1 : ℝ)^d) ≤ Real.exp (-c₀*(n+1 : ℝ)^δ) := by
    apply Real.exp_le_exp.mpr
    have ht := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx hd) hc₀.le
    have ht' := mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg (show 0 ≤ (n+1 : ℝ) by positivity) d)
    linarith
  have hpr : (activeMeasure p n m θ ε).real (WithLp.ofLp ⁻¹' A)ᶜ ≤
      Q*Real.exp (-c₀*(n+1 : ℝ)^δ) := by
    have hp := hprob p hps hpl hph n m hn hsize hpower
    rw [← hps] at hp
    exact hp.trans (mul_le_mul_of_nonneg_left
      (htail (min_le_right _ _) (min_le_right _ _)) hQ.le)
  have hr : R ≤ Cf*Real.exp (-c₀*(n+1 : ℝ)^δ) :=
    mul_le_mul_of_nonneg_left (htail (min_le_left _ _) (min_le_left _ _)) hCf.le
  have heff := habsorb (n+1 : ℝ) hx
    ((activeMeasure p n m θ ε).real (WithLp.ofLp ⁻¹' A)ᶜ) R hpr hr
  rw [← hps] at heff
  have hDA : 0 ≤ restrictedBlockDerivativeNorm G J A := by
    unfold restrictedBlockDerivativeNorm; positivity
  have hDB : 0 ≤ blockDerivativeNorm G := by unfold blockDerivativeNorm; positivity
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hK.le) (by positivity)) hDA
  · exact (mul_le_mul_of_nonneg_right heff hDB).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCf.le) (Real.exp_pos _).le) hDB)

end Riesz2.LengthDerivative
