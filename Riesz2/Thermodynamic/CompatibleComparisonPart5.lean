/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.CompatibleComparisonPart3
public import Riesz2.Thermodynamic.CompatibleComparisonPart4
public import Riesz2.ToMathlib.GibbsPotentialLocalCongruence

/-!
# One physical law for compatible conditional comparison

Reindexing and local realization bridges for the proof of Proposition 6.6. All
constructions use the existing simplex, ambient energy, and normalized Hausdorff laws.
-/

public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal ContDiff Topology

namespace Riesz2.CompatibleComparison

/-- See Subsection 6.1 and the proof of Proposition 6.6 of the paper: casting the
dimension of a Euclidean coordinate vector is the existing relabelling
isometry for `finCongr`. -/
theorem finCongr_vector_heq_internal {m n : ℕ} (h : m = n)
    (x : EuclideanSpace ℝ (Fin m)) :
    HEq x (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr h) x) := by
  subst n
  rfl

/-- See Subsection 6.1 and the proof of Proposition 6.6 of the paper: the exterior-first
assembly is literally the active-first concatenation, after the forced
cast of the total size. No cyclic invariance of the energy is needed. -/
theorem exterior_assembly_active_first_internal (a d : ℕ)
    (u : EuclideanSpace ℝ (Fin (a+1))) (y : EuclideanSpace ℝ (Fin (d+1))) :
    HEq (RetainedSimplex.assemble (a+1) d (Equiv.refl _) u y)
      (RetainedSimplex.assemble (d+1) a
        (InterpolatingDensities.exteriorPermutation (d+1) a) y u) := by
  let h : a+1+d+1 = d+1+a+1 := by omega
  apply (finCongr_vector_heq_internal h _).trans
  apply heq_of_eq
  apply PiLp.ext
  intro i
  obtain ⟨k,rfl⟩ := (InterpolatingDensities.exteriorPermutation (d+1) a).surjective i
  simp only [RetainedSimplex.assemble,LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'_apply,Equiv.symm_apply_apply]
  change RetainedSimplex.join (a+1) (d+1) (u,y)
      (Fin.cast h.symm (InterpolatingDensities.exteriorPermutation (d+1) a k)) =
    RetainedSimplex.join (d+1) (a+1) (y,u) k
  refine Fin.addCases (m := d+1) (n := a+1) (fun j => ?_) (fun j => ?_) k
  · have hj := InterpolatingDensities.exteriorPermutation_retained (d+1) a j
    have hc : (j.castAdd a).castSucc = j.castAdd (a+1) := by apply Fin.ext; rfl
    rw [hc] at hj
    have he : Fin.cast h.symm
        (InterpolatingDensities.exteriorPermutation (d+1) a (j.castAdd (a+1))) =
        j.natAdd (a+1) := by
      apply Fin.ext
      simpa only [Fin.val_cast,Fin.val_natAdd] using congrArg Fin.val hj
    rw [he,RetainedSimplex.join_right,RetainedSimplex.join_left]
  · have hj := InterpolatingDensities.exteriorPermutation_active (d+1) a j (by omega)
    have he : Fin.cast h.symm
        (InterpolatingDensities.exteriorPermutation (d+1) a (j.natAdd (d+1))) =
        j.castAdd (d+1) := by
      apply Fin.ext
      simpa only [Fin.val_cast,Fin.val_castLE,Fin.val_castAdd] using congrArg Fin.val hj
    rw [he,RetainedSimplex.join_left,RetainedSimplex.join_right]

/-- See Subsection 6.1 of the paper: dependent casts of the volume and its complete
gap vector preserve the physical ambient energy. -/
theorem ambient_energy_heq_internal (p : Parameters) {N M : ℕ+} (h : N = M)
    (x : {x : EuclideanSpace ℝ (Fin (N : ℕ)) // x ∈ gapAmbientDomain N})
    (y : {y : EuclideanSpace ℝ (Fin (M : ℕ)) // y ∈ gapAmbientDomain M})
    (he : HEq x.val y.val) :
    physicalAmbientGapEnergy p N x = physicalAmbientGapEnergy p M y := by
  subst M
  have he' : x = y := Subtype.ext (eq_of_heq he)
  rw [he']

/-- See Subsection 6.1 and the proof of Proposition 6.6 of the paper: an ambient
exterior-first endpoint and the active-first endpoint used by the intrinsic
analytic construction agree on the entire physical open fibre. -/
theorem endpoint_realization_alignment_internal (p : Parameters) (a d : ℕ) (L : ℝ)
    (y : AffineSimplex.chartDomain (d+1) ((d+1+a : ℕ)+1))
    (hyL : ((d+1+a : ℕ)+1 : ℝ)-∑ i, y.val i = L)
    (K : EuclideanSpace ℝ (Fin (a+1)) → ℝ)
    (hK : ∀ u (hu : RetainedSimplex.assemble (d+1) a
      (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u ∈
        gapAmbientDomain (d+1+a).succPNat),
      K u = physicalAmbientGapEnergy p (d+1+a).succPNat
        ⟨RetainedSimplex.assemble (d+1) a
          (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u,hu⟩)
    (J : AffineSimplex.Tangent a → ℝ)
    (hJ : ∀ w (_hw : AffineSimplex.centredChart a L w ∈ AffineSimplex.massSimplex a L),
      ∃ hu : RetainedSimplex.assemble (a+1) d (Equiv.refl _)
        (AffineSimplex.centredChart a L w) y.val ∈ gapAmbientDomain (a+1+d).succPNat,
        J w = physicalAmbientGapEnergy p (a+1+d).succPNat
          ⟨RetainedSimplex.assemble (a+1) d (Equiv.refl _)
            (AffineSimplex.centredChart a L w) y.val,hu⟩) :
    EqOn (fun w => K (AffineSimplex.centredChart a L w)) J
      (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L) := by
  intro w hw
  dsimp only
  obtain ⟨hu,hJw⟩ := hJ w hw
  rw [hK _ (InterpolationCoefficientBounds.fibre_mem_internal (d+1) a y L hyL hw),hJw]
  apply ambient_energy_heq_internal p (by apply PNat.eq; simp only [Nat.succPNat_coe]; omega)
  exact (exterior_assembly_active_first_internal a d _ y.val).symm

section Physical

variable (p : Parameters) (a d e : ℕ) (ha : 1 ≤ a)
    (θ : PhysicalCutoff) (ε L : ℝ) (hL : 0 < L)
    (y : AffineSimplex.chartDomain (d+1) ((d+1+a : ℕ)+1))
    (z : AffineSimplex.chartDomain (e+1) ((e+1+a : ℕ)+1))
    (hyL : ((d+1+a : ℕ)+1 : ℝ)-∑ i, y.val i = L)
    (hzL : ((e+1+a : ℕ)+1 : ℝ)-∑ i, z.val i = L)
    (Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ)
    (hKy : ∀ u (hu : RetainedSimplex.assemble (d+1) a
      (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u ∈
        gapAmbientDomain (d+1+a).succPNat),
      Ky u = physicalAmbientGapEnergy p (d+1+a).succPNat
        ⟨RetainedSimplex.assemble (d+1) a
          (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u,hu⟩)
    (hKz : ∀ u (hu : RetainedSimplex.assemble (e+1) a
      (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u ∈
        gapAmbientDomain (e+1+a).succPNat),
      Kz u = physicalAmbientGapEnergy p (e+1+a).succPNat
        ⟨RetainedSimplex.assemble (e+1) a
          (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u,hu⟩)

include ha hL hyL hzL hKy hKz in
/-- See the proof of Proposition 6.6 in the paper: the full physical analytic
construction is valid for the specified ambient endpoint realizations used
by the coefficient and decay theorems. The collision constant precedes
time. The potential includes the physical β. -/
theorem physical_intrinsic_wellposed_internal :
    let Ω := AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L
    let H := fun (t : ℝ) (u : EuclideanSpace ℝ (Fin (a+1))) =>
      (∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u i)+θ.val ((a+1 : ℝ)^(-ε)*(u i)⁻¹)))+
        (1-t)*Ky u+t*Kz u
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) 1,
    let V := fun w : AffineSimplex.Tangent a => p.val.1*H t (AffineSimplex.centredChart a L w)
    ∃ μ : Measure (AffineSimplex.Tangent a),
      IsEuclideanGibbsPotential volume μ Ω V ∧
      (∀ w ∈ Ω, ∀ u : AffineSimplex.Tangent a,
        (2*p.val.1*(p.val.2*(p.val.2+1))*L^(-p.val.2-2))*‖u‖^2 ≤
          fderiv ℝ (fderiv ℝ V) w u u) ∧
      (∀ w ∈ Ω, (Metric.infDist w (frontier Ω))⁻¹^2-B ≤
        ‖gradient V w‖^2/4-Laplacian.laplacian V w/2) := by
  intro Ω H
  have hy : ∀ i, 0 < y.val i := y.property.1
  have hz : ∀ i, 0 < z.val i := z.property.1
  have hcy : L+∑ i, y.val i = ((a+1+d : ℕ)+1 : ℝ) := by
    have heq : ((d+1+a : ℕ)+1 : ℝ) = ((a+1+d : ℕ)+1 : ℝ) := by push_cast; ring
    linarith only [hyL,heq]
  have hcz : L+∑ i, z.val i = ((a+1+e : ℕ)+1 : ℝ) := by
    have heq : ((e+1+a : ℕ)+1 : ℝ) = ((a+1+e : ℕ)+1 : ℝ) := by push_cast; ring
    linarith only [hzL,heq]
  have hinput := ConditionalWellPosedness.compatible_conditionals_wellposed p a d e ha
      (Equiv.refl _) (Equiv.refl _) hL y.val hy z.val hz hcy hcz θ
      (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < a+1) (-ε)) Finset.univ true
  dsimp only at hinput
  let Jy := hinput.choose
  let Jz := hinput.choose_spec.choose
  have hrest := hinput.choose_spec.choose_spec
  have hJy := hrest.1
  have hJz := hrest.2.1
  let B := hrest.2.2.choose
  have hB := hrest.2.2.choose_spec.1
  have hpath := hrest.2.2.choose_spec.2
  have hey := endpoint_realization_alignment_internal p a d L y hyL Ky hKy Jy
    (fun w hw => ⟨_,hJy w hw⟩)
  have hez := endpoint_realization_alignment_internal p a e L z hzL Kz hKz Jz
    (fun w hw => ⟨_,hJz w hw⟩)
  refine ⟨B,hB,?_⟩
  intro t ht V
  let ρ := (hpath t ht).choose
  have hρ := (hpath t ht).choose_spec.1
  have hcurv := (hpath t ht).choose_spec.2.1
  have hbar := (hpath t ht).choose_spec.2.2.1
  let W := fun w => p.val.1*H t (AffineSimplex.centredChart a L w)
  let W₀ := fun w : AffineSimplex.Tangent a => p.val.1 *
    ((∑ i, (θ.val ((a+1 : ℝ)^(-ε)*AffineSimplex.centredChart a L w i)+
      θ.val ((a+1 : ℝ)^(-ε)*(AffineSimplex.centredChart a L w i)⁻¹)))+
        (1-t)*Jy w+t*Jz w)
  have he : EqOn W W₀ Ω := by
    intro w hw
    dsimp only [W,H,W₀]
    rw [show Ky (AffineSimplex.centredChart a L w) = Jy w from hey hw,
      show Kz (AffineSimplex.centredChart a L w) = Jz w from hez hw]
  have hρ' : IsEuclideanGibbsPotential volume ρ Ω W₀ := by
    simpa only [W₀,ite_true,Nat.cast_add,Nat.cast_one] using hρ
  have hopen : IsOpen Ω := ConditionalWellPosedness.fibre_isOpen a L
  have hW := GibbsPotentialLocalCongruence.congr hρ' hopen.measurableSet he.symm
  have heN (w) (hw : w ∈ Ω) : W =ᶠ[𝓝 w] W₀ := by
    filter_upwards [hopen.mem_nhds hw] with x hx
    exact he hx
  have hcurvW : ∀ w ∈ Ω, ∀ u : AffineSimplex.Tangent a,
      (2*p.val.1*(p.val.2*(p.val.2+1))*L^(-p.val.2-2))*‖u‖^2 ≤
        fderiv ℝ (fderiv ℝ W) w u u := by
    intro w hw u
    rw [(heN w hw).fderiv.fderiv_eq]
    exact hcurv w hw u
  have hbarW : ∀ w ∈ Ω, (Metric.infDist w (frontier Ω))⁻¹^2-B ≤
      ‖gradient W w‖^2/4-Laplacian.laplacian W w/2 := by
    intro w hw
    rw [(heN w hw).gradient_eq,
      (InnerProductSpace.laplacian_congr_nhds (heN w hw)).eq_of_nhds]
    exact hbar w hw
  exact ⟨ρ,hW,hcurvW,hbarW⟩

include ha hL hyL hzL hKy hKz in
/-- See the proof of Proposition 6.6 in the paper: full analytic well-posedness
and the ground-state barrier on each specified orthonormal chart, for the
same physical potential used by the ambient coefficient estimates. -/
theorem physical_chart_wellposed_internal :
    let Ω := AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L
    let H := fun (t : ℝ) (u : EuclideanSpace ℝ (Fin (a+1))) =>
      (∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u i)+θ.val ((a+1 : ℝ)^(-ε)*(u i)⁻¹)))+
        (1-t)*Ky u+t*Kz u
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) 1,
    ∀ frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a),
    let U := frame '' Ω
    let V := fun x => p.val.1*H t (AffineSimplex.centredChart a L (frame.symm x))
    ∃ μ : Measure (EuclideanSpace ℝ (Fin a)),
    ∃ hV : IsEuclideanGibbsPotential volume μ U V,
    let hU := frame.toHomeomorph.isOpenMap Ω (ConditionalWellPosedness.fibre_isOpen a L)
    let hB := frame.isometry.lipschitzWith.isBounded_image
      (ConditionalWellPosedness.fibre_isBounded a L)
    ConditionalWellPosedness.EuclideanWellPosed hU hB hV ∧
      (∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹^2-B ≤
        ‖gradient V x‖^2/4-Laplacian.laplacian V x/2) := by
  intro Ω H
  obtain ⟨B,hB,hpath⟩ := physical_intrinsic_wellposed_internal p a d e ha θ ε L hL
    y z hyL hzL Ky Kz hKy hKz
  refine ⟨B,hB,?_⟩
  intro t ht frame U V
  obtain ⟨ρ,hρ,hH,hbar⟩ := hpath t ht
  have hκ : 0 < 2*p.val.1*(p.val.2*(p.val.2+1))*L^(-p.val.2-2) := by
    have hβ := p.property.1
    have hs := p.property.2.1
    positivity
  obtain ⟨hV,hwell⟩ := ConditionalWellPosedness.internal_orthonormal_wellposed a ha L hρ
    hκ hB hH hbar frame
  exact ⟨ρ.map frame,hV,hwell,
    NeumannIsometryTransport.barrier_map frame
      (ConditionalWellPosedness.fibre_isOpen a L) (hρ.1.of_le (by norm_num)) hbar⟩

variable
    (hKys : ContDiffOn ℝ ∞ Ky (RetainedSimplex.assemble (d+1) a
      (InterpolatingDensities.exteriorPermutation (d+1) a) y.val ⁻¹'
        gapAmbientDomain (d+1+a).succPNat))
    (hKzs : ContDiffOn ℝ ∞ Kz (RetainedSimplex.assemble (e+1) a
      (InterpolatingDensities.exteriorPermutation (e+1) a) z.val ⁻¹'
        gapAmbientDomain (e+1+a).succPNat))

include hyL hzL hKys hKzs in
/-- See Subsection 6.1 and the proof of Proposition 6.6 of the paper: the specified
physical interpolant, including its β factor, is smooth on a neighborhood
of every point of its physical mass fibre. -/
theorem physical_interpolant_smooth_internal (t : ℝ) :
    let H := fun u : EuclideanSpace ℝ (Fin (a+1)) => p.val.1*
      ((∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u i)+θ.val ((a+1 : ℝ)^(-ε)*(u i)⁻¹)))+
        (1-t)*Ky u+t*Kz u)
    ∀ u ∈ AffineSimplex.massSimplex a L, ContDiffAt ℝ ∞ H u := by
  intro H u hu
  have huy := InterpolationCoefficientBounds.fibre_mem_internal (d+1) a y L hyL hu
  have huz := InterpolationCoefficientBounds.fibre_mem_internal (e+1) a z L hzL hu
  have hopeny := (PhysicalEnergy.isOpen_gapAmbientDomain (d+1+a).succPNat).preimage
    (RetainedSimplex.continuous_assemble (d+1) a
      (InterpolatingDensities.exteriorPermutation (d+1) a) y.val)
  have hopenz := (PhysicalEnergy.isOpen_gapAmbientDomain (e+1+a).succPNat).preimage
    (RetainedSimplex.continuous_assemble (e+1) a
      (InterpolatingDensities.exteriorPermutation (e+1) a) z.val)
  exact (((InterpolationCoercivity.forcing_smooth θ
    (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < a+1) (-ε)) hu.1).add
      ((hKys.contDiffAt (hopeny.mem_nhds huy)).const_smul (1-t))).add
        ((hKzs.contDiffAt (hopenz.mem_nhds huz)).const_smul t)).const_smul p.val.1

include hyL hzL hKys hKzs in
/-- See the proof of Proposition 6.6 in the paper: compression of the literal
β-scaled physical Hessian is the Hessian of the same chart potential.
This is a pointwise identity on the whole open physical chart. -/
theorem physical_chart_hessian_internal (t : ℝ)
    (frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
    (A : Matrix (Fin (a+1)) (Fin a) ℝ)
    (hA : ∀ v : Fin a → ℝ, A *ᵥ v = (frame.symm (WithLp.toLp 2 v)).val) :
    let H := fun u : EuclideanSpace ℝ (Fin (a+1)) => p.val.1*
      ((∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u i)+θ.val ((a+1 : ℝ)^(-ε)*(u i)⁻¹)))+
        (1-t)*Ky u+t*Kz u)
    let g := fun x => AffineSimplex.centredChart a L (frame.symm x)
    ∀ x ∈ frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L),
      A.transpose*hessianMatrix H (g x)*A = hessianMatrix (H ∘ g) x := by
  intro H g x hx
  have hxs : g x ∈ AffineSimplex.massSimplex a L := by
    obtain ⟨w,hw,rfl⟩ := hx
    simpa only [g,frame.symm_apply_apply,mem_preimage] using hw
  exact frame_hessian_internal a L frame A hA H x
    (physical_interpolant_smooth_internal p a d e θ ε L y z hyL hzL Ky Kz hKys hKzs t _ hxs)

include hyL hzL hKys hKzs in
/-- See Subsection 6.1 and the proof of Proposition 6.6 of the paper:
the specified orthonormal Gibbs law pushes forward to the literal
normalized Hausdorff interpolant, with positive finite normalization. -/
theorem physical_normalized_chart_internal (t N : ℝ) (hLN : L < N)
    (frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a)) :
    let H := fun u : EuclideanSpace ℝ (Fin (a+1)) => p.val.1*
      ((∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u i)+θ.val ((a+1 : ℝ)^(-ε)*(u i)⁻¹)))+
        (1-t)*Ky u+t*Kz u)
    let U := frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
    let g := fun x => AffineSimplex.centredChart a L (frame.symm x)
    let w := fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal (Real.exp (-H u.val))
    ∀ (μ : Measure (EuclideanSpace ℝ (Fin a)))
      (_hV : IsEuclideanGibbsPotential volume μ U (H ∘ g)),
    ∃ (h0 : (∫⁻ u, w u ∂(AffineSimplex.simplexVolume a L).comap Subtype.val) ≠ 0)
      (htop : (∫⁻ u, w u ∂(AffineSimplex.simplexVolume a L).comap Subtype.val) ≠ ⊤),
      (μ.comap (Subtype.val : U → _)).map
          (InterpolationTransport.orthonormalInclusion a L N hLN frame) =
        (AffineFibre.normalizedMeasure ((AffineSimplex.simplexVolume a L).comap Subtype.val)
          w h0 htop).map (InterpolationTransport.inclusion a L N hLN) := by
  intro H U g w μ hV
  have hcont : Continuous (fun u : AffineSimplex.massSimplex a L => H u.val) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    exact (physical_interpolant_smooth_internal p a d e θ ε L y z hyL hzL Ky Kz
      hKys hKzs t u.val u.property).continuousAt.comp continuous_subtype_val.continuousAt
  exact InterpolationTransport.normalized_intrinsic_law_internal a L N hLN frame μ
    (H ∘ g) hV w (hcont.neg.measurable.exp.ennreal_ofReal) (fun _ _ _ => rfl)

include ha hL hyL hzL hKy hKz in
/-- See Lemma 6.1 and the proof of Proposition 6.6 of the paper:
the integrated identity and both value moments hold for the specified
ambient endpoints on the same intrinsic carrier, rather than for a newly
chosen pair of endpoint realizations. -/
theorem physical_integrated_block_identity_internal (hε : 0 < ε)
    (G : BlockObservable a.succPNat) :
    let Ω := AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L
    let μ : Measure Ω := volume.comap Subtype.val
    let H := fun (t : ℝ) (u : EuclideanSpace ℝ (Fin (a+1))) => p.val.1*
      ((∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u i)+θ.val ((a+1 : ℝ)^(-ε)*(u i)⁻¹)))+
        (1-t)*Ky u+t*Kz u)
    let ν := fun t => μ.tilted (fun w : Ω => -H t (AffineSimplex.centredChart a L w.val))
    let g := fun w : Ω => G.val (WithLp.ofLp (AffineSimplex.centredChart a L w.val))
    let D := fun w : Ω => Ky (AffineSimplex.centredChart a L w.val)-Kz (AffineSimplex.centredChart a L w.val)
    ∃ δ : ℝ, 0 < δ ∧
      ContDiffOn ℝ ∞ (fun t => ∫ w, g w ∂ν t) (Ioo (-δ) (1+δ)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        Integrable (fun w : Ω => Real.exp (-H t (AffineSimplex.centredChart a L w.val))) μ ∧
        (0 < ∫ w, Real.exp (-H t (AffineSimplex.centredChart a L w.val)) ∂μ) ∧
        (∃ h0 ht, ν t = AffineFibre.normalizedMeasure μ
          (fun w : Ω => ENNReal.ofReal (Real.exp (-H t (AffineSimplex.centredChart a L w.val)))) h0 ht) ∧
        IsProbabilityMeasure (ν t) ∧ MemLp g 2 (ν t) ∧ MemLp D 2 (ν t) ∧
        HasDerivAt (fun u => ∫ w, g w ∂ν u) (p.val.1*covariance g D (ν t)) t) ∧
      IntervalIntegrable (fun t => covariance g D (ν t)) volume 0 1 ∧
      (∫ w, g w ∂ν 1)-(∫ w, g w ∂ν 0) =
        p.val.1*∫ t in (0 : ℝ)..1, covariance g D (ν t) := by
  intro Ω μ H ν g D
  have hcy : L+∑ i, y.val i = ((a+1+d : ℕ)+1 : ℝ) := by
    have heq : ((d+1+a : ℕ)+1 : ℝ) = ((a+1+d : ℕ)+1 : ℝ) := by push_cast; ring
    linarith only [hyL,heq]
  have hcz : L+∑ i, z.val i = ((a+1+e : ℕ)+1 : ℝ) := by
    have heq : ((e+1+a : ℕ)+1 : ℝ) = ((a+1+e : ℕ)+1 : ℝ) := by push_cast; ring
    linarith only [hzL,heq]
  obtain ⟨Jy,Jz,hJy,hJz,hrest⟩ := integrated_block_identity p a d e ha
    (Equiv.refl _) (Equiv.refl _) hL y.val y.property.1 z.val z.property.1 hcy hcz θ ε hε G
  have hey := endpoint_realization_alignment_internal p a d L y hyL Ky hKy Jy
    (fun w hw => ⟨_,hJy w hw⟩)
  have hez := endpoint_realization_alignment_internal p a e L z hzL Kz hKz Jz
    (fun w hw => ⟨_,hJz w hw⟩)
  have heY (w : Ω) : Jy w.val = Ky (AffineSimplex.centredChart a L w.val) := (hey w.property).symm
  have heZ (w : Ω) : Jz w.val = Kz (AffineSimplex.centredChart a L w.val) := (hez w.property).symm
  dsimp only at hrest
  simpa only [heY,heZ,Nat.cast_add,Nat.cast_one] using hrest

include ha hL hyL hzL hKy hKz in
/-- See the proof of Proposition 6.6 in the paper: the actual orthonormal Gibbs
law is the image of the time law in the integrated identity, and both
literal observables have finite second moments on that very law. -/
theorem physical_chart_value_moments_internal (hε : 0 < ε)
    (G : BlockObservable a.succPNat) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a)) :
    let Ω := AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L
    let H := fun (t : ℝ) (u : EuclideanSpace ℝ (Fin (a+1))) => p.val.1*
      ((∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u i)+θ.val ((a+1 : ℝ)^(-ε)*(u i)⁻¹)))+
        (1-t)*Ky u+t*Kz u)
    let ν := (volume.comap (Subtype.val : Ω → AffineSimplex.Tangent a)).tilted
      (fun w : Ω => -H t (AffineSimplex.centredChart a L w.val))
    let U := frame '' Ω
    let g := fun x => AffineSimplex.centredChart a L (frame.symm x)
    ∀ (μ : Measure (EuclideanSpace ℝ (Fin a)))
      (_hV : IsEuclideanGibbsPotential volume μ U (fun x => H t (g x))),
      ν.map (fun w : Ω => frame w.val) = μ ∧
      MemLp (fun x => G.val (WithLp.ofLp (g x))) 2 μ ∧
      MemLp (fun x => Ky (g x)-Kz (g x)) 2 μ := by
  intro Ω H ν U g μ hV
  obtain ⟨_,_,_,hcal,_,_⟩ := physical_integrated_block_identity_internal p a d e ha θ ε L hL
    y z hyL hzL Ky Kz hKy hKz hε G
  have hdata := hcal t ht
  obtain ⟨h0,htop,hnorm⟩ := hdata.2.2.1
  obtain ⟨_,_,hpath⟩ := physical_intrinsic_wellposed_internal p a d e ha θ ε L hL
    y z hyL hzL Ky Kz hKy hKz
  obtain ⟨ρ,hρ,_,_⟩ := hpath t ht
  have hopen : IsOpen Ω := ConditionalWellPosedness.fibre_isOpen a L
  have hcont : Continuous (fun w : Ω => H t (AffineSimplex.centredChart a L w.val)) :=
    hρ.1.continuousOn.comp_continuous continuous_subtype_val (fun w => w.property)
  obtain ⟨_,_,hmap⟩ := GibbsPotentialLocalCongruence.normalized_subtype hρ hopen.measurableSet
    hcont.neg.measurable.exp.ennreal_ofReal
  have hνρ : ν.map (Subtype.val : Ω → AffineSimplex.Tangent a) = ρ := by
    rw [show ν = _ from hnorm]
    exact hmap
  have hρμ : ρ.map frame = μ := GibbsPotentialLocalCongruence.unique
    (IntrinsicScalarPoisson.gibbs_isometry frame hρ) hV
  have hlaw : ν.map (fun w : Ω => frame w.val) = μ := by
    change ν.map (frame ∘ (Subtype.val : Ω → AffineSimplex.Tangent a)) = μ
    rw [← Measure.map_map frame.continuous.measurable measurable_subtype_coe,hνρ,hρμ]
  have hf : MeasurableEmbedding (fun w : Ω => frame w.val) :=
    frame.toHomeomorph.measurableEmbedding.comp (MeasurableEmbedding.subtype_coe hopen.measurableSet)
  refine ⟨hlaw,?_,?_⟩
  · rw [← hlaw]
    apply hf.memLp_map_measure_iff.mpr
    simpa only [Function.comp_def,g,frame.symm_apply_apply] using hdata.2.2.2.2.1
  · rw [← hlaw]
    apply hf.memLp_map_measure_iff.mpr
    simpa only [Function.comp_def,g,frame.symm_apply_apply] using hdata.2.2.2.2.2.1

include ha hL hyL hzL hKy hKz in
/-- See the proof of Proposition 6.6 in the paper: the same time-uniform analytic
data apply to any given Gibbs realization of the physical chart potential.
This allows the law in the original scalar-form certificate to be used. -/
theorem physical_chart_wellposed_of_gibbs_internal :
    let Ω := AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L
    let H := fun (t : ℝ) (u : EuclideanSpace ℝ (Fin (a+1))) => p.val.1*
      ((∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u i)+θ.val ((a+1 : ℝ)^(-ε)*(u i)⁻¹)))+
        (1-t)*Ky u+t*Kz u)
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) 1,
    ∀ frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a),
    let U := frame '' Ω
    let V := fun x => H t (AffineSimplex.centredChart a L (frame.symm x))
    ∀ (μ : Measure (EuclideanSpace ℝ (Fin a)))
      (hV : IsEuclideanGibbsPotential volume μ U V),
    let hU := frame.toHomeomorph.isOpenMap Ω (ConditionalWellPosedness.fibre_isOpen a L)
    let hB := frame.isometry.lipschitzWith.isBounded_image
      (ConditionalWellPosedness.fibre_isBounded a L)
    ConditionalWellPosedness.EuclideanWellPosed hU hB hV ∧
      (∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹^2-B ≤
        ‖gradient V x‖^2/4-Laplacian.laplacian V x/2) := by
  intro Ω H
  obtain ⟨B,hB,hpath⟩ := physical_chart_wellposed_internal p a d e ha θ ε L hL
    y z hyL hzL Ky Kz hKy hKz
  refine ⟨B,hB,?_⟩
  intro t ht frame U V μ hV
  obtain ⟨μ₀,hV₀,hwell,hbar⟩ := hpath t ht frame
  have he : μ₀ = μ := GibbsPotentialLocalCongruence.unique hV₀ hV
  subst μ₀
  exact ⟨hwell,hbar⟩

include hyL hzL hKys hKzs in
/-- See Lemma 6.4 and the proof of Proposition 6.6 of the paper: the literal
interaction difference is smooth near every point of the mass fibre. -/
theorem physical_interaction_smooth_internal :
    ∀ u ∈ AffineSimplex.massSimplex a L,
      ContDiffAt ℝ ∞ (fun x => Ky x-Kz x) u := by
  intro u hu
  have huy := InterpolationCoefficientBounds.fibre_mem_internal (d+1) a y L hyL hu
  have huz := InterpolationCoefficientBounds.fibre_mem_internal (e+1) a z L hzL hu
  have hopeny := (PhysicalEnergy.isOpen_gapAmbientDomain (d+1+a).succPNat).preimage
    (RetainedSimplex.continuous_assemble (d+1) a
      (InterpolatingDensities.exteriorPermutation (d+1) a) y.val)
  have hopenz := (PhysicalEnergy.isOpen_gapAmbientDomain (e+1+a).succPNat).preimage
    (RetainedSimplex.continuous_assemble (e+1) a
      (InterpolatingDensities.exteriorPermutation (e+1) a) z.val)
  exact (hKys.contDiffAt (hopeny.mem_nhds huy)).sub (hKzs.contDiffAt (hopenz.mem_nhds huz))

include ha hL hyL hzL hKy hKz hKys hKzs in
/-- See Lemma 6.4 and the proof of Proposition 6.6 of the paper: the physical
interaction has its exact Sobolev jet on the specified Gibbs law. Smoothness,
the value moment and the collision barrier are proved from physical data. Only the good/bad coefficient-envelope estimates remain inputs of this
internal analytic assembly. -/
theorem physical_interaction_jet_internal (hε : 0 < ε)
    (G : BlockObservable a.succPNat) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
    (A : Matrix (Fin (a+1)) (Fin a) ℝ)
    (hA : ∀ v : Fin a → ℝ, A *ᵥ v = (frame.symm (WithLp.toLp 2 v)).val) :
    let Ω := AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L
    let U := frame '' Ω
    let g := fun x => AffineSimplex.centredChart a L (frame.symm x)
    let V := fun x => p.val.1*
      ((∑ i, (θ.val ((a+1 : ℝ)^(-ε)*g x i)+θ.val ((a+1 : ℝ)^(-ε)*(g x i)⁻¹)))+
        (1-t)*Ky (g x)+t*Kz (g x))
    let D := fun u => Ky u-Kz u
    let b := fun j x => InteractionDifferential.pinnedRepresentative (fun i : Fin a =>
      fderiv ℝ D (g x) (WithLp.toLp 2 (Pi.single i.castSucc 1-Pi.single i.succ 1))) j
    ∀ (μ : Measure (EuclideanSpace ℝ (Fin a)))
      (hV : IsEuclideanGibbsPotential volume μ U V),
    let hU := frame.toHomeomorph.isOpenMap Ω (ConditionalWellPosedness.fibre_isOpen a L)
    let hB := frame.isometry.lipschitzWith.isBounded_image
      (ConditionalWellPosedness.fibre_isBounded a L)
    ∀ (good : Set (EuclideanSpace ℝ (Fin a))) (W : EuclideanSpace ℝ (Fin a) → ℝ) (B K : ℝ),
      (∀ j, ∀ᵐ x ∂μ.restrict good, |b j x| ≤ B) →
      IntegrableOn W goodᶜ μ →
      (∀ j, ∀ᵐ x ∂μ.restrict goodᶜ, b j x^2 ≤ K*W x) →
    ∃ F : ScalarForm.Domain (IntrinsicScalarCore.jet hU hB hV),
      ScalarForm.value _ F =ᵐ[μ] D ∘ g ∧
      ∃ b₂ : Fin (a+1) → Lp ℝ 2 μ,
        (∀ j, b₂ j =ᵐ[μ] b j) ∧
        RectangularFormTransport.tupleMap A.transpose b₂ =
          fun k => DifferentiatedPoisson.coordinateLp k (ScalarForm.deriv _ F) := by
  intro Ω U g V D b μ hV hU hB good W B K hgood hW hsq
  obtain ⟨B₀,hB₀,hpath⟩ := physical_chart_wellposed_of_gibbs_internal p a d e ha θ ε L hL
    y z hyL hzL Ky Kz hKy hKz
  have hbar := (hpath t ht frame μ hV).2
  have hmoment := (physical_chart_value_moments_internal p a d e ha θ ε L hL
    y z hyL hzL Ky Kz hKy hKz hε G t ht frame μ hV).2.2
  have hsupport := IntrinsicScalarCore.supported hU hV
  have hgs (x) (hx : x ∈ U) : g x ∈ AffineSimplex.massSimplex a L := by
    obtain ⟨w,hw,rfl⟩ := hx
    simpa only [g,Ω,frame.symm_apply_apply,mem_preimage] using hw
  have hds (u) (hu : u ∈ AffineSimplex.massSimplex a L) : ContDiffAt ℝ ∞ D u :=
    physical_interaction_smooth_internal a d e L y z hyL hzL Ky Kz hKys hKzs u hu
  have hg : ContDiff ℝ ∞ g := by
    dsimp only [g,AffineSimplex.centredChart]
    exact (((AffineSimplex.Tangent a).subtypeL.contDiff).comp
      frame.symm.toContinuousLinearEquiv.contDiff).add contDiff_const
  exact interaction_jet_from_envelope_internal a ha L frame A hA μ V hV D
    (hsupport.mono fun x hx => (hds _ (hgs x hx)).differentiableAt (by simp))
    (fun x hx => ((hds _ (hgs x hx)).comp x hg.contDiffAt).contDiffWithinAt)
    hmoment good W B K B₀ hB₀ hbar hgood hW hsq

end Physical

/-- See the proof of Proposition 6.6 in the paper: transport a scalar class to
the physical image and identify its literal representative. Every extended
essential norm, including the supremum norm, is preserved. -/
theorem consecutive_literal_class_internal {X Y Z : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (f : X → Y) (hf : MeasurableEmbedding f)
    (j : X → Z) (hj : MeasurableEmbedding j) (u : Lp ℝ 2 (μ.map f))
    (v : Z → ℝ) (hu : (u : Y → ℝ) ∘ f =ᵐ[μ] v ∘ j) :
    let Tf := ScalarFormEmbedding.pullback μ f hf
    let Tj := ScalarFormEmbedding.pullback μ j hj
    (Tj.symm (Tf u) : Z → ℝ) =ᵐ[μ.map j] v ∧
      (∀ p : ℝ≥0∞, eLpNorm (Tj.symm (Tf u)) p (μ.map j) = eLpNorm u p (μ.map f)) ∧
      Tf.symm (Tj (Tj.symm (Tf u))) = u := by
  intro Tf Tj
  refine ⟨hj.ae_map_iff.mpr ?_,?_,by simp only [LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.symm_apply_apply]⟩
  · filter_upwards [ScalarFormEmbedding.pullback_ae μ f hf u,
      ScalarFormEmbedding.inverse_ae μ j hj (Tf u),hu] with x hx hy hz
    exact hy.trans (hx.trans hz)
  · intro p
    exact (ScalarFormEmbedding.inverse_eLpNorm μ j hj (Tf u) p).trans
      (ScalarFormEmbedding.pullback_eLpNorm μ f hf u p)

/-- See the proof of Proposition 6.6 in the paper: the covariance point-source
formula on the original intrinsic scalar-form certificate. The dependent
law equality and equality of the complete transported form are substituted
here, rather than replacing the certificate by a new form. Analytic chart
and coefficient data remain explicit in this internal transport theorem. -/
theorem certificate_point_source_covariance_internal (a : ℕ) (L N : ℝ) (hLN : L < N)
    (frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
    (ν : Measure (AffineSimplex.chartDomain (a+1) N)) (Q : ScalarFormData ν)
    (hQ : InterpolationCoefficientBounds.IsIntrinsicFibreForm a L N hLN frame ν Q)
    (μ : Measure (EuclideanSpace ℝ (Fin a))) (V : EuclideanSpace ℝ (Fin a) → ℝ)
    (hV : IsEuclideanGibbsPotential volume μ
      (frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)) V)
    (hlaw : (μ.comap Subtype.val).map
      (InterpolationTransport.orthonormalInclusion a L N hLN frame) = ν) :
    let U := frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
    let hU := frame.toHomeomorph.isOpenMap _ (ConditionalWellPosedness.fibre_isOpen a L)
    let hB := frame.isometry.lipschitzWith.isBounded_image
      (ConditionalWellPosedness.fibre_isBounded a L)
    let ξ : Measure U := μ.comap Subtype.val
    let j := InterpolationTransport.orthonormalInclusion a L N hLN frame
    let hj := InterpolationTransport.measurableEmbedding_orthonormalInclusion a L N hLN frame
    let hv := MeasurableEmbedding.subtype_coe hU.measurableSet
    let Tf := ScalarFormEmbedding.pullback ξ Subtype.val hv
    let Tj : Lp ℝ 2 ν ≃ₗᵢ[ℝ] Lp ℝ 2 ξ := hlaw ▸ ScalarFormEmbedding.pullback ξ j hj
    ∃ hV' : IsEuclideanGibbsPotential volume (ξ.map Subtype.val) U V,
    ConditionalWellPosedness.EuclideanWellPosed hU hB hV' →
    ∀ (A : Matrix (Fin (a+1)) (Fin a) ℝ), A.transpose*A = 1 →
      A.mulVecLin.range = zeroSumComponents (Fin (a+1)) →
    ∀ (M : AffineSimplex.chartDomain (a+1) N → Matrix (Fin (a+1)) (Fin (a+1)) ℝ)
      (M₀ : EuclideanSpace ℝ (Fin a) → Matrix (Fin (a+1)) (Fin (a+1)) ℝ),
      M ∘ j =ᵐ[ξ] M₀ ∘ Subtype.val →
      (fun x => A.transpose*M₀ x*A) =ᵐ[ξ.map Subtype.val] hessianMatrix V →
      (∀ᵐ x ∂ν, (M x).PosSemidef) →
      (∀ i k, Measurable (fun x => M x i k)) →
    ∀ c : ℝ, 0 < c →
      (∀ᵐ x ∂ν, ∀ v ∈ zeroSumComponents (Fin (a+1)),
        c*(∑ i, v i^2) ≤ ∑ i, ∑ k, v i*M x i k*v k) →
    ∀ (F K : ScalarForm.Domain (IntrinsicScalarCore.jet hU hB hV'))
      (g k : Lp ℝ 2 ν),
      Tf.symm (Tj g) = ScalarForm.value _ F →
      Tf.symm (Tj k) = ScalarForm.value _ K →
    ∀ (J : Finset (Fin (a+1))) (χ b : Fin (a+1) → Lp ℝ 2 ν),
      RectangularFormTransport.tupleMap A.transpose
        (fun i => Tf.symm (Tj (if i ∈ J then χ i else 0))) =
          (fun i => DifferentiatedPoisson.coordinateLp i (ScalarForm.deriv _ F)) →
      RectangularFormTransport.tupleMap A.transpose (fun i => Tf.symm (Tj (b i))) =
          (fun i => DifferentiatedPoisson.coordinateLp i (ScalarForm.deriv _ K)) →
    ∀ ψ : Fin (a+1) → Fin (a+1) → Q.1,
      (∀ i ∈ J, WeightedWeakSolution Q M (zeroSumComponents (Fin (a+1)))
        (fun l => if l = i then χ i else 0) (ψ i)) →
      covariance g k ν = ∑ i ∈ J, ∫ x, ∑ l, b l x*(ψ i l).val x ∂ν := by
  intro U hU hB ξ j hj hv Tf Tj
  obtain ⟨hV',_,hform⟩ := intrinsic_certificate_for_potential_internal a L N hLN frame ν Q hQ μ V hV hlaw
  refine ⟨hV',?_⟩
  cases hlaw
  have he : Q = ScalarFormEmbedding.form ξ j hj
      (ScalarFormEmbedding.restriction ξ Subtype.val hv (IntrinsicScalarCore.form hU hB hV')) :=
    eq_of_heq hform
  subst Q
  exact consecutive_covariance_point_sources_internal a.succPNat ξ Subtype.val hv j hj
    hU hB hV'

end Riesz2.CompatibleComparison
