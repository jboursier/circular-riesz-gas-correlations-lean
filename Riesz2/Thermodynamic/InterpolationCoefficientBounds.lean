/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.InterpolationBoundaryBridge
public import Riesz2.Thermodynamic.InterpolationTransport
public import Riesz2.ToMathlib.PeriodizedMatrixBoundsMonotone

/-!
# Physical interpolation coefficient bounds

Complete bounds for Subsection 6.1. The ambient realization identities below retain the
normal derivatives, and the scalar law is the original normalized Hausdorff law.
-/

public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ContDiff Topology ENNReal

attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.InterpolationCoefficientBounds

/-- See Subsection 6.1 of the paper: every point of a
compatible mass fibre lies in the full open assembly domain. -/
theorem fibre_mem_internal (e a : ℕ)
    (y : AffineSimplex.chartDomain e ((e+a : ℕ)+1)) (L : ℝ)
    (hyL : ((e+a : ℕ)+1 : ℝ)-∑ k, y.val k = L)
    {u : EuclideanSpace ℝ (Fin (a+1))} (hu : u ∈ AffineSimplex.massSimplex a L) :
    RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val u ∈
      gapAmbientDomain (e+a).succPNat := by
  apply ProperMarginalChart.simplex_ambient
  apply InterpolatingDensities.assemble_exterior_mem e a y u
  rwa [hyL]

/-- See Subsection 6.1 of the paper: two realizations of the same endpoint
energy have identical ambient Hessians on their whole open domain. -/
theorem realization_hessian_internal (p : Parameters) (e a : ℕ)
    (y : AffineSimplex.chartDomain e ((e+a : ℕ)+1))
    (V W : EuclideanSpace ℝ (Fin (a+1)) → ℝ)
    (hV : ∀ u (hu : RetainedSimplex.assemble e a
      (InterpolatingDensities.exteriorPermutation e a) y.val u ∈ gapAmbientDomain (e+a).succPNat),
      V u = physicalAmbientGapEnergy p (e+a).succPNat
        ⟨RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val u, hu⟩)
    (hW : ∀ u (hu : RetainedSimplex.assemble e a
      (InterpolatingDensities.exteriorPermutation e a) y.val u ∈ gapAmbientDomain (e+a).succPNat),
      W u = physicalAmbientGapEnergy p (e+a).succPNat
        ⟨RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val u, hu⟩)
    {u : EuclideanSpace ℝ (Fin (a+1))}
    (hu : RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val u ∈
      gapAmbientDomain (e+a).succPNat) :
    hessianMatrix V u = hessianMatrix W u := by
  apply InterpolationExceptional.hessian_eqOn_internal
    (U := RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val ⁻¹' gapAmbientDomain (e+a).succPNat)
    ((PhysicalEnergy.isOpen_gapAmbientDomain _).preimage
      (RetainedSimplex.continuous_assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val))
    (fun x hx => (hV x hx).trans (hW x hx).symm) hu

/-- See Subsection 6.1 of the paper: all-size coercivity transfers to any ambient endpoint realizations. There is no coefficient premise. -/
theorem coercivity_internal (p : Parameters) (θ : PhysicalCutoff)
    (ε : ℝ) (hε : 0 ≤ ε) (e f a : ℕ) (ha : 1 ≤ a)
    (y : AffineSimplex.chartDomain e ((e+a : ℕ)+1))
    (z : AffineSimplex.chartDomain f ((f+a : ℕ)+1)) (L : ℝ)
    (hyL : ((e+a : ℕ)+1 : ℝ)-∑ k, y.val k = L)
    (hzL : ((f+a : ℕ)+1 : ℝ)-∑ k, z.val k = L)
    (Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ)
    (hKy : ∀ u (hu : RetainedSimplex.assemble e a
      (InterpolatingDensities.exteriorPermutation e a) y.val u ∈ gapAmbientDomain (e+a).succPNat),
      Ky u = physicalAmbientGapEnergy p (e+a).succPNat
        ⟨RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val u, hu⟩)
    (hKz : ∀ u (hu : RetainedSimplex.assemble f a
      (InterpolatingDensities.exteriorPermutation f a) z.val u ∈ gapAmbientDomain (f+a).succPNat),
      Kz u = physicalAmbientGapEnergy p (f+a).succPNat
        ⟨RetainedSimplex.assemble f a (InterpolatingDensities.exteriorPermutation f a) z.val u, hu⟩)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    let H := fun u : EuclideanSpace ℝ (Fin (a+1)) =>
      (∑ k, (θ.val ((a+1 : ℝ)^(-ε)*u k) + θ.val ((a+1 : ℝ)^(-ε)*(u k)⁻¹))) +
        (1-t)*Ky u+t*Kz u
    ∀ x ∈ AffineSimplex.massSimplex a L, ∀ v : EuclideanSpace ℝ (Fin (a+1)),
      min 1 (p.val.2*(p.val.2+1))*(a+1 : ℝ)^(-(p.val.2+2)*ε)*(∑ i, (v i)^2) ≤
        ∑ i, ∑ j, v i*hessianMatrix H x i j*v j := by
  intro H
  obtain ⟨hc, Vy, Vz, hVy, hVz, hvy, hvz, hb⟩ :=
    InterpolationCoercivity.physical_interpolant_coercivity p θ ε hε e f a ha y z L hyL hzL
  intro x hx v
  have hxy := fibre_mem_internal e a y L hyL hx
  have hxz := fibre_mem_internal f a z L hzL hx
  have hDy := (PhysicalEnergy.isOpen_gapAmbientDomain (e+a).succPNat).preimage
    (RetainedSimplex.continuous_assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val)
  have hDz := (PhysicalEnergy.isOpen_gapAmbientDomain (f+a).succPNat).preimage
    (RetainedSimplex.continuous_assemble f a (InterpolatingDensities.exteriorPermutation f a) z.val)
  let V := fun u : EuclideanSpace ℝ (Fin (a+1)) =>
    (∑ k, (θ.val ((a+1 : ℝ)^(-ε)*u k) + θ.val ((a+1 : ℝ)^(-ε)*(u k)⁻¹))) +
      (1-t)*Vy u+t*Vz u
  have hEq : EqOn H V ((RetainedSimplex.assemble e a
      (InterpolatingDensities.exteriorPermutation e a) y.val ⁻¹' gapAmbientDomain (e+a).succPNat) ∩
      (RetainedSimplex.assemble f a
      (InterpolatingDensities.exteriorPermutation f a) z.val ⁻¹' gapAmbientDomain (f+a).succPNat)) := by
    intro u hu
    dsimp only [H,V]
    rw [(hKy u hu.1).trans (hvy u hu.1).symm,
      (hKz u hu.2).trans (hvz u hu.2).symm]
  rw [InterpolationExceptional.hessian_eqOn_internal (hDy.inter hDz) hEq ⟨hxy,hxz⟩]
  exact (hb t ht x hx).2 v

/-- See Subsection 6.1 of the paper: the included physical law
is supported on both compatible mass fibres, for any fibre measure. -/
theorem common_fibre_support_internal (a d e : ℕ) (L : ℝ)
    (y : AffineSimplex.chartDomain (d+1) ((d+1+a : ℕ)+1))
    (z : AffineSimplex.chartDomain (e+1) ((e+1+a : ℕ)+1))
    (hyL : ((d+1+a : ℕ)+1 : ℝ)-∑ k, y.val k = L)
    (hzL : ((e+1+a : ℕ)+1 : ℝ)-∑ k, z.val k = L)
    (hLN : L < ((a.succPNat+d : ℕ)+1 : ℝ))
    (ρ : Measure (AffineSimplex.massSimplex a L)) :
    ∀ᵐ x ∂ρ.map (InterpolationTransport.inclusion a L _ hLN),
      x.val ∈ AffineSimplex.massSimplex a (((d+1+a : ℕ)+1 : ℝ)-∑ k, y.val k) ∧
      x.val ∈ AffineSimplex.massSimplex a (((e+1+a : ℕ)+1 : ℝ)-∑ k, z.val k) := by
  rw [(InterpolationTransport.measurableEmbedding_inclusion a L _ hLN).ae_map_iff]
  exact ae_of_all _ (fun u => ⟨hyL ▸ u.property, hzL ▸ u.property⟩)


/-- See Subsection 6.1 of the paper: the form is exactly the
embedding transport of a Neumann realization on the orthonormal fibre.
The equality of laws fixes the physical probability, and `HEq` identifies
the whole form domain and energy, including the measured carrier. -/
@[expose] def IsIntrinsicFibreForm (a : ℕ) (L N : ℝ) (hLN : L < N)
    (frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
    (ν : Measure (AffineSimplex.chartDomain (a+1) N)) (Q : ScalarFormData ν) : Prop :=
  let U := frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
  let hU : IsOpen U := frame.toHomeomorph.isOpenMap _ (ConditionalWellPosedness.fibre_isOpen a L)
  let j := InterpolationTransport.orthonormalInclusion a L N hLN frame
  let hj := InterpolationTransport.measurableEmbedding_orthonormalInclusion a L N hLN frame
  let hv := MeasurableEmbedding.subtype_coe hU.measurableSet
  ∃ (ν₀ : Measure (EuclideanSpace ℝ (Fin a))) (V : EuclideanSpace ℝ (Fin a) → ℝ),
    IsEuclideanGibbsPotential volume ν₀ U V ∧
    let ξ : Measure U := ν₀.comap Subtype.val
    ∃ Q₀ : ScalarFormData (ξ.map Subtype.val),
      IsNeumannRealization U Q₀ ∧ IsClosedScalarDirichletForm Q₀ ∧ IsConservativeScalarForm Q₀ ∧
      ξ.map j = ν ∧
      HEq Q (ScalarFormEmbedding.form ξ j hj (ScalarFormEmbedding.restriction ξ Subtype.val hv Q₀))

/-- See Subsection 6.1 of the paper: ambient realizations
give the original finite normalized Hausdorff law and its intrinsic closed
conservative scalar form, in every orthonormal scalar chart. -/
theorem physical_form_internal (p : Parameters) (θ : PhysicalCutoff)
    (ε : ℝ) (e f a : ℕ) (he : 1 ≤ e) (hf : 1 ≤ f)
    (y : AffineSimplex.chartDomain e ((e+a : ℕ)+1))
    (z : AffineSimplex.chartDomain f ((f+a : ℕ)+1)) (L : ℝ)
    (hyL : ((e+a : ℕ)+1 : ℝ)-∑ k, y.val k = L)
    (hzL : ((f+a : ℕ)+1 : ℝ)-∑ k, z.val k = L)
    (Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ)
    (hKy : ∀ u (hu : RetainedSimplex.assemble e a
      (InterpolatingDensities.exteriorPermutation e a) y.val u ∈ gapAmbientDomain (e+a).succPNat),
      Ky u = physicalAmbientGapEnergy p (e+a).succPNat
        ⟨RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val u, hu⟩)
    (hKz : ∀ u (hu : RetainedSimplex.assemble f a
      (InterpolatingDensities.exteriorPermutation f a) z.val u ∈ gapAmbientDomain (f+a).succPNat),
      Kz u = physicalAmbientGapEnergy p (f+a).succPNat
        ⟨RetainedSimplex.assemble f a (InterpolatingDensities.exteriorPermutation f a) z.val u, hu⟩)

    (N : ℝ) (hN : ((e+a : ℕ)+1 : ℝ) = N) (hLN : L < N)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    let H := fun u : EuclideanSpace ℝ (Fin (a+1)) =>
      (∑ k, (θ.val ((a+1 : ℝ)^(-ε)*u k) + θ.val ((a+1 : ℝ)^(-ε)*(u k)⁻¹))) +
        (1-t)*Ky u+t*Kz u
    let μ : Measure (AffineSimplex.massSimplex a L) :=
      (AffineSimplex.simplexVolume a L).comap Subtype.val
    let w := fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal (Real.exp (-p.val.1*H u.val))
    ∃ (h0 : (∫⁻ u, w u ∂μ) ≠ 0) (htop : (∫⁻ u, w u ∂μ) ≠ ⊤),
      let ν := (AffineFibre.normalizedMeasure μ w h0 htop).map
        (InterpolationTransport.inclusion a L N hLN)
      IsProbabilityMeasure ν ∧
      ∀ frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a),
        ∃ Q : ScalarFormData ν, IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
          IsIntrinsicFibreForm a L N hLN frame ν Q := by
  subst N
  intro H μ w
  obtain ⟨Ay, Az, hAy, hAz, hay, haz, hnorm⟩ :=
    InterpolationTransport.physical_scalar_transport p a e f he hf θ ε L y z
      (by linarith) (by linarith)
  obtain ⟨h0, htop, hforms⟩ := hnorm t ht
  simp only [Nat.cast_add, Nat.cast_one] at h0 htop
  have hw : w = (fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal
      (Real.exp (-p.val.1*((∑ k, (θ.val ((a+1 : ℝ)^(-ε)*u.val k) +
        θ.val ((a+1 : ℝ)^(-ε)*(u.val k)⁻¹))) + (1-t)*Ay u.val+t*Az u.val)))) := by
    funext u
    have huy := fibre_mem_internal e a y L hyL u.property
    have huz := fibre_mem_internal f a z L hzL u.property
    dsimp only [w,H]
    rw [(hKy u.val huy).trans (hay u.val huy).symm,
      (hKz u.val huz).trans (haz u.val huz).symm]
  have hw' : w = (fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal
      (Real.exp (-p.val.1*((∑ k, (θ.val ((a+1 : ℝ)^(-ε)*u.val k) +
        θ.val ((a+1 : ℝ)^(-ε)*(u.val k)⁻¹))) +
      (1-t)*physicalAmbientGapEnergy p (e+a).succPNat
        ⟨RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val u.val,
          fibre_mem_internal e a y L hyL u.property⟩ +
      t*physicalAmbientGapEnergy p (f+a).succPNat
        ⟨RetainedSimplex.assemble f a (InterpolatingDensities.exteriorPermutation f a) z.val u.val,
          fibre_mem_internal f a z L hzL u.property⟩)))) := by
    funext u
    dsimp only [w,H]
    rw [hKy u.val (fibre_mem_internal e a y L hyL u.property),
      hKz u.val (fibre_mem_internal f a z L hzL u.property)]
  rw [hw']
  refine ⟨h0, htop, ?_, ?_⟩
  · refine @InterpolationTransport.probability a L _ _ _ ?_
    apply AffineFibre.isProbabilityMeasure_normalizedMeasure
    rw [← hw',hw]
    have hy : Continuous (fun u : AffineSimplex.massSimplex a L => Ay u.val) :=
      hAy.continuousOn.comp_continuous continuous_subtype_val
        (fun u => fibre_mem_internal e a y L hyL u.property)
    have hz : Continuous (fun u : AffineSimplex.massSimplex a L => Az u.val) :=
      hAz.continuousOn.comp_continuous continuous_subtype_val
        (fun u => fibre_mem_internal f a z L hzL u.property)
    have hpen : Continuous (fun u : AffineSimplex.massSimplex a L =>
        ∑ k, (θ.val ((a+1 : ℝ)^(-ε)*u.val k) + θ.val ((a+1 : ℝ)^(-ε)*(u.val k)⁻¹))) := by
      apply continuous_iff_continuousAt.mpr
      intro u
      exact ((InterpolationCoercivity.forcing_smooth θ
        (Real.rpow_pos_of_pos (by positivity) _) u.property.1).continuousAt).comp
          continuous_subtype_val.continuousAt
    exact (((hpen.add (hy.const_mul (1-t))).add (hz.const_mul t)).const_mul (-p.val.1)).measurable.exp.ennreal_ofReal
  · intro frame
    have hh := hforms frame
    dsimp only [Nat.succPNat_coe] at hh
    obtain ⟨ν₀, hG, hlaw, _⟩ := hh
    let U := frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
    let ξ : Measure U := ν₀.comap Subtype.val
    let j := InterpolationTransport.orthonormalInclusion a L ((e+a : ℕ)+1) hLN frame
    let hj := InterpolationTransport.measurableEmbedding_orthonormalInclusion a L ((e+a : ℕ)+1) hLN frame
    let hU : IsOpen U := frame.toHomeomorph.isOpenMap _ (ConditionalWellPosedness.fibre_isOpen a L)
    let hv := MeasurableEmbedding.subtype_coe hU.measurableSet
    obtain ⟨Q₀,hreal,hQ₀,hc₀,hQξ,hcξ,hQt,hct⟩ :=
      InterpolationTransport.intrinsic_scalar_explicit_internal a L _ hLN frame ν₀ _ hG
    let Qt := ScalarFormEmbedding.form ξ j hj (ScalarFormEmbedding.restriction ξ Subtype.val hv Q₀)
    have hcert : IsIntrinsicFibreForm a L _ hLN frame (ξ.map j) Qt :=
      ⟨ν₀,_,hG,Q₀,hreal,hQ₀,hc₀,rfl,HEq.rfl⟩
    have hres : ∃ Q : ScalarFormData (ξ.map j), IsClosedScalarDirichletForm Q ∧
        IsConservativeScalarForm Q ∧ IsIntrinsicFibreForm a L _ hLN frame (ξ.map j) Q :=
      ⟨Qt,hQt,hct,hcert⟩
    rw [hlaw] at hres
    let w₀ : AffineSimplex.massSimplex a L → ℝ≥0∞ := (fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal
      (Real.exp (-p.val.1*((∑ k, (θ.val (((a+1 : ℕ) : ℝ)^(-ε)*u.val k) +
        θ.val (((a+1 : ℕ) : ℝ)^(-ε)*(u.val k)⁻¹))) +
      (1-t)*physicalAmbientGapEnergy p (e+a).succPNat
        ⟨RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val u.val,
          fibre_mem_internal e a y L hyL u.property⟩ +
      t*physicalAmbientGapEnergy p (f+a).succPNat
        ⟨RetainedSimplex.assemble f a (InterpolatingDensities.exteriorPermutation f a) z.val u.val,
          fibre_mem_internal f a z L hzL u.property⟩))))
    have hweq : w₀ = (fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal
      (Real.exp (-p.val.1*((∑ k, (θ.val ((a+1 : ℝ)^(-ε)*u.val k) +
        θ.val ((a+1 : ℝ)^(-ε)*(u.val k)⁻¹))) +
      (1-t)*physicalAmbientGapEnergy p (e+a).succPNat
        ⟨RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val u.val,
          fibre_mem_internal e a y L hyL u.property⟩ +
      t*physicalAmbientGapEnergy p (f+a).succPNat
        ⟨RetainedSimplex.assemble f a (InterpolatingDensities.exteriorPermutation f a) z.val u.val,
          fibre_mem_internal f a z L hzL u.property⟩)))) := by
      funext u
      simp only [w₀, Nat.cast_add, Nat.cast_one]
    change ∃ Q : ScalarFormData ((AffineFibre.normalizedMeasure μ w₀ _ _).map
      (InterpolationTransport.inclusion a L ((e+a : ℕ)+1)
        (InterpolationTransport.compatible_mass_lt a e he L y (by linarith)))),
      IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
        IsIntrinsicFibreForm a L _ hLN frame _ Q at hres
    have h00 : (∫⁻ u, w₀ u ∂μ) ≠ 0 := by
      simpa only [w₀,μ,Nat.cast_add,Nat.cast_one] using h0
    have h0t : (∫⁻ u, w₀ u ∂μ) ≠ ⊤ := by
      simpa only [w₀,μ,Nat.cast_add,Nat.cast_one] using htop
    have hm : AffineFibre.normalizedMeasure μ w₀ h00 h0t =
        AffineFibre.normalizedMeasure μ _ h0 htop := by
      simp only [AffineFibre.normalizedMeasure_eq_smul,hweq]
    have hmap := congrArg (fun ρ => ρ.map (InterpolationTransport.inclusion a L ((e+a : ℕ)+1)
      (InterpolationTransport.compatible_mass_lt a e he L y (by linarith)))) hm
    rw [hmap] at hres
    exact hres


/-- See Subsection 6.1 of the paper: the whole-simplex interaction bound
holds for any ambient realizations of the original physical endpoints. -/
theorem interaction_square_internal (s ε : ℝ) (hs : 0 < s)
    (hε : 0 ≤ ε) (hσε : min s 1 / 2 + 2 * ε < 1) :
    ∃ (n₀ : ℕ) (C : ℝ), 2 ≤ n₀ ∧ 0 < C ∧
      ∀ p : Parameters, p.val.2 = s → ∀ (e f a : ℕ), n₀ ≤ a + 1 →
      4 * (a + 1) ≤ e + a + 1 → 4 * (a + 1) ≤ f + a + 1 →
      ∀ (y : AffineSimplex.chartDomain e ((e + a : ℕ) + 1))
        (z : AffineSimplex.chartDomain f ((f + a : ℕ) + 1)),
      InterpolantLocalLaws.exteriorGeometry s ε e a y.val →
      InterpolantLocalLaws.exteriorGeometry s ε f a z.val →
      ∀ L : ℝ,
      ((e + a : ℕ) + 1 : ℝ) - ∑ k, y.val k = L →
      ((f + a : ℕ) + 1 : ℝ) - ∑ k, z.val k = L →
      let Y := RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val
      let Z := RetainedSimplex.assemble f a (InterpolatingDensities.exteriorPermutation f a) z.val
      let Dy := Y ⁻¹' gapAmbientDomain (e + a).succPNat
      let Dz := Z ⁻¹' gapAmbientDomain (f + a).succPNat
      ∀ Ky Kz : EuclideanSpace ℝ (Fin (a + 1)) → ℝ,
        (∀ u (hu : u ∈ Dy), Ky u = physicalAmbientGapEnergy p (e + a).succPNat ⟨Y u, hu⟩) →
        (∀ u (hu : u ∈ Dz), Kz u = physicalAmbientGapEnergy p (f + a).succPNat ⟨Z u, hu⟩) →
        ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ AffineSimplex.massSimplex a L,
        ∀ i j : Fin (a + 1),
          |(1 - t) * hessianMatrix Ky u i j + t * hessianMatrix Kz u i j| ^ 2 ≤
            C * (a + 1 : ℝ) ^ C *
              InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s (WithLp.ofLp u) := by
  obtain ⟨n₀,C,hn₀,hC,hbound⟩ :=
    InterpolationExceptional.physical_interaction_sq_internal s ε hs hε hσε
  refine ⟨n₀,C,hn₀,hC,?_⟩
  intro p hps e f a hn hNy hNz y z hgy hgz L hyL hzL Y Z Dy Dz Ky Kz hKy hKz t ht u hu i j
  obtain ⟨Vy,Vz,_,_,hVy,hVz,hb⟩ :=
    hbound p hps e f a hn hNy hNz y z hgy hgz L hyL hzL
  rw [realization_hessian_internal p e a y Ky Vy hKy hVy
    (fibre_mem_internal e a y L hyL hu),
    realization_hessian_internal p f a z Kz Vz hKz hVz
    (fibre_mem_internal f a z L hzL hu)]
  exact hb t ht u hu i j


/-- The display equation (6.14) of the paper: the sum of the physical
interaction and forcing Hessian squares on every compatible positive mass
fibre, in both exponent regimes. The size threshold precedes the cutoff. -/
theorem whole_simplex_bound (s ε : ℝ) (hs : 0 < s)
    (hε : 0 ≤ ε) (hσε : min s 1 / 2 + 2 * ε < 1) :
    ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ θ : PhysicalCutoff, ∃ C : ℝ, 0 < C ∧
      ∀ p : Parameters, p.val.2 = s → ∀ (e f a : ℕ), n₀ ≤ a + 1 →
      4 * (a + 1) ≤ e + a + 1 → 4 * (a + 1) ≤ f + a + 1 →
      ∀ (y : AffineSimplex.chartDomain e ((e + a : ℕ) + 1))
        (z : AffineSimplex.chartDomain f ((f + a : ℕ) + 1)),
      InterpolantLocalLaws.exteriorGeometry s ε e a y.val →
      InterpolantLocalLaws.exteriorGeometry s ε f a z.val →
      ∀ L : ℝ,
      ((e + a : ℕ) + 1 : ℝ) - ∑ k, y.val k = L →
      ((f + a : ℕ) + 1 : ℝ) - ∑ k, z.val k = L →
      let Y := RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val
      let Z := RetainedSimplex.assemble f a (InterpolatingDensities.exteriorPermutation f a) z.val
      let Dy := Y ⁻¹' gapAmbientDomain (e + a).succPNat
      let Dz := Z ⁻¹' gapAmbientDomain (f + a).succPNat
      ∀ Ky Kz : EuclideanSpace ℝ (Fin (a + 1)) → ℝ,
        (∀ u (hu : u ∈ Dy), Ky u = physicalAmbientGapEnergy p (e + a).succPNat ⟨Y u, hu⟩) →
        (∀ u (hu : u ∈ Dz), Kz u = physicalAmbientGapEnergy p (f + a).succPNat ⟨Z u, hu⟩) →
        ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ AffineSimplex.massSimplex a L,
        ∀ i j : Fin (a + 1),
          |(1 - t) * hessianMatrix Ky u i j + t * hessianMatrix Kz u i j| ^ 2 +
            |hessianMatrix (fun v : EuclideanSpace ℝ (Fin (a + 1)) =>
              ∑ k, (θ.val ((a + 1 : ℝ) ^ (-ε) * v k) +
                θ.val ((a + 1 : ℝ) ^ (-ε) * (v k)⁻¹))) u i j| ^ 2 ≤
            C * (a + 1 : ℝ) ^ C *
              InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s (WithLp.ofLp u) := by
  obtain ⟨n₀, B, hn₀, hB, hb⟩ := interaction_square_internal s ε hs hε hσε
  refine ⟨n₀, hn₀, fun θ => ?_⟩
  obtain ⟨F, hF, hf⟩ := InterpolationCoercivity.forcing_sq_le_weight θ s hs
  let C := B + F + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hBC : B ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro p hps e f a hn hNy hNz y z hgy hgz L hyL hzL Y Z Dy Dz Ky Kz hKy hKz t ht u hu i j
  have hp := hb p hps e f a hn hNy hNz y z hgy hgz L hyL hzL Ky Kz hKy hKz t ht u hu i j
  have hforce := hf a ε hε u hu.1 i j
  have hn1 : (1 : ℝ) ≤ a + 1 := by have := Nat.cast_nonneg a (α := ℝ); linarith
  have hpow := Real.rpow_le_rpow_of_exponent_le hn1 hBC
  have hpow1 : 1 ≤ (a + 1 : ℝ) ^ C := Real.one_le_rpow hn1 hC.le
  have hW : 0 ≤ InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s (WithLp.ofLp u) :=
    zero_le_one.trans (InterpolantLocalLaws.one_le_exceptionalWeight s _ (fun i => (hu.1 i).le))
  let W := InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s (WithLp.ofLp u)
  calc
    _ ≤ B * (a + 1 : ℝ) ^ B * W + F * W := add_le_add hp hforce
    _ ≤ B * (a + 1 : ℝ) ^ C * W + (F * (a + 1 : ℝ) ^ C) * W := by
      apply add_le_add
      · gcongr
      · exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hF.le hpow1) hW
    _ = (B + F) * (a + 1 : ℝ) ^ C * W := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show B + F ≤ C by dsimp [C]; linarith)
        (by positivity)) hW


/-- See Subsection 6.1 of the paper: the full physical interval matrix is the
ambient endpoint Hessian in either exponent range. -/
theorem endpoint_hessian_internal (p : Parameters)
    (e a : ℕ) (y : AffineSimplex.chartDomain e ((e+a : ℕ)+1))
    (Ky : EuclideanSpace ℝ (Fin (a+1)) → ℝ)
    (hKy : ∀ u, ∀ hu : RetainedSimplex.assemble e a
        (InterpolatingDensities.exteriorPermutation e a) y.val u ∈ gapAmbientDomain (e+a).succPNat,
      Ky u = physicalAmbientGapEnergy p (e+a).succPNat
        ⟨RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val u, hu⟩)
    (u : EuclideanSpace ℝ (Fin (a+1)))
    (hu : u ∈ AffineSimplex.massSimplex a (((e+a : ℕ)+1 : ℝ)-∑ k, y.val k))
    (H : ∀ ir : Fin (e+a+1) × Fin ((e+a+1)/2),
      0 < cyclicGapSum (e+a).succPNat ir.1 (ir.2.val+1)
        (WithLp.ofLp (RetainedSimplex.assemble e a
          (InterpolatingDensities.exteriorPermutation e a) y.val u)) ∧
      cyclicGapSum (e+a).succPNat ir.1 (ir.2.val+1)
        (WithLp.ofLp (RetainedSimplex.assemble e a
          (InterpolatingDensities.exteriorPermutation e a) y.val u)) < ((e+a).succPNat : ℝ)) :
    hessianMatrix Ky u = IntervalBoundary.intervalMatrix (e+a).succPNat (a+1) (by change a+1 ≤ e+a+1; omega)
      (fun ir => (2 - if 2*(ir.2.val+1) = e+a+1 then (1 : ℝ) else 0) *
        PhysicalEnergy.intervalCoefficient p (e+a).succPNat
          ⟨cyclicGapSum (e+a).succPNat ir.1 (ir.2.val+1)
            (WithLp.ofLp (RetainedSimplex.assemble e a
              (InterpolatingDensities.exteriorPermutation e a) y.val u)), H ir⟩) := by
  let N := (e+a).succPNat
  let Y := RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val
  let D := Y ⁻¹' gapAmbientDomain N
  have hD : IsOpen D := (PhysicalEnergy.isOpen_gapAmbientDomain N).preimage
    (RetainedSimplex.continuous_assemble e a _ y.val)
  have hsimplex := InterpolatingDensities.assemble_exterior_mem e a y u hu
  have hs : WithLp.ofLp (Y u) ∈ Riesz1.gapSimplex N :=
    ⟨hsimplex.1, by simpa only [N, Nat.succPNat_coe, Nat.cast_succ] using hsimplex.2⟩
  have huD : u ∈ D := PhysicalEnergy.simplex_subset_ambient N _ hs
  obtain ⟨W, hW, hval, hmat⟩ :=
    CrossingCoefficients.ambient_hessian_intervalMatrix_internal p N
  have heq : EqOn Ky (fun v => W (Y v)) D := by
    intro v hv
    exact (hKy v hv).trans (hval ⟨Y v,hv⟩).symm
  rw [InterpolationExceptional.hessian_eqOn_internal hD heq huD]
  ext i j
  rw [InterpolationExceptional.hessian_assembly_internal e a y.val W u
    (hW.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds huD)) i j]
  exact hmat ⟨Y u,huD⟩ a.succPNat (by dsimp [N]; omega) i j

/-- See Subsection 6.1 of the paper: entry decay for the actual two endpoint
Hessians, with the structural exponent before epsilon and temperature. -/
theorem interaction_entry_internal (s K : ℝ) (hs : 0 < s) (hK : 0 ≤ K) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ ε : ℝ, 0 ≤ ε →
      min s 1 / 2 + 2 * ε < 1 → ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ (p : Parameters), p.val.2 = s → ∀ e d a : ℕ,
      e ≤ d → n₀ ≤ a + 1 → 4 * (a + 1) ≤ e + a + 1 →
      ∀ y : AffineSimplex.chartDomain e ((e + a : ℕ) + 1),
      ∀ z : AffineSimplex.chartDomain d ((d + a : ℕ) + 1),
      InterpolantLocalLaws.exteriorGeometry s ε e a y.val →
      InterpolantLocalLaws.exteriorGeometry s ε d a z.val →
      ∀ u : EuclideanSpace ℝ (Fin (a + 1)),
      u ∈ AffineSimplex.massSimplex a (((e + a : ℕ) + 1 : ℝ) - ∑ k, y.val k) →
      u ∈ AffineSimplex.massSimplex a (((d + a : ℕ) + 1 : ℝ) - ∑ k, z.val k) →
      WithLp.ofLp u ∈ goodBlockEvent s a.succPNat (e + a).succPNat (K * ε) →
      ∀ Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ,
      (∀ x (hx : RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val x ∈ gapAmbientDomain (e+a).succPNat),
        Ky x = physicalAmbientGapEnergy p (e+a).succPNat
          ⟨RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val x,hx⟩) →
      (∀ x (hx : RetainedSimplex.assemble d a (InterpolatingDensities.exteriorPermutation d a) z.val x ∈ gapAmbientDomain (d+a).succPNat),
        Kz x = physicalAmbientGapEnergy p (d+a).succPNat
          ⟨RetainedSimplex.assemble d a (InterpolatingDensities.exteriorPermutation d a) z.val x,hx⟩) →
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ i j : Fin (a+1),
        |(1-t)*hessianMatrix Ky u i j+t*hessianMatrix Kz u i j| ≤
          C*(a+1 : ℝ)^(κ*ε)*(1+|(i.val : ℝ)-j.val|)^(-s) := by
  obtain ⟨C,κ,hC,hκ,hb⟩ := CrossingCoefficients.physical_interpolant_entry_bound s K hs hK
  refine ⟨C,κ,hC,hκ,fun ε hε hσε => ?_⟩
  obtain ⟨n₀,hn₀,hb⟩ := hb ε hε hσε
  refine ⟨n₀,hn₀,?_⟩
  intro p hps e d a hed hn hsize y z hgy hgz u huy huz hgood Ky Kz hKy hKz t ht i j
  obtain ⟨H,J,hentry⟩ := hb p hps e d a hed hn hsize y z hgy hgz u huy huz hgood
  have he := hentry t ht i j
  rw [endpoint_hessian_internal p e a y Ky hKy u huy H,
    endpoint_hessian_internal p d a z Kz hKz u huz J]
  have hd : (Nat.dist i.val j.val : ℝ) = |(i.val : ℝ)-j.val| := by
    exact_mod_cast natCast_dist_eq_abs i.val j.val
  simpa only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Nat.succPNat_coe,hd] using he


/-- See Subsection 6.1 of the paper, complete long-range branch. The loss
exponent precedes epsilon, the size and tail power precede temperature,
and one prefactor works on each compact positive temperature interval.
The all-size matrix and physical coercivity clauses precede the large-size
upper bounds. Bounded scalar tests use their actual essential suprema.
The reference cutoff has the least degree prescribed by Lemma 5.4 of the paper, used before Lemma 6.3. -/
@[expose] def LongRangeBounds (s : Riesz1.RieszExponent) : Prop :=
    let h := (paperReferenceCutoffExponent s : ℕ)
    ∃ A K ε₀ κ γ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧ 0 < κ ∧ 0 < γ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∃ (n₀ : ℕ) (δ : ℝ), 2 ≤ n₀ ∧ 0 < δ ∧
      (128 : ℝ) ≤ (n₀ : ℝ)^(1-s.val/2-2*ε) ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    ∀ (a d e : ℕ) (_ha : 1 ≤ a) (hde : d ≤ e),
    let n := a.succPNat
    let N := ((n : ℕ)+d).succPNat
    ∀ _hN : 4*(n : ℕ) ≤ (N : ℕ), (n : ℝ)^(2/s.val) ≤ (N : ℝ) →
    ∀ (y : AffineSimplex.chartDomain (d+1) ((d+1+a : ℕ)+1))
      (z : AffineSimplex.chartDomain (e+1) ((e+1+a : ℕ)+1)) (L : ℝ),
    ((d+1+a : ℕ)+1 : ℝ)-∑ k, y.val k = L →
    ((e+1+a : ℕ)+1 : ℝ)-∑ k, z.val k = L →
    InterpolantLocalLaws.admissibleExterior (ofLong β s) (d+1) a (Nat.succ_le_succ (Nat.zero_le d)) θ ε A K y →
    InterpolantLocalLaws.admissibleExterior (ofLong β s) (e+1) a (Nat.succ_le_succ (Nat.zero_le e)) θ ε A K z →
    let Dy := RetainedSimplex.assemble (d+1) a (InterpolatingDensities.exteriorPermutation (d+1) a) y.val ⁻¹'
      gapAmbientDomain (d+1+a).succPNat
    let Dz := RetainedSimplex.assemble (e+1) a (InterpolatingDensities.exteriorPermutation (e+1) a) z.val ⁻¹'
      gapAmbientDomain (e+1+a).succPNat
    ∃ Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ,
      ContDiffOn ℝ ∞ Ky Dy ∧ ContDiffOn ℝ ∞ Kz Dz ∧
      (∀ u (hu : u ∈ Dy), Ky u = physicalAmbientGapEnergy (ofLong β s) (d+1+a).succPNat
        ⟨RetainedSimplex.assemble (d+1) a (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u,hu⟩) ∧
      (∀ u (hu : u ∈ Dz), Kz u = physicalAmbientGapEnergy (ofLong β s) (e+1+a).succPNat
        ⟨RetainedSimplex.assemble (e+1) a (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u,hu⟩) ∧
    ∀ t ∈ Icc (0 : ℝ) 1,
    let H := fun u : EuclideanSpace ℝ (Fin (a+1)) =>
      (∑ k, (θ.val ((a+1 : ℝ)^(-ε)*u k)+θ.val ((a+1 : ℝ)^(-ε)*(u k)⁻¹)))+(1-t)*Ky u+t*Kz u
    let m := PhysicalCore.properReferencePeriod s n N
    let k := ⌊(n : ℝ)^(K*ε)⌋₊^h
    ∃ (hm : 2 ≤ (m : ℕ)) (hnm : (n : ℕ) ≤ (m : ℕ))
      (hk : 1 ≤ k) (hkm : k ≤ (m : ℕ)/4),
      (∀ μ : Measure (AffineSimplex.chartDomain n ((n+d : ℕ)+1)),
        PeriodizedMatrixBounds (ν := μ) s n m hm k C κ γ ε
          (InterpolationMatrix.matrix β s n d e hde m hm hnm k θ ε (K*ε) t)) ∧
      (∀ x ∈ AffineSimplex.massSimplex a L, ∀ v : EuclideanSpace ℝ (Fin (a+1)),
        C⁻¹*(n : ℝ)^(-κ*ε)*(∑ i, (v i)^2) ≤ ∑ i,∑ j, v i*hessianMatrix H x i j*v j) ∧
    (n₀ ≤ (n : ℕ) →
      (∀ x ∈ AffineSimplex.massSimplex a L, ∀ i j : Fin (a+1),
        |(1-t)*hessianMatrix Ky x i j+t*hessianMatrix Kz x i j|^2+
          |InterpolationMatrix.penaltyHessian n θ ε x i j|^2 ≤
          C*(n : ℝ)^C*InterpolantLocalLaws.exceptionalWeight (n := n) s.val (WithLp.ofLp x)) ∧
      let μ : Measure (AffineSimplex.massSimplex a L) := (AffineSimplex.simplexVolume a L).comap Subtype.val
      let w := fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal (Real.exp (-β.val*H u.val))
      ∃ (h0 : (∫⁻ u, w u ∂μ) ≠ 0) (htop : (∫⁻ u, w u ∂μ) ≠ ⊤),
      ∃ hLN : L < ((n+d : ℕ)+1 : ℝ),
      let ρ := AffineFibre.normalizedMeasure μ w h0 htop
      let ν := ρ.map (InterpolationTransport.inclusion a L ((n+d : ℕ)+1) hLN)
      IsProbabilityMeasure ν ∧
      ∀ frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a),
      ∃ Q : ScalarFormData ν, ∃ hQ : IsClosedScalarDirichletForm Q,
      IsConservativeScalarForm Q ∧
      IsIntrinsicFibreForm a L ((n+d : ℕ)+1) hLN frame ν Q ∧
      let P : AffineSimplex.chartDomain n ((n+d : ℕ)+1) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ :=
        fun q i j => (1-t)*hessianMatrix Ky q.val i j+t*hessianMatrix Kz q.val i j
      let Y := InterpolationMatrix.multiplicationPart β s n d e hde m hm hnm k θ ε (K*ε) t P
      let wgt : Fin (n : ℕ) → ℝ := fun i => (min (i.val+1) ((n : ℕ)-i.val) : ℕ)^(-s.val/2)
      let inc : Fin (n : ℕ) → Fin (n : ℕ) → Fin (n : ℕ) → ℝ := fun j i l =>
        (Nat.dist i.val l.val : ℝ)*wgt j*
          (min (min (i.val+1) ((n : ℕ)-i.val)) (min (l.val+1) ((n : ℕ)-l.val)) : ℕ)^(-1-s.val/2)
      ∀ φ ψ : Lp ℝ 2 ν, MemLp (φ : _ → ℝ) ∞ ν → MemLp (ψ : _ → ℝ) ∞ ν →
      ∀ i j l : Fin (n : ℕ),
      ∃ hp : Integrable (matrixFieldPair Y (Pi.single j φ) (Pi.single i ψ)) ν,
      ∃ hd : Integrable (matrixFieldPair Y (Pi.single j φ)
        (fun q => (Pi.single i ψ : Fin (n : ℕ) → Lp ℝ 2 ν) q-(Pi.single l ψ : Fin (n : ℕ) → Lp ℝ 2 ν) q)) ν,
      |InterpolationMatrix.perturbationPair β s n d e hde m hm hnm k hk hkm θ ε (K*ε) t
        ν Q hQ P (Pi.single j φ) (Pi.single i ψ) hp| ≤
        C*(n : ℝ)^(κ*ε)*wgt i*wgt j*‖φ‖*‖ψ‖+
          C*Real.exp (-c*(n : ℝ)^δ)*
            ((eLpNorm (φ : _ → ℝ) ∞ ν).toReal*(eLpNorm (ψ : _ → ℝ) ∞ ν).toReal) ∧
      |InterpolationMatrix.perturbationPair β s n d e hde m hm hnm k hk hkm θ ε (K*ε) t
        ν Q hQ P (Pi.single j φ)
        (fun q => (Pi.single i ψ : Fin (n : ℕ) → Lp ℝ 2 ν) q-(Pi.single l ψ : Fin (n : ℕ) → Lp ℝ 2 ν) q) hd| ≤
        C*(n : ℝ)^(κ*ε)*inc j i l*‖φ‖*‖ψ‖+
          C*Real.exp (-c*(n : ℝ)^δ)*
            ((eLpNorm (φ : _ → ℝ) ∞ ν).toReal*(eLpNorm (ψ : _ → ℝ) ∞ ν).toReal))

/-- See Subsection 6.1 of the paper: all clauses of `LongRangeBounds`, assuming
the periodic-zeta connection formula and locally uniform rigidity from
the companion paper. -/
theorem long_range_bounds (hzeta : External.PeriodicZeta)
    (hRig : External.LongRangeRigidityLocallyUniform) (s : Riesz1.RieszExponent) :
    LongRangeBounds s := by
  unfold LongRangeBounds
  intro h
  obtain ⟨A,K,εbase,hA,hK,hεbase,hlocal⟩ :=
    InterpolantLocalLaws.local_laws hRig s.val s.property.1 (ne_of_lt s.property.2)
  obtain ⟨ρ,hρ,hprofiles⟩ := InterpolationBoundaryBridge.physical_good_profiles_ae_internal s K (by linarith)
  obtain ⟨κT,hκT,hpert⟩ := InterpolationPerturbation.perturbation_bounds_from_profiles_internal hzeta s h K ρ hρ
  let κM := (s.val+7+(h : ℝ))+(s.val+2+(h : ℝ)*(1+s.val))
  let κ := max (κM*K) (max κT (s.val+2))
  let γ := ((h : ℝ)+1)*K
  let ε₀ := min εbase (min (4*K*((h : ℝ)+1))⁻¹ ((1-s.val/2)/4))
  have hK0 : 0 < K := by linarith
  have hh0 : 0 ≤ (h : ℝ) := Nat.cast_nonneg h
  have hgap : 0 < 1-s.val/2 := by linarith [s.property.2]
  have hε₀ : 0 < ε₀ := lt_min hεbase (lt_min (by positivity) (by positivity))
  have hκ : 0 < κ := lt_of_lt_of_le hκT ((le_max_left _ _).trans (le_max_right _ _))
  have hγ : 0 < γ := by dsimp [γ]; positivity
  refine ⟨A,K,ε₀,κ,γ,hA,hK,hε₀,hκ,hγ,fun ε hε hεsmall => ?_⟩
  have hεbase' : ε < εbase := hεsmall.trans_le (min_le_left _ _)
  have hεcut : ε ≤ (4*K*((h : ℝ)+1))⁻¹ :=
    (hεsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hεgap : ε < (1-s.val/2)/4 :=
    hεsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hσε : s.val/2+2*ε < 1 := by linarith
  have hσε' : min s.val 1/2+2*ε < 1 := by rw [min_eq_left s.property.2.le]; exact hσε
  obtain ⟨δ,hδ,hlocalNext⟩ := hlocal ε hε hεbase'
  clear hlocal
  rename' hlocalNext => hlocal
  obtain ⟨ng,hng,hprofilesNext⟩ := hprofiles ε hε hσε
  clear hprofiles
  rename' hprofilesNext => hprofiles
  obtain ⟨ns,hns,hsquare⟩ := whole_simplex_bound s.val ε s.property.1 hε.le hσε'
  obtain ⟨nc,hnc,hC5⟩ := InterpolationCoefficients.complement_threshold (s.val/2) ε hσε
  let n₀ := max ng (max ns nc)
  refine ⟨n₀,δ,hng.trans (le_max_left _ _),hδ,hC5 n₀ ((le_max_right _ _).trans (le_max_right _ _)),?_⟩
  intro βlo βhi hlo hle θ
  have hhi : 0 < βhi := hlo.trans_le hle
  obtain ⟨D,hD,hsq⟩ := hsquare θ
  obtain ⟨Ag,hAg,hprofilesNext⟩ := hprofiles βhi hhi
  clear hprofiles
  rename' hprofilesNext => hprofiles
  obtain ⟨Cl,cl,hCl,hcl,hlocalNext⟩ := hlocal βlo βhi hlo hle θ
  clear hlocal
  rename' hlocalNext => hlocal
  obtain ⟨Cp,hCp,hpertNext⟩ := hpert ε δ hε.le hδ βhi Ag D Cl cl hhi hAg hD hCl hcl
  clear hpert
  rename' hpertNext => hpert
  obtain ⟨Cm,hCm,hmat⟩ := InterpolationMatrix.matrix_bounds s θ h
  let b := min 1 (s.val*(s.val+1))
  have hb : 0 < b := lt_min zero_lt_one (by have := s.property.1; positivity)
  let C := 1+Cm+Cp+D+b⁻¹
  have hC : 0 < C := by dsimp [C]; linarith [inv_pos.mpr hb]
  have hCmC : Cm ≤ C := by dsimp [C]; linarith [inv_pos.mpr hb]
  have hCpC : Cp ≤ C := by dsimp [C]; linarith [inv_pos.mpr hb]
  have hDC : D ≤ C := by dsimp [C]; linarith [inv_pos.mpr hb]
  have hCb : C⁻¹ ≤ b := (inv_le_comm₀ hC hb).mpr (by dsimp [C]; linarith [inv_pos.mpr hb])
  refine ⟨C,cl/4,hC,by positivity,?_⟩
  intro β hβ a d e ha hde n N hN hNpower y z L hyL hzL hy hz Dy Dz
  have hycompat : (∑ k,y.val k)+L = ((d+1+a : ℕ)+1 : ℝ) := by linarith
  have hzcompat : (∑ k,z.val k)+L = ((e+1+a : ℕ)+1 : ℝ) := by linarith
  obtain ⟨Ky,hKy,hky,_⟩ := InterpolationCoercivity.assembled_energy_realization (ofLong β s) (d+1) a (by omega) y
  obtain ⟨Kz,hKz,hkz,_⟩ := InterpolationCoercivity.assembled_energy_realization (ofLong β s) (e+1) a (by omega) z
  refine ⟨Ky,Kz,hKy,hKz,hky,hkz,?_⟩
  intro t ht H m k
  have hm : 2 ≤ (m : ℕ) := by
    have hh := (PhysicalCore.properReferencePeriod_bounds s n N (by omega)).1
    change 2 ≤ (PhysicalCore.properReferencePeriod s n N : ℕ)
    have := n.pos
    omega
  have hnm : (n : ℕ) ≤ (m : ℕ) := by
    have hh := (PhysicalCore.properReferencePeriod_bounds s n N (by omega)).1
    change (n : ℕ) ≤ (PhysicalCore.properReferencePeriod s n N : ℕ)
    omega
  have hperiod : (d+1+a).succPNat = N := by apply PNat.eq; dsimp [N,n]; omega
  have hperiodR : ((d+1+a : ℕ)+1 : ℝ) = ((n+d : ℕ)+1 : ℝ) := by
    exact_mod_cast (show d+1+a+1 = (n : ℕ)+d+1 by dsimp [n]; omega)
  have hn2 : 2 ≤ (n : ℕ) := by dsimp [n]; omega
  have hmn : 2*(n : ℕ) ≤ (m : ℕ) := (PhysicalCore.properReferencePeriod_bounds s n N (by omega)).1
  have hη : 0 ≤ K*ε := by positivity
  have hsmall : ((h : ℝ)+1)*(K*ε) ≤ 1/4 := by
    have hpos : 0 < 4*K*((h : ℝ)+1) := by positivity
    have hh := mul_le_mul_of_nonneg_right hεcut hpos.le
    rw [inv_mul_cancel₀ hpos.ne'] at hh
    nlinarith only [hh]
  have hηa : K*ε ≤ 1-s.val/2 := by nlinarith only [hsmall,mul_nonneg hh0 hη,s.property.2]
  obtain ⟨hk,hkm4⟩ := AuxiliaryMean.interpolation_cutoff_bounds_internal n m hn2 hmn (K*ε) h hη (by nlinarith only [hsmall,hη])
  have hkm : k ≤ (m : ℕ)/4 := by dsimp [k]; omega
  refine ⟨hm,hnm,hk,hkm,?_,?_,?_⟩
  · intro μ
    apply PeriodizedMatrixBoundsMonotone.of_losses_le s n m hm k (by linarith : 0 < Cm) hCmC
      (show κM*(K*ε) ≤ κ*ε from by
        have hh : κM*K ≤ κ := le_max_left _ _
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh hε.le)
      (show ((h : ℝ)+1)*(K*ε) ≤ γ*ε from by dsimp [γ]; ring_nf; exact le_rfl)
    exact hmat β n d e hde hN m hm hmn
      (PhysicalCore.properReferencePeriod_bounds s n N (by omega)).2.1
      (InterpolationMatrix.properReferencePeriod_scale s n N (by omega) hNpower)
      ε (K*ε) t hε.le hη hηa ht.1 ht.2 hkm μ
  · intro x hx v
    have hbnd := coercivity_internal (ofLong β s) θ ε hε.le (d+1) (e+1) a ha y z L hyL hzL Ky Kz hky hkz t ht x hx v
    have hp := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ n by exact_mod_cast n.pos)
      (show -κ*ε ≤ -(s.val+2)*ε by
        have hle := (le_max_right κT (s.val+2)).trans (le_max_right (κM*K) (max κT (s.val+2)))
        nlinarith only [mul_le_mul_of_nonneg_right hle hε.le])
    have hl := mul_le_mul hCb hp (by positivity) hb.le
    exact (mul_le_mul_of_nonneg_right hl (Finset.sum_nonneg (fun i _ => sq_nonneg (v i)))).trans
      (by simpa only [ofLong,n,Nat.succPNat_coe,Nat.cast_succ] using hbnd)
  · intro hlarge
    have hng' : ng ≤ a+1 := (le_max_left _ _).trans hlarge
    have hns' : ns ≤ a+1 := ((le_max_left _ _).trans (le_max_right _ _)).trans hlarge
    have hNy : 4*(a+1) ≤ d+1+a+1 := by dsimp [N,n] at hN; omega
    have hNz : 4*(a+1) ≤ e+1+a+1 := by omega
    have hbnd := hsq (ofLong β s) rfl (d+1) (e+1) a hns' hNy hNz y z hy.1 hz.1 L hyL hzL Ky Kz hky hkz t ht
    have hsquare' (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1))
        (hx : x.val ∈ AffineSimplex.massSimplex a L) (i j : Fin (n : ℕ)) :
        |(1-t)*hessianMatrix Ky x.val i j+t*hessianMatrix Kz x.val i j|^2+
          |InterpolationMatrix.penaltyHessian n θ ε x.val i j|^2 ≤
          D*(n : ℝ)^D*InterpolantLocalLaws.exceptionalWeight (n := n) s.val (WithLp.ofLp x.val) := by
      simpa only [InterpolationMatrix.penaltyHessian,n,Nat.succPNat_coe,Nat.cast_succ] using hbnd x.val hx i j
    refine ⟨?_,?_⟩
    · intro x hx i j
      let q : AffineSimplex.chartDomain n ((n+d : ℕ)+1) :=
        ⟨x,hx.1,hx.2.trans_lt (by rw [← hperiodR]; exact InterpolationTransport.compatible_mass_lt a (d+1) (by omega) L y hycompat)⟩
      exact (hsquare' q hx i j).trans (by
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
        have hw : 0 ≤ InterpolantLocalLaws.exceptionalWeight (n := n) s.val (WithLp.ofLp x) :=
          zero_le_one.trans (InterpolantLocalLaws.one_le_exceptionalWeight s.val _ (fun i => (hx.1 i).le))
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul hDC (Real.rpow_le_rpow_of_exponent_le hn1 hDC) (by positivity) hC.le) hw)
    · intro μ w
      have hLN : L < ((n+d : ℕ)+1 : ℝ) := by
        rw [←hperiodR]
        exact InterpolationTransport.compatible_mass_lt a (d+1) (by omega) L y hycompat
      obtain ⟨h0,htop,hprob,hforms⟩ := physical_form_internal (ofLong β s) θ ε (d+1) (e+1) a
        (by omega) (by omega) y z L hyL hzL Ky Kz hky hkz _ hperiodR hLN t ht
      refine ⟨h0,htop,hLN,?_⟩
      let ρlaw := AffineFibre.normalizedMeasure μ w h0 htop
      let ν := ρlaw.map (InterpolationTransport.inclusion a L ((n+d : ℕ)+1) hLN)
      have : IsProbabilityMeasure ν := hprob
      refine ⟨hprob,?_⟩
      intro frame
      obtain ⟨Q,hQ,hcons,hIntrinsic⟩ := hforms frame
      refine ⟨Q,hQ,hcons,hIntrinsic,?_⟩
      intro P Y wgt inc φ ψ hφ hψ i j l
      have hsupport := common_fibre_support_internal a d e L y z hyL hzL hLN ρlaw
      have hg := hprofiles β hβ.2 a d e (d+1) (e+1) hde (by omega) (by omega) hng' hNy
        m hm hnm k hmn θ t ht y z hy.1 hz.1 Ky Kz hky hkz ν hsupport
      have hsquareAE : ∀ᵐ x ∂ν.restrict (InterpolationMatrix.goodSet s n d (K*ε))ᶜ,
          ∀ i j, |P x i j|^2+|InterpolationMatrix.penaltyHessian n θ ε x.val i j|^2 ≤
            D*(n : ℝ)^D*InterpolantLocalLaws.exceptionalWeight (n := n) s.val (WithLp.ofLp x.val) := by
        filter_upwards [ae_restrict_of_ae hsupport] with x hx i j
        exact hsquare' x (hyL ▸ hx.1) i j
      have hpowerY : ((a+1 : ℕ) : ℝ)^(2/s.val) ≤ ((d+1+a : ℕ)+1 : ℝ) := by
        rw [hperiodR]
        simpa only [N,n,Nat.succPNat_coe,Nat.cast_succ] using hNpower
      obtain ⟨_,hlocal'⟩ := hlocal (ofLong β s) rfl hβ.1 hβ.2 (d+1) (e+1) a (by omega) (by omega) ha hNy
        (by omega) hpowerY
      obtain ⟨h0',htop',_,hbad,_,_⟩ := hlocal' L y z hycompat hzcompat hy hz t ht.1 ht.2
      have htail : (∫⁻ x in (InterpolationMatrix.goodSet s n d (K*ε))ᶜ,
          ENNReal.ofReal (InterpolantLocalLaws.exceptionalWeight (n := n) s.val (WithLp.ofLp x.val)) ∂ν) ≤
          ENNReal.ofReal (Cl*Real.exp (-cl*(n : ℝ)^δ)) := by
        dsimp only [ν]
        erw [InterpolationTransport.weighted_tail_eq s a d L (K*ε) hLN ρlaw]
        simp only [AffineFibre.normalizedMeasure_eq_smul] at hbad ⊢
        simp_rw [←hky,←hkz] at hbad
        have hperiodEvent : (d+1+a).succPNat = (a+1+d).succPNat := by
          apply PNat.eq
          simp only [Nat.succPNat_coe]
          omega
        simpa only [ρlaw,w,H,μ,n,Nat.succPNat_coe,Nat.cast_succ,ofLong,
          AffineFibre.normalizedMeasure_eq_smul,hperiodEvent] using hbad
      have hP (i j) : Measurable (fun x => P x i j) :=
        (((DifferentiatedPoisson.measurable_hessian_entries (V := Ky) i j).comp measurable_subtype_coe).const_mul (1-t)).add
          (((DifferentiatedPoisson.measurable_hessian_entries (V := Kz) i j).comp measurable_subtype_coe).const_mul t)
      obtain ⟨hp,hd,hpoint,hinc⟩ := hpert β hβ.2 n d e hde m hm hnm hk hkm θ t ν Q hQ P hP hg hsquareAE htail
        φ ψ (eLpNorm (φ : _ → ℝ) ∞ ν).toReal (eLpNorm (ψ : _ → ℝ) ∞ ν).toReal
        ENNReal.toReal_nonneg ENNReal.toReal_nonneg
        (InterpolationPerturbation.essential_scalar_bound_internal φ hφ)
        (InterpolationPerturbation.essential_scalar_bound_internal ψ hψ) i j l
      refine ⟨hp,hd,hpoint.trans ?_,hinc.trans ?_⟩ <;>
        dsimp only [κ] <;> gcongr <;> first
        | exact_mod_cast n.pos
        | exact (le_max_left κT (s.val+2)).trans (le_max_right (κM*K) (max κT (s.val+2)))


/-- See Subsection 6.1 of the paper, complete short-range branch. Global
physical and identity-cutoff coercivity hold at every size at least two. The entry and whole-simplex square bounds start at the stated threshold. -/
@[expose] def ShortRangeBounds (s : ShortExponent) : Prop :=
    ∃ A K ε₀ κ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧ 0 < κ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∃ (n₀ : ℕ) (δ : ℝ), 2 ≤ n₀ ∧ 0 < δ ∧
      (128 : ℝ) ≤ (n₀ : ℝ)^(1-(min s.val 1)/2-2*ε) ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    ∀ (a e f : ℕ) (_ha : 1 ≤ a) (_hef : e ≤ f),
      4*(a+1) ≤ e+a+1 → (a+1 : ℝ)^(2/s.val) ≤ ((e+a : ℕ)+1 : ℝ) →
    ∀ (y : AffineSimplex.chartDomain e ((e+a : ℕ)+1))
      (z : AffineSimplex.chartDomain f ((f+a : ℕ)+1)) (L : ℝ),
    ∀ (he : 1 ≤ e) (hf : 1 ≤ f),
    ((e+a : ℕ)+1 : ℝ)-∑ k, y.val k = L →
    ((f+a : ℕ)+1 : ℝ)-∑ k, z.val k = L →
    InterpolantLocalLaws.admissibleExterior (ofShort β s) e a he θ ε A K y →
    InterpolantLocalLaws.admissibleExterior (ofShort β s) f a hf θ ε A K z →
    let Dy := RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val ⁻¹'
      gapAmbientDomain (e+a).succPNat
    let Dz := RetainedSimplex.assemble f a (InterpolatingDensities.exteriorPermutation f a) z.val ⁻¹'
      gapAmbientDomain (f+a).succPNat
    ∃ Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ,
      ContDiffOn ℝ ∞ Ky Dy ∧ ContDiffOn ℝ ∞ Kz Dz ∧
      (∀ u (hu : u ∈ Dy), Ky u = physicalAmbientGapEnergy (ofShort β s) (e+a).succPNat
        ⟨RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val u,hu⟩) ∧
      (∀ u (hu : u ∈ Dz), Kz u = physicalAmbientGapEnergy (ofShort β s) (f+a).succPNat
        ⟨RetainedSimplex.assemble f a (InterpolatingDensities.exteriorPermutation f a) z.val u,hu⟩) ∧
    ∀ t ∈ Icc (0 : ℝ) 1,
    let H := fun u : EuclideanSpace ℝ (Fin (a+1)) =>
      (∑ k, (θ.val ((a+1 : ℝ)^(-ε)*u k)+θ.val ((a+1 : ℝ)^(-ε)*(u k)⁻¹)))+(1-t)*Ky u+t*Kz u
    let M := fun x : EuclideanSpace ℝ (Fin (a+1)) =>
      if WithLp.ofLp x ∈ goodBlockEvent s.val a.succPNat (e+a).succPNat (K*ε)
        then hessianMatrix H x else (1 : Matrix (Fin (a+1)) (Fin (a+1)) ℝ)
    (∀ x ∈ AffineSimplex.massSimplex a L, ∀ v : Fin (a+1) → ℝ,
      C⁻¹*(a+1 : ℝ)^(-κ*ε)*(∑ i, (v i)^2) ≤ ∑ i,∑ j, v i*hessianMatrix H x i j*v j) ∧
    (∀ x ∈ AffineSimplex.massSimplex a L, ∀ v : Fin (a+1) → ℝ,
      C⁻¹*(a+1 : ℝ)^(-κ*ε)*(∑ i, (v i)^2) ≤ ∑ i,∑ j, v i*M x i j*v j) ∧
    (n₀ ≤ a+1 → ∀ x ∈ AffineSimplex.massSimplex a L,
      (∀ i j : Fin (a+1), |M x i j| ≤ C*(a+1 : ℝ)^(κ*ε)*(1+|(i.val : ℝ)-j.val|)^(-s.val)) ∧
      ∀ i j : Fin (a+1),
        |(1-t)*hessianMatrix Ky x i j+t*hessianMatrix Kz x i j|^2+
          |hessianMatrix (fun u : EuclideanSpace ℝ (Fin (a+1)) =>
            ∑ k, (θ.val ((a+1 : ℝ)^(-ε)*u k)+θ.val ((a+1 : ℝ)^(-ε)*(u k)⁻¹))) x i j|^2 ≤
          C*(a+1 : ℝ)^C*InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s.val (WithLp.ofLp x))

/-- See Subsection 6.1 of the paper: every clause of `ShortRangeBounds`. -/
theorem short_range_bounds (hRig : External.LongRangeRigidityLocallyUniform) (s : ShortExponent) :
    ShortRangeBounds s := by
  unfold ShortRangeBounds
  obtain ⟨A,K,εbase,hA,hK,hεbase,_⟩ :=
    InterpolantLocalLaws.local_laws hRig s.val (by linarith [s.property]) (ne_of_gt s.property)
  obtain ⟨Ce,κe,hCe,hκe,hentry⟩ := interaction_entry_internal s.val K (by linarith [s.property]) (by linarith)
  let κ := max (max (4*K) κe) (s.val+2)
  let ε₀ := min εbase (1/16)
  have hκ : 0 < κ := by dsimp [κ]; have := s.property; positivity
  refine ⟨A,K,ε₀,κ,hA,hK,lt_min hεbase (by norm_num),hκ,fun ε hε hsmall => ?_⟩
  have hσε : min s.val 1/2+2*ε < 1 := by
    rw [min_eq_right s.property.le]
    have hh := hsmall.trans_le (min_le_right εbase (1/16))
    linarith
  obtain ⟨ne,hne,hentry⟩ := hentry ε hε.le hσε
  obtain ⟨ns,hns,hsquare⟩ := whole_simplex_bound s.val ε (by linarith [s.property]) hε.le hσε
  obtain ⟨nc,hnc,hC5⟩ := InterpolationCoefficients.complement_threshold (min s.val 1/2) ε hσε
  let n₀ := max ne (max ns nc)
  refine ⟨n₀,ε,hne.trans (le_max_left _ _),hε,hC5 n₀ ((le_max_right _ _).trans (le_max_right _ _)),?_⟩
  intro βlo βhi hlo hle θ
  obtain ⟨F,hF,hshort⟩ := InterpolationCoercivity.short_range_entry_internal θ
  obtain ⟨B,hB,hsq⟩ := hsquare θ
  let b := min 1 (s.val*(s.val+1))
  have hb : 0 < b := lt_min zero_lt_one (by have := s.property; positivity)
  let C := 2+F+Ce+B+b⁻¹
  have hC : 0 < C := by dsimp [C]; linarith [inv_pos.mpr hb]
  have hCb : C⁻¹ ≤ b := (inv_le_comm₀ hC hb).mpr (by dsimp [C]; linarith [inv_pos.mpr hb])
  have hsumC : 1+F+Ce ≤ C := by dsimp [C]; linarith [inv_pos.mpr hb]
  have hBC : B ≤ C := by dsimp [C]; linarith [inv_pos.mpr hb]
  refine ⟨C,1,hC,by norm_num,?_⟩
  intro β hβ a e f ha hef hsize hpower y z L he hf hyL hzL hy hz Dy Dz
  obtain ⟨Ky,hKy,hky,_⟩ := InterpolationCoercivity.assembled_energy_realization (ofShort β s) e a (by omega) y
  obtain ⟨Kz,hKz,hkz,_⟩ := InterpolationCoercivity.assembled_energy_realization (ofShort β s) f a (by omega) z
  refine ⟨Ky,Kz,hKy,hKz,hky,hkz,?_⟩
  intro t ht H M
  have hn1 : (1 : ℝ) ≤ a+1 := by have := Nat.cast_nonneg a (α := ℝ); linarith
  have hn0 : (0 : ℝ) < a+1 := by positivity
  have hglob := coercivity_internal (ofShort β s) θ ε hε.le e f a ha y z L hyL hzL Ky Kz hky hkz t ht
  have hloss : C⁻¹*(a+1 : ℝ)^(-κ*ε) ≤ b*(a+1 : ℝ)^(-(s.val+2)*ε) := by
    apply mul_le_mul hCb _ (by positivity) hb.le
    apply Real.rpow_le_rpow_of_exponent_le hn1
    have hh := le_max_right (max (4*K) κe) (s.val+2)
    nlinarith
  have hglobal (x) (hx : x ∈ AffineSimplex.massSimplex a L) (v : Fin (a+1) → ℝ) :
      C⁻¹*(a+1 : ℝ)^(-κ*ε)*(∑ i,(v i)^2) ≤ ∑ i,∑ j,v i*hessianMatrix H x i j*v j := by
    exact (mul_le_mul_of_nonneg_right hloss (Finset.sum_nonneg (fun i _ => sq_nonneg (v i)))).trans
      (hglob x hx (WithLp.toLp 2 v))
  refine ⟨hglobal,?_,?_⟩
  · intro x hx v
    have hcut := (InterpolationCoercivity.identity_cutoff_coercivity_internal
      (AffineSimplex.massSimplex a L)
      {x | WithLp.ofLp x ∈ goodBlockEvent s.val a.succPNat (e+a).succPNat (K*ε)} H
      (c := b) (w := (a+1 : ℝ)^(-(s.val+2)*ε)) hb (by positivity)
      (Real.rpow_le_one_of_one_le_of_nonpos hn1 (by have := s.property; nlinarith))
      (fun u hu v => hglob u hu (WithLp.toLp 2 v))).2 x hx v
    have hb1 : b ≤ 1 := min_le_left _ _
    rw [min_eq_left hb1] at hcut
    exact (mul_le_mul_of_nonneg_right hloss (Finset.sum_nonneg (fun i _ => sq_nonneg (v i)))).trans hcut
  · intro hlarge x hx
    have hne' : ne ≤ a+1 := (le_max_left _ _).trans hlarge
    have hns' : ns ≤ a+1 := ((le_max_left _ _).trans (le_max_right _ _)).trans hlarge
    have _hxY : x ∈ AffineSimplex.massSimplex a (((e+a : ℕ)+1 : ℝ)-∑ k,y.val k) := hyL ▸ hx
    have _hxZ : x ∈ AffineSimplex.massSimplex a (((f+a : ℕ)+1 : ℝ)-∑ k,z.val k) := hzL ▸ hx
    let G := {u : EuclideanSpace ℝ (Fin (a+1)) |
      u ∈ AffineSimplex.massSimplex a L ∧ WithLp.ofLp u ∈ goodBlockEvent s.val a.succPNat (e+a).succPNat (K*ε)}
    have hlower : ∀ u ∈ G, ∀ i, (a+1 : ℝ)^(-(K*ε)) ≤ u i := by
      intro u hu i
      simpa only [Nat.succPNat_coe,Nat.cast_succ] using (hu.2.2.1 i).1
    have hsmooth : ∀ u ∈ G, ContDiffAt ℝ ∞ Ky u ∧ ContDiffAt ℝ ∞ Kz u := by
      intro u hu
      have hUy := fibre_mem_internal e a y L hyL hu.1
      have hUz := fibre_mem_internal f a z L hzL hu.1
      exact ⟨hKy.contDiffAt (((PhysicalEnergy.isOpen_gapAmbientDomain _).preimage
        (RetainedSimplex.continuous_assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val)).mem_nhds hUy),
        hKz.contDiffAt (((PhysicalEnergy.isOpen_gapAmbientDomain _).preimage
        (RetainedSimplex.continuous_assemble f a (InterpolatingDensities.exteriorPermutation f a) z.val)).mem_nhds hUz)⟩
    have hcross : ∀ u ∈ G, ∀ i j,
        |(1-t)*hessianMatrix Ky u i j+t*hessianMatrix Kz u i j| ≤
          Ce*(a+1 : ℝ)^(κe*ε)*(1+|(i.val : ℝ)-j.val|)^(-s.val) := by
      intro u hu i j
      exact hentry (ofShort β s) rfl e f a hef hne' hsize y z hy.1 hz.1 u
        (hyL ▸ hu.1) (hzL ▸ hu.1) hu.2 Ky Kz hky hkz t ht i j
    have hentries := hshort a ε (K*ε) (κe*ε) s.val Ce t hε.le (by have := hK; positivity)
      (by positivity) s.property hCe.le G Ky Kz hlower hsmooth hcross x
    refine ⟨fun i j => ?_,fun i j => ?_⟩
    · have he : |M x i j| ≤ (1+F+Ce)*(a+1 : ℝ)^(max (4*(K*ε)) (κe*ε))*(1+|(i.val : ℝ)-j.val|)^(-s.val) := by
        have hr := hentries i j
        by_cases hg : x ∈ G
        · rw [ite_eq_left hg] at hr
          dsimp only [M]
          rw [ite_eq_left hg.2]
          exact hr
        · rw [ite_eq_right hg] at hr
          have hng : WithLp.ofLp x ∉ goodBlockEvent s.val a.succPNat (e+a).succPNat (K*ε) :=
            fun h => hg ⟨hx,h⟩
          dsimp only [M]
          rw [ite_eq_right hng]
          exact hr
      apply he.trans
      have hp : max (4*(K*ε)) (κe*ε) ≤ κ*ε := by
        apply max_le
        · have hh := (le_max_left (4*K) κe).trans (le_max_left (max (4*K) κe) (s.val+2))
          nlinarith
        · have hh := (le_max_right (4*K) κe).trans (le_max_left (max (4*K) κe) (s.val+2))
          nlinarith
      gcongr
    · have hp := hsq (ofShort β s) rfl e f a hns' hsize (by omega) y z hy.1 hz.1 L hyL hzL
        Ky Kz hky hkz t ht x hx i j
      have hW : 0 ≤ InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s.val (WithLp.ofLp x) :=
        zero_le_one.trans (InterpolantLocalLaws.one_le_exceptionalWeight s.val _ (fun i => (hx.1 i).le))
      exact hp.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul hBC (Real.rpow_le_rpow_of_exponent_le hn1 hBC) (by positivity) hC.le) hW)

/-- See Subsection 6.1 of the paper, all clauses in both exponent
ranges. The two transparent predicates spell out the full statements,
including all quantifier order and normalization data. Together the
exponent subtypes cover exactly `(0,1) ∪ (1,∞)`. -/
theorem coefficient_bounds (hzeta : External.PeriodicZeta)
    (hRig : External.LongRangeRigidityLocallyUniform) :
    (∀ s : Riesz1.RieszExponent, LongRangeBounds s) ∧
    (∀ s : ShortExponent, ShortRangeBounds s) :=
  ⟨long_range_bounds hzeta hRig, short_range_bounds hRig⟩

end Riesz2.InterpolationCoefficientBounds
