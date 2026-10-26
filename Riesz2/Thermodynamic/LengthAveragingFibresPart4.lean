/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.LengthAveragingFibresPart2
public import Riesz2.Thermodynamic.FixedLengthDecayPart5

/-!
# Intrinsic forms and conditional comparison on marginal length fibres

Supporting results for the proof of Lemma 6.5. The law is the actual retained marginal
kernel, and exceptional energies use its weighted conditional integral before conversion
to real numbers.
-/

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Classical ContDiff

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.LengthAveragingFibres

section IntrinsicLaw

variable (p : Parameters) (n m : ℕ) (θ : PhysicalCutoff) (ε : ℝ)
  (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ))

/-- See Lemma 6.5 and the proof of Lemma 6.5 of the paper: the retained
kernel is exactly the normalized Hausdorff marginal density, included in
the retained chart. This identifies the law before transporting any form. -/
theorem retained_normalized_law_internal :
    ∃ h0 ht, retainedKernel p n m θ ε L =
      (AffineFibre.normalizedMeasure
        ((AffineSimplex.simplexVolume n L.val).comap Subtype.val)
        (fun u : AffineSimplex.massSimplex n L.val => marginalWeight p n m θ ε u.val)
        h0 ht).map (InterpolationTransport.inclusion n L.val _ L.property.2) := by
  let μ : Measure (AffineSimplex.massSimplex n L.val) :=
    (AffineSimplex.simplexVolume n L.val).comap Subtype.val
  have hv := MeasurableEmbedding.subtype_coe (RetainedSimplex.measurableSet_simplex n L.val)
  have hvol : μ.map Subtype.val = AffineSimplex.simplexVolume n L.val := by
    rw [map_comap_subtype_coe (RetainedSimplex.measurableSet_simplex n L.val)]
    rw [AffineSimplex.simplexVolume_eq_restrict,
      Measure.restrict_restrict (RetainedSimplex.measurableSet_simplex n L.val), inter_self]
  have hz : (∫⁻ u, marginalWeight p n m θ ε u.val ∂μ) =
      ∫⁻ x, marginalWeight p n m θ ε x ∂AffineSimplex.simplexVolume n L.val := by
    rw [← hvol, hv.lintegral_map]
  have h0 := hz.trans_ne (fibre_mass p n m θ ε L).1
  have ht := hz.trans_ne (fibre_mass p n m θ ε L).2
  refine ⟨h0, ht, ?_⟩
  apply (MeasurableEmbedding.subtype_coe
    (AffineSimplex.isOpen_chartDomain _ _).measurableSet).map_injective
  rw [map_retainedKernel, InterpolationTransport.map_inclusion_val]
  have hm := AffineFibre.normalizedMeasure_map μ hv
    (measurable_marginalWeight p n m θ ε) h0 ht
  change AffineFibre.normalizedMeasure _ _ _ _ = _
  simp only [AffineFibre.normalizedMeasure_eq_smul] at hm ⊢
  rw [hvol] at hm
  exact hm

/-- See the proof of Lemma 6.5 in the paper: every interior retained
marginal fibre has the intrinsic closed conservative scalar form obtained
from its smooth density in an orthonormal mass chart. The density retains
the physical penalty at `ε`, independently of the fine tolerance. -/
theorem retained_intrinsic_scalar_internal
    (frame : AffineSimplex.Tangent n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    let P := fun x : EuclideanSpace ℝ (Fin (n+1)) =>
      p.val.1 * ∑ i, (θ.val ((n+1 : ℝ)^(-ε)*x i) +
        θ.val ((n+1 : ℝ)^(-ε)*(x i)⁻¹)) -
      Real.log (∫ y : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n+1) m (Equiv.refl _) (x,y)).toReal)
    let U := frame '' (AffineSimplex.centredChart n L.val ⁻¹' AffineSimplex.massSimplex n L.val)
    let V := fun z => P (AffineSimplex.centredChart n L.val (frame.symm z))
    ∃ ν : Measure (EuclideanSpace ℝ (Fin n)),
      IsEuclideanGibbsPotential volume ν U V ∧
      (ν.comap (Subtype.val : U → _)).map
        (InterpolationTransport.orthonormalInclusion n L.val _ L.property.2 frame) =
          retainedKernel p n m θ ε L ∧
      ∃ Q : ScalarFormData (retainedKernel p n m θ ε L),
        IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q := by
  intro P U V
  obtain ⟨h0, ht, hlaw⟩ := retained_normalized_law_internal p n m θ ε L
  have hsm := (ConditionalWellPosedness.penalized_marginal_fibre_regular p n m
    (Equiv.refl _) L.property.2 θ
    (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < n+1) (-ε)) Finset.univ true).1
  have hV : ContDiffOn ℝ ∞ V U := by
    apply hsm.comp frame.symm.contDiff.contDiffOn
    rintro z ⟨y, hy, rfl⟩
    simpa only [frame.symm_apply_apply] using hy
  have hd (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ U)
      (hx : AffineSimplex.centredChart n L.val (frame.symm z) ∈
        AffineSimplex.massSimplex n L.val) :
      marginalWeight p n m θ ε (AffineSimplex.centredChart n L.val (frame.symm z)) =
        ENNReal.ofReal (Real.exp (-V z)) := by
    have hh := ConditionalWellPosedness.penalized_marginal_fibre_density p n m
      (Equiv.refl _) L.property.2 θ ((n+1 : ℝ)^(-ε)) Finset.univ true hx
    simpa only [V, P, marginalWeight, ite_true, Equiv.refl_apply] using hh.symm
  have hresult :=
    InterpolationTransport.scalar_of_smooth_density_internal n L.val _ L.property.2
      frame V hV (fun u => marginalWeight p n m θ ε u.val)
      ((measurable_marginalWeight p n m θ ε).comp measurable_subtype_coe) hd h0 ht
  dsimp only at hresult
  rw [← hlaw] at hresult
  exact hresult

end IntrinsicLaw

section MarginalHessian

/-- See the proof of Lemma 6.5 in the paper: adding the active penalty
only adds its own Hessian. The unforced marginal Hessian, including its
score covariance subtraction, is unchanged. This identity holds on the
whole positive retained carrier in either exponent regime. -/
theorem marginal_penalty_hessian_internal (p : Parameters) (n : ℕ+) (m : ℕ)
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a) (b : Bool)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (i j : Fin (n : ℕ)) :
    let F := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      ∑ k, (θ.val (a*y k) + if b then θ.val (a*(y k)⁻¹) else 0)
    let V := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      -Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,z)).toReal)
    hessianMatrix (fun y => p.val.1*F y+V y) x.val i j =
      p.val.1*hessianMatrix F x.val i j + hessianMatrix V x.val i j := by
  intro F V
  have hF := DecayShort.PhysicalComparison.penalty_contDiffAt n θ ha b x.val x.property.1
  have hV : ContDiffAt ℝ 2 V x.val :=
    ((Riesz2.MarginalHessian.physical_marginal_potential_smooth p n m n.pos
      (Equiv.refl _)).contDiffAt
      ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds x.property)).of_le (by norm_num)
  rw [DecayShort.PhysicalComparison.hessianMatrix_entry
    ((contDiffAt_const.mul hF).add hV),
    PhysicalCollision.internal_hessian_add (contDiffAt_const.mul hF) hV,
    PhysicalCollision.internal_hessian_const_mul hF,
    DecayShort.PhysicalComparison.hessianMatrix_entry hF,
    DecayShort.PhysicalComparison.hessianMatrix_entry hV]

/-- See the proof of Lemma 6.5 in the paper: the two-sided marginal
Hessian has the literal conditional interval matrix, compensation matrix,
and negative score covariance. The exterior conditional is unchanged by
the inverse-gap penalty. This is pointwise, hence valid on every retained
length fibre, including a point exterior conditional. -/
theorem long_twoSided_hessian_internal (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε : ℝ) :
    let p := ofLong β s
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      β.val * ∑ i, (θ.val ((n : ℝ)^(-ε)*x i) +
        θ.val ((n : ℝ)^(-ε)*(x i)⁻¹)) -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal)
    ∃ U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain ((n : ℕ)+m).succPNat) ∧
      (∀ y : gapAmbientDomain ((n : ℕ)+m).succPNat,
        U y.val = β.val*physicalAmbientGapEnergy p ((n : ℕ)+m).succPNat y) ∧
      ∀ x : AffineSimplex.chartDomain n ((n+m : ℕ)+1),
        let μ := ProperMarginalChart.conditionalMeasure p n m n.pos (Equiv.refl _) x
        let q := WithLp.toLp 2 (ConditionalForces.compensationVector n m)
        let Xi := fun i z => β.val⁻¹ *
          (fderiv ℝ U (RetainedSimplex.chart n m ((n+m : ℕ)+1)
            (Equiv.refl _) (x.val,z)) (EuclideanSpace.single (i.castAdd m).castSucc 1) -
           fderiv ℝ U (RetainedSimplex.chart n m ((n+m : ℕ)+1)
            (Equiv.refl _) (x.val,z)) q)
        (∀ i : Fin (n : ℕ), MemLp (Xi i) 2 μ) ∧
        ∀ i j : Fin (n : ℕ), hessianMatrix V x.val i j =
          β.val*(InterpolationMatrix.penaltyHessian n θ ε x.val i j +
            GoodBlocks.conditionalHessian β s n m i j x +
            ConditionalForces.compensationQ β s n m i j x) -
          β.val^2*ProbabilityTheory.covariance (Xi i) (Xi j) μ := by
  intro p V
  obtain ⟨U, hU, hv, hx⟩ := PhysicalIdentity.proper_hessian_expansion β s n m θ ε
  refine ⟨U, hU, hv, fun x => ?_⟩
  intro μ q Xi
  obtain ⟨hXi, hH⟩ := hx x
  refine ⟨hXi, fun i j => ?_⟩
  have ha : 0 < (n : ℝ)^(-ε) := Real.rpow_pos_of_pos (by positivity) _
  have htwo := marginal_penalty_hessian_internal p n m θ ha true x i j
  have hone := marginal_penalty_hessian_internal p n m θ ha false x i j
  simp only [Bool.false_eq_true, ite_false, add_zero] at hone
  simp only [ite_true] at htwo
  simp only [← sub_eq_add_neg] at htwo hone
  change hessianMatrix V x.val i j = _
  dsimp only [p, ofLong] at htwo hone
  change _ = β.val*InterpolationMatrix.penaltyHessian n θ ε x.val i j + _ at htwo
  change _ = β.val*PhysicalCore.forcingHessian n θ ε x.val i j + _ at hone
  have he := hH i j
  change hessianMatrix V x.val i j = _ at htwo
  change _ = β.val*(PhysicalCore.forcingHessian n θ ε x.val i j +
    GoodBlocks.conditionalHessian β s n m i j x +
    ConditionalForces.compensationQ β s n m i j x) -
    β.val^2*ProbabilityTheory.covariance (Xi i) (Xi j) μ at he
  simp only [ofLong] at he
  rw [hone] at he
  rw [htwo]
  linarith only [he]

/-- See the proof of Lemma 6.5 in the paper: in the long regime the
two-sided physical marginal retains the volume-independent lower
curvature of the upper-penalized marginal. The inverse penalty adds a
convex active term. No exterior is fixed in this argument. -/
theorem long_twoSided_curvature_internal (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε : ℝ) (hε : 0 ≤ ε) :
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      β.val*∑ i, (θ.val ((n : ℝ)^(-ε)*x i) + θ.val ((n : ℝ)^(-ε)*(x i)⁻¹)) -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (x,z)).toReal)
    ContDiffOn ℝ ∞ V (AffineSimplex.chartDomain n ((n+m : ℕ)+1)) ∧
      ∀ x ∈ AffineSimplex.chartDomain n ((n+m : ℕ)+1),
        ∀ u : EuclideanSpace ℝ (Fin (n : ℕ)),
          (β.val*min 1 (s.val*(s.val+1))*(n : ℝ)^(-(s.val+2)*ε))*‖u‖^2 ≤
            fderiv ℝ (fderiv ℝ V) x u u := by
  intro V
  let V₀ := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
    β.val*∑ i, θ.val ((n : ℝ)^(-ε)*x i) -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (x,z)).toReal)
  let I := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) => ∑ i, θ.val ((n : ℝ)^(-ε)*(x i)⁻¹)
  obtain ⟨hV₀, hcurv⟩ := PhysicalIdentity.proper_scaled_curvature β s n m θ ε hε
  obtain ⟨hI, hIc⟩ := DecayShort.PhysicalFibres.inverse_retained_penalty n
    ((n+m : ℕ)+1) θ (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < n) (-ε))
  have he : V = fun x => V₀ x+β.val*I x := by
    funext x
    simp only [V, V₀, I, Finset.sum_add_distrib]
    ring
  rw [he]
  refine ⟨hV₀.add (contDiffOn_const.mul hI), fun x hx u => ?_⟩
  have hVx : ContDiffAt ℝ 2 V₀ x :=
    (hV₀.contDiffAt ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds hx)).of_le (by norm_num)
  have hIx : ContDiffAt ℝ 2 I x :=
    (hI.contDiffAt ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds hx)).of_le (by norm_num)
  rw [PhysicalCollision.internal_hessian_add hVx (contDiffAt_const.mul hIx),
    PhysicalCollision.internal_hessian_const_mul hIx]
  exact (hcurv x hx u).trans (le_add_of_nonneg_right
    (mul_nonneg β.property.le (Riesz1.fderiv_fderiv_nonneg_of_convexOn
      (AffineSimplex.isOpen_chartDomain _ _) (AffineSimplex.convex_chartDomain _ _)
      hIc (hI.of_le (by norm_num)) hx u)))

/-- See the proof of Lemma 6.5 in the paper: the actual long marginal
matrix is positive and uniformly coercive on the entire retained carrier.
The lower constant is independent of exterior volume and fibre length. -/
theorem long_twoSided_matrix_internal (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε : ℝ) (hε : 0 ≤ ε) :
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      β.val*∑ i, (θ.val ((n : ℝ)^(-ε)*x i) + θ.val ((n : ℝ)^(-ε)*(x i)⁻¹)) -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (x,z)).toReal)
    let a := β.val*min 1 (s.val*(s.val+1))*(n : ℝ)^(-(s.val+2)*ε)
    0 < a ∧ ∀ x : AffineSimplex.chartDomain n ((n+m : ℕ)+1),
      (hessianMatrix V x.val).PosSemidef ∧
      ∀ z : Fin (n : ℕ) → ℝ,
        a*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*hessianMatrix V x.val i j*z j := by
  intro V a
  have ha : 0 < a := by
    dsimp only [a]
    exact mul_pos (mul_pos β.property
      (lt_min zero_lt_one (mul_pos s.property.1 (by linarith [s.property.1]))))
      (Real.rpow_pos_of_pos (by positivity) _)
  obtain ⟨hsm, hc⟩ := long_twoSided_curvature_internal β s n m θ ε hε
  refine ⟨ha, fun x => ?_⟩
  have hx : ContDiffAt ℝ 2 V x.val :=
    (hsm.contDiffAt ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds x.property)).of_le
      (by norm_num)
  have hl (z : Fin (n : ℕ) → ℝ) :
      a*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*hessianMatrix V x.val i j*z j := by
    have hh := hc x.val x.property (WithLp.toLp 2 z)
    rw [← PhysicalEnergy.hessianMatrix_quadratic hx] at hh
    simpa only [EuclideanSpace.real_norm_sq_eq] using hh
  refine ⟨Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩, hl⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial]
    exact DecayShort.PhysicalComparison.hessianMatrix_symm hx j i
  · intro z
    have hh := (show 0 ≤ a*(∑ i, z i^2) by positivity).trans (hl z)
    simpa only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum, mul_assoc] using hh

/-- See the proof of Lemma 6.5 in the paper: an absolute envelope for
every entry of the actual long marginal Hessian. Covariance positivity
and the compensation signs bound its trace by the literal `W₀`. No
fixed-exterior Hessian replaces it. The factor `n^(-C₀)` is explicit. -/
theorem long_twoSided_envelope_internal (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε C₀ : ℝ) (hε : 0 ≤ ε) :
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      β.val*∑ i, (θ.val ((n : ℝ)^(-ε)*x i) + θ.val ((n : ℝ)^(-ε)*(x i)⁻¹)) -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (x,z)).toReal)
    ∀ (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1)) (i j : Fin (n : ℕ)),
      |hessianMatrix V x.val i j| ≤ β.val*(n : ℝ)*(n : ℝ)^(-C₀)*
        longEnvelope β s n m θ ε C₀ x := by
  intro V
  obtain ⟨U, _hU, _hv, hx⟩ := long_twoSided_hessian_internal β s n m θ ε
  have hp := (long_twoSided_matrix_internal β s n m θ ε hε).2
  intro x i j
  obtain ⟨hXi, heq⟩ := hx x
  let μ := ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x
  let q := WithLp.toLp 2 (ConditionalForces.compensationVector n m)
  let Xi := fun (k : Fin (n : ℕ)) (z : EuclideanSpace ℝ (Fin m)) => β.val⁻¹ *
    (fderiv ℝ U (RetainedSimplex.chart n m ((n+m : ℕ)+1) (Equiv.refl _) (x.val,z))
      (EuclideanSpace.single (k.castAdd m).castSucc 1) -
     fderiv ℝ U (RetainedSimplex.chart n m ((n+m : ℕ)+1) (Equiv.refl _) (x.val,z)) q)
  let f := ∑ k, |InterpolationMatrix.penaltyHessian n θ ε x.val k k|
  let P := ∑ k, ∑ l, GoodBlocks.conditionalHessian β s n m k l x
  let b := ∑ k, ConditionalForces.compensationB β s n m k x
  let c := ConditionalForces.compensationC β s n m x
  have hf : 0 ≤ f := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hP : 0 ≤ P := Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ =>
    GoodBlocks.conditionalHessian_nonneg β s n m k l x
  have hb : 0 ≤ b := Finset.sum_nonneg fun k _ => ConditionalForces.compensationB_nonneg β s n m k x
  have hc : 0 ≤ c := ConditionalForces.compensationC_nonneg β s n m x
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hd (k : Fin (n : ℕ)) : hessianMatrix V x.val k k ≤
      β.val*(|InterpolationMatrix.penaltyHessian n θ ε x.val k k| +
        (∑ l, GoodBlocks.conditionalHessian β s n m k l x) + c) := by
    have hcv : 0 ≤ ProbabilityTheory.covariance (Xi k) (Xi k) μ :=
      integral_nonneg fun z => mul_self_nonneg _
    have hPi := Finset.single_le_sum (fun l _ =>
      GoodBlocks.conditionalHessian_nonneg β s n m k l x) (Finset.mem_univ k)
    have hQ : ConditionalForces.compensationQ β s n m k k x ≤ c := by
      dsimp only [ConditionalForces.compensationQ, c]
      linarith [ConditionalForces.compensationB_nonneg β s n m k x]
    have hh := heq k k
    exact (hh.le.trans (sub_le_self _ (mul_nonneg (sq_nonneg _) hcv))).trans
      (mul_le_mul_of_nonneg_left (add_le_add
        (add_le_add (le_abs_self _) hPi) hQ) β.property.le)
  have ht : (hessianMatrix V x.val).trace ≤ β.val*(f+P+(n : ℝ)*c) := by
    apply (Finset.sum_le_sum (fun k _ => hd k)).trans_eq
    simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, f, P]
  have hbase : f+P+(n : ℝ)*c ≤ (n : ℝ)*(1+f+P+b+c) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) (add_nonneg hf hP),
      mul_nonneg (by positivity : (0 : ℝ) ≤ n) hb]
  have hscale : (n : ℝ)^(-C₀)*longEnvelope β s n m θ ε C₀ x = 1+f+P+b+c := by
    unfold longEnvelope
    rw [← mul_assoc, ← Real.rpow_add (by positivity : (0 : ℝ) < n),
      neg_add_cancel, Real.rpow_zero, one_mul]
  calc
    _ ≤ (hessianMatrix V x.val).trace := PhysicalFormDomain.Internal.entry_le_trace (hp x).1 i j
    _ ≤ β.val*(f+P+(n : ℝ)*c) := ht
    _ ≤ β.val*((n : ℝ)*(1+f+P+b+c)) := mul_le_mul_of_nonneg_left hbase β.property.le
    _ = β.val*(n : ℝ)*((n : ℝ)^(-C₀)*longEnvelope β s n m θ ε C₀ x) := by
      rw [hscale, mul_assoc]
    _ = _ := by ring

end MarginalHessian

section ConditionalEnergy

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- See Subsection 6.3 of the paper: finiteness of the nonnegative conditional
remainder proves integrability before its real value is used. -/
theorem conditional_envelope_real_internal (W : X → ℝ) (hW : Measurable W)
    (hW0 : ∀ x, 0 ≤ W x) (G : Set X)
    (he : (∫⁻ x in Gᶜ, ENNReal.ofReal (W x) ∂ν) ≠ (∞ : ℝ≥0∞)) :
    IntegrableOn W Gᶜ ν ∧ (∫ x in Gᶜ, W x ∂ν) =
      (∫⁻ x in Gᶜ, ENNReal.ofReal (W x) ∂ν).toReal := by
  exact ⟨(lintegral_ofReal_ne_top_iff_integrable
    hW.aestronglyMeasurable (ae_of_all _ hW0)).mp he,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hW0) hW.aestronglyMeasurable⟩

/-- See the proof of Lemma 6.5 in the paper: a conditional weighted
envelope controls the absolute first moment of a coefficient on the bad
set. The finite exceptional integral is used directly, without a square
root loss or a second moment assumption on that coefficient. -/
theorem conditional_dominated_integral_internal (W : X → ℝ) (hW : Measurable W)
    (hW0 : ∀ x, 0 ≤ W x) (G : Set X)
    (he : (∫⁻ x in Gᶜ, ENNReal.ofReal (W x) ∂ν) ≠ (∞ : ℝ≥0∞))
    (f : X → ℝ) (hf : AEStronglyMeasurable f (ν.restrict Gᶜ))
    (D : ℝ) (hbound : ∀ᵐ x ∂ν.restrict Gᶜ, |f x| ≤ D * W x) :
    IntegrableOn f Gᶜ ν ∧ (∫ x in Gᶜ, |f x| ∂ν) ≤
      D * (∫⁻ x in Gᶜ, ENNReal.ofReal (W x) ∂ν).toReal := by
  obtain ⟨hWi, hWe⟩ := conditional_envelope_real_internal W hW hW0 G he
  have hfi : IntegrableOn f Gᶜ ν :=
    (hWi.const_mul D).mono' hf (by simpa only [Real.norm_eq_abs] using hbound)
  refine ⟨hfi, ?_⟩
  calc
    _ ≤ ∫ x in Gᶜ, D * W x ∂ν := integral_mono_ae hfi.abs (hWi.const_mul D) hbound
    _ = _ := by rw [integral_const_mul, hWe]

/-- See the proof of Lemma 6.5 in the paper: conditional good/bad
assembly of a coefficient pairing. Its exceptional error is the weighted
conditional integral itself. In particular no unconditional exceptional
probability is substituted on an individual fibre. -/
theorem conditional_coefficient_pair_internal (n : ℕ+)
    (W : X → ℝ) (hW : Measurable W) (hW0 : ∀ x, 0 ≤ W x)
    (G : Set X) (hG : MeasurableSet G)
    (he : (∫⁻ x in Gᶜ, ENNReal.ofReal (W x) ∂ν) ≠ (∞ : ℝ≥0∞))
    (Y : X → ℝ) (hY : Measurable Y) (A D C₀ : ℝ) (hA : 0 ≤ A)
    (hgood : ∀ x ∈ G, |Y x| ≤ A)
    (hbad : ∀ᵐ x ∂ν.restrict Gᶜ, |Y x| ≤ D*(n : ℝ)^(-C₀)*W x)
    (φ η : Lp ℝ 2 ν) (Mφ Mη : ℝ) (hMφ : 0 ≤ Mφ) (hMη : 0 ≤ Mη)
    (hφ : ∀ᵐ x ∂ν, |φ x| ≤ Mφ) (hη : ∀ᵐ x ∂ν, |η x| ≤ Mη) :
    Integrable (fun x => φ x*η x*Y x) ν ∧
      |∫ x, φ x*η x*Y x ∂ν| ≤ A*‖φ‖*‖η‖ +
        D*(n : ℝ)^(-C₀)*(∫⁻ x in Gᶜ, ENNReal.ofReal (W x) ∂ν).toReal*Mφ*Mη := by
  have hφm := (Lp.stronglyMeasurable φ).measurable
  have hηm := (Lp.stronglyMeasurable η).measurable
  obtain ⟨hiG, hbG⟩ := PolynomialProfileTruncation.bounded_coefficient_pair hG hY hA
    hgood hφm hηm (Lp.memLp φ) (Lp.memLp η)
  have hbound : ∀ᵐ x ∂ν.restrict Gᶜ,
      |φ x*η x*Y x| ≤ (D*(n : ℝ)^(-C₀)*Mφ*Mη)*W x := by
    filter_upwards [hbad, ae_restrict_of_ae hφ, ae_restrict_of_ae hη] with x hy hf hg
    rw [abs_mul, abs_mul]
    calc
      _ ≤ (Mφ*Mη)*(D*(n : ℝ)^(-C₀)*W x) :=
        mul_le_mul (mul_le_mul hf hg (abs_nonneg _) hMφ) hy (abs_nonneg _)
          (mul_nonneg hMφ hMη)
      _ = _ := by ring
  obtain ⟨hiB, hbB⟩ := conditional_dominated_integral_internal W hW hW0 G he
    (fun x => φ x*η x*Y x) ((hφm.mul hηm).mul hY).aestronglyMeasurable _ hbound
  have hi : Integrable (fun x => φ x*η x*Y x) ν := by
    have hh := integrableOn_union.mpr ⟨hiG, hiB⟩
    simpa only [union_compl_self, integrableOn_univ] using hh
  have hnorm (f : Lp ℝ 2 ν) : Real.sqrt (∫ x, f x^2 ∂ν) = ‖f‖ := by
    simpa only [Lp.toLp_coeFn] using (PerturbationPairingAssembly.toLp_norm (Lp.memLp f)).symm
  rw [hnorm φ, hnorm η] at hbG
  refine ⟨hi, ?_⟩
  rw [← integral_add_compl hG hi]
  apply (abs_add_le _ _).trans
  apply (add_le_add hbG (abs_integral_le_integral_abs.trans hbB)).trans_eq
  ring

/-- See the proof of Lemma 6.5 in the paper: the normal correction's
physical energy is controlled by the conditional weighted remainder.
The factor `n^(-C₀)` stays explicit until all later summations. This
applies to the exact long or short envelope, with the physical Hessian
and its covariance subtraction retained in `H`. -/
theorem conditional_normal_energy_internal (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (n : ℕ+)
    (H : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (hHm : ∀ i j, Measurable (fun x => H x i j))
    (hH : ∀ᵐ x ∂ν, (H x).PosSemidef)
    (S : Q.1) (r : MatrixEnergy.Natural Q hQ H ⊤ hH)
    (hr : ∀ i, MatrixEnergy.tuple Q hQ H ⊤ hH r i = (n : ℝ)⁻¹ • S)
    (W : X → ℝ) (hW : Measurable W) (hW0 : ∀ x, 0 ≤ W x)
    (G : Set X) (hG : MeasurableSet G)
    (he : (∫⁻ x in Gᶜ, ENNReal.ofReal (W x) ∂ν) ≠ (∞ : ℝ≥0∞))
    (K B D C₀ : ℝ) (hK : 0 ≤ K)
    (hSB : ∀ᵐ x ∂ν, |S.val x| ≤ B)
    (hgood : ∀ᵐ x ∂ν.restrict G, (∑ i, ∑ j, H x i j) ≤ K)
    (hbad : ∀ᵐ x ∂ν.restrict Gᶜ,
      |∑ i, ∑ j, H x i j| ≤ D * (n : ℝ)^(-C₀) * W x) :
    MatrixEnergy.weakForm Q hQ H ⊤ hH r r ≤
      (n : ℝ)⁻¹ * Q.2 S S + (n : ℝ)⁻¹ ^ 2 *
        (K * ‖S.val‖ ^ 2 + B ^ 2 *
          (D * (n : ℝ)^(-C₀) * (∫⁻ x in Gᶜ, ENNReal.ofReal (W x) ∂ν).toReal)) := by
  have hm := Finset.measurable_sum Finset.univ fun i _ =>
    Finset.measurable_sum Finset.univ fun j _ => hHm i j
  obtain ⟨hi, hb⟩ := conditional_dominated_integral_internal W hW hW0 G he
    (fun x => ∑ i, ∑ j, H x i j) hm.aestronglyMeasurable _ hbad
  exact FixedLengthDecay.normal_energy_estimate_internal Q hQ n H hH S r hr G hG
    K B _ hK hSB hgood hi.abs hb

end ConditionalEnergy

section ConditionalComparison

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} [IsProbabilityMeasure ν]

/-- See the proof of Lemma 6.5 in the paper: an auxiliary matrix which
equals the physical Hessian on the fine set has an integrable defect, with
first moment given by the conditional envelope. This uses an absolute
envelope, rather than a squared-coefficient envelope. -/
theorem conditional_cutoff_moments_internal (n : ℕ+)
    (H M : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (hHm : ∀ i j, Measurable (fun x => H x i j))
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hMb : ∃ K : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ K)
    (W : X → ℝ) (hW : Measurable W) (hW0 : ∀ x, 0 ≤ W x)
    (G : Set X) (hG : MeasurableSet G)
    (he : (∫⁻ x in Gᶜ, ENNReal.ofReal (W x) ∂ν) ≠ (∞ : ℝ≥0∞))
    (heq : ∀ᵐ x ∂ν, x ∈ G → H x = M x)
    (D C₀ : ℝ)
    (hbad : ∀ᵐ x ∂ν.restrict Gᶜ, ∀ i j,
      |H x i j - M x i j| ≤ D * (n : ℝ)^(-C₀) * W x) :
    (∀ i j, Integrable (fun x => H x i j) ν) ∧
    (∀ i j, Integrable (fun x => H x i j-M x i j) ν) ∧
    (∀ i j, (∫ x, |H x i j-M x i j| ∂ν) ≤
      D * (n : ℝ)^(-C₀) * (∫⁻ x in Gᶜ, ENNReal.ofReal (W x) ∂ν).toReal) := by
  obtain ⟨K, hK⟩ := hMb
  have hMi (i j : Fin (n : ℕ)) : Integrable (fun x => M x i j) ν :=
    (integrable_const K).mono' (hMm i j).aestronglyMeasurable
      (hK.mono fun x hx => by simpa only [Real.norm_eq_abs] using hx i j)
  have hzero (i j : Fin (n : ℕ)) :
      (fun x => H x i j-M x i j) =ᵐ[ν.restrict G] 0 := by
    filter_upwards [ae_restrict_of_ae heq, ae_restrict_mem hG] with x hx hg
    simp only [hx hg, sub_self, Pi.zero_apply]
  have hBi (i j : Fin (n : ℕ)) := conditional_dominated_integral_internal W hW hW0 G he
    (fun x => H x i j-M x i j) ((hHm i j).sub (hMm i j)).aestronglyMeasurable _
    (hbad.mono fun _ hx => hx i j)
  have hDi (i j : Fin (n : ℕ)) : Integrable (fun x => H x i j-M x i j) ν := by
    have hgi : IntegrableOn (fun x => H x i j-M x i j) G ν :=
      (integrable_const (0 : ℝ)).congr (hzero i j).symm
    have hh := integrableOn_union.mpr ⟨hgi, (hBi i j).1⟩
    simpa only [union_compl_self, integrableOn_univ] using hh
  refine ⟨fun i j => ?_, hDi, fun i j => ?_⟩
  · exact ((hDi i j).add (hMi i j)).congr (ae_of_all _ (fun _ => sub_add_cancel _ _))
  · have hgood : (∫ x in G, |H x i j-M x i j| ∂ν) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hzero i j] with x hx
      change H x i j-M x i j = 0 at hx
      change |H x i j-M x i j| = 0
      rw [hx, abs_zero]
    rw [← integral_add_compl hG (hDi i j).abs, hgood, zero_add]
    exact (hBi i j).2

/-- See the proof of Lemma 6.5 in the paper: the actual tangent/normal
comparison from a conditional coefficient envelope. Natural-domain
representatives, both maximum-principle bounds, all pairing integrability,
and the normal energy bound are proved by the comparison API.
The exceptional remainder is left conditional and the envelope exponent
is not absorbed before the comparison. This internal implication can be
used on `retainedKernel` with either exact envelope. -/
theorem conditional_vector_comparison_internal
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q) (n : ℕ+)
    (H M : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (hHm : ∀ i j, Measurable (fun x => H x i j))
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hMb : ∃ K : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ K)
    (hH : ∀ᵐ x ∂ν, (H x).PosSemidef) (hM : ∀ᵐ x ∂ν, (M x).PosSemidef)
    (a d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hHa : ∀ᵐ x ∂ν, (∀ i j, H x i j = H x j i) ∧
      ∀ z : Fin (n : ℕ) → ℝ, a*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*H x i j*z j)
    (hMd : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
      ∀ z : Fin (n : ℕ) → ℝ, d*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*M x i j*z j)
    (W : X → ℝ) (hW : Measurable W) (hW0 : ∀ x, 0 ≤ W x)
    (G : Set X) (hG : MeasurableSet G)
    (he : (∫⁻ x in Gᶜ, ENNReal.ofReal (W x) ∂ν) ≠ (∞ : ℝ≥0∞))
    (heq : ∀ᵐ x ∂ν, x ∈ G → H x = M x)
    (D C₀ K : ℝ) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hdefect : ∀ᵐ x ∂ν.restrict Gᶜ, ∀ i j,
      |H x i j-M x i j| ≤ D*(n : ℝ)^(-C₀)*W x)
    (hgood : ∀ᵐ x ∂ν.restrict G, (∑ i, ∑ j, H x i j) ≤ K)
    (hbad : ∀ᵐ x ∂ν.restrict Gᶜ,
      |∑ i, ∑ j, H x i j| ≤ D*(n : ℝ)^(-C₀)*W x)
    (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν) (B : ℝ) (hB : 0 ≤ B)
    (hχ : ∀ᵐ x ∂ν, |χ x| ≤ B) (ψ v : Fin (n : ℕ) → Q.1)
    (hψ : WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ)))
      (fun i => if i = i₀ then χ else 0) ψ)
    (hv : WeightedWeakSolution Q M ⊤ (fun i => if i = i₀ then χ else 0) v) :
    let e := (∫⁻ x in Gᶜ, ENNReal.ofReal (W x) ∂ν).toReal
    let S : Q.1 := ∑ i, v i
    let V := d⁻¹*B
    let U := 2*V+a⁻¹*B
    let T := D*(n : ℝ)^(-C₀)*e
    let R := (n : ℝ)⁻¹*Q.2 S S + (n : ℝ)⁻¹^2*
      (K*‖S.val‖^2 + ((n : ℝ)*V)^2*T)
    ‖WithLp.toLp 2 (fun i => (ψ i).val-(v i).val)‖ ≤
      Real.sqrt ((2*(n : ℝ)^2*V*U*T+R)/a) + (n : ℝ)^(-(1 : ℝ)/2)*‖S.val‖ := by
  obtain ⟨hHi, hDi, hDb⟩ := conditional_cutoff_moments_internal n H M hHm hMm hMb
    W hW hW0 G hG he heq D C₀ hdefect
  have hm := Finset.measurable_sum Finset.univ fun i _ =>
    Finset.measurable_sum Finset.univ fun j _ => hHm i j
  obtain ⟨hi, hb⟩ := conditional_dominated_integral_internal W hW hW0 G he
    (fun x => ∑ i, ∑ j, H x i j) hm.aestronglyMeasurable _ hbad
  exact FixedLengthDecay.short_comparison_from_moments_internal Q hQ n H M hHm hMm hMb
    hH hM a d ha hd hHa hMd hHi hDi _ (by positivity) hDb G hG K _ hK
      (by positivity) hgood hi.abs hb i₀ χ B hB hχ ψ v hψ hv

end ConditionalComparison

section RetainedPhysicalEnergy

/-- See the proof of Lemma 6.5 in the paper: the actual long marginal
has a unique natural-energy tangent solution over its retained fibre law.
The maximum principle uses the same physical matrix and the uniform
curvature constant, independently of the fibre length and total volume. -/
theorem long_retained_tangent_solution_internal
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) (hε : 0 ≤ ε)
    (L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ)) :
    let ν := retainedKernel (ofLong β s) n m θ ε L
    let V := fun x : EuclideanSpace ℝ (Fin (n+1)) =>
      β.val*∑ i, (θ.val ((n+1 : ℝ)^(-ε)*x i) + θ.val ((n+1 : ℝ)^(-ε)*(x i)⁻¹)) -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity (ofLong β s) (n+1) m (Equiv.refl _) (x,z)).toReal)
    let H := fun x : AffineSimplex.chartDomain (n+1) ((n+1+m : ℕ)+1) => hessianMatrix V x.val
    let a := β.val*min 1 (s.val*(s.val+1))*(n+1 : ℝ)^(-(s.val+2)*ε)
    ∀ (Q : ScalarFormData ν) (_hQ : IsClosedScalarDirichletForm Q)
      (i₀ : Fin (n+1)) (χ : Lp ℝ 2 ν),
      (∃! ψ : Fin (n+1) → Q.1, WeightedWeakSolution Q H
        (zeroSumComponents (Fin (n+1))) (fun i => if i = i₀ then χ else 0) ψ) ∧
      ∀ (B : ℝ), 0 ≤ B → (∀ᵐ x ∂ν, |χ x| ≤ B) →
      ∀ ψ : Fin (n+1) → Q.1, WeightedWeakSolution Q H
        (zeroSumComponents (Fin (n+1))) (fun i => if i = i₀ then χ else 0) ψ →
        ∀ j, ∀ᵐ x ∂ν, |(ψ j).val x| ≤ a⁻¹*B := by
  intro ν V H a Q hQ i₀ χ
  have hmatrix : 0 < a ∧ ∀ x : AffineSimplex.chartDomain (n+1) ((n+1+m : ℕ)+1),
      (H x).PosSemidef ∧ ∀ z : Fin (n+1) → ℝ,
        a*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*H x i j*z j := by
    simpa only [H, V, a, Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using
      long_twoSided_matrix_internal β s n.succPNat m θ ε hε
  obtain ⟨ha, hd⟩ := hmatrix
  have hm (i j : Fin (n+1)) : Measurable (fun x => H x i j) :=
    (DifferentiatedPoisson.measurable_hessian_entries (V := V) i j).comp measurable_subtype_coe
  have hp : ∀ᵐ x ∂ν, (H x).PosSemidef := ae_of_all _ fun x => (hd x).1
  have hl : ∀ᵐ x ∂ν, ∀ z ∈ zeroSumComponents (Fin (n+1)),
      a*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*H x i j*z j :=
    ae_of_all _ fun x z _ => (hd x).2 z
  refine ⟨MatrixEnergy.weightedWeakSolution_existsUnique Q hQ H
    (zeroSumComponents (Fin (n+1))) hp a ha hl hm _, ?_⟩
  intro B hB hχ ψ hψ
  have hdata : ∀ᵐ x ∂ν, (∀ i j, H x i j = H x j i) ∧
      ∀ z : Fin (n+1) → ℝ, a*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*H x i j*z j := by
    apply ae_of_all
    intro x
    refine ⟨?_, (hd x).2⟩
    intro i j
    simpa only [Matrix.conjTranspose_apply, star_trivial] using
      (congrFun (congrFun (hd x).1.1 i) j).symm
  exact (FixedLengthDecay.point_source_ae_bound_internal Q hQ H hm a ha hdata
    (zeroSumComponents (Fin (n+1))) i₀ χ B hB hχ ψ hψ).2

/-- See the proof of Lemma 6.5 in the paper: the normal correction
energy on the actual long marginal fibre is bounded by its exact
conditional remainder. The off-event Hessian envelope is proved here. The good-event column estimate is the separate internal input `hgood`.
The residual coefficient keeps the explicit factor `n^(3-C₀)`. -/
theorem long_retained_normal_energy_internal
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (n m : ℕ)
    (θ : PhysicalCutoff) (ε C₀ η κ : ℝ) (hε : 0 ≤ ε)
    (L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ))
    (he : longRemainder β s n m θ ε C₀ η κ L ≠ (∞ : ℝ≥0∞)) :
    let ν := retainedKernel (ofLong β s) n m θ ε L
    let V := fun x : EuclideanSpace ℝ (Fin (n+1)) =>
      β.val*∑ i, (θ.val ((n+1 : ℝ)^(-ε)*x i) + θ.val ((n+1 : ℝ)^(-ε)*(x i)⁻¹)) -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity (ofLong β s) (n+1) m (Equiv.refl _) (x,z)).toReal)
    let H := fun x : AffineSimplex.chartDomain (n+1) ((n+1+m : ℕ)+1) => hessianMatrix V x.val
    ∀ (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
      (hH : ∀ᵐ x ∂ν, (H x).PosSemidef) (S : Q.1)
      (r : MatrixEnergy.Natural Q hQ H ⊤ hH),
      (∀ i, MatrixEnergy.tuple Q hQ H ⊤ hH r i = (n+1 : ℝ)⁻¹ • S) →
    ∀ (K B : ℝ), 0 ≤ K → (∀ᵐ x ∂ν, |S.val x| ≤ B) →
      (∀ᵐ x ∂ν.restrict (longFineEvent β s n.succPNat m η κ),
        (∑ i, ∑ j, H x i j) ≤ K) →
    MatrixEnergy.weakForm Q hQ H ⊤ hH r r ≤
      (n+1 : ℝ)⁻¹*Q.2 S S + (n+1 : ℝ)⁻¹^2*
        (K*‖S.val‖^2 + B^2*(β.val*(n+1 : ℝ)^3*(n+1 : ℝ)^(-C₀)*
          (longRemainder β s n m θ ε C₀ η κ L).toReal)) := by
  intro ν V H Q hQ hH S r hr K B hK hSB hgood
  have hm (i j : Fin (n+1)) : Measurable (fun x => H x i j) :=
    (DifferentiatedPoisson.measurable_hessian_entries (V := V) i j).comp measurable_subtype_coe
  have hW := measurable_longEnvelope β s n.succPNat m θ ε C₀
  have hW0 (x) : 0 ≤ longEnvelope β s n.succPNat m θ ε C₀ x :=
    (Real.rpow_nonneg (by positivity) C₀).trans
      (longEnvelope_lower β s n.succPNat m θ ε C₀ x)
  have hbad : ∀ᵐ x ∂ν.restrict (longFineEvent β s n.succPNat m η κ)ᶜ,
      |∑ i, ∑ j, H x i j| ≤ β.val*(n+1 : ℝ)^3*(n+1 : ℝ)^(-C₀)*
        longEnvelope β s n.succPNat m θ ε C₀ x := by
    apply ae_of_all
    intro x
    calc
      _ ≤ ∑ i, ∑ j, |H x i j| := by
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        exact Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (n+1), ∑ _j : Fin (n+1),
          β.val*(n+1 : ℝ)*(n+1 : ℝ)^(-C₀)*longEnvelope β s n.succPNat m θ ε C₀ x :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          simpa only [H, V, Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using
            long_twoSided_envelope_internal β s n.succPNat m θ ε C₀ hε x i j
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_add, Nat.cast_one]
        ring
  have hr' : ∀ i, MatrixEnergy.tuple Q hQ H ⊤ hH r i = (n.succPNat : ℝ)⁻¹ • S := by
    simpa only [Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using hr
  have hbad' : ∀ᵐ x ∂ν.restrict (longFineEvent β s n.succPNat m η κ)ᶜ,
      |∑ i, ∑ j, H x i j| ≤ β.val*(n+1 : ℝ)^3*(n.succPNat : ℝ)^(-C₀)*
        longEnvelope β s n.succPNat m θ ε C₀ x := by
    simpa only [Nat.succPNat_coe, Nat.cast_succ] using hbad
  simpa only [ν, longRemainder, retainedExceptionalMass,
    Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using
    conditional_normal_energy_internal Q hQ n.succPNat H hm hH S r hr' _ hW hW0 _
      (measurableSet_longFineEvent β s n.succPNat m η κ) he K B (β.val*(n+1 : ℝ)^3) C₀
      hK hSB hgood hbad'

end RetainedPhysicalEnergy

section ConditionalFibreSums

/-- See the proof of Lemma 6.5 in the paper: take the square root of
the conditional comparison, keeping its exceptional power separate from
the source norm. The remainder is a finite nonnegative real number. -/
theorem conditional_comparison_sqrt_internal (n : ℕ+) (loss P A T F B e E : ℝ)
    (hA : 0 ≤ A) (hT : 0 ≤ T) (hF : 0 ≤ F) (hB : 0 ≤ B)
    (he : 0 ≤ e) (hE : 0 ≤ E)
    (herror : E^2 ≤ A*(n : ℝ)^(2*loss-1)*F^2 + T*(n : ℝ)^(-2*P)*B^2*e) :
    E ≤ Real.sqrt A*(n : ℝ)^(loss-1/2)*F +
      Real.sqrt T*(n : ℝ)^(-P)*B*Real.sqrt e := by
  let u := Real.sqrt A*(n : ℝ)^(loss-1/2)*F
  let v := Real.sqrt T*(n : ℝ)^(-P)*B*Real.sqrt e
  have hu : 0 ≤ u := by dsimp only [u]; positivity
  have hv : 0 ≤ v := by dsimp only [v]; positivity
  have hp (t : ℝ) : ((n : ℝ)^t)^2 = (n : ℝ)^(2*t) := by
    rw [← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ n)]
    congr 1
    ring
  have hu2 : u^2 = A*(n : ℝ)^(2*loss-1)*F^2 := by
    dsimp only [u]
    rw [mul_pow, mul_pow, Real.sq_sqrt hA, hp]
    rw [show 2*(loss-1/2) = 2*loss-1 by ring]
  have hv2 : v^2 = T*(n : ℝ)^(-2*P)*B^2*e := by
    dsimp only [v]
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hT, Real.sq_sqrt he, hp]
    rw [show 2*(-P) = -2*P by ring]
  have hh : E^2 ≤ (u+v)^2 := by
    rw [← hu2, ← hv2] at herror
    nlinarith only [herror, mul_nonneg hu hv]
  exact (sq_le_sq₀ hE (add_nonneg hu hv)).mp hh

variable {H : Type*} [NormedAddCommGroup H]

/-- See the proof of Lemma 6.5 and equation (6.23) of the paper:
the two sums from a squared conditional vector comparison and auxiliary
sum bounds. The weights are arbitrary here so both literal regimes can
use the same calculation. -/
theorem conditional_fibre_sums_from_square_internal (n : ℕ+)
    (w : Fin (n : ℕ) → ℝ) (hw : ∀ j, 0 ≤ w j)
    (q W A D E T loss P F B e : ℝ)
    (hq : 0 ≤ q) (hW : 0 ≤ W) (hE : 0 ≤ E) (hT : 0 ≤ T)
    (hF : 0 ≤ F) (hB : 0 ≤ B) (he : 0 ≤ e) (hP : 1/2 ≤ P)
    (ψ v : Fin (n : ℕ) → H)
    (hweights : (∑ j, w j^2) ≤ W*(n : ℝ)^(1-2*q))
    (hweighted : (∑ j, w j*‖v j‖) ≤ A*(n : ℝ)^(loss-q)*F)
    (hsum : (∑ j, ‖v j‖) ≤ D*(n : ℝ)^loss*F)
    (herror : ‖WithLp.toLp 2 (fun j => ψ j-v j)‖^2 ≤
      E*(n : ℝ)^(2*loss-1)*F^2 + T*(n : ℝ)^(-2*P)*B^2*e) :
    (∑ j, w j*‖ψ j‖) ≤ (A+Real.sqrt W*Real.sqrt E)*(n : ℝ)^(loss-q)*F +
      Real.sqrt W*Real.sqrt T*B*Real.sqrt e ∧
    (∑ j, ‖ψ j‖) ≤ (D+Real.sqrt E)*(n : ℝ)^loss*F + Real.sqrt T*B*Real.sqrt e := by
  have hn : (0 : ℝ) < n := by positivity
  have herr := conditional_comparison_sqrt_internal n loss P E T F B e _
    hE hT hF hB he (norm_nonneg _) herror
  have herr' : ‖WithLp.toLp 2 (fun j => ψ j-v j)‖ ≤
      (Real.sqrt E*(n : ℝ)^loss)*(n : ℝ)^(-(1 : ℝ)/2)*F +
        (n : ℝ)^(-P)*(Real.sqrt T*B)*Real.sqrt e := by
    convert herr using 1
    rw [show loss-1/2 = loss+(-(1 : ℝ)/2) by ring, Real.rpow_add hn]
    ring
  have hweighted' : (∑ j, w j*‖v j‖) ≤ (A*(n : ℝ)^loss)*(n : ℝ)^(-q)*F := by
    convert hweighted using 1
    rw [show loss-q = loss+(-q) by ring, Real.rpow_add hn]
    ring
  obtain ⟨hx, hy⟩ := conditional_sums_internal n w hw q W (A*(n : ℝ)^loss)
    (D*(n : ℝ)^loss) (Real.sqrt E*(n : ℝ)^loss) F (Real.sqrt T*B) e P
    hW ψ v hweights hweighted' hsum herr'
  have hx' : (∑ j, w j*‖ψ j‖) ≤
      (A+Real.sqrt W*Real.sqrt E)*(n : ℝ)^(loss-q)*F +
        Real.sqrt W*(n : ℝ)^(1/2-q-P)*(Real.sqrt T*B)*Real.sqrt e := by
    convert hx using 1
    rw [show loss-q = loss+(-q) by ring, Real.rpow_add hn]
    ring
  have hy' : (∑ j, ‖ψ j‖) ≤ (D+Real.sqrt E)*(n : ℝ)^loss*F +
      (n : ℝ)^(1/2-P)*(Real.sqrt T*B)*Real.sqrt e := by
    convert hy using 1
    ring
  obtain ⟨h₁, h₂⟩ := conditional_sums_absorption_internal n q P (Real.sqrt W)
    ((A+Real.sqrt W*Real.sqrt E)*(n : ℝ)^(loss-q)*F)
    ((D+Real.sqrt E)*(n : ℝ)^loss*F) (Real.sqrt T*B) e _ _ hq hP
    (Real.sqrt_nonneg _) (by positivity) hx' hy'
  exact ⟨by simpa only [mul_assoc] using h₁, by simpa only [mul_assoc] using h₂⟩

/-- See the proof of Lemma 6.5 and equation (6.23) of the paper:
the long-regime fibre sums from the auxiliary profile and squared
conditional comparison, using the literal boundary weights. The
exceptional term is `B sqrt(e)` in both sums, without a volume factor. -/
theorem conditional_long_fibre_sums_internal (s : Riesz1.RieszExponent) (n : ℕ+)
    (i₀ : Fin (n : ℕ)) (hi₀ : |(i₀.val : ℝ)+1-(n : ℝ)/2| ≤ (n : ℝ)/4)
    (D E T loss P F B e : ℝ) (hD : 0 ≤ D) (hE : 0 ≤ E) (hT : 0 ≤ T)
    (hF : 0 ≤ F) (hB : 0 ≤ B) (he : 0 ≤ e) (hP : 1/2 ≤ P)
    (ψ v : Fin (n : ℕ) → H)
    (hvalue : ∀ j, ‖v j‖ ≤ D*(n : ℝ)^loss*
      (1+(Nat.dist j.val i₀.val : ℝ))^(s.val-2)*F)
    (hsum : (∑ j, ‖v j‖) ≤ D*(n : ℝ)^loss*F)
    (herror : ‖WithLp.toLp 2 (fun j => ψ j-v j)‖^2 ≤
      E*(n : ℝ)^(2*loss-1)*F^2 + T*(n : ℝ)^(-2*P)*B^2*e) :
    let K := 8^(2-s.val)*(2/(1-s.val/2))+8^(s.val/2)
    let W := 2/(1-s.val)
    (∑ j, InteractionDifferential.boundaryWeight s.val n j*‖ψ j‖) ≤
      (K*D+Real.sqrt W*Real.sqrt E)*(n : ℝ)^(loss-s.val/2)*F +
        Real.sqrt W*Real.sqrt T*B*Real.sqrt e ∧
    (∑ j, ‖ψ j‖) ≤ (D+Real.sqrt E)*(n : ℝ)^loss*F + Real.sqrt T*B*Real.sqrt e := by
  intro K W
  have hn : (0 : ℝ) < n := by positivity
  have hw := FixedLengthDecay.long_auxiliary_weighted_sum_internal s n i₀ hi₀
    (D*(n : ℝ)^loss) F (by positivity) hF (fun j => ‖v j‖)
    (fun _ => norm_nonneg _) hvalue hsum
  have hw' : (∑ j, InteractionDifferential.boundaryWeight s.val n j*‖v j‖) ≤
      (K*D)*(n : ℝ)^(loss-s.val/2)*F := by
    convert hw using 1
    rw [show loss-s.val/2 = loss+(-s.val/2) by ring, Real.rpow_add hn]
    ring
  apply conditional_fibre_sums_from_square_internal n
    (InteractionDifferential.boundaryWeight s.val n)
    (fun j => (InteractionDifferential.boundaryWeight_pos _ _ _).le)
    (s.val/2) W (K*D) D E T loss P F B e (by have := s.property.1; positivity)
    (by dsimp only [W]; have := s.property.2; positivity) hE hT hF hB he hP ψ v _ hw' hsum herror
  simpa only [W, show (1 : ℝ)-2*(s.val/2) = 1-s.val by ring] using
    FixedLengthDecay.long_boundary_square_sum s n

/-- See the proof of Lemma 6.5 and equation (6.23) of the paper:
the short-regime fibre sums from its auxiliary profile and squared
conditional comparison. Square summability of the actual boundary
weights gives the half-power gain. -/
theorem conditional_short_fibre_sums_internal (s : ℝ) (hs : 1 < s) (n : ℕ+)
    (i₀ : Fin (n : ℕ)) (hi₀ : |(i₀.val : ℝ)+1-(n : ℝ)/2| ≤ (n : ℝ)/4)
    (D E T loss P F B e : ℝ) (hD : 0 ≤ D) (hE : 0 ≤ E) (hT : 0 ≤ T)
    (hF : 0 ≤ F) (hB : 0 ≤ B) (he : 0 ≤ e) (hP : 1/2 ≤ P)
    (ψ v : Fin (n : ℕ) → H)
    (hvalue : ∀ j, ‖v j‖ ≤ D*(n : ℝ)^loss*
      (1+(Nat.dist j.val i₀.val : ℝ))^(-s)*F)
    (hsum : (∑ j, ‖v j‖) ≤ D*(n : ℝ)^loss*F)
    (herror : ‖WithLp.toLp 2 (fun j => ψ j-v j)‖^2 ≤
      E*(n : ℝ)^(2*loss-1)*F^2 + T*(n : ℝ)^(-2*P)*B^2*e) :
    let K := 4*8^s+Real.sqrt 8
    let W := 2*∑' k : ℕ, (1+(k : ℝ))^(-(2*s-1))
    (∑ j, InteractionDifferential.boundaryWeight s n j*‖ψ j‖) ≤
      (K*D+Real.sqrt W*Real.sqrt E)*(n : ℝ)^(loss-1/2)*F +
        Real.sqrt W*Real.sqrt T*B*Real.sqrt e ∧
    (∑ j, ‖ψ j‖) ≤ (D+Real.sqrt E)*(n : ℝ)^loss*F + Real.sqrt T*B*Real.sqrt e := by
  intro K W
  have hn : (0 : ℝ) < n := by positivity
  have hw := FixedLengthDecay.short_auxiliary_weighted_sum_internal s hs n i₀ hi₀
    (D*(n : ℝ)^loss) F (by positivity) hF (fun j => ‖v j‖)
    (fun _ => norm_nonneg _) hvalue hsum
  have hw' : (∑ j, InteractionDifferential.boundaryWeight s n j*‖v j‖) ≤
      (K*D)*(n : ℝ)^(loss-1/2)*F := by
    convert hw using 1
    rw [show loss-1/2 = loss+(-(1 : ℝ)/2) by ring, Real.rpow_add hn]
    ring
  have hW : 0 ≤ W := by
    dsimp only [W]
    exact mul_nonneg (by norm_num) (tsum_nonneg (fun _ => Real.rpow_nonneg (by positivity) _))
  apply conditional_fibre_sums_from_square_internal n
    (InteractionDifferential.boundaryWeight s n)
    (fun j => (InteractionDifferential.boundaryWeight_pos _ _ _).le)
    (1/2) W (K*D) D E T loss P F B e (by norm_num) hW
    hE hT hF hB he hP ψ v _ hw' hsum herror
  simpa only [W, show (1 : ℝ)-2*(1/2) = 0 by ring, Real.rpow_zero, mul_one] using
    FixedLengthDecay.short_boundary_square_sum s hs n

end ConditionalFibreSums

end Riesz2.LengthAveragingFibres
