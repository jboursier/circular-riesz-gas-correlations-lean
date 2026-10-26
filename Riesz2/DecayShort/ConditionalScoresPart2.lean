/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.ConditionalScores
public import Riesz2.ToMathlib.CutoffApproximation
public import Riesz1.ToMathlib.WeightedSobolev.LocalIntegrationByParts
public import Riesz1.ToMathlib.WeightedSobolev.BoundedGradientCutoff

/-!
# Collision approximation for physical conditional scores

Further fixed-fibre inputs for Subsection 4.4. The energy is the
ambient energy, including its specified normal derivatives. All
integrability statements are at every retained point of the physical domain.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators ContDiff

namespace Riesz2.DecayShort.ConditionalScores

section DensityCutoff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Internal collision approximation criterion for Subsection 4.4.
The cutoff error is controlled by the actual logarithmic density gradient.
The measure need not be finite or absolutely continuous. -/
private theorem internal_density_level_weightedH1
    (μ : Measure E) (V : Set E) {w F : E → ℝ}
    (hw : ContDiff ℝ ∞ w)
    (hFsm : ContDiffOn ℝ ∞ F {x | 0 < w x})
    (hpos : ∀ᵐ x ∂μ, 0 < w x)
    (hF : MemLp F 2 μ) (hG : MemLp (gradient F) 2 μ)
    (hS : MemLp (fun x => (F x / w x) • gradient w x) 2 μ) :
    Riesz1.WeightedSobolev.IsWeightedH1 μ V F (gradient F) := by
  let U : Set E := {x | 0 < w x}
  have hU : IsOpen U := isOpen_lt continuous_const hw.continuous
  let a : ℕ → ℝ := fun k => k + 1
  let θ : ℕ → E → ℝ := fun k x =>
    1 - CutoffApproximation.scalarCutoff (a k * w x)
  let φ : ℕ → E → ℝ := fun k x => θ k x * F x
  let S : E → E := fun x => (F x / w x) • gradient w x
  obtain ⟨C, hC, hCb⟩ := CutoffApproximation.scalarCutoff_derivative_bound 1
  have ha (k : ℕ) : 0 < a k := by dsimp [a]; positivity
  have hθ (k : ℕ) : ContDiff ℝ ∞ (θ k) :=
    contDiff_const.sub (CutoffApproximation.scalarCutoff_contDiff.comp
      (contDiff_const.mul hw))
  have hθs (k : ℕ) : tsupport (θ k) ⊆ U := by
    have hs : tsupport (θ k) ⊆ {x | 1 ≤ a k * w x} := by
      apply closure_minimal _ (isClosed_le continuous_const (continuous_const.mul hw.continuous))
      intro x hx
      by_contra hn
      change ¬ 1 ≤ a k * w x at hn
      have he := CutoffApproximation.scalarCutoff_eq_one (le_of_lt (lt_of_not_ge hn))
      exact hx (by dsimp [θ]; rw [he]; ring)
    intro x hx
    have hx' := hs hx
    change 1 ≤ a k * w x at hx'
    change 0 < w x
    nlinarith [ha k]
  have hφ (k : ℕ) : ContDiff ℝ ∞ (φ k) :=
    Riesz1.WeightedSobolev.contDiff_cutoff_mul hU (hθ k) (hθs k) hFsm
  have hθb (k : ℕ) (x : E) : 0 ≤ θ k x ∧ θ k x ≤ 1 := by
    dsimp [θ]
    constructor <;> linarith [CutoffApproximation.scalarCutoff_nonneg (a k * w x),
      CutoffApproximation.scalarCutoff_le_one (a k * w x)]
  have hj (k : ℕ) (x : E) (hx : 0 < w x) :
      gradient (φ k) x = θ k x • gradient F x -
        (a k * deriv CutoffApproximation.scalarCutoff (a k * w x) * w x) • S x := by
    have hwd := ((hw.differentiable (by simp)) x).hasFDerivAt
    have hcd := ((CutoffApproximation.scalarCutoff_contDiff.differentiable (by simp))
      (a k * w x)).hasDerivAt.comp_hasFDerivAt x (hwd.const_mul (a k))
    have hfd := (hFsm.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have hd := ((hasFDerivAt_const (1 : ℝ) x).sub hcd).mul hfd.hasFDerivAt
    have he : gradient (φ k) x = θ k x • gradient F x -
        (F x * (deriv CutoffApproximation.scalarCutoff (a k * w x) * a k)) • gradient w x := by
      change HasFDerivAt (φ k) _ x at hd
      unfold gradient
      rw [hd.fderiv]
      simp only [map_add, map_smul, smul_smul, zero_sub, map_neg, smul_neg]
      exact (sub_eq_add_neg _ _).symm
    dsimp only [S]
    rw [he]
    simp only [smul_smul]
    have hc : a k * deriv CutoffApproximation.scalarCutoff (a k * w x) * w x *
        (F x / w x) = F x * (deriv CutoffApproximation.scalarCutoff (a k * w x) * a k) := by
      field_simp
    rw [hc]
  have hα (k : ℕ) (x : E) (hx : 0 < w x) :
      |a k * deriv CutoffApproximation.scalarCutoff (a k * w x) * w x| ≤ 2 * C := by
    by_cases hh : a k * w x ≤ 2
    · have hb : |deriv CutoffApproximation.scalarCutoff (a k * w x)| ≤ C := by
        simpa only [iteratedDeriv_one] using hCb (a k * w x)
      rw [abs_mul, abs_mul, abs_of_pos (ha k), abs_of_pos hx]
      nlinarith [mul_le_mul_of_nonneg_left hb (mul_nonneg (ha k).le hx.le),
        abs_nonneg (deriv CutoffApproximation.scalarCutoff (a k * w x))]
    · have he : deriv CutoffApproximation.scalarCutoff (a k * w x) = 0 := by
        simpa only [iteratedDeriv_one] using
          CutoffApproximation.scalarCutoff_iteratedDeriv_eq_zero 1 (by norm_num)
            (Or.inr (lt_of_not_ge hh))
      rw [he, mul_zero, zero_mul, abs_zero]
      positivity
  have hφb (k : ℕ) : ∀ᵐ x ∂μ, ‖φ k x‖ ≤ ‖F x‖ := by
    exact ae_of_all _ fun x => by
      rw [show φ k x = θ k x * F x from rfl, norm_mul,
        Real.norm_of_nonneg (hθb k x).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hθb k x).2
  have hgb (k : ℕ) : ∀ᵐ x ∂μ,
      ‖gradient (φ k) x‖ ≤ ‖gradient F x‖ + (2 * C) * ‖S x‖ := by
    filter_upwards [hpos] with x hx
    rw [hj k x hx]
    apply (norm_sub_le _ _).trans
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (hθb k x).1, Real.norm_eq_abs]
    exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) (hθb k x).2)
      (mul_le_mul_of_nonneg_right (hα k x hx) (norm_nonneg _))
  have hm (k : ℕ) : MemLp (φ k) 2 μ :=
    hF.of_le_mul (c := 1) (hφ k).continuous.aestronglyMeasurable
      (by simpa only [one_mul] using hφb k)
  have hb : MemLp (fun x => ‖gradient F x‖ + (2 * C) * ‖S x‖) 2 μ :=
    hG.norm.add (hS.norm.const_mul (2 * C))
  have hgm (k : ℕ) : MemLp (gradient (φ k)) 2 μ := by
    apply hb.of_le_mul (c := 1)
      (Riesz1.WeightedSobolev.continuous_gradient_of_contDiff (hφ k)).aestronglyMeasurable
    filter_upwards [hgb k] with x hx
    simpa only [one_mul, Real.norm_of_nonneg (by positivity :
      0 ≤ ‖gradient F x‖ + (2 * C) * ‖S x‖)] using hx
  have hev (x : E) (hx : 0 < w x) : ∀ᶠ k : ℕ in atTop, 2 < a k * w x := by
    have ht : Tendsto (fun k : ℕ => a k * w x) atTop atTop :=
      ((tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop).atTop_add (tendsto_const_nhds (x := (1 : ℝ)))).atTop_mul_const hx
    exact ht.eventually_gt_atTop 2
  have hvlim : ∀ᵐ x ∂μ, Tendsto (fun k => φ k x) atTop (𝓝 (F x)) := by
    filter_upwards [hpos] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [hev x hx] with k hk
    simp only [φ, θ, CutoffApproximation.scalarCutoff_eq_zero hk.le, sub_zero, one_mul]
  have hglim : ∀ᵐ x ∂μ, Tendsto (fun k => gradient (φ k) x)
      atTop (𝓝 (gradient F x)) := by
    filter_upwards [hpos] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [hev x hx] with k hk
    rw [hj k x hx]
    have he : deriv CutoffApproximation.scalarCutoff (a k * w x) = 0 := by
      simpa only [iteratedDeriv_one] using
        CutoffApproximation.scalarCutoff_iteratedDeriv_eq_zero 1 (by norm_num) (Or.inr hk)
    simp only [θ, CutoffApproximation.scalarCutoff_eq_zero hk.le, sub_zero, one_smul,
      he, mul_zero, zero_mul, zero_smul]
  refine ⟨hF, hG, φ, fun k => ⟨univ, isOpen_univ, subset_univ _, (hφ k).contDiffOn⟩, ?_, ?_⟩
  · exact (Riesz1.WeightedSobolev.tendsto_toLp_iff_lintegral_sq φ hm F hF).mp
      (Riesz1.WeightedSobolev.tendsto_toLp_of_dominated hm hF hF.norm hφb
        (ae_of_all _ fun _ => le_rfl) hvlim)
  · exact (Riesz1.WeightedSobolev.tendsto_toLp_iff_lintegral_sq _ hgm _ hG).mp
      (Riesz1.WeightedSobolev.tendsto_toLp_of_dominated hgm hG hb hgb
        (ae_of_all _ fun x => le_add_of_nonneg_right (by positivity)) hglim)


end DensityCutoff

set_option backward.isDefEq.respectTransparency false in
/-- Internal polynomial domination criterion for Subsection 4.4.
Every inverse coordinate moment is available for the actual physical fibre,
so a bound at the smallest full gap gives L² membership for any finite
dimensional tensor or vector field. -/
theorem internal_memLp_of_min_gap_bound {V : Type*} [NormedAddCommGroup V]
    (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (f : AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ i, x.val i) → V)
    (hf : AEStronglyMeasurable f (PhysicalFibres.measure p n m hn σ x))
    (K r : ℝ) (hK : 0 ≤ K) (hr : 0 < r)
    (hb : ∀ z, ∀ δ : ℝ, 0 < δ →
      (∀ a, δ ≤ (PhysicalFibres.configuration n m σ x z).val a) →
      ‖f z‖ ≤ K * δ ^ (-r)) :
    MemLp f 2 (PhysicalFibres.measure p n m hn σ x) := by
  classical
  let c := fun z => (PhysicalFibres.configuration n m σ x z).val
  let μ := PhysicalFibres.measure p n m hn σ x
  have hs := PhysicalFibres.configuration_mem_simplex n m σ x
  have hi (a : Fin (n + m + 1)) : MemLp (fun z => (c z a) ^ (-r)) 2 μ := by
    apply (memLp_two_iff_integrable_sq
      ((((EuclideanSpace.proj (𝕜 := ℝ) a).continuous.comp
        (PhysicalFibres.continuous_configuration n m σ x).subtype_val).measurable.pow_const _).aestronglyMeasurable)).mpr
    have ht := PhysicalFibres.integrable_coordinate_inverse_power p n m hn σ x a (2 * r)
      (by positivity)
    apply ht.congr
    apply ae_of_all
    intro z
    change (c z a) ^ (-(2 * r)) = ((c z a) ^ (-r)) ^ 2
    rw [← Real.rpow_natCast, ← Real.rpow_mul ((hs z).1 a).le]
    congr 1
    push_cast
    ring
  have hmajor := (memLp_finsetSum Finset.univ (fun a _ => hi a)).const_mul K
  apply hmajor.mono' hf
  apply ae_of_all
  intro z
  obtain ⟨a, _, ha⟩ := Finset.exists_min_image Finset.univ (fun a => c z a)
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin (n + m + 1))).Nonempty)
  exact (hb z (c z a) ((hs z).1 a) (fun b => ha b (Finset.mem_univ b))).trans
    (mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun b _ => Real.rpow_nonneg ((hs z).1 b).le _)
        (Finset.mem_univ a)) hK)

/-- The existing retained chart, at a fixed retained point, is affine in
the exterior free coordinates. This supplies its exact derivative rather
than changing the exterior metric. -/
theorem internal_exterior_chart_affine (n m : ℕ)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    (x : EuclideanSpace ℝ (Fin n)) (L : ℝ) :
    ∃ C : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin (n + m + 1)),
      ∀ z, RetainedSimplex.chart n m L σ (x,z) =
        C z + RetainedSimplex.chart n m L σ (x,0) := by
  have : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :=
    Prod.continuousSMul
  let e := (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ).toContinuousLinearEquiv.toContinuousLinearMap
  let J := (RetainedSimplex.join n m).toContinuousLinearEquiv.toContinuousLinearMap
  let T := (AffineSimplex.tangentMap (n + m)).toContinuousLinearMap
  refine ⟨e.comp (T.comp (J.comp (ContinuousLinearMap.inr ℝ _ _))), fun z => ?_⟩
  have hj : RetainedSimplex.join n m (x,z) =
      RetainedSimplex.join n m (0,z) + RetainedSimplex.join n m (x,0) := by
    rw [← map_add]
    congr 1
    simp
  unfold RetainedSimplex.chart
  rw [AffineSimplex.chart_eq_tangentMap_add (n + m) L (RetainedSimplex.join n m (x,z)),
    AffineSimplex.chart_eq_tangentMap_add (n + m) L (RetainedSimplex.join n m (x,0)), hj]
  simp only [map_add, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  change e (T (J (0,z))) + e (T (J (x,0))) + e (AffineSimplex.chart (n + m) L 0) =
    e (T (J (0,z))) + (e (T (J (x,0))) + e (AffineSimplex.chart (n + m) L 0))
  exact add_assoc _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The physical domination criterion in the ambient exterior chart. -/
theorem internal_chart_memLp_of_min_gap_bound {V : Type*} [NormedAddCommGroup V]
    (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (f : EuclideanSpace ℝ (Fin m) → V)
    (hf : AEStronglyMeasurable f (ProperMarginalChart.conditionalMeasure p n m hn σ x))
    (K r : ℝ) (hK : 0 ≤ K) (hr : 0 < r)
    (hb : ∀ z ∈ AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ i, x.val i),
      ∀ δ : ℝ, 0 < δ →
      (∀ a, δ ≤ RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ (x.val,z) a) →
      ‖f z‖ ≤ K * δ ^ (-r)) :
    MemLp f 2 (ProperMarginalChart.conditionalMeasure p n m hn σ x) := by
  have he := PhysicalFibres.map_measure p n m hn σ x
  rw [← he, (MeasurableEmbedding.subtype_coe
    (AffineSimplex.isOpen_chartDomain _ _).measurableSet).memLp_map_measure_iff]
  apply internal_memLp_of_min_gap_bound p n m hn σ x (f ∘ Subtype.val)
    (by
      rw [← he] at hf
      exact hf.comp_measurable measurable_subtype_coe) K r hK hr
  intro z δ hδ hgap
  exact hb z.val z.property δ hδ hgap

set_option backward.isDefEq.respectTransparency false in
/-- Internal chain-rule bounds for a directional ambient score in an affine
chart. The chart derivative and the ambient normal direction are explicit. -/
theorem internal_affine_score_gradient_bound {E D : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
    (C : D →L[ℝ] E) (b v : E) (U : E → ℝ) (z : D)
    (hU : ContDiffAt ℝ 2 U (C z + b)) :
    ‖gradient (fun y => fderiv ℝ U (C y + b) v) z‖ ≤
      ‖fderiv ℝ (fderiv ℝ U) (C z + b)‖ * ‖C‖ * ‖v‖ := by
  have hd := ((hU.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt
  have hc := C.hasFDerivAt.add_const b (x := z)
  have hj := (hd.comp z hc).clm_apply (hasFDerivAt_const v z)
  change HasFDerivAt (fun y => fderiv ℝ U (C y + b) v) _ z at hj
  change ‖(InnerProductSpace.toDual ℝ D).symm
    (fderiv ℝ (fun y => fderiv ℝ U (C y + b) v) z)‖ ≤ _
  rw [LinearIsometryEquiv.norm_map, hj.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro t
  simp only [add_apply, ContinuousLinearMap.comp_apply, zero_apply, map_zero,
    zero_add, ContinuousLinearMap.flip_apply]
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ U) (C z + b) (C t)‖ * ‖v‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖fderiv ℝ (fderiv ℝ U) (C z + b)‖ * (‖C‖ * ‖t‖)) * ‖v‖ := by
      gcongr
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_left (C.le_opNorm t) (norm_nonneg _))
    _ = _ := by ring

set_option backward.isDefEq.respectTransparency false in
/-- Collision approximation input for Subsection 4.4.
Every ambient directional score of the energy belongs to the actual
weighted H¹ completion on every physical exterior fibre, with its classical
exterior gradient. This includes the individual scores and the uniform
compensation direction without changing their ambient extension. -/
theorem physical_scores_weightedH1 (p : Parameters) (n m : ℕ) (hn : 1 ≤ n) :
    ∃ U : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain (n + m).succPNat) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
          y ∈ gapAmbientDomain (n + m).succPNat},
        U y.val = p.val.1 * physicalAmbientGapEnergy p (n + m).succPNat y) ∧
      ∀ (σ : Equiv.Perm (Fin (n + m + 1)))
        (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
        (v : EuclideanSpace ℝ (Fin (n + m + 1))),
        let F := fun z => p.val.1⁻¹ * fderiv ℝ U
          (RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ (x.val,z)) v
        Riesz1.WeightedSobolev.IsWeightedH1
          (ProperMarginalChart.conditionalMeasure p n m hn σ x)
          (AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ i, x.val i)) F (gradient F) := by
  classical
  obtain ⟨U, hU, hv, hT⟩ := MarginalHessian.physical_energy_tensors p (n + m).succPNat
  change (EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ) at U
  simp only [Nat.succPNat_coe] at hU hv hT
  obtain ⟨B, hB, hb⟩ := hT 1
  obtain ⟨D, hD, hd⟩ := hT 2
  have hβ : 0 < p.val.1 := p.property.1
  refine ⟨U, hU, hv, fun σ x v => ?_⟩
  let L : ℝ := ((n + m : ℕ) + 1)
  let Ω := AffineSimplex.chartDomain m (L - ∑ i, x.val i)
  let c := fun z => RetainedSimplex.chart n m L σ (x.val,z)
  let μ := ProperMarginalChart.conditionalMeasure p n m hn σ x
  let F := fun z => p.val.1⁻¹ * fderiv ℝ U (c z) v
  let w := fun z => (ProperMarginalChart.chartDensity p n m σ (x.val,z)).toReal
  obtain ⟨C, hc⟩ := internal_exterior_chart_affine n m σ x.val L
  have hca : c = fun z => C z + c 0 := funext hc
  have hcs : ContDiff ℝ ∞ c := by rw [hca]; exact C.contDiff.add contDiff_const
  have hcd (z) : HasFDerivAt c C z := by rw [hca]; exact C.hasFDerivAt.add_const _
  have hs (z) (hz : z ∈ Ω) : WithLp.ofLp (c z) ∈ Riesz1.gapSimplex (n + m).succPNat :=
    PhysicalFibres.configuration_mem_simplex n m σ x ⟨z,hz⟩
  have hΩ : IsOpen Ω := AffineSimplex.isOpen_chartDomain _ _
  have ha (z) (hz : z ∈ Ω) : c z ∈ gapAmbientDomain (n + m).succPNat :=
    PhysicalEnergy.simplex_subset_ambient _ _ (hs z hz)
  have hUs (z) (hz : z ∈ Ω) : ContDiffAt ℝ ∞ U (c z) :=
    hU.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain _).mem_nhds (ha z hz))
  have hFs : ContDiffOn ℝ ∞ F Ω := by
    rw [hΩ.contDiffOn_iff]
    intro z hz
    exact contDiffAt_const.mul
      (((hUs z hz).fderiv_right (m := ∞) (by simp)).comp z hcs.contDiffAt |>.clm_apply contDiffAt_const)
  have hwp (z) (hz : z ∈ Ω) : w z = Real.exp (-U (c z)) := by
    have hz' : (x.val,z) ∈ RetainedSimplex.domain n m L :=
      (Set.ext_iff.mp (RetainedSimplex.fibre_domain n m L x.property) z).mpr hz
    have hzS := (RetainedSimplex.chart_mem_simplex n m L σ (x.val,z)).mpr hz'
    dsimp only [L] at hz' hzS
    simp only [w, ProperMarginalChart.chartDensity, indicator_of_mem hz',
      ProperMarginalChart.density, dite_eq_left hzS, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
    rw [hv ⟨c z, ha z hz⟩]
    congr 1
    ring
  have hwiff (z) : 0 < w z ↔ z ∈ Ω := by
    constructor
    · intro hz
      by_contra hnz
      have hz' : (x.val,z) ∉ RetainedSimplex.domain n m L := by
        intro hh
        exact hnz ((Set.ext_iff.mp (RetainedSimplex.fibre_domain n m L x.property) z).mp hh)
      have he : w z = 0 := by
        dsimp only [L] at hz'
        simp only [w, ProperMarginalChart.chartDensity, indicator_of_notMem hz', ENNReal.toReal_zero]
      linarith
    · intro hz
      rw [hwp z hz]
      exact Real.exp_pos _
  have hww : {z | 0 < w z} = Ω := Set.ext hwiff
  have hws : ContDiff ℝ ∞ w := by
    have := (MarginalHessian.physical_chart_density_smooth_compact p n m hn σ).1
    exact this.comp (contDiff_const.prodMk contDiff_id)
  have hμ : ∀ᵐ z ∂μ, z ∈ Ω := ConditionalEnergyMoments.physical_conditional_support p n m hn σ x
  have hmeas : Measurable F := (measurable_fderiv_apply_const ℝ U v).comp hcs.continuous.measurable |>.const_mul _
  have hgmeas : Measurable (gradient F) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin m))).symm.continuous.measurable.comp
      (measurable_fderiv ℝ F)
  have hfirst (z) (hz : z ∈ Ω) (δ : ℝ) (hδ : 0 < δ) (hgap : ∀ a, δ ≤ c z a) :
      ‖fderiv ℝ U (c z)‖ ≤ B * δ ^ (-p.val.2 - 1) := by
    simpa only [PNat.val_ofNat, Nat.cast_one, norm_iteratedFDeriv_one] using hb (c z) (hs z hz) δ hδ hgap
  have hsecond (z) (hz : z ∈ Ω) (δ : ℝ) (hδ : 0 < δ) (hgap : ∀ a, δ ≤ c z a) :
      ‖fderiv ℝ (fderiv ℝ U) (c z)‖ ≤ D * δ ^ (-p.val.2 - 2) := by
    rw [← norm_iteratedFDeriv_one (fderiv ℝ U), norm_iteratedFDeriv_fderiv]
    simpa only [PNat.val_ofNat, Nat.cast_ofNat] using hd (c z) (hs z hz) δ hδ hgap
  have hFbound (z) (hz : z ∈ Ω) (δ : ℝ) (hδ : 0 < δ) (hgap : ∀ a, δ ≤ c z a) :
      ‖F z‖ ≤ (p.val.1⁻¹ * B * ‖v‖) * δ ^ (-(p.val.2 + 1)) := by
    dsimp only [F]
    rw [norm_mul, Real.norm_of_nonneg (inv_nonneg.mpr p.property.1.le)]
    have ht := (ContinuousLinearMap.le_opNorm (fderiv ℝ U (c z)) v).trans
      (mul_le_mul_of_nonneg_right (hfirst z hz δ hδ hgap) (norm_nonneg _))
    calc
      _ ≤ p.val.1⁻¹ * (B * δ ^ (-p.val.2 - 1) * ‖v‖) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      _ = _ := by rw [show -p.val.2 - 1 = -(p.val.2 + 1) by ring]; ring
  have hgval (z) (hz : z ∈ Ω) :
      gradient F z = p.val.1⁻¹ • gradient (fun y => fderiv ℝ U (c y) v) z := by
    have hd := (((hUs z hz).fderiv_right (m := 1) (by simp)).differentiableAt
      (by simp)).hasFDerivAt
    have hh := (hd.comp z (hcd z)).clm_apply (hasFDerivAt_const v z)
    change HasFDerivAt (fun y => fderiv ℝ U (c y) v) _ z at hh
    unfold gradient
    rw [(hh.const_mul p.val.1⁻¹).fderiv, hh.fderiv, map_smul]
  have hgBound (z) (hz : z ∈ Ω) (δ : ℝ) (hδ : 0 < δ) (hgap : ∀ a, δ ≤ c z a) :
      ‖gradient F z‖ ≤ (p.val.1⁻¹ * D * ‖C‖ * ‖v‖) * δ ^ (-(p.val.2 + 2)) := by
    rw [hgval z hz, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr p.property.1.le)]
    have hh := internal_affine_score_gradient_bound C (c 0) v U z
      (by rw [← hc]; exact (hUs z hz).of_le (by norm_num))
    have heq : (fun y => fderiv ℝ U (C y + c 0) v) =
        (fun y => fderiv ℝ U (c y) v) := funext fun y => by rw [← hc y]
    rw [heq, ← hc z] at hh
    calc
      _ ≤ p.val.1⁻¹ * (‖fderiv ℝ (fderiv ℝ U) (c z)‖ * ‖C‖ * ‖v‖) := by gcongr
      _ ≤ p.val.1⁻¹ * ((D * δ ^ (-p.val.2 - 2)) * ‖C‖ * ‖v‖) := by
        gcongr
        exact hsecond z hz δ hδ hgap
      _ = _ := by rw [show -p.val.2 - 2 = -(p.val.2 + 2) by ring]; ring
  have hFM : MemLp F 2 μ := internal_chart_memLp_of_min_gap_bound p n m hn σ x F
    hmeas.aestronglyMeasurable _ _ (by positivity) (by linarith [p.property.2.1]) hFbound
  have hGM : MemLp (gradient F) 2 μ := internal_chart_memLp_of_min_gap_bound p n m hn σ x _
    hgmeas.aestronglyMeasurable _ _ (by positivity) (by linarith [p.property.2.1]) hgBound
  have hwgrad (z) (hz : z ∈ Ω) :
      gradient w z = -w z • (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin m))).symm
        ((fderiv ℝ U (c z)).comp C) := by
    have he : w =ᶠ[𝓝 z] fun y => Real.exp (-U (c y)) := by
      filter_upwards [hΩ.mem_nhds hz] with y hy
      exact hwp y hy
    have hj := (((hUs z hz).differentiableAt (by simp)).hasFDerivAt.comp z (hcd z)).neg.exp
    change HasFDerivAt (fun y => Real.exp (-U (c y))) _ z at hj
    unfold gradient
    rw [he.fderiv_eq, hj.fderiv]
    simp only [map_smul, map_neg, Function.comp_apply, Pi.neg_apply]
    rw [← hwp z hz]
    simp only [neg_smul, smul_neg]
  let S := fun z => (F z / w z) • gradient w z
  have hSm : Measurable S :=
    (hmeas.div hws.continuous.measurable).smul
      ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin m))).symm.continuous.measurable.comp
        (measurable_fderiv ℝ w))
  have hSM : MemLp S 2 μ := by
    apply internal_chart_memLp_of_min_gap_bound p n m hn σ x S hSm.aestronglyMeasurable
      (p.val.1⁻¹ * B ^ 2 * ‖v‖ * ‖C‖) (2 * (p.val.2 + 1))
      (by positivity) (by linarith [p.property.2.1])
    intro z hz δ hδ hgap
    have hwp0 : 0 < w z := (hwiff z).mpr hz
    have hSv : S z = -F z • (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin m))).symm
        ((fderiv ℝ U (c z)).comp C) := by
      dsimp only [S]
      rw [hwgrad z hz, smul_smul]
      congr 1
      field_simp [hwp0.ne']
    rw [hSv, norm_smul, norm_neg, LinearIsometryEquiv.norm_map]
    have hcomp : ‖(fderiv ℝ U (c z)).comp C‖ ≤ ‖fderiv ℝ U (c z)‖ * ‖C‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    calc
      _ ≤ ((p.val.1⁻¹ * B * ‖v‖) * δ ^ (-(p.val.2 + 1))) *
          ((B * δ ^ (-p.val.2 - 1)) * ‖C‖) := by
        apply mul_le_mul (hFbound z hz δ hδ hgap)
          (hcomp.trans (mul_le_mul_of_nonneg_right (hfirst z hz δ hδ hgap) (norm_nonneg _)))
          (norm_nonneg _) (by positivity)
      _ = _ := by
        rw [show -p.val.2 - 1 = -(p.val.2 + 1) by ring]
        rw [show -(2 * (p.val.2 + 1)) = -(p.val.2 + 1) + -(p.val.2 + 1) by ring,
          Real.rpow_add hδ]
        ring
  apply internal_density_level_weightedH1 μ Ω hws
    (by rwa [hww]) _ hFM hGM hSM
  filter_upwards [hμ] with z hz
  exact (hwiff z).mpr hz

end Riesz2.DecayShort.ConditionalScores
