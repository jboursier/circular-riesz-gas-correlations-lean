/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.MarginalHessianPart4
public import Riesz2.ToMathlib.DominatedDensityForce
public import Riesz1.ToMathlib.LogConcave.PrekopaFrontier
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Proper marginal integration and compensated calculus

See Appendix A of the paper: all-order integration of the physical supported
density, the smooth marginal potential, and its compensated first and second
derivative formulas, including active penalties. The fixed exterior chart is
the existing centred hyperplane chart. Translation identifies its normalized
law with the physical conditional. Forces belong to L² and the energy
Hessian is integrable, so the separated covariance formula is well defined.
-/

public section
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace Riesz2
universe u v
variable {X : Type u} {Y : Type v}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (μ : Measure Y) [IsFiniteMeasureOnCompacts μ]

omit [NormedSpace ℝ X] [NormedSpace ℝ Y] [SecondCountableTopology Y] in
private theorem compact_fibre_bound {F : Type*} [NormedAddCommGroup F]
    {f : X × Y → F} (hf : Continuous f) (hs : HasCompactSupport f) :
    ∃ b : Y → ℝ, Integrable b μ ∧ ∀ x z, ‖f (x,z)‖ ≤ b z := by
  classical
  let K := Prod.snd '' tsupport f
  have hK : IsCompact K := hs.isCompact.image continuous_snd
  obtain ⟨C, hC⟩ := (hs.isCompact_range hf).bddAbove_image continuous_norm.continuousOn
  refine ⟨K.indicator (fun _ => max C 0), ?_, fun x z => ?_⟩
  · exact (integrable_indicator_iff hK.measurableSet).mpr
      (integrableOn_const (hK.measure_lt_top (μ := μ)).ne)
  · by_cases hz : z ∈ K
    · rw [indicator_of_mem hz]
      exact (hC ⟨f (x,z), ⟨(x,z), rfl⟩, rfl⟩).trans (le_max_left _ _)
    · rw [indicator_of_notMem hz, show f (x,z) = 0 from
        Function.notMem_support.mp (fun h => hz ⟨(x,z), subset_closure h, rfl⟩), norm_zero]

set_option backward.isDefEq.respectTransparency false in
private theorem compact_integral_smooth_nat (a : ℕ) :
    ∀ (F : Type u) [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (f : X × Y → F), ContDiff ℝ ∞ f → HasCompactSupport f →
      ContDiff ℝ a (fun x => ∫ z, f (x,z) ∂μ) := by
  induction a with
  | zero =>
    intro F _ _ _ f hf hs
    obtain ⟨b, hb, hbound⟩ := compact_fibre_bound μ hf.continuous hs
    change ContDiff ℝ 0 _
    rw [contDiff_zero]
    apply continuous_iff_continuousAt.mpr
    intro x
    apply continuousAt_of_dominated
      (Eventually.of_forall (fun y => (hf.continuous.comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable))
      (Eventually.of_forall (fun y => Eventually.of_forall (hbound y))) hb
      (Eventually.of_forall (fun z => (hf.continuous.comp
        (continuous_id.prodMk continuous_const)).continuousAt))
  | succ a ih =>
    intro F _ _ _ f hf hs
    let S := (ContinuousLinearMap.compL ℝ X (X × Y) F).flip
      (ContinuousLinearMap.inl ℝ X Y)
    let df : X × Y → X →L[ℝ] F := fun q => S (fderiv ℝ f q)
    have hdf : ContDiff ℝ ∞ df := S.contDiff.comp (hf.fderiv_right (by simp))
    have hsdf : HasCompactSupport df := (hs.fderiv ℝ).comp_left S.map_zero
    obtain ⟨b, hb, hbound⟩ := compact_fibre_bound μ hdf.continuous hsdf
    obtain ⟨b0, hb0, hbound0⟩ := compact_fibre_bound μ hf.continuous hs
    have hi (x : X) : Integrable (fun z => f (x,z)) μ :=
      hb0.mono' ((hf.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
        (Eventually.of_forall (hbound0 x))
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun x => ∫ z, df (x,z) ∂μ, ih _ df hdf hsdf, fun x => ?_⟩
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := Set.univ)
      (bound := b) Filter.univ_mem
      (Eventually.of_forall (fun y => (hi y).aestronglyMeasurable)) (hi x)
      ((hdf.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall (fun z y _ => hbound y z)) hb
      (Eventually.of_forall (fun z y _ => ?_))
    have hp : HasFDerivAt (fun t : X => (t,z)) (ContinuousLinearMap.inl ℝ X Y) y := by
      convert (hasFDerivAt_id y).prodMk (hasFDerivAt_const z y) using 1 <;> rfl
    exact (hf.differentiable (by simp) (y,z)).hasFDerivAt.comp y hp


set_option backward.isDefEq.respectTransparency false in
private theorem compact_partial_domination {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {f : X × Y → F}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (U : Set X) (hU : IsOpen U) :
    let S := (ContinuousLinearMap.compL ℝ X (X × Y) F).flip
      (ContinuousLinearMap.inl ℝ X Y)
    let df := fun q => S (fderiv ℝ f q)
    ContDiff ℝ ∞ df ∧ HasCompactSupport df ∧
      DominatedFibre.DominatedFDerivOn μ U (fun x z => f (x,z))
        (fun x z => df (x,z)) := by
  dsimp only
  let S := (ContinuousLinearMap.compL ℝ X (X × Y) F).flip
    (ContinuousLinearMap.inl ℝ X Y)
  let df : X × Y → X →L[ℝ] F := fun q => S (fderiv ℝ f q)
  have hd : ContDiff ℝ ∞ df := S.contDiff.comp (hf.fderiv_right (by simp))
  have hc : HasCompactSupport df := (hs.fderiv ℝ).comp_left S.map_zero
  obtain ⟨b, hb, hbound⟩ := compact_fibre_bound μ hd.continuous hc
  obtain ⟨b0, hb0, hbound0⟩ := compact_fibre_bound μ hf.continuous hs
  refine ⟨hd, hc, ?_⟩
  constructor
  · intro x _
    exact hb0.mono' ((hf.continuous.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall (hbound0 x))
  · intro x _
    exact (hd.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · intro x hx
    refine ⟨U, hU.mem_nhds hx, Set.Subset.rfl, b, hb,
      Eventually.of_forall (fun z y _ => hbound y z),
      Eventually.of_forall (fun z y _ => ?_)⟩
    have hp : HasFDerivAt (fun t : X => (t,z)) (ContinuousLinearMap.inl ℝ X Y) y := by
      convert (hasFDerivAt_id y).prodMk (hasFDerivAt_const z y) using 1 <;> rfl
    exact (hf.differentiable (by simp) (y,z)).hasFDerivAt.comp y hp

private theorem compact_partial_domination_actual {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {f : X × Y → F}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (U : Set X) (hU : IsOpen U) :
    let df := fun q : X × Y => fderiv ℝ (fun t => f (t,q.2)) q.1
    ContDiff ℝ ∞ df ∧ HasCompactSupport df ∧
      DominatedFibre.DominatedFDerivOn μ U (fun x z => f (x,z))
        (fun x z => df (x,z)) := by
  have he : (fun q : X × Y => fderiv ℝ (fun t => f (t,q.2)) q.1) =
      fun q => ((ContinuousLinearMap.compL ℝ X (X × Y) F).flip
        (ContinuousLinearMap.inl ℝ X Y)) (fderiv ℝ f q) := by
    funext q
    have hp : HasFDerivAt (fun t : X => (t,q.2)) (ContinuousLinearMap.inl ℝ X Y) q.1 := by
      convert (hasFDerivAt_id q.1).prodMk (hasFDerivAt_const q.2 q.1) using 1 <;> rfl
    exact ((hf.differentiable (by simp) q).hasFDerivAt.comp q.1 hp).fderiv
  exact (congrArg (fun g : X × Y → X →L[ℝ] F =>
    ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      DominatedFibre.DominatedFDerivOn μ U (fun x z => f (x,z))
        (fun x z => g (x,z))) he).mpr (compact_partial_domination μ hf hs U hU)

set_option backward.isDefEq.respectTransparency false in
private theorem internal_gibbs_gradient_apply {A E : Type*} [MeasurableSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure A} {B : Set E}
    {w : E → A → ℝ} {dw : E → A → E →L[ℝ] ℝ}
    (h : DominatedFibre.DominatedFDerivOn μ B w dw) {x : E} (hx : x ∈ B)
    (hn : ∀ z, 0 ≤ w x z) (hp : 0 < ∫ z, w x z ∂μ)
    (S : A → E →L[ℝ] ℝ) (hforce : ∀ᵐ z ∂μ, dw x z = -w x z • S z) (u : E) :
    let ρ := AffineFibre.normalizedMeasure μ (fun z => ENNReal.ofReal (w x z))
      (by rw [← ofReal_integral_eq_lintegral_ofReal (h.integrable x hx) (Eventually.of_forall hn)]
          exact ENNReal.ofReal_ne_zero_iff.mpr hp)
      (by rw [← ofReal_integral_eq_lintegral_ofReal (h.integrable x hx) (Eventually.of_forall hn)]
          exact ENNReal.ofReal_ne_top)
    fderiv ℝ (fun t => -Real.log (∫ z, w t z ∂μ)) x u = ∫ z, S z u ∂ρ := by
  dsimp only
  have he : (∫ z, dw x z u ∂μ) = -(∫ z, w x z * S z u ∂μ) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [hforce] with z hz
    simp only [hz, smul_apply, smul_eq_mul, neg_mul]
  rw [(DominatedFibre.hasFDerivAt_neg_log_integral h hx hp).fderiv,
    DominatedFibre.integral_normalizedMeasure (h.integrable x hx) hn hp]
  simp only [smul_apply, smul_eq_mul,
    ContinuousLinearMap.integral_apply (h.integrable_derivative hx), he]
  ring

private theorem internal_indicator_gibbs_derivatives
    {E A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [MeasurableSpace A]
    {μ : Measure A} {Q : Set (E × A)} (hQ : IsOpen Q)
    {w H : E × A → ℝ} (hH : ContDiffOn ℝ ∞ H Q)
    (hw : w = Q.indicator (fun q => Real.exp (-H q))) (x : E)
    (hae : ∀ᵐ z ∂μ, (x,z) ∉ frontier Q) :
    ∀ᵐ z ∂μ,
      fderiv ℝ (fun t => w (t,z)) x =
        -w (x,z) • fderiv ℝ (fun t => H (t,z)) x ∧
      fderiv ℝ (fderiv ℝ (fun t => w (t,z))) x =
        w (x,z) • ((fderiv ℝ (fun t => H (t,z)) x).smulRight
          (fderiv ℝ (fun t => H (t,z)) x) -
            fderiv ℝ (fderiv ℝ (fun t => H (t,z))) x) := by
  classical
  filter_upwards [hae] with z hz
  have hp : Continuous (fun t : E => (t,z)) := continuous_id.prodMk continuous_const
  by_cases hq : (x,z) ∈ Q
  · have hs : ContDiffAt ℝ ∞ (fun t : E => H (t,z)) x :=
      (hH.contDiffAt (hQ.mem_nhds hq)).comp x (contDiff_id.prodMk contDiff_const).contDiffAt
    have he : (fun t : E => w (t,z)) =ᶠ[𝓝 x] fun t => Real.exp (-H (t,z)) := by
      filter_upwards [hp.continuousAt.preimage_mem_nhds (hQ.mem_nhds hq)] with t ht
      rw [hw, indicator_of_mem (show (t,z) ∈ Q from ht)]
    have hval : w (x,z) = Real.exp (-H (x,z)) := he.eq_of_nhds
    have hfirst := DominatedFibre.hasFDerivAt_exp_neg
      (hs.differentiableAt (by norm_num)).hasFDerivAt
    refine ⟨?_, ?_⟩
    · rw [he.fderiv_eq, hfirst.fderiv, hval]
    · have hegrad : fderiv ℝ (fun t : E => Real.exp (-H (t,z))) =ᶠ[𝓝 x]
          fun t => -Real.exp (-H (t,z)) • fderiv ℝ (fun r => H (r,z)) t := by
        filter_upwards [(hs.of_le (show (2 : ℕ∞ω) ≤ ∞ by simp)).eventually (by norm_num)] with t ht
        exact (DominatedFibre.hasFDerivAt_exp_neg
          (ht.differentiableAt (by norm_num)).hasFDerivAt).fderiv
      rw [he.fderiv.fderiv_eq, hegrad.fderiv_eq, hval]
      exact (DominatedFibre.hasFDerivAt_exp_neg_derivative
        (hs.differentiableAt (by norm_num)).hasFDerivAt
        ((hs.fderiv_right (m := 1) (by norm_num)).differentiableAt
          (by norm_num)).hasFDerivAt).fderiv
  · have hcl : (x,z) ∉ closure Q := by
      intro h
      exact hz ⟨h, by simpa only [hQ.interior_eq] using hq⟩
    have he : (fun t : E => w (t,z)) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hp.continuousAt.preimage_mem_nhds
        (isClosed_closure.isOpen_compl.mem_nhds hcl)] with t ht
      rw [hw, indicator_of_notMem (fun h => ht (subset_closure h))]
    rw [he.eq_of_nhds, he.fderiv_eq, he.fderiv.fderiv_eq]
    constructor
    · ext u
      simp
    · ext u v
      simp

namespace MarginalHessian


/-- See Appendix A of the paper: The existing centred exterior chart, inserted after retained gaps. -/
def compensatedChart (n m : ℕ) (L : ℝ) (σ : Equiv.Perm (Fin (n + m + 1)))
    (q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin (n + m + 1)) :=
  RetainedSimplex.assemble n m σ q.1
    (AffineSimplex.centredChart m (L - ∑ i, q.1 i) (AffineSimplex.tangentEquiv m q.2))

private theorem centred_eq_shifted (m : ℕ) (L : ℝ) (z : EuclideanSpace ℝ (Fin m)) :
    AffineSimplex.centredChart m L (AffineSimplex.tangentEquiv m z) =
      AffineSimplex.chart m L (z + AffineSimplex.coordinates m (AffineSimplex.centre m L)) := by
  calc
    _ = AffineSimplex.chart m L (AffineSimplex.coordinates m
        (AffineSimplex.centredChart m L (AffineSimplex.tangentEquiv m z))) :=
      (AffineSimplex.chart_coordinates m L (AffineSimplex.sum_centredChart m L _)).symm
    _ = _ := by
      congr 1
      ext i
      simp [AffineSimplex.coordinates, AffineSimplex.centredChart,
        AffineSimplex.tangentEquiv, AffineSimplex.tangentMap, AffineSimplex.chart_castSucc]

private theorem smooth_shift (n m : ℕ) (L : ℝ) :
    ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) =>
      AffineSimplex.coordinates m (AffineSimplex.centre m (L - ∑ i, x i))) := by
  have he : (fun x : EuclideanSpace ℝ (Fin n) =>
      AffineSimplex.coordinates m (AffineSimplex.centre m (L - ∑ i, x i))) =
      fun x => ((L - ∑ i, x i) / (m + 1)) •
        (WithLp.toLp 2 (fun _ : Fin m => (1 : ℝ))) := by
    funext x
    ext i
    simp [AffineSimplex.coordinates, AffineSimplex.centre]
  rw [he]
  have hsum : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, x i) := by
    convert (∑ i : Fin n, EuclideanSpace.proj (𝕜 := ℝ) i).contDiff (n := ∞) using 1
    ext x
    simp
  exact ((contDiff_const.sub hsum).div_const _).smul contDiff_const

/-- See Appendix A of the paper: The deleted-coordinate fibre chart is translated by the free coordinates
of its barycentre. This is a homeomorphism on the entire product space. -/
def compensatedShift (n m : ℕ) (L : ℝ) :
    (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) ≃ₜ
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) where
  toFun q := (q.1, q.2 + AffineSimplex.coordinates m
    (AffineSimplex.centre m (L - ∑ i, q.1 i)))
  invFun q := (q.1, q.2 - AffineSimplex.coordinates m
    (AffineSimplex.centre m (L - ∑ i, q.1 i)))
  left_inv q := by simp
  right_inv q := by simp
  continuous_toFun := continuous_fst.prodMk (continuous_snd.add
    ((smooth_shift n m L).continuous.comp continuous_fst))
  continuous_invFun := continuous_fst.prodMk (continuous_snd.sub
    ((smooth_shift n m L).continuous.comp continuous_fst))

/-- See Appendix A of the paper: Equality with the existing centred hyperplane chart, with a translation
Jacobian independent of the retained point. -/
theorem compensatedChart_eq_shift (n m : ℕ) (L : ℝ)
    (σ : Equiv.Perm (Fin (n + m + 1))) (q : EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin m)) :
    compensatedChart n m L σ q =
      RetainedSimplex.chart n m L σ (compensatedShift n m L q) := by
  unfold compensatedChart
  rw [centred_eq_shifted, RetainedSimplex.assemble_chart]
  rfl

/-- See Appendix A of the paper: Smoothness and compact support in the chart with uniform exterior compensation. -/
theorem compensated_density_smooth_compact (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) :
    ContDiff ℝ ∞ (fun q => (ProperMarginalChart.chartDensity p n m σ
        (compensatedShift n m ((n + m : ℕ) + 1) q)).toReal) ∧
      HasCompactSupport (fun q => (ProperMarginalChart.chartDensity p n m σ
        (compensatedShift n m ((n + m : ℕ) + 1) q)).toReal) := by
  obtain ⟨hf, hs⟩ := physical_chart_density_smooth_compact p n m hn σ
  refine ⟨hf.comp ?_, hs.comp_homeomorph _⟩
  exact contDiff_fst.prodMk (contDiff_snd.add
    ((smooth_shift n m _).comp contDiff_fst))

/-- See Appendix A of the paper: The active direction with its mass distributed equally over all exterior labels. -/
def compensatedDirection (n m : ℕ) (σ : Equiv.Perm (Fin (n + m + 1))) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n + m + 1)) := by
  have : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin (m + 1))) :=
    Prod.continuousSMul
  exact (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((RetainedSimplex.join n (m + 1)).toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).prod
        (((-(m + 1 : ℝ)⁻¹) • ∑ i : Fin n, EuclideanSpace.proj (𝕜 := ℝ) i).smulRight
          (WithLp.toLp 2 (fun _ : Fin (m + 1) => (1 : ℝ))))))

/-- See Appendix A of the paper: retained components of a compensated displacement. -/
theorem compensatedDirection_retained (n m : ℕ)
    (σ : Equiv.Perm (Fin (n + m + 1))) (u : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    compensatedDirection n m σ u (σ (i.castAdd m).castSucc) = u i := by
  rw [show (i.castAdd m).castSucc = i.castAdd (m + 1) from rfl]
  simp [compensatedDirection, RetainedSimplex.join,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

/-- See Appendix A of the paper: every exterior component receives the same
compensation, the negative retained mass divided by the number of exterior gaps. -/
theorem compensatedDirection_exterior (n m : ℕ)
    (σ : Equiv.Perm (Fin (n + m + 1))) (u : EuclideanSpace ℝ (Fin n)) (i : Fin (m + 1)) :
    compensatedDirection n m σ u (σ (i.natAdd n)) = -(∑ j, u j) / (m + 1 : ℝ) := by
  simp [compensatedDirection, RetainedSimplex.join,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft', div_eq_mul_inv]
  ring

/-- See Appendix A of the paper: The entire active dependence of the centred chart is affine, with the
uniformly compensated direction as its linear part. -/
theorem compensatedChart_affine (n m : ℕ) (L : ℝ)
    (σ : Equiv.Perm (Fin (n + m + 1))) (x : EuclideanSpace ℝ (Fin n))
    (z : EuclideanSpace ℝ (Fin m)) :
    compensatedChart n m L σ (x,z) =
      compensatedDirection n m σ x + compensatedChart n m L σ (0,z) := by
  have : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin (m + 1))) :=
    Prod.continuousSMul
  let e := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ
  let j := (RetainedSimplex.join n (m + 1)).toContinuousLinearEquiv
  change e (j (x, _)) = e (j (x, _)) + e (j (0, _))
  rw [← map_add, ← map_add]
  congr 1
  congr 1
  apply Prod.ext
  · simp
  · ext i
    simp only [Prod.snd_add, AffineSimplex.centredChart, PiLp.add_apply]
    simp [AffineSimplex.centre, div_eq_mul_inv]
    ring

/-- See Appendix A of the paper: The compensated chart differentiates in the uniformly compensated direction. -/
theorem compensatedChart_hasFDerivAt (n m : ℕ) (L : ℝ)
    (σ : Equiv.Perm (Fin (n + m + 1))) (x : EuclideanSpace ℝ (Fin n))
    (z : EuclideanSpace ℝ (Fin m)) :
    HasFDerivAt (fun t => compensatedChart n m L σ (t,z))
      (compensatedDirection n m σ) x := by
  have he : (fun t => compensatedChart n m L σ (t,z)) =
      fun t => compensatedDirection n m σ t + compensatedChart n m L σ (0,z) :=
    funext (fun t => compensatedChart_affine n m L σ t z)
  rw [he]
  exact (compensatedDirection n m σ).hasFDerivAt.add_const _

/-- See Appendix A of the paper: The fixed-fibre translation has Jacobian one and preserves the actual
physical marginal normalizer, including point fibres. -/
theorem compensated_fibre_mass (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin (n + m + 1))) (x : EuclideanSpace ℝ (Fin n)) :
    AffineFibre.fibreMass volume (fun q => ProperMarginalChart.chartDensity p n m σ
      (compensatedShift n m ((n + m : ℕ) + 1) q)) x =
        AffineFibre.fibreMass volume (ProperMarginalChart.chartDensity p n m σ) x := by
  exact lintegral_add_right_eq_self
    (fun z => ProperMarginalChart.chartDensity p n m σ (x,z))
    (AffineSimplex.coordinates m (AffineSimplex.centre m (((n + m : ℕ) + 1) - ∑ i, x i)))

/-- See Appendix A of the paper: The physical conditional is the image of its fixed compensated-fibre
realization by the barycentre translation. -/
theorem compensated_conditional_map (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    let c := AffineSimplex.coordinates m
      (AffineSimplex.centre m (((n + m : ℕ) + 1) - ∑ i, x.val i))
    (AffineFibre.normalizedMeasure volume
      (fun z => ProperMarginalChart.chartDensity p n m σ (x.val,z + c))
      (by rw [lintegral_add_right_eq_self (fun z => ProperMarginalChart.chartDensity p n m σ (x.val,z)) c]; exact (ProperMarginalChart.fibre_mass p n m hn σ x.property).1)
      (by rw [lintegral_add_right_eq_self (fun z => ProperMarginalChart.chartDensity p n m σ (x.val,z)) c]; exact (ProperMarginalChart.fibre_mass p n m hn σ x.property).2)).map
        (fun z => z + c) = ProperMarginalChart.conditionalMeasure p n m hn σ x := by
  intro c
  have hm := AffineFibre.normalizedMeasure_map volume
    (MeasurableEquiv.addRight c).measurableEmbedding
    ((ProperMarginalChart.measurable_chartDensity p n m σ).comp measurable_prodMk_left)
    (show (∫⁻ z, ProperMarginalChart.chartDensity p n m σ (x.val,z+c)) ≠ 0 by
      rw [lintegral_add_right_eq_self (fun z => ProperMarginalChart.chartDensity p n m σ (x.val,z)) c]
      exact (ProperMarginalChart.fibre_mass p n m hn σ x.property).1)
    (show (∫⁻ z, ProperMarginalChart.chartDensity p n m σ (x.val,z+c)) ≠ ⊤ by
      rw [lintegral_add_right_eq_self (fun z => ProperMarginalChart.chartDensity p n m σ (x.val,z)) c]
      exact (ProperMarginalChart.fibre_mass p n m hn σ x.property).2)
  have hmap : (volume : Measure (EuclideanSpace ℝ (Fin m))).map (MeasurableEquiv.addRight c) = volume :=
    (measurePreserving_add_right volume c).map_eq
  simp only [hmap] at hm
  exact hm.symm

/-- See Appendix A of the paper: Smoothness of the existing full chart after the fixed-fibre translation. -/
theorem compensatedChart_smooth (n m : ℕ) (L : ℝ)
    (σ : Equiv.Perm (Fin (n + m + 1))) : ContDiff ℝ ∞ (compensatedChart n m L σ) := by
  have : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :=
    Prod.continuousSMul
  have hA : ContDiff ℝ ∞ (AffineSimplex.chart (n + m) L) := by
    have he : AffineSimplex.chart (n + m) L = fun x =>
        (AffineSimplex.tangentMap (n + m)).toContinuousLinearMap x +
          AffineSimplex.chart (n + m) L 0 :=
      funext (AffineSimplex.chart_eq_tangentMap_add (n + m) L)
    rw [he]
    exact (AffineSimplex.tangentMap (n + m)).toContinuousLinearMap.contDiff.add contDiff_const
  have hC : ContDiff ℝ ∞ (RetainedSimplex.chart n m L σ) :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ).contDiff.comp
      (hA.comp (RetainedSimplex.join n m).toContinuousLinearEquiv.contDiff)
  have he : compensatedChart n m L σ =
      RetainedSimplex.chart n m L σ ∘ compensatedShift n m L :=
    funext (compensatedChart_eq_shift n m L σ)
  rw [he]
  exact hC.comp (contDiff_fst.prodMk (contDiff_snd.add
    ((smooth_shift n m L).comp contDiff_fst)))

/-- See Appendix A of the paper: The chart density is the supported physical weight in the centred chart. -/
theorem compensated_density_eq (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    (q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :
    ProperMarginalChart.chartDensity p n m σ (compensatedShift n m ((n + m : ℕ) + 1) q) =
      ProperMarginalChart.density p (n + m) (compensatedChart n m ((n + m : ℕ) + 1) σ q) := by
  classical
  rw [compensatedChart_eq_shift]
  by_cases hq : compensatedShift n m ((n + m : ℕ) + 1) q ∈
      RetainedSimplex.domain n m ((n + m : ℕ) + 1)
  · exact indicator_of_mem hq _
  · have hs : RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ
          (compensatedShift n m ((n + m : ℕ) + 1) q) ∉
          AffineSimplex.massSimplex (n + m) ((n + m : ℕ) + 1) := fun h =>
      hq ((RetainedSimplex.chart_mem_simplex n m _ σ _).mp h)
    simp only [ProperMarginalChart.chartDensity, indicator_of_notMem hq,
      ProperMarginalChart.density, dite_eq_right hs]


private theorem compensated_boundary_null (n m : ℕ) (L : ℝ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ AffineSimplex.chartDomain n L) :
    ∀ᵐ z : EuclideanSpace ℝ (Fin m) ∂volume,
      (x,z) ∉ frontier ((compensatedShift n m L) ⁻¹' RetainedSimplex.domain n m L) := by
  have hxp : x ∈ Prod.fst '' RetainedSimplex.domain n m L := by
    rw [RetainedSimplex.fst_image_domain]
    exact hx
  obtain ⟨q, hq, hqx⟩ := hxp
  have hfibre : ∃ z, (x,z) ∈ RetainedSimplex.domain n m L :=
    ⟨q.2, by simpa only [← hqx] using hq⟩
  have hnull := Riesz1.volume_section_frontier_eq_zero
    (RetainedSimplex.isOpen_domain n m L) (RetainedSimplex.convex_domain n m L) hfibre
  have hae : ∀ᵐ z : EuclideanSpace ℝ (Fin m) ∂volume,
      (x,z) ∉ frontier (RetainedSimplex.domain n m L) := by
    rw [ae_iff]
    simpa only [not_not] using hnull
  let c := AffineSimplex.coordinates m (AffineSimplex.centre m (L - ∑ i, x i))
  have hm := measurePreserving_add_right (volume : Measure (EuclideanSpace ℝ (Fin m))) c
  have ht : ∀ᵐ z : EuclideanSpace ℝ (Fin m) ∂volume,
      (x,z+c) ∉ frontier (RetainedSimplex.domain n m L) :=
    ae_of_ae_map hm.measurable.aemeasurable (by rw [hm.map_eq]; exact hae)
  filter_upwards [ht] with z hz
  rw [← (compensatedShift n m L).preimage_frontier]
  exact hz

/-- See Appendix A of the paper: first and second density derivative
formulas in the fixed, uniformly compensated exterior chart. Domination
and integrability are conclusions for the physical weight. -/
theorem physical_compensated_density_domination (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) :
    let w := fun q => (ProperMarginalChart.chartDensity p n m σ
      (compensatedShift n m ((n + m : ℕ) + 1) q)).toReal
    let dw := fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) =>
      fderiv ℝ (fun t => w (t,q.2)) q.1
    let ddw := fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) =>
      fderiv ℝ (fun t => dw (t,q.2)) q.1
    DominatedFibre.DominatedFDerivOn volume
        (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (fun x z => w (x,z))
        (fun x z => dw (x,z)) ∧
      DominatedFibre.DominatedFDerivOn volume
        (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (fun x z => dw (x,z))
        (fun x z => ddw (x,z)) := by
  obtain ⟨hf, hs⟩ := compensated_density_smooth_compact p n m hn σ
  obtain ⟨hd, hc, h⟩ := compact_partial_domination_actual volume hf hs
    (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (AffineSimplex.isOpen_chartDomain n _)
  exact ⟨h, (compact_partial_domination_actual volume hd hc
    (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (AffineSimplex.isOpen_chartDomain n _)).2.2⟩

private theorem internal_compensated_energy (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    (U : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ)
    (hU : ContDiffOn ℝ ∞ U (gapAmbientDomain (n + m).succPNat))
    (hv : ∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
        y ∈ gapAmbientDomain (n + m).succPNat},
      U y.val = p.val.1 * physicalAmbientGapEnergy p (n + m).succPNat y) :
    let L : ℝ := ((n + m : ℕ) + 1)
    let Q := (compensatedShift n m L) ⁻¹' RetainedSimplex.domain n m L
    let H := fun q => U (compensatedChart n m L σ q)
    ContDiffOn ℝ ∞ H Q ∧
      (fun q => (ProperMarginalChart.chartDensity p n m σ
        (compensatedShift n m L q)).toReal) = Q.indicator (fun q => Real.exp (-H q)) := by
  intro L Q H
  have hs (q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) (hq : q ∈ Q) :
      compensatedChart n m L σ q ∈ AffineSimplex.massSimplex (n + m) L := by
    rw [compensatedChart_eq_shift]
    exact (RetainedSimplex.chart_mem_simplex n m L σ _).mpr hq
  refine ⟨hU.comp (compensatedChart_smooth n m L σ).contDiffOn
    (fun q hq => ProperMarginalChart.simplex_ambient (n + m) (hs q hq)), ?_⟩
  classical
  funext q
  by_cases hq : q ∈ Q
  · have hval := hv ⟨compensatedChart n m L σ q,
      ProperMarginalChart.simplex_ambient (n + m) (hs q hq)⟩
    have hd : ProperMarginalChart.density p (n + m) (compensatedChart n m L σ q) =
        ENNReal.ofReal (Real.exp (-H q)) := by
      dsimp only [ProperMarginalChart.density]
      rw [dite_eq_left (hs q hq)]
      dsimp only [H]
      rw [hval]
      simp only [neg_mul]
      rfl
    rw [compensated_density_eq, hd, ENNReal.toReal_ofReal (Real.exp_nonneg _), indicator_of_mem hq]
  · have hq' : compensatedShift n m L q ∉ RetainedSimplex.domain n m L := hq
    rw [indicator_of_notMem hq]
    change ENNReal.toReal ((RetainedSimplex.domain n m L).indicator
      (fun r => ProperMarginalChart.density p (n + m) (RetainedSimplex.chart n m L σ r))
        (compensatedShift n m L q)) = 0
    rw [indicator_of_notMem hq']
    rfl

/-- See Appendix A of the paper, integration step: the actual physical
unnormalized marginal density is smooth in every order, for every proper
retained set, including point exterior fibres. -/
theorem physical_marginal_density_smooth (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) :
    ContDiff ℝ ∞ (fun x => ∫ z : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p n m σ (x, z)).toReal) := by
  obtain ⟨hf, hs⟩ := physical_chart_density_smooth_compact p n m hn σ
  exact contDiff_infty.mpr (fun a => compact_integral_smooth_nat volume a ℝ _ hf hs)

private theorem chart_density_lt_top (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    (q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :
    ProperMarginalChart.chartDensity p n m σ q < ⊤ := by
  classical
  unfold ProperMarginalChart.chartDensity Set.indicator
  split_ifs
  · dsimp only [ProperMarginalChart.density]
    split_ifs <;> simp
  · simp

/-- See Appendix A of the paper: the real physical normalizer is the real
value of the positive finite extended normalizer, at every interior point. -/
theorem physical_marginal_normalizer (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p n m σ (x, z)).toReal) =
      (AffineFibre.fibreMass volume (ProperMarginalChart.chartDensity p n m σ) x).toReal ∧
      0 < ∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p n m σ (x, z)).toReal := by
  have hfin (z : EuclideanSpace ℝ (Fin m)) :
      ProperMarginalChart.chartDensity p n m σ (x,z) < ⊤ :=
    chart_density_lt_top p n m σ (x,z)
  have he := integral_toReal (μ := volume)
    ((ProperMarginalChart.measurable_chartDensity p n m σ).comp
      measurable_prodMk_left).aemeasurable (Eventually.of_forall hfin)
  simp only [Function.comp_apply] at he
  refine ⟨he, ?_⟩
  rw [he]
  exact ENNReal.toReal_pos (ProperMarginalChart.fibre_mass p n m hn σ hx).1
    (ProperMarginalChart.fibre_mass p n m hn σ hx).2

/-- See Appendix A of the paper, regularity clause, without an active
penalty: the negative logarithm of the actual marginal density is smooth
on the whole retained interior. -/
theorem physical_marginal_potential_smooth (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) :
    ContDiffOn ℝ ∞ (fun x => -Real.log (∫ z : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p n m σ (x, z)).toReal))
      (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :=
  ((physical_marginal_density_smooth p n m hn σ).contDiffOn.log
    (fun _ hx => (physical_marginal_normalizer p n m hn σ hx).2.ne')).neg

private theorem internal_active_penalty_smooth (n m : ℕ) (θ : PhysicalCutoff)
    {a : ℝ} (ha : 0 < a) (J : Finset (Fin n)) (b : Bool) :
    ContDiffOn ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) =>
      ∑ i ∈ J, (θ.val (a * x i) + if b then θ.val (a * (x i)⁻¹) else 0))
      (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) := by
  apply ContDiffOn.sum
  intro i _ x hx
  have hi : ContDiffAt ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) => x i) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt
  have hu := (PhysicalCollision.cutoff_contDiffAt θ (mul_pos ha (hx.1 i))).comp x
    (contDiffAt_const.mul hi)
  cases b
  · simpa only [Bool.false_eq_true, ↓reduceIte, add_zero, Function.comp_def] using hu.contDiffWithinAt
  · have hv := (PhysicalCollision.cutoff_contDiffAt θ (mul_pos ha (inv_pos.mpr (hx.1 i)))).comp x
      (contDiffAt_const.mul (hi.inv (hx.1 i).ne'))
    simpa only [↓reduceIte, Function.comp_def, Pi.inv_apply] using (hu.add hv).contDiffWithinAt

/-- See Appendix A of the paper, all allowed active penalties: adding the
selected upper or two-sided cutoff preserves all-order marginal
regularity on the retained interior. The empty active set gives zero penalty. -/
theorem physical_penalized_marginal_potential_smooth (p : Parameters) (n m : ℕ)
    (hn : 1 ≤ n) (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff)
    {a : ℝ} (ha : 0 < a) (J : Finset (Fin n)) (b : Bool) :
    ContDiffOn ℝ ∞ (fun x => p.val.1 * ∑ i ∈ J, (θ.val (a * x i) +
        if b then θ.val (a * (x i)⁻¹) else 0) -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p n m σ (x,z)).toReal))
      (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) := by
  have hP := internal_active_penalty_smooth n m θ ha J b
  exact (contDiffOn_const.mul hP).add
    (physical_marginal_potential_smooth p n m hn σ)

/-- Internal chain-rule bridge for Appendix A: chart derivatives
are exactly the ambient uniformly compensated derivatives in both orders. -/
theorem internal_compensated_energy_derivatives (n m : ℕ) (L : ℝ)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    {U : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ}
    (x : EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin m))
    (hU : ContDiffAt ℝ 2 U (compensatedChart n m L σ (x,z)))
    (u v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun t => U (compensatedChart n m L σ (t,z))) x u =
      fderiv ℝ U (compensatedChart n m L σ (x,z)) (compensatedDirection n m σ u) ∧
    fderiv ℝ (fderiv ℝ (fun t => U (compensatedChart n m L σ (t,z)))) x u v =
      fderiv ℝ (fderiv ℝ U) (compensatedChart n m L σ (x,z))
        (compensatedDirection n m σ u) (compensatedDirection n m σ v) := by
  constructor
  · exact congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => A u)
      ((hU.differentiableAt (by norm_num)).hasFDerivAt.comp x
        (compensatedChart_hasFDerivAt n m L σ x z)).fderiv
  · have hU' : ContDiffAt ℝ 2 U
        (compensatedDirection n m σ x + compensatedChart n m L σ (0,z)) := by
      rw [← compensatedChart_affine]
      exact hU
    simpa only [← compensatedChart_affine] using
      AffineMetricTransport.hessian_comp_affine (compensatedDirection n m σ)
        (compensatedChart n m L σ (0,z)) hU' u v

set_option backward.isDefEq.respectTransparency false in
/-- See Appendix A of the paper: the physical marginal is smooth and its
uniformly compensated first and second derivatives are the conditional
mean force and mean energy Hessian minus covariance. Every expectation is
integrable, all forces are in L², and their covariance matrix is nonnegative.
The conditional is identified with the physical conditional by its
constant-Jacobian fibre translation. -/
theorem physical_compensated_marginal_calculus (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) :
    ∃ U : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain (n + m).succPNat) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
          y ∈ gapAmbientDomain (n + m).succPNat},
        U y.val = p.val.1 * physicalAmbientGapEnergy p (n + m).succPNat y) ∧
      ContDiffOn ℝ ∞ (fun t => -Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p n m σ (t,z)).toReal))
          (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) ∧
      ∀ x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
        let c := AffineSimplex.coordinates m
          (AffineSimplex.centre m (((n + m : ℕ) + 1) - ∑ i, x.val i))
        let ρ := AffineFibre.normalizedMeasure volume
          (fun z => ProperMarginalChart.chartDensity p n m σ (x.val,z+c))
          (by rw [lintegral_add_right_eq_self (fun z => ProperMarginalChart.chartDensity p n m σ (x.val,z)) c]
              exact (ProperMarginalChart.fibre_mass p n m hn σ x.property).1)
          (by rw [lintegral_add_right_eq_self (fun z => ProperMarginalChart.chartDensity p n m σ (x.val,z)) c]
              exact (ProperMarginalChart.fibre_mass p n m hn σ x.property).2)
        let H := fun z t => U (compensatedChart n m ((n + m : ℕ) + 1) σ (t,z))
        ρ.map (fun z => z+c) = ProperMarginalChart.conditionalMeasure p n m hn σ x ∧
        (∀ u, MemLp (fun z => fderiv ℝ (H z) x.val u) 2 ρ) ∧
        (∀ u v, Integrable (fun z => fderiv ℝ (fderiv ℝ (H z)) x.val u v) ρ) ∧
        (∀ u v,
          fderiv ℝ (fun t => -Real.log (∫ z : EuclideanSpace ℝ (Fin m),
            (ProperMarginalChart.chartDensity p n m σ (t,z)).toReal)) x.val u =
              ∫ z, fderiv ℝ (H z) x.val u ∂ρ ∧
          fderiv ℝ (fderiv ℝ (fun t => -Real.log (∫ z : EuclideanSpace ℝ (Fin m),
            (ProperMarginalChart.chartDensity p n m σ (t,z)).toReal))) x.val u v =
              (∫ z, fderiv ℝ (fderiv ℝ (H z)) x.val u v ∂ρ) -
                ProbabilityTheory.covariance (fun z => fderiv ℝ (H z) x.val u)
                  (fun z => fderiv ℝ (H z) x.val v) ρ) ∧
        ∀ b : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, b i * ProbabilityTheory.covariance
          (fun z => fderiv ℝ (H z) x.val (EuclideanSpace.single i 1))
          (fun z => fderiv ℝ (H z) x.val (EuclideanSpace.single j 1)) ρ * b j := by
  obtain ⟨W, hW, hval, _⟩ := PhysicalEnergy.ambient_derivatives p (n + m).succPNat
  let U := fun y => p.val.1 * W y
  have hU : ContDiffOn ℝ ∞ U (gapAmbientDomain (n + m).succPNat) :=
    contDiffOn_const.mul hW
  have hv : ∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
      y ∈ gapAmbientDomain (n + m).succPNat},
      U y.val = p.val.1 * physicalAmbientGapEnergy p (n + m).succPNat y :=
    fun y => congrArg (fun t : ℝ => p.val.1 * t) (hval y)
  refine ⟨U, hU, hv, physical_marginal_potential_smooth p n m hn σ, ?_⟩
  intro x c ρ H
  let w := fun q => (ProperMarginalChart.chartDensity p n m σ
    (compensatedShift n m ((n + m : ℕ) + 1) q)).toReal
  let dw := fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) =>
    fderiv ℝ (fun t => w (t,q.2)) q.1
  let ddw := fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) =>
    fderiv ℝ (fun t => dw (t,q.2)) q.1
  obtain ⟨h, h'⟩ := physical_compensated_density_domination p n m hn σ
  change DominatedFibre.DominatedFDerivOn volume _ (fun t z => w (t,z)) (fun t z => dw (t,z)) at h
  change DominatedFibre.DominatedFDerivOn volume _ (fun t z => dw (t,z)) (fun t z => ddw (t,z)) at h'
  have hZ : (fun t : EuclideanSpace ℝ (Fin n) => ∫ z : EuclideanSpace ℝ (Fin m), w (t,z)) =
      fun t => ∫ z : EuclideanSpace ℝ (Fin m), (ProperMarginalChart.chartDensity p n m σ (t,z)).toReal := by
    funext t
    exact integral_add_right_eq_self
      (fun z => (ProperMarginalChart.chartDensity p n m σ (t,z)).toReal)
      (AffineSimplex.coordinates m (AffineSimplex.centre m (((n + m : ℕ) + 1) - ∑ i, t i)))
  have hp (t : EuclideanSpace ℝ (Fin n)) (ht : t ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
      0 < ∫ z : EuclideanSpace ℝ (Fin m), w (t,z) := by
    rw [congrFun hZ t]
    exact (physical_marginal_normalizer p n m hn σ ht).2
  have hw (t : EuclideanSpace ℝ (Fin n)) (_ht : t ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
      (z : EuclideanSpace ℝ (Fin m)) : 0 ≤ w (t,z) := ENNReal.toReal_nonneg
  let ρreal := AffineFibre.normalizedMeasure volume (fun z => ENNReal.ofReal (w (x.val,z)))
    (by rw [← ofReal_integral_eq_lintegral_ofReal (h.integrable x.val x.property)
          (Eventually.of_forall (hw x.val x.property))]
        exact ENNReal.ofReal_ne_zero_iff.mpr (hp x.val x.property))
    (by rw [← ofReal_integral_eq_lintegral_ofReal (h.integrable x.val x.property)
          (Eventually.of_forall (hw x.val x.property))]
        exact ENNReal.ofReal_ne_top)
  have hwof (z : EuclideanSpace ℝ (Fin m)) : ENNReal.ofReal (w (x.val,z)) =
      ProperMarginalChart.chartDensity p n m σ (x.val,z+c) :=
    ENNReal.ofReal_toReal (chart_density_lt_top p n m σ _).ne
  have hρ : ρreal = ρ :=
    congrArg (fun weight : EuclideanSpace ℝ (Fin m) → ENNReal =>
      volume.withDensity (fun z => (∫⁻ y, weight y)⁻¹ * weight z)) (funext hwof)
  let S := fun z => fderiv ℝ (H z) x.val
  let T := fun z => fderiv ℝ (fderiv ℝ (H z)) x.val
  obtain ⟨hH, he⟩ := internal_compensated_energy p n m σ U hU hv
  have hid := internal_indicator_gibbs_derivatives
    ((RetainedSimplex.isOpen_domain n m ((n + m : ℕ) + 1)).preimage
      (compensatedShift n m ((n + m : ℕ) + 1)).continuous) hH he x.val
    (compensated_boundary_null n m ((n + m : ℕ) + 1) x.property)
  have hforce : ∀ᵐ z : EuclideanSpace ℝ (Fin m) ∂volume, dw (x.val,z) = -w (x.val,z) • S z :=
    hid.mono fun _ hz => hz.1
  have hsecond : ∀ᵐ z : EuclideanSpace ℝ (Fin m) ∂volume,
      ddw (x.val,z) = w (x.val,z) • ((S z).smulRight (S z) - T z) :=
    hid.mono fun _ hz => hz.2
  have hL2 (u : EuclideanSpace ℝ (Fin n)) : MemLp (fun z => S z u) 2 ρ := by
    have hh := DominatedFibre.memLp_gibbs_force h h' hw x.property
      (hp x.val x.property) S hforce u
    change MemLp (fun z => S z u) 2 ρreal at hh
    rwa [hρ] at hh
  have hTi (u v : EuclideanSpace ℝ (Fin n)) : Integrable (fun z => T z u v) ρ := by
    have hh := (DominatedFibre.integrable_normalizedMeasure_iff (h.integrable x.val x.property)
      (hw x.val x.property) (hp x.val x.property) _).mpr
      (DominatedFibre.integrable_weighted_gibbs_hessian h h' hw x.property
        (hp x.val x.property) S T hforce hsecond u v)
    change Integrable (fun z => T z u v) ρreal at hh
    rwa [hρ] at hh
  have : IsProbabilityMeasure ρ := by
    dsimp only [ρ]
    apply AffineFibre.isProbabilityMeasure_normalizedMeasure
    exact (ProperMarginalChart.measurable_chartDensity p n m σ).comp
      (measurable_const.prodMk (measurable_id.add measurable_const))
  refine ⟨compensated_conditional_map p n m hn σ x, hL2, hTi, ?_, ?_⟩
  · intro u v
    have hg := internal_gibbs_gradient_apply h x.property (hw x.val x.property)
      (hp x.val x.property) S hforce u
    have hh := DominatedFibre.gibbs_marginal_hessian_apply_of_domination
      (AffineSimplex.isOpen_chartDomain n _) h h' hw hp x.property S T hforce hsecond u v
    change fderiv ℝ (fun t => -Real.log (∫ z : EuclideanSpace ℝ (Fin m), w (t,z))) x.val u =
      ∫ z, S z u ∂ρreal at hg
    change fderiv ℝ (fderiv ℝ (fun t => -Real.log (∫ z : EuclideanSpace ℝ (Fin m), w (t,z)))) x.val u v =
      (∫ z, T z u v ∂ρreal) - ProbabilityTheory.covariance (fun z => S z u) (fun z => S z v) ρreal at hh
    simp_rw [congrFun hZ] at hg hh
    rw [hρ] at hg hh
    exact ⟨hg, hh⟩
  · exact covariance_quadratic_nonneg (fun i => hL2 (EuclideanSpace.single i 1))

set_option backward.isDefEq.respectTransparency false in
/-- See Appendix A of the paper, including every allowed active penalty:
all-order marginal regularity and the uniformly compensated mean-force and
Hessian-minus-covariance formulas, with the actual physical conditional.
The finite expectations and covariance positivity are conclusions. -/
theorem physical_penalized_compensated_marginal_calculus (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff)
    {a : ℝ} (ha : 0 < a) (J : Finset (Fin n)) (b : Bool) :
    let P := fun x : EuclideanSpace ℝ (Fin n) => ∑ i ∈ J,
      (θ.val (a * x i) + if b then θ.val (a * (x i)⁻¹) else 0)
    ∃ U : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain (n + m).succPNat) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
          y ∈ gapAmbientDomain (n + m).succPNat},
        U y.val = p.val.1 * physicalAmbientGapEnergy p (n + m).succPNat y) ∧
      ContDiffOn ℝ ∞ (fun t => p.val.1 * P t - Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p n m σ (t,z)).toReal))
          (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) ∧
      ∀ x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
        let c := AffineSimplex.coordinates m
          (AffineSimplex.centre m (((n + m : ℕ) + 1) - ∑ i, x.val i))
        let ρ := AffineFibre.normalizedMeasure volume
          (fun z => ProperMarginalChart.chartDensity p n m σ (x.val,z+c))
          (by rw [lintegral_add_right_eq_self (fun z => ProperMarginalChart.chartDensity p n m σ (x.val,z)) c]
              exact (ProperMarginalChart.fibre_mass p n m hn σ x.property).1)
          (by rw [lintegral_add_right_eq_self (fun z => ProperMarginalChart.chartDensity p n m σ (x.val,z)) c]
              exact (ProperMarginalChart.fibre_mass p n m hn σ x.property).2)
        let H := fun z t => U (compensatedChart n m ((n + m : ℕ) + 1) σ (t,z))
        ρ.map (fun z => z+c) = ProperMarginalChart.conditionalMeasure p n m hn σ x ∧
        (∀ u, MemLp (fun z => fderiv ℝ (H z) x.val u) 2 ρ) ∧
        (∀ u v, Integrable (fun z => fderiv ℝ (fderiv ℝ (H z)) x.val u v) ρ) ∧
        (∀ u v,
          fderiv ℝ (fun t => p.val.1 * P t - Real.log (∫ z : EuclideanSpace ℝ (Fin m),
            (ProperMarginalChart.chartDensity p n m σ (t,z)).toReal)) x.val u =
              p.val.1 * fderiv ℝ P x.val u + ∫ z, fderiv ℝ (H z) x.val u ∂ρ ∧
          fderiv ℝ (fderiv ℝ (fun t => p.val.1 * P t - Real.log (∫ z : EuclideanSpace ℝ (Fin m),
            (ProperMarginalChart.chartDensity p n m σ (t,z)).toReal))) x.val u v =
              p.val.1 * fderiv ℝ (fderiv ℝ P) x.val u v +
                (∫ z, fderiv ℝ (fderiv ℝ (H z)) x.val u v ∂ρ) -
                ProbabilityTheory.covariance (fun z => fderiv ℝ (H z) x.val u)
                  (fun z => fderiv ℝ (H z) x.val v) ρ) ∧
        ∀ b : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, b i * ProbabilityTheory.covariance
          (fun z => fderiv ℝ (H z) x.val (EuclideanSpace.single i 1))
          (fun z => fderiv ℝ (H z) x.val (EuclideanSpace.single j 1)) ρ * b j := by
  intro P
  obtain ⟨U, hU, hv, hsm, hmain⟩ := physical_compensated_marginal_calculus p n m hn σ
  refine ⟨U, hU, hv, physical_penalized_marginal_potential_smooth p n m hn σ θ ha J b, ?_⟩
  intro x c ρ H
  obtain ⟨hmap, hL2, hT, hderiv, hcov⟩ := hmain x
  refine ⟨hmap, hL2, hT, ?_, hcov⟩
  intro u v
  let V₀ := fun t => -Real.log (∫ z : EuclideanSpace ℝ (Fin m),
    (ProperMarginalChart.chartDensity p n m σ (t,z)).toReal)
  have hP : ContDiffAt ℝ ∞ P x.val :=
    (internal_active_penalty_smooth n m θ ha J b).contDiffAt
      ((AffineSimplex.isOpen_chartDomain n _).mem_nhds x.property)
  have hV : ContDiffAt ℝ ∞ V₀ x.val := hsm.contDiffAt
    ((AffineSimplex.isOpen_chartDomain n _).mem_nhds x.property)
  have hP2 : ContDiffAt ℝ 2 P x.val := hP.of_le (by norm_num)
  have hV2 : ContDiffAt ℝ 2 V₀ x.val := hV.of_le (by norm_num)
  have hg := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L u)
    (((hP.differentiableAt (by norm_num)).hasFDerivAt.const_mul p.val.1).add
      (hV.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  simp only [Pi.add_def, add_apply, smul_apply, smul_eq_mul] at hg
  have hh := PhysicalCollision.internal_hessian_add (F := fun t => p.val.1 * P t)
    (contDiffAt_const.mul hP2) hV2 u v
  rw [PhysicalCollision.internal_hessian_const_mul hP2] at hh
  constructor
  · change fderiv ℝ (fun t => p.val.1 * P t + V₀ t) x.val u = _
    rw [hg, (hderiv u v).1]
  · change fderiv ℝ (fderiv ℝ (fun t => p.val.1 * P t + V₀ t)) x.val u v = _
    rw [hh, (hderiv u v).2]
    ring

/-- See Appendix A of the paper: the active
penalty potential used in the derivative theorem is the negative logarithm
of the actual penalized marginal density. Its real normalizer is
positive and its integrand is integrable, at every retained interior point. -/
theorem physical_penalized_marginal_density (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff)
    (a : ℝ) (J : Finset (Fin n)) (b : Bool)
    {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    let e : Fin n ↪ Fin (n + m + 1) := ⟨fun i => σ (i.castAdd m).castSucc,
      fun i j h => by simpa only [Equiv.apply_eq_iff_eq, Fin.castSucc_inj, Fin.castAdd_inj] using h⟩
    let P := ∑ i ∈ J, (θ.val (a * x i) + if b then θ.val (a * (x i)⁻¹) else 0)
    Integrable (fun z : EuclideanSpace ℝ (Fin m) =>
      (ProperMarginalChart.penalizedChartDensity p n m σ θ a (J.map e) b (x,z)).toReal) volume ∧
    0 < ∫ z : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.penalizedChartDensity p n m σ θ a (J.map e) b (x,z)).toReal ∧
    p.val.1 * P - Real.log (∫ z : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p n m σ (x,z)).toReal) =
        -Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.penalizedChartDensity p n m σ θ a (J.map e) b (x,z)).toReal) := by
  classical
  intro e P
  have hJ : ∀ i ∈ J.map e, ∃ j : Fin n, i = σ (j.castAdd m).castSucc := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    exact ⟨j, rfl⟩
  have hsum : (∑ i ∈ J.map e,
      (θ.val (a * RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ (x,0) i) +
        if b then θ.val (a * (RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ (x,0) i)⁻¹) else 0)) = P := by
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro i _
    simp only [show e i = σ (i.castAdd m).castSucc from rfl, RetainedSimplex.chart_retained]
  have he (z : EuclideanSpace ℝ (Fin m)) :
      (ProperMarginalChart.penalizedChartDensity p n m σ θ a (J.map e) b (x,z)).toReal =
        Real.exp (-p.val.1 * P) * (ProperMarginalChart.chartDensity p n m σ (x,z)).toReal := by
    rw [ProperMarginalChart.penalizedChartDensity_eq_mul p n m σ θ a (J.map e) b hJ, hsum,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  obtain ⟨hf, hs⟩ := physical_chart_density_smooth_compact p n m hn σ
  obtain ⟨bound, hi, hb⟩ := compact_fibre_bound volume hf.continuous hs
  have hbase : Integrable (fun z : EuclideanSpace ℝ (Fin m) =>
      (ProperMarginalChart.chartDensity p n m σ (x,z)).toReal) volume :=
    hi.mono' ((hf.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall (hb x))
  have hpos := (physical_marginal_normalizer p n m hn σ hx).2
  have hZ : (∫ z : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.penalizedChartDensity p n m σ θ a (J.map e) b (x,z)).toReal) =
      Real.exp (-p.val.1 * P) * ∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p n m σ (x,z)).toReal := by
    simp_rw [he]
    exact integral_const_mul _ _
  refine ⟨(hbase.const_mul _).congr (Eventually.of_forall (fun z => (he z).symm)), ?_, ?_⟩
  · rw [hZ]
    exact mul_pos (Real.exp_pos _) hpos
  · rw [hZ, Real.log_mul (Real.exp_ne_zero _) hpos.ne', Real.log_exp]
    ring

end MarginalHessian
end Riesz2
