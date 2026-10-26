/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.ConditionalForcesPart2
public import Riesz2.DecayShort.PhysicalFibresPart3
public import Riesz2.HelfferSjostrand.MarginalHessianPart4
public import Riesz2.ToMathlib.RegularizedDensityScore

/-!
# Higher moments on physical conditional fibres

Integrability inputs for the proofs of Lemmas 5.7 and 5.8. The actual
ambient energy tensors have moments of every positive integral order at
every retained point. The measure and configuration are the physical
objects, including fibres of dimension zero.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace Riesz2.ConditionalForces

set_option backward.isDefEq.respectTransparency false

section ScoreGraph

variable {B E : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Internal score criterion. The numerator is the directional derivative
of the smooth supported density, so no boundary extension of the force
is assumed. The three moments are analytic premises of this general lemma. -/
private theorem supported_score_graph_internal
    (μ : Measure E) {Q : Set (B × E)} (hQ : IsOpen Q)
    {w V : B × E → ℝ} (hw : ContDiff ℝ ∞ w)
    (hwn : ∀ q, 0 ≤ w q) (hV : ContDiffOn ℝ ∞ V Q)
    (he : ∀ q ∈ Q, w q = Real.exp (-V q)) (b : B) (v : B × E)
    (hsupp : ∀ᵐ z ∂μ, (b,z) ∈ Q)
    (hF : MemLp (fun z => fderiv ℝ V (b,z) v) 2 μ)
    (hG : MemLp (gradient (fun z => fderiv ℝ V (b,z) v)) 2 μ)
    (hS : MemLp (fun z => (fderiv ℝ V (b,z) v) •
      gradient (fun y => V (b,y)) z) 2 μ) :
    Riesz1.WeightedSobolev.IsWeightedH1 μ (Prod.mk b ⁻¹' Q)
      (fun z => fderiv ℝ V (b,z) v)
      (gradient (fun z => fderiv ℝ V (b,z) v)) := by
  let W := fun z => w (b,z)
  let F := fun z => fderiv ℝ V (b,z) v
  let g := fun z => -fderiv ℝ w (b,z) v
  have hw' : ContDiff ℝ ∞ W := hw.comp (contDiff_const.prodMk contDiff_id)
  have hg : ContDiff ℝ ∞ g :=
    (((hw.fderiv_right (by simp)).clm_apply contDiff_const).neg).comp
      (contDiff_const.prodMk contDiff_id)
  have hvalue (z : E) (hz : (b,z) ∈ Q) : g z = W z * F z := by
    have hVq := hV.contDiffAt (hQ.mem_nhds hz)
    have heq : w =ᶠ[𝓝 (b,z)] fun q => Real.exp (-V q) := by
      filter_upwards [hQ.mem_nhds hz] with q hq using he q hq
    have hd := ((hVq.differentiableAt (by simp)).hasFDerivAt.neg.exp).fderiv
    change fderiv ℝ (fun q => Real.exp (-V q)) (b,z) =
      Real.exp (-V (b,z)) • -fderiv ℝ V (b,z) at hd
    rw [← heq.fderiv_eq] at hd
    dsimp only [g, W, F]
    rw [hd, smul_apply, neg_apply, he _ hz]
    ring
  have hFdiff (z : E) (hz : (b,z) ∈ Q) : DifferentiableAt ℝ F z := by
    exact (((hV.fderiv_of_isOpen hQ (m := ∞) (by simp)).contDiffAt
      (hQ.mem_nhds hz)).clm_apply contDiffAt_const).differentiableAt (by simp) |>.comp z
        ((differentiableAt_const _).prodMk differentiableAt_id)
  have hjet (z : E) (hz : (b,z) ∈ Q) :
      gradient g z = W z • gradient F z + F z • gradient W z := by
    have heq : g =ᶠ[𝓝 z] fun y => W y * F y := by
      have hmem : ∀ᶠ y in 𝓝 z, (b,y) ∈ Q :=
        (continuous_const.prodMk continuous_id).continuousAt (hQ.mem_nhds hz)
      filter_upwards [hmem] with y hy using hvalue y hy
    have hd := ((hw'.differentiable (by simp) z).hasFDerivAt.mul
      (hFdiff z hz).hasFDerivAt).hasGradientAt.gradient
    simp only [gradient] at hd ⊢
    rw [heq.fderiv_eq]
    simpa only [gradient, map_add, map_smul, Pi.mul_def] using hd
  have hscore (z : E) (hz : (b,z) ∈ Q) :
      gradient W z = -W z • gradient (fun y => V (b,y)) z := by
    have heq : W =ᶠ[𝓝 z] fun y => Real.exp (-V (b,y)) := by
      have hmem : ∀ᶠ y in 𝓝 z, (b,y) ∈ Q :=
        (continuous_const.prodMk continuous_id).continuousAt (hQ.mem_nhds hz)
      filter_upwards [hmem] with y hy using he _ hy
    have hdV : DifferentiableAt ℝ (fun y => V (b,y)) z :=
      ((hV.contDiffAt (hQ.mem_nhds hz)).differentiableAt (by simp)).comp z
        ((differentiableAt_const _).prodMk differentiableAt_id)
    have hd := (hdV.hasFDerivAt.neg.exp).hasGradientAt.gradient
    simp only [gradient] at hd ⊢
    simp only [Pi.neg_apply] at hd
    rw [heq.fderiv_eq, hd, map_smul, map_neg, ← he (b,z) hz]
    simp only [neg_smul, smul_neg]
    rfl
  apply DensityScore.isWeightedH1_of_density_quotient_internal μ (Prod.mk b ⁻¹' Q) hw' hg
    (fun z => hwn (b,z))
    (hsupp.mono fun z hz => by dsimp [W]; rw [he _ hz]; exact Real.exp_pos _)
    (hsupp.mono hvalue) (hsupp.mono hjet) hF hG
  apply MemLp.ae_eq _ hS.neg
  filter_upwards [hsupp] with z hz
  change -(F z • gradient (fun y => V (b,y)) z) = (F z / W z) • gradient W z
  rw [hscore z hz, smul_smul]
  have hp : 0 < W z := by dsimp [W]; rw [he _ hz]; exact Real.exp_pos _
  rw [show F z / W z * -W z = -F z by field_simp, neg_smul]

end ScoreGraph


/-- Derivative bounds for an affine score, including its exterior gradient. -/
private theorem affine_score_bounds_internal {n m d : ℕ}
    (A : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) →L[ℝ]
      EuclideanSpace ℝ (Fin d)) (a : EuclideanSpace ℝ (Fin d))
    (U : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin m))
    (v : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))
    (hU : ContDiffAt ℝ 2 U (A (x,z) + a)) :
    let V := fun q => U (A q + a)
    ‖fderiv ℝ V (x,z) v‖ ≤ ‖fderiv ℝ U (A (x,z) + a)‖ * ‖A‖ * ‖v‖ ∧
    ‖gradient (fun y => fderiv ℝ V (x,y) v) z‖ ≤
      ‖fderiv ℝ (fderiv ℝ U) (A (x,z) + a)‖ * ‖A‖ ^ 2 * ‖v‖ ∧
    ‖gradient (fun y => V (x,y)) z‖ ≤ ‖fderiv ℝ U (A (x,z) + a)‖ * ‖A‖ := by
  have : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :=
    Prod.continuousSMul
  intro V
  let I := ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))
  have hp : HasFDerivAt (fun y => (x,y)) I z :=
    (hasFDerivAt_const x z).prodMk (hasFDerivAt_id z)
  have ha : HasFDerivAt (fun y => A (x,y) + a) (A.comp I) z :=
    ((A.hasFDerivAt.comp z hp).add_const a)
  have hfirst := (hU.differentiableAt (by norm_num)).hasFDerivAt
  have hfull := (hfirst.comp (x,z) (A.hasFDerivAt.add_const a)).fderiv
  have hb : ‖fderiv ℝ V (x,z) v‖ ≤ ‖fderiv ℝ U (A (x,z) + a)‖ * ‖A‖ * ‖v‖ := by
    rw [show fderiv ℝ V (x,z) = _ from hfull]
    exact ((fderiv ℝ U _).le_opNorm (A v)).trans
      (by nlinarith only [A.le_opNorm v,
        mul_le_mul_of_nonneg_left (A.le_opNorm v) (norm_nonneg (fderiv ℝ U (A (x,z) + a)))])
  have hnear := ha.continuousAt.tendsto.eventually (hU.eventually (by norm_num))
  have heq : (fun y => fderiv ℝ V (x,y) v) =ᶠ[𝓝 z]
      fun y => fderiv ℝ U (A (x,y) + a) (A v) := by
    filter_upwards [hnear] with y hy
    have hd := ((hy.differentiableAt (by norm_num)).hasFDerivAt.comp
      (x,y) (A.hasFDerivAt.add_const a)).fderiv
    exact congrArg (fun T => T v) hd
  have hd := (((hU.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp z ha).clm_apply (hasFDerivAt_const (A v) z)
  have hdd := hd.fderiv
  simp only [Function.comp_def] at hdd
  have hg : ‖gradient (fun y => fderiv ℝ V (x,y) v) z‖ ≤
      ‖fderiv ℝ (fderiv ℝ U) (A (x,z) + a)‖ * ‖A‖ ^ 2 * ‖v‖ := by
    rw [Riesz1.LogSobolevInternal.norm_gradient_eq_norm_fderiv, heq.fderiv_eq, hdd]
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro u
    simp only [add_apply, ContinuousLinearMap.comp_apply, zero_apply, map_zero, zero_add]
    change ‖fderiv ℝ (fderiv ℝ U) (A (x,z) + a) (A (0,u)) (A v)‖ ≤
      (‖fderiv ℝ (fderiv ℝ U) (A (x,z) + a)‖ * ‖A‖ ^ 2 * ‖v‖) * ‖u‖
    calc
      ‖fderiv ℝ (fderiv ℝ U) (A (x,z) + a) (A (0,u)) (A v)‖ ≤
          ‖fderiv ℝ (fderiv ℝ U) (A (x,z) + a)‖ * ‖A (0,u)‖ * ‖A v‖ := by
        exact ((fderiv ℝ (fderiv ℝ U) _ (A (0,u))).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ U) _).le_opNorm _) (norm_nonneg _))
      _ ≤ ‖fderiv ℝ (fderiv ℝ U) (A (x,z) + a)‖ * (‖A‖ * ‖u‖) * (‖A‖ * ‖v‖) := by
        gcongr
        · simpa using A.le_opNorm (0,u)
        · exact A.le_opNorm v
      _ = _ := by ring
  refine ⟨hb, hg, ?_⟩
  rw [Riesz1.LogSobolevInternal.norm_gradient_eq_norm_fderiv]
  change ‖fderiv ℝ (fun y => U (A (x,y) + a)) z‖ ≤ _
  rw [show fderiv ℝ (fun y => U (A (x,y) + a)) z = _ from (hfirst.comp z ha).fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  change ‖fderiv ℝ U (A (x,z) + a) (A (0,u))‖ ≤ _
  calc
    _ ≤ ‖fderiv ℝ U (A (x,z) + a)‖ * ‖A (0,u)‖ := (fderiv ℝ U _).le_opNorm _
    _ ≤ ‖fderiv ℝ U (A (x,z) + a)‖ * (‖A‖ * ‖u‖) :=
      mul_le_mul_of_nonneg_left (by simpa using A.le_opNorm (0,u)) (norm_nonneg _)
    _ = _ := by ring

set_option backward.isDefEq.respectTransparency false in
/-- Integrability input to the proofs of Lemmas 5.7 and 5.8:
every positive-order physical energy tensor has all even moments on every
positive exterior fibre. The realization is beta times the energy
on its entire ambient domain. -/
theorem physical_tensor_even_moments (p : Parameters) (n m : ℕ) (hn : 1 ≤ n) :
    ∃ U : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain (n + m).succPNat) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
          y ∈ gapAmbientDomain (n + m).succPNat},
        U y.val = p.val.1 * physicalAmbientGapEnergy p (n + m).succPNat y) ∧
      ∀ (σ : Equiv.Perm (Fin (n + m + 1)))
        (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (j k : ℕ+),
        MemLp (fun z => ‖iteratedFDeriv ℝ j U
          (DecayShort.PhysicalFibres.configuration n m σ x z).val‖ ^ (k : ℕ)) 2
          (DecayShort.PhysicalFibres.measure p n m hn σ x) := by
  classical
  obtain ⟨U, hU, hv, ht⟩ := MarginalHessian.physical_energy_tensors p (n + m).succPNat
  change (EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ) at U
  simp only [Nat.succPNat_coe] at hU hv ht
  refine ⟨U, hU, hv, fun σ x j k => ?_⟩
  obtain ⟨C, hC, hb⟩ := ht j
  let c := fun z => (DecayShort.PhysicalFibres.configuration n m σ x z).val
  let μ := DecayShort.PhysicalFibres.measure p n m hn σ x
  let r := 2 * (k : ℝ) * (p.val.2 + (j : ℝ))
  have hr : 0 < r := by
    dsimp [r]
    exact mul_pos (mul_pos (by norm_num) (by exact_mod_cast k.pos))
      (add_pos p.property.2.1 (by exact_mod_cast j.pos))
  have hi (a : Fin (n + m + 1)) : Integrable (fun z => (c z a) ^ (-r)) μ :=
    DecayShort.PhysicalFibres.integrable_coordinate_inverse_power p n m hn σ x a r hr
  have hmajor : Integrable (fun z => C ^ (2 * (k : ℕ)) * ∑ a, (c z a) ^ (-r)) μ :=
    (integrable_finsetSum Finset.univ (fun a _ => hi a)).const_mul _
  have hc : Continuous c := (DecayShort.PhysicalFibres.continuous_configuration n m σ x).subtype_val
  have hcdom : ∀ z, c z ∈ gapAmbientDomain (n + m).succPNat :=
    fun z => (DecayShort.PhysicalFibres.configuration n m σ x z).property
  have hmeas : Measurable (fun z => ‖iteratedFDeriv ℝ j U (c z)‖ ^ (k : ℕ)) :=
    (((ContinuousOn.continuousOn_iteratedFDeriv hU (PhysicalEnergy.isOpen_gapAmbientDomain _)
      (by simp)).comp_continuous hc hcdom).norm.pow _).measurable
  apply (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).mpr
  apply hmajor.mono' (hmeas.pow_const 2).aestronglyMeasurable
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← pow_mul]
  obtain ⟨a, _, ha⟩ := Finset.exists_min_image Finset.univ (fun a => c z a)
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin (n + m + 1))).Nonempty)
  have hs := DecayShort.PhysicalFibres.configuration_mem_simplex n m σ x z
  have hδ : 0 < c z a := hs.1 a
  have he := pow_le_pow_left₀ (norm_nonneg _) (hb (c z) hs (c z a) hδ
    (fun b => ha b (Finset.mem_univ b))) (2 * (k : ℕ))
  have hpow : ((c z a) ^ (-p.val.2 - (j : ℝ))) ^ (2 * (k : ℕ)) =
      (c z a) ^ (-r) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    congr 1
    dsimp [r]
    push_cast
    ring
  rw [mul_pow, hpow] at he
  have hsum : (c z a) ^ (-r) ≤ ∑ b, (c z b) ^ (-r) :=
    Finset.single_le_sum (fun b _ => Real.rpow_nonneg (hs.1 b).le _) (Finset.mem_univ a)
  rw [Nat.mul_comm (k : ℕ) 2]
  exact he.trans (mul_le_mul_of_nonneg_left hsum (pow_nonneg hC.le _))

private theorem chart_affine_tangent_internal (n m : ℕ) (L : ℝ)
    (σ : Equiv.Perm (Fin (n + m + 1))) :
    ∃ A : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n + m + 1)),
      (∀ q, RetainedSimplex.chart n m L σ q = A q +
        RetainedSimplex.chart n m L σ (0,0)) ∧
      ∀ d : EuclideanSpace ℝ (Fin (n + m + 1)), (∑ i, d i) = 0 →
        A (RetainedSimplex.coordinates n m σ d) = d := by
  have : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :=
    Prod.continuousSMul
  let e := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ
  let A := e.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((AffineSimplex.tangentMap (n + m)).toContinuousLinearMap.comp
      (RetainedSimplex.join n m).toContinuousLinearEquiv.toContinuousLinearMap)
  refine ⟨A, ?_, ?_⟩
  · intro q
    dsimp only [RetainedSimplex.chart]
    rw [AffineSimplex.chart_eq_tangentMap_add, map_add]
    change A q + e (AffineSimplex.chart (n + m) L 0) =
      A q + e (AffineSimplex.chart (n + m) L ((RetainedSimplex.join n m) (0,0)))
    simp only [show ((0 : EuclideanSpace ℝ (Fin n)), (0 : EuclideanSpace ℝ (Fin m))) = 0 from rfl,
      map_zero]
  · intro d hd
    have hsum : (∑ i, (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ.symm d) i) = 0 := by
      change (∑ i, d (σ i)) = 0
      rwa [Equiv.sum_comp]
    change e (AffineSimplex.chart (n + m) 0
      ((RetainedSimplex.join n m) (RetainedSimplex.coordinates n m σ d))) = d
    simp only [RetainedSimplex.coordinates, LinearEquiv.apply_symm_apply]
    rw [AffineSimplex.chart_coordinates (n + m) 0 hsum]
    simp only [e, ← LinearIsometryEquiv.piLpCongrLeft_symm, LinearIsometryEquiv.apply_symm_apply]

/-- Sobolev input to the proofs of Lemmas 5.7 and 5.8: every
constant directional derivative in the full retained/exterior chart belongs
to the actual weighted H¹ graph on each physical conditional fibre. This
includes uniformly compensated active directions. All integrability and
boundary approximation premises are proved, for either physical exponent
regime and also for zero-dimensional fibres. -/
theorem physical_chart_scores_H1 (p : Parameters) (n m : ℕ) (hn : 1 ≤ n) :
    ∃ U : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain (n + m).succPNat) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
          y ∈ gapAmbientDomain (n + m).succPNat},
        U y.val = p.val.1 * physicalAmbientGapEnergy p (n + m).succPNat y) ∧
      ∀ (σ : Equiv.Perm (Fin (n + m + 1)))
        (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
        (v : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)),
        let V := fun q => U (RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ q)
        Riesz1.WeightedSobolev.IsWeightedH1
          (ProperMarginalChart.conditionalMeasure p n m hn σ x)
          (AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ i, x.val i))
          (fun z => fderiv ℝ V (x.val,z) v)
          (gradient (fun z => fderiv ℝ V (x.val,z) v)) := by
  have : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :=
    Prod.continuousSMul
  classical
  obtain ⟨U, hU, hv, ht⟩ := physical_tensor_even_moments p n m hn
  refine ⟨U, hU, hv, fun σ x v => ?_⟩
  let L : ℝ := ((n + m : ℕ) + 1)
  let Q := RetainedSimplex.domain n m L
  let c := RetainedSimplex.chart n m L σ
  let V := fun q => U (c q)
  let μ := ProperMarginalChart.conditionalMeasure p n m hn σ x
  let w := fun q => (ProperMarginalChart.chartDensity p n m σ q).toReal
  obtain ⟨A, hca, _⟩ := chart_affine_tangent_internal n m L σ
  let a := c (0,0)
  have hc (q) : c q = A q + a := hca q
  have hc' : c = fun q => A q + a := funext hc
  have hsupp : ∀ᵐ z ∂μ, (x.val,z) ∈ Q := by
    filter_upwards [ConditionalEnergyMoments.physical_conditional_support p n m hn σ x] with z hz
    exact (Set.ext_iff.mp (RetainedSimplex.fibre_domain n m L x.property) z).mpr hz
  have hmaps (q) (hq : q ∈ Q) : c q ∈ gapAmbientDomain (n + m).succPNat :=
    ProperMarginalChart.simplex_ambient (n + m)
      ((RetainedSimplex.chart_mem_simplex n m L σ q).mpr hq)
  have hV : ContDiffOn ℝ ∞ V Q := by
    apply hU.comp _ hmaps
    rw [hc']
    exact (A.contDiff.add contDiff_const).contDiffOn
  have hw : ContDiff ℝ ∞ w := (MarginalHessian.physical_chart_density_smooth_compact p n m hn σ).1
  have he (q) (hq : q ∈ Q) : w q = Real.exp (-V q) := by
    have hmass := (RetainedSimplex.chart_mem_simplex n m L σ q).mpr hq
    dsimp only [w, ProperMarginalChart.chartDensity]
    rw [indicator_of_mem hq]
    dsimp only [ProperMarginalChart.density]
    rw [dite_eq_left hmass]
    rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)]
    dsimp only [V]
    rw [hv ⟨c q, hmaps q hq⟩]
    congr 1
    ring
  have hm (j k : ℕ+) : MemLp (fun z => ‖iteratedFDeriv ℝ j U (c (x.val,z))‖ ^ (k : ℕ)) 2 μ := by
    dsimp only [μ]
    rw [← DecayShort.PhysicalFibres.map_measure p n m hn σ x]
    apply (MeasurableEmbedding.subtype_coe
      (AffineSimplex.isOpen_chartDomain _ _).measurableSet).memLp_map_measure_iff.mpr
    exact ht σ x j k
  have h1 : MemLp (fun z => ‖fderiv ℝ U (c (x.val,z))‖) 2 μ := by
    simpa only [PNat.val_ofNat, pow_one, norm_iteratedFDeriv_one] using hm 1 1
  have h11 : MemLp (fun z => ‖fderiv ℝ U (c (x.val,z))‖ ^ 2) 2 μ := by
    simpa only [PNat.val_ofNat, norm_iteratedFDeriv_one] using hm 1 2
  have h2 : MemLp (fun z => ‖fderiv ℝ (fderiv ℝ U) (c (x.val,z))‖) 2 μ := by
    have heq (z) : ‖fderiv ℝ (fderiv ℝ U) (c (x.val,z))‖ =
        ‖iteratedFDeriv ℝ 2 U (c (x.val,z))‖ := by
      rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
    simpa only [PNat.val_ofNat, pow_one, ← heq] using hm 2 1
  have hb : ∀ᵐ z ∂μ,
      ‖fderiv ℝ V (x.val,z) v‖ ≤ ‖fderiv ℝ U (c (x.val,z))‖ * ‖A‖ * ‖v‖ ∧
      ‖gradient (fun y => fderiv ℝ V (x.val,y) v) z‖ ≤
        ‖fderiv ℝ (fderiv ℝ U) (c (x.val,z))‖ * ‖A‖ ^ 2 * ‖v‖ ∧
      ‖gradient (fun y => V (x.val,y)) z‖ ≤ ‖fderiv ℝ U (c (x.val,z))‖ * ‖A‖ := by
    filter_upwards [hsupp] with z hz
    have hUx : ContDiffAt ℝ 2 U (A (x.val,z) + a) := by
      rw [← hc]
      exact (hU.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain _).mem_nhds
        (hmaps _ hz))).of_le (show (2 : WithTop ℕ∞) ≤ ∞ by norm_num)
    simpa only [V, hc'] using affine_score_bounds_internal A a U x.val z v hUx
  have hFmeas : Measurable (fun z => fderiv ℝ V (x.val,z) v) :=
    (measurable_fderiv_apply_const ℝ V v).comp (measurable_const.prodMk measurable_id)
  have hgrad (f : EuclideanSpace ℝ (Fin m) → ℝ) : Measurable (gradient f) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin m))).symm.continuous.measurable.comp
      (measurable_fderiv ℝ f)
  have hF : MemLp (fun z => fderiv ℝ V (x.val,z) v) 2 μ :=
    ((h1.mul_const ‖A‖).mul_const ‖v‖).mono' hFmeas.aestronglyMeasurable
      (hb.mono fun _ hz => hz.1)
  have hG : MemLp (gradient (fun z => fderiv ℝ V (x.val,z) v)) 2 μ :=
    ((h2.mul_const (‖A‖ ^ 2)).mul_const ‖v‖).mono'
      (hgrad _).aestronglyMeasurable (hb.mono fun _ hz => hz.2.1)
  have hS : MemLp (fun z => (fderiv ℝ V (x.val,z) v) •
      gradient (fun y => V (x.val,y)) z) 2 μ := by
    apply ((h11.mul_const (‖A‖ ^ 2)).mul_const ‖v‖).mono'
      (hFmeas.smul (hgrad _)).aestronglyMeasurable
    filter_upwards [hb] with z hz
    change ‖(fderiv ℝ V (x.val,z) v) • gradient (fun y => V (x.val,y)) z‖ ≤ _
    rw [norm_smul]
    apply (mul_le_mul hz.1 hz.2.2 (norm_nonneg _) (by positivity)).trans_eq
    ring
  have hgraph := supported_score_graph_internal μ (RetainedSimplex.isOpen_domain n m L)
    hw (fun q => ENNReal.toReal_nonneg) hV he x.val v hsupp hF hG hS
  have hdomain : Prod.mk x.val ⁻¹' Q =
      AffineSimplex.chartDomain m (L - ∑ i, x.val i) := by
    exact RetainedSimplex.fibre_domain n m L x.property
  rw [hdomain] at hgraph
  exact hgraph

/-- Tangent-score form of the Sobolev input to the proofs of Lemmas 5.7 and 5.8. Every ambient mass-preserving directional
force has its actual exterior gradient in the conditional H¹ graph. -/
theorem physical_tangent_scores_H1 (p : Parameters) (n m : ℕ) (hn : 1 ≤ n) :
    ∃ U : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain (n + m).succPNat) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
          y ∈ gapAmbientDomain (n + m).succPNat},
        U y.val = p.val.1 * physicalAmbientGapEnergy p (n + m).succPNat y) ∧
      ∀ (σ : Equiv.Perm (Fin (n + m + 1)))
        (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
        (d : EuclideanSpace ℝ (Fin (n + m + 1))), (∑ i, d i) = 0 →
        let F := fun z => fderiv ℝ U
          (RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ (x.val,z)) d
        Riesz1.WeightedSobolev.IsWeightedH1
          (ProperMarginalChart.conditionalMeasure p n m hn σ x)
          (AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ i, x.val i)) F (gradient F) := by
  have : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :=
    Prod.continuousSMul
  classical
  obtain ⟨U, hU, hv, hgraph⟩ := physical_chart_scores_H1 p n m hn
  refine ⟨U, hU, hv, fun σ x d hd => ?_⟩
  let L : ℝ := ((n + m : ℕ) + 1)
  let c := RetainedSimplex.chart n m L σ
  let v := RetainedSimplex.coordinates n m σ d
  obtain ⟨A, hc, hA⟩ := chart_affine_tangent_internal n m L σ
  have hAv : A v = d := hA d hd
  have hderiv (q) : HasFDerivAt c A q := by
    have heq : c = fun q => A q + c (0,0) := funext hc
    rw [heq]
    exact A.hasFDerivAt.add_const _
  let V := fun q => U (c q)
  let F := fun z => fderiv ℝ U (c (x.val,z)) d
  have he (z) (hz : z ∈ AffineSimplex.chartDomain m (L - ∑ i, x.val i)) :
      fderiv ℝ V (x.val,z) v = F z := by
    have hq := (Set.ext_iff.mp (RetainedSimplex.fibre_domain n m L x.property) z).mpr hz
    have hmass := (RetainedSimplex.chart_mem_simplex n m L σ (x.val,z)).mpr hq
    have hdiff := (hU.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain _).mem_nhds
      (ProperMarginalChart.simplex_ambient _ hmass))).differentiableAt (by simp)
    have hval := (hdiff.hasFDerivAt.comp (x.val,z) (hderiv (x.val,z))).fderiv
    change fderiv ℝ V (x.val,z) = _ at hval
    rw [hval, ContinuousLinearMap.comp_apply, hAv]
  apply (hgraph σ x v).congr
  · filter_upwards [ConditionalEnergyMoments.physical_conditional_support p n m hn σ x] with z hz
    exact he z hz
  · filter_upwards [ConditionalEnergyMoments.physical_conditional_support p n m hn σ x] with z hz
    have hev : (fun y => fderiv ℝ V (x.val,y) v) =ᶠ[𝓝 z] F := by
      filter_upwards [(AffineSimplex.isOpen_chartDomain _ _).mem_nhds hz] with y hy
      exact he y hy
    exact congrArg ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin m))).symm)
      hev.fderiv_eq

/-- The literal compensated force of Subsection 5.1 satisfies
the H¹ requirement in the proofs of Lemmas 5.7 and 5.8. The representative is
beta times the energy, so the displayed force divides by beta.
The compensation vector is uniform. -/
theorem physical_compensated_force_H1 (p : Parameters) (n : ℕ+) (m : ℕ) :
    ∃ U : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain ((n : ℕ) + m).succPNat) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) //
          y ∈ gapAmbientDomain ((n : ℕ) + m).succPNat},
        U y.val = p.val.1 * physicalAmbientGapEnergy p ((n : ℕ) + m).succPNat y) ∧
      ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (i : Fin (n : ℕ)),
        let q := WithLp.toLp 2 (compensationVector n m)
        let F := fun z => p.val.1⁻¹ *
          (fderiv ℝ U (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z))
            (EuclideanSpace.single (i.castAdd m).castSucc 1) -
           fderiv ℝ U (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) q)
        Riesz1.WeightedSobolev.IsWeightedH1
          (ProperMarginalChart.conditionalMeasure p n m n.pos (Equiv.refl _) x)
          (AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ j, x.val j)) F (gradient F) := by
  classical
  obtain ⟨U, hU, hv, hg⟩ := physical_tangent_scores_H1 p n m n.pos
  refine ⟨U, hU, hv, fun x i => ?_⟩
  dsimp only
  let q := WithLp.toLp 2 (compensationVector n m)
  let e := EuclideanSpace.single (i.castAdd m).castSucc (1 : ℝ)
  let d := p.val.1⁻¹ • (e - q)
  have hsum : (∑ a, d a) = 0 := by
    simp only [d, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, ← Finset.mul_sum,
      Finset.sum_sub_distrib]
    have he : (∑ a, e a) = 1 := by simp [e, EuclideanSpace.single, PiLp.single_apply]
    rw [he, show (∑ a, q a) = 1 from compensationVector_sum n m, sub_self, mul_zero]
  have hgraph := hg (Equiv.refl _) x d hsum
  have heq : (fun z => fderiv ℝ U
      (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) d) =
      (fun z => p.val.1⁻¹ *
        (fderiv ℝ U (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) e -
         fderiv ℝ U (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) q)) := by
    funext z
    simp only [d, map_smul, map_sub, smul_eq_mul]
  rw [heq] at hgraph
  exact hgraph

end Riesz2.ConditionalForces
