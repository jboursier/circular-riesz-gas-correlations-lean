/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.LengthDerivativePart5
public import Riesz2.Frozen.External.ThermodynamicLogConcavity
public import Riesz2.ToMathlib.BoundedIntervalPoincare
public import Mathlib.Analysis.Convex.Continuous

/-!
# Length averaging

See Lemma 6.5. The density and average are the coarea objects defined in the code.
Smooth Poincaré is extended by clamping and weighted mollification, with coefficient
exactly twelve times the length variance. The quantitative implication assumes the
length derivative estimate.
-/

public section
noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff

namespace Riesz2.LengthAveraging

open LengthAveragingFibres LengthDerivative LengthVariance

/-- See Lemma 6.5 of the paper: the real-line version of the canonical length
density is its zero extension outside the possible length interval. This
bridge preserves the density at every interior point. -/
theorem real_length_density (p : Parameters) (n m : ℕ) (θ : PhysicalCutoff) (ε : ℝ) :
    ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧
      {x | 0 < f x} = Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ) ∧
      ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) ∧
      ContinuousOn f (Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ)) ∧
      (∀ L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ),
        ENNReal.ofReal (f L.val) = lengthDensity p n m θ ε L) ∧
      (lengthMeasure p n m θ ε).map Subtype.val =
        volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
  let U := Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ)
  let f : ℝ → ℝ := Function.extend (Subtype.val : U → ℝ)
    (fun L => (lengthDensity p n m θ ε L).toReal) (fun _ => 0)
  have hm : Measurable f := (MeasurableEmbedding.subtype_coe measurableSet_Ioo).measurable_extend
    (measurable_lengthDensity p n m θ ε).ennreal_toReal measurable_const
  have he (L : U) : f L.val = (lengthDensity p n m θ ε L).toReal :=
    Subtype.val_injective.extend_apply _ _ L
  have hz (x : ℝ) (hx : x ∉ U) : f x = 0 := by
    apply Function.extend_apply'
    rintro ⟨L,hL⟩
    exact hx (hL ▸ L.property)
  have hpos (x : ℝ) (hx : x ∈ U) : 0 < f x := by
    rw [he ⟨x,hx⟩]
    exact ENNReal.toReal_pos (lengthDensity_valid p n m θ ε _).1
      (lengthDensity_valid p n m θ ε _).2
  have hnonneg (x : ℝ) : 0 ≤ f x := by
    by_cases hx : x ∈ U
    · exact (hpos x hx).le
    · rw [hz x hx]
  have hsupport : {x | 0 < f x} = U := by
    ext x
    constructor
    · intro hx
      by_contra h
      change 0 < f x at hx
      rw [hz x h] at hx
      exact lt_irrefl _ hx
    · exact hpos x
  have hlog : ConcaveOn ℝ U (fun x => Real.log (f x)) := by
    apply (lengthDensity_logConcave p n m θ ε).congr
    intro x hx
    exact congrArg Real.log (he ⟨x,hx⟩).symm
  have hcont : ContinuousOn f U := by
    apply (Real.continuous_exp.comp_continuousOn (hlog.continuousOn isOpen_Ioo)).congr
    intro x hx
    exact (Real.exp_log (hpos x hx)).symm
  have hof (L : U) : ENNReal.ofReal (f L.val) = lengthDensity p n m θ ε L := by
    rw [he,ENNReal.ofReal_toReal (lengthDensity_valid p n m θ ε L).2]
  refine ⟨f,hm,hnonneg,hsupport,hsupport ▸ hlog,hcont,hof,?_⟩
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg measurable_subtype_coe,
    lengthMeasure,lintegral_withDensity_eq_lintegral_mul _
      (measurable_lengthDensity p n m θ ε) (show Measurable (fun L : U => g L.val) from hg.comp measurable_subtype_coe)]
  have hdensity : lengthDensity p n m θ ε = fun L => ENNReal.ofReal (f L.val) := funext fun L => (hof L).symm
  change (∫⁻ L : U, lengthDensity p n m θ ε L * g L.val ∂volume.comap Subtype.val) = _
  rw [hdensity]
  rw [lintegral_subtype_comap measurableSet_Ioo (fun x => ENNReal.ofReal (f x) * g x),
    lintegral_withDensity_eq_lintegral_mul _ (hm.ennreal_ofReal) hg]
  change (∫⁻ x in U, ENNReal.ofReal (f x) * g x) = ∫⁻ x, ENNReal.ofReal (f x) * g x
  apply setLIntegral_eq_of_support_subset
  intro x hx
  by_contra h
  exact hx (by simp only [hz x h,ENNReal.ofReal_zero,zero_mul])

/-- See Lemma 6.5 of the paper: the specified every-length
expectation is bounded, so all its first and second moments are finite. -/
theorem averagedObservable_bounded (p : Parameters) (n m : ℕ) (θ : PhysicalCutoff) (ε : ℝ)
    (G : BlockObservable n.succPNat) :
    ∃ B : ℝ, ∀ L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ),
      |averagedObservable p n m θ ε G L| ≤ B := by
  let N : ℝ := ((n+1+m : ℕ)+1 : ℝ)
  obtain ⟨K,hK⟩ := G.property
  let B := (K : ℝ)*N + |G.val 0|
  refine ⟨B, fun L => ?_⟩
  have hB (x : EuclideanSpace ℝ (Fin (n+1)))
      (hx : x ∈ AffineSimplex.massSimplex n L.val) :
      ‖G.val (WithLp.ofLp x)‖ ≤ B := by
    have hcoord (i : Fin (n+1)) : |x i| ≤ N := by
      rw [abs_of_pos (hx.1 i)]
      exact (Finset.single_le_sum (fun j _ => (hx.1 j).le) (Finset.mem_univ i)).trans
        (hx.2.trans_le L.property.2.le)
    have hnorm : ‖WithLp.ofLp x‖ ≤ N := (pi_norm_le_iff_of_nonneg (by dsimp [N]; positivity)).mpr
      (fun i => by simpa only [Real.norm_eq_abs] using hcoord i)
    have h := hK.norm_sub_le (WithLp.ofLp x) 0
    simp only [sub_zero] at h
    calc
      _ ≤ ‖G.val (WithLp.ofLp x)-G.val 0‖ + ‖G.val 0‖ :=
        norm_le_norm_sub_add _ _
      _ ≤ (K : ℝ)*N + |G.val 0| := add_le_add
        (h.trans (mul_le_mul_of_nonneg_left hnorm K.property)) (by rw [Real.norm_eq_abs])
  change |∫ x, G.val (WithLp.ofLp x) ∂fibreKernel p n m θ ε L| ≤ B
  rw [← Real.norm_eq_abs]
  have hb : ∀ᵐ x ∂fibreKernel p n m θ ε L, ‖G.val (WithLp.ofLp x)‖ ≤ B := by
    filter_upwards [mem_simplex_ae_fibre p n m θ ε L] with x hx
    exact hB x hx
  simpa using norm_integral_le_of_norm_le_const hb

/-- See Lemma 6.5 of the paper: the exact smooth Poincaré
coefficient applies to the bounded, locally C¹ physical fibre expectation.
The positive-variance premise belongs to this internal analytic helper. -/
theorem averagedObservable_poincare_internal
    (hLC : External.ThermodynamicLogConcavity)
    (p : Parameters) (n m : ℕ) (θ : PhysicalCutoff) (ε : ℝ)
    (G : BlockObservable n.succPNat) (M : ℝ → ℝ)
    (hM : ∀ L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ),
      M L.val = averagedObservable p n m θ ε G L)
    (hMC : ContDiffOn ℝ 1 M (Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ)))
    (hd : MemLp (fun L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ) => deriv M L.val)
      2 (lengthMeasure p n m θ ε))
    (hv : 0 < (Riesz1.variance (activeMeasure p n m θ ε) (fun x => ∑ i, x i)
      (memLp_one_iff_integrable.mp (length_memLp p n m θ ε 1))).toReal) :
    MemLp (averagedObservable p n m θ ε G) 2 (lengthMeasure p n m θ ε) ∧
      (∫ L, (averagedObservable p n m θ ε G L -
        ∫ K, averagedObservable p n m θ ε G K ∂lengthMeasure p n m θ ε)^2
        ∂lengthMeasure p n m θ ε) ≤
      12 * (Riesz1.variance (activeMeasure p n m θ ε) (fun x => ∑ i, x i)
        (memLp_one_iff_integrable.mp (length_memLp p n m θ ε 1))).toReal *
          (eLpNorm (fun L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ) => deriv M L.val)
            2 (lengthMeasure p n m θ ε)).toReal^2 := by
  let U := Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ)
  let ν := lengthMeasure p n m θ ε
  have : IsProbabilityMeasure ν := lengthMeasure_probability p n m θ ε
  obtain ⟨f,hfm,hfn,hpos,hlog,hfc,hfval,hlaw⟩ := real_length_density p n m θ ε
  let μ := volume.withDensity (fun x => ENNReal.ofReal (f x))
  have hμ : ν.map Subtype.val = μ := hlaw
  have : IsProbabilityMeasure μ := hμ ▸ (inferInstance : IsProbabilityMeasure (ν.map Subtype.val))
  have : IsProbabilityMeasure (activeMeasure p n m θ ε) :=
    (ProperMarginalChart.activeTiltedGapLaw_density_valid p n.succPNat m (by simp; omega) θ ε true).2.2.1
  have hμactive : (activeMeasure p n m θ ε).map (fun x => ∑ i, x i) = μ :=
    (lengthMeasure_map p n m θ ε).symm.trans hμ
  have hsum : Measurable (fun x : EuclideanSpace ℝ (Fin (n+1)) => ∑ i, x i) :=
    (continuous_finsetSum _ (fun i _ => PiLp.continuous_apply 2 _ i)).measurable
  have hid : MemLp (fun x : ℝ => x) 2 μ := by
    rw [← hμactive]
    exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable hsum.aemeasurable).mpr
      (length_memLp p n m θ ε 2)
  have hV : Riesz1.variance μ (fun x : ℝ => x) (hid.integrable one_le_two) =
      Riesz1.variance (activeMeasure p n m θ ε) (fun x => ∑ i, x i)
        (memLp_one_iff_integrable.mp (length_memLp p n m θ ε 1)) := by
    exact Riesz1.variance_eq_of_map (activeMeasure p n m θ ε) μ
      hsum.aemeasurable hμactive hid (length_memLp p n m θ ε 2)
  let v := (Riesz1.variance μ (fun x : ℝ => x) (hid.integrable one_le_two)).toReal
  have hv' : 0 < v := by dsimp only [v]; rw [hV]; exact hv
  have hvar : (∫⁻ x, ENNReal.ofReal ((x-∫ y, y ∂μ)^2) ∂μ) = ENNReal.ofReal v := by
    change Riesz1.variance μ (fun x : ℝ => x) (hid.integrable one_le_two) = _
    rw [Riesz1.variance_eq_ofReal_integral_sq μ _ hid]
    dsimp [v]
    rw [Riesz1.variance_eq_ofReal_integral_sq μ _ hid,ENNReal.toReal_ofReal
      (integral_nonneg fun x => sq_nonneg _)]
  obtain ⟨c,_hc,hLC⟩ := hLC
  have hmass : (∫⁻ x, ENNReal.ofReal (f x)) = 1 := by
    simpa only [μ,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
      using (inferInstance : IsProbabilityMeasure μ).measure_univ
  have hP := (hLC f hfm hfn hlog hmass _ v (hid.integrable one_le_two) rfl hv' hvar).2
  have hsupp : ∀ᵐ x ∂μ, x ∈ U := by
    rw [← hμ]
    exact (ae_map_iff measurable_subtype_coe.aemeasurable measurableSet_Ioo).mpr
      (ae_of_all _ fun L => L.property)
  have hMm : AEStronglyMeasurable M μ := by
    have hm := hMC.continuousOn.aestronglyMeasurable measurableSet_Ioo (μ := μ)
    rwa [Measure.restrict_eq_self_of_ae_mem hsupp] at hm
  have hdμ : MemLp (deriv M) 2 μ := by
    rw [← hμ]
    exact (memLp_map_measure_iff (measurable_deriv M).aestronglyMeasurable
      measurable_subtype_coe.aemeasurable).mpr hd
  obtain ⟨B,hB⟩ := averagedObservable_bounded p n m θ ε G
  have hbound : ∀ x ∈ U, |M x| ≤ B := fun x hx => by rw [hM ⟨x,hx⟩]; exact hB _
  have hP' (u : ℝ → ℝ) (hu : ContDiff ℝ ∞ u) (hu2 : MemLp u 2 μ)
      (hdu : MemLp (deriv u) 2 μ) :
      (∫ x, (u x-∫ y, u y ∂μ)^2 ∂μ) ≤ 12*v*∫ x, (deriv u x)^2 ∂μ := by
    have h := hP u hu hu2 hdu
    change (∫⁻ x, ENNReal.ofReal ((u x-∫ y, u y ∂μ)^2) ∂μ) ≤
      ENNReal.ofReal (12*v) * ∫⁻ x, ENNReal.ofReal ((deriv u x)^2) ∂μ at h
    have hcent : Integrable (fun x => (u x-∫ y, u y ∂μ)^2) μ :=
      (hu2.sub (memLp_const _)).integrable_sq
    rw [← ofReal_integral_eq_lintegral_ofReal
        hcent (ae_of_all _ fun x => sq_nonneg _),
      ← ofReal_integral_eq_lintegral_ofReal hdu.integrable_sq (ae_of_all _ fun x => sq_nonneg _),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 12*v)] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  obtain ⟨hM2,hineq⟩ := BoundedIntervalPoincare.on_open_interval (lo := 0)
    (hi := ((n+1+m : ℕ)+1 : ℝ)) (by positivity) hMC hfc
    (fun x hx => by rw [← hpos] at hx; exact hx) hbound (by positivity : 0 ≤ 12*v)
    hsupp hMm hdμ hP'
  have hML2 : MemLp (fun L : U => M L.val) 2 ν :=
    (memLp_map_measure_iff (hμ.symm ▸ hMm) measurable_subtype_coe.aemeasurable).mp (hμ.symm ▸ hM2)
  have hG2 : MemLp (averagedObservable p n m θ ε G) 2 ν :=
    (memLp_congr_ae (ae_of_all _ hM)).mp hML2
  have hmean : (∫ x, M x ∂μ) = ∫ L, averagedObservable p n m θ ε G L ∂ν := by
    rw [← hμ,integral_map measurable_subtype_coe.aemeasurable (hμ.symm ▸ hMm)]
    exact integral_congr_ae (ae_of_all _ hM)
  have hleft : (∫ x, (M x-∫ y, M y ∂μ)^2 ∂μ) =
      ∫ L, (averagedObservable p n m θ ε G L-
        ∫ K, averagedObservable p n m θ ε G K ∂ν)^2 ∂ν := by
    rw [hmean,← hμ,integral_map measurable_subtype_coe.aemeasurable
      (((hμ.symm ▸ hMm).sub aestronglyMeasurable_const).pow 2)]
    exact integral_congr_ae (ae_of_all _ fun L => by dsimp only; rw [hM L])
  have hright : (∫ x, (deriv M x)^2 ∂μ) =
      (eLpNorm (fun L : U => deriv M L.val) 2 ν).toReal^2 := by
    have he : (∫ x, (deriv M x)^2 ∂μ) = ∫ L : U, (deriv M L.val)^2 ∂ν := by
      rw [← hμ]
      exact integral_map measurable_subtype_coe.aemeasurable
        (((measurable_deriv M).pow_const 2).aestronglyMeasurable)
    rw [he,Riesz1.eLpNorm_two_toReal_eq_sqrt_integral_sq hd,
      Real.sq_sqrt (integral_nonneg fun L => sq_nonneg _)]
  rw [hleft,hright] at hineq
  refine ⟨hG2, ?_⟩
  simpa only [v,hV] using hineq

/-- Numerical square-root and polynomial bookkeeping for Lemma 6.5. The exponential prefactor is absorbed with half
of its original decay constant. -/
theorem averaging_rate_internal {x τ ε κd κv A B c δ V d W DA DB : ℝ}
    (hx : 1 ≤ x) (hε : 0 < ε) (hκv : 0 < κv) (hA : 0 < A) (hB : 0 < B)
    (_hc : 0 < c) (_hδ : 0 < δ) (_hV : 0 ≤ V) (hd : 0 ≤ d) (hW : 0 ≤ W)
    (hDA : 0 ≤ DA) (hDB : 0 ≤ DB)
    (hvar : V ≤ B*x^(τ+κv*ε)) (hpoincare : W ≤ 12*V*d^2)
    (hder : d ≤ A*x^(κd*ε-τ)*DA + A*Real.exp (-c*x^δ)*DB)
    {Q : ℝ} (hQ : 0 ≤ Q)
    (htail : x^(τ/2+κv*ε)*Real.exp (-c*x^δ) ≤ Q*Real.exp (-(c/2)*x^δ)) :
    Real.sqrt W ≤ (Real.sqrt (12*B)*A)*(1+Q) *
      x^((κd+κv)*ε-τ/2)*DA +
      (Real.sqrt (12*B)*A)*(1+Q)*Real.exp (-(c/2)*x^δ)*DB := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  let q := τ/2+κv*ε
  let H := Real.sqrt (12*B)
  have hH : 0 < H := Real.sqrt_pos.mpr (by positivity)
  have hp : 0 < x^q := Real.rpow_pos_of_pos hx0 _
  have hvar' : 12*V ≤ (H*x^q)^2 := by
    have he : (H*x^q)^2 = 12*B*x^(τ+2*κv*ε) := by
      rw [mul_pow,Real.sq_sqrt (by positivity : 0 ≤ 12*B),← Real.rpow_natCast,← Real.rpow_mul hx0.le]
      congr 2
      dsimp only [q]
      ring
    rw [he]
    have ht := Real.rpow_le_rpow_of_exponent_le hx
      (show τ+κv*ε ≤ τ+2*κv*ε by nlinarith)
    nlinarith [mul_le_mul_of_nonneg_left ht hB.le]
  have hroot : Real.sqrt W ≤ H*x^q*d := by
    have hs := Real.sq_sqrt hW
    have hh : 0 ≤ H*x^q*d := by positivity
    have hmul := mul_le_mul_of_nonneg_right hvar' (sq_nonneg d)
    nlinarith [Real.sqrt_nonneg W]
  have he : x^q*x^(κd*ε-τ) = x^((κd+κv)*ε-τ/2) := by
    rw [← Real.rpow_add hx0]
    congr 1
    dsimp only [q]
    ring
  calc
    _ ≤ H*x^q*(A*x^(κd*ε-τ)*DA + A*Real.exp (-c*x^δ)*DB) :=
      hroot.trans (mul_le_mul_of_nonneg_left hder (by positivity))
    _ = H*A*(x^q*x^(κd*ε-τ))*DA + H*A*(x^q*Real.exp (-c*x^δ))*DB := by ring
    _ ≤ H*A*x^((κd+κv)*ε-τ/2)*DA + H*A*(Q*Real.exp (-(c/2)*x^δ))*DB := by
      rw [he]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left htail (by positivity)) hDB)
    _ ≤ _ := by
      have h1 : H*A ≤ H*A*(1+Q) := by nlinarith [mul_nonneg (mul_pos hH hA).le hQ]
      have h2 : H*A*Q ≤ H*A*(1+Q) := by nlinarith [mul_pos hH hA]
      calc
        _ = H*A*x^((κd+κv)*ε-τ/2)*DA + H*A*Q*Real.exp (-(c/2)*x^δ)*DB := by ring
        _ ≤ _ := add_le_add
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (by positivity)) hDA)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le) hDB)

/-- The length-averaging estimate of Lemma 6.5 follows from the derivative
estimate in its proof. The derivative premise includes local absolute
continuity, the fibre representative and both derivative norms. C¹ regularity
comes from the proper-block regularity theorem. The loss is fixed before
epsilon and the tail power before the compact temperature interval. -/
theorem length_averaging_from_derivative_internal
    (hRig : External.LongRangeRigidityLocallyUniform)
    (hLC : External.ThermodynamicLogConcavity)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (K κd εd : ℝ) (_hK : 1 < K) (hκd : 0 < κd) (hεd : 0 < εd)
    (hDerivative : ∀ ε : ℝ, 0 < ε → ε ≤ εd → ∃ δ : ℝ, 0 < δ ∧
      ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
        ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
          ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
          ∀ n m : ℕ, 1 ≤ n → 4*(n+1) ≤ n+1+m+1 →
            (n+1 : ℝ)^(2/s) ≤ ((n+1+m : ℕ)+1 : ℝ) →
          ∀ G : BlockObservable n.succPNat, ∀ J : Finset (Fin (n+1)),
            DependsOnBlockCoordinates G J →
            (∀ i ∈ J, |(i.val : ℝ)+1-(n+1 : ℝ)/2| ≤ (n+1 : ℝ)/4) →
          ∃ M : ℝ → ℝ,
            (∀ L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ),
              M L.val = averagedObservable p n m θ ε G L) ∧
            (∀ u v : ℝ, u ∈ Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ) →
              v ∈ Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ) →
              AbsolutelyContinuousOnInterval M u v) ∧
            MemLp (fun L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ) => deriv M L.val)
              2 (lengthMeasure p n m θ ε) ∧
            (eLpNorm (fun L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ) => deriv M L.val)
              2 (lengthMeasure p n m θ ε)).toReal ≤
              C*(n+1 : ℝ)^(κd*ε-min s 1)*restrictedBlockDerivativeNorm G J
                (goodBlockEvent s n.succPNat (n+1+m).succPNat (K*ε)) +
              C*Real.exp (-c*(n+1 : ℝ)^δ)*blockDerivativeNorm G) :
    ∃ κ εstar : ℝ, 0 < κ ∧ 0 < εstar ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ εstar → ∃ δ : ℝ, 0 < δ ∧
      ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
        ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
          ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
          ∀ n m : ℕ, 1 ≤ n → 4*(n+1) ≤ n+1+m+1 →
            (n+1 : ℝ)^(2/s) ≤ ((n+1+m : ℕ)+1 : ℝ) →
          let ν := activeMeasure p n m θ ε
          let V := Riesz1.variance ν (fun x => ∑ i, x i)
            (memLp_one_iff_integrable.mp (length_memLp p n m θ ε 1))
          |(∫ x, ∑ i, x i ∂ν)-(n+1 : ℝ)| ≤ C*Real.exp (-c*(n+1 : ℝ)^δ) ∧
            ENNReal.ofReal (c*(n+1 : ℝ)^(min s 1)) ≤ V ∧
            V ≤ ENNReal.ofReal (C*(n+1 : ℝ)^(min s 1+κ*ε)) ∧
          ∀ G : BlockObservable n.succPNat, ∀ J : Finset (Fin (n+1)),
            DependsOnBlockCoordinates G J →
            (∀ i ∈ J, |(i.val : ℝ)+1-(n+1 : ℝ)/2| ≤ (n+1 : ℝ)/4) →
          ∃ hG : MemLp (averagedObservable p n m θ ε G) 2 (lengthMeasure p n m θ ε),
            Real.sqrt ((Riesz1.variance (lengthMeasure p n m θ ε)
              (averagedObservable p n m θ ε G) (by have := lengthMeasure_probability p n m θ ε; exact hG.integrable one_le_two)).toReal) ≤
              C*(n+1 : ℝ)^(κ*ε-min s 1/2)*restrictedBlockDerivativeNorm G J
                (goodBlockEvent s n.succPNat (n+1+m).succPNat (K*ε)) +
              C*Real.exp (-c*(n+1 : ℝ)^δ)*blockDerivativeNorm G := by
  obtain ⟨κv,εv,hκv,hεv,hVariance⟩ := length_averaging_variance hRig s hs hs1
  refine ⟨κd+κv,min εd εv,add_pos hκd hκv,lt_min hεd hεv,fun ε hε hεsmall => ?_⟩
  obtain ⟨δd,hδd,hD⟩ := hDerivative ε hε (hεsmall.trans (min_le_left _ _))
  obtain ⟨δv,hδv,hV⟩ := hVariance ε hε (hεsmall.trans (min_le_right _ _))
  refine ⟨min δd δv,lt_min hδd hδv,fun βlo βhi hlo hle θ => ?_⟩
  obtain ⟨A,a,hA,ha,hDb⟩ := hD βlo βhi hlo hle θ
  obtain ⟨B,b,hB,hb,hVb⟩ := hV βlo βhi hlo hle θ
  obtain ⟨Q,hQ,hQb⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := min s 1/2+κv*ε) hδd (show a/2 < a by linarith)
  let H := Real.sqrt (12*B)*A*(1+Q)
  have hH : 0 < H := by dsimp only [H]; positivity
  let C := B+H
  let c := min b (a/2)
  have hc : 0 < c := lt_min hb (by positivity)
  refine ⟨C,c,add_pos hB hH,hc,fun p hps hpl hph n m hn hsize hscale => ?_⟩
  intro ν V
  obtain ⟨hmean,hlower,hupper,_hlog⟩ := hVb p hps hpl hph n m hn hsize hscale
  have hx : 1 ≤ (n+1 : ℝ) := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have htail {d z : ℝ} (hd : min δd δv ≤ d) (hz : c ≤ z) :
      Real.exp (-z*(n+1 : ℝ)^d) ≤ Real.exp (-c*(n+1 : ℝ)^(min δd δv)) := by
    apply Real.exp_le_exp.mpr
    have ht := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx hd) hc.le
    have hz' := mul_le_mul_of_nonneg_right hz (Real.rpow_nonneg (show 0 ≤ (n+1 : ℝ) by positivity) d)
    linarith
  refine ⟨hmean.trans ?_,?_,hupper.trans ?_,fun G J hJ hmiddle => ?_⟩
  · exact mul_le_mul (le_add_of_nonneg_right hH.le)
      (htail (min_le_right _ _) (min_le_left _ _)) (Real.exp_pos _).le (add_pos hB hH).le
  · apply le_trans (ENNReal.ofReal_le_ofReal ?_) hlower
    exact mul_le_mul_of_nonneg_right (min_le_left b (a/2)) (by positivity)
  · apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul (le_add_of_nonneg_right hH.le)
      (Real.rpow_le_rpow_of_exponent_le hx (by nlinarith)) (by positivity) (add_pos hB hH).le
  · have hVfinite : V < ⊤ := hupper.trans_lt ENNReal.ofReal_lt_top
    have hVpos : 0 < V := lt_of_lt_of_le
      (ENNReal.ofReal_pos.mpr (mul_pos hb (Real.rpow_pos_of_pos (by positivity) _))) hlower
    have hVr : 0 < V.toReal := ENNReal.toReal_pos hVpos.ne' hVfinite.ne
    obtain ⟨F,hF,_hFAC,hdF,hbdF⟩ := hDb p hps hpl hph n m hn hsize hscale G J hJ hmiddle
    have hj : Fin.last n ∉ J := by
      intro h
      have hh := hmiddle (Fin.last n) h
      simp only [Fin.val_last] at hh
      have hab := le_abs_self (((n : ℝ)+1)-(n+1 : ℝ)/2)
      have hpos : 0 < (n+1 : ℝ) := by positivity
      linarith
    obtain ⟨M,hM,hMC,_hMAC⟩ := proper_averagedObservable_C1 p n m θ ε J (Fin.last n) hj G hJ
    have he : (fun L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ) => deriv M L.val) =
        (fun L => deriv F L.val) := funext fun L => averagedObservable_deriv_eq_internal
          p n m θ ε G hM hF L
    have hdM : MemLp (fun L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ) => deriv M L.val)
        2 (lengthMeasure p n m θ ε) := he.symm ▸ hdF
    obtain ⟨hG,hP⟩ := averagedObservable_poincare_internal hLC p n m θ ε G M hM hMC hdM hVr
    refine ⟨hG,?_⟩
    have : IsProbabilityMeasure (lengthMeasure p n m θ ε) := lengthMeasure_probability p n m θ ε
    rw [Riesz1.variance_eq_ofReal_integral_sq _ _ hG,
      ENNReal.toReal_ofReal (integral_nonneg fun L => sq_nonneg _)]
    have hupperR : V.toReal ≤ B*(n+1 : ℝ)^(min s 1+κv*ε) :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hupper
    have hDA : 0 ≤ restrictedBlockDerivativeNorm G J
        (goodBlockEvent s n.succPNat (n+1+m).succPNat (K*ε)) := by
      unfold restrictedBlockDerivativeNorm; positivity
    have hDB : 0 ≤ blockDerivativeNorm G := by unfold blockDerivativeNorm; positivity
    have hr := averaging_rate_internal hx hε hκv hA hB ha hδd hVr.le
      ENNReal.toReal_nonneg (integral_nonneg fun L => sq_nonneg _) hDA hDB
      hupperR hP (by simpa only [he] using hbdF) hQ (hQb (n+1 : ℝ) hx)
    apply hr.trans
    apply add_le_add
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB.le) (by positivity)) hDA
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul (le_add_of_nonneg_left hB.le)
          (htail (min_le_left _ _) (min_le_right _ _)) (Real.exp_pos _).le (add_pos hB hH).le) hDB

end Riesz2.LengthAveraging
