/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.ScalarPoisson
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Square integrability from a square integrable gradient

On a bounded strictly convex Gibbs domain with the collision barrier,
an interior smooth function with finite gradient norm has finite value norm.
Bounded sine approximations, Poincaré, a positive mass sublevel set and Fatou
give the result without assuming integrability of the original function.
-/

public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace Riesz2.GradientSquareIntegrability

/-- A positive mass region on which approximants are bounded pins their means.
This implication is independent of any differential structure. -/
theorem second_moment_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {f : X → ℝ}
    (hf : MemLp f 2 μ) {A : Set X} (hA : MeasurableSet A)
    (hpos : 0 < μ A) {K E : ℝ} (hK : 0 ≤ K)
    (hb : ∀ x ∈ A, |f x| ≤ K)
    (hv : (∫ x, (f x - ∫ y, f y ∂μ)^2 ∂μ) ≤ E) :
    (∫ x, f x^2 ∂μ) ≤ (1 + 2 / (μ A).toReal) * E + 2*K^2 := by
  let c := ∫ x, f x ∂μ
  have hp : 0 < (μ A).toReal := ENNReal.toReal_pos hpos.ne' (measure_ne_top μ A)
  have hc : Integrable (fun x => (f x-c)^2) μ := (hf.sub (memLp_const c)).integrable_sq
  have hi := integral_mono_ae (μ := μ.restrict A) (integrable_const (c^2))
    ((hc.restrict).const_mul 2 |>.add (integrable_const (2*K^2)))
    ((ae_restrict_mem hA).mono fun x hx => by
      have hh := hb x hx
      have hs : f x^2 ≤ K^2 := by nlinarith [sq_abs (f x), abs_nonneg (f x)]
      change c^2 ≤ 2*(f x-c)^2+2*K^2
      nlinarith only [hs, sq_nonneg (2*f x-c)])
  change (∫ _x in A, c^2 ∂μ) ≤
    ∫ x in A, 2*(f x-c)^2+2*K^2 ∂μ at hi
  rw [integral_const, integral_add (hc.restrict.const_mul 2) (integrable_const (2*K^2)),
    integral_const_mul, integral_const] at hi
  simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul] at hi
  have hs : (∫ x in A, (f x-c)^2 ∂μ) ≤ ∫ x, (f x-c)^2 ∂μ :=
    setIntegral_le_integral hc (ae_of_all _ fun x => sq_nonneg _) 
  have hmean : c^2 ≤ 2*E/(μ A).toReal + 2*K^2 := by
    have hmul : (c^2-2*K^2)*(μ A).toReal ≤ 2*E := by nlinarith
    have hh := (le_div_iff₀ hp).mpr hmul
    linarith
  have heq := Riesz1.WeightedSobolev.integral_sub_mean_sq hf
  dsimp only [c] at hmean
  rw [heq] at hv
  have he : 2*E/(μ A).toReal = (2/(μ A).toReal)*E := by ring
  rw [he] at hmean
  nlinarith

/-- Uniform variance bounds and local boundedness of approximants imply a
finite second moment for their pointwise limit. No first moment is presumed. -/
theorem memLp_of_variance_approximants {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] (f : X → ℝ) (hm : Measurable f)
    (g : ℕ → X → ℝ) (hg : ∀ k, MemLp (g k) 2 μ)
    (hb : ∀ k x, |g k x| ≤ |f x|)
    (ht : ∀ x, Tendsto (fun k => g k x) atTop (𝓝 (f x)))
    (E : ℝ) (hE : 0 ≤ E)
    (hv : ∀ k, (∫ x, (g k x - ∫ y, g k y ∂μ)^2 ∂μ) ≤ E) :
    MemLp f 2 μ := by
  obtain ⟨K, hK⟩ := exists_pos_preimage_ball (μ := μ) f 0 (NeZero.ne μ)
  let A := f ⁻¹' Metric.ball 0 (K : ℝ)
  have hA : MeasurableSet A := hm measurableSet_ball
  have hpos : 0 < μ A := hK
  let B := (1+2/(μ A).toReal)*E+2*(K : ℝ)^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbound (k : ℕ) : (∫ x, g k x^2 ∂μ) ≤ B := by
    apply second_moment_bound (hg k) hA hpos (Nat.cast_nonneg K) _ (hv k)
    intro x hx
    have hx' : |f x| < (K : ℝ) := by simpa only [A, mem_preimage,
      Metric.mem_ball, Real.dist_eq, sub_zero] using hx
    exact (hb k x).trans hx'.le
  have hn (k : ℕ) : eLpNorm (g k) 2 μ ≤ ENNReal.ofReal (Real.sqrt B) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) (hg k).aestronglyMeasurable]
    have hh : (∫⁻ x, ‖g k x‖ₑ ^ (2 : ℕ) ∂μ) = ENNReal.ofReal (∫ x, g k x^2 ∂μ) := by
      rw [ofReal_integral_eq_lintegral_ofReal (hg k).integrable_sq
        (ae_of_all _ fun x => sq_nonneg _)]
      apply lintegral_congr
      intro x
      simp [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg (g k x)), sq_abs]
    norm_num only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
    rw [hh, ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun x => sq_nonneg _)
      (by norm_num), Real.sqrt_eq_rpow]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow
      (integral_nonneg fun x => sq_nonneg _) (hbound k) (by norm_num))
  exact lt_of_le_of_lt (Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall hn) (fun k => (hg k).aestronglyMeasurable)
    hm.aestronglyMeasurable (ae_of_all _ ht)) ENNReal.ofReal_lt_top

/-- On a bounded strictly convex Gibbs domain with the intrinsic collision
barrier, a measurable interior smooth function with square integrable
gradient is itself square integrable. No value norm or first moment is an input. -/
theorem memLp_of_gradient {d : ℕ} (hd : 1 ≤ d)
    {U : Set (EuclideanSpace ℝ (Fin d))} {μ : Measure (EuclideanSpace ℝ (Fin d))}
    {V : EuclideanSpace ℝ (Fin d) → ℝ}
    (hU : IsOpen U) (hB : Bornology.IsBounded U) (hne : U.Nonempty) (hc : Convex ℝ U)
    (hV : IsEuclideanGibbsPotential volume μ U V) {C κ : ℝ} (hC : 0 ≤ C) (hκ : 0 < κ)
    (hH : ∀ x ∈ U, ∀ u, κ*‖u‖^2 ≤ fderiv ℝ (fderiv ℝ V) x u u)
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹^2-C ≤
      ‖gradient V x‖^2/4-Laplacian.laplacian V x/2)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hm : Measurable f)
    (hs : ContDiffOn ℝ ∞ f U) (hdf : MemLp (gradient f) 2 μ) :
    MemLp f 2 μ := by
  let : NeZero d := ⟨by omega⟩
  have := IntrinsicScalarCore.probability hV
  let R := fun k : ℕ => (k+1 : ℝ)
  let g := fun k x => R k * Real.sin (f x / R k)
  have hR (k : ℕ) : 0 < R k := by dsimp [R]; positivity
  have hgb (k : ℕ) (x) : |g k x| ≤ |f x| := by
    dsimp only [g]
    rw [abs_mul, abs_of_pos (hR k)]
    have hh := mul_le_mul_of_nonneg_left (Real.abs_sin_le_abs (x := f x/R k)) (hR k).le
    simpa only [abs_div, abs_of_pos (hR k), mul_div_cancel₀ _ (hR k).ne'] using hh
  have hgm (k : ℕ) : MemLp (g k) 2 μ := by
    apply MemLp.of_bound ((hm.div_const (R k)).sin.const_mul (R k)).aestronglyMeasurable (R k)
    exact ae_of_all _ fun x => by
      rw [norm_mul, Real.norm_of_nonneg (hR k).le, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (hR k).le (Real.abs_sin_le_one _)
  have hgs (k : ℕ) : ContDiffOn ℝ ∞ (g k) U :=
    contDiffOn_const.mul ((hs.div_const (R k)).sin)
  have hgrad (k : ℕ) : gradient (g k) =ᵐ[μ] fun x =>
      Real.cos (f x / R k) • gradient f x := by
    filter_upwards [IntrinsicScalarCore.supported hU hV] with x hx
    have hfd := (hs.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have hdg : HasFDerivAt (g k) (Real.cos (f x/R k) • fderiv ℝ f x) x := by
      convert ((hfd.hasFDerivAt.const_mul (R k)⁻¹).sin.const_mul (R k)) using 1
      · funext y
        dsimp [g]
        rw [div_eq_mul_inv, mul_comm (f y)]
      · simp only [smul_smul]
        rw [mul_comm ((R k)⁻¹) (f x), ← div_eq_mul_inv]
        congr 1
        field_simp [ne_of_gt (hR k)]
    unfold gradient
    rw [hdg.fderiv]
    simp only [map_smul]
  have hgradb (k : ℕ) : ∀ᵐ x ∂μ, ‖gradient (g k) x‖ ≤ ‖gradient f x‖ := by
    filter_upwards [hgrad k] with x hx
    rw [hx, norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)
  have hdg (k : ℕ) : MemLp (gradient (g k)) 2 μ :=
    hdf.norm.mono' (((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.continuous.measurable.comp
      (measurable_fderiv ℝ (g k))).aestronglyMeasurable) (hgradb k)
  have ht (x) : Tendsto (fun k => g k x) atTop (𝓝 (f x)) := by
    have hz : Tendsto (fun k : ℕ => f x/R k) atTop (𝓝 0) := by
      simpa only [R, div_eq_mul_inv, one_div, mul_zero, one_mul] using
        (tendsto_const_nhds (x := f x)).mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have he (k : ℕ) : g k x = f x * Real.sinc (f x/R k) := by
      by_cases hf : f x = 0
      · simp [g,hf]
      · rw [Real.sinc_of_ne_zero (div_ne_zero hf (hR k).ne')]
        dsimp only [g]
        field_simp
    simpa only [he, Real.sinc_zero, mul_one, Function.comp_def] using
      tendsto_const_nhds.mul (Real.continuous_sinc.continuousAt.tendsto.comp hz)
  apply memLp_of_variance_approximants f hm g hgm hgb ht
    (κ⁻¹*(∫ x, ‖gradient f x‖^2 ∂μ)) (by positivity)
  intro k
  have hgraph := (IntrinsicScalarCore.mem_interior_completion_iff hU hB hV hC hbar
    ((hgm k).toLp (g k)) ((hdg k).toLp (gradient (g k)))).mp
      (subset_closure ⟨g k,hgs k,hgm k,hdg k,rfl⟩)
  have hmem := (EuclideanScalarForm.mem_neumannSobolevGraph_iff hU hB
    (IntrinsicScalarCore.supported hU hV) _ _).mp hgraph
  let F : ScalarForm.Domain (IntrinsicScalarCore.jet hU hB hV) :=
    ⟨WithLp.toLp 2 ((hgm k).toLp (g k),(hdg k).toLp (gradient (g k))),hmem⟩
  have hF : ScalarForm.value _ F =ᵐ[μ] g k := (hgm k).coeFn_toLp
  have hDF : ScalarForm.deriv _ F =ᵐ[μ] gradient (g k) := (hdg k).coeFn_toLp
  have hp := IntrinsicScalarPoisson.poincare hU hB hne hc hV hκ hH F
  have hv : (∫ x, (g k x-∫ y, g k y ∂μ)^2 ∂μ) =
      ‖ScalarForm.value _ F‖^2-(∫ x, ScalarForm.value _ F x ∂μ)^2 := by
    have hn : ‖ScalarForm.value (IntrinsicScalarCore.jet hU hB hV) F‖^2 =
        ∫ x, (ScalarForm.value (IntrinsicScalarCore.jet hU hB hV) F x)^2 ∂μ := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by simp only [Real.inner_apply, pow_two]
    rw [hn, ← Riesz1.WeightedSobolev.integral_sub_mean_sq (Lp.memLp (ScalarForm.value _ F))]
    have hm' := integral_congr_ae hF
    rw [hm']
    exact integral_congr_ae ((hF.symm.fun_sub (EventuallyEq.rfl)).pow_const 2)
  have he : ScalarForm.energy (IntrinsicScalarCore.jet hU hB hV) F F =
      ∫ x, ‖gradient (g k) x‖^2 ∂μ := by
    rw [ScalarForm.energy, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hDF] with x hx
    rw [hx, real_inner_self_eq_norm_sq]
  rw [hv]
  apply hp.trans
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hκ.le)
  exact integral_mono_ae (hdg k).norm.integrable_sq hdf.norm.integrable_sq
    ((hgradb k).mono fun x hx => pow_le_pow_left₀ (norm_nonneg _) hx 2)

/-- Norm control for a mixed derivative pulled back through a linear chart. -/
theorem mixed_derivative_norm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (H : E →L[ℝ] E →L[ℝ] ℝ) (B : F →L[ℝ] E) (d : E) :
    ‖((ContinuousLinearMap.apply ℝ ℝ d).comp H).comp B‖ ≤ ‖H‖*(‖B‖*‖d‖) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  change ‖H (B v) d‖ ≤ _
  calc
    _ ≤ ‖H (B v)‖*‖d‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖H‖*‖B v‖)*‖d‖ := mul_le_mul_of_nonneg_right (H.le_opNorm (B v)) (norm_nonneg _)
    _ ≤ (‖H‖*(‖B‖*‖v‖))*‖d‖ := by gcongr; exact B.le_opNorm v
    _ = _ := by ring

end Riesz2.GradientSquareIntegrability


