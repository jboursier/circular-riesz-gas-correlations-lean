/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.LogSobolev
public import Riesz2.ToMathlib.BoundedExponentialPath
public import Riesz1.HelfferSjostrand.BLSecondVariation
public import Riesz1.ToMathlib.Poincare.SmoothCore
public import Riesz1.ToMathlib.WeightedSobolev.L2Facts
public import Riesz1.ToMathlib.WeightedSobolev.Graph

/-!
# Poincaré by second variation of logarithmic Sobolev

The scalar inverse in the proof of Proposition 3.3 uses
Lemma 3.7. We test its entropy inequality on `exp(t f / 2)`,
differentiate twice at zero, and pass to the Neumann Sobolev completion.
-/

public section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz2.LogSobolevPoincare

namespace Internal

/-- The second-variation step in Proposition 3.3. This internal
analytic implication takes the exponential-test entropy inequality as input.
The Gibbs application below supplies it from Lemma 3.7. -/
theorem poincare_of_exponential_entropy
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f g : Ω → ℝ} {B A C : ℝ}
    (hf : Measurable f) (hg : Measurable g) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hfb : ∀ x, |f x| ≤ B) (hgb : ∀ x, |g x| ≤ A)
    (hLS : ∀ t : ℝ,
      t * (∫ x, Real.exp (t * f x) * f x ∂μ) -
          (∫ x, Real.exp (t * f x) ∂μ) * Real.log (∫ x, Real.exp (t * f x) ∂μ) ≤
        C / 2 * t ^ 2 * ∫ x, Real.exp (t * f x) * g x ∂μ) :
    (∫ x, f x ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 ≤ C * ∫ x, g x ∂μ := by
  let M (t : ℝ) := ∫ x, Real.exp (t * f x) ∂μ
  let M₁ (t : ℝ) := ∫ x, Real.exp (t * f x) * f x ∂μ
  let M₂ (t : ℝ) := ∫ x, Real.exp (t * f x) * (f x * f x) ∂μ
  let E (t : ℝ) := ∫ x, Real.exp (t * f x) * g x ∂μ
  let E₁ (t : ℝ) := ∫ x, Real.exp (t * f x) * (f x * g x) ∂μ
  have hff : ∀ x, |f x * f x| ≤ B * B := fun x => by
    rw [abs_mul]; exact mul_le_mul (hfb x) (hfb x) (abs_nonneg _) hB
  have hfg : ∀ x, |f x * g x| ≤ B * A := fun x => by
    rw [abs_mul]; exact mul_le_mul (hfb x) (hgb x) (abs_nonneg _) hB
  have hM : ContDiff ℝ ∞ M := by
    simpa only [M, mul_one] using BoundedExponentialPath.smooth_weighted_integral
      (μ := μ) hf measurable_const hB (by norm_num : (0 : ℝ) ≤ 1) hfb
      (fun _ => by norm_num : ∀ _ : Ω, |(1 : ℝ)| ≤ 1)
  have hM₁ : ContDiff ℝ ∞ M₁ :=
    BoundedExponentialPath.smooth_weighted_integral hf hf hB hB hfb hfb
  have hM₂ : ContDiff ℝ ∞ M₂ :=
    BoundedExponentialPath.smooth_weighted_integral hf (hf.mul hf) hB
      (mul_nonneg hB hB) hfb hff
  have hE : ContDiff ℝ ∞ E :=
    BoundedExponentialPath.smooth_weighted_integral hf hg hB hA hfb hgb
  have hE₁ : ContDiff ℝ ∞ E₁ :=
    BoundedExponentialPath.smooth_weighted_integral hf (hf.mul hg) hB
      (mul_nonneg hB hA) hfb hfg
  have hMp (t : ℝ) : 0 < M t := BoundedExponentialPath.normalizer_pos hf hB hfb t
  have dM (t : ℝ) : HasDerivAt M (M₁ t) t := by
    simpa only [M, M₁, mul_one] using BoundedExponentialPath.hasDerivAt_weighted_integral
      (μ := μ) hf measurable_const hB (by norm_num : (0 : ℝ) ≤ 1) hfb
      (fun _ => by norm_num : ∀ _ : Ω, |(1 : ℝ)| ≤ 1) t
  have dM₁ (t : ℝ) : HasDerivAt M₁ (M₂ t) t :=
    BoundedExponentialPath.hasDerivAt_weighted_integral hf hf hB hB hfb hfb t
  have dE (t : ℝ) : HasDerivAt E (E₁ t) t :=
    BoundedExponentialPath.hasDerivAt_weighted_integral hf hg hB hA hfb hgb t
  let D (t : ℝ) := C / 2 * t ^ 2 * E t - (t * M₁ t - M t * Real.log (M t))
  let D₁ (t : ℝ) := C / 2 * (2 * t * E t + t ^ 2 * E₁ t) -
    (M₁ t + t * M₂ t - (M₁ t * Real.log (M t) + M₁ t))
  have dD (t : ℝ) : HasDerivAt D (D₁ t) t := by
    convert ((((hasDerivAt_id t).pow 2).mul (dE t)).const_mul (C / 2)).sub
      (((hasDerivAt_id t).mul (dM₁ t)).sub ((dM t).mul ((dM t).log (hMp t).ne'))) using 1
    · funext u; dsimp [D]; ring
    · dsimp [D₁]; field_simp [(hMp t).ne']
  have dD₁ : HasDerivAt D₁
      (C * E 0 - M₂ 0 + (M₁ 0) ^ 2) 0 := by
    have dM₂ := (hM₂.differentiable (by simp)).differentiableAt.hasDerivAt (x := 0)
    have dE₁ := (hE₁.differentiable (by simp)).differentiableAt.hasDerivAt (x := 0)
    have hM0 : M 0 = 1 := by simp [M]
    convert ((((hasDerivAt_id (0 : ℝ)).const_mul 2).mul (dE 0)).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).mul dE₁) |>.const_mul (C / 2)).sub
      (((dM₁ 0).add ((hasDerivAt_id (0 : ℝ)).mul dM₂)).sub
        (((dM₁ 0).mul ((dM 0).log (hMp 0).ne')).add (dM₁ 0))) using 1
    · rfl
    · simp only [id_eq, Pi.pow_apply, hM0, Real.log_one, mul_zero, zero_mul,
        zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_one]
      ring
  have hD : ContDiff ℝ 2 D := by
    exact ((contDiff_const.mul (contDiff_id.pow 2)).mul (hE.of_le (by simp))).sub
      ((contDiff_id.mul (hM₁.of_le (by simp))).sub
        ((hM.of_le (by simp)).mul ((hM.log fun t => (hMp t).ne').of_le (by simp))))
  have hzero : D 0 = 0 := by simp [D, M]
  have hfirst : deriv D 0 = 0 := by rw [(dD 0).deriv]; simp [D₁, M]
  have hnonneg : ∀ᶠ t in 𝓝 (0 : ℝ), 0 ≤ D t :=
    Eventually.of_forall fun t => sub_nonneg.mpr (hLS t)
  have hsecond := Riesz1.bl_second_variation_nonneg hD hzero hfirst hnonneg
  have heq : deriv D = D₁ := funext fun t => (dD t).deriv
  rw [heq, dD₁.deriv] at hsecond
  simp only [M₂, E, M₁, zero_mul, Real.exp_zero, one_mul, ← pow_two] at hsecond
  linarith

/-- Smooth-core application of the second variation for
Proposition 3.3. The entropy premise is discharged below. -/
theorem smooth_poincare {d : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))}
    (hB : Bornology.IsBounded U) (hU : IsOpen U)
    {μ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ U) {C : ℝ}
    (hLS : ∀ (F : EuclideanSpace ℝ (Fin d) → ℝ),
      Riesz1.WeightedSobolev.SmoothNearClosure U F →
      (∫ x, F x ^ 2 * Real.log (F x ^ 2) ∂μ) -
          (∫ x, F x ^ 2 ∂μ) * Real.log (∫ x, F x ^ 2 ∂μ) ≤
        2 * C * ∫ x, ‖gradient F x‖ ^ 2 ∂μ)
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (hfs : Riesz1.WeightedSobolev.SmoothNearClosure U f) :
    (∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ) ≤ C * ∫ x, ‖gradient f x‖ ^ 2 ∂μ := by
  classical
  obtain ⟨W, hW, hUW, hs⟩ := hfs
  have hf := hs.continuousOn.mono (subset_closure.trans hUW)
  have hd : ContinuousOn (gradient f) U :=
    ((InnerProductSpace.toDual ℝ _).symm.continuous.comp_continuousOn
      (hs.continuousOn_fderiv_of_isOpen hW (by norm_num))).mono
        (subset_closure.trans hUW)
  obtain ⟨_, B, hb⟩ := Riesz1.bounds_of_smoothNearClosure hB ⟨W, hW, hUW, hs⟩
  let f₀ := U.indicator f
  let g₀ := U.indicator (fun x => ‖gradient f x‖ ^ 2)
  have hfm : Measurable f₀ := hf.measurable_piecewise continuousOn_const hU.measurableSet
  have hgm : Measurable g₀ := (hd.norm.pow 2).measurable_piecewise
    continuousOn_const hU.measurableSet
  have hfa : f₀ =ᵐ[μ] f := hμ.mono fun x hx => indicator_of_mem hx _
  have hga : g₀ =ᵐ[μ] (fun x => ‖gradient f x‖ ^ 2) :=
    hμ.mono fun x hx => indicator_of_mem hx _
  have hfb : ∀ x, |f₀ x| ≤ max B 0 := by
    intro x
    by_cases hx : x ∈ U
    · simpa only [f₀, indicator_of_mem hx, ← Real.norm_eq_abs] using
        (hb x hx).1.trans (le_max_left B 0)
    · simp only [f₀, indicator_of_notMem hx, abs_zero]; exact le_max_right _ _
  have hgb : ∀ x, |g₀ x| ≤ (max B 0) ^ 2 := by
    intro x
    by_cases hx : x ∈ U
    · rw [show g₀ x = ‖gradient f x‖ ^ 2 from indicator_of_mem hx _,
        abs_of_nonneg (sq_nonneg ‖gradient f x‖)]
      exact pow_le_pow_left₀ (norm_nonneg _) ((hb x hx).2.trans (le_max_left B 0)) 2
    · simp only [g₀, indicator_of_notMem hx, abs_zero]; positivity
  have hent (t : ℝ) :
      t * (∫ x, Real.exp (t * f₀ x) * f₀ x ∂μ) -
          (∫ x, Real.exp (t * f₀ x) ∂μ) * Real.log (∫ x, Real.exp (t * f₀ x) ∂μ) ≤
        C / 2 * t ^ 2 * ∫ x, Real.exp (t * f₀ x) * g₀ x ∂μ := by
    let F := fun x => Real.exp (t / 2 * f x)
    have hF : Riesz1.WeightedSobolev.SmoothNearClosure U F :=
      ⟨W, hW, hUW, (contDiffOn_const.mul hs).exp⟩
    have hsq (x) : F x ^ 2 = Real.exp (t * f x) := by
      dsimp only [F]
      rw [pow_two, ← Real.exp_add]; congr 1; ring
    have hgF (x) (hx : x ∈ U) :
        gradient F x = (Real.exp (t / 2 * f x) * (t / 2)) • gradient f x := by
      have hdf := (hs.contDiffAt (hW.mem_nhds (hUW (subset_closure hx)))).differentiableAt
        (by norm_num)
      simp only [F, gradient, fderiv_exp (hdf.const_mul _), fderiv_const_mul hdf,
        map_smul, smul_smul]
    have hval (x) : F x ^ 2 * Real.log (F x ^ 2) =
        t * (Real.exp (t * f x) * f x) := by rw [hsq, Real.log_exp]; ring
    have hgrad : (fun x => ‖gradient F x‖ ^ 2) =ᵐ[μ]
        (fun x => t ^ 2 / 4 * (Real.exp (t * f x) * ‖gradient f x‖ ^ 2)) := by
      filter_upwards [hμ] with x hx
      rw [hgF x hx, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, mul_pow,
        show Real.exp (t / 2 * f x) ^ 2 = Real.exp (t * f x) from hsq x]
      ring
    have h := hLS F hF
    simp_rw [hval, hsq, integral_const_mul] at h
    rw [integral_congr_ae hgrad, integral_const_mul] at h
    have h1 := integral_congr_ae (hfa.mono fun x hx =>
      congrArg (fun z => Real.exp (t * z) * z) hx)
    have h2 := integral_congr_ae (hfa.mono fun x hx => congrArg (fun z => Real.exp (t * z)) hx)
    have h3 : (∫ x, Real.exp (t * f₀ x) * g₀ x ∂μ) =
        ∫ x, Real.exp (t * f x) * ‖gradient f x‖ ^ 2 ∂μ :=
      integral_congr_ae ((hfa.and hga).mono fun x hx => by dsimp only; rw [hx.1, hx.2])
    rw [h1, h2, h3]
    convert h using 1; ring
  have hvar := poincare_of_exponential_entropy (C := C) hfm hgm
    (le_max_right B 0) (sq_nonneg _) hfb hgb hent
  have hmem := Riesz1.Poincare.isWeightedH1_of_smoothNearClosure hB hμ
    (show Riesz1.WeightedSobolev.SmoothNearClosure U f from ⟨W, hW, hUW, hs⟩)
  rw [Riesz1.WeightedSobolev.integral_sub_mean_sq hmem.memLp_fun]
  have h1 := integral_congr_ae (hfa.mono fun x hx => congrArg (fun z => z ^ 2) hx)
  have h2 := integral_congr_ae hfa
  have h3 := integral_congr_ae hga
  rwa [h1, h2, h3] at hvar

end Internal

/-- Lemma 3.7 supplies the Poincaré step of Proposition 3.3.
The logarithmic Sobolev inequality is differentiated on smooth exponential
tests, then extended by the defining H¹ approximation. -/
theorem poincare_of_gibbsPotential {d : ℕ} (hd : 1 ≤ d)
    {U : Set (EuclideanSpace ℝ (Fin d))} (hB : Bornology.IsBounded U)
    (hU : IsOpen U) (hc : Convex ℝ U)
    {ρ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure ρ]
    {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : IsEuclideanGibbsPotential volume ρ U V)
    {κ : ℝ} (hκ : 0 < κ)
    (hH : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h)
    {F : EuclideanSpace ℝ (Fin d) → ℝ}
    {G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hFG : Riesz1.WeightedSobolev.IsWeightedH1 ρ U F G) :
    (∫ x, (F x - ∫ y, F y ∂ρ) ^ 2 ∂ρ) ≤ κ⁻¹ * ∫ x, ‖G x‖ ^ 2 ∂ρ := by
  have hρU : ∀ᵐ x ∂ρ, x ∈ U := by
    rw [hV.2.2.2]
    apply Measure.smul_absolutelyContinuous.ae_le
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hU.measurableSet)
  have hρ : ρ = (volume.restrict U).withDensity (fun x => ENNReal.ofReal
      ((∫⁻ x in U, ENNReal.ofReal (Real.exp (-V x))).toReal⁻¹ * Real.exp (-V x))) := by
    rw [hV.2.2.2, ← withDensity_smul' _ _ (ENNReal.inv_ne_top.mpr hV.2.1.ne')]
    congr 1
    funext x
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos
      (ENNReal.toReal_pos hV.2.1.ne' hV.2.2.1.ne), ENNReal.ofReal_toReal hV.2.2.1.ne]
    rfl
  have hsmooth (f : EuclideanSpace ℝ (Fin d) → ℝ)
      (hf : Riesz1.WeightedSobolev.SmoothNearClosure U f) :
      (∫ x, (f x - ∫ y, f y ∂ρ) ^ 2 ∂ρ) ≤ κ⁻¹ * ∫ x, ‖gradient f x‖ ^ 2 ∂ρ := by
    apply Internal.smooth_poincare hB hU hρU (f := f) (C := κ⁻¹) _ hf
    intro f hf
    have h := log_sobolev_conditioning_of_hessian hd hc hU
      (hV.1.of_le (by norm_num)) hκ hH ρ hρ f (gradient f)
      (Riesz1.Poincare.isWeightedH1_of_smoothNearClosure hB hρU hf)
    simpa only [div_eq_mul_inv] using h.2.2.2
  obtain ⟨hF, hG, f, hf, hv, hg⟩ := hFG
  have hm k := Riesz1.Poincare.isWeightedH1_of_smoothNearClosure hB hρU (hf k)
  have hv' := Riesz1.WeightedSobolev.tendsto_integral_sq_of_lintegral
    (fun k => (hm k).1.aestronglyMeasurable.sub hF.aestronglyMeasurable) hv
  have hvar := Riesz1.WeightedSobolev.tendsto_integral_sub_mean_sq hF
    (fun k => (hm k).1) hv'
  have hg' := (Riesz1.WeightedSobolev.tendsto_toLp_iff_lintegral_sq
    (fun k => gradient (f k)) (fun k => (hm k).2.1) G hG).mpr hg
  have hnorm {g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
      (hg : MemLp g 2 ρ) : ‖hg.toLp g‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 ∂ρ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    rw [hx, real_inner_self_eq_norm_sq]
  have henergy : Tendsto (fun k => ∫ x, ‖gradient (f k) x‖ ^ 2 ∂ρ) atTop
      (𝓝 (∫ x, ‖G x‖ ^ 2 ∂ρ)) := by
    simpa only [hnorm] using hg'.norm.pow 2
  exact le_of_tendsto_of_tendsto hvar (henergy.const_mul κ⁻¹)
    (Eventually.of_forall fun k => hsmooth (f k) (hf k))

end Riesz2.LogSobolevPoincare
