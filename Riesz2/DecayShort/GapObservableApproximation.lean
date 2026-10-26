/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.ShortRangeResult
public import Riesz1.ToMathlib.WeightedSobolev.LipschitzH1Convolution
public import Riesz1.ToMathlib.WeightedSobolev.GraphLimits

/-!
# Smooth approximation of gap observables

The reduction in the proof of Theorem 2 of the paper: smooth the
scalar observables, center at one, keep their essential derivative bound,
and pass to the limit under the absolutely continuous finite-volume gap laws.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology ENNReal NNReal ContDiff

namespace Riesz2.DecayShort.GapObservableApproximation

/-- The exact Lipschitz constant used in the smooth reduction of
Theorem 2 of the paper is the essential derivative bound. -/
theorem observable_lipschitz (f : GapObservable) :
    LipschitzWith ⟨derivativeSup f, ENNReal.toReal_nonneg⟩ f.val.1 := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |f.val.1 x - f.val.1 y| ≤ derivativeSup f * |x - y|
  exact CenteredObservable.abs_observable_sub_le f y x

/-- Smooth scalar approximations, centered at gap one, for the reduction in
Theorem 2 of the paper. The derivative bound has no enlargement.
The same sequence works for every finite-volume gap law. -/
theorem exists_smooth_observables (f : GapObservable) :
    ∃ F : ℕ → GapObservable,
      (∀ k, ContDiff ℝ ∞ (F k).val.1) ∧
      (∀ k, (F k).val.1 1 = 0) ∧
      (∀ k, derivativeSup (F k) ≤ derivativeSup f) ∧
      (∀ k x, |(F k).val.2 x| ≤ derivativeSup f) ∧
      (∀ x, Tendsto (fun k => (F k).val.1 x) atTop (𝓝 (f.val.1 x - f.val.1 1))) ∧
      ∀ᵐ x ∂volume, Tendsto (fun k => (F k).val.2 x) atTop (𝓝 (f.val.2 x)) := by
  obtain ⟨φ, hs, _, hb, hv, hd⟩ :=
    Riesz1.WeightedSobolev.exists_smooth_approximation_lipschitz (observable_lipschitz f)
  have hder k x : |deriv (φ k) x| ≤ derivativeSup f := by
    have hh := hb k x
    rw [gradient_eq_deriv', Real.norm_eq_abs] at hh
    exact hh
  let ψ : ℕ → ℝ → ℝ := fun k x => φ k x - φ k 1
  have hψ k : ContDiff ℝ ∞ (ψ k) := (hs k).sub contDiff_const
  have hψder k x : HasDerivAt (ψ k) (deriv (φ k) x) x :=
    ((hs k).differentiable (by simp) x).hasDerivAt.sub_const _
  have hL k : LipschitzWith ⟨derivativeSup f, ENNReal.toReal_nonneg⟩ (ψ k) := by
    apply lipschitzWith_of_nnnorm_deriv_le ((hψ k).differentiable (by simp))
    intro x
    rw [(hψder k x).deriv]
    exact_mod_cast hder k x
  have htop k : eLpNorm (deriv (φ k)) ∞ volume ≤ ENNReal.ofReal (derivativeSup f) := by
    rw [eLpNorm_exponent_top (measurable_deriv _).aestronglyMeasurable]
    apply eLpNormEssSup_le_of_ae_bound
    exact ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hder k x
  let F : ℕ → GapObservable := fun k => ⟨(ψ k, deriv (φ k)),
    ⟨⟨_, hL k⟩, (measurable_deriv _).aestronglyMeasurable,
      ae_of_all _ (hψder k), (htop k).trans_lt ENNReal.ofReal_lt_top⟩⟩
  refine ⟨F, hψ, ?_, ?_, hder, ?_, ?_⟩
  · intro k
    exact sub_self _
  · intro k
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (htop k)).trans_eq
      (ENNReal.toReal_ofReal ENNReal.toReal_nonneg)
  · intro x
    exact (hv x).sub (hv 1)
  · filter_upwards [hd, f.property.2.2.1] with x hx hfx
    simpa only [gradient_eq_deriv', hfx.deriv] using hx

/-- Internal dominated-convergence step of Theorem 2 of the paper.
It gives strong L² convergence of bounded scalar tests after a measurable
coordinate pullback. -/
theorem internal_bounded_toLp {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {u : ℕ → Ω → ℝ} {v : Ω → ℝ}
    (hu : ∀ k, AEStronglyMeasurable (u k) μ) (hv : AEStronglyMeasurable v μ)
    {B : ℝ} (hbu : ∀ k, ∀ᵐ x ∂μ, ‖u k x‖ ≤ B)
    (hbv : ∀ᵐ x ∂μ, ‖v x‖ ≤ B)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun k => u k x) atTop (𝓝 (v x))) :
    ∃ (hm : ∀ k, MemLp (u k) 2 μ) (hn : MemLp v 2 μ),
      Tendsto (fun k => (hm k).toLp (u k)) atTop (𝓝 (hn.toLp v)) := by
  let hm k : MemLp (u k) 2 μ := MemLp.of_bound (hu k) B (hbu k)
  let hn : MemLp v 2 μ := MemLp.of_bound hv B hbv
  exact ⟨hm, hn, Riesz1.WeightedSobolev.tendsto_toLp_of_dominated hm hn
    (memLp_const B) hbu hbv ht⟩

/-- Absolute continuity used by the smooth reduction of Theorem 2
in the paper, expressed directly on particle configurations. -/
theorem gap_absolutelyContinuous (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (i : Fin (N : ℕ)) :
    (gibbsMeasure p N).map (fun X => gap X i.val) ≪ volume := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, N = (m + 1).succPNat :=
    ⟨(N : ℕ) - 2, PNat.eq (by simp only [Nat.succPNat_coe]; omega)⟩
  have heq : (gibbsMeasure p (m + 1).succPNat).map (fun X => gap X i.val) =
      (gapLaw p (m + 1).succPNat).map (fun g => g i) := by
    unfold gapLaw
    rw [Measure.map_map (measurable_pi_apply i)
      (show Measurable (gapVector (N := (m + 1).succPNat)) from Riesz1.measurable_gapVector _)]
    rfl
  rw [heq]
  exact GapDensities.gapLaw_marginal_absolutelyContinuous p m i

/-- Internal bound for centered tests in the approximation step of
Theorem 2 of the paper. -/
theorem internal_centered_bound (_p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (i : Fin (N : ℕ)) (f : GapObservable) (X : Riesz1.Configuration N) :
    ‖f.val.1 (gap X i.val) - f.val.1 1‖ ≤ derivativeSup f * ((N : ℝ) + 1) := by
  rw [Real.norm_eq_abs]
  apply (CenteredObservable.abs_observable_sub_le f 1 _).trans
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  calc
    |gap X i.val - 1| ≤ |gap X i.val| + |(1 : ℝ)| := abs_sub _ _
    _ ≤ (N : ℝ) + 1 := by
      rw [abs_of_pos (show 0 < gap X i.val from Riesz1.gap_pos X i.val), abs_one]
      have hh : gap X i.val ≤ (N : ℝ) := (Riesz1.gap_lt_particle_number hN X i.val).le
      linarith only [hh]

/-- Internal strong convergence under one gap law for the smooth reduction
of Theorem 2 of the paper. Both the observable and its selected
derivative converge in L². In particular the actual derivative norms converge. -/
theorem internal_gap_limits (f : GapObservable) (F : ℕ → GapObservable)
    (hcenter : ∀ k, (F k).val.1 1 = 0)
    (hsup : ∀ k, derivativeSup (F k) ≤ derivativeSup f)
    (hbound : ∀ k x, |(F k).val.2 x| ≤ derivativeSup f)
    (hval : ∀ x, Tendsto (fun k => (F k).val.1 x) atTop (𝓝 (f.val.1 x - f.val.1 1)))
    (hder : ∀ᵐ x ∂volume, Tendsto (fun k => (F k).val.2 x) atTop (𝓝 (f.val.2 x)))
    (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (i : Fin (N : ℕ)) :
    ∃ (hm : ∀ k, MemLp (fun X => (F k).val.1 (gap X i.val)) 2 (gibbsMeasure p N))
      (hn : MemLp (fun X => f.val.1 (gap X i.val) - f.val.1 1) 2 (gibbsMeasure p N))
      (hdm : ∀ k, MemLp (fun X => (F k).val.2 (gap X i.val)) 2 (gibbsMeasure p N))
      (hdn : MemLp (fun X => f.val.2 (gap X i.val)) 2 (gibbsMeasure p N)),
      Tendsto (fun k => (hm k).toLp _) atTop (𝓝 (hn.toLp _)) ∧
      Tendsto (fun k => (hdm k).toLp _) atTop (𝓝 (hdn.toLp _)) ∧
      Tendsto (fun k => (gapDerivativeNorm p N i.val (F k)).toReal)
        atTop (𝓝 (gapDerivativeNorm p N i.val f).toReal) := by
  have := gibbsMeasure_probability p N
  have hac := gap_absolutelyContinuous p N hN i
  have hg : Measurable (fun X : Riesz1.Configuration N => gap X i.val) :=
    Riesz1.measurable_gap _
  have hB k (X : Riesz1.Configuration N) : ‖(F k).val.1 (gap X i.val)‖ ≤ derivativeSup f * ((N : ℝ) + 1) := by
    have hb := internal_centered_bound p N hN i (F k) X
    rw [hcenter k, sub_zero] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (hsup k) (by positivity))
  obtain ⟨hm, hn, ht⟩ := internal_bounded_toLp (μ := gibbsMeasure p N)
    (fun k => ((CenteredObservable.continuous_observable (F k)).measurable.comp hg).aestronglyMeasurable)
    ((((CenteredObservable.continuous_observable f).measurable.comp hg).sub_const _).aestronglyMeasurable)
    (fun k => ae_of_all _ (hB k)) (ae_of_all _ (internal_centered_bound p N hN i f))
    (ae_of_all _ fun X => hval (gap X i.val))
  have hfd : ∀ᵐ X ∂gibbsMeasure p N, ‖f.val.2 (gap X i.val)‖ ≤ derivativeSup f := by
    have hh := ae_of_ae_map hg.aemeasurable (hac.ae_le (CenteredObservable.ae_abs_derivative_le f))
    simpa only [Real.norm_eq_abs] using hh
  obtain ⟨hdm, hdn, hdt⟩ := internal_bounded_toLp (μ := gibbsMeasure p N)
    (fun k => ((F k).property.2.1.mono_ac hac).comp_measurable hg)
    ((f.property.2.1.mono_ac hac).comp_measurable hg)
    (fun k => ae_of_all _ fun X => by simpa only [Real.norm_eq_abs, Function.comp_def] using hbound k (gap X i.val))
    hfd (ae_of_ae_map hg.aemeasurable (hac.ae_le hder))
  refine ⟨hm, hn, hdm, hdn, ht, hdt, ?_⟩
  simpa only [Lp.norm_toLp, gapDerivativeNorm, Function.comp_def] using hdt.norm

/-- Internal covariance limit for the smooth reduction of Theorem 2
in the paper. Finite-volume gaps are bounded, so the centered tests and their
products have constant integrable dominators. -/
theorem internal_covariance_limit (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (i j : Fin (N : ℕ)) (f g : GapObservable) (F G : ℕ → GapObservable)
    (hF0 : ∀ k, (F k).val.1 1 = 0) (hG0 : ∀ k, (G k).val.1 1 = 0)
    (hFs : ∀ k, derivativeSup (F k) ≤ derivativeSup f)
    (hGs : ∀ k, derivativeSup (G k) ≤ derivativeSup g)
    (hF : ∀ x, Tendsto (fun k => (F k).val.1 x) atTop (𝓝 (f.val.1 x - f.val.1 1)))
    (hG : ∀ x, Tendsto (fun k => (G k).val.1 x) atTop (𝓝 (g.val.1 x - g.val.1 1))) :
    Tendsto (fun k => covariance (fun X => (F k).val.1 (gap X i.val))
      (fun X => (G k).val.1 (gap X j.val)) (gibbsMeasure p N)) atTop
      (𝓝 (covariance (fun X => f.val.1 (gap X i.val))
        (fun X => g.val.1 (gap X j.val)) (gibbsMeasure p N))) := by
  have := gibbsMeasure_probability p N
  let μ := gibbsMeasure p N
  let u k (X : Riesz1.Configuration N) := (F k).val.1 (gap X i.val)
  let v k (X : Riesz1.Configuration N) := (G k).val.1 (gap X j.val)
  let a (X : Riesz1.Configuration N) := f.val.1 (gap X i.val) - f.val.1 1
  let b (X : Riesz1.Configuration N) := g.val.1 (gap X j.val) - g.val.1 1
  let A := derivativeSup f * ((N : ℝ) + 1)
  let B := derivativeSup g * ((N : ℝ) + 1)
  have hu k : ∀ X, ‖u k X‖ ≤ A := by
    intro X
    have hh := internal_centered_bound p N hN i (F k) X
    rw [hF0 k, sub_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (hFs k) (by positivity))
  have hv k : ∀ X, ‖v k X‖ ≤ B := by
    intro X
    have hh := internal_centered_bound p N hN j (G k) X
    rw [hG0 k, sub_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (hGs k) (by positivity))
  have hum k : AEStronglyMeasurable (u k) μ :=
    ((CenteredObservable.continuous_observable (F k)).measurable.comp (Riesz1.measurable_gap _)).aestronglyMeasurable
  have hvm k : AEStronglyMeasurable (v k) μ :=
    ((CenteredObservable.continuous_observable (G k)).measurable.comp (Riesz1.measurable_gap _)).aestronglyMeasurable
  have ht := tendsto_integral_of_dominated_convergence (fun _ => A)
    hum (integrable_const A) (fun k => ae_of_all _ (hu k)) (ae_of_all _ fun X => hF _)
  have hs := tendsto_integral_of_dominated_convergence (fun _ => B)
    hvm (integrable_const B) (fun k => ae_of_all _ (hv k)) (ae_of_all _ fun X => hG _)
  have hp := tendsto_integral_of_dominated_convergence (fun _ => A * B)
    (fun k => (hum k).mul (hvm k)) (integrable_const (A * B))
    (fun k => ae_of_all _ fun X => by
      change ‖u k X * v k X‖ ≤ A * B
      rw [norm_mul]
      exact mul_le_mul (hu k X) (hv k X) (norm_nonneg _) (mul_nonneg ENNReal.toReal_nonneg (by positivity)))
    (ae_of_all _ fun X => (hF (gap X i.val)).mul (hG (gap X j.val)))
  have hab := ShortRangeResult.internal_gapSecondMoments p N i j f g
  have hac : MemLp a 2 μ := hab.1.sub (memLp_const _)
  have hbc : MemLp b 2 μ := hab.2.1.sub (memLp_const _)
  have he : covariance a b μ = covariance (fun X => f.val.1 (gap X i.val))
      (fun X => g.val.1 (gap X j.val)) μ := by
    rw [covariance_sub_const_left (hab.1.integrable (by norm_num)),
      covariance_sub_const_right (hab.2.1.integrable (by norm_num))]
  have heq k : covariance (u k) (v k) μ =
      (∫ X, u k X * v k X ∂μ) - (∫ X, u k X ∂μ) * (∫ X, v k X ∂μ) :=
    covariance_eq_sub (MemLp.of_bound (hum k) A (ae_of_all _ (hu k)))
      (MemLp.of_bound (hvm k) B (ae_of_all _ (hv k)))
  have hlim : Tendsto (fun k => (∫ X, u k X * v k X ∂μ) -
      (∫ X, u k X ∂μ) * (∫ X, v k X ∂μ)) atTop
      (𝓝 ((∫ X, a X * b X ∂μ) - (∫ X, a X ∂μ) * (∫ X, b X ∂μ))) :=
    hp.sub (ht.mul hs)
  have heab : covariance a b μ = (∫ X, a X * b X ∂μ) -
      (∫ X, a X ∂μ) * (∫ X, b X ∂μ) := covariance_eq_sub hac hbc
  simp_rw [← heq] at hlim
  rw [← heab, he] at hlim
  exact hlim

/-- Internal transfer of a smooth covariance estimate to all observables,
as in the approximation sentence in Theorem 2 of the paper.
Only the derivative L² norms pass to the limit. The essential supremum
terms are bounded by the original observables throughout. -/
theorem internal_transfer (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (i j : Fin (N : ℕ)) (B c δ : ℝ) (hB : 0 ≤ B) (d : ℕ)
    (h : ∀ (f g : GapObservable), ContDiff ℝ ∞ f.val.1 → ContDiff ℝ ∞ g.val.1 →
      |covariance (fun X => f.val.1 (gap X i.val))
        (fun X => g.val.1 (gap X j.val)) (gibbsMeasure p N)| ≤
        B * correlationFactor p N i.val f c δ d * correlationFactor p N j.val g c δ d)
    (f g : GapObservable) :
    |covariance (fun X => f.val.1 (gap X i.val))
      (fun X => g.val.1 (gap X j.val)) (gibbsMeasure p N)| ≤
      B * correlationFactor p N i.val f c δ d * correlationFactor p N j.val g c δ d := by
  obtain ⟨F, hFsmooth, hF0, hFs, hFb, hFv, hFd⟩ := exists_smooth_observables f
  obtain ⟨G, hGsmooth, hG0, hGs, hGb, hGv, hGd⟩ := exists_smooth_observables g
  obtain ⟨_, _, _, _, _, _, hFn⟩ := internal_gap_limits f F hF0 hFs hFb hFv hFd p N hN i
  obtain ⟨_, _, _, _, _, _, hGn⟩ := internal_gap_limits g G hG0 hGs hGb hGv hGd p N hN j
  have hcov := internal_covariance_limit p N hN i j f g F G hF0 hG0 hFs hGs hFv hGv
  have hbound k : |covariance (fun X => (F k).val.1 (gap X i.val))
      (fun X => (G k).val.1 (gap X j.val)) (gibbsMeasure p N)| ≤
      B * ((gapDerivativeNorm p N i.val (F k)).toReal +
          derivativeSup f * Real.exp (-c * (d : ℝ) ^ δ)) *
        ((gapDerivativeNorm p N j.val (G k)).toReal +
          derivativeSup g * Real.exp (-c * (d : ℝ) ^ δ)) := by
    apply (h (F k) (G k) (hFsmooth k) (hGsmooth k)).trans
    unfold correlationFactor
    gcongr
    · exact ShortRangeResult.internal_correlationFactor_nonneg p N j.val (G k) c δ d
    · exact mul_nonneg hB (add_nonneg ENNReal.toReal_nonneg
        (mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le))
    · exact hFs k
    · exact hGs k
  exact le_of_tendsto_of_tendsto hcov.abs
    ((tendsto_const_nhds.mul (hFn.add_const _)).mul (hGn.add_const _))
    (Eventually.of_forall hbound)

end Riesz2.DecayShort.GapObservableApproximation
