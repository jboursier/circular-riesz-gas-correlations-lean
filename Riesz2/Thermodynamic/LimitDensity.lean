/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.External.LogConcaveExponentialTails
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Absolute continuity of a nondegenerate log-concave weak limit

See the proof of Theorem 3 in the paper. Finite support witnesses and separation give a
common lower ball for the approximating densities. The midpoint estimate gives an
everywhere upper bound. Portmanteau and outer regularity then give absolute continuity.
-/

public section
noncomputable section

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace BoundedContinuousFunction

namespace Riesz2.LimitDensity

open LogConcaveDensityLimits.Internal LogConcaveExponentialTails

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Separation makes a lower bound robust under perturbation of finitely
many points whose convex hull contains a larger ball. -/
theorem lower_ball_of_nearby_superlevel {ι : Type*} (p v : ι → E)
    {f : E → ℝ} (hf : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    {b r : ℝ} {z : E} (hb : 0 < b) (hr : 0 < r)
    (hball : ball z (2 * r) ⊆ convexHull ℝ (range p))
    (hnear : ∀ i, dist (p i) (v i) < r / 2)
    (hhigh : ∀ i, b ≤ f (v i))
    (hvol : 0 < volume {x | b ≤ f x}) :
    ∀ y ∈ ball z r, b ≤ f y := by
  intro y hy
  by_contra hlow
  obtain ⟨ℓ, hℓ, hsep⟩ := exists_low_halfspace hf hb hvol (not_le.mp hlow)
  have hn : 0 < ‖ℓ‖ := norm_pos_iff.mpr hℓ
  let u := (InnerProductSpace.toDual ℝ E).symm ℓ
  have hun : ‖u‖ = ‖ℓ‖ := (InnerProductSpace.toDual ℝ E).symm.norm_map _
  have hlu : ℓ u = ‖ℓ‖ ^ 2 := by
    rw [← InnerProductSpace.toDual_symm_apply, real_inner_self_eq_norm_sq, hun]
  let w := ‖ℓ‖⁻¹ • u
  have hwn : ‖w‖ = 1 := by
    simp only [w, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, hun]
    exact inv_mul_cancel₀ hn.ne'
  have hlw : ℓ w = ‖ℓ‖ := by
    simp only [w, map_smul, smul_eq_mul, hlu]
    field_simp
  have hp (i) : ℓ (p i) ≤ ℓ y + ‖ℓ‖ * (r / 2) := by
    have hv : ℓ (v i) ≤ ℓ y := by
      by_contra hh
      exact (not_lt_of_ge (hhigh i)) (hsep _ (not_le.mp hh))
    have he := ℓ.le_opNorm (p i - v i)
    have hdist : ‖p i - v i‖ < r / 2 := by
      simpa only [dist_eq_norm] using hnear i
    have he' := (le_abs_self (ℓ (p i - v i))).trans he
    rw [map_sub] at he'
    have hmul := mul_lt_mul_of_pos_left hdist hn
    linarith
  have hh : convexHull ℝ (range p) ⊆ {x | ℓ x ≤ ℓ y + ‖ℓ‖ * (r / 2)} :=
    convexHull_min (by rintro _ ⟨i, rfl⟩; exact hp i)
      (convex_halfSpace_le ℓ.toLinearMap.isLinear _)
  have hx : y + r • w ∈ ball z (2 * r) := by
    rw [mem_ball, dist_eq_norm] at hy ⊢
    have he : y + r • w - z = (y - z) + r • w := by abel
    rw [he]
    calc
      _ ≤ ‖y - z‖ + ‖r • w‖ := norm_add_le _ _
      _ = ‖y - z‖ + r := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hwn, mul_one]
      _ < 2 * r := by linarith
  have hbad := hh (hball hx)
  change ℓ (y + r • w) ≤ _ at hbad
  rw [map_add, map_smul, smul_eq_mul, hlw] at hbad
  nlinarith [mul_pos hn hr]

/-- Full affine span of the limiting support forces a common positive
lower ball for all sufficiently late approximating densities. -/
theorem eventual_lower_ball_of_full_support
    (F : ℕ → E → ℝ)
    (hF : ∀ n, ConcaveOn ℝ {x | 0 < F n x} (fun x => Real.log (F n x)))
    (P : ℕ → ProbabilityMeasure E) (Q : ProbabilityMeasure E)
    (hP : ∀ n, (P n : Measure E) = volume.withDensity (fun x => ENNReal.ofReal (F n x)))
    (hweak : Tendsto P atTop (𝓝 Q))
    (hspan : affineSpan ℝ Q.toMeasure.support = ⊤) :
    ∃ z : E, ∃ r b : ℝ, 0 < r ∧ 0 < b ∧
      ∀ᶠ n in atTop, ∀ y ∈ ball z r, b ≤ F n y := by
  classical
  obtain ⟨s, hs, a, ha⟩ := AffineBasis.exists_affine_subbasis hspan
  have : Finite s := a.setFinite
  let := Fintype.ofFinite s
  have : Nonempty s := a.nonempty
  obtain ⟨z, hz⟩ : (interior (convexHull ℝ (range a))).Nonempty :=
    ⟨_, a.centroid_mem_interior_convexHull⟩
  obtain ⟨R, hR, hRball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
  let r := R / 2
  have hr : 0 < r := half_pos hR
  have hball : ball z (2 * r) ⊆ convexHull ℝ (range a) := by
    rw [show 2 * r = R by dsimp [r]; ring]
    exact hRball.trans interior_subset
  have hpos (i : s) : 0 < Q.toMeasure (ball (a i) (r / 2)) := by
    apply (Measure.mem_support_iff_forall _).mp (hs (ha ▸ i.property))
    exact ball_mem_nhds _ (half_pos hr)
  have hthreshold (i : s) : ∃ b : ℝ, 0 < b ∧
      ENNReal.ofReal b * volume (ball (a i) (r / 2)) <
        Q.toMeasure (ball (a i) (r / 2)) := by
    let v := volume (ball (a i) (r / 2))
    let m := Q.toMeasure (ball (a i) (r / 2))
    have hv : 0 < v.toReal := ENNReal.toReal_pos
      (measure_ball_pos volume _ (half_pos hr)).ne' measure_ball_lt_top.ne
    have hm : 0 < m.toReal := ENNReal.toReal_pos (hpos i).ne' (measure_ne_top _ _)
    refine ⟨m.toReal / (2 * v.toReal), by positivity, ?_⟩
    apply (ENNReal.toReal_lt_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      measure_ball_lt_top.ne) (measure_ne_top _ _)).mp
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    change m.toReal / (2 * v.toReal) * v.toReal < m.toReal
    rw [div_mul_eq_mul_div, mul_div_mul_right _ _ hv.ne']
    linarith
  choose b hb hbm using hthreshold
  obtain ⟨i₀, _, hmin⟩ := Finset.exists_min_image Finset.univ b Finset.univ_nonempty
  let B := b i₀
  have hB : 0 < B := hb i₀
  have hlarge (i : s) : ∀ᶠ n in atTop,
      ENNReal.ofReal B * volume (ball (a i) (r / 2)) < (P n : Measure E) (ball (a i) (r / 2)) := by
    apply eventually_lt_of_lt_liminf (hu := isBoundedUnder_of_eventually_ge
      (Eventually.of_forall fun _ => bot_le))
    have hsmall : ENNReal.ofReal B * volume (ball (a i) (r / 2)) ≤
        ENNReal.ofReal (b i) * volume (ball (a i) (r / 2)) := by
      gcongr
      exact hmin i (Finset.mem_univ i)
    exact (hsmall.trans_lt (hbm i)).trans_le
      (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak isOpen_ball)
  refine ⟨z, r, B, hr, hB, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hlarge] with n hn
  have hpoint (i : s) : ∃ v ∈ ball (a i) (r / 2), B ≤ F n v := by
    by_contra hh
    have hlow : ∀ v ∈ ball (a i) (r / 2), F n v ≤ B := by
      intro v hv
      exact (not_le.mp (fun he => hh ⟨v, hv, he⟩)).le
    have hbound := withDensity_apply_le_constant (μ := volume) isOpen_ball.measurableSet
      ((ae_restrict_mem isOpen_ball.measurableSet).mono hlow)
    rw [← hP n] at hbound
    exact (hn i).not_ge hbound
  choose v hv hhigh using hpoint
  apply lower_ball_of_nearby_superlevel a v (hF n) hB hr hball
    (fun i => by simpa only [mem_ball, dist_comm] using hv i) hhigh
  apply superlevel_measure_pos_of_constant_mass_lt (B := ball (a i₀) (r / 2))
    isOpen_ball.measurableSet
  rw [← hP n]
  exact hn i₀

/-- A weak limit of densities with one eventual finite upper bound is
dominated by that bound times Lebesgue measure. -/
theorem dominated_of_eventual_density_bound
    (F : ℕ → E → ℝ) (P : ℕ → ProbabilityMeasure E) (Q : ProbabilityMeasure E)
    (hP : ∀ n, (P n : Measure E) = volume.withDensity (fun x => ENNReal.ofReal (F n x)))
    (hweak : Tendsto P atTop (𝓝 Q)) (B : ℝ)
    (hbound : ∀ᶠ n in atTop, ∀ x, F n x ≤ B) :
    Q.toMeasure ≤ ENNReal.ofReal B • volume := by
  have hopen (O : Set E) (hO : IsOpen O) :
      Q.toMeasure O ≤ (ENNReal.ofReal B • volume) O := by
    have hb : ∀ᶠ n in atTop, (P n : Measure E) O ≤ ENNReal.ofReal B * volume O := by
      filter_upwards [hbound] with n hn
      rw [hP]
      exact withDensity_apply_le_constant hO.measurableSet (ae_of_all _ hn)
    exact (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hO).trans
      ((liminf_le_liminf hb).trans_eq (liminf_const _))
  have : Measure.OuterRegular (ENNReal.ofReal B • (volume : Measure E)) :=
    Measure.OuterRegular.smul volume ENNReal.ofReal_ne_top
  apply Measure.le_iff'.mpr
  intro A
  rw [A.measure_eq_iInf_isOpen (ENNReal.ofReal B • volume)]
  exact le_iInf fun O => le_iInf fun hAO => le_iInf fun hO =>
    (measure_mono hAO).trans (hopen O hO)

end Riesz2.LimitDensity

namespace Riesz2

/-- See the proof of Theorem 3 in the paper: a weak limit of
log-concave probability densities whose support has full affine span has
a Lebesgue density. Full affine span is equivalent to the support lying
in no proper affine hyperplane. -/
theorem convergence_limit_density (k : ℕ) (_hk : 1 ≤ k)
    (F : ℕ → EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ∀ n, Measurable (F n) ∧ (∀ x, 0 ≤ F n x) ∧
      (∫⁻ x, ENNReal.ofReal (F n x)) = 1 ∧
      ConcaveOn ℝ {x | 0 < F n x} (fun x => Real.log (F n x)))
    (Q : ProbabilityMeasure (EuclideanSpace ℝ (Fin k)))
    (hweak : ∀ φ : EuclideanSpace ℝ (Fin k) →ᵇ ℝ,
      Tendsto (fun n => ∫ x, φ x ∂volume.withDensity (fun x => ENNReal.ofReal (F n x)))
        atTop (𝓝 (∫ x, φ x ∂Q)))
    (hspan : affineSpan ℝ Q.toMeasure.support = ⊤) :
    ∃ g : EuclideanSpace ℝ (Fin k) → ℝ,
      Measurable g ∧ (∀ x, 0 ≤ g x) ∧
        (∫⁻ x, ENNReal.ofReal (g x)) = 1 ∧
        Q.toMeasure = volume.withDensity (fun x => ENNReal.ofReal (g x)) := by
  let E := EuclideanSpace ℝ (Fin k)
  have hprob (n : ℕ) : IsProbabilityMeasure
      (volume.withDensity (fun x => ENNReal.ofReal (F n x))) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact (hF n).2.2.1
  let P : ℕ → ProbabilityMeasure E := fun n =>
    ⟨volume.withDensity (fun x => ENNReal.ofReal (F n x)), hprob n⟩
  have hw : Tendsto P atTop (𝓝 Q) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr hweak
  obtain ⟨z, r, b, hr, hb, hlower⟩ := LimitDensity.eventual_lower_ball_of_full_support
    F (fun n => (hF n).2.2.2) P Q (fun _ => rfl) hw hspan
  let B := Real.exp (2 * Real.log (1 / volume.real (ball (0 : E) (r / 2))) - Real.log b)
  have hupper : ∀ᶠ n in atTop, ∀ x, F n x ≤ B := by
    filter_upwards [hlower] with n hn
    obtain ⟨hi, hm⟩ := LogConcaveExponentialTails.integrable_and_integral_eq_one
      (hF n).1 (hF n).2.1 (hF n).2.2.1
    exact LogConcaveExponentialTails.upper_of_lower_ball hi (hF n).2.1 hm
      (hF n).2.2.2 hr (by simpa only [Real.exp_log hb] using hn)
  have hdom := LimitDensity.dominated_of_eventual_density_bound F P Q (fun _ => rfl) hw B hupper
  have hac : Q.toMeasure ≪ (volume : Measure E) := by
    apply Measure.AbsolutelyContinuous.mk
    intro A _ hA
    apply le_antisymm _ bot_le
    exact (Measure.le_iff'.mp hdom A).trans_eq (by simp [hA])
  let g : E → ℝ := fun x => (Q.toMeasure.rnDeriv volume x).toReal
  have hgm : Measurable g := (Measure.measurable_rnDeriv Q.toMeasure volume).ennreal_toReal
  have heq : Q.toMeasure = volume.withDensity (fun x => ENNReal.ofReal (g x)) := by
    rw [← Measure.withDensity_rnDeriv_eq Q.toMeasure volume hac]
    apply withDensity_congr_ae
    filter_upwards [Measure.rnDeriv_lt_top Q.toMeasure volume] with x hx
    exact (ENNReal.ofReal_toReal hx.ne).symm
  refine ⟨g, hgm, fun _ => ENNReal.toReal_nonneg, ?_, heq⟩
  have hmass := Q.prop.measure_univ
  change Q.toMeasure univ = 1 at hmass
  rw [heq, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hmass
  exact hmass

end Riesz2
