/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.External.LogConcaveDensityLimits
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Integral.Asymptotics

/-!
# Exponential bounds for log-concave densities

Infrastructure for convergence of log-concave densities.
Log-concavity is taken on the positive support, and densities are normalized.
-/

public section

noncomputable section

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

namespace Riesz2.LogConcaveExponentialTails

open LogConcaveDensityLimits.Internal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ : Measure E} [Measure.IsAddHaarMeasure μ]

/-- A convex set of positive Haar measure contains an open ball. -/
theorem exists_ball_subset_of_convex_of_measure_pos {s : Set E}
    (hs : Convex ℝ s) (hm : 0 < μ s) :
    ∃ z : E, ∃ r : ℝ, 0 < r ∧ ball z r ⊆ s := by
  have hi : (interior s).Nonempty := by
    by_contra hn
    have he : interior s = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    have hsub : s ⊆ frontier s := fun x hx => ⟨subset_closure hx, by simp [he]⟩
    have hz : μ s = 0 := measure_mono_null hsub (hs.addHaar_frontier μ)
    exact hm.ne' hz
  obtain ⟨z, hz⟩ := hi
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
  exact ⟨z, r, hr, hsub.trans interior_subset⟩

/-- A positive-mass lower limit gives a ball on which all sufficiently late
log-concave functions have one common strictly positive lower bound. -/
theorem exists_eventual_lower_ball {F : ℕ → E → ℝ} {g : E → ℝ}
    (hF : ∀ n, ConcaveOn ℝ {x | 0 < F n x} (fun x => Real.log (F n x)))
    (hgmass : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) ≠ 0)
    (hlim : ∀ᵐ x ∂μ, ENNReal.ofReal (g x) ≤
      liminf (fun n => ENNReal.ofReal (F n x)) atTop) :
    ∃ z : E, ∃ r l : ℝ, 0 < r ∧ ∃ N : ℕ,
      ∀ n, N ≤ n → ∀ y ∈ ball z r, Real.exp l ≤ F n y := by
  let S : ℕ × ℕ → Set E := fun p => {x | ∀ n, p.2 ≤ n → (1 : ℝ) / (p.1 + 1) ≤ F n x}
  have hp : ∃ p, 0 < μ (S p) := by
    by_contra hn
    have hz : ∀ p, μ (S p) = 0 := fun p => le_antisymm (not_lt.mp (fun h => hn ⟨p, h⟩)) bot_le
    have hae : ∀ᵐ x ∂μ, ∀ p, x ∉ S p := by
      exact ae_all_iff.mpr fun p => measure_eq_zero_iff_ae_notMem.mp (hz p)
    have hgzero : (fun x => ENNReal.ofReal (g x)) =ᵐ[μ] 0 := by
      filter_upwards [hae, hlim] with x hx hl
      by_contra hne
      have hgpos : 0 < g x := ENNReal.ofReal_pos.mp (bot_lt_iff_ne_bot.mpr hne)
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hgpos
      have he : ∀ᶠ n in atTop, (1 : ℝ) / (k + 1) ≤ F n x := by
        have hb : ENNReal.ofReal ((1 : ℝ) / (k + 1)) <
            liminf (fun n => ENNReal.ofReal (F n x)) atTop :=
          ((ENNReal.ofReal_lt_ofReal_iff hgpos).mpr hk).trans_le hl
        filter_upwards [eventually_lt_of_lt_liminf hb] with n hn
        exact le_of_not_gt fun h => hn.not_ge (ENNReal.ofReal_le_ofReal h.le)
      obtain ⟨N, hN⟩ := eventually_atTop.mp he
      exact hx (k, N) hN
    exact hgmass (lintegral_eq_zero_of_ae_eq_zero hgzero)
  obtain ⟨⟨k, N⟩, hp⟩ := hp
  have hk : 0 < (1 : ℝ) / (k + 1) := by positivity
  have hc : Convex ℝ (S (k, N)) := by
    intro x hx y hy a b ha hb hab n hn
    exact convex_superlevel_of_concaveOn_log (hF n) hk (hx n hn) (hy n hn) ha hb hab
  obtain ⟨z, r, hr, hsub⟩ := exists_ball_subset_of_convex_of_measure_pos hc hp
  refine ⟨z, r, Real.log ((1 : ℝ) / (k + 1)), hr, N, ?_⟩
  intro n hn y hy
  rw [Real.exp_log hk]
  exact hsub hy n hn

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- A lower bound on a ball propagates towards any positive density value by
log-concavity. This holds for the actual representative at every point. -/
theorem lower_on_interpolated_ball {f : E → ℝ}
    (hf : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    {z : E} {r l t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hb : ∀ y ∈ ball z r, Real.exp l ≤ f y) {x : E} (hx : 0 < f x) :
    ∀ y ∈ ball (t • x + (1 - t) • z) ((1 - t) * r),
      Real.exp (t * Real.log (f x) + (1 - t) * l) ≤ f y := by
  intro y hy
  let w := (1 - t)⁻¹ • (y - t • x)
  have he : y = t • x + (1 - t) • w := by
    dsimp [w]
    rw [smul_inv_smul₀ (sub_pos.mpr ht1).ne']
    abel
  have hd : y - (t • x + (1 - t) • z) = (1 - t) • (w - z) := by
    rw [he]
    module
  have hw : w ∈ ball z r := by
    rw [mem_ball, dist_eq_norm] at hy ⊢
    rw [hd, norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr ht1)] at hy
    exact (mul_lt_mul_iff_right₀ (sub_pos.mpr ht1)).mp hy
  have hwp : 0 < f w := (Real.exp_pos l).trans_le (hb w hw)
  have hlog := hf.2 hx hwp ht0.le (sub_pos.mpr ht1).le (by ring : t + (1 - t) = 1)
  have hl : l ≤ Real.log (f w) := by
    rw [← Real.log_exp l]
    exact Real.log_le_log (Real.exp_pos l) (hb w hw)
  rw [← he] at hlog
  have hyp : 0 < f y := by
    rw [he]
    exact hf.1 hx hwp ht0.le (sub_pos.mpr ht1).le (by ring)
  rw [← Real.exp_log hyp]
  exact Real.exp_le_exp.mpr (by dsimp only [smul_eq_mul] at hlog; nlinarith)

/-- Integrating the interpolated-ball lower bound bounds every positive value
of a probability density by a local ball average. -/
theorem interpolated_ball_mass_le {f : E → ℝ}
    (hi : Integrable f μ)
    (hf : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    {z : E} {r l t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hb : ∀ y ∈ ball z r, Real.exp l ≤ f y) {x : E} (hx : 0 < f x) :
    Real.exp (t * Real.log (f x) + (1 - t) * l) *
        μ.real (ball (0 : E) ((1 - t) * r)) ≤
      ∫ y in ball (t • x + (1 - t) • z) ((1 - t) * r), f y ∂μ := by
  have h := setIntegral_mono_on
    (integrableOn_const (C := Real.exp (t * Real.log (f x) + (1 - t) * l))
      measure_ball_lt_top.ne)
    hi.integrableOn isOpen_ball.measurableSet
    (lower_on_interpolated_ball hf ht0 ht1 hb hx)
  rw [setIntegral_const, smul_eq_mul, MeasureTheory.Measure.addHaar_real_ball_center] at h
  simpa only [mul_comm] using h

/-- A common lower ball and unit mass give an everywhere upper bound, including
on support boundaries. -/
theorem upper_of_lower_ball {f : E → ℝ} (hi : Integrable f μ)
    (h0 : ∀ x, 0 ≤ f x) (hm : (∫ x, f x ∂μ) = 1)
    (hf : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    {z : E} {r l : ℝ} (hr : 0 < r)
    (hb : ∀ y ∈ ball z r, Real.exp l ≤ f y) :
    ∀ x, f x ≤ Real.exp (2 * Real.log (1 / μ.real (ball (0 : E) (r / 2))) - l) := by
  have hv : 0 < μ.real (ball (0 : E) (r / 2)) :=
    ENNReal.toReal_pos (measure_ball_pos μ _ (by linarith)).ne'
      measure_ball_lt_top.ne
  intro x
  by_cases hx : 0 < f x
  · have h := interpolated_ball_mass_le hi hf (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) hb hx
    have hle := setIntegral_le_integral hi (ae_of_all _ h0)
      (s := ball ((1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • z) (r / 2))
    rw [hm] at hle
    have hb' : Real.exp ((Real.log (f x) + l) / 2) ≤
        1 / μ.real (ball (0 : E) (r / 2)) := by
      apply (le_div_iff₀ hv).mpr
      rw [show (1 - 1 / 2 : ℝ) * r = r / 2 by ring,
        show (1 / 2 : ℝ) * Real.log (f x) + (1 - 1 / 2 : ℝ) * l =
          (Real.log (f x) + l) / 2 by ring] at h
      exact h.trans hle
    have hlog := Real.log_le_log (Real.exp_pos _) hb'
    rw [Real.log_exp] at hlog
    rw [← Real.exp_log hx]
    exact Real.exp_le_exp.mpr (by linarith)
  · exact (not_lt.mp hx).trans (Real.exp_pos _).le

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- A spherical drop in the log density extrapolates along every ray. This
secant argument also covers points on the boundary of the positive support. -/
theorem log_le_of_spherical_drop {f : E → ℝ}
    (hf : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    {z : E} {l a R : ℝ} (hR : 0 < R) (hz : Real.exp l ≤ f z)
    (hs : ∀ y, dist y z = R → f y ≤ Real.exp (l - a * R))
    {x : E} (hx : 0 < f x) (hRx : R ≤ dist x z) :
    Real.log (f x) ≤ l - a * dist x z := by
  by_cases he : R = dist x z
  · have h := Real.log_le_log hx (hs x he.symm)
    rwa [Real.log_exp, he] at h
  have hd : R < dist x z := lt_of_le_of_ne hRx he
  let t := R / dist x z
  have hd0 : 0 < dist x z := hR.trans hd
  have ht0 : 0 < t := div_pos hR hd0
  have ht1 : t < 1 := (div_lt_one hd0).mpr hd
  let y := t • x + (1 - t) • z
  have hdist : dist y z = R := by
    rw [dist_eq_norm]
    have heq : y - z = t • (x - z) := by dsimp [y]; module
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos ht0, ← dist_eq_norm]
    exact div_mul_cancel₀ _ hd0.ne'
  have hzp : 0 < f z := (Real.exp_pos l).trans_le hz
  have hyp : 0 < f y := hf.1 hx hzp ht0.le (sub_pos.mpr ht1).le (by ring)
  have hlz : l ≤ Real.log (f z) := by
    have h := Real.log_le_log (Real.exp_pos l) hz
    rwa [Real.log_exp] at h
  have hly : Real.log (f y) ≤ l - a * R := by
    have h := Real.log_le_log hyp (hs y hdist)
    rwa [Real.log_exp] at h
  have hconc := hf.2 hx hzp ht0.le (sub_pos.mpr ht1).le (by ring : t + (1 - t) = 1)
  have htD : t * dist x z = R := div_mul_cancel₀ _ hd0.ne'
  change t * Real.log (f x) + (1 - t) * Real.log (f z) ≤ Real.log (f y) at hconc
  apply (mul_le_mul_iff_right₀ ht0).mp
  have heq : t * (l - a * dist x z) = t * l - a * R := by
    calc
      _ = t * l - a * (t * dist x z) := by ring
      _ = _ := by rw [htD]
  rw [heq]
  nlinarith [mul_nonneg (sub_pos.mpr ht1).le (sub_nonneg.mpr hlz)]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- Combine a global upper bound and one spherical drop into an everywhere
exponential envelope about the origin. -/
theorem envelope_of_spherical_drop {f : E → ℝ}
    (hf : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    {z : E} {l a R U : ℝ} (ha : 0 < a) (hR : 0 < R)
    (hz : Real.exp l ≤ f z) (hu : ∀ x, f x ≤ Real.exp U)
    (hs : ∀ y, dist y z = R → f y ≤ Real.exp (l - a * R)) :
    ∀ x, f x ≤ Real.exp (-a * ‖x‖ + (max l (U + a * R) + a * ‖z‖)) := by
  intro x
  have hn : ‖x‖ ≤ dist x z + ‖z‖ := by
    simpa only [dist_zero_right] using dist_triangle x z 0
  by_cases hx : 0 < f x
  · rw [← Real.exp_log hx]
    apply Real.exp_le_exp.mpr
    by_cases hRx : R ≤ dist x z
    · have h := log_le_of_spherical_drop hf hR hz hs hx hRx
      have hm := le_max_left l (U + a * R)
      nlinarith
    · have h := Real.log_le_log hx (hu x)
      rw [Real.log_exp] at h
      have hm := le_max_right l (U + a * R)
      have hd := not_le.mp hRx
      nlinarith
  · exact (not_lt.mp hx).trans (Real.exp_pos _).le

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Measure.IsAddHaarMeasure μ] in
/-- The integral of an integrable function outside larger and larger centered
closed balls tends to zero. -/
theorem tendsto_integral_compl_closedBall (f : E → ℝ) (hi : Integrable f μ) (z : E) :
    Tendsto (fun n : ℕ => ∫ y in (closedBall z n)ᶜ, f y ∂μ) atTop (𝓝 0) := by
  have he : (⋂ n : ℕ, (closedBall z (n : ℝ))ᶜ) = ∅ := by
    ext x
    simp only [mem_iInter, mem_compl_iff, mem_closedBall, not_le, mem_empty_iff_false,
      iff_false, not_forall, not_lt]
    exact exists_nat_ge (dist x z)
  have ht := tendsto_setIntegral_of_antitone
    (s := fun n : ℕ => (closedBall z (n : ℝ))ᶜ)
    (fun _ => isClosed_closedBall.measurableSet.compl)
    (fun i j hij => compl_subset_compl.mpr (closedBall_subset_closedBall (by exact_mod_cast hij)))
    ⟨0, hi.integrableOn⟩
  simpa only [he, setIntegral_empty] using ht

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E]
    [FiniteDimensional ℝ E] [Measure.IsAddHaarMeasure μ] in
/-- A normalized nonnegative real density is integrable and has real integral one. -/
theorem integrable_and_integral_eq_one {f : E → ℝ} (hm : Measurable f)
    (h0 : ∀ x, 0 ≤ f x) (hmass : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) = 1) :
    Integrable f μ ∧ (∫ x, f x ∂μ) = 1 := by
  have hi : Integrable f μ := ⟨hm.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ h0)).mpr (by rw [hmass]; exact ENNReal.one_lt_top)⟩
  refine ⟨hi, ?_⟩
  have he := ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ h0)
  rw [hmass] at he
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg h0) zero_le_one).mp
    (he.trans ENNReal.ofReal_one.symm)

/-- Finite mass and a lower ball force a strict drop on a sufficiently distant
sphere. No continuity at the boundary of the support is assumed. -/
theorem exists_spherical_drop {f : E → ℝ} (hi : Integrable f μ)
    (h0 : ∀ x, 0 ≤ f x)
    (hf : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    {z : E} {r l : ℝ} (hr : 0 < r)
    (hb : ∀ y ∈ ball z r, Real.exp l ≤ f y) :
    ∃ R : ℝ, 0 < R ∧ ∀ x, dist x z = R → f x ≤ Real.exp (l - 1) := by
  let v := μ.real (ball (0 : E) (r / 2))
  have hv : 0 < v := ENNReal.toReal_pos
    (measure_ball_pos μ _ (by linarith : 0 < r / 2)).ne' measure_ball_lt_top.ne
  have hε : 0 < Real.exp (l - 1 / 2) * v := mul_pos (Real.exp_pos _) hv
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    ((tendsto_integral_compl_closedBall f hi z).eventually (gt_mem_nhds hε))
  let R := 2 * ((K : ℝ) + r + 1)
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨R, hR, fun x hx => ?_⟩
  by_contra hbad
  have hxpos : 0 < f x := (Real.exp_pos _).trans (not_le.mp hbad)
  have hlog : l - 1 < Real.log (f x) := by
    have h := Real.log_lt_log (Real.exp_pos _) (not_le.mp hbad)
    rwa [Real.log_exp] at h
  let q := (1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • z
  have hq : dist q z = R / 2 := by
    rw [dist_eq_norm]
    have he : q - z = (1 / 2 : ℝ) • (x - z) := by dsimp [q]; module
    rw [he, norm_smul]
    norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    rw [← dist_eq_norm, hx]
    ring
  have hsub : ball q (r / 2) ⊆ (closedBall z (K : ℝ))ᶜ := by
    intro y hy
    have hd := dist_triangle q y z
    have hy' : dist q y < r / 2 := by simpa only [mem_ball, dist_comm] using hy
    rw [hq] at hd
    change ¬dist y z ≤ (K : ℝ)
    dsimp [R] at hd
    linarith
  have hm := interpolated_ball_mass_le hi hf (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) hb hxpos
  have hm' : Real.exp ((Real.log (f x) + l) / 2) * v ≤
      ∫ y in ball q (r / 2), f y ∂μ := by
    rw [show (1 - 1 / 2 : ℝ) * r = r / 2 by ring,
      show (1 / 2 : ℝ) * Real.log (f x) + (1 - 1 / 2 : ℝ) * l =
        (Real.log (f x) + l) / 2 by ring] at hm
    exact hm
  have hle := setIntegral_mono_set hi.integrableOn (ae_of_all _ h0) (ae_of_all _ hsub)
  have hlt := hK K le_rfl
  have hexp : Real.exp (l - 1 / 2) < Real.exp ((Real.log (f x) + l) / 2) :=
    Real.exp_lt_exp.mpr (by linarith)
  exact (mul_lt_mul_of_pos_right hexp hv).not_ge (hm'.trans (hle.trans hlt.le))

/-- Convergence of log-concave densities: every nonnegative
log-concave probability density admits an everywhere exponential envelope. This
form holds for any finite-dimensional normed real space with Haar measure. -/
theorem exists_exponential_envelope {f : E → ℝ} (hm : Measurable f)
    (h0 : ∀ x, 0 ≤ f x) (hmass : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) = 1)
    (hf : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x))) :
    ∃ a : ℝ, 0 < a ∧ ∃ b : ℝ, ∀ x, f x ≤ Real.exp (-a * ‖x‖ + b) := by
  obtain ⟨hi, hint⟩ := integrable_and_integral_eq_one hm h0 hmass
  obtain ⟨z, r, l, hr, N, hb⟩ := exists_eventual_lower_ball
    (F := fun _ : ℕ => f) (g := f) (fun _ => hf)
    (by rw [hmass]; exact one_ne_zero)
    (ae_of_all _ fun x => by simp only [liminf_const]; exact le_rfl)
  have hb' := hb N le_rfl
  obtain ⟨R, hR, hs⟩ := exists_spherical_drop hi h0 hf hr hb'
  have hu := upper_of_lower_ball hi h0 hint hf hr hb'
  refine ⟨1 / R, by positivity, ?_⟩
  let U := 2 * Real.log (1 / μ.real (ball (0 : E) (r / 2))) - l
  refine ⟨max l (U + (1 / R) * R) + (1 / R) * ‖z‖, ?_⟩
  apply envelope_of_spherical_drop hf (by positivity) hR (hb' z (mem_ball_self hr)) hu
  intro x hx
  simpa only [one_div_mul_cancel hR.ne'] using hs x hx

namespace Internal

/-- Internal analytic interface: L¹ convergence, a common positive lower ball,
and an exponential bound on the limit give a common spherical drop at every
smaller rate. Its premises are discharged from weak convergence below. -/
theorem eventual_spherical_drop_of_lower_ball
    {F : ℕ → E → ℝ} {g : E → ℝ}
    (hFi : ∀ n, Integrable (F n) μ) (hgi : Integrable g μ)
    (hF : ∀ n, ConcaveOn ℝ {x | 0 < F n x} (fun x => Real.log (F n x)))
    (hL1 : Tendsto (fun n => ∫ y, |F n y - g y| ∂μ) atTop (𝓝 0))
    {z : E} {r l : ℝ} (hr : 0 < r)
    (hb : ∀ᶠ n in atTop, ∀ y ∈ ball z r, Real.exp l ≤ F n y)
    {a₀ b₀ c : ℝ} (ha₀ : 0 < a₀) (_hc : 0 < c) (hca : c < a₀)
    (hg : ∀ y, g y ≤ Real.exp (-a₀ * ‖y‖ + b₀)) :
    ∃ R : ℝ, 0 < R ∧ ∀ᶠ n in atTop,
      ∀ x, dist x z = R → F n x ≤ Real.exp (l - c * R) := by
  let T := a₀ * (‖z‖ + r / 2) + b₀ - l + Real.log 2
  obtain ⟨R, hR⟩ := exists_gt (max 0 (2 * T / (a₀ - c)))
  have hR0 : 0 < R := (le_max_left _ _).trans_lt hR
  have hRT : 2 * T < R * (a₀ - c) := by
    exact (div_lt_iff₀ (sub_pos.mpr hca)).mp ((le_max_right _ _).trans_lt hR)
  let v := μ.real (ball (0 : E) (r / 2))
  let A := Real.exp (l - c * R / 2)
  have hv : 0 < v := ENNReal.toReal_pos
    (measure_ball_pos μ _ (by linarith : 0 < r / 2)).ne' measure_ball_lt_top.ne
  have hA : 0 < A := Real.exp_pos _
  have he : 0 < A * v / 2 := by positivity
  refine ⟨R, hR0, ?_⟩
  filter_upwards [hb, hL1.eventually (gt_mem_nhds he)] with n hn hsmall
  intro x hx
  by_contra hbad
  have hxpos : 0 < F n x := (Real.exp_pos _).trans (not_le.mp hbad)
  have hlog : l - c * R < Real.log (F n x) := by
    have h := Real.log_lt_log (Real.exp_pos _) (not_le.mp hbad)
    rwa [Real.log_exp] at h
  let q := (1 / 2 : ℝ) • x + (1 - 1 / 2 : ℝ) • z
  have hq : dist q z = R / 2 := by
    rw [dist_eq_norm]
    have heq : q - z = (1 / 2 : ℝ) • (x - z) := by dsimp [q]; module
    rw [heq, norm_smul]
    norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    rw [← dist_eq_norm, hx]
    ring
  have hgsmall : ∀ y ∈ ball q (r / 2), g y ≤ A / 2 := by
    intro y hy
    have hd := dist_triangle q y z
    have hy' : dist q y < r / 2 := by simpa only [mem_ball, dist_comm] using hy
    have hyz : dist y z ≤ ‖y‖ + ‖z‖ := by
      simpa only [dist_zero_left, dist_zero_right] using dist_triangle y 0 z
    rw [hq] at hd
    have hexp : -a₀ * ‖y‖ + b₀ ≤ l - c * R / 2 - Real.log 2 := by
      dsimp only [T] at hRT
      nlinarith
    calc
      g y ≤ Real.exp (-a₀ * ‖y‖ + b₀) := hg y
      _ ≤ Real.exp (l - c * R / 2 - Real.log 2) := Real.exp_le_exp.mpr hexp
      _ = A / 2 := by rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hgmass : (∫ y in ball q (r / 2), g y ∂μ) ≤ (A / 2) * v := by
    have h := setIntegral_mono_on hgi.integrableOn
      (integrableOn_const (C := A / 2) measure_ball_lt_top.ne)
      isOpen_ball.measurableSet hgsmall
    rw [setIntegral_const, smul_eq_mul, MeasureTheory.Measure.addHaar_real_ball_center] at h
    simpa only [mul_comm] using h
  have hFmass : (∫ y in ball q (r / 2), F n y ∂μ) < A * v := by
    have hpoint : ∀ y, F n y ≤ |F n y - g y| + g y := by
      intro y
      linarith [le_abs_self (F n y - g y)]
    have hiabs : Integrable (fun y => |F n y - g y|) μ := ((hFi n).sub hgi).abs
    have h := integral_mono (μ := μ.restrict (ball q (r / 2))) (hFi n).integrableOn
      (hiabs.integrableOn.add hgi.integrableOn) hpoint
    dsimp only [Pi.add_apply, Pi.sub_apply] at h
    rw [integral_add hiabs.integrableOn hgi.integrableOn] at h
    have hle := setIntegral_le_integral hiabs (ae_of_all _ fun y => abs_nonneg (F n y - g y))
      (s := ball q (r / 2))
    nlinarith
  have hm := interpolated_ball_mass_le (hFi n) (hF n)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1) hn hxpos
  rw [show (1 - 1 / 2 : ℝ) * r = r / 2 by ring,
    show (1 / 2 : ℝ) * Real.log (F n x) + (1 - 1 / 2 : ℝ) * l =
      (Real.log (F n x) + l) / 2 by ring] at hm
  have hexp : A < Real.exp ((Real.log (F n x) + l) / 2) :=
    Real.exp_lt_exp.mpr (by linarith)
  exact (mul_lt_mul_of_pos_right hexp hv).not_ge (hm.trans hFmass.le)

/-- Internal assembly of the common everywhere envelope from L¹ convergence
and the one-sided lower limit inferior proved in `LogConcaveDensityLimits`. -/
theorem eventual_envelope_of_L1_of_le_liminf
    {F : ℕ → E → ℝ} {g : E → ℝ}
    (hFm : ∀ n, Measurable (F n)) (hF0 : ∀ n x, 0 ≤ F n x)
    (hFmass : ∀ n, (∫⁻ x, ENNReal.ofReal (F n x) ∂μ) = 1)
    (hF : ∀ n, ConcaveOn ℝ {x | 0 < F n x} (fun x => Real.log (F n x)))
    (hgi : Integrable g μ) (hgmass : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) ≠ 0)
    (hL1 : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal |F n x - g x| ∂μ) atTop (𝓝 0))
    (hlim : ∀ᵐ x ∂μ, ENNReal.ofReal (g x) ≤
      liminf (fun n => ENNReal.ofReal (F n x)) atTop)
    {a₀ b₀ c : ℝ} (ha₀ : 0 < a₀) (hc : 0 < c) (hca : c < a₀)
    (hg : ∀ y, g y ≤ Real.exp (-a₀ * ‖y‖ + b₀)) :
    ∃ b : ℝ, ∀ᶠ n in atTop, ∀ x, F n x ≤ Real.exp (-c * ‖x‖ + b) := by
  have hFi (n : ℕ) := integrable_and_integral_eq_one (hFm n) (hF0 n) (hFmass n)
  obtain ⟨z, r, l, hr, N, hb⟩ := exists_eventual_lower_ball hF hgmass hlim
  have hb' : ∀ᶠ n in atTop, ∀ y ∈ ball z r, Real.exp l ≤ F n y :=
    (eventually_ge_atTop N).mono fun n hn => hb n hn
  have hreal : Tendsto (fun n => ∫ x, |F n x - g x| ∂μ) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL1
    simp only [ENNReal.toReal_zero] at h
    convert h using 1
    ext n
    exact integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => abs_nonneg _)
      (((hFi n).1.sub hgi).abs.aestronglyMeasurable)
  obtain ⟨R, hR, hs⟩ := eventual_spherical_drop_of_lower_ball
    (fun n => (hFi n).1) hgi hF hreal hr hb' ha₀ hc hca hg
  let U := 2 * Real.log (1 / μ.real (ball (0 : E) (r / 2))) - l
  refine ⟨max l (U + c * R) + c * ‖z‖, ?_⟩
  filter_upwards [hb', hs] with n hn hns
  exact envelope_of_spherical_drop (hF n) hc hR (hn z (mem_ball_self hr))
    (upper_of_lower_ball (hFi n).1 (hF0 n) (hFi n).2 (hF n) hr hn) hns

end Internal

/-- Every strictly decreasing radial exponential is integrable against Haar
measure in finite dimension. The comparison exponent retains the dimension. -/
theorem integrable_exp_neg_norm {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : E => Real.exp (-c * ‖x‖)) μ := by
  let p : ℝ := Module.finrank ℝ E + 1
  have hp : (Module.finrank ℝ E : ℝ) < p := by dsimp [p]; linarith
  have href := integrable_one_add_norm (μ := μ) hp
  have hnorm : Tendsto (fun x : E => 1 + ‖x‖) (cocompact E) atTop :=
    tendsto_const_nhds.add_atTop tendsto_norm_cocompact_atTop
  have hO := (isLittleO_exp_neg_mul_rpow_atTop hc (-p)).isBigO.comp_tendsto hnorm
  have hO' : (fun x : E => Real.exp (-c * ‖x‖)) =O[cocompact E]
      (fun x : E => (1 + ‖x‖) ^ (-p)) := by
    convert hO.const_mul_left (Real.exp c) using 1
    · ext x
      dsimp only [Function.comp_apply]
      rw [← Real.exp_add]
      congr 1
      ring
    · rfl
  have hcont : Continuous (fun x : E => Real.exp (-c * ‖x‖)) := by fun_prop
  exact hcont.locallyIntegrable.integrable_of_isBigO_cocompact hO'
    (href.integrableAtFilter _)

namespace Internal

omit [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- Two common exponential envelopes give a single integrable envelope for
the exponentially weighted absolute difference. -/
theorem weighted_abs_sub_le_of_envelopes {f g : E → ℝ} {a c b b' : ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf : ∀ x, f x ≤ Real.exp (-c * ‖x‖ + b))
    (hg : ∀ x, g x ≤ Real.exp (-c * ‖x‖ + b')) :
    ∀ x, Real.exp (a * ‖x‖) * |f x - g x| ≤
      Real.exp (-(c - a) * ‖x‖ + (max b b' + Real.log 2)) := by
  intro x
  have habs : |f x - g x| ≤ f x + g x := abs_le.mpr ⟨by linarith [hf0 x], by linarith [hg0 x]⟩
  have h1 : f x ≤ Real.exp (-c * ‖x‖ + max b b') :=
    (hf x).trans (Real.exp_le_exp.mpr (by linarith [le_max_left b b']))
  have h2 : g x ≤ Real.exp (-c * ‖x‖ + max b b') :=
    (hg x).trans (Real.exp_le_exp.mpr (by linarith [le_max_right b b']))
  calc
    Real.exp (a * ‖x‖) * |f x - g x| ≤
        Real.exp (a * ‖x‖) * (2 * Real.exp (-c * ‖x‖ + max b b')) := by
      gcongr
      linarith
    _ = Real.exp (-(c - a) * ‖x‖ + (max b b' + Real.log 2)) := by
      rw [show -(c - a) * ‖x‖ + (max b b' + Real.log 2) =
        (a * ‖x‖ + (-c * ‖x‖ + max b b')) + Real.log 2 by ring]
      simp only [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      ring

end Internal

/-- The extended integral of a radial exponential outside increasing balls
tends to zero. No real-integral junk value enters this statement. -/
theorem tendsto_lintegral_exp_compl_closedBall {c : ℝ} (hc : 0 < c) (b : ℝ) :
    Tendsto (fun R : ℕ => ∫⁻ x in (closedBall (0 : E) (R : ℝ))ᶜ,
      ENNReal.ofReal (Real.exp (-c * ‖x‖ + b)) ∂μ) atTop (𝓝 0) := by
  have hi : Integrable (fun x : E => Real.exp (-c * ‖x‖ + b)) μ := by
    simpa only [Real.exp_add, mul_comm] using (integrable_exp_neg_norm hc (μ := μ)).const_mul (Real.exp b)
  have ht := ENNReal.tendsto_ofReal (tendsto_integral_compl_closedBall _ hi (0 : E))
  simp only [ENNReal.ofReal_zero] at ht
  convert ht using 1
  ext R
  exact (ofReal_integral_eq_lintegral_ofReal hi.integrableOn
    (ae_of_all _ fun x => (Real.exp_pos _).le)).symm

end Riesz2.LogConcaveExponentialTails

namespace Riesz2

open scoped BoundedContinuousFunction

/-- Convergence of log-concave densities, the standalone
exponential-envelope conjunct, with the Euclidean density convention. -/
theorem logConcaveDensity_exponential_envelope (d : ℕ) (_hd : 1 ≤ d)
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∫⁻ x, ENNReal.ofReal (f x)) = 1)
    (hlc : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x))) :
    ∃ a : ℝ, 0 < a ∧ ∃ b : ℝ, ∀ x, f x ≤ Real.exp (-a * ‖x‖ + b) :=
  LogConcaveExponentialTails.exists_exponential_envelope hf.1 hf.2.1 hf.2.2 hlc

/-- Convergence of log-concave densities: at every rate strictly
below a prescribed exponential rate of the weak limit, the approximating
densities eventually share one everywhere exponential envelope. -/
theorem logConcaveDensity_eventual_exponential_envelope (d : ℕ) (hd : 1 ≤ d)
    (F : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (hF : ∀ n, (Measurable (F n) ∧ (∀ x, 0 ≤ F n x) ∧
      (∫⁻ x, ENNReal.ofReal (F n x)) = 1) ∧
      ConcaveOn ℝ {x | 0 < F n x} (fun x => Real.log (F n x)))
    (hg : Measurable g ∧ (∀ x, 0 ≤ g x) ∧ (∫⁻ x, ENNReal.ofReal (g x)) = 1)
    (hweak : ∀ φ : EuclideanSpace ℝ (Fin d) →ᵇ ℝ,
      Tendsto (fun n => ∫ x, φ x ∂volume.withDensity (fun x => ENNReal.ofReal (F n x)))
        atTop (𝓝 (∫ x, φ x ∂volume.withDensity (fun x => ENNReal.ofReal (g x)))))
    (a₀ b₀ : ℝ) (ha₀ : 0 < a₀) (hgenv : ∀ x, g x ≤ Real.exp (-a₀ * ‖x‖ + b₀))
    (c : ℝ) (hc : 0 < c) (hca : c < a₀) :
    ∃ b : ℝ, ∀ᶠ n in atTop, ∀ x, F n x ≤ Real.exp (-c * ‖x‖ + b) := by
  let E := EuclideanSpace ℝ (Fin d)
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hprobF (n : ℕ) : IsProbabilityMeasure
      (volume.withDensity (fun x => ENNReal.ofReal (F n x))) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact (hF n).1.2.2
  have hprobg : IsProbabilityMeasure
      (volume.withDensity (fun x => ENNReal.ofReal (g x))) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hg.2.2
  let P : ℕ → ProbabilityMeasure E := fun n => ⟨volume.withDensity
    (fun x => ENNReal.ofReal (F n x)), hprobF n⟩
  let Q : ProbabilityMeasure E := ⟨volume.withDensity
    (fun x => ENNReal.ofReal (g x)), hprobg⟩
  have hgi := (LogConcaveExponentialTails.integrable_and_integral_eq_one hg.1 hg.2.1 hg.2.2).1
  have hlim := LogConcaveDensityLimits.Internal.le_liminf_of_weak
    (fun n => (hF n).2) hgi hg.2.1 P Q (fun _ => rfl) rfl
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr hweak)
  exact LogConcaveExponentialTails.Internal.eventual_envelope_of_L1_of_le_liminf
    (fun n => (hF n).1.1) (fun n => (hF n).1.2.1) (fun n => (hF n).1.2.2)
    (fun n => (hF n).2) hgi (by rw [hg.2.2]; exact one_ne_zero)
    (logConcaveDensity_limits d hd F g hF hg hweak).2 hlim ha₀ hc hca hgenv

/-- Uniform exponential tails for convergent log-concave densities. For each `0 < a < a₀`, one fixed index and one integrable
radial exponential dominate all later weighted density differences. Their
integrals outside balls tend to zero uniformly in those indices. -/
theorem logConcaveDensity_uniform_weighted_tails (d : ℕ) (hd : 1 ≤ d)
    (F : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (hF : ∀ n, (Measurable (F n) ∧ (∀ x, 0 ≤ F n x) ∧
      (∫⁻ x, ENNReal.ofReal (F n x)) = 1) ∧
      ConcaveOn ℝ {x | 0 < F n x} (fun x => Real.log (F n x)))
    (hg : Measurable g ∧ (∀ x, 0 ≤ g x) ∧ (∫⁻ x, ENNReal.ofReal (g x)) = 1)
    (hweak : ∀ φ : EuclideanSpace ℝ (Fin d) →ᵇ ℝ,
      Tendsto (fun n => ∫ x, φ x ∂volume.withDensity (fun x => ENNReal.ofReal (F n x)))
        atTop (𝓝 (∫ x, φ x ∂volume.withDensity (fun x => ENNReal.ofReal (g x)))))
    (a₀ b₀ : ℝ) (ha₀ : 0 < a₀) (hgenv : ∀ x, g x ≤ Real.exp (-a₀ * ‖x‖ + b₀))
    (a : ℝ) (ha : 0 < a) (haa : a < a₀) :
    ∃ b : ℝ, ∃ N : ℕ,
      (∀ n, N ≤ n → ∀ x, Real.exp (a * ‖x‖) * |F n x - g x| ≤
        Real.exp (-((a₀ - a) / 2) * ‖x‖ + b)) ∧
      (∫⁻ x : EuclideanSpace ℝ (Fin d),
        ENNReal.ofReal (Real.exp (-((a₀ - a) / 2) * ‖x‖ + b))) < ⊤ ∧
      (∀ ε : ℝ≥0∞, 0 < ε → ∃ R : ℕ, ∀ n, N ≤ n →
        (∫⁻ x in (closedBall (0 : EuclideanSpace ℝ (Fin d)) (R : ℝ))ᶜ,
          ENNReal.ofReal (Real.exp (a * ‖x‖) * |F n x - g x|)) < ε) := by
  let c := (a₀ + a) / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hca : c < a₀ := by dsimp [c]; linarith
  have hδ : 0 < (a₀ - a) / 2 := by linarith
  have heq : c - a = (a₀ - a) / 2 := by dsimp [c]; ring
  obtain ⟨b, hb⟩ := logConcaveDensity_eventual_exponential_envelope
    d hd F g hF hg hweak a₀ b₀ ha₀ hgenv c hc hca
  obtain ⟨N, hN⟩ := eventually_atTop.mp hb
  let B := max b b₀ + Real.log 2
  have hgc : ∀ x, g x ≤ Real.exp (-c * ‖x‖ + b₀) := by
    intro x
    exact (hgenv x).trans (Real.exp_le_exp.mpr (by nlinarith [norm_nonneg x]))
  have hbound (n : ℕ) (hn : N ≤ n) : ∀ x,
      Real.exp (a * ‖x‖) * |F n x - g x| ≤ Real.exp (-((a₀ - a) / 2) * ‖x‖ + B) := by
    simpa only [heq] using LogConcaveExponentialTails.Internal.weighted_abs_sub_le_of_envelopes
      (a := a) (hF n).1.2.1 hg.2.1 (hN n hn) hgc
  have hi : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      Real.exp (-((a₀ - a) / 2) * ‖x‖ + B)) := by
    simpa only [Real.exp_add, mul_comm] using
      (LogConcaveExponentialTails.integrable_exp_neg_norm
        (E := EuclideanSpace ℝ (Fin d)) (μ := volume) hδ).const_mul (Real.exp B)
  refine ⟨B, N, hbound,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => (Real.exp_pos _).le)).mp hi.2, ?_⟩
  intro ε hε
  have ht := LogConcaveExponentialTails.tendsto_lintegral_exp_compl_closedBall
    (E := EuclideanSpace ℝ (Fin d)) (μ := volume) hδ B
  obtain ⟨R, hR⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
  refine ⟨R, fun n hn => lt_of_le_of_lt ?_ (hR R le_rfl)⟩
  exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hbound n hn x)

end Riesz2

end
