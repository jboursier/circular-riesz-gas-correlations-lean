/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.External.LogConcavePoincare
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Probability.CDF

/-!
# Sharp variance comparison in probability coordinates

Supporting results for one-dimensional log-concavity estimates.
Probability coordinates are constructed from the actual CDF, and the
density profile is proved concave without a smooth-density premise.
Reflection about probability one half gives the sharp variance comparison.
The final theorem proves the smooth Poincaré clause with coefficient `12`
and exactly the density, mean, and extended-variance premises.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace Riesz2.LogConcavePoincare

/-- Log odds are strictly increasing on the open probability interval. -/
theorem log_odds_strictMonoOn_internal :
    StrictMonoOn (fun p : ℝ => Real.log p - Real.log (1 - p)) (Ioo (0 : ℝ) 1) := by
  intro p hp q hq hpq
  have hl := Real.log_lt_log hp.1 hpq
  have hr := Real.log_le_log (sub_pos.mpr hq.2) (by linarith : 1 - q ≤ 1 - p)
  linarith

/-- Every real log odds is attained in the open probability interval. -/
theorem log_odds_surjective_internal (t : ℝ) :
    ∃ p ∈ Ioo (0 : ℝ) 1, Real.log p - Real.log (1 - p) = t := by
  let p := Real.exp t / (1 + Real.exp t)
  have he := Real.exp_pos t
  have hden : 0 < 1 + Real.exp t := by positivity
  have hp : p ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨div_pos he hden, (div_lt_one hden).mpr ?_⟩
    linarith
  refine ⟨p, hp, ?_⟩
  have hsub : 1 - p = 1 / (1 + Real.exp t) := by dsimp [p]; field_simp; ring
  rw [hsub]
  dsimp [p]
  rw [Real.log_div he.ne' hden.ne', Real.log_exp,
    Real.log_div one_ne_zero hden.ne', Real.log_one]
  ring

/-- Construct a probability-coordinate inverse using the unique inverse
in log-odds coordinates. The resulting real function has the explicit
whole-line meaning `G⁻¹(log p - log(1-p))`, where `G` is an order
isomorphism onto the real line. No default value outside `(0,1)` is chosen. -/
theorem exists_probability_inverse_internal {F f : ℝ → ℝ} {D : Set ℝ}
    (hD : Convex ℝ D) (hstrict : StrictMonoOn F D)
    (himage : F '' D = Ioo (0 : ℝ) 1)
    (hderivative : ∀ x ∈ D, HasDerivAt F (f x) x)
    (hpositive : ∀ x ∈ D, 0 < f x) :
    ∃ Q : ℝ → ℝ, Measurable Q ∧ MapsTo Q (Ioo (0 : ℝ) 1) D ∧
      (∀ p ∈ Ioo (0 : ℝ) 1, F (Q p) = p) ∧
      (∀ p ∈ Ioo (0 : ℝ) 1, HasDerivAt Q (1 / f (Q p)) p) := by
  have : OrdConnected D := hD.ordConnected
  let L := fun p : ℝ => Real.log p - Real.log (1 - p)
  have hL : StrictMonoOn L (Ioo (0 : ℝ) 1) := log_odds_strictMonoOn_internal
  have hFmap (x : ℝ) (hx : x ∈ D) : F x ∈ Ioo (0 : ℝ) 1 := by
    rw [← himage]
    exact mem_image_of_mem F hx
  let G : D → ℝ := fun x => L (F x)
  have hGstrict : StrictMono G := by
    intro x y hxy
    exact hL (hFmap x x.2) (hFmap y y.2) (hstrict x.2 y.2 hxy)
  have hGsurj : Function.Surjective G := by
    intro t
    obtain ⟨p, hp, hpt⟩ := log_odds_surjective_internal t
    rw [← himage] at hp
    obtain ⟨x, hx, hxp⟩ := hp
    exact ⟨⟨x, hx⟩, by change L (F x) = t; rw [hxp]; exact hpt⟩
  let e : D ≃o ℝ := hGstrict.orderIsoOfSurjective G hGsurj
  let Q := fun p : ℝ => ((e.symm (L p) : D) : ℝ)
  have hcont : Continuous (fun t : ℝ => ((e.symm t : D) : ℝ)) :=
    continuous_subtype_val.comp e.symm.continuous
  have hQm : Measurable Q := hcont.measurable.comp (by dsimp [L]; fun_prop)
  have hQmap (p : ℝ) : Q p ∈ D := (e.symm (L p)).2
  have hinv (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) : F (Q p) = p := by
    apply hL.injOn (hFmap _ (hQmap p)) hp
    change e (e.symm (L p)) = L p
    exact e.apply_symm_apply _
  refine ⟨Q, hQm, fun p _ => hQmap p, hinv, ?_⟩
  intro p hp
  have hLp : ContinuousAt L p := by
    apply ContinuousAt.sub (Real.continuousAt_log hp.1.ne')
    exact Real.continuousAt_log (sub_pos.mpr hp.2).ne' |>.comp
      (continuousAt_const.sub continuousAt_id)
  have hQp : ContinuousAt Q p := hcont.continuousAt.comp hLp
  have hlocal : ∀ᶠ q in 𝓝 p, F (Q q) = q := by
    filter_upwards [isOpen_Ioo.mem_nhds hp] with q hq
    exact hinv q hq
  simpa only [one_div] using
    (hderivative (Q p) (hQmap p)).of_local_left_inverse hQp (hpositive _ (hQmap p)).ne' hlocal

/-- A continuous profile with antitone right derivatives is concave.
This version permits corners in the logarithm of the original density.
It does not impose a smooth-density premise. -/
theorem concaveOn_of_antitone_right_derivative_internal {J k : ℝ → ℝ}
    (hc : ContinuousOn J (Ioo (0 : ℝ) 1))
    (hd : ∀ p ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt J (k p) (Ici p) p)
    (hk : AntitoneOn k (Ioo (0 : ℝ) 1)) : ConcaveOn ℝ (Ioo (0 : ℝ) 1) J := by
  apply concaveOn_of_slope_anti_adjacent (convex_Ioo (0 : ℝ) 1)
  intro x y z hx hz hxy hyz
  have hy : y ∈ Ioo (0 : ℝ) 1 := ⟨hx.1.trans hxy, hyz.trans hz.2⟩
  have hxyD : Icc x y ⊆ Ioo (0 : ℝ) 1 := fun t ht =>
    ⟨hx.1.trans_le ht.1, ht.2.trans_lt hy.2⟩
  have hyzD : Icc y z ⊆ Ioo (0 : ℝ) 1 := fun t ht =>
    ⟨hy.1.trans_le ht.1, ht.2.trans_lt hz.2⟩
  have hlin (b c t : ℝ) : HasDerivAt (fun u => J b + c * (u - b)) c t := by
    convert (((hasDerivAt_id t).sub_const b).const_mul c).const_add (J b) using 1 <;> simp
  have hu : J z ≤ J y + k y * (z - y) := by
    apply image_le_of_deriv_right_le_deriv_boundary (hc.mono hyzD)
      (fun t ht => hd t (hyzD ⟨ht.1, ht.2.le⟩))
      (by simp : J y ≤ J y + k y * (y - y))
      (by fun_prop) (fun t _ => (hlin y (k y) t).hasDerivWithinAt) _ (right_mem_Icc.mpr hyz.le)
    intro t ht
    exact hk hy (hyzD ⟨ht.1, ht.2.le⟩) ht.1
  have hl : J x + k y * (y - x) ≤ J y := by
    apply image_le_of_deriv_right_le_deriv_boundary (by fun_prop)
      (fun t _ => (hlin x (k y) t).hasDerivWithinAt)
      (by simp : J x + k y * (x - x) ≤ J x)
      (hc.mono hxyD) (fun t ht => hd t (hxyD ⟨ht.1, ht.2.le⟩)) _
      (right_mem_Icc.mpr hxy.le)
    intro t ht
    exact hk (hxyD ⟨ht.1, ht.2.le⟩) hy ht.2.le
  exact ((div_le_iff₀ (sub_pos.mpr hyz)).mpr (by linarith : J z - J y ≤ k y * (z - y))).trans
    ((le_div_iff₀ (sub_pos.mpr hxy)).mpr (by linarith : k y * (y - x) ≤ J y - J x))

/-- The density profile in probability coordinates is concave, including
for a density whose logarithm has corners. `D` is an open convex part of
the positive support. The parametrization and its reciprocal derivative
are the only analytic inputs in this internal bridge. -/
theorem concave_density_profile_internal {f Q : ℝ → ℝ} {D : Set ℝ}
    (hD : IsOpen D) (hfpos : ∀ x ∈ D, 0 < f x)
    (hlog : ConcaveOn ℝ D (fun x => Real.log (f x)))
    (hmap : MapsTo Q (Ioo (0 : ℝ) 1) D)
    (hQ : ∀ p ∈ Ioo (0 : ℝ) 1, HasDerivAt Q (1 / f (Q p)) p) :
    ConcaveOn ℝ (Ioo (0 : ℝ) 1) (fun p => f (Q p)) := by
  let G := fun x => -Real.log (f x)
  let d := fun x => derivWithin G (Ioi x) x
  have hG : ConvexOn ℝ D G := hlog.neg
  have hfc : ContinuousOn f D := by
    apply ((hlog.continuousOn hD).rexp).congr
    intro x hx
    exact (Real.exp_log (hfpos x hx)).symm
  have hQdiff : DifferentiableOn ℝ Q (Ioo (0 : ℝ) 1) :=
    fun p hp => (hQ p hp).differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn Q (Ioo (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioo (0 : ℝ) 1) hQdiff.continuousOn
      (by simpa only [interior_Ioo] using hQdiff)
    intro p hp
    rw [interior_Ioo] at hp
    rw [(hQ p hp).deriv]
    exact div_nonneg zero_le_one (hfpos _ (hmap hp)).le
  have hdf (x : ℝ) (hx : x ∈ D) :
      HasDerivWithinAt f (f x * (-d x)) (Ici x) x := by
    have hg := hG.hasDerivWithinAt_rightDeriv_of_mem_interior (hD.interior_eq.symm ▸ hx)
    have he := (hasDerivWithinAt_Ioi_iff_Ici.mp hg).neg.exp
    have hEq : f =ᶠ[𝓝[Ici x] x] (fun t => Real.exp (-G t)) := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hD.mem_nhds hx)] with t ht
      dsimp [G]
      rw [neg_neg, Real.exp_log (hfpos t ht)]
    have he' := he.congr_of_eventuallyEq hEq (by
      dsimp [G]
      rw [neg_neg, Real.exp_log (hfpos x hx)])
    change HasDerivWithinAt f (Real.exp (-G x) * (-d x)) (Ici x) x at he'
    simpa only [G, neg_neg, Real.exp_log (hfpos x hx)] using he'
  apply concaveOn_of_antitone_right_derivative_internal
    (hfc.comp hQdiff.continuousOn hmap)
    (k := fun p => -d (Q p))
  · intro p hp
    have hmaps : MapsTo Q (Ici p ∩ Ioo (0 : ℝ) 1) (Ici (Q p)) := by
      intro t ht
      exact hmono hp ht.2 ht.1
    have hd := (hdf (Q p) (hmap hp)).comp p (hQ p hp).hasDerivWithinAt hmaps
    have hs : Ici p ∩ Ioo (0 : ℝ) 1 ∈ 𝓝[Ici p] p :=
      inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hp))
    have hd' := hd.mono_of_mem_nhdsWithin hs
    convert hd' using 1
    field_simp [(hfpos _ (hmap hp)).ne']
  · intro p hp q hq hpq
    apply neg_le_neg
    exact hG.monotoneOn_rightDeriv (hD.interior_eq.symm ▸ hmap hp)
      (hD.interior_eq.symm ▸ hmap hq) (hmono hp hq hpq)

/-- Reflection and concavity give the sharp reciprocal-profile bound.
This is the pointwise analytic step in the variance comparison for
one-dimensional log-concavity estimates. -/
theorem reciprocal_profile_reflection_internal {I : ℝ → ℝ}
    (hI : ConcaveOn ℝ (Ioo 0 1) I) (hpos : ∀ p ∈ Ioo 0 1, 0 < I p)
    {p : ℝ} (hp : p ∈ Ioo 0 1) :
    2 / I (1 / 2) ≤ 1 / I p + 1 / I (1 - p) := by
  have hpr : 1 - p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.2], by linarith [hp.1]⟩
  have hm : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  have hc := hI.2 hp hpr (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have he : (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • (1 - p) = 1 / 2 := by
    simp only [smul_eq_mul]
    ring
  rw [he] at hc
  simp only [smul_eq_mul] at hc
  have hC := hpos _ hm
  have hA := hpos _ hp
  have hB := hpos _ hpr
  rw [div_add_div _ _ hA.ne' hB.ne']
  apply (div_le_div_iff₀ hC (mul_pos hA hB)).mpr
  nlinarith [sq_nonneg (I p - I (1 - p))]

/-- The reflected increment of a probability-coordinate parametrization
dominates that of a uniform law of density `I(1/2)`. This internal lemma
requires the parametrization and its derivative explicitly. -/
theorem reflected_increment_internal {Q I : ℝ → ℝ}
    (hI : ConcaveOn ℝ (Ioo 0 1) I) (hpos : ∀ p ∈ Ioo 0 1, 0 < I p)
    (hQ : ∀ p ∈ Ioo 0 1, HasDerivAt Q (1 / I p) p)
    {p q : ℝ} (hp : p ∈ Ioo 0 1) (hq : q ∈ Ioo 0 1) (hpq : p ≤ q) :
    (2 / I (1 / 2)) * (q - p) ≤
      (Q q - Q (1 - q)) - (Q p - Q (1 - p)) := by
  let S := fun t => Q t - Q (1 - t)
  have hd (t : ℝ) (ht : t ∈ Ioo 0 1) :
      HasDerivAt S (1 / I t + 1 / I (1 - t)) t := by
    have htr : 1 - t ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    convert (hQ t ht).sub ((hQ (1 - t) htr).comp t
      ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))) using 1 <;>
      first | rfl | ring
  have hdif : DifferentiableOn ℝ S (Ioo 0 1) :=
    fun t ht => (hd t ht).differentiableAt.differentiableWithinAt
  apply (convex_Ioo (0 : ℝ) 1).mul_sub_le_image_sub_of_le_deriv
    hdif.continuousOn (by simpa only [interior_Ioo] using hdif) _ p hp q hq hpq
  intro t ht
  rw [interior_Ioo] at ht
  rw [(hd t ht).deriv]
  exact reciprocal_profile_reflection_internal hI hpos ht

/-- A reflected pair controls the centered square at every probability
coordinate. The center is arbitrary, so no first-moment identity is
needed for this step of one-dimensional log-concavity estimates. -/
theorem reflected_square_internal {Q I : ℝ → ℝ}
    (hI : ConcaveOn ℝ (Ioo 0 1) I) (hpos : ∀ p ∈ Ioo 0 1, 0 < I p)
    (hQ : ∀ p ∈ Ioo 0 1, HasDerivAt Q (1 / I p) p)
    (a : ℝ) {p : ℝ} (hp : p ∈ Ioo 0 1) :
    (2 * p - 1) ^ 2 / (2 * I (1 / 2) ^ 2) ≤
      (Q p - a) ^ 2 + (Q (1 - p) - a) ^ 2 := by
  have hm : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  have hC := hpos _ hm
  have hpair : (2 * p - 1) ^ 2 / I (1 / 2) ^ 2 ≤
      (Q p - Q (1 - p)) ^ 2 := by
    by_cases hpm : 1 / 2 ≤ p
    · have h := reflected_increment_internal hI hpos hQ hm hp hpm
      have he : 1 - (1 / 2 : ℝ) = 1 / 2 := by norm_num
      rw [he, sub_self, sub_zero] at h
      have heq : 2 / I (1 / 2) * (p - 1 / 2) = (2 * p - 1) / I (1 / 2) := by ring
      rw [heq] at h
      have hn : 0 ≤ (2 * p - 1) / I (1 / 2) := div_nonneg (by linarith) hC.le
      simpa only [div_pow] using pow_le_pow_left₀ hn h 2
    · have hmp : p ≤ 1 / 2 := (lt_of_not_ge hpm).le
      have h := reflected_increment_internal hI hpos hQ hp hm hmp
      have he : 1 - (1 / 2 : ℝ) = 1 / 2 := by norm_num
      rw [he, sub_self, zero_sub] at h
      have heq : 2 / I (1 / 2) * (1 / 2 - p) = -(2 * p - 1) / I (1 / 2) := by ring
      rw [heq] at h
      have hn : 0 ≤ -(2 * p - 1) / I (1 / 2) := div_nonneg (by linarith) hC.le
      have hs := pow_le_pow_left₀ hn h 2
      simpa only [div_pow, neg_sq] using hs
  have hpol : (Q p - Q (1 - p)) ^ 2 ≤
      2 * ((Q p - a) ^ 2 + (Q (1 - p) - a) ^ 2) := by
    nlinarith [sq_nonneg (Q p + Q (1 - p) - 2 * a)]
  apply (div_le_iff₀ (by positivity : 0 < 2 * I (1 / 2) ^ 2)).mpr
  have hs := (div_le_iff₀ (sq_pos_of_pos hC)).mp (hpair.trans hpol)
  nlinarith

/-- Reflection preserves Lebesgue integration on the open unit interval.
No integrability premise is needed for the nonnegative extended integral. -/
theorem lintegral_unit_reflection {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ p in Ioo (0 : ℝ) 1, g (1 - p)) = ∫⁻ p in Ioo (0 : ℝ) 1, g p := by
  have he := (volume.measurePreserving_sub_left (1 : ℝ)).setLIntegral_comp_preimage
    (s := Ioo (0 : ℝ) 1) measurableSet_Ioo hg
  have hs : (fun p : ℝ => 1 - p) ⁻¹' Ioo (0 : ℝ) 1 = Ioo (0 : ℝ) 1 := by
    ext p
    simp only [mem_preimage, mem_Ioo]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  rw [hs] at he
  exact he

/-- The uniform comparison polynomial integrates to the sharp numerical
coefficient used in one-dimensional log-concavity estimates. -/
theorem integral_reflected_square_polynomial (C : ℝ) :
    (∫ p in Ioo (0 : ℝ) 1, (2 * p - 1) ^ 2 / (2 * C ^ 2)) = 1 / (6 * C ^ 2) := by
  have hd (p : ℝ) : HasDerivAt (fun t : ℝ => (2 * t - 1) ^ 3 / (12 * C ^ 2))
      ((2 * p - 1) ^ 2 / (2 * C ^ 2)) p := by
    convert ((((hasDerivAt_id p).const_mul 2).sub_const 1).pow 3).div_const
      (12 * C ^ 2) using 1
    · rfl
    · simp only [id_eq]
      ring
  have hi : IntervalIntegrable (fun p : ℝ => (2 * p - 1) ^ 2 / (2 * C ^ 2)) volume 0 1 :=
    (by fun_prop : Continuous (fun p : ℝ => (2 * p - 1) ^ 2 / (2 * C ^ 2))).intervalIntegrable _ _
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun p _ => hd p) hi
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo] at he
  rw [he]
  norm_num
  ring

/-- Sharp variance lower bound for a parametrization with positive
concave reciprocal-derivative profile. This internal analytic theorem
does not construct probability coordinates for a density. It permits
unbounded parametrizations at either end and keeps the second moment
extended-valued throughout. -/
theorem sharp_variance_probability_coordinates_internal {Q I : ℝ → ℝ}
    (hQm : Measurable Q)
    (hI : ConcaveOn ℝ (Ioo 0 1) I) (hpos : ∀ p ∈ Ioo 0 1, 0 < I p)
    (hQ : ∀ p ∈ Ioo 0 1, HasDerivAt Q (1 / I p) p) (a : ℝ) :
    ENNReal.ofReal (1 / (12 * I (1 / 2) ^ 2)) ≤
      ∫⁻ p in Ioo (0 : ℝ) 1, ENNReal.ofReal ((Q p - a) ^ 2) := by
  let C := I (1 / 2)
  have hC : 0 < C := hpos _ (by constructor <;> norm_num)
  have hpoly : (∫⁻ p in Ioo (0 : ℝ) 1,
      ENNReal.ofReal ((2 * p - 1) ^ 2 / (2 * C ^ 2))) =
        ENNReal.ofReal (1 / (6 * C ^ 2)) := by
    have hi : IntegrableOn (fun p : ℝ => (2 * p - 1) ^ 2 / (2 * C ^ 2)) (Ioo 0 1) :=
      (by fun_prop : Continuous (fun p : ℝ => (2 * p - 1) ^ 2 / (2 * C ^ 2))).integrableOn_Icc.mono_set
        Ioo_subset_Icc_self
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun _ => by positivity)),
      integral_reflected_square_polynomial]
  have hb : (∫⁻ p in Ioo (0 : ℝ) 1,
      ENNReal.ofReal ((2 * p - 1) ^ 2 / (2 * C ^ 2))) ≤
      ∫⁻ p in Ioo (0 : ℝ) 1,
        ENNReal.ofReal ((Q p - a) ^ 2) + ENNReal.ofReal ((Q (1 - p) - a) ^ 2) := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with p hp
    rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (reflected_square_internal hI hpos hQ a hp)
  rw [hpoly, lintegral_add_left (by fun_prop),
    lintegral_unit_reflection (g := fun p => ENNReal.ofReal ((Q p - a) ^ 2))
      (by fun_prop)] at hb
  have he : ENNReal.ofReal (1 / (6 * C ^ 2)) =
      ENNReal.ofReal (1 / (12 * C ^ 2)) * 2 := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (12 * C ^ 2))]
    congr 1
    ring
  rw [he, ← mul_two] at hb
  exact (ENNReal.mul_le_mul_iff_right (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mp (by simpa only [mul_comm] using hb)

/-- Transport the sharp probability-coordinate estimate to the actual
extended second moment. All extra parametrization premises are confined
to this internal reduction for one-dimensional log-concavity estimates.
The second moment may be taken about any real center `a`. -/
theorem median_coefficient_of_coordinates_internal {f Q : ℝ → ℝ} {μ : Measure ℝ}
    (htransport : MeasurePreserving Q (volume.restrict (Ioo (0 : ℝ) 1)) μ)
    (hprofile : ConcaveOn ℝ (Ioo 0 1) (fun p => f (Q p)))
    (hpositive : ∀ p ∈ Ioo 0 1, 0 < f (Q p))
    (hderivative : ∀ p ∈ Ioo 0 1, HasDerivAt Q (1 / f (Q p)) p)
    {m a v : ℝ} (hmedian : Q (1 / 2) = m) (hv : 0 < v)
    (hvar : (∫⁻ x, ENNReal.ofReal ((x - a) ^ 2) ∂μ) = ENNReal.ofReal v) :
    1 / (f m) ^ 2 ≤ 12 * v := by
  have hb := sharp_variance_probability_coordinates_internal htransport.measurable
    hprofile hpositive hderivative a
  rw [htransport.lintegral_comp (by fun_prop : Measurable
    (fun x : ℝ => ENNReal.ofReal ((x - a) ^ 2))), hvar, hmedian] at hb
  have hbR := (ENNReal.ofReal_le_ofReal_iff hv.le).mp hb
  have hfm : 0 < f m := by
    rw [← hmedian]
    exact hpositive _ (by constructor <;> norm_num)
  have he : 1 / (f m) ^ 2 = 12 * (1 / (12 * (f m) ^ 2)) := by ring
  rw [he]
  exact mul_le_mul_of_nonneg_left hbR (by norm_num)

/-- Positive mass on both sides places a point in the interior of the
positive support of a log-concave density. -/
theorem mem_interior_positive_support_of_mass_internal {f : ℝ → ℝ}
    (hf : Measurable f)
    (hlog : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    {m : ℝ}
    (hmleft : (volume.withDensity (fun x => ENNReal.ofReal (f x))) (Iic m) ≠ 0)
    (hmright : (volume.withDensity (fun x => ENNReal.ofReal (f x))) (Ici m) ≠ 0) :
    m ∈ interior {x | 0 < f x} := by
  let μ := volume.withDensity (fun x => ENNReal.ofReal (f x))
  have hpoint (U : Set ℝ) (hU : MeasurableSet U) (hmass : μ U ≠ 0) : ∃ x ∈ U, 0 < f x := by
    by_contra hn
    apply hmass
    rw [withDensity_apply _ hU]
    apply (lintegral_eq_zero_iff hf.ennreal_ofReal).mpr
    filter_upwards [ae_restrict_mem hU] with x hx
    exact ENNReal.ofReal_eq_zero.mpr (le_of_not_gt (fun h => hn ⟨x, hx, h⟩))
  have hlmass : μ (Iio m) ≠ 0 := by
    rwa [measure_congr (Iio_ae_eq_Iic (μ := μ))]
  have hrmass : μ (Ioi m) ≠ 0 := by
    rwa [measure_congr (Ioi_ae_eq_Ici (μ := μ))]
  obtain ⟨l, hl, hfl⟩ := hpoint (Iio m) measurableSet_Iio hlmass
  obtain ⟨r, hr, hfr⟩ := hpoint (Ioi m) measurableSet_Ioi hrmass
  have hs : Icc l r ⊆ {x | 0 < f x} := hlog.1.ordConnected.out hfl hfr
  exact mem_interior_iff_mem_nhds.mpr
    (mem_of_superset (Ioo_mem_nhds hl hr) (Ioo_subset_Icc_self.trans hs))

/-- A median of an absolutely continuous law with log-concave density
lies in the interior of its positive support, including for densities
with positive support endpoints. -/
theorem median_mem_interior_positive_support_internal {f : ℝ → ℝ}
    (hf : Measurable f)
    (hlog : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    {m : ℝ}
    (hmleft : (volume.withDensity (fun x => ENNReal.ofReal (f x))) (Iic m) = ENNReal.ofReal (1 / 2))
    (hmright : (volume.withDensity (fun x => ENNReal.ofReal (f x))) (Ici m) = ENNReal.ofReal (1 / 2)) :
    m ∈ interior {x | 0 < f x} := by
  apply mem_interior_positive_support_of_mass_internal hf hlog
  · rw [hmleft]
    norm_num
  · rw [hmright]
    norm_num

/-- The actual CDF is a differentiable order parametrization of the
interior positive support onto `(0,1)`. The density itself need not be
smooth, and the support can be bounded or unbounded. -/
theorem cdf_positive_support_data_internal {f : ℝ → ℝ}
    (hf : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hlog : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    (hprob : IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (f x)))) :
    let μ := volume.withDensity (fun x => ENNReal.ofReal (f x))
    let F := ProbabilityTheory.cdf μ
    let D := interior {x | 0 < f x}
    StrictMonoOn F D ∧ F '' D = Ioo (0 : ℝ) 1 ∧
      ∀ x ∈ D, HasDerivAt F (f x) x := by
  let μ := volume.withDensity (fun x => ENNReal.ofReal (f x))
  let F := ProbabilityTheory.cdf μ
  let D := interior {x | 0 < f x}
  have : IsProbabilityMeasure μ := hprob
  have hmass : (∫⁻ x, ENNReal.ofReal (f x)) = 1 := by
    simpa only [μ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using
      (measure_univ (μ := μ))
  have hfi : Integrable f := ⟨hf.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ hnn)).mpr (by rw [hmass]; exact ENNReal.one_lt_top)⟩
  have hFint (x : ℝ) : F x = ∫ t in Iic x, f t := by
    rw [ProbabilityTheory.cdf_eq_real, measureReal_def]
    change (μ (Iic x)).toReal = _
    rw [withDensity_apply _ measurableSet_Iic,
      ← ofReal_integral_eq_lintegral_ofReal hfi.integrableOn (ae_of_all _ hnn),
      ENNReal.toReal_ofReal (integral_nonneg hnn)]
  have hFcont : Continuous (F : ℝ → ℝ) := by
    rw [continuous_iff_continuousAt]
    intro x
    have he : (F : ℝ → ℝ) = fun y => ∫ t in Iic y, f t := funext hFint
    rw [he]
    exact hfi.integrableOn.continuousOn_Iic_primitive_Iic.continuousAt
      (Iic_mem_nhds (by linarith : x < x + 1))
  have hfc : ContinuousOn f D := by
    apply (((hlog.subset interior_subset hlog.1.interior).continuousOn isOpen_interior).rexp).congr
    intro x hx
    exact (Real.exp_log ((interior_subset (s := {x | 0 < f x})) hx)).symm
  have hFder (x : ℝ) (hx : x ∈ D) : HasDerivAt F (f x) x := by
    have hd := intervalIntegral.integral_hasDerivAt_right (a := x) (b := x)
      hfi.intervalIntegrable hf.stronglyMeasurable.stronglyMeasurableAtFilter
      (hfc.continuousAt (isOpen_interior.mem_nhds hx))
    have he : (F : ℝ → ℝ) = fun y => (∫ t in Iic x, f t) + ∫ t in x..y, f t := by
      funext y
      rw [hFint, ← intervalIntegral.integral_Iic_sub_Iic hfi.integrableOn hfi.integrableOn]
      ring
    rw [he]
    exact hd.const_add _
  have hstrict : StrictMonoOn F D := by
    apply strictMonoOn_of_deriv_pos hlog.1.interior hFcont.continuousOn
    intro x hx
    rw [isOpen_interior.interior_eq] at hx
    rw [(hFder x hx).deriv]
    exact (interior_subset (s := {x | 0 < f x})) hx
  refine ⟨hstrict, ?_, hFder⟩
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨l, r, hxr, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (isOpen_interior.mem_nhds hx)
    let u := (l + x) / 2
    let w := (x + r) / 2
    have hu : u ∈ D := hsub ⟨by dsimp [u]; linarith [hxr.1], by dsimp [u]; linarith [hxr.1, hxr.2]⟩
    have hw : w ∈ D := hsub ⟨by dsimp [w]; linarith [hxr.1, hxr.2], by dsimp [w]; linarith [hxr.2]⟩
    exact ⟨(ProbabilityTheory.cdf_nonneg μ u).trans_lt (hstrict hu hx (by dsimp [u]; linarith [hxr.1])),
      (hstrict hx hw (by dsimp [w]; linarith [hxr.2])).trans_le (ProbabilityTheory.cdf_le_one μ w)⟩
  · intro p hp
    obtain ⟨l, hl⟩ := ((ProbabilityTheory.tendsto_cdf_atBot μ).eventually (Iio_mem_nhds hp.1)).exists
    obtain ⟨r, hr⟩ := ((ProbabilityTheory.tendsto_cdf_atTop μ).eventually (Ioi_mem_nhds hp.2)).exists
    obtain ⟨x, hxp⟩ := mem_range_of_exists_le_of_exists_ge hFcont ⟨l, hl.le⟩ ⟨r, hr.le⟩
    have hxleft : μ (Iic x) ≠ 0 := by
      rw [← ProbabilityTheory.ofReal_cdf, hxp]
      exact (ENNReal.ofReal_pos.mpr hp.1).ne'
    have hxright : μ (Ici x) ≠ 0 := by
      intro hz
      have he := lintegral_halfline_add μ (fun _ => 1) x
      simp only [lintegral_const, one_mul, Measure.restrict_apply_univ, measure_univ, hz, add_zero] at he
      rw [← ProbabilityTheory.ofReal_cdf, hxp] at he
      have hpone := congrArg ENNReal.toReal he
      rw [ENNReal.toReal_ofReal hp.1.le, ENNReal.toReal_one] at hpone
      exact hp.2.ne hpone
    exact ⟨x, mem_interior_positive_support_of_mass_internal hf hlog hxleft hxright, hxp⟩

/-- A measurable inverse of a CDF on its open strictly increasing
support pushes Lebesgue probability coordinates to the original law. -/
theorem probability_inverse_measurePreserving_internal (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {Q : ℝ → ℝ} {D : Set ℝ}
    (hQm : Measurable Q) (hD : IsOpen D)
    (hstrict : StrictMonoOn (ProbabilityTheory.cdf μ) D)
    (hmap : MapsTo Q (Ioo (0 : ℝ) 1) D)
    (hinv : ∀ p ∈ Ioo (0 : ℝ) 1, ProbabilityTheory.cdf μ (Q p) = p) :
    MeasurePreserving Q (volume.restrict (Ioo (0 : ℝ) 1)) μ := by
  let ν := volume.restrict (Ioo (0 : ℝ) 1)
  have : IsProbabilityMeasure ν := ⟨by simp [ν, Real.volume_Ioo]⟩
  have horder (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
      Q p ≤ t ↔ p ≤ ProbabilityTheory.cdf μ t := by
    constructor
    · intro hpt
      simpa only [hinv p hp] using ProbabilityTheory.monotone_cdf μ hpt
    · intro hpt
      by_contra hn
      have ht : t < Q p := lt_of_not_ge hn
      obtain ⟨l, r, hlr, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hD.mem_nhds (hmap hp))
      obtain ⟨z, hzlo, hzhi⟩ := exists_between (max_lt hlr.1 ht)
      have hzD : z ∈ D := hsub ⟨(le_max_left l t).trans_lt hzlo, hzhi.trans hlr.2⟩
      have htz : t ≤ z := ((le_max_right l t).trans_lt hzlo).le
      have he := (ProbabilityTheory.monotone_cdf μ htz).trans_lt (hstrict hzD (hmap hp) hzhi)
      rw [hinv p hp] at he
      exact (not_lt_of_ge hpt) he
  have hvol (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
      volume (Ioo (0 : ℝ) 1 ∩ Iic c) = ENNReal.ofReal c := by
    rcases eq_or_lt_of_le hc1 with rfl | hc
    · rw [inter_eq_left.mpr (show Ioo (0 : ℝ) 1 ⊆ Iic 1 from fun _ hp => hp.2.le), Real.volume_Ioo]
      norm_num
    · have he : Ioo (0 : ℝ) 1 ∩ Iic c = Ioc 0 c := by
        ext p
        simp only [mem_inter_iff, mem_Ioo, mem_Iic, mem_Ioc]
        constructor
        · rintro ⟨⟨hp0, _⟩, hpc⟩
          exact ⟨hp0, hpc⟩
        · rintro ⟨hp0, hpc⟩
          exact ⟨⟨hp0, hpc.trans_lt hc⟩, hpc⟩
      rw [he, Real.volume_Ioc, sub_zero]
  refine ⟨hQm, Measure.ext_of_Iic (ν.map Q) μ (fun t => ?_)⟩
  have hs : (Q ⁻¹' Iic t) ∩ Ioo (0 : ℝ) 1 = Ioo (0 : ℝ) 1 ∩ Iic (ProbabilityTheory.cdf μ t) := by
    ext p
    simp only [mem_inter_iff, mem_preimage, mem_Iic]
    constructor
    · rintro ⟨hpt, hp⟩
      exact ⟨hp, (horder p hp t).mp hpt⟩
    · rintro ⟨hp, hpt⟩
      exact ⟨(horder p hp t).mpr hpt, hp⟩
  rw [Measure.map_apply hQm measurableSet_Iic]
  change volume.restrict (Ioo (0 : ℝ) 1) (Q ⁻¹' Iic t) = _
  rw [Measure.restrict_apply (hQm measurableSet_Iic), hs,
    hvol _ (ProbabilityTheory.cdf_nonneg μ t) (ProbabilityTheory.cdf_le_one μ t),
    ProbabilityTheory.ofReal_cdf]

/-- For an actual log-concave density, a measure-preserving inverse with
the reciprocal derivative supplies the sharp coefficient. The profile
concavity is proved, not assumed, in this internal reduction. -/
theorem median_coefficient_of_density_coordinates_internal {f Q : ℝ → ℝ} {μ : Measure ℝ}
    (hlog : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    (htransport : MeasurePreserving Q (volume.restrict (Ioo (0 : ℝ) 1)) μ)
    (hmap : MapsTo Q (Ioo (0 : ℝ) 1) (interior {x | 0 < f x}))
    (hderivative : ∀ p ∈ Ioo 0 1, HasDerivAt Q (1 / f (Q p)) p)
    {m a v : ℝ} (hmedian : Q (1 / 2) = m) (hv : 0 < v)
    (hvar : (∫⁻ x, ENNReal.ofReal ((x - a) ^ 2) ∂μ) = ENNReal.ofReal v) :
    1 / (f m) ^ 2 ≤ 12 * v := by
  have hprofile := concave_density_profile_internal (f := f) (Q := Q) isOpen_interior
    (fun x hx => (interior_subset (s := {x | 0 < f x})) hx)
    (hlog.subset interior_subset hlog.1.interior) hmap hderivative
  exact median_coefficient_of_coordinates_internal htransport hprofile
    (fun p hp => (interior_subset (s := {x | 0 < f x})) (hmap hp)) hderivative hmedian hv hvar

/-- Assemble the exact coefficient of the smooth Poincaré clause of
one-dimensional log-concavity estimates once probability coordinates
with the reciprocal derivative have been supplied.  -/
theorem poincare_of_probability_coordinates_internal {f Q h : ℝ → ℝ}
    (hf : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hlog : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    (hprob : IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (f x))))
    (htransport : MeasurePreserving Q (volume.restrict (Ioo (0 : ℝ) 1))
      (volume.withDensity (fun x => ENNReal.ofReal (f x))))
    (hmap : MapsTo Q (Ioo (0 : ℝ) 1) (interior {x | 0 < f x}))
    (hderivative : ∀ p ∈ Ioo 0 1, HasDerivAt Q (1 / f (Q p)) p)
    {m a v : ℝ} (hmedian : Q (1 / 2) = m) (hv : 0 < v)
    (hvar : (∫⁻ x, ENNReal.ofReal ((x - a) ^ 2)
      ∂volume.withDensity (fun x => ENNReal.ofReal (f x))) = ENNReal.ofReal v)
    (hmleft : (volume.withDensity (fun x => ENNReal.ofReal (f x))) (Iic m) = ENNReal.ofReal (1 / 2))
    (hmright : (volume.withDensity (fun x => ENNReal.ofReal (f x))) (Ici m) = ENNReal.ofReal (1 / 2))
    (hh : ContDiff ℝ ∞ h)
    (hL2 : MemLp h 2 (volume.withDensity (fun x => ENNReal.ofReal (f x))))
    (hdL2 : MemLp (deriv h) 2 (volume.withDensity (fun x => ENNReal.ofReal (f x)))) :
    (∫⁻ x, ENNReal.ofReal ((h x - ∫ y, h y
      ∂volume.withDensity (fun x => ENNReal.ofReal (f x))) ^ 2)
      ∂volume.withDensity (fun x => ENNReal.ofReal (f x))) ≤
      ENNReal.ofReal (12 * v) * ∫⁻ x, ENNReal.ofReal ((deriv h x) ^ 2)
        ∂volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
  have hfm : 0 < f m := by
    rw [← hmedian]
    exact (interior_subset (s := {x | 0 < f x}))
      (hmap (show (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 by constructor <;> norm_num))
  have hcoefficient := median_coefficient_of_density_coordinates_internal hlog htransport
    hmap hderivative hmedian hv hvar
  exact (poincare_of_median_internal hf hnn hlog hprob hh hL2 hdL2 m hfm hmleft hmright).trans
    (by gcongr)

/-- Sharp median-density comparison supporting one-dimensional log-concavity estimates. The estimate holds for the extended
second moment about any center `a`, without a first-moment identity.
The median belongs to the interior positive support automatically. -/
theorem median_density_variance_bound_internal {f : ℝ → ℝ}
    (hf : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hlog : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    (hprob : IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (f x))))
    {a v m : ℝ} (hv : 0 < v)
    (hvar : (∫⁻ x, ENNReal.ofReal ((x - a) ^ 2)
      ∂volume.withDensity (fun x => ENNReal.ofReal (f x))) = ENNReal.ofReal v)
    (hmleft : (volume.withDensity (fun x => ENNReal.ofReal (f x))) (Iic m) = ENNReal.ofReal (1 / 2))
    (hmright : (volume.withDensity (fun x => ENNReal.ofReal (f x))) (Ici m) = ENNReal.ofReal (1 / 2)) :
    1 / (f m) ^ 2 ≤ 12 * v := by
  let μ := volume.withDensity (fun x => ENNReal.ofReal (f x))
  let F := ProbabilityTheory.cdf μ
  let D := interior {x | 0 < f x}
  have : IsProbabilityMeasure μ := hprob
  obtain ⟨hstrict, himage, hFder⟩ := cdf_positive_support_data_internal hf hnn hlog hprob
  obtain ⟨Q, hQm, hmap, hinv, hQder⟩ := exists_probability_inverse_internal hlog.1.interior
    hstrict himage hFder (fun x hx => (interior_subset (s := {x | 0 < f x})) hx)
  have htransport := probability_inverse_measurePreserving_internal μ hQm isOpen_interior hstrict hmap hinv
  have hmD : m ∈ D := median_mem_interior_positive_support_internal hf hlog hmleft hmright
  have hQhalf : Q (1 / 2) = m := by
    apply hstrict.injOn (hmap (show (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 by constructor <;> norm_num)) hmD
    rw [hinv _ (by constructor <;> norm_num), ProbabilityTheory.cdf_eq_real,
      measureReal_def, hmleft, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  exact median_coefficient_of_density_coordinates_internal hlog htransport hmap hQder hQhalf hv hvar

/-- The smooth-observable Poincaré clause of one-dimensional log-concavity estimates, with exactly the density, mean, and
extended-variance premises of the predicate and coefficient `12 * v`.
 -/
theorem smooth_poincare (f : ℝ → ℝ) (hf : Measurable f) (hnn : ∀ x, 0 ≤ f x)
    (hlog : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    (hmass : (∫⁻ x, ENNReal.ofReal (f x)) = 1) :
    let μ := volume.withDensity (fun x => ENNReal.ofReal (f x))
    ∀ a v : ℝ, Integrable (fun x => x) μ →
      (∫ x, x ∂μ) = a → 0 < v →
      (∫⁻ x, ENNReal.ofReal ((x - a) ^ 2) ∂μ) = ENNReal.ofReal v →
      ∀ h : ℝ → ℝ, ContDiff ℝ ∞ h → MemLp h 2 μ → MemLp (deriv h) 2 μ →
        (∫⁻ x, ENNReal.ofReal ((h x - ∫ y, h y ∂μ) ^ 2) ∂μ) ≤
          ENNReal.ofReal (12 * v) * ∫⁻ x, ENNReal.ofReal ((deriv h x) ^ 2) ∂μ := by
  dsimp only
  let μ := volume.withDensity (fun x => ENNReal.ofReal (f x))
  have hprob : IsProbabilityMeasure μ := ⟨by
    simpa only [μ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hmass⟩
  intro a v _hi _hmean hv hvar h hh hL2 hdL2
  obtain ⟨m, _hfm, hl, hr, hpoincare⟩ := exists_median_poincare f hf hnn hlog hmass
  have hcoefficient := median_density_variance_bound_internal hf hnn hlog hprob hv hvar hl hr
  exact (hpoincare h hh hL2 hdL2).trans (by gcongr)

end Riesz2.LogConcavePoincare

end
