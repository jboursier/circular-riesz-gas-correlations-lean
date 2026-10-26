/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BLEuclidean
public import Riesz1.HelfferSjostrand.BLEnergy
public import Riesz1.HelfferSjostrand.LogSobolevEntropyH1
public import Riesz1.ToMathlib.ConvexHessian
public import Riesz1.ToMathlib.Gaussian.AffineDensity
public import Riesz1.Frozen.External.PrekopaLeindlerProof
public import Riesz1.Frozen.External.BakryEmeryProof
public import Riesz2.ToMathlib.LogConcaveRpow
public import Mathlib.Tactic

/-!
# Convex-measure inequalities from Riesz 1

This file applies the companion library's convex-measure inequalities.

* `Riesz2.euclidean_brascamp_lieb` is the Euclidean Brascamp–Lieb inequality
  on a bounded open convex set.
* `Riesz2.prekopa_leindler` is the midpoint Prékopa–Leindler inequality.
* `Riesz2.log_sobolev_conditioning` gives the logarithmic Sobolev inequality
  with constant `2 / κ` for density proportional to `e^{-κ|x|²/2} f 1_Ω`.
  `Riesz2.log_sobolev_conditioning_of_hessian` treats a `C²` potential with
  Hessian at least `κ I`.

Log-concavity means convexity of the positive set and concavity of the logarithm
on it, as in `Riesz2.External.LogConcaveConvergence`.
The proofs use `Riesz1.External.prekopa_leindler`,
`Riesz1.External.bakry_emery` and
`Riesz1.convexOn_sub_norm_sq_of_hessian_lower`.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace

namespace Riesz2

/-! ### Euclidean Brascamp–Lieb -/

/-- The Euclidean Brascamp–Lieb inequality. Let `1 ≤ d`, and let `Ω ⊂ ℝ^d` be nonempty, bounded,
open and convex. Let `V` be `C²` on `Ω` with `∇²V ≥ κ I` for some `κ > 0`. Let `ν` be the
probability `Z⁻¹ e^{-V} dx` on `Ω`, where `Z = ∫_Ω e^{-V}`. Then `0 < Z < ∞`, and for every `F` in
`H¹(ν)` with weak gradient `G`,
`Var_ν F ≤ ∫ ⟨G, (∇²V)⁻¹ G⟩ dν ≤ κ⁻¹ ∫ |G|² dν`.
The inverse energy is written as the variational energy `sup_h (2⟨G, h⟩ - ∇²V(h, h))`. The identity
of this energy with `⟨G, (∇²V)⁻¹ G⟩` at each point of `Ω` is part of the conclusion, and the energy
is integrable. -/
theorem euclidean_brascamp_lieb {d : ℕ} (hd : 1 ≤ d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩb : Bornology.IsBounded Ω) (hΩo : IsOpen Ω)
    (hΩne : Ω.Nonempty) (hΩc : Convex ℝ Ω)
    {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiffOn ℝ 2 V Ω) {κ : ℝ} (hκ : 0 < κ)
    (hH : ∀ x ∈ Ω, ∀ h : EuclideanSpace ℝ (Fin d), κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h)
    (ν : Measure (EuclideanSpace ℝ (Fin d)))
    (hν : ν = (volume.restrict Ω).withDensity
      (fun x => ENNReal.ofReal (Real.exp (-V x) / ∫ y in Ω, Real.exp (-V y)))) :
    (0 < ∫⁻ x in Ω, ENNReal.ofReal (Real.exp (-V x))) ∧
      (∫⁻ x in Ω, ENNReal.ofReal (Real.exp (-V x))) < ⊤ ∧
      IsProbabilityMeasure ν ∧
      (∀ (F : EuclideanSpace ℝ (Fin d) → ℝ)
          (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
        Riesz1.WeightedSobolev.IsWeightedH1 ν Ω F G →
          (∫ x, (F x - ∫ y, F y ∂ν) ^ 2 ∂ν) ≤
              ∫ x, sSup (Set.range fun h : EuclideanSpace ℝ (Fin d) =>
                2 * ⟪G x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h) ∂ν ∧
            Integrable (fun x => sSup (Set.range fun h : EuclideanSpace ℝ (Fin d) =>
              2 * ⟪G x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h)) ν ∧
            (∫ x, sSup (Set.range fun h : EuclideanSpace ℝ (Fin d) =>
                2 * ⟪G x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h) ∂ν) ≤
              κ⁻¹ * ∫ x, ‖G x‖ ^ 2 ∂ν) ∧
      (∀ (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
          (x : EuclideanSpace ℝ (Fin d)),
        x ∈ Ω → ∃ hB : IsCoercive (fderiv ℝ (fderiv ℝ V) x),
          sSup (Set.range fun h : EuclideanSpace ℝ (Fin d) =>
            2 * ⟪G x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h) =
            ⟪G x, hB.continuousLinearEquivOfBilin.symm (G x)⟫_ℝ) := by
  have key := Riesz1.brascamp_lieb_euclidean Riesz1.External.prekopa_leindler hd hΩb hΩo hΩne
    hΩc hV hκ hH
  dsimp only at key
  obtain ⟨hZpos, hZfin, hprob, hvar, hid⟩ := key
  have hνeq : ν = (volume.restrict Ω).tilted (fun x => -V x) := hν
  subst hνeq
  refine ⟨hZpos, hZfin, hprob, fun F G hFG => ?_, hid⟩
  obtain ⟨hV1, hV2, -⟩ := hvar F G hFG
  refine ⟨hV1, hV2, ?_⟩
  have hae : ∀ᵐ x ∂((volume.restrict Ω).tilted (fun x => -V x)), x ∈ Ω :=
    (tilted_absolutelyContinuous _ _).ae_le (ae_restrict_mem hΩo.measurableSet)
  have hbound : ∀ᵐ x ∂((volume.restrict Ω).tilted (fun x => -V x)),
      sSup (Set.range fun h : EuclideanSpace ℝ (Fin d) =>
        2 * ⟪G x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h) ≤ ‖G x‖ ^ 2 / κ := by
    filter_upwards [hae] with x hx
    exact (Riesz1.bl_variational_energy_bounds (fderiv ℝ (fderiv ℝ V) x) (G x) hκ
      (hH x hx)).2
  have hGint : Integrable (fun x => ‖G x‖ ^ 2 / κ)
      ((volume.restrict Ω).tilted (fun x => -V x)) :=
    (hFG.memLp_grad.norm.integrable_sq).div_const κ
  have hmono := integral_mono_ae hV2 hGint hbound
  rw [integral_div, div_eq_inv_mul] at hmono
  exact hmono

/-! ### Midpoint Prékopa–Leindler -/

/-- The Prékopa–Leindler inequality. Let `1 ≤ d`, and let `f₀, f₁, h : ℝ^d → [0, ∞)` be bounded
Borel functions with bounded supports. Suppose `h((x + y)/2) ≥ √(f₀(x) f₁(y))` for all `x, y`.
Then `f₀`, `f₁` and `h` are integrable, and `√((∫ f₀)(∫ f₁)) ≤ ∫ h`. -/
theorem prekopa_leindler {d : ℕ} (hd : 1 ≤ d) (f₀ f₁ h : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf₀ : Measurable f₀) (hf₁ : Measurable f₁) (hh : Measurable h)
    (hf₀0 : ∀ x, 0 ≤ f₀ x) (hf₁0 : ∀ x, 0 ≤ f₁ x) (hh0 : ∀ x, 0 ≤ h x)
    (hf₀b : Bornology.IsBounded (Set.range f₀)) (hf₁b : Bornology.IsBounded (Set.range f₁))
    (hhb : Bornology.IsBounded (Set.range h))
    (hf₀s : Bornology.IsBounded (Function.support f₀))
    (hf₁s : Bornology.IsBounded (Function.support f₁))
    (hhs : Bornology.IsBounded (Function.support h))
    (hmid : ∀ x y : EuclideanSpace ℝ (Fin d),
      Real.sqrt (f₀ x * f₁ y) ≤ h ((1 / 2 : ℝ) • (x + y))) :
    Integrable f₀ ∧ Integrable f₁ ∧ Integrable h ∧
      Real.sqrt ((∫ x, f₀ x) * ∫ x, f₁ x) ≤ ∫ x, h x := by
  obtain ⟨h₀, h₁, h₂, h₃⟩ := Riesz1.External.prekopa_leindler d hd f₀ f₁ h hf₀ hf₁ hh hf₀0
    hf₁0 hh0 hf₀b hf₁b hhb hf₀s hf₁s hhs hmid
  exact ⟨h₀, h₁, h₂, h₃⟩

/-! ### Logarithmic Sobolev inequality for log-concave densities on a convex domain -/

/-- The Bakry–Émery criterion. Let `1 ≤ d`, let `Ω ⊂ ℝ^d` be a convex open set, and let `κ > 0`.
Let `f : ℝ^d → [0, ∞)` be Borel and log-concave, in the sense that its positive set is convex and
`log ∘ f` is concave on it. Let `ρ` be a probability measure with density proportional to
`e^{-κ|x|²/2} f(x)` on `Ω`, with proportionality constant `c`. Then for every `h ∈ H¹(ρ)` with weak
gradient `G`, the functions `h²`, `h² log h²` and `|G|²` are `ρ`-integrable, and
`Ent_ρ(h²) ≤ (2/κ) ∫ |G|² dρ`, where
`Ent_ρ(h²) = ∫ h² log h² dρ - (∫ h² dρ) log (∫ h² dρ)`. -/
theorem log_sobolev_conditioning {d : ℕ} (hd : 1 ≤ d) {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hΩc : Convex ℝ Ω) (hΩo : IsOpen Ω) {κ : ℝ} (hκ : 0 < κ)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hflc : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ρ] {c : ℝ}
    (hρ : ρ = (volume.restrict Ω).withDensity
      (fun x => ENNReal.ofReal (c * (Real.exp (-(κ / 2 * ‖x‖ ^ 2)) * f x)))) :
    ∀ (F : EuclideanSpace ℝ (Fin d) → ℝ)
      (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
      Riesz1.WeightedSobolev.IsWeightedH1 ρ Ω F G →
        Integrable (fun x => F x ^ 2) ρ ∧
        Integrable (fun x => F x ^ 2 * Real.log (F x ^ 2)) ρ ∧
        Integrable (fun x => ‖G x‖ ^ 2) ρ ∧
        (∫ x, F x ^ 2 * Real.log (F x ^ 2) ∂ρ) -
            (∫ x, F x ^ 2 ∂ρ) * Real.log (∫ x, F x ^ 2 ∂ρ) ≤
          2 / κ * ∫ x, ‖G x‖ ^ 2 ∂ρ := by
  intro F G hFG
  obtain ⟨w, hw_def⟩ : ∃ w : ℝ, w = κ⁻¹ := ⟨_, rfl⟩
  have hw : 0 < w := by rw [hw_def]; exact inv_pos.mpr hκ
  have hwκ : (2 * w)⁻¹ = κ / 2 := by rw [hw_def]; field_simp
  have h2w : 2 * w = 2 / κ := by rw [hw_def]; ring
  -- The Gaussian mass of `Ω` is positive, since `ρ` is a probability measure.
  have hvolΩ : volume Ω ≠ 0 := by
    intro h0
    have hres : volume.restrict Ω = 0 := Measure.restrict_eq_zero.mpr h0
    have h1 : ρ Set.univ = 1 := measure_univ
    rw [hρ, hres] at h1
    simp at h1
  have hZ : 0 < ∫ y in Ω, Real.exp (-((2 * w)⁻¹ * ‖y‖ ^ 2)) := by
    have hint : Integrable
        (fun y : EuclideanSpace ℝ (Fin d) => Real.exp (-((2 * w)⁻¹ * ‖y‖ ^ 2))) := by
      simpa using Riesz1.Gaussian.integrable_exp_quadratic_affine
        (E := EuclideanSpace ℝ (Fin d)) hw 0 0
    rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun y => (Real.exp_pos _).le)
      hint.integrableOn]
    have hsupp : Function.support
        (fun y : EuclideanSpace ℝ (Fin d) => Real.exp (-((2 * w)⁻¹ * ‖y‖ ^ 2))) = Set.univ :=
      Set.eq_univ_of_forall fun y => Function.mem_support.mpr (Real.exp_pos _).ne'
    rw [hsupp, Set.univ_inter]
    exact pos_iff_ne_zero.mpr hvolΩ
  set Z : ℝ := ∫ y in Ω, Real.exp (-((2 * w)⁻¹ * ‖y‖ ^ 2)) with hZdef
  have hZne : Z ≠ 0 := hZ.ne'
  -- The constant `c` is positive, since `ρ` is a probability measure.
  have hc : 0 < c := by
    by_contra hcn
    have hcn' : c ≤ 0 := not_lt.mp hcn
    have hfun : (fun x : EuclideanSpace ℝ (Fin d) =>
        ENNReal.ofReal (c * (Real.exp (-(κ / 2 * ‖x‖ ^ 2)) * f x))) = fun _ => 0 := by
      funext x
      refine ENNReal.ofReal_eq_zero.mpr ?_
      have := mul_nonneg (Real.exp_pos (-(κ / 2 * ‖x‖ ^ 2))).le (hf0 x)
      nlinarith
    have h0 : ρ = 0 := by
      rw [hρ, hfun]
      simp
    have h1 : ρ Set.univ = 1 := measure_univ
    rw [h0] at h1
    simp at h1
  -- Rewrite `ρ` in the normalized form of `logSobolev_conditioning_H1`.
  have hνρ : ρ = ((volume.restrict Ω).withDensity
      (fun x => ENNReal.ofReal (Real.exp (-((2 * w)⁻¹ * ‖x‖ ^ 2)) / Z))).withDensity
      (fun x => ENNReal.ofReal (c * Z * f x)) := by
    have hg1 : Measurable (fun x : EuclideanSpace ℝ (Fin d) =>
        ENNReal.ofReal (Real.exp (-((2 * w)⁻¹ * ‖x‖ ^ 2)) / Z)) :=
      (by fun_prop : Measurable fun x : EuclideanSpace ℝ (Fin d) =>
        Real.exp (-((2 * w)⁻¹ * ‖x‖ ^ 2)) / Z).ennreal_ofReal
    have hg2 : Measurable (fun x : EuclideanSpace ℝ (Fin d) => ENNReal.ofReal (c * Z * f x)) :=
      (hf.const_mul (c * Z)).ennreal_ofReal
    rw [hρ, ← withDensity_mul₀ hg1.aemeasurable hg2.aemeasurable]
    congr 1
    funext x
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le hZ.le), hwκ]
    congr 1
    field_simp
  -- The log-concavity of `f` gives the multiplicative inequality of `c Z f`, on `Ω`.
  have hlog : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ t : ℝ, 0 < t → t < 1 →
      (c * Z * f x) ^ t * (c * Z * f y) ^ (1 - t) ≤ c * Z * f (t • x + (1 - t) • y) := by
    intro x _ y _ t ht0 ht1
    have hcZ : 0 < c * Z := mul_pos hc hZ
    have hk := Riesz2.rpow_mul_rpow_le_of_concaveOn_log hf0 hflc x y ht0 ht1
    have hsplit : (c * Z) ^ t * (c * Z) ^ (1 - t) = c * Z := by
      rw [← Real.rpow_add hcZ]
      simp
    rw [Real.mul_rpow hcZ.le (hf0 x), Real.mul_rpow hcZ.le (hf0 y)]
    calc (c * Z) ^ t * f x ^ t * ((c * Z) ^ (1 - t) * f y ^ (1 - t))
        = (c * Z) ^ t * (c * Z) ^ (1 - t) * (f x ^ t * f y ^ (1 - t)) := by ring
      _ = c * Z * (f x ^ t * f y ^ (1 - t)) := by rw [hsplit]
      _ ≤ c * Z * f (t • x + (1 - t) • y) := mul_le_mul_of_nonneg_left hk hcZ.le
  have hfG : ∀ x ∈ Ω, 0 ≤ c * Z * f x := fun x _ => mul_nonneg (mul_pos hc hZ).le (hf0 x)
  have hU : ∀ᵐ x ∂ρ, x ∈ closure Ω := by
    rw [hρ]
    filter_upwards [(withDensity_absolutelyContinuous (volume.restrict Ω) _).ae_le
      (ae_restrict_mem hΩo.measurableSet)] with x hx
    exact subset_closure hx
  obtain ⟨hI1, hI2, hI3, hI4⟩ := Riesz1.LogSobolevEntropy.logSobolev_conditioning_H1
    Riesz1.External.bakry_emery hd hw hΩc hΩo.measurableSet hZ
    (hf.const_mul (c * Z)) hfG hlog ρ hνρ hU hFG
  have hneg1 : ∀ x, Real.negMulLog (F x ^ 2) = -(F x ^ 2 * Real.log (F x ^ 2)) := fun x => by
    simp only [Real.negMulLog, neg_mul]
  have hneg2 : Real.negMulLog (∫ x, F x ^ 2 ∂ρ) =
      -((∫ x, F x ^ 2 ∂ρ) * Real.log (∫ x, F x ^ 2 ∂ρ)) := by
    simp only [Real.negMulLog, neg_mul]
  have hJ : Integrable (fun x => F x ^ 2 * Real.log (F x ^ 2)) ρ := by
    simpa [Real.negMulLog] using hI2.neg
  simp only [hneg1, integral_neg, hneg2] at hI4
  rw [h2w] at hI4
  exact ⟨hI1, hJ, hI3, by linarith⟩

/-- The Bakry–Émery criterion, the form for a `C²` potential. Let `1 ≤ d`, let `Ω ⊂ ℝ^d` be a
convex open set, and let `V` be `C²` on `Ω` with `∇²V ≥ κ I` for some `κ > 0`. Let `ρ` be a
probability measure with density proportional to `e^{-V}` on `Ω`, with proportionality constant
`c`. Then the conclusion of `Riesz2.log_sobolev_conditioning` holds for every `h ∈ H¹(ρ)` with weak
gradient `G`. -/
theorem log_sobolev_conditioning_of_hessian {d : ℕ} (hd : 1 ≤ d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩc : Convex ℝ Ω) (hΩo : IsOpen Ω)
    {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiffOn ℝ 2 V Ω) {κ : ℝ} (hκ : 0 < κ)
    (hH : ∀ x ∈ Ω, ∀ h : EuclideanSpace ℝ (Fin d), κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h)
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ρ] {c : ℝ}
    (hρ : ρ = (volume.restrict Ω).withDensity
      (fun x => ENNReal.ofReal (c * Real.exp (-V x)))) :
    ∀ (F : EuclideanSpace ℝ (Fin d) → ℝ)
      (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
      Riesz1.WeightedSobolev.IsWeightedH1 ρ Ω F G →
        Integrable (fun x => F x ^ 2) ρ ∧
        Integrable (fun x => F x ^ 2 * Real.log (F x ^ 2)) ρ ∧
        Integrable (fun x => ‖G x‖ ^ 2) ρ ∧
        (∫ x, F x ^ 2 * Real.log (F x ^ 2) ∂ρ) -
            (∫ x, F x ^ 2 ∂ρ) * Real.log (∫ x, F x ^ 2 ∂ρ) ≤
          2 / κ * ∫ x, ‖G x‖ ^ 2 ∂ρ := by
  classical
  -- `V - κ|x|²/2` is convex on `Ω`, so `e^{-V + κ|x|²/2}` is log-concave there.
  have hW : ConvexOn ℝ Ω (fun x => V x - κ / 2 * ‖x‖ ^ 2) :=
    Riesz1.convexOn_sub_norm_sq_of_hessian_lower hΩc hΩo hV hH
  have hWc : ContinuousOn (fun x => V x - κ / 2 * ‖x‖ ^ 2) Ω :=
    hV.continuousOn.sub (by fun_prop :
      Continuous fun x : EuclideanSpace ℝ (Fin d) => κ / 2 * ‖x‖ ^ 2).continuousOn
  obtain ⟨f, hfdef⟩ : ∃ f : EuclideanSpace ℝ (Fin d) → ℝ,
      f = Ω.piecewise (fun x => Real.exp (-(V x - κ / 2 * ‖x‖ ^ 2))) (fun _ => 0) := ⟨_, rfl⟩
  have hfΩ : ∀ x ∈ Ω, f x = Real.exp (-(V x - κ / 2 * ‖x‖ ^ 2)) := fun x hx => by
    rw [hfdef, Set.piecewise_eq_of_mem _ _ _ hx]
  have hfout : ∀ x ∉ Ω, f x = 0 := fun x hx => by
    rw [hfdef, Set.piecewise_eq_of_notMem _ _ _ hx]
  have hf : Measurable f := by
    rw [hfdef]
    exact ContinuousOn.measurable_piecewise
      (Real.continuous_exp.comp_continuousOn hWc.neg) continuousOn_const hΩo.measurableSet
  have hf0 : ∀ x, 0 ≤ f x := fun x => by
    by_cases hx : x ∈ Ω
    · rw [hfΩ x hx]
      exact (Real.exp_pos _).le
    · simp [hfout x hx]
  have hset : {x | 0 < f x} = Ω := by
    ext x
    by_cases hx : x ∈ Ω
    · show 0 < f x ↔ x ∈ Ω
      rw [hfΩ x hx]
      exact ⟨fun _ => hx, fun _ => Real.exp_pos _⟩
    · show 0 < f x ↔ x ∈ Ω
      rw [hfout x hx]
      exact ⟨fun h => absurd h (lt_irrefl 0), fun h => absurd h hx⟩
  have hflc : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) := by
    rw [hset]
    refine (neg_concaveOn_iff.mpr hW).congr fun x hx => ?_
    simp only [Pi.neg_apply]
    rw [hfΩ x hx, Real.log_exp]
  have hρ' : ρ = (volume.restrict Ω).withDensity
      (fun x => ENNReal.ofReal (c * (Real.exp (-(κ / 2 * ‖x‖ ^ 2)) * f x))) := by
    rw [hρ]
    refine withDensity_congr_ae ?_
    filter_upwards [ae_restrict_mem hΩo.measurableSet] with x hx
    rw [hfΩ x hx, ← Real.exp_add,
      show -V x = -(κ / 2 * ‖x‖ ^ 2) + -(V x - κ / 2 * ‖x‖ ^ 2) by ring]
  exact log_sobolev_conditioning hd hΩc hΩo hκ hf hf0 hflc ρ hρ'

end Riesz2

end

end
