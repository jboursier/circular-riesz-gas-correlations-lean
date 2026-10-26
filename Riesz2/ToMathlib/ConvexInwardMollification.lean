/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Tactic

/-!
# Mollification inside a convex set

Contract toward an interior point before applying a normalized smooth bump.
The resulting coordinate estimates use the original convex set, including
its boundary, and preserve coordinate support. These estimates support
the proof of Proposition 6.6.
-/

public section
noncomputable section

open MeasureTheory Set Filter Metric
open scoped ContDiff Convolution Topology NNReal

namespace Riesz2.ConvexInwardMollification

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)]

/-- Contraction toward `c`, followed by convolution with a normalized bump.
Local integrability makes the convolution an integral on its whole carrier. -/
def mollify (F : E → ℝ) (_hF : LocallyIntegrable F volume) (c : E) (t : ℝ) (b : ContDiffBump (0 : E)) : E → ℝ :=
  fun x => (b.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F)
    ((1-t) • x + t • c)

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)] in
/-- Every sample stays in the same convex set, including when `x` is on
its boundary. The ball at `c` is consumed in proportion to the contraction. -/
theorem sample_mem {A : Set E} (hA : Convex ℝ A) {c x y : E} {r t : ℝ}
    (hc : ball c r ⊆ A) (hx : x ∈ A) (ht : 0 < t) (ht1 : t ≤ 1)
    (hy : ‖y‖ < t*r) : (1-t) • x + t • c - y ∈ A := by
  have hcy : c - t⁻¹ • y ∈ ball c r := by
    rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr ht.le)]
    exact (inv_mul_lt_iff₀ ht).mpr hy
  have hh := hA hx (hc hcy) (sub_nonneg.mpr ht1) ht.le (by ring : 1-t+t=1)
  rw [smul_sub, smul_smul, mul_inv_cancel₀ ht.ne', one_smul] at hh
  simpa only [add_sub_assoc] using hh

/-- Smoothness of the contracted convolution. -/
theorem contDiff {F : E → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F)
    (c : E) (t : ℝ) (b : ContDiffBump (0 : E)) :
    ContDiff ℝ ∞ (mollify F hF.continuous.locallyIntegrable c t b) :=
  (b.hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) b.contDiff_normed
      hF.continuous.locallyIntegrable).comp (by fun_prop)

/-- A normalized convolution preserves any paired difference bound which
holds at every sample in the support of its kernel. -/
theorem paired_bound {F : E → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F)
    (b : ContDiffBump (0 : E)) (u v : E) {D : ℝ}
    (hD : ∀ y, ‖y‖ < b.rOut → |F (u-y)-F (v-y)| ≤ D) :
    |(b.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F) u -
      (b.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F) v| ≤ D := by
  have hi (z : E) : Integrable (fun y => b.normed volume y * F (z-y)) volume := by
    simpa only [ConvolutionExistsAt, ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
      (b.hasCompactSupport_normed (μ := volume)).convolutionExists_left (μ := volume)
        (ContinuousLinearMap.lsmul ℝ ℝ) b.continuous_normed
          hF.continuous.locallyIntegrable z
  change |(∫ y, b.normed volume y * F (u-y)) -
    (∫ y, b.normed volume y * F (v-y))| ≤ D
  rw [← integral_sub (hi u) (hi v)]
  calc
    _ = ‖∫ y, b.normed volume y * (F (u-y)-F (v-y))‖ := by
      simp only [mul_sub, Real.norm_eq_abs]
    _ ≤ ∫ y, b.normed volume y * D := by
      apply norm_integral_le_of_norm_le (b.integrable_normed.mul_const D)
      filter_upwards [] with y
      rw [norm_mul, Real.norm_of_nonneg (b.nonneg_normed y), Real.norm_eq_abs]
      by_cases hy : b.normed volume y = 0
      · simp [hy]
      · apply mul_le_mul_of_nonneg_left _ (b.nonneg_normed y)
        apply hD y
        have hs : y ∈ Function.support (b.normed volume) := hy
        rwa [b.support_normed_eq, mem_ball, dist_zero_right] at hs
    _ = D := by rw [integral_mul_const, b.integral_normed, one_mul]

/-- Global Lipschitz constants do not increase under inward mollification. -/
theorem lipschitzWith {F : E → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F)
    (c : E) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (b : ContDiffBump (0 : E)) :
    LipschitzWith C (mollify F hF.continuous.locallyIntegrable c t b) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  change |mollify F hF.continuous.locallyIntegrable c t b x - mollify F hF.continuous.locallyIntegrable c t b z| ≤ _
  apply paired_bound hF b
  intro y _
  have hh := hF.norm_sub_le ((1-t) • x+t • c-y) ((1-t) • z+t • c-y)
  rw [sub_sub_sub_cancel_right, add_sub_add_right_eq_sub, ← smul_sub,
    norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr ht1)] at hh
  exact hh.trans (by
    rw [dist_eq_norm]
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left (norm_nonneg _) (by linarith)) C.coe_nonneg)

/-- Quantitative convergence, uniform on every bounded set. -/
theorem error_bound {F : E → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F)
    (c : E) {t : ℝ} (ht : 0 ≤ t) (b : ContDiffBump (0 : E)) (x : E) :
    |mollify F hF.continuous.locallyIntegrable c t b x-F x| ≤ C * (b.rOut + t*‖c-x‖) := by
  have he := b.dist_normed_convolution_le (μ := volume) hF.continuous.aestronglyMeasurable
    (x₀ := (1-t) • x+t • c) (ε := C*b.rOut) (fun y hy =>
      (hF.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left (mem_ball.mp hy).le C.coe_nonneg))
  have hh := hF.norm_sub_le ((1-t) • x+t • c) x
  have hid : (1-t) • x+t • c-x = t • (c-x) := by module
  rw [hid, norm_smul, Real.norm_of_nonneg ht] at hh
  exact (abs_sub_le _ _ _).trans ((add_le_add he hh).trans_eq (by ring))

section Coordinates

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Inward convolution preserves bounds along each coordinate on the original
convex set, with no enlargement of that set. -/
theorem coordinate_bound {F : (ι → ℝ) → ℝ} {C : ℝ≥0} (hF : LipschitzWith C F)
    {A : Set (ι → ℝ)} (hA : Convex ℝ A) {c : ι → ℝ} {r t : ℝ}
    (hc : ball c r ⊆ A) (ht : 0 < t) (ht1 : t ≤ 1)
    (b : ContDiffBump (0 : ι → ℝ)) (hb : b.rOut ≤ t*r)
    (j : ι) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ x u, x ∈ A → Function.update x j u ∈ A →
      |F (Function.update x j u)-F x| ≤ D*|u-x j|)
    (x : ι → ℝ) (u : ℝ) (hx : x ∈ A) (hu : Function.update x j u ∈ A) :
    |mollify F hF.continuous.locallyIntegrable c t b (Function.update x j u)-mollify F hF.continuous.locallyIntegrable c t b x| ≤ D*|u-x j| := by
  apply paired_bound hF b
  intro y hy
  have hxy := sample_mem hA hc hx ht ht1 (hy.trans_le hb)
  have huy := sample_mem hA hc hu ht ht1 (hy.trans_le hb)
  have he : (1-t) • Function.update x j u+t • c-y =
      Function.update ((1-t) • x+t • c-y) j ((1-t)*u+t*c j-y j) := by
    ext i
    by_cases hi : i=j <;> simp [hi, Function.update_of_ne]
  rw [he] at huy ⊢
  have hh := hD _ _ hxy huy
  have he' : (1-t)*u+t*c j-y j-((1-t) • x+t • c-y) j = (1-t)*(u-x j) := by
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he', abs_mul, abs_of_nonneg (sub_nonneg.mpr ht1)] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_left (abs_nonneg _) (by linarith)) hD0)

omit [DecidableEq ι] in
/-- Coordinate support survives the contraction and convolution literally. -/
theorem dependsOn {F : (ι → ℝ) → ℝ} (hFi : LocallyIntegrable F volume) (c : ι → ℝ) (t : ℝ)
    (b : ContDiffBump (0 : ι → ℝ)) (J : Set ι)
    (hF : ∀ x z, (∀ j ∈ J, x j=z j) → F x=F z) :
    ∀ x z, (∀ j ∈ J, x j=z j) → mollify F hFi c t b x=mollify F hFi c t b z := by
  intro x z hx
  unfold mollify convolution
  apply integral_congr_ae
  filter_upwards [] with y
  congr 1
  apply hF
  intro j hj
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hx j hj]

end Coordinates
end Riesz2.ConvexInwardMollification
