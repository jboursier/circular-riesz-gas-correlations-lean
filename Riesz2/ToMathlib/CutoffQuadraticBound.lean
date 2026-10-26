/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.PhysicalCutoff
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Tactic

/-!
# Quadratic growth of the physical cutoff

Every physical cutoff `θ` satisfies `θ t ≤ K t²` for `t ≥ 0`, with `K` depending on `θ`. The
function `t ↦ (C/2) t² - θ t` is convex on the half-line, because its second derivative
`C - θ''` is nonnegative there. Convexity, the vanishing of `θ` on `[0, 1/2]`, and the
nonnegativity of `θ` then give nonnegativity of `t ↦ (C/2) t² - θ t`.
-/

public section

open Set Filter Topology

namespace Riesz2

/-- A physical cutoff has quadratic growth: there is `K ≥ 0` with `θ t ≤ K t²` for every
`t ≥ 0`. The constant depends on the cutoff through its curvature bound. -/
theorem PhysicalCutoff.exists_sq_bound (θ : PhysicalCutoff) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 ≤ t → θ.val t ≤ K * t ^ 2 := by
  obtain ⟨hcd, -, -, hzero, C, hC1, hCd, -⟩ := θ.property
  have hθ0 : θ.val 0 = 0 := hzero 0 ⟨le_rfl, by norm_num⟩
  have hθhalf : θ.val (1 / 2) = 0 := hzero (1 / 2) ⟨by norm_num, le_rfl⟩
  have hopen : IsOpen (Ioi (0 : ℝ)) := isOpen_Ioi
  have hcdpos : ContDiffOn ℝ (⊤ : ℕ∞) θ.val (Ioi 0) := hcd.mono Ioi_subset_Ici_self
  have hdcd : ContDiffOn ℝ (⊤ : ℕ∞) (deriv θ.val) (Ioi 0) :=
    hcdpos.deriv_of_isOpen hopen (by simp)
  have hθdiff : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt θ.val (deriv θ.val t) t := fun t ht =>
    ((hcdpos.differentiableOn (by simp)) t ht).differentiableAt (hopen.mem_nhds ht) |>.hasDerivAt
  have hdθdiff : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (deriv θ.val) (deriv (deriv θ.val) t) t :=
    fun t ht => ((hdcd.differentiableOn (by simp)) t ht).differentiableAt
      (hopen.mem_nhds ht) |>.hasDerivAt
  -- The auxiliary convex function `φ t = (C/2) t² - θ t`.
  let φ : ℝ → ℝ := fun t => (C / 2) * t ^ 2 - θ.val t
  have hφd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt φ (C * t - deriv θ.val t) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => (C / 2) * t ^ 2) (C / 2 * (2 * t)) t := by
      simpa using (hasDerivAt_pow 2 t).const_mul (C / 2)
    have h2 := h1.sub (hθdiff t ht)
    convert h2 using 1
    ring
  have hφderiv : ∀ t ∈ Ioi (0 : ℝ), deriv φ t = C * t - deriv θ.val t :=
    fun t ht => (hφd t ht).deriv
  have hφdd : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (deriv φ) (C - deriv (deriv θ.val) t) t := by
    intro t ht
    have hev : deriv φ =ᶠ[𝓝 t] fun u => C * u - deriv θ.val u :=
      Filter.eventually_of_mem (hopen.mem_nhds ht) hφderiv
    have h1 : HasDerivAt (fun u : ℝ => C * u - deriv θ.val u) (C * 1 - deriv (deriv θ.val) t) t :=
      ((hasDerivAt_id t).const_mul C).sub (hdθdiff t ht)
    exact (h1.congr_of_eventuallyEq hev).congr_deriv (by ring)
  have hφconv : ConvexOn ℝ (Ici 0) φ := by
    refine convexOn_of_deriv2_nonneg (convex_Ici 0) ?_ ?_ ?_ ?_
    · have hφc : ContinuousOn φ (Ici 0) :=
        ((continuousOn_const.mul (continuous_pow 2).continuousOn).sub hcd.continuousOn)
      exact hφc
    · rw [interior_Ici]
      intro t ht
      exact (hφd t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro t ht
      exact (hφdd t ht).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro t ht
      show 0 ≤ deriv (deriv φ) t
      rw [(hφdd t ht).deriv]
      have := hCd t ht
      linarith [this.2]
  -- Nonnegativity of `φ` on the half-line.
  have hφnn : ∀ t : ℝ, 0 ≤ t → 0 ≤ φ t := by
    intro t ht
    rcases le_total t (1 / 2) with h | h
    · have h0 : θ.val t = 0 := hzero t ⟨ht, h⟩
      simp only [φ, h0, sub_zero]
      positivity
    · have htpos : 0 < t := by linarith
      have hlam : 0 < 1 / (2 * t) := by positivity
      have hlam1 : 1 / (2 * t) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      have hc := hφconv.2 (show (0 : ℝ) ∈ Ici 0 from le_rfl)
        (show t ∈ Ici 0 from ht) (by linarith : (0 : ℝ) ≤ 1 - 1 / (2 * t))
        hlam.le (by ring : (1 - 1 / (2 * t)) + 1 / (2 * t) = 1)
      have hlt : (1 - 1 / (2 * t)) • (0 : ℝ) + (1 / (2 * t)) • t = 1 / 2 := by
        simp only [smul_eq_mul, mul_zero, zero_add]
        field_simp
      rw [hlt] at hc
      have hφ0 : φ 0 = 0 := by simp [φ, hθ0]
      have hφhalf : 0 ≤ φ (1 / 2) := by
        simp only [φ, hθhalf, sub_zero]
        positivity
      simp only [smul_eq_mul, hφ0, mul_zero, zero_add] at hc
      nlinarith
  refine ⟨C / 2, by linarith, fun t ht => ?_⟩
  have h := hφnn t ht
  simp only [φ] at h
  linarith

end Riesz2
