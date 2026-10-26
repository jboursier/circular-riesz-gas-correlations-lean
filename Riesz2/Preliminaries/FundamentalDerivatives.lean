/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Bridges.KernelIdentification
public import Riesz2.Preliminaries.FundamentalHeatRoute

/-!
# Fundamental solution and all derivatives

See Lemma 2.3 of the paper, using the literal Riesz 1 mean-zero circle kernel of
Subsection 1.1, its Fourier normalization Subsection 2.2, and the Hurwitz zeta notation
Subsection 2.2. The representation follows the manuscript heat-kernel route:
Gamma/Fourier identification, continuity, centered images, Fubini, then the
finite-part limit and Hurwitz notation. The companion derivative API supplies
the signed derivative formula and its convergence, with positive curvature
and strict convexity.

All derivative and image-series assertions are restricted to real lifts off the
integers. The zeta formula is restricted to `(0,1)`, so both Hurwitz arguments
are positive. No assertion uses the analytic value at a collision.
-/

public section

open Filter Set Topology
open scoped ContDiff

namespace Riesz2

/-- See Lemma 2.3 of the paper: the mean-zero fundamental solution is the sum of
two Hurwitz zeta values and the limit of the renormalized symmetric image sums
on `(0,1)`. For every order `p ≥ 1`, its signed image formula is absolutely and
locally uniformly convergent off the integers. The derivatives of the finite
renormalized sums also converge locally uniformly to that derivative. Its second
derivative is positive off the integers, and it is strictly convex on `(0,1)`.

The parameter `s : Riesz1.RieszExponent` means exactly `0 < s.val < 1`.
The canonical representative is identified with the mean-zero solution of
Subsection 2.2 by `companionKernelIdentification` and `Riesz1.fundamental`. -/
theorem fundamentalSolution_all_derivatives (s : Riesz1.RieszExponent) :
    (∀ x : ℝ, 0 < x → x < 1 →
      Riesz1.rieszRepresentative s x =
          (Riesz1.hurwitzZetaPos (s.val : ℂ) x).re +
            (Riesz1.hurwitzZetaPos (s.val : ℂ) (1 - x)).re ∧
      Tendsto (fun M : ℕ =>
        (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |(k : ℝ) + x| ^ (-s.val)) -
          2 * (M : ℝ) ^ (1 - s.val) / (1 - s.val)) atTop
        (𝓝 (Riesz1.rieszRepresentative s x))) ∧
    (∀ p : ℕ, 1 ≤ p →
      (∀ x : ℝ, (x : UnitAddCircle) ≠ 0 →
        iteratedDeriv p (fun y : ℝ => Riesz1.rieszRepresentative s y) x =
          ((-1 : ℝ) ^ p * ∏ j ∈ Finset.range p, (s.val + (j : ℝ))) *
            ∑' k : ℤ, Real.sign (x + k) ^ p / |x + k| ^ (s.val + (p : ℝ))) ∧
      (∀ x : ℝ, (x : UnitAddCircle) ≠ 0 →
        Summable (fun k : ℤ =>
          ‖Real.sign (x + k) ^ p / |x + k| ^ (s.val + (p : ℝ))‖)) ∧
      HasSumLocallyUniformlyOn
        (fun (k : ℤ) (x : ℝ) =>
          Real.sign (x + k) ^ p / |x + k| ^ (s.val + (p : ℝ)))
        (fun x : ℝ =>
          ∑' k : ℤ, Real.sign (x + k) ^ p / |x + k| ^ (s.val + (p : ℝ)))
        {x : ℝ | (x : UnitAddCircle) ≠ 0} ∧
      TendstoLocallyUniformlyOn
        (fun (M : ℕ) (x : ℝ) => iteratedDeriv p (fun y : ℝ =>
          (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |(k : ℝ) + y| ^ (-s.val)) -
            2 * (M : ℝ) ^ (1 - s.val) / (1 - s.val)) x)
        (iteratedDeriv p (fun x : ℝ => Riesz1.rieszRepresentative s x)) atTop
        {x : ℝ | (x : UnitAddCircle) ≠ 0}) ∧
    (∀ x : ℝ, (x : UnitAddCircle) ≠ 0 →
      0 < iteratedDeriv 2 (fun y : ℝ => Riesz1.rieszRepresentative s y) x) ∧
    StrictConvexOn ℝ (Ioo (0 : ℝ) 1) (fun x : ℝ => Riesz1.rieszRepresentative s x) := by
  refine ⟨?_, ?_, fun _ hx => iteratedDeriv_two_rieszRepresentative_pos s hx,
    strictConvexOn_rieszRepresentative s⟩
  · intro x hx0 hx1
    have hlimit := fundamentalSolution_heat_finitePart s hx0 hx1
    exact ⟨Riesz1.rieszRepresentative_eq_hurwitzZetaPos s hx0 hx1, hlimit⟩
  · intro p hp
    refine ⟨fun _ hx => iteratedDeriv_rieszRepresentative s hp hx,
      fun _ hx => summable_norm_kernel_images s hp hx,
      hasSumLocallyUniformlyOn_kernel_images s hp, ?_⟩
    exact Riesz1.tendstoLocallyUniformlyOn_partialSum_iteratedDeriv s.val s.2.1 s.2.2 hp

end Riesz2

end
