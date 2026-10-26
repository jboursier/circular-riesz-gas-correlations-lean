/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.PhysicalEnergy
public import Riesz2.ToMathlib.AffineSimplexCharts
public import Riesz2.ToMathlib.AffineMetricTransport
public import Riesz2.Frozen.ProperMarginalDomain
public import Mathlib.Probability.Moments.Variance

/-!
# Components of proper marginal Hessian calculus

Steps in Appendix A: covariance positivity, identification of the proper
domain, and all-order unpenalized physical energy calculus when just one
exterior coordinate is omitted. In this case the marginal potential is an
affine pullback of the ambient energy.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz2.MarginalHessian

/-- Covariance positivity in Appendix A: the covariance matrix of any finite
family of square-integrable real forces is nonnegative. -/
theorem covariance_quadratic_nonneg {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    {μ : Measure A} [IsFiniteMeasure μ] {X : ι → A → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ) (b : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, b i * ProbabilityTheory.covariance (X i) (X j) μ * b j := by
  have hn : 0 ≤ ProbabilityTheory.covariance
      (fun y => ∑ i, b i * X i y) (fun y => ∑ i, b i * X i y) μ :=
    integral_nonneg fun y => mul_self_nonneg _
  rw [ProbabilityTheory.covariance_fun_sum_fun_sum
    (fun i => (hX i).const_mul (b i)) (fun i => (hX i).const_mul (b i))] at hn
  simp only [ProbabilityTheory.covariance_const_mul_left,
    ProbabilityTheory.covariance_const_mul_right] at hn
  simpa only [mul_comm, mul_left_comm, mul_assoc] using hn

/-- See Appendix A of the paper: the existing affine simplex chart domain is
literally the proper marginal domain at positive integer mass. -/
theorem properMarginalDomain_eq_chartDomain (n N : ℕ+) :
    properMarginalDomain n N = AffineSimplex.chartDomain n N := rfl

/-- The proper interior is mapped to the ambient energy
domain when the single omitted coordinate is recovered from total mass. -/
theorem singleExterior_chart_mem (n : ℕ+) {x : EuclideanSpace ℝ (Fin (n : ℕ))}
    (hx : x ∈ properMarginalDomain n ⟨n + 1, by omega⟩) :
    AffineSimplex.chart n (n + 1) x ∈ gapAmbientDomain ⟨n + 1, by omega⟩ := by
  have hc : AffineSimplex.chart n (n + 1) x ∈ AffineSimplex.massSimplex n (n + 1) :=
    (AffineSimplex.chart_mem_simplex_iff n (n + 1) x).mpr (by
      simpa only [properMarginalDomain, AffineSimplex.chartDomain,
        PNat.mk_coe, Nat.cast_add, Nat.cast_one] using hx)
  exact PhysicalEnergy.simplex_subset_ambient _ _
    ⟨hc.1, by
      change ∑ i, AffineSimplex.chart n (n + 1) x i = (((n : ℕ) + 1 : ℕ) : ℝ)
      simpa only [Nat.cast_add, Nat.cast_one] using hc.2⟩

/-- See Appendix A of the paper, one exterior gap: the derivative direction is
exactly `eᵢ - e_last`, so the exterior compensation has coefficient one. -/
theorem compensated_basis_last (n : ℕ) (i : Fin n) :
    AffineSimplex.tangentMap n (EuclideanSpace.single i 1) =
      EuclideanSpace.single i.castSucc 1 - EuclideanSpace.single (Fin.last n) 1 := by
  ext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [AffineSimplex.tangentMap, AffineSimplex.chart_last]
  · simp [AffineSimplex.tangentMap, AffineSimplex.chart_castSucc]

/-- A boundary case of Appendix A: with one exterior
gap and zero active penalty, the temperature-weighted physical energy
pullback is smooth and has the compensated first and second derivatives.
This states an existence result for a smooth realization of the energy. -/
theorem singleExterior_physical_smooth (p : Parameters) (n : ℕ+) :
    ∃ U : EuclideanSpace ℝ (Fin ((n : ℕ) + 1)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain ⟨n + 1, by omega⟩) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ) + 1)) //
          y ∈ gapAmbientDomain ⟨n + 1, by omega⟩},
        U y.val = p.val.1 * physicalAmbientGapEnergy p ⟨n + 1, by omega⟩ y) ∧
      ContDiffOn ℝ ∞ (fun x => U (AffineSimplex.chart n (n + 1) x))
        (properMarginalDomain n ⟨n + 1, by omega⟩) ∧
      ∀ x ∈ properMarginalDomain n ⟨n + 1, by omega⟩,
        ∀ u v : EuclideanSpace ℝ (Fin (n : ℕ)),
          fderiv ℝ (fun z => U (AffineSimplex.chart n (n + 1) z)) x u =
            fderiv ℝ U (AffineSimplex.chart n (n + 1) x) (AffineSimplex.tangentMap n u) ∧
          fderiv ℝ (fderiv ℝ (fun z => U (AffineSimplex.chart n (n + 1) z))) x u v =
            fderiv ℝ (fderiv ℝ U) (AffineSimplex.chart n (n + 1) x)
              (AffineSimplex.tangentMap n u) (AffineSimplex.tangentMap n v) := by
  obtain ⟨W, hs, hv, _⟩ := PhysicalEnergy.ambient_derivatives p ⟨n + 1, by omega⟩
  let U := fun y => p.val.1 * W y
  have hU : ContDiffOn ℝ ∞ U (gapAmbientDomain ⟨n + 1, by omega⟩) := contDiffOn_const.mul hs
  have hc : ContDiff ℝ ∞ (AffineSimplex.chart n (n + 1)) := by
    have he : AffineSimplex.chart n (n + 1) = fun x =>
        (AffineSimplex.tangentMap n).toContinuousLinearMap x +
          AffineSimplex.chart n (n + 1) 0 := by
      funext x
      exact AffineSimplex.chart_eq_tangentMap_add _ _ _
    rw [he]
    exact (AffineSimplex.tangentMap n).toContinuousLinearMap.contDiff.add contDiff_const
  refine ⟨U, hU, fun y => congrArg (fun r : ℝ => p.val.1 * r) (hv y),
    hU.comp hc.contDiffOn (fun x hx => singleExterior_chart_mem n hx), ?_⟩
  intro x hx u v
  have hUa : ContDiffAt ℝ ∞ U (AffineSimplex.chart n (n + 1) x) :=
    hU.contDiffAt (PhysicalEnergy.isOpen_gapAmbientDomain _ |>.mem_nhds
      (singleExterior_chart_mem n hx))
  constructor
  · exact congrArg (fun T => T u)
      (AffineSimplex.hasFDerivAt_comp_chart n (n + 1)
        (hUa.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  · have h2 : ContDiffAt ℝ 2 U (AffineSimplex.chart n (n + 1) x) :=
      hUa.of_le (by norm_num)
    have h2' : ContDiffAt ℝ 2 U
        ((AffineSimplex.tangentMap n).toContinuousLinearMap x +
          AffineSimplex.chart n (n + 1) 0) := by
      change ContDiffAt ℝ 2 U
        (AffineSimplex.tangentMap n x + AffineSimplex.chart n (n + 1) 0)
      rw [← AffineSimplex.chart_eq_tangentMap_add]
      exact h2
    have he := AffineMetricTransport.hessian_comp_affine
      (AffineSimplex.tangentMap n).toContinuousLinearMap (AffineSimplex.chart n (n + 1) 0)
      h2' u v
    change fderiv ℝ (fderiv ℝ (fun z => U (AffineSimplex.tangentMap n z +
      AffineSimplex.chart n (n + 1) 0))) x u v =
        fderiv ℝ (fderiv ℝ U) (AffineSimplex.tangentMap n x +
          AffineSimplex.chart n (n + 1) 0)
            (AffineSimplex.tangentMap n u) (AffineSimplex.tangentMap n v) at he
    simp only [← AffineSimplex.chart_eq_tangentMap_add] at he
    exact he

end Riesz2.MarginalHessian
