/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Tactic

/-!
# Derivatives of a finite sum of scalar potentials of linear forms

The domain restrictions belong to the scalar potentials. All derivatives are
evaluated at points where every argument lies in its specified open domain.
-/

public section

open Filter Set
open scoped Topology BigOperators

namespace Riesz2

/-- First and bilinear second derivatives of a finite linear potential.
This general calculus lemma does not assert any physical-domain or curvature hypotheses. -/
theorem finite_linear_potential_derivatives {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    (c : ι → ℝ) (K : ι → ℝ → ℝ) (l : ι → E →L[ℝ] ℝ)
    (V : ι → Set ℝ) (hV : ∀ i, IsOpen (V i))
    (hK : ∀ i, ContDiffOn ℝ 2 (K i) (V i))
    (x : E) (hx : ∀ i, l i x ∈ V i) (u v : E) :
    fderiv ℝ (fun z => ∑ i, c i * K i (l i z)) x u =
      ∑ i, c i * deriv (K i) (l i x) * l i u ∧
    fderiv ℝ (fderiv ℝ (fun z => ∑ i, c i * K i (l i z))) x u v =
      ∑ i, c i * deriv (deriv (K i)) (l i x) * (l i u * l i v) := by
  classical
  let J : E → E →L[ℝ] ℝ := fun z => ∑ i, (c i * deriv (K i) (l i z)) • l i
  have hd (z : E) (hz : ∀ i, l i z ∈ V i) :
      HasFDerivAt (fun z => ∑ i, c i * K i (l i z)) (J z) z := by
    apply HasFDerivAt.fun_sum
    intro i _
    have hdi := (((hK i).differentiableOn (by norm_num)).differentiableAt
      ((hV i).mem_nhds (hz i))).hasDerivAt
    convert (hdi.comp_hasFDerivAt z (l i).hasFDerivAt).const_mul (c i) using 1 <;>
      simp only [Function.comp_def, smul_smul]
  have hJ : HasFDerivAt J
      (∑ i, ((c i * deriv (deriv (K i)) (l i x)) • l i).smulRight (l i)) x := by
    apply HasFDerivAt.fun_sum
    intro i _
    have hKi : ContDiffOn ℝ 1 (deriv (K i)) (V i) :=
      (hK i).deriv_of_isOpen (hV i) (by norm_num)
    have hdi := ((hKi.differentiableOn (by norm_num)).differentiableAt
      ((hV i).mem_nhds (hx i))).hasDerivAt
    have h := (hdi.comp_hasFDerivAt x (l i).hasFDerivAt).const_mul (c i)
    convert h.smul_const (l i) using 1 <;>
      simp only [Function.comp_def, smul_smul]
  have hnear : ∀ᶠ z in 𝓝 x, ∀ i, l i z ∈ V i :=
    eventually_all.mpr (fun i => (l i).continuous.continuousAt
      ((hV i).mem_nhds (hx i)))
  have he : fderiv ℝ (fun z => ∑ i, c i * K i (l i z)) =ᶠ[𝓝 x] J :=
    hnear.mono (fun z hz => (hd z hz).fderiv)
  constructor
  · rw [(hd x hx).fderiv]
    simp only [J, sum_apply, smul_apply,
      smul_eq_mul]
  · rw [he.fderiv_eq, hJ.fderiv]
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply,
      smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring

end Riesz2
