/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.FiniteLinearPotential
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Higher derivatives of finite linear potentials

Operator norm estimates for affine pullbacks and finite sums of scalar
potentials. These estimates supply the tensor step in Appendix A.
-/

public section
open Set
open scoped ContDiff

namespace Riesz2

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- An affine pullback multiplies the order-`n` tensor norm by at most
the `n`th power of its linear part's operator norm. -/
theorem norm_iteratedFDeriv_comp_affine_le {Q : Set F} (hQ : IsOpen Q)
    {f : F → G} {n : ℕ} (hf : ContDiffOn ℝ n f Q)
    (a : E →ᴬ[ℝ] F) {x : E} (hx : a x ∈ Q) :
    ‖iteratedFDeriv ℝ n (f ∘ a) x‖ ≤
      ‖iteratedFDeriv ℝ n f (a x)‖ * ‖a.contLinear‖ ^ n := by
  have hp := (hf.ftaylorSeriesWithin hQ.uniqueDiffOn).comp_continuousAffineMap a
  have he := hp.eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl
    (hQ.preimage a.continuous).uniqueDiffOn hx
  change (iteratedFDerivWithin ℝ n f Q (a x)).compContinuousLinearMap
    (fun _ => a.contLinear) = _ at he
  rw [iteratedFDerivWithin_of_isOpen n (hQ.preimage a.continuous) hx,
    iteratedFDerivWithin_of_isOpen n hQ hx] at he
  rw [← he]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (iteratedFDeriv ℝ n f (a x)).norm_compContinuousLinearMap_le
      (fun _ : Fin n => a.contLinear)

/-- A finite linear potential's tensor norm is controlled directly by its
scalar derivatives, without losses from a general composition bound. -/
theorem norm_iteratedFDeriv_finite_linear_potential_le {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (K : ι → ℝ → ℝ) (l : ι → E →L[ℝ] ℝ)
    (V : ι → Set ℝ) (hV : ∀ i, IsOpen (V i)) {n : ℕ}
    (hK : ∀ i, ContDiffOn ℝ n (K i) (V i)) {x : E}
    (hx : ∀ i, l i x ∈ V i) :
    ‖iteratedFDeriv ℝ n (fun z => ∑ i, c i * K i (l i z)) x‖ ≤
      ∑ i, |c i| * |iteratedDeriv n (K i) (l i x)| * ‖l i‖ ^ n := by
  classical
  have hc (i : ι) : ContDiffAt ℝ n (fun z => K i (l i z)) x :=
    ((hK i).contDiffAt ((hV i).mem_nhds (hx i))).comp x (l i).contDiff.contDiffAt
  rw [iteratedFDeriv_fun_sum_apply (fun i _ => contDiffAt_const.mul (hc i))]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  change ‖iteratedFDeriv ℝ n (c i • (fun z => K i (l i z))) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply (hc i), norm_smul, Real.norm_eq_abs]
  have h := norm_iteratedFDeriv_comp_affine_le (hV i) (hK i)
    (l i).toContinuousAffineMap (hx i)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at h
  change ‖iteratedFDeriv ℝ n (fun z => K i (l i z)) x‖ ≤
    |iteratedDeriv n (K i) (l i x)| * ‖l i‖ ^ n at h
  exact (mul_le_mul_of_nonneg_left h (abs_nonneg _)).trans_eq (mul_assoc _ _ _).symm

end Riesz2
