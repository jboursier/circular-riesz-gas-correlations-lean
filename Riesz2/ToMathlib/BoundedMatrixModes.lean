/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.SchurRestriction
public import Riesz2.ToMathlib.CoerciveSolutionMaps

/-!
# Scalar modes of bounded matrix weak equations

Finite scalar combinations of components are legitimate tests on the literal
matrix-energy domain. Bounded measurable coefficients act on L², with
their pointwise bounds retained in the norm estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped BigOperators

namespace Riesz2.BoundedMatrixModes

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι] {ν : Measure α}

/-- Multiplication by a bounded measurable real function, including its L²
representative and the exact multiplier norm bound. -/
theorem exists_multiplier (d : α → ℝ) (hd : Measurable d) (B : ℝ)
    (_hB : 0 ≤ B) (hb : ∀ᵐ x ∂ν, |d x| ≤ B) (f : Lp ℝ 2 ν) :
    ∃ g : Lp ℝ 2 ν, (∀ᵐ x ∂ν, g x = d x * f x) ∧ ‖g‖ ≤ B * ‖f‖ := by
  have hpt : ∀ᵐ x ∂ν, ‖d x * f x‖ ≤ B * ‖f x‖ := by
    filter_upwards [hb] with x hx
    simpa only [norm_mul, Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_right hx (abs_nonneg (f x))
  have hm : MemLp (fun x => d x * f x) 2 ν :=
    (Lp.memLp f).of_le_mul (hd.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)) hpt
  refine ⟨hm.toLp _, hm.coeFn_toLp, ?_⟩
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hm.coeFn_toLp, hpt] with x hx hle
  rwa [hx]

/-- A finite linear combination of L² representatives agrees almost everywhere
with the corresponding finite combination of their values. -/
theorem coe_sum_smul (c : ι → ℝ) (u : ι → Lp ℝ 2 ν) :
    ∀ᵐ x ∂ν, (∑ i, c i • u i) x = ∑ i, c i * u i x := by
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => c i • u i),
    ae_all_iff.mpr (fun i => Lp.coeFn_smul (c i) (u i))] with x hs hc
  rw [hs]
  exact Finset.sum_congr rfl (fun i _ => hc i)

/-- Rank-one tests with a zero-sum coefficient vector belong to the domain of any bounded measurable matrix field. -/
theorem rank_one_domain (Q : ScalarFormData ν) (M : α → Matrix ι ι ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hMb : ∃ B : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ B)
    (c : ι → ℝ) (hc : ∑ i, c i = 0) (w : Q.1) :
    WeightedFormDomain Q M (zeroSumComponents ι) (fun i => c i • w) := by
  apply (BoundedMatrixForms.domain_iff Q M hMm hMb _ _).mpr
  filter_upwards [ae_all_iff.mpr (fun i => Lp.coeFn_smul (c i) w.val)] with x hx
  change (∑ i, (c i • w).val x) = 0
  simp only [Submodule.coe_smul, hx, Pi.smul_apply, smul_eq_mul, ← Finset.sum_mul, hc, zero_mul]

/-- Scalar mode identity for a constrained weak equation. The coefficient
vector is a right eigenvector of the constant reference matrix. The error
source is constructed in L². It is not an additional analytic hypothesis. -/
theorem weak_mode (Q : ScalarFormData ν) (M : α → Matrix ι ι ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hMb : ∃ B : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ B)
    (H : Matrix ι ι ℝ) (c : ι → ℝ) (hc : ∑ i, c i = 0)
    (b : ℝ) (heig : ∀ i, ∑ j, H i j * c j = b * c i)
    (B : ℝ) (hB : 0 ≤ B)
    (herror : ∀ᵐ x ∂ν, ∀ i, |∑ j, (M x i j - H i j) * c j| ≤ B)
    (f : ι → Lp ℝ 2 ν) (u : ι → Q.1)
    (hu : WeightedWeakSolution Q M (zeroSumComponents ι) f u) :
    ∃ g : Lp ℝ 2 ν,
      (∀ᵐ x ∂ν, g x = ∑ i, ∑ j, (u i).val x * (M x i j - H i j) * c j) ∧
      ‖g‖ ≤ B * ∑ i, ‖(u i).val‖ ∧
      ∀ w : Q.1,
        Q.2 (∑ i, c i • u i) w + b * inner ℝ (∑ i, c i • (u i).val) w.val =
          inner ℝ ((∑ i, c i • f i) - g) w.val := by
  classical
  let d : ι → α → ℝ := fun i x => ∑ j, (M x i j - H i j) * c j
  have hd (i) : Measurable (d i) :=
    Finset.measurable_sum _ (fun j _ => ((hMm i j).sub measurable_const).mul_const _)
  have hex (i) := exists_multiplier (d i) (hd i) B hB
    (herror.mono (fun x hx => hx i)) (u i).val
  choose g hg hgn using hex
  have hgv : ∀ᵐ x ∂ν, (∑ i, g i) x = ∑ i, ∑ j,
      (u i).val x * (M x i j - H i j) * c j := by
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ g, ae_all_iff.mpr hg] with x hs hx
    rw [hs]
    apply Finset.sum_congr rfl
    intro i _
    rw [hx i]
    dsimp only [d]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  refine ⟨∑ i, g i, hgv, ?_, ?_⟩
  · calc
      _ ≤ ∑ i, ‖g i‖ := norm_sum_le _ _
      _ ≤ ∑ i, B * ‖(u i).val‖ := Finset.sum_le_sum (fun i _ => hgn i)
      _ = _ := (Finset.mul_sum _ _ _).symm
  intro w
  have ht := hu.2 (fun i => c i • w) (rank_one_domain Q M hMm hMb c hc w)
  have hq : (∑ i, Q.2 (u i) (c i • w)) = Q.2 (∑ i, c i • u i) w := by
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  have hf : (∑ i, inner ℝ (f i) (c i • w).val) =
      inner ℝ (∑ i, c i • f i) w.val := by
    simp only [Submodule.coe_smul, inner_smul_right, sum_inner, inner_smul_left,
      conj_trivial]
  have hvalues := coe_sum_smul c (fun i => (u i).val)
  have hp : matrixFieldPair M (fun i => (u i).val) (fun i => (c i • w).val) =ᵐ[ν]
      (fun x => b * ((∑ i, c i • (u i).val) x * w.val x) + (∑ i, g i) x * w.val x) := by
    filter_upwards [hgv, hvalues,
      ae_all_iff.mpr (fun i => Lp.coeFn_smul (c i) w.val)] with x hgx hux hwx
    rw [hgx, hux]
    simp only [matrixFieldPair, Submodule.coe_smul, hwx, Pi.smul_apply, smul_eq_mul]
    have he (i) : ∑ j, (u i).val x * M x i j * (c j * w.val x) =
        b * (c i * (u i).val x) * w.val x +
          (∑ j, (u i).val x * (M x i j - H i j) * c j) * w.val x := by
      have hsum : ∑ j, (M x i j - H i j) * c j =
          (∑ j, M x i j * c j) - b * c i := by
        simp_rw [sub_mul, Finset.sum_sub_distrib, heig i]
      calc
        _ = (u i).val x * (∑ j, M x i j * c j) * w.val x := by
          simp only [Finset.mul_sum, Finset.sum_mul]; apply Finset.sum_congr rfl
          intro j _; ring
        _ = b * (c i * (u i).val x) * w.val x +
            ((u i).val x * ∑ j, (M x i j - H i j) * c j) * w.val x := by
          rw [hsum]; ring
        _ = _ := by
          congr 2
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _; ring
    simp_rw [he]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
    ring
  have hi := integral_congr_ae hp
  rw [integral_add, integral_const_mul] at hi
  · have hinner (v : Lp ℝ 2 ν) : (∫ x, v x * w.val x ∂ν) = inner ℝ v w.val := by
      rw [L2.inner_def]
      simp only [Real.inner_apply]
    rw [hinner, hinner] at hi
    rw [hq, hf, hi] at ht
    rw [inner_sub_left]
    linarith [ht.2]
  · exact ((Lp.memLp _).integrable_mul (Lp.memLp w.val)).const_mul b
  · exact (Lp.memLp _).integrable_mul (Lp.memLp w.val)

end Riesz2.BoundedMatrixModes
