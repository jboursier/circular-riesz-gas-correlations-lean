/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.OptimalDecay
public import Riesz2.ToMathlib.ConstrainedNormalMultiplier
public import Riesz2.HelfferSjostrand.GapRepresentationPart3

/-!
# Short-range normal multiplier

See Lemma 4.6 of the paper: constrained existence, square integrability
of the multiplier, its sharp inverse-size bound, and component decay
with the constant mode retained. The proof compares the constrained
solution with the orthogonal projection of the unrestricted solution.
Coercivity bounds the component ℓ¹ norm of their defect without a
dimension loss. All projections act on the scalar form carrier.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set InnerProductSpace
open scoped BigOperators ENNReal NNReal

namespace Riesz2.MultiplierControl

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}

/-- Internal normal estimate for Lemma 4.6. Bounded
absolute column sums give an L² representative of the multiplier.
The sum of component norms is retained explicitly in this intermediate bound. -/
theorem normal_l2 (m : ℕ+) (Q : ScalarFormData ν)
    (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j)) (B : ℝ) (hB : 0 ≤ B)
    (hcol : ∀ᵐ x ∂ν, ∀ j, ∑ i, |M x i j| ≤ B)
    (f : Fin (m : ℕ) → Lp ℝ 2 ν) (u : Fin (m : ℕ) → Q.1) :
    ∃ l : Lp ℝ 2 ν,
      (∀ᵐ x ∂ν, l x = gapMultiplierField m Q M f u x) ∧
      ‖l‖ ≤ (m : ℝ)⁻¹ * (B * ∑ j, ‖(u j).val‖ + ‖∑ i, f i‖) := by
  let d := fun j x => ∑ i, M x i j
  have hd (j : Fin (m : ℕ)) : Measurable (d j) :=
    Finset.measurable_sum _ (fun i _ => hMm i j)
  have hb (j : Fin (m : ℕ)) : ∀ᵐ x ∂ν, |d j x| ≤ B :=
    hcol.mono (fun x hx => (Finset.abs_sum_le_sum_abs _ _).trans (hx j))
  obtain ⟨v, hv, hn⟩ : ∃ v : Fin (m : ℕ) → Lp ℝ 2 ν,
      (∀ j, ∀ᵐ x ∂ν, v j x = d j x * (u j).val x) ∧
      (∀ j, ‖v j‖ ≤ B * ‖(u j).val‖) := by
    choose v hv hn using fun j =>
      BoundedMatrixModes.exists_multiplier (d j) (hd j) B hB (hb j) (u j).val
    exact ⟨v, hv, hn⟩
  let l : Lp ℝ 2 ν := (m : ℝ)⁻¹ • ((∑ j, v j) - ∑ i, f i)
  refine ⟨l, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_smul (m : ℝ)⁻¹ ((∑ j, v j) - ∑ i, f i),
      Lp.coeFn_sub (∑ j, v j) (∑ i, f i),
      Lp.coeFn_fun_finsetSum Finset.univ v,
      Lp.coeFn_fun_finsetSum Finset.univ f, ae_all_iff.mpr hv] with x hl hs hvx hfx hx
    dsimp only [l]
    rw [hl, Pi.smul_apply, smul_eq_mul, hs, Pi.sub_apply, hvx, hfx]
    simp only [gapMultiplierField, hx, d, Finset.sum_mul]
    rw [Finset.sum_comm]
  · calc
      ‖l‖ = (m : ℝ)⁻¹ * ‖(∑ j, v j) - ∑ i, f i‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (m : ℝ)⁻¹)]
      _ ≤ (m : ℝ)⁻¹ * ((∑ j, ‖v j‖) + ‖∑ i, f i‖) := by
        gcongr
        exact (norm_sub_le _ _).trans (add_le_add (norm_sum_le _ _) le_rfl)
      _ ≤ _ := by
        gcongr
        calc
          ∑ j, ‖v j‖ ≤ ∑ j, B * ‖(u j).val‖ := Finset.sum_le_sum fun j _ => hn j
          _ = _ := (Finset.mul_sum _ _ _).symm

/-- Internal bounded-coefficient bridge for Lemma 4.6: the tangent
weak equation extends to all Sobolev tests with the normal multiplier.
Every matrix and multiplier integral is integrable. -/
theorem ambient_equation (m : ℕ+) (Q : ScalarFormData ν)
    (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hMb : ∃ B : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ B)
    (hMs : ∀ᵐ x ∂ν, ∀ i j, M x i j = M x j i)
    (f : Fin (m : ℕ) → Lp ℝ 2 ν) (u : Fin (m : ℕ) → Q.1)
    (hu : WeightedWeakSolution Q M (zeroSumComponents _) f u)
    (l : Lp ℝ 2 ν) (hl : ∀ᵐ x ∂ν, l x = gapMultiplierField m Q M f u x)
    (k : Fin (m : ℕ) → Q.1) :
    (∑ i, Q.2 (u i) (k i)) +
      (∫ x, matrixFieldPair M (fun i => (u i).val) (fun i => (k i).val) x ∂ν) =
        ∑ i, inner ℝ (f i + l) (k i).val := by
  let p := ConstrainedNormalMultiplier.projectTuple m Q k
  have hp : WeightedFormDomain Q M (zeroSumComponents _) p :=
    (BoundedMatrixForms.domain_iff Q M hMm hMb _ p).mpr
      (ConstrainedNormalMultiplier.projectTuple_zeroSum m Q k)
  have heq := (hu.2 p hp).2
  have hki := BoundedMatrixForms.integrable_pair M hMm hMb
    (fun i => (u i).val) (fun i => (k i).val)
  have hpi := BoundedMatrixForms.integrable_pair M hMm hMb
    (fun i => (u i).val) (fun i => (p i).val)
  have hvk := ConstrainedNormalMultiplier.source_pair_integral m f (fun i => (k i).val)
  have hvp := ConstrainedNormalMultiplier.source_pair_integral m f (fun i => (p i).val)
  have hlk := ConstrainedNormalMultiplier.source_pair_integral m
    (fun _ => l) (fun i => (k i).val)
  have hn : (fun x => matrixFieldPair M (fun i => (u i).val) (fun i => (k i).val) x -
      ∑ i, f i x * (k i).val x) =ᵐ[ν]
      (fun x => (matrixFieldPair M (fun i => (u i).val) (fun i => (p i).val) x -
        ∑ i, f i x * (p i).val x) + ∑ i, l x * (k i).val x) := by
    filter_upwards [hMs, hl, ConstrainedNormalMultiplier.projectTuple_ae m Q k] with x hs hlx hpx
    have hid := ConstrainedNormalMultiplier.normal_projection_identity m (M x) hs
      (fun i => (u i).val x) (fun i => f i x) (fun i => (k i).val x)
    simpa only [matrixFieldPair, hlx, gapMultiplierField, p, hpx, Finset.mul_sum] using hid
  have hsub : Integrable (fun x => matrixFieldPair M (fun i => (u i).val)
      (fun i => (p i).val) x - ∑ i, f i x * (p i).val x) ν := hpi.sub hvp.1
  have he := integral_congr_ae hn
  rw [integral_sub hki hvk.1, integral_add hsub hlk.1,
    integral_sub hpi hvp.1, ← hvk.2, ← hvp.2, ← hlk.2] at he
  rw [ConstrainedNormalMultiplier.diffusion_projectTuple m Q u k hu.1.1] at heq
  simp only [inner_add_left, Finset.sum_add_distrib]
  linarith

/-- Internal bounded-coefficient identity: the matrix integral is bilinear
on the entire product of scalar form domains. -/
theorem pair_sub_left {ι : Type*} [Fintype ι]
    (M : α → Matrix ι ι ℝ) (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hMb : ∃ B : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ B)
    (u v w : ι → Lp ℝ 2 ν) :
    (∫ x, matrixFieldPair M (fun i => u i - v i) w x ∂ν) =
      (∫ x, matrixFieldPair M u w x ∂ν) - ∫ x, matrixFieldPair M v w x ∂ν := by
  have he : matrixFieldPair M (fun i => u i - v i) w =ᵐ[ν]
      fun x => matrixFieldPair M u w x - matrixFieldPair M v w x := by
    filter_upwards [ae_all_iff.mpr (fun i => Lp.coeFn_sub (u i) (v i))] with x hx
    simp only [matrixFieldPair, hx, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  rw [integral_congr_ae he]
  exact integral_sub (BoundedMatrixForms.integrable_pair M hMm hMb u w)
    (BoundedMatrixForms.integrable_pair M hMm hMb v w)

/-- An exact zero component sum gives almost-everywhere tangency on the domain. No independent representative of a vector field is introduced. -/
theorem tangent_of_sum_zero (m : ℕ+) (Q : ScalarFormData ν)
    (w : Fin (m : ℕ) → Q.1) (hw : ∑ i, w i = 0) :
    ∀ᵐ x ∂ν, (fun i => (w i).val x) ∈ zeroSumComponents (Fin (m : ℕ)) := by
  have he : (∑ i, (w i).val) = 0 := by simpa only [Submodule.coe_sum, Submodule.coe_zero] using congrArg Subtype.val hw
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => (w i).val),
    Lp.coeFn_zero ℝ 2 ν] with x hs hz
  change ∑ i, (w i).val x = 0
  simpa only [Pi.zero_apply] using (hs.symm.trans ((congrArg (fun f : Lp ℝ 2 ν => f x) he).trans hz))

/-- Pairing a constant component field against a summable kernel. This is the
normal-to-tangent estimate used in Lemma 4.6. -/
theorem constant_pair_bound (m : ℕ+) (s : ℝ) (hs : 1 < s)
    (g : ComponentGeometry (Fin (m : ℕ)))
    (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j)) (B : ℝ) (hB : 0 ≤ B)
    (hentry : ∀ᵐ x ∂ν, ∀ i j,
      |M x i j| ≤ B * (1 + componentDistance g i j) ^ (-s))
    (v : Lp ℝ 2 ν) (w : Fin (m : ℕ) → Lp ℝ 2 ν) :
    |∫ x, matrixFieldPair M (fun _ => (m : ℝ)⁻¹ • v) w x ∂ν| ≤
      (m : ℝ)⁻¹ * (B * (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s))) *
        ‖v‖ * ∑ j, ‖w j‖ := by
  have hb : ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ B := by
    filter_upwards [hentry] with x hx i j
    exact (hx i j).trans (mul_le_of_le_one_right hB
      (Real.rpow_le_one_of_one_le_of_nonpos
        (by linarith [ComponentGeometryBounds.nonneg g i j]) (by linarith)))
  have hi i j := OptimalDecay.Internal.entry_integrable (fun x => M x i j)
    (hMm i j) B (hb.mono fun x hx => hx i j) ((m : ℝ)⁻¹ • v) (w j)
  have hexp : (∫ x, matrixFieldPair M (fun _ => (m : ℝ)⁻¹ • v) w x ∂ν) =
      ∑ i, ∑ j, ∫ x, ((m : ℝ)⁻¹ • v) x * M x i j * w j x ∂ν := by
    unfold matrixFieldPair
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ (fun j _ => hi i j)
    · exact fun i _ => integrable_finsetSum _ fun j _ => hi i j
  rw [hexp]
  calc
    _ ≤ ∑ i, ∑ j, |∫ x, ((m : ℝ)⁻¹ • v) x * M x i j * w j x ∂ν| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, (B * (1 + componentDistance g i j) ^ (-s)) *
        ((m : ℝ)⁻¹ * ‖v‖) * ‖w j‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have he := OptimalDecay.Internal.entry_bound (fun x => M x i j) (hMm i j)
        (B * (1 + componentDistance g i j) ^ (-s))
        (mul_nonneg hB (Real.rpow_nonneg (by linarith [ComponentGeometryBounds.nonneg g i j]) _))
        (hentry.mono fun x hx => hx i j) ((m : ℝ)⁻¹ • v) (w j)
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (m : ℝ)⁻¹)] using he
    _ = (m : ℝ)⁻¹ * B * ‖v‖ *
        ∑ j, (∑ i, (1 + componentDistance g i j) ^ (-s)) * ‖w j‖ := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ (m : ℝ)⁻¹ * B * ‖v‖ *
        ∑ j, (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s)) * ‖w j‖ := by
      gcongr with j
      simpa only [ComponentGeometryBounds.symm g] using ComponentGeometryBounds.sum_power_le g j hs
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- Internal comparison identity for Lemma 4.6.
The defect between a constrained solution and the projection of the full
solution is forced solely by the normal part of the full solution. -/
theorem projection_defect_energy (m : ℕ+) (Q : ScalarFormData ν)
    (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hMb : ∃ B : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ B)
    (f : Fin (m : ℕ) → Lp ℝ 2 ν) (u v : Fin (m : ℕ) → Q.1)
    (hu : WeightedWeakSolution Q M (zeroSumComponents _) f u)
    (hv : WeightedWeakSolution Q M ⊤ f v) :
    let w := fun i => u i - ConstrainedNormalMultiplier.projectTuple m Q v i
    (∑ i, Q.2 (w i) (w i)) +
      (∫ x, matrixFieldPair M (fun i => (w i).val) (fun i => (w i).val) x ∂ν) =
        ∫ x, matrixFieldPair M (fun _ => ((m : ℝ)⁻¹ • ∑ i, v i).val)
          (fun i => (w i).val) x ∂ν := by
  intro w
  let a : Q.1 := (m : ℝ)⁻¹ • ∑ i, v i
  have hw : ∑ i, w i = 0 := by
    simp only [w, Finset.sum_sub_distrib,
      ConstrainedNormalMultiplier.tuple_sum_zero m Q u hu.1.1,
      ConstrainedNormalMultiplier.tuple_sum_zero m Q _
        (ConstrainedNormalMultiplier.projectTuple_zeroSum m Q v), sub_self]
  have hwu := (BoundedMatrixForms.domain_iff Q M hMm hMb _ w).mpr
    (tangent_of_sum_zero m Q w hw)
  have hwt := (BoundedMatrixForms.domain_iff Q M hMm hMb ⊤ w).mpr
    (Eventually.of_forall fun _ => Submodule.mem_top)
  have hdiff : (∑ i, Q.2 (u i) (w i)) - (∑ i, Q.2 (v i) (w i)) =
      ∑ i, Q.2 (w i) (w i) := by
    have hz : ∑ i, Q.2 a (w i) = 0 := by
      rw [← map_sum, hw, map_zero]
    have hi (i) : u i - v i = w i - a := by
      dsimp only [w, a, ConstrainedNormalMultiplier.projectTuple]
      module
    rw [← Finset.sum_sub_distrib]
    simp_rw [← LinearMap.sub_apply, ← map_sub, hi, map_sub, LinearMap.sub_apply]
    rw [Finset.sum_sub_distrib, hz, sub_zero]
  have hpair : (∫ x, matrixFieldPair M (fun i => (u i).val) (fun i => (w i).val) x ∂ν) -
      (∫ x, matrixFieldPair M (fun i => (v i).val) (fun i => (w i).val) x ∂ν) =
      (∫ x, matrixFieldPair M (fun i => (w i).val) (fun i => (w i).val) x ∂ν) -
        ∫ x, matrixFieldPair M (fun _ => a.val) (fun i => (w i).val) x ∂ν := by
    rw [← pair_sub_left M hMm hMb, ← pair_sub_left M hMm hMb]
    congr 1
    have hi (i) : (u i).val - (v i).val = (w i).val - a.val := by
      change (u i - v i).val = (w i - a).val
      congr 1
      dsimp only [w, a, ConstrainedNormalMultiplier.projectTuple]
      module
    simp only [hi]
  linarith [(hu.2 w hwu).2, (hv.2 w hwt).2]

/-- Coercivity bounds the component ℓ¹ norm of the projection defect without
any factor depending on m. Internal comparison for Lemma 4.6. -/
theorem projection_defect_l1 (m : ℕ+) (s : ℝ) (hs : 1 < s)
    (g : ComponentGeometry (Fin (m : ℕ)))
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (a B : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (hentry : ∀ᵐ x ∂ν, ∀ i j,
      |M x i j| ≤ B * (1 + componentDistance g i j) ^ (-s))
    (hlower : ∀ᵐ x ∂ν, ∀ z : Fin (m : ℕ) → ℝ,
      a * ∑ i, z i ^ 2 ≤ ∑ i, ∑ j, z i * M x i j * z j)
    (f : Fin (m : ℕ) → Lp ℝ 2 ν) (u v : Fin (m : ℕ) → Q.1)
    (hu : WeightedWeakSolution Q M (zeroSumComponents _) f u)
    (hv : WeightedWeakSolution Q M ⊤ f v) :
    let w := fun i => u i - ConstrainedNormalMultiplier.projectTuple m Q v i
    ∑ i, ‖(w i).val‖ ≤
      a⁻¹ * (B * (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s))) * ‖∑ i, (v i).val‖ := by
  intro w
  have hm : (0 : ℝ) < (m : ℝ) := by positivity
  have hb : ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ B := by
    filter_upwards [hentry] with x hx i j
    exact (hx i j).trans (mul_le_of_le_one_right hB
      (Real.rpow_le_one_of_one_le_of_nonpos
        (by linarith [ComponentGeometryBounds.nonneg g i j]) (by linarith)))
  have he := projection_defect_energy m Q M hMm ⟨B, hb⟩ f u v hu hv
  change (∑ i, Q.2 (w i) (w i)) + _ = _ at he
  have hc := constant_pair_bound m s hs g M hMm B hB hentry
    (∑ i, (v i).val) (fun i => (w i).val)
  simp only [Submodule.coe_smul, Submodule.coe_sum] at he ⊢
  have hupper : (∫ x, matrixFieldPair M (fun i => (w i).val) (fun i => (w i).val) x ∂ν) ≤
      (m : ℝ)⁻¹ * (B * (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s))) *
        ‖∑ i, (v i).val‖ * ∑ i, ‖(w i).val‖ := by
    have hn := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hQ.2.2.1 (w i))
    have ha := le_abs_self (∫ x, matrixFieldPair M
      (fun _ => (m : ℝ)⁻¹ • ∑ i, (v i).val) (fun i => (w i).val) x ∂ν)
    linarith
  have hlow : a * ∑ i, ‖(w i).val‖ ^ 2 ≤
      ∫ x, matrixFieldPair M (fun i => (w i).val) (fun i => (w i).val) x ∂ν := by
    have hi : Integrable (fun x => ∑ i, (w i).val x ^ 2) ν :=
      integrable_finsetSum _ fun i _ => (Lp.memLp (w i).val).integrable_sq
    have hl := integral_mono_ae (hi.const_mul a)
      (BoundedMatrixForms.integrable_pair M hMm ⟨B, hb⟩ (fun i => (w i).val) (fun i => (w i).val))
      (hlower.mono fun x hx => hx (fun i => (w i).val x))
    rw [integral_const_mul, InitialDecay.Internal.integral_square_sum,
      PiLp.norm_sq_eq_of_L2] at hl
    exact hl
  have hcs : (∑ i, ‖(w i).val‖) ^ 2 ≤ (m : ℝ) * ∑ i, ‖(w i).val‖ ^ 2 := by
    simpa [mul_comm] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i => ‖(w i).val‖) (fun _ : Fin (m : ℕ) => (1 : ℝ))
  have hfinal : a * (∑ i, ‖(w i).val‖) ^ 2 ≤
      (B * (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s))) *
        ‖∑ i, (v i).val‖ * ∑ i, ‖(w i).val‖ := by
    calc
      _ ≤ (m : ℝ) * (a * ∑ i, ‖(w i).val‖ ^ 2) := by nlinarith [mul_le_mul_of_nonneg_left hcs ha.le]
      _ ≤ (m : ℝ) * (∫ x, matrixFieldPair M (fun i => (w i).val) (fun i => (w i).val) x ∂ν) :=
        mul_le_mul_of_nonneg_left hlow hm.le
      _ ≤ (m : ℝ) * ((m : ℝ)⁻¹ * (B * (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s))) *
        ‖∑ i, (v i).val‖ * ∑ i, ‖(w i).val‖) := mul_le_mul_of_nonneg_left hupper hm.le
      _ = _ := by rw [← mul_assoc, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul]
  have hn : 0 ≤ ∑ i, ‖(w i).val‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  by_cases hz : (∑ i, ‖(w i).val‖) = 0
  · rw [hz]
    positivity
  have hp : 0 < ∑ i, ‖(w i).val‖ := lt_of_le_of_ne hn (Ne.symm hz)
  have hcancel : a * ∑ i, ‖(w i).val‖ ≤
      (B * (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s))) * ‖∑ i, (v i).val‖ := by
    nlinarith only [hfinal, hp]
  simpa only [mul_assoc] using (le_inv_mul_iff₀ ha).mpr hcancel

/-- Internal ℓ¹ stability of imposing the zero-sum constraint. Its constant is
independent of the number of components, as needed in Lemma 4.6. -/
theorem constrained_l1 (m : ℕ+) (s : ℝ) (hs : 1 < s)
    (g : ComponentGeometry (Fin (m : ℕ)))
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (a B : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (hentry : ∀ᵐ x ∂ν, ∀ i j,
      |M x i j| ≤ B * (1 + componentDistance g i j) ^ (-s))
    (hlower : ∀ᵐ x ∂ν, ∀ z : Fin (m : ℕ) → ℝ,
      a * ∑ i, z i ^ 2 ≤ ∑ i, ∑ j, z i * M x i j * z j)
    (f : Fin (m : ℕ) → Lp ℝ 2 ν) (u v : Fin (m : ℕ) → Q.1)
    (hu : WeightedWeakSolution Q M (zeroSumComponents _) f u)
    (hv : WeightedWeakSolution Q M ⊤ f v) :
    ∑ i, ‖(u i).val‖ ≤
      (2 + a⁻¹ * (B * (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s)))) * ∑ i, ‖(v i).val‖ := by
  let w := fun i => u i - ConstrainedNormalMultiplier.projectTuple m Q v i
  let a₀ : Q.1 := (m : ℝ)⁻¹ • ∑ i, v i
  have hw := projection_defect_l1 m s hs g Q hQ M hMm a B ha hB hentry hlower f u v hu hv
  have hvsum : ‖∑ i, (v i).val‖ ≤ ∑ i, ‖(v i).val‖ := norm_sum_le _ _
  have hmean : (∑ _i : Fin (m : ℕ), ‖a₀.val‖) = ‖∑ i, (v i).val‖ := by
    simp only [a₀, Submodule.coe_smul, Submodule.coe_sum, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (m : ℝ)⁻¹), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ (by positivity : (m : ℝ) ≠ 0), one_mul]
  have hi (i : Fin (m : ℕ)) : ‖(u i).val‖ ≤ ‖(v i).val‖ + ‖a₀.val‖ + ‖(w i).val‖ := by
    have he : (u i).val = ((v i).val - a₀.val) + (w i).val := by
      change (u i).val = (v i - a₀ + w i).val
      congr 1
      dsimp only [w, a₀, ConstrainedNormalMultiplier.projectTuple]
      module
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  have hnonneg : 0 ≤ a⁻¹ * (B * (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s))) := by positivity
  calc
    _ ≤ ∑ i, (‖(v i).val‖ + ‖a₀.val‖ + ‖(w i).val‖) := Finset.sum_le_sum fun i _ => hi i
    _ = (∑ i, ‖(v i).val‖) + ‖∑ i, (v i).val‖ + ∑ i, ‖(w i).val‖ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hmean]
    _ ≤ (∑ i, ‖(v i).val‖) + (∑ i, ‖(v i).val‖) +
        a⁻¹ * (B * (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s))) * ∑ i, ‖(v i).val‖ :=
      add_le_add (add_le_add le_rfl hvsum) (hw.trans (mul_le_mul_of_nonneg_left hvsum hnonneg))
    _ = _ := by ring

/-- Internal reciprocity identity for Lemma 4.6. All test vectors
lie in the full Sobolev domain, and the normal forcing is the L² representative
of the multiplier. -/
theorem point_source_duality (m : ℕ+) (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q)
    (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hMb : ∃ B : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ B)
    (hMs : ∀ᵐ x ∂ν, ∀ i j, M x i j = M x j i)
    (i₀ j : Fin (m : ℕ)) (χ η : Lp ℝ 2 ν)
    (u v : Fin (m : ℕ) → Q.1)
    (hu : WeightedWeakSolution Q M (zeroSumComponents _)
      (fun i => if i = i₀ then χ else 0) u)
    (hv : WeightedWeakSolution Q M ⊤ (fun i => if i = j then η else 0) v)
    (l : Lp ℝ 2 ν) (hl : ∀ᵐ x ∂ν,
      l x = gapMultiplierField m Q M (fun i => if i = i₀ then χ else 0) u x) :
    inner ℝ η (u j).val = inner ℝ χ (v i₀).val + inner ℝ l (∑ i, (v i).val) := by
  have he := ambient_equation m Q M hMm hMb hMs _ u hu l hl v
  have ht := (BoundedMatrixForms.domain_iff Q M hMm hMb ⊤ u).mpr
    (Eventually.of_forall fun _ => Submodule.mem_top)
  have hvu := (hv.2 u ht).2
  have hs : (∫ x, matrixFieldPair M (fun i => (u i).val) (fun i => (v i).val) x ∂ν) =
      ∫ x, matrixFieldPair M (fun i => (v i).val) (fun i => (u i).val) x ∂ν := by
    apply integral_congr_ae
    filter_upwards [hMs] with x hx
    unfold matrixFieldPair
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    rw [hx k i]
    ring
  have hdiff : (∑ i, Q.2 (u i) (v i)) = ∑ i, Q.2 (v i) (u i) :=
    Finset.sum_congr rfl fun i _ => hQ.2.1 _ _
  have hsource (k : Fin (m : ℕ)) (ζ : Lp ℝ 2 ν) (z : Fin (m : ℕ) → Q.1) :
      (∑ i, inner ℝ (if i = k then ζ else 0) (z i).val) = inner ℝ ζ (z k).val := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  simp only [inner_add_left, Finset.sum_add_distrib, hsource] at he hvu
  rw [← inner_sum] at he
  linarith

/-- Unique constrained existence on the full form domain, the existence
clause of Lemma 4.6. -/
theorem constrained_exists_unique (m : ℕ+) (β : ℝ) (hβ : 0 < β)
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (a : ℝ) (ha : 0 < a)
    (hM : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
      ∀ z : Fin (m : ℕ) → ℝ,
        a * ∑ i, z i ^ 2 ≤ ∑ i, ∑ j, z i * M x i j * z j)
    (f : Fin (m : ℕ) → Lp ℝ 2 ν) :
    ∃! u : Fin (m : ℕ) → Q.1,
      WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _) f u := by
  exact MatrixEnergy.weightedWeakSolution_existsUnique Q hQ (fun x => β • M x)
    (zeroSumComponents _) (AbstractEnergy.scaled_posSemidef β a hβ.le ha.le M hM)
    (β * a) (mul_pos hβ ha)
    (AbstractEnergy.scaled_lower β a hβ.le M (hM.mono fun x hx => hx.2) _)
    (AbstractEnergy.scaled_measurable β M hMm) f

namespace Internal

/-- Summing a point-source profile costs only the summable kernel constant. -/
theorem sum_point_profile (m : ℕ+) (s : ℝ) (hs : 1 < s)
    (g : ComponentGeometry (Fin (m : ℕ))) (i₀ : Fin (m : ℕ))
    (u : Fin (m : ℕ) → Lp ℝ 2 ν) (D F : ℝ) (hD : 0 ≤ D) (hF : 0 ≤ F)
    (hu : ∀ j, ‖u j‖ ≤ D * (1 + componentDistance g j i₀) ^ (-s) * F) :
    ∑ j, ‖u j‖ ≤ D * (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s)) * F := by
  calc
    _ ≤ ∑ j, D * (1 + componentDistance g j i₀) ^ (-s) * F :=
      Finset.sum_le_sum fun j _ => hu j
    _ = D * (∑ j, (1 + componentDistance g j i₀) ^ (-s)) * F := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ _ := by
      gcongr
      simpa only [ComponentGeometryBounds.symm g] using ComponentGeometryBounds.sum_power_le g i₀ hs

/-- Reduction of the multiplier estimate to the optimal point-source theorem. -/
theorem estimate_of_point_source_bounds (m : ℕ+) (s β : ℝ) (hs : 1 < s) (hβ : 0 < β)
    (g : ComponentGeometry (Fin (m : ℕ)))
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j)) (B : ℝ) (hB : 1 ≤ B)
    (hM : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
      (∀ z : Fin (m : ℕ) → ℝ,
        B⁻¹ * ∑ i, z i ^ 2 ≤ ∑ i, ∑ j, z i * M x i j * z j) ∧
      (∀ i j, |M x i j| ≤ B * (1 + componentDistance g i j) ^ (-s)))
    (D : ℝ) (hD : 0 ≤ D)
    (hdec : ∀ (i₀ : Fin (m : ℕ)) (χ : Lp ℝ 2 ν),
      ∃ v : Fin (m : ℕ) → Q.1,
        WeightedWeakSolution Q (fun x => β • M x) ⊤ (fun i => if i = i₀ then χ else 0) v ∧
        ∀ j, ‖(v j).val‖ ≤ D * (1 + componentDistance g j i₀) ^ (-s) * ‖χ‖)
    (i₀ : Fin (m : ℕ)) (χ : Lp ℝ 2 ν) (u : Fin (m : ℕ) → Q.1)
    (hu : WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _)
      (fun i => if i = i₀ then χ else 0) u) :
    let K := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s)
    ∃ l : Lp ℝ 2 ν,
      (∀ᵐ x ∂ν, l x = gapMultiplierField m Q (fun x => β • M x)
        (fun i => if i = i₀ then χ else 0) u x) ∧
      ‖l‖ ≤ (m : ℝ)⁻¹ * (β * B * K * ((2 + B ^ 2 * K) * D * K) + 1) * ‖χ‖ ∧
      ∀ j, ‖(u j).val‖ ≤ D * (1 + componentDistance g j i₀) ^ (-s) * ‖χ‖ + D * K * ‖l‖ := by
  intro K
  have hB0 : 0 < B := by linarith
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let Mβ := fun x => β • M x
  have hmm := AbstractEnergy.scaled_measurable β M hMm
  have he : ∀ᵐ x ∂ν, ∀ i j,
      |Mβ x i j| ≤ (β * B) * (1 + componentDistance g i j) ^ (-s) := by
    filter_upwards [hM] with x hx i j
    simpa only [Mβ, Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hβ, mul_assoc] using
      mul_le_mul_of_nonneg_left (hx.2.2 i j) hβ.le
  have hb : ∀ᵐ x ∂ν, ∀ i j, |Mβ x i j| ≤ β * B := by
    filter_upwards [he] with x hx i j
    exact (hx i j).trans (mul_le_of_le_one_right (by positivity)
      (Real.rpow_le_one_of_one_le_of_nonpos
        (by linarith [ComponentGeometryBounds.nonneg g i j]) (by linarith)))
  have hsβ : ∀ᵐ x ∂ν, ∀ i j, Mβ x i j = Mβ x j i := by
    filter_upwards [hM] with x hx i j
    simp only [Mβ, Matrix.smul_apply, smul_eq_mul, hx.1 i j]
  have hlower : ∀ᵐ x ∂ν, ∀ z : Fin (m : ℕ) → ℝ,
      (β * B⁻¹) * ∑ i, z i ^ 2 ≤ ∑ i, ∑ j, z i * Mβ x i j * z j := by
    filter_upwards [AbstractEnergy.scaled_lower β B⁻¹ hβ.le M
      (hM.mono fun x hx => hx.2.1) ⊤] with x hx z
    exact hx z (Submodule.mem_top)
  obtain ⟨v, hv, hnv⟩ := hdec i₀ χ
  have hvs := sum_point_profile m s hs g i₀ (fun i => (v i).val) D ‖χ‖ hD (norm_nonneg _) hnv
  have hus := constrained_l1 m s hs g Q hQ Mβ hmm (β * B⁻¹) (β * B)
    (by positivity) (by positivity) he hlower _ u v hu hv
  have hfactor : (β * B⁻¹)⁻¹ * (β * B * K) = B ^ 2 * K := by
    field_simp
  change (∑ i, ‖(u i).val‖) ≤ (2 + (β * B⁻¹)⁻¹ * (β * B * K)) * ∑ i, ‖(v i).val‖ at hus
  rw [hfactor] at hus
  have hus' : ∑ i, ‖(u i).val‖ ≤ ((2 + B ^ 2 * K) * D * K) * ‖χ‖ := by
    calc
      _ ≤ (2 + B ^ 2 * K) * ∑ i, ‖(v i).val‖ := hus
      _ ≤ (2 + B ^ 2 * K) * (D * K * ‖χ‖) := by gcongr
      _ = _ := by ring
  have hcol : ∀ᵐ x ∂ν, ∀ j, ∑ i, |Mβ x i j| ≤ β * B * K := by
    filter_upwards [he] with x hx j
    calc
      _ ≤ ∑ i, (β * B) * (1 + componentDistance g i j) ^ (-s) := Finset.sum_le_sum fun i _ => hx i j
      _ = (β * B) * ∑ i, (1 + componentDistance g i j) ^ (-s) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (by
        simpa only [ComponentGeometryBounds.symm g] using ComponentGeometryBounds.sum_power_le g j hs) (by positivity)
  obtain ⟨l, hl, hln⟩ := normal_l2 m Q Mβ hmm (β * B * K) (by positivity) hcol
    (fun i => if i = i₀ then χ else 0) u
  refine ⟨l, hl, ?_, ?_⟩
  · simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hln
    calc
      _ ≤ (m : ℝ)⁻¹ * (β * B * K * ∑ j, ‖(u j).val‖ + ‖χ‖) := hln
      _ ≤ (m : ℝ)⁻¹ * (β * B * K * (((2 + B ^ 2 * K) * D * K) * ‖χ‖) + ‖χ‖) := by gcongr
      _ = _ := by ring
  intro j
  obtain ⟨w, hw, hnw⟩ := hdec j (u j).val
  have hws := sum_point_profile m s hs g j (fun i => (w i).val) D ‖(u j).val‖ hD (norm_nonneg _) hnw
  have hid := point_source_duality m Q hQ Mβ hmm ⟨β * B, hb⟩ hsβ i₀ j χ (u j).val u w hu hw l hl
  rw [real_inner_self_eq_norm_sq] at hid
  have hwi : ‖(w i₀).val‖ ≤ D * (1 + componentDistance g j i₀) ^ (-s) * ‖(u j).val‖ := by
    simpa only [ComponentGeometryBounds.symm g i₀ j] using hnw i₀
  have hsum : ‖∑ i, (w i).val‖ ≤ D * K * ‖(u j).val‖ := (norm_sum_le _ _).trans hws
  have hquad : ‖(u j).val‖ ^ 2 ≤
      (D * (1 + componentDistance g j i₀) ^ (-s) * ‖χ‖ + D * K * ‖l‖) * ‖(u j).val‖ := by
    calc
      _ ≤ ‖χ‖ * ‖(w i₀).val‖ + ‖l‖ * ‖∑ i, (w i).val‖ := by
        rw [hid]
        exact add_le_add (real_inner_le_norm _ _) (real_inner_le_norm _ _)
      _ ≤ ‖χ‖ * (D * (1 + componentDistance g j i₀) ^ (-s) * ‖(u j).val‖) +
          ‖l‖ * (D * K * ‖(u j).val‖) := by gcongr
      _ = _ := by ring
  by_cases hz : ‖(u j).val‖ = 0
  · rw [hz]
    have hp : 0 ≤ (1 + componentDistance g j i₀) ^ (-s) :=
      Real.rpow_nonneg (by linarith [ComponentGeometryBounds.nonneg g j i₀]) _
    positivity
  have hp : 0 < ‖(u j).val‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  nlinarith only [hquad, hp]

end Internal

/-- Uniform polynomial-loss form of Lemma 4.6.
The degree and prefactor precede the size, scalar form, geometry, coefficients,
source and labels. Both multiplier membership and constrained uniqueness are
conclusions. The multiplier is the normal representative. -/
theorem control_lambda_uniform (s β : ℝ) (hs : 1 < s) (hβ : 0 < β) :
    ∃ r C : ℝ, 0 ≤ r ∧ 1 ≤ C ∧
      ∀ (α : Type*) [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
        (m : ℕ+) (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q →
        IsConservativeScalarForm Q → ∀ (g : ComponentGeometry (Fin (m : ℕ)))
        (B : ℝ), 1 ≤ B →
        ∀ M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
        (∀ i j, Measurable (fun x => M x i j)) →
        (∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
          (∀ z : Fin (m : ℕ) → ℝ,
            B⁻¹ * ∑ i, z i ^ 2 ≤ ∑ i, ∑ j, z i * M x i j * z j) ∧
          (∀ i j, |M x i j| ≤ B * (1 + componentDistance g i j) ^ (-s))) →
        ∀ (i₀ : Fin (m : ℕ)) (χ : Lp ℝ 2 ν),
          (∃! u : Fin (m : ℕ) → Q.1, WeightedWeakSolution Q (fun x => β • M x)
            (zeroSumComponents _) (fun i => if i = i₀ then χ else 0) u) ∧
          ∀ u : Fin (m : ℕ) → Q.1, WeightedWeakSolution Q (fun x => β • M x)
            (zeroSumComponents _) (fun i => if i = i₀ then χ else 0) u →
          ∃ l : Lp ℝ 2 ν,
            (∀ᵐ x ∂ν, l x = gapMultiplierField m Q (fun x => β • M x)
              (fun i => if i = i₀ then χ else 0) u x) ∧
            ‖l‖ ≤ C * B ^ r * (m : ℝ)⁻¹ * ‖χ‖ ∧
            ∀ j, ‖(u j).val‖ ≤ C * B ^ r *
              ((1 + componentDistance g j i₀) ^ (-s) + (m : ℝ)⁻¹) * ‖χ‖ := by
  obtain ⟨r, C, hr, hC, hdec⟩ := OptimalDecay.optimal_decay_uniform s β hs hβ
  let K := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s)
  let L := C * K * (2 + K)
  let U := β * K * L + 1
  let E := 1 + U + C + C * K * U
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hC0 : 0 ≤ C := by linarith
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hU : 1 ≤ U := by dsimp [U]; linarith [mul_nonneg (mul_nonneg hβ.le hK) hL]
  have hU0 : 0 ≤ U := by linarith
  have hE : 1 ≤ E := by dsimp [E]; nlinarith [mul_nonneg (mul_nonneg hC0 hK) hU0]
  have hEU : U ≤ E := by dsimp [E]; linarith [mul_nonneg (mul_nonneg hC0 hK) hU0]
  have hEC : C ≤ E := by dsimp [E]; linarith [mul_nonneg (mul_nonneg hC0 hK) hU0]
  have hECU : C * K * U ≤ E := by dsimp [E]; linarith
  refine ⟨2 * r + 3, E, by linarith, hE, ?_⟩
  intro α _ ν _ m Q hQ hcons g B hB M hmm hM i₀ χ
  have hB0 : 0 < B := by linarith
  have hex := constrained_exists_unique m β hβ Q hQ M hmm B⁻¹ (by positivity)
    (hM.mono fun x hx => ⟨hx.1, hx.2.1⟩) (fun i => if i = i₀ then χ else 0)
  refine ⟨hex, ?_⟩
  intro u hu
  have hdec' (i : Fin (m : ℕ)) (η : Lp ℝ 2 ν) :
      ∃ v : Fin (m : ℕ) → Q.1,
        WeightedWeakSolution Q (fun x => β • M x) ⊤ (fun k => if k = i then η else 0) v ∧
        ∀ j, ‖(v j).val‖ ≤ (C * B ^ r) * (1 + componentDistance g j i) ^ (-s) * ‖η‖ := by
    have hh := hdec α (Fin (m : ℕ)) ν Q hQ hcons g B hB M hmm hM i η
    obtain ⟨v, hv, _⟩ := hh.1
    exact ⟨v, hv, hh.2 v hv⟩
  obtain ⟨l, hl, hln, hcomp⟩ := Internal.estimate_of_point_source_bounds m s β hs hβ g Q hQ M hmm B hB hM
    (C * B ^ r) (by positivity) hdec' i₀ χ u hu
  change ‖l‖ ≤ (m : ℝ)⁻¹ * (β * B * K * ((2 + B ^ 2 * K) * (C * B ^ r) * K) + 1) * ‖χ‖ at hln
  have hB2 : 1 ≤ B ^ (2 : ℕ) := one_le_pow₀ hB
  have hpoly : 2 + B ^ 2 * K ≤ (2 + K) * B ^ 2 := by nlinarith only [hB2]
  have hterm : β * B * K * ((2 + B ^ 2 * K) * (C * B ^ r) * K) ≤
      (β * K * L) * B ^ (r + 3) := by
    calc
      _ ≤ β * B * K * (((2 + K) * B ^ 2) * (C * B ^ r) * K) := by gcongr
      _ = _ := by rw [Real.rpow_add hB0, Real.rpow_ofNat]; dsimp [L]; ring
  have hBp : 1 ≤ B ^ (r + 3) := Real.one_le_rpow hB (by linarith)
  have hcost : β * B * K * ((2 + B ^ 2 * K) * (C * B ^ r) * K) + 1 ≤ U * B ^ (r + 3) := by
    dsimp [U]
    nlinarith only [hterm, hBp]
  have hsharp : ‖l‖ ≤ U * B ^ (r + 3) * (m : ℝ)⁻¹ * ‖χ‖ := by
    calc
      _ ≤ (m : ℝ)⁻¹ * (β * B * K * ((2 + B ^ 2 * K) * (C * B ^ r) * K) + 1) * ‖χ‖ := hln
      _ ≤ (m : ℝ)⁻¹ * (U * B ^ (r + 3)) * ‖χ‖ := by gcongr
      _ = _ := by ring
  have hp₁ : B ^ r ≤ B ^ (2 * r + 3) :=
    Real.rpow_le_rpow_of_exponent_le hB (by linarith)
  have hp₂ : B ^ (r + 3) ≤ B ^ (2 * r + 3) :=
    Real.rpow_le_rpow_of_exponent_le hB (by linarith)
  have hpadd : B ^ r * B ^ (r + 3) = B ^ (2 * r + 3) := by
    rw [← Real.rpow_add hB0]
    congr 1
    ring
  refine ⟨l, hl, ?_, ?_⟩
  · exact hsharp.trans (by gcongr)
  intro j
  have hprofile : 0 ≤ (1 + componentDistance g j i₀) ^ (-s) :=
    Real.rpow_nonneg (by linarith [ComponentGeometryBounds.nonneg g j i₀]) _
  calc
    _ ≤ (C * B ^ r) * (1 + componentDistance g j i₀) ^ (-s) * ‖χ‖ +
        (C * B ^ r) * K * ‖l‖ := hcomp j
    _ ≤ (C * B ^ r) * (1 + componentDistance g j i₀) ^ (-s) * ‖χ‖ +
        (C * B ^ r) * K * (U * B ^ (r + 3) * (m : ℝ)⁻¹ * ‖χ‖) := by gcongr
    _ = (C * B ^ r) * (1 + componentDistance g j i₀) ^ (-s) * ‖χ‖ +
        (C * K * U) * (B ^ r * B ^ (r + 3)) * (m : ℝ)⁻¹ * ‖χ‖ := by ring
    _ ≤ (E * B ^ (2 * r + 3)) * (1 + componentDistance g j i₀) ^ (-s) * ‖χ‖ +
        (E * B ^ (2 * r + 3)) * (m : ℝ)⁻¹ * ‖χ‖ := by rw [hpadd]; gcongr
    _ = _ := by ring

/-- See Lemma 4.6 of the paper, with the polynomial-loss quantifier
order of Section 4: the exponent precedes h, A, every size and all source data.
The abstract admissible scalar form may be intrinsic or Euclidean. The component
geometry includes the interval in the statement and inherited cyclic geometry.
The weak solution is the constrained inverse of Lemma 4.6. See also
`constrained_unique_minimum` for its unique-minimum characterization. -/
theorem control_lambda (s : ShortExponent) (β : InverseTemperature)
    (q : ℝ) (hq : 0 ≤ q) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ h : ℝ, 0 < h → ∀ A : ℝ, 1 ≤ A →
      ∃ C : ℝ, 1 ≤ C ∧
      ∀ (n m : ℕ+), (m : ℕ) ≤ (n : ℕ) →
      ∀ (α : Type*) [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
        (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q →
        IsConservativeScalarForm Q → ∀ g : ComponentGeometry (Fin (m : ℕ)),
        ∀ M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
          SummableCoerciveMatrix (ρ := ν) s n h A q g M →
          ∀ (i₀ : Fin (m : ℕ)) (χ : Lp ℝ 2 ν),
            (∃! u : Fin (m : ℕ) → Q.1,
              WeightedWeakSolution Q (fun x => β.val • M x) (zeroSumComponents _)
                (fun i => if i = i₀ then χ else 0) u) ∧
            ∀ u : Fin (m : ℕ) → Q.1,
              WeightedWeakSolution Q (fun x => β.val • M x) (zeroSumComponents _)
                (fun i => if i = i₀ then χ else 0) u →
              ∃ l : Lp ℝ 2 ν,
                (∀ᵐ x ∂ν, l x = gapMultiplierField m Q (fun x => β.val • M x)
                  (fun i => if i = i₀ then χ else 0) u x) ∧
                ‖l‖ ≤ C * (n : ℝ) ^ (r * h) * (m : ℝ)⁻¹ * ‖χ‖ ∧
                ∀ j, ‖(u j).val‖ ≤ C * (n : ℝ) ^ (r * h) *
                  ((1 + componentDistance g j i₀) ^ (-s.val) + (m : ℝ)⁻¹) * ‖χ‖ := by
  obtain ⟨r, C, hr, hC, hbound⟩ := control_lambda_uniform s.val β.val s.property β.property
  refine ⟨q * r, mul_nonneg hq hr, ?_⟩
  intro h hh A hA
  have hA0 : 0 < A := by linarith
  refine ⟨C * A ^ r, one_le_mul_of_one_le_of_one_le hC (Real.one_le_rpow hA hr), ?_⟩
  intro n m _hm α _ ν _ Q hQ hcons g M hM i₀ χ
  have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.property
  have hn0 : (0 : ℝ) < (n : ℝ) := by positivity
  have hB : 1 ≤ A * (n : ℝ) ^ (q * h) :=
    one_le_mul_of_one_le_of_one_le hA (Real.one_le_rpow hn (mul_nonneg hq hh.le))
  have he := hbound α ν m Q hQ hcons g (A * (n : ℝ) ^ (q * h)) hB M hM.1 hM.2 i₀ χ
  have hfactor : C * (A * (n : ℝ) ^ (q * h)) ^ r =
      (C * A ^ r) * (n : ℝ) ^ ((q * r) * h) := by
    rw [Real.mul_rpow hA0.le (by positivity), ← Real.rpow_mul hn0.le,
      show (q * h) * r = (q * r) * h by ring]
    ring
  simpa only [hfactor] using he

/-- Internal realization bridge for Lemma 4.6: the full-domain
constrained weak solution is the unique quadratic minimizer. This reuses the
matrix-energy minimum theorem, including all finite-energy competitors. -/
theorem constrained_unique_minimum (m : ℕ+) (β : ℝ) (hβ : 0 < β)
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j)) (a : ℝ) (ha : 0 < a)
    (hM : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
      ∀ z : Fin (m : ℕ) → ℝ, a * ∑ i, z i ^ 2 ≤ ∑ i, ∑ j, z i * M x i j * z j)
    (f : Fin (m : ℕ) → Lp ℝ 2 ν) (u : Fin (m : ℕ) → Q.1)
    (hu : WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _) f u) :
    ∀ w : Fin (m : ℕ) → Q.1,
      WeightedFormDomain Q (fun x => β • M x) (zeroSumComponents _) w →
      let Ju := (∑ i, Q.2 (u i) (u i)) +
        (∫ x, matrixFieldPair (fun x => β • M x) (fun i => (u i).val) (fun i => (u i).val) x ∂ν) -
        2 * (∑ i, inner ℝ (f i) (u i).val)
      let Jw := (∑ i, Q.2 (w i) (w i)) +
        (∫ x, matrixFieldPair (fun x => β • M x) (fun i => (w i).val) (fun i => (w i).val) x ∂ν) -
        2 * (∑ i, inner ℝ (f i) (w i).val)
      Ju ≤ Jw ∧ (Jw = Ju → w = u) := by
  exact MatrixEnergy.weightedWeakSolution_unique_minimum Q hQ (fun x => β • M x)
    (zeroSumComponents _) (AbstractEnergy.scaled_posSemidef β a hβ.le ha.le M hM)
    (β * a) (mul_pos hβ ha)
    (AbstractEnergy.scaled_lower β a hβ.le M (hM.mono fun x hx => hx.2) _)
    (AbstractEnergy.scaled_measurable β M hMm) f u hu

/-- Boundary check for Lemma 4.6: on one component the
constraint forces the solution to vanish and the multiplier is exactly −χ. -/
theorem singleton_solution_and_multiplier (Q : ScalarFormData ν)
    (M : α → Matrix (Fin 1) (Fin 1) ℝ) (χ : Lp ℝ 2 ν) (u : Fin 1 → Q.1)
    (hu : WeightedWeakSolution Q M (zeroSumComponents _) (fun _ => χ) u) :
    u = 0 ∧ ∀ᵐ x ∂ν, gapMultiplierField 1 Q M (fun _ => χ) u x = -χ x := by
  have hs := ConstrainedNormalMultiplier.tuple_sum_zero 1 Q u hu.1.1
  change (∑ i : Fin 1, u i) = 0 at hs
  rw [Fin.sum_univ_one] at hs
  have hzero : u = 0 := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    simpa only [hi, Pi.zero_apply] using hs
  refine ⟨hzero, ?_⟩
  have hz : ∀ᵐ x ∂ν, (u 0).val x = 0 := by
    rw [hzero]
    change ∀ᵐ x ∂ν, (0 : Lp ℝ 2 ν) x = 0
    filter_upwards [Lp.coeFn_zero ℝ 2 ν] with x hx
    simpa only [Pi.zero_apply] using hx
  filter_upwards [hz] with x hx
  have hj (j : Fin 1) : (u j).val x = 0 := by
    have he : j = 0 := Subsingleton.elim _ _
    simpa only [he] using hx
  have hm : (∑ i : Fin 1, ∑ j : Fin 1, M x i j * (u j).val x) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    rw [hj j, mul_zero]
  unfold gapMultiplierField
  change ((1 : ℕ+) : ℝ)⁻¹ * ((∑ i : Fin 1, ∑ j : Fin 1, M x i j * (u j).val x) -
    ∑ _i : Fin 1, χ x) = -χ x
  rw [hm, Fin.sum_univ_one]
  norm_num

end Riesz2.MultiplierControl
