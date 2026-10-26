/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.DerivativeControl

/-!
# Projection and Schur cancellation for the local boundary source

The projected equation of the proof of Proposition 5.15 is obtained
directly from the weak equation. The Schur identities below keep the
scalar generator inside the exterior form inverse and fix the signs in
Subsection 5.5.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter
open scoped BigOperators Classical

namespace Riesz2.LocalizedBoundary

section Projection

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  {ν : Measure Ω}

omit [Fintype ι] [DecidableEq ι] in
/-- See the proof of Proposition 5.15 in the paper: integrability of every restricted row pairing. -/
theorem row_integrable_internal (M : Ω → Matrix ι ι ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hMb : ∃ B : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ B)
    (u : ι → Lp ℝ 2 ν) (v : Lp ℝ 2 ν) (l : ι) (J : Finset ι) :
    Integrable (fun x => ∑ i ∈ J, M x l i * u i x * v x) ν := by
  obtain ⟨B, hB⟩ := hMb
  apply integrable_finsetSum
  intro i _
  have h := ((Lp.memLp (u i)).integrable_mul (Lp.memLp v)).bdd_mul
    (hMm l i).aestronglyMeasurable
    (hB.mono (fun x hx => by simpa only [Real.norm_eq_abs] using hx l i))
  convert h using 1
  ext x
  simp only [Pi.mul_apply]
  ring

/-- See the proof of Proposition 5.15 in the paper: single-component equation from the unrestricted weak equation, for every test in the scalar form domain. -/
theorem row_weak_internal (Q : ScalarFormData ν) (M : Ω → Matrix ι ι ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hMb : ∃ B : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ B)
    (hMs : ∀ᵐ x ∂ν, ∀ i j, M x i j = M x j i)
    (f : ι → Lp ℝ 2 ν) (u : ι → Q.1)
    (hu : WeightedWeakSolution Q M ⊤ f u) (l : ι) (v : Q.1) :
    Q.2 (u l) v + (∫ x, ∑ i, M x l i * (u i).val x * v.val x ∂ν) =
      inner ℝ (f l) v.val := by
  let k : ι → Q.1 := Pi.single l v
  have hk : WeightedFormDomain Q M ⊤ k :=
    (BoundedMatrixForms.domain_iff Q M hMm hMb ⊤ k).mpr
      (Eventually.of_forall (fun _ => Submodule.mem_top))
  have he := (hu.2 k hk).2
  have hpair : matrixFieldPair M (fun i => (u i).val) (fun i => (k i).val) =ᵐ[ν]
      fun x => ∑ i, M x l i * (u i).val x * v.val x := by
    filter_upwards [hMs, Lp.coeFn_zero ℝ 2 ν] with x hx hzero
    have hkv (i : ι) : (k i).val x = if i = l then v.val x else 0 := by
      by_cases hi : i = l
      · subst i
        simp only [k, Pi.single_apply, ite_true]
      · simpa only [k, Pi.single_apply, hi, ite_false, Submodule.coe_zero,
          Pi.zero_apply] using hzero
    simp only [matrixFieldPair, hkv, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    apply Finset.sum_congr rfl
    intro i _
    rw [hx i l]
    ring
  rw [integral_congr_ae hpair] at he
  simpa only [k, Pi.single_apply, apply_ite, map_zero, Submodule.coe_zero,
    inner_zero_right, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using he

/-- Projection onto a finite set avoiding the source index, in the proof of
Proposition 5.15. All scalar tests remain in the original form domain. -/
theorem projection_internal (Q : ScalarFormData ν) (M : Ω → Matrix ι ι ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hMb : ∃ B : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ B)
    (hMs : ∀ᵐ x ∂ν, ∀ i j, M x i j = M x j i)
    (χ lam : Lp ℝ 2 ν) (i₀ : ι) (u : ι → Q.1)
    (hu : WeightedWeakSolution Q M ⊤ (fun i => (if i = i₀ then χ else 0) + lam) u)
    (J : Finset ι) (hi₀ : i₀ ∉ J) (l : ι) (hl : l ∈ J) (v : Q.1) :
    Q.2 (u l) v + (∫ x, ∑ i ∈ J, M x l i * (u i).val x * v.val x ∂ν) =
      -(∫ x, ∑ i ∈ Jᶜ, M x l i * (u i).val x * v.val x ∂ν) + inner ℝ lam v.val := by
  have hli : l ≠ i₀ := fun h => hi₀ (h ▸ hl)
  have he := row_weak_internal Q M hMm hMb hMs _ u hu l v
  simp only [ite_eq_right hli, zero_add] at he
  have hi := row_integrable_internal M hMm hMb (fun i => (u i).val) v.val l J
  have hc := row_integrable_internal M hMm hMb (fun i => (u i).val) v.val l Jᶜ
  have hs : (fun x => ∑ i, M x l i * (u i).val x * v.val x) =
      fun x => (∑ i ∈ J, M x l i * (u i).val x * v.val x) +
        ∑ i ∈ Jᶜ, M x l i * (u i).val x * v.val x := by
    funext x
    exact (Finset.sum_add_sum_compl J _).symm
  rw [hs, integral_add hi hc] at he
  linarith only [he]

/-- The projected equation in the proof of Proposition 5.15, for a
periodized matrix and constrained solution. The projected set may be any
set avoiding the source index. Multiplier L² regularity and integrability
of both row pairings are conclusions. -/
theorem projected_equation (s : Riesz1.RieszExponent) (n m : ℕ+)
    (hm : 2 ≤ (m : ℕ)) (K : ℕ) (C κ γ ε : ℝ)
    (Q : ScalarFormData ν) (M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M)
    (β : ℝ) (χ : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1)
    (hu : WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _)
      (fun i => if i = i₀ then χ else 0) u) :
    ∃ lam : Lp ℝ 2 ν,
      (∀ᵐ x ∂ν, lam x = gapMultiplierField m Q (fun x => β • M x)
        (fun i => if i = i₀ then χ else 0) u x) ∧
      ∀ J : Finset (Fin (m : ℕ)), i₀ ∉ J → ∀ l ∈ J, ∀ v : Q.1,
        Integrable (fun x => ∑ i ∈ J, β * M x l i * (u i).val x * v.val x) ν ∧
        Integrable (fun x => ∑ i ∈ Jᶜ, β * M x l i * (u i).val x * v.val x) ν ∧
        Q.2 (u l) v + (∫ x, ∑ i ∈ J, β * M x l i * (u i).val x * v.val x ∂ν) =
          -(∫ x, ∑ i ∈ Jᶜ, β * M x l i * (u i).val x * v.val x ∂ν) +
            inner ℝ lam v.val := by
  have hMm := SchurRestriction.periodized_scaled_measurable β hM
  have hMb := SchurRestriction.periodized_scaled_bounded β hM
  have hMs : ∀ᵐ x ∂ν, ∀ i j, (β • M x) i j = (β • M x) j i :=
    hM.2.1.mono (fun x hx i j => by
      simp only [Matrix.smul_apply, smul_eq_mul, hx.1 i j])
  obtain ⟨lam, hlam, he⟩ := DerivativeControl.restore_multiplier m Q
    (fun x => β • M x) hMm hMb hMs _ u hu
  refine ⟨lam, hlam, fun J hJ l hl v => ?_⟩
  exact ⟨row_integrable_internal _ hMm hMb _ _ l J,
    row_integrable_internal _ hMm hMb _ _ l Jᶜ,
    projection_internal Q _ hMm hMb hMs χ lam i₀ u he J hJ l hl v⟩

end Projection

section Schur

variable {U W : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

omit [CompleteSpace U] in
/-- See Subsection 5.5 of the paper, sign identity for the embedded field. Here `A`
is the new principal form including the scalar energy and `R` is the
boundary remainder form including its factor β. -/
theorem embedded_source_identity_internal
    (A R : U →L[ℝ] U →L[ℝ] ℝ) (D : W →L[ℝ] W →L[ℝ] ℝ)
    (C : U →L[ℝ] W →L[ℝ] ℝ) (d : ℝ) (hd : 0 < d)
    (hD : ∀ w, d * ‖w‖ ^ 2 ≤ D w w) (f : StrongDual ℝ U)
    (u : U) (hu : ∀ v, A u v + R u v = f v) :
    ∀ p : U × W,
      OperatorSchur.blockForm A D C
        (u, -OperatorSchur.exterior D C d hd hD u) p =
      f p.1 - C p.1 (OperatorSchur.exterior D C d hd hD u) - R u p.1 := by
  rintro ⟨v, w⟩
  simp only [OperatorSchur.blockForm_apply, map_neg, neg_apply,
    OperatorSchur.exterior_solves]
  linarith only [hu v]

/-- See the proof of Proposition 5.15 in the paper, Schur restriction identity under
the exact internal form equations. Uniqueness is derived from full block
coercivity. -/
theorem restriction_identity_internal
    (A R : U →L[ℝ] U →L[ℝ] ℝ) (D : W →L[ℝ] W →L[ℝ] ℝ)
    (C : U →L[ℝ] W →L[ℝ] ℝ) (d : ℝ) (hd : 0 < d)
    (hD : ∀ w, d * ‖w‖ ^ 2 ≤ D w w)
    (c : ℝ) (hc : 0 < c)
    (hfull : ∀ u w, c * (‖u‖ ^ 2 + ‖w‖ ^ 2) ≤
      OperatorSchur.blockForm A D C (u, w) (u, w))
    (f : StrongDual ℝ U) (u : U) (hu : ∀ v, A u v + R u v = f v)
    (ψ₀ : U × W)
    (hψ₀ : ∀ p : U × W, OperatorSchur.blockForm A D C ψ₀ p =
      f p.1 - C p.1 (OperatorSchur.exterior D C d hd hD u) - R u p.1) :
    ψ₀.1 = u ∧ ψ₀.2 = -OperatorSchur.exterior D C d hd hD u := by
  let g : StrongDual ℝ U := f - C.flip (OperatorSchur.exterior D C d hd hD u) - R u
  have he : ∀ p, OperatorSchur.blockForm A D C
      (u, -OperatorSchur.exterior D C d hd hD u) p = g p.1 + (0 : StrongDual ℝ W) p.2 := by
    simpa only [g, sub_apply, ContinuousLinearMap.flip_apply,
      zero_apply, add_zero] using
      embedded_source_identity_internal A R D C d hd hD f u hu
  have hψ : ∀ p, OperatorSchur.blockForm A D C ψ₀ p =
      g p.1 + (0 : StrongDual ℝ W) p.2 := by
    simpa only [g, sub_apply, ContinuousLinearMap.flip_apply,
      zero_apply, add_zero] using hψ₀
  obtain ⟨p, hp, huniq⟩ := OperatorSchur.block_existsUnique A D C d hd hD c hc hfull g 0
  have heq := (huniq ψ₀ hψ).trans (huniq _ he).symm
  exact ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩

end Schur

end Riesz2.LocalizedBoundary

end
