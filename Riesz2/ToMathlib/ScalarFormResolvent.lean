/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.CoerciveSolutionMaps
public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Bounded resolvents of the scalar form

The ambient resolvent is the value projection of the existing, uniquely
specified weak solution. Its resolvent identity and bounded transform hold
on real L², without an eigenbasis or an additional operator realization.
Infrastructure for the proof of Proposition 5.15.
-/

@[expose] public section
noncomputable section

open MeasureTheory

namespace Riesz2.ScalarFormResolvent

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}
  (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)

/-- The ambient bounded operator `(b + L)⁻¹`, for a strictly positive shift.
This is the value of the scalar weak solution, on its whole carrier. -/
def resolvent (b : ℝ) (hb : 0 < b) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  (ScalarFormHilbert.value Q hQ).comp (ScalarFormHilbert.shiftedSolution Q hQ b hb)

theorem resolvent_apply (b : ℝ) (hb : 0 < b) (f : Lp ℝ 2 ν) :
    resolvent Q hQ b hb f =
      (ScalarFormHilbert.equiv Q hQ (ScalarFormHilbert.shiftedSolution Q hQ b hb f)).val :=
  rfl

/-- Symmetry of the weak inverse on ambient L². -/
theorem symmetric (b : ℝ) (hb : 0 < b) (f g : Lp ℝ 2 ν) :
    inner ℝ (resolvent Q hQ b hb f) g = inner ℝ f (resolvent Q hQ b hb g) := by
  have hf := ScalarFormHilbert.shiftedSolution_solves Q hQ b hb f
    (ScalarFormHilbert.shiftedSolution Q hQ b hb g)
  have hg := ScalarFormHilbert.shiftedSolution_solves Q hQ b hb g
    (ScalarFormHilbert.shiftedSolution Q hQ b hb f)
  rw [hQ.2.1, real_inner_comm] at hg
  change _ = inner ℝ f (ScalarFormHilbert.value Q hQ
    (ScalarFormHilbert.shiftedSolution Q hQ b hb g))
  rw [real_inner_comm]
  exact hg.symm.trans hf

/-- A positive scalar shift gives a positive self-adjoint bounded inverse. -/
theorem isPositive (b : ℝ) (hb : 0 < b) :
    (resolvent Q hQ b hb).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff _).mpr
  refine ⟨symmetric Q hQ b hb, fun f => ?_⟩
  have he := ScalarFormHilbert.shiftedSolution_solves Q hQ b hb f
    (ScalarFormHilbert.shiftedSolution Q hQ b hb f)
  rw [real_inner_self_eq_norm_sq] at he
  rw [real_inner_comm]
  change 0 ≤ inner ℝ f (ScalarFormHilbert.value Q hQ
    (ScalarFormHilbert.shiftedSolution Q hQ b hb f))
  rw [← he]
  exact add_nonneg (hQ.2.2.1 _) (mul_nonneg hb.le (sq_nonneg _))

theorem isSelfAdjoint (b : ℝ) (hb : 0 < b) :
    IsSelfAdjoint (resolvent Q hQ b hb) :=
  (isPositive Q hQ b hb).isSelfAdjoint

/-- The sharp ambient resolvent bound. -/
theorem norm_le (b : ℝ) (hb : 0 < b) : ‖resolvent Q hQ b hb‖ ≤ b⁻¹ := by
  refine (resolvent Q hQ b hb).opNorm_le_bound (inv_nonneg.mpr hb.le) ?_
  intro f
  change ‖ScalarFormHilbert.value Q hQ
    (ScalarFormHilbert.shiftedSolution Q hQ b hb f)‖ ≤ _
  exact ScalarFormHilbert.shiftedSolution_value_norm_le Q hQ b hb f

/-- Injectivity follows from density of the literal scalar domain. -/
theorem injective (b : ℝ) (hb : 0 < b) :
    Function.Injective (resolvent Q hQ b hb) := by
  intro f g hfg
  have hu : ScalarFormHilbert.shiftedSolution Q hQ b hb f =
      ScalarFormHilbert.shiftedSolution Q hQ b hb g :=
    ScalarFormHilbert.value_injective Q hQ hfg
  have he (w : Q.1) : inner ℝ f w.val = inner ℝ g w.val := by
    change inner ℝ f (ScalarFormHilbert.value Q hQ
      ((ScalarFormHilbert.equiv Q hQ).symm w)) = _
    rw [← ScalarFormHilbert.shiftedSolution_solves Q hQ b hb f
      ((ScalarFormHilbert.equiv Q hQ).symm w), hu]
    exact ScalarFormHilbert.shiftedSolution_solves Q hQ b hb g _
  have hall : ∀ x : Lp ℝ 2 ν, inner ℝ f x = inner ℝ g x := by
    have hh := hQ.1.equalizer ((continuous_const.inner continuous_id))
      ((continuous_const.inner continuous_id)) (funext he)
    exact congrFun hh
  exact ext_inner_right ℝ hall

/-- Resolvent identity on the complete form domain. Its value projection gives
the usual bounded-operator identity. -/
theorem solution_sub (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (f : Lp ℝ 2 ν) :
    ScalarFormHilbert.shiftedSolution Q hQ a ha f -
      ScalarFormHilbert.shiftedSolution Q hQ b hb f =
        (b - a) • ScalarFormHilbert.shiftedSolution Q hQ a ha
          (resolvent Q hQ b hb f) := by
  let u := ScalarFormHilbert.shiftedSolution Q hQ a ha f
  let v := ScalarFormHilbert.shiftedSolution Q hQ b hb f
  have heq : u - v = ScalarFormHilbert.shiftedSolution Q hQ a ha
      ((b - a) • resolvent Q hQ b hb f) := by
    apply ScalarFormHilbert.shiftedSolution_unique Q hQ a ha
    intro w
    have hu := ScalarFormHilbert.shiftedSolution_solves Q hQ a ha f w
    have hv := ScalarFormHilbert.shiftedSolution_solves Q hQ b hb f w
    change Q.2 (ScalarFormHilbert.equiv Q hQ u) _ +
      a * inner ℝ (ScalarFormHilbert.value Q hQ u) _ = _ at hu
    change Q.2 (ScalarFormHilbert.equiv Q hQ v) _ +
      b * inner ℝ (ScalarFormHilbert.value Q hQ v) _ = _ at hv
    simp only [map_sub, LinearMap.sub_apply, inner_sub_left, real_inner_smul_left,
      resolvent, ContinuousLinearMap.comp_apply]
    change Q.2 (ScalarFormHilbert.equiv Q hQ u) _ -
      Q.2 (ScalarFormHilbert.equiv Q hQ v) _ +
        a * (inner ℝ (ScalarFormHilbert.value Q hQ u) _ -
          inner ℝ (ScalarFormHilbert.value Q hQ v) _) =
            (b - a) * inner ℝ (ScalarFormHilbert.value Q hQ v) _
    linarith
  simpa only [map_smul] using heq

/-- The exact resolvent identity, including equal shifts. -/
theorem resolvent_sub (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    resolvent Q hQ a ha - resolvent Q hQ b hb =
      (b - a) • (resolvent Q hQ a ha * resolvent Q hQ b hb) := by
  apply ContinuousLinearMap.ext
  intro f
  have he := congrArg (ScalarFormHilbert.value Q hQ) (solution_sub Q hQ a b ha hb f)
  change resolvent Q hQ a ha f - resolvent Q hQ b hb f =
    (b - a) • resolvent Q hQ a ha (resolvent Q hQ b hb f)
  simpa only [map_sub, map_smul, resolvent, ContinuousLinearMap.comp_apply] using he

/-- Resolvents with different shifts commute, as do equal shifts. -/
theorem commute (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Commute (resolvent Q hQ a ha) (resolvent Q hQ b hb) := by
  by_cases hab : a = b
  · subst b; exact Commute.refl _
  have h := resolvent_sub Q hQ a b ha hb
  have h' := resolvent_sub Q hQ b a hb ha
  have he : (b - a) • (resolvent Q hQ a ha * resolvent Q hQ b hb) =
      (b - a) • (resolvent Q hQ b hb * resolvent Q hQ a ha) := by
    calc
      _ = resolvent Q hQ a ha - resolvent Q hQ b hb := h.symm
      _ = -(resolvent Q hQ b hb - resolvent Q hQ a ha) := (neg_sub _ _).symm
      _ = -((a - b) • (resolvent Q hQ b hb * resolvent Q hQ a ha)) := congrArg Neg.neg h'
      _ = _ := by
        have hn : -(a - b) = b - a := by ring
        exact (neg_smul (a - b) _).symm.trans (congrArg (fun c : ℝ => c • _) hn)
  exact (smul_right_injective _ (sub_ne_zero.mpr (Ne.symm hab))) he

/-- The bounded transform factor is invertible. Its two-sided inverse is
`I + (1-b) (b+L)⁻¹`. No nonsingular inverse with a default value is used. -/
theorem bounded_transform_inverse (b : ℝ) (hb : 0 < b) :
    let T := resolvent Q hQ 1 zero_lt_one
    let R := resolvent Q hQ b hb
    (1 + (b - 1) • T) * (1 + (1 - b) • R) = 1 ∧
      (1 + (1 - b) • R) * (1 + (b - 1) • T) = 1 := by
  dsimp only
  have he := resolvent_sub Q hQ 1 b zero_lt_one hb
  have hc := commute Q hQ 1 b zero_lt_one hb
  have hexpand : (1 + (b - 1) • resolvent Q hQ 1 zero_lt_one) *
      (1 + (1 - b) • resolvent Q hQ b hb) = 1 := by
    apply ContinuousLinearMap.ext
    intro f
    have hf := congrArg (fun R : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν => R f) he
    simp only [sub_apply, smul_apply,
      mul_apply_eq_comp] at hf
    simp only [mul_apply_eq_comp, add_apply,
      one_apply_eq_self, smul_apply, map_add, map_smul]
    rw [← hf]
    module
  refine ⟨hexpand, ?_⟩
  rw [show (1 + (1 - b) • resolvent Q hQ b hb) *
      (1 + (b - 1) • resolvent Q hQ 1 zero_lt_one) =
    (1 + (b - 1) • resolvent Q hQ 1 zero_lt_one) *
      (1 + (1 - b) • resolvent Q hQ b hb) by
    apply ContinuousLinearMap.ext
    intro f
    have hh := congrArg (fun R : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν => R f) hc.eq
    simp only [mul_apply_eq_comp] at hh
    simp only [mul_apply_eq_comp, add_apply,
      one_apply_eq_self, smul_apply, map_add, map_smul]
    rw [hh]
    module]
  exact hexpand

/-- The weak inverse equals the rational function of `(I+L)⁻¹` prescribed in
the proof of Proposition 5.15 for `σ = 0`. -/
theorem bounded_transform (b : ℝ) (hb : 0 < b) :
    (1 + (b - 1) • resolvent Q hQ 1 zero_lt_one) * resolvent Q hQ b hb =
      resolvent Q hQ 1 zero_lt_one := by
  have he := resolvent_sub Q hQ 1 b zero_lt_one hb
  apply ContinuousLinearMap.ext
  intro f
  have hf := congrArg (fun R : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν => R f) he
  simp only [sub_apply, smul_apply,
    mul_apply_eq_comp] at hf
  simp only [mul_apply_eq_comp, add_apply,
    one_apply_eq_self, smul_apply]
  exact (add_comm _ _).trans (eq_add_of_sub_eq hf).symm

/-- The bounded transform is a positive contraction, also when the scalar
form has a nontrivial nullspace. -/
theorem transform_positive_contraction :
    (resolvent Q hQ 1 zero_lt_one).IsPositive ∧
      ‖resolvent Q hQ 1 zero_lt_one‖ ≤ 1 := by
  exact ⟨isPositive Q hQ 1 zero_lt_one, by simpa using norm_le Q hQ 1 zero_lt_one⟩

/-- The complement of the bounded transform is positive as well. This is
the order interval required by the bounded-transform functional calculus. -/
theorem transform_complement_positive :
    (1 - resolvent Q hQ 1 zero_lt_one).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff _).mpr
  refine ⟨?_, fun f => ?_⟩
  · intro f g
    change inner ℝ (f - resolvent Q hQ 1 zero_lt_one f) g =
      inner ℝ f (g - resolvent Q hQ 1 zero_lt_one g)
    simp only [inner_sub_left, inner_sub_right]
    rw [symmetric]
  · simp only [sub_apply, one_apply_eq_self, inner_sub_left, real_inner_self_eq_norm_sq]
    have hn : ‖resolvent Q hQ 1 zero_lt_one f‖ ≤ ‖f‖ := by
      change ‖ScalarFormHilbert.value Q hQ
        (ScalarFormHilbert.shiftedSolution Q hQ 1 zero_lt_one f)‖ ≤ _
      simpa only [inv_one, one_mul] using
        ScalarFormHilbert.shiftedSolution_value_norm_le Q hQ 1 zero_lt_one f
    have hh := real_inner_le_norm (resolvent Q hQ 1 zero_lt_one f) f
    have hm := mul_le_mul_of_nonneg_right hn (norm_nonneg f)
    nlinarith only [hh, hm]

/-- The full bilinear scalar energy of the weak inverse is the bounded
operator `R - b R²`. This is the form identity needed to identify the
half-generator multiplier. It does not assert a square-root construction. -/
theorem energy_pair (b : ℝ) (hb : 0 < b) (f g : Lp ℝ 2 ν) :
    Q.2 (ScalarFormHilbert.equiv Q hQ (ScalarFormHilbert.shiftedSolution Q hQ b hb f))
      (ScalarFormHilbert.equiv Q hQ (ScalarFormHilbert.shiftedSolution Q hQ b hb g)) =
        inner ℝ ((resolvent Q hQ b hb - b •
          (resolvent Q hQ b hb * resolvent Q hQ b hb)) f) g := by
  have he := ScalarFormHilbert.shiftedSolution_solves Q hQ b hb f
    (ScalarFormHilbert.shiftedSolution Q hQ b hb g)
  change _ + b * inner ℝ (resolvent Q hQ b hb f) (resolvent Q hQ b hb g) =
    inner ℝ f (resolvent Q hQ b hb g) at he
  simp only [sub_apply, smul_apply, mul_apply_eq_comp, inner_sub_left,
    real_inner_smul_left]
  rw [symmetric, symmetric]
  linarith only [he]

/-- The operator giving the resolvent's scalar energy is positive. -/
theorem energy_operator_positive (b : ℝ) (hb : 0 < b) :
    (resolvent Q hQ b hb - b • (resolvent Q hQ b hb * resolvent Q hQ b hb)).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff _).mpr
  refine ⟨?_, fun f => ?_⟩
  · intro f g
    change inner ℝ (resolvent Q hQ b hb f - b • resolvent Q hQ b hb (resolvent Q hQ b hb f)) g =
      inner ℝ f (resolvent Q hQ b hb g - b • resolvent Q hQ b hb (resolvent Q hQ b hb g))
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, inner_smul_right]
    rw [symmetric, symmetric, ← symmetric Q hQ b hb f,
      symmetric Q hQ b hb f (resolvent Q hQ b hb g)]
  · rw [← energy_pair]
    exact hQ.2.2.1 _

/-- The sharp scalar form-energy estimate, obtained by completing a square
in the weak equation (the proof of Proposition 5.15, infrastructure). -/
theorem energy_le (b : ℝ) (hb : 0 < b) (f : Lp ℝ 2 ν) :
    Q.2 (ScalarFormHilbert.equiv Q hQ (ScalarFormHilbert.shiftedSolution Q hQ b hb f))
      (ScalarFormHilbert.equiv Q hQ (ScalarFormHilbert.shiftedSolution Q hQ b hb f)) ≤
        (4 * b)⁻¹ * ‖f‖ ^ 2 := by
  have he := ScalarFormHilbert.shiftedSolution_solves Q hQ b hb f
    (ScalarFormHilbert.shiftedSolution Q hQ b hb f)
  rw [real_inner_self_eq_norm_sq] at he
  have hi := real_inner_le_norm f
    (ScalarFormHilbert.value Q hQ (ScalarFormHilbert.shiftedSolution Q hQ b hb f))
  have hsq := sq_nonneg (‖f‖ - 2 * b *
    ‖ScalarFormHilbert.value Q hQ (ScalarFormHilbert.shiftedSolution Q hQ b hb f)‖)
  rw [← div_eq_inv_mul]
  apply (le_div_iff₀ (show 0 < 4 * b by positivity)).mpr
  have hm := mul_le_mul_of_nonneg_left (he.le.trans hi)
    (show 0 ≤ 4 * b by positivity)
  nlinarith only [hm, hsq]

end Riesz2.ScalarFormResolvent
