/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.ComplexL2
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Continuous calculus for real L² operators through complexification

The coordinate maps are the existing Riesz 1 maps. Complexification is isometric,
and its closed real star algebra is stable under the real continuous calculus.
This supplies real operators without postulating a real functional-calculus instance.
Infrastructure for the proof of Proposition 5.15.
-/

@[expose] public section
noncomputable section

open MeasureTheory Riesz1

namespace Riesz2.RealL2ContinuousCalculus

variable {α : Type*} [MeasurableSpace α] (ν : Measure α)

-- Use the real algebra obtained from the complex algebra throughout the calculus.
local instance complexEndRealAlgebra : Algebra ℝ (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) :=
  Algebra.complexToReal
local instance complexEndRealModule : Module ℝ (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) :=
  (complexEndRealAlgebra ν).toModule
local instance complexEndRealSMul : SMul ℝ (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) :=
  (complexEndRealModule ν).toSMul
local instance complexEndRealTower : IsScalarTower ℝ ℝ (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) :=
  ⟨fun r s A => mul_smul r s A⟩

/-- The squared norm splits into the two existing real coordinates. -/
theorem norm_sq_coordinates (f : Lp ℂ 2 ν) :
    ‖f‖ ^ 2 = ‖complexL2Re ν f‖ ^ 2 + ‖complexL2Im ν f‖ ^ 2 := by
  have h := complexL2_inner_re ν f f
  change RCLike.re (inner ℂ f f) = _ at h
  rw [inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact h

/-- Inclusion of real L² preserves the norm, for every measure. -/
theorem norm_ofReal (f : Lp ℝ 2 ν) : ‖realL2Complex ν f‖ = ‖f‖ := by
  have h := norm_sq_coordinates ν (realL2Complex ν f)
  rw [complexL2Re_ofReal, complexL2Im_ofReal, norm_zero, zero_pow (by omega), add_zero] at h
  nlinarith [norm_nonneg (realL2Complex ν f), norm_nonneg f]

/-- The real coordinate projection is contractive. -/
theorem norm_re_le (f : Lp ℂ 2 ν) : ‖complexL2Re ν f‖ ≤ ‖f‖ := by
  have h := norm_sq_coordinates ν f
  nlinarith [sq_nonneg ‖complexL2Im ν f‖, norm_nonneg (complexL2Re ν f), norm_nonneg f]

/-- Complex-linear extension of a bounded real operator. -/
def complexify (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν :=
  LinearMap.mkContinuous
    ({ toFun := fun f => complexL2OfPair ν (A (complexL2Re ν f), A (complexL2Im ν f))
       map_add' := fun f g => by
        apply complexL2_ext ν <;> simp only [map_add, complexL2Re_ofPair, complexL2Im_ofPair]
       map_smul' := fun z f => by
        apply complexL2_ext ν
        · simp only [RingHom.id_apply, complexL2Re_ofPair, complexL2Im_ofPair, complexL2Re_smul,
            map_sub, map_smul]
        · simp only [RingHom.id_apply, complexL2Im_ofPair, complexL2Re_ofPair, complexL2Im_smul,
            map_add, map_smul] } : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν)
    ‖A‖ (fun f => by
      have h := norm_sq_coordinates ν
        (complexL2OfPair ν (A (complexL2Re ν f), A (complexL2Im ν f)))
      rw [complexL2Re_ofPair, complexL2Im_ofPair] at h
      have hr := A.le_opNorm (complexL2Re ν f)
      have hi := A.le_opNorm (complexL2Im ν f)
      have hs := norm_sq_coordinates ν f
      have hr' := sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr hr
      have hi' := sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr hi
      have hh : ‖complexL2OfPair ν (A (complexL2Re ν f), A (complexL2Im ν f))‖ ^ 2 ≤
          (‖A‖ * ‖f‖) ^ 2 := by
        rw [mul_pow, hs, mul_add]
        exact h.le.trans (add_le_add (by simpa only [mul_pow] using hr')
          (by simpa only [mul_pow] using hi'))
      exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp hh)

theorem re_complexify (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (f : Lp ℂ 2 ν) :
    complexL2Re ν (complexify ν A f) = A (complexL2Re ν f) :=
  complexL2Re_ofPair ν _

theorem im_complexify (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (f : Lp ℂ 2 ν) :
    complexL2Im ν (complexify ν A f) = A (complexL2Im ν f) :=
  complexL2Im_ofPair ν _

theorem complexify_ofReal (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (f : Lp ℝ 2 ν) :
    complexify ν A (realL2Complex ν f) = realL2Complex ν (A f) := by
  apply complexL2_ext ν
  · rw [re_complexify, complexL2Re_ofReal, complexL2Re_ofReal]
  · rw [im_complexify, complexL2Im_ofReal, complexL2Im_ofReal, map_zero]

/-- Compression to real L². On the complexification range this is its inverse. -/
def realPart (A : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  (complexL2Re ν).comp ((A.restrictScalars ℝ).comp (realL2Complex ν))

theorem realPart_complexify (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) :
    realPart ν (complexify ν A) = A := by
  apply ContinuousLinearMap.ext
  intro f
  exact (re_complexify ν A _).trans (congrArg A (complexL2Re_ofReal ν f))

/-- Complexification has exactly the original operator norm. -/
theorem norm_complexify (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) :
    ‖complexify ν A‖ = ‖A‖ := by
  apply le_antisymm
  · unfold complexify
    exact LinearMap.mkContinuous_norm_le _ (norm_nonneg A) _
  · apply A.opNorm_le_bound (norm_nonneg _) fun f => ?_
    rw [← norm_ofReal ν (A f), ← complexify_ofReal]
    exact ((complexify ν A).le_opNorm _).trans_eq (by rw [norm_ofReal])

/-- Complexification respects adjoints. -/
theorem complexify_star (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) :
    complexify ν (star A) = star (complexify ν A) := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro g
  simp only [ContinuousLinearMap.star_eq_adjoint]
  rw [ContinuousLinearMap.adjoint_inner_right]
  apply Complex.ext
  · simp only [complexL2_inner_re, re_complexify, im_complexify,
      ContinuousLinearMap.adjoint_inner_right]
  · simp only [complexL2_inner_im, re_complexify, im_complexify,
      ContinuousLinearMap.adjoint_inner_right]

/-- The real star algebra of bounded real L² operators embeds into the complex one. -/
def complexifyHom : (Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) →⋆ₐ[ℝ] (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) where
  toFun := complexify ν
  map_one' := by
    apply ContinuousLinearMap.ext
    intro f
    apply complexL2_ext ν <;>
      simp only [re_complexify, im_complexify, one_apply_eq_self]
  map_mul' A B := by
    apply ContinuousLinearMap.ext
    intro f
    apply complexL2_ext ν <;>
      simp only [re_complexify, im_complexify, mul_apply_eq_comp]
  map_zero' := by
    apply ContinuousLinearMap.ext
    intro f
    apply complexL2_ext ν <;>
      simp only [re_complexify, im_complexify, zero_apply, map_zero]
  map_add' A B := by
    apply ContinuousLinearMap.ext
    intro f
    apply complexL2_ext ν <;>
      simp only [re_complexify, im_complexify, add_apply, map_add]
  commutes' r := by
    apply ContinuousLinearMap.ext
    intro f
    apply complexL2_ext ν
    · change complexL2Re ν (complexify ν (r • 1) f) = complexL2Re ν ((r : ℂ) • f)
      rw [re_complexify, complexL2Re_smul]
      simp only [smul_apply, one_apply_eq_self, Complex.ofReal_re, Complex.ofReal_im,
        zero_smul, sub_zero]
    · change complexL2Im ν (complexify ν (r • 1) f) = complexL2Im ν ((r : ℂ) • f)
      rw [im_complexify, complexL2Im_smul]
      simp only [smul_apply, one_apply_eq_self, Complex.ofReal_re, Complex.ofReal_im,
        zero_smul, add_zero]
  map_star' := complexify_star ν

/-- The embedding is an isometry, so its range is closed. -/
theorem isometry_complexify : Isometry (complexify ν) := by
  apply AddMonoidHomClass.isometry_of_norm (complexifyHom ν)
  exact norm_complexify ν

/-- The complexifications form a closed real star subalgebra. -/
theorem isClosed_range_complexify :
    IsClosed (Set.range (complexify ν)) :=
  (isometry_complexify ν).isClosedEmbedding.isClosed_range

/-- Every real continuous multiplier of a complexified symmetric operator is real. -/
theorem cfc_mem_range (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (f : ℝ → ℝ) :
    cfc f (complexify ν A) ∈ Set.range (complexify ν) := by
  have hs : StarAlgebra.elemental ℝ (complexify ν A) ≤ (complexifyHom ν).range := by
    apply StarSubalgebra.topologicalClosure_minimal
    · exact StarAlgebra.adjoin_le (Set.singleton_subset_iff.mpr ⟨A, rfl⟩)
    · change IsClosed (Set.range (complexify ν))
      exact isClosed_range_complexify ν
  exact hs (cfc_mem_elemental f (complexify ν A))

/-- Positivity transfers to complex L². -/
theorem positive_complexify (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (hA : A.IsPositive) :
    (complexify ν A).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
  intro f
  have him : (inner ℂ (complexify ν A f) f).im = 0 := by
    simp only [complexL2_inner_im, re_complexify, im_complexify]
    have hh : inner ℝ (A (complexL2Re ν f)) (complexL2Im ν f) =
        inner ℝ (complexL2Re ν f) (A (complexL2Im ν f)) := hA.isSymmetric _ _
    rw [hh, real_inner_comm]
    exact sub_self _
  constructor
  · apply Complex.ext
    · rfl
    · exact him.symm
  · change 0 ≤ (inner ℂ (complexify ν A f) f).re
    rw [complexL2_inner_re, re_complexify, im_complexify]
    exact add_nonneg (hA.re_inner_nonneg_left _) (hA.re_inner_nonneg_left _)

/-- Complexification is injective. -/
theorem complexify_injective : Function.Injective (complexify ν) :=
  (isometry_complexify ν).injective

/-- Real compression preserves positive operators. -/
theorem positive_realPart (A : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (hA : A.IsPositive) :
    (realPart ν A).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff _).mpr
  constructor
  · intro f g
    change inner ℝ (complexL2Re ν (A (realL2Complex ν f))) g =
      inner ℝ f (complexL2Re ν (A (realL2Complex ν g)))
    have he : inner ℂ (A (realL2Complex ν f)) (realL2Complex ν g) =
        inner ℂ (realL2Complex ν f) (A (realL2Complex ν g)) := hA.isSymmetric _ _
    have hr := congrArg Complex.re he
    simpa only [complexL2_inner_re, complexL2Re_ofReal, complexL2Im_ofReal,
      inner_zero_left, inner_zero_right, add_zero] using hr
  · intro f
    change 0 ≤ inner ℝ (complexL2Re ν (A (realL2Complex ν f))) f
    have hp := hA.re_inner_nonneg_left (realL2Complex ν f)
    change 0 ≤ (inner ℂ (A (realL2Complex ν f)) (realL2Complex ν f)).re at hp
    simpa only [complexL2_inner_re, complexL2Re_ofReal, complexL2Im_ofReal,
      inner_zero_right, add_zero] using hp

/-- Real continuous functional calculus. Self-adjointness and continuity are
part of its carrier, so the complex calculus never evaluates an unsupported input. -/
def calculus (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (hA : IsSelfAdjoint A)
    (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ (complexify ν A))) :
    Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  realPart ν (cfcHom (hA.map (complexifyHom ν)) ⟨fun x => f x, hf.domRestrict⟩)

/-- The restriction has the original complex multiplier as its complexification. -/
theorem complexify_calculus (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (hA : IsSelfAdjoint A)
    (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ (complexify ν A))) :
    complexify ν (calculus ν A hA f hf) = cfc f (complexify ν A) := by
  have he : calculus ν A hA f hf = realPart ν (cfc f (complexify ν A)) := by
    have hc : IsSelfAdjoint (complexify ν A) := hA.map (complexifyHom ν)
    rw [cfc_apply f _ hc hf]
    rfl
  obtain ⟨B, hB⟩ := cfc_mem_range ν A f
  rw [he, ← hB, realPart_complexify]

/-- The restricted real calculus inherits every spectral supremum bound. -/
theorem norm_calculus_le (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (hA : IsSelfAdjoint A)
    (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ (complexify ν A)))
    {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x ∈ spectrum ℝ (complexify ν A), |f x| ≤ C) :
    ‖calculus ν A hA f hf‖ ≤ C := by
  rw [← norm_complexify ν, complexify_calculus]
  exact norm_cfc_le hC (fun x hx => by change |f x| ≤ C; exact h x hx)

/-- The real calculus fixes the identity function. -/
theorem calculus_id (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (hA : IsSelfAdjoint A) :
    calculus ν A hA id continuous_id.continuousOn = A := by
  apply complexify_injective ν
  rw [complexify_calculus]
  exact cfc_id ℝ (complexify ν A) (hA.map (complexifyHom ν))

/-- The calculus respects products of continuous spectral functions. -/
theorem calculus_mul (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (hA : IsSelfAdjoint A)
    (f g : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ (complexify ν A)))
    (hg : ContinuousOn g (spectrum ℝ (complexify ν A))) :
    calculus ν A hA (fun x => f x * g x) (hf.mul hg) =
      calculus ν A hA f hf * calculus ν A hA g hg := by
  apply complexify_injective ν
  rw [show complexify ν (calculus ν A hA f hf * calculus ν A hA g hg) =
    complexify ν (calculus ν A hA f hf) * complexify ν (calculus ν A hA g hg) from
      (complexifyHom ν).map_mul _ _]
  simp only [complexify_calculus]
  exact cfc_mul f g _ hf hg

/-- Equal functions on the actual spectrum give the same real operator. -/
theorem calculus_congr (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (hA : IsSelfAdjoint A)
    (f g : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ (complexify ν A)))
    (hg : ContinuousOn g (spectrum ℝ (complexify ν A)))
    (h : ∀ x ∈ spectrum ℝ (complexify ν A), f x = g x) :
    calculus ν A hA f hf = calculus ν A hA g hg := by
  apply complexify_injective ν
  simp only [complexify_calculus]
  exact cfc_congr h

/-- A nonnegative continuous spectral function produces a positive real operator. -/
theorem positive_calculus (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (hA : IsSelfAdjoint A)
    (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ (complexify ν A)))
    (h : ∀ x ∈ spectrum ℝ (complexify ν A), 0 ≤ f x) :
    (calculus ν A hA f hf).IsPositive := by
  have he : calculus ν A hA f hf = realPart ν (cfc f (complexify ν A)) := by
    have hc : IsSelfAdjoint (complexify ν A) := hA.map (complexifyHom ν)
    rw [cfc_apply f _ hc hf]
    rfl
  rw [he]
  apply positive_realPart ν
  exact ContinuousLinearMap.nonneg_iff_isPositive.mp (cfc_nonneg h)

/-- Positive square root of a bounded positive operator on real L². -/
def sqrt (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (hA : A.IsPositive) :
    Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  calculus ν A hA.isSelfAdjoint Real.sqrt Real.continuous_sqrt.continuousOn

/-- The real square root is positive. -/
theorem sqrt_positive (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (hA : A.IsPositive) :
    (sqrt ν A hA).IsPositive :=
  positive_calculus ν A hA.isSelfAdjoint Real.sqrt _ (fun _ _ => Real.sqrt_nonneg _)

/-- The real positive square root squares to the given positive operator. -/
theorem sqrt_mul_self (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (hA : A.IsPositive) :
    sqrt ν A hA * sqrt ν A hA = A := by
  rw [sqrt, ← calculus_mul]
  calc
    _ = calculus ν A hA.isSelfAdjoint id continuous_id.continuousOn :=
      calculus_congr ν A hA.isSelfAdjoint _ _ _ _ (fun x hx => by
        have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg
          (ContinuousLinearMap.nonneg_iff_isPositive.mpr (positive_complexify ν A hA)) hx
        exact Real.mul_self_sqrt hx0)
    _ = A := calculus_id ν A hA.isSelfAdjoint

/-- Squared norm of the real square root, with no discrete-spectrum assumption. -/
theorem sqrt_norm_sq (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (hA : A.IsPositive)
    (f : Lp ℝ 2 ν) : ‖sqrt ν A hA f‖ ^ 2 = inner ℝ (A f) f := by
  have hs : inner ℝ (sqrt ν A hA (sqrt ν A hA f)) f =
      inner ℝ (sqrt ν A hA f) (sqrt ν A hA f) := (sqrt_positive ν A hA).isSymmetric _ _
  have he : sqrt ν A hA (sqrt ν A hA f) = A f :=
    congrArg (fun B : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν => B f) (sqrt_mul_self ν A hA)
  rw [he, real_inner_self_eq_norm_sq] at hs
  exact hs.symm

/-- The restricted calculus respects sums. -/
theorem calculus_add (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (hA : IsSelfAdjoint A)
    (f g : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ (complexify ν A)))
    (hg : ContinuousOn g (spectrum ℝ (complexify ν A))) :
    calculus ν A hA (fun x => f x + g x) (hf.add hg) =
      calculus ν A hA f hf + calculus ν A hA g hg := by
  apply complexify_injective ν
  rw [show complexify ν (calculus ν A hA f hf + calculus ν A hA g hg) =
    complexify ν (calculus ν A hA f hf) + complexify ν (calculus ν A hA g hg) from
      (complexifyHom ν).map_add _ _]
  simp only [complexify_calculus]
  exact cfc_add (a := complexify ν A) (f := f) (g := g) hf hg

/-- Constants in the real calculus are the corresponding scalar multiples of the identity. -/
theorem calculus_const (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (hA : IsSelfAdjoint A) (r : ℝ) :
    calculus ν A hA (fun _ => r) continuous_const.continuousOn = r • 1 := by
  apply complexify_injective ν
  rw [complexify_calculus]
  have hc : IsSelfAdjoint (complexify ν A) := hA.map (complexifyHom ν)
  rw [cfc_const r _ hc]
  exact ((complexifyHom ν).commutes r).symm

/-- A commuting real operator commutes with every continuous spectral function. -/
theorem calculus_commute (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (hA : IsSelfAdjoint A)
    (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ (complexify ν A)))
    (B : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (hc : Commute A B) :
    Commute (calculus ν A hA f hf) B := by
  have hm : Commute (complexify ν A) (complexify ν B) := hc.map (complexifyHom ν)
  have hh := hm.cfc_real f
  apply complexify_injective ν
  simpa only [show ∀ C D, complexify ν (C * D) = complexify ν C * complexify ν D from
    (complexifyHom ν).map_mul, complexify_calculus] using hh.eq

/-- Square roots of commuting positive real operators commute. -/
theorem sqrt_commute (A B : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν)
    (hA : A.IsPositive) (hB : B.IsPositive) (hc : Commute A B) :
    Commute (sqrt ν A hA) (sqrt ν B hB) := by
  have hh := calculus_commute ν B hB.isSelfAdjoint Real.sqrt
    Real.continuous_sqrt.continuousOn A hc.symm
  exact calculus_commute ν A hA.isSelfAdjoint Real.sqrt
    Real.continuous_sqrt.continuousOn _ hh.symm

/-- Commuting positive real L² operators have a positive product. -/
theorem positive_mul (A B : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν)
    (hA : A.IsPositive) (hB : B.IsPositive) (hc : Commute A B) :
    (A * B).IsPositive := by
  have hh : (complexify ν A * complexify ν B).IsPositive :=
    ContinuousLinearMap.nonneg_iff_isPositive.mp
      ((hc.map (complexifyHom ν)).mul_nonneg
        (ContinuousLinearMap.nonneg_iff_isPositive.mpr (positive_complexify ν A hA))
        (ContinuousLinearMap.nonneg_iff_isPositive.mpr (positive_complexify ν B hB)))
  have he : complexify ν (A * B) = complexify ν A * complexify ν B :=
    (complexifyHom ν).map_mul A B
  rw [← he] at hh
  have hr := positive_realPart ν _ hh
  rw [realPart_complexify] at hr
  exact hr

/-- A symmetric injective bounded real operator has dense range. -/
theorem denseRange_of_selfAdjoint_injective (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν)
    (hA : IsSelfAdjoint A) (hi : Function.Injective A) : DenseRange A := by
  have hadj : A.adjoint = A := by simpa only [ContinuousLinearMap.star_eq_adjoint] using hA.star_eq
  have he := ContinuousLinearMap.orthogonal_ker A
  rw [hadj, LinearMap.ker_eq_bot.mpr hi, Submodule.bot_orthogonal_eq_top] at he
  rw [denseRange_iff_closure_range]
  change closure (A.range : Set (Lp ℝ 2 ν)) = Set.univ
  rw [← Submodule.topologicalClosure_coe, ← he]
  rfl

/-- The bilinear square-root identity. -/
theorem sqrt_inner (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (hA : A.IsPositive)
    (f g : Lp ℝ 2 ν) :
    inner ℝ (sqrt ν A hA f) (sqrt ν A hA g) = inner ℝ (A f) g := by
  have hh : inner ℝ (sqrt ν A hA (sqrt ν A hA f)) g =
      inner ℝ (sqrt ν A hA f) (sqrt ν A hA g) := (sqrt_positive ν A hA).isSymmetric _ _
  have he := congrArg (fun B : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν => B f) (sqrt_mul_self ν A hA)
  exact hh.symm.trans (congrArg (fun x => inner ℝ x g) he)

/-- The positive real square root is unique. -/
theorem sqrt_unique (A B : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν)
    (hA : A.IsPositive) (hB : B.IsPositive) (he : B * B = A) :
    B = sqrt ν A hA := by
  apply complexify_injective ν
  have hsq : complexify ν B * complexify ν B = complexify ν A := by
    have hh : complexify ν (B * B) = complexify ν B * complexify ν B :=
      (complexifyHom ν).map_mul B B
    exact hh.symm.trans (congrArg (complexify ν) he)
  have hroot : CFC.sqrt (complexify ν A) = complexify ν B :=
    CFC.sqrt_unique hsq
      (ContinuousLinearMap.nonneg_iff_isPositive.mpr (positive_complexify ν B hB))
  have hs : complexify ν (sqrt ν A hA) * complexify ν (sqrt ν A hA) = complexify ν A := by
    have hh : complexify ν (sqrt ν A hA * sqrt ν A hA) =
        complexify ν (sqrt ν A hA) * complexify ν (sqrt ν A hA) :=
      (complexifyHom ν).map_mul _ _
    exact hh.symm.trans (congrArg (complexify ν) (sqrt_mul_self ν A hA))
  exact hroot.symm.trans (CFC.sqrt_unique hs
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr
      (positive_complexify ν _ (sqrt_positive ν A hA))))

/-- Continuous functions on the unit interval act on a self-adjoint real operator.
The extension to ℝ is the canonical nearest-point retraction to the interval. -/
def intervalHom (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (hA : IsSelfAdjoint A) :
    C(Set.Icc (0 : ℝ) 1, ℝ) →ₐ[ℝ] (Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) where
  toFun f := calculus ν A hA (Set.IccExtend zero_le_one f)
    (f.continuous.comp continuous_projIcc).continuousOn
  map_one' := by
    change calculus ν A hA (fun _ => 1) _ = 1
    rw [calculus_const, one_smul]
  map_mul' f g := calculus_mul ν A hA _ _ _ _
  map_zero' := by
    change calculus ν A hA (fun _ => 0) _ = 0
    rw [calculus_const]
    exact zero_smul ℝ (1 : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν)
  map_add' f g := calculus_add ν A hA _ _ _ _
  commutes' r := calculus_const ν A hA r

/-- A pointwise scalar bound on the compact spectral parameter is an operator bound. -/
theorem norm_intervalHom_le (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (hA : IsSelfAdjoint A)
    (f : C(Set.Icc (0 : ℝ) 1, ℝ)) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ u, |f u| ≤ C) : ‖intervalHom ν A hA f‖ ≤ C :=
  norm_calculus_le ν A hA _ (f.continuous.comp continuous_projIcc).continuousOn hC (fun x _ => hf (Set.projIcc 0 1 zero_le_one x))

/-- Positivity also transfers from the compact interval. -/
theorem positive_intervalHom (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (hA : IsSelfAdjoint A)
    (f : C(Set.Icc (0 : ℝ) 1, ℝ)) (hf : ∀ u, 0 ≤ f u) :
    (intervalHom ν A hA f).IsPositive :=
  positive_calculus ν A hA _ (f.continuous.comp continuous_projIcc).continuousOn (fun x _ => hf (Set.projIcc 0 1 zero_le_one x))

/-- Positive contractions have their real spectrum in the full closed unit interval. -/
theorem spectrum_subset_unitInterval (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν)
    (hA : A.IsPositive) (hn : ‖A‖ ≤ 1) :
    spectrum ℝ (complexify ν A) ⊆ Set.Icc (0 : ℝ) 1 := by
  intro x hx
  have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr (positive_complexify ν A hA)) hx
  have hx1 : |x| ≤ ‖complexify ν A‖ := by
    have hh := spectrum.norm_le_norm_mul_of_mem hx
    have h1 : ‖(1 : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    exact hh.trans (by nlinarith [norm_nonneg (complexify ν A)])
  rw [norm_complexify, abs_of_nonneg hx0] at hx1
  exact ⟨hx0, hx1.trans hn⟩

/-- The coordinate function acts as the original positive contraction. -/
theorem intervalHom_coordinate (A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν)
    (hA : A.IsPositive) (hn : ‖A‖ ≤ 1) :
    intervalHom ν A hA.isSelfAdjoint ⟨Subtype.val, continuous_subtype_val⟩ = A := by
  change calculus ν A hA.isSelfAdjoint (Set.IccExtend zero_le_one Subtype.val)
    (continuous_subtype_val.comp continuous_projIcc).continuousOn = A
  apply Eq.trans (b := calculus ν A hA.isSelfAdjoint id continuous_id.continuousOn)
    _ (calculus_id ν A hA.isSelfAdjoint)
  apply calculus_congr
  intro x hx
  exact Set.IccExtend_of_mem zero_le_one _ (spectrum_subset_unitInterval ν A hA hn hx)

end Riesz2.RealL2ContinuousCalculus
