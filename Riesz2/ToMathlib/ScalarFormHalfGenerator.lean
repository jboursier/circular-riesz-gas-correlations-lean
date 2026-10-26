/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.RealL2ContinuousCalculus
public import Riesz2.ToMathlib.ScalarFormResolvent
public import Riesz2.Frozen.IsNeumannRealization
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The half-generator on the whole closed scalar form domain

The polar isometry of the form embedding is constructed on its dense adjoint
range and extended in the complete form norm. The complementary bounded
square root then gives the half-generator on every element of the literal
form domain. Infrastructure for the proof of Proposition 5.15.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set

namespace Riesz2.ScalarFormHalfGenerator

open ScalarFormHilbert

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}
  (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)

/-- The unit-shift solution is exactly the adjoint of the form embedding. -/
theorem shiftedSolution_eq_adjoint :
    shiftedSolution Q hQ 1 zero_lt_one = (value Q hQ).adjoint := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℝ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_left, inner_eq]
  have he := shiftedSolution_solves Q hQ 1 zero_lt_one f w
  simpa only [one_mul, add_comm] using he

/-- The generator domain is dense in the complete form norm. -/
theorem denseRange_shiftedSolution : DenseRange (shiftedSolution Q hQ 1 zero_lt_one) := by
  rw [shiftedSolution_eq_adjoint, denseRange_iff_closure_range]
  change closure (((value Q hQ).adjoint).range : Set (Space Q hQ)) = univ
  rw [← Submodule.topologicalClosure_coe, ← ContinuousLinearMap.orthogonal_ker,
    LinearMap.ker_eq_bot.mpr (value_injective Q hQ), Submodule.bot_orthogonal_eq_top]
  rfl

/-- The norm used for extending the polar isometry. -/
theorem polar_norm (f : Lp ℝ 2 ν) :
    ‖RealL2ContinuousCalculus.sqrt ν (ScalarFormResolvent.resolvent Q hQ 1 zero_lt_one)
      (ScalarFormResolvent.isPositive Q hQ 1 zero_lt_one) f‖ =
      ‖shiftedSolution Q hQ 1 zero_lt_one f‖ := by
  have hs := RealL2ContinuousCalculus.sqrt_norm_sq ν _
    (ScalarFormResolvent.isPositive Q hQ 1 zero_lt_one) f
  have he := shiftedSolution_solves Q hQ 1 zero_lt_one f
    (shiftedSolution Q hQ 1 zero_lt_one f)
  rw [real_inner_self_eq_norm_sq, one_mul] at he
  have hn := norm_sq Q hQ (shiftedSolution Q hQ 1 zero_lt_one f)
  have hh : ‖shiftedSolution Q hQ 1 zero_lt_one f‖ ^ 2 =
      inner ℝ f (ScalarFormResolvent.resolvent Q hQ 1 zero_lt_one f) :=
    hn.trans ((add_comm _ _).trans he)
  rw [real_inner_comm] at hs
  nlinarith [norm_nonneg (shiftedSolution Q hQ 1 zero_lt_one f),
    norm_nonneg (RealL2ContinuousCalculus.sqrt ν _
      (ScalarFormResolvent.isPositive Q hQ 1 zero_lt_one) f)]

/-- Polar isometry of the injective, densely ranged form embedding. -/
def polar : Space Q hQ →ₗᵢ[ℝ] Lp ℝ 2 ν :=
  (RealL2ContinuousCalculus.sqrt ν (ScalarFormResolvent.resolvent Q hQ 1 zero_lt_one)
    (ScalarFormResolvent.isPositive Q hQ 1 zero_lt_one)).toLinearMap.extendOfIsometry
    (e := (shiftedSolution Q hQ 1 zero_lt_one).toLinearMap)
    (denseRange_shiftedSolution Q hQ) (polar_norm Q hQ)

/-- On the generator domain the polar isometry is the bounded square root. -/
theorem polar_shiftedSolution (f : Lp ℝ 2 ν) :
    polar Q hQ (shiftedSolution Q hQ 1 zero_lt_one f) =
      RealL2ContinuousCalculus.sqrt ν (ScalarFormResolvent.resolvent Q hQ 1 zero_lt_one)
        (ScalarFormResolvent.isPositive Q hQ 1 zero_lt_one) f :=
  LinearMap.extendOfIsometry_eq _ _ _ f

/-- The polar factorization holds on the entire form domain. -/
theorem sqrt_polar (u : Space Q hQ) :
    RealL2ContinuousCalculus.sqrt ν (ScalarFormResolvent.resolvent Q hQ 1 zero_lt_one)
      (ScalarFormResolvent.isPositive Q hQ 1 zero_lt_one) (polar Q hQ u) = value Q hQ u := by
  refine (denseRange_shiftedSolution Q hQ).induction_on u
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro f
  rw [polar_shiftedSolution]
  exact congrArg (fun A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν => A f)
    (RealL2ContinuousCalculus.sqrt_mul_self ν _
      (ScalarFormResolvent.isPositive Q hQ 1 zero_lt_one))

/-- The scalar half-generator on the full form domain, with the form norm. -/
def halfGenerator : Space Q hQ →L[ℝ] Lp ℝ 2 ν :=
  (RealL2ContinuousCalculus.sqrt ν (1 - ScalarFormResolvent.resolvent Q hQ 1 zero_lt_one)
    (ScalarFormResolvent.transform_complement_positive Q hQ)).comp (polar Q hQ).toContinuousLinearMap

/-- Full form-domain square-root identity, the proof of Proposition 5.15. -/
theorem halfGenerator_norm_sq (u : Space Q hQ) :
    ‖halfGenerator Q hQ u‖ ^ 2 = Q.2 (equiv Q hQ u) (equiv Q hQ u) := by
  have he := RealL2ContinuousCalculus.sqrt_norm_sq ν _
    (ScalarFormResolvent.transform_complement_positive Q hQ) (polar Q hQ u)
  have ht := RealL2ContinuousCalculus.sqrt_norm_sq ν _
    (ScalarFormResolvent.isPositive Q hQ 1 zero_lt_one) (polar Q hQ u)
  rw [sqrt_polar] at ht
  simp only [sub_apply, one_apply_eq_self, inner_sub_left, real_inner_self_eq_norm_sq,
    (polar Q hQ).norm_map] at he
  change ‖halfGenerator Q hQ u‖ ^ 2 = _ at he
  have hn := norm_sq Q hQ u
  change ‖u‖ ^ 2 = ‖value Q hQ u‖ ^ 2 + _ at hn
  linarith

/-- Norm form of the identity on every element of the scalar domain,
the proof of Proposition 5.15. -/
theorem halfGenerator_norm (u : Q.1) :
    ‖halfGenerator Q hQ ((equiv Q hQ).symm u)‖ = Real.sqrt (Q.2 u u) := by
  have he := halfGenerator_norm_sq Q hQ ((equiv Q hQ).symm u)
  simpa only [LinearEquiv.apply_symm_apply, Real.sqrt_sq (norm_nonneg _)] using
    congrArg Real.sqrt he

local notation "T" => ScalarFormResolvent.resolvent Q hQ 1 zero_lt_one
local notation "S" => RealL2ContinuousCalculus.sqrt ν T
  (ScalarFormResolvent.isPositive Q hQ 1 zero_lt_one)
local notation "U" => RealL2ContinuousCalculus.sqrt ν (1 - T)
  (ScalarFormResolvent.transform_complement_positive Q hQ)

/-- Both bounded square-root factors commute. -/
theorem roots_commute : Commute S U := by
  apply RealL2ContinuousCalculus.sqrt_commute
  exact (Commute.one_right T).sub_right (Commute.refl T)

/-- The polar isometry is onto ambient L². -/
theorem polar_surjective : Function.Surjective (polar Q hQ) := by
  have hinj : Function.Injective S := by
    intro f g hfg
    apply ScalarFormResolvent.injective Q hQ 1 zero_lt_one
    have he := congrArg S hfg
    have hs := RealL2ContinuousCalculus.sqrt_mul_self ν T
      (ScalarFormResolvent.isPositive Q hQ 1 zero_lt_one)
    have hf := congrArg (fun A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν => A f) hs
    have hg := congrArg (fun A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν => A g) hs
    exact hf.symm.trans (he.trans hg)
  have hd := RealL2ContinuousCalculus.denseRange_of_selfAdjoint_injective ν S
    (RealL2ContinuousCalculus.sqrt_positive ν T
      (ScalarFormResolvent.isPositive Q hQ 1 zero_lt_one)).isSelfAdjoint hinj
  intro f
  have hf : f ∈ closure (Set.range (polar Q hQ)) := by
    apply closure_mono ?_ (hd f)
    rintro _ ⟨g, rfl⟩
    exact ⟨shiftedSolution Q hQ 1 zero_lt_one g, polar_shiftedSolution Q hQ g⟩
  rw [(polar Q hQ).isometry.isClosedEmbedding.isClosed_range.closure_eq] at hf
  exact hf

/-- Full bilinear representation of the form by the half-generator,
the proof of Proposition 5.15. -/
theorem halfGenerator_pair (u v : Space Q hQ) :
    inner ℝ (halfGenerator Q hQ u) (halfGenerator Q hQ v) =
      Q.2 (equiv Q hQ u) (equiv Q hQ v) := by
  change inner ℝ (U (polar Q hQ u)) (U (polar Q hQ v)) = _
  rw [RealL2ContinuousCalculus.sqrt_inner]
  simp only [sub_apply, one_apply_eq_self, inner_sub_left]
  rw [← RealL2ContinuousCalculus.sqrt_inner ν T
    (ScalarFormResolvent.isPositive Q hQ 1 zero_lt_one), sqrt_polar, sqrt_polar,
    (polar Q hQ).inner_map_map, inner_eq]
  ring

/-- The constructed half-generator is symmetric on its full scalar domain. -/
theorem halfGenerator_symmetric (u v : Space Q hQ) :
    inner ℝ (halfGenerator Q hQ u) (value Q hQ v) =
      inner ℝ (value Q hQ u) (halfGenerator Q hQ v) := by
  rw [← sqrt_polar Q hQ u, ← sqrt_polar Q hQ v]
  change inner ℝ (U (polar Q hQ u)) (S (polar Q hQ v)) =
    inner ℝ (S (polar Q hQ u)) (U (polar Q hQ v))
  have hs (f g : Lp ℝ 2 ν) : inner ℝ (S f) g = inner ℝ f (S g) :=
    (RealL2ContinuousCalculus.sqrt_positive ν T
      (ScalarFormResolvent.isPositive Q hQ 1 zero_lt_one)).isSymmetric f g
  have hu (f g : Lp ℝ 2 ν) : inner ℝ (U f) g = inner ℝ f (U g) :=
    (RealL2ContinuousCalculus.sqrt_positive ν (1 - T)
      (ScalarFormResolvent.transform_complement_positive Q hQ)).isSymmetric f g
  calc
    _ = inner ℝ (S (U (polar Q hQ u))) (polar Q hQ v) := (hs _ _).symm
    _ = inner ℝ (U (S (polar Q hQ u))) (polar Q hQ v) := by
      have he := congrArg (fun A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν => A (polar Q hQ u))
        (roots_commute Q hQ).eq
      exact congrArg (fun z => inner ℝ z (polar Q hQ v)) he
    _ = _ := hu _ _

/-- Nonnegativity holds on the whole domain, including the nullspace. -/
theorem halfGenerator_nonneg (u : Space Q hQ) :
    0 ≤ inner ℝ (halfGenerator Q hQ u) (value Q hQ u) := by
  rw [← sqrt_polar Q hQ u]
  have hs (f g : Lp ℝ 2 ν) : inner ℝ (S f) g = inner ℝ f (S g) :=
    (RealL2ContinuousCalculus.sqrt_positive ν T
      (ScalarFormResolvent.isPositive Q hQ 1 zero_lt_one)).isSymmetric f g
  change 0 ≤ inner ℝ (U (polar Q hQ u)) (S (polar Q hQ u))
  rw [← hs]
  exact (RealL2ContinuousCalculus.positive_mul ν S U
    (RealL2ContinuousCalculus.sqrt_positive ν T
      (ScalarFormResolvent.isPositive Q hQ 1 zero_lt_one))
    (RealL2ContinuousCalculus.sqrt_positive ν (1 - T)
      (ScalarFormResolvent.transform_complement_positive Q hQ))
    (roots_commute Q hQ)).re_inner_nonneg_left (polar Q hQ u)

/-- Spectral identification on the dense generator core: the factors are
`sqrt(1-T) sqrt(T)` rather than an arbitrary form-space isometry. -/
theorem halfGenerator_shiftedSolution (f : Lp ℝ 2 ν) :
    halfGenerator Q hQ (shiftedSolution Q hQ 1 zero_lt_one f) = U (S f) := by
  change U (polar Q hQ (shiftedSolution Q hQ 1 zero_lt_one f)) = _
  rw [polar_shiftedSolution]

/-- The half-generator as an ambient partial operator has exactly the form domain. -/
def operator : Lp ℝ 2 ν →ₗ.[ℝ] Lp ℝ 2 ν where
  domain := Q.1
  toFun := (halfGenerator Q hQ).toLinearMap.comp (equiv Q hQ).symm.toLinearMap

/-- The two bounded square-root squares partition the identity. -/
theorem roots_partition (f : Lp ℝ 2 ν) : S (S f) + U (U f) = f := by
  have hs := congrArg (fun A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν => A f)
    (RealL2ContinuousCalculus.sqrt_mul_self ν T (ScalarFormResolvent.isPositive Q hQ 1 zero_lt_one))
  have hu := congrArg (fun A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν => A f)
    (RealL2ContinuousCalculus.sqrt_mul_self ν (1 - T)
      (ScalarFormResolvent.transform_complement_positive Q hQ))
  change S (S f) = T f at hs
  change U (U f) = f - T f at hu
  rw [hs, hu]
  module

/-- The full half-generator graph has the bounded parametrization `(Sx,Ux)`. -/
theorem mem_operator_graph_iff (f a : Lp ℝ 2 ν) :
    (f, a) ∈ (operator Q hQ).graph ↔ ∃ x : Lp ℝ 2 ν, S x = f ∧ U x = a := by
  constructor
  · intro hf
    obtain ⟨u, hu, ha⟩ := (LinearPMap.mem_graph_iff (operator Q hQ)).mp hf
    let v := (equiv Q hQ).symm u
    refine ⟨polar Q hQ v, ?_, ?_⟩
    · exact (sqrt_polar Q hQ v).trans hu
    · exact ha
  · rintro ⟨x, hx, ha⟩
    obtain ⟨v, hv⟩ := polar_surjective Q hQ x
    apply (LinearPMap.mem_graph_iff (operator Q hQ)).mpr
    refine ⟨equiv Q hQ v, ?_, ?_⟩
    · exact (sqrt_polar Q hQ v).symm.trans ((congrArg S hv).trans hx)
    · change halfGenerator Q hQ ((equiv Q hQ).symm (equiv Q hQ v)) = a
      rw [LinearEquiv.symm_apply_apply]
      change U (polar Q hQ v) = a
      exact (congrArg U hv).trans ha

/-- The full half-generator graph is the kernel of the bounded relation `Uf=Sa`. -/
theorem mem_operator_graph_iff_relation (f a : Lp ℝ 2 ν) :
    (f, a) ∈ (operator Q hQ).graph ↔ U f = S a := by
  rw [mem_operator_graph_iff]
  constructor
  · rintro ⟨x, rfl, rfl⟩
    exact (congrArg (fun A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν => A x) (roots_commute Q hQ).eq).symm
  · intro h
    refine ⟨S f + U a, ?_, ?_⟩
    · rw [map_add]
      have hc := congrArg (fun A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν => A a) (roots_commute Q hQ).eq
      change S (U a) = U (S a) at hc
      rw [hc, ← h]
      exact roots_partition Q hQ f
    · rw [map_add]
      have hc := congrArg (fun A : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν => A f) (roots_commute Q hQ).eq
      change S (U f) = U (S f) at hc
      rw [← hc, h]
      exact roots_partition Q hQ a

/-- The full half-generator graph equals its Hilbert-space adjoint graph. -/
theorem operator_graph_adjoint : (operator Q hQ).graph.adjoint = (operator Q hQ).graph := by
  have hs (f g : Lp ℝ 2 ν) : inner ℝ (S f) g = inner ℝ f (S g) :=
    (RealL2ContinuousCalculus.sqrt_positive ν T
      (ScalarFormResolvent.isPositive Q hQ 1 zero_lt_one)).isSymmetric f g
  have hu (f g : Lp ℝ 2 ν) : inner ℝ (U f) g = inner ℝ f (U g) :=
    (RealL2ContinuousCalculus.sqrt_positive ν (1 - T)
      (ScalarFormResolvent.transform_complement_positive Q hQ)).isSymmetric f g
  apply le_antisymm
  · rintro ⟨f, a⟩ hp
    apply (mem_operator_graph_iff_relation Q hQ f a).mpr
    apply ext_inner_left ℝ
    intro x
    have hmem : (S x, U x) ∈ (operator Q hQ).graph :=
      (mem_operator_graph_iff Q hQ _ _).mpr ⟨x, rfl, rfl⟩
    have he := (Submodule.mem_adjoint_iff _ _).mp hp _ _ hmem
    change inner ℝ (U x) f - inner ℝ (S x) a = 0 at he
    rw [hu, hs] at he
    exact sub_eq_zero.mp he
  · rintro ⟨f, a⟩ hp
    have hr := (mem_operator_graph_iff_relation Q hQ f a).mp hp
    apply (Submodule.mem_adjoint_iff _ _).mpr
    intro b d hbd
    obtain ⟨x, hx, hd⟩ := (mem_operator_graph_iff Q hQ b d).mp hbd
    change inner ℝ d f - inner ℝ b a = 0
    rw [← hx, ← hd, hu, hs, hr, sub_self]

/-- The positive square root is self-adjoint on exactly the whole form domain,
the proof of Proposition 5.15. -/
theorem operator_selfAdjoint : IsSelfAdjoint (operator Q hQ) := by
  have hd : Dense ((operator Q hQ).domain : Set (Lp ℝ 2 ν)) := by
    intro f
    apply closure_mono ?_ (hQ.1 f)
    rintro _ ⟨u, rfl⟩
    exact u.property
  change (operator Q hQ).adjoint = operator Q hQ
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint hd, operator_graph_adjoint]

/-- Squaring the self-adjoint half-generator gives exactly the variational
scalar generator graph of the form, in both directions.
See the proof of Proposition 5.15 in the paper. -/
theorem square_graph_iff (f a : Lp ℝ 2 ν) :
    (∃ g : Lp ℝ 2 ν, (f, g) ∈ (operator Q hQ).graph ∧ (g, a) ∈ (operator Q hQ).graph) ↔
      ∃ u : Q.1, u.val = f ∧ ∀ v : Q.1, Q.2 u v = inner ℝ a v.val := by
  constructor
  · rintro ⟨g, hfg, hga⟩
    obtain ⟨u, hu, hug⟩ := (LinearPMap.mem_graph_iff (operator Q hQ)).mp hfg
    obtain ⟨w, hw, hwa⟩ := (LinearPMap.mem_graph_iff (operator Q hQ)).mp hga
    refine ⟨u, hu, fun v => ?_⟩
    have he := halfGenerator_pair Q hQ ((equiv Q hQ).symm u) ((equiv Q hQ).symm v)
    have hs := halfGenerator_symmetric Q hQ ((equiv Q hQ).symm w) ((equiv Q hQ).symm v)
    change inner ℝ (halfGenerator Q hQ ((equiv Q hQ).symm u))
      (halfGenerator Q hQ ((equiv Q hQ).symm v)) = Q.2 u v at he
    change halfGenerator Q hQ ((equiv Q hQ).symm u) = g at hug
    change halfGenerator Q hQ ((equiv Q hQ).symm w) = a at hwa
    change inner ℝ (halfGenerator Q hQ ((equiv Q hQ).symm w)) v.val =
      inner ℝ w.val (halfGenerator Q hQ ((equiv Q hQ).symm v)) at hs
    rw [hug] at he
    rw [hwa, hw] at hs
    exact he.symm.trans hs.symm
  · rintro ⟨u, hu, hea⟩
    let z := (equiv Q hQ).symm u
    refine ⟨halfGenerator Q hQ z, ?_, ?_⟩
    · apply (LinearPMap.mem_graph_iff (operator Q hQ)).mpr
      exact ⟨u, hu, rfl⟩
    · rw [← operator_graph_adjoint]
      apply (Submodule.mem_adjoint_iff _ _).mpr
      intro b d hbd
      obtain ⟨v, hv, hvd⟩ := (LinearPMap.mem_graph_iff (operator Q hQ)).mp hbd
      change Q.1 at v
      have he := halfGenerator_pair Q hQ ((equiv Q hQ).symm v) z
      change inner ℝ (halfGenerator Q hQ ((equiv Q hQ).symm v))
        (halfGenerator Q hQ z) = Q.2 v u at he
      change halfGenerator Q hQ ((equiv Q hQ).symm v) = d at hvd
      rw [hvd, hQ.2.1, hea v, hv] at he
      change inner ℝ d (halfGenerator Q hQ z) - inner ℝ b a = 0
      exact sub_eq_zero.mpr (he.trans (real_inner_comm _ _))

/-- The abstract full-domain identity is the literal gradient norm for every
intrinsic Neumann realization, the proof of Proposition 5.15. -/
theorem norm_eq_gradient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] {ρ : Measure E}
    (P : ScalarFormData ρ) (hP : IsClosedScalarDirichletForm P)
    (Ω : Set E) (hreal : IsNeumannRealization Ω P) (u : P.1) (g : Lp E 2 ρ)
    (hg : (u.val, g) ∈ neumannSobolevGraph ρ Ω) :
    ‖halfGenerator P hP ((equiv P hP).symm u)‖ = ‖g‖ := by
  rw [halfGenerator_norm, hreal.2.2 u u g g hg hg, real_inner_self_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg _)]

end Riesz2.ScalarFormHalfGenerator
