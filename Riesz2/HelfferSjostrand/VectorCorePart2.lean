/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.VectorCore
public import Riesz2.HelfferSjostrand.IntrinsicIntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
public import Riesz2.ToMathlib.CutoffApproximation
public import Riesz2.ToMathlib.VectorRadialCompositionPart2
public import Mathlib.MeasureTheory.Function.Holder

/-!
# Compact localization for the natural vector core

Approximation steps for Subsection 3.1, using the original
intrinsic scalar jets and the Gibbs potential. Compact cutoffs converging
to one are constructed from the scalar form core.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff BigOperators NNReal ENNReal Laplacian
open Matrix

namespace Riesz2.CompactSobolevMultiplication

section Jets

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Continuous real scalar multiplication, with the vector carrier explicit. -/
def scalarAction : ℝ →L[ℝ] E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℝ

/-- The product rule as a bounded operator on the original value-gradient jets.
The two coefficients are the multiplier and its gradient, respectively. -/
def jetMultiplier (a : Lp ℝ ∞ μ) (b : Lp E ∞ μ) :
    ScalarForm.Jet μ E →L[ℝ] ScalarForm.Jet μ E :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (Lp ℝ 2 μ) (Lp E 2 μ)).symm.toContinuousLinearMap.comp
    ((((ContinuousLinearMap.lsmul ℝ ℝ).holderL μ ∞ 2 2 a).comp (WithLp.fstL 2 ℝ (Lp ℝ 2 μ) (Lp E 2 μ))).prod
      ((((scalarAction (E := E)).holderL μ ∞ 2 2 a).comp (WithLp.sndL 2 ℝ (Lp ℝ 2 μ) (Lp E 2 μ))) +
        (((scalarAction (E := E)).flip.holderL μ ∞ 2 2 b).comp (WithLp.fstL 2 ℝ (Lp ℝ 2 μ) (Lp E 2 μ)))))

/-- Actual values of the product operator, without choosing pointwise representatives. -/
theorem jetMultiplier_value (a : Lp ℝ ∞ μ) (b : Lp E ∞ μ) (u : ScalarForm.Jet μ E) :
    (WithLp.ofLp (jetMultiplier a b u)).1 =ᵐ[μ]
      fun x => a x * (WithLp.ofLp u).1 x :=
  (ContinuousLinearMap.lsmul ℝ ℝ).coeFn_holder (r := 2) a (WithLp.ofLp u).1

/-- Actual gradient of the product operator. -/
theorem jetMultiplier_deriv (a : Lp ℝ ∞ μ) (b : Lp E ∞ μ) (u : ScalarForm.Jet μ E) :
    (WithLp.ofLp (jetMultiplier a b u)).2 =ᵐ[μ]
      fun x => a x • (WithLp.ofLp u).2 x + (WithLp.ofLp u).1 x • b x := by
  have he := Lp.coeFn_add
    ((scalarAction (E := E)).holder 2 a (WithLp.ofLp u).2)
    ((scalarAction (E := E)).flip.holder 2 b (WithLp.ofLp u).1)
  filter_upwards [he, (scalarAction (E := E)).coeFn_holder (r := 2) a (WithLp.ofLp u).2,
    (scalarAction (E := E)).flip.coeFn_holder (r := 2) b (WithLp.ofLp u).1] with x hx hy hz
  exact hx.trans (congrArg₂ (· + ·) hy hz)

end Jets

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsFiniteMeasure μ] {U : Set E}
  (hU : IsOpen U) (hB : Bornology.IsBounded U) (hμ : ∀ᵐ x ∂μ, x ∈ U)

open EuclideanScalarForm Riesz1.WeightedSobolev

/-- The product with a fixed compact smooth multiplier has a compact smooth
approximation in H¹, with the precise product value and gradient. This is the
local smoothing step in Subsection 3.1. No boundary capacity
assumption or global bound on the function being multiplied is needed. -/
theorem compact_multiply (η : E → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U)
    (u : ScalarForm.Domain (smoothJet hU hB hμ)) :
    ∃ w : ScalarForm.Domain (smoothJet hU hB hμ),
      ((ScalarForm.value (smoothJet hU hB hμ) w : E → ℝ) =ᵐ[μ]
        fun x => η x * ScalarForm.value (smoothJet hU hB hμ) u x) ∧
      ((ScalarForm.deriv (smoothJet hU hB hμ) w : E → E) =ᵐ[μ]
        fun x => η x • ScalarForm.deriv (smoothJet hU hB hμ) u x +
          ScalarForm.value (smoothJet hU hB hμ) u x • gradient η x) ∧
      ∃ f : ℕ → EuclideanScalarForm.smoothCore U,
        (∀ k, ContDiff ℝ (⊤ : ℕ∞) (f k).val ∧ HasCompactSupport (f k).val ∧
          tsupport (f k).val ⊆ tsupport η) ∧
        Tendsto (fun k => ScalarForm.ofCore (smoothJet hU hB hμ) (f k)) atTop (𝓝 w) := by
  let J := smoothJet hU hB hμ
  have hgc : HasCompactSupport (gradient η) := by
    exact (hηc.fderiv (𝕜 := ℝ)).comp_left (show (InnerProductSpace.toDual ℝ E).symm 0 = 0 from map_zero _)
  have hgs : Continuous (gradient η) :=
    (InnerProductSpace.toDual ℝ E).symm.continuous.comp
      (hη.continuous_fderiv (by norm_num))
  have ha : MemLp η ∞ μ := hη.continuous.memLp_top_of_hasCompactSupport hηc μ
  have hb : MemLp (gradient η) ∞ μ := hgs.memLp_top_of_hasCompactSupport hgc μ
  let a := ha.toLp η
  let b := hb.toLp (gradient η)
  let A := jetMultiplier a b
  obtain ⟨f, hf⟩ := CutoffApproximation.exists_core_approximation J u
  let g : ℕ → EuclideanScalarForm.smoothCore U := fun k =>
    ⟨fun x => η x * (f k).val x,
      univ, isOpen_univ, subset_univ _,
      (contDiff_cutoff_mul hU hη hηU
        (by obtain ⟨W, hW, hUW, hfs⟩ := (f k).property
            exact hfs.mono (subset_closure.trans hUW))).contDiffOn⟩
  have hg (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (g k).val ∧
      HasCompactSupport (g k).val ∧ tsupport (g k).val ⊆ tsupport η := by
    have hsm : ContDiff ℝ (⊤ : ℕ∞) (g k).val :=
      contDiff_cutoff_mul hU hη hηU (by
        obtain ⟨W, hW, hUW, hfs⟩ := (f k).property
        exact hfs.mono (subset_closure.trans hUW))
    exact ⟨hsm,
      hηc.mul_right, tsupport_mul_subset_left⟩
  have hAg (k : ℕ) : A (J (f k)) = J (g k) := by
    apply WithLp.ofLp_injective
    apply Prod.ext
    · apply Lp.ext
      filter_upwards [jetMultiplier_value a b (J (f k)), ha.coeFn_toLp,
        (memLp_of_smoothNearClosure hB hμ (f k).property).1.coeFn_toLp,
        (memLp_of_smoothNearClosure hB hμ (g k).property).1.coeFn_toLp] with x hx hy hz ht
      change a x = η x at hy
      change (WithLp.ofLp (J (f k))).1 x = (f k).val x at hz
      change (WithLp.ofLp (J (g k))).1 x = (g k).val x at ht
      exact hx.trans (by simpa only [g, hy, hz] using ht.symm)
    · apply Lp.ext
      filter_upwards [jetMultiplier_deriv a b (J (f k)), ha.coeFn_toLp, hb.coeFn_toLp,
        (memLp_of_smoothNearClosure hB hμ (f k).property).1.coeFn_toLp,
        (memLp_of_smoothNearClosure hB hμ (f k).property).2.coeFn_toLp,
        (memLp_of_smoothNearClosure hB hμ (g k).property).2.coeFn_toLp, hμ]
        with x hx hy hz hv hd ht hxU
      have hdf := differentiableAt_core hU (f k) hxU
      have hp : gradient (g k).val x =
          η x • gradient (f k).val x + (f k).val x • gradient η x := by
        change (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fun y => η y * (f k).val y) x) = _
        rw [fderiv_fun_mul (hη.differentiable (by norm_num) x) hdf, map_add, map_smul, map_smul]
        rfl
      change a x = η x at hy
      change b x = gradient η x at hz
      change (WithLp.ofLp (J (f k))).1 x = (f k).val x at hv
      change (WithLp.ofLp (J (f k))).2 x = gradient (f k).val x at hd
      change (WithLp.ofLp (J (g k))).2 x = gradient (g k).val x at ht
      exact hx.trans (by simpa only [hy, hz, hv, hd, hp] using ht.symm)
  have hAl : Tendsto (fun k => J (g k)) atTop (𝓝 (A u.val)) := by
    have hl := A.continuous.tendsto u.val |>.comp (tendsto_subtype_rng.mp hf)
    change Tendsto (fun k => A (J (f k))) atTop (𝓝 (A u.val)) at hl
    simpa only [hAg] using hl
  have hw : A u.val ∈ ScalarForm.completionSubmodule J :=
    J.range.isClosed_topologicalClosure.mem_of_tendsto hAl
      (Eventually.of_forall fun k => (ScalarForm.ofCore J (g k)).property)
  let w : ScalarForm.Domain J := ⟨A u.val, hw⟩
  refine ⟨w, ?_, ?_, g, hg, tendsto_subtype_rng.mpr hAl⟩
  · filter_upwards [jetMultiplier_value a b u.val, ha.coeFn_toLp] with x hx hy
    exact hx.trans (by rw [hy]; rfl)
  · filter_upwards [jetMultiplier_deriv a b u.val, ha.coeFn_toLp, hb.coeFn_toLp]
      with x hx hy hz
    exact hx.trans (by rw [hy, hz]; rfl)

end Euclidean

namespace Internal

section SupportedMultipliers

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- On a common measurable support, a coefficient bounded only on that support
acts continuously on L². This is the local matrix-energy convergence criterion
used after compact localization in Subsection 3.1. -/
theorem supported_multiplier_convergence (K : Set α) (hK : MeasurableSet K)
    (b : α → ℝ) (hb : AEStronglyMeasurable b μ) (C : ℝ) (hC : 0 ≤ C)
    (hbK : ∀ x ∈ K, ‖b x‖ ≤ C)
    (f : ℕ → Lp ℝ 2 μ) (u : Lp ℝ 2 μ)
    (hf : ∀ k, ∀ᵐ x ∂μ, x ∉ K → f k x = 0)
    (hu : ∀ᵐ x ∂μ, x ∉ K → u x = 0)
    (hlim : Tendsto f atTop (𝓝 u)) :
    ∃ (hv : ∀ k, MemLp (fun x => b x * f k x) 2 μ)
      (hw : MemLp (fun x => b x * u x) 2 μ),
      Tendsto (fun k => (hv k).toLp (fun x => b x * f k x)) atTop
        (𝓝 (hw.toLp (fun x => b x * u x))) := by
  classical
  have ht : MemLp (K.indicator b) ∞ μ := by
    apply memLp_top_of_bound (hb.indicator hK) C
    exact Eventually.of_forall fun x => by
      by_cases hx : x ∈ K
      · simpa only [indicator_of_mem hx] using hbK x hx
      · simpa only [indicator_of_notMem hx, norm_zero] using hC
  let A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
    (ContinuousLinearMap.lsmul ℝ ℝ).holderL μ ∞ 2 2 (ht.toLp _)
  have hAe (v : Lp ℝ 2 μ) (hv : ∀ᵐ x ∂μ, x ∉ K → v x = 0) :
      (A v : α → ℝ) =ᵐ[μ] fun x => b x * v x := by
    filter_upwards [(ContinuousLinearMap.lsmul ℝ ℝ).coeFn_holder
      (r := 2) (ht.toLp _) v, ht.coeFn_toLp, hv] with x hx hy hz
    change (A v : α → ℝ) x = (ht.toLp _ : α → ℝ) x * v x at hx
    rw [hx, hy]
    by_cases hxK : x ∈ K
    · simp only [indicator_of_mem hxK]
    · simp only [indicator_of_notMem hxK, hz hxK, mul_zero]
  have hv (k : ℕ) : MemLp (fun x => b x * f k x) 2 μ :=
    (Lp.memLp (A (f k))).ae_eq (hAe (f k) (hf k))
  have hw : MemLp (fun x => b x * u x) 2 μ :=
    (Lp.memLp (A u)).ae_eq (hAe u hu)
  have hve (k : ℕ) : (hv k).toLp (fun x => b x * f k x) = A (f k) :=
    Lp.ext ((hv k).coeFn_toLp.trans (hAe (f k) (hf k)).symm)
  have hwe : hw.toLp (fun x => b x * u x) = A u :=
    Lp.ext (hw.coeFn_toLp.trans (hAe u hu).symm)
  refine ⟨hv, hw, ?_⟩
  simpa only [hve, hwe, Function.comp_def] using A.continuous.tendsto u |>.comp hlim

end SupportedMultipliers

section CutoffLimits

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsFiniteMeasure μ] {U : Set E}
  (hU : IsOpen U) (hB : Bornology.IsBounded U) (hμ : ∀ᵐ x ∂μ, x ∈ U)

open EuclideanScalarForm Riesz1.WeightedSobolev

/-- Internal bounded-field step of Subsection 3.1.
Compact cutoffs with vanishing gradients approximate every bounded scalar H¹
field in H¹. Each localized field has compact smooth approximants on the same
support, and its value is the scalar product. Applying this to the
finitely many components preserves a common scalar cutoff. -/
theorem bounded_cutoff_convergence (η : ℕ → EuclideanScalarForm.smoothCore U)
    (hη : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (η k).val ∧
      HasCompactSupport (η k).val ∧ tsupport (η k).val ⊆ U)
    (hηb : ∀ k x, 0 ≤ (η k).val x ∧ (η k).val x ≤ 1)
    (hηl : ∀ᵐ x ∂μ, Tendsto (fun k => (η k).val x) atTop (𝓝 1))
    (hηg : Tendsto (fun k => ScalarForm.deriv (smoothJet hU hB hμ)
      (ScalarForm.ofCore (smoothJet hU hB hμ) (η k))) atTop (𝓝 0))
    (u : ScalarForm.Domain (smoothJet hU hB hμ))
    (M : ℝ)
    (hu : ∀ᵐ x ∂μ, |ScalarForm.value (smoothJet hU hB hμ) u x| ≤ M) :
    ∃ w : ℕ → ScalarForm.Domain (smoothJet hU hB hμ),
      (∀ k, (ScalarForm.value (smoothJet hU hB hμ) (w k) : E → ℝ) =ᵐ[μ]
        fun x => (η k).val x * ScalarForm.value (smoothJet hU hB hμ) u x) ∧
      (∀ k, ∃ f : ℕ → EuclideanScalarForm.smoothCore U,
        (∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j).val ∧ HasCompactSupport (f j).val ∧
          tsupport (f j).val ⊆ tsupport (η k).val) ∧
        Tendsto (fun j => ScalarForm.ofCore (smoothJet hU hB hμ) (f j)) atTop (𝓝 (w k))) ∧
      Tendsto w atTop (𝓝 u) := by
  let J := smoothJet hU hB hμ
  choose w hwv hwg hwf using fun k =>
    compact_multiply hU hB hμ (η k).val (hη k).1 (hη k).2.1 (hη k).2.2 u
  let F : E → ℝ := ScalarForm.value J u
  let G : E → E := ScalarForm.deriv J u
  have hF : MemLp F 2 μ := Lp.memLp _
  have hG : MemLp G 2 μ := Lp.memLp _
  have hD (k : ℕ) : MemLp (fun x => F x • gradient (η k).val x) 2 μ := by
    apply (memLp_of_smoothNearClosure hB hμ (η k).property).2.of_le_mul (c := M)
      (hF.aestronglyMeasurable.smul
        (memLp_of_smoothNearClosure hB hμ (η k).property).2.aestronglyMeasurable)
    filter_upwards [hu] with x hx
    change ‖F x • gradient (η k).val x‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  have hDn (k : ℕ) :
      ‖(hD k).toLp (fun x => F x • gradient (η k).val x)‖ ≤
        M * ‖ScalarForm.deriv J (ScalarForm.ofCore J (η k))‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(hD k).coeFn_toLp, hu,
      (memLp_of_smoothNearClosure hB hμ (η k).property).2.coeFn_toLp] with x hx hy hz
    change (ScalarForm.deriv J (ScalarForm.ofCore J (η k)) : E → E) x =
      gradient (η k).val x at hz
    rw [hx, hz, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hy (norm_nonneg _)
  have hDl : Tendsto (fun k => (hD k).toLp (fun x => F x • gradient (η k).val x))
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) hDn
    simpa only [norm_zero, mul_zero] using hηg.norm.const_mul M
  have hboundary : Tendsto (fun k => ∫⁻ x, ‖F x • gradient (η k).val x‖ₑ ^ 2 ∂μ)
      atTop (𝓝 0) := by
    have hh := (tendsto_toLp_iff_lintegral_sq _ hD (0 : E → E) MemLp.zero).mp
      (by simpa only [MemLp.toLp_zero] using hDl)
    simpa only [Pi.zero_apply, sub_zero] using hh
  obtain ⟨hvl, hgl⟩ := CutoffApproximation.Internal.cutoff_jet_convergence
    (θ := fun k => (η k).val) (fun k => (hη k).1.continuous.aestronglyMeasurable)
    (fun k => Eventually.of_forall fun x => by
      simpa only [abs_of_nonneg (hηb k x).1] using (hηb k x).2)
    hηl hF hG (fun k => gradient (η k).val) hD hboundary
  have hval : Tendsto (fun k => ScalarForm.value J (w k)) atTop (𝓝 (ScalarForm.value J u)) := by
    have hh := (tendsto_toLp_iff_lintegral_sq _ (fun k => Lp.memLp (ScalarForm.value J (w k)))
      F hF).mpr (by
        convert hvl using 1
        ext k
        exact lintegral_congr_ae ((hwv k).mono fun x hx => by
          dsimp only
          change (ScalarForm.value J (w k) : E → ℝ) x = (η k).val x * F x at hx
          rw [hx]))
    simpa only [F, Lp.toLp_coeFn] using hh
  have hgrad : Tendsto (fun k => ScalarForm.deriv J (w k)) atTop (𝓝 (ScalarForm.deriv J u)) := by
    have hh := (tendsto_toLp_iff_lintegral_sq _ (fun k => Lp.memLp (ScalarForm.deriv J (w k)))
      G hG).mpr (by
        convert hgl using 1
        ext k
        exact lintegral_congr_ae ((hwg k).mono fun x hx => by
          dsimp only
          change (ScalarForm.deriv J (w k) : E → E) x =
            (η k).val x • G x + F x • gradient (η k).val x at hx
          rw [hx]))
    simpa only [G, Lp.toLp_coeFn] using hh
  refine ⟨w, hwv, hwf, ?_⟩
  apply tendsto_subtype_rng.mpr
  exact (WithLp.prod_continuous_toLp 2 _ _).tendsto _ |>.comp (hval.prodMk_nhds hgrad)

end CutoffLimits

section CompactWeighted

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsFiniteMeasure μ] {U : Set E}
  (hU : IsOpen U) (hB : Bornology.IsBounded U) (hμ : ∀ᵐ x ∂μ, x ∈ U)

open EuclideanScalarForm Riesz1.WeightedSobolev

/-- Compact localization followed by smooth approximation simultaneously in
H¹ and in the L² norm of any measurable coefficient continuous in the interior.
The coefficient may be unbounded at the boundary. This proves the last local
approximation step of Subsection 3.1, entry by entry for a
locally continuous square-root Hessian. -/
theorem compact_multiply_weighted (η : E → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U)
    (b : E → ℝ) (hb : Measurable b) (hbU : ContinuousOn b U)
    (u : ScalarForm.Domain (smoothJet hU hB hμ)) :
    ∃ (w : ScalarForm.Domain (smoothJet hU hB hμ))
      (f : ℕ → EuclideanScalarForm.smoothCore U),
      ((ScalarForm.value (smoothJet hU hB hμ) w : E → ℝ) =ᵐ[μ]
        fun x => η x * ScalarForm.value (smoothJet hU hB hμ) u x) ∧
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (f k).val ∧ HasCompactSupport (f k).val ∧
        tsupport (f k).val ⊆ tsupport η) ∧
      Tendsto (fun k => ScalarForm.ofCore (smoothJet hU hB hμ) (f k)) atTop (𝓝 w) ∧
      ∃ (hv : ∀ k, MemLp (fun x => b x * ScalarForm.value (smoothJet hU hB hμ)
          (ScalarForm.ofCore (smoothJet hU hB hμ) (f k)) x) 2 μ)
        (hw : MemLp (fun x => b x * ScalarForm.value (smoothJet hU hB hμ) w x) 2 μ),
        Tendsto (fun k => (hv k).toLp (fun x => b x * ScalarForm.value (smoothJet hU hB hμ)
          (ScalarForm.ofCore (smoothJet hU hB hμ) (f k)) x)) atTop
          (𝓝 (hw.toLp (fun x => b x * ScalarForm.value (smoothJet hU hB hμ) w x))) := by
  let J := smoothJet hU hB hμ
  obtain ⟨w, hwv, _, f, hf, hfl⟩ := compact_multiply hU hB hμ η hη hηc hηU u
  refine ⟨w, f, hwv, hf, hfl, ?_⟩
  let fv : ℕ → Lp ℝ 2 μ := fun k => ScalarForm.value J (ScalarForm.ofCore J (f k))
  have hfs (k : ℕ) : ∀ᵐ x ∂μ, x ∉ tsupport η → fv k x = 0 := by
    filter_upwards [(memLp_of_smoothNearClosure hB hμ (f k).property).1.coeFn_toLp]
      with x hx hn
    change fv k x = (f k).val x at hx
    exact hx.trans (image_eq_zero_of_notMem_tsupport fun h => hn ((hf k).2.2 h))
  have hws : ∀ᵐ x ∂μ, x ∉ tsupport η → ScalarForm.value J w x = 0 := by
    filter_upwards [hwv] with x hx hn
    change ScalarForm.value J w x = η x * ScalarForm.value J u x at hx
    rw [hx, image_eq_zero_of_notMem_tsupport hn, zero_mul]
  obtain ⟨C, hC⟩ := hηc.isCompact.exists_bound_of_continuousOn (hbU.mono hηU)
  have hvl : Tendsto fv atTop (𝓝 (ScalarForm.value J w)) :=
    (ScalarForm.value J).continuous.tendsto w |>.comp hfl
  exact supported_multiplier_convergence (tsupport η) isClosed_closure.measurableSet
    b hb.aestronglyMeasurable (max C 0) (le_max_right _ _)
    (fun x hx => (hC x hx).trans (le_max_left _ _)) fv (ScalarForm.value J w) hfs hws hvl

end CompactWeighted
end Internal
end Riesz2.CompactSobolevMultiplication


namespace Riesz2.VectorCore

namespace Internal

/-- A fixed smooth clipping of a scalar core approximation to the constant one.
It vanishes below one half and equals one above one. -/
def coreClip (r : ℝ) : ℝ := 1 - CutoffApproximation.scalarCutoff (2 * r)

theorem coreClip_smooth : ContDiff ℝ (⊤ : ℕ∞) coreClip :=
  contDiff_const.sub (CutoffApproximation.scalarCutoff_contDiff.comp
    (contDiff_const.mul contDiff_id))

theorem coreClip_bounds (r : ℝ) : 0 ≤ coreClip r ∧ coreClip r ≤ 1 := by
  unfold coreClip
  constructor <;> linarith [CutoffApproximation.scalarCutoff_nonneg (2 * r),
    CutoffApproximation.scalarCutoff_le_one (2 * r)]

theorem coreClip_zero : coreClip 0 = 0 := by
  simp only [coreClip, mul_zero,
    CutoffApproximation.scalarCutoff_eq_one (by norm_num : (0 : ℝ) ≤ 1), sub_self]

theorem coreClip_one : coreClip 1 = 1 := by
  norm_num [coreClip, CutoffApproximation.scalarCutoff_eq_zero (le_refl (2 : ℝ))]

theorem coreClip_deriv_bound : ∃ C : ℝ≥0, ∀ r, ‖deriv coreClip r‖₊ ≤ C := by
  obtain ⟨C, hC, hb⟩ := CutoffApproximation.scalarCutoff_derivative_bound 1
  refine ⟨⟨2 * C, by positivity⟩, fun r => ?_⟩
  have hd : deriv coreClip r = -deriv CutoffApproximation.scalarCutoff (2 * r) * 2 := by
    exact ((hasDerivAt_const r (1 : ℝ)).sub
      (((CutoffApproximation.scalarCutoff_contDiff.differentiable (by norm_num))
        (2 * r)).hasDerivAt.comp r ((hasDerivAt_id r).const_mul 2))).deriv.trans (by ring)
  change ‖deriv coreClip r‖ ≤ 2 * C
  rw [hd, norm_mul, norm_neg, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hh : ‖deriv CutoffApproximation.scalarCutoff (2 * r)‖ ≤ C := by
    simpa only [iteratedDeriv_one, Real.norm_eq_abs] using hb (2 * r)
  linarith

end Internal

section Cutoffs

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  {ρ : Measure E} {U : Set E} {V : E → ℝ}
  (hU : IsOpen U) (hB : Bornology.IsBounded U)
  (hV : IsEuclideanGibbsPotential volume ρ U V)

open IntrinsicScalarCore ScalarForm EuclideanScalarForm Riesz1.WeightedSobolev

/-- Compact cutoff construction for Subsection 3.1. The functions belong
to the scalar core, take values in `[0,1]`, converge to one in H¹,
and converge almost everywhere. The boundary assumption is the
collision barrier. -/
theorem exists_compact_cutoffs {C : ℝ} (hC : 0 ≤ C)
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹ ^ 2 - C ≤
      ‖gradient V x‖ ^ 2 / 4 - Δ V x / 2) :
    letI := probability hV
    ∃ η : ℕ → EuclideanScalarForm.smoothCore U,
      (∀ k, η k ∈ compactTests U) ∧
      (∀ k x, 0 ≤ (η k).val x ∧ (η k).val x ≤ 1) ∧
      Tendsto (fun k => ScalarForm.ofCore (jet hU hB hV) (η k)) atTop
        (𝓝 (EuclideanScalarForm.constant hU hB (supported hU hV) 1)) ∧
      ∀ᵐ x ∂ρ, Tendsto (fun k => (η k).val x) atTop (𝓝 1) := by
  have := probability hV
  let J := jet hU hB hV
  let one : Domain J := EuclideanScalarForm.constant hU hB (supported hU hV) 1
  obtain ⟨a, ha, hal⟩ := mem_closure_iff_seq_limit.mp
    (dense_compactFormDomain hU hB hV hC hbar one)
  have ha' (k : ℕ) : ∃ f : EuclideanScalarForm.smoothCore U,
      f ∈ compactTests U ∧ ScalarForm.ofCore J f = a k := ha k
  choose f hf hfa using ha'
  obtain ⟨D, hD⟩ := Internal.coreClip_deriv_bound
  let η : ℕ → EuclideanScalarForm.smoothCore U := fun k =>
    ⟨Internal.coreClip ∘ (f k).val,
      (f k).property.comp_smooth Internal.coreClip_smooth⟩
  have hη (k : ℕ) : η k ∈ compactTests U := by
    have hs : tsupport (η k).val ⊆ tsupport (f k).val := by
      apply closure_mono
      intro x hx
      change (f k).val x ≠ 0
      intro hz
      exact hx (by simp only [η, Function.comp_def, hz, Internal.coreClip_zero])
    exact ⟨Internal.coreClip_smooth.comp (hf k).1,
      ((hf k).2.1.isCompact.of_isClosed_subset
        isClosed_closure hs), hs.trans (hf k).2.2⟩
  have hηb (k : ℕ) (x : E) : 0 ≤ (η k).val x ∧ (η k).val x ≤ 1 :=
    Internal.coreClip_bounds _
  have hfl : Tendsto (fun k => ofCore J (f k)) atTop (𝓝 one) :=
    hal.congr (fun k => (hfa k).symm)
  have hvl : Tendsto (fun k => value J (ofCore J (f k))) atTop (𝓝 (value J one)) := by
    simpa only [Function.comp_def] using (value J).continuous.tendsto one |>.comp hfl
  have hone : deriv J one = 0 := EuclideanScalarForm.deriv_constant hU hB (supported hU hV) 1
  have hgl : Tendsto (fun k => deriv J (ofCore J (f k))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, hone] using
      (deriv J).continuous.tendsto one |>.comp hfl
  have hLip := lipschitzWith_of_nnnorm_deriv_le
    (Internal.coreClip_smooth.differentiable (by norm_num)) hD
  have hvη (k : ℕ) : value J (ofCore J (η k)) =
      hLip.compLp Internal.coreClip_zero (value J (ofCore J (f k))) := by
    apply Lp.ext
    filter_upwards [(memLp_of_smoothNearClosure hB (supported hU hV) (η k).property).1.coeFn_toLp,
      hLip.coeFn_compLp Internal.coreClip_zero (value J (ofCore J (f k))),
      (memLp_of_smoothNearClosure hB (supported hU hV) (f k).property).1.coeFn_toLp]
      with x hx hy hz
    change (value J (ofCore J (f k)) : E → ℝ) x = (f k).val x at hz
    exact hx.trans (by simpa only [η, Function.comp_def, hz] using hy.symm)
  have hvone : hLip.compLp Internal.coreClip_zero (value J one) = value J one := by
    apply Lp.ext
    filter_upwards [hLip.coeFn_compLp Internal.coreClip_zero (value J one),
      value_constant hU hB (supported hU hV) 1] with x hx hy
    change (value J one : E → ℝ) x = 1 at hy
    simpa only [Function.comp_def, hy, Internal.coreClip_one] using hx
  have hηvl : Tendsto (fun k => value J (ofCore J (η k))) atTop (𝓝 (value J one)) := by
    simpa only [hvη, hvone, Function.comp_def] using
      (hLip.continuous_compLp Internal.coreClip_zero).tendsto (value J one) |>.comp hvl
  have hgη (k : ℕ) : ‖deriv J (ofCore J (η k))‖ ≤ (D : ℝ) * ‖deriv J (ofCore J (f k))‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(memLp_of_smoothNearClosure hB (supported hU hV) (η k).property).2.coeFn_toLp,
      (memLp_of_smoothNearClosure hB (supported hU hV) (f k).property).2.coeFn_toLp,
      supported hU hV] with x hx hy hxU
    change (deriv J (ofCore J (η k)) : E → E) x = gradient (η k).val x at hx
    change (deriv J (ofCore J (f k)) : E → E) x = gradient (f k).val x at hy
    rw [hx, hy]
    have hc : gradient (η k).val x =
        _root_.deriv Internal.coreClip ((f k).val x) • gradient (f k).val x := by
      change (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (Internal.coreClip ∘ (f k).val) x) = _
      rw [((Internal.coreClip_smooth.differentiable (by norm_num) _).hasDerivAt.comp_hasFDerivAt x
        (differentiableAt_core hU (f k) hxU).hasFDerivAt).fderiv, map_smul]
      rfl
    rw [hc, norm_smul]
    exact mul_le_mul_of_nonneg_right (hD _ : ‖_root_.deriv Internal.coreClip _‖ ≤ (D : ℝ)) (norm_nonneg _)
  have hηgl : Tendsto (fun k => deriv J (ofCore J (η k))) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) hgη
    simpa only [norm_zero, mul_zero] using hgl.norm.const_mul (D : ℝ)
  have hηl : Tendsto (fun k => ofCore J (η k)) atTop (𝓝 one) := by
    apply tendsto_subtype_rng.mpr
    change Tendsto (fun k => WithLp.toLp 2 (value J (ofCore J (η k)),
      deriv J (ofCore J (η k)))) atTop (𝓝 (one.val))
    have he : one.val = WithLp.toLp 2 (value J one, (0 : Lp E 2 ρ)) := by
      rw [← EuclideanScalarForm.deriv_constant hU hB (supported hU hV) 1]
      rfl
    rw [he]
    exact (WithLp.prod_continuous_toLp 2 _ _).tendsto _ |>.comp (hηvl.prodMk_nhds hηgl)
  obtain ⟨ns, hns, hnsLim⟩ := (tendstoInMeasure_of_tendsto_Lp hηvl).exists_seq_tendsto_ae
  refine ⟨η ∘ ns, fun k => hη _, fun k x => hηb _ x, hηl.comp hns.tendsto_atTop, ?_⟩
  filter_upwards [hnsLim, ae_all_iff.mpr (fun k =>
    (memLp_of_smoothNearClosure hB (supported hU hV) (η (ns k)).property).1.coeFn_toLp),
    value_constant hU hB (supported hU hV) 1] with x hx hy hz
  change (value J one : E → ℝ) x = 1 at hz
  change ∀ k, (value J (ofCore J (η (ns k))) : E → ℝ) x = (η (ns k)).val x at hy
  simpa only [hy, hz, Function.comp_def] using hx

end Cutoffs

section RadialLimits

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
  {ρ : Measure E} {U : Set E} {V : E → ℝ}
  (hU : IsOpen U) (hB : Bornology.IsBounded U)
  (hV : IsEuclideanGibbsPotential volume ρ U V)

open IntrinsicScalarCore ScalarForm EuclideanScalarForm Riesz1.WeightedSobolev

/-- Radial H¹ approximation in Subsection 3.1. The radial
excess tends to zero in the original intrinsic jet space, and subtracting it
gives bounded vector fields. This includes the zero radius and empty index set. -/
theorem exists_radial_excess (u : ι → ScalarForm.Domain (jet hU hB hV)) :
    ∃ w : ℕ → ι → ScalarForm.Domain (jet hU hB hV),
      (∀ n i, ScalarForm.value (jet hU hB hV) (w n i) =
        VectorRadial.truncateValues n (fun j => ScalarForm.value (jet hU hB hV) (u j)) i) ∧
      (∀ i, Tendsto (fun n => w n i) atTop (𝓝 0)) ∧
      ∀ n, ∀ᵐ x ∂ρ, ∀ i,
        |ScalarForm.value (jet hU hB hV) (u i) x -
          ScalarForm.value (jet hU hB hV) (w n i) x| ≤ (n : ℝ) := by
  classical
  have := probability hV
  let J := jet hU hB hV
  let F : ι → E → ℝ := fun i => value J (u i)
  let G : ι → E → E := fun i => deriv J (u i)
  have hFG (i : ι) : IsWeightedH1 ρ U (F i) (G i) := by
    apply (mem_completion_iff hU hB (supported hU hV) _ _ (Lp.memLp _) (Lp.memLp _)).mp
    simp only [Lp.toLp_coeFn]
    change WithLp.toLp 2 (value J (u i), deriv J (u i)) ∈ completionSubmodule J
    have he : WithLp.toLp 2 (value J (u i), deriv J (u i)) = (u i).val :=
      WithLp.toLp_ofLp 2 _
    rw [he]
    exact (u i).property
  let T : ℕ → ι → E → ℝ := fun n i x =>
    VectorRadial.truncate n (WithLp.toLp 2 (fun j => F j x) : EuclideanSpace ℝ ι) i
  let D : ℕ → ι → E → E := fun n i x =>
    VectorRadial.weakDifferential n (WithLp.toLp 2 (fun j => F j x)) (fun j => G j x) i
  have hTD (n : ℕ) (i : ι) : IsWeightedH1 ρ U (T n i) (D n i) :=
    VectorRadial.sobolev_truncate hU hB (supported hU hV)
      (form hU hB hV) (realization hU hB hV) hFG n i
  let w : ℕ → ι → Domain J := fun n i =>
    ⟨WithLp.toLp 2 ((hTD n i).1.toLp (T n i), (hTD n i).2.1.toLp (D n i)),
      (mem_completion_iff hU hB (supported hU hV) _ _ (hTD n i).1 (hTD n i).2.1).mpr (hTD n i)⟩
  have hwv (n : ℕ) (i : ι) : (value J (w n i) : E → ℝ) =ᵐ[ρ] T n i :=
    (hTD n i).1.coeFn_toLp
  have hwg (n : ℕ) (i : ι) : (deriv J (w n i) : E → E) =ᵐ[ρ] D n i :=
    (hTD n i).2.1.coeFn_toLp
  have heq (x : E) : ∀ᶠ n : ℕ in atTop, ∀ i, T n i x = 0 ∧ D n i x = 0 := by
    have hh : ∀ᶠ n : ℕ in atTop,
        ‖(WithLp.toLp 2 (fun j => F j x) : EuclideanSpace ℝ ι)‖ < (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
    filter_upwards [hh] with n hn
    intro i
    refine ⟨congrArg (fun z : EuclideanSpace ℝ ι => z i)
      (VectorRadial.truncate_of_norm_le n hn.le), ?_⟩
    simp only [D, VectorRadial.weakDifferential, NNReal.coe_natCast, not_lt.mpr hn.le, ↓reduceIte]
  have hlim (i : ι) : Tendsto (fun n => w n i) atTop (𝓝 0) := by
    have hval : Tendsto (fun n => value J (w n i)) atTop (𝓝 0) := by
      have ht := tendsto_toLp_of_dominated (fun n => (hTD n i).1)
        (MemLp.zero : MemLp (0 : E → ℝ) 2 ρ) (hFG i).1.norm
        (fun n => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => by simpa only [Pi.zero_apply, norm_zero] using norm_nonneg (F i x))
        (Eventually.of_forall fun x => tendsto_const_nhds.congr'
          ((heq x).mono fun n hn => (hn i).1.symm))
      · change Tendsto (fun n => value J (w n i)) atTop
          (𝓝 ((MemLp.zero : MemLp (0 : E → ℝ) 2 ρ).toLp 0)) at ht
        simpa only [MemLp.toLp_zero] using ht
      change |VectorRadial.coefficient n _ * F i x| ≤ |F i x|
      rw [abs_mul, abs_of_nonneg (VectorRadial.coefficient_nonneg _ _)]
      exact mul_le_of_le_one_left (abs_nonneg _) (VectorRadial.coefficient_le_one _ _)
    have hgrad : Tendsto (fun n => deriv J (w n i)) atTop (𝓝 0) := by
      let b : E → ℝ := fun x => ‖G i x‖ + ∑ j, ‖G j x‖
      have hb : MemLp b 2 ρ :=
        (hFG i).2.1.norm.add (memLp_finsetSum _ (fun j _ => (hFG j).2.1.norm))
      have ht := tendsto_toLp_of_dominated (fun n => (hTD n i).2.1)
        (MemLp.zero : MemLp (0 : E → E) 2 ρ) hb
        (fun n => Eventually.of_forall fun x => VectorRadial.norm_weakDifferential_le n _ _ i)
        (Eventually.of_forall fun x => by
          simpa only [Pi.zero_apply, norm_zero, b] using
            add_nonneg (norm_nonneg (G i x))
              (Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => norm_nonneg (G j x)))
        (Eventually.of_forall fun x => tendsto_const_nhds.congr'
          ((heq x).mono fun n hn => (hn i).2.symm))
      change Tendsto (fun n => deriv J (w n i)) atTop
        (𝓝 ((MemLp.zero : MemLp (0 : E → E) 2 ρ).toLp 0)) at ht
      simpa only [MemLp.toLp_zero] using ht
    apply tendsto_subtype_rng.mpr
    exact (WithLp.prod_continuous_toLp 2 _ _).tendsto _ |>.comp (hval.prodMk_nhds hgrad)
  refine ⟨w, ?_, hlim, fun n => ?_⟩
  · intro n i
    apply Lp.ext
    filter_upwards [hwv n i, VectorRadial.truncateValues_ae n (fun j => value J (u j))]
      with x hx hy
    exact hx.trans (hy i).symm
  · filter_upwards [ae_all_iff.mpr (hwv n)] with x hx
    intro i
    rw [hx i]
    let z : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun j => F j x)
    exact (PiLp.norm_apply_le (z - VectorRadial.truncate n z) i).trans
      (VectorRadial.norm_sub_truncate_le n z)

end RadialLimits

namespace Internal
section CompactAssembly

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι] [DecidableEq ι]
  {ρ : Measure E} {U : Set E} {V : E → ℝ}
  (hU : IsOpen U) (hB : Bornology.IsBounded U)
  (hV : IsEuclideanGibbsPotential volume ρ U V)

open IntrinsicScalarCore ScalarForm EuclideanScalarForm MatrixEnergy Riesz1.WeightedSobolev

local instance : InnerProductSpace ℝ (ScalarForm.Domain (jet hU hB hV)) := inferInstance
local instance : InnerProductSpace ℝ
    (PiLp 2 (fun _ : ι => ScalarForm.Domain (jet hU hB hV))) := PiLp.innerProductSpace _

omit [DecidableEq ι] in
/-- Internal assembly of compact approximation in H¹ and in every multiplier
coordinate, including a fixed component constraint. All estimates are local to
the common support. No global coefficient bound is assumed. -/
theorem mem_compactCompletion_of_supported_smooth
    (B : E → Matrix ι ι ℝ) (S : Submodule ℝ (ι → ℝ))
    (hBm : ∀ i j, AEStronglyMeasurable (fun x => B x i j) ρ)
    (K : Set E) (hK : MeasurableSet K)
    (hBK : ∀ i j, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ‖B x i j‖ ≤ C)
    (z : graph (componentValue hU hB hV) B S)
    (hzK : ∀ i, ∀ᵐ x ∂ρ, x ∉ K → input (componentValue hU hB hV) i z.val x = 0)
    (f : ℕ → ι → EuclideanScalarForm.smoothCore U)
    (hf : ∀ n i, f n i ∈ compactTests U ∧ tsupport (f n i).val ⊆ K)
    (hfS : ∀ n x, (fun i => (f n i).val x) ∈ S)
    (hfl : ∀ i, Tendsto (fun n => ofCore (jet hU hB hV) (f n i)) atTop
      (𝓝 ((WithLp.ofLp z.val).1 i))) :
    z.val ∈ compactCompletion hU hB hV B S := by
  have := probability hV
  let J := jet hU hB hV
  let v := componentValue (ι := ι) hU hB hV
  let fv : ℕ → ι → Lp ℝ 2 ρ := fun n i => value J (ofCore J (f n i))
  have hvs (n : ℕ) (i : ι) : ∀ᵐ x ∂ρ, x ∉ K → fv n i x = 0 := by
    filter_upwards [(memLp_of_smoothNearClosure hB (supported hU hV) (f n i).property).1.coeFn_toLp]
      with x hx hn
    change fv n i x = (f n i).val x at hx
    exact hx.trans (image_eq_zero_of_notMem_tsupport fun h => hn ((hf n i).2 h))
  have hvl (i : ι) : Tendsto (fun n => fv n i) atTop (𝓝 (input v i z.val)) :=
    (value J).continuous.tendsto _ |>.comp (hfl i)
  choose C hC hCb using hBK
  have hp (k i : ι) :=
    CompactSobolevMultiplication.Internal.supported_multiplier_convergence K hK
      (fun x => B x k i) (hBm k i) (C k i) (hC k i) (hCb k i)
      (fun n => fv n i) (input v i z.val) (fun n => hvs n i) (hzK i) (hvl i)
  choose hv hw hprod using hp
  let q : ℕ → ι → Lp ℝ 2 ρ := fun n k =>
    ∑ i, (hv k i n).toLp (fun x => B x k i * fv n i x)
  let r : ι → Lp ℝ 2 ρ := fun k =>
    ∑ i, (hw k i).toLp (fun x => B x k i * input v i z.val x)
  have hq (n : ℕ) (k : ι) : (q n k : E → ℝ) =ᵐ[ρ]
      fun x => ∑ i, B x k i * fv n i x := by
    filter_upwards [Lp.coeFn_finsetSum Finset.univ
      (fun i => (hv k i n).toLp (fun x => B x k i * fv n i x)),
      ae_all_iff.mpr (fun i => (hv k i n).coeFn_toLp)] with x hx hy
    simp only [Finset.sum_apply] at hx
    exact hx.trans (Finset.sum_congr rfl (fun i _ => hy i))
  have hr (k : ι) : r k = output k z.val := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_finsetSum Finset.univ
      (fun i => (hw k i).toLp (fun x => B x k i * input v i z.val x)),
      ae_all_iff.mpr (fun i => (hw k i).coeFn_toLp), z.property] with x hx hy hz
    simp only [Finset.sum_apply] at hx
    exact hx.trans ((Finset.sum_congr rfl (fun i _ => hy i)).trans (hz.2 k).symm)
  have hql (k : ι) : Tendsto (fun n => q n k) atTop (𝓝 (output k z.val)) := by
    rw [← hr k]
    exact tendsto_finsetSum Finset.univ (fun i _ => hprod k i)
  let p : ℕ → MatrixEnergy.Jet (κ := ι) (ρ := ρ)
      (H := PiLp 2 (fun _ : ι => Domain J)) := fun n =>
    WithLp.toLp 2 (WithLp.toLp 2 (fun i => ofCore J (f n i)), WithLp.toLp 2 (q n))
  have hpc (n : ℕ) : p n ∈ compactGraph hU hB hV B S := by
    constructor
    · have he (i : ι) : (input v i (p n) : E → ℝ) =ᵐ[ρ] (f n i).val :=
        (memLp_of_smoothNearClosure hB (supported hU hV) (f n i).property).1.coeFn_toLp
      filter_upwards [ae_all_iff.mpr he, ae_all_iff.mpr (hq n)] with x hx hy
      refine ⟨?_, fun k => hy k⟩
      exact (funext hx) ▸ hfS n x
    · intro i
      exact ⟨f n i, (hf n i).1, rfl⟩
  have hpl : Tendsto p atTop (𝓝 z.val) := by
    have hb : Tendsto (fun n => (WithLp.ofLp (p n)).1) atTop
        (𝓝 (WithLp.ofLp z.val).1) := by
      exact (PiLp.continuous_toLp 2 _).tendsto _ |>.comp (tendsto_pi_nhds.mpr hfl)
    have he : Tendsto (fun n => (WithLp.ofLp (p n)).2) atTop
        (𝓝 (WithLp.ofLp z.val).2) := by
      exact (PiLp.continuous_toLp 2 _).tendsto _ |>.comp (tendsto_pi_nhds.mpr hql)
    exact (WithLp.prod_continuous_toLp 2 _ _).tendsto _ |>.comp (hb.prodMk_nhds he)
  exact mem_closure_of_tendsto hpl (Eventually.of_forall hpc)

end CompactAssembly

section BoundedAssembly

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  [Fintype ι] [DecidableEq ι]
  {ρ : Measure E} {U : Set E} {V : E → ℝ}
  (hU : IsOpen U) (hB : Bornology.IsBounded U)
  (hV : IsEuclideanGibbsPotential volume ρ U V)

open IntrinsicScalarCore ScalarForm EuclideanScalarForm MatrixEnergy Riesz1.WeightedSobolev

local instance : InnerProductSpace ℝ (ScalarForm.Domain (jet hU hB hV)) := inferInstance
local instance : InnerProductSpace ℝ
    (PiLp 2 (fun _ : ι => ScalarForm.Domain (jet hU hB hV))) := PiLp.innerProductSpace _

omit [Nontrivial E] [DecidableEq ι] in
/-- Internal localized-vector assembly for intrinsic coordinates. -/
theorem mem_compactCompletion_of_local_approximation
    (B : E → Matrix ι ι ℝ) (hBm : ∀ i j, AEStronglyMeasurable (fun x => B x i j) ρ)
    (hBc : ∀ i j, ContinuousOn (fun x => B x i j) U)
    (z : graph (componentValue hU hB hV) B ⊤)
    (K : Set E) (hK : IsCompact K) (hKU : K ⊆ U)
    (hzK : ∀ i, ∀ᵐ x ∂ρ, x ∉ K → input (componentValue hU hB hV) i z.val x = 0)
    (hf : ∀ i, ∃ f : ℕ → EuclideanScalarForm.smoothCore U,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n).val ∧ HasCompactSupport (f n).val ∧ tsupport (f n).val ⊆ K) ∧
      Tendsto (fun n => ofCore (jet hU hB hV) (f n)) atTop (𝓝 ((WithLp.ofLp z.val).1 i))) :
    z.val ∈ compactCompletion hU hB hV B ⊤ := by
  choose f hfc hfl using hf
  apply mem_compactCompletion_of_supported_smooth hU hB hV B ⊤ hBm K hK.measurableSet
    (fun i j => ?_) z hzK (fun n i => f i n)
    (fun n i => ⟨⟨(hfc i n).1, (hfc i n).2.1, (hfc i n).2.2.trans hKU⟩, (hfc i n).2.2⟩)
    (fun _ _ => Submodule.mem_top) hfl
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn ((hBc i j).mono hKU)
  exact ⟨max C 0, le_max_right _ _, fun x hx => (hC x hx).trans (le_max_left _ _)⟩

omit [DecidableEq ι] in
/-- The bounded-field part of Subsection 3.1, assembled in
the full original matrix graph. The coefficient is only locally continuous. -/
theorem mem_compactCompletion_of_bounded
    {C : ℝ} (hC : 0 ≤ C)
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹ ^ 2 - C ≤
      ‖gradient V x‖ ^ 2 / 4 - Δ V x / 2)
    (B : E → Matrix ι ι ℝ) (hBm : ∀ i j, AEStronglyMeasurable (fun x => B x i j) ρ)
    (hBc : ∀ i j, ContinuousOn (fun x => B x i j) U)
    (z : graph (componentValue hU hB hV) B ⊤)
    (M : ℝ) (hzM : ∀ i, ∀ᵐ x ∂ρ, |input (componentValue hU hB hV) i z.val x| ≤ M) :
    z.val ∈ compactCompletion hU hB hV B ⊤ := by
  have := probability hV
  let J := jet hU hB hV
  let v := componentValue (ι := ι) hU hB hV
  obtain ⟨η, hη, hηb, hηl, hηae⟩ := exists_compact_cutoffs hU hB hV hC hbar
  have hηg : Tendsto (fun n => deriv J (ofCore J (η n))) atTop (𝓝 0) := by
    have hh := (deriv J).continuous.tendsto _ |>.comp hηl
    have hone : deriv J (EuclideanScalarForm.constant hU hB (supported hU hV) 1) = 0 :=
      EuclideanScalarForm.deriv_constant hU hB (supported hU hV) 1
    simpa only [Function.comp_def, hone] using hh
  have hp (i : ι) := CompactSobolevMultiplication.Internal.bounded_cutoff_convergence
    hU hB (supported hU hV) η hη hηb hηae hηg ((WithLp.ofLp z.val).1 i) M (hzM i)
  choose w hwv hwf hwl using hp
  have hq (n : ℕ) (k : ι) : MemLp (fun x => (η n).val x * output k z.val x) 2 ρ := by
    apply (Lp.memLp (output k z.val)).of_le_mul (c := 1)
      ((hη n).1.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable _))
    exact Eventually.of_forall fun x => by
      change ‖(η n).val x * output k z.val x‖ ≤ _
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hηb n x).1, one_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hηb n x).2
  let q : ℕ → ι → Lp ℝ 2 ρ := fun n k => (hq n k).toLp _
  have hql (k : ι) : Tendsto (fun n => q n k) atTop (𝓝 (output k z.val)) := by
    have hh := CutoffApproximation.Internal.cutoff_smul_l2_convergence
      (θ := fun n => (η n).val) (fun n => (hη n).1.continuous.aestronglyMeasurable)
      (fun n => Eventually.of_forall fun x => by
        simpa only [abs_of_nonneg (hηb n x).1] using (hηb n x).2)
      hηae (Lp.memLp (output k z.val))
    have ht := (tendsto_toLp_iff_lintegral_sq _ (fun n => hq n k)
      (output k z.val) (Lp.memLp _)).mpr (by simpa only [smul_eq_mul] using hh.2)
    simpa only [Lp.toLp_coeFn] using ht
  let p : ℕ → MatrixEnergy.Jet (κ := ι) (ρ := ρ)
      (H := PiLp 2 (fun _ : ι => Domain J)) := fun n =>
    WithLp.toLp 2 (WithLp.toLp 2 (fun i => w i n), WithLp.toLp 2 (q n))
  have hpg (n : ℕ) : p n ∈ graph v B ⊤ := by
    change ∀ᵐ x ∂ρ, (fun i => input v i (p n) x) ∈ (⊤ : Submodule ℝ (ι → ℝ)) ∧
      ∀ k, output k (p n) x = ∑ i, B x k i * input v i (p n) x
    filter_upwards [ae_all_iff.mpr (fun i => hwv i n),
      ae_all_iff.mpr (fun k => (hq n k).coeFn_toLp), z.property] with x hx hy hz
    refine ⟨Submodule.mem_top, fun k => ?_⟩
    change q n k x = ∑ i, B x k i * value J (w i n) x
    change ∀ i, value J (w i n) x = (η n).val x * input v i z.val x at hx
    rw [hy k, hz.2 k, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hx i]; ring
  have hpc (n : ℕ) : p n ∈ compactCompletion hU hB hV B ⊤ := by
    apply mem_compactCompletion_of_local_approximation hU hB hV B hBm hBc ⟨p n, hpg n⟩
      (tsupport (η n).val) (hη n).2.1 (hη n).2.2
    · intro i
      filter_upwards [hwv i n] with x hx hn
      change input v i (p n) x = (η n).val x * input v i z.val x at hx
      rw [hx, image_eq_zero_of_notMem_tsupport hn, zero_mul]
    · exact fun i => hwf i n
  have hpl : Tendsto p atTop (𝓝 z.val) := by
    have hb := (PiLp.continuous_toLp 2 _).tendsto _ |>.comp (tendsto_pi_nhds.mpr hwl)
    have he := (PiLp.continuous_toLp 2 _).tendsto _ |>.comp (tendsto_pi_nhds.mpr hql)
    exact (WithLp.prod_continuous_toLp 2 _ _).tendsto _ |>.comp (hb.prodMk_nhds he)
  exact (compactGraph hU hB hV B ⊤).isClosed_topologicalClosure.mem_of_tendsto hpl
    (Eventually.of_forall hpc)

omit [DecidableEq ι] in
/-- Reverse inclusion of Subsection 3.1, for any locally
continuous matrix multiplier. Radial approximation makes the fields bounded
while simultaneously converging in the complete multiplier graph. -/
theorem graph_le_compactCompletion
    {C : ℝ} (hC : 0 ≤ C)
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹ ^ 2 - C ≤
      ‖gradient V x‖ ^ 2 / 4 - Δ V x / 2)
    (B : E → Matrix ι ι ℝ) (hBm : ∀ i j, AEStronglyMeasurable (fun x => B x i j) ρ)
    (hBc : ∀ i j, ContinuousOn (fun x => B x i j) U) :
    graph (componentValue hU hB hV) B ⊤ ≤ compactCompletion hU hB hV B ⊤ := by
  have := probability hV
  let J := jet hU hB hV
  let v := componentValue (ι := ι) hU hB hV
  intro z hz
  obtain ⟨w, hwv, hwl, hwb⟩ := exists_radial_excess hU hB hV (WithLp.ofLp z).1
  let F : ι → Lp ℝ 2 ρ := fun i => input v i z
  let a : ℕ → E → ℝ := fun n x => VectorRadial.coefficient n
    (WithLp.toLp 2 (fun i => F i x) : EuclideanSpace ℝ ι)
  have ha (n : ℕ) : AEStronglyMeasurable (a n) ρ := by
    have hn := (VectorRadial.memLp_values F).aestronglyMeasurable.norm.aemeasurable
    exact (aemeasurable_const.max (aemeasurable_const.sub
      (aemeasurable_const.div hn))).aestronglyMeasurable
  have hq (n : ℕ) (k : ι) : MemLp (fun x => a n x * output k z x) 2 ρ := by
    apply (Lp.memLp (output k z)).of_le_mul (c := 1)
      ((ha n).mul (Lp.aestronglyMeasurable _))
    exact Eventually.of_forall fun x => by
      change ‖a n x * output k z x‖ ≤ 1 * ‖output k z x‖
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (VectorRadial.coefficient_nonneg _ _), one_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (VectorRadial.coefficient_le_one _ _)
  let q : ℕ → ι → Lp ℝ 2 ρ := fun n k => (hq n k).toLp _
  have hql (k : ι) : Tendsto (fun n => q n k) atTop (𝓝 0) := by
    have ht := tendsto_toLp_of_dominated (fun n => hq n k)
      (MemLp.zero : MemLp (0 : E → ℝ) 2 ρ) (Lp.memLp (output k z)).norm
      (fun n => Eventually.of_forall fun x => by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (VectorRadial.coefficient_nonneg _ _)]
        exact mul_le_of_le_one_left (norm_nonneg _) (VectorRadial.coefficient_le_one _ _))
      (Eventually.of_forall fun x => by simp only [Pi.zero_apply, norm_zero]; positivity) ?_
    · simpa only [MemLp.toLp_zero] using ht
    filter_upwards [hz] with x hx
    apply tendsto_const_nhds.congr'
    have hh : ∀ᶠ n : ℕ in atTop,
        ‖(WithLp.toLp 2 (fun i => F i x) : EuclideanSpace ℝ ι)‖ ≤ (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
    filter_upwards [hh] with n hn
    have he (i : ι) : a n x * F i x = 0 :=
      congrArg (fun t : EuclideanSpace ℝ ι => t i)
        (VectorRadial.truncate_of_norm_le n hn)
    change (0 : ℝ) = a n x * output k z x
    rw [hx.2 k, Finset.mul_sum]
    change 0 = ∑ i, a n x * (B x k i * F i x)
    simp only [show ∀ i, a n x * (B x k i * F i x) = 0 from
      fun i => by rw [← mul_left_comm, he i, mul_zero], Finset.sum_const_zero]
  let p : ℕ → MatrixEnergy.Jet (κ := ι) (ρ := ρ)
      (H := PiLp 2 (fun _ : ι => Domain J)) := fun n =>
    WithLp.toLp 2 (WithLp.toLp 2 (w n), WithLp.toLp 2 (q n))
  have hpg (n : ℕ) : p n ∈ graph v B ⊤ := by
    change ∀ᵐ x ∂ρ, (fun i => input v i (p n) x) ∈ (⊤ : Submodule ℝ (ι → ℝ)) ∧
      ∀ k, output k (p n) x = ∑ i, B x k i * input v i (p n) x
    filter_upwards [VectorRadial.truncateValues_ae n F,
      ae_all_iff.mpr (fun k => (hq n k).coeFn_toLp), hz] with x hx hy hz'
    refine ⟨Submodule.mem_top, fun k => ?_⟩
    change q n k x = ∑ i, B x k i * value J (w n i) x
    have hw (i : ι) : value J (w n i) x = a n x * F i x := by
      rw [hwv n i]
      exact hx i
    rw [hy k, hz'.2 k, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hw i]; ring
  have hpl : Tendsto p atTop (𝓝 0) := by
    have hb := (PiLp.continuous_toLp 2 _).tendsto _ |>.comp (tendsto_pi_nhds.mpr hwl)
    have he := (PiLp.continuous_toLp 2 _).tendsto _ |>.comp (tendsto_pi_nhds.mpr hql)
    exact (WithLp.prod_continuous_toLp 2 _ _).tendsto _ |>.comp (hb.prodMk_nhds he)
  have hc (n : ℕ) : z - p n ∈ compactCompletion hU hB hV B ⊤ := by
    apply mem_compactCompletion_of_bounded hU hB hV hC hbar B hBm hBc
      ⟨z - p n, (graph v B ⊤).sub_mem hz (hpg n)⟩ (n : ℝ)
    intro i
    filter_upwards [Lp.coeFn_sub (input v i z) (input v i (p n)), hwb n] with x hx hy
    change |input v i (z - p n) x| ≤ _
    rw [map_sub]
    rw [hx]
    exact hy i
  have hl : Tendsto (fun n => z - p n) atTop (𝓝 z) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hpl
  exact (compactGraph hU hB hV B ⊤).isClosed_topologicalClosure.mem_of_tendsto hl
    (Eventually.of_forall hc)

end BoundedAssembly
end Internal

section Identification

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  [Fintype ι] {ρ : Measure E} {U : Set E} {V : E → ℝ}
  (hU : IsOpen U) (hB : Bornology.IsBounded U)
  (hV : IsEuclideanGibbsPotential volume ρ U V)

open IntrinsicScalarCore MatrixEnergy

local instance : InnerProductSpace ℝ (ScalarForm.Domain (jet hU hB hV)) := inferInstance
local instance : InnerProductSpace ℝ
    (PiLp 2 (fun _ : ι => ScalarForm.Domain (jet hU hB hV))) := PiLp.innerProductSpace _

/-- The natural vector domain equals the compact core completion, Subsection 3.1, in the original H¹-plus-multiplier graph. This
version permits every locally continuous multiplier and every finite component
count, independent of the base dimension. -/
theorem compactCompletion_eq_graph
    {C : ℝ} (hC : 0 ≤ C)
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹ ^ 2 - C ≤
      ‖gradient V x‖ ^ 2 / 4 - Δ V x / 2)
    (B : E → Matrix ι ι ℝ) (hBc : ∀ i j, ContinuousOn (fun x => B x i j) U) :
    compactCompletion hU hB hV B ⊤ = graph (componentValue hU hB hV) B ⊤ := by
  apply le_antisymm (compactCompletion_le_graph hU hB hV B ⊤)
  apply Internal.graph_le_compactCompletion hU hB hV hC hbar B _ hBc
  intro i j
  have hh : AEStronglyMeasurable (fun x => B x i j) (ρ.restrict U) :=
    (hBc i j).aestronglyMeasurable hU.measurableSet
  rwa [Measure.restrict_eq_self_of_ae_mem (supported hU hV)] at hh

variable [DecidableEq ι]

open scoped MatrixOrder Matrix.Norms.L2Operator

/-- Natural-domain characterization in Subsection 3.1. Finite matrix
energy in the original scalar form is equivalent to being the value of a compact
core limit. Local continuity and nonnegativity suffice. The multiplier is the
canonical positive square root, without any extension of the coefficients. -/
theorem finite_energy_iff_compactCompletion
    {C : ℝ} (hC : 0 ≤ C)
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹ ^ 2 - C ≤
      ‖gradient V x‖ ^ 2 / 4 - Δ V x / 2)
    (M : E → Matrix ι ι ℝ)
    (hMc : ∀ i j, ContinuousOn (fun x => M x i j) U)
    (hM : ∀ x ∈ U, (M x).PosSemidef)
    (u : ι → (form hU hB hV).1) :
    WeightedFormDomain (form hU hB hV) M ⊤ u ↔
      ∃ z : compactCompletion hU hB hV (fun x => CFC.sqrt (M x)) ⊤,
        ∀ i, input (componentValue hU hB hV) i z.val = (u i).val := by
  have := probability hV
  let J := jet hU hB hV
  let v := componentValue (ι := ι) hU hB hV
  let B := fun x => CFC.sqrt (M x)
  have hBc : ∀ i j, ContinuousOn (fun x => B x i j) U := by
    have hm : ContinuousOn M U := continuousOn_pi.mpr fun i => continuousOn_pi.mpr (hMc i)
    have hh : ContinuousOn B U := CFC.continuousOn_sqrt.comp hm (fun x hx => (hM x hx).nonneg)
    exact fun i j => (continuous_apply j).continuousOn.comp
      ((continuous_apply i).continuousOn.comp hh (fun _ _ => mem_univ _)) (fun _ _ => mem_univ _)
  have hBm (i j : ι) : AEStronglyMeasurable (fun x => B x i j) ρ := by
    have hh := (hBc i j).aestronglyMeasurable (μ := ρ) hU.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem (supported hU hV)] at hh
  have hfac : ∀ᵐ x ∂ρ, (B x)ᵀ * B x = M x :=
    (supported hU hV).mono fun x hx => sqrt_factor (M x) (hM x hx)
  have heq := compactCompletion_eq_graph hU hB hV hC hbar B hBc
  constructor
  · intro hu
    have hq := (integrable_iff_memLp_factor M B hBm hfac (fun i => (u i).val)).mp hu.2
    let e := ScalarForm.valueEquiv J (value_injective hU hB hV)
    let w : ι → ScalarForm.Domain J := fun i => e.symm (u i)
    have hw (i : ι) : ScalarForm.value J (w i) = (u i).val :=
      congrArg Subtype.val (e.apply_symm_apply (u i))
    let q : ι → Lp ℝ 2 ρ := fun k => (hq k).toLp _
    let z : MatrixEnergy.Jet (κ := ι) (ρ := ρ)
        (H := PiLp 2 (fun _ : ι => ScalarForm.Domain J)) :=
      WithLp.toLp 2 (WithLp.toLp 2 w, WithLp.toLp 2 q)
    have hzg : z ∈ graph v B ⊤ := by
      change ∀ᵐ x ∂ρ, (fun i => input v i z x) ∈ (⊤ : Submodule ℝ (ι → ℝ)) ∧
        ∀ k, output k z x = ∑ i, B x k i * input v i z x
      filter_upwards [ae_all_iff.mpr (fun k => (hq k).coeFn_toLp)] with x hx
      refine ⟨Submodule.mem_top, fun k => ?_⟩
      change q k x = ∑ i, B x k i * ScalarForm.value J (w i) x
      simpa only [hw] using hx k
    refine ⟨⟨z, heq.symm ▸ hzg⟩, fun i => ?_⟩
    exact hw i
  · rintro ⟨z, hz⟩
    have hzg := compactCompletion_le_graph hU hB hV B ⊤ z.property
    refine ⟨Eventually.of_forall fun _ => Submodule.mem_top, ?_⟩
    apply (integrable_iff_memLp_factor M B hBm hfac (fun i => (u i).val)).mpr
    intro k
    apply (Lp.memLp (output k z.val)).ae_eq
    filter_upwards [hzg] with x hx
    simpa only [hz] using hx.2 k

end Identification
section IntrinsicHessian

open IntrinsicScalarCore MatrixEnergy
open scoped MatrixOrder Matrix.Norms.L2Operator

/-- Continuity of the Hessian on the actual smooth domain. Exterior values of the potential are unrestricted. -/
theorem continuousOn_hessianMatrix {d : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin d))} {V : EuclideanSpace ℝ (Fin d) → ℝ}
    (hU : IsOpen U) (hV : ContDiffOn ℝ (⊤ : ℕ∞) V U) (i j : Fin d) :
    ContinuousOn (fun x => hessianMatrix V x i j) U := by
  intro x hx
  have hv := hV.contDiffAt (hU.mem_nhds hx)
  have hh := (hv.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)
  have hc : ContinuousWithinAt (fun y => fderiv ℝ (fderiv ℝ V) y
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) U x :=
    ((hh.continuousAt.clm_apply continuousAt_const).clm_apply continuousAt_const).continuousWithinAt
  apply hc.congr
  · intro y hy
    exact Intrinsic.hessianMatrix_eq_second (hV.contDiffAt (hU.mem_nhds hy)) i j
  · exact Intrinsic.hessianMatrix_eq_second hv i j

/-- See Subsection 3.1 of the paper: the natural intrinsic finite-Hessian-energy
domain equals the compact smooth vector core completion. Strictly positive
curvature and the collision barrier are the analytic assumptions.
Orthonormal affine coordinates identify intrinsic vector fields
with these `d` components. -/
theorem natural_vector_core {d : ℕ} (hd : 1 ≤ d)
    {U : Set (EuclideanSpace ℝ (Fin d))} {ρ : Measure (EuclideanSpace ℝ (Fin d))}
    {V : EuclideanSpace ℝ (Fin d) → ℝ}
    (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V)
    {κ C : ℝ} (hκ : 0 < κ)
    (hcurv : ∀ x ∈ U, κ • (1 : Matrix (Fin d) (Fin d) ℝ) ≤ hessianMatrix V x)
    (hC : 0 ≤ C)
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹ ^ 2 - C ≤
      ‖gradient V x‖ ^ 2 / 4 - Δ V x / 2)
    (u : Fin d → (form hU hB hV).1) :
    WeightedFormDomain (form hU hB hV) (hessianMatrix V) ⊤ u ↔
      ∃ z : compactCompletion hU hB hV (fun x => CFC.sqrt (hessianMatrix V x)) ⊤,
        ∀ i, input (componentValue hU hB hV) i z.val = (u i).val := by
  have : NeZero d := ⟨by omega⟩
  apply finite_energy_iff_compactCompletion hU hB hV hC hbar (hessianMatrix V)
    (continuousOn_hessianMatrix hU hV.1) _ u
  intro x hx
  apply Matrix.nonneg_iff_posSemidef.mp
  exact (smul_nonneg hκ.le (show (0 : Matrix (Fin d) (Fin d) ℝ) ≤ 1 from zero_le_one)).trans
    (hcurv x hx)

end IntrinsicHessian
end Riesz2.VectorCore
