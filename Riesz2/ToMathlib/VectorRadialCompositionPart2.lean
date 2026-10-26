/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.VectorRadialComposition
public import Riesz1.ToMathlib.WeightedSobolev.BoundedProduct
public import Riesz1.ToMathlib.WeightedSobolev.TruncationGraph
public import Riesz1.ToMathlib.WeightedSobolev.PiecewiseComposition

/-!
# Radial Sobolev composition and admissible tests

Infrastructure for Subsection 3.5 and the proof of Proposition 3.6.
The scalar level-set theorem applies to bounded sums of component squares.
Clipping strictly outside the sphere removes boundedness assumptions on the input.
The complete coupled chain rule gives the diffusion-pairing sign and finite-energy
tests in the domain for bounded Euclidean Neumann realizations.

The abstract closed-Dirichlet-form case, without a gradient realization, is not
asserted here.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set Topology
open scoped BigOperators NNReal ENNReal

namespace Riesz2.VectorRadial

open Riesz1.WeightedSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsFiniteMeasure μ] {U : Set E}

/-- Finite sums in the scalar Sobolev graph (Subsection 3.1). -/
theorem sobolev_finset_sum {ι : Type*} (s : Finset ι)
    (hb : Bornology.IsBounded U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    {F : ι → E → ℝ} {G : ι → E → E}
    (hFG : ∀ i ∈ s, IsWeightedH1 μ U (F i) (G i)) :
    IsWeightedH1 μ U (fun x => ∑ i ∈ s, F i x) (fun x => ∑ i ∈ s, G i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hz := isWeightedH1_of_smoothNearClosure hb hμ
      (f := fun _ : E => (0 : ℝ))
      ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
    apply hz.congr
    · exact Eventually.of_forall fun x => by simp
    · exact Eventually.of_forall fun x => by simp
  | @insert i s hi ih =>
    have hh := (hFG i (Finset.mem_insert_self i s)).add hb hμ
      (ih (fun j hj => hFG j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi] using hh

/-- The bounded squared vector norm has its coupled weak differential (Subsection 3.1). -/
theorem sobolev_sum_sq {ι : Type*} [Fintype ι]
    (hb : Bornology.IsBounded U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    {F : ι → E → ℝ} {G : ι → E → E}
    (hFG : ∀ i, IsWeightedH1 μ U (F i) (G i)) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ i, ∀ᵐ x ∂μ, |F i x| ≤ B) :
    IsWeightedH1 μ U (fun x => ∑ i, F i x ^ 2)
      (fun x => ∑ i, (2 * F i x) • G i x) :=
  sobolev_finset_sum Finset.univ hb hμ
    (fun i _ => (hFG i).sq_of_bound hb hμ hB (hbound i))

/-- Scalar clipping in the existing Neumann graph, including both threshold levels.
This uses the realization to discharge gradient uniqueness (Subsection 3.1). -/
theorem sobolev_clip (hU : IsOpen U) (hb : Bornology.IsBounded U)
    (hμ : ∀ᵐ x ∂μ, x ∈ U) (Q : ScalarFormData μ) (hQ : IsNeumannRealization U Q)
    {F : E → ℝ} {G : E → E} (hFG : IsWeightedH1 μ U F G)
    {B : ℝ} (hB : 0 ≤ B) :
    IsWeightedH1 μ U (fun x => clipReal B (F x))
      ({x | |F x| < B}.indicator G) := by
  exact Riesz1.WeightedSobolev.Internal.graph_clip
    (P := SmoothNearClosure U) (value := id) (grad := gradient)
    (fun f hf => (memLp_of_smoothNearClosure hb hμ hf).1)
    (fun f hf => (memLp_of_smoothNearClosure hb hμ hf).2)
    hFG.1 hFG.2.1
    (fun S hS hS0 K hSb => hFG.comp_smooth hb hμ hS hS0 hSb) hB
    (level_deriv_zero hU hb hμ Q hQ hFG (-B))
    (level_deriv_zero hU hb hμ Q hQ hFG B)

/-- On every vector sphere the radial combination of weak component gradients vanishes.
This proves the sphere-locality step of the proof of Proposition 3.6, without
assuming bounded input components or any relation between the two dimensions. -/
theorem sphere_deriv_zero {ι : Type*} [Fintype ι]
    (hU : IsOpen U) (hb : Bornology.IsBounded U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    (Q : ScalarFormData μ) (hQ : IsNeumannRealization U Q)
    {F : ι → E → ℝ} {G : ι → E → E}
    (hFG : ∀ i, IsWeightedH1 μ U (F i) (G i)) (R : ℝ≥0) :
    ∀ᵐ x ∂μ, ‖(WithLp.toLp 2 (fun i => F i x) : EuclideanSpace ℝ ι)‖ = R →
      ∑ i, F i x • G i x = 0 := by
  classical
  let H : ι → E → ℝ := fun i x => clipReal ((R : ℝ) + 1) (F i x)
  let K : ι → E → E := fun i => {x | |F i x| < (R : ℝ) + 1}.indicator (G i)
  have hHK i : IsWeightedH1 μ U (H i) (K i) :=
    sobolev_clip hU hb hμ Q hQ (hFG i) (by positivity)
  have hs := sobolev_sum_sq hb hμ hHK (by positivity : 0 ≤ (R : ℝ) + 1)
    (fun i => Eventually.of_forall fun x => abs_clipReal_le_radius (by positivity))
  have hl := level_deriv_zero hU hb hμ Q hQ hs ((R : ℝ) ^ 2)
  filter_upwards [hl] with x hx hr
  have hi (i : ι) : |F i x| ≤ (R : ℝ) := by
    have he := PiLp.norm_apply_le (WithLp.toLp 2 (fun i => F i x) : EuclideanSpace ℝ ι) i
    simpa only [Real.norm_eq_abs, hr] using he
  have hH (i : ι) : H i x = F i x :=
    clipReal_eq_of_abs_le ((hi i).trans (by linarith))
  have hK (i : ι) : K i x = G i x :=
    indicator_of_mem (by dsimp; linarith [hi i]) _
  have hsq : ∑ i, H i x ^ 2 = (R : ℝ) ^ 2 := by
    simp only [hH]
    have he := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 (fun i => F i x))
    rw [hr] at he
    exact he.symm
  have hz := hx hsq
  simp only [hH, hK, mul_smul, ← Finset.smul_sum] at hz
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

namespace Internal

/-- Exterior scalar differential for the squared-radius reparametrization of Subsection 3.5. -/
theorem sqrt_coefficient_hasDerivAt {R t : ℝ} (hR : 0 < R) (ht : R ^ 2 ≤ t) :
    HasDerivAt (fun r : ℝ => 1 - R / Real.sqrt r) (R / (2 * Real.sqrt t ^ 3)) t := by
  have ht0 : 0 < t := (sq_pos_of_pos hR).trans_le ht
  have hs : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ht0)
  convert (hasDerivAt_const t (1 : ℝ)).sub
    ((hasDerivAt_const t R).div (Real.hasDerivAt_sqrt ht0.ne') hs) using 1
  field_simp
  ring

/-- A Lipschitz extension in the squared-radius variable for Subsection 3.5. -/
theorem sqrt_coefficient_lipschitz {R : ℝ} (hR : 0 < R) :
    LipschitzWith ⟨1 / (2 * R ^ 2), by positivity⟩
      (fun t : ℝ => 1 - R / Real.sqrt (max (R ^ 2) t)) := by
  let C : ℝ≥0 := ⟨1 / (2 * R ^ 2), by positivity⟩
  have hd (t : ℝ) (ht : t ∈ Ici (R ^ 2)) := sqrt_coefficient_hasDerivAt hR ht
  have hb (t : ℝ) (ht : t ∈ Ici (R ^ 2)) :
      ‖deriv (fun r : ℝ => 1 - R / Real.sqrt r) t‖₊ ≤ C := by
    rw [(hd t ht).deriv]
    change ‖R / (2 * Real.sqrt t ^ 3)‖ ≤ 1 / (2 * R ^ 2)
    have hs : R ≤ Real.sqrt t := by
      simpa only [Real.sqrt_sq hR.le] using Real.sqrt_le_sqrt ht
    have hs0 : 0 < Real.sqrt t := hR.trans_le hs
    rw [Real.norm_of_nonneg (by positivity)]
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt t ^ 3)
      (by positivity : 0 < 2 * R ^ 2)).mpr
    have hc : R ^ 3 ≤ Real.sqrt t ^ 3 := pow_le_pow_left₀ hR.le hs 3
    nlinarith
  have hl := Convex.lipschitzOnWith_of_nnnorm_deriv_le
    (fun t ht => (hd t ht).differentiableAt) hb (convex_Ici (R ^ 2))
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact (hl.dist_le_mul _ (show R ^ 2 ≤ max (R ^ 2) x from le_max_left _ _) _
      (show R ^ 2 ≤ max (R ^ 2) y from le_max_left _ _)).trans
    (mul_le_mul_of_nonneg_left (by
      simpa only [NNReal.coe_one, one_mul, id_eq] using
        (LipschitzWith.id.const_max (R ^ 2)).dist_le_mul x y)
      C.coe_nonneg)

/-- The squared-radius extension fixes zero for positive radii (Subsection 3.5). -/
theorem sqrt_coefficient_zero {R : ℝ} (hR : 0 < R) :
    (1 - R / Real.sqrt (max (R ^ 2) 0)) = 0 := by
  rw [max_eq_left (sq_nonneg _), Real.sqrt_sq hR.le, div_self hR.ne', sub_self]

/-- The scalar extension is smooth away from the cutoff level (Subsection 3.5). -/
theorem sqrt_coefficient_contDiffOn {R : ℝ} (hR : 0 < R) :
    ContDiffOn ℝ 1 (fun t : ℝ => 1 - R / Real.sqrt (max (R ^ 2) t))
      ({R ^ 2} : Set ℝ)ᶜ := by
  intro t ht
  have hne : t ≠ R ^ 2 := by simpa using ht
  rcases lt_or_gt_of_ne hne with ht | ht
  · apply ContDiffAt.contDiffWithinAt
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ht] with r hr
    rw [max_eq_left hr.le, Real.sqrt_sq hR.le, div_self hR.ne', sub_self]
  · have ht0 : t ≠ 0 := ne_of_gt ((sq_pos_of_pos hR).trans ht)
    have hs : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ((sq_pos_of_pos hR).trans ht))
    apply ContDiffAt.contDiffWithinAt
    apply ((contDiffAt_const (c := (1 : ℝ))).sub
      ((contDiffAt_const (c := R)).div (Real.contDiffAt_sqrt ht0) hs)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with r hr
    rw [max_eq_right hr.le]
    rfl


end Internal

/-- The indicator formula for the radial weak differential (Subsection 3.5).
It uses the exterior Jacobian on the strict exterior and vanishes on the closed ball.
This is a formula along Sobolev jets, not a claim of classical differentiability on
the cutoff sphere. Level locality justifies its values on the sphere and at zero. -/
def weakDifferential {ι : Type*} [Fintype ι] (R : ℝ≥0)
    (z : EuclideanSpace ℝ ι) (g : ι → E) (i : ι) : E :=
  if (R : ℝ) < ‖z‖ then
    (1 - (R : ℝ) / ‖z‖) • g i +
      ((R : ℝ) * z i / ‖z‖ ^ 3) • ∑ j, z j • g j
  else 0

/-- Bounded-input radial Sobolev composition, including sphere locality, for
the proof of Proposition 3.6 and Subsection 3.5. -/
theorem sobolev_truncate_of_bound {ι : Type*} [Fintype ι]
    (hU : IsOpen U) (hb : Bornology.IsBounded U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    (Q : ScalarFormData μ) (hQ : IsNeumannRealization U Q)
    {F : ι → E → ℝ} {G : ι → E → E}
    (hFG : ∀ i, IsWeightedH1 μ U (F i) (G i)) (R : ℝ≥0) (hR : 0 < (R : ℝ))
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ i, ∀ᵐ x ∂μ, |F i x| ≤ B) (i : ι) :
    IsWeightedH1 μ U
      (fun x => truncate R (WithLp.toLp 2 (fun j => F j x) : EuclideanSpace ℝ ι) i)
      (fun x => weakDifferential R (WithLp.toLp 2 (fun j => F j x)) (fun j => G j x) i) := by
  classical
  let A : E → ℝ := fun x => ∑ j, F j x ^ 2
  let D : E → E := fun x => ∑ j, (2 * F j x) • G j x
  let T : ℝ → ℝ := fun t => 1 - (R : ℝ) / Real.sqrt (max ((R : ℝ) ^ 2) t)
  have hAD : IsWeightedH1 μ U A D := sobolev_sum_sq hb hμ hFG hB hbound
  have hTD : IsWeightedH1 μ U (fun x => T (A x)) (fun x => deriv T (A x) • D x) :=
    Riesz1.WeightedSobolev.Internal.graph_comp_piecewise
      (P := SmoothNearClosure U) (value := id) (grad := gradient)
      (fun f hf => (memLp_of_smoothNearClosure hb hμ hf).1)
      (fun f hf => (memLp_of_smoothNearClosure hb hμ hf).2) hAD.1 hAD.2.1
      (fun S hS hS0 K hSb => hAD.comp_smooth hb hμ hS hS0 hSb)
      (Internal.sqrt_coefficient_lipschitz hR) (Internal.sqrt_coefficient_zero hR)
      (finite_singleton _) (Internal.sqrt_coefficient_contDiffOn hR)
      (fun a ha => by
        have he : a = (R : ℝ) ^ 2 := mem_singleton_iff.mp ha
        subst a
        exact level_deriv_zero hU hb hμ Q hQ hAD _)
  have hTb (x : E) : |T (A x)| ≤ 1 := by
    have hs : (R : ℝ) ≤ Real.sqrt (max ((R : ℝ) ^ 2) (A x)) := by
      calc (R : ℝ) = Real.sqrt ((R : ℝ) ^ 2) := (Real.sqrt_sq hR.le).symm
           _ ≤ _ := Real.sqrt_le_sqrt (le_max_left _ _)
    have hs0 : 0 < Real.sqrt (max ((R : ℝ) ^ 2) (A x)) := hR.trans_le hs
    dsimp only [T]
    rw [abs_le]
    constructor
    · have hdiv := (div_le_one hs0).mpr hs
      linarith
    · exact sub_le_self _ (div_nonneg R.coe_nonneg hs0.le)
  have hp := hTD.mul_of_bound hb hμ (hFG i) (by norm_num : (0 : ℝ) ≤ 1) hB
    (Eventually.of_forall hTb) (hbound i)
  have hl := level_deriv_zero hU hb hμ Q hQ hAD ((R : ℝ) ^ 2)
  apply hp.congr
  · apply Eventually.of_forall
    intro x
    let z : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun j => F j x)
    have he : A x = ‖z‖ ^ 2 := (EuclideanSpace.real_norm_sq_eq z).symm
    by_cases hz : (R : ℝ) < ‖z‖
    · have hsq : (R : ℝ) ^ 2 ≤ A x := by rw [he]; nlinarith [norm_nonneg z]
      change (1 - (R : ℝ) / Real.sqrt (max ((R : ℝ) ^ 2) (A x))) * F i x =
        coefficient R z * F i x
      rw [max_eq_right hsq, he, Real.sqrt_sq (norm_nonneg z), coefficient_of_lt_norm R hz]
    · have hle : ‖z‖ ≤ (R : ℝ) := le_of_not_gt hz
      have hsq : A x ≤ (R : ℝ) ^ 2 := by rw [he]; nlinarith [norm_nonneg z]
      change T (A x) * F i x = (truncate R z) i
      rw [truncate_of_norm_le R hle]
      change (1 - (R : ℝ) / Real.sqrt (max ((R : ℝ) ^ 2) (A x))) * F i x = 0
      rw [max_eq_left hsq, Real.sqrt_sq hR.le, div_self hR.ne', sub_self, zero_mul]
  · filter_upwards [hl] with x hx
    let z : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun j => F j x)
    have he : A x = ‖z‖ ^ 2 := (EuclideanSpace.real_norm_sq_eq z).symm
    change T (A x) • G i x + F i x • (deriv T (A x) • D x) =
      weakDifferential R z (fun j => G j x) i
    have hD : D x = (2 : ℝ) • ∑ j, F j x • G j x := by
      simp only [D, mul_smul, Finset.smul_sum]
    by_cases hz : (R : ℝ) < ‖z‖
    · have hn : ‖z‖ ≠ 0 := ne_of_gt (hR.trans hz)
      have hsq : (R : ℝ) ^ 2 < A x := by rw [he]; nlinarith [norm_nonneg z]
      have hder : deriv T (A x) = (R : ℝ) / (2 * ‖z‖ ^ 3) := by
        have heq : T =ᶠ[𝓝 (A x)] fun t => 1 - (R : ℝ) / Real.sqrt t := by
          filter_upwards [Ioi_mem_nhds hsq] with t ht
          exact congrArg (fun y => 1 - (R : ℝ) / Real.sqrt y) (max_eq_right ht.le)
        rw [heq.deriv_eq, (Internal.sqrt_coefficient_hasDerivAt hR hsq.le).deriv,
          he, Real.sqrt_sq (norm_nonneg z)]
      have hTv : T (A x) = 1 - (R : ℝ) / ‖z‖ := by
        change 1 - (R : ℝ) / Real.sqrt (max ((R : ℝ) ^ 2) (A x)) = _
        rw [max_eq_right hsq.le, he, Real.sqrt_sq (norm_nonneg z)]
      rw [hder, hTv, hD]
      simp only [weakDifferential, hz, ↓reduceIte, smul_smul]
      have hc : F i x * ((R : ℝ) / (2 * ‖z‖ ^ 3) * 2) = (R : ℝ) * F i x / ‖z‖ ^ 3 := by ring
      rw [hc]
    · have hle : ‖z‖ ≤ (R : ℝ) := le_of_not_gt hz
      have hsq : A x ≤ (R : ℝ) ^ 2 := by rw [he]; nlinarith [norm_nonneg z]
      have hTv : T (A x) = 0 := by
        change 1 - (R : ℝ) / Real.sqrt (max ((R : ℝ) ^ 2) (A x)) = 0
        rw [max_eq_left hsq, Real.sqrt_sq hR.le, div_self hR.ne', sub_self]
      simp only [weakDifferential, hz, ↓reduceIte, hTv, zero_smul, zero_add]
      rcases hsq.eq_or_lt with heq | hlt
      · rw [hx heq, smul_zero, smul_zero]
      · have heq : T =ᶠ[𝓝 (A x)] fun _ => (0 : ℝ) := by
          filter_upwards [Iio_mem_nhds hlt] with t ht
          change 1 - (R : ℝ) / Real.sqrt (max ((R : ℝ) ^ 2) t) = 0
          rw [max_eq_left ht.le, Real.sqrt_sq hR.le, div_self hR.ne', sub_self]
        rw [heq.deriv_eq, deriv_const, zero_smul, smul_zero]


omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- An L² majorant for the radial weak differential (Subsection 3.5). -/
theorem norm_weakDifferential_le {ι : Type*} [Fintype ι] (R : ℝ≥0) (z : EuclideanSpace ℝ ι) (g : ι → E) (i : ι) :
    ‖weakDifferential R z g i‖ ≤ ‖g i‖ + ∑ j, ‖g j‖ := by
  classical
  have hsum : 0 ≤ ∑ j, ‖g j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  unfold weakDifferential
  split_ifs with hz
  · have hn : 0 < ‖z‖ := R.coe_nonneg.trans_lt hz
    have hi : |z i| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z i
    have hs : ‖∑ j, z j • g j‖ ≤ ‖z‖ * ∑ j, ‖g j‖ := by
      calc _ ≤ ∑ j, ‖z j • g j‖ := norm_sum_le _ _
           _ ≤ ∑ j, ‖z‖ * ‖g j‖ := Finset.sum_le_sum fun j _ => by
             rw [norm_smul]
             exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le z j) (norm_nonneg _)
           _ = _ := (Finset.mul_sum _ _ _).symm
    have hc0 : 0 ≤ 1 - (R : ℝ) / ‖z‖ := by
      rw [← coefficient_of_lt_norm R hz]
      exact coefficient_nonneg R z
    have hc1 : 1 - (R : ℝ) / ‖z‖ ≤ 1 :=
      sub_le_self _ (div_nonneg R.coe_nonneg hn.le)
    have hk : ‖(R : ℝ) * z i / ‖z‖ ^ 3‖ * ‖z‖ ≤ 1 := by
      rw [norm_div, norm_mul, Real.norm_of_nonneg R.coe_nonneg,
        Real.norm_eq_abs, Real.norm_of_nonneg (by positivity : 0 ≤ ‖z‖ ^ 3)]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0 < ‖z‖ ^ 3)).mpr
      have hh : (R : ℝ) * |z i| ≤ ‖z‖ ^ 2 := by nlinarith
      have hh' := mul_le_mul_of_nonneg_right hh hn.le
      nlinarith
    calc _ ≤ ‖(1 - (R : ℝ) / ‖z‖) • g i‖ +
        ‖((R : ℝ) * z i / ‖z‖ ^ 3) • ∑ j, z j • g j‖ := norm_add_le _ _
         _ = (1 - (R : ℝ) / ‖z‖) * ‖g i‖ +
             ‖(R : ℝ) * z i / ‖z‖ ^ 3‖ * ‖∑ j, z j • g j‖ := by
           rw [norm_smul, norm_smul, Real.norm_of_nonneg hc0]
         _ ≤ ‖g i‖ + 1 * (∑ j, ‖g j‖) := by
           apply add_le_add
           · nlinarith [norm_nonneg (g i)]
           · calc _ ≤ ‖(R : ℝ) * z i / ‖z‖ ^ 3‖ * (‖z‖ * ∑ j, ‖g j‖) :=
                    mul_le_mul_of_nonneg_left hs (norm_nonneg _)
                  _ ≤ _ := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hk hsum
         _ = _ := by ring
  · simpa only [norm_zero] using add_nonneg (norm_nonneg (g i)) hsum


/-- Coupled radial composition in the intrinsic Sobolev graph, with the complete weak
differential including zero and the cutoff sphere (the proof of Proposition 3.6). -/
theorem sobolev_truncate {ι : Type*} [Fintype ι]
    (hU : IsOpen U) (hb : Bornology.IsBounded U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    (Q : ScalarFormData μ) (hQ : IsNeumannRealization U Q)
    {F : ι → E → ℝ} {G : ι → E → E}
    (hFG : ∀ i, IsWeightedH1 μ U (F i) (G i)) (R : ℝ≥0) (i : ι) :
    IsWeightedH1 μ U
      (fun x => truncate R (WithLp.toLp 2 (fun j => F j x) : EuclideanSpace ℝ ι) i)
      (fun x => weakDifferential R (WithLp.toLp 2 (fun j => F j x)) (fun j => G j x) i) := by
  classical
  rcases eq_or_lt_of_le R.coe_nonneg with hR | hR
  · have hR0 : R = 0 := NNReal.coe_eq_zero.mp hR.symm
    subst R
    have hl := point_level_deriv_zero_of_closable hU hb hμ
      (value_injective_of_neumannRealization hU hb hμ Q hQ) hFG (fun _ => 0)
    apply (hFG i).congr
    · exact Eventually.of_forall fun x => by simp only [truncate_radius_zero]
    · filter_upwards [hl] with x hx
      let z : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun j => F j x)
      change G i x = weakDifferential 0 z (fun j => G j x) i
      by_cases hz : 0 < ‖z‖
      · simp [weakDifferential, hz]
      · have hz0 : z = 0 := norm_eq_zero.mp (le_antisymm (le_of_not_gt hz) (norm_nonneg z))
        have hF0 (j : ι) : F j x = 0 := by
          have he := congrArg (fun y : EuclideanSpace ℝ ι => y j) hz0
          exact he
        simp [weakDifferential, hz, hx hF0 i]
  let H : ℕ → ι → E → ℝ := fun n j x => clipReal n (F j x)
  let K : ℕ → ι → E → E := fun n j => {x | |F j x| < (n : ℝ)}.indicator (G j)
  have hHK (n : ℕ) (j : ι) : IsWeightedH1 μ U (H n j) (K n j) :=
    sobolev_clip hU hb hμ Q hQ (hFG j) (Nat.cast_nonneg n)
  let f : ℕ → E → ℝ := fun n x =>
    truncate R (WithLp.toLp 2 (fun j => H n j x) : EuclideanSpace ℝ ι) i
  let g : ℕ → E → E := fun n x =>
    weakDifferential R (WithLp.toLp 2 (fun j => H n j x)) (fun j => K n j x) i
  let V : E → ℝ := fun x =>
    truncate R (WithLp.toLp 2 (fun j => F j x) : EuclideanSpace ℝ ι) i
  let W : E → E := fun x =>
    weakDifferential R (WithLp.toLp 2 (fun j => F j x)) (fun j => G j x) i
  have hfg (n : ℕ) : IsWeightedH1 μ U (f n) (g n) :=
    sobolev_truncate_of_bound hU hb hμ Q hQ (hHK n) R hR (Nat.cast_nonneg n)
      (fun j => Eventually.of_forall fun x => abs_clipReal_le_radius (Nat.cast_nonneg n)) i
  have heq (x : E) : ∀ᶠ n : ℕ in atTop, f n x = V x ∧ g n x = W x := by
    have hh : ∀ᶠ n : ℕ in atTop, ∀ j, |F j x| < (n : ℝ) :=
      eventually_all.mpr (fun j => tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _))
    filter_upwards [hh] with n hn
    have hH (j : ι) : H n j x = F j x := clipReal_eq_of_abs_le (hn j).le
    have hK (j : ι) : K n j x = G j x := indicator_of_mem (show x ∈ {x | |F j x| < (n : ℝ)} from hn j) _
    constructor <;> simp only [f, V, g, W, hH, hK]
  have hfLim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (V x)) :=
    Eventually.of_forall fun x => tendsto_const_nhds.congr' ((heq x).mono fun n hn => hn.1.symm)
  have hgLim : ∀ᵐ x ∂μ, Tendsto (fun n => g n x) atTop (𝓝 (W x)) :=
    Eventually.of_forall fun x => tendsto_const_nhds.congr' ((heq x).mono fun n hn => hn.2.symm)
  let b : E → ℝ := fun x => ‖G i x‖ + ∑ j, ‖G j x‖
  have hbLp : MemLp b 2 μ :=
    (hFG i).2.1.norm.add (memLp_finsetSum _ (fun j _ => (hFG j).2.1.norm))
  have hgb (n : ℕ) : ∀ᵐ x ∂μ, ‖g n x‖ ≤ b x := by
    apply Eventually.of_forall
    intro x
    apply (norm_weakDifferential_le R _ _ i).trans
    apply add_le_add
    · exact norm_indicator_le_norm_self _ _
    · exact Finset.sum_le_sum fun j _ => norm_indicator_le_norm_self _ _
  have hWb : ∀ᵐ x ∂μ, ‖W x‖ ≤ b x :=
    Eventually.of_forall fun x => norm_weakDifferential_le R _ _ i
  have hW : MemLp W 2 μ := hbLp.mono'
    (aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hfg n).2.1.aestronglyMeasurable) hgLim) hWb
  have hfb (n : ℕ) : ∀ᵐ x ∂μ, ‖f n x‖ ≤ |F i x| := by
    apply Eventually.of_forall
    intro x
    let z : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun j => H n j x)
    change |coefficient R z * H n i x| ≤ |F i x|
    rw [abs_mul, abs_of_nonneg (coefficient_nonneg R z)]
    exact (mul_le_of_le_one_left (abs_nonneg _) (coefficient_le_one R z)).trans
      (abs_clipReal_le (Nat.cast_nonneg n))
  have hVb : ∀ᵐ x ∂μ, ‖V x‖ ≤ |F i x| := by
    apply Eventually.of_forall
    intro x
    let z : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun j => F j x)
    change |coefficient R z * F i x| ≤ |F i x|
    rw [abs_mul, abs_of_nonneg (coefficient_nonneg R z)]
    exact mul_le_of_le_one_left (abs_nonneg _) (coefficient_le_one R z)
  have hV : MemLp V 2 μ := (hFG i).1.norm.mono'
    (aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hfg n).1.aestronglyMeasurable) hfLim) hVb
  exact Riesz1.WeightedSobolev.Internal.graph_closed_limit
    (P := SmoothNearClosure U) (value := id) (grad := gradient)
    (fun f hf => (memLp_of_smoothNearClosure hb hμ hf).1)
    (fun f hf => (memLp_of_smoothNearClosure hb hμ hf).2) hfg hV hW
    (tendsto_toLp_of_dominated (fun n => (hfg n).1) hV (hFG i).1.norm hfb hVb hfLim)
    (tendsto_toLp_of_dominated (fun n => (hfg n).2.1) hW hbLp hgb hWb hgLim)


omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Pointwise diffusion-pairing sign for the proof of Proposition 3.6. -/
theorem sum_inner_weakDifferential_nonneg {ι : Type*} [Fintype ι] (R : ℝ≥0) (z : EuclideanSpace ℝ ι) (g : ι → E) :
    0 ≤ ∑ i, inner ℝ (g i) (weakDifferential R z g i) := by
  classical
  by_cases hz : (R : ℝ) < ‖z‖
  · have he : (∑ i, inner ℝ (g i) (weakDifferential R z g i)) =
        (1 - (R : ℝ) / ‖z‖) * ∑ i, ‖g i‖ ^ 2 +
          ((R : ℝ) / ‖z‖ ^ 3) * ‖∑ j, z j • g j‖ ^ 2 := by
      simp only [weakDifferential, hz, ↓reduceIte, inner_add_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq, Finset.sum_add_distrib, ← Finset.mul_sum]
      congr 1
      rw [← real_inner_self_eq_norm_sq, sum_inner]
      simp only [real_inner_smul_left]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    have hc : 0 ≤ 1 - (R : ℝ) / ‖z‖ := by
      rw [← coefficient_of_lt_norm R hz]
      exact coefficient_nonneg R z
    exact add_nonneg (mul_nonneg hc (Finset.sum_nonneg fun _ _ => sq_nonneg _))
      (mul_nonneg (div_nonneg R.coe_nonneg (pow_nonneg (norm_nonneg z) _)) (sq_nonneg _))
  · simp only [weakDifferential, hz, ↓reduceIte, inner_zero_right, Finset.sum_const_zero, le_refl]


/-- In a bounded Euclidean Neumann realization, radial truncation belongs to the scalar form domain and has nonnegative diffusion pairing
(the proof of Proposition 3.6). No membership assumption on the test is used. -/
theorem exists_truncation_neumann {ι : Type*} [Fintype ι]
    (hU : IsOpen U) (hb : Bornology.IsBounded U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    (Q : ScalarFormData μ) (hQ : IsNeumannRealization U Q)
    (R : ℝ≥0) (u : ι → Q.1) :
    ∃ h : ι → Q.1, (∀ i, (h i).val = truncateValues R (fun j => (u j).val) i) ∧
      0 ≤ ∑ i, Q.2 (u i) (h i) := by
  classical
  have hG (i : ι) := (hQ.1 (u i).val).mp (u i).property
  choose g hg using hG
  have hFG (i : ι) : IsWeightedH1 μ U (u i).val (g i) := by
    apply (isWeightedH1_iff_neumannSobolevGraph hb hμ (Lp.memLp _) (Lp.memLp _)).mpr
    simpa only [Lp.toLp_coeFn] using hg i
  let D : ι → E → E := fun i x => weakDifferential R
    (WithLp.toLp 2 (fun j => (u j).val x)) (fun j => g j x) i
  have hT (i : ι) := sobolev_truncate hU hb hμ Q hQ hFG R i
  have hjet (i : ι) :
      (truncateValues R (fun j => (u j).val) i, (hT i).2.1.toLp (D i)) ∈
        neumannSobolevGraph μ U :=
    (isWeightedH1_iff_neumannSobolevGraph hb hμ (hT i).1 (hT i).2.1).mp (hT i)
  let h : ι → Q.1 := fun i =>
    ⟨truncateValues R (fun j => (u j).val) i, (hQ.1 _).mpr ⟨_, hjet i⟩⟩
  refine ⟨h, fun _ => rfl, ?_⟩
  have hi (i : ι) : Integrable (fun x => inner ℝ (g i x) (D i x)) μ := by
    apply (L2.integrable_inner (𝕜 := ℝ) (g i) ((hT i).2.1.toLp (D i))).congr
    filter_upwards [(hT i).2.1.coeFn_toLp] with x hx
    rw [hx]
  have he (i : ι) : Q.2 (u i) (h i) = ∫ x, inner ℝ (g i x) (D i x) ∂μ := by
    rw [hQ.2.2 (u i) (h i) (g i) ((hT i).2.1.toLp (D i)) (hg i) (hjet i),
      L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hT i).2.1.coeFn_toLp] with x hx
    rw [hx]
  simp only [he]
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  exact integral_nonneg fun x => sum_inner_weakDifferential_nonneg R _ _

/-- Admissible finite-energy radial tests for bounded Euclidean Neumann realizations,
using the actual `WeightedFormDomain` (Subsection 3.5 and
the proof of Proposition 3.6). This includes every fixed component subspace
and measurable nonnegative matrices with no upper bound. -/
theorem admissible_truncation_neumann {ι : Type*} [Fintype ι]
    (hU : IsOpen U) (hb : Bornology.IsBounded U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    (Q : ScalarFormData μ) (hQ : IsNeumannRealization U Q)
    (M : E → Matrix ι ι ℝ) (S : Submodule ℝ (ι → ℝ))
    (hMmeas : ∀ i j, Measurable (fun x => M x i j))
    (hM : ∀ᵐ x ∂μ, (M x).PosSemidef) (R : ℝ≥0) (u : ι → Q.1)
    (hu : WeightedFormDomain Q M S u) :
    ∃ h : ι → Q.1,
      (∀ i, (h i).val = truncateValues R (fun j => (u j).val) i) ∧
      WeightedFormDomain Q M S h ∧ 0 ≤ ∑ i, Q.2 (u i) (h i) ∧
      (∫ x, matrixFieldPair M (fun i => (h i).val) (fun i => (h i).val) x ∂μ) ≤
        ∫ x, matrixFieldPair M (fun i => (u i).val) (fun i => (u i).val) x ∂μ := by
  obtain ⟨h, hh, hsign⟩ := exists_truncation_neumann hU hb hμ Q hQ R u
  refine ⟨h, hh, Internal.weightedFormDomain_of_truncateValues R Q M S hMmeas hM u h hu hh,
    hsign, ?_⟩
  simp only [hh]
  exact integral_matrixFieldPair_truncateValues_le R M hMmeas hM _ hu.2


end Riesz2.VectorRadial
