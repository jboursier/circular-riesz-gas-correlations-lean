/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.MatrixEnergySpaces
public import Riesz2.Frozen.IsNeumannRealization
public import Riesz1.ToMathlib.WeightedSobolev.BoundedDomainComposition
public import Riesz1.ToMathlib.WeightedSobolev.LevelSetGraph
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Radial truncation of finite vectors

Infrastructure for Subsection 3.5 and the radial tests of
the proof of Proposition 3.6. Radii are nonnegative real numbers.
The formula at zero uses the continuous value of the vector map.

The finite-energy bridge is an internal conditional interface: scalar Sobolev
membership of the truncated values must still be established separately.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set Topology
open scoped BigOperators NNReal ENNReal

namespace Riesz2.VectorRadial

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Scalar multiplier of the radial excess outside a ball (Subsection 3.5). -/
def coefficient (R : ℝ≥0) (z : V) : ℝ := max 0 (1 - (R : ℝ) / ‖z‖)

/-- Radial excess `T_R(z) = (1 - R / ‖z‖)₊ z` (Subsection 3.5).
At zero the scalar multiplier is one and the vector is zero, giving exactly
the continuous value. No arbitrary extension of the vector map is used. -/
def truncate (R : ℝ≥0) (z : V) : V := coefficient R z • z

omit [InnerProductSpace ℝ V] in
theorem coefficient_nonneg (R : ℝ≥0) (z : V) : 0 ≤ coefficient R z := le_max_left _ _

omit [InnerProductSpace ℝ V] in
theorem coefficient_le_one (R : ℝ≥0) (z : V) : coefficient R z ≤ 1 := by
  apply max_le zero_le_one
  have := div_nonneg R.coe_nonneg (norm_nonneg z)
  linarith

theorem truncate_zero (R : ℝ≥0) : truncate R (0 : V) = 0 := smul_zero _

theorem truncate_radius_zero (z : V) : truncate 0 z = z := by
  simp [truncate, coefficient]

theorem truncate_of_norm_le (R : ℝ≥0) {z : V} (hz : ‖z‖ ≤ R) : truncate R z = 0 := by
  by_cases h0 : z = 0
  · rw [h0, truncate_zero]
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr h0
  have hd : 1 ≤ (R : ℝ) / ‖z‖ := (le_div_iff₀ hn).mpr (by simpa using hz)
  have hb : coefficient R z = 0 := max_eq_left (by linarith)
  rw [truncate, hb, zero_smul]

omit [InnerProductSpace ℝ V] in
theorem coefficient_of_lt_norm (R : ℝ≥0) {z : V} (hz : (R : ℝ) < ‖z‖) :
    coefficient R z = 1 - (R : ℝ) / ‖z‖ := by
  apply max_eq_right
  have hn : 0 < ‖z‖ := lt_of_le_of_lt R.coe_nonneg hz
  have hd : (R : ℝ) / ‖z‖ < 1 := (div_lt_one hn).mpr hz
  linarith

/-- The norm is the scalar positive part, including zero and the sphere (Subsection 3.5). -/
theorem norm_truncate (R : ℝ≥0) (z : V) : ‖truncate R z‖ = max 0 (‖z‖ - R) := by
  by_cases hz : ‖z‖ ≤ R
  · rw [truncate_of_norm_le R hz, norm_zero, max_eq_left (sub_nonpos.mpr hz)]
  have hz' : (R : ℝ) < ‖z‖ := lt_of_not_ge hz
  have hn : ‖z‖ ≠ 0 := ne_of_gt (lt_of_le_of_lt R.coe_nonneg hz')
  rw [truncate, norm_smul, Real.norm_of_nonneg (coefficient_nonneg R z),
    coefficient_of_lt_norm R hz', max_eq_right (sub_nonneg.mpr hz'.le)]
  field_simp

theorem norm_truncate_le (R : ℝ≥0) (z : V) : ‖truncate R z‖ ≤ ‖z‖ := by
  rw [norm_truncate]
  exact max_le (norm_nonneg _) (sub_le_self _ R.coe_nonneg)

/-- The removed part lies in the closed ball, also at radius zero. -/
theorem norm_sub_truncate_le (R : ℝ≥0) (z : V) : ‖z - truncate R z‖ ≤ R := by
  have he : z - truncate R z = (1 - coefficient R z) • z := by
    rw [sub_smul, one_smul, truncate]
  rw [he, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr (coefficient_le_one R z))]
  by_cases hz : ‖z‖ ≤ R
  · have hb : 0 ≤ coefficient R z * ‖z‖ := mul_nonneg (coefficient_nonneg R z) (norm_nonneg z)
    nlinarith
  have hz' := lt_of_not_ge hz
  rw [coefficient_of_lt_norm R hz']
  have hn : ‖z‖ ≠ 0 := ne_of_gt (lt_of_le_of_lt R.coe_nonneg hz')
  field_simp
  linarith

/-- The removed component minimizes distance to the closed ball (Subsection 3.5). -/
theorem sub_truncate_minimizes (R : ℝ≥0) (z : V) {y : V} (hy : ‖y‖ ≤ R) :
    ‖z - (z - truncate R z)‖ ≤ ‖z - y‖ := by
  rw [sub_sub_cancel, norm_truncate]
  apply max_le (norm_nonneg _)
  have h : ‖z‖ ≤ ‖z - y‖ + ‖y‖ := by
    simpa only [norm_sub_rev, add_comm] using norm_le_insert y z
  linarith

/-- Complementarity of the radial excess and the removed ball component. -/
theorem inner_truncate_sub (R : ℝ≥0) (z : V) :
    inner ℝ (truncate R z) (z - truncate R z) = (R : ℝ) * ‖truncate R z‖ := by
  by_cases hz : ‖z‖ ≤ R
  · simp [truncate_of_norm_le R hz]
  have hz' := lt_of_not_ge hz
  have hn : ‖z‖ ≠ 0 := ne_of_gt (lt_of_le_of_lt R.coe_nonneg hz')
  rw [inner_sub_right, truncate, real_inner_smul_left, inner_smul_right,
    real_inner_smul_left, real_inner_self_eq_norm_sq,
    norm_smul, Real.norm_of_nonneg (coefficient_nonneg R z), coefficient_of_lt_norm R hz']
  field_simp
  ring

/-- Firm monotonicity of the radial excess, the pointwise sign needed by nonlocal
Dirichlet forms (the proof of Proposition 3.6). -/
theorem firm (R : ℝ≥0) (z w : V) :
    ‖truncate R z - truncate R w‖ ^ 2 ≤
      inner ℝ (truncate R z - truncate R w) (z - w) := by
  have hcross (a b : V) :
      inner ℝ (truncate R a) (b - truncate R b) ≤ (R : ℝ) * ‖truncate R a‖ := by
    exact (real_inner_le_norm _ _).trans (by
      nlinarith [norm_sub_truncate_le R b, norm_nonneg (truncate R a)])
  have hc : 0 ≤ inner ℝ (truncate R z - truncate R w)
      ((z - truncate R z) - (w - truncate R w)) := by
    have hz := inner_truncate_sub R z
    have hw := inner_truncate_sub R w
    have hzw := hcross z w
    have hwz := hcross w z
    simp only [inner_sub_left, inner_sub_right] at hz hw hzw hwz ⊢
    linarith
  have he : z - w = (truncate R z - truncate R w) +
      ((z - truncate R z) - (w - truncate R w)) := by abel
  rw [he, inner_add_right, real_inner_self_eq_norm_sq]
  linarith

theorem monotone (R : ℝ≥0) (z w : V) :
    0 ≤ inner ℝ (truncate R z - truncate R w) (z - w) :=
  (sq_nonneg _).trans (firm R z w)

/-- The radial excess is 1-Lipschitz in the Hilbert norm (Subsection 3.5). -/
theorem lipschitzWith_truncate (R : ℝ≥0) : LipschitzWith 1 (truncate (V := V) R) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have h := (firm R z w).trans (real_inner_le_norm _ _)
  nlinarith [norm_nonneg (truncate R z - truncate R w), norm_nonneg (z - w)]

theorem continuous_truncate (R : ℝ≥0) : Continuous (truncate (V := V) R) :=
  (lipschitzWith_truncate R).continuous

/-- Radial truncation respects every fixed real component subspace. -/
theorem truncate_mem (R : ℝ≥0) (S : Submodule ℝ V) {z : V} (hz : z ∈ S) :
    truncate R z ∈ S := S.smul_mem _ hz

/-- Every convex combination of the identity and the ball projection is contractive.
This is the map used in the short-time Dirichlet-form argument. -/
theorem lipschitzWith_sub_truncate (R : ℝ≥0) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    LipschitzWith 1 (fun z : V => z - ε • truncate R z) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have he : (z - ε • truncate R z) - (w - ε • truncate R w) =
      (z - w) - ε • (truncate R z - truncate R w) := by module
  rw [he]
  have hi := firm R z w
  have hexp : ‖(z - w) - ε • (truncate R z - truncate R w)‖ ^ 2 =
      ‖z - w‖ ^ 2 - 2 * ε * inner ℝ (truncate R z - truncate R w) (z - w) +
        ε ^ 2 * ‖truncate R z - truncate R w‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm (z - w),
      norm_smul, Real.norm_of_nonneg hε]
    ring
  have he2 : ε ^ 2 ≤ 2 * ε := by nlinarith
  have hn := sq_nonneg ‖truncate R z - truncate R w‖
  have hi' := mul_le_mul_of_nonneg_left hi hε
  nlinarith [norm_nonneg ((z - w) - ε • (truncate R z - truncate R w)), norm_nonneg (z - w)]

/-- Classical derivative of the norm away from zero, in the supplied real metric. -/
theorem hasFDerivAt_norm {z : V} (hz : z ≠ 0) :
    HasFDerivAt (fun y : V => ‖y‖) (‖z‖⁻¹ • innerSL ℝ z) z := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have h := (hasStrictFDerivAt_norm_sq z).hasFDerivAt.sqrt (pow_ne_zero 2 hn)
  simp only [Real.sqrt_sq (norm_nonneg _)] at h
  have he : ‖z‖⁻¹ • innerSL ℝ z = (1 / (2 * ‖z‖)) • (2 • innerSL ℝ z) := by
    ext v
    simp only [smul_apply, innerSL_apply_apply, two_smul, add_apply, smul_eq_mul]
    field_simp
    ring
  rw [he]
  exact h

/-- Classical derivative off the cutoff sphere, on the exterior side (Subsection 3.5). -/
theorem hasFDerivAt_truncate_outside (R : ℝ≥0) {z : V} (hz : (R : ℝ) < ‖z‖) :
    HasFDerivAt (truncate R)
      ((1 - (R : ℝ) / ‖z‖) • ContinuousLinearMap.id ℝ V +
        ((R : ℝ) / ‖z‖ ^ 3) • (innerSL ℝ z).smulRight z) z := by
  have hn : ‖z‖ ≠ 0 := ne_of_gt (lt_of_le_of_lt R.coe_nonneg hz)
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp hn
  have hs := (hasDerivAt_const ‖z‖ (1 : ℝ)).sub
    ((hasDerivAt_const ‖z‖ (R : ℝ)).div (hasDerivAt_id ‖z‖) hn)
  have hb := hs.comp_hasFDerivAt z (hasFDerivAt_norm hz0)
  have h := hb.smul (hasFDerivAt_id z)
  have hder : (1 - (R : ℝ) / ‖z‖) • ContinuousLinearMap.id ℝ V +
      ((R : ℝ) / ‖z‖ ^ 3) • (innerSL ℝ z).smulRight z =
      (1 - (R : ℝ) / ‖z‖) • ContinuousLinearMap.id ℝ V +
        ((0 - (0 * ‖z‖ - (R : ℝ) * 1) / ‖z‖ ^ 2) •
          (‖z‖⁻¹ • innerSL ℝ z)).smulRight z := by
    ext v
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul, zero_sub, zero_mul,
      smul_smul, mul_one]
    congr 2
    field_simp
  rw [hder]
  apply h.congr_of_eventuallyEq
  filter_upwards [continuous_norm.continuousAt.eventually (Ioi_mem_nhds hz)] with y hy
  simp only [truncate, coefficient_of_lt_norm R hy]
  rfl

/-- On the open interior of the ball the classical derivative is zero (Subsection 3.5). -/
theorem hasFDerivAt_truncate_inside (R : ℝ≥0) {z : V} (hz : ‖z‖ < R) :
    HasFDerivAt (truncate R) (0 : V →L[ℝ] V) z := by
  apply (hasFDerivAt_const (0 : V) z).congr_of_eventuallyEq
  filter_upwards [continuous_norm.continuousAt.eventually (Iio_mem_nhds hz)] with y hy
  exact truncate_of_norm_le R hy.le

/-- Radial eigenvalue of the exterior derivative (Subsection 3.5). -/
theorem fderiv_truncate_radial (R : ℝ≥0) {z : V} (hz : (R : ℝ) < ‖z‖) :
    fderiv ℝ (truncate R) z z = z := by
  rw [(hasFDerivAt_truncate_outside R hz).fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, real_inner_self_eq_norm_sq, smul_smul, ← add_smul]
  have hn : ‖z‖ ≠ 0 := ne_of_gt (lt_of_le_of_lt R.coe_nonneg hz)
  have hc : 1 - (R : ℝ) / ‖z‖ + (R : ℝ) / ‖z‖ ^ 3 * ‖z‖ ^ 2 = 1 := by field_simp; ring
  rw [hc, one_smul]

/-- Transverse eigenvalue of the exterior derivative (Subsection 3.5). -/
theorem fderiv_truncate_transverse (R : ℝ≥0) {z v : V} (hz : (R : ℝ) < ‖z‖)
    (hv : inner ℝ z v = 0) :
    fderiv ℝ (truncate R) z v = (1 - (R : ℝ) / ‖z‖) • v := by
  rw [(hasFDerivAt_truncate_outside R hz).fderiv]
  simp [hv]

/-- The exterior differential has a nonnegative quadratic form, in any base direction.
The sphere itself requires the weak level-set argument. -/
theorem inner_fderiv_truncate_nonneg (R : ℝ≥0) {z : V} (hz : (R : ℝ) < ‖z‖) (v : V) :
    0 ≤ inner ℝ v (fderiv ℝ (truncate R) z v) := by
  rw [(hasFDerivAt_truncate_outside R hz).fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_add_right,
    inner_smul_right, real_inner_self_eq_norm_sq, real_inner_comm z v]
  have hc : 0 ≤ 1 - (R : ℝ) / ‖z‖ := by
    rw [← coefficient_of_lt_norm R hz]
    exact coefficient_nonneg R z
  have hr : 0 ≤ (R : ℝ) / ‖z‖ ^ 3 := div_nonneg R.coe_nonneg (pow_nonneg (norm_nonneg _) _)
  nlinarith [mul_nonneg hr (sq_nonneg (inner ℝ v z)), mul_nonneg hc (sq_nonneg ‖v‖)]

section Lp

variable {α : Type*} [MeasurableSpace α] {ρ : Measure α}

/-- Radial excess preserves every Lᵖ space, with no boundedness assumption on the measure. -/
theorem memLp_truncate {p : ℝ≥0∞} (R : ℝ≥0) {u : α → V} (hu : MemLp u p ρ) :
    MemLp (fun x => truncate R (u x)) p ρ :=
  (lipschitzWith_truncate R).comp_memLp (truncate_zero R) hu

/-- Strong L² continuity of radial truncation in the input field. -/
theorem continuous_compLp_truncate (R : ℝ≥0) :
    Continuous ((lipschitzWith_truncate (V := V) R).compLp (p := 2) (μ := ρ) (truncate_zero R)) :=
  (lipschitzWith_truncate R).continuous_compLp (truncate_zero R)

/-- The excess outside growing balls tends to zero in L². -/
theorem tendsto_toLp_truncate {u : α → V} (hu : MemLp u 2 ρ) :
    Tendsto (fun n : ℕ => (memLp_truncate (n : ℝ≥0) hu).toLp
      (fun x => truncate (n : ℝ≥0) (u x))) atTop (𝓝 0) := by
  have h := Riesz1.WeightedSobolev.tendsto_toLp_of_dominated
    (fun n : ℕ => memLp_truncate (n : ℝ≥0) hu) (MemLp.zero' (μ := ρ) (p := 2) (ε := V))
    hu.norm (fun n => Eventually.of_forall fun x => norm_truncate_le n (u x))
    (Eventually.of_forall fun x => by simpa only [norm_zero] using norm_nonneg (u x)) ?_
  · have hz : (MemLp.zero' (μ := ρ) (p := 2) (ε := V)).toLp (fun _ => 0) = 0 := by
      apply Lp.ext
      exact (MemLp.zero' (μ := ρ) (p := 2) (ε := V)).coeFn_toLp.trans (Lp.coeFn_zero _ _ _).symm
    rw [hz] at h
    exact h
  apply Eventually.of_forall
  intro x
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (⌈‖u x‖⌉₊)] with n hn
  exact (truncate_of_norm_le n ((Nat.le_ceil ‖u x‖).trans (by exact_mod_cast hn))).symm

end Lp

section FiniteValues

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι] {ρ : Measure α}

/-- A finite tuple of scalar L² functions, viewed in the Euclidean component metric. -/
theorem memLp_values (u : ι → Lp ℝ 2 ρ) :
    MemLp (fun x => (WithLp.toLp 2 (fun i => u i x) : EuclideanSpace ℝ ι)) 2 ρ :=
  memLp_piLp_iff.mpr (fun i => Lp.memLp (u i))

/-- Radially truncate the values of a finite tuple of L² classes. -/
def truncateValues (R : ℝ≥0) (u : ι → Lp ℝ 2 ρ) (i : ι) : Lp ℝ 2 ρ :=
  ((memLp_truncate R (memLp_values u)).eval_piLp i).toLp
    (fun x => truncate R (WithLp.toLp 2 (fun j => u j x) : EuclideanSpace ℝ ι) i)

/-- Simultaneous representative identity for every component of the truncation. -/
theorem truncateValues_ae (R : ℝ≥0) (u : ι → Lp ℝ 2 ρ) :
    ∀ᵐ x ∂ρ, ∀ i, truncateValues R u i x =
      coefficient R (WithLp.toLp 2 (fun j => u j x) : EuclideanSpace ℝ ι) * u i x := by
  apply ae_all_iff.mpr
  intro i
  exact ((memLp_truncate R (memLp_values u)).eval_piLp i).coeFn_toLp

/-- Radial values remain in any prescribed fixed component subspace. -/
theorem truncateValues_mem (R : ℝ≥0) (u : ι → Lp ℝ 2 ρ) (S : Submodule ℝ (ι → ℝ))
    (hu : ∀ᵐ x ∂ρ, (fun i => u i x) ∈ S) :
    ∀ᵐ x ∂ρ, (fun i => truncateValues R u i x) ∈ S := by
  filter_upwards [hu, truncateValues_ae R u] with x hx he
  have hv : (fun i => truncateValues R u i x) =
      coefficient R (WithLp.toLp 2 (fun i => u i x) : EuclideanSpace ℝ ι) • (fun i => u i x) :=
    funext he
  rw [hv]
  exact S.smul_mem _ hx

/-- The matrix integrand scales by the square of the radial coefficient. -/
theorem matrixFieldPair_truncateValues (R : ℝ≥0) (M : α → Matrix ι ι ℝ)
    (u : ι → Lp ℝ 2 ρ) :
    matrixFieldPair M (truncateValues R u) (truncateValues R u) =ᵐ[ρ]
      fun x => coefficient R (WithLp.toLp 2 (fun i => u i x) : EuclideanSpace ℝ ι) ^ 2 *
        matrixFieldPair M u u x := by
  filter_upwards [truncateValues_ae R u] with x hx
  simp only [matrixFieldPair, hx, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A nonnegative matrix energy decreases pointwise under radial truncation. -/
theorem matrixFieldPair_truncateValues_le (R : ℝ≥0) (M : α → Matrix ι ι ℝ)
    (hM : ∀ᵐ x ∂ρ, (M x).PosSemidef) (u : ι → Lp ℝ 2 ρ) :
    ∀ᵐ x ∂ρ, 0 ≤ matrixFieldPair M (truncateValues R u) (truncateValues R u) x ∧
      matrixFieldPair M (truncateValues R u) (truncateValues R u) x ≤ matrixFieldPair M u u x := by
  filter_upwards [hM, matrixFieldPair_truncateValues R M u] with x hx he
  have hp : 0 ≤ matrixFieldPair M u u x := by
    rw [MatrixEnergy.matrixFieldPair_eq_dot]
    simpa only [star_trivial] using hx.dotProduct_mulVec_nonneg (fun i => u i x)
  rw [he]
  have hb0 := coefficient_nonneg R (WithLp.toLp 2 (fun i => u i x) : EuclideanSpace ℝ ι)
  have hb1 := coefficient_le_one R (WithLp.toLp 2 (fun i => u i x) : EuclideanSpace ℝ ι)
  constructor
  · positivity
  · nlinarith [mul_nonneg hp (show 0 ≤ 1 -
      coefficient R (WithLp.toLp 2 (fun i => u i x) : EuclideanSpace ℝ ι) ^ 2 by nlinarith)]

/-- Absolute integrability of the full unbounded matrix energy is preserved. -/
theorem integrable_matrixFieldPair_truncateValues (R : ℝ≥0) (M : α → Matrix ι ι ℝ)
    (hMmeas : ∀ i j, Measurable (fun x => M x i j))
    (hM : ∀ᵐ x ∂ρ, (M x).PosSemidef) (u : ι → Lp ℝ 2 ρ)
    (hu : Integrable (matrixFieldPair M u u) ρ) :
    Integrable (matrixFieldPair M (truncateValues R u) (truncateValues R u)) ρ := by
  apply hu.mono'
  · exact Finset.aestronglyMeasurable_fun_sum _ (fun i _ =>
      Finset.aestronglyMeasurable_fun_sum _ (fun j _ =>
        ((Lp.aestronglyMeasurable _).mul (hMmeas i j).aestronglyMeasurable).mul
          (Lp.aestronglyMeasurable _)))
  filter_upwards [matrixFieldPair_truncateValues_le R M hM u] with x hx
  rw [Real.norm_of_nonneg hx.1]
  exact hx.2

/-- Matrix-energy comparison with both real integrals justified by finite energy. -/
theorem integral_matrixFieldPair_truncateValues_le (R : ℝ≥0) (M : α → Matrix ι ι ℝ)
    (hMmeas : ∀ i j, Measurable (fun x => M x i j))
    (hM : ∀ᵐ x ∂ρ, (M x).PosSemidef) (u : ι → Lp ℝ 2 ρ)
    (hu : Integrable (matrixFieldPair M u u) ρ) :
    (∫ x, matrixFieldPair M (truncateValues R u) (truncateValues R u) x ∂ρ) ≤
      ∫ x, matrixFieldPair M u u x ∂ρ :=
  integral_mono_ae (integrable_matrixFieldPair_truncateValues R M hMmeas hM u hu) hu
    ((matrixFieldPair_truncateValues_le R M hM u).mono (fun _ hx => hx.2))

/-- Internal bridge to the natural domain. Once Sobolev membership has been
proved, no additional boundedness of the matrix or projection into its domain is needed. -/
theorem Internal.weightedFormDomain_of_truncateValues (R : ℝ≥0) (Q : ScalarFormData ρ)
    (M : α → Matrix ι ι ℝ) (S : Submodule ℝ (ι → ℝ))
    (hMmeas : ∀ i j, Measurable (fun x => M x i j))
    (hM : ∀ᵐ x ∂ρ, (M x).PosSemidef) (u h : ι → Q.1)
    (hu : WeightedFormDomain Q M S u)
    (hh : ∀ i, (h i).val = truncateValues R (fun j => (u j).val) i) :
    WeightedFormDomain Q M S h := by
  change (∀ᵐ x ∂ρ, (fun i => (h i).val x) ∈ S) ∧ _
  simp only [hh]
  exact ⟨truncateValues_mem R _ S hu.1,
    integrable_matrixFieldPair_truncateValues R M hMmeas hM _ hu.2⟩

end FiniteValues

section Levels

open Riesz1.WeightedSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsFiniteMeasure μ] {U : Set E}

/-- The library Sobolev completion is precisely the graph (Subsection 3.1),
with the product norm changed only by a homeomorphism. -/
theorem isWeightedH1_iff_neumannSobolevGraph (hb : Bornology.IsBounded U)
    (hμ : ∀ᵐ x ∂μ, x ∈ U) {F : E → ℝ} {G : E → E}
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    IsWeightedH1 μ U F G ↔ (hF.toLp F, hG.toLp G) ∈ neumannSobolevGraph μ U := by
  let e := WithLp.homeomorphProd 2 (Lp ℝ 2 μ) (Lp E 2 μ)
  let A : Set (Lp ℝ 2 μ × Lp E 2 μ) :=
    {p | ∃ (f : E → ℝ) (hf : MemLp f 2 μ) (hg : MemLp (gradient f) 2 μ),
      SmoothNearClosure U f ∧ p = (hf.toLp f, hg.toLp (gradient f))}
  have he : e ⁻¹' A = jetCore μ (SmoothNearClosure U) id gradient := by
    ext z
    constructor
    · rintro ⟨f, hf, hg, hfs, hz⟩
      refine ⟨f, hfs, hf, hg, ?_⟩
      exact e.injective hz
    · rintro ⟨f, hfs, hf, hg, rfl⟩
      exact ⟨f, hf, hg, hfs, rfl⟩
  rw [isWeightedH1_iff_isGraphH1, isGraphH1_iff_mem_closure
    (P := SmoothNearClosure U) (value := id) (derivative := gradient)
    (fun f hf => (memLp_of_smoothNearClosure hb hμ hf).1)
    (fun f hf => (memLp_of_smoothNearClosure hb hμ hf).2)]
  change WithLp.toLp 2 (hF.toLp F, hG.toLp G) ∈ closure (jetCore μ (SmoothNearClosure U) id gradient) ↔
    WithLp.toLp 2 (hF.toLp F, hG.toLp G) ∈ e ⁻¹' closure A
  rw [e.preimage_closure, he]

/-- The Neumann realization supplies precisely the injectivity needed by the
Euclidean Sobolev completion, with no new closability assumption (Subsection 3.1). -/
theorem value_injective_of_neumannRealization (hU : IsOpen U) (hb : Bornology.IsBounded U)
    (hμ : ∀ᵐ x ∂μ, x ∈ U) (Q : ScalarFormData μ) (hQ : IsNeumannRealization U Q) :
    Function.Injective (ScalarForm.value (EuclideanScalarForm.smoothJet hU hb hμ)) := by
  let J := EuclideanScalarForm.smoothJet hU hb hμ
  have hg (u : ScalarForm.Domain J) :
      (ScalarForm.value J u, ScalarForm.deriv J u) ∈ neumannSobolevGraph μ U := by
    have hH1 := (EuclideanScalarForm.mem_completion_iff hU hb hμ
      (ScalarForm.value J u) (ScalarForm.deriv J u)
      (Lp.memLp _) (Lp.memLp _)).mp (by
        simp only [Lp.toLp_coeFn]
        change u.val ∈ ScalarForm.completionSubmodule J
        exact u.property)
    have he := (isWeightedH1_iff_neumannSobolevGraph hb hμ (Lp.memLp _) (Lp.memLp _)).mp hH1
    simpa only [Lp.toLp_coeFn] using he
  intro u v huv
  have hd : ScalarForm.deriv J u = ScalarForm.deriv J v := by
    apply hQ.2.1 _ _ _ (hg u)
    rw [huv]
    exact hg v
  apply Subtype.ext
  apply (WithLp.equiv 2 _).injective
  exact Prod.ext huv hd

/-- Internal locality interface: the weak derivative vanishes on every scalar level,
using the library's level jets and injectivity of the completed value map.
This supplies the level-set step in the proof of Proposition 3.6. -/
theorem level_deriv_zero_of_closable (hU : IsOpen U) (hb : Bornology.IsBounded U)
    (hμ : ∀ᵐ x ∂μ, x ∈ U)
    (hcl : Function.Injective (ScalarForm.value (EuclideanScalarForm.smoothJet hU hb hμ)))
    {F : E → ℝ} {G : E → E} (hFG : IsWeightedH1 μ U F G) (a : ℝ) :
    ∀ᵐ x ∂μ, F x = a → G x = 0 := by
  have hlevel := Riesz1.WeightedSobolev.Internal.graph_levelSet
    (P := SmoothNearClosure U) (value := id) (grad := gradient)
    (fun f hf => (memLp_of_smoothNearClosure hb hμ hf).1)
    (fun f hf => (memLp_of_smoothNearClosure hb hμ hf).2)
    hFG.1 hFG.2.1
    (fun S hS hS0 K hSb => hFG.comp_smooth hb hμ hS hS0 hSb) a
  let J := EuclideanScalarForm.smoothJet hU hb hμ
  let z : ScalarForm.Domain J :=
    ⟨WithLp.toLp 2 (hlevel.1.toLp (fun _ => 0),
      hlevel.2.1.toLp ({x | F x = a}.indicator G)),
      (EuclideanScalarForm.mem_completion_iff hU hb hμ _ _ hlevel.1 hlevel.2.1).mpr hlevel⟩
  have hv : ScalarForm.value J z = 0 := MemLp.toLp_zero hlevel.1
  have hz : z = 0 := hcl (by simpa only [map_zero] using hv)
  have hd : hlevel.2.1.toLp ({x | F x = a}.indicator G) = 0 := by
    have he := congrArg (ScalarForm.deriv J) hz
    change hlevel.2.1.toLp ({x | F x = a}.indicator G) = ScalarForm.deriv J 0 at he
    simpa only [map_zero] using he
  have he : {x | F x = a}.indicator G =ᵐ[μ] 0 :=
    hlevel.2.1.coeFn_toLp.symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp hd)
  filter_upwards [he] with x hx ha
  rw [indicator_of_mem (show x ∈ {x | F x = a} from ha)] at hx
  exact hx

/-- On a vector point-level all weak component derivatives vanish. This includes
the zero vector, without requiring equality of base and component dimensions. -/
theorem point_level_deriv_zero_of_closable {ι : Type*} [Fintype ι]
    (hU : IsOpen U) (hb : Bornology.IsBounded U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    (hcl : Function.Injective (ScalarForm.value (EuclideanScalarForm.smoothJet hU hb hμ)))
    {F : ι → E → ℝ} {G : ι → E → E} (hFG : ∀ i, IsWeightedH1 μ U (F i) (G i))
    (a : ι → ℝ) : ∀ᵐ x ∂μ, (∀ i, F i x = a i) → ∀ i, G i x = 0 := by
  have he := ae_all_iff.mpr (fun i => level_deriv_zero_of_closable hU hb hμ hcl (hFG i) (a i))
  filter_upwards [he] with x hx ha i
  exact hx i (ha i)

/-- Scalar level locality for the existing intrinsic Neumann realization.
All measure and derivative conventions are those of Subsection 3.1. -/
theorem level_deriv_zero (hU : IsOpen U) (hb : Bornology.IsBounded U)
    (hμ : ∀ᵐ x ∂μ, x ∈ U) (Q : ScalarFormData μ) (hQ : IsNeumannRealization U Q)
    {F : E → ℝ} {G : E → E} (hFG : IsWeightedH1 μ U F G) (a : ℝ) :
    ∀ᵐ x ∂μ, F x = a → G x = 0 :=
  level_deriv_zero_of_closable hU hb hμ
    (value_injective_of_neumannRealization hU hb hμ Q hQ) hFG a

end Levels

end Riesz2.VectorRadial
