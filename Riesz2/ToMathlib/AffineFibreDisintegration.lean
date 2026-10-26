/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.AffineSimplexCharts
public import Riesz1.ToMathlib.LogConcave.PrekopaContinuity
public import Riesz1.ToMathlib.LogConcave.MarginalConcaveDensity
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Affine fibres and explicit conditional densities

Shared infrastructure for Subsection 3.4, Subsection 6.1 and Lemma 6.5.
Normalization is defined only
when the nonnegative integral is positive and finite. Product disintegration uses
these explicit densities on every fibre of the base carrier, including dimension
zero. Applications restrict the base carrier to its open projection.

The sum-coordinate chart reuses `AffineSimplex.chart`. Its full-dimensional
Jacobian is one. Intrinsic hyperplane volume contributes `√(n+1)`. Consequently
the coarea factor for the sum of `n+1` coordinates is `1/√(n+1)`.
All integrals involving nonnegative tests are extended integrals.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz2
namespace AffineFibre

section Normalization

variable {F : Type*} [MeasurableSpace F]

/-- The normalized density of a weight with positive finite mass. The proof arguments
exclude empty or infinite fibres rather than assigning them an arbitrary probability. -/
def normalizedDensity (ν : Measure F) (w : F → ℝ≥0∞)
    (_h0 : (∫⁻ y, w y ∂ν) ≠ 0) (_ht : (∫⁻ y, w y ∂ν) ≠ ∞) : F → ℝ≥0∞ :=
  fun y => (∫⁻ z, w z ∂ν)⁻¹ * w y

/-- The probability obtained by normalizing a finite nonzero density. -/
def normalizedMeasure (ν : Measure F) (w : F → ℝ≥0∞)
    (h0 : (∫⁻ y, w y ∂ν) ≠ 0) (ht : (∫⁻ y, w y ∂ν) ≠ ∞) : Measure F :=
  ν.withDensity (normalizedDensity ν w h0 ht)

theorem measurable_normalizedDensity (ν : Measure F) {w : F → ℝ≥0∞}
    (hw : Measurable w) (h0 : (∫⁻ y, w y ∂ν) ≠ 0) (ht : (∫⁻ y, w y ∂ν) ≠ ∞) :
    Measurable (normalizedDensity ν w h0 ht) := measurable_const.mul hw

theorem lintegral_normalizedDensity (ν : Measure F) {w : F → ℝ≥0∞}
    (hw : Measurable w) (h0 : (∫⁻ y, w y ∂ν) ≠ 0) (ht : (∫⁻ y, w y ∂ν) ≠ ∞) :
    ∫⁻ y, normalizedDensity ν w h0 ht y ∂ν = 1 := by
  change (∫⁻ y, (∫⁻ z, w z ∂ν)⁻¹ * w y ∂ν) = 1
  rw [lintegral_const_mul _ hw, ENNReal.inv_mul_cancel h0 ht]

theorem isProbabilityMeasure_normalizedMeasure (ν : Measure F) {w : F → ℝ≥0∞}
    (hw : Measurable w) (h0 : (∫⁻ y, w y ∂ν) ≠ 0) (ht : (∫⁻ y, w y ∂ν) ≠ ∞) :
    IsProbabilityMeasure (normalizedMeasure ν w h0 ht) := by
  constructor
  simpa only [normalizedMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] using lintegral_normalizedDensity ν hw h0 ht

theorem normalizedDensity_pos (ν : Measure F) {w : F → ℝ≥0∞}
    (h0 : (∫⁻ y, w y ∂ν) ≠ 0) (ht : (∫⁻ y, w y ∂ν) ≠ ∞) {y : F}
    (hy : 0 < w y) : 0 < normalizedDensity ν w h0 ht y := by
  exact ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr ht) hy.ne'

theorem normalizedDensity_ne_top (ν : Measure F) {w : F → ℝ≥0∞}
    (h0 : (∫⁻ y, w y ∂ν) ≠ 0) (ht : (∫⁻ y, w y ∂ν) ≠ ∞) {y : F}
    (hy : w y ≠ ∞) : normalizedDensity ν w h0 ht y ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr h0) hy

/-- Nonnegative conditional expectations are ratios of extended integrals. -/
theorem lintegral_normalizedMeasure (ν : Measure F) {w : F → ℝ≥0∞}
    (hw : Measurable w) (h0 : (∫⁻ y, w y ∂ν) ≠ 0) (ht : (∫⁻ y, w y ∂ν) ≠ ∞)
    {f : F → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂normalizedMeasure ν w h0 ht =
      (∫⁻ y, w y ∂ν)⁻¹ * ∫⁻ y, w y * f y ∂ν := by
  rw [normalizedMeasure, lintegral_withDensity_eq_lintegral_mul _
    (measurable_normalizedDensity ν hw h0 ht) hf]
  change (∫⁻ y, ((∫⁻ z, w z ∂ν)⁻¹ * w y) * f y ∂ν) = _
  simp_rw [mul_assoc]
  exact lintegral_const_mul _ (hw.mul hf)

/-- A positive finite constant Jacobian cancels in the normalized conditional law. -/
theorem normalizedDensity_smul_measure (ν : Measure F) {w : F → ℝ≥0∞}
    (h0 : (∫⁻ y, w y ∂ν) ≠ 0) (ht : (∫⁻ y, w y ∂ν) ≠ ∞)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ∞) (y : F) :
    c * normalizedDensity (c • ν) w
      (by rw [lintegral_smul_measure]; exact mul_ne_zero hc0 h0)
      (by rw [lintegral_smul_measure]; exact ENNReal.mul_ne_top hct ht) y =
      normalizedDensity ν w h0 ht y := by
  simp only [normalizedDensity, lintegral_smul_measure, smul_eq_mul]
  rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hct)]
  simp_rw [← mul_assoc]
  rw [ENNReal.mul_inv_cancel hc0 hct, one_mul]

/-- A convenient scalar-measure expression for normalization. -/
theorem normalizedMeasure_eq_smul (ν : Measure F) (w : F → ℝ≥0∞)
    (h0 : (∫⁻ y, w y ∂ν) ≠ 0) (ht : (∫⁻ y, w y ∂ν) ≠ ∞) :
    normalizedMeasure ν w h0 ht = (∫⁻ y, w y ∂ν)⁻¹ • ν.withDensity w :=
  withDensity_smul' _ w (ENNReal.inv_ne_top.mpr h0)

/-- Normalizing intrinsic volume or a constant multiple of coordinate volume gives
the same probability. No measurability of the weight is needed for this identity. -/
theorem normalizedMeasure_smul_measure (ν : Measure F) (w : F → ℝ≥0∞)
    (h0 : (∫⁻ y, w y ∂ν) ≠ 0) (ht : (∫⁻ y, w y ∂ν) ≠ ∞)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ∞) :
    normalizedMeasure (c • ν) w
      (by rw [lintegral_smul_measure]; exact mul_ne_zero hc0 h0)
      (by rw [lintegral_smul_measure]; exact ENNReal.mul_ne_top hct ht) =
      normalizedMeasure ν w h0 ht := by
  simp only [normalizedMeasure_eq_smul, lintegral_smul_measure, smul_eq_mul,
    withDensity_smul_measure, smul_smul]
  rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hct)]
  have hc : c⁻¹ * (∫⁻ y, w y ∂ν)⁻¹ * c = (∫⁻ y, w y ∂ν)⁻¹ := by
    rw [mul_right_comm, ENNReal.inv_mul_cancel hc0 hct, one_mul]
  rw [hc]

/-- Normalization commutes with an injective measurable change of coordinates. -/
theorem normalizedMeasure_map {G : Type*} [MeasurableSpace G]
    (ν : Measure F) {e : F → G} (he : MeasurableEmbedding e) {w : G → ℝ≥0∞}
    (hw : Measurable w)
    (h0 : (∫⁻ y, w (e y) ∂ν) ≠ 0) (ht : (∫⁻ y, w (e y) ∂ν) ≠ ∞) :
    normalizedMeasure (ν.map e) w
      (by rw [he.lintegral_map]; exact h0)
      (by rw [he.lintegral_map]; exact ht) =
      (normalizedMeasure ν (fun y => w (e y)) h0 ht).map e := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [he.lintegral_map, lintegral_normalizedMeasure _ hw,
    lintegral_normalizedMeasure ν (w := fun y => w (e y)) (f := fun y => f (e y))
      (hw.comp he.measurable) h0 ht (hf.comp he.measurable),
    he.lintegral_map, he.lintegral_map]
  exact hf

/-- The real formula is valid because integrability and positivity are established,
so neither the Bochner integral nor inversion can take a junk value. -/
theorem normalizedDensity_ofReal (ν : Measure F) {w : F → ℝ}
    (hw : Integrable w ν) (hn : ∀ y, 0 ≤ w y) (hp : 0 < ∫ y, w y ∂ν) (y : F) :
    normalizedDensity ν (fun z => ENNReal.ofReal (w z))
      (by rw [← ofReal_integral_eq_lintegral_ofReal hw (Filter.Eventually.of_forall hn)]
          exact ENNReal.ofReal_ne_zero_iff.mpr hp)
      (by rw [← ofReal_integral_eq_lintegral_ofReal hw (Filter.Eventually.of_forall hn)]
          exact ENNReal.ofReal_ne_top) y =
      ENNReal.ofReal (w y / ∫ z, w z ∂ν) := by
  simp only [normalizedDensity]
  rw [← ofReal_integral_eq_lintegral_ofReal hw (Filter.Eventually.of_forall hn),
    ENNReal.ofReal_div_of_pos hp, div_eq_mul_inv, mul_comm]

end Normalization

section Product

variable {B F : Type*} [MeasurableSpace B] [MeasurableSpace F]
variable (μ : Measure B) (ν : Measure F) [SFinite μ] [SFinite ν]

/-- The unnormalized marginal density, evaluated at each base point. -/
@[reducible] def fibreMass (w : B × F → ℝ≥0∞) (x : B) : ℝ≥0∞ := ∫⁻ y, w (x, y) ∂ν

theorem measurable_fibreMass {w : B × F → ℝ≥0∞} (hw : Measurable w) :
    Measurable (fibreMass ν w) := hw.lintegral_prod_right'

/-- Reuse the companion library's marginal identification, with no normalization assumption. -/
theorem map_fst_withDensity {w : B × F → ℝ≥0∞} (hw : Measurable w) :
    ((μ.prod ν).withDensity w).map Prod.fst = μ.withDensity (fibreMass ν w) :=
  Riesz1.map_fst_withDensity_fiber μ ν w hw

/-- Joint measurability of the explicit conditional density, on any base carrier
where all fibres have finite nonzero mass. -/
theorem measurable_conditionalDensity {w : B × F → ℝ≥0∞} (hw : Measurable w)
    (h0 : ∀ x, fibreMass ν w x ≠ 0) (ht : ∀ x, fibreMass ν w x ≠ ∞) :
    Measurable (fun p : B × F =>
      normalizedDensity ν (fun y => w (p.1, y)) (h0 p.1) (ht p.1) p.2) :=
  ((measurable_fibreMass ν hw).comp measurable_fst).inv.mul hw

omit [SFinite ν] in
/-- Every fibre, not merely almost every fibre, gives a probability. -/
theorem conditional_isProbabilityMeasure {w : B × F → ℝ≥0∞} (hw : Measurable w)
    (h0 : ∀ x, fibreMass ν w x ≠ 0) (ht : ∀ x, fibreMass ν w x ≠ ∞) (x : B) :
    IsProbabilityMeasure (normalizedMeasure ν (fun y => w (x, y)) (h0 x) (ht x)) :=
  isProbabilityMeasure_normalizedMeasure ν (hw.comp measurable_prodMk_left) (h0 x) (ht x)

/-- The explicit probabilities form a measurable family, including their values on
all measurable events. This avoids an arbitrary choice of conditional laws. -/
theorem measurable_conditionalMeasure_apply {w : B × F → ℝ≥0∞} (hw : Measurable w)
    (h0 : ∀ x, fibreMass ν w x ≠ 0) (ht : ∀ x, fibreMass ν w x ≠ ∞)
    {s : Set F} (hs : MeasurableSet s) :
    Measurable (fun x => normalizedMeasure ν (fun y => w (x, y)) (h0 x) (ht x) s) := by
  simp only [normalizedMeasure, withDensity_apply _ hs]
  have h := (measurable_conditionalDensity ν hw h0 ht).lintegral_prod_right'
    (ν := ν.restrict s)
  exact h

omit [SFinite μ] in
/-- Disintegration of any product density into its marginal and the explicit normalized
fibre laws. Nonnegative tests may have infinite expectation. -/
theorem lintegral_disintegration {w : B × F → ℝ≥0∞} (hw : Measurable w)
    (h0 : ∀ x, fibreMass ν w x ≠ 0) (ht : ∀ x, fibreMass ν w x ≠ ∞)
    {f : B × F → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p, f p ∂(μ.prod ν).withDensity w =
      ∫⁻ x, (∫⁻ y, f (x, y) ∂normalizedMeasure ν (fun y => w (x, y)) (h0 x) (ht x))
        ∂μ.withDensity (fibreMass ν w) := by
  have heq (x : B) := lintegral_normalizedMeasure ν
    (hw.comp measurable_prodMk_left) (h0 x) (ht x) (hf.comp (measurable_prodMk_left (x := x)))
  simp only [Function.comp_def] at heq
  simp_rw [heq]
  have hmeas : Measurable (fun x => (∫⁻ y, w (x, y) ∂ν)⁻¹ *
      ∫⁻ y, w (x, y) * f (x, y) ∂ν) :=
    (measurable_fibreMass ν hw).inv.mul (hw.mul hf).lintegral_prod_right'
  rw [lintegral_withDensity_eq_lintegral_mul _ hw hf, lintegral_prod _ (hw.mul hf).aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_fibreMass ν hw) hmeas]
  apply lintegral_congr
  intro x
  change (∫⁻ y, w (x, y) * f (x, y) ∂ν) =
    fibreMass ν w x * ((fibreMass ν w x)⁻¹ * ∫⁻ y, w (x, y) * f (x, y) ∂ν)
  exact (ENNReal.mul_inv_cancel_left (h0 x) (ht x)).symm

/-- Measurability of conditional expectations of a jointly measurable nonnegative test. -/
theorem measurable_conditional_lintegral {w : B × F → ℝ≥0∞} (hw : Measurable w)
    (h0 : ∀ x, fibreMass ν w x ≠ 0) (ht : ∀ x, fibreMass ν w x ≠ ∞)
    {f : B × F → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun x => ∫⁻ y, f (x, y)
      ∂normalizedMeasure ν (fun y => w (x, y)) (h0 x) (ht x)) := by
  have heq (x : B) := lintegral_normalizedMeasure ν
    (hw.comp measurable_prodMk_left) (h0 x) (ht x) (hf.comp (measurable_prodMk_left (x := x)))
  simp only [Function.comp_def] at heq
  simp_rw [heq]
  exact (measurable_fibreMass ν hw).inv.mul (hw.mul hf).lintegral_prod_right'

end Product

section ConvexFibres

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [MeasurableSpace B] [BorelSpace B]
variable {n : ℕ} {Q : Set (B × EuclideanSpace ℝ (Fin n))}
  {V : B × EuclideanSpace ℝ (Fin n) → ℝ}

/-- See Subsection 3.4 of the paper: every interior fibre has a finite, strictly positive mass.
This uses the proved companion results, also when the fibre dimension is zero. -/
theorem convex_fibre_mass (hQo : IsOpen Q) (hQb : Bornology.IsBounded Q)
    (hV : ConvexOn ℝ Q V) {x : B} (hx : x ∈ Prod.fst '' Q) :
    let w := fun p => ENNReal.ofReal (Q.indicator (fun q => Real.exp (-V q)) p)
    fibreMass (volume : Measure (EuclideanSpace ℝ (Fin n))) w x ≠ 0 ∧
      fibreMass (volume : Measure (EuclideanSpace ℝ (Fin n))) w x ≠ ∞ := by
  obtain ⟨p, hp, rfl⟩ := hx
  have hi := Riesz1.integrable_fiber_exp_indicator hQo hQb hV p.1
  have hpos := Riesz1.marginal_exp_indicator_pos hQo hQb hV (z := p.1) ⟨p.2, hp⟩
  have heq := ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun y =>
      indicator_nonneg (fun q _ => (Real.exp_pos (-V q)).le) (p.1, y)))
  dsimp only [fibreMass]
  rw [← heq]
  exact ⟨ENNReal.ofReal_ne_zero_iff.mpr hpos, ENNReal.ofReal_ne_top⟩

/-- The explicitly normalized conditional law on each point of the open projection.
No value is assigned to an empty fibre or selected from an a.e. equivalence class. -/
def convexConditionalMeasure (hQo : IsOpen Q) (hQb : Bornology.IsBounded Q)
    (hV : ConvexOn ℝ Q V) (x : Prod.fst '' Q) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  normalizedMeasure volume
    (fun y => ENNReal.ofReal (Q.indicator (fun q => Real.exp (-V q)) (x.val, y)))
    (convex_fibre_mass hQo hQb hV x.property).1
    (convex_fibre_mass hQo hQb hV x.property).2

theorem isProbabilityMeasure_convexConditionalMeasure
    (hQo : IsOpen Q) (hQb : Bornology.IsBounded Q) (hV : ConvexOn ℝ Q V)
    (x : Prod.fst '' Q) : IsProbabilityMeasure (convexConditionalMeasure hQo hQb hV x) := by
  exact isProbabilityMeasure_normalizedMeasure _
    ((Riesz1.measurable_exp_indicator hQo hV).ennreal_ofReal.comp measurable_prodMk_left)
    _ _

/-- Every conditional event probability is measurable in the exterior parameter. -/
theorem measurable_convexConditionalMeasure_apply
    (hQo : IsOpen Q) (hQb : Bornology.IsBounded Q) (hV : ConvexOn ℝ Q V)
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : MeasurableSet s) :
    Measurable (fun x => convexConditionalMeasure hQo hQb hV x s) := by
  have hw : Measurable (fun p : (Prod.fst '' Q) × EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (Q.indicator (fun q => Real.exp (-V q)) (p.1.val, p.2))) :=
    (Riesz1.measurable_exp_indicator hQo hV).ennreal_ofReal.comp
      ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
  exact measurable_conditionalMeasure_apply volume hw
    (fun x => (convex_fibre_mass hQo hQb hV x.property).1)
    (fun x => (convex_fibre_mass hQo hQb hV x.property).2) hs

/-- In zero dimensions the explicit conditional probability is the point mass,
including for base points of measure zero. -/
theorem convexConditionalMeasure_zero
    {Q : Set (B × EuclideanSpace ℝ (Fin 0))} {V : B × EuclideanSpace ℝ (Fin 0) → ℝ}
    (hQo : IsOpen Q) (hQb : Bornology.IsBounded Q) (hV : ConvexOn ℝ Q V)
    (x : Prod.fst '' Q) : convexConditionalMeasure hQo hQb hV x = Measure.dirac 0 := by
  have := isProbabilityMeasure_convexConditionalMeasure hQo hQb hV x
  apply Measure.ext_of_lintegral
  intro f hf
  calc
    ∫⁻ y, f y ∂convexConditionalMeasure hQo hQb hV x =
        ∫⁻ _, f 0 ∂convexConditionalMeasure hQo hQb hV x :=
      lintegral_congr (fun y => congrArg f (Subsingleton.elim y 0))
    _ = f 0 := by simp
    _ = ∫⁻ y, f y ∂Measure.dirac 0 := by simp

end ConvexFibres

namespace SumChart

open AffineSimplex

/-- Affine fibre coordinates with the sum as base coordinate. This is the existing
deleted-last-coordinate chart at variable mass, with its inverse made explicit. -/
def totalChart (n : ℕ) : (ℝ × EuclideanSpace ℝ (Fin n)) ≃ₜ
    EuclideanSpace ℝ (Fin (n + 1)) where
  toFun p := chart n p.1 p.2
  invFun y := (∑ i, y i, coordinates n y)
  left_inv p := by simp [sum_chart, coordinates_chart]
  right_inv y := chart_coordinates n _ rfl
  continuous_toFun := by
    have heq : (fun p : ℝ × EuclideanSpace ℝ (Fin n) => chart n p.1 p.2) =
        fun p => AffineSimplex.tangentMap n p.2 + p.1 • chart n 1 0 := by
      funext p
      ext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [chart_last, AffineSimplex.tangentMap]
        ring
      · simp [chart_castSucc, AffineSimplex.tangentMap]
    rw [heq]
    exact ((AffineSimplex.tangentMap n).continuous_of_finiteDimensional.comp continuous_snd).add
      (continuous_fst.smul continuous_const)
  continuous_invFun :=
    (continuous_finsetSum _ (fun i _ => PiLp.continuous_apply 2 _ i)).prodMk
      (continuous_coordinates n)

theorem totalChart_apply (n : ℕ) (L : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    totalChart n (L, x) = chart n L x := rfl

/-- The full-dimensional chart has Jacobian one. The shear in the last coordinate
preserves volume, before the intrinsic area factor on each fibre is introduced. -/
theorem measurePreserving_totalChart (n : ℕ) : MeasurePreserving (totalChart n) := by
  have hshear : MeasurePreserving
      (fun p : EuclideanSpace ℝ (Fin n) × ℝ => (p.1, p.2 - ∑ i, p.1 i)) := by
    change MeasurePreserving _
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod (volume : Measure ℝ))
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).prod (volume : Measure ℝ))
    apply (MeasurePreserving.id (volume : Measure (EuclideanSpace ℝ (Fin n)))).skew_product
      (g := fun x t => t - ∑ i, x i)
    · exact measurable_snd.sub
        (Finset.measurable_sum _ (fun i _ => (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).measurable.comp measurable_fst))
    · exact Filter.Eventually.of_forall fun x =>
        (measurePreserving_sub_right (volume : Measure ℝ) (∑ i, x i)).map_eq
  have hsplit : MeasurePreserving
      (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
        WithLp.toLp 2 (Fin.snoc (WithLp.ofLp p.2) p.1 : Fin (n + 1) → ℝ)) := by
    have h := (PiLp.volume_preserving_toLp (Fin (n + 1))).comp
      ((volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm.comp
        ((MeasurePreserving.id (volume : Measure ℝ)).prod
          (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n))))
    convert h using 1
    ext p i
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
  have hswap₁ := Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (EuclideanSpace ℝ (Fin n))))
  have hswap₂ := Measure.measurePreserving_swap (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (ν := (volume : Measure ℝ))
  have h := hsplit.comp (hswap₂.comp (hshear.comp hswap₁))
  convert h using 1
  rfl

/-- Hyperplane integration in the existing nonorthogonal chart. -/
theorem lintegral_hyperplaneVolume (n : ℕ) (L : ℝ)
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞) :
    ∫⁻ y, f y ∂hyperplaneVolume n L = ENNReal.ofReal (Real.sqrt (n + 1)) *
      ∫⁻ x, f (chart n L x) := by
  rw [hyperplaneVolume_eq, lintegral_smul_measure,
    (isClosedEmbedding_chart n L).measurableEmbedding.lintegral_map, smul_eq_mul]

/-- Coarea for the sum map, with its exact constant `1/√(n+1)`. -/
theorem lintegral_coarea (n : ℕ)
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y = (ENNReal.ofReal (Real.sqrt (n + 1)))⁻¹ *
      ∫⁻ L : ℝ, ∫⁻ y, f y ∂hyperplaneVolume n L := by
  simp_rw [lintegral_hyperplaneVolume]
  have hmeas : Measurable (fun L => ∫⁻ x, f (chart n L x)) :=
    (hf.comp (totalChart n).continuous.measurable).lintegral_prod_right'
  rw [lintegral_const_mul _ hmeas,
    ← mul_assoc, ENNReal.inv_mul_cancel
      (ENNReal.ofReal_ne_zero_iff.mpr (Real.sqrt_pos.mpr (by positivity))) ENNReal.ofReal_ne_top,
    one_mul]
  calc
    ∫⁻ y, f y = ∫⁻ p, f (totalChart n p) :=
      ((measurePreserving_totalChart n).lintegral_comp hf).symm
    _ = _ := lintegral_prod _ (hf.comp (totalChart n).continuous.measurable).aemeasurable

/-- Joint measurability of intrinsic hyperplane integrals. No a.e. choice of fibres. -/
theorem measurable_hyperplane_lintegral (n : ℕ)
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun L => ∫⁻ y, f y ∂hyperplaneVolume n L) := by
  simp_rw [lintegral_hyperplaneVolume]
  exact measurable_const.mul
    (hf.comp (totalChart n).continuous.measurable).lintegral_prod_right'

/-- Coarea restricted to the positive orthant gives the intrinsic simplex fibres. -/
theorem lintegral_coarea_positive (n : ℕ)
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y in {y | ∀ i, 0 < y i}, f y =
      (ENNReal.ofReal (Real.sqrt (n + 1)))⁻¹ *
        ∫⁻ L : ℝ, ∫⁻ y, f y ∂simplexVolume n L := by
  have hopen : IsOpen {y : EuclideanSpace ℝ (Fin (n + 1)) | ∀ i, 0 < y i} := by
    simpa only [ofPred_forall] using isOpen_iInter_of_finite
      (fun i : Fin (n + 1) => isOpen_lt continuous_const (PiLp.continuous_apply 2 _ i))
  rw [← lintegral_indicator hopen.measurableSet]
  rw [lintegral_coarea n (hf.indicator hopen.measurableSet)]
  congr 1
  apply lintegral_congr
  intro L
  rw [lintegral_indicator hopen.measurableSet, hyperplaneVolume,
    Measure.restrict_restrict hopen.measurableSet]
  rfl

/-- Intrinsic simplex integrals are measurable functions of the mass, even at zero
and outside the positive mass range. -/
theorem measurable_simplex_lintegral (n : ℕ)
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun L => ∫⁻ y, f y ∂simplexVolume n L) := by
  have hopen : IsOpen {y : EuclideanSpace ℝ (Fin (n + 1)) | ∀ i, 0 < y i} := by
    simpa only [ofPred_forall] using isOpen_iInter_of_finite
      (fun i : Fin (n + 1) => isOpen_lt continuous_const (PiLp.continuous_apply 2 _ i))
  have heq (L : ℝ) : (∫⁻ y, f y ∂simplexVolume n L) =
      ∫⁻ y, ({y | ∀ i, 0 < y i}.indicator f) y ∂hyperplaneVolume n L := by
    rw [lintegral_indicator hopen.measurableSet, hyperplaneVolume,
      Measure.restrict_restrict hopen.measurableSet]
    rfl
  simp_rw [heq]
  exact measurable_hyperplane_lintegral n (hf.indicator hopen.measurableSet)

/-- The `√(n+1)` chart factor cancels from each normalized simplex law. -/
theorem normalizedMeasure_simplexVolume (n : ℕ) (L : ℝ)
    {w : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞} (hw : Measurable w)
    (h0 : (∫⁻ x in chartDomain n L, w (chart n L x)) ≠ 0)
    (ht : (∫⁻ x in chartDomain n L, w (chart n L x)) ≠ ∞) :
    normalizedMeasure (simplexVolume n L) w
      (by rw [lintegral_simplexVolume]; exact mul_ne_zero
            (ENNReal.ofReal_ne_zero_iff.mpr (Real.sqrt_pos.mpr (by positivity))) h0)
      (by rw [lintegral_simplexVolume]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ht) =
      (normalizedMeasure (volume.restrict (chartDomain n L))
        (fun x => w (chart n L x)) h0 ht).map (chart n L) := by
  have he := (isClosedEmbedding_chart n L).measurableEmbedding
  have hm0 : (∫⁻ y, w y ∂(volume.restrict (chartDomain n L)).map (chart n L)) ≠ 0 := by
    rw [he.lintegral_map]
    exact h0
  have hmt : (∫⁻ y, w y ∂(volume.restrict (chartDomain n L)).map (chart n L)) ≠ ∞ := by
    rw [he.lintegral_map]
    exact ht
  simpa only [simplexVolume_eq] using (normalizedMeasure_smul_measure _ w hm0 hmt
    (ENNReal.ofReal_ne_zero_iff.mpr (Real.sqrt_pos.mpr (by positivity)))
    ENNReal.ofReal_ne_top).trans (normalizedMeasure_map _ he hw h0 ht)

/-- The sum is fixed on intrinsic simplex volume, including its null boundary. -/
theorem sum_eq_ae_simplexVolume (n : ℕ) (L : ℝ) :
    ∀ᵐ y ∂simplexVolume n L, ∑ i, y i = L := by
  have hs : MeasurableSet (massSimplex n L) := by
    change MeasurableSet ({y | ∀ i, 0 < y i} ∩ massHyperplane n L)
    apply MeasurableSet.inter
    · simpa only [ofPred_forall] using MeasurableSet.iInter
        (fun i : Fin (n + 1) => measurableSet_lt measurable_const
          (PiLp.continuous_apply 2 _ i).measurable)
    · exact (isClosed_massHyperplane n L).measurableSet
  exact (ae_restrict_mem hs).mono (fun _ hy => hy.2)

/-- Multiplication by a function of the length is constant on each intrinsic fibre. -/
theorem lintegral_mul_sum (n : ℕ) (L : ℝ)
    {w : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞} (hw : Measurable w)
    (f : ℝ → ℝ≥0∞) :
    ∫⁻ y, w y * f (∑ i, y i) ∂simplexVolume n L =
      (∫⁻ y, w y ∂simplexVolume n L) * f L := by
  calc
    _ = ∫⁻ y, w y * f L ∂simplexVolume n L :=
      lintegral_congr_ae ((sum_eq_ae_simplexVolume n L).mono (fun y hy => by rw [hy]))
    _ = _ := lintegral_mul_const _ hw

/-- See Lemma 6.5 of the paper: the pushforward by the sum has the explicit coarea density.
This identity holds without finiteness assumptions and retains the exact Jacobian. -/
theorem map_sum_withDensity_positive (n : ℕ)
    {w : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞} (hw : Measurable w) :
    (((volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))).restrict
        {y | ∀ i, 0 < y i}).withDensity w).map (fun y => ∑ i, y i) =
      volume.withDensity (fun L => (ENNReal.ofReal (Real.sqrt (n + 1)))⁻¹ *
        ∫⁻ y, w y ∂simplexVolume n L) := by
  have hm : Measurable (fun y : EuclideanSpace ℝ (Fin (n + 1)) => ∑ i, y i) :=
    (continuous_finsetSum _ (fun i _ => PiLp.continuous_apply 2 _ i)).measurable
  have hZ := measurable_simplex_lintegral n hw
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hm, lintegral_withDensity_eq_lintegral_mul _ hw
    (g := fun y => f (∑ i, y i)) (hf.comp hm)]
  simp only [Pi.mul_apply]
  rw [lintegral_coarea_positive n (f := fun y => w y * f (∑ i, y i))
    (hw.mul (hf.comp hm))]
  simp_rw [lintegral_mul_sum n _ hw f]
  rw [lintegral_withDensity_eq_lintegral_mul volume
    (f := fun L => (ENNReal.ofReal (Real.sqrt (n + 1)))⁻¹ *
      ∫⁻ y, w y ∂simplexVolume n L) (measurable_const.mul hZ) hf]
  simpa only [Pi.mul_apply, mul_assoc] using (lintegral_const_mul
    (ENNReal.ofReal (Real.sqrt (n + 1)))⁻¹ (hZ.mul hf)).symm

/-- Conditional expectations on the length fibres are measurable on any base carrier
where the masses are finite and positive at every point. -/
theorem measurable_simplex_conditional_lintegral (n : ℕ) (I : Set ℝ)
    {w : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞} (hw : Measurable w)
    (h0 : ∀ L : I, (∫⁻ y, w y ∂simplexVolume n L.val) ≠ 0)
    (ht : ∀ L : I, (∫⁻ y, w y ∂simplexVolume n L.val) ≠ ∞)
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun L : I => ∫⁻ y, f y
      ∂normalizedMeasure (simplexVolume n L.val) w (h0 L) (ht L)) := by
  have heq (L : I) := lintegral_normalizedMeasure (simplexVolume n L.val) hw (h0 L) (ht L) hf
  simp_rw [heq]
  exact ((measurable_simplex_lintegral n hw).comp measurable_subtype_coe).inv.mul
    ((measurable_simplex_lintegral n (hw.mul hf)).comp measurable_subtype_coe)

/-- Explicit disintegration on any measurable set of regular lengths. The base
measure is Lebesgue measure on that carrier. Its density is the intrinsic fibre
mass times `1/√(n+1)`. In particular one may take `I = (0,N)`. -/
theorem lintegral_simplex_disintegration (n : ℕ) {I : Set ℝ} (hI : MeasurableSet I)
    {w : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞} (hw : Measurable w)
    (h0 : ∀ L : I, (∫⁻ y, w y ∂simplexVolume n L.val) ≠ 0)
    (ht : ∀ L : I, (∫⁻ y, w y ∂simplexVolume n L.val) ≠ ∞)
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y in {y | (∑ i, y i) ∈ I} ∩ {y | ∀ i, 0 < y i}, w y * f y =
      (ENNReal.ofReal (Real.sqrt (n + 1)))⁻¹ *
        ∫⁻ L : I, (∫⁻ y, w y ∂simplexVolume n L.val) *
          (∫⁻ y, f y ∂normalizedMeasure (simplexVolume n L.val) w (h0 L) (ht L))
          ∂(volume.comap ((↑) : I → ℝ)) := by
  have heq (L : I) : (∫⁻ y, w y ∂simplexVolume n L.val) *
      (∫⁻ y, f y ∂normalizedMeasure (simplexVolume n L.val) w (h0 L) (ht L)) =
      ∫⁻ y, w y * f y ∂simplexVolume n L.val := by
    rw [lintegral_normalizedMeasure _ hw (h0 L) (ht L) hf]
    exact ENNReal.mul_inv_cancel_left (h0 L) (ht L)
  simp_rw [heq]
  rw [lintegral_subtype_comap hI (fun L => ∫⁻ y, w y * f y ∂simplexVolume n L)]
  have hm : Measurable (fun y : EuclideanSpace ℝ (Fin (n + 1)) => ∑ i, y i) :=
    (continuous_finsetSum _ (fun i _ => PiLp.continuous_apply 2 _ i)).measurable
  have h := congrArg (fun μ : Measure ℝ => μ I) (map_sum_withDensity_positive n (hw.mul hf))
  rw [Measure.map_apply hm hI, withDensity_apply _ (hm hI), withDensity_apply _ hI,
    Measure.restrict_restrict (hm hI)] at h
  have hN : Measurable (fun L => ∫⁻ y, w y * f y ∂simplexVolume n L) :=
    measurable_simplex_lintegral n (hw.mul hf)
  simp only [Pi.mul_apply] at h
  rw [lintegral_const_mul _ hN] at h
  exact h

end SumChart

end AffineFibre
end Riesz2
