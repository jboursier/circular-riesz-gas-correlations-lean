/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.ConvexIntervalMarginal
public import Riesz1.ToMathlib.LogConcave.MarginalConcaveDensity
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Coordinate densities of bounded convex Gibbs laws

Coordinate marginalization of a normalized exponential density on a bounded open
convex domain. Fibres of dimension zero are included. The density is the actual
fibre integral at every point, with its positive set exactly the projected domain.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz2

/-- Insert a real base coordinate and a Euclidean fibre at any tuple position. -/
def coordinateFibreChart {n : ℕ} (i : Fin (n + 1)) :
    (ℝ × EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] (Fin (n + 1) → ℝ) where
  toFun p := i.insertNth p.1 (WithLp.ofLp p.2)
  map_add' p q := by
    ext k
    refine i.succAboveCases ?_ (fun j => ?_) k
    · simp
    · simp
  map_smul' a p := by
    ext k
    refine i.succAboveCases ?_ (fun j => ?_) k
    · simp
    · simp

/-- A coordinate of a bounded convex Gibbs law has a normalized Borel
log-concave density. This is an internal general marginal theorem, with
normalization supplied by the probability instance on the given joint law. -/
theorem exists_coordinate_logConcaveDensity {n : ℕ}
    (Ω : Set (Fin (n + 1) → ℝ)) (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (V : (Fin (n + 1) → ℝ) → ℝ)
    (hV : ConvexOn ℝ Ω V) (c : ℝ) (hc : 0 < c)
    (i : Fin (n + 1))
    [IsProbabilityMeasure (volume.withDensity
      (fun y => ENNReal.ofReal (Ω.indicator (fun z => c * Real.exp (-V z)) y)))] :
    ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧
      (∫⁻ x, ENNReal.ofReal (f x)) = 1 ∧
      ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) ∧
      (volume.withDensity
        (fun y => ENNReal.ofReal (Ω.indicator (fun z => c * Real.exp (-V z)) y))).map
          (fun y => y i) = volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
  let L := coordinateFibreChart i
  let Q := L ⁻¹' Ω
  let W := V ∘ L
  have hLc : Continuous L := L.continuous_of_finiteDimensional
  have hQo : IsOpen Q := hΩo.preimage hLc
  have hW : ConvexOn ℝ Q W := hV.comp_linearMap L
  let split := fun y : Fin (n + 1) → ℝ =>
    (y i, WithLp.toLp 2 (i.removeNth y))
  have hsplit : Continuous split := by
    apply Continuous.prodMk (continuous_apply i)
    apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
    exact continuous_pi fun j => continuous_apply (i.succAbove j)
  have hQb : Bornology.IsBounded Q := by
    apply (hΩb.isCompact_closure.image hsplit).isBounded.subset
    intro p hp
    refine ⟨L p, subset_closure hp, ?_⟩
    simp [split, L, coordinateFibreChart]
  let J := Q.indicator (fun p => Real.exp (-W p))
  have hJm : Measurable J := Riesz1.measurable_exp_indicator hQo hW
  have hJi (x : ℝ) : Integrable (fun z => J (x, z)) :=
    Riesz1.integrable_fiber_exp_indicator hQo hQb hW x
  have hJ0 (p) : 0 ≤ J p := indicator_nonneg (fun _ _ => (Real.exp_pos _).le) p
  let f := fun x => c * ∫ z, J (x, z)
  have hfi (x : ℝ) : ENNReal.ofReal (f x) =
      ENNReal.ofReal c * ∫⁻ z, ENNReal.ofReal (J (x, z)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hJi x)
      (Filter.Eventually.of_forall fun z => hJ0 (x, z)), ← ENNReal.ofReal_mul hc.le]
  have hfm : Measurable f := by
    have hm : Measurable (fun x => ∫⁻ z : EuclideanSpace ℝ (Fin n),
        ENNReal.ofReal (J (x, z))) :=
      (ENNReal.measurable_ofReal.comp hJm).lintegral_prod_right'
    have he : f = fun x => (ENNReal.ofReal c *
        ∫⁻ z, ENNReal.ofReal (J (x, z))).toReal := by
      ext x
      rw [← hfi, ENNReal.toReal_ofReal (mul_nonneg hc.le (integral_nonneg fun z => hJ0 (x, z)))]
    rw [he]
    exact (measurable_const.mul hm).ennreal_toReal
  have hf0 (x : ℝ) : 0 ≤ f x := mul_nonneg hc.le (integral_nonneg fun z => hJ0 (x, z))
  have hpos : {x | 0 < f x} = Prod.fst '' Q := by
    ext x
    constructor
    · intro hx
      by_contra hxQ
      have hzero : ∀ z, J (x, z) = 0 := by
        intro z
        exact indicator_of_notMem (fun h => hxQ ⟨(x, z), h, rfl⟩) _
      have : f x = 0 := by simp [f, hzero]
      simp [this] at hx
    · intro hx
      exact mul_pos hc ((convexLocalization hQo hW.1 hQb hW (fun _ => 0)).1 x hx).2
  have hlog : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) := by
    rw [hpos]
    exact (convex_interval_marginal hQo hQb hW hW (fun _ => 0)
      (fun _ _ => by simp) hc).2.2.2.1
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i
  let F := fun p : ℝ × (Fin n → ℝ) =>
    Ω.indicator (fun z => c * Real.exp (-V z)) (e.symm p)
  have hF (p : ℝ × (Fin n → ℝ)) :
      F p = c * J (p.1, WithLp.toLp 2 p.2) := by
    change Ω.indicator _ (i.insertNth p.1 p.2) = _
    by_cases hp : i.insertNth p.1 p.2 ∈ Ω
    · rw [indicator_of_mem hp]
      change _ = c * Q.indicator _ (p.1, WithLp.toLp 2 p.2)
      rw [indicator_of_mem (show (p.1, WithLp.toLp 2 p.2) ∈ Q from hp)]
      rfl
    · rw [indicator_of_notMem hp]
      change _ = c * Q.indicator _ (p.1, WithLp.toLp 2 p.2)
      rw [indicator_of_notMem (show (p.1, WithLp.toLp 2 p.2) ∉ Q from hp), mul_zero]
  have hFm : Measurable F := by
    have he : F = fun p => c * J (p.1, WithLp.toLp 2 p.2) := funext hF
    rw [he]
    exact measurable_const.mul (hJm.comp (measurable_fst.prodMk
      ((PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).measurable.comp measurable_snd)))
  have hsplitLaw :
      (volume.withDensity (fun y => ENNReal.ofReal
        (Ω.indicator (fun z => c * Real.exp (-V z)) y))).map e =
      (volume.prod volume).withDensity (fun p => ENNReal.ofReal (F p)) := by
    have hcomp : (fun y => ENNReal.ofReal (Ω.indicator (fun z => c * Real.exp (-V z)) y)) =
        (fun p => ENNReal.ofReal (F p)) ∘ e := by
      ext y
      simp [F]
    rw [hcomp]
    exact (Riesz1.map_withDensity_comp volume e.measurable
      (g := fun p => ENNReal.ofReal (F p)) (ENNReal.measurable_ofReal.comp hFm)).trans
      (congrArg (fun μ => μ.withDensity (fun p => ENNReal.ofReal (F p)))
        (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).map_eq)
  have hfibre (x : ℝ) : (∫⁻ z, ENNReal.ofReal (F (x, z))) = ENNReal.ofReal (f x) := by
    have hint : (fun z : Fin n → ℝ => F (x, z)) =
        (fun z : EuclideanSpace ℝ (Fin n) => c * J (x, z)) ∘ WithLp.toLp 2 := by
      ext z
      exact hF (x, z)
    have hi : Integrable (fun z : Fin n → ℝ => F (x, z)) := by
      rw [hint]
      exact ((PiLp.volume_preserving_toLp (Fin n)).integrable_comp
        ((hJm.comp (measurable_const.prodMk measurable_id)).const_mul c).aestronglyMeasurable).mpr
        ((hJi x).const_mul c)
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun z => show 0 ≤ F (x, z) by
        rw [hF]; exact mul_nonneg hc.le (hJ0 _))]
    congr 1
    rw [← (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)).integral_comp'
      (fun z => F (x, z))]
    simp only [hF]
    exact integral_const_mul c _
  have hlaw : (volume.withDensity (fun y => ENNReal.ofReal
      (Ω.indicator (fun z => c * Real.exp (-V z)) y))).map (fun y => y i) =
      volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
    have he : (fun y : Fin (n + 1) → ℝ => y i) = Prod.fst ∘ e := rfl
    rw [he, ← Measure.map_map measurable_fst e.measurable, hsplitLaw,
      Riesz1.map_fst_withDensity_fiber volume volume (fun p => ENNReal.ofReal (F p))
        (ENNReal.measurable_ofReal.comp hFm)]
    congr 1
    exact funext hfibre
  have hprob : IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (f x))) := by
    rw [← hlaw]
    exact (Measure.isProbabilityMeasure_map_iff
      (measurable_pi_apply i).aemeasurable).mpr inferInstance
  refine ⟨f, hfm, hf0, ?_, hlog, hlaw⟩
  have hmass := hprob.measure_univ
  simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hmass

/-- Positive affine rescaling preserves normalized Borel log-concave densities,
with the full inverse Jacobian. The formula is valid on all of the real line. -/
theorem exists_affine_logConcaveDensity (f : ℝ → ℝ) (hfm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : (∫⁻ x, ENNReal.ofReal (f x)) = 1)
    (hlog : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)))
    (a b : ℝ) (ha : 0 < a) :
    ∃ g : ℝ → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x) ∧
      (∫⁻ x, ENNReal.ofReal (g x)) = 1 ∧
      ConcaveOn ℝ {x | 0 < g x} (fun x => Real.log (g x)) ∧
      (volume.withDensity (fun x => ENNReal.ofReal (f x))).map (fun x => a * x + b) =
        volume.withDensity (fun x => ENNReal.ofReal (g x)) := by
  let g := fun x => f ((x - b) / a) / a
  have hgm : Measurable g := (hfm.comp (by fun_prop)).div_const a
  have hg0 (x) : 0 ≤ g x := div_nonneg (hf0 _) ha.le
  have hmap : (volume : Measure ℝ).map (fun x => a * x + b) =
      ENNReal.ofReal a⁻¹ • volume := by
    have he : (fun x : ℝ => a * x + b) = (fun x => x + b) ∘ (fun x => a * x) := rfl
    rw [he, ← Measure.map_map (by fun_prop) (by fun_prop), Real.map_volume_mul_left ha.ne',
      Measure.map_smul, map_add_right_eq_self, abs_of_pos (inv_pos.mpr ha)]
    fun_prop
  have hlaw : (volume.withDensity (fun x => ENNReal.ofReal (f x))).map (fun x => a * x + b) =
      volume.withDensity (fun x => ENNReal.ofReal (g x)) := by
    have hc : (fun x => ENNReal.ofReal (f x)) =
        fun x => ENNReal.ofReal (f (((a * x + b) - b) / a)) := by
      ext x
      rw [add_sub_cancel_right, mul_div_cancel_left₀ x ha.ne']
    rw [hc, Riesz1.map_withDensity_comp volume (by fun_prop)
      (g := fun x => ENNReal.ofReal (f ((x - b) / a)))
      (ENNReal.measurable_ofReal.comp (hfm.comp (by fun_prop))),
      hmap, withDensity_smul_measure]
    have he : (fun x => ENNReal.ofReal (g x)) =
        ENNReal.ofReal a⁻¹ • (fun x => ENNReal.ofReal (f ((x - b) / a))) := by
      ext x
      change ENNReal.ofReal (f ((x - b) / a) / a) = _
      rw [div_eq_inv_mul, ENNReal.ofReal_mul (inv_pos.mpr ha).le]
      rfl
    rw [he]
    exact (withDensity_smul (f := fun x => ENNReal.ofReal (f ((x - b) / a))) _
      (ENNReal.measurable_ofReal.comp (hfm.comp (by fun_prop)))).symm
  have hprob : IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (f x))) :=
    ⟨by simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hf1⟩
  have hgp : IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (g x))) := by
    rw [← hlaw]
    exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr hprob
  let A : ℝ →ᵃ[ℝ] ℝ :=
    { toFun := fun x => (x - b) / a
      linear := a⁻¹ • LinearMap.id
      map_vadd' := by intro x y; simp [div_eq_mul_inv]; ring }
  have hpos : {x | 0 < g x} = A ⁻¹' {x | 0 < f x} := by
    ext x
    exact div_pos_iff_of_pos_right ha
  have hglog : ConcaveOn ℝ {x | 0 < g x} (fun x => Real.log (g x)) := by
    rw [hpos]
    apply ((hlog.comp_affineMap A).add_const (-Real.log a)).congr
    intro x hx
    change Real.log (f (A x)) + -Real.log a = Real.log (f (A x) / a)
    simpa only [sub_eq_add_neg] using
      (Real.log_div (show f (A x) ≠ 0 from ne_of_gt hx) ha.ne').symm
  refine ⟨g, hgm, hg0, ?_, hglog, hlaw⟩
  simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hgp.measure_univ

end Riesz2

end
