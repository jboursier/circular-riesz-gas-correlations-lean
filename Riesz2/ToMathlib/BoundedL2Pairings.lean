/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Integrable coefficients on bounded L² classes

The domain is the actual submodule of essentially bounded L² functions.
An integrable, possibly unbounded coefficient gives a bilinear pairing on
this domain. No continuity in the L² norm is asserted.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace Riesz2.BoundedL2Pairings

variable {X : Type*} [MeasurableSpace X] (ν : Measure X)

/-- The submodule of L² classes with a finite essential bound. -/
def boundedSubmodule : Submodule ℝ (Lp ℝ 2 ν) where
  carrier := {f | ∃ B : ℝ, ∀ᵐ x ∂ν, |f x| ≤ B}
  zero_mem' := ⟨0, by
    change ∀ᵐ x ∂ν, |(0 : Lp ℝ 2 ν) x| ≤ 0
    filter_upwards [Lp.coeFn_zero ℝ 2 ν] with x hx
    simpa only [Pi.zero_apply, abs_zero] using (le_of_eq (congrArg abs hx))⟩
  add_mem' := by
    rintro f g ⟨B, hB⟩ ⟨C, hC⟩
    refine ⟨B + C, ?_⟩
    filter_upwards [hB, hC, Lp.coeFn_add f g] with x hf hg ha
    rw [ha]
    exact (abs_add_le _ _).trans (add_le_add hf hg)
  smul_mem' := by
    rintro c f ⟨B, hB⟩
    refine ⟨|c| * B, ?_⟩
    filter_upwards [hB, Lp.coeFn_smul c f] with x hf hs
    rw [hs]
    simpa only [Pi.smul_apply, smul_eq_mul, abs_mul] using
      mul_le_mul_of_nonneg_left hf (abs_nonneg c)

variable {ν}

/-- The essential supremum is finite on the bounded submodule. -/
theorem memLp_top (f : boundedSubmodule ν) : MemLp (f.val : X → ℝ) ∞ ν := by
  obtain ⟨B, hB⟩ := f.property
  rw [memLp_iff, eLpNorm_exponent_top (Lp.aestronglyMeasurable f.val)]
  exact eLpNormEssSup_lt_top_of_ae_bound
    (hB.mono fun x hx => by simpa only [Real.norm_eq_abs] using hx)

/-- Any explicit essential bound bounds the real essential supremum.
Its finiteness has been proved before applying `toReal`. -/
theorem essentialNorm_le (f : boundedSubmodule ν) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ᵐ x ∂ν, |f.val x| ≤ B) :
    (eLpNorm (f.val : X → ℝ) ∞ ν).toReal ≤ B := by
  have he : eLpNorm (f.val : X → ℝ) ∞ ν ≤ ENNReal.ofReal B := by
    rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable f.val)]
    exact eLpNormEssSup_le_of_ae_bound
      (hf.mono fun x hx => by simpa only [Real.norm_eq_abs] using hx)
  simpa only [ENNReal.toReal_ofReal hB] using ENNReal.toReal_mono ENNReal.ofReal_ne_top he

/-- An integrable coefficient pairs integrably with any two bounded L²
classes. This applies without finite total mass. -/
theorem integrable_product (Y : X → ℝ) (hY : Integrable Y ν)
    (f g : boundedSubmodule ν) :
    Integrable (fun x => f.val x * Y x * g.val x) ν := by
  obtain ⟨B, hB⟩ := f.property
  obtain ⟨C, hC⟩ := g.property
  exact (hY.bdd_mul (Lp.aestronglyMeasurable f.val)
    (by simpa only [Real.norm_eq_abs] using hB)).mul_bdd
    (Lp.aestronglyMeasurable g.val) (by simpa only [Real.norm_eq_abs] using hC)

/-- The multiplication pairing on its whole bounded L² domain. The
coefficient is required to be integrable before the map is constructed. -/
def coefficientPair (Y : X → ℝ) (hY : Integrable Y ν) :
    boundedSubmodule ν →ₗ[ℝ] boundedSubmodule ν →ₗ[ℝ] ℝ where
  toFun f :=
    { toFun := fun g => ∫ x, f.val x * Y x * g.val x ∂ν
      map_add' := by
        intro g h
        have he : (fun x => f.val x * Y x * (g + h).val x) =ᵐ[ν]
            fun x => f.val x * Y x * g.val x + f.val x * Y x * h.val x := by
          filter_upwards [Lp.coeFn_add g.val h.val] with x hx
          simp only [Submodule.coe_add, hx, Pi.add_apply, mul_add]
        rw [integral_congr_ae he, integral_add (integrable_product Y hY f g)
          (integrable_product Y hY f h)]
      map_smul' := by
        intro c g
        have he : (fun x => f.val x * Y x * (c • g).val x) =ᵐ[ν]
            fun x => c * (f.val x * Y x * g.val x) := by
          filter_upwards [Lp.coeFn_smul c g.val] with x hx
          simp only [Submodule.coe_smul, hx, Pi.smul_apply, smul_eq_mul]
          ring
        simpa only [RingHom.id_apply, smul_eq_mul] using
          (integral_congr_ae he).trans (integral_const_mul _ _) }
  map_add' := by
    intro f g
    ext h
    have he : (fun x => (f + g).val x * Y x * h.val x) =ᵐ[ν]
        fun x => f.val x * Y x * h.val x + g.val x * Y x * h.val x := by
      filter_upwards [Lp.coeFn_add f.val g.val] with x hx
      simp only [Submodule.coe_add, hx, Pi.add_apply, add_mul]
    exact (integral_congr_ae he).trans
      (integral_add (integrable_product Y hY f h) (integrable_product Y hY g h))
  map_smul' := by
    intro c f
    ext g
    have he : (fun x => (c • f).val x * Y x * g.val x) =ᵐ[ν]
        fun x => c * (f.val x * Y x * g.val x) := by
      filter_upwards [Lp.coeFn_smul c f.val] with x hx
      simp only [Submodule.coe_smul, hx, Pi.smul_apply, smul_eq_mul]
      ring
    exact (integral_congr_ae he).trans (integral_const_mul _ _)

/-- Evaluation of the pairing retains its integrable coefficient. -/
theorem coefficientPair_apply (Y : X → ℝ) (hY : Integrable Y ν)
    (f g : boundedSubmodule ν) :
    coefficientPair Y hY f g = ∫ x, f.val x * Y x * g.val x ∂ν := rfl

end Riesz2.BoundedL2Pairings
