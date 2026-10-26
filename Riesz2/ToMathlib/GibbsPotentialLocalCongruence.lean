/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.IsEuclideanGibbsPotential
public import Riesz2.ToMathlib.AffineFibreDisintegration

/-!
# Local congruence for normalized Gibbs potentials

Potentials agreeing on the physical domain determine exactly the same
normalized measure. Values outside the domain never enter this assertion.
The consumer is the proof of Proposition 6.6.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Riesz2.GibbsPotentialLocalCongruence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] {σ μ ν : Measure E} {U : Set E} {V W : E → ℝ}

/-- Equality on the domain preserves the complete Gibbs predicate,
including its positive finite normalizer and its literal law. -/
theorem congr (hV : IsEuclideanGibbsPotential σ μ U V) (hU : MeasurableSet U)
    (he : EqOn V W U) : IsEuclideanGibbsPotential σ μ U W := by
  have hw : (fun x => ENNReal.ofReal (Real.exp (-V x))) =ᵐ[σ.restrict U]
      (fun x => ENNReal.ofReal (Real.exp (-W x))) :=
    (ae_restrict_mem hU).mono (fun x hx => by dsimp only; rw [he hx])
  have hZ := lintegral_congr_ae hw
  refine ⟨hV.1.congr he.symm, ?_⟩
  change 0 < _ ∧ _ < ⊤ ∧ _
  rw [← hZ, ← withDensity_congr_ae hw]
  exact hV.2

/-- The normalized Gibbs predicate determines the measure uniquely. -/
theorem unique (hV : IsEuclideanGibbsPotential σ μ U V)
    (hW : IsEuclideanGibbsPotential σ ν U V) : μ = ν :=
  hV.2.2.2.trans hW.2.2.2.symm

/-- The Gibbs law is exactly the pushforward of the normalized density
on the domain subtype. This uses the restricted reference measure, so
no global measurability of exterior values of the potential is needed. -/
theorem normalized_subtype (hV : IsEuclideanGibbsPotential σ μ U V)
    (hU : MeasurableSet U)
    (hw : Measurable (fun x : U => ENNReal.ofReal (Real.exp (-V x.val)))) :
    ∃ (h0 : (∫⁻ x : U, ENNReal.ofReal (Real.exp (-V x.val)) ∂σ.comap Subtype.val) ≠ 0)
      (ht : (∫⁻ x : U, ENNReal.ofReal (Real.exp (-V x.val)) ∂σ.comap Subtype.val) ≠ ⊤),
      (AffineFibre.normalizedMeasure (σ.comap (Subtype.val : U → E))
        (fun x : U => ENNReal.ofReal (Real.exp (-V x.val))) h0 ht).map Subtype.val = μ := by
  let e := (Subtype.val : U → E)
  let ξ := σ.comap e
  let w := fun x : U => ENNReal.ofReal (Real.exp (-V x.val))
  have he := MeasurableEmbedding.subtype_coe hU
  have href : ξ.map e = σ.restrict U := map_comap_subtype_coe hU σ
  have hZ : (∫⁻ x, w x ∂ξ) = ∫⁻ x, ENNReal.ofReal (Real.exp (-V x)) ∂σ.restrict U := by
    rw [← href,he.lintegral_map]
  have h0 : (∫⁻ x, w x ∂ξ) ≠ 0 := hZ ▸ hV.2.1.ne'
  have ht : (∫⁻ x, w x ∂ξ) ≠ ⊤ := hZ ▸ hV.2.2.1.ne
  obtain ⟨w',hw',hext⟩ := he.exists_measurable_extend hw (fun _ => inferInstance)
  have hw'e : (fun x : U => w' (e x)) = w := hext
  have h0' : (∫⁻ x, w' (e x) ∂ξ) ≠ 0 := by rw [hw'e]; exact h0
  have ht' : (∫⁻ x, w' (e x) ∂ξ) ≠ ⊤ := by rw [hw'e]; exact ht
  have hm := AffineFibre.normalizedMeasure_map ξ he hw' h0' ht'
  have hew : w' =ᵐ[σ.restrict U] fun x => ENNReal.ofReal (Real.exp (-V x)) := by
    filter_upwards [ae_restrict_mem hU] with x hx
    exact congrFun hw'e ⟨x,hx⟩
  refine ⟨h0,ht,?_⟩
  change (AffineFibre.normalizedMeasure ξ w h0 ht).map e = μ
  simp only [AffineFibre.normalizedMeasure_eq_smul] at hm ⊢
  rw [he.lintegral_map] at hm
  change (∫⁻ x, w' (e x) ∂ξ)⁻¹ • (ξ.map e).withDensity w' =
    ((∫⁻ x, w' (e x) ∂ξ)⁻¹ • ξ.withDensity (fun x => w' (e x))).map e at hm
  rw [hw'e] at hm
  rw [← hm,href,hZ,withDensity_congr_ae hew]
  exact hV.2.2.2.symm

end Riesz2.GibbsPotentialLocalCongruence
