/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.WeightedSobolevIsometry
public import Riesz2.HelfferSjostrand.IntrinsicScalarCore
public import Riesz2.ToMathlib.VectorRadialComposition

/-!
# Orthonormal transport of the literal Neumann graph

Bridges for Proposition 3.3: the scalar values and rotated
weak gradients live in the existing L² carriers, and the graph and energy are
those of the Neumann realization.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff RealInnerProductSpace

namespace Riesz2.NeumannIsometryTransport

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The inverse orthonormal chart preserves the pushed-forward measure,
Proposition 3.3. -/
theorem measurePreserving_symm (e : E ≃ₗᵢ[ℝ] F) (ρ : Measure E) :
    MeasurePreserving e.symm (ρ.map e) ρ :=
  ⟨e.symm.continuous.measurable, e.toHomeomorph.toMeasurableEquiv.map_symm_map⟩

/-- Scalar L² values in an orthonormal chart, Proposition 3.3. This is the existing measure-preserving L² functor. -/
def valueMap (e : E ≃ₗᵢ[ℝ] F) (ρ : Measure E) :
    Lp ℝ 2 ρ →ₗᵢ[ℝ] Lp ℝ 2 (ρ.map e) :=
  Lp.compMeasurePreservingₗᵢ ℝ e.symm (measurePreserving_symm e ρ)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Chart values agree with composition almost everywhere, Proposition 3.3. -/
theorem valueMap_ae (e : E ≃ₗᵢ[ℝ] F) (ρ : Measure E) (f : Lp ℝ 2 ρ) :
    valueMap e ρ f =ᵐ[ρ.map e] f ∘ e.symm :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_symm e ρ)

/-- Native weak gradients in an orthonormal chart, Proposition 3.3. Both the base and the gradient are transported. -/
def gradientMap (e : E ≃ₗᵢ[ℝ] F) (ρ : Measure E) :
    Lp E 2 ρ →L[ℝ] Lp F 2 (ρ.map e) :=
  (e.toContinuousLinearEquiv.toContinuousLinearMap.compLpL 2 (ρ.map e)).comp
    (Lp.compMeasurePreservingₗᵢ ℝ e.symm (measurePreserving_symm e ρ)).toContinuousLinearMap

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Chart gradients have the actual rotated native values, Proposition 3.3. -/
theorem gradientMap_ae (e : E ≃ₗᵢ[ℝ] F) (ρ : Measure E) (g : Lp E 2 ρ) :
    gradientMap e ρ g =ᵐ[ρ.map e] fun y => e (g (e.symm y)) := by
  filter_upwards [e.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLpL
      (p := 2) (μ := ρ.map e) (Lp.compMeasurePreserving e.symm (measurePreserving_symm e ρ) g),
    Lp.coeFn_compMeasurePreserving g (measurePreserving_symm e ρ)] with y hy hz
  exact hy.trans (congrArg e hz)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Orthonormal gradient transport preserves the whole L² norm, Proposition 3.3. -/
theorem gradientMap_norm (e : E ≃ₗᵢ[ℝ] F) (ρ : Measure E) (g : Lp E 2 ρ) :
    ‖gradientMap e ρ g‖ = ‖g‖ := by
  let p := Lp.compMeasurePreserving e.symm (measurePreserving_symm e ρ) g
  have he : ∀ᵐ y ∂ρ.map e, ‖gradientMap e ρ g y‖ = ‖p y‖ := by
    filter_upwards [gradientMap_ae e ρ g,
      Lp.coeFn_compMeasurePreserving g (measurePreserving_symm e ρ)] with y hy hz
    rw [hy, hz, e.norm_map]
    rfl
  have hn : ‖gradientMap e ρ g‖ = ‖p‖ := le_antisymm
    (Lp.norm_le_norm_of_ae_le (he.mono fun _ h => h.le))
    (Lp.norm_le_norm_of_ae_le (he.mono fun _ h => h.ge))
  exact hn.trans (Lp.norm_compMeasurePreserving g (measurePreserving_symm e ρ))

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- The native gradient L² pairing is preserved, Proposition 3.3. -/
theorem gradientMap_inner (e : E ≃ₗᵢ[ℝ] F) (ρ : Measure E) (g h : Lp E 2 ρ) :
    inner ℝ (gradientMap e ρ g) (gradientMap e ρ h) = inner ℝ g h := by
  let T : Lp E 2 ρ →ₗᵢ[ℝ] Lp F 2 (ρ.map e) :=
    ⟨(gradientMap e ρ).toLinearMap, gradientMap_norm e ρ⟩
  exact T.inner_map_map g h

/-- The literal graph transports through an orthonormal chart,
Proposition 3.3. No new Sobolev encoding is introduced. -/
theorem neumannSobolevGraph_map (e : E ≃ₗᵢ[ℝ] F) {ρ : Measure E} [IsFiniteMeasure ρ]
    {U : Set E} (hB : Bornology.IsBounded U) (hρ : ∀ᵐ x ∂ρ, x ∈ U)
    (f : Lp ℝ 2 ρ) (g : Lp E 2 ρ) (hfg : (f, g) ∈ neumannSobolevGraph ρ U) :
    (valueMap e ρ f, gradientMap e ρ g) ∈ neumannSobolevGraph (ρ.map e) (e '' U) := by
  have hh : Riesz1.WeightedSobolev.IsWeightedH1 ρ U f g := by
    apply (VectorRadial.isWeightedH1_iff_neumannSobolevGraph hB hρ (Lp.memLp f) (Lp.memLp g)).mpr
    simpa only [Lp.toLp_coeFn] using hfg
  have ht := SobolevIsometry.weightedH1 e hρ hh
  have hs : ∀ᵐ y ∂ρ.map e, y ∈ e '' U := by
    apply e.toHomeomorph.measurableEmbedding.ae_map_iff.mpr
    exact hρ.mono fun x hx => mem_image_of_mem e hx
  have he := (VectorRadial.isWeightedH1_iff_neumannSobolevGraph
    (e.isometry.lipschitzWith.isBounded_image hB) hs ht.1 ht.2.1).mp ht
  have hv : ht.1.toLp (f ∘ e.symm) = valueMap e ρ f :=
    Lp.ext (ht.1.coeFn_toLp.trans (valueMap_ae e ρ f).symm)
  have hg : ht.2.1.toLp (fun y => e (g (e.symm y))) = gradientMap e ρ g :=
    Lp.ext (ht.2.1.coeFn_toLp.trans (gradientMap_ae e ρ g).symm)
  rwa [hv, hg] at he

/-- The scalar graph is identified in both directions, Proposition 3.3. The converse pulls back the actual weak gradients.
No regularity is inferred from an arbitrary L² representative. -/
theorem neumannSobolevGraph_map_iff (e : E ≃ₗᵢ[ℝ] F) {ρ : Measure E} [IsFiniteMeasure ρ]
    {U : Set E} (hB : Bornology.IsBounded U) (hρ : ∀ᵐ x ∂ρ, x ∈ U)
    (f : Lp ℝ 2 ρ) (g : Lp E 2 ρ) :
    (valueMap e ρ f, gradientMap e ρ g) ∈ neumannSobolevGraph (ρ.map e) (e '' U) ↔
      (f, g) ∈ neumannSobolevGraph ρ U := by
  refine ⟨fun hfg => ?_, neumannSobolevGraph_map e hB hρ f g⟩
  have hs : ∀ᵐ y ∂ρ.map e, y ∈ e '' U := by
    apply e.toHomeomorph.measurableEmbedding.ae_map_iff.mpr
    exact hρ.mono fun x hx => mem_image_of_mem e hx
  have hh : Riesz1.WeightedSobolev.IsWeightedH1 (ρ.map e) (e '' U)
      (valueMap e ρ f) (gradientMap e ρ g) := by
    apply (VectorRadial.isWeightedH1_iff_neumannSobolevGraph
      (e.isometry.lipschitzWith.isBounded_image hB) hs (Lp.memLp _) (Lp.memLp _)).mpr
    simpa only [Lp.toLp_coeFn] using hfg
  have hb := SobolevIsometry.weightedH1 e.symm hs hh
  have hμ : (ρ.map e).map e.symm = ρ := e.toHomeomorph.toMeasurableEquiv.map_symm_map
  have hU : e.symm '' (e '' U) = U := by ext x; simp
  rw [hμ, hU] at hb
  have hp : MeasurePreserving e ρ (ρ.map e) := ⟨e.continuous.measurable, rfl⟩
  have hf : (valueMap e ρ f ∘ e) =ᵐ[ρ] f := by
    filter_upwards [hp.quasiMeasurePreserving.ae (valueMap_ae e ρ f)] with x hx
    simpa only [Function.comp_apply, e.symm_apply_apply] using hx
  have hg : (fun x => e.symm (gradientMap e ρ g (e x))) =ᵐ[ρ] g := by
    filter_upwards [hp.quasiMeasurePreserving.ae (gradientMap_ae e ρ g)] with x hx
    simpa only [e.symm_apply_apply] using congrArg e.symm hx
  have hn := hb.congr hf hg
  apply (VectorRadial.isWeightedH1_iff_neumannSobolevGraph hB hρ (Lp.memLp f) (Lp.memLp g)).mp
    at hn
  simpa only [Lp.toLp_coeFn] using hn

/-- The scalar energy in the two existing Neumann realizations agrees
under chart transport, Proposition 3.3. This also covers
mixed scalar pairings, as required for vector diffusion and scalar Poisson. -/
theorem realization_energy_map (e : E ≃ₗᵢ[ℝ] F) {ρ : Measure E}
    {U : Set E} (Q : ScalarFormData ρ) (Q' : ScalarFormData (ρ.map e))
    (hQ : IsNeumannRealization U Q) (hQ' : IsNeumannRealization (e '' U) Q')
    (f h : Q.1) (f' h' : Q'.1) (g k : Lp E 2 ρ)
    (hfg : (f.val, g) ∈ neumannSobolevGraph ρ U)
    (hhk : (h.val, k) ∈ neumannSobolevGraph ρ U)
    (hfg' : (f'.val, gradientMap e ρ g) ∈ neumannSobolevGraph (ρ.map e) (e '' U))
    (hhk' : (h'.val, gradientMap e ρ k) ∈ neumannSobolevGraph (ρ.map e) (e '' U)) :
    Q'.2 f' h' = Q.2 f h := by
  rw [hQ.2.2 f h g k hfg hhk, hQ'.2.2 f' h' _ _ hfg' hhk', gradientMap_inner]

omit [BorelSpace E] in
/-- Every finite tuple in a realized scalar form has native weak component
gradients with exactly the required summed Hessian energy, Proposition 3.3. The component count is independent of the base. -/
theorem component_gradients {ι : Type*} [Fintype ι]
    {ρ : Measure E} {U : Set E} (Q : ScalarFormData ρ)
    (hQ : IsNeumannRealization U Q) (u : ι → Q.1) :
    ∃ du : ι → Lp E 2 ρ,
      (∀ i, ((u i).val, du i) ∈ neumannSobolevGraph ρ U) ∧
      (∑ i, Q.2 (u i) (u i)) = ∑ i, ‖du i‖ ^ 2 := by
  choose du hdu using fun i => (hQ.1 (u i).val).mp (u i).property
  refine ⟨du, hdu, Finset.sum_congr rfl fun i _ => ?_⟩
  rw [hQ.2.2 (u i) (u i) (du i) (du i) (hdu i) (hdu i), real_inner_self_eq_norm_sq]

end Riesz2.NeumannIsometryTransport
