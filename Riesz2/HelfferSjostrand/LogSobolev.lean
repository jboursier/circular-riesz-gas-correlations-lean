/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Bridges.ConvexMeasureInputs
public import Riesz2.Frozen.IsEuclideanGibbsPotential
public import Riesz1.ToMathlib.WeightedSobolev.Graph
public import Riesz1.ToMathlib.LogConcave.PrekopaContinuity
public import Mathlib.Analysis.Normed.Affine.Isometry

/-!
# Logarithmic Sobolev constant of a uniformly convex potential

See Lemma 3.7 of the paper. Convexity of `V - c|x|²/2` suffices. The
potential need not be twice differentiable. Entropy integrability is part of
the conclusion. The final interface uses the Gibbs potential and
Neumann graph, with the gradient norm of the Euclidean chart itself.
-/

public section

noncomputable section

open MeasureTheory Filter Set Topology

namespace Riesz2

/-- See Lemma 3.7 of the paper: the logarithmic Sobolev constant is `2 / c`.
The convex remainder is finite on the open convex domain. The coefficient
`a` is the normalization in `ρ ∝ exp(-V)` and is unrestricted a priori:
positivity follows from the probability assumption. -/
theorem logSobolev_of_convex_sub_quadratic {d : ℕ} (hd : 1 ≤ d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    {V : EuclideanSpace ℝ (Fin d) → ℝ} {c : ℝ} (hc : 0 < c)
    (hV : ConvexOn ℝ Ω (fun x => V x - c / 2 * ‖x‖ ^ 2))
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ρ] {a : ℝ}
    (hρ : ρ = (volume.restrict Ω).withDensity
      (fun x => ENNReal.ofReal (a * Real.exp (-V x))))
    (F : EuclideanSpace ℝ (Fin d) → ℝ)
    (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hFG : Riesz1.WeightedSobolev.IsWeightedH1 ρ Ω F G) :
    Integrable (fun x => F x ^ 2) ρ ∧
      Integrable (fun x => F x ^ 2 * Real.log (F x ^ 2)) ρ ∧
      Integrable (fun x => ‖G x‖ ^ 2) ρ ∧
      (∫ x, F x ^ 2 * Real.log (F x ^ 2) ∂ρ) -
          (∫ x, F x ^ 2 ∂ρ) * Real.log (∫ x, F x ^ 2 ∂ρ) ≤
        2 / c * ∫ x, ‖G x‖ ^ 2 ∂ρ := by
  classical
  let f := Ω.indicator (fun x => Real.exp (-(V x - c / 2 * ‖x‖ ^ 2)))
  have hf : Measurable f := Riesz1.measurable_indicator_of_continuousOn
    hΩo (Real.continuous_exp.comp_continuousOn (hV.continuousOn hΩo).neg)
  have hf0 : ∀ x, 0 ≤ f x := indicator_nonneg fun x _ => (Real.exp_pos _).le
  have hs : {x | 0 < f x} = Ω := by
    ext x
    by_cases hx : x ∈ Ω
    · simp only [mem_ofPred_eq, f, indicator_of_mem hx, hx, iff_true]
      exact Real.exp_pos _
    · simp [f, hx]
  have hflc : ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) := by
    rw [hs]
    refine hV.neg.congr fun x hx => ?_
    simp [f, hx]
  have hρ' : ρ = (volume.restrict Ω).withDensity
      (fun x => ENNReal.ofReal (a * (Real.exp (-(c / 2 * ‖x‖ ^ 2)) * f x))) := by
    rw [hρ]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem hΩo.measurableSet] with x hx
    simp only [f, indicator_of_mem hx]
    rw [← Real.exp_add]
    congr 3
    ring
  exact log_sobolev_conditioning hd hΩc hΩo hc hf hf0 hflc ρ hρ' F G hFG

/-- See Subsection 3.1 of the paper: a pair in the Neumann graph satisfies the
companion library's Sobolev predicate for its L² representatives. This
direction needs neither boundedness of the domain nor finiteness of the law. -/
theorem isWeightedH1_of_mem_neumannSobolevGraph
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] {ρ : Measure E} {Ω : Set E}
    {F : Lp ℝ 2 ρ} {G : Lp E 2 ρ} (h : (F, G) ∈ neumannSobolevGraph ρ Ω) :
    Riesz1.WeightedSobolev.IsWeightedH1 ρ Ω F G := by
  obtain ⟨p, hp, hlim⟩ := mem_closure_iff_seq_limit.mp h
  choose f hf hg hs heq using hp
  have hv : Tendsto (fun k => (hf k).toLp (f k)) atTop (𝓝 F) := by
    simpa only [Function.comp_def, heq] using (continuous_fst.tendsto (F, G)).comp hlim
  have hd : Tendsto (fun k => (hg k).toLp (gradient (f k))) atTop (𝓝 G) := by
    simpa only [Function.comp_def, heq] using (continuous_snd.tendsto (F, G)).comp hlim
  refine ⟨Lp.memLp F, Lp.memLp G, f, hs, ?_, ?_⟩
  · apply (Riesz1.WeightedSobolev.tendsto_toLp_iff_lintegral_sq f hf F (Lp.memLp F)).mp
    simpa only [Lp.toLp_coeFn] using hv
  · apply (Riesz1.WeightedSobolev.tendsto_toLp_iff_lintegral_sq
      (fun k => gradient (f k)) hg G (Lp.memLp G)).mp
    simpa only [Lp.toLp_coeFn] using hd

/-- See Lemma 3.7 of the paper, using the Gibbs potential and Neumann graph.
The conclusion includes entropy integrability. -/
theorem logSobolev_of_gibbsPotential {d : ℕ} (hd : 1 ≤ d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    {ρ : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure ρ]
    {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : IsEuclideanGibbsPotential volume ρ Ω V)
    {c : ℝ} (hc : 0 < c)
    (hVc : ConvexOn ℝ Ω (fun x => V x - c / 2 * ‖x‖ ^ 2))
    (F : Lp ℝ 2 ρ) (G : Lp (EuclideanSpace ℝ (Fin d)) 2 ρ)
    (hFG : (F, G) ∈ neumannSobolevGraph ρ Ω) :
    Integrable (fun x => F x ^ 2) ρ ∧
      Integrable (fun x => F x ^ 2 * Real.log (F x ^ 2)) ρ ∧
      Integrable (fun x => ‖G x‖ ^ 2) ρ ∧
      (∫ x, F x ^ 2 * Real.log (F x ^ 2) ∂ρ) -
          (∫ x, F x ^ 2 ∂ρ) * Real.log (∫ x, F x ^ 2 ∂ρ) ≤
        2 / c * ∫ x, ‖G x‖ ^ 2 ∂ρ := by
  obtain ⟨_, hZ0, hZt, hρ⟩ := hV
  apply logSobolev_of_convex_sub_quadratic hd hΩo hΩc hc hVc ρ
    (a := (∫⁻ x in Ω, ENNReal.ofReal (Real.exp (-V x))).toReal⁻¹) ?_ F G
    (isWeightedH1_of_mem_neumannSobolevGraph hFG)
  rw [hρ, ← withDensity_smul' _ _ (ENNReal.inv_ne_top.mpr hZ0.ne')]
  congr 1
  funext x
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos
    (ENNReal.toReal_pos hZ0.ne' hZt.ne), ENNReal.ofReal_toReal hZt.ne]
  rfl

/-- See Lemma 3.7 of the paper, the affine Euclidean version. The Gibbs
potential and H¹ pair are expressed in an orthonormal affine chart, the
convention of Subsection 3.1. Pulling the gradient back by the chart's linear
isometry gives the intrinsic gradient on the affine space. Integrals and the
constant `2 / c` are preserved. This includes affine subspaces with their
intrinsic volume, whose constant chart Jacobian is absorbed in normalization. -/
theorem logSobolev_of_affine_chart
    {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MetricSpace P] [NormedAddTorsor E P] [MeasurableSpace P] [BorelSpace P]
    {d : ℕ} (hd : 1 ≤ d) (e : P ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin d))
    (ρ : Measure P) [IsProbabilityMeasure ρ]
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    {V : EuclideanSpace ℝ (Fin d) → ℝ}
    (hV : IsEuclideanGibbsPotential volume (ρ.map e) Ω V)
    {c : ℝ} (hc : 0 < c)
    (hVc : ConvexOn ℝ Ω (fun x => V x - c / 2 * ‖x‖ ^ 2))
    (F : Lp ℝ 2 (ρ.map e)) (G : Lp (EuclideanSpace ℝ (Fin d)) 2 (ρ.map e))
    (hFG : (F, G) ∈ neumannSobolevGraph (ρ.map e) Ω) :
    Integrable (fun x => F (e x) ^ 2) ρ ∧
      Integrable (fun x => F (e x) ^ 2 * Real.log (F (e x) ^ 2)) ρ ∧
      Integrable (fun x => ‖e.linearIsometryEquiv.symm (G (e x))‖ ^ 2) ρ ∧
      (∫ x, F (e x) ^ 2 * Real.log (F (e x) ^ 2) ∂ρ) -
          (∫ x, F (e x) ^ 2 ∂ρ) * Real.log (∫ x, F (e x) ^ 2 ∂ρ) ≤
        2 / c * ∫ x, ‖e.linearIsometryEquiv.symm (G (e x))‖ ^ 2 ∂ρ := by
  have he : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  obtain ⟨hF, hEnt, hG, hLS⟩ := logSobolev_of_gibbsPotential hd hΩo hΩc hV hc hVc F G hFG
  refine ⟨he.integrable_map_iff.mp hF, he.integrable_map_iff.mp hEnt, ?_, ?_⟩
  · simpa only [Function.comp_def, LinearIsometryEquiv.norm_map] using
      he.integrable_map_iff.mp hG
  · simpa only [he.integral_map, LinearIsometryEquiv.norm_map] using hLS

end Riesz2

end
