/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.ConvergesInLawAlong
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

/-!
# Deterministic scaling of weakly convergent real laws

Joint continuity of product probability measures and continuous multiplication give the
varying deterministic scaling needed for mesoscopic normalization.
-/

public section

open MeasureTheory Filter Topology

namespace Riesz2

/-- Multiplication by a converging deterministic factor preserves weak convergence. -/
theorem convergesInLawAlong_map_mul {ι : Type*} {l : Filter ι}
    {μ : ι → Measure ℝ} {ν : Measure ℝ} (h : ConvergesInLawAlong l μ ν)
    {c : ι → ℝ} {a : ℝ} (hc : Tendsto c l (𝓝 a)) :
    ConvergesInLawAlong l (fun i => (μ i).map (fun x => c i * x))
      (ν.map (fun x => a * x)) := by
  have : ∀ i, IsProbabilityMeasure (μ i) := h.1
  have : IsProbabilityMeasure ν := h.2.1
  let m : ι → ProbabilityMeasure ℝ := fun i => ⟨μ i, h.1 i⟩
  let v : ProbabilityMeasure ℝ := ⟨ν, h.2.1⟩
  have hm : Tendsto m l (𝓝 v) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr h.2.2
  let d : ℝ → ProbabilityMeasure ℝ := fun x => ⟨Measure.dirac x, by infer_instance⟩
  have hd : Tendsto (fun i => d (c i)) l (𝓝 (d a)) := by
    apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro f
    simpa [d, Function.comp_def] using f.continuous.continuousAt.tendsto.comp hc
  have hp := ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp (hm.prodMk_nhds hd)
  have ht := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun i => (m i).prod (d (c i))) (v.prod (d a)) hp
    (f := fun z : ℝ × ℝ => z.2 * z.1) (by fun_prop)
  have heq (ρ : ProbabilityMeasure ℝ) (b : ℝ) :
      ((ρ.prod (d b)).map (fun z : ℝ × ℝ => z.2 * z.1) : Measure ℝ) =
        (ρ : Measure ℝ).map (fun x => b * x) := by
    change ((ρ : Measure ℝ).prod (Measure.dirac b)).map
      (fun z : ℝ × ℝ => z.2 * z.1) = _
    rw [Measure.prod_dirac, Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  refine ⟨fun i => (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance,
    (Measure.isProbabilityMeasure_map_iff (by fun_prop)).mpr inferInstance, fun f => ?_⟩
  have hf := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp ht f
  simp only [heq] at hf
  exact hf

end Riesz2
