/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.IntrinsicScalarCore
public import Riesz2.ToMathlib.VectorRadialComposition

/-!
# Compact vector cores and radial matrix-energy limits

The compact core for Subsection 3.1 uses intrinsic scalar jets and their
compact smooth test subspace. Its completion is taken in the sum of the H¹
and square-root matrix-energy norms. This completion is included in the
natural finite-energy domain. The radial matrix-energy limit proves the
Hessian-energy part of the first approximation step for unbounded coefficients.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator

namespace Riesz2.VectorCore

section CompactCore

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι] [DecidableEq ι] {ρ : Measure E} {U : Set E} {V : E → ℝ}
  (hU : IsOpen U) (hB : Bornology.IsBounded U)
  (hV : IsEuclideanGibbsPotential volume ρ U V)

open IntrinsicScalarCore MatrixEnergy

local instance : InnerProductSpace ℝ (ScalarForm.Domain (jet hU hB hV)) := inferInstance
local instance : InnerProductSpace ℝ
    (PiLp 2 (fun _ : ι => ScalarForm.Domain (jet hU hB hV))) := PiLp.innerProductSpace _

/-- Compact smooth scalar fields, component by component, in the existing intrinsic
H¹ jet domain. The component count is independent of the base dimension. -/
def compactBase : Submodule ℝ
    (PiLp 2 (fun _ : ι => ScalarForm.Domain (jet hU hB hV))) where
  carrier := {u | ∀ i, u i ∈ compactFormDomain hU hB hV}
  zero_mem' := fun _ => (compactFormDomain hU hB hV).zero_mem
  add_mem' hu hw i := (compactFormDomain hU hB hV).add_mem (hu i) (hw i)
  smul_mem' a _ hu i := (compactFormDomain hU hB hV).smul_mem a (hu i)

/-- The existing scalar value projection on each intrinsic vector component. -/
def componentValue (i : ι) :
    PiLp 2 (fun _ : ι => ScalarForm.Domain (jet hU hB hV)) →L[ℝ] Lp ℝ 2 ρ :=
  (ScalarForm.value (jet hU hB hV)).comp (PiLp.proj 2 _ i)

/-- See Subsection 3.1 of the paper: the compact smooth vector core, including the coordinates
of a matrix multiplier and a fixed component constraint. For the Hessian form, the
multiplier is its positive square root. An arbitrary multiplier also makes sense. -/
def compactGraph (B : E → Matrix ι ι ℝ) (S : Submodule ℝ (ι → ℝ)) :
    Submodule ℝ (MatrixEnergy.Jet (κ := ι) (ρ := ρ)
      (H := PiLp 2 (fun _ : ι => ScalarForm.Domain (jet hU hB hV)))) :=
  graph (componentValue hU hB hV) B S ⊓
    (compactBase hU hB hV).comap (WithLp.fstL 2 ℝ _ _).toLinearMap

/-- See Subsection 3.1 of the paper: completion of the compact smooth vector core in mass,
diffusion and matrix energy, in the same ambient jets as the natural graph. -/
def compactCompletion (B : E → Matrix ι ι ℝ) (S : Submodule ℝ (ι → ℝ)) :=
  (compactGraph hU hB hV B S).topologicalClosure

set_option backward.isDefEq.respectTransparency false in
omit [DecidableEq ι] in
/-- The closed-multiplier half of Subsection 3.1: every compact
core limit lies in the full natural square-root graph. No density assertion is used. -/
theorem compactCompletion_le_graph (B : E → Matrix ι ι ℝ)
    (S : Submodule ℝ (ι → ℝ)) :
    compactCompletion hU hB hV B S ≤ graph (componentValue hU hB hV) B S := by
  apply Submodule.topologicalClosure_minimal
  · exact inf_le_left
  · exact isClosed_graph (ι := ι) (κ := ι)
      (H := PiLp 2 (fun _ : ι => ScalarForm.Domain (jet hU hB hV)))
      (componentValue (ι := ι) hU hB hV) B S

/-- Partial conclusion of Subsection 3.1, stated with the natural domain: a compact-core limit has a tuple of H¹ values with
finite matrix energy and the required fixed-subspace constraint. -/
theorem compactCompletion_finite_energy (M : E → Matrix ι ι ℝ)
    (S : Submodule ℝ (ι → ℝ))
    (hMmeas : ∀ i j, Measurable (fun x => M x i j))
    (hM : ∀ᵐ x ∂ρ, (M x).PosSemidef)
    (z : compactCompletion hU hB hV (fun x => CFC.sqrt (M x)) S) :
    ∃ u : ι → (form hU hB hV).1,
      WeightedFormDomain (form hU hB hV) M S u ∧
      ∀ i, (u i).val = input (componentValue hU hB hV) i z.val := by
  let u : ι → (form hU hB hV).1 := fun i =>
    ScalarForm.valueEquiv (jet hU hB hV) (value_injective hU hB hV)
      ((WithLp.ofLp z.val).1 i)
  have hu (i : ι) : (u i).val = input (componentValue hU hB hV) i z.val := rfl
  have hz := compactCompletion_le_graph hU hB hV (fun x => CFC.sqrt (M x)) S z.property
  refine ⟨u, ⟨?_, ?_⟩, hu⟩
  · filter_upwards [hz] with x hx
    simpa only [hu] using hx.1
  · apply (integrable_iff_memLp_factor M (fun x => CFC.sqrt (M x))
      (fun i j => (measurable_sqrt_entries M hMmeas i j).aestronglyMeasurable)
      (hM.mono (fun x hx => sqrt_factor (M x) hx)) (fun i => (u i).val)).mpr
    intro k
    apply (Lp.memLp (output k z.val)).ae_eq
    filter_upwards [hz] with x hx
    simpa only [hu] using hx.2 k

end CompactCore

namespace Internal

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι] {ρ : Measure α}

/-- Matrix-energy approximation step of Subsection 3.1:
the radial excess tends to zero in the full, possibly unbounded matrix energy.
Absolute integrability is proved separately for every member of the sequence. -/
theorem tendsto_matrixEnergy_radial_excess (M : α → Matrix ι ι ℝ)
    (hMmeas : ∀ i j, Measurable (fun x => M x i j))
    (hM : ∀ᵐ x ∂ρ, (M x).PosSemidef) (u : ι → Lp ℝ 2 ρ)
    (hu : Integrable (matrixFieldPair M u u) ρ) :
    (∀ n : ℕ, Integrable
      (matrixFieldPair M (VectorRadial.truncateValues n u)
        (VectorRadial.truncateValues n u)) ρ) ∧
    Tendsto (fun n : ℕ => ∫ x, matrixFieldPair M (VectorRadial.truncateValues n u)
      (VectorRadial.truncateValues n u) x ∂ρ) atTop (𝓝 0) := by
  have hi (n : ℕ) :=
    VectorRadial.integrable_matrixFieldPair_truncateValues n M hMmeas hM u hu
  refine ⟨hi, ?_⟩
  have hlim : ∀ᵐ x ∂ρ, Tendsto
      (fun n : ℕ => matrixFieldPair M (VectorRadial.truncateValues n u)
        (VectorRadial.truncateValues n u) x) atTop (𝓝 (0 : ℝ)) := by
    have he := ae_all_iff.mpr (fun n : ℕ => VectorRadial.truncateValues_ae n u)
    filter_upwards [he] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop
      (⌈‖(WithLp.toLp 2 (fun i => u i x) : EuclideanSpace ℝ ι)‖⌉₊)] with n hn
    have hnorm : ‖(WithLp.toLp 2 (fun i => u i x) : EuclideanSpace ℝ ι)‖ ≤ (n : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hn)
    have ht := VectorRadial.truncate_of_norm_le (n : ℝ≥0) hnorm
    have ht' (i : ι) : VectorRadial.truncateValues n u i x = 0 := by
      have hh := congrArg (fun v : EuclideanSpace ℝ ι => v i) ht
      exact (hx n i).trans hh
    simp only [matrixFieldPair, ht', zero_mul, Finset.sum_const_zero]
  have ht := tendsto_integral_of_dominated_convergence (matrixFieldPair M u u)
    (fun n => (hi n).aestronglyMeasurable) hu (fun n => ?_) hlim
  · simpa only [integral_zero] using ht
  filter_upwards [VectorRadial.matrixFieldPair_truncateValues_le n M hM u] with x hx
  rw [Real.norm_of_nonneg hx.1]
  exact hx.2

end Internal
end Riesz2.VectorCore
