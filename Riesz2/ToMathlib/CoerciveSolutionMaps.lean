/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.MatrixEnergySpaces
public import Riesz2.Frozen.ScalarPoissonSolution
public import Riesz1.ToMathlib.Variational.NormalizedInverse
public import Riesz1.ToMathlib.Variational.ProbabilityPoisson

/-!
# Coercive solution maps on complete form domains

The Lax–Milgram argument supplies the scalar and constrained inverses used in
Subsection 3.5, Proposition 3.3 and the auxiliary vector equations.

The normalized inverse is the Riesz 1 construction, expressed as a continuous
linear map with explicit bounds. Restrictions use closed subspaces of the full
form domain. The matrix case uses the complete graph in `MatrixEnergySpaces`
and its identification with `WeightedFormDomain` and `WeightedWeakSolution`.
-/

@[expose] public section
noncomputable section

open MeasureTheory InnerProductSpace Filter
open scoped BigOperators

namespace Riesz2.CoerciveSolution

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

section Normalization

variable (m : V →L[ℝ] ℝ) (B : V →L[ℝ] V →L[ℝ] ℝ)
  (C : ℝ) (hC : 0 < C) (hP : ∀ u : V, m u = 0 → ‖u‖ ^ 2 ≤ C * B u u)

/-- Quantitative bound for the existing normalized variational inverse. -/
theorem normalized_norm_le (f : StrongDual ℝ V) :
    ‖Riesz1.Internal.normalizedVariationalInverse m B C hC hP f‖ ≤ C * ‖f‖ := by
  let u := Riesz1.Internal.normalizedVariationalInverse m B C hC hP f
  have hp := hP u.val u.property
  have he := Riesz1.Internal.normalizedVariationalInverse_solves m B C hC hP f u
  have hf := f.le_opNorm u.val
  have hb : B u.val u.val ≤ ‖f‖ * ‖u‖ := by
    rw [he]
    exact (le_abs_self _).trans hf
  change ‖u‖ ≤ C * ‖f‖
  by_cases hz : ‖u‖ = 0
  · rw [hz]
    exact mul_nonneg hC.le (norm_nonneg _)
  · have hn : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hp' : ‖u‖ ^ 2 ≤ C * (‖f‖ * ‖u‖) := hp.trans (mul_le_mul_of_nonneg_left hb hC.le)
    nlinarith

/-- Riesz 1's inverse as a continuous linear map into the complete normalization kernel.
This also applies to the zero functional, whose kernel is the whole form domain. -/
def normalized : StrongDual ℝ V →L[ℝ] m.ker :=
  (Riesz1.Internal.normalizedVariationalInverse m B C hC hP).mkContinuous C
    (normalized_norm_le m B C hC hP)

theorem normalized_solves (f : StrongDual ℝ V) (w : m.ker) :
    B (normalized m B C hC hP f).val w.val = f w.val :=
  Riesz1.Internal.normalizedVariationalInverse_solves m B C hC hP f w

theorem normalized_unique (f : StrongDual ℝ V) (u : m.ker)
    (hu : ∀ w : m.ker, B u.val w.val = f w.val) :
    u = normalized m B C hC hP f :=
  Riesz1.Internal.normalizedVariationalInverse_unique m B C hC hP f u hu

/-- The solution is the unique minimizer when the form is symmetric. -/
theorem normalized_minimizer_iff (hs : ∀ u w, B u w = B w u)
    (f : StrongDual ℝ V) (u : m.ker) :
    (∀ w : m.ker, B u.val u.val - 2 * f u.val ≤ B w.val w.val - 2 * f w.val) ↔
      u = normalized m B C hC hP f :=
  Riesz1.Internal.normalizedVariationalInverse_minimizer_iff m B C hC hP hs f u

end Normalization

section Coercive

variable (B : V →L[ℝ] V →L[ℝ] ℝ) (c : ℝ) (hc : 0 < c)
  (hB : ∀ u, c * ‖u‖ ^ 2 ≤ B u u)

omit [CompleteSpace V] in
include hc hB in
/-- Conversion of a coercivity bound to the norm bound used by the library inverse. -/
theorem poincare_of_coercive (u : V) : ‖u‖ ^ 2 ≤ c⁻¹ * B u u := by
  rw [← div_eq_inv_mul, le_div_iff₀ hc]
  simpa only [mul_comm] using hB u

/-- The coercive inverse on the whole Hilbert form domain, for arbitrary continuous
dual sources. Constructed by reusing the library inverse with zero normalization. -/
def inverse : StrongDual ℝ V →L[ℝ] V :=
  (0 : V →L[ℝ] ℝ).ker.subtypeL.comp
    (normalized 0 B c⁻¹ (inv_pos.mpr hc) (fun u _ => poincare_of_coercive B c hc hB u))

theorem inverse_solves (f : StrongDual ℝ V) (w : V) :
    B (inverse B c hc hB f) w = f w :=
  normalized_solves 0 B c⁻¹ (inv_pos.mpr hc)
    (fun u _ => poincare_of_coercive B c hc hB u) f ⟨w, by simp⟩

theorem inverse_unique (f : StrongDual ℝ V) (u : V)
    (hu : ∀ w, B u w = f w) : u = inverse B c hc hB f := by
  exact congrArg Subtype.val (normalized_unique 0 B c⁻¹ (inv_pos.mpr hc)
    (fun u _ => poincare_of_coercive B c hc hB u) f ⟨u, by simp⟩ (fun w => hu w.val))

include hc hB in
theorem inverse_existsUnique (f : StrongDual ℝ V) :
    ∃! u : V, ∀ w, B u w = f w :=
  ⟨inverse B c hc hB f, inverse_solves B c hc hB f, fun u => inverse_unique B c hc hB f u⟩

/-- Energy identity obtained by testing against the solution. -/
theorem inverse_energy (f : StrongDual ℝ V) :
    B (inverse B c hc hB f) (inverse B c hc hB f) = f (inverse B c hc hB f) :=
  inverse_solves B c hc hB f _

theorem inverse_norm_le (f : StrongDual ℝ V) :
    ‖inverse B c hc hB f‖ ≤ c⁻¹ * ‖f‖ :=
  normalized_norm_le 0 B c⁻¹ (inv_pos.mpr hc)
    (fun u _ => poincare_of_coercive B c hc hB u) f

/-- The embedding pulls an ambient Hilbert source back to a continuous form functional. -/
def forcing (J : V →L[ℝ] H) : H →L[ℝ] StrongDual ℝ V :=
  ((ContinuousLinearMap.compL ℝ V H ℝ).flip J).comp (innerSL ℝ)

omit [CompleteSpace V] in
theorem forcing_apply (J : V →L[ℝ] H) (f : H) (w : V) :
    forcing J f w = inner ℝ f (J w) := rfl

/-- Continuous solution map for Hilbert sources. -/
def solution (J : V →L[ℝ] H) : H →L[ℝ] V :=
  (inverse B c hc hB).comp (forcing J)

theorem solution_solves (J : V →L[ℝ] H) (f : H) (w : V) :
    B (solution B c hc hB J f) w = inner ℝ f (J w) :=
  inverse_solves B c hc hB (forcing J f) w

/-- The sharp L² bound uses coercivity in the ambient norm, not the graph-norm
coercivity constant. This is the energy estimate in Subsection 3.5. -/
theorem solution_value_norm_le (J : V →L[ℝ] H) (a : ℝ) (ha : 0 < a)
    (hlower : ∀ u, a * ‖J u‖ ^ 2 ≤ B u u) (f : H) :
    ‖J (solution B c hc hB J f)‖ ≤ a⁻¹ * ‖f‖ := by
  let u := solution B c hc hB J f
  have hl := hlower u
  have he := solution_solves B c hc hB J f u
  have hs := real_inner_le_norm f (J u)
  change ‖J u‖ ≤ a⁻¹ * ‖f‖
  rw [← div_eq_inv_mul, le_div_iff₀ ha]
  by_cases hz : ‖J u‖ = 0
  · simpa only [hz, zero_mul] using norm_nonneg f
  · have hn : 0 < ‖J u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

/-- Full energy, including both diffusion and matrix energy, is bounded by the source. -/
theorem solution_energy_le (J : V →L[ℝ] H) (a : ℝ) (ha : 0 < a)
    (hlower : ∀ u, a * ‖J u‖ ^ 2 ≤ B u u) (f : H) :
    B (solution B c hc hB J f) (solution B c hc hB J f) ≤ a⁻¹ * ‖f‖ ^ 2 := by
  rw [solution_solves]
  calc
    inner ℝ f (J (solution B c hc hB J f)) ≤ ‖f‖ * ‖J (solution B c hc hB J f)‖ :=
      real_inner_le_norm _ _
    _ ≤ ‖f‖ * (a⁻¹ * ‖f‖) := mul_le_mul_of_nonneg_left
      (solution_value_norm_le B c hc hB J a ha hlower f) (norm_nonneg _)
    _ = a⁻¹ * ‖f‖ ^ 2 := by ring

end Coercive

section Restriction

variable (B : V →L[ℝ] V →L[ℝ] ℝ) (S : Submodule ℝ V)
  (hS : IsClosed (S : Set V)) (c : ℝ) (hc : 0 < c)
  (hB : ∀ u : S, c * ‖u.val‖ ^ 2 ≤ B u.val u.val)

/-- Coercive solution on a closed subspace of the full form domain, without projecting
arbitrary elements onto that subspace. -/
def constrained : StrongDual ℝ S →L[ℝ] S := by
  haveI : CompleteSpace S := hS.completeSpace_coe
  exact inverse (B.bilinearComp S.subtypeL S.subtypeL) c hc hB

theorem constrained_solves (f : StrongDual ℝ S) (w : S) :
    B (constrained B S hS c hc hB f).val w.val = f w := by
  have : CompleteSpace S := hS.completeSpace_coe
  exact inverse_solves (B.bilinearComp S.subtypeL S.subtypeL) c hc hB f w

theorem constrained_unique (f : StrongDual ℝ S) (u : S)
    (hu : ∀ w : S, B u.val w.val = f w) :
    u = constrained B S hS c hc hB f := by
  have : CompleteSpace S := hS.completeSpace_coe
  exact inverse_unique (B.bilinearComp S.subtypeL S.subtypeL) c hc hB f u hu

theorem constrained_norm_le (f : StrongDual ℝ S) :
    ‖constrained B S hS c hc hB f‖ ≤ c⁻¹ * ‖f‖ := by
  have : CompleteSpace S := hS.completeSpace_coe
  exact inverse_norm_le (B.bilinearComp S.subtypeL S.subtypeL) c hc hB f

end Restriction
end Riesz2.CoerciveSolution

namespace Riesz2.MatrixEnergy

variable {α ι : Type*} [MeasurableSpace α] {ρ : Measure α}
  [Fintype ι] [DecidableEq ι]
  (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q)
  (M : α → Matrix ι ι ℝ) (S : Submodule ℝ (ι → ℝ))
  (hM : ∀ᵐ x ∂ρ, (M x).PosSemidef)
  (a : ℝ) (ha : 0 < a)
  (hlower : ∀ᵐ x ∂ρ, ∀ t ∈ S,
    a * (∑ i, t i ^ 2) ≤ ∑ i, ∑ j, t i * M x i j * t j)

local instance : NormedAddCommGroup (Natural Q hQ M S hM) := inferInstance
local instance : InnerProductSpace ℝ (Natural Q hQ M S hM) := inferInstance
local instance : CompleteSpace (Natural Q hQ M S hM) := inferInstance

/-- The continuous inverse for arbitrary dual sources on the whole natural matrix
domain, including fixed component constraints (Subsection 3.5). -/
def dualSolution : StrongDual ℝ (Natural Q hQ M S hM) →L[ℝ] Natural Q hQ M S hM :=
  CoerciveSolution.inverse (V := Natural Q hQ M S hM) (weakForm Q hQ M S hM) (a / (1 + a))
    (div_pos ha (add_pos zero_lt_one ha)) (weakForm_coercivity Q hQ M S hM a ha hlower)

theorem dualSolution_solves (f : StrongDual ℝ (Natural Q hQ M S hM))
    (w : Natural Q hQ M S hM) :
    weakForm Q hQ M S hM (dualSolution Q hQ M S hM a ha hlower f) w = f w :=
  CoerciveSolution.inverse_solves (V := Natural Q hQ M S hM) (weakForm Q hQ M S hM) (a / (1 + a))
    (div_pos ha (add_pos zero_lt_one ha)) (weakForm_coercivity Q hQ M S hM a ha hlower) f w

theorem dualSolution_unique (f : StrongDual ℝ (Natural Q hQ M S hM))
    (u : Natural Q hQ M S hM) (hu : ∀ w, weakForm Q hQ M S hM u w = f w) :
    u = dualSolution Q hQ M S hM a ha hlower f :=
  CoerciveSolution.inverse_unique (V := Natural Q hQ M S hM) (weakForm Q hQ M S hM) (a / (1 + a))
    (div_pos ha (add_pos zero_lt_one ha)) (weakForm_coercivity Q hQ M S hM a ha hlower) f u hu

/-- Continuous finite-vector L²-to-form-domain solution map. Component dimension and
base dimension are independent. `S = ⊤` gives the unrestricted equation. -/
def solution : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ) →L[ℝ] Natural Q hQ M S hM :=
  CoerciveSolution.solution (V := Natural Q hQ M S hM) (weakForm Q hQ M S hM) (a / (1 + a))
    (div_pos ha (add_pos zero_lt_one ha)) (weakForm_coercivity Q hQ M S hM a ha hlower)
    (values Q hQ M S hM)

theorem solution_solves (f : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ))
    (w : Natural Q hQ M S hM) :
    weakForm Q hQ M S hM (solution Q hQ M S hM a ha hlower f) w =
      inner ℝ f (values Q hQ M S hM w) :=
  CoerciveSolution.solution_solves (V := Natural Q hQ M S hM) (weakForm Q hQ M S hM) (a / (1 + a))
    (div_pos ha (add_pos zero_lt_one ha)) (weakForm_coercivity Q hQ M S hM a ha hlower)
    (values Q hQ M S hM) f w

include hlower in
/-- The pointwise matrix bound controls L² mass on the full form domain. -/
theorem weakForm_mass_bound (z : Natural Q hQ M S hM) :
    a * ‖values Q hQ M S hM z‖ ^ 2 ≤ weakForm Q hQ M S hM z z := by
  rw [weakForm_apply]
  exact (matrix_lower_bound Q hQ M S hM a hlower z).trans
    (le_add_of_nonneg_left (Finset.sum_nonneg (fun i _ => hQ.2.2.1 _)))

/-- Sharp value bound in Subsection 3.5, valid for every fixed component subspace. -/
theorem solution_value_norm_le (f : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ)) :
    ‖values Q hQ M S hM (solution Q hQ M S hM a ha hlower f)‖ ≤ a⁻¹ * ‖f‖ :=
  CoerciveSolution.solution_value_norm_le (V := Natural Q hQ M S hM) (weakForm Q hQ M S hM) (a / (1 + a))
    (div_pos ha (add_pos zero_lt_one ha)) (weakForm_coercivity Q hQ M S hM a ha hlower)
    (values Q hQ M S hM) a ha
    (weakForm_mass_bound Q hQ M S hM a hlower) f

/-- Bound for the sum of diffusion and matrix energies (Subsection 3.5). -/
theorem solution_energy_le (f : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ)) :
    weakForm Q hQ M S hM (solution Q hQ M S hM a ha hlower f)
      (solution Q hQ M S hM a ha hlower f) ≤ a⁻¹ * ‖f‖ ^ 2 :=
  CoerciveSolution.solution_energy_le (V := Natural Q hQ M S hM) (weakForm Q hQ M S hM) (a / (1 + a))
    (div_pos ha (add_pos zero_lt_one ha)) (weakForm_coercivity Q hQ M S hM a ha hlower)
    (values Q hQ M S hM) a ha
    (weakForm_mass_bound Q hQ M S hM a hlower) f

/-- Diffusion bound in squared form, without assuming a choice of gradient realization. -/
theorem solution_diffusion_le (f : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ)) :
    (∑ i, Q.2 (tuple Q hQ M S hM (solution Q hQ M S hM a ha hlower f) i)
      (tuple Q hQ M S hM (solution Q hQ M S hM a ha hlower f) i)) ≤ a⁻¹ * ‖f‖ ^ 2 := by
  have he := solution_energy_le Q hQ M S hM a ha hlower f
  rw [weakForm_apply, integral_pair_eq] at he
  exact (le_add_of_nonneg_right real_inner_self_nonneg).trans he

/-- The gradient estimate with 's square-root convention (Subsection 3.5). -/
theorem solution_gradient_le (f : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ)) :
    Real.sqrt (∑ i, Q.2 (tuple Q hQ M S hM (solution Q hQ M S hM a ha hlower f) i)
      (tuple Q hQ M S hM (solution Q hQ M S hM a ha hlower f) i)) ≤
        (Real.sqrt a)⁻¹ * ‖f‖ := by
  have he := Real.sqrt_le_sqrt (solution_diffusion_le Q hQ M S hM a ha hlower f)
  simpa only [Real.sqrt_mul (inv_nonneg.mpr ha.le), Real.sqrt_inv,
    Real.sqrt_sq (norm_nonneg _)] using he

/-- The L² source equation is exactly the predicate, with all its test and
cross-integrability requirements. -/
theorem solution_weightedWeakSolution (hMmeas : ∀ i j, Measurable (fun x => M x i j))
    (f : ι → Lp ℝ 2 ρ) :
    WeightedWeakSolution Q M S f
      (tuple Q hQ M S hM (solution Q hQ M S hM a ha hlower (WithLp.toLp 2 f))) := by
  apply (weightedWeakSolution_iff Q hQ M S hM hMmeas f _).mpr
  intro w
  exact solution_solves Q hQ M S hM a ha hlower (WithLp.toLp 2 f) w

/-- Uniqueness is literal equality of domain tuples, not equality only in a
core completion or for a smaller class of test functions. -/
theorem weightedWeakSolution_unique (hMmeas : ∀ i j, Measurable (fun x => M x i j))
    (f : ι → Lp ℝ 2 ρ) (u : ι → Q.1) (hu : WeightedWeakSolution Q M S f u) :
    u = tuple Q hQ M S hM (solution Q hQ M S hM a ha hlower (WithLp.toLp 2 f)) := by
  obtain ⟨z, rfl⟩ := exists_tuple Q hQ M S hM hMmeas u hu.1
  have hz := (weightedWeakSolution_iff Q hQ M S hM hMmeas f z).mp hu
  have he : z = solution Q hQ M S hM a ha hlower (WithLp.toLp 2 f) :=
    CoerciveSolution.inverse_unique (V := Natural Q hQ M S hM) (weakForm Q hQ M S hM) (a / (1 + a))
    (div_pos ha (add_pos zero_lt_one ha)) (weakForm_coercivity Q hQ M S hM a ha hlower)
      (CoerciveSolution.forcing (values Q hQ M S hM) (WithLp.toLp 2 f)) z hz
  exact congrArg (tuple Q hQ M S hM) he

include hQ hM ha hlower in
/-- Arbitrary L² sources have a unique full-domain weak solution. This internal
interface supplies the existence step of Subsection 3.5, without geometric or
conservativity assumptions that the variational argument does not need. -/
theorem weightedWeakSolution_existsUnique (hMmeas : ∀ i j, Measurable (fun x => M x i j))
    (f : ι → Lp ℝ 2 ρ) : ∃! u : ι → Q.1, WeightedWeakSolution Q M S f u :=
  ⟨_, solution_weightedWeakSolution Q hQ M S hM a ha hlower hMmeas f,
    fun u hu => weightedWeakSolution_unique Q hQ M S hM a ha hlower hMmeas f u hu⟩

/-- The inverse as an operator on the ambient L² space. Its range consists of values
of elements of the entire finite-energy form domain. -/
def l2Inverse : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ) →L[ℝ] PiLp 2 (fun _ : ι => Lp ℝ 2 ρ) :=
  (values Q hQ M S hM).comp (solution Q hQ M S hM a ha hlower)

theorem l2Inverse_norm_le (f : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ)) :
    ‖l2Inverse Q hQ M S hM a ha hlower f‖ ≤ a⁻¹ * ‖f‖ :=
  solution_value_norm_le Q hQ M S hM a ha hlower f

/-- Operator-norm version of the sharp ambient inverse bound. -/
theorem l2Inverse_opNorm_le : ‖l2Inverse Q hQ M S hM a ha hlower‖ ≤ a⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr ha.le)
    (l2Inverse_norm_le Q hQ M S hM a ha hlower)

/-- Symmetry survives restriction to a fixed component space. -/
theorem l2Inverse_symmetric (f g : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ)) :
    inner ℝ (l2Inverse Q hQ M S hM a ha hlower f) g =
      inner ℝ f (l2Inverse Q hQ M S hM a ha hlower g) := by
  rw [real_inner_comm]
  change inner ℝ g (values Q hQ M S hM _) = inner ℝ f (values Q hQ M S hM _)
  rw [← solution_solves Q hQ M S hM a ha hlower g,
    ← solution_solves Q hQ M S hM a ha hlower f]
  exact weakForm_symm Q hQ M S hM _ _

/-- Positivity of the ambient inverse. -/
theorem l2Inverse_nonneg (f : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ)) :
    0 ≤ inner ℝ f (l2Inverse Q hQ M S hM a ha hlower f) := by
  change 0 ≤ inner ℝ f (values Q hQ M S hM _)
  rw [← solution_solves Q hQ M S hM a ha hlower f]
  exact weakForm_nonneg Q hQ M S hM _

end Riesz2.MatrixEnergy

namespace Riesz2.ScalarFormHilbert

variable {α : Type*} [MeasurableSpace α] {ρ : Measure α}
  (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q)

/-- The scalar energy is continuous in its complete form norm. -/
def energyForm : Space Q hQ →L[ℝ] Space Q hQ →L[ℝ] ℝ :=
  (innerSL ℝ) - (innerSL ℝ).bilinearComp (value Q hQ) (value Q hQ)

theorem energyForm_apply (u w : Space Q hQ) :
    energyForm Q hQ u w = Q.2 (equiv Q hQ u) (equiv Q hQ w) := by
  change inner ℝ u w - inner ℝ (value Q hQ u) (value Q hQ w) = _
  rw [inner_eq]
  ring

/-- Positive scalar shift of the closed scalar form. -/
def shiftedForm (b : ℝ) : Space Q hQ →L[ℝ] Space Q hQ →L[ℝ] ℝ :=
  let mass : Lp ℝ 2 ρ →L[ℝ] Lp ℝ 2 ρ →L[ℝ] ℝ := innerSL ℝ
  energyForm Q hQ + b • mass.bilinearComp (value Q hQ) (value Q hQ)

theorem shiftedForm_apply (b : ℝ) (u w : Space Q hQ) :
    shiftedForm Q hQ b u w = Q.2 (equiv Q hQ u) (equiv Q hQ w) +
      b * inner ℝ (value Q hQ u) (value Q hQ w) := by
  change energyForm Q hQ u w + b * inner ℝ (value Q hQ u) (value Q hQ w) = _
  rw [energyForm_apply]

/-- Coercivity in the complete scalar graph norm. -/
theorem shiftedForm_coercivity (b : ℝ) (u : Space Q hQ) :
    min 1 b * ‖u‖ ^ 2 ≤ shiftedForm Q hQ b u u := by
  rw [shiftedForm_apply, norm_sq, real_inner_self_eq_norm_sq]
  have he := hQ.2.2.1 (equiv Q hQ u)
  have h₁ := mul_le_mul_of_nonneg_right (min_le_left 1 b) he
  have h₂ := mul_le_mul_of_nonneg_right (min_le_right 1 b) (sq_nonneg ‖value Q hQ u‖)
  change min 1 b * (‖value Q hQ u‖ ^ 2 + Q.2 _ _) ≤ _
  nlinarith only [h₁, h₂]

/-- Scalar L²-to-full-form-domain resolvent for every strictly positive shift. -/
def shiftedSolution (b : ℝ) (hb : 0 < b) : Lp ℝ 2 ρ →L[ℝ] Space Q hQ :=
  CoerciveSolution.solution (shiftedForm Q hQ b) (min 1 b) (lt_min zero_lt_one hb)
    (shiftedForm_coercivity Q hQ b) (value Q hQ)

theorem shiftedSolution_solves (b : ℝ) (hb : 0 < b) (f : Lp ℝ 2 ρ) (w : Space Q hQ) :
    Q.2 (equiv Q hQ (shiftedSolution Q hQ b hb f)) (equiv Q hQ w) +
      b * inner ℝ (value Q hQ (shiftedSolution Q hQ b hb f)) (value Q hQ w) =
        inner ℝ f (value Q hQ w) := by
  rw [← shiftedForm_apply]
  exact CoerciveSolution.solution_solves _ _ _ _ _ f w

theorem shiftedSolution_unique (b : ℝ) (hb : 0 < b) (f : Lp ℝ 2 ρ)
    (u : Space Q hQ)
    (hu : ∀ w, Q.2 (equiv Q hQ u) (equiv Q hQ w) +
      b * inner ℝ (value Q hQ u) (value Q hQ w) = inner ℝ f (value Q hQ w)) :
    u = shiftedSolution Q hQ b hb f := by
  apply CoerciveSolution.inverse_unique (shiftedForm Q hQ b) (min 1 b)
    (lt_min zero_lt_one hb) (shiftedForm_coercivity Q hQ b)
  intro w
  change shiftedForm Q hQ b u w = inner ℝ f (value Q hQ w)
  rw [shiftedForm_apply]
  exact hu w

theorem shiftedSolution_value_norm_le (b : ℝ) (hb : 0 < b) (f : Lp ℝ 2 ρ) :
    ‖value Q hQ (shiftedSolution Q hQ b hb f)‖ ≤ b⁻¹ * ‖f‖ := by
  apply CoerciveSolution.solution_value_norm_le (shiftedForm Q hQ b) (min 1 b)
    (lt_min zero_lt_one hb) (shiftedForm_coercivity Q hQ b) (value Q hQ) b hb
  intro u
  rw [shiftedForm_apply, real_inner_self_eq_norm_sq]
  exact le_add_of_nonneg_left (hQ.2.2.1 _)

section MeanZero

variable [IsProbabilityMeasure ρ]

/-- The mean on the scalar form domain is the existing Riesz 1 L² mean. -/
def mean : Space Q hQ →L[ℝ] ℝ := (Riesz1.poissonMean ρ).comp (value Q hQ)

theorem mean_eq_integral (u : Space Q hQ) :
    mean Q hQ u = ∫ x, (value Q hQ u) x ∂ρ :=
  Riesz1.poissonMean_eq_integral ρ _

variable (C : ℝ) (hC : 0 ≤ C)
  (hP : ∀ u : Space Q hQ, mean Q hQ u = 0 →
    ‖value Q hQ u‖ ^ 2 ≤ C * Q.2 (equiv Q hQ u) (equiv Q hQ u))

include hP in
/-- Poincaré controls the complete graph norm on the mean-zero kernel. -/
theorem meanZero_bound (u : Space Q hQ) (hu : mean Q hQ u = 0) :
    ‖u‖ ^ 2 ≤ (C + 1) * energyForm Q hQ u u := by
  have hp := hP u hu
  rw [value_apply] at hp
  rw [norm_sq, energyForm_apply]
  nlinarith only [hp]

/-- Continuous scalar Poisson inverse for arbitrary dual sources, restricted to the
closed mean-zero subspace. Poincaré is an internal analytic input supplied by consumers. -/
def meanZeroDualSolution : StrongDual ℝ (Space Q hQ) →L[ℝ] (mean Q hQ).ker :=
  CoerciveSolution.normalized (mean Q hQ) (energyForm Q hQ) (C + 1)
    (by positivity) (meanZero_bound Q hQ C hP)

/-- Centering and the L² forcing use exactly the Riesz 1 probability-space objects. -/
def meanZeroSolution : Lp ℝ 2 ρ →L[ℝ] (mean Q hQ).ker :=
  (meanZeroDualSolution Q hQ C hC hP).comp (CoerciveSolution.forcing (value Q hQ))

theorem meanZeroSolution_solves (f : Lp ℝ 2 ρ) (w : (mean Q hQ).ker) :
    Q.2 (equiv Q hQ (meanZeroSolution Q hQ C hC hP f).val) (equiv Q hQ w.val) =
      inner ℝ f (value Q hQ w.val) := by
  rw [← energyForm_apply]
  exact CoerciveSolution.normalized_solves _ _ _ _ _ _ w

theorem meanZeroSolution_unique (f : Lp ℝ 2 ρ) (u : (mean Q hQ).ker)
    (hu : ∀ w : (mean Q hQ).ker,
      Q.2 (equiv Q hQ u.val) (equiv Q hQ w.val) = inner ℝ f (value Q hQ w.val)) :
    u = meanZeroSolution Q hQ C hC hP f := by
  apply CoerciveSolution.normalized_unique
  intro w
  change energyForm Q hQ u.val w.val = inner ℝ f (value Q hQ w.val)
  rw [energyForm_apply]
  exact hu w

/-- The scalar Poisson equation has the exact energy identity on its whole mean-zero
form domain. -/
theorem meanZeroSolution_energy (f : Lp ℝ 2 ρ) :
    Q.2 (equiv Q hQ (meanZeroSolution Q hQ C hC hP f).val)
      (equiv Q hQ (meanZeroSolution Q hQ C hC hP f).val) =
        inner ℝ f (value Q hQ (meanZeroSolution Q hQ C hC hP f).val) :=
  meanZeroSolution_solves Q hQ C hC hP f _

/-- Sharp scalar value estimate, including the degenerate Poincaré constant `C = 0`. -/
theorem meanZeroSolution_value_norm_le (f : Lp ℝ 2 ρ) :
    ‖value Q hQ (meanZeroSolution Q hQ C hC hP f).val‖ ≤ C * ‖f‖ := by
  let u := meanZeroSolution Q hQ C hC hP f
  have hp := hP u.val u.property
  have he := meanZeroSolution_energy Q hQ C hC hP f
  have hb : Q.2 (equiv Q hQ u.val) (equiv Q hQ u.val) ≤ ‖f‖ * ‖value Q hQ u.val‖ :=
    he.trans_le (real_inner_le_norm _ _)
  have h := hp.trans (mul_le_mul_of_nonneg_left hb hC)
  change ‖value Q hQ u.val‖ ≤ C * ‖f‖
  by_cases hz : ‖value Q hQ u.val‖ = 0
  · rw [hz]
    exact mul_nonneg hC (norm_nonneg _)
  · have hn : 0 < ‖value Q hQ u.val‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith only [h, hn]

/-- Scalar Dirichlet-energy estimate under the supplied Poincaré inequality. -/
theorem meanZeroSolution_energy_le (f : Lp ℝ 2 ρ) :
    Q.2 (equiv Q hQ (meanZeroSolution Q hQ C hC hP f).val)
      (equiv Q hQ (meanZeroSolution Q hQ C hC hP f).val) ≤ C * ‖f‖ ^ 2 := by
  rw [meanZeroSolution_energy]
  calc
    inner ℝ f (value Q hQ (meanZeroSolution Q hQ C hC hP f).val) ≤
        ‖f‖ * ‖value Q hQ (meanZeroSolution Q hQ C hC hP f).val‖ := real_inner_le_norm _ _
    _ ≤ ‖f‖ * (C * ‖f‖) := mul_le_mul_of_nonneg_left
      (meanZeroSolution_value_norm_le Q hQ C hC hP f) (norm_nonneg _)
    _ = C * ‖f‖ ^ 2 := by ring

include hQ in
omit [IsProbabilityMeasure ρ] in
/-- A null direction of a nonnegative symmetric scalar form pairs to zero with every
form-domain test, including when the form is degenerate. -/
theorem energy_null_pair (e u : Q.1) (he : Q.2 e e = 0) : Q.2 e u = 0 := by
  have hp : ∀ t : ℝ, 0 ≤ Q.2 u u * (t * t) + (2 * Q.2 e u) * t + 0 := by
    intro t
    have ht := hQ.2.2.1 (e + t • u)
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      he, hQ.2.1 u e] at ht
    nlinarith only [ht]
  have hd := discrim_le_zero hp
  dsimp only [discrim] at hd
  nlinarith only [hd, sq_nonneg (Q.2 e u)]

/-- Constants extend the mean-zero weak equation to every test in the full scalar
form domain. The right side is the existing centered L² source. -/
theorem meanZeroSolution_full_equation (e : Q.1) (he : ∀ᵐ x ∂ρ, e.val x = 1)
    (heQ : Q.2 e e = 0) (f : Lp ℝ 2 ρ) (w : Space Q hQ) :
    Q.2 (equiv Q hQ (meanZeroSolution Q hQ C hC hP f).val) (equiv Q hQ w) =
      inner ℝ (Riesz1.poissonCenter ρ f) (value Q hQ w) := by
  let e' : Space Q hQ := (equiv Q hQ).symm e
  have hev : value Q hQ e' = Lp.const 2 ρ (1 : ℝ) := by
    apply Lp.ext
    filter_upwards [he, Lp.coeFn_const 2 ρ (1 : ℝ)] with x hx hy
    exact hx.trans hy.symm
  have hem : mean Q hQ e' = 1 := by
    change Riesz1.poissonMean ρ (value Q hQ e') = 1
    rw [hev, Riesz1.poissonMean_one]
  let w₀ : (mean Q hQ).ker := ⟨w - mean Q hQ w • e', by simp [hem]⟩
  have ht := meanZeroSolution_solves Q hQ C hC hP f w₀
  have hnull := energy_null_pair Q hQ e (equiv Q hQ (meanZeroSolution Q hQ C hC hP f).val) heQ
  have hm : inner ℝ (Lp.const 2 ρ (1 : ℝ)) (value Q hQ w) = mean Q hQ w := rfl
  have hf : inner ℝ f (Lp.const 2 ρ (1 : ℝ)) = Riesz1.poissonMean ρ f := real_inner_comm _ _
  simpa only [w₀, map_sub, map_smul, LinearEquiv.apply_symm_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    inner_sub_right, inner_smul_right, hev, show equiv Q hQ e' = e from rfl,
    hQ.2.1 _ e, hnull, mul_zero, zero_mul,
    sub_zero, Riesz1.poissonCenter, inner_sub_left, real_inner_smul_left, hm, hf,
    mul_comm] using ht

/-- Bridge to the scalar Poisson predicate, retaining integrability of the
source, the solution and every centered-source cross term (Subsection 3.1). -/
theorem meanZeroSolution_scalarPoissonSolution (e : Q.1)
    (he : ∀ᵐ x ∂ρ, e.val x = 1) (heQ : Q.2 e e = 0) (G : Q.1) :
    ScalarPoissonSolution Q G
      (equiv Q hQ (meanZeroSolution Q hQ C hC hP G.val).val) := by
  let u := meanZeroSolution Q hQ C hC hP G.val
  refine ⟨(Lp.memLp G.val).integrable one_le_two,
    (Lp.memLp (value Q hQ u.val)).integrable one_le_two, ?_, fun w => ?_⟩
  · exact (mean_eq_integral Q hQ u.val).symm.trans u.property
  · have hprod := (Lp.memLp (Riesz1.poissonCenter ρ G.val)).integrable_mul (Lp.memLp w.val)
    have hae : (fun x => Riesz1.poissonCenter ρ G.val x * w.val x) =ᵐ[ρ]
        fun x => (G.val x - ∫ y, G.val y ∂ρ) * w.val x :=
      (Riesz1.poissonCenter_ae ρ G.val).mono (fun x hx => congrArg (· * w.val x) hx)
    refine ⟨hprod.congr hae, ?_⟩
    exact (meanZeroSolution_full_equation Q hQ C hC hP e he heQ G.val
      ((equiv Q hQ).symm w)).trans
        ((Riesz1.poisson_inner_eq_integral _ _ _).trans (integral_congr_ae hae))

/-- Centering does not change the forcing on the mean-zero scalar domain. -/
theorem inner_center_meanZero (f : Lp ℝ 2 ρ) (w : (mean Q hQ).ker) :
    inner ℝ (Riesz1.poissonCenter ρ f) (value Q hQ w.val) =
      inner ℝ f (value Q hQ w.val) := by
  rw [Riesz1.poissonCenter, inner_sub_left, real_inner_smul_left]
  change inner ℝ f (value Q hQ w.val) - Riesz1.poissonMean ρ f * mean Q hQ w.val = _
  have hw : mean Q hQ w.val = 0 := w.property
  rw [hw, mul_zero, sub_zero]

/-- Uniqueness in the literal scalar Poisson predicate. -/
theorem scalarPoissonSolution_unique (G ψ : Q.1) (hψ : ScalarPoissonSolution Q G ψ) :
    ψ = equiv Q hQ (meanZeroSolution Q hQ C hC hP G.val).val := by
  let v : Space Q hQ := (equiv Q hQ).symm ψ
  have hv : mean Q hQ v = 0 := (mean_eq_integral Q hQ v).trans hψ.2.2.1
  have hu := meanZeroSolution_unique Q hQ C hC hP G.val ⟨v, hv⟩ (fun w => ?_)
  · exact congrArg (fun z : (mean Q hQ).ker => equiv Q hQ z.val) hu
  · have hae : (fun x => Riesz1.poissonCenter ρ G.val x * (value Q hQ w.val) x) =ᵐ[ρ]
        fun x => (G.val x - ∫ y, G.val y ∂ρ) * (value Q hQ w.val) x :=
      (Riesz1.poissonCenter_ae ρ G.val).mono
        (fun x hx => congrArg (· * (value Q hQ w.val) x) hx)
    exact (hψ.2.2.2 (equiv Q hQ w.val)).2.trans
      ((integral_congr_ae hae).symm.trans
        ((Riesz1.poisson_inner_eq_integral ρ _ _).symm.trans (inner_center_meanZero Q hQ G.val w)))

include hC hP in
/-- Internal scalar existence-and-uniqueness interface, using only a constant null
direction, closedness and the supplied Poincaré inequality. -/
theorem scalarPoissonSolution_existsUnique (e : Q.1)
    (he : ∀ᵐ x ∂ρ, e.val x = 1) (heQ : Q.2 e e = 0) (G : Q.1) :
    ∃! ψ : Q.1, ScalarPoissonSolution Q G ψ := by
  refine ⟨_, meanZeroSolution_scalarPoissonSolution Q hQ C hC hP e he heQ G, ?_⟩
  exact fun ψ hψ => scalarPoissonSolution_unique Q hQ C hC hP G ψ hψ

end MeanZero
end Riesz2.ScalarFormHilbert
