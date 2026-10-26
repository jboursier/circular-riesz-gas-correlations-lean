/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.IsClosedScalarDirichletForm
public import Riesz2.Frozen.WeightedWeakSolution
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Riesz2.Frozen.IsConservativeScalarForm
public import Riesz2.Frozen.IsNeumannRealization
public import Riesz2.Frozen.SummableCoerciveMatrix
public import Riesz2.Frozen.InverseTemperature
public import Mathlib.Analysis.Convex.Basic
public import Riesz2.Frozen.AdmissibleParticlePairs
public import Riesz2.Frozen.PairGibbsMeasure
public import Riesz2.Frozen.PairAmbientGapPotential
public import Riesz2.Frozen.IntrinsicGapLaw
public import Riesz2.Frozen.IntrinsicGapDomain
public import Riesz2.Frozen.HessianMatrix
public import Riesz2.Frozen.IsEuclideanGibbsPotential
public import Riesz2.Frozen.ScalarPoissonSolution
public import Riesz2.Frozen.ZeroSumComponents
public import Riesz2.Frozen.GapMultiplierField
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Tactic

/-! # Concrete closed forms and nonvacuous weak equations -/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace Riesz2.DefinitionSanity

/-- The conservative zero generator on its full L² domain. -/
def zeroForm {α : Type*} [MeasurableSpace α] (ρ : Measure α) : ScalarFormData ρ :=
  ⟨⊤, 0⟩

theorem zeroForm_closed {α : Type*} [MeasurableSpace α] (ρ : Measure α) :
    IsClosedScalarDirichletForm (zeroForm ρ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f
    exact subset_closure ⟨⟨f, Submodule.mem_top⟩, rfl⟩
  · intro f g
    rfl
  · intro f
    exact le_rfl
  · intro f u _ _
    refine ⟨⟨u, Submodule.mem_top⟩, rfl, ?_⟩
    change Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)
    exact tendsto_const_nhds
  · intro φ hφ hφ0 f
    have hLp := hφ.comp_memLp hφ0 (Lp.memLp f.val)
    refine ⟨⟨hLp.toLp (φ ∘ f.val), Submodule.mem_top⟩, ?_, le_rfl⟩
    exact hLp.coeFn_toLp

theorem zeroForm_conservative {α : Type*} [MeasurableSpace α]
    (ρ : Measure α) [IsFiniteMeasure ρ] : IsConservativeScalarForm (zeroForm ρ) := by
  have hLp : MemLp (fun _ : α => (1 : ℝ)) 2 ρ := memLp_const 1
  exact ⟨⟨hLp.toLp _, Submodule.mem_top⟩, hLp.coeFn_toLp, rfl⟩

theorem lp_zero_dimension_eq
    (g h : Lp (EuclideanSpace ℝ (Fin 0)) 2 (Measure.dirac (0 : EuclideanSpace ℝ (Fin 0)))) :
    g = h := by
  apply Lp.ext
  exact Filter.Eventually.of_forall (fun _ => Subsingleton.elim _ _)

/-- The whole scalar graph on a zero-dimensional Euclidean probability space. -/
theorem neumann_zero_dimension_graph
    (f : Lp ℝ 2 (Measure.dirac (0 : EuclideanSpace ℝ (Fin 0))))
    (g : Lp (EuclideanSpace ℝ (Fin 0)) 2 (Measure.dirac (0 : EuclideanSpace ℝ (Fin 0)))) :
    (f, g) ∈ neumannSobolevGraph (Measure.dirac (0 : EuclideanSpace ℝ (Fin 0))) univ := by
  have hf : MemLp (fun _ : EuclideanSpace ℝ (Fin 0) => f 0) 2 (Measure.dirac (0 : EuclideanSpace ℝ (Fin 0))) :=
    memLp_const _
  have hg : MemLp (gradient (fun _ : EuclideanSpace ℝ (Fin 0) => f 0)) 2
      (Measure.dirac (0 : EuclideanSpace ℝ (Fin 0))) := by
    simp
  apply subset_closure
  refine ⟨fun _ => f 0, hf, hg, ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩, ?_⟩
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [hf.coeFn_toLp] with x hx
    exact (congrArg f (Subsingleton.elim x 0)).trans hx.symm
  · exact lp_zero_dimension_eq _ _

theorem zero_dimension_neumann :
    IsNeumannRealization (univ : Set (EuclideanSpace ℝ (Fin 0)))
      (zeroForm (Measure.dirac (0 : EuclideanSpace ℝ (Fin 0)))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro f
    exact ⟨fun _ => ⟨0, neumann_zero_dimension_graph f 0⟩, fun _ => Submodule.mem_top⟩
  · intro f g h _ _
    exact lp_zero_dimension_eq _ _
  · intro f h g k _ _
    have hg : g = 0 := lp_zero_dimension_eq _ _
    have hk : k = 0 := lp_zero_dimension_eq _ _
    subst g k
    rw [inner_zero_left]
    rfl

/-- Zero is a real weak solution for every form, matrix and fixed component subspace. -/
theorem weak_zero {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {ρ : Measure α} (Q : ScalarFormData ρ) (M : α → Matrix ι ι ℝ)
    (S : Submodule ℝ (ι → ℝ)) :
    WeightedWeakSolution Q M S (fun _ => 0) (fun _ => 0) := by
  classical
  have hzero : ∀ᵐ x ∂ρ, (0 : Lp ℝ 2 ρ) x = 0 := Lp.coeFn_zero ℝ 2 ρ
  have hdom : WeightedFormDomain Q M S (fun _ => 0) := by
    constructor
    · filter_upwards [hzero] with x hx
      change (fun _ : ι => (0 : Lp ℝ 2 ρ) x) ∈ S
      rw [hx]
      simpa only [Pi.zero_def] using S.zero_mem
    · apply (integrable_zero α ℝ ρ).congr
      filter_upwards [hzero] with x hx
      change (0 : ℝ) = ∑ i, ∑ j, (0 : Lp ℝ 2 ρ) x * M x i j * (0 : Lp ℝ 2 ρ) x
      simp only [hx, zero_mul, Finset.sum_const_zero]
  refine ⟨hdom, ?_⟩
  intro h _
  have hpair : matrixFieldPair M (fun i => ((0 : Q.1)).val) (fun i => (h i).val) =ᵐ[ρ] 0 := by
    filter_upwards [hzero] with x hx
    change (∑ i, ∑ j, (0 : Lp ℝ 2 ρ) x * M x i j * (h j).val x) = 0
    simp only [hx, zero_mul, Finset.sum_const_zero]
  refine ⟨(integrable_zero α ℝ ρ).congr hpair.symm, ?_⟩
  rw [integral_eq_zero_of_ae hpair]
  simp

/-- With a nonzero coercive identity matrix, the zero source has an actual finite-energy solution. -/
theorem identity_equation_exists (m : ℕ+) :
    ∃ u : Fin (m : ℕ) → (zeroForm (Measure.dirac (0 : EuclideanSpace ℝ (Fin 0)))).1,
      WeightedWeakSolution (zeroForm (Measure.dirac (0 : EuclideanSpace ℝ (Fin 0))))
        (fun _ => (1 : Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)) ⊤ (fun _ => 0) u := by
  exact ⟨fun _ => 0, weak_zero _ _ _⟩

/-- Zero-dimensional canonical volume gives a concrete normalized smooth scalar Gibbs law. -/
theorem zero_dimension_gibbs :
    IsEuclideanGibbsPotential volume (Measure.dirac (0 : EuclideanSpace ℝ (Fin 0)))
      univ (fun _ => 0) := by
  constructor
  · exact contDiffOn_const
  · simp [volume_euclideanSpace_eq_dirac]

/-- All scalar-form and matrix hypotheses of point-source decay have a concrete instance. -/
theorem point_source_data_nonempty :
    let ν := Measure.dirac (0 : EuclideanSpace ℝ (Fin 0))
    ∃ (s : ShortExponent) (g : ComponentGeometry (Fin 1)) (Q : ScalarFormData ν),
      IsProbabilityMeasure ν ∧ IsNeumannRealization univ Q ∧
      IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
      SummableCoerciveMatrix (ρ := ν) s 1 1 1 0 g
        (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
  let g : ComponentGeometry (Fin 1) := Sum.inl
    ⟨fun _ => 0, fun _ _ _ => Subsingleton.elim _ _⟩
  refine ⟨⟨2, by norm_num⟩, g, zeroForm _, inferInstance,
    zero_dimension_neumann, zeroForm_closed _, zeroForm_conservative _, ?_⟩
  constructor
  · intro i j
    exact measurable_const
  · apply Filter.Eventually.of_forall
    intro x
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      have hij : i = j := Subsingleton.elim _ _
      subst j
      rfl
    · intro z
      simp only [Fin.sum_univ_one]
      simp [pow_two]
    · intro i j
      have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      subst i j
      simp [g, componentDistance]

/-- Scalar Poisson has a real mean-zero solution at zero source. -/
theorem scalar_poisson_zero {α : Type*} [MeasurableSpace α] {ν : Measure α}
    (Q : ScalarFormData ν) : ScalarPoissonSolution Q 0 0 := by
  have hz : (fun x => ((0 : Q.1)).val x) =ᵐ[ν] 0 := by
    exact Lp.coeFn_zero ℝ 2 ν
  have hInt : Integrable (fun x => ((0 : Q.1)).val x) ν :=
    (integrable_zero α ℝ ν).congr hz.symm
  have hMean : (∫ x, ((0 : Q.1)).val x ∂ν) = 0 := integral_eq_zero_of_ae hz
  refine ⟨hInt, hInt, hMean, ?_⟩
  intro h
  have hzero : (fun x => (((0 : Q.1)).val x - ∫ y, ((0 : Q.1)).val y ∂ν) * h.val x) =ᵐ[ν] 0 := by
    filter_upwards [hz] with x hx
    rw [hMean, hx]
    simp
  exact ⟨(integrable_zero α ℝ ν).congr hzero.symm,
    by rw [integral_eq_zero_of_ae hzero]; simp⟩

theorem hessian_constant (n : ℕ) (c : ℝ) :
    hessianMatrix (fun _ : EuclideanSpace ℝ (Fin n) => c) = 0 := by
  funext x
  ext i j
  simp [hessianMatrix]

/-- The normal multiplier has an actual zero-field instance, without a global L² assumption. -/
theorem multiplier_zero {α : Type*} [MeasurableSpace α] {ν : Measure α}
    (N : ℕ+) (Q : ScalarFormData ν) :
    gapMultiplierField N Q (fun _ => 0) (fun _ => 0) (fun _ => 0) =ᵐ[ν] 0 := by
  filter_upwards [Lp.coeFn_zero ℝ 2 ν] with x hx
  simp only [gapMultiplierField, Matrix.zero_apply, zero_mul, Finset.sum_const_zero,
    hx, Pi.zero_apply, sub_zero, mul_zero]

/-- Every physical law admits the bounded zero L² source. -/
theorem zero_source_bounded {α : Type*} [MeasurableSpace α] (ν : Measure α) :
    eLpNorm (0 : Lp ℝ 2 ν) ∞ ν < ⊤ := by
  rw [eLpNorm_congr_ae (Lp.coeFn_zero ℝ 2 ν), eLpNorm_zero]
  exact ENNReal.zero_lt_top

end Riesz2.DefinitionSanity
end
end
