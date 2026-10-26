/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.GapMultiplierField
public import Riesz2.Frozen.ZeroSumComponents
public import Riesz2.Frozen.WeightedWeakSolution
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Tactic

/-!
# Normal multipliers for a finite zero-sum constraint

Local integrability and the finite-dimensional normal projection identity for
Proposition 3.3. These facts use the multiplier.
No global square integrability of the multiplier is required.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped BigOperators

namespace Riesz2.ConstrainedNormalMultiplier

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}

section Local

variable [TopologicalSpace α] [BorelSpace α] [IsFiniteMeasure ν] {U : Set α}

/-- A continuous local coefficient times a compact interior test and an L²
function is integrable, as needed for the distribution scope in Proposition 3.3. The coefficient need not be bounded near the boundary. -/
theorem integrable_local_coefficient (hU : IsOpen U) {a φ : α → ℝ}
    (ha : ContinuousOn a U) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (f : Lp ℝ 2 ν) :
    Integrable (fun x => a x * f x * φ x) ν := by
  have hp : Continuous (fun x => a x * φ x) :=
    (ha.mul hφ.continuousOn).continuous_of_tsupport_subset hU
      (tsupport_mul_subset_right.trans hφU)
  have hpc : HasCompactSupport (fun x => a x * φ x) := hc.mul_left
  have hi := (hp.memLp_of_hasCompactSupport hpc (p := 2)).integrable_mul (Lp.memLp f)
  convert hi using 1
  ext x
  dsimp only [Pi.mul_apply]
  ring

/-- Local distribution integrability of the literal normal multiplier,
Proposition 3.3. Every compact test inside the continuity
region is allowed, without any global multiplier bound. -/
theorem multiplier_test_integrable (N : ℕ+) (Q : ScalarFormData ν)
    (M : α → Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (hU : IsOpen U) (hM : ∀ i j, ContinuousOn (fun x => M x i j) U)
    (v : Fin (N : ℕ) → Lp ℝ 2 ν) (u : Fin (N : ℕ) → Q.1)
    (φ : α → ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) :
    Integrable (fun x => gapMultiplierField N Q M v u x * φ x) ν := by
  have hm (i j : Fin (N : ℕ)) :=
    integrable_local_coefficient hU (hM i j) hφ hc hφU (u j).val
  have hv (i : Fin (N : ℕ)) : Integrable (fun x => v i x * φ x) ν :=
    (Lp.memLp (v i)).integrable_mul (hφ.memLp_of_hasCompactSupport hc (p := 2))
  have hi := ((integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hm i j))).sub
      (integrable_finsetSum Finset.univ (fun i _ => hv i))).const_mul (N : ℝ)⁻¹
  convert hi using 1
  ext x
  simp only [gapMultiplierField, Pi.sub_apply, ← Finset.sum_mul]
  ring

end Local

/-- The matrix/source residual splits into tangent and normal pairings,
Proposition 3.3. Symmetry is essential because the matrix pairing has the first vector on the left. -/
theorem normal_projection_identity (N : ℕ+)
    (M : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (hM : ∀ i j, M i j = M j i) (u v h : Fin (N : ℕ) → ℝ) :
    (∑ i, ∑ j, u i * M i j * h j) - (∑ i, v i * h i) =
      ((∑ i, ∑ j, u i * M i j * (h j - (N : ℝ)⁻¹ * ∑ k, h k)) -
        (∑ i, v i * (h i - (N : ℝ)⁻¹ * ∑ k, h k))) +
      ((N : ℝ)⁻¹ * ((∑ i, ∑ j, M i j * u j) - ∑ i, v i)) * ∑ i, h i := by
  have hs : (∑ i, ∑ j, u i * M i j) = ∑ i, ∑ j, M i j * u j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hM j i, mul_comm]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, ← mul_assoc]
  rw [hs]
  ring

/-- Canonical orthogonal projection of a finite tuple in an existing scalar
form domain onto the zero-sum component constraint, Proposition 3.3. No energy-domain projection is asserted here. -/
def projectTuple (N : ℕ+) (Q : ScalarFormData ν) (k : Fin (N : ℕ) → Q.1) :
    Fin (N : ℕ) → Q.1 := fun i => k i - (N : ℝ)⁻¹ • ∑ j, k j

/-- Pointwise formula for projection on an existing scalar form carrier,
Proposition 3.3. -/
theorem projectTuple_ae (N : ℕ+) (Q : ScalarFormData ν) (k : Fin (N : ℕ) → Q.1) :
    ∀ᵐ x ∂ν, ∀ i, (projectTuple N Q k i).val x =
      (k i).val x - (N : ℝ)⁻¹ * ∑ j, (k j).val x := by
  have he (i) : (projectTuple N Q k i).val =ᵐ[ν]
      fun x => (k i).val x - (N : ℝ)⁻¹ * ∑ j, (k j).val x := by
    have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun j => (k j).val)
    have hm := Lp.coeFn_smul (N : ℝ)⁻¹ (∑ j, (k j).val)
    have hd := Lp.coeFn_sub (k i).val ((N : ℝ)⁻¹ • ∑ j, (k j).val)
    filter_upwards [hs, hm, hd] with x hx hy hz
    simp only [projectTuple, Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_sum]
    rw [hz, Pi.sub_apply, hy, Pi.smul_apply, smul_eq_mul, hx]
  exact ae_all_iff.mpr he

/-- Orthogonal projection has zero component sum, Proposition 3.3, including the one-component case. -/
theorem projectTuple_zeroSum (N : ℕ+) (Q : ScalarFormData ν) (k : Fin (N : ℕ) → Q.1) :
    ∀ᵐ x ∂ν, (fun i => (projectTuple N Q k i).val x) ∈ zeroSumComponents (Fin (N : ℕ)) := by
  filter_upwards [projectTuple_ae N Q k] with x hx
  change (∑ i, (projectTuple N Q k i).val x) = 0
  simp only [hx, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : (N : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- Almost-everywhere tangency implies zero sum in the actual scalar form
carrier, Proposition 3.3. Thus normal diffusion terms vanish
as form pairings, without assuming pointwise derivatives. -/
theorem tuple_sum_zero (N : ℕ+) (Q : ScalarFormData ν) (u : Fin (N : ℕ) → Q.1)
    (hu : ∀ᵐ x ∂ν, (fun i => (u i).val x) ∈ zeroSumComponents (Fin (N : ℕ))) :
    ∑ i, u i = 0 := by
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_zero]
  apply Lp.ext
  filter_upwards [hu, Lp.coeFn_fun_finsetSum Finset.univ (fun i => (u i).val),
    Lp.coeFn_zero ℝ 2 ν] with x hx hs hz
  exact hs.trans ((show ∑ i, (u i).val x = 0 from hx).trans hz.symm)

/-- The diffusion pairing ignores the normal part of the test against a
tangent field, Proposition 3.3. This statement concerns
only scalar form membership. Finite matrix energy is handled separately. -/
theorem diffusion_projectTuple (N : ℕ+) (Q : ScalarFormData ν)
    (u k : Fin (N : ℕ) → Q.1)
    (hu : ∀ᵐ x ∂ν, (fun i => (u i).val x) ∈ zeroSumComponents (Fin (N : ℕ))) :
    (∑ i, Q.2 (u i) (projectTuple N Q k i)) = ∑ i, Q.2 (u i) (k i) := by
  have hs' : (∑ i, Q.2 (u i) (∑ j, k j)) = 0 := by
    rw [← LinearMap.sum_apply, ← map_sum, tuple_sum_zero N Q u hu]
    simp only [map_zero, LinearMap.zero_apply]
  simp only [projectTuple, map_sub, map_smul, smul_eq_mul,
    Finset.sum_sub_distrib, ← Finset.mul_sum, hs', mul_zero, sub_zero]

section CompactTests

variable [TopologicalSpace α] [BorelSpace α] [IsFiniteMeasure ν] {U : Set α}

/-- A local continuous matrix pairs integrably with every L² field and compact
continuous test field, Proposition 3.3. Matrix coefficients
are allowed to diverge at the boundary. -/
theorem matrix_compact_test_integrable (N : ℕ+) (Q : ScalarFormData ν)
    (M : α → Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (hU : IsOpen U) (hM : ∀ i j, ContinuousOn (fun x => M x i j) U)
    (u : Fin (N : ℕ) → Lp ℝ 2 ν) (k : Fin (N : ℕ) → Q.1)
    (h : Fin (N : ℕ) → α → ℝ)
    (hh : ∀ i, Continuous (h i) ∧ HasCompactSupport (h i) ∧ tsupport (h i) ⊆ U)
    (hk : ∀ᵐ x ∂ν, ∀ i, (k i).val x = h i x) :
    Integrable (matrixFieldPair M u (fun i => (k i).val)) ν := by
  have hi (i j : Fin (N : ℕ)) : Integrable (fun x => u i x * M x i j * h j x) ν := by
    have hhj := integrable_local_coefficient hU (hM i j)
      (hh j).1 (hh j).2.1 (hh j).2.2 (u i)
    simpa only [mul_comm] using hhj
  apply (integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hi i j))).congr
  filter_upwards [hk] with x hx
  simp only [matrixFieldPair, hx]

omit [MeasurableSpace α] [BorelSpace α] in
/-- Subtracting the component mean preserves compact continuous test fields,
Proposition 3.3. In particular this projection is justified
on compact tests even when it is unavailable on general matrix-energy fields. -/
theorem projected_compact_tests (N : ℕ+) (h : Fin (N : ℕ) → α → ℝ)
    (hh : ∀ i, Continuous (h i) ∧ HasCompactSupport (h i) ∧ tsupport (h i) ⊆ U) :
    ∀ i, let p := fun x => h i x - (N : ℝ)⁻¹ * ∑ j, h j x
      Continuous p ∧ HasCompactSupport p ∧ tsupport p ⊆ U := by
  classical
  let K := ⋃ i, tsupport (h i)
  have hK : IsCompact K := isCompact_iUnion (fun i => (hh i).2.1)
  have hKclosed : IsClosed K := isClosed_iUnion_of_finite (fun i => isClosed_tsupport (h i))
  have hKU : K ⊆ U := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact (hh i).2.2 hi
  have hs (i : Fin (N : ℕ)) : tsupport (fun x => h i x - (N : ℝ)⁻¹ * ∑ j, h j x) ⊆ K := by
    apply closure_minimal _ hKclosed
    intro x hx
    by_contra hnot
    have hz (j : Fin (N : ℕ)) : h j x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hj => hnot (mem_iUnion.mpr ⟨j, hj⟩))
    exact hx (by simp [hz])
  intro i
  refine ⟨(hh i).1.sub (continuous_const.mul (continuous_finsetSum _ (fun j _ => (hh j).1))),
    hK.of_isClosed_subset (isClosed_tsupport _) (hs i), (hs i).trans hKU⟩

/-- The zero-sum projection of compact tests lies in the entire literal matrix-energy domain, Proposition 3.3. Its energy is proved
integrable from local coefficient regularity, not assumed by projection. -/
theorem projected_compact_domain (N : ℕ+) (Q : ScalarFormData ν)
    (M : α → Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (hU : IsOpen U) (hM : ∀ i j, ContinuousOn (fun x => M x i j) U)
    (k : Fin (N : ℕ) → Q.1) (h : Fin (N : ℕ) → α → ℝ)
    (hh : ∀ i, Continuous (h i) ∧ HasCompactSupport (h i) ∧ tsupport (h i) ⊆ U)
    (hk : ∀ᵐ x ∂ν, ∀ i, (k i).val x = h i x) :
    WeightedFormDomain Q M (zeroSumComponents _) (projectTuple N Q k) := by
  refine ⟨projectTuple_zeroSum N Q k, ?_⟩
  apply matrix_compact_test_integrable N Q M hU hM
    (fun i => (projectTuple N Q k i).val) (projectTuple N Q k)
    (fun i x => h i x - (N : ℝ)⁻¹ * ∑ j, h j x) (projected_compact_tests N h hh)
  filter_upwards [projectTuple_ae N Q k, hk] with x hx hy
  simp only [hx, hy, implies_true]

omit [TopologicalSpace α] [BorelSpace α] [IsFiniteMeasure ν] in
/-- L² source pairings are exactly the corresponding finite integral,
Proposition 3.3. -/
theorem source_pair_integral (N : ℕ+) (v k : Fin (N : ℕ) → Lp ℝ 2 ν) :
    Integrable (fun x => ∑ i, v i x * k i x) ν ∧
      (∑ i, inner ℝ (v i) (k i)) = ∫ x, ∑ i, v i x * k i x ∂ν := by
  have hi (i : Fin (N : ℕ)) : Integrable (fun x => v i x * k i x) ν :=
    (Lp.memLp (v i)).integrable_mul (Lp.memLp (k i))
  refine ⟨integrable_finsetSum _ (fun i _ => hi i), ?_⟩
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [L2.inner_def]
  simp only [Real.inner_apply]

/-- Internal extension of the tangent weak equation to every compact ambient
test, Proposition 3.3. The resulting multiplier is the
literal local distribution. All matrix and multiplier integrals are
proved integrable. No global multiplier bound or projected-domain assumption
is imposed. The tangent weak solution itself is an input to this bridge. -/
theorem ambient_equation_of_tangent_solution (N : ℕ+) (Q : ScalarFormData ν)
    (M : α → Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (hU : IsOpen U) (hM : ∀ i j, ContinuousOn (fun x => M x i j) U)
    (hSymm : ∀ᵐ x ∂ν, ∀ i j, M x i j = M x j i)
    (v : Fin (N : ℕ) → Lp ℝ 2 ν) (u : Fin (N : ℕ) → Q.1)
    (hu : WeightedWeakSolution Q M (zeroSumComponents _) v u)
    (k : Fin (N : ℕ) → Q.1) (h : Fin (N : ℕ) → α → ℝ)
    (hh : ∀ i, Continuous (h i) ∧ HasCompactSupport (h i) ∧ tsupport (h i) ⊆ U)
    (hk : ∀ᵐ x ∂ν, ∀ i, (k i).val x = h i x) :
    Integrable (matrixFieldPair M (fun i => (u i).val) (fun i => (k i).val)) ν ∧
    Integrable (fun x => gapMultiplierField N Q M v u x * ∑ i, h i x) ν ∧
    (∑ i, Q.2 (u i) (k i)) +
      (∫ x, matrixFieldPair M (fun i => (u i).val) (fun i => (k i).val) x ∂ν) =
        (∑ i, inner ℝ (v i) (k i).val) +
          ∫ x, gapMultiplierField N Q M v u x * (∑ i, h i x) ∂ν := by
  let p := projectTuple N Q k
  have hp := projected_compact_domain N Q M hU hM k h hh hk
  obtain ⟨hpi, heq⟩ := hu.2 p hp
  have hki := matrix_compact_test_integrable N Q M hU hM
    (fun i => (u i).val) k h hh hk
  have hvk := source_pair_integral N v (fun i => (k i).val)
  have hvp := source_pair_integral N v (fun i => (p i).val)
  let A := matrixFieldPair M (fun i => (u i).val) (fun i => (k i).val)
  let Ap := matrixFieldPair M (fun i => (u i).val) (fun i => (p i).val)
  let F := fun x => ∑ i, v i x * (k i).val x
  let Fp := fun x => ∑ i, v i x * (p i).val x
  let L := fun x => gapMultiplierField N Q M v u x * ∑ i, h i x
  have hn : (fun x => A x - F x) =ᵐ[ν] fun x => (Ap x - Fp x) + L x := by
    filter_upwards [hSymm, projectTuple_ae N Q k, hk] with x hx hy hz
    have hi := normal_projection_identity N (M x) (hx) (fun i => (u i).val x)
      (fun i => v i x) (fun i => (k i).val x)
    simpa only [A, Ap, F, Fp, L, matrixFieldPair, gapMultiplierField, p, hy, hz] using hi
  have hLi : Integrable L ν := by
    have hh := ((hki.sub hvk.1).congr hn).sub (hpi.sub hvp.1)
    convert hh using 1
    ext x
    dsimp only [Pi.sub_apply]
    ring
  have he : (∫ x, A x ∂ν) - (∫ x, F x ∂ν) =
      ((∫ x, Ap x ∂ν) - (∫ x, Fp x ∂ν)) + ∫ x, L x ∂ν := by
    have hsub : Integrable (fun x => Ap x - Fp x) ν := hpi.sub hvp.1
    rw [← integral_sub hki hvk.1, integral_congr_ae hn,
      integral_add hsub hLi, integral_sub hpi hvp.1]
  rw [diffusion_projectTuple N Q u k hu.1.1, hvp.2] at heq
  refine ⟨hki, hLi, ?_⟩
  rw [hvk.2]
  linarith only [he, heq]

end CompactTests

end Riesz2.ConstrainedNormalMultiplier
