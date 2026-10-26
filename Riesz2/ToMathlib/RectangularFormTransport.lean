/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.MatrixEnergySpaces

/-!
# Rectangular changes of vector components

Transport of the literal scalar and matrix pairings through a rectangular
orthonormal inclusion, for Proposition 3.3. The base measure
and scalar Sobolev carrier are unchanged. No new energy domain is introduced.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Matrix
open scoped BigOperators RealInnerProductSpace

namespace Riesz2.RectangularFormTransport

variable {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]

/-- Apply a real matrix to a finite tuple in any real module, as used for the
ambient inclusion in Proposition 3.3. -/
def tupleMap {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Matrix ι κ ℝ) : (κ → V) →ₗ[ℝ] (ι → V) where
  toFun u i := ∑ a, A i a • u a
  map_add' u v := by ext i; simp [smul_add, Finset.sum_add_distrib]
  map_smul' r u := by ext i; simp [smul_smul, mul_comm, Finset.smul_sum]

omit [Fintype ι] in
/-- Composition is literal matrix multiplication, Proposition 3.3. This applies on the full scalar form carrier. -/
theorem tupleMap_mul {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : Matrix ι κ ℝ) (B : Matrix κ τ ℝ) (u : τ → V) :
    tupleMap A (tupleMap B u) = tupleMap (A * B) u := by
  ext i
  simp only [tupleMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.smul_sum,
    smul_smul, Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]

/-- The identity matrix fixes every tuple, Proposition 3.3. -/
theorem tupleMap_one {V : Type*} [AddCommGroup V] [Module ℝ V]
    [DecidableEq ι] (u : ι → V) : tupleMap (1 : Matrix ι ι ℝ) u = u := by
  ext i
  simp [tupleMap, Matrix.one_apply]

/-- A rectangular orthonormal inclusion has a left inverse on scalar tuples,
Proposition 3.3. -/
theorem tupleMap_left_inverse {V : Type*} [AddCommGroup V] [Module ℝ V]
    [DecidableEq κ] (A : Matrix ι κ ℝ) (hA : A.transpose * A = 1) (u : κ → V) :
    tupleMap A.transpose (tupleMap A u) = u := by
  rw [tupleMap_mul, hA, tupleMap_one]

section Values

variable {α : Type*} [MeasurableSpace α] {ρ : Measure α}

/-- Matrix combination on L² has its usual pointwise value almost everywhere,
Proposition 3.3. -/
theorem tupleMap_lp_ae (A : Matrix ι κ ℝ) (u : κ → Lp ℝ 2 ρ) :
    ∀ᵐ x ∂ρ, ∀ i, tupleMap A u i x = ∑ a, A i a * u a x := by
  apply ae_all_iff.mpr
  intro i
  have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun a => A i a • u a)
  have hm := ae_all_iff.mpr (fun a => Lp.coeFn_smul (A i a) (u a))
  filter_upwards [hs, hm] with x hx hy
  change (∑ a, A i a • u a) x = _
  rw [hx]
  exact Finset.sum_congr rfl (fun a _ => by rw [hy a]; rfl)

omit [Fintype ι] in
/-- Scalar form values commute with a rectangular component map, Proposition 3.3. -/
theorem tupleMap_value (Q : ScalarFormData ρ) (A : Matrix ι κ ℝ)
    (u : κ → Q.1) (i : ι) :
    (tupleMap A u i).val = tupleMap A (fun a => (u a).val) i := by
  simp only [tupleMap, LinearMap.coe_mk, AddHom.coe_mk,
    Submodule.coe_sum, Submodule.coe_smul]

/-- The finite matrix pairing commutes with compression, including all cross
terms in Proposition 3.3. -/
theorem matrixFieldPair_tupleMap (A : Matrix ι κ ℝ) (M : α → Matrix ι ι ℝ)
    (u w : κ → Lp ℝ 2 ρ) :
    matrixFieldPair M (tupleMap A u) (tupleMap A w) =ᵐ[ρ]
      matrixFieldPair (fun x => A.transpose * M x * A) u w := by
  filter_upwards [tupleMap_lp_ae A u, tupleMap_lp_ae A w] with x hu hw
  simp only [MatrixEnergy.matrixFieldPair_eq_dot, hu, hw]
  change (A *ᵥ fun a => u a x) ⬝ᵥ (M x *ᵥ (A *ᵥ fun a => w a x)) =
    (fun a => u a x) ⬝ᵥ ((A.transpose * M x * A) *ᵥ fun a => w a x)
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_transpose_mulVec, dotProduct_comm]

/-- Orthonormal component inclusion preserves every scalar bilinear pairing,
Proposition 3.3. This includes the diffusion pairing. -/
theorem sum_bilinear_tupleMap {V : Type*} [AddCommGroup V] [Module ℝ V]
    [DecidableEq κ] (A : Matrix ι κ ℝ) (hA : A.transpose * A = 1)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (u w : κ → V) :
    (∑ i, B (tupleMap A u i) (tupleMap A w i)) = ∑ a, B (u a) (w a) := by
  simp only [tupleMap, LinearMap.coe_mk, AddHom.coe_mk, map_sum, LinearMap.sum_apply,
    map_smul, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  calc
    (∑ i, ∑ b, ∑ a, A i b * (A i a * B (u a) (w b))) =
        ∑ b, ∑ a, (∑ i, A i b * A i a) * B (u a) (w b) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    _ = ∑ a, B (u a) (w a) := by
      have hc (a b : κ) : (∑ i, A i a * A i b) = if a = b then 1 else 0 := by
        simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using
          congrArg (fun C : Matrix κ κ ℝ => C a b) hA
      simp [hc]

/-- Orthonormal component inclusion preserves scalar form diffusion, Proposition 3.3. -/
theorem diffusion_tupleMap [DecidableEq κ] (Q : ScalarFormData ρ)
    (A : Matrix ι κ ℝ) (hA : A.transpose * A = 1) (u w : κ → Q.1) :
    (∑ i, Q.2 (tupleMap A u i) (tupleMap A w i)) = ∑ a, Q.2 (u a) (w a) :=
  sum_bilinear_tupleMap A hA Q.2 u w

/-- Orthonormal component inclusion preserves the L² source pairing, Proposition 3.3. -/
theorem source_tupleMap [DecidableEq κ] (Q : ScalarFormData ρ)
    (A : Matrix ι κ ℝ) (hA : A.transpose * A = 1)
    (v : κ → Lp ℝ 2 ρ) (u : κ → Q.1) :
    (∑ i, inner ℝ (tupleMap A v i) (tupleMap A u i).val) =
      ∑ a, inner ℝ (v a) (u a).val := by
  let B : Lp ℝ 2 ρ →ₗ[ℝ] Lp ℝ 2 ρ →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (inner ℝ) inner_add_left (fun r x y => real_inner_smul_left x y r)
      inner_add_right (fun r x y => inner_smul_right x y r)
  simp_rw [tupleMap_value]
  exact sum_bilinear_tupleMap A hA B v (fun a => (u a).val)

/-- Included fields take values in precisely the matrix range, Proposition 3.3. -/
theorem tupleMap_mem_range (Q : ScalarFormData ρ) (A : Matrix ι κ ℝ)
    (u : κ → Q.1) :
    ∀ᵐ x ∂ρ, (fun i => (tupleMap A u i).val x) ∈ A.mulVecLin.range := by
  have he := tupleMap_lp_ae A (fun a => (u a).val)
  filter_upwards [he] with x hx
  refine ⟨fun a => (u a).val x, ?_⟩
  ext i
  rw [tupleMap_value]
  exact (hx i).symm

/-- Every range-valued scalar-form tuple is recovered by compression and
inclusion. This acts on the complete scalar carrier, Proposition 3.3. -/
theorem tupleMap_right_inverse [DecidableEq κ]
    (Q : ScalarFormData ρ) (A : Matrix ι κ ℝ) (hA : A.transpose * A = 1)
    (u : ι → Q.1)
    (hu : ∀ᵐ x ∂ρ, (fun i => (u i).val x) ∈ A.mulVecLin.range) :
    tupleMap A (tupleMap A.transpose u) = u := by
  rw [tupleMap_mul]
  funext i
  apply Subtype.ext
  rw [tupleMap_value]
  apply Lp.ext
  filter_upwards [hu, tupleMap_lp_ae (A * A.transpose) (fun i => (u i).val)] with x hx hy
  rw [hy i]
  have hp : (A * A.transpose) *ᵥ (fun i => (u i).val x) = fun i => (u i).val x := by
    obtain ⟨v, hv⟩ := hx
    change A *ᵥ v = (fun i => (u i).val x) at hv
    rw [← hv, mulVec_mulVec, Matrix.mul_assoc, hA, Matrix.mul_one]
  exact congrFun hp i

/-- Inclusion identifies the full compressed finite-energy domain with the
range-constrained ambient one, Proposition 3.3. -/
theorem weightedFormDomain_tupleMap (Q : ScalarFormData ρ)
    (A : Matrix ι κ ℝ) (M : α → Matrix ι ι ℝ) (u : κ → Q.1) :
    WeightedFormDomain Q M A.mulVecLin.range (tupleMap A u) ↔
      WeightedFormDomain Q (fun x => A.transpose * M x * A) ⊤ u := by
  have he : matrixFieldPair M (fun i => (tupleMap A u i).val)
      (fun i => (tupleMap A u i).val) =ᵐ[ρ]
      matrixFieldPair (fun x => A.transpose * M x * A)
        (fun a => (u a).val) (fun a => (u a).val) := by
    simp_rw [tupleMap_value]
    exact matrixFieldPair_tupleMap A M _ _
  constructor
  · intro hu
    exact ⟨Eventually.of_forall (fun _ => Submodule.mem_top), hu.2.congr he⟩
  · intro hu
    exact ⟨tupleMap_mem_range Q A u, hu.2.congr he.symm⟩

/-- The complete weak equation is transported by rectangular inclusion,
with all cross-integrability clauses, Proposition 3.3.
 -/
theorem weightedWeakSolution_tupleMap [DecidableEq κ]
    (Q : ScalarFormData ρ) (A : Matrix ι κ ℝ) (hA : A.transpose * A = 1)
    (M : α → Matrix ι ι ℝ) (v : κ → Lp ℝ 2 ρ) (u : κ → Q.1) :
    WeightedWeakSolution Q M A.mulVecLin.range (tupleMap A v) (tupleMap A u) ↔
      WeightedWeakSolution Q (fun x => A.transpose * M x * A) ⊤ v u := by
  have hpair (u w : κ → Q.1) :
      matrixFieldPair M (fun i => (tupleMap A u i).val)
        (fun i => (tupleMap A w i).val) =ᵐ[ρ]
        matrixFieldPair (fun x => A.transpose * M x * A)
          (fun a => (u a).val) (fun a => (w a).val) := by
    simp_rw [tupleMap_value]
    exact matrixFieldPair_tupleMap A M _ _
  constructor
  · rintro ⟨hu, hw⟩
    refine ⟨(weightedFormDomain_tupleMap Q A M u).mp hu, fun w hw' => ?_⟩
    obtain ⟨hi, he⟩ := hw (tupleMap A w) ((weightedFormDomain_tupleMap Q A M w).mpr hw')
    refine ⟨hi.congr (hpair u w), ?_⟩
    rw [diffusion_tupleMap Q A hA, integral_congr_ae (hpair u w), source_tupleMap Q A hA] at he
    exact he
  · rintro ⟨hu, hw⟩
    refine ⟨(weightedFormDomain_tupleMap Q A M u).mpr hu, fun w hw' => ?_⟩
    have hrec := tupleMap_right_inverse Q A hA w hw'.1
    let t := tupleMap A.transpose w
    have ht : WeightedFormDomain Q (fun x => A.transpose * M x * A) ⊤ t := by
      apply (weightedFormDomain_tupleMap Q A M t).mp
      rwa [hrec]
    obtain ⟨hi, he⟩ := hw t ht
    have hcross := hpair u t
    rw [hrec] at hcross
    refine ⟨hi.congr hcross.symm, ?_⟩
    rw [← hrec, diffusion_tupleMap Q A hA, integral_congr_ae (hpair u t),
      source_tupleMap Q A hA]
    exact he

/-- The full variational functional is unchanged by rectangular
inclusion, Proposition 3.3. -/
theorem functional_tupleMap [DecidableEq κ]
    (Q : ScalarFormData ρ) (A : Matrix ι κ ℝ) (hA : A.transpose * A = 1)
    (M : α → Matrix ι ι ℝ) (v : κ → Lp ℝ 2 ρ) (u : κ → Q.1) :
    (∑ i, Q.2 (tupleMap A u i) (tupleMap A u i)) +
      (∫ x, matrixFieldPair M (fun i => (tupleMap A u i).val)
        (fun i => (tupleMap A u i).val) x ∂ρ) -
      2 * (∑ i, inner ℝ (tupleMap A v i) (tupleMap A u i).val) =
    (∑ a, Q.2 (u a) (u a)) +
      (∫ x, matrixFieldPair (fun x => A.transpose * M x * A)
        (fun a => (u a).val) (fun a => (u a).val) x ∂ρ) -
      2 * (∑ a, inner ℝ (v a) (u a).val) := by
  rw [diffusion_tupleMap Q A hA, source_tupleMap Q A hA]
  congr 1
  congr 1
  apply integral_congr_ae
  simp_rw [tupleMap_value]
  exact matrixFieldPair_tupleMap A M _ _

/-- Unique weak solvability transports to the entire ambient constrained
domain, Proposition 3.3 (internal transport criterion). -/
theorem existsUnique_weightedWeakSolution_tupleMap [DecidableEq κ]
    (Q : ScalarFormData ρ) (A : Matrix ι κ ℝ) (hA : A.transpose * A = 1)
    (M : α → Matrix ι ι ℝ) (v : κ → Lp ℝ 2 ρ)
    (hsol : ∃! u : κ → Q.1,
      WeightedWeakSolution Q (fun x => A.transpose * M x * A) ⊤ v u) :
    ∃! u : ι → Q.1, WeightedWeakSolution Q M A.mulVecLin.range (tupleMap A v) u := by
  obtain ⟨u, hu, huniq⟩ := hsol
  refine ⟨tupleMap A u, (weightedWeakSolution_tupleMap Q A hA M v u).mpr hu, ?_⟩
  intro w hw
  have hrec := tupleMap_right_inverse Q A hA w hw.1.1
  have ht : WeightedWeakSolution Q (fun x => A.transpose * M x * A) ⊤ v
      (tupleMap A.transpose w) := by
    apply (weightedWeakSolution_tupleMap Q A hA M v _).mp
    rwa [hrec]
  exact hrec.symm.trans (congrArg (tupleMap A) (huniq _ ht))

/-- Unique minimization over the full finite-energy domain transports to
all range-valued ambient fields, Proposition 3.3.
This internal criterion does not restrict the competitors to gradient fields. -/
theorem unique_minimum_tupleMap [DecidableEq κ]
    (Q : ScalarFormData ρ) (A : Matrix ι κ ℝ) (hA : A.transpose * A = 1)
    (M : α → Matrix ι ι ℝ) (v : κ → Lp ℝ 2 ρ) (u : κ → Q.1) :
    let J := fun w : κ → Q.1 =>
      (∑ a, Q.2 (w a) (w a)) +
        (∫ x, matrixFieldPair (fun x => A.transpose * M x * A)
          (fun a => (w a).val) (fun a => (w a).val) x ∂ρ) -
        2 * (∑ a, inner ℝ (v a) (w a).val)
    let J' := fun w : ι → Q.1 =>
      (∑ i, Q.2 (w i) (w i)) +
        (∫ x, matrixFieldPair M (fun i => (w i).val) (fun i => (w i).val) x ∂ρ) -
        2 * (∑ i, inner ℝ (tupleMap A v i) (w i).val)
    (∀ w : κ → Q.1, WeightedFormDomain Q (fun x => A.transpose * M x * A) ⊤ w →
      J u ≤ J w ∧ (J w = J u → w = u)) →
    ∀ w : ι → Q.1, WeightedFormDomain Q M A.mulVecLin.range w →
      J' (tupleMap A u) ≤ J' w ∧ (J' w = J' (tupleMap A u) → w = tupleMap A u) := by
  intro J J' hmin w hw
  let t := tupleMap A.transpose w
  have hrec : tupleMap A t = w := tupleMap_right_inverse Q A hA w hw.1
  have ht : WeightedFormDomain Q (fun x => A.transpose * M x * A) ⊤ t := by
    apply (weightedFormDomain_tupleMap Q A M t).mp
    rwa [hrec]
  have hu : J' (tupleMap A u) = J u := functional_tupleMap Q A hA M v u
  have htw : J' w = J t := by
    rw [← hrec]
    exact functional_tupleMap Q A hA M v t
  obtain ⟨hle, heq⟩ := hmin t ht
  refine ⟨by linarith only [hle, hu, htw], fun hh => ?_⟩
  have he : t = u := heq (by linarith only [hh, hu, htw])
  exact hrec.symm.trans (congrArg (tupleMap A) he)

end Values

end Riesz2.RectangularFormTransport
