/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.SchurRestriction
public import Riesz2.DecayLong.ExteriorForcesPart2
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Variational bounds for finite matrix resolvents

A positive constant matrix plus a nonnegative scalar form has inverse bounded
by the constant matrix inverse. The source may be any scalar L² function times
a deterministic vector. The form domain and the matrix index are independent.
-/

@[expose] public section
noncomputable section

open MeasureTheory Matrix
open scoped BigOperators MatrixOrder

namespace Riesz2.BoundarySchurBounds

section Variational

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (B : V →L[ℝ] V →L[ℝ] ℝ) (c : ℝ) (hc : 0 < c)
  (hB : ∀ w, c * ‖w‖ ^ 2 ≤ B w w) (J : V →L[ℝ] H)

/-- Internal comparison principle. Variational majorants for two sources bound
their cross pairing through the inverse of a symmetric coercive form. -/
private theorem pair_le_of_variational (hs : ∀ u v, B u v = B v u)
    (f g : H) (A G : ℝ) (hA : 0 ≤ A) (hG : 0 ≤ G)
    (hf : ∀ w, 2 * inner ℝ f (J w) - B w w ≤ A ^ 2)
    (hg : ∀ w, 2 * inner ℝ g (J w) - B w w ≤ G ^ 2) :
    |inner ℝ f (J (CoerciveSolution.solution B c hc hB J g))| ≤ A * G := by
  let u := CoerciveSolution.solution B c hc hB J f
  let v := CoerciveSolution.solution B c hc hB J g
  have hu (w) : B u w = inner ℝ f (J w) :=
    CoerciveSolution.solution_solves B c hc hB J f w
  have hv (w) : B v w = inner ℝ g (J w) :=
    CoerciveSolution.solution_solves B c hc hB J g w
  have hpos (w) : 0 ≤ B w w := (by positivity : 0 ≤ c * ‖w‖ ^ 2).trans (hB w)
  have hfu : B u u ≤ A ^ 2 := by have := hf u; rw [← hu] at this; linarith
  have hgv : B v v ≤ G ^ 2 := by have := hg v; rw [← hv] at this; linarith
  let b : LinearMap.BilinForm ℝ V := B.toLinearMap₁₂
  have hcs : (B u v) ^ 2 ≤ B u u * B v v :=
    b.apply_sq_le_of_symm hpos ⟨fun x y => hs x y⟩ u v
  have hmul : B u u * B v v ≤ A ^ 2 * G ^ 2 :=
    mul_le_mul hfu hgv (hpos v) (sq_nonneg A)
  change |inner ℝ f (J v)| ≤ _
  rw [← hu]
  have hn := abs_nonneg (B u v)
  have hab := mul_nonneg hA hG
  nlinarith [sq_abs (B u v)]

end Variational

section Finite

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Completing the square for a nonsingular positive definite real matrix. -/
private theorem matrix_variational_upper {D : Matrix ι ι ℝ} (hD : D.PosDef)
    (v w : ι → ℝ) :
    2 * (v ⬝ᵥ w) - w ⬝ᵥ (D *ᵥ w) ≤ v ⬝ᵥ (D⁻¹ *ᵥ v) := by
  have hsolve : D *ᵥ (D⁻¹ *ᵥ v) = v := by
    rw [mulVec_mulVec, D.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hD.det_pos.ne'), one_mulVec]
  have hsym (a b : ι → ℝ) : a ⬝ᵥ (D *ᵥ b) = b ⬝ᵥ (D *ᵥ a) := by
    have ht : Dᵀ = D := by simpa only [conjTranspose_eq_transpose_of_trivial] using hD.isHermitian.eq
    rw [dotProduct_mulVec, ← vecMul_transpose D a, ht, dotProduct_comm]
  have h := hD.posSemidef.dotProduct_mulVec_nonneg (w - D⁻¹ *ᵥ v)
  simp only [star_trivial, mulVec_sub, dotProduct_sub, sub_dotProduct, hsolve] at h
  rw [hsym (D⁻¹ *ᵥ v) w, hsolve, dotProduct_comm w v,
    dotProduct_comm (D⁻¹ *ᵥ v) v] at h
  linarith

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}

/-- A deterministic vector multiplied by a scalar L² source. -/
def tensor (v : ι → ℝ) (f : Lp ℝ 2 ν) : PiLp 2 (fun _ : ι => Lp ℝ 2 ν) :=
  WithLp.toLp 2 (fun i => v i • f)

omit [DecidableEq ι] in
/-- Exact pairing for the rank-one source, with all integrals justified by L². -/
private theorem tensor_pair (v : ι → ℝ) (f : Lp ℝ 2 ν)
    (w : PiLp 2 (fun _ : ι => Lp ℝ 2 ν)) :
    inner ℝ (tensor v f) w = ∫ x, f x * (v ⬝ᵥ (fun i => w i x)) ∂ν := by
  rw [PiLp.inner_apply]
  simp only [tensor, PiLp.toLp_apply, real_inner_smul_left]
  simp_rw [L2.inner_def, Real.inner_apply, ← integral_const_mul]
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    filter_upwards with x
    simp only [dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · intro i _
    exact ((Lp.memLp f).integrable_mul (Lp.memLp (w i))).const_mul (v i)

/-- The variational majorant for a tensor source and a constant matrix.
The inverse quadratic form has the exact β⁻¹ normalization. -/
private theorem tensor_variational_upper {D : Matrix ι ι ℝ} (hD : D.PosDef)
    {β : ℝ} (hβ : 0 < β) (v : ι → ℝ) (f : Lp ℝ 2 ν)
    (w : PiLp 2 (fun _ : ι => Lp ℝ 2 ν)) :
    2 * inner ℝ (tensor v f) w -
      β * ∫ x, matrixFieldPair (fun _ => D) w.ofLp w.ofLp x ∂ν ≤
        β⁻¹ * (v ⬝ᵥ (D⁻¹ *ᵥ v)) * ‖f‖ ^ 2 := by
  have hi : Integrable (matrixFieldPair (fun _ => D) w.ofLp w.ofLp) ν :=
    BoundedMatrixForms.integrable_pair (fun _ => D) (fun _ _ => measurable_const)
      ⟨∑ i, ∑ j, |D i j|, Filter.Eventually.of_forall (fun x i j =>
        (Finset.single_le_sum (fun k _ => abs_nonneg (D i k)) (Finset.mem_univ j)).trans
          (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => abs_nonneg (D k l)))
            (Finset.mem_univ i)))⟩ w.ofLp w.ofLp
  have hip : Integrable (fun x => f x * (v ⬝ᵥ (fun i => w i x))) ν := by
    simp only [dotProduct, Finset.mul_sum]
    apply integrable_finsetSum
    intro i _
    simpa only [Pi.mul_apply, mul_left_comm] using
      ((Lp.memLp f).integrable_mul (Lp.memLp (w i))).const_mul (v i)
  have his : Integrable (fun x => β⁻¹ * (v ⬝ᵥ (D⁻¹ *ᵥ v)) * (f x * f x)) ν :=
    ((Lp.memLp f).integrable_mul (Lp.memLp f)).const_mul _
  rw [tensor_pair, ← integral_const_mul, ← integral_const_mul, ← integral_sub
    (hip.const_mul 2) (hi.const_mul β)]
  have hnorm : ‖f‖ ^ 2 = ∫ x, f x * f x ∂ν := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [Real.inner_apply]
  rw [hnorm, ← integral_const_mul]
  apply integral_mono_ae ((hip.const_mul 2).sub (hi.const_mul β)) his
  filter_upwards with x
  have h := matrix_variational_upper hD ((β⁻¹ * f x) • v) (fun i => w i x)
  have hq : ((β⁻¹ * f x) • v) ⬝ᵥ (D⁻¹ *ᵥ ((β⁻¹ * f x) • v)) =
      (β⁻¹ * f x) ^ 2 * (v ⬝ᵥ (D⁻¹ *ᵥ v)) := by
    rw [mulVec_smul, smul_dotProduct, dotProduct_smul]
    simp only [smul_eq_mul]
    ring
  rw [hq, smul_dotProduct] at h
  have hm := mul_le_mul_of_nonneg_left h hβ.le
  have hb : β * β⁻¹ = 1 := mul_inv_cancel₀ hβ.ne'
  have hd : matrixFieldPair (fun _ : α => D) w.ofLp w.ofLp x =
      (fun i => w i x) ⬝ᵥ (D *ᵥ (fun i => w i x)) := by
    simp only [matrixFieldPair, dotProduct, mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  dsimp only [Pi.sub_apply]
  rw [hd]
  simp only [smul_eq_mul] at hm
  calc
    _ = β * (2 * ((β⁻¹ * f x) * (v ⬝ᵥ (fun i => w i x))) -
        (fun i => w i x) ⬝ᵥ (D *ᵥ (fun i => w i x))) := by
      field_simp
    _ ≤ β * ((β⁻¹ * f x) ^ 2 * (v ⬝ᵥ (D⁻¹ *ᵥ v))) := hm
    _ = _ := by field_simp

end Finite

section ConstantMatrix

variable {α ι : Type*} [MeasurableSpace α] {ν : Measure α}
  [Fintype ι] [DecidableEq ι]
  (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)

omit [DecidableEq ι] in
theorem constant_bounded (D : Matrix ι ι ℝ) :
    ∃ b : ℝ, ∀ᵐ _x ∂ν, ∀ i j, |D i j| ≤ b := by
  refine ⟨∑ i, ∑ j, |D i j|, Filter.Eventually.of_forall (fun x i j => ?_)⟩
  exact (Finset.single_le_sum (fun k _ => abs_nonneg (D i k)) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => abs_nonneg (D k l)))
      (Finset.mem_univ i))

/-- The product scalar form plus a positive constant matrix. This uses the
existing bounded-matrix form, on the whole scalar form domain. -/
def constantForm (D : Matrix ι ι ℝ) (hD : D.PosSemidef) :=
  BoundedMatrixForms.form Q hQ (fun _ => D) (fun _ _ => measurable_const)
    (constant_bounded D) (Filter.Eventually.of_forall (fun _ => hD))

private theorem constantForm_apply (D : Matrix ι ι ℝ) (hD : D.PosSemidef)
    (u w : MatrixEnergy.Vector (ι := ι) Q hQ) :
    constantForm Q hQ D hD u w = OperatorSchur.vectorEnergy Q hQ u w +
      ∫ x, matrixFieldPair (fun _ => D) (OperatorSchur.vectorValues Q hQ u).ofLp
        (OperatorSchur.vectorValues Q hQ w).ofLp x ∂ν := by
  rw [constantForm, BoundedMatrixForms.form_apply, OperatorSchur.vectorEnergy_apply]
  rfl

/-- The resolvent equation is the weak equation, including
its full weighted-domain condition and every product-domain test. -/
theorem constantForm_equation_iff (D : Matrix ι ι ℝ) (hD : D.PosSemidef)
    (u : MatrixEnergy.Vector (ι := ι) Q hQ)
    (f : PiLp 2 (fun _ : ι => Lp ℝ 2 ν)) :
    (∀ w, constantForm Q hQ D hD u w =
      inner ℝ f (OperatorSchur.vectorValues Q hQ w)) ↔
      WeightedWeakSolution Q (fun _ => D) ⊤ f.ofLp (MatrixEnergy.vectorEquiv Q hQ u) :=
  BoundedMatrixForms.equation_iff Q hQ (fun _ => D) (fun _ _ => measurable_const)
    (constant_bounded D) (Filter.Eventually.of_forall (fun _ => hD)) u f.ofLp

private theorem constantForm_coercive (D : Matrix ι ι ℝ) (hD : D.PosSemidef)
    (a : ℝ) (hlow : a • (1 : Matrix ι ι ℝ) ≤ D)
    (u : MatrixEnergy.Vector (ι := ι) Q hQ) :
    min 1 a * ‖u‖ ^ 2 ≤ constantForm Q hQ D hD u u := by
  apply BoundedMatrixForms.form_coercive Q hQ (fun _ => D) _ _ _ a _ u
  apply Filter.Eventually.of_forall
  intro x t
  have h := (FiniteMatrixOrder.smul_one_le_iff hD.isHermitian a).mp hlow t
  simpa only [dotProduct, mulVec, Finset.mul_sum, ← mul_assoc, ← pow_two] using h

private theorem constantForm_symmetric (D : Matrix ι ι ℝ) (hD : D.PosSemidef)
    (u w : MatrixEnergy.Vector (ι := ι) Q hQ) :
    constantForm Q hQ D hD u w = constantForm Q hQ D hD w u :=
  BoundedMatrixForms.form_symmetric Q hQ (fun _ => D) _ _ _ u w

/-- Internal sharp comparison, for constant D and arbitrary scalar L² sources.
The lower bound a is used solely to construct the unique resolvent. -/
private theorem constant_resolvent_pair {D : Matrix ι ι ℝ} (hD : D.PosDef)
    (β : ℝ) (hβ : 0 < β) (a : ℝ) (ha : 0 < a)
    (hlow : a • (1 : Matrix ι ι ℝ) ≤ β • D)
    (v w : ι → ℝ) (f g : Lp ℝ 2 ν) (A G : ℝ) (hA : 0 ≤ A) (hG : 0 ≤ G)
    (hv : v ⬝ᵥ (D⁻¹ *ᵥ v) ≤ A ^ 2)
    (hw : w ⬝ᵥ (D⁻¹ *ᵥ w) ≤ G ^ 2) :
    let F := constantForm Q hQ (β • D) (hD.posSemidef.smul hβ.le)
    let J := OperatorSchur.vectorValues (ι := ι) Q hQ
    let R := CoerciveSolution.solution F (min 1 a) (lt_min zero_lt_one ha)
      (constantForm_coercive Q hQ _ _ a hlow) J
    |inner ℝ (tensor v f) (J (R (tensor w g)))| ≤ β⁻¹ * A * G * ‖f‖ * ‖g‖ := by
  dsimp only
  let F := constantForm Q hQ (β • D) (hD.posSemidef.smul hβ.le)
  let J := OperatorSchur.vectorValues (ι := ι) Q hQ
  have hmajor (z : ι → ℝ) (k : Lp ℝ 2 ν) (T : ℝ)
      (hz : z ⬝ᵥ (D⁻¹ *ᵥ z) ≤ T ^ 2) (u : MatrixEnergy.Vector (ι := ι) Q hQ) :
      2 * inner ℝ (tensor z k) (J u) - F u u ≤
        (Real.sqrt β⁻¹ * T * ‖k‖) ^ 2 := by
    have h := tensor_variational_upper hD hβ z k (J u)
    have he := OperatorSchur.vectorEnergy_nonneg Q hQ u
    have hp : F u u = OperatorSchur.vectorEnergy Q hQ u u +
        β * ∫ x, matrixFieldPair (fun _ => D) (J u).ofLp (J u).ofLp x ∂ν := by
      change constantForm Q hQ (β • D) _ u u = _
      rw [constantForm_apply, SchurRestriction.integral_pair_smul]
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr hβ.le)) (sq_nonneg ‖k‖)
    have hsqrt := Real.sq_sqrt (inv_nonneg.mpr hβ.le)
    rw [mul_pow, mul_pow, hsqrt, hp]
    linarith only [h, he, hmul]
  have h := pair_le_of_variational F (min 1 a) (lt_min zero_lt_one ha)
    (constantForm_coercive Q hQ _ _ a hlow) J
    (constantForm_symmetric Q hQ _ _) (tensor v f) (tensor w g)
    (Real.sqrt β⁻¹ * A * ‖f‖) (Real.sqrt β⁻¹ * G * ‖g‖)
    (by positivity) (by positivity) (hmajor v f A hv) (hmajor w g G hw)
  have hsqrt := Real.sq_sqrt (inv_nonneg.mpr hβ.le)
  convert h using 1
  calc
    _ = (Real.sqrt β⁻¹) ^ 2 * A * G * ‖f‖ * ‖g‖ := by rw [hsqrt]
    _ = _ := by ring

end ConstantMatrix

private theorem gaussian_quadratic_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (v : ι → ℝ) :
    let μ := ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ ι) S
    (eLpNorm (fun z : EuclideanSpace ℝ ι => ∑ i, v i * z i) 2 μ).toReal ^ 2 =
      v ⬝ᵥ (S *ᵥ v) := by
  let μ := ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ ι) S
  let x := WithLp.toLp 2 v
  have hf : MemLp (fun z : EuclideanSpace ℝ ι => inner ℝ x z) 2 μ :=
    MemLp.const_inner x ProbabilityTheory.IsGaussian.memLp_two_id
  have heq : (fun z : EuclideanSpace ℝ ι => ∑ i, v i * z i) =
      (fun z => inner ℝ x z) := by
    funext z
    simp only [x, PiLp.inner_apply, Real.inner_apply]
  dsimp only
  rw [heq, ← Lp.norm_toLp _ hf, ← real_inner_self_eq_norm_sq, L2.inner_def]
  calc
    _ = ∫ z, inner ℝ x z * inner ℝ x z ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with z hz
      rw [hz, Real.inner_apply]
    _ = ProbabilityTheory.covarianceBilin μ x x := by
      rw [ProbabilityTheory.covarianceBilin_apply ProbabilityTheory.IsGaussian.memLp_two_id]
      simp only [μ, ProbabilityTheory.integral_id_multivariateGaussian', sub_zero]
    _ = _ := ProbabilityTheory.covarianceBilin_multivariateGaussian hS x x

private theorem reference_exterior_lower (s : Riesz1.RieszExponent) (m : ℕ+)
    (hm : 2 ≤ (m : ℕ)) (K : ℕ) (hK : 1 ≤ K) (hKm : K ≤ (m : ℕ) / 4)
    (E : Finset (Fin (m : ℕ))) (β : ℝ) (hβ : 0 < β) :
    ∃ a : ℝ, 0 < a ∧ a • (1 : Matrix E E ℝ) ≤
      β • (((2 : ℝ) • referenceIntervalMatrix s m hm K).submatrix
        (Subtype.val : E → Fin (m : ℕ)) Subtype.val) := by
  obtain ⟨c, hc, htrunc⟩ := referenceIntervalMatrix_truncated_coercivity s
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  refine ⟨β * 2 * (c * (K : ℝ) ^ (-1 - s.val)), by positivity, ?_⟩
  have h := smul_le_smul_of_nonneg_left (htrunc m hm K hK hKm).2.2
    (show 0 ≤ β * 2 from by positivity)
  have hp := FiniteMatrixOrder.loewner_principal h E
  have hone : (1 : Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ).submatrix
      (Subtype.val : E → Fin (m : ℕ)) Subtype.val = 1 :=
    submatrix_one _ Subtype.val_injective
  change (β * 2) • ((c * (K : ℝ) ^ (-1 - s.val)) •
    ((1 : Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ).submatrix
      (Subtype.val : E → Fin (m : ℕ)) Subtype.val)) ≤ _ at hp
  rw [hone, smul_smul] at hp
  convert hp using 1
  ext i j
  simp only [Matrix.smul_apply, submatrix_apply, smul_eq_mul, mul_assoc]

/-- The row used for the Gaussian force is exactly the column Ceᵢ of the
reference coupling, by symmetry of the interval matrix. -/
theorem reference_column_eq (s : Riesz1.RieszExponent) (m : ℕ+)
    (hm : 2 ≤ (m : ℕ)) (K : ℕ) (i a : Fin (m : ℕ)) :
    2 * referenceIntervalMatrix s m hm K i a =
      ((2 : ℝ) • referenceIntervalMatrix s m hm K) a i := by
  have h := congrArg (fun A : Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ => A a i)
    (referenceIntervalMatrix_isHermitian s m hm K).eq
  simp only [conjTranspose_apply, star_trivial] at h
  simpa only [Matrix.smul_apply, smul_eq_mul] using congrArg (fun x : ℝ => 2 * x) h

/-- See Lemma 5.5 of the paper, in the stronger cutoff form. There is a unique
full-domain resolvent of βD + L on the exterior L² product. Both Schur
pairings are bounded by C K², with C depending only on s and β. The same
resolvent acts on every scalar source. No boundedness of the source is assumed.
The exterior may be empty. -/
theorem bilinear_schur_cutoff (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (β : ℝ) (hβ : 0 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ+) (hm : 2 ≤ (m : ℕ)) (K : ℕ),
      ∀ (hK : 1 ≤ K) (hKm : K ≤ (m : ℕ) / 4), ∀ n : ℕ, n ≤ (m : ℕ) →
      ∀ {α : Type} [MeasurableSpace α] (ν : Measure α)
        (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q),
      let E := Finset.univ.filter (fun j : Fin (m : ℕ) => n ≤ j.val)
      let D : Matrix E E ℝ := ((2 : ℝ) • referenceIntervalMatrix s m hm K).submatrix
        (Subtype.val : E → Fin (m : ℕ)) Subtype.val
      let hD := (ExteriorForces.exteriorBlock_posDef s m hm hK hKm E).1
      let col := fun (i : Fin (m : ℕ)) (a : E) => 2 * referenceIntervalMatrix s m hm K i a.val
      let F := constantForm Q hQ (β • D) (hD.posSemidef.smul hβ.le)
      let J := OperatorSchur.vectorValues (ι := E) Q hQ
      ∃ R : PiLp 2 (fun _ : E => Lp ℝ 2 ν) →L[ℝ] MatrixEnergy.Vector (ι := E) Q hQ,
        (∀ f w, F (R f) w = inner ℝ f (J w)) ∧
        (∀ f u, (∀ w, F u w = inner ℝ f (J w)) → u = R f) ∧
        ∀ (η φ : Lp ℝ 2 ν) (i j l : Fin (m : ℕ)),
          i.val < n → j.val < n → l.val < n →
          |inner ℝ (tensor (col j) η) (J (R (tensor (col i) φ)))| ≤
            C * (K : ℝ) ^ 2 * (min (i.val + 1) (n - i.val) : ℕ) ^ (-s.val / 2) *
              (min (j.val + 1) (n - j.val) : ℕ) ^ (-s.val / 2) * ‖η‖ * ‖φ‖ ∧
          |inner ℝ (tensor (col j - col l) η) (J (R (tensor (col i) φ)))| ≤
            C * (K : ℝ) ^ 2 * (Nat.dist j.val l.val : ℝ) *
              (min (i.val + 1) (n - i.val) : ℕ) ^ (-s.val / 2) *
              (min (min (j.val + 1) (n - j.val)) (min (l.val + 1) (n - l.val)) : ℕ) ^
                (-1 - s.val / 2) * ‖η‖ * ‖φ‖ := by
  obtain ⟨B, hB, hforce⟩ := ExteriorForces.exterior_force_bounds hz s
  refine ⟨β⁻¹ * B ^ 2, by positivity, ?_⟩
  intro m hm K hK hKm n hn α _ ν Q hQ
  dsimp only
  let E := Finset.univ.filter (fun j : Fin (m : ℕ) => n ≤ j.val)
  let D : Matrix E E ℝ := ((2 : ℝ) • referenceIntervalMatrix s m hm K).submatrix
    (Subtype.val : E → Fin (m : ℕ)) Subtype.val
  let col := fun (i : Fin (m : ℕ)) (a : E) => 2 * referenceIntervalMatrix s m hm K i a.val
  have hD := (ExteriorForces.exteriorBlock_posDef s m hm hK hKm E).1
  obtain ⟨a, ha, hlow⟩ := reference_exterior_lower s m hm K hK hKm E β hβ
  let F := constantForm Q hQ (β • D) (hD.posSemidef.smul hβ.le)
  let J := OperatorSchur.vectorValues (ι := E) Q hQ
  let R := CoerciveSolution.solution F (min 1 a) (lt_min zero_lt_one ha)
    (constantForm_coercive Q hQ _ _ a hlow) J
  refine ⟨R, CoerciveSolution.solution_solves _ _ _ _ _, ?_, ?_⟩
  · intro f u hu
    apply CoerciveSolution.inverse_unique F (min 1 a) (lt_min zero_lt_one ha)
      (constantForm_coercive Q hQ _ _ a hlow)
    exact hu
  intro η φ i j l hi hj hl
  obtain ⟨hpoint, hinc⟩ := hforce m hm K hK hKm n hn
  dsimp only at hpoint hinc
  have hq (k : Fin (m : ℕ)) (hk : k.val < n) :
      col k ⬝ᵥ (D⁻¹ *ᵥ col k) ≤
        (B * K * (min (k.val + 1) (n - k.val) : ℕ) ^ (-s.val / 2)) ^ 2 := by
    rw [← gaussian_quadratic_norm hD.inv.posSemidef (col k)]
    exact pow_le_pow_left₀ (ENNReal.toReal_nonneg) (hpoint k hk).2 2
  have hqi : (col j - col l) ⬝ᵥ (D⁻¹ *ᵥ (col j - col l)) ≤
      (B * K * (Nat.dist j.val l.val : ℝ) *
        (min (min (j.val + 1) (n - j.val)) (min (l.val + 1) (n - l.val)) : ℕ) ^
          (-1 - s.val / 2)) ^ 2 := by
    rw [← gaussian_quadratic_norm hD.inv.posSemidef (col j - col l)]
    have heq : (fun z : EuclideanSpace ℝ E => ∑ t, (col j - col l) t * z t) =
        ((fun z : EuclideanSpace ℝ E => ∑ t, col j t * z t) -
          (fun z : EuclideanSpace ℝ E => ∑ t, col l t * z t)) := by
      funext z
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    rw [heq]
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg (hinc j l hj hl).2 2
  constructor
  · have h := constant_resolvent_pair Q hQ hD β hβ a ha hlow (col j) (col i) η φ _ _
      (by positivity) (by positivity) (hq j hj) (hq i hi)
    dsimp only at h
    convert h using 1
    ring
  · have h := constant_resolvent_pair Q hQ hD β hβ a ha hlow (col j - col l) (col i) η φ _ _
      (by positivity) (by positivity) hqi (hq i hi)
    dsimp only at h
    convert h using 1
    ring


/-- The cutoff loss retains the structural exponent 2 M₀, independently of ε. -/
theorem cutoff_sq_le (n M₀ : ℕ) (hn : 1 ≤ n) (ε : ℝ) :
    ((⌊(n : ℝ) ^ ε⌋₊ ^ M₀ : ℕ) : ℝ) ^ 2 ≤ (n : ℝ) ^ ((2 * M₀ : ℝ) * ε) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ = (⌊(n : ℝ) ^ ε⌋₊ : ℝ) ^ (M₀ * 2) := by rw [Nat.cast_pow, pow_mul]
    _ ≤ ((n : ℝ) ^ ε) ^ (M₀ * 2) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le (by positivity)) _
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
      congr 1
      push_cast
      ring

/-- See Lemma 5.5 of the paper: both bilinear Schur estimates with the prescribed
cutoff K = floor(n^ε)^M₀ and loss n^(κ ε). The constants precede ε and every
system size and scalar probability space. The unique resolvent is specified
by its equation on every product form-domain test. -/
theorem bilinear_schur (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (β : ℝ) (hβ : 0 < β) (M₀ : ℕ) (hM₀ : 0 < M₀) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ (ε : ℝ), 0 < ε →
      ∀ n : ℕ, 1 ≤ n → ∀ (m : ℕ+) (hm : 2 ≤ (m : ℕ)), n ≤ (m : ℕ) →
      let K := ⌊(n : ℝ) ^ ε⌋₊ ^ M₀
      ∀ (hK : 1 ≤ K) (hKm : K ≤ (m : ℕ) / 4),
      ∀ {α : Type} [MeasurableSpace α] (ν : Measure α)
        (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q),
      let E := Finset.univ.filter (fun j : Fin (m : ℕ) => n ≤ j.val)
      let D : Matrix E E ℝ := ((2 : ℝ) • referenceIntervalMatrix s m hm K).submatrix
        (Subtype.val : E → Fin (m : ℕ)) Subtype.val
      let hD := (ExteriorForces.exteriorBlock_posDef s m hm hK hKm E).1
      let col := fun (i : Fin (m : ℕ)) (a : E) => 2 * referenceIntervalMatrix s m hm K i a.val
      let F := constantForm Q hQ (β • D) (hD.posSemidef.smul hβ.le)
      let J := OperatorSchur.vectorValues (ι := E) Q hQ
      ∃ R : PiLp 2 (fun _ : E => Lp ℝ 2 ν) →L[ℝ] MatrixEnergy.Vector (ι := E) Q hQ,
        (∀ f w, F (R f) w = inner ℝ f (J w)) ∧
        (∀ f u, (∀ w, F u w = inner ℝ f (J w)) → u = R f) ∧
        ∀ (η φ : Lp ℝ 2 ν) (i j l : Fin (m : ℕ)),
          i.val < n → j.val < n → l.val < n →
          |inner ℝ (tensor (col j) η) (J (R (tensor (col i) φ)))| ≤
            C * (n : ℝ) ^ (κ * ε) * (min (i.val + 1) (n - i.val) : ℕ) ^ (-s.val / 2) *
              (min (j.val + 1) (n - j.val) : ℕ) ^ (-s.val / 2) * ‖η‖ * ‖φ‖ ∧
          |inner ℝ (tensor (col j - col l) η) (J (R (tensor (col i) φ)))| ≤
            C * (n : ℝ) ^ (κ * ε) * (Nat.dist j.val l.val : ℝ) *
              (min (i.val + 1) (n - i.val) : ℕ) ^ (-s.val / 2) *
              (min (min (j.val + 1) (n - j.val)) (min (l.val + 1) (n - l.val)) : ℕ) ^
                (-1 - s.val / 2) * ‖η‖ * ‖φ‖ := by
  obtain ⟨C, hC, hmain⟩ := bilinear_schur_cutoff hz s β hβ
  refine ⟨C, 2 * M₀, hC, by positivity, ?_⟩
  intro ε hε n hn m hm hnm K hK hKm α _ ν Q hQ
  obtain ⟨R, hR, huniq, hest⟩ := hmain m hm K hK hKm n hnm ν Q hQ
  refine ⟨R, hR, huniq, ?_⟩
  intro η φ i j l hi hj hl
  obtain ⟨hpoint, hinc⟩ := hest η φ i j l hi hj hl
  have hcut : (K : ℝ) ^ 2 ≤ (n : ℝ) ^ ((2 * M₀ : ℝ) * ε) := cutoff_sq_le n M₀ hn ε
  constructor
  · apply hpoint.trans
    gcongr
  · apply hinc.trans
    gcongr

/-- In the full-cycle case the exterior carrier is empty, so both Schur
pairings vanish for all sources. -/
theorem empty_exterior_pair {m : ℕ+} {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (f g : PiLp 2 (fun _ : (Finset.univ.filter
      (fun j : Fin (m : ℕ) => (m : ℕ) ≤ j.val)) => Lp ℝ 2 ν)) :
    inner ℝ f g = 0 := by
  have hE : IsEmpty ↥(Finset.univ.filter (fun j : Fin (m : ℕ) => (m : ℕ) ≤ j.val)) :=
    ⟨fun j => by have hj := (Finset.mem_filter.mp j.property).2; omega⟩
  rw [PiLp.inner_apply]
  exact Finset.sum_eq_zero (fun j _ => (hE.false j).elim)

end Riesz2.BoundarySchurBounds
