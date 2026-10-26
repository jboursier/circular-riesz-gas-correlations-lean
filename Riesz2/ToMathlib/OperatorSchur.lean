/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.CoerciveSolutionMaps
public import Riesz2.ToMathlib.FiniteMatrixOrder

/-!
# Schur elimination on Hilbert form domains

Schur elimination for Subsection 4.3, Lemma 4.6, Subsection 5.1, Lemma 5.4
and the proof of Lemma 5.14. The diagonal forms act on complete form spaces.
The coupling and Schur correction are bounded ambient operators.

The exterior inverse is the coercive inverse. Elimination holds for arbitrary
dual sources. Compression inherits coercivity by testing the full form on the
harmonic lift. Bounded perturbations preserve the associated-operator domain.
The final section applies this to finite tuples in the scalar domain,
including finite row sums. Empty exterior spaces are allowed.
-/

@[expose] public section
noncomputable section

open MeasureTheory InnerProductSpace
open scoped BigOperators

namespace Riesz2.OperatorSchur

section Elimination

variable {U W : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

variable (A : U →L[ℝ] U →L[ℝ] ℝ) (D : W →L[ℝ] W →L[ℝ] ℝ)
  (C : U →L[ℝ] W →L[ℝ] ℝ) (d : ℝ) (hd : 0 < d)
  (hD : ∀ w, d * ‖w‖ ^ 2 ≤ D w w)

/-- Exterior response on the full exterior form domain. -/
def exterior : U →L[ℝ] W := (CoerciveSolution.inverse D d hd hD).comp C

theorem exterior_solves (u : U) (w : W) :
    D (exterior D C d hd hD u) w = C u w :=
  CoerciveSolution.inverse_solves D d hd hD (C u) w

/-- A zero exterior space has zero exterior response, covering an empty block and
the one-component constant-mode decomposition. -/
theorem exterior_eq_zero [Subsingleton W] (u : U) : exterior D C d hd hD u = 0 :=
  Subsingleton.elim _ _

/-- The Schur form is continuous in the form norm. It need not be an ambient bounded
operator. The order of the coupling and exterior inverse is fixed. -/
def reduced : U →L[ℝ] U →L[ℝ] ℝ := A - C.flip.comp (exterior D C d hd hD)

theorem reduced_apply (u v : U) :
    reduced A D C d hd hD u v = A u v - C v (exterior D C d hd hD u) := rfl

theorem reduced_eq_of_subsingleton [Subsingleton W] : reduced A D C d hd hD = A := by
  ext u v
  simp only [reduced_apply, exterior_eq_zero, map_zero, sub_zero]

/-- The full symmetric off-diagonal block form on the product of form domains. -/
def blockForm : (U × W) →L[ℝ] (U × W) →L[ℝ] ℝ :=
  A.bilinearComp (ContinuousLinearMap.fst ℝ U W) (ContinuousLinearMap.fst ℝ U W) +
  C.bilinearComp (ContinuousLinearMap.fst ℝ U W) (ContinuousLinearMap.snd ℝ U W) +
  C.flip.bilinearComp (ContinuousLinearMap.snd ℝ U W) (ContinuousLinearMap.fst ℝ U W) +
  D.bilinearComp (ContinuousLinearMap.snd ℝ U W) (ContinuousLinearMap.snd ℝ U W)

omit [CompleteSpace W] in
theorem blockForm_apply (u v : U) (z w : W) :
    blockForm A D C (u, z) (v, w) = A u v + C u w + C v z + D z w := rfl

/-- Elimination of the exterior equation, for arbitrary continuous dual sources.
No multiplication operator is commuted with the scalar generator. -/
theorem eliminate_iff (f : StrongDual ℝ U) (g : StrongDual ℝ W) (u : U) (z : W) :
    ((∀ v, A u v + C v z = f v) ∧ (∀ w, D z w + C u w = g w)) ↔
      z = CoerciveSolution.inverse D d hd hD g - exterior D C d hd hD u ∧
      ∀ v, reduced A D C d hd hD u v =
        f v - C v (CoerciveSolution.inverse D d hd hD g) := by
  constructor
  · rintro ⟨hu, hz⟩
    have he : z = CoerciveSolution.inverse D d hd hD (g - C u) := by
      apply CoerciveSolution.inverse_unique
      intro w
      change D z w = g w - C u w
      linarith [hz w]
    have he' : z = CoerciveSolution.inverse D d hd hD g - exterior D C d hd hD u := by
      simpa only [map_sub, exterior, ContinuousLinearMap.comp_apply] using he
    refine ⟨he', fun v => ?_⟩
    have hv := hu v
    rw [he', map_sub] at hv
    rw [reduced_apply]
    linarith
  · rintro ⟨rfl, hu⟩
    constructor
    · intro v
      have hv := hu v
      rw [reduced_apply] at hv
      rw [map_sub]
      linarith
    · intro w
      simp only [map_sub, sub_apply,
        CoerciveSolution.inverse_solves, exterior_solves]
      ring

omit [CompleteSpace W] in
/-- Testing a block equation on the two coordinate subspaces is equivalent to
testing it on the entire product domain. -/
theorem block_equation_iff (f : StrongDual ℝ U) (g : StrongDual ℝ W) (u : U) (z : W) :
    (∀ p : U × W, blockForm A D C (u, z) p = f p.1 + g p.2) ↔
      (∀ v, A u v + C v z = f v) ∧ (∀ w, D z w + C u w = g w) := by
  constructor
  · intro h
    constructor
    · intro v
      simpa [blockForm_apply] using h (v, 0)
    · intro w
      simpa [blockForm_apply, add_comm] using h (0, w)
  · rintro ⟨hu, hz⟩ ⟨v, w⟩
    rw [blockForm_apply]
    linarith [hu v, hz w]

/-- The inverse restricted to sources in the first block is the Schur inverse. -/
theorem zero_exterior_source_iff (f : StrongDual ℝ U) (u : U) (z : W) :
    (∀ p : U × W, blockForm A D C (u, z) p = f p.1) ↔
      z = -exterior D C d hd hD u ∧
        ∀ v, reduced A D C d hd hD u v = f v := by
  simpa using (block_equation_iff A D C f 0 u z).trans
    (eliminate_iff A D C d hd hD f 0 u z)

/-- The reduced energy is the full energy on the harmonic lift. -/
theorem harmonic_energy (u : U) :
    blockForm A D C (u, -exterior D C d hd hD u)
      (u, -exterior D C d hd hD u) = reduced A D C d hd hD u u := by
  simp only [blockForm_apply, map_neg, neg_apply, neg_neg,
    exterior_solves, reduced_apply]
  ring

/-- Symmetry of the Schur form follows from symmetry of the two diagonal forms. -/
theorem reduced_symmetric (hA : ∀ u v, A u v = A v u)
    (hDs : ∀ z w, D z w = D w z) (u v : U) :
    reduced A D C d hd hD u v = reduced A D C d hd hD v u := by
  rw [reduced_apply, reduced_apply, hA]
  congr 1
  rw [← exterior_solves D C d hd hD v, ← exterior_solves D C d hd hD u]
  exact hDs _ _

/-- Completing the square takes place entirely inside the exterior form domain. -/
theorem complete_square (hDs : ∀ z w, D z w = D w z) (u : U) (z : W) :
    blockForm A D C (u, z) (u, z) = reduced A D C d hd hD u u +
      D (z + exterior D C d hd hD u) (z + exterior D C d hd hD u) := by
  simp only [blockForm_apply, reduced_apply, map_add, add_apply]
  rw [exterior_solves, exterior_solves,
    hDs z (exterior D C d hd hD u), exterior_solves]
  ring

/-- Harmonic extension minimizes the full energy for a fixed first component. -/
theorem reduced_le_block (hDs : ∀ z w, D z w = D w z) (u : U) (z : W) :
    reduced A D C d hd hD u u ≤ blockForm A D C (u, z) (u, z) := by
  rw [complete_square A D C d hd hD hDs]
  exact le_add_of_nonneg_right ((mul_nonneg hd.le (sq_nonneg _)).trans (hD _))

/-- Coercive compression in form norms. Its hypothesis is a lower bound on the full
block form, not a bound assumed for the desired Schur complement. -/
theorem reduced_coercive (a : ℝ) (ha : 0 ≤ a)
    (hfull : ∀ u z, a * (‖u‖ ^ 2 + ‖z‖ ^ 2) ≤ blockForm A D C (u, z) (u, z))
    (u : U) : a * ‖u‖ ^ 2 ≤ reduced A D C d hd hD u u := by
  have h := hfull u (-exterior D C d hd hD u)
  rw [harmonic_energy] at h
  exact (by nlinarith [mul_nonneg ha (sq_nonneg ‖-exterior D C d hd hD u‖)] :
    a * ‖u‖ ^ 2 ≤ a * (‖u‖ ^ 2 + ‖-exterior D C d hd hD u‖ ^ 2)).trans h

include d hd hD in
/-- Unique solvability of the full system follows from coercivity and elimination.
This includes the zero exterior space. -/
theorem block_existsUnique [CompleteSpace U] (a : ℝ) (ha : 0 < a)
    (hfull : ∀ u z, a * (‖u‖ ^ 2 + ‖z‖ ^ 2) ≤ blockForm A D C (u, z) (u, z))
    (f : StrongDual ℝ U) (g : StrongDual ℝ W) :
    ∃! p : U × W, ∀ q : U × W, blockForm A D C p q = f q.1 + g q.2 := by
  let S := reduced A D C d hd hD
  have hS : ∀ u, a * ‖u‖ ^ 2 ≤ S u u := reduced_coercive A D C d hd hD a ha.le hfull
  let b := f - C.flip (CoerciveSolution.inverse D d hd hD g)
  let u := CoerciveSolution.inverse S a ha hS b
  let z := CoerciveSolution.inverse D d hd hD g - exterior D C d hd hD u
  have hu : ∀ v, S u v = b v := CoerciveSolution.inverse_solves S a ha hS b
  refine ⟨(u, z), ?_, ?_⟩
  · exact (block_equation_iff A D C f g u z).mpr
      ((eliminate_iff A D C d hd hD f g u z).mpr ⟨rfl, hu⟩)
  · rintro ⟨v, w⟩ hvw
    have h := (eliminate_iff A D C d hd hD f g v w).mp
      ((block_equation_iff A D C f g v w).mp hvw)
    have hv : v = u := CoerciveSolution.inverse_unique S a ha hS b v h.2
    exact Prod.ext hv (by simpa only [hv] using h.1)

end Elimination

section Ambient

variable {U W H K : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
  (JU : U →L[ℝ] H) (JW : W →L[ℝ] K) (T : H →L[ℝ] K)
  (D : W →L[ℝ] W →L[ℝ] ℝ) (d : ℝ) (hd : 0 < d)
  (hD : ∀ w, d * ‖w‖ ^ 2 ≤ D w w)

/-- Coupling induced by an ambient bounded operator. Scalar differential operators
remain in the two diagonal forms. -/
def coupling : U →L[ℝ] W →L[ℝ] ℝ :=
  (CoerciveSolution.forcing JW).comp (T.comp JU)

omit [CompleteSpace W] [CompleteSpace H] [CompleteSpace K] in
theorem coupling_apply (u : U) (w : W) :
    coupling JU JW T u w = inner ℝ (T (JU u)) (JW w) := rfl

/-- Bounded Schur correction on the ambient first space, using the full-domain
exterior solution. -/
def correction : H →L[ℝ] H :=
  T.adjoint.comp (JW.comp ((CoerciveSolution.solution D d hd hD JW).comp T))

theorem correction_pair (h k : H) :
    inner ℝ (correction JW T D d hd hD h) k =
      inner ℝ (JW (CoerciveSolution.solution D d hd hD JW (T h))) (T k) :=
  T.adjoint_inner_left _ _

/-- The form Schur correction is represented by the bounded ambient correction. -/
theorem reduced_eq_ambient (A : U →L[ℝ] U →L[ℝ] ℝ) (u v : U) :
    reduced A D (coupling JU JW T) d hd hD u v =
      A u v - inner ℝ (correction JW T D d hd hD (JU u)) (JU v) := by
  rw [reduced_apply, correction_pair, real_inner_comm]
  rfl

omit [CompleteSpace H] [CompleteSpace K] in
/-- Coercivity also gives an exterior response estimate in the full form norm. -/
theorem exterior_norm_le (u : U) :
    ‖exterior D (coupling JU JW T) d hd hD u‖ ≤
      d⁻¹ * ‖CoerciveSolution.forcing JW (T (JU u))‖ :=
  CoerciveSolution.inverse_norm_le D d hd hD _

/-- Positivity of the correction requires no ambient boundedness of a diagonal generator. -/
theorem correction_nonneg (h : H) :
    0 ≤ inner ℝ (correction JW T D d hd hD h) h := by
  rw [correction_pair, real_inner_comm, ← CoerciveSolution.solution_solves D d hd hD JW]
  exact (mul_nonneg hd.le (sq_nonneg _)).trans (hD _)

/-- Symmetry of the correction, expressed in ambient pairings. -/
theorem correction_symmetric (hDs : ∀ z w, D z w = D w z) (h k : H) :
    inner ℝ (correction JW T D d hd hD h) k =
      inner ℝ h (correction JW T D d hd hD k) := by
  conv_rhs => rw [real_inner_comm]
  rw [correction_pair, correction_pair]
  conv_lhs => rw [real_inner_comm]
  conv_rhs => rw [real_inner_comm]
  rw [← CoerciveSolution.solution_solves D d hd hD JW,
    ← CoerciveSolution.solution_solves D d hd hD JW]
  exact hDs _ _

/-- Quantitative bound for the bounded correction from ambient exterior coercivity. -/
theorem correction_norm_le (b : ℝ) (hb : 0 < b)
    (hlower : ∀ w, b * ‖JW w‖ ^ 2 ≤ D w w) (h : H) :
    ‖correction JW T D d hd hD h‖ ≤ (‖T‖ ^ 2 * b⁻¹) * ‖h‖ := by
  calc
    ‖correction JW T D d hd hD h‖ ≤
        ‖T.adjoint‖ * ‖JW (CoerciveSolution.solution D d hd hD JW (T h))‖ :=
      T.adjoint.le_opNorm _
    _ ≤ ‖T‖ * (b⁻¹ * ‖T h‖) := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact mul_le_mul_of_nonneg_left
        (CoerciveSolution.solution_value_norm_le D d hd hD JW b hb hlower _) (norm_nonneg _)
    _ ≤ ‖T‖ * (b⁻¹ * (‖T‖ * ‖h‖)) := by
      gcongr
      exact T.le_opNorm h
    _ = (‖T‖ ^ 2 * b⁻¹) * ‖h‖ := by ring

theorem correction_opNorm_le (b : ℝ) (hb : 0 < b)
    (hlower : ∀ w, b * ‖JW w‖ ^ 2 ≤ D w w) :
    ‖correction JW T D d hd hD‖ ≤ ‖T‖ ^ 2 * b⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (sq_nonneg _) (inv_nonneg.mpr hb.le))
    (correction_norm_le JW T D d hd hD b hb hlower)

omit [CompleteSpace H] [CompleteSpace K] in
/-- Ambient coercivity is inherited by harmonic compression, in addition to any
form-norm coercivity needed to construct the inverse. -/
theorem reduced_mass_bound (A : U →L[ℝ] U →L[ℝ] ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hfull : ∀ u z, a * (‖JU u‖ ^ 2 + ‖JW z‖ ^ 2) ≤
      blockForm A D (coupling JU JW T) (u, z) (u, z)) (u : U) :
    a * ‖JU u‖ ^ 2 ≤ reduced A D (coupling JU JW T) d hd hD u u := by
  have h := hfull u (-exterior D (coupling JU JW T) d hd hD u)
  rw [harmonic_energy] at h
  have hn := mul_nonneg ha (sq_nonneg ‖JW (-exterior D (coupling JU JW T) d hd hD u)‖)
  nlinarith

end Ambient

section Domains

variable {V H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (J : V → H) (B : V → V → ℝ) (R : H →L[ℝ] H)

/-- A bounded ambient perturbation of a form. Its associated operator is defined
only on its variational domain, never extended by a default value. -/
def boundedPerturbation (u v : V) : ℝ := B u v + inner ℝ (R (J u)) (J v)

omit [CompleteSpace H] in
/-- Adding a bounded ambient operator preserves the entire operator domain.
In particular, `L + R` has domain `Dom L` in Subsection 4.3. -/
theorem boundedPerturbation_domain :
    Riesz1.Internal.formOperatorDomain J (boundedPerturbation J B R) =
      Riesz1.Internal.formOperatorDomain J B := by
  ext u
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f - R (J u), fun v => ?_⟩
    rw [inner_sub_left]
    have h := hf v
    change B u v + inner ℝ (R (J u)) (J v) = _ at h
    linarith
  · rintro ⟨f, hf⟩
    refine ⟨f + R (J u), fun v => ?_⟩
    simp only [boundedPerturbation, hf, inner_add_left]

/-- The perturbed operator is the sum of the original operator and the bounded
term on the original domain. -/
theorem boundedPerturbation_operator (hJ : DenseRange J)
    (u : Riesz1.Internal.formOperatorDomain J B) :
    Riesz1.Internal.formOperator J hJ (boundedPerturbation J B R)
      ⟨u.val, by rw [boundedPerturbation_domain]; exact u.property⟩ =
      Riesz1.Internal.formOperator J hJ B u + R (J u.val) := by
  apply (Riesz1.Internal.formOperator_eq_iff J hJ _ _ _).mpr
  intro v
  simp only [boundedPerturbation, inner_add_left,
    Riesz1.Internal.formOperator_spec J hJ B u v]

end Domains

section SchurDomain

variable {U W H K : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
  (JU : U →L[ℝ] H) (JW : W →L[ℝ] K) (T : H →L[ℝ] K)
  (A : U →L[ℝ] U →L[ℝ] ℝ) (D : W →L[ℝ] W →L[ℝ] ℝ)
  (d : ℝ) (hd : 0 < d) (hD : ∀ w, d * ‖w‖ ^ 2 ≤ D w w)

/-- Schur elimination preserves the entire diagonal operator domain, even when
that operator is unbounded. This is the domain part of Subsection 5.1. -/
theorem reduced_operatorDomain :
    Riesz1.Internal.formOperatorDomain JU
      (fun u v => reduced A D (coupling JU JW T) d hd hD u v) =
      Riesz1.Internal.formOperatorDomain JU (fun u v => A u v) := by
  have he : (fun u v => reduced A D (coupling JU JW T) d hd hD u v) =
      boundedPerturbation JU (fun u v => A u v) (-correction JW T D d hd hD) := by
    funext u v
    rw [reduced_eq_ambient]
    simp only [boundedPerturbation, neg_apply, inner_neg_left, sub_eq_add_neg]
  rw [he, boundedPerturbation_domain]

/-- Strong Schur equation on precisely the original diagonal operator domain. -/
theorem reduced_operator (hJ : DenseRange JU)
    (u : Riesz1.Internal.formOperatorDomain JU (fun u v => A u v)) :
    Riesz1.Internal.formOperator JU hJ
      (fun u v => reduced A D (coupling JU JW T) d hd hD u v)
      ⟨u.val, by rw [reduced_operatorDomain]; exact u.property⟩ =
      Riesz1.Internal.formOperator JU hJ (fun u v => A u v) u -
        correction JW T D d hd hD (JU u.val) := by
  apply (Riesz1.Internal.formOperator_eq_iff JU hJ _ _ _).mpr
  intro v
  rw [reduced_eq_ambient, inner_sub_left,
    Riesz1.Internal.formOperator_spec JU hJ (fun u v => A u v) u v]

end SchurDomain

section CommonScalarForm

variable {α ι : Type*} [MeasurableSpace α] {ρ : Measure α} [Fintype ι]
  (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q)

/-- Product inclusion of the existing finite Hilbert product of the scalar
form domains. It changes neither the scalar carrier nor its derivative metric. -/
def vectorValues : MatrixEnergy.Vector (ι := ι) Q hQ →L[ℝ] PiLp 2 (fun _ : ι => Lp ℝ 2 ρ) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => Lp ℝ 2 ρ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => MatrixEnergy.vectorValue Q hQ i))

omit [Fintype ι] in
theorem vectorValues_apply (u : MatrixEnergy.Vector (ι := ι) Q hQ) (i : ι) :
    vectorValues Q hQ u i = (MatrixEnergy.vectorEquiv Q hQ u i).val := rfl

/-- The sum of the common scalar energies, continuous in the full product form norm. -/
def vectorEnergy : MatrixEnergy.Vector (ι := ι) Q hQ →L[ℝ]
    MatrixEnergy.Vector (ι := ι) Q hQ →L[ℝ] ℝ :=
  ∑ i, (ScalarFormHilbert.energyForm Q hQ).bilinearComp (PiLp.proj 2 _ i) (PiLp.proj 2 _ i)

theorem vectorEnergy_apply (u v : MatrixEnergy.Vector (ι := ι) Q hQ) :
    vectorEnergy Q hQ u v = ∑ i, Q.2 (MatrixEnergy.vectorEquiv Q hQ u i)
      (MatrixEnergy.vectorEquiv Q hQ v i) := by
  simp only [vectorEnergy, sum_apply, ContinuousLinearMap.bilinearComp_apply,
    ScalarFormHilbert.energyForm_apply]
  rfl

/-- Exact mass-plus-energy identity on the finite product form domain. -/
theorem vector_norm_sq (u : MatrixEnergy.Vector (ι := ι) Q hQ) :
    ‖u‖ ^ 2 = ‖vectorValues Q hQ u‖ ^ 2 + vectorEnergy Q hQ u u := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, vectorEnergy_apply,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => ScalarFormHilbert.norm_sq Q hQ (u i)

theorem vectorEnergy_nonneg (u : MatrixEnergy.Vector (ι := ι) Q hQ) :
    0 ≤ vectorEnergy Q hQ u u := by
  rw [vectorEnergy_apply]
  exact Finset.sum_nonneg fun _ _ => hQ.2.2.1 _

/-- A bounded (possibly nonlocal) coefficient operator added to the componentwise
common scalar form. The resulting generator may still be unbounded. -/
def vectorForm (R : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ) →L[ℝ]
    PiLp 2 (fun _ : ι => Lp ℝ 2 ρ)) :
    MatrixEnergy.Vector (ι := ι) Q hQ →L[ℝ] MatrixEnergy.Vector (ι := ι) Q hQ →L[ℝ] ℝ :=
  vectorEnergy Q hQ + (CoerciveSolution.forcing (vectorValues Q hQ)).comp
    (R.comp (vectorValues Q hQ))

theorem vectorForm_apply (R : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ) →L[ℝ]
    PiLp 2 (fun _ : ι => Lp ℝ 2 ρ)) (u v : MatrixEnergy.Vector (ι := ι) Q hQ) :
    vectorForm Q hQ R u v = vectorEnergy Q hQ u v +
      inner ℝ (R (vectorValues Q hQ u)) (vectorValues Q hQ v) := rfl

/-- Ambient coefficient coercivity yields coercivity in the complete product form
norm. The diffusion coefficient remains exactly one. -/
theorem vectorForm_coercive (R : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ) →L[ℝ]
    PiLp 2 (fun _ : ι => Lp ℝ 2 ρ)) (a : ℝ)
    (hR : ∀ f, a * ‖f‖ ^ 2 ≤ inner ℝ (R f) f)
    (u : MatrixEnergy.Vector (ι := ι) Q hQ) :
    min 1 a * ‖u‖ ^ 2 ≤ vectorForm Q hQ R u u := by
  rw [vector_norm_sq Q hQ, vectorForm_apply]
  have h₁ := mul_le_mul_of_nonneg_right (min_le_left 1 a) (vectorEnergy_nonneg Q hQ u)
  have h₂ := mul_le_mul_of_nonneg_right (min_le_right 1 a)
    (sq_nonneg ‖vectorValues Q hQ u‖)
  nlinarith [hR (vectorValues Q hQ u)]

/-- Full-domain solution for bounded coercive coefficients over the scalar
form. This is the concrete finite product specialization of the coercive solution map. -/
def vectorSolution (R : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ) →L[ℝ]
    PiLp 2 (fun _ : ι => Lp ℝ 2 ρ)) (a : ℝ) (ha : 0 < a)
    (hR : ∀ f, a * ‖f‖ ^ 2 ≤ inner ℝ (R f) f) :
    PiLp 2 (fun _ : ι => Lp ℝ 2 ρ) →L[ℝ] MatrixEnergy.Vector (ι := ι) Q hQ :=
  CoerciveSolution.solution (vectorForm Q hQ R) (min 1 a) (lt_min zero_lt_one ha)
    (vectorForm_coercive Q hQ R a hR) (vectorValues Q hQ)

theorem vectorSolution_solves (R : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ) →L[ℝ]
    PiLp 2 (fun _ : ι => Lp ℝ 2 ρ)) (a : ℝ) (ha : 0 < a)
    (hR : ∀ f, a * ‖f‖ ^ 2 ≤ inner ℝ (R f) f)
    (f : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ)) (v : MatrixEnergy.Vector (ι := ι) Q hQ) :
    vectorForm Q hQ R (vectorSolution Q hQ R a ha hR f) v =
      inner ℝ f (vectorValues Q hQ v) :=
  CoerciveSolution.solution_solves _ _ _ _ _ f v

theorem vectorSolution_unique (R : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ) →L[ℝ]
    PiLp 2 (fun _ : ι => Lp ℝ 2 ρ)) (a : ℝ) (ha : 0 < a)
    (hR : ∀ f, a * ‖f‖ ^ 2 ≤ inner ℝ (R f) f)
    (f : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ)) (u : MatrixEnergy.Vector (ι := ι) Q hQ)
    (hu : ∀ v, vectorForm Q hQ R u v = inner ℝ f (vectorValues Q hQ v)) :
    u = vectorSolution Q hQ R a ha hR f := by
  unfold vectorSolution CoerciveSolution.solution
  simp only [ContinuousLinearMap.comp_apply]
  apply CoerciveSolution.inverse_unique
  exact hu

/-- Ambient mass bound for the finite-vector inverse. -/
theorem vectorSolution_value_norm_le (R : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ) →L[ℝ]
    PiLp 2 (fun _ : ι => Lp ℝ 2 ρ)) (a : ℝ) (ha : 0 < a)
    (hR : ∀ f, a * ‖f‖ ^ 2 ≤ inner ℝ (R f) f)
    (f : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ)) :
    ‖vectorValues Q hQ (vectorSolution Q hQ R a ha hR f)‖ ≤ a⁻¹ * ‖f‖ := by
  apply CoerciveSolution.solution_value_norm_le _ _ _ _ _ a ha
  intro u
  rw [vectorForm_apply]
  exact (hR _).trans (le_add_of_nonneg_left (vectorEnergy_nonneg Q hQ u))

/-- Testing on a single component recovers all scalar equations, with no change
of scalar domain. Conversely those equations imply the full vector weak equation. -/
theorem vector_equation_iff [DecidableEq ι]
    (R : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ) →L[ℝ] PiLp 2 (fun _ : ι => Lp ℝ 2 ρ))
    (u : MatrixEnergy.Vector (ι := ι) Q hQ) (f : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ)) :
    (∀ v, vectorForm Q hQ R u v = inner ℝ f (vectorValues Q hQ v)) ↔
      ∀ i (v : Q.1), Q.2 (MatrixEnergy.vectorEquiv Q hQ u i) v +
        inner ℝ (R (vectorValues Q hQ u) i) v.val = inner ℝ (f i) v.val := by
  constructor
  · intro h i v
    let w := (MatrixEnergy.vectorEquiv (ι := ι) Q hQ).symm (Pi.single i v)
    have hw : MatrixEnergy.vectorEquiv Q hQ w = Pi.single i v :=
      LinearEquiv.apply_symm_apply _ _
    have he := h w
    rw [vectorForm_apply, vectorEnergy_apply, PiLp.inner_apply, PiLp.inner_apply] at he
    simp only [vectorValues_apply, hw, Pi.single_apply, apply_ite, map_zero,
      Submodule.coe_zero, inner_zero_right, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] at he
    exact he
  · intro h v
    rw [vectorForm_apply, vectorEnergy_apply, PiLp.inner_apply, PiLp.inner_apply,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => h i (MatrixEnergy.vectorEquiv Q hQ v i)

/-- The complete vector operator domain is the product of the complete scalar
operator domains. Bounded nonlocal coefficients do not change this set. -/
theorem vectorForm_operatorDomain_iff [DecidableEq ι]
    (R : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ) →L[ℝ] PiLp 2 (fun _ : ι => Lp ℝ 2 ρ))
    (u : MatrixEnergy.Vector (ι := ι) Q hQ) :
    u ∈ Riesz1.Internal.formOperatorDomain (vectorValues Q hQ)
      (fun u v => vectorForm Q hQ R u v) ↔
      ∀ i, MatrixEnergy.vectorEquiv Q hQ u i ∈
        Riesz1.Internal.formOperatorDomain (fun v : Q.1 => v.val) (fun u v => Q.2 u v) := by
  constructor
  · rintro ⟨f, hf⟩ i
    have hi := (vector_equation_iff Q hQ R u f).mp hf i
    refine ⟨f i - R (vectorValues Q hQ u) i, fun v => ?_⟩
    rw [inner_sub_left]
    linarith [hi v]
  · intro hu
    choose f hf using hu
    let g := WithLp.toLp 2 (fun i => f i + R (vectorValues Q hQ u) i)
    refine ⟨g, (vector_equation_iff Q hQ R u g).mpr ?_⟩
    intro i v
    change Q.2 (MatrixEnergy.vectorEquiv Q hQ u i) v + _ =
      inner ℝ (f i + R (vectorValues Q hQ u) i) v.val
    have hfi : Q.2 (MatrixEnergy.vectorEquiv Q hQ u i) v = inner ℝ (f i) v.val := hf i v
    rw [hfi, inner_add_left]

end CommonScalarForm

section ScalarRows

variable {α ι : Type*} [MeasurableSpace α] {ρ : Measure α} [Fintype ι]
  (Q : ScalarFormData ρ)

/-- Finite sums of weak generator equations stay on the same scalar form
domain. No derivative or generator is applied to a matrix coefficient. -/
theorem row_sum_weak (u : ι → Q.1) (f : ι → Lp ℝ 2 ρ)
    (hu : ∀ i v, Q.2 (u i) v = inner ℝ (f i) v.val) (v : Q.1) :
    Q.2 (∑ i, u i) v = inner ℝ (∑ i, f i) v.val := by
  simp only [map_sum, LinearMap.sum_apply, sum_inner, hu]

/-- Fixed finite linear combinations, including normalized constant rows, preserve
the weak generator equation. -/
theorem weighted_row_weak (c : ι → ℝ) (u : ι → Q.1) (f : ι → Lp ℝ 2 ρ)
    (hu : ∀ i v, Q.2 (u i) v = inner ℝ (f i) v.val) (v : Q.1) :
    Q.2 (∑ i, c i • u i) v = inner ℝ (∑ i, c i • f i) v.val := by
  apply row_sum_weak Q (fun i => c i • u i) (fun i => c i • f i)
  intro i w
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, real_inner_smul_left, hu]

/-- Every row sum belongs to the full scalar generator domain. -/
theorem row_sum_mem_domain (u : ι → Q.1) (f : ι → Lp ℝ 2 ρ)
    (hu : ∀ i v, Q.2 (u i) v = inner ℝ (f i) v.val) :
    (∑ i, u i) ∈ Riesz1.Internal.formOperatorDomain (fun v : Q.1 => v.val)
      (fun u v => Q.2 u v) :=
  ⟨∑ i, f i, row_sum_weak Q u f hu⟩

/-- The scalar generator commutes with finite row sums on its domain. -/
theorem generator_row_sum (hQ : IsClosedScalarDirichletForm Q)
    (u : ι → Q.1) (f : ι → Lp ℝ 2 ρ)
    (hu : ∀ i v, Q.2 (u i) v = inner ℝ (f i) v.val) :
    Riesz1.Internal.formOperator (fun v : Q.1 => v.val) hQ.1 (fun u v => Q.2 u v)
      ⟨∑ i, u i, row_sum_mem_domain Q u f hu⟩ = ∑ i, f i :=
  (Riesz1.Internal.formOperator_eq_iff _ hQ.1 _ _ _).mpr (row_sum_weak Q u f hu)

omit [Fintype ι] in
/-- Component equations for a bounded coefficient operator identify the full scalar
generator representatives. This interface also accepts nonlocal bounded coefficients. -/
theorem component_mem_domain (u : ι → Q.1) (f p : ι → Lp ℝ 2 ρ)
    (hu : ∀ i v, Q.2 (u i) v + inner ℝ (p i) v.val = inner ℝ (f i) v.val) (i : ι) :
    u i ∈ Riesz1.Internal.formOperatorDomain (fun v : Q.1 => v.val)
      (fun u v => Q.2 u v) := by
  refine ⟨f i - p i, fun v => ?_⟩
  rw [inner_sub_left]
  linarith [hu i v]

/-- Summing `L uᵢ + pᵢ = fᵢ` yields `L (∑ uᵢ) = ∑ fᵢ - ∑ pᵢ`, with explicit
membership in the unbounded generator domain (Lemma 4.6). -/
theorem bounded_system_row_sum (u : ι → Q.1) (f p : ι → Lp ℝ 2 ρ)
    (hu : ∀ i v, Q.2 (u i) v + inner ℝ (p i) v.val = inner ℝ (f i) v.val) :
    ∀ v, Q.2 (∑ i, u i) v = inner ℝ ((∑ i, f i) - ∑ i, p i) v.val := by
  have h : ∀ i v, Q.2 (u i) v = inner ℝ (f i - p i) v.val := by
    intro i v
    rw [inner_sub_left]
    linarith [hu i v]
  simpa only [Finset.sum_sub_distrib] using row_sum_weak Q u (fun i => f i - p i) h

/-- Full operator-domain and row-sum statement for a vector weak equation over the
common scalar form, with the bounded coefficient term in its original order. -/
theorem vector_equation_row_sum [DecidableEq ι] (hQ : IsClosedScalarDirichletForm Q)
    (R : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ) →L[ℝ] PiLp 2 (fun _ : ι => Lp ℝ 2 ρ))
    (u : MatrixEnergy.Vector (ι := ι) Q hQ) (f : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ))
    (hu : ∀ v, vectorForm Q hQ R u v = inner ℝ f (vectorValues Q hQ v)) :
    ∃ hsum : (∑ i, MatrixEnergy.vectorEquiv Q hQ u i) ∈
      Riesz1.Internal.formOperatorDomain (fun v : Q.1 => v.val) (fun u v => Q.2 u v),
      Riesz1.Internal.formOperator (fun v : Q.1 => v.val) hQ.1 (fun u v => Q.2 u v)
        ⟨∑ i, MatrixEnergy.vectorEquiv Q hQ u i, hsum⟩ =
        (∑ i, f i) - ∑ i, R (vectorValues Q hQ u) i := by
  have he := bounded_system_row_sum Q (MatrixEnergy.vectorEquiv Q hQ u) f
    (R (vectorValues Q hQ u)) ((vector_equation_iff Q hQ R u f).mp hu)
  exact ⟨⟨_, he⟩, (Riesz1.Internal.formOperator_eq_iff _ hQ.1 _ _ _).mpr he⟩

end ScalarRows

end Riesz2.OperatorSchur

end
