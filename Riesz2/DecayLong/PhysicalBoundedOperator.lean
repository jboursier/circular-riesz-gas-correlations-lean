/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.PhysicalPerturbation
public import Riesz2.DecayLong.BoundedPerturbationOperatorPart2

/-!
# The bounded-input physical perturbation operator

The operator in Proposition 5.18 is the actual multiplication defect plus
its full exterior Schur correction, on L∞ vector fields with L¹ output.
The already constructed ambient periodized matrix supplies its active block.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.PhysicalPerturbation

open BoundedPerturbationOperator PhysicalCore ColumnSubtraction

/-- The multiplication defect in Proposition 5.18 and Lemma 5.17,
using the actual ambient periodized extension of the proper active matrix. -/
def properMultiplication (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (M : ℕ+) (hnM : (n : ℕ) ≤ (M : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ)
    (A : EuclideanSpace ℝ (Fin (n : ℕ)) → Matrix (Fin (M : ℕ)) (Fin (M : ℕ)) ℝ) :
    EuclideanSpace ℝ (Fin (n : ℕ)) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ :=
  fun x i k => hessianMatrix (fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
    β.val * ∑ j, θ.val ((n : ℝ)^(-ε)*y j) -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (y,z)).toReal)) x i k -
    β.val * A x (i.castLE hnM) (k.castLE hnM)

section Schur

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}
  (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
  (s : Riesz1.RieszExponent) (n M : ℕ+) (hnM : (n : ℕ) ≤ (M : ℕ))
  (hM : 2 ≤ (M : ℕ)) (K : ℕ) (β : ℝ)

local notation "Eidx" => Finset.univ.filter (fun a : Fin (M : ℕ) => (n : ℕ) ≤ Fin.val a)
local notation "col" => fun (i : Fin (n : ℕ)) (a : Eidx) =>
  2*referenceIntervalMatrix s M hM K (Fin.castLE hnM i) (Subtype.val a)

/-- The exterior Schur correction in Proposition 5.18, represented on the
whole active L² space. The adjoint records the paper's reversed
scalar pairing. -/
def properSchurOperator
    (R : PiLp 2 (fun _ : Eidx => Lp ℝ 2 ν) →L[ℝ]
      MatrixEnergy.Vector (ι := Eidx) Q hQ) :
    PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν) →L[ℝ]
      PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν) :=
  reduced col ((OperatorSchur.vectorValues Q hQ).comp R).adjoint β

/-- The Schur part used by Lemma 5.17 is exactly the
physical exterior tensor pairing in Proposition 5.18, including β². -/
theorem properSchurOperator_point
    (R : PiLp 2 (fun _ : Eidx => Lp ℝ 2 ν) →L[ℝ]
      MatrixEnergy.Vector (ι := Eidx) Q hQ)
    (φ ψ : Lp ℝ 2 ν) (j k : Fin (n : ℕ)) :
    inner ℝ (PiLp.single 2 j φ) (properSchurOperator (Q := Q) (hQ := hQ) (s := s) (n := n) (M := M)
      (hnM := hnM) (hM := hM) (K := K) (β := β) R
      (PiLp.single 2 k ψ)) =
      β^2 * inner ℝ (BoundarySchurBounds.tensor (col k) ψ)
        (OperatorSchur.vectorValues Q hQ (R (BoundarySchurBounds.tensor (col j) φ))) := by
  rw [properSchurOperator,inner_reduced_adjoint,coupling_single,coupling_single]
  rfl

end Schur

/-- On the physical chart the multiplication operator in Proposition 5.18
is precisely the previously used Hessian-minus-active-matrix defect. -/
theorem properMultiplication_chart (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ)
    (A : EuclideanSpace ℝ (Fin (n : ℕ)) → Matrix (Fin (M : ℕ)) (Fin (M : ℕ)) ℝ)
    (heq : ∀ x : AffineSimplex.chartDomain n ((n+m : ℕ)+1),
      A x.val = properMatrix β s n m M hM hnM K θ ε κ₀ x)
    (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1)) (j k : Fin (n : ℕ)) :
    properMultiplication β s n m M hnM θ ε A x.val j k =
      hessianMatrix (fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
        β.val * ∑ i, θ.val ((n : ℝ)^(-ε)*y i) -
          Real.log (∫ z : EuclideanSpace ℝ (Fin m),
            (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (y,z)).toReal)) x.val j k -
        β.val * properActive β s n m M hM hnM K θ ε κ₀ x j k := by
  simp only [properMultiplication,heq x,properMatrix_active]

section Operator

variable (β : InverseTemperature) (s : Riesz1.RieszExponent)
  (n : ℕ+) (m : ℕ) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
  (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε : ℝ)
  (ν : Measure (EuclideanSpace ℝ (Fin (n : ℕ)))) [IsFiniteMeasure ν]
  (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
  (A : EuclideanSpace ℝ (Fin (n : ℕ)) → Matrix (Fin (M : ℕ)) (Fin (M : ℕ)) ℝ)

local notation "Y" => properMultiplication β s n m M hnM θ ε A
local notation "Eidx" => Finset.univ.filter (fun a : Fin (M : ℕ) => (n : ℕ) ≤ Fin.val a)

/-- The actual bounded-input operator `tM` of Proposition 5.18, on its whole
L∞ carrier with L¹ output. Coefficient integrability is proved before the
map is constructed. The full exterior resolvent is retained. -/
def properBoundedOperator (hY : ∀ j k, Integrable (fun x => Y x j k) ν)
    (R : PiLp 2 (fun _ : Eidx => Lp ℝ 2 ν) →L[ℝ]
      MatrixEnergy.Vector (ι := Eidx) Q hQ) :
    Lp (EuclideanSpace ℝ (Fin (n : ℕ))) ∞ ν →ₗ[ℝ]
      Lp (EuclideanSpace ℝ (Fin (n : ℕ))) 1 ν :=
  operator Y hY (properSchurOperator (Q := Q) (hQ := hQ) (s := s) (n := n) (M := M)
    (hnM := hnM) (hM := hM) (K := K) (β := β.val) R)

/-- The bounded-input map of Proposition 5.18 has exactly the original
multiplication-plus-Schur scalar pairing used in Lemma 5.17. -/
theorem properBoundedOperator_point (hY : ∀ j k, Integrable (fun x => Y x j k) ν)
    (R : PiLp 2 (fun _ : Eidx => Lp ℝ 2 ν) →L[ℝ]
      MatrixEnergy.Vector (ι := Eidx) Q hQ)
    (φ ψ : Lp ℝ ∞ ν) (j k : Fin (n : ℕ)) :
    pairing (injection ∞ j φ) (properBoundedOperator (β := β) (s := s) (n := n) (m := m) (M := M)
      (hM := hM) (hnM := hnM) (K := K) (θ := θ) (ε := ε) (ν := ν)
      (Q := Q) (hQ := hQ) (A := A) hY R
      (injection ∞ k ψ)) =
      (∫ x, φ x * Y x j k * ψ x ∂ν) + β.val^2 *
        inner ℝ (BoundarySchurBounds.tensor
          (fun a : Eidx => 2*referenceIntervalMatrix s M hM K (k.castLE hnM) a.val) (toL2 ψ))
          (OperatorSchur.vectorValues Q hQ (R (BoundarySchurBounds.tensor
            (fun a : Eidx => 2*referenceIntervalMatrix s M hM K (j.castLE hnM) a.val) (toL2 φ)))) := by
  rw [properBoundedOperator,pairing_operator_injections,properSchurOperator_point]

/-- Apply Lemma 5.17 to the actual whole-carrier
physical operator of Proposition 5.18. This internal implication consumes the
original tested operator bounds and the auxiliary value and mean estimates.
No physical equation or form-domain restriction is imposed on the test. -/
theorem proper_column_subtraction_internal [IsProbabilityMeasure ν]
    (hY : ∀ j k, Integrable (fun x => Y x j k) ν)
    (R : PiLp 2 (fun _ : Eidx => Lp ℝ 2 ν) →L[ℝ]
      MatrixEnergy.Vector (ι := Eidx) Q hQ)
    (hn : 2 ≤ (n : ℕ)) (A₀ D a d c δ : ℝ)
    (hA₀ : 0 ≤ A₀) (hD : 0 ≤ D) (hc : 0 < c) (hδ : 0 < δ)
    (hOp : OperatorBounds s n (A₀*(n : ℝ)^a) c δ
      (properBoundedOperator (β := β) (s := s) (n := n) (m := m) (M := M)
        (hM := hM) (hnM := hnM) (K := K) (θ := θ) (ε := ε) (ν := ν)
        (Q := Q) (hQ := hQ) (A := A) hY R))
    (i₀ : Fin (n : ℕ))
    (hdepth : (n : ℝ)/4 ≤ ((min (i₀.val+1) ((n : ℕ)-i₀.val) : ℕ) : ℝ))
    (v : Fin (n : ℕ) → BoundedL2Pairings.boundedSubmodule ν)
    (hvalue : ∀ k, ‖(v k).val‖ ≤
      D*(n : ℝ)^d*(1+(Nat.dist k.val i₀.val : ℝ))^(-(2-s.val)))
    (hsum : ‖∑ k, (v k).val‖ ≤ D*(n : ℝ)^d*(n : ℝ)^(-(1-s.val))) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : Fin (n : ℕ) → BoundedL2Pairings.boundedSubmodule ν,
      |pairing (field u) (properBoundedOperator (β := β) (s := s) (n := n) (m := m)
        (M := M) (hM := hM) (hnM := hnM) (K := K) (θ := θ) (ε := ε) (ν := ν)
        (Q := Q) (hQ := hQ) (A := A) hY R (field v))| ≤
        C*(n : ℝ)^(a+d)*(n : ℝ)^(-(1/2 : ℝ))*
          ‖WithLp.toLp 2 (fun i => (u i).val)‖ +
        C*Real.exp (-(c/2)*(n : ℝ)^δ)*‖field u‖*‖field v‖ := by
  obtain ⟨C,hC,hbound⟩ := column_subtraction_pairing s n hn A₀ D a d c δ hA₀ hD hc hδ
    (properBoundedOperator (β := β) (s := s) (n := n) (m := m) (M := M)
      (hM := hM) (hnM := hnM) (K := K) (θ := θ) (ε := ε) (ν := ν)
      (Q := Q) (hQ := hQ) (A := A) hY R) hOp i₀ hdepth (field v)
    (by simpa only [coordinate_field,toL2_ofBoundedScalar] using hvalue)
    (by simpa only [toL2_coordinateSum_field] using hsum)
  refine ⟨C,hC,fun u => ?_⟩
  have hh := hbound (field u)
  rw [← source_norm,source_field] at hh
  exact hh

end Operator

end Riesz2.PhysicalPerturbation
