/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.FixedLengthDecayPart3
public import Riesz2.DecayLong.BoundedPerturbationOperatorPart2

/-!
# The bounded-input fixed-length perturbation operator

The map in Lemma 6.4 acts on actual bounded vector fields with integrable output. Its
pairing is the existing native perturbation pair.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.FixedLengthDecay

open BoundedPerturbationOperator ColumnSubtraction

section Operator

variable (β : InverseTemperature) (s : Riesz1.RieszExponent)
  (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (m : ℕ+) (hm : 2 ≤ (m : ℕ))
  (hnm : (n : ℕ) ≤ (m : ℕ)) (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ (m : ℕ)/4)
  (θ : PhysicalCutoff) (ε η t : ℝ)
  (ν : Measure (AffineSimplex.chartDomain n ((n+d : ℕ)+1))) [IsFiniteMeasure ν]
  (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
  (P : AffineSimplex.chartDomain n ((n+d : ℕ)+1) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)

local notation "Y" => InterpolationMatrix.multiplicationPart β s n d e hde m hm hnm k θ ε η t P
local notation "R" => InterpolationMatrix.referenceResolvent ν Q hQ s β m hm k hk hkm n
local notation "Eidx" => InterpolationMatrix.exteriorIndices m n
local notation "col" => fun i : Fin (n : ℕ) =>
  InterpolationMatrix.referenceColumn s m hm k n (Fin.castLE hnm i)
local notation "Bnd" => BoundedL2Pairings.boundedSubmodule ν

/-- The full exterior Schur correction of Lemma 6.4, on the
entire active L² space rather than just on the physical form domain. -/
def fixedLengthSchurOperator :
    PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν) →L[ℝ]
      PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν) :=
  reduced col ((OperatorSchur.vectorValues Q hQ).comp R) β.val

/-- The whole bounded-input perturbation map in Lemma 6.4, with
integrable multiplication coefficients and the actual full resolvent. -/
def fixedLengthBoundedOperator (hY : ∀ i j, Integrable (fun x => Y x i j) ν) :
    Lp (EuclideanSpace ℝ (Fin (n : ℕ))) ∞ ν →ₗ[ℝ]
      Lp (EuclideanSpace ℝ (Fin (n : ℕ))) 1 ν :=
  operator Y hY (fixedLengthSchurOperator (β := β) (s := s) (n := n) (d := d) (m := m) (hm := hm)
    (hnm := hnm) (k := k) (hk := hk) (hkm := hkm) (ν := ν) (Q := Q) (hQ := hQ))

omit [IsFiniteMeasure ν] in
/-- The bounded-input Schur map used in Lemma 5.17
is exactly the native reference-resolvent point pairing of Lemma 6.4. -/
theorem fixedLengthSchurOperator_point (φ ψ : Lp ℝ 2 ν) (j i : Fin (n : ℕ)) :
    inner ℝ (PiLp.single 2 j φ)
      (fixedLengthSchurOperator (β := β) (s := s) (n := n) (d := d) (m := m) (hm := hm)
    (hnm := hnm) (k := k) (hk := hk) (hkm := hkm) (ν := ν) (Q := Q) (hQ := hQ) (PiLp.single 2 i ψ)) =
      InterpolationMatrix.schurPointPair ν Q hQ s β m hm k hk hkm n φ ψ
        (j.castLE hnm) (Fin.castLE hnm i) := by
  rw [fixedLengthSchurOperator,inner_reduced,coupling_single,coupling_single]
  rfl

/-- The scalar column of the whole operator in Lemma 6.4 is the
existing native multiplication-plus-Schur pairing, with no domain restriction. -/
theorem fixedLengthBoundedOperator_point (hY : ∀ i j, Integrable (fun x => Y x i j) ν)
    (φ ψ : Lp ℝ ∞ ν) (j i : Fin (n : ℕ)) :
    pairing (injection ∞ j φ) (fixedLengthBoundedOperator (β := β) (s := s) (n := n) (d := d) (e := e)
      (hde := hde) (m := m) (hm := hm) (hnm := hnm) (k := k) (hk := hk) (hkm := hkm)
      (θ := θ) (ε := ε) (η := η) (t := t) (ν := ν) (Q := Q) (hQ := hQ) (P := P) hY (injection ∞ i ψ)) =
      (∫ x, φ x * Y x j i * ψ x ∂ν) +
        InterpolationMatrix.schurPointPair ν Q hQ s β m hm k hk hkm n (toL2 φ) (toL2 ψ)
          (j.castLE hnm) (Fin.castLE hnm i) := by
  rw [fixedLengthBoundedOperator,pairing_operator_injections,fixedLengthSchurOperator_point]

/-- For Lemma 6.4, the expectation of the actual L∞ → L¹ map is
exactly the physical perturbation form defined in the code. Every
multiplication integral is justified before identifying the pairing. -/
theorem fixedLengthBoundedOperator_pairing (hY : ∀ i j, Integrable (fun x => Y x i j) ν)
    (u v : Fin (n : ℕ) → Bnd) :
    ∃ hint : Integrable (matrixFieldPair Y (fun i => (u i).val) (fun i => (v i).val)) ν,
      pairing (field u) (fixedLengthBoundedOperator (β := β) (s := s) (n := n) (d := d) (e := e)
        (hde := hde) (m := m) (hm := hm) (hnm := hnm) (k := k) (hk := hk) (hkm := hkm)
        (θ := θ) (ε := ε) (η := η) (t := t) (ν := ν) (Q := Q) (hQ := hQ) (P := P) hY (field v)) =
      InterpolationMatrix.perturbationPair β s n d e hde m hm hnm k hk hkm θ ε η t
        ν Q hQ P (fun i => (u i).val) (fun i => (v i).val) hint := by
  obtain ⟨hint,hexp⟩ := perturbation_column_expansion_internal β s n d e hde m hm hnm k hk hkm
    θ ε η t ν Q hQ P hY u v
  refine ⟨hint,?_⟩
  rw [hexp]
  change pairing (field u) (operator Y hY
    (fixedLengthSchurOperator (β := β) (s := s) (n := n) (d := d) (m := m) (hm := hm)
      (hnm := hnm) (k := k) (hk := hk) (hkm := hkm) (ν := ν) (Q := Q) (hQ := hQ)) (field v)) = _
  rw [pairing_operator_columns]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  unfold point
  rw [fixedLengthSchurOperator_point]

/-- The two tested estimates of Lemma 6.4 imply exactly the
operator hypotheses of Lemma 5.17 on actual L∞ fields.
Both scalar tests range over the entire bounded-L² carrier. -/
theorem fixedLength_operator_bounds_internal [IsProbabilityMeasure ν]
    (hY : ∀ i j, Integrable (fun x => Y x i j) ν) (A₀ c δ : ℝ)
    (hpoint : ∀ (φ ψ : Bnd) (j i : Fin (n : ℕ)),
      |(∫ x, φ.val x*Y x j i*ψ.val x ∂ν) +
        InterpolationMatrix.schurPointPair ν Q hQ s β m hm k hk hkm n φ.val ψ.val
          (j.castLE hnm) (i.castLE hnm)| ≤
      A₀ * InteractionDifferential.boundaryWeight s.val n j *
        InteractionDifferential.boundaryWeight s.val n i * ‖φ.val‖ * ‖ψ.val‖ +
      A₀*Real.exp (-c*(n : ℝ)^δ)*
        (eLpNorm (φ.val : _ → ℝ) ∞ ν).toReal*(eLpNorm (ψ.val : _ → ℝ) ∞ ν).toReal)
    (hinc : ∀ (φ ψ : Bnd) (j i l : Fin (n : ℕ)),
      |(∫ x, φ.val x*ψ.val x*(Y x j i-Y x j l) ∂ν) +
        InterpolationMatrix.schurIncrementPair ν Q hQ s β m hm k hk hkm n φ.val ψ.val
          (j.castLE hnm) (i.castLE hnm) (l.castLE hnm)| ≤
      A₀ * InteractionDifferential.boundaryWeight s.val n j * (Nat.dist i.val l.val : ℝ) *
        (min ((min (i.val+1) ((n : ℕ)-i.val) : ℕ) : ℝ)
          ((min (l.val+1) ((n : ℕ)-l.val) : ℕ) : ℝ))^(-1-s.val/2) * ‖φ.val‖ * ‖ψ.val‖ +
      A₀*Real.exp (-c*(n : ℝ)^δ)*
        (eLpNorm (φ.val : _ → ℝ) ∞ ν).toReal*(eLpNorm (ψ.val : _ → ℝ) ∞ ν).toReal) :
    OperatorBounds s n A₀ c δ
      (fixedLengthBoundedOperator (β := β) (s := s) (n := n) (d := d) (e := e)
        (hde := hde) (m := m) (hm := hm) (hnm := hnm) (k := k) (hk := hk) (hkm := hkm)
        (θ := θ) (ε := ε) (η := η) (t := t) (ν := ν) (Q := Q) (hQ := hQ) (P := P) hY) := by
  let S := fixedLengthSchurOperator (β := β) (s := s) (n := n) (d := d) (m := m) (hm := hm)
    (hnm := hnm) (k := k) (hk := hk) (hkm := hkm) (ν := ν) (Q := Q) (hQ := hQ)
  have he (φ ψ : Bnd) (j i : Fin (n : ℕ)) : point Y S φ ψ j i =
      (∫ x, φ.val x*Y x j i*ψ.val x ∂ν) +
        InterpolationMatrix.schurPointPair ν Q hQ s β m hm k hk hkm n φ.val ψ.val
          (j.castLE hnm) (i.castLE hnm) := by
    unfold point
    rw [show S = fixedLengthSchurOperator (β := β) (s := s) (n := n) (d := d) (m := m) (hm := hm)
      (hnm := hnm) (k := k) (hk := hk) (hkm := hkm) (ν := ν) (Q := Q) (hQ := hQ) from rfl,
      fixedLengthSchurOperator_point]
  apply operator_bounds_internal s n A₀ c δ Y hY S
  · intro φ ψ j i
    rw [he]
    have hh := hpoint φ ψ j i
    simp only [InteractionDifferential.boundaryWeight_long s.property.2] at hh
    convert hh using 1; ring
  · intro φ ψ j i l
    rw [he,he,perturbation_row_increment_internal β s n d e hde m hm hnm k hk hkm
      θ ε η t ν Q hQ P hY φ ψ j i l]
    have hh := hinc φ ψ j i l
    simp only [InteractionDifferential.boundaryWeight_long s.property.2] at hh
    convert hh using 1; ring

/-- The application of Lemma 5.17 in Lemma 6.4,
before absorbing exceptional polynomial factors. The original source
coefficient is retained explicitly, so constants can be chosen uniformly
before the source and the volume in the comparison theorem. -/
theorem fixedLength_column_subtraction_polynomial_internal [IsProbabilityMeasure ν]
    (hY : ∀ i j, Integrable (fun x => Y x i j) ν)
    (hn : 2 ≤ (n : ℕ)) (A₀ D c δ : ℝ) (hA₀ : 0 ≤ A₀) (hD : 0 ≤ D)
    (hOp : OperatorBounds s n A₀ c δ
      (fixedLengthBoundedOperator (β := β) (s := s) (n := n) (d := d) (e := e)
        (hde := hde) (m := m) (hm := hm) (hnm := hnm) (k := k) (hk := hk) (hkm := hkm)
        (θ := θ) (ε := ε) (η := η) (t := t) (ν := ν) (Q := Q) (hQ := hQ) (P := P) hY))
    (i₀ : Fin (n : ℕ))
    (hdepth : (n : ℝ)/4 ≤ ((min (i₀.val+1) ((n : ℕ)-i₀.val) : ℕ) : ℝ))
    (v : Fin (n : ℕ) → Bnd)
    (hvalue : ∀ i, ‖(v i).val‖ ≤ D*(1+(Nat.dist i.val i₀.val : ℝ))^(-(2-s.val)))
    (hsum : ‖∑ i, (v i).val‖ ≤ D*(n : ℝ)^(-(1-s.val)))
    (u : Fin (n : ℕ) → Bnd) :
    ∃ hint : Integrable (matrixFieldPair Y (fun i => (u i).val) (fun i => (v i).val)) ν,
      |InterpolationMatrix.perturbationPair β s n d e hde m hm hnm k hk hkm θ ε η t
        ν Q hQ P (fun i => (u i).val) (fun i => (v i).val) hint| ≤
      A₀*sourceConstant s*D*Real.sqrt (2/(1-s.val))*(n : ℝ)^(-(1/2 : ℝ))*
        ‖WithLp.toLp 2 (fun i => (u i).val)‖ +
      3*A₀*(n : ℝ)^(5/2 : ℝ)*Real.exp (-c*(n : ℝ)^δ)*‖field u‖*‖field v‖ := by
  have hh := column_subtraction_pairing_polynomial s n hn A₀ c δ hA₀
    (fixedLengthBoundedOperator (β := β) (s := s) (n := n) (d := d) (e := e)
      (hde := hde) (m := m) (hm := hm) (hnm := hnm) (k := k) (hk := hk) (hkm := hkm)
      (θ := θ) (ε := ε) (η := η) (t := t) (ν := ν) (Q := Q) (hQ := hQ) (P := P) hY)
    hOp i₀ hdepth (field v) D hD
    (by simpa only [coordinate_field,toL2_ofBoundedScalar] using hvalue)
    (by simpa only [toL2_coordinateSum_field] using hsum) (field u)
  obtain ⟨hint,he⟩ := fixedLengthBoundedOperator_pairing (β := β) (s := s) (n := n)
    (d := d) (e := e) (hde := hde) (m := m) (hm := hm) (hnm := hnm) (k := k)
    (hk := hk) (hkm := hkm) (θ := θ) (ε := ε) (η := η) (t := t) (ν := ν)
    (Q := Q) (hQ := hQ) (P := P) hY u v
  refine ⟨hint,?_⟩
  rw [he,← source_norm,source_field] at hh
  exact hh

/-- Apply Lemma 5.17 to the whole bounded-input map
in Lemma 6.4, and identify its conclusion with the actual fixed-length
physical perturbation form. This internal implication takes only the two
original operator tests and the auxiliary value and mean estimates. -/
theorem fixedLength_column_subtraction_internal [IsProbabilityMeasure ν]
    (hY : ∀ i j, Integrable (fun x => Y x i j) ν)
    (hn : 2 ≤ (n : ℕ)) (A₀ D a d₀ c δ : ℝ)
    (hA₀ : 0 ≤ A₀) (hD : 0 ≤ D) (hc : 0 < c) (hδ : 0 < δ)
    (hOp : OperatorBounds s n (A₀*(n : ℝ)^a) c δ
      (fixedLengthBoundedOperator (β := β) (s := s) (n := n) (d := d) (e := e)
        (hde := hde) (m := m) (hm := hm) (hnm := hnm) (k := k) (hk := hk) (hkm := hkm)
        (θ := θ) (ε := ε) (η := η) (t := t) (ν := ν) (Q := Q) (hQ := hQ) (P := P) hY))
    (i₀ : Fin (n : ℕ))
    (hdepth : (n : ℝ)/4 ≤ ((min (i₀.val+1) ((n : ℕ)-i₀.val) : ℕ) : ℝ))
    (v : Fin (n : ℕ) → Bnd)
    (hvalue : ∀ i, ‖(v i).val‖ ≤
      D*(n : ℝ)^d₀*(1+(Nat.dist i.val i₀.val : ℝ))^(-(2-s.val)))
    (hsum : ‖∑ i, (v i).val‖ ≤ D*(n : ℝ)^d₀*(n : ℝ)^(-(1-s.val))) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : Fin (n : ℕ) → Bnd,
      ∃ hint : Integrable (matrixFieldPair Y (fun i => (u i).val) (fun i => (v i).val)) ν,
        |InterpolationMatrix.perturbationPair β s n d e hde m hm hnm k hk hkm θ ε η t
          ν Q hQ P (fun i => (u i).val) (fun i => (v i).val) hint| ≤
        C*(n : ℝ)^(a+d₀)*(n : ℝ)^(-(1/2 : ℝ))*
          ‖WithLp.toLp 2 (fun i => (u i).val)‖ +
        C*Real.exp (-(c/2)*(n : ℝ)^δ)*‖field u‖*‖field v‖ := by
  obtain ⟨C,hC,hbound⟩ := column_subtraction_pairing s n hn A₀ D a d₀ c δ hA₀ hD hc hδ
    (fixedLengthBoundedOperator (β := β) (s := s) (n := n) (d := d) (e := e)
      (hde := hde) (m := m) (hm := hm) (hnm := hnm) (k := k) (hk := hk) (hkm := hkm)
      (θ := θ) (ε := ε) (η := η) (t := t) (ν := ν) (Q := Q) (hQ := hQ) (P := P) hY)
    hOp i₀ hdepth (field v)
    (by simpa only [coordinate_field,toL2_ofBoundedScalar] using hvalue)
    (by simpa only [toL2_coordinateSum_field] using hsum)
  refine ⟨C,hC,fun u => ?_⟩
  obtain ⟨hint,he⟩ := fixedLengthBoundedOperator_pairing (β := β) (s := s) (n := n)
    (d := d) (e := e) (hde := hde) (m := m) (hm := hm) (hnm := hnm) (k := k)
    (hk := hk) (hkm := hkm) (θ := θ) (ε := ε) (η := η) (t := t) (ν := ν)
    (Q := Q) (hQ := hQ) (P := P) hY u v
  refine ⟨hint,?_⟩
  have hh := hbound (field u)
  rw [he,← source_norm,source_field] at hh
  exact hh

end Operator

end Riesz2.FixedLengthDecay
