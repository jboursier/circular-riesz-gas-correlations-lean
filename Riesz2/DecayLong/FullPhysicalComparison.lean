/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.PhysicalIdentityPart8

/-!
# The unrestricted full-cycle physical comparison

The equations (5.1) and (5.13) in the paper's Subsection 5.1
use the entire intrinsic scalar Sobolev product. This module retains that
domain in their subtraction and in equation (5.15).
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical ContDiff

namespace Riesz2.PhysicalIdentity

namespace Internal

/-- The full-product equations and energy comparison of Subsection 5.1,
equation (5.15). Every test belongs to the entire scalar Sobolev product. -/
def UnrestrictedComparison {α : Type*} [MeasurableSpace α] {ρ : Measure α}
    (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q) (N : ℕ+)
    (H B : MatrixEnergy.Vector (ι := Fin (N : ℕ)) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := Fin (N : ℕ)) Q hQ →L[ℝ] ℝ) (β a : ℝ) : Prop :=
  let E := OperatorSchur.vectorEnergy (ι := Fin (N : ℕ)) Q hQ
  let A := E + H
  let S := E + β • B
  let T := H - β • B
  let J := OperatorSchur.vectorValues (ι := Fin (N : ℕ)) Q hQ
  A = S + T ∧
    (∀ f : PiLp 2 (fun _ : Fin (N : ℕ) => Lp ℝ 2 ρ),
      (∃! v, ∀ z, S v z = inner ℝ f (J z)) ∧
      (∃! ψ, ∀ z, A ψ z = inner ℝ f (J z))) ∧
    ∀ (f : PiLp 2 (fun _ : Fin (N : ℕ) => Lp ℝ 2 ρ)) (v ψ),
      (∀ z, S v z = inner ℝ f (J z)) →
      (∀ z, A ψ z = inner ℝ f (J z)) →
      (∀ z, A (v - ψ) z = T v z) ∧
        β * a * ‖J (v - ψ)‖ ^ 2 ≤ H (v - ψ) (v - ψ) ∧
        H (v - ψ) (v - ψ) ≤ T v (v - ψ) ∧
        β * a * ‖J (v - ψ)‖ ^ 2 + E (v - ψ) (v - ψ) ≤ T v (v - ψ)

/-- Internal assembly for Subsection 5.1: coercivity on the whole
product, followed by same-source subtraction and testing by the difference. -/
theorem unrestricted_comparison {α : Type*} [MeasurableSpace α] {ρ : Measure α}
    (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q) (N : ℕ+)
    (M C : α → Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (H B : MatrixEnergy.Vector (ι := Fin (N : ℕ)) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := Fin (N : ℕ)) Q hQ →L[ℝ] ℝ)
    (hH : MatrixPairing Q hQ N M H) (hB : MatrixPairing Q hQ N C B)
    (β a b : ℝ) (hβ : 0 < β) (ha : 0 < a) (hb : 0 < b)
    (hl : ∀ᵐ x ∂ρ, ∀ t : Fin (N : ℕ) → ℝ,
      β * a * (∑ i, t i ^ 2) ≤ ∑ i, ∑ j, t i * M x i j * t j)
    (hc : ∀ᵐ x ∂ρ, ∀ t : Fin (N : ℕ) → ℝ,
      b * (∑ i, t i ^ 2) ≤ ∑ i, ∑ j, t i * C x i j * t j) :
    UnrestrictedComparison Q hQ N H B β a := by
  let E := OperatorSchur.vectorEnergy (ι := Fin (N : ℕ)) Q hQ
  let A := E + H
  let S := E + β • B
  let T := H - β • B
  let J := OperatorSchur.vectorValues (ι := Fin (N : ℕ)) Q hQ
  have hmass (u : MatrixEnergy.Vector (ι := Fin (N : ℕ)) Q hQ) :
      β * a * ‖J u‖ ^ 2 ≤ H u u := by
    have hh := matrix_pair_lower Q hQ M (β * a) hl u (hH u u).1
    rwa [← (hH u u).2] at hh
  have he (u : MatrixEnergy.Vector (ι := Fin (N : ℕ)) Q hQ) :
      β * a * ‖J u‖ ^ 2 + E u u ≤ A u u := by
    change _ ≤ E u u + H u u
    linarith only [hmass u]
  have heS (u : MatrixEnergy.Vector (ι := Fin (N : ℕ)) Q hQ) :
      (β * b) * ‖J u‖ ^ 2 + E u u ≤ S u u := by
    have hh := matrix_pair_lower Q hQ C b hc u (hB u u).1
    rw [← (hB u u).2] at hh
    have hh' := mul_le_mul_of_nonneg_left hh hβ.le
    change _ ≤ E u u + β * B u u
    nlinarith only [hh']
  have hid : A = S + T := by
    ext u v
    change E u v + H u v = (E u v + β * B u v) + (H u v - β * B u v)
    ring
  refine ⟨hid, ?_, ?_⟩
  · intro f
    constructor
    · simpa only [CoerciveSolution.forcing_apply] using
        CoerciveSolution.inverse_existsUnique S (min 1 (β * b))
          (lt_min zero_lt_one (mul_pos hβ hb))
          (graph_form_coercive Q hQ S (β * b) heS) (CoerciveSolution.forcing J f)
    · simpa only [CoerciveSolution.forcing_apply] using
        CoerciveSolution.inverse_existsUnique A (min 1 (β * a))
          (lt_min zero_lt_one (mul_pos hβ ha))
          (graph_form_coercive Q hQ A (β * a) he) (CoerciveSolution.forcing J f)
  · intro f v ψ hv hψ
    have heq := comparison_equation A S T hid (CoerciveSolution.forcing J f) v ψ hv hψ
    refine ⟨heq, hmass (v - ψ), ?_, ?_⟩
    · have hh := heq (v - ψ)
      have hn := OperatorSchur.vectorEnergy_nonneg Q hQ (v - ψ)
      change E (v - ψ) (v - ψ) + H (v - ψ) (v - ψ) = _ at hh
      linarith only [hh, hn]
    · exact comparison_energy A S T hid (CoerciveSolution.forcing J f) v ψ hv hψ
        (fun u => β * a * ‖J u‖ ^ 2 + E u u) he

end Internal

/-- Subsection 5.1, equation (5.1), equation (5.13) and equation (5.15), for `n=N`:
the unrestricted physical and core equations have unique solutions for every
L² vector source, and their difference satisfies the physical equation with
the signed perturbation as source and the displayed Hessian energy bounds.
The Neumann realization, both matrix domains and all multiplication pairings
are those of the original intrinsic tilted gap law. -/
theorem full_unrestricted_comparison (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K : ℕ) (hK : 1 ≤ K) (hKN : K ≤ (N : ℕ) / 4)
    (θ : PhysicalCutoff) (ε κ₀ : ℝ) (hε : 0 ≤ ε) :
    let ρ := fullIntrinsicTiltedGapLaw (ofLong β s) N θ ε false
    let Y := fun z : gapTangentSpace N => WithLp.toLp 2 (fun i => 1 + z.val i)
    let C := fun z => PhysicalCore.fullMatrix s N hN K θ ε κ₀ (Y z)
    let a := min 1 (s.val * (s.val + 1)) * (N : ℝ) ^ (-(s.val + 2) * ε)
    0 < a ∧ ∃ U : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        U y.val = fullPhysicalPotentialValue (ofLong β s) N hN θ ε false y) ∧
      ∃ Q : ScalarFormData ρ, IsNeumannRealization (intrinsicGapDomain N) Q ∧
        ∃ hQ : IsClosedScalarDirichletForm Q,
          (∀ (W : Submodule ℝ (Fin (N : ℕ) → ℝ)) (u : Fin (N : ℕ) → Q.1),
            (WeightedFormDomain Q (fun z => hessianMatrix U (Y z)) W u ↔
              ∀ᵐ z ∂ρ, (fun i => (u i).val z) ∈ W) ∧
            (WeightedFormDomain Q C W u ↔ ∀ᵐ z ∂ρ, (fun i => (u i).val z) ∈ W)) ∧
          ∃ H B,
            Internal.MatrixPairing Q hQ N (fun z => hessianMatrix U (Y z)) H ∧
            Internal.MatrixPairing Q hQ N C B ∧
            Internal.MatrixPairing Q hQ N
              (fun z => hessianMatrix U (Y z) - β.val • C z) (H - β.val • B) ∧
            Internal.UnrestrictedComparison Q hQ N H B β.val a := by
  intro ρ Y C a
  obtain ⟨U, hU, hv, Q, hr, hQ, hd, H, hH⟩ := full_physical_form β s N hN θ ε
  have ha : 0 < a := (Internal.full_physical_lower β s N hN θ ε hε U hU hv).1
  obtain ⟨b, hb, hc⟩ := PhysicalCore.fullMatrix_lower β s N hN K hK hKN θ ε κ₀ hε
  obtain ⟨B, hB⟩ := Internal.full_core_form β s N hN K θ ε κ₀ Q hQ
  refine ⟨ha, U, hU, hv, Q, hr, hQ, ?_, H, B, hH, hB,
    Internal.signed_pairing Q hQ N _ C H B hH hB β.val, ?_⟩
  · exact fun W u => ⟨hd W u, Internal.domain_of_pairing Q hQ N C B hB W u⟩
  · exact Internal.unrestricted_comparison Q hQ N _ C H B hH hB β.val a b
      β.property ha hb (Internal.full_physical_lower_ae β s N hN θ ε hε U hU hv)
      (ae_of_all ρ (fun z t => hc (Y z) t))

end Riesz2.PhysicalIdentity
