/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.BoundedPerturbationOperator

/-!
# Applying column subtraction to the bounded-input operators

The scalar tested pairings of the physical and fixed-length operators are
identified with their actual L∞ → L¹ maps before column subtraction.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter
open scoped BigOperators ENNReal Classical

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.BoundedPerturbationOperator

open ColumnSubtraction

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} {n : ℕ}

/-- The tested scalar column of the multiplication-plus-Schur operator
in Lemma 5.17, on the existing bounded physical carrier. -/
def point (Y : X → Matrix (Fin n) (Fin n) ℝ)
    (S : PiLp 2 (fun _ : Fin n => Lp ℝ 2 ν) →L[ℝ]
      PiLp 2 (fun _ : Fin n => Lp ℝ 2 ν))
    (φ ψ : BoundedL2Pairings.boundedSubmodule ν) (i k : Fin n) : ℝ :=
  (∫ x, φ.val x * Y x i k * ψ.val x ∂ν) +
    inner ℝ (PiLp.single 2 i φ.val) (S (PiLp.single 2 k ψ.val))

/-- The complete expectation in Lemma 5.17 is the
finite sum of its native scalar column pairings. -/
theorem pairing_operator_columns [IsFiniteMeasure ν]
    (Y : X → Matrix (Fin n) (Fin n) ℝ)
    (hY : ∀ i k, Integrable (fun x => Y x i k) ν)
    (S : PiLp 2 (fun _ : Fin n => Lp ℝ 2 ν) →L[ℝ]
      PiLp 2 (fun _ : Fin n => Lp ℝ 2 ν))
    (u v : Fin n → BoundedL2Pairings.boundedSubmodule ν) :
    pairing (field u) (operator Y hY S (field v)) = ∑ i, ∑ k, point Y S (u i) (v k) i k := by
  rw [pairing_operator_fields]
  have he (f : Fin n → BoundedL2Pairings.boundedSubmodule ν) :
      WithLp.toLp 2 (fun i => (f i).val) = ∑ i, PiLp.single 2 i (f i).val := by
    apply PiLp.ext
    intro i
    simp
  rw [he u,he v,map_sum,sum_inner]
  simp only [inner_sum,point,Finset.sum_add_distrib]

/-- The tested actual operator in Lemma 5.17 agrees
with the native bounded-L² column pairing. -/
theorem point_infinity [IsFiniteMeasure ν]
    (Y : X → Matrix (Fin n) (Fin n) ℝ)
    (hY : ∀ i k, Integrable (fun x => Y x i k) ν)
    (S : PiLp 2 (fun _ : Fin n => Lp ℝ 2 ν) →L[ℝ]
      PiLp 2 (fun _ : Fin n => Lp ℝ 2 ν))
    (φ ψ : Lp ℝ ∞ ν) (i k : Fin n) :
    pairing (injection ∞ i φ) (operator Y hY S (injection ∞ k ψ)) =
      point Y S (boundedScalar φ) (boundedScalar ψ) i k := by
  rw [pairing_operator_injections]
  unfold point
  congr 1
  apply integral_congr_ae
  filter_upwards [inclusion_ae ∞ 2 (by simp) φ,
    inclusion_ae ∞ 2 (by simp) ψ] with x hφ hψ
  change φ x * Y x i k * ψ x =
    inclusion ∞ 2 (by simp) φ x * Y x i k * inclusion ∞ 2 (by simp) ψ x
  rw [hφ,hψ]

/-- Translate the two tested bounds of Lemma 5.17 from
the native scalar pairing to the actual bounded-input linear operator.
This is an internal adapter. Both premises are the original tested bounds. -/
theorem operator_bounds_internal [IsProbabilityMeasure ν]
    (s : Riesz1.RieszExponent) (n : ℕ+) (P c δ : ℝ)
    (Y : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (hY : ∀ i k, Integrable (fun x => Y x i k) ν)
    (S : PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν) →L[ℝ]
      PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν))
    (hpoint : ∀ (φ ψ : BoundedL2Pairings.boundedSubmodule ν) (i k : Fin (n : ℕ)),
      |point Y S φ ψ i k| ≤ P * ‖φ.val‖ * ‖ψ.val‖ *
        ((min (i.val+1) ((n : ℕ)-i.val) : ℕ) : ℝ)^(-s.val/2) *
        ((min (k.val+1) ((n : ℕ)-k.val) : ℕ) : ℝ)^(-s.val/2) +
        P * Real.exp (-c*(n : ℝ)^δ) *
          (eLpNorm (φ.val : X → ℝ) ∞ ν).toReal *
          (eLpNorm (ψ.val : X → ℝ) ∞ ν).toReal)
    (hinc : ∀ (φ ψ : BoundedL2Pairings.boundedSubmodule ν) (i k l : Fin (n : ℕ)),
      |point Y S φ ψ i k - point Y S φ ψ i l| ≤
        P * (Nat.dist k.val l.val : ℝ) * ‖φ.val‖ * ‖ψ.val‖ *
          ((min (i.val+1) ((n : ℕ)-i.val) : ℕ) : ℝ)^(-s.val/2) *
          (min (((min (k.val+1) ((n : ℕ)-k.val) : ℕ) : ℝ))
            (((min (l.val+1) ((n : ℕ)-l.val) : ℕ) : ℝ)))^(-1-s.val/2) +
        P * Real.exp (-c*(n : ℝ)^δ) *
          (eLpNorm (φ.val : X → ℝ) ∞ ν).toReal *
          (eLpNorm (ψ.val : X → ℝ) ∞ ν).toReal) :
    OperatorBounds s n P c δ (operator Y hY S) := by
  constructor
  · intro φ ψ i k
    rw [point_infinity]
    have hh := hpoint (boundedScalar φ) (boundedScalar ψ) i k
    rw [boundedScalar_essentialNorm,boundedScalar_essentialNorm] at hh
    simpa only [boundedScalar_val] using hh
  · intro φ ψ i k l
    rw [map_sub,map_sub,point_infinity,point_infinity]
    have hh := hinc (boundedScalar φ) (boundedScalar ψ) i k l
    rw [boundedScalar_essentialNorm,boundedScalar_essentialNorm] at hh
    simpa only [boundedScalar_val] using hh

end Riesz2.BoundedPerturbationOperator
