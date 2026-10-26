/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.DerivativeControl

/-!
# Derivative estimate with the parent loss

The derivative estimate in the proof of Proposition 5.15, transferred
with the parent loss. The scalar form and reference cutoff are preserved.
-/

public section
noncomputable section
open MeasureTheory
open scoped BigOperators Matrix
namespace Riesz2.LocalizedMatrix.Analytic

/-- See the proof of Proposition 5.15 in the paper, derivative clause
(Lemma 5.11): uniform parent loss for the unchanged cutoff K. This internal
transfer interface takes the local structural matrix predicate. Construction
of that predicate belongs to the separate matrix-localization interface. -/
theorem derivative_transfer_internal (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (γ : ℝ) (hγ : 1 / 2 ≤ γ) (κstar γstar : ℝ) (hκstar : 0 < κstar) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (Cstar : ℝ), 1 ≤ Cstar →
    ∀ (βlo : ℝ), 0 < βlo → ∀ (βhi : ℝ), βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ), 0 < ε →
    ∀ {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
      (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q →
    ∀ (n n₀ m : ℕ+) (hm : 2 ≤ (m : ℕ)) (K : ℕ),
    2 ≤ (n : ℕ) → 2 ≤ (n₀ : ℕ) →
    ∀
      (M : X → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ),
    PeriodizedMatrixBounds (ν := ν) s n₀ m hm K Cstar κstar γstar
      (ε * Real.log n / Real.log n₀) M →
    ∀ (β : ℝ), βlo ≤ β → β ≤ βhi →
    ∀ (χ : Q.1) (i₀ : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents (Fin (m : ℕ)))
      (fun i => if i = i₀ then χ.val else 0) u →
    let t := γ / 2 + 1 / 4
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    let p := (1 - s.val / 2)⁻¹
    let V := fun x => (∑ i, |(rieszMatrix sh m hm *ᵥ
      (fun j => (u j).val x)) i| ^ p) ^ (1 / p)
    let Xρ := fun ρ => Real.sqrt (∑ i, (weightRadius m i i₀ ^ ρ * ‖(u i).val‖) ^ 2)
    ∃ lam : Lp ℝ 2 ν,
      (∀ᵐ x ∂ν, lam x = gapMultiplierField m Q (fun x => β • M x)
        (fun i => if i = i₀ then χ.val else 0) u x) ∧
      WeightedWeakSolution Q (fun x => β • M x) ⊤
        (fun i => (if i = i₀ then χ.val else 0) + lam) u ∧
      Integrable (fun x => V x ^ 2) ν ∧
      ∀ (η : ℝ), 0 < η → η < 1 / 4 →
        (∑ i, weightRadius m i i₀ ^ (2 * t) * Q.2 (u i) (u i)) ≤
          C * (n : ℝ) ^ (κ * ε) * (‖χ.val‖ ^ 2 + Xρ γ *
            (η ^ (3 - s.val) * Xρ (3 / 2 - s.val) +
              η⁻¹ * Real.sqrt (Real.log (2 * (m : ℝ))) *
                Real.sqrt (∫ x, V x ^ 2 ∂ν) + (m : ℝ) * ‖lam‖)) := by
  obtain ⟨κ, hκ, hb⟩ := DerivativeControl.diff hz s γ hγ κstar γstar hκstar
  refine ⟨κ, hκ, fun Cstar hCstar βlo hβlo βhi hβhi => ?_⟩
  obtain ⟨C, hC, hb⟩ := hb Cstar hCstar βlo hβlo βhi hβhi
  refine ⟨C, hC, ?_⟩
  intro ε hε X _ ν _ Q hQ n n₀ m hm K hn hn₀ M hM β hβloβ hββhi χ i₀ u hu
  let ε₀ := ε * Real.log n / Real.log n₀
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hn₀1 : (1 : ℝ) < n₀ := by exact_mod_cast hn₀
  have hlogn := Real.log_pos hn1
  have hlogn₀ := Real.log_pos hn₀1
  have hε₀ : 0 < ε₀ := div_pos (mul_pos hε hlogn) hlogn₀
  have he : (n₀ : ℝ) ^ (κ * ε₀) = (n : ℝ) ^ (κ * ε) := by
    apply Real.log_injOn_pos (Real.rpow_pos_of_pos (by positivity) _)
      (Real.rpow_pos_of_pos (by positivity) _)
    rw [Real.log_rpow (by positivity), Real.log_rpow (by positivity)]
    dsimp [ε₀]
    field_simp
  simpa only [he] using hb ε₀ hε₀ ν Q hQ n₀ m hm K M hM β hβloβ hββhi χ i₀ u hu

end Riesz2.LocalizedMatrix.Analytic
