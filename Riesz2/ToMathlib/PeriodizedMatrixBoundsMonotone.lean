/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.PeriodizedMatrixBounds
public import Mathlib.Tactic

/-!
# Increasing the losses in periodized matrix bounds

The interval representation and exact exterior blocks are retained.
-/

public section
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Riesz2.PeriodizedMatrixBoundsMonotone

/-- See Assumptions 5.3 of the paper: increasing positive prefactors and power
losses preserves every clause of the literal matrix predicate. -/
theorem of_losses_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Riesz1.RieszExponent) (n m : ℕ+) (hm : 2 ≤ (m : ℕ)) (K : ℕ)
    {C D κ κ' γ τ η ε : ℝ} (hC : 0 < C) (hCD : C ≤ D)
    (hκ : κ*η ≤ κ'*ε) (hγ : γ*η ≤ τ*ε)
    (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hM : PeriodizedMatrixBounds (ν := μ) s n m hm K C κ γ η M) :
    PeriodizedMatrixBounds (ν := μ) s n m hm K D κ' τ ε M := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hD : 0 < D := hC.trans_le hCD
  have hu : C*(n : ℝ)^(κ*η) ≤ D*(n : ℝ)^(κ'*ε) :=
    mul_le_mul hCD (Real.rpow_le_rpow_of_exponent_le hn hκ) (by positivity) hD.le
  have hl : D⁻¹*(n : ℝ)^(-κ'*ε) ≤ C⁻¹*(n : ℝ)^(-κ*η) :=
    mul_le_mul (inv_anti₀ hC hCD)
      (Real.rpow_le_rpow_of_exponent_le hn (by linarith)) (by positivity) (inv_pos.mpr hC).le
  have ht := Real.rpow_le_rpow_of_exponent_le hn hγ
  obtain ⟨hmeas, hmat, a, ha, hrep⟩ := hM
  refine ⟨hmeas, ?_, a, ha, ?_⟩
  · filter_upwards [hmat] with x hx
    refine ⟨hx.1, hx.2.1, fun z => ?_, fun i j hi hj => ?_⟩
    · exact (mul_le_mul_of_nonneg_right hl
        (Finset.sum_nonneg (fun i _ => sq_nonneg (z i)))).trans (hx.2.2.1 z)
    · exact (hx.2.2.2 i j hi hj).trans (mul_le_mul_of_nonneg_right hu (by positivity))
  · filter_upwards [hrep] with x hx
    refine ⟨fun i r => ⟨(hx.1 i r).1, ?_, ?_⟩, hx.2⟩
    · exact (hx.1 i r).2.1.trans (mul_le_mul_of_nonneg_right hu (by positivity))
    · intro hr
      exact (mul_le_mul_of_nonneg_right hl (by positivity)).trans ((hx.1 i r).2.2 (ht.trans hr))

end Riesz2.PeriodizedMatrixBoundsMonotone
