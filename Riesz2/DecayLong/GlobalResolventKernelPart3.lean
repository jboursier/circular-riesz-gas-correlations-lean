/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.GlobalResolventKernelPart2

/-!
# Quantitative periodization of global resolvent increments

See the proof of Lemma 5.13 in the paper: the exact coefficient reduction
from Part2 is combined with the power-tail estimate. The analytic
coefficient increment hypothesis appears only in an internal helper.
-/

public section
noncomputable section

open Matrix Set Filter
open scoped BigOperators Fin.NatCast Topology ContDiff

namespace Riesz2.GlobalResolventKernelInternal

/-- Internal quantitative reduction for the increment clause of the proof of Lemma 5.13. An inverse coefficient sequence with a
summable increment envelope gives the same envelope on every finite cycle.
The constant precedes the size and the matrix parameters. -/
theorem matrix_increment_bound_of_coefficients {q : ℝ} (hq : 1 < q) :
    ∃ T : ℝ, 0 < T ∧ ∀ (s : Riesz1.RieszExponent) (N : ℕ+)
      (hN : 2 ≤ (N : ℕ)) (a : ℝ) (ha : 0 < a) (B : ℝ)
      (φ : ℤ → ℂ) (hφ : Summable (fun n => ‖φ n‖)) (C : ℝ), 0 ≤ C →
      latticeFourier φ hφ 0 = 0 →
      (∀ (k : Fin (N : ℕ)) (hk : k ≠ 0),
        latticeFourier φ hφ (cycleAngle N k) =
          (((a + B ^ 2 / a) /
            (2 * latticeRieszSymbol s ⟨cycleAngle N k, cycleAngle_mem_Ioo N k hk⟩ +
              (a + B ^ 2 / a)) : ℝ) : ℂ)) →
      (∀ n : ℤ, ‖φ (n + 1) - φ n‖ ≤ C / (1 + |(n : ℝ)| ^ q)) →
      ∀ h : Fin (N : ℕ),
        |factorizationMatrix s N hN a ha B 0 (h + 1) -
          factorizationMatrix s N hN a ha B 0 h| ≤
            T * C * (1 + (Riesz1.cyclicIndexDistance N h 0 : ℝ)) ^ (-q) := by
  obtain ⟨T, hT, hb⟩ := inverse_power_sum hq
  refine ⟨T * 2 ^ q, by positivity, ?_⟩
  intro s N hN a ha B φ hφ C hC hzero hfreq hdiff h
  obtain ⟨hs, ht, _⟩ := hb N hN h.val
  rw [distance_nat] at ht
  let u := fun l : ℤ =>
    φ ((h.val : ℤ) + 1 + l * (N : ℕ)) - φ ((h.val : ℤ) + l * (N : ℕ))
  let v := fun l : ℤ => C *
    (1 / (1 + |(h.val : ℝ) + (l : ℝ) * (N : ℝ)| ^ q))
  have hv : Summable v := hs.mul_left C
  have hdom : ∀ l : ℤ, ‖u l‖ ≤ v l := by
    intro l
    have hh := hdiff ((h.val : ℤ) + l * (N : ℕ))
    dsimp only [u, v]
    rw [show (h.val : ℤ) + 1 + l * (N : ℕ) =
      (h.val : ℤ) + l * (N : ℕ) + 1 by ring]
    convert hh using 1
    push_cast
    ring
  have hu : Summable (fun l => ‖u l‖) := hv.of_nonneg_of_le
    (fun _ => norm_nonneg _) hdom
  have hnorm : ‖∑' l : ℤ, u l‖ ≤ C * T /
      (1 + (Riesz1.cyclicIndexDistance N h 0 : ℝ) ^ q) := by
    calc
      _ ≤ ∑' l : ℤ, ‖u l‖ := norm_tsum_le_tsum_norm hu
      _ ≤ ∑' l : ℤ, v l := Summable.tsum_le_tsum hdom hu hv
      _ = C * ∑' l : ℤ,
          1 / (1 + |(h.val : ℝ) + (l : ℝ) * (N : ℝ)| ^ q) := tsum_mul_left
      _ ≤ C * (T / (1 + (Riesz1.cyclicIndexDistance N h 0 : ℝ) ^ q)) :=
        mul_le_mul_of_nonneg_left ht hC
      _ = _ := by ring
  have he := kernel_increment_series s N hN a ha B φ hφ hzero hfreq h
  rw [← Real.norm_eq_abs, ← Complex.norm_real, he]
  change ‖∑' l : ℤ, u l‖ ≤ _
  have hd : 0 ≤ (Riesz1.cyclicIndexDistance N h 0 : ℝ) := Nat.cast_nonneg _
  have hen := power_envelope_compare (by linarith : 0 ≤ q) hd
  calc
    _ ≤ C * T / (1 + (Riesz1.cyclicIndexDistance N h 0 : ℝ) ^ q) := hnorm
    _ ≤ (C * T) * (2 ^ q *
        (1 + (Riesz1.cyclicIndexDistance N h 0 : ℝ)) ^ (-q)) := by
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left hen (mul_nonneg hC hT.le)
    _ = _ := by ring

end Riesz2.GlobalResolventKernelInternal
