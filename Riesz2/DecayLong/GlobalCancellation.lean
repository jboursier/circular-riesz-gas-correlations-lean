/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.DerivativeCommutators
public import Riesz2.DecayLong.GlobalEndpointRegions
public import Riesz2.ToMathlib.FiniteSchurBounds
public import Riesz2.ToMathlib.PowerCommutatorBounds

/-!
# Global endpoint and fractional row cancellation

The cyclic weights use `weightRadius` of Subsection 5.4.
The endpoint estimate follows the four regions of Lemma 5.12.
The fractional row estimate uses the actual inverse of the sampled
Riesz matrix, including its constant Fourier mode.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Fin.NatCast Matrix ENNReal
open Finset

namespace Riesz2.GlobalCancellation

/-- Lemma 5.12: the full reciprocal-radius sum
is logarithmic, uniformly in its centre. -/
theorem sum_inverse_radius (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (i₀ : Fin (N : ℕ)) :
    (∑ i, (weightRadius N i i₀)⁻¹) ≤
      2 * (1 + 1 / Real.log 2) * Real.log (2 * (N : ℝ)) := by
  exact GlobalEndpointRegions.full_harmonic N hN i₀

/-- A stronger logarithmic endpoint bound. The normalized commutator kernel
is controlled by a reciprocal-distance kernel and a rank-one kernel. -/
theorem endpoint_logarithmic {p : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (i₀ : Fin (N : ℕ))
    (B : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ) {Bstar : ℝ} (hB : 0 ≤ Bstar)
    (hdec : ∀ i j, |B i j| ≤ Bstar * (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-p))
    (v : Fin (N : ℕ) → ℝ) :
    Real.sqrt (∑ i, (weightRadius N i i₀ ^ (p - 1 / 2) * (B *ᵥ v) i -
      (B *ᵥ (fun j => weightRadius N j i₀ ^ (p - 1 / 2) * v j)) i) ^ 2) ≤
      (8 * (1 + 1 / Real.log 2)) * Bstar * Real.log (2 * (N : ℝ)) *
        Real.sqrt (∑ j, (weightRadius N j i₀ ^ (1 / 2 : ℝ) * v j) ^ 2) := by
  classical
  let r := fun i => weightRadius N i i₀
  let D := fun i j => 1 + (Riesz1.cyclicIndexDistance N i j : ℝ)
  let K := fun i j => (r i ^ (p - 1 / 2) - r j ^ (p - 1 / 2)) * B i j / Real.sqrt (r j)
  let A := fun i j => (D i j)⁻¹
  let w := fun i => (Real.sqrt (r i))⁻¹
  let u := fun i => Real.sqrt (r i) * v i
  let H := 2 * (1 + 1 / Real.log 2) * Real.log (2 * (N : ℝ))
  have hr (i) : 0 < r i := by dsimp [r]; linarith [one_le_weightRadius N i i₀]
  have hD (i j) : 0 < D i j := by dsimp [D]; positivity
  have hH : 0 ≤ H := by
    dsimp [H]
    have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have : 0 < Real.log (2 * (N : ℝ)) := Real.log_pos (by linarith)
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hrow (i) : ∑ j, A i j ≤ H := by
    simpa only [A, D, weightRadius, cyclicIndexDistance_comm' N i] using sum_inverse_radius N hN i
  have hcol (j) : ∑ i, A i j ≤ H := by
    exact sum_inverse_radius N hN j
  have hwsq : ∑ i, w i ^ 2 ≤ H := by
    have heq (i) : w i ^ 2 = (r i)⁻¹ := by
      dsimp only [w]
      rw [inv_pow, Real.sq_sqrt (hr i).le]
    simp_rw [heq]
    exact sum_inverse_radius N hN i₀
  have hK (i j) : |K i j| ≤ 2 * Bstar * (A i j + w i * w j) := by
    have hd : |r i - r j| ≤ D i j :=
      (DerivativeCommutators.weightRadius_lipschitz N i₀ i j).trans (by dsimp [D]; linarith)
    have hscalar := PowerCommutatorBounds.scalar_kernel_bound hp hp2 (hr i) (hr j) (hD i j) hd
    calc
      |K i j| = |r i ^ (p - 1 / 2) - r j ^ (p - 1 / 2)| * |B i j| / Real.sqrt (r j) := by
        dsimp only [K]
        rw [abs_div, abs_mul, abs_of_pos (Real.sqrt_pos.mpr (hr j))]
      _ ≤ |r i ^ (p - 1 / 2) - r j ^ (p - 1 / 2)| * (Bstar * D i j ^ (-p)) / Real.sqrt (r j) := by
        gcongr
        exact hdec i j
      _ = Bstar * (|r i ^ (p - 1 / 2) - r j ^ (p - 1 / 2)| * D i j ^ (-p) / Real.sqrt (r j)) := by ring
      _ ≤ Bstar * (2 * ((D i j)⁻¹ + (Real.sqrt (r i))⁻¹ * (Real.sqrt (r j))⁻¹)) :=
        mul_le_mul_of_nonneg_left hscalar hB
      _ = _ := by dsimp only [A, w]; ring
  have h := PowerCommutatorBounds.sqrt_sum_sq_le_of_majorant K A w u hH hB
    (fun i j => inv_nonneg.mpr (hD i j).le)
    (fun i => inv_nonneg.mpr (Real.sqrt_nonneg _)) hrow hcol hwsq hK
  have heq (i) : (∑ j, K i j * u j) =
      r i ^ (p - 1 / 2) * (B *ᵥ v) i - (B *ᵥ (fun j => r j ^ (p - 1 / 2) * v j)) i := by
    simp only [Matrix.mulVec, dotProduct, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro j _
    dsimp only [K, u]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr (hr j))]
  simp_rw [heq] at h
  convert h using 1
  simp only [H, u, r, Real.sqrt_eq_rpow]
  ring

/-- Lemma 5.12, equation (5.41), with the literal quadratic cutoff remainder.
Here `p = 2 - s`. The matrix envelope is explicit. -/
theorem endpoint_by_regions (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (_hN : 2 ≤ (N : ℕ))
      (i₀ : Fin (N : ℕ)) (B : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
      (Bstar : ℝ), 0 < Bstar →
      (∀ i j, |B i j| ≤ Bstar * (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-p)) →
      ∀ R : ℝ, 1 ≤ R → ∀ v : Fin (N : ℕ) → ℝ,
      Real.sqrt (∑ i, (weightRadius N i i₀ ^ (p - 1 / 2) * (B *ᵥ v) i -
        (B *ᵥ (fun j => weightRadius N j i₀ ^ (p - 1 / 2) * v j)) i) ^ 2) ≤
        C * Bstar * R ^ (1 - p) *
          Real.sqrt (∑ j, (weightRadius N j i₀ ^ (p - 1 / 2) * v j) ^ 2) +
        C * Bstar * (R ^ 2 + Real.log (2 * (N : ℝ))) *
          Real.sqrt (∑ j, (weightRadius N j i₀ ^ (1 / 2 : ℝ) * v j) ^ 2) := by
  simpa only [GlobalEndpointRegions.norm₂_eq] using
    GlobalEndpointRegions.endpoint_estimate p hp hp2

/-- Lemma 5.12:
the endpoint commutator, with the polynomial remainder and a
constant uniform in the size, centre, matrix, cutoff radius and input vector. -/
theorem global_endpoint (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (_hN : 2 ≤ (N : ℕ))
      (i₀ : Fin (N : ℕ)) (B : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
      (Bstar : ℝ), 0 < Bstar →
      (∀ i j, |B i j| ≤ Bstar * (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-p)) →
      ∀ R : ℝ, 1 ≤ R → ∀ v : Fin (N : ℕ) → ℝ,
      Real.sqrt (∑ i, (weightRadius N i i₀ ^ (p - 1 / 2) * (B *ᵥ v) i -
        (B *ᵥ (fun j => weightRadius N j i₀ ^ (p - 1 / 2) * v j)) i) ^ 2) ≤
        C * Bstar * R ^ (1 - p) *
          Real.sqrt (∑ j, (weightRadius N j i₀ ^ (p - 1 / 2) * v j) ^ 2) +
        C * Bstar * (R ^ C + Real.log (2 * (N : ℝ))) *
          Real.sqrt (∑ j, (weightRadius N j i₀ ^ (1 / 2 : ℝ) * v j) ^ 2) := by
  obtain ⟨C, hC, hc⟩ := endpoint_by_regions p hp hp2
  refine ⟨max C 2, lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
  intro N hN i₀ B Bstar hB hdec R hR v
  refine (hc N hN i₀ B Bstar hB hdec R hR v).trans ?_
  have hlog : 0 ≤ Real.log (2 * (N : ℝ)) := by
    apply Real.log_nonneg
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hpow : R ^ 2 ≤ R ^ max C 2 := by
    rw [← Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hR (le_max_right _ _)
  gcongr
  · exact le_max_left _ _
  · exact le_max_left _ _

/-- Lemma 5.10: optimization of the inverse-row estimate.
The small and large optimal scales are clamped at `1` and the cycle size. -/
theorem inverse_row_optimized (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 0 < p.toReal) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (A₀ A₁ : ℝ) (v : Fin (N : ℕ) → ℝ), 0 ≤ A₀ → 0 ≤ A₁ →
      ‖WithLp.toLp p v‖ ≤ A₀ →
      ‖WithLp.toLp p (fun j => v (j - 1)) - WithLp.toLp p v‖ ≤ A₁ →
      ‖WithLp.toLp p (v ᵥ* (rieszMatrix s N hN)⁻¹)‖ ≤
        C * ((N : ℝ) ^ (s.val - 1) * A₀ + A₀ ^ s.val * A₁ ^ (1 - s.val)) := by
  exact DerivativeCommutators.inverse_row_optimized hz s hp

/-- See the proof of Lemma 5.13 in the paper: fractional cancellation of
an arbitrary row, with constants chosen before the size, row and its bounds.
The forward difference is literal, and both zero-bound cases are included. -/
theorem global_row_cancellation (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent) :
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    let b := 1 - s.val / 2
    let q := 2 / s.val
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (F : Fin (N : ℕ) → ℝ) (A₀ A₁ : ℝ), 0 ≤ A₀ → 0 ≤ A₁ →
      (∑ j, |F j| ^ q) ^ (1 / q) ≤ A₀ →
      (∑ j, |F (j + 1) - F j| ^ q) ^ (1 / q) ≤ A₁ →
      (∑ j, |(F ᵥ* (rieszMatrix sh N hN)⁻¹) j| ^ q) ^ (1 / q) ≤
        C * ((N : ℝ) ^ (-b) * A₀ + A₀ ^ (1 - b) * A₁ ^ b) ∧
      (A₁ = 0 → A₀ ^ (1 - b) * A₁ ^ b = 0) := by
  dsimp only
  let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
    constructor <;> linarith [s.property.1, s.property.2]⟩
  let q := 2 / s.val
  let p := ENNReal.ofReal q
  have hq : 1 ≤ q := by
    dsimp [q]
    rw [le_div_iff₀ s.property.1]
    linarith [s.property.2]
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  let : Fact (1 ≤ p) := ⟨by
    exact_mod_cast (show ENNReal.ofReal 1 ≤ ENNReal.ofReal q from ENNReal.ofReal_le_ofReal hq)⟩
  have hp : 0 < p.toReal := by simpa only [p, ENNReal.toReal_ofReal hq0.le] using hq0
  obtain ⟨C, hC, hc⟩ := inverse_row_optimized hz sh hp
  refine ⟨C, hC, ?_⟩
  intro N hN F A₀ A₁ hA₀ hA₁ hF hΔ
  have hnorm (w : Fin (N : ℕ) → ℝ) :
      ‖WithLp.toLp p w‖ = (∑ j, |w j| ^ q) ^ (1 / q) := by
    rw [PiLp.norm_eq_sum hp]
    simp only [p, ENNReal.toReal_ofReal hq0.le, Real.norm_eq_abs]
  have hback : ‖WithLp.toLp p (fun j => F (j - 1)) - WithLp.toLp p F‖ ≤ A₁ := by
    change ‖WithLp.toLp p (fun j => F (j - 1) - F j)‖ ≤ A₁
    have heq : (fun j => F (j - 1) - F j) =
        (fun j => -(F (j + 1) - F j)) ∘ (fun j => j - 1) := by
      funext j
      simp
    rw [heq]
    change ‖WithLp.toLp p (fun j => (fun k => -(F (k + 1) - F k)) (j - 1))‖ ≤ A₁
    rw [DerivativeCommutators.norm_shift hp N 1 (fun j => -(F (j + 1) - F j))]
    change ‖-(WithLp.toLp p (fun j => F (j + 1) - F j))‖ ≤ A₁
    rw [norm_neg, hnorm]
    exact hΔ
  have h := hc N hN A₀ A₁ F hA₀ hA₁ (by rw [hnorm]; exact hF) hback
  rw [hnorm] at h
  constructor
  · convert h using 1
    dsimp only [sh]
    ring_nf
  · intro hzero
    rw [hzero, Real.zero_rpow (by linarith [s.property.2] : 1 - s.val / 2 ≠ 0), mul_zero]

end Riesz2.GlobalCancellation
