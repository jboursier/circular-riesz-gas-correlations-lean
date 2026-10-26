/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.GlobalResolventKernel
public import Riesz2.Preliminaries.ReciprocalSymbol

/-!
# Fourier identification of the global resolvent kernel

Continuation of the proof of Lemma 5.13. The existing
factorization matrix is used throughout. The constant frequency is retained.
-/

public section

noncomputable section

open Matrix Set Filter
open scoped BigOperators Fin.NatCast Topology ContDiff

namespace Riesz2

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

namespace GlobalResolventKernelInternal

/-- Integer difference labels agree with the arithmetic on the cycle. -/
theorem label_sub (N : ℕ+) (i j : Fin (N : ℕ)) :
    Riesz1.labelOf N ((i.val : ℤ) - j.val) = i - j := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [Riesz1.APG.labelOf_val, Fin.val_sub]
  rw [Int.natCast_emod, Nat.cast_add, Nat.cast_sub (Nat.le_of_lt j.isLt)]
  rw [show ((N : ℕ) : ℤ) - j.val + i.val = ((i.val : ℤ) - j.val) + (N : ℕ) by ring]
  simp only [Int.add_emod, Int.emod_self, add_zero, Int.emod_emod]

end GlobalResolventKernelInternal

/-- Exact Fourier multiplier of the actual global factorization matrix
(the proof of Lemma 5.13). This includes the zero frequency. -/
theorem factorizationMatrix_fourier (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (a : ℝ) (ha : 0 < a) (B : ℝ) (k : Fin (N : ℕ)) :
    let μ := a + B ^ 2 / a
    cycleFourier N (fun h => (factorizationMatrix s N hN a ha B 0 h : ℂ)) k =
      (μ : ℂ) / (2 * cycleFourier N (fun h => (sampledRieszKernel s N hN h : ℂ)) k + μ) := by
  let μ := a + B ^ 2 / a
  let A := factorizationMatrix s N hN a ha B
  let f : Fin (N : ℕ) → ℂ := fun h => (A 0 h : ℂ)
  let g : Fin (N : ℕ) → ℂ := fun h => (sampledRieszKernel s N hN h : ℂ)
  have hμ : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (factorization_shift_pos ha B).ne'
  have hconv (n : Fin (N : ℕ)) :
      (2 : ℂ) * cycleConvolution N g f n + (μ : ℂ) * f n =
        (μ : ℂ) * (if n = 0 then 1 else 0) := by
    have hh := congrArg (fun T : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ => T 0 n)
      (factorizationMatrix_mul_reference s N hN a ha B).1
    change (∑ j, A 0 j * (2 * sampledRieszKernel s N hN (n - j))) =
      μ * (if (0 : Fin (N : ℕ)) = n then 1 else 0) - μ * A 0 n at hh
    have hsum : (∑ j, A 0 j * (2 * sampledRieszKernel s N hN (n - j))) =
        2 * ∑ j, sampledRieszKernel s N hN (n - j) * A 0 j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsum, show (if (0 : Fin (N : ℕ)) = n then (1 : ℝ) else 0) =
      (if n = 0 then 1 else 0) by simp only [eq_comm]] at hh
    have hreal : 2 * (∑ j, sampledRieszKernel s N hN (n - j) * A 0 j) +
        μ * A 0 n = μ * (if n = 0 then 1 else 0) := by linarith only [hh]
    simp only [cycleConvolution, GlobalResolventKernelInternal.label_sub, g, f]
    have hh := congrArg (fun r : ℝ => (r : ℂ)) hreal
    push_cast at hh
    by_cases hn : n = 0 <;>
      simpa only [hn, ↓reduceIte, Complex.ofReal_one, Complex.ofReal_zero] using hh
  have heq : 2 * cycleFourier N g k * cycleFourier N f k +
      (μ : ℂ) * cycleFourier N f k = μ := by
    calc
      _ = cycleFourier N (fun n => 2 * cycleConvolution N g f n + (μ : ℂ) * f n) k := by
        rw [mul_assoc (2 : ℂ), ← cycleFourier_convolution]
        simp only [cycleFourier, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
      _ = cycleFourier N (fun n => (μ : ℂ) * (if n = 0 then 1 else 0)) k := by simp_rw [hconv]
      _ = (μ : ℂ) * cycleFourier N (fun n => if n = 0 then 1 else 0) k := by
        simp only [cycleFourier, mul_assoc, ← Finset.mul_sum]
      _ = μ := by rw [cycleFourier_delta, mul_one]
  have hd : 2 * cycleFourier N g k + (μ : ℂ) ≠ 0 := by
    intro hh
    have hh' : (2 * cycleFourier N g k + (μ : ℂ)) * cycleFourier N f k = μ := by
      linear_combination heq
    rw [hh, zero_mul] at hh'
    exact hμ hh'.symm
  apply (eq_div_iff hd).mpr
  linear_combination heq

/-- At nonzero frequencies the exact symbol is the shifted lattice symbol,
with the factor two from `H = 2 ℍ` (the proof of Lemma 5.13). -/
theorem factorizationMatrix_fourier_nonzero (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (a : ℝ) (ha : 0 < a) (B : ℝ)
    (k : Fin (N : ℕ)) (hk : k ≠ 0) :
    cycleFourier N (fun h => (factorizationMatrix s N hN a ha B 0 h : ℂ)) k =
      (((a + B ^ 2 / a) /
        (2 * latticeRieszSymbol s ⟨cycleAngle N k, cycleAngle_mem_Ioo N k hk⟩ +
          (a + B ^ 2 / a)) : ℝ) : ℂ) := by
  rw [factorizationMatrix_fourier, sampledRieszKernel_nonzero_eigenvalue s N hN k hk]
  simp only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat]

/-- The zero frequency has its actual positive mass, rather than the continuous
cusp extension used for the nonzero-frequency multiplier. -/
theorem factorizationMatrix_fourier_zero (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (a : ℝ) (ha : 0 < a) (B : ℝ) :
    cycleFourier N (fun h => (factorizationMatrix s N hN a ha B 0 h : ℂ)) 0 =
      (((a + B ^ 2 / a) /
        (2 * (∑ h, sampledRieszKernel s N hN h) + (a + B ^ 2 / a)) : ℝ) : ℂ) := by
  rw [factorizationMatrix_fourier]
  have hz : cycleFourier N (fun h => (sampledRieszKernel s N hN h : ℂ)) 0 =
      ((∑ h, sampledRieszKernel s N hN h : ℝ) : ℂ) := by
    simp [cycleFourier, cycleAngle, Complex.ofReal_sum]
  rw [hz]
  simp only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat]

namespace GlobalResolventKernelInternal

/-- Exact aliasing reduction for the existing matrix inverse. The analytic
hypotheses here concern an arbitrary summable sequence. -/
theorem aliasing_of_coefficients (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (a : ℝ) (ha : 0 < a) (B : ℝ)
    (φ : ℤ → ℂ) (hφ : Summable (fun n => ‖φ n‖))
    (hzero : latticeFourier φ hφ 0 = 0)
    (hfreq : ∀ (k : Fin (N : ℕ)) (hk : k ≠ 0),
      latticeFourier φ hφ (cycleAngle N k) =
        (((a + B ^ 2 / a) /
          (2 * latticeRieszSymbol s ⟨cycleAngle N k, cycleAngle_mem_Ioo N k hk⟩ +
            (a + B ^ 2 / a)) : ℝ) : ℂ)) :
    ∀ h : Fin (N : ℕ), (factorizationMatrix s N hN a ha B 0 h : ℂ) =
      periodizeSequence N φ hφ h +
        ((a + B ^ 2 / a : ℝ) : ℂ) /
          ((N : ℂ) * (2 * ((∑ k, sampledRieszKernel s N hN k : ℝ) : ℂ) +
            ((a + B ^ 2 / a : ℝ) : ℂ))) := by
  let μ := a + B ^ 2 / a
  let ℓ : ℝ := 2 * ∑ k, sampledRieszKernel s N hN k
  let c : ℂ := (μ : ℂ) / ((N : ℂ) * ((ℓ + μ : ℝ) : ℂ))
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast N.ne_zero
  have heq : (fun h => (factorizationMatrix s N hN a ha B 0 h : ℂ)) =
      (fun h => periodizeSequence N φ hφ h + c) := by
    apply cycleFourier_injective N
    funext k
    have hs : cycleFourier N (fun h => periodizeSequence N φ hφ h + c) k =
        latticeFourier φ hφ (cycleAngle N k) + (if k = 0 then (N : ℂ) * c else 0) := by
      have hh : cycleFourier N (fun h => periodizeSequence N φ hφ h + c) k =
          cycleFourier N (periodizeSequence N φ hφ) k + cycleFourier N (fun _ => c) k := by
        simp only [cycleFourier, add_mul, Finset.sum_add_distrib]
      rw [hh, inverse_aliasing, cycleFourier_const]
    rw [hs]
    by_cases hk : k = 0
    · subst k
      rw [factorizationMatrix_fourier_zero]
      simp only [cycleAngle, Fin.val_zero, Nat.cast_zero, mul_zero, zero_div,
        hzero, ↓reduceIte, zero_add]
      change (((μ / (ℓ + μ) : ℝ) : ℂ)) = (N : ℂ) * c
      rw [Complex.ofReal_div]
      dsimp only [c]
      simp only [div_eq_mul_inv, _root_.mul_inv_rev]
      calc
        _ = ((N : ℂ) * (N : ℂ)⁻¹) * ((μ : ℂ) * ((ℓ + μ : ℝ) : ℂ)⁻¹) := by
          rw [mul_inv_cancel₀ hN0, one_mul]
        _ = _ := by ring
    · rw [factorizationMatrix_fourier_nonzero s N hN a ha B k hk, hfreq k hk,
        ite_eq_right hk, add_zero]
  intro h
  have hh := congrFun heq h
  simpa only [c, μ, ℓ, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat] using hh

/-- The constant correction cancels exactly in a forward kernel difference.
This reduces the increment clause of the proof of Lemma 5.13 to the
periodization of coefficient increments. -/
theorem increment_of_aliasing (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (a : ℝ) (ha : 0 < a) (B : ℝ)
    (φ : ℤ → ℂ) (hφ : Summable (fun n => ‖φ n‖))
    (hzero : latticeFourier φ hφ 0 = 0)
    (hfreq : ∀ (k : Fin (N : ℕ)) (hk : k ≠ 0),
      latticeFourier φ hφ (cycleAngle N k) =
        (((a + B ^ 2 / a) /
          (2 * latticeRieszSymbol s ⟨cycleAngle N k, cycleAngle_mem_Ioo N k hk⟩ +
            (a + B ^ 2 / a)) : ℝ) : ℂ))
    (h : Fin (N : ℕ)) :
    ((factorizationMatrix s N hN a ha B 0 (h + 1) -
      factorizationMatrix s N hN a ha B 0 h : ℝ) : ℂ) =
      periodizeSequence N φ hφ (h + 1) - periodizeSequence N φ hφ h := by
  rw [Complex.ofReal_sub, aliasing_of_coefficients s N hN a ha B φ hφ hzero hfreq,
    aliasing_of_coefficients s N hN a ha B φ hφ hzero hfreq]
  ring

/-- Forward differences commute with periodization, including the last-to-first
edge of the cycle. The series on the right is absolutely summable. -/
theorem periodize_forward_difference (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (φ : ℤ → ℂ) (hφ : Summable (fun n => ‖φ n‖)) (h : Fin (N : ℕ)) :
    periodizeSequence N φ hφ (h + 1) - periodizeSequence N φ hφ h =
      ∑' l : ℤ, (φ ((h.val : ℤ) + 1 + l * (N : ℕ)) -
        φ ((h.val : ℤ) + l * (N : ℕ))) := by
  have hs1 := (summable_norm_periodizeSequence N φ hφ ((h.val : ℤ) + 1)).of_norm
  have hs0 := (summable_norm_periodizeSequence N φ hφ h.val).of_norm
  have hval : ((h + 1).val : ℤ) + (((h.val + 1) / (N : ℕ) : ℕ) : ℤ) * (N : ℕ) =
      (h.val : ℤ) + 1 := by
    have hone : (1 : Fin (N : ℕ)).val = 1 := by
      rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
    rw [Fin.val_add, hone]
    have hh := Nat.mod_add_div (h.val + 1) (N : ℕ)
    exact_mod_cast (by simpa only [mul_comm] using hh)
  have he : periodizeSequence N φ hφ (h + 1) =
      ∑' l : ℤ, φ ((h.val : ℤ) + 1 + l * (N : ℕ)) := by
    rw [← hval, periodizeSequence_lift N φ hφ]
    rfl
  rw [he]
  exact (hs1.tsum_sub hs0).symm

/-- Complete reduction of the actual matrix increment to coefficient
increments, with its zero-frequency correction cancelled exactly. -/
theorem kernel_increment_series (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (a : ℝ) (ha : 0 < a) (B : ℝ)
    (φ : ℤ → ℂ) (hφ : Summable (fun n => ‖φ n‖))
    (hzero : latticeFourier φ hφ 0 = 0)
    (hfreq : ∀ (k : Fin (N : ℕ)) (hk : k ≠ 0),
      latticeFourier φ hφ (cycleAngle N k) =
        (((a + B ^ 2 / a) /
          (2 * latticeRieszSymbol s ⟨cycleAngle N k, cycleAngle_mem_Ioo N k hk⟩ +
            (a + B ^ 2 / a)) : ℝ) : ℂ))
    (h : Fin (N : ℕ)) :
    ((factorizationMatrix s N hN a ha B 0 (h + 1) -
      factorizationMatrix s N hN a ha B 0 h : ℝ) : ℂ) =
      ∑' l : ℤ, (φ ((h.val : ℤ) + 1 + l * (N : ℕ)) -
        φ ((h.val : ℤ) + l * (N : ℕ))) := by
  rw [increment_of_aliasing s N hN a ha B φ hφ hzero hfreq,
    periodize_forward_difference N hN φ hφ]

/-- The reciprocal of the shifted symbol has the same cusp envelopes through
order two, with a constant independent of the positive shift. Multiplication
by the shift therefore gives polynomial (in fact linear) dependence on it. -/
theorem shifted_reciprocal_bounds (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : ℝ, 0 < μ → ∀ j : ℕ, j ≤ 2 →
      ∀ θ : Set.Ioo (0 : ℝ) (2 * Real.pi),
        |iteratedDeriv j (fun y : ℝ =>
          (μ + 2 * (2 + symbolZetaFactor s *
            Riesz1.hurwitzKernel (1 - s.val) (y / (2 * Real.pi))))⁻¹) θ.val| ≤
          C * symbolEndpointDistance θ ^ (1 - s.val - (j : ℝ)) := by
  let F := fun y : ℝ => 2 + symbolZetaFactor s *
    Riesz1.hurwitzKernel (1 - s.val) (y / (2 * Real.pi))
  obtain ⟨c, _, hc, _, hlower⟩ := latticeRieszSymbol_power_bounds hz s
  obtain ⟨D, hD, hd1⟩ := latticeRieszSymbol_all_derivatives hz s 1
  obtain ⟨E, hE, hd2⟩ := latticeRieszSymbol_all_derivatives hz s 2
  let c' := 2 * c
  let D' := 2 * D
  let E' := 2 * E
  let C := c'⁻¹ + D' * c'⁻¹ ^ 2 + (2 * D' ^ 2 * c'⁻¹ ^ 3 + E' * c'⁻¹ ^ 2)
  have hc' : 0 < c' := by dsimp [c']; positivity
  have hD' : 0 ≤ D' := by dsimp [D']; positivity
  have hE' : 0 ≤ E' := by dsimp [E']; positivity
  have h1 : 0 ≤ D' * c'⁻¹ ^ 2 := by positivity
  have h2 : 0 ≤ 2 * D' ^ 2 * c'⁻¹ ^ 3 + E' * c'⁻¹ ^ 2 := by positivity
  have hC0 : c'⁻¹ ≤ C := by dsimp [C]; linarith only [h1, h2]
  have hC1 : D' * c'⁻¹ ^ 2 ≤ C := by
    have hi := (inv_pos.mpr hc').le
    dsimp [C]; linarith only [h2, hi]
  have hC2 : 2 * D' ^ 2 * c'⁻¹ ^ 3 + E' * c'⁻¹ ^ 2 ≤ C := by
    have hi := (inv_pos.mpr hc').le
    dsimp [C]; linarith only [h1, hi]
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro μ hμ j hj θ
  let Q := fun y : ℝ => μ + 2 * F y
  have hQ : ContDiffOn ℝ 2 Q (Set.Ioo 0 (2 * Real.pi)) := by
    exact (contDiffOn_const.add (contDiffOn_const.mul (symbol_hurwitz_contDiff s))).of_le (by norm_num)
  have hpos (y : ℝ) (hy : y ∈ Set.Ioo 0 (2 * Real.pi)) : 0 < Q y := by
    change 0 < μ + 2 * F y
    have hh : 0 < F y := by
      dsimp [F]
      rw [← latticeRieszSymbol_eq_hurwitzKernel hz s ⟨y, hy⟩]
      exact latticeRieszSymbol_pos s _
    positivity
  have hne : ∀ y ∈ Set.Ioo 0 (2 * Real.pi), Q y ≠ 0 := fun y hy => (hpos y hy).ne'
  have hρ := symbolEndpointDistance_pos θ
  have hlo : c' * symbolEndpointDistance θ ^ (s.val - 1) ≤ Q θ.val := by
    have hh := (hlower θ).1
    rw [latticeRieszSymbol_eq_hurwitzKernel hz s θ] at hh
    dsimp only [Q, c', F]
    nlinarith only [hh, hμ]
  have hder1 : |deriv Q θ.val| ≤ D' * symbolEndpointDistance θ ^ (s.val - 1 - 1) := by
    have heq : deriv Q θ.val = 2 * iteratedDeriv 1 F θ.val := by
      rw [show deriv Q θ.val = iteratedDeriv 1 Q θ.val by
        simp only [iteratedDeriv_succ, iteratedDeriv_zero]]
      dsimp only [Q]
      rw [iteratedDeriv_const_add (by omega), iteratedDeriv_const_mul_field]
    rw [heq, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
    simpa only [D', F, Nat.cast_one, mul_assoc] using
      (mul_le_mul_of_nonneg_left (hd1 θ) two_pos.le)
  have hder2 : |deriv (deriv Q) θ.val| ≤ E' * symbolEndpointDistance θ ^ (s.val - 1 - 2) := by
    have heq : deriv (deriv Q) θ.val = 2 * iteratedDeriv 2 F θ.val := by
      rw [show deriv (deriv Q) θ.val = iteratedDeriv 2 Q θ.val by
        simp only [iteratedDeriv_succ, iteratedDeriv_zero]]
      dsimp only [Q]
      rw [iteratedDeriv_const_add (by omega), iteratedDeriv_const_mul_field]
    rw [heq, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
    simpa only [E', F, Nat.cast_ofNat, mul_assoc] using
      (mul_le_mul_of_nonneg_left (hd2 θ) two_pos.le)
  change |iteratedDeriv j (fun y => (Q y)⁻¹) θ.val| ≤ _
  interval_cases j
  · simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero]
    have hh := ReciprocalCusp.inv_bound hc' hρ hlo
    rw [show -(s.val - 1) = 1 - s.val by ring] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hC0 (by positivity))
  · simp only [iteratedDeriv_succ, iteratedDeriv_zero, Nat.cast_one]
    rw [deriv_fun_inv'' ((hQ.contDiffAt (isOpen_Ioo.mem_nhds θ.property)).differentiableAt
      (by norm_num)) (hne θ θ.property)]
    have hh := ReciprocalCusp.first_bound hc' hD' hρ hlo hder1
    rw [show -(s.val - 1) - 1 = 1 - s.val - 1 by ring] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hC1 (by positivity))
  · simp only [iteratedDeriv_succ, iteratedDeriv_zero, Nat.cast_ofNat]
    rw [ReciprocalCusp.second_derivative isOpen_Ioo hQ hne θ.property]
    have hh := ReciprocalCusp.second_bound hc' hD' hE' hρ hlo hder1 hder2
    rw [show -(s.val - 1) - 2 = 1 - s.val - 2 by ring] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hC2 (by positivity))

/-- Positivity of the existing reciprocal on its whole circle carrier. -/
theorem reciprocal_nonneg (s : Riesz1.RieszExponent)
    (x : AddCircle (2 * Real.pi)) : 0 ≤ reciprocalRieszSymbol s x := by
  dsimp only [reciprocalRieszSymbol]
  split_ifs with hx
  · exact le_rfl
  · exact (inv_pos.mpr (latticeRieszSymbol_pos s _)).le

/-- A continuous shifted multiplier with its cusp value fixed at zero.
The coefficient constant is uniform in every positive shift. -/
theorem exists_resolvent_multiplier (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : ℝ, 0 < μ →
      ∃ H : C(AddCircle (2 * Real.pi), ℂ), H 0 = 0 ∧
        ContDiffOn ℝ 2 (fun y : ℝ => H (y : AddCircle (2 * Real.pi)))
          (Ioo 0 (2 * Real.pi)) ∧
        (∀ j : ℕ, j ≤ 2 → ∀ y ∈ Ioo (0 : ℝ) (2 * Real.pi),
          ‖iteratedDeriv j (fun z : ℝ => H (z : AddCircle (2 * Real.pi))) y‖ ≤
            (C * μ) * (min y (2 * Real.pi - y)) ^ (1 - s.val - (j : ℝ))) ∧
        ∀ θ : Ioo (0 : ℝ) (2 * Real.pi),
          H (θ.val : AddCircle (2 * Real.pi)) =
            ((μ / (2 * latticeRieszSymbol s θ + μ) : ℝ) : ℂ) := by
  obtain ⟨C, hC, hb⟩ := shifted_reciprocal_bounds hz s
  refine ⟨C, hC, ?_⟩
  intro μ hμ
  let r := reciprocalRieszSymbol s
  let h : AddCircle (2 * Real.pi) → ℝ := fun x => μ * r x / (2 + μ * r x)
  have hr := continuous_reciprocalRieszSymbol hz s
  have hden (x : AddCircle (2 * Real.pi)) : 2 + μ * r x ≠ 0 := by
    have hh := reciprocal_nonneg s x
    exact (by positivity : 0 < 2 + μ * r x).ne'
  have hhc : Continuous h :=
    (continuous_const.mul hr).div (continuous_const.add (continuous_const.mul hr)) hden
  let H : C(AddCircle (2 * Real.pi), ℂ) := ⟨fun x => (h x : ℂ), Complex.continuous_ofReal.comp hhc⟩
  let F := fun y : ℝ => 2 + symbolZetaFactor s *
    Riesz1.hurwitzKernel (1 - s.val) (y / (2 * Real.pi))
  let Q := fun y : ℝ => μ + 2 * F y
  have hFpos (y : ℝ) (hy : y ∈ Ioo 0 (2 * Real.pi)) : 0 < F y := by
    dsimp only [F]
    rw [← latticeRieszSymbol_eq_hurwitzKernel hz s ⟨y, hy⟩]
    exact latticeRieszSymbol_pos s _
  have hQne : ∀ y ∈ Ioo 0 (2 * Real.pi), Q y ≠ 0 := by
    intro y hy
    have hp := hFpos y hy
    exact (by dsimp [Q]; positivity : 0 < Q y).ne'
  have heq (y : ℝ) (hy : y ∈ Ioo 0 (2 * Real.pi)) :
      h (y : AddCircle (2 * Real.pi)) = μ * (Q y)⁻¹ := by
    dsimp only [h, r]
    rw [reciprocalRieszSymbol_coe s ⟨y, hy⟩, latticeRieszSymbol_eq_hurwitzKernel hz s ⟨y, hy⟩]
    change μ * (F y)⁻¹ / (2 + μ * (F y)⁻¹) = μ * (Q y)⁻¹
    have hp := hFpos y hy
    have hq := hQne y hy
    have hd : 2 + μ * (F y)⁻¹ ≠ 0 := by positivity
    dsimp only [Q] at hq ⊢
    field_simp
    ring
  have hev {y : ℝ} (hy : y ∈ Ioo 0 (2 * Real.pi)) :
      (fun z : ℝ => h (z : AddCircle (2 * Real.pi))) =ᶠ[𝓝 y]
        (fun z => μ * (Q z)⁻¹) := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz
    exact heq z hz
  have hQ : ContDiffOn ℝ ∞ Q (Ioo 0 (2 * Real.pi)) :=
    contDiffOn_const.add (contDiffOn_const.mul (symbol_hurwitz_contDiff s))
  have hhs : ContDiffOn ℝ 2 (fun z : ℝ => h (z : AddCircle (2 * Real.pi)))
      (Ioo 0 (2 * Real.pi)) := by
    exact (contDiffOn_const.mul (hQ.inv hQne)).of_le (by norm_num) |>.congr
      (fun y hy => heq y hy)
  refine ⟨H, ?_, Complex.ofRealCLM.contDiff.comp_contDiffOn hhs, ?_, ?_⟩
  · simp only [H, ContinuousMap.coe_mk, h, r,
      reciprocalRieszSymbol_zero, mul_zero, zero_div, Complex.ofReal_zero]
  · intro j hj y hy
    have hs : ContDiffAt ℝ j (fun z : ℝ => h (z : AddCircle (2 * Real.pi))) y :=
      (hhs.contDiffAt (isOpen_Ioo.mem_nhds hy)).of_le (by exact_mod_cast hj)
    have hi := iteratedDeriv_smul_const hs (1 : ℂ)
    simp only [Complex.real_smul, mul_one] at hi
    change ‖iteratedDeriv j (fun z : ℝ => (h (z : AddCircle (2 * Real.pi)) : ℂ)) y‖ ≤ _
    rw [hi, Complex.norm_real, Real.norm_eq_abs, (hev hy).iteratedDeriv_eq j,
      iteratedDeriv_const_mul_field, abs_mul, abs_of_pos hμ]
    have hh := mul_le_mul_of_nonneg_left (hb μ hμ j hj ⟨y, hy⟩) hμ.le
    simpa only [Q, F, symbolEndpointDistance, mul_assoc, mul_comm C μ] using hh
  · intro θ
    change (h (θ.val : AddCircle (2 * Real.pi)) : ℂ) = _
    rw [heq θ θ.property]
    have hFe : F θ.val = latticeRieszSymbol s θ :=
      (latticeRieszSymbol_eq_hurwitzKernel hz s θ).symm
    simp only [Q, hFe, div_eq_mul_inv, add_comm μ]

/-- The ordinary cusp produces absolutely summable coefficients for the
shifted multiplier, with a linear bound in the positive shift. This is the
coefficient construction used in the proof of Lemma 5.13. -/
theorem exists_resolvent_coefficients (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : ℝ, 0 < μ → ∃ φ : ℤ → ℂ,
      (∀ n : ℤ, ‖φ n‖ ≤ C * μ / (1 + |(n : ℝ)| ^ (2 - s.val))) ∧
      ∃ hφ : Summable (fun n => ‖φ n‖), latticeFourier φ hφ 0 = 0 ∧
        ∀ θ : Ioo (0 : ℝ) (2 * Real.pi),
          latticeFourier φ hφ θ.val = ((μ / (2 * latticeRieszSymbol s θ + μ) : ℝ) : ℂ) := by
  obtain ⟨A, hA, hm⟩ := exists_resolvent_multiplier hz s
  obtain ⟨K, hK, hb⟩ := FractionalCuspFourier.fractional_cusp_fourier
    (sub_pos.mpr s.property.2) (by linarith [s.property.1] : 1 - s.val < 1)
  refine ⟨K * A, mul_pos hK hA, ?_⟩
  intro μ hμ
  obtain ⟨H, hH0, hHs, hHd, hHe⟩ := hm μ hμ
  obtain ⟨hdec, hφ, hre, _, _⟩ := hb (A * μ) (mul_pos hA hμ) H hH0 hHs hHd
  refine ⟨fourierCoeff H, ?_, hφ, ?_, ?_⟩
  · intro n
    simpa only [show 1 + (1 - s.val) = 2 - s.val by ring, mul_assoc] using hdec n
  · simpa only [AddCircle.coe_zero, hH0] using hre 0
  · intro θ
    rw [hre]
    exact hHe θ

/-- Identification of the two existing cyclic-distance conventions. -/
theorem distance_nat (N : ℕ+) (h : Fin (N : ℕ)) :
    ((Riesz1.cyclicDist N (h.val : ℤ) 0 : ℤ) : ℝ) =
      (Riesz1.cyclicIndexDistance N h 0 : ℝ) := by
  have hh := cyclicIndexDistance_labelOf N (h.val : ℤ) 0
  rw [Riesz1.labelOf_natCast, show Riesz1.labelOf N 0 = (0 : Fin (N : ℕ)) from
    Riesz1.labelOf_natCast N 0] at hh
  exact_mod_cast hh.symm

/-- The two standard summable-power envelopes differ by a uniform factor. -/
theorem power_envelope_compare {p d : ℝ} (hp : 0 ≤ p) (hd : 0 ≤ d) :
    1 / (1 + d ^ p) ≤ 2 ^ p * (1 + d) ^ (-p) := by
  have hpow : (1 + d) ^ p ≤ 2 ^ p * (1 + d ^ p) := by
    rcases le_total d 1 with hd1 | hd1
    · have hh := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + d) (by linarith : 1 + d ≤ 2) hp
      nlinarith only [hh, mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) p)
        (Real.rpow_nonneg hd p)]
    · calc
        _ ≤ (2 * d) ^ p := Real.rpow_le_rpow (by positivity) (by linarith) hp
        _ = 2 ^ p * d ^ p := Real.mul_rpow (by norm_num) hd
        _ ≤ _ := by nlinarith only [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) p]
  rw [Real.rpow_neg (by positivity : 0 ≤ 1 + d), ← div_eq_mul_inv]
  exact (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa only [one_mul] using hpow)

end GlobalResolventKernelInternal

/-- The entry-decay clause of the proof of Lemma 5.13.
The polynomial bound can be taken linear in the positive shift μ. -/
theorem factorizationMatrix_entry_decay (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (a : ℝ) (ha : 0 < a) (B : ℝ) (h : Fin (N : ℕ)),
      |factorizationMatrix s N hN a ha B 0 h| ≤
        C * (a + B ^ 2 / a) *
          (1 + (Riesz1.cyclicIndexDistance N h 0 : ℝ)) ^ (-(2 - s.val)) := by
  let p := 2 - s.val
  have hp : 1 < p := by dsimp [p]; linarith [s.property.2]
  obtain ⟨A, hA, hcoeff⟩ := GlobalResolventKernelInternal.exists_resolvent_coefficients hz s
  obtain ⟨T, hT, htail⟩ := inverse_power_sum hp
  obtain ⟨c, _, hc, _, hmode⟩ := sampledRieszKernel_zero_mode_bounds s
  refine ⟨(A * T + 2 / c) * 2 ^ p, by positivity, ?_⟩
  intro N hN a ha B h
  let μ := a + B ^ 2 / a
  have hμ : 0 < μ := factorization_shift_pos ha B
  obtain ⟨φ, hφb, hφ, hzero, hfreq⟩ := hcoeff μ hμ
  let mass := ∑ k, sampledRieszKernel s N hN k
  let d : ℝ := Riesz1.cyclicIndexDistance N h 0
  let D := 1 + d ^ p
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hD : 0 < D := by dsimp [D]; positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hlower : c * (N : ℝ) ^ (1 - s.val) ≤ mass := (hmode N hN).1
  have hmass : 0 < mass := (by positivity : 0 < c * (N : ℝ) ^ (1 - s.val)).trans_le hlower
  have hden : 0 < 2 * mass + μ := by positivity
  obtain ⟨hts, htb, hnp⟩ := htail N hN h.val
  rw [GlobalResolventKernelInternal.distance_nat] at htb hnp
  have hperiod : ‖periodizeSequence N φ hφ h‖ ≤ (A * μ) * T / D := by
    calc
      _ ≤ ∑' l : ℤ, ‖φ ((h.val : ℤ) + l * (N : ℕ))‖ :=
        norm_tsum_le_tsum_norm (summable_norm_periodizeSequence N φ hφ h.val)
      _ ≤ ∑' l : ℤ, (A * μ) *
          (1 / (1 + |(h.val : ℝ) + (l : ℝ) * (N : ℝ)| ^ p)) := by
        apply Summable.tsum_le_tsum _ (summable_norm_periodizeSequence N φ hφ h.val) (hts.mul_left _)
        intro l
        convert hφb ((h.val : ℤ) + l * (N : ℕ)) using 1
        push_cast
        ring
      _ = (A * μ) * ∑' l : ℤ, 1 / (1 + |(h.val : ℝ) + (l : ℝ) * (N : ℝ)| ^ p) := tsum_mul_left
      _ ≤ (A * μ) * (T / D) := mul_le_mul_of_nonneg_left htb (by positivity)
      _ = _ := by ring
  have hmass : (2 * mass + μ)⁻¹ ≤ (1 / c) * (N : ℝ) ^ (s.val - 1) := by
    calc
      _ ≤ (c * (N : ℝ) ^ (1 - s.val))⁻¹ := inv_anti₀ (by positivity) (by linarith only [hlower, hmass, hμ])
      _ = _ := by
        rw [mul_inv, ← Real.rpow_neg hNpos.le]
        congr 2 <;> ring
  have hconst : μ / ((N : ℝ) * (2 * mass + μ)) ≤ (2 / c) * μ / D := by
    calc
      _ = μ * (N : ℝ)⁻¹ * (2 * mass + μ)⁻¹ := by rw [div_eq_mul_inv, mul_inv]; ring
      _ ≤ μ * (N : ℝ)⁻¹ * ((1 / c) * (N : ℝ) ^ (s.val - 1)) :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = (μ / c) * (N : ℝ) ^ (-p) := by
        rw [← Real.rpow_neg_one]
        calc
          _ = (μ / c) * ((N : ℝ) ^ (-1 : ℝ) * (N : ℝ) ^ (s.val - 1)) := by ring
          _ = _ := by
            rw [← Real.rpow_add hNpos]
            dsimp [p]
            congr 2
            ring
      _ ≤ (μ / c) * (2 / D) := mul_le_mul_of_nonneg_left hnp (by positivity)
      _ = _ := by ring
  have heq := GlobalResolventKernelInternal.aliasing_of_coefficients s N hN a ha B φ hφ hzero
    (fun k hk => hfreq ⟨_, cycleAngle_mem_Ioo N k hk⟩) h
  have hnorm : |factorizationMatrix s N hN a ha B 0 h| ≤
      ‖periodizeSequence N φ hφ h‖ + μ / ((N : ℝ) * (2 * mass + μ)) := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, heq]
    have hh := norm_add_le (periodizeSequence N φ hφ h)
      ((μ : ℂ) / ((N : ℂ) * ((2 * mass + μ : ℝ) : ℂ)))
    convert hh using 1
    · simp only [μ, mass, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat]
    · simp only [norm_div, norm_mul, Complex.norm_natCast, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hμ, abs_of_pos hden]
  have htotal : |factorizationMatrix s N hN a ha B 0 h| ≤ (A * T + 2 / c) * μ / D := by
    have hh := hnorm.trans (add_le_add hperiod hconst)
    convert hh using 1
    ring
  have henv := GlobalResolventKernelInternal.power_envelope_compare (by linarith : 0 ≤ p) hd
  calc
    _ ≤ (A * T + 2 / c) * μ / D := htotal
    _ ≤ ((A * T + 2 / c) * μ) * (2 ^ p * (1 + d) ^ (-p)) := by
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left henv (by positivity : 0 ≤ (A * T + 2 / c) * μ)
    _ = _ := by ring

end Riesz2
