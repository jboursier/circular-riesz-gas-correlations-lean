/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.AngularBlockEstimates
public import Riesz2.ToMathlib.CyclicFourierL2

/-!
# The angular fractional primitive

The auxiliary operator in the proof of Lemma 5.9 of the paper uses
angular distance to `2πℤ`. Smooth blocks supported in the paper's angular
annuli give its Gagliardo–Nirenberg bound by L¹/L² interpolation.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Riesz2.DiscreteInterpolation

/-- The angular version of the displayed GN inequality in the proof of
Lemma 5.9 of the paper. The proof reconstructs the output from the smooth angular blocks, applies their
L¹ and L² estimates, and cancels the scale powers by Hölder interpolation. -/
theorem elliptic_GN_angular_complex (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent) :
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (u : Fin (N : ℕ) → ℂ), (∑ i, u i) = 0 →
      let w := cycleConvolution N (fun i => (sampledRieszKernel sh N hN i : ℂ)) u
      let v := cycleConvolution N (fun i => (sampledRieszKernel s N hN i : ℂ)) u
      (∑ i, ‖w i‖ ^ (1 - s.val / 2)⁻¹) ^ (1 - s.val / 2) ≤
        C * Real.log (2 * (N : ℝ)) * (∑ i, ‖v i‖) ^ (1 - s.val) *
          (∑ i, ‖angularPrimitive N (3 / 2 - s.val) u i‖ ^ 2) ^ (s.val / 2) := by
  dsimp only
  let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
    constructor <;> linarith [s.property.1, s.property.2]⟩
  obtain ⟨C, hC, h₁⟩ := angular_block_l1 hz s
  obtain ⟨D, hD, h₂⟩ := angular_block_l2 hz s
  let K := C ^ (1 - s.val) * D ^ s.val
  have hK : 0 < K := mul_pos (Real.rpow_pos_of_pos hC _) (Real.rpow_pos_of_pos hD _)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(5 / Real.log 2) * K, by positivity, fun N hN u hu => ?_⟩
  let w := cycleConvolution N (fun i => (sampledRieszKernel sh N hN i : ℂ)) u
  let v := cycleConvolution N (fun i => (sampledRieszKernel s N hN i : ℂ)) u
  let J := angularPrimitive N (3 / 2 - s.val) u
  let A := ∑ i, ‖v i‖
  let B := (∑ i, ‖J i‖ ^ 2) ^ (1 / 2 : ℝ)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hB : 0 ≤ B := Real.rpow_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) _
  let V : ℕ → Fin (N : ℕ) → ℂ := fun j => cycleFourierInv N (fun k =>
    (angularBlock (dyadicScale N j) (dyadicScale_pos N j) (cycleAngle N k) : ℂ) *
      cycleFourier N w k)
  have hw : (∑ i, w i) = 0 := by
    have hzero : cycleFourier N u 0 = 0 := by
      simpa only [cycleFourier, cycleAngle, Fin.val_zero, Nat.cast_zero,
        mul_zero, zero_div, Complex.ofReal_zero, Complex.exp_zero, mul_one] using hu
    have hh := cycleFourier_convolution (fun i => (sampledRieszKernel sh N hN i : ℂ)) u 0
    rw [hzero, mul_zero] at hh
    simpa only [cycleFourier, cycleAngle, Fin.val_zero, Nat.cast_zero,
      mul_zero, zero_div, Complex.ofReal_zero, Complex.exp_zero, mul_one] using hh
  have hrecon (i : Fin (N : ℕ)) :
      (∑ j ∈ Finset.range (dyadicDepth N + 1), V j i) = w i :=
    angularBlock_reconstruction N w hw i
  have hblock (j : ℕ) (hj : j ∈ Finset.range (dyadicDepth N + 1)) :
      (∑ i, ‖V j i‖ ^ (1 - s.val / 2)⁻¹) ^ (1 - s.val / 2) ≤
        K * A ^ (1 - s.val) * B ^ s.val := by
    have hj' : j ≤ dyadicDepth N := by have := Finset.mem_range.mp hj; omega
    exact block_interpolation s (V j) (dyadicScale_pos N j) hA hB hC.le hD.le
      (h₁ _ (dyadicScale_pos N j) (dyadicScale_le_one N hj') N hN u)
      (h₂ _ (dyadicScale_pos N j) N hN u)
  have hp : 1 ≤ (1 - s.val / 2)⁻¹ := by
    apply (one_le_inv₀ (by linarith [s.property.2] : 0 < 1 - s.val / 2)).mpr
    linarith [s.property.1]
  have htriangle := finite_sum_lp (Finset.range (dyadicDepth N + 1)) V hp
  have hpe : (1 : ℝ) / (1 - s.val / 2)⁻¹ = 1 - s.val / 2 := by simp only [one_div, inv_inv]
  simp only [hrecon, hpe] at htriangle
  have hsum := Finset.sum_le_sum hblock
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hexp : B ^ s.val = (∑ i, ‖J i‖ ^ 2) ^ (s.val / 2) := by
    dsimp only [B]
    rw [← Real.rpow_mul (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    congr 1
    ring
  change (∑ i, ‖w i‖ ^ (1 - s.val / 2)⁻¹) ^ (1 - s.val / 2) ≤
    ((5 / Real.log 2) * K) * Real.log (2 * (N : ℝ)) * A ^ (1 - s.val) *
      (∑ i, ‖J i‖ ^ 2) ^ (s.val / 2)
  calc
    _ ≤ ((dyadicDepth N + 1 : ℕ) : ℝ) * (K * A ^ (1 - s.val) * B ^ s.val) :=
      htriangle.trans hsum
    _ ≤ ((5 / Real.log 2) * Real.log (2 * (N : ℝ))) *
        (K * A ^ (1 - s.val) * B ^ s.val) :=
      mul_le_mul_of_nonneg_right (dyadicDepth_log_bound N) (by positivity)
    _ = _ := by rw [hexp]; ring

/-- The real-vector angular GN display in the proof of Lemma 5.9
of the paper, using the actual sampled Riesz matrices. -/
theorem elliptic_GN_angular (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent) :
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (u : Fin (N : ℕ) → ℝ), (∑ i, u i) = 0 →
      let H := fun v : Riesz1.RieszExponent =>
        (Matrix.of (fun a b : Fin (N : ℕ) => sampledRieszKernel v N hN (b - a))).mulVec u
      (∑ i, |H sh i| ^ (1 - s.val / 2)⁻¹) ^ (1 - s.val / 2) ≤
        C * Real.log (2 * (N : ℝ)) * (∑ i, |H s i|) ^ (1 - s.val) *
          (∑ i, ‖angularPrimitive N (3 / 2 - s.val) (fun j => (u j : ℂ)) i‖ ^ 2) ^
            (s.val / 2) := by
  dsimp only
  obtain ⟨C, hC, hb⟩ := elliptic_GN_angular_complex hz s
  refine ⟨C, hC, fun N hN u hu => ?_⟩
  have huc : (∑ i, (u i : ℂ)) = 0 := by rw [← Complex.ofReal_sum, hu, Complex.ofReal_zero]
  have hh := hb N hN (fun i => (u i : ℂ)) huc
  dsimp only at hh ⊢
  rw [← sampledRieszMatrix_eq_convolution, ← sampledRieszMatrix_eq_convolution] at hh
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hh

end Riesz2.DiscreteInterpolation
