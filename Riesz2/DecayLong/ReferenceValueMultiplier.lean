/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.GlobalResolventKernelPart2
public import Riesz2.Preliminaries.InverseRieszMatrix

/-!
# Direct value multiplier of the reference resolvent

The `σ = 0` argument in equation (5.68), in the proof of
Proposition 5.15, follows Lemma 2.4: uniform cusp derivatives,
Fourier coefficients, absolute aliasing and the exact constant frequency.
-/

@[expose] public section
noncomputable section

open Matrix Set Filter
open scoped BigOperators Fin.NatCast NNReal Topology ContDiff

namespace Riesz2.ReferenceValueMultiplier

local instance referenceValueMultiplierPeriodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Uniform two-derivative bounds, including shift zero, used in
Lemma 2.4 for equation (5.68) (Proposition 5.15). -/
theorem value_shifted_reciprocal_bounds (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : ℝ, 0 ≤ μ → ∀ j : ℕ, j ≤ 2 →
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
    exact add_pos_of_nonneg_of_pos hμ (mul_pos two_pos hh)
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

/-- The continuous value multiplier, its zero cusp extension and uniform
order-two bounds for Lemma 2.4, as applied in
equation (5.68) in the proof of Proposition 5.15. -/
theorem spectral_value_multiplier_bounds (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : ℝ, 0 ≤ μ →
      ∃ H : C(AddCircle (2 * Real.pi), ℂ), H 0 = 0 ∧
        ContDiffOn ℝ 2 (fun y : ℝ => H (y : AddCircle (2 * Real.pi)))
          (Ioo 0 (2 * Real.pi)) ∧
        (∀ j : ℕ, j ≤ 2 → ∀ y ∈ Ioo (0 : ℝ) (2 * Real.pi),
          ‖iteratedDeriv j (fun z : ℝ => H (z : AddCircle (2 * Real.pi))) y‖ ≤
            C * (min y (2 * Real.pi - y)) ^ (1 - s.val - (j : ℝ))) ∧
        ∀ θ : Ioo (0 : ℝ) (2 * Real.pi),
          H (θ.val : AddCircle (2 * Real.pi)) =
            ((1 / (2 * latticeRieszSymbol s θ + μ) : ℝ) : ℂ) := by
  obtain ⟨C, hC, hb⟩ := value_shifted_reciprocal_bounds hz s
  refine ⟨C, hC, ?_⟩
  intro μ hμ
  let r := reciprocalRieszSymbol s
  let h : AddCircle (2 * Real.pi) → ℝ := fun x => r x / (2 + μ * r x)
  have hr := continuous_reciprocalRieszSymbol hz s
  have hden (x : AddCircle (2 * Real.pi)) : 2 + μ * r x ≠ 0 := by
    have hh := GlobalResolventKernelInternal.reciprocal_nonneg s x
    exact (add_pos_of_pos_of_nonneg two_pos (mul_nonneg hμ hh)).ne'
  have hhc : Continuous h :=
    hr.div (continuous_const.add (continuous_const.mul hr)) hden
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
    exact (add_pos_of_nonneg_of_pos hμ (mul_pos two_pos hp)).ne'
  have heq (y : ℝ) (hy : y ∈ Ioo 0 (2 * Real.pi)) :
      h (y : AddCircle (2 * Real.pi)) = (Q y)⁻¹ := by
    dsimp only [h, r]
    rw [reciprocalRieszSymbol_coe s ⟨y, hy⟩, latticeRieszSymbol_eq_hurwitzKernel hz s ⟨y, hy⟩]
    change (F y)⁻¹ / (2 + μ * (F y)⁻¹) = (Q y)⁻¹
    have hp := hFpos y hy
    have hq := hQne y hy
    have hd : 2 + μ * (F y)⁻¹ ≠ 0 :=
      (add_pos_of_pos_of_nonneg two_pos (mul_nonneg hμ (inv_nonneg.mpr hp.le))).ne'
    dsimp only [Q] at hq ⊢
    field_simp
    ring
  have hev {y : ℝ} (hy : y ∈ Ioo 0 (2 * Real.pi)) :
      (fun z : ℝ => h (z : AddCircle (2 * Real.pi))) =ᶠ[𝓝 y]
        (fun z => (Q z)⁻¹) := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz
    exact heq z hz
  have hQ : ContDiffOn ℝ ∞ Q (Ioo 0 (2 * Real.pi)) :=
    contDiffOn_const.add (contDiffOn_const.mul (symbol_hurwitz_contDiff s))
  have hhs : ContDiffOn ℝ 2 (fun z : ℝ => h (z : AddCircle (2 * Real.pi)))
      (Ioo 0 (2 * Real.pi)) := by
    exact (hQ.inv hQne).of_le (by norm_num) |>.congr
      (fun y hy => heq y hy)
  refine ⟨H, ?_, Complex.ofRealCLM.contDiff.comp_contDiffOn hhs, ?_, ?_⟩
  · simp only [H, ContinuousMap.coe_mk, h, r,
      reciprocalRieszSymbol_zero, zero_div, Complex.ofReal_zero]
  · intro j hj y hy
    have hs : ContDiffAt ℝ j (fun z : ℝ => h (z : AddCircle (2 * Real.pi))) y :=
      (hhs.contDiffAt (isOpen_Ioo.mem_nhds hy)).of_le (by exact_mod_cast hj)
    have hi := iteratedDeriv_smul_const hs (1 : ℂ)
    simp only [Complex.real_smul, mul_one] at hi
    change ‖iteratedDeriv j (fun z : ℝ => (h (z : AddCircle (2 * Real.pi)) : ℂ)) y‖ ≤ _
    rw [hi, Complex.norm_real, Real.norm_eq_abs, (hev hy).iteratedDeriv_eq j]
    simpa only [Q, F, symbolEndpointDistance] using hb μ hμ j hj ⟨y, hy⟩
  · intro θ
    change (h (θ.val : AddCircle (2 * Real.pi)) : ℂ) = _
    rw [heq θ θ.property]
    have hFe : F θ.val = latticeRieszSymbol s θ :=
      (latticeRieszSymbol_eq_hurwitzKernel hz s θ).symm
    simp only [Q, hFe, div_eq_mul_inv, one_mul, add_comm μ]




/-- Fourier coefficients of the value multiplier in equation (5.68)
(Proposition 5.15), obtained from the cusp estimate of Lemma 2.4. -/
theorem exists_value_coefficients (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : ℝ, 0 ≤ μ → ∃ φ : ℤ → ℂ,
      (∀ n : ℤ, ‖φ n‖ ≤ C / (1 + |(n : ℝ)| ^ (2 - s.val))) ∧
      ∃ hφ : Summable (fun n => ‖φ n‖), latticeFourier φ hφ 0 = 0 ∧
        ∀ θ : Ioo (0 : ℝ) (2 * Real.pi),
          latticeFourier φ hφ θ.val = ((2 * latticeRieszSymbol s θ + μ)⁻¹ : ℝ) := by
  obtain ⟨A, hA, hm⟩ := spectral_value_multiplier_bounds hz s
  obtain ⟨K, hK, hb⟩ := FractionalCuspFourier.fractional_cusp_fourier
    (sub_pos.mpr s.property.2) (by linarith [s.property.1] : 1 - s.val < 1)
  refine ⟨K * A, mul_pos hK hA, ?_⟩
  intro μ hμ
  obtain ⟨H, hH0, hHs, hHd, hHe⟩ := hm μ hμ
  obtain ⟨hdec, hφ, hre, _, _⟩ := hb A hA H hH0 hHs hHd
  refine ⟨fourierCoeff H, ?_, hφ, ?_, ?_⟩
  · intro n
    simpa only [show 1 + (1 - s.val) = 2 - s.val by ring] using hdec n
  · simpa only [AddCircle.coe_zero, hH0] using hre 0
  · intro θ
    rw [hre]
    simpa only [one_div] using hHe θ

/-- The exact aliasing identity, retaining the positive zero frequency, for
equation (5.68) in Proposition 5.15. This internal bridge is the
periodization step of Lemma 2.4. -/
theorem value_aliasing_internal (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (μ : ℝ) (hμ : 0 ≤ μ)
    (φ : ℤ → ℂ) (hφ : Summable (fun n => ‖φ n‖))
    (hzero : latticeFourier φ hφ 0 = 0)
    (hfreq : ∀ θ : Ioo (0 : ℝ) (2 * Real.pi),
      latticeFourier φ hφ θ.val = ((2 * latticeRieszSymbol s θ + μ)⁻¹ : ℝ))
    (h : Fin (N : ℕ)) :
    ((((2 : ℝ) • rieszMatrix s N hN + μ • 1)⁻¹ 0 h : ℝ) : ℂ) =
      periodizeSequence N φ hφ h +
        1 / ((N : ℂ) * ((2 * (∑ k, sampledRieszKernel s N hN k) + μ : ℝ) : ℂ)) := by
  let f : Fin (N : ℕ) → ℝ := fun n =>
    2 * sampledRieszKernel s N hN n + μ * (if n = 0 then 1 else 0)
  let ell := 2 * ∑ k, sampledRieszKernel s N hN k
  have hfour (k : Fin (N : ℕ)) :
      cycleFourier N (fun n => (f n : ℂ)) k =
        2 * cycleFourier N (fun n => (sampledRieszKernel s N hN n : ℂ)) k + μ := by
    have he : cycleFourier N (fun n => (f n : ℂ)) k =
        2 * cycleFourier N (fun n => (sampledRieszKernel s N hN n : ℂ)) k +
          (μ : ℂ) * cycleFourier N (fun n => if n = 0 then 1 else 0) k := by
      simp only [cycleFourier, f, Complex.ofReal_add, Complex.ofReal_mul,
        Complex.ofReal_ofNat, apply_ite Complex.ofReal, Complex.ofReal_one,
        Complex.ofReal_zero, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    rw [he, cycleFourier_delta, mul_one]
  have hlambda : cycleFourier N (fun n => (f n : ℂ)) 0 = ((ell + μ : ℝ) : ℂ) := by
    rw [hfour]
    simp [cycleFourier, cycleAngle, ell, Complex.ofReal_sum]
  obtain ⟨c, _, hc, _, hb⟩ := sampledRieszKernel_zero_mode_bounds s
  have hmass : 0 < ∑ k, sampledRieszKernel s N hN k :=
    (mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)).trans_le (hb N hN).1
  have hell : 0 < ell + μ := add_pos_of_pos_of_nonneg (mul_pos two_pos hmass) hμ
  have hfreq' (k : Fin (N : ℕ)) (hk : k ≠ 0) :
      cycleFourier N (fun n => (f n : ℂ)) k =
        ((2 * latticeRieszSymbol s ⟨_, cycleAngle_mem_Ioo N k hk⟩ + μ : ℝ) : ℂ) := by
    rw [hfour, sampledRieszKernel_nonzero_eigenvalue s N hN k hk]
    push_cast
    rfl
  have hne (k : Fin (N : ℕ)) (hk : k ≠ 0) :
      cycleFourier N (fun n => (f n : ℂ)) k ≠ 0 := by
    rw [hfreq' k hk]
    exact Complex.ofReal_ne_zero.mpr
      (add_pos_of_pos_of_nonneg (mul_pos two_pos (latticeRieszSymbol_pos s _)) hμ).ne'
  have heven (x : ℤ) : f (Riesz1.labelOf N (-x)) = f (Riesz1.labelOf N x) := by
    have hlabel : Riesz1.labelOf N (-x) = -(Riesz1.labelOf N x) := by
      apply Fin.ext
      apply Int.ofNat_inj.mp
      rw [Riesz1.APG.labelOf_val, Fin.val_neg']
      rw [Int.natCast_emod, Nat.cast_sub (Nat.le_of_lt (Riesz1.labelOf N x).isLt),
        Riesz1.APG.labelOf_val]
      rw [Int.neg_emod_eq_sub_emod]
      simp only [Int.sub_emod, Int.emod_self, Int.emod_emod]
    simp only [f, hlabel, sampledRieszKernel_even, neg_eq_zero]
  have hi := (inverse_aliasing_real N hN φ hφ f heven (ell + μ) hlambda hell.ne'
    hzero (fun k hk => by
      rw [hfreq' k hk, hfreq ⟨_, cycleAngle_mem_Ioo N k hk⟩, Complex.ofReal_inv]) hne).2 0 h
  have hmatrix : Matrix.of (fun a b : Fin (N : ℕ) =>
      f (Riesz1.labelOf N ((b.val : ℤ) - a.val))) =
      (2 : ℝ) • rieszMatrix s N hN + μ • 1 := by
    ext a b
    simp only [Matrix.of_apply]
    rw [GlobalResolventKernelInternal.label_sub]
    simp only [Matrix.of_apply, f, rieszMatrix, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply, sub_eq_zero, eq_comm]
  rw [hmatrix] at hi
  simpa only [GlobalResolventKernelInternal.label_sub, sub_zero, ell] using hi


/-- Direct scalar value-kernel decay in equation (5.68) in the
proof of Proposition 5.15: uniform multiplier bounds, the coefficient estimate
of Lemma 2.4, aliasing, and its exact zero-mode correction. -/
theorem spectralInverse_decay_direct (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (μ : ℝ) (_hμ : 0 ≤ μ) (h : Fin (N : ℕ)),
      |((2 : ℝ) • rieszMatrix s N hN + μ • 1)⁻¹ 0 h| ≤
        C * (1 + (Riesz1.cyclicIndexDistance N h 0 : ℝ)) ^ (-(2 - s.val)) := by
  let p := 2 - s.val
  have hp : 1 < p := by dsimp [p]; linarith [s.property.2]
  obtain ⟨A, hA, hcoeff⟩ := exists_value_coefficients hz s
  obtain ⟨T, hT, htail⟩ := inverse_power_sum hp
  obtain ⟨c, _, hc, _, hmode⟩ := sampledRieszKernel_zero_mode_bounds s
  refine ⟨(A * T + 2 / c) * 2 ^ p, by positivity, ?_⟩
  intro N hN μ hμ h
  obtain ⟨φ, hφb, hφ, hzero, hfreq⟩ := hcoeff μ hμ
  let mass := ∑ k, sampledRieszKernel s N hN k
  let d : ℝ := Riesz1.cyclicIndexDistance N h 0
  let D := 1 + d ^ p
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hD : 0 < D := by dsimp [D]; positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hlower : c * (N : ℝ) ^ (1 - s.val) ≤ mass := (hmode N hN).1
  have hmass : 0 < mass := (by positivity : 0 < c * (N : ℝ) ^ (1 - s.val)).trans_le hlower
  have hden : 0 < 2 * mass + μ := add_pos_of_pos_of_nonneg (mul_pos two_pos hmass) hμ
  obtain ⟨hts, htb, hnp⟩ := htail N hN h.val
  rw [GlobalResolventKernelInternal.distance_nat] at htb hnp
  have hperiod : ‖periodizeSequence N φ hφ h‖ ≤ A * T / D := by
    calc
      _ ≤ ∑' l : ℤ, ‖φ ((h.val : ℤ) + l * (N : ℕ))‖ :=
        norm_tsum_le_tsum_norm (summable_norm_periodizeSequence N φ hφ h.val)
      _ ≤ ∑' l : ℤ, A *
          (1 / (1 + |(h.val : ℝ) + (l : ℝ) * (N : ℝ)| ^ p)) := by
        apply Summable.tsum_le_tsum _ (summable_norm_periodizeSequence N φ hφ h.val) (hts.mul_left _)
        intro l
        convert hφb ((h.val : ℤ) + l * (N : ℕ)) using 1
        push_cast
        ring
      _ = A * ∑' l : ℤ, 1 / (1 + |(h.val : ℝ) + (l : ℝ) * (N : ℝ)| ^ p) := tsum_mul_left
      _ ≤ A * (T / D) := mul_le_mul_of_nonneg_left htb hA.le
      _ = _ := by ring
  have hmassinv : (2 * mass + μ)⁻¹ ≤ c⁻¹ * (N : ℝ) ^ (-(1 - s.val)) := by
    calc
      _ ≤ (c * (N : ℝ) ^ (1 - s.val))⁻¹ :=
        inv_anti₀ (mul_pos hc (Real.rpow_pos_of_pos hNpos _)) (by linarith)
      _ = _ := by rw [mul_inv, Real.rpow_neg hNpos.le]
  have hconst : 1 / ((N : ℝ) * (2 * mass + μ)) ≤ (2 / c) / D := by
    calc
      _ = (N : ℝ)⁻¹ * (2 * mass + μ)⁻¹ := by rw [one_div, mul_inv]
      _ ≤ (N : ℝ)⁻¹ * (c⁻¹ * (N : ℝ) ^ (-(1 - s.val))) :=
        mul_le_mul_of_nonneg_left hmassinv (by positivity)
      _ = c⁻¹ * (N : ℝ) ^ (-p) := by
        rw [← Real.rpow_neg_one]
        calc
          _ = c⁻¹ * ((N : ℝ) ^ (-1 : ℝ) * (N : ℝ) ^ (-(1 - s.val))) := by ring
          _ = _ := by rw [← Real.rpow_add hNpos]; dsimp [p]; congr 2; ring
      _ ≤ c⁻¹ * (2 / D) := mul_le_mul_of_nonneg_left hnp (by positivity)
      _ = _ := by ring
  have heq := value_aliasing_internal s N hN μ hμ φ hφ hzero hfreq h
  have hnorm : |((2 : ℝ) • rieszMatrix s N hN + μ • 1)⁻¹ 0 h| ≤
      ‖periodizeSequence N φ hφ h‖ + 1 / ((N : ℝ) * (2 * mass + μ)) := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, heq]
    have hh := norm_add_le (periodizeSequence N φ hφ h)
      (1 / ((N : ℂ) * ((2 * mass + μ : ℝ) : ℂ)))
    convert hh using 1
    simp only [norm_div, norm_one, norm_mul, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hden]
  have htotal : |((2 : ℝ) • rieszMatrix s N hN + μ • 1)⁻¹ 0 h| ≤
      (A * T + 2 / c) / D := by
    have hh := hnorm.trans (add_le_add hperiod hconst)
    convert hh using 1
    ring
  have henv := GlobalResolventKernelInternal.power_envelope_compare (by linarith : 0 ≤ p) hd
  calc
    _ ≤ (A * T + 2 / c) / D := htotal
    _ ≤ (A * T + 2 / c) * (2 ^ p * (1 + d) ^ (-p)) := by
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left henv (by positivity : 0 ≤ A * T + 2 / c)
    _ = _ := by ring

end Riesz2.ReferenceValueMultiplier
