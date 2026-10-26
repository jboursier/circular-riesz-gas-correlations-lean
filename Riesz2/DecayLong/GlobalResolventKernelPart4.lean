/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.GlobalResolventKernelPart3
public import Riesz2.ToMathlib.ReciprocalCuspThird
public import Riesz2.ToMathlib.FractionalCuspFourierThird

/-!
# Global resolvent kernel: third derivatives and complete kernel bounds

Third-derivative and resolvent kernel bounds in the proof of Lemma 5.13,
using the factorization matrix and continuous multiplier of
`GlobalResolventKernelPart2`.
-/

public section
noncomputable section

open Matrix Set Filter
open scoped BigOperators Fin.NatCast Topology ContDiff Matrix.Norms.L2Operator

namespace Riesz2

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

namespace GlobalResolventKernelInternal

/-- Uniform order-three reciprocal envelope for the proof of Lemma 5.13. The constant precedes the positive shift. -/
theorem shifted_reciprocal_bounds_three (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : ℝ, 0 < μ → ∀ j : ℕ, j ≤ 3 →
      ∀ θ : Ioo (0 : ℝ) (2 * Real.pi),
        |iteratedDeriv j (fun y : ℝ =>
          (μ + 2 * (2 + symbolZetaFactor s *
            Riesz1.hurwitzKernel (1 - s.val) (y / (2 * Real.pi))))⁻¹) θ.val| ≤
          C * symbolEndpointDistance θ ^ (1 - s.val - (j : ℝ)) := by
  obtain ⟨C₀, hC₀, hb₀⟩ := shifted_reciprocal_bounds hz s
  obtain ⟨c, _, hc, _, hlower⟩ := latticeRieszSymbol_power_bounds hz s
  obtain ⟨D, hD, hd1⟩ := latticeRieszSymbol_all_derivatives hz s 1
  obtain ⟨E, hE, hd2⟩ := latticeRieszSymbol_all_derivatives hz s 2
  obtain ⟨G, hG, hd3⟩ := latticeRieszSymbol_all_derivatives hz s 3
  let c' := 2 * c
  let D' := 2 * D
  let E' := 2 * E
  let G' := 2 * G
  let C₃ := 6 * D' ^ 3 * c'⁻¹ ^ 4 + 6 * D' * E' * c'⁻¹ ^ 3 + G' * c'⁻¹ ^ 2
  have hc' : 0 < c' := by dsimp [c']; positivity
  have hD' : 0 ≤ D' := by dsimp [D']; positivity
  have hE' : 0 ≤ E' := by dsimp [E']; positivity
  have hG' : 0 ≤ G' := by dsimp [G']; positivity
  have hC₃ : 0 ≤ C₃ := by dsimp [C₃]; positivity
  refine ⟨C₀ + C₃, by positivity, ?_⟩
  intro μ hμ j hj θ
  by_cases hj2 : j ≤ 2
  · exact (hb₀ μ hμ j hj2 θ).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC₃) (Real.rpow_nonneg (symbolEndpointDistance_pos θ).le _))
  have hj3 : j = 3 := by omega
  subst j
  let F := fun y : ℝ => 2 + symbolZetaFactor s *
    Riesz1.hurwitzKernel (1 - s.val) (y / (2 * Real.pi))
  let Q := fun y : ℝ => μ + 2 * F y
  have hQ : ContDiffOn ℝ 3 Q (Ioo 0 (2 * Real.pi)) :=
    (contDiffOn_const.add (contDiffOn_const.mul (symbol_hurwitz_contDiff s))).of_le
      (by norm_num)
  have hne : ∀ y ∈ Ioo 0 (2 * Real.pi), Q y ≠ 0 := by
    intro y hy
    have hp : 0 < F y := by
      dsimp only [F]
      rw [← latticeRieszSymbol_eq_hurwitzKernel hz s ⟨y, hy⟩]
      exact latticeRieszSymbol_pos s _
    exact (by dsimp [Q]; positivity : 0 < Q y).ne'
  have hρ := symbolEndpointDistance_pos θ
  have hlo : c' * symbolEndpointDistance θ ^ (s.val - 1) ≤ Q θ.val := by
    have hh := (hlower θ).1
    rw [latticeRieszSymbol_eq_hurwitzKernel hz s θ] at hh
    dsimp only [Q, c', F]
    nlinarith only [hh, hμ]
  have hder (k : ℕ) (hk : k ≠ 0) :
      iteratedDeriv k Q θ.val = 2 * iteratedDeriv k F θ.val := by
    dsimp only [Q]
    rw [iteratedDeriv_const_add (Nat.pos_of_ne_zero hk), iteratedDeriv_const_mul_field]
  have hder1 : |deriv Q θ.val| ≤ D' * symbolEndpointDistance θ ^ (s.val - 1 - 1) := by
    rw [show deriv Q θ.val = iteratedDeriv 1 Q θ.val by
      simp only [iteratedDeriv_succ, iteratedDeriv_zero]]
    rw [hder 1 (by norm_num), abs_mul, show |(2 : ℝ)| = 2 by norm_num]
    simpa only [D', F, Nat.cast_one, mul_assoc] using
      mul_le_mul_of_nonneg_left (hd1 θ) two_pos.le
  have hder2 : |deriv (deriv Q) θ.val| ≤ E' * symbolEndpointDistance θ ^ (s.val - 1 - 2) := by
    rw [show deriv (deriv Q) θ.val = iteratedDeriv 2 Q θ.val by
      simp only [iteratedDeriv_succ, iteratedDeriv_zero]]
    rw [hder 2 (by norm_num), abs_mul, show |(2 : ℝ)| = 2 by norm_num]
    simpa only [E', F, Nat.cast_ofNat, mul_assoc] using
      mul_le_mul_of_nonneg_left (hd2 θ) two_pos.le
  have hder3 : |deriv (deriv (deriv Q)) θ.val| ≤
      G' * symbolEndpointDistance θ ^ (s.val - 1 - 3) := by
    rw [show deriv (deriv (deriv Q)) θ.val = iteratedDeriv 3 Q θ.val by
      simp only [iteratedDeriv_succ, iteratedDeriv_zero]]
    rw [hder 3 (by norm_num), abs_mul, show |(2 : ℝ)| = 2 by norm_num]
    simpa only [G', F, Nat.cast_ofNat, mul_assoc] using
      mul_le_mul_of_nonneg_left (hd3 θ) two_pos.le
  change |iteratedDeriv 3 (fun y => (Q y)⁻¹) θ.val| ≤ _
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, Nat.cast_ofNat]
  rw [ReciprocalCusp.third_derivative isOpen_Ioo hQ hne θ.property]
  have hh := ReciprocalCusp.third_bound hc' hD' hE' hG' hρ hlo hder1 hder2 hder3
  rw [show -(s.val - 1) - 3 = 1 - s.val - 3 by ring] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith : C₃ ≤ C₀ + C₃)
    (Real.rpow_nonneg hρ.le _))

/-- Upgrade Part2's continuous multiplier to order three, without introducing
another multiplier. Infrastructure for the proof of Lemma 5.13. -/
theorem exists_resolvent_multiplier_three (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : ℝ, 0 < μ →
      ∃ H : C(AddCircle (2 * Real.pi), ℂ), H 0 = 0 ∧
        ContDiffOn ℝ 3 (fun y : ℝ => H (y : AddCircle (2 * Real.pi)))
          (Ioo 0 (2 * Real.pi)) ∧
        (∀ j : ℕ, j ≤ 3 → ∀ y ∈ Ioo (0 : ℝ) (2 * Real.pi),
          ‖iteratedDeriv j (fun z : ℝ => H (z : AddCircle (2 * Real.pi))) y‖ ≤
            (C * μ) * (min y (2 * Real.pi - y)) ^ (1 - s.val - (j : ℝ))) ∧
        ∀ θ : Ioo (0 : ℝ) (2 * Real.pi),
          H (θ.val : AddCircle (2 * Real.pi)) =
            ((μ / (2 * latticeRieszSymbol s θ + μ) : ℝ) : ℂ) := by
  obtain ⟨C, hC, hb⟩ := shifted_reciprocal_bounds_three hz s
  obtain ⟨_, _, hm⟩ := exists_resolvent_multiplier hz s
  refine ⟨C, hC, ?_⟩
  intro μ hμ
  obtain ⟨H, hH0, _, _, hHe⟩ := hm μ hμ
  let F := fun y : ℝ => 2 + symbolZetaFactor s *
    Riesz1.hurwitzKernel (1 - s.val) (y / (2 * Real.pi))
  let Q := fun y : ℝ => μ + 2 * F y
  let f := fun y : ℝ => μ * (Q y)⁻¹
  have hne : ∀ y ∈ Ioo 0 (2 * Real.pi), Q y ≠ 0 := by
    intro y hy
    have hp : 0 < F y := by
      dsimp only [F]
      rw [← latticeRieszSymbol_eq_hurwitzKernel hz s ⟨y, hy⟩]
      exact latticeRieszSymbol_pos s _
    exact (by dsimp [Q]; positivity : 0 < Q y).ne'
  have hQ : ContDiffOn ℝ ∞ Q (Ioo 0 (2 * Real.pi)) :=
    contDiffOn_const.add (contDiffOn_const.mul (symbol_hurwitz_contDiff s))
  have hf : ContDiffOn ℝ 3 f (Ioo 0 (2 * Real.pi)) :=
    (contDiffOn_const.mul (hQ.inv hne)).of_le (by norm_num)
  have heq (y : ℝ) (hy : y ∈ Ioo 0 (2 * Real.pi)) :
      H (y : AddCircle (2 * Real.pi)) = (f y : ℂ) := by
    rw [hHe ⟨y, hy⟩, latticeRieszSymbol_eq_hurwitzKernel hz s ⟨y, hy⟩]
    simp only [f, Q, F, div_eq_mul_inv, add_comm μ]
  have hHs : ContDiffOn ℝ 3 (fun y : ℝ => H (y : AddCircle (2 * Real.pi)))
      (Ioo 0 (2 * Real.pi)) :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn hf).congr heq
  refine ⟨H, hH0, hHs, ?_, hHe⟩
  intro j hj y hy
  have hev : (fun z : ℝ => H (z : AddCircle (2 * Real.pi))) =ᶠ[𝓝 y]
      (fun z => (f z : ℂ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz
    exact heq z hz
  have hs : ContDiffAt ℝ j f y :=
    (hf.contDiffAt (isOpen_Ioo.mem_nhds hy)).of_le (by exact_mod_cast hj)
  have hi := iteratedDeriv_smul_const hs (1 : ℂ)
  simp only [Complex.real_smul, mul_one] at hi
  rw [hev.iteratedDeriv_eq j, hi, Complex.norm_real, Real.norm_eq_abs]
  dsimp only [f]
  rw [iteratedDeriv_const_mul_field, abs_mul, abs_of_pos hμ]
  have hh := mul_le_mul_of_nonneg_left (hb μ hμ j hj ⟨y, hy⟩) hμ.le
  simpa only [Q, F, symbolEndpointDistance, mul_assoc, mul_comm C μ] using hh

/-- The same actual multiplier supplies summable coefficients and the sharper
increment envelope, for the proof of Lemma 5.13. -/
theorem exists_resolvent_increment_coefficients (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : ℝ, 0 < μ → ∃ φ : ℤ → ℂ,
      (∀ n : ℤ, ‖φ (n + 1) - φ n‖ ≤ C * μ / (1 + |(n : ℝ)| ^ (3 - s.val))) ∧
      ∃ hφ : Summable (fun n => ‖φ n‖), latticeFourier φ hφ 0 = 0 ∧
        ∀ θ : Ioo (0 : ℝ) (2 * Real.pi),
          latticeFourier φ hφ θ.val = ((μ / (2 * latticeRieszSymbol s θ + μ) : ℝ) : ℂ) := by
  have hη : 0 < 1 - s.val := sub_pos.mpr s.property.2
  have hη1 : 1 - s.val < 1 := by linarith [s.property.1]
  obtain ⟨A, hA, hm⟩ := exists_resolvent_multiplier_three hz s
  obtain ⟨K, hK, hb⟩ := FractionalCuspFourier.coefficient_increment_decay hη hη1
  obtain ⟨_, _, hcusp⟩ := FractionalCuspFourier.fractional_cusp_fourier hη hη1
  refine ⟨K * A, mul_pos hK hA, ?_⟩
  intro μ hμ
  obtain ⟨H, hH0, hHs, hHd, hHe⟩ := hm μ hμ
  obtain ⟨_, hφ, hre, _, _⟩ := hcusp (A * μ) (mul_pos hA hμ) H hH0
    (hHs.of_le (by norm_num)) (fun j hj => hHd j (by omega))
  refine ⟨fourierCoeff H, ?_, hφ, ?_, ?_⟩
  · intro n
    simpa only [show 2 + (1 - s.val) = 3 - s.val by ring, mul_assoc] using
      hb (A * μ) (mul_pos hA hμ) H hHs hHd n
  · simpa only [AddCircle.coe_zero, hH0] using hre 0
  · intro θ
    rw [hre]
    exact hHe θ

end GlobalResolventKernelInternal

/-- The first-difference clause of the proof of Lemma 5.13, with a constant depending only on the exponent
and linear dependence on the prescribed shift. -/
theorem factorizationMatrix_increment_decay (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (a : ℝ) (ha : 0 < a) (B : ℝ) (h : Fin (N : ℕ)),
      |factorizationMatrix s N hN a ha B 0 (h + 1) -
        factorizationMatrix s N hN a ha B 0 h| ≤
          C * (a + B ^ 2 / a) *
            (1 + (Riesz1.cyclicIndexDistance N h 0 : ℝ)) ^ (-(3 - s.val)) := by
  have hq : 1 < 3 - s.val := by linarith [s.property.2]
  obtain ⟨A, hA, hb⟩ :=
    GlobalResolventKernelInternal.exists_resolvent_increment_coefficients hz s
  obtain ⟨T, hT, ht⟩ :=
    GlobalResolventKernelInternal.matrix_increment_bound_of_coefficients hq
  refine ⟨T * A, mul_pos hT hA, ?_⟩
  intro N hN a ha B h
  have hμ := factorization_shift_pos ha B
  obtain ⟨φ, hd, hφ, hzero, hfreq⟩ := hb (a + B ^ 2 / a) hμ
  have hh := ht s N hN a ha B φ hφ (A * (a + B ^ 2 / a)) (by positivity)
    hzero (fun k hk => hfreq ⟨_, cycleAngle_mem_Ioo N k hk⟩) hd h
  simpa only [mul_assoc] using hh

universe u v

/-- See the proof of Lemma 5.13 in the paper, in full. All constants precede
the cycle and factorization parameters. The polynomial bound is explicitly
the linear polynomial `Q_s(t) = K * t`. The row kernel is independent of its
base label, the exact nonzero constant mode is retained, and commutation is
stated for arbitrary scalar linear operators on their domains. -/
theorem global_resolvent_kernel (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ c C K : ℝ, 0 < c ∧ 0 < C ∧ 0 < K ∧
      ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (a : ℝ) (ha : 0 < a), a ≤ 1 →
      ∀ B : ℝ, 1 ≤ B → ∀ i : Fin (N : ℕ),
      let H := (2 : ℝ) • rieszMatrix s N hN
      let μ := a + B ^ 2 / a
      let A := factorizationMatrix s N hN a ha B
      let ℓ := ∑ j, H i j
      let f := fun h : Fin (N : ℕ) => A i (i + h)
      (∀ h : Fin (N : ℕ), f h = A 0 h ∧
        |f h| ≤ K * (1 + μ) /
          (1 + (Riesz1.cyclicIndexDistance N h 0 : ℝ)) ^ (2 - s.val) ∧
        |f (h + 1) - f h| ≤ K * (1 + μ) /
          (1 + (Riesz1.cyclicIndexDistance N h 0 : ℝ)) ^ (3 - s.val)) ∧
      (c * (N : ℝ) ^ (1 - s.val) ≤ ℓ ∧ ℓ ≤ C * (N : ℝ) ^ (1 - s.val)) ∧
      A *ᵥ (fun _ => 1) = (μ / (ℓ + μ)) • (fun _ => 1) ∧
      A * H = μ • 1 - μ • A ∧ A.PosSemidef ∧ ‖A‖ ≤ 1 ∧
      (∀ (V : Type u) (W : Type v) [AddCommGroup V] [Module ℝ V]
        [AddCommGroup W] [Module ℝ W] (L : V →ₗ[ℝ] W) (z : Fin (N : ℕ) → V)
        (k : Fin (N : ℕ)), L (∑ j, A k j • z j) = ∑ j, A k j • L (z j)) := by
  obtain ⟨c, C, hc, hC, hmass⟩ := global_reference_mass_bounds s
  obtain ⟨K₀, hK₀, he⟩ := factorizationMatrix_entry_decay hz s
  obtain ⟨K₁, hK₁, hd⟩ := factorizationMatrix_increment_decay hz s
  refine ⟨c, C, K₀ + K₁, hc, hC, by positivity, ?_⟩
  intro N hN a ha _ B _ i
  dsimp only
  have hf (h : Fin (N : ℕ)) : factorizationMatrix s N hN a ha B i (i + h) =
      factorizationMatrix s N hN a ha B 0 h := by
    simpa only [zero_add, add_comm h i] using
      factorizationMatrix_translate s N hN a ha B 0 h i
  have hμ := factorization_shift_pos ha B
  have hpoly₀ : K₀ * (a + B ^ 2 / a) ≤ (K₀ + K₁) * (1 + (a + B ^ 2 / a)) := by
    nlinarith [mul_pos hK₁ hμ]
  have hpoly₁ : K₁ * (a + B ^ 2 / a) ≤ (K₀ + K₁) * (1 + (a + B ^ 2 / a)) := by
    nlinarith [mul_pos hK₀ hμ]
  refine ⟨?_, hmass N hN i, ?_,
    (factorizationMatrix_mul_reference s N hN a ha B).1,
    (factorizationMatrix_posDef s N hN a ha B).posSemidef,
    factorizationMatrix_norm_le_one s N hN a ha B, ?_⟩
  · intro h
    refine ⟨hf h, ?_, ?_⟩
    · rw [hf]
      have hh := (he N hN a ha B h).trans
        (mul_le_mul_of_nonneg_right hpoly₀ (by positivity))
      simpa only [div_eq_mul_inv, Real.rpow_neg (by positivity :
        0 ≤ 1 + (Riesz1.cyclicIndexDistance N h 0 : ℝ))] using hh
    · rw [hf, hf]
      have hh := (hd N hN a ha B h).trans
        (mul_le_mul_of_nonneg_right hpoly₁ (by positivity))
      simpa only [div_eq_mul_inv, Real.rpow_neg (by positivity :
        0 ≤ 1 + (Riesz1.cyclicIndexDistance N h 0 : ℝ))] using hh
  · simpa only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum,
      rieszMatrix_row_sum] using factorizationMatrix_constant_mode s N hN a ha B
  · intro V W _ _ _ _ L z k
    exact component_matrix_commutes_linear _ L z k

end Riesz2
