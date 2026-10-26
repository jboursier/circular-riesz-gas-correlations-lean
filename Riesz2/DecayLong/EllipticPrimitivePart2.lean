/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.AngularPrimitive
public import Riesz2.DecayLong.EllipticPrimitive
public import Riesz2.ToMathlib.BoundedMatrixModes
public import Riesz2.ToMathlib.CyclicFourierL2

/-!
# Fourier modes for the elliptic primitive estimate

The finite real and imaginary Fourier modes of the weak
solution satisfy scalar shifted equations. The reference is twice the full
sampled Riesz matrix, with its exact nonzero Fourier eigenvalues.
-/

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset
open scoped BigOperators Fin.NatCast ComplexConjugate

namespace Riesz2.EllipticPrimitive

/-- The nonzero character has zero sum, before taking its real and imaginary
parts in the proof of Lemma 5.9. -/
theorem character_sum (N : ℕ+) (k : Fin (N : ℕ)) (hk : k ≠ 0) :
    (∑ j : Fin (N : ℕ),
      Complex.exp (Complex.I * (j.val : ℂ) * (cycleAngle N k : ℂ))) = 0 := by
  have h := cycleFourier_const (N := N) 1 k
  simpa only [cycleFourier, one_mul, ite_eq_right (by simpa using hk)] using h

/-- Each Fourier character has norm one, including the zero frequency. -/
theorem character_norm (N : ℕ+) (k j : Fin (N : ℕ)) :
    ‖Complex.exp (Complex.I * (j.val : ℂ) * (cycleAngle N k : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

/-- Exact character eigenvector identity for the sampled matrix,
the finite algebraic step of the proof of Lemma 5.9. -/
theorem character_eigenvector (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (k : Fin (N : ℕ)) (hk : k ≠ 0)
    (i : Fin (N : ℕ)) :
    (∑ j : Fin (N : ℕ), (sampledRieszKernel s N hN (j - i) : ℂ) *
      Complex.exp (Complex.I * (j.val : ℂ) * (cycleAngle N k : ℂ))) =
      (latticeRieszSymbol s ⟨cycleAngle N k, cycleAngle_mem_Ioo N k hk⟩ : ℂ) *
        Complex.exp (Complex.I * (i.val : ℂ) * (cycleAngle N k : ℂ)) := by
  let q : ℂ := ((Real.sqrt (N : ℝ))⁻¹ : ℝ)
  have hN0 : (0 : ℝ) < N := by positivity
  have hq : q ≠ 0 := Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_pos.mpr hN0).ne')
  have he := congrFun (cycleMatrix_mulVec_column
    (fun j => (sampledRieszKernel s N hN j : ℂ)) k) i
  rw [sampledRieszKernel_nonzero_eigenvalue s N hN k hk] at he
  simp only [Matrix.mulVec, dotProduct, cycleMatrix, cycleUnitary, Matrix.of_apply,
    Pi.smul_apply, smul_eq_mul] at he
  have hlabel (j : Fin (N : ℕ)) :
      Riesz1.labelOf N ((j.val : ℤ) - (i.val : ℤ)) = j - i := by
    apply Fin.ext
    apply Int.ofNat_inj.mp
    rw [Riesz1.APG.labelOf_val, Fin.val_sub]
    rw [Int.natCast_emod, Nat.cast_add, Nat.cast_sub (Nat.le_of_lt i.isLt)]
    rw [show ((N : ℕ) : ℤ) - i.val + j.val = ((j.val : ℤ) - i.val) + (N : ℕ) by ring]
    simp only [Int.add_emod, Int.emod_self, add_zero, Int.emod_emod]
  simp_rw [hlabel] at he
  apply mul_left_cancel₀ hq
  calc
    _ = ∑ j : Fin (N : ℕ), (sampledRieszKernel s N hN (j - i) : ℂ) *
        (q * Complex.exp (Complex.I * (j.val : ℂ) * (cycleAngle N k : ℂ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _; ring
    _ = _ := he
    _ = _ := by ring

/-- A row bound for the full-reference error controls its action against
every real coefficient vector bounded by one. -/
theorem error_mode_bound {ι : Type*} [Fintype ι]
    (E : Matrix ι ι ℝ) (c : ι → ℝ) (hc : ∀ j, |c j| ≤ 1)
    (B : ℝ) (hE : ∀ i, ∑ j, |E i j| ≤ B) (i : ι) :
    |∑ j, E i j * c j| ≤ B := by
  calc
    _ ≤ ∑ j, |E i j * c j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |E i j| := Finset.sum_le_sum (fun j _ => by
      rw [abs_mul]; simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hc j) (abs_nonneg (E i j)))
    _ ≤ _ := hE i

/-- Internal Fourier forcing step in the proof of Lemma 5.9, before
equation (5.32) of the paper. The actual error source is projected first, then its
pointwise ℓ¹ norm is bounded by column sums. `V` represents the spatial ℓ¹
norm of the solution. The final theorem supplies the error bound. -/
theorem fourier_mode_rhs_bound {α : Type*} [MeasurableSpace α] {ν : Measure α}
    (s : Riesz1.RieszExponent) (n m : ℕ+) (hm : 2 ≤ (m : ℕ))
    (K : ℕ) (C κ γ ε : ℝ) (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M)
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (β : ℝ) (hβ : 0 < β) (χ : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1)
    (hu : WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents (Fin (m : ℕ)))
      (fun i => if i = i₀ then χ else 0) u)
    (B : ℝ) (hB : 0 ≤ B)
    (herror : ∀ᵐ x ∂ν, ∀ i, ∑ j, |M x i j - 2 * sampledRieszKernel s m hm (j - i)| ≤ B)
    (V : Lp ℝ 2 ν)
    (hV : ∀ᵐ x ∂ν, V x = ∑ j, |(u j).val x|)
    (k : Fin (m : ℕ)) (hk : k ≠ 0) (t : ℂ →ₗ[ℝ] ℝ)
    (ht : ∀ j : Fin (m : ℕ),
      |t (Complex.exp (Complex.I * (j.val : ℂ) * (cycleAngle m k : ℂ)))| ≤ 1) :
    ‖∑ j, t (Complex.exp (Complex.I * (j.val : ℂ) * (cycleAngle m k : ℂ))) • (u j).val‖ ≤
      (β * 2 * latticeRieszSymbol s ⟨cycleAngle m k, cycleAngle_mem_Ioo m k hk⟩)⁻¹ *
        (‖χ‖ + β * B * ‖V‖) := by
  classical
  let c : Fin (m : ℕ) → ℝ := fun j =>
    t (Complex.exp (Complex.I * (j.val : ℂ) * (cycleAngle m k : ℂ)))
  let H : Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ :=
    fun i j => β * 2 * sampledRieszKernel s m hm (j - i)
  let b := β * 2 * latticeRieszSymbol s ⟨cycleAngle m k, cycleAngle_mem_Ioo m k hk⟩
  have hp (a : ℝ) (z : ℂ) : t ((a : ℂ) * z) = a * t z := by
    simpa only [Complex.real_smul, smul_eq_mul] using t.map_smul a z
  have hc : ∑ j, c j = 0 := by
    change (∑ j, t _) = 0
    rw [← map_sum, character_sum m k hk, map_zero]
  have hb : 0 < b := by
    have hs := lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _)
      (latticeRieszSymbol_lower s ⟨cycleAngle m k, cycleAngle_mem_Ioo m k hk⟩)
    dsimp only [b]
    positivity
  have heig (i) : ∑ j, H i j * c j = b * c i := by
    have he := congrArg t (character_eigenvector s m hm k hk i)
    simp only [map_sum, hp] at he
    dsimp only [H, b, c]
    calc
      _ = (β * 2) * ∑ j, sampledRieszKernel s m hm (j - i) *
          t (Complex.exp (Complex.I * (j.val : ℂ) * (cycleAngle m k : ℂ))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _; ring
      _ = _ := by rw [he]; ring
  have herr : ∀ᵐ x ∂ν, ∀ i, |∑ j, ((β • M x) i j - H i j) * c j| ≤ β * B := by
    filter_upwards [herror] with x hx
    intro i
    have h := error_mode_bound (fun i j => M x i j -
      2 * sampledRieszKernel s m hm (j - i)) c ht B (hx) i
    have he : (∑ j, ((β • M x) i j - H i j) * c j) =
        β * ∑ j, (M x i j - 2 * sampledRieszKernel s m hm (j - i)) * c j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Matrix.smul_apply, smul_eq_mul, H]
      ring
    rw [he, abs_mul, abs_of_pos hβ]
    exact mul_le_mul_of_nonneg_left h hβ.le
  obtain ⟨g, hgv, _, hg⟩ := BoundedMatrixModes.weak_mode Q (fun x => β • M x)
    (SchurRestriction.periodized_scaled_measurable β hM)
    (SchurRestriction.periodized_scaled_bounded β hM) H c hc b heig
    (β * B) (mul_nonneg hβ.le hB) herr
    (fun i => if i = i₀ then χ else 0) u hu
  -- Retain the actual Fourier projection of E u until after spatial summation.
  have hgn : ‖g‖ ≤ (β * B) * ‖V‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hgv, hV, herror, hM.2.1] with x hgx hvx hex hsym
    rw [hgx]
    have htranspose (i j) : M x i j - 2 * sampledRieszKernel s m hm (j - i) =
        M x j i - 2 * sampledRieszKernel s m hm (i - j) := by
      rw [hsym.1 i j, show j - i = -(i - j) by abel, sampledRieszKernel_even]
    have hid : (∑ i, ∑ j, (u i).val x * ((β • M x) i j - H i j) * c j) =
        β * ∑ j, c j * ∑ i,
          (M x j i - 2 * sampledRieszKernel s m hm (i - j)) * (u i).val x := by
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Matrix.smul_apply, smul_eq_mul, H]
      rw [show β * M x i j - β * 2 * sampledRieszKernel s m hm (j - i) =
        β * (M x i j - 2 * sampledRieszKernel s m hm (j - i)) by ring,
        htranspose i j]
      ring
    rw [hid, norm_mul, Real.norm_eq_abs, abs_of_pos hβ]
    have hprojection : |∑ j, c j * ∑ i,
        (M x j i - 2 * sampledRieszKernel s m hm (i - j)) * (u i).val x| ≤
        ∑ j, |∑ i, (M x j i - 2 * sampledRieszKernel s m hm (i - j)) * (u i).val x| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (ht j)
    have hcol (i) : ∑ j, |M x j i - 2 * sampledRieszKernel s m hm (i - j)| ≤ B := by
      simpa only [← htranspose] using hex i
    have hspatial := FiniteSchurBounds.sum_norm_le
      (fun j i => M x j i - 2 * sampledRieszKernel s m hm (i - j))
      (fun i => (u i).val x) hcol
    simp only [smul_eq_mul, Real.norm_eq_abs] at hspatial
    have hV0 : 0 ≤ V x := by rw [hvx]; positivity
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg hV0, hvx]
    exact (mul_le_mul_of_nonneg_left (hprojection.trans hspatial) hβ.le).trans_eq (by ring)
  let v : Q.1 := ∑ j, c j • u j
  have hv : v.val = ∑ j, c j • (u j).val := by simp [v]
  have hres := scalar_resolvent_bound_internal Q hQ hb
    ((∑ i, c i • (if i = i₀ then χ else 0)) - g) v (by
      intro w
      simpa only [hv] using hg w)
  rw [hv] at hres
  have hf : (∑ i, c i • (if i = i₀ then χ else 0)) = c i₀ • χ := by simp
  rw [hf] at hres
  have hfn : ‖c i₀ • χ‖ ≤ ‖χ‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (ht i₀) (norm_nonneg χ)
  exact hres.trans (mul_le_mul_of_nonneg_left
    ((norm_sub_le _ _).trans (add_le_add hfn hgn)) (inv_nonneg.mpr hb.le))

/-- The angular harmonic sum used just before equation (5.32) in the proof of
Lemma 5.9 of the paper, with the zero frequency omitted literally. -/
theorem angular_frequency_inverse_harmonic :
    ∃ H : ℝ, 0 < H ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) →
      (N : ℝ)⁻¹ * (∑ k : Fin (N : ℕ), if k = 0 then 0 else
        (FourierMultiplierKernels.angularRadius (cycleAngle N k))⁻¹) ≤
          H * Real.log (2 * (N : ℝ)) := by
  obtain ⟨H, hH, hh⟩ := frequency_inverse_harmonic
  refine ⟨H, hH, fun N hN => le_trans ?_ (hh N hN)⟩
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k = 0
  · simp [hk, DiscreteInterpolation.frequencyRadius, cycleAngle]
  · rw [ite_eq_right hk]
    obtain ⟨hr, hrρ, _⟩ := DiscreteInterpolation.angularRadius_cycle_comparison N k hk
    exact inv_anti₀ hr hrρ

/-- The half-power singularity of the angular primitive divided by the
reference eigenvalue in the proof of Lemma 5.9 of the paper. -/
theorem angular_primitive_symbol_bound (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ+) (k : Fin (N : ℕ)) (hk : k ≠ 0),
      FourierMultiplierKernels.angularRadius (cycleAngle N k) ^ (-(3 / 2 - s.val)) *
        (2 * latticeRieszSymbol s ⟨cycleAngle N k, cycleAngle_mem_Ioo N k hk⟩)⁻¹ ≤
      A * FourierMultiplierKernels.angularRadius (cycleAngle N k) ^ (-1 / 2 : ℝ) := by
  obtain ⟨c, _, hc, _, hb⟩ := latticeRieszSymbol_power_bounds hz s
  refine ⟨(2 * c)⁻¹, by positivity, fun N k hk => ?_⟩
  let θ : Set.Ioo (0 : ℝ) (2 * Real.pi) :=
    ⟨cycleAngle N k, cycleAngle_mem_Ioo N k hk⟩
  let ρ := FourierMultiplierKernels.angularRadius (cycleAngle N k)
  have he : symbolEndpointDistance θ = ρ :=
    (FourierMultiplierKernels.angularRadius_eq_min (Set.Ioo_subset_Icc_self θ.property)).symm
  have hρ : 0 < ρ := he ▸ symbolEndpointDistance_pos θ
  have hinv : (2 * latticeRieszSymbol s θ)⁻¹ ≤ (2 * c)⁻¹ * ρ ^ (1 - s.val) := by
    have hh := inv_anti₀ (by positivity : 0 < 2 * (c * ρ ^ (s.val - 1)))
      (mul_le_mul_of_nonneg_left (by simpa only [he] using (hb θ).1)
        (by norm_num : (0 : ℝ) ≤ 2))
    apply hh.trans_eq
    rw [mul_inv, mul_inv, ← Real.rpow_neg hρ.le]
    rw [show -(s.val - 1) = 1 - s.val by ring, mul_inv]
    ring
  change ρ ^ (-(3 / 2 - s.val)) * (2 * latticeRieszSymbol s θ)⁻¹ ≤ _
  calc
    _ ≤ ρ ^ (-(3 / 2 - s.val)) * ((2 * c)⁻¹ * ρ ^ (1 - s.val)) :=
      mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg hρ.le _)
    _ = _ := by
      rw [mul_left_comm, ← Real.rpow_add hρ]
      congr 2
      ring

/-- Internal Parseval step for equation (5.32) in the proof of Lemma 5.9
of the paper, retaining the L² norm of the pointwise spatial ℓ¹ norm.
The error-row premise belongs only to this internal helper. -/
theorem angular_primitive_rhs_estimate_internal (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent) :
    ∃ D : ℝ, 0 < D ∧
    ∀ {α : Type*} [MeasurableSpace α] {ν : Measure α}
      (n m : ℕ+) (hm : 2 ≤ (m : ℕ)) (K : ℕ) (C κ γ ε : ℝ)
      (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ),
    PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M →
    ∀ (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q →
    ∀ (β : ℝ), 0 < β → ∀ (χ : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents (Fin (m : ℕ)))
      (fun i => if i = i₀ then χ else 0) u →
    ∀ (B : ℝ), 0 ≤ B →
    (∀ᵐ x ∂ν, ∀ i, ∑ j, |M x i j - 2 * sampledRieszKernel s m hm (j - i)| ≤ B) →
    let J := fun x => cycleFourierInv m (fun k =>
      (if k = 0 then 0 else (FourierMultiplierKernels.angularRadius (cycleAngle m k) ^
        (-(3 / 2 - s.val)) : ℝ)) * cycleFourier m (fun j => ((u j).val x : ℂ)) k)
    Integrable (fun x => ∑ i, ‖J x i‖ ^ 2) ν ∧
      Real.sqrt (∫ x, ∑ i, ‖J x i‖ ^ 2 ∂ν) ≤
        D * Real.sqrt (Real.log (2 * (m : ℝ))) *
          (β⁻¹ * ‖χ‖ + B * (eLpNorm (fun x => ∑ j, |(u j).val x|) 2 ν).toReal) := by
  obtain ⟨A, hA, hsymbol⟩ := angular_primitive_symbol_bound hz s
  obtain ⟨H, hH, hh⟩ := angular_frequency_inverse_harmonic
  refine ⟨Real.sqrt (2 * A ^ 2 * H), by positivity,
    fun {α} _ {ν} n m hm K C κ γ ε M hM Q hQ β hβ χ i₀ u hu B hB herror => ?_⟩
  let ρ := fun k => FourierMultiplierKernels.angularRadius (cycleAngle m k)
  let p : Fin (m : ℕ) → ℝ := fun k => if k = 0 then 0 else ρ k ^ (-(3 / 2 - s.val))
  have hVmem : MemLp (fun x => ∑ j, |(u j).val x|) 2 ν := by
    simpa only [Real.norm_eq_abs] using
      memLp_finsetSum Finset.univ (fun j _ => (Lp.memLp (u j).val).norm)
  let V := hVmem.toLp (fun x => ∑ j, |(u j).val x|)
  have hVnorm : ‖V‖ = (eLpNorm (fun x => ∑ j, |(u j).val x|) 2 ν).toReal :=
    Lp.norm_toLp _ hVmem
  let T := β⁻¹ * ‖χ‖ + B * (eLpNorm (fun x => ∑ j, |(u j).val x|) 2 ν).toReal
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hρ (k) (hk : k ≠ 0) : 0 < ρ k := by
    obtain ⟨hr, hc, _⟩ := DiscreteInterpolation.angularRadius_cycle_comparison m k hk
    exact hr.trans_le hc
  have hmode (k) (hk : k ≠ 0) (t : ℂ →ₗ[ℝ] ℝ)
      (ht : ∀ j : Fin (m : ℕ),
        |t (Complex.exp (Complex.I * (j.val : ℂ) * (cycleAngle m k : ℂ)))| ≤ 1) :
      p k ^ 2 * ‖∑ j, t (Complex.exp (Complex.I * (j.val : ℂ) *
        (cycleAngle m k : ℂ))) • (u j).val‖ ^ 2 ≤ A ^ 2 * (ρ k)⁻¹ * T ^ 2 := by
    let S := latticeRieszSymbol s ⟨cycleAngle m k, cycleAngle_mem_Ioo m k hk⟩
    have hS : 0 < S := lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _)
      (latticeRieszSymbol_lower s _)
    have hp : 0 ≤ p k := by
      dsimp only [p]
      rw [ite_eq_right hk]
      exact Real.rpow_nonneg (hρ k hk).le _
    have hmde := fourier_mode_rhs_bound s n m hm K C κ γ ε M hM Q hQ β hβ χ i₀ u hu
      B hB herror V hVmem.coeFn_toLp k hk t ht
    rw [hVnorm] at hmde
    have hbnd : p k * ‖∑ j, t (Complex.exp (Complex.I * (j.val : ℂ) *
        (cycleAngle m k : ℂ))) • (u j).val‖ ≤ A * ρ k ^ (-1 / 2 : ℝ) * T := by
      calc
        _ ≤ p k * ((β * 2 * S)⁻¹ * (‖χ‖ + β * B * (eLpNorm (fun x => ∑ j, |(u j).val x|) 2 ν).toReal)) :=
          mul_le_mul_of_nonneg_left hmde hp
        _ = (p k * (2 * S)⁻¹) * T := by
          dsimp only [T]
          field_simp
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ hT
          simpa only [p, ite_eq_right hk] using hsymbol m k hk
    have hsquare := pow_le_pow_left₀ (mul_nonneg hp (norm_nonneg _)) hbnd 2
    have he : (ρ k ^ (-1 / 2 : ℝ)) ^ 2 = (ρ k)⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hρ k hk).le]
      norm_num [Real.rpow_neg_one]
    simpa only [mul_pow, he] using hsquare
  let R : Fin (m : ℕ) → Lp ℝ 2 ν := fun k => ∑ j,
    (Complex.exp (Complex.I * (j.val : ℂ) * (cycleAngle m k : ℂ))).re • (u j).val
  let I : Fin (m : ℕ) → Lp ℝ 2 ν := fun k => ∑ j,
    (Complex.exp (Complex.I * (j.val : ℂ) * (cycleAngle m k : ℂ))).im • (u j).val
  have hterm (k : Fin (m : ℕ)) :
      p k ^ 2 * (‖R k‖ ^ 2 + ‖I k‖ ^ 2) ≤ (2 * A ^ 2 * T ^ 2) * (ρ k)⁻¹ := by
    by_cases hk : k = 0
    · subst k
      simp only [p, ite_eq_left rfl, zero_pow (by norm_num : 2 ≠ 0), zero_mul]
      simp [ρ, FourierMultiplierKernels.angularRadius, cycleAngle]
    have hr := hmode k hk Complex.reLm (fun j =>
      (Complex.abs_re_le_norm _).trans_eq (character_norm m k j))
    have hi := hmode k hk Complex.imLm (fun j =>
      (Complex.abs_im_le_norm _).trans_eq (character_norm m k j))
    change p k ^ 2 * ‖R k‖ ^ 2 ≤ _ at hr
    change p k ^ 2 * ‖I k‖ ^ 2 ≤ _ at hi
    nlinarith
  obtain ⟨hint, heq⟩ := CyclicFourierL2.multiplier_parseval m p (fun j => (u j).val)
  refine ⟨hint, ?_⟩
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  have hlog : 0 ≤ Real.log (2 * (m : ℝ)) := Real.log_nonneg (by
    have hm0 : (1 : ℝ) ≤ m := by exact_mod_cast m.pos
    linarith)
  rw [heq]
  calc
    _ ≤ (m : ℝ)⁻¹ * ∑ k, (2 * A ^ 2 * T ^ 2) * (ρ k)⁻¹ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => hterm k)) (by positivity)
    _ = (2 * A ^ 2 * T ^ 2) * ((m : ℝ)⁻¹ * ∑ k, (ρ k)⁻¹) := by
      rw [← Finset.mul_sum]; ring
    _ ≤ (2 * A ^ 2 * T ^ 2) * (H * Real.log (2 * (m : ℝ))) :=
      mul_le_mul_of_nonneg_left (by
        convert hh m hm using 1
        congr 2
        funext k
        by_cases hk : k = 0
        · subst k
          simp [ρ, FourierMultiplierKernels.angularRadius, cycleAngle]
        · simp only [ite_eq_right hk]
          rfl) (by positivity)
    _ = _ := by
      simp only [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * A ^ 2 * H), Real.sq_sqrt hlog]
      ring

/-- The angular resolvent bound before logarithm absorption in Lemma 5.9
of the paper. Both the loss exponent and the prefactor precede ε. The
spatial weight is exactly `W_(1/2)` and the single logarithm is retained.
The prefactor is uniform for `β ≥ βlo > 0`. Both energies are integrable. -/
theorem elliptic_primitive_angular_radius_uniform (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (κstar γstar : ℝ) (hκstar : 0 < κstar) (M₀ : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (Cstar : ℝ), 1 ≤ Cstar → ∀ βlo : ℝ, 0 < βlo → ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ), 0 < ε →
    ∀ (β : ℝ), βlo ≤ β →
    ∀ {α : Type*} [MeasurableSpace α] (ν : Measure α)
      (n m : ℕ+) (hm : 2 ≤ (m : ℕ))
      (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ),
    PeriodizedMatrixBounds (ν := ν) s n m hm (⌊(n : ℝ) ^ ε⌋₊ ^ M₀)
      Cstar κstar γstar ε M →
    ∀ (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q →
    ∀ (χ : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents (Fin (m : ℕ)))
      (fun i => if i = i₀ then χ else 0) u →
    let J := fun x => DiscreteInterpolation.angularPrimitive m (3 / 2 - s.val)
      (fun j => ((u j).val x : ℂ))
    let w := fun j => weightRadius m j i₀ ^ (1 / 2 : ℝ)
    Integrable (fun x => ∑ i, ‖J x i‖ ^ 2) ν ∧
    Integrable (fun x => ∑ j, (w j * (u j).val x) ^ 2) ν ∧
      Real.sqrt (∫ x, ∑ i, ‖J x i‖ ^ 2 ∂ν) ≤
        C * (n : ℝ) ^ (κ * ε) * Real.log (2 * (m : ℝ)) *
          (‖χ‖ + Real.sqrt (∫ x, ∑ j, (w j * (u j).val x) ^ 2 ∂ν)) := by
  obtain ⟨T, Dshort, hT, hDshort, hfull⟩ := full_reference_error_sums s
  let κ := κstar + M₀
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  obtain ⟨D, hD, hprimitive⟩ := angular_primitive_rhs_estimate_internal hz s
  obtain ⟨H, hH, hh⟩ := radius_inverse_harmonic
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let L₀ := Real.sqrt (Real.log 2)
  have hL₀ : 0 < L₀ := Real.sqrt_pos.mpr hlog2
  refine ⟨κ, hκ, fun Cstar hCstar βlo hβlo => ?_⟩
  let B₀ := T * Cstar + 2 * Dshort
  have hB₀ : 0 < B₀ := by dsimp only [B₀]; positivity
  let F := βlo⁻¹ / L₀ + B₀ * Real.sqrt H
  have hF : 0 < F := by dsimp only [F]; positivity
  refine ⟨D * F, mul_pos hD hF, fun ε hε β hβloβ {α} _ ν n m hm M hM Q hQ χ i₀ u hu => ?_⟩
  have hβ : 0 < β := hβlo.trans_le hβloβ
  have hn : 1 ≤ (n : ℝ) := by exact_mod_cast n.pos
  have hK : 1 ≤ ⌊(n : ℝ) ^ ε⌋₊ ^ M₀ :=
    one_le_pow₀ (one_le_floor_and_floor_le (Real.one_le_rpow hn hε.le)).1
  let P := (n : ℝ) ^ (κ * ε)
  have hP : 1 ≤ P := Real.one_le_rpow hn (mul_nonneg hκ.le hε.le)
  have hP0 : 0 ≤ P := le_trans zero_le_one hP
  have hn0 : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn
  have hmain : (n : ℝ) ^ (κstar * ε) ≤ P :=
    Real.rpow_le_rpow_of_exponent_le hn (by dsimp only [κ]; nlinarith)
  have hfloor : ((⌊(n : ℝ) ^ ε⌋₊ ^ M₀ : ℕ) : ℝ) ≤ (n : ℝ) ^ ((M₀ : ℝ) * ε) := by
    rw [Nat.cast_pow, mul_comm (M₀ : ℝ), Real.rpow_mul_natCast hn0.le]
    exact pow_le_pow_left₀ (by positivity) (Nat.floor_le (by positivity)) _
  have hshort : ((⌊(n : ℝ) ^ ε⌋₊ ^ M₀ : ℕ) : ℝ) ^ (1 - s.val) ≤ P := by
    calc
      _ ≤ ((n : ℝ) ^ ((M₀ : ℝ) * ε)) ^ (1 - s.val) :=
        Real.rpow_le_rpow (by positivity) hfloor (by linarith [s.property.2])
      _ = (n : ℝ) ^ ((M₀ : ℝ) * ε * (1 - s.val)) := (Real.rpow_mul hn0.le _ _).symm
      _ ≤ P := Real.rpow_le_rpow_of_exponent_le hn (by
        dsimp only [κ]
        nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ M₀) hε.le,
          mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ M₀) hε.le) s.property.1.le])
  have herr : ∀ᵐ x ∂ν, ∀ i, ∑ j, |M x i j - 2 * sampledRieszKernel s m hm (j - i)| ≤ B₀ * P := by
    filter_upwards [hfull ν n m hm _ hK Cstar κstar γstar ε (by linarith) M hM] with x hx
    intro i
    calc
      _ ≤ T * Cstar * (n : ℝ) ^ (κstar * ε) +
          2 * Dshort * ((⌊(n : ℝ) ^ ε⌋₊ ^ M₀ : ℕ) : ℝ) ^ (1 - s.val) := (hx i).1
      _ ≤ T * Cstar * P + 2 * Dshort * P :=
        add_le_add (mul_le_mul_of_nonneg_left hmain (by positivity))
          (mul_le_mul_of_nonneg_left hshort (by positivity))
      _ = _ := by dsimp only [B₀]; ring
  obtain ⟨hJ, hbound⟩ := hprimitive n m hm _ Cstar κstar γstar ε M hM Q hQ β hβ χ i₀ u hu
    (B₀ * P) (mul_nonneg hB₀.le hP0) herr
  let w := fun j => weightRadius m j i₀ ^ (1 / 2 : ℝ)
  obtain ⟨hw, hwint⟩ := CyclicFourierL2.weighted_integral_sq w (fun j => (u j).val)
  refine ⟨hJ, hw, ?_⟩
  rw [hwint]
  let X := Real.sqrt (∑ j, (w j * ‖(u j).val‖) ^ 2)
  let L := Real.sqrt (Real.log (2 * (m : ℝ)))
  have hX : 0 ≤ X := Real.sqrt_nonneg _
  have hlog : Real.log 2 ≤ Real.log (2 * (m : ℝ)) :=
    Real.log_le_log (by norm_num) (by
      have hm0 : (1 : ℝ) ≤ m := by exact_mod_cast m.pos
      linarith)
  have hL : L₀ ≤ L := Real.sqrt_le_sqrt hlog
  have hL0 : 0 ≤ L := Real.sqrt_nonneg _
  have hLs : L ^ 2 = Real.log (2 * (m : ℝ)) :=
    Real.sq_sqrt (hlog2.le.trans hlog)
  have hsum : (eLpNorm (fun x => ∑ j, |(u j).val x|) 2 ν).toReal ≤
      Real.sqrt H * L * X := by
    have hmV : MemLp (fun x => ∑ j, |(u j).val x|) 2 ν := by
      simpa only [Real.norm_eq_abs] using
        memLp_finsetSum Finset.univ (fun j _ => (Lp.memLp (u j).val).norm)
    let V := hmV.toLp (fun x => ∑ j, |(u j).val x|)
    have hnV : ‖V‖ = (eLpNorm (fun x => ∑ j, |(u j).val x|) 2 ν).toReal :=
      Lp.norm_toLp _ hmV
    rw [← hnV]
    rw [← Real.sqrt_sq (norm_nonneg V)]
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    have hpoint : ∀ᵐ x ∂ν, V x ^ 2 ≤
        (H * Real.log (2 * (m : ℝ))) * ∑ j, (w j * (u j).val x) ^ 2 := by
      filter_upwards [hmV.coeFn_toLp] with x hx
      rw [hx]
      have hcs := radius_weight_cauchy m i₀ (1 / 2) (fun j => (u j).val x)
      norm_num only [sub_self, Real.rpow_zero, one_mul] at hcs
      have hroot := Real.sqrt_le_sqrt (hh m hm i₀)
      have hb := hcs.trans (mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _))
      have hs := pow_le_pow_left₀ (Finset.sum_nonneg (fun j _ => abs_nonneg _)) hb 2
      rw [mul_pow, Real.sq_sqrt (mul_nonneg hH.le (hlog2.le.trans hlog)),
        Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg _))] at hs
      exact hs
    have hi := integral_mono_ae (Lp.memLp V).integrable_sq (hw.const_mul _) hpoint
    rw [CyclicFourierL2.integral_sq, integral_const_mul, hwint] at hi
    dsimp only [X]
    rw [mul_pow, mul_pow, Real.sq_sqrt hH.le, hLs,
      Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg _))]
    exact hi
  have hβinv : β⁻¹ ≤ βlo⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hβlo hβloβ
  have hcoef : β⁻¹ ≤ F * P * L := by
    calc
      _ ≤ βlo⁻¹ := hβinv
      _ = (βlo⁻¹ / L₀) * L₀ := by field_simp
      _ ≤ (βlo⁻¹ / L₀) * L := mul_le_mul_of_nonneg_left hL (by positivity)
      _ ≤ (βlo⁻¹ / L₀) * P * L := by
        have := mul_le_mul_of_nonneg_left hP (by positivity : 0 ≤ βlo⁻¹ / L₀)
        nlinarith
      _ ≤ _ := by
        have : βlo⁻¹ / L₀ ≤ F := le_add_of_nonneg_right (mul_nonneg hB₀.le (Real.sqrt_nonneg H))
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hP0) hL0
  have herrcoef : B₀ * Real.sqrt H ≤ F :=
    le_add_of_nonneg_left (by positivity : 0 ≤ βlo⁻¹ / L₀)
  have hT : β⁻¹ * ‖χ‖ + B₀ * P * (eLpNorm (fun x => ∑ j, |(u j).val x|) 2 ν).toReal ≤ F * P * L * (‖χ‖ + X) := by
    have hχ := mul_le_mul_of_nonneg_right hcoef (norm_nonneg χ)
    have he := mul_le_mul_of_nonneg_left hsum (mul_nonneg hB₀.le hP0)
    have he' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right herrcoef hP0) hL0) hX
    nlinarith
  calc
    _ ≤ D * L * (β⁻¹ * ‖χ‖ + B₀ * P * (eLpNorm (fun x => ∑ j, |(u j).val x|) 2 ν).toReal) := hbound
    _ ≤ D * L * (F * P * L * (‖χ‖ + X)) :=
      mul_le_mul_of_nonneg_left hT (mul_nonneg hD.le hL0)
    _ = _ := by
      change D * L * (F * P * L * (‖χ‖ + X)) =
        D * F * P * Real.log (2 * (m : ℝ)) * (‖χ‖ + X)
      rw [← hLs]
      ring


/-- Before logarithm absorption in display equation (5.32) in the proof of Lemma 5.9 of the paper:
the fractional primitive of a zero-sum weak solution has the asserted mixed
L² bound with exactly the paper's `W_(1/2)` weight. The loss exponent precedes epsilon, the matrix prefactor and temperature. The
prefactor is uniform on every half-line `β ≥ βlo > 0`, hence locally uniform
on `(0,∞)`. Both squared-norm integrals are explicitly integrable.

The result holds on every closed scalar Dirichlet form and every cycle of
size at least two, so it also applies to the scalar probability spaces and
the periods and cutoffs of Subsection 5.1. -/
theorem elliptic_primitive_angular_radius (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (κstar γstar : ℝ) (hκstar : 0 < κstar) (M₀ : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (ε : ℝ), 0 < ε →
    ∀ (Cstar : ℝ), 1 ≤ Cstar → ∀ βlo : ℝ, 0 < βlo → ∃ C : ℝ, 0 < C ∧
    ∀ (β : ℝ), βlo ≤ β →
    ∀ {α : Type*} [MeasurableSpace α] (ν : Measure α)
      (n m : ℕ+) (hm : 2 ≤ (m : ℕ))
      (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ),
    PeriodizedMatrixBounds (ν := ν) s n m hm (⌊(n : ℝ) ^ ε⌋₊ ^ M₀)
      Cstar κstar γstar ε M →
    ∀ (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q →
    ∀ (χ : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents (Fin (m : ℕ)))
      (fun i => if i = i₀ then χ else 0) u →
    let J := fun x => DiscreteInterpolation.angularPrimitive m (3 / 2 - s.val)
      (fun j => ((u j).val x : ℂ))
    let w := fun j => weightRadius m j i₀ ^ (1 / 2 : ℝ)
    Integrable (fun x => ∑ i, ‖J x i‖ ^ 2) ν ∧
    Integrable (fun x => ∑ j, (w j * (u j).val x) ^ 2) ν ∧
      Real.sqrt (∫ x, ∑ i, ‖J x i‖ ^ 2 ∂ν) ≤
        C * (n : ℝ) ^ (κ * ε) * Real.log (2 * (m : ℝ)) *
          (‖χ‖ + Real.sqrt (∫ x, ∑ j, (w j * (u j).val x) ^ 2 ∂ν)) := by
  obtain ⟨κ, hκ, hb⟩ := elliptic_primitive_angular_radius_uniform hz s κstar γstar hκstar M₀
  exact ⟨κ, hκ, fun ε hε Cstar hCstar βlo hβlo => by
    obtain ⟨C, hC, hc⟩ := hb Cstar hCstar βlo hβlo
    exact ⟨C, hC, hc ε hε⟩⟩


end Riesz2.EllipticPrimitive
