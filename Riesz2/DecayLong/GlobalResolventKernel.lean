/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.GlobalFactorization

/-!
# Algebra and constant mode of the global resolvent

Exact identities and positivity for the literal factorization matrix of Subsection 5.4. These are the algebraic clauses of the proof of Lemma 5.13.
-/

public section

noncomputable section

open Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace Riesz2

/-- The shift in Subsection 5.4 is strictly positive. -/
theorem factorization_shift_pos {a : ℝ} (ha : 0 < a) (B : ℝ) :
    0 < a + B ^ 2 / a := by positivity

/-- The shifted reference in Subsection 5.4 is positive definite, so its
nonsingular inverse is its actual inverse. -/
theorem factorization_shifted_posDef (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (a : ℝ) (ha : 0 < a) (B : ℝ) :
    ((2 : ℝ) • rieszMatrix s N hN +
      (a + B ^ 2 / a) • (1 : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)).PosDef :=
  ((rieszMatrix_posDef s N hN).smul two_pos).add
    (PosDef.one.smul (factorization_shift_pos ha B))

/-- Positive definiteness, hence also positive semidefiniteness, in the proof of Lemma 5.13. -/
theorem factorizationMatrix_posDef (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (a : ℝ) (ha : 0 < a) (B : ℝ) :
    (factorizationMatrix s N hN a ha B).PosDef :=
  (factorization_shifted_posDef s N hN a ha B).inv.smul (factorization_shift_pos ha B)

/-- Both inverse identities for the global factorization matrix
(the proof of Lemma 5.13). -/
theorem factorizationMatrix_shifted_mul (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (a : ℝ) (ha : 0 < a) (B : ℝ) :
    let H := (2 : ℝ) • rieszMatrix s N hN
    let μ := a + B ^ 2 / a
    let A := factorizationMatrix s N hN a ha B
    A * (H + μ • 1) = μ • 1 ∧ (H + μ • 1) * A = μ • 1 := by
  dsimp only
  have hdet := isUnit_iff_ne_zero.mpr
    (factorization_shifted_posDef s N hN a ha B).det_pos.ne'
  constructor
  · rw [factorizationMatrix, smul_mul, nonsing_inv_mul _ hdet]
  · rw [factorizationMatrix, Matrix.mul_smul, mul_nonsing_inv _ hdet]

/-- The exact resolvent identity `A H = μ I - μ A`, on both sides. This is the
last identity in the proof of Lemma 5.13. -/
theorem factorizationMatrix_mul_reference (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (a : ℝ) (ha : 0 < a) (B : ℝ) :
    let H := (2 : ℝ) • rieszMatrix s N hN
    let μ := a + B ^ 2 / a
    let A := factorizationMatrix s N hN a ha B
    A * H = μ • 1 - μ • A ∧ H * A = μ • 1 - μ • A := by
  obtain ⟨hl, hr⟩ := factorizationMatrix_shifted_mul s N hN a ha B
  dsimp only at hl hr ⊢
  rw [mul_add, Matrix.mul_smul (factorizationMatrix s N hN a ha B) (a + B ^ 2 / a), mul_one] at hl
  rw [add_mul, smul_mul (a + B ^ 2 / a), one_mul] at hr
  exact ⟨eq_sub_of_add_eq hl, eq_sub_of_add_eq hr⟩

/-- The global resolvent commutes with the reference matrix
(the proof of Lemma 5.13). -/
theorem factorizationMatrix_commute (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (a : ℝ) (ha : 0 < a) (B : ℝ) :
    Commute (factorizationMatrix s N hN a ha B) ((2 : ℝ) • rieszMatrix s N hN) := by
  obtain ⟨hl, hr⟩ := factorizationMatrix_mul_reference s N hN a ha B
  exact hl.trans hr.symm

/-- The Loewner contraction bound for the proof of Lemma 5.13. -/
theorem factorizationMatrix_le_one (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (a : ℝ) (ha : 0 < a) (B : ℝ) :
    factorizationMatrix s N hN a ha B ≤ 1 := by
  let H := (2 : ℝ) • rieszMatrix s N hN
  let μ := a + B ^ 2 / a
  let K := H + μ • (1 : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
  have hp : H.PosDef := (rieszMatrix_posDef s N hN).smul two_pos
  have hk : K.PosDef := factorization_shifted_posDef s N hN a ha B
  have hdet : IsUnit K.det := isUnit_iff_ne_zero.mpr hk.det_pos.ne'
  have hKi : K⁻¹ * K = 1 := nonsing_inv_mul _ hdet
  have hKi' : K * K⁻¹ = 1 := mul_nonsing_inv _ hdet
  have hHsym : Hᴴ = H := hp.isHermitian
  have hKsym : (K⁻¹)ᴴ = K⁻¹ := hk.inv.isHermitian
  have hHH : (H * H).PosSemidef := by
    simpa only [hHsym] using posSemidef_conjTranspose_mul_self H
  have hmid : (H * H + μ • H).PosSemidef :=
    hHH.add (hp.posSemidef.smul (factorization_shift_pos ha B).le)
  have hc := hmid.conjTranspose_mul_mul_same K⁻¹
  rw [hKsym] at hc
  have heq : K⁻¹ * (H * H + μ • H) * K⁻¹ =
      1 - factorizationMatrix s N hN a ha B := by
    have hm : H * H + μ • H = H * K := by
      simp only [K, mul_add, Matrix.mul_smul, mul_one]
    rw [hm, Matrix.mul_assoc, Matrix.mul_assoc, hKi', mul_one]
    have hh : H = K - μ • 1 := by dsimp only [K]; abel
    rw [hh, mul_sub, hKi, Matrix.mul_smul, mul_one]
    rfl
  rw [heq] at hc
  exact Matrix.le_iff.mpr hc

/-- The operator norm clause of the proof of Lemma 5.13. -/
theorem factorizationMatrix_norm_le_one (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (a : ℝ) (ha : 0 < a) (B : ℝ) :
    ‖factorizationMatrix s N hN a ha B‖ ≤ 1 := by
  let H := (2 : ℝ) • rieszMatrix s N hN
  let μ := a + B ^ 2 / a
  let K := H + μ • (1 : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
  have hμ : 0 < μ := factorization_shift_pos ha B
  have hp : H.PosDef := (rieszMatrix_posDef s N hN).smul two_pos
  have hk : K.PosDef := factorization_shifted_posDef s N hN a ha B
  have hdet : IsUnit K.det := isUnit_iff_ne_zero.mpr hk.det_pos.ne'
  have hquad (u : Fin (N : ℕ) → ℝ) :
      (factorizationMatrix s N hN a ha B *ᵥ u) ⬝ᵥ
        (factorizationMatrix s N hN a ha B *ᵥ u) ≤ u ⬝ᵥ u := by
    obtain ⟨v, rfl⟩ : ∃ v, u = K *ᵥ v :=
      ⟨K⁻¹ *ᵥ u, by rw [mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]⟩
    have hav : factorizationMatrix s N hN a ha B *ᵥ (K *ᵥ v) = μ • v := by
      change (μ • K⁻¹) *ᵥ (K *ᵥ v) = _
      rw [smul_mulVec, mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
    have hKv : K *ᵥ v = H *ᵥ v + μ • v := by
      dsimp only [K]
      rw [add_mulVec, smul_mulVec μ, one_mulVec]
    have hpos : 0 ≤ v ⬝ᵥ (H *ᵥ v) := by
      simpa only [star_trivial] using hp.posSemidef.dotProduct_mulVec_nonneg v
    have hsq := dotProduct_self_nonneg' (H *ᵥ v)
    rw [hav, hKv]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul]
    rw [dotProduct_comm (H *ᵥ v) v]
    nlinarith [mul_nonneg hμ.le hpos]
  change ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin (N : ℕ)) (factorizationMatrix s N hN a ha B)‖ ≤ 1
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [one_mul]
  have hsq : ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin (N : ℕ))
      (factorizationMatrix s N hN a ha B)) u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, Matrix.ofLp_toEuclideanCLM,
      Real.norm_eq_abs, sq_abs]
    simpa only [dotProduct, pow_two] using hquad u.ofLp
  nlinarith [norm_nonneg ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin (N : ℕ))
    (factorizationMatrix s N hN a ha B)) u), norm_nonneg u]

/-- The row sum of the circulant reference, without a change of normalization. -/
theorem rieszMatrix_row_sum (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (i : Fin (N : ℕ)) :
    ∑ j, rieszMatrix s N hN i j = ∑ k, sampledRieszKernel s N hN k := by
  exact (Equiv.subRight i).sum_comp (fun k => sampledRieszKernel s N hN k)

/-- The two-sided row-mass growth in the proof of Lemma 5.13.
Constants precede the size and all factorization parameters. -/
theorem global_reference_mass_bounds (s : Riesz1.RieszExponent) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (i : Fin (N : ℕ)),
      c * (N : ℝ) ^ (1 - s.val) ≤ ∑ j, ((2 : ℝ) • rieszMatrix s N hN) i j ∧
      (∑ j, ((2 : ℝ) • rieszMatrix s N hN) i j) ≤ C * (N : ℝ) ^ (1 - s.val) := by
  obtain ⟨c, C, hc, hC, hb⟩ := sampledRieszKernel_zero_mode_bounds s
  refine ⟨2 * c, 2 * C, by positivity, by positivity, ?_⟩
  intro N hN i
  simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, rieszMatrix_row_sum]
  constructor <;> nlinarith [(hb N hN).1, (hb N hN).2]

/-- The exact constant mode in the proof of Lemma 5.13.
The row sum of `H = 2 ℍ` is kept explicitly. -/
theorem factorizationMatrix_constant_mode (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (a : ℝ) (ha : 0 < a) (B : ℝ) :
    let μ := a + B ^ 2 / a
    let ℓ := 2 * ∑ k, sampledRieszKernel s N hN k
    factorizationMatrix s N hN a ha B *ᵥ (fun _ => 1) =
      (μ / (ℓ + μ)) • (fun _ => 1) := by
  let μ := a + B ^ 2 / a
  let ℓ := 2 * ∑ k, sampledRieszKernel s N hN k
  let K := (2 : ℝ) • rieszMatrix s N hN +
    μ • (1 : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
  have hk : K.PosDef := factorization_shifted_posDef s N hN a ha B
  have hdet : IsUnit K.det := isUnit_iff_ne_zero.mpr hk.det_pos.ne'
  have hmode : K *ᵥ (fun _ => 1) = (ℓ + μ) • (fun _ => 1) := by
    dsimp only [K]
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
      mul_one, rieszMatrix_row_sum]
    rfl
  obtain ⟨c, C, hc, hC, hb⟩ := sampledRieszKernel_zero_mode_bounds s
  have hlpos : 0 < ℓ := mul_pos two_pos
    ((mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)).trans_le (hb N hN).1)
  have hden : ℓ + μ ≠ 0 := (add_pos hlpos (factorization_shift_pos ha B)).ne'
  have hinv : K⁻¹ *ᵥ (fun _ => 1) = (ℓ + μ)⁻¹ • (fun _ => 1) := by
    have hh := congrArg (fun v => K⁻¹ *ᵥ v) hmode
    rw [mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec, mulVec_smul] at hh
    calc K⁻¹ *ᵥ (fun _ => 1) =
        (ℓ + μ)⁻¹ • ((ℓ + μ) • (K⁻¹ *ᵥ (fun _ => 1))) := by
          rw [smul_smul, inv_mul_cancel₀ hden, one_smul]
      _ = _ := by rw [← hh]
  change (μ • K⁻¹) *ᵥ (fun _ => 1) = _
  rw [smul_mulVec, hinv, smul_smul, div_eq_mul_inv]

/-- Scalar linear operators commute with every deterministic component matrix.
This is the componentwise-generator clause of the proof of Lemma 5.13,
stated on an arbitrary scalar operator domain, so no boundedness of a generator
is assumed. -/
theorem component_matrix_commutes_linear {ι V W : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (A : Matrix ι ι ℝ) (L : V →ₗ[ℝ] W) (u : ι → V) (i : ι) :
    L (∑ j, A i j • u j) = ∑ j, A i j • L (u j) := by
  simp only [map_sum, map_smul]

/-- Simultaneous cyclic translation preserves the global factorization matrix
(the proof of Lemma 5.13). In particular its kernel is independent of
the selected row. -/
theorem factorizationMatrix_translate (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (a : ℝ) (ha : 0 < a) (B : ℝ)
    (i j t : Fin (N : ℕ)) :
    factorizationMatrix s N hN a ha B (i + t) (j + t) =
      factorizationMatrix s N hN a ha B i j := by
  let K := (2 : ℝ) • rieszMatrix s N hN +
    (a + B ^ 2 / a) • (1 : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
  let e := Equiv.addRight t
  have he : K.submatrix e e = K := by
    ext u v
    simp [K, e, rieszMatrix, Matrix.one_apply]
  have hi := Matrix.inv_submatrix_equiv K e e
  rw [he] at hi
  have hij := congrFun (congrFun hi i) j
  change (a + B ^ 2 / a) * K⁻¹ (i + t) (j + t) =
    (a + B ^ 2 / a) * K⁻¹ i j
  exact congrArg ((a + B ^ 2 / a) * ·) hij.symm

/-- The row-kernel convention in the proof of Lemma 5.13 is
the zero row evaluated at the cyclic displacement. -/
theorem factorizationMatrix_kernel (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (a : ℝ) (ha : 0 < a) (B : ℝ)
    (i j : Fin (N : ℕ)) :
    factorizationMatrix s N hN a ha B i j =
      factorizationMatrix s N hN a ha B 0 (j - i) := by
  have h := factorizationMatrix_translate s N hN a ha B i j (-i)
  simpa only [add_neg_cancel, ← sub_eq_add_neg] using h.symm

/-- Evenness of the real global resolvent kernel
(the proof of Lemma 5.13). -/
theorem factorizationMatrix_kernel_even (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (a : ℝ) (ha : 0 < a) (B : ℝ) (h : Fin (N : ℕ)) :
    factorizationMatrix s N hN a ha B 0 (-h) =
      factorizationMatrix s N hN a ha B 0 h := by
  have hs : (factorizationMatrix s N hN a ha B).IsSymm :=
    Matrix.isHermitian_iff_isSymm.mp
      (factorizationMatrix_posDef s N hN a ha B).isHermitian
  have ht := factorizationMatrix_translate s N hN a ha B 0 (-h) h
  have ht' : factorizationMatrix s N hN a ha B h 0 =
      factorizationMatrix s N hN a ha B 0 (-h) := by
    simpa only [zero_add, neg_add_cancel] using ht
  exact ht'.symm.trans (congrFun (congrFun hs 0) h)

end Riesz2
