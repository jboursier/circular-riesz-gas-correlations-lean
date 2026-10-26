/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.GlobalResolventKernelPart4
public import Riesz2.DecayLong.GlobalCancellation
public import Riesz2.DecayLong.GlobalReferenceErrorPart2

/-!
# Algebra and endpoint pieces of the global commutators

Algebraic identities and endpoint estimates in the proof of Lemma 5.13.
The reference and compact error pieces use the factorization matrix,
including its constant mode.
-/

@[expose] public section

noncomputable section

open Matrix Finset
open scoped BigOperators Fin.NatCast Matrix.Norms.L2Operator

namespace Riesz2.GlobalCommutators

/-- The symmetric-kernel identity in the proof of Lemma 5.13. This specializes the weighted energy identity. -/
theorem differential_identity (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (a : ℝ) (ha : 0 < a) (B : ℝ)
    (i₀ : Fin (N : ℕ)) (g : Fin (N : ℕ) → ℝ) :
    let A := factorizationMatrix s N hN a ha B
    let w := fun i => weightRadius N i i₀ ^ (3 / 2 - s.val)
    (∑ i, (w i * g i) * (w i * (A *ᵥ g) i -
      (A *ᵥ (fun j => w j * g j)) i)) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, A i j * (w i - w j) ^ 2 * g i * g j := by
  dsimp only
  let A := factorizationMatrix s N hN a ha B
  let w := fun i => weightRadius N i i₀ ^ (3 / 2 - s.val)
  have hs : ∀ i j, A i j = A j i := by
    have hh := Matrix.isHermitian_iff_isSymm.mp
      (factorizationMatrix_posDef s N hN a ha B).isHermitian
    intro i j
    exact congrFun (congrFun hh j) i
  have h := DerivativeCommutators.weighted_commutator_identity A A hs w g
  simp only [sub_self, zero_mulVec, Pi.zero_apply, mul_zero, sum_const_zero, add_zero] at h
  calc
    _ = (∑ i, w i ^ 2 * g i * (A *ᵥ g) i) -
        ∑ i, (w i * g i) * (A *ᵥ (fun j => w j * g j)) i := by
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro i _
      dsimp [w, A]
      ring
    _ = _ := by change _ = (1 / 2 : ℝ) * ∑ i, ∑ j, A i j * (w i - w j) ^ 2 * g i * g j; linarith

/-- Exact cancellation on the smaller-radius part of a row, as used in
the proof of Lemma 5.13. The complementary sum is
retained, including at the threshold and on the two-point cycle. -/
theorem differential_small_radius_cancellation (s : Riesz1.RieszExponent)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (a : ℝ) (ha : 0 < a) (B : ℝ)
    (i₀ i : Fin (N : ℕ)) (g : Fin (N : ℕ) → ℝ) (hg : ∑ j, g j = 0) :
    let A := factorizationMatrix s N hN a ha B
    let S := univ.filter (fun j => weightRadius N j i₀ < weightRadius N i i₀ / 2)
    (∑ j ∈ S, A i j * g j) =
      (∑ j ∈ S, (A i j - A i i₀) * g j) -
        A i i₀ * ∑ j ∈ univ.filter
          (fun j => weightRadius N i i₀ / 2 ≤ weightRadius N j i₀), g j := by
  dsimp only
  let S := univ.filter (fun j => weightRadius N j i₀ < weightRadius N i i₀ / 2)
  have hc : Sᶜ = univ.filter
      (fun j => weightRadius N i i₀ / 2 ≤ weightRadius N j i₀) := by
    ext j
    simp [S, not_lt]
  have hsplit : (∑ j ∈ S, g j) + ∑ j ∈ Sᶜ, g j = 0 := by
    rw [sum_add_sum_compl, hg]
  have hm := congrArg (factorizationMatrix s N hN a ha B i i₀ * ·) hsplit
  rw [mul_add, mul_zero, hc] at hm
  simp only [sub_mul, sum_sub_distrib, ← mul_sum]
  linarith

/-- Algebraic decomposition of the proof of Lemma 5.13:
the reference piece is `-μ[W,A]`, and the error splits as `E=E_K+T`.
This holds for every splitting of the actual error. -/
theorem spatial_decomposition (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (a : ℝ) (ha : 0 < a) (B : ℝ)
    (M T : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (w v : Fin (N : ℕ) → ℝ) (i : Fin (N : ℕ)) :
    let A := factorizationMatrix s N hN a ha B
    let μ := a + B ^ 2 / a
    let H := (2 : ℝ) • rieszMatrix s N hN
    let Eₖ := M - H - T
    w i * ((A * M) *ᵥ v) i - ((A * M) *ᵥ (fun j => w j * v j)) i =
      -μ * (w i * (A *ᵥ v) i - (A *ᵥ (fun j => w j * v j)) i) +
      (w i * ((A * Eₖ) *ᵥ v) i - ((A * Eₖ) *ᵥ (fun j => w j * v j)) i) +
      (w i * ((A * T) *ᵥ v) i - ((A * T) *ᵥ (fun j => w j * v j)) i) := by
  dsimp only
  let A := factorizationMatrix s N hN a ha B
  let H := (2 : ℝ) • rieszMatrix s N hN
  have he : M = H + (M - H - T) + T := by abel
  conv_lhs => rw [he]
  rw [mul_add, mul_add]
  rw [(factorizationMatrix_mul_reference s N hN a ha B).1]
  simp only [add_mulVec, sub_mulVec, smul_mulVec, one_mulVec, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The entry bound of the actual factorization matrix, expressed for
arbitrary rows. This bridges the zero-row convention to the
endpoint commutator API used in the proof of Lemma 5.13. -/
theorem factorization_entry_bound (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (a : ℝ) (ha : 0 < a) (B : ℝ) (i j : Fin (N : ℕ)),
      |factorizationMatrix s N hN a ha B i j| ≤
        C * (a + B ^ 2 / a) *
          (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-(2 - s.val)) := by
  obtain ⟨C, hC, hb⟩ := factorizationMatrix_entry_decay hz s
  refine ⟨C, hC, ?_⟩
  intro N hN a ha B i j
  rw [factorizationMatrix_kernel]
  have hd : Riesz1.cyclicIndexDistance N (j - i) 0 =
      Riesz1.cyclicIndexDistance N i j := by
    rw [← GlobalReferenceErrorInternal.distance_translate N (j - i) 0 i]
    simpa only [sub_add_cancel, zero_add] using cyclicIndexDistance_comm' N j i
  simpa only [hd] using hb N hN a ha B (j - i)

/-- The full reference contribution to the proof of Lemma 5.13 satisfies a stronger endpoint estimate
without an `η X` term. Its constant is uniform before the cycle and source,
and is quadratic in the prescribed shift. -/
theorem spatial_reference_endpoint (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (a : ℝ) (ha : 0 < a) (B : ℝ) (i₀ : Fin (N : ℕ))
      (v : Fin (N : ℕ) → ℝ),
      let A := factorizationMatrix s N hN a ha B
      let H := (2 : ℝ) • rieszMatrix s N hN
      let μ := a + B ^ 2 / a
      let w := fun i => weightRadius N i i₀ ^ (3 / 2 - s.val)
      Real.sqrt (∑ i, (w i * ((A * H) *ᵥ v) i -
        ((A * H) *ᵥ (fun j => w j * v j)) i) ^ 2) ≤
        C * μ ^ 2 * Real.log (2 * (N : ℝ)) *
          Real.sqrt (∑ j, (weightRadius N j i₀ ^ (1 / 2 : ℝ) * v j) ^ 2) := by
  obtain ⟨C, hC, hb⟩ := factorization_entry_bound hz s
  refine ⟨(8 * (1 + 1 / Real.log 2)) * C, by
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity, ?_⟩
  intro N hN a ha B i₀ v
  dsimp only
  let μ := a + B ^ 2 / a
  have hμ := factorization_shift_pos ha B
  have h := GlobalCancellation.endpoint_logarithmic
    (p := 2 - s.val) (by linarith [s.property.2]) (by linarith [s.property.1])
    N hN i₀ (factorizationMatrix s N hN a ha B)
    (Bstar := C * μ) (by positivity) (hb N hN a ha B) v
  have heq (i : Fin (N : ℕ)) :
      weightRadius N i i₀ ^ (3 / 2 - s.val) *
          ((factorizationMatrix s N hN a ha B * ((2 : ℝ) • rieszMatrix s N hN)) *ᵥ v) i -
        ((factorizationMatrix s N hN a ha B * ((2 : ℝ) • rieszMatrix s N hN)) *ᵥ
          (fun j => weightRadius N j i₀ ^ (3 / 2 - s.val) * v j)) i =
      -μ * (weightRadius N i i₀ ^ (3 / 2 - s.val) *
        (factorizationMatrix s N hN a ha B *ᵥ v) i -
        (factorizationMatrix s N hN a ha B *ᵥ
          (fun j => weightRadius N j i₀ ^ (3 / 2 - s.val) * v j)) i) := by
    rw [(factorizationMatrix_mul_reference s N hN a ha B).1]
    simp only [sub_mulVec, smul_mulVec, one_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [heq, mul_pow, neg_sq, ← mul_sum]
  rw [Real.sqrt_mul (sq_nonneg μ), Real.sqrt_sq hμ.le]
  have hp : 2 - s.val - 1 / 2 = 3 / 2 - s.val := by ring
  rw [hp] at h
  simp only [mul_pow] at h
  convert mul_le_mul_of_nonneg_left h hμ.le using 1
  dsimp [μ]
  ring

/-- The compact error product in the proof of Lemma 5.13
has the reference decay exponent, with an explicit polynomial cutoff loss.
The hypotheses describe a finite-range matrix and its column
sums. -/
theorem compact_error_entry_bound (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (a : ℝ) (ha : 0 < a) (B K L : ℝ), 0 ≤ K → 0 ≤ L →
      ∀ E : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ,
      (∀ l j, 2 * K < (Riesz1.cyclicIndexDistance N l j : ℝ) → E l j = 0) →
      (∀ j, ∑ l, |E l j| ≤ L) → ∀ i j,
      |(factorizationMatrix s N hN a ha B * E) i j| ≤
        (C * (a + B ^ 2 / a) * (1 + 2 * K) ^ (2 - s.val) * L) *
          (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-(2 - s.val)) := by
  obtain ⟨C, hC, hb⟩ := factorization_entry_bound hz s
  refine ⟨C, hC, ?_⟩
  intro N hN a ha B K L hK hL E hsupp hcol i j
  let p := 2 - s.val
  let S := 1 + 2 * K
  let D := fun i j => 1 + (Riesz1.cyclicIndexDistance N i j : ℝ)
  have hS : 0 < S := by dsimp [S]; linarith
  have hD (i j : Fin (N : ℕ)) : 0 < D i j := by dsimp [D]; positivity
  have hp : 0 ≤ p := by dsimp [p]; linarith [s.property.2]
  have hpoint (l : Fin (N : ℕ)) :
      |factorizationMatrix s N hN a ha B i l * E l j| ≤
        (C * (a + B ^ 2 / a) * S ^ p * D i j ^ (-p)) * |E l j| := by
    by_cases he : E l j = 0
    · simp only [he, mul_zero, abs_zero, le_refl]
    have hdlj : (Riesz1.cyclicIndexDistance N l j : ℝ) ≤ 2 * K := by
      exact le_of_not_gt (fun h => he (hsupp l j h))
    have htri : (Riesz1.cyclicIndexDistance N i j : ℝ) ≤
        (Riesz1.cyclicIndexDistance N i l : ℝ) +
          (Riesz1.cyclicIndexDistance N l j : ℝ) := by
      exact_mod_cast cyclicIndexDistance_triangle i l j
    have hgeom : D i j ≤ S * D i l := by
      dsimp [D, S]
      nlinarith [(Nat.cast_nonneg (Riesz1.cyclicIndexDistance N i l) :
        (0 : ℝ) ≤ (Riesz1.cyclicIndexDistance N i l : ℝ))]
    have hpow : D i l ^ (-p) ≤ S ^ p * D i j ^ (-p) := by
      rw [Real.rpow_neg (hD i l).le, Real.rpow_neg (hD i j).le]
      have hh : 1 / D i l ^ p ≤ S ^ p / D i j ^ p := by
        apply (div_le_div_iff₀ (Real.rpow_pos_of_pos (hD i l) p)
          (Real.rpow_pos_of_pos (hD i j) p)).mpr
        simpa only [one_mul, Real.mul_rpow hS.le (hD i l).le] using
          Real.rpow_le_rpow (hD i j).le hgeom hp
      simpa only [div_eq_mul_inv, one_mul] using hh
    calc
      _ = |factorizationMatrix s N hN a ha B i l| * |E l j| := abs_mul _ _
      _ ≤ (C * (a + B ^ 2 / a) * D i l ^ (-p)) * |E l j| :=
        mul_le_mul_of_nonneg_right (hb N hN a ha B i l) (abs_nonneg _)
      _ ≤ (C * (a + B ^ 2 / a) * (S ^ p * D i j ^ (-p))) * |E l j| := by
        gcongr
      _ = _ := by ring
  calc
    _ ≤ ∑ l, |factorizationMatrix s N hN a ha B i l * E l j| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ l, (C * (a + B ^ 2 / a) * S ^ p * D i j ^ (-p)) * |E l j| :=
      sum_le_sum (fun l _ => hpoint l)
    _ = (C * (a + B ^ 2 / a) * S ^ p * D i j ^ (-p)) * ∑ l, |E l j| :=
      (mul_sum _ _ _).symm
    _ ≤ (C * (a + B ^ 2 / a) * S ^ p * D i j ^ (-p)) * L := by
      apply mul_le_mul_of_nonneg_left (hcol j)
      exact mul_nonneg (mul_nonneg (mul_nonneg hC.le
        (factorization_shift_pos ha B).le) (Real.rpow_nonneg hS.le _))
        (Real.rpow_nonneg (hD i j).le _)
    _ = _ := by dsimp [p, S, D]; ring

/-- Endpoint estimate for the finite-range error piece of the proof of Lemma 5.13. This uses a positive real cutoff and
keeps its complete quantitative loss. -/
theorem spatial_compact_error_endpoint (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (a : ℝ) (ha : 0 < a) (B K L : ℝ), 0 ≤ K → 0 ≤ L →
      ∀ E : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ,
      (∀ l j, 2 * K < (Riesz1.cyclicIndexDistance N l j : ℝ) → E l j = 0) →
      (∀ j, ∑ l, |E l j| ≤ L) → ∀ (i₀ : Fin (N : ℕ)) (v : Fin (N : ℕ) → ℝ),
      let A := factorizationMatrix s N hN a ha B
      let w := fun i => weightRadius N i i₀ ^ (3 / 2 - s.val)
      Real.sqrt (∑ i, (w i * ((A * E) *ᵥ v) i -
        ((A * E) *ᵥ (fun j => w j * v j)) i) ^ 2) ≤
        C * (a + B ^ 2 / a) * (1 + 2 * K) ^ (2 - s.val) * L *
          Real.log (2 * (N : ℝ)) *
            Real.sqrt (∑ j, (weightRadius N j i₀ ^ (1 / 2 : ℝ) * v j) ^ 2) := by
  obtain ⟨C, hC, hb⟩ := compact_error_entry_bound hz s
  refine ⟨(8 * (1 + 1 / Real.log 2)) * C, by
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity, ?_⟩
  intro N hN a ha B K L hK hL E hsupp hcol i₀ v
  dsimp only
  have hstar : 0 ≤ C * (a + B ^ 2 / a) * (1 + 2 * K) ^ (2 - s.val) * L :=
    mul_nonneg (mul_nonneg (mul_nonneg hC.le (factorization_shift_pos ha B).le)
      (Real.rpow_nonneg (by linarith) _)) hL
  have h := GlobalCancellation.endpoint_logarithmic
    (p := 2 - s.val) (by linarith [s.property.2]) (by linarith [s.property.1])
    N hN i₀ (factorizationMatrix s N hN a ha B * E) hstar
    (hb N hN a ha B K L hK hL E hsupp hcol) v
  rw [show 2 - s.val - 1 / 2 = 3 / 2 - s.val by ring] at h
  exact h.trans_eq (by ring)

/-- Lemma 5.13, Step 2: apply Lemma 5.12
to the full reference contribution, using the resolvent identity and retaining
both the small high-weight coefficient and the quadratic radius remainder. -/
theorem spatial_reference_endpoint_by_regions (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (a : ℝ) (ha : 0 < a) (B : ℝ) (i₀ : Fin (N : ℕ))
      (R : ℝ), 1 ≤ R → ∀ (v : Fin (N : ℕ) → ℝ),
      let A := factorizationMatrix s N hN a ha B
      let H := (2 : ℝ) • rieszMatrix s N hN
      let μ := a + B ^ 2 / a
      let w := fun i => weightRadius N i i₀ ^ (3 / 2 - s.val)
      Real.sqrt (∑ i, (w i * ((A * H) *ᵥ v) i -
        ((A * H) *ᵥ (fun j => w j * v j)) i) ^ 2) ≤
        C * μ ^ 2 * (R ^ (s.val - 1) *
          Real.sqrt (∑ j, (weightRadius N j i₀ ^ (3 / 2 - s.val) * v j) ^ 2) +
          (R ^ 2 + Real.log (2 * (N : ℝ))) * Real.sqrt (∑ j, (weightRadius N j i₀ ^ (1 / 2 : ℝ) * v j) ^ 2)) := by
  obtain ⟨C, hC, hb⟩ := factorization_entry_bound hz s
  obtain ⟨Ce, hCe, he⟩ := GlobalCancellation.endpoint_by_regions
    (2 - s.val) (by linarith [s.property.2]) (by linarith [s.property.1])
  refine ⟨Ce * C, mul_pos hCe hC, ?_⟩
  intro N hN a ha B i₀ R hR v
  dsimp only
  let μ := a + B ^ 2 / a
  have hμ := factorization_shift_pos ha B
  have h := he N hN i₀ (factorizationMatrix s N hN a ha B)
    (C * μ) (by positivity) (hb N hN a ha B) R hR v
  have heq (i : Fin (N : ℕ)) :
      weightRadius N i i₀ ^ (3 / 2 - s.val) *
          ((factorizationMatrix s N hN a ha B * ((2 : ℝ) • rieszMatrix s N hN)) *ᵥ v) i -
        ((factorizationMatrix s N hN a ha B * ((2 : ℝ) • rieszMatrix s N hN)) *ᵥ
          (fun j => weightRadius N j i₀ ^ (3 / 2 - s.val) * v j)) i =
      -μ * (weightRadius N i i₀ ^ (3 / 2 - s.val) *
        (factorizationMatrix s N hN a ha B *ᵥ v) i -
        (factorizationMatrix s N hN a ha B *ᵥ
          (fun j => weightRadius N j i₀ ^ (3 / 2 - s.val) * v j)) i) := by
    rw [(factorizationMatrix_mul_reference s N hN a ha B).1]
    simp only [sub_mulVec, smul_mulVec, one_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [heq, mul_pow, neg_sq, ← mul_sum]
  rw [Real.sqrt_mul (sq_nonneg μ), Real.sqrt_sq hμ.le]
  have hp : 2 - s.val - 1 / 2 = 3 / 2 - s.val := by ring
  rw [hp, show 1 - (2 - s.val) = s.val - 1 by ring] at h
  simp only [mul_pow] at h
  convert mul_le_mul_of_nonneg_left h hμ.le using 1
  dsimp [μ]
  ring

/-- Lemma 5.13, Step 2: apply Lemma 5.12
to the compact error product. The positive envelope `1 + L` also covers
zero error. The cutoff loss remains polynomial before the second radius is chosen. -/
theorem spatial_compact_error_endpoint_by_regions (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (a : ℝ) (ha : 0 < a) (B K L : ℝ), 0 ≤ K → 0 ≤ L →
      ∀ E : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ,
      (∀ l j, 2 * K < (Riesz1.cyclicIndexDistance N l j : ℝ) → E l j = 0) →
      (∀ j, ∑ l, |E l j| ≤ L) → ∀ (i₀ : Fin (N : ℕ)) (R : ℝ), 1 ≤ R → ∀ (v : Fin (N : ℕ) → ℝ),
      let A := factorizationMatrix s N hN a ha B
      let w := fun i => weightRadius N i i₀ ^ (3 / 2 - s.val)
      Real.sqrt (∑ i, (w i * ((A * E) *ᵥ v) i -
        ((A * E) *ᵥ (fun j => w j * v j)) i) ^ 2) ≤
        C * (a + B ^ 2 / a) * (1 + 2 * K) ^ (2 - s.val) * (1 + L) *
          (R ^ (s.val - 1) *
            Real.sqrt (∑ j, (weightRadius N j i₀ ^ (3 / 2 - s.val) * v j) ^ 2) +
            (R ^ 2 + Real.log (2 * (N : ℝ))) *
              Real.sqrt (∑ j, (weightRadius N j i₀ ^ (1 / 2 : ℝ) * v j) ^ 2)) := by
  obtain ⟨C, hC, hb⟩ := compact_error_entry_bound hz s
  obtain ⟨Ce, hCe, he⟩ := GlobalCancellation.endpoint_by_regions
    (2 - s.val) (by linarith [s.property.2]) (by linarith [s.property.1])
  refine ⟨Ce * C, mul_pos hCe hC, ?_⟩
  intro N hN a ha B K L hK hL E hsupp hcol i₀ R hR v
  dsimp only
  have hstar : 0 < C * (a + B ^ 2 / a) * (1 + 2 * K) ^ (2 - s.val) * (1 + L) := by
    have := factorization_shift_pos ha B
    positivity
  have hb' := hb N hN a ha B K (1 + L) hK (by linarith) E hsupp
    (fun j => (hcol j).trans (by linarith))
  have h := he N hN i₀ (factorizationMatrix s N hN a ha B * E) _ hstar hb' R hR v
  rw [show 2 - s.val - 1 / 2 = 3 / 2 - s.val by ring,
    show 1 - (2 - s.val) = s.val - 1 by ring] at h
  exact h.trans_eq (by ring)

/-- The small absolute row and column sums of the first cutoff tail in
the proof of Lemma 5.13. Only its support and size are
needed here. No smoothness of the cutoff or matrix is assumed. -/
theorem tail_cutoff_absolute_sums (s : Riesz1.RieszExponent) (N : ℕ+)
    (K L : ℝ) (hK : 1 ≤ K) (hL : 0 ≤ L)
    (E z : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (hE : ∀ i j, |E i j| ≤ L *
      (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-1 - s.val / 2))
    (hz : ∀ i j, |z i j| ≤ 1)
    (hz₀ : ∀ i j, (Riesz1.cyclicIndexDistance N i j : ℝ) ≤ K → z i j = 0) :
    (∀ i, ∑ j, |z i j * E i j| ≤
      (2 * (1 + 2 / s.val)) * L * K ^ (-s.val / 2)) ∧
    (∀ j, ∑ i, |z i j * E i j| ≤
      (2 * (1 + 2 / s.val)) * L * K ^ (-s.val / 2)) := by
  have hone (F ζ : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
      (hF : ∀ i j, |F i j| ≤ L *
        (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-1 - s.val / 2))
      (hζ : ∀ i j, |ζ i j| ≤ 1)
      (hζ₀ : ∀ i j, (Riesz1.cyclicIndexDistance N i j : ℝ) ≤ K → ζ i j = 0)
      (i : Fin (N : ℕ)) :
      (∑ j, |ζ i j * F i j|) ≤
        (2 * (1 + 2 / s.val)) * L * K ^ (-s.val / 2) := by
    let S := univ.filter (fun j => K ≤ weightRadius N j i)
    have hp : 1 < 1 + s.val / 2 := by linarith [s.property.1]
    have hpoint (j : Fin (N : ℕ)) : |ζ i j * F i j| ≤
        if j ∈ S then L * weightRadius N j i ^ (-(1 + s.val / 2)) else 0 := by
      by_cases hj : j ∈ S
      · simp only [hj, ↓reduceIte]
        calc
          _ = |ζ i j| * |F i j| := abs_mul _ _
          _ ≤ 1 * (L * (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^
              (-1 - s.val / 2)) := mul_le_mul (hζ i j) (hF i j) (abs_nonneg _) zero_le_one
          _ = _ := by
            rw [one_mul, weightRadius_eq_comm]
            congr 2
            ring
      · have hr : weightRadius N j i < K := by simpa only [S, mem_filter, mem_univ,
            true_and, not_le] using hj
        have hd : (Riesz1.cyclicIndexDistance N i j : ℝ) ≤ K := by
          rw [weightRadius_eq_comm] at hr
          linarith
        simp only [hj, ↓reduceIte, hζ₀ i j hd, zero_mul, abs_zero, le_refl]
    calc
      _ ≤ ∑ j, if j ∈ S then L * weightRadius N j i ^ (-(1 + s.val / 2)) else 0 :=
        sum_le_sum (fun j _ => hpoint j)
      _ = L * ∑ j ∈ S, weightRadius N j i ^ (-(1 + s.val / 2)) := by
        rw [← sum_filter, filter_mem_eq_inter, univ_inter, mul_sum]
      _ ≤ L * (2 * (1 + 1 / ((1 + s.val / 2) - 1)) * K ^ (1 - (1 + s.val / 2))) :=
        mul_le_mul_of_nonneg_left (sum_weightRadius_tail_le N i hp hK) hL
      _ = _ := by
        rw [show 1 - (1 + s.val / 2) = -s.val / 2 by ring,
          show 1 / ((1 + s.val / 2) - 1) = 2 / s.val by ring]
        ring
  refine ⟨hone E z hE hz hz₀, ?_⟩
  intro j
  exact hone Eᵀ zᵀ (by
    intro i j
    simpa only [transpose_apply, cyclicIndexDistance_comm' N i j] using hE j i)
    (fun i j => hz j i) (by
      intro i j hij
      exact hz₀ j i (by rwa [cyclicIndexDistance_comm' N j i])) j

/-- The unweighted tail product in the proof of Lemma 5.13. This proves in particular the bound on
`A T W_α v` by substituting the weighted vector for `v`. The bound uses
the actual contraction `A`. -/
theorem spatial_unweighted_tail (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (a : ℝ) (ha : 0 < a) (B K L : ℝ)
    (hK : 1 ≤ K) (hL : 0 ≤ L)
    (E z : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (hE : ∀ i j, |E i j| ≤ L *
      (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-1 - s.val / 2))
    (hz : ∀ i j, |z i j| ≤ 1)
    (hz₀ : ∀ i j, (Riesz1.cyclicIndexDistance N i j : ℝ) ≤ K → z i j = 0)
    (v : Fin (N : ℕ) → ℝ) :
    let T : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ := fun i j => z i j * E i j
    Real.sqrt (∑ i, ((factorizationMatrix s N hN a ha B * T) *ᵥ v) i ^ 2) ≤
      (2 * (1 + 2 / s.val)) * L * K ^ (-s.val / 2) *
        Real.sqrt (∑ j, v j ^ 2) := by
  dsimp only
  let T : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ := fun i j => z i j * E i j
  obtain ⟨hrow, hcol⟩ := tail_cutoff_absolute_sums s N K L hK hL E z hE hz hz₀
  have hc := dotProduct_mulVec_self_le_of_norm_le (factorizationMatrix s N hN a ha B)
    (factorizationMatrix_norm_le_one s N hN a ha B) (T *ᵥ v)
  have hc' : (∑ i, (factorizationMatrix s N hN a ha B *ᵥ (T *ᵥ v)) i ^ 2) ≤
      ∑ i, (T *ᵥ v) i ^ 2 := by
    simpa only [one_pow, one_mul, dotProduct, pow_two] using hc
  have hschur := FiniteSchurBounds.sqrt_sum_sq_norm_le T v
    (show 0 ≤ (2 * (1 + 2 / s.val)) * L * K ^ (-s.val / 2) by
      have : 0 < s.val := s.property.1
      positivity) hrow hcol
  change Real.sqrt (∑ i, ((factorizationMatrix s N hN a ha B * T) *ᵥ v) i ^ 2) ≤ _
  rw [← mulVec_mulVec]
  exact (Real.sqrt_le_sqrt hc').trans (by
    simpa only [smul_eq_mul, Real.norm_eq_abs, sq_abs, Matrix.mulVec, dotProduct] using hschur)

end Riesz2.GlobalCommutators
