/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.GlobalCommutatorsPart3

/-!
# Tail contributions to the global spatial commutator

Cutoff, retained-row and fractional-cancellation estimates for Step 2 of
the proof of Lemma 5.13. They are used in both the regional estimates and
the pointwise bounds with fixed exponents.
-/

@[expose] public section

noncomputable section

open Matrix Finset MeasureTheory
open scoped BigOperators Fin.NatCast Matrix.Norms.L2Operator MatrixOrder ENNReal

namespace Riesz2.GlobalCommutators
namespace Internal

/-- A row envelope and its squared sum control the finite output norm.
Internal assembly for the proof of Lemma 5.13. -/
theorem spatial_output_envelope {ι : Type*} [Fintype ι]
    (f c : ι → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hc : ∀ i, 0 ≤ c i) (hf : ∀ i, |f i| ≤ A * c i) :
    Real.sqrt (∑ i, f i ^ 2) ≤ A * Real.sqrt (∑ i, c i ^ 2) := by
  have hsq : (∑ i, f i ^ 2) ≤ A ^ 2 * ∑ i, c i ^ 2 := by
    rw [mul_sum]
    apply sum_le_sum
    intro i _
    have hh := sq_le_sq₀ (abs_nonneg (f i)) (mul_nonneg hA (hc i))
    simpa only [sq_abs, mul_pow] using hh.mpr (hf i)
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq hA] at h

/-- The two reciprocal-radius Cauchy–Schwarz factors in the proof of Lemma 5.13 cost one logarithm, including zero vectors. -/
theorem spatial_reciprocal_action (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (i₀ : Fin (N : ℕ)) (p L : ℝ) (hL : 0 ≤ L)
    (Q : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (hQ : ∀ i j, |Q i j| ≤ L * weightRadius N i i₀ ^ (-p))
    (v : Fin (N : ℕ) → ℝ) :
    Real.sqrt (∑ i, (weightRadius N i i₀ ^ (p - 1 / 2) * (Q *ᵥ v) i) ^ 2) ≤
      (2 * (1 + 1 / Real.log 2)) * L * Real.log (2 * (N : ℝ)) *
        Real.sqrt (∑ j, (weightRadius N j i₀ ^ (1 / 2 : ℝ) * v j) ^ 2) := by
  let r := fun i => weightRadius N i i₀
  let Z := Real.sqrt (∑ j, (r j ^ (1 / 2 : ℝ) * v j) ^ 2)
  let H := ∑ j, (r j)⁻¹
  have hr (i) : 0 < r i := by dsimp [r]; linarith [one_le_weightRadius N i i₀]
  have hcs : (∑ j, |v j|) ≤ Real.sqrt H * Z := by
    have h := FiniteZeroSumBounds.weighted_cauchy_subset univ
      (fun j => r j ^ (1 / 2 : ℝ)) (fun _ => 1) v
      (fun j => Real.rpow_pos_of_pos (hr j) _)
    have he (j) : (1 / r j ^ (1 / 2 : ℝ)) ^ 2 = (r j)⁻¹ := by
      rw [one_div, inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul (hr j).le]
      norm_num
    simpa only [one_mul, he, mem_univ, sum_const_zero, Z, H] using h
  have hp (i) : |r i ^ (p - 1 / 2) * (Q *ᵥ v) i| ≤
      (L * Real.sqrt H * Z) * r i ^ (-(1 / 2 : ℝ)) := by
    calc
      _ = r i ^ (p - 1 / 2) * |(Q *ᵥ v) i| := by
        rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (hr i) _)]
      _ ≤ r i ^ (p - 1 / 2) * ∑ j, |Q i j| * |v j| := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (hr i).le _)
        simpa only [mulVec, dotProduct, abs_mul] using abs_sum_le_sum_abs
          (fun j => Q i j * v j) univ
      _ ≤ r i ^ (p - 1 / 2) * ∑ j, (L * r i ^ (-p)) * |v j| := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (hr i).le _)
        apply sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (hQ i j) (abs_nonneg _)
      _ = L * r i ^ (-(1 / 2 : ℝ)) * ∑ j, |v j| := by
        rw [← mul_sum]
        have he : r i ^ (p - 1 / 2) * r i ^ (-p) = r i ^ (-(1 / 2 : ℝ)) := by
          rw [← Real.rpow_add (hr i)]; congr 1; ring
        calc _ = L * (r i ^ (p - 1 / 2) * r i ^ (-p)) * ∑ j, |v j| := by ring
             _ = _ := by rw [he]
      _ ≤ L * r i ^ (-(1 / 2 : ℝ)) * (Real.sqrt H * Z) :=
        mul_le_mul_of_nonneg_left hcs (mul_nonneg hL (Real.rpow_nonneg (hr i).le _))
      _ = _ := by ring
  have he (i) : (r i ^ (-(1 / 2 : ℝ))) ^ 2 = (r i)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hr i).le]
    norm_num [Real.rpow_neg_one]
  have h := spatial_output_envelope _ _ (L * Real.sqrt H * Z)
    (mul_nonneg (mul_nonneg hL (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
    (fun i => Real.rpow_nonneg (hr i).le _) hp
  simp_rw [he] at h
  have hh : (L * Real.sqrt H * Z) * Real.sqrt H = L * H * Z := by
    calc _ = L * Z * (Real.sqrt H) ^ 2 := by ring
         _ = _ := by rw [Real.sq_sqrt (show 0 ≤ H by dsimp [H]; exact sum_nonneg fun j _ => inv_nonneg.mpr (hr j).le)]; ring
  rw [hh] at h
  exact h.trans (by
    have hb := GlobalCancellation.sum_inverse_radius N hN i₀
    calc L * H * Z ≤ L * ((2 * (1 + 1 / Real.log 2)) * Real.log (2 * (N : ℝ))) * Z := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hL) (Real.sqrt_nonneg _)
      _ = _ := by dsimp [Z, r]; ring)

/-- The discarded part of the actual resolvent convolution in the proof of Lemma 5.13. Only an absolute column bound on the
matrix to its right is needed. -/
theorem spatial_discarded_action (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (a : ℝ) (ha : 0 < a) (B L : ℝ), 0 ≤ L →
      ∀ (T : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ),
      (∀ j, ∑ l, |T l j| ≤ L) → ∀ (i₀ : Fin (N : ℕ)) (v : Fin (N : ℕ) → ℝ),
      let r := fun i => weightRadius N i i₀
      let Q : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ := fun i j =>
        ∑ l, (factorizationMatrix s N hN a ha B i l *
          (1 - CutoffApproximation.scalarCutoff
            (16 * (Riesz1.cyclicIndexDistance N i l : ℝ) / r i))) * T l j
      Real.sqrt (∑ i, (r i ^ (3 / 2 - s.val) * (Q *ᵥ v) i) ^ 2) ≤
        C * (a + B ^ 2 / a) * L * Real.log (2 * (N : ℝ)) *
          Real.sqrt (∑ j, (r j ^ (1 / 2 : ℝ) * v j) ^ 2) := by
  obtain ⟨C, hC, hentry⟩ := factorization_entry_bound hz s
  have hp : 0 < 2 - s.val := by linarith [s.property.2]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(2 * (1 + 1 / Real.log 2)) * C * 16 ^ (2 - s.val), by positivity, ?_⟩
  intro N hN a ha B L hL T hcol i₀ v r Q
  let μ := a + B ^ 2 / a
  have hμ : 0 < μ := factorization_shift_pos ha B
  have hr (i) : 0 < r i := by dsimp [r]; linarith [one_le_weightRadius N i i₀]
  have hpoint (i l) :
      |factorizationMatrix s N hN a ha B i l *
        (1 - CutoffApproximation.scalarCutoff
          (16 * (Riesz1.cyclicIndexDistance N i l : ℝ) / r i))| ≤
        C * μ * 16 ^ (2 - s.val) * r i ^ (-(2 - s.val)) := by
    let d : ℝ := Riesz1.cyclicIndexDistance N i l
    let z := CutoffApproximation.scalarCutoff (16 * d / r i)
    have hri : 0 < r i := hr i
    have hz₀ : 0 ≤ z := CutoffApproximation.scalarCutoff_nonneg _
    have hz₁ : z ≤ 1 := CutoffApproximation.scalarCutoff_le_one _
    by_cases he : z = 1
    · change |factorizationMatrix s N hN a ha B i l * (1 - z)| ≤ _
      rw [he, sub_self, mul_zero, abs_zero]
      positivity
    have hd : r i / 16 < d := by
      by_contra h
      apply he
      apply CutoffApproximation.scalarCutoff_eq_one
      apply (div_le_iff₀ (hr i)).mpr
      linarith [le_of_not_gt h]
    have hpow : (1 + d) ^ (-(2 - s.val)) ≤
        16 ^ (2 - s.val) * r i ^ (-(2 - s.val)) := by
      calc
        _ ≤ (r i / 16) ^ (-(2 - s.val)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
        _ = _ := by
          rw [Real.div_rpow (hr i).le (by norm_num),
            Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 16)]
          simp only [div_eq_mul_inv, inv_inv]
          ring
    calc
      _ = |factorizationMatrix s N hN a ha B i l| * (1 - z) := by
        rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - z)]
      _ ≤ |factorizationMatrix s N hN a ha B i l| * 1 :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ ≤ C * μ * (1 + d) ^ (-(2 - s.val)) := by
        simpa only [mul_one] using hentry N hN a ha B i l
      _ ≤ C * μ * (16 ^ (2 - s.val) * r i ^ (-(2 - s.val))) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by ring
  have hQ (i j) : |Q i j| ≤
      (C * μ * 16 ^ (2 - s.val) * L) * r i ^ (-(2 - s.val)) := by
    have hri : 0 < r i := hr i
    calc
      _ ≤ ∑ l, |(factorizationMatrix s N hN a ha B i l *
          (1 - CutoffApproximation.scalarCutoff
            (16 * (Riesz1.cyclicIndexDistance N i l : ℝ) / r i))) * T l j| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ l, (C * μ * 16 ^ (2 - s.val) * r i ^ (-(2 - s.val))) * |T l j| := by
        apply sum_le_sum
        intro l _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hpoint i l) (abs_nonneg _)
      _ = (C * μ * 16 ^ (2 - s.val) * r i ^ (-(2 - s.val))) * ∑ l, |T l j| :=
        (mul_sum _ _ _).symm
      _ ≤ (C * μ * 16 ^ (2 - s.val) * r i ^ (-(2 - s.val))) * L :=
        mul_le_mul_of_nonneg_left (hcol j) (by positivity)
      _ = _ := by ring
  have h := spatial_reciprocal_action N hN i₀ (2 - s.val)
    (C * μ * 16 ^ (2 - s.val) * L) (by positivity) Q hQ v
  rw [show 2 - s.val - 1 / 2 = 3 / 2 - s.val by ring] at h
  exact h.trans_eq (by dsimp [μ, r]; ring)

/-- Bounded output radii of the actual tail product in the proof of Lemma 5.13. The contraction estimate covers every
cutoff scale, including scales larger than the cycle. -/
theorem spatial_small_rows (s : Riesz1.RieszExponent) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (a : ℝ) (ha : 0 < a) (B K L : ℝ)
    (hK : 1 ≤ K) (hL : 0 ≤ L)
    (E z : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (hE : ∀ i j, |E i j| ≤ L *
      (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-1 - s.val / 2))
    (hz : ∀ i j, |z i j| ≤ 1)
    (hz₀ : ∀ i j, (Riesz1.cyclicIndexDistance N i j : ℝ) ≤ K → z i j = 0)
    (i₀ : Fin (N : ℕ)) (v : Fin (N : ℕ) → ℝ) :
    let T : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ := fun i j => z i j * E i j
    let w := fun i => weightRadius N i i₀ ^ (3 / 2 - s.val)
    Real.sqrt (∑ i, (if weightRadius N i i₀ < 16 * K then
      w i * ((factorizationMatrix s N hN a ha B * T) *ᵥ v) i else 0) ^ 2) ≤
      (16 * K) ^ (3 / 2 - s.val) * (2 * (1 + 2 / s.val)) * L * K ^ (-s.val / 2) *
        Real.sqrt (∑ j, (weightRadius N j i₀ ^ (1 / 2 : ℝ) * v j) ^ 2) := by
  intro T w
  have hα : 0 ≤ 3 / 2 - s.val := by linarith [s.property.2]
  have hp : 0 ≤ (16 * K) ^ (3 / 2 - s.val) := Real.rpow_nonneg (by linarith) _
  have hs : (∑ i, (if weightRadius N i i₀ < 16 * K then
      w i * ((factorizationMatrix s N hN a ha B * T) *ᵥ v) i else 0) ^ 2) ≤
      ((16 * K) ^ (3 / 2 - s.val)) ^ 2 *
        ∑ i, (((factorizationMatrix s N hN a ha B * T) *ᵥ v) i) ^ 2 := by
    rw [mul_sum]
    apply sum_le_sum
    intro i _
    split_ifs with hi
    · rw [mul_pow]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact pow_le_pow_left₀ (by dsimp [weightRadius]; positivity)
        (Real.rpow_le_rpow (by dsimp [weightRadius]; positivity) hi.le hα) _
    · simp only [zero_pow (by norm_num : 2 ≠ 0)]
      positivity
  have hv : Real.sqrt (∑ j, v j ^ 2) ≤
      Real.sqrt (∑ j, (weightRadius N j i₀ ^ (1 / 2 : ℝ) * v j) ^ 2) := by
    apply Real.sqrt_le_sqrt
    apply sum_le_sum
    intro j _
    rw [mul_pow]
    have hj := Real.one_le_rpow (one_le_weightRadius N j i₀) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hsq : (1 : ℝ) ≤ (weightRadius N j i₀ ^ (1 / 2 : ℝ)) ^ 2 := by nlinarith
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hsq (sq_nonneg (v j))
  have hroot := Real.sqrt_le_sqrt hs
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hp] at hroot
  have ht := spatial_unweighted_tail s N hN a ha B K L hK hL E z hE hz hz₀ v
  exact hroot.trans ((mul_le_mul_of_nonneg_left ht hp).trans (by
    calc _ ≤ (16 * K) ^ (3 / 2 - s.val) *
        ((2 * (1 + 2 / s.val)) * L * K ^ (-s.val / 2) *
          Real.sqrt (∑ j, (weightRadius N j i₀ ^ (1 / 2 : ℝ) * v j) ^ 2)) := by
            apply mul_le_mul_of_nonneg_left _ hp
            exact mul_le_mul_of_nonneg_left hv (by have := s.property.1; positivity)
      _ = _ := by ring))

/-- Component Hölder and the summable output profile in the proof of Lemma 5.13. This internal assembly accepts proved
fractional row bounds and retains the constant mode of the inverse. -/
theorem spatial_fractional_row_action (s : Riesz1.RieszExponent)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (i₀ : Fin (N : ℕ))
    (J : Finset (Fin (N : ℕ))) (L : ℝ) (hL : 0 ≤ L)
    (F : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ) :
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    let δ := s.val ^ 2 * (2 - s.val) / 4
    let q := 2 / s.val
    let p := (1 - s.val / 2)⁻¹
    (∀ i ∈ J, (∑ j, |(F i ᵥ* (rieszMatrix sh N hN)⁻¹) j| ^ q) ^ (1 / q) ≤
      L * weightRadius N i i₀ ^ (-(2 - s.val) - δ)) →
    ∀ v : Fin (N : ℕ) → ℝ,
      Real.sqrt (∑ i, (if i ∈ J then
        weightRadius N i i₀ ^ (3 / 2 - s.val) * (F *ᵥ v) i else 0) ^ 2) ≤
        Real.sqrt (2 * (1 + 1 / (2 * δ))) * L *
          (∑ j, |(rieszMatrix sh N hN *ᵥ v) j| ^ p) ^ (1 / p) := by
  intro sh δ q p hrow v
  let r := fun i => weightRadius N i i₀
  let H := rieszMatrix sh N hN
  let P := (∑ j, |(H *ᵥ v) j| ^ p) ^ (1 / p)
  have hr (i) : 0 < r i := by dsimp [r]; linarith [one_le_weightRadius N i i₀]
  have hδ : 0 < δ := by dsimp [δ]; exact div_pos (mul_pos (sq_pos_of_pos s.property.1)
    (by linarith [s.property.2])) (by norm_num)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hpq : q.HolderConjugate p := by
    apply Real.holderConjugate_iff.mpr
    constructor
    · dsimp [q]; rw [lt_div_iff₀ s.property.1]; linarith [s.property.2]
    · dsimp [p, q]; field_simp; ring_nf
  have hact (i) (hi : i ∈ J) : |(F *ᵥ v) i| ≤
      L * r i ^ (-(2 - s.val) - δ) * P := by
    have hH : IsUnit H := (sampledRieszKernel_posDef sh N hN).isUnit
    have hid : (F *ᵥ v) i = (F i ᵥ* H⁻¹) ⬝ᵥ (H *ᵥ v) := by
      rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det H).mp hH)]
      simp only [Matrix.one_mulVec]
      rfl
    calc
      _ = |(F i ᵥ* H⁻¹) ⬝ᵥ (H *ᵥ v)| := congrArg abs hid
      _ ≤ ∑ j, |(F i ᵥ* H⁻¹) j| * |(H *ᵥ v) j| := by
        simpa only [dotProduct, abs_mul] using abs_sum_le_sum_abs
          (fun j => (F i ᵥ* H⁻¹) j * (H *ᵥ v) j) univ
      _ ≤ (∑ j, |(F i ᵥ* H⁻¹) j| ^ q) ^ (1 / q) * P := by
        simpa only [abs_abs] using Real.inner_le_Lp_mul_Lq univ
          (fun j => |(F i ᵥ* H⁻¹) j|) (fun j => |(H *ᵥ v) j|) hpq
      _ ≤ _ := mul_le_mul_of_nonneg_right (hrow i hi) hP
  have hout (i) : |(if i ∈ J then
      r i ^ (3 / 2 - s.val) * (F *ᵥ v) i else 0)| ≤
      (L * P) * r i ^ (-(1 / 2 : ℝ) - δ) := by
    split_ifs with hi
    · rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (hr i) _)]
      calc
        _ ≤ r i ^ (3 / 2 - s.val) * (L * r i ^ (-(2 - s.val) - δ) * P) :=
          mul_le_mul_of_nonneg_left (hact i hi) (Real.rpow_nonneg (hr i).le _)
        _ = _ := by
          have he : r i ^ (3 / 2 - s.val) * r i ^ (-(2 - s.val) - δ) =
              r i ^ (-(1 / 2 : ℝ) - δ) := by
            rw [← Real.rpow_add (hr i)]; congr 1; ring
          calc _ = (L * P) * (r i ^ (3 / 2 - s.val) * r i ^ (-(2 - s.val) - δ)) := by ring
               _ = _ := by rw [he]
    · rw [abs_zero]
      exact mul_nonneg (mul_nonneg hL hP) (Real.rpow_nonneg (hr i).le _)
  have hsq : (∑ i, (r i ^ (-(1 / 2 : ℝ) - δ)) ^ 2) ≤ 2 * (1 + 1 / (2 * δ)) := by
    have he (i) : (r i ^ (-(1 / 2 : ℝ) - δ)) ^ 2 = r i ^ (-(1 + 2 * δ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hr i).le]; congr 1; ring
    simp_rw [he]
    have hall : univ.filter (fun i => (1 : ℝ) ≤ weightRadius N i i₀) = univ :=
      filter_true_of_mem (fun i _ => one_le_weightRadius N i i₀)
    have hb := sum_weightRadius_tail_le N i₀ (t := 1 + 2 * δ) (R := 1)
      (by linarith) (by norm_num)
    simpa only [hall, show 1 + 2 * δ - 1 = 2 * δ by ring, Real.one_rpow, mul_one] using hb
  have h := spatial_output_envelope _ _ (L * P) (mul_nonneg hL hP)
    (fun i => Real.rpow_nonneg (hr i).le _) hout
  exact h.trans (by
    calc _ ≤ (L * P) * Real.sqrt (2 * (1 + 1 / (2 * δ))) :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsq) (mul_nonneg hL hP)
      _ = _ := by dsimp [P, H]; ring)

/-- Finite Euclidean triangle inequality used in the spatial assembly. -/
theorem spatial_norm_add {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    Real.sqrt (∑ i, (f i + g i) ^ 2) ≤
      Real.sqrt (∑ i, f i ^ 2) + Real.sqrt (∑ i, g i ^ 2) := by
  have h := norm_add_le (WithLp.toLp 2 f) (WithLp.toLp 2 g)
  simpa only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs,
    PiLp.add_apply] using h

/-- Restricting output rows decreases the finite Euclidean norm. -/
theorem spatial_norm_restrict {ι : Type*} [Fintype ι] [DecidableEq ι] (J : Finset ι) (f : ι → ℝ) :
    Real.sqrt (∑ i, (if i ∈ J then f i else 0) ^ 2) ≤ Real.sqrt (∑ i, f i ^ 2) := by
  classical
  apply Real.sqrt_le_sqrt
  apply sum_le_sum
  intro i _
  split_ifs <;> simp only [zero_pow (by norm_num : 2 ≠ 0), le_refl, sq_nonneg]

/-- Absolute sums of the resolvent kernel, used in the comparable-weight
piece of the proof of Lemma 5.13. -/
theorem spatial_resolvent_absolute_sums (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (a : ℝ) (ha : 0 < a) (B : ℝ),
      let A := factorizationMatrix s N hN a ha B
      (∀ i, ∑ l, |A i l| ≤ C * (a + B ^ 2 / a)) ∧
      (∀ j, ∑ l, |A l j| ≤ C * (a + B ^ 2 / a)) := by
  obtain ⟨C, hC, hb⟩ := factorization_entry_bound hz s
  have hs : 0 < 1 - s.val := by linarith [s.property.2]
  refine ⟨C * (2 * (1 + 1 / (1 - s.val))), by positivity, ?_⟩
  intro N hN a ha B A
  have hμ := factorization_shift_pos ha B
  have hone (i : Fin (N : ℕ)) :
      (∑ l, weightRadius N l i ^ (-(2 - s.val))) ≤ 2 * (1 + 1 / (1 - s.val)) := by
    have hall : univ.filter (fun l => (1 : ℝ) ≤ weightRadius N l i) = univ :=
      filter_true_of_mem fun l _ => one_le_weightRadius N l i
    have h := sum_weightRadius_tail_le N i (t := 2 - s.val) (R := 1) (by linarith) (by norm_num)
    simpa only [hall, show 2 - s.val - 1 = 1 - s.val by ring, Real.one_rpow, mul_one] using h
  constructor <;> intro i
  · calc
      _ ≤ ∑ l, C * (a + B ^ 2 / a) * weightRadius N l i ^ (-(2 - s.val)) := by
        apply sum_le_sum
        intro l _
        simpa only [A, weightRadius_eq_comm] using hb N hN a ha B i l
      _ = C * (a + B ^ 2 / a) * ∑ l, weightRadius N l i ^ (-(2 - s.val)) := (mul_sum _ _ _).symm
      _ ≤ C * (a + B ^ 2 / a) * (2 * (1 + 1 / (1 - s.val))) :=
        mul_le_mul_of_nonneg_left (hone i) (by positivity)
      _ = _ := by ring
  · calc
      _ ≤ ∑ l, C * (a + B ^ 2 / a) * weightRadius N l i ^ (-(2 - s.val)) :=
        sum_le_sum fun l _ => hb N hN a ha B l i
      _ = C * (a + B ^ 2 / a) * ∑ l, weightRadius N l i ^ (-(2 - s.val)) := (mul_sum _ _ _).symm
      _ ≤ C * (a + B ^ 2 / a) * (2 * (1 + 1 / (1 - s.val))) :=
        mul_le_mul_of_nonneg_left (hone i) (by positivity)
      _ = _ := by ring

/-- Comparable output and source weights in the proof of Lemma 5.13. This internal Schur estimate uses the
literal two retained cutoffs. Its matrix inputs are unrestricted. -/
theorem spatial_comparable_product (s : Riesz1.RieszExponent)
    (N : ℕ+) (i₀ : Fin (N : ℕ)) (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (A T : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (hAr : ∀ i, ∑ l, |A i l| ≤ U) (hAc : ∀ l, ∑ i, |A i l| ≤ U)
    (hTr : ∀ l, ∑ j, |T l j| ≤ V) (hTc : ∀ j, ∑ l, |T l j| ≤ V)
    (v : Fin (N : ℕ) → ℝ) :
    let r := fun i => weightRadius N i i₀
    let w := fun i => r i ^ (3 / 2 - s.val)
    let Q : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ := fun i j =>
      CutoffApproximation.scalarCutoff (4 * (Riesz1.cyclicIndexDistance N i j : ℝ) / r i) *
        ∑ l, (A i l * CutoffApproximation.scalarCutoff
          (16 * (Riesz1.cyclicIndexDistance N i l : ℝ) / r i)) * T l j
    Real.sqrt (∑ i, (w i * (Q *ᵥ v) i) ^ 2) ≤
      2 ^ (3 / 2 - s.val) * U * V * Real.sqrt (∑ j, (w j * v j) ^ 2) := by
  intro r w Q
  let α := 3 / 2 - s.val
  let P : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ := fun i j => ∑ l, |A i l| * |T l j|
  let K : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ := fun i j => w i * Q i j / w j
  have hα : 0 ≤ α := by dsimp [α]; linarith [s.property.2]
  have hr (i) : 0 < r i := by dsimp [r]; linarith [one_le_weightRadius N i i₀]
  have hw (i) : 0 < w i := Real.rpow_pos_of_pos (hr i) _
  have hP (i j) : 0 ≤ P i j := by dsimp [P]; positivity
  have hPr (i) : ∑ j, P i j ≤ U * V := by
    calc
      _ = ∑ l, |A i l| * ∑ j, |T l j| := by
        dsimp [P]; rw [sum_comm]; simp_rw [mul_sum]
      _ ≤ ∑ l, |A i l| * V := sum_le_sum fun l _ =>
        mul_le_mul_of_nonneg_left (hTr l) (abs_nonneg _)
      _ = (∑ l, |A i l|) * V := (sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (hAr i) hV
  have hPc (j) : ∑ i, P i j ≤ U * V := by
    calc
      _ = ∑ l, (∑ i, |A i l|) * |T l j| := by
        dsimp [P]; rw [sum_comm]; simp_rw [sum_mul]
      _ ≤ ∑ l, U * |T l j| := sum_le_sum fun l _ =>
        mul_le_mul_of_nonneg_right (hAc l) (abs_nonneg _)
      _ = U * ∑ l, |T l j| := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (hTc j) hU
  have hQ (i j) : |Q i j| ≤ P i j := by
    have hz₀ := CutoffApproximation.scalarCutoff_nonneg
      (4 * (Riesz1.cyclicIndexDistance N i j : ℝ) / r i)
    have hz₁ := CutoffApproximation.scalarCutoff_le_one
      (4 * (Riesz1.cyclicIndexDistance N i j : ℝ) / r i)
    calc
      _ ≤ |∑ l, (A i l * CutoffApproximation.scalarCutoff
          (16 * (Riesz1.cyclicIndexDistance N i l : ℝ) / r i)) * T l j| := by
        dsimp [Q]
        rw [abs_mul, abs_of_nonneg hz₀]
        exact mul_le_of_le_one_left (abs_nonneg _) hz₁
      _ ≤ ∑ l, |(A i l * CutoffApproximation.scalarCutoff
          (16 * (Riesz1.cyclicIndexDistance N i l : ℝ) / r i)) * T l j| := abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply sum_le_sum
        intro l _
        rw [abs_mul, abs_mul, abs_of_nonneg (CutoffApproximation.scalarCutoff_nonneg _)]
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        exact mul_le_of_le_one_right (abs_nonneg _) (CutoffApproximation.scalarCutoff_le_one _)
  have hK (i j) : |K i j| ≤ 2 ^ α * P i j := by
    by_cases hz : CutoffApproximation.scalarCutoff
        (4 * (Riesz1.cyclicIndexDistance N i j : ℝ) / r i) = 0
    · simp only [K, Q, hz, zero_mul, mul_zero, zero_div, abs_zero]
      exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hP i j)
    have hd : (Riesz1.cyclicIndexDistance N i j : ℝ) < r i / 2 := by
      by_contra h
      apply hz
      apply CutoffApproximation.scalarCutoff_eq_zero
      apply (le_div_iff₀ (hr i)).mpr
      linarith [le_of_not_gt h]
    have hri : r i ≤ 2 * r j := by
      have hl := (abs_le.mp (DerivativeCommutators.weightRadius_lipschitz N i₀ i j)).2
      change r i - r j ≤ _ at hl
      linarith
    have hweight : w i / w j ≤ 2 ^ α := by
      apply (div_le_iff₀ (hw j)).mpr
      change r i ^ α ≤ 2 ^ α * r j ^ α
      rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (hr j).le]
      exact Real.rpow_le_rpow (hr i).le hri hα
    calc
      _ = (w i / w j) * |Q i j| := by
        dsimp [K]; rw [abs_div, abs_mul, abs_of_pos (hw i), abs_of_pos (hw j)]; ring
      _ ≤ 2 ^ α * P i j := mul_le_mul hweight (hQ i j) (abs_nonneg _) (by positivity)
  have hKr (i) : ∑ j, |K i j| ≤ 2 ^ α * U * V := by
    calc _ ≤ ∑ j, 2 ^ α * P i j := sum_le_sum fun j _ => hK i j
         _ = 2 ^ α * ∑ j, P i j := (mul_sum _ _ _).symm
         _ ≤ 2 ^ α * (U * V) := mul_le_mul_of_nonneg_left (hPr i) (by positivity)
         _ = _ := by ring
  have hKc (j) : ∑ i, |K i j| ≤ 2 ^ α * U * V := by
    calc _ ≤ ∑ i, 2 ^ α * P i j := sum_le_sum fun i _ => hK i j
         _ = 2 ^ α * ∑ i, P i j := (mul_sum _ _ _).symm
         _ ≤ 2 ^ α * (U * V) := mul_le_mul_of_nonneg_left (hPc j) (by positivity)
         _ = _ := by ring
  have he (i) : ∑ j, K i j * (w j * v j) = w i * (Q *ᵥ v) i := by
    rw [mulVec, dotProduct, mul_sum]
    apply sum_congr rfl
    intro j _
    dsimp [K]
    field_simp [(hw j).ne']
  have h := FiniteSchurBounds.sqrt_sum_sq_norm_le K (fun j => w j * v j)
    (show 0 ≤ 2 ^ α * U * V by positivity) hKr hKc
  simpa only [smul_eq_mul, he, Real.norm_eq_abs, sq_abs] using h

/-- Assembly of all four regions of the actual weighted tail product
in the proof of Lemma 5.13. Its internal hypotheses
are entry and difference bounds, rather than commutator conclusions. -/
theorem spatial_tail_action (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent) :
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    let p := (1 - s.val / 2)⁻¹
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (a : ℝ) (ha : 0 < a) (B K L : ℝ), 1 ≤ K → 0 ≤ L →
      ∀ E : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ,
      (∀ k j, |E k j| ≤ L * weightRadius N k j ^ (-(1 + s.val / 2))) →
      (∀ k j, |E k j - E (k + 1) j| + |E k j - E k (j + 1)| ≤
        L * weightRadius N k j ^ (-(1 + s.val))) →
      (∀ k j, |(E k j - E (k + 1) j) -
        (E k (j + 1) - E (k + 1) (j + 1))| ≤
          L * weightRadius N k j ^ (-(2 + s.val))) →
      ∀ (i₀ : Fin (N : ℕ)) (v : Fin (N : ℕ) → ℝ),
      let r := fun i => weightRadius N i i₀
      let T : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ := fun i j =>
        (1 - CutoffApproximation.scalarCutoff ((Riesz1.cyclicIndexDistance N i j : ℝ) / K)) * E i j
      Real.sqrt (∑ i, (r i ^ (3 / 2 - s.val) *
        ((factorizationMatrix s N hN a ha B * T) *ᵥ v) i) ^ 2) ≤
        C * (1 + (a + B ^ 2 / a)) * L *
          (K ^ (-s.val / 2) * Real.sqrt (∑ j, (r j ^ (3 / 2 - s.val) * v j) ^ 2) +
            ((16 * K) ^ (3 / 2 - s.val) * K ^ (-s.val / 2) + Real.log (2 * (N : ℝ))) *
              Real.sqrt (∑ j, (r j ^ (1 / 2 : ℝ) * v j) ^ 2) +
            (∑ j, |(rieszMatrix sh N hN *ᵥ v) j| ^ p) ^ (1 / p)) := by
  intro sh p
  obtain ⟨Cd, hCd, hd⟩ := spatial_discarded_action hz s
  obtain ⟨Ca, hCa, hA⟩ := spatial_resolvent_absolute_sums hz s
  obtain ⟨Cf, hCf, hf⟩ := spatial_retained_row_norms hz s
  let δ := s.val ^ 2 * (2 - s.val) / 4
  let S := 2 * (1 + 2 / s.val)
  let Cn := 2 ^ (3 / 2 - s.val) * Ca * S
  let D := Cd * S
  let F := Real.sqrt (2 * (1 + 1 / (2 * δ))) * Cf
  let C := S + Cn + D + F
  have hS : 0 < S := by dsimp [S]; have := s.property.1; positivity
  have hCn : 0 < Cn := by dsimp [Cn]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hδ : 0 < δ := by dsimp [δ]; exact div_pos (mul_pos (sq_pos_of_pos s.property.1)
    (by linarith [s.property.2])) (by norm_num)
  have hF : 0 < F := by dsimp [F]; positivity
  have hSC : S ≤ C := by dsimp [C]; linarith
  have hNC : Cn ≤ C := by dsimp [C]; linarith
  have hDC : D ≤ C := by dsimp [C]; linarith
  have hFC : F ≤ C := by dsimp [C]; linarith
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro N hN a ha B K L hK hL E hE hΔ hΔ₂ i₀ v r T
  let μ := a + B ^ 2 / a
  let A := factorizationMatrix s N hN a ha B
  let z := fun i j => 1 - CutoffApproximation.scalarCutoff ((Riesz1.cyclicIndexDistance N i j : ℝ) / K)
  let c := fun i l => CutoffApproximation.scalarCutoff (16 * (Riesz1.cyclicIndexDistance N i l : ℝ) / r i)
  let o := fun i j => CutoffApproximation.scalarCutoff (4 * (Riesz1.cyclicIndexDistance N i j : ℝ) / r i)
  let G : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ := fun i j => ∑ l, (A i l * c i l) * T l j
  let Qd : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ := fun i j => ∑ l, (A i l * (1 - c i l)) * T l j
  let Qn : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ := fun i j => o i j * G i j
  let Qf : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ := fun i j => (1 - o i j) * G i j
  let J := univ.filter (fun i => 16 * K ≤ r i)
  let small := fun i => if i ∈ J then 0 else r i ^ (3 / 2 - s.val) * ((A * T) *ᵥ v) i
  let disc := fun i => if i ∈ J then r i ^ (3 / 2 - s.val) * (Qd *ᵥ v) i else 0
  let near := fun i => if i ∈ J then r i ^ (3 / 2 - s.val) * (Qn *ᵥ v) i else 0
  let far := fun i => if i ∈ J then r i ^ (3 / 2 - s.val) * (Qf *ᵥ v) i else 0
  let X := Real.sqrt (∑ j, (r j ^ (3 / 2 - s.val) * v j) ^ 2)
  let Z := Real.sqrt (∑ j, (r j ^ (1 / 2 : ℝ) * v j) ^ 2)
  let P := (∑ j, |(rieszMatrix sh N hN *ᵥ v) j| ^ p) ^ (1 / p)
  let k := K ^ (-s.val / 2)
  let b := (16 * K) ^ (3 / 2 - s.val) * k
  let logN := Real.log (2 * (N : ℝ))
  have hμ : 0 < μ := factorization_shift_pos ha B
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hk1 : k ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hK (by linarith [s.property.1])
  have hX : 0 ≤ X := Real.sqrt_nonneg _
  have hZ : 0 ≤ Z := Real.sqrt_nonneg _
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hlog : 0 ≤ logN := by
    dsimp [logN]
    apply Real.log_nonneg
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hz₁ (i j) : |z i j| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (CutoffApproximation.scalarCutoff_le_one _))]
    linarith [CutoffApproximation.scalarCutoff_nonneg ((Riesz1.cyclicIndexDistance N i j : ℝ) / K)]
  have hz₀ (i j) (hij : (Riesz1.cyclicIndexDistance N i j : ℝ) ≤ K) : z i j = 0 := by
    dsimp [z]
    rw [CutoffApproximation.scalarCutoff_eq_one ((div_le_one (by linarith : 0 < K)).mpr hij)]
    ring
  have hE' (i j) : |E i j| ≤ L * (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-1 - s.val / 2) := by
    simpa only [weightRadius, show -(1 + s.val / 2) = -1 - s.val / 2 by ring] using hE i j
  obtain ⟨hTr, hTc⟩ := tail_cutoff_absolute_sums s N K L hK hL E z hE' hz₁ hz₀
  have hsmall : Real.sqrt (∑ i, small i ^ 2) ≤ S * L * b * Z := by
    have hh := spatial_small_rows s N hN a ha B K L hK hL E z hE' hz₁ hz₀ i₀ v
    have he (i) : small i = (if r i < 16 * K then
        r i ^ (3 / 2 - s.val) * ((A * T) *ᵥ v) i else 0) := by
      dsimp only [small, J]
      simp only [mem_filter, mem_univ, true_and]
      rw [← ite_not]
      simp only [not_le]
    simp_rw [he]
    exact hh.trans_eq (by dsimp [S, b, k, Z, r]; ring)
  have hdisc : Real.sqrt (∑ i, disc i ^ 2) ≤ D * μ * L * logN * Z := by
    have hcol (j) : ∑ l, |T l j| ≤ S * L := by
      exact (hTc j).trans (by change S * L * k ≤ S * L; exact mul_le_of_le_one_right (by positivity) hk1)
    have hh := hd N hN a ha B (S * L) (by positivity) T hcol i₀ v
    exact (spatial_norm_restrict J _).trans (hh.trans_eq (by dsimp [D, μ, logN, Z, r]; ring))
  have hnear : Real.sqrt (∑ i, near i ^ 2) ≤ Cn * μ * L * k * X := by
    obtain ⟨hAr, hAc⟩ := hA N hN a ha B
    have hh := spatial_comparable_product s N i₀ (Ca * μ) (S * L * k)
      (by positivity) (by positivity) A T hAr hAc hTr hTc v
    exact (spatial_norm_restrict J _).trans (hh.trans_eq (by dsimp [Cn, μ, k, X, r]; ring))
  have hfar : Real.sqrt (∑ i, far i ^ 2) ≤ F * μ * L * P := by
    have hh := spatial_fractional_row_action s N hN i₀ J (Cf * μ * L) (by positivity) Qf
      (fun i hi => by
        have hiR : 16 * K ≤ r i := (mem_filter.mp hi).2
        have hi16 : 16 ≤ r i := by linarith
        have heq : Qf i = fun j => (1 - o i j) * ∑ l, (A i l * c i l) * E l j := by
          funext j
          exact spatial_far_tail_identity N i (r i) K (by linarith) (by linarith) hiR A E j
        rw [heq]
        exact (hf N hN a ha B i₀ i L hL E hE hΔ hΔ₂ hi16).2.2) v
    exact hh.trans_eq (by dsimp [F, μ, P, δ]; ring)
  have he (i) : r i ^ (3 / 2 - s.val) * ((A * T) *ᵥ v) i =
      ((small i + disc i) + near i) + far i := by
    by_cases hi : i ∈ J
    · have hmat : A * T = (Qd + Qn) + Qf := by
        ext k j
        change (∑ l, A k l * T l j) =
          ((∑ l, (A k l * (1 - c k l)) * T l j) + o k j * ∑ l, (A k l * c k l) * T l j) +
            (1 - o k j) * ∑ l, (A k l * c k l) * T l j
        simp only [mul_sum]
        rw [← sum_add_distrib, ← sum_add_distrib]
        apply sum_congr rfl
        intro l _
        ring
      rw [hmat]
      simp only [add_mulVec, Pi.add_apply, small, disc, near, far, hi, ↓reduceIte]
      ring
    · simp only [small, disc, near, far, hi, ↓reduceIte, add_zero]
  change Real.sqrt (∑ i, (r i ^ (3 / 2 - s.val) * ((A * T) *ᵥ v) i) ^ 2) ≤ _
  simp_rw [he]
  have ht := (spatial_norm_add (fun i => (small i + disc i) + near i) far).trans
    (add_le_add ((spatial_norm_add (fun i => small i + disc i) near).trans
      (add_le_add (spatial_norm_add small disc) le_rfl)) le_rfl)
  apply ht.trans
  have hs := add_le_add (add_le_add (add_le_add hsmall hdisc) hnear) hfar
  apply hs.trans
  have hC : 0 ≤ C := hS.le.trans hSC
  have hcoeff₁ : S ≤ C * (1 + μ) := hSC.trans
    (le_mul_of_one_le_right hC (by linarith only [hμ]))
  have hcoeff₂ : D * μ ≤ C * (1 + μ) :=
    mul_le_mul hDC (by linarith only [hμ]) hμ.le hC
  have hcoeff₃ : Cn * μ ≤ C * (1 + μ) :=
    mul_le_mul hNC (by linarith only [hμ]) hμ.le hC
  have hcoeff₄ : F * μ ≤ C * (1 + μ) :=
    mul_le_mul hFC (by linarith only [hμ]) hμ.le hC
  have h1 : S * L * b * Z ≤ C * (1 + μ) * L * b * Z := by gcongr
  have h2 : D * μ * L * logN * Z ≤ C * (1 + μ) * L * logN * Z := by gcongr
  have h3 : Cn * μ * L * k * X ≤ C * (1 + μ) * L * k * X := by gcongr
  have h4 : F * μ * L * P ≤ C * (1 + μ) * L * P := by gcongr
  calc
    _ ≤ ((C * (1 + μ) * L * b * Z + C * (1 + μ) * L * logN * Z) +
        C * (1 + μ) * L * k * X) + C * (1 + μ) * L * P := add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    _ = _ := by dsimp [b, k, logN, X, Z, P, μ]; ring

end Internal
end Riesz2.GlobalCommutators
