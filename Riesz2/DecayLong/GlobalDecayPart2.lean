/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.GlobalDecay
public import Riesz2.DecayLong.GlobalCommutatorsPart4
public import Riesz2.ToMathlib.ConstrainedQuadraticFormBounds

/-!
# Factorized tests for global constrained decay

Factorized weighted tests in the proof of Lemma 5.13, on the original
scalar domains and component constraint spaces.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

namespace Riesz2.BilinearMatrixTests

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup V] [Module ℝ V]

/-- Absolute quadratic bounds on zero-sum real vectors transfer to a
nonnegative symmetric bilinear form with the identical coefficient. -/
theorem transfer_abs (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hs : ∀ u v, B u v = B v u) (hn : ∀ u, 0 ≤ B u u)
    (K : Matrix ι ι ℝ) (w : ι → ℝ) (C : ℝ)
    (hb : ∀ g : ι → ℝ, ∑ i, g i = 0 →
      |∑ i, ∑ j, K i j * g i * g j| ≤ C * ∑ i, w i * g i ^ 2)
    (u : ι → V) (hu : ∑ i, u i = 0) :
    |∑ i, ∑ j, K i j * B (u i) (u j)| ≤ C * ∑ i, w i * B (u i) (u i) := by
  apply abs_le.mpr
  constructor
  · have h := ConstrainedQuadraticFormBounds.transfer B hs hn (-K) w C
      (fun g hg => by
        simp only [Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib]
        linarith only [(abs_le.mp (hb g hg)).1]) u hu
    simp only [Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib] at h
    linarith only [h]
  · exact ConstrainedQuadraticFormBounds.transfer B hs hn K w C
      (fun g hg => (le_abs_self _).trans (hb g hg)) u hu

/-- A positive semidefinite component matrix has nonnegative contraction
with every nonnegative scalar bilinear form. -/
theorem contraction_nonneg (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hn : ∀ u, 0 ≤ B u u) (A : Matrix ι ι ℝ) (hA : A.PosSemidef)
    (u : ι → V) : 0 ≤ ∑ i, ∑ j, A i j * B (u i) (u j) := by
  let R := CFC.sqrt A
  have hf : Rᵀ * R = A := MatrixEnergy.sqrt_factor A hA
  have he : (∑ i, ∑ j, A i j * B (u i) (u j)) =
      ∑ k, B (∑ i, R k i • u i) (∑ j, R k j • u j) := by
    calc
      _ = ∑ i, ∑ j, ∑ k, R k i * R k j * B (u i) (u j) := by
        rw [← hf]
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
      _ = ∑ i, ∑ k, ∑ j, R k i * R k j * B (u i) (u j) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = ∑ k, ∑ i, ∑ j, R k i * R k j * B (u i) (u j) := Finset.sum_comm
      _ = _ := by
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
          smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        ring
  rw [he]
  exact Finset.sum_nonneg (fun k _ => hn _)

omit [DecidableEq ι] in
/-- The form part of the factorized weighted test splits exactly into a
positive retained form and its differential commutator. -/
theorem weighted_test_identity (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hs : ∀ u v, B u v = B v u)
    (A : Matrix ι ι ℝ) (hA : A.IsSymm) (w : ι → ℝ) (u : ι → V) :
    (∑ i, B (u i) (∑ j, A i j • (w j ^ 2 • u j))) =
      (∑ i, ∑ j, A i j * B (w i • u i) (w j • u j)) +
        ∑ i, ∑ j, (w i * A i j * (w i - w j)) * B (u i) (u j) := by
  have hsym (i j) : A i j = A j i := congrArg (fun M => M j i) hA
  calc
    _ = ∑ i, ∑ j, (w i ^ 2 * A i j) * B (u i) (u j) := by
      simp only [map_sum, map_smul, smul_eq_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hs (u j) (u i), hsym j i]
      ring
    _ = _ := by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

end Riesz2.BilinearMatrixTests


namespace Riesz2.GlobalDecay

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

/-- See the proof of Lemma 5.13 in the paper, differential commutator on the actual
scalar form. The coefficient is uniform in the form and component
size. The zero-sum condition holds in the form carrier itself. -/
theorem differential_form_commutator (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω), ∀ (m : ℕ+) (hm : 2 ≤ (m : ℕ))
      (a : ℝ) (ha : 0 < a), a ≤ 1 → ∀ B : ℝ, 1 ≤ B →
      ∀ (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q →
      ∀ (i₀ : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1),
      (∀ᵐ x ∂ν, ∑ i, (u i).val x = 0) →
      let A := factorizationMatrix s m hm a ha B
      let w := fun i => weightRadius m i i₀ ^ (3 / 2 - s.val)
      |∑ i, ∑ j, (w i * A i j * (w i - w j)) * Q.2 (u i) (u j)| ≤
        C * (1 + (a + B ^ 2 / a)) * Real.sqrt (Real.log (2 * (m : ℝ))) *
          ∑ i, weightRadius m i i₀ ^ (2 * (1 - s.val / 2)) * Q.2 (u i) (u i) := by
  obtain ⟨C, hC, hb⟩ := GlobalCommutators.global_differential_commutator hz s
  refine ⟨C, hC, ?_⟩
  intro Ω _ ν m hm a ha ha1 B hB Q hQ i₀ u hu A w
  have hsum : ∑ i, u i = 0 := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum, Submodule.coe_zero] using
      AbstractEquation.sum_values_eq_zero _ hu
  apply BilinearMatrixTests.transfer_abs Q.2 hQ.2.1 hQ.2.2.1
    (fun i j => w i * A i j * (w i - w j))
    (fun i => weightRadius m i i₀ ^ (2 * (1 - s.val / 2))) _ _ u hsum
  intro g hg
  have hh := hb m hm a ha ha1 B hB i₀ g hg
  have he : (∑ i, ∑ j, (w i * A i j * (w i - w j)) * g i * g j) =
      ∑ i, (w i * g i) * (w i * (A *ᵥ g) i -
        (A *ᵥ (fun j => w j * g j)) i) := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_sub, sub_mul,
      Finset.sum_sub_distrib]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
      apply Finset.sum_congr rfl <;> intro j _ <;> ring
  rw [he]
  convert hh using 1
  apply congrArg (fun z => C * (1 + (a + B ^ 2 / a)) *
    Real.sqrt (Real.log (2 * (m : ℝ))) * z)
  apply Finset.sum_congr rfl
  intro i _
  dsimp only at *
  rw [mul_pow]
  congr 1
  conv_rhs =>
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by
      linarith [one_le_weightRadius m i i₀] : 0 ≤ weightRadius m i i₀)]
  congr 1
  norm_num
  ring

/-- See the proof of Lemma 5.13 in the paper, lower bound for the diffusion term
of the factorized test, after discarding its nonnegative retained part. -/
theorem factorized_diffusion_lower (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω), ∀ (m : ℕ+) (hm : 2 ≤ (m : ℕ))
      (a : ℝ) (ha : 0 < a), a ≤ 1 → ∀ B : ℝ, 1 ≤ B →
      ∀ (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q →
      ∀ (i₀ : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1),
      (∀ᵐ x ∂ν, ∑ i, (u i).val x = 0) →
      let A := factorizationMatrix s m hm a ha B
      let w := fun i => weightRadius m i i₀ ^ (3 / 2 - s.val);
      -(C * (1 + (a + B ^ 2 / a)) * Real.sqrt (Real.log (2 * (m : ℝ))) *
          ∑ i, weightRadius m i i₀ ^ (2 * (1 - s.val / 2)) * Q.2 (u i) (u i)) ≤
        ∑ i, Q.2 (u i) (∑ j, A i j • (w j ^ 2 • u j)) := by
  obtain ⟨C, hC, hb⟩ := differential_form_commutator hz s
  refine ⟨C, hC, ?_⟩
  intro Ω _ ν m hm a ha ha1 B hB Q hQ i₀ u hu A w
  have hp := (factorizationMatrix_posDef s m hm a ha B).posSemidef
  have hs : A.IsSymm := Matrix.isHermitian_iff_isSymm.mp hp.isHermitian
  rw [BilinearMatrixTests.weighted_test_identity Q.2 hQ.2.1 A hs w u]
  have hn := BilinearMatrixTests.contraction_nonneg Q.2 hQ.2.2.1 A hp
    (fun i => w i • u i)
  have hh := (abs_le.mp (hb ν m hm a ha ha1 B hB Q hQ i₀ u hu)).1
  linarith only [hn, hh]

/-- See the proof of Lemma 5.13 in the paper, admissible factorized test and its
exact weak equation. This identity uses arbitrary L² forcing, without
pointwise second derivatives of the solution. -/
theorem factorized_weak_test {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : ScalarFormData ν) (M : Ω → Matrix ι ι ℝ)
    (hm : ∀ i j, Measurable (fun x => M x i j))
    (hb : ∃ b : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ b)
    (hs : ∀ᵐ x ∂ν, (M x).IsSymm)
    (A : Matrix ι ι ℝ) (hA : A.IsSymm) (w : ι → ℝ)
    (f : ι → Lp ℝ 2 ν) (u : ι → Q.1)
    (hu : WeightedWeakSolution Q M ⊤ f u) :
    let t := fun i => ∑ j, A i j • (w j ^ 2 • u j)
    WeightedFormDomain Q M ⊤ t ∧
      Integrable (fun x => ∑ i, (w i * (u i).val x) *
        (w i * ((A * M x) *ᵥ (fun j => (u j).val x)) i)) ν ∧
      (∑ i, Q.2 (u i) (t i)) +
        (∫ x, ∑ i, (w i * (u i).val x) *
          (w i * ((A * M x) *ᵥ (fun j => (u j).val x)) i) ∂ν) =
        ∑ i, inner ℝ (f i) (t i).val := by
  intro t
  have ht : WeightedFormDomain Q M ⊤ t :=
    (BoundedMatrixForms.domain_iff Q M hm hb ⊤ t).mpr
      (Eventually.of_forall (fun _ => Submodule.mem_top))
  obtain ⟨hi, he⟩ := hu.2 t ht
  have hc : ∀ᵐ x ∂ν, ∀ i, (t i).val x =
      ∑ j, A i j * (w j ^ 2 * (u j).val x) := by
    apply ae_all_iff.mpr
    intro i
    have hh := BoundedMatrixModes.coe_sum_smul
      (fun j => A i j * w j ^ 2) (fun j => (u j).val)
    simpa only [t, smul_smul, Submodule.coe_sum, Submodule.coe_smul, mul_assoc] using hh
  have hp : matrixFieldPair M (fun i => (u i).val) (fun i => (t i).val) =ᵐ[ν]
      fun x => ∑ i, (w i * (u i).val x) *
        (w i * ((A * M x) *ᵥ (fun j => (u j).val x)) i) := by
    filter_upwards [hs, hc] with x hx ht'
    rw [MatrixEnergy.matrixFieldPair_eq_dot]
    have htv : (fun i => (t i).val x) = A *ᵥ (fun j => w j ^ 2 * (u j).val x) :=
      funext ht'
    rw [htv, dotProduct_mulVec_eq_of_transpose_eq hx,
      dotProduct_mulVec_eq_of_transpose_eq hA, Matrix.mulVec_mulVec]
    apply Finset.sum_congr rfl
    intro i _
    ring
  exact ⟨ht, hi.congr hp, by rwa [integral_congr_ae hp] at he⟩

/-- Internal source pairing for the factorized weighted test. The two
Euclidean coefficients are exactly the weighted source column and row mass.
This bound has no factor depending on the component dimension. -/
theorem factorized_source_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : ScalarFormData ν) (A : Matrix ι ι ℝ) (w : ι → ℝ)
    (i₀ : ι) (χ lam : Lp ℝ 2 ν) (u : ι → Q.1) :
    (∑ i, inner ℝ ((if i = i₀ then χ else 0) + lam)
      (∑ j, A i j • (w j ^ 2 • u j)).val) ≤
      (Real.sqrt (∑ j, (w j * A i₀ j) ^ 2) * ‖χ‖ +
        Real.sqrt (∑ j, (w j * ∑ i, A i j) ^ 2) * ‖lam‖) *
          Real.sqrt (∑ j, (w j * ‖(u j).val‖) ^ 2) := by
  have hone (c : ι → ℝ) (v : Lp ℝ 2 ν) :
      (∑ j, c j * w j ^ 2 * inner ℝ v (u j).val) ≤
        Real.sqrt (∑ j, (w j * c j) ^ 2) * ‖v‖ *
          Real.sqrt (∑ j, (w j * ‖(u j).val‖) ^ 2) := by
    calc
      _ = ∑ j, inner ℝ ((w j * c j) • v) (w j • (u j).val) := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [real_inner_smul_left, real_inner_smul_right]
        ring
      _ ≤ ∑ j, ‖(w j * c j) • v‖ * ‖w j • (u j).val‖ :=
        Finset.sum_le_sum (fun j _ => real_inner_le_norm _ _)
      _ ≤ Real.sqrt (∑ j, ‖(w j * c j) • v‖ ^ 2) *
          Real.sqrt (∑ j, ‖w j • (u j).val‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ = _ := by
        simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        rw [← Finset.sum_mul, Real.sqrt_mul (Finset.sum_nonneg (fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))),
          Real.sqrt_sq (norm_nonneg v)]
  have he : (∑ i, inner ℝ ((if i = i₀ then χ else 0) + lam)
      (∑ j, A i j • (w j ^ 2 • u j)).val) =
      (∑ j, A i₀ j * w j ^ 2 * inner ℝ χ (u j).val) +
        ∑ j, (∑ i, A i j) * w j ^ 2 * inner ℝ lam (u j).val := by
    simp only [Submodule.coe_sum, Submodule.coe_smul, inner_sum,
      real_inner_smul_right, inner_add_left, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_eq_single i₀]
      · simp only [ite_true]
        apply Finset.sum_congr rfl
        intro j _
        ring
      · intro i _ hi
        simp only [ite_eq_right hi, inner_zero_left, mul_zero, Finset.sum_const_zero]
      · simp
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
  rw [he]
  have hχ := hone (fun j => A i₀ j) χ
  have hl := hone (fun j => ∑ i, A i j) lam
  linarith only [hχ, hl]

/-- See the proof of Lemma 5.13 in the paper, the weighted point-source column of
the factorization matrix has only a logarithmic loss. -/
theorem factorized_source_column (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ+) (hm : 2 ≤ (m : ℕ))
      (a : ℝ) (ha : 0 < a) (B : ℝ) (i₀ : Fin (m : ℕ)),
      Real.sqrt (∑ j, (weightRadius m j i₀ ^ (3 / 2 - s.val) *
        factorizationMatrix s m hm a ha B i₀ j) ^ 2) ≤
          C * (a + B ^ 2 / a) * Real.sqrt (Real.log (2 * (m : ℝ))) := by
  obtain ⟨C, hC, hb⟩ := GlobalCommutators.factorization_entry_bound hz s
  let D := Real.sqrt (2 * (1 + 1 / Real.log 2))
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨C * D, mul_pos hC hD, ?_⟩
  intro m hm a ha B i₀
  let A := factorizationMatrix s m hm a ha B
  let μ := a + B ^ 2 / a
  have hμ : 0 < μ := factorization_shift_pos ha B
  have hr (j) : 0 < weightRadius m j i₀ := by linarith [one_le_weightRadius m j i₀]
  have he (j) : (weightRadius m j i₀ ^ (3 / 2 - s.val) * A i₀ j) ^ 2 ≤
      (C * μ) ^ 2 * (weightRadius m j i₀)⁻¹ := by
    have h := hb m hm a ha B i₀ j
    rw [cyclicIndexDistance_comm' m i₀ j] at h
    change |A i₀ j| ≤ C * μ * weightRadius m j i₀ ^ (-(2 - s.val)) at h
    have hh := mul_le_mul_of_nonneg_left h
      (Real.rpow_nonneg (hr j).le (3 / 2 - s.val))
    have hid : weightRadius m j i₀ ^ (3 / 2 - s.val) *
        (C * μ * weightRadius m j i₀ ^ (-(2 - s.val))) =
          C * μ * weightRadius m j i₀ ^ (-(1 / 2 : ℝ)) := by
      calc
        _ = (C * μ) * (weightRadius m j i₀ ^ (3 / 2 - s.val) *
            weightRadius m j i₀ ^ (-(2 - s.val))) := by ring
        _ = _ := by rw [← Real.rpow_add (hr j),
          show 3 / 2 - s.val + -(2 - s.val) = -(1 / 2 : ℝ) by ring]
    rw [hid] at hh
    have ht : |weightRadius m j i₀ ^ (3 / 2 - s.val) * A i₀ j| ≤
        C * μ * weightRadius m j i₀ ^ (-(1 / 2 : ℝ)) := by
      simpa only [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (hr j) _)] using hh
    have hp := pow_le_pow_left₀ (abs_nonneg _) ht 2
    calc
      _ ≤ (C * μ * weightRadius m j i₀ ^ (-(1 / 2 : ℝ))) ^ 2 := by
        simpa only [sq_abs] using hp
      _ = _ := by
        rw [mul_pow]
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul (hr j).le]
        norm_num [Real.rpow_neg_one]
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => he j)
  rw [← Finset.mul_sum] at hsum
  have hh := hsum.trans (mul_le_mul_of_nonneg_left
    (GlobalCancellation.sum_inverse_radius m hm i₀) (sq_nonneg (C * μ)))
  have hroot := Real.sqrt_le_sqrt hh
  rw [Real.sqrt_mul (sq_nonneg (C * μ)), Real.sqrt_sq (by positivity : 0 ≤ C * μ),
    Real.sqrt_mul (by positivity : 0 ≤ 2 * (1 + 1 / Real.log 2))] at hroot
  convert hroot using 1
  dsimp [D]
  ring

/-- See the proof of Lemma 5.13 in the paper, the constant component mode after
factorization. Its weighted Euclidean norm costs exactly one cycle size. -/
theorem factorized_constant_column (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ+) (hm : 2 ≤ (m : ℕ))
      (a : ℝ) (ha : 0 < a) (B : ℝ) (i₀ : Fin (m : ℕ)),
      Real.sqrt (∑ j, (weightRadius m j i₀ ^ (3 / 2 - s.val) *
        ∑ i, factorizationMatrix s m hm a ha B i j) ^ 2) ≤
          C * (a + B ^ 2 / a) * (m : ℝ) := by
  obtain ⟨c, _, hc, _, hb⟩ := global_reference_mass_bounds s
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  intro m hm a ha B i₀
  let A := factorizationMatrix s m hm a ha B
  let μ := a + B ^ 2 / a
  let ℓ := 2 * ∑ k, sampledRieszKernel s m hm k
  have hμ : 0 < μ := factorization_shift_pos ha B
  have hmass : c * (m : ℝ) ^ (1 - s.val) ≤ ℓ := by
    simpa only [ℓ, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum,
      rieszMatrix_row_sum] using (hb m hm i₀).1
  have hℓ : 0 < ℓ := (by positivity : 0 < c * (m : ℝ) ^ (1 - s.val)).trans_le hmass
  have hmode := factorizationMatrix_constant_mode s m hm a ha B
  have hsym (i j) : A i j = A j i := by
    exact congrArg (fun M => M j i)
      (Matrix.isHermitian_iff_isSymm.mp (factorizationMatrix_posDef s m hm a ha B).isHermitian)
  have hcol (j) : (∑ i, A i j) = μ / (ℓ + μ) := by
    have h := congrFun hmode j
    simpa only [Matrix.mulVec, dotProduct, mul_one, Pi.smul_apply, smul_eq_mul,
      hsym _ j] using h
  have hrad (j) : weightRadius m j i₀ ≤ (m : ℝ) := by
    have hh := Riesz1.APG.cyclicIndexDistance_le_half (N := m) j i₀
    have : 1 + Riesz1.cyclicIndexDistance m j i₀ ≤ (m : ℕ) := by omega
    dsimp [weightRadius]
    exact_mod_cast this
  have hα : 0 ≤ 3 / 2 - s.val := by linarith [s.property.2]
  have hsum : (∑ j, weightRadius m j i₀ ^ (2 * (3 / 2 - s.val))) ≤
      (m : ℝ) ^ (2 * (2 - s.val)) := by
    calc
      _ ≤ ∑ _j : Fin (m : ℕ), (m : ℝ) ^ (2 * (3 / 2 - s.val)) := by
        apply Finset.sum_le_sum
        intro j _
        exact Real.rpow_le_rpow (by linarith [one_le_weightRadius m j i₀])
          (hrad j) (by positivity)
      _ = (m : ℝ) * (m : ℝ) ^ (2 * (3 / 2 - s.val)) := by simp
      _ = _ := by
        conv_lhs => lhs; rw [← Real.rpow_one (m : ℝ)]
        rw [← Real.rpow_add (by positivity : (0 : ℝ) < m)]
        congr 1
        ring
  have he (j) : (weightRadius m j i₀ ^ (3 / 2 - s.val)) ^ 2 =
      weightRadius m j i₀ ^ (2 * (3 / 2 - s.val)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by
      linarith [one_le_weightRadius m j i₀] : 0 ≤ weightRadius m j i₀)]
    congr 1
    norm_num
    ring
  change Real.sqrt (∑ j, (weightRadius m j i₀ ^ (3 / 2 - s.val) *
    (∑ i, A i j)) ^ 2) ≤ c⁻¹ * μ * (m : ℝ)
  simp_rw [hcol, mul_pow, he]
  rw [← Finset.sum_mul]
  rw [Real.sqrt_mul (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (by
      linarith [one_le_weightRadius m j i₀]) _)),
    Real.sqrt_sq (by positivity : 0 ≤ μ / (ℓ + μ))]
  have hroot : Real.sqrt (∑ j, weightRadius m j i₀ ^ (2 * (3 / 2 - s.val))) ≤
      (m : ℝ) ^ (2 - s.val) := by
    have hh := Real.sqrt_le_sqrt hsum
    rw [show (m : ℝ) ^ (2 * (2 - s.val)) = ((m : ℝ) ^ (2 - s.val)) ^ 2 by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ m)]
      congr 1
      norm_num
      ring, Real.sqrt_sq (by positivity)] at hh
    exact hh
  have hdiv : μ / (ℓ + μ) ≤ μ / (c * (m : ℝ) ^ (1 - s.val)) := by
    apply div_le_div_of_nonneg_left hμ.le (by positivity)
    linarith only [hmass, hμ]
  calc
    _ ≤ (m : ℝ) ^ (2 - s.val) * (μ / (c * (m : ℝ) ^ (1 - s.val))) :=
      mul_le_mul hroot hdiv (by positivity) (by positivity)
    _ = _ := by
      rw [div_eq_mul_inv, mul_inv_rev, ← Real.rpow_neg (by positivity : (0 : ℝ) ≤ m)]
      calc
        _ = c⁻¹ * μ * ((m : ℝ) ^ (2 - s.val) * (m : ℝ) ^ (-(1 - s.val))) := by ring
        _ = _ := by rw [← Real.rpow_add (by positivity : (0 : ℝ) < m)]; norm_num

/-- Internal factorized energy inequality. The scalar diffusion and spatial
commutator inputs are used only under this distinct internal name. All
matrix integrals come from the bounded weak equation. -/
theorem factorized_energy_internal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : ScalarFormData ν) (M : Ω → Matrix ι ι ℝ)
    (hm : ∀ i j, Measurable (fun x => M x i j))
    (hb : ∃ b : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ b)
    (hs : ∀ᵐ x ∂ν, (M x).IsSymm)
    (A : Matrix ι ι ℝ) (hA : A.IsSymm) (w : ι → ℝ)
    (β : ℝ) (hβ : 0 ≤ β) (k d : ℝ)
    (hk : ∀ᵐ x ∂ν, ∀ z : ι → ℝ,
      k * (∑ i, z i ^ 2) ≤ ∑ i, z i * ((A * M x) *ᵥ z) i)
    (i₀ : ι) (χ lam : Lp ℝ 2 ν) (u : ι → Q.1)
    (hu : WeightedWeakSolution Q (fun x => β • M x) ⊤
      (fun i => (if i = i₀ then χ else 0) + lam) u)
    (hd : -d ≤ ∑ i, Q.2 (u i) (∑ j, A i j • (w j ^ 2 • u j))) :
    let cf := fun x => Real.sqrt (∑ i,
      (w i * ((A * M x) *ᵥ (fun j => (u j).val x)) i -
        ((A * M x) *ᵥ (fun j => w j * (u j).val x)) i) ^ 2)
    MemLp cf 2 ν →
    β * k * (∑ i, (w i * ‖(u i).val‖) ^ 2) ≤
      (Real.sqrt (∑ j, (w j * A i₀ j) ^ 2) * ‖χ‖ +
        Real.sqrt (∑ j, (w j * ∑ i, A i j) ^ 2) * ‖lam‖) *
          Real.sqrt (∑ j, (w j * ‖(u j).val‖) ^ 2) +
      β * Real.sqrt (∑ j, (w j * ‖(u j).val‖) ^ 2) *
        Real.sqrt (∫ x, cf x ^ 2 ∂ν) + d := by
  intro cf hcf
  have hsm : ∀ i j, Measurable (fun x => (β • M x) i j) :=
    fun i j => (hm i j).const_mul β
  have hsb : ∃ b : ℝ, ∀ᵐ x ∂ν, ∀ i j, |(β • M x) i j| ≤ b := by
    obtain ⟨b, hb⟩ := hb
    refine ⟨|β| * b, hb.mono (fun x hx i j => ?_)⟩
    simpa only [Matrix.smul_apply, smul_eq_mul, abs_mul] using
      mul_le_mul_of_nonneg_left (hx i j) (abs_nonneg β)
  have hss : ∀ᵐ x ∂ν, (β • M x).IsSymm :=
    hs.mono (fun _ hx => by rw [Matrix.IsSymm, Matrix.transpose_smul, hx])
  obtain ⟨_, hGi, htest⟩ := factorized_weak_test Q (fun x => β • M x)
    hsm hsb hss A hA w _ u hu
  let G := fun x => ∑ i, (w i * (u i).val x) *
    (w i * ((A * M x) *ᵥ (fun j => (u j).val x)) i)
  have heβ : (fun x => ∑ i, (w i * (u i).val x) *
      (w i * ((A * (β • M x)) *ᵥ (fun j => (u j).val x)) i)) =
        fun x => β * G x := by
    funext x
    simp only [Matrix.mul_smul, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul,
      G, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heβ, integral_const_mul] at htest
  rw [heβ] at hGi
  let xf := fun x => Real.sqrt (∑ i, (w i * (u i).val x) ^ 2)
  have hxf : MemLp xf 2 ν := FiniteMixedL2.weighted_memLp w (fun i => (u i).val)
  have hint : (∫ x, xf x ^ 2 ∂ν) = ∑ i, (w i * ‖(u i).val‖) ^ 2 :=
    FiniteMixedL2.weighted_sq_integral w _
  have hpt : ∀ᵐ x ∂ν, β * k * xf x ^ 2 ≤ β * G x + β * (xf x * cf x) := by
    filter_upwards [hk] with x hx
    let v := fun i => (u i).val x
    let q := fun i => w i * v i
    let c := fun i => w i * ((A * M x) *ᵥ v) i - ((A * M x) *ᵥ q) i
    have hh := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ q (fun i => -c i)
    simp only [neg_sq] at hh
    change (∑ i, q i * -c i) ≤ xf x * cf x at hh
    have hident : (∑ i, q i * ((A * M x) *ᵥ q) i) =
        G x + ∑ i, q i * -c i := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [q, c, G, v]
      ring
    have hh' := hx q
    rw [hident] at hh'
    have hsq : xf x ^ 2 = ∑ i, q i ^ 2 :=
      Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))
    rw [hsq]
    have hp := mul_le_mul_of_nonneg_left (hh'.trans (add_le_add le_rfl hh)) hβ
    linarith only [hp]
  have hprod : Integrable (fun x => xf x * cf x) ν := hxf.integrable_mul hcf
  have hineq := integral_mono_ae (hxf.integrable_sq.const_mul (β * k))
    (hGi.add (hprod.const_mul β)) hpt
  change (∫ x, β * k * xf x ^ 2 ∂ν) ≤
    ∫ x, β * G x + β * (xf x * cf x) ∂ν at hineq
  rw [integral_add hGi (hprod.const_mul β)] at hineq
  simp only [integral_const_mul] at hineq
  rw [hint] at hineq
  have hcs := FiniteMixedL2.integral_mul_le hxf hcf
    (Eventually.of_forall (fun _ => Real.sqrt_nonneg _))
    (Eventually.of_forall (fun _ => Real.sqrt_nonneg _))
  rw [hint] at hcs
  have hsource := factorized_source_bound Q A w i₀ χ lam u
  have hcsβ := mul_le_mul_of_nonneg_left hcs hβ
  linarith only [hineq, htest, hd, hsource, hcsβ]

/-- The finite real square integral of an L² function represents exactly
its extended L² norm. This lemma prevents any use of an integral junk value. -/
theorem sqrt_integral_sq_eq (f : Ω → ℝ) (hf : MemLp f 2 ν) :
    Real.sqrt (∫ x, f x ^ 2 ∂ν) = (eLpNorm f 2 ν).toReal := by
  let g := hf.toLp f
  have he : (∫ x, f x ^ 2 ∂ν) = ‖g‖ ^ 2 := by
    rw [← CyclicFourierL2.integral_sq g]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
  rw [he, Real.sqrt_sq (norm_nonneg _)]
  exact Lp.norm_toLp f hf

/-- Internal passage from the pointwise spatial commutator to finite real
L² norms. Integrability of the commutator is a conclusion. -/
theorem spatial_L2_internal (f X Z P : Ω → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hX : MemLp X 2 ν) (hZ : MemLp Z 2 ν)
    (hP : MemLp P 2 ν) (η C b : ℝ) (hη : 0 ≤ η) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (h : ∀ᵐ x ∂ν, f x ≤ η * X x + C * (b * Z x + P x)) :
    MemLp f 2 ν ∧ Real.sqrt (∫ x, f x ^ 2 ∂ν) ≤
      η * Real.sqrt (∫ x, X x ^ 2 ∂ν) +
        C * (b * Real.sqrt (∫ x, Z x ^ 2 ∂ν) + Real.sqrt (∫ x, P x ^ 2 ∂ν)) := by
  have he := GlobalCommutators.Internal.spatial_integrate ν f X Z P hf hf0
    η C b hη hC hb h
  have hfin : ENNReal.ofReal η * eLpNorm X 2 ν +
      ENNReal.ofReal C * (ENNReal.ofReal b * eLpNorm Z 2 ν + eLpNorm P 2 ν) < ⊤ := by
    finiteness
  have hm : MemLp f 2 ν := he.trans_lt hfin
  refine ⟨hm, ?_⟩
  have hh := ENNReal.toReal_mono hfin.ne he
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)] at hh
  simp only [ENNReal.toReal_mul] at hh
  rw [ENNReal.toReal_add (by finiteness) hP.eLpNorm_ne_top] at hh
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hη,
    ENNReal.toReal_ofReal hC, ENNReal.toReal_ofReal hb] at hh
  simpa only [sqrt_integral_sq_eq f hm, sqrt_integral_sq_eq X hX,
    sqrt_integral_sq_eq Z hZ, sqrt_integral_sq_eq P hP] using hh

/-- See the proof of Lemma 5.13 in the paper, coercivity of the actual factorized
matrix in its unsymmetrized quadratic pairing. -/
theorem factorized_coercivity (s : Riesz1.RieszExponent) (m : ℕ+)
    (hm : 2 ≤ (m : ℕ)) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (B : ℝ) (hB : 1 ≤ B) (M : Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hM : M.IsSymm) (hMa : a • 1 ≤ M)
    (hMB : ‖M - (2 : ℝ) • rieszMatrix s m hm‖ ≤ B)
    (z : Fin (m : ℕ) → ℝ) :
    a / 4 * (∑ i, z i ^ 2) ≤
      ∑ i, z i * ((factorizationMatrix s m hm a ha B * M) *ᵥ z) i := by
  let A := factorizationMatrix s m hm a ha B
  have hA : A.IsSymm := Matrix.isHermitian_iff_isSymm.mp
    (factorizationMatrix_posDef s m hm a ha B).isHermitian
  have hsym : ((1 / 2 : ℝ) • (A * M + M * A)).IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    rw [Matrix.IsSymm, Matrix.transpose_smul, Matrix.transpose_add,
      Matrix.transpose_mul, Matrix.transpose_mul, hA, hM, add_comm]
  have hh := (FiniteMatrixOrder.smul_one_le_iff hsym (a / 4)).mp
    (global_factorization s m hm a ha ha1 B hB M hM hMa hMB) z
  have he : z ⬝ᵥ (((1 / 2 : ℝ) • (A * M + M * A)) *ᵥ z) =
      z ⬝ᵥ ((A * M) *ᵥ z) := by
    rw [Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul, dotProduct_add]
    have heq : z ⬝ᵥ ((M * A) *ᵥ z) = z ⬝ᵥ ((A * M) *ᵥ z) := by
      rw [← Matrix.mulVec_mulVec, dotProduct_mulVec_eq_of_transpose_eq hM,
        dotProduct_comm, ← dotProduct_mulVec_eq_of_transpose_eq hA, Matrix.mulVec_mulVec]
    rw [heq, smul_eq_mul]
    ring
  rw [he] at hh
  simpa only [dotProduct, sq] using hh

/-- Lemma 5.13, Steps 2 and 4: integrate the regional spatial
commutator in the first shifted energy inequality. The polynomial loss
exponent is chosen before the form, matrix, measure, temperature and source. -/
theorem first_weighted_shifted_by_regions_internal (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ D Cc Cm Cd Cs : ℝ, 0 < D ∧ 0 < Cc ∧ 0 < Cm ∧ 0 < Cd ∧ 0 < Cs ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
      (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q →
    ∀ (m : ℕ+) (hm : 2 ≤ (m : ℕ)) (a : ℝ) (ha : 0 < a), a ≤ 1 →
    ∀ B L : ℝ, 1 ≤ B → 0 ≤ L →
    ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    (∀ i j, Measurable (fun x => M x i j)) →
    (∃ b : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ b) →
    (∀ᵐ x ∂ν, (M x).IsSymm ∧ a • 1 ≤ M x ∧
      ‖M x - (2 : ℝ) • rieszMatrix s m hm‖ ≤ B) →
    (∀ᵐ x ∂ν,
      let E := M x - (2 : ℝ) • rieszMatrix s m hm
      (∀ i j, |E i j| ≤ L * weightRadius m i j ^ (-(1 + s.val / 2))) ∧
      (∀ i j, |E i j - E (i + 1) j| + |E i j - E i (j + 1)| ≤
        L * weightRadius m i j ^ (-(1 + s.val))) ∧
      (∀ i j, |(E i j - E (i + 1) j) - (E i (j + 1) - E (i + 1) (j + 1))| ≤
        L * weightRadius m i j ^ (-(2 + s.val))) ∧
      (∀ j, ∑ i, |E i j| ≤ L)) →
    ∀ (β : ℝ), 0 < β → ∀ (χ lam : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ))
      (u : Fin (m : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β • M x) ⊤
      (fun i => (if i = i₀ then χ else 0) + lam) u →
    (∀ᵐ x ∂ν, ∑ i, (u i).val x = 0) →
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    let p := (1 - s.val / 2)⁻¹
    let V := fun x => (∑ i, |(rieszMatrix sh m hm *ᵥ
      (fun j => (u j).val x)) i| ^ p) ^ (1 / p)
    let Xρ := fun ρ => Real.sqrt (∑ i, (weightRadius m i i₀ ^ ρ * ‖(u i).val‖) ^ 2)
    let X := Xρ (3 / 2 - s.val)
    let Z := Xρ (1 / 2)
    let Ysq := ∑ i, weightRadius m i i₀ ^ (2 * (1 - s.val / 2)) * Q.2 (u i) (u i)
    let P := Real.sqrt (∫ x, V x ^ 2 ∂ν)
    let μ := a + B ^ 2 / a
    let T := Cs * (1 + μ) ^ (2 * (1 + D)) * (1 + L) ^ (1 + D) * (a / 8) ^ (-D)
    β * a / 8 * X ^ 2 ≤
      (Cc * μ * Real.sqrt (Real.log (2 * (m : ℝ))) * ‖χ‖ +
        Cm * μ * (m : ℝ) * ‖lam‖) * X +
      β * T * X * (Real.log (2 * (m : ℝ)) * Z + P) +
      Cd * (1 + μ) * Real.sqrt (Real.log (2 * (m : ℝ))) * Ysq := by
  obtain ⟨Cc, hCc, hc⟩ := factorized_source_column hz s
  obtain ⟨Cm, hCm, hmodes⟩ := factorized_constant_column s
  obtain ⟨Cd, hCd, hdiff⟩ := factorized_diffusion_lower hz s
  obtain ⟨D, Cs, hD, hCs, hsp⟩ := GlobalCommutators.Internal.spatial_commutator_pointwise_by_regions hz s
  refine ⟨D, Cc, Cm, Cd, Cs, hD, hCc, hCm, hCd, hCs, ?_⟩
  intro Ω _ ν Q hQ m hm a ha ha1 B L hB hL M hMm hMb hM hE β hβ χ lam i₀ u hu hzsum
    sh p V Xρ X Z Ysq P μ T
  let A := factorizationMatrix s m hm a ha B
  let w := fun i => weightRadius m i i₀ ^ (3 / 2 - s.val)
  let v := fun x j => (u j).val x
  let xf := fun x => Real.sqrt (∑ i, (w i * v x i) ^ 2)
  let zf := fun x => Real.sqrt (∑ i, (weightRadius m i i₀ ^ (1 / 2 : ℝ) * v x i) ^ 2)
  let cf := fun x => Real.sqrt (∑ i,
    (w i * ((A * M x) *ᵥ v x) i - ((A * M x) *ᵥ (fun j => w j * v x j)) i) ^ 2)
  have hη : 0 < a / 8 := by positivity
  have hη1 : a / 8 < 1 := by linarith only [ha1]
  have hp : 1 ≤ p := by
    apply (one_le_inv₀ (by linarith [s.property.1, s.property.2] :
      0 < 1 - s.val / 2)).mpr
    linarith [s.property.1]
  have hV : MemLp V 2 ν := DerivativeControl.matrix_lp_memLp p hp (rieszMatrix sh m hm) _
  have hxf : MemLp xf 2 ν := FiniteMixedL2.weighted_memLp w _
  have hzf : MemLp zf 2 ν := FiniteMixedL2.weighted_memLp _ _
  have hmv (j) : Measurable (fun x => v x j) := (Lp.stronglyMeasurable (u j).val).measurable
  have hmul (q : Ω → Fin (m : ℕ) → ℝ) (hq : ∀ j, Measurable fun x => q x j) (i) :
      Measurable (fun x => ((A * M x) *ᵥ q x) i) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply]
    exact Finset.measurable_sum _ (fun j _ =>
      (Finset.measurable_sum _ (fun k _ => (hMm k j).const_mul (A i k))).mul (hq j))
  have hcf : Measurable cf := by
    apply Measurable.sqrt
    apply Finset.measurable_sum
    intro i _
    exact (((hmul v hmv i).const_mul (w i)).sub
      (hmul (fun x j => w j * v x j) (fun j => (hmv j).const_mul _) i)).pow_const 2
  have hpoint : ∀ᵐ x ∂ν, cf x ≤ a / 8 * xf x + T *
      (Real.log (2 * (m : ℝ)) * zf x + V x) := by
    filter_upwards [hE] with x hx
    have hh := hsp m hm a ha B L hL _ hx.1 hx.2.1 hx.2.2.1 hx.2.2.2 i₀ (v x) (a / 8) hη hη1
    have heq : (2 : ℝ) • rieszMatrix s m hm +
        (M x - (2 : ℝ) • rieszMatrix s m hm) = M x := by abel
    dsimp only at hh
    rw [heq] at hh
    exact hh
  have hlog : 0 ≤ Real.log (2 * (m : ℝ)) := by
    apply Real.log_nonneg
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  obtain ⟨hcfLp, hcfb⟩ := spatial_L2_internal cf xf zf V hcf (fun _ => Real.sqrt_nonneg _)
    hxf hzf hV (a / 8) T (Real.log (2 * (m : ℝ))) hη.le (by dsimp [T]; positivity) hlog hpoint
  rw [FiniteMixedL2.weighted_sq_integral, FiniteMixedL2.weighted_sq_integral] at hcfb
  have hs : A.IsSymm := Matrix.isHermitian_iff_isSymm.mp
    (factorizationMatrix_posDef s m hm a ha B).isHermitian
  have hco : ∀ᵐ x ∂ν, ∀ z : Fin (m : ℕ) → ℝ,
      a / 4 * (∑ i, z i ^ 2) ≤ ∑ i, z i * ((A * M x) *ᵥ z) i :=
    hM.mono (fun x hx z => factorized_coercivity s m hm a ha ha1 B hB (M x) hx.1 hx.2.1 hx.2.2 z)
  have hd := hdiff ν m hm a ha ha1 B hB Q hQ i₀ u hzsum
  have he := factorized_energy_internal Q M hMm hMb (hM.mono (fun _ hx => hx.1))
    A hs w β hβ.le (a / 4) (Cd * (1 + μ) * Real.sqrt (Real.log (2 * (m : ℝ))) * Ysq)
    hco i₀ χ lam u hu hd hcfLp
  have hcol := hc m hm a ha B i₀
  have hmode := hmodes m hm a ha B i₀
  have hX : 0 ≤ X := Real.sqrt_nonneg _
  have hsource := mul_le_mul_of_nonneg_right
    (add_le_add (mul_le_mul_of_nonneg_right hcol (norm_nonneg χ))
      (mul_le_mul_of_nonneg_right hmode (norm_nonneg lam))) hX
  have hcs := mul_le_mul_of_nonneg_left hcfb (mul_nonneg hβ.le hX)
  have hXsq : (∑ i, (w i * ‖(u i).val‖) ^ 2) = X ^ 2 :=
    (Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))).symm
  rw [hXsq, Real.sqrt_sq hX] at he
  change β * (a / 4) * X ^ 2 ≤ _ at he
  change _ ≤ (Cc * μ * Real.sqrt (Real.log (2 * (m : ℝ))) * ‖χ‖ +
    Cm * μ * (m : ℝ) * ‖lam‖) * X at hsource
  change β * X * Real.sqrt (∫ x, cf x ^ 2 ∂ν) ≤
    β * X * (a / 8 * X + T * (Real.log (2 * (m : ℝ)) * Z + P)) at hcs
  nlinarith only [he, hsource, hcs]

/-- Internal polynomial bookkeeping for the shifted test. A single bound
on the inverse coercivity, error, logarithm and multiplier absorbs all
coefficients with an exponent depending only on the spatial exponent. -/
theorem shifted_absorption_internal (Cc Cm Cd Cs D βlo : ℝ)
    (hCc : 0 < Cc) (hCm : 0 < Cm) (hCd : 0 < Cd) (hCs : 0 < Cs)
    (hD : 0 < D) (hβlo : 0 < βlo) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T a B L β ℓ F X Z P Y lam : ℝ),
    1 ≤ T → 0 < a → a ≤ 1 → 1 ≤ B → 0 ≤ L → L ≤ T →
    a⁻¹ + B ≤ T → βlo ≤ β → 0 ≤ ℓ → ℓ ≤ T →
    0 ≤ F → 0 ≤ X → 0 ≤ Z → 0 ≤ P → 0 ≤ Y →
    lam ≤ T * (F + Real.sqrt ℓ * Z) →
    let μ := a + B ^ 2 / a
    let S := Cs * (1 + μ) ^ (2 * (1 + D)) * (1 + L) ^ (1 + D) * (a / 8) ^ (-D)
    β * a / 8 * X ^ 2 ≤ (Cc * μ * Real.sqrt ℓ * F + Cm * μ * lam) * X +
      β * S * X * (ℓ * Z + P) + Cd * (1 + μ) * Real.sqrt ℓ * Y →
    X ^ 2 ≤ C * T ^ (10 + 8 * D) * (X * (F + Z + P) + Y) := by
  let E := 1 + D
  let q := 7 + 8 * D
  let A := Cs * 3 ^ (2 * E) * 2 ^ E * 8 ^ D
  let C₀ := 6 * (Cc + Cm + Cd) * βlo⁻¹ + A
  refine ⟨8 * C₀, by dsimp [C₀, A]; positivity, ?_⟩
  intro T a B L β ℓ F X Z P Y lam hT ha ha1 hB hL hLT hab hβ hℓ hℓT
    hF hX hZ hP hY hlam μ S hraw
  have hT0 : 0 < T := by linarith only [hT]
  have hβ0 : 0 < β := hβlo.trans_le hβ
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hshift := GlobalCommutators.Internal.spatial_shift_bound ha ha1 hB hT hab
  change 1 + μ ≤ 3 * T ^ 3 at hshift
  have hiT : a⁻¹ ≤ T := by linarith only [hab, hB]
  have hsqrt : Real.sqrt ℓ ≤ 2 * T := by
    have hs := Real.sq_sqrt hℓ
    nlinarith only [hs, Real.sqrt_nonneg ℓ, hℓT, hT,
      sq_nonneg (T - 1), sq_nonneg (Real.sqrt ℓ - 1)]
  have hpow (u v : ℝ) (huv : u ≤ v) : T ^ u ≤ T ^ v :=
    Real.rpow_le_rpow_of_exponent_le hT huv
  have hSP : S ≤ A * T ^ q := by
    have hη : (a / 8) ^ (-D) = (8 * a⁻¹) ^ D := by
      rw [Real.rpow_neg (by positivity : 0 ≤ a / 8), ← Real.inv_rpow (by positivity : 0 ≤ a / 8)]
      congr 1
      field_simp
    have hpow₁ := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + μ) hshift
      (by dsimp [E]; positivity : 0 ≤ 2 * E)
    have hpow₂ := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + L)
      (show 1 + L ≤ 2 * T by linarith only [hT, hLT]) (by dsimp [E]; positivity : 0 ≤ E)
    have hpow₃ := Real.rpow_le_rpow (by positivity : 0 ≤ 8 * a⁻¹)
      (mul_le_mul_of_nonneg_left hiT (by norm_num)) hD.le
    calc
      S = Cs * (1 + μ) ^ (2 * E) * (1 + L) ^ E * (8 * a⁻¹) ^ D := by
        dsimp only [S, E]
        rw [hη]
      _ ≤ Cs * (3 * T ^ 3) ^ (2 * E) * (2 * T) ^ E * (8 * T) ^ D := by gcongr
      _ = A * T ^ q := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (by positivity),
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hT0.le,
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) hT0.le,
          ← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
        dsimp only [A]
        norm_num only [Nat.cast_ofNat]
        rw [show (3 : ℝ) * (2 * E) = 6 * E by ring]
        have hexp : 6 * E + E + D = q := by dsimp [E, q]; ring
        rw [show Cs * (3 ^ (2 * E) * T ^ (6 * E)) * (2 ^ E * T ^ E) *
          (8 ^ D * T ^ D) = (Cs * 3 ^ (2 * E) * 2 ^ E * 8 ^ D) *
            ((T ^ (6 * E) * T ^ E) * T ^ D) by ring,
          ← Real.rpow_add hT0, ← Real.rpow_add hT0, hexp]
  let J := T ^ (q + 2)
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have h5 : T ^ (5 : ℝ) ≤ J := hpow 5 (q + 2) (by dsimp [q]; linarith only [hD])
  have h4 : T ^ (4 : ℝ) ≤ J := hpow 4 (q + 2) (by dsimp [q]; linarith only [hD])
  have hq : T ^ (q + 1) ≤ J := hpow _ _ (by linarith)
  have hlam' : lam ≤ 2 * T ^ (2 : ℝ) * (F + Z) := by
    have hh := mul_le_mul_of_nonneg_left
      (add_le_add (le_rfl : F ≤ F) (mul_le_mul_of_nonneg_right hsqrt hZ)) hT0.le
    have hf : T * F ≤ 2 * T ^ 2 * F := by
      have : T ≤ 2 * T ^ 2 := by nlinarith only [hT, sq_nonneg (T - 1)]
      exact mul_le_mul_of_nonneg_right this hF
    rw [Real.rpow_two]
    nlinarith only [hlam, hh, hf]
  have hsrc : Cc * μ * Real.sqrt ℓ * F + Cm * μ * lam ≤
      6 * (Cc + Cm) * J * (F + Z) := by
    have hμb : μ ≤ 3 * T ^ (3 : ℝ) := by simpa only [Real.rpow_ofNat] using (by linarith only [hshift] : μ ≤ 3 * T ^ 3)
    have h₁ : Cc * μ * Real.sqrt ℓ * F ≤ 6 * Cc * J * (F + Z) := by
      calc
        _ ≤ Cc * (3 * T ^ (3 : ℝ)) * (2 * T) * F := by gcongr
        _ = 6 * Cc * T ^ (4 : ℝ) * F := by
          rw [show T ^ (4 : ℝ) = T ^ (3 : ℝ) * T by
            rw [← Real.rpow_add_one hT0.ne']; norm_num]
          ring
        _ ≤ _ := by gcongr; exact le_add_of_nonneg_right hZ
    have h₂ : Cm * μ * lam ≤ 6 * Cm * J * (F + Z) := by
      calc
        _ ≤ Cm * μ * (2 * T ^ (2 : ℝ) * (F + Z)) := by gcongr
        _ ≤ Cm * (3 * T ^ (3 : ℝ)) * (2 * T ^ (2 : ℝ) * (F + Z)) := by gcongr
        _ = 6 * Cm * T ^ (5 : ℝ) * (F + Z) := by
          rw [show T ^ (5 : ℝ) = T ^ (3 : ℝ) * T ^ (2 : ℝ) by rw [← Real.rpow_add hT0]; norm_num]
          ring
        _ ≤ _ := by gcongr
    linarith only [h₁, h₂]
  have hspatial : S * (ℓ * Z + P) ≤ A * J * (Z + P) := by
    have hh : ℓ * Z + P ≤ T * (Z + P) := by
      nlinarith only [mul_le_mul_of_nonneg_right hℓT hZ,
        mul_le_mul_of_nonneg_right hT hP]
    calc
      _ ≤ (A * T ^ q) * (T * (Z + P)) := by gcongr
      _ = A * T ^ (q + 1) * (Z + P) := by rw [Real.rpow_add_one hT0.ne']; ring
      _ ≤ _ := by gcongr
  have hdiff : Cd * (1 + μ) * Real.sqrt ℓ ≤ 6 * Cd * J := by
    calc
      _ ≤ Cd * (3 * T ^ 3) * (2 * T) := by gcongr
      _ = 6 * Cd * T ^ (4 : ℝ) := by norm_num [Real.rpow_ofNat]; ring
      _ ≤ _ := by gcongr
  let H := X * (F + Z + P) + Y
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hbr : 6 * (Cc + Cm) * J * (F + Z) * X +
      β * (A * J * (Z + P)) * X + 6 * Cd * J * Y ≤ β * C₀ * J * H := by
    have hβinv : 1 ≤ β * βlo⁻¹ := by simpa only [div_eq_mul_inv] using (one_le_div₀ hβlo).mpr hβ
    have hs₀ : 0 ≤ 6 * (Cc + Cm) * J * X * (F + Z) := by positivity
    have hd₀ : 0 ≤ 6 * Cd * J * Y := by positivity
    have hs₁ := mul_le_mul_of_nonneg_right hβinv hs₀
    have hd₁ := mul_le_mul_of_nonneg_right hβinv hd₀
    dsimp only [C₀, H]
    nlinarith only [hs₁, hd₁,
      mul_nonneg (by positivity : 0 ≤ β * A * J) (by positivity : 0 ≤ X * F + Y),
      mul_nonneg (by positivity : 0 ≤ 6 * (Cc + Cm) * β * βlo⁻¹ * J) (by positivity : 0 ≤ X * P + Y),
      mul_nonneg (by positivity : 0 ≤ 6 * Cd * β * βlo⁻¹ * J) (by positivity : 0 ≤ X * (F + Z + P))]
  have hraw' : β * a / 8 * X ^ 2 ≤ β * C₀ * J * H := by
    apply hraw.trans
    apply le_trans _ hbr
    apply add_le_add
    · apply add_le_add
      · exact mul_le_mul_of_nonneg_right hsrc hX
      · have hh := mul_le_mul_of_nonneg_left hspatial (mul_nonneg hβ0.le hX)
        nlinarith only [hh]
    · exact mul_le_mul_of_nonneg_right hdiff hY
  have hat : 1 ≤ a * T := by simpa only [mul_comm] using (inv_le_iff_one_le_mul₀ ha).mp hiT
  have heq : T ^ (10 + 8 * D) = T * J := by
    dsimp only [J, q]
    rw [mul_comm T, ← Real.rpow_add_one hT0.ne']
    congr 1
    ring
  rw [heq]
  apply (mul_le_mul_iff_right₀ (by positivity : 0 < β * a / 8)).mp
  have hh := mul_le_mul_of_nonneg_right hat
    (show 0 ≤ β * C₀ * J * H by dsimp [C₀, A]; positivity)
  nlinarith only [hraw', hh]

/-- See the proof of Lemma 5.13 in the paper, first weighted inequality equation (5.51).
The commutator and energy estimates follow from the periodized matrix bounds. The loss exponent precedes ε, the
prefactor, and the temperature interval. The source may be any L² class. -/
theorem global_energy_first (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ)
    (hκstar : 0 ≤ κstar) (hγstar : 0 ≤ γstar) (M₀ : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε →
    ∀ Cstar : ℝ, 1 ≤ Cstar →
    ∀ βlo : ℝ, 0 < βlo → ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (Q : ScalarFormData ν),
    IsClosedScalarDirichletForm Q → ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ)),
    2 ≤ (n : ℕ) → (n : ℕ) ≤ (m : ℕ) →
    (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
    let K := ⌊(n : ℝ) ^ ε⌋₊ ^ M₀
    1 ≤ K → 4 * K ≤ (m : ℕ) →
    ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M →
    ∀ β : ℝ, βlo ≤ β → β ≤ βhi →
    ∀ (χ : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _)
      (fun i => if i = i₀ then χ else 0) u →
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    let p := (1 - s.val / 2)⁻¹
    let V := fun x => (∑ i, |(rieszMatrix sh m hm *ᵥ
      (fun j => (u j).val x)) i| ^ p) ^ (1 / p)
    let Xρ := fun ρ => Real.sqrt (∑ i, (weightRadius m i i₀ ^ ρ * ‖(u i).val‖) ^ 2)
    Xρ (3 / 2 - s.val) ^ 2 ≤ C * (n : ℝ) ^ (κ * ε) *
      (Xρ (3 / 2 - s.val) * (‖χ‖ + Xρ (1 / 2) + Real.sqrt (∫ x, V x ^ 2 ∂ν)) +
        ∑ i, weightRadius m i i₀ ^ (2 * (1 - s.val / 2)) * Q.2 (u i) (u i)) := by
  obtain ⟨κe, hκe, herr⟩ := global_error_differences s κstar γstar hκstar hγstar M₀
  obtain ⟨κm, hκm, hmult⟩ := global_energy_multiplier s κstar γstar hκstar hγstar M₀
  obtain ⟨D, Cc, Cm, Cd, Cs, hD, hCc, hCm, hCd, hCs, hraw⟩ :=
    first_weighted_shifted_by_regions_internal hzeta s
  let r := 10 + 8 * D
  let k := κe + κm + 1
  have hr : 0 < r := by dsimp [r]; positivity
  have hk : 0 < k := by dsimp [k]; positivity
  refine ⟨k * r, mul_pos hk hr, fun ε hε Cstar hCstar βlo hβlo βhi hβhi => ?_⟩
  obtain ⟨Ce, hCe, herr⟩ := herr ε hε Cstar hCstar
  obtain ⟨Cl, hCl, hmult⟩ := hmult ε hε Cstar hCstar βhi (hβlo.le.trans hβhi)
  obtain ⟨Clog, hClog, hlog⟩ := EllipticRegularity.log_absorption s hε (by norm_num : (0 : ℝ) < 1)
  obtain ⟨Ca, hCa, habs⟩ := shifted_absorption_internal Cc Cm Cd Cs D βlo hCc hCm hCd hCs hD hβlo
  let A := Ce + Cl + Clog + 1
  have hA : 1 ≤ A := by dsimp [A]; linarith only [hCe, hCl, hClog]
  have hA0 : 0 < A := by linarith only [hA]
  refine ⟨Ca * A ^ r, by positivity, ?_⟩
  intro Ω _ ν Q hQ n m hm hn hnm hmn K hK hKm M hM β hβloβ hββhi χ i₀ u hu sh p V Xρ
  let R := (n : ℝ) ^ (k * ε)
  let T := A * R
  let L := Ce * (n : ℝ) ^ (κe * ε)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by positivity
  have hR : 1 ≤ R := Real.one_le_rpow hn1 (mul_nonneg hk.le hε.le)
  have hT : 1 ≤ T := one_le_mul_of_one_le_of_one_le hA hR
  have hpow (q : ℝ) (hq : q ≤ k) : (n : ℝ) ^ (q * ε) ≤ R :=
    Real.rpow_le_rpow_of_exponent_le hn1 (mul_le_mul_of_nonneg_right hq hε.le)
  have heT : L ≤ T := by
    apply mul_le_mul
    · dsimp [A]; linarith only [hCl, hClog]
    · exact hpow κe (by dsimp [k]; linarith only [hκm])
    · positivity
    · exact hA0.le
  have hlT : Cl * (n : ℝ) ^ (κm * ε) ≤ T := by
    apply mul_le_mul
    · dsimp [A]; linarith only [hCe, hClog]
    · exact hpow κm (by dsimp [k]; linarith only [hκe])
    · positivity
    · exact hA0.le
  have hlogT : Real.log (2 * (m : ℝ)) ≤ T := by
    have hh := hlog n m (by linarith only [hmn, Real.rpow_nonneg hn0.le (1 / 2 + 1 / s.val)])
    rw [Real.rpow_one] at hh
    apply hh.trans
    apply mul_le_mul
    · dsimp [A]; linarith only [hCe, hCl]
    · simpa only [one_mul] using hpow 1 (by dsimp [k]; linarith only [hκe, hκm])
    · positivity
    · exact hA0.le
  obtain ⟨a, B, ha, ha1, hB, hab, he⟩ := herr n m hm hn hnm hmn hK hKm ν M hM
  obtain ⟨lam, _, hfull, _, hlam⟩ := hmult ν Q n m hm hn hnm hmn hK hKm M hM β
    (hβlo.le.trans hβloβ) hββhi χ i₀ u hu
  have hsym : ∀ᵐ x ∂ν, (M x).IsSymm := by
    filter_upwards [hM.2.1] with x hx
    ext i j
    exact hx.1 j i
  have hcoef : ∀ᵐ x ∂ν, (M x).IsSymm ∧ a • 1 ≤ M x ∧
      ‖M x - (2 : ℝ) • rieszMatrix s m hm‖ ≤ B := by
    filter_upwards [hsym, he] with x hx he
    exact ⟨hx, he.2.2.2.2.2.1, he.2.2.2.2.2.2⟩
  have herror : ∀ᵐ x ∂ν,
      let E := M x - (2 : ℝ) • rieszMatrix s m hm
      (∀ i j, |E i j| ≤ L * weightRadius m i j ^ (-(1 + s.val / 2))) ∧
      (∀ i j, |E i j - E (i + 1) j| + |E i j - E i (j + 1)| ≤
        L * weightRadius m i j ^ (-(1 + s.val))) ∧
      (∀ i j, |(E i j - E (i + 1) j) - (E i (j + 1) - E (i + 1) (j + 1))| ≤
        L * weightRadius m i j ^ (-(2 + s.val))) ∧
      (∀ j, ∑ i, |E i j| ≤ L) := by
    filter_upwards [he] with x hx
    simpa only [L, weightRadius, show -(1 + s.val / 2) = -1 - s.val / 2 by ring,
      show -(1 + s.val) = -1 - s.val by ring, show -(2 + s.val) = -2 - s.val by ring]
      using ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.2.1⟩
  have hβ : 0 < β := hβlo.trans_le hβloβ
  have hraw' := hraw ν Q hQ m hm a ha ha1 B L hB (by dsimp [L]; positivity) M hM.1
    (SchurRestriction.periodized_scaled_bounded 1 hM |>.imp (fun b hb => by simpa using hb))
    hcoef herror β hβ χ lam i₀ u hfull hu.1.1
  have hlog0 : 0 ≤ Real.log (2 * (m : ℝ)) := by
    apply Real.log_nonneg
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hmultT := hlam.trans (mul_le_mul_of_nonneg_right hlT (by positivity :
    0 ≤ ‖χ‖ + Real.sqrt (Real.log (2 * (m : ℝ))) * Xρ (1 / 2)))
  have hh := habs T a B L β (Real.log (2 * (m : ℝ))) ‖χ‖
    (Xρ (3 / 2 - s.val)) (Xρ (1 / 2)) (Real.sqrt (∫ x, V x ^ 2 ∂ν))
    (∑ i, weightRadius m i i₀ ^ (2 * (1 - s.val / 2)) * Q.2 (u i) (u i))
    ((m : ℝ) * ‖lam‖) hT ha ha1 hB (by dsimp [L]; positivity) heT
    (hab.trans heT) hβloβ hlog0 hlogT (norm_nonneg _) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (Finset.sum_nonneg (fun i _ => mul_nonneg (Real.rpow_nonneg
      (by linarith [one_le_weightRadius m i i₀]) _) (hQ.2.2.1 _))) hmultT
    (by simpa only [mul_assoc] using hraw')
  have hcoef : Ca * T ^ (10 + 8 * D) = (Ca * A ^ r) * (n : ℝ) ^ ((k * r) * ε) := by
    change Ca * T ^ r = _
    dsimp only [T, R]
    rw [Real.mul_rpow hA0.le (by positivity), ← Real.rpow_mul hn0.le,
      show (k * ε) * r = (k * r) * ε by ring]
    ring
  rw [hcoef] at hh
  exact hh

/-- See the proof of Lemma 5.13 in the paper, all clauses together: both weighted
inequalities, the canonical L² multiplier, its summed identity, and the
unweighted value and diffusion bound. All constants share the prescribed
uniform polynomial loss. -/
theorem global_energy (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ)
    (hκstar : 0 < κstar) (hγstar : 0 ≤ γstar) (M₀ : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε →
    ∀ Cstar : ℝ, 1 ≤ Cstar →
    ∀ βlo : ℝ, 0 < βlo → ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
      (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q →
    ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ)),
    2 ≤ (n : ℕ) → (n : ℕ) ≤ (m : ℕ) →
    (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
    let K := ⌊(n : ℝ) ^ ε⌋₊ ^ M₀
    1 ≤ K → 4 * K ≤ (m : ℕ) →
    ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M →
    ∀ β : ℝ, βlo ≤ β → β ≤ βhi →
    ∀ (χ : Q.1) (i₀ : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _)
      (fun i => if i = i₀ then χ.val else 0) u →
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    let p := (1 - s.val / 2)⁻¹
    let V := fun x => (∑ i, |(rieszMatrix sh m hm *ᵥ
      (fun j => (u j).val x)) i| ^ p) ^ (1 / p)
    let Xρ := fun ρ => Real.sqrt (∑ i, (weightRadius m i i₀ ^ ρ * ‖(u i).val‖) ^ 2)
    let X := Xρ (3 / 2 - s.val)
    let Z := Xρ (1 / 2)
    let Ysq := ∑ i, weightRadius m i i₀ ^ (2 * (1 - s.val / 2)) * Q.2 (u i) (u i)
    let P := Real.sqrt (∫ x, V x ^ 2 ∂ν)
    let Cn := C * (n : ℝ) ^ (κ * ε)
    ∃ lam : Lp ℝ 2 ν,
      (∀ᵐ x ∂ν, lam x = gapMultiplierField m Q (fun x => β • M x)
        (fun i => if i = i₀ then χ.val else 0) u x) ∧
      WeightedWeakSolution Q (fun x => β • M x) ⊤
        (fun i => (if i = i₀ then χ.val else 0) + lam) u ∧
      (∀ᵐ x ∂ν, (m : ℝ) * lam x =
        β * (∑ i, ∑ j, (M x - (2 : ℝ) • rieszMatrix s m hm) i j * (u j).val x) - χ.val x) ∧
      (m : ℝ) * ‖lam‖ ≤ Cn * (‖χ.val‖ + Real.sqrt (Real.log (2 * (m : ℝ))) * Z) ∧
      Integrable (fun x => V x ^ 2) ν ∧
      X ^ 2 ≤ Cn * (X * (‖χ.val‖ + Z + P) + Ysq) ∧
      (∀ η : ℝ, 0 < η → η < 1 / 4 →
        Ysq ≤ Cn * (‖χ.val‖ ^ 2 + X * (η ^ (3 - s.val) * X + η⁻¹ * P + ‖χ.val‖ + Z))) ∧
      Real.sqrt (∑ i, ‖(u i).val‖ ^ 2) + Real.sqrt (∑ i, Q.2 (u i) (u i)) ≤ Cn * ‖χ.val‖ := by
  obtain ⟨κ₁, hκ₁, h₁⟩ := global_energy_first hzeta s κstar γstar hκstar.le hγstar M₀
  obtain ⟨κ₂, hκ₂, h₂⟩ := global_energy_second hzeta s κstar γstar hκstar hγstar M₀
  obtain ⟨κm, hκm, hm⟩ := global_energy_multiplier s κstar γstar hκstar.le hγstar M₀
  let κ := κ₁ + κ₂ + κm + κstar
  have hκ : 0 < κ := by dsimp [κ]; positivity
  refine ⟨κ, hκ, fun ε hε Cstar hCstar βlo hβlo βhi hβhi => ?_⟩
  obtain ⟨C₁, hC₁, h₁⟩ := h₁ ε hε Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨C₂, hC₂, h₂⟩ := h₂ ε hε Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Cm, hCm, hm⟩ := hm ε hε Cstar hCstar βhi (hβlo.le.trans hβhi)
  let Cu := 1 + 2 * βlo⁻¹ * Cstar
  have hCu : 0 < Cu := by dsimp [Cu]; positivity
  let C := C₁ + C₂ + Cm + Cu
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Ω _ ν _ Q hQ n m hms hn hnm hmn K hK hKm M hM β hβloβ hββhi χ i₀ u hu
    sh p V Xρ X Z Ysq P Cn
  have hcoef (c t : ℝ) (hc : 0 ≤ c) (hcC : c ≤ C) (htκ : t ≤ κ) :
      c * (n : ℝ) ^ (t * ε) ≤ Cn := by
    apply mul_le_mul hcC
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast n.pos : (1 : ℝ) ≤ n)
        (mul_le_mul_of_nonneg_right htκ hε.le)) (by positivity) hC.le
  have hc₁ := hcoef C₁ κ₁ hC₁.le (by dsimp [C]; linarith only [hC₂, hCm, hCu])
    (by dsimp [κ]; linarith only [hκ₂, hκm, hκstar])
  have hc₂ := hcoef C₂ κ₂ hC₂.le (by dsimp [C]; linarith only [hC₁, hCm, hCu])
    (by dsimp [κ]; linarith only [hκ₁, hκm, hκstar])
  have hcm := hcoef Cm κm hCm.le (by dsimp [C]; linarith only [hC₁, hC₂, hCu])
    (by dsimp [κ]; linarith only [hκ₁, hκ₂, hκstar])
  have hcu := hcoef Cu κstar hCu.le (by dsimp [C]; linarith only [hC₁, hC₂, hCm])
    (by dsimp [κ]; linarith only [hκ₁, hκ₂, hκm])
  obtain ⟨lam, hlam, hfull, hid, hl⟩ := hm ν Q n m hms hn hnm hmn hK hKm M hM β
    (hβlo.le.trans hβloβ) hββhi χ.val i₀ u hu
  obtain ⟨_, _, _, hi, hy⟩ := h₂ ν Q hQ n m hms hn hnm hmn hK hKm M hM β hβloβ hββhi χ i₀ u hu
  have hx := h₁ ν Q hQ n m hms hn hnm hmn hK hKm M hM β hβloβ hββhi χ.val i₀ u hu
  have hY : 0 ≤ Ysq := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (Real.rpow_nonneg (by linarith [one_le_weightRadius m i i₀]) _) (hQ.2.2.1 _))
  have hX : 0 ≤ X := Real.sqrt_nonneg _
  have hZ : 0 ≤ Z := Real.sqrt_nonneg _
  have hP : 0 ≤ P := Real.sqrt_nonneg _
  refine ⟨lam, hlam, hfull, hid, hl.trans (mul_le_mul_of_nonneg_right hcm (by positivity)), hi,
    hx.trans (mul_le_mul_of_nonneg_right hc₁ (by positivity)), ?_, ?_⟩
  · intro η hη hη'
    exact (hy η hη hη').trans (mul_le_mul_of_nonneg_right hc₂ (by positivity))
  · exact (global_energy_unweighted s n m hms K Cstar κstar γstar ε hCstar hκstar.le hε.le
      Q hQ M hM βlo β hβlo hβloβ χ.val i₀ u hu).trans
      (mul_le_mul_of_nonneg_right hcu (norm_nonneg _))

/-- See Lemma 5.13 of the paper, the extended weighted norm agrees
with the finite real component norm on L² fields. -/
theorem weighted_norm_toReal (m : ℕ+) (i₀ : Fin (m : ℕ)) (ρ : ℝ)
    (u : Fin (m : ℕ) → Lp ℝ 2 ν) :
    (weightedRadiusNorm ν m i₀ ρ (fun x j => u j x)).toReal =
      Real.sqrt (∑ j, (weightRadius m j i₀ ^ ρ * ‖u j‖) ^ 2) := by
  rw [← GlobalCommutators.Internal.spatial_weighted_norm_eq ν m i₀ ρ _
    (fun j => (Lp.stronglyMeasurable (u j)).measurable),
    ← sqrt_integral_sq_eq _ (FiniteMixedL2.weighted_memLp _ _),
    FiniteMixedL2.weighted_sq_integral]

/-- See Lemma 5.13 of the paper, weighted interpolation in finite real norms.
The two endpoint cases are included. -/
theorem weighted_norm_interpolation (m : ℕ+) (i₀ : Fin (m : ℕ))
    (u : Fin (m : ℕ) → Lp ℝ 2 ν) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) :
    Real.sqrt (∑ j, (weightRadius m j i₀ ^ a * ‖u j‖) ^ 2) ≤
      (Real.sqrt (∑ j, ‖u j‖ ^ 2)) ^ (1 - a / b) *
        (Real.sqrt (∑ j, (weightRadius m j i₀ ^ b * ‖u j‖) ^ 2)) ^ (a / b) := by
  have h := weightedRadiusNorm_le_mul_rpow ν m i₀
    (fun j => (Lp.stronglyMeasurable (u j)).measurable) ha hab hb
  have hfin (ρ : ℝ) : weightedRadiusNorm ν m i₀ ρ (fun x j => u j x) ≠ ⊤ := by
    rw [← GlobalCommutators.Internal.spatial_weighted_norm_eq ν m i₀ ρ _
      (fun j => (Lp.stronglyMeasurable (u j)).measurable)]
    exact (FiniteMixedL2.weighted_memLp _ _).eLpNorm_ne_top
  have hθ : 0 ≤ a / b := div_nonneg ha hb.le
  have hθ' : 0 ≤ 1 - a / b := by have := (div_le_one hb).mpr hab; linarith
  have hh := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hθ' (hfin 0))
      (ENNReal.rpow_ne_top_of_nonneg hθ (hfin b))) h
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, weighted_norm_toReal,
    Real.rpow_zero, one_mul] using hh

/-- Internal comparison of finite weighted L² norms. -/
theorem weighted_norm_mono_internal {ι : Type*} [Fintype ι]
    (u : ι → Lp ℝ 2 ν) (w v : ι → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hw : ∀ i, 0 ≤ w i) (_hv : ∀ i, 0 ≤ v i) (h : ∀ i, w i ≤ C * v i) :
    Real.sqrt (∑ i, (w i * ‖u i‖) ^ 2) ≤ C * Real.sqrt (∑ i, (v i * ‖u i‖) ^ 2) := by
  have hh := Real.sqrt_le_sqrt (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    pow_le_pow_left₀ (mul_nonneg (hw i) (norm_nonneg (u i)))
      (mul_le_mul_of_nonneg_right (h i) (norm_nonneg (u i))) 2))
  simp only [mul_assoc, mul_pow, ← Finset.mul_sum] at hh
  rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC] at hh
  simpa only [mul_pow] using hh

/-- See Lemma 5.13 of the paper, comparison of the elliptic estimate's weight
`1 + d^ρ` with the literal regularized radius `(1 + d)^ρ`. -/
theorem elliptic_weight_comparison (m : ℕ+) (i₀ : Fin (m : ℕ)) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (u : Fin (m : ℕ) → Lp ℝ 2 ν) :
    Real.sqrt (∫ x, ∑ j, ((1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ ρ) * u j x) ^ 2 ∂ν) ≤
      2 * Real.sqrt (∑ j, (weightRadius m j i₀ ^ ρ * ‖u j‖) ^ 2) := by
  rw [(CyclicFourierL2.weighted_integral_sq _ u).2]
  apply weighted_norm_mono_internal u _ _ 2 (by norm_num)
    (fun _ => by positivity) (fun j => Real.rpow_nonneg
      (by linarith [one_le_weightRadius m j i₀]) _)
  intro j
  have h₁ : 1 ≤ weightRadius m j i₀ ^ ρ := Real.one_le_rpow (one_le_weightRadius m j i₀) hρ
  have h₂ := Real.rpow_le_rpow (Nat.cast_nonneg (Riesz1.cyclicIndexDistance m j i₀))
    (show (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ≤ weightRadius m j i₀ by
      dsimp [weightRadius]; linarith) hρ
  linarith only [h₁, h₂]

/-- See Lemma 5.13 of the paper, the required elliptic interpolation in
exactly the regularized weights of Subsection 5.4, for arbitrary L² sources. -/
theorem elliptic_regularized (hzeta : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (κstar γstar : ℝ) (hκstar : 0 < κstar) (hγstar : 0 < γstar) (M₀ : ℕ+) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε →
    ∀ Cstar : ℝ, 1 ≤ Cstar → ∀ βlo : ℝ, 0 < βlo → ∃ C : ℝ, 0 < C ∧
    ∀ β : ℝ, βlo ≤ β →
    ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
      (n m : ℕ+) (hm : 2 ≤ (m : ℕ)),
    (n : ℕ) ≤ (m : ℕ) → (m : ℝ) ≤ 3 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
    ⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ) ≤ (m : ℕ) / 4 →
    ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm (⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ))
      Cstar κstar γstar ε M →
    ∀ Q : ScalarFormData ν, IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
    ∀ (i₀ : Fin (m : ℕ)) (χ : Lp ℝ 2 ν) (u : Fin (m : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _)
      (fun i => if i = i₀ then χ else 0) u →
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    let p := (1 - s.val / 2)⁻¹
    let V := fun x => (∑ i, |(rieszMatrix sh m hm *ᵥ
      (fun j => (u j).val x)) i| ^ p) ^ (1 / p)
    let Xρ := fun ρ => Real.sqrt (∑ i, (weightRadius m i i₀ ^ ρ * ‖(u i).val‖) ^ 2)
    Integrable (fun x => V x ^ 2) ν ∧
      Real.sqrt (∫ x, V x ^ 2 ∂ν) ≤ C * (n : ℝ) ^ (κ * ε) *
        (‖χ‖ + Xρ (1 / 2)) ^ s.val * Xρ (3 / 2 - s.val) ^ (1 - s.val) := by
  obtain ⟨κ, hκ, hb⟩ := EllipticRegularity.elliptic_L2 hzeta s κstar γstar hκstar hγstar M₀
  refine ⟨κ, hκ, fun ε hε Cstar hCstar βlo hβlo => ?_⟩
  obtain ⟨C, hC, hb⟩ := hb ε hε Cstar hCstar βlo hβlo
  refine ⟨2 * C, by positivity, ?_⟩
  intro β hβ Ω _ ν _ n m hm hnm hmn hK M hM Q hQ hQc i₀ χ u hu sh p V Xρ
  obtain ⟨_, _, hi, he⟩ := hb β hβ ν n m hm hnm hmn hK M hM Q hQ hQc i₀ χ u hu
  have hp : 1 / p = 1 - s.val / 2 := by simp only [p, one_div, inv_inv]
  have hi' : Integrable (fun x => V x ^ 2) ν := by simpa only [V, hp, rieszMatrix] using hi
  refine ⟨hi', ?_⟩
  have h₁ := elliptic_weight_comparison m i₀ (1 / 2) (by norm_num) (fun j => (u j).val)
  have h₂ := elliptic_weight_comparison m i₀ (3 / 2 - s.val)
    (by linarith [s.property.2]) (fun j => (u j).val)
  have hsource : ‖χ‖ + Real.sqrt (∫ x, ∑ j,
      ((1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (1 / 2 : ℝ)) * (u j).val x) ^ 2 ∂ν) ≤
      2 * (‖χ‖ + Xρ (1 / 2)) := by linarith only [h₁, norm_nonneg χ]
  have hbase := Real.rpow_le_rpow (by positivity) hsource s.property.1.le
  have hweight := Real.rpow_le_rpow (by positivity) h₂ (by linarith [s.property.2] : 0 ≤ 1 - s.val)
  have hbound := he.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left hbase (by positivity)) hweight (by positivity) (by positivity))
  have heq : C * (n : ℝ) ^ (κ * ε) * (2 * (‖χ‖ + Xρ (1 / 2))) ^ s.val *
      (2 * Xρ (3 / 2 - s.val)) ^ (1 - s.val) =
      (2 * C) * (n : ℝ) ^ (κ * ε) *
        (‖χ‖ + Xρ (1 / 2)) ^ s.val * Xρ (3 / 2 - s.val) ^ (1 - s.val) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity),
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg _)]
    calc
      _ = (C * (n : ℝ) ^ (κ * ε) * (‖χ‖ + Xρ (1 / 2)) ^ s.val *
          Xρ (3 / 2 - s.val) ^ (1 - s.val)) * (2 ^ s.val * 2 ^ (1 - s.val)) := by ring
      _ = _ := by rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; norm_num; ring
  rw [heq] at hbound
  simpa only [V, hp, rieszMatrix] using hbound

/-- See Lemma 5.13 of the paper, the homogeneous subquadratic absorption
used for its four monomials. The coefficient exponent is explicit and
depends only on the subquadratic power. Zero source and zero coefficient
are included. -/
theorem subquadratic_absorption (t : ℝ) (ht : 0 < t) (ht2 : t < 2)
    (A F X : ℝ) (hA : 0 ≤ A) (hF : 0 ≤ F) (hX : 0 ≤ X) :
    A * F ^ (2 - t) * X ^ t ≤ X ^ 2 / 16 +
      16 ^ (t / (2 - t)) * A ^ (2 / (2 - t)) * F ^ 2 := by
  have hδ : 0 < 2 - t := by linarith only [ht2]
  rcases hA.eq_or_lt with rfl | hA
  · simp only [zero_mul]
    positivity
  rcases hF.eq_or_lt with rfl | hF
  · rw [Real.zero_rpow hδ.ne']
    simp only [mul_zero, zero_mul, zero_pow (by norm_num : 2 ≠ 0), add_zero]
    positivity
  let R := (16 * A) ^ ((2 - t)⁻¹) * F
  have hR : 0 < R := by dsimp [R]; positivity
  by_cases hXR : X ≤ R
  · have hp := Real.rpow_le_rpow hX hXR ht.le
    have hh := mul_le_mul_of_nonneg_left hp
      (mul_nonneg hA.le (Real.rpow_nonneg hF.le (2 - t)))
    have he : A * F ^ (2 - t) * R ^ t =
        16 ^ (t / (2 - t)) * A ^ (2 / (2 - t)) * F ^ 2 := by
      dsimp only [R]
      rw [Real.mul_rpow (by positivity) hF.le, ← Real.rpow_mul (by positivity : 0 ≤ 16 * A),
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 16) hA.le]
      have hpowF : F ^ (2 - t) * F ^ t = F ^ 2 := by rw [← Real.rpow_add hF]; norm_num
      have hpowA : A * A ^ ((2 - t)⁻¹ * t) = A ^ (2 / (2 - t)) := by
        rw [mul_comm A, ← Real.rpow_add_one hA.ne']
        congr 1
        field_simp
        ring
      calc
        _ = 16 ^ ((2 - t)⁻¹ * t) * (A * A ^ ((2 - t)⁻¹ * t)) *
          (F ^ (2 - t) * F ^ t) := by ring
        _ = _ := by rw [hpowF, hpowA,
          show (2 - t)⁻¹ * t = t / (2 - t) by rw [div_eq_mul_inv]; ring]
    rw [he] at hh
    exact hh.trans (le_add_of_nonneg_left (by positivity))
  · have hRX : R ≤ X := le_of_lt (lt_of_not_ge hXR)
    have hp := Real.rpow_le_rpow hR.le hRX hδ.le
    have he : R ^ (2 - t) = 16 * A * F ^ (2 - t) := by
      dsimp only [R]
      rw [Real.mul_rpow (by positivity) hF.le, ← Real.rpow_mul (by positivity : 0 ≤ 16 * A),
        inv_mul_cancel₀ hδ.ne', Real.rpow_one]
    rw [he] at hp
    have hh := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hX t)
    have hxp : X ^ (2 - t) * X ^ t = X ^ 2 := by
      rw [← Real.rpow_add' hX (by linarith only [ht2, ht] : 2 - t + t ≠ 0)]
      norm_num
    rw [hxp] at hh
    have hm : A * F ^ (2 - t) * X ^ t ≤ X ^ 2 / 16 := by linarith only [hh]
    exact hm.trans (le_add_of_nonneg_right (by positivity))

end Riesz2.GlobalDecay
