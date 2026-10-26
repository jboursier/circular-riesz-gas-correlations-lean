/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.DerivativeControl
public import Riesz2.DecayLong.GlobalReferenceErrorPart2
public import Riesz2.DecayLong.GlobalCancellation
public import Riesz2.DecayLong.EllipticRegularity

/-!
# Energy and multipliers for the constrained global equation

The unweighted energy and summed-equation parts of the proof of Lemma 5.13. The multiplier is the normal
multiplier, restored in the full scalar form domain. Scalar dimension
and component dimension are independent, and the source may be any L² class.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter
open scoped BigOperators Matrix

namespace Riesz2.GlobalDecay

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

/-- The Euclidean L² norm of a point source, including a zero source.
Used in the proof of Lemma 5.13. -/
theorem point_source_norm (m : ℕ+) (i₀ : Fin (m : ℕ)) (χ : Lp ℝ 2 ν) :
    ‖(WithLp.toLp 2 (fun i => if i = i₀ then χ else 0) :
      PiLp 2 (fun _ : Fin (m : ℕ) => Lp ℝ 2 ν))‖ = ‖χ‖ := by
  rw [PiLp.norm_eq_of_L2]
  simp only [apply_ite norm, norm_zero, ite_pow, zero_pow (by norm_num : 2 ≠ 0)]
  rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _), Real.sqrt_sq (norm_nonneg _)]

/-- See the proof of Lemma 5.13 in the paper, unweighted energy part, for every L²
source. Both estimates keep their exact coercivity constants. -/
theorem unweighted_energy (s : Riesz1.RieszExponent) (n m : ℕ+)
    (hm : 2 ≤ (m : ℕ)) (K : ℕ) (Cstar κstar γstar ε : ℝ) (hCstar : 1 ≤ Cstar)
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M)
    (β : ℝ) (hβ : 0 < β) (χ : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ))
    (u : Fin (m : ℕ) → Q.1)
    (hu : WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _)
      (fun i => if i = i₀ then χ else 0) u) :
    let a := Cstar⁻¹ * (n : ℝ) ^ (-κstar * ε)
    Real.sqrt (∑ i, ‖(u i).val‖ ^ 2) ≤ (β * a)⁻¹ * ‖χ‖ ∧
      Real.sqrt (∑ i, Q.2 (u i) (u i)) ≤ (Real.sqrt (β * a))⁻¹ * ‖χ‖ := by
  let a := Cstar⁻¹ * (n : ℝ) ^ (-κstar * ε)
  have ha : 0 < a := SchurRestriction.periodized_mass_pos hCstar
  have hl : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
      ∀ z : Fin (m : ℕ) → ℝ,
        a * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j :=
    hM.2.1.mono (fun _ hx => ⟨hx.1, hx.2.2.1⟩)
  have he := (AbstractEquation.existence_energy Q hQ β hβ M hM.1 a ha hl
    (zeroSumComponents _) (fun i => if i = i₀ then χ else 0)).2 u hu
  rw [point_source_norm] at he
  simpa only [PiLp.norm_eq_of_L2, WithLp.ofLp_toLp] using he

/-- See the proof of Lemma 5.13 in the paper, uniform unweighted bound. The displayed
prefactor depends only on the structural prefactor and the lower temperature.
The loss exponent is exactly the structural coercivity exponent. -/
theorem global_energy_unweighted (s : Riesz1.RieszExponent) (n m : ℕ+)
    (hm : 2 ≤ (m : ℕ)) (K : ℕ) (Cstar κstar γstar ε : ℝ)
    (hCstar : 1 ≤ Cstar) (hκstar : 0 ≤ κstar) (hε : 0 ≤ ε)
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M)
    (βlo β : ℝ) (hβlo : 0 < βlo) (hβ : βlo ≤ β)
    (χ : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1)
    (hu : WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _)
      (fun i => if i = i₀ then χ else 0) u) :
    Real.sqrt (∑ i, ‖(u i).val‖ ^ 2) + Real.sqrt (∑ i, Q.2 (u i) (u i)) ≤
      (1 + 2 * βlo⁻¹ * Cstar) * (n : ℝ) ^ (κstar * ε) * ‖χ‖ := by
  let a := Cstar⁻¹ * (n : ℝ) ^ (-κstar * ε)
  have ha : 0 < a := SchurRestriction.periodized_mass_pos hCstar
  have hβpos := hβlo.trans_le hβ
  obtain ⟨hv, hg⟩ := unweighted_energy s n m hm K Cstar κstar γstar ε hCstar
    Q hQ M hM β hβpos χ i₀ u hu
  have hinv : (β * a)⁻¹ = β⁻¹ * Cstar * (n : ℝ) ^ (κstar * ε) := by
    dsimp only [a]
    rw [mul_inv_rev, mul_inv_rev, inv_inv, ← Real.rpow_neg (by positivity : (0 : ℝ) ≤ n)]
    rw [neg_mul, neg_neg]
    ring
  have hbound : (β * a)⁻¹ ≤ βlo⁻¹ * Cstar * (n : ℝ) ^ (κstar * ε) := by
    rw [hinv]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (inv_anti₀ hβlo hβ) (by linarith only [hCstar]))
      (by positivity)
  have hsqrt : (Real.sqrt (β * a))⁻¹ ≤ 1 + (β * a)⁻¹ := by
    rw [← Real.sqrt_inv]
    have hx : 0 ≤ (β * a)⁻¹ := by positivity
    nlinarith only [Real.sq_sqrt hx, Real.sqrt_nonneg ((β * a)⁻¹)]
  have hpow : 1 ≤ (n : ℝ) ^ (κstar * ε) :=
    Real.one_le_rpow (by exact_mod_cast n.pos) (mul_nonneg hκstar hε)
  have hgrad : (Real.sqrt (β * a))⁻¹ ≤
      (1 + βlo⁻¹ * Cstar) * (n : ℝ) ^ (κstar * ε) := by
    have hh := hsqrt.trans (add_le_add le_rfl hbound)
    nlinarith only [hh, hpow]
  have hh := add_le_add (hv.trans (mul_le_mul_of_nonneg_right hbound (norm_nonneg χ)))
    (hg.trans (mul_le_mul_of_nonneg_right hgrad (norm_nonneg χ)))
  convert hh using 1
  ring

/-- The zero-source case in the proof of Lemma 5.13: the
constrained solution vanishes literally in the scalar form carrier. -/
theorem zero_source (s : Riesz1.RieszExponent) (n m : ℕ+)
    (hm : 2 ≤ (m : ℕ)) (K : ℕ) (Cstar κstar γstar ε : ℝ) (hCstar : 1 ≤ Cstar)
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M)
    (β : ℝ) (hβ : 0 < β) (u : Fin (m : ℕ) → Q.1)
    (hu : WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _)
      (fun _ => 0) u) : u = 0 := by
  let i₀ : Fin (m : ℕ) := ⟨0, m.pos⟩
  have h := (unweighted_energy s n m hm K Cstar κstar γstar ε hCstar
    Q hQ M hM β hβ 0 i₀ u (by simpa only [ite_self] using hu)).1
  simp only [norm_zero, mul_zero] at h
  have hs : (∑ i, ‖(u i).val‖ ^ 2) = 0 := by
    have hn : 0 ≤ ∑ i, ‖(u i).val‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    nlinarith only [h, Real.sqrt_nonneg (∑ i, ‖(u i).val‖ ^ 2), Real.sq_sqrt hn]
  funext i
  apply Subtype.ext
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp
    ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖(u j).val‖)).mp
      hs i (Finset.mem_univ i)))

/-- A logarithmic weighted Cauchy–Schwarz estimate for L² component norms,
used in the multiplier part of the proof of Lemma 5.13. -/
theorem sum_norm_le_half_weight (m : ℕ+) (hm : 2 ≤ (m : ℕ))
    (i₀ : Fin (m : ℕ)) (v : Fin (m : ℕ) → Lp ℝ 2 ν) :
    (∑ i, ‖v i‖) ≤
      Real.sqrt (2 * (1 + 1 / Real.log 2)) * Real.sqrt (Real.log (2 * (m : ℝ))) *
        Real.sqrt (∑ i, (weightRadius m i i₀ ^ (1 / 2 : ℝ) * ‖v i‖) ^ 2) := by
  have hr (i) : 0 < weightRadius m i i₀ :=
    lt_of_lt_of_le zero_lt_one (one_le_weightRadius m i i₀)
  have hid (i) :
      weightRadius m i i₀ ^ (-(1 / 2 : ℝ)) *
        (weightRadius m i i₀ ^ (1 / 2 : ℝ) * ‖v i‖) = ‖v i‖ := by
    rw [← mul_assoc, ← Real.rpow_add (hr i)]
    norm_num [Real.rpow_neg_one]
  have hpow (i) : (weightRadius m i i₀ ^ (-(1 / 2 : ℝ))) ^ 2 =
      (weightRadius m i i₀)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hr i).le]
    norm_num [Real.rpow_neg_one]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun i => weightRadius m i i₀ ^ (-(1 / 2 : ℝ)))
    (fun i => weightRadius m i i₀ ^ (1 / 2 : ℝ) * ‖v i‖)
  simp only [hid, hpow] at hcs
  have hs := GlobalCancellation.sum_inverse_radius m hm i₀
  have hroot := Real.sqrt_le_sqrt hs
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * (1 + 1 / Real.log 2))] at hroot
  exact hcs.trans (mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _))

/-- See the proof of Lemma 5.13 in the paper, summed equation. The deterministic
reference has constant row mass, and the zero-sum constraint cancels it
pointwise. The multiplier is an L² function of the configuration. -/
theorem multiplier_reference_identity (s : Riesz1.RieszExponent)
    (m : ℕ+) (hm : 2 ≤ (m : ℕ)) (Q : ScalarFormData ν)
    (M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ) (β : ℝ)
    (χ : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1)
    (hz : ∀ᵐ x ∂ν, ∑ i, (u i).val x = 0) (lam : Lp ℝ 2 ν)
    (hlam : ∀ᵐ x ∂ν, lam x = gapMultiplierField m Q (fun x => β • M x)
      (fun i => if i = i₀ then χ else 0) u x) :
    ∀ᵐ x ∂ν, (m : ℝ) * lam x =
      β * (∑ i, ∑ j, (M x - (2 : ℝ) • rieszMatrix s m hm) i j * (u j).val x) - χ x := by
  have hsym : ∀ i j, rieszMatrix s m hm i j = rieszMatrix s m hm j i := by
    have hs := (rieszMatrix_posDef s m hm).isHermitian
    intro i j
    exact congrArg (fun A => A j i) hs
  have hcol (j) : (∑ i, ((2 : ℝ) • rieszMatrix s m hm) i j) =
      2 * ∑ k, sampledRieszKernel s m hm k := by
    simp only [Matrix.smul_apply, smul_eq_mul, hsym _ j, ← Finset.mul_sum,
      rieszMatrix_row_sum]
  have hzero : ∀ᵐ x ∂ν, ∀ i : Fin (m : ℕ), (0 : Lp ℝ 2 ν) x = 0 :=
    ae_all_iff.mpr (fun _ => Lp.coeFn_zero ℝ 2 ν)
  filter_upwards [hz, hlam, hzero] with x hx hl h0
  have hf : (∑ i : Fin (m : ℕ), (if i = i₀ then χ else 0 : Lp ℝ 2 ν) x) = χ x := by
    rw [Finset.sum_eq_single i₀]
    · rw [ite_eq_left rfl]
    · intro i _ hi
      rw [ite_eq_right hi]
      exact h0 i
    · simp
  have hh : (∑ i, ∑ j, ((2 : ℝ) • rieszMatrix s m hm) i j * (u j).val x) = 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hcol, ← Finset.mul_sum, hx, mul_zero]
  rw [hl]
  simp only [Matrix.smul_apply, smul_eq_mul] at hh
  simp only [gapMultiplierField, Matrix.smul_apply, smul_eq_mul, hf,
    Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]
  rw [hh, sub_zero]
  simp_rw [show ∀ i j, β * M x i j * (u j).val x =
    β * (M x i j * (u j).val x) by intros; ring, ← Finset.mul_sum]
  have hn : (m : ℝ) ≠ 0 := by positivity
  field_simp

/-- Internal norm estimate for the reference-error column sum. Its inputs are coefficient bounds. -/
theorem multiplier_bound_of_column_sum (s : Riesz1.RieszExponent)
    (m : ℕ+) (hm : 2 ≤ (m : ℕ)) (Q : ScalarFormData ν)
    (M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ᵐ x ∂ν, ∀ j, ∑ i, |(M x - (2 : ℝ) • rieszMatrix s m hm) i j| ≤ B)
    (β : ℝ) (χ : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1)
    (hz : ∀ᵐ x ∂ν, ∑ i, (u i).val x = 0) (lam : Lp ℝ 2 ν)
    (hlam : ∀ᵐ x ∂ν, lam x = gapMultiplierField m Q (fun x => β • M x)
      (fun i => if i = i₀ then χ else 0) u x) :
    (m : ℝ) * ‖lam‖ ≤ ‖χ‖ + |β| * B *
      Real.sqrt (2 * (1 + 1 / Real.log 2)) * Real.sqrt (Real.log (2 * (m : ℝ))) *
        Real.sqrt (∑ i, (weightRadius m i i₀ ^ (1 / 2 : ℝ) * ‖(u i).val‖) ^ 2) := by
  let d := fun j x => ∑ i, (M x - (2 : ℝ) • rieszMatrix s m hm) i j
  have hd (j) : Measurable (d j) :=
    Finset.measurable_sum _ (fun i _ => (hMm i j).sub measurable_const)
  have hdb (j) : ∀ᵐ x ∂ν, |d j x| ≤ B :=
    hb.mono (fun x hx => (Finset.abs_sum_le_sum_abs _ _).trans (hx j))
  choose g hg hgn using fun j =>
    BoundedMatrixModes.exists_multiplier (d j) (hd j) B hB (hdb j) (u j).val
  have he : (m : ℝ) • lam = β • (∑ j, g j) - χ := by
    apply Lp.ext
    filter_upwards [multiplier_reference_identity s m hm Q M β χ i₀ u hz lam hlam,
      Lp.coeFn_smul (m : ℝ) lam, Lp.coeFn_sub (β • ∑ j, g j) χ,
      Lp.coeFn_smul β (∑ j, g j), Lp.coeFn_fun_finsetSum Finset.univ g,
      ae_all_iff.mpr hg] with x hx hm' hs hβ hg' hv
    rw [hm', hs]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [hβ]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hg']
    rw [hx]
    congr 2
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [hv j]
    exact (Finset.sum_mul _ _ _).symm
  have hgnorm : ‖∑ j, g j‖ ≤ B * ∑ j, ‖(u j).val‖ := by
    calc
      _ ≤ ∑ j, ‖g j‖ := norm_sum_le _ _
      _ ≤ ∑ j, B * ‖(u j).val‖ := Finset.sum_le_sum (fun j _ => hgn j)
      _ = _ := (Finset.mul_sum _ _ _).symm
  calc
    _ = ‖(m : ℝ) • lam‖ := by simp [norm_smul]
    _ = ‖β • (∑ j, g j) - χ‖ := congrArg norm he
    _ ≤ ‖β • (∑ j, g j)‖ + ‖χ‖ := norm_sub_le _ _
    _ ≤ |β| * (B * ∑ j, ‖(u j).val‖) + ‖χ‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      gcongr
    _ ≤ _ := by
      have hsum := mul_le_mul_of_nonneg_left (sum_norm_le_half_weight m hm i₀
        (fun j => (u j).val)) (mul_nonneg (abs_nonneg β) hB)
      nlinarith only [hsum]

/-- See the proof of Lemma 5.13 in the paper, multiplier clauses, with the shared
loss exponent chosen before ε, all sizes, the scalar form and the source.
The statement holds for arbitrary L² sources. -/
theorem global_energy_multiplier (s : Riesz1.RieszExponent)
    (κstar γstar : ℝ) (hκstar : 0 ≤ κstar) (hγstar : 0 ≤ γstar) (M₀ : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε →
    ∀ Cstar : ℝ, 1 ≤ Cstar → ∀ βhi : ℝ, 0 ≤ βhi →
    ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (Q : ScalarFormData ν)
      (n m : ℕ+) (hm : 2 ≤ (m : ℕ)),
    2 ≤ (n : ℕ) → (n : ℕ) ≤ (m : ℕ) →
    (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
    let K := ⌊(n : ℝ) ^ ε⌋₊ ^ M₀
    1 ≤ K → 4 * K ≤ (m : ℕ) →
    ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M →
    ∀ β : ℝ, 0 ≤ β → β ≤ βhi →
    ∀ (χ : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _)
      (fun i => if i = i₀ then χ else 0) u →
    ∃ lam : Lp ℝ 2 ν,
      (∀ᵐ x ∂ν, lam x = gapMultiplierField m Q (fun x => β • M x)
        (fun i => if i = i₀ then χ else 0) u x) ∧
      WeightedWeakSolution Q (fun x => β • M x) ⊤
        (fun i => (if i = i₀ then χ else 0) + lam) u ∧
      (∀ᵐ x ∂ν, (m : ℝ) * lam x =
        β * (∑ i, ∑ j, (M x - (2 : ℝ) • rieszMatrix s m hm) i j * (u j).val x) - χ x) ∧
      (m : ℝ) * ‖lam‖ ≤ C * (n : ℝ) ^ (κ * ε) *
        (‖χ‖ + Real.sqrt (Real.log (2 * (m : ℝ))) *
          Real.sqrt (∑ i, (weightRadius m i i₀ ^ (1 / 2 : ℝ) * ‖(u i).val‖) ^ 2)) := by
  obtain ⟨κ, hκ, herr⟩ := global_error_differences s κstar γstar hκstar hγstar M₀
  refine ⟨κ, hκ, fun ε hε Cstar hCstar βhi hβhi => ?_⟩
  obtain ⟨Ce, hCe, herr⟩ := herr ε hε Cstar hCstar
  let D := Real.sqrt (2 * (1 + 1 / Real.log 2))
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  let C := 1 + βhi * Ce * D
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Ω _ ν Q n m hm hn hnm hmn K hK hKm M hM β hβ hββhi χ i₀ u hu
  obtain ⟨a, B, _, _, _, _, he⟩ := herr n m hm hn hnm hmn hK hKm ν M hM
  have hsym : ∀ᵐ x ∂ν, ∀ i j, (β • M x) i j = (β • M x) j i := by
    filter_upwards [hM.2.1] with x hx
    intro i j
    simp only [Matrix.smul_apply, smul_eq_mul, hx.1 i j]
  obtain ⟨lam, hlam, hfull⟩ := DerivativeControl.restore_multiplier m Q (fun x => β • M x)
    (SchurRestriction.periodized_scaled_measurable β hM)
    (SchurRestriction.periodized_scaled_bounded β hM) hsym _ u hu
  refine ⟨lam, hlam, hfull,
    multiplier_reference_identity s m hm Q M β χ i₀ u hu.1.1 lam hlam, ?_⟩
  let P := (n : ℝ) ^ (κ * ε)
  have hP : 1 ≤ P := Real.one_le_rpow (by exact_mod_cast n.pos) (mul_nonneg hκ.le hε.le)
  have hcol : ∀ᵐ x ∂ν, ∀ j,
      ∑ i, |(M x - (2 : ℝ) • rieszMatrix s m hm) i j| ≤ Ce * P :=
    he.mono (fun _ hx => hx.2.2.2.2.1)
  have hb := multiplier_bound_of_column_sum s m hm Q M hM.1 (Ce * P)
    (by positivity) hcol β χ i₀ u hu.1.1 lam hlam
  rw [abs_of_nonneg hβ] at hb
  let Z := Real.sqrt (Real.log (2 * (m : ℝ))) *
    Real.sqrt (∑ i, (weightRadius m i i₀ ^ (1 / 2 : ℝ) * ‖(u i).val‖) ^ 2)
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hb' : (m : ℝ) * ‖lam‖ ≤ ‖χ‖ + βhi * Ce * D * P * Z := by
    calc
      _ ≤ ‖χ‖ + β * (Ce * P) * D * Z := by
        convert hb using 1
        dsimp [Z, D]
        ring
      _ = ‖χ‖ + β * (Ce * D * P * Z) := by ring
      _ ≤ ‖χ‖ + βhi * (Ce * D * P * Z) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hββhi (by positivity))
      _ = _ := by ring
  have hcoef : 0 ≤ βhi * Ce * D := by positivity
  calc
    _ ≤ ‖χ‖ + βhi * Ce * D * P * Z := hb'
    _ ≤ P * ‖χ‖ + βhi * Ce * D * P * Z := by
      apply add_le_add _ le_rfl
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hP (norm_nonneg χ)
    _ ≤ C * P * (‖χ‖ + Z) := by
      dsimp [C]
      nlinarith [mul_nonneg hcoef (mul_nonneg (show 0 ≤ P by positivity) (norm_nonneg χ)),
        mul_nonneg (show 0 ≤ P by positivity) hZ]

/-- See the proof of Lemma 5.13 in the paper, second weighted inequality. The
multiplier, its ambient weak equation, and finiteness of the fractional
mixed norm are conclusions. Constants are uniform on each closed positive
temperature interval, and the loss exponent precedes ε and temperature. -/
theorem global_energy_second (hzeta : External.PeriodicZeta)
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
    ∃ lam : Lp ℝ 2 ν,
      (∀ᵐ x ∂ν, lam x = gapMultiplierField m Q (fun x => β • M x)
        (fun i => if i = i₀ then χ.val else 0) u x) ∧
      WeightedWeakSolution Q (fun x => β • M x) ⊤
        (fun i => (if i = i₀ then χ.val else 0) + lam) u ∧
      Integrable (fun x => V x ^ 2) ν ∧
      ∀ η : ℝ, 0 < η → η < 1 / 4 →
        (∑ i, weightRadius m i i₀ ^ (2 * (1 - s.val / 2)) * Q.2 (u i) (u i)) ≤
          C * (n : ℝ) ^ (κ * ε) *
            (‖χ.val‖ ^ 2 + Xρ (3 / 2 - s.val) *
              (η ^ (3 - s.val) * Xρ (3 / 2 - s.val) +
                η⁻¹ * Real.sqrt (∫ x, V x ^ 2 ∂ν) + ‖χ.val‖ + Xρ (1 / 2))) := by
  obtain ⟨κm, hκm, hmult⟩ := global_energy_multiplier s κstar γstar hκstar.le hγstar M₀
  have hα : (1 / 2 : ℝ) ≤ 3 / 2 - s.val := by linarith [s.property.2]
  obtain ⟨κd, hκd, hdiff⟩ :=
    DerivativeControl.diff_with_multiplier hzeta s (3 / 2 - s.val) hα κstar γstar hκstar
  refine ⟨κd + κm + 1, by positivity, fun ε hε Cstar hCstar βlo hβlo βhi hβhi => ?_⟩
  obtain ⟨Cm, hCm, hmult⟩ := hmult ε hε Cstar hCstar βhi (hβlo.le.trans hβhi)
  obtain ⟨Cd, hCd, hdiff⟩ := hdiff Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨D, hD, hlog⟩ := EllipticRegularity.log_absorption s hε (by norm_num : (0 : ℝ) < 1 / 2)
  let C₀ := (1 + Cm) * (1 + D)
  refine ⟨Cd * C₀, by dsimp [C₀]; positivity, ?_⟩
  intro Ω _ ν _ Q hQ n m hm hn hnm hmn K hK hKm M hM β hβloβ hββhi χ i₀ u hu
    sh p V Xρ
  obtain ⟨lam, hlam, hfull, _, hmlam⟩ :=
    hmult ν Q n m hm hn hnm hmn hK hKm M hM β (hβlo.le.trans hβloβ) hββhi χ.val i₀ u hu
  obtain ⟨hVi, hdiff⟩ := hdiff ε hε ν Q hQ n m hm K M hM β hβloβ hββhi
    χ i₀ u lam hfull hu.1.1
  have ht : (3 / 2 - s.val) / 2 + 1 / 4 = 1 - s.val / 2 := by ring
  refine ⟨lam, hlam, hfull, hVi, ?_⟩
  intro η hη hη'
  have he := hdiff η hη hη'
  simp only [ht] at he
  let T := (n : ℝ) ^ (κm * ε)
  let R := (n : ℝ) ^ ε
  let L := Real.sqrt (Real.log (2 * (m : ℝ)))
  let X := Xρ (3 / 2 - s.val)
  let Z := Xρ (1 / 2)
  let P := Real.sqrt (∫ x, V x ^ 2 ∂ν)
  let F := ‖χ.val‖
  let H := C₀ * (T * R)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by positivity
  have hT : 1 ≤ T := Real.one_le_rpow hn1 (mul_nonneg hκm.le hε.le)
  have hR : 1 ≤ R := Real.one_le_rpow hn1 hε.le
  have hTR : 1 ≤ T * R := one_le_mul_of_one_le_of_one_le hT hR
  have hC₀ : 1 ≤ C₀ :=
    one_le_mul_of_one_le_of_one_le (by linarith only [hCm]) (by linarith only [hD])
  have hH : 1 ≤ H := one_le_mul_of_one_le_of_one_le hC₀ hTR
  have hCmC₀ : Cm ≤ C₀ := by
    dsimp only [C₀]
    nlinarith only [hCm, hD, mul_nonneg hCm.le hD.le]
  have hDC₀ : D ≤ C₀ := by
    dsimp only [C₀]
    nlinarith only [hCm, hD, mul_nonneg hCm.le hD.le]
  have hCmDC₀ : Cm * D ≤ C₀ := by dsimp only [C₀]; linarith only [hCm, hD]
  have hTTR : T ≤ T * R := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hR (by linarith only [hT])
  have hRTR : R ≤ T * R := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hT (by linarith only [hR])
  have hlog' : L ≤ D * R := by
    dsimp only [L, R]
    rw [Real.sqrt_eq_rpow]
    exact hlog n m (by linarith only [hmn, Real.rpow_nonneg hn0.le (1 / 2 + 1 / s.val)])
  have hLH : L ≤ H :=
    hlog'.trans (mul_le_mul hDC₀ hRTR (by positivity) (by linarith only [hC₀]))
  have hCT : Cm * T ≤ H :=
    mul_le_mul hCmC₀ hTTR (by positivity) (by linarith only [hC₀])
  have hCTL : Cm * T * L ≤ H := by
    calc
      _ ≤ Cm * T * (D * R) := mul_le_mul_of_nonneg_left hlog' (by positivity)
      _ = (Cm * D) * (T * R) := by ring
      _ ≤ H := mul_le_mul_of_nonneg_right hCmDC₀ (by positivity)
  have hX : 0 ≤ X := Real.sqrt_nonneg _
  have hZ : 0 ≤ Z := Real.sqrt_nonneg _
  have hP : 0 ≤ P := Real.sqrt_nonneg _
  have hF : 0 ≤ F := norm_nonneg _
  have hmultiplier : (m : ℝ) * ‖lam‖ ≤ H * F + H * Z := by
    have h : (m : ℝ) * ‖lam‖ ≤ Cm * T * F + (Cm * T * L) * Z := by
      convert hmlam using 1
      dsimp [T, L, Z, Xρ, F]
      ring
    exact h.trans (add_le_add (mul_le_mul_of_nonneg_right hCT hF)
      (mul_le_mul_of_nonneg_right hCTL hZ))
  have hηX : η ^ (3 - s.val) * X ≤ H * (η ^ (3 - s.val) * X) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hH
      (mul_nonneg (Real.rpow_nonneg hη.le (3 - s.val)) hX)
  have hηP : η⁻¹ * L * P ≤ H * (η⁻¹ * P) := by
    have hh := mul_le_mul_of_nonneg_left hLH (mul_nonneg (inv_nonneg.mpr hη.le) hP)
    nlinarith only [hh]
  have hinner : η ^ (3 - s.val) * X + η⁻¹ * L * P + (m : ℝ) * ‖lam‖ ≤
      H * (η ^ (3 - s.val) * X + η⁻¹ * P + F + Z) := by
    linarith only [hηX, hηP, hmultiplier]
  have hbracket : F ^ 2 + X *
      (η ^ (3 - s.val) * X + η⁻¹ * L * P + (m : ℝ) * ‖lam‖) ≤
      H * (F ^ 2 + X * (η ^ (3 - s.val) * X + η⁻¹ * P + F + Z)) := by
    have hh := mul_le_mul_of_nonneg_left hinner hX
    have hf := mul_le_mul_of_nonneg_right hH (sq_nonneg F)
    nlinarith only [hh, hf]
  calc
    _ ≤ Cd * (n : ℝ) ^ (κd * ε) * (F ^ 2 + X *
        (η ^ (3 - s.val) * X + η⁻¹ * L * P + (m : ℝ) * ‖lam‖)) := he
    _ ≤ Cd * (n : ℝ) ^ (κd * ε) *
        (H * (F ^ 2 + X * (η ^ (3 - s.val) * X + η⁻¹ * P + F + Z))) :=
      mul_le_mul_of_nonneg_left hbracket (by positivity)
    _ = _ := by
      dsimp only [H, T, R]
      rw [show (κd + κm + 1) * ε = κd * ε + (κm * ε + ε) by ring,
        Real.rpow_add hn0, Real.rpow_add hn0]
      ring

end Riesz2.GlobalDecay
