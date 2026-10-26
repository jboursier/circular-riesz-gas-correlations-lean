/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.PaperPhysicalComparisonPart4
public import Riesz2.DecayShort.PhysicalDecayPart3
import all Riesz2.DecayShort.PhysicalComparisonPart4

/-!
# Matrix action in the paper's interior comparison

The boundary/core split, compensated covariance contraction and L² transport
in Lemma 4.9, for the event and matrix fields of
equation (4.10) and equation (4.13).
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators

namespace Riesz2.DecayShort
open PhysicalComparison

attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false in
/-- Internal entry envelope in the proof of Lemma 4.9.
The boundary part is kept separate from the compensation and covariance. -/
theorem internal_paper_difference_entry (p : Parameters) (_hs : 1 < p.val.2)
    (n : ℕ+) (m : ℕ) (hN : 2 ≤ (n : ℕ)+m+1)
    (hhalf : 2*(n : ℕ) ≤ (n : ℕ)+m+1)
    (U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ)
    (hv : ∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) //
      y ∈ gapAmbientDomain ((n : ℕ)+m).succPNat},
      U y.val = p.val.1*physicalAmbientGapEnergy p ((n : ℕ)+m).succPNat y)
    (θ : PhysicalCutoff) (h : ℝ) (b : Bool) (D : ℝ) (hD : 0 ≤ D)
    (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1)) (i j : Fin (n : ℕ)) :
    let hn : (n : ℕ) ≤ (((n : ℕ)+m).succPNat : ℕ) := by simp; omega
    let B := IntervalBoundary.boundaryMatrix ((n : ℕ)+m).succPNat n hn
      (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
    let N : ℝ := ((n : ℕ)+m+1 : ℕ)
    let a := N ^ (-(1/2 : ℝ))
    let w := ConditionalScores.weight p.val.2
    |(paperFrozenPhysicalMatrix p n m U θ h b D x -
      paperFrozenInteriorMatrix p n m U θ h b D x) i j -
      (if x ∈ paperProperGoodEvent p n m U h D then B i j else 0)| ≤
        3*D/N + p.val.1*D*(w i*w j+a*(w i+w j)+N⁻¹) := by
  classical
  intro hn B N a w
  have hβ := p.property.1
  have hN0 : 0 < N := by dsimp only [N]; positivity
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hsq : a*a = N⁻¹ := by
    dsimp only [a]
    rw [← Real.rpow_add hN0]
    norm_num [Real.rpow_neg_one]
  by_cases hx : x ∈ paperProperGoodEvent p n m U h D
  · have he := paper_frozen_difference_decomposition p n m θ h b D U hv x i j
    rw [ite_eq_left hx] at he
    have he' : (paperFrozenPhysicalMatrix p n m U θ h b D x -
        paperFrozenInteriorMatrix p n m U θ h b D x) i j =
        B i j + paperCompensationEntry p n m x i j - p.val.1 *
          ProbabilityTheory.covariance (paperCompensatedScore p n m U x i)
            (paperCompensatedScore p n m U x j)
            (ProperMarginalChart.conditionalMeasure p n m n.pos (Equiv.refl _) x) := by
      unfold paperCompensatedScore paperCompensationEntry
      rw [he]
      dsimp only [B, Nat.succPNat_coe]
      ring
    rw [he',ite_eq_left hx]
    have hc := paper_compensated_score_covariance p n m hN hhalf U hv h D hD x hx i j
    have hq := hx.2.2.1 i j
    have hc' : |p.val.1 * ProbabilityTheory.covariance
        (paperCompensatedScore p n m U x i) (paperCompensatedScore p n m U x j)
        (ProperMarginalChart.conditionalMeasure p n m n.pos (Equiv.refl _) x)| ≤
        p.val.1*D*(w i*w j+a*(w i+w j)+N⁻¹) := by
      rw [abs_mul,abs_of_pos hβ]
      apply (mul_le_mul_of_nonneg_left hc hβ.le).trans_eq
      change p.val.1*(D*(w i+a)*(w j+a)) = _
      rw [show w i*w j+a*(w i+w j)+N⁻¹ = (w i+a)*(w j+a) by rw [← hsq]; ring]
      ring
    calc
      _ = |paperCompensationEntry p n m x i j - p.val.1 *
          ProbabilityTheory.covariance (paperCompensatedScore p n m U x i)
            (paperCompensatedScore p n m U x j)
            (ProperMarginalChart.conditionalMeasure p n m n.pos (Equiv.refl _) x)| := by congr 1; ring
      _ ≤ _ := (abs_sub _ _).trans (add_le_add
        (hq.trans (by change D/N ≤ 3*D/N; have ht := mul_le_mul_of_nonneg_right (show D ≤ 3*D by linarith) (inv_nonneg.mpr hN0.le); simpa only [div_eq_mul_inv] using ht)) hc')
  · rw [(paperFrozenMatrices_off_event p n m U θ h b D x hx).1,
      (paperFrozenMatrices_off_event p n m U θ h b D x hx).2, sub_self, Matrix.zero_apply,
      ite_eq_right hx, sub_zero, abs_zero]
    have hwi := (ConditionalScores.weight_pos p.val.2 i).le
    have hwj := (ConditionalScores.weight_pos p.val.2 j).le
    positivity


/-- The boundary Schur/bulk split in the proof of Lemma 4.9. -/
theorem paper_boundary_matrix_action_norm (p : Parameters) (hs : 1 < p.val.2)
    (n : ℕ+) (m : ℕ) (U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ) (h : ℝ)
    (D : ℝ) (hD : 0 ≤ D)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (hx : x ∈ paperProperGoodEvent p n m U h D)
    (z : Fin (n : ℕ) → ℝ) :
    let hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ) := by
      change (n : ℕ) ≤ (n : ℕ) + m + 1; omega
    let B := IntervalBoundary.boundaryMatrix ((n : ℕ) + m).succPNat n hn
      (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
    let S := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-p.val.2)
    let K := 2 * (8 : ℝ) ^ p.val.2
    ‖(WithLp.toLp 2 (fun i => ∑ j, B i j * z j) : EuclideanSpace ℝ (Fin (n : ℕ)))‖ ≤
      K * D * (n : ℝ) ^ (-p.val.2) * (∑ j, |z j|) * Real.sqrt n +
        (D * S) * Real.sqrt (∑ j, if (ConditionalScores.boundaryDistance j : ℝ) < (n : ℝ) / 8
          then z j ^ 2 else 0) := by
  classical
  intro hn B S K
  let zb := fun i : Fin (n : ℕ) => if (n : ℝ) / 8 ≤ (ConditionalScores.boundaryDistance i : ℝ)
    then z i else 0
  let ze := fun i : Fin (n : ℕ) => if (ConditionalScores.boundaryDistance i : ℝ) < (n : ℝ) / 8
    then z i else 0
  let vb : EuclideanSpace ℝ (Fin (n : ℕ)) := WithLp.toLp 2 (fun i => ∑ j, B i j * zb j)
  let ve : EuclideanSpace ℝ (Fin (n : ℕ)) := WithLp.toLp 2 (fun i => ∑ j, B i j * ze j)
  have hz (i) : z i = zb i + ze i := by
    dsimp only [zb,ze]
    by_cases hi : (n : ℝ) / 8 ≤ (ConditionalScores.boundaryDistance i : ℝ)
    · rw [ite_eq_left hi, ite_eq_right (not_lt.mpr hi), add_zero]
    · rw [ite_eq_right hi, ite_eq_left (lt_of_not_ge hi), zero_add]
  have hB (i j) : 0 ≤ B i j := IntervalBoundary.boundaryMatrix_nonneg
    ((n : ℕ) + m).succPNat n hn _
      (conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x) i j
  let L := K * D * (n : ℝ) ^ (-p.val.2)
  let Z := ∑ j, |z j|
  have hL : 0 ≤ L := by dsimp only [L,K]; positivity
  have hZ : 0 ≤ Z := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hb (i : Fin (n : ℕ)) : |vb i| ≤ L * Z := by
    calc
      _ ≤ ∑ j, |B i j * zb j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, L * |z j| := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : (n : ℝ) / 8 ≤ (ConditionalScores.boundaryDistance j : ℝ)
        · simp only [zb, ite_eq_left hj, abs_mul, abs_of_nonneg (hB i j)]
          exact mul_le_mul_of_nonneg_right (paper_boundary_bulk_entries p hs n m U h D hD x hx i j hj)
            (abs_nonneg _)
        · simp only [zb, ite_eq_right hj, mul_zero, abs_zero]
          exact mul_nonneg hL (abs_nonneg _)
      _ = L * Z := by rw [← Finset.mul_sum]
  have hbnorm : ‖vb‖ ≤ L * Z * Real.sqrt n := by
    have ht : ‖vb‖ ≤ ‖(WithLp.toLp 2 (fun _ : Fin (n : ℕ) => L * Z) :
        EuclideanSpace ℝ (Fin (n : ℕ)))‖ := by
      rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
        EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
      apply Finset.sum_le_sum
      intro i _
      apply sq_le_sq.mpr
      rw [abs_of_nonneg (mul_nonneg hL hZ)]
      exact hb i
    apply ht.trans_eq
    rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, sq_abs, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    rw [mul_comm (n : ℝ), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hL hZ)]
  obtain ⟨hr,hc⟩ := paper_boundary_schur_bounds p hs n m U h D hD x hx
  have hDS : 0 ≤ D * S := mul_nonneg hD
    (mul_nonneg (by norm_num) (tsum_nonneg fun _ => by positivity))
  have he := FiniteSchurBounds.sqrt_sum_sq_norm_le (fun i j => B i j) ze hDS hr hc
  have henorm : ‖ve‖ ≤ (D * S) * Real.sqrt (∑ j : Fin (n : ℕ),
      if (ConditionalScores.boundaryDistance j : ℝ) < (n : ℝ) / 8 then z j ^ 2 else 0) := by
    rw [EuclideanSpace.norm_eq]
    simpa only [ve,ze, smul_eq_mul, Real.norm_eq_abs, sq_abs, ite_pow, zero_pow two_ne_zero] using he
  have hsplit : (WithLp.toLp 2 (fun i => ∑ j, B i j * z j) :
      EuclideanSpace ℝ (Fin (n : ℕ))) = vb + ve := by
    apply PiLp.ext
    intro i
    change (∑ j, B i j * z j) = (∑ j, B i j * zb j) + ∑ j, B i j * ze j
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← mul_add, ← hz]
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add hbnorm henorm)

/-- Covariance and compensation contraction in Lemma 4.9. -/
theorem internal_paper_remainder_action (p : Parameters) (hs : 1 < p.val.2) :
    ∀ (n : ℕ+) (m : ℕ),
      2 ≤ (n : ℕ) + m + 1 → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ),
      (∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) //
        y ∈ gapAmbientDomain ((n : ℕ)+m).succPNat},
        U y.val = p.val.1*physicalAmbientGapEnergy p ((n : ℕ)+m).succPNat y) →
      ∀ (θ : PhysicalCutoff) (h : ℝ) (b : Bool) (D : ℝ), 0 ≤ D →
      ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (z : Fin (n : ℕ) → ℝ),
      let hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ) := by
        change (n : ℕ) ≤ (n : ℕ) + m + 1; omega
      let B := IntervalBoundary.boundaryMatrix ((n : ℕ) + m).succPNat n hn
        (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
      let N : ℝ := ((n : ℕ) + m + 1 : ℕ)
      let a := N ^ (-(1 / 2 : ℝ))
      let W := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(2 * p.val.2 - 1))
      let Z := ∑ j, |z j|
      let ZW := ∑ j, ConditionalScores.weight p.val.2 j * |z j|
      let R := fun i j => (paperFrozenPhysicalMatrix p n m U θ h b D x -
        paperFrozenInteriorMatrix p n m U θ h b D x) i j -
        (if x ∈ paperProperGoodEvent p n m U h D then B i j else 0)
      ‖(WithLp.toLp 2 (fun i => ∑ j, R i j * z j) : EuclideanSpace ℝ (Fin (n : ℕ)))‖ ≤
        (3 * D / N * Z + p.val.1 * D * (a * ZW + N⁻¹ * Z)) * Real.sqrt n +
          (p.val.1 * D * (ZW + a * Z)) * Real.sqrt W := by
  classical
  intro n m hN hhalf U hv θ h b D hD x z hn B N a W Z ZW R
  let w := ConditionalScores.weight p.val.2 (n := (n : ℕ))
  let U₀ := 3 * D / N * Z + p.val.1 * D * (a * ZW + N⁻¹ * Z)
  let V := p.val.1 * D * (ZW + a * Z)
  have hw (i) : 0 ≤ w i := (ConditionalScores.weight_pos p.val.2 i).le
  have hZ : 0 ≤ Z := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hZW : 0 ≤ ZW := Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (abs_nonneg _)
  have hN0 : 0 < N := by dsimp only [N]; positivity
  have ha : 0 ≤ a := Real.rpow_nonneg hN0.le _
  have hU : 0 ≤ U₀ := by dsimp only [U₀]; have hβ := p.property.1.le; positivity
  have hV : 0 ≤ V := by dsimp only [V]; have hβ := p.property.1.le; positivity
  have hpoint (i : Fin (n : ℕ)) : |∑ j, R i j * z j| ≤ U₀ + V * w i := by
    calc
      _ ≤ ∑ j, |R i j * z j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |R i j| * |z j| := by simp only [abs_mul]
      _ ≤ ∑ j, (3 * D / N + p.val.1 * D *
          (w i * w j + a * (w i + w j) + N⁻¹)) * |z j| := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right
          (internal_paper_difference_entry p hs n m hN hhalf U hv θ h b D hD x i j) (abs_nonneg _)
      _ = U₀ + V * w i := by
        dsimp only [U₀, V, Z, ZW]
        simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
  let wv : EuclideanSpace ℝ (Fin (n : ℕ)) := WithLp.toLp 2 w
  let onev : EuclideanSpace ℝ (Fin (n : ℕ)) := WithLp.toLp 2 (fun _ => 1)
  let y : EuclideanSpace ℝ (Fin (n : ℕ)) := WithLp.toLp 2 (fun i => ∑ j, R i j * z j)
  have hnorm : ‖y‖ ≤ ‖U₀ • onev + V • wv‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
      EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    apply sq_le_sq.mpr
    change |∑ j, R i j * z j| ≤ |U₀ * 1 + V * w i|
    rw [mul_one, abs_of_nonneg (add_nonneg hU (mul_nonneg hV (hw i)))]
    exact hpoint i
  have hones : ‖onev‖ = Real.sqrt n := by
    rw [EuclideanSpace.norm_eq]
    simp only [onev, Real.norm_eq_abs, abs_one, one_pow,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hweights : ‖wv‖ ≤ Real.sqrt W := by
    rw [EuclideanSpace.norm_eq]
    simp only [wv, Real.norm_eq_abs, sq_abs]
    exact Real.sqrt_le_sqrt (boundary_weight_square_sum p.val.2 hs n)
  calc
    _ ≤ ‖U₀ • onev + V • wv‖ := hnorm
    _ ≤ ‖U₀ • onev‖ + ‖V • wv‖ := norm_add_le _ _
    _ = U₀ * Real.sqrt n + V * ‖wv‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hU, abs_of_nonneg hV, hones]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hweights hV)

/-- Pointwise residual decomposition in Lemma 4.9. -/
theorem paper_frozen_difference_action_norm (p : Parameters) (hs : 1 < p.val.2) :
    ∀ (n : ℕ+) (m : ℕ),
      2 ≤ (n : ℕ) + m + 1 → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ),
      (∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) //
        y ∈ gapAmbientDomain ((n : ℕ)+m).succPNat},
        U y.val = p.val.1*physicalAmbientGapEnergy p ((n : ℕ)+m).succPNat y) →
      ∀ (θ : PhysicalCutoff) (h : ℝ) (b : Bool) (D : ℝ), 0 ≤ D →
      ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (z : Fin (n : ℕ) → ℝ),
      let M := paperFrozenPhysicalMatrix p n m U θ h b D x - paperFrozenInteriorMatrix p n m U θ h b D x
      let N : ℝ := ((n : ℕ) + m + 1 : ℕ)
      let a := N ^ (-(1 / 2 : ℝ))
      let S := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-p.val.2)
      let W := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(2 * p.val.2 - 1))
      let K := 2 * (8 : ℝ) ^ p.val.2
      let Z := ∑ j, |z j|
      let ZW := ∑ j, ConditionalScores.weight p.val.2 j * |z j|
      let E := Real.sqrt (∑ j, if (ConditionalScores.boundaryDistance j : ℝ) < (n : ℝ) / 8
        then z j ^ 2 else 0)
      ‖(WithLp.toLp 2 (fun i => ∑ j, M i j * z j) : EuclideanSpace ℝ (Fin (n : ℕ)))‖ ≤
        K * D * (n : ℝ) ^ (-p.val.2) * Z * Real.sqrt n + D * S * E +
        (3 * D / N * Z + p.val.1 * D * (a * ZW + N⁻¹ * Z)) * Real.sqrt n +
          (p.val.1 * D * (ZW + a * Z)) * Real.sqrt W := by
  classical
  intro n m hN hhalf U hv θ h b D hD x z M N a S W K Z ZW E
  let hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ) := by
    change (n : ℕ) ≤ (n : ℕ) + m + 1; omega
  let B := IntervalBoundary.boundaryMatrix ((n : ℕ) + m).succPNat n hn
    (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
  let Bf := fun i j => if x ∈ paperProperGoodEvent p n m U h D then B i j else 0
  let vb : EuclideanSpace ℝ (Fin (n : ℕ)) := WithLp.toLp 2 (fun i => ∑ j, Bf i j * z j)
  let vr : EuclideanSpace ℝ (Fin (n : ℕ)) := WithLp.toLp 2 (fun i => ∑ j, (M i j - Bf i j) * z j)
  have hb : ‖vb‖ ≤ K * D * (n : ℝ) ^ (-p.val.2) * Z * Real.sqrt n + D * S * E := by
    by_cases hx : x ∈ paperProperGoodEvent p n m U h D
    · simpa only [vb,Bf,ite_eq_left hx] using paper_boundary_matrix_action_norm p hs n m U h D hD x hx z
    · have hz : vb = 0 := by
        apply PiLp.ext
        intro i
        simp [vb,Bf,ite_eq_right hx]
      rw [hz,norm_zero]
      have hS : 0 ≤ S := mul_nonneg (by norm_num) (tsum_nonneg fun _ => by positivity)
      have hZ : 0 ≤ Z := Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hE : 0 ≤ E := Real.sqrt_nonneg _
      dsimp only [K]
      positivity
  have hr : ‖vr‖ ≤ (3 * D / N * Z + p.val.1 * D * (a * ZW + N⁻¹ * Z)) * Real.sqrt n +
      (p.val.1 * D * (ZW + a * Z)) * Real.sqrt W := internal_paper_remainder_action p hs n m hN hhalf U hv θ h b D hD x z
  have hsplit : (WithLp.toLp 2 (fun i => ∑ j, M i j * z j) : EuclideanSpace ℝ (Fin (n : ℕ))) =
      vb + vr := by
    apply PiLp.ext
    intro i
    change (∑ j, M i j * z j) = (∑ j, Bf i j * z j) + ∑ j, (M i j - Bf i j) * z j
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsplit]
  exact ((norm_add_le _ _).trans (add_le_add hb hr)).trans_eq (by ring)

/-- L² transport on any measurable pullback in Lemma 4.9. -/
theorem paper_frozen_difference_l2_norm (p : Parameters) (hs : 1 < p.val.2) :
    ∀ (n : ℕ+) (m : ℕ),
      2 ≤ (n : ℕ) + m + 1 → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ),
      (∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) //
        y ∈ gapAmbientDomain ((n : ℕ)+m).succPNat},
        U y.val = p.val.1*physicalAmbientGapEnergy p ((n : ℕ)+m).succPNat y) →
      ∀ (θ : PhysicalCutoff) (h : ℝ), 0 < h → ∀ (b : Bool) (D : ℝ), 0 ≤ D →
      ∀ (α : Type*) [MeasurableSpace α]
      (τ : α → AffineSimplex.chartDomain n ((n + m : ℕ) + 1)), Measurable τ →
      ∀ (ν : Measure α) (u : Fin (n : ℕ) → Lp ℝ 2 ν),
      let M := fun x => paperFrozenPhysicalMatrix p n m U θ h b D (τ x) -
        paperFrozenInteriorMatrix p n m U θ h b D (τ x)
      let N : ℝ := ((n : ℕ) + m + 1 : ℕ)
      let a := N ^ (-(1 / 2 : ℝ))
      let S := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-p.val.2)
      let W := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(2 * p.val.2 - 1))
      let K := 2 * (8 : ℝ) ^ p.val.2
      let cZ := K * D * (n : ℝ) ^ (-p.val.2) * Real.sqrt n +
        (3 * D / N + p.val.1 * D * N⁻¹) * Real.sqrt n +
        p.val.1 * D * a * Real.sqrt W
      let cW := p.val.1 * D * (a * Real.sqrt n + Real.sqrt W)
      ∃ g : Fin (n : ℕ) → Lp ℝ 2 ν,
        (∀ᵐ x ∂ν, ∀ i, g i x = ∑ j, M x i j * u j x) ∧
        ‖WithLp.toLp 2 g‖ ≤ cZ * (∑ i, ‖u i‖) +
          cW * (∑ i, ConditionalScores.weight p.val.2 i * ‖u i‖) +
          D * S * Real.sqrt (∑ i, if
            (ConditionalScores.boundaryDistance i : ℝ) < (n : ℝ) / 8 then ‖u i‖ ^ 2 else 0) := by
  classical
  intro n m hN hhalf U hv θ h hh b D hD α _ τ hτ ν u M N a S W K cZ cW
  have hβ := p.property.1.le
  have hN0 : 0 < N := by dsimp only [N]; positivity
  have hS : 0 ≤ S := mul_nonneg (by norm_num) (tsum_nonneg fun _ => by positivity)
  have hcZ : 0 ≤ cZ := by dsimp only [cZ,K,a]; positivity
  have hcW : 0 ≤ cW := by dsimp only [cW,a]; positivity
  obtain ⟨Z,ZW,E,hvals,hZn,hZWn,hEn⟩ := internal_l2_contractions p.val.2 u
  obtain ⟨G,hG,hGn⟩ := internal_envelope3 Z ZW E cZ cW (D*S) hcZ hcW (mul_nonneg hD hS)
  obtain ⟨hmH,hmM,_,_⟩ := paperFrozenMatrices_measurable_symmetric p hs n m U θ h hh b D
  have hm (i j) : Measurable (fun x => M x i j) := ((hmH i j).comp hτ).sub ((hmM i j).comp hτ)
  have hb : ∀ᵐ x ∂ν,
      ‖(WithLp.toLp 2 (fun i => ∑ j, M x i j * u j x) : EuclideanSpace ℝ (Fin (n : ℕ)))‖ ≤ G x := by
    filter_upwards [hvals,hG] with x hx hg
    rw [hg,hx.1,hx.2.1,hx.2.2]
    apply (paper_frozen_difference_action_norm p hs n m hN hhalf U hv θ h b D hD (τ x) (fun j => u j x)).trans_eq
    dsimp only [cZ,cW]
    ring
  obtain ⟨g,hg,hgn⟩ := internal_action_l2 M hm u G hb
  refine ⟨g,hg,hgn.trans (hGn.trans ?_)⟩
  rw [hEn]
  exact add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hZn hcZ) (mul_le_mul_of_nonneg_left hZWn hcW)) le_rfl

end Riesz2.DecayShort
