/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.MultiplierControl
public import Riesz2.DecayShort.PaperGoodEventPart2
public import Riesz2.DecayShort.PhysicalComparisonPart4
import all Riesz2.DecayShort.PhysicalComparisonPart4
import all Riesz2.DecayShort.ConditionalScoresPart3

/-!
# Compact-temperature estimates for the physical short-range equation

Uniform estimates for Proposition 4.10. Polynomial exponents precede
the temperature interval. Prefactors precede every temperature in it.
The residual profiles below are used in thermodynamic length averaging.
The proper physical estimate uses the comparison in `PhysicalDecayPart6`.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open Riesz2.InitialDecay
open scoped BigOperators ENNReal ContDiff Topology

namespace Riesz2.DecayShort.PhysicalDecay

attribute [local instance] Classical.propDecidable

/-- Internal matrix rescaling for Proposition 4.10.
A common enlargement of B handles every temperature in a positive interval. -/
theorem internal_scaled_matrix_bounds {ι : Type*} [Fintype ι]
    (s βlo βhi K B β : ℝ) (hlo : 0 < βlo) (hB : 1 ≤ B)
    (hK : 1 ≤ K) (hhiK : βhi ≤ K) (hloK : βlo⁻¹ ≤ K)
    (hβ : β ∈ Icc βlo βhi) (g : ComponentGeometry ι)
    (M : Matrix ι ι ℝ)
    (hM : (∀ i j, M i j = M j i) ∧
      (∀ z : ι → ℝ, B⁻¹ * ∑ i, z i ^ 2 ≤ ∑ i, ∑ j, z i * M i j * z j) ∧
      (∀ i j, |M i j| ≤ B * (1 + componentDistance g i j) ^ (-s))) :
    (∀ i j, (β • M) i j = (β • M) j i) ∧
      (∀ z : ι → ℝ, (K * B)⁻¹ * ∑ i, z i ^ 2 ≤
        ∑ i, ∑ j, z i * (β • M) i j * z j) ∧
      (∀ i j, |(β • M) i j| ≤ (K * B) * (1 + componentDistance g i j) ^ (-s)) := by
  have hβ0 : 0 < β := hlo.trans_le hβ.1
  have hB0 : 0 < B := by linarith
  have hK0 : 0 < K := by linarith
  have hinv : K⁻¹ ≤ β := by
    have he := (inv_le_inv₀ hK0 (inv_pos.mpr hlo)).mpr hloK
    rw [inv_inv] at he
    exact he.trans hβ.1
  refine ⟨fun i j => by simp only [Matrix.smul_apply, smul_eq_mul, hM.1 i j], ?_, ?_⟩
  · intro z
    calc
      _ ≤ β * (B⁻¹ * ∑ i, z i ^ 2) := by
        rw [mul_inv]
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hinv
          (mul_nonneg (inv_nonneg.mpr hB0.le) (Finset.sum_nonneg fun i _ => sq_nonneg (z i)))
      _ ≤ β * (∑ i, ∑ j, z i * M i j * z j) :=
        mul_le_mul_of_nonneg_left (hM.2.1 z) hβ0.le
      _ = _ := by simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]; ring_nf
  · intro i j
    simp only [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hβ0]
    calc
      _ ≤ β * (B * (1 + componentDistance g i j) ^ (-s)) :=
        mul_le_mul_of_nonneg_left (hM.2.2 i j) hβ0.le
      _ ≤ _ := by
        have hp : 0 ≤ (1 + componentDistance g i j) ^ (-s) :=
          Real.rpow_nonneg (by linarith [ComponentGeometryBounds.nonneg g i j]) _
        nlinarith [mul_le_mul_of_nonneg_right (hβ.2.trans hhiK) (mul_nonneg hB0.le hp)]

/-- Compact-temperature input for Proposition 4.10,
obtained from `InitialDecay.initial_decay_uniform` at temperature one.
The exponent is independent of the interval and of its temperatures. -/
theorem initial_decay_compact (s a : ℝ) (hs : 1 < s) (ha : 1 / 2 < a) (has : a < s - 1 / 2) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ β : ℝ, β ∈ Icc βlo βhi →
      ∀ (α ι : Type*) [MeasurableSpace α] [Fintype ι] [DecidableEq ι]
        (ν : Measure α) [IsProbabilityMeasure ν]
        (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q →
        IsConservativeScalarForm Q → ∀ (g : ComponentGeometry ι) (B : ℝ), 1 ≤ B →
        ∀ M : α → Matrix ι ι ℝ, (∀ i j, Measurable (fun x => M x i j)) →
        (∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
          (∀ z : ι → ℝ, B⁻¹ * ∑ i, z i ^ 2 ≤ ∑ i, ∑ j, z i * M x i j * z j) ∧
          (∀ i j, |M x i j| ≤ B * (1 + componentDistance g i j) ^ (-s))) →
        ∀ (i₀ : ι) (χ : Lp ℝ 2 ν),
          (∃! u : ι → Q.1, WeightedWeakSolution Q (fun x => β • M x) ⊤
            (fun i => if i = i₀ then χ else 0) u) ∧
          (∀ u : ι → Q.1, WeightedWeakSolution Q (fun x => β • M x) ⊤
              (fun i => if i = i₀ then χ else 0) u →
            ‖WithLp.toLp 2 (fun i => distortionWeight g i₀ a i • (u i).val)‖ +
              Real.sqrt (∑ i, Q.2 (distortionWeight g i₀ a i • u i)
                (distortionWeight g i₀ a i • u i)) ≤ C * B ^ r * ‖χ‖) := by
  obtain ⟨r, C, hr, hC, hdec⟩ := InitialDecay.initial_decay_uniform s a 1 hs ha has (by norm_num)
  refine ⟨r, hr, fun βlo βhi hlo hle => ?_⟩
  let K := 1 + max βhi 0 + βlo⁻¹
  have hK : 1 ≤ K := by
    have := le_max_right βhi 0
    have := inv_pos.mpr hlo
    dsimp [K]
    linarith
  have hKhi : βhi ≤ K := by
    have hi := le_max_left βhi 0
    have hp := inv_pos.mpr hlo
    dsimp [K]
    linarith
  have hKlo : βlo⁻¹ ≤ K := by dsimp [K]; have := le_max_right βhi 0; linarith
  refine ⟨C * K ^ r, one_le_mul_of_one_le_of_one_le hC (Real.one_le_rpow hK hr), ?_⟩
  intro β hβ α ι _ _ _ ν _ Q hQ hcons g B hB M hm hM i₀ χ
  have hb := hM.mono fun x hx =>
    internal_scaled_matrix_bounds s βlo βhi K B β hlo hB hK hKhi hKlo hβ g (M x) hx
  have he := hdec α ι ν Q hQ hcons g (K * B) (one_le_mul_of_one_le_of_one_le hK hB)
    (fun x => β • M x) (AbstractEnergy.scaled_measurable β M hm) hb i₀ χ
  have hf : C * (K * B) ^ r = (C * K ^ r) * B ^ r := by
    rw [Real.mul_rpow (by linarith : 0 ≤ K) (by linarith : 0 ≤ B)]
    ring
  simpa only [one_smul, hf] using he

/-- Compact-temperature input for Proposition 4.10,
obtained from `OptimalDecay.optimal_decay_uniform` at temperature one.
The exponent is independent of the interval and of its temperatures. -/
theorem optimal_decay_compact (s : ℝ) (hs : 1 < s) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ β : ℝ, β ∈ Icc βlo βhi →
      ∀ (α ι : Type*) [MeasurableSpace α] [Fintype ι] [DecidableEq ι]
        (ν : Measure α) [IsProbabilityMeasure ν]
        (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q →
        IsConservativeScalarForm Q → ∀ (g : ComponentGeometry ι) (B : ℝ), 1 ≤ B →
        ∀ M : α → Matrix ι ι ℝ, (∀ i j, Measurable (fun x => M x i j)) →
        (∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
          (∀ z : ι → ℝ, B⁻¹ * ∑ i, z i ^ 2 ≤ ∑ i, ∑ j, z i * M x i j * z j) ∧
          (∀ i j, |M x i j| ≤ B * (1 + componentDistance g i j) ^ (-s))) →
        ∀ (i₀ : ι) (χ : Lp ℝ 2 ν),
          (∃! u : ι → Q.1, WeightedWeakSolution Q (fun x => β • M x) ⊤
            (fun i => if i = i₀ then χ else 0) u) ∧
          (∀ u : ι → Q.1, WeightedWeakSolution Q (fun x => β • M x) ⊤
              (fun i => if i = i₀ then χ else 0) u → ∀ j : ι,
            ‖(u j).val‖ ≤ C * B ^ r * (1 + componentDistance g j i₀) ^ (-s) * ‖χ‖) := by
  obtain ⟨r, C, hr, hC, hdec⟩ := OptimalDecay.optimal_decay_uniform s 1 hs (by norm_num)
  refine ⟨r, hr, fun βlo βhi hlo hle => ?_⟩
  let K := 1 + max βhi 0 + βlo⁻¹
  have hK : 1 ≤ K := by
    have := le_max_right βhi 0
    have := inv_pos.mpr hlo
    dsimp [K]
    linarith
  have hKhi : βhi ≤ K := by
    have hi := le_max_left βhi 0
    have hp := inv_pos.mpr hlo
    dsimp [K]
    linarith
  have hKlo : βlo⁻¹ ≤ K := by dsimp [K]; have := le_max_right βhi 0; linarith
  refine ⟨C * K ^ r, one_le_mul_of_one_le_of_one_le hC (Real.one_le_rpow hK hr), ?_⟩
  intro β hβ α ι _ _ _ ν _ Q hQ hcons g B hB M hm hM i₀ χ
  have hb := hM.mono fun x hx =>
    internal_scaled_matrix_bounds s βlo βhi K B β hlo hB hK hKhi hKlo hβ g (M x) hx
  have he := hdec α ι ν Q hQ hcons g (K * B) (one_le_mul_of_one_le_of_one_le hK hB)
    (fun x => β • M x) (AbstractEnergy.scaled_measurable β M hm) hb i₀ χ
  have hf : C * (K * B) ^ r = (C * K ^ r) * B ^ r := by
    rw [Real.mul_rpow (by linarith : 0 ≤ K) (by linarith : 0 ≤ B)]
    ring
  simpa only [one_smul, hf] using he

/-- Compact-temperature input for Proposition 4.10,
obtained from `MultiplierControl.control_lambda_uniform` at temperature one.
The exponent is independent of the interval and of its temperatures. -/
theorem control_lambda_compact (s : ℝ) (hs : 1 < s) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ β : ℝ, β ∈ Icc βlo βhi →
      ∀ (α : Type*) [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
        (m : ℕ+) (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q →
        IsConservativeScalarForm Q → ∀ (g : ComponentGeometry (Fin (m : ℕ)))
        (B : ℝ), 1 ≤ B →
        ∀ M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
        (∀ i j, Measurable (fun x => M x i j)) →
        (∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
          (∀ z : Fin (m : ℕ) → ℝ,
            B⁻¹ * ∑ i, z i ^ 2 ≤ ∑ i, ∑ j, z i * M x i j * z j) ∧
          (∀ i j, |M x i j| ≤ B * (1 + componentDistance g i j) ^ (-s))) →
        ∀ (i₀ : Fin (m : ℕ)) (χ : Lp ℝ 2 ν),
          (∃! u : Fin (m : ℕ) → Q.1, WeightedWeakSolution Q (fun x => β • M x)
            (zeroSumComponents _) (fun i => if i = i₀ then χ else 0) u) ∧
          ∀ u : Fin (m : ℕ) → Q.1, WeightedWeakSolution Q (fun x => β • M x)
            (zeroSumComponents _) (fun i => if i = i₀ then χ else 0) u →
          ∃ l : Lp ℝ 2 ν,
            (∀ᵐ x ∂ν, l x = gapMultiplierField m Q (fun x => β • M x)
              (fun i => if i = i₀ then χ else 0) u x) ∧
            ‖l‖ ≤ C * B ^ r * (m : ℝ)⁻¹ * ‖χ‖ ∧
            ∀ j, ‖(u j).val‖ ≤ C * B ^ r *
              ((1 + componentDistance g j i₀) ^ (-s) + (m : ℝ)⁻¹) * ‖χ‖ := by
  obtain ⟨r, C, hr, hC, hdec⟩ := MultiplierControl.control_lambda_uniform s 1 hs (by norm_num)
  refine ⟨r, hr, fun βlo βhi hlo hle => ?_⟩
  let K := 1 + max βhi 0 + βlo⁻¹
  have hK : 1 ≤ K := by
    have := le_max_right βhi 0
    have := inv_pos.mpr hlo
    dsimp [K]
    linarith
  have hKhi : βhi ≤ K := by
    have hi := le_max_left βhi 0
    have hp := inv_pos.mpr hlo
    dsimp [K]
    linarith
  have hKlo : βlo⁻¹ ≤ K := by dsimp [K]; have := le_max_right βhi 0; linarith
  refine ⟨C * K ^ r, one_le_mul_of_one_le_of_one_le hC (Real.one_le_rpow hK hr), ?_⟩
  intro β hβ α _ ν _ m Q hQ hcons g B hB M hm hM i₀ χ
  have hb := hM.mono fun x hx =>
    internal_scaled_matrix_bounds s βlo βhi K B β hlo hB hK hKhi hKlo hβ g (M x) hx
  have he := hdec α ν m Q hQ hcons g (K * B) (one_le_mul_of_one_le_of_one_le hK hB)
    (fun x => β • M x) (AbstractEnergy.scaled_measurable β M hm) hb i₀ χ
  have hf : C * (K * B) ^ r = (C * K ^ r) * B ^ r := by
    rw [Real.mul_rpow (by linarith : 0 ≤ K) (by linarith : 0 ≤ B)]
    ring
  simpa only [one_smul, hf] using he

open PhysicalComparison

open ConditionalScores

set_option backward.isDefEq.respectTransparency false in
/-- Uniform residual entries for Proposition 4.10
(and Subsection 4.5), retaining all covariance and boundary terms. -/
theorem internal_difference_entries_uniform (s βlo : ℝ) (hs : 1 < s) (hlo : 0 < βlo) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Parameters), p.val.2 = s → βlo ≤ p.val.1 → ∀ (n : ℕ+) (m : ℕ),
      4 ≤ (n : ℕ) + m + 1 → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (θ : PhysicalCutoff) (h : ℝ) (b : Bool) (D : ℝ), 0 ≤ D →
      ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (i j : Fin (n : ℕ)),
      let hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ) := by
        change (n : ℕ) ≤ (n : ℕ) + m + 1; omega
      let B := IntervalBoundary.boundaryMatrix ((n : ℕ) + m).succPNat n hn
        (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
      let N : ℝ := ((n : ℕ) + m + 1 : ℕ)
      let w := ConditionalScores.weight p.val.2
      |(frozenPhysicalMatrix p n m θ h b D x - frozenInternalMatrix p n m θ h b D x) i j -
        (if x ∈ ExceptionalEvent.properGoodEvent p n m hn h D then B i j else 0)| ≤
        3 * D / N + p.val.1 * C * D *
          (w i * w j + N ^ (-(1 / 2 : ℝ)) * (w i + w j) + N⁻¹) ∧
      |(frozenPhysicalMatrix p n m θ h b D x - frozenInternalMatrix p n m θ h b D x) i j| ≤
        (if x ∈ ExceptionalEvent.properGoodEvent p n m hn h D then B i j else 0) +
        3 * D / N + p.val.1 * C * D *
          (w i * w j + N ^ (-(1 / 2 : ℝ)) * (w i + w j) + N⁻¹) := by
  classical
  obtain ⟨C,hC1,hinc⟩ := legacyGoodEvent_subset_paperGoodEvent s βlo hs hlo
  have hC : 0 < C := by linarith
  refine ⟨C,hC,?_⟩
  intro p hp hpl n m hN hhalf θ h b D hD x i j hn B N w
  have hs : 1 < p.val.2 := by rw [hp]; exact hs
  have hN0 : 0 < N := by dsimp only [N]; positivity
  have hrest : 0 ≤ 3 * D / N + p.val.1 * C * D *
      (w i * w j + N ^ (-(1 / 2 : ℝ)) * (w i + w j) + N⁻¹) := by
    have hi := (ConditionalScores.weight_pos p.val.2 i).le
    have hj := (ConditionalScores.weight_pos p.val.2 j).le
    have hβ := p.property.1.le
    positivity
  by_cases hx : x ∈ ExceptionalEvent.properGoodEvent p n m hn h D
  swap
  · rw [(frozenMatrices_off_event p n m θ h b D x hx).1,
      (frozenMatrices_off_event p n m θ h b D x hx).2, sub_self, Matrix.zero_apply,
      abs_zero, ite_eq_right hx, zero_add]
    simpa only [sub_zero, abs_zero] using And.intro hrest hrest
  obtain ⟨U,_,hv,_⟩ := MarginalHessian.physical_energy_tensors p ((n : ℕ)+m).succPNat
  change (EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ) at U
  let μ := ProperMarginalChart.conditionalMeasure p n m n.pos (Equiv.refl _) x
  let e : Fin (n : ℕ) → EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) :=
    fun k => EuclideanSpace.single (Fin.castLE hn k) (1 : ℝ)
  let q : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) :=
    WithLp.toLp 2 (ConditionalForces.compensationVector n m)
  let F := fun k z => p.val.1⁻¹ * fderiv ℝ U
    (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) (e k)
  let G := fun z => p.val.1⁻¹ * fderiv ℝ U
    (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) q
  let H := IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat ((n : ℕ) + m + 1) le_rfl
    (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
  let S := Finset.univ.filter (fun a : Fin ((n : ℕ) + m + 1) => (n : ℕ) ≤ a.val)
  let bi := fun k : Fin (n : ℕ) => (m + 1 : ℝ)⁻¹ * ∑ a ∈ S, H (Fin.castLE hn k) a
  let c := (m + 1 : ℝ)⁻¹ ^ 2 * ∑ a ∈ S, ∑ b ∈ S, H a b
  have hpaper := hinc p hp hpl n m hN hhalf U hv h D hD hx
  have hcov : |ProbabilityTheory.covariance (F i - G) (F j - G) μ| ≤
      C * D * (w i * w j + N ^ (-(1 / 2 : ℝ)) * (w i + w j) + N⁻¹) := by
    have hc := paper_compensated_score_covariance p n m (by omega) hhalf U hv h (C*D)
      (mul_nonneg hC.le hD) x hpaper i j
    have he (k : Fin (n : ℕ)) : paperCompensatedScore p n m U x k = F k-G := by
      funext z
      simp only [paperCompensatedScore,F,G,e,q,map_sub,mul_sub,Pi.sub_apply]
    rw [he i,he j] at hc
    have ha : (N ^ (-(1/2 : ℝ)))^2 = N⁻¹ := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hN0.le]
      norm_num only [Nat.cast_ofNat,show -(1/2 : ℝ)*2 = -1 by ring,Real.rpow_neg_one]
    apply hc.trans_eq
    change (C*D)*(w i+N^(-(1/2 : ℝ)))*(w j+N^(-(1/2 : ℝ))) = _
    rw [← ha]
    ring
  have hHnn (a k) : 0 ≤ H a k := IntervalBoundary.intervalMatrix_nonneg
    ((n : ℕ) + m).succPNat ((n : ℕ) + m + 1) le_rfl _
    (conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x) a k
  have hbn (k) : 0 ≤ bi k := mul_nonneg (by positivity)
    (Finset.sum_nonneg fun a _ => hHnn _ a)
  have hcn : 0 ≤ c := mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun a _ =>
    Finset.sum_nonneg fun k _ => hHnn a k)
  have hbc (k) : bi k + c ≤ D / N := hx.2.2.2.2.2.1 k
  have hbi (k) : bi k ≤ D / N := (le_add_of_nonneg_right hcn).trans (hbc k)
  have hc : c ≤ D / N := (le_add_of_nonneg_left (hbn i)).trans (hbc i)
  have hQ : |-bi i - bi j + c| ≤ 3 * D / N := by
    calc
      _ ≤ |-bi i - bi j| + |c| := abs_add_le _ _
      _ ≤ |-bi i| + |bi j| + |c| := add_le_add (abs_sub _ _) le_rfl
      _ = bi i + bi j + c := by rw [abs_neg, abs_of_nonneg (hbn i),
          abs_of_nonneg (hbn j), abs_of_nonneg hcn]
      _ ≤ D / N + D / N + D / N := add_le_add (add_le_add (hbi i) (hbi j)) hc
      _ = 3 * D / N := by ring
  have he := frozen_difference_decomposition p n m θ h b D U hv x i j
  change _ = (if x ∈ ExceptionalEvent.properGoodEvent p n m hn h D then
    B i j - bi i - bi j + c - p.val.1 * ProbabilityTheory.covariance
      (fun z => p.val.1⁻¹ * fderiv ℝ U
        (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) (e i - q))
      (fun z => p.val.1⁻¹ * fderiv ℝ U
        (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) (e j - q)) μ else 0) at he
  simp only [ite_eq_left hx, map_sub, mul_sub] at he
  change _ = B i j - bi i - bi j + c -
    p.val.1 * ProbabilityTheory.covariance (F i - G) (F j - G) μ at he
  rw [he, ite_eq_left hx]
  have hBnn := IntervalBoundary.boundaryMatrix_nonneg ((n : ℕ) + m).succPNat n hn _
    (conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x) i j
  have hsmall : |(-bi i - bi j + c) -
      p.val.1 * ProbabilityTheory.covariance (F i - G) (F j - G) μ| ≤
      3 * D / N + p.val.1 * C * D *
        (w i * w j + N ^ (-(1 / 2 : ℝ)) * (w i + w j) + N⁻¹) := by
    have hp : |p.val.1 * ProbabilityTheory.covariance (F i - G) (F j - G) μ| ≤
        p.val.1 * (C * D * (w i * w j + N ^ (-(1 / 2 : ℝ)) * (w i + w j) + N⁻¹)) := by
      rw [abs_mul, abs_of_pos p.property.1]
      exact mul_le_mul_of_nonneg_left hcov p.property.1.le
    exact ((abs_sub _ _).trans (add_le_add hQ hp)).trans_eq (by ring)
  constructor
  · exact (congrArg abs (by ring :
      B i j - bi i - bi j + c - p.val.1 * ProbabilityTheory.covariance (F i - G) (F j - G) μ - B i j =
      (-bi i - bi j + c) - p.val.1 * ProbabilityTheory.covariance (F i - G) (F j - G) μ)).le.trans hsmall
  · calc
      _ = |B i j + ((-bi i - bi j + c) -
          p.val.1 * ProbabilityTheory.covariance (F i - G) (F j - G) μ)| := congrArg abs (by ring)
      _ ≤ |B i j| + |(-bi i - bi j + c) -
          p.val.1 * ProbabilityTheory.covariance (F i - G) (F j - G) μ| := abs_add_le _ _
      _ ≤ B i j + (3 * D / N + p.val.1 * C * D *
          (w i * w j + N ^ (-(1 / 2 : ℝ)) * (w i + w j) + N⁻¹)) := by
        rw [abs_of_nonneg hBnn]
        exact add_le_add le_rfl hsmall
      _ = _ := by ring

set_option backward.isDefEq.respectTransparency false in
/-- Uniform residual transport for Proposition 4.10
(and Subsection 4.5), with a prefactor chosen before the temperature. -/
theorem internal_remainder_action_uniform (s βlo : ℝ) (hs : 1 < s) (hlo : 0 < βlo) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Parameters), p.val.2 = s → βlo ≤ p.val.1 → ∀ (n : ℕ+) (m : ℕ),
      4 ≤ (n : ℕ) + m + 1 → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
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
      let R := fun i j => (frozenPhysicalMatrix p n m θ h b D x -
        frozenInternalMatrix p n m θ h b D x) i j -
        (if x ∈ ExceptionalEvent.properGoodEvent p n m hn h D then B i j else 0)
      ‖(WithLp.toLp 2 (fun i => ∑ j, R i j * z j) : EuclideanSpace ℝ (Fin (n : ℕ)))‖ ≤
        (3 * D / N * Z + p.val.1 * C * D * (a * ZW + N⁻¹ * Z)) * Real.sqrt n +
          (p.val.1 * C * D * (ZW + a * Z)) * Real.sqrt W := by
  classical
  obtain ⟨C,hC,hentry⟩ := internal_difference_entries_uniform s βlo hs hlo
  refine ⟨C,hC,?_⟩
  intro p hp hpl
  have hs : 1 < p.val.2 := by rw [hp]; exact hs
  have hentry := hentry p hp hpl
  intro n m hN hhalf θ h b D hD x z hn B N a W Z ZW R
  let w := ConditionalScores.weight p.val.2 (n := (n : ℕ))
  let U := 3 * D / N * Z + p.val.1 * C * D * (a * ZW + N⁻¹ * Z)
  let V := p.val.1 * C * D * (ZW + a * Z)
  have hw (i) : 0 ≤ w i := (ConditionalScores.weight_pos p.val.2 i).le
  have hZ : 0 ≤ Z := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hZW : 0 ≤ ZW := Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (abs_nonneg _)
  have hN0 : 0 < N := by dsimp only [N]; positivity
  have ha : 0 ≤ a := Real.rpow_nonneg hN0.le _
  have hU : 0 ≤ U := by dsimp only [U]; have hβ := p.property.1.le; positivity
  have hV : 0 ≤ V := by dsimp only [V]; have hβ := p.property.1.le; positivity
  have hpoint (i : Fin (n : ℕ)) : |∑ j, R i j * z j| ≤ U + V * w i := by
    calc
      _ ≤ ∑ j, |R i j * z j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |R i j| * |z j| := by simp only [abs_mul]
      _ ≤ ∑ j, (3 * D / N + p.val.1 * C * D *
          (w i * w j + a * (w i + w j) + N⁻¹)) * |z j| := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right
          (hentry n m hN hhalf θ h b D hD x i j).1 (abs_nonneg _)
      _ = U + V * w i := by
        dsimp only [U, V, Z, ZW]
        simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
  let wv : EuclideanSpace ℝ (Fin (n : ℕ)) := WithLp.toLp 2 w
  let onev : EuclideanSpace ℝ (Fin (n : ℕ)) := WithLp.toLp 2 (fun _ => 1)
  let y : EuclideanSpace ℝ (Fin (n : ℕ)) := WithLp.toLp 2 (fun i => ∑ j, R i j * z j)
  have hnorm : ‖y‖ ≤ ‖U • onev + V • wv‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
      EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _
    apply sq_le_sq.mpr
    change |∑ j, R i j * z j| ≤ |U * 1 + V * w i|
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
    _ ≤ ‖U • onev + V • wv‖ := hnorm
    _ ≤ ‖U • onev‖ + ‖V • wv‖ := norm_add_le _ _
    _ = U * Real.sqrt n + V * ‖wv‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hU, abs_of_nonneg hV, hones]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hweights hV)

set_option backward.isDefEq.respectTransparency false in
/-- Uniform residual transport for Proposition 4.10
(and Subsection 4.5), with a prefactor chosen before the temperature. -/
theorem internal_difference_action_uniform (s βlo : ℝ) (hs : 1 < s) (hlo : 0 < βlo) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Parameters), p.val.2 = s → βlo ≤ p.val.1 → ∀ (n : ℕ+) (m : ℕ),
      4 ≤ (n : ℕ) + m + 1 → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (θ : PhysicalCutoff) (h : ℝ) (b : Bool) (D : ℝ), 0 ≤ D →
      ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (z : Fin (n : ℕ) → ℝ),
      let M := frozenPhysicalMatrix p n m θ h b D x - frozenInternalMatrix p n m θ h b D x
      let N : ℝ := ((n : ℕ) + m + 1 : ℕ)
      let a := N ^ (-(1 / 2 : ℝ))
      let S := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-p.val.2)
      let W := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(2 * p.val.2 - 1))
      let K := 2 * (8 : ℝ) ^ (p.val.2 + 1) + 1
      let Z := ∑ j, |z j|
      let ZW := ∑ j, ConditionalScores.weight p.val.2 j * |z j|
      let E := Real.sqrt (∑ j, if (ConditionalScores.boundaryDistance j : ℝ) < (n : ℝ) / 8
        then z j ^ 2 else 0)
      ‖(WithLp.toLp 2 (fun i => ∑ j, M i j * z j) : EuclideanSpace ℝ (Fin (n : ℕ)))‖ ≤
        K * D * (n : ℝ) ^ (-p.val.2) * Z * Real.sqrt n + D * S * E +
        (3 * D / N * Z + p.val.1 * C * D * (a * ZW + N⁻¹ * Z)) * Real.sqrt n +
          (p.val.1 * C * D * (ZW + a * Z)) * Real.sqrt W := by
  classical
  obtain ⟨C,hC,hrem⟩ := internal_remainder_action_uniform s βlo hs hlo
  refine ⟨C,hC,?_⟩
  intro p hp hpl
  have hs : 1 < p.val.2 := by rw [hp]; exact hs
  have hrem := hrem p hp hpl
  intro n m hN hhalf θ h b D hD x z M N a S W K Z ZW E
  let hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ) := by
    change (n : ℕ) ≤ (n : ℕ) + m + 1; omega
  let B := IntervalBoundary.boundaryMatrix ((n : ℕ) + m).succPNat n hn
    (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
  let Bf := fun i j => if x ∈ ExceptionalEvent.properGoodEvent p n m hn h D then B i j else 0
  let vb : EuclideanSpace ℝ (Fin (n : ℕ)) := WithLp.toLp 2 (fun i => ∑ j, Bf i j * z j)
  let vr : EuclideanSpace ℝ (Fin (n : ℕ)) := WithLp.toLp 2 (fun i => ∑ j, (M i j - Bf i j) * z j)
  have hb : ‖vb‖ ≤ K * D * (n : ℝ) ^ (-p.val.2) * Z * Real.sqrt n + D * S * E := by
    by_cases hx : x ∈ ExceptionalEvent.properGoodEvent p n m hn h D
    · simpa only [vb,Bf,ite_eq_left hx] using boundary_matrix_action_norm p hs n m hhalf D hD x hx.2 z
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
  have hr : ‖vr‖ ≤ (3 * D / N * Z + p.val.1 * C * D * (a * ZW + N⁻¹ * Z)) * Real.sqrt n +
      (p.val.1 * C * D * (ZW + a * Z)) * Real.sqrt W := hrem n m hN hhalf θ h b D hD x z
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

set_option backward.isDefEq.respectTransparency false in
/-- Uniform residual transport for Proposition 4.10
(and Subsection 4.5), with a prefactor chosen before the temperature. -/
theorem internal_difference_l2_uniform (s βlo : ℝ) (hs : 1 < s) (hlo : 0 < βlo) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Parameters), p.val.2 = s → βlo ≤ p.val.1 → ∀ (n : ℕ+) (m : ℕ),
      4 ≤ (n : ℕ) + m + 1 → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (θ : PhysicalCutoff) (h : ℝ), 0 < h → ∀ (b : Bool) (D : ℝ), 0 ≤ D →
      ∀ (α : Type*) [MeasurableSpace α]
      (τ : α → AffineSimplex.chartDomain n ((n + m : ℕ) + 1)), Measurable τ →
      ∀ (ν : Measure α) (u : Fin (n : ℕ) → Lp ℝ 2 ν),
      let M := fun x => frozenPhysicalMatrix p n m θ h b D (τ x) -
        frozenInternalMatrix p n m θ h b D (τ x)
      let N : ℝ := ((n : ℕ) + m + 1 : ℕ)
      let a := N ^ (-(1 / 2 : ℝ))
      let S := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-p.val.2)
      let W := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(2 * p.val.2 - 1))
      let K := 2 * (8 : ℝ) ^ (p.val.2 + 1) + 1
      let cZ := K * D * (n : ℝ) ^ (-p.val.2) * Real.sqrt n +
        (3 * D / N + p.val.1 * C * D * N⁻¹) * Real.sqrt n +
        p.val.1 * C * D * a * Real.sqrt W
      let cW := p.val.1 * C * D * (a * Real.sqrt n + Real.sqrt W)
      ∃ g : Fin (n : ℕ) → Lp ℝ 2 ν,
        (∀ᵐ x ∂ν, ∀ i, g i x = ∑ j, M x i j * u j x) ∧
        ‖WithLp.toLp 2 g‖ ≤ cZ * (∑ i, ‖u i‖) +
          cW * (∑ i, ConditionalScores.weight p.val.2 i * ‖u i‖) +
          D * S * Real.sqrt (∑ i, if
            (ConditionalScores.boundaryDistance i : ℝ) < (n : ℝ) / 8 then ‖u i‖ ^ 2 else 0) := by
  classical
  obtain ⟨C,hC,hact⟩ := internal_difference_action_uniform s βlo hs hlo
  refine ⟨C,hC,?_⟩
  intro p hp hpl
  have hs : 1 < p.val.2 := by rw [hp]; exact hs
  have hact := hact p hp hpl
  intro n m hN hhalf θ h hh b D hD α _ τ hτ ν u M N a S W K cZ cW
  have hβ := p.property.1.le
  have hN0 : 0 < N := by dsimp only [N]; positivity
  have hS : 0 ≤ S := mul_nonneg (by norm_num) (tsum_nonneg fun _ => by positivity)
  have hcZ : 0 ≤ cZ := by dsimp only [cZ,K,a]; positivity
  have hcW : 0 ≤ cW := by dsimp only [cW,a]; positivity
  obtain ⟨Z,ZW,E,hvals,hZn,hZWn,hEn⟩ := internal_l2_contractions p.val.2 u
  obtain ⟨G,hG,hGn⟩ := internal_envelope3 Z ZW E cZ cW (D*S) hcZ hcW (mul_nonneg hD hS)
  obtain ⟨hmH,hmM,_,_⟩ := frozenMatrices_measurable_symmetric p hs n m θ h hh b D
  have hm (i j) : Measurable (fun x => M x i j) := ((hmH i j).comp hτ).sub ((hmM i j).comp hτ)
  have hb : ∀ᵐ x ∂ν,
      ‖(WithLp.toLp 2 (fun i => ∑ j, M x i j * u j x) : EuclideanSpace ℝ (Fin (n : ℕ)))‖ ≤ G x := by
    filter_upwards [hvals,hG] with x hx hg
    rw [hg,hx.1,hx.2.1,hx.2.2]
    apply (hact n m hN hhalf θ h b D hD (τ x) (fun j => u j x)).trans_eq
    dsimp only [cZ,cW]
    ring
  obtain ⟨g,hg,hgn⟩ := internal_action_l2 M hm u G hb
  refine ⟨g,hg,hgn.trans (hGn.trans ?_)⟩
  rw [hEn]
  exact add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hZn hcZ) (mul_le_mul_of_nonneg_left hZWn hcW)) le_rfl

set_option backward.isDefEq.respectTransparency false in
/-- Compact-temperature physical residual profile for Proposition 4.10 (and Subsection 4.5), on every measurable fibre. -/
theorem internal_residual_profile_compact (s βlo βhi : ℝ) (hs : 1 < s)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : Parameters), p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ (n : ℕ+) (m : ℕ),
      4 ≤ (n : ℕ) + m + 1 → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (θ : PhysicalCutoff) (h : ℝ), 0 < h → ∀ (b : Bool) (D : ℝ), 0 ≤ D →
      ∀ (α : Type*) [MeasurableSpace α]
      (τ : α → AffineSimplex.chartDomain n ((n + m : ℕ) + 1)), Measurable τ →
      ∀ (ν : Measure α) (i₀ : Fin (n : ℕ)),
      (n : ℝ)/4 ≤ (i₀.val : ℝ)+1 → (i₀.val : ℝ)+1 ≤ 3*(n : ℝ)/4 →
      ∀ (V : ℝ), 0 ≤ V → ∀ u : Fin (n : ℕ) → Lp ℝ 2 ν,
      (∀ i, ‖u i‖ ≤ V * (1 + |(i.val : ℝ) - (i₀.val : ℝ)|) ^ (-p.val.2)) →
      ∃ g : Fin (n : ℕ) → Lp ℝ 2 ν,
        (∀ᵐ x ∂ν, ∀ i, g i x = ∑ j,
          (frozenPhysicalMatrix p n m θ h b D (τ x) -
            frozenInternalMatrix p n m θ h b D (τ x)) i j * u j x) ∧
        ‖WithLp.toLp 2 g‖ ≤ C * D * V *
          ((n : ℝ) ^ (-(p.val.2 - 1/2)) +
            (((n : ℕ) + m + 1 : ℕ) : ℝ) ^ (-(1/2 : ℝ))) := by
  classical
  obtain ⟨C,hC,hbound⟩ := internal_difference_l2_uniform s βlo hs hlo
  let S := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s)
  let W := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(2 * s - 1))
  let K := 2 * (8 : ℝ) ^ (s + 1) + 1
  let B := βhi*C
  let L := (8 : ℝ) ^ (s - 1/2)*S + (8 : ℝ) ^ s*Real.sqrt W
  let J := 1+K+3+B+B*Real.sqrt W
  let Cr := 1 + J*S+B*(1+Real.sqrt W)*L+S*(8 : ℝ)^s
  have hS : 0 ≤ S := mul_nonneg (by norm_num) (tsum_nonneg fun _ => by positivity)
  have hW : 0 ≤ W := mul_nonneg (by norm_num) (tsum_nonneg fun _ => by positivity)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hB : 0 ≤ B := mul_nonneg (hlo.le.trans hle) hC.le
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  have hCr : 1 ≤ Cr := by
    have h₁ := mul_nonneg hJ hS
    have h₂ : 0 ≤ B*(1+Real.sqrt W)*L := by positivity
    have h₃ : 0 ≤ S*(8 : ℝ)^s := by positivity
    dsimp only [Cr]
    linarith
  refine ⟨Cr,hCr,?_⟩
  intro p hp hpl hph
  subst s
  have hs : 1 < p.val.2 := hs
  have hbound := hbound p rfl hpl
  intro n m hN hhalf θ h hh b D hD α _ τ hτ ν i₀ hlo hhi V hV u hu
  let N : ℝ := ((n : ℕ)+m+1 : ℕ)
  let a := N ^ (-(1/2 : ℝ))
  let l := (n : ℝ)^(-(p.val.2-1/2))
  let cZ := K*D*(n : ℝ)^(-p.val.2)*Real.sqrt n +
    (3*D/N+B*D*N⁻¹)*Real.sqrt n+B*D*a*Real.sqrt W
  let cW := B*D*(a*Real.sqrt n+Real.sqrt W)
  have hnN : (n : ℝ) ≤ N := by dsimp only [N]; norm_cast; omega
  obtain ⟨hp,hNrate,hNr,hsize⟩ := comparison_size_bounds p.val.2 hs n N hnN
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hl : 0 ≤ l := by dsimp only [l]; positivity
  have hr : 0 ≤ l+a := add_nonneg hl ha
  have hcZ : 0 ≤ cZ := by dsimp only [cZ]; positivity
  have hcW : 0 ≤ cW := by dsimp only [cW]; positivity
  have hzcoeff : cZ ≤ D*J*(l+a) := by
    have hmid := mul_le_mul_of_nonneg_left hNrate (mul_nonneg (by linarith : 0 ≤ 3+B) hD)
    have heq : cZ = K*D*l+(3+B)*D*(Real.sqrt n/N)+B*D*a*Real.sqrt W := by
      dsimp only [cZ,l]
      rw [← hp]
      simp only [div_eq_mul_inv]
      ring
    rw [heq]
    calc
      _ ≤ K*D*l+(3+B)*D*a+B*D*a*Real.sqrt W := by linarith only [hmid]
      _ = D*(K*l+(3+B+B*Real.sqrt W)*a) := by ring
      _ ≤ D*(J*l+J*a) := by
        apply mul_le_mul_of_nonneg_left _ hD
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right (by dsimp only [J]; nlinarith [mul_nonneg hB (Real.sqrt_nonneg W)] : K ≤ J) hl
        · exact mul_le_mul_of_nonneg_right (by dsimp only [J]; linarith : 3+B+B*Real.sqrt W ≤ J) ha
      _ = _ := by ring
  have hwcoeff : cW ≤ B*D*(1+Real.sqrt W) := by
    apply mul_le_mul_of_nonneg_left (add_le_add hNr le_rfl) (mul_nonneg hB hD)
  have hc := internal_profile_contractions p.val.2 hs n.pos i₀ hlo hhi V hV
    (fun i => ‖u i‖) hu
  have he := internal_boundary_contraction n.pos p.val.2 (by linarith) i₀ hlo hhi V hV
    (fun i => ‖u i‖) (fun i => norm_nonneg _) hu
  change (∑ i, ‖u i‖) ≤ V*S ∧
    (∑ i, ConditionalScores.weight p.val.2 i*‖u i‖) ≤ V*(L*l) at hc
  change _ ≤ V*(8 : ℝ)^p.val.2*l at he
  obtain ⟨g,hg,hgn⟩ := hbound n m hN hhalf θ h hh b D hD α τ hτ ν u
  have hgn0 : ‖WithLp.toLp 2 g‖ ≤ cZ*(∑ i, ‖u i‖) +
    cW*(∑ i, ConditionalScores.weight p.val.2 i*‖u i‖) + D*S*Real.sqrt (∑ i, if
      (ConditionalScores.boundaryDistance i : ℝ) < (n : ℝ) / 8 then ‖u i‖ ^ 2 else 0) := by
    apply hgn.trans
    dsimp only [cZ,cW,B,K,W,N,a]
    have hsw : 0 ≤ ∑ i, ConditionalScores.weight p.val.2 i * ‖u i‖ :=
      Finset.sum_nonneg fun i _ => mul_nonneg (ConditionalScores.weight_pos p.val.2 i).le (norm_nonneg _)
    gcongr
  refine ⟨g,hg,hgn0.trans ?_⟩
  calc
    _ ≤ cZ*(V*S)+cW*(V*(L*l))+D*S*(V*(8 : ℝ)^p.val.2*l) := by
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hc.1 hcZ)
        (mul_le_mul_of_nonneg_left hc.2 hcW))
        (mul_le_mul_of_nonneg_left he (mul_nonneg hD hS))
    _ ≤ (D*J*(l+a))*(V*S)+(B*D*(1+Real.sqrt W))*(V*(L*(l+a)))+
        D*S*(V*(8 : ℝ)^p.val.2*(l+a)) := by
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_right hzcoeff (mul_nonneg hV hS)
        · exact mul_le_mul hwcoeff
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right ha) hL) hV)
            (by positivity) (by positivity)
      · exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right ha) (by positivity))
          (mul_nonneg hD hS)
    _ = (J*S+B*(1+Real.sqrt W)*L+S*(8 : ℝ)^p.val.2)*D*V*(l+a) := by ring
    _ ≤ Cr*D*V*(l+a) := by
      apply mul_le_mul_of_nonneg_right _ hr
      apply mul_le_mul_of_nonneg_right _ hV
      apply mul_le_mul_of_nonneg_right _ hD
      dsimp only [Cr]
      linarith

end Riesz2.DecayShort.PhysicalDecay
