/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.ReductionScales
public import Riesz1.Rigidity.ReductionAverageTail
public import Riesz1.Externals.BakryEmeryProof
public import Riesz1.Externals.PrekopaLeindlerProof

/-!
# Block-average reduction above a common temperature floor

The companion block-average reduction holds uniformly over inverse temperatures
above a positive floor. The scale geometry and constrained-mean bound come from
`Riesz1.reduction_av_scales`. The explicit coefficient of
`scale_centered_moment` is bounded using the temperature floor.
-/

public section

noncomputable section

open MeasureTheory Finset

namespace Riesz2.ExternalRigidity

private theorem scale_coefficient_le (s : Riesz1.RieszExponent) {βlo : ℝ}
    (hβlo : 0 < βlo) (P : Riesz1.Parameters) (hs : P.val.2 = s.val)
    (hβ : βlo ≤ P.val.1) :
    2 ^ (P.val.2 + 3) /
        (P.val.1 * Riesz1.rigidityCurvatureConstant (Riesz1.parametersExponent P).val) ≤
      2 ^ (s.val + 3) / (βlo * Riesz1.rigidityCurvatureConstant s.val) := by
  change 2 ^ (P.val.2 + 3) / (P.val.1 * Riesz1.rigidityCurvatureConstant P.val.2) ≤ _
  rw [hs]
  have ha := Riesz1.rigidityCurvatureConstant_pos s
  exact div_le_div_of_nonneg_left (by positivity) (mul_pos hβlo ha)
    (mul_le_mul_of_nonneg_right hβ ha.le)

private theorem finite_sum_tail {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Finset ι) (hS : S.Nonempty)
    (F : ι → Ω → ℝ) (w : ℝ) :
    μ.real {x | (S.card : ℝ) * w ≤ |∑ j ∈ S, F j x|} ≤
      ∑ j ∈ S, μ.real {x | w ≤ |F j x|} := by
  classical
  apply le_trans (measureReal_mono (μ := μ) (s₂ := ⋃ j ∈ S, {x | w ≤ |F j x|})
    ?_ (measure_ne_top _ _))
    (measureReal_biUnion_finset_le S _)
  intro x hx
  have hsum : ∑ _j ∈ S, w ≤ ∑ j ∈ S, |F j x| := calc
      ∑ _j ∈ S, w = (S.card : ℝ) * w := by simp
      _ ≤ |∑ j ∈ S, F j x| := hx
      _ ≤ ∑ j ∈ S, |F j x| := Finset.abs_sum_le_sum_abs _ _
  obtain ⟨j, hj, hvalue⟩ := Finset.exists_le_of_sum_le hS hsum
  exact Set.mem_iUnion₂.mpr ⟨j, hj, hvalue⟩

/-- Uniform version of the companion block-average reduction, used in the companion rigidity theorem. For every positive reduction exponent, the positive
rate and prefactor precede every Gibbs parameter with exponent `s` and inverse
temperature at least `βlo`, and all sizes, labels and block radii. -/
theorem reduction_av_uniform (s : Riesz1.RieszExponent) {e βlo : ℝ}
    (he : 0 < e) (hβlo : 0 < βlo) :
    ∃ cR CR : ℝ, 0 < cR ∧ 0 < CR ∧
      ∀ P : Riesz1.Parameters, P.val.2 = s.val → βlo ≤ P.val.1 →
      ∀ (N : ℕ+) (_hN : 2 ≤ (N : ℕ)) (i : ℤ) {k : ℕ}, 1 ≤ k →
        2 * k ≤ (N : ℕ) →
        (Riesz1.gibbsMeasure P N).real {X |
          (k : ℝ) ^ (s.val / 2 + e) ≤
            |(N : ℝ) * (Riesz1.cyclicLift X i - Riesz1.blockAverage X i k)|} ≤
          CR * Real.exp (-cR * (k : ℝ) ^ (e / (s.val + 2))) := by
  classical
  let q : ℕ := max 2 ⌈2 / e⌉₊
  have hq : 2 ≤ q := le_max_left _ _
  have hqpos : 0 < q := by omega
  have hqr : (0 : ℝ) < q := Nat.cast_pos.mpr hqpos
  have hqe : 2 / e ≤ (q : ℝ) :=
    (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))
  let Cs : ℝ := 2 ^ (s.val + 3) / (βlo * Riesz1.rigidityCurvatureConstant s.val)
  have hCs : 0 < Cs := div_pos (Real.rpow_pos_of_pos two_pos _)
    (mul_pos hβlo (Riesz1.rigidityCurvatureConstant_pos s))
  let cR : ℝ := min (1 / (16 * (q : ℝ) ^ 2 * Cs)) (Real.log 2 / 4)
  have hcR : 0 < cR := lt_min (by positivity)
    (div_pos (Real.log_pos one_lt_two) (by norm_num))
  refine ⟨cR, 5 * (q : ℝ) + Real.exp (cR * q), hcR, by positivity, ?_⟩
  intro P hs hβ N hN i k hk hkN
  have := Riesz1.isProbabilityMeasure_gibbsMeasure P N
  have hkreal : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr hk
  have hkpos : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hkreal
  let T : ℝ := (k : ℝ) ^ (s.val / 2 + e)
  let A : ℝ := (k : ℝ) ^ (e / (s.val + 2))
  have hA : 0 ≤ A := Real.rpow_nonneg hkpos.le _
  have hAT : A ≤ T := Real.rpow_le_rpow_of_exponent_le hkreal (by
    have := div_le_self he.le (show 1 ≤ s.val + 2 by linarith [s.property.1])
    linarith [s.property.1])
  have hexp {r : ℝ} (hr : cR ≤ r) : Real.exp (-r * A) ≤ Real.exp (-cR * A) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right hr hA)
  by_cases hsmall : T < q
  · have hcover : 1 ≤ Real.exp (cR * q) * Real.exp (-cR * A) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      have := mul_le_mul_of_nonneg_left (hAT.trans hsmall.le) hcR.le
      linarith
    exact measureReal_le_one.trans (hcover.trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity))
        (Real.exp_pos _).le))
  · have hw : 1 ≤ T / q := (one_le_div hqr).mpr (le_of_not_gt hsmall)
    -- Only the witness-independent facts of the scale theorem are used.
    obtain ⟨_, _, hscale⟩ := Riesz1.reduction_av_scales
      Riesz1.Externals.bakry_emery_proof Riesz1.Externals.prekopa_leindler_proof
      P he hq hqe Riesz1.isForcingCutoff_forcingCutoff
    have hinc : ∀ m ∈ range q,
        (Riesz1.gibbsMeasure P N).real {X |
          T / q ≤ |Riesz1.scaleIncrement i k q m X|} ≤ 5 * Real.exp (-cR * A) := by
      intro m hm
      have hm' : m < q := mem_range.mp hm
      let ν := Riesz1.scaleLaw P N Riesz1.forcingCutoff e i k q m
      have := Riesz1.isProbabilityMeasure_scaleLaw P N
        Riesz1.isForcingCutoff_forcingCutoff e i hk q m
      have hmean := (hscale N hN i hk hkN hm').2.2.1
      have htv := (hscale N hN i hk hkN hm').2.2.2.1
      rw [hs] at htv
      have hpow : (k : ℝ) ^ (P.val.2 * ((m : ℝ) + 1) / q + 1 / q + e) ≤
          (k : ℝ) ^ (s.val + 1 / q + e) := by
        apply Real.rpow_le_rpow_of_exponent_le hkreal
        rw [hs, mul_div_assoc]
        have hmreal : ((m : ℝ) + 1) / q ≤ 1 := (div_le_one hqr).mpr (by
          exact_mod_cast (show m + 1 ≤ q by omega))
        linarith [mul_le_of_le_one_right s.property.1.le hmreal]
      have hmom (t : ℝ) := Riesz1.scale_centered_moment
        Riesz1.Externals.bakry_emery_proof Riesz1.Externals.prekopa_leindler_proof
        P N hN Riesz1.isForcingCutoff_forcingCutoff he.le i hk hkN hm' t
      have hlog (t : ℝ) :
          Real.log (∫ X, Real.exp (t * (Riesz1.scaleIncrement i k q m X -
            ∫ Y, Riesz1.scaleIncrement i k q m Y ∂ν)) ∂ν) ≤
            (Cs * (k : ℝ) ^ (s.val + 1 / q + e)) * t ^ 2 := by
        refine (hmom t).2.trans ?_
        calc
          _ ≤ (Cs * t ^ 2) * (k : ℝ) ^ (s.val + 1 / q + e) :=
            mul_le_mul (mul_le_mul_of_nonneg_right
              (scale_coefficient_le s hβlo P hs hβ) (sq_nonneg t)) hpow
              (Real.rpow_nonneg hkpos.le _) (mul_nonneg hCs.le (sq_nonneg t))
          _ = _ := by ring
      have htail := Riesz1.measureReal_le_totalVariation_add_of_centered
        (Riesz1.gibbsMeasure P N) ν (Riesz1.measurable_scaleIncrement i k q m)
        (mul_pos hCs (Real.rpow_pos_of_pos hkpos _)) hw hmean
        (fun t => (hmom t).1) hlog
      have halgebra := Riesz1.reduction_av_exponent_le s.property.1 he
        (show (2 : ℝ) ≤ q by exact_mod_cast hq) hqe hCs hkreal
      have hgauss : 2 * Real.exp (-(T / q) ^ 2 /
          (16 * (Cs * (k : ℝ) ^ (s.val + 1 / q + e)))) ≤
          2 * Real.exp (-cR * A) :=
        mul_le_mul_of_nonneg_left
          ((Real.exp_le_exp.mpr halgebra).trans (hexp (min_le_left _ _))) two_pos.le
      have hvariation := htv.trans (mul_le_mul_of_nonneg_left
        (hexp (min_le_right _ _)) (show (0 : ℝ) ≤ 3 by norm_num))
      linarith
    have hsum (X : Riesz1.Configuration N) :=
      (hscale N hN i hk hkN (show 0 < q by omega)).1 X
    have htail := finite_sum_tail (Riesz1.gibbsMeasure P N) (range q)
      ⟨0, mem_range.mpr hqpos⟩ (fun m X => Riesz1.scaleIncrement i k q m X) (T / q)
    have hthreshold : ((range q).card : ℝ) * (T / q) = T := by
      rw [card_range, mul_div_cancel₀ T (ne_of_gt hqr)]
    simp only [hthreshold, hsum] at htail
    refine htail.trans ((Finset.sum_le_sum hinc).trans ?_)
    simp only [sum_const, card_range, nsmul_eq_mul]
    have : (q : ℝ) * (5 * Real.exp (-cR * A)) =
        (5 * (q : ℝ)) * Real.exp (-cR * A) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (Real.exp_pos _).le) (Real.exp_pos _).le

end Riesz2.ExternalRigidity

end
