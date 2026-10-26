/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.LengthAveragingFibres
public import Riesz2.Thermodynamic.InterpolatingDensities
public import Riesz2.Thermodynamic.InterpolantLocalLawsPart4
public import Riesz2.ToMathlib.CovarianceCauchySchwarz
public import Riesz1.ToMathlib.VarianceTwoErrors
public import Riesz1.ToMathlib.VarianceFrozenIntegral

/-!
# Active length: mean comparison and variance interfaces

Supporting results for the proof of Lemma 6.5, on the active law and the coarea length
measure. Variances use `Riesz1.variance`, retaining their extended values.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Riesz2.LengthVariance

open LengthAveragingFibres

/-- The total active length as a block observable, Lemma 6.5. The function is the coordinate sum on the whole carrier. -/
def lengthObservable (n : ℕ+) : BlockObservable n :=
  ⟨fun x => ∑ i, x i, by
    let T : (Fin (n : ℕ) → ℝ) →L[ℝ] ℝ := ∑ i, ContinuousLinearMap.proj i
    refine ⟨‖T‖₊, ?_⟩
    have he : (fun x => ∑ i, x i) = T := by
      funext x
      simp [T]
    rw [he]
    exact T.lipschitzWith⟩

/-- Every coordinate derivative of the length is exactly one. This is the
normalization check for the proof of Lemma 6.5. -/
theorem coordinateDerivativeNorm_length (n : ℕ+) (j : Fin (n : ℕ)) :
    coordinateDerivativeNorm (lengthObservable n) j = 1 := by
  classical
  apply le_antisymm
  · apply csInf_le (OrderBot.bddBelow _)
    intro x t
    simp only [lengthObservable, Finset.sum_update_of_mem (Finset.mem_univ j),
      NNReal.coe_one, one_mul]
    rw [Finset.sdiff_singleton_eq_erase]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    have he : t + ∑ x_1 ∈ Finset.univ.erase j, x x_1 -
        ((∑ x_1 ∈ Finset.univ.erase j, x x_1) + x j) = t - x j := by ring
    rw [he]
  · have h := InterpolatingDensities.coordinate_bound (lengthObservable n) j 0 1
    simp only [lengthObservable, Pi.zero_apply, Finset.sum_update_of_mem (Finset.mem_univ j),
      Finset.sum_const_zero, sub_zero, abs_one, mul_one] at h
    have hh : (1 : ℝ) ≤ (coordinateDerivativeNorm (lengthObservable n) j : ℝ) := by
      simpa only [lengthObservable, zero_add, add_zero, abs_one] using h
    exact_mod_cast hh

/-- The derivative sum of the length is the number of active gaps,
Theorem 4. -/
theorem blockDerivativeNorm_length (n : ℕ+) :
    blockDerivativeNorm (lengthObservable n) = (n : ℝ) := by
  simp [blockDerivativeNorm, coordinateDerivativeNorm_length]

/-- See the proof of Lemma 6.5 in the paper, untilted mean: the sum of
the first `n+1` gaps has expectation `n+1`. Both exponent regimes use the
cyclic-symmetry theorem. -/
theorem untilted_mean (p : Parameters) (n m : ℕ) :
    (∫ X, ∑ i : Fin (n + 1), gap X i.val ∂gibbsMeasure p ((n + 1) + m).succPNat) =
      (n + 1 : ℝ) := by
  let N := ((n + 1) + m).succPNat
  have hN : 2 ≤ (N : ℕ) := by dsimp only [N, Nat.succPNat_coe]; omega
  have hV : Measurable (@gapVector N) := Riesz1.measurable_gapVector N
  have hg (j : ℤ) : Integrable (fun X : Riesz1.Configuration N => gap X j)
      (gibbsMeasure p N) ∧ (∫ X, gap X j ∂gibbsMeasure p N) = 1 := by
    have h := RemovableGapBarrier.gap_mean_one p N hN (Riesz1.labelOf N j)
    rw [gapLaw] at h
    have hi := (integrable_map_measure (measurable_pi_apply _).aestronglyMeasurable
      hV.aemeasurable).mp h.1
    have he := h.2
    rw [integral_map hV.aemeasurable (measurable_pi_apply _).aestronglyMeasurable] at he
    refine ⟨hi.congr (Filter.Eventually.of_forall fun X =>
      (gap_eq_gapVector_labelOf X j).symm), ?_⟩
    simpa only [← gap_eq_gapVector_labelOf] using he
  rw [integral_finsetSum _ fun i _ => (hg i.val).1]
  calc
    _ = ∑ _i : Fin (n + 1), (1 : ℝ) := Finset.sum_congr rfl fun i _ => (hg i.val).2
    _ = _ := by simp

/-- Every positive real moment of the active length is finite. The bound
by the fixed ambient volume is used only for validity of these integrals,
not for any uniform variance rate. See Theorem 1. -/
theorem length_memLp (p : Parameters) (n m : ℕ) (θ : PhysicalCutoff) (ε : ℝ)
    (q : ℝ≥0∞) :
    MemLp (fun x : EuclideanSpace ℝ (Fin (n + 1)) => ∑ i, x i) q
      (activeMeasure p n m θ ε) := by
  let N := ((n + 1) + m).succPNat
  let a : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩
  have hmeas : Measurable (fun X : Riesz1.Configuration N =>
      WithLp.toLp 2 (finiteGapBlock (K := a) X)) :=
    (PiLp.continuous_toLp 2 _).measurable.comp
      (measurable_pi_iff.mpr fun i => Riesz1.measurable_gap i.val)
  have hsum : Measurable (fun x : EuclideanSpace ℝ (Fin (n + 1)) => ∑ i, x i) :=
    (continuous_finsetSum _ fun i _ => PiLp.continuous_apply 2 _ i).measurable
  have hprob := (InterpolatingDensities.tilt_valid p N a (by dsimp [N, a]; simp; omega)
    θ ε true).2.2
  change MemLp _ q ((tiltedParticleMeasure p N a _ θ ε true).map _)
  apply (memLp_map_measure_iff hsum.aestronglyMeasurable hmeas.aemeasurable).mpr
  apply MemLp.of_bound
    (hsum.comp hmeas).aestronglyMeasurable ((n + 1 : ℝ) * (N : ℝ))
  apply Filter.Eventually.of_forall
  intro X
  change ‖∑ i : Fin (n + 1), gap X i.val‖ ≤ _
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => (Riesz1.gap_pos X i.val).le)]
  calc
    _ ≤ ∑ _i : Fin (n + 1), (N : ℝ) :=
      Finset.sum_le_sum fun i _ => Riesz1.gap_le_N X i.val
    _ = _ := by simp

/-- The exact active expectation is the particle expectation of the gap
sum. This bridge uses the push-forward, Lemma 6.5. -/
theorem active_mean_eq (p : Parameters) (n m : ℕ) (θ : PhysicalCutoff) (ε : ℝ) :
    (∫ x, ∑ i, x i ∂activeMeasure p n m θ ε) =
      ∫ X, ∑ i : Fin (n + 1), gap X i.val
        ∂tiltedParticleMeasure p ((n + 1) + m).succPNat
          (⟨n + 1, Nat.succ_pos n⟩ : ℕ+) (by simp; omega) θ ε true := by
  unfold activeMeasure activeTiltedGapLaw
  have hm : Measurable (fun X : Riesz1.Configuration ((n + 1) + m).succPNat =>
      WithLp.toLp 2 (finiteGapBlock (K := (⟨n + 1, Nat.succ_pos n⟩ : ℕ+)) X)) :=
    (WithLp.measurable_toLp 2 _).comp
      (measurable_pi_iff.mpr fun i => Riesz1.measurable_gap i.val)
  exact integral_map hm.aemeasurable
    (continuous_finsetSum _ fun i _ => PiLp.continuous_apply 2 _ i).aestronglyMeasurable

/-- See the proof of Lemma 6.5 in the paper, mean comparison at fixed
temperature, before polynomial absorption. This is only the mean clause. The variance bounds and compact-temperature quantifiers are separate. -/
theorem mean_bound_fixed_temperature (s β ε : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (hβ : 0 < β) (hε : 0 < ε) (θ : PhysicalCutoff) :
    ∃ C c δ : ℝ, 0 < C ∧ 0 < c ∧ 0 < δ ∧
      ∀ p : Parameters, p.val.2 = s → p.val.1 = β → ∀ n m : ℕ,
        |(∫ x, ∑ i, x i ∂activeMeasure p n m θ ε) - (n + 1 : ℝ)| ≤
          C * (n + 1 : ℝ) * Real.exp (-c * (n + 1 : ℝ) ^ δ) := by
  obtain ⟨C, c, δ, hC, hc, hδ, hmean⟩ :=
    InterpolatingDensities.tilt_expectation s β ε hs hs1 hβ hε θ
  refine ⟨C, c, δ, hC, hc, hδ, fun p hps hpβ n m => ?_⟩
  have h := (hmean p hps hpβ ((n + 1) + m).succPNat
    (⟨n + 1, Nat.succ_pos n⟩ : ℕ+) (by simp; omega) (by simp; omega)
    (lengthObservable _)).2.2
  rw [blockDerivativeNorm_length] at h
  rw [active_mean_eq]
  simp only [PNat.mk_coe, Nat.cast_add, Nat.cast_one] at h
  change |(∫ X, ∑ i : Fin (n + 1), gap X i.val ∂tiltedParticleMeasure p
    ((n + 1) + m).succPNat (⟨n + 1, Nat.succ_pos n⟩ : ℕ+) _ θ ε true) -
    (∫ X, ∑ i : Fin (n + 1), gap X i.val ∂gibbsMeasure p ((n + 1) + m).succPNat)| ≤
    C * Real.exp (-c * (n + 1 : ℝ) ^ δ) * (n + 1 : ℝ) at h
  rw [untilted_mean p n m] at h
  simpa only [PNat.mk_coe, Nat.cast_add, Nat.cast_one, mul_assoc, mul_comm,
    mul_left_comm] using h

/-- The fixed-temperature mean estimate in the proof of Lemma 6.5 absorbs
the active-size factor. -/
theorem mean_exponential_fixed_temperature (s β ε : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (hβ : 0 < β) (hε : 0 < ε) (θ : PhysicalCutoff) :
    ∃ C c δ : ℝ, 0 < C ∧ 0 < c ∧ 0 < δ ∧
      ∀ p : Parameters, p.val.2 = s → p.val.1 = β → ∀ n m : ℕ,
        |(∫ x, ∑ i, x i ∂activeMeasure p n m θ ε) - (n + 1 : ℝ)| ≤
          C * Real.exp (-c * (n + 1 : ℝ) ^ δ) := by
  obtain ⟨C, c, δ, hC, hc, hδ, h⟩ :=
    mean_bound_fixed_temperature s β ε hs hs1 hβ hε θ
  obtain ⟨B, hB, hb⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := 1) (c := c) (c' := c / 2) hδ (by linarith)
  refine ⟨C * (B + 1), c / 2, δ, by positivity, by positivity, hδ,
    fun p hps hpβ n m => (h p hps hpβ n m).trans ?_⟩
  have ht := hb (n + 1 : ℝ) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  rw [Real.rpow_one] at ht
  nlinarith [Real.exp_pos (-(c / 2) * (n + 1 : ℝ) ^ δ)]

namespace Internal

/-- The fourth-power version of finite Cauchy--Schwarz used in the proof of Lemma 6.5. -/
theorem sum_pow_four_le {ι : Type*} [Fintype ι] (u : ι → ℝ) :
    (∑ i, u i) ^ 4 ≤ (Fintype.card ι : ℝ) ^ 3 * ∑ i, u i ^ 4 := by
  have h₁ := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := u)
  have h₂ := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => u i ^ 2)
  simp only [Finset.card_univ] at h₁ h₂
  have h₃ := pow_le_pow_left₀ (sq_nonneg _) h₁ 2
  have h₄ := mul_le_mul_of_nonneg_left h₂ (sq_nonneg (Fintype.card ι : ℝ))
  simp_rw [← pow_mul, show 2 * 2 = 4 from rfl] at h₄
  calc
    _ ≤ ((Fintype.card ι : ℝ) * ∑ i, u i ^ 2) ^ 2 := by nlinarith [h₃]
    _ = (Fintype.card ι : ℝ) ^ 2 * (∑ i, u i ^ 2) ^ 2 := mul_pow _ _ 2
    _ ≤ _ := by nlinarith [h₄]

/-- See the proof of Lemma 6.5 in the paper, the good-event and
fourth-moment implication. All moments remain extended integrals, so the
bound is meaningful even before finiteness is established. -/
theorem variance_good_bad {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {S : X → ℝ} (hS : MemLp S 2 μ)
    (hSm : Measurable S) (a T : ℝ) (hT : 0 ≤ T) {A : Set X}
    (hA : MeasurableSet A) (hgood : ∀ x ∈ A, |S x - a| ≤ T) :
    Riesz1.variance μ S (hS.integrable one_le_two) ≤ ENNReal.ofReal (T ^ 2) +
      (∫⁻ x, ENNReal.ofReal ((S x - a) ^ 4) ∂μ) ^ (1 / 2 : ℝ) *
        μ Aᶜ ^ (1 / 2 : ℝ) := by
  apply (Riesz1.variance_le_lintegral_sq_sub μ hS a).trans
  rw [← lintegral_add_compl _ hA]
  apply add_le_add
  · calc
      _ ≤ ∫⁻ _x in A, ENNReal.ofReal (T ^ 2) ∂μ := by
        apply setLIntegral_mono' hA
        intro x hx
        exact ENNReal.ofReal_le_ofReal (by
          nlinarith [sq_abs (S x - a), hgood x hx, abs_nonneg (S x - a)])
      _ ≤ ENNReal.ofReal (T ^ 2) := by
        simp only [lintegral_const, Measure.restrict_apply_univ]
        exact mul_le_of_le_one_right' (prob_le_one (μ := μ))
  · have h := LengthAveragingFibres.Internal.restricted_second_moment_le (ν := μ)
      ((hSm.sub_const a).abs.ennreal_ofReal) hA.compl
    have he (x : ℝ) : |x| ^ 4 = x ^ 4 := by
      calc
        _ = (|x| ^ 2) ^ 2 := by ring
        _ = _ := by rw [sq_abs]; ring
    simpa only [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs, he] using h

/-- The Cramér–Rao bound in the proof of Lemma 6.5 follows from the
integration-by-parts pairing and the score-square bound, both assumed here. -/
theorem score_square_lower {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {S T : X → ℝ} (hS : MemLp S 2 μ) (hT : MemLp T 2 μ)
    {β A : ℝ} (hβ : 0 < β) (hA : 0 < A)
    (hpair : β * cov[S, T; μ] = 1)
    (hscore : (∫ x, T x ^ 2 ∂μ) ≤ A / β) :
    ENNReal.ofReal (1 / (β * A)) ≤ Riesz1.variance μ S (hS.integrable one_le_two) := by
  have hCS := CovarianceCauchySchwarz.abs_covariance_le hS hT
  have hCSsq := pow_le_pow_left₀ (abs_nonneg _) hCS 2
  rw [sq_abs, mul_pow,
    Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _),
    Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)] at hCSsq
  have hVT : (∫ x, (T x - ∫ y, T y ∂μ) ^ 2 ∂μ) ≤ ∫ x, T x ^ 2 ∂μ := by
    rw [← ProbabilityTheory.variance_eq_integral hT.aemeasurable]
    exact ProbabilityTheory.variance_le_expectation_sq hT.aestronglyMeasurable
  have hV : 0 ≤ ∫ x, (S x - ∫ y, S y ∂μ) ^ 2 ∂μ :=
    integral_nonneg fun _ => sq_nonneg _
  have hprod := mul_le_mul_of_nonneg_left (hVT.trans hscore) hV
  have hmul := mul_le_mul_of_nonneg_left (hCSsq.trans hprod) (sq_nonneg β)
  have hpairSq : β ^ 2 * cov[S, T; μ] ^ 2 = 1 := by
    rw [← mul_pow, hpair]
    norm_num
  rw [hpairSq] at hmul
  have he : β ^ 2 * ((∫ x, (S x - ∫ y, S y ∂μ) ^ 2 ∂μ) * (A / β)) =
      (∫ x, (S x - ∫ y, S y ∂μ) ^ 2 ∂μ) * (β * A) := by
    field_simp
  rw [he] at hmul
  rw [Riesz1.variance_eq_ofReal_integral_sq μ S hS]
  exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ (mul_pos hβ hA)).mpr hmul)

end Internal

/-- See the proof of Lemma 6.5 in the paper, the required fourth
moment of the length displacement, uniform on a compact temperature
interval and in both volumes. No independence is used. -/
theorem centered_fourth_moment (s ε βlo βhi : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (hε : 0 < ε) (hlo : 0 < βlo) (hle : βlo ≤ βhi) (θ : PhysicalCutoff) :
    ∃ B : ℝ, 0 < B ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ n m : ℕ,
      (∫⁻ x, ENNReal.ofReal (((∑ i, x i) - (n + 1 : ℝ)) ^ 4)
        ∂activeMeasure p n m θ ε) ≤ ENNReal.ofReal (B * (n + 1 : ℝ) ^ 4) := by
  obtain ⟨M, hM, hm⟩ := InterpolantLocalLaws.compact_tilted_gap_moments
    s ε βlo βhi hs hs1 hε hlo hle θ 4 (by norm_num)
  refine ⟨8 * M + 8, by positivity, fun p hps hpl hph n m => ?_⟩
  let N := ((n + 1) + m).succPNat
  let a : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩
  let hn : (a : ℕ) ≤ (N : ℕ) := by
    change n + 1 ≤ n + 1 + m + 1
    omega
  let μ := tiltedParticleMeasure p N a hn θ ε true
  have : IsProbabilityMeasure μ := (InterpolatingDensities.tilt_valid p N a hn θ ε true).2.2
  have hcoordinate (i : Fin (n + 1)) :
      (∫⁻ X, ENNReal.ofReal ((gap X i.val - 1) ^ 4) ∂μ) ≤ ENNReal.ofReal (8 * M + 8) := by
    have hb := (le_add_of_nonneg_right zero_le).trans
      (hm p hps hpl hph N a (by dsimp only [N, Nat.succPNat_coe]; omega) hn i.val)
    have hfour : (∫⁻ X, ENNReal.ofReal (gap X i.val ^ 4) ∂μ) ≤ ENNReal.ofReal M := by
      simpa only [μ, CenteredObservable.rpow_four_eq] using hb
    calc
      _ ≤ ∫⁻ X, ENNReal.ofReal (8 * gap X i.val ^ 4 + 8) ∂μ :=
        lintegral_mono fun X => ENNReal.ofReal_le_ofReal (CenteredObservable.pow_four_sub_one_le _)
      _ = 8 * (∫⁻ X, ENNReal.ofReal (gap X i.val ^ 4) ∂μ) + 8 := by
        have he (X : Riesz1.Configuration N) :
            ENNReal.ofReal (8 * gap X i.val ^ 4 + 8) =
              8 * ENNReal.ofReal (gap X i.val ^ 4) + 8 := by
          rw [ENNReal.ofReal_add (by positivity) (by norm_num),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8), ENNReal.ofReal_ofNat]
        simp_rw [he]
        have hg : Measurable (fun X : Riesz1.Configuration N =>
            ENNReal.ofReal (gap X i.val ^ (4 : ℕ))) :=
          ((Riesz1.measurable_gap i.val).pow_const 4).ennreal_ofReal
        rw [lintegral_add_left (hg.const_mul 8), lintegral_const_mul _ hg]
        simp
      _ ≤ _ := by
        rw [ENNReal.ofReal_add (by positivity) (by norm_num),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8), ENNReal.ofReal_ofNat]
        exact add_le_add (mul_le_mul_of_nonneg_left hfour zero_le) le_rfl
  have hmapping : Measurable (fun X : Riesz1.Configuration N =>
      WithLp.toLp 2 (finiteGapBlock (K := a) X)) :=
    (WithLp.measurable_toLp 2 _).comp
      (measurable_pi_iff.mpr fun i => Riesz1.measurable_gap i.val)
  change (∫⁻ x, ENNReal.ofReal (((∑ i, x i) - (n + 1 : ℝ)) ^ 4)
    ∂μ.map (fun X => WithLp.toLp 2 (finiteGapBlock (K := a) X))) ≤ _
  rw [lintegral_map (by fun_prop) hmapping]
  have hsum (X : Riesz1.Configuration N) :
      (∑ i : Fin (n + 1), gap X i.val) - (n + 1 : ℝ) =
        ∑ i : Fin (n + 1), (gap X i.val - 1) := by
    rw [Finset.sum_sub_distrib]
    simp
  change (∫⁻ X, ENNReal.ofReal (((∑ i : Fin (n + 1), gap X i.val) - (n + 1 : ℝ)) ^ 4) ∂μ) ≤ _
  simp_rw [hsum]
  calc
    _ ≤ ∫⁻ X, ENNReal.ofReal ((n + 1 : ℝ) ^ 3 *
        ∑ i : Fin (n + 1), (gap X i.val - 1) ^ 4) ∂μ := by
      apply lintegral_mono
      intro X
      apply ENNReal.ofReal_le_ofReal
      simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
        Internal.sum_pow_four_le (fun i : Fin (n + 1) => gap X i.val - 1)
    _ = ENNReal.ofReal ((n + 1 : ℝ) ^ 3) *
        ∑ i : Fin (n + 1), ∫⁻ X, ENNReal.ofReal ((gap X i.val - 1) ^ 4) ∂μ := by
      have he (X : Riesz1.Configuration N) :
          ENNReal.ofReal ((n + 1 : ℝ) ^ 3 * ∑ i : Fin (n + 1), (gap X i.val - 1) ^ 4) =
          ENNReal.ofReal ((n + 1 : ℝ) ^ 3) *
            ∑ i : Fin (n + 1), ENNReal.ofReal ((gap X i.val - 1) ^ 4) := by
        rw [ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
      simp_rw [he]
      have hg (i : Fin (n + 1)) : Measurable (fun X : Riesz1.Configuration N =>
          ENNReal.ofReal ((gap X i.val - 1) ^ (4 : ℕ))) :=
        (((Riesz1.measurable_gap i.val).sub_const 1).pow_const 4).ennreal_ofReal
      rw [lintegral_const_mul _ (Finset.measurable_sum _ fun i _ => hg i),
        lintegral_finsetSum _ (fun i _ => hg i)]
    _ ≤ ENNReal.ofReal ((n + 1 : ℝ) ^ 3) *
        ∑ _i : Fin (n + 1), ENNReal.ofReal (8 * M + 8) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hcoordinate i) zero_le
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      push_cast
      ring

/-- The upper variance bound in the proof of Lemma 6.5 has polynomial loss
`2ε`. The tolerance threshold precedes the compact temperature interval. -/
theorem upper_variance (hRig : External.LongRangeRigidityLocallyUniform)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ εstar : ℝ, 0 < εstar ∧ ∀ ε : ℝ, 0 < ε → ε ≤ εstar →
      ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
      ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s →
        βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ n m : ℕ, 1 ≤ n →
        4 * (n + 1) ≤ n + 1 + m + 1 →
        (n + 1 : ℝ) ^ (2 / s) ≤ ((n + 1 + m : ℕ) + 1 : ℝ) →
        Riesz1.variance (activeMeasure p n m θ ε)
          (fun x => ∑ i, x i) (memLp_one_iff_integrable.mp (length_memLp p n m θ ε 1)) ≤
          ENNReal.ofReal (C * (n + 1 : ℝ) ^ (min s 1 + 2 * ε)) := by
  obtain ⟨εstar, a₀, hεstar, ha₀, hrare⟩ :=
    InterpolantLocalLaws.compact_full_law_weighted_rigidity hRig s hs hs1
  refine ⟨εstar, hεstar, fun ε hε hεsmall βlo βhi hlo hle θ => ?_⟩
  obtain ⟨D, c, hD, hc, ht⟩ := hrare ε hε hεsmall ε hε βlo βhi hlo hle θ
  obtain ⟨B, hB, hfour⟩ := centered_fourth_moment s ε βlo βhi hs hs1 hε hlo hle θ
  have hδ : 0 < a₀ * ε := mul_pos ha₀ hε
  obtain ⟨K, hK, hpoly⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := 2) (c := c / 2) (c' := c / 4) hδ (by linarith)
  let H := Real.sqrt B * Real.sqrt D * K
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  refine ⟨1 + H, by positivity, fun p hps hpl hph n m hn2 hsize hscale => ?_⟩
  let N := ((n + 1) + m).succPNat
  let a : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩
  let hn : (a : ℕ) ≤ (N : ℕ) := by change n + 1 ≤ n + 1 + m + 1; omega
  let ν := activeMeasure p n m θ ε
  let μ := tiltedParticleMeasure p N a hn θ ε true
  have hac : (a : ℝ) = n + 1 := by simp [a]
  have : IsProbabilityMeasure μ := (InterpolatingDensities.tilt_valid p N a hn θ ε true).2.2
  have : IsProbabilityMeasure ν :=
    (ProperMarginalChart.activeTiltedGapLaw_density_valid p a m hn θ ε true).2.2.1
  let A : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
    WithLp.ofLp ⁻¹' goodBlockEvent s a N ε
  have hA : MeasurableSet A :=
    (InterpolantLocalLaws.measurableSet_goodBlockEvent s a N ε).preimage
      (WithLp.measurable_ofLp 2 _)
  have hm : Measurable (fun X : Riesz1.Configuration N =>
      WithLp.toLp 2 (finiteGapBlock (K := a) X)) :=
    (WithLp.measurable_toLp 2 _).comp
      (measurable_pi_iff.mpr fun i => Riesz1.measurable_gap i.val)
  have hbad : ν Aᶜ ≤ ENNReal.ofReal (D * Real.exp (-c * (n + 1 : ℝ) ^ (a₀ * ε))) := by
    have hscl : (a : ℝ) ^ (2 / s) ≤ (N : ℝ) := by
      simpa only [N, a, PNat.mk_coe, Nat.succPNat_coe, Nat.cast_add, Nat.cast_succ, Nat.cast_one] using hscale
    have hh := ht p hps hpl hph N a (by change 2 ≤ n + 1; omega)
      hsize hscl hn
    rw [hac] at hh
    change (μ.map (fun X => WithLp.toLp 2 (finiteGapBlock (K := a) X))) Aᶜ ≤ _
    rw [Measure.map_apply hm hA.compl]
    apply le_trans _ hh
    calc
      _ = ∫⁻ _X in {X : Riesz1.Configuration N | finiteGapBlock (K := a) X ∉
          goodBlockEvent s a N ε}, (1 : ℝ≥0∞) ∂μ := by
            rw [lintegral_one, Measure.restrict_apply_univ]
            rfl
      _ ≤ _ := by
        apply lintegral_mono
        intro X
        have hh := InterpolantLocalLaws.one_le_exceptionalWeight s (finiteGapBlock (K := a) X)
          (fun i => (Riesz1.gap_pos X i.val).le)
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hh
  have hgood : ∀ x ∈ A, |(∑ i, x i) - (n + 1 : ℝ)| ≤
      (n + 1 : ℝ) ^ ε * (n + 1 : ℝ) ^ (min s 1 / 2) := by
    intro x hx
    have hh := hx.2.2 0 (n + 1) (by omega) le_rfl
    have he : Finset.univ.filter (fun i : Fin (n + 1) => 0 ≤ i.val ∧ i.val < n + 1) =
        Finset.univ := Finset.filter_true_of_mem (fun i _ => ⟨Nat.zero_le _, i.isLt⟩)
    change |(∑ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => 0 ≤ i.val ∧ i.val < n + 1),
        x i) - ((n + 1 - 0 : ℕ) : ℝ)| ≤
        (a : ℝ) ^ ε * ((n + 1 - 0 : ℕ) : ℝ) ^ (min s 1 / 2) at hh
    rw [he, Nat.sub_zero, hac] at hh
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  have hSm : Measurable (fun x : EuclideanSpace ℝ (Fin (n + 1)) => ∑ i, x i) :=
    (continuous_finsetSum _ fun i _ => PiLp.continuous_apply 2 _ i).measurable
  have hh := Internal.variance_good_bad ν (length_memLp p n m θ ε 2) hSm (n + 1)
    ((n + 1 : ℝ) ^ ε * (n + 1 : ℝ) ^ (min s 1 / 2)) (by positivity) hA hgood
  apply hh.trans
  have hbound := add_le_add
    (le_refl (ENNReal.ofReal (((n + 1 : ℝ) ^ ε * (n + 1 : ℝ) ^ (min s 1 / 2)) ^ 2))) (mul_le_mul
    (ENNReal.rpow_le_rpow (hfour p hps hpl hph n m) (by norm_num : (0 : ℝ) ≤ 1 / 2))
    (ENNReal.rpow_le_rpow hbad (by norm_num : (0 : ℝ) ≤ 1 / 2)) zero_le zero_le)
  apply hbound.trans
  have hnpos : (0 : ℝ) < n + 1 := by positivity
  have hn1 : (1 : ℝ) ≤ n + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hpower : ((n + 1 : ℝ) ^ ε * (n + 1 : ℝ) ^ (min s 1 / 2)) ^ 2 =
      (n + 1 : ℝ) ^ (min s 1 + 2 * ε) := by
    rw [← Real.rpow_add hnpos, ← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
    congr 1
    ring
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
    hpower]
  apply ENNReal.ofReal_le_ofReal
  have hroot : (B * (n + 1 : ℝ) ^ 4) ^ (1 / 2 : ℝ) *
      (D * Real.exp (-c * (n + 1 : ℝ) ^ (a₀ * ε))) ^ (1 / 2 : ℝ) =
      Real.sqrt B * Real.sqrt D * (n + 1 : ℝ) ^ 2 *
        Real.exp (-(c / 2) * (n + 1 : ℝ) ^ (a₀ * ε)) := by
    rw [Real.mul_rpow hB.le (by positivity), Real.mul_rpow hD.le (Real.exp_pos _).le,
      ← Real.rpow_natCast, ← Real.rpow_mul hnpos.le, ← Real.exp_mul]
    norm_num only [show (4 : ℝ) * (1 / 2) = 2 by norm_num]
    rw [← Real.sqrt_eq_rpow B, ← Real.sqrt_eq_rpow D, Real.rpow_two,
      show (-c * (n + 1 : ℝ) ^ (a₀ * ε)) * (1 / 2) =
        -(c / 2) * (n + 1 : ℝ) ^ (a₀ * ε) by ring]
    ring
  rw [hroot]
  have hpoly' := hpoly (n + 1 : ℝ) hn1
  rw [Real.rpow_two] at hpoly'
  have he : Real.exp (-(c / 4) * (n + 1 : ℝ) ^ (a₀ * ε)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (by positivity)) (by positivity))
  have htail : Real.sqrt B * Real.sqrt D * (n + 1 : ℝ) ^ 2 *
      Real.exp (-(c / 2) * (n + 1 : ℝ) ^ (a₀ * ε)) ≤ H := by
    have h := mul_le_mul_of_nonneg_left hpoly' (mul_nonneg (Real.sqrt_nonneg B) (Real.sqrt_nonneg D))
    have h' := mul_le_mul_of_nonneg_left he hH
    dsimp only [H] at h'
    nlinarith
  have hP : 1 ≤ (n + 1 : ℝ) ^ (min s 1 + 2 * ε) :=
    Real.one_le_rpow hn1 (by linarith [le_min hs.le zero_le_one])
  nlinarith

end Riesz2.LengthVariance
