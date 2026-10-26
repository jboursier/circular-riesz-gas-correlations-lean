/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.LocalReconstruction
public import Riesz2.Thermodynamic.LocalReconstructionPart2
public import Riesz2.Thermodynamic.PalmInversionPart2
public import Riesz1.Auxiliary.LoopMomentsLifts
public import Riesz2.ToMathlib.DiscreteTailMoments
public import Riesz2.ToMathlib.TotalVariationMomentTransfer
public import Riesz2.ToMathlib.NonnegativeGibbsTilt
public import Riesz2.Frozen.LimitingRieszProcess

/-!
# Spatial count moments

The proof of Corollary 1.1 gives uniform moments of every positive real order and
convergence of the first two moments on bounded intervals. Counts use the configuration
definitions and the Palm inversion suspension. The composition assumes weak gap
convergence, microscopic local total variation convergence and uniqueness of the limit.
-/

public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace Riesz2

local instance countMomentsConfigurationMeasurableSpace : MeasurableSpace LineConfiguration :=
  configurationMeasurableSpace
local notation "Gaps" => (ℤ → Ioi (0 : ℝ))

/-- Translating a bounded interval translates its two endpoints in the count. This includes empty intervals and both possible signs of the offset. -/
theorem count_translateConfiguration_Ioc (C : LineConfiguration) (u a b : ℝ) :
    count (translateConfiguration u C) (Ioc a b) = count C (Ioc (a + u) (b + u)) := by
  unfold count translateConfiguration
  congr 1
  apply Set.encard_congr
  exact
    { toFun := fun x => ⟨x.val + u, x.property.1, by
        constructor <;> linarith [x.property.2.1, x.property.2.2]⟩
      invFun := fun x => ⟨x.val - u, by simpa using x.property.1, by
        constructor <;> linarith [x.property.2.1, x.property.2.2]⟩
      left_inv := fun x => by ext; simp
      right_inv := fun x => by ext; simp }

/-- See the proof of Corollary 1.1 in the paper, deterministic inversion step.
At every allowed offset, more than `m` points force the first `m` gaps after
the first positive point to fit inside the spatial window. -/
theorem count_gt_implies_short_span_internal
    (y : reconstructibleGapSequences) (u R : ℝ) (hu : 0 ≤ u)
    (huy : u ≤ (y.val 0 : ℝ)) (m : ℕ)
    (hcount : (m : ℝ) < intervalCount 0 R
      (translateConfiguration u (reconstructConfiguration y))) :
    gapSequenceSpan y.val 1 m ≤ R := by
  by_contra h
  have hspan : R < gapPosition y.val ((m : ℤ) + 1) - (y.val 0 : ℝ) := by
    have h := lt_of_not_ge h
    rw [gapSequenceSpan_eq_position_sub_internal y.val (gapPosition y.val)
      (gapPosition_add_one y.val) 1 m] at h
    have h1 : gapPosition y.val 1 = (y.val 0 : ℝ) := by
      simpa only [gapPosition_zero, zero_add] using gapPosition_add_one y.val 0
    simpa only [h1, add_comm] using h
  have hlast : R + u < gapPosition y.val ((m : ℤ) + 1) := by linarith
  have hsub : Ioc u (R + u) ⊆ Ioc (gapPosition y.val 0)
      (gapPosition y.val (m : ℤ)) ∪
        Ioo (gapPosition y.val (m : ℤ)) (gapPosition y.val ((m : ℤ) + 1)) := by
    intro x hx
    by_cases hx' : x ≤ gapPosition y.val (m : ℤ)
    · exact Or.inl ⟨by rw [gapPosition_zero]; linarith [hx.1], hx'⟩
    · exact Or.inr ⟨lt_of_not_ge hx', hx.2.trans_lt hlast⟩
  have hempty : (reconstructConfiguration y).val ∩
      Ioo (gapPosition y.val (m : ℤ)) (gapPosition y.val ((m : ℤ) + 1)) = ∅ := by
    ext x
    constructor
    · rintro ⟨⟨i, rfl⟩, hi⟩
      have h₁ := (gapPosition_strictMono y.val).lt_iff_lt.mp hi.1
      have h₂ := (gapPosition_strictMono y.val).lt_iff_lt.mp hi.2
      omega
    · exact False.elim
  have hb : count (translateConfiguration u (reconstructConfiguration y)) (Ioc 0 R) ≤
      (m : ℝ≥0∞) := by
    rw [count_translateConfiguration_Ioc, zero_add]
    have hsub' : (reconstructConfiguration y).val ∩ Ioc u (R + u) ⊆
        (reconstructConfiguration y).val ∩
          Ioc (gapPosition y.val 0) (gapPosition y.val (m : ℤ)) := by
      rintro x ⟨hx, hx'⟩
      rcases hsub hx' with h | h
      · exact ⟨hx, h⟩
      · have : x ∈ (∅ : Set ℝ) := hempty ▸ ⟨hx, h⟩
        exact False.elim this
    have he := count_reconstructConfiguration_Ioc y 0 (m : ℤ)
    simp only [sub_zero, Int.toNat_natCast] at he
    rw [← he]
    unfold count
    exact_mod_cast Set.encard_mono hsub'
  have hb' : intervalCount 0 R (translateConfiguration u (reconstructConfiguration y)) ≤ m := by
    exact ENNReal.toReal_le_of_le_ofReal (Nat.cast_nonneg m) (by simpa using hb)
  exact (not_lt_of_ge hb') hcount

/-- See the proof of Corollary 1.1 in the paper: the inversion weight
appears explicitly in the count-tail bound. No stationarity or normalization
is needed for this geometric comparison. -/
theorem suspension_count_tail_le_short_span_internal
    (q : Measure reconstructibleGapSequences) [SFinite q] (R : ℝ) (m : ℕ) :
    gapSuspensionMeasure q {C | (m : ℝ) < intervalCount 0 R C} ≤
      ∫⁻ y in {y : reconstructibleGapSequences | gapSequenceSpan y.val 1 m ≤ R},
        ENNReal.ofReal (y.val 0 : ℝ) ∂q := by
  have hE : MeasurableSet {C : LineConfiguration | (m : ℝ) < intervalCount 0 R C} :=
    measurableSet_lt measurable_const (measurable_intervalCount 0 R)
  rw [← lintegral_indicator_one hE]
  change (∫⁻ C, {C : LineConfiguration | (m : ℝ) < intervalCount 0 R C}.indicator
    (fun _ => (1 : ℝ≥0∞)) C ∂gapSuspensionMeasure q) ≤ _
  have hS : MeasurableSet {y : reconstructibleGapSequences | gapSequenceSpan y.val 1 m ≤ R} :=
    measurableSet_le ((continuous_gapSequenceSpan 1 m).measurable.comp measurable_subtype_coe)
      measurable_const
  rw [lintegral_gapSuspensionMeasure q _ (measurable_const.indicator hE),
    ← lintegral_indicator hS]
  apply lintegral_mono
  intro y
  by_cases hy : gapSequenceSpan y.val 1 m ≤ R
  · rw [indicator_of_mem (show y ∈ {y : reconstructibleGapSequences |
      gapSequenceSpan y.val 1 m ≤ R} from hy)]
    calc
      _ ≤ ∫⁻ _u in Ico (0 : ℝ) (y.val 0 : ℝ), (1 : ℝ≥0∞) ∂volume :=
        lintegral_mono fun u => by
          by_cases hc : (m : ℝ) < intervalCount 0 R
              (translateConfiguration u (reconstructConfiguration y)) <;> simp [hc]
      _ = ENNReal.ofReal (y.val 0 : ℝ) := by
        simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ico,
          sub_zero, one_mul]
  · rw [indicator_of_notMem (show y ∉ {y : reconstructibleGapSequences |
      gapSequenceSpan y.val 1 m ≤ R} from hy)]
    apply le_of_eq
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [ae_restrict_mem measurableSet_Ico] with u hu
    have hn : translateConfiguration u (reconstructConfiguration y) ∉
        {C : LineConfiguration | (m : ℝ) < intervalCount 0 R C} :=
      fun hc => hy (count_gt_implies_short_span_internal y u R hu.1 hu.2.le m hc)
    simp only [indicator_of_notMem hn, Pi.zero_apply]

/-- A positive gap span increases with its number of gaps. -/
private theorem count_moment_span_mono (y : Gaps) (i : ℤ) {k m : ℕ} (h : k ≤ m) :
    gapSequenceSpan y i k ≤ gapSequenceSpan y i m := by
  unfold gapSequenceSpan
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h)
    (fun j _ _ => (y _).property.le)

/-- The library's exact lift periodicity gives the length of any whole number
of periods. It also bounds counts in the finitely many volumes below the window size. -/
private theorem count_moment_span_periods {N : ℕ+} (X : Riesz1.Configuration N) (L : ℕ) :
    gapSequenceSpan (periodicGapSequence X) 1 (L * (N : ℕ)) = (L : ℝ) * N := by
  rw [gapSequenceSpan_periodic]
  unfold Riesz1.blockLength
  rw [Nat.cast_mul, Riesz1.cyclicLift_add_int_mul]
  push_cast
  ring

/-- Rigidity controls short spans of the periodic gap law. For large volumes
use the first `min m (N/2)` gaps. Beyond a period the event is empty. For the
remaining volumes a fixed number of complete periods gives a deterministic bound. -/
theorem periodicGapLaw_short_span_rigidity_tail_internal (p : Parameters) (R : ℝ) (hR : 0 < R) :
    ∃ (M : ℕ) (δ C c : ℝ), 0 < δ ∧ 0 < C ∧ 0 < c ∧
      ∀ N : ℕ+, 2 ≤ (N : ℕ) → ∀ m : ℕ, M ≤ m →
        (periodicGapLaw p N).toMeasure {y | gapSequenceSpan y 1 m ≤ R} ≤
          ENNReal.ofReal (C * Real.exp (-c * ((m : ℝ) / 3) ^ δ)) := by
  obtain ⟨η₀, hη₀, hsmall, hrigidity⟩ := periodicGapLaw_finite_rigidity p
  obtain ⟨C, c, hC, hc, hb⟩ := hrigidity (η₀ / 2) (half_pos hη₀) (half_lt_self hη₀)
  let α := min p.val.2 1 / 2 + η₀ / 2
  let δ := η₀ / 2 / (4 * (p.val.2 + 2))
  have hδ : 0 < δ := by dsimp [δ]; have := p.property.2.1; positivity
  obtain ⟨K, hK⟩ := eventually_atTop.mp
    (eventually_short_span_is_deviation_internal α R (by dsimp [α]; linarith))
  let L : ℕ := ⌈R⌉₊ + 1
  have hL : R < (L : ℝ) := by dsimp [L]; push_cast; linarith [Nat.le_ceil R]
  refine ⟨max (3 * K) (max (L * L) 3), δ, C, c, hδ, hC, hc, ?_⟩
  intro N hN m hm
  have hmK : 3 * K ≤ m := (le_max_left _ _).trans hm
  have hmL : L * L ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hm3 : 3 ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans hm)
  have hempty (he : ∀ X : Riesz1.Configuration N,
      ¬gapSequenceSpan (periodicGapSequence X) 1 m ≤ R) :
      (periodicGapLaw p N).toMeasure {y | gapSequenceSpan y 1 m ≤ R} = 0 := by
    rw [periodicGapLaw_toMeasure, Measure.map_apply (measurable_periodicGapSequence N)
      (measurableSet_le (continuous_gapSequenceSpan 1 m).measurable measurable_const)]
    have he' : periodicGapSequence ⁻¹' {y : Gaps | gapSequenceSpan y 1 m ≤ R} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr he
    rw [he', measure_empty]
  by_cases hRN : R < (N : ℝ)
  · by_cases hmN : m < (N : ℕ)
    · let k := min m ((N : ℕ) / 2)
      have hmk : m ≤ 3 * k := by dsimp [k]; omega
      have hk : 1 ≤ k := by omega
      have hkK : K ≤ k := by omega
      have hsub : {y : Gaps | gapSequenceSpan y 1 m ≤ R} ⊆
          {y | (k : ℝ) ^ α < |gapSequenceSpan y 1 k - k|} := by
        intro y hy
        exact hK k hkK y 1 ((count_moment_span_mono y 1 (min_le_left _ _)).trans hy)
      apply (measure_mono hsub).trans
      apply (hb N hN k hk (min_le_right _ _) 1).trans
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply Real.exp_le_exp.mpr
      have hmk' : (m : ℝ) / 3 ≤ k := by
        have hcast : (m : ℝ) ≤ 3 * k := by exact_mod_cast hmk
        linarith
      have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ (m : ℝ) / 3) hmk' hδ.le
      nlinarith
    · rw [hempty (fun X hX => ?_)]
      · exact bot_le
      · have hs := (count_moment_span_mono (periodicGapSequence X) 1
          (le_of_not_gt hmN)).trans hX
        rw [gapSequenceSpan_periodic, Riesz1.blockLength_N] at hs
        exact (not_le_of_gt hRN) hs
  · rw [hempty (fun X hX => ?_)]
    · exact bot_le
    · have hNL : (N : ℕ) ≤ L := by exact_mod_cast ((le_of_not_gt hRN).trans hL.le)
      have hs := (count_moment_span_mono (periodicGapSequence X) 1
        ((Nat.mul_le_mul_left L hNL).trans hmL)).trans hX
      rw [count_moment_span_periods] at hs
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
      have hL0 : 0 ≤ (L : ℝ) := hR.le.trans hL.le
      nlinarith

/-- The limiting gap rigidity bound has no half-period restriction. -/
theorem limiting_short_span_rigidity_tail_internal
    (q : ProbabilityMeasure Gaps) (R α δ C c : ℝ) (hα : α < 1) (hδ : 0 < δ)
    (hC : 0 < C) (hc : 0 < c)
    (hdev : ∀ m : ℕ, 1 ≤ m → q.toMeasure
      {y | (m : ℝ) ^ α < |gapSequenceSpan y 1 m - m|} ≤
        ENNReal.ofReal (C * Real.exp (-c * (m : ℝ) ^ δ))) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → q.toMeasure {y | gapSequenceSpan y 1 m ≤ R} ≤
      ENNReal.ofReal (C * Real.exp (-c * ((m : ℝ) / 3) ^ δ)) := by
  obtain ⟨M, hM⟩ := eventually_atTop.mp
    (eventually_short_span_is_deviation_internal α R hα)
  refine ⟨max M 1, fun m hm => ?_⟩
  apply (measure_mono (fun y hy => hM m ((le_max_left _ _).trans hm) y 1 hy)).trans
  apply (hdev m ((le_max_right _ _).trans hm)).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ (m : ℝ) / 3)
    (by linarith [Nat.cast_nonneg (α := ℝ) m] : (m : ℝ) / 3 ≤ m) hδ.le
  nlinarith

/-- Cauchy--Schwarz controls the inversion weight using only its second
moment. The unweighted short-span bound is supplied by rigidity below. -/
theorem suspension_count_tail_of_short_span_internal
    (q : Measure reconstructibleGapSequences) [IsProbabilityMeasure q]
    (R A b : ℝ) (hA : 0 ≤ A) (hb : 0 ≤ b) (m : ℕ)
    (hsecond : (∫⁻ y, ENNReal.ofReal ((y.val 0 : ℝ) ^ (2 : ℝ)) ∂q) ≤ ENNReal.ofReal A)
    (hprob : (q.map Subtype.val) {y : Gaps | gapSequenceSpan y 1 m ≤ R} ≤ ENNReal.ofReal b) :
    gapSuspensionMeasure q {C | (m : ℝ) < intervalCount 0 R C} ≤
      ENNReal.ofReal (Real.sqrt A * Real.sqrt b) := by
  have hS : MeasurableSet {y : reconstructibleGapSequences | gapSequenceSpan y.val 1 m ≤ R} :=
    measurableSet_le ((continuous_gapSequenceSpan 1 m).measurable.comp measurable_subtype_coe)
      measurable_const
  have hprob' : q {y : reconstructibleGapSequences | gapSequenceSpan y.val 1 m ≤ R} ≤
      ENNReal.ofReal b := by
    simpa only [Measure.map_apply measurable_subtype_coe
      (measurableSet_le (continuous_gapSequenceSpan 1 m).measurable measurable_const),
      preimage_ofPred_eq] using hprob
  have hw : Measurable (fun y : reconstructibleGapSequences => (y.val 0 : ℝ)) :=
    measurable_subtype_coe.comp ((measurable_pi_apply 0).comp measurable_subtype_coe)
  have habs (y : reconstructibleGapSequences) : |(y.val 0 : ℝ)| = (y.val 0 : ℝ) :=
    abs_of_pos (y.val 0).property
  obtain ⟨hi, hbound⟩ := MomentEvent.integrable_rpow_abs_and_integral_le_of_lintegral_le
    hw hA (by simpa only [habs] using hsecond)
  have hi' : Integrable (fun y : reconstructibleGapSequences => (y.val 0 : ℝ) ^ 2) q := by
    simpa only [habs, Real.rpow_two] using hi
  have hbound' : (∫ y : reconstructibleGapSequences, (y.val 0 : ℝ) ^ 2 ∂q) ≤ A := by
    simpa only [habs, Real.rpow_two] using hbound
  have hcs := MomentEvent.abs_integral_mul_le_sqrt_mul_sqrt
    (g := fun _ : reconstructibleGapSequences => (1 : ℝ)) (M := 1)
    measurable_const hw zero_le_one (fun _ => by norm_num) hi' hS
  simp only [one_mul] at hcs
  have hprobReal := ENNReal.toReal_le_of_le_ofReal hb hprob'
  have hle := hcs.trans (mul_le_mul (Real.sqrt_le_sqrt hbound')
    (Real.sqrt_le_sqrt hprobReal) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hiY := MomentEvent.integrable_of_integrable_sq hw hi'
  apply (suspension_count_tail_le_short_span_internal q R m).trans
  rw [← ofReal_integral_eq_lintegral_ofReal hiY.integrableOn
    (ae_of_all _ fun y => (y.val 0).property.le)]
  exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans hle)

/-- Palm inversion turns the rigidity tail into a stretched-exponential
spatial count tail. Cauchy--Schwarz halves the rate and requires only the
second moment of the distinguished gap. -/
theorem suspension_count_stretched_tail_internal
    (q : Measure reconstructibleGapSequences) [IsProbabilityMeasure q]
    (R A C c δ : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (m : ℕ)
    (hsecond : (∫⁻ y, ENNReal.ofReal ((y.val 0 : ℝ) ^ (2 : ℝ)) ∂q) ≤ ENNReal.ofReal A)
    (hprob : (q.map Subtype.val) {y : Gaps | gapSequenceSpan y 1 m ≤ R} ≤
      ENNReal.ofReal (C * Real.exp (-c * ((m : ℝ) / 3) ^ δ))) :
    gapSuspensionMeasure q {X | (m : ℝ) < intervalCount 0 R X} ≤
      ENNReal.ofReal (Real.sqrt A * Real.sqrt C *
        Real.exp (-(c / 2) * ((m : ℝ) / 3) ^ δ)) := by
  have h := suspension_count_tail_of_short_span_internal q R A
    (C * Real.exp (-c * ((m : ℝ) / 3) ^ δ)) hA (by positivity) m hsecond hprob
  have he : Real.sqrt (Real.exp (-c * ((m : ℝ) / 3) ^ δ)) =
      Real.exp (-(c / 2) * ((m : ℝ) / 3) ^ δ) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    ring
  simpa only [Real.sqrt_mul hC, he, mul_assoc] using h

/-- Tail summation after rigidity and Palm inversion. The stretched
exponential count tail supplies every polynomial order. The bounded initial
segment uses probability at most one. -/
theorem suspension_count_moment_bound_of_rigidity_internal
    (p R A δ C c : ℝ) (hp : 0 < p) (hA : 0 ≤ A) (hδ : 0 < δ)
    (hC : 0 < C) (hc : 0 < c) (M : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (q : Measure reconstructibleGapSequences)
      [IsProbabilityMeasure q] [IsProbabilityMeasure (gapSuspensionMeasure q)],
      (∫⁻ y, ENNReal.ofReal ((y.val 0 : ℝ) ^ (2 : ℝ)) ∂q) ≤ ENNReal.ofReal A →
      (∀ m : ℕ, M ≤ m → (q.map Subtype.val) {y : Gaps | gapSequenceSpan y 1 m ≤ R} ≤
        ENNReal.ofReal (C * Real.exp (-c * ((m : ℝ) / 3) ^ δ))) →
      (∫⁻ X, ENNReal.ofReal (intervalCount 0 R X ^ p) ∂gapSuspensionMeasure q) ≤
        ENNReal.ofReal B := by
  obtain ⟨k, hk⟩ := exists_nat_gt (p + 1)
  let d := c / 2 / (3 : ℝ) ^ δ
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨D, hD, hpoly⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := k) (c := d) (c' := 0) hδ hd
  let E := Real.sqrt A * Real.sqrt C
  let F := max (E * D) (((M : ℝ) + 1) ^ k)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  obtain ⟨B, hB, hbound⟩ := exists_moment_bound_of_polynomial_tails p (k : ℝ) F hp hk hF
  refine ⟨B, hB, fun q _ _ hsecond htail => ?_⟩
  apply hbound (gapSuspensionMeasure q) (intervalCount 0 R) (measurable_intervalCount 0 R)
    (fun _ => ENNReal.toReal_nonneg)
  intro n
  let m := n + 1
  have hm : (0 : ℝ) < m := by dsimp [m]; positivity
  have hm1 : (1 : ℝ) ≤ m := by dsimp [m]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hmcast : (m : ℝ) = (n : ℝ) + 1 := by simp [m]
  rw [← hmcast]
  change gapSuspensionMeasure q {X | (m : ℝ) < intervalCount 0 R X} ≤
    ENNReal.ofReal (F / (m : ℝ) ^ (k : ℝ))
  by_cases hMm : M ≤ m
  · have hrate := hpoly (m : ℝ) hm1
    simp only [neg_zero, zero_mul, Real.exp_zero, mul_one, Real.rpow_natCast] at hrate
    have hexp : -(c / 2) * ((m : ℝ) / 3) ^ δ = -d * (m : ℝ) ^ δ := by
      rw [Real.div_rpow (by positivity) (by norm_num)]
      dsimp [d]
      ring
    apply (suspension_count_stretched_tail_internal q R A C c δ hA hC.le m
      hsecond (htail m hMm)).trans
    apply ENNReal.ofReal_le_ofReal
    rw [hexp, Real.rpow_natCast, le_div_iff₀ (pow_pos hm _)]
    calc
      _ = E * ((m : ℝ) ^ k * Real.exp (-d * (m : ℝ) ^ δ)) := by dsimp [E]; ring
      _ ≤ E * D := mul_le_mul_of_nonneg_left hrate hE
      _ ≤ F := le_max_left _ _
  · have hsmall : (m : ℝ) ^ (k : ℝ) ≤ F := by
      rw [Real.rpow_natCast]
      have hmM : (m : ℝ) ≤ (M : ℝ) + 1 := by exact_mod_cast (show m ≤ M + 1 by omega)
      exact (pow_le_pow_left₀ hm.le hmM k).trans (le_max_right _ _)
    have h1 : (1 : ℝ) ≤ F / (m : ℝ) ^ (k : ℝ) := by
      exact (le_div_iff₀ (Real.rpow_pos_of_pos hm _)).mpr (by simpa using hsmall)
    exact prob_le_one.trans (by simpa using ENNReal.ofReal_le_ofReal h1)

/-- Power moments transport to the true reconstruction carrier. No value of a
configuration is assigned to a gap sequence outside that carrier. -/
theorem lintegral_reconstructionGapMeasure_coordinate_rpow
    (μ : Measure Gaps) (hs : ∀ᵐ y ∂μ, y ∈ reconstructibleGapSequences) (i : ℤ) (r : ℝ) :
    (∫⁻ y, ENNReal.ofReal ((y.val i : ℝ) ^ r) ∂reconstructionGapMeasure μ) =
      ∫⁻ y : Gaps, ENNReal.ofReal ((y i : ℝ) ^ r) ∂μ := by
  have hf : Measurable (fun y : Gaps => ENNReal.ofReal ((y i : ℝ) ^ r)) :=
    ((measurable_subtype_coe.comp (measurable_pi_apply i)).pow_const r).ennreal_ofReal
  calc
    _ = ∫⁻ y : Gaps, ENNReal.ofReal ((y i : ℝ) ^ r)
        ∂(reconstructionGapMeasure μ).map Subtype.val :=
      (lintegral_map hf measurable_subtype_coe).symm
    _ = _ := by rw [map_reconstructionGapMeasure μ hs]

/-- The actual finite periodic gap law is supported on the reconstruction
carrier, including the one-particle boundary. -/
theorem periodicGapLaw_reconstructible (p : Parameters) (N : ℕ+) :
    ∀ᵐ y ∂(periodicGapLaw p N).toMeasure, y ∈ reconstructibleGapSequences := by
  rw [periodicGapLaw_toMeasure]
  exact (ae_map_iff (measurable_periodicGapSequence N).aemeasurable
    measurableSet_reconstructibleGapSequences).mpr
    (ae_of_all _ fun X => finite_configuration_mem_reconstructibleGapSequences X)

/-- See the proof of Corollary 1.1 in the paper, finite-volume clause,
proved for every volume at least two. In particular this includes the required
range `N ≥ 8*R + 8`. The law is the actual periodic spatial Gibbs law. -/
theorem periodic_spatial_count_moment_bound (p : Parameters) (R r : ℝ)
    (hR : 0 < R) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ+, 2 ≤ (N : ℕ) →
      (∫⁻ X, ENNReal.ofReal (intervalCount 0 R X ^ r) ∂periodicSpatialLaw p N) ≤
        ENNReal.ofReal C := by
  obtain ⟨M, δ, D, c, hδ, hD, hc, htail⟩ :=
    periodicGapLaw_short_span_rigidity_tail_internal p R hR
  obtain ⟨A, hA, hsecond⟩ := periodicGapLaw_moment_bound p 2 (by norm_num)
  obtain ⟨C, hC, hb⟩ := suspension_count_moment_bound_of_rigidity_internal
    r R A δ D c hr hA.le hδ hD hc M
  refine ⟨C, hC, fun N hN => ?_⟩
  let q := reconstructionGapMeasure (periodicGapLaw p N).toMeasure
  have : IsProbabilityMeasure q :=
    reconstructionGapMeasure_probability _ (periodicGapLaw_reconstructible p N)
  have : IsProbabilityMeasure (gapSuspensionMeasure q) := by
    dsimp [q]
    rw [reconstructionGapMeasure_periodicGapLaw, gapSuspensionMeasure_finite]
    exact periodicSpatialLaw_probability p N
  rw [← gapSuspensionMeasure_finite, ← reconstructionGapMeasure_periodicGapLaw]
  apply hb q
  · rw [lintegral_reconstructionGapMeasure_coordinate_rpow _ (periodicGapLaw_reconstructible p N)]
    exact (le_add_right le_rfl).trans (hsecond N hN 0)
  · rw [show q.map Subtype.val = (periodicGapLaw p N).toMeasure from
      map_reconstructionGapMeasure _ (periodicGapLaw_reconstructible p N)]
    exact htail N hN

/-- The infinite-volume moment bound in the proof of Corollary 1.1 follows
from weak gap convergence. The Palm inversion candidate is normalized and
has a finite bound for every positive real moment. -/
theorem limiting_suspension_count_moments_from_gap_limit_internal
    (p : Parameters) (q : ProbabilityMeasure Gaps)
    (hq : Tendsto (fun n : ℕ => periodicGapLaw p n.succPNat) atTop (𝓝 q)) :
    IsProbabilityMeasure (gapSuspensionMeasure (reconstructionGapMeasure q.toMeasure)) ∧
      ∀ R r : ℝ, 0 < R → 0 < r → ∃ C : ℝ, 0 < C ∧
        (∫⁻ X, ENNReal.ofReal (intervalCount 0 R X ^ r)
          ∂gapSuspensionMeasure (reconstructionGapMeasure q.toMeasure)) ≤ ENNReal.ofReal C := by
  let V : ℕ → ℕ+ := fun n => (n + 1).succPNat
  have hV : ∀ n, 2 ≤ (V n : ℕ) := by intro n; simp [V]
  have hVtop : Tendsto (fun n => (V n : ℕ)) atTop atTop := by
    simpa only [V, Nat.succPNat_coe, Nat.add_assoc, one_add_one_eq_two] using
      tendsto_add_atTop_nat 2
  have hqV : Tendsto (fun n => periodicGapLaw p (V n)) atTop (𝓝 q) :=
    (tendsto_add_atTop_iff_nat 1).mpr hq
  have havg := periodicGapLaw_limit_averages p V hV hVtop q hqV
  have hs : ∀ᵐ y ∂q.toMeasure, y ∈ reconstructibleGapSequences := by
    filter_upwards [havg] with y hy
    apply mem_reconstructibleGapSequences_of_divergent_sums
    · exact gapSequenceSpan_diverges_of_average_internal y (fun _ => 0) hy.1
    · exact gapSequenceSpan_diverges_of_average_internal y (fun k => -(k : ℤ)) hy.2
  let μ := reconstructionGapMeasure q.toMeasure
  have : IsProbabilityMeasure μ := reconstructionGapMeasure_probability _ hs
  have hmean := periodicGapLaw_limit_mean p V hV q hqV
  have hmean' := reconstructionGapMeasure_mean q.toMeasure hs 0 (hmean 0).1 (hmean 0).2
  have : IsProbabilityMeasure (gapSuspensionMeasure μ) :=
    gapSuspensionMeasure_probability _ hmean'.1 hmean'.2
  refine ⟨inferInstance, fun R r hR hr => ?_⟩
  obtain ⟨η₀, hη₀, hsmall, hrigidity⟩ := periodicGapLaw_limit_rigidity p V hV hVtop q hqV
  obtain ⟨D, c, hD, hc, hdev⟩ := hrigidity (η₀ / 2) (half_pos hη₀) (half_lt_self hη₀)
  let δ := η₀ / 2 / (4 * (p.val.2 + 2))
  have hδ : 0 < δ := by dsimp [δ]; have := p.property.2.1; positivity
  obtain ⟨M, htail⟩ := limiting_short_span_rigidity_tail_internal q R
    (min p.val.2 1 / 2 + η₀ / 2) δ D c (by linarith) hδ hD hc
    (fun m hm => hdev m hm 1)
  obtain ⟨A, hA, _, hsecond⟩ := periodicGapLaw_limit_moment_bound p V hV q hqV 2 (by norm_num)
  obtain ⟨C, hC, hb⟩ := suspension_count_moment_bound_of_rigidity_internal
    r R A δ D c hr hA.le hδ hD hc M
  refine ⟨C, hC, hb μ ?_ ?_⟩
  · rw [lintegral_reconstructionGapMeasure_coordinate_rpow _ hs]
    exact (le_add_right le_rfl).trans (hsecond 0)
  · rw [show μ.map Subtype.val = q.toMeasure from map_reconstructionGapMeasure _ hs]
    exact htail


/-- A bounded interval count factors through restriction to any containing
window, with exactly the endpoint conventions. -/
theorem intervalCount_restrictConfiguration (a b S : ℝ)
    (hsub : Ioc a b ⊆ Icc (-S) S) (C : LineConfiguration) :
    intervalCount a b (restrictConfiguration (Icc (-S) S) C) = intervalCount a b C := by
  unfold intervalCount
  rw [count_restrictConfiguration, inter_eq_left.mpr hsub]

/-- See the proof of Corollary 1.1 in the paper, measurable-law passage.
Local total variation controls the law of every fixed bounded interval count. -/
theorem intervalCount_law_totalVariation_tendsto_from_local_internal
    (laws : ℕ+ → Measure LineConfiguration) (P : PointProcess)
    (hlocal : LocalConverges laws P) (a b : ℝ) :
    letI (N : ℕ+) : IsProbabilityMeasure (laws N) := hlocal.choose N
    Tendsto (fun n : ℕ => totalVariation
      ((laws n.succPNat).map (intervalCount a b))
      ((P : Measure LineConfiguration).map (intervalCount a b))) atTop (𝓝 0) := by
  have (N : ℕ+) : IsProbabilityMeasure (laws N) := hlocal.choose N
  let S := max |a| |b| + 1
  have hS : 0 < S := by dsimp [S]; positivity
  have hsub : Ioc a b ⊆ Icc (-S) S := by
    intro x hx
    have ha : |a| ≤ S := by dsimp [S]; linarith [le_max_left |a| |b|]
    have hb : |b| ≤ S := by dsimp [S]; linarith [le_max_right |a| |b|]
    constructor <;> linarith [neg_abs_le a, le_abs_self b, hx.1, hx.2]
  have hres := measurable_restrictConfiguration (Icc (-S) S) measurableSet_Icc
  have hcount := measurable_intervalCount a b
  have hfactor (μ : Measure LineConfiguration) :
      (μ.map (restrictConfiguration (Icc (-S) S))).map (intervalCount a b) =
        μ.map (intervalCount a b) := by
    rw [Measure.map_map hcount hres]
    congr 1
    funext C
    exact intervalCount_restrictConfiguration a b S hsub C
  have ht : Tendsto (fun n : ℕ => totalVariation
      ((laws n.succPNat).map (restrictConfiguration (Icc (-S) S)))
      ((P : Measure LineConfiguration).map (restrictConfiguration (Icc (-S) S))))
      atTop (𝓝 0) := hlocal.choose_spec S hS
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => bot_le)
  intro n
  simpa only [hfactor] using NonnegativeTilt.totalVariation_map_le
    ((laws n.succPNat).map (restrictConfiguration (Icc (-S) S)))
    ((P : Measure LineConfiguration).map (restrictConfiguration (Icc (-S) S)))
    (intervalCount a b) hcount

/-- A finite nonnegative fourth moment gives the actual square integrability
of the squared observable and bounds its integral. -/
theorem memLp_sq_and_integral_fourth_le_of_lintegral_le_internal
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ)
    (hf : Measurable f) (D : ℝ) (hD : 0 ≤ D)
    (hfourth : (∫⁻ x, ENNReal.ofReal (f x ^ 4) ∂μ) ≤ ENNReal.ofReal D) :
    MemLp (fun x => f x ^ 2) 2 μ ∧ (∫ x, (f x ^ 2) ^ 2 ∂μ) ≤ D := by
  have hnn (x : Ω) : 0 ≤ (f x ^ 2) ^ 2 := sq_nonneg _
  have hi : Integrable (fun x => (f x ^ 2) ^ 2) μ := by
    refine ⟨(hf.pow_const 2 |>.pow_const 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all μ hnn)).mpr ?_⟩
    simpa only [← pow_mul, show (2 : ℕ) * 2 = 4 from rfl] using
      hfourth.trans_lt ENNReal.ofReal_lt_top
  refine ⟨(memLp_two_iff_integrable_sq (hf.pow_const 2).aestronglyMeasurable).mpr hi, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff hD).mp
  rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all μ hnn)]
  simpa only [← pow_mul, show (2 : ℕ) * 2 = 4 from rfl] using hfourth

/-- See the proof of Corollary 1.1 in the paper, the final analytic passage
from local total variation and fourth moments to first and second moments.
The hypotheses are internal interfaces. The count moment bounds themselves
are supplied by the spatial estimates of the preceding module. -/
theorem intervalCount_first_second_moments_tendsto_internal
    (laws : ℕ+ → Measure LineConfiguration) (P : PointProcess)
    (hlocal : LocalConverges laws P) (a b D : ℝ) (hD : 0 ≤ D)
    (hfinite : ∀ N : ℕ+, 2 ≤ (N : ℕ) →
      (∫⁻ C, ENNReal.ofReal (intervalCount a b C ^ 4) ∂laws N) ≤ ENNReal.ofReal D)
    (hlimit : (∫⁻ C, ENNReal.ofReal (intervalCount a b C ^ 4) ∂P) ≤ ENNReal.ofReal D) :
    (∀ N : ℕ+, 2 ≤ (N : ℕ) → Integrable (intervalCount a b) (laws N) ∧
      Integrable (fun C => intervalCount a b C ^ 2) (laws N)) ∧
    Integrable (intervalCount a b) (P : Measure LineConfiguration) ∧
    Integrable (fun C => intervalCount a b C ^ 2) (P : Measure LineConfiguration) ∧
    Tendsto (fun n : ℕ => ∫ C, intervalCount a b C ∂laws n.succPNat)
      atTop (𝓝 (∫ C, intervalCount a b C ∂P)) ∧
    Tendsto (fun n : ℕ => ∫ C, intervalCount a b C ^ 2 ∂laws n.succPNat)
      atTop (𝓝 (∫ C, intervalCount a b C ^ 2 ∂P)) := by
  have (N : ℕ+) : IsProbabilityMeasure (laws N) := hlocal.choose N
  let c := intervalCount a b
  have hc : Measurable c := measurable_intervalCount a b
  have hfin N hN := memLp_sq_and_integral_fourth_le_of_lintegral_le_internal
    (laws N) c hc D hD (hfinite N hN)
  have hlim := memLp_sq_and_integral_fourth_le_of_lintegral_le_internal
    (P : Measure LineConfiguration) c hc D hD hlimit
  have integrable_count (μ : Measure LineConfiguration) [IsProbabilityMeasure μ]
      (h : MemLp (fun C => c C ^ 2) 2 μ) : Integrable c μ :=
    ((memLp_two_iff_integrable_sq hc.aestronglyMeasurable).mpr
      (h.integrable (by norm_num))).integrable (by norm_num)
  refine ⟨fun N hN => ⟨integrable_count _ (hfin N hN).1, (hfin N hN).1.integrable (by norm_num)⟩,
    integrable_count _ hlim.1, hlim.1.integrable (by norm_num), ?_⟩
  let μ : ℕ → ProbabilityMeasure ℝ := fun n => ⟨(laws (n + 1).succPNat).map c, inferInstance⟩
  let ν : ProbabilityMeasure ℝ := ⟨(P : Measure LineConfiguration).map c, inferInstance⟩
  have htv := intervalCount_law_totalVariation_tendsto_from_local_internal laws P hlocal a b
  have htv' := (tendsto_add_atTop_iff_nat 1).mpr htv
  have hweak := probabilityMeasure_tendsto_of_totalVariation μ ν htv'
  have hfourth n : (∫⁻ x : ℝ, ENNReal.ofReal (x ^ 4) ∂μ n) ≤ ENNReal.ofReal D := by
    change (∫⁻ x : ℝ, ENNReal.ofReal (x ^ 4) ∂(laws (n + 1).succPNat).map c) ≤ _
    rw [lintegral_map (by fun_prop) hc]
    exact hfinite _ (by simp)
  have hνfourth : (∫⁻ x : ℝ, ENNReal.ofReal (x ^ 4) ∂ν) ≤ ENNReal.ofReal D := by
    change (∫⁻ x : ℝ, ENNReal.ofReal (x ^ 4) ∂(P : Measure LineConfiguration).map c) ≤ _
    rw [lintegral_map (by fun_prop) hc]
    exact hlimit
  have hμ n := memLp_sq_and_integral_fourth_le_of_lintegral_le_internal
    (μ n).toMeasure id measurable_id D hD (hfourth n)
  have hν := memLp_sq_and_integral_fourth_le_of_lintegral_le_internal
    ν.toMeasure id measurable_id D hD hνfourth
  have ht := WeakMomentTruncation.first_second_moments_tendsto_of_uniform_fourth_internal
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak)
    (fun n => (hμ n).1) hν.1 (Eventually.of_forall fun n => (hμ n).2)
  have he (ρ : Measure LineConfiguration) (j : ℕ) :
      (∫ x : ℝ, x ^ j ∂ρ.map c) = ∫ C, c C ^ j ∂ρ :=
    integral_map hc.aemeasurable (by fun_prop)
  have heId (ρ : Measure LineConfiguration) :
      (∫ x : ℝ, x ∂ρ.map c) = ∫ C, c C ∂ρ :=
    integral_map hc.aemeasurable measurable_id.aestronglyMeasurable
  change Tendsto (fun n : ℕ => ∫ x : ℝ, x ∂(laws (n + 1).succPNat).map c) atTop
      (𝓝 (∫ x : ℝ, x ∂(P : Measure LineConfiguration).map c)) ∧
    Tendsto (fun n : ℕ => ∫ x : ℝ, x ^ 2 ∂(laws (n + 1).succPNat).map c) atTop
      (𝓝 (∫ x : ℝ, x ^ 2 ∂(P : Measure LineConfiguration).map c)) at ht
  simp only [heId, he] at ht
  exact ⟨(tendsto_add_atTop_iff_nat 1).mp ht.1, (tendsto_add_atTop_iff_nat 1).mp ht.2⟩

/-- The interval count under translation has the literal endpoint-shift
identity, including empty intervals. -/
theorem intervalCount_translateConfiguration (C : LineConfiguration) (u a b : ℝ) :
    intervalCount a b (translateConfiguration u C) = intervalCount (a + u) (b + u) C := by
  unfold intervalCount
  rw [count_translateConfiguration_Ioc]

/-- The normalization and second moment of a suspension supply the mean-one
input of the stationarity theorem. -/
theorem suspension_stationary_of_second_moment_internal
    (q : Measure reconstructibleGapSequences) [IsProbabilityMeasure q]
    [IsProbabilityMeasure (gapSuspensionMeasure q)]
    (hshift : q.map (reindexReconstructibleGaps 1) = q) (A : ℝ) (hA : 0 ≤ A)
    (hsecond : (∫⁻ y, ENNReal.ofReal ((y.val 0 : ℝ) ^ (2 : ℝ)) ∂q) ≤ ENNReal.ofReal A) :
    ∀ t : ℝ, (gapSuspensionMeasure q).map (translateConfiguration t) = gapSuspensionMeasure q := by
  have hw : Measurable (fun y : reconstructibleGapSequences => (y.val 0 : ℝ)) :=
    measurable_subtype_coe.comp ((measurable_pi_apply 0).comp measurable_subtype_coe)
  have habs (y : reconstructibleGapSequences) : |(y.val 0 : ℝ)| = (y.val 0 : ℝ) :=
    abs_of_pos (y.val 0).property
  obtain ⟨hi, _⟩ := MomentEvent.integrable_rpow_abs_and_integral_le_of_lintegral_le
    hw hA (by simpa only [habs] using hsecond)
  have hi' : Integrable (fun y : reconstructibleGapSequences => (y.val 0 : ℝ) ^ 2) q := by
    simpa only [habs, Real.rpow_two] using hi
  have hiY := MomentEvent.integrable_of_integrable_sq hw hi'
  have hmean : (∫ y : reconstructibleGapSequences, (y.val 0 : ℝ) ∂q) = 1 := by
    have he : ENNReal.ofReal (∫ y : reconstructibleGapSequences, (y.val 0 : ℝ) ∂q) = 1 := by
      rw [ofReal_integral_eq_lintegral_ofReal hiY (ae_of_all _ fun y => (y.val 0).property.le),
        ← gapSuspensionMeasure_univ, measure_univ]
    have he' := congrArg ENNReal.toReal he
    simpa only [ENNReal.toReal_ofReal (integral_nonneg fun y : reconstructibleGapSequences => (y.val 0).property.le),
      ENNReal.toReal_one] using he'
  exact gapSuspensionMeasure_stationary_internal q hshift hiY hmean

/-- See the proof of Corollary 1.1 in the paper: the finite periodic
spatial law is stationary, directly from its already identified suspension. -/
theorem periodicSpatialLaw_stationary (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    ∀ t : ℝ, (periodicSpatialLaw p N).map (translateConfiguration t) = periodicSpatialLaw p N := by
  let q := reconstructionGapMeasure (periodicGapLaw p N).toMeasure
  have : IsProbabilityMeasure q := reconstructionGapMeasure_probability _ (periodicGapLaw_reconstructible p N)
  have he : gapSuspensionMeasure q = periodicSpatialLaw p N := by
    dsimp [q]
    rw [reconstructionGapMeasure_periodicGapLaw, gapSuspensionMeasure_finite]
  have : IsProbabilityMeasure (gapSuspensionMeasure q) := by
    rw [he]
    exact periodicSpatialLaw_probability p N
  have hs : (periodicGapLaw p N).toMeasure.map (fun y j => y (j + 1)) =
      (periodicGapLaw p N).toMeasure := by
    have h := congrArg ProbabilityMeasure.toMeasure (periodicGapLaw_shift_all p N 1)
    rw [ProbabilityMeasure.toMeasure_map] at h
    change (periodicGapLaw p N).toMeasure.map (fun y j => y (1 + j)) = _ at h
    simpa only [add_comm] using h
  have hshift := reconstructionGapMeasure_shift (periodicGapLaw p N).toMeasure
    (periodicGapLaw_reconstructible p N) 1 hs
  obtain ⟨A, hA, hsecond⟩ := periodicGapLaw_moment_bound p 2 (by norm_num)
  have hsecond' : (∫⁻ y, ENNReal.ofReal ((y.val 0 : ℝ) ^ (2 : ℝ)) ∂q) ≤ ENNReal.ofReal A := by
    rw [lintegral_reconstructionGapMeasure_coordinate_rpow _ (periodicGapLaw_reconstructible p N)]
    exact (le_add_right le_rfl).trans (hsecond N hN 0)
  simpa only [he] using suspension_stationary_of_second_moment_internal q hshift A hA.le hsecond'

/-- Translating the origin window transfers any of its nonnegative moments
under a stationary law. -/
theorem lintegral_intervalCount_rpow_of_stationary
    (μ : Measure LineConfiguration) (hstat : ∀ t, μ.map (translateConfiguration t) = μ)
    (a b r : ℝ) :
    (∫⁻ C, ENNReal.ofReal (intervalCount a b C ^ r) ∂μ) =
      ∫⁻ C, ENNReal.ofReal (intervalCount 0 (b - a) C ^ r) ∂μ := by
  have hf : Measurable (fun C => ENNReal.ofReal (intervalCount 0 (b - a) C ^ r)) :=
    ((measurable_intervalCount 0 (b - a)).pow_const r).ennreal_ofReal
  have he := lintegral_map (μ := μ) hf (measurable_translateConfiguration_const a)
  rw [hstat a] at he
  simpa only [intervalCount_translateConfiguration, zero_add, sub_add_cancel] using he.symm

/-- See the proof of Corollary 1.1 in the paper, uniform finite-volume
moments on every bounded half-open interval. -/
theorem periodic_spatial_interval_count_moment_bound (p : Parameters) (a b r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ+, 2 ≤ (N : ℕ) →
      (∫⁻ X, ENNReal.ofReal (intervalCount a b X ^ r) ∂periodicSpatialLaw p N) ≤
        ENNReal.ofReal C := by
  by_cases hab : a < b
  · obtain ⟨C, hC, hb⟩ := periodic_spatial_count_moment_bound p (b - a) r (sub_pos.mpr hab) hr
    refine ⟨C, hC, fun N hN => ?_⟩
    rw [lintegral_intervalCount_rpow_of_stationary _ (periodicSpatialLaw_stationary p N hN)]
    exact hb N hN
  · refine ⟨1, zero_lt_one, fun N _ => ?_⟩
    have he (X : LineConfiguration) : intervalCount a b X = 0 := by
      simp [intervalCount, count, Ioc_eq_empty hab]
    simp only [he, Real.zero_rpow hr.ne', ENNReal.ofReal_zero, lintegral_zero]
    exact bot_le

/-- Stationarity of the inversion candidate from the precise weak-gap-limit
clause. Its mean, shift invariance and divergent sums are supplied by limit theorems. -/
theorem limiting_suspension_stationary_from_gap_limit_internal
    (p : Parameters) (q : ProbabilityMeasure (ℤ → Ioi (0 : ℝ)))
    (hq : Tendsto (fun n : ℕ => periodicGapLaw p n.succPNat) atTop (𝓝 q)) :
    ∀ t : ℝ,
      (gapSuspensionMeasure (reconstructionGapMeasure q.toMeasure)).map (translateConfiguration t) =
        gapSuspensionMeasure (reconstructionGapMeasure q.toMeasure) := by
  let V : ℕ → ℕ+ := fun n => (n + 1).succPNat
  have hV : ∀ n, 2 ≤ (V n : ℕ) := by intro n; simp [V]
  have hVtop : Tendsto (fun n => (V n : ℕ)) atTop atTop := by
    simpa only [V, Nat.succPNat_coe, Nat.add_assoc, one_add_one_eq_two] using tendsto_add_atTop_nat 2
  have hqV : Tendsto (fun n => periodicGapLaw p (V n)) atTop (𝓝 q) :=
    (tendsto_add_atTop_iff_nat 1).mpr hq
  have hshift (a : ℤ) : q.toMeasure.map (fun y j => y (j + a)) = q.toMeasure := by
    have h := congrArg ProbabilityMeasure.toMeasure (periodicGapLaw_limit_shift p V hV q hqV a)
    rw [ProbabilityMeasure.toMeasure_map] at h
    change q.toMeasure.map (fun y j => y (a + j)) = _ at h
    simpa only [add_comm] using h
  have havg := periodicGapLaw_limit_averages p V hV hVtop q hqV
  have hdiv : ∀ᵐ y ∂q.toMeasure,
      Tendsto (fun k : ℕ => ∑ j ∈ Finset.range k, (y (0 + (j : ℤ)) : ℝ)) atTop atTop ∧
      Tendsto (fun k : ℕ => ∑ j ∈ Finset.range k, (y (-(k : ℤ) + (j : ℤ)) : ℝ)) atTop atTop := by
    filter_upwards [havg] with y hy
    exact ⟨gapSequenceSpan_diverges_of_average_internal y (fun _ => 0) hy.1,
      gapSequenceSpan_diverges_of_average_internal y (fun k => -(k : ℤ)) hy.2⟩
  obtain ⟨P, hP, hstat, _⟩ := palm_inversion_from_gap_limit_internal q hshift
    (periodicGapLaw_limit_mean p V hV q hqV) hdiv
  simpa only [IsStationary, hP] using hstat

/-- See the proof of Corollary 1.1 in the paper: every bounded interval
has every positive real moment under the limiting suspension, from the
weak gap convergence alone. -/
theorem limiting_suspension_interval_count_moments_from_gap_limit_internal
    (p : Parameters) (q : ProbabilityMeasure (ℤ → Ioi (0 : ℝ)))
    (hq : Tendsto (fun n : ℕ => periodicGapLaw p n.succPNat) atTop (𝓝 q))
    (a b r : ℝ) (hr : 0 < r) :
    ∃ C : ℝ, 0 < C ∧
      (∫⁻ X, ENNReal.ofReal (intervalCount a b X ^ r)
        ∂gapSuspensionMeasure (reconstructionGapMeasure q.toMeasure)) ≤ ENNReal.ofReal C := by
  by_cases hab : a < b
  · obtain ⟨C, hC, hb⟩ := (limiting_suspension_count_moments_from_gap_limit_internal p q hq).2
      (b - a) r (sub_pos.mpr hab) hr
    refine ⟨C, hC, ?_⟩
    rw [lintegral_intervalCount_rpow_of_stationary _
      (limiting_suspension_stationary_from_gap_limit_internal p q hq)]
    exact hb
  · refine ⟨1, zero_lt_one, ?_⟩
    have he (X : LineConfiguration) : intervalCount a b X = 0 := by
      simp [intervalCount, count, Ioc_eq_empty hab]
    simp only [he, Real.zero_rpow hr.ne', ENNReal.ofReal_zero, lintegral_zero]
    exact bot_le

/-- Local convergence of the periodic law from the exact microscopic local-TV
conclusion and the fixed-window identification of Subsection 2.2. -/
theorem periodic_localConverges_from_microscopic_internal
    (p : Parameters) (P : PointProcess) (hlocal : LocalConverges (microscopicLaw p) P) :
    LocalConverges (periodicSpatialLaw p) P := by
  have hwindow := periodicSpatialLaw_restrict_eq_microscopicLaw p
  have (N : ℕ+) : IsProbabilityMeasure (microscopicLaw p N) := hlocal.choose N
  have (N : ℕ+) : IsProbabilityMeasure (periodicSpatialLaw p N) := periodicSpatialLaw_probability p N
  refine ⟨fun N => periodicSpatialLaw_probability p N, fun R hR => ?_⟩
  have ht := hlocal.choose_spec R hR
  have hN : ∀ᶠ n : ℕ in atTop, 4 * R < (n.succPNat : ℝ) := by
    filter_upwards [(tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually (eventually_gt_atTop (4 * R))]
      with n hn
    simp only [Nat.succPNat_coe, Nat.cast_succ]
    linarith
  apply ht.congr'
  filter_upwards [hN] with n hn
  change totalVariation ((microscopicLaw p n.succPNat).map (restrictConfiguration (Icc (-R) R)))
      ((P : Measure LineConfiguration).map (restrictConfiguration (Icc (-R) R))) =
    totalVariation ((periodicSpatialLaw p n.succPNat).map (restrictConfiguration (Icc (-R) R)))
      ((P : Measure LineConfiguration).map (restrictConfiguration (Icc (-R) R)))
  simp only [hwindow n.succPNat R hn]

/-- The moment convergence in the proof of Corollary 1.1 assumes weak gap
convergence, microscopic local total variation convergence and uniqueness
of the limit. The finite periodic/microscopic window identity is the one
in Subsection 2.2. The conclusion includes all positive real-order moments
on every bounded interval and convergence of the first two moments of the
periodic finite process. -/
theorem hyper_riesz_count_moments_from_predecessors_internal
    (p : Parameters) (q : ProbabilityMeasure (ℤ → Ioi (0 : ℝ)))
    (hq : Tendsto (fun n : ℕ => periodicGapLaw p n.succPNat) atTop (𝓝 q))
    (P : PointProcess)
    (hP : (P : Measure LineConfiguration) =
      gapSuspensionMeasure (reconstructionGapMeasure q.toMeasure))
    (hlocal : LocalConverges (microscopicLaw p) P)
    (hunique : UniqueRieszLimit p) :
    ∃ h : UniqueRieszLimit p,
      (∀ (R r : ℝ), 0 < R → 0 < r → ∃ C : ℝ, 0 < C ∧
        (∀ N : ℕ+, 8 * R + 8 ≤ (N : ℝ) →
          (∫⁻ X, ENNReal.ofReal (intervalCount 0 R X ^ r) ∂periodicSpatialLaw p N) ≤
            ENNReal.ofReal C) ∧
        (∫⁻ X, ENNReal.ofReal (intervalCount 0 R X ^ r) ∂limitingRieszProcess p h) ≤
          ENNReal.ofReal C) ∧
      (∀ (a b r : ℝ), 0 < r → ∃ C : ℝ, 0 < C ∧
        (∀ N : ℕ+, 2 ≤ (N : ℕ) →
          (∫⁻ X, ENNReal.ofReal (intervalCount a b X ^ r) ∂periodicSpatialLaw p N) ≤
            ENNReal.ofReal C) ∧
        (∫⁻ X, ENNReal.ofReal (intervalCount a b X ^ r) ∂limitingRieszProcess p h) ≤
          ENNReal.ofReal C) ∧
      (∀ a b : ℝ,
        (∀ N : ℕ+, 2 ≤ (N : ℕ) →
          Integrable (intervalCount a b) (periodicSpatialLaw p N) ∧
          Integrable (fun X => intervalCount a b X ^ 2) (periodicSpatialLaw p N)) ∧
        Integrable (intervalCount a b) (limitingRieszProcess p h : Measure LineConfiguration) ∧
        Integrable (fun X => intervalCount a b X ^ 2)
          (limitingRieszProcess p h : Measure LineConfiguration) ∧
        Tendsto (fun n : ℕ => ∫ X, intervalCount a b X ∂periodicSpatialLaw p n.succPNat)
          atTop (𝓝 (∫ X, intervalCount a b X ∂limitingRieszProcess p h)) ∧
        Tendsto (fun n : ℕ => ∫ X, intervalCount a b X ^ 2 ∂periodicSpatialLaw p n.succPNat)
          atTop (𝓝 (∫ X, intervalCount a b X ^ 2 ∂limitingRieszProcess p h))) := by
  have hselected : LocalConverges (microscopicLaw p) (limitingRieszProcess p hunique) :=
    Classical.choose_spec hunique.exists
  have hselectedEq : limitingRieszProcess p hunique = P :=
    hunique.unique hselected hlocal
  have hall (a b r : ℝ) (hr : 0 < r) : ∃ C : ℝ, 0 < C ∧
      (∀ N : ℕ+, 2 ≤ (N : ℕ) →
        (∫⁻ X, ENNReal.ofReal (intervalCount a b X ^ r) ∂periodicSpatialLaw p N) ≤
          ENNReal.ofReal C) ∧
      (∫⁻ X, ENNReal.ofReal (intervalCount a b X ^ r) ∂P) ≤ ENNReal.ofReal C := by
    obtain ⟨C, hC, hfinite⟩ := periodic_spatial_interval_count_moment_bound p a b r hr
    obtain ⟨D, hD, hlimit⟩ :=
      limiting_suspension_interval_count_moments_from_gap_limit_internal p q hq a b r hr
    refine ⟨max C D, lt_of_lt_of_le hC (le_max_left _ _),
      fun N hN => (hfinite N hN).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)), ?_⟩
    rw [hP]
    exact hlimit.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))
  refine ⟨hunique, ?_, ?_, ?_⟩
  · intro R r hR hr
    obtain ⟨C, hC, hf, hl⟩ := hall 0 R r hr
    refine ⟨C, hC, fun N hN => hf N ?_, ?_⟩
    · exact_mod_cast (show (2 : ℝ) ≤ (N : ℝ) by linarith)
    · simpa only [hselectedEq] using hl
  · simpa only [hselectedEq] using hall
  · intro a b
    obtain ⟨D, hD, hf, hl⟩ := hall a b 4 (by norm_num)
    have ht := intervalCount_first_second_moments_tendsto_internal
      (periodicSpatialLaw p) P (periodic_localConverges_from_microscopic_internal p P hlocal)
      a b D hD.le (by simpa only [Real.rpow_ofNat] using hf)
      (by simpa only [Real.rpow_ofNat] using hl)
    simpa only [hselectedEq] using ht

end Riesz2
