/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.GapLimit
public import Riesz2.Thermodynamic.ConfigurationOperations
public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite

/-!
# Local reconstruction events and their length-weighted tails

The event in the proof of Theorem 3 uses the actual two-sided gap carrier and spans of
the gap-limit construction.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2

local notation "Gaps" => (ℤ → Ioi (0 : ℝ))

/-- Rooted enumerations with equal consecutive increments on a finite interval
agree throughout that interval. This is the deterministic locality argument,
independent of any chosen encoding of gap reconstruction. -/
theorem rooted_positions_eq_of_increments_eq
    (z w : ℤ → ℝ) (hz : z 0 = 0) (hw : w 0 = 0) (a b : ℤ)
    (ha : a ≤ 0) (hb : 0 ≤ b)
    (hinc : ∀ j ∈ Finset.Ico a b, z (j + 1) - z j = w (j + 1) - w j) :
    ∀ i : ℤ, a ≤ i → i ≤ b → z i = w i := by
  intro i
  induction i using Int.induction_on with
  | zero => intro _ _; exact hz.trans hw.symm
  | succ i hi =>
    intro hai hib
    have hprev := hi (by omega) (by omega)
    have hstep := hinc (i : ℤ) (by simp only [Finset.mem_Ico]; omega)
    linarith
  | pred i hi =>
    intro hai hib
    have hprev := hi (by omega) (by omega)
    have hstep := hinc (-(i : ℤ) - 1) (by simp only [Finset.mem_Ico]; omega)
    rw [sub_add_cancel] at hstep
    linarith

/-- An ordered configuration bracketed strictly outside a closed window is
determined by its intervening labels. The inequalities include both window
endpoints and permit offsets at either endpoint of the distinguished gap. -/
theorem mem_translated_window_iff_finite_labels
    (C : LineConfiguration) (z : ℤ → ℝ) (hz : Monotone z)
    (hC : C.val = range z) (a b : ℤ) (R u : ℝ)
    (ha : z a - u < -R) (hb : R < z b - u) (x : ℝ) :
    x ∈ (restrictConfiguration (Icc (-R) R) (translateConfiguration u C)).val ↔
      ∃ i ∈ Finset.Ioo a b, z i - u = x ∧ x ∈ Icc (-R) R := by
  change (x + u ∈ C.val ∧ x ∈ Icc (-R) R) ↔ _
  rw [hC]
  constructor
  · rintro ⟨⟨i, hi⟩, hx⟩
    refine ⟨i, ?_, by linarith, hx⟩
    simp only [Finset.mem_Ioo]
    constructor
    · by_contra h
      have hzi := hz (le_of_not_gt h)
      have := hx.1
      linarith
    · by_contra h
      have hzi := hz (le_of_not_gt h)
      have := hx.2
      linarith
  · rintro ⟨i, _, hi, hx⟩
    exact ⟨⟨i, by linarith⟩, hx⟩

/-- Finite-list agreement identifies closed-window restrictions of two ordered
configurations once the same labels bracket the window in both enumerations. -/
theorem translated_windows_eq_of_finite_labels
    (C D : LineConfiguration) (z w : ℤ → ℝ) (hz : Monotone z) (hw : Monotone w)
    (hC : C.val = range z) (hD : D.val = range w) (a b : ℤ) (R u : ℝ)
    (hza : z a - u < -R) (hzb : R < z b - u)
    (hwa : w a - u < -R) (hwb : R < w b - u)
    (heq : ∀ i ∈ Finset.Ioo a b, z i = w i) :
    restrictConfiguration (Icc (-R) R) (translateConfiguration u C) =
      restrictConfiguration (Icc (-R) R) (translateConfiguration u D) := by
  apply Subtype.ext
  ext x
  rw [mem_translated_window_iff_finite_labels C z hz hC a b R u hza hzb,
    mem_translated_window_iff_finite_labels D w hw hD a b R u hwa hwb]
  constructor <;> rintro ⟨i, hi, hix, hx⟩
  · exact ⟨i, hi, (heq i hi) ▸ hix, hx⟩
  · exact ⟨i, hi, (heq i hi).symm ▸ hix, hx⟩


/-- See the proof of Theorem 3 in the paper: the two spans which bracket a
closed radius-`R` window for every offset in the distinguished gap. The event
has its literal meaning also at lengths zero and one. -/
def localReconstructionEvent (m : ℕ) (R : ℝ) : Set Gaps :=
  {y | R < gapSequenceSpan y (-(m : ℤ)) m ∧ R < gapSequenceSpan y 1 (m - 1)}

/-- Telescoping identifies a finite gap span in any enumeration with those
increments. -/
theorem gapSequenceSpan_eq_position_sub_internal
    (y : Gaps) (z : ℤ → ℝ) (hstep : ∀ i, z (i + 1) = z i + (y i : ℝ))
    (a : ℤ) (k : ℕ) : gapSequenceSpan y a k = z (a + (k : ℤ)) - z a := by
  induction k with
  | zero => simp [gapSequenceSpan]
  | succ k hk =>
    change (∑ j ∈ Finset.range (k + 1), (y (a + (j : ℤ)) : ℝ)) = _
    rw [Finset.sum_range_succ]
    change gapSequenceSpan y a k + (y (a + (k : ℤ)) : ℝ) = _
    rw [hk, show a + ((k + 1 : ℕ) : ℤ) = (a + (k : ℤ)) + 1 by omega, hstep]
    ring

/-- Deterministic part of the proof of Theorem 3 as a
generic reconstruction interface. The hypotheses specify rooted enumerations
of the actual configurations, rather than postulating finite determination.
Increments on precisely the block `[-m,m)` determine the closed-window law. -/
theorem convergence_local_block_determination_internal
    (y y' : Gaps) (C D : LineConfiguration) (z w : ℤ → ℝ)
    (hC : C.val = range z) (hD : D.val = range w)
    (hz0 : z 0 = 0) (hw0 : w 0 = 0)
    (hzstep : ∀ i, z (i + 1) = z i + (y i : ℝ))
    (hwstep : ∀ i, w (i + 1) = w i + (y' i : ℝ))
    (m : ℕ) (hm : 2 ≤ m) (R u : ℝ)
    (hy : y ∈ localReconstructionEvent m R)
    (hu : 0 ≤ u) (huy : u ≤ (y 0 : ℝ))
    (heq : ∀ j ∈ Finset.Ico (-(m : ℤ)) (m : ℤ), y j = y' j) :
    restrictConfiguration (Icc (-R) R) (translateConfiguration u C) =
      restrictConfiguration (Icc (-R) R) (translateConfiguration u D) := by
  have hz : StrictMono z := strictMono_int_of_lt_succ fun i => by
    rw [hzstep]
    exact lt_add_of_pos_right _ (y i).property
  have hw : StrictMono w := strictMono_int_of_lt_succ fun i => by
    rw [hwstep]
    exact lt_add_of_pos_right _ (y' i).property
  have hpositions := rooted_positions_eq_of_increments_eq z w hz0 hw0
    (-(m : ℤ)) (m : ℤ) (by omega) (by omega) (fun j hj => by
      rw [hzstep, hwstep, heq j hj]; ring)
  have hleft := gapSequenceSpan_eq_position_sub_internal y z hzstep (-(m : ℤ)) m
  rw [neg_add_cancel, hz0, zero_sub] at hleft
  have hright := gapSequenceSpan_eq_position_sub_internal y z hzstep 1 (m - 1)
  rw [show (1 : ℤ) + ((m - 1 : ℕ) : ℤ) = (m : ℤ) by omega] at hright
  have hz1 : z 1 = (y 0 : ℝ) := by simpa only [hz0, zero_add] using hzstep 0
  rw [hz1] at hright
  have hza : z (-(m : ℤ)) - u < -R := by
    have h := hy.1
    rw [hleft] at h
    linarith
  have hzb : R < z (m : ℤ) - u := by
    have h := hy.2
    rw [hright] at h
    linarith
  apply translated_windows_eq_of_finite_labels C D z w hz.monotone hw.monotone hC hD
    (-(m : ℤ)) (m : ℤ) R u hza hzb
  · rw [← hpositions (-(m : ℤ)) le_rfl (by omega)]
    exact hza
  · rw [← hpositions (m : ℤ) (by omega) le_rfl]
    exact hzb
  · intro i hi
    simp only [Finset.mem_Ioo] at hi
    exact hpositions i hi.1.le hi.2.le

/-- Both bracketing spans are continuous, so the reconstruction event is Borel. -/
theorem measurableSet_localReconstructionEvent (m : ℕ) (R : ℝ) :
    MeasurableSet (localReconstructionEvent m R) :=
  (measurableSet_lt measurable_const (continuous_gapSequenceSpan _ _).measurable).inter
    (measurableSet_lt measurable_const (continuous_gapSequenceSpan _ _).measurable)

/-- The one-gap boundary cannot bracket a positive window on the right. -/
theorem localReconstructionEvent_one (R : ℝ) (hR : 0 ≤ R) :
    localReconstructionEvent 1 R = ∅ := by
  ext y
  simp only [localReconstructionEvent, mem_ofPred_eq, gapSequenceSpan,
    Nat.sub_self, Finset.range_zero, Finset.sum_empty, mem_empty_iff_false,
    iff_false, not_and, not_lt]
  exact fun _ => hR

/-- Boundary check for the proof of Theorem 3: for unit
gaps the shorter, right-hand span is the exact strict threshold. -/
theorem localReconstructionEvent_unit (m : ℕ) (R : ℝ) :
    (fun _ : ℤ => (⟨1, zero_lt_one⟩ : Ioi (0 : ℝ))) ∈ localReconstructionEvent m R ↔
      R < ((m - 1 : ℕ) : ℝ) := by
  simp only [localReconstructionEvent, mem_ofPred_eq, gapSequenceSpan,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  constructor
  · exact And.right
  · intro h
    exact ⟨h.trans_le (by exact_mod_cast Nat.sub_le m 1), h⟩

/-- A sublinear rigidity threshold is eventually smaller than the deficit of
any span whose length stays below a fixed radius. -/
theorem eventually_short_span_is_deviation_internal (α R : ℝ) (hα : α < 1) :
    ∀ᶠ k : ℕ in atTop, ∀ (y : Gaps) (i : ℤ),
      gapSequenceSpan y i k ≤ R → (k : ℝ) ^ α < |gapSequenceSpan y i k - k| := by
  have ht : Tendsto (fun k : ℕ => (k : ℝ) ^ (α - 1)) atTop (𝓝 0) := by
    simpa only [neg_sub, Function.comp_def] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hα)).comp tendsto_natCast_atTop_atTop
  have hR := (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop)
    |>.eventually (eventually_gt_atTop (2 * R))
  filter_upwards [ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2),
    hR, eventually_ge_atTop 1] with k hk hkR hk1 y i hspan
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk1)
  have hp : (k : ℝ) ^ α < (k : ℝ) / 2 := by
    rw [Real.rpow_sub hkpos, Real.rpow_one] at hk
    linarith [(div_lt_iff₀ hkpos).mp hk]
  have habs := le_abs_self (-(gapSequenceSpan y i k - k))
  rw [abs_neg] at habs
  linarith

/-- Cauchy--Schwarz in the nonnegative-integral convention used for the
length-weighted exceptional events. -/
theorem length_weighted_event_le_internal (μ : Measure Gaps) [IsFiniteMeasure μ]
    (D b : ℝ) (hD : 0 ≤ D) (hb : 0 ≤ b)
    (hmom : (∫⁻ y, ENNReal.ofReal ((y 0 : ℝ) ^ (2 : ℝ)) ∂μ) ≤ ENNReal.ofReal D)
    (E : Set Gaps) (hE : MeasurableSet E) (hprob : μ E ≤ ENNReal.ofReal b) :
    (∫⁻ y in E, ENNReal.ofReal (y 0 : ℝ) ∂μ) ≤
      ENNReal.ofReal (Real.sqrt D * Real.sqrt b) := by
  have hy : Measurable (fun y : Gaps => (y 0 : ℝ)) :=
    measurable_subtype_coe.comp (measurable_pi_apply 0)
  have habs (y : Gaps) : |(y 0 : ℝ)| = (y 0 : ℝ) := abs_of_pos (y 0).property
  obtain ⟨hi, hbound⟩ := MomentEvent.integrable_rpow_abs_and_integral_le_of_lintegral_le
    (μ := μ) (p := 2) hy hD (by simpa only [habs] using hmom)
  have hisq : Integrable (fun y : Gaps => (y 0 : ℝ) ^ 2) μ := by
    simpa only [habs, Real.rpow_two] using hi
  have hsq : (∫ y : Gaps, (y 0 : ℝ) ^ 2 ∂μ) ≤ D := by
    simpa only [habs, Real.rpow_two] using hbound
  have hcs := MomentEvent.abs_integral_mul_le_sqrt_mul_sqrt
    (g := fun _ : Gaps => (1 : ℝ)) (M := 1) measurable_const hy
    zero_le_one (fun _ => by norm_num) hisq hE
  simp only [one_mul] at hcs
  have hreal : μ.real E ≤ b := ENNReal.toReal_le_of_le_ofReal hb hprob
  have hle := hcs.trans (mul_le_mul (Real.sqrt_le_sqrt hsq)
    (Real.sqrt_le_sqrt hreal) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hiY := MomentEvent.integrable_of_integrable_sq hy hisq
  rw [← ofReal_integral_eq_lintegral_ofReal hiY.integrableOn
    (ae_of_all _ fun y => (y 0).property.le)]
  exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans hle)

/-- The two failed bracketing conditions lie in their two span-deviation events.
This is an internal probability estimate for the proof of Theorem 3. -/
theorem localReconstruction_compl_measure_le_internal
    (μ : Measure Gaps) (m : ℕ) (R α b₁ b₂ : ℝ)
    (h₁ : ∀ y : Gaps, gapSequenceSpan y (-(m : ℤ)) m ≤ R →
      (m : ℝ) ^ α < |gapSequenceSpan y (-(m : ℤ)) m - m|)
    (h₂ : ∀ y : Gaps, gapSequenceSpan y 1 (m - 1) ≤ R →
      ((m - 1 : ℕ) : ℝ) ^ α < |gapSequenceSpan y 1 (m - 1) - (m - 1 : ℕ)|)
    (hb₁ : μ {y | (m : ℝ) ^ α < |gapSequenceSpan y (-(m : ℤ)) m - m|} ≤
      ENNReal.ofReal b₁)
    (hb₂ : μ {y | ((m - 1 : ℕ) : ℝ) ^ α <
      |gapSequenceSpan y 1 (m - 1) - (m - 1 : ℕ)|} ≤ ENNReal.ofReal b₂) :
    μ (localReconstructionEvent m R)ᶜ ≤ ENNReal.ofReal b₁ + ENNReal.ofReal b₂ := by
  apply (measure_mono (show (localReconstructionEvent m R)ᶜ ⊆
    {y | (m : ℝ) ^ α < |gapSequenceSpan y (-(m : ℤ)) m - m|} ∪
      {y | ((m - 1 : ℕ) : ℝ) ^ α <
        |gapSequenceSpan y 1 (m - 1) - (m - 1 : ℕ)|} from ?_)).trans
      ((measure_union_le _ _).trans (add_le_add hb₁ hb₂))
  intro y hy
  change ¬(R < gapSequenceSpan y (-(m : ℤ)) m ∧ R < gapSequenceSpan y 1 (m - 1)) at hy
  by_cases h : R < gapSequenceSpan y (-(m : ℤ)) m
  · exact Or.inr (h₂ y (le_of_not_gt (fun h' => hy ⟨h, h'⟩)))
  · exact Or.inl (h₁ y (le_of_not_gt h))

/-- Uniform length-weighted tails from a uniform span estimate and second moment.
The index-dependent admissibility relation allows finite periods only when both
spans have length at most half the period. -/
theorem localReconstruction_weighted_tails_internal
    {ι : Type*} (μ : ι → Measure Gaps) [∀ i, IsFiniteMeasure (μ i)]
    (admissible : ℕ → ι → Prop) (α δ C c D R : ℝ)
    (hα : α < 1) (hδ : 0 < δ) (hC : 0 ≤ C) (hc : 0 < c) (hD : 0 ≤ D)
    (hmom : ∀ i, (∫⁻ y, ENNReal.ofReal ((y 0 : ℝ) ^ (2 : ℝ)) ∂μ i) ≤ ENNReal.ofReal D)
    (hdev : ∀ m i, 2 ≤ m → admissible m i →
      ∀ k ∈ ({m, m - 1} : Finset ℕ), ∀ a : ℤ,
        μ i {y | (k : ℝ) ^ α < |gapSequenceSpan y a k - k|} ≤
          ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ δ))) :
    Tendsto (fun m : ℕ => ⨆ i : {i : ι // admissible m i},
      ∫⁻ y in (localReconstructionEvent m R)ᶜ,
        ENNReal.ofReal (y 0 : ℝ) ∂μ i.val) atTop (𝓝 0) := by
  let e : ℕ → ℝ := fun k => C * Real.exp (-c * (k : ℝ) ^ δ)
  have he0 (k : ℕ) : 0 ≤ e k := mul_nonneg hC (Real.exp_pos _).le
  have het : Tendsto e atTop (𝓝 0) := by
    have h := (StretchedCutoff.tendsto_power_mul_exp hδ hc 0).comp
      tendsto_natCast_atTop_atTop
    simpa only [e, Function.comp_def, Real.rpow_zero, one_mul, mul_zero] using h.const_mul C
  have hpred : Tendsto (fun m : ℕ => m - 1) atTop atTop :=
    tendsto_atTop.mpr fun b => eventually_atTop.mpr ⟨b + 1, fun m hm => by omega⟩
  have herror : Tendsto (fun m : ℕ =>
      ENNReal.ofReal (Real.sqrt D * Real.sqrt (e m + e (m - 1)))) atTop (𝓝 0) := by
    have hsum : Tendsto (fun m => e m + e (m - 1)) atTop (𝓝 0) := by
      simpa only [add_zero, Function.comp_def] using het.add (het.comp hpred)
    have ht := (Real.continuous_sqrt.tendsto 0).comp hsum
    have ht' : Tendsto (fun m => Real.sqrt D * Real.sqrt (e m + e (m - 1)))
        atTop (𝓝 0) := by
      simpa only [Real.sqrt_zero, mul_zero, Function.comp_def] using ht.const_mul (Real.sqrt D)
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp ht'
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds herror
    (Eventually.of_forall fun _ => bot_le)
  have hs := eventually_short_span_is_deviation_internal α R hα
  filter_upwards [hs, hpred.eventually hs, eventually_ge_atTop 2] with m hm hm' hm2
  apply iSup_le
  intro i
  apply length_weighted_event_le_internal (μ i.val) D (e m + e (m - 1))
    hD (add_nonneg (he0 _) (he0 _)) (hmom _)
    (localReconstructionEvent m R)ᶜ (measurableSet_localReconstructionEvent m R).compl
  rw [ENNReal.ofReal_add (he0 _) (he0 _)]
  exact localReconstruction_compl_measure_le_internal (μ i.val) m R α _ _
    (fun y => hm y _) (fun y => hm' y _)
    (hdev m i.val hm2 i.property m (by simp) _)
    (hdev m i.val hm2 i.property (m - 1) (by simp) _)

/-- The finite-volume weighted-tail assertion of the proof of Theorem 3, with the supremum over exactly `N ≥ 2*m`. -/
theorem convergence_local_block_finite_weighted_tails (p : Parameters) (R : ℝ) :
    Tendsto (fun m : ℕ => ⨆ N : {N : ℕ+ // 2 * m ≤ (N : ℕ)},
      ∫⁻ y in (localReconstructionEvent m R)ᶜ,
        ENNReal.ofReal (y 0 : ℝ) ∂periodicGapLaw p N.val) atTop (𝓝 0) := by
  obtain ⟨η₀, hη₀, hsmall, hrigidity⟩ := periodicGapLaw_finite_rigidity p
  obtain ⟨C, c, hC, hc, hb⟩ := hrigidity (η₀ / 2) (half_pos hη₀) (half_lt_self hη₀)
  obtain ⟨D, hD, hmom⟩ := periodicGapLaw_moment_bound p 2 (by norm_num)
  have hDall : ∀ N : ℕ+,
      (∫⁻ y : Gaps, ENNReal.ofReal ((y 0 : ℝ) ^ (2 : ℝ)) ∂periodicGapLaw p N) ≤
        ENNReal.ofReal (max D 1) := by
    intro N
    by_cases hN : 2 ≤ (N : ℕ)
    · exact ((le_add_right le_rfl).trans (hmom N hN 0)).trans
        (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    · have hN1 : N = 1 := PNat.eq (by have := N.pos; simp only [PNat.val_ofNat]; omega)
      subst N
      have hy : Measurable (fun y : Gaps => ENNReal.ofReal ((y 0 : ℝ) ^ (2 : ℝ))) :=
        ((measurable_subtype_coe.comp (measurable_pi_apply 0)).pow_const (2 : ℝ)).ennreal_ofReal
      rw [lintegral_periodicGapLaw p 1 hy]
      have := gibbsMeasure_probability p 1
      simp only [periodicGapSequence_one, Real.one_rpow, ENNReal.ofReal_one,
        lintegral_const, measure_univ, mul_one]
      exact_mod_cast ENNReal.ofReal_le_ofReal (le_max_right D 1)
  apply localReconstruction_weighted_tails_internal
    (fun N : ℕ+ => (periodicGapLaw p N).toMeasure) (fun m N => 2 * m ≤ (N : ℕ))
    (min p.val.2 1 / 2 + η₀ / 2) (η₀ / 2 / (4 * (p.val.2 + 2))) C c (max D 1) R
    (by linarith) (by have := p.property.2.1; positivity) hC.le hc
    (le_trans hD.le (le_max_left _ _)) hDall
  intro m N hm hN k hk a
  have hk' : k = m ∨ k = m - 1 := by simpa using hk
  apply hb N (by omega) k (by rcases hk' with rfl | rfl <;> omega) (by
    rcases hk' with rfl | rfl <;> omega) a

/-- The limiting weighted-tail assertion of the proof of Theorem 3. It assumes weak convergence of the gap laws. -/
theorem convergence_local_block_limit_weighted_tails_from_gap_limit_internal
    (p : Parameters) (q : ProbabilityMeasure Gaps)
    (hq : Tendsto (fun n : ℕ => periodicGapLaw p n.succPNat) atTop (𝓝 q)) (R : ℝ) :
    Tendsto (fun m : ℕ => ∫⁻ y in (localReconstructionEvent m R)ᶜ,
      ENNReal.ofReal (y 0 : ℝ) ∂q) atTop (𝓝 0) := by
  let V : ℕ → ℕ+ := fun n => (n + 1).succPNat
  have hV : ∀ n, 2 ≤ (V n : ℕ) := by intro n; simp [V]
  have hVtop : Tendsto (fun n => (V n : ℕ)) atTop atTop := by
    simpa only [V, Nat.succPNat_coe, Nat.add_assoc, one_add_one_eq_two] using
      tendsto_add_atTop_nat 2
  have hqV : Tendsto (fun n => periodicGapLaw p (V n)) atTop (𝓝 q) :=
    (tendsto_add_atTop_iff_nat 1).mpr hq
  obtain ⟨η₀, hη₀, hsmall, hrigidity⟩ := periodicGapLaw_limit_rigidity p V hV hVtop q hqV
  obtain ⟨C, c, hC, hc, hb⟩ := hrigidity (η₀ / 2) (half_pos hη₀) (half_lt_self hη₀)
  obtain ⟨D, hD, _, hmom⟩ := periodicGapLaw_limit_moment_bound p V hV q hqV 2 (by norm_num)
  have ht := localReconstruction_weighted_tails_internal
    (fun _ : Unit => q.toMeasure) (fun _ _ => True)
    (min p.val.2 1 / 2 + η₀ / 2) (η₀ / 2 / (4 * (p.val.2 + 2))) C c D R
    (by linarith) (by have := p.property.2.1; positivity) hC.le hc hD.le
    (fun _ => (le_add_right le_rfl).trans (hmom 0))
    (fun m _ hm _ k hk a => hb k (by
      have hk' : k = m ∨ k = m - 1 := by simpa using hk
      rcases hk' with rfl | rfl <;> omega) a)
  simpa only [iSup_subtype, iSup_true, iSup_const] using ht

end Riesz2
