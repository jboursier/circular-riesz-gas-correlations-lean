/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.ExceptionalEvent
public import Riesz2.DecayShort.LocalLawPart3

/-!
# Gap and block deviations for the exceptional event

The large-block and small-block splitting in Subsection 4.5.
The estimates use the physical short-range law and its local law.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace Riesz2.DecayShort.ExceptionalEvent

/-- Internal small-block step of Subsection 4.5. Positivity makes a
large negative deviation impossible. A positive deviation forces one large
coordinate. The threshold retains the square-root block factor. -/
theorem internal_small_block_large_coordinate {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (y : ι → ℝ) (hy : ∀ i ∈ J, 0 < y i)
    {R : ℝ} (hR : 0 < R) (hk : 0 < J.card) (hkR : (J.card : ℝ) ≤ R)
    (hdev : R * (J.card : ℝ) ^ (1 / 2 : ℝ) <
      |(∑ i ∈ J, y i) - (J.card : ℝ)|) :
    ∃ i ∈ J, R ^ (1 / 2 : ℝ) ≤ y i := by
  have hk1 : (1 : ℝ) ≤ J.card := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < J.card := by exact_mod_cast hk
  have hroot : (J.card : ℝ) ≤ R * (J.card : ℝ) ^ (1 / 2 : ℝ) := by
    have hr : 1 ≤ (J.card : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow hk1 (by norm_num)
    nlinarith
  have hsum : 0 ≤ ∑ i ∈ J, y i := Finset.sum_nonneg fun i hi => (hy i hi).le
  have hpos : R * (J.card : ℝ) ^ (1 / 2 : ℝ) < ∑ i ∈ J, y i := by
    rcases (lt_abs.mp hdev) with h | h <;> linarith
  by_contra hn
  have hi : ∀ i ∈ J, y i < R ^ (1 / 2 : ℝ) := by
    simpa only [not_exists, not_and, not_le] using hn
  have hsmall : (∑ i ∈ J, y i) ≤ (J.card : ℝ) * R ^ (1 / 2 : ℝ) := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using
      (Finset.sum_le_sum fun i hiJ => (hi i hiJ).le)
  have hsqrt : (J.card : ℝ) ^ (1 / 2 : ℝ) ≤ R ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow hk0.le hkR (by norm_num)
  have hsquare : ((J.card : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = J.card := by
    simpa only [Real.sqrt_eq_rpow] using Real.sq_sqrt hk0.le
  have hRroot : (R ^ (1 / 2 : ℝ)) ^ 2 = R := by
    simpa only [Real.sqrt_eq_rpow] using Real.sq_sqrt hR.le
  have hprod : (J.card : ℝ) * R ^ (1 / 2 : ℝ) ≤
      R * (J.card : ℝ) ^ (1 / 2 : ℝ) := by
    calc
      _ = ((J.card : ℝ) ^ (1 / 2 : ℝ)) ^ 2 * R ^ (1 / 2 : ℝ) :=
        congrArg (fun t => t * R ^ (1 / 2 : ℝ)) hsquare.symm
      _ = (J.card : ℝ) ^ (1 / 2 : ℝ) *
          ((J.card : ℝ) ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ)) := by ring
      _ ≤ R ^ (1 / 2 : ℝ) *
          ((J.card : ℝ) ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hsqrt (by positivity)
      _ = (R ^ (1 / 2 : ℝ)) ^ 2 * (J.card : ℝ) ^ (1 / 2 : ℝ) := by ring
      _ = _ := congrArg (fun t => t * (J.card : ℝ) ^ (1 / 2 : ℝ)) hRroot
  linarith

/-- See Subsection 4.5 of the paper, large/small-block probability input.
The exponent is chosen before the compact temperature interval. The estimate
holds for each finite set of gaps of cardinality at most the active size. The simultaneous interval event is obtained by a finite union bound. -/
theorem physical_block_deviation_probability (s h : ℝ) (hs : 1 < s) (hh : 0 < h) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ (N n : ℕ+), 2 ≤ (N : ℕ) →
      ∀ J : Finset (Fin (N : ℕ)), 1 ≤ J.card → J.card ≤ (n : ℕ) → J.card < (N : ℕ) →
        (gibbsMeasure p N) {X | (n : ℝ) ^ h * (J.card : ℝ) ^ (1 / 2 : ℝ) <
          |(∑ i ∈ J, gap X i.val) - (J.card : ℝ)|} ≤
            ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ δ)) := by
  classical
  let η := h / 2
  let α := η / (4 * (s + 2))
  let δ := min (h / 2) (h * α)
  have hη : 0 < η := by dsimp [η]; positivity
  have hα : 0 < α := by dsimp [α]; positivity
  have hδ : 0 < δ := lt_min (by positivity) (mul_pos hh hα)
  refine ⟨δ, hδ, fun βlo βhi hlo hle => ?_⟩
  obtain ⟨A, a, hA, ha, hlocal⟩ := shortRange_localLaw_sets s βlo βhi η hs hlo hle hη
  obtain ⟨B, b, hB, hb, htail, _⟩ := SingleGapTails.single_gap_tails s βlo βhi
    (by linarith) (ne_of_gt hs) hlo hle
  let c := min a b
  have hc : 0 < c := lt_min ha hb
  obtain ⟨K, hK, hpoly⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := 1) (c := c) (c' := c / 2) hδ (by linarith)
  refine ⟨A + B * K + 1, c / 2, by positivity, by positivity, ?_⟩
  intro p hp hpl hph N n hN J hk hkn hkN
  have hprob := gibbsMeasure_probability p N
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hk1 : (1 : ℝ) ≤ J.card := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < J.card := by exact_mod_cast hk
  have hknR : (J.card : ℝ) ≤ n := by exact_mod_cast hkn
  have hnc : (n : ℝ) ^ δ ≤ (n : ℝ) ^ (h / 2) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (min_le_left _ _)
  have hlarge : (n : ℝ) ^ δ ≤ (n : ℝ) ^ (h * α) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (min_le_right _ _)
  by_cases hsplit : (n : ℝ) ^ h ≤ J.card
  · have hthreshold : (J.card : ℝ) ^ (1 / 2 + η) ≤
        (n : ℝ) ^ h * (J.card : ℝ) ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_add hk0]
      have ht : (J.card : ℝ) ^ η ≤ (n : ℝ) ^ h :=
        (Real.rpow_le_rpow hk0.le hknR hη.le).trans
          (Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [η]; linarith))
      nlinarith [Real.rpow_pos_of_pos hk0 (1 / 2 : ℝ)]
    have hmeas : MeasurableSet {x : Fin (N : ℕ) → ℝ |
        (J.card : ℝ) ^ (1 / 2 + η) ≤ |(∑ i ∈ J, x i) - (J.card : ℝ)|} :=
      measurableSet_le measurable_const
        (((Finset.measurable_sum J fun i _ => measurable_pi_apply i).sub measurable_const).abs)
    have hmap := Measure.map_apply (μ := gibbsMeasure p N)
      (show Measurable (@gapVector N) from Riesz1.measurable_gapVector N) hmeas
    have hl := hlocal p hp hpl hph N hN J hk hkN
    change (gibbsMeasure p N).map gapVector _ ≤ _ at hl
    rw [hmap] at hl
    have hexp : c / 2 * (n : ℝ) ^ δ ≤ a * (J.card : ℝ) ^ α := by
      have ht : (n : ℝ) ^ (h * α) ≤ (J.card : ℝ) ^ α := by
        rw [Real.rpow_mul hn0.le]
        exact Real.rpow_le_rpow (by positivity) hsplit hα.le
      have hca : c / 2 ≤ a := by dsimp only [c]; linarith [min_le_left a b, min_le_right a b]
      exact (mul_le_mul_of_nonneg_left (hlarge.trans ht) (by positivity : 0 ≤ c / 2)).trans
        (mul_le_mul_of_nonneg_right hca (by positivity))
    apply (measure_mono (show {X | (n : ℝ) ^ h * (J.card : ℝ) ^ (1 / 2 : ℝ) <
        |(∑ i ∈ J, gap X i.val) - (J.card : ℝ)|} ⊆ _ from fun X hX =>
          hthreshold.trans hX.le)).trans hl |>.trans
    apply ENNReal.ofReal_le_ofReal
    have he := Real.exp_le_exp.mpr (neg_le_neg hexp)
    simpa only [α, neg_mul] using (mul_le_mul_of_nonneg_left he hA.le).trans
      (mul_le_mul_of_nonneg_right (by nlinarith : A ≤ A + B * K + 1) (Real.exp_pos _).le)
  · have hsub : {X : Riesz1.Configuration N |
        (n : ℝ) ^ h * (J.card : ℝ) ^ (1 / 2 : ℝ) <
          |(∑ i ∈ J, gap X i.val) - (J.card : ℝ)|} ⊆
        ⋃ i ∈ J, {X | (n : ℝ) ^ (h / 2) ≤ gap X i.val} := by
      intro X hX
      obtain ⟨i, hi, hgi⟩ := internal_small_block_large_coordinate J
        (fun i => gap X i.val) (fun i _ => Riesz1.gap_pos X i.val)
        (Real.rpow_pos_of_pos hn0 h) hk (le_of_lt (lt_of_not_ge hsplit)) hX
      refine mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, ?_⟩⟩
      have he : ((n : ℝ) ^ h) ^ (1 / 2 : ℝ) = (n : ℝ) ^ (h / 2) := by
        rw [← Real.rpow_mul hn0.le]
        congr 1
        ring
      rwa [he] at hgi
    have ht (i : Fin (N : ℕ)) : (gibbsMeasure p N) {X | (n : ℝ) ^ (h / 2) ≤ gap X i.val} ≤
        ENNReal.ofReal (B * Real.exp (-c * (n : ℝ) ^ δ)) := by
      apply ((htail p hp hpl hph N hN i.val).2 _ (Real.one_le_rpow hn1 (by positivity))).trans
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ hB.le
      apply Real.exp_le_exp.mpr
      have hcb : c ≤ b := min_le_right _ _
      simpa only [neg_mul] using neg_le_neg ((mul_le_mul_of_nonneg_right hcb (by positivity)).trans
        (mul_le_mul_of_nonneg_left hnc hb.le))
    calc
      _ ≤ (gibbsMeasure p N) (⋃ i ∈ J, {X | (n : ℝ) ^ (h / 2) ≤ gap X i.val}) := measure_mono hsub
      _ ≤ ∑ i ∈ J, (gibbsMeasure p N) {X | (n : ℝ) ^ (h / 2) ≤ gap X i.val} :=
        measure_biUnion_finset_le J _
      _ ≤ ∑ _i ∈ J, ENNReal.ofReal (B * Real.exp (-c * (n : ℝ) ^ δ)) :=
        Finset.sum_le_sum fun i _ => ht i
      _ = ENNReal.ofReal ((J.card : ℝ) * (B * Real.exp (-c * (n : ℝ) ^ δ))) := by
        rw [Finset.sum_const, ← ENNReal.ofReal_nsmul]
        simp only [nsmul_eq_mul]
      _ ≤ ENNReal.ofReal ((n : ℝ) * (B * Real.exp (-c * (n : ℝ) ^ δ))) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hknR (by positivity))
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have ht := hpoly (n : ℝ) hn1
        rw [Real.rpow_one] at ht
        nlinarith [mul_le_mul_of_nonneg_left ht hB.le,
          Real.exp_pos (-(c / 2) * (n : ℝ) ^ δ)]

/-- Internal domination by the actual uniform active-tilt normalizer.
It applies to every event, including nonmeasurable ones. -/
theorem internal_activeTilt_measure_le {p : Parameters} {N n : ℕ+}
    {hn : (n : ℕ) ≤ (N : ℕ)} {θ : PhysicalCutoff} {h z : ℝ} {ι : Bool}
    (hz : 0 < z) (hZ : ENNReal.ofReal z ≤ tiltNormalizer p N n hn θ h ι) :
    tiltedParticleMeasure p N n hn θ h ι ≤ ENNReal.ofReal z⁻¹ • gibbsMeasure p N := by
  have hd : (gibbsMeasure p N).withDensity (fun X =>
      ENNReal.ofReal (Real.exp (-p.val.1 * physicalGapPenalty N n hn θ h ι X))) ≤
        gibbsMeasure p N := by
    refine (withDensity_mono (ae_of_all _ fun X => ?_)).trans_eq withDensity_one
    apply ENNReal.ofReal_le_one.mpr
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [p.property.1])
      (DefinitionSanity.penalty_nonneg N n hn θ h ι X)
  have hi := ENNReal.inv_le_inv.mpr hZ
  rw [← ENNReal.ofReal_inv_of_pos hz] at hi
  change (tiltNormalizer p N n hn θ h ι)⁻¹ • _ ≤ _
  calc
    _ ≤ (tiltNormalizer p N n hn θ h ι)⁻¹ • gibbsMeasure p N := by gcongr
    _ ≤ _ := by gcongr

/-- See Subsection 4.5 of the paper, the block-deviation input under both actual active
tilts. This includes `n = N`. Only the tested block must be proper. The
stretched-exponential power precedes the cutoff and the temperature range. -/
theorem physical_tilted_block_deviation_probability (s h : ℝ) (hs : 1 < s) (hh : 0 < h) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (θ : PhysicalCutoff) (βlo βhi : ℝ),
      0 < βlo → βlo ≤ βhi → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ (N n : ℕ+), 2 ≤ (N : ℕ) → ∀ (hn : (n : ℕ) ≤ (N : ℕ)) (ι : Bool),
      ∀ J : Finset (Fin (N : ℕ)), 1 ≤ J.card → J.card ≤ (n : ℕ) → J.card < (N : ℕ) →
        (tiltedParticleMeasure p N n hn θ h ι)
          {X | (n : ℝ) ^ h * (J.card : ℝ) ^ (1 / 2 : ℝ) <
            |(∑ i ∈ J, gap X i.val) - (J.card : ℝ)|} ≤
              ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ δ)) := by
  obtain ⟨δ, hδ, hb⟩ := physical_block_deviation_probability s h hs hh
  refine ⟨δ, hδ, fun θ βlo βhi hlo hle => ?_⟩
  obtain ⟨C, c, hC, hc, htail⟩ := hb βlo βhi hlo hle
  obtain ⟨Cθ, hCθ, hcurv, _⟩ := θ.property.2.2.2.2
  obtain ⟨z, hz, _, hnorm⟩ := activeTilt_normalizer_uniform_lower
    s βlo βhi h Cθ hs hlo hle hh hCθ
  refine ⟨z⁻¹ * C, c, by positivity, hc, ?_⟩
  intro p hp hpl hph N n hN hn ι J hk hkn hkN
  have hd := internal_activeTilt_measure_le hz (hnorm p hp hpl hph N n hN hn θ hcurv ι)
  have he := hd {X | (n : ℝ) ^ h * (J.card : ℝ) ^ (1 / 2 : ℝ) <
    |(∑ i ∈ J, gap X i.val) - (J.card : ℝ)|}
  rw [Measure.smul_apply, smul_eq_mul] at he
  apply he.trans
  have hb := mul_le_mul' (le_refl (ENNReal.ofReal z⁻¹)) (htail p hp hpl hph N n hN J hk hkn hkN)
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hz.le)] at hb
  simpa only [mul_assoc] using hb

end Riesz2.DecayShort.ExceptionalEvent
