/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.ExceptionalEventPart2
public import Riesz2.Frozen.GoodBlockEvent
public import Riesz1.Rigidity.ReductionScalesMean
public import Riesz2.Preliminaries.InverseIntervalKernelPart2

/-!
# Simultaneous exceptional events for the short-range law

See Subsection 4.5 of the paper: ordinary intervals, coordinate cutoffs and the
existing coefficient event, under both physical active tilts.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace Riesz2.DecayShort.ExceptionalEvent

/-- Internal counting step of Subsection 4.5: every ordinary interval has
its actual length, including the empty boundary case. -/
theorem internal_interval_card (N a b : ℕ) (hb : b ≤ N) :
    (Finset.univ.filter (fun i : Fin N => a ≤ i.val ∧ i.val < b)).card = b - a := by
  classical
  rw [← Nat.card_Ico]
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico] using hi
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro j hj
    have hj' := Finset.mem_Ico.mp hj
    exact ⟨⟨j,lt_of_lt_of_le hj'.2 hb⟩, by simp [hj'.1,hj'.2], rfl⟩

/-- Internal embedding step of Subsection 4.5: an ordinary interval in a
proper block retains its original ambient labels and its exact gap sum. -/
theorem internal_interval_sum (N n : ℕ) (hn : n ≤ N) (x : Fin N → ℝ)
    (a b : ℕ) (hb : b ≤ n) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => a ≤ i.val ∧ i.val < b),
      x (Fin.castLE hn i)) =
    ∑ i ∈ Finset.univ.filter (fun i : Fin N => a ≤ i.val ∧ i.val < b), x i := by
  classical
  apply Finset.sum_bij (fun i _ => Fin.castLE hn i)
  · intro i hi
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castLE] using hi
  · intro i _ j _ hij
    exact Fin.ext (congrArg (fun i : Fin N => i.val) hij)
  · intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    refine ⟨⟨j.val,lt_of_lt_of_le hj'.2 hb⟩, by simp [hj'.1,hj'.2], Fin.ext rfl⟩
  · intro i _
    rfl

private theorem measurable_forall {A ι : Type*} [MeasurableSpace A] [Countable ι]
    {P : ι → A → Prop} (h : ∀ i, MeasurableSet {x | P i x}) :
    MeasurableSet {x | ∀ i, P i x} := by
  simpa only [ofPred_forall] using MeasurableSet.iInter h

/-- Measurability of the auxiliary event used for Subsection 4.4.
For `s > 1` its interval exponent is precisely one half. -/
theorem measurableSet_goodBlockEvent (s : ℝ) (n N : ℕ+) (h : ℝ) :
    MeasurableSet (goodBlockEvent s n N h) := by
  apply MeasurableSet.inter
    (measurableSet_lt (Finset.measurable_sum _ fun i _ => measurable_pi_apply i) measurable_const)
  apply MeasurableSet.inter
  · exact measurable_forall fun i => (measurableSet_le measurable_const
      (measurable_pi_apply i)).inter (measurableSet_le (measurable_pi_apply i) measurable_const)
  · apply measurable_forall
    intro a
    apply measurable_forall
    intro b
    by_cases hab : a < b
    · by_cases hbn : b ≤ (n : ℕ)
      · simp only [hab,hbn,true_implies]
        exact measurableSet_le
          (((Finset.measurable_sum _ fun i _ => measurable_pi_apply i).sub measurable_const).abs)
          measurable_const
      · simp [hbn]
    · simp [hab]

/-- An auxiliary proper-block good event for the proof of Lemma 4.8.
The interval and gap conditions use `goodBlockEvent`. The six
coefficient families use `coefficientEvent`. -/
def properGoodEvent (p : Parameters) (n : ℕ+) (m : ℕ)
    (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (h D : ℝ) :
    Set (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :=
  {x | WithLp.ofLp x.val ∈ goodBlockEvent p.val.2 n ((n : ℕ) + m).succPNat h} ∩
    coefficientEvent p n m hn D

/-- See Subsection 4.5 of the paper, both coordinate cutoffs under either active
tilt. The common power is `h`, independent of inverse temperature. -/
theorem physical_tilted_coordinate_probability (s h : ℝ) (hs : 1 < s) (hh : 0 < h)
    (θ : PhysicalCutoff) (βlo βhi : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ (N n : ℕ+), 2 ≤ (N : ℕ) → ∀ (hn : (n : ℕ) ≤ (N : ℕ)) (ι : Bool) (j : ℤ),
        (tiltedParticleMeasure p N n hn θ h ι) {X | gap X j < (n : ℝ) ^ (-h)} ≤
          ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ h)) ∧
        (tiltedParticleMeasure p N n hn θ h ι) {X | (n : ℝ) ^ h < gap X j} ≤
          ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ h)) := by
  obtain ⟨C,c,hC,hc,ht,_⟩ := SingleGapTails.single_gap_tails s βlo βhi
    (by linarith) hs.ne' hlo hle
  obtain ⟨Cθ,hCθ,hcurv,_⟩ := θ.property.2.2.2.2
  obtain ⟨z,hz,_,hZ⟩ := activeTilt_normalizer_uniform_lower s βlo βhi h Cθ hs hlo hle hh hCθ
  refine ⟨z⁻¹ * C,c,by positivity,hc,fun p hp hpl hph N n hN hn ι j => ?_⟩
  have hd := internal_activeTilt_measure_le hz (hZ p hp hpl hph N n hN hn θ hcurv ι)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hsmall : (gibbsMeasure p N) {X | gap X j < (n : ℝ) ^ (-h)} ≤
      ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ h)) := by
    apply (measure_mono (show {X | gap X j < (n : ℝ) ^ (-h)} ⊆
      {X | gap X j ≤ (n : ℝ) ^ (-h)} from fun _ hx => (show gap _ j < _ from hx).le)).trans
        ((ht p hp hpl hph N hN j).1 _ (Real.rpow_pos_of_pos hn0 _)
          (Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith))) |>.trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.exp_le_exp.mpr
    rw [← Real.rpow_mul hn0.le]
    have he : -h * -s = h * s := by ring
    rw [he]
    have ht := Real.rpow_le_rpow_of_exponent_le hn1 (show h ≤ h * s by nlinarith)
    nlinarith
  have hlarge := (measure_mono (show {X : Riesz1.Configuration N | (n : ℝ) ^ h < gap X j} ⊆
      {X | (n : ℝ) ^ h ≤ gap X j} from fun _ hx => (show _ < gap _ j from hx).le)).trans
    ((ht p hp hpl hph N hN j).2 _ (Real.one_le_rpow hn1 hh.le))
  have transfer (E : Set (Riesz1.Configuration N))
      (hE : (gibbsMeasure p N) E ≤ ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ h))) :
      (tiltedParticleMeasure p N n hn θ h ι) E ≤
        ENNReal.ofReal (z⁻¹ * C * Real.exp (-c * (n : ℝ) ^ h)) := by
    apply (hd _).trans
    rw [Measure.smul_apply, smul_eq_mul]
    have he := mul_le_mul' (le_refl (ENNReal.ofReal z⁻¹)) hE
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hz.le)] at he
    simpa only [mul_assoc] using he
  exact ⟨transfer _ hsmall,transfer _ hlarge⟩

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 4.5 of the paper, simultaneous ordinary-interval and coordinate
probability on the particle carrier. This is the auxiliary proper
good-block event, and includes both active penalties. -/
theorem physical_tilted_goodBlock_probability (s h : ℝ) (hs : 1 < s) (hh : 0 < h) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (θ : PhysicalCutoff) (βlo βhi : ℝ),
      0 < βlo → βlo ≤ βhi → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ (N n : ℕ+), 2 ≤ (N : ℕ) → ∀ (hn : (n : ℕ) ≤ (N : ℕ)),
        (n : ℕ) < (N : ℕ) → ∀ ι : Bool,
        (tiltedParticleMeasure p N n hn θ h ι)
          {X | finiteGapBlock X ∉ goodBlockEvent s n N h} ≤
            ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ δ)) := by
  classical
  obtain ⟨δ₀,hδ₀,hblock⟩ := physical_tilted_block_deviation_probability s h hs hh
  let δ := min δ₀ h
  have hδ : 0 < δ := lt_min hδ₀ hh
  refine ⟨δ,hδ,fun θ βlo βhi hlo hle => ?_⟩
  obtain ⟨B,b,hB,hb,ht⟩ := hblock θ βlo βhi hlo hle
  obtain ⟨A,a,hA,ha,hgap⟩ := physical_tilted_coordinate_probability s h hs hh θ βlo βhi hlo hle
  let c := min a b
  have hc : 0 < c := lt_min ha hb
  obtain ⟨K,hK,hpoly⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := 2) (c := c) (c' := c / 2) hδ (by linarith)
  refine ⟨4 * (A + B) * (K + 1),c / 2,by positivity,by positivity,?_⟩
  intro p hp hpl hph N n hN hn hproper ι
  let μ := tiltedParticleMeasure p N n hn θ h ι
  have : IsProbabilityMeasure μ := DefinitionSanity.tilted_probability p N n hn θ h ι
  let I := Fin (n : ℕ) ⊕ (Fin (n : ℕ) ⊕ (Fin (n : ℕ) × Fin ((n : ℕ) + 1)))
  let E : I → Set (Riesz1.Configuration N) := Sum.elim
    (fun i => {X | gap X i.val < (n : ℝ) ^ (-h)})
    (Sum.elim (fun i => {X | (n : ℝ) ^ h < gap X i.val})
      (fun ab => if ab.1.val < ab.2.val then
        {X | (n : ℝ) ^ h * (ab.2.val - ab.1.val : ℕ) ^ (1 / 2 : ℝ) <
          |(∑ i ∈ Finset.univ.filter (fun i : Fin (n : ℕ) =>
            ab.1.val ≤ i.val ∧ i.val < ab.2.val), finiteGapBlock X i) -
              (ab.2.val - ab.1.val : ℕ)|} else ∅))
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have weaken {r C c₀ : ℝ} (hC : 0 ≤ C) (hCAB : C ≤ A + B) (hc₀ : c ≤ c₀) (hr : δ ≤ r)
      (S : Set (Riesz1.Configuration N))
      (hS : μ S ≤ ENNReal.ofReal (C * Real.exp (-c₀ * (n : ℝ) ^ r))) :
      μ S ≤ ENNReal.ofReal ((A + B) * Real.exp (-c * (n : ℝ) ^ δ)) := by
    apply hS.trans
    apply ENNReal.ofReal_le_ofReal
    have he : Real.exp (-c₀ * (n : ℝ) ^ r) ≤ Real.exp (-c * (n : ℝ) ^ δ) := by
      apply Real.exp_le_exp.mpr
      have hpow := Real.rpow_le_rpow_of_exponent_le hn1 hr
      have := mul_le_mul hc₀ hpow (by positivity : 0 ≤ (n : ℝ) ^ δ) (by linarith : 0 ≤ c₀)
      linarith
    apply (mul_le_mul_of_nonneg_left he hC).trans
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    exact hCAB
  have htail (i : I) : μ (E i) ≤ ENNReal.ofReal ((A + B) * Real.exp (-c * (n : ℝ) ^ δ)) := by
    rcases i with i | (i | ⟨a₀,b₀⟩)
    · exact weaken hA.le (by linarith) (min_le_left _ _) (min_le_right _ _) _
        (hgap p hp hpl hph N n hN hn ι i.val).1
    · exact weaken hA.le (by linarith) (min_le_left _ _) (min_le_right _ _) _
        (hgap p hp hpl hph N n hN hn ι i.val).2
    · dsimp only [E, Sum.elim_inr]
      split_ifs with hab
      · let J := Finset.univ.filter (fun i : Fin (N : ℕ) => a₀.val ≤ i.val ∧ i.val < b₀.val)
        have hbn : b₀.val ≤ (n : ℕ) := by have := b₀.isLt; omega
        have hj : J.card = b₀.val - a₀.val := internal_interval_card _ _ _ (hbn.trans hn)
        have hj1 : 1 ≤ J.card := by rw [hj]; omega
        have hjn : J.card ≤ (n : ℕ) := by rw [hj]; omega
        have hsum (X : Riesz1.Configuration N) :
            (∑ i ∈ Finset.univ.filter (fun i : Fin (n : ℕ) => a₀.val ≤ i.val ∧ i.val < b₀.val),
              finiteGapBlock X i) = ∑ i ∈ J, gap X i.val := by
          exact internal_interval_sum _ _ hn (fun i => gap X i.val) _ _ hbn
        have hb₀ := ht p hp hpl hph N n hN hn ι J hj1 hjn (hjn.trans_lt hproper)
        simp_rw [hj,← hsum] at hb₀
        exact weaken hB.le (by linarith) (min_le_right _ _) (min_le_left _ _) _ hb₀
      · rw [measure_empty]
        exact zero_le
  have hsub : {X : Riesz1.Configuration N | finiteGapBlock X ∉ goodBlockEvent s n N h} ⊆
      ⋃ i : I, E i := by
    intro X hX
    by_contra hnot
    have hnE (i : I) : X ∉ E i := fun hi => hnot (mem_iUnion.mpr ⟨i,hi⟩)
    apply hX
    have hmass : (∑ i : Fin (n : ℕ), finiteGapBlock X i) < (N : ℝ) := by
      have he : (∑ i : Fin (n : ℕ), finiteGapBlock X i) = Riesz1.blockLength X 0 n := by
        rw [Riesz1.blockLength_eq_sum]
        simpa only [finiteGapBlock,gap,Riesz1.gap,zero_add] using
          (Fin.sum_univ_eq_sum_range (fun j : ℕ => gap X j) (n : ℕ))
      rw [he]
      exact Riesz1.blockLength_lt_N X 0 hproper
    refine ⟨hmass,?_,?_⟩
    · intro i
      exact ⟨not_lt.mp (hnE (Sum.inl i)),not_lt.mp (hnE (Sum.inr (Sum.inl i)))⟩
    · intro a₀ b₀ hab hbn
      let a : Fin (n : ℕ) := ⟨a₀,by omega⟩
      let b : Fin ((n : ℕ) + 1) := ⟨b₀,by omega⟩
      have he := hnE (Sum.inr (Sum.inr (a,b)))
      dsimp only [E, Sum.elim_inr] at he
      rw [ite_eq_left hab] at he
      have hs1 : min s 1 = 1 := min_eq_right hs.le
      rw [hs1]
      exact not_lt.mp he
  have hcard : (Fintype.card I : ℝ) ≤ 4 * (n : ℝ) ^ 2 := by
    dsimp [I]
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    push_cast
    nlinarith
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).mpr
  change μ.real _ ≤ _
  calc
    _ ≤ μ.real (⋃ i : I, E i) := measureReal_mono hsub
    _ ≤ ∑ i : I, μ.real (E i) := measureReal_iUnion_fintype_le _
    _ ≤ (Fintype.card I : ℝ) * ((A + B) * Real.exp (-c * (n : ℝ) ^ δ)) := by
      calc
        _ ≤ ∑ _i : I, (A + B) * Real.exp (-c * (n : ℝ) ^ δ) := by
          apply Finset.sum_le_sum
          intro i _
          change (μ (E i)).toReal ≤ _
          exact ENNReal.toReal_le_of_le_ofReal (by positivity) (htail i)
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ 4 * (A + B) * ((n : ℝ) ^ 2 * Real.exp (-c * (n : ℝ) ^ δ)) := by
      nlinarith [mul_le_mul_of_nonneg_right hcard (by positivity :
        0 ≤ (A + B) * Real.exp (-c * (n : ℝ) ^ δ))]
    _ ≤ 4 * (A + B) * ((K + 1) * Real.exp (-(c / 2) * (n : ℝ) ^ δ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have ht := hpoly (n : ℝ) hn1
      rw [Real.rpow_two] at ht
      nlinarith [Real.exp_pos (-(c / 2) * (n : ℝ) ^ δ)]
    _ = _ := by ring

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 4.5 of the paper: transfer of the complete gap and interval
event to the actual retained law, using its positive open carrier. -/
theorem proper_goodBlock_probability (s h : ℝ) (hs : 1 < s) (hh : 0 < h) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (θ : PhysicalCutoff) (βlo βhi : ℝ),
      0 < βlo → βlo ≤ βhi → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ (n : ℕ+) (m : ℕ) (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)),
        2 * (n : ℕ) ≤ (n : ℕ) + m + 1 → ∀ ι : Bool,
        let μ := (activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ h ι).comap
          ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
        μ {x | WithLp.ofLp x.val ∉ goodBlockEvent s n ((n : ℕ) + m).succPNat h} ≤
          ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ δ)) := by
  obtain ⟨δ,hδ,hprob⟩ := physical_tilted_goodBlock_probability s h hs hh
  refine ⟨δ,hδ,fun θ βlo βhi hlo hle => ?_⟩
  obtain ⟨C,c,hC,hc,ht⟩ := hprob θ βlo βhi hlo hle
  refine ⟨C,c,hC,hc,?_⟩
  intro p hp hpl hph n m hn hhalf ι μ
  let N := ((n : ℕ) + m).succPNat
  let E := {y : EuclideanSpace ℝ (Fin (n : ℕ)) | WithLp.ofLp y ∉ goodBlockEvent s n N h}
  have hE : MeasurableSet E := (measurableSet_goodBlockEvent s n N h).compl.preimage
    (PiLp.continuous_ofLp 2 (fun _ : Fin (n : ℕ) => ℝ)).measurable
  change ((activeTiltedGapLaw p N n hn θ h ι).comap _) _ ≤ _
  rw [(MeasurableEmbedding.subtype_coe (AffineSimplex.isOpen_chartDomain n _).measurableSet).comap_apply]
  apply (measure_mono (show ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
    EuclideanSpace ℝ (Fin (n : ℕ))) '' {x | WithLp.ofLp x.val ∉ goodBlockEvent s n N h} ⊆ E from
      by rintro _ ⟨x,hx,rfl⟩; exact hx)).trans
  rw [activeTiltedGapLaw, Measure.map_apply (DefinitionSanity.active_projection_measurable _ _) hE]
  exact ht p hp hpl hph N n (by dsimp [N]; have := n.pos; omega) hn
    (by dsimp [N]; have := n.pos; omega) ι

set_option backward.isDefEq.respectTransparency false in
/-- Probability bound for the auxiliary proper-block event in Subsection 4.5.
The coefficient degree precedes the tolerance. The stretched-exponential
power precedes the cutoff and compact temperature interval. All gap,
ordinary-interval and six coefficient conditions are included. -/
theorem proper_good_event_probability (s : ℝ) (hs : 1 < s) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ h : ℝ, 0 < h → ∃ δ : ℝ, 0 < δ ∧
      ∀ (θ : PhysicalCutoff) (βlo βhi : ℝ), 0 < βlo → βlo ≤ βhi →
      ∃ A C c : ℝ, 1 ≤ A ∧ 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ (n : ℕ+) (m : ℕ) (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)),
        4 ≤ (n : ℕ) + m + 1 → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 → ∀ ι : Bool,
        let μ := (activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ h ι).comap
          ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
        μ (properGoodEvent p n m hn h (A * (n : ℝ) ^ (κ * h)))ᶜ ≤
          ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ δ)) := by
  obtain ⟨κ,hκ,hcoeff⟩ := coefficient_exception_probability s hs
  refine ⟨κ,hκ,fun h hh => ?_⟩
  obtain ⟨δ₀,hδ₀,hgap⟩ := proper_goodBlock_probability s h hs hh
  let δ := min δ₀ h
  refine ⟨δ,lt_min hδ₀ hh,fun θ βlo βhi hlo hle => ?_⟩
  obtain ⟨B,b,hB,hb,hg⟩ := hgap θ βlo βhi hlo hle
  obtain ⟨A,C,c,hA,hC,hc,hc₀⟩ := hcoeff θ βlo βhi h hlo hle hh
  let d := min b c
  refine ⟨A,B + C,d,hA,by positivity,lt_min hb hc,?_⟩
  intro p hp hpl hph n m hn _ hhalf ι μ
  have hgap₀ := hg p hp hpl hph n m hn hhalf ι
  have hcoeff₀ := hc₀ p hp hpl hph n m hn hhalf ι
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have he₁ : Real.exp (-b * (n : ℝ) ^ δ₀) ≤ Real.exp (-d * (n : ℝ) ^ δ) := by
    apply Real.exp_le_exp.mpr
    have hp := Real.rpow_le_rpow_of_exponent_le hn1 (min_le_left δ₀ h)
    have hd : d ≤ b := min_le_left b c
    have := mul_le_mul hd hp (by positivity : 0 ≤ (n : ℝ) ^ δ) hb.le
    linarith
  have he₂ : Real.exp (-c * (n : ℝ) ^ h) ≤ Real.exp (-d * (n : ℝ) ^ δ) := by
    apply Real.exp_le_exp.mpr
    have hp := Real.rpow_le_rpow_of_exponent_le hn1 (min_le_right δ₀ h)
    have hd : d ≤ c := min_le_right b c
    have := mul_le_mul hd hp (by positivity : 0 ≤ (n : ℝ) ^ δ) hc.le
    linarith
  calc
    _ ≤ μ {x | WithLp.ofLp x.val ∉ goodBlockEvent p.val.2 n ((n : ℕ) + m).succPNat h} +
        μ (coefficientEvent p n m hn (A * (n : ℝ) ^ (κ * h)))ᶜ := by
      rw [properGoodEvent, compl_inter]
      exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (B * Real.exp (-b * (n : ℝ) ^ δ₀)) +
        ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ h)) := by
      rw [hp]
      exact add_le_add hgap₀ hcoeff₀
    _ ≤ ENNReal.ofReal (B * Real.exp (-d * (n : ℝ) ^ δ)) +
        ENNReal.ofReal (C * Real.exp (-d * (n : ℝ) ^ δ)) :=
      add_le_add (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left he₁ hB.le))
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left he₂ hC.le))
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

/-- See Subsection 4.4 of the paper, the full-cycle short-range event. It uses
every cyclic interval of length at most half the cycle, the square-root
deviation profile, and the actual ambient interaction Hessian entries. -/
def fullGoodEvent (p : Parameters) (N : ℕ+) (h D : ℝ) : Set (Riesz1.Configuration N) :=
  {X | (∀ i : Fin (N : ℕ), (N : ℝ) ^ (-h) ≤ gap X i.val ∧ gap X i.val ≤ (N : ℝ) ^ h) ∧
    (∀ (a : Fin (N : ℕ)) (r : Fin ((N : ℕ) / 2)),
      |(∑ i ∈ cyclicIndexInterval N a (r.val + 1), gap X i.val) - (r.val + 1 : ℕ)| ≤
        (N : ℝ) ^ h * (r.val + 1 : ℕ) ^ (1 / 2 : ℝ)) ∧
    ∀ a b : Fin (N : ℕ), GoodBlocks.particleHessian p N a b X ≤
      D * (1 + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-p.val.2)}

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 4.5 of the paper, the full-cycle probability clause, for both
active tilts. The coefficient degree depends only on the Riesz exponent. The tail power depends only on the exponent and tolerance. -/
theorem full_good_event_probability (s : ℝ) (hs : 1 < s) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ h : ℝ, 0 < h → ∃ δ : ℝ, 0 < δ ∧
      ∀ (θ : PhysicalCutoff) (βlo βhi : ℝ), 0 < βlo → βlo ≤ βhi →
      ∃ A C c : ℝ, 1 ≤ A ∧ 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ N : ℕ+, 4 ≤ (N : ℕ) → ∀ ι : Bool,
        (tiltedParticleMeasure p N N le_rfl θ h ι)
          (fullGoodEvent p N h (A * (N : ℝ) ^ (κ * h)))ᶜ ≤
            ENNReal.ofReal (C * Real.exp (-c * (N : ℝ) ^ δ)) := by
  classical
  obtain ⟨κ,hκ,hmom⟩ := interval_counting_coefficient_moments s hs
  refine ⟨κ,hκ,fun h hh => ?_⟩
  obtain ⟨δ₀,hδ₀,hblock⟩ := physical_tilted_block_deviation_probability s h hs hh
  let δ := min δ₀ h
  have hδ : 0 < δ := lt_min hδ₀ hh
  refine ⟨δ,hδ,fun θ βlo βhi hlo hle => ?_⟩
  obtain ⟨B,b,hB,hb,hbt⟩ := hblock θ βlo βhi hlo hle
  obtain ⟨G,g,hG,hg,hgt⟩ := physical_tilted_coordinate_probability s h hs hh θ βlo βhi hlo hle
  obtain ⟨M,hM,hmt⟩ := hmom θ βlo βhi h hlo hle hh
  let A := max 1 (Real.exp 1 * M)
  let c := min 1 (min b g)
  have hc : 0 < c := lt_min zero_lt_one (lt_min hb hg)
  let T := G + B + 1
  have hT : 0 < T := by dsimp [T]; positivity
  obtain ⟨K,hK,hpoly⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := 2) (c := c) (c' := c / 2) hδ (by linarith)
  refine ⟨A,4 * T * (K + 1),c / 2,le_max_left _ _,by positivity,by positivity,?_⟩
  intro p hp hpl hph N hN ι
  let μ := tiltedParticleMeasure p N N le_rfl θ h ι
  have : IsProbabilityMeasure μ := DefinitionSanity.tilted_probability p N N le_rfl θ h ι
  let I := Fin (N : ℕ) ⊕ (Fin (N : ℕ) ⊕
    ((Fin (N : ℕ) × Fin ((N : ℕ) / 2)) ⊕ (Fin (N : ℕ) × Fin (N : ℕ))))
  let E : I → Set (Riesz1.Configuration N) := Sum.elim
    (fun i => {X | gap X i.val < (N : ℝ) ^ (-h)})
    (Sum.elim (fun i => {X | (N : ℝ) ^ h < gap X i.val})
      (Sum.elim (fun ar => {X | (N : ℝ) ^ h * (ar.2.val + 1 : ℕ) ^ (1 / 2 : ℝ) <
        |(∑ i ∈ cyclicIndexInterval N ar.1 (ar.2.val + 1), gap X i.val) - (ar.2.val + 1 : ℕ)|})
        (fun ab => {X | A * (N : ℝ) ^ (κ * h) *
          (1 + (Riesz1.cyclicIndexDistance N ab.1 ab.2 : ℝ)) ^ (-p.val.2) <
            GoodBlocks.particleHessian p N ab.1 ab.2 X})))
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have weaken {C₀ c₀ r : ℝ} (hC₀ : 0 ≤ C₀) (hCT : C₀ ≤ T) (hcc : c ≤ c₀) (hr : δ ≤ r)
      (S : Set (Riesz1.Configuration N))
      (hS : μ S ≤ ENNReal.ofReal (C₀ * Real.exp (-c₀ * (N : ℝ) ^ r))) :
      μ.real S ≤ T * Real.exp (-c * (N : ℝ) ^ δ) := by
    apply (ENNReal.toReal_le_of_le_ofReal (by positivity) hS).trans
    have he : Real.exp (-c₀ * (N : ℝ) ^ r) ≤ Real.exp (-c * (N : ℝ) ^ δ) := by
      apply Real.exp_le_exp.mpr
      have ht := mul_le_mul hcc (Real.rpow_le_rpow_of_exponent_le hN1 hr)
        (by positivity : 0 ≤ (N : ℝ) ^ δ) (hc.le.trans hcc)
      linarith
    exact (mul_le_mul_of_nonneg_left he hC₀).trans
      (mul_le_mul_of_nonneg_right hCT (Real.exp_pos _).le)
  have htail (i : I) : μ.real (E i) ≤ T * Real.exp (-c * (N : ℝ) ^ δ) := by
    rcases i with i | (i | (⟨a,r⟩ | ⟨a,b₀⟩))
    · exact weaken hG.le (by dsimp [T]; linarith) ((min_le_right 1 _).trans (min_le_right b g))
        (min_le_right δ₀ h) _ (hgt p hp hpl hph N N (by omega) le_rfl ι i.val).1
    · exact weaken hG.le (by dsimp [T]; linarith) ((min_le_right 1 _).trans (min_le_right b g))
        (min_le_right δ₀ h) _ (hgt p hp hpl hph N N (by omega) le_rfl ι i.val).2
    · let J := cyclicIndexInterval N a (r.val + 1)
      have hr : r.val + 1 ≤ (N : ℕ) / 2 := by have := r.isLt; omega
      have hj : J.card = r.val + 1 := card_cyclicIndexInterval N a (hr.trans (Nat.div_le_self _ _))
      have ht := hbt p hp hpl hph N N (by omega) le_rfl ι J (by rw [hj]; omega)
        (by rw [hj]; omega) (by rw [hj]; omega)
      rw [hj] at ht
      exact weaken hB.le (by dsimp [T]; linarith) ((min_le_right 1 _).trans (min_le_left b g))
        (min_le_left δ₀ h) _ ht
    · have hf := GoodBlocks.measurable_particleHessian p N a b₀
      have hw : 0 < (1 + (Riesz1.cyclicIndexDistance N a b₀ : ℝ)) ^ (-p.val.2) := by positivity
      have hm (q : ℝ) (hq : 1 ≤ q) := ((hmt p hp hpl hph).2 N hN ι q hq a b₀).2
      have hmark := internal_profile_tail μ (GoodBlocks.particleHessian p N a b₀) hf
        hN1 hκ hh hM (le_max_right 1 _) hw (fun q hq => by simpa only [hp] using hm q hq)
      have he : Real.exp (-((N : ℝ) ^ h)) ≤ Real.exp (-c * (N : ℝ) ^ δ) := by
        apply Real.exp_le_exp.mpr
        have ht := mul_le_mul (min_le_left 1 (min b g))
          (Real.rpow_le_rpow_of_exponent_le hN1 (min_le_right δ₀ h))
          (by positivity : 0 ≤ (N : ℝ) ^ δ) zero_le_one
        linarith
      apply hmark.trans (he.trans ?_)
      have h1 : 1 ≤ T := by dsimp [T]; linarith
      simpa only [one_mul] using mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have hsub : (fullGoodEvent p N h (A * (N : ℝ) ^ (κ * h)))ᶜ ⊆ ⋃ i : I, E i := by
    intro X hx
    by_contra hnot
    have hnE (i : I) : X ∉ E i := fun hi => hnot (mem_iUnion.mpr ⟨i,hi⟩)
    apply hx
    refine ⟨fun i => ⟨not_lt.mp (hnE (Sum.inl i)),not_lt.mp (hnE (Sum.inr (Sum.inl i)))⟩,
      fun a r => not_lt.mp (hnE (Sum.inr (Sum.inr (Sum.inl (a,r))))),
      fun a b => not_lt.mp (hnE (Sum.inr (Sum.inr (Sum.inr (a,b)))))⟩
  have hcard : (Fintype.card I : ℝ) ≤ 4 * (N : ℝ) ^ 2 := by
    have hnat : Fintype.card I ≤ 4 * (N : ℕ) ^ 2 := by
      dsimp [I]
      simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
      have := Nat.div_le_self (N : ℕ) 2
      have := N.pos
      nlinarith
    exact_mod_cast hnat
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).mpr
  change μ.real _ ≤ _
  calc
    _ ≤ μ.real (⋃ i : I, E i) := measureReal_mono hsub
    _ ≤ ∑ i : I, μ.real (E i) := measureReal_iUnion_fintype_le _
    _ ≤ (Fintype.card I : ℝ) * (T * Real.exp (-c * (N : ℝ) ^ δ)) := by
      simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
        (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => htail i)
    _ ≤ 4 * T * ((N : ℝ) ^ 2 * Real.exp (-c * (N : ℝ) ^ δ)) := by
      nlinarith [mul_le_mul_of_nonneg_right hcard (by positivity :
        0 ≤ T * Real.exp (-c * (N : ℝ) ^ δ))]
    _ ≤ 4 * T * ((K + 1) * Real.exp (-(c / 2) * (N : ℝ) ^ δ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have ht := hpoly (N : ℝ) hN1
      rw [Real.rpow_two] at ht
      nlinarith [Real.exp_pos (-(c / 2) * (N : ℝ) ^ δ)]
    _ = _ := by ring

end Riesz2.DecayShort.ExceptionalEvent
