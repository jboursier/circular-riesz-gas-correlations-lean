/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.PaperBoundaryMoments
public import Riesz2.DecayShort.PaperGoodEventMoments

/-!
# Direct probability bound for the paper's good event

Steps 1--3 of Lemma 4.8: apply Markov to the four coefficient and variance families of equation (4.10), then
take their finite union together with the gap and block failures.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal ContDiff Topology

namespace Riesz2.DecayShort

set_option backward.isDefEq.respectTransparency false in
/-- Direct moment-to-probability argument of Lemma 4.8 for
equation (4.10). The coefficient degree precedes the tolerance,
and the tail power precedes the cutoff and temperature interval. -/
theorem paper_proper_good_event_probability (s : ℝ) (hs : 1 < s) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ h : ℝ, 0 < h → ∃ δ : ℝ, 0 < δ ∧
      ∀ (θ : PhysicalCutoff) (βlo βhi : ℝ), 0 < βlo → βlo ≤ βhi →
      ∃ A C c : ℝ, 1 ≤ A ∧ 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ (n : ℕ+) (m : ℕ) (hn : (n : ℕ) ≤ (((n : ℕ)+m).succPNat : ℕ)),
        2 ≤ (n : ℕ)+m+1 → 2*(n : ℕ) ≤ (n : ℕ)+m+1 → ∀ b : Bool,
      ∀ (U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ),
      (∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) //
        y ∈ gapAmbientDomain ((n : ℕ)+m).succPNat},
        U y.val = p.val.1 * physicalAmbientGapEnergy p ((n : ℕ)+m).succPNat y) →
      let μ := (activeTiltedGapLaw p ((n : ℕ)+m).succPNat n hn θ h b).comap
        ((↑) : AffineSimplex.chartDomain n ((n+m : ℕ)+1) → EuclideanSpace ℝ (Fin (n : ℕ)))
      μ (paperProperGoodEvent p n m U h (A*(n : ℝ)^(κ*h)))ᶜ ≤
        ENNReal.ofReal (C*Real.exp (-c*(n : ℝ)^δ)) := by
  classical
  obtain ⟨d,hd,hm⟩ := interval_counting_coefficient_moments s hs
  obtain ⟨db,hdb,hmb⟩ := paper_boundary_entry_moments s hs
  obtain ⟨dv,hdv,hmv⟩ := paper_compensated_variance_moments s hs
  let κ := d+db+dv
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  refine ⟨κ,hκ,fun h hh => ?_⟩
  obtain ⟨δ₀,hδ₀,hgap⟩ := ExceptionalEvent.proper_goodBlock_probability s h hs hh
  let δ := min δ₀ h
  have hδ : 0 < δ := lt_min hδ₀ hh
  refine ⟨δ,hδ,fun θ βlo βhi hlo hle => ?_⟩
  obtain ⟨M,hM,hm⟩ := hm θ βlo βhi h hlo hle hh
  obtain ⟨Mb,hMb,hmb⟩ := hmb θ βlo βhi h hlo hle hh
  obtain ⟨Mv,hMv,hmv⟩ := hmv θ βlo βhi h hlo hle hh
  obtain ⟨B,b,hB,hb,hgap⟩ := hgap θ βlo βhi hlo hle
  let C₀ := 3*M+Mb+Mv
  have hC₀ : 0 < C₀ := by dsimp only [C₀]; positivity
  let A := max 1 (Real.exp 1*C₀)
  let c := min b (1/2)
  have hc : 0 < c := lt_min hb (by norm_num)
  obtain ⟨K,hK,hpoly⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := 2) (c := c) (c' := c/2) hδ (by linarith)
  refine ⟨A,B+4*(K+1),c/2,le_max_left _ _,by positivity,by positivity,?_⟩
  intro p hp hpl hph n m hn hN hhalf ι U hv μ
  have hμ : IsProbabilityMeasure μ := activeTilt_proper_probability p n m hn θ h ι
  let N := ((n : ℕ)+m).succPNat
  let X := AffineSimplex.chartDomain n ((n+m : ℕ)+1)
  let a := fun x => conditionalIntervalWeight p n m n.pos (Equiv.refl _) x
  let H := fun x => IntervalBoundary.intervalMatrix N ((n : ℕ)+m+1) le_rfl (a x)
  let S := Finset.univ.filter (fun a : Fin ((n : ℕ)+m+1) => (n : ℕ) ≤ a.val)
  let b₀ := fun i x => (m+1 : ℝ)⁻¹*∑ a ∈ S, H x (Fin.castLE hn i) a
  let c₀ := fun x => (m+1 : ℝ)⁻¹^2*∑ a ∈ S, ∑ b ∈ S, H x a b
  let J := (Fin (n : ℕ) × Fin (n : ℕ)) ⊕
    ((Fin (n : ℕ) × Fin (n : ℕ)) ⊕ ((Fin (n : ℕ) × Fin (n : ℕ)) ⊕ Fin (n : ℕ)))
  let f : J → X → ℝ := Sum.elim
    (fun ij x => IntervalBoundary.intervalMatrix N n hn (a x) ij.1 ij.2)
    (Sum.elim (fun ij x => |paperCompensationEntry p n m x ij.1 ij.2|)
      (Sum.elim (fun ij x => IntervalBoundary.boundaryMatrix N n hn (a x) ij.1 ij.2)
        (fun i x => paperCompensatedVariance p n m U x i)))
  let w : J → ℝ := Sum.elim
    (fun ij => (1+(Riesz1.cyclicIndexDistance N (Fin.castLE hn ij.1)
      (Fin.castLE hn ij.2) : ℝ))^(-s))
    (Sum.elim (fun _ => (N : ℝ)⁻¹)
      (Sum.elim (fun ij => paperBoundaryProfile s ij.1 ij.2)
        (fun i => (ConditionalScores.boundaryDistance i : ℝ)^(1-2*s)+(N : ℝ)⁻¹)))
  have hw (j : J) : 0 < w j := by
    rcases j with ij | (ij | (ij | i))
    · dsimp only [w,Sum.elim_inl]; positivity
    · dsimp only [w,Sum.elim_inr,Sum.elim_inl]; positivity
    · dsimp only [w,Sum.elim_inr,Sum.elim_inl,paperBoundaryProfile]
      apply add_pos_of_pos_of_nonneg _ (by positivity)
      apply Real.rpow_pos_of_pos
      exact_mod_cast (show 0 < max (ij.1.val+1) (ij.2.val+1) by omega)
    · dsimp only [w,Sum.elim_inr]
      exact add_pos_of_nonneg_of_pos (by positivity) (by positivity)
  have hf (j : J) : Measurable (f j) := by
    rcases j with ij | (ij | (ij | i))
    · exact measurable_conditional_intervalMatrix p n m n.pos _ hn ij.1 ij.2
    · exact (measurable_paperCompensationEntry p n m ij.1 ij.2).abs
    · dsimp only [f,Sum.elim_inr,Sum.elim_inl,IntervalBoundary.boundaryMatrix]
      apply Finset.measurable_sum
      intro t _
      split_ifs
      · exact measurable_const
      · exact (measurable_conditionalIntervalWeight p n m n.pos (Equiv.refl _) t).mul_const _
    · exact measurable_paperCompensatedVariance p n m U i
  have hmom (j : J) (q : ℝ) (hq : 1 ≤ q) :
      eLpNorm (f j) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (C₀*q^κ*w j) := by
    obtain ⟨hP,_,_,hbc⟩ := ((hm p hp hpl hph).1 n m hn hhalf ι).2.2 q hq
    rcases j with ij | (ij | (ij | i))
    · exact (hP ij.1 ij.2).2.trans (internal_moment_bound_enlarge hM.le
        (by dsimp only [C₀]; linarith) hq (by dsimp only [κ]; linarith) (by positivity))
    · have hbi := (le_self_add : eLpNorm (b₀ ij.1) (ENNReal.ofReal q) μ ≤
          eLpNorm (b₀ ij.1) (ENNReal.ofReal q) μ+eLpNorm c₀ (ENNReal.ofReal q) μ).trans (hbc ij.1).2.2.1
      have hbj := (le_self_add : eLpNorm (b₀ ij.2) (ENNReal.ofReal q) μ ≤
          eLpNorm (b₀ ij.2) (ENNReal.ofReal q) μ+eLpNorm c₀ (ENNReal.ofReal q) μ).trans (hbc ij.2).2.2.1
      have hci := (le_add_self : eLpNorm c₀ (ENNReal.ofReal q) μ ≤
          eLpNorm (b₀ ij.1) (ENNReal.ofReal q) μ+eLpNorm c₀ (ENNReal.ofReal q) μ).trans (hbc ij.1).2.2.1
      have he : (fun x => paperCompensationEntry p n m x ij.1 ij.2) =
          fun x => -b₀ ij.1 x-b₀ ij.2 x+c₀ x := by
        funext x
        dsimp only [paperCompensationEntry,b₀,c₀,H,a,N,S,Nat.succPNat_coe]
        ring
      have hqE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by simpa using ENNReal.ofReal_le_ofReal hq
      have hnorm := (eLpNorm_add_le (f := fun x => -b₀ ij.1 x-b₀ ij.2 x)
        (g := c₀) (μ := μ) hqE).trans
        (add_le_add ((eLpNorm_sub_le (f := -b₀ ij.1) (g := b₀ ij.2) hqE).trans
          (add_le_add (by simpa only [eLpNorm_neg] using hbi) hbj)) hci)
      change eLpNorm (fun x => |paperCompensationEntry p n m x ij.1 ij.2|) _ μ ≤ _
      change eLpNorm (fun x => ‖paperCompensationEntry p n m x ij.1 ij.2‖) _ μ ≤ _
      rw [eLpNorm_norm _ (measurable_paperCompensationEntry p n m ij.1 ij.2).aestronglyMeasurable]
      rw [he]
      apply hnorm.trans
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      have heq : M*q^d/(((n : ℕ)+m+1 : ℕ) : ℝ)+M*q^d/(((n : ℕ)+m+1 : ℕ) : ℝ)+
          M*q^d/(((n : ℕ)+m+1 : ℕ) : ℝ) = (3*M)*q^d*(N : ℝ)⁻¹ := by
        simp only [N,Nat.succPNat_coe,div_eq_mul_inv]; ring
      rw [heq]
      exact internal_moment_bound_enlarge (by positivity) (by dsimp only [C₀]; linarith)
        hq (by dsimp only [κ]; linarith) (by positivity)
    · exact (hmb p hp hpl hph n m hn hhalf ι q hq ij.1 ij.2).2.trans
        (internal_moment_bound_enlarge hMb.le (by dsimp only [C₀]; linarith)
          hq (by dsimp only [κ]; linarith) (by unfold paperBoundaryProfile; positivity))
    · exact (hmv p hp hpl hph n m hn hN hhalf ι U hv q hq i).2.trans
        (internal_moment_bound_enlarge hMv.le (by dsimp only [C₀]; linarith)
          hq (by dsimp only [κ]; linarith) (by positivity))
  have htail (j : J) : μ.real {x | A*(n : ℝ)^(κ*h)*w j < f j x} ≤
      Real.exp (-((n : ℝ)^h)) :=
    ExceptionalEvent.internal_profile_tail μ (f j) (hf j) (by exact_mod_cast n.pos)
      hκ hh hC₀ (le_max_right _ _) (hw j) (hmom j)
  let E := ⋃ j : J, {x | A*(n : ℝ)^(κ*h)*w j < f j x}
  have hevent : (paperProperGoodEvent p n m U h (A*(n : ℝ)^(κ*h)))ᶜ =
      {x | WithLp.ofLp x.val ∉ goodBlockEvent s n N h} ∪ E := by
    ext x
    simp only [mem_compl_iff,mem_union,E,mem_iUnion]
    change (¬ x ∈ paperProperGoodEvent p n m U h (A*(n : ℝ)^(κ*h))) ↔
      (WithLp.ofLp x.val ∉ goodBlockEvent s n N h) ∨
        ∃ j : J, A*(n : ℝ)^(κ*h)*w j < f j x
    rw [show (∃ j : J, A*(n : ℝ)^(κ*h)*w j < f j x) ↔
      ¬ ∀ j : J, f j x ≤ A*(n : ℝ)^(κ*h)*w j by simp]
    rw [← not_and_or]
    apply not_congr
    dsimp only [J]
    simp only [paperProperGoodEvent, hp,mem_inter_iff,mem_ofPred_eq,f,w,
      Sum.forall,Sum.elim_inl,Sum.elim_inr,Prod.forall,div_eq_mul_inv,N,Nat.succPNat_coe]
    rfl
  have hcard : (Fintype.card J : ℝ) ≤ 4*(n : ℝ)^2 := by
    have hnpos := n.pos
    have hnat : Fintype.card J ≤ 4*(n : ℕ)^2 := by
      simp only [J,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
      nlinarith
    exact_mod_cast hnat
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hcoeff : μ E ≤ ENNReal.ofReal (4*(K+1)*Real.exp (-(c/2)*(n : ℝ)^δ)) := by
    apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).mpr
    change μ.real E ≤ _
    calc
      _ ≤ ∑ j : J, μ.real {x | A*(n : ℝ)^(κ*h)*w j < f j x} :=
        measureReal_iUnion_fintype_le _
      _ ≤ (Fintype.card J : ℝ)*Real.exp (-((n : ℝ)^h)) := by
        simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
          (Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => htail j)
      _ ≤ 4*(n : ℝ)^2*Real.exp (-c*(n : ℝ)^δ) := by
        apply mul_le_mul hcard _ (Real.exp_pos _).le (by positivity)
        apply Real.exp_le_exp.mpr
        have ht := mul_le_mul (show c ≤ 1 by dsimp only [c]; exact (min_le_right _ _).trans (by norm_num))
          (Real.rpow_le_rpow_of_exponent_le hn1 (min_le_right δ₀ h))
          (by positivity : 0 ≤ (n : ℝ)^δ) (by norm_num : (0 : ℝ) ≤ 1)
        linarith
      _ ≤ 4*(K*Real.exp (-(c/2)*(n : ℝ)^δ)) := by
        have ht := hpoly (n : ℝ) hn1
        rw [Real.rpow_two] at ht
        nlinarith
      _ ≤ _ := by nlinarith [Real.exp_pos (-(c/2)*(n : ℝ)^δ)]
  have hgap₀ := hgap p hp hpl hph n m hn hhalf ι
  have he : Real.exp (-b*(n : ℝ)^δ₀) ≤ Real.exp (-(c/2)*(n : ℝ)^δ) := by
    apply Real.exp_le_exp.mpr
    have ht := mul_le_mul (show c/2 ≤ b by have := min_le_left b (1/2 : ℝ); dsimp only [c]; linarith)
      (Real.rpow_le_rpow_of_exponent_le hn1 (min_le_left δ₀ h))
      (by positivity : 0 ≤ (n : ℝ)^δ) hb.le
    linarith
  rw [hevent]
  apply (measure_union_le _ _).trans
  apply (add_le_add (hgap₀.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left he hB.le))) hcoeff).trans_eq
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

end Riesz2.DecayShort
