/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.PaperGoodEventPart4
public import Riesz2.DecayShort.PaperHessianMoments

/-!
# Exceptional estimates on the short-range good event

The probability bound applies Markov directly to the conditions of
equation (4.10). The fourth moment is bounded through compensated variances
as in the proof of Lemma 4.8.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal ContDiff Topology

namespace Riesz2.DecayShort

/-- Probability and exceptional Hessian bounds of Lemma 4.8 for
equation (4.10), uniformly on compact positive temperature intervals.
Every fixed polynomial weight is permitted, as in the weighted exceptional estimate.
The variance condition uses any realization of the physical energy. -/
theorem paper_exceptional_event_estimates (s : ℝ) (hs : 1 < s) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ h : ℝ, 0 < h → ∃ δ : ℝ, 0 < δ ∧
      ∀ (θ : PhysicalCutoff) (βlo βhi : ℝ), 0 < βlo → βlo ≤ βhi →
      ∃ A : ℝ, 1 ≤ A ∧ ∀ a : ℝ, ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ (n : ℕ+) (m : ℕ) (hn : (n : ℕ) ≤ (((n : ℕ)+m).succPNat : ℕ)),
        2 ≤ (n : ℕ)+m+1 → 2*(n : ℕ) ≤ (n : ℕ)+m+1 → ∀ b : Bool,
      ∀ (U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ),
      (∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) //
        y ∈ gapAmbientDomain ((n : ℕ)+m).succPNat},
        U y.val = p.val.1 * physicalAmbientGapEnergy p ((n : ℕ)+m).succPNat y) →
      let F := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
        ∑ i, (θ.val (((n : ℝ)^h)⁻¹*x i) + if b then θ.val (((n : ℝ)^h)⁻¹*(x i)⁻¹) else 0)
      let K := fun x => p.val.1⁻¹*(p.val.1*F x-Real.log
        (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal))
      let μ := (activeTiltedGapLaw p ((n : ℕ)+m).succPNat n hn θ h b).comap
        ((↑) : AffineSimplex.chartDomain n ((n+m : ℕ)+1) → EuclideanSpace ℝ (Fin (n : ℕ)))
      let T := fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) =>
        ‖fderiv ℝ (fderiv ℝ K) x.val‖
      let E := (paperProperGoodEvent p n m U h (A*(n : ℝ)^(κ*h)))ᶜ
      μ E ≤ ENNReal.ofReal (C*Real.exp (-c*(n : ℝ)^δ)) ∧
      ENNReal.ofReal ((n : ℝ)^a)*eLpNorm T 2 (μ.restrict E) ≤
        ENNReal.ofReal (C*Real.exp (-c*(n : ℝ)^δ)) := by
  obtain ⟨κ,hκ,hprob⟩ := paper_proper_good_event_probability s hs
  refine ⟨κ,hκ,fun h hh => ?_⟩
  obtain ⟨δ,hδ,hprob⟩ := hprob h hh
  refine ⟨δ,hδ,fun θ βlo βhi hlo hle => ?_⟩
  obtain ⟨A,B,b,hA,hB,hb,hprob⟩ := hprob θ βlo βhi hlo hle
  obtain ⟨M,hM,hfour⟩ := paper_hessian_fourth_moments s hs θ βlo βhi h hlo hle hh
  refine ⟨A,hA,fun a => ?_⟩
  obtain ⟨C,hC,hrare⟩ := ExceptionalEvent.internal_weighted_exceptional (d := 2) (a := a) hδ hb hB hM
  refine ⟨B+C,b/8,by positivity,by positivity,?_⟩
  intro p hp hpl hph n m hn hN hhalf b' U hv F K μ T E
  have htail : μ E ≤ ENNReal.ofReal (B*Real.exp (-b*(n : ℝ)^δ)) :=
    hprob p hp hpl hph n m hn hN hhalf b' U hv
  obtain ⟨hT,_,hTnorm⟩ := hfour p hp hpl hph n m hn hN hhalf b'
  have hExp : Real.exp (-b*(n : ℝ)^δ) ≤ Real.exp (-(b/8)*(n : ℝ)^δ) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n) δ])
  constructor
  · apply htail.trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul (by linarith) hExp (Real.exp_pos _).le (by positivity)
  · have ht := hrare (n : ℝ) (by exact_mod_cast n.pos) μ T E hT
      (by norm_num only [Real.rpow_ofNat]; exact hTnorm) htail
    exact ht.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (by linarith : C ≤ B+C) (Real.exp_pos _).le))

end Riesz2.DecayShort
