/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.PhysicalDecayPart2
public import Riesz2.DecayShort.PaperInteriorComparisonPart3
public import Riesz2.DecayShort.PaperGoodEventPart3
import all Riesz2.DecayShort.PhysicalComparisonPart4
public import Riesz2.ToMathlib.NaturalMatrixPerturbation

/-!
# Uniform proper physical short-range decay

The proper-marginal clause of Proposition 4.10, with the
quantifier order and common constants on every compact temperature interval.
The bounded auxiliary matrix and interior comparison are the fields of
equation (4.13) on the event in equation (4.10).
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal

namespace Riesz2.DecayShort.PhysicalDecay

open PhysicalComparison

set_option backward.isDefEq.respectTransparency false in
/-- Internal exceptional envelope for Proposition 4.10 and Lemma 4.8.
It includes the identity matrix on the bad set and absorbs every fixed
real polynomial weight. The truncation level precedes that weight. The loss and
tail exponents precede the cutoff and every positive compact temperature interval. -/
theorem internal_paper_exceptional_envelope_compact (s : ℝ) (hs : 1 < s) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ h : ℝ, 0 < h → ∃ δ : ℝ, 0 < δ ∧
      ∀ (θ : PhysicalCutoff) (βlo βhi : ℝ), 0 < βlo → βlo ≤ βhi →
      ∃ A : ℝ, 1 ≤ A ∧ ∀ a : ℝ,
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ (n : ℕ+) (m : ℕ) (hn : (n : ℕ) ≤ (((n : ℕ)+m).succPNat : ℕ)),
        4 ≤ (n : ℕ)+m+1 → 2*(n : ℕ) ≤ (n : ℕ)+m+1 → ∀ b : Bool,
        ∀ (W : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ),
        (∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) //
          y ∈ gapAmbientDomain ((n : ℕ)+m).succPNat},
          W y.val = p.val.1*physicalAmbientGapEnergy p ((n : ℕ)+m).succPNat y) →
        let F := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
          ∑ i, (θ.val (((n : ℝ)^h)⁻¹*x i) +
            if b then θ.val (((n : ℝ)^h)⁻¹*(x i)⁻¹) else 0)
        let K := fun x => p.val.1⁻¹*(p.val.1*F x-
          Real.log (∫ z : EuclideanSpace ℝ (Fin m),
            (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal))
        let μ := (activeTiltedGapLaw p ((n : ℕ)+m).succPNat n hn θ h b).comap
          ((↑) : AffineSimplex.chartDomain n ((n+m : ℕ)+1) → EuclideanSpace ℝ (Fin (n : ℕ)))
        let E := (paperProperGoodEvent p n m W h (A*(n : ℝ)^(κ*h)))ᶜ
        let Z := E.indicator (fun x => ‖fderiv ℝ (fderiv ℝ K) x.val‖+1)
        Measurable Z ∧ MemLp Z 2 μ ∧
          (n : ℝ)^a*(eLpNorm Z 2 μ).toReal ≤ C*Real.exp (-c*(n : ℝ)^δ) := by
  classical
  obtain ⟨κ,hκ,hprob⟩ := paper_exceptional_event_estimates s hs
  refine ⟨κ,hκ,fun h hh => ?_⟩
  obtain ⟨δ,hδ,hprob⟩ := hprob h hh
  refine ⟨δ,hδ,fun θ βlo βhi hlo hle => ?_⟩
  obtain ⟨A,hA,hprob⟩ := hprob θ βlo βhi hlo hle
  obtain ⟨B,c,hB,hc,hprob⟩ := hprob 0
  obtain ⟨M,hM,hmom⟩ := paper_hessian_fourth_moments
    s hs θ βlo βhi h hlo hle hh
  refine ⟨A,hA,fun a => ?_⟩
  obtain ⟨C,hC,hbound⟩ := ExceptionalEvent.internal_weighted_exceptional
    (d := 2) (a := a) hδ hc hB (show 0 < M+1 by linarith)
  refine ⟨C,c/8,hC,by positivity,?_⟩
  intro p hp hpl hph n m hn hN hhalf b W hvW F K μ E Z
  have hs : 1 < p.val.2 := by simpa only [hp] using hs
  let _ : IsProbabilityMeasure μ := activeTilt_proper_probability p n m hn θ h b
  let T := fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) =>
    ‖fderiv ℝ (fderiv ℝ K) x.val‖
  obtain ⟨hT,hTmem,hTnorm⟩ := hmom p hp hpl hph n m hn (by omega) hhalf b
  change Measurable T at hT
  change MemLp T 4 μ at hTmem
  have hTplus : Measurable (fun x => T x+1) := hT.add measurable_const
  have hE : MeasurableSet E := (measurableSet_paperProperGoodEvent p n m W h _).compl
  have hnorm : eLpNorm (fun x => T x+1) 4 μ ≤ ENNReal.ofReal ((M+1)*(n : ℝ)^2) := by
    have hone : eLpNorm (fun _ : AffineSimplex.chartDomain n ((n+m : ℕ)+1) => (1 : ℝ)) 4 μ = 1 := by
      simp [eLpNorm_const', (by norm_num : (4 : ℝ≥0∞) ≠ 0), (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)]
    refine (eLpNorm_add_le (by norm_num)).trans ((add_le_add hTnorm hone.le).trans ?_)
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
    nlinarith [sq_nonneg ((n : ℝ)-1)]
  have hmem : MemLp (fun x => T x+1) 2 μ :=
    (hTmem.add (memLp_const (1 : ℝ))).mono_exponent (by norm_num)
  have hZ : MemLp Z 2 μ := hmem.indicator hE.nullMeasurableSet
  refine ⟨hTplus.indicator hE,hZ,?_⟩
  have he := eLpNorm_indicator_eq_eLpNorm_restrict (f := fun x => T x+1)
    (p := (2 : ℝ≥0∞)) (μ := μ) hE.nullMeasurableSet
  have hb := hbound (n : ℝ) (by exact_mod_cast n.pos) μ (fun x => T x+1) E hTplus
    (by norm_num only [Real.rpow_ofNat]; exact hnorm)
    (hprob p hp hpl hph n m hn (by omega) hhalf b W hvW).1
  rw [← he] at hb
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity)] at ht
  exact ht

/-- Internal maximum-principle step of Proposition 4.10,
for the actual auxiliary physical matrix on any measured base. The bound
uses the Euclidean vector essential supremum and the scalar source norm. -/
theorem internal_paper_frozen_maximum (p : Parameters) (hs : 1 < p.val.2)
    (n : ℕ+) (m : ℕ)
    (W : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ) (θ : PhysicalCutoff) (h : ℝ) (hh : 0 < h)
    (b : Bool) (D : ℝ) {α : Type*} [MeasurableSpace α]
    (τ : α → AffineSimplex.chartDomain n ((n+m : ℕ)+1)) (hτ : Measurable τ)
    (ν : Measure α) (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν) (u : Fin (n : ℕ) → Q.1)
    (hu : WeightedWeakSolution Q
      (fun x => p.val.1 • paperFrozenPhysicalMatrix p n m W θ h b D (τ x))
      ⊤ (fun i => if i=i₀ then χ else 0) u) :
    eLpNorm (fun x => WithLp.toLp 2 (fun i => (u i).val x)) ∞ ν ≤
      ENNReal.ofReal ((p.val.1*(n : ℝ)^(-(p.val.2+2)*h))⁻¹) * eLpNorm χ ∞ ν := by
  classical
  let H := fun x => p.val.1 • paperFrozenPhysicalMatrix p n m W θ h b D (τ x)
  let a := p.val.1*(n : ℝ)^(-(p.val.2+2)*h)
  have ha : 0 < a := mul_pos p.property.1
    (Real.rpow_pos_of_pos (by exact_mod_cast n.pos) _)
  obtain ⟨hm,_,hsym,_⟩ := paperFrozenMatrices_measurable_symmetric p hs n m W θ h hh b D
  have hHm : ∀ i j, Measurable (fun x => H x i j) :=
    AbstractEnergy.scaled_measurable _ _ (fun i j => (hm i j).comp hτ)
  have hH : ∀ᵐ x ∂ν, (∀ i j, H x i j = H x j i) ∧
      ∀ z : Fin (n : ℕ) → ℝ, a*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*H x i j*z j := by
    apply ae_of_all
    intro x
    refine ⟨fun i j => congrArg (fun t : ℝ => p.val.1*t) (hsym (τ x) i j),fun z => ?_⟩
    have ht := mul_le_mul_of_nonneg_left
      (paperFrozenPhysicalMatrix_lower p hs n m W θ h hh b D (τ x) z) p.property.1.le
    simpa only [H,a, Matrix.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc,
      mul_left_comm] using ht
  have he : eLpNorm (fun x => WithLp.toLp 2
      (fun i => ((if i=i₀ then χ else 0 : Lp ℝ 2 ν)) x)) ∞ ν = eLpNorm χ ∞ ν := by
    rw [← eLpNorm_norm _ (VectorRadial.memLp_values
      (fun i => if i=i₀ then χ else 0)).aestronglyMeasurable]
    rw [← eLpNorm_norm χ (Lp.aestronglyMeasurable χ)]
    apply eLpNorm_congr_ae
    filter_upwards [Lp.coeFn_zero ℝ 2 ν] with x hx
    change (0 : Lp ℝ 2 ν) x = 0 at hx
    have hz : (WithLp.toLp 2 (fun i => (if i=i₀ then χ else 0 : Lp ℝ 2 ν) x) :
        EuclideanSpace ℝ (Fin (n : ℕ))) = EuclideanSpace.single i₀ (χ x) := by
      ext i
      by_cases hi : i=i₀
      · simp [hi,EuclideanSpace.single]
      · simpa only [ite_eq_right hi, EuclideanSpace.single, PiLp.single_apply, ite_eq_right hi] using hx
    rw [hz]
    simp [EuclideanSpace.single,PiLp.norm_single]
  have ht := AbstractEnergy.weakSolution_eLpNorm_top_le Q hQ H hHm a ha hH
    ⊤ (fun i => if i=i₀ then χ else 0) u hu
  rwa [he] at ht

set_option backward.isDefEq.respectTransparency false in
/-- Internal actual-residual construction in Proposition 4.10.
The only envelope premise is on this internal helper. The physical
exceptional theorem supplies it below. The maximum principle supplies
the boundedness of the auxiliary weak solution here. -/
theorem internal_paper_proper_residual (p : Parameters) (hs : 1 < p.val.2)
    (n : ℕ+) (m : ℕ) (hn : (n : ℕ) ≤ (((n : ℕ)+m).succPNat : ℕ))
    (W : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ)
    (θ : PhysicalCutoff) (h : ℝ) (hh : 0 < h) (b : Bool) (D : ℝ)
    {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (τ : α → AffineSimplex.chartDomain n ((n+m : ℕ)+1))
    (hτ : MeasurePreserving τ ν ((activeTiltedGapLaw p ((n : ℕ)+m).succPNat n hn θ h b).comap
      ((↑) : AffineSimplex.chartDomain n ((n+m : ℕ)+1) → EuclideanSpace ℝ (Fin (n : ℕ)))))
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν) (hχ : eLpNorm χ ∞ ν < ⊤)
    (u : Fin (n : ℕ) → Q.1)
    (hu : WeightedWeakSolution Q
      (fun x => p.val.1 • paperFrozenPhysicalMatrix p n m W θ h b D (τ x))
      ⊤ (fun i => if i=i₀ then χ else 0) u) :
    let F := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      ∑ i, (θ.val (((n : ℝ)^h)⁻¹*x i) +
        if b then θ.val (((n : ℝ)^h)⁻¹*(x i)⁻¹) else 0)
    let K := fun x => p.val.1⁻¹*(p.val.1*F x-
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal))
    let μ := (activeTiltedGapLaw p ((n : ℕ)+m).succPNat n hn θ h b).comap
      ((↑) : AffineSimplex.chartDomain n ((n+m : ℕ)+1) → EuclideanSpace ℝ (Fin (n : ℕ)))
    let E := (paperProperGoodEvent p n m W h D)ᶜ
    let Z := E.indicator (fun x => ‖fderiv ℝ (fderiv ℝ K) x.val‖+1)
    MemLp Z 2 μ →
    ∃ g : Fin (n : ℕ) → Lp ℝ 2 ν,
      (∀ᵐ x ∂ν, ∀ i, g i x = ∑ j,
        ((p.val.1 • hessianMatrix K (τ x).val) i j-
          (p.val.1 • paperFrozenPhysicalMatrix p n m W θ h b D (τ x)) i j)*(u j).val x) ∧
      ‖WithLp.toLp 2 g‖ ≤ (n : ℝ)^2 *
        ((p.val.1*(n : ℝ)^(-(p.val.2+2)*h))⁻¹ * (eLpNorm χ ∞ ν).toReal) *
        (p.val.1*(eLpNorm Z 2 μ).toReal) := by
  classical
  intro F K μ E Z hZ
  have hK := (PhysicalFibres.active_marginal_curvature p hs n m n.pos (Equiv.refl _) θ h hh b).1
  change ContDiffOn ℝ (⊤ : ℕ∞) K (AffineSimplex.chartDomain n ((n+m : ℕ)+1)) at hK
  let H := fun x => p.val.1 • hessianMatrix K (τ x).val
  let M := fun x => p.val.1 • paperFrozenPhysicalMatrix p n m W θ h b D (τ x)
  let a := p.val.1*(n : ℝ)^(-(p.val.2+2)*h)
  let R := a⁻¹*(eLpNorm χ ∞ ν).toReal
  let T := fun x => p.val.1*Z (τ x)
  have ha : 0 < a := mul_pos p.property.1
    (Real.rpow_pos_of_pos (by exact_mod_cast n.pos) _)
  have hHm : ∀ i j, Measurable (fun x => H x i j) :=
    AbstractEnergy.scaled_measurable _ _ (fun i j =>
      (measurable_hessianMatrix (AffineSimplex.isOpen_chartDomain _ _) hK i j).comp hτ.measurable)
  have hMm : ∀ i j, Measurable (fun x => M x i j) :=
    AbstractEnergy.scaled_measurable _ _ (fun i j =>
      ((paperFrozenMatrices_measurable_symmetric p hs n m W θ h hh b D).1 i j).comp hτ.measurable)
  have hT : MemLp T 2 ν := (hZ.comp_measurePreserving hτ).const_mul p.val.1
  have hT0 : ∀ᵐ x ∂ν, 0 ≤ T x := ae_of_all ν fun x => by
    dsimp only [T,Z]
    exact mul_nonneg p.property.1.le (indicator_nonneg (fun _ _ => by positivity) (τ x))
  have hentry : ∀ᵐ x ∂ν, ∀ i j, |(H x-M x) i j| ≤ T x := by
    apply ae_of_all
    intro x i j
    by_cases hx : τ x ∈ paperProperGoodEvent p n m W h D
    · have hm : paperFrozenPhysicalMatrix p n m W θ h b D (τ x) = hessianMatrix K (τ x).val := by
        simp only [paperFrozenPhysicalMatrix,ite_eq_left hx]
        rfl
      simp only [H,M,hm,sub_self,Matrix.zero_apply,abs_zero]
      dsimp only [T,Z]
      exact mul_nonneg p.property.1.le (indicator_nonneg (fun _ _ => by positivity) (τ x))
    · have hm := (paperFrozenMatrices_off_event p n m W θ h b D (τ x) hx).1
      have he : Z (τ x) = ‖fderiv ℝ (fderiv ℝ K) (τ x).val‖+1 := indicator_of_mem hx _
      have hKx := (hK.contDiffAt ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds (τ x).property)).of_le
        (show (2 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) by norm_num)
      have hb : |hessianMatrix K (τ x).val i j| ≤ ‖fderiv ℝ (fderiv ℝ K) (τ x).val‖ := by
        rw [hessianMatrix_entry hKx]
        have ht := ContinuousLinearMap.le_opNorm₂ (fderiv ℝ (fderiv ℝ K) (τ x).val)
          (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)
        simpa [EuclideanSpace.single,PiLp.norm_single] using ht
      have hi : |(1 : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ) i j| ≤ 1 := by
        simp only [Matrix.one_apply]; split_ifs <;> norm_num
      dsimp only [H,M,T]
      rw [hm,Matrix.sub_apply,Matrix.smul_apply,Matrix.smul_apply,smul_eq_mul,smul_eq_mul,
        ← mul_sub,abs_mul,abs_of_pos p.property.1,he]
      exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add hb hi)) p.property.1.le
  -- Proposition 3.6 bounds the auxiliary vector before multiplication
  -- by the exceptional Hessian in Proposition 4.10.
  have hmax := internal_paper_frozen_maximum p hs n m W θ h hh b D τ hτ.measurable ν Q hQ i₀ χ u hu
  have hU : ∀ᵐ x ∂ν, ‖(WithLp.toLp 2 (fun i => (u i).val x) : EuclideanSpace ℝ (Fin (n : ℕ)))‖ ≤ R := by
    have hle := ae_le_eLpNormEssSup (f := fun x => WithLp.toLp 2 (fun i => (u i).val x)) (μ := ν)
    rw [← eLpNorm_exponent_top (VectorRadial.memLp_values (fun i => (u i).val)).aestronglyMeasurable] at hle
    filter_upwards [hle] with x hx
    have ht := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hχ.ne) (hx.trans hmax)
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (inv_nonneg.mpr ha.le),
      enorm_eq_nnnorm,ENNReal.coe_toReal,coe_nnnorm,R,a] using ht
  obtain ⟨g,hg,hgn⟩ := internal_action_of_envelope (fun x => H x-M x)
    (fun i j => (hHm i j).sub (hMm i j)) T hT hT0 (fun i => (u i).val) R
    (by dsimp only [R]; positivity) hentry hU
  refine ⟨g,hg,hgn.trans_eq ?_⟩
  have hn : eLpNorm T 2 ν = ENNReal.ofReal p.val.1*eLpNorm Z 2 μ := by
    change eLpNorm (p.val.1 • (Z ∘ τ)) 2 ν = _
    rw [eLpNorm_const_smul,Real.enorm_eq_ofReal_abs,abs_of_pos p.property.1,
      eLpNorm_comp_measurePreserving hZ.aestronglyMeasurable hτ]
  rw [hn,ENNReal.toReal_mul,ENNReal.toReal_ofReal p.property.1.le]

set_option backward.isDefEq.respectTransparency false in
/-- The complete proper auxiliary profile of Proposition 4.10, obtained from
Lemma 4.9 and Proposition 4.5, with the physical statement's beta-independent
exponent order and compact-temperature prefactors. -/
theorem paper_frozen_proper_decay_compact (s : ℝ) (hs : 1 < s)
    (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ (θ : PhysicalCutoff) (h : ℝ), 0 < h →
      ∀ A : ℝ, 1 ≤ A → ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : Parameters), p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (n : ℕ+) (m : ℕ)
        (W : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ),
        (∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) //
          y ∈ gapAmbientDomain ((n : ℕ)+m).succPNat},
          W y.val = p.val.1*physicalAmbientGapEnergy p ((n : ℕ)+m).succPNat y) →
        2 ≤ (n : ℕ)+m+1 → 2*(n : ℕ) ≤ (n : ℕ)+m+1 → ∀ (b : Bool)
        (α : Type*) [MeasurableSpace α]
        (τ : α → AffineSimplex.chartDomain n ((n+m : ℕ)+1)), Measurable τ →
        ∀ (ν : Measure α) [IsProbabilityMeasure ν] (Q : ScalarFormData ν),
        IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
        ∀ (i₀ : Fin (n : ℕ)), (n : ℝ)/4 ≤ (i₀.val : ℝ)+1 →
          (i₀.val : ℝ)+1 ≤ 3*(n : ℝ)/4 → ∀ χ : Lp ℝ 2 ν,
        let H := fun x => p.val.1 • paperFrozenPhysicalMatrix p n m W θ h b (A*(n : ℝ)^(κ*h)) (τ x)
        let f := fun i => if i=i₀ then χ else 0
        (∃! u : Fin (n : ℕ) → Q.1, WeightedWeakSolution Q H ⊤ f u) ∧
        ∀ u : Fin (n : ℕ) → Q.1, WeightedWeakSolution Q H ⊤ f u →
          ∀ j : Fin (n : ℕ), ‖(u j).val‖ ≤ C*(n : ℝ)^(r*h)*
            ((1+|(j.val : ℝ)-(i₀.val : ℝ)|)^(-p.val.2) +
              (n : ℝ)^(-(p.val.2-1/2)) +
              (((n : ℕ)+m+1 : ℕ) : ℝ)^(-(1/2 : ℝ)))*‖χ‖ := by
  classical
  obtain ⟨rc,hrc,hcomp⟩ := paper_fixed_scalar_form_comparison s hs κ hκ
  obtain ⟨rv,hrv,hdecay⟩ := paper_auxiliary_decay_compact s hs κ hκ
  refine ⟨rc+rv,add_nonneg hrc hrv,?_⟩
  intro θ h hh A hA βlo βhi hlo hle
  obtain ⟨Cc,hCc,hcomp⟩ := hcomp θ h hh A hA βlo βhi hlo hle
  obtain ⟨Cv,hCv,hdecay⟩ := hdecay θ h hh A hA βlo βhi hlo hle
  refine ⟨Cc+Cv,by linarith,?_⟩
  intro p hp hpl hph
  subst s
  have hs : 1 < p.val.2 := hs
  have hcomp := hcomp p rfl hpl hph
  have hdecay := hdecay p rfl hpl hph
  intro n m W hvW hN hhalf b α _ τ hτ ν _ Q hQ hcons i₀ hlo hhi χ H f
  have hpair := hcomp n m W hvW hN hhalf b α τ hτ ν Q hQ hcons i₀ hlo hhi χ
  refine ⟨hpair.1,?_⟩
  intro u hu j
  obtain ⟨v,hv,_⟩ := (hdecay n m W hvW hN hhalf b α τ hτ ν Q hQ hcons i₀ χ).1
  have hvn := (hdecay n m W hvW hN hhalf b α τ hτ ν Q hQ hcons i₀ χ).2 v hv j
  -- equation (4.14) followed by optimal core decay.
  have hc := (hpair.2.2 u v hu hv).1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  let P := (n : ℝ)^((rc+rv)*h)
  let R := (n : ℝ)^(-(p.val.2-1/2))+
    (((n : ℕ)+m+1 : ℕ) : ℝ)^(-(1/2 : ℝ))
  let d := (1+|(j.val : ℝ)-(i₀.val : ℝ)|)^(-p.val.2)
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have hpC : (n : ℝ)^(rc*h) ≤ P := Real.rpow_le_rpow_of_exponent_le hn1
    (by nlinarith : rc*h ≤ (rc+rv)*h)
  have hpV : (n : ℝ)^(rv*h) ≤ P := Real.rpow_le_rpow_of_exponent_le hn1
    (by nlinarith : rv*h ≤ (rc+rv)*h)
  have hc' : ‖(u j-v j).val‖ ≤ Cc*P*R*‖χ‖ := by
    apply (PiLp.norm_apply_le (WithLp.toLp 2 (fun i => (u i-v i).val)) j).trans
    apply (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans hc |>.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpC (by linarith)) hR) (norm_nonneg χ)
  have hv' : ‖(v j).val‖ ≤ Cv*P*d*‖χ‖ := hvn.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpV (by linarith)) hd) (norm_nonneg χ))
  have huj : (u j).val = (u j-v j).val+(v j).val := by
    change (u j).val = ((u j).val-(v j).val)+(v j).val
    abel
  change _ ≤ (Cc+Cv)*P*((d+(n : ℝ)^(-(p.val.2-1/2)))+
    (((n : ℕ)+m+1 : ℕ) : ℝ)^(-(1/2 : ℝ)))*‖χ‖
  rw [huj]
  apply (norm_add_le _ _).trans
  apply (add_le_add hc' hv').trans
  have hc0 : 0 ≤ Cc := by linarith
  have hv0 : 0 ≤ Cv := by linarith
  have h₁ := mul_nonneg (mul_nonneg (mul_nonneg hc0 hP) hd) (norm_nonneg χ)
  have h₂ := mul_nonneg (mul_nonneg (mul_nonneg hv0 hP) hR) (norm_nonneg χ)
  dsimp only [R] at *
  nlinarith only [h₁,h₂]

set_option backward.isDefEq.respectTransparency false in
/-- Proper-marginal clause of Proposition 4.10 in exterior-chart
coordinates. The loss exponent precedes h and beta, the tail exponent precedes
the cutoff and beta, and the constants are common on each positive compact interval. -/
theorem proper_physical_decay_compact_chart (s : ℝ) (hs : 1 < s) :
    ∃ q : ℝ, 0 < q ∧ ∀ h : ℝ, 0 < h → ∃ δ : ℝ, 0 < δ ∧
      ∀ (θ : PhysicalCutoff) (βlo βhi : ℝ), 0 < βlo → βlo ≤ βhi →
      ∃ A c : ℝ, 1 ≤ A ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ (n : ℕ+) (m : ℕ) (hn : (n : ℕ) ≤ (((n : ℕ)+m).succPNat : ℕ)),
        4 ≤ (n : ℕ)+m+1 → 2 ≤ (n : ℕ) →
        2*(n : ℕ) ≤ (n : ℕ)+m+1 → ∀ b : Bool,
        let N := ((n : ℕ)+m).succPNat
        let ν := activeTiltedGapLaw p N n hn θ h b
        0 < tiltNormalizer p N n hn θ h b ∧
        tiltNormalizer p N n hn θ h b < ⊤ ∧ IsProbabilityMeasure ν ∧
        ∃ (V : EuclideanSpace ℝ (Fin (n : ℕ)) → ℝ) (Q : ScalarFormData ν),
          IsEuclideanGibbsPotential volume ν (properMarginalDomain n N) V ∧
          IsNeumannRealization (properMarginalDomain n N) Q ∧
          IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
          ∀ i₀ : Fin (n : ℕ), (n : ℕ) ≤ 4*(i₀.val+1) →
            4*(i₀.val+1) ≤ 3*(n : ℕ) → ∀ χ : Lp ℝ 2 ν,
          eLpNorm χ ∞ ν < ⊤ →
          (∃! u : Fin (n : ℕ) → Q.1,
            WeightedWeakSolution Q (hessianMatrix V) ⊤ (fun i => if i=i₀ then χ else 0) u) ∧
          (∀ u : Fin (n : ℕ) → Q.1,
            WeightedWeakSolution Q (hessianMatrix V) ⊤ (fun i => if i=i₀ then χ else 0) u →
            ∀ j : Fin (n : ℕ), ENNReal.ofReal ‖(u j).val‖ ≤
              ENNReal.ofReal (A*(n : ℝ)^(q*h)*
                ((1+|(j.val : ℝ)-(i₀.val : ℝ)|)^(-p.val.2)+
                  (n : ℝ)^(-(p.val.2-1/2))+(N : ℝ)^(-(1/2 : ℝ)))) *
                (ENNReal.ofReal ‖χ‖+ENNReal.ofReal (Real.exp (-c*(n : ℝ)^δ))*eLpNorm χ ∞ ν)) := by
  classical
  obtain ⟨κ,hκ,henv⟩ := internal_paper_exceptional_envelope_compact s hs
  obtain ⟨r,hr,hdec⟩ := paper_frozen_proper_decay_compact s hs κ hκ.le
  refine ⟨r+1,by linarith,fun h hh => ?_⟩
  obtain ⟨δ,hδ,henv⟩ := henv h hh
  refine ⟨δ,hδ,fun θ βlo βhi hlo hle => ?_⟩
  obtain ⟨A₀,hA₀,henv⟩ := henv θ βlo βhi hlo hle
  obtain ⟨C₀,hC₀,hdec⟩ := hdec θ h hh A₀ hA₀ βlo βhi hlo hle
  obtain ⟨C₁,c,hC₁,hc,henv⟩ := henv (2+2*(s+2)*h)
  obtain ⟨B,hB,hinsert⟩ := internal_insert_exponential_error (t := s-1/2) hδ hc
  let D₀ := C₀+βlo⁻¹*C₁
  let A := max 1 (B*D₀)
  refine ⟨A,c/2,le_max_left _ _,by positivity,?_⟩
  intro p hp hpl hph
  subst s
  have hs : 1 < p.val.2 := hs
  have hβ : 0 < p.val.1 := p.property.1
  have hβinv : p.val.1⁻¹ ≤ βlo⁻¹ := (inv_le_inv₀ hβ hlo).mpr hpl
  have hdec := hdec p rfl hpl hph
  have henv := henv p rfl hpl hph
  intro n m hn hN _hn2 hhalf b N ν
  obtain ⟨hZ0,hZt,hprob,_⟩ := ProperMarginalChart.activeTiltedGapLaw_density_valid p n m hn θ h b
  let _ : IsProbabilityMeasure ν := hprob
  refine ⟨hZ0,hZt,hprob,?_⟩
  let U := AffineSimplex.chartDomain n ((n+m : ℕ)+1)
  let F := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
    ∑ i, (θ.val (((n : ℝ)^h)⁻¹*x i) +
      if b then θ.val (((n : ℝ)^h)⁻¹*(x i)⁻¹) else 0)
  let K := fun x => p.val.1⁻¹*(p.val.1*F x-
    Real.log (∫ z : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal))
  let a := p.val.1*(n : ℝ)^(-(p.val.2+2)*h)
  obtain ⟨V,k,Q,hVk,hG,hNeum,hQ,hcons,hsupp,hHb,hl,hHeq,hsol⟩ :=
    internal_proper_realization p hs n m hn θ h hh b
  rw [← ProperMarginalChart.baseDomain_eq_properMarginalDomain n m]
  refine ⟨V,Q,hG,hNeum,hQ,hcons,?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have ha : 0 < a := mul_pos p.property.1 (Real.rpow_pos_of_pos hn0 _)
  have hU : IsOpen U := AffineSimplex.isOpen_chartDomain _ _
  have hne : U.Nonempty := by
    refine ⟨WithLp.toLp 2 (fun _ => (1 : ℝ)),?_,?_⟩
    · intro i; exact zero_lt_one
    · simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
      norm_cast
      omega
  obtain ⟨τ,hτ,_,hτval⟩ := internal_retained_projection ν U hU.measurableSet hne hsupp
  obtain ⟨W,_,hvW,_⟩ := MarginalHessian.physical_energy_tensors p N
  change (EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ) at W
  let D := A₀*(n : ℝ)^(κ*h)
  let M := fun x => p.val.1 • paperFrozenPhysicalMatrix p n m W θ h b D (τ x)
  obtain ⟨hm,_,hsym,_⟩ := paperFrozenMatrices_measurable_symmetric p hs n m W θ h hh b D
  have hMm : ∀ i j, Measurable (fun x => M x i j) :=
    AbstractEnergy.scaled_measurable _ _ (fun i j => (hm i j).comp hτ.measurable)
  have hMs : ∀ᵐ x ∂ν, ∀ i j, M x i j=M x j i := ae_of_all ν fun x i j =>
    congrArg (fun t : ℝ => p.val.1*t) (hsym (τ x) i j)
  obtain ⟨Cp,hCp,hupper⟩ := paperFrozenPhysicalMatrix_upper θ
  let Bm := 1+Cp*(n : ℝ)^(4*h)+D*((2*∑' k : ℕ, (1+(k : ℝ))^(-p.val.2))+1)
  have hMb : ∃ Bm' : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ Bm' := by
    refine ⟨p.val.1*Bm,ae_of_all ν fun x i j => ?_⟩
    simp only [M,Matrix.smul_apply,smul_eq_mul,abs_mul,abs_of_pos p.property.1]
    apply mul_le_mul_of_nonneg_left _ p.property.1.le
    apply internal_entry_bound _ Bm (hsym (τ x))
      (fun z => (mul_nonneg (Real.rpow_nonneg hn0.le _) (Finset.sum_nonneg fun i _ => sq_nonneg (z i))).trans
        (paperFrozenPhysicalMatrix_lower p hs n m W θ h hh b D (τ x) z))
      (hupper p hs n m W hvW (by omega) hhalf h hh b D (by dsimp only [D]; positivity) (τ x))
  let μ := ν.comap ((↑) : U → EuclideanSpace ℝ (Fin (n : ℕ)))
  let E := (paperProperGoodEvent p n m W h D)ᶜ
  let Z := E.indicator (fun x => ‖fderiv ℝ (fderiv ℝ K) x.val‖+1)
  obtain ⟨_,hZ,hZbound⟩ := henv n m hn hN hhalf b W hvW
  change MemLp Z 2 μ at hZ
  change (n : ℝ)^(2+2*(p.val.2+2)*h)*(eLpNorm Z 2 μ).toReal ≤
    C₁*Real.exp (-c*(n : ℝ)^δ) at hZbound
  intro i₀ hlo hhi χ hχ
  refine ⟨hsol _,?_⟩
  intro u hu j
  have hloR : (n : ℝ)/4 ≤ (i₀.val : ℝ)+1 := by
    have ht : (n : ℝ) ≤ 4*((i₀.val : ℝ)+1) := by exact_mod_cast hlo
    linarith
  have hhiR : (i₀.val : ℝ)+1 ≤ 3*(n : ℝ)/4 := by
    have ht : (4 : ℝ)*(i₀.val+1) ≤ 3*(n : ℝ) := by exact_mod_cast hhi
    linarith
  obtain ⟨v,hv,_⟩ := (hdec n m W hvW (by omega) hhalf b _ τ hτ.measurable ν Q hQ hcons i₀ hloR hhiR χ).1
  have hvdec := (hdec n m W hvW (by omega) hhalf b _ τ hτ.measurable ν Q hQ hcons i₀ hloR hhiR χ).2 v hv j
  obtain ⟨g,hg,hgn⟩ := internal_paper_proper_residual p hs n m hn W θ h hh b D ν τ hτ Q hQ i₀ χ hχ v hv hZ
  have hg' : ∀ᵐ x ∂ν, ∀ i, g i x = ∑ l,
      (hessianMatrix V x i l-M x i l)*(v l).val x := by
    filter_upwards [hg,hsupp,hτval] with x hx hxu hτx i
    simpa only [hτx,← hHeq x hxu] using hx i
  -- Subtract and test on the natural physical energy domain. The theorem also
  -- justifies using the bounded auxiliary solution as a physical form element.
  have hcomp := (NaturalMatrixPerturbation.internal_comparison Q hQ (hessianMatrix V) M
    DifferentiatedPoisson.measurable_hessian_entries hMm hHb hMb hMs ⊤ a ha
    (hl.mono fun x hx z _ => hx z) (fun i => if i=i₀ then χ else 0) g u v hu hv hg').1
  have hainv : a⁻¹ = p.val.1⁻¹*(n : ℝ)^((p.val.2+2)*h) := by
    change (p.val.1*(n : ℝ)^(-(p.val.2+2)*h))⁻¹ = _
    rw [mul_inv_rev,← Real.rpow_neg hn0.le]
    rw [show -(-(p.val.2+2)*h) = (p.val.2+2)*h by ring, mul_comm]
  change ‖WithLp.toLp 2 g‖ ≤ (n : ℝ)^2 * (a⁻¹*(eLpNorm χ ∞ ν).toReal) *
    (p.val.1*(eLpNorm Z 2 μ).toReal) at hgn
  have herror : ‖WithLp.toLp 2 (fun i => (u i-v i).val)‖ ≤
      p.val.1⁻¹*C₁*Real.exp (-c*(n : ℝ)^δ)*(eLpNorm χ ∞ ν).toReal := by
    apply hcomp.trans
    apply (mul_le_mul_of_nonneg_left hgn (inv_nonneg.mpr ha.le)).trans
    calc
      _ = p.val.1⁻¹*((n : ℝ)^(2+2*(p.val.2+2)*h)*(eLpNorm Z 2 μ).toReal)*
          (eLpNorm χ ∞ ν).toReal := by
        rw [hainv,Real.rpow_add hn0,Real.rpow_two]
        rw [show 2*(p.val.2+2)*h = (p.val.2+2)*h+(p.val.2+2)*h by ring,Real.rpow_add hn0]
        field_simp [p.property.1.ne']
      _ ≤ _ := by
        have ht := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hZbound (inv_nonneg.mpr p.property.1.le))
          (show 0 ≤ (eLpNorm χ ∞ ν).toReal from ENNReal.toReal_nonneg)
        nlinarith only [ht]
  let P := (n : ℝ)^(r*h)
  let e := (1+|(j.val : ℝ)-(i₀.val : ℝ)|)^(-p.val.2)+
    (n : ℝ)^(-(p.val.2-1/2))+(N : ℝ)^(-(1/2 : ℝ))
  have hP : 1 ≤ P := Real.one_le_rpow hn1 (mul_nonneg hr hh.le)
  have he0 : 0 ≤ e := by dsimp only [e]; positivity
  have hC00 : 0 ≤ C₀ := by linarith
  have hD0 : 0 ≤ D₀ := by dsimp only [D₀]; positivity
  have hvdec' : ‖(v j).val‖ ≤ C₀*P*e*‖χ‖ := by
    simpa only [P,e,N,Nat.succPNat_coe] using hvdec
  have hv' : ‖(v j).val‖ ≤ D₀*P*e*‖χ‖ := hvdec'.trans (by
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg χ)
    apply mul_le_mul_of_nonneg_right _ he0
    apply mul_le_mul_of_nonneg_right _ (show 0 ≤ P from zero_le_one.trans hP)
    dsimp only [D₀]
    exact le_add_of_nonneg_right (by positivity))
  have herror' : ‖(u j-v j).val‖ ≤ D₀*P*Real.exp (-c*(n : ℝ)^δ)*(eLpNorm χ ∞ ν).toReal := by
    apply (PiLp.norm_apply_le (WithLp.toLp 2 (fun i => (u i-v i).val)) j).trans
    apply herror.trans
    apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have hC : p.val.1⁻¹*C₁ ≤ D₀ := by
      apply (mul_le_mul_of_nonneg_right hβinv hC₁.le).trans
      dsimp only [D₀]
      exact le_add_of_nonneg_left hC00
    exact hC.trans (le_mul_of_one_le_right hD0 hP)
  have huj : (u j).val = (u j-v j).val+(v j).val := by
    change (u j).val = ((u j).val-(v j).val)+(v j).val
    abel
  have hnorm : ‖(u j).val‖ ≤ A*(n : ℝ)^((r+1)*h)*e*
      (‖χ‖+Real.exp (-(c/2)*(n : ℝ)^δ)*(eLpNorm χ ∞ ν).toReal) := by
    rw [huj]
    apply (norm_add_le _ _).trans ((add_le_add herror' hv').trans ?_)
    have ht := hinsert n (D₀*P) ‖χ‖ (eLpNorm χ ∞ ν).toReal e hn1
      (mul_nonneg hD0 (by dsimp [P]; positivity)) (norm_nonneg _) ENNReal.toReal_nonneg
      (by
        dsimp only [e]
        exact (le_add_of_nonneg_left (Real.rpow_nonneg (by positivity) _)).trans
          (le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _)))
    apply (show D₀*P*Real.exp (-c*(n : ℝ)^δ)*(eLpNorm χ ∞ ν).toReal+D₀*P*e*‖χ‖ =
      (D₀*P)*e*‖χ‖+(D₀*P)*Real.exp (-c*(n : ℝ)^δ)*(eLpNorm χ ∞ ν).toReal by ring).le.trans
    apply ht.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ he0
    calc
      _ = (B*D₀)*P := by ring
      _ ≤ A*(n : ℝ)^((r+1)*h) := mul_le_mul (le_max_right 1 (B*D₀))
        (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)) (by dsimp [P]; positivity) (by dsimp [A]; positivity)
  have ht := ENNReal.ofReal_le_ofReal hnorm
  rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_add (norm_nonneg _) (by positivity),
    ENNReal.ofReal_mul (Real.exp_pos _).le,ENNReal.ofReal_toReal hχ.ne] at ht
  exact ht

/-- Complete proper-marginal clause of Proposition 4.10,
with the stated quantifier order, coordinates, parameter ranges,
normalizers, Neumann realization, uniqueness and extended-valued decay bound. -/
theorem proper_physical_decay_compact :
    ∀ s : ShortExponent, ∃ q : ℝ, 0 < q ∧
      ∀ h : ℝ, 0 < h → ∃ δ : ℝ, 0 < δ ∧
      ∀ θ : PhysicalCutoff, ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
      ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
      ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      let p := ofShort β s
      ∀ (N n : ℕ+), 4 ≤ (N : ℕ) → 2 ≤ (n : ℕ) →
        2*(n : ℕ) ≤ (N : ℕ) → ∀ (hn : (n : ℕ) ≤ (N : ℕ)) (b : Bool),
        let ν := activeTiltedGapLaw p N n hn θ h b
        0 < tiltNormalizer p N n hn θ h b ∧
        tiltNormalizer p N n hn θ h b < ⊤ ∧ IsProbabilityMeasure ν ∧
        ∃ (V : EuclideanSpace ℝ (Fin (n : ℕ)) → ℝ) (Q : ScalarFormData ν),
          IsEuclideanGibbsPotential volume ν (properMarginalDomain n N) V ∧
          IsNeumannRealization (properMarginalDomain n N) Q ∧
          IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
          ∀ i₀ : Fin (n : ℕ), (n : ℕ) ≤ 4*(i₀.val+1) →
            4*(i₀.val+1) ≤ 3*(n : ℕ) → ∀ χ : Lp ℝ 2 ν,
          eLpNorm χ ∞ ν < ⊤ →
          (∃! u : Fin (n : ℕ) → Q.1,
            WeightedWeakSolution Q (hessianMatrix V) ⊤ (fun i => if i=i₀ then χ else 0) u) ∧
          (∀ u : Fin (n : ℕ) → Q.1,
            WeightedWeakSolution Q (hessianMatrix V) ⊤ (fun i => if i=i₀ then χ else 0) u →
            ∀ j : Fin (n : ℕ), ENNReal.ofReal ‖(u j).val‖ ≤
              ENNReal.ofReal (A*(n : ℝ)^(q*h)*
                ((1+|(j.val : ℝ)-(i₀.val : ℝ)|)^(-s.val)+
                  (n : ℝ)^(-(s.val-1/2))+(N : ℝ)^(-(1/2 : ℝ)))) *
                (ENNReal.ofReal ‖χ‖+ENNReal.ofReal (Real.exp (-c*(n : ℝ)^δ))*eLpNorm χ ∞ ν)) := by
  intro s
  obtain ⟨q,hq,hdec⟩ := proper_physical_decay_compact_chart s.val s.property
  refine ⟨q,hq,fun h hh => ?_⟩
  obtain ⟨δ,hδ,hdec⟩ := hdec h hh
  refine ⟨δ,hδ,fun θ βlo βhi hlo hle => ?_⟩
  obtain ⟨A,c,hA,hc,hdec⟩ := hdec θ βlo βhi hlo hle
  refine ⟨A,c,lt_of_lt_of_le zero_lt_one hA,hc,fun β hβ => ?_⟩
  let p := ofShort β s
  have hdec := hdec p rfl hβ.1 hβ.2
  intro _p N n hN hn2 hhalf hn b
  obtain ⟨m,he⟩ : ∃ m : ℕ, ((n : ℕ)+m).succPNat = N := by
    refine ⟨(N : ℕ)-(n : ℕ)-1,?_⟩
    apply PNat.coe_injective
    change (n : ℕ)+((N : ℕ)-(n : ℕ)-1)+1 = (N : ℕ)
    omega
  subst N
  exact hdec n m hn (by simpa only [Nat.succPNat_coe] using hN) hn2
    (by simpa only [Nat.succPNat_coe] using hhalf) b

end Riesz2.DecayShort.PhysicalDecay
