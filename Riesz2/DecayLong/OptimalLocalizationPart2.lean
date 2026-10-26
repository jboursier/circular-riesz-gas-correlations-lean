/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.OptimalLocalization
public import Riesz2.DecayLong.OptimalLocalizationUnconstrained
public import Riesz2.DecayLong.OptimalLocalizationBootstrap
public import Riesz2.DecayLong.ReferenceComparisonPart2

/-!
# Uniform loss parameters for the localization bootstrap

The uniform induction assertion has one prefactor for every loss parameter
above a fixed positive lower bound. All matrices, forms, sources and solutions
are the existing objects.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped BigOperators Classical Fin.NatCast

namespace Riesz2.OptimalLocalizationPart2

/-- The pointwise assertion of Subsection 5.5 at fixed constants, for
one equation mode. Configuration and component dimensions are independent. -/
def EstimateAt (s : Riesz1.RieszExponent) (κstar γstar : ℝ) (M₀ : ℕ+)
    (a g : ℝ) (b : Bool) (κ ε Cstar βlo βhi C : ℝ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
  ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ)),
  2 ≤ (n : ℕ) → (n : ℕ) ≤ (m : ℕ) →
  (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
  let K := ⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ)
  1 ≤ K → 4 * K ≤ (m : ℕ) →
  ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
  PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M →
  ∀ β : ℝ, βlo ≤ β → β ≤ βhi →
  ∀ (i₀ : Fin (m : ℕ)) (χ : Lp ℝ 2 ν),
  ∃! u : Fin (m : ℕ) → Q.1,
    WeightedWeakSolution Q (fun x => β • M x)
      (if b then zeroSumComponents _ else ⊤)
      (fun i => if i = i₀ then χ else 0) u ∧
    ∀ j, ‖(u j).val‖ ≤ C * (n : ℝ) ^ (κ * ε) * weightRadius m j i₀ ^ (-a) * ‖χ‖ ∧
      Real.sqrt (Q.2 (u j) (u j)) ≤
        C * (n : ℝ) ^ (κ * ε) * weightRadius m j i₀ ^ (-g) * ‖χ‖

/-- Uniform induction assertion for Subsection 5.5. One prefactor controls
every ε ≥ εmin > 0, using the same matrices, scalar forms and weak solutions. -/
def UniformProfile (s : Riesz1.RieszExponent) (A G : ℝ) (b : Bool) : Prop :=
  ∀ (κstar γstar : ℝ) (M₀ : ℕ+), 0 < κstar → 0 < γstar →
    ∃ κ : ℝ, 0 < κ ∧ ∀ εmin : ℝ, 0 < εmin →
    ∀ Cstar : ℝ, 1 ≤ Cstar →
    ∀ βlo : ℝ, 0 < βlo → ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, εmin ≤ ε →
      EstimateAt s κstar γstar M₀ A G b κ ε Cstar βlo βhi C

/-- See Subsection 5.5 of the paper: forgetting uniformity in the loss parameter
recovers the original mode-specific induction assertion. -/
theorem uniformProfile_forget_internal (s : Riesz1.RieszExponent) (A G : ℝ) (b : Bool)
    (h : UniformProfile s A G b) :
    OptimalLocalizationBootstrap.UniformEstimate s A G b := by
  intro κstar γstar M₀ hκstar hγstar
  obtain ⟨κ, hκ, hp⟩ := h κstar γstar M₀ hκstar hγstar
  refine ⟨κ, hκ, fun ε hε Cstar hCstar βlo βhi hβlo hβhi => ?_⟩
  obtain ⟨C, hC, hp⟩ := hp ε hε Cstar hCstar βlo hβlo βhi hβhi
  refine ⟨C, hC, ?_⟩
  intro β hβ n m hn hm hnm hmn K hK hKm d Ω ν _ _ _ _ hν _ Q _ hQ hQc M hM i₀ χ
  have := hν
  obtain ⟨v, ⟨hv, hest⟩, _⟩ := hp ε le_rfl ν Q hQ hQc n m hm hn hnm hmn hK hKm M hM
    β.val hβ.1 hβ.2 i₀ χ
  have hl : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
      ∀ z : Fin (m : ℕ) → ℝ,
        Cstar⁻¹ * (n : ℝ) ^ (-κstar * ε) * (∑ i, z i ^ 2) ≤
          ∑ i, ∑ j, z i * M x i j * z j :=
    hM.2.1.mono (fun _ hx => ⟨hx.1, hx.2.2.1⟩)
  have hu := (AbstractEquation.existence_energy Q hQ β.val β.property M hM.1 _
    (SchurRestriction.periodized_mass_pos hCstar) hl (if b then zeroSumComponents _ else ⊤) (fun i => if i = i₀ then χ else 0)).1
  refine ⟨hu, fun u husol j => ?_⟩
  have heq : u = v := hu.unique husol hv
  subst u
  exact hest j

/-- The base case of Proposition 5.15 with the strengthened
quantifiers of Subsection 5.5, from the uniform global estimates. -/
theorem base_uniform_internal (hzeta : External.PeriodicZeta) (s : Riesz1.RieszExponent) :
    ∀ b, UniformProfile s (3 / 2 - s.val) (1 - s.val / 2) b := by
  intro b κstar γstar M₀ hκstar hγstar
  cases b
  · obtain ⟨κ, hκ, hp⟩ := LocalizedMatrix.Analytic.global_bis hzeta s κstar γstar
      hκstar hγstar M₀
    refine ⟨κ, hκ, fun εmin hεmin Cstar hCstar βlo hβlo βhi hβhi => ?_⟩
    obtain ⟨C, hC, hp⟩ := hp εmin hεmin Cstar hCstar βlo hβlo βhi hβhi
    refine ⟨C, hC, ?_⟩
    intro ε hεlower Ω _ ν _ Q hQ hQc n m hm hn hnm hmn K hK hKm M hM β hβl hβu i₀ χ
    obtain ⟨v, ⟨hv, hest⟩, _⟩ :=
      hp ε hεlower ν Q hQ hQc n m hm hn hnm hmn hK hKm M hM β hβl hβu χ i₀
    refine ⟨v, ⟨hv, ?_⟩, fun u hu => ?_⟩
    · simpa only [mul_right_comm _ ‖χ‖] using
        OptimalLocalizationBootstrap.component_bounds_internal Q hQ m i₀ _ _ _ v hest
    · have hl : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
          ∀ z : Fin (m : ℕ) → ℝ,
            Cstar⁻¹ * (n : ℝ) ^ (-κstar * ε) * (∑ i, z i ^ 2) ≤
              ∑ i, ∑ j, z i * M x i j * z j :=
        hM.2.1.mono (fun _ hx => ⟨hx.1, hx.2.2.1⟩)
      have heq := (AbstractEquation.existence_energy Q hQ β (hβlo.trans_le hβl) M hM.1 _
        (SchurRestriction.periodized_mass_pos hCstar) hl ⊤ (fun i => if i = i₀ then χ else 0)).1
      have he : u = v := heq.unique hu.1 hv
      exact he
  · obtain ⟨κ, hκ, hp⟩ := LocalizedMatrix.Analytic.global_decay hzeta s κstar γstar
      hκstar hγstar M₀
    refine ⟨κ, hκ, fun εmin hεmin Cstar hCstar βlo hβlo βhi hβhi => ?_⟩
    obtain ⟨C, hC, hp⟩ := hp εmin hεmin Cstar hCstar βlo hβlo βhi hβhi
    refine ⟨C, hC, ?_⟩
    intro ε hεlower Ω _ ν _ Q hQ hQc n m hm hn hnm hmn K hK hKm M hM β hβl hβu i₀ χ
    obtain ⟨v, ⟨hv, lam, hlam, hfull, hest, hlamest⟩, _⟩ :=
      hp ε hεlower ν Q hQ hQc n m hm hn hnm hmn hK hKm M hM β hβl hβu χ i₀
    have hl : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
        ∀ z : Fin (m : ℕ) → ℝ,
          Cstar⁻¹ * (n : ℝ) ^ (-κstar * ε) * (∑ i, z i ^ 2) ≤
            ∑ i, ∑ j, z i * M x i j * z j :=
      hM.2.1.mono (fun _ hx => ⟨hx.1, hx.2.2.1⟩)
    have heq := (AbstractEquation.existence_energy Q hQ β (hβlo.trans_le hβl) M hM.1 _
      (SchurRestriction.periodized_mass_pos hCstar) hl (zeroSumComponents _)
      (fun i => if i = i₀ then χ else 0)).1
    refine ⟨v, ⟨hv, ?_⟩, fun u hu => heq.unique hu.1 hv⟩
    simpa only [mul_right_comm _ ‖χ‖] using
        OptimalLocalizationBootstrap.component_bounds_internal Q hQ m i₀ _ _ _ v hest

/-- See the proof of Proposition 5.15 in the paper: the cyclic shell estimate
has a single prefactor for every ε ≥ εmin. -/
theorem scaled_profile_sum_uniform_internal (s : Riesz1.RieszExponent) (u : ℝ) (hu : 0 < u)
    (εmin : ℝ) (hεmin : 0 < εmin) :
    ∃ L : ℝ, 0 < L ∧ ∀ ε : ℝ, εmin ≤ ε →
      ∀ (n m : ℕ+) (_hm : 2 ≤ (m : ℕ)),
      2 ≤ (n : ℕ) → (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
      ∀ j : Fin (m : ℕ),
      (m : ℝ) ^ (-(2 - s.val)) * (∑ i, weightRadius m j i ^ (-u)) ≤
        L * (n : ℝ) ^ ε *
          ((m : ℝ) ^ (-(2 - s.val)) + (m : ℝ) ^ (-(u + 1 - s.val))) := by
  obtain ⟨L, hL, hp⟩ := OptimalLocalizationUnconstrained.scaled_profile_sum s u hu εmin hεmin
  refine ⟨L, hL, fun ε hε n m hm hn hmn j => ?_⟩
  apply (hp n m hm hn hmn j).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ hL.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast n.pos) hε

open OptimalLocalizationUnconstrained

/-- Uniform composition in the proof of Proposition 5.15, assuming the
constrained improvement. A single prefactor controls every ε ≥ εmin. -/
theorem unconstrained_step_uniform_internal (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (A G : ℝ)
    (hAlo : 3 / 2 - s.val ≤ A) (hGlo : 1 - s.val / 2 ≤ G)
    (hcurrent : UniformProfile s A G false)
    (hconstrained : UniformProfile s (min (2 - s.val) (A + 1 - s.val))
      (min ((3 - s.val) / 2) (G + 1 - s.val)) true) :
    UniformProfile s (min (2 - s.val) (A + 1 - s.val))
      (min ((3 - s.val) / 2) (G + 1 - s.val)) false := by
  intro κstar γstar M₀ hκstar hγstar
  obtain ⟨κp, hκp, hp⟩ := hcurrent κstar γstar M₀ hκstar hγstar
  obtain ⟨κc, hκc, hc⟩ := hconstrained κstar γstar M₀ hκstar hγstar
  obtain ⟨κm, hκm, hm⟩ := LocalizedMatrix.Analytic.global_bis_mean hzeta s
    κstar γstar hκstar hγstar M₀
  obtain ⟨κe, hκe, he⟩ := LocalizedMatrix.Analytic.global_error_differences s κstar γstar hκstar.le hγstar.le M₀
  refine ⟨κc + κm + κp + κe + 1, by positivity,
    fun εmin hεmin Cstar hCstar βlo hβlo βhi hβhi => ?_⟩
  obtain ⟨Cp, hCp, hp⟩ := hp εmin hεmin Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Cc, hCc, hc⟩ := hc εmin hεmin Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Cm, hCm, hm⟩ := hm εmin hεmin Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Ce, hCe, he⟩ := he Cstar hCstar
  have hA : 0 < A := by linarith only [hAlo, s.property.2]
  have hG : 0 < G := by linarith only [hGlo, s.property.2]
  obtain ⟨La, hLa, hsa⟩ := scaled_profile_sum_uniform_internal s A hA εmin hεmin
  obtain ⟨Lg, hLg, hsg⟩ := scaled_profile_sum_uniform_internal s G hG εmin hεmin
  let L := La + Lg
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hβhi0 : 0 < βhi := hβlo.trans_le hβhi
  let C := Cc + Cm + 2 * Cp * βhi * Ce * Cm * L
  have hCe0 : 0 ≤ Ce := zero_le_one.trans hCe
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro ε hεlower Ω _ ν _ Q hQ hQc n m hm2 hn hnm hmn K hK hKm M hM β hβl hβu i₀ χ
  have hε : 0 < ε := hεmin.trans_le hεlower
  have hβ : 0 < β := hβlo.trans_le hβl
  let Dp := Cp * (n : ℝ) ^ (κp * ε)
  let Dc := Cc * (n : ℝ) ^ (κc * ε)
  let Dm := Cm * (n : ℝ) ^ (κm * ε)
  let Be := Ce * (n : ℝ) ^ (κe * ε)
  let B := βhi * Be * Dm
  have hDp : 0 ≤ Dp := by dsimp only [Dp]; positivity
  have hDm : 0 ≤ Dm := by dsimp only [Dm]; positivity
  have hBe : 0 ≤ Be := by dsimp only [Be]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  obtain ⟨u, ⟨hu, v, lam, f, hvc, _, _, _, _, _, hf, hfg, _, ⟨g, hg, hgeq⟩, _⟩, _⟩ :=
    hm ε hεlower ν Q hQ hQc n m hm2 hn hnm hmn hK hKm M hM β hβl hβu χ i₀
  obtain ⟨vc, ⟨hvc', hvcest⟩, _⟩ :=
    hc ε hεlower ν Q hQ hQc n m hm2 hn hnm hmn hK hKm M hM β hβl hβu i₀ χ
  let a := Cstar⁻¹ * (n : ℝ) ^ (-κstar * ε)
  have ha : 0 < a := SchurRestriction.periodized_mass_pos hCstar
  have hl : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
      ∀ z : Fin (m : ℕ) → ℝ, a * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j :=
    hM.2.1.mono (fun _ hx => ⟨hx.1, hx.2.2.1⟩)
  have huniqC := (AbstractEquation.existence_energy Q hQ β hβ M hM.1 a ha hl
    (zeroSumComponents _) (fun i => if i = i₀ then χ else 0)).1
  have hvc_eq : vc = v := huniqC.unique hvc' hvc
  subst vc
  have hpoint : ∀ (ζ : Lp ℝ 2 ν) (i : Fin (m : ℕ)),
      ∃ z : Fin (m : ℕ) → Q.1,
        WeightedWeakSolution Q (fun x => β • M x) ⊤ (fun k => if k = i then ζ else 0) z ∧
        ∀ j, ‖(z j).val‖ ≤ Dp * weightRadius m j i ^ (-A) * ‖ζ‖ ∧
          Real.sqrt (Q.2 (z j) (z j)) ≤ Dp * weightRadius m j i ^ (-G) * ‖ζ‖ := by
    intro ζ i
    obtain ⟨z, hz, _⟩ := hp ε hεlower ν Q hQ hQc n m hm2 hn hnm hmn hK hKm M hM β hβl hβu i ζ
    exact ⟨z, hz⟩
  obtain ⟨_, _, _, _, _, _, heae⟩ := he ε hε n m hm2 hn hnm hmn hK hKm ν M hM
  have hrow : ∀ᵐ x ∂ν, ∀ i, ∑ j, |(M x - (2 : ℝ) • rieszMatrix s m hm2) i j| ≤ Be :=
    heae.mono (fun _ hx => hx.2.2.2.1)
  have hgB : ∀ i, ‖g i‖ ≤ B * (m : ℝ) ^ (-(2 - s.val)) * ‖χ‖ := by
    intro i
    have hg₁ := row_source_norm_internal m β Be hβ.le hBe
      (fun x => M x - (2 : ℝ) • rieszMatrix s m hm2) hrow f.val g hg i
    have hg₂ := mul_le_mul_of_nonneg_left hf (mul_nonneg hβ.le hBe)
    have hg₃ : (β * Be) * (Dm * (m : ℝ) ^ (-(2 - s.val)) * ‖χ‖) ≤
        (βhi * Be) * (Dm * (m : ℝ) ^ (-(2 - s.val)) * ‖χ‖) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hβu hBe) (by positivity)
    exact hg₁.trans (hg₂.trans (hg₃.trans_eq (by dsimp only [B]; ring)))
  have hsa' (j) : (m : ℝ) ^ (-(2 - s.val)) * (∑ i, weightRadius m j i ^ (-A)) ≤
      L * (n : ℝ) ^ ε *
        ((m : ℝ) ^ (-(2 - s.val)) + (m : ℝ) ^ (-(A + 1 - s.val))) := by
    apply (hsa ε hεlower n m hm2 hn hmn j).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (by dsimp only [L]; linarith only [hLg]) (by positivity)
  have hsg' (j) : (m : ℝ) ^ (-(2 - s.val)) * (∑ i, weightRadius m j i ^ (-G)) ≤
      L * (n : ℝ) ^ ε *
        ((m : ℝ) ^ (-(2 - s.val)) + (m : ℝ) ^ (-(G + 1 - s.val))) := by
    apply (hsg ε hεlower n m hm2 hn hmn j).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (by dsimp only [L]; linarith only [hLa]) (by positivity)
  have hAinc : 0 ≤ A + 1 - s.val := by linarith only [hA, s.property.2]
  have hGinc : 0 ≤ G + 1 - s.val := by linarith only [hG, s.property.2]
  have hrem := remainder_improvement_internal s n m hm2 i₀ Q hQ M hM.1
    (SchurRestriction.periodized_bounded hM) β a hβ ha hl A G ε Dp B L ‖χ‖
    hDp hB hL (norm_nonneg χ) hAinc hGinc hpoint hsa' hsg' g hgB
    (fun j => u j - v j - f) hgeq
  have hfinal := assemble_internal s m hm2 i₀ Q hQ A G Dc Dm
    (2 * Dp * B * L * (n : ℝ) ^ ε) ‖χ‖ hDm (norm_nonneg χ) hAinc hGinc
    u v f hvcest hf hfg hrem
  have hcoef : Dc + Dm + 2 * Dp * B * L * (n : ℝ) ^ ε ≤
      C * (n : ℝ) ^ ((κc + κm + κp + κe + 1) * ε) :=
    loss_assembly_internal n ε κc κm κp κe Cc Cm Cp Ce βhi L hε hκc hκm hκp hκe
      hCc.le hCm.le hCp.le hCe0 hβhi0.le hL
  have huniq := (AbstractEquation.existence_energy Q hQ β hβ M hM.1 a ha hl
    ⊤ (fun i => if i = i₀ then χ else 0)).1
  refine ⟨u, ⟨hu, fun j => ⟨?_, ?_⟩⟩, fun z hz => huniq.unique hz.1 hu⟩
  · exact (hfinal j).1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (by
        exact Real.rpow_nonneg (zero_le_one.trans (one_le_weightRadius m j i₀)) _))
      (norm_nonneg χ))
  · exact (hfinal j).2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (by
        exact Real.rpow_nonneg (zero_le_one.trans (one_le_weightRadius m j i₀)) _))
      (norm_nonneg χ))


/-- See the proof of Proposition 5.15 in the paper: apply the uniform induction
hypothesis to the actual localized matrix at its varying loss parameter.
The prefactor is chosen before the parent loss parameter, sizes, coefficient
representation and target. The cutoff and scalar form are unchanged. -/
theorem window_point_source_internal (s : Riesz1.RieszExponent) (Aexp Gexp : ℝ)
    (hcurrent : UniformProfile s Aexp Gexp false)
    (κstar γstar : ℝ) (M₀ : ℕ+) (hκstar : 0 < κstar) (hγstar : 0 < γstar) :
    ∃ κ D : ℝ, 0 < κ ∧ 0 < D ∧
    ∀ εmin : ℝ, 0 < εmin → ∀ Cstar : ℝ, 1 ≤ Cstar →
    ∀ βlo : ℝ, 0 < βlo → ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧
    ∀ ε : ℝ, εmin ≤ ε →
    ∀ {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
      (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
    ∀ (n m : ℕ+), 2 ≤ (n : ℕ) →
    ∀ hm : 2 ≤ (m : ℕ),
    (n : ℕ) ≤ (m : ℕ) →
    (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
    let K := ⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ)
    1 ≤ K →
    ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M →
    ∀ A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → Ω → ℝ,
    (∀ t, Measurable (A t)) →
    (∀ᵐ x ∂ν, IntervalBoundary.intervalMatrix m m le_rfl (fun t => A t x) = M x) →
    ∀ (j i₀ : Fin (m : ℕ)) (hR : 16 ≤ Riesz1.cyclicIndexDistance m j i₀),
    (n : ℝ) ^ (D * ε) ≤ (Riesz1.cyclicIndexDistance m j i₀ : ℝ) →
    let n₀ := LocalizedMatrix.windowSize m j i₀
    let m₀ := LocalizedMatrix.windowPeriod s m j i₀
    let hn : (n₀ : ℕ) ≤ (m : ℕ) := by
      have := (LocalizedMatrix.window_size_bounds m j i₀ hR).2.2.2
      dsimp only [n₀]; omega
    let hn₀ : (n₀ : ℕ) ≤ (m₀ : ℕ) := by
      have := LocalizedMatrix.two_windowSize_lt_period s m j i₀ hR
      dsimp only [n₀, m₀]; omega
    let hm₀ : 2 ≤ (m₀ : ℕ) := by
      have := LocalizedMatrix.two_windowSize_lt_period s m j i₀ hR
      have := n₀.pos
      dsimp only [n₀, m₀] at *; omega
    let b := j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ))
    let Ml := LocalizedMatrix.matrix s m m₀ n₀ hm₀ hn hn₀ K (fun t => A (t.1 + b, t.2))
    ∀ β : ℝ, βlo ≤ β → β ≤ βhi →
    ∀ (i : Fin (m₀ : ℕ)) (χ : Lp ℝ 2 ν),
    ∃! u : Fin (m₀ : ℕ) → Q.1,
      WeightedWeakSolution Q (fun x => β • Ml x) ⊤
        (fun k => if k = i then χ else 0) u ∧
      ∀ l, ‖(u l).val‖ ≤ C * (n : ℝ) ^ (κ * ε) * weightRadius m₀ l i ^ (-Aexp) * ‖χ‖ ∧
        Real.sqrt (Q.2 (u l) (u l)) ≤
          C * (n : ℝ) ^ (κ * ε) * weightRadius m₀ l i ^ (-Gexp) * ‖χ‖ := by
  obtain ⟨κl, γl, Dl, hκl, hγl, hDl, hlocal⟩ :=
    ReferenceComparisonError.localization_for_representation_internal s κstar γstar M₀ hκstar hγstar
  obtain ⟨κ, hκ, hp⟩ := hcurrent κl γl M₀ hκl hγl
  let D := max Dl (8 * (M₀ : ℕ))
  refine ⟨κ, D, hκ, hDl.trans_le (le_max_left _ _), ?_⟩
  intro εmin hεmin Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Cl, hCl, hlocal⟩ := hlocal Cstar hCstar
  have hs := s.property.1
  have hα : 0 < 3 / 2 + 1 / s.val := by positivity
  obtain ⟨C, hC, hp⟩ := hp (εmin / (3 / 2 + 1 / s.val))
    (div_pos hεmin hα) Cl hCl βlo hβlo βhi hβhi
  refine ⟨C, hC, ?_⟩
  intro ε hεlower Ω _ ν _ Q hQ hQc n m hn hm hnm hmn K hK M hM A hAm hArep
    j i₀ hR hsep n₀ m₀ hnp hn₀ hm₀ b Ml β hβl hβu i χ
  have hε : 0 < ε := hεmin.trans_le hεlower
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have sep (d : ℝ) (hd : d ≤ D) :
      (n : ℝ) ^ (d * ε) ≤ (Riesz1.cyclicIndexDistance m j i₀ : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hn1 (mul_le_mul_of_nonneg_right hd hε.le)).trans hsep
  have hMl := hlocal ν ε hε n m hn hm M hM A hAm hArep j i₀ hR
    (sep Dl (le_max_left _ _))
  obtain ⟨hε₀, hlower, hpowers, hcut⟩ :=
    LocalizedMatrix.Analytic.window_loss_parameters s n m hn hmn j i₀ hR ε hε
  have hemin : εmin / (3 / 2 + 1 / s.val) ≤ ε * Real.log (n : ℝ) / Real.log (n₀ : ℝ) :=
    (div_le_div_of_nonneg_right hεlower hα.le).trans hlower
  have hKlocal := LocalizedMatrix.window_reference_cutoff_admissible s n m ε hε M₀ j i₀ hR
    (sep (8 * (M₀ : ℕ)) (le_max_right _ _))
  have hn₀2 : 2 ≤ (n₀ : ℕ) := by
    have := (LocalizedMatrix.window_size_bounds m j i₀ hR).1
    change 5 ≤ (n₀ : ℕ) at this
    omega
  have hcut' : ⌊(n₀ : ℝ) ^ (ε * Real.log (n : ℝ) / Real.log (n₀ : ℝ))⌋₊ ^ (M₀ : ℕ) = K :=
    hcut M₀
  have hp' := hp _ hemin ν Q hQ hQc n₀ m₀ hm₀ hn₀2 hn₀
    (LocalizedMatrix.Analytic.windowPeriod_analytic_upper s m j i₀)
  rw [hcut'] at hp'
  have he := hp' hK hKlocal.2 Ml hMl β hβl hβu i χ
  have hpower : (n₀ : ℝ) ^ (κ * (ε * Real.log (n : ℝ) / Real.log (n₀ : ℝ))) =
      (n : ℝ) ^ (κ * ε) := hpowers κ
  simpa only [Bool.false_eq_true, ↓reduceIte, hpower] using he


/-- See the proof of Proposition 5.15 in the paper: construct the actual local
comparison and retain the boundary, reference and error-source bounds on the
same witnesses. -/
theorem localized_decomposition_internal (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ)
    (hκstar : 0 < κstar) (hγstar : 0 < γstar) (M₀ : ℕ+) :
    ∃ κz κφ κg D : ℝ, 0 < κz ∧ 0 < κφ ∧ 0 < κg ∧ 0 < D ∧ ∀ ε : ℝ, 0 < ε →
    ∀ Cstar : ℝ, 1 ≤ Cstar →
    ∀ (βlo : ℝ) (_hβlo : 0 < βlo), ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ Cz Cφ Cg : ℝ, 0 < Cz ∧ 0 < Cφ ∧ 0 < Cg ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
      (Q : ScalarFormData ν) (_hQ : IsClosedScalarDirichletForm Q), IsConservativeScalarForm Q →
    ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ)),
    2 ≤ (n : ℕ) → (n : ℕ) ≤ (m : ℕ) →
    (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
    let K := ⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ)
    1 ≤ K → 4 * K ≤ (m : ℕ) →
    ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M →
    ∃ A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → Ω → ℝ,
      (∀ t, Measurable (A t)) ∧
      (∀ᵐ x ∂ν, (∀ t, 0 ≤ A t x) ∧
        IntervalBoundary.intervalMatrix m m le_rfl (fun t => A t x) = M x) ∧
    ∀ (j i₀ : Fin (m : ℕ)) (hR : 16 ≤ Riesz1.cyclicIndexDistance m j i₀),
    (n : ℝ) ^ (D * ε) ≤ (Riesz1.cyclicIndexDistance m j i₀ : ℝ) →
    let n₀ := LocalizedMatrix.windowSize m j i₀
    let m₀ := LocalizedMatrix.windowPeriod s m j i₀
    let hn : (n₀ : ℕ) ≤ (m : ℕ) := by
      have := (LocalizedMatrix.window_size_bounds m j i₀ hR).2.2.2
      dsimp only [n₀]; omega
    let hn₀ : (n₀ : ℕ) ≤ (m₀ : ℕ) := by
      have := LocalizedMatrix.two_windowSize_lt_period s m j i₀ hR
      dsimp only [n₀, m₀]; omega
    let hm₀ : 2 ≤ (m₀ : ℕ) := by
      have := LocalizedMatrix.two_windowSize_lt_period s m j i₀ hR
      have := n₀.pos
      dsimp only [n₀, m₀] at *; omega
    let b := j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ))
    let P := fun x (l i : Fin (n₀ : ℕ)) => M x (l.castLE hn + b) (i.castLE hn + b)
    let Ml := LocalizedMatrix.matrix s m m₀ n₀ hm₀ hn hn₀ K (fun t => A (t.1 + b, t.2))
    let _Rem := LocalizedMatrix.remainder s m m₀ n₀ hm₀ hn hn₀ K
      (fun t => A (t.1 + b, t.2)) P
    let c : Fin (m₀ : ℕ) := ⟨Riesz1.cyclicIndexDistance m j i₀ / 8, by
      have hc := LocalizedMatrix.window_card m j i₀
      have ht := LocalizedMatrix.two_windowSize_lt_period s m j i₀ hR
      change _ < (LocalizedMatrix.windowPeriod s m j i₀ : ℕ)
      change (LocalizedMatrix.windowSize m j i₀ : ℕ) = _ at hc
      omega⟩
    ∀ (β : ℝ) (_hβl : βlo ≤ β), β ≤ βhi →
    ∀ (χ : Lp ℝ 2 ν) (u : Fin (m : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _)
      (fun i => if i = i₀ then χ else 0) u →
    ∃ ψ₀ z φ : Fin (m₀ : ℕ) → Q.1,
      (∀ i : Fin (n₀ : ℕ), ψ₀ (i.castLE hn₀) = u (LocalizedMatrix.windowEmbedding m j i₀ i)) ∧
      (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (2 - s.val) * ‖(z c).val‖ +
        (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ ((3 - s.val) / 2) *
          Real.sqrt (Q.2 (z c) (z c)) ≤ Cz * (n : ℝ) ^ (κz * ε) * ‖χ‖ ∧
      ‖(φ c).val‖ ≤ Cφ * (n : ℝ) ^ (κφ * ε) * ‖χ‖ *
        (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (-(2 - s.val)) ∧
      Real.sqrt (Q.2 (φ c) (φ c)) ≤ Cφ * (n : ℝ) ^ (κφ * ε) * ‖χ‖ *
        (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (-(3 - s.val) / 2) ∧
    ∃ g : Fin (m₀ : ℕ) → Lp ℝ 2 ν,
      WeightedWeakSolution Q (fun x => β • Ml x) ⊤ g (fun i => ψ₀ i - z i - φ i) ∧
      (∑ i, ‖g i‖) ≤ Cg * (n : ℝ) ^ (κg * ε) * ‖χ‖ *
        (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (-(1 - s.val)) ∧
      ∀ i, (Riesz1.cyclicIndexDistance m₀ i c : ℝ) ≤
        (Riesz1.cyclicIndexDistance m j i₀ : ℝ) / 64 →
        ‖g i‖ ≤ Cg * (n : ℝ) ^ (κg * ε) * ‖χ‖ *
          (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (-(2 - s.val)) := by
  obtain ⟨κφ, Dφ, hκφ, hDφ, href⟩ :=
    ReferenceComparison.loc_reference_solution hzeta s κstar γstar hκstar hγstar M₀
  obtain ⟨κb, Db, hκb, hDb, hboundary⟩ :=
    LocalizedBoundary.loc_boundary hzeta s κstar γstar hκstar hγstar M₀
  obtain ⟨κl, γl, Dl, hκl, hγl, hDl, hlocal⟩ :=
    ReferenceComparisonError.localization_for_representation_internal s κstar γstar M₀ hκstar hγstar
  obtain ⟨κ, hκ, hcomp⟩ :=
    ReferenceComparisonError.comparison_error_of_reference_estimates_internal s κl γl κφ hκl.le hκφ.le M₀
  let D := max (max Dφ Db) (max Dl (8 * (M₀ : ℕ)))
  refine ⟨κb, κφ, κ, D, hκb, hκφ, hκ, hDφ.trans_le ((le_max_left Dφ Db).trans (le_max_left _ _)), ?_⟩
  intro ε hε Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Cφ, hCφ, href⟩ := href ε hε Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Cb, hCb, hboundary⟩ := hboundary ε hε Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Cl, hCl, hlocal⟩ := hlocal Cstar hCstar
  obtain ⟨C, hC, hcomp⟩ := hcomp Cl hCl Cφ hCφ βhi (hβlo.trans_le hβhi)
  refine ⟨Cb, Cφ, C, hCb, hCφ, hC, ?_⟩
  intro Ω _ ν _ Q hQ hQc n m hm hn hnm hmn K hK hKm M hM
  obtain ⟨A, hAm, hArep, hb⟩ := hboundary ν Q hQ hQc n m hm hn hnm hmn hK hKm M hM
  refine ⟨A, hAm, hArep, ?_⟩
  intro j i₀ hR hsep n₀ m₀ hnp hn₀ hm₀ b P Ml Rem c β hβl hβu χ u hu
  let pv := (MatrixEnergy.vectorEquiv Q hQ).symm
    (fun i => u (LocalizedMatrix.windowEmbedding m j i₀ i))
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ (n : ℕ) by omega)
  have sep (d : ℝ) (hd : d ≤ D) :
      (n : ℝ) ^ (d * ε) ≤ (Riesz1.cyclicIndexDistance m j i₀ : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hn1 (mul_le_mul_of_nonneg_right hd hε.le)).trans hsep
  have hsepφ := sep Dφ ((le_max_left Dφ Db).trans (le_max_left _ _))
  have hsepb := sep Db ((le_max_right Dφ Db).trans (le_max_left _ _))
  have hsepl := sep Dl ((le_max_left Dl _).trans (le_max_right _ _))
  have hsepc := sep (8 * (M₀ : ℕ)) ((le_max_right Dl _).trans (le_max_right _ _))
  have hMl := hlocal ν ε hε n m hn hm M hM A hAm (hArep.mono fun _ hx => hx.2) j i₀ hR hsepl
  obtain ⟨r, hr, hbdata, hzexists, hzest⟩ := hb j i₀ hR hsepb β hβl hβu χ u hu
  obtain ⟨lam, hlam, _, wb, hwb, Vb, hVb, hψexists, hψactive⟩ := hbdata
  obtain ⟨lamf, hlamf, U, hU, w, hw, V, hV, hφ⟩ :=
    href ν Q hQ hQc n m hm hn hnm hmn hK hKm M hM β hβl hβu χ i₀ u hu j hR hsepφ
  have helam : lamf = lam := by
    apply Lp.ext
    filter_upwards [hlamf, hlam] with x hx hy
    exact hx.trans hy.symm
  subst lamf
  have hKml := (LocalizedMatrix.window_reference_cutoff_admissible s n m ε hε M₀ j i₀ hR hsepc).2
  have hew : wb = w := by
    have he := LocalizedFieldPart4.normalized_schur_exists_internal hzeta s β (hβlo.trans_le hβl)
      n₀ m₀ hn₀ hm₀ K hK (by change 4 * K ≤ (m₀ : ℕ) at hKml; omega) ν Q hQ pv
    exact he.unique hwb hw
  subst wb
  have heV : Vb = V := by
    funext l
    apply Lp.ext
    have hrow := LocalizedFieldPart3.schur_row_ae_internal Q hQ s n₀ m₀ hn₀ hm₀ K
      Cl κl γl (ε * Real.log (n : ℝ) / Real.log (n₀ : ℝ)) β Ml hMl w l
    rw [hV l]
    filter_upwards [hVb l, hU l, hrow,
      Lp.coeFn_add ((-β) • U l - β • LocalizedFieldPart3.referenceRow Q hQ s n₀ m₀ hm₀ K
        (LocalizedFieldPart3.exteriorReindex Q hQ n₀ m₀ hn₀ w) (l.castLE hn₀)) lam,
      Lp.coeFn_sub ((-β) • U l) (β • LocalizedFieldPart3.referenceRow Q hQ s n₀ m₀ hm₀ K
        (LocalizedFieldPart3.exteriorReindex Q hQ n₀ m₀ hn₀ w) (l.castLE hn₀)),
      Lp.coeFn_smul (-β) (U l)] with x hv hu hr ha hs hm
    rw [ha, Pi.add_apply, hs, Pi.sub_apply, hm, Pi.smul_apply, smul_eq_mul, hu, hr]
    exact hv
  subst Vb
  obtain ⟨ψ₀, hψ, _⟩ := hψexists
  obtain ⟨z, hz, _⟩ := hzexists
  let f := (SchurRestriction.extendSource n₀ m₀ hn₀ (WithLp.toLp 2 V)).ofLp
  let rb := (SchurRestriction.extendSource n₀ m₀ hn₀ (WithLp.toLp 2 r)).ofLp
  have hsum : (SchurRestriction.extendSource n₀ m₀ hn₀ (WithLp.toLp 2 (fun i => V i + r i))).ofLp =
      fun i => f i + rb i := by
    have hh : WithLp.toLp 2 (fun i => V i + r i) = WithLp.toLp 2 V + WithLp.toLp 2 r := rfl
    rw [hh, map_add]
    rfl
  have hψ' : WeightedWeakSolution Q (fun x => β • Ml x) ⊤ (fun i => f i + rb i) ψ₀ := by
    rwa [hsum] at hψ
  have hz' : WeightedWeakSolution Q (fun x => β • Ml x) ⊤ rb z := by
    simpa only [rb, funext (ReferenceComparisonPart2.extendSource_sum_internal n₀ m₀ hn₀ r)] using hz
  have hn₀real : 1 < (n₀ : ℝ) := by
    have ht := (LocalizedMatrix.window_size_bounds m j i₀ hR).1
    change 5 ≤ (n₀ : ℕ) at ht
    exact_mod_cast (show 1 < (n₀ : ℕ) by omega)
  have hRreal : (16 : ℝ) ≤ (Riesz1.cyclicIndexDistance m j i₀ : ℝ) := by exact_mod_cast hR
  have hφ' :
      let φ := fun i => ∑ k, ScalarFormHilbert.equiv Q hQ
        (FiniteFormReferenceKernel.solutionKernel Q hQ _
          (ReferenceOperatorKernelPart3.reference_posDef s ⟨β, hβlo.trans_le hβl⟩ m₀ hm₀) i k (f k))
      (∑ i, ‖(φ i).val‖) ≤ Cφ * (n : ℝ) ^ (κφ * ε) * ‖χ‖ *
        (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (-(1 - s.val)) ∧
      ∀ i, (Riesz1.cyclicIndexDistance m₀ i c : ℝ) ≤
        (Riesz1.cyclicIndexDistance m j i₀ : ℝ) / 32 →
        ‖(φ i).val‖ ≤ Cφ * (n : ℝ) ^ (κφ * ε) * ‖χ‖ *
          (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (-(2 - s.val)) ∧
        Real.sqrt (Q.2 (φ i) (φ i)) ≤ Cφ * (n : ℝ) ^ (κφ * ε) * ‖χ‖ *
          (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (-(3 - s.val) / 2) := by
    simpa only [ReferenceComparison.referenceSolution, map_sum] using hφ
  have he := hcomp ε hε ν Q hQ n n₀ m₀ hn₀real hm₀ hK Ml hMl
    ⟨β, hβlo.trans_le hβl⟩ hβu χ c _ hRreal f rb ψ₀ z hψ' hz' hφ'
  let φ := ReferenceComparison.referenceSolution Q hQ s ⟨β, hβlo.trans_le hβl⟩ m₀ hm₀ f
  obtain ⟨g, hg, hgeq, hmass, hcentral⟩ := he
  have hcenter : (Riesz1.cyclicIndexDistance m₀ c c : ℝ) ≤
      (Riesz1.cyclicIndexDistance m j i₀ : ℝ) / 32 := by
    simp only [Riesz2.cyclicIndexDistance_self, Nat.cast_zero]
    positivity
  have hp := hφ.2 c hcenter
  refine ⟨ψ₀, z, φ, hψactive ψ₀ hψ, hzest z hz, hp.1, hp.2, g, ?_, hmass, hcentral⟩
  simpa only [φ, ReferenceComparison.referenceSolution, map_sum] using hgeq


/-- See the proof of Proposition 5.15 in the paper: remove the positive spatial
weights from the actual boundary estimate. -/
theorem unweight_boundary_internal (R p q z g B : ℝ) (hR : 0 < R)
    (hz : 0 ≤ z) (hg : 0 ≤ g) (h : R ^ p * z + R ^ q * g ≤ B) :
    z ≤ B * R ^ (-p) ∧ g ≤ B * R ^ (-q) := by
  have hv : R ^ p * z ≤ B := (le_add_of_nonneg_right (by positivity)).trans h
  have hg' : R ^ q * g ≤ B := (le_add_of_nonneg_left (by positivity)).trans h
  constructor
  · have hh := mul_le_mul_of_nonneg_right hv (Real.rpow_nonneg hR.le (-p))
    simpa only [mul_right_comm _ z, ← Real.rpow_add hR, add_neg_cancel,
      Real.rpow_zero, one_mul] using hh
  · have hh := mul_le_mul_of_nonneg_right hg' (Real.rpow_nonneg hR.le (-q))
    simpa only [mul_right_comm _ g, ← Real.rpow_add hR, add_neg_cancel,
      Real.rpow_zero, one_mul] using hh

/-- See the proof of Proposition 5.15 in the paper: the restriction identity
at the center gives the value and energy triangle for the actual comparison. -/
theorem decomposition_triangles_internal {Ω : Type} [MeasurableSpace Ω] {ν : Measure Ω}
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (m : ℕ+) (j i₀ : Fin (m : ℕ)) (hR : 16 ≤ Riesz1.cyclicIndexDistance m j i₀)
    (m₀ : ℕ+) (hn₀ : (LocalizedMatrix.windowSize m j i₀ : ℕ) ≤ (m₀ : ℕ))
    (u : Fin (m : ℕ) → Q.1) (ψ z φ : Fin (m₀ : ℕ) → Q.1)
    (hψ : ∀ i : Fin (LocalizedMatrix.windowSize m j i₀ : ℕ),
      ψ (i.castLE hn₀) = u (LocalizedMatrix.windowEmbedding m j i₀ i)) :
    let c₀ : Fin (LocalizedMatrix.windowSize m j i₀ : ℕ) :=
      ⟨Riesz1.cyclicIndexDistance m j i₀ / 8, by
        have hc := LocalizedMatrix.window_card m j i₀
        change (LocalizedMatrix.windowSize m j i₀ : ℕ) = _ at hc
        omega⟩
    let c := c₀.castLE hn₀
    ‖(u j).val‖ ≤ ‖(z c).val‖ + ‖(φ c).val‖ + ‖(ψ c - z c - φ c).val‖ ∧
      Real.sqrt (Q.2 (u j) (u j)) ≤ Real.sqrt (Q.2 (z c) (z c)) +
        Real.sqrt (Q.2 (φ c) (φ c)) +
          Real.sqrt (Q.2 (ψ c - z c - φ c) (ψ c - z c - φ c)) := by
  intro c₀ c
  have hnp : (LocalizedMatrix.windowSize m j i₀ : ℕ) ≤ (m : ℕ) :=
    by have := (LocalizedMatrix.window_size_bounds m j i₀ hR).2.2.2; omega
  have hcast : c₀.castLE hnp = (↑(Riesz1.cyclicIndexDistance m j i₀ / 8) : Fin (m : ℕ)) := by
    apply Fin.ext
    have hc := c₀.isLt
    change Riesz1.cyclicIndexDistance m j i₀ / 8 < _ at hc
    simp only [Fin.val_castLE, Fin.val_natCast]
    change Riesz1.cyclicIndexDistance m j i₀ / 8 = (Riesz1.cyclicIndexDistance m j i₀ / 8) % (m : ℕ)
    rw [Nat.mod_eq_of_lt (by omega)]
  have hemb : LocalizedMatrix.windowEmbedding m j i₀ c₀ = j := by
    rw [LocalizedMatrix.windowEmbedding_apply m j i₀ c₀ hnp]
    rw [hcast]
    abel
  have he : u j = z c + φ c + (ψ c - z c - φ c) := by
    rw [← hemb, ← hψ c₀]
    change ψ c = z c + φ c + (ψ c - z c - φ c)
    abel
  rw [he]
  constructor
  · exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  · exact (LocalizedBoundary.energy_sqrt_add_internal Q hQ _ _).trans
      (add_le_add (LocalizedBoundary.energy_sqrt_add_internal Q hQ _ _) le_rfl)


/-- Fixed-ε conclusion of the proof of Proposition 5.15 under
the uniform induction assertion of Subsection 5.5. The prefactor is chosen for the fixed ε. -/
theorem constrained_step_fixed_internal (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (A G : ℝ)
    (hAlo : 3 / 2 - s.val ≤ A) (_hAhi : A ≤ 2 - s.val)
    (hGlo : 1 - s.val / 2 ≤ G) (_hGhi : G ≤ (3 - s.val) / 2) (_hGA : G ≤ A)
    (hcurrent : UniformProfile s A G false)
    (κstar γstar : ℝ) (M₀ : ℕ+) (hκstar : 0 < κstar) (hγstar : 0 < γstar) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε →
    ∀ Cstar : ℝ, 1 ≤ Cstar → ∀ βlo : ℝ, 0 < βlo → ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧
      EstimateAt s κstar γstar M₀ (min (2 - s.val) (A + 1 - s.val))
        (min ((3 - s.val) / 2) (G + 1 - s.val)) true κ ε Cstar βlo βhi C := by
  obtain ⟨κz, κφ, κg, Dd, hκz, hκφ, hκg, hDd, hdec⟩ :=
    localized_decomposition_internal hzeta s κstar γstar hκstar hγstar M₀
  obtain ⟨κp, Dp, hκp, hDp, hpoint⟩ :=
    window_point_source_internal s A G hcurrent κstar γstar M₀ hκstar hγstar
  obtain ⟨κl, γl, Dl, hκl, hγl, hDl, hlocal⟩ :=
    ReferenceComparisonError.localization_for_representation_internal s κstar γstar M₀ hκstar hγstar
  have hA : 0 < A := by linarith only [hAlo, s.property.2]
  have hG : 0 < G := by linarith only [hGlo, s.property.2]
  have hp : 0 < 2 - s.val := by linarith [s.property.2]
  have hpg : 0 < (3 - s.val) / 2 := by linarith [s.property.2]
  have hpgp : (3 - s.val) / 2 ≤ 2 - s.val := by linarith [s.property.2]
  obtain ⟨Ce, hCe, herr⟩ := OptimalLocalization.comparison_error_internal s A G hA hG
  let D := max (max Dd Dp) Dl
  let κ := κstar + D * (2 - s.val) + κz + κφ + κg + κp + 1
  have hD : 0 < D := hDd.trans_le ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨κ, by dsimp only [κ]; positivity, ?_⟩
  intro ε hε Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Cz, Cφ, Cg, hCz, hCφ, hCg, hdec⟩ := hdec ε hε Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Cp, hCp, hpoint⟩ := hpoint ε hε Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Cl, hCl, hlocal⟩ := hlocal Cstar hCstar
  obtain ⟨L, hL, hlog⟩ := OptimalLocalization.logarithmic_loss_internal s ε hε
  let Bs := 1 + 2 * βlo⁻¹ * Cstar
  let B := Bs + Cz + Cφ + 2 * Ce * Cp * Cg * L
  let C := (17 ^ (2 - s.val) + 2 ^ (2 - s.val)) * B
  have hBs : 0 < Bs := by dsimp only [Bs]; positivity
  have hB : 0 < B := by dsimp only [B]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Ω _ ν _ Q hQ hQc n m hm hn hnm hmn K hK hKm M hM β hβl hβu i₀ χ
  have hβ : 0 < β := hβlo.trans_le hβl
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by positivity
  have hκsmall (t : ℝ) (ht : t ≤ 2 - s.val) : κstar + D * t ≤ κ := by
    have hh := mul_le_mul_of_nonneg_left ht hD.le
    dsimp only [κ]
    linarith only [hh, hκz, hκφ, hκg, hκp]
  have hκz' : κz ≤ κ := by dsimp only [κ]; linarith only [hκstar, hκz, hκφ, hκg, hκp, mul_nonneg hD.le hp.le]
  have hκφ' : κφ ≤ κ := by dsimp only [κ]; linarith only [hκstar, hκz, hκφ, hκg, hκp, mul_nonneg hD.le hp.le]
  have hκe' : κp + κg + 1 ≤ κ := by dsimp only [κ]; linarith only [hκstar, hκz, hκφ, hκg, hκp, mul_nonneg hD.le hp.le]
  let a := Cstar⁻¹ * (n : ℝ) ^ (-κstar * ε)
  have hl : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
      ∀ z : Fin (m : ℕ) → ℝ, a * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j :=
    hM.2.1.mono (fun _ hx => ⟨hx.1, hx.2.2.1⟩)
  obtain ⟨u, hu, huniq⟩ := (AbstractEquation.existence_energy Q hQ β hβ M hM.1 a
    (SchurRestriction.periodized_mass_pos hCstar) hl (zeroSumComponents _)
    (fun i => if i = i₀ then χ else 0)).1
  refine ⟨u, ⟨hu, ?_⟩, fun v hv => huniq v hv.1⟩
  intro j
  let R : ℝ := Riesz1.cyclicIndexDistance m j i₀
  let av := min (2 - s.val) (A + 1 - s.val)
  let gv := min ((3 - s.val) / 2) (G + 1 - s.val)
  have hav0 : 0 ≤ av := le_min hp.le (by linarith [s.property.2])
  have hgv0 : 0 ≤ gv := le_min hpg.le (by linarith [s.property.2])
  have havp : av ≤ 2 - s.val := min_le_left _ _
  have hgvp : gv ≤ 2 - s.val := (min_le_left _ _).trans hpgp
  by_cases hsmall : R < max 16 ((n : ℝ) ^ (D * ε))
  · have henergy := GlobalDecay.global_energy_unweighted s n m hm K Cstar κstar γstar ε
      hCstar hκstar.le hε.le Q hQ M hM βlo β hβlo hβl χ i₀ u hu
    have hplain : ∀ j, ‖(u j).val‖ ≤ Bs * (n : ℝ) ^ (κstar * ε) * ‖χ‖ ∧
        Real.sqrt (Q.2 (u j) (u j)) ≤ Bs * (n : ℝ) ^ (κstar * ε) * ‖χ‖ := by
      simpa only [neg_zero, Real.rpow_zero, one_mul, mul_one] using
        OptimalLocalizationBootstrap.component_bounds_internal Q hQ m i₀ 0 0 _ u
          (by simpa only [mul_zero, Real.rpow_zero, one_mul] using henergy)
    have lift (t x : ℝ) (ht : 0 ≤ t) (htp : t ≤ 2 - s.val)
        (hx : x ≤ Bs * (n : ℝ) ^ (κstar * ε) * ‖χ‖) :
        x ≤ C * (n : ℝ) ^ (κ * ε) * (1 + R) ^ (-t) * ‖χ‖ := by
      have hh := OptimalLocalization.small_distance_internal (n : ℝ) ε D κstar t R Bs ‖χ‖ x
        hn1 hε.le hD.le ht (by dsimp only [R]; positivity) hsmall hBs.le (norm_nonneg χ) hx
      apply hh.trans
      have hcb : 17 ^ t * Bs ≤ C := by
        have ht17 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 17) htp
        have hBsB : Bs ≤ B := by dsimp only [B]; linarith only [hCz, hCφ, show 0 ≤ Ce * Cp * Cg * L by positivity]
        dsimp only [C]
        exact mul_le_mul (ht17.trans (le_add_of_nonneg_right (by positivity))) hBsB hBs.le (by positivity)
      have hco := LocalizedMatrix.loss_mono_internal hn1 hε.le (by positivity) hcb (hκsmall t htp)
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hco
        (by positivity : 0 ≤ (1 + R) ^ (-t))) (norm_nonneg χ)
      exact hh
    exact ⟨lift av _ hav0 havp (hplain j).1, lift gv _ hgv0 hgvp (hplain j).2⟩
  · have hlarge : max 16 ((n : ℝ) ^ (D * ε)) ≤ R := le_of_not_gt hsmall
    have hR : 16 ≤ Riesz1.cyclicIndexDistance m j i₀ := by
      have hh : (16 : ℝ) ≤ (Riesz1.cyclicIndexDistance m j i₀ : ℝ) := (le_max_left _ _).trans hlarge
      exact_mod_cast hh
    have hR16 : 16 ≤ R := (le_max_left _ _).trans hlarge
    have hR1 : 1 ≤ R := by linarith
    have hRm : R ≤ (m : ℝ) := by
      have hh := Riesz1.APG.cyclicIndexDistance_le_half j i₀
      dsimp only [R]
      exact_mod_cast (show Riesz1.cyclicIndexDistance m j i₀ ≤ (m : ℕ) by omega)
    have sep (d : ℝ) (hd : d ≤ D) : (n : ℝ) ^ (d * ε) ≤ R :=
      (Real.rpow_le_rpow_of_exponent_le hn1 (mul_le_mul_of_nonneg_right hd hε.le)).trans
        ((le_max_right _ _).trans hlarge)
    obtain ⟨Ac, hAm, hArep, hdec⟩ := hdec ν Q hQ hQc n m hm hn hnm hmn hK hKm M hM
    obtain ⟨ψ, z, φ, hψ, hz, hφv, hφg, g, hgeq, hmass, hcentral⟩ :=
      hdec j i₀ hR (sep Dd ((le_max_left _ _).trans (le_max_left _ _))) β hβl hβu χ u hu
    let n₀ := LocalizedMatrix.windowSize m j i₀
    let m₀ := LocalizedMatrix.windowPeriod s m j i₀
    have hsize := LocalizedMatrix.window_size_bounds m j i₀ hR
    have htwo := LocalizedMatrix.two_windowSize_lt_period s m j i₀ hR
    have hnp : (n₀ : ℕ) ≤ (m : ℕ) := by dsimp only [n₀]; omega
    have hn₀ : (n₀ : ℕ) ≤ (m₀ : ℕ) := by dsimp only [n₀, m₀]; omega
    have hm₀ : 2 ≤ (m₀ : ℕ) := by have := n₀.pos; dsimp only [n₀, m₀] at *; omega
    let b : Fin (m : ℕ) := j - ↑(Riesz1.cyclicIndexDistance m j i₀ / 8)
    let Ml := LocalizedMatrix.matrix s m m₀ n₀ hm₀ hnp hn₀ K (fun t => Ac (t.1 + b, t.2))
    let c : Fin (m₀ : ℕ) := ⟨Riesz1.cyclicIndexDistance m j i₀ / 8, by
      have hc := LocalizedMatrix.window_card m j i₀
      change (n₀ : ℕ) = _ at hc
      omega⟩
    have hMl := hlocal ν ε hε n m hn hm M hM Ac hAm (hArep.mono fun _ hx => hx.2)
      j i₀ hR (sep Dl (le_max_right _ _))
    have hpoint' : ∀ (ζ : Lp ℝ 2 ν) (i : Fin (m₀ : ℕ)),
        ∃ v : Fin (m₀ : ℕ) → Q.1,
          WeightedWeakSolution Q (fun x => β • Ml x) ⊤ (fun k => if k = i then ζ else 0) v ∧
          ∀ l, ‖(v l).val‖ ≤ Cp * (n : ℝ) ^ (κp * ε) * weightRadius m₀ l i ^ (-A) * ‖ζ‖ ∧
            Real.sqrt (Q.2 (v l) (v l)) ≤ Cp * (n : ℝ) ^ (κp * ε) * weightRadius m₀ l i ^ (-G) * ‖ζ‖ := by
      intro ζ i
      obtain ⟨v, hv, _⟩ := hpoint ε le_rfl ν Q hQ hQc n m hn hm hnm hmn hK M hM Ac hAm
        (hArep.mono fun _ hx => hx.2) j i₀ hR
        (sep Dp ((le_max_right _ _).trans (le_max_left _ _))) β hβl hβu i ζ
      exact ⟨v, hv⟩
    have herr' := herr ν Q hQ n₀ m₀ hm₀ K Cl κl γl
      (ε * Real.log (n : ℝ) / Real.log (n₀ : ℝ)) β hCl hβ Ml hMl
      (Cp * (n : ℝ) ^ (κp * ε)) (by positivity) hpoint' g
      (fun i => ψ i - z i - φ i) hgeq c R
      (Cg * (n : ℝ) ^ (κg * ε) * ‖χ‖) hR16 (by positivity) hmass hcentral
    let Z := Cz * (n : ℝ) ^ (κz * ε) * ‖χ‖
    let P := Cφ * (n : ℝ) ^ (κφ * ε) * ‖χ‖
    let E := (Ce * Cp * Cg * L) * (n : ℝ) ^ ((κp + κg + 1) * ε) * ‖χ‖
    have herrBound (x q : ℝ) (hx : x ≤ Ce * (Cp * (n : ℝ) ^ (κp * ε)) *
        (Cg * (n : ℝ) ^ (κg * ε) * ‖χ‖) * (1 + Real.log (2 * R)) *
        (R ^ (-(2 - s.val)) + R ^ (-q))) :
        x ≤ E * (R ^ (-(2 - s.val)) + R ^ (-q)) := by
      apply hx.trans
      have hh := mul_le_mul_of_nonneg_left (hlog n m hn hm hmn R hR1 hRm)
        (show 0 ≤ Ce * (Cp * (n : ℝ) ^ (κp * ε)) * (Cg * (n : ℝ) ^ (κg * ε) * ‖χ‖) by positivity)
      apply (mul_le_mul_of_nonneg_right hh (by positivity)).trans_eq
      dsimp only [E]
      rw [show (κp + κg + 1) * ε = κp * ε + κg * ε + ε by ring,
        Real.rpow_add hn0, Real.rpow_add hn0]
      ring
    have hev := herrBound _ (A + 1 - s.val) herr'.1
    have heg := herrBound _ (G + 1 - s.val) herr'.2
    have hz' := unweight_boundary_internal R _ _ _ _ Z (by linarith) (norm_nonneg _)
      (Real.sqrt_nonneg _) hz
    have htri := decomposition_triangles_internal Q hQ m j i₀ hR m₀ hn₀ u ψ z φ hψ
    have hv := OptimalLocalization.assemble_profile_internal R (2 - s.val) (A + 1 - s.val) av
      Z P E _ _ _ _ hR1 hav0 (min_le_left _ _) (min_le_right _ _)
      (by positivity) (by positivity) (by positivity) htri.1 hz'.1 hφv hev
    have heg' : Real.sqrt (Q.2 (ψ c - z c - φ c) (ψ c - z c - φ c)) ≤
        E * (R ^ (-((3 - s.val) / 2)) + R ^ (-(G + 1 - s.val))) := by
      apply heg.trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hrpow : R ^ (-(2 - s.val)) ≤ R ^ (-((3 - s.val) / 2)) :=
        Real.rpow_le_rpow_of_exponent_le hR1 (by linarith only [hpgp])
      exact add_le_add hrpow le_rfl
    have hφg' : Real.sqrt (Q.2 (φ c) (φ c)) ≤ P * R ^ (-((3 - s.val) / 2)) := by
      simpa only [neg_div] using hφg
    have hg := OptimalLocalization.assemble_profile_internal R ((3 - s.val) / 2) (G + 1 - s.val) gv
      Z P E _ _ _ _ hR1 hgv0 (min_le_left _ _) (min_le_right _ _)
      (by positivity) (by positivity) (by positivity) htri.2 hz'.2 hφg' heg'
    have hsum : Z + P + 2 * E ≤ B * (n : ℝ) ^ (κ * ε) * ‖χ‖ := by
      have hzcoef := LocalizedMatrix.loss_mono_internal hn1 hε.le hCz.le le_rfl hκz'
      have hpcoef := LocalizedMatrix.loss_mono_internal hn1 hε.le hCφ.le le_rfl hκφ'
      have hecoef := LocalizedMatrix.loss_mono_internal hn1 hε.le
        (show 0 ≤ Ce * Cp * Cg * L by positivity) le_rfl hκe'
      have hh := add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right hzcoef (norm_nonneg χ))
        (mul_le_mul_of_nonneg_right hpcoef (norm_nonneg χ)))
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hecoef (norm_nonneg χ))
          (by norm_num : (0 : ℝ) ≤ 2))
      apply hh.trans
      dsimp only [B]
      nlinarith only [show 0 ≤ Bs * (n : ℝ) ^ (κ * ε) * ‖χ‖ by positivity]
    have lift (t x : ℝ) (htp : t ≤ 2 - s.val)
        (hx : x ≤ (2 ^ t * (Z + P + 2 * E)) * (1 + R) ^ (-t)) :
        x ≤ C * (n : ℝ) ^ (κ * ε) * (1 + R) ^ (-t) * ‖χ‖ := by
      have ht2 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) htp
      have hc : 2 ^ t * (Z + P + 2 * E) ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ := by
        have ht2' : (2 : ℝ) ^ t ≤ 17 ^ (2 - s.val) + 2 ^ (2 - s.val) :=
          ht2.trans (le_add_of_nonneg_left (by positivity))
        have hh := mul_le_mul ht2' hsum
          (by positivity : 0 ≤ Z + P + 2 * E) (by positivity)
        convert hh using 1; dsimp only [C]; ring
      exact hx.trans ((mul_le_mul_of_nonneg_right hc (by positivity)).trans_eq (by ring))
    exact ⟨lift av _ havp hv, lift gv _ hgvp hg⟩



/-- See Subsection 5.5 of the paper: specialize the uniform prefactor to one ε,
retaining the abstract scalar space used by the step composition. -/
theorem uniformProfile_fixed_internal (s : Riesz1.RieszExponent) (A G : ℝ) (b : Bool)
    (h : UniformProfile s A G b)
    (κstar γstar : ℝ) (M₀ : ℕ+) (hκstar : 0 < κstar) (hγstar : 0 < γstar) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε →
    ∀ Cstar : ℝ, 1 ≤ Cstar → ∀ βlo : ℝ, 0 < βlo → ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧ EstimateAt s κstar γstar M₀ A G b κ ε Cstar βlo βhi C := by
  obtain ⟨κ, hκ, hp⟩ := h κstar γstar M₀ hκstar hγstar
  refine ⟨κ, hκ, fun ε hε Cstar hCstar βlo hβlo βhi hβhi => ?_⟩
  obtain ⟨C, hC, hp⟩ := hp ε hε Cstar hCstar βlo hβlo βhi hβhi
  exact ⟨C, hC, hp ε le_rfl⟩

/-- Fixed-ε conclusion of the proof of Proposition 5.15
under the uniform induction assertion of Subsection 5.5. The constrained improvement follows from the local construction.
The prefactor is chosen for the fixed ε. -/
theorem unconstrained_step_fixed_internal (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (A G : ℝ)
    (hAlo : 3 / 2 - s.val ≤ A) (hAhi : A ≤ 2 - s.val)
    (hGlo : 1 - s.val / 2 ≤ G) (hGhi : G ≤ (3 - s.val) / 2) (hGA : G ≤ A)
    (hcurrent : ∀ b, UniformProfile s A G b)
    (κstar γstar : ℝ) (M₀ : ℕ+) (hκstar : 0 < κstar) (hγstar : 0 < γstar) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε →
    ∀ Cstar : ℝ, 1 ≤ Cstar → ∀ βlo : ℝ, 0 < βlo → ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧
      EstimateAt s κstar γstar M₀ (min (2 - s.val) (A + 1 - s.val))
        (min ((3 - s.val) / 2) (G + 1 - s.val)) false κ ε Cstar βlo βhi C := by
  have ht := uniformProfile_fixed_internal s A G true (hcurrent true) κstar γstar M₀ hκstar hγstar
  have hf := uniformProfile_fixed_internal s A G false (hcurrent false) κstar γstar M₀ hκstar hγstar
  have hc := constrained_step_fixed_internal hzeta s A G hAlo hAhi hGlo hGhi hGA
    (hcurrent false) κstar γstar M₀ hκstar hγstar
  exact OptimalLocalizationUnconstrained.unconstrained_step_internal hzeta s κstar γstar
    hκstar hγstar M₀ A G hAlo hAhi hGlo hGhi hGA ⟨ht, hf⟩ hc

/-- Composition for Proposition 5.15, assuming the constrained improvement
preserves `UniformProfile`. The unrestricted step, base case and finite
saturation give the conclusion. -/
theorem optimal_decay_of_uniform_step_internal (hzeta : External.PeriodicZeta)
    (hconstrained : ∀ (s : Riesz1.RieszExponent) (A G : ℝ),
      3 / 2 - s.val ≤ A → A ≤ 2 - s.val →
      1 - s.val / 2 ≤ G → G ≤ (3 - s.val) / 2 → G ≤ A →
      (∀ b, UniformProfile s A G b) →
      UniformProfile s (min (2 - s.val) (A + 1 - s.val))
        (min ((3 - s.val) / 2) (G + 1 - s.val)) true) :
  ∀ (s : Riesz1.RieszExponent) (κₛ γₛ : ℝ) (M₀ : ℕ+),
    0 < κₛ → 0 < γₛ → ∃ κ : ℝ, 0 < κ ∧
    ∀ ε : ℝ, 0 < ε → ∀ Cₛ : ℝ, 1 ≤ Cₛ →
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
      ∃ C : ℝ, 0 < C ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n m : ℕ+) (_ : 2 ≤ (n : ℕ)) (hm : 2 ≤ (m : ℕ)),
        (n : ℕ) ≤ (m : ℕ) → (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
        let K := (Nat.floor ((n : ℝ) ^ ε)) ^ (M₀ : ℕ)
        1 ≤ K → 4 * K ≤ (m : ℕ) →
        ∀ (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d)))
          (ν : Measure (EuclideanSpace ℝ (Fin d))),
          IsOpen Ω → Convex ℝ Ω → Bornology.IsBounded Ω → Ω.Nonempty →
          IsProbabilityMeasure ν →
          (∃ V : EuclideanSpace ℝ (Fin d) → ℝ,
            IsEuclideanGibbsPotential volume ν Ω V 2) →
          ∀ Q : ScalarFormData ν, IsNeumannRealization Ω Q →
            IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
          ∀ M : EuclideanSpace ℝ (Fin d) → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
            PeriodizedMatrixBounds (ν := ν) s n m hm K Cₛ κₛ γₛ ε M →
            ∀ (i₀ : Fin (m : ℕ)) (χ : Lp ℝ 2 ν) (b : Bool),
              let S := if b then zeroSumComponents (Fin (m : ℕ)) else ⊤
              (∃! u : Fin (m : ℕ) → Q.1, WeightedWeakSolution Q
                (fun x => β.val • M x) S (fun i => if i = i₀ then χ else 0) u) ∧
              (∀ u : Fin (m : ℕ) → Q.1, WeightedWeakSolution Q
                  (fun x => β.val • M x) S (fun i => if i = i₀ then χ else 0) u →
                ∀ j : Fin (m : ℕ),
                  ‖(u j).val‖ ≤ C * (n : ℝ) ^ (κ * ε) *
                    (1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ)) ^ (-(2 - s.val)) * ‖χ‖ ∧
                  Real.sqrt (Q.2 (u j) (u j)) ≤ C * (n : ℝ) ^ (κ * ε) *
                    (1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ)) ^ (-(3 - s.val) / 2) * ‖χ‖) := by
  intro s κₛ γₛ M₀ hκₛ hγₛ
  have hfinal : ∀ b, UniformProfile s (2 - s.val) ((3 - s.val) / 2) b := by
    apply OptimalLocalizationBootstrap.finite_saturation_internal s
      (fun A G => ∀ b, UniformProfile s A G b) (base_uniform_internal hzeta s)
    intro A G hA hA' hG hG' hGA h b
    have hc := hconstrained s A G hA hA' hG hG' hGA h
    cases b
    · exact unconstrained_step_uniform_internal hzeta s A G hA hG (h false) hc
    · exact hc
  obtain ⟨κt, hκt, ht⟩ := uniformProfile_forget_internal s _ _ true (hfinal true) κₛ γₛ M₀ hκₛ hγₛ
  obtain ⟨κf, hκf, hf⟩ := uniformProfile_forget_internal s _ _ false (hfinal false) κₛ γₛ M₀ hκₛ hγₛ
  refine ⟨κt + κf, by positivity, fun ε hε Cₛ hCₛ βlo βhi hβlo hβhi => ?_⟩
  obtain ⟨Ct, hCt, ht⟩ := ht ε hε Cₛ hCₛ βlo βhi hβlo hβhi
  obtain ⟨Cf, hCf, hf⟩ := hf ε hε Cₛ hCₛ βlo βhi hβlo hβhi
  refine ⟨Ct + Cf, by positivity, ?_⟩
  intro β hβ n m hn hm hnm hmn K hK hKm d Ω ν hΩo hΩc hΩb hΩn hν hV Q hQN hQ hQc M hM i₀ χ b S
  have hnt : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have htf : Ct * (n : ℝ) ^ (κt * ε) ≤ (Ct + Cf) * (n : ℝ) ^ ((κt + κf) * ε) := by
    apply mul_le_mul (by linarith) _ (by positivity) (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le hnt (by nlinarith)
  have hff : Cf * (n : ℝ) ^ (κf * ε) ≤ (Ct + Cf) * (n : ℝ) ^ ((κt + κf) * ε) := by
    apply mul_le_mul (by linarith) _ (by positivity) (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le hnt (by nlinarith)
  cases b
  · obtain ⟨hex, he⟩ := hf β hβ n m hn hm hnm hmn hK hKm d Ω ν
      hΩo hΩc hΩb hΩn hν hV Q hQN hQ hQc M hM i₀ χ
    refine ⟨hex, fun u hu j => ?_⟩
    obtain ⟨hv, hg⟩ := he u hu j
    constructor
    · exact hv.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hff (by positivity)) (norm_nonneg χ))
    · have hg' := hg.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hff (by positivity)) (norm_nonneg χ))
      simpa only [neg_div] using hg'
  · obtain ⟨hex, he⟩ := ht β hβ n m hn hm hnm hmn hK hKm d Ω ν
      hΩo hΩc hΩb hΩn hν hV Q hQN hQ hQc M hM i₀ χ
    refine ⟨hex, fun u hu j => ?_⟩
    obtain ⟨hv, hg⟩ := he u hu j
    constructor
    · exact hv.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right htf (by positivity)) (norm_nonneg χ))
    · have hg' := hg.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right htf (by positivity)) (norm_nonneg χ))
      simpa only [neg_div] using hg'

end Riesz2.OptimalLocalizationPart2
