/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.FixedLengthDecayPart6
public import Riesz2.Thermodynamic.InterpolationCoefficientBounds

/-!
# Long-range physical fixed-length comparison

Physical coefficient interfaces for Lemma 6.4, using the normalized law and the native
perturbation bounds of Subsection 6.1.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical MatrixOrder ENNReal ContDiff

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.FixedLengthDecay

/-- See Lemma 6.4 of the paper: native bounded-test integrability gives
entrywise integrability on the actual probability law. Constant tests
are legitimate L² classes, and their representatives are identified a.e. -/
theorem entries_integrable_of_native_tests_internal
    {X ι : Type*} [MeasurableSpace X] [Fintype ι] [DecidableEq ι]
    (ν : Measure X) [IsProbabilityMeasure ν] (Y : X → Matrix ι ι ℝ)
    (htests : ∀ φ ψ : Lp ℝ 2 ν,
      MemLp (φ : X → ℝ) ∞ ν → MemLp (ψ : X → ℝ) ∞ ν →
      ∀ i j, Integrable (matrixFieldPair Y (Pi.single j φ) (Pi.single i ψ)) ν) :
    ∀ i j, Integrable (fun x => Y x i j) ν := by
  let h1 : MemLp (fun _ : X => (1 : ℝ)) 2 ν := memLp_const 1
  let f : Lp ℝ 2 ν := h1.toLp (fun _ => (1 : ℝ))
  have hf : (f : X → ℝ) =ᵐ[ν] fun _ => 1 := h1.coeFn_toLp
  have hft : MemLp (f : X → ℝ) ∞ ν := by
    rw [memLp_congr_ae hf]
    exact memLp_const 1
  intro i j
  apply (htests f f hft hft j i).congr
  filter_upwards [InterpolationPerturbation.matrix_point_pair_ae_internal Y f f i j, hf]
    with x hx hfx
  simpa only [hfx, one_mul] using hx

section NativePhysical

variable (β : InverseTemperature) (s : Riesz1.RieszExponent)
  (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (m : ℕ+) (hm : 2 ≤ (m : ℕ))
  (hnm : (n : ℕ) ≤ (m : ℕ)) (k : ℕ) (θ : PhysicalCutoff) (ε η t : ℝ)
  (ν : Measure (AffineSimplex.chartDomain n ((n+d : ℕ)+1)))
  (P : AffineSimplex.chartDomain n ((n+d : ℕ)+1) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)

local notation "H" => fun x : AffineSimplex.chartDomain n ((n+d : ℕ)+1) =>
  β.val • (InterpolationMatrix.penaltyHessian n θ ε (Subtype.val x) + P x)
local notation "M" => InterpolationMatrix.matrix β s n d e hde m hm hnm k θ ε η t
local notation "Y" => InterpolationMatrix.multiplicationPart β s n d e hde m hm hnm k θ ε η t P

/-- See Lemma 6.4 and Subsection 6.1 of the paper: native perturbation
integrability supplies both unbounded coefficient domains on the same law.
The auxiliary active block is integrable by its uniform bound. -/
theorem physical_entries_of_native_tests_internal [IsProbabilityMeasure ν]
    (C κ γ εM : ℝ)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm k C κ γ εM M)
    (htests : ∀ φ ψ : Lp ℝ 2 ν,
      MemLp (φ : _ → ℝ) ∞ ν → MemLp (ψ : _ → ℝ) ∞ ν →
      ∀ i j, Integrable (matrixFieldPair Y (Pi.single j φ) (Pi.single i ψ)) ν) :
    (∀ i j, Integrable (fun x => H x i j) ν) ∧
    (∀ i j, Integrable (fun x => Y x i j) ν) := by
  have hYi := entries_integrable_of_native_tests_internal ν Y htests
  obtain ⟨b, hb⟩ := SchurRestriction.periodized_scaled_bounded β.val hM
  have hAi (i j : Fin (n : ℕ)) : Integrable
      (fun x => β.val * InterpolationMatrix.activeBlock β s n d e hde m hm hnm k θ ε η t x i j) ν := by
    apply (integrable_const b).mono'
      ((InterpolationMatrix.measurable_activeBlock β s n d e hde m hm hnm k θ ε η t i j).const_mul β.val).aestronglyMeasurable
    filter_upwards [hb] with x hx
    simpa only [Matrix.smul_apply, smul_eq_mul, Real.norm_eq_abs,
      InterpolationMatrix.matrix_active] using hx (i.castLE hnm) (j.castLE hnm)
  refine ⟨fun i j => ?_, hYi⟩
  apply ((hYi i j).add (hAi i j)).congr
  apply ae_of_all
  intro x
  change Y x i j + β.val * InterpolationMatrix.activeBlock β s n d e hde m hm hnm k θ ε η t x i j = H x i j
  simp only [InterpolationMatrix.multiplicationPart_eq_defect, Matrix.smul_apply,
    Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
  ring

end NativePhysical

/-- See the proof of Lemma 6.4: the localization and summed-equation estimates work on the original scalar form,
without requiring a change of base carrier. The final clause is a component
bound for a bounded source. All constants precede the base law. -/
theorem auxiliary_on_scalar_form_internal (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ) (M₀ : ℕ+)
    (hκstar : 0 < κstar) (hγstar : 0 < γstar) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ∀ Cstar : ℝ, 1 ≤ Cstar →
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    ∀ (n m : ℕ+) (hn : 2 ≤ (n : ℕ)) (hm : 2 ≤ (m : ℕ)),
    ∀ (_hnm : 2 * (n : ℕ) ≤ (m : ℕ)),
      (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
    let K := ⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ)
    1 ≤ K → 4 * K ≤ (m : ℕ) →
    ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν],
    ∀ Q : ScalarFormData ν,
      IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
    ∀ M : X → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
      PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M →
    ∀ i₀ : Fin (n : ℕ), |(i₀.val : ℝ) + 1 - (n : ℝ) / 2| ≤ (n : ℝ) / 4 →
    ∀ (χ : Lp ℝ 2 ν) (Bχ : ℝ), 0 ≤ Bχ → (∀ᵐ x ∂ν, |χ x| ≤ Bχ) →
    let c : Fin (m : ℕ) := i₀.castLE (by omega)
    (∃! u : Fin (m : ℕ) → Q.1, WeightedWeakSolution Q
      (fun x => β.val • M x) ⊤ (fun i => if i = c then χ else 0) u) ∧
    ∀ u : Fin (m : ℕ) → Q.1, WeightedWeakSolution Q
      (fun x => β.val • M x) ⊤ (fun i => if i = c then χ else 0) u →
    let v := fun i : Fin (n : ℕ) => u (i.castLE (by omega))
    let S := ∑ i, v i
    (∀ j : Fin (n : ℕ), ‖(v j).val‖ ≤ C * (n : ℝ) ^ (κ * ε) *
      (1 + (Nat.dist j.val i₀.val : ℝ)) ^ (s.val - 2) * ‖χ‖) ∧
    (∑ j, ‖(v j).val‖) ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ ∧
    ‖S.val‖ ≤ C * (n : ℝ) ^ (κ * ε - (1 - s.val)) * ‖χ‖ ∧
    Real.sqrt (Q.2 S S) ≤ C * (n : ℝ) ^ (κ * ε - (1 - s.val) / 2) * ‖χ‖ ∧
    ∀ i, ∀ᵐ x ∂ν, |(v i).val x| ≤ C*(n : ℝ)^(κ*ε)*Bχ := by
  have hfinal : ∀ b, OptimalLocalizationPart2.UniformProfile s
      (2-s.val) ((3-s.val)/2) b := by
    apply OptimalLocalizationBootstrap.finite_saturation_internal s
      (fun A G => ∀ b, OptimalLocalizationPart2.UniformProfile s A G b)
      (OptimalLocalizationPart2.base_uniform_internal hzeta s)
    intro A G hA hA' hG hG' hGA h b
    have hc := OptimalLocalizationPart5.loc_constrained_step hzeta s A G
      hA hA' hG hG' hGA h
    cases b
    · exact OptimalLocalizationPart2.unconstrained_step_uniform_internal
        hzeta s A G hA hG (h false) hc
    · exact hc
  obtain ⟨κp, hκp, hpoint⟩ := hfinal false κstar γstar M₀ hκstar hγstar
  obtain ⟨κe, hκe, herror⟩ := global_error_differences s κstar γstar hκstar.le hγstar.le (M₀ : ℕ)
  obtain ⟨c₀, C₀, hc₀, _, hmass⟩ := global_reference_mass_bounds s
  let κ := κp + κe + κstar
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  refine ⟨κ, hκ, fun ε hε Cstar hCstar βlo βhi hβlo hβhi => ?_⟩
  obtain ⟨Cp, hCp, hpoint⟩ := hpoint ε hε Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Ce, hCe, herror⟩ := herror ε hε Cstar hCstar
  let D := 2 * ∑' r : ℕ, (1 + (r : ℝ)) ^ (-(2 - s.val))
  let Tv := 2 * (1 + 1 / (1 - s.val)) * 4 ^ (1 - s.val)
  let Tg := 2 * (1 + 1 / ((3 - s.val) / 2 - 1)) * 4 ^ ((3 - s.val) / 2 - 1)
  let B := 1 + βhi * Ce * Cp * D
  let V := (βlo * c₀)⁻¹ * B
  let G := (Real.sqrt (βlo * c₀))⁻¹ * B
  let C := 1 + Cp + Cp * D + V + Cp * Tv + G + Cp * Tg + βlo⁻¹ * Cstar
  have hD : 0 ≤ D := mul_nonneg (by norm_num) (tsum_nonneg fun _ => by positivity)
  have hs1 : 0 < 1 - s.val := sub_pos.mpr s.property.2
  have hqt : 0 < (3 - s.val) / 2 - 1 := by linarith [s.property.2]
  have hTv : 0 < Tv := by dsimp only [Tv]; positivity
  have hTg : 0 < Tg := by dsimp only [Tg]; positivity
  have hβhi0 : 0 < βhi := hβlo.trans_le hβhi
  have hCe0 : 0 < Ce := zero_lt_one.trans_le hCe
  have hB : 0 < B := by dsimp only [B]; positivity
  have hV : 0 < V := by dsimp only [V]; positivity
  have hG : 0 < G := by dsimp only [G]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro β hβ n m hn hm hnm hmn K hK hKm X _ ν _ Q hQ hQc M hM i₀ hi₀ χ Bχ hBχ hχ c
  have hβpos : 0 < β.val := β.property
  have hnm' : (n : ℕ) ≤ (m : ℕ) := by omega
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by positivity
  let L := (n : ℝ) ^ (κ * ε)
  let Ap := Cp * (n : ℝ) ^ (κp * ε)
  let Be := Ce * (n : ℝ) ^ (κe * ε)
  have hL : 1 ≤ L := Real.one_le_rpow hn1 (mul_nonneg hκ.le hε.le)
  have hAp : 0 ≤ Ap := by dsimp only [Ap]; positivity
  have hBe : 0 ≤ Be := by dsimp only [Be]; positivity
  have hk₁ : κp ≤ κ := by dsimp only [κ]; linarith
  have hk₂ : κp + κe ≤ κ := by dsimp only [κ]; linarith
  have hApL : Ap ≤ Cp * L :=
    LocalizedMatrix.loss_mono_internal hn1 hε.le hCp.le le_rfl hk₁
  have hprod : Be * Ap ≤ Ce * Cp * L := by
    calc
      _ = Ce * Cp * (n : ℝ) ^ ((κp + κe) * ε) := by
        dsimp only [Be, Ap]
        rw [add_mul, Real.rpow_add hn0]
        ring
      _ ≤ _ := LocalizedMatrix.loss_mono_internal hn1 hε.le (by positivity) le_rfl hk₂
  obtain ⟨u₀, ⟨hu₀,hest⟩, _⟩ := hpoint ε le_rfl ν Q hQ hQc n m hm hn hnm'
    hmn hK hKm M hM β.val hβ.1 hβ.2 c χ
  have hl : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
      ∀ z : Fin (m : ℕ) → ℝ,
        Cstar⁻¹*(n : ℝ)^(-κstar*ε)*(∑ i, z i^2) ≤ ∑ i,∑ j, z i*M x i j*z j :=
    hM.2.1.mono (fun _ hx => ⟨hx.1,hx.2.2.1⟩)
  have hex := (AbstractEquation.existence_energy Q hQ β.val β.property M hM.1 _
    (SchurRestriction.periodized_mass_pos hCstar) hl ⊤ (fun i => if i=c then χ else 0)).1
  refine ⟨hex, ?_⟩
  intro u hu v S
  have heq : u₀ = u := hex.unique hu₀ hu
  subst u₀
  have huest := hest
  have hv : ∀ j, ‖(u j).val‖ ≤ Ap * weightRadius m j c ^ (-(2 - s.val)) * ‖χ‖ :=
    fun j => (huest j).1
  have hg : ∀ j, Real.sqrt (Q.2 (u j) (u j)) ≤
      Ap * weightRadius m j c ^ (-((3 - s.val) / 2)) * ‖χ‖ := by
    intro j
    simpa only [Ap, weightRadius, neg_div] using (huest j).2
  have hsum : (∑ j, ‖(u j).val‖) ≤ Ap * D * ‖χ‖ := by
    calc
      _ ≤ ∑ j, Ap * weightRadius m j c ^ (-(2 - s.val)) * ‖χ‖ :=
        Finset.sum_le_sum fun j _ => hv j
      _ = Ap * (∑ j, weightRadius m j c ^ (-(2 - s.val))) * ‖χ‖ := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (AuxiliaryMean.profile_sum_le m c (2 - s.val) (by linarith [s.property.2])) hAp) (norm_nonneg χ)
  obtain ⟨a, Be₀, _, _, _, _, herr⟩ := herror n m hm hn hnm' hmn hK hKm ν M hM
  let H := (2 : ℝ) • rieszMatrix s m hm
  let ell := 2 * ∑ j, sampledRieszKernel s m hm j
  have hrow : ∀ i, ∑ j, (β.val • H) i j = β.val * ell := by
    intro i
    simp only [H, ell, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, rieszMatrix_row_sum]
  have hell : c₀ * (m : ℝ) ^ (1 - s.val) ≤ ell := by
    simpa only [ell, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, rieszMatrix_row_sum] using
      (hmass m hm c).1
  have hellpos : 0 < ell := (mul_pos hc₀ (Real.rpow_pos_of_pos (by positivity) _)).trans_le hell
  have herows : ∀ᵐ x ∂ν, ∀ i, |∑ j, (β.val • M x - β.val • H) i j| ≤ β.val * Be := by
    filter_upwards [herr] with x hx
    intro i
    have hh := hx.2.2.2.1 i
    calc
      _ = β.val * |∑ j, (M x - H) i j| := by
        simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, ← mul_sub,
          ← Finset.mul_sum, abs_mul, abs_of_pos β.property]
      _ ≤ β.val * ∑ j, |(M x - H) i j| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) β.property.le
      _ ≤ _ := mul_le_mul_of_nonneg_left hh β.property.le
  have hscalar := AuxiliaryMean.summed_estimates_internal Q hQ m (fun x => β.val • M x)
    (SchurRestriction.periodized_scaled_measurable β.val hM)
    (SchurRestriction.periodized_scaled_bounded β.val hM)
    (β.val • H) (β.val * ell) (β.val * Be) (by positivity) (by positivity)
    hrow herows c χ u hu
  have hsource : ‖χ‖ + β.val * Be * ∑ j, ‖(u j).val‖ ≤ B * L * ‖χ‖ := by
    have ht := mul_le_mul_of_nonneg_left hsum (show 0 ≤ β.val * Be by positivity)
    have ht' : β.val * Be * (Ap * D * ‖χ‖) ≤ βhi * Ce * Cp * L * D * ‖χ‖ := by
      calc
        _ = β.val * (Be * Ap) * D * ‖χ‖ := by ring
        _ ≤ βhi * (Ce * Cp * L) * D * ‖χ‖ := by gcongr; exact hβ.2
        _ = _ := by ring
    have hf := mul_le_mul_of_nonneg_right hL (norm_nonneg χ)
    dsimp only [B]
    nlinarith only [ht, ht', hf]
  have hfull := AuxiliaryMean.reference_mass_powers_internal s.val c₀ βlo β.val ell (n : ℝ) (m : ℝ)
    (B * L) ‖χ‖ ‖(∑ j, u j).val‖ (Real.sqrt (Q.2 (∑ j, u j) (∑ j, u j)))
    hc₀ hβlo hβ.1 hn0 (by exact_mod_cast hnm') s.property.2 hell (by positivity) (norm_nonneg χ)
    (hscalar.1.trans (mul_le_mul_of_nonneg_left hsource (by positivity)))
    (hscalar.2.trans (mul_le_mul_of_nonneg_left hsource (by positivity)))
  have hsub := AuxiliaryMean.subtract_exterior_internal Q hQ n m hnm i₀ hi₀
    (2 - s.val) ((3 - s.val) / 2) Ap ‖χ‖ (by linarith [s.property.2])
    (by linarith [s.property.2]) hAp (norm_nonneg χ) u hv hg
  have hpD : 0 ≤ Cp * D := mul_nonneg hCp.le hD
  have hpTv : 0 ≤ Cp * Tv := by positivity
  have hpTg : 0 ≤ Cp * Tg := by positivity
  have hβC : 0 ≤ βlo⁻¹ * Cstar := by positivity
  have hpointC : Cp ≤ C := by dsimp only [C]; linarith
  have hsumC : Cp * D ≤ C := by dsimp only [C]; linarith
  have hvC : V + Cp * Tv ≤ C := by dsimp only [C]; linarith
  have hgC : G + Cp * Tg ≤ C := by dsimp only [C]; linarith
  have hsupC : βlo⁻¹ * Cstar ≤ C := by dsimp only [C]; linarith
  have hloss : Ap ≤ C * L := hApL.trans (mul_le_mul_of_nonneg_right hpointC (by positivity))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    have he := (hsub.1 j).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hloss (by positivity)) (norm_nonneg χ))
    simpa only [show -(2 - s.val) = s.val - 2 by ring] using he
  · exact hsub.2.1.trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hApL hD) (norm_nonneg χ)).trans
      (by nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        hsumC (show 0 ≤ L by positivity)) (norm_nonneg χ)]))
  · have hh := hsub.2.2.1.trans (add_le_add hfull.1 le_rfl)
    have ht := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hApL hTv.le) (by positivity : 0 ≤ (n : ℝ) ^ (1 - (2 - s.val))))
      (norm_nonneg χ)
    have hpow : (n : ℝ) ^ (κ * ε - (1 - s.val)) = L * (n : ℝ) ^ (-(1 - s.val)) := by
      dsimp only [L]
      rw [sub_eq_add_neg, Real.rpow_add hn0]
    rw [hpow]
    have hc := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hvC (show 0 ≤ L by positivity)) (by positivity : 0 ≤ (n : ℝ) ^ (-(1 - s.val)))) (norm_nonneg χ)
    dsimp only [V, Tv] at hc
    rw [show 1 - (2 - s.val) = -(1 - s.val) by ring] at ht hh
    rw [show 2 - s.val - 1 = 1 - s.val by ring] at hh
    dsimp only [Tv] at ht
    change ‖S.val‖ ≤ _ at hh
    nlinarith only [hh, ht, hc]
  · have hh := hsub.2.2.2.trans (add_le_add hfull.2 le_rfl)
    have ht := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hApL hTg.le) (by positivity : 0 ≤ (n : ℝ) ^ (1 - (3 - s.val) / 2)))
      (norm_nonneg χ)
    have hpow : (n : ℝ) ^ (κ * ε - (1 - s.val) / 2) = L * (n : ℝ) ^ (-(1 - s.val) / 2) := by
      dsimp only [L]
      rw [sub_eq_add_neg, Real.rpow_add hn0, neg_div]
    rw [hpow]
    have hc := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hgC (show 0 ≤ L by positivity)) (by positivity : 0 ≤ (n : ℝ) ^ (-(1 - s.val) / 2))) (norm_nonneg χ)
    dsimp only [G, Tg] at hc
    rw [show 1 - (3 - s.val) / 2 = -(1 - s.val) / 2 by ring] at ht hh
    dsimp only [Tg] at ht
    change Real.sqrt (Q.2 S S) ≤ _ at hh
    nlinarith only [hh, ht, hc]
  · let a₀ := β.val * (Cstar⁻¹ * (n : ℝ) ^ (-κstar * ε))
    have ha₀ : 0 < a₀ := mul_pos β.property (SchurRestriction.periodized_mass_pos hCstar)
    have hlower := SchurRestriction.periodized_scaled_lower β.val β.property hM
    have hsym := hM.2.1
    have hcoerc : ∀ᵐ x ∂ν, (∀ i j, (β.val • M x) i j = (β.val • M x) j i) ∧
        ∀ z : Fin (m : ℕ) → ℝ,
          a₀ * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * (β.val • M x) i j * z j := by
      filter_upwards [hsym, hlower] with x hx hy
      exact ⟨fun i j => by simp only [Matrix.smul_apply, hx.1 i j], hy⟩
    have hh := (point_source_ae_bound_internal Q hQ (fun x => β.val • M x)
      (SchurRestriction.periodized_scaled_measurable β.val hM) a₀ ha₀ hcoerc
      ⊤ c χ Bχ hBχ hχ u hu).2
    have ha : a₀⁻¹ ≤ βlo⁻¹ * Cstar * (n : ℝ) ^ (κstar * ε) := by
      have he : a₀⁻¹ = β.val⁻¹ * Cstar * (n : ℝ) ^ (κstar * ε) := by
        dsimp only [a₀]
        rw [mul_inv, mul_inv, inv_inv, ← Real.rpow_neg hn0.le,
          show -(-κstar * ε) = κstar * ε by ring]
        ring
      rw [he]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (inv_anti₀ hβlo hβ.1) (by linarith : 0 ≤ Cstar)) (by positivity)
    have hk : κstar ≤ κ := by dsimp only [κ]; linarith
    have hlast := ha.trans (LocalizedMatrix.loss_mono_internal hn1 hε.le (by positivity) hsupC hk)
    intro i
    exact (hh (i.castLE hnm')).mono fun x hx => hx.trans
      (mul_le_mul_of_nonneg_right hlast hBχ)


/-- See the proof of Lemma 6.4 in the paper: the exact auxiliary Schur inverse and
all five estimates on an arbitrary closed conservative scalar form. This
uses the existing full-domain Schur lift and its unique weak equation. -/
theorem schur_on_scalar_form_internal (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ) (M₀ : ℕ+)
    (hκstar : 0 < κstar) (hγstar : 0 < γstar) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ∀ Cstar : ℝ, ∀ hCstar : 1 ≤ Cstar,
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    ∀ (n m : ℕ+) (hn : 2 ≤ (n : ℕ)) (hm : 2 ≤ (m : ℕ)),
    ∀ (hnm : 2 * (n : ℕ) ≤ (m : ℕ)),
      (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
    let K := ⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ)
    1 ≤ K → 4 * K ≤ (m : ℕ) →
    ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν],
    ∀ (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q), IsConservativeScalarForm Q →
    ∀ (M : X → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
      (hM : PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M),
    ∀ i₀ : Fin (n : ℕ), |(i₀.val : ℝ) + 1 - (n : ℝ) / 2| ≤ (n : ℝ) / 4 →
    ∀ (χ : Lp ℝ 2 ν) (Bχ : ℝ), 0 ≤ Bχ → (∀ᵐ x ∂ν, |χ x| ≤ Bχ) →
    let f : PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν) :=
      WithLp.toLp 2 (fun i => if i = i₀ then χ else 0)
    let Abar := SchurRestriction.schurForm Q hQ n m (by omega) s hm K
      Cstar κstar γstar ε β.val hCstar β.property M hM
    (∃! v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ,
      ∀ w, Abar v w = inner ℝ f (OperatorSchur.vectorValues Q hQ w)) ∧
    ∀ v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ,
      (∀ w, Abar v w = inner ℝ f (OperatorSchur.vectorValues Q hQ w)) →
    let v' := MatrixEnergy.vectorEquiv Q hQ v
    let S := ∑ i, v' i
    (∀ j : Fin (n : ℕ), ‖(v' j).val‖ ≤ C * (n : ℝ) ^ (κ * ε) *
      (1 + (Nat.dist j.val i₀.val : ℝ)) ^ (s.val - 2) * ‖χ‖) ∧
    (∑ j, ‖(v' j).val‖) ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ ∧
    ‖S.val‖ ≤ C * (n : ℝ) ^ (κ * ε - (1 - s.val)) * ‖χ‖ ∧
    Real.sqrt (Q.2 S S) ≤ C * (n : ℝ) ^ (κ * ε - (1 - s.val) / 2) * ‖χ‖ ∧
    ∀ i, ∀ᵐ x ∂ν, |(v' i).val x| ≤ C*(n : ℝ)^(κ*ε)*Bχ := by
  obtain ⟨κ, hκ, hbounds⟩ := auxiliary_on_scalar_form_internal hzeta s κstar γstar
    M₀ hκstar hγstar
  refine ⟨κ, hκ, fun ε hε Cstar hCstar βlo βhi hβlo hβhi => ?_⟩
  obtain ⟨C, hC, hbounds⟩ := hbounds ε hε Cstar hCstar βlo βhi hβlo hβhi
  refine ⟨C, hC, ?_⟩
  intro β hβ n m hn hm hnm hmn K hK hKm X _ ν _ Q hQ hQc M hM i₀ hi₀ χ Bχ hBχ hχ f Abar
  obtain ⟨hex, hlift⟩ := AuxiliaryMean.schur_lift_point_source_internal Q hQ s n m (by omega)
    hm K Cstar κstar γstar ε β.val hCstar β.property M hM i₀ χ
  refine ⟨hex, ?_⟩
  intro v hv v' S
  obtain ⟨u, hu, heq⟩ := hlift v hv
  have he := (hbounds β hβ n m hn hm hnm hmn hK hKm X ν Q hQ hQc M hM i₀ hi₀ χ Bχ hBχ hχ).2 u hu
  simpa only [heq] using he


section NativeComparison


variable (β : InverseTemperature) (s : Riesz1.RieszExponent)
  (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (m : ℕ+) (hm : 2 ≤ (m : ℕ))
  (hnm : 2*(n : ℕ) ≤ (m : ℕ)) (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ (m : ℕ)/4)
  (θ : PhysicalCutoff) (ε η t : ℝ)
  (ν : Measure (AffineSimplex.chartDomain n ((n+d : ℕ)+1)))
  (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
  (P : AffineSimplex.chartDomain n ((n+d : ℕ)+1) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)

local notation "H" => fun x : AffineSimplex.chartDomain n ((n+d : ℕ)+1) =>
  β.val • (InterpolationMatrix.penaltyHessian n θ ε (Subtype.val x) + P x)
local notation "M" => InterpolationMatrix.matrix β s n d e hde m hm (by omega) k θ ε η t
local notation "Y" => InterpolationMatrix.multiplicationPart β s n d e hde m hm (by omega) k θ ε η t P
local notation "Bnd" => BoundedL2Pairings.boundedSubmodule ν
local notation "ess" => fun f : Bnd => ENNReal.toReal (eLpNorm (fun x => (Subtype.val f) x) ∞ ν)
local notation "w" => InteractionDifferential.boundaryWeight s.val n
local notation "depth" => fun i : Fin (n : ℕ) => (min (Fin.val i+1) ((n : ℕ)-Fin.val i) : ℕ)

/-- See Lemma 6.4 of the paper: normalize the literal native physical
comparison, including its normal energy and exceptional terms, at one common
loss. The displayed squared estimate is the large-size input to the all-size composition after replacing the loss by four times itself. -/
theorem normalized_native_square_internal
    (C κ γ : ℝ) (hC : 1 ≤ C)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm k C κ γ η M)
    (hPm : ∀ i j, Measurable (fun x => P x i j))
    (hH : ∀ᵐ x ∂ν, (H x).PosSemidef)
    (hHi : ∀ i j, Integrable (fun x => H x i j) ν)
    (hYi : ∀ i j, Integrable (fun x => Y x i j) ν)
    (loss a0 D0 V0 A0 E0 βhi c δ : ℝ)
    (hloss : 0 ≤ loss) (ha0 : 0 < a0) (hD0 : 0 ≤ D0)
    (hV0 : 0 ≤ V0) (hA0 : 0 ≤ A0) (hE0 : 0 ≤ E0)
    (hβhi : β.val ≤ βhi) (hκloss : κ*η ≤ loss)
    (hlower : ∀ᵐ x ∂ν, ∀ z : Fin (n : ℕ) → ℝ,
      (a0*(n : ℝ)^(-loss))*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*H x i j*z j)
    (i₀ : Fin (n : ℕ)) (hi₀ : |(i₀.val : ℝ)+1-(n : ℝ)/2| ≤ (n : ℝ)/4)
    (χ : Lp ℝ 2 ν) (B : ℝ) (hB : 0 ≤ B)
    (hχ : ∀ᵐ x ∂ν, |χ x| ≤ B)
    (ψ v : Fin (n : ℕ) → Q.1)
    (hψ : WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ)))
      (fun i => if i = i₀ then χ else 0) ψ)
    (hv : ∀ i, ∀ᵐ x ∂ν, |(v i).val x| ≤ V0*(n : ℝ)^loss*B)
    (hvalue : ∀ i, ‖(v i).val‖ ≤ (D0*(n : ℝ)^loss)*(1+(Nat.dist i.val i₀.val : ℝ))^(s.val-2)*‖χ‖)
    (hsum : ‖(∑ i, v i : Q.1).val‖ ≤ (D0*(n : ℝ)^loss)*(n : ℝ)^(-(1-s.val))*‖χ‖)
    (hgrad : Real.sqrt (Q.2 (∑ i, v i) (∑ i, v i)) ≤
      D0*(n : ℝ)^(loss-(1-s.val)/2)*‖χ‖)
    (haux : ∀ z : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ,
      SchurRestriction.schurForm Q hQ n m (by omega) s hm k C κ γ η β.val hC β.property M hM
        ((MatrixEnergy.vectorEquiv Q hQ).symm v) z =
          inner ℝ (WithLp.toLp 2 (fun i => if i = i₀ then χ else 0))
            (OperatorSchur.vectorValues Q hQ z))
    (hpoint : ∀ (φ ζ : Bnd) (j i : Fin (n : ℕ)),
      |(∫ x, φ.val x*Y x j i*ζ.val x ∂ν) +
        InterpolationMatrix.schurPointPair ν Q hQ s β m hm k hk hkm n φ.val ζ.val
          (j.castLE (by omega)) (i.castLE (by omega))| ≤ (A0*(n : ℝ)^loss)*w j*w i*‖φ.val‖*‖ζ.val‖ + (E0*Real.exp (-c*(n : ℝ)^δ))*ess φ*ess ζ)
    (hinc : ∀ (φ ζ : Bnd) (j i l : Fin (n : ℕ)),
      |(∫ x, φ.val x*ζ.val x*(Y x j i-Y x j l) ∂ν) +
        InterpolationMatrix.schurIncrementPair ν Q hQ s β m hm k hk hkm n φ.val ζ.val
          (j.castLE (by omega)) (i.castLE (by omega)) (l.castLE (by omega))| ≤
        (A0*(n : ℝ)^loss)*w j*(Nat.dist i.val l.val : ℝ)*(min (depth i : ℝ) (depth l : ℝ))^(-1-s.val/2)*
          ‖φ.val‖*‖ζ.val‖ + (E0*Real.exp (-c*(n : ℝ)^δ))*ess φ*ess ζ) :
    let K := 2*8^(2-s.val)*(2/(1-s.val/2)) +
      8^(1+s.val/2)*(2/s.val) + 4^(s.val/2)
    let L0 := (K*Real.sqrt (2/(1-s.val)))*A0*D0
    let K0 := βhi*(C*(1+1/s.val)*(2/(1-s.val))) + A0*(2/(1-s.val/2))^2
    ‖WithLp.toLp 2 (fun i => (ψ i).val-(v i).val)‖^2 ≤
      (3*((2*L0/a0)^2+(1+K0)*D0^2/a0+D0^2))*(n : ℝ)^(8*loss-1)*‖χ‖^2 +
      (9*(3*E0*(2*V0+a0⁻¹)*V0+E0*V0^2)/a0)*
        (n : ℝ)^(2+4*loss)*Real.exp (-c*(n : ℝ)^δ)*B^2 := by
  intro K L0 K0
  have hn : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have ha : 0 < a0*(n : ℝ)^(-loss) := by positivity
  have hC0 : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1).trans hC
  have hβ0 : 0 ≤ βhi := β.property.le.trans hβhi
  have hK : 0 ≤ K := by
    have hs := s.property.1
    have hs1 : 0 < 1-s.val/2 := by linarith [s.property.2]
    dsimp only [K]; positivity
  have hL0 : 0 ≤ L0 := by dsimp only [L0]; positivity
  have hK0 : 0 ≤ K0 := by
    have hs := s.property.1
    have hs1 : 0 < 1-s.val := sub_pos.mpr s.property.2
    dsimp only [K0]; positivity
  let S : Q.1 := ∑ i, v i
  let V := V0*(n : ℝ)^loss*B
  let D := D0*(n : ℝ)^loss
  let A := A0*(n : ℝ)^loss
  let Err := E0*Real.exp (-c*(n : ℝ)^δ)
  let a := a0*(n : ℝ)^(-loss)
  let L := (K*Real.sqrt (2/(1-s.val)))*A*D*‖χ‖*(n : ℝ)^(-(1 : ℝ)/2)
  let τ := 3*(n : ℝ)^2*(Err*(2*V+a⁻¹*B)*V)
  let R := (n : ℝ)⁻¹*Q.2 S S +
    ((β.val*(C*(1+1/s.val)*(2/(1-s.val))))*(n : ℝ)^(κ*η)*(n : ℝ)^(2-s.val) +
      A*(∑ j, w j)^2)*‖((n : ℝ)⁻¹ • S).val‖^2 + (n : ℝ)^2*Err*V^2
  have hcomp := long_comparison_from_native_bounds_internal β s n d e hde m hm hnm
    k hk hkm θ ε η t ν Q hQ P C κ γ hC hM hPm hH hHi hYi a ha hlower
    i₀ hi₀ χ B V D A Err hB (by dsimp [V]; positivity)
    (by dsimp [D]; positivity) (by dsimp [A]; positivity) (by dsimp [Err]; positivity)
    hχ ψ v hψ hv hvalue hsum haux hpoint hinc
  change ‖WithLp.toLp 2 (fun i => (ψ i).val-(v i).val)‖ ≤
    2*L/a+Real.sqrt ((2*τ+R)/a)+(n : ℝ)^(-(1 : ℝ)/2)*‖S.val‖ at hcomp
  have hm : ‖S.val‖ ≤ D0*(n : ℝ)^(loss-(1-s.val))*‖χ‖ := by
    apply hsum.trans_eq
    rw [show loss-(1-s.val) = loss+(-(1-s.val)) by ring, Real.rpow_add hn]
    ring
  have hLb : L ≤ L0*(n : ℝ)^(2*loss-1/2)*‖χ‖ := by
    apply le_of_eq
    dsimp only [L,L0,A,D]
    rw [show 2*loss-1/2 = (loss+loss)+(-(1 : ℝ)/2) by ring,
      Real.rpow_add hn,Real.rpow_add hn]
    ring
  have hinv : a⁻¹ = a0⁻¹*(n : ℝ)^loss := by
    dsimp only [a]
    rw [mul_inv, ←Real.rpow_neg hn.le, neg_neg]
  have hτb : τ ≤ 3*(n : ℝ)^2*(E0*Real.exp (-c*(n : ℝ)^δ)*
      ((2*V0+a0⁻¹)*(n : ℝ)^loss*B)*(V0*(n : ℝ)^loss*B)) := by
    apply le_of_eq
    dsimp only [τ,Err,V]
    rw [hinv]
    ring
  have hRshape := long_normal_energy_shape_internal Q s n S R
    ((β.val*(C*(1+1/s.val)*(2/(1-s.val))))*(n : ℝ)^(κ*η)) A Err V
    (by dsimp [A]; positivity) le_rfl
  have hcoeff : (β.val*(C*(1+1/s.val)*(2/(1-s.val))))*(n : ℝ)^(κ*η) +
      A*(2/(1-s.val/2))^2 ≤ K0*(n : ℝ)^loss := by
    have hs : 0 < 1-s.val := sub_pos.mpr s.property.2
    have hsp := s.property.1
    dsimp only [A,K0]
    calc
      _ ≤ (βhi*(C*(1+1/s.val)*(2/(1-s.val))))*(n : ℝ)^loss +
          (A0*(n : ℝ)^loss)*(2/(1-s.val/2))^2 := by gcongr
      _ = _ := by ring
  have hRb : R ≤ (n : ℝ)⁻¹*Q.2 S S +
      K0*(n : ℝ)^loss*(n : ℝ)^(-s.val)*‖S.val‖^2 +
        (n : ℝ)^2*(E0*Real.exp (-c*(n : ℝ)^δ))*(V0*(n : ℝ)^loss*B)^2 := by
    apply hRshape.trans
    exact add_le_add (add_le_add le_rfl (by gcongr)) le_rfl
  have hR : 0 ≤ R := by
    dsimp only [R]
    have hq := hQ.2.2.1 S
    have hβpos := β.property
    have hs := s.property.1
    have hs1 : 0 < 1-s.val := sub_pos.mpr s.property.2
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hErr : 0 ≤ Err := by dsimp [Err]; positivity
    positivity
  exact long_comparison_square_uniform_internal s loss a0 L0 K0 D0 V0 E0 c δ
    hloss ha0 hL0 hK0 hD0 hV0 hE0 _ ν Q hQ n S ‖χ‖ B
    ‖WithLp.toLp 2 (fun i => (ψ i).val-(v i).val)‖ L τ R
    (norm_nonneg _) hB (norm_nonneg _) (by dsimp [L]; positivity)
    (by dsimp [τ,Err,V]; positivity) hR hm hgrad hLb hτb hRb hcomp

end NativeComparison

/-- See Lemma 6.4 of the paper: choose
the coefficient family before the sizes and exteriors, on the original
normalized Hausdorff law. Both physical coefficient domains and the two native
row estimates hold on its actual intrinsic scalar form, above the size threshold.
The reference cutoff has the least degree of Lemma 5.4 of the paper,
as used in the proof of Lemma 6.4. -/
def LongRangeNativePhysicalInputs (s : Riesz1.RieszExponent) : Prop :=
    let h := (paperReferenceCutoffExponent s : ℕ)
    ∃ A K ε₀ κ γ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧ 0 < κ ∧ 0 < γ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∃ (n₀ : ℕ) (δ : ℝ), 2 ≤ n₀ ∧ 0 < δ ∧
      (128 : ℝ) ≤ (n₀ : ℝ)^(1-s.val/2-2*ε) ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    ∀ (a d e : ℕ) (_ha : 1 ≤ a) (hde : d ≤ e),
    let n := a.succPNat
    let N := ((n : ℕ)+d).succPNat
    ∀ _hN : 4*(n : ℕ) ≤ (N : ℕ), (n : ℝ)^(2/s.val) ≤ (N : ℝ) →
    ∀ (y : AffineSimplex.chartDomain (d+1) ((d+1+a : ℕ)+1))
      (z : AffineSimplex.chartDomain (e+1) ((e+1+a : ℕ)+1)) (L : ℝ),
    ((d+1+a : ℕ)+1 : ℝ)-∑ k, y.val k = L →
    ((e+1+a : ℕ)+1 : ℝ)-∑ k, z.val k = L →
    InterpolantLocalLaws.admissibleExterior (ofLong β s) (d+1) a (Nat.succ_le_succ (Nat.zero_le d)) θ ε A K y →
    InterpolantLocalLaws.admissibleExterior (ofLong β s) (e+1) a (Nat.succ_le_succ (Nat.zero_le e)) θ ε A K z →
    let Dy := RetainedSimplex.assemble (d+1) a (InterpolatingDensities.exteriorPermutation (d+1) a) y.val ⁻¹'
      gapAmbientDomain (d+1+a).succPNat
    let Dz := RetainedSimplex.assemble (e+1) a (InterpolatingDensities.exteriorPermutation (e+1) a) z.val ⁻¹'
      gapAmbientDomain (e+1+a).succPNat
    ∃ Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ,
      ContDiffOn ℝ ∞ Ky Dy ∧ ContDiffOn ℝ ∞ Kz Dz ∧
      (∀ u (hu : u ∈ Dy), Ky u = physicalAmbientGapEnergy (ofLong β s) (d+1+a).succPNat
        ⟨RetainedSimplex.assemble (d+1) a (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u,hu⟩) ∧
      (∀ u (hu : u ∈ Dz), Kz u = physicalAmbientGapEnergy (ofLong β s) (e+1+a).succPNat
        ⟨RetainedSimplex.assemble (e+1) a (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u,hu⟩) ∧
    ∀ t ∈ Icc (0 : ℝ) 1,
    let H := fun u : EuclideanSpace ℝ (Fin (a+1)) =>
      (∑ k, (θ.val ((a+1 : ℝ)^(-ε)*u k)+θ.val ((a+1 : ℝ)^(-ε)*(u k)⁻¹)))+(1-t)*Ky u+t*Kz u
    let m := PhysicalCore.properReferencePeriod s n N
    let k := ⌊(n : ℝ)^(K*ε)⌋₊^h
    ∃ (hm : 2 ≤ (m : ℕ)) (hnm : (n : ℕ) ≤ (m : ℕ))
      (hk : 1 ≤ k) (hkm : k ≤ (m : ℕ)/4),
      (∀ μ : Measure (AffineSimplex.chartDomain n ((n+d : ℕ)+1)),
        PeriodizedMatrixBounds (ν := μ) s n m hm k C κ γ ε
          (InterpolationMatrix.matrix β s n d e hde m hm hnm k θ ε (K*ε) t)) ∧
      (∀ x ∈ AffineSimplex.massSimplex a L, ∀ v : EuclideanSpace ℝ (Fin (a+1)),
        C⁻¹*(n : ℝ)^(-κ*ε)*(∑ i, (v i)^2) ≤ ∑ i,∑ j, v i*hessianMatrix H x i j*v j) ∧
    (n₀ ≤ (n : ℕ) →
      (∀ x ∈ AffineSimplex.massSimplex a L, ∀ i j : Fin (a+1),
        |(1-t)*hessianMatrix Ky x i j+t*hessianMatrix Kz x i j|^2+
          |InterpolationMatrix.penaltyHessian n θ ε x i j|^2 ≤
          C*(n : ℝ)^C*InterpolantLocalLaws.exceptionalWeight (n := n) s.val (WithLp.ofLp x)) ∧
      let μ : Measure (AffineSimplex.massSimplex a L) := (AffineSimplex.simplexVolume a L).comap Subtype.val
      let w := fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal (Real.exp (-β.val*H u.val))
      ∃ (h0 : (∫⁻ u, w u ∂μ) ≠ 0) (htop : (∫⁻ u, w u ∂μ) ≠ ⊤),
      ∃ hLN : L < ((n+d : ℕ)+1 : ℝ),
      let ρ := AffineFibre.normalizedMeasure μ w h0 htop
      let ν := ρ.map (InterpolationTransport.inclusion a L ((n+d : ℕ)+1) hLN)
      IsProbabilityMeasure ν ∧
      ∀ frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a),
      ∃ Q : ScalarFormData ν, ∃ hQ : IsClosedScalarDirichletForm Q,
      IsConservativeScalarForm Q ∧
      InterpolationCoefficientBounds.IsIntrinsicFibreForm a L ((n+d : ℕ)+1) hLN frame ν Q ∧
      let P : AffineSimplex.chartDomain n ((n+d : ℕ)+1) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ :=
        fun q i j => (1-t)*hessianMatrix Ky q.val i j+t*hessianMatrix Kz q.val i j
      let Y := InterpolationMatrix.multiplicationPart β s n d e hde m hm hnm k θ ε (K*ε) t P
      (∀ i j : Fin (n : ℕ), Integrable
        (fun x : AffineSimplex.chartDomain n ((n+d : ℕ)+1) =>
          β.val*(InterpolationMatrix.penaltyHessian n θ ε x.val i j+P x i j)) ν) ∧
      (∀ i j : Fin (n : ℕ), Integrable (fun x => Y x i j) ν) ∧
      (∀ (φ ψ : BoundedL2Pairings.boundedSubmodule ν) (j i : Fin (n : ℕ)),
        |(∫ x, φ.val x*Y x j i*ψ.val x ∂ν)+
          InterpolationMatrix.schurPointPair ν Q hQ s β m hm k hk hkm n φ.val ψ.val
            (j.castLE hnm) (i.castLE hnm)| ≤
          (C*(n : ℝ)^(κ*ε))*InteractionDifferential.boundaryWeight s.val n j*InteractionDifferential.boundaryWeight s.val n i*‖φ.val‖*‖ψ.val‖+
            (C*Real.exp (-c*(n : ℝ)^δ))*
              (eLpNorm (fun x => φ.val x) ∞ ν).toReal*(eLpNorm (fun x => ψ.val x) ∞ ν).toReal) ∧
      (∀ (φ ψ : BoundedL2Pairings.boundedSubmodule ν) (j i l : Fin (n : ℕ)),
        |(∫ x, φ.val x*ψ.val x*(Y x j i-Y x j l) ∂ν)+
          InterpolationMatrix.schurIncrementPair ν Q hQ s β m hm k hk hkm n φ.val ψ.val
            (j.castLE hnm) (i.castLE hnm) (l.castLE hnm)| ≤
          (C*(n : ℝ)^(κ*ε))*InteractionDifferential.boundaryWeight s.val n j*
            (Nat.dist i.val l.val : ℝ)*
              (min ((min (i.val+1) ((n : ℕ)-i.val) : ℕ) : ℝ)
                ((min (l.val+1) ((n : ℕ)-l.val) : ℕ) : ℝ))^(-1-s.val/2)*‖φ.val‖*‖ψ.val‖+
            (C*Real.exp (-c*(n : ℝ)^δ))*
              (eLpNorm (fun x => φ.val x) ∞ ν).toReal*(eLpNorm (fun x => ψ.val x) ∞ ν).toReal))

/-- See Lemma 6.4 of the paper: the uniform physical coefficient and native-row
family with entrywise integrability, assuming the periodic-zeta connection
formula and locally uniform rigidity from the companion paper. -/
theorem long_range_native_physical_inputs (hzeta : External.PeriodicZeta)
    (hRig : External.LongRangeRigidityLocallyUniform) (s : Riesz1.RieszExponent) :
    LongRangeNativePhysicalInputs s := by
  unfold LongRangeNativePhysicalInputs
  intro h
  obtain ⟨A,K,ε₀,κ,γ,hA,hK,hε₀,hκ,hγ,hbounds⟩ :=
    InterpolationCoefficientBounds.long_range_bounds hzeta hRig s
  refine ⟨A,K,ε₀,κ,γ,hA,hK,hε₀,hκ,hγ,?_⟩
  intro ε hε hsmall
  obtain ⟨n₀,δ,hn₀,hδ,hthreshold,hboundsNext⟩ := hbounds ε hε hsmall
  clear hbounds
  rename' hboundsNext => hbounds
  refine ⟨n₀,δ,hn₀,hδ,hthreshold,?_⟩
  intro βlo βhi hlo hle θ
  obtain ⟨C,c,hC,hc,hboundsNext⟩ := hbounds βlo βhi hlo hle θ
  clear hbounds
  rename' hboundsNext => hbounds
  refine ⟨C,c,hC,hc,?_⟩
  intro β hβ a d e ha hde n N hN hNpower y z L hyL hzL hy hz Dy Dz
  obtain ⟨Ky,Kz,hKy,hKz,hky,hkz,hboundsNext⟩ :=
    hbounds β hβ a d e ha hde hN hNpower y z L hyL hzL hy hz
  clear hbounds
  rename' hboundsNext => hbounds
  refine ⟨Ky,Kz,hKy,hKz,hky,hkz,?_⟩
  intro t ht H m k
  obtain ⟨hm,hnm,hk,hkm,hmat,hcoerc,hlarge⟩ := hbounds t ht
  refine ⟨hm,hnm,hk,hkm,hmat,hcoerc,?_⟩
  intro hnlarge
  obtain ⟨hsquare,hlarge⟩ := hlarge hnlarge
  refine ⟨hsquare,?_⟩
  intro μ w
  obtain ⟨h0,htop,hLN,hprob,hforms⟩ := hlarge
  refine ⟨h0,htop,hLN,hprob,?_⟩
  intro frame
  obtain ⟨Q,hQ,hcons,hIntrinsic,hperts⟩ := hforms frame
  refine ⟨Q,hQ,hcons,hIntrinsic,?_⟩
  intro P Y
  let ν := (AffineFibre.normalizedMeasure μ w h0 htop).map
    (InterpolationTransport.inclusion a L ((n+d : ℕ)+1) hLN)
  let : IsProbabilityMeasure ν := hprob
  have htests (φ ψ : BoundedL2Pairings.boundedSubmodule ν) (i j l : Fin (n : ℕ)) :=
    hperts φ.val ψ.val (BoundedL2Pairings.memLp_top φ) (BoundedL2Pairings.memLp_top ψ) i j l
  have hHiYi := physical_entries_of_native_tests_internal β s n d e hde m hm hnm
    k θ ε (K*ε) t ν P C κ γ ε (hmat ν)
      (fun φ ψ hφ hψ i j => (hperts φ ψ hφ hψ i j i).choose)
  have hperm (a wi wj f g e p q : ℝ) :
      a*wi*wj*f*g+e*(p*q) = a*wj*wi*f*g+e*p*q := by ring
  have hiperm (a dist w r f g e p q : ℝ) :
      a*(dist*w*r)*f*g+e*(p*q) = a*w*dist*r*f*g+e*p*q := by ring
  have hrows := native_row_bounds_internal β s n d e hde m hm hnm
    k hk hkm θ ε (K*ε) t ν Q hQ P (C*(n : ℝ)^(κ*ε)) (C*Real.exp (-c*(n : ℝ)^δ))
      (by
        intro φ ψ i j l
        obtain ⟨hp,hd,hpbound,hdbound⟩ := htests φ ψ i j l
        refine ⟨hp,hd,hpbound.trans_eq ?_,hdbound.trans_eq ?_⟩
        · simp only [InteractionDifferential.boundaryWeight_long s.property.2]
          apply hperm
        · simp only [InteractionDifferential.boundaryWeight_long s.property.2,Nat.cast_min]
          apply hiperm)
  refine ⟨?_,hHiYi.2,?_,?_⟩
  · intro i j
    simpa only [Matrix.smul_apply,Matrix.add_apply,smul_eq_mul] using hHiYi.1 i j
  · exact hrows.1
  · exact hrows.2

/-- See Lemma 6.4 of the paper: the actual included physical matrix has
its literal ambient Hessian, symmetry, positivity and the direct all-size
curvature bound, independently of any upper coefficient estimate. -/
theorem included_physical_curvature_internal (p : Parameters) (θ : PhysicalCutoff)
    (ε : ℝ) (hε : 0 ≤ ε) (d e a : ℕ) (ha : 1 ≤ a)
    (y : AffineSimplex.chartDomain d ((d+a : ℕ)+1))
    (z : AffineSimplex.chartDomain e ((e+a : ℕ)+1)) (L : ℝ)
    (hyL : ((d+a : ℕ)+1 : ℝ)-∑ k, y.val k = L)
    (hzL : ((e+a : ℕ)+1 : ℝ)-∑ k, z.val k = L) :
    let Y := RetainedSimplex.assemble d a (InterpolatingDensities.exteriorPermutation d a) y.val
    let Z := RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) z.val
    let Dy := Y ⁻¹' gapAmbientDomain (d+a).succPNat
    let Dz := Z ⁻¹' gapAmbientDomain (e+a).succPNat
    ∀ Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ,
    ContDiffOn ℝ ∞ Ky Dy → ContDiffOn ℝ ∞ Kz Dz →
    (∀ x (hx : x ∈ Dy), Ky x = physicalAmbientGapEnergy p (d+a).succPNat ⟨Y x,hx⟩) →
    (∀ x (hx : x ∈ Dz), Kz x = physicalAmbientGapEnergy p (e+a).succPNat ⟨Z x,hx⟩) →
    ∀ (N : ℝ) (hLN : L < N) (ρ : Measure (AffineSimplex.massSimplex a L)),
    let ν := ρ.map (InterpolationTransport.inclusion a L N hLN)
    ∀ t ∈ Icc (0 : ℝ) 1,
    let Ht := fun u : EuclideanSpace ℝ (Fin (a+1)) =>
      (∑ k, (θ.val ((a+1 : ℝ)^(-ε)*u k) + θ.val ((a+1 : ℝ)^(-ε)*(u k)⁻¹))) +
        (1-t)*Ky u+t*Kz u
    let H : AffineSimplex.chartDomain (a+1) N → Matrix (Fin (a+1)) (Fin (a+1)) ℝ :=
      fun x i j => p.val.1 *
        (InterpolationMatrix.penaltyHessian (⟨a+1,by omega⟩ : ℕ+) θ ε x.val i j+
          ((1-t)*hessianMatrix Ky x.val i j+t*hessianMatrix Kz x.val i j))
    ∀ᵐ x ∂ν, hessianMatrix (fun u => p.val.1*Ht u) x.val = H x ∧
      (H x).PosSemidef ∧ ∀ v : Fin (a+1) → ℝ,
        (p.val.1*min 1 (p.val.2*(p.val.2+1))*(a+1 : ℝ)^(-(p.val.2+2)*ε)) * (∑ i, v i^2) ≤
          ∑ i, ∑ j, v i*H x i j*v j := by
  intro Y Z Dy Dz Ky Kz hKy hKz hky hkz N hLN ρ ν t ht Ht H
  have hDy : IsOpen Dy := (PhysicalEnergy.isOpen_gapAmbientDomain _).preimage
    (RetainedSimplex.continuous_assemble d a _ y.val)
  have hDz : IsOpen Dz := (PhysicalEnergy.isOpen_gapAmbientDomain _).preimage
    (RetainedSimplex.continuous_assemble e a _ z.val)
  have hsupp : ∀ᵐ x ∂ν, x.val ∈ AffineSimplex.massSimplex a L := by
    rw [(InterpolationTransport.measurableEmbedding_inclusion a L N hLN).ae_map_iff]
    exact ae_of_all _ (fun x => x.property)
  filter_upwards [hsupp] with x hx
  obtain ⟨heq,hl⟩ := physical_hessian_and_curvature_internal p θ ε hε d e a ha
    y z L hyL hzL Ky Kz hKy hKz hky hkz t ht x.val hx
  have heq' : hessianMatrix (fun u => p.val.1*Ht u) x.val = H x := by
    exact heq
  have hl' : ∀ v : Fin (a+1) → ℝ,
      (p.val.1*min 1 (p.val.2*(p.val.2+1))*(a+1 : ℝ)^(-(p.val.2+2)*ε)) * (∑ i, v i^2) ≤
        ∑ i, ∑ j, v i*H x i j*v j := by
    exact hl
  have hxsY : x.val ∈ Dy := InterpolationCoefficientBounds.fibre_mem_internal d a y L hyL hx
  have hxsZ : x.val ∈ Dz := InterpolationCoefficientBounds.fibre_mem_internal e a z L hzL hx
  have hs : ContDiffAt ℝ ∞ (fun u => p.val.1*Ht u) x.val :=
    contDiffAt_const.mul (((InterpolationCoercivity.forcing_smooth θ
      (Real.rpow_pos_of_pos (by positivity) _) hx.1).add
      (contDiffAt_const.mul (hKy.contDiffAt (hDy.mem_nhds hxsY)))).add
      (contDiffAt_const.mul (hKz.contDiffAt (hDz.mem_nhds hxsZ))))
  have hc : 0 < p.val.1*min 1 (p.val.2*(p.val.2+1))*(a+1 : ℝ)^(-(p.val.2+2)*ε) := by
    have hp := p.property.1
    have hs := p.property.2.1
    positivity
  refine ⟨heq',Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_,?_⟩,hl'⟩
  · rw [←heq']
    ext i j
    simp only [Matrix.conjTranspose_apply,star_trivial,Intrinsic.hessianMatrix_eq_second hs]
    exact hs.isSymmSndFDerivAt (by simp) _ _
  · intro v
    have hh := (show 0 ≤ _*(∑ i, v i^2) from mul_nonneg hc.le (Finset.sum_nonneg fun i _ => sq_nonneg _)).trans (hl' v)
    simpa only [dotProduct,Matrix.mulVec,star_trivial,Finset.mul_sum,mul_assoc] using hh

end Riesz2.FixedLengthDecay
