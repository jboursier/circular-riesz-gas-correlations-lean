/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.GlobalYoungClosure

/-!
# Constrained global decay

The direct L²-source weighted tests and scalar closure in Lemma 5.13,
using the scalar forms and periodized matrices of Subsection 5.4.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter
open scoped BigOperators Matrix

namespace Riesz2.DerivativeControl

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- L²-source version of the weighted derivative test for Lemma 5.11,
used to extend Lemma 5.13 without differentiating the source. -/
theorem diff_with_multiplier_L2 (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (γ : ℝ) (hγ : 1 / 2 ≤ γ) (κstar γstar : ℝ) (hκstar : 0 < κstar) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (Cstar : ℝ), 1 ≤ Cstar →
    ∀ (βlo : ℝ), 0 < βlo → ∀ (βhi : ℝ), βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ), 0 < ε →
    ∀ {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
      (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q →
    ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ)) (K : ℕ)
      (M : X → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ),
    PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M →
    ∀ (β : ℝ), βlo ≤ β → β ≤ βhi →
    ∀ (χ : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1)
      (lam : Lp ℝ 2 ν),
    WeightedWeakSolution Q (fun x => β • M x) ⊤
      (fun i => (if i = i₀ then χ else 0) + lam) u →
    (∀ᵐ x ∂ν, ∑ i, (u i).val x = 0) →
    let t := γ / 2 + 1 / 4
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    let p := (1 - s.val / 2)⁻¹
    let V := fun x => (∑ i, |(rieszMatrix sh m hm *ᵥ
      (fun j => (u j).val x)) i| ^ p) ^ (1 / p)
    let Xρ := fun (ρ : ℝ) => Real.sqrt (∑ i, (weightRadius m i i₀ ^ ρ * ‖(u i).val‖) ^ 2)
    Integrable (fun x => V x ^ 2) ν ∧
    ∀ (η : ℝ), 0 < η → η < 1 / 4 →
      (∑ i, weightRadius m i i₀ ^ (2 * t) * Q.2 (u i) (u i)) ≤
        C * (n : ℝ) ^ (κ * ε) * (‖χ‖ ^ 2 + Xρ γ *
          (η ^ (3 - s.val) * Xρ (3 / 2 - s.val) +
            η⁻¹ * Real.sqrt (Real.log (2 * (m : ℝ))) *
              Real.sqrt (∫ x, V x ^ 2 ∂ν) + (m : ℝ) * ‖lam‖)) := by
  obtain ⟨B, D, hB, hD, hmatrix⟩ := matrix_lower_integral_internal hz s γ hγ
  refine ⟨κstar, hκstar, fun Cstar hCstar βlo hβlo βhi hβhi => ?_⟩
  let C := βlo⁻¹ * Cstar + βhi * (B + D) * Cstar + 1
  have hCstar0 : 0 < Cstar := lt_of_lt_of_le zero_lt_one hCstar
  have hβhi0 : 0 < βhi := hβlo.trans_le hβhi
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro ε hε X _ ν _ Q hQ n m hm K M hM β hβloβ hββhi χ i₀ u lam hu hzero
    t sh p V Xρ
  let v := fun i => (u i).val
  let f := fun i => if i = i₀ then χ else 0
  let A := Cstar * (n : ℝ) ^ (κstar * ε)
  let a := Cstar⁻¹ * (n : ℝ) ^ (-κstar * ε)
  have hβ : 0 < β := hβlo.trans_le hβloβ
  have ha : 0 < a := SchurRestriction.periodized_mass_pos hCstar
  have hn : 1 ≤ (n : ℝ) := by exact_mod_cast n.pos
  have hP : 1 ≤ (n : ℝ) ^ (κstar * ε) :=
    Real.one_le_rpow hn (mul_nonneg hκstar.le hε.le)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hsym : ∀ᵐ x ∂ν, ∀ i j, M x i j = M x j i := hM.2.1.mono (fun _ hx => hx.1)
  have hMb := SchurRestriction.periodized_scaled_bounded β hM
  have hMm := SchurRestriction.periodized_scaled_measurable β hM
  have huC := constrained_of_multiplier Q _ f lam u hzero hu
  have hlower : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
      ∀ z : Fin (m : ℕ) → ℝ, a * (∑ i, z i ^ 2) ≤
        ∑ i, ∑ j, z i * M x i j * z j :=
    hM.2.1.mono (fun _ hx => ⟨hx.1, hx.2.2.1⟩)
  have henergy := (AbstractEquation.existence_energy Q hQ β hβ M hM.1 a ha hlower
    (zeroSumComponents (Fin (m : ℕ))) f).2 u huC
  have hf : ‖(WithLp.toLp 2 f : PiLp 2 (fun _ : Fin (m : ℕ) => Lp ℝ 2 ν))‖ = ‖χ‖ := by
    have hs : (WithLp.toLp 2 f : PiLp 2 (fun _ : Fin (m : ℕ) => Lp ℝ 2 ν)) =
        PiLp.single 2 i₀ χ := by
      ext i
      simp [f, PiLp.single_apply, eq_comm]
    rw [hs, PiLp.norm_single]
  rw [hf] at henergy
  have hcomponent : ‖(u i₀).val‖ ≤ (β * a)⁻¹ * ‖χ‖ :=
    (PiLp.norm_apply_le (WithLp.toLp 2 v) i₀).trans henergy.1
  have hsource : inner ℝ χ (u i₀).val ≤ (β * a)⁻¹ * ‖χ‖ ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hcomponent (norm_nonneg χ)
    nlinarith [real_inner_le_norm χ (u i₀).val]
  have hp : 1 ≤ p := by
    dsimp [p]
    exact (one_le_inv₀ (by linarith [s.property.2])).mpr (by linarith [s.property.1])
  have hV : MemLp V 2 ν := matrix_lp_memLp p hp _ v
  refine ⟨hV.integrable_sq, fun η hη hη' => ?_⟩
  let w := fun i => weightRadius m i i₀ ^ (2 * t)
  let E := fun x => ∑ i, w i * v i x * (M x *ᵥ (fun j => v j x)) i
  have htest := weighted_test_domain Q _ hMm hMb w u
  have heq := hu.2 (fun i => w i • u i) htest
  have hpair := weighted_pair Q M hsym w u
  have hE : Integrable E ν := by
    exact (BoundedMatrixForms.integrable_pair M hM.1
      (SchurRestriction.periodized_bounded hM) v (fun i => (w i • u i).val)).congr hpair
  have hscale : (∫ x, matrixFieldPair (fun x => β • M x) v
      (fun i => (w i • u i).val) x ∂ν) = β * ∫ x, E x ∂ν := by
    rw [SchurRestriction.integral_pair_smul, integral_congr_ae hpair]
  rw [weighted_form, hscale] at heq
  have hsourcepair : (∑ i, inner ℝ (f i + lam) (w i • u i).val) =
      inner ℝ χ (u i₀).val + inner ℝ lam (∑ i, w i • v i) := by
    simp only [inner_add_left, Finset.sum_add_distrib, Submodule.coe_smul,
      ← inner_sum]
    congr 1
    rw [Finset.sum_eq_single i₀]
    · simp [f, w, weightRadius, Riesz1.cyclicIndexDistance]
    · intro i _ hi
      simp [f, hi]
    · simp
  rw [hsourcepair] at heq
  have hlambda : inner ℝ lam (∑ i, w i • v i) ≤
      (m : ℝ) * ‖lam‖ * Xρ γ := by
    have hn := multiplier_norm m hm i₀ γ v
    have h := mul_le_mul_of_nonneg_left hn (norm_nonneg lam)
    have hb := real_inner_le_norm lam (∑ i, w i • v i)
    change inner ℝ lam (∑ i, w i • v i) ≤ _
    dsimp only [w, t] at hb
    nlinarith
  obtain ⟨α, _, hα⟩ := DerivativeCommutators.periodized_interval_entries s n m hm K
    Cstar κstar γstar ε M hM
  have hcoeff : ∀ᵐ x ∂ν, (∀ k r, 0 ≤ α k r x ∧ α k r x ≤
      A * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2)) ∧
      ∀ a b, M x a b = ∑ k, ∑ r, α k r x *
        (if a ∈ cyclicIndexInterval m k (r.val + 1) then 1 else 0) *
        (if b ∈ cyclicIndexInterval m k (r.val + 1) then 1 else 0) :=
    hα.mono (fun _ hx => ⟨fun k r => ⟨(hx.1 k r).1, (hx.1 k r).2.1⟩, hx.2⟩)
  have hmatrix' := hmatrix ν m hm i₀ η A hη hη' hA α M hcoeff v hE
  have hraw : (∑ i, w i * Q.2 (u i) (u i)) ≤
      (β * a)⁻¹ * ‖χ‖ ^ 2 + (m : ℝ) * ‖lam‖ * Xρ γ +
      β * (B * A * η ^ (3 - s.val) * Xρ γ * Xρ (3 / 2 - s.val) +
        D * A * η⁻¹ * Real.sqrt (Real.log (2 * (m : ℝ))) * Xρ γ *
          Real.sqrt (∫ x, V x ^ 2 ∂ν)) := by
    have h := mul_le_mul_of_nonneg_left hmatrix' hβ.le
    linarith
  have hinv : (β * a)⁻¹ ≤ βlo⁻¹ * Cstar * (n : ℝ) ^ (κstar * ε) := by
    have hn0 : 0 < (n : ℝ) := by positivity
    have he : (β * a)⁻¹ = β⁻¹ * Cstar * (n : ℝ) ^ (κstar * ε) := by
      dsimp [a]
      rw [mul_inv_rev, mul_inv_rev, inv_inv, ← Real.rpow_neg hn0.le]
      rw [neg_mul, neg_neg]
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (inv_anti₀ hβlo hβloβ) hCstar0.le) (by positivity)
  apply absorb_internal hB hD hCstar hβlo hβhi hβloβ hββhi hP hinv
    (Real.sqrt_nonneg _) (by positivity) (by positivity) (by positivity)
  convert hraw using 1
  dsimp only [A]
  ring


end Riesz2.DerivativeControl

namespace Riesz2.GlobalDecay

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

/-- See the proof of Lemma 5.13 in the paper, the second weighted inequality for every
L² source. The weighted test uses only its L² pairing. -/
theorem global_energy_second_L2 (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ)
    (hκstar : 0 < κstar) (hγstar : 0 ≤ γstar) (M₀ : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε →
    ∀ Cstar : ℝ, 1 ≤ Cstar →
    ∀ βlo : ℝ, 0 < βlo → ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
      (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q →
    ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ)),
    2 ≤ (n : ℕ) → (n : ℕ) ≤ (m : ℕ) →
    (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
    let K := ⌊(n : ℝ) ^ ε⌋₊ ^ M₀
    1 ≤ K → 4 * K ≤ (m : ℕ) →
    ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M →
    ∀ β : ℝ, βlo ≤ β → β ≤ βhi →
    ∀ (χ : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _)
      (fun i => if i = i₀ then χ else 0) u →
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    let p := (1 - s.val / 2)⁻¹
    let V := fun x => (∑ i, |(rieszMatrix sh m hm *ᵥ
      (fun j => (u j).val x)) i| ^ p) ^ (1 / p)
    let Xρ := fun (ρ : ℝ) => Real.sqrt (∑ i, (weightRadius m i i₀ ^ ρ * ‖(u i).val‖) ^ 2)
    ∃ lam : Lp ℝ 2 ν,
      (∀ᵐ x ∂ν, lam x = gapMultiplierField m Q (fun x => β • M x)
        (fun i => if i = i₀ then χ else 0) u x) ∧
      WeightedWeakSolution Q (fun x => β • M x) ⊤
        (fun i => (if i = i₀ then χ else 0) + lam) u ∧
      Integrable (fun x => V x ^ 2) ν ∧
      ∀ η : ℝ, 0 < η → η < 1 / 4 →
        (∑ i, weightRadius m i i₀ ^ (2 * (1 - s.val / 2)) * Q.2 (u i) (u i)) ≤
          C * (n : ℝ) ^ (κ * ε) *
            (‖χ‖ ^ 2 + Xρ (3 / 2 - s.val) *
              (η ^ (3 - s.val) * Xρ (3 / 2 - s.val) +
                η⁻¹ * Real.sqrt (∫ x, V x ^ 2 ∂ν) + ‖χ‖ + Xρ (1 / 2))) := by
  obtain ⟨κm, hκm, hmult⟩ := global_energy_multiplier s κstar γstar hκstar.le hγstar M₀
  have hα : (1 / 2 : ℝ) ≤ 3 / 2 - s.val := by linarith [s.property.2]
  obtain ⟨κd, hκd, hdiff⟩ :=
    DerivativeControl.diff_with_multiplier_L2 hzeta s (3 / 2 - s.val) hα κstar γstar hκstar
  refine ⟨κd + κm + 1, by positivity, fun ε hε Cstar hCstar βlo hβlo βhi hβhi => ?_⟩
  obtain ⟨Cm, hCm, hmult⟩ := hmult ε hε Cstar hCstar βhi (hβlo.le.trans hβhi)
  obtain ⟨Cd, hCd, hdiff⟩ := hdiff Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨D, hD, hlog⟩ := EllipticRegularity.log_absorption s hε (by norm_num : (0 : ℝ) < 1 / 2)
  let C₀ := (1 + Cm) * (1 + D)
  refine ⟨Cd * C₀, by dsimp [C₀]; positivity, ?_⟩
  intro Ω _ ν _ Q hQ n m hm hn hnm hmn K hK hKm M hM β hβloβ hββhi χ i₀ u hu
    sh p V Xρ
  obtain ⟨lam, hlam, hfull, _, hmlam⟩ :=
    hmult ν Q n m hm hn hnm hmn hK hKm M hM β (hβlo.le.trans hβloβ) hββhi χ i₀ u hu
  obtain ⟨hVi, hdiff⟩ := hdiff ε hε ν Q hQ n m hm K M hM β hβloβ hββhi
    χ i₀ u lam hfull hu.1.1
  have ht : (3 / 2 - s.val) / 2 + 1 / 4 = 1 - s.val / 2 := by ring
  refine ⟨lam, hlam, hfull, hVi, ?_⟩
  intro η hη hη'
  have he := hdiff η hη hη'
  simp only [ht] at he
  let T := (n : ℝ) ^ (κm * ε)
  let R := (n : ℝ) ^ ε
  let L := Real.sqrt (Real.log (2 * (m : ℝ)))
  let X := Xρ (3 / 2 - s.val)
  let Z := Xρ (1 / 2)
  let P := Real.sqrt (∫ x, V x ^ 2 ∂ν)
  let F := ‖χ‖
  let H := C₀ * (T * R)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by positivity
  have hT : 1 ≤ T := Real.one_le_rpow hn1 (mul_nonneg hκm.le hε.le)
  have hR : 1 ≤ R := Real.one_le_rpow hn1 hε.le
  have hTR : 1 ≤ T * R := one_le_mul_of_one_le_of_one_le hT hR
  have hC₀ : 1 ≤ C₀ :=
    one_le_mul_of_one_le_of_one_le (by linarith only [hCm]) (by linarith only [hD])
  have hH : 1 ≤ H := one_le_mul_of_one_le_of_one_le hC₀ hTR
  have hCmC₀ : Cm ≤ C₀ := by
    dsimp only [C₀]
    nlinarith only [hCm, hD, mul_nonneg hCm.le hD.le]
  have hDC₀ : D ≤ C₀ := by
    dsimp only [C₀]
    nlinarith only [hCm, hD, mul_nonneg hCm.le hD.le]
  have hCmDC₀ : Cm * D ≤ C₀ := by dsimp only [C₀]; linarith only [hCm, hD]
  have hTTR : T ≤ T * R := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hR (by linarith only [hT])
  have hRTR : R ≤ T * R := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hT (by linarith only [hR])
  have hlog' : L ≤ D * R := by
    dsimp only [L, R]
    rw [Real.sqrt_eq_rpow]
    exact hlog n m (by linarith only [hmn, Real.rpow_nonneg hn0.le (1 / 2 + 1 / s.val)])
  have hLH : L ≤ H :=
    hlog'.trans (mul_le_mul hDC₀ hRTR (by positivity) (by linarith only [hC₀]))
  have hCT : Cm * T ≤ H :=
    mul_le_mul hCmC₀ hTTR (by positivity) (by linarith only [hC₀])
  have hCTL : Cm * T * L ≤ H := by
    calc
      _ ≤ Cm * T * (D * R) := mul_le_mul_of_nonneg_left hlog' (by positivity)
      _ = (Cm * D) * (T * R) := by ring
      _ ≤ H := mul_le_mul_of_nonneg_right hCmDC₀ (by positivity)
  have hX : 0 ≤ X := Real.sqrt_nonneg _
  have hZ : 0 ≤ Z := Real.sqrt_nonneg _
  have hP : 0 ≤ P := Real.sqrt_nonneg _
  have hF : 0 ≤ F := norm_nonneg _
  have hmultiplier : (m : ℝ) * ‖lam‖ ≤ H * F + H * Z := by
    have h : (m : ℝ) * ‖lam‖ ≤ Cm * T * F + (Cm * T * L) * Z := by
      convert hmlam using 1
      dsimp [T, L, Z, Xρ, F]
      ring
    exact h.trans (add_le_add (mul_le_mul_of_nonneg_right hCT hF)
      (mul_le_mul_of_nonneg_right hCTL hZ))
  have hηX : η ^ (3 - s.val) * X ≤ H * (η ^ (3 - s.val) * X) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hH
      (mul_nonneg (Real.rpow_nonneg hη.le (3 - s.val)) hX)
  have hηP : η⁻¹ * L * P ≤ H * (η⁻¹ * P) := by
    have hh := mul_le_mul_of_nonneg_left hLH (mul_nonneg (inv_nonneg.mpr hη.le) hP)
    nlinarith only [hh]
  have hinner : η ^ (3 - s.val) * X + η⁻¹ * L * P + (m : ℝ) * ‖lam‖ ≤
      H * (η ^ (3 - s.val) * X + η⁻¹ * P + F + Z) := by
    linarith only [hηX, hηP, hmultiplier]
  have hbracket : F ^ 2 + X *
      (η ^ (3 - s.val) * X + η⁻¹ * L * P + (m : ℝ) * ‖lam‖) ≤
      H * (F ^ 2 + X * (η ^ (3 - s.val) * X + η⁻¹ * P + F + Z)) := by
    have hh := mul_le_mul_of_nonneg_left hinner hX
    have hf := mul_le_mul_of_nonneg_right hH (sq_nonneg F)
    nlinarith only [hh, hf]
  calc
    _ ≤ Cd * (n : ℝ) ^ (κd * ε) * (F ^ 2 + X *
        (η ^ (3 - s.val) * X + η⁻¹ * L * P + (m : ℝ) * ‖lam‖)) := he
    _ ≤ Cd * (n : ℝ) ^ (κd * ε) *
        (H * (F ^ 2 + X * (η ^ (3 - s.val) * X + η⁻¹ * P + F + Z))) :=
      mul_le_mul_of_nonneg_left hbracket (by positivity)
    _ = _ := by
      dsimp only [H, T, R]
      rw [show (κd + κm + 1) * ε = κd * ε + (κm * ε + ε) by ring,
        Real.rpow_add hn0, Real.rpow_add hn0]
      ring


/-- Internal final scalar bounds for the gradient and multiplier in Lemma 5.13, after closing the value and primitive estimates. -/
theorem post_closure_internal (s T H F X Z P Y L J : ℝ) (hs : s < 1)
    (hT : 1 ≤ T) (hH : 1 ≤ H) (hF : 0 ≤ F) (hX : 0 ≤ X)
    (hZ : 0 ≤ Z) (hP : 0 ≤ P) (hY : 0 ≤ Y) (_hL : 0 ≤ L)
    (hLT : L ≤ T) (hXF : X ≤ H * F) (hZF : Z ≤ H * F) (hPF : P ≤ H * F)
    (hJ : J ≤ T * (F + L * Z))
    (hy : ∀ η : ℝ, 0 < η → η < 1 / 4 →
      Y ≤ T * (F ^ 2 + X * (η ^ (3 - s) * X + η⁻¹ * P + F + Z))) :
    X + Real.sqrt Y ≤ 8 * T ^ 2 * H * F ∧ J ≤ 8 * T ^ 2 * H * F := by
  have hT0 : 0 ≤ T := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hFF : F ≤ H * F := by nlinarith
  have heta : (1 / 8 : ℝ) ^ (3 - s) ≤ 1 :=
    Real.rpow_le_one (by norm_num) (by norm_num) (by linarith)
  have he := hy (1 / 8) (by norm_num) (by norm_num)
  norm_num only [inv_div, inv_one, div_one] at he
  have hi : (1 / 8 : ℝ) ^ (3 - s) * X + 8 * P + F + Z ≤ 11 * H * F := by
    have hh := mul_le_mul_of_nonneg_right heta hX
    nlinarith only [hh, hXF, hZF, hPF, hFF]
  have hb : Y ≤ 12 * T * (H * F) ^ 2 := by
    have hh := mul_le_mul hXF hi (by positivity) (by positivity : 0 ≤ H * F)
    have hf : F ^ 2 ≤ (H * F) ^ 2 := pow_le_pow_left₀ hF hFF 2
    have hk := mul_le_mul_of_nonneg_left (add_le_add hf hh) hT0
    nlinarith only [he, hk]
  have hsqrt : Real.sqrt Y ≤ 4 * T * H * F := by
    have ht : T ≤ T ^ 2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_right ht (sq_nonneg (H * F))
    nlinarith only [hb, hh, Real.sq_sqrt hY, Real.sqrt_nonneg Y,
      mul_nonneg hT0 (mul_nonneg hH0 hF)]
  have hTH : H * F ≤ T * H * F := by nlinarith
  have hTT : T * H * F ≤ T ^ 2 * H * F := by
    have hh : T ≤ T ^ 2 := by nlinarith
    nlinarith only [mul_le_mul_of_nonneg_right hh (mul_nonneg hH0 hF)]
  constructor
  · nlinarith only [hXF, hsqrt, hTH, hTT,
      mul_nonneg (sq_nonneg T) (mul_nonneg hH0 hF)]
  · have hz' := mul_le_mul hLT hZF hZ hT0
    have hf' : F ≤ T * H * F := hFF.trans hTH
    have hh := mul_le_mul_of_nonneg_left (add_le_add hf' hz') hT0
    nlinarith only [hJ, hh, mul_nonneg (sq_nonneg T) (mul_nonneg hH0 hF)]

/-- See Lemma 5.13 of the paper, all weighted and multiplier estimates for any
constrained weak solution and any L² source. The loss exponent precedes ε,
Cstar and the compact temperature interval. -/
theorem global_decay_bounds (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ)
    (hκstar : 0 < κstar) (hγstar : 0 < γstar) (M₀ : ℕ+) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε →
    ∀ Cstar : ℝ, 1 ≤ Cstar →
    ∀ βlo : ℝ, 0 < βlo → ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
      (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
    ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ)),
    2 ≤ (n : ℕ) → (n : ℕ) ≤ (m : ℕ) →
    (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
    let K := ⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ)
    1 ≤ K → 4 * K ≤ (m : ℕ) →
    ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M →
    ∀ β : ℝ, βlo ≤ β → β ≤ βhi →
    ∀ (χ : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _)
      (fun i => if i = i₀ then χ else 0) u →
    ∃ lam : Lp ℝ 2 ν,
      (∀ᵐ x ∂ν, lam x = gapMultiplierField m Q (fun x => β • M x)
        (fun i => if i = i₀ then χ else 0) u x) ∧
      WeightedWeakSolution Q (fun x => β • M x) ⊤
        (fun i => (if i = i₀ then χ else 0) + lam) u ∧
      Real.sqrt (∑ i, (weightRadius m i i₀ ^ (3 / 2 - s.val) * ‖(u i).val‖) ^ 2) +
        Real.sqrt (∑ i, weightRadius m i i₀ ^ (2 * (1 - s.val / 2)) * Q.2 (u i) (u i)) ≤
          C * (n : ℝ) ^ (κ * ε) * ‖χ‖ ∧
      ‖lam‖ ≤ C * (n : ℝ) ^ (κ * ε) * (m : ℝ)⁻¹ * ‖χ‖ ∧
      C * (n : ℝ) ^ (κ * ε) * (m : ℝ)⁻¹ * ‖χ‖ ≤
        C * (n : ℝ) ^ (-1 + κ * ε) * ‖χ‖ := by
  obtain ⟨κ₁, hκ₁, h₁⟩ := global_energy_first hzeta s κstar γstar hκstar.le hγstar.le M₀
  obtain ⟨κ₂, hκ₂, h₂⟩ := global_energy_second_L2 hzeta s κstar γstar hκstar hγstar.le M₀
  obtain ⟨κe, hκe, he⟩ := elliptic_regularized hzeta s κstar γstar hκstar hγstar M₀
  obtain ⟨κm, hκm, hmult⟩ := global_energy_multiplier s κstar γstar hκstar.le hγstar.le M₀
  let θ : ℝ := 1 / (3 - 2 * s.val)
  have hα : 0 < 3 / 2 - s.val := by linarith [s.property.2]
  have hden : 0 < 3 - 2 * s.val := by linarith [s.property.2]
  have hθ : 0 < θ := div_pos (by norm_num) hden
  have hθ1 : θ < 1 := (div_lt_one hden).mpr (by linarith [s.property.2])
  have hθratio : (1 / 2) / (3 / 2 - s.val) = θ := by
    dsimp [θ]
    field_simp
  obtain ⟨D, r, hD, hr, hclosure⟩ := scalar_young_closure_internal
    s.val θ s.property.1 s.property.2 hθ hθ1
  let k := κ₁ + κ₂ + κe + κm + κstar + 1
  have hk : 0 < k := by dsimp [k]; positivity
  refine ⟨k * (r + 3), by positivity, fun ε hε Cstar hCstar βlo hβlo βhi hβhi => ?_⟩
  obtain ⟨C₁, hC₁, h₁⟩ := h₁ ε hε Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨C₂, hC₂, h₂⟩ := h₂ ε hε Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Ce, hCe, he⟩ := he ε hε Cstar hCstar βlo hβlo
  obtain ⟨Cm, hCm, hmult⟩ := hmult ε hε Cstar hCstar βhi (hβlo.le.trans hβhi)
  obtain ⟨Cl, hCl, hlog⟩ := EllipticRegularity.log_absorption s hε (by norm_num : (0 : ℝ) < 1 / 2)
  let Cu := 1 + 2 * βlo⁻¹ * Cstar
  have hCu : 0 < Cu := by dsimp [Cu]; positivity
  let A := C₁ + C₂ + Ce + Cm + Cl + Cu + 1
  have hA : 1 ≤ A := by dsimp [A]; linarith only [hC₁, hC₂, hCe, hCm, hCl, hCu]
  refine ⟨8 * D * A ^ (r + 3), by positivity, ?_⟩
  intro Ω _ ν _ Q hQ hQc n m hm hn hnm hmn K hK hKm M hM β hβloβ hββhi χ i₀ u hu
  let T := A * (n : ℝ) ^ (k * ε)
  let H := D * T ^ (r + 1)
  let S := D * T ^ r
  let Xρ := fun (ρ : ℝ) => Real.sqrt (∑ i, (weightRadius m i i₀ ^ ρ * ‖(u i).val‖) ^ 2)
  let X := Xρ (3 / 2 - s.val)
  let Z := Xρ (1 / 2)
  let U := Real.sqrt (∑ i, ‖(u i).val‖ ^ 2)
  let Y := ∑ i, weightRadius m i i₀ ^ (2 * (1 - s.val / 2)) * Q.2 (u i) (u i)
  let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
    constructor <;> linarith [s.property.1, s.property.2]⟩
  let p := (1 - s.val / 2)⁻¹
  let V := fun x => (∑ i, |(rieszMatrix sh m hm *ᵥ (fun j => (u j).val x)) i| ^ p) ^ (1 / p)
  let P := Real.sqrt (∫ x, V x ^ 2 ∂ν)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by positivity
  have hT : 1 ≤ T := one_le_mul_of_one_le_of_one_le hA
    (Real.one_le_rpow hn1 (mul_nonneg hk.le hε.le))
  have hS : 1 ≤ S := one_le_mul_of_one_le_of_one_le hD (Real.one_le_rpow hT hr.le)
  have hH : 1 ≤ H := one_le_mul_of_one_le_of_one_le hD
    (Real.one_le_rpow hT (by linarith))
  have hcoef (c t : ℝ) (hcA : c ≤ A) (htk : t ≤ k) :
      c * (n : ℝ) ^ (t * ε) ≤ T :=
    mul_le_mul hcA (Real.rpow_le_rpow_of_exponent_le hn1
      (mul_le_mul_of_nonneg_right htk hε.le)) (by positivity) (by linarith)
  have hc₁ := hcoef C₁ κ₁ (by dsimp [A]; linarith only [hC₂,hCe,hCm,hCl,hCu])
    (by dsimp [k]; linarith only [hκ₂,hκe,hκm,hκstar])
  have hc₂ := hcoef C₂ κ₂ (by dsimp [A]; linarith only [hC₁,hCe,hCm,hCl,hCu])
    (by dsimp [k]; linarith only [hκ₁,hκe,hκm,hκstar])
  have hce := hcoef Ce κe (by dsimp [A]; linarith only [hC₁,hC₂,hCm,hCl,hCu])
    (by dsimp [k]; linarith only [hκ₁,hκ₂,hκm,hκstar])
  have hcm := hcoef Cm κm (by dsimp [A]; linarith only [hC₁,hC₂,hCe,hCl,hCu])
    (by dsimp [k]; linarith only [hκ₁,hκ₂,hκe,hκstar])
  have hcu := hcoef Cu κstar (by dsimp [A]; linarith only [hC₁,hC₂,hCe,hCm,hCl])
    (by dsimp [k]; linarith only [hκ₁,hκ₂,hκe,hκm])
  have hcl := hcoef Cl 1 (by dsimp [A]; linarith only [hC₁,hC₂,hCe,hCm,hCu])
    (by dsimp [k]; linarith only [hκ₁,hκ₂,hκe,hκm,hκstar])
  have hX : 0 ≤ X := Real.sqrt_nonneg _
  have hZ : 0 ≤ Z := Real.sqrt_nonneg _
  have hP : 0 ≤ P := Real.sqrt_nonneg _
  have hY : 0 ≤ Y := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (Real.rpow_nonneg (by linarith [one_le_weightRadius m i i₀]) _) (hQ.2.2.1 _))
  have he₁ : X ^ 2 ≤ T * (X * (‖χ‖ + Z + P) + Y) :=
    (h₁ ν Q hQ n m hm hn hnm hmn hK hKm M hM β hβloβ hββhi χ i₀ u hu).trans
      (mul_le_mul_of_nonneg_right hc₁ (by positivity))
  obtain ⟨_, _, _, _, hy⟩ := h₂ ν Q hQ n m hm hn hnm hmn hK hKm M hM β hβloβ hββhi χ i₀ u hu
  have he₂ : ∀ η : ℝ, 0 < η → η < 1 / 4 →
      Y ≤ T * (‖χ‖ ^ 2 + X * (η ^ (3 - s.val) * X + η⁻¹ * P + ‖χ‖ + Z)) := by
    intro η hη hη'
    exact (hy η hη hη').trans (mul_le_mul_of_nonneg_right hc₂ (by positivity))
  have hmn' : (m : ℝ) ≤ 3 * (n : ℝ) ^ (1 / 2 + 1 / s.val) :=
    hmn.trans (by nlinarith only [Real.rpow_nonneg hn0.le (1 / 2 + 1 / s.val)])
  obtain ⟨_, hp⟩ := he β hβloβ ν n m hm hnm hmn' (by dsimp [K] at hKm; omega)
    M hM Q hQ hQc i₀ χ u hu
  have heP : P ≤ T * (‖χ‖ + Z) ^ s.val * X ^ (1 - s.val) :=
    hp.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hce (by positivity)) (by positivity))
  have hU : U ≤ T * ‖χ‖ := by
    have hh := global_energy_unweighted s n m hm K Cstar κstar γstar ε hCstar hκstar.le hε.le
      Q hQ M hM βlo β hβlo hβloβ χ i₀ u hu
    have hb := mul_le_mul_of_nonneg_right hcu (norm_nonneg χ)
    have hg := Real.sqrt_nonneg (∑ i, Q.2 (u i) (u i))
    linarith only [hh, hb, hg]
  have hZi : Z ≤ U ^ (1 - θ) * X ^ θ := by
    simpa only [hθratio] using
      weighted_norm_interpolation m i₀ (fun i => (u i).val) (1 / 2) (3 / 2 - s.val)
        (by norm_num) (by linarith [s.property.2]) hα
  have hXS : X ≤ S * ‖χ‖ := by
    by_cases hf : ‖χ‖ = 0
    · have hχ : χ = 0 := norm_eq_zero.mp hf
      have huz := zero_source s n m hm K Cstar κstar γstar ε hCstar Q hQ M hM β
        (hβlo.trans_le hβloβ) u (by simpa only [hχ, ite_self] using hu)
      simp [X, Xρ, huz, hf]
    · have hF : 0 < ‖χ‖ := lt_of_le_of_ne (norm_nonneg χ) (Ne.symm hf)
      have hh := hclosure T ‖χ‖ U X Z P Y hT hF
        (Real.sqrt_nonneg _) hX hZ hP hU hZi heP he₁ he₂
      dsimp only [S]
      linarith only [hh, norm_nonneg χ]
  have hZX : Z ≤ X := by
    have hw (i : Fin (m : ℕ)) : 0 ≤ weightRadius m i i₀ :=
      (zero_le_one.trans (one_le_weightRadius m i i₀))
    have hh := weighted_norm_mono_internal (fun i => (u i).val)
      (fun i => weightRadius m i i₀ ^ (1 / 2 : ℝ))
      (fun i => weightRadius m i i₀ ^ (3 / 2 - s.val)) 1 (by norm_num)
      (fun i => Real.rpow_nonneg (hw i) _) (fun i => Real.rpow_nonneg (hw i) _)
      (fun i => by
        rw [one_mul]
        exact Real.rpow_le_rpow_of_exponent_le (one_le_weightRadius m i i₀)
          (by linarith [s.property.2]))
    simpa only [one_mul] using hh
  have hSH : S ≤ H := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hT (by linarith : r ≤ r + 1)) (by linarith)
  have hXF : X ≤ H * ‖χ‖ := hXS.trans (mul_le_mul_of_nonneg_right hSH (norm_nonneg χ))
  have hZF : Z ≤ H * ‖χ‖ := hZX.trans hXF
  have hPF : P ≤ H * ‖χ‖ := by
    have hbase : ‖χ‖ + Z ≤ S * ‖χ‖ := by
      have hh : Z ≤ X := hZX
      by_cases hf : ‖χ‖ = 0
      · simp only [hf, mul_zero] at hXS ⊢
        linarith only [hh, hXS]
      · have hF : 0 < ‖χ‖ := lt_of_le_of_ne (norm_nonneg χ) (Ne.symm hf)
        exact (add_le_add_right hZX ‖χ‖).trans
          (hclosure T ‖χ‖ U X Z P Y hT hF
            (Real.sqrt_nonneg _) hX hZ hP hU hZi heP he₁ he₂)
    have hb := heP.trans (mul_le_mul
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hbase s.property.1.le)
        (by linarith : 0 ≤ T))
      (Real.rpow_le_rpow hX hXS (by linarith [s.property.2])) (by positivity) (by positivity))
    have hid : (S * ‖χ‖) ^ s.val * (S * ‖χ‖) ^ (1 - s.val) = S * ‖χ‖ := by
      rw [← Real.rpow_add' (by positivity : 0 ≤ S * ‖χ‖) (by linarith : s.val + (1 - s.val) ≠ 0)]
      norm_num
    have hTS : T * S = H := by
      dsimp only [S, H]
      rw [Real.rpow_add_one (by linarith : T ≠ 0)]
      ring
    calc
      P ≤ T * ((S * ‖χ‖) ^ s.val * (S * ‖χ‖) ^ (1 - s.val)) := by nlinarith only [hb]
      _ = H * ‖χ‖ := by rw [hid]; rw [← mul_assoc, hTS]
  obtain ⟨lam, hlam, hfull, _, hmlam⟩ := hmult ν Q n m hm hn hnm hmn hK hKm M hM β
    (hβlo.le.trans hβloβ) hββhi χ i₀ u hu
  have hJ : (m : ℝ) * ‖lam‖ ≤ T * (‖χ‖ + Real.sqrt (Real.log (2 * (m : ℝ))) * Z) :=
    hmlam.trans (mul_le_mul_of_nonneg_right hcm (by positivity))
  have hL : Real.sqrt (Real.log (2 * (m : ℝ))) ≤ T := by
    rw [Real.sqrt_eq_rpow]
    exact (hlog n m hmn').trans (by simpa only [one_mul] using hcl)
  obtain ⟨hXY, hml⟩ := post_closure_internal s.val T H ‖χ‖ X Z P Y
    (Real.sqrt (Real.log (2 * (m : ℝ)))) ((m : ℝ) * ‖lam‖) s.property.2 hT hH
    (norm_nonneg _) hX hZ hP hY (Real.sqrt_nonneg _) hL hXF hZF hPF hJ he₂
  have hcoeff : 8 * T ^ 2 * H =
      (8 * D * A ^ (r + 3)) * (n : ℝ) ^ ((k * (r + 3)) * ε) := by
    have hid : T ^ 2 * T ^ (r + 1) = T ^ (r + 3) := by
      rw [← Real.rpow_two, ← Real.rpow_add (by linarith : 0 < T)]
      congr 1
      ring
    calc
      _ = 8 * D * (T ^ 2 * T ^ (r + 1)) := by dsimp only [H]; ring
      _ = 8 * D * T ^ (r + 3) := by rw [hid]
      _ = _ := by
        dsimp only [T]
        rw [Real.mul_rpow (by linarith : 0 ≤ A) (by positivity),
          ← Real.rpow_mul hn0.le, show (k * ε) * (r + 3) = (k * (r + 3)) * ε by ring]
        ring
  rw [hcoeff] at hXY hml
  refine ⟨lam, hlam, hfull, hXY, ?_, ?_⟩
  · have hh : ‖lam‖ ≤
        ((8 * D * A ^ (r + 3)) * (n : ℝ) ^ ((k * (r + 3)) * ε) * ‖χ‖) / (m : ℝ) :=
      (le_div_iff₀ (by positivity : (0 : ℝ) < m)).mpr
        (by simpa only [mul_comm] using hml)
    exact hh.trans_eq (by rw [div_eq_mul_inv]; ac_rfl)
  · have hinv : (m : ℝ)⁻¹ ≤ (n : ℝ)⁻¹ :=
      inv_anti₀ hn0 (by exact_mod_cast hnm)
    have hh := mul_le_mul_of_nonneg_left hinv
      (by positivity : 0 ≤ (8 * D * A ^ (r + 3)) * (n : ℝ) ^ ((k * (r + 3)) * ε))
    have hh' := mul_le_mul_of_nonneg_right hh (norm_nonneg χ)
    rw [show -1 + (k * (r + 3)) * ε = (k * (r + 3)) * ε + (-1) by ring,
      Real.rpow_add hn0, Real.rpow_neg_one]
    simpa only [mul_assoc] using hh'

/-- See Lemma 5.13 of the paper (Global decay, constrained equation).
Unique weak solvability, both regularized weighted estimates, the canonical
L² multiplier and both multiplier inequalities, for every L² source.
The constants are uniform on each compact positive temperature interval. -/
theorem global_decay (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ)
    (hκstar : 0 < κstar) (hγstar : 0 < γstar) (M₀ : ℕ+) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε →
    ∀ Cstar : ℝ, 1 ≤ Cstar →
    ∀ βlo : ℝ, 0 < βlo → ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
      (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
    ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ)),
    2 ≤ (n : ℕ) → (n : ℕ) ≤ (m : ℕ) →
    (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
    let K := ⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ)
    1 ≤ K → 4 * K ≤ (m : ℕ) →
    ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M →
    ∀ β : ℝ, βlo ≤ β → β ≤ βhi →
    ∀ (χ : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ)),
    ∃! u : Fin (m : ℕ) → Q.1,
      WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _)
        (fun i => if i = i₀ then χ else 0) u ∧
    ∃ lam : Lp ℝ 2 ν,
      (∀ᵐ x ∂ν, lam x = gapMultiplierField m Q (fun x => β • M x)
        (fun i => if i = i₀ then χ else 0) u x) ∧
      WeightedWeakSolution Q (fun x => β • M x) ⊤
        (fun i => (if i = i₀ then χ else 0) + lam) u ∧
      Real.sqrt (∑ i, (weightRadius m i i₀ ^ (3 / 2 - s.val) * ‖(u i).val‖) ^ 2) +
        Real.sqrt (∑ i, weightRadius m i i₀ ^ (2 * (1 - s.val / 2)) * Q.2 (u i) (u i)) ≤
          C * (n : ℝ) ^ (κ * ε) * ‖χ‖ ∧
      ‖lam‖ ≤ C * (n : ℝ) ^ (κ * ε) * (m : ℝ)⁻¹ * ‖χ‖ ∧
      C * (n : ℝ) ^ (κ * ε) * (m : ℝ)⁻¹ * ‖χ‖ ≤
        C * (n : ℝ) ^ (-1 + κ * ε) * ‖χ‖ := by
  obtain ⟨κ, hκ, hb⟩ := global_decay_bounds hzeta s κstar γstar hκstar hγstar M₀
  refine ⟨κ, hκ, fun ε hε Cstar hCstar βlo hβlo βhi hβhi => ?_⟩
  obtain ⟨C, hC, hb⟩ := hb ε hε Cstar hCstar βlo hβlo βhi hβhi
  refine ⟨C, hC, ?_⟩
  intro Ω _ ν _ Q hQ hQc n m hm hn hnm hmn K hK hKm M hM β hβloβ hββhi χ i₀
  let a := Cstar⁻¹ * (n : ℝ) ^ (-κstar * ε)
  have ha : 0 < a := SchurRestriction.periodized_mass_pos hCstar
  have hl : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
      ∀ z : Fin (m : ℕ) → ℝ,
        a * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j :=
    hM.2.1.mono (fun _ hx => ⟨hx.1, hx.2.2.1⟩)
  obtain ⟨u, hu, huniq⟩ := (AbstractEquation.existence_energy Q hQ β
    (hβlo.trans_le hβloβ) M hM.1 a ha hl (zeroSumComponents _)
    (fun i => if i = i₀ then χ else 0)).1
  exact ⟨u, ⟨hu, hb ν Q hQ hQc n m hm hn hnm hmn hK hKm M hM β hβloβ hββhi χ i₀ u hu⟩,
    fun v hv => huniq v hv.1⟩

end Riesz2.GlobalDecay
