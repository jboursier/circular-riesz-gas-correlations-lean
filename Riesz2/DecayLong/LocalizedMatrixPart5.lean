/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.UnconstrainedGlobalDecay
public import Riesz2.DecayLong.LocalizedMatrixPart3

/-!
# Uniform analytic transfer at a common cutoff

The analytic clause of the proof of Proposition 5.15.
The exponent is free above a fixed positive lower bound, while every prefactor
is chosen before that exponent. The cutoff stays literally `floor(n^ε)^M₀`.
The proofs reuse the scalar-form estimates and make their dependence
on the logarithm-absorption parameter explicit. No configuration space changes.
-/

@[expose] public section
noncomputable section
open MeasureTheory Matrix Filter
open scoped BigOperators Fin.NatCast MatrixOrder Matrix.Norms.L2Operator
namespace Riesz2.LocalizedMatrix.Analytic
open Riesz2.EllipticPrimitive Riesz2.EllipticRegularity Riesz2.GlobalDecay
open Riesz2.UnconstrainedGlobalDecay Riesz2.DerivativeControl

/-- See the proof of Proposition 5.15 in the paper: logarithmic absorption
uniform for every local loss exponent above `εmin`. -/
theorem log_absorption (s : Riesz1.RieszExponent) {εmin A : ℝ}
    (hεmin : 0 < εmin) (hA : 0 < A) :
    ∃ D : ℝ, 0 < D ∧ ∀ ε : ℝ, εmin ≤ ε → ∀ n m : ℕ+,
      (m : ℝ) ≤ 3 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
      Real.log (2 * (m : ℝ)) ^ A ≤ D * (n : ℝ) ^ ε := by
  obtain ⟨D, hD, hb⟩ := EllipticRegularity.log_absorption s hεmin hA
  refine ⟨D, hD, fun ε hε n m hm => (hb n m hm).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast n.pos : (1 : ℝ) ≤ n) hε) hD.le

/-- Uniform local-exponent interface for the proof of Lemma 5.13, used in
the proof of Proposition 5.15. The reference cutoff is unchanged. -/
theorem global_error_backward_differences (s : Riesz1.RieszExponent)
    (κₛ γₛ : ℝ) (hκₛ : 0 ≤ κₛ) (_hγₛ : 0 ≤ γₛ) (M₀ : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (Cₛ : ℝ), 1 ≤ Cₛ →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ (ε : ℝ), 0 < ε → ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ))
        (_hn : 2 ≤ (n : ℕ)) (_hnm : (n : ℕ) ≤ (m : ℕ))
        (_hmn : (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val)),
        let K := ⌊(n : ℝ) ^ ε⌋₊ ^ M₀
        1 ≤ K → 4 * K ≤ (m : ℕ) →
        ∀ {α : Type*} [MeasurableSpace α] (ν : Measure α)
          (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ),
        PeriodizedMatrixBounds (ν := ν) s n m hm K Cₛ κₛ γₛ ε M →
        ∃ a B : ℝ, 0 < a ∧ a ≤ 1 ∧ 1 ≤ B ∧ a⁻¹ + B ≤ C * (n : ℝ) ^ (κ * ε) ∧
          ∀ᵐ x ∂ν,
            let E := M x - (2 : ℝ) • rieszMatrix s m hm
            (∀ i j, |E i j| ≤ C * (n : ℝ) ^ (κ * ε) *
              (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-1 - s.val / 2)) ∧
            (∀ i j, |E i j - E (i - 1) j| + |E i j - E i (j - 1)| ≤
              C * (n : ℝ) ^ (κ * ε) *
                (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-1 - s.val)) ∧
            (∀ i j, |(E i j - E (i - 1) j) - (E i (j - 1) - E (i - 1) (j - 1))| ≤
              C * (n : ℝ) ^ (κ * ε) *
                (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-2 - s.val)) ∧
            (∀ i, ∑ j, |E i j| ≤ C * (n : ℝ) ^ (κ * ε)) ∧
            (∀ j, ∑ i, |E i j| ≤ C * (n : ℝ) ^ (κ * ε)) ∧
            a • (1 : Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ) ≤ M x ∧ ‖E‖ ≤ B := by
  obtain ⟨R, hR, hest⟩ := global_reference_error_estimates s
  let q := 1 + s.val / 2
  let t := s.val + 2
  let κ := κₛ + (M₀ : ℝ) * q + 1
  have hq : 0 < q := by dsimp [q]; linarith [s.property.1]
  have ht : 1 < t := by dsimp [t]; linarith [s.property.1]
  have hκ : 0 < κ := by dsimp [κ]; positivity
  refine ⟨κ, hκ, ?_⟩
  intro Cₛ hCₛ
  let S := ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s.val - 1)
  let U := ∑' k : ℕ, (1 + (k : ℝ)) ^ (-t)
  let Z := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-q)
  let D := Cₛ + 4 * R * S
  let J := Cₛ + 2 * R
  let F := 2 * (1 + 1 / (t - 1)) * 2 ^ (t - 1)
  let G := 2 * (U + 2 ^ t)
  let C := 1 + D + 2 * F * J + G * J + D * Z + Cₛ + 1
  have hS : 0 ≤ S := tsum_nonneg fun _ => by positivity
  have hU : 0 ≤ U := tsum_nonneg fun _ => by positivity
  have hZ : 0 ≤ Z := mul_nonneg two_pos.le (tsum_nonneg fun _ => by positivity)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hFJ : 0 ≤ 2 * F * J := by positivity
  have hGJ : 0 ≤ G * J := by positivity
  have hDZ : 0 ≤ D * Z := by positivity
  have hC1 : 1 ≤ C := by dsimp [C]; linarith only [hD, hFJ, hGJ, hDZ, hCₛ]
  have hCD : D ≤ C := by dsimp [C]; linarith only [hFJ, hGJ, hDZ, hCₛ]
  have hCF : 2 * F * J ≤ C := by dsimp [C]; linarith only [hD, hGJ, hDZ, hCₛ]
  have hCG : G * J ≤ C := by dsimp [C]; linarith only [hD, hFJ, hDZ, hCₛ]
  have hCZ : D * Z ≤ C := by dsimp [C]; linarith only [hD, hFJ, hGJ, hCₛ]
  have hCA : Cₛ + 1 + D * Z ≤ C := by dsimp [C]; linarith only [hD, hFJ, hGJ]
  refine ⟨C, hC1, ?_⟩
  intro ε hε n m hm hn _ _ K hK _ α _ ν M hM
  let L := (n : ℝ) ^ (κ * ε)
  let W := (n : ℝ) ^ (κₛ * ε)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ (n : ℕ))
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hL : 1 ≤ L := Real.one_le_rpow hn1 (mul_nonneg hκ.le hε.le)
  have hW : 1 ≤ W := Real.one_le_rpow hn1 (mul_nonneg hκₛ hε.le)
  have hWL : W ≤ L := Real.rpow_le_rpow_of_exponent_le hn1
    (mul_le_mul_of_nonneg_right (by dsimp [κ]; linarith only [mul_nonneg (Nat.cast_nonneg M₀) hq.le]) hε.le)
  have hKL : (K : ℝ) ^ q ≤ L := by
    have hh := GlobalReferenceErrorInternal.cutoff_power_le n ε q hq.le M₀
    exact hh.trans (Real.rpow_le_rpow_of_exponent_le hn1
      (mul_le_mul_of_nonneg_right (by dsimp [κ]; linarith) hε.le))
  have hPJ : Cₛ * W + 2 * R ≤ J * L := by
    have h1 := mul_le_mul_of_nonneg_left hWL (by linarith only [hCₛ] : 0 ≤ Cₛ)
    have h2 := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ 2 * R)
    dsimp [J]
    nlinarith only [h1, h2]
  have hPD : Cₛ * W + 4 * R * S * (K : ℝ) ^ q ≤ D * L := by
    have h1 := mul_le_mul_of_nonneg_left hWL (by linarith only [hCₛ] : 0 ≤ Cₛ)
    have h2 := mul_le_mul_of_nonneg_left hKL (by positivity : 0 ≤ 4 * R * S)
    dsimp [D]
    nlinarith only [h1, h2]
  let a := Cₛ⁻¹ * (n : ℝ) ^ (-κₛ * ε)
  let B := max 1 (D * Z * L)
  have hs0 := s.property.1
  have ha : 0 < a := by dsimp [a]; positivity
  have hae : a = (Cₛ * W)⁻¹ := by
    dsimp [a, W]
    rw [show -κₛ * ε = -(κₛ * ε) by ring, Real.rpow_neg hn0.le, _root_.mul_inv_rev, mul_comm]
  have ha1 : a ≤ 1 := by
    rw [hae]
    apply inv_le_one_of_one_le₀
    nlinarith only [hCₛ, hW, mul_nonneg (sub_nonneg.mpr hCₛ) (sub_nonneg.mpr hW)]
  have hB1 : 1 ≤ B := le_max_left _ _
  have haL : a⁻¹ ≤ Cₛ * L := by
    rw [hae, inv_inv]
    exact mul_le_mul_of_nonneg_left hWL (by linarith only [hL, hCₛ])
  have hBL : B ≤ (1 + D * Z) * L := by
    apply max_le
    · have hp := mul_nonneg hDZ (show 0 ≤ L by linarith only [hL])
      nlinarith only [hL, hp]
    · nlinarith only [hL]
  have hab : a⁻¹ + B ≤ C * L := by
    calc _ ≤ Cₛ * L + (1 + D * Z) * L := add_le_add haL hBL
         _ = (Cₛ + 1 + D * Z) * L := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_right hCA (by linarith only [hL, hCₛ])
  refine ⟨a, B, ha, ha1, hB1, hab, ?_⟩
  have he := hest n m hm K hK Cₛ (by linarith only [hL, hCₛ]) κₛ γₛ ε ν M hM
  have hc := periodizedMatrixBounds_coercive s n m hm K Cₛ κₛ γₛ ε M hM
  filter_upwards [he, hc] with x hx hcx
  let E := M x - (2 : ℝ) • rieszMatrix s m hm
  have hentry (i j : Fin (m : ℕ)) : |E i j| ≤ C * L *
      (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-1 - s.val / 2) := by
    have hh := hx.1 i j
    change |E i j| ≤ (Cₛ * W + 4 * R * S * (K : ℝ) ^ q) *
      (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-q) at hh
    rw [show -q = -1 - s.val / 2 by dsimp [q]; ring] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (hPD.trans
      (mul_le_mul_of_nonneg_right hCD (by linarith only [hL, hCₛ]))) (by positivity))
  have hfirst (i j : Fin (m : ℕ)) :
      |E i j - E (i - 1) j| + |E i j - E i (j - 1)| ≤ C * L *
        (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-1 - s.val) := by
    have hh := hx.2.1 i j
    have hfc : 2 * (2 * (Cₛ * W + 2 * R) * (1 + 1 / (t - 1)) * 2 ^ (t - 1)) ≤ C * L := by
      calc
        _ = (2 * F) * (Cₛ * W + 2 * R) := by dsimp [F]; ring
        _ ≤ (2 * F) * (J * L) := mul_le_mul_of_nonneg_left hPJ (by positivity)
        _ = (2 * F * J) * L := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hCF (by linarith only [hL, hCₛ])
    exact hh.trans (mul_le_mul_of_nonneg_right hfc (by positivity))
  have hmixed (i j : Fin (m : ℕ)) :
      |(E i j - E (i - 1) j) - (E i (j - 1) - E (i - 1) (j - 1))| ≤ C * L *
        (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-2 - s.val) := by
    have hh := hx.2.2.1 i j
    have hgc : 2 * (Cₛ * W + 2 * R) * (U + 2 ^ t) ≤ C * L := by
      calc
        _ = G * (Cₛ * W + 2 * R) := by dsimp [G]; ring
        _ ≤ G * (J * L) := mul_le_mul_of_nonneg_left hPJ hG
        _ = (G * J) * L := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hCG (by linarith only [hL, hCₛ])
    exact hh.trans (mul_le_mul_of_nonneg_right hgc (by positivity))
  have hbound : (Cₛ * W + 4 * R * S * (K : ℝ) ^ q) * Z ≤ D * Z * L := by
    have hh := mul_le_mul_of_nonneg_right hPD hZ
    nlinarith only [hh]
  have hboundC : (Cₛ * W + 4 * R * S * (K : ℝ) ^ q) * Z ≤ C * L :=
    hbound.trans (mul_le_mul_of_nonneg_right hCZ (by linarith only [hL, hCₛ]))
  exact ⟨hentry, hfirst, hmixed, fun i => (hx.2.2.2.1 i).trans hboundC,
    (fun j => (hx.2.2.2.2.1 j).trans hboundC), hcx,
    hx.2.2.2.2.2.trans (hbound.trans (le_max_right _ _))⟩

/-- Uniform local-exponent interface for the proof of Lemma 5.13, used in
the proof of Proposition 5.15. The reference cutoff is unchanged. -/
theorem global_error_differences (s : Riesz1.RieszExponent)
    (κₛ γₛ : ℝ) (hκₛ : 0 ≤ κₛ) (_hγₛ : 0 ≤ γₛ) (M₀ : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (Cₛ : ℝ), 1 ≤ Cₛ →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ (ε : ℝ), 0 < ε → ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ))
        (_hn : 2 ≤ (n : ℕ)) (_hnm : (n : ℕ) ≤ (m : ℕ))
        (_hmn : (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val)),
        let K := ⌊(n : ℝ) ^ ε⌋₊ ^ M₀
        1 ≤ K → 4 * K ≤ (m : ℕ) →
        ∀ {α : Type*} [MeasurableSpace α] (ν : Measure α)
          (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ),
        PeriodizedMatrixBounds (ν := ν) s n m hm K Cₛ κₛ γₛ ε M →
        ∃ a B : ℝ, 0 < a ∧ a ≤ 1 ∧ 1 ≤ B ∧ a⁻¹ + B ≤ C * (n : ℝ) ^ (κ * ε) ∧
          ∀ᵐ x ∂ν,
            let E := M x - (2 : ℝ) • rieszMatrix s m hm
            (∀ i j, |E i j| ≤ C * (n : ℝ) ^ (κ * ε) *
              (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-1 - s.val / 2)) ∧
            (∀ i j, |E i j - E (i + 1) j| + |E i j - E i (j + 1)| ≤
              C * (n : ℝ) ^ (κ * ε) *
                (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-1 - s.val)) ∧
            (∀ i j, |(E i j - E (i + 1) j) - (E i (j + 1) - E (i + 1) (j + 1))| ≤
              C * (n : ℝ) ^ (κ * ε) *
                (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-2 - s.val)) ∧
            (∀ i, ∑ j, |E i j| ≤ C * (n : ℝ) ^ (κ * ε)) ∧
            (∀ j, ∑ i, |E i j| ≤ C * (n : ℝ) ^ (κ * ε)) ∧
            a • (1 : Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ) ≤ M x ∧ ‖E‖ ≤ B := by
  obtain ⟨κ, hκ, hb⟩ := global_error_backward_differences s κₛ γₛ hκₛ _hγₛ M₀
  refine ⟨κ, hκ, ?_⟩
  intro Cₛ hCₛ
  obtain ⟨C, hC, hb⟩ := hb Cₛ hCₛ
  let F := (2 : ℝ) ^ (1 + s.val)
  let C' := 2 * F * C
  have hF : 1 ≤ F := Real.one_le_rpow (by norm_num) (by linarith [s.property.1])
  have hCC : C ≤ C' := by
    dsimp [C']
    nlinarith only [hC, hF, mul_nonneg (sub_nonneg.mpr hF) (show 0 ≤ C by linarith only [hC])]
  refine ⟨C', hC.trans hCC, ?_⟩
  intro ε hε n m hm hn hnm hmn K hK hKm α _ ν M hM
  obtain ⟨a, B, ha, ha1, hB1, hab, he⟩ := hb ε hε n m hm hn hnm hmn hK hKm ν M hM
  let L := (n : ℝ) ^ (κ * ε)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hloss : C * L ≤ C' * L := mul_le_mul_of_nonneg_right hCC hL
  refine ⟨a, B, ha, ha1, hB1, hab.trans hloss, ?_⟩
  filter_upwards [he] with x hx
  let E := M x - (2 : ℝ) • rieszMatrix s m hm
  refine ⟨fun i j => (hx.1 i j).trans (mul_le_mul_of_nonneg_right hloss (by positivity)),
    ?_, ?_, fun i => (hx.2.2.2.1 i).trans hloss,
    fun j => (hx.2.2.2.2.1 j).trans hloss, hx.2.2.2.2.2.1, hx.2.2.2.2.2.2⟩
  · intro i j
    have hi := hx.2.1 (i + 1) j
    have hj := hx.2.1 i (j + 1)
    simp only [add_sub_cancel_right] at hi hj
    have hpi := GlobalReferenceErrorInternal.forward_distance_power m hm i j
      (q := 1 + s.val) (by linarith [s.property.1])
    have hpj := GlobalReferenceErrorInternal.forward_distance_power m hm j i
      (q := 1 + s.val) (by linarith [s.property.1])
    have hdist (u v : Fin (m : ℕ)) : Riesz1.cyclicIndexDistance m u v =
        Riesz1.cyclicIndexDistance m v u := by simp only [Riesz1.cyclicIndexDistance, Nat.dist_comm]
    rw [hdist (j + 1) i, hdist j i] at hpj
    rw [show -(1 + s.val) = -1 - s.val by ring] at hpi hpj
    have hci := mul_le_mul_of_nonneg_left hpi (show 0 ≤ C * L by positivity)
    have hcj := mul_le_mul_of_nonneg_left hpj (show 0 ≤ C * L by positivity)
    change |E i j - E (i + 1) j| + |E i j - E i (j + 1)| ≤ _
    rw [abs_sub_comm (E i j) (E (i + 1) j), abs_sub_comm (E i j) (E i (j + 1))]
    have h1 : |E (i + 1) j - E i j| ≤ C * L *
        (F * (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-1 - s.val)) :=
      (le_add_of_nonneg_right (abs_nonneg _)).trans (hi.trans hci)
    have h2 : |E i (j + 1) - E i j| ≤ C * L *
        (F * (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-1 - s.val)) :=
      (le_add_of_nonneg_left (abs_nonneg _)).trans (hj.trans hcj)
    dsimp [C']
    nlinarith only [h1, h2]
  · intro i j
    have hh := hx.2.2.1 (i + 1) (j + 1)
    simp only [add_sub_cancel_right, GlobalReferenceErrorInternal.distance_translate] at hh
    have hh' := hh.trans (mul_le_mul_of_nonneg_right hloss
      (show 0 ≤ (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-2 - s.val) by positivity))
    convert hh' using 1
    congr 1
    ring

/-- Uniform local-exponent interface for Lemma 5.9 of the paper, used in
the proof of Proposition 5.15. The angular resolvent estimate supplies the bound.
Parseval expresses it using the sine multiplier. -/
theorem elliptic_primitive (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (κstar γstar : ℝ) (hκstar : 0 < κstar) (M₀ : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (Cstar : ℝ), 1 ≤ Cstar → ∀ βlo : ℝ, 0 < βlo → ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ), 0 < ε →
    ∀ (β : ℝ), βlo ≤ β →
    ∀ {α : Type*} [MeasurableSpace α] (ν : Measure α)
      (n m : ℕ+) (hm : 2 ≤ (m : ℕ))
      (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ),
    PeriodizedMatrixBounds (ν := ν) s n m hm (⌊(n : ℝ) ^ ε⌋₊ ^ M₀)
      Cstar κstar γstar ε M →
    ∀ (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q →
    ∀ (χ : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents (Fin (m : ℕ)))
      (fun i => if i = i₀ then χ else 0) u →
    let J := fun x => cycleFourierInv m (fun k =>
      (if k = 0 then 0 else (DiscreteInterpolation.frequencyRadius (cycleAngle m k) ^
        (-(3 / 2 - s.val)) : ℝ)) * cycleFourier m (fun j => ((u j).val x : ℂ)) k)
    let w := fun j => 1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (1 / 2 : ℝ)
    Integrable (fun x => ∑ i, ‖J x i‖ ^ 2) ν ∧
    Integrable (fun x => ∑ j, (w j * (u j).val x) ^ 2) ν ∧
      Real.sqrt (∫ x, ∑ i, ‖J x i‖ ^ 2 ∂ν) ≤
        C * (n : ℝ) ^ (κ * ε) * Real.log (2 * (m : ℝ)) *
          (‖χ‖ + Real.sqrt (∫ x, ∑ j, (w j * (u j).val x) ^ 2 ∂ν)) := by
  obtain ⟨κ, hκ, hp⟩ := elliptic_primitive_angular_radius_uniform hz s κstar γstar hκstar M₀
  let A := (Real.pi / 2) ^ (3 / 2 - s.val)
  have hA : 0 < A := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨κ, hκ, fun Cstar hCstar βlo hβlo => ?_⟩
  obtain ⟨C, hC, hc⟩ := hp Cstar hCstar βlo hβlo
  refine ⟨A * C, mul_pos hA hC, ?_⟩
  intro ε hε β hβ α _ ν n m hm M hM Q hQ χ i₀ u hu J w
  obtain ⟨hJ, hwr, hprimitive⟩ := hc ε hε β hβ ν n m hm M hM Q hQ χ i₀ u hu
  have hlog : 0 ≤ Real.log (2 * (m : ℝ)) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ m := by exact_mod_cast m.pos
    linarith)
  have hJs := (CyclicFourierL2.multiplier_parseval m
    (fun k => if k = 0 then 0 else
      DiscreteInterpolation.frequencyRadius (cycleAngle m k) ^ (-(3 / 2 - s.val)))
    (fun j => (u j).val)).1
  have hw := (CyclicFourierL2.weighted_integral_sq w (fun j => (u j).val)).1
  have hwle (j : Fin (m : ℕ)) : weightRadius m j i₀ ^ (1 / 2 : ℝ) ≤ w j := by
    dsimp only [w]
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    have hd : 0 ≤ (Riesz1.cyclicIndexDistance m j i₀ : ℝ) := Nat.cast_nonneg _
    have hs := Real.sq_sqrt hd
    change 1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ≤
      (1 + Real.sqrt (Riesz1.cyclicIndexDistance m j i₀ : ℝ)) ^ 2
    nlinarith [Real.sqrt_nonneg (Riesz1.cyclicIndexDistance m j i₀ : ℝ)]
  have hweight := Real.sqrt_le_sqrt (integral_mono hwr hw (fun x => by
    apply Finset.sum_le_sum
    intro j _
    rw [mul_pow, mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Real.rpow_nonneg (by unfold weightRadius; positivity) _)
        (hwle j) 2) (sq_nonneg _)))
  have henergy := integral_mono hJs (hJ.const_mul (A ^ 2)) (fun x =>
    DiscreteInterpolation.sine_energy_le_angularPrimitive m
      (by linarith [s.property.2] : 0 ≤ 3 / 2 - s.val)
      (fun j => ((u j).val x : ℂ)))
  rw [integral_const_mul] at henergy
  have hnorm := Real.sqrt_le_sqrt henergy
  rw [Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq hA.le] at hnorm
  refine ⟨hJs, hw, hnorm.trans ?_⟩
  calc
    _ ≤ A * (C * (n : ℝ) ^ (κ * ε) * Real.log (2 * (m : ℝ)) *
        (‖χ‖ + Real.sqrt (∫ x, ∑ j, (weightRadius m j i₀ ^ (1 / 2 : ℝ) *
          (u j).val x) ^ 2 ∂ν))) := mul_le_mul_of_nonneg_left hprimitive hA.le
    _ ≤ A * (C * (n : ℝ) ^ (κ * ε) * Real.log (2 * (m : ℝ)) *
        (‖χ‖ + Real.sqrt (∫ x, ∑ j, (w j * (u j).val x) ^ 2 ∂ν))) := by
      gcongr
    _ = _ := by ring

/-- Uniform local-exponent interface for the proof of Lemma 5.13, used in
the proof of Proposition 5.15. The reference cutoff is unchanged. -/
theorem global_energy_multiplier (s : Riesz1.RieszExponent)
    (κstar γstar : ℝ) (hκstar : 0 ≤ κstar) (hγstar : 0 ≤ γstar) (M₀ : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ Cstar : ℝ, 1 ≤ Cstar → ∀ βhi : ℝ, 0 ≤ βhi →
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
    ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (Q : ScalarFormData ν)
      (n m : ℕ+) (hm : 2 ≤ (m : ℕ)),
    2 ≤ (n : ℕ) → (n : ℕ) ≤ (m : ℕ) →
    (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
    let K := ⌊(n : ℝ) ^ ε⌋₊ ^ M₀
    1 ≤ K → 4 * K ≤ (m : ℕ) →
    ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M →
    ∀ β : ℝ, 0 ≤ β → β ≤ βhi →
    ∀ (χ : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _)
      (fun i => if i = i₀ then χ else 0) u →
    ∃ lam : Lp ℝ 2 ν,
      (∀ᵐ x ∂ν, lam x = gapMultiplierField m Q (fun x => β • M x)
        (fun i => if i = i₀ then χ else 0) u x) ∧
      WeightedWeakSolution Q (fun x => β • M x) ⊤
        (fun i => (if i = i₀ then χ else 0) + lam) u ∧
      (∀ᵐ x ∂ν, (m : ℝ) * lam x =
        β * (∑ i, ∑ j, (M x - (2 : ℝ) • rieszMatrix s m hm) i j * (u j).val x) - χ x) ∧
      (m : ℝ) * ‖lam‖ ≤ C * (n : ℝ) ^ (κ * ε) *
        (‖χ‖ + Real.sqrt (Real.log (2 * (m : ℝ))) *
          Real.sqrt (∑ i, (weightRadius m i i₀ ^ (1 / 2 : ℝ) * ‖(u i).val‖) ^ 2)) := by
  obtain ⟨κ, hκ, herr⟩ := global_error_differences s κstar γstar hκstar hγstar M₀
  refine ⟨κ, hκ, fun Cstar hCstar βhi hβhi => ?_⟩
  obtain ⟨Ce, hCe, herr⟩ := herr Cstar hCstar
  let D := Real.sqrt (2 * (1 + 1 / Real.log 2))
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  let C := 1 + βhi * Ce * D
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro ε hε Ω _ ν Q n m hm hn hnm hmn K hK hKm M hM β hβ hββhi χ i₀ u hu
  obtain ⟨a, B, _, _, _, _, he⟩ := herr ε hε n m hm hn hnm hmn hK hKm ν M hM
  have hsym : ∀ᵐ x ∂ν, ∀ i j, (β • M x) i j = (β • M x) j i := by
    filter_upwards [hM.2.1] with x hx
    intro i j
    simp only [Matrix.smul_apply, smul_eq_mul, hx.1 i j]
  obtain ⟨lam, hlam, hfull⟩ := DerivativeControl.restore_multiplier m Q (fun x => β • M x)
    (SchurRestriction.periodized_scaled_measurable β hM)
    (SchurRestriction.periodized_scaled_bounded β hM) hsym _ u hu
  refine ⟨lam, hlam, hfull,
    multiplier_reference_identity s m hm Q M β χ i₀ u hu.1.1 lam hlam, ?_⟩
  let P := (n : ℝ) ^ (κ * ε)
  have hP : 1 ≤ P := Real.one_le_rpow (by exact_mod_cast n.pos) (mul_nonneg hκ.le hε.le)
  have hcol : ∀ᵐ x ∂ν, ∀ j,
      ∑ i, |(M x - (2 : ℝ) • rieszMatrix s m hm) i j| ≤ Ce * P :=
    he.mono (fun _ hx => hx.2.2.2.2.1)
  have hb := multiplier_bound_of_column_sum s m hm Q M hM.1 (Ce * P)
    (by positivity) hcol β χ i₀ u hu.1.1 lam hlam
  rw [abs_of_nonneg hβ] at hb
  let Z := Real.sqrt (Real.log (2 * (m : ℝ))) *
    Real.sqrt (∑ i, (weightRadius m i i₀ ^ (1 / 2 : ℝ) * ‖(u i).val‖) ^ 2)
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hb' : (m : ℝ) * ‖lam‖ ≤ ‖χ‖ + βhi * Ce * D * P * Z := by
    calc
      _ ≤ ‖χ‖ + β * (Ce * P) * D * Z := by
        convert hb using 1
        dsimp [Z, D]
        ring
      _ = ‖χ‖ + β * (Ce * D * P * Z) := by ring
      _ ≤ ‖χ‖ + βhi * (Ce * D * P * Z) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hββhi (by positivity))
      _ = _ := by ring
  have hcoef : 0 ≤ βhi * Ce * D := by positivity
  calc
    _ ≤ ‖χ‖ + βhi * Ce * D * P * Z := hb'
    _ ≤ P * ‖χ‖ + βhi * Ce * D * P * Z := by
      apply add_le_add _ le_rfl
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hP (norm_nonneg χ)
    _ ≤ C * P * (‖χ‖ + Z) := by
      dsimp [C]
      nlinarith [mul_nonneg hcoef (mul_nonneg (show 0 ≤ P by positivity) (norm_nonneg χ)),
        mul_nonneg (show 0 ≤ P by positivity) hZ]

/-- Uniform local-exponent interface for Lemma 5.9, used in
the proof of Proposition 5.15. The reference cutoff is unchanged. -/
theorem elliptic_L2 (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (κstar γstar : ℝ) (hκstar : 0 < κstar) (_hγstar : 0 < γstar) (M₀ : ℕ+) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ εmin : ℝ, 0 < εmin →
    ∀ Cstar : ℝ, 1 ≤ Cstar → ∀ βlo : ℝ, 0 < βlo → ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, εmin ≤ ε →
    ∀ β : ℝ, βlo ≤ β →
    ∀ {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
      (n m : ℕ+) (hm : 2 ≤ (m : ℕ)),
    (n : ℕ) ≤ (m : ℕ) →
    (m : ℝ) ≤ 3 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
    ⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ) ≤ (m : ℕ) / 4 →
    ∀ M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm (⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ))
      Cstar κstar γstar ε M →
    ∀ Q : ScalarFormData ν, IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
    ∀ (i₀ : Fin (m : ℕ)) (χ : Lp ℝ 2 ν) (u : Fin (m : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents (Fin (m : ℕ)))
      (fun i => if i = i₀ then χ else 0) u →
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    let H := Matrix.of (fun a b : Fin (m : ℕ) => sampledRieszKernel sh m hm (b - a))
    let F := fun x => (∑ i, |(H *ᵥ (fun j => (u j).val x)) i| ^
      (1 - s.val / 2)⁻¹) ^ (1 - s.val / 2)
    let w₁ := fun j => 1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (1 / 2 : ℝ)
    let w₂ := fun j => 1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (3 / 2 - s.val)
    Integrable (fun x => ∑ j, (w₁ j * (u j).val x) ^ 2) ν ∧
    Integrable (fun x => ∑ j, (w₂ j * (u j).val x) ^ 2) ν ∧
    Integrable (fun x => F x ^ 2) ν ∧
      Real.sqrt (∫ x, F x ^ 2 ∂ν) ≤
        C * (n : ℝ) ^ (κ * ε) *
          (‖χ‖ + Real.sqrt (∫ x, ∑ j, (w₁ j * (u j).val x) ^ 2 ∂ν)) ^ s.val *
          (Real.sqrt (∫ x, ∑ j, (w₂ j * (u j).val x) ^ 2 ∂ν)) ^ (1 - s.val) := by
  obtain ⟨κp, hκp, hp⟩ := elliptic_primitive_angular_radius_uniform hz s κstar γstar hκstar M₀
  obtain ⟨Ci, hCi, hi⟩ := integrated_interpolation_angular hz s
  refine ⟨κp * s.val + 1, by nlinarith [s.property.1], fun εmin hεmin Cstar hCstar βlo hβlo => ?_⟩
  obtain ⟨Cp, hCp, hp⟩ := hp Cstar hCstar βlo hβlo
  obtain ⟨D, hD, hlog⟩ := log_absorption s hεmin
    (by linarith [s.property.1] : 0 < (3 + s.val) / 2)
  refine ⟨Ci * Cp ^ s.val * D, by positivity,
    fun ε hεlower β hβ {α} _ ν _ n m hm _hnm hmn _hK M hM Q hQ _hQc i₀ χ u hu => ?_⟩
  have hε : 0 < ε := hεmin.trans_le hεlower
  obtain ⟨hJ, hwr, hprimitive₀⟩ := hp ε hε β hβ ν n m hm M hM Q hQ χ i₀ u hu
  have hlog₀ : 0 ≤ Real.log (2 * (m : ℝ)) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ m := by exact_mod_cast m.pos
    linarith)
  let w₁ := fun j => 1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (1 / 2 : ℝ)
  have hw₁ := (CyclicFourierL2.weighted_integral_sq w₁ (fun j => (u j).val)).1
  have hwle (j : Fin (m : ℕ)) : weightRadius m j i₀ ^ (1 / 2 : ℝ) ≤ w₁ j := by
    dsimp only [w₁]
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    have hd : 0 ≤ (Riesz1.cyclicIndexDistance m j i₀ : ℝ) := Nat.cast_nonneg _
    have hs := Real.sq_sqrt hd
    change 1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ≤
      (1 + Real.sqrt (Riesz1.cyclicIndexDistance m j i₀ : ℝ)) ^ 2
    nlinarith [Real.sqrt_nonneg (Riesz1.cyclicIndexDistance m j i₀ : ℝ)]
  have hprimitive := hprimitive₀.trans (mul_le_mul_of_nonneg_left
    (add_le_add_right (Real.sqrt_le_sqrt (integral_mono hwr hw₁ (fun x => by
      apply Finset.sum_le_sum
      intro j _
      rw [mul_pow, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Real.rpow_nonneg (by unfold weightRadius; positivity) _)
          (hwle j) 2) (sq_nonneg _)))) ‖χ‖) (by positivity))
  have hsum : ∀ᵐ x ∂ν, ∑ i, (u i).val x = 0 := hu.1.1
  obtain ⟨hF, hinterp⟩ := hi ν m hm (fun j => (u j).val) hsum i₀
  let L := Real.log (2 * (m : ℝ))
  let X := Real.sqrt (∫ x, ∑ j,
    ((1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (3 / 2 - s.val)) * (u j).val x) ^ 2 ∂ν)
  let Z := ‖χ‖ + Real.sqrt (∫ x, ∑ j,
    ((1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (1 / 2 : ℝ)) * (u j).val x) ^ 2 ∂ν)
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast n.pos
  have hL : 0 < L := Real.log_pos (by
    have : (1 : ℝ) ≤ m := by exact_mod_cast m.pos
    linarith)
  have hX : 0 ≤ X := Real.sqrt_nonneg _
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hw₂ := (CyclicFourierL2.weighted_integral_sq
    (fun j => 1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (3 / 2 - s.val))
    (fun j => (u j).val)).1
  refine ⟨hw₁, hw₂, hF, ?_⟩
  have hpPow := Real.rpow_le_rpow (Real.sqrt_nonneg _) hprimitive s.property.1.le
  have hbound := hinterp.trans (mul_le_mul_of_nonneg_left hpPow
    (by positivity : 0 ≤ Ci * L ^ ((3 - s.val) / 2) * X ^ (1 - s.val)))
  have heq : Ci * L ^ ((3 - s.val) / 2) * X ^ (1 - s.val) *
      (Cp * (n : ℝ) ^ (κp * ε) * L * Z) ^ s.val =
      Ci * Cp ^ s.val * L ^ ((3 + s.val) / 2) *
        (n : ℝ) ^ (κp * s.val * ε) * Z ^ s.val * X ^ (1 - s.val) := by
    rw [Real.mul_rpow (by positivity : 0 ≤ Cp * (n : ℝ) ^ (κp * ε) * L) hZ,
      Real.mul_rpow (by positivity : 0 ≤ Cp * (n : ℝ) ^ (κp * ε)) hL.le,
      Real.mul_rpow hCp.le (Real.rpow_nonneg hn0.le _), ← Real.rpow_mul hn0.le]
    calc
      _ = Ci * Cp ^ s.val * (L ^ ((3 - s.val) / 2) * L ^ s.val) *
          (n : ℝ) ^ (κp * ε * s.val) * Z ^ s.val * X ^ (1 - s.val) := by ring
      _ = _ := by
        rw [← Real.rpow_add hL,
          show (3 - s.val) / 2 + s.val = (3 + s.val) / 2 by ring,
          show κp * ε * s.val = κp * s.val * ε by ring]
  have hlog' := hlog ε hεlower n m hmn
  calc
    _ ≤ Ci * L ^ ((3 - s.val) / 2) * X ^ (1 - s.val) *
        (Cp * (n : ℝ) ^ (κp * ε) * L * Z) ^ s.val := hbound
    _ = _ := heq
    _ ≤ Ci * Cp ^ s.val * (D * (n : ℝ) ^ ε) *
        (n : ℝ) ^ (κp * s.val * ε) * Z ^ s.val * X ^ (1 - s.val) := by
      gcongr
    _ = _ := by
      rw [show (κp * s.val + 1) * ε = ε + κp * s.val * ε by ring,
        Real.rpow_add hn0]
      ring

/-- Uniform local-exponent interface for Lemma 5.9, used in
the proof of Proposition 5.15. The reference cutoff is unchanged. -/
theorem elliptic_regularized (hzeta : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (κstar γstar : ℝ) (hκstar : 0 < κstar) (hγstar : 0 < γstar) (M₀ : ℕ+) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ εmin : ℝ, 0 < εmin →
    ∀ Cstar : ℝ, 1 ≤ Cstar → ∀ βlo : ℝ, 0 < βlo → ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, εmin ≤ ε →
    ∀ β : ℝ, βlo ≤ β →
    ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
      (n m : ℕ+) (hm : 2 ≤ (m : ℕ)),
    (n : ℕ) ≤ (m : ℕ) → (m : ℝ) ≤ 3 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
    ⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ) ≤ (m : ℕ) / 4 →
    ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm (⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ))
      Cstar κstar γstar ε M →
    ∀ Q : ScalarFormData ν, IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
    ∀ (i₀ : Fin (m : ℕ)) (χ : Lp ℝ 2 ν) (u : Fin (m : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _)
      (fun i => if i = i₀ then χ else 0) u →
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    let p := (1 - s.val / 2)⁻¹
    let V := fun x => (∑ i, |(rieszMatrix sh m hm *ᵥ
      (fun j => (u j).val x)) i| ^ p) ^ (1 / p)
    let Xρ := fun ρ => Real.sqrt (∑ i, (weightRadius m i i₀ ^ ρ * ‖(u i).val‖) ^ 2)
    Integrable (fun x => V x ^ 2) ν ∧
      Real.sqrt (∫ x, V x ^ 2 ∂ν) ≤ C * (n : ℝ) ^ (κ * ε) *
        (‖χ‖ + Xρ (1 / 2)) ^ s.val * Xρ (3 / 2 - s.val) ^ (1 - s.val) := by
  obtain ⟨κ, hκ, hb⟩ := elliptic_L2 hzeta s κstar γstar hκstar hγstar M₀
  refine ⟨κ, hκ, fun εmin hεmin Cstar hCstar βlo hβlo => ?_⟩
  obtain ⟨C, hC, hb⟩ := hb εmin hεmin Cstar hCstar βlo hβlo
  refine ⟨2 * C, by positivity, ?_⟩
  intro ε hεlower β hβ Ω _ ν _ n m hm hnm hmn hK M hM Q hQ hQc i₀ χ u hu sh p V Xρ
  have hε : 0 < ε := hεmin.trans_le hεlower
  obtain ⟨_, _, hi, he⟩ := hb ε hεlower β hβ ν n m hm hnm hmn hK M hM Q hQ hQc i₀ χ u hu
  have hp : 1 / p = 1 - s.val / 2 := by simp only [p, one_div, inv_inv]
  have hi' : Integrable (fun x => V x ^ 2) ν := by simpa only [V, hp, rieszMatrix] using hi
  refine ⟨hi', ?_⟩
  have h₁ := elliptic_weight_comparison m i₀ (1 / 2) (by norm_num) (fun j => (u j).val)
  have h₂ := elliptic_weight_comparison m i₀ (3 / 2 - s.val)
    (by linarith [s.property.2]) (fun j => (u j).val)
  have hsource : ‖χ‖ + Real.sqrt (∫ x, ∑ j,
      ((1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (1 / 2 : ℝ)) * (u j).val x) ^ 2 ∂ν) ≤
      2 * (‖χ‖ + Xρ (1 / 2)) := by linarith only [h₁, norm_nonneg χ]
  have hbase := Real.rpow_le_rpow (by positivity) hsource s.property.1.le
  have hweight := Real.rpow_le_rpow (by positivity) h₂ (by linarith [s.property.2] : 0 ≤ 1 - s.val)
  have hbound := he.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left hbase (by positivity)) hweight (by positivity) (by positivity))
  have heq : C * (n : ℝ) ^ (κ * ε) * (2 * (‖χ‖ + Xρ (1 / 2))) ^ s.val *
      (2 * Xρ (3 / 2 - s.val)) ^ (1 - s.val) =
      (2 * C) * (n : ℝ) ^ (κ * ε) *
        (‖χ‖ + Xρ (1 / 2)) ^ s.val * Xρ (3 / 2 - s.val) ^ (1 - s.val) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity),
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg _)]
    calc
      _ = (C * (n : ℝ) ^ (κ * ε) * (‖χ‖ + Xρ (1 / 2)) ^ s.val *
          Xρ (3 / 2 - s.val) ^ (1 - s.val)) * (2 ^ s.val * 2 ^ (1 - s.val)) := by ring
      _ = _ := by rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]; norm_num; ring
  rw [heq] at hbound
  simpa only [V, hp, rieszMatrix] using hbound

/-- Uniform local-exponent interface for the proof of Lemma 5.13, used in
the proof of Proposition 5.15. The reference cutoff is unchanged. -/
theorem global_energy_first (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ)
    (hκstar : 0 ≤ κstar) (hγstar : 0 ≤ γstar) (M₀ : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ εmin : ℝ, 0 < εmin →
    ∀ Cstar : ℝ, 1 ≤ Cstar →
    ∀ βlo : ℝ, 0 < βlo → ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, εmin ≤ ε →
    ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (Q : ScalarFormData ν),
    IsClosedScalarDirichletForm Q → ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ)),
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
    let Xρ := fun ρ => Real.sqrt (∑ i, (weightRadius m i i₀ ^ ρ * ‖(u i).val‖) ^ 2)
    Xρ (3 / 2 - s.val) ^ 2 ≤ C * (n : ℝ) ^ (κ * ε) *
      (Xρ (3 / 2 - s.val) * (‖χ‖ + Xρ (1 / 2) + Real.sqrt (∫ x, V x ^ 2 ∂ν)) +
        ∑ i, weightRadius m i i₀ ^ (2 * (1 - s.val / 2)) * Q.2 (u i) (u i)) := by
  obtain ⟨κe, hκe, herr⟩ := global_error_differences s κstar γstar hκstar hγstar M₀
  obtain ⟨κm, hκm, hmult⟩ := global_energy_multiplier s κstar γstar hκstar hγstar M₀
  obtain ⟨D, Cc, Cm, Cd, Cs, hD, hCc, hCm, hCd, hCs, hraw⟩ :=
    first_weighted_shifted_by_regions_internal hzeta s
  let r := 10 + 8 * D
  let k := κe + κm + 1
  have hr : 0 < r := by dsimp [r]; positivity
  have hk : 0 < k := by dsimp [k]; positivity
  refine ⟨k * r, mul_pos hk hr, fun εmin hεmin Cstar hCstar βlo hβlo βhi hβhi => ?_⟩
  obtain ⟨Ce, hCe, herr⟩ := herr Cstar hCstar
  obtain ⟨Cl, hCl, hmult⟩ := hmult Cstar hCstar βhi (hβlo.le.trans hβhi)
  obtain ⟨Clog, hClog, hlog⟩ := log_absorption s hεmin (by norm_num : (0 : ℝ) < 1)
  obtain ⟨Ca, hCa, habs⟩ := shifted_absorption_internal Cc Cm Cd Cs D βlo hCc hCm hCd hCs hD hβlo
  let A := Ce + Cl + Clog + 1
  have hA : 1 ≤ A := by dsimp [A]; linarith only [hCe, hCl, hClog]
  have hA0 : 0 < A := by linarith only [hA]
  refine ⟨Ca * A ^ r, by positivity, ?_⟩
  intro ε hεlower Ω _ ν Q hQ n m hm hn hnm hmn K hK hKm M hM β hβloβ hββhi χ i₀ u hu sh p V Xρ
  have hε : 0 < ε := hεmin.trans_le hεlower
  let R := (n : ℝ) ^ (k * ε)
  let T := A * R
  let L := Ce * (n : ℝ) ^ (κe * ε)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by positivity
  have hR : 1 ≤ R := Real.one_le_rpow hn1 (mul_nonneg hk.le hε.le)
  have hT : 1 ≤ T := one_le_mul_of_one_le_of_one_le hA hR
  have hpow (q : ℝ) (hq : q ≤ k) : (n : ℝ) ^ (q * ε) ≤ R :=
    Real.rpow_le_rpow_of_exponent_le hn1 (mul_le_mul_of_nonneg_right hq hε.le)
  have heT : L ≤ T := by
    apply mul_le_mul
    · dsimp [A]; linarith only [hCl, hClog]
    · exact hpow κe (by dsimp [k]; linarith only [hκm])
    · positivity
    · exact hA0.le
  have hlT : Cl * (n : ℝ) ^ (κm * ε) ≤ T := by
    apply mul_le_mul
    · dsimp [A]; linarith only [hCe, hClog]
    · exact hpow κm (by dsimp [k]; linarith only [hκe])
    · positivity
    · exact hA0.le
  have hlogT : Real.log (2 * (m : ℝ)) ≤ T := by
    have hh := hlog ε hεlower n m (by linarith only [hmn, Real.rpow_nonneg hn0.le (1 / 2 + 1 / s.val)])
    rw [Real.rpow_one] at hh
    apply hh.trans
    apply mul_le_mul
    · dsimp [A]; linarith only [hCe, hCl]
    · simpa only [one_mul] using hpow 1 (by dsimp [k]; linarith only [hκe, hκm])
    · positivity
    · exact hA0.le
  obtain ⟨a, B, ha, ha1, hB, hab, he⟩ := herr ε hε n m hm hn hnm hmn hK hKm ν M hM
  obtain ⟨lam, _, hfull, _, hlam⟩ := hmult ε hε ν Q n m hm hn hnm hmn hK hKm M hM β
    (hβlo.le.trans hβloβ) hββhi χ i₀ u hu
  have hsym : ∀ᵐ x ∂ν, (M x).IsSymm := by
    filter_upwards [hM.2.1] with x hx
    ext i j
    exact hx.1 j i
  have hcoef : ∀ᵐ x ∂ν, (M x).IsSymm ∧ a • 1 ≤ M x ∧
      ‖M x - (2 : ℝ) • rieszMatrix s m hm‖ ≤ B := by
    filter_upwards [hsym, he] with x hx he
    exact ⟨hx, he.2.2.2.2.2.1, he.2.2.2.2.2.2⟩
  have herror : ∀ᵐ x ∂ν,
      let E := M x - (2 : ℝ) • rieszMatrix s m hm
      (∀ i j, |E i j| ≤ L * weightRadius m i j ^ (-(1 + s.val / 2))) ∧
      (∀ i j, |E i j - E (i + 1) j| + |E i j - E i (j + 1)| ≤
        L * weightRadius m i j ^ (-(1 + s.val))) ∧
      (∀ i j, |(E i j - E (i + 1) j) - (E i (j + 1) - E (i + 1) (j + 1))| ≤
        L * weightRadius m i j ^ (-(2 + s.val))) ∧
      (∀ j, ∑ i, |E i j| ≤ L) := by
    filter_upwards [he] with x hx
    simpa only [L, weightRadius, show -(1 + s.val / 2) = -1 - s.val / 2 by ring,
      show -(1 + s.val) = -1 - s.val by ring, show -(2 + s.val) = -2 - s.val by ring]
      using ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.2.1⟩
  have hβ : 0 < β := hβlo.trans_le hβloβ
  have hraw' := hraw ν Q hQ m hm a ha ha1 B L hB (by dsimp [L]; positivity) M hM.1
    (SchurRestriction.periodized_scaled_bounded 1 hM |>.imp (fun b hb => by simpa using hb))
    hcoef herror β hβ χ lam i₀ u hfull hu.1.1
  have hlog0 : 0 ≤ Real.log (2 * (m : ℝ)) := by
    apply Real.log_nonneg
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hmultT := hlam.trans (mul_le_mul_of_nonneg_right hlT (by positivity :
    0 ≤ ‖χ‖ + Real.sqrt (Real.log (2 * (m : ℝ))) * Xρ (1 / 2)))
  have hh := habs T a B L β (Real.log (2 * (m : ℝ))) ‖χ‖
    (Xρ (3 / 2 - s.val)) (Xρ (1 / 2)) (Real.sqrt (∫ x, V x ^ 2 ∂ν))
    (∑ i, weightRadius m i i₀ ^ (2 * (1 - s.val / 2)) * Q.2 (u i) (u i))
    ((m : ℝ) * ‖lam‖) hT ha ha1 hB (by dsimp [L]; positivity) heT
    (hab.trans heT) hβloβ hlog0 hlogT (norm_nonneg _) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (Finset.sum_nonneg (fun i _ => mul_nonneg (Real.rpow_nonneg
      (by linarith [one_le_weightRadius m i i₀]) _) (hQ.2.2.1 _))) hmultT
    (by simpa only [mul_assoc] using hraw')
  have hcoef : Ca * T ^ (10 + 8 * D) = (Ca * A ^ r) * (n : ℝ) ^ ((k * r) * ε) := by
    change Ca * T ^ r = _
    dsimp only [T, R]
    rw [Real.mul_rpow hA0.le (by positivity), ← Real.rpow_mul hn0.le,
      show (k * ε) * r = (k * r) * ε by ring]
    ring
  rw [hcoef] at hh
  exact hh

/-- Uniform local-exponent interface for the proof of Lemma 5.13, used in
the proof of Proposition 5.15. The reference cutoff is unchanged. -/
theorem global_energy_second_L2 (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ)
    (hκstar : 0 < κstar) (hγstar : 0 ≤ γstar) (M₀ : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ εmin : ℝ, 0 < εmin →
    ∀ Cstar : ℝ, 1 ≤ Cstar →
    ∀ βlo : ℝ, 0 < βlo → ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, εmin ≤ ε →
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
  refine ⟨κd + κm + 1, by positivity, fun εmin hεmin Cstar hCstar βlo hβlo βhi hβhi => ?_⟩
  obtain ⟨Cm, hCm, hmult⟩ := hmult Cstar hCstar βhi (hβlo.le.trans hβhi)
  obtain ⟨Cd, hCd, hdiff⟩ := hdiff Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨D, hD, hlog⟩ := log_absorption s hεmin (by norm_num : (0 : ℝ) < 1 / 2)
  let C₀ := (1 + Cm) * (1 + D)
  refine ⟨Cd * C₀, by dsimp [C₀]; positivity, ?_⟩
  intro ε hεlower Ω _ ν _ Q hQ n m hm hn hnm hmn K hK hKm M hM β hβloβ hββhi χ i₀ u hu
    sh p V Xρ
  have hε : 0 < ε := hεmin.trans_le hεlower
  obtain ⟨lam, hlam, hfull, _, hmlam⟩ :=
    hmult ε hε ν Q n m hm hn hnm hmn hK hKm M hM β (hβlo.le.trans hβloβ) hββhi χ i₀ u hu
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
    exact hlog ε hεlower n m (by linarith only [hmn, Real.rpow_nonneg hn0.le (1 / 2 + 1 / s.val)])
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

/-- Uniform local-exponent interface for Lemma 5.13, used in
the proof of Proposition 5.15 and the base of Proposition 5.15.
The exact eta and four Young absorptions of Lemma 5.13, Step 5, give
polynomial closure constants before `εmin` is fixed. Logarithms are then
absorbed uniformly for every `ε ≥ εmin`. The reference cutoff is unchanged. -/
theorem global_decay_bounds (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ)
    (hκstar : 0 < κstar) (hγstar : 0 < γstar) (M₀ : ℕ+) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ εmin : ℝ, 0 < εmin →
    ∀ Cstar : ℝ, 1 ≤ Cstar →
    ∀ βlo : ℝ, 0 < βlo → ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, εmin ≤ ε →
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
  refine ⟨k * (r + 3), by positivity, fun εmin hεmin Cstar hCstar βlo hβlo βhi hβhi => ?_⟩
  obtain ⟨C₁, hC₁, h₁⟩ := h₁ εmin hεmin Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨C₂, hC₂, h₂⟩ := h₂ εmin hεmin Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Ce, hCe, he⟩ := he εmin hεmin Cstar hCstar βlo hβlo
  obtain ⟨Cm, hCm, hmult⟩ := hmult Cstar hCstar βhi (hβlo.le.trans hβhi)
  obtain ⟨Cl, hCl, hlog⟩ := log_absorption s hεmin (by norm_num : (0 : ℝ) < 1 / 2)
  let Cu := 1 + 2 * βlo⁻¹ * Cstar
  have hCu : 0 < Cu := by dsimp [Cu]; positivity
  let A := C₁ + C₂ + Ce + Cm + Cl + Cu + 1
  have hA : 1 ≤ A := by dsimp [A]; linarith only [hC₁, hC₂, hCe, hCm, hCl, hCu]
  refine ⟨8 * D * A ^ (r + 3), by positivity, ?_⟩
  intro ε hεlower Ω _ ν _ Q hQ hQc n m hm hn hnm hmn K hK hKm M hM β hβloβ hββhi χ i₀ u hu
  have hε : 0 < ε := hεmin.trans_le hεlower
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
    (h₁ ε hεlower ν Q hQ n m hm hn hnm hmn hK hKm M hM β hβloβ hββhi χ i₀ u hu).trans
      (mul_le_mul_of_nonneg_right hc₁ (by positivity))
  obtain ⟨_, _, _, _, hy⟩ := h₂ ε hεlower ν Q hQ n m hm hn hnm hmn hK hKm M hM β hβloβ hββhi χ i₀ u hu
  have he₂ : ∀ η : ℝ, 0 < η → η < 1 / 4 →
      Y ≤ T * (‖χ‖ ^ 2 + X * (η ^ (3 - s.val) * X + η⁻¹ * P + ‖χ‖ + Z)) := by
    intro η hη hη'
    exact (hy η hη hη').trans (mul_le_mul_of_nonneg_right hc₂ (by positivity))
  have hmn' : (m : ℝ) ≤ 3 * (n : ℝ) ^ (1 / 2 + 1 / s.val) :=
    hmn.trans (by nlinarith only [Real.rpow_nonneg hn0.le (1 / 2 + 1 / s.val)])
  obtain ⟨_, hp⟩ := he ε hεlower β hβloβ ν n m hm hnm hmn' (by dsimp [K] at hKm; omega)
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
  obtain ⟨lam, hlam, hfull, _, hmlam⟩ := hmult ε hε ν Q n m hm hn hnm hmn hK hKm M hM β
    (hβlo.le.trans hβloβ) hββhi χ i₀ u hu
  have hJ : (m : ℝ) * ‖lam‖ ≤ T * (‖χ‖ + Real.sqrt (Real.log (2 * (m : ℝ))) * Z) :=
    hmlam.trans (mul_le_mul_of_nonneg_right hcm (by positivity))
  have hL : Real.sqrt (Real.log (2 * (m : ℝ))) ≤ T := by
    rw [Real.sqrt_eq_rpow]
    exact (hlog ε hεlower n m hmn').trans (by simpa only [one_mul] using hcl)
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

/-- Uniform local-exponent interface for Lemma 5.13, used in
the proof of Proposition 5.15. The reference cutoff is unchanged. -/
theorem global_decay (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ)
    (hκstar : 0 < κstar) (hγstar : 0 < γstar) (M₀ : ℕ+) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ εmin : ℝ, 0 < εmin →
    ∀ Cstar : ℝ, 1 ≤ Cstar →
    ∀ βlo : ℝ, 0 < βlo → ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, εmin ≤ ε →
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
  refine ⟨κ, hκ, fun εmin hεmin Cstar hCstar βlo hβlo βhi hβhi => ?_⟩
  obtain ⟨C, hC, hb⟩ := hb εmin hεmin Cstar hCstar βlo hβlo βhi hβhi
  refine ⟨C, hC, ?_⟩
  intro ε hεlower Ω _ ν _ Q hQ hQc n m hm hn hnm hmn K hK hKm M hM β hβloβ hββhi χ i₀
  have hε : 0 < ε := hεmin.trans_le hεlower
  let a := Cstar⁻¹ * (n : ℝ) ^ (-κstar * ε)
  have ha : 0 < a := SchurRestriction.periodized_mass_pos hCstar
  have hl : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
      ∀ z : Fin (m : ℕ) → ℝ,
        a * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j :=
    hM.2.1.mono (fun _ hx => ⟨hx.1, hx.2.2.1⟩)
  obtain ⟨u, hu, huniq⟩ := (AbstractEquation.existence_energy Q hQ β
    (hβlo.trans_le hβloβ) M hM.1 a ha hl (zeroSumComponents _)
    (fun i => if i = i₀ then χ else 0)).1
  exact ⟨u, ⟨hu, hb ε hεlower ν Q hQ hQc n m hm hn hnm hmn hK hKm M hM β hβloβ hββhi χ i₀ u hu⟩,
    fun v hv => huniq v hv.1⟩

/-- Uniform local-exponent interface for the proof of Lemma 5.14, used in
the proof of Proposition 5.15. The reference cutoff is unchanged. -/
theorem global_bis_mean (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ)
    (hκstar : 0 < κstar) (hγstar : 0 < γstar) (M₀ : ℕ+) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ εmin : ℝ, 0 < εmin →
    ∀ Cstar : ℝ, 1 ≤ Cstar →
    ∀ βlo : ℝ, 0 < βlo → ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, εmin ≤ ε →
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
    let ell := 2 * ∑ k, sampledRieszKernel s m hm k
    let H := (2 : ℝ) • rieszMatrix s m hm
    let A := C * (n : ℝ) ^ (κ * ε)
    ∃! u : Fin (m : ℕ) → Q.1,
      WeightedWeakSolution Q (fun x => β • M x) ⊤
        (fun i => if i = i₀ then χ else 0) u ∧
      ∃ (v : Fin (m : ℕ) → Q.1) (lam : Lp ℝ 2 ν) (f : Q.1),
        WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _)
          (fun i => if i = i₀ then χ else 0) v ∧
        (∀ᵐ x ∂ν, lam x = gapMultiplierField m Q (fun x => β • M x)
          (fun i => if i = i₀ then χ else 0) v x) ∧
        WeightedWeakSolution Q (fun x => β • M x) ⊤
          (fun i => (if i = i₀ then χ else 0) + lam) v ∧
        (∀ z : Q.1, Q.2 f z + (β * ell) * inner ℝ f.val z.val = inner ℝ (-lam) z.val) ∧
        Real.sqrt (∑ i, (weightRadius m i i₀ ^ (3 / 2 - s.val) * ‖(v i).val‖) ^ 2) +
          Real.sqrt (∑ i, weightRadius m i i₀ ^ (2 * (1 - s.val / 2)) * Q.2 (v i) (v i)) ≤
            A * ‖χ‖ ∧
        (m : ℝ) * ‖lam‖ ≤ A * ‖χ‖ ∧
        ‖f.val‖ ≤ A * (m : ℝ) ^ (-(2 - s.val)) * ‖χ‖ ∧
        Real.sqrt (Q.2 f f) ≤ A * (m : ℝ) ^ (-(3 - s.val) / 2) * ‖χ‖ ∧
        WeightedWeakSolution Q (fun x => β • M x) ⊤ (fun _ => -lam) (fun i => u i - v i) ∧
        (∃ g : Fin (m : ℕ) → Lp ℝ 2 ν,
          (∀ i, ∀ᵐ x ∂ν, g i x = -β * f.val x * ∑ j, (M x - H) i j) ∧
          WeightedWeakSolution Q (fun x => β • M x) ⊤ g (fun i => u i - v i - f)) ∧
        Real.sqrt (∑ i, ‖(u i - v i - f).val‖ ^ 2) +
          Real.sqrt (∑ i, Q.2 (u i - v i - f) (u i - v i - f)) ≤
            A * (m : ℝ) ^ (-(3 / 2 - s.val)) * ‖χ‖ ∧
        Real.sqrt (∑ i, ‖(u i - v i).val‖ ^ 2) ≤
          A * (m : ℝ) ^ (-(3 / 2 - s.val)) * ‖χ‖ ∧
        Real.sqrt (∑ i, Q.2 (u i - v i) (u i - v i)) ≤
          A * (m : ℝ) ^ (-(1 - s.val / 2)) * ‖χ‖ := by
  obtain ⟨κv, hκv, hv⟩ := global_decay hzeta s κstar γstar hκstar hγstar M₀
  obtain ⟨κe, hκe, he⟩ := global_error_differences s κstar γstar hκstar.le hγstar.le M₀
  obtain ⟨c, Cmass, hc, _, hmass⟩ := global_reference_mass_bounds s
  let k := κv + κe + κstar
  have hk : 0 < k := by dsimp [k]; positivity
  refine ⟨4 * k, by positivity, fun εmin hεmin Cstar hCstar βlo hβlo βhi hβhi => ?_⟩
  obtain ⟨Cv, hCv, hv⟩ := hv εmin hεmin Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Ce, hCe, he⟩ := he Cstar hCstar
  let R := (βlo * c)⁻¹
  let D := 2 + Cv + βhi * Ce + 2 * βlo⁻¹ * Cstar + R + Real.sqrt R
  have hβhi0 := hβlo.trans_le hβhi
  have hR : 0 < R := by dsimp [R]; positivity
  have hβCe : 0 ≤ βhi * Ce := mul_nonneg hβhi0.le (by linarith only [hCe])
  have hiC : 0 ≤ 2 * βlo⁻¹ * Cstar := by positivity
  have hD : 1 ≤ D := by
    dsimp only [D]
    linarith only [hCv, hβCe, hiC, hR, Real.sqrt_nonneg R]
  refine ⟨4 * D ^ 4, by positivity, ?_⟩
  intro ε hεlower Ω _ ν _ Q hQ hQc n m hm hn hnm hmn K hK hKm M hM β hβloβ hββhi χ i₀ ell H A
  have hε : 0 < ε := hεmin.trans_le hεlower
  let T := D * (n : ℝ) ^ (k * ε)
  let a := Cstar⁻¹ * (n : ℝ) ^ (-κstar * ε)
  have ha : 0 < a := SchurRestriction.periodized_mass_pos hCstar
  have hβ : 0 < β := hβlo.trans_le hβloβ
  have hm0 : (0 : ℝ) < m := by positivity
  obtain ⟨hT, hAT, hCvT, hCeT, hRT, hRsT, henergyT, hTA, hT2A, hT4A⟩ :=
    loss_bounds_internal n ε κv κe κstar Cv Ce Cstar βlo βhi β c
      hε hκv hκe hκstar hCv hCe hCstar hβlo hβhi hβloβ hc
  have hAT' : A = 4 * T ^ 4 := hAT
  have hl : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
      ∀ z : Fin (m : ℕ) → ℝ,
        a * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j :=
    hM.2.1.mono (fun _ hx => ⟨hx.1, hx.2.2.1⟩)
  obtain ⟨u, hu, huniq⟩ := (AbstractEquation.existence_energy Q hQ β hβ M hM.1 a ha hl ⊤
    (fun i => if i = i₀ then χ else 0)).1
  obtain ⟨v, ⟨hvc, lam, hlam, hvfull, hvest, hlamest, _⟩, _⟩ :=
    hv ε hεlower ν Q hQ hQc n m hm hn hnm hmn hK hKm M hM β hβloβ hββhi χ i₀
  have hlamT : ‖lam‖ ≤ T * (m : ℝ)⁻¹ * ‖χ‖ := hlamest.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCvT (by positivity)) (norm_nonneg χ))
  have hvT : Real.sqrt (∑ i, (weightRadius m i i₀ ^ (3 / 2 - s.val) * ‖(v i).val‖) ^ 2) +
      Real.sqrt (∑ i, weightRadius m i i₀ ^ (2 * (1 - s.val / 2)) * Q.2 (v i) (v i)) ≤
        T * ‖χ‖ := hvest.trans (mul_le_mul_of_nonneg_right hCvT (norm_nonneg χ))
  have hell : c * (m : ℝ) ^ (1 - s.val) ≤ ell := by
    have hh := (hmass m hm i₀).1
    simpa only [ell, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, rieszMatrix_row_sum] using hh
  obtain ⟨ae, B, _, _, _, _, heae⟩ := he ε hε n m hm hn hnm hmn hK hKm ν M hM
  let Be := Ce * (n : ℝ) ^ (κe * ε)
  have hBe : 0 ≤ Be := by dsimp [Be]; positivity
  have hrow : ∀ᵐ x ∂ν, ∀ i, ∑ j, |(M x - H) i j| ≤ Be :=
    heae.mono (fun _ hx => hx.2.2.2.1)
  have hH (i) : ∑ j, H i j = ell := by
    simp only [H, ell, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, rieszMatrix_row_sum]
  have hβBe : β * Be ≤ T := by
    have hb : β * Be ≤ βhi * Be := mul_le_mul_of_nonneg_right hββhi hBe
    apply hb.trans
    calc
      βhi * Be = βhi * Ce * (n : ℝ) ^ (κe * ε) := by dsimp only [Be]; ring
      _ ≤ T := hCeT
  obtain ⟨f, g, hfeq, hfT, hfgT, hg, hgeq, hrT, hwT, hwgT⟩ :=
    correction_bounds_internal s m Q hQ M hM.1 (SchurRestriction.periodized_bounded hM)
      β a hβ ha hl H ell c βlo T Be hH hc hβlo hβloβ hell hT hRT hRsT henergyT hBe
      hrow hβBe χ lam i₀ u v hu hvfull hlamT
  have hw : WeightedWeakSolution Q (fun x => β • M x) ⊤ (fun _ => -lam)
      (fun i => u i - v i) := by
    have hh := weak_sub_internal Q _ (SchurRestriction.periodized_scaled_measurable β hM)
      (SchurRestriction.periodized_scaled_bounded β hM) _ _ u v hu hvfull
    convert hh using 1
    funext i
    abel
  refine ⟨u, ⟨hu, v, lam, f, hvc, hlam, hvfull, hfeq,
    hvT.trans (mul_le_mul_of_nonneg_right hTA (norm_nonneg χ)), ?_, ?_, ?_,
    hw, ⟨g, hg, hgeq⟩, ?_, ?_, ?_⟩, fun z hz => huniq z hz.1⟩
  · have hh := mul_le_mul_of_nonneg_left hlamT hm0.le
    have hid : (m : ℝ) * (T * (m : ℝ)⁻¹ * ‖χ‖) = T * ‖χ‖ := by field_simp
    rw [hid] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hTA (norm_nonneg χ))
  · exact hfT.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hT2A (by positivity)) (norm_nonneg χ))
  · exact hfgT.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hT2A (by positivity)) (norm_nonneg χ))
  · exact hrT.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hT4A (by positivity)) (norm_nonneg χ))
  · rw [hAT']
    exact hwT
  · rw [hAT']
    exact hwgT

/-- Uniform local-exponent interface for Lemma 5.14, used in
the proof of Proposition 5.15. The reference cutoff is unchanged. -/
theorem global_bis (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ)
    (hκstar : 0 < κstar) (hγstar : 0 < γstar) (M₀ : ℕ+) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ εmin : ℝ, 0 < εmin →
    ∀ Cstar : ℝ, 1 ≤ Cstar →
    ∀ βlo : ℝ, 0 < βlo → ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, εmin ≤ ε →
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
      WeightedWeakSolution Q (fun x => β • M x) ⊤
        (fun i => if i = i₀ then χ else 0) u ∧
      Real.sqrt (∑ i, (weightRadius m i i₀ ^ (3 / 2 - s.val) * ‖(u i).val‖) ^ 2) +
        Real.sqrt (∑ i, weightRadius m i i₀ ^ (2 * (1 - s.val / 2)) * Q.2 (u i) (u i)) ≤
          C * (n : ℝ) ^ (κ * ε) * ‖χ‖ := by
  obtain ⟨κ, hκ, hmean⟩ := global_bis_mean hzeta s κstar γstar hκstar hγstar M₀
  refine ⟨κ, hκ, fun εmin hεmin Cstar hCstar βlo hβlo βhi hβhi => ?_⟩
  obtain ⟨C, hC, hmean⟩ := hmean εmin hεmin Cstar hCstar βlo hβlo βhi hβhi
  refine ⟨6 * C, by positivity, ?_⟩
  intro ε hεlower Ω _ ν _ Q hQ hQc n m hm hn hnm hmn K hK hKm M hM β hβloβ hββhi χ i₀
  have hε : 0 < ε := hεmin.trans_le hεlower
  obtain ⟨u, ⟨hu, v, lam, f, _, _, _, _, hvEst, _, _, _, _, _, _, hwEst, hwgEst⟩, _⟩ :=
    hmean ε hεlower ν Q hQ hQc n m hm hn hnm hmn hK hKm M hM β hβloβ hββhi χ i₀
  let A := C * (n : ℝ) ^ (κ * ε)
  have hm0 : (0 : ℝ) < m := by positivity
  have hα : 0 ≤ 3 / 2 - s.val := by linarith only [s.property.2]
  have hb : 0 ≤ 1 - s.val / 2 := by linarith only [s.property.2]
  have hvalue := (weight_bound_internal m hm i₀ Q hQ _ hα (fun i => u i - v i)).1
  have hgrad := (weight_bound_internal m hm i₀ Q hQ _ hb (fun i => u i - v i)).2
  have hcancel (ρ : ℝ) : (m : ℝ) ^ ρ * (A * (m : ℝ) ^ (-ρ) * ‖χ‖) = A * ‖χ‖ := by
    calc
      _ = A * ((m : ℝ) ^ ρ * (m : ℝ) ^ (-ρ)) * ‖χ‖ := by ring
      _ = _ := by rw [← Real.rpow_add hm0, add_neg_cancel, Real.rpow_zero, mul_one]
  have hwv : Real.sqrt (∑ i, (weightRadius m i i₀ ^ (3 / 2 - s.val) * ‖(u i - v i).val‖) ^ 2) ≤
      A * ‖χ‖ := by
    have hh := mul_le_mul_of_nonneg_left hwEst (by positivity : 0 ≤ (m : ℝ) ^ (3 / 2 - s.val))
    exact hvalue.trans (hh.trans_eq (hcancel _))
  have hwg : Real.sqrt (∑ i, weightRadius m i i₀ ^ (2 * (1 - s.val / 2)) *
      Q.2 (u i - v i) (u i - v i)) ≤ A * ‖χ‖ := by
    have hh := mul_le_mul_of_nonneg_left hwgEst (by positivity : 0 ≤ (m : ℝ) ^ (1 - s.val / 2))
    exact hgrad.trans (hh.trans_eq (hcancel _))
  have ht := weighted_triangle_internal Q hQ
    (fun i => weightRadius m i i₀ ^ (3 / 2 - s.val))
    (fun i => weightRadius m i i₀ ^ (2 * (1 - s.val / 2)))
    (fun i => Real.rpow_nonneg (by linarith only [one_le_weightRadius m i i₀]) _)
    v (fun i => u i - v i)
  have hadd (i) : v i + (u i - v i) = u i := by abel
  simp only [hadd] at ht
  have hfinal : Real.sqrt (∑ i, (weightRadius m i i₀ ^ (3 / 2 - s.val) * ‖(u i).val‖) ^ 2) +
      Real.sqrt (∑ i, weightRadius m i i₀ ^ (2 * (1 - s.val / 2)) * Q.2 (u i) (u i)) ≤
        (6 * C) * (n : ℝ) ^ (κ * ε) * ‖χ‖ := by
    have hh : Real.sqrt (∑ i, (weightRadius m i i₀ ^ (3 / 2 - s.val) * ‖(u i).val‖) ^ 2) +
        Real.sqrt (∑ i, weightRadius m i i₀ ^ (2 * (1 - s.val / 2)) * Q.2 (u i) (u i)) ≤
          6 * A * ‖χ‖ := by
      nlinarith only [ht.1, ht.2, hvEst, hwv, hwg]
    convert hh using 1
    dsimp only [A]
    ring
  have hl : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
      ∀ z : Fin (m : ℕ) → ℝ,
        (Cstar⁻¹ * (n : ℝ) ^ (-κstar * ε)) * (∑ i, z i ^ 2) ≤
          ∑ i, ∑ j, z i * M x i j * z j :=
    hM.2.1.mono (fun _ hx => ⟨hx.1, hx.2.2.1⟩)
  have huniq := (AbstractEquation.existence_energy Q hQ β (hβlo.trans_le hβloβ)
    M hM.1 _ (SchurRestriction.periodized_mass_pos hCstar) hl ⊤
    (fun i => if i = i₀ then χ else 0)).1
  exact ⟨u, ⟨hu, hfinal⟩, fun z hz => huniq.unique hz.1 hu⟩

/-- See the proof of Proposition 5.15 in the paper: the local exponent has a
positive lower bound depending only on the original exponent and s. All powers
of the local loss, including the integer reference cutoff, agree exactly with
the parent loss. This also covers the capped period branch. -/
theorem local_loss_parameters (s : Riesz1.RieszExponent) (n n₀ m : ℕ+)
    (hn : 2 ≤ (n : ℕ)) (hn₀ : 2 ≤ (n₀ : ℕ))
    (hn₀m : (n₀ : ℕ) ≤ (m : ℕ))
    (hmn : (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val))
    (ε : ℝ) (hε : 0 < ε) :
    let ε₀ := ε * Real.log n / Real.log n₀
    0 < ε₀ ∧ ε / (3 / 2 + 1 / s.val) ≤ ε₀ ∧
      (∀ κ : ℝ, (n₀ : ℝ) ^ (κ * ε₀) = (n : ℝ) ^ (κ * ε)) ∧
      (∀ M₀ : ℕ, ⌊(n₀ : ℝ) ^ ε₀⌋₊ ^ M₀ = ⌊(n : ℝ) ^ ε⌋₊ ^ M₀) := by
  let a := 1 / 2 + 1 / s.val
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hn₀1 : (1 : ℝ) < n₀ := by exact_mod_cast hn₀
  have hln : 0 < Real.log n := Real.log_pos hn1
  have hln₀ : 0 < Real.log n₀ := Real.log_pos hn₀1
  have hs0 := s.property.1
  have ha : 0 < a := by dsimp [a]; positivity
  have hsize : (n₀ : ℝ) ≤ 2 * (n : ℝ) ^ a :=
    (by exact_mod_cast hn₀m : (n₀ : ℝ) ≤ m).trans hmn
  have hlogsize : Real.log n₀ ≤ (a + 1) * Real.log n := by
    have hl := Real.log_le_log (by positivity : (0 : ℝ) < n₀) hsize
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos (by positivity) _).ne',
      Real.log_rpow (by positivity)] at hl
    have hlog2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    linarith
  dsimp only
  refine ⟨div_pos (mul_pos hε hln) hln₀, ?_, ?_, ?_⟩
  · have ha1 : 0 < a + 1 := by linarith
    have hh := mul_le_mul_of_nonneg_left hlogsize hε.le
    apply (div_le_div_iff₀ (show 0 < 3 / 2 + 1 / s.val by dsimp [a] at ha; linarith) hln₀).mpr
    dsimp only [a] at hh
    nlinarith only [hh]
  · intro κ
    apply Real.log_injOn_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.rpow_pos_of_pos (by positivity) _)
    rw [Real.log_rpow (by positivity), Real.log_rpow (by positivity)]
    field_simp
  · intro M₀
    have he : (n₀ : ℝ) ^ (ε * Real.log n / Real.log n₀) = (n : ℝ) ^ ε := by
      apply Real.log_injOn_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.rpow_pos_of_pos (by positivity) _)
      rw [Real.log_rpow (by positivity), Real.log_rpow (by positivity)]
      field_simp
    rw [he]

/-- See the proof of Proposition 5.15 in the paper: instantiate the exact
loss identities on the actual window, without a new geometric hypothesis. -/
theorem window_loss_parameters (s : Riesz1.RieszExponent) (n m : ℕ+)
    (hn : 2 ≤ (n : ℕ))
    (hmn : (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val))
    (j i₀ : Fin (m : ℕ)) (hR : 16 ≤ Riesz1.cyclicIndexDistance m j i₀)
    (ε : ℝ) (hε : 0 < ε) :
    let n₀ := windowSize m j i₀
    let ε₀ := ε * Real.log n / Real.log n₀
    0 < ε₀ ∧ ε / (3 / 2 + 1 / s.val) ≤ ε₀ ∧
      (∀ κ : ℝ, (n₀ : ℝ) ^ (κ * ε₀) = (n : ℝ) ^ (κ * ε)) ∧
      (∀ M₀ : ℕ, ⌊(n₀ : ℝ) ^ ε₀⌋₊ ^ M₀ = ⌊(n : ℝ) ^ ε⌋₊ ^ M₀) := by
  have hw := window_size_bounds m j i₀ hR
  exact local_loss_parameters s n (windowSize m j i₀) m hn
    (by omega) (by omega) hmn ε hε

/-- See the proof of Proposition 5.15 in the paper: the component period
satisfies the size bound needed by every uniform analytic interface. -/
theorem windowPeriod_analytic_upper (s : Riesz1.RieszExponent) (m : ℕ+)
    (j i₀ : Fin (m : ℕ)) :
    (windowPeriod s m j i₀ : ℝ) ≤
      2 * (windowSize m j i₀ : ℝ) ^ (1 / 2 + 1 / s.val) := by
  let n₀ := windowSize m j i₀
  let a := 1 / 2 + 1 / s.val
  have hn₀ : (1 : ℝ) ≤ n₀ := by exact_mod_cast n₀.pos
  have hs : 1 ≤ 1 / s.val := (one_le_div s.property.1).mpr s.property.2.le
  have ha : 1 ≤ a := by dsimp [a]; linarith
  have hp : 1 ≤ (n₀ : ℝ) ^ a := Real.one_le_rpow hn₀ (by linarith)
  have hn : (n₀ : ℝ) ≤ (n₀ : ℝ) ^ a := Real.self_le_rpow_of_one_le hn₀ ha
  have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n₀) a)
  have hm : (windowPeriod s m j i₀ : ℕ) ≤
      max (2 * (n₀ : ℕ)) ⌈(n₀ : ℝ) ^ a⌉₊ := min_le_right _ _
  have hm' : (windowPeriod s m j i₀ : ℝ) ≤
      max (2 * (n₀ : ℝ)) (⌈(n₀ : ℝ) ^ a⌉₊ : ℝ) := by exact_mod_cast hm
  exact hm'.trans (max_le (by linarith) (by linarith))

end Riesz2.LocalizedMatrix.Analytic
