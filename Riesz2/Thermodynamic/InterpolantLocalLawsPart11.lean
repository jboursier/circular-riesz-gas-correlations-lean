/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.InterpolantLocalLawsPart9
public import Riesz2.Thermodynamic.InterpolantLocalLawsPart8

/-!
# All-size bounds for the physical interaction differential

The common-simplex physical specialization of the proof of Proposition 6.6.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff
open Filter

namespace Riesz2.InterpolantLocalLaws

/-- Internal all-size polynomial bookkeeping for the proof of Proposition 6.6. The cutoff is any positive lower bound
for both actual boundary distances. -/
theorem internal_polynomial_force_bound (s γ ε : ℝ) (hs : 0 < s)
    (hγ : γ < 1) (hε : 0 ≤ ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ n N M d a b F : ℝ,
      1 ≤ n → 2 ≤ N → N ≤ M → 0 < d → d ≤ a → d ≤ b →
      (|F| ≤ 2 * (n * (2 * s * (N / 2) ^ (-s - 1) *
          ∑' k : ℤ, |(k : ℝ)| ^ (-s - 1)) +
        4 * s * (16 * n ^ ε) ^ (1 / (1 - γ)) * a ^ (-s - 1) +
        4 * s * (16 * n ^ ε) ^ (1 / (1 - γ)) * b ^ (-s - 1) +
        4 * (s * 2 ^ (s + 1) * ∑' k : ℕ, (k : ℝ) ^ (-s - 1)) +
        (s * 2 ^ (s + 1) * (1 + ∑' k : ℤ, |(k : ℝ)| ^ (-s - 1))) *
          (N ^ (-s) + M ^ (-s)))) →
      |F| ≤ B * n ^ (1 + ε / (1 - γ)) * (1 + d ^ (-s - 1)) := by
  let S := ∑' k : ℤ, |(k : ℝ)| ^ (-s - 1)
  let U := ∑' k : ℕ, (k : ℝ) ^ (-s - 1)
  let V := (16 : ℝ) ^ (1 / (1 - γ))
  let J := s * 2 ^ (s + 1) * (1 + S)
  let B := 4 * s * S + 16 * s * V + 8 * (s * 2 ^ (s + 1) * U) + 4 * J + 1
  have hS : 0 ≤ S := tsum_nonneg fun k => Real.rpow_nonneg (abs_nonneg _) _
  have hU : 0 ≤ U := tsum_nonneg fun k => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hV : 0 < V := Real.rpow_pos_of_pos (by norm_num) _
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  intro n N M d a b F hn hN hNM hd ha hb hF
  have hnp : 0 < n := by linarith
  let P := n ^ (1 + ε / (1 - γ))
  have hnP : n ≤ P := by
    calc
      n = n ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn (by
        have : 0 ≤ ε / (1 - γ) := div_nonneg hε (by linarith)
        linarith)
  have hP : 1 ≤ P := hn.trans hnP
  have hNa : (N / 2) ^ (-s - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hNp : N ^ (-s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hMp : M ^ (-s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hap := Real.rpow_le_rpow_of_nonpos hd ha (by linarith : -s - 1 ≤ 0)
  have hbp := Real.rpow_le_rpow_of_nonpos hd hb (by linarith : -s - 1 ≤ 0)
  have hT : (16 * n ^ ε) ^ (1 / (1 - γ)) ≤ V * P := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hnp.le]
    apply mul_le_mul_of_nonneg_left _ hV.le
    apply Real.rpow_le_rpow_of_exponent_le hn
    simp only [div_eq_mul_inv, one_mul]
    linarith
  have hc : n * (2 * s * (N / 2) ^ (-s - 1) * S) ≤ P * (2 * s * S) := by
    calc
      _ ≤ n * (2 * s * S) := by
        have hh := mul_le_mul_of_nonneg_left hNa (show 0 ≤ n * (2 * s * S) by positivity)
        nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right hnP (by positivity)
  have hba := mul_le_mul hT hap (Real.rpow_nonneg (hd.trans_le ha).le _) (by positivity : 0 ≤ V * P)
  have hbb := mul_le_mul hT hbp (Real.rpow_nonneg (hd.trans_le hb).le _) (by positivity : 0 ≤ V * P)
  have him := mul_le_mul_of_nonneg_left (add_le_add hNp hMp) hJ
  have hdp : 0 ≤ d ^ (-s - 1) := by positivity
  have hconst : 8 * (s * 2 ^ (s + 1) * U) + 4 * J ≤
      (8 * (s * 2 ^ (s + 1) * U) + 4 * J) * P * (1 + d ^ (-s - 1)) := by
    have hm : 1 ≤ P * (1 + d ^ (-s - 1)) := by nlinarith [mul_nonneg (show 0 ≤ P by linarith) hdp]
    nlinarith [mul_le_mul_of_nonneg_left hm
      (show 0 ≤ 8 * (s * 2 ^ (s + 1) * U) + 4 * J by positivity)]
  change |F| ≤ 2 * (n * (2 * s * (N / 2) ^ (-s - 1) * S) +
    4 * s * (16 * n ^ ε) ^ (1 / (1 - γ)) * a ^ (-s - 1) +
    4 * s * (16 * n ^ ε) ^ (1 / (1 - γ)) * b ^ (-s - 1) +
    4 * (s * 2 ^ (s + 1) * U) + J * (N ^ (-s) + M ^ (-s))) at hF
  have hraw : |F| ≤ 4 * s * S * P + 16 * s * V * P * d ^ (-s - 1) +
      8 * (s * 2 ^ (s + 1) * U) + 4 * J := by
    linear_combination hF + 2 * hc + 8 * s * hba + 8 * s * hbb + 2 * him
  have hcp := mul_nonneg (show 0 ≤ 4 * s * S * P by positivity) hdp
  have htp : 0 ≤ 16 * s * V * P := by positivity
  have hpp : 0 ≤ P * (1 + d ^ (-s - 1)) := by positivity
  apply hraw.trans
  change _ ≤ B * P * (1 + d ^ (-s - 1))
  dsimp only [B]
  nlinarith only [hconst, hcp, htp, hpp]

/-- See the proof of Proposition 6.6 in the paper: the actual common-simplex
force is bounded by a polynomial in the active size times any positive
active-gap cutoff, uniformly over compatible geometric exteriors. -/
theorem physical_force_polynomial (s : ℝ) (hs : 0 < s) (_hs1 : s ≠ 1) :
    ∀ ε : ℝ, 0 < ε →
      ε < min (1 - min s 1 / 2) (s - min s 1 / 2) / 4 →
      ∃ B : ℝ, 0 < B ∧ ∀ a : ℕ, 1 ≤ a → ∀ e d : ℕ,
        4 * (a + 1) ≤ e + a + 1 → e ≤ d →
        (a + 1 : ℝ) ^ (2 / s) ≤ (e + a + 1 : ℝ) →
      ∀ (p : Parameters), p.val.2 = s →
      ∃ WN : EuclideanSpace ℝ (Fin (e + a + 1)) → ℝ,
        ∃ WM : EuclideanSpace ℝ (Fin (d + a + 1)) → ℝ,
      ContDiffOn ℝ ∞ WN (gapAmbientDomain (e + a).succPNat) ∧
      ContDiffOn ℝ ∞ WM (gapAmbientDomain (d + a).succPNat) ∧
      (∀ x : {x : EuclideanSpace ℝ (Fin (e + a + 1)) //
          x ∈ gapAmbientDomain (e + a).succPNat},
        WN x.val = physicalAmbientGapEnergy p (e + a).succPNat x) ∧
      (∀ x : {x : EuclideanSpace ℝ (Fin (d + a + 1)) //
          x ∈ gapAmbientDomain (d + a).succPNat},
        WM x.val = physicalAmbientGapEnergy p (d + a).succPNat x) ∧
      ∀ (L : ℝ) (y : EuclideanSpace ℝ (Fin e)) (z : EuclideanSpace ℝ (Fin d)),
      (∀ k, 0 < y k) → (∀ k, 0 < z k) →
      (∑ k, y k) + L = (e + a + 1 : ℝ) →
      (∑ k, z k) + L = (d + a + 1 : ℝ) →
      |L - (a + 1 : ℝ)| ≤ (a + 1 : ℝ) ^ (min s 1 / 2 + ε) →
      (∀ r : ℕ, (_hr : 0 < r) → (hrb : r ≤ e) →
        |(∑ k : Fin r, y ⟨k.val, by have := k.isLt; omega⟩) - r| ≤
          4 * (a + 1 : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε)) →
      (∀ r : ℕ, (_hr : 0 < r) → (hrb : r ≤ e) →
        |(∑ k : Fin r, y ⟨e - r + k.val, by have := k.isLt; omega⟩) - r| ≤
          4 * (a + 1 : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε)) →
      (∀ r : ℕ, (_hr : 0 < r) → (hrb : r ≤ d) →
        |(∑ k : Fin r, z ⟨k.val, by have := k.isLt; omega⟩) - r| ≤
          4 * (a + 1 : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε)) →
      (∀ r : ℕ, (_hr : 0 < r) → (hrb : r ≤ d) →
        |(∑ k : Fin r, z ⟨d - r + k.val, by have := k.isLt; omega⟩) - r| ≤
          4 * (a + 1 : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε)) →
      let D := fun u => WN (RetainedSimplex.assemble e a
          (InterpolatingDensities.exteriorPermutation e a) y u) -
        WM (RetainedSimplex.assemble d a
          (InterpolatingDensities.exteriorPermutation d a) z u)
      ∀ u : EuclideanSpace ℝ (Fin (a + 1)),
      (∀ k, 0 < u k) → (∑ k, u k) = L →
      DifferentiableAt ℝ D u ∧ ∀ δ : ℝ, 0 < δ → (∀ k, δ ≤ u k) →
      ∀ i : Fin a,
        |fderiv ℝ D u
          (WithLp.toLp 2 (Pi.single i.castSucc 1 - Pi.single i.succ 1))| ≤
          B * (a + 1 : ℝ) ^ (1 + ε / (1 - (min s 1 / 2 + ε))) *
            (1 + δ ^ (-s - 1)) := by
  intro ε hε hεs
  have hγ1 : min s 1 / 2 + ε < 1 := by
    have hh := hεs.trans_le (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
    linarith [min_le_right s 1]
  obtain ⟨B, hB, hbound⟩ := internal_polynomial_force_bound s (min s 1 / 2 + ε) ε hs hγ1 hε.le
  refine ⟨B, hB, ?_⟩
  intro a ha e d hN hed _hsize p hps
  have he : 0 < e := by omega
  have hd : 0 < d := by omega
  have hA : 1 ≤ (a + 1 : ℝ) ^ ε := Real.one_le_rpow (by linarith) hε.le
  have hex := physical_force_absolute_composition p (e + a).succPNat (d + a).succPNat
    (by change e + a + 1 ≤ d + a + 1; omega) (by change 2 ≤ e + a + 1; omega)
  change ∃ WN : EuclideanSpace ℝ (Fin (e + a + 1)) → ℝ,
    ∃ WM : EuclideanSpace ℝ (Fin (d + a + 1)) → ℝ, _ at hex
  obtain ⟨WN, WM, hWN, hWM, hvN, hvM, hforce⟩ := hex
  refine ⟨WN, WM, hWN, hWM, hvN, hvM, ?_⟩
  intro L y z hy hz hmassY hmassZ hL hYR hYL hZR hZL D u hu hmass
  let X := RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y u
  let Y := RetainedSimplex.assemble d a (InterpolatingDensities.exteriorPermutation d a) z u
  have hX := assembled_physical_simplex e a y u hy hu (by rw [hmass]; simpa only [Nat.cast_add, Nat.cast_one] using hmassY)
  have hY := assembled_physical_simplex d a z u hz hu (by rw [hmass]; simpa only [Nat.cast_add, Nat.cast_one] using hmassZ)
  have hXN := PhysicalEnergy.simplex_subset_ambient (e + a).succPNat _ hX
  have hYM := PhysicalEnergy.simplex_subset_ambient (d + a).succPNat _ hY
  have hdn := (hWN.differentiableOn (by simp)).differentiableAt
    ((PhysicalEnergy.isOpen_gapAmbientDomain _).mem_nhds hXN)
  have hdm := (hWM.differentiableOn (by simp)).differentiableAt
    ((PhysicalEnergy.isOpen_gapAmbientDomain _).mem_nhds hYM)
  have hAN := (contDiff_exterior_assembly e a y).differentiable (by simp)
  have hAM := (contDiff_exterior_assembly d a z).differentiable (by simp)
  have hdN := hdn.comp u (hAN u)
  have hdM := hdm.comp u (hAM u)
  refine ⟨hdN.sub hdM, ?_⟩
  intro δ hδ hlow i
  dsimp only [D]
  change |fderiv ℝ ((WN ∘ RetainedSimplex.assemble e a
    (InterpolatingDensities.exteriorPermutation e a) y) -
      (WM ∘ RetainedSimplex.assemble d a
        (InterpolatingDensities.exteriorPermutation d a) z)) u _| ≤ _
  rw [fderiv_sub hdN hdM, sub_apply]
  simp only [Function.comp_def]
  rw [internal_assembled_pinned_derivative e a he y u WN hdn i,
    internal_assembled_pinned_derivative d a hd z u WM hdm i]
  have hactive (b : ℕ) (w : EuclideanSpace ℝ (Fin b)) (k : Fin (a + 1)) :
      RetainedSimplex.assemble b a (InterpolatingDensities.exteriorPermutation b a) w u
        ⟨k.val, by have := k.isLt; omega⟩ = u k :=
    InterpolatingDensities.assemble_exterior_active b a w u k (by omega)
  have hcommon : ∀ k : Fin (a + 1), X ⟨k.val, by have := k.isLt; omega⟩ =
      Y ⟨k.val, by have := k.isLt; omega⟩ := fun k => (hactive e y k).trans (hactive d z k).symm
  have hlen : |(∑ k : Fin (a + 1), X ⟨k.val, by have := k.isLt; omega⟩) -
      (a + 1 : ℝ)| ≤ (a + 1 : ℝ) ^ (min s 1 / 2 + ε) := by
    simpa only [X, hactive, hmass] using hL
  have right (b : ℕ) (hb : 0 < b) (w : EuclideanSpace ℝ (Fin b))
      (hw : ∀ r : ℕ, (_hr : 0 < r) → (hrb : r ≤ b) →
        |(∑ k : Fin r, w ⟨k.val, by have := k.isLt; omega⟩) - r| ≤
          4 * (a + 1 : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε)) :
      ∀ r : ℕ, 0 < r → r ≤ ((b + a).succPNat : ℕ) - (a + 1) →
        |cyclicGapSum (b + a).succPNat ⟨a + 1, by change a + 1 < b + a + 1; omega⟩ r
          (WithLp.ofLp (RetainedSimplex.assemble b a
            (InterpolatingDensities.exteriorPermutation b a) w u)) - r| ≤
          4 * (a + 1 : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε) := by
    intro r hr hrb
    have hrb' : r ≤ b := by change r ≤ b + a + 1 - (a + 1) at hrb; omega
    rw [cyclicGapSum_assembled_exterior_prefix b a r hb hrb']
    exact hw r hr hrb'
  have left (b : ℕ) (w : EuclideanSpace ℝ (Fin b))
      (hw : ∀ r : ℕ, (_hr : 0 < r) → (hrb : r ≤ b) →
        |(∑ k : Fin r, w ⟨b - r + k.val, by have := k.isLt; omega⟩) - r| ≤
          4 * (a + 1 : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε)) :
      ∀ r : ℕ, (hr : 0 < r) → (hrb : r ≤ ((b + a).succPNat : ℕ) - (a + 1)) →
        |cyclicGapSum (b + a).succPNat
          ⟨((b + a).succPNat : ℕ) - r, by have hp := (b + a).succPNat.pos; omega⟩ r
          (WithLp.ofLp (RetainedSimplex.assemble b a
            (InterpolatingDensities.exteriorPermutation b a) w u)) - r| ≤
          4 * (a + 1 : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε) := by
    intro r hr hrb
    have hrb' : r ≤ b := by change r ≤ b + a + 1 - (a + 1) at hrb; omega
    have hh := assembled_exterior_left b a r hr hrb' w u
    change cyclicGapSum (b + a).succPNat _ r _ = _ at hh
    simp only [Nat.succPNat_coe] at *
    rw [hh]
    exact hw r hr hrb'
  have hhalf := internal_half_period_of_length a.succPNat (e + a).succPNat hγ1.le hN
    (by simpa only [Nat.succPNat_coe, Nat.cast_succ] using hlen)
  have hh := hforce (a + 1) (i.val + 1) (by omega) (by have := i.isLt; omega)
    (by change a + 1 + 1 < e + a + 1; omega)
    (WithLp.ofLp X) hX (WithLp.ofLp Y) hY hcommon hhalf
    (min s 1 / 2 + ε) ((a + 1 : ℝ) ^ ε) (by positivity) hγ1 hA
    (by simpa only [Nat.cast_add, Nat.cast_one, X] using right e he y hYR)
    (by simpa only [Nat.cast_add, Nat.cast_one, X] using left e y hYL)
    (by simpa only [Nat.cast_add, Nat.cast_one, Y] using right d hd z hZR)
    (by simpa only [Nat.cast_add, Nat.cast_one, Y] using left d z hZL)
  dsimp only at hh
  rw [cyclicGapSum_assembled_active e a (i.val + 1)
    (a + 1 - (i.val + 1)) (by have := i.isLt; omega) (by omega)] at hh
  have hpre := cyclicGapSum_assembled_active e a 0 (i.val + 1)
    (by omega) (by have := i.isLt; omega) y u
  change cyclicGapSum (e + a).succPNat 0 (i.val + 1) _ = _ at hpre
  rw [hpre] at hh
  have hsuf : a + 1 - (i.val + 1) = a - i.val := by omega
  have hsumSuffix :
      (∑ k : Fin (a + 1 - (i.val + 1)), u ⟨i.val + 1 + k.val, by have := k.isLt; have := i.isLt; omega⟩) =
        ∑ k : Fin (a - i.val), u ⟨i.val + 1 + k.val, by have := k.isLt; have := i.isLt; omega⟩ := by
    apply Fintype.sum_equiv (finCongr hsuf)
    intro k
    rfl
  rw [hsumSuffix] at hh
  have lower (r q : ℕ) (hr : 0 < r) (hqr : q + r ≤ a + 1) :
      δ ≤ ∑ k : Fin r, u ⟨q + k.val, by have := k.isLt; omega⟩ := by
    have hh : (r : ℝ) * δ ≤ ∑ k : Fin r, u ⟨q + k.val, by have := k.isLt; omega⟩ := by
      calc
        _ = ∑ _k : Fin r, δ := by simp
        _ ≤ _ := Finset.sum_le_sum fun k _ => hlow _
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith
  apply hbound (a + 1) (e + a + 1) (d + a + 1) δ _ _ _
    (by linarith) (by exact_mod_cast (show 2 ≤ e + a + 1 by omega))
    (by exact_mod_cast (show e + a + 1 ≤ d + a + 1 by omega)) hδ
    (lower (a - i.val) (i.val + 1) (by have := i.isLt; omega) (by have := i.isLt; omega))
    (by simpa only [Nat.zero_add] using lower (i.val + 1) 0 (by omega) (by have := i.isLt; omega))
  simpa only [hps, Nat.add_sub_add_right, Nat.add_sub_cancel, Nat.zero_add, Nat.succPNat_coe,
    Nat.cast_succ, Nat.cast_add, Nat.cast_one, X, Y, WithLp.toLp_ofLp] using hh

/-- Internal uniform-force reconstruction for the proof of Proposition 6.6, including the zero-force carrier. -/
theorem internal_uniform_primitive (a : ℕ) (f : Fin a → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hf : ∀ i, |f i| ≤ B) (j : Fin (a + 1)) :
    |InteractionDifferential.pinnedRepresentative f j| ≤ (a : ℝ) * B := by
  apply (InteractionDifferential.pinnedRepresentative_abs_le f j).trans
  let S := Finset.univ.filter (fun i : Fin a =>
    min j.val (InteractionDifferential.middle a).val ≤ i.val ∧
      i.val < max j.val (InteractionDifferential.middle a).val)
  have hc : (S.card : ℝ) ≤ a := by
    exact_mod_cast (show S.card ≤ a by simpa only [Fintype.card_fin] using Finset.card_le_univ S)
  calc
    _ ≤ ∑ _i ∈ S, B := Finset.sum_le_sum fun i _ => hf i
    _ = (S.card : ℝ) * B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hB

/-- Internal global physical-force assembly for the proof of Proposition 6.6. A minimizing coordinate is selected only
inside the proof. The resulting bound uses the literal exceptional weight. -/
theorem internal_polynomial_global (s B q : ℝ) (hs : 0 < s) (hB : 0 ≤ B)
    (a : ℕ) (x : Fin (a + 1) → ℝ) (hx : ∀ j, 0 < x j)
    (f : Fin a → ℝ)
    (hf : ∀ δ : ℝ, 0 < δ → (∀ k, δ ≤ x k) →
      ∀ i, |f i| ≤ B * (a + 1 : ℝ) ^ q * (1 + δ ^ (-s - 1))) :
    (∑ j, InteractionDifferential.pinnedRepresentative f j ^ 2) ≤
      4 * B ^ 2 * (a + 1 : ℝ) ^ (3 + 2 * q) *
        exceptionalWeight (n := a.succPNat) s x := by
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image Finset.univ x Finset.univ_nonempty
  have hh := internal_global_weight_composition s hs a x hx j
    (B * (a + 1 : ℝ) ^ q) (by positivity) f
    (hf (x j) (hx j) (fun k => hj k (Finset.mem_univ k)))
  have hn : (0 : ℝ) < a + 1 := by positivity
  have hW : 0 ≤ exceptionalWeight (n := a.succPNat) s x :=
    le_trans zero_le_one (one_le_exceptionalWeight (n := a.succPNat) s x (fun i => (hx i).le))
  have ha : (a : ℝ) ^ 2 ≤ (a + 1 : ℝ) ^ 2 := by nlinarith [(show (0 : ℝ) ≤ a by positivity)]
  have hmul := mul_le_mul_of_nonneg_right ha
    (show 0 ≤ 4 * (a + 1 : ℝ) * (B * (a + 1 : ℝ) ^ q) ^ 2 *
      exceptionalWeight (n := a.succPNat) s x by positivity)
  have he : (a + 1 : ℝ) ^ (3 + 2 * q) =
      (a + 1 : ℝ) ^ 2 * (a + 1 : ℝ) * ((a + 1 : ℝ) ^ q) ^ 2 := by
    rw [show (3 : ℝ) + 2 * q = (2 + 1) + q * 2 by ring,
      Real.rpow_add hn, Real.rpow_add hn, Real.rpow_mul hn.le]
    simp only [Real.rpow_two, Real.rpow_one]
  apply hh.trans
  rw [he]
  convert hmul using 1 <;> ring

/-- Internal bounded-size fine estimate in the proof of Proposition 6.6. The cutoff loss is linear in the
fine-event parameter, and the remaining size power is explicit. -/
theorem internal_polynomial_fine (s ε K B q : ℝ) (hs : 0 < s)
    (hε : 0 ≤ ε) (hK : 0 ≤ K) (hB : 0 ≤ B) (a : ℕ)
    (f : Fin a → ℝ)
    (hf : ∀ i, |f i| ≤ B * (a + 1 : ℝ) ^ q *
      (1 + ((a + 1 : ℝ) ^ (-(K * ε))) ^ (-s - 1)))
    (j : Fin (a + 1)) :
    |InteractionDifferential.pinnedRepresentative f j| ≤
      2 * B * (a + 1 : ℝ) ^ (q + 1 + K * ε * (s + 1) + s - min s 1 / 2) *
        InteractionDifferential.boundaryWeight s a.succPNat j := by
  let n : ℝ := a + 1
  have hn : 0 < n := by dsimp [n]; positivity
  have hn1 : 1 ≤ n := by dsimp [n]; linarith [(show (0 : ℝ) ≤ a by positivity)]
  have hp : (n ^ (-(K * ε))) ^ (-s - 1) = n ^ (K * ε * (s + 1)) := by
    rw [← Real.rpow_mul hn.le]; congr 1; ring
  have hpow1 : 1 ≤ n ^ (K * ε * (s + 1)) := Real.one_le_rpow hn1 (by positivity)
  have hh := internal_uniform_primitive a f
    (B * n ^ q * (1 + (n ^ (-(K * ε))) ^ (-s - 1))) (by positivity) hf j
  rw [hp] at hh
  have hsize : (a : ℝ) ≤ n := by dsimp [n]; linarith
  have hfirst : |InteractionDifferential.pinnedRepresentative f j| ≤
      2 * B * n ^ (q + 1 + K * ε * (s + 1)) := by
    calc
      _ ≤ (a : ℝ) * (B * n ^ q * (1 + n ^ (K * ε * (s + 1)))) := hh
      _ ≤ n * (B * n ^ q * (2 * n ^ (K * ε * (s + 1)))) := by
        apply mul_le_mul hsize _ (by positivity) hn.le
        apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by
        rw [show q + 1 + K * ε * (s + 1) = 1 + q + K * ε * (s + 1) by ring,
          Real.rpow_add hn, Real.rpow_add hn, Real.rpow_one]
        ring
  have hσs : min s 1 / 2 ≤ s := by
    have hm : 0 ≤ min s 1 := le_min hs.le zero_le_one
    linarith [min_le_left s 1]
  have hd := InteractionDifferential.boundary_distance_pos a.succPNat j
  have hdist : (min (j.val + 1) (a + 1 - j.val) : ℕ) ≤ a + 1 := by omega
  have hw : n ^ (min s 1 / 2 - s) ≤ InteractionDifferential.boundaryWeight s a.succPNat j := by
    exact Real.rpow_le_rpow_of_nonpos hd (by simpa only [n, Nat.succPNat_coe, Nat.cast_succ] using (Nat.cast_le (α := ℝ)).mpr hdist) (by linarith)
  have ht := mul_le_mul_of_nonneg_left hw
    (show 0 ≤ 2 * B * n ^ (q + 1 + K * ε * (s + 1) + s - min s 1 / 2) by positivity)
  apply hfirst.trans
  apply le_trans _ ht
  apply le_of_eq
  calc
    _ = 2 * B * n ^ ((q + 1 + K * ε * (s + 1) + s - min s 1 / 2) +
        (min s 1 / 2 - s)) := by congr 2; ring
    _ = _ := by rw [Real.rpow_add hn]; ring

/-- Internal power absorption for the fine-event estimate of the proof of Proposition 6.6. The tolerance changes the prefactor,
and the loss exponent stays bounded as the tolerance decreases. -/
theorem internal_fine_absorption (s ε K C : ℝ) (hs : 0 < s)
    (hε : 0 < ε) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hγs : min s 1 / 2 + ε < s) (hγ1 : min s 1 / 2 + ε < 1) :
    ∃ H : ℝ, 0 < H ∧
      ∀ (a : ℕ) (N : ℝ), 0 < N → ∀ (f : Fin a → ℝ),
      (∀ i : Fin a, |f i| ≤ C *
        (((16 * (a + 1 : ℝ) ^ ε) ^ (1 / (1 - (min s 1 / 2 + ε)))) *
          (a + 1 : ℝ) ^ ((K * ε) * (s + 1)) *
          ((i.val + 1 : ℝ) ^ (-s - 1) + ((a - i.val : ℕ) : ℝ) ^ (-s - 1)) +
         (a + 1 : ℝ) ^ ε *
          (a + 1 : ℝ) ^ ((K * ε) * (s + 1 - (min s 1 / 2 + ε))) *
          ((i.val + 1 : ℝ) ^ (min s 1 / 2 + ε - s - 1) +
            ((a - i.val : ℕ) : ℝ) ^ (min s 1 / 2 + ε - s - 1))) + C * N ^ (-s)) →
      ∀ j : Fin (a + 1),
      |InteractionDifferential.pinnedRepresentative f j| ≤
        H * (a + 1 : ℝ) ^
          ((1 / (1 - (min s 1 / 2 + ε)) + K * (s + 1) + 2) * ε) *
          (InteractionDifferential.boundaryWeight s a.succPNat j + (a + 1 : ℝ) * N ^ (-s)) := by
  let γ := min s 1 / 2 + ε
  let v := 1 / (1 - γ)
  let κ := v + K * (s + 1) + 2
  let H₁ := 2 * C * (16 : ℝ) ^ v * (1 + 1 / s)
  let H₂ := 2 * C * (1 + 1 / (s - γ))
  have hv : 0 < v := by dsimp [v, γ]; positivity
  have hH₁ : 0 ≤ H₁ := by dsimp [H₁]; positivity
  have hH₂ : 0 ≤ H₂ := by
    dsimp [H₂]
    have : 0 < s - γ := by dsimp [γ]; linarith
    positivity
  have hκ : 0 ≤ κ * ε := by dsimp [κ]; positivity
  refine ⟨H₁ + H₂ + C + 1, by positivity, ?_⟩
  intro a N hN f hf j
  let n : ℝ := a + 1
  have hn : 0 < n := by dsimp [n]; positivity
  have hn1 : 1 ≤ n := by dsimp [n]; linarith [(show (0 : ℝ) ≤ a by positivity)]
  let P := n ^ (κ * ε)
  have hP : 1 ≤ P := Real.one_le_rpow hn1 hκ
  have hT : (16 * n ^ ε) ^ v = 16 ^ v * n ^ (ε * v) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hn.le]
  have h₁ : 2 * C * ((16 * n ^ ε) ^ v) * n ^ ((K * ε) * (s + 1)) * (1 + 1 / s) ≤ H₁ * P := by
    rw [hT]
    calc
      _ = H₁ * n ^ (ε * v + (K * ε) * (s + 1)) := by
        rw [Real.rpow_add hn]; dsimp only [H₁]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [κ]; nlinarith)) hH₁
  have h₂ : 2 * C * n ^ (2 * ε + (K * ε) * (s + 1 - γ)) *
      (1 + 1 / (s - γ)) ≤ H₂ * P := by
    calc
      _ = H₂ * n ^ (2 * ε + (K * ε) * (s + 1 - γ)) := by dsimp only [H₂]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn1 (by
          have hγ : 0 ≤ γ := by dsimp [γ]; positivity
          dsimp [κ]
          nlinarith [mul_nonneg (mul_nonneg hK hε.le) hγ])) hH₂
  have hh := internal_differential_fine_bound s ε (K * ε) C
    ((16 * n ^ ε) ^ v) (C * N ^ (-s)) a hs hε.le hγs hC (by positivity)
    (by positivity) f hf j
  have hw := InteractionDifferential.boundaryWeight_pos s a.succPNat j
  have hnN : 0 ≤ n * N ^ (-s) := by positivity
  have hpN : n * N ^ (-s) ≤ P * (n * N ^ (-s)) := by nlinarith
  have haN : (a : ℝ) * (C * N ^ (-s)) ≤ C * (n * N ^ (-s)) := by
    dsimp [n]; nlinarith [mul_nonneg hC (Real.rpow_nonneg hN.le (-s))]
  have hpw : 0 ≤ P * InteractionDifferential.boundaryWeight s a.succPNat j := by positivity
  have hpn : 0 ≤ P * (n * N ^ (-s)) := by positivity
  change _ ≤ (H₁ + H₂ + C + 1) * P *
    (InteractionDifferential.boundaryWeight s a.succPNat j + n * N ^ (-s))
  have hcN := mul_le_mul_of_nonneg_left hpN hC
  have hcoef := mul_le_mul_of_nonneg_right (add_le_add h₁ h₂) hw.le
  change _ ≤ (_ + _) * InteractionDifferential.boundaryWeight s a.succPNat j + _ at hh
  nlinarith only [hh, haN, hcN, hcoef, hpw, hpn,
    mul_nonneg hH₁ hpn, mul_nonneg hH₂ hpn, mul_nonneg hC hpw]

/-- Internal extension-independence bridge for Lemma 6.4.
Two ambient realizations of the physical energy agree on a
neighborhood of every physical assembled point, hence have equal derivatives. -/
theorem internal_realization_eventuallyEq (p : Parameters) (e a : ℕ)
    (y : EuclideanSpace ℝ (Fin e)) (u : EuclideanSpace ℝ (Fin (a + 1)))
    (V W : EuclideanSpace ℝ (Fin (e + a + 1)) → ℝ)
    (hV : ∀ x : {x : EuclideanSpace ℝ (Fin (e + a + 1)) //
        x ∈ gapAmbientDomain (e + a).succPNat},
      V x.val = physicalAmbientGapEnergy p (e + a).succPNat x)
    (hW : ∀ x : {x : EuclideanSpace ℝ (Fin (e + a + 1)) //
        x ∈ gapAmbientDomain (e + a).succPNat},
      W x.val = physicalAmbientGapEnergy p (e + a).succPNat x)
    (hu : RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y u ∈
      gapAmbientDomain (e + a).succPNat) :
    (fun w => V (RetainedSimplex.assemble e a
        (InterpolatingDensities.exteriorPermutation e a) y w)) =ᶠ[nhds u]
      (fun w => W (RetainedSimplex.assemble e a
        (InterpolatingDensities.exteriorPermutation e a) y w)) := by
  have hn := (PhysicalEnergy.isOpen_gapAmbientDomain (e + a).succPNat).mem_nhds hu
  have hc := (contDiff_exterior_assembly e a y).continuous.continuousAt (x := u)
  filter_upwards [hc.preimage_mem_nhds hn] with w hw
  exact (hV ⟨_, hw⟩).trans (hW ⟨_, hw⟩).symm

/-- See the proof of Proposition 6.6 in the paper, both estimates at every
active size. The result holds for every compatible geometric exterior pair,
so in particular for admissible exteriors. The fine cutoff factor `K` is
arbitrary and may be the structural constant supplied by the local laws.
The representative is exactly Lemma 6.4, with its actual tangent pairing.
The constants precede both volumes, the temperature and the exteriors. -/
theorem interaction_differential (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (K : ℝ) (hK : 1 < K) :
    ∀ ε : ℝ, 0 < ε →
      ε < min (1 - min s 1 / 2) (s - min s 1 / 2) / 4 →
      ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ a e d : ℕ, 1 ≤ a →
        4 * (a + 1) ≤ e + a + 1 → e ≤ d →
        (a + 1 : ℝ) ^ (2 / s) ≤ (e + a + 1 : ℝ) →
      ∀ (p : Parameters), p.val.2 = s →
      ∃ WN : EuclideanSpace ℝ (Fin (e + a + 1)) → ℝ,
        ∃ WM : EuclideanSpace ℝ (Fin (d + a + 1)) → ℝ,
      ContDiffOn ℝ ∞ WN (gapAmbientDomain (e + a).succPNat) ∧
      ContDiffOn ℝ ∞ WM (gapAmbientDomain (d + a).succPNat) ∧
      (∀ x : {x : EuclideanSpace ℝ (Fin (e + a + 1)) //
          x ∈ gapAmbientDomain (e + a).succPNat},
        WN x.val = physicalAmbientGapEnergy p (e + a).succPNat x) ∧
      (∀ x : {x : EuclideanSpace ℝ (Fin (d + a + 1)) //
          x ∈ gapAmbientDomain (d + a).succPNat},
        WM x.val = physicalAmbientGapEnergy p (d + a).succPNat x) ∧
      ∀ (L : ℝ) (y : EuclideanSpace ℝ (Fin e)) (z : EuclideanSpace ℝ (Fin d)),
      (∀ k, 0 < y k) → (∀ k, 0 < z k) →
      (∑ k, y k) + L = (e + a + 1 : ℝ) →
      (∑ k, z k) + L = (d + a + 1 : ℝ) →
      |L - (a + 1 : ℝ)| ≤ (a + 1 : ℝ) ^ (min s 1 / 2 + ε) →
      (∀ r : ℕ, (_hr : 0 < r) → (hrb : r ≤ e) →
        |(∑ k : Fin r, y ⟨k.val, by have := k.isLt; omega⟩) - r| ≤
          4 * (a + 1 : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε)) →
      (∀ r : ℕ, (_hr : 0 < r) → (hrb : r ≤ e) →
        |(∑ k : Fin r, y ⟨e - r + k.val, by have := k.isLt; omega⟩) - r| ≤
          4 * (a + 1 : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε)) →
      (∀ r : ℕ, (_hr : 0 < r) → (hrb : r ≤ d) →
        |(∑ k : Fin r, z ⟨k.val, by have := k.isLt; omega⟩) - r| ≤
          4 * (a + 1 : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε)) →
      (∀ r : ℕ, (_hr : 0 < r) → (hrb : r ≤ d) →
        |(∑ k : Fin r, z ⟨d - r + k.val, by have := k.isLt; omega⟩) - r| ≤
          4 * (a + 1 : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε)) →
      let D := fun u => WN (RetainedSimplex.assemble e a
          (InterpolatingDensities.exteriorPermutation e a) y u) -
        WM (RetainedSimplex.assemble d a
          (InterpolatingDensities.exteriorPermutation d a) z u)
      ∀ u : EuclideanSpace ℝ (Fin (a + 1)),
      (∀ k, 0 < u k) → (∑ k, u k) = L →
      DifferentiableAt ℝ D u ∧
      (∀ v : Fin (a + 1) → ℝ, (∑ j, v j) = 0 →
        (∑ j, InteractionDifferential.pinnedRepresentative
          (fun i : Fin a => fderiv ℝ D u
            (WithLp.toLp 2 (Pi.single i.castSucc 1 - Pi.single i.succ 1))) j * v j) =
          fderiv ℝ D u (WithLp.toLp 2 v)) ∧
      (WithLp.ofLp u ∈ goodBlockEvent s a.succPNat (e + a).succPNat (K * ε) →
        ∀ j : Fin (a + 1),
        |InteractionDifferential.pinnedRepresentative
          (fun i : Fin a => fderiv ℝ D u
            (WithLp.toLp 2 (Pi.single i.castSucc 1 - Pi.single i.succ 1))) j| ≤
          C * (a + 1 : ℝ) ^ (κ * ε) *
            (InteractionDifferential.boundaryWeight s a.succPNat j +
              (a + 1 : ℝ) * (e + a + 1 : ℝ) ^ (-s))) ∧
      (‖WithLp.toLp 2 (InteractionDifferential.pinnedRepresentative
          (fun i : Fin a => fderiv ℝ D u
            (WithLp.toLp 2 (Pi.single i.castSucc 1 - Pi.single i.succ 1))))‖ ^ 2 ≤
        C * (a + 1 : ℝ) ^ C * exceptionalWeight (n := a.succPNat) s (WithLp.ofLp u)) ∧
      (a + 1 : ℝ) * (e + a + 1 : ℝ) ^ (-s) ≤ (a + 1 : ℝ)⁻¹ := by
  intro ε hε hεs
  have hγ1 : min s 1 / 2 + ε < 1 := by
    have hh := hεs.trans_le (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
    linarith [min_le_right s 1]
  have hγs : min s 1 / 2 + ε < s := by
    have hh := hεs.trans_le (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
    linarith
  let γ := min s 1 / 2 + ε
  let v := 1 / (1 - γ)
  let q := 1 + ε / (1 - γ)
  let κ := v + K * (s + 1) + 2
  let R := 2 + s - min s 1 / 2
  have hv : 0 < v := by dsimp [v, γ]; positivity
  have hq : 0 < q := by dsimp [q, γ]; positivity
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hσ : 0 ≤ min s 1 / 2 := by positivity
  have hσs : min s 1 / 2 ≤ s := by linarith [min_le_left s 1]
  have hR : 0 ≤ R := by dsimp [R]; linarith
  obtain ⟨B, hB, hpoly⟩ := physical_force_polynomial s hs hs1 ε hε hεs
  obtain ⟨F, hF, hforce⟩ := exterior_force_on_common_simplex s hs hs1
  obtain ⟨n₀, hn₀⟩ := hforce ε hε hεs
  obtain ⟨H, hH, hfine⟩ := internal_fine_absorption s ε K F hs hε (by linarith) hF.le hγs hγ1
  let nbar : ℕ := max 2 n₀
  let C := H + 2 * B * (nbar : ℝ) ^ R + 4 * B ^ 2 + 5 + 2 * q
  have hnbar : (0 : ℝ) < nbar := by exact_mod_cast (show 0 < nbar by dsimp [nbar]; omega)
  have hC : 0 < C := by dsimp [C]; positivity
  have hterm : 0 ≤ 2 * B * (nbar : ℝ) ^ R := by positivity
  have hHC : H ≤ C := by dsimp [C]; nlinarith [sq_nonneg B]
  have hBC : 2 * B * (nbar : ℝ) ^ R ≤ C := by dsimp [C]; nlinarith [sq_nonneg B]
  have hGC : 4 * B ^ 2 ≤ C := by dsimp [C]; linarith
  have hQC : 3 + 2 * q ≤ C := by dsimp [C]; nlinarith [sq_nonneg B]
  refine ⟨C, κ, hC, hκ, ?_⟩
  intro a e d ha hN hed hsize p hps
  obtain ⟨WN, WM, hWN, hWM, hvN, hvM, hb⟩ := hpoly a ha e d hN hed hsize p hps
  refine ⟨WN, WM, hWN, hWM, hvN, hvM, ?_⟩
  intro L y z hy hz hmassY hmassZ hL hYR hYL hZR hZL D u hu hmass
  have hDu := hb L y z hy hz hmassY hmassZ hL hYR hYL hZR hZL u hu hmass
  clear hb hpoly hforce
  let f : Fin a → ℝ := fun i => fderiv ℝ D u
    (WithLp.toLp 2 (Pi.single i.castSucc 1 - Pi.single i.succ 1))
  let n : ℝ := a + 1
  have hn : 0 < n := by dsimp [n]; positivity
  have hn1 : 1 ≤ n := by dsimp [n]; linarith
  have hNr : 0 < (e + a + 1 : ℝ) := by positivity
  have hP : 0 ≤ n ^ (κ * ε) := by positivity
  have hW : 0 ≤ exceptionalWeight (n := a.succPNat) s (WithLp.ofLp u) :=
    le_trans zero_le_one (one_le_exceptionalWeight (n := a.succPNat) s _ (fun i => (hu i).le))
  refine ⟨hDu.1, ?_, ?_, ?_, ?_⟩
  · intro v₀ hv₀
    exact pinned_derivative_representative_pairing a D u hDu.1 v₀ hv₀
  · intro hgood j
    have hw := InteractionDifferential.boundaryWeight_pos s a.succPNat j
    have herror : 0 ≤ n * (e + a + 1 : ℝ) ^ (-s) := by positivity
    have hphysical : ∀ i, |f i| ≤ B * n ^ q *
        (1 + (n ^ (-(K * ε))) ^ (-s - 1)) :=
      hDu.2 (n ^ (-(K * ε))) (by positivity) (fun k => by
        simpa only [n, Nat.succPNat_coe, Nat.cast_succ] using (hgood.2.1 k).1)
    by_cases hlarge : n₀ ≤ a + 1
    · obtain ⟨VN, VM, _hVN, _hVM, heN, heM, hbf⟩ :=
        hn₀ a e d hlarge ha hN hed hsize p hps
      let E := fun w => VN (RetainedSimplex.assemble e a
          (InterpolatingDensities.exteriorPermutation e a) y w) -
        VM (RetainedSimplex.assemble d a
          (InterpolatingDensities.exteriorPermutation d a) z w)
      have hE := hbf L y z hy hz hmassY hmassZ hL hYR hYL hZR hZL u hu hmass
      have hXN := PhysicalEnergy.simplex_subset_ambient (e + a).succPNat _
        (assembled_physical_simplex e a y u hy hu (by
          rw [hmass]; simpa only [Nat.cast_add, Nat.cast_one] using hmassY))
      have hYM := PhysicalEnergy.simplex_subset_ambient (d + a).succPNat _
        (assembled_physical_simplex d a z u hz hu (by
          rw [hmass]; simpa only [Nat.cast_add, Nat.cast_one] using hmassZ))
      have heq : fderiv ℝ D u = fderiv ℝ E u :=
        ((internal_realization_eventuallyEq p e a y u WN VN hvN heN hXN).sub
          (internal_realization_eventuallyEq p d a z u WM VM hvM heM hYM)).fderiv_eq
      have hcut (i : Fin a) := internal_force_cutoff
        (η := K * ε) (γ := γ) (n := n)
        (T := (16 * n ^ ε) ^ v) (A := n ^ ε)
        hn (by exact_mod_cast (Nat.sub_pos_of_lt i.isLt) : (0 : ℝ) < (a - i.val : ℕ))
        (by positivity : (0 : ℝ) < i.val + 1) hs (by dsimp [γ]; linarith) hF.le
        (by positivity) (by positivity)
        (by simpa only [n, Nat.succPNat_coe, Nat.cast_succ] using
          (goodBlockEvent_interval_lower s (K * ε) a.succPNat (e + a).succPNat
            (WithLp.ofLp u) hgood (i.val + 1) (a - i.val)
            (by change i.val + 1 + (a - i.val) ≤ a + 1; have := i.isLt; omega)))
        (by simpa only [n, Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add,
          Nat.cast_one, Nat.zero_add] using
          (goodBlockEvent_interval_lower s (K * ε) a.succPNat (e + a).succPNat
            (WithLp.ofLp u) hgood 0 (i.val + 1)
            (by change 0 + (i.val + 1) ≤ a + 1; have := i.isLt; omega)))
        (hE.2 i)
      have hprof : ∀ i : Fin a, |f i| ≤ F *
          (((16 * n ^ ε) ^ v) * n ^ ((K * ε) * (s + 1)) *
            ((i.val + 1 : ℝ) ^ (-s - 1) + ((a - i.val : ℕ) : ℝ) ^ (-s - 1)) +
           n ^ ε * n ^ ((K * ε) * (s + 1 - γ)) *
            ((i.val + 1 : ℝ) ^ (γ - s - 1) + ((a - i.val : ℕ) : ℝ) ^ (γ - s - 1))) +
            F * (e + a + 1 : ℝ) ^ (-s) := by
        intro i
        dsimp only [f]
        rw [heq]
        apply (hcut i).trans_eq
        ring
      have hh := hfine a (e + a + 1) hNr f hprof j
      apply hh.trans
      change _ ≤ C * n ^ (κ * ε) *
        (InteractionDifferential.boundaryWeight s a.succPNat j + n * (e + a + 1 : ℝ) ^ (-s))
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hHC hP) (by positivity)
    · have hh := internal_polynomial_fine s ε K B q hs hε.le (by linarith) hB.le a f hphysical j
      have hsmall : n ≤ (nbar : ℝ) := by
        dsimp only [n]
        exact_mod_cast (show a + 1 ≤ nbar by dsimp [nbar]; omega)
      have hexp : q + 1 + K * ε * (s + 1) + s - min s 1 / 2 ≤ R + κ * ε := by
        dsimp [q, R, κ, v]
        simp only [div_eq_mul_inv, one_mul]
        nlinarith only [hε]
      have hp₁ := Real.rpow_le_rpow_of_exponent_le hn1 hexp
      have hp₂ := Real.rpow_le_rpow hn.le hsmall hR
      have hh₂ : n ^ (q + 1 + K * ε * (s + 1) + s - min s 1 / 2) ≤
          (nbar : ℝ) ^ R * n ^ (κ * ε) := by
        apply hp₁.trans
        rw [Real.rpow_add hn]
        exact mul_le_mul_of_nonneg_right hp₂ hP
      have hbd := mul_le_mul_of_nonneg_left hh₂ (show 0 ≤ 2 * B by positivity)
      have hfinal := mul_le_mul_of_nonneg_right hbd hw.le
      apply hh.trans
      change _ ≤ C * n ^ (κ * ε) *
        (InteractionDifferential.boundaryWeight s a.succPNat j + n * (e + a + 1 : ℝ) ^ (-s))
      calc
        _ ≤ (2 * B * (nbar : ℝ) ^ R) * n ^ (κ * ε) *
            InteractionDifferential.boundaryWeight s a.succPNat j := by
          convert hfinal using 1; ring
        _ ≤ C * n ^ (κ * ε) * InteractionDifferential.boundaryWeight s a.succPNat j :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBC hP) hw.le
        _ ≤ _ := by nlinarith only [mul_nonneg (mul_nonneg hC.le hP) herror]
  · have hh := internal_polynomial_global s B q hs hB.le a (WithLp.ofLp u) hu f hDu.2
    have hp := Real.rpow_le_rpow_of_exponent_le hn1 hQC
    have hc := mul_le_mul hGC hp (by positivity : 0 ≤ n ^ (3 + 2 * q)) hC.le
    have hm := mul_le_mul_of_nonneg_right hc hW
    simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
    exact hh.trans hm
  · exact InteractionDifferential.period_error_le hs hn hNr hsize

/-- See Subsection 6.1 of the paper: the exterior geometry supplies the
ordinary prefix and suffix sums used by the physical force estimates. -/
theorem exteriorGeometry_ordinary (s ε : ℝ) (e a : ℕ)
    (y : EuclideanSpace ℝ (Fin e)) (hy : exteriorGeometry s ε e a y)
    (r : ℕ) (hr : 0 < r) (hre : r ≤ e) :
    (|(∑ k : Fin r, y ⟨k.val, by have := k.isLt; omega⟩) - r| ≤
      4 * (a + 1 : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε)) ∧
    (|(∑ k : Fin r, y ⟨e - r + k.val, by have := k.isLt; omega⟩) - r| ≤
      4 * (a + 1 : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε)) := by
  classical
  have hpre : (∑ k : Fin r, y ⟨k.val, by have := k.isLt; omega⟩) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin e => i.val < r), y i := by
    apply Finset.sum_bij (fun (k : Fin r) _ => (⟨k.val, by have := k.isLt; omega⟩ : Fin e))
    · intro k _; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact k.isLt
    · intro i _ j _ hij
      apply Fin.ext
      exact congrArg (fun k : Fin e => k.val) hij
    · intro i hi
      have hi' : i.val < r := (Finset.mem_filter.mp hi).2
      exact ⟨⟨i.val, hi'⟩, Finset.mem_univ _, Fin.ext rfl⟩
    · intro k _; rfl
  have hsuf : (∑ k : Fin r, y ⟨e - r + k.val, by have := k.isLt; omega⟩) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin e => e - r ≤ i.val), y i := by
    apply Finset.sum_bij (fun (k : Fin r) _ =>
      (⟨e - r + k.val, by have := k.isLt; omega⟩ : Fin e))
    · intro k _; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
    · intro i _ j _ hij
      have hh := Fin.val_eq_of_eq hij
      dsimp only at hh
      apply Fin.ext; omega
    · intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      refine ⟨⟨i.val - (e - r), by have := i.isLt; omega⟩, Finset.mem_univ _, ?_⟩
      apply Fin.ext; dsimp only; omega
    · intro k _; rfl
  have hh := hy.2 r (by omega) hre
  simpa only [hpre, hsuf, Nat.cast_add, Nat.cast_one] using hh

/-- See the proof of Proposition 6.6 in the paper, on the actual admissible
exterior carrier of Subsection 6.1. Both differential bounds, the tangent
pairing and the period comparison hold simultaneously for all active
sizes `n ≥ 2`. -/
theorem admissible_interaction_differential (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (K : ℝ) (hK : 1 < K) :
    ∀ ε : ℝ, 0 < ε →
      ε < min (1 - min s 1 / 2) (s - min s 1 / 2) / 4 →
      ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ a e d : ℕ, 1 ≤ a →
        4 * (a + 1) ≤ e + a + 1 → e ≤ d →
        (a + 1 : ℝ) ^ (2 / s) ≤ (e + a + 1 : ℝ) →
      ∀ (p : Parameters), p.val.2 = s →
      ∃ WN : EuclideanSpace ℝ (Fin (e + a + 1)) → ℝ,
        ∃ WM : EuclideanSpace ℝ (Fin (d + a + 1)) → ℝ,
      ContDiffOn ℝ ∞ WN (gapAmbientDomain (e + a).succPNat) ∧
      ContDiffOn ℝ ∞ WM (gapAmbientDomain (d + a).succPNat) ∧
      (∀ x : {x : EuclideanSpace ℝ (Fin (e + a + 1)) //
          x ∈ gapAmbientDomain (e + a).succPNat},
        WN x.val = physicalAmbientGapEnergy p (e + a).succPNat x) ∧
      (∀ x : {x : EuclideanSpace ℝ (Fin (d + a + 1)) //
          x ∈ gapAmbientDomain (d + a).succPNat},
        WM x.val = physicalAmbientGapEnergy p (d + a).succPNat x) ∧
      ∀ (he : 1 ≤ e) (hd : 1 ≤ d) (θ : PhysicalCutoff) (A : ℝ), 1 < A →
      ∀ (L : ℝ)
        (y : AffineSimplex.chartDomain e ((e + a : ℕ) + 1))
        (z : AffineSimplex.chartDomain d ((d + a : ℕ) + 1)),
      admissibleExterior p e a he θ ε A K y →
      admissibleExterior p d a hd θ ε A K z →
      (∑ k, y.val k) + L = (e + a + 1 : ℝ) →
      (∑ k, z.val k) + L = (d + a + 1 : ℝ) →
      let D := fun u => WN (RetainedSimplex.assemble e a
          (InterpolatingDensities.exteriorPermutation e a) y.val u) -
        WM (RetainedSimplex.assemble d a
          (InterpolatingDensities.exteriorPermutation d a) z.val u)
      ∀ u : EuclideanSpace ℝ (Fin (a + 1)),
      (∀ k, 0 < u k) → (∑ k, u k) = L →
      DifferentiableAt ℝ D u ∧
      (∀ v : Fin (a + 1) → ℝ, (∑ j, v j) = 0 →
        (∑ j, InteractionDifferential.pinnedRepresentative
          (fun i : Fin a => fderiv ℝ D u
            (WithLp.toLp 2 (Pi.single i.castSucc 1 - Pi.single i.succ 1))) j * v j) =
          fderiv ℝ D u (WithLp.toLp 2 v)) ∧
      (WithLp.ofLp u ∈ goodBlockEvent s a.succPNat (e + a).succPNat (K * ε) →
        ∀ j : Fin (a + 1),
        |InteractionDifferential.pinnedRepresentative
          (fun i : Fin a => fderiv ℝ D u
            (WithLp.toLp 2 (Pi.single i.castSucc 1 - Pi.single i.succ 1))) j| ≤
          C * (a + 1 : ℝ) ^ (κ * ε) *
            (InteractionDifferential.boundaryWeight s a.succPNat j +
              (a + 1 : ℝ) * (e + a + 1 : ℝ) ^ (-s))) ∧
      (‖WithLp.toLp 2 (InteractionDifferential.pinnedRepresentative
          (fun i : Fin a => fderiv ℝ D u
            (WithLp.toLp 2 (Pi.single i.castSucc 1 - Pi.single i.succ 1))))‖ ^ 2 ≤
        C * (a + 1 : ℝ) ^ C * exceptionalWeight (n := a.succPNat) s (WithLp.ofLp u)) ∧
      (a + 1 : ℝ) * (e + a + 1 : ℝ) ^ (-s) ≤ (a + 1 : ℝ)⁻¹ := by
  intro ε hε hεs
  obtain ⟨C, κ, hC, hκ, hmain⟩ := interaction_differential s hs hs1 K hK ε hε hεs
  refine ⟨C, κ, hC, hκ, ?_⟩
  intro a e d ha hN hed hsize p hps
  obtain ⟨WN, WM, hWN, hWM, hvN, hvM, hb⟩ := hmain a e d ha hN hed hsize p hps
  refine ⟨WN, WM, hWN, hWM, hvN, hvM, ?_⟩
  intro he hd θ A _hA L y z hy hz hmassY hmassZ
  have hgY : exteriorGeometry s ε e a y.val := by
    simpa only [hps] using hy.1
  have hgZ : exteriorGeometry s ε d a z.val := by
    simpa only [hps] using hz.1
  have hlength : |L - (a + 1 : ℝ)| ≤ (a + 1 : ℝ) ^ (min s 1 / 2 + ε) := by
    have hh := hgY.1
    simp only [Nat.cast_add, Nat.cast_one] at hh
    have heq : (e + a + 1 : ℝ) - ∑ k, y.val k = L := by linarith only [hmassY]
    rwa [heq] at hh
  exact hb L y.val z.val y.property.1 z.property.1 hmassY hmassZ hlength
    (fun r hr hre => (exteriorGeometry_ordinary s ε e a y.val hgY r hr hre).1)
    (fun r hr hre => (exteriorGeometry_ordinary s ε e a y.val hgY r hr hre).2)
    (fun r hr hre => (exteriorGeometry_ordinary s ε d a z.val hgZ r hr hre).1)
    (fun r hr hre => (exteriorGeometry_ordinary s ε d a z.val hgZ r hr hre).2)

end Riesz2.InterpolantLocalLaws
