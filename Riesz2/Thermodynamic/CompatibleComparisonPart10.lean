/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.CompatibleComparisonPart7

/-!
# Physical differential bounds with a tolerance-independent loss

The force estimates in the proof of Proposition 6.6 give a loss chosen before the
tolerance. The finite-size and large-size arguments use the same physical differential.
-/

public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal ContDiff Topology

namespace Riesz2.InterpolantLocalLaws

/-- See the proof of Proposition 6.6 in the paper:
both physical differential estimates, with the loss chosen using only `s,K`
before the tolerance. This internal geometric interface also retains the exact
tangent pairing and the finite-period error, at every active size. -/
theorem interaction_differential_uniform_internal (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (K : ℝ) (hK : 1 < K) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε →
      ε < min (1 - min s 1 / 2) (s - min s 1 / 2) / 4 →
      ∃ C : ℝ, 0 < C ∧ ∀ a e d : ℕ, 1 ≤ a →
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
  let κ := K * (s + 1) + 6
  have hκ : 0 < κ := by dsimp [κ]; positivity
  refine ⟨κ, hκ, ?_⟩
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
  let R := 2 + s - min s 1 / 2
  have hv : 0 < v := by dsimp [v, γ]; positivity
  have hq : 0 < q := by dsimp [q, γ]; positivity
  have hεquarter : ε ≤ 1/4 := by
    have hh := hεs.trans_le
      (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
    have hσnonneg : 0 ≤ min s 1 / 2 := by positivity
    linarith
  have hvle : v ≤ 4 := by
    dsimp [v, γ]
    apply (div_le_iff₀ (by linarith : 0 < 1 - (min s 1 / 2 + ε))).mpr
    linarith [min_le_right s 1]
  have hloss : 1 / (1 - (min s 1 / 2 + ε)) + K * (s + 1) + 2 ≤ κ := by
    change v + K * (s + 1) + 2 ≤ κ
    dsimp [κ]
    linarith
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
  refine ⟨C, hC, ?_⟩
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
      have hp := Real.rpow_le_rpow_of_exponent_le hn1
        (mul_le_mul_of_nonneg_right hloss hε.le)
      have hh' := hh.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp hH.le) (by positivity))
      apply hh'.trans
      change _ ≤ C * n ^ (κ * ε) *
        (InteractionDifferential.boundaryWeight s a.succPNat j + n * (e + a + 1 : ℝ) ^ (-s))
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hHC hP) (by positivity)
    · have hh := internal_polynomial_fine s ε K B q hs hε.le (by linarith) hB.le a f hphysical j
      have hsmall : n ≤ (nbar : ℝ) := by
        dsimp only [n]
        exact_mod_cast (show a + 1 ≤ nbar by dsimp [nbar]; omega)
      have hexp : q + 1 + K * ε * (s + 1) + s - min s 1 / 2 ≤ R + κ * ε := by
        have hqv : q = 1 + ε * v := by dsimp [q, v]; ring
        dsimp only [R, κ]
        rw [hqv]
        nlinarith only [mul_le_mul_of_nonneg_right hvle hε.le, hε]
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

end Riesz2.InterpolantLocalLaws

namespace Riesz2.CompatibleComparison

/-- See the proof of Proposition 6.6 in the paper:
the actual pinned coefficients for every specified physical endpoint realization
satisfy the fine-event bound and the global squared bound. The loss is chosen
before `ε`, depending only on `s,K`. The prefactor then precedes sizes,
temperature, cutoffs and admissible compatible exteriors. -/
theorem physical_differential_bounds_uniform_internal (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (K : ℝ) (hK : 1 < K) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε →
      ε < min (1-min s 1/2) (s-min s 1/2)/4 →
    ∃ C : ℝ, 0 < C ∧ ∀ a d e : ℕ, 1 ≤ a →
      4*(a+1) ≤ d+1+a+1 → d ≤ e →
      (a+1 : ℝ)^(2/s) ≤ (d+1+a+1 : ℝ) →
    ∀ (p : Parameters), p.val.2 = s →
    ∀ (θ : PhysicalCutoff) (A L : ℝ), 1 < A →
    ∀ (y : AffineSimplex.chartDomain (d+1) ((d+1+a : ℕ)+1))
      (z : AffineSimplex.chartDomain (e+1) ((e+1+a : ℕ)+1)),
      InterpolantLocalLaws.admissibleExterior p (d+1) a (by omega) θ ε A K y →
      InterpolantLocalLaws.admissibleExterior p (e+1) a (by omega) θ ε A K z →
      ((d+1+a : ℕ)+1 : ℝ)-∑ i, y.val i = L →
      ((e+1+a : ℕ)+1 : ℝ)-∑ i, z.val i = L →
    ∀ (Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ),
      (∀ u (hu : RetainedSimplex.assemble (d+1) a
        (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u ∈
          gapAmbientDomain (d+1+a).succPNat),
        Ky u = physicalAmbientGapEnergy p (d+1+a).succPNat
          ⟨RetainedSimplex.assemble (d+1) a
            (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u,hu⟩) →
      (∀ u (hu : RetainedSimplex.assemble (e+1) a
        (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u ∈
          gapAmbientDomain (e+1+a).succPNat),
        Kz u = physicalAmbientGapEnergy p (e+1+a).succPNat
          ⟨RetainedSimplex.assemble (e+1) a
            (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u,hu⟩) →
    ∀ u ∈ AffineSimplex.massSimplex a L,
    let b := InteractionDifferential.pinnedRepresentative (fun i : Fin a =>
      fderiv ℝ (fun v => Ky v-Kz v) u
        (WithLp.toLp 2 (Pi.single i.castSucc 1-Pi.single i.succ 1)))
    ; (WithLp.ofLp u ∈ goodBlockEvent s a.succPNat (d+1+a).succPNat (K*ε) →
        ∀ j, |b j| ≤ C*(a+1 : ℝ)^(κ*ε)*
          (InteractionDifferential.boundaryWeight s a.succPNat j+
            (a+1 : ℝ)*(d+1+a+1 : ℝ)^(-s))) ∧
      (∀ j, b j^2 ≤ C*(a+1 : ℝ)^C*
        InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s (WithLp.ofLp u)) := by
  obtain ⟨κ,hκ,hmain⟩ := InterpolantLocalLaws.interaction_differential_uniform_internal
    s hs hs1 K hK
  refine ⟨κ,hκ,?_⟩
  intro ε hε hεs
  obtain ⟨C,hC,hmain⟩ := hmain ε hε hεs
  refine ⟨C,hC,?_⟩
  intro a d e ha hsize hde hpower p hps
  obtain ⟨WN,WM,hWN,hWM,hvN,hvM,hbound⟩ :=
    hmain a (d+1) (e+1) ha hsize (by omega) (by simpa only [Nat.cast_add,Nat.cast_one] using hpower) p hps
  intro θ A L hA y z hy hz hyL hzL Ky Kz hKy hKz u hu b
  have hcy : (∑ i, y.val i)+L = (↑(d+1)+a+1 : ℝ) := by
    simp only [Nat.cast_add,Nat.cast_one] at hyL ⊢
    linarith only [hyL]
  have hcz : (∑ i, z.val i)+L = (↑(e+1)+a+1 : ℝ) := by
    simp only [Nat.cast_add,Nat.cast_one] at hzL ⊢
    linarith only [hzL]
  have hgy : InterpolantLocalLaws.exteriorGeometry s ε (d+1) a y.val := by
    simpa only [hps] using hy.1
  have hgz : InterpolantLocalLaws.exteriorGeometry s ε (e+1) a z.val := by
    simpa only [hps] using hz.1
  have hlength : |L-(a+1 : ℝ)| ≤ (a+1 : ℝ)^(min s 1/2+ε) := by
    have hh := hgy.1
    simp only [Nat.cast_add,Nat.cast_one] at hh hyL
    rwa [hyL] at hh
  have hbound' := hbound L y.val z.val y.property.1 z.property.1 hcy hcz hlength
    (fun r hr hre => (InterpolantLocalLaws.exteriorGeometry_ordinary s ε (d+1) a
      y.val hgy r hr hre).1)
    (fun r hr hre => (InterpolantLocalLaws.exteriorGeometry_ordinary s ε (d+1) a
      y.val hgy r hr hre).2)
    (fun r hr hre => (InterpolantLocalLaws.exteriorGeometry_ordinary s ε (e+1) a
      z.val hgz r hr hre).1)
    (fun r hr hre => (InterpolantLocalLaws.exteriorGeometry_ordinary s ε (e+1) a
      z.val hgz r hr hre).2)
    u hu.1 hu.2
  have hdiff : (fun v => Ky v-Kz v) =ᶠ[𝓝 u]
      (fun v => WN (RetainedSimplex.assemble (d+1) a
        (InterpolatingDensities.exteriorPermutation (d+1) a) y.val v)-
        WM (RetainedSimplex.assemble (e+1) a
          (InterpolatingDensities.exteriorPermutation (e+1) a) z.val v)) := by
    have hyOpen := (PhysicalEnergy.isOpen_gapAmbientDomain (d+1+a).succPNat).preimage
      (RetainedSimplex.continuous_assemble (d+1) a
        (InterpolatingDensities.exteriorPermutation (d+1) a) y.val)
    have hzOpen := (PhysicalEnergy.isOpen_gapAmbientDomain (e+1+a).succPNat).preimage
      (RetainedSimplex.continuous_assemble (e+1) a
        (InterpolatingDensities.exteriorPermutation (e+1) a) z.val)
    filter_upwards [hyOpen.mem_nhds
      (InterpolationCoefficientBounds.fibre_mem_internal (d+1) a y L hyL hu),
      hzOpen.mem_nhds
      (InterpolationCoefficientBounds.fibre_mem_internal (e+1) a z L hzL hu)] with v hv hw
    exact congrArg₂ (fun x y : ℝ => x-y)
      ((hKy v hv).trans (hvN ⟨_,hv⟩).symm)
      ((hKz v hw).trans (hvM ⟨_,hw⟩).symm)
  have he := hdiff.fderiv_eq (𝕜 := ℝ)
  refine ⟨?_,?_⟩
  · simpa only [b,he,Nat.cast_add,Nat.cast_one] using hbound'.2.2.1
  · intro j
    have hsum := hbound'.2.2.2.1
    simp only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs] at hsum
    apply (Finset.single_le_sum (fun i _ => sq_nonneg
      (InteractionDifferential.pinnedRepresentative _ i)) (Finset.mem_univ j)).trans
    simpa only [b,he] using hsum

end Riesz2.CompatibleComparison
