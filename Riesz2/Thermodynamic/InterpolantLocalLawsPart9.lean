/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.InterpolantLocalLawsPart7
public import Riesz2.ToMathlib.SubcriticalPowerSum
public import Riesz2.ToMathlib.RpowPartialSums
public import Riesz2.Thermodynamic.IntegratedCovariancePart2

/-!
# Rigidity-segment estimates for the exterior interaction

Physical assembly and boundary power sums for Appendix C and the proof of Proposition
6.6.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff
open Filter

namespace Riesz2.InterpolantLocalLaws

/-- See Subsection 6.1 of the paper: the existing fixed-exterior assembly is a
physical mass simplex point whenever its two blocks have the prescribed masses. -/
theorem assembled_physical_simplex (e a : ℕ)
    (y : EuclideanSpace ℝ (Fin e)) (u : EuclideanSpace ℝ (Fin (a + 1)))
    (hy : ∀ j, 0 < y j) (hu : ∀ j, 0 < u j)
    (hmass : (∑ j, y j) + (∑ j, u j) = (e + a + 1 : ℕ)) :
    WithLp.ofLp (RetainedSimplex.assemble e a
      (InterpolatingDensities.exteriorPermutation e a) y u) ∈
      Riesz1.gapSimplex (e + a).succPNat := by
  constructor
  · intro k
    have hklt : k.val < e + a + 1 := k.isLt
    by_cases hk : k.val < a + 1
    · have heq : k = Fin.castLE (show a + 1 ≤ e + a + 1 by omega) ⟨k.val, hk⟩ := by
        apply Fin.ext; rfl
      rw [heq]
      exact (InterpolatingDensities.assemble_exterior_active e a y u ⟨k.val, hk⟩
        (by omega)) ▸ hu _
    · have heq : k = (⟨a + 1 + (k.val - (a + 1)), by have := k.isLt; omega⟩ :
          Fin (e + a + 1)) := by apply Fin.ext; dsimp only; omega
      rw [heq]
      exact (assemble_exterior_retained e a y u
        ⟨k.val - (a + 1), by have hklt : k.val < e + a + 1 := k.isLt; omega⟩) ▸ hy _
  · change (∑ j, RetainedSimplex.assemble e a
      (InterpolatingDensities.exteriorPermutation e a) y u j) = _
    simpa only [id_eq, Nat.succPNat_coe] using
      (IntegratedCovariance.sum_assemble e a
        (InterpolatingDensities.exteriorPermutation e a) y u id).trans hmass

/-- See Appendix C in the paper: a rigidity cutoff bounds every
positive ordinary interval from below by its length times the cutoff. -/
theorem goodBlockEvent_interval_lower (s η : ℝ) (n N : ℕ+)
    (x : Fin (n : ℕ) → ℝ) (hx : x ∈ goodBlockEvent s n N η)
    (i r : ℕ) (hir : i + r ≤ (n : ℕ)) :
    (r : ℝ) * (n : ℝ) ^ (-η) ≤
      ∑ k : Fin r, x ⟨i + k.val, by have := k.isLt; omega⟩ := by
  calc
    _ = ∑ _k : Fin r, (n : ℝ) ^ (-η) := by simp
    _ ≤ _ := Finset.sum_le_sum fun k _ => (hx.2.1 _).1

/-- Internal power bookkeeping in Appendix C:
a lower cutoff converts a negative boundary power into a rank power. -/
theorem internal_cutoff_rpow {n r a η q : ℝ} (hn : 0 < n) (hr : 0 < r)
    (hq : q ≤ 0) (ha : r * n ^ (-η) ≤ a) :
    a ^ q ≤ n ^ (-η * q) * r ^ q := by
  have h := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < r * n ^ (-η)) ha hq
  apply h.trans_eq
  rw [Real.mul_rpow hr.le (Real.rpow_nonneg hn.le _), ← Real.rpow_mul hn.le]
  ring

/-- The two boundary families have identical rank sums. The minimum
prefix-displacement weight is no larger than either boundary rank.
This is the finite sum in Appendix C. -/
theorem internal_two_boundary_power_sum (a : ℕ) (σ q : ℝ) (hσ : 0 ≤ σ) :
    (∑ i : Fin a, (((i.val + 1 : ℝ) ^ q + ((a - i.val : ℕ) : ℝ) ^ q) *
      ((min (i.val + 1) (a - i.val) : ℕ) : ℝ) ^ σ)) ≤
      2 * ∑ i : Fin a, (i.val + 1 : ℝ) ^ (q + σ) := by
  have hleft (i : Fin a) :
      ((min (i.val + 1) (a - i.val) : ℕ) : ℝ) ^ σ ≤ (i.val + 1 : ℝ) ^ σ := by
    apply Real.rpow_le_rpow (by positivity) _ hσ
    exact_mod_cast min_le_left (i.val + 1) (a - i.val)
  have hright (i : Fin a) :
      ((min (i.val + 1) (a - i.val) : ℕ) : ℝ) ^ σ ≤ ((a - i.val : ℕ) : ℝ) ^ σ := by
    apply Real.rpow_le_rpow (by positivity) _ hσ
    exact_mod_cast min_le_right (i.val + 1) (a - i.val)
  calc
    _ ≤ ∑ i : Fin a, ((i.val + 1 : ℝ) ^ (q + σ) + ((a - i.val : ℕ) : ℝ) ^ (q + σ)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [add_mul, Real.rpow_add (by positivity : 0 < (i.val + 1 : ℝ)),
        Real.rpow_add (by exact_mod_cast (Nat.sub_pos_of_lt i.isLt) :
          (0 : ℝ) < (a - i.val : ℕ))]
      exact add_le_add (mul_le_mul_of_nonneg_left (hleft i) (by positivity))
        (mul_le_mul_of_nonneg_left (hright i) (by positivity))
    _ = _ := by
      rw [Finset.sum_add_distrib]
      have he := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin a))
        (fun i : Fin a => (i.val + 1 : ℝ) ^ (q + σ))
      have hr : (∑ i : Fin a, ((a - i.val : ℕ) : ℝ) ^ (q + σ)) =
          ∑ i : Fin a, (i.val + 1 : ℝ) ^ (q + σ) := by
        rw [← he]
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        simp only [Fin.revPerm_apply, Fin.val_rev]
        have hi := i.isLt
        exact_mod_cast (show a - i.val = a - (i.val + 1) + 1 by omega)
      rw [hr]
      ring

/-- The convergent boundary series in Appendix C has a constant depending only on the exponent. -/
theorem internal_summable_boundary (s σ : ℝ) (hσs : σ < s) (a : ℕ) :
    (∑ i : Fin a, (i.val + 1 : ℝ) ^ (σ - s - 1)) ≤
      ∑' k : ℕ, (k : ℝ) ^ (σ - s - 1) := by
  have hs : Summable (fun k : ℕ => (k : ℝ) ^ (σ - s - 1)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  apply (Finset.sum_le_sum_of_injOn (fun i : Fin a => i.val + 1)
    (by intro i _ j _ h; apply Fin.ext; dsimp only at h; omega)
    (by intro k hk; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
        exact Finset.mem_range.mpr (by have := i.isLt; omega))
    (by intro i _; simp only [Nat.cast_add, Nat.cast_one, le_refl])
    (by intro _ _ _; positivity) :
      (∑ i : Fin a, (i.val + 1 : ℝ) ^ (σ - s - 1)) ≤
        ∑ k ∈ Finset.range (a + 1), (k : ℝ) ^ (σ - s - 1)).trans
  exact hs.sum_le_tsum _ (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- The second boundary sum in Appendix C.
The constant may depend on the positive tolerance. Its power is exactly ε. -/
theorem internal_critical_boundary (s σ ε : ℝ) (hσs : 2 * σ ≤ s)
    (hε : 0 < ε) (hε1 : ε < 1) (a : ℕ) :
    (∑ i : Fin a, (i.val + 1 : ℝ) ^ (2 * σ + ε - s - 1)) ≤
      (a + 1 : ℝ) ^ ε / ε := by
  have hsum : (∑ i : Fin a, (i.val + 1 : ℝ) ^ (2 * σ + ε - s - 1)) ≤
      ∑ r ∈ Finset.Icc 1 (a + 1), (r : ℝ) ^ (-(1 - ε)) := by
    apply Finset.sum_le_sum_of_injOn (fun i : Fin a => i.val + 1)
      (by intro i _ j _ h; apply Fin.ext; dsimp only at h; omega) ?_ ?_
    · intro _ _ _; positivity
    · intro k hk
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
      exact Finset.mem_Icc.mpr ⟨by omega, by have := i.isLt; omega⟩
    · intro i _
      simp only [Nat.cast_add, Nat.cast_one]
      apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ i.val + 1 by omega))
      linarith
  apply hsum.trans
  convert (subcritical_power_sum (s := 1 - ε) (by linarith) (by linarith)
    (show 1 ≤ a + 1 by omega)).2 using 1;
    simp only [Nat.cast_add, Nat.cast_one, show 1 - (1 - ε) = ε by ring]

/-- Internal cutoff specialization of the physical two-boundary force bound
in Appendix C. -/
theorem internal_force_cutoff {s γ η C T A n r l a b F E : ℝ}
    (hn : 0 < n) (hr : 0 < r) (hl : 0 < l) (hs : 0 < s)
    (hγ : γ < s + 1) (hC : 0 ≤ C) (hT : 0 ≤ T) (hA : 0 ≤ A)
    (ha : r * n ^ (-η) ≤ a) (hb : l * n ^ (-η) ≤ b)
    (hF : |F| ≤ C * (T * a ^ (-s - 1) + A * a ^ (γ - s - 1) +
      (T * b ^ (-s - 1) + A * b ^ (γ - s - 1))) + E) :
    |F| ≤ C * (T * n ^ (η * (s + 1)) * (r ^ (-s - 1) + l ^ (-s - 1)) +
      A * n ^ (η * (s + 1 - γ)) * (r ^ (γ - s - 1) + l ^ (γ - s - 1))) + E := by
  have h₁ := internal_cutoff_rpow hn hr (by linarith : -s - 1 ≤ 0) ha
  have h₂ := internal_cutoff_rpow hn hl (by linarith : -s - 1 ≤ 0) hb
  have h₃ := internal_cutoff_rpow hn hr (by linarith : γ - s - 1 ≤ 0) ha
  have h₄ := internal_cutoff_rpow hn hl (by linarith : γ - s - 1 ≤ 0) hb
  rw [show -η * (-s - 1) = η * (s + 1) by ring] at h₁ h₂
  rw [show -η * (γ - s - 1) = η * (s + 1 - γ) by ring] at h₃ h₄
  apply hF.trans
  refine add_le_add ?_ le_rfl
  apply mul_le_mul_of_nonneg_left _ hC
  have ht₁ := mul_le_mul_of_nonneg_left h₁ hT
  have ht₂ := mul_le_mul_of_nonneg_left h₂ hT
  have ht₃ := mul_le_mul_of_nonneg_left h₃ hA
  have ht₄ := mul_le_mul_of_nonneg_left h₄ hA
  nlinarith

/-- Smoothness of the literal assembly of Subsection 6.1 as a function of
its active block. This is a bridge to the existing concatenation map. -/
theorem contDiff_exterior_assembly (e a : ℕ) (y : EuclideanSpace ℝ (Fin e)) :
    ContDiff ℝ ∞ (RetainedSimplex.assemble e a
      (InterpolatingDensities.exteriorPermutation e a) y) := by
  let E := EuclideanSpace ℝ (Fin e)
  let F := EuclideanSpace ℝ (Fin (a + 1))
  have : ContinuousSMul ℝ (E × F) := Prod.continuousSMul
  exact (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (InterpolatingDensities.exteriorPermutation e a)).contDiff.comp
    ((RetainedSimplex.join e (a + 1)).toContinuousLinearEquiv.contDiff.comp
      (contDiff_const.prodMk contDiff_id))

/-- The physical left exterior prefix of Subsection 6.1, expressed in the
existing assembly. The full exterior rank is included. -/
theorem assembled_exterior_left (e a r : ℕ) (hr : 0 < r) (hre : r ≤ e)
    (y : EuclideanSpace ℝ (Fin e)) (u : EuclideanSpace ℝ (Fin (a + 1))) :
    cyclicGapSum (e + a).succPNat
      ⟨e + a + 1 - r, by change e + a + 1 - r < e + a + 1; omega⟩ r
      (WithLp.ofLp (RetainedSimplex.assemble e a
        (InterpolatingDensities.exteriorPermutation e a) y u)) =
      ∑ k : Fin r, y ⟨e - r + k.val, by have := k.isLt; omega⟩ := by
  rw [cyclicGapSum_nonwrapping _ _ r (by change e + a + 1 - r + r ≤ e + a + 1; omega)]
  apply Finset.sum_congr rfl
  intro k _
  have hidx : (⟨e + a + 1 - r + k.val, by have := k.isLt; omega⟩ : Fin (e + a + 1)) =
      ⟨a + 1 + (e - r + k.val), by have := k.isLt; omega⟩ := by
    apply Fin.ext; dsimp only; omega
  rw [hidx]
  exact assemble_exterior_retained e a y u ⟨e - r + k.val, by have := k.isLt; omega⟩

/-- The physical force clause of Appendix C
on the actual common active simplex. Smooth realizations agree with the
ambient energies on their whole domains, and the force is the
derivative of their literal fixed-exterior difference. -/
theorem exterior_force_on_common_simplex (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
      ε < min (1 - min s 1 / 2) (s - min s 1 / 2) / 4 →
      ∃ n₀ : ℕ, ∀ (a e d : ℕ), n₀ ≤ a + 1 → 1 ≤ a →
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
      ∀ (u : EuclideanSpace ℝ (Fin (a + 1))), (∀ k, 0 < u k) → (∑ k, u k) = L →
      DifferentiableAt ℝ D u ∧ ∀ i : Fin a,
        let b := ∑ k : Fin (i.val + 1), u ⟨k.val, by have := k.isLt; omega⟩
        let c := ∑ k : Fin (a - i.val), u ⟨i.val + 1 + k.val, by have := i.isLt; have := k.isLt; omega⟩
        let T := (16 * (a + 1 : ℝ) ^ ε) ^ (1 / (1 - (min s 1 / 2 + ε)))
        |fderiv ℝ D u (WithLp.toLp 2 (Pi.single i.castSucc 1 - Pi.single i.succ 1))| ≤
          C * (T * c ^ (-s - 1) + (a + 1 : ℝ) ^ ε * c ^ (min s 1 / 2 + ε - s - 1) +
            (T * b ^ (-s - 1) + (a + 1 : ℝ) ^ ε * b ^ (min s 1 / 2 + ε - s - 1))) +
          C * (e + a + 1 : ℝ) ^ (-s) := by
  obtain ⟨C, hC, hf⟩ := exterior_force_difference s hs hs1
  refine ⟨C, hC, ?_⟩
  intro ε hε hεs
  obtain ⟨n₀, hn₀⟩ := hf ε hε hεs
  refine ⟨n₀, ?_⟩
  intro a e d hnn ha hN hed hsize p hps
  have he : 0 < e := by omega
  have hd : 0 < d := by omega
  have hex := hn₀ (a + 1) (e + a).succPNat (d + a).succPNat
    hnn (by omega) hN (by change e + a + 1 ≤ d + a + 1; omega)
    (by simpa only [Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using hsize)
  change ∃ WN : EuclideanSpace ℝ (Fin (e + a + 1)) → ℝ,
    ∃ WM : EuclideanSpace ℝ (Fin (d + a + 1)) → ℝ, _ at hex
  obtain ⟨WN, WM, hW⟩ := hex
  obtain ⟨hWN, hWM, hvN, hvM, hforce⟩ := hW p hps
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
  intro i
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
  have hh := hforce (i.val + 1) (by omega) (by have := i.isLt; omega)
    (WithLp.ofLp X) hX (WithLp.ofLp Y) hY hcommon (by simpa only [Nat.cast_add, Nat.cast_one] using hlen)
    (by simpa only [Nat.cast_add, Nat.cast_one, X] using right e he y hYR)
    (by simpa only [Nat.cast_add, Nat.cast_one, X] using left e y hYL)
    (by simpa only [Nat.cast_add, Nat.cast_one, Y] using right d hd z hZR)
    (by simpa only [Nat.cast_add, Nat.cast_one, Y] using left d z hZL)
  dsimp only at hh
  rw [cyclicGapSum_assembled_active e a (i.val + 1)
      (a + 1 - (i.val + 1)) (by have := i.isLt; omega) (by omega),
] at hh
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
  simpa only [Nat.add_sub_add_right, Nat.add_sub_cancel, Nat.zero_add, Nat.succPNat_coe,
    Nat.cast_succ, Nat.cast_add, Nat.cast_one, X, Y, WithLp.toLp_ofLp] using hh

/-- Internal summation of the two boundary profiles in the oscillation
proof of Appendix C. The first series is
summable and the second has precisely the permitted tolerance loss. -/
theorem internal_weighted_force_sum (a : ℕ) (s σ ε C T E : ℝ)
    (_hs : 0 < s) (hσ : 0 ≤ σ) (hσs : σ < s) (h2σ : 2 * σ ≤ s)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : 0 ≤ C) (hT : 0 ≤ T) (hE : 0 ≤ E) :
    let n : ℝ := a + 1
    let B := fun i : Fin a => C *
      (T * n ^ (ε * (s + 1)) *
        ((i.val + 1 : ℝ) ^ (-s - 1) + ((a - i.val : ℕ) : ℝ) ^ (-s - 1)) +
       n ^ ε * n ^ (ε * (s + 1 - (σ + ε))) *
        ((i.val + 1 : ℝ) ^ (σ + ε - s - 1) +
          ((a - i.val : ℕ) : ℝ) ^ (σ + ε - s - 1))) + E
    2 * n ^ ε * (∑ i : Fin a, B i * ((min (i.val + 1) (a - i.val) : ℕ) : ℝ) ^ σ) ≤
      4 * C * (T * n ^ (ε * (s + 2)) * (∑' k : ℕ, (k : ℝ) ^ (σ - s - 1)) +
        n ^ (ε * (s + 4 - (σ + ε))) / ε) +
        2 * E * n ^ (ε + 1 + σ) := by
  intro n B
  have hn : 0 < n := by dsimp [n]; positivity
  let w := fun i : Fin a => ((min (i.val + 1) (a - i.val) : ℕ) : ℝ) ^ σ
  let U := T * n ^ (ε * (s + 1))
  let V := n ^ ε * n ^ (ε * (s + 1 - (σ + ε)))
  let S₁ := ∑ i : Fin a, ((i.val + 1 : ℝ) ^ (-s - 1) +
    ((a - i.val : ℕ) : ℝ) ^ (-s - 1)) * w i
  let S₂ := ∑ i : Fin a, ((i.val + 1 : ℝ) ^ (σ + ε - s - 1) +
    ((a - i.val : ℕ) : ℝ) ^ (σ + ε - s - 1)) * w i
  have h₁ : S₁ ≤ 2 * ∑' k : ℕ, (k : ℝ) ^ (σ - s - 1) := by
    apply (internal_two_boundary_power_sum a σ (-s - 1) hσ).trans
    simpa only [show -s - 1 + σ = σ - s - 1 by ring] using
      mul_le_mul_of_nonneg_left (internal_summable_boundary s σ hσs a)
        (show (0 : ℝ) ≤ 2 by norm_num)
  have h₂ : S₂ ≤ 2 * (n ^ ε / ε) := by
    apply (internal_two_boundary_power_sum a σ (σ + ε - s - 1) hσ).trans
    simpa only [n, show σ + ε - s - 1 + σ = 2 * σ + ε - s - 1 by ring] using
      mul_le_mul_of_nonneg_left (internal_critical_boundary s σ ε h2σ hε hε1 a)
        (show (0 : ℝ) ≤ 2 by norm_num)
  have hw : (∑ i : Fin a, w i) ≤ n ^ (1 + σ) := by
    calc
      _ ≤ ∑ _i : Fin a, n ^ σ := by
        apply Finset.sum_le_sum
        intro i _
        apply Real.rpow_le_rpow (by positivity) _ hσ
        dsimp [n]
        exact_mod_cast (show min (i.val + 1) (a - i.val) ≤ a + 1 by omega)
      _ = (a : ℝ) * n ^ σ := by simp
      _ ≤ n * n ^ σ := mul_le_mul_of_nonneg_right (by dsimp [n]; linarith)
        (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [Real.rpow_add hn, Real.rpow_one]
  have heq : (∑ i : Fin a, B i * w i) = C * (U * S₁ + V * S₂) + E * ∑ i : Fin a, w i := by
    simp only [B, U, V, S₁, S₂, add_mul, mul_add, Finset.mul_sum,
      Finset.sum_add_distrib, mul_assoc]
  have hh : (∑ i : Fin a, B i * w i) ≤
      C * (U * (2 * ∑' k : ℕ, (k : ℝ) ^ (σ - s - 1)) + V * (2 * (n ^ ε / ε))) +
        E * n ^ (1 + σ) := by
    rw [heq]
    exact add_le_add (mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left h₁ (by dsimp [U]; positivity))
        (mul_le_mul_of_nonneg_left h₂ (by dsimp [V]; positivity))) hC)
      (mul_le_mul_of_nonneg_left hw hE)
  apply (mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2 * n ^ ε)).trans_eq
  dsimp only [U, V]
  have hp₁ : n ^ ε * n ^ (ε * (s + 1)) = n ^ (ε * (s + 2)) := by
    rw [← Real.rpow_add hn]; congr 1; ring
  have hp₂ : n ^ ε * (n ^ ε * n ^ (ε * (s + 1 - (σ + ε)))) * n ^ ε =
      n ^ (ε * (s + 4 - (σ + ε))) := by
    rw [← Real.rpow_add hn, ← Real.rpow_add hn, ← Real.rpow_add hn]
    congr 1; ring
  have hp₃ : n ^ ε * n ^ (1 + σ) = n ^ (ε + 1 + σ) := by
    rw [← Real.rpow_add hn]; congr 1; ring
  linear_combination 4 * C * T * (∑' k : ℕ, (k : ℝ) ^ (σ - s - 1)) * hp₁ +
    4 * C / ε * hp₂ + 2 * E * hp₃

/-- The period term in the oscillation proof of
Appendix C is at most the cutoff power, uniformly
in every allowed volume. -/
theorem internal_oscillation_period {s σ ε n N : ℝ} (hs : 0 < s)
    (hσ : σ ≤ 1) (hn : 1 ≤ n) (hN : 0 < N) (hsize : n ^ (2 / s) ≤ N) :
    N ^ (-s) * n ^ (ε + 1 + σ) ≤ n ^ ε := by
  have hnp : 0 < n := by linarith
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg hnp.le _) hsize hs.le
  rw [← Real.rpow_mul hnp.le, div_mul_cancel₀ _ hs.ne'] at hp
  have hi := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hnp 2) hp
    (show (-1 : ℝ) ≤ 0 by norm_num)
  rw [← Real.rpow_mul hN.le, ← Real.rpow_mul hnp.le] at hi
  norm_num only [mul_neg_one] at hi
  calc
    _ ≤ n ^ (-2 : ℝ) * n ^ (ε + 1 + σ) :=
      mul_le_mul_of_nonneg_right hi (by positivity)
    _ = n ^ (ε - 1 + σ) := by rw [← Real.rpow_add hnp]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn (by linarith)

/-- Uniform choice of the loss exponent before the tolerance and temperature
in Appendix C. Constants depending on ε
are absorbed only into the eventual size threshold. -/
theorem internal_coarse_power_absorption (s σ C : ℝ) (hs : 0 < s)
    (hσ : 0 ≤ σ) (hσ1 : σ < 1) (hC : 0 ≤ C) :
    ∃ A_s : ℝ, 1 < A_s ∧ ∀ ε : ℝ, 0 < ε → ε < (1 - σ) / 4 →
      ∃ n₀ : ℕ, ∀ (n : ℕ), n₀ ≤ n → 2 ≤ n → ∀ N : ℝ, 0 < N →
        (n : ℝ) ^ (2 / s) ≤ N →
        4 * C * (((16 * (n : ℝ) ^ ε) ^ (1 / (1 - (σ + ε)))) *
          (n : ℝ) ^ (ε * (s + 2)) * (∑' k : ℕ, (k : ℝ) ^ (σ - s - 1)) +
          (n : ℝ) ^ (ε * (s + 4 - (σ + ε))) / ε) +
          2 * (C * N ^ (-s)) * (n : ℝ) ^ (ε + 1 + σ) ≤
        (n : ℝ) ^ (A_s * ε) := by
  let q := 2 / (1 - σ)
  let Q := s + 5 + q
  have hq : 0 < q := by dsimp [q]; positivity
  refine ⟨Q + 1, by dsimp [Q]; linarith, ?_⟩
  intro ε hε hεσ
  let S := ∑' k : ℕ, (k : ℝ) ^ (σ - s - 1)
  have hS : 0 ≤ S := tsum_nonneg fun k => Real.rpow_nonneg (Nat.cast_nonneg _) _
  let K := 4 * C * (16 ^ q * S + 1 / ε) + 2 * C
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (ht.eventually_ge_atTop K)
  refine ⟨n₀, ?_⟩
  intro n hnn hn N hN hsize
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hden : 0 < 1 - (σ + ε) := by linarith
  have hqe : 1 / (1 - (σ + ε)) ≤ q := by
    dsimp [q]
    rw [div_le_div_iff₀ hden (by linarith : 0 < 1 - σ)]
    linarith
  have hT : (16 * (n : ℝ) ^ ε) ^ (1 / (1 - (σ + ε))) ≤
      16 ^ q * (n : ℝ) ^ (ε * q) := by
    calc
      _ ≤ (16 * (n : ℝ) ^ ε) ^ q := Real.rpow_le_rpow_of_exponent_le
        (by nlinarith [Real.one_le_rpow hn1 hε.le]) hqe
      _ = _ := by rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hnp.le]
  have hfirst : ((16 * (n : ℝ) ^ ε) ^ (1 / (1 - (σ + ε)))) *
      (n : ℝ) ^ (ε * (s + 2)) * S ≤
      16 ^ q * S * (n : ℝ) ^ (ε * Q) := by
    calc
      _ ≤ (16 ^ q * (n : ℝ) ^ (ε * q)) * (n : ℝ) ^ (ε * (s + 2)) * S :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hT (by positivity)) hS
      _ = 16 ^ q * S * (n : ℝ) ^ (ε * (q + s + 2)) := by
        rw [show ε * (q + s + 2) = ε * q + ε * (s + 2) by ring,
          Real.rpow_add hnp]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [Q]; nlinarith)) (by positivity)
  have hsecond : (n : ℝ) ^ (ε * (s + 4 - (σ + ε))) / ε ≤
      (1 / ε) * (n : ℝ) ^ (ε * Q) := by
    rw [one_div_mul_eq_div]
    apply div_le_div_of_nonneg_right _ hε.le
    apply Real.rpow_le_rpow_of_exponent_le hn1
    dsimp [Q]
    nlinarith
  have hperiod := internal_oscillation_period hs hσ1.le hn1 hN hsize (ε := ε)
  have hQ : ε ≤ ε * Q := by dsimp [Q]; nlinarith
  have hper : 2 * (C * N ^ (-s)) * (n : ℝ) ^ (ε + 1 + σ) ≤
      2 * C * (n : ℝ) ^ (ε * Q) := by
    have hh := hperiod.trans (Real.rpow_le_rpow_of_exponent_le hn1 hQ)
    nlinarith [mul_le_mul_of_nonneg_left hh (show 0 ≤ 2 * C by positivity)]
  calc
    _ ≤ K * (n : ℝ) ^ (ε * Q) := by
      have hh := mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond)
        (show 0 ≤ 4 * C by positivity)
      dsimp only [S] at hfirst
      dsimp only [K]
      nlinarith
    _ ≤ (n : ℝ) ^ ε * (n : ℝ) ^ (ε * Q) :=
      mul_le_mul_of_nonneg_right (hn₀ n hnn) (by positivity)
    _ = _ := by rw [← Real.rpow_add hnp]; congr 1; ring

/-- Internal rigidity-segment specialization for
Appendix C. This proves the full power-series bound
from the pinned force interface, with no norm comparison loss. -/
theorem internal_coarse_segment (a : ℕ) (N : ℕ+) (s ε C : ℝ)
    (hs : 0 < s) (hε : 0 < ε)
    (hεs : ε < min (1 - min s 1 / 2) (s - min s 1 / 2) / 4) (hC : 0 ≤ C)
    (f : EuclideanSpace ℝ (Fin (a + 1)) → ℝ)
    (x y : EuclideanSpace ℝ (Fin (a + 1)))
    (hx : WithLp.ofLp x ∈ goodBlockEvent s a.succPNat N ε)
    (hy : WithLp.ofLp y ∈ goodBlockEvent s a.succPNat N ε)
    (hmass : ∑ j, x j = ∑ j, y j)
    (hf : ∀ u : EuclideanSpace ℝ (Fin (a + 1)),
      WithLp.ofLp u ∈ goodBlockEvent s a.succPNat N ε →
      (∑ j, u j) = ∑ j, x j →
      DifferentiableAt ℝ f u ∧ ∀ i : Fin a,
        let b := ∑ k : Fin (i.val + 1), u ⟨k.val, by have := k.isLt; omega⟩
        let c := ∑ k : Fin (a - i.val), u ⟨i.val + 1 + k.val, by have := i.isLt; have := k.isLt; omega⟩
        let T := (16 * (a + 1 : ℝ) ^ ε) ^ (1 / (1 - (min s 1 / 2 + ε)))
        |fderiv ℝ f u (WithLp.toLp 2 (Pi.single i.castSucc 1 - Pi.single i.succ 1))| ≤
          C * (T * c ^ (-s - 1) + (a + 1 : ℝ) ^ ε * c ^ (min s 1 / 2 + ε - s - 1) +
            (T * b ^ (-s - 1) + (a + 1 : ℝ) ^ ε * b ^ (min s 1 / 2 + ε - s - 1))) +
          C * (N : ℝ) ^ (-s)) :
    |f y - f x| ≤
      4 * C * (((16 * (a + 1 : ℝ) ^ ε) ^ (1 / (1 - (min s 1 / 2 + ε)))) *
        (a + 1 : ℝ) ^ (ε * (s + 2)) * (∑' k : ℕ, (k : ℝ) ^ (min s 1 / 2 - s - 1)) +
        (a + 1 : ℝ) ^ (ε * (s + 4 - (min s 1 / 2 + ε))) / ε) +
        2 * (C * (N : ℝ) ^ (-s)) * (a + 1 : ℝ) ^ (ε + 1 + min s 1 / 2) := by
  let n : ℝ := a + 1
  let σ := min s 1 / 2
  let γ := σ + ε
  let T := (16 * n ^ ε) ^ (1 / (1 - γ))
  let B := fun i : Fin a => C *
    (T * n ^ (ε * (s + 1)) *
      ((i.val + 1 : ℝ) ^ (-s - 1) + ((a - i.val : ℕ) : ℝ) ^ (-s - 1)) +
     n ^ ε * n ^ (ε * (s + 1 - γ)) *
      ((i.val + 1 : ℝ) ^ (γ - s - 1) + ((a - i.val : ℕ) : ℝ) ^ (γ - s - 1))) +
      C * (N : ℝ) ^ (-s)
  have hσ : 0 ≤ σ := by dsimp [σ]; positivity
  have hσs : σ < s := by dsimp [σ]; linarith [min_le_left s 1]
  have h2σ : 2 * σ ≤ s := by dsimp [σ]; linarith [min_le_left s 1]
  have hγs : γ < s + 1 := by
    have hh := hεs.trans_le (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
    dsimp [γ, σ]; linarith
  have hε1 : ε < 1 := by
    have hh := hεs.trans_le (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
    dsimp [σ] at hσ
    linarith
  have hB : ∀ u : EuclideanSpace ℝ (Fin (a + 1)),
      WithLp.ofLp u ∈ goodBlockEvent s a.succPNat N ε →
      (∑ j, u j) = ∑ j, x j → ∀ i : Fin a,
      |fderiv ℝ f u (WithLp.toLp 2 (Pi.single i.castSucc 1 - Pi.single i.succ 1))| ≤ B i := by
    intro u hu hmass i
    have hright := goodBlockEvent_interval_lower s ε a.succPNat N (WithLp.ofLp u) hu
      (i.val + 1) (a - i.val) (by change i.val + 1 + (a - i.val) ≤ a + 1; have := i.isLt; omega)
    have hleft := goodBlockEvent_interval_lower s ε a.succPNat N (WithLp.ofLp u) hu
      0 (i.val + 1) (by change 0 + (i.val + 1) ≤ a + 1; have := i.isLt; omega)
    have hh := internal_force_cutoff (η := ε) (γ := γ) (n := n) (T := T) (A := n ^ ε)
      (by dsimp [n]; positivity)
      (by exact_mod_cast (Nat.sub_pos_of_lt i.isLt) : (0 : ℝ) < (a - i.val : ℕ))
      (by positivity : (0 : ℝ) < i.val + 1) hs hγs hC (by dsimp [T]; positivity)
      (by positivity : 0 ≤ n ^ ε)
      (by simpa only [n, Nat.succPNat_coe, Nat.cast_succ] using hright)
      (by simpa only [n, Nat.succPNat_coe, Nat.cast_succ, Nat.zero_add] using hleft)
      ((hf u hu hmass).2 i)
    apply hh.trans_eq
    dsimp only [B]
    ring
  have hh := internal_rigidity_segment_bound N s ε f x y hx hy hmass B
    (fun u hu hm => (hf u hu hm).1) hB
  apply hh.trans
  simpa only [B, n, T, γ, σ, Nat.succPNat_coe, Nat.cast_succ] using
    internal_weighted_force_sum a s σ ε C T (C * (N : ℝ) ^ (-s)) hs hσ hσs h2σ
      hε hε1 hC (by dsimp [T]; positivity) (by positivity)

/-- See Appendix C in the paper, both conclusions: the actual
pinned force difference on the positive common simplex and its coarse
oscillation on the rigidity event. The constants precede ε and β. The size threshold depends only on s and ε. -/
theorem exterior_force_and_coarse_oscillation (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ C A_s : ℝ, 0 < C ∧ 1 < A_s ∧ ∀ ε : ℝ, 0 < ε →
      ε < min (1 - min s 1 / 2) (s - min s 1 / 2) / 4 →
      ∃ n₀ : ℕ, ∀ (a e d : ℕ), n₀ ≤ a + 1 → 1 ≤ a →
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
      ∀ (u : EuclideanSpace ℝ (Fin (a + 1))), (∀ k, 0 < u k) → (∑ k, u k) = L →
      DifferentiableAt ℝ D u ∧ (∀ i : Fin a,
        let b := ∑ k : Fin (i.val + 1), u ⟨k.val, by have := k.isLt; omega⟩
        let c := ∑ k : Fin (a - i.val), u ⟨i.val + 1 + k.val, by have := i.isLt; have := k.isLt; omega⟩
        let T := (16 * (a + 1 : ℝ) ^ ε) ^ (1 / (1 - (min s 1 / 2 + ε)))
        |fderiv ℝ D u (WithLp.toLp 2 (Pi.single i.castSucc 1 - Pi.single i.succ 1))| ≤
          C * (T * c ^ (-s - 1) + (a + 1 : ℝ) ^ ε * c ^ (min s 1 / 2 + ε - s - 1) +
            (T * b ^ (-s - 1) + (a + 1 : ℝ) ^ ε * b ^ (min s 1 / 2 + ε - s - 1))) +
          C * (e + a + 1 : ℝ) ^ (-s)) ∧ (WithLp.ofLp u ∈ goodBlockEvent s a.succPNat (e + a).succPNat ε →
          ∀ v : EuclideanSpace ℝ (Fin (a + 1)),
          WithLp.ofLp v ∈ goodBlockEvent s a.succPNat (e + a).succPNat ε →
          (∑ k, v k) = L → |D v - D u| ≤ (a + 1 : ℝ) ^ (A_s * ε)) := by
  obtain ⟨C, hC, hforce⟩ := exterior_force_on_common_simplex s hs hs1
  have hσ : 0 ≤ min s 1 / 2 := by positivity
  have hσ1 : min s 1 / 2 < 1 := by linarith [min_le_right s 1]
  obtain ⟨A_s, hAs, hAbs⟩ := internal_coarse_power_absorption s (min s 1 / 2) C hs hσ hσ1 hC.le
  refine ⟨C, A_s, hC, hAs, ?_⟩
  intro ε hε hεs
  have hεσ : ε < (1 - min s 1 / 2) / 4 :=
    hεs.trans_le (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  obtain ⟨nF, hnF⟩ := hforce ε hε hεs
  obtain ⟨nA, hnA⟩ := hAbs ε hε hεσ
  refine ⟨max nF nA, ?_⟩
  intro a e d hnn ha hN hed hsize p hps
  obtain ⟨WN, WM, hWN, hWM, hvN, hvM, hbound⟩ := hnF a e d
    ((le_max_left _ _).trans hnn) ha hN hed hsize p hps
  refine ⟨WN, WM, hWN, hWM, hvN, hvM, ?_⟩
  intro L y z hy hz hmassY hmassZ hL hYR hYL hZR hZL D u hu hmass
  have hDu := hbound L y z hy hz hmassY hmassZ hL hYR hYL hZR hZL u hu hmass
  refine ⟨hDu.1, hDu.2, ?_⟩
  intro hgood v hv hvmass
  have hsegment := internal_coarse_segment a (e + a).succPNat s ε C hs hε hεs hC.le D u v
    hgood hv (hmass.trans hvmass.symm) ?_
  · apply hsegment.trans
    simpa only [Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using
      hnA (a + 1) ((le_max_right _ _).trans hnn) (by omega) (e + a + 1 : ℝ)
        (by positivity) (by simpa only [Nat.cast_add, Nat.cast_one] using hsize)
  · intro w hw hm
    have hpos : ∀ k, 0 < w k := fun k =>
      (Real.rpow_pos_of_pos (by exact_mod_cast a.succPNat.pos) (-ε)).trans_le (hw.2.1 k).1
    simpa only [D, Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using
      hbound L y z hy hz hmassY hmassZ hL hYR hYL hZR hZL w hpos (hm.trans hmass)

/-- Actual exterior-force bound at every source size, including fewer
ranks than the threshold. This is the bounded-size physical ingredient
of Appendix C and the proof of Proposition 6.6. -/
theorem physical_exterior_absolute_bound (p : Parameters) (N : ℕ+)
    (x : Fin (N : ℕ) → ℝ) (hx : x ∈ Riesz1.gapSimplex N)
    (n i : ℕ) (hi : 0 < i) (hin : i < n) (hn : n < (N : ℕ))
    (γ A : ℝ) (hγ : γ < 1) (hA : 1 ≤ A)
    (hR : ∀ r : ℕ, 0 < r → r ≤ (N : ℕ) - n →
      |cyclicGapSum N ⟨n, hn⟩ r x - r| ≤ 4 * A * (r : ℝ) ^ γ)
    (hL : ∀ r : ℕ, (hr : 0 < r) → (hrn : r ≤ (N : ℕ) - n) →
      |cyclicGapSum N ⟨(N : ℕ) - r, by omega⟩ r x - r| ≤ 4 * A * (r : ℝ) ^ γ) :
    |∑ r : Fin ((N : ℕ) - n - 1), intervalForce p N
        ⟨cyclicGapSum N ⟨i, by omega⟩ (n - i + r.val + 1) x,
          PhysicalEnergy.gapSum_mem N _ (by omega) (by have := r.isLt; omega) x hx⟩| ≤
      2 * p.val.2 * (16 * A) ^ (1 / (1 - γ)) *
        ((cyclicGapSum N ⟨i, by omega⟩ (n - i) x) ^ (-p.val.2 - 1) +
          (cyclicGapSum N 0 i x) ^ (-p.val.2 - 1)) +
      2 * (p.val.2 * 2 ^ (p.val.2 + 1) * ∑' k : ℕ, (k : ℝ) ^ (-p.val.2 - 1)) +
      (p.val.2 * 2 ^ (p.val.2 + 1) *
        (1 + ∑' k : ℤ, |(k : ℝ)| ^ (-p.val.2 - 1))) * (N : ℝ) ^ (-p.val.2) := by
  let m := (N : ℕ) - n - 1
  let a := cyclicGapSum N ⟨i, by omega⟩ (n - i) x
  let b := cyclicGapSum N 0 i x
  let Y := fun r : Fin m => cyclicGapSum N ⟨n, hn⟩ (r.val + 1) x
  let Z := fun r : Fin m => cyclicGapSum N
    ⟨(N : ℕ) - (r.val + 1), by have := r.isLt; dsimp [m] at *; omega⟩ (r.val + 1) x
  have hm (r : Fin m) : r.val + 1 < (N : ℕ) := by have := r.isLt; dsimp [m] at *; omega
  have hY0 (r : Fin m) : 0 ≤ Y r :=
    (PhysicalEnergy.gapSum_mem N _ (by omega) (hm r) x hx).1.le
  have hZ0 (r : Fin m) : 0 ≤ Z r :=
    (PhysicalEnergy.gapSum_mem N _ (by omega) (hm r) x hx).1.le
  have hY (r : Fin m) : |Y r - (r.val + 1 : ℝ)| ≤ 4 * A * (r.val + 1 : ℝ) ^ γ := by
    simpa only [Y, Nat.cast_add, Nat.cast_one] using
      hR (r.val + 1) (by omega) (by have := r.isLt; dsimp [m] at *; omega)
  have hZ (r : Fin m) : |Z r - (r.val + 1 : ℝ)| ≤ 4 * A * (r.val + 1 : ℝ) ^ γ := by
    simpa only [Z, Nat.cast_add, Nat.cast_one] using
      hL (r.val + 1) (by omega) (by have := r.isLt; dsimp [m] at *; omega)
  have hright := internal_principal_exterior_absolute_bound (a := a) p.property.2.1 hγ hA
    (PhysicalEnergy.gapSum_mem N ⟨i, by omega⟩ (by omega : 0 < n - i) (by omega) x hx).1 m Y hY0 hY
  have hleft := internal_principal_exterior_absolute_bound (a := b) p.property.2.1 hγ hA
    (PhysicalEnergy.gapSum_mem N 0 hi (by omega) x hx).1 m Z hZ0 hZ
  have herr := physical_exterior_two_boundary_error p N x hx n i hin hn
  dsimp only at herr
  have triangle (u v w P Q R : ℝ) (he : |u - (v - w)| ≤ R)
      (hv : |v| ≤ P) (hw : |w| ≤ Q) : |u| ≤ P + Q + R := by
    calc
      _ = |(u - (v - w)) + (v - w)| := by congr 1; ring
      _ ≤ |u - (v - w)| + |v - w| := abs_add_le _ _
      _ ≤ |u - (v - w)| + (|v| + |w|) := add_le_add le_rfl (abs_sub v w)
      _ ≤ _ := by linarith
  have hh := triangle _ _ _ _ _ _ herr hright hleft
  convert hh using 1
  ring

/-- The actual physical two-volume force at every source size, with
common-pair cancellation and absolute exterior bounds. Appendix C, bounded-size clause, and
the proof of Proposition 6.6, global-bound input. -/
theorem physical_force_absolute_composition (p : Parameters) (N M : ℕ+)
    (hNM : (N : ℕ) ≤ (M : ℕ)) (hN : 2 ≤ (N : ℕ)) :
    ∃ WN : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ∃ WM : EuclideanSpace ℝ (Fin (M : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ WN (gapAmbientDomain N) ∧
      ContDiffOn ℝ ∞ WM (gapAmbientDomain M) ∧
      (∀ x : {x : EuclideanSpace ℝ (Fin (N : ℕ)) // x ∈ gapAmbientDomain N},
        WN x.val = physicalAmbientGapEnergy p N x) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (M : ℕ)) // y ∈ gapAmbientDomain M},
        WM y.val = physicalAmbientGapEnergy p M y) ∧
      ∀ (n i : ℕ) (hi : 0 < i) (hin : i < n) (hn : n + 1 < (N : ℕ))
        (x : Fin (N : ℕ) → ℝ) (hx : x ∈ Riesz1.gapSimplex N)
        (y : Fin (M : ℕ) → ℝ) (hy : y ∈ Riesz1.gapSimplex M),
      (∀ k : Fin n, x ⟨k.val, by have := k.isLt; omega⟩ =
        y ⟨k.val, by have := k.isLt; omega⟩) →
      (∑ k : Fin n, x ⟨k.val, by have := k.isLt; omega⟩) ≤ (N : ℝ) / 2 →
      ∀ γ A : ℝ, 0 ≤ γ → γ < 1 → 1 ≤ A →
      (∀ r : ℕ, 0 < r → r ≤ (N : ℕ) - n →
        |cyclicGapSum N ⟨n, by omega⟩ r x - r| ≤ 4 * A * (r : ℝ) ^ γ) →
      (∀ r : ℕ, (hr : 0 < r) → (hrn : r ≤ (N : ℕ) - n) →
        |cyclicGapSum N ⟨(N : ℕ) - r, by omega⟩ r x - r| ≤ 4 * A * (r : ℝ) ^ γ) →
      (∀ r : ℕ, 0 < r → r ≤ (M : ℕ) - n →
        |cyclicGapSum M ⟨n, by omega⟩ r y - r| ≤ 4 * A * (r : ℝ) ^ γ) →
      (∀ r : ℕ, (hr : 0 < r) → (hrn : r ≤ (M : ℕ) - n) →
        |cyclicGapSum M ⟨(M : ℕ) - r, by omega⟩ r y - r| ≤ 4 * A * (r : ℝ) ^ γ) →
      let a := cyclicGapSum N ⟨i, by omega⟩ (n - i) x
      let b := cyclicGapSum N 0 i x
      let B := fun t : ℝ =>
        4 * p.val.2 * (16 * A) ^ (1 / (1 - γ)) * t ^ (-p.val.2 - 1)
      |fderiv ℝ WN (WithLp.toLp 2 x)
          (WithLp.toLp 2 (Pi.single ⟨i - 1, by omega⟩ 1 - Pi.single ⟨i, by omega⟩ 1)) -
        fderiv ℝ WM (WithLp.toLp 2 y)
          (WithLp.toLp 2 (Pi.single ⟨i - 1, by omega⟩ 1 - Pi.single ⟨i, by omega⟩ 1))| ≤
        2 * ((n : ℝ) * (2 * p.val.2 * ((N : ℝ) / 2) ^ (-p.val.2 - 1) *
            ∑' k : ℤ, |(k : ℝ)| ^ (-p.val.2 - 1)) +
          B a + B b + 4 * (p.val.2 * 2 ^ (p.val.2 + 1) * ∑' k : ℕ, (k : ℝ) ^ (-p.val.2 - 1)) +
          (p.val.2 * 2 ^ (p.val.2 + 1) *
            (1 + ∑' k : ℤ, |(k : ℝ)| ^ (-p.val.2 - 1))) *
              ((N : ℝ) ^ (-p.val.2) + (M : ℝ) ^ (-p.val.2))) := by
  obtain ⟨WN, hWN, hvN, hdN⟩ := physical_pinned_force_decomposition p N hN
  obtain ⟨WM, hWM, hvM, hdM⟩ := physical_pinned_force_decomposition p M (hN.trans hNM)
  refine ⟨WN, WM, hWN, hWM, hvN, hvM, ?_⟩
  intro n i hi hin hn x hx y hy hxy hmass γ A _hγ hγ1 hA hXR hXL hYR hYL
  have hcommon := internal_signed_common_force_error p N M hNM hi hin (by omega)
    x hx y hy hxy hmass
  have heN := physical_exterior_absolute_bound p N x hx n i hi hin (by omega) γ A hγ1 hA hXR hXL
  have heM := physical_exterior_absolute_bound p M y hy n i hi hin (by omega) γ A hγ1 hA hYR hYL
  have hr := cyclicGapSum_common_active N M (r := n - i) (by omega : n ≤ (N : ℕ)) (by omega)
    hin (by omega) x y hxy
  have hl := cyclicGapSum_common_active N M (i := 0) (r := i) (by omega : n ≤ (N : ℕ)) (by omega)
    (by omega : 0 < n) (by simpa using hin.le : 0 + i ≤ n) x y hxy
  change cyclicGapSum N 0 i x = cyclicGapSum M 0 i y at hl
  rw [← hr, ← hl] at heM
  dsimp only
  rw [hdN x hx n i hi hin (by omega), hdM y hy n i hi hin (by omega)]
  have triangle (r l e r' l' e' P Q R : ℝ)
      (hc : |(r - l) - (r' - l')| ≤ P) (he : |e| ≤ Q) (he' : |e'| ≤ R) :
      |-2 * (r + e - l) - -2 * (r' + e' - l')| ≤ 2 * (P + Q + R) := by
    have hh : |e - e'| ≤ Q + R := (abs_sub e e').trans (add_le_add he he')
    calc
      _ = 2 * |((r - l) - (r' - l')) + (e - e')| := by
        rw [show -2 * (r + e - l) - -2 * (r' + e' - l') =
          -2 * (((r - l) - (r' - l')) + (e - e')) by ring,
          abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 2 * (|(r - l) - (r' - l')| + |e - e'|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
      _ ≤ _ := by linarith
  have hh := triangle _ _ _ _ _ _ _ _ _ hcommon heN heM
  apply hh.trans_eq
  ring

/-- Internal all-size constant bookkeeping for
Appendix C. Both boundaries are bounded below by
the same positive cutoff, and all period errors are uniform in volume. -/
theorem internal_all_size_force_bound (s γ A d : ℝ) (hs : 0 < s)
    (hA : 0 ≤ A) (hd : 0 < d) (n : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ N M a b F : ℝ, 2 ≤ N → N ≤ M → d ≤ a → d ≤ b →
      (|F| ≤ 2 * ((n : ℝ) * (2 * s * (N / 2) ^ (-s - 1) *
          ∑' k : ℤ, |(k : ℝ)| ^ (-s - 1)) +
        4 * s * (16 * A) ^ (1 / (1 - γ)) * a ^ (-s - 1) +
        4 * s * (16 * A) ^ (1 / (1 - γ)) * b ^ (-s - 1) +
        4 * (s * 2 ^ (s + 1) * ∑' k : ℕ, (k : ℝ) ^ (-s - 1)) +
        (s * 2 ^ (s + 1) * (1 + ∑' k : ℤ, |(k : ℝ)| ^ (-s - 1))) *
          (N ^ (-s) + M ^ (-s)))) → |F| ≤ B := by
  let S := ∑' k : ℤ, |(k : ℝ)| ^ (-s - 1)
  let U := ∑' k : ℕ, (k : ℝ) ^ (-s - 1)
  let T := (16 * A) ^ (1 / (1 - γ))
  let J := s * 2 ^ (s + 1) * (1 + S)
  have hS : 0 ≤ S := tsum_nonneg fun k => Real.rpow_nonneg (abs_nonneg _) _
  have hU : 0 ≤ U := tsum_nonneg fun k => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hT : 0 ≤ T := Real.rpow_nonneg (by positivity) _
  refine ⟨2 * ((n : ℝ) * (2 * s * S) + 8 * s * T * d ^ (-s - 1) +
    4 * (s * 2 ^ (s + 1) * U) + 2 * J) + 1, by dsimp [J]; positivity, ?_⟩
  intro N M a b F hN hNM ha hb hF
  have hNa : (N / 2) ^ (-s - 1) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hNp : N ^ (-s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hMp : M ^ (-s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hap := Real.rpow_le_rpow_of_nonpos hd ha (by linarith : -s - 1 ≤ 0)
  have hbp := Real.rpow_le_rpow_of_nonpos hd hb (by linarith : -s - 1 ≤ 0)
  have hc := mul_le_mul_of_nonneg_left hNa (show 0 ≤ (n : ℝ) * (2 * s * S) by positivity)
  have hba := mul_le_mul_of_nonneg_left hap (show 0 ≤ 4 * s * T by positivity)
  have hbb := mul_le_mul_of_nonneg_left hbp (show 0 ≤ 4 * s * T by positivity)
  have him := mul_le_mul_of_nonneg_left (add_le_add hNp hMp) (show 0 ≤ J by dsimp [J]; positivity)
  dsimp only [S, U, T, J] at *
  nlinarith

/-- See Appendix C in the paper: uniform physical oscillation
for each bounded active size. The positive bound is chosen before either
volume, temperature, or exterior. No lower rank-count condition is used. -/
theorem bounded_size_oscillation (s : ℝ) (hs : 0 < s) (_hs1 : s ≠ 1) :
    ∀ ε : ℝ, 0 < ε →
      ε < min (1 - min s 1 / 2) (s - min s 1 / 2) / 4 →
      ∀ a : ℕ, 1 ≤ a → ∃ B : ℝ, 0 < B ∧ ∀ e d : ℕ,
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
      ∀ u v : EuclideanSpace ℝ (Fin (a + 1)),
      WithLp.ofLp u ∈ goodBlockEvent s a.succPNat (e + a).succPNat ε →
      WithLp.ofLp v ∈ goodBlockEvent s a.succPNat (e + a).succPNat ε →
      (∑ k, u k) = L → (∑ k, v k) = L → |D v - D u| ≤ B := by
  intro ε hε hεs a ha
  have hγ1 : min s 1 / 2 + ε < 1 := by
    have hh := hεs.trans_le (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
    linarith [min_le_right s 1]
  have hA : 1 ≤ (a + 1 : ℝ) ^ ε := Real.one_le_rpow (by linarith) hε.le
  obtain ⟨B₀, hBpos, hB₀⟩ := internal_all_size_force_bound s (min s 1 / 2 + ε)
    ((a + 1 : ℝ) ^ ε) ((a + 1 : ℝ) ^ (-ε)) hs (by positivity) (by positivity) (a + 1)
  refine ⟨2 * (a + 1 : ℝ) ^ ε * (B₀ * (a + 1 : ℝ) ^ (1 + min s 1 / 2)) + 1,
    by positivity, ?_⟩
  intro e d hN hed _hsize p hps
  have he : 0 < e := by omega
  have hd : 0 < d := by omega
  have hex := physical_force_absolute_composition p (e + a).succPNat (d + a).succPNat
    (by change e + a + 1 ≤ d + a + 1; omega) (by change 2 ≤ e + a + 1; omega)
  change ∃ WN : EuclideanSpace ℝ (Fin (e + a + 1)) → ℝ,
    ∃ WM : EuclideanSpace ℝ (Fin (d + a + 1)) → ℝ, _ at hex
  obtain ⟨WN, WM, hWN, hWM, hvN, hvM, hforce⟩ := hex
  refine ⟨WN, WM, hWN, hWM, hvN, hvM, ?_⟩
  intro L y z hy hz hmassY hmassZ hL hYR hYL hZR hZL D u v hu hv hmass hvmass
  have hforceD : ∀ w : EuclideanSpace ℝ (Fin (a + 1)),
      WithLp.ofLp w ∈ goodBlockEvent s a.succPNat (e + a).succPNat ε →
      (∑ k, w k) = L → DifferentiableAt ℝ D w ∧
      ∀ i : Fin a, |fderiv ℝ D w
        (WithLp.toLp 2 (Pi.single i.castSucc 1 - Pi.single i.succ 1))| ≤ B₀ := by
    intro u hgood hmass
    have hu : ∀ k, 0 < u k := fun k =>
      (Real.rpow_pos_of_pos (by exact_mod_cast a.succPNat.pos) (-ε)).trans_le (hgood.2.1 k).1
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
    intro i
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
        (a + 1 - (i.val + 1)) (by have := i.isLt; omega) (by omega),
  ] at hh
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
    have hcutR := goodBlockEvent_interval_lower s ε a.succPNat (e + a).succPNat
      (WithLp.ofLp u) hgood (i.val + 1) (a - i.val)
      (by change i.val + 1 + (a - i.val) ≤ a + 1; have := i.isLt; omega)
    have hcutL := goodBlockEvent_interval_lower s ε a.succPNat (e + a).succPNat
      (WithLp.ofLp u) hgood 0 (i.val + 1)
      (by change 0 + (i.val + 1) ≤ a + 1; have := i.isLt; omega)
    have hlowR : (a + 1 : ℝ) ^ (-ε) ≤
        ∑ k : Fin (a - i.val), u ⟨i.val + 1 + k.val, by have := i.isLt; have := k.isLt; omega⟩ := by
      have hr : (1 : ℝ) ≤ (a - i.val : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt i.isLt
      have hnn : 0 ≤ (a + 1 : ℝ) ^ (-ε) := by positivity
      have hh := mul_le_mul_of_nonneg_right hr hnn
      simp only [one_mul] at hh
      apply hh.trans
      simpa only [Nat.succPNat_coe, Nat.cast_succ] using hcutR
    have hlowL : (a + 1 : ℝ) ^ (-ε) ≤
        ∑ k : Fin (i.val + 1), u ⟨k.val, by have := k.isLt; omega⟩ := by
      have hr : (1 : ℝ) ≤ (i.val + 1 : ℕ) := by exact_mod_cast Nat.succ_pos i.val
      have hh := mul_le_mul_of_nonneg_right hr (show 0 ≤ (a + 1 : ℝ) ^ (-ε) by positivity)
      simp only [one_mul] at hh
      apply hh.trans
      simpa only [Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one, Nat.zero_add] using hcutL
    apply hB₀ (e + a + 1) (d + a + 1) _ _ _
      (by exact_mod_cast (show 2 ≤ e + a + 1 by omega))
      (by exact_mod_cast (show e + a + 1 ≤ d + a + 1 by omega)) hlowR hlowL
    simpa only [hps, Nat.add_sub_add_right, Nat.add_sub_cancel, Nat.zero_add, Nat.succPNat_coe,
      Nat.cast_succ, Nat.cast_add, Nat.cast_one, X, Y, WithLp.toLp_ofLp] using hh
  have hseg := internal_rigidity_segment_bound (e + a).succPNat s ε D u v hu hv
    (hmass.trans hvmass.symm) (fun _ => B₀)
    (fun w hw hm => (hforceD w hw (hm.trans hmass)).1)
    (fun w hw hm => (hforceD w hw (hm.trans hmass)).2)
  apply hseg.trans
  have hsum : (∑ i : Fin a, B₀ * ((min (i.val + 1) (a - i.val) : ℕ) : ℝ) ^ (min s 1 / 2)) ≤
      B₀ * (a + 1 : ℝ) ^ (1 + min s 1 / 2) := by
    calc
      _ ≤ ∑ _i : Fin a, B₀ * (a + 1 : ℝ) ^ (min s 1 / 2) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ hBpos.le
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        exact_mod_cast (show min (i.val + 1) (a - i.val) ≤ a + 1 by omega)
      _ = (a : ℝ) * (B₀ * (a + 1 : ℝ) ^ (min s 1 / 2)) := by simp
      _ ≤ (a + 1 : ℝ) * (B₀ * (a + 1 : ℝ) ^ (min s 1 / 2)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by rw [Real.rpow_add (by positivity : 0 < (a + 1 : ℝ)), Real.rpow_one]; ring
  have hh := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2 * (a + 1 : ℝ) ^ ε by positivity)
  simpa only [Nat.succPNat_coe, Nat.cast_succ] using hh.trans (le_add_of_nonneg_right (show (0 : ℝ) ≤ 1 by norm_num))

/-- Every edge between a component and its middle pin is at least the
component's boundary distance from both ends, as used in the proof of Proposition 6.6. No factor depending on dimension is lost. -/
theorem middle_path_boundary_distance (a : ℕ) (j : Fin (a + 1)) (i : Fin a)
    (hi : min j.val (InteractionDifferential.middle a).val ≤ i.val ∧
      i.val < max j.val (InteractionDifferential.middle a).val) :
    min (j.val + 1) (a + 1 - j.val) ≤ i.val + 1 ∧
      min (j.val + 1) (a + 1 - j.val) ≤ a - i.val := by
  dsimp only [InteractionDifferential.middle] at hi
  have hj := j.isLt
  have hii := i.isLt
  omega

/-- Internal finite-tail specialization for the middle-directed sum of
the proof of Proposition 6.6. -/
theorem internal_middle_rank_tail (a : ℕ) (j : Fin (a + 1)) (t : ℝ) (ht : 1 < t) :
    let S := Finset.univ.filter (fun i : Fin a =>
      min j.val (InteractionDifferential.middle a).val ≤ i.val ∧
        i.val < max j.val (InteractionDifferential.middle a).val)
    let δ : ℝ := (min (j.val + 1) (a + 1 - j.val) : ℕ)
    (∑ i ∈ S, ((i.val + 1 : ℝ) ^ (-t) + ((a - i.val : ℕ) : ℝ) ^ (-t))) ≤
      2 * (1 + 1 / (t - 1)) * δ ^ (1 - t) := by
  intro S δ
  have hδ : 1 ≤ δ := by
    dsimp [δ]
    exact_mod_cast (show 1 ≤ min (j.val + 1) (a + 1 - j.val) by have := j.isLt; omega)
  let g := fun k : ℕ => if δ ≤ 1 + (k : ℝ) then (1 + (k : ℝ)) ^ (-t) else 0
  have hg0 : ∀ k, 0 ≤ g k := by intro k; dsimp [g]; split_ifs <;> positivity
  have hgs : Summable g := by
    apply Summable.of_nonneg_of_le hg0 _ (summable_one_add_rpow_neg ht)
    intro k
    dsimp [g]
    split_ifs
    · exact le_rfl
    · positivity
  have hbound (r : Fin a → ℕ) (hr : Set.InjOn r S)
      (hR : ∀ i ∈ S, δ ≤ 1 + (r i : ℝ)) :
      (∑ i ∈ S, (1 + (r i : ℝ)) ^ (-t)) ≤ (1 + 1 / (t - 1)) * δ ^ (1 - t) := by
    have he : (∑ i ∈ S, (1 + (r i : ℝ)) ^ (-t)) = ∑ k ∈ S.image r, g k := by
      rw [Finset.sum_image hr]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [g, ite_eq_left (hR i hi)]
    rw [he]
    exact (hgs.sum_le_tsum _ (fun k _ => hg0 k)).trans (tsum_tail_indicator_le ht hδ)
  have hright := hbound (fun i => i.val) Fin.val_injective.injOn (by
    intro i hi
    have hd := (middle_path_boundary_distance a j i (Finset.mem_filter.mp hi).2).1
    dsimp [δ]
    exact_mod_cast (show min (j.val + 1) (a + 1 - j.val) ≤ 1 + i.val by omega))
  have hleft := hbound (fun i => a - i.val - 1) (by
    intro i _ k _ hik
    apply Fin.ext
    have hi := i.isLt
    have hk := k.isLt
    dsimp only at hik
    omega) (by
    intro i hi
    have hd := (middle_path_boundary_distance a j i (Finset.mem_filter.mp hi).2).2
    have hh : 1 + (a - i.val - 1) = a - i.val := by have := i.isLt; omega
    dsimp [δ]
    exact_mod_cast (show min (j.val + 1) (a + 1 - j.val) ≤ 1 + (a - i.val - 1) by omega))
  have he : (∑ i ∈ S, (1 + ((a - i.val - 1 : ℕ) : ℝ)) ^ (-t)) =
      ∑ i ∈ S, ((a - i.val : ℕ) : ℝ) ^ (-t) := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact_mod_cast (show 1 + (a - i.val - 1) = a - i.val by have := i.isLt; omega)
  rw [he] at hleft
  simp only [Finset.sum_add_distrib]
  have her : (∑ i ∈ S, (i.val + 1 : ℝ) ^ (-t)) = ∑ i ∈ S, (1 + (i.val : ℝ)) ^ (-t) := by
    apply Finset.sum_congr rfl; intro i _; congr 1; ring
  rw [her]
  linarith

/-- Internal reconstruction estimate for the proof of Proposition 6.6.
Two summable boundary-force profiles retain their separate endpoint powers. Only the constant period error acquires the number of active coordinates. -/
theorem internal_pinned_two_profiles (a : ℕ) (f : Fin a → ℝ)
    (p q C₁ C₂ E : ℝ) (hp : 1 < p) (hq : 1 < q)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hE : 0 ≤ E)
    (hf : ∀ i : Fin a, |f i| ≤
      C₁ * ((i.val + 1 : ℝ) ^ (-p) + ((a - i.val : ℕ) : ℝ) ^ (-p)) +
      C₂ * ((i.val + 1 : ℝ) ^ (-q) + ((a - i.val : ℕ) : ℝ) ^ (-q)) + E)
    (j : Fin (a + 1)) :
    let δ : ℝ := (min (j.val + 1) (a + 1 - j.val) : ℕ)
    |InteractionDifferential.pinnedRepresentative f j| ≤
      2 * C₁ * (1 + 1 / (p - 1)) * δ ^ (1 - p) +
      2 * C₂ * (1 + 1 / (q - 1)) * δ ^ (1 - q) + (a : ℝ) * E := by
  intro δ
  let S := Finset.univ.filter (fun i : Fin a =>
    min j.val (InteractionDifferential.middle a).val ≤ i.val ∧
      i.val < max j.val (InteractionDifferential.middle a).val)
  apply (InteractionDifferential.pinnedRepresentative_abs_le f j).trans
  have hh := Finset.sum_le_sum (s := S) (fun i _ => hf i)
  have h₁ := internal_middle_rank_tail a j p hp
  have h₂ := internal_middle_rank_tail a j q hq
  have hcard : (S.card : ℝ) ≤ a := by exact_mod_cast (show S.card ≤ a by simpa only [Fintype.card_fin] using Finset.card_le_univ S)
  have hsum (r : ℝ) : (∑ i ∈ S, r) = (S.card : ℝ) * r := by simp
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsum] at hh
  have hP := mul_le_mul_of_nonneg_left h₁ hC₁
  have hQ := mul_le_mul_of_nonneg_left h₂ hC₂
  have hR := mul_le_mul_of_nonneg_right hcard hE
  simp only [Finset.sum_add_distrib] at hP hQ
  dsimp only [S, δ] at *
  nlinarith

/-- The middle-normalized primitive has its global squared norm bounded
by the squared force norm with the exact finite-dimensional factor.
This is the algebraic step in the proof of Proposition 6.6. -/
theorem pinnedRepresentative_sq_sum_le (a : ℕ) (f : Fin a → ℝ) :
    (∑ j : Fin (a + 1), (InteractionDifferential.pinnedRepresentative f j) ^ 2) ≤
      (a : ℝ) * (a + 1 : ℝ) * ∑ i : Fin a, (f i) ^ 2 := by
  have hpoint (j : Fin (a + 1)) :
      (InteractionDifferential.pinnedRepresentative f j) ^ 2 ≤ (a : ℝ) * ∑ i, (f i) ^ 2 := by
    let S := Finset.univ.filter (fun i : Fin a =>
      min j.val (InteractionDifferential.middle a).val ≤ i.val ∧
        i.val < max j.val (InteractionDifferential.middle a).val)
    have habs := InteractionDifferential.pinnedRepresentative_abs_le f j
    have hsum0 : 0 ≤ ∑ i ∈ S, |f i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    have hsq := (sq_le_sq₀ (abs_nonneg _) hsum0).mpr habs
    rw [sq_abs] at hsq
    have hcs := (sq_sum_le_card_mul_sum_sq (s := S) (f := fun i => |f i|) :
      (∑ i ∈ S, |f i|) ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, |f i| ^ 2)
    simp only [sq_abs] at hcs
    have hcard : (S.card : ℝ) ≤ a := by exact_mod_cast (show S.card ≤ a by simpa only [Fintype.card_fin] using Finset.card_le_univ S)
    have hsub := Finset.sum_le_univ_sum_of_nonneg (s := S) (fun i : Fin a => sq_nonneg (f i))
    exact hsq.trans (hcs.trans (mul_le_mul hcard hsub
      (Finset.sum_nonneg fun i _ => sq_nonneg (f i)) (Nat.cast_nonneg a)))
  calc
    _ ≤ ∑ _j : Fin (a + 1), (a : ℝ) * ∑ i, (f i) ^ 2 :=
      Finset.sum_le_sum fun j _ => hpoint j
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one]; ring

/-- The inverse-gap weight in the proof of Proposition 6.6
dominates the square of the singular force at each actual gap. -/
theorem force_power_sq_le_exceptionalWeight {s : ℝ} (hs : 0 < s) (a : ℕ)
    (x : Fin (a + 1) → ℝ) (hx : ∀ i, 0 < x i) (j : Fin (a + 1)) :
    (1 + x j ^ (-s - 1)) ^ 2 ≤ 4 * exceptionalWeight (n := a.succPNat) s x := by
  have hW := one_le_exceptionalWeight (n := a.succPNat) s x (fun i => (hx i).le)
  have hterm : x j ^ (-4 * s - 12) ≤ ∑ i : Fin (a + 1), x i ^ (-4 * s - 12) :=
    Finset.single_le_sum (fun i _ => Real.rpow_nonneg (hx i).le _) (Finset.mem_univ j)
  have hsq : (x j ^ (-s - 1)) ^ 2 ≤ exceptionalWeight (n := a.succPNat) s x := by
    change (x j ^ (-s - 1)) ^ 2 ≤ 1 + ∑ i : Fin (a + 1), x i ^ (-4 * s - 12)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hx j).le]
    norm_num only [Nat.cast_ofNat]
    have he : (-s - 1) * (2 : ℝ) = -2 * s - 2 := by ring
    rw [he]
    by_cases hx1 : x j ≤ 1
    · have hp := Real.rpow_le_rpow_of_exponent_ge (hx j) hx1
        (by linarith : -4 * s - 12 ≤ -2 * s - 2)
      change _ ≤ 1 + ∑ i : Fin (a + 1), x i ^ (-4 * s - 12)
      linarith
    · have hp := Real.rpow_le_one_of_one_le_of_nonpos (le_of_not_ge hx1) (by linarith : -2 * s - 2 ≤ 0)
      have hsum0 := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => Real.rpow_nonneg (hx i).le (-4 * s - 12))
      linarith
  nlinarith [sq_nonneg (x j ^ (-s - 1) - 1)]

/-- Internal fine-event bound in the proof of Proposition 6.6.
This retains the actual boundary weight and both cutoff exponents. The force estimate is a hypothesis. -/
theorem internal_differential_fine_bound (s ε η C T E : ℝ) (a : ℕ)
    (hs : 0 < s) (hε : 0 ≤ ε) (hγ : min s 1 / 2 + ε < s)
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hE : 0 ≤ E) (f : Fin a → ℝ)
    (hf : ∀ i : Fin a, |f i| ≤ C *
      (T * (a + 1 : ℝ) ^ (η * (s + 1)) *
        ((i.val + 1 : ℝ) ^ (-s - 1) + ((a - i.val : ℕ) : ℝ) ^ (-s - 1)) +
       (a + 1 : ℝ) ^ ε * (a + 1 : ℝ) ^ (η * (s + 1 - (min s 1 / 2 + ε))) *
        ((i.val + 1 : ℝ) ^ (min s 1 / 2 + ε - s - 1) +
          ((a - i.val : ℕ) : ℝ) ^ (min s 1 / 2 + ε - s - 1))) + E)
    (j : Fin (a + 1)) :
    |InteractionDifferential.pinnedRepresentative f j| ≤
      (2 * C * T * (a + 1 : ℝ) ^ (η * (s + 1)) * (1 + 1 / s) +
        2 * C * (a + 1 : ℝ) ^ (2 * ε + η * (s + 1 - (min s 1 / 2 + ε))) *
          (1 + 1 / (s - (min s 1 / 2 + ε)))) *
        InteractionDifferential.boundaryWeight s a.succPNat j + (a : ℝ) * E := by
  let n : ℝ := a + 1
  let σ := min s 1 / 2
  let γ := σ + ε
  let δ : ℝ := (min (j.val + 1) (a + 1 - j.val) : ℕ)
  have hδ : 1 ≤ δ := by
    dsimp [δ]
    exact_mod_cast (show 1 ≤ min (j.val + 1) (a + 1 - j.val) by have := j.isLt; omega)
  have hδp : 0 < δ := by linarith
  have hσ : 0 ≤ σ := by dsimp [σ]; positivity
  have hW : InteractionDifferential.boundaryWeight s a.succPNat j = δ ^ (σ - s) := rfl
  have h₁ : δ ^ (-s) ≤ InteractionDifferential.boundaryWeight s a.succPNat j := by
    rw [hW]
    exact Real.rpow_le_rpow_of_exponent_le hδ (by linarith)
  have h₂ : δ ^ (γ - s) ≤ n ^ ε * InteractionDifferential.boundaryWeight s a.succPNat j := by
    simpa only [n, γ, σ, Nat.succPNat_coe, Nat.cast_succ] using
      InteractionDifferential.boundary_power_loss s a.succPNat j hε
  have hforce (i : Fin a) : |f i| ≤
      (C * T * n ^ (η * (s + 1))) *
        ((i.val + 1 : ℝ) ^ (-(s + 1)) + ((a - i.val : ℕ) : ℝ) ^ (-(s + 1))) +
      (C * n ^ ε * n ^ (η * (s + 1 - γ))) *
        ((i.val + 1 : ℝ) ^ (-(s + 1 - γ)) + ((a - i.val : ℕ) : ℝ) ^ (-(s + 1 - γ))) + E := by
    have hh := hf i
    rw [show -(s + 1) = -s - 1 by ring,
      show -(s + 1 - γ) = γ - s - 1 by ring]
    apply hh.trans_eq
    dsimp only [n, γ, σ]
    ring
  have hh := internal_pinned_two_profiles a f (s + 1) (s + 1 - γ)
    (C * T * n ^ (η * (s + 1))) (C * n ^ ε * n ^ (η * (s + 1 - γ))) E
    (by linarith) (by dsimp [γ, σ]; linarith) (by positivity) (by positivity) hE hforce j
  dsimp only at hh
  rw [show 1 - (s + 1) = -s by ring,
    show 1 - (s + 1 - γ) = γ - s by ring,
    show s + 1 - 1 = s by ring, show s + 1 - γ - 1 = s - γ by ring] at hh
  have hp₁ := mul_le_mul_of_nonneg_left h₁
    (show 0 ≤ 2 * (C * T * n ^ (η * (s + 1))) * (1 + 1 / s) by positivity)
  have hp₂ := mul_le_mul_of_nonneg_left h₂
    (show 0 ≤ 2 * (C * n ^ ε * n ^ (η * (s + 1 - γ))) * (1 + 1 / (s - γ)) by
      have hhγ : 0 < s - γ := by dsimp [γ, σ]; linarith
      positivity)
  apply hh.trans
  have he : n ^ ε * n ^ (η * (s + 1 - γ)) * n ^ ε =
      n ^ (2 * ε + η * (s + 1 - γ)) := by
    rw [← Real.rpow_add (by dsimp [n]; positivity : 0 < n),
      ← Real.rpow_add (by dsimp [n]; positivity : 0 < n)]
    congr 1; ring
  dsimp only [δ] at hp₁ hp₂
  have hsum := add_le_add (add_le_add hp₁ hp₂) (le_refl ((a : ℝ) * E))
  apply hsum.trans_eq
  dsimp only [n, γ, σ] at he ⊢
  linear_combination 2 * C * (1 + 1 / (s - (min s 1 / 2 + ε))) *
    InteractionDifferential.boundaryWeight s a.succPNat j * he

/-- See Lemma 6.4 of the paper: reconstructing from the actual pinned derivatives
represents the differential of the given smooth energy difference on every
tangent vector. No surrogate force is used in this identity. -/
theorem pinned_derivative_representative_pairing (a : ℕ)
    (D : EuclideanSpace ℝ (Fin (a + 1)) → ℝ)
    (u : EuclideanSpace ℝ (Fin (a + 1)))
    (_hD : DifferentiableAt ℝ D u) (v : Fin (a + 1) → ℝ) (hv : ∑ j, v j = 0) :
    (∑ j : Fin (a + 1), InteractionDifferential.pinnedRepresentative
      (fun i : Fin a => fderiv ℝ D u
        (WithLp.toLp 2 (Pi.single i.castSucc 1 - Pi.single i.succ 1))) j * v j) =
      fderiv ℝ D u (WithLp.toLp 2 v) := by
  rw [InteractionDifferential.pinnedRepresentative_pairing _ v hv]
  exact (linear_pinned_pairing (fderiv ℝ D u) v hv).symm

/-- Internal global-weight assembly for the proof of Proposition 6.6.
Once the actual forces are controlled by the smallest active gap, the
entire middle-normalized vector is controlled by the gap
weight, with an explicit polynomial dimension factor. -/
theorem internal_global_weight_composition (s : ℝ) (hs : 0 < s) (a : ℕ)
    (x : Fin (a + 1) → ℝ) (hx : ∀ i, 0 < x i) (j : Fin (a + 1))
    (K : ℝ) (hK : 0 ≤ K) (f : Fin a → ℝ)
    (hf : ∀ i : Fin a, |f i| ≤ K * (1 + x j ^ (-s - 1))) :
    (∑ k : Fin (a + 1), InteractionDifferential.pinnedRepresentative f k ^ 2) ≤
      4 * (a : ℝ) ^ 2 * (a + 1 : ℝ) * K ^ 2 * exceptionalWeight (n := a.succPNat) s x := by
  have hW := force_power_sq_le_exceptionalWeight hs a x hx j
  have hpoint (i : Fin a) : (f i) ^ 2 ≤
      4 * K ^ 2 * exceptionalWeight (n := a.succPNat) s x := by
    have hh := (sq_le_sq₀ (abs_nonneg (f i))
      (mul_nonneg hK (add_nonneg zero_le_one (Real.rpow_nonneg (hx j).le (-s - 1))))).mpr (hf i)
    rw [sq_abs, mul_pow] at hh
    have hw := mul_le_mul_of_nonneg_left hW (sq_nonneg K)
    nlinarith
  have hsum : (∑ i : Fin a, (f i) ^ 2) ≤
      (a : ℝ) * (4 * K ^ 2 * exceptionalWeight (n := a.succPNat) s x) := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
      Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  apply (pinnedRepresentative_sq_sum_le a f).trans
  have hh := mul_le_mul_of_nonneg_left hsum (show 0 ≤ (a : ℝ) * (a + 1 : ℝ) by positivity)
  apply hh.trans_eq
  ring

end Riesz2.InterpolantLocalLaws
