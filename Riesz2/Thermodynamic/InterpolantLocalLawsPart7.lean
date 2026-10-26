/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.InterpolantLocalLawsPart6
public import Riesz2.Thermodynamic.InterpolantLocalLaws
public import Riesz2.Thermodynamic.InteractionDifferential

/-!
# Physical two-volume force comparison

Composition of the common-particle cancellation and the two exterior rank families for
Appendix C.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ContDiff

namespace Riesz2.InterpolantLocalLaws

/-- See Appendix C in the paper: the two signed common-particle
families cost exactly `n` period errors, including both boundary particles. -/
theorem internal_signed_common_force_error (p : Parameters) (N M : ℕ+)
    (hNM : (N : ℕ) ≤ (M : ℕ)) {n i : ℕ}
    (hi : 0 < i) (hin : i < n) (hn : n < (N : ℕ))
    (x : Fin (N : ℕ) → ℝ) (hx : x ∈ Riesz1.gapSimplex N)
    (y : Fin (M : ℕ) → ℝ) (hy : y ∈ Riesz1.gapSimplex M)
    (hxy : ∀ k : Fin n,
      x ⟨k.val, by have := k.isLt; omega⟩ =
        y ⟨k.val, by have := k.isLt; omega⟩)
    (hmass : (∑ k : Fin n, x ⟨k.val, by have := k.isLt; omega⟩) ≤ (N : ℝ) / 2) :
    |((∑ r : Fin (n - i), intervalForce p N
        ⟨cyclicGapSum N ⟨i, by omega⟩ (r.val + 1) x,
          PhysicalEnergy.gapSum_mem N _ (by omega) (by have := r.isLt; omega) x hx⟩) -
      ∑ k : Fin i, intervalForce p N
        ⟨cyclicGapSum N ⟨k.val, by have := k.isLt; omega⟩ (i - k.val) x,
          PhysicalEnergy.gapSum_mem N _ (by have := k.isLt; omega) (by omega) x hx⟩) -
      ((∑ r : Fin (n - i), intervalForce p M
        ⟨cyclicGapSum M ⟨i, by omega⟩ (r.val + 1) y,
          PhysicalEnergy.gapSum_mem M _ (by omega) (by have := r.isLt; omega) y hy⟩) -
      ∑ k : Fin i, intervalForce p M
        ⟨cyclicGapSum M ⟨k.val, by have := k.isLt; omega⟩ (i - k.val) y,
          PhysicalEnergy.gapSum_mem M _ (by have := k.isLt; omega) (by omega) y hy⟩)| ≤
      (n : ℝ) * (2 * p.val.2 * ((N : ℝ) / 2) ^ (-p.val.2 - 1) *
        ∑' k : ℤ, |(k : ℝ)| ^ (-p.val.2 - 1)) := by
  let a : Fin (n - i) ⊕ Fin i → ℕ := Sum.elim (fun _ => i) Fin.val
  let r : Fin (n - i) ⊕ Fin i → ℕ := Sum.elim (fun k => k.val + 1) (fun k => i - k.val)
  let w : Fin (n - i) ⊕ Fin i → ℝ := Sum.elim (fun _ => 1) (fun _ => -1)
  have h := internal_common_force_sum_error p N M hNM hn.le a r
    (by intro k; cases k with | inl k => exact hin | inr k => have := k.isLt; simp [a]; omega)
    (by intro k; cases k with | inl k => simp [r] | inr k => have := k.isLt; simpa only [r, Sum.elim_inr] using Nat.sub_pos_of_lt k.isLt)
    (by intro k; cases k <;> simp only [a, r, Sum.elim_inl, Sum.elim_inr]; all_goals omega)
    (by intro k; cases k with
        | inl k => have := k.isLt; simp only [r, Sum.elim_inl]; omega
        | inr k => simp only [r, Sum.elim_inr]; omega)
    x hx y hy hxy hmass w (by intro k; cases k <;> simp [w])
  simp only [Fintype.sum_sum_type, a, r, w, Sum.elim_inl, Sum.elim_inr,
    one_mul, neg_one_mul, Finset.sum_sub_distrib,
    Fintype.card_sum, Fintype.card_fin, Nat.sub_add_cancel hin.le, neg_sub] at h
  convert h using 1
  congr 1
  ring

/-- A nonwrapping suffix seen from the left boundary is indexed by
`Fin.revPerm`. See Appendix C in the paper: all strict exterior
particles occur exactly once, with ranks starting at one. -/
theorem exterior_suffix_rank_reversal (N : ℕ+) (n : ℕ) (hn : n < (N : ℕ))
    (x : Fin (N : ℕ) → ℝ) (f : ℝ → ℝ) :
    (∑ r : Fin ((N : ℕ) - n - 1),
      f (cyclicGapSum N ⟨n + r.val + 1, by have := r.isLt; omega⟩
        ((N : ℕ) - n - (r.val + 1)) x)) =
    ∑ r : Fin ((N : ℕ) - n - 1),
      f (cyclicGapSum N ⟨(N : ℕ) - (r.val + 1), by have := r.isLt; omega⟩
        (r.val + 1) x) := by
  have h := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin ((N : ℕ) - n - 1)))
    (fun r : Fin ((N : ℕ) - n - 1) =>
      f (cyclicGapSum N ⟨n + r.val + 1, by have := r.isLt; omega⟩
        ((N : ℕ) - n - (r.val + 1)) x))
  rw [← h]
  apply Finset.sum_congr rfl
  intro r _
  congr 2
  · apply Fin.ext
    simp only [Fin.revPerm_apply, Fin.val_rev]
    have := r.isLt
    omega
  · simp only [Fin.revPerm_apply, Fin.val_rev]
    have := r.isLt
    omega

/-- The complementary exterior separation uses the left active prefix
and the suffix following that exterior particle (Subsection 6.1). -/
theorem cyclicGapSum_exterior_complement (N : ℕ+)
    (x : Fin (N : ℕ) → ℝ) (hmass : ∑ k, x k = (N : ℝ))
    (n i r : ℕ) (hi : i < n) (hr : n + r + 1 < (N : ℕ)) :
    (N : ℝ) - cyclicGapSum N ⟨i, by omega⟩ (n - i + r + 1) x =
      cyclicGapSum N 0 i x + cyclicGapSum N ⟨n + r + 1, hr⟩
        ((N : ℕ) - n - (r + 1)) x := by
  have hidx : (⟨i + (n - i + r + 1), by omega⟩ : Fin (N : ℕ)) =
      ⟨n + r + 1, hr⟩ := by
    apply Fin.ext
    dsimp only
    omega
  have hlen : (N : ℕ) - i - (n - i + r + 1) = (N : ℕ) - n - (r + 1) := by omega
  have h := cyclicGapSum_linear_complement N x hmass i (n - i + r + 1) (by omega)
  rw [hidx, hlen] at h
  exact h

/-- See Appendix C in the paper: removing both nearest
images of each actual exterior particle produces the ordinary right
prefix and left suffix families, with the source signs. -/
theorem physical_exterior_two_boundary_error (p : Parameters) (N : ℕ+)
    (x : Fin (N : ℕ) → ℝ) (hx : x ∈ Riesz1.gapSimplex N)
    (n i : ℕ) (hi : i < n) (hn : n < (N : ℕ)) :
    let a := cyclicGapSum N ⟨i, by omega⟩ (n - i) x
    let b := cyclicGapSum N 0 i x
    |(∑ r : Fin ((N : ℕ) - n - 1), intervalForce p N
        ⟨cyclicGapSum N ⟨i, by omega⟩ (n - i + r.val + 1) x,
          PhysicalEnergy.gapSum_mem N _ (by omega) (by have := r.isLt; omega) x hx⟩) -
      ((∑ r : Fin ((N : ℕ) - n - 1),
        -p.val.2 * (a + cyclicGapSum N ⟨n, by omega⟩ (r.val + 1) x) ^ (-p.val.2 - 1)) -
      ∑ r : Fin ((N : ℕ) - n - 1),
        -p.val.2 * (b + cyclicGapSum N
          ⟨(N : ℕ) - (r.val + 1), by have := r.isLt; omega⟩
          (r.val + 1) x) ^ (-p.val.2 - 1))| ≤
      (p.val.2 * 2 ^ (p.val.2 + 1) *
        (1 + ∑' k : ℤ, |(k : ℝ)| ^ (-p.val.2 - 1))) * (N : ℝ) ^ (-p.val.2) := by
  dsimp only
  have hright (r : Fin ((N : ℕ) - n - 1)) :
      cyclicGapSum N ⟨i, by omega⟩ (n - i + r.val + 1) x =
      cyclicGapSum N ⟨i, by omega⟩ (n - i) x +
        cyclicGapSum N ⟨n, by omega⟩ (r.val + 1) x := by
    rw [show n - i + r.val + 1 = (n - i) + (r.val + 1) by omega,
      cyclicGapSum_split_nonwrapping N i (n - i) (r.val + 1) (by omega)]
    congr 2
    apply Fin.ext
    dsimp only
    omega
  have h := internal_exterior_image_sum_error p N x hx n i hi hn
  dsimp only [Subtype.coe_mk] at h
  have hR : (∑ r : Fin ((N : ℕ) - n - 1),
      (cyclicGapSum N ⟨i, by omega⟩ (n - i + r.val + 1) x) ^ (-p.val.2 - 1)) =
      ∑ r : Fin ((N : ℕ) - n - 1),
        (cyclicGapSum N ⟨i, by omega⟩ (n - i) x +
          cyclicGapSum N ⟨n, hn⟩ (r.val + 1) x) ^ (-p.val.2 - 1) := by
    apply Finset.sum_congr rfl
    intro r _
    exact congrArg (fun t : ℝ => t ^ (-p.val.2 - 1)) (hright r)
  have hL : (∑ r : Fin ((N : ℕ) - n - 1),
      ((N : ℝ) - cyclicGapSum N ⟨i, by omega⟩ (n - i + r.val + 1) x) ^ (-p.val.2 - 1)) =
      ∑ r : Fin ((N : ℕ) - n - 1),
        (cyclicGapSum N 0 i x + cyclicGapSum N
          ⟨(N : ℕ) - (r.val + 1), by have := r.isLt; omega⟩ (r.val + 1) x) ^ (-p.val.2 - 1) := by
    rw [← exterior_suffix_rank_reversal N n hn x
      (fun t => (cyclicGapSum N 0 i x + t) ^ (-p.val.2 - 1))]
    apply Finset.sum_congr rfl
    intro r _
    exact congrArg (fun t : ℝ => t ^ (-p.val.2 - 1))
      (cyclicGapSum_exterior_complement N x hx.2 n i r.val hi (by have := r.isLt; omega))
  rw [hR, hL] at h
  simp only [Finset.mul_sum, neg_mul, Finset.sum_neg_distrib] at h ⊢
  convert h using 1
  congr 1
  ring

/-- Internal rank comparison with the two exterior cardinalities given
separately. See Appendix C in the paper. No identification of
the smaller and larger finite carriers is left implicit. -/
theorem internal_principal_exterior_lengths_le {s γ A a : ℝ} (hs : 0 < s)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hA : 1 ≤ A) (ha : 0 < a)
    (m k : ℕ) (hm : 0 < m) (hmk : m ≤ k)
    (hT : (16 * A) ^ (1 / (1 - γ)) ≤ (m : ℝ))
    (Y : Fin m → ℝ) (Z : Fin k → ℝ)
    (hY0 : ∀ r, 0 ≤ Y r) (hZ0 : ∀ r, 0 ≤ Z r)
    (hY : ∀ r, |Y r - (r.val + 1 : ℝ)| ≤ 4 * A * (r.val + 1 : ℝ) ^ γ)
    (hZ : ∀ r, |Z r - (r.val + 1 : ℝ)| ≤ 4 * A * (r.val + 1 : ℝ) ^ γ) :
    |(∑ r, -s * (a + Y r) ^ (-s - 1)) -
      (∑ r, -s * (a + Z r) ^ (-s - 1))| ≤
      4 * s * (16 * A) ^ (1 / (1 - γ)) * a ^ (-s - 1) +
        8 * (s + 1) * 2 ^ (s + 2) * A * a ^ (γ - s - 1) +
        2 ^ (s + 1) * (m : ℝ) ^ (-s) := by
  have he : m + (k - m) = k := Nat.add_sub_of_le hmk
  let e := finCongr he
  have h := internal_principal_exterior_different_lengths hs hγ hγ1 hA ha
    m (k - m) hm hT Y (Z ∘ e) hY0 (fun r => hZ0 (e r)) hY
    (fun r => by simpa only [Function.comp_apply, e, finCongr_apply, Fin.val_cast] using hZ (e r))
  dsimp only [Function.comp_apply] at h
  rwa [Equiv.sum_comp e (fun r => -s * (a + Z r) ^ (-s - 1))] at h

/-- See Appendix C in the paper: comparison of the actual
strict exterior force sums. The geometric hypotheses are the literal
prefix and suffix conditions of Subsection 6.1, on the two mass simplexes.
The displayed threshold is internal to the eventual-size argument. -/
theorem internal_physical_exterior_comparison (p : Parameters) (N M : ℕ+)
    (hNM : (N : ℕ) ≤ (M : ℕ)) {n i : ℕ}
    (hi : 0 < i) (hin : i < n) (hn : n + 1 < (N : ℕ))
    (x : Fin (N : ℕ) → ℝ) (hx : x ∈ Riesz1.gapSimplex N)
    (y : Fin (M : ℕ) → ℝ) (hy : y ∈ Riesz1.gapSimplex M)
    (hxy : ∀ k : Fin n,
      x ⟨k.val, by have := k.isLt; omega⟩ =
        y ⟨k.val, by have := k.isLt; omega⟩)
    {γ A : ℝ} (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hA : 1 ≤ A)
    (hT : (16 * A) ^ (1 / (1 - γ)) ≤ (((N : ℕ) - n - 1 : ℕ) : ℝ))
    (hXR : ∀ r : ℕ, 0 < r → r ≤ (N : ℕ) - n →
      |cyclicGapSum N ⟨n, by omega⟩ r x - r| ≤ 4 * A * (r : ℝ) ^ γ)
    (hXL : ∀ r : ℕ, (hr : 0 < r) → (hrn : r ≤ (N : ℕ) - n) →
      |cyclicGapSum N ⟨(N : ℕ) - r, by omega⟩ r x - r| ≤ 4 * A * (r : ℝ) ^ γ)
    (hYR : ∀ r : ℕ, 0 < r → r ≤ (M : ℕ) - n →
      |cyclicGapSum M ⟨n, by omega⟩ r y - r| ≤ 4 * A * (r : ℝ) ^ γ)
    (hYL : ∀ r : ℕ, (hr : 0 < r) → (hrn : r ≤ (M : ℕ) - n) →
      |cyclicGapSum M ⟨(M : ℕ) - r, by omega⟩ r y - r| ≤ 4 * A * (r : ℝ) ^ γ) :
    let a := cyclicGapSum N ⟨i, by omega⟩ (n - i) x
    let b := cyclicGapSum N 0 i x
    let B := fun t : ℝ =>
      4 * p.val.2 * (16 * A) ^ (1 / (1 - γ)) * t ^ (-p.val.2 - 1) +
        8 * (p.val.2 + 1) * 2 ^ (p.val.2 + 2) * A * t ^ (γ - p.val.2 - 1)
    |(∑ r : Fin ((N : ℕ) - n - 1), intervalForce p N
        ⟨cyclicGapSum N ⟨i, by omega⟩ (n - i + r.val + 1) x,
          PhysicalEnergy.gapSum_mem N _ (by omega) (by have := r.isLt; omega) x hx⟩) -
      (∑ r : Fin ((M : ℕ) - n - 1), intervalForce p M
        ⟨cyclicGapSum M ⟨i, by omega⟩ (n - i + r.val + 1) y,
          PhysicalEnergy.gapSum_mem M _ (by omega) (by have := r.isLt; omega) y hy⟩)| ≤
      B a + B b + 2 * 2 ^ (p.val.2 + 1) * (((N : ℕ) - n - 1 : ℕ) : ℝ) ^ (-p.val.2) +
        (p.val.2 * 2 ^ (p.val.2 + 1) *
          (1 + ∑' k : ℤ, |(k : ℝ)| ^ (-p.val.2 - 1))) *
            ((N : ℝ) ^ (-p.val.2) + (M : ℝ) ^ (-p.val.2)) := by
  let a := cyclicGapSum N ⟨i, by omega⟩ (n - i) x
  let b := cyclicGapSum N 0 i x
  have ha : 0 < a := (PhysicalEnergy.gapSum_mem N _ (by omega : 0 < n - i)
    (by omega) x hx).1
  have hb : 0 < b := (PhysicalEnergy.gapSum_mem N 0 hi (by omega) x hx).1
  have har : cyclicGapSum M ⟨i, by omega⟩ (n - i) y = a := by
    exact (cyclicGapSum_common_active N M (by omega) (by omega) hin (by omega) x y hxy).symm
  have hbl : cyclicGapSum M 0 i y = b := by
    have h := cyclicGapSum_common_active N M (by omega : n ≤ (N : ℕ)) (by omega)
      (show 0 < n by omega) (show 0 + i ≤ n by omega) x y hxy
    have hzN : (⟨0, by omega⟩ : Fin (N : ℕ)) = 0 := by apply Fin.ext; simp
    have hzM : (⟨0, by omega⟩ : Fin (M : ℕ)) = 0 := by apply Fin.ext; simp
    simpa only [hzN, hzM, b] using h.symm
  let XR (r : Fin ((N : ℕ) - n - 1)) := cyclicGapSum N ⟨n, by omega⟩ (r.val + 1) x
  let XL (r : Fin ((N : ℕ) - n - 1)) :=
    cyclicGapSum N ⟨(N : ℕ) - (r.val + 1), by have := r.isLt; omega⟩ (r.val + 1) x
  let YR (r : Fin ((M : ℕ) - n - 1)) := cyclicGapSum M ⟨n, by omega⟩ (r.val + 1) y
  let YL (r : Fin ((M : ℕ) - n - 1)) :=
    cyclicGapSum M ⟨(M : ℕ) - (r.val + 1), by have := r.isLt; omega⟩ (r.val + 1) y
  have hr := internal_principal_exterior_lengths_le p.property.2.1 hγ hγ1 hA ha
    ((N : ℕ) - n - 1) ((M : ℕ) - n - 1) (by omega) (by omega) hT XR YR
    (fun r => (PhysicalEnergy.gapSum_mem N _ (by omega) (by have := r.isLt; omega) x hx).1.le)
    (fun r => (PhysicalEnergy.gapSum_mem M _ (by omega) (by have := r.isLt; omega) y hy).1.le)
    (fun r => by simpa only [XR, Nat.cast_add, Nat.cast_one] using hXR (r.val + 1) (by omega) (by have := r.isLt; omega))
    (fun r => by simpa only [YR, Nat.cast_add, Nat.cast_one] using hYR (r.val + 1) (by omega) (by have := r.isLt; omega))
  have hl := internal_principal_exterior_lengths_le p.property.2.1 hγ hγ1 hA hb
    ((N : ℕ) - n - 1) ((M : ℕ) - n - 1) (by omega) (by omega) hT XL YL
    (fun r => (PhysicalEnergy.gapSum_mem N _ (by omega) (by have := r.isLt; omega) x hx).1.le)
    (fun r => (PhysicalEnergy.gapSum_mem M _ (by omega) (by have := r.isLt; omega) y hy).1.le)
    (fun r => by simpa only [XL, Nat.cast_add, Nat.cast_one] using hXL (r.val + 1) (by omega) (by have := r.isLt; omega))
    (fun r => by simpa only [YL, Nat.cast_add, Nat.cast_one] using hYL (r.val + 1) (by omega) (by have := r.isLt; omega))
  have hNx := physical_exterior_two_boundary_error p N x hx n i hin (by omega)
  have hMy := physical_exterior_two_boundary_error p M y hy n i hin (by omega)
  dsimp only at hNx hMy ⊢
  rw [har, hbl] at hMy
  dsimp only [XR, YR] at hr
  dsimp only [XL, YL] at hl
  have comb (u v r r' l l' P Q R S : ℝ)
      (hu : |u - (r - l)| ≤ P) (hv : |v - (r' - l')| ≤ Q)
      (hr : |r - r'| ≤ R) (hl : |l - l'| ≤ S) :
      |u - v| ≤ P + Q + R + S := by
    calc
      _ = |((u - (r - l)) - (v - (r' - l'))) + ((r - r') - (l - l'))| := by congr 1; ring
      _ ≤ |(u - (r - l)) - (v - (r' - l'))| + |(r - r') - (l - l')| := abs_add_le _ _
      _ ≤ (|u - (r - l)| + |v - (r' - l')|) + (|r - r'| + |l - l'|) :=
        add_le_add (abs_sub _ _) (abs_sub _ _)
      _ ≤ _ := by linarith
  have hh := comb _ _ _ _ _ _ _ _ _ _ hNx hMy hr hl
  dsimp only [a, b] at hh
  linarith

/-- The small-rank cutoff in Appendix C
eventually lies inside every permitted strict exterior, uniformly in the
volume. The threshold depends on the two exponents alone. -/
theorem exterior_rank_threshold {σ ε : ℝ} (_hσ : σ < 1) (hε : 0 < ε)
    (hεσ : ε < (1 - σ) / 4) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ N : ℕ, 4 * n ≤ N →
      (16 * (n : ℝ) ^ ε) ^ (1 / (1 - (σ + ε))) ≤ ((N - n - 1 : ℕ) : ℝ) := by
  let q := 1 / (1 - (σ + ε))
  have hden : 0 < 1 - (σ + ε) := by linarith
  have hq : 0 < q := by dsimp [q]; positivity
  have hδ : 0 < 1 - ε * q := by
    have hh : ε * q < 1 := by
      dsimp [q]
      rw [mul_one_div, div_lt_one hden]
      linarith
    linarith
  have ht : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - ε * q))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp (ht.eventually (Filter.eventually_ge_atTop (16 ^ q)))
  refine ⟨max k 2, ?_⟩
  intro n hn N hN
  have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpow := mul_le_mul_of_nonneg_right (hk n ((le_max_left _ _).trans hn))
    (Real.rpow_nonneg hnp.le (ε * q))
  rw [← Real.rpow_add hnp, sub_add_cancel, Real.rpow_one] at hpow
  calc
    _ = 16 ^ q * (n : ℝ) ^ (ε * q) := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hnp.le ε), ← Real.rpow_mul hnp.le]
    _ ≤ (n : ℝ) := hpow
    _ ≤ ((N - n - 1 : ℕ) : ℝ) := by exact_mod_cast (show n ≤ N - n - 1 by omega)

/-- The unmatched-rank error has the physical period scale, including
the smallest allowed sizes (Appendix C). -/
theorem exterior_rank_tail_le {s : ℝ} (hs : 0 < s) (n N : ℕ)
    (hn : 1 ≤ n) (hN : 4 * n ≤ N) :
    (((N - n - 1 : ℕ) : ℝ)) ^ (-s) ≤ 2 ^ s * (N : ℝ) ^ (-s) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hhalf : (N : ℝ) / 2 ≤ ((N - n - 1 : ℕ) : ℝ) := by
    have h : N ≤ 2 * (N - n - 1) := by omega
    have hh : (N : ℝ) ≤ 2 * ((N - n - 1 : ℕ) : ℝ) := by exact_mod_cast h
    linarith
  apply (Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (N : ℝ) / 2)
    hhalf (by linarith : -s ≤ 0)).trans_eq
  rw [div_eq_mul_inv, Real.mul_rpow hNp.le (by norm_num),
    Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), neg_neg, mul_comm]

/-- Internal composition of the actual force families in Appendix C. The two smooth energies realize the physical energies. All estimates concern their actual pinned derivatives. -/
theorem internal_physical_force_composition (p : Parameters) (N M : ℕ+)
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
      (16 * A) ^ (1 / (1 - γ)) ≤ (((N : ℕ) - n - 1 : ℕ) : ℝ) →
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
        4 * p.val.2 * (16 * A) ^ (1 / (1 - γ)) * t ^ (-p.val.2 - 1) +
          8 * (p.val.2 + 1) * 2 ^ (p.val.2 + 2) * A * t ^ (γ - p.val.2 - 1)
      |fderiv ℝ WN (WithLp.toLp 2 x)
          (WithLp.toLp 2 (Pi.single ⟨i - 1, by omega⟩ 1 - Pi.single ⟨i, by omega⟩ 1)) -
        fderiv ℝ WM (WithLp.toLp 2 y)
          (WithLp.toLp 2 (Pi.single ⟨i - 1, by omega⟩ 1 - Pi.single ⟨i, by omega⟩ 1))| ≤
        2 * ((n : ℝ) * (2 * p.val.2 * ((N : ℝ) / 2) ^ (-p.val.2 - 1) *
            ∑' k : ℤ, |(k : ℝ)| ^ (-p.val.2 - 1)) +
          B a + B b + 2 * 2 ^ (p.val.2 + 1) * (((N : ℕ) - n - 1 : ℕ) : ℝ) ^ (-p.val.2) +
          (p.val.2 * 2 ^ (p.val.2 + 1) *
            (1 + ∑' k : ℤ, |(k : ℝ)| ^ (-p.val.2 - 1))) *
              ((N : ℝ) ^ (-p.val.2) + (M : ℝ) ^ (-p.val.2))) := by
  obtain ⟨WN, hWN, hvN, hdN⟩ := physical_pinned_force_decomposition p N hN
  obtain ⟨WM, hWM, hvM, hdM⟩ := physical_pinned_force_decomposition p M (hN.trans hNM)
  refine ⟨WN, WM, hWN, hWM, hvN, hvM, ?_⟩
  intro n i hi hin hn x hx y hy hxy hmass γ A hγ hγ1 hA hT hXR hXL hYR hYL
  have hcommon := internal_signed_common_force_error p N M hNM hi hin (by omega)
    x hx y hy hxy hmass
  have hext := internal_physical_exterior_comparison p N M hNM hi hin hn
    x hx y hy hxy hγ hγ1 hA hT hXR hXL hYR hYL
  dsimp only at hext ⊢
  rw [hdN x hx n i hi hin (by omega), hdM y hy n i hi hin (by omega)]
  have triangle (r l e r' l' e' P Q : ℝ)
      (hc : |(r - l) - (r' - l')| ≤ P) (he : |e - e'| ≤ Q) :
      |-2 * (r + e - l) - -2 * (r' + e' - l')| ≤ 2 * (P + Q) := by
    calc
      _ = 2 * |((r - l) - (r' - l')) + (e - e')| := by
        rw [show -2 * (r + e - l) - -2 * (r' + e' - l') =
          -2 * (((r - l) - (r' - l')) + (e - e')) by ring,
          abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 2 * (|(r - l) - (r' - l')| + |e - e'|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
      _ ≤ _ := by linarith
  have hh := triangle _ _ _ _ _ _ _ _ hcommon hext
  linarith

/-- Internal constant bookkeeping in Appendix C.
The single output constant depends only on the exponent, before `γ`, the
forcing scale, both volumes and both boundary distances. -/
theorem internal_force_bound_absorb (s : ℝ) (hs : 0 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ n N M : ℕ, 1 ≤ n → 4 * n ≤ N → N ≤ M →
      ∀ γ A T a b F : ℝ, 0 ≤ A → 0 ≤ T → 0 < a → 0 < b →
      (let B := fun t : ℝ => 4 * s * T * t ^ (-s - 1) +
          8 * (s + 1) * 2 ^ (s + 2) * A * t ^ (γ - s - 1)
       |F| ≤ 2 * ((n : ℝ) * (2 * s * ((N : ℝ) / 2) ^ (-s - 1) *
           ∑' k : ℤ, |(k : ℝ)| ^ (-s - 1)) +
         B a + B b + 2 * 2 ^ (s + 1) * (((N - n - 1 : ℕ)) : ℝ) ^ (-s) +
         (s * 2 ^ (s + 1) * (1 + ∑' k : ℤ, |(k : ℝ)| ^ (-s - 1))) *
           ((N : ℝ) ^ (-s) + (M : ℝ) ^ (-s)))) →
      |F| ≤ C * (T * a ^ (-s - 1) + A * a ^ (γ - s - 1) +
        (T * b ^ (-s - 1) + A * b ^ (γ - s - 1))) + C * (N : ℝ) ^ (-s) := by
  let S := ∑' k : ℤ, |(k : ℝ)| ^ (-s - 1)
  have hS : 0 ≤ S := tsum_nonneg fun k => Real.rpow_nonneg (abs_nonneg _) _
  let J := s * 2 ^ (s + 1) * (1 + S)
  let K := 4 * s + 8 * (s + 1) * 2 ^ (s + 2)
  let D : ℝ := 2 * 2 ^ (s + 1) * 2 ^ s
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨2 * (K + 4 * J + D + 1), by positivity, ?_⟩
  intro n N M hn hN hNM γ A T a b F hA hT ha hb hF
  dsimp only at hF
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hMp : (N : ℝ) ≤ M := by exact_mod_cast hNM
  have hnr : (n : ℝ) ≤ N := by exact_mod_cast (show n ≤ N by omega)
  have hscale : (N : ℝ) * ((N : ℝ) / 2) ^ (-s - 1) =
      2 ^ (s + 1) * (N : ℝ) ^ (-s) := by
    rw [div_eq_mul_inv, Real.mul_rpow hNp.le (by norm_num),
      Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num),
      show -(-s - 1) = s + 1 by ring]
    calc
      _ = 2 ^ (s + 1) * ((N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-s - 1)) := by
        rw [Real.rpow_one]
        ring
      _ = _ := by rw [← Real.rpow_add hNp, show 1 + (-s - 1) = -s by ring]
  have hc : (n : ℝ) * (2 * s * ((N : ℝ) / 2) ^ (-s - 1) * S) ≤
      2 * J * (N : ℝ) ^ (-s) := by
    calc
      _ ≤ (N : ℝ) * (2 * s * ((N : ℝ) / 2) ^ (-s - 1) * S) :=
        mul_le_mul_of_nonneg_right hnr (by positivity)
      _ = 2 * s * S * ((N : ℝ) * ((N : ℝ) / 2) ^ (-s - 1)) := by ring
      _ = 2 * s * S * (2 ^ (s + 1) * (N : ℝ) ^ (-s)) := by rw [hscale]
      _ ≤ _ := by dsimp [J]; nlinarith [Real.rpow_nonneg hNp.le (-s),
        mul_nonneg hs.le (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (s + 1))]
  have ht := mul_le_mul_of_nonneg_left (exterior_rank_tail_le hs n N hn hN)
    (show 0 ≤ 2 * (2 : ℝ) ^ (s + 1) by positivity)
  have ht' : 2 * 2 ^ (s + 1) * (((N - n - 1 : ℕ)) : ℝ) ^ (-s) ≤
      D * (N : ℝ) ^ (-s) := ht.trans_eq (by dsimp [D]; ring)
  have himg : J * ((N : ℝ) ^ (-s) + (M : ℝ) ^ (-s)) ≤ 2 * J * (N : ℝ) ^ (-s) := by
    have hpow := Real.rpow_le_rpow_of_nonpos hNp hMp (by linarith : -s ≤ 0)
    nlinarith
  have hB (t : ℝ) (ht : 0 < t) :
      4 * s * T * t ^ (-s - 1) + 8 * (s + 1) * 2 ^ (s + 2) * A * t ^ (γ - s - 1) ≤
        K * (T * t ^ (-s - 1) + A * t ^ (γ - s - 1)) := by
    dsimp only [K]
    have hp := mul_nonneg hT (Real.rpow_nonneg ht.le (-s - 1))
    have hq := mul_nonneg hA (Real.rpow_nonneg ht.le (γ - s - 1))
    nlinarith [mul_nonneg (show 0 ≤ 4 * s by positivity) hq,
      mul_nonneg (show 0 ≤ 8 * (s + 1) * 2 ^ (s + 2) by positivity) hp]
  have hBa := hB a ha
  have hBb := hB b hb
  have hz : 0 ≤ (N : ℝ) ^ (-s) := Real.rpow_nonneg hNp.le _
  have hu : 0 ≤ T * a ^ (-s - 1) + A * a ^ (γ - s - 1) +
      (T * b ^ (-s - 1) + A * b ^ (γ - s - 1)) := by positivity
  change |F| ≤ 2 * (K + 4 * J + D + 1) * _ + 2 * (K + 4 * J + D + 1) * _
  have hSe : (∑' k : ℤ, |(k : ℝ)| ^ (-s - 1)) = S := rfl
  have hJe : s * 2 ^ (s + 1) * (1 + S) = J := rfl
  rw [hSe, hJe] at hF
  nlinarith only [hF, hc, ht', himg, hBa, hBb,
    mul_nonneg (show 0 ≤ 4 * J + D + 1 by positivity) hu,
    mul_nonneg (show 0 ≤ K + 1 by positivity) hz]

/-- The force inequality of Appendix C.
The constant is chosen before the tolerance and temperature, and the size
threshold before the volumes and configurations. The two full physical
cycles have the same active coordinates, so their final coordinates are
exactly compatible fixed exteriors. The oscillation clause is separate. -/
theorem exterior_force_difference (s : ℝ) (hs : 0 < s) (_hs1 : s ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
      ε < min (1 - min s 1 / 2) (s - min s 1 / 2) / 4 →
      ∃ n₀ : ℕ, ∀ (n : ℕ) (N M : ℕ+) (_hnn : n₀ ≤ n) (hn : 2 ≤ n)
        (hN : 4 * n ≤ (N : ℕ)) (hNM : (N : ℕ) ≤ (M : ℕ)),
        (n : ℝ) ^ (2 / s) ≤ (N : ℝ) →
        ∃ WN : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
          ∃ WM : EuclideanSpace ℝ (Fin (M : ℕ)) → ℝ,
        ∀ p : Parameters, p.val.2 = s →
        ContDiffOn ℝ ∞ WN (gapAmbientDomain N) ∧
        ContDiffOn ℝ ∞ WM (gapAmbientDomain M) ∧
        (∀ x : {x : EuclideanSpace ℝ (Fin (N : ℕ)) // x ∈ gapAmbientDomain N},
          WN x.val = physicalAmbientGapEnergy p N x) ∧
        (∀ y : {y : EuclideanSpace ℝ (Fin (M : ℕ)) // y ∈ gapAmbientDomain M},
          WM y.val = physicalAmbientGapEnergy p M y) ∧
        ∀ (i : ℕ) (hi : 0 < i) (hin : i < n)
          (x : Fin (N : ℕ) → ℝ) (hx : x ∈ Riesz1.gapSimplex N)
          (y : Fin (M : ℕ) → ℝ) (hy : y ∈ Riesz1.gapSimplex M),
        (∀ k : Fin n, x ⟨k.val, by have := k.isLt; omega⟩ =
          y ⟨k.val, by have := k.isLt; omega⟩) →
        |(∑ k : Fin n, x ⟨k.val, by have := k.isLt; omega⟩) - (n : ℝ)| ≤
          (n : ℝ) ^ (min s 1 / 2 + ε) →
        (∀ r : ℕ, 0 < r → r ≤ (N : ℕ) - n →
          |cyclicGapSum N ⟨n, by omega⟩ r x - r| ≤
            4 * (n : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε)) →
        (∀ r : ℕ, (hr : 0 < r) → (hrn : r ≤ (N : ℕ) - n) →
          |cyclicGapSum N ⟨(N : ℕ) - r, by omega⟩ r x - r| ≤
            4 * (n : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε)) →
        (∀ r : ℕ, 0 < r → r ≤ (M : ℕ) - n →
          |cyclicGapSum M ⟨n, by omega⟩ r y - r| ≤
            4 * (n : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε)) →
        (∀ r : ℕ, (hr : 0 < r) → (hrn : r ≤ (M : ℕ) - n) →
          |cyclicGapSum M ⟨(M : ℕ) - r, by omega⟩ r y - r| ≤
            4 * (n : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε)) →
        let a := cyclicGapSum N ⟨i, by omega⟩ (n - i) x
        let b := cyclicGapSum N 0 i x
        let T := (16 * (n : ℝ) ^ ε) ^ (1 / (1 - (min s 1 / 2 + ε)))
        |fderiv ℝ WN (WithLp.toLp 2 x)
            (WithLp.toLp 2 (Pi.single ⟨i - 1, by omega⟩ 1 - Pi.single ⟨i, by omega⟩ 1)) -
          fderiv ℝ WM (WithLp.toLp 2 y)
            (WithLp.toLp 2 (Pi.single ⟨i - 1, by omega⟩ 1 - Pi.single ⟨i, by omega⟩ 1))| ≤
          C * (T * a ^ (-s - 1) + (n : ℝ) ^ ε * a ^ (min s 1 / 2 + ε - s - 1) +
            (T * b ^ (-s - 1) + (n : ℝ) ^ ε * b ^ (min s 1 / 2 + ε - s - 1))) +
          C * (N : ℝ) ^ (-s) := by
  obtain ⟨C, hC, hbound⟩ := internal_force_bound_absorb s hs
  refine ⟨C, hC, ?_⟩
  intro ε hε hεs
  have hσ : min s 1 / 2 < 1 := by linarith [min_le_right s 1]
  have hσ0 : 0 ≤ min s 1 / 2 := by positivity
  have hεσ : ε < (1 - min s 1 / 2) / 4 :=
    hεs.trans_le (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hγ1 : min s 1 / 2 + ε < 1 := by linarith
  obtain ⟨n₀, hn₀⟩ := exterior_rank_threshold hσ hε hεσ
  refine ⟨n₀, ?_⟩
  intro n N M hnn hn hN hNM _hsize
  let p₀ : Parameters := ⟨(1, s), by exact ⟨by norm_num, hs, _hs1⟩⟩
  obtain ⟨WN, WM, hWN, hWM, hvN, hvM, hc⟩ :=
    internal_physical_force_composition p₀ N M hNM (by omega)
  refine ⟨WN, WM, ?_⟩
  intro p hps
  have henergy (Q : ℕ+) (z : {z : EuclideanSpace ℝ (Fin (Q : ℕ)) // z ∈ gapAmbientDomain Q}) :
      physicalAmbientGapEnergy p₀ Q z = physicalAmbientGapEnergy p Q z := by
    unfold physicalAmbientGapEnergy
    congr 1
    · exact congrArg (fun t : ℝ => (Q : ℝ) ^ (-t)) hps.symm
    · apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro r _
      congr 1
      unfold kernelAtParameters
      simp only [p₀, hps]
  refine ⟨hWN, hWM, fun x => (hvN x).trans (henergy N x),
    fun y => (hvM y).trans (henergy M y), ?_⟩
  intro i hi hin x hx y hy hxy hlength hXR hXL hYR hYL
  have hhalf := internal_half_period_of_length (⟨n, by omega⟩ : ℕ+) N hγ1.le hN hlength
  have hA : 1 ≤ (n : ℝ) ^ ε := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n by omega)) hε.le
  have hT := hn₀ n hnn N hN
  have hh := hc n i hi hin (by omega) x hx y hy hxy hhalf
    (min s 1 / 2 + ε) ((n : ℝ) ^ ε) (by linarith) hγ1 hA hT hXR hXL hYR hYL
  dsimp only [p₀] at hh
  dsimp only
  let F := fderiv ℝ WN (WithLp.toLp 2 x)
      (WithLp.toLp 2 (Pi.single ⟨i - 1, by omega⟩ 1 - Pi.single ⟨i, by omega⟩ 1)) -
    fderiv ℝ WM (WithLp.toLp 2 y)
      (WithLp.toLp 2 (Pi.single ⟨i - 1, by omega⟩ 1 - Pi.single ⟨i, by omega⟩ 1))
  exact hbound n N M (by omega) hN hNM (min s 1 / 2 + ε) ((n : ℝ) ^ ε)
    _ _ _ F (Real.rpow_nonneg (by positivity) _) (by positivity)
    (PhysicalEnergy.gapSum_mem N _ (by omega : 0 < n - i) (by omega) x hx).1
    (PhysicalEnergy.gapSum_mem N 0 hi (by omega) x hx).1 hh

/-- See Subsection 6.1 of the paper: the rigidity event is convex.
In particular its intersection with any fixed-mass simplex is convex. -/
theorem convex_goodBlockEvent (s : ℝ) (n N : ℕ+) (η : ℝ) :
    Convex ℝ (goodBlockEvent s n N η) := by
  intro x hx y hy a b ha hb hab
  change (∑ i : Fin (n : ℕ), (a * x i + b * y i)) < (N : ℝ) ∧ _
  have hsum : (∑ i, (a * x i + b * y i)) = a * (∑ i, x i) + b * (∑ i, y i) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  refine ⟨?_, ?_, ?_⟩
  · rw [hsum]
    rcases eq_or_lt_of_le ha with h | h
    · have ha0 : a = 0 := h.symm
      have hb1 : b = 1 := by linarith
      simpa only [ha0, hb1, zero_mul, one_mul, zero_add] using hy.1
    · have hh := mul_lt_mul_of_pos_left hx.1 h
      have hh' := mul_le_mul_of_nonneg_left hy.1.le hb
      nlinarith
  · intro i
    change (n : ℝ) ^ (-η) ≤ a * x i + b * y i ∧ a * x i + b * y i ≤ (n : ℝ) ^ η
    have hxi := hx.2.1 i
    have hyi := hy.2.1 i
    constructor
    · calc
        _ = a * (n : ℝ) ^ (-η) + b * (n : ℝ) ^ (-η) := by rw [← add_mul, hab, one_mul]
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hxi.1 ha)
          (mul_le_mul_of_nonneg_left hyi.1 hb)
    · calc
        _ ≤ a * (n : ℝ) ^ η + b * (n : ℝ) ^ η :=
          add_le_add (mul_le_mul_of_nonneg_left hxi.2 ha) (mul_le_mul_of_nonneg_left hyi.2 hb)
        _ = _ := by rw [← add_mul, hab, one_mul]
  · intro c d hcd hdn
    have hxc := hx.2.2 c d hcd hdn
    have hyc := hy.2.2 c d hcd hdn
    let S := Finset.univ.filter (fun i : Fin (n : ℕ) => c ≤ i.val ∧ i.val < d)
    change |(∑ i ∈ S, (a * x i + b * y i)) - (d - c : ℕ)| ≤ _
    have he : (∑ i ∈ S, (a * x i + b * y i)) - (d - c : ℕ) =
        a * ((∑ i ∈ S, x i) - (d - c : ℕ)) +
        b * ((∑ i ∈ S, y i) - (d - c : ℕ)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      nlinarith
    rw [he]
    calc
      _ ≤ |a * ((∑ i ∈ S, x i) - (d - c : ℕ))| +
          |b * ((∑ i ∈ S, y i) - (d - c : ℕ))| := abs_add_le _ _
      _ = a * |(∑ i ∈ S, x i) - (d - c : ℕ)| +
          b * |(∑ i ∈ S, y i) - (d - c : ℕ)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * ((n : ℝ) ^ η * (d - c : ℕ) ^ (min s 1 / 2)) +
          b * ((n : ℝ) ^ η * (d - c : ℕ) ^ (min s 1 / 2)) :=
        add_le_add (mul_le_mul_of_nonneg_left hxc ha) (mul_le_mul_of_nonneg_left hyc hb)
      _ = _ := by rw [← add_mul, hab, one_mul]

/-- The two rigidity constraints and fixed total mass give the minimum
of the prefix and suffix ranks in the oscillation proof of Appendix C. -/
theorem goodBlockEvent_prefix_difference (s : ℝ) (n N : ℕ+) (η : ℝ)
    (x y : Fin (n : ℕ) → ℝ) (hx : x ∈ goodBlockEvent s n N η)
    (hy : y ∈ goodBlockEvent s n N η) (hmass : ∑ k, x k = ∑ k, y k)
    (i : ℕ) (hi : 0 < i) (hin : i < (n : ℕ)) :
    |(∑ k ∈ Finset.univ.filter (fun k : Fin (n : ℕ) => k.val < i), x k) -
      (∑ k ∈ Finset.univ.filter (fun k : Fin (n : ℕ) => k.val < i), y k)| ≤
      2 * (n : ℝ) ^ η * (min i ((n : ℕ) - i) : ℕ) ^ (min s 1 / 2) := by
  let P := Finset.univ.filter (fun k : Fin (n : ℕ) => k.val < i)
  let Q := Finset.univ.filter (fun k : Fin (n : ℕ) => i ≤ k.val)
  have hpz (z : Fin (n : ℕ) → ℝ) (hz : z ∈ goodBlockEvent s n N η) :
      |(∑ k ∈ P, z k) - (i : ℝ)| ≤ (n : ℝ) ^ η * (i : ℝ) ^ (min s 1 / 2) := by
    simpa only [P, Nat.zero_le, true_and, Nat.sub_zero] using hz.2.2 0 i hi hin.le
  have hqz (z : Fin (n : ℕ) → ℝ) (hz : z ∈ goodBlockEvent s n N η) :
      |(∑ k ∈ Q, z k) - ((n : ℕ) - i : ℕ)| ≤
        (n : ℝ) ^ η * ((n : ℕ) - i : ℕ) ^ (min s 1 / 2) := by
    have he : Finset.univ.filter (fun k : Fin (n : ℕ) => i ≤ k.val ∧ k.val < (n : ℕ)) = Q := by
      ext k
      simp only [Q, Finset.mem_filter, Finset.mem_univ, true_and, k.isLt, and_true]
    simpa only [he] using hz.2.2 i n hin le_rfl
  have bound (u v c B : ℝ) (hu : |u - c| ≤ B) (hv : |v - c| ≤ B) : |u - v| ≤ 2 * B := by
    calc
      _ = |(u - c) - (v - c)| := by congr 1; ring
      _ ≤ |u - c| + |v - c| := abs_sub _ _
      _ ≤ _ := by linarith
  rcases le_total i ((n : ℕ) - i) with h | h
  · rw [min_eq_left h]
    exact (bound _ _ _ _ (hpz x hx) (hpz y hy)).trans_eq (by ring)
  · rw [min_eq_right h]
    have hsplit (z : Fin (n : ℕ) → ℝ) : (∑ k ∈ P, z k) + (∑ k ∈ Q, z k) = ∑ k, z k := by
      simpa only [P, Q, not_lt] using Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun k : Fin (n : ℕ) => k.val < i) z
    have he : (∑ k ∈ P, x k) - (∑ k ∈ P, y k) =
        -((∑ k ∈ Q, x k) - (∑ k ∈ Q, y k)) := by
      have hhx := hsplit x
      have hhy := hsplit y
      linarith
    change |(∑ k ∈ P, x k) - (∑ k ∈ P, y k)| ≤ _
    rw [he, abs_neg]
    exact (bound _ _ _ _ (hqz x hx) (hqz y hy)).trans_eq (by ring)

/-- An absolute exterior-force bound with no lower bound on the number
of exterior ranks. This is the bounded-size ingredient in Appendix C and the proof of Proposition 6.6.
The integer series converges for every `s > 0`. -/
theorem internal_principal_exterior_absolute_bound {s γ A a : ℝ} (hs : 0 < s)
    (hγ1 : γ < 1) (hA : 1 ≤ A) (ha : 0 < a)
    (M : ℕ) (Y : Fin M → ℝ) (hY0 : ∀ r, 0 ≤ Y r)
    (hY : ∀ r, |Y r - (r.val + 1 : ℝ)| ≤ 4 * A * (r.val + 1 : ℝ) ^ γ) :
    |∑ r, -s * (a + Y r) ^ (-s - 1)| ≤
      2 * s * (16 * A) ^ (1 / (1 - γ)) * a ^ (-s - 1) +
        s * 2 ^ (s + 1) * ∑' k : ℕ, (k : ℝ) ^ (-s - 1) := by
  classical
  let T := (16 * A) ^ (1 / (1 - γ))
  let S := Finset.univ.filter (fun r : Fin M => (r.val + 1 : ℝ) < T)
  let f := fun r : Fin M => s * (a + Y r) ^ (-s - 1)
  have hT : 1 ≤ T := Real.one_le_rpow (by nlinarith) (by positivity)
  have hTp : 0 < T := by linarith
  have hf : ∀ r, 0 ≤ f r := fun r =>
    mul_nonneg hs.le (Real.rpow_nonneg (by linarith [hY0 r]) _)
  have hsmall : (∑ r ∈ S, f r) ≤ 2 * s * T * a ^ (-s - 1) := by
    have hterm (r : Fin M) : f r ≤ s * a ^ (-s - 1) := by
      apply mul_le_mul_of_nonneg_left _ hs.le
      exact Real.rpow_le_rpow_of_nonpos ha (by linarith [hY0 r]) (by linarith)
    calc
      _ ≤ ∑ _ ∈ Finset.range ⌈T⌉₊, s * a ^ (-s - 1) := by
        apply Finset.sum_le_sum_of_injOn (fun r : Fin M => r.val)
          Fin.val_injective.injOn ?_ (fun r _ => hterm r)
        · intro _ _ _
          positivity
        · intro r hr
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hr
          rw [Finset.mem_range]
          have hkt := (Finset.mem_filter.mp hk).2
          have hceil : T ≤ (⌈T⌉₊ : ℝ) := Nat.le_ceil T
          exact_mod_cast (show (k.val : ℝ) < ⌈T⌉₊ by linarith)
      _ = (⌈T⌉₊ : ℝ) * (s * a ^ (-s - 1)) := by simp
      _ ≤ (2 * T) * (s * a ^ (-s - 1)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hh := Nat.ceil_lt_add_one hTp.le
        linarith
      _ = _ := by ring
  have hseries : Summable (fun k : ℕ => (k : ℝ) ^ (-s - 1)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have href : (∑ r : Fin M, (r.val + 1 : ℝ) ^ (-s - 1)) ≤
      ∑' k : ℕ, (k : ℝ) ^ (-s - 1) := by
    calc
      _ ≤ ∑ k ∈ Finset.range (M + 1), (k : ℝ) ^ (-s - 1) := by
        apply Finset.sum_le_sum_of_injOn (fun r : Fin M => r.val + 1)
          (by intro r _ t _ hrt; apply Fin.ext; dsimp only at hrt; omega)
          ?_ (by intro r _; simp only [Nat.cast_add, Nat.cast_one, le_refl])
        · intro _ _ _
          positivity
        · intro r hr
          obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hr
          exact Finset.mem_range.mpr (by have := t.isLt; omega)
      _ ≤ _ := hseries.sum_le_tsum _ (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hlarge (r : Fin M) (hr : r ∈ Finset.univ \ S) :
      f r ≤ s * 2 ^ (s + 1) * (r.val + 1 : ℝ) ^ (-s - 1) := by
    have hrt : T ≤ (r.val + 1 : ℝ) := by
      simpa only [S, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter,
        true_and, not_lt] using hr
    have hlow := (internal_large_rank_geometry (by linarith : 0 < A) hγ1 hrt (hY r)).2
    have hp := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (r.val + 1 : ℝ) / 2)
      (by linarith : (r.val + 1 : ℝ) / 2 ≤ a + Y r) (by linarith : -s - 1 ≤ 0)
    have he : ((r.val + 1 : ℝ) / 2) ^ (-s - 1) =
        2 ^ (s + 1) * (r.val + 1 : ℝ) ^ (-s - 1) := by
      rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by norm_num),
        Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num),
        show -(-s - 1) = s + 1 by ring, mul_comm]
    exact (mul_le_mul_of_nonneg_left hp hs.le).trans_eq (by rw [he]; ring)
  have hl : (∑ r ∈ Finset.univ \ S, f r) ≤
      s * 2 ^ (s + 1) * ∑' k : ℕ, (k : ℝ) ^ (-s - 1) := by
    calc
      _ ≤ ∑ r ∈ Finset.univ \ S, s * 2 ^ (s + 1) * (r.val + 1 : ℝ) ^ (-s - 1) :=
        Finset.sum_le_sum hlarge
      _ ≤ ∑ r : Fin M, s * 2 ^ (s + 1) * (r.val + 1 : ℝ) ^ (-s - 1) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (by intro r hr; exact (Finset.mem_sdiff.mp hr).1)
        intro r _ _
        positivity
      _ = s * 2 ^ (s + 1) * ∑ r : Fin M, (r.val + 1 : ℝ) ^ (-s - 1) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left href (by positivity)
  calc
    _ = ∑ r, f r := by
      simp only [neg_mul, Finset.sum_neg_distrib, abs_neg]
      exact abs_of_nonneg (Finset.sum_nonneg fun r _ => hf r)
    _ = (∑ r ∈ S, f r) + ∑ r ∈ Finset.univ \ S, f r :=
      (Finset.sum_add_sum_compl S f).symm
    _ ≤ _ := add_le_add hsmall hl

/-- A linear differential on a mass simplex pairs with a tangent velocity
by its pinned forces and the prefix velocities. This is the exact
summation by parts needed to integrate Appendix C,
and also identifies the representative in Lemma 6.4. -/
theorem linear_pinned_pairing {n : ℕ}
    (L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ)
    (v : Fin (n + 1) → ℝ) (hv : ∑ j, v j = 0) :
    L (WithLp.toLp 2 v) =
      ∑ i : Fin n, L (WithLp.toLp 2 (Pi.single i.castSucc 1 - Pi.single i.succ 1)) *
        ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => j.val ≤ i.val), v j := by
  let q := fun j : Fin (n + 1) => L (WithLp.toLp 2 (Pi.single j 1))
  have hL : L (WithLp.toLp 2 v) = ∑ j, q j * v j := by
    have hr := (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).sum_repr (WithLp.toLp 2 v)
    have hh := congrArg L hr
    rw [map_sum] at hh
    simp only [map_smul, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply,
      smul_eq_mul] at hh
    change (∑ j, v j * q j) = _ at hh
    simpa only [mul_comm] using hh.symm
  have hp := InteractionDifferential.pinnedRepresentative_pairing
    (fun i : Fin n => q i.castSucc - q i.succ) v hv
  rw [InteractionDifferential.pinnedRepresentative_coefficient_pairing q v hv] at hp
  rw [hL, hp]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change L (WithLp.toLp 2 (Pi.single i.castSucc 1)) -
      L (WithLp.toLp 2 (Pi.single i.succ 1)) = _
  change L (WithLp.toLp 2 (Pi.single i.castSucc (1 : ℝ))) -
    L (WithLp.toLp 2 (Pi.single i.succ (1 : ℝ))) =
    L (WithLp.toLp 2 (Pi.single i.castSucc (1 : ℝ)) -
      WithLp.toLp 2 (Pi.single i.succ (1 : ℝ)))
  exact (L.map_sub _ _).symm

/-- Internal segment integration for Appendix C. Pinned derivatives pair with the actual
prefix displacement, so integration introduces no dimension-dependent
norm comparison. -/
theorem internal_segment_pinned_bound {n : ℕ}
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (x y : EuclideanSpace ℝ (Fin (n + 1)))
    (hmass : ∑ j, x j = ∑ j, y j) (B : Fin n → ℝ)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ f (x + t • (y - x)))
    (hB : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin n,
      |fderiv ℝ f (x + t • (y - x))
        (WithLp.toLp 2 (Pi.single i.castSucc 1 - Pi.single i.succ 1))| ≤ B i) :
    |f y - f x| ≤ ∑ i : Fin n, B i *
      |∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => j.val ≤ i.val), (y j - x j)| := by
  let z := fun t : ℝ => x + t • (y - x)
  let g := fun t : ℝ => f (z t)
  let g' := fun t : ℝ => fderiv ℝ f (z t) (y - x)
  have hz (t : ℝ) : HasDerivAt z (y - x) t := by
    convert! ((hasDerivAt_id t).smul_const (y - x)).const_add x using 1
    simp only [one_smul]
  have hg (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : HasDerivAt g (g' t) t :=
    (hf t ht).hasFDerivAt.comp_hasDerivAt t (hz t)
  have hv : ∑ j : Fin (n + 1), (y j - x j) = 0 := by
    rw [Finset.sum_sub_distrib, hmass, sub_self]
  have hbound (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
      ‖g' t‖ ≤ ∑ i : Fin n, B i *
        |∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => j.val ≤ i.val), (y j - x j)| := by
    dsimp only [g']
    have he : y - x = WithLp.toLp 2 (fun j => y j - x j) := by ext j; rfl
    rw [he, linear_pinned_pairing (fderiv ℝ f (z t)) (fun j => y j - x j) hv, Real.norm_eq_abs]
    calc
      _ ≤ ∑ i : Fin n, |fderiv ℝ f (z t)
          (WithLp.toLp 2 (Pi.single i.castSucc 1 - Pi.single i.succ 1)) *
          ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => j.val ≤ i.val), (y j - x j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hB t ⟨ht.1, ht.2.le⟩ i) (abs_nonneg _)
  have hh := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht => (hg t ht).hasDerivWithinAt) hbound
  simpa only [g, z, zero_smul, add_zero, one_smul, add_sub_cancel, Real.norm_eq_abs] using hh

/-- Pulling a differentiable energy through the literal fixed-exterior
assembly preserves each pinned particle derivative. This is the physical
chart bridge used by Appendix C and Lemma 6.4. -/
theorem internal_assembled_pinned_derivative (e a : ℕ) (he : 0 < e)
    (y : EuclideanSpace ℝ (Fin e)) (u : EuclideanSpace ℝ (Fin (a + 1)))
    (W : EuclideanSpace ℝ (Fin (e + a + 1)) → ℝ)
    (hW : DifferentiableAt ℝ W
      (RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y u))
    (j : Fin a) :
    fderiv ℝ (fun v => W (RetainedSimplex.assemble e a
        (InterpolatingDensities.exteriorPermutation e a) y v)) u
      (WithLp.toLp 2 (Pi.single j.castSucc 1 - Pi.single j.succ 1)) =
      fderiv ℝ W (RetainedSimplex.assemble e a
        (InterpolatingDensities.exteriorPermutation e a) y u)
        (WithLp.toLp 2 (Pi.single ⟨j.val, by have := j.isLt; omega⟩ 1 -
          Pi.single ⟨j.val + 1, by have := j.isLt; omega⟩ 1)) := by
  let E := EuclideanSpace ℝ (Fin e)
  let F := EuclideanSpace ℝ (Fin (a + 1))
  let G := EuclideanSpace ℝ (Fin (e + a + 1))
  have : ContinuousSMul ℝ (E × F) := Prod.continuousSMul
  let J : E × F →L[ℝ] G :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
      (InterpolatingDensities.exteriorPermutation e a)).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (RetainedSimplex.join e (a + 1)).toContinuousLinearEquiv.toContinuousLinearMap
  let A : F →L[ℝ] G := J.comp (ContinuousLinearMap.inr ℝ E F)
  have hmap : HasFDerivAt (RetainedSimplex.assemble e a
      (InterpolatingDensities.exteriorPermutation e a) y) A u := by
    have hp : HasFDerivAt (fun v : F => (y, v)) (ContinuousLinearMap.inr ℝ E F) u := by
      convert! (hasFDerivAt_const y u).prodMk (hasFDerivAt_id u) using 1
    exact J.hasFDerivAt.comp u hp
  have hchain := hW.hasFDerivAt.comp u hmap
  change (fderiv ℝ (W ∘ RetainedSimplex.assemble e a
    (InterpolatingDensities.exteriorPermutation e a) y) u) _ = _
  rw [hchain.fderiv]
  change fderiv ℝ W _ (A _) = _
  congr 1
  have hA (v : F) : A v = RetainedSimplex.assemble e a
      (InterpolatingDensities.exteriorPermutation e a) 0 v := rfl
  rw [hA]
  ext k
  by_cases hk : k.val < a + 1
  · have hidx : k = Fin.castLE (show a + 1 ≤ e + a + 1 by omega) ⟨k.val, hk⟩ := by
      apply Fin.ext
      rfl
    rw [hidx, InterpolatingDensities.assemble_exterior_active]
    simp only [Pi.sub_apply, Pi.single_apply,
      Fin.ext_iff, Fin.val_castSucc, Fin.val_succ, Fin.val_castLE]
  · have hidx : k = (⟨a + 1 + (k.val - (a + 1)), by have := k.isLt; omega⟩ :
        Fin (e + a + 1)) := by apply Fin.ext; dsimp only; omega
    rw [hidx, assemble_exterior_retained e a (0 : E) _
      ⟨k.val - (a + 1), by have := k.isLt; omega⟩]
    have hj := j.isLt
    simp only [PiLp.zero_apply, Pi.sub_apply, Pi.single_apply, Fin.ext_iff]
    have h₁ : a + 1 + (k.val - (a + 1)) ≠ j.val := by omega
    have h₂ : a + 1 + (k.val - (a + 1)) ≠ j.val + 1 := by omega
    simp only [h₁, h₂, ↓reduceIte, sub_self]

/-- Internal rigidity-set integration for Appendix C. The fixed-mass segment and its prefix
displacements are proved from the event. Only the analytic
differential bounds remain inputs to this internal calculus helper. -/
theorem internal_rigidity_segment_bound {n : ℕ} (N : ℕ+) (s η : ℝ)
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (x y : EuclideanSpace ℝ (Fin (n + 1)))
    (hx : WithLp.ofLp x ∈ goodBlockEvent s n.succPNat N η)
    (hy : WithLp.ofLp y ∈ goodBlockEvent s n.succPNat N η)
    (hmass : ∑ j, x j = ∑ j, y j) (B : Fin n → ℝ)
    (hf : ∀ z : EuclideanSpace ℝ (Fin (n + 1)),
      WithLp.ofLp z ∈ goodBlockEvent s n.succPNat N η →
      (∑ j, z j) = ∑ j, x j → DifferentiableAt ℝ f z)
    (hB : ∀ z : EuclideanSpace ℝ (Fin (n + 1)),
      WithLp.ofLp z ∈ goodBlockEvent s n.succPNat N η →
      (∑ j, z j) = ∑ j, x j → ∀ i : Fin n,
      |fderiv ℝ f z
        (WithLp.toLp 2 (Pi.single i.castSucc 1 - Pi.single i.succ 1))| ≤ B i) :
    |f y - f x| ≤ 2 * (n.succPNat : ℝ) ^ η *
      ∑ i : Fin n, B i * (min (i.val + 1) (n - i.val) : ℕ) ^ (min s 1 / 2) := by
  have hsegment (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      WithLp.ofLp (x + t • (y - x)) ∈ goodBlockEvent s n.succPNat N η ∧
      (∑ j, (x + t • (y - x)) j) = ∑ j, x j := by
    have he : WithLp.ofLp (x + t • (y - x)) =
        (1 - t) • WithLp.ofLp x + t • WithLp.ofLp y := by
      ext j
      simp only [Pi.add_apply, Pi.smul_apply, PiLp.add_apply, PiLp.smul_apply,
        PiLp.sub_apply, smul_eq_mul]
      ring
    refine ⟨he ▸ (convex_goodBlockEvent s n.succPNat N η) hx hy
      (sub_nonneg.mpr ht.2) ht.1 (by ring), ?_⟩
    change (∑ j, (x j + t * (y j - x j))) = _
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hmass,
      sub_self, mul_zero, add_zero]
  have hh := internal_segment_pinned_bound f x y hmass B
    (fun t ht => hf _ (hsegment t ht).1 (hsegment t ht).2)
    (fun t ht => hB _ (hsegment t ht).1 (hsegment t ht).2)
  apply hh.trans
  have hB0 (i : Fin n) : 0 ≤ B i := (abs_nonneg _).trans (hB x hx rfl i)
  calc
    _ ≤ ∑ i : Fin n, B i *
        (2 * (n.succPNat : ℝ) ^ η * (min (i.val + 1) (n - i.val) : ℕ) ^ (min s 1 / 2)) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hB0 i)
      have hp := goodBlockEvent_prefix_difference s n.succPNat N η
        (WithLp.ofLp y) (WithLp.ofLp x) hy hx hmass.symm (i.val + 1) (by omega)
        (by change i.val + 1 < n + 1; have := i.isLt; omega)
      have hsub : n + 1 - (i.val + 1) = n - i.val := by omega
      convert! hp using 1 <;>
        simp only [Finset.sum_sub_distrib, Nat.lt_succ_iff, Nat.succPNat_coe, hsub]
      rfl
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring

end Riesz2.InterpolantLocalLaws
