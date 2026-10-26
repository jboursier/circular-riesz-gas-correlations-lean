/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.InterpolantLocalLawsPart5
public import Riesz2.Thermodynamic.InterpolatingDensitiesPart2
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Separating the internal and exterior particle forces

Exact physical rank decompositions for Appendix C. All separations are the cyclic gap
sums on the positive mass simplex.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ContDiff

namespace Riesz2.InterpolantLocalLaws

/-- A nonwrapping interval uses the ordinary physical gap labels.
This includes empty intervals and intervals ending at the last gap, as needed
in Appendix C. -/
theorem cyclicGapSum_nonwrapping (N : ℕ+) (i : Fin (N : ℕ)) (r : ℕ)
    (hir : i.val + r ≤ (N : ℕ)) (x : Fin (N : ℕ) → ℝ) :
    cyclicGapSum N i r x =
      ∑ a : Fin r, x ⟨i.val + a.val, by have := a.isLt; omega⟩ := by
  rw [cyclicGapSum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  apply Fin.ext
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega)

/-- Common active coordinates give literally equal internal separations
in two different physical volumes (Appendix C). -/
theorem cyclicGapSum_common_active (N M : ℕ+) {n i r : ℕ}
    (hnN : n ≤ (N : ℕ)) (hnM : n ≤ (M : ℕ)) (hi : i < n)
    (hir : i + r ≤ n) (x : Fin (N : ℕ) → ℝ) (y : Fin (M : ℕ) → ℝ)
    (hxy : ∀ k : Fin n,
      x ⟨k.val, by have := k.isLt; omega⟩ =
        y ⟨k.val, by have := k.isLt; omega⟩) :
    cyclicGapSum N ⟨i, by omega⟩ r x =
      cyclicGapSum M ⟨i, by omega⟩ r y := by
  rw [cyclicGapSum_nonwrapping N _ r (by simpa using hir.trans hnN),
    cyclicGapSum_nonwrapping M _ r (by simpa using hir.trans hnM)]
  apply Finset.sum_congr rfl
  intro a _
  exact hxy ⟨i + a.val, by have := a.isLt; omega⟩

/-- Complementing a wrapped interval based at particle `i` gives the
ordinary interval from particle `k` to `i`. This fixes the sign and the
rank-zero boundary particle in Appendix C. -/
theorem wrapped_intervalForce (p : Parameters) (N : ℕ+)
    (x : Fin (N : ℕ) → ℝ) (hx : x ∈ Riesz1.gapSimplex N)
    (i k : ℕ) (hi : i < (N : ℕ)) (hk : k < i) :
    intervalForce p N
      ⟨cyclicGapSum N ⟨i, hi⟩ ((N : ℕ) - i + k) x,
        PhysicalEnergy.gapSum_mem N _ (by omega) (by omega) x hx⟩ =
      -intervalForce p N
        ⟨cyclicGapSum N ⟨k, by omega⟩ (i - k) x,
          PhysicalEnergy.gapSum_mem N _ (by omega) (by omega) x hx⟩ := by
  have h := physical_intervalForce_complement p N x hx ⟨k, by omega⟩
    (r := i - k) (by omega) (by omega)
  have hind : (⟨k, by omega⟩ : Fin (N : ℕ)) +
      (i - k) • (1 : Fin (N : ℕ)) = ⟨i, hi⟩ := by
    have hn (a : ℕ) : a • (1 : Fin (N : ℕ)) =
        ⟨a % (N : ℕ), Nat.mod_lt _ N.pos⟩ := by
      induction a with
      | zero => rfl
      | succ a ih =>
        rw [succ_nsmul, ih]
        apply Fin.ext
        exact (Nat.add_mod _ _ _).symm
    rw [hn]
    apply Fin.ext
    change (k + (i - k) % (N : ℕ)) % (N : ℕ) = i
    rw [Nat.mod_eq_of_lt (show i - k < (N : ℕ) by omega), Nat.add_sub_of_le hk.le,
      Nat.mod_eq_of_lt hi]
  rw [hind] at h
  convert h using 1
  congr 2
  congr 1
  omega

/-- See Appendix C in the paper: the full forward force sum
splits into the common particles on the right (including particle `n`),
the strict exterior particles, and the common particles on the left
(including particle zero). No singular term has yet been estimated. -/
theorem physical_forward_force_split (p : Parameters) (N : ℕ+)
    (x : Fin (N : ℕ) → ℝ) (hx : x ∈ Riesz1.gapSimplex N)
    (n i : ℕ) (hi : 0 < i) (hin : i < n) (hn : n < (N : ℕ)) :
    (∑ r : Fin ((N : ℕ) - 1), intervalForce p N
      ⟨cyclicGapSum N ⟨i, by omega⟩ (r.val + 1) x,
        PhysicalEnergy.gapSum_mem N _ (by omega) (by have := r.isLt; omega) x hx⟩) =
    (∑ r : Fin (n - i), intervalForce p N
      ⟨cyclicGapSum N ⟨i, by omega⟩ (r.val + 1) x,
        PhysicalEnergy.gapSum_mem N _ (by omega) (by have := r.isLt; omega) x hx⟩) +
    (∑ r : Fin ((N : ℕ) - n - 1), intervalForce p N
      ⟨cyclicGapSum N ⟨i, by omega⟩ (n - i + r.val + 1) x,
        PhysicalEnergy.gapSum_mem N _ (by omega) (by have := r.isLt; omega) x hx⟩) -
    ∑ k : Fin i, intervalForce p N
      ⟨cyclicGapSum N ⟨k.val, by have := k.isLt; omega⟩ (i - k.val) x,
        PhysicalEnergy.gapSum_mem N _ (by have := k.isLt; omega) (by omega) x hx⟩ := by
  let F (r : Fin ((N : ℕ) - 1)) := intervalForce p N
    ⟨cyclicGapSum N ⟨i, by omega⟩ (r.val + 1) x,
      PhysicalEnergy.gapSum_mem N _ (by omega) (by have := r.isLt; omega) x hx⟩
  have he : (n - i) + ((N : ℕ) - n - 1) + i = (N : ℕ) - 1 := by omega
  have hsum := (Equiv.sum_comp (finCongr he) F).symm
  rw [Fin.sum_univ_add, Fin.sum_univ_add] at hsum
  change (∑ r, F r) = _
  rw [hsum]
  simp only [finCongr_apply, Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd, F]
  have hlast : (∑ k : Fin i, intervalForce p N
      ⟨cyclicGapSum N ⟨i, by omega⟩
        ((n - i + ((N : ℕ) - n - 1) + k.val) + 1) x,
        PhysicalEnergy.gapSum_mem N _ (by omega) (by have := k.isLt; omega) x hx⟩) =
      -(∑ k : Fin i, intervalForce p N
        ⟨cyclicGapSum N ⟨k.val, by have := k.isLt; omega⟩ (i - k.val) x,
          PhysicalEnergy.gapSum_mem N _ (by have := k.isLt; omega) (by omega) x hx⟩) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    convert wrapped_intervalForce p N x hx i k.val (by omega) k.isLt using 1
    congr 2
    congr 1
    omega
  rw [hlast]
  ring

/-- The retained coordinates of the exterior chart are exactly the
physical exterior gaps (Subsection 6.1). This complements its active-coordinate
bridge, without introducing another concatenation map. -/
theorem assemble_exterior_retained (e a : ℕ)
    (y : EuclideanSpace ℝ (Fin e)) (u : EuclideanSpace ℝ (Fin (a + 1)))
    (k : Fin e) :
    RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y u
      ⟨a + 1 + k.val, by have := k.isLt; omega⟩ = y k := by
  rw [← InterpolatingDensities.exteriorPermutation_retained e a k]
  change RetainedSimplex.join e (a + 1) (y, u)
    ((InterpolatingDensities.exteriorPermutation e a).symm
      (InterpolatingDensities.exteriorPermutation e a (k.castAdd a).castSucc)) = _
  rw [Equiv.symm_apply_apply]
  exact RetainedSimplex.join_left e (a + 1) y u k

/-- Internal distances in the actual fixed-exterior chart depend only on
the common active vector, including both fixed boundary particles.
See Appendix C in the paper. -/
theorem cyclicGapSum_assembled_active (e a i r : ℕ) (hi : i < a + 1)
    (hir : i + r ≤ a + 1) (y : EuclideanSpace ℝ (Fin e))
    (u : EuclideanSpace ℝ (Fin (a + 1))) :
    cyclicGapSum (e + a).succPNat ⟨i, by change i < e + a + 1; omega⟩ r
      (WithLp.ofLp (RetainedSimplex.assemble e a
        (InterpolatingDensities.exteriorPermutation e a) y u)) =
      ∑ k : Fin r, u ⟨i + k.val, by have := k.isLt; omega⟩ := by
  rw [cyclicGapSum_nonwrapping _ _ r (by simpa using (show i + r ≤ e + a + 1 by omega))]
  apply Finset.sum_congr rfl
  intro k _
  exact InterpolatingDensities.assemble_exterior_active e a y u
    ⟨i + k.val, by have := k.isLt; omega⟩ (by omega)

/-- The right exterior prefix in the assembled configuration is literally
the prefix of the fixed exterior in Subsection 6.1. It includes the empty and
full exterior prefixes, and imposes no typicality hypothesis. -/
theorem cyclicGapSum_assembled_exterior_prefix (e a r : ℕ) (he : 0 < e)
    (hr : r ≤ e) (y : EuclideanSpace ℝ (Fin e))
    (u : EuclideanSpace ℝ (Fin (a + 1))) :
    cyclicGapSum (e + a).succPNat ⟨a + 1, by change a + 1 < e + a + 1; omega⟩ r
      (WithLp.ofLp (RetainedSimplex.assemble e a
        (InterpolatingDensities.exteriorPermutation e a) y u)) =
      ∑ k : Fin r, y ⟨k.val, by have := k.isLt; omega⟩ := by
  rw [cyclicGapSum_nonwrapping _ _ r (by simpa using (show a + 1 + r ≤ e + a + 1 by omega))]
  apply Finset.sum_congr rfl
  intro k _
  exact assemble_exterior_retained e a y u ⟨k.val, by have := k.isLt; omega⟩

/-- Exact distance from an active particle to a right exterior rank in
the actual physical assembly. The two terms are its active suffix and the
exterior prefix. This is the rank matching interface used in the proof of
Appendix C. -/
theorem cyclicGapSum_assembled_to_exterior (e a i r : ℕ) (he : 0 < e)
    (hi : i < a + 1) (hr : r ≤ e) (y : EuclideanSpace ℝ (Fin e))
    (u : EuclideanSpace ℝ (Fin (a + 1))) :
    cyclicGapSum (e + a).succPNat ⟨i, by change i < e + a + 1; omega⟩ (a + 1 - i + r)
      (WithLp.ofLp (RetainedSimplex.assemble e a
        (InterpolatingDensities.exteriorPermutation e a) y u)) =
      (∑ k : Fin (a + 1 - i), u ⟨i + k.val, by have := k.isLt; omega⟩) +
        ∑ k : Fin r, y ⟨k.val, by have := k.isLt; omega⟩ := by
  let N := (e + a).succPNat
  have hind : (⟨i, by dsimp [N]; omega⟩ : Fin (N : ℕ)) +
      (a + 1 - i) • (1 : Fin (N : ℕ)) = ⟨a + 1, by dsimp [N]; omega⟩ := by
    have hn (b : ℕ) : b • (1 : Fin (N : ℕ)) =
        ⟨b % (N : ℕ), Nat.mod_lt _ N.pos⟩ := by
      induction b with
      | zero => rfl
      | succ b ih =>
        rw [succ_nsmul, ih]
        apply Fin.ext
        exact (Nat.add_mod _ _ _).symm
    rw [hn]
    apply Fin.ext
    change (i + (a + 1 - i) % (N : ℕ)) % (N : ℕ) = a + 1
    rw [Nat.mod_eq_of_lt (show a + 1 - i < (N : ℕ) by dsimp [N]; omega),
      Nat.add_sub_of_le hi.le,
      Nat.mod_eq_of_lt (show a + 1 < (N : ℕ) by dsimp [N]; omega)]
  rw [cyclicGapSum_split, hind,
    cyclicGapSum_assembled_active e a i (a + 1 - i) hi (by omega),
    cyclicGapSum_assembled_exterior_prefix e a r he hr]

/-- Every nonwrapping internal interval is bounded by the total active
mass. This applies to the actual common particles in the force split. -/
theorem cyclicGapSum_le_active_mass (N : ℕ+) {n i r : ℕ}
    (hn : n ≤ (N : ℕ)) (hi : i < n) (hir : i + r ≤ n)
    (x : Fin (N : ℕ) → ℝ) (hx : ∀ k, 0 ≤ x k) :
    cyclicGapSum N ⟨i, by omega⟩ r x ≤
      ∑ k : Fin n, x ⟨k.val, by have := k.isLt; omega⟩ := by
  rw [cyclicGapSum_nonwrapping _ _ r (by simpa using hir.trans hn)]
  apply Finset.sum_le_sum_of_injOn
    (fun k : Fin r => (⟨i + k.val, by have := k.isLt; omega⟩ : Fin n))
    (by
      intro k _ l _ hkl
      apply Fin.ext
      have := congrArg Fin.val hkl
      dsimp only at this
      omega)
    (by intro k _; exact Finset.mem_univ _)
    (by intro k _; exact le_rfl)
  intro k _ _
  exact hx _

/-- The geometric length condition alone puts every common internal
separation below half the smaller period. Appendix C. This also holds at bounded sizes. -/
theorem internal_half_period_of_length {L γ : ℝ} (n N : ℕ+)
    (hγ : γ ≤ 1) (hN : 4 * (n : ℕ) ≤ (N : ℕ))
    (hL : |L - (n : ℝ)| ≤ (n : ℝ) ^ γ) : L ≤ (N : ℝ) / 2 := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hp : (n : ℝ) ^ γ ≤ (n : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hn hγ
  have hNr : 4 * (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hh := (abs_le.mp hL).2
  linarith

/-- Internal helper for Appendix C: cancel
the singular force of an actual common active pair in different volumes.
Its error is uniform in all active gaps, with no lower cutoff. -/
theorem internal_common_pair_force_error (p : Parameters) (N M : ℕ+)
    (hNM : (N : ℕ) ≤ (M : ℕ)) {n i r : ℕ}
    (hn : n ≤ (N : ℕ)) (hi : i < n) (hr : 0 < r) (hir : i + r ≤ n)
    (x : Fin (N : ℕ) → ℝ) (hx : x ∈ Riesz1.gapSimplex N)
    (y : Fin (M : ℕ) → ℝ) (hy : y ∈ Riesz1.gapSimplex M)
    (hxy : ∀ k : Fin n,
      x ⟨k.val, by have := k.isLt; omega⟩ =
        y ⟨k.val, by have := k.isLt; omega⟩)
    (hmass : (∑ k : Fin n, x ⟨k.val, by have := k.isLt; omega⟩) ≤ (N : ℝ) / 2)
    (hrN : r < (N : ℕ)) :
    |intervalForce p N
        ⟨cyclicGapSum N ⟨i, by omega⟩ r x,
          PhysicalEnergy.gapSum_mem N _ hr hrN x hx⟩ -
      intervalForce p M
        ⟨cyclicGapSum M ⟨i, by omega⟩ r y,
          PhysicalEnergy.gapSum_mem M _ hr (by omega) y hy⟩| ≤
      2 * p.val.2 * ((N : ℝ) / 2) ^ (-p.val.2 - 1) *
        ∑' k : ℤ, |(k : ℝ)| ^ (-p.val.2 - 1) := by
  have he := cyclicGapSum_common_active N M hn (hn.trans hNM) hi hir x y hxy
  have hhalf := (cyclicGapSum_le_active_mass N hn hi hir x
    (fun k => (hx.1 k).le)).trans hmass
  have hb := internal_intervalForce_difference p N M hNM
    ⟨cyclicGapSum N ⟨i, by omega⟩ r x,
      PhysicalEnergy.gapSum_mem N _ hr hrN x hx⟩ hhalf
  convert hb using 1
  congr 2
  congr 1
  exact Subtype.ext he.symm

/-- Internal helper for Appendix C: summing
the actual common-pair errors costs only the number of pairs. The signs
can be those of either side of the pinned particle. No force estimate is
assumed as an input. -/
theorem internal_common_force_sum_error {ι : Type*} [Fintype ι]
    (p : Parameters) (N M : ℕ+) (hNM : (N : ℕ) ≤ (M : ℕ)) {n : ℕ}
    (hn : n ≤ (N : ℕ)) (a r : ι → ℕ) (ha : ∀ k, a k < n)
    (hr : ∀ k, 0 < r k) (har : ∀ k, a k + r k ≤ n)
    (hrN : ∀ k, r k < (N : ℕ))
    (x : Fin (N : ℕ) → ℝ) (hx : x ∈ Riesz1.gapSimplex N)
    (y : Fin (M : ℕ) → ℝ) (hy : y ∈ Riesz1.gapSimplex M)
    (hxy : ∀ k : Fin n,
      x ⟨k.val, by have := k.isLt; omega⟩ =
        y ⟨k.val, by have := k.isLt; omega⟩)
    (hmass : (∑ k : Fin n, x ⟨k.val, by have := k.isLt; omega⟩) ≤ (N : ℝ) / 2)
    (w : ι → ℝ) (hw : ∀ k, |w k| ≤ 1) :
    |∑ k, w k * (intervalForce p N
        ⟨cyclicGapSum N ⟨a k, by have := ha k; omega⟩ (r k) x,
          PhysicalEnergy.gapSum_mem N _ (hr k) (hrN k) x hx⟩ -
      intervalForce p M
        ⟨cyclicGapSum M ⟨a k, by have := ha k; omega⟩ (r k) y,
          PhysicalEnergy.gapSum_mem M _ (hr k) (by have := hrN k; omega) y hy⟩)| ≤
      Fintype.card ι * (2 * p.val.2 * ((N : ℝ) / 2) ^ (-p.val.2 - 1) *
        ∑' k : ℤ, |(k : ℝ)| ^ (-p.val.2 - 1)) := by
  calc
    _ ≤ ∑ k, |w k * (intervalForce p N
        ⟨cyclicGapSum N ⟨a k, by have := ha k; omega⟩ (r k) x,
          PhysicalEnergy.gapSum_mem N _ (hr k) (hrN k) x hx⟩ -
      intervalForce p M
        ⟨cyclicGapSum M ⟨a k, by have := ha k; omega⟩ (r k) y,
          PhysicalEnergy.gapSum_mem M _ (hr k) (by have := hrN k; omega) y hy⟩)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : ι, (2 * p.val.2 * ((N : ℝ) / 2) ^ (-p.val.2 - 1) *
        ∑' k : ℤ, |(k : ℝ)| ^ (-p.val.2 - 1)) := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (hw k)).trans
        (internal_common_pair_force_error p N M hNM hn (ha k) (hr k) (har k)
          x hx y hy hxy hmass (hrN k))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- See Appendix C in the paper: the smooth realization of
the physical energy has precisely the internal/exterior rank split
above. The two fixed boundary particles belong to the internal sums. -/
theorem physical_pinned_force_decomposition (p : Parameters) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ∀ (x : Fin (N : ℕ) → ℝ) (hx : x ∈ Riesz1.gapSimplex N)
        (n i : ℕ) (hi : 0 < i) (hin : i < n) (hn : n < (N : ℕ)),
        fderiv ℝ W (WithLp.toLp 2 x)
          (WithLp.toLp 2 (Pi.single ⟨i - 1, by omega⟩ 1 -
            Pi.single ⟨i, by omega⟩ 1)) =
        -2 * ((∑ r : Fin (n - i), intervalForce p N
          ⟨cyclicGapSum N ⟨i, by omega⟩ (r.val + 1) x,
            PhysicalEnergy.gapSum_mem N _ (by omega) (by have := r.isLt; omega) x hx⟩) +
        (∑ r : Fin ((N : ℕ) - n - 1), intervalForce p N
          ⟨cyclicGapSum N ⟨i, by omega⟩ (n - i + r.val + 1) x,
            PhysicalEnergy.gapSum_mem N _ (by omega) (by have := r.isLt; omega) x hx⟩) -
        ∑ k : Fin i, intervalForce p N
          ⟨cyclicGapSum N ⟨k.val, by have := k.isLt; omega⟩ (i - k.val) x,
            PhysicalEnergy.gapSum_mem N _ (by have := k.isLt; omega) (by omega) x hx⟩) := by
  obtain ⟨W, hW, hv, hd⟩ := physical_pinned_pair_force p N hN
  refine ⟨W, hW, hv, ?_⟩
  intro x hx n i hi hin hn
  have hind : (⟨i - 1, by omega⟩ : Fin (N : ℕ)) + 1 = ⟨i, by omega⟩ := by
    apply Fin.ext
    change (i - 1 + 1 % (N : ℕ)) % (N : ℕ) = i
    rw [Nat.mod_eq_of_lt (by omega : 1 < (N : ℕ))]
    rw [Nat.sub_add_cancel hi, Nat.mod_eq_of_lt (by omega)]
  have hh := hd x hx ⟨i - 1, by omega⟩
  dsimp only at hh
  rw [hind] at hh
  rw [hh, physical_forward_force_split p N x hx n i hi hin hn]

/-- See Appendix C in the paper: the actual exterior
prefixes in two admissible geometries have the required rank mismatch.
This concerns rank locations, before applying the inverse-power force. -/
theorem internal_rank_location_difference {A γ r Y Z : ℝ}
    (hY : |Y - r| ≤ 4 * A * r ^ γ)
    (hZ : |Z - r| ≤ 4 * A * r ^ γ) :
    |Y - Z| ≤ 8 * A * r ^ γ := by
  calc
    |Y - Z| = |(Y - r) - (Z - r)| := by congr 1; ring
    _ ≤ |Y - r| + |Z - r| := abs_sub _ _
    _ ≤ 4 * A * r ^ γ + 4 * A * r ^ γ := add_le_add hY hZ
    _ = _ := by ring

/-- Internal mean-value estimate for a matched exterior rank in Appendix C. The constant depends only on `s`, and the
positive boundary distance `a` need not be at least one. -/
theorem internal_paired_principal_force {s a r Y Z : ℝ} (hs : 0 < s)
    (ha : 0 < a) (hr : 0 ≤ r) (hY : r / 2 ≤ Y) (hZ : r / 2 ≤ Z) :
    |(-s * (a + Y) ^ (-s - 1)) - (-s * (a + Z) ^ (-s - 1))| ≤
      s * (s + 1) * 2 ^ (s + 2) * (a + r) ^ (-s - 2) * |Y - Z| := by
  let δ := (a + r) / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hd (t : ℝ) (ht : t ∈ Set.Ici δ) :
      DifferentiableAt ℝ (fun t : ℝ => t ^ (-s - 1)) t :=
    (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (hδ.trans_le ht)))).differentiableAt
  have hb (t : ℝ) (ht : t ∈ Set.Ici δ) :
      ‖deriv (fun t : ℝ => t ^ (-s - 1)) t‖ ≤ (s + 1) * δ ^ (-s - 2) := by
    rw [Real.deriv_rpow_const, norm_mul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hδ.trans_le ht).le _)]
    have habs : |-s - 1| = s + 1 := by rw [abs_of_neg (by linarith)]; ring
    rw [habs, show -s - 1 - 1 = -s - 2 by ring]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hδ ht (by linarith)) (by linarith)
  have hAY : a + Y ∈ Set.Ici δ := by change δ ≤ a + Y; dsimp [δ]; linarith
  have hAZ : a + Z ∈ Set.Ici δ := by change δ ≤ a + Z; dsimp [δ]; linarith
  have hm := (convex_Ici δ).norm_image_sub_le_of_norm_deriv_le hd hb hAZ hAY
  simp only [Real.norm_eq_abs, show a + Y - (a + Z) = Y - Z by ring] at hm
  have he : δ ^ (-s - 2) = 2 ^ (s + 2) * (a + r) ^ (-s - 2) := by
    dsimp only [δ]
    rw [div_eq_mul_inv, Real.mul_rpow (by positivity : 0 ≤ a + r) (by norm_num),
      Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num),
      show -(-s - 2) = s + 2 by ring, mul_comm]
  rw [he] at hm
  calc
    _ = s * |(a + Y) ^ (-s - 1) - (a + Z) ^ (-s - 1)| := by
      rw [← mul_sub, abs_mul, abs_neg, abs_of_pos hs]
    _ ≤ s * ((s + 1) * (2 ^ (s + 2) * (a + r) ^ (-s - 2)) * |Y - Z|) :=
      mul_le_mul_of_nonneg_left hm hs.le
    _ = _ := by ring

/-- The weighted rank sum in Appendix C.
The bound is uniform for `0 ≤ γ ≤ 1` and for every positive boundary
distance, including distances below one. All sums here are finite. -/
theorem internal_weighted_rank_sum {s γ a : ℝ} (hs : 0 < s)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (ha : 0 < a) (M : ℕ) :
    (∑ r : Fin M, (r.val + 1 : ℝ) ^ γ *
      (a + (r.val + 1 : ℝ)) ^ (-s - 2)) ≤ a ^ (γ - s - 1) / s := by
  let q := γ - s - 2
  have hq : q < -1 := by dsimp [q]; linarith
  have hq1 : q + 1 < 0 := by linarith
  have hAM : a ≤ a + (M : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hanti : AntitoneOn (fun t : ℝ => t ^ q) (Set.Icc a (a + (M : ℝ))) := by
    intro t ht u _ htu
    exact Real.rpow_le_rpow_of_nonpos (ha.trans_le ht.1) htu (by linarith)
  have hsum := hanti.sum_le_integral
  have hint : (∫ t in a..a + (M : ℝ), t ^ q) ≤ a ^ (q + 1) / (-(q + 1)) := by
    rw [integral_rpow (Or.inr ⟨by linarith, by
      rw [Set.uIcc_of_le hAM]
      intro h
      exact (not_le_of_gt ha) h.1⟩)]
    have hb : 0 ≤ (a + (M : ℝ)) ^ (q + 1) := Real.rpow_nonneg (by positivity) _
    rw [div_neg]
    apply (div_le_iff_of_neg hq1).mpr
    rw [neg_mul, div_mul_cancel₀ _ (ne_of_lt hq1)]
    linarith
  calc
    _ ≤ ∑ r : Fin M, (a + (r.val + 1 : ℝ)) ^ q := by
      apply Finset.sum_le_sum
      intro r _
      have hbase : (0 : ℝ) < (r.val + 1 : ℝ) := by positivity
      have hp := Real.rpow_le_rpow hbase.le
        (show (r.val + 1 : ℝ) ≤ a + (r.val + 1 : ℝ) by linarith) hγ
      apply (mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg (by positivity) _)).trans_eq
      rw [← Real.rpow_add (by positivity : 0 < a + (r.val + 1 : ℝ))]
      congr 1
      dsimp [q]
      ring
    _ = ∑ r ∈ Finset.range M, (a + ((r + 1 : ℕ) : ℝ)) ^ q := by
      rw [← Fin.sum_univ_eq_sum_range]
      simp only [Nat.cast_add, Nat.cast_one]
    _ ≤ ∫ t in a..a + (M : ℝ), t ^ q := hsum
    _ ≤ a ^ (q + 1) / (-(q + 1)) := hint
    _ ≤ a ^ (q + 1) / s := by
      apply div_le_div_of_nonneg_left (Real.rpow_nonneg ha.le _) hs
      dsimp [q]
      linarith
    _ = _ := by congr 2; dsimp [q]; ring

/-- Removing both nearest images leaves an error uniform on the entire
physical period. This lets Appendix C treat the two
exterior boundaries symmetrically, even when a particle approaches one
of them. -/
theorem intervalForce_two_boundary_error (p : Parameters) (N : ℕ+)
    (L : {L : ℝ // 0 < L ∧ L < (N : ℝ)}) :
    |intervalForce p N L + p.val.2 * L.val ^ (-p.val.2 - 1) -
      p.val.2 * ((N : ℝ) - L.val) ^ (-p.val.2 - 1)| ≤
      p.val.2 * ((N : ℝ) / 2) ^ (-p.val.2 - 1) *
        (1 + ∑' k : ℤ, |(k : ℝ)| ^ (-p.val.2 - 1)) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hshort (K : {L : ℝ // 0 < L ∧ L < (N : ℝ)})
      (hK : K.val ≤ (N : ℝ) / 2) :
      |intervalForce p N K + p.val.2 * K.val ^ (-p.val.2 - 1) -
        p.val.2 * ((N : ℝ) - K.val) ^ (-p.val.2 - 1)| ≤
        p.val.2 * ((N : ℝ) / 2) ^ (-p.val.2 - 1) *
          (1 + ∑' k : ℤ, |(k : ℝ)| ^ (-p.val.2 - 1)) := by
    have hp := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (N : ℝ) / 2)
      (show (N : ℝ) / 2 ≤ (N : ℝ) - K.val by linarith)
      (show -p.val.2 - 1 ≤ 0 by linarith [p.property.2.1])
    calc
      _ ≤ |intervalForce p N K + p.val.2 * K.val ^ (-p.val.2 - 1)| +
          |p.val.2 * ((N : ℝ) - K.val) ^ (-p.val.2 - 1)| := abs_sub _ _
      _ ≤ p.val.2 * ((N : ℝ) / 2) ^ (-p.val.2 - 1) *
          (∑' k : ℤ, |(k : ℝ)| ^ (-p.val.2 - 1)) +
          p.val.2 * ((N : ℝ) / 2) ^ (-p.val.2 - 1) := by
        apply add_le_add (intervalForce_period_correction p N K hK)
        rw [abs_of_nonneg (mul_nonneg p.property.2.1.le
          (Real.rpow_nonneg (by linarith [K.property.2] : 0 ≤ (N : ℝ) - K.val) _))]
        exact mul_le_mul_of_nonneg_left hp p.property.2.1.le
      _ = _ := by ring
  by_cases hL : L.val ≤ (N : ℝ) / 2
  · exact hshort L hL
  · let K : {L : ℝ // 0 < L ∧ L < (N : ℝ)} :=
      ⟨(N : ℝ) - L.val, by linarith [L.property.2], by linarith [L.property.1]⟩
    have hh := hshort K (by dsimp [K]; linarith)
    have hf := intervalForce_complement p N L
    have he : intervalForce p N L + p.val.2 * L.val ^ (-p.val.2 - 1) -
        p.val.2 * ((N : ℝ) - L.val) ^ (-p.val.2 - 1) =
        -(intervalForce p N K + p.val.2 * K.val ^ (-p.val.2 - 1) -
          p.val.2 * ((N : ℝ) - K.val) ^ (-p.val.2 - 1)) := by
      change intervalForce p N K = -intervalForce p N L at hf
      rw [hf]
      dsimp only [K]
      rw [sub_sub_cancel]
      ring
    rw [he, abs_neg]
    exact hh

/-- At the threshold prescribed in Appendix C, the
geometric rank error is at most one quarter of the rank itself. -/
theorem internal_large_rank_geometry {A γ r Y : ℝ} (hA : 0 < A)
    (hγ : γ < 1) (hr : (16 * A) ^ (1 / (1 - γ)) ≤ r)
    (hY : |Y - r| ≤ 4 * A * r ^ γ) :
    4 * A * r ^ γ ≤ r / 4 ∧ r / 2 ≤ Y := by
  have hT : 0 < (16 * A) ^ (1 / (1 - γ)) := Real.rpow_pos_of_pos (by positivity) _
  have hr0 : 0 < r := hT.trans_le hr
  have hpow := Real.rpow_le_rpow hT.le hr (sub_pos.mpr hγ).le
  rw [← Real.rpow_mul (by positivity : 0 ≤ 16 * A),
    one_div_mul_cancel (sub_ne_zero.mpr (ne_of_gt hγ)), Real.rpow_one] at hpow
  have hh := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hr0.le γ)
  have he : r ^ (1 - γ) * r ^ γ = r := by
    rw [← Real.rpow_add hr0, sub_add_cancel, Real.rpow_one]
  rw [he] at hh
  have hlow := (abs_le.mp hY).1
  constructor <;> nlinarith

/-- Internal comparison of the principal forces at every common exterior
rank. This proves both the small-rank and paired-rank contributions in
Appendix C, uniformly in the number of ranks
and for every positive distance from the active boundary. -/
theorem internal_principal_exterior_comparison {s γ A a : ℝ} (hs : 0 < s)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hA : 1 ≤ A) (ha : 0 < a)
    (M : ℕ) (Y Z : Fin M → ℝ) (hY0 : ∀ r, 0 ≤ Y r) (hZ0 : ∀ r, 0 ≤ Z r)
    (hY : ∀ r, |Y r - (r.val + 1 : ℝ)| ≤ 4 * A * (r.val + 1 : ℝ) ^ γ)
    (hZ : ∀ r, |Z r - (r.val + 1 : ℝ)| ≤ 4 * A * (r.val + 1 : ℝ) ^ γ) :
    let T := (16 * A) ^ (1 / (1 - γ))
    |∑ r, ((-s * (a + Y r) ^ (-s - 1)) - (-s * (a + Z r) ^ (-s - 1)))| ≤
      4 * s * T * a ^ (-s - 1) +
        8 * (s + 1) * 2 ^ (s + 2) * A * a ^ (γ - s - 1) := by
  classical
  dsimp only
  let T := (16 * A) ^ (1 / (1 - γ))
  let f := fun r : Fin M => (-s * (a + Y r) ^ (-s - 1)) -
    (-s * (a + Z r) ^ (-s - 1))
  let S := Finset.univ.filter (fun r : Fin M => (r.val + 1 : ℝ) < T)
  have hA0 : 0 < A := by linarith
  have hT : 1 ≤ T := Real.one_le_rpow (by nlinarith) (by positivity)
  have hTp : 0 < T := by linarith
  have hsmall (r : Fin M) : |f r| ≤ 2 * s * a ^ (-s - 1) := by
    have hpowY := Real.rpow_le_rpow_of_nonpos ha
      (show a ≤ a + Y r by linarith [hY0 r]) (by linarith : -s - 1 ≤ 0)
    have hpowZ := Real.rpow_le_rpow_of_nonpos ha
      (show a ≤ a + Z r by linarith [hZ0 r]) (by linarith : -s - 1 ≤ 0)
    calc
      _ ≤ |-s * (a + Y r) ^ (-s - 1)| + |-s * (a + Z r) ^ (-s - 1)| := abs_sub _ _
      _ = s * (a + Y r) ^ (-s - 1) + s * (a + Z r) ^ (-s - 1) := by
        simp only [abs_mul, abs_neg, abs_of_pos hs,
          abs_of_nonneg (Real.rpow_nonneg (by linarith [hY0 r] : 0 ≤ a + Y r) _),
          abs_of_nonneg (Real.rpow_nonneg (by linarith [hZ0 r] : 0 ≤ a + Z r) _)]
      _ ≤ _ := by nlinarith
  have hshort : (∑ r ∈ S, |f r|) ≤ 4 * s * T * a ^ (-s - 1) := by
    have hi : Function.Injective (fun r : Fin M => r.val) := Fin.val_injective
    calc
      _ ≤ ∑ _ ∈ Finset.range ⌈T⌉₊, 2 * s * a ^ (-s - 1) := by
        apply Finset.sum_le_sum_of_injOn (fun r : Fin M => r.val)
          hi.injOn ?_ (fun r _ => hsmall r)
        · intro _ _ _
          positivity
        · intro r hr
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hr
          rw [Finset.mem_range]
          have hrt := (Finset.mem_filter.mp hk).2
          have hceil : T ≤ (⌈T⌉₊ : ℝ) := Nat.le_ceil T
          exact_mod_cast (show (k.val : ℝ) < ⌈T⌉₊ by linarith)
      _ = (⌈T⌉₊ : ℝ) * (2 * s * a ^ (-s - 1)) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ (2 * T) * (2 * s * a ^ (-s - 1)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hc := Nat.ceil_lt_add_one hTp.le
        linarith
      _ = _ := by ring
  let B := 8 * s * (s + 1) * 2 ^ (s + 2) * A
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hlarge (r : Fin M) (hr : r ∈ Finset.univ \ S) :
      |f r| ≤ B * ((r.val + 1 : ℝ) ^ γ * (a + (r.val + 1 : ℝ)) ^ (-s - 2)) := by
    have hrt : T ≤ (r.val + 1 : ℝ) := by
      simpa only [S, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter,
        true_and, not_lt] using hr
    have hlowY := (internal_large_rank_geometry hA0 hγ1 hrt (hY r)).2
    have hlowZ := (internal_large_rank_geometry hA0 hγ1 hrt (hZ r)).2
    have hdiff := internal_rank_location_difference (hY r) (hZ r)
    have hb := internal_paired_principal_force hs ha (by positivity) hlowY hlowZ
    calc
      |f r| ≤ s * (s + 1) * 2 ^ (s + 2) *
          (a + (r.val + 1 : ℝ)) ^ (-s - 2) * |Y r - Z r| := hb
      _ ≤ s * (s + 1) * 2 ^ (s + 2) *
          (a + (r.val + 1 : ℝ)) ^ (-s - 2) *
          (8 * A * (r.val + 1 : ℝ) ^ γ) := by
        exact mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ = _ := by dsimp [B]; ring
  have hlong : (∑ r ∈ Finset.univ \ S, |f r|) ≤
      8 * (s + 1) * 2 ^ (s + 2) * A * a ^ (γ - s - 1) := by
    calc
      _ ≤ ∑ r ∈ Finset.univ \ S,
          B * ((r.val + 1 : ℝ) ^ γ * (a + (r.val + 1 : ℝ)) ^ (-s - 2)) :=
        Finset.sum_le_sum hlarge
      _ ≤ ∑ r : Fin M,
          B * ((r.val + 1 : ℝ) ^ γ * (a + (r.val + 1 : ℝ)) ^ (-s - 2)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (by
          intro r hr
          exact (Finset.mem_sdiff.mp hr).1)
        intro r _ _
        positivity
      _ = B * ∑ r : Fin M,
          (r.val + 1 : ℝ) ^ γ * (a + (r.val + 1 : ℝ)) ^ (-s - 2) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ B * (a ^ (γ - s - 1) / s) :=
        mul_le_mul_of_nonneg_left (internal_weighted_rank_sum hs hγ hγ1.le ha M) hB
      _ = _ := by dsimp [B]; field_simp
  change |∑ r, f r| ≤ _
  calc
    _ ≤ ∑ r, |f r| := Finset.abs_sum_le_sum_abs _ _
    _ = (∑ r ∈ S, |f r|) + ∑ r ∈ Finset.univ \ S, |f r| :=
      (Finset.sum_add_sum_compl S (fun r => |f r|)).symm
    _ ≤ _ := add_le_add hshort hlong

/-- Unpaired exterior ranks have the period-scale tail in Appendix C. The endpoint `R` is real, so a half-period
or a rounded number of common ranks can be used without changing constants. -/
theorem internal_unpaired_principal_tail {s a R : ℝ} (hs : 0 < s)
    (ha : 0 ≤ a) (hR : 0 < R) (M : ℕ) (Y : Fin M → ℝ)
    (hY : ∀ r, (R + (r.val + 1 : ℝ)) / 2 ≤ Y r) :
    |∑ r, -s * (a + Y r) ^ (-s - 1)| ≤ 2 ^ (s + 1) * R ^ (-s) := by
  have hanti : AntitoneOn (fun t : ℝ => t ^ (-s - 1))
      (Set.Icc R (R + (M : ℝ))) := by
    intro t ht u _ htu
    exact Real.rpow_le_rpow_of_nonpos (hR.trans_le ht.1) htu (by linarith)
  have hint : (∫ t in R..R + (M : ℝ), t ^ (-s - 1)) ≤ R ^ (-s) / s := by
    rw [integral_rpow (Or.inr ⟨by linarith, by
      rw [Set.uIcc_of_le (le_add_of_nonneg_right (Nat.cast_nonneg _))]
      intro h
      exact (not_le_of_gt hR) h.1⟩),
      show -s - 1 + 1 = -s by ring]
    rw [div_neg]
    have hb := Real.rpow_nonneg (show 0 ≤ R + (M : ℝ) by positivity) (-s)
    apply (le_div_iff₀ hs).mpr
    rw [neg_mul, div_mul_cancel₀ _ hs.ne']
    linarith
  have hsum : (∑ r : Fin M, (R + (r.val + 1 : ℝ)) ^ (-s - 1)) ≤ R ^ (-s) / s := by
    apply le_trans _ hint
    convert hanti.sum_le_integral using 1
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [Nat.cast_add, Nat.cast_one]
  have hterm (r : Fin M) :
      |-s * (a + Y r) ^ (-s - 1)| ≤
        s * 2 ^ (s + 1) * (R + (r.val + 1 : ℝ)) ^ (-s - 1) := by
    have hbase : 0 < (R + (r.val + 1 : ℝ)) / 2 := by positivity
    have hp := Real.rpow_le_rpow_of_nonpos hbase
      (show (R + (r.val + 1 : ℝ)) / 2 ≤ a + Y r by linarith [hY r])
      (show -s - 1 ≤ 0 by linarith)
    have hscale : ((R + (r.val + 1 : ℝ)) / 2) ^ (-s - 1) =
        2 ^ (s + 1) * (R + (r.val + 1 : ℝ)) ^ (-s - 1) := by
      rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by norm_num),
        Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num),
        show -(-s - 1) = s + 1 by ring, mul_comm]
    rw [hscale] at hp
    rw [abs_mul, abs_neg, abs_of_pos hs,
      abs_of_nonneg (Real.rpow_nonneg (by linarith [hY r] : 0 ≤ a + Y r) _)]
    exact (mul_le_mul_of_nonneg_left hp hs.le).trans_eq (by ring)
  calc
    _ ≤ ∑ r, |-s * (a + Y r) ^ (-s - 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : Fin M,
        s * 2 ^ (s + 1) * (R + (r.val + 1 : ℝ)) ^ (-s - 1) :=
      Finset.sum_le_sum (fun r _ => hterm r)
    _ = (s * 2 ^ (s + 1)) *
        ∑ r : Fin M, (R + (r.val + 1 : ℝ)) ^ (-s - 1) := (Finset.mul_sum _ _ _).symm
    _ ≤ (s * 2 ^ (s + 1)) * (R ^ (-s) / s) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by field_simp

/-- The sum of all remaining images over the actual strict exterior
particles has the period-scale error required by
Appendix C. Both nearest boundary forces are retained,
and neither of their possible singularities is bounded separately. -/
theorem internal_exterior_image_sum_error (p : Parameters) (N : ℕ+)
    (x : Fin (N : ℕ) → ℝ) (hx : x ∈ Riesz1.gapSimplex N)
    (n i : ℕ) (hi : i < n) (hn : n < (N : ℕ)) :
    let d := fun r : Fin ((N : ℕ) - n - 1) =>
      (⟨cyclicGapSum N ⟨i, by omega⟩ (n - i + r.val + 1) x,
        PhysicalEnergy.gapSum_mem N _ (by omega) (by have := r.isLt; omega) x hx⟩ :
        {L : ℝ // 0 < L ∧ L < (N : ℝ)})
    |(∑ r, intervalForce p N (d r)) +
        p.val.2 * (∑ r, (d r).val ^ (-p.val.2 - 1)) -
        p.val.2 * (∑ r, ((N : ℝ) - (d r).val) ^ (-p.val.2 - 1))| ≤
      (p.val.2 * 2 ^ (p.val.2 + 1) *
        (1 + ∑' k : ℤ, |(k : ℝ)| ^ (-p.val.2 - 1))) * (N : ℝ) ^ (-p.val.2) := by
  dsimp only
  let d := fun r : Fin ((N : ℕ) - n - 1) =>
      (⟨cyclicGapSum N ⟨i, by omega⟩ (n - i + r.val + 1) x,
        PhysicalEnergy.gapSum_mem N _ (by omega) (by have := r.isLt; omega) x hx⟩ :
        {L : ℝ // 0 < L ∧ L < (N : ℝ)})
  let B := p.val.2 * ((N : ℝ) / 2) ^ (-p.val.2 - 1) *
    (1 + ∑' k : ℤ, |(k : ℝ)| ^ (-p.val.2 - 1))
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hB : 0 ≤ B := by
    dsimp only [B]
    apply mul_nonneg (mul_nonneg p.property.2.1.le (Real.rpow_nonneg (by positivity) _))
    have ht : 0 ≤ ∑' k : ℤ, |(k : ℝ)| ^ (-p.val.2 - 1) :=
      tsum_nonneg (fun _ => Real.rpow_nonneg (abs_nonneg _) _)
    linarith
  have herr : |∑ r, (intervalForce p N (d r) + p.val.2 * (d r).val ^ (-p.val.2 - 1) -
      p.val.2 * ((N : ℝ) - (d r).val) ^ (-p.val.2 - 1))| ≤ (N : ℝ) * B := by
    calc
      _ ≤ ∑ r, |intervalForce p N (d r) + p.val.2 * (d r).val ^ (-p.val.2 - 1) -
          p.val.2 * ((N : ℝ) - (d r).val) ^ (-p.val.2 - 1)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin ((N : ℕ) - n - 1), B :=
        Finset.sum_le_sum (fun r _ => intervalForce_two_boundary_error p N (d r))
      _ = (((N : ℕ) - n - 1 : ℕ) : ℝ) * B := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast (show (N : ℕ) - n - 1 ≤ N by omega)) hB
  have hscale : (N : ℝ) * ((N : ℝ) / 2) ^ (-p.val.2 - 1) =
      2 ^ (p.val.2 + 1) * (N : ℝ) ^ (-p.val.2) := by
    rw [div_eq_mul_inv, Real.mul_rpow hN.le (by norm_num),
      Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num),
      show -(-p.val.2 - 1) = p.val.2 + 1 by ring]
    calc
      _ = 2 ^ (p.val.2 + 1) * ((N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-p.val.2 - 1)) := by
        rw [Real.rpow_one]
        ring
      _ = _ := by rw [← Real.rpow_add hN, show 1 + (-p.val.2 - 1) = -p.val.2 by ring]
  change |(∑ r, intervalForce p N (d r)) +
      p.val.2 * (∑ r, (d r).val ^ (-p.val.2 - 1)) -
      p.val.2 * (∑ r, ((N : ℝ) - (d r).val) ^ (-p.val.2 - 1))| ≤ _
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply herr.trans_eq
  dsimp only [B]
  calc
    _ = p.val.2 * (1 + ∑' k : ℤ, |(k : ℝ)| ^ (-p.val.2 - 1)) *
        ((N : ℝ) * ((N : ℝ) / 2) ^ (-p.val.2 - 1)) := by ring
    _ = _ := by rw [hscale]; ring

/-- Internal comparison for different numbers of exterior ranks. The
common ranks use the paired estimate. The additional ranks contribute
only the power tail. This is the principal-force part of Appendix C, before its physical reindexing. -/
theorem internal_principal_exterior_different_lengths {s γ A a : ℝ} (hs : 0 < s)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hA : 1 ≤ A) (ha : 0 < a)
    (M K : ℕ) (hM : 0 < M) (hT : (16 * A) ^ (1 / (1 - γ)) ≤ (M : ℝ))
    (Y : Fin M → ℝ) (Z : Fin (M + K) → ℝ)
    (hY0 : ∀ r, 0 ≤ Y r) (hZ0 : ∀ r, 0 ≤ Z r)
    (hY : ∀ r, |Y r - (r.val + 1 : ℝ)| ≤ 4 * A * (r.val + 1 : ℝ) ^ γ)
    (hZ : ∀ r, |Z r - (r.val + 1 : ℝ)| ≤ 4 * A * (r.val + 1 : ℝ) ^ γ) :
    let T := (16 * A) ^ (1 / (1 - γ))
    |(∑ r, -s * (a + Y r) ^ (-s - 1)) -
      (∑ r, -s * (a + Z r) ^ (-s - 1))| ≤
      4 * s * T * a ^ (-s - 1) +
        8 * (s + 1) * 2 ^ (s + 2) * A * a ^ (γ - s - 1) +
        2 ^ (s + 1) * (M : ℝ) ^ (-s) := by
  dsimp only
  have hcommon := internal_principal_exterior_comparison hs hγ hγ1 hA ha M Y
    (fun r => Z (r.castAdd K)) hY0 (fun r => hZ0 (r.castAdd K)) hY
    (fun r => hZ (r.castAdd K))
  dsimp only at hcommon
  rw [Finset.sum_sub_distrib] at hcommon
  have htail := internal_unpaired_principal_tail hs ha.le
    (show (0 : ℝ) < M by exact_mod_cast hM) K (fun r => Z (r.natAdd M))
    (fun r => by
      have hrt : (16 * A) ^ (1 / (1 - γ)) ≤ ((r.natAdd M).val + 1 : ℝ) := by
        simp only [Fin.val_natAdd, Nat.cast_add]
        have hr : (0 : ℝ) ≤ r.val := Nat.cast_nonneg _
        linarith
      have hh := (internal_large_rank_geometry (by linarith : 0 < A)
        hγ1 hrt (hZ (r.natAdd M))).2
      simpa only [Fin.val_natAdd, Nat.cast_add, add_assoc] using hh)
  rw [Fin.sum_univ_add]
  calc
    _ = |((∑ r : Fin M, -s * (a + Y r) ^ (-s - 1)) -
        (∑ r : Fin M, -s * (a + Z (r.castAdd K)) ^ (-s - 1))) -
        (∑ r : Fin K, -s * (a + Z (r.natAdd M)) ^ (-s - 1))| := by
      congr 1
      ring
    _ ≤ |(∑ r : Fin M, -s * (a + Y r) ^ (-s - 1)) -
        (∑ r : Fin M, -s * (a + Z (r.castAdd K)) ^ (-s - 1))| +
        |∑ r : Fin K, -s * (a + Z (r.natAdd M)) ^ (-s - 1)| := abs_sub _ _
    _ ≤ _ := add_le_add hcommon htail

/-- A split at an ordinary physical label has no modular ambiguity.
Used to identify both boundary distances in Appendix C. -/
theorem cyclicGapSum_split_nonwrapping (N : ℕ+) (i r t : ℕ)
    (hir : i + r < (N : ℕ)) (x : Fin (N : ℕ) → ℝ) :
    cyclicGapSum N ⟨i, by omega⟩ (r + t) x =
      cyclicGapSum N ⟨i, by omega⟩ r x +
        cyclicGapSum N ⟨i + r, hir⟩ t x := by
  rw [cyclicGapSum_split]
  congr 2
  have hn (b : ℕ) : b • (1 : Fin (N : ℕ)) =
      ⟨b % (N : ℕ), Nat.mod_lt _ N.pos⟩ := by
    induction b with
    | zero => rfl
    | succ b ih =>
      rw [succ_nsmul, ih]
      apply Fin.ext
      exact (Nat.add_mod _ _ _).symm
  rw [hn]
  apply Fin.ext
  change (i + r % (N : ℕ)) % (N : ℕ) = i + r
  rw [Nat.mod_eq_of_lt (show r < (N : ℕ) by omega), Nat.mod_eq_of_lt hir]

/-- The complement of a nonwrapping separation consists of its left
prefix and right suffix, with the physical total mass retained. -/
theorem cyclicGapSum_linear_complement (N : ℕ+)
    (x : Fin (N : ℕ) → ℝ) (hmass : ∑ k, x k = (N : ℝ))
    (i r : ℕ) (hir : i + r < (N : ℕ)) :
    (N : ℝ) - cyclicGapSum N ⟨i, by omega⟩ r x =
      cyclicGapSum N 0 i x +
        cyclicGapSum N ⟨i + r, hir⟩ ((N : ℕ) - i - r) x := by
  have h1 := cyclicGapSum_split_nonwrapping N 0 i ((N : ℕ) - i)
    (by simpa using (show i < (N : ℕ) by omega)) x
  have h2 := cyclicGapSum_split_nonwrapping N i r ((N : ℕ) - i - r) hir x
  rw [Nat.add_sub_of_le (by omega), cyclicGapSum_full, hmass] at h1
  have hlen : r + ((N : ℕ) - i - r) = (N : ℕ) - i := by omega
  rw [hlen] at h2
  simp only [zero_add] at h1
  have hz : (⟨0, N.pos⟩ : Fin (N : ℕ)) = 0 := by apply Fin.ext; simp
  rw [hz] at h1
  linarith

/-- The left exterior suffix in the literal assembly of Subsection 6.1. -/
theorem cyclicGapSum_assembled_exterior_suffix (e a r : ℕ) (hr : r < e)
    (y : EuclideanSpace ℝ (Fin e)) (u : EuclideanSpace ℝ (Fin (a + 1))) :
    cyclicGapSum (e + a).succPNat
      ⟨a + 1 + r, by change a + 1 + r < e + a + 1; omega⟩ (e - r)
      (WithLp.ofLp (RetainedSimplex.assemble e a
        (InterpolatingDensities.exteriorPermutation e a) y u)) =
      ∑ k : Fin (e - r), y ⟨r + k.val, by have := k.isLt; omega⟩ := by
  rw [cyclicGapSum_nonwrapping _ _ (e - r) (by
    change a + 1 + r + (e - r) ≤ e + a + 1
    omega)]
  apply Finset.sum_congr rfl
  intro k _
  have he : (⟨a + 1 + r + k.val, by have := k.isLt; omega⟩ : Fin (e + a + 1)) =
      ⟨a + 1 + (r + k.val), by have := k.isLt; omega⟩ := by
    apply Fin.ext
    exact add_assoc _ _ _
  change (RetainedSimplex.assemble e a
    (InterpolatingDensities.exteriorPermutation e a) y u)
      ⟨a + 1 + r + k.val, by have := k.isLt; omega⟩ = _
  rw [he]
  exact assemble_exterior_retained e a y u
    ⟨r + k.val, by have := k.isLt; omega⟩

/-- Exact left-boundary distance for the same physical exterior particle
as `cyclicGapSum_assembled_to_exterior`. Together these identify the two
principal images with the two boundary rank families in Appendix C. -/
theorem cyclicGapSum_assembled_to_exterior_complement (e a i r : ℕ)
    (hi : i < a + 1) (hr : r < e) (y : EuclideanSpace ℝ (Fin e))
    (u : EuclideanSpace ℝ (Fin (a + 1)))
    (hmass : (∑ k, (RetainedSimplex.assemble e a
      (InterpolatingDensities.exteriorPermutation e a) y u) k) =
        ((e + a).succPNat : ℝ)) :
    ((e + a).succPNat : ℝ) -
      cyclicGapSum (e + a).succPNat ⟨i, by change i < e + a + 1; omega⟩
        (a + 1 - i + r) (WithLp.ofLp (RetainedSimplex.assemble e a
          (InterpolatingDensities.exteriorPermutation e a) y u)) =
      (∑ k : Fin i, u ⟨k.val, by have := k.isLt; omega⟩) +
        ∑ k : Fin (e - r), y ⟨r + k.val, by have := k.isLt; omega⟩ := by
  rw [cyclicGapSum_linear_complement (e + a).succPNat
    (WithLp.ofLp (RetainedSimplex.assemble e a
      (InterpolatingDensities.exteriorPermutation e a) y u)) hmass i (a + 1 - i + r) (by
    change i + (a + 1 - i + r) < e + a + 1
    omega)]
  have hi0 := cyclicGapSum_assembled_active e a 0 i (by omega) (by omega) y u
  simp only [zero_add] at hi0
  have hz : (⟨0, (e + a).succPNat.pos⟩ : Fin ((e + a).succPNat : ℕ)) = 0 := by
    apply Fin.ext
    simp
  rw [hz] at hi0
  rw [hi0]
  congr 1
  have hstart : i + (a + 1 - i + r) = a + 1 + r := by omega
  have hlen : ((e + a).succPNat : ℕ) - i - (a + 1 - i + r) = e - r := by
    change e + a + 1 - i - (a + 1 - i + r) = e - r
    omega
  simp_rw [hstart, hlen]
  exact cyclicGapSum_assembled_exterior_suffix e a r hr y u

end Riesz2.InterpolantLocalLaws
