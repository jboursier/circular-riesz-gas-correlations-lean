/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.PhysicalCollisionPart3

/-!
# The radial bounds in the collision proof

The two inequalities of equation (A.2), Step 2 of Lemma A.1 in
the paper, with constants before the configuration. Intrinsic coordinates
are centered at the configuration of unit gaps.
-/

public section
noncomputable section

open Set Filter
open scoped Topology BigOperators ContDiff

namespace Riesz2.PhysicalCollision

/-- Lemma A.1, Step 2, display equation (A.2) of the paper:
the radial gradient lower bound and the intrinsic Laplacian upper bound hold
simultaneously. `twoSided` is the indicator of the inverse-gap penalty.
The smooth realization agrees with the energy on its entire domain. -/
theorem penalized_radial_bounds (N : ℕ+) (p : Parameters) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (I : Finset (Fin (N : ℕ))) (twoSided : Bool) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z ∈ intrinsicGapDomain N,
        let V := fun w : gapTangentSpace N =>
          p.val.1 * W (WithLp.toLp 2 (fun i => 1 + w.val i)) + p.val.1 *
            ∑ i ∈ I, (θ.val (a * (1 + w.val i)) +
              if twoSided then θ.val (a / (1 + w.val i)) else 0)
        c * ((⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-p.val.2 - 1) +
          if twoSided then ∑ i ∈ I, (1 + z.val i)⁻¹ ^ 3 else 0) - C ≤
            inner ℝ (gradient V z) z ∧
        Laplacian.laplacian V z ≤ C *
          ((⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-p.val.2 - 2) +
            if twoSided then ∑ i ∈ I, (1 + z.val i)⁻¹ ^ 4 else 0) := by
  obtain ⟨W, hW, hval, _, Ct, _, _, hCt, _, ht⟩ :=
    penalized_differential_estimates N p hN θ ha I twoSided
  obtain ⟨Wr, _, hvalr, c, Cr, hc, hCr, hr⟩ :=
    penalized_radial_lower N p hN θ ha I twoSided
  refine ⟨W, hW, hval, c, max Cr (2 * Ct), hc,
    hCr.trans_le (le_max_left _ _), fun z hz => ?_⟩
  let V := fun w : gapTangentSpace N =>
    p.val.1 * W (WithLp.toLp 2 (fun i => 1 + w.val i)) + p.val.1 *
      ∑ i ∈ I, (θ.val (a * (1 + w.val i)) +
        if twoSided then θ.val (a / (1 + w.val i)) else 0)
  have he : (fun w : gapTangentSpace N =>
      p.val.1 * Wr (WithLp.toLp 2 (fun i => 1 + w.val i)) + p.val.1 *
        ∑ i ∈ I, (θ.val (a * (1 + w.val i)) +
          if twoSided then θ.val (a / (1 + w.val i)) else 0)) =ᶠ[𝓝 z] V := by
    filter_upwards [(AffineMetric.intrinsicGapDomain_isOpen N).mem_nhds hz] with w hw
    have hy := PhysicalEnergy.simplex_subset_ambient N _ (intrinsic_chart_mem_simplex N hw)
    dsimp only [V]
    rw [hvalr ⟨_, hy⟩, hval ⟨_, hy⟩]
  have hrad := hr z hz
  rw [he.gradient_eq] at hrad
  have hd : 1 ≤ (⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-p.val.2 - 2) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (minimum_gap_pos N hz)
      (minimum_gap_le_one N z) (by linarith [p.property.2.1])
  have hi : 0 ≤ if twoSided then ∑ i ∈ I, (1 + z.val i)⁻¹ ^ 4 else 0 := by
    split_ifs
    · exact Finset.sum_nonneg fun i _ => pow_nonneg (inv_nonneg.mpr (hz i).le) _
    · exact le_rfl
  refine ⟨by dsimp only; linarith [le_max_left Cr (2 * Ct)], ?_⟩
  have htrace := (ht z hz).2.1
  change Laplacian.laplacian V z ≤ _ at htrace ⊢
  apply htrace.trans
  have hscale := mul_le_mul_of_nonneg_right (le_max_right Cr (2 * Ct))
    (show 0 ≤ (⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-p.val.2 - 2) +
      if twoSided then ∑ i ∈ I, (1 + z.val i)⁻¹ ^ 4 else 0 by linarith)
  nlinarith only [hscale, mul_nonneg hCt.le (by linarith : 0 ≤
    (⨅ i : Fin (N : ℕ), 1 + z.val i) ^ (-p.val.2 - 2) +
      (if twoSided then ∑ i ∈ I, (1 + z.val i)⁻¹ ^ 4 else 0) - 1)]

end Riesz2.PhysicalCollision
