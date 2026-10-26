/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.PhysicalCorePart6
public import Riesz2.HelfferSjostrand.IntrinsicIntegrationByParts

/-!
# The reference Hessian at unit gaps

The matrix display following equation (3.9) in Subsection 3.2 of the paper.
The coefficient error is summed over the actual short cyclic intervals,
including their antipodal weights.
-/

public section
noncomputable section

open Set
open scoped BigOperators ContDiff

namespace Riesz2.PhysicalEnergy

/-- Internal denominator conversion for the matrix estimate after equation (3.9)
in Subsection 3.2 of the paper. -/
theorem internal_reference_decay {t d : ℝ} (ht : 0 < t) (hd : 0 ≤ d) :
    (1 + d) ^ (-t) ≤ 2 / (1 + d ^ t) := by
  have hx : 0 < 1 + d := by linarith
  have hp : 0 < (1 + d) ^ t := Real.rpow_pos_of_pos hx _
  have hq : 0 < 1 + d ^ t := by positivity
  have h1 : 1 ≤ (1 + d) ^ t := Real.one_le_rpow (by linarith) ht.le
  have h2 : d ^ t ≤ (1 + d) ^ t := Real.rpow_le_rpow hd (by linarith) ht.le
  rw [Real.rpow_neg hx.le, inv_eq_one_div, div_le_div_iff₀ hp hq]
  linarith

/-- The unit-gap display equation (3.10) of the paper
(Subsection 3.2). For every `0 < s < 1`, one
constant works for every period and every matrix entry at unit gaps.
The temperature slot is fixed to one since this is the unscaled energy.
The realization agrees with the ambient energy everywhere on its domain. -/
theorem unit_gap_hessian_comparison (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)),
      ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
        ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
        (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
          W y.val = physicalAmbientGapEnergy (ofLong ⟨1, one_pos⟩ s) N y) ∧
        ∀ i j : Fin (N : ℕ),
          |hessianMatrix W (WithLp.toLp 2 (fun _ => 1)) i j -
            2 * sampledRieszKernel s N hN (j - i)| ≤
              C / (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (s.val + 2) := by
  classical
  obtain ⟨D, hD, herr⟩ := PhysicalCore.sampled_coefficient_error s
  have ht : 0 < s.val + 2 := by linarith [s.property.1]
  refine ⟨2 * D * (1 + 1 / (s.val + 2)), by positivity, fun N hN => ?_⟩
  let p := ofLong (⟨1, one_pos⟩ : InverseTemperature) s
  let y : EuclideanSpace ℝ (Fin (N : ℕ)) := WithLp.toLp 2 (fun _ => 1)
  have hsum (a : Fin (N : ℕ)) (r : ℕ) :
      cyclicGapSum N a r (WithLp.ofLp y) = r := by simp [cyclicGapSum, y]
  have hy : y ∈ gapAmbientDomain N := by
    intro a r hr hrN
    rw [hsum]
    constructor
    · exact_mod_cast (by omega : 0 < r)
    · exact_mod_cast (by omega : r < (N : ℕ))
  obtain ⟨W, hW, hval, hjet⟩ := ambient_derivatives p N
  refine ⟨W, hW, hval, fun a b => ?_⟩
  let L (r : Fin ((N : ℕ) / 2)) : {L : ℝ // 0 < L ∧ L < (N : ℝ)} :=
    ⟨r.val + 1, by
      have hr := r.isLt
      have hNr : (r.val + 1 : ℝ) < N := by exact_mod_cast (by omega : r.val + 1 < (N : ℕ))
      exact ⟨by positivity, hNr⟩⟩
  let m (r : Fin ((N : ℕ) / 2)) : ℝ :=
    2 - if 2 * (r.val + 1) = (N : ℕ) then 1 else 0
  let F (_ : Fin (N : ℕ)) (r : Fin ((N : ℕ) / 2)) : ℝ :=
    m r * (intervalCoefficient p N (L r) -
      sampledSecondDifference s N hN ⟨r.val + 1, by have := r.isLt; omega⟩)
  have hF (i r) : |F i r| ≤ (2 * D) * (r.val + 1 : ℝ) ^ (-(s.val + 2) - 2) := by
    have h := herr ⟨1, one_pos⟩ N hN (r.val + 1) (by omega) (by have := r.isLt; omega)
    simp only [Nat.cast_add, Nat.cast_one] at h
    change |sampledSecondDifference s N hN _ - intervalCoefficient p N (L r)| ≤ _ at h
    rw [abs_sub_comm] at h
    have hm : 0 ≤ m r ∧ m r ≤ 2 := by dsimp only [m]; split_ifs <;> norm_num
    dsimp only [F]
    rw [abs_mul, abs_of_nonneg hm.1]
    have hb := mul_le_mul hm.2 h (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    convert hb using 1; ring_nf
  have hsingle (i j : Fin (N : ℕ)) (r : Fin ((N : ℕ) / 2)) :
      cyclicGapSum N i (r.val + 1) (WithLp.ofLp (EuclideanSpace.single j (1 : ℝ))) =
        if j ∈ cyclicIndexInterval N i (r.val + 1) then 1 else 0 := by
    convert cyclicGapSum_single N i j (show r.val + 1 ≤ (N : ℕ) by have := r.isLt; omega) using 1
    congr 1
    ext k
    simp [EuclideanSpace.single, eq_comm]
  have hcoeff (i) (r : Fin ((N : ℕ) / 2)) :
      intervalCoefficient p N ⟨cyclicGapSum N i (r.val + 1) (WithLp.ofLp y),
        hy i (r.val + 1) (by omega) (by have := r.isLt; omega)⟩ =
      intervalCoefficient p N (L r) := congrArg _ (Subtype.ext (by simpa only [L, Nat.cast_add, Nat.cast_one] using hsum i (r.val + 1)))
  have he : hessianMatrix W y a b - 2 * sampledRieszKernel s N hN (b - a) =
      ∑ i, ∑ r, F i r * (if a ∈ cyclicIndexInterval N i (r.val + 1) then 1 else 0) *
        (if b ∈ cyclicIndexInterval N i (r.val + 1) then 1 else 0) := by
    rw [Intrinsic.hessianMatrix_eq_second
      (hW.contDiffAt ((isOpen_gapAmbientDomain N).mem_nhds hy)),
      (hjet ⟨y, hy⟩ _ _).2, ← referenceIntervalMatrix_full s N hN,
      PhysicalCore.Internal.referenceMatrix_sum]
    simp_rw [hcoeff, hsingle]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    have hr : (r.val + 1) % (N : ℕ) = r.val + 1 :=
      Nat.mod_eq_of_lt (by have := r.isLt; omega)
    simp only [F, m, BoundaryEntries.referenceWeight, show 1 ≤ r.val + 1 by omega,
      ↓reduceIte, hr]
    split_ifs <;> ring
  rw [he]
  convert PhysicalCore.Internal.signed_interval_entry_bound N ht
    (by positivity : 0 ≤ 2 * D) F hF a b using 1
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤
    1 + (Riesz1.cyclicIndexDistance N a b : ℝ)), div_eq_mul_inv]

/-- An equivalent denominator for equation (3.10) of the paper
(Subsection 3.2), obtained from the unit-gap profile. -/
theorem reference_hessian_comparison (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)),
      ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
        ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
        (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
          W y.val = physicalAmbientGapEnergy (ofLong ⟨1, one_pos⟩ s) N y) ∧
        ∀ i j : Fin (N : ℕ),
          |hessianMatrix W (WithLp.toLp 2 (fun _ => 1)) i j -
            2 * sampledRieszKernel s N hN (j - i)| ≤
              C / (1 + (Riesz1.cyclicIndexDistance N i j : ℝ) ^ (s.val + 2)) := by
  obtain ⟨C, hC, hprofile⟩ := unit_gap_hessian_comparison s
  refine ⟨2 * C, by positivity, fun N hN => ?_⟩
  obtain ⟨W, hW, hval, hentry⟩ := hprofile N hN
  refine ⟨W, hW, hval, fun i j => (hentry i j).trans ?_⟩
  have hd := internal_reference_decay (by linarith [s.property.1] : 0 < s.val + 2)
    (Nat.cast_nonneg (Riesz1.cyclicIndexDistance N i j))
  have hh := mul_le_mul_of_nonneg_left hd hC.le
  rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤
    1 + (Riesz1.cyclicIndexDistance N i j : ℝ))] at hh
  convert hh using 1 <;> ring

end Riesz2.PhysicalEnergy
