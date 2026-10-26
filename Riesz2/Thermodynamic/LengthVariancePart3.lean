/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.RpowPartialSums
public import Riesz2.ToMathlib.CyclicIndicatorConvolution
public import Riesz2.Thermodynamic.LengthVariancePart2
public import Riesz2.ToMathlib.AffineMetricTransport

/-!
# Compensated length curvature and the collision density

Supporting results for the proof of Lemma 6.5. The cyclic overlap sum and the physical
interval Hessian formula give the expected full energy-plus-penalty curvature, uniformly
on compact temperature intervals. The actual penalized density is differentiable across
collision faces. Extended length variances are transported to the literal active law.
-/

public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Finset

namespace Riesz2.LengthVariance.Internal

/-- The squared overlap profile has summable power weights, with a constant
independent of both the active size and the interval truncation. -/
theorem interval_overlap_power_sum {s : ℝ} (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ k K : ℕ, 1 ≤ k →
      (∑ j ∈ range K, (1 + (j : ℝ)) ^ (-s - 2) *
        (min (k : ℝ) (1 + (j : ℝ)) * (k : ℝ) * (1 + (j : ℝ)))) ≤
          C * (k : ℝ) ^ (2 - min s 1) := by
  have he (x : ℝ) (hx : 0 < x) :
      x ^ (-s - 2) * (x * x) = x ^ (-s) := by
    rw [← sq, ← Real.rpow_two, ← Real.rpow_add hx]
    congr 1
    ring
  have he' (x : ℝ) (hx : 0 < x) :
      x ^ (-s - 2) * x = x ^ (-(1 + s)) := by
    conv_lhs => rhs; rw [← Real.rpow_one x]
    rw [← Real.rpow_add hx]
    congr 1
    ring
  by_cases hshort : 1 < s
  · let C := ∑' j : ℕ, (1 + (j : ℝ)) ^ (-s)
    have hC : 0 < C := by
      have hh := (summable_one_add_rpow_neg hshort).le_tsum 0
        (fun j _ => Real.rpow_nonneg (by positivity) _)
      norm_num at hh
      exact lt_of_lt_of_le zero_lt_one hh
    refine ⟨C, hC, fun k K hk => ?_⟩
    have hmin : min s 1 = 1 := min_eq_right hshort.le
    rw [hmin, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    calc
      _ ≤ ∑ j ∈ range K, (k : ℝ) * (1 + (j : ℝ)) ^ (-s) := by
        apply sum_le_sum
        intro j _
        calc
          _ ≤ (1 + (j : ℝ)) ^ (-s - 2) *
              ((1 + (j : ℝ)) * (k : ℝ) * (1 + (j : ℝ))) := by
            gcongr
            exact min_le_right _ _
          _ = _ := by
            calc
              _ = (k : ℝ) * ((1 + (j : ℝ)) ^ (-s - 2) *
                ((1 + (j : ℝ)) * (1 + (j : ℝ)))) := by ring
              _ = _ := by rw [he _ (by positivity)]
      _ = (k : ℝ) * ∑ j ∈ range K, (1 + (j : ℝ)) ^ (-s) := by rw [mul_sum]
      _ ≤ (k : ℝ) * C := mul_le_mul_of_nonneg_left
        (sum_range_one_add_rpow_le_tsum hshort K) (Nat.cast_nonneg k)
      _ = _ := mul_comm _ _
  · have hlong : s < 1 := lt_of_le_of_ne (le_of_not_gt hshort) hs1
    let A := 1 / (1 - s)
    let B := 1 + 1 / s
    refine ⟨A + B, by dsimp [A, B]; positivity, fun k K hk => ?_⟩
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    let f := fun j : ℕ => (1 + (j : ℝ)) ^ (-s - 2) *
      (min (k : ℝ) (1 + (j : ℝ)) * (k : ℝ) * (1 + (j : ℝ)))
    have hf0 (j) : 0 ≤ f j := by dsimp [f]; positivity
    have hhead : (∑ j ∈ range (min K k), f j) ≤ A * (k : ℝ) ^ (2 - s) := by
      calc
        _ ≤ ∑ j ∈ range k, (k : ℝ) * (1 + (j : ℝ)) ^ (-s) := by
          apply (sum_le_sum_of_subset_of_nonneg (range_mono (min_le_right K k))
            (fun j _ _ => hf0 j)).trans
          apply sum_le_sum
          intro j _
          dsimp only [f]
          calc
            _ ≤ (1 + (j : ℝ)) ^ (-s - 2) *
                ((1 + (j : ℝ)) * (k : ℝ) * (1 + (j : ℝ))) := by
              gcongr
              exact min_le_right _ _
            _ = _ := by
              calc
                _ = (k : ℝ) * ((1 + (j : ℝ)) ^ (-s - 2) *
                  ((1 + (j : ℝ)) * (1 + (j : ℝ)))) := by ring
                _ = _ := by rw [he _ (by positivity)]
        _ = (k : ℝ) * ∑ j ∈ range k, (1 + (j : ℝ)) ^ (-s) := by rw [mul_sum]
        _ ≤ (k : ℝ) * ((k : ℝ) ^ (1 - s) / (1 - s)) :=
          mul_le_mul_of_nonneg_left (sum_range_one_add_rpow_le_of_lt_one hs hlong hk) hk0.le
        _ = _ := by
          have hp : (k : ℝ) * (k : ℝ) ^ (1 - s) = (k : ℝ) ^ (2 - s) := by
            conv_lhs => lhs; rw [← Real.rpow_one (k : ℝ)]
            rw [← Real.rpow_add hk0]
            congr 1
            ring
          dsimp [A]
          rw [← mul_div_assoc, hp]
          ring
    let g := fun j : ℕ => if (k : ℝ) ≤ 1 + (j : ℝ) then
      (1 + (j : ℝ)) ^ (-(1 + s)) else 0
    have hg0 (j) : 0 ≤ g j := by dsimp [g]; split_ifs <;> positivity
    have hgs : Summable g := (summable_one_add_rpow_neg (show 1 < 1 + s by linarith)).of_nonneg_of_le
      hg0 (fun j => by
        dsimp [g]
        split_ifs
        · exact le_rfl
        · positivity)
    have htail : (∑ j ∈ Ico (min K k) K, f j) ≤ B * (k : ℝ) ^ (2 - s) := by
      calc
        _ ≤ ∑ j ∈ Ico (min K k) K, (k : ℝ) ^ 2 * g j := by
          apply sum_le_sum
          intro j hj
          have hjk : k ≤ j := by have := mem_Ico.mp hj; omega
          have hjk' : (k : ℝ) ≤ 1 + (j : ℝ) := by exact_mod_cast (show k ≤ 1 + j by omega)
          dsimp only [f, g]
          rw [ite_eq_left hjk']
          calc
            _ ≤ (1 + (j : ℝ)) ^ (-s - 2) *
                ((k : ℝ) * (k : ℝ) * (1 + (j : ℝ))) := by
              gcongr
              exact min_le_left _ _
            _ = _ := by
              calc
                _ = (k : ℝ) ^ 2 * ((1 + (j : ℝ)) ^ (-s - 2) * (1 + (j : ℝ))) := by ring
                _ = _ := by rw [he' _ (by positivity)]
        _ = (k : ℝ) ^ 2 * ∑ j ∈ Ico (min K k) K, g j := by rw [mul_sum]
        _ ≤ (k : ℝ) ^ 2 * ∑' j, g j := mul_le_mul_of_nonneg_left
          (hgs.sum_le_tsum _ (fun j _ => hg0 j)) (sq_nonneg _)
        _ ≤ (k : ℝ) ^ 2 * (B * (k : ℝ) ^ (-s)) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          simpa only [g, B, show (1 + s) - 1 = s by ring,
            show (1 : ℝ) - (1 + s) = -s by ring] using
            tsum_tail_indicator_le (show 1 < 1 + s by linarith) hk1
        _ = _ := by
          rw [mul_left_comm, ← Real.rpow_two, ← Real.rpow_add hk0]
          congr 1
    rw [← sum_range_add_sum_Ico f (min_le_left K k)]
    exact (add_le_add hhead htail).trans_eq (by rw [min_eq_left hlong.le]; ring)

end Riesz2.LengthVariance.Internal

namespace Riesz2.LengthVariance

open MeasureTheory Finset
open scoped BigOperators

/-- See the proof of Lemma 6.5 in the paper: the physical compensated
length direction is the centered active indicator. The normalization is
proved on every coordinate, including the exterior coordinates. -/
theorem compensated_length_centered_indicator (n m : ℕ) :
    let I : Finset (Fin (n + 1 + (m + 1))) :=
      univ.map (Fin.castAddEmb (m + 1))
    let u : EuclideanSpace ℝ (Fin (n + 1)) := WithLp.toLp 2 (fun _ => (n + 1 : ℝ)⁻¹)
    let w := MarginalHessian.compensatedDirection (n + 1) m (Equiv.refl _) u
    I.card = n + 1 ∧ ∀ j, w j = ((n + 1 : ℝ)⁻¹ + (m + 1 : ℝ)⁻¹) *
      ((if j ∈ I then 1 else 0) - (I.card : ℝ) / (n + 1 + (m + 1) : ℝ)) := by
  classical
  intro I u w
  have hcard : I.card = n + 1 := by simp [I]
  refine ⟨hcard, ?_⟩
  intro j
  have hj := (compensated_length_direction n m).2.2 j
  change w j = _ at hj
  rw [hj, hcard]
  have hmem : j ∈ I ↔ j.val < n + 1 := by
    constructor
    · intro h
      obtain ⟨i, _, hi⟩ := mem_map.mp h
      rw [← hi]
      exact i.isLt
    · intro h
      exact mem_map.mpr ⟨⟨j.val, h⟩, mem_univ _, Fin.ext rfl⟩
  simp only [hmem, Nat.cast_add, Nat.cast_one]
  split_ifs <;> field_simp <;> ring

namespace Internal

/-- See the proof of Lemma 6.5 in the paper: the complete deterministic
power sum for the actual compensated direction. Its constant depends only
on the exponent, independently of both sizes and the truncation. -/
theorem compensated_interval_power_bound {s : ℝ} (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n m : ℕ, 2 * (n + 1) ≤ n + 1 + (m + 1) →
      let N := (n + 1 + m).succPNat
      let u : EuclideanSpace ℝ (Fin (n + 1)) := WithLp.toLp 2 (fun _ => (n + 1 : ℝ)⁻¹)
      let w := MarginalHessian.compensatedDirection (n + 1) m (Equiv.refl _) u
      (∑ r : Fin ((N : ℕ) / 2), (r.val + 1 : ℝ) ^ (-s - 2) *
        ∑ i : Fin (N : ℕ), (cyclicGapSum N i (r.val + 1) (WithLp.ofLp w)) ^ 2) ≤
          C * (n + 1 : ℝ) ^ (-min s 1) := by
  classical
  obtain ⟨D, hD, hpower⟩ := interval_overlap_power_sum hs hs1
  refine ⟨4 * D, by positivity, fun n m hsize => ?_⟩
  intro N u w
  let I : Finset (Fin (N : ℕ)) := univ.map (Fin.castAddEmb (m + 1))
  let α : ℝ := (n + 1 : ℝ)⁻¹ + (m + 1 : ℝ)⁻¹
  have hI : I.card = n + 1 := by
    change (univ.map (Fin.castAddEmb (m + 1)) : Finset (Fin ((n + 1) + (m + 1)))).card = n + 1
    simp
  have hw : WithLp.ofLp w = fun j => α *
      ((if j ∈ I then 1 else 0) - (I.card : ℝ) / (N : ℝ)) := by
    funext j
    simpa only [N, Nat.succPNat_coe, Nat.cast_add, Nat.cast_one, Nat.cast_succ,
      Nat.cast_zero, zero_add, add_assoc] using (compensated_length_centered_indicator n m).2 j
  have hn0 : (0 : ℝ) < n + 1 := by positivity
  have hm0 : (0 : ℝ) < m + 1 := by positivity
  have hnm : (n + 1 : ℝ) ≤ m + 1 := by exact_mod_cast (show n + 1 ≤ m + 1 by omega)
  have hα : α ≤ 2 * (n + 1 : ℝ)⁻¹ := by
    have hh := inv_anti₀ hn0 hnm
    dsimp [α]
    linarith
  have hα0 : 0 ≤ α := by dsimp [α]; positivity
  have hαsq : α ^ 2 ≤ 4 * (n + 1 : ℝ)⁻¹ ^ 2 := by
    nlinarith [sq_nonneg (2 * (n + 1 : ℝ)⁻¹ - α)]
  have hterm (r : Fin ((N : ℕ) / 2)) :
      (∑ i : Fin (N : ℕ), (cyclicGapSum N i (r.val + 1) (WithLp.ofLp w)) ^ 2) ≤
        α ^ 2 * (min (n + 1 : ℝ) (r.val + 1 : ℝ) * (n + 1 : ℝ) * (r.val + 1 : ℝ)) := by
    rw [hw]
    have hh := sum_sq_cyclicGapSum_centered_indicator_le N I
      (show r.val + 1 ≤ (N : ℕ) by have := r.isLt; omega) α
    simpa only [hI, Nat.cast_add, Nat.cast_one] using hh
  calc
    _ ≤ ∑ r : Fin ((N : ℕ) / 2), (r.val + 1 : ℝ) ^ (-s - 2) *
        (α ^ 2 * (min (n + 1 : ℝ) (r.val + 1 : ℝ) * (n + 1 : ℝ) * (r.val + 1 : ℝ))) :=
      sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (hterm r) (by positivity)
    _ = α ^ 2 * ∑ r : Fin ((N : ℕ) / 2), (r.val + 1 : ℝ) ^ (-s - 2) *
        (min (n + 1 : ℝ) (r.val + 1 : ℝ) * (n + 1 : ℝ) * (r.val + 1 : ℝ)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro r _
      ring
    _ ≤ α ^ 2 * (D * (n + 1 : ℝ) ^ (2 - min s 1)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg α)
      simpa only [sum_range, Nat.cast_add, Nat.cast_one, add_comm] using
        hpower (n + 1) ((N : ℕ) / 2) (by omega)
    _ ≤ (4 * (n + 1 : ℝ)⁻¹ ^ 2) * (D * (n + 1 : ℝ) ^ (2 - min s 1)) :=
      mul_le_mul_of_nonneg_right hαsq (by positivity)
    _ = _ := by
      have he : (n + 1 : ℝ)⁻¹ ^ 2 = (n + 1 : ℝ) ^ (-2 : ℝ) := by
        rw [Real.rpow_neg hn0.le, Real.rpow_two, inv_pow]
      rw [he]
      calc
        _ = 4 * D * ((n + 1 : ℝ) ^ (-2 : ℝ) * (n + 1 : ℝ) ^ (2 - min s 1)) := by ring
        _ = _ := by rw [← Real.rpow_add hn0]; congr 2; ring

end Internal
end Riesz2.LengthVariance

namespace Riesz2.LengthVariance

open MeasureTheory Finset
open scoped BigOperators ContDiff

/-- See the proof of Lemma 6.5 in the paper: expected Hamiltonian
curvature in the compensated unit length direction, for the actual two-sided
tilt. The realization agrees with the energy on its entire ambient
domain. Integrability is asserted before the real expectation. Constants
are uniform on each compact positive temperature interval. -/
theorem expected_energy_curvature (s ε βlo βhi : ℝ) (hs : 0 < s)
    (hs1 : s ≠ 1) (hε : 0 < ε) (hlo : 0 < βlo) (hle : βlo ≤ βhi)
    (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ n m : ℕ,
      2 * (n + 1) ≤ n + 1 + (m + 1) →
      let N := (n + 1 + m).succPNat
      let a : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩
      let hn : (a : ℕ) ≤ (N : ℕ) := by change n + 1 ≤ n + 1 + m + 1; omega
      let u : EuclideanSpace ℝ (Fin (n + 1)) := WithLp.toLp 2 (fun _ => (n + 1 : ℝ)⁻¹)
      let w := MarginalHessian.compensatedDirection (n + 1) m (Equiv.refl _) u
      ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
        ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
        (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
          W y.val = physicalAmbientGapEnergy p N y) ∧
        Integrable (fun X => fderiv ℝ (fderiv ℝ W) (WithLp.toLp 2 (gapVector X)) w w)
          (tiltedParticleMeasure p N a hn θ ε true) ∧
        (∫ X, fderiv ℝ (fderiv ℝ W) (WithLp.toLp 2 (gapVector X)) w w
          ∂tiltedParticleMeasure p N a hn θ ε true) ≤ C * (n + 1 : ℝ) ^ (-min s 1) := by
  classical
  obtain ⟨B, hB, hcoeff⟩ := compact_interval_curvature s ε βlo βhi hs hs1 hε hlo hle θ
  obtain ⟨D, hD, hpower⟩ := Internal.compensated_interval_power_bound hs hs1
  refine ⟨B * D, mul_pos hB hD, fun p hps hpl hph n m hsize => ?_⟩
  intro N a hn u w
  have hN : 2 ≤ (N : ℕ) := by dsimp [N]; omega
  let μ := tiltedParticleMeasure p N a hn θ ε true
  obtain ⟨W, hW, hval, hd⟩ := PhysicalEnergy.ambient_derivatives p N
  let F := fun (i : Fin (N : ℕ)) (r : Fin ((N : ℕ) / 2)) =>
    GoodBlocks.particleCoefficient p N i.val (r.val + 1) (by omega) (by have := r.isLt; omega)
  let q := fun (i : Fin (N : ℕ)) (r : Fin ((N : ℕ) / 2)) =>
    (cyclicGapSum N i (r.val + 1) (WithLp.ofLp w)) ^ 2
  have hFi (i) (r) : Integrable (F i r) μ :=
    (hcoeff p hps hpl hph N a hN hn i.val (r.val + 1) (by omega) (by have := r.isLt; omega)).1
  have hFb (i) (r) : (∫ X, F i r X ∂μ) ≤ B * (r.val + 1 : ℝ) ^ (-s - 2) :=
    by simpa only [Nat.cast_add, Nat.cast_one] using
      (hcoeff p hps hpl hph N a hN hn i.val (r.val + 1) (by omega) (by have := r.isLt; omega)).2
  have hquad (X : Riesz1.Configuration N) :
      fderiv ℝ (fderiv ℝ W) (WithLp.toLp 2 (gapVector X)) w w =
        ∑ i, ∑ r, F i r X * q i r := by
    rw [(hd ⟨WithLp.toLp 2 (gapVector X), GapChart.gapVector_mem_gapAmbientDomain X⟩ w w).2]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro r _
    dsimp only [F, q]
    rw [GoodBlocks.particleCoefficient_gapVector, pow_two]
  have hi : Integrable (fun X => ∑ i, ∑ r, F i r X * q i r) μ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun r _ => (hFi i r).mul_const _
  refine ⟨W, hW, hval, hi.congr (Filter.Eventually.of_forall fun X => (hquad X).symm), ?_⟩
  calc
    _ = ∫ X, ∑ i, ∑ r, F i r X * q i r ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall hquad)
    _ = ∑ i, ∑ r, (∫ X, F i r X ∂μ) * q i r := by
      rw [integral_finsetSum _ (fun i _ =>
        integrable_finsetSum _ fun r _ => (hFi i r).mul_const _)]
      apply sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun r _ => (hFi i r).mul_const _)]
      simp_rw [integral_mul_const]
    _ ≤ ∑ i, ∑ r, (B * (r.val + 1 : ℝ) ^ (-s - 2)) * q i r :=
      sum_le_sum fun i _ => sum_le_sum fun r _ =>
        mul_le_mul_of_nonneg_right (hFb i r) (sq_nonneg _)
    _ = B * ∑ r : Fin ((N : ℕ) / 2), (r.val + 1 : ℝ) ^ (-s - 2) *
        ∑ i : Fin (N : ℕ), q i r := by
      rw [sum_comm, mul_sum]
      apply sum_congr rfl
      intro r _
      rw [← mul_sum]
      ring
    _ ≤ B * (D * (n + 1 : ℝ) ^ (-min s 1)) :=
      mul_le_mul_of_nonneg_left (hpower n m hsize) hB.le
    _ = _ := by ring

end Riesz2.LengthVariance

namespace Riesz2.LengthVariance

open MeasureTheory Finset
open scoped BigOperators ContDiff

/-- See the proof of Lemma 6.5 in the paper: expected total curvature
of energy plus the actual active penalty in the compensated length direction.
This is the full Hessian input for the two global score identities. All real
integrals in the conclusion are integrable. -/
theorem expected_total_curvature (s ε βlo βhi : ℝ) (hs : 0 < s)
    (hs1 : s ≠ 1) (hε : 0 < ε) (hlo : 0 < βlo) (hle : βlo ≤ βhi)
    (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ n m : ℕ,
      2 * (n + 1) ≤ n + 1 + (m + 1) →
      let N := (n + 1 + m).succPNat
      let a : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩
      let hn : (a : ℕ) ≤ (N : ℕ) := by change n + 1 ≤ n + 1 + m + 1; omega
      let u : EuclideanSpace ℝ (Fin (n + 1)) := WithLp.toLp 2 (fun _ => (n + 1 : ℝ)⁻¹)
      let w := MarginalHessian.compensatedDirection (n + 1) m (Equiv.refl _) u
      ∃ U : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
        ContDiffOn ℝ ∞ U (gapAmbientDomain N) ∧
        (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
          U y.val = physicalAmbientGapEnergy p N y +
            ∑ i : Fin (n + 1), (θ.val ((n + 1 : ℝ) ^ (-ε) * y.val (i.castAdd (m + 1))) +
              θ.val ((n + 1 : ℝ) ^ (-ε) / y.val (i.castAdd (m + 1))))) ∧
        Integrable (fun X => fderiv ℝ (fderiv ℝ U) (WithLp.toLp 2 (gapVector X)) w w)
          (tiltedParticleMeasure p N a hn θ ε true) ∧
        (∫ X, fderiv ℝ (fderiv ℝ U) (WithLp.toLp 2 (gapVector X)) w w
          ∂tiltedParticleMeasure p N a hn θ ε true) ≤ C * (n + 1 : ℝ) ^ (-min s 1) := by
  classical
  obtain ⟨A, hA, henergy⟩ := expected_energy_curvature s ε βlo βhi hs hs1 hε hlo hle θ
  obtain ⟨B, hB, hpenalty⟩ := expected_penalty_curvature s ε βlo βhi hs hs1 hε hlo hle θ
  refine ⟨A + B, add_pos hA hB, fun p hps hpl hph n m hsize => ?_⟩
  intro N a hn u w
  let μ := tiltedParticleMeasure p N a hn θ ε true
  have hN : 2 ≤ (N : ℕ) := by dsimp [N]; omega
  obtain ⟨W, hW, hval, hiW, hbW⟩ := henergy p hps hpl hph n m hsize
  let P := fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
    ∑ i, (θ.val ((n + 1 : ℝ) ^ (-ε) * x i) + θ.val ((n + 1 : ℝ) ^ (-ε) / x i))
  let T₀ : EuclideanSpace ℝ (Fin (N : ℕ)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    { toFun := fun y => WithLp.toLp 2 (fun i => y (i.castAdd (m + 1)))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let T := T₀.toContinuousLinearMap
  have hT (y) (i : Fin (n + 1)) : T y i = y (i.castAdd (m + 1)) := rfl
  have hTw : T w = u := by
    ext i
    exact MarginalHessian.compensatedDirection_retained (n + 1) m (Equiv.refl _) u i
  have hTgap (X : Riesz1.Configuration N) : T (WithLp.toLp 2 (gapVector X)) =
      WithLp.toLp 2 (finiteGapBlock (K := a) X) := by ext i; rfl
  have hPs (x : EuclideanSpace ℝ (Fin (n + 1))) (hx : ∀ i, 0 < x i) :
      ContDiffAt ℝ ∞ P x := by
    apply ContDiffAt.sum
    intro i _
    have hproj : ContDiffAt ℝ ∞ (fun y : EuclideanSpace ℝ (Fin (n + 1)) => y i) x :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt
    exact ((PhysicalCollision.cutoff_contDiffAt θ (mul_pos (Real.rpow_pos_of_pos (by positivity) _) (hx i))).comp x (contDiffAt_const.mul hproj)).add
      ((PhysicalCollision.cutoff_contDiffAt θ (div_pos (Real.rpow_pos_of_pos (by positivity) _) (hx i))).comp x (contDiffAt_const.div hproj (hx i).ne'))
  let H := fun X : Riesz1.Configuration N =>
    fderiv ℝ (fderiv ℝ P) (WithLp.toLp 2 (finiteGapBlock (K := a) X)) u u
  have hH0 (X) : 0 ≤ H X := by
    obtain ⟨D, _, hd⟩ := Internal.penalty_direction_curvature θ
    exact (hd ((n + 1 : ℝ) ^ (-ε)) (by positivity) (n + 1)
      (WithLp.toLp 2 (finiteGapBlock (K := a) X)) u (fun i => Riesz1.gap_pos X i.val)).1
  have hHm : Measurable H :=
    ((ContinuousLinearMap.measurable_apply u).comp
      (measurable_fderiv_apply_const ℝ (fderiv ℝ P) u)).comp
      ((PiLp.continuous_toLp 2 _).measurable.comp
        (measurable_pi_iff.mpr fun i => Riesz1.measurable_gap i.val))
  have hHb : (∫⁻ X, ENNReal.ofReal (H X) ∂μ) ≤ ENNReal.ofReal (B * (n + 1 : ℝ) ^ (-min s 1)) := by
    have hb := hpenalty p hps hpl hph N a hN hn
    simp only [a, PNat.mk_coe, Nat.cast_add, Nat.cast_one] at hb
    apply hb.trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hB.le
    apply Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) n])
    have ht : min s 1 ≤ 1 := min_le_right _ _
    linarith
  have hiH : Integrable H μ := ⟨hHm.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hH0)).mpr
      (hHb.trans_lt ENNReal.ofReal_lt_top)⟩
  have hbH : (∫ X, H X ∂μ) ≤ B * (n + 1 : ℝ) ^ (-min s 1) := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    rw [ofReal_integral_eq_lintegral_ofReal hiH (Filter.Eventually.of_forall hH0)]
    exact hHb
  let U := fun y => W y + P (T y)
  have hUP : ContDiffOn ℝ ∞ (fun y => P (T y)) (gapAmbientDomain N) := by
    intro y hy
    have hpos (i : Fin (n + 1)) : 0 < T y i := by
      simpa only [hT, PhysicalEnergy.gapSum_one] using
        (hy (i.castAdd (m + 1)) 1 (by omega) (by omega)).1
    exact ((hPs (T y) hpos).comp y T.contDiff.contDiffAt).contDiffWithinAt
  have hquad (X : Riesz1.Configuration N) :
      fderiv ℝ (fderiv ℝ U) (WithLp.toLp 2 (gapVector X)) w w =
        fderiv ℝ (fderiv ℝ W) (WithLp.toLp 2 (gapVector X)) w w + H X := by
    let y := WithLp.toLp 2 (gapVector X)
    have hy := GapChart.gapVector_mem_gapAmbientDomain X
    have hW2 := (hW.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hy)).of_le
      (show (2 : WithTop ℕ∞) ≤ ∞ by simp)
    have hP2 := (hUP.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hy)).of_le
      (show (2 : WithTop ℕ∞) ≤ ∞ by simp)
    rw [PhysicalCollision.internal_hessian_add hW2 hP2 w w]
    congr 1
    have he := AffineMetricTransport.hessian_comp_affine (f := P) (x := y) T 0
      (by simpa only [add_zero, y, hTgap] using
        (hPs (WithLp.toLp 2 (finiteGapBlock (K := a) X))
          (fun i => Riesz1.gap_pos X i.val)).of_le (show (2 : WithTop ℕ∞) ≤ ∞ by simp)) w w
    simpa only [add_zero, y, hTw, hTgap, H] using he
  refine ⟨U, hW.add hUP, ?_, ?_, ?_⟩
  · intro y
    dsimp only [U]
    rw [hval y]
    rfl
  · exact (hiW.add hiH).congr (Filter.Eventually.of_forall fun X => (hquad X).symm)
  · rw [integral_congr_ae (Filter.Eventually.of_forall hquad), integral_add hiW hiH]
    exact (add_le_add hbW hbH).trans_eq (by ring)

end Riesz2.LengthVariance

namespace Riesz2.LengthVariance

open Set Filter
open scoped Topology ContDiff

/-- See the proof of Lemma 6.5 in the paper, collision boundary step:
the actual two-sided penalized density is differentiable across every
collision face in every affine mass chart. Nonnegative penalization preserves
the zero first derivative of the unpenalized density at a collision. This
assertion concerns the density itself, rather than its score flux. -/
theorem penalized_affine_density_differentiable (p : Parameters) (k : ℕ) (hk : 1 ≤ k)
    (d : ℕ) (A : EuclideanSpace ℝ (Fin d) →ᴬ[ℝ] EuclideanSpace ℝ (Fin (k + 1)))
    (hmass : ∀ x, ∑ i, A x i = (k + 1 : ℝ)) (θ : PhysicalCutoff)
    {a : ℝ} (ha : 0 < a) (J : Finset (Fin (k + 1))) :
    Differentiable ℝ (fun x => (ProperMarginalChart.penalizedDensity p k θ a J true (A x)).toReal) := by
  classical
  let f := fun x => (ProperMarginalChart.density p k (A x)).toReal
  let g := fun x => (ProperMarginalChart.penalizedDensity p k θ a J true (A x)).toReal
  let P := fun x => ∑ i ∈ J, (θ.val (a * A x i) + θ.val (a * (A x i)⁻¹))
  have hf : ContDiff ℝ ∞ f := MarginalHessian.physical_affine_density_smooth p k hk d A hmass
  have hgf (x) : g x = f x * Real.exp (-p.val.1 * P x) := by
    dsimp [g, f, ProperMarginalChart.penalizedDensity, P]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  have hnonneg (x) : 0 ≤ g x := ENNReal.toReal_nonneg
  have hbound (x) : g x ≤ f x := by
    by_cases hx : ∀ i, 0 < A x i
    · rw [hgf]
      apply mul_le_of_le_one_right ENNReal.toReal_nonneg
      apply Real.exp_le_one_iff.mpr
      have hP : 0 ≤ P x := by
        apply Finset.sum_nonneg
        intro i _
        exact add_nonneg (θ.property.2.2.1 _ (mul_nonneg ha.le (hx i).le))
          (θ.property.2.2.1 _ (mul_nonneg ha.le (inv_nonneg.mpr (hx i).le)))
      nlinarith [p.property.1]
    · have hz : f x = 0 := by
        have hnot : A x ∉ AffineSimplex.massSimplex k (k + 1) := fun h => hx h.1
        simp only [f, ProperMarginalChart.density, dite_eq_right hnot, ENNReal.toReal_zero]
      rw [hgf, hz, zero_mul]
  intro x
  change DifferentiableAt ℝ g x
  by_cases hx : ∀ i, 0 < A x i
  · have hPs : ContDiffAt ℝ ∞ P x := by
      apply ContDiffAt.sum
      intro i _
      have hi : ContDiffAt ℝ ∞ (fun y => A y i) x :=
        (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt.comp x A.contDiff.contDiffAt
      exact ((PhysicalCollision.cutoff_contDiffAt θ (mul_pos ha (hx i))).comp x
        (contDiffAt_const.mul hi)).add
        ((PhysicalCollision.cutoff_contDiffAt θ (mul_pos ha (inv_pos.mpr (hx i)))).comp x
          (contDiffAt_const.mul (hi.inv (hx i).ne')))
    have hg : g = fun y => f y * Real.exp (-p.val.1 * P y) := funext hgf
    rw [hg]
    exact ((hf.contDiffAt).mul (((contDiffAt_const (c := -p.val.1)).mul hPs).exp)).differentiableAt (by simp)
  · have hfx : f x = 0 := by
      have hnot : A x ∉ AffineSimplex.massSimplex k (k + 1) := fun h => hx h.1
      simp only [f, ProperMarginalChart.density, dite_eq_right hnot, ENNReal.toReal_zero]
    have hgx : g x = 0 := le_antisymm ((hbound x).trans_eq hfx) (hnonneg x)
    have hmin : IsLocalMin f x := Eventually.of_forall fun y => by
      rw [hfx]
      exact ENNReal.toReal_nonneg
    have hdf : HasFDerivAt f (0 : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) x := by
      have hh := (hf.differentiable (by simp) x).hasFDerivAt
      rwa [hmin.fderiv_eq_zero] at hh
    have ho := hdf.isLittleO
    simp only [hfx, sub_zero, zero_apply] at ho
    apply (HasFDerivAt.of_isLittleO (f' := (0 : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)) ?_).differentiableAt
    simp only [hgx, sub_zero, zero_apply]
    apply Asymptotics.IsLittleO.of_bound
    intro c hc
    filter_upwards [ho.bound hc] with y hy
    exact (show ‖g y‖ ≤ ‖f y‖ by
      rw [Real.norm_of_nonneg (hnonneg y), Real.norm_of_nonneg ENNReal.toReal_nonneg]
      exact hbound y).trans hy

end Riesz2.LengthVariance

namespace Riesz2.LengthVariance

open MeasureTheory

/-- See the proof of Lemma 6.5 in the paper: exact transfer of the
extended length variance from the full tilted particle law to the literal
active law. The full-law second moment is a conclusion. -/
theorem active_variance_eq_particle (p : Parameters) (n m : ℕ) (θ : PhysicalCutoff) (ε : ℝ) :
    let N := (n + 1 + m).succPNat
    let a : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩
    let hn : (a : ℕ) ≤ (N : ℕ) := by change n + 1 ≤ n + 1 + m + 1; omega
    ∃ hS : Integrable (fun X : Riesz1.Configuration N => ∑ i : Fin (n + 1), gap X i.val)
        (tiltedParticleMeasure p N a hn θ ε true),
      MemLp (fun X : Riesz1.Configuration N => ∑ i : Fin (n + 1), gap X i.val) 2
        (tiltedParticleMeasure p N a hn θ ε true) ∧
      Riesz1.variance (LengthAveragingFibres.activeMeasure p n m θ ε) (fun x => ∑ i, x i)
        (memLp_one_iff_integrable.mp (length_memLp p n m θ ε 1)) =
      Riesz1.variance (tiltedParticleMeasure p N a hn θ ε true)
        (fun X => ∑ i : Fin (n + 1), gap X i.val) hS := by
  intro N a hn
  let μ := tiltedParticleMeasure p N a hn θ ε true
  have := (InterpolatingDensities.tilt_valid p N a hn θ ε true).2.2
  let T := fun X : Riesz1.Configuration N => WithLp.toLp 2 (finiteGapBlock (K := a) X)
  have hm : Measurable T := (WithLp.measurable_toLp 2 _).comp
    (measurable_pi_iff.mpr fun i => Riesz1.measurable_gap i.val)
  have hF : MemLp (fun x : EuclideanSpace ℝ (Fin (n + 1)) => ∑ i, x i) 2 (μ.map T) :=
    length_memLp p n m θ ε 2
  have hS := hF.comp_of_map hm.aemeasurable
  refine ⟨hS.integrable one_le_two, hS, ?_⟩
  exact Riesz1.variance_map_eq μ hm.aemeasurable hF

end Riesz2.LengthVariance
