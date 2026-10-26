/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.ConditionalForces
public import Riesz2.DecayLong.ExteriorForcesPart2
public import Riesz2.DecayLong.BoundaryEntriesPart4

/-!
# Cancellation in physical compensation coefficients

Continuation of Lemma 5.7. The interval
representation retains the two endpoints in an adjacent row difference.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical Fin.NatCast

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.ConditionalForces

private theorem interval_diameter (N : ℕ+) {r : ℕ} (hr : 2 * r ≤ (N : ℕ))
    (a i j : Fin (N : ℕ)) (hi : i ∈ cyclicIndexInterval N a r)
    (hj : j ∈ cyclicIndexInterval N a r) :
    Riesz1.cyclicIndexDistance N i j < r := by
  have h := Finset.single_le_sum (s := Finset.univ) (a := a)
    (f := fun b : Fin (N : ℕ) =>
      (if i ∈ cyclicIndexInterval N b r then (1 : ℝ) else 0) *
      (if j ∈ cyclicIndexInterval N b r then (1 : ℝ) else 0))
    (fun b _ => by positivity) (Finset.mem_univ a)
  rw [cyclicIndexInterval_pair_count N hr] at h
  simp only [hi, hj, ↓reduceIte, one_mul] at h
  by_contra hn
  have hz : r - Riesz1.cyclicIndexDistance N i j = 0 := by omega
  simp only [hz, Nat.cast_zero] at h
  linarith

private theorem short_interval_mass_zero (n m : ℕ) (r : Fin ((n + m + 1) / 2))
    (a i : Fin (n + m + 1)) (hi : i.val < n)
    (hia : i ∈ cyclicIndexInterval (n + m).succPNat a (r.val + 1))
    (hr : r.val + 1 < min (i.val + 1) (n - i.val)) :
    (∑ b ∈ cyclicIndexInterval (n + m).succPNat a (r.val + 1),
      compensationVector n m b) = 0 := by
  apply Finset.sum_eq_zero
  intro b hb
  have hdist := interval_diameter (n + m).succPNat
    (by have := r.isLt; simp only [Nat.succPNat_coe]; omega) a i b hia hb
  have hactive : b.val < n := by
    by_contra hn
    have hbN := b.isLt
    simp only [Riesz1.cyclicIndexDistance, Nat.dist, Nat.succPNat_coe, Nat.succ_eq_add_one] at hdist
    simp only [Nat.succPNat_coe, Nat.succ_eq_add_one] at hbN
    omega
  simp only [compensationVector, hactive, ↓reduceIte]

private theorem interval_mass_bound (n m : ℕ) (hper : 2 * n ≤ n + m + 1)
    (r : Fin ((n + m + 1) / 2)) (a : Fin (n + m + 1)) :
    0 ≤ (∑ b ∈ cyclicIndexInterval (n + m).succPNat a (r.val + 1),
      compensationVector n m b) ∧
    (∑ b ∈ cyclicIndexInterval (n + m).succPNat a (r.val + 1),
      compensationVector n m b) ≤ 2 / (n + m + 1 : ℝ) * (r.val + 1 : ℝ) := by
  refine ⟨Finset.sum_nonneg (fun b _ => compensationVector_nonneg n m b), ?_⟩
  calc
    _ ≤ ∑ _b ∈ cyclicIndexInterval (n + m).succPNat a (r.val + 1),
        2 / (n + m + 1 : ℝ) :=
      Finset.sum_le_sum fun b _ => compensationVector_le n m hper b
    _ ≤ _ := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact_mod_cast (show (cyclicIndexInterval (n + m).succPNat a (r.val + 1)).card ≤ r.val + 1 from
        (Finset.card_image_le).trans_eq (Finset.card_range _))

/-- Internal finite-sum identity for the literal compensation contraction.
It applies before taking conditional expectations. -/
theorem particle_compensation_row_internal (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n m : ℕ) (i : Fin (n + m + 1))
    (X : Riesz1.Configuration (n + m).succPNat) :
    (∑ b, GoodBlocks.particleHessian (ofLong β s) (n + m).succPNat i b X *
      compensationVector n m b) =
    ∑ r : Fin ((n + m + 1) / 2), ∑ a : Fin (n + m + 1),
      if i ∈ cyclicIndexInterval (n + m).succPNat a (r.val + 1) then
        GoodBlocks.particleCoefficient (ofLong β s) (n + m).succPNat a.val
          (r.val + 1) (by omega) (by have := r.isLt; simpa only [Nat.succPNat_coe, Nat.succ_eq_add_one] using (Nat.succ_le_of_lt r.isLt)) X *
        (∑ b ∈ cyclicIndexInterval (n + m).succPNat a (r.val + 1),
          compensationVector n m b) else 0 := by
  simp only [GoodBlocks.particleHessian, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hi : i ∈ cyclicIndexInterval (n + m).succPNat a (r.val + 1)
  · simp only [hi, true_and, ↓reduceIte, Finset.mul_sum]
    simp_rw [ite_mul, zero_mul]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext b; simp
    · intro b hb
      rfl
  · simp only [hi, false_and, ↓reduceIte, zero_mul, Finset.sum_const_zero]

private theorem particle_increment_norm_internal {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Riesz1.RieszExponent) (n m : ℕ)
    (hper : 2 * n ≤ n + m + 1) {p B : ℝ} (hp : 1 ≤ p) (hB : 0 ≤ B)
    (F : Fin (n + m + 1) → Fin ((n + m + 1) / 2) → Ω → ℝ)
    (hF : ∀ a r, eLpNorm (F a r) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (B * (r.val + 1 : ℝ) ^ (-s.val - 2)))
    (i : Fin (n + m + 1)) (hi : i.val + 1 < n) :
    let R (k : Fin (n + m + 1)) (x : Ω) :=
      ∑ r : Fin ((n + m + 1) / 2), ∑ a : Fin (n + m + 1),
        if k ∈ cyclicIndexInterval (n + m).succPNat a (r.val + 1) then
          F a r x * (∑ b ∈ cyclicIndexInterval (n + m).succPNat a (r.val + 1),
            compensationVector n m b) else 0
    eLpNorm (fun x => R (i + 1) x - R i x) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (4 * B / (n + m + 1 : ℝ) * (1 + 1 / s.val) *
        (min (i.val + 1) (n - (i.val + 1)) : ℕ) ^ (-s.val)) := by
  classical
  dsimp only
  let N : ℕ+ := (n + m).succPNat
  let d := min (i.val + 1) (n - (i.val + 1))
  let w (r : Fin ((n + m + 1) / 2)) (a : Fin (n + m + 1)) :=
    ∑ b ∈ cyclicIndexInterval N a (r.val + 1), compensationVector n m b
  let S (r : Fin ((n + m + 1) / 2)) (a : Fin (n + m + 1)) (x : Ω) := F a r x * w r a
  let T (r : Fin ((n + m + 1) / 2)) (x : Ω) :=
    (∑ a, if i + 1 ∈ cyclicIndexInterval N a (r.val + 1) then S r a x else 0) -
    ∑ a, if i ∈ cyclicIndexInterval N a (r.val + 1) then S r a x else 0
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hnext : (i + 1).val = i.val + 1 :=
    Fin.val_add_one_of_lt' (by omega)
  have hS (r : Fin ((n + m + 1) / 2)) (a : Fin (n + m + 1)) :
      eLpNorm (S r a) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (2 * B / (n + m + 1 : ℝ) * (r.val + 1 : ℝ) ^ (-s.val - 1)) := by
    have hw := interval_mass_bound n m hper r a
    have he : S r a = w r a • F a r := by funext x; simp [S, mul_comm]
    rw [he, eLpNorm_const_smul, Real.enorm_eq_ofReal hw.1]
    apply (mul_le_mul le_rfl (hF a r) (by positivity) (by positivity)).trans
    rw [← ENNReal.ofReal_mul hw.1]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (2 / (n + m + 1 : ℝ) * (r.val + 1 : ℝ)) *
          (B * (r.val + 1 : ℝ) ^ (-s.val - 2)) :=
        mul_le_mul_of_nonneg_right hw.2 (by positivity)
      _ = _ := by
        rw [show -s.val - 1 = 1 + (-s.val - 2) by ring,
          Real.rpow_add (by positivity : (0 : ℝ) < r.val + 1), Real.rpow_one]
        ring
  have hT (r : Fin ((n + m + 1) / 2)) :
      eLpNorm (T r) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal
        (if (d : ℝ) ≤ (r.val + 1 : ℝ) then
          4 * B / (n + m + 1 : ℝ) * (r.val + 1 : ℝ) ^ (-s.val - 1) else 0) := by
    by_cases hlen : d ≤ r.val + 1
    · rw [ite_eq_left (by exact_mod_cast hlen)]
      have he : T r = S r (i + 1) - S r (i + 1 - ((r.val + 1 : ℕ) : Fin (n + m + 1))) := by
        funext x
        exact ExteriorForces.interval_row_increment N
          (by change r.val + 1 ≤ n + m + 1; have := r.isLt; omega) i (fun a => S r a x)
      rw [he]
      apply (eLpNorm_sub_le hpE).trans
      apply (add_le_add (hS r _) (hS r _)).trans_eq
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    · have hr : r.val + 1 < d := by omega
      rw [ite_eq_right (by exact_mod_cast (show ¬d ≤ r.val + 1 from hlen))]
      have he : T r = 0 := by
        funext x
        dsimp only [T]
        have hz (k : Fin (n + m + 1)) (hk : k.val < n)
            (hrk : r.val + 1 < min (k.val + 1) (n - k.val)) :
            (∑ a, if k ∈ cyclicIndexInterval N a (r.val + 1) then S r a x else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro a _
          split_ifs with ha
          · dsimp only [S, w, N]
            rw [short_interval_mass_zero n m r a k hk ha hrk, mul_zero]
          · rfl
        rw [hz i (by omega) (by dsimp [d] at hr; omega),
          hz (i + 1) (by rw [hnext]; omega) (by rw [hnext]; dsimp [d] at hr; omega)]
        exact sub_self 0
      rw [he, eLpNorm_zero, ENNReal.ofReal_zero]
  have he : (fun x =>
      (∑ r : Fin ((n + m + 1) / 2), ∑ a : Fin (n + m + 1),
        if i + 1 ∈ cyclicIndexInterval N a (r.val + 1) then S r a x else 0) -
      ∑ r : Fin ((n + m + 1) / 2), ∑ a : Fin (n + m + 1),
        if i ∈ cyclicIndexInterval N a (r.val + 1) then S r a x else 0) =
      fun x => ∑ r, T r x := by
    funext x
    simp only [T, Finset.sum_sub_distrib]
    rfl
  change eLpNorm (fun x =>
      (∑ r : Fin ((n + m + 1) / 2), ∑ a : Fin (n + m + 1),
        if i + 1 ∈ cyclicIndexInterval N a (r.val + 1) then S r a x else 0) -
      ∑ r : Fin ((n + m + 1) / 2), ∑ a : Fin (n + m + 1),
        if i ∈ cyclicIndexInterval N a (r.val + 1) then S r a x else 0) _ _ ≤ _
  rw [he]
  apply (show eLpNorm (fun x => ∑ r, T r x) (ENNReal.ofReal p) μ ≤
      ∑ r, eLpNorm (T r) (ENNReal.ofReal p) μ by
    simpa only [Finset.sum_fn] using eLpNorm_sum_le (f := T) (s := Finset.univ) hpE).trans
  apply (Finset.sum_le_sum fun r _ => hT r).trans
  rw [← ENNReal.ofReal_sum_of_nonneg (fun r _ => by split_ifs <;> positivity)]
  apply ENNReal.ofReal_le_ofReal
  have heq : (∑ r : Fin ((n + m + 1) / 2), if (d : ℝ) ≤ r.val + 1 then
      4 * B / (n + m + 1 : ℝ) * (r.val + 1 : ℝ) ^ (-s.val - 1) else 0) =
      (4 * B / (n + m + 1 : ℝ)) * ∑ r : Fin ((n + m + 1) / 2),
        if (d : ℝ) ≤ r.val + 1 then (r.val + 1 : ℝ) ^ (-(s.val + 1)) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    split_ifs
    · congr 2; ring
    · rw [mul_zero]
  rw [heq]
  have ht := BoundaryEntries.finite_length_tail_internal
    (by linarith [s.property.1] : 1 < s.val + 1)
    (by exact_mod_cast hd : (1 : ℝ) ≤ d) ((n + m + 1) / 2)
  simp only [show s.val + 1 - 1 = s.val by ring,
    show (1 : ℝ) - (s.val + 1) = -s.val by ring] at ht
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ht
    (by positivity : 0 ≤ 4 * B / (n + m + 1 : ℝ))

/-- See Lemma 5.7 in the paper, adjacent increment clause.
The constant is locally uniform in temperature. Its moment degree is exactly
`(s + 2) / s`, and the depth is the source depth of the left index. -/
theorem compensation_adjacent_moments (s : Riesz1.RieszExponent)
    (βlo βhi ε Cθ : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi)
    (hε : 0 < ε) (hCθ : 1 ≤ Cθ) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n : ℕ+) (m : ℕ), 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ (p : ℝ), 1 ≤ p →
      let μ := (activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n hn θ ε false).comap
        ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
          EuclideanSpace ℝ (Fin (n : ℕ)))
      ∀ i : Fin (n : ℕ), i.val + 1 < (n : ℕ) →
        eLpNorm (fun x => compensationB β s n m (i + 1) x - compensationB β s n m i x)
          (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (C * p ^ ((s.val + 2) / s.val) *
          ((n : ℝ) + m + 1)⁻¹ *
          (min (i.val + 1) ((n : ℕ) - i.val) : ℕ) ^ (-s.val)) := by
  obtain ⟨D, hD, hcoeff⟩ := GoodBlocks.tilted_coefficient_moments s.val βlo βhi ε Cθ
    s.property.1 hlo hle hε hCθ
  have hs : 0 < s.val := s.property.1
  refine ⟨4 * D * (1 + 1 / s.val) * 2 ^ s.val, by positivity, ?_⟩
  intro β hβ n m hper hn θ hcurv p hp
  dsimp only
  intro i hi
  let N : ℕ+ := ((n : ℕ) + m).succPNat
  let ρ := tiltedParticleMeasure (ofLong β s) N n hn θ ε false
  let u : Fin ((n : ℕ) + m + 1) := (i.castAdd m).castSucc
  let v : Fin ((n : ℕ) + m + 1) := ((i + 1).castAdd m).castSucc
  have hv : v = u + 1 := by
    apply Fin.ext
    change (i + 1).val = (u + 1).val
    rw [Fin.val_add_one_of_lt' hi,
      Fin.val_add_one_of_lt' (show u.val + 1 < (n : ℕ) + m + 1 by dsimp [u]; omega)]
    rfl
  let f := fun y : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) =>
    (∑ a, GoodBlocks.gapHessian s N v a y * compensationVector n m a) -
    ∑ a, GoodBlocks.gapHessian s N u a y * compensationVector n m a
  have hf : Measurable f :=
    (Finset.measurable_sum _ fun a _ => (GoodBlocks.measurable_gapHessian s N v a).mul_const _).sub
      (Finset.measurable_sum _ fun a _ => (GoodBlocks.measurable_gapHessian s N u a).mul_const _)
  have hj := conditional_gap_observable_eLpNorm_le β s n m hn θ ε f hf hp
  have he : (fun x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) =>
      ∫ z, f (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z))
        ∂ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x) =
      (fun x => compensationB β s n m (i + 1) x - compensationB β s n m i x) := by
    funext x
    exact integral_sub (integrable_compensationB β s n m (i + 1) x)
      (integrable_compensationB β s n m i x)
  rw [he] at hj
  apply hj.trans
  have hN : 2 ≤ (N : ℕ) := by dsimp [N]; have := n.pos; omega
  have hnorm := particle_increment_norm_internal ρ s n m hper hp
    (by positivity : 0 ≤ D * p ^ ((s.val + 2) / s.val))
    (fun a r => GoodBlocks.particleCoefficient (ofLong β s) N a.val (r.val + 1)
      (by omega) (by have := r.isLt; exact Nat.succ_le_of_lt r.isLt))
    (fun a r => by
      simpa only [Nat.cast_add, Nat.cast_one] using hcoeff (ofLong β s) rfl hβ.1 hβ.2 N n hN hn θ hcurv a.val
        (r.val + 1) (by omega) (by exact Nat.succ_le_of_lt r.isLt) p hp)
    u (by dsimp [u]; exact hi)
  have hrow (k : Fin ((n : ℕ) + m + 1)) (X : Riesz1.Configuration N) :=
    particle_compensation_row_internal β s n m k X
  have hfun : (fun X : Riesz1.Configuration N => f (WithLp.toLp 2 (gapVector X))) =
      (fun X : Riesz1.Configuration N =>
      (∑ r : Fin (((n : ℕ) + m + 1) / 2), ∑ a : Fin ((n : ℕ) + m + 1),
        if u + 1 ∈ cyclicIndexInterval N a (r.val + 1) then
          GoodBlocks.particleCoefficient (ofLong β s) N a.val (r.val + 1)
            (by omega) (by exact Nat.succ_le_of_lt r.isLt) X *
          (∑ b ∈ cyclicIndexInterval N a (r.val + 1), compensationVector n m b) else 0) -
      ∑ r : Fin (((n : ℕ) + m + 1) / 2), ∑ a : Fin ((n : ℕ) + m + 1),
        if u ∈ cyclicIndexInterval N a (r.val + 1) then
          GoodBlocks.particleCoefficient (ofLong β s) N a.val (r.val + 1)
            (by omega) (by exact Nat.succ_le_of_lt r.isLt) X *
          (∑ b ∈ cyclicIndexInterval N a (r.val + 1), compensationVector n m b) else 0) := by
    funext X
    simp only [f, GoodBlocks.gapHessian_particle β, hv]
    rw [hrow (u + 1), hrow u]
  rw [hfun]
  apply hnorm.trans
  apply ENNReal.ofReal_le_ofReal
  let d := min (i.val + 1) ((n : ℕ) - (i.val + 1))
  let δ := min (i.val + 1) ((n : ℕ) - i.val)
  have hd : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by dsimp [d]; omega)
  have hδ : 0 < (δ : ℝ) := by exact_mod_cast (show 0 < δ by dsimp [δ]; omega)
  have hcmp : (δ : ℝ) ≤ 2 * (d : ℝ) := by
    exact_mod_cast (show δ ≤ 2 * d by dsimp [δ, d]; omega)
  have hpow : (d : ℝ) ^ (-s.val) ≤ 2 ^ s.val * (δ : ℝ) ^ (-s.val) := by
    have hh := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < (δ : ℝ) / 2)
      ((div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by linarith : (δ : ℝ) ≤ d * 2))
      (neg_nonpos.mpr s.property.1.le)
    rw [Real.div_rpow hδ.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul] at hh
    simpa only [mul_comm] using hh
  have hmul := mul_le_mul_of_nonneg_left hpow
    (by positivity : 0 ≤ 4 * (D * p ^ ((s.val + 2) / s.val)) /
      ((n : ℝ) + m + 1) * (1 + 1 / s.val))
  dsimp only [u] at hnorm ⊢
  simpa only [d, δ, Fin.val_castSucc, Fin.val_castAdd, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Internal telescoping of moment bounds along a finite block. The depth
function is concave along the block, so its endpoint minimum controls the path. -/
theorem block_moment_telescoping_internal {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n : ℕ) [NeZero n] (f : Fin n → Ω → ℝ)
    {p M t : ℝ} (hp : 1 ≤ p) (hM : 0 ≤ M) (ht : 0 ≤ t)
    (hf : ∀ k : Fin n, k.val + 1 < n →
      eLpNorm (fun x => f (k + 1) x - f k x) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (M * (min (k.val + 1) (n - k.val) : ℕ) ^ (-t)))
    (j l : Fin n) :
    eLpNorm (fun x => f j x - f l x) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (M * (Nat.dist j.val l.val : ℝ) *
        (min (min (j.val + 1) (n - j.val)) (min (l.val + 1) (n - l.val)) : ℕ) ^ (-t)) := by
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have hordered (j l : Fin n) (hjl : j.val ≤ l.val) :
      eLpNorm (fun x => f j x - f l x) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (M * (Nat.dist j.val l.val : ℝ) *
          (min (min (j.val + 1) (n - j.val)) (min (l.val + 1) (n - l.val)) : ℕ) ^ (-t)) := by
    let d := min (min (j.val + 1) (n - j.val)) (min (l.val + 1) (n - l.val))
    let A := M * (d : ℝ) ^ (-t)
    have hd : 0 < (d : ℝ) := by
      exact_mod_cast (show 0 < d by dsimp [d]; have := j.isLt; have := l.isLt; omega)
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hstep (k : Fin n) (hjk : j.val ≤ k.val) (hkl : k.val < l.val) :
        eLpNorm (fun x => f (k + 1) x - f k x) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal A := by
      apply (hf k (by have := l.isLt; omega)).trans
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ hM
      apply Real.rpow_le_rpow_of_nonpos hd _ (neg_nonpos.mpr ht)
      exact_mod_cast (show d ≤ min (k.val + 1) (n - k.val) by dsimp [d]; omega)
    have hseq (q : ℕ) (hq : j.val + q ≤ l.val) :
        eLpNorm (fun x => f ⟨j.val + q, by have := l.isLt; omega⟩ x - f j x)
          (ENNReal.ofReal p) μ ≤ ENNReal.ofReal ((q : ℝ) * A) := by
      induction q with
      | zero => simp
      | succ q ih =>
        let k : Fin n := ⟨j.val + q, by have := l.isLt; omega⟩
        have hk : k.val + 1 < n := by dsimp [k]; have := l.isLt; omega
        have he : (⟨j.val + (q + 1), by have := l.isLt; omega⟩ : Fin n) = k + 1 := by
          apply Fin.ext
          rw [Fin.val_add_one_of_lt' hk]
          rfl
        rw [he]
        have heq : (fun x => f (k + 1) x - f j x) =
            (fun x => f (k + 1) x - f k x) + (fun x => f k x - f j x) := by
          funext x; simp only [Pi.add_apply]; ring
        rw [heq]
        apply (eLpNorm_add_le hpE).trans
        apply (add_le_add (hstep k (by dsimp [k]; omega) (by dsimp [k]; omega))
          (ih (by omega))).trans_eq
        rw [← ENNReal.ofReal_add hA (by positivity)]
        congr 1
        push_cast
        ring
    have h := hseq (l.val - j.val) (by omega)
    have he : (⟨j.val + (l.val - j.val), by have := l.isLt; omega⟩ : Fin n) = l := by
      apply Fin.ext
      exact Nat.add_sub_of_le hjl
    rw [he] at h
    have hneg : (fun x => f j x - f l x) = -(fun x => f l x - f j x) := by
      funext x; simp only [Pi.neg_apply]; ring
    rw [hneg, eLpNorm_neg, Nat.dist_eq_sub_of_le hjl]
    convert h using 1
    congr 1
    dsimp only [A, d]
    ring
  rcases le_total j.val l.val with h | h
  · exact hordered j l h
  · have he : (fun x => f j x - f l x) = -(fun x => f l x - f j x) := by
      funext x; simp only [Pi.neg_apply]; ring
    rw [he, eLpNorm_neg]
    simpa only [Nat.dist_comm l.val j.val, min_comm
      (min (l.val + 1) (n - l.val)) (min (j.val + 1) (n - j.val))] using hordered l j h

/-- See the proof of Lemma 5.8 in the paper, the `Q` difference clause.
Both endpoint depths are retained, with the moment degree of Part 1. -/
theorem compensationQ_increment_moments (s : Riesz1.RieszExponent)
    (βlo βhi ε Cθ : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi)
    (hε : 0 < ε) (hCθ : 1 ≤ Cθ) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n : ℕ+) (m : ℕ), 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ (p : ℝ), 1 ≤ p →
      let μ := (activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n hn θ ε false).comap
        ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
          EuclideanSpace ℝ (Fin (n : ℕ)))
      ∀ i j l : Fin (n : ℕ),
        eLpNorm (fun x => compensationQ β s n m i j x - compensationQ β s n m i l x)
          (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (C * p ^ ((s.val + 2) / s.val) * (Nat.dist j.val l.val : ℝ) *
          (min (i.val + 1) ((n : ℕ) - i.val) : ℕ) ^ (-s.val / 2) *
          (min (min (j.val + 1) ((n : ℕ) - j.val))
            (min (l.val + 1) ((n : ℕ) - l.val)) : ℕ) ^ (-1 - s.val / 2)) := by
  obtain ⟨C, hC, hstep⟩ := compensation_adjacent_moments s βlo βhi ε Cθ hlo hle hε hCθ
  refine ⟨C, hC, ?_⟩
  intro β hβ n m hper hn θ hcurv p hp
  dsimp only
  let μ := (activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n hn θ ε false).comap
    ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
  let M := C * p ^ ((s.val + 2) / s.val) * ((n : ℝ) + m + 1)⁻¹
  have hM : 0 ≤ M := by dsimp [M]; positivity
  intro i j l
  have htel := block_moment_telescoping_internal μ n (compensationB β s n m) hp hM s.property.1.le
    (hstep β hβ n m hper hn θ hcurv p hp) l j
  have he : (fun x => compensationQ β s n m i j x - compensationQ β s n m i l x) =
      (fun x => compensationB β s n m l x - compensationB β s n m j x) := by
    funext x
    exact compensationQ_sub β s n m i j l x
  rw [he]
  apply htel.trans
  apply ENNReal.ofReal_le_ofReal
  let a := min (i.val + 1) ((n : ℕ) - i.val)
  let d := min (min (j.val + 1) ((n : ℕ) - j.val)) (min (l.val + 1) ((n : ℕ) - l.val))
  let R : ℝ := (n : ℝ) + m + 1
  have ha : 0 < (a : ℝ) := by exact_mod_cast (show 0 < a by dsimp [a]; have := i.isLt; omega)
  have hd : 0 < (d : ℝ) := by
    exact_mod_cast (show 0 < d by dsimp [d]; have := j.isLt; have := l.isLt; omega)
  have hR : 0 < R := by dsimp [R]; positivity
  have haR : (a : ℝ) ≤ R := by
    dsimp [R]; exact_mod_cast (show a ≤ (n : ℕ) + m + 1 by dsimp [a]; omega)
  have hdR : (d : ℝ) ≤ R := by
    dsimp [R]; exact_mod_cast (show d ≤ (n : ℕ) + m + 1 by dsimp [d]; omega)
  have hpow : R⁻¹ * (d : ℝ) ^ (-s.val) ≤
      (a : ℝ) ^ (-s.val / 2) * (d : ℝ) ^ (-1 - s.val / 2) := by
    have h1 := Real.rpow_le_rpow_of_nonpos ha haR (by linarith [s.property.1] : -s.val / 2 ≤ 0)
    have h2 := Real.rpow_le_rpow_of_nonpos hd hdR (by linarith [s.property.2] : -1 + s.val / 2 ≤ 0)
    have hm := mul_le_mul h1 h2 (by positivity) (by positivity)
    rw [← Real.rpow_add hR, show -s.val / 2 + (-1 + s.val / 2) = -1 by ring,
      Real.rpow_neg_one] at hm
    have hh := mul_le_mul_of_nonneg_right hm (by positivity : 0 ≤ (d : ℝ) ^ (-s.val))
    rw [mul_assoc, ← Real.rpow_add hd,
      show -1 + s.val / 2 + -s.val = -1 - s.val / 2 by ring] at hh
    exact hh
  have hm := mul_le_mul_of_nonneg_left hpow
    (by positivity : 0 ≤ C * p ^ ((s.val + 2) / s.val) * (Nat.dist j.val l.val : ℝ))
  simpa only [M, a, d, R, Nat.dist_comm l.val j.val, min_comm
    (min (l.val + 1) ((n : ℕ) - l.val)) (min (j.val + 1) ((n : ℕ) - j.val)),
    mul_assoc, mul_left_comm, mul_comm] using hm

/-- See the proof of Lemma 5.8 in the paper, all four clauses with one
constant, quantified before temperature, sizes, indices, and moment exponent.
The law and coefficients are the literal physical objects of Part 1. -/
theorem compensation_moments (s : Riesz1.RieszExponent)
    (βlo βhi ε Cθ : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi)
    (hε : 0 < ε) (hCθ : 1 ≤ Cθ) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n : ℕ+) (m : ℕ), 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ (p : ℝ), 1 ≤ p →
      let μ := (activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n hn θ ε false).comap
        ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
          EuclideanSpace ℝ (Fin (n : ℕ)))
      (∀ i : Fin (n : ℕ),
        eLpNorm (compensationB β s n m i) (ENNReal.ofReal p) μ +
          eLpNorm (compensationC β s n m) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (C * p ^ ((s.val + 2) / s.val) * ((n : ℝ) + m + 1) ^ (-s.val))) ∧
      (∀ i : Fin (n : ℕ), i.val + 1 < (n : ℕ) →
        eLpNorm (fun x => compensationB β s n m (i + 1) x - compensationB β s n m i x)
          (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (C * p ^ ((s.val + 2) / s.val) * ((n : ℝ) + m + 1)⁻¹ *
          (min (i.val + 1) ((n : ℕ) - i.val) : ℕ) ^ (-s.val))) ∧
      (∀ i j : Fin (n : ℕ),
        eLpNorm (compensationQ β s n m i j) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (C * p ^ ((s.val + 2) / s.val) *
          (min (i.val + 1) ((n : ℕ) - i.val) : ℕ) ^ (-s.val / 2) *
          (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) ^ (-s.val / 2))) ∧
      (∀ i j l : Fin (n : ℕ),
        eLpNorm (fun x => compensationQ β s n m i j x - compensationQ β s n m i l x)
          (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (C * p ^ ((s.val + 2) / s.val) * (Nat.dist j.val l.val : ℝ) *
          (min (i.val + 1) ((n : ℕ) - i.val) : ℕ) ^ (-s.val / 2) *
          (min (min (j.val + 1) ((n : ℕ) - j.val))
            (min (l.val + 1) ((n : ℕ) - l.val)) : ℕ) ^ (-1 - s.val / 2))) := by
  obtain ⟨C₀, hC₀, h₀⟩ := compensation_size_moments s βlo βhi ε Cθ hlo hle hε hCθ
  obtain ⟨C₁, hC₁, h₁⟩ := compensation_adjacent_moments s βlo βhi ε Cθ hlo hle hε hCθ
  obtain ⟨C₂, hC₂, h₂⟩ := compensationQ_size_moments s βlo βhi ε Cθ hlo hle hε hCθ
  obtain ⟨C₃, hC₃, h₃⟩ := compensationQ_increment_moments s βlo βhi ε Cθ hlo hle hε hCθ
  refine ⟨C₀ + C₁ + C₂ + C₃, by positivity, ?_⟩
  intro β hβ n m hper hn θ hcurv p hp
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    apply (h₀ β hβ n m hper hn θ hcurv p hp i).trans
    apply ENNReal.ofReal_le_ofReal
    gcongr
    linarith
  · intro i hi
    apply (h₁ β hβ n m hper hn θ hcurv p hp i hi).trans
    apply ENNReal.ofReal_le_ofReal
    gcongr
    linarith
  · intro i j
    apply (h₂ β hβ n m hper hn θ hcurv p hp i j).trans
    apply ENNReal.ofReal_le_ofReal
    gcongr
    linarith
  · intro i j l
    apply (h₃ β hβ n m hper hn θ hcurv p hp i j l).trans
    apply ENNReal.ofReal_le_ofReal
    gcongr
    linarith

end Riesz2.ConditionalForces
