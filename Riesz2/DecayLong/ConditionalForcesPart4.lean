/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.ConditionalForcesPart3
public import Riesz2.Bridges.ConvexMeasureInputs
public import Riesz2.Bridges.LongRangeInputs

/-!
# Crossing quadratic forms for conditional forces

Both inequalities of equation (5.24) in the proof of Lemma 5.7, on the
physical conditional fibre. Periodic-image comparisons also provide inputs
to the sharper difference bound.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology BigOperators

namespace Riesz2.ConditionalForces

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- Internal square completion for the crossing-only Schur bound in
the proof of Lemma 5.7. Terms deleted from the energy annihilate the
exterior test direction. No invertibility of the crossing matrix is needed. -/
theorem crossing_variational_internal {ι : Type*} [Fintype ι]
    (w a b : ι → ℝ) (keep : ι → Prop) [DecidablePred keep]
    (hw : ∀ k, 0 ≤ w k) (hb : ∀ k, ¬keep k → b k = 0)
    {β : ℝ} (hβ : 0 < β) :
    2 * (∑ k, w k * (a k * b k)) - β * (∑ k, w k * (b k) ^ 2) ≤
      β⁻¹ * ∑ k, if keep k then w k * (a k) ^ 2 else 0 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : keep k
  · rw [ite_eq_left hk]
    have hs := mul_nonneg (hw k) (sq_nonneg (a k - β * b k))
    have hi := mul_nonneg (inv_nonneg.mpr hβ.le) hs
    have he : β⁻¹ * (w k * (a k - β * b k) ^ 2) =
        β⁻¹ * (w k * a k ^ 2) -
          (2 * (w k * (a k * b k)) - β * (w k * b k ^ 2)) := by
      field_simp
      ring
    linarith only [hi, he]
  · simp [hk, hb k hk]

/-- A finite crossing form remains nonnegative after compensation. This is
also the nonnegativity needed before passing from real to extended integrals. -/
theorem crossing_quadratic_nonneg_internal {ι : Type*} [Fintype ι]
    (w a : ι → ℝ) (keep : ι → Prop) [DecidablePred keep]
    (hw : ∀ k, 0 ≤ w k) :
    0 ≤ ∑ k, if keep k then w k * (a k) ^ 2 else 0 := by
  apply Finset.sum_nonneg
  intro k _
  split_ifs
  · exact mul_nonneg (hw k) (sq_nonneg _)
  · exact le_rfl

/-- Internal bridge from arbitrary directions to the actual interval matrix
of Subsection 5.1. It is an algebraic identity, so it holds before
restricting to the positive physical carrier. -/
theorem interval_bilinear_internal (s : Riesz1.RieszExponent) (N : ℕ+)
    (y u v : EuclideanSpace ℝ (Fin (N : ℕ))) :
    (∑ a, ∑ b, u a * GoodBlocks.gapHessian s N a b y * v b) =
      ∑ r : Fin ((N : ℕ) / 2), ∑ i : Fin (N : ℕ),
        BoundaryEntries.intervalWeight s N r i y *
          ((∑ a ∈ cyclicIndexInterval N i (r.val + 1), u a) *
            (∑ b ∈ cyclicIndexInterval N i (r.val + 1), v b)) := by
  classical
  let f := fun (a b : Fin (N : ℕ)) (r : Fin ((N : ℕ) / 2)) (i : Fin (N : ℕ)) =>
    u a * (if a ∈ cyclicIndexInterval N i (r.val + 1) ∧
      b ∈ cyclicIndexInterval N i (r.val + 1) then
        BoundaryEntries.intervalWeight s N r i y else 0) * v b
  calc
    _ = ∑ a, ∑ b, ∑ r, ∑ i, f a b r i := by
      simp only [f, BoundaryEntries.gapHessian_intervalWeight, Finset.mul_sum, Finset.sum_mul]
    _ = ∑ a, ∑ r, ∑ i, ∑ b, f a b r i := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
    _ = ∑ r, ∑ i, ∑ a, ∑ b, f a b r i := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro i _
      have hterm (a b : Fin (N : ℕ)) : f a b r i =
          if a ∈ cyclicIndexInterval N i (r.val + 1) then
            if b ∈ cyclicIndexInterval N i (r.val + 1) then
              BoundaryEntries.intervalWeight s N r i y * (u a * v b) else 0 else 0 := by
        dsimp only [f]
        split_ifs <;> simp_all
        all_goals ring
      simp_rw [hterm]
      simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_mem, Finset.univ_inter]
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum, Finset.sum_mul]

/-- Row version of the physical interval contraction identity. -/
theorem interval_row_internal (s : Riesz1.RieszExponent) (N : ℕ+)
    (y v : EuclideanSpace ℝ (Fin (N : ℕ))) (a : Fin (N : ℕ)) :
    (∑ b, GoodBlocks.gapHessian s N a b y * v b) =
      ∑ r : Fin ((N : ℕ) / 2), ∑ i : Fin (N : ℕ),
        BoundaryEntries.intervalWeight s N r i y *
          (if a ∈ cyclicIndexInterval N i (r.val + 1) then
            ∑ b ∈ cyclicIndexInterval N i (r.val + 1), v b else 0) := by
  classical
  have h := interval_bilinear_internal s N y (EuclideanSpace.single a 1) v
  simpa only [EuclideanSpace.single, PiLp.single_apply, Pi.single_apply,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    Finset.sum_ite_eq, mul_ite, mul_one] using h

/-- Internal compensation identity for a finite interval family. The vector
has zero active coordinates. Hence every deleted internal interval has zero
compensation mass. -/
theorem crossing_compensation_identity_internal {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (w : ι → ℝ) (J : ι → Finset κ) (I : Finset κ) (q : κ → ℝ)
    (hq : ∀ a ∈ I, q a = 0) (a : κ) :
    (∑ k, if ¬J k ⊆ I then
      w k * ((if a ∈ J k then 1 else 0) - ∑ b ∈ J k, q b) ^ 2 else 0) =
    (∑ k, if ¬J k ⊆ I ∧ a ∈ J k then w k else 0) -
      2 * (∑ k, w k * (if a ∈ J k then ∑ b ∈ J k, q b else 0)) +
      ∑ k, w k * (∑ b ∈ J k, q b) ^ 2 := by
  classical
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : J k ⊆ I
  · have hz : (∑ b ∈ J k, q b) = 0 :=
      Finset.sum_eq_zero (fun b hb => hq b (hk hb))
    simp [hk, hz]
  · by_cases ha : a ∈ J k <;> simp only [hk, ha, not_false_eq_true,
      and_self, and_false, ↓reduceIte] <;> ring

/-- Finite integration against the actual physical conditional law. The
coefficient multiplying each interval is deterministic on the fibre. -/
theorem integral_interval_sum_internal (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (c : Fin (((n : ℕ) + m + 1) / 2) → Fin ((n : ℕ) + m + 1) → ℝ) :
    Integrable (fun z => ∑ r, ∑ i,
      BoundaryEntries.intervalWeight s ((n : ℕ) + m).succPNat r i
        (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) * c r i)
      (ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x) ∧
    (∫ z, ∑ r, ∑ i,
      BoundaryEntries.intervalWeight s ((n : ℕ) + m).succPNat r i
        (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) * c r i
      ∂ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x) =
      ∑ r, ∑ i, BoundaryEntries.conditionalIntervalWeight β s n m r i x * c r i := by
  have hi (r i) := (BoundaryEntries.integrable_intervalWeight β s n m x r i).mul_const (c r i)
  refine ⟨integrable_finsetSum _ (fun r _ => integrable_finsetSum _ (fun i _ => hi r i)), ?_⟩
  let f : Fin (((n : ℕ) + m + 1) / 2) → Fin ((n : ℕ) + m + 1) →
      EuclideanSpace ℝ (Fin m) → ℝ := fun r i z =>
    BoundaryEntries.intervalWeight s ((n : ℕ) + m).succPNat r i
      (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) * c r i
  change (∫ z, ∑ r, ∑ i, f r i z ∂_) = _
  rw [integral_finsetSum Finset.univ
    (f := fun r z => ∑ i, f r i z)
    (fun r _ => integrable_finsetSum _ (fun i _ => hi r i))]
  apply Finset.sum_congr rfl
  intro r _
  rw [integral_finsetSum Finset.univ (f := fun i z => f r i z) (fun i _ => hi r i)]
  dsimp only [f]
  simp only [integral_mul_const, BoundaryEntries.conditionalIntervalWeight]

/-- See Subsection 5.1 of the paper: the actual row compensation is the interval
coefficient contracted against the exterior mass of the interval. -/
theorem compensationB_intervals (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (i : Fin (n : ℕ))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    compensationB β s n m i x =
      ∑ r, ∑ a, BoundaryEntries.conditionalIntervalWeight β s n m r a x *
        (if (i.castAdd m).castSucc ∈
            cyclicIndexInterval ((n : ℕ) + m).succPNat a (r.val + 1) then
          ∑ b ∈ cyclicIndexInterval ((n : ℕ) + m).succPNat a (r.val + 1),
            compensationVector n m b else 0) := by
  unfold compensationB
  apply Eq.trans _ (integral_interval_sum_internal β s n m x _).2
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  exact interval_row_internal s ((n : ℕ) + m).succPNat
    (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z))
    (WithLp.toLp 2 (compensationVector n m)) (i.castAdd m).castSucc

/-- See Subsection 5.1 of the paper: the quadratic compensation averages the square
of the exterior mass of each physical interval. -/
theorem compensationC_intervals (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    compensationC β s n m x =
      ∑ r, ∑ a, BoundaryEntries.conditionalIntervalWeight β s n m r a x *
        (∑ b ∈ cyclicIndexInterval ((n : ℕ) + m).succPNat a (r.val + 1),
          compensationVector n m b) ^ 2 := by
  unfold compensationC
  apply Eq.trans _ (integral_interval_sum_internal β s n m x _).2
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  have he := interval_bilinear_internal s ((n : ℕ) + m).succPNat
    (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z))
    (WithLp.toLp 2 (compensationVector n m)) (WithLp.toLp 2 (compensationVector n m))
  simp only [← pow_two] at he
  convert he using 1
  rfl

/-- Exact crossing expansion in the proof of Lemma 5.7.
This identifies the averaged crossing-only compensated quadratic form
with the right side of the first variance inequality. -/
theorem compensated_crossing_intervals (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ) (i : Fin (n : ℕ))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    (∑ r, ∑ a, if ¬cyclicIndexInterval ((n : ℕ) + m).succPNat a (r.val + 1) ⊆
          BoundaryEntries.activeIndices ((n : ℕ) + m).succPNat n then
        BoundaryEntries.conditionalIntervalWeight β s n m r a x *
          ((if (i.castAdd m).castSucc ∈
              cyclicIndexInterval ((n : ℕ) + m).succPNat a (r.val + 1) then 1 else 0) -
            ∑ b ∈ cyclicIndexInterval ((n : ℕ) + m).succPNat a (r.val + 1),
              compensationVector n m b) ^ 2 else 0) =
      BoundaryEntries.physicalCrossing β s n m x i i -
        2 * compensationB β s n m i x + compensationC β s n m x := by
  classical
  rw [compensationB_intervals, compensationC_intervals]
  have hq (a : Fin ((n : ℕ) + m + 1))
      (ha : a ∈ BoundaryEntries.activeIndices ((n : ℕ) + m).succPNat n) :
      compensationVector n m a = 0 := by
    simp only [BoundaryEntries.activeIndices, Finset.mem_filter, Finset.mem_univ,
      true_and] at ha
    simp only [compensationVector, ha, ↓reduceIte]
  have h := crossing_compensation_identity_internal
    (fun k : Fin (((n : ℕ) + m + 1) / 2) × Fin ((n : ℕ) + m + 1) =>
      BoundaryEntries.conditionalIntervalWeight β s n m k.1 k.2 x)
    (fun k => cyclicIndexInterval ((n : ℕ) + m).succPNat k.2 (k.1.val + 1))
    (BoundaryEntries.activeIndices ((n : ℕ) + m).succPNat n)
    (compensationVector n m) hq (i.castAdd m).castSucc
  simp only [Fintype.sum_prod_type] at h
  convert h using 1
  all_goals simp [BoundaryEntries.physicalCrossing, and_self]

/-- The compensated crossing form in equation (5.24) is nonnegative, including
point exterior fibres and retained indices at either boundary. -/
theorem compensated_crossing_nonneg (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ) (i : Fin (n : ℕ))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    0 ≤ BoundaryEntries.physicalCrossing β s n m x i i -
      2 * compensationB β s n m i x + compensationC β s n m x := by
  rw [← compensated_crossing_intervals]
  apply Finset.sum_nonneg
  intro r _
  apply Finset.sum_nonneg
  intro a _
  have hw := BoundaryEntries.conditionalIntervalWeight_nonneg β s n m r a x
  split_ifs <;> positivity

/-- Internal identification of the Hessian of any realization of beta times
the energy. The expression uses the existing physical interval
coefficients, and includes arbitrary ambient directions. -/
theorem physical_hessian_intervals_internal (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (N : ℕ+)
    (U : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ)
    (hU : ∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) //
        y ∈ gapAmbientDomain N},
      U y.val = β.val * physicalAmbientGapEnergy (ofLong β s) N y)
    (y : EuclideanSpace ℝ (Fin (N : ℕ)))
    (hy : WithLp.ofLp y ∈ Riesz1.gapSimplex N)
    (u v : EuclideanSpace ℝ (Fin (N : ℕ))) :
    fderiv ℝ (fderiv ℝ U) y u v = β.val *
      ∑ r : Fin ((N : ℕ) / 2), ∑ i : Fin (N : ℕ),
        BoundaryEntries.intervalWeight s N r i y *
          ((∑ a ∈ cyclicIndexInterval N i (r.val + 1), u a) *
            (∑ b ∈ cyclicIndexInterval N i (r.val + 1), v b)) := by
  obtain ⟨W, hW, hv, hjet⟩ := PhysicalEnergy.ambient_derivatives (ofLong β s) N
  have hyA := PhysicalEnergy.simplex_subset_ambient N _ hy
  have he : U =ᶠ[𝓝 y] fun z => β.val * W z := by
    filter_upwards [(PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hyA] with z hz
    rw [hU ⟨z,hz⟩, hv ⟨z,hz⟩]
  rw [he.fderiv.fderiv_eq, PhysicalCollision.internal_hessian_const_mul
    ((hW.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hyA)).of_le
      (by norm_num))]
  rw [(hjet ⟨y,hyA⟩ u v).2, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  rw [BoundaryEntries.intervalWeight_physical β s N r i y hy]
  rw [BoundaryEntries.gapSum_eq_interval_sum N i
    ((Nat.succ_le_of_lt r.isLt).trans (Nat.div_le_self _ _)) (WithLp.ofLp u),
    BoundaryEntries.gapSum_eq_interval_sum N i
      ((Nat.succ_le_of_lt r.isLt).trans (Nat.div_le_self _ _)) (WithLp.ofLp v)]

/-- Pointwise crossing-only Schur bound from the proof of Lemma 5.7, for the literal ambient compensated direction.
An exterior test direction vanishes on active gaps, so internal intervals
annihilate it exactly. -/
theorem physical_crossing_variational_internal (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (U : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ)
    (hU : ∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) //
        y ∈ gapAmbientDomain ((n : ℕ) + m).succPNat},
      U y.val = β.val * physicalAmbientGapEnergy (ofLong β s) ((n : ℕ) + m).succPNat y)
    (y : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)))
    (hy : WithLp.ofLp y ∈ Riesz1.gapSimplex ((n : ℕ) + m).succPNat)
    (i : Fin (n : ℕ)) (h : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)))
    (hh : ∀ a : Fin (n : ℕ), h (a.castAdd m).castSucc = 0) :
    let d := EuclideanSpace.single (i.castAdd m).castSucc (1 : ℝ) -
      WithLp.toLp 2 (compensationVector n m)
    2 * (β.val⁻¹ * fderiv ℝ (fderiv ℝ U) y d h) -
      fderiv ℝ (fderiv ℝ U) y h h ≤
      β.val⁻¹ * ∑ r : Fin (((n : ℕ) + m + 1) / 2), ∑ a : Fin ((n : ℕ) + m + 1),
        if ¬cyclicIndexInterval ((n : ℕ) + m).succPNat a (r.val + 1) ⊆
            BoundaryEntries.activeIndices ((n : ℕ) + m).succPNat n then
          BoundaryEntries.intervalWeight s ((n : ℕ) + m).succPNat r a y *
            ((if (i.castAdd m).castSucc ∈
                cyclicIndexInterval ((n : ℕ) + m).succPNat a (r.val + 1) then 1 else 0) -
              ∑ b ∈ cyclicIndexInterval ((n : ℕ) + m).succPNat a (r.val + 1),
                compensationVector n m b) ^ 2 else 0 := by
  classical
  intro d
  let N := ((n : ℕ) + m).succPNat
  let J := fun k : Fin (((n : ℕ) + m + 1) / 2) × Fin ((n : ℕ) + m + 1) =>
    cyclicIndexInterval N k.2 (k.1.val + 1)
  let w := fun k : Fin (((n : ℕ) + m + 1) / 2) × Fin ((n : ℕ) + m + 1) =>
    BoundaryEntries.intervalWeight s N k.1 k.2 y
  let a := fun k => ∑ b ∈ J k, d b
  let b := fun k => ∑ c ∈ J k, h c
  have hsum (k) : a k =
      (if (i.castAdd m).castSucc ∈ J k then 1 else 0) -
        ∑ b ∈ J k, compensationVector n m b := by
    simp only [a, d, PiLp.sub_apply, Finset.sum_sub_distrib,
      EuclideanSpace.single, PiLp.single_apply, Finset.sum_ite_eq']
  have hz (k) (hk : ¬¬J k ⊆ BoundaryEntries.activeIndices N n) : b k = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    have hcn : c.val < (n : ℕ) := by
      simpa only [BoundaryEntries.activeIndices, Finset.mem_filter, Finset.mem_univ,
        true_and] using (not_not.mp hk) hc
    let c' : Fin (n : ℕ) := ⟨c.val, hcn⟩
    have he : c = (c'.castAdd m).castSucc := Fin.ext rfl
    rw [he]
    exact hh c'
  have H := crossing_variational_internal w a b
    (fun k => ¬J k ⊆ BoundaryEntries.activeIndices N n)
    (fun k => BoundaryEntries.intervalWeight_nonneg β s N k.1 k.2 y hy)
    hz β.property
  have Hd := physical_hessian_intervals_internal β s N U hU y hy d h
  have Hh := physical_hessian_intervals_internal β s N U hU y hy h h
  convert H using 1
  · erw [Hd, Hh]
    simp only [a, b, w, J, Fintype.sum_prod_type, pow_two]
    field_simp [β.property.ne']
    rfl
  · simp only [Fintype.sum_prod_type, hsum, J, w, N]

/-- The original retained/exterior chart is affine in the exterior
coordinates. Its derivative vanishes on the retained gaps and expands
Euclidean norms. This fixes the metric used in the conditional Brascamp–Lieb step. -/
theorem exterior_chart_affine_internal (n m : ℕ) (L : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ∃ A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin (n + m + 1)),
      (∀ z, RetainedSimplex.chart n m L (Equiv.refl _) (x,z) =
        A z + RetainedSimplex.chart n m L (Equiv.refl _) (x,0)) ∧
      (∀ h (i : Fin n), A h (i.castAdd m).castSucc = 0) ∧
      ∀ h, ‖h‖ ^ 2 ≤ ‖A h‖ ^ 2 := by
  have : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :=
    Prod.continuousSMul
  let J := (RetainedSimplex.join n m).toContinuousLinearEquiv.toContinuousLinearMap
  let A := (AffineSimplex.tangentMap (n + m)).toContinuousLinearMap.comp
    (J.comp (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin m))))
  refine ⟨A, ?_, ?_, ?_⟩
  · intro z
    have hj : (RetainedSimplex.join n m) (x,z) =
        (RetainedSimplex.join n m) (0,z) + (RetainedSimplex.join n m) (x,0) := by
      rw [← map_add]
      congr 1
      simp
    have he (v : EuclideanSpace ℝ (Fin (n + m + 1))) :
        LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.refl _) v = v := by
      ext i
      rfl
    simp only [RetainedSimplex.chart, he]
    rw [AffineSimplex.chart_eq_tangentMap_add (n + m) L ((RetainedSimplex.join n m) (x,z)),
      AffineSimplex.chart_eq_tangentMap_add (n + m) L ((RetainedSimplex.join n m) (x,0)),
      hj, map_add]
    exact add_assoc _ _ _
  · intro h i
    change AffineSimplex.chart (n + m) 0 ((RetainedSimplex.join n m) (0,h))
      (i.castAdd m).castSucc = 0
    rw [AffineSimplex.chart_castSucc, RetainedSimplex.join_left]
    rfl
  · intro h
    have ht := AffineSimplex.norm_tangentMap_sq (n + m)
      ((RetainedSimplex.join n m) (0,h))
    have hj : ‖(RetainedSimplex.join n m) (0,h)‖ ^ 2 = ‖h‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
        Fin.sum_univ_add]
      simp only [RetainedSimplex.join_left, RetainedSimplex.join_right,
        PiLp.zero_apply, zero_pow (by norm_num : 2 ≠ 0), Finset.sum_const_zero, zero_add]
    change ‖h‖ ^ 2 ≤ ‖AffineSimplex.tangentMap (n + m)
      ((RetainedSimplex.join n m) (0,h))‖ ^ 2
    rw [ht, hj]
    linarith [sq_nonneg (∑ i, (RetainedSimplex.join n m) (0,h) i)]

/-- Uniform positive curvature at fixed volume, for every realization of
beta times the physical energy. No lower bound on the smallest gap is
assumed. All negative powers have strictly positive arguments. -/
theorem physical_hessian_lower_internal (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (U : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ)
    (hU : ∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
      U y.val = β.val * physicalAmbientGapEnergy (ofLong β s) N y)
    (y : EuclideanSpace ℝ (Fin (N : ℕ)))
    (hy : WithLp.ofLp y ∈ Riesz1.gapSimplex N)
    (u : EuclideanSpace ℝ (Fin (N : ℕ))) :
    (β.val * (s.val * (s.val + 1)) * (N : ℝ) ^ (-s.val - 2)) * ‖u‖ ^ 2 ≤
      fderiv ℝ (fderiv ℝ U) y u u := by
  obtain ⟨W,hW,hv,_,_,hlow,_,_⟩ :=
    (PhysicalEnergy.restriction_and_derivatives (ofLong β s) N hN).2.2
  have hyA := PhysicalEnergy.simplex_subset_ambient N _ hy
  have he : U =ᶠ[𝓝 y] fun z => β.val * W z := by
    filter_upwards [(PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hyA] with z hz
    rw [hU ⟨z,hz⟩, hv ⟨z,hz⟩]
  rw [he.fderiv.fderiv_eq, PhysicalCollision.internal_hessian_const_mul
    ((hW.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hyA)).of_le
      (by norm_num))]
  have h := mul_le_mul_of_nonneg_left (hlow (WithLp.ofLp y) hy u) β.property.le
  have hsum : (N : ℝ) ^ (-s.val - 2) * ‖u‖ ^ 2 ≤
      ∑ i, y i ^ (-s.val - 2) * (u i) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply Real.rpow_le_rpow_of_nonpos (hy.1 i) _ (by linarith [s.property.1])
    exact (Finset.single_le_sum (fun j _ => (hy.1 j).le) (Finset.mem_univ i)).trans_eq hy.2
  change β.val * (s.val * (s.val + 1) *
    (∑ i, y i ^ (-s.val - 2) * (u i) ^ 2)) ≤ _ at h
  have hp : 0 ≤ β.val * (s.val * (s.val + 1)) :=
    mul_nonneg β.property.le (mul_nonneg s.property.1.le (by linarith [s.property.1]))
  have hs := mul_le_mul_of_nonneg_left hsum hp
  nlinarith only [h, hs]

/-- Identification of the density-defined physical conditional with the
normalized exponential required by the library Brascamp--Lieb theorem. -/
theorem physical_conditional_density_internal (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (U : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ)
    (hU : ∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
        y ∈ gapAmbientDomain (n + m).succPNat},
      U y.val = p.val.1 * physicalAmbientGapEnergy p (n + m).succPNat y)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    let Q := AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ i, x.val i)
    let V := fun z => U (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z))
    ProperMarginalChart.conditionalMeasure p n m hn (Equiv.refl _) x =
      (volume.restrict Q).withDensity
        (fun z => ENNReal.ofReal (Real.exp (-V z) / ∫ y in Q, Real.exp (-V y))) := by
  classical
  intro Q V
  have hQ : MeasurableSet Q := (AffineSimplex.isOpen_chartDomain m _).measurableSet
  have hd : (fun z => ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x.val,z)) =
      Q.indicator (fun z => ENNReal.ofReal (Real.exp (-V z))) := by
    funext z
    have hmem := Set.ext_iff.mp (RetainedSimplex.fibre_domain n m
      ((n + m : ℕ) + 1) x.property) z
    by_cases hz : z ∈ Q
    · have hq : (x.val,z) ∈ RetainedSimplex.domain n m ((n + m : ℕ) + 1) := hmem.mpr hz
      have hs := (RetainedSimplex.chart_mem_simplex n m ((n + m : ℕ) + 1)
        (Equiv.refl _) (x.val,z)).mpr hq
      simp only [ProperMarginalChart.chartDensity, indicator_of_mem hq,
        ProperMarginalChart.density, dite_eq_left hs, indicator_of_mem hz]
      rw [show V z = p.val.1 * physicalAmbientGapEnergy p (n + m).succPNat
        ⟨_, ProperMarginalChart.simplex_ambient _ hs⟩ from
          hU ⟨_, ProperMarginalChart.simplex_ambient _ hs⟩]
      congr 2
      ring
    · have hq : (x.val,z) ∉ RetainedSimplex.domain n m ((n + m : ℕ) + 1) :=
        fun h => hz (hmem.mp h)
      simp only [ProperMarginalChart.chartDensity, indicator_of_notMem hq,
        indicator_of_notMem hz]
  obtain ⟨h0,ht⟩ := ProperMarginalChart.fibre_mass p n m hn (Equiv.refl _) x.property
  change (∫⁻ z, ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x.val,z)) ≠ 0 at h0
  change (∫⁻ z, ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x.val,z)) ≠ ⊤ at ht
  rw [hd, lintegral_indicator hQ] at h0 ht
  have hρ : ProperMarginalChart.conditionalMeasure p n m hn (Equiv.refl _) x =
      AffineFibre.normalizedMeasure (volume.restrict Q)
        (fun z => ENNReal.ofReal (Real.exp (-V z))) h0 ht := by
    unfold ProperMarginalChart.conditionalMeasure
    simp only [hd]
    exact AffineFibre.normalizedMeasure_indicator volume hQ _ h0 ht
  have hm : AEMeasurable (fun z => ENNReal.ofReal (Real.exp (-V z))) (volume.restrict Q) := by
    have hw0 : AEMeasurable
        (fun z => ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x.val,z)) volume :=
      ((ProperMarginalChart.measurable_chartDensity p n m (Equiv.refl _)).comp
        measurable_prodMk_left).aemeasurable
    have hw := hw0.restrict (s := Q)
    rw [hd] at hw
    apply hw.congr
    filter_upwards [ae_restrict_mem hQ] with z hz
    exact indicator_of_mem hz _
  have hZ := integral_toReal hm (ae_of_all _ (fun z => ENNReal.ofReal_lt_top))
  simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hZ
  have hZpos : 0 < ∫ z in Q, Real.exp (-V z) := by
    rw [hZ]
    exact ENNReal.toReal_pos h0 ht
  have hmass : (∫⁻ z in Q, ENNReal.ofReal (Real.exp (-V z))) =
      ENNReal.ofReal (∫ z in Q, Real.exp (-V z)) := by
    rw [hZ, ENNReal.ofReal_toReal ht]
  rw [hρ]
  unfold AffineFibre.normalizedMeasure AffineFibre.normalizedDensity
  rw [hmass]
  congr 1
  funext z
  rw [← ENNReal.ofReal_inv_of_pos hZpos,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hZpos.le), div_eq_inv_mul]

/-- Chain-rule step for the physical force: a constant ambient score
pulled back by an affine fibre has the contracted ambient Hessian as its
actual derivative. -/
theorem affine_score_gradient_internal {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (A : F →L[ℝ] E) (c d : E) (b : ℝ) (U : E → ℝ) (z h : F)
    (hU : ContDiffAt ℝ 2 U (A z + c)) :
    inner ℝ (gradient (fun y => b * fderiv ℝ U (A y + c) d) z) h =
      b * fderiv ℝ (fderiv ℝ U) (A z + c) d (A h) := by
  have hD := ((hU.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp z (A.hasFDerivAt.add_const c)
  have hF := (hD.clm_apply (hasFDerivAt_const d z)).const_mul b
  rw [inner_gradient_left]
  erw [hF.fderiv]
  simp only [smul_apply, add_apply,
    ContinuousLinearMap.comp_apply, zero_apply, map_zero,
    zero_add, ContinuousLinearMap.flip_apply, smul_eq_mul]
  rw [hU.isSymmSndFDerivAt (by norm_num) (A h) d]

/-- The physical crossing majorant is integrable, and its expectation is
exactly the compensated crossing form in equation (5.24). -/
theorem compensated_crossing_integral (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ) (i : Fin (n : ℕ))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    let B := fun z => ∑ r : Fin (((n : ℕ) + m + 1) / 2), ∑ a : Fin ((n : ℕ) + m + 1),
      if ¬cyclicIndexInterval ((n : ℕ) + m).succPNat a (r.val + 1) ⊆
          BoundaryEntries.activeIndices ((n : ℕ) + m).succPNat n then
        BoundaryEntries.intervalWeight s ((n : ℕ) + m).succPNat r a
          (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) *
          ((if (i.castAdd m).castSucc ∈
              cyclicIndexInterval ((n : ℕ) + m).succPNat a (r.val + 1) then 1 else 0) -
            ∑ b ∈ cyclicIndexInterval ((n : ℕ) + m).succPNat a (r.val + 1),
              compensationVector n m b) ^ 2 else 0
    let μ := ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x
    Integrable B μ ∧ (∫ z, B z ∂μ) =
      BoundaryEntries.physicalCrossing β s n m x i i -
        2 * compensationB β s n m i x + compensationC β s n m x := by
  classical
  intro B μ
  let c := fun (r : Fin (((n : ℕ) + m + 1) / 2)) (a : Fin ((n : ℕ) + m + 1)) =>
    if ¬cyclicIndexInterval ((n : ℕ) + m).succPNat a (r.val + 1) ⊆
        BoundaryEntries.activeIndices ((n : ℕ) + m).succPNat n then
      ((if (i.castAdd m).castSucc ∈
          cyclicIndexInterval ((n : ℕ) + m).succPNat a (r.val + 1) then 1 else 0) -
        ∑ b ∈ cyclicIndexInterval ((n : ℕ) + m).succPNat a (r.val + 1),
          compensationVector n m b) ^ 2 else 0
  have hi := integral_interval_sum_internal β s n m x c
  have he : B = fun z => ∑ r, ∑ a,
      BoundaryEntries.intervalWeight s ((n : ℕ) + m).succPNat r a
        (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) * c r a := by
    funext z
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro a _
    dsimp only [c]
    split_ifs <;> simp
  refine ⟨he ▸ hi.1, ?_⟩
  rw [he, hi.2, ← compensated_crossing_intervals]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro a _
  dsimp only [c]
  split_ifs <;> simp

/-- Internal physical Brascamp–Lieb application. The observable graph certificate is
supplied here only to separate the analytic assembly. The final
theorem below obtains it from the proved physical score theorem. -/
theorem physical_force_variance_internal (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (U : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ)
    (hUs : ContDiffOn ℝ ∞ U (gapAmbientDomain ((n : ℕ) + m).succPNat))
    (hUv : ∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) //
        y ∈ gapAmbientDomain ((n : ℕ) + m).succPNat},
      U y.val = β.val * physicalAmbientGapEnergy (ofLong β s) ((n : ℕ) + m).succPNat y)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (i : Fin (n : ℕ))
    (hF : let d := EuclideanSpace.single (i.castAdd m).castSucc (1 : ℝ) -
        WithLp.toLp 2 (compensationVector n m)
      let F := fun z => β.val⁻¹ * fderiv ℝ U
        (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) d
      Riesz1.WeightedSobolev.IsWeightedH1
        (ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x)
        (AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ a, x.val a)) F (gradient F)) :
    let d := EuclideanSpace.single (i.castAdd m).castSucc (1 : ℝ) -
      WithLp.toLp 2 (compensationVector n m)
    let F := fun z => β.val⁻¹ * fderiv ℝ U
      (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) d
    let μ := ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x
    (∫ z, (F z - ∫ y, F y ∂μ) ^ 2 ∂μ) ≤
      β.val⁻¹ * (BoundaryEntries.physicalCrossing β s n m x i i -
        2 * compensationB β s n m i x + compensationC β s n m x) := by
  classical
  intro d F μ
  have : IsProbabilityMeasure μ :=
    ProperMarginalChart.conditionalMeasure_probability (ofLong β s) n m n.pos (Equiv.refl _) x
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [variance_eq_zero_of_subsingleton μ F]
    exact mul_nonneg (inv_nonneg.mpr β.property.le) (compensated_crossing_nonneg β s n 0 i x)
  let N := ((n : ℕ) + m).succPNat
  let Q := AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ a, x.val a)
  let c := fun z => RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)
  let V := fun z => U (c z)
  have hQ : IsOpen Q := AffineSimplex.isOpen_chartDomain _ _
  have hs (z) (hz : z ∈ Q) : WithLp.ofLp (c z) ∈ Riesz1.gapSimplex N := by
    have hd := (Set.ext_iff.mp (RetainedSimplex.fibre_domain n m _ x.property) z).mpr hz
    have hy := (RetainedSimplex.chart_mem_simplex n m _ (Equiv.refl _) _).mpr hd
    exact ⟨hy.1, by simpa only [N, c, Nat.succPNat_coe, Nat.cast_succ] using hy.2⟩
  have hA (z) (hz : z ∈ Q) : c z ∈ gapAmbientDomain N :=
    PhysicalEnergy.simplex_subset_ambient N _ (hs z hz)
  obtain ⟨A, hc, hactive, hnorm⟩ := exterior_chart_affine_internal n m ((n + m : ℕ) + 1) x.val
  have hce : c = fun z => A z + c 0 := funext hc
  have hUat (z) (hz : z ∈ Q) : ContDiffAt ℝ 2 U (A z + c 0) := by
    rw [← hc]
    exact (hUs.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds
      (hA z hz))).of_le (by norm_num)
  have hV : ContDiffOn ℝ 2 V Q := by
    apply (hUs.of_le (by norm_num)).comp _ hA
    rw [hce]
    exact (A.contDiff.add contDiff_const).contDiffOn
  have hH (z) (hz : z ∈ Q) (h) : fderiv ℝ (fderiv ℝ V) z h h =
      fderiv ℝ (fderiv ℝ U) (c z) (A h) (A h) := by
    dsimp only [V]
    rw [hce]
    exact AffineMetricTransport.hessian_comp_affine A (c 0) (hUat z hz) h h
  let κ := β.val * (s.val * (s.val + 1)) * (N : ℝ) ^ (-s.val - 2)
  have hκ : 0 < κ := by
    have hβ := β.property
    have hsp := s.property.1
    have hNp : (0 : ℝ) < N := by exact_mod_cast N.pos
    dsimp only [κ]
    positivity
  have hlow (z) (hz : z ∈ Q) (h) : κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) z h h := by
    rw [hH z hz]
    exact (mul_le_mul_of_nonneg_left (hnorm h) hκ.le).trans
      (physical_hessian_lower_internal β s N (by dsimp [N]; have := n.pos; omega)
        U hUv (c z) (hs z hz) (A h))
  have hne : Q.Nonempty := by
    have hximage : x.val ∈ Prod.fst '' RetainedSimplex.domain n m ((n + m : ℕ) + 1) := by
      rw [RetainedSimplex.fst_image_domain]
      exact x.property
    obtain ⟨⟨a,z⟩, hz, he⟩ := hximage
    change a = x.val at he
    subst a
    exact ⟨z, (Set.ext_iff.mp (RetainedSimplex.fibre_domain n m _ x.property) z).mp hz⟩
  have hμ := physical_conditional_density_internal (ofLong β s) n m n.pos U hUv x
  have hBL := euclidean_brascamp_lieb hm (AffineSimplex.isBounded_chartDomain m _) hQ hne
    (AffineSimplex.convex_chartDomain m _) hV hκ hlow μ hμ
  obtain ⟨hvar, hint, _⟩ := hBL.2.2.2.1 F (gradient F) hF
  let B := fun z => ∑ r : Fin (((n : ℕ) + m + 1) / 2), ∑ a : Fin ((n : ℕ) + m + 1),
    if ¬cyclicIndexInterval N a (r.val + 1) ⊆ BoundaryEntries.activeIndices N n then
      BoundaryEntries.intervalWeight s N r a (c z) *
        ((if (i.castAdd m).castSucc ∈ cyclicIndexInterval N a (r.val + 1) then 1 else 0) -
          ∑ b ∈ cyclicIndexInterval N a (r.val + 1), compensationVector n m b) ^ 2 else 0
  have hBi := compensated_crossing_integral β s n m i x
  change Integrable B μ ∧ (∫ z, B z ∂μ) = _ at hBi
  have hgrad (z) (hz : z ∈ Q) (h) : inner ℝ (gradient F z) h =
      β.val⁻¹ * fderiv ℝ (fderiv ℝ U) (c z) d (A h) := by
    have heF : F = fun z => β.val⁻¹ * fderiv ℝ U (A z + c 0) d := by
      funext z
      rw [← hc]
    rw [heF, show c z = A z + c 0 from hc z]
    exact affine_score_gradient_internal A (c 0) d β.val⁻¹ U z h (hUat z hz)
  have hbound : ∀ᵐ z ∂μ,
      sSup (Set.range fun h => 2 * inner ℝ (gradient F z) h -
        fderiv ℝ (fderiv ℝ V) z h h) ≤ β.val⁻¹ * B z := by
    filter_upwards [ConditionalEnergyMoments.physical_conditional_support
      (ofLong β s) n m n.pos (Equiv.refl _) x] with z hz
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨h,rfl⟩
    dsimp only
    erw [hgrad z hz h, hH z hz h]
    exact physical_crossing_variational_internal β s n m U hUv (c z) (hs z hz) i (A h)
      (hactive h)
  have hmono := integral_mono_ae hint (hBi.1.const_mul β.val⁻¹) hbound
  rw [integral_const_mul, hBi.2] at hmono
  exact hvar.trans hmono

/-- See the proof of Lemma 5.7 in the paper, the complete two-inequality
statement equation (5.24). The force is the literal uniformly compensated
ambient derivative on the physical conditional law. The theorem concludes
its Sobolev graph membership and both finite variance bounds, with all integrability conclusions. -/
theorem compensated_force_variance (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) :
    ∃ U : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain ((n : ℕ) + m).succPNat) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) //
          y ∈ gapAmbientDomain ((n : ℕ) + m).succPNat},
        U y.val = β.val * physicalAmbientGapEnergy (ofLong β s) ((n : ℕ) + m).succPNat y) ∧
      ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (i : Fin (n : ℕ)),
        let q := WithLp.toLp 2 (compensationVector n m)
        let F := fun z => β.val⁻¹ *
          (fderiv ℝ U (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z))
              (EuclideanSpace.single (i.castAdd m).castSucc 1) -
            fderiv ℝ U (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) q)
        let μ := ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x
        Riesz1.WeightedSobolev.IsWeightedH1 μ
          (AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ a, x.val a)) F (gradient F) ∧
        (∫ z, (F z - ∫ y, F y ∂μ) ^ 2 ∂μ) ≤
          β.val⁻¹ * (BoundaryEntries.physicalCrossing β s n m x i i -
            2 * compensationB β s n m i x + compensationC β s n m x) ∧
        β.val⁻¹ * (BoundaryEntries.physicalCrossing β s n m x i i -
            2 * compensationB β s n m i x + compensationC β s n m x) ≤
          β.val⁻¹ * (BoundaryEntries.physicalCrossing β s n m x i i + compensationC β s n m x) := by
  obtain ⟨U, hs, hv, hgraph⟩ := physical_compensated_force_H1 (ofLong β s) n m
  refine ⟨U, hs, hv, fun x i => ?_⟩
  dsimp only
  refine ⟨hgraph x i, ?_, compensated_crossing_le β s n m i x⟩
  have he : (fun z => β.val⁻¹ *
      fderiv ℝ U (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z))
        (EuclideanSpace.single (i.castAdd m).castSucc 1 - WithLp.toLp 2 (compensationVector n m))) =
      (fun z => β.val⁻¹ *
        (fderiv ℝ U (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z))
            (EuclideanSpace.single (i.castAdd m).castSucc 1) -
          fderiv ℝ U (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z))
            (WithLp.toLp 2 (compensationVector n m)))) := by
    funext z
    rw [map_sub]
  have hg := hgraph x i
  dsimp only at hg
  erw [← he] at hg
  have hh := physical_force_variance_internal β s n m U hs hv x i hg
  dsimp only at hh
  simpa only [map_sub] using hh

/-- Image-by-image comparison for the pinned-particle step in
the proof of Lemma 5.8. Controlling both arcs controls every periodic
image, including the negative images. The multiplicity-two particle
coefficient is obtained by multiplying this inequality by two. -/
theorem two_arc_coefficient_comparison_internal (p : Parameters) (N : ℕ+)
    (L L' : {L : ℝ // 0 < L ∧ L < (N : ℝ)})
    (A : ℝ) (hA : 1 ≤ A) (hleft : L'.val ≤ A * L.val)
    (hright : (N : ℝ) - L'.val ≤ A * ((N : ℝ) - L.val)) :
    A ^ (-p.val.2 - 2) * PhysicalEnergy.intervalCoefficient p N L ≤
      PhysicalEnergy.intervalCoefficient p N L' := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have ha : 0 < A := by linarith
  have hq : -p.val.2 - 2 ≤ 0 := by linarith [p.property.2.1]
  have hdist (k : ℤ) : |L'.val + k * (N : ℝ)| ≤ A * |L.val + k * (N : ℝ)| := by
    by_cases hk : 0 ≤ k
    · have hkR : (0 : ℝ) ≤ k := by exact_mod_cast hk
      rw [abs_of_pos (add_pos_of_pos_of_nonneg L'.property.1 (mul_nonneg hkR hN.le)),
        abs_of_pos (add_pos_of_pos_of_nonneg L.property.1 (mul_nonneg hkR hN.le))]
      nlinarith [mul_nonneg (sub_nonneg.mpr hA) (mul_nonneg hkR hN.le)]
    · have hkR : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
      have hL : L.val + k * (N : ℝ) < 0 := by nlinarith [L.property.2]
      have hL' : L'.val + k * (N : ℝ) < 0 := by nlinarith [L'.property.2]
      rw [abs_of_neg hL', abs_of_neg hL]
      nlinarith [mul_nonneg (sub_nonneg.mpr hA)
        (mul_nonneg (show 0 ≤ -(k : ℝ) - 1 by linarith) hN.le)]
  have hpositive (T : {L : ℝ // 0 < L ∧ L < (N : ℝ)}) (k : ℤ) :
      0 < |T.val + k * (N : ℝ)| := by
    by_cases hk : 0 ≤ k
    · have hkR : (0 : ℝ) ≤ k := by exact_mod_cast hk
      exact abs_pos.mpr (add_pos_of_pos_of_nonneg T.property.1 (mul_nonneg hkR hN.le)).ne'
    · have hkR : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
      apply abs_pos.mpr
      have : T.val + k * (N : ℝ) < 0 := by nlinarith [T.property.2]
      exact this.ne
  have hterm (k : ℤ) :
      A ^ (-p.val.2 - 2) * |L.val + k * (N : ℝ)| ^ (-p.val.2 - 2) ≤
        |L'.val + k * (N : ℝ)| ^ (-p.val.2 - 2) := by
    have h := Real.rpow_le_rpow_of_nonpos (hpositive L' k) (hdist k) hq
    rwa [Real.mul_rpow ha.le (abs_nonneg _)] at h
  have hsum (T : {L : ℝ // 0 < L ∧ L < (N : ℝ)}) :
      Summable (fun k : ℤ => |T.val + k * (N : ℝ)| ^ (-p.val.2 - 2)) := by
    have h := (PeriodicPower.summable_and_le
      (by linarith [p.property.2.1] : 1 < p.val.2 + 2)
      (lt_min T.property.1 (sub_pos.mpr T.property.2))
      (min_le_left T.val ((N : ℝ) - T.val))
      (min_le_right T.val ((N : ℝ) - T.val))).1
    simpa only [show -(p.val.2 + 2) = -p.val.2 - 2 by ring] using h
  have hseries := ((hsum L).mul_left (A ^ (-p.val.2 - 2))).tsum_le_tsum hterm (hsum L')
  rw [tsum_mul_left] at hseries
  rw [PhysicalEnergy.intervalCoefficient_images, PhysicalEnergy.intervalCoefficient_images]
  have h := mul_le_mul_of_nonneg_left hseries
    (mul_nonneg p.property.2.1.le (by linarith [p.property.2.1] : 0 ≤ p.val.2 + 1))
  nlinarith only [h]

/-- The two-arc hypotheses of the preceding image comparison follow from
proximity and a lower bound on both reference arcs. In the proof of Lemma 5.8
one takes `a = delta * n^(-epsilon) / 2` and `D = delta * n^epsilon`. -/
theorem nearby_coefficient_comparison_internal (p : Parameters) (N : ℕ+)
    (L L' : {L : ℝ // 0 < L ∧ L < (N : ℝ)})
    (a D : ℝ) (ha : 0 < a) (hD : 0 ≤ D)
    (hleft : a ≤ L.val) (hright : a ≤ (N : ℝ) - L.val)
    (hnear : |L'.val - L.val| ≤ D) :
    (1 + D / a) ^ (-p.val.2 - 2) * PhysicalEnergy.intervalCoefficient p N L ≤
      PhysicalEnergy.intervalCoefficient p N L' := by
  have hquot : 0 ≤ D / a := div_nonneg hD ha.le
  apply two_arc_coefficient_comparison_internal p N L L' (1 + D / a) (by linarith)
  · have h := mul_le_mul_of_nonneg_left hleft hquot
    rw [div_mul_cancel₀ D ha.ne'] at h
    have hb := (abs_le.mp hnear).2
    nlinarith only [h,hb]
  · have h := mul_le_mul_of_nonneg_left hright hquot
    rw [div_mul_cancel₀ D ha.ne'] at h
    have hb := (abs_le.mp hnear).1
    nlinarith only [h,hb]

/-- The pinned diagonal curvature comparison in
the proof of Lemma 5.8, after selecting a set of nearby pinned
particles. This gives the factor equal to the number of selected particles.
None of the exterior gaps is bounded here. -/
theorem pinned_diagonal_comparison_internal {ι : Type*} [Fintype ι]
    (p : Parameters) (N : ℕ+)
    (L : {L : ℝ // 0 < L ∧ L < (N : ℝ)})
    (R : ι → {L : ℝ // 0 < L ∧ L < (N : ℝ)}) (S : Finset ι)
    (a D d : ℝ) (ha : 0 < a) (hD : 0 ≤ D)
    (hcard : d ≤ (S.card : ℝ))
    (hleft : a ≤ L.val) (hright : a ≤ (N : ℝ) - L.val)
    (hnear : ∀ r ∈ S, |(R r).val - L.val| ≤ D) :
    d * (1 + D / a) ^ (-p.val.2 - 2) *
        (2 * PhysicalEnergy.intervalCoefficient p N L) ≤
      ∑ r, 2 * PhysicalEnergy.intervalCoefficient p N (R r) := by
  have hfactor : 0 ≤ (1 + D / a) ^ (-p.val.2 - 2) *
      (2 * PhysicalEnergy.intervalCoefficient p N L) := by
    have hp := (PhysicalEnergy.intervalCoefficient_pos p N L).le
    have hbase : 0 ≤ 1 + D / a := by positivity
    exact mul_nonneg (Real.rpow_nonneg hbase _) (mul_nonneg (by norm_num) hp)
  calc
    _ = d * ((1 + D / a) ^ (-p.val.2 - 2) *
        (2 * PhysicalEnergy.intervalCoefficient p N L)) := by ring
    _ ≤ (S.card : ℝ) * ((1 + D / a) ^ (-p.val.2 - 2) *
        (2 * PhysicalEnergy.intervalCoefficient p N L)) :=
      mul_le_mul_of_nonneg_right hcard hfactor
    _ = ∑ r ∈ S, (1 + D / a) ^ (-p.val.2 - 2) *
        (2 * PhysicalEnergy.intervalCoefficient p N L) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ r ∈ S, 2 * PhysicalEnergy.intervalCoefficient p N (R r) := by
      apply Finset.sum_le_sum
      intro r hr
      have h := nearby_coefficient_comparison_internal p N L (R r) a D ha hD hleft hright
        (hnear r hr)
      linarith only [h]
    _ ≤ ∑ r, 2 * PhysicalEnergy.intervalCoefficient p N (R r) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun r _ _ => mul_nonneg (by norm_num) (PhysicalEnergy.intervalCoefficient_pos p N (R r)).le)

end Riesz2.ConditionalForces
