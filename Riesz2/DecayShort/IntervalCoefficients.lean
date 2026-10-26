/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.PhysicalFibres
public import Riesz2.ToMathlib.CyclicIntervalBoundary
public import Riesz2.ToMathlib.CyclicIntervalHessianBounds
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Physical interval coefficients and their boundary grouping

The coefficients use the ambient energy normalization, including
the even antipodal half-weight. Conditional coefficients are ordinary finite
expectations on the positive physical fibre. Their boundary matrix groups exactly
into prefix, suffix and full-block terms (Subsection 4.4).
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace Riesz2.DecayShort

/-- See Subsection 4.4 of the paper: the physical short-interval coefficient `a_J`. -/
def intervalWeight (p : Parameters) (N : ℕ+) (t : Fin (N : ℕ) × Fin ((N : ℕ) / 2))
    (y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N}) : ℝ :=
  (2 - if 2 * (t.2.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
    PhysicalEnergy.intervalCoefficient p N
      ⟨cyclicGapSum N t.1 (t.2.val + 1) (WithLp.ofLp y.val),
        y.property t.1 (t.2.val + 1) (by omega) (by have := t.2.isLt; omega)⟩

/-- The physical interval coefficient is measurable on its complete ambient carrier. -/
theorem measurable_intervalWeight (p : Parameters) (N : ℕ+)
    (t : Fin (N : ℕ) × Fin ((N : ℕ) / 2)) : Measurable (intervalWeight p N t) := by
  have he : intervalWeight p N t = fun y =>
      (2 - if 2 * (t.2.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
      (p.val.2 * (p.val.2 + 1) *
        ∑' k : ℤ, |PhysicalEnergy.intervalLinear N t.1 (t.2.val + 1) y.val + k * (N : ℝ)| ^
          (-p.val.2 - 2)) := by
    funext y
    rw [intervalWeight, PhysicalEnergy.intervalCoefficient_images,
      PhysicalEnergy.intervalLinear_apply]
  rw [he]
  apply Measurable.const_mul
  apply Measurable.const_mul
  apply Measurable.tsum
  intro k
  exact (((PhysicalEnergy.intervalLinear N t.1 (t.2.val + 1)).continuous.measurable.comp
    measurable_subtype_coe).add_const _).abs.pow_const _

/-- Every physical interval coefficient is strictly positive, including antipodal intervals. -/
theorem intervalWeight_pos (p : Parameters) (N : ℕ+)
    (t : Fin (N : ℕ) × Fin ((N : ℕ) / 2))
    (y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N}) :
    0 < intervalWeight p N t y := by
  unfold intervalWeight
  apply mul_pos _ (PhysicalEnergy.intervalCoefficient_pos p N _)
  split_ifs <;> norm_num

set_option backward.isDefEq.respectTransparency false in
/-- A pointwise integrable majorant for every physical interval coefficient.
No value at a collision is introduced. -/
theorem intervalWeight_le_inverseSum (p : Parameters) (N : ℕ+)
    (t : Fin (N : ℕ) × Fin ((N : ℕ) / 2))
    (y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N})
    (hy : WithLp.ofLp y.val ∈ Riesz1.gapSimplex N) :
    intervalWeight p N t y ≤
      2 * PhysicalEnergy.coefficientConstant p.val.2 p.property.2.1 *
        ∑ i, (y.val i) ^ (-p.val.2 - 2) := by
  classical
  let : Nonempty (Fin (N : ℕ)) := ⟨⟨0, N.pos⟩⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ (fun i => y.val i)
    Finset.univ_nonempty
  have hgap (j : Fin (N : ℕ)) : y.val i ≤ y.val j ∧ y.val j ≤ (N : ℝ) := by
    refine ⟨hi j (Finset.mem_univ j), ?_⟩
    exact (Finset.single_le_sum (s := Finset.univ) (fun a _ => (hy.1 a).le)
      (Finset.mem_univ j)).trans_eq hy.2
  have hh := (PhysicalEnergy.coefficient_gap_bounds p N t.1
    (by omega : 1 ≤ t.2.val + 1) (by have := t.2.isLt; omega)
    (WithLp.ofLp y.val) hy (hy.1 i) hgap).2
  have hpow : (t.2.val + 1 : ℝ) ^ (-p.val.2 - 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by have := Nat.cast_nonneg (α := ℝ) t.2.val; linarith) (by linarith [p.property.2.1])
  have hiSum : (y.val i) ^ (-p.val.2 - 2) ≤ ∑ j, (y.val j) ^ (-p.val.2 - 2) :=
    Finset.single_le_sum (s := Finset.univ)
      (fun j _ => Real.rpow_nonneg (hy.1 j).le _) (Finset.mem_univ i)
  have hC := (PhysicalEnergy.coefficientConstant_pos p.val.2 p.property.2.1).le
  have hpos := (PhysicalEnergy.intervalCoefficient_pos p N
    ⟨cyclicGapSum N t.1 (t.2.val + 1) (WithLp.ofLp y.val),
      y.property t.1 (t.2.val + 1) (by omega) (by have := t.2.isLt; omega)⟩).le
  unfold intervalWeight
  calc
    _ ≤ 2 * PhysicalEnergy.intervalCoefficient p N _ := by
      apply mul_le_mul_of_nonneg_right _ hpos
      split_ifs <;> norm_num
    _ ≤ 2 * (PhysicalEnergy.coefficientConstant p.val.2 p.property.2.1 *
        (y.val i) ^ (-p.val.2 - 2) * (t.2.val + 1 : ℝ) ^ (-p.val.2 - 2)) := by
      exact mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_add, Nat.cast_one] using hh) (by norm_num)
    _ ≤ 2 * (PhysicalEnergy.coefficientConstant p.val.2 p.property.2.1 *
        (y.val i) ^ (-p.val.2 - 2)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right (mul_nonneg hC (Real.rpow_nonneg (hy.1 i).le _)) hpow) (by norm_num)
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hiSum (by positivity :
        0 ≤ 2 * PhysicalEnergy.coefficientConstant p.val.2 p.property.2.1)

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 4.5 of the paper, fixed-fibre finiteness of every interval coefficient.
This holds at every retained point, rather than only almost everywhere. -/
theorem integrable_intervalWeight (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (t : Fin (n + m + 1) × Fin ((n + m + 1) / 2)) :
    Integrable (fun z => intervalWeight p (n + m).succPNat t
      (PhysicalFibres.configuration n m σ x z)) (PhysicalFibres.measure p n m hn σ x) := by
  have hg := (integrable_finsetSum Finset.univ
    (fun i _ => PhysicalFibres.integrable_coordinate_inverse p n m hn σ x i)).const_mul
      (2 * PhysicalEnergy.coefficientConstant p.val.2 p.property.2.1)
  apply hg.mono' ((measurable_intervalWeight p (n + m).succPNat t).comp
    (PhysicalFibres.continuous_configuration n m σ x).measurable).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  change ‖intervalWeight p (n + m).succPNat t (PhysicalFibres.configuration n m σ x z)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_pos (intervalWeight_pos p _ _ _)]
  exact intervalWeight_le_inverseSum p (n + m).succPNat t _ (PhysicalFibres.configuration_mem_simplex n m σ x z)

/-- See Subsection 4.4 of the paper: the actual finite conditional coefficient, on the
retained chart. Active penalties factor out of this conditional law. -/
def conditionalIntervalWeight (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (t : Fin (n + m + 1) × Fin ((n + m + 1) / 2)) : ℝ :=
  ∫ z, intervalWeight p (n + m).succPNat t (PhysicalFibres.configuration n m σ x z)
    ∂PhysicalFibres.measure p n m hn σ x

/-- Conditional coefficients are nonnegative ordinary finite expectations. -/
theorem conditionalIntervalWeight_nonneg (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (t : Fin (n + m + 1) × Fin ((n + m + 1) / 2)) :
    0 ≤ conditionalIntervalWeight p n m hn σ x t :=
  integral_nonneg (fun z => (intervalWeight_pos p (n + m).succPNat t
    (PhysicalFibres.configuration n m σ x z)).le)

/-- Ordinary and extended conditional expectations agree, with a finite result.
This rules out a divergent-integral interpretation of the coefficient. -/
theorem conditionalIntervalWeight_lintegral (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (t : Fin (n + m + 1) × Fin ((n + m + 1) / 2)) :
    (∫⁻ z, ENNReal.ofReal (intervalWeight p (n + m).succPNat t
      (PhysicalFibres.configuration n m σ x z)) ∂PhysicalFibres.measure p n m hn σ x) =
      ENNReal.ofReal (conditionalIntervalWeight p n m hn σ x t) := by
  exact (ofReal_integral_eq_lintegral_ofReal (integrable_intervalWeight p n m hn σ x t)
    (Filter.Eventually.of_forall (fun z => (intervalWeight_pos p (n + m).succPNat t
      (PhysicalFibres.configuration n m σ x z)).le))).symm

/-- A prefix, suffix and full-block representation of the boundary matrix
`P_∂` in Subsection 4.4. Here `N = n + m + 1`. The prefix and suffix
coefficients are `IntervalBoundary.prefixCoefficient` and
`IntervalBoundary.suffixCoefficient`. Suffix labels are zero-based.
The full-block term is `IntervalBoundary.fullCoefficient`.
Conditional weights are finite at every retained point by
`integrable_intervalWeight`, for either active tilt. The result also
holds in the long-range regime and when `N = 2`. -/
theorem exact_boundary_representation (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (hhalf : 2 * n ≤ n + m + 1)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (i j : Fin n) :
    let A := conditionalIntervalWeight p n m hn (Equiv.refl _) x
    IntervalBoundary.boundaryMatrix (n + m).succPNat n (by simp; omega) A i j =
      (∑ k ∈ Finset.Ico 1 n,
        IntervalBoundary.prefixCoefficient (n + m).succPNat n (by simp; omega) A k *
          IntervalBoundary.rankOne (IntervalBoundary.initialSegment n k) i j) +
      (∑ k ∈ Finset.Ico 1 n,
        IntervalBoundary.suffixCoefficient (n + m).succPNat n (by simp; omega) A k *
          IntervalBoundary.rankOne (IntervalBoundary.terminalSegment n k) i j) +
      IntervalBoundary.fullCoefficient (n + m).succPNat n (by simp; omega) A :=
  IntervalBoundary.boundary_representation (n + m).succPNat hn hhalf _ i j

/-- The physical boundary matrix is exactly `P - P_int`, as in Subsection 4.4. The internal and boundary matrices use the same finite coefficients. -/
theorem physical_boundary_eq_sub (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (hsize : n ≤ n + m + 1)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    let A := conditionalIntervalWeight p n m hn (Equiv.refl _) x
    IntervalBoundary.boundaryMatrix (n + m).succPNat n hsize A =
      IntervalBoundary.intervalMatrix (n + m).succPNat n hsize A -
        IntervalBoundary.internalMatrix (n + m).succPNat n hsize A := by
  intro A
  have he := IntervalBoundary.internal_add_boundary (n + m).succPNat n hsize A
  rw [← he, add_sub_cancel_left]

private theorem gapSum_single (N : ℕ+) (a b : Fin (N : ℕ)) (r : ℕ) (hr : r ≤ (N : ℕ)) :
    cyclicGapSum N a r (WithLp.ofLp (EuclideanSpace.single b (1 : ℝ))) =
      if b ∈ cyclicIndexInterval N a r then 1 else 0 := by
  convert cyclicGapSum_single N a b hr using 1
  congr 1
  ext j
  simp [EuclideanSpace.single, PiLp.single_apply, eq_comm]

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 4.4 of the paper: the conditional interval matrix is the actual
mean physical ambient Hessian. Both the derivatives and their conditional
integrals are identified. Integrability is concluded at every retained point. -/
theorem conditional_hessian_entries (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (hsize : n ≤ n + m + 1) :
    ∃ W : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain (n + m).succPNat) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
          y ∈ gapAmbientDomain (n + m).succPNat},
        W y.val = physicalAmbientGapEnergy p (n + m).succPNat y) ∧
      ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (i j : Fin n),
        let f := fun z => fderiv ℝ (fderiv ℝ W)
          (PhysicalFibres.configuration n m (Equiv.refl _) x z).val
          (EuclideanSpace.single (Fin.castLE hsize i) 1)
          (EuclideanSpace.single (Fin.castLE hsize j) 1)
        Integrable f (PhysicalFibres.measure p n m hn (Equiv.refl _) x) ∧
          (∫ z, f z ∂PhysicalFibres.measure p n m hn (Equiv.refl _) x) =
            IntervalBoundary.intervalMatrix (n + m).succPNat n hsize
              (conditionalIntervalWeight p n m hn (Equiv.refl _) x) i j := by
  classical
  obtain ⟨W, hW, hv, hj⟩ := PhysicalEnergy.ambient_derivatives p (n + m).succPNat
  change (EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ) at W
  simp only [Nat.succPNat_coe] at hW hv hj
  refine ⟨W, hW, hv, fun x i j => ?_⟩
  dsimp only
  let f := fun z => fderiv ℝ (fderiv ℝ W)
    (PhysicalFibres.configuration n m (Equiv.refl _) x z).val
    (EuclideanSpace.single (Fin.castLE hsize i) 1)
    (EuclideanSpace.single (Fin.castLE hsize j) 1)
  let K : (Fin (n + m + 1) × Fin ((n + m + 1) / 2)) → ℝ := fun t =>
    IntervalBoundary.rankOne
      (IntervalBoundary.trace (n + m).succPNat n hsize t.1 (t.2.val + 1)) i j
  have he : f = fun z => ∑ t : Fin (n + m + 1) × Fin ((n + m + 1) / 2),
      intervalWeight p (n + m).succPNat t
        (PhysicalFibres.configuration n m (Equiv.refl _) x z) * K t := by
    funext z
    rw [show f z = _ from (hj _ _ _).2, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro r _
    rw [gapSum_single (n + m).succPNat a _ _ (Nat.le_trans (Nat.succ_le_of_lt r.isLt) (Nat.div_le_self _ _)),
      gapSum_single (n + m).succPNat a _ _ (Nat.le_trans (Nat.succ_le_of_lt r.isLt) (Nat.div_le_self _ _))]
    dsimp only [intervalWeight, K, IntervalBoundary.rankOne, IntervalBoundary.trace]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hi : Fin.castLE hsize i ∈ cyclicIndexInterval (n + m).succPNat a (r.val + 1) <;>
      by_cases hj : Fin.castLE hsize j ∈ cyclicIndexInterval (n + m).succPNat a (r.val + 1) <;>
      simp [hi, hj]
  have hg (t : Fin (n + m + 1) × Fin ((n + m + 1) / 2)) :
      Integrable (fun z => intervalWeight p (n + m).succPNat t
        (PhysicalFibres.configuration n m (Equiv.refl _) x z) * K t)
          (PhysicalFibres.measure p n m hn (Equiv.refl _) x) :=
    (integrable_intervalWeight p n m hn (Equiv.refl _) x t).mul_const _
  refine ⟨?_, ?_⟩
  · change Integrable f _
    rw [he]
    exact integrable_finsetSum _ (fun t _ => hg t)
  · change (∫ z, f z ∂_) = _
    rw [he, integral_finsetSum _ (fun t _ => hg t)]
    simp only [integral_mul_const, conditionalIntervalWeight, IntervalBoundary.intervalMatrix, K]
    rfl

/-- See Subsection 4.4 of the paper: every grouped physical boundary coefficient is
nonnegative and finite, since it is a finite sum of ordinary finite expectations.
Suffix start `k` uses zero-based labels. -/
theorem physical_boundary_coefficients_nonneg (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (hsize : n ≤ n + m + 1)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    let A := conditionalIntervalWeight p n m hn (Equiv.refl _) x
    (∀ k, 0 ≤ IntervalBoundary.prefixCoefficient (n + m).succPNat n hsize A k) ∧
      (∀ k, 0 ≤ IntervalBoundary.suffixCoefficient (n + m).succPNat n hsize A k) ∧
      0 ≤ IntervalBoundary.fullCoefficient (n + m).succPNat n hsize A := by
  classical
  intro A
  have hA (t) : 0 ≤ A t := conditionalIntervalWeight_nonneg p n m hn (Equiv.refl _) x t
  refine ⟨fun k => ?_, fun k => ?_, ?_⟩
  all_goals
    apply Finset.sum_nonneg
    intro t _
    split_ifs <;> first | exact hA t | exact le_rfl

end Riesz2.DecayShort
