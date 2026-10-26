/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.BoundaryEntriesPart4
public import Riesz2.DecayLong.PhysicalFormDomainPart2

/-!
# The physical core

The core of equation (5.4), using the physical internal and crossing
blocks, the reference matrix, and the density-defined good event.
The exterior dimension of the physical fibre is `m`. The independent
component period is `M`. This file proves algebraic identities,
measurability and symmetry.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped BigOperators Classical ContDiff

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.PhysicalCore

/-- The Hessian of the upper-only forcing in Section 5.
This uses the existing Hessian operation, on the entire ambient space. -/
def forcingHessian (n : ℕ+) (θ : PhysicalCutoff) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin (n : ℕ))) :
    Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ :=
  hessianMatrix (fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
    ∑ i, θ.val ((n : ℝ) ^ (-ε) * y i)) x

/-- See Subsection 5.1 of the paper: the active block `A₀`. The internal
physical coefficients and forcing are used on the good event. Reference boundary intervals
are retained everywhere, including on the good event. -/
def properActive (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ :=
  (if x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀ then
    forcingHessian n θ ε x.val + BoundaryEntries.physicalInternal β s n m x
  else BoundaryEntries.referenceInternal s M hM K n hnM) +
    BoundaryEntries.referenceCrossing s M hM K n hnM

/-- See Subsection 5.1 of the paper: the full component matrix, with the original
reference exterior blocks. The two branches are precisely the active and
exterior blocks of this matrix. -/
def properMatrix (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    Matrix (Fin (M : ℕ)) (Fin (M : ℕ)) ℝ :=
  fun a b => if ha : a.val < (n : ℕ) then
    if hb : b.val < (n : ℕ) then
      properActive β s n m M hM hnM K θ ε κ₀ x ⟨a.val, ha⟩ ⟨b.val, hb⟩
    else 2 * referenceIntervalMatrix s M hM K a b
  else 2 * referenceIntervalMatrix s M hM K a b

/-- The full core restricts to the intended active block. -/
theorem properMatrix_active (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (a b : Fin (n : ℕ)) :
    properMatrix β s n m M hM hnM K θ ε κ₀ x (a.castLE hnM) (b.castLE hnM) =
      properActive β s n m M hM hnM K θ ε κ₀ x a b := by
  simp only [properMatrix, Fin.val_castLE, a.isLt, b.isLt, ↓reduceDIte]

/-- The exterior and coupling entries have the literal reference normalization
required by `PeriodizedMatrixBounds` predicate. -/
theorem properMatrix_exterior (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (a b : Fin (M : ℕ)) (hab : (n : ℕ) ≤ a.val ∨ (n : ℕ) ≤ b.val) :
    properMatrix β s n m M hM hnM K θ ε κ₀ x a b =
      ((2 : ℝ) • referenceIntervalMatrix s M hM K) a b := by
  simp only [properMatrix, Matrix.smul_apply, smul_eq_mul]
  split_ifs with ha hb <;> first | rfl | omega

/-- Freezing off the good event gives exactly the full reference active block. -/
theorem properActive_of_not_mem (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (hx : x ∉ GoodBlocks.properGoodEvent β s n m ε κ₀) (a b : Fin (n : ℕ)) :
    properActive β s n m M hM hnM K θ ε κ₀ x a b =
      2 * referenceIntervalMatrix s M hM K (a.castLE hnM) (b.castLE hnM) := by
  simp only [properActive, ite_eq_right hx, Matrix.add_apply]
  exact BoundaryEntries.referenceInternal_add_crossing s M hM K n hnM a b

/-- See Subsection 5.1 of the paper: the whole matrix, including its active entries,
is the reference off the good event. -/
theorem properMatrix_of_not_mem (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (hx : x ∉ GoodBlocks.properGoodEvent β s n m ε κ₀) :
    properMatrix β s n m M hM hnM K θ ε κ₀ x =
      (2 : ℝ) • referenceIntervalMatrix s M hM K := by
  ext a b
  unfold properMatrix
  split_ifs with ha hb
  · have ha' : Fin.castLE hnM (⟨a.val, ha⟩ : Fin (n : ℕ)) = a := Fin.ext rfl
    have hb' : Fin.castLE hnM (⟨b.val, hb⟩ : Fin (n : ℕ)) = b := Fin.ext rfl
    simpa only [ha', hb', Matrix.smul_apply, smul_eq_mul] using
      properActive_of_not_mem β s n m M hM hnM K θ ε κ₀ x hx ⟨a.val, ha⟩ ⟨b.val, hb⟩
  all_goals rfl

/-- The exact signed multiplication difference, before adding compensation
or a Schur correction. It is combined pointwise, so no separate integration
of unbounded signed pieces is implicit in this identity. -/
theorem properActive_defect (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (a b : Fin (n : ℕ)) :
    forcingHessian n θ ε x.val a b + GoodBlocks.conditionalHessian β s n m a b x -
      properActive β s n m M hM hnM K θ ε κ₀ x a b =
      if x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀ then
        BoundaryEntries.boundaryRemainder β s n m M hM hnM K x a b
      else forcingHessian n θ ε x.val a b + GoodBlocks.conditionalHessian β s n m a b x -
        2 * referenceIntervalMatrix s M hM K (a.castLE hnM) (b.castLE hnM) := by
  by_cases hx : x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀
  · simp only [ite_eq_left hx, properActive, Matrix.add_apply,
      BoundaryEntries.boundaryRemainder, Matrix.sub_apply]
    have hp := BoundaryEntries.physicalInternal_add_crossing β s n m x a b
    linarith only [hp]
  · rw [ite_eq_right hx, properActive_of_not_mem β s n m M hM hnM K θ ε κ₀ x hx]

/-- Every entry of the actual physical internal block is Borel. -/
theorem measurable_physicalInternal (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (a b : Fin (n : ℕ)) :
    Measurable (fun x => BoundaryEntries.physicalInternal β s n m x a b) := by
  have he : (fun x => BoundaryEntries.physicalInternal β s n m x a b) =
      fun x => GoodBlocks.conditionalHessian β s n m a b x -
        BoundaryEntries.physicalCrossing β s n m x a b := by
    funext x
    have hp := BoundaryEntries.physicalInternal_add_crossing β s n m x a b
    linarith only [hp]
  rw [he]
  exact (GoodBlocks.measurable_conditionalHessian β s n m a b).sub
    (BoundaryEntries.measurable_physicalCrossing β s n m a b)

/-- The forcing Hessian uses measurable classical derivatives. -/
theorem measurable_forcingHessian (n : ℕ+) (θ : PhysicalCutoff) (ε : ℝ)
    (a b : Fin (n : ℕ)) : Measurable (fun x => forcingHessian n θ ε x a b) :=
  DifferentiatedPoisson.measurable_hessian_entries a b

/-- The active block is a measurable field on the full open carrier. -/
theorem measurable_properActive (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ)
    (a b : Fin (n : ℕ)) :
    Measurable (fun x => properActive β s n m M hM hnM K θ ε κ₀ x a b) := by
  have he : (fun x => properActive β s n m M hM hnM K θ ε κ₀ x a b) =
      fun x => (if x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀ then
        forcingHessian n θ ε x.val a b + BoundaryEntries.physicalInternal β s n m x a b
      else BoundaryEntries.referenceInternal s M hM K n hnM a b) +
        BoundaryEntries.referenceCrossing s M hM K n hnM a b := by
    funext x
    unfold properActive
    split_ifs <;> rfl
  rw [he]
  exact (((measurable_forcingHessian n θ ε a b).comp measurable_subtype_coe).add
    (measurable_physicalInternal β s n m a b)).ite
      (GoodBlocks.measurableSet_properGoodEvent β s n m ε κ₀) measurable_const |>.add_const _

/-- Measurability in the exact entrywise interface of the periodized
matrix predicate. -/
theorem measurable_properMatrix (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ)
    (a b : Fin (M : ℕ)) :
    Measurable (fun x => properMatrix β s n m M hM hnM K θ ε κ₀ x a b) := by
  unfold properMatrix
  split_ifs
  · exact measurable_properActive β s n m M hM hnM K θ ε κ₀ _ _
  all_goals exact measurable_const

/-- Symmetry of the physical internal sum, retaining the original conditional
coefficient rather than replacing it by an almost-everywhere version. -/
theorem physicalInternal_symmetric (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (a b : Fin (n : ℕ)) :
    BoundaryEntries.physicalInternal β s n m x a b =
      BoundaryEntries.physicalInternal β s n m x b a := by
  simp only [BoundaryEntries.physicalInternal, and_comm, and_assoc]

/-- Symmetry of every literal reference interval subfamily. -/
theorem referenceIntervalBlock_symmetric (s : Riesz1.RieszExponent)
    (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (K : ℕ) (n : ℕ+)
    (hnM : (n : ℕ) ≤ (M : ℕ)) (family : Finset (Fin (M : ℕ)) → Prop)
    (a b : Fin (n : ℕ)) :
    BoundaryEntries.referenceIntervalBlock s M hM K n hnM family a b =
      BoundaryEntries.referenceIntervalBlock s M hM K n hnM family b a := by
  unfold BoundaryEntries.referenceIntervalBlock
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> ring

/-- The forcing is smooth on the whole proper physical carrier. -/
theorem forcing_smooth (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε : ℝ) :
    ContDiffOn ℝ ∞ (fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      ∑ i, θ.val ((n : ℝ) ^ (-ε) * y i))
      (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) := by
  have ha : 0 < (n : ℝ) ^ (-ε) := Real.rpow_pos_of_pos (by exact_mod_cast n.pos) _
  apply ContDiffOn.sum
  intro i _ x hx
  exact ((PhysicalCollision.cutoff_contDiffAt θ (mul_pos ha (hx.1 i))).comp x
    (contDiffAt_const.mul (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt)).contDiffWithinAt

/-- Symmetry of the actual classical forcing Hessian on the physical carrier. -/
theorem forcingHessian_symmetric (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (a b : Fin (n : ℕ)) :
    forcingHessian n θ ε x.val a b = forcingHessian n θ ε x.val b a := by
  have hsm := (forcing_smooth n m θ ε).contDiffAt
    ((AffineSimplex.isOpen_chartDomain n _).mem_nhds x.property)
  simp only [forcingHessian, Intrinsic.hessianMatrix_eq_second hsm]
  exact (hsm.isSymmSndFDerivAt (by norm_num)).eq _ _

/-- Symmetry of the full active block, including its reference crossing
part on both sides of the good-event boundary. -/
theorem properActive_symmetric (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (a b : Fin (n : ℕ)) :
    properActive β s n m M hM hnM K θ ε κ₀ x a b =
      properActive β s n m M hM hnM K θ ε κ₀ x b a := by
  unfold properActive
  split_ifs
  · simp only [Matrix.add_apply]
    rw [forcingHessian_symmetric n m θ ε x a b,
      physicalInternal_symmetric β s n m x a b]
    congr 1
    exact referenceIntervalBlock_symmetric s M hM K n hnM _ a b
  · simp only [Matrix.add_apply]
    rw [show BoundaryEntries.referenceInternal s M hM K n hnM a b =
      BoundaryEntries.referenceInternal s M hM K n hnM b a from
        referenceIntervalBlock_symmetric s M hM K n hnM _ a b,
      show BoundaryEntries.referenceCrossing s M hM K n hnM a b =
      BoundaryEntries.referenceCrossing s M hM K n hnM b a from
        referenceIntervalBlock_symmetric s M hM K n hnM _ a b]

/-- Symmetry in the exact entrywise interface of the periodized
matrix assumptions. -/
theorem properMatrix_symmetric (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (a b : Fin (M : ℕ)) :
    properMatrix β s n m M hM hnM K θ ε κ₀ x a b =
      properMatrix β s n m M hM hnM K θ ε κ₀ x b a := by
  have href : referenceIntervalMatrix s M hM K a b =
      referenceIntervalMatrix s M hM K b a := by
    simpa only [Matrix.conjTranspose_apply, star_trivial] using
      (congrFun (congrFun (referenceIntervalMatrix_isHermitian s M hM K) b) a)
  unfold properMatrix
  split_ifs
  · exact properActive_symmetric β s n m M hM hnM K θ ε κ₀ x _ _
  all_goals rw [href]

/-- An interval wholly inside the retained window is independent of every
exterior coordinate in the actual affine chart. This is valid even for an
exterior chart point outside the positive fibre, since only active gaps occur. -/
theorem internal_gapSum_independent (n : ℕ+) (m : ℕ)
    (x : EuclideanSpace ℝ (Fin (n : ℕ)))
    (r : Fin (((n : ℕ) + m + 1) / 2)) (i : Fin ((n : ℕ) + m + 1))
    (hi : IntervalBoundary.IsInternal ((n : ℕ) + m).succPNat n (i, r))
    (z w : EuclideanSpace ℝ (Fin m)) :
    cyclicGapSum ((n : ℕ) + m).succPNat i (r.val + 1)
        (WithLp.ofLp (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x, z))) =
      cyclicGapSum ((n : ℕ) + m).succPNat i (r.val + 1)
        (WithLp.ofLp (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x, w))) := by
  have hr : r.val + 1 ≤ (((n : ℕ) + m).succPNat : ℕ) := by
    have := r.isLt
    simp only [Nat.succPNat_coe]
    omega
  rw [← sum_cyclicIndexInterval_eq_cyclicGapSum _ _ hr,
    ← sum_cyclicIndexInterval_eq_cyclicGapSum _ _ hr]
  apply Finset.sum_congr rfl
  intro a ha
  have han : a.val < (n : ℕ) := hi a ha
  let b : Fin (n : ℕ) := ⟨a.val, han⟩
  have he : (b.castAdd m).castSucc = a := Fin.ext rfl
  change RetainedSimplex.chart n m _ (Equiv.refl _) (x, z) a =
    RetainedSimplex.chart n m _ (Equiv.refl _) (x, w) a
  rw [← he]
  exact (RetainedSimplex.chart_retained n m _ (Equiv.refl _) x z b).trans
    (RetainedSimplex.chart_retained n m _ (Equiv.refl _) x w b).symm

/-- Internal conditional coefficients are the actual deterministic active
coefficients. Evaluation at exterior coordinate zero is safe here: the
interval sum involves only the strictly positive retained gaps, and is
strictly smaller than total mass. No derivative at a collision is taken. -/
theorem conditionalIntervalWeight_internal (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (r : Fin (((n : ℕ) + m + 1) / 2)) (i : Fin ((n : ℕ) + m + 1))
    (hi : IntervalBoundary.IsInternal ((n : ℕ) + m).succPNat n (i, r)) :
    BoundaryEntries.conditionalIntervalWeight β s n m r i x =
      BoundaryEntries.intervalWeight s ((n : ℕ) + m).succPNat r i
        (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val, 0)) := by
  let ρ := ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x
  have : IsProbabilityMeasure ρ :=
    ProperMarginalChart.conditionalMeasure_probability (ofLong β s) n m n.pos (Equiv.refl _) x
  have he (z : EuclideanSpace ℝ (Fin m)) :
      BoundaryEntries.intervalWeight s ((n : ℕ) + m).succPNat r i
        (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val, z)) =
      BoundaryEntries.intervalWeight s ((n : ℕ) + m).succPNat r i
        (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val, 0)) := by
    unfold BoundaryEntries.intervalWeight
    rw [internal_gapSum_independent n m x.val r i hi z 0]
  change (∫ z, BoundaryEntries.intervalWeight s ((n : ℕ) + m).succPNat r i
    (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val, z)) ∂ρ) = _
  simp_rw [he]
  simp

/-- The deterministic internal interval sum is strictly between zero and the
physical period, even when evaluated at exterior chart coordinate zero.
This rules out a totalized kernel derivative at a collision in the bridge. -/
theorem internal_gapSum_mem (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (r : Fin (((n : ℕ) + m + 1) / 2)) (i : Fin ((n : ℕ) + m + 1))
    (hi : IntervalBoundary.IsInternal ((n : ℕ) + m).succPNat n (i, r)) :
    let L := cyclicGapSum ((n : ℕ) + m).succPNat i (r.val + 1)
      (WithLp.ofLp (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val, 0)))
    0 < L ∧ L < (((n : ℕ) + m).succPNat : ℝ) := by
  let μ := ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x
  have : IsProbabilityMeasure μ :=
    ProperMarginalChart.conditionalMeasure_probability (ofLong β s) n m n.pos (Equiv.refl _) x
  have hs := ConditionalEnergyMoments.physical_conditional_support (ofLong β s) n m n.pos
    (Equiv.refl _) x
  change ∀ᵐ z ∂μ, z ∈ AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ a, x.val a) at hs
  obtain ⟨z, hz⟩ := hs.exists
  have hd := (Set.ext_iff.mp (RetainedSimplex.fibre_domain n m _ x.property) z).mpr hz
  have hy := (RetainedSimplex.chart_mem_simplex n m _ (Equiv.refl _) (x.val, z)).mpr hd
  have hy' : WithLp.ofLp (RetainedSimplex.chart n m ((n + m : ℕ) + 1)
      (Equiv.refl _) (x.val, z)) ∈ Riesz1.gapSimplex ((n : ℕ) + m).succPNat :=
    ⟨hy.1, by simpa only [Nat.succPNat_coe, Nat.cast_succ] using hy.2⟩
  have hr : r.val + 1 < (((n : ℕ) + m).succPNat : ℕ) := by
    have := r.isLt
    simp only [Nat.succPNat_coe]
    omega
  have hL := PhysicalEnergy.gapSum_mem ((n : ℕ) + m).succPNat i (by omega) hr _ hy'
  rwa [internal_gapSum_independent n m x.val r i hi z 0] at hL

/-- See Subsection 5.1 of the paper, bridge for internal coefficients: the conditional
integral is the literal noncollision physical image coefficient, including
the antipodal factor. The separation is certified before differentiation. -/
theorem internal_coefficient_formula (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (r : Fin (((n : ℕ) + m + 1) / 2)) (i : Fin ((n : ℕ) + m + 1))
    (hi : IntervalBoundary.IsInternal ((n : ℕ) + m).succPNat n (i, r)) :
    let N := ((n : ℕ) + m).succPNat
    let L := cyclicGapSum N i (r.val + 1)
      (WithLp.ofLp (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val, 0)))
    BoundaryEntries.conditionalIntervalWeight β s n m r i x =
      (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
        PhysicalEnergy.intervalCoefficient (ofLong β s) N
          ⟨L, internal_gapSum_mem β s n m x r i hi⟩ := by
  rw [conditionalIntervalWeight_internal β s n m x r i hi]
  simp only [BoundaryEntries.intervalWeight, PhysicalEnergy.intervalCoefficient,
    PhysicalEnergy.kernelDerivative, ofLong, s.property.2, ↓reduceDIte,
    PhysicalEnergy.scaledSeparation, PNat.val_ofNat]

/-- The internal coefficient retains the principal-image lower bound,
uniformly in the exterior and without any conditional expectation premise. -/
theorem internal_coefficient_lower (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (r : Fin (((n : ℕ) + m + 1) / 2)) (i : Fin ((n : ℕ) + m + 1))
    (hi : IntervalBoundary.IsInternal ((n : ℕ) + m).succPNat n (i, r)) :
    let L := cyclicGapSum ((n : ℕ) + m).succPNat i (r.val + 1)
      (WithLp.ofLp (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val, 0)))
    s.val * (s.val + 1) * L ^ (-s.val - 2) ≤
      BoundaryEntries.conditionalIntervalWeight β s n m r i x := by
  intro L
  rw [internal_coefficient_formula β s n m x r i hi]
  have hL := internal_gapSum_mem β s n m x r i hi
  have hlow := PhysicalEnergy.intervalCoefficient_lower (ofLong β s)
    ((n : ℕ) + m).succPNat ⟨L, hL⟩
  have hpos := (PhysicalEnergy.intervalCoefficient_pos (ofLong β s)
    ((n : ℕ) + m).succPNat ⟨L, hL⟩).le
  calc
    _ ≤ PhysicalEnergy.intervalCoefficient (ofLong β s) ((n : ℕ) + m).succPNat ⟨L, hL⟩ := hlow
    _ ≤ _ := le_mul_of_one_le_left hpos (by split_ifs <;> norm_num)

end Riesz2.PhysicalCore
