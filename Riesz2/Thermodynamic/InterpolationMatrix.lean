/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.PhysicalCorePart7
public import Riesz2.DecayShort.PhysicalComparisonPart2
public import Riesz2.Thermodynamic.InterpolationCoefficientsPart2
public import Riesz2.ToMathlib.PeriodizedMatrixInterpolation
import all Riesz2.DecayShort.ExceptionalEventPart4
import all Riesz2.DecayLong.BoundarySchurBounds

/-!
# The fixed-exterior interpolation matrix

The internal coefficients in Subsection 6.1 are the existing physical internal
coefficients: conditioning does not change an internal interval. The scalar carrier
below is the positive ambient active chart. Restriction to any compatible fixed-length
simplex uses the same field. The physical period and the enlarged component period
remain distinct.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical ContDiff MatrixOrder

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.InterpolationMatrix

/-- See Subsection 6.1 of the paper: the ambient two-sided forcing Hessian. The
function differentiated here is exactly the summand of `physicalGapPenalty`
in active gap coordinates, with both penalties present. -/
def penaltyHessian (n : ℕ+) (θ : PhysicalCutoff) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin (n : ℕ))) : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ :=
  hessianMatrix (fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
    ∑ i, (θ.val ((n : ℝ)^(-ε)*y i) +
      θ.val ((n : ℝ)^(-ε)*(y i)⁻¹))) x

/-- The common active chart embeds in the chart of a larger period by
identity on every coordinate. There is no choice of an exterior. -/
def largerChart (n : ℕ+) (d e : ℕ) (hde : d ≤ e)
    (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1)) :
    AffineSimplex.chartDomain n ((n+e : ℕ)+1) :=
  ⟨x.val, x.property.1, x.property.2.trans_le (by exact_mod_cast (show (n : ℕ)+d+1 ≤ (n : ℕ)+e+1 by omega))⟩

/-- See Subsection 6.1 of the paper: the common rigidity event, rather than a
conditional-Hessian event from the proper marginal construction. -/
def goodSet (s : Riesz1.RieszExponent) (n : ℕ+) (d : ℕ) (η : ℝ) :
    Set (AffineSimplex.chartDomain n ((n+d : ℕ)+1)) :=
  {x | WithLp.ofLp x.val ∈ goodBlockEvent s.val n ((n : ℕ)+d).succPNat η}

/-- See Subsection 6.1 of the paper: the physical interpolated retained internal
block `P⁽¹⁾(t)`. Internal coefficients do not depend on the fixed exterior
values, by `PhysicalCore.conditionalIntervalWeight_internal`. -/
def internalBlock (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (t : ℝ)
    (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1)) :
    Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ :=
  (1-t) • BoundaryEntries.physicalInternal β s n d x +
    t • BoundaryEntries.physicalInternal β s n e (largerChart n d e hde x)

/-- See Subsection 6.1 of the paper: the active block `A₀(t)`, on its entire
positive carrier. The two branches are exactly the prescribed freezing. -/
def activeBlock (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε η t : ℝ)
    (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1)) :
    Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ :=
  (if x ∈ goodSet s n d η then
    penaltyHessian n θ ε x.val + internalBlock β s n d e hde t x
  else BoundaryEntries.referenceInternal s M hM K n hnM) +
    BoundaryEntries.referenceCrossing s M hM K n hnM

/-- See Subsection 6.1 of the paper: the full matrix `M(t)` with the reference
coupling and exterior blocks. The component period may differ from both
physical periods. -/
def matrix (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε η t : ℝ)
    (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1)) :
    Matrix (Fin (M : ℕ)) (Fin (M : ℕ)) ℝ :=
  fun i j => if hi : i.val < (n : ℕ) then
    if hj : j.val < (n : ℕ) then
      activeBlock β s n d e hde M hM hnM K θ ε η t x ⟨i.val,hi⟩ ⟨j.val,hj⟩
    else 2*referenceIntervalMatrix s M hM K i j
  else 2*referenceIntervalMatrix s M hM K i j

/-- The enlargement is continuous and measurable on the whole common chart. -/
theorem measurable_largerChart (n : ℕ+) (d e : ℕ) (hde : d ≤ e) :
    Measurable (largerChart n d e hde) := measurable_subtype_coe.subtype_mk

/-- The common rigidity event in Subsection 6.1 is measurable. -/
theorem measurableSet_goodSet (s : Riesz1.RieszExponent) (n : ℕ+) (d : ℕ) (η : ℝ) :
    MeasurableSet (goodSet s n d η) := by
  apply (InterpolantLocalLaws.measurableSet_goodBlockEvent s.val n _ η).preimage
  exact Measurable.of_eval (fun i => (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable.comp measurable_subtype_coe)

/-- The two-sided forcing Hessian is Borel entrywise (Subsection 6.1). -/
theorem measurable_penaltyHessian (n : ℕ+) (θ : PhysicalCutoff) (ε : ℝ)
    (i j : Fin (n : ℕ)) : Measurable (fun x => penaltyHessian n θ ε x i j) :=
  DifferentiatedPoisson.measurable_hessian_entries i j

/-- The actual two-sided forcing has no mixed entries on the positive
carrier, including below the cutoff (Subsection 6.1). -/
theorem penaltyHessian_off_diagonal (n : ℕ+) (θ : PhysicalCutoff) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin (n : ℕ))) (hx : ∀ i, 0 < x i)
    (i j : Fin (n : ℕ)) (hij : i ≠ j) : penaltyHessian n θ ε x i j = 0 :=
  DecayShort.PhysicalComparison.penalty_hessian_off_diagonal n θ
    (Real.rpow_pos_of_pos (by positivity) _) true x hx i j hij

/-- Nonnegative singleton coefficients of the actual two-sided forcing
on its entire positive carrier (Subsection 6.1). -/
theorem penaltyHessian_diagonal_nonneg (n : ℕ+) (θ : PhysicalCutoff) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin (n : ℕ))) (hx : ∀ i, 0 < x i) (i : Fin (n : ℕ)) :
    0 ≤ penaltyHessian n θ ε x i i := by
  let L := (∑ i, x i)+1
  have hxL : x ∈ AffineSimplex.chartDomain n L := ⟨hx, by dsimp only [L]; linarith⟩
  have ha : 0 < (n : ℝ)^(-ε) := Real.rpow_pos_of_pos (by positivity) _
  have hsm := DecayShort.PhysicalComparison.penalty_contDiffAt n θ ha true x hx
  simp only [ite_true] at hsm
  rw [penaltyHessian, DecayShort.PhysicalComparison.hessianMatrix_entry hsm]
  have hconv := (DecayShort.ExceptionalEvent.penalty_smooth_convex n L θ ha true).2
  exact Riesz1.fderiv_fderiv_nonneg_of_convexOn (AffineSimplex.isOpen_chartDomain n L)
    hconv.1 hconv
    ((DecayShort.ExceptionalEvent.penalty_smooth_convex n L θ ha true).1.of_le
      (by norm_num)) hxL _

/-- Symmetry of the two-sided forcing on every positive active vector. -/
theorem penaltyHessian_symmetric (n : ℕ+) (θ : PhysicalCutoff) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin (n : ℕ))) (hx : ∀ i, 0 < x i) (i j : Fin (n : ℕ)) :
    penaltyHessian n θ ε x i j = penaltyHessian n θ ε x j i := by
  by_cases hij : i = j
  · subst j; rfl
  · rw [penaltyHessian_off_diagonal n θ ε x hx i j hij,
      penaltyHessian_off_diagonal n θ ε x hx j i (Ne.symm hij)]

/-- The actual interpolated internal field is measurable entrywise. -/
theorem measurable_internalBlock (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (t : ℝ) (i j : Fin (n : ℕ)) :
    Measurable (fun x => internalBlock β s n d e hde t x i j) := by
  exact ((PhysicalCore.measurable_physicalInternal β s n d i j).const_mul (1-t)).add
    (((PhysicalCore.measurable_physicalInternal β s n e i j).comp
      (measurable_largerChart n d e hde)).const_mul t)

/-- Symmetry holds for the exact interpolated internal block at every size. -/
theorem internalBlock_symmetric (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (t : ℝ)
    (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1)) (i j : Fin (n : ℕ)) :
    internalBlock β s n d e hde t x i j = internalBlock β s n d e hde t x j i := by
  simp only [internalBlock, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    PhysicalCore.physicalInternal_symmetric β s n d x i j,
    PhysicalCore.physicalInternal_symmetric β s n e (largerChart n d e hde x) i j]

/-- The active matrix of Subsection 6.1 is a measurable field. -/
theorem measurable_activeBlock (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε η t : ℝ)
    (i j : Fin (n : ℕ)) :
    Measurable (fun x => activeBlock β s n d e hde M hM hnM K θ ε η t x i j) := by
  have he : (fun x => activeBlock β s n d e hde M hM hnM K θ ε η t x i j) =
      fun x => (if x ∈ goodSet s n d η then
        penaltyHessian n θ ε x.val i j + internalBlock β s n d e hde t x i j
      else BoundaryEntries.referenceInternal s M hM K n hnM i j) +
        BoundaryEntries.referenceCrossing s M hM K n hnM i j := by
    funext x
    unfold activeBlock
    split_ifs <;> rfl
  rw [he]
  exact (((measurable_penaltyHessian n θ ε i j).comp measurable_subtype_coe).add
    (measurable_internalBlock β s n d e hde t i j)).ite
      (measurableSet_goodSet s n d η) measurable_const |>.add_const _

/-- The exact full matrix is measurable at all sizes (Subsection 6.1). -/
theorem measurable_matrix (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε η t : ℝ)
    (i j : Fin (M : ℕ)) :
    Measurable (fun x => matrix β s n d e hde M hM hnM K θ ε η t x i j) := by
  unfold matrix
  split_ifs
  · exact measurable_activeBlock β s n d e hde M hM hnM K θ ε η t _ _
  all_goals exact measurable_const

/-- The active restriction is exactly `A₀(t)` (Subsection 6.1). -/
theorem matrix_active (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε η t : ℝ)
    (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1)) (i j : Fin (n : ℕ)) :
    matrix β s n d e hde M hM hnM K θ ε η t x (i.castLE hnM) (j.castLE hnM) =
      activeBlock β s n d e hde M hM hnM K θ ε η t x i j := by
  simp only [matrix, Fin.val_castLE, i.isLt, j.isLt, ↓reduceDIte]

/-- The coupling and exterior blocks are the exact reference,
without an exceptional-set modification (Subsection 6.1). -/
theorem matrix_exterior (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε η t : ℝ)
    (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1)) (i j : Fin (M : ℕ))
    (hij : (n : ℕ) ≤ i.val ∨ (n : ℕ) ≤ j.val) :
    matrix β s n d e hde M hM hnM K θ ε η t x i j =
      ((2 : ℝ) • referenceIntervalMatrix s M hM K) i j := by
  simp only [matrix, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> first | rfl | omega

/-- Off the common good event the whole matrix is exactly the reference,
including its active block (Subsection 6.1). -/
theorem matrix_off_goodSet (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε η t : ℝ)
    (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1)) (hx : x ∉ goodSet s n d η) :
    matrix β s n d e hde M hM hnM K θ ε η t x =
      (2 : ℝ) • referenceIntervalMatrix s M hM K := by
  ext i j
  unfold matrix
  split_ifs with hi hj
  · simp only [activeBlock, ite_eq_right hx, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact BoundaryEntries.referenceInternal_add_crossing s M hM K n hnM _ _
  all_goals rfl

/-- Symmetry of the entire actual matrix, pointwise at every size
(Subsection 6.1). -/
theorem matrix_symmetric (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε η t : ℝ)
    (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1)) (i j : Fin (M : ℕ)) :
    matrix β s n d e hde M hM hnM K θ ε η t x i j =
      matrix β s n d e hde M hM hnM K θ ε η t x j i := by
  have href : referenceIntervalMatrix s M hM K i j = referenceIntervalMatrix s M hM K j i := by
    simpa only [Matrix.conjTranspose_apply, star_trivial] using
      congrFun (congrFun (referenceIntervalMatrix_isHermitian s M hM K) j) i
  unfold matrix
  split_ifs
  · unfold activeBlock
    split_ifs <;> simp only [Matrix.add_apply]
    · rw [penaltyHessian_symmetric n θ ε x.val x.property.1,
        internalBlock_symmetric β s n d e hde t x]
      congr 1
      exact PhysicalCore.referenceIntervalBlock_symmetric s M hM K n hnM _ _ _
    · rw [show BoundaryEntries.referenceInternal s M hM K n hnM _ _ =
          BoundaryEntries.referenceInternal s M hM K n hnM _ _ from
            PhysicalCore.referenceIntervalBlock_symmetric s M hM K n hnM _ _ _,
        show BoundaryEntries.referenceCrossing s M hM K n hnM _ _ =
          BoundaryEntries.referenceCrossing s M hM K n hnM _ _ from
            PhysicalCore.referenceIntervalBlock_symmetric s M hM K n hnM _ _ _]
  all_goals rw [href]

section Intervals

variable (β : InverseTemperature) (s : Riesz1.RieszExponent)
  (n : ℕ+) (d e : ℕ) (hde : d ≤ e)
  (hn : 2*(n : ℕ) ≤ (n : ℕ)+d+1)
  (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : 2*(n : ℕ) ≤ (M : ℕ))
  (K : ℕ) (θ : PhysicalCutoff) (ε η t : ℝ)

/-- See Subsection 6.1 of the paper: the complete measurable interval coefficient
family. Physical internal coefficients retain their physical antipodal
normalization. All other intervals keep the reference coefficients. -/
def intervalWeight (i : Fin (M : ℕ)) (r : Fin ((M : ℕ)/2))
    (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1)) : ℝ :=
  if x ∈ goodSet s n d η then
    if hi : IntervalBoundary.IsInternal M n (i,r) then
      (1-t)*BoundaryEntries.conditionalIntervalWeight β s n d
        ⟨r.val, by have := (PhysicalCore.Internal.internal_iff_end_le M n hnM i r).mp hi; omega⟩
        ⟨i.val, by have := (PhysicalCore.Internal.internal_iff_end_le M n hnM i r).mp hi; omega⟩ x +
      t*BoundaryEntries.conditionalIntervalWeight β s n e
        ⟨r.val, by have := (PhysicalCore.Internal.internal_iff_end_le M n hnM i r).mp hi; omega⟩
        ⟨i.val, by have := (PhysicalCore.Internal.internal_iff_end_le M n hnM i r).mp hi; omega⟩
        (largerChart n d e hde x) +
      if r.val = 0 then penaltyHessian n θ ε x.val
        ⟨i.val, by have := (PhysicalCore.Internal.internal_iff_end_le M n hnM i r).mp hi; omega⟩
        ⟨i.val, by have := (PhysicalCore.Internal.internal_iff_end_le M n hnM i r).mp hi; omega⟩ else 0
    else BoundaryEntries.referenceWeight s M hM K (i,r)
  else BoundaryEntries.referenceWeight s M hM K (i,r)

/-- Every actual interval coefficient is Borel (Subsection 6.1). -/
theorem measurable_intervalWeight (i : Fin (M : ℕ)) (r : Fin ((M : ℕ)/2)) :
    Measurable (intervalWeight β s n d e hde hn M hM hnM K θ ε η t i r) := by
  unfold intervalWeight
  apply Measurable.ite (measurableSet_goodSet s n d η)
  split_ifs
  · apply Measurable.add
    · exact ((BoundaryEntries.measurable_conditionalIntervalWeight β s n d _ _).const_mul (1-t)).add
        (((BoundaryEntries.measurable_conditionalIntervalWeight β s n e _ _).comp
          (measurable_largerChart n d e hde)).const_mul t)
    · exact (measurable_penaltyHessian n θ ε _ _).comp measurable_subtype_coe
  · exact (((BoundaryEntries.measurable_conditionalIntervalWeight β s n d _ _).const_mul (1-t)).add
        (((BoundaryEntries.measurable_conditionalIntervalWeight β s n e _ _).comp
          (measurable_largerChart n d e hde)).const_mul t)).add measurable_const
  all_goals exact measurable_const

/-- Nonnegativity of the complete interpolation coefficient family,
including singletons and the bad-event branch (Subsection 6.1). -/
theorem intervalWeight_nonneg (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (i : Fin (M : ℕ)) (r : Fin ((M : ℕ)/2))
    (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1)) :
    0 ≤ intervalWeight β s n d e hde hn M hM hnM K θ ε η t i r x := by
  unfold intervalWeight
  split_ifs
  · exact add_nonneg (add_nonneg
      (mul_nonneg (sub_nonneg.mpr ht1) (BoundaryEntries.conditionalIntervalWeight_nonneg β s n d _ _ x))
      (mul_nonneg ht (BoundaryEntries.conditionalIntervalWeight_nonneg β s n e _ _ _)))
      (penaltyHessian_diagonal_nonneg n θ ε x.val x.property.1 _)
  · exact add_nonneg (add_nonneg
      (mul_nonneg (sub_nonneg.mpr ht1) (BoundaryEntries.conditionalIntervalWeight_nonneg β s n d _ _ x))
      (mul_nonneg ht (BoundaryEntries.conditionalIntervalWeight_nonneg β s n e _ _ _))) le_rfl
  all_goals exact BoundaryEntries.referenceWeight_nonneg s M hM K (i,r)

end Intervals

/-- A diagonal active matrix is precisely the singleton contribution
in the enlarged cyclic interval representation. The premise is local to
this finite algebra helper. -/
theorem singleton_sum_internal (n M : ℕ+) (hnM : 2*(n : ℕ) ≤ (M : ℕ))
    (F : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (hF : ∀ i j, i ≠ j → F i j = 0) (a b : Fin (n : ℕ)) :
    F a b = ∑ i : Fin (M : ℕ), ∑ r : Fin ((M : ℕ)/2),
      if hi : IntervalBoundary.IsInternal M n (i,r) then
        (if r.val = 0 then F
          ⟨i.val, by have := (PhysicalCore.Internal.internal_iff_end_le M n hnM i r).mp hi; omega⟩
          ⟨i.val, by have := (PhysicalCore.Internal.internal_iff_end_le M n hnM i r).mp hi; omega⟩ else 0)*
        (if a.castLE (by omega) ∈ cyclicIndexInterval M i (r.val+1) then 1 else 0)*
        (if b.castLE (by omega) ∈ cyclicIndexInterval M i (r.val+1) then 1 else 0)
      else 0 := by
  let r₀ : Fin ((M : ℕ)/2) := ⟨0, by have := n.pos; omega⟩
  let i₀ := a.castLE (by omega : (n : ℕ) ≤ (M : ℕ))
  have hs (i : Fin (M : ℕ)) : cyclicIndexInterval M i 1 = {i} := by
    simp only [cyclicIndexInterval, Finset.range_one, Finset.image_singleton,
      add_zero, Nat.mod_eq_of_lt i.isLt]
  symm
  rw [Finset.sum_eq_single i₀]
  · rw [Finset.sum_eq_single r₀]
    · have hi : IntervalBoundary.IsInternal M n (i₀,r₀) :=
        (PhysicalCore.Internal.internal_iff_end_le M n hnM i₀ r₀).mpr a.isLt
      rw [dite_eq_left hi]
      have hb : b.castLE (by omega : (n : ℕ) ≤ (M : ℕ)) = i₀ ↔ b = a := by
        constructor
        · exact fun h => Fin.ext (show b.val = a.val from congrArg (fun k : Fin (M : ℕ) => k.val) h)
        · rintro rfl; rfl
      by_cases hab : a = b
      · subst b
        simp [r₀, i₀, hs]
      · simp only [r₀, ite_true, zero_add, hs,
          Finset.mem_singleton, hb, ite_eq_right (Ne.symm hab), mul_zero]
        exact (hF a b hab).symm
    · intro r _ hr
      have hr0 : r.val ≠ 0 := fun h => hr (Fin.ext h)
      split_ifs <;> simp_all
    · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro r _
    by_cases hr : r.val = 0
    · have hai : a.castLE (by omega : (n : ℕ) ≤ (M : ℕ)) ≠ i := Ne.symm hi
      split_ifs <;> simp_all
    · split_ifs <;> simp_all
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

/-- See Subsection 6.1 of the paper: the exact matrix has the full positive interval
representation. This is valid at all sizes and on both event branches. -/
theorem matrix_interval_entries (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (hn : 2*(n : ℕ) ≤ (n : ℕ)+d+1)
    (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : 2*(n : ℕ) ≤ (M : ℕ))
    (K : ℕ) (θ : PhysicalCutoff) (ε η t : ℝ)
    (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1)) (a b : Fin (M : ℕ)) :
    matrix β s n d e hde M hM (by omega) K θ ε η t x a b =
      ∑ i, ∑ r, intervalWeight β s n d e hde hn M hM hnM K θ ε η t i r x *
        (if a ∈ cyclicIndexInterval M i (r.val+1) then 1 else 0)*
        (if b ∈ cyclicIndexInterval M i (r.val+1) then 1 else 0) := by
  by_cases hx : x ∈ goodSet s n d η
  · by_cases ha : a.val < (n : ℕ)
    · by_cases hb : b.val < (n : ℕ)
      · let a' : Fin (n : ℕ) := ⟨a.val,ha⟩
        let b' : Fin (n : ℕ) := ⟨b.val,hb⟩
        have hea : a'.castLE (by omega : (n : ℕ) ≤ (M : ℕ)) = a := Fin.ext rfl
        have heb : b'.castLE (by omega : (n : ℕ) ≤ (M : ℕ)) = b := Fin.ext rfl
        rw [← hea, ← heb, matrix_active]
        simp only [hea, heb]
        simp only [activeBlock, ite_eq_left hx, internalBlock, Matrix.add_apply,
          Matrix.smul_apply, smul_eq_mul]
        rw [singleton_sum_internal n M hnM (penaltyHessian n θ ε x.val)
            (penaltyHessian_off_diagonal n θ ε x.val x.property.1) a' b',
          PhysicalCore.physicalInternal_reference_intervals β s n d hn M hnM x a' b',
          PhysicalCore.physicalInternal_reference_intervals β s n e (by omega) M hnM
            (largerChart n d e hde x) a' b',
          BoundaryEntries.referenceCrossing, PhysicalCore.Internal.referenceIntervalBlock_sum]
        simp only [hea, heb, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro r _
        have hsub : cyclicIndexInterval M i (r.val+1) ⊆ BoundaryEntries.activeIndices M n ↔
            IntervalBoundary.IsInternal M n (i,r) := by
          simp only [IntervalBoundary.IsInternal, Finset.subset_iff,
            BoundaryEntries.activeIndices, Finset.mem_filter, Finset.mem_univ, true_and]
        simp only [intervalWeight, ite_eq_left hx, hsub]
        split_ifs <;> simp_all
        all_goals ring
      · rw [matrix_exterior β s n d e hde M hM (by omega) K θ ε η t x a b (Or.inr (by omega))]
        change 2*referenceIntervalMatrix s M hM K a b = _
        rw [PhysicalCore.Internal.referenceMatrix_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro r _
        by_cases hi : IntervalBoundary.IsInternal M n (i,r)
        · have hbi : b ∉ cyclicIndexInterval M i (r.val+1) := fun h => hb (hi b h)
          simp only [intervalWeight, ite_eq_left hx, dite_eq_left hi, hbi, ite_false, mul_zero]
        · simp only [intervalWeight, ite_eq_left hx, dite_eq_right hi]
    · rw [matrix_exterior β s n d e hde M hM (by omega) K θ ε η t x a b (Or.inl (by omega))]
      change 2*referenceIntervalMatrix s M hM K a b = _
      rw [PhysicalCore.Internal.referenceMatrix_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro r _
      by_cases hi : IntervalBoundary.IsInternal M n (i,r)
      · have hai : a ∉ cyclicIndexInterval M i (r.val+1) := fun h => ha (hi a h)
        simp only [intervalWeight, ite_eq_left hx, dite_eq_left hi, hai, ite_false, mul_zero, zero_mul]
      · simp only [intervalWeight, ite_eq_left hx, dite_eq_right hi]
  · rw [matrix_off_goodSet β s n d e hde M hM (by omega) K θ ε η t x hx]
    change 2*referenceIntervalMatrix s M hM K a b = _
    rw [PhysicalCore.Internal.referenceMatrix_sum]
    simp only [intervalWeight, ite_eq_right hx]

/-- See Subsection 6.1 of the paper: the exact quadratic identity in the literal
periodized matrix predicate, at every active size. -/
theorem matrix_interval_quadratic (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (hn : 2*(n : ℕ) ≤ (n : ℕ)+d+1)
    (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : 2*(n : ℕ) ≤ (M : ℕ))
    (K : ℕ) (θ : PhysicalCutoff) (ε η t : ℝ)
    (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1)) (z : Fin (M : ℕ) → ℝ) :
    (∑ a, ∑ b, z a * matrix β s n d e hde M hM (by omega) K θ ε η t x a b * z b) =
      ∑ i, ∑ r, intervalWeight β s n d e hde hn M hM hnM K θ ε η t i r x *
        (cyclicGapSum M i (r.val+1) z)^2 := by
  have h := sum_quadratic_rankOne (κ := Fin (M : ℕ) × Fin ((M : ℕ)/2)) Finset.univ
    (fun p => intervalWeight β s n d e hde hn M hM hnM K θ ε η t p.1 p.2 x)
    (fun p a => if a ∈ cyclicIndexInterval M p.1 (p.2.val+1) then (1 : ℝ) else 0) z
  simp only [Fintype.sum_prod_type] at h
  have hs (i : Fin (M : ℕ)) (r : Fin ((M : ℕ)/2)) :
      (∑ a : Fin (M : ℕ), (if a ∈ cyclicIndexInterval M i (r.val+1) then (1 : ℝ) else 0)*z a) =
        cyclicGapSum M i (r.val+1) z := by
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
    exact sum_cyclicIndexInterval_eq_cyclicGapSum M i (by have := r.isLt; omega) z
  simp only [hs] at h
  simp only [matrix_interval_entries β s n d e hde hn M hM hnM K θ ε η t x]
  exact h

/-- See Subsection 6.1 of the paper, all-size internal comparison: the original
conditional coefficient has its deterministic inverse-power lower bound
on the common rigidity event. No conditional-Hessian cutoff is used. -/
theorem internal_coefficient_lower (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (d : ℕ) (hn : 2*(n : ℕ) ≤ (n : ℕ)+d+1) (η : ℝ)
    (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1)) (hx : x ∈ goodSet s n d η)
    (i : Fin ((n : ℕ)+d+1)) (r : Fin (((n : ℕ)+d+1)/2))
    (hi : IntervalBoundary.IsInternal ((n : ℕ)+d).succPNat n (i,r)) :
    s.val*(s.val+1)*(n : ℝ)^(-(s.val+2)*η)*(r.val+1 : ℝ)^(-s.val-2) ≤
      BoundaryEntries.conditionalIntervalWeight β s n d r i x := by
  let N := ((n : ℕ)+d).succPNat
  let L := cyclicGapSum N i (r.val+1)
    (WithLp.ofLp (RetainedSimplex.chart n d ((n+d : ℕ)+1) (Equiv.refl _) (x.val,0)))
  have hL := PhysicalCore.internal_gapSum_mem β s n d x r i hi
  have hupper : L ≤ (r.val+1 : ℝ)*(n : ℝ)^η := by
    dsimp only [L]
    rw [PhysicalCore.Internal.internal_gapSum_active n d hn x.val r i hi]
    unfold cyclicGapSum
    calc
      _ ≤ ∑ _k ∈ Finset.range (r.val+1), (n : ℝ)^η :=
        Finset.sum_le_sum fun k _ => (hx.2.1 _).2
      _ = _ := by simp
  have hp := Real.rpow_le_rpow_of_nonpos hL.1 hupper
    (show -s.val-2 ≤ 0 by linarith [s.property.1])
  have he : ((r.val+1 : ℝ)*(n : ℝ)^η)^(-s.val-2) =
      (n : ℝ)^(-(s.val+2)*η)*(r.val+1 : ℝ)^(-s.val-2) := by
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ n)]
    have he : η*(-s.val-2) = -(s.val+2)*η := by ring
    rw [he, mul_comm]
  rw [he] at hp
  simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left hp
    (by have := s.property.1; positivity)).trans
      (PhysicalCore.internal_coefficient_lower β s n d x r i hi)

/-- See Subsection 6.1 of the paper: uniformly in every size and both physical
periods, a power multiple of every reference coefficient lies below the
actual interpolation coefficient. -/
theorem intervalWeight_reference_lower (s : Riesz1.RieszExponent) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (β : InverseTemperature)
      (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (hn : 2*(n : ℕ) ≤ (n : ℕ)+d+1)
      (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : 2*(n : ℕ) ≤ (M : ℕ))
      (K : ℕ) (θ : PhysicalCutoff) (ε η t : ℝ), 0 ≤ η → 0 ≤ t → t ≤ 1 →
      ∀ (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1))
        (i : Fin (M : ℕ)) (r : Fin ((M : ℕ)/2)),
      c*(n : ℝ)^(-(s.val+2)*η)*BoundaryEntries.referenceWeight s M hM K (i,r) ≤
        intervalWeight β s n d e hde hn M hM hnM K θ ε η t i r x := by
  obtain ⟨B,hB,hbound⟩ := BoundaryEntries.referenceWeight_bound s
  let c := min 1 (s.val*(s.val+1)/B)
  have hc : 0 < c := lt_min zero_lt_one (div_pos (by nlinarith [s.property.1]) hB)
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcB : c*B ≤ s.val*(s.val+1) := (le_div_iff₀ hB).mp (min_le_right _ _)
  refine ⟨c,hc,hc1,?_⟩
  intro β n d e hde hn M hM hnM K θ ε η t hη ht ht1 x i r
  let v := (n : ℝ)^(-(s.val+2)*η)
  have hv : 0 ≤ v := by dsimp only [v]; positivity
  have hv1 : v ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast n.pos) (by nlinarith [s.property.1])
  have hq1 : c*v ≤ 1 := (mul_le_of_le_one_right hc.le hv1).trans hc1
  have href : c*v*BoundaryEntries.referenceWeight s M hM K (i,r) ≤
      BoundaryEntries.referenceWeight s M hM K (i,r) :=
    mul_le_of_le_one_left (BoundaryEntries.referenceWeight_nonneg s M hM K (i,r)) hq1
  by_cases hx : x ∈ goodSet s n d η
  · by_cases hi : IntervalBoundary.IsInternal M n (i,r)
    · have hend := (PhysicalCore.Internal.internal_iff_end_le M n hnM i r).mp hi
      let i₀ : Fin ((n : ℕ)+d+1) := ⟨i.val, by omega⟩
      let r₀ : Fin (((n : ℕ)+d+1)/2) := ⟨r.val, by omega⟩
      let i₁ : Fin ((n : ℕ)+e+1) := ⟨i.val, by omega⟩
      let r₁ : Fin (((n : ℕ)+e+1)/2) := ⟨r.val, by omega⟩
      have hi₀ : IntervalBoundary.IsInternal ((n : ℕ)+d).succPNat n (i₀,r₀) :=
        (PhysicalCore.Internal.internal_iff_end_le ((n : ℕ)+d).succPNat n hn i₀ r₀).mpr hend
      have hi₁ : IntervalBoundary.IsInternal ((n : ℕ)+e).succPNat n (i₁,r₁) :=
        (PhysicalCore.Internal.internal_iff_end_le ((n : ℕ)+e).succPNat n (by change 2*(n : ℕ) ≤ (n : ℕ)+e+1; omega) i₁ r₁).mpr hend
      have hx₁ : largerChart n d e hde x ∈ goodSet s n e η := by
        refine ⟨?_, hx.2⟩
        simpa only [Nat.succPNat_coe, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using
          (largerChart n d e hde x).property.2
      have hl₀ := internal_coefficient_lower β s n d hn η x hx i₀ r₀ hi₀
      have hl₁ := internal_coefficient_lower β s n e (by omega) η
        (largerChart n d e hde x) hx₁ i₁ r₁ hi₁
      have hb : c*v*BoundaryEntries.referenceWeight s M hM K (i,r) ≤
          s.val*(s.val+1)*v*(r.val+1 : ℝ)^(-s.val-2) := by
        calc
          _ ≤ c*v*(B*(r.val+1 : ℝ)^(-s.val-2)) :=
            mul_le_mul_of_nonneg_left
              (by simpa only [Nat.cast_add, Nat.cast_one] using hbound M hM K (i,r)) (by positivity)
          _ = (c*B)*v*(r.val+1 : ℝ)^(-s.val-2) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcB hv) (by positivity)
      have h₀ : c*v*BoundaryEntries.referenceWeight s M hM K (i,r) ≤
          BoundaryEntries.conditionalIntervalWeight β s n d r₀ i₀ x := hb.trans hl₀
      have h₁ : c*v*BoundaryEntries.referenceWeight s M hM K (i,r) ≤
          BoundaryEntries.conditionalIntervalWeight β s n e r₁ i₁ (largerChart n d e hde x) := hb.trans hl₁
      have hcomb := add_le_add (mul_le_mul_of_nonneg_left h₀ (sub_nonneg.mpr ht1))
        (mul_le_mul_of_nonneg_left h₁ ht)
      have hpen : 0 ≤ if r.val = 0 then penaltyHessian n θ ε x.val
          ⟨i.val,by omega⟩ ⟨i.val,by omega⟩ else 0 := by
        split_ifs
        · exact penaltyHessian_diagonal_nonneg n θ ε x.val x.property.1 _
        · exact le_rfl
      simp only [intervalWeight, ite_eq_left hx, dite_eq_left hi]
      dsimp only [i₀,r₀,i₁,r₁] at hcomb
      change c*v*BoundaryEntries.referenceWeight s M hM K (i,r) ≤ _
      nlinarith only [hcomb,hpen]
    · simpa only [intervalWeight, ite_eq_left hx, dite_eq_right hi] using href
  · simpa only [intervalWeight, ite_eq_right hx] using href

/-- See Subsection 6.1 of the paper: the full interpolation matrix dominates the
actual truncated reference at every size. This includes all fixed exterior
blocks, rather than just the active principal block. -/
theorem matrix_reference_lower (s : Riesz1.RieszExponent) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (β : InverseTemperature)
      (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (_hn : 2*(n : ℕ) ≤ (n : ℕ)+d+1)
      (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : 2*(n : ℕ) ≤ (M : ℕ))
      (K : ℕ) (θ : PhysicalCutoff) (ε η t : ℝ), 0 ≤ η → 0 ≤ t → t ≤ 1 →
      ∀ x : AffineSimplex.chartDomain n ((n+d : ℕ)+1),
        (c*(n : ℝ)^(-(s.val+2)*η)) • ((2 : ℝ) • referenceIntervalMatrix s M hM K) ≤
          matrix β s n d e hde M hM (by omega) K θ ε η t x := by
  obtain ⟨c,hc,hc1,hcoeff⟩ := intervalWeight_reference_lower s
  refine ⟨c,hc,hc1,?_⟩
  intro β n d e hde hn M hM hnM K θ ε η t hη ht ht1 x
  let q := c*(n : ℝ)^(-(s.val+2)*η)
  let v := fun (p : Fin (M : ℕ) × Fin ((M : ℕ)/2)) (a : Fin (M : ℕ)) =>
    if a ∈ cyclicIndexInterval M p.1 (p.2.val+1) then (1 : ℝ) else 0
  let w := fun p : Fin (M : ℕ) × Fin ((M : ℕ)/2) =>
    intervalWeight β s n d e hde hn M hM hnM K θ ε η t p.1 p.2 x -
      q*BoundaryEntries.referenceWeight s M hM K p
  have he : matrix β s n d e hde M hM (by omega) K θ ε η t x -
      q • ((2 : ℝ) • referenceIntervalMatrix s M hM K) =
      ∑ p, w p • Matrix.vecMulVec (v p) (v p) := by
    ext a b
    change matrix β s n d e hde M hM (by omega) K θ ε η t x a b -
      q*(2*referenceIntervalMatrix s M hM K a b) = _
    rw [matrix_interval_entries β s n d e hde hn M hM hnM K θ ε η t x,
      PhysicalCore.Internal.referenceMatrix_sum]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      smul_eq_mul, Fintype.sum_prod_type, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro r _
    dsimp only [v,w]
    ring
  apply Matrix.le_iff.mpr
  rw [he]
  exact FiniteMatrixOrder.posSemidef_rankOneSum Finset.univ w v
    (fun p _ => sub_nonneg.mpr (hcoeff β n d e hde hn M hM hnM K θ ε η t hη ht ht1 x p.1 p.2))

/-- See Subsection 6.1 of the paper, all-size coercivity: comparison with the
truncated reference gives the explicit loss before specializing the cutoff. -/
theorem matrix_truncated_coercivity (s : Riesz1.RieszExponent) :
    ∃ c : ℝ, 0 < c ∧ ∀ (β : InverseTemperature)
      (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (_hn : 2*(n : ℕ) ≤ (n : ℕ)+d+1)
      (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : 2*(n : ℕ) ≤ (M : ℕ))
      (K : ℕ), 1 ≤ K → K ≤ (M : ℕ)/4 →
      ∀ (θ : PhysicalCutoff) (ε η t : ℝ), 0 ≤ η → 0 ≤ t → t ≤ 1 →
      ∀ x : AffineSimplex.chartDomain n ((n+d : ℕ)+1),
        (c*(n : ℝ)^(-(s.val+2)*η)*(K : ℝ)^(-1-s.val)) •
          (1 : Matrix (Fin (M : ℕ)) (Fin (M : ℕ)) ℝ) ≤
            matrix β s n d e hde M hM (by omega) K θ ε η t x := by
  obtain ⟨c,hc,_,hcompare⟩ := matrix_reference_lower s
  obtain ⟨a,ha,href⟩ := referenceIntervalMatrix_truncated_coercivity s
  refine ⟨c*2*a,by positivity,?_⟩
  intro β n d e hde hn M hM hnM K hK hKM θ ε η t hη ht ht1 x
  let q := c*(n : ℝ)^(-(s.val+2)*η)
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hh := smul_le_smul_of_nonneg_left (href M hM K hK hKM).2.2
    (mul_nonneg hq (by norm_num : (0 : ℝ) ≤ 2))
  have he : (c*2*a)*(n : ℝ)^(-(s.val+2)*η)*(K : ℝ)^(-1-s.val) =
      (q*2)*(a*(K : ℝ)^(-1-s.val)) := by dsimp only [q]; ring
  rw [he]
  have hh' : ((q*2)*(a*(K : ℝ)^(-1-s.val))) •
      (1 : Matrix (Fin (M : ℕ)) (Fin (M : ℕ)) ℝ) ≤
        q • ((2 : ℝ) • referenceIntervalMatrix s M hM K) := by
    simpa only [smul_smul] using hh
  exact hh'.trans (hcompare β n d e hde hn M hM hnM K θ ε η t hη ht ht1 x)

/-- See Subsection 6.1 of the paper: the prescribed floor cutoff gives an explicit
coercivity exponent independent of the small parameter and temperature. -/
theorem matrix_cutoff_coercivity (s : Riesz1.RieszExponent) :
    ∃ c : ℝ, 0 < c ∧ ∀ (h : ℕ) (β : InverseTemperature)
      (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (_hn : 2*(n : ℕ) ≤ (n : ℕ)+d+1)
      (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : 2*(n : ℕ) ≤ (M : ℕ))
      (θ : PhysicalCutoff) (ε η t : ℝ), 0 ≤ η → 0 ≤ t → t ≤ 1 →
      let K := ⌊(n : ℝ)^η⌋₊^h
      K ≤ (M : ℕ)/4 → ∀ x : AffineSimplex.chartDomain n ((n+d : ℕ)+1),
        (c*(n : ℝ)^(-((s.val+2)+(h : ℝ)*(1+s.val))*η)) •
          (1 : Matrix (Fin (M : ℕ)) (Fin (M : ℕ)) ℝ) ≤
            matrix β s n d e hde M hM (by omega) K θ ε η t x := by
  obtain ⟨c,hc,hbound⟩ := matrix_truncated_coercivity s
  refine ⟨c,hc,?_⟩
  intro h β n d e hde hn M hM hnM θ ε η t hη ht ht1 K hKM x
  have hn0 : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hf : 1 ≤ ⌊(n : ℝ)^η⌋₊ :=
    (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hn1 hη)
  have hK : 1 ≤ K := one_le_pow₀ hf
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hupper : (K : ℝ) ≤ (n : ℝ)^((h : ℝ)*η) := by
    calc
      _ = (⌊(n : ℝ)^η⌋₊ : ℝ)^h := by rw [Nat.cast_pow]
      _ ≤ ((n : ℝ)^η)^h := pow_le_pow_left₀ (Nat.cast_nonneg _)
        (Nat.floor_le (Real.rpow_nonneg hn0.le _)) h
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
        congr 1; ring
  have hp := Real.rpow_le_rpow_of_nonpos hK0 hupper
    (show -1-s.val ≤ 0 by linarith [s.property.1])
  have he : (n : ℝ)^(-((s.val+2)+(h : ℝ)*(1+s.val))*η) =
      (n : ℝ)^(-(s.val+2)*η)*((n : ℝ)^((h : ℝ)*η))^(-1-s.val) := by
    rw [← Real.rpow_mul hn0.le, ← Real.rpow_add hn0]
    congr 1; ring
  have hscalar : c*(n : ℝ)^(-((s.val+2)+(h : ℝ)*(1+s.val))*η) ≤
      c*(n : ℝ)^(-(s.val+2)*η)*(K : ℝ)^(-1-s.val) := by
    rw [he, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left hp (by positivity)
  exact (smul_le_smul_of_nonneg_right hscalar
    (show (0 : Matrix (Fin (M : ℕ)) (Fin (M : ℕ)) ℝ) ≤ 1 from zero_le_one)).trans
      (hbound β n d e hde hn M hM hnM K hK hKM θ ε η t hη ht ht1 x)

/-- See Subsection 6.1 of the paper, all-size internal upper bound on the actual
common chart. The active-mass premise is used only by this internal helper. Compatible admissible exteriors supply it uniformly, before choosing a point. -/
theorem internal_coefficient_upper_internal (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (d : ℕ) (hn : 2*(n : ℕ) ≤ (n : ℕ)+d+1) (η : ℝ)
    (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1)) (hx : x ∈ goodSet s n d η)
    (hmass : 2*(∑ j, x.val j) ≤ ((n+d : ℕ)+1 : ℝ))
    (i : Fin ((n : ℕ)+d+1)) (r : Fin (((n : ℕ)+d+1)/2))
    (hi : IntervalBoundary.IsInternal ((n : ℕ)+d).succPNat n (i,r)) :
    BoundaryEntries.conditionalIntervalWeight β s n d r i x ≤
      (2*(s.val*(s.val+1)*PeriodicPower.bound (s.val+2) (by linarith [s.property.1])))*
        (n : ℝ)^((s.val+2)*η)*(r.val+1 : ℝ)^(-s.val-2) := by
  let N := ((n : ℕ)+d).succPNat
  let L := cyclicGapSum N i (r.val+1)
    (WithLp.ofLp (RetainedSimplex.chart n d ((n+d : ℕ)+1) (Equiv.refl _) (x.val,0)))
  have hL := PhysicalCore.internal_gapSum_mem β s n d x r i hi
  have hend := (PhysicalCore.Internal.internal_iff_end_le N n hn i r).mp hi
  have hrepr : L = cyclicGapSum n ⟨i.val,by omega⟩ (r.val+1) (WithLp.ofLp x.val) :=
    PhysicalCore.Internal.internal_gapSum_active n d hn x.val r i hi
  have hbounds : (r.val+1 : ℝ)*(n : ℝ)^(-η) ≤ L ∧
      L ≤ (r.val+1 : ℝ)*(n : ℝ)^η := by
    rw [hrepr]
    unfold cyclicGapSum
    constructor
    · calc
        _ = ∑ _j ∈ Finset.range (r.val+1), (n : ℝ)^(-η) := by simp
        _ ≤ _ := Finset.sum_le_sum fun j _ => (hx.2.1 _).1
    · calc
        _ ≤ ∑ _j ∈ Finset.range (r.val+1), (n : ℝ)^η :=
          Finset.sum_le_sum fun j _ => (hx.2.1 _).2
        _ = _ := by simp
  have hsub : L ≤ ∑ j, x.val j := by
    rw [hrepr, InterpolationCoefficients.cyclicGapSum_filter n i.val (r.val+1) (by omega) hend]
    exact Finset.sum_le_univ_sum_of_nonneg fun j => (x.property.1 j).le
  have hhalf : 2*L ≤ (N : ℝ) := by
    have hm : 2*(∑ j, x.val j) ≤ (N : ℝ) := by
      simpa only [N, Nat.succPNat_coe, Nat.cast_add, Nat.cast_succ] using hmass
    linarith
  have hu := (InterpolationCoefficients.internal_coefficient_comparison_internal (ofLong β s) N
    (by positivity) (by positivity : (0 : ℝ) < r.val+1) ⟨L,hL⟩ hhalf hbounds.1 hbounds.2).2
  rw [PhysicalCore.internal_coefficient_formula β s n d x r i hi]
  have hc := (PhysicalEnergy.intervalCoefficient_pos (ofLong β s) N ⟨L,hL⟩).le
  change (2-if 2*(r.val+1) = (N : ℕ) then (1 : ℝ) else 0)*
    PhysicalEnergy.intervalCoefficient (ofLong β s) N ⟨L,hL⟩ ≤ _
  change PhysicalEnergy.intervalCoefficient (ofLong β s) N ⟨L,hL⟩ ≤
    (s.val*(s.val+1)*PeriodicPower.bound (s.val+2) _)*
      (n : ℝ)^((s.val+2)*η)*(r.val+1 : ℝ)^(-s.val-2) at hu
  split_ifs <;> nlinarith only [hu,hc]

namespace Internal

/-- A cutoff/Taylor split converts the coarse inverse-power estimate to
its summable error profile. -/
theorem coefficient_error_internal {s n r η h D B E P Q : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hn : 1 ≤ n) (hr : 1 ≤ r)
    (hη : 0 ≤ η) (hh : 0 ≤ h) (hD : 0 ≤ D) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (hPu : P ≤ D*n^((s+2)*η)*r^(-s-2)) (hQu : Q ≤ B*r^(-s-2))
    (hsmall : n^(h*η) ≤ r → n^η*r^(s/2) ≤ r/2 →
      |P-Q| ≤ E*(n^η*r^(-3-s/2)+r^(-s-4))) :
    |P-Q| ≤ (2*(D+B+E))*n^((s+3+h)*η)*r^(-3-s/2) := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hq : 0 ≤ r^(-3-s/2) := by positivity
  have hu : 1 ≤ n^((s+2)*η) := Real.one_le_rpow hn (by positivity)
  have hbase : |P-Q| ≤ (D+B)*n^((s+2)*η)*r^(-s-2) := by
    have hab : |P-Q| ≤ P+Q := (abs_sub P Q).trans_eq (by rw [abs_of_nonneg hP,abs_of_nonneg hQ])
    have hBu := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu hB) (by positivity : 0 ≤ r^(-s-2))
    nlinarith only [hab,hPu,hQu,hBu]
  by_cases hcut : n^(h*η) ≤ r
  swap
  · have he : r^(1-s/2)*r^(-3-s/2) = r^(-s-2) := by
      rw [← Real.rpow_add hr0]; congr 1; ring
    have hscale : r^(1-s/2) ≤ n^(h*η) :=
      (Real.rpow_le_rpow_of_exponent_le hr (by linarith : 1-s/2 ≤ 1)).trans
        (by rw [Real.rpow_one]; exact le_of_not_ge hcut)
    have ht := mul_le_mul_of_nonneg_right hscale hq
    rw [he] at ht
    have hprod := mul_le_mul_of_nonneg_left ht
      (mul_nonneg (add_nonneg hD hB) (by positivity : 0 ≤ n^((s+2)*η)))
    have hpow : n^((s+2)*η)*n^(h*η) = n^((s+2+h)*η) := by
      rw [← Real.rpow_add hn0]; congr 1; ring
    have hmon : n^((s+2+h)*η) ≤ n^((s+3+h)*η) :=
      Real.rpow_le_rpow_of_exponent_le hn (by nlinarith)
    apply hbase.trans (hprod.trans _)
    calc
      _ = (D+B)*n^((s+2+h)*η)*r^(-3-s/2) := by rw [← hpow]; ring
      _ ≤ (D+B)*n^((s+3+h)*η)*r^(-3-s/2) := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (show D+B ≤ 2*(D+B+E) by linarith) (by positivity)) hq
  by_cases htest : n^η*r^(s/2) ≤ r/2
  · have ht := hsmall hcut htest
    have hdec : r^(-s-4) ≤ r^(-3-s/2) :=
      Real.rpow_le_rpow_of_exponent_le hr (by linarith)
    have hv : n^η ≤ n^((s+3+h)*η) :=
      Real.rpow_le_rpow_of_exponent_le hn (by nlinarith)
    have hv1 : 1 ≤ n^((s+3+h)*η) := Real.one_le_rpow hn (by positivity)
    have hmajor : n^η*r^(-3-s/2)+r^(-s-4) ≤ 2*n^((s+3+h)*η)*r^(-3-s/2) := by
      nlinarith only [hdec,mul_le_mul_of_nonneg_right hv hq,mul_le_mul_of_nonneg_right hv1 hq]
    exact ht.trans ((mul_le_mul_of_nonneg_left hmajor hE).trans (by
      have hw : 0 ≤ n^((s+3+h)*η)*r^(-3-s/2) := by positivity
      nlinarith only [mul_nonneg (add_nonneg hD hB) hw]))
  · have hrpow : r^(1-s/2)*r^(s/2) = r := by
      rw [← Real.rpow_add hr0]; norm_num
    have hscale : r^(1-s/2) ≤ 2*n^η := by
      have hp : 0 < r^(s/2) := by positivity
      nlinarith only [lt_of_not_ge htest, hrpow, hp]
    have he : r^(1-s/2)*r^(-3-s/2) = r^(-s-2) := by
      rw [← Real.rpow_add hr0]; congr 1; ring
    have ht := mul_le_mul_of_nonneg_right hscale hq
    rw [he] at ht
    have hprod := mul_le_mul_of_nonneg_left ht
      (mul_nonneg (add_nonneg hD hB) (by positivity : 0 ≤ n^((s+2)*η)))
    have hpow : n^((s+2)*η)*n^η = n^((s+3)*η) := by
      rw [← Real.rpow_add hn0]; congr 1; ring
    have hmon : n^((s+3)*η) ≤ n^((s+3+h)*η) :=
      Real.rpow_le_rpow_of_exponent_le hn (by nlinarith)
    have hmajor : (D+B)*n^((s+2)*η)*(2*n^η*r^(-3-s/2)) ≤
        (2*(D+B+E))*n^((s+3+h)*η)*r^(-3-s/2) := by
      calc
        _ = 2*(D+B)*n^((s+3)*η)*r^(-3-s/2) := by rw [← hpow]; ring
        _ ≤ 2*(D+B)*n^((s+3+h)*η)*r^(-3-s/2) := by gcongr
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (show 2*(D+B) ≤ 2*(D+B+E) by linarith) (by positivity)) hq
    exact hbase.trans (hprod.trans hmajor)

end Internal

/-- See Subsection 6.1 of the paper, internal reference-error ingredient: at the
physical period every retained internal coefficient has the improved
summable error profile, including lengths below the actual floor cutoff. -/
theorem internal_coefficient_error_internal (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℕ) (β : InverseTemperature)
      (n : ℕ+) (d : ℕ) (_hn : 4*(n : ℕ) ≤ (n : ℕ)+d+1) (η : ℝ), 0 ≤ η →
      ∀ (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1)), x ∈ goodSet s n d η →
      2*(∑ j, x.val j) ≤ ((n+d : ℕ)+1 : ℝ) →
      ∀ (i : Fin ((n : ℕ)+d+1)) (r : Fin (((n : ℕ)+d+1)/2)),
      IntervalBoundary.IsInternal ((n : ℕ)+d).succPNat n (i,r) →
      |BoundaryEntries.conditionalIntervalWeight β s n d r i x -
        BoundaryEntries.referenceWeight s ((n : ℕ)+d).succPNat (by have := n.pos; simp only [Nat.succPNat_coe]; omega)
          (⌊(n : ℝ)^η⌋₊^h) (i,r)| ≤
        C*(n : ℝ)^((s.val+3+(h : ℝ))*η)*(r.val+1 : ℝ)^(-3-s.val/2) := by
  obtain ⟨B,hB,href⟩ := BoundaryEntries.referenceWeight_bound s
  obtain ⟨E,hE,htaylor⟩ := PhysicalCore.Internal.physical_sampled_error s
  let D := 2*(s.val*(s.val+1)*PeriodicPower.bound (s.val+2) (by linarith [s.property.1]))
  have hD : 0 < D := by
    dsimp only [D]
    have := s.property.1
    have := PeriodicPower.bound_pos (s.val+2) (by linarith)
    positivity
  refine ⟨2*(D+B+2*E),by positivity,?_⟩
  intro h β n d hn η hη x hx hmass i r hi
  let N := ((n : ℕ)+d).succPNat
  have hN : 2 ≤ (N : ℕ) := by have := n.pos; dsimp only [N,Nat.succPNat_coe]; omega
  have hn2 : 2*(n : ℕ) ≤ (N : ℕ) := by dsimp only [N,Nat.succPNat_coe]; omega
  have hend := (PhysicalCore.Internal.internal_iff_end_le N n hn2 i r).mp hi
  have hrn : r.val+1 ≤ (n : ℕ) := by omega
  have hanti : 2*(r.val+1) ≠ (N : ℕ) := by
    have := n.pos; dsimp only [N,Nat.succPNat_coe]; omega
  let K := ⌊(n : ℝ)^η⌋₊^h
  let P := BoundaryEntries.conditionalIntervalWeight β s n d r i x
  let Q := BoundaryEntries.referenceWeight s N hN K (i,r)
  have hPu : P ≤ D*(n : ℝ)^((s.val+2)*η)*(r.val+1 : ℝ)^(-s.val-2) :=
    internal_coefficient_upper_internal β s n d hn2 η x hx hmass i r hi
  have hQu : Q ≤ B*(r.val+1 : ℝ)^(-s.val-2) := by
    simpa only [Nat.cast_add,Nat.cast_one] using href N hN K (i,r)
  apply Internal.coefficient_error_internal (s := s.val) (n := (n : ℝ)) (r := r.val+1)
    (η := η) (h := (h : ℝ)) (D := D) (B := B) (E := 2*E) (P := P) (Q := Q)
    s.property.1 s.property.2 (by exact_mod_cast n.pos)
    (by exact_mod_cast (show 1 ≤ r.val+1 by omega)) hη (Nat.cast_nonneg h)
    hD.le hB.le (by positivity) (BoundaryEntries.conditionalIntervalWeight_nonneg β s n d r i x)
    (BoundaryEntries.referenceWeight_nonneg s N hN K (i,r)) hPu hQu
  intro hcut hsmall
  have hKu : (K : ℝ) ≤ (n : ℝ)^((h : ℝ)*η) := by
    calc
      _ = (⌊(n : ℝ)^η⌋₊ : ℝ)^h := by rw [Nat.cast_pow]
      _ ≤ ((n : ℝ)^η)^h := pow_le_pow_left₀ (Nat.cast_nonneg _)
        (Nat.floor_le (Real.rpow_nonneg (by positivity) _)) h
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ n)]
        congr 1; ring
  have hK : K ≤ r.val+1 := by exact_mod_cast hKu.trans hcut
  have hrefeq : Q = 2*sampledSecondDifference s N hN ⟨r.val+1,by have := r.isLt; omega⟩ := by
    simp only [Q,BoundaryEntries.referenceWeight,hK,ite_true,hanti,ite_false,
      Nat.mod_eq_of_lt (show r.val+1 < (N : ℕ) by have := r.isLt; dsimp only [N,Nat.succPNat_coe]; omega)]
    ring
  let L := cyclicGapSum N i (r.val+1)
    (WithLp.ofLp (RetainedSimplex.chart n d ((n+d : ℕ)+1) (Equiv.refl _) (x.val,0)))
  have hL := PhysicalCore.internal_gapSum_mem β s n d x r i hi
  have hrepr : L = cyclicGapSum n ⟨i.val,by omega⟩ (r.val+1) (WithLp.ofLp x.val) :=
    PhysicalCore.Internal.internal_gapSum_active n d hn2 x.val r i hi
  have hdev : |L-(r.val+1 : ℝ)| ≤ (n : ℝ)^η*(r.val+1 : ℝ)^(s.val/2) := by
    rw [hrepr, InterpolationCoefficients.cyclicGapSum_filter n i.val (r.val+1) (by omega) hend]
    have hh := hx.2.2 i.val (i.val+(r.val+1)) (by omega) hend
    simpa only [Nat.add_sub_cancel_left, min_eq_left s.property.2.le,
      Nat.cast_add,Nat.cast_one] using hh
  have he := htaylor β N N hN le_rfl (r.val+1) (by omega)
    (by have := r.isLt; dsimp only [N,Nat.succPNat_coe]; omega)
    ⟨L,hL⟩ ((n : ℝ)^η) (by simpa only [Nat.cast_add,Nat.cast_one] using hdev)
    (by simpa only [Nat.cast_add,Nat.cast_one] using hsmall)
  have hpeq : P = 2*PhysicalEnergy.intervalCoefficient (ofLong β s) N ⟨L,hL⟩ := by
    dsimp only [P]
    rw [PhysicalCore.internal_coefficient_formula β s n d x r i hi]
    change (2-if 2*(r.val+1) = (N : ℕ) then (1 : ℝ) else 0)*
      PhysicalEnergy.intervalCoefficient (ofLong β s) N ⟨L,hL⟩ = _
    rw [ite_eq_right hanti,sub_zero]
  change |P-Q| ≤ 2*E*((n : ℝ)^η*(r.val+1 : ℝ)^(-3-s.val/2)+(r.val+1 : ℝ)^(-s.val-4))
  rw [hpeq,hrefeq,← mul_sub,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  simpa only [ite_true,add_zero,Nat.cast_add,Nat.cast_one,mul_assoc] using
    mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 2)

/-- The exterior component indices in Subsection 6.1. These are component
labels, independent of the physical exterior gaps. -/
def exteriorIndices (M : ℕ+) (n : ℕ) : Finset (Fin (M : ℕ)) :=
  Finset.univ.filter (fun j => n ≤ j.val)

/-- The unchanged reference block `D₀` in Subsection 6.1. -/
def referenceExteriorMatrix (s : Riesz1.RieszExponent) (M : ℕ+)
    (hM : 2 ≤ (M : ℕ)) (K n : ℕ) :
    Matrix (exteriorIndices M n) (exteriorIndices M n) ℝ :=
  ((2 : ℝ) • referenceIntervalMatrix s M hM K).submatrix Subtype.val Subtype.val

/-- The reference coupling column `Ceᵢ`, written using symmetry as in
`BoundarySchurBounds.reference_column_eq` (Subsection 6.1). -/
def referenceColumn (s : Riesz1.RieszExponent) (M : ℕ+)
    (hM : 2 ≤ (M : ℕ)) (K n : ℕ) (i : Fin (M : ℕ))
    (a : exteriorIndices M n) : ℝ := 2*referenceIntervalMatrix s M hM K i a.val

section Resolvent

variable {α : Type} [MeasurableSpace α] (ν : Measure α)
  (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
  (s : Riesz1.RieszExponent) (β : InverseTemperature) (M : ℕ+)
  (hM : 2 ≤ (M : ℕ)) (K : ℕ) (hK : 1 ≤ K) (hKM : K ≤ (M : ℕ)/4) (n : ℕ)

/-- The exterior reference form `βD₀+L`, on the full product scalar form
domain (Subsection 6.1). It is meaningful for any closed scalar form, in
particular the intrinsic form of the actual interpolant. -/
def referenceExteriorForm :=
  BoundarySchurBounds.constantForm Q hQ (β.val • referenceExteriorMatrix s M hM K n)
    (((ExteriorForces.exteriorBlock_posDef s M hM hK hKM (exteriorIndices M n)).1.posSemidef).smul
      β.property.le)

/-- The full exterior resolvent is unique. The arbitrary coercivity
prefactor appears only in this proof. It is not part of the definition
of the resolvent, nor a choice of its mathematical value. -/
theorem referenceResolvent_existsUnique :
    ∃! R : PiLp 2 (fun _ : exteriorIndices M n => Lp ℝ 2 ν) →L[ℝ]
      MatrixEnergy.Vector (ι := exteriorIndices M n) Q hQ,
      ∀ f w, referenceExteriorForm ν Q hQ s β M hM K hK hKM n (R f) w =
        inner ℝ f (OperatorSchur.vectorValues Q hQ w) := by
  obtain ⟨a,ha,hlow⟩ := BoundarySchurBounds.reference_exterior_lower s M hM K hK hKM
    (exteriorIndices M n) β.val β.property
  let F := referenceExteriorForm ν Q hQ s β M hM K hK hKM n
  let J := OperatorSchur.vectorValues (ι := exteriorIndices M n) Q hQ
  have hcoerc : ∀ u, min 1 a * ‖u‖^2 ≤ F u u :=
    BoundarySchurBounds.constantForm_coercive Q hQ _ _ a hlow
  let R := CoerciveSolution.solution F (min 1 a) (lt_min zero_lt_one ha) hcoerc J
  refine ⟨R,CoerciveSolution.solution_solves F _ _ _ J,?_⟩
  intro R' hR'
  apply ContinuousLinearMap.ext
  intro f
  exact CoerciveSolution.inverse_unique F (min 1 a) (lt_min zero_lt_one ha) hcoerc
    (CoerciveSolution.forcing J f) (R' f) (hR' f)

/-- See Subsection 6.1 of the paper: the unique resolvent of `βD₀+L` on all
exterior L² sources, including the full scalar form domain. This is a
unique choice, justified by `referenceResolvent_existsUnique`. -/
def referenceResolvent :=
  Classical.choose (referenceResolvent_existsUnique ν Q hQ s β M hM K hK hKM n)

/-- The defined resolvent satisfies its complete weak equation. -/
theorem referenceResolvent_solves
    (f : PiLp 2 (fun _ : exteriorIndices M n => Lp ℝ 2 ν))
    (w : MatrixEnergy.Vector (ι := exteriorIndices M n) Q hQ) :
    referenceExteriorForm ν Q hQ s β M hM K hK hKM n
      (referenceResolvent ν Q hQ s β M hM K hK hKM n f) w =
        inner ℝ f (OperatorSchur.vectorValues Q hQ w) :=
  (Classical.choose_spec (referenceResolvent_existsUnique ν Q hQ s β M hM K hK hKM n)).1 f w

/-- Uniqueness identifies the defined resolvent with any full-domain
exterior resolvent. -/
theorem referenceResolvent_unique
    (R : PiLp 2 (fun _ : exteriorIndices M n => Lp ℝ 2 ν) →L[ℝ]
      MatrixEnergy.Vector (ι := exteriorIndices M n) Q hQ)
    (hR : ∀ f w, referenceExteriorForm ν Q hQ s β M hM K hK hKM n (R f) w =
      inner ℝ f (OperatorSchur.vectorValues Q hQ w)) :
    R = referenceResolvent ν Q hQ s β M hM K hK hKM n :=
  (Classical.choose_spec (referenceResolvent_existsUnique ν Q hQ s β M hM K hK hKM n)).2 R hR

/-- Symmetry of the full scalar-form resolvent, required when a column
increment is in its input rather than its test (Subsection 6.1). -/
theorem referenceResolvent_pair_symmetric
    (f g : PiLp 2 (fun _ : exteriorIndices M n => Lp ℝ 2 ν)) :
    inner ℝ f (OperatorSchur.vectorValues Q hQ
      (referenceResolvent ν Q hQ s β M hM K hK hKM n g)) =
    inner ℝ g (OperatorSchur.vectorValues Q hQ
      (referenceResolvent ν Q hQ s β M hM K hK hKM n f)) := by
  rw [← referenceResolvent_solves ν Q hQ s β M hM K hK hKM n f,
    ← referenceResolvent_solves ν Q hQ s β M hM K hK hKM n g]
  exact BoundarySchurBounds.constantForm_symmetric Q hQ _ _ _ _

/-- See Subsection 6.1 of the paper: the Schur contribution to a single-entry
perturbation pairing. The factor is `β²` because the defined
resolvent is `(βD₀+L)⁻¹`. Hence this is `βB(D₀+β⁻¹L)⁻¹C`. -/
def schurPointPair (φ η : Lp ℝ 2 ν) (j i : Fin (M : ℕ)) : ℝ :=
  β.val^2*inner ℝ (BoundarySchurBounds.tensor (referenceColumn s M hM K n j) φ)
    (OperatorSchur.vectorValues Q hQ (referenceResolvent ν Q hQ s β M hM K hK hKM n
      (BoundarySchurBounds.tensor (referenceColumn s M hM K n i) η)))

/-- See Subsection 6.1 of the paper: the same Schur term for an input column
increment, retaining its exact signed cancellation. -/
def schurIncrementPair (φ η : Lp ℝ 2 ν) (j i l : Fin (M : ℕ)) : ℝ :=
  β.val^2*inner ℝ (BoundarySchurBounds.tensor (referenceColumn s M hM K n j) φ)
    (OperatorSchur.vectorValues Q hQ (referenceResolvent ν Q hQ s β M hM K hK hKM n
      (BoundarySchurBounds.tensor (referenceColumn s M hM K n i-referenceColumn s M hM K n l) η)))

end Resolvent

/-- See Subsection 6.1 of the paper, Schur part of both perturbation bounds:
the actual unique exterior resolvent has the two required profiles.
The scalar form and measure are arbitrary, so no marginal/conditional
identification is inserted as an analytic hypothesis. -/
theorem schur_pair_bounds (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (β : InverseTemperature) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (K : ℕ)
      (hK : 1 ≤ K) (hKM : K ≤ (M : ℕ)/4) (n : ℕ), n ≤ (M : ℕ) →
      ∀ {α : Type} [MeasurableSpace α] (ν : Measure α)
        (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
        (φ η : Lp ℝ 2 ν) (i j l : Fin (M : ℕ)),
        i.val < n → j.val < n → l.val < n →
        |schurPointPair ν Q hQ s β M hM K hK hKM n φ η j i| ≤
          C*(K : ℝ)^2*(min (i.val+1) (n-i.val) : ℕ)^(-s.val/2)*
            (min (j.val+1) (n-j.val) : ℕ)^(-s.val/2)*‖φ‖*‖η‖ ∧
        |schurIncrementPair ν Q hQ s β M hM K hK hKM n φ η j i l| ≤
          C*(K : ℝ)^2*(Nat.dist i.val l.val : ℝ)*
            (min (j.val+1) (n-j.val) : ℕ)^(-s.val/2)*
            (min (min (i.val+1) (n-i.val)) (min (l.val+1) (n-l.val)) : ℕ)^(-1-s.val/2)*‖φ‖*‖η‖ := by
  obtain ⟨C,hC,hbound⟩ := BoundarySchurBounds.bilinear_schur_cutoff hz s β.val β.property
  refine ⟨β.val^2*C,by have := β.property; positivity,?_⟩
  intro M hM K hK hKM n hn α _ ν Q hQ φ η i j l hi hj hl
  obtain ⟨R,hR,_huniq,hest⟩ := hbound M hM K hK hKM n hn ν Q hQ
  have heq : R = referenceResolvent ν Q hQ s β M hM K hK hKM n :=
    referenceResolvent_unique ν Q hQ s β M hM K hK hKM n R hR
  rw [heq] at hest
  have hp := (hest φ η i j l hi hj hl).1
  have hd := (hest η φ j i l hj hi hl).2
  constructor
  · unfold schurPointPair
    rw [abs_mul,abs_of_nonneg (sq_nonneg β.val)]
    exact (mul_le_mul_of_nonneg_left hp (sq_nonneg β.val)).trans_eq (by
      dsimp only [referenceColumn]; ring)
  · unfold schurIncrementPair
    rw [referenceResolvent_pair_symmetric ν Q hQ s β M hM K hK hKM n,
      abs_mul,abs_of_nonneg (sq_nonneg β.val)]
    exact (mul_le_mul_of_nonneg_left hd (sq_nonneg β.val)).trans_eq (by
      dsimp only [referenceColumn]; ring)

/-- The multiplication part of `Tₜ` in Subsection 6.1, for a
given ambient physical matrix field `P`.  Both branches are the
specified physical formulas on their entire common chart. -/
def multiplicationPart (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε η t : ℝ)
    (P : AffineSimplex.chartDomain n ((n+d : ℕ)+1) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1)) : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ :=
  if x ∈ goodSet s n d η then
    β.val • (P x-internalBlock β s n d e hde t x-
      BoundaryEntries.referenceCrossing s M hM K n hnM)
  else β.val • (penaltyHessian n θ ε x.val+P x-
    ((2 : ℝ) • referenceIntervalMatrix s M hM K).submatrix
      (Fin.castLE hnM) (Fin.castLE hnM))

/-- Exact multiplication defect in Subsection 6.1. Thus adding its Schur
term to the reduced auxiliary form cancels the Schur correction with
the correct temperature normalization. No term is dropped on the bad set. -/
theorem multiplicationPart_eq_defect (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε η t : ℝ)
    (P : AffineSimplex.chartDomain n ((n+d : ℕ)+1) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1)) :
    multiplicationPart β s n d e hde M hM hnM K θ ε η t P x =
      β.val • (penaltyHessian n θ ε x.val+P x-
        activeBlock β s n d e hde M hM hnM K θ ε η t x) := by
  ext i j
  by_cases hx : x ∈ goodSet s n d η
  · simp only [multiplicationPart,activeBlock,ite_eq_left hx,Matrix.smul_apply,
      Matrix.add_apply,Matrix.sub_apply,smul_eq_mul]
    ring
  · simp only [multiplicationPart,activeBlock,ite_eq_right hx,Matrix.smul_apply,
      Matrix.add_apply,Matrix.sub_apply,Matrix.submatrix_apply,smul_eq_mul]
    rw [BoundaryEntries.referenceInternal_add_crossing s M hM K n hnM i j]

/-- The multiplication defect is Borel whenever the supplied physical
matrix field is Borel (Subsection 6.1). -/
theorem measurable_multiplicationPart (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε η t : ℝ)
    (P : AffineSimplex.chartDomain n ((n+d : ℕ)+1) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (hP : ∀ i j, Measurable (fun x => P x i j)) (i j : Fin (n : ℕ)) :
    Measurable (fun x => multiplicationPart β s n d e hde M hM hnM K θ ε η t P x i j) := by
  simp_rw [multiplicationPart_eq_defect]
  exact ((((measurable_penaltyHessian n θ ε i j).comp measurable_subtype_coe).add (hP i j)).sub
    (measurable_activeBlock β s n d e hde M hM hnM K θ ε η t i j)).const_mul β.val

/-- The complete perturbation pairing of Subsection 6.1 relative to its
supplied ambient physical field. The pairing is defined on its actual
integrability domain. The Bochner integral is never used with a junk value.
The reference resolvent acts over the given scalar form, on the same measure.
Physical coefficient and tail estimates must establish this domain for
bounded tests before applying the estimates. -/
def perturbationPair (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (hK : 1 ≤ K) (hKM : K ≤ (M : ℕ)/4)
    (θ : PhysicalCutoff) (ε η t : ℝ)
    (ν : Measure (AffineSimplex.chartDomain n ((n+d : ℕ)+1)))
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (P : AffineSimplex.chartDomain n ((n+d : ℕ)+1) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (u v : Fin (n : ℕ) → Lp ℝ 2 ν)
    (_hint : Integrable (matrixFieldPair
      (multiplicationPart β s n d e hde M hM hnM K θ ε η t P) u v) ν) : ℝ :=
  (∫ x, matrixFieldPair (multiplicationPart β s n d e hde M hM hnM K θ ε η t P) u v x ∂ν) +
    β.val^2*inner ℝ
      (∑ i : Fin (n : ℕ), BoundarySchurBounds.tensor (referenceColumn s M hM K n (i.castLE hnM)) (u i))
      (OperatorSchur.vectorValues Q hQ (referenceResolvent ν Q hQ s β M hM K hK hKM n
        (∑ i : Fin (n : ℕ), BoundarySchurBounds.tensor (referenceColumn s M hM K n (i.castLE hnM)) (v i))))

/-- See Subsection 6.1 of the paper: the physical internal matrix has summable
reference error at its own period. This internal helper states the active
mass bound explicitly. Compatible admissible fixed exteriors supply it. -/
theorem internal_entry_error_same_period_internal (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℕ) (β : InverseTemperature)
      (n : ℕ+) (d : ℕ) (_hn : 4*(n : ℕ) ≤ (n : ℕ)+d+1) (η : ℝ), 0 ≤ η →
      ∀ (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1)), x ∈ goodSet s n d η →
      2*(∑ j, x.val j) ≤ ((n+d : ℕ)+1 : ℝ) → ∀ a b : Fin (n : ℕ),
      |BoundaryEntries.physicalInternal β s n d x a b -
        BoundaryEntries.referenceInternal s ((n : ℕ)+d).succPNat
          (by have := n.pos; simp only [Nat.succPNat_coe]; omega)
          (⌊(n : ℝ)^η⌋₊^h) n (by simp only [Nat.succPNat_coe]; omega) a b| ≤
        C*(n : ℝ)^((s.val+3+(h : ℝ))*η)*
          (1+(Nat.dist a.val b.val : ℝ))^(-1-s.val/2) := by
  obtain ⟨B,hB,hbound⟩ := internal_coefficient_error_internal s
  refine ⟨B*(1+1/(1+s.val/2)),by have := s.property.1; positivity,?_⟩
  intro h β n d hn η hη x hx hmass a b
  let N := ((n : ℕ)+d).succPNat
  have hN : 2 ≤ (N : ℕ) := by have := n.pos; dsimp only [N,Nat.succPNat_coe]; omega
  have hn2 : 2*(n : ℕ) ≤ (N : ℕ) := by dsimp only [N,Nat.succPNat_coe]; omega
  have hnN : (n : ℕ) ≤ (N : ℕ) := by omega
  let K := ⌊(n : ℝ)^η⌋₊^h
  let F := fun (i : Fin (N : ℕ)) (r : Fin ((N : ℕ)/2)) =>
    if IntervalBoundary.IsInternal N n (i,r) then
      BoundaryEntries.conditionalIntervalWeight β s n d r i x -
        BoundaryEntries.referenceWeight s N hN K (i,r)
    else 0
  have hF (i) (r) : |F i r| ≤ (B*(n : ℝ)^((s.val+3+(h : ℝ))*η))*
      (r.val+1 : ℝ)^(-(1+s.val/2)-2) := by
    dsimp only [F]
    split_ifs with hi
    · simpa only [show -(1+s.val/2)-2 = -3-s.val/2 by ring] using
        hbound h β n d hn η hη x hx hmass i r hi
    · rw [abs_zero]; positivity
  have hb := PhysicalCore.Internal.signed_interval_entry_bound N
    (by linarith [s.property.1] : 0 < 1+s.val/2) (by positivity) F hF
    (a.castLE hnN) (b.castLE hnN)
  have he : BoundaryEntries.physicalInternal β s n d x a b -
      BoundaryEntries.referenceInternal s N hN K n hnN a b =
      ∑ i, ∑ r, F i r*(if a.castLE hnN ∈ cyclicIndexInterval N i (r.val+1) then 1 else 0)*
        (if b.castLE hnN ∈ cyclicIndexInterval N i (r.val+1) then 1 else 0) := by
    rw [PhysicalCore.physicalInternal_reference_intervals β s n d hn2 N hn2 x a b,
      BoundaryEntries.referenceInternal,PhysicalCore.Internal.referenceIntervalBlock_sum,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    have hsub : cyclicIndexInterval N i (r.val+1) ⊆ BoundaryEntries.activeIndices N n ↔
        IntervalBoundary.IsInternal N n (i,r) := by
      simp only [IntervalBoundary.IsInternal,Finset.subset_iff,BoundaryEntries.activeIndices,
        Finset.mem_filter,Finset.mem_univ,true_and]
    simp only [hsub,F]
    by_cases hi : IntervalBoundary.IsInternal N n (i,r)
    · simp only [hi,ite_true,dite_true]
      by_cases ha : a.castLE hnN ∈ cyclicIndexInterval N i (r.val+1) <;>
        by_cases hc : b.castLE hnN ∈ cyclicIndexInterval N i (r.val+1) <;>
          simp only [ha,hc,and_self,and_false,false_and,ite_true,ite_false,
            mul_one,mul_zero,sub_self]
      all_goals rfl
    · simp only [hi,ite_false,dite_false,zero_mul,sub_zero]
  rw [he]
  rw [PhysicalCore.Internal.active_distance N n hn2 a b] at hb
  simpa only [show -(1+s.val/2) = -1-s.val/2 by ring,mul_assoc,mul_left_comm,mul_comm] using hb

end Riesz2.InterpolationMatrix
