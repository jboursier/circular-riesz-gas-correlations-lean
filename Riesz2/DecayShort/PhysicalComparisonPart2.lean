/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.PhysicalComparison
import all Riesz2.DecayShort.ExceptionalEventPart4

/-!
# Further bounds for the auxiliary physical matrices

Measurability, symmetry, and deterministic estimates for the auxiliary fields of Subsection 4.5.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal ContDiff

namespace Riesz2.DecayShort.PhysicalComparison

/-- Measurability of the full coefficient event of Subsection 4.4,
including the actual finite exterior gradient energies. -/
theorem measurableSet_coefficientEvent (p : Parameters) (hs : 1 < p.val.2)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (h : ℝ) (hh : 0 < h) (D : ℝ) :
    MeasurableSet (ExceptionalEvent.coefficientEvent p n m
      (by simp only [Nat.succPNat_coe]; omega) D) := by
  classical
  obtain ⟨Cθ,hCθ,hcurv,_⟩ := θ.property.2.2.2.2
  obtain ⟨_,_,hV⟩ := activeTilt_conditional_exterior_energy_moments p.val.2 p.val.1 p.val.1
    h Cθ hs p.property.1 le_rfl hh hCθ
  have hmV (i : Fin (n : ℕ)) : Measurable (fun x =>
      (PhysicalFibres.exteriorGradientEnergy p n m n.pos x i).toReal) :=
    (hV p rfl le_rfl le_rfl n m (by simp only [Nat.succPNat_coe]; omega)
      θ hcurv false i 1 le_rfl).1
  have hmH (i j : Fin ((n : ℕ) + m + 1)) :=
    measurable_conditional_intervalMatrix p n m n.pos _ le_rfl i j
  have hall {ι : Type} [Countable ι] {P : ι →
      AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → Prop}
      (hm : ∀ i, MeasurableSet {x | P i x}) : MeasurableSet {x | ∀ i, P i x} := by
    simpa only [ofPred_forall] using MeasurableSet.iInter hm
  unfold ExceptionalEvent.coefficientEvent
  simp only [ofPred_and]
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ (MeasurableSet.inter ?_
    (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_))))
  · apply hall
    intro i
    apply hall
    intro j
    exact measurableSet_le
      (measurable_conditional_intervalMatrix p n m n.pos _ _ i j) measurable_const
  · apply hall
    intro k
    exact measurableSet_le
      ((measurable_physical_boundary_coefficients p n m n.pos _).1 _) measurable_const
  · apply hall
    intro k
    exact measurableSet_le
      ((measurable_physical_boundary_coefficients p n m n.pos _).2.1 _) measurable_const
  · exact measurableSet_le ((measurable_physical_boundary_coefficients p n m n.pos _).2.2)
      measurable_const
  · apply hall
    intro i
    apply measurableSet_le _ measurable_const
    exact ((Finset.measurable_sum _ fun a _ => hmH _ a).const_mul _).add
      ((Finset.measurable_sum _ fun a _ =>
        Finset.measurable_sum _ fun b _ => hmH a b).const_mul _)
  · exact hall fun i => measurableSet_le (hmV i) measurable_const

/-- The auxiliary physical good event for Subsection 4.4 is measurable. -/
theorem measurableSet_properGoodEvent (p : Parameters) (hs : 1 < p.val.2)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (h : ℝ) (hh : 0 < h) (D : ℝ) :
    MeasurableSet (ExceptionalEvent.properGoodEvent p n m
      (by simp only [Nat.succPNat_coe]; omega) h D) := by
  apply MeasurableSet.inter _ (measurableSet_coefficientEvent p hs n m θ h hh D)
  exact (ExceptionalEvent.measurableSet_goodBlockEvent _ _ _ _).preimage
    (by fun_prop)

/-- The Hessian convention agrees entrywise with the second
Fréchet derivative wherever the potential is twice smooth. -/
theorem hessianMatrix_entry {n : ℕ} {V : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hV : ContDiffAt ℝ 2 V x) (i j : Fin n) :
    hessianMatrix V x i j =
      fderiv ℝ (fderiv ℝ V) x (EuclideanSpace.single j 1) (EuclideanSpace.single i 1) := by
  have he := Riesz1.inner_fderiv_gradient
    ((hV.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)
  simpa [hessianMatrix, EuclideanSpace.single, PiLp.inner_apply, RCLike.inner_apply,
    PiLp.single_apply] using he

/-- Smooth Hessians are symmetric, in the matrix convention. -/
theorem hessianMatrix_symm {n : ℕ} {V : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hV : ContDiffAt ℝ 2 V x) (i j : Fin n) :
    hessianMatrix V x i j = hessianMatrix V x j i := by
  rw [hessianMatrix_entry hV, hessianMatrix_entry hV]
  exact hV.isSymmSndFDerivAt (by norm_num) _ _

/-- Twice continuously differentiable potentials have measurable Hessian
entries on an open domain. -/
theorem measurable_hessianMatrix {n : ℕ} {V : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hV : ContDiffOn ℝ ∞ V U)
    (i j : Fin n) : Measurable (fun x : U => hessianMatrix V x.val i j) := by
  apply Continuous.measurable
  apply continuous_iff_continuousAt.mpr
  intro x
  have hx := hV.contDiffAt (hU.mem_nhds x.property)
  have he : (fun y : U => hessianMatrix V y.val i j) =
      fun y : U => fderiv ℝ (fderiv ℝ V) y.val
        (EuclideanSpace.single j 1) (EuclideanSpace.single i 1) := by
    funext y
    exact hessianMatrix_entry ((hV.contDiffAt (hU.mem_nhds y.property)).of_le (by norm_num)) i j
  rw [he]
  exact (((hx.fderiv_right (m := 2) (by norm_num)).continuousAt_fderiv
    (by norm_num)).clm_apply continuousAt_const).clm_apply continuousAt_const |>.comp
      continuous_subtype_val.continuousAt

set_option backward.isDefEq.respectTransparency false in
/-- Measurability and symmetry clauses of Subsection 4.5 for both
auxiliary fields, on the entire positive retained carrier. -/
theorem frozenMatrices_measurable_symmetric (p : Parameters) (hs : 1 < p.val.2)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (h : ℝ) (hh : 0 < h) (b : Bool) (D : ℝ) :
    (∀ i j, Measurable (fun x => frozenPhysicalMatrix p n m θ h b D x i j)) ∧
    (∀ i j, Measurable (fun x => frozenInternalMatrix p n m θ h b D x i j)) ∧
    (∀ x i j, frozenPhysicalMatrix p n m θ h b D x i j =
      frozenPhysicalMatrix p n m θ h b D x j i) ∧
    (∀ x i j, frozenInternalMatrix p n m θ h b D x i j =
      frozenInternalMatrix p n m θ h b D x j i) := by
  classical
  let F := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
    ∑ i, (θ.val (((n : ℝ) ^ h)⁻¹ * y i) +
      if b then θ.val (((n : ℝ) ^ h)⁻¹ * (y i)⁻¹) else 0)
  let K := fun y => p.val.1⁻¹ * (p.val.1 * F y -
    Real.log (∫ z : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,z)).toReal))
  have hF := (ExceptionalEvent.penalty_smooth_convex n ((n + m : ℕ) + 1) θ
    (inv_pos.mpr (Real.rpow_pos_of_pos (show (0 : ℝ) < n by exact_mod_cast n.pos) h)) b).1
  have hK := (PhysicalFibres.active_marginal_curvature p hs n m n.pos (Equiv.refl _) θ h hh b).1
  have hB := measurableSet_properGoodEvent p hs n m θ h hh D
  have hmI (i j : Fin (n : ℕ)) : Measurable (fun x => IntervalBoundary.internalMatrix
      ((n : ℕ) + m).succPNat n (by simp only [Nat.succPNat_coe]; omega)
      (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x) i j) := by
    apply Finset.measurable_sum
    intro t _
    split_ifs
    · exact (measurable_conditionalIntervalWeight p n m n.pos (Equiv.refl _) t).mul_const _
    · exact measurable_const
  refine ⟨fun i j => ?_, fun i j => ?_, fun x i j => ?_, fun x i j => ?_⟩
  · have hm : Measurable (fun x => if x ∈ ExceptionalEvent.properGoodEvent p n m
        (by simp only [Nat.succPNat_coe]; omega) h D then hessianMatrix K x.val i j
        else (1 : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ) i j) := Measurable.ite hB
      (measurable_hessianMatrix (AffineSimplex.isOpen_chartDomain _ _) hK i j)
      (measurable_const (a := (1 : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ) i j))
    convert hm using 1
    funext x
    by_cases hx : x ∈ ExceptionalEvent.properGoodEvent p n m
      (by simp only [Nat.succPNat_coe]; omega) h D
    · simp only [frozenPhysicalMatrix, ite_eq_left hx, K, F]
    · simp only [frozenPhysicalMatrix, ite_eq_right hx]
  · have hm : Measurable (fun x => if x ∈ ExceptionalEvent.properGoodEvent p n m
        (by simp only [Nat.succPNat_coe]; omega) h D then hessianMatrix F x.val i j +
        IntervalBoundary.internalMatrix ((n : ℕ) + m).succPNat n
          (by simp only [Nat.succPNat_coe]; omega)
          (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x) i j
        else (1 : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ) i j) := Measurable.ite hB
      ((measurable_hessianMatrix (AffineSimplex.isOpen_chartDomain _ _) hF i j).add (hmI i j))
      (measurable_const (a := (1 : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ) i j))
    convert hm using 1
    funext x
    by_cases hx : x ∈ ExceptionalEvent.properGoodEvent p n m
      (by simp only [Nat.succPNat_coe]; omega) h D
    · simp only [frozenInternalMatrix, ite_eq_left hx, Matrix.add_apply, F]
    · simp only [frozenInternalMatrix, ite_eq_right hx]
  · change (if x ∈ ExceptionalEvent.properGoodEvent p n m
      (by simp only [Nat.succPNat_coe]; omega) h D then hessianMatrix K x.val else 1) i j =
        (if x ∈ ExceptionalEvent.properGoodEvent p n m
      (by simp only [Nat.succPNat_coe]; omega) h D then hessianMatrix K x.val else 1) j i
    by_cases hx : x ∈ ExceptionalEvent.properGoodEvent p n m
      (by simp only [Nat.succPNat_coe]; omega) h D
    · simp only [ite_eq_left hx]
      exact hessianMatrix_symm ((hK.contDiffAt
        ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds x.property)).of_le (by norm_num)) i j
    · simp only [ite_eq_right hx]
      exact (Matrix.isSymm_one.apply i j).symm
  · change (if x ∈ ExceptionalEvent.properGoodEvent p n m
      (by simp only [Nat.succPNat_coe]; omega) h D then hessianMatrix F x.val + _ else 1) i j =
        (if x ∈ ExceptionalEvent.properGoodEvent p n m
      (by simp only [Nat.succPNat_coe]; omega) h D then hessianMatrix F x.val + _ else 1) j i
    by_cases hx : x ∈ ExceptionalEvent.properGoodEvent p n m
      (by simp only [Nat.succPNat_coe]; omega) h D
    · simp only [ite_eq_left hx, Matrix.add_apply]
      rw [hessianMatrix_symm ((hF.contDiffAt
        ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds x.property)).of_le (by norm_num)) i j,
        IntervalBoundary.internalMatrix_symm]
    · simp only [ite_eq_right hx]
      exact (Matrix.isSymm_one.apply i j).symm

/-- The active penalty is twice smooth at every positive point. -/
theorem penalty_contDiffAt (n : ℕ) (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (b : Bool) (x : EuclideanSpace ℝ (Fin n)) (hx : ∀ i, 0 < x i) :
    ContDiffAt ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) =>
      ∑ i, (θ.val (a * y i) + if b then θ.val (a * (y i)⁻¹) else 0)) x := by
  let L := (∑ i, x i) + 1
  have hxL : x ∈ AffineSimplex.chartDomain n L := ⟨hx, by dsimp [L]; linarith⟩
  exact ((ExceptionalEvent.penalty_smooth_convex n L θ ha b).1.contDiffAt
    ((AffineSimplex.isOpen_chartDomain n L).mem_nhds hxL)).of_le (by norm_num)

/-- The penalty in Subsection 4.5 has no mixed coordinate entries. -/
theorem penalty_hessian_off_diagonal (n : ℕ) (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (b : Bool) (x : EuclideanSpace ℝ (Fin n)) (hx : ∀ i, 0 < x i)
    (i j : Fin n) (hij : i ≠ j) :
    hessianMatrix (fun y : EuclideanSpace ℝ (Fin n) =>
      ∑ k, (θ.val (a * y k) + if b then θ.val (a * (y k)⁻¹) else 0)) x i j = 0 := by
  classical
  let φ := fun t : ℝ => θ.val (a * t) + if b then θ.val (a * t⁻¹) else 0
  have hφ (t : ℝ) (ht : 0 < t) : ContDiffAt ℝ 2 φ t := by
    have h₁ := (PhysicalCollision.cutoff_contDiffAt θ (mul_pos ha ht)).comp t
      (contDiffAt_const.mul contDiffAt_id)
    cases b
    · simpa only [φ, Bool.false_eq_true, ↓reduceIte, add_zero, Function.comp_def] using
        h₁.of_le (by norm_num)
    · have h₂ := (PhysicalCollision.cutoff_contDiffAt θ (mul_pos ha (inv_pos.mpr ht))).comp t
        (contDiffAt_const.mul (contDiffAt_id.inv ht.ne'))
      simpa only [φ, ↓reduceIte, Function.comp_def, Pi.inv_apply, id_eq] using (h₁.add h₂).of_le (by norm_num)
  rw [hessianMatrix_entry (penalty_contDiffAt n θ ha b x hx)]
  have he := (finite_linear_potential_derivatives (fun _ : Fin n => (1 : ℝ))
    (fun _ => φ) (fun k => EuclideanSpace.proj k) (fun _ => Ioi (0 : ℝ))
    (fun _ => isOpen_Ioi) (fun _ t ht => (hφ t ht).contDiffWithinAt) x hx
    (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)).2
  simpa [φ, EuclideanSpace.single, PiLp.single_apply, hij, Ne.symm hij] using he

/-- Uniform diagonal penalty bound on the actual good event, with a
polynomial loss and no factor of the component cardinality (Subsection 4.5). -/
theorem penalty_hessian_good_bound (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Parameters) (n : ℕ+) (m : ℕ) (h : ℝ), 0 < h →
      ∀ (b : Bool) (D : ℝ) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)),
      x ∈ ExceptionalEvent.properGoodEvent p n m
        (by simp only [Nat.succPNat_coe]; omega) h D → ∀ i : Fin (n : ℕ),
      let F := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
        ∑ k, (θ.val (((n : ℝ) ^ h)⁻¹ * y k) +
          if b then θ.val (((n : ℝ) ^ h)⁻¹ * (y k)⁻¹) else 0)
      |hessianMatrix F x.val i i| ≤ C * (n : ℝ) ^ (4 * h) := by
  obtain ⟨C,hC,hdiag⟩ := ExceptionalEvent.internal_penalty_diagonal θ
  refine ⟨2 * C, by positivity, ?_⟩
  intro p n m h hh b D x hx i F
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have ha := inv_pos.mpr (Real.rpow_pos_of_pos hn0 h)
  have ha1 : ((n : ℝ) ^ h)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_rpow hn1 hh.le)
  have hFx := penalty_contDiffAt n θ ha b x.val x.property.1
  have hnonneg : 0 ≤ hessianMatrix F x.val i i := by
    rw [hessianMatrix_entry hFx]
    have hconv := (ExceptionalEvent.penalty_smooth_convex n ((n + m : ℕ) + 1) θ ha b).2
    exact Riesz1.fderiv_fderiv_nonneg_of_convexOn (AffineSimplex.isOpen_chartDomain _ _)
      hconv.1 hconv ((ExceptionalEvent.penalty_smooth_convex n ((n + m : ℕ) + 1) θ ha b).1.of_le
        (by norm_num)) x.property _
  rw [abs_of_nonneg hnonneg, hessianMatrix_entry hFx]
  have hlower : (n : ℝ) ^ (-h) ≤ x.val i := (hx.1.2.1 i).1
  have hi : (x.val i)⁻¹ ≤ (n : ℝ) ^ h := by
    have he : (n : ℝ) ^ (-h) = ((n : ℝ) ^ h)⁻¹ := Real.rpow_neg hn0.le h
    rw [he] at hlower
    have hb := inv_le_inv₀ (x.property.1 i) (inv_pos.mpr (Real.rpow_pos_of_pos hn0 h))
    simpa only [inv_inv] using hb.mpr hlower
  have h4 : (x.val i)⁻¹ ^ 4 ≤ (n : ℝ) ^ (4 * h) := by
    have hb := pow_le_pow_left₀ (inv_nonneg.mpr (x.property.1 i).le) hi 4
    calc
      _ ≤ ((n : ℝ) ^ h) ^ 4 := hb
      _ = (n : ℝ) ^ (4 * h) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
        congr 1
        ring
  have hpow : 1 ≤ (n : ℝ) ^ (4 * h) := Real.one_le_rpow hn1 (by linarith)
  exact (hdiag n _ ha ha1 b x.val x.property.1 i).trans (by nlinarith)

/-- Ordinary and inherited cyclic distances coincide on an active block of
at most half the cycle, including the singleton block (Subsection 4.5). -/
theorem properBlock_distance (N : ℕ+) (n : ℕ) (hn : n ≤ (N : ℕ))
    (hhalf : 2 * n ≤ (N : ℕ)) (i j : Fin n) :
    (Riesz1.cyclicIndexDistance N (Fin.castLE hn i) (Fin.castLE hn j) : ℝ) =
      |(i.val : ℝ) - (j.val : ℝ)| := by
  have hd : Nat.dist i.val j.val ≤ (N : ℕ) - Nat.dist i.val j.val := by
    have hi := i.isLt
    have hj := j.isLt
    unfold Nat.dist
    omega
  rw [Riesz1.cyclicIndexDistance, Fin.val_castLE, Fin.val_castLE, min_eq_left hd]
  rcases le_total i.val j.val with hle | hle
  · rw [Nat.dist_eq_sub_of_le hle, Nat.cast_sub hle, abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast hle))]
    ring
  · rw [Nat.dist_eq_sub_of_le_right hle, Nat.cast_sub hle, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hle))]


/-- Complete ordinary-distance entry estimate for the auxiliary internal
matrix in Subsection 4.5, including the diagonal penalty and the
prescribed exceptional value. The constant precedes all sizes and scales. -/
theorem frozenInternalMatrix_entry_bound (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Parameters) (n : ℕ+) (m : ℕ),
      2 * (n : ℕ) ≤ (n : ℕ) + m + 1 → ∀ h : ℝ, 0 < h → ∀ (b : Bool) (D : ℝ),
      0 ≤ D → ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (i j : Fin (n : ℕ)),
        |frozenInternalMatrix p n m θ h b D x i j| ≤
          (1 + D + C * (n : ℝ) ^ (4 * h)) *
            (1 + |(i.val : ℝ) - (j.val : ℝ)|) ^ (-p.val.2) := by
  classical
  obtain ⟨C,hC,hpen⟩ := penalty_hessian_good_bound θ
  refine ⟨C,hC,?_⟩
  intro p n m hhalf h hh b D hD x i j
  let F := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
    ∑ k, (θ.val (((n : ℝ) ^ h)⁻¹ * y k) +
      if b then θ.val (((n : ℝ) ^ h)⁻¹ * (y k)⁻¹) else 0)
  let N := ((n : ℕ) + m).succPNat
  have hn : (n : ℕ) ≤ (N : ℕ) := by change (n : ℕ) ≤ (n : ℕ) + m + 1; omega
  let I := IntervalBoundary.internalMatrix N n hn
    (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
  let r := (1 + |(i.val : ℝ) - (j.val : ℝ)|) ^ (-p.val.2)
  have hr : 0 ≤ r := Real.rpow_nonneg (by positivity) _
  by_cases hx : x ∈ ExceptionalEvent.properGoodEvent p n m hn h D
  · have hIb : |I i j| ≤ D * r := by
      rw [abs_of_nonneg (IntervalBoundary.internalMatrix_nonneg N n hn _
        (conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x) i j)]
      apply (IntervalBoundary.internalMatrix_le_intervalMatrix N n hn _
        (conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x) i j).trans
      have he := hx.2.1 i j
      rw [properBlock_distance N n hn (by simpa only [N, Nat.succPNat_coe] using hhalf)] at he
      exact he
    have hFb : |hessianMatrix F x.val i j| ≤ C * (n : ℝ) ^ (4 * h) * r := by
      by_cases hij : i = j
      · subst j
        simpa only [r, sub_self, abs_zero, add_zero, Real.one_rpow, mul_one] using
          hpen p n m h hh b D x hx i
      · rw [penalty_hessian_off_diagonal n θ
          (inv_pos.mpr (Real.rpow_pos_of_pos (show (0 : ℝ) < n by exact_mod_cast n.pos) h))
          b x.val x.property.1 i j hij, abs_zero]
        positivity
    change |(if x ∈ ExceptionalEvent.properGoodEvent p n m hn h D then
      hessianMatrix F x.val + I else 1) i j| ≤ _
    rw [ite_eq_left hx, Matrix.add_apply]
    calc
      _ ≤ |hessianMatrix F x.val i j| + |I i j| := abs_add_le _ _
      _ ≤ C * (n : ℝ) ^ (4 * h) * r + D * r := add_le_add hFb hIb
      _ ≤ (1 + D + C * (n : ℝ) ^ (4 * h)) * r := by nlinarith
  · rw [(frozenMatrices_off_event p n m θ h b D x hx).2]
    by_cases hij : i = j
    · subst j
      simp only [Matrix.one_apply_eq, sub_self, abs_zero, add_zero, Real.one_rpow, mul_one, abs_one]
      nlinarith [mul_nonneg hC.le (Real.rpow_nonneg (show (0 : ℝ) ≤ n by positivity) (4 * h))]
    · simp only [Matrix.one_apply_ne hij, abs_zero]
      positivity

/-- Covariance contributes a nonnegative quadratic form, so it can be
removed in the upper estimate of Subsection 4.5. -/
theorem internal_covariance_quadratic_nonneg {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (X : ι → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 ρ) (z : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, z i * ProbabilityTheory.covariance (X i) (X j) ρ * z j := by
  have hY (i) : MemLp (fun x => z i * X i x) 2 ρ := (hX i).const_mul _
  have he := ProbabilityTheory.covariance_fun_sum_fun_sum hY hY
  simp only [ProbabilityTheory.covariance_const_mul_left,
    ProbabilityTheory.covariance_const_mul_right] at he
  have hn : 0 ≤ ProbabilityTheory.covariance (fun x => ∑ i, z i * X i x)
      (fun x => ∑ i, z i * X i x) ρ := by
    unfold ProbabilityTheory.covariance
    exact integral_nonneg fun x => mul_self_nonneg _
  rw [he] at hn
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hn

/-- Restriction of complete interval matrices retains the ambient labels.
This bridge uses the existing interval encoding on both sides. -/
theorem intervalMatrix_restrict (N : ℕ+) (n : ℕ) (hn : n ≤ (N : ℕ))
    (A : Fin (N : ℕ) × Fin ((N : ℕ) / 2) → ℝ) (i j : Fin n) :
    IntervalBoundary.intervalMatrix N (N : ℕ) le_rfl A (Fin.castLE hn i) (Fin.castLE hn j) =
      IntervalBoundary.intervalMatrix N n hn A i j := by
  classical
  simp only [IntervalBoundary.intervalMatrix, IntervalBoundary.rankOne,
    IntervalBoundary.trace, Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Upper bound for the marginal Hessian before coefficient estimates
(Subsection 4.5). Covariance is discarded as a whole positive
semidefinite matrix. The exterior mode is the exact averaged ambient
Hessian, rather than a bound through the trace of the marginal Hessian. -/
theorem physical_hessian_quadratic_upper (p : Parameters) (n : ℕ+) (m : ℕ)
    (θ : PhysicalCutoff) (h : ℝ) (_hh : 0 < h) (b : Bool)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (z : Fin (n : ℕ) → ℝ) :
    let F := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      ∑ i, (θ.val (((n : ℝ) ^ h)⁻¹ * y i) +
        if b then θ.val (((n : ℝ) ^ h)⁻¹ * (y i)⁻¹) else 0)
    let K := fun y => p.val.1⁻¹ * (p.val.1 * F y -
      Real.log (∫ w : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,w)).toReal))
    let N := ((n : ℕ) + m).succPNat
    let hn : (n : ℕ) ≤ (N : ℕ) := by change (n : ℕ) ≤ (n : ℕ) + m + 1; omega
    let A := conditionalIntervalWeight p n m n.pos (Equiv.refl _) x
    let P := IntervalBoundary.intervalMatrix N n hn A
    let H := IntervalBoundary.intervalMatrix N (N : ℕ) le_rfl A
    let S := Finset.univ.filter (fun a : Fin (N : ℕ) => (n : ℕ) ≤ a.val)
    let c := (m + 1 : ℝ)⁻¹ ^ 2 * ∑ a ∈ S, ∑ b ∈ S, H a b
    (∑ i, ∑ j, z i * hessianMatrix K x.val i j * z j) ≤
      (∑ i, ∑ j, z i * hessianMatrix F x.val i j * z j) +
        2 * (∑ i, ∑ j, z i * P i j * z j) + 2 * c * (∑ i, z i) ^ 2 := by
  classical
  intro F K N hn A P H S c
  have ha := inv_pos.mpr (Real.rpow_pos_of_pos (show (0 : ℝ) < n by exact_mod_cast n.pos) h)
  obtain ⟨U,hU,hv,hK,hm⟩ := PhysicalFibres.active_marginal_hessian p n m n.pos θ ha b
  obtain ⟨ρ,hρ,hmap,hB,hXi,he⟩ := hm x
  let _ := hρ
  let q : EuclideanSpace ℝ (Fin (N : ℕ)) := WithLp.toLp 2 (Fin.append (fun _ : Fin (n : ℕ) => (0 : ℝ))
    (fun _ : Fin (m + 1) => (m + 1 : ℝ)⁻¹))
  let e := fun i : Fin (n : ℕ) => EuclideanSpace.single (Fin.castLE hn i) (1 : ℝ)
  let B := Matrix.toBilin (EuclideanSpace.basisFun (Fin (N : ℕ)) ℝ).toBasis H
  have hBa (u v : EuclideanSpace ℝ (Fin (N : ℕ))) :
      B u v = ∑ a, ∑ b, u a * H a b * v b := by
    simp only [B, Matrix.toBilin_apply, OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
  let Z := ∑ i, z i • e i
  have hmean (u v : EuclideanSpace ℝ (Fin (N : ℕ))) :
      (∫ w, p.val.1⁻¹ * fderiv ℝ (fderiv ℝ U)
        (MarginalHessian.compensatedChart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,w)) u v ∂ρ) =
          B u v := by
    rw [hBa]
    exact ExceptionalEvent.internal_centred_hessian_mean p n m n.pos U hv x ρ hmap u v
  have hq (a : Fin (N : ℕ)) : q a = if (n : ℕ) ≤ a.val then (m + 1 : ℝ)⁻¹ else 0 := by
    exact Fin.addCases (m := (n : ℕ)) (n := m + 1)
      (fun j => by simp [q, Fin.append, j.isLt])
      (fun j => by simp [q, Fin.append, Fin.val_natAdd]) a
  have hqq : B q q = c := by
    rw [hBa]
    simp only [hq, c, S, Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs
    · apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> ring
    · simp
  have hee (i j) : B (e i) (e j) = P i j := by
    rw [hBa]
    simp only [e, EuclideanSpace.single, PiLp.single_apply,
      mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact intervalMatrix_restrict N n hn A i j
  have hBsym (u v) : B u v = B v u := by
    simp only [hBa]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [show H b a = H a b from IntervalBoundary.intervalMatrix_symm N _ _ A b a]
    ring
  have hBnn (u) : 0 ≤ B u u := by
    have hpsd : H.PosSemidef := by
      have hi := IntervalBoundary.internal_add_boundary N (N : ℕ) le_rfl A
      change (IntervalBoundary.intervalMatrix N (N : ℕ) le_rfl A).PosSemidef
      rw [← hi]
      exact (IntervalBoundary.internalMatrix_posSemidef N _ _ A
        (conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x)).add
        (IntervalBoundary.boundaryMatrix_posSemidef N _ _ A
          (conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x))
    have hp := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 (WithLp.ofLp u)
    simpa only [hBa, dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum, mul_assoc] using hp
  let Xi := fun i w => p.val.1⁻¹ * (fderiv ℝ U
    (MarginalHessian.compensatedChart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,w)) (e i) -
    fderiv ℝ U (MarginalHessian.compensatedChart n m ((n + m : ℕ) + 1)
      (Equiv.refl _) (x.val,w)) q)
  have hcov := internal_covariance_quadratic_nonneg ρ Xi hXi z
  have hKx : ContDiffAt ℝ 2 K x.val :=
    (hK.contDiffAt ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds x.property)).of_le (by norm_num)
  have hentry (i j) : hessianMatrix K x.val i j = hessianMatrix F x.val i j + P i j -
      B (e i) q - B (e j) q + c - p.val.1 * ProbabilityTheory.covariance (Xi i) (Xi j) ρ := by
    rw [hessianMatrix_entry hKx,
      hKx.isSymmSndFDerivAt (by norm_num) (EuclideanSpace.single j 1) (EuclideanSpace.single i 1),
      hessianMatrix_entry (penalty_contDiffAt n θ ha b x.val x.property.1)]
    have hf := he i j
    change fderiv ℝ (fderiv ℝ K) x.val _ _ = _ at hf
    rw [hmean, hmean, hmean, hmean] at hf
    change fderiv ℝ (fderiv ℝ K) x.val (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      fderiv ℝ (fderiv ℝ F) x.val (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
        B (e i) (e j) - B (e i) q - B (e j) q + B q q -
        p.val.1 * ProbabilityTheory.covariance (Xi i) (Xi j) ρ at hf
    rw [hee, hqq] at hf
    change fderiv ℝ (fderiv ℝ K) x.val _ _ = _ at hf
    rw [(penalty_contDiffAt n θ ha b x.val x.property.1).isSymmSndFDerivAt
      (by norm_num) (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)]
    simpa only [e, q, Xi, F, K] using hf
  have hZZ : B Z Z = ∑ i, ∑ j, z i * P i j * z j := by
    simp only [Z, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, hee, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [show P j i = P i j from IntervalBoundary.intervalMatrix_symm N n hn A j i]
    ring
  have hZq : B Z q = ∑ i, z i * B (e i) q := by
    simp only [Z, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  have hposeq : B (Z + (∑ i, z i) • q) (Z + (∑ i, z i) • q) =
      B Z Z + 2 * (∑ i, z i) * B Z q + (∑ i, z i) ^ 2 * c := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, hqq, hBsym q Z]
    ring
  have hpos' := hBnn (Z + (∑ i, z i) • q)
  rw [hposeq] at hpos'
  have hsum : (∑ i, ∑ j, z i * hessianMatrix K x.val i j * z j) =
      (∑ i, ∑ j, z i * hessianMatrix F x.val i j * z j) + B Z Z -
        2 * (∑ i, z i) * B Z q + c * (∑ i, z i) ^ 2 -
        p.val.1 * (∑ i, ∑ j, z i * ProbabilityTheory.covariance (Xi i) (Xi j) ρ * z j) := by
    rw [hZZ, hZq]
    simp only [hentry, mul_add, mul_sub, add_mul, sub_mul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul, sq]
    rw [Finset.sum_comm (f := fun i j => z i * B (e j) q * z j)]
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum, ← hZZ]
  nlinarith [mul_nonneg p.property.1.le hcov]

/-- Complete retained interval matrices have summable row and column bounds
on the coefficient event of Subsection 4.4. -/
theorem complete_schur_bounds (p : Parameters) (hs : 1 < p.val.2)
    (n : ℕ+) (m : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (hx : x ∈ ExceptionalEvent.coefficientEvent p n m (by simp only [Nat.succPNat_coe]; omega) D) :
    let N := ((n : ℕ) + m).succPNat
    let hn : (n : ℕ) ≤ (N : ℕ) := by change (n : ℕ) ≤ (n : ℕ) + m + 1; omega
    let P := IntervalBoundary.intervalMatrix N n hn
      (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
    let C := D * (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-p.val.2))
    (∀ i, ∑ j, P i j ≤ C) ∧ (∀ j, ∑ i, P i j ≤ C) := by
  intro N hn P C
  let g : ComponentGeometry (Fin (n : ℕ)) := Sum.inr ⟨N, Fin.castLEEmb hn⟩
  have hr (i) : ∑ j, P i j ≤ C := by
    calc
      _ ≤ ∑ j, D * (1 + componentDistance g i j) ^ (-p.val.2) :=
        Finset.sum_le_sum fun j _ => hx.1 i j
      _ = D * ∑ j, (1 + componentDistance g i j) ^ (-p.val.2) := (Finset.mul_sum ..).symm
      _ ≤ C := mul_le_mul_of_nonneg_left (ComponentGeometryBounds.sum_power_le g i hs) hD
  refine ⟨hr, fun j => ?_⟩
  calc
    _ = ∑ i, P j i := by
      apply Finset.sum_congr rfl
      intro i _
      exact IntervalBoundary.intervalMatrix_symm N n hn _ i j
    _ ≤ C := hr j

/-- The exterior constant mode of the actual conditional ambient Hessian
is nonnegative and costs at most `D/N` on the good event (Subsection 4.5). -/
theorem exterior_mode_bound (p : Parameters) (n : ℕ+) (m : ℕ) (D : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (hx : x ∈ ExceptionalEvent.coefficientEvent p n m (by simp only [Nat.succPNat_coe]; omega) D) :
    let H := IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat ((n : ℕ) + m + 1) le_rfl
      (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
    let S := Finset.univ.filter (fun a : Fin ((n : ℕ) + m + 1) => (n : ℕ) ≤ a.val)
    let c := (m + 1 : ℝ)⁻¹ ^ 2 * ∑ a ∈ S, ∑ b ∈ S, H a b
    0 ≤ c ∧ c * (n : ℝ) ≤ D := by
  classical
  intro H S c
  have hm (a b) : 0 ≤ H a b := IntervalBoundary.intervalMatrix_nonneg
    ((n : ℕ) + m).succPNat ((n : ℕ) + m + 1) le_rfl
    (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
    (conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x) a b
  have hc : 0 ≤ c := mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun a _ =>
    Finset.sum_nonneg fun b _ => hm a b)
  have hbc := hx.2.2.2.2.1 ⟨0,n.pos⟩
  have hb : 0 ≤ (m + 1 : ℝ)⁻¹ * ∑ a ∈ S, H (Fin.castLE (by omega) ⟨0,n.pos⟩) a :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => hm _ a)
  have hcN : c ≤ D / ((n : ℝ) + m + 1) := by
    change _ + c ≤ _ at hbc
    simp only [Nat.succPNat_coe, Nat.cast_add, Nat.cast_succ] at hbc
    linarith
  have hN : (0 : ℝ) < (n : ℝ) + m + 1 := by positivity
  have hc' := (le_div_iff₀ hN).mp hcN
  refine ⟨hc, ?_⟩
  nlinarith [mul_nonneg hc (show (0 : ℝ) ≤ m + 1 by positivity)]

set_option backward.isDefEq.respectTransparency false in
/-- Upper quadratic-form clause for the entire physical auxiliary field
in Subsection 4.5. The bound contains only the permitted polynomial
loss and a summable series, with no bare component-cardinality factor. -/
theorem frozenPhysicalMatrix_upper (p : Parameters) (hs : 1 < p.val.2) (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ+) (m : ℕ) (h : ℝ), 0 < h → ∀ (b : Bool) (D : ℝ),
      0 ≤ D → ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (z : Fin (n : ℕ) → ℝ),
      (∑ i, ∑ j, z i * frozenPhysicalMatrix p n m θ h b D x i j * z j) ≤
        (1 + C * (n : ℝ) ^ (4 * h) +
          2 * D * ((2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-p.val.2)) + 1)) * (∑ i, z i ^ 2) := by
  classical
  obtain ⟨C,hC,hpen⟩ := penalty_hessian_good_bound θ
  refine ⟨C,hC,?_⟩
  intro n m h hh b D hD x z
  let F := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
    ∑ i, (θ.val (((n : ℝ) ^ h)⁻¹ * y i) +
      if b then θ.val (((n : ℝ) ^ h)⁻¹ * (y i)⁻¹) else 0)
  let K := fun y => p.val.1⁻¹ * (p.val.1 * F y -
    Real.log (∫ w : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,w)).toReal))
  let N := ((n : ℕ) + m).succPNat
  have hn : (n : ℕ) ≤ (N : ℕ) := by change (n : ℕ) ≤ (n : ℕ) + m + 1; omega
  let A := conditionalIntervalWeight p n m n.pos (Equiv.refl _) x
  let P := IntervalBoundary.intervalMatrix N n hn A
  let S := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-p.val.2)
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  by_cases hx : x ∈ ExceptionalEvent.properGoodEvent p n m hn h D
  · have hp : (∑ i, ∑ j, z i * hessianMatrix F x.val i j * z j) ≤
        C * (n : ℝ) ^ (4 * h) * (∑ i, z i ^ 2) := by
      have he (i : Fin (n : ℕ)) : (∑ j, z i * hessianMatrix F x.val i j * z j) =
          z i * hessianMatrix F x.val i i * z i := by
        apply Finset.sum_eq_single i
        · intro j _ hij
          rw [penalty_hessian_off_diagonal n θ
            (inv_pos.mpr (Real.rpow_pos_of_pos (show (0 : ℝ) < n by exact_mod_cast n.pos) h))
            b x.val x.property.1 i j (Ne.symm hij)]
          ring
        · simp
      simp_rw [he]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      have hb := (le_abs_self (hessianMatrix F x.val i i)).trans (hpen p n m h hh b D x hx i)
      nlinarith [mul_le_mul_of_nonneg_right hb (sq_nonneg (z i))]
    obtain ⟨hr,hc⟩ := complete_schur_bounds p hs n m D hD x hx.2
    have hPnn (i j) : 0 ≤ P i j := IntervalBoundary.intervalMatrix_nonneg N n hn A
      (conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x) i j
    have hP : (∑ i, ∑ j, z i * P i j * z j) ≤ D * S * (∑ i, z i ^ 2) := by
      calc
        _ ≤ ∑ i, ∑ j, |z i| * P i j * |z j| := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          apply (le_abs_self _).trans_eq
          rw [abs_mul, abs_mul, abs_of_nonneg (hPnn i j)]
        _ ≤ _ := by
          simpa only [add_self_div_two] using
            InitialDecay.Internal.schur_quadratic_le P hPnn (D * S) (D * S) hr hc z
    have hmode := exterior_mode_bound p n m D x hx.2
    have hsum : (∑ i, z i) ^ 2 ≤ (n : ℝ) * ∑ i, z i ^ 2 := by
      have he := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin (n : ℕ) => (1 : ℝ)) z
      simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one] using he
    have hmode' := mul_le_mul_of_nonneg_left hsum hmode.1
    have hmode'' := mul_le_mul_of_nonneg_right hmode.2 (Finset.sum_nonneg (s := Finset.univ) fun i _ => sq_nonneg (z i))
    have hupper := physical_hessian_quadratic_upper p n m θ h hh b x z
    change (∑ i, ∑ j, z i * (if x ∈ ExceptionalEvent.properGoodEvent p n m hn h D
      then hessianMatrix K x.val else 1) i j * z j) ≤ _
    rw [ite_eq_left hx]
    change (∑ i, ∑ j, z i * hessianMatrix K x.val i j * z j) ≤
      (1 + C * (n : ℝ) ^ (4 * h) + 2 * D * (S + 1)) * (∑ i, z i ^ 2)
    dsimp only at hupper
    change (∑ i, ∑ j, z i * hessianMatrix K x.val i j * z j) ≤
      (∑ i, ∑ j, z i * hessianMatrix F x.val i j * z j) +
        2 * (∑ i, ∑ j, z i * P i j * z j) + _ at hupper
    simp only [Nat.succPNat_coe, Nat.succ_eq_add_one] at hupper
    have hm3 := hmode'.trans (by simpa only [mul_assoc] using hmode'')
    have htwo := mul_le_mul_of_nonneg_left hm3 (show (0 : ℝ) ≤ 2 by norm_num)
    simp only [← mul_assoc] at htwo
    apply hupper.trans
    calc
      _ ≤ C * (n : ℝ) ^ (4 * h) * (∑ i, z i ^ 2) +
          2 * (D * S * (∑ i, z i ^ 2)) + 2 * (D * (∑ i, z i ^ 2)) :=
        add_le_add (add_le_add hp (mul_le_mul_of_nonneg_left hP (by norm_num))) (by simpa only [mul_assoc] using htwo)
      _ ≤ _ := by
        nlinarith [Finset.sum_nonneg (s := Finset.univ) fun i => fun _ => sq_nonneg (z i)]
  · rw [(frozenMatrices_off_event p n m θ h b D x hx).1]
    simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← sq]
    have hnn := Finset.sum_nonneg (s := Finset.univ) (fun i _ => sq_nonneg (z i))
    nlinarith [mul_nonneg (show 0 ≤ C * (n : ℝ) ^ (4 * h) by positivity) hnn,
      mul_nonneg (show 0 ≤ 2 * D * (S + 1) by positivity) hnn]

/-- See Subsection 4.5 of the paper: all uniform matrix bounds, for every admissible
choice of the truncation parameters in Subsection 4.4. The exponent precedes
both `h` and the good-event prefactor. The matrix assumption uses the
predicate and the ordinary interval embedding. -/
theorem uniform_matrix_bounds (p : Parameters) (hs : 1 < p.val.2)
    (κ : ℝ) (_hκ : 0 ≤ κ) :
    ∃ q : ℝ, 0 ≤ q ∧ ∀ (θ : PhysicalCutoff) (h : ℝ), 0 < h →
      ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, 1 ≤ C ∧ ∀ (n : ℕ+) (m : ℕ),
        4 ≤ (n : ℕ) + m + 1 → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 → ∀ b : Bool,
        let D := A * (n : ℝ) ^ (κ * h)
        let M := frozenInternalMatrix p n m θ h b D
        let H := frozenPhysicalMatrix p n m θ h b D
        let hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ) := by
          simp only [Nat.succPNat_coe]; omega
        let P := fun x => IntervalBoundary.boundaryMatrix ((n : ℕ) + m).succPNat n hn
          (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
        let g : ComponentGeometry (Fin (n : ℕ)) := Sum.inl
          ⟨fun i => (i.val : ℤ), fun i j hij => Fin.ext (Int.ofNat_inj.mp hij)⟩
        (∀ ρ : Measure (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)),
          SummableCoerciveMatrix (ρ := ρ) ⟨p.val.2,hs⟩ n h C q g M) ∧
        (∀ x (z : Fin (n : ℕ) → ℝ),
          (C * (n : ℝ) ^ (q * h))⁻¹ * (∑ i, z i ^ 2) ≤
            (∑ i, ∑ j, z i * H x i j * z j) ∧
          (∑ i, ∑ j, z i * H x i j * z j) ≤
            C * (n : ℝ) ^ (q * h) * (∑ i, z i ^ 2)) ∧
        (∀ x, x ∈ ExceptionalEvent.properGoodEvent p n m hn h D →
          (∀ i, ∑ j, |P x i j| ≤ C * (n : ℝ) ^ (q * h)) ∧
          (∀ j, ∑ i, |P x i j| ≤ C * (n : ℝ) ^ (q * h)) ∧
          ∀ i j, (n : ℝ) / 8 ≤ (ConditionalScores.boundaryDistance j : ℝ) →
            P x i j ≤ C * (n : ℝ) ^ (q * h) * (n : ℝ) ^ (-p.val.2)) := by
  let q := max (p.val.2 + 2) (max 4 κ)
  have hq4 : 4 ≤ q := (le_max_left 4 κ).trans (le_max_right _ _)
  have hqκ : κ ≤ q := (le_max_right 4 κ).trans (le_max_right _ _)
  have hqs : p.val.2 + 2 ≤ q := le_max_left _ _
  refine ⟨q, by linarith, ?_⟩
  intro θ h hh A hA
  obtain ⟨Ci,hCi,hentry⟩ := frozenInternalMatrix_entry_bound θ
  obtain ⟨Cp,hCp,hupper⟩ := frozenPhysicalMatrix_upper p hs θ
  let S := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-p.val.2)
  let K := 2 * (8 : ℝ) ^ (p.val.2 + 1) + 1
  let C := 1 + Ci + Cp + A + 2 * A * (S + 1) + K * A + S * A
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hA0 : 0 ≤ A := by linarith
  have hC1 : 1 ≤ C := by
    dsimp only [C]
    nlinarith [mul_nonneg hK hA0, mul_nonneg hS hA0,
      mul_nonneg hA0 (show 0 ≤ S + 1 by linarith)]
  have hCe : 1 + A + Ci ≤ C := by
    dsimp only [C]
    nlinarith [mul_nonneg hK hA0, mul_nonneg hS hA0,
      mul_nonneg hA0 (show 0 ≤ S + 1 by linarith)]
  have hCu : 1 + Cp + 2 * A * (S + 1) ≤ C := by
    dsimp only [C]
    nlinarith [mul_nonneg hK hA0, mul_nonneg hS hA0]
  have hCb : A * S ≤ C := by
    dsimp only [C]
    nlinarith [mul_nonneg hK hA0, mul_nonneg hA0 (show 0 ≤ S + 1 by linarith)]
  have hCk : K * A ≤ C := by
    dsimp only [C]
    nlinarith [mul_nonneg hS hA0, mul_nonneg hA0 (show 0 ≤ S + 1 by linarith)]
  refine ⟨C,hC1,?_⟩
  intro n m hN hhalf b D M H hn P g
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hqpow : 1 ≤ (n : ℝ) ^ (q * h) := Real.one_le_rpow hn1 (by nlinarith)
  have hpowκ : (n : ℝ) ^ (κ * h) ≤ (n : ℝ) ^ (q * h) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (mul_le_mul_of_nonneg_right hqκ hh.le)
  have hpow4 : (n : ℝ) ^ (4 * h) ≤ (n : ℝ) ^ (q * h) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (mul_le_mul_of_nonneg_right hq4 hh.le)
  have hD : 0 ≤ D := mul_nonneg hA0 (Real.rpow_nonneg hn0.le _)
  have hC0 : 0 < C := by linarith
  have hlower : (C * (n : ℝ) ^ (q * h))⁻¹ ≤
      (n : ℝ) ^ (-(p.val.2 + 2) * h) := by
    rw [show -(p.val.2 + 2) * h = -((p.val.2 + 2) * h) by ring, Real.rpow_neg hn0.le]
    apply (inv_le_inv₀ (by positivity) (Real.rpow_pos_of_pos hn0 _)).mpr
    exact (Real.rpow_le_rpow_of_exponent_le hn1
      (mul_le_mul_of_nonneg_right hqs hh.le)).trans
      (le_mul_of_one_le_left (Real.rpow_nonneg hn0.le _) hC1)
  have hcoeff : 1 + D + Ci * (n : ℝ) ^ (4 * h) ≤ C * (n : ℝ) ^ (q * h) := by
    calc
      _ ≤ (1 + A + Ci) * (n : ℝ) ^ (q * h) := by
        dsimp only [D]
        nlinarith [mul_le_mul_of_nonneg_left hpowκ hA0,
          mul_le_mul_of_nonneg_left hpow4 hCi.le]
      _ ≤ _ := mul_le_mul_of_nonneg_right hCe (Real.rpow_nonneg hn0.le _)
  have hphysical : 1 + Cp * (n : ℝ) ^ (4 * h) + 2 * D * (S + 1) ≤
      C * (n : ℝ) ^ (q * h) := by
    calc
      _ ≤ (1 + Cp + 2 * A * (S + 1)) * (n : ℝ) ^ (q * h) := by
        dsimp only [D]
        nlinarith [mul_le_mul_of_nonneg_left hpow4 hCp.le,
          mul_le_mul_of_nonneg_left hpowκ (show 0 ≤ 2 * A * (S + 1) by positivity)]
      _ ≤ _ := mul_le_mul_of_nonneg_right hCu (Real.rpow_nonneg hn0.le _)
  have hbound : D * S ≤ C * (n : ℝ) ^ (q * h) := by
    calc
      _ = (A * S) * (n : ℝ) ^ (κ * h) := by dsimp only [D]; ring
      _ ≤ (A * S) * (n : ℝ) ^ (q * h) := mul_le_mul_of_nonneg_left hpowκ (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hCb (Real.rpow_nonneg hn0.le _)
  obtain ⟨hmH,hmM,hsH,hsM⟩ := frozenMatrices_measurable_symmetric p hs n m θ h hh b D
  refine ⟨fun ρ => ⟨hmM, ae_of_all ρ fun x => ⟨hsM x, ?_, ?_⟩⟩, ?_, ?_⟩
  · intro z
    exact (mul_le_mul_of_nonneg_right hlower (Finset.sum_nonneg fun i _ => sq_nonneg (z i))).trans
      (frozenInternalMatrix_lower p hs n m (by omega) θ h hh b D x z)
  · intro i j
    apply (hentry p n m hhalf h hh b D hD x i j).trans
    apply mul_le_mul_of_nonneg_right hcoeff
    exact Real.rpow_nonneg (by positivity) _
  · intro x z
    constructor
    · exact (mul_le_mul_of_nonneg_right hlower (Finset.sum_nonneg fun i _ => sq_nonneg (z i))).trans
        (frozenPhysicalMatrix_lower p hs n m θ h hh b D x z)
    · exact (hupper n m h hh b D hD x z).trans
        (mul_le_mul_of_nonneg_right hphysical (Finset.sum_nonneg fun i _ => sq_nonneg (z i)))
  · intro x hx
    obtain ⟨hr,hc⟩ := boundary_schur_bounds p hs n m D hD x hx.2
    refine ⟨fun i => (hr i).trans hbound, fun j => (hc j).trans hbound, ?_⟩
    intro i j hj
    apply (boundary_bulk_entries p hs n m hhalf D hD x hx.2 i j hj).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hn0.le _)
    calc
      _ = (K * A) * (n : ℝ) ^ (κ * h) := by dsimp only [K, D]; ring
      _ ≤ (K * A) * (n : ℝ) ^ (q * h) := mul_le_mul_of_nonneg_left hpowκ (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hCk (Real.rpow_nonneg hn0.le _)

set_option backward.isDefEq.respectTransparency false in
/-- The first analytic step of Subsection 4.5: existence, uniqueness
and optimal decay for the actual auxiliary internal matrix. A measurable
restriction map includes every fixed-length fibre. -/
theorem internal_auxiliary_point_source_decay (p : Parameters) (hs : 1 < p.val.2)
    (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ (θ : PhysicalCutoff) (h : ℝ), 0 < h →
      ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, 1 ≤ C ∧ ∀ (n : ℕ+) (m : ℕ),
        4 ≤ (n : ℕ) + m + 1 → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 → ∀ (b : Bool)
        (α : Type*) [MeasurableSpace α]
        (τ : α → AffineSimplex.chartDomain n ((n + m : ℕ) + 1)), Measurable τ →
        ∀ (ν : Measure α) [IsProbabilityMeasure ν] (Q : ScalarFormData ν),
        IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
        ∀ (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν),
        let M := fun x => frozenInternalMatrix p n m θ h b (A * (n : ℝ) ^ (κ * h)) (τ x)
        (∃! u : Fin (n : ℕ) → Q.1, WeightedWeakSolution Q (fun x => p.val.1 • M x) ⊤
          (fun i => if i = i₀ then χ else 0) u) ∧
        (∀ u : Fin (n : ℕ) → Q.1, WeightedWeakSolution Q (fun x => p.val.1 • M x) ⊤
          (fun i => if i = i₀ then χ else 0) u → ∀ j : Fin (n : ℕ),
            ‖(u j).val‖ ≤ C * (n : ℝ) ^ (r * h) *
              (1 + |(j.val : ℝ) - (i₀.val : ℝ)|) ^ (-p.val.2) * ‖χ‖) := by
  classical
  obtain ⟨q,hq,hmat⟩ := uniform_matrix_bounds p hs κ hκ
  obtain ⟨r,Cd,hr,hCd,hdecay⟩ := OptimalDecay.optimal_decay_uniform p.val.2 p.val.1 hs p.property.1
  refine ⟨q * r,mul_nonneg hq hr,?_⟩
  intro θ h hh A hA
  obtain ⟨Cm,hCm,hmat⟩ := hmat θ h hh A hA
  have hCm0 : 0 < Cm := by linarith
  refine ⟨Cd * Cm ^ r, one_le_mul_of_one_le_of_one_le hCd (Real.one_le_rpow hCm hr), ?_⟩
  intro n m hN hhalf b α _ τ hτ ν _ Q hQ hcons i₀ χ M
  let B := Cm * (n : ℝ) ^ (q * h)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le hCm
    (Real.one_le_rpow hn1 (mul_nonneg hq hh.le))
  let g : ComponentGeometry (Fin (n : ℕ)) := Sum.inl
    ⟨fun i => (i.val : ℤ), fun i j hij => Fin.ext (Int.ofNat_inj.mp hij)⟩
  have hM := (hmat n m hN hhalf b).1 (ν.map τ)
  have hm (i j) : Measurable (fun x => M x i j) := (hM.1 i j).comp hτ
  have hb : ∀ᵐ x ∂ν,
      (∀ i j, M x i j = M x j i) ∧
      (∀ z : Fin (n : ℕ) → ℝ, B⁻¹ * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j) ∧
      (∀ i j, |M x i j| ≤ B * (1 + componentDistance g i j) ^ (-p.val.2)) :=
    ae_of_ae_map hτ.aemeasurable hM.2
  have he := hdecay α (Fin (n : ℕ)) ν Q hQ hcons g B hB M hm hb i₀ χ
  have hfactor : Cd * B ^ r = (Cd * Cm ^ r) * (n : ℝ) ^ ((q * r) * h) := by
    dsimp only [B]
    rw [Real.mul_rpow hCm0.le (by positivity), ← Real.rpow_mul hn0.le,
      show (q * h) * r = (q * r) * h by ring]
    ring
  have hd (i j : Fin (n : ℕ)) : componentDistance g i j = |(i.val : ℝ) - (j.val : ℝ)| := by
    change |((i.val : ℤ) : ℝ) - ((j.val : ℤ) : ℝ)| = _
    rw [Int.cast_natCast, Int.cast_natCast]
  simpa only [hfactor, hd] using he

end Riesz2.DecayShort.PhysicalComparison
