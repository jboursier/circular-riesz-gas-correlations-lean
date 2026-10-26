/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Preliminaries.GapChart
public import Riesz2.Preliminaries.FundamentalDerivatives
public import Riesz2.ToMathlib.PeriodicPowerBounds
public import Riesz2.ToMathlib.FiniteLinearPotential
public import Riesz2.Frozen.HessianMatrix
public import Mathlib.Analysis.Calculus.MeanValue
public import Riesz1.ToMathlib.LangevinCommutator

/-!
# Physical energy and interval coefficients

The short-interval ambient energy of Subsection 3.2 restricts to the
particle energy under the gap chart. Derivatives are evaluated strictly
away from collisions, in either exponent regime.
-/

@[expose] public section

noncomputable section
open Set Filter
open scoped BigOperators Topology ContDiff

namespace Riesz2.PhysicalEnergy

/-- Positive-order derivatives of the circle kernel in real
coordinates. The carrier excludes collisions. -/
def kernelDerivative (p : Parameters) (j : ℕ+) (x : OffLattice) : ℝ :=
  if h : p.val.2 < 1 then
    iteratedDeriv j (fun y : ℝ => Riesz1.rieszRepresentative
      ⟨p.val.2, p.property.2.1, h⟩ y) x.val
  else iteratedDeriv j (fun y : ℝ =>
    ∑' k : ℤ, |(k : ℝ) + y| ^ (-p.val.2)) x.val

/-- See Subsection 3.2 in the paper: the derivative image formula in both exponent regimes. -/
theorem kernelDerivative_images (p : Parameters) (j : ℕ+) (x : OffLattice) :
    kernelDerivative p j x =
      ((-1 : ℝ) ^ (j : ℕ) * ∏ a ∈ Finset.range j, (p.val.2 + (a : ℝ))) *
        ∑' k : ℤ, Real.sign (x.val + k) ^ (j : ℕ) /
          |x.val + k| ^ (p.val.2 + (j : ℝ)) := by
  unfold kernelDerivative
  split_ifs with h
  · exact iteratedDeriv_rieszRepresentative ⟨p.val.2, p.property.2.1, h⟩
      j.pos x.property
  · exact iteratedDeriv_short_images_signed
      ⟨p.val.2, lt_of_le_of_ne (le_of_not_gt h) (Ne.symm p.property.2.2)⟩ j x.property

/-- Noncollision lift of a separation strictly inside a period. -/
def scaledSeparation (N : ℕ+) (L : {L : ℝ // 0 < L ∧ L < (N : ℝ)}) : OffLattice :=
  ⟨L.val / N, (interiorCirclePoint
    ⟨L.val / N, div_pos L.property.1 (by exact_mod_cast N.pos),
      (div_lt_one (by exact_mod_cast N.pos : (0 : ℝ) < N)).mpr L.property.2⟩).property⟩

/-- The physical interval coefficient with the normalization of equation (3.9). -/
def intervalCoefficient (p : Parameters) (N : ℕ+)
    (L : {L : ℝ // 0 < L ∧ L < (N : ℝ)}) : ℝ :=
  (N : ℝ) ^ (-p.val.2 - 2) * kernelDerivative p 2 (scaledSeparation N L)

private theorem sign_sq (x : ℝ) (hx : x ≠ 0) : Real.sign x ^ 2 = 1 := by
  rcases Real.sign_apply_eq_of_ne_zero x hx with h | h <;> simp [h]

/-- See Subsection 3.2 in the paper: the normalized second derivative is the physical
image sum. No analytic value at a collision occurs in either side. -/
theorem intervalCoefficient_images (p : Parameters) (N : ℕ+)
    (L : {L : ℝ // 0 < L ∧ L < (N : ℝ)}) :
    intervalCoefficient p N L = p.val.2 * (p.val.2 + 1) *
      ∑' k : ℤ, |L.val + k * (N : ℝ)| ^ (-p.val.2 - 2) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hsign (k : ℤ) : Real.sign (L.val / N + k) ^ 2 = 1 :=
    sign_sq _ (by simpa [add_comm, scaledSeparation] using
      Riesz1.add_int_ne_zero_of_nonInt (scaledSeparation N L).property k)
  unfold intervalCoefficient
  rw [kernelDerivative_images]
  norm_num only [PNat.val_ofNat, Finset.prod_range_succ, Finset.prod_range_zero,
    Nat.cast_zero, Nat.cast_one, one_mul, add_zero, neg_one_sq]
  change (N : ℝ) ^ (-p.val.2 - 2) *
    (p.val.2 * (p.val.2 + 1) * ∑' k : ℤ,
      Real.sign (L.val / N + k) ^ 2 / |L.val / N + k| ^ (p.val.2 + 2)) = _
  simp_rw [hsign, one_div, ← Real.rpow_neg (abs_nonneg _),
    show -(p.val.2 + 2) = -p.val.2 - 2 by ring]
  rw [mul_left_comm, ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro k
  have he : L.val / (N : ℝ) + k = (L.val + k * N) / N := by field_simp
  rw [he, abs_div, abs_of_pos hN, Real.div_rpow (abs_nonneg _) hN.le]
  have hn : (N : ℝ) ^ (-p.val.2 - 2) ≠ 0 := (Real.rpow_pos_of_pos hN _).ne'
  field_simp

/-- See Subsection 3.2 in the paper, restriction clause: reuse of the exact
ordered-pair calculation, including the even antipodal rank and `N=2`. -/
theorem restriction (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (X : Riesz1.Configuration N) :
    physicalAmbientGapEnergy p N
      ⟨WithLp.toLp 2 (gapVector X), GapChart.gapVector_mem_gapAmbientDomain X⟩ =
        energy p X :=
  GapChart.physicalAmbientGapEnergy_gapVector p N hN X

/-- The coefficient is strictly positive on the entire ambient energy domain. -/
theorem intervalCoefficient_pos (p : Parameters) (N : ℕ+)
    (L : {L : ℝ // 0 < L ∧ L < (N : ℝ)}) : 0 < intervalCoefficient p N L := by
  rw [intervalCoefficient_images]
  have hs : 1 < p.val.2 + 2 := by linarith [p.property.2.1]
  have hnear := PeriodicPower.nearest_le hs L.property.1 L.property.2
  rw [show -(p.val.2 + 2) = -p.val.2 - 2 by ring] at hnear
  exact mul_pos (mul_pos p.property.2.1 (by linarith [p.property.2.1]))
    (lt_of_lt_of_le (Real.rpow_pos_of_pos L.property.1 _) hnear)

/-- The nearest-image lower bound used in both curvature and gap-bound estimates. -/
theorem intervalCoefficient_lower (p : Parameters) (N : ℕ+)
    (L : {L : ℝ // 0 < L ∧ L < (N : ℝ)}) :
    p.val.2 * (p.val.2 + 1) * L.val ^ (-p.val.2 - 2) ≤
      intervalCoefficient p N L := by
  rw [intervalCoefficient_images]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg p.property.2.1.le (by linarith [p.property.2.1]))
  simpa only [show -(p.val.2 + 2) = -p.val.2 - 2 by ring] using
    PeriodicPower.nearest_le (by linarith [p.property.2.1] : 1 < p.val.2 + 2)
      L.property.1 L.property.2

/-- Uniform endpoint-distance upper bound for the physical coefficient. -/
theorem intervalCoefficient_upper (p : Parameters) (N : ℕ+)
    (L : {L : ℝ // 0 < L ∧ L < (N : ℝ)}) {δ : ℝ} (hδ : 0 < δ)
    (hL : δ ≤ L.val) (hNL : δ ≤ (N : ℝ) - L.val) :
    intervalCoefficient p N L ≤ p.val.2 * (p.val.2 + 1) *
      PeriodicPower.bound (p.val.2 + 2) (by linarith [p.property.2.1]) *
        δ ^ (-p.val.2 - 2) := by
  rw [intervalCoefficient_images, mul_assoc (p.val.2 * (p.val.2 + 1))]
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg p.property.2.1.le (by linarith [p.property.2.1]))
  simpa only [show -(p.val.2 + 2) = -p.val.2 - 2 by ring] using
    (PeriodicPower.summable_and_le (by linarith [p.property.2.1] : 1 < p.val.2 + 2)
      hδ hL hNL).2

/-- The constant for the coefficient consequences of rigidity and gap bounds.
Its carrier is the positive exponent range, on which both displayed series converge. -/
def coefficientConstant (s : ℝ) (hs : 0 < s) : ℝ :=
  s * (s + 1) * (2 * (s + 2) * PeriodicPower.bound (s + 3) (by linarith)) *
    2 ^ (s + 3) + s * (s + 1) * PeriodicPower.bound (s + 2) (by linarith) + 1

theorem coefficientConstant_pos (s : ℝ) (hs : 0 < s) : 0 < coefficientConstant s hs := by
  have hB2 := PeriodicPower.bound_pos (s + 2) (by linarith)
  have hB3 := PeriodicPower.bound_pos (s + 3) (by linarith)
  unfold coefficientConstant
  positivity

/-- A coefficient bound for the Hessian of equation (3.9), valid for every
positive real interval length `r`. -/
theorem coefficient_variation (p : Parameters) (N : ℕ+) {r A : ℝ}
    (hr : 0 < r) (hrN : r ≤ (N : ℝ) / 2)
    (L : {L : ℝ // 0 < L ∧ L < (N : ℝ)})
    (hdev : |L.val - r| ≤ A * r ^ (p.val.2 / 2))
    (hsmall : A * r ^ (p.val.2 / 2) ≤ r / 2) :
    |intervalCoefficient p N L - intervalCoefficient p N
      ⟨r, hr, by linarith⟩| ≤
        coefficientConstant p.val.2 p.property.2.1 * A * r ^ (-3 - p.val.2 / 2) := by
  have hs := p.property.2.1
  have hq : 1 < p.val.2 + 2 := by linarith
  have hB2 := PeriodicPower.bound_pos (p.val.2 + 2) hq
  have hB3 := PeriodicPower.bound_pos (p.val.2 + 3) (by linarith)
  have hA : 0 ≤ A := by
    have := abs_nonneg (L.val - r)
    have hp := Real.rpow_pos_of_pos hr (p.val.2 / 2)
    nlinarith
  have hL := abs_le.mp (hdev.trans hsmall)
  have hv := PeriodicPower.variation (N := (N : ℝ)) (p := p.val.2 + 2)
    (a := r / 2) (b := 3 * r / 2) (δ := r / 2) (x := r) (y := L.val)
    hq (by positivity) le_rfl (by linarith) ⟨by linarith, by linarith⟩
    ⟨by linarith [hL.1], by linarith [hL.2]⟩
  rw [intervalCoefficient_images, intervalCoefficient_images, ← mul_sub, abs_mul,
    abs_of_pos (mul_pos hs (by linarith : 0 < p.val.2 + 1))]
  simp only [show -(p.val.2 + 2) = -p.val.2 - 2 by ring,
    show -p.val.2 - 2 - 1 = -p.val.2 - 3 by ring,
    show p.val.2 + 2 + 1 = p.val.2 + 3 by ring] at hv
  have hpos : 0 ≤ 2 * (p.val.2 + 2) *
      PeriodicPower.bound (p.val.2 + 3) (by linarith) * (r / 2) ^ (-p.val.2 - 3) :=
    by positivity
  have hv' := mul_le_mul_of_nonneg_left
    (hv.trans (mul_le_mul_of_nonneg_left hdev hpos))
    (show 0 ≤ p.val.2 * (p.val.2 + 1) by positivity)
  have he : (r / 2) ^ (-p.val.2 - 3) * r ^ (p.val.2 / 2) =
      2 ^ (p.val.2 + 3) * r ^ (-3 - p.val.2 / 2) := by
    rw [Real.div_rpow hr.le (by norm_num : (0 : ℝ) ≤ 2),
      show -p.val.2 - 3 = -(p.val.2 + 3) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv, inv_inv]
    rw [mul_right_comm, ← Real.rpow_add hr]
    rw [show -(p.val.2 + 3) + p.val.2 / 2 = -3 - p.val.2 / 2 by ring]
    ring
  have he' : p.val.2 * (p.val.2 + 1) *
      (2 * (p.val.2 + 2) * PeriodicPower.bound (p.val.2 + 3) (by linarith) *
        (r / 2) ^ (-p.val.2 - 3) * (A * r ^ (p.val.2 / 2))) =
      (p.val.2 * (p.val.2 + 1) * (2 * (p.val.2 + 2) *
        PeriodicPower.bound (p.val.2 + 3) (by linarith)) * 2 ^ (p.val.2 + 3)) *
          A * r ^ (-3 - p.val.2 / 2) := by
    calc
      _ = (p.val.2 * (p.val.2 + 1) * (2 * (p.val.2 + 2) *
        PeriodicPower.bound (p.val.2 + 3) (by linarith))) * A *
          ((r / 2) ^ (-p.val.2 - 3) * r ^ (p.val.2 / 2)) := by ring
      _ = _ := by rw [he]; ring
  rw [he'] at hv'
  exact hv'.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by
      unfold coefficientConstant
      have : 0 ≤ p.val.2 * (p.val.2 + 1) *
          PeriodicPower.bound (p.val.2 + 2) hq := by positivity
      linarith) hA) (Real.rpow_nonneg hr.le _))

/-- An explicit threshold for the small relative-deviation condition
in the interval coefficient bound. The rigidity deviation is a hypothesis. -/
theorem rigidity_threshold {s A r : ℝ} (hs : s < 1) (hA : 1 ≤ A) (hr : 0 < r)
    (hthreshold : (2 * A) ^ (1 / (1 - s / 2)) ≤ r) :
    A * r ^ (s / 2) ≤ r / 2 := by
  have hpow : 2 * A ≤ r ^ (1 - s / 2) := by
    apply (Real.rpow_inv_le_iff_of_pos (by linarith : 0 ≤ 2 * A) hr.le
      (by linarith : 0 < 1 - s / 2)).mp
    simpa only [one_div] using hthreshold
  have hm := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hr.le (s / 2))
  rw [← Real.rpow_add hr, show 1 - s / 2 + s / 2 = 1 by ring, Real.rpow_one] at hm
  linarith

private theorem interval_index_inj (N : ℕ+) (i : Fin (N : ℕ)) :
    Set.InjOn (fun a : ℕ => (⟨(i.val + a) % (N : ℕ), Nat.mod_lt _ N.pos⟩ : Fin (N : ℕ)))
      (Finset.range (N : ℕ)) := by
  intro a ha b hb he
  have hm : Nat.ModEq (N : ℕ) (i.val + a) (i.val + b) := congrArg Fin.val he
  have hc := Nat.ModEq.add_left_cancel' i.val hm
  change a % (N : ℕ) = b % (N : ℕ) at hc
  simpa only [Nat.mod_eq_of_lt (Finset.mem_range.mp ha),
    Nat.mod_eq_of_lt (Finset.mem_range.mp hb)] using hc

/-- Componentwise gap bounds give the corresponding interval bounds. -/
theorem gapSum_bounds (N : ℕ+) (i : Fin (N : ℕ)) (r : ℕ)
    (y : Fin (N : ℕ) → ℝ) {a b : ℝ} (hy : ∀ j, a ≤ y j ∧ y j ≤ b) :
    a * r ≤ cyclicGapSum N i r y ∧ cyclicGapSum N i r y ≤ b * r := by
  constructor
  · simpa [cyclicGapSum, mul_comm] using
      Finset.sum_le_sum (s := Finset.range r) (fun k _ => (hy
        ⟨(i.val + k) % (N : ℕ), Nat.mod_lt _ N.pos⟩).1)
  · simpa [cyclicGapSum, mul_comm] using
      Finset.sum_le_sum (s := Finset.range r) (fun k _ => (hy
        ⟨(i.val + k) % (N : ℕ), Nat.mod_lt _ N.pos⟩).2)

/-- A lower bound on all gaps controls the omitted part of a proper interval. -/
theorem gapSum_complement_lower (N : ℕ+) (i : Fin (N : ℕ)) {r : ℕ}
    (hr : r ≤ (N : ℕ)) (y : Fin (N : ℕ) → ℝ) {a : ℝ}
    (hy : ∀ j, a ≤ y j) (hmass : ∑ j, y j = (N : ℝ)) :
    a * ((N : ℝ) - r) ≤ (N : ℝ) - cyclicGapSum N i r y := by
  classical
  have hh : (∑ k ∈ Finset.range r,
      (y ⟨(i.val + k) % (N : ℕ), Nat.mod_lt _ N.pos⟩ - a)) ≤
        ∑ j, (y j - a) := by
    apply Finset.sum_le_sum_of_injOn (g := fun j => y j - a)
      (fun k : ℕ => (⟨(i.val + k) % (N : ℕ), Nat.mod_lt _ N.pos⟩ : Fin (N : ℕ)))
      ((interval_index_inj N i).mono (Finset.range_mono hr))
      (Finset.subset_univ _) (fun _ _ => le_rfl)
    intro j _ _
    exact sub_nonneg.mpr (hy j)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hmass] at hh
  change cyclicGapSum N i r y - (r : ℝ) * a ≤ (N : ℝ) - (N : ℝ) * a at hh
  nlinarith

/-- A nonempty proper cyclic sum of positive mass-`N` gaps is inside `(0,N)`. -/
theorem gapSum_mem (N : ℕ+) (i : Fin (N : ℕ)) {r : ℕ}
    (hr : 1 ≤ r) (hrN : r < (N : ℕ)) (y : Fin (N : ℕ) → ℝ)
    (hy : y ∈ Riesz1.gapSimplex N) :
    0 < cyclicGapSum N i r y ∧ cyclicGapSum N i r y < (N : ℝ) := by
  classical
  let e : ℕ → Fin (N : ℕ) := fun k =>
    ⟨(i.val + k) % (N : ℕ), Nat.mod_lt _ N.pos⟩
  have hinj : Set.InjOn e (Finset.range (N : ℕ)) := interval_index_inj N i
  have hrsub : Finset.range r ⊆ Finset.range (N : ℕ) := Finset.range_mono hrN.le
  have hnot : e r ∉ (Finset.range r).image e := by
    intro h
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp h
    have heq := hinj (hrsub ha) (Finset.mem_range.mpr hrN) he
    have := Finset.mem_range.mp ha
    omega
  constructor
  · exact Finset.sum_pos (fun k _ => hy.1 (e k)) (Finset.nonempty_range_iff.mpr (by omega))
  · calc
      cyclicGapSum N i r y = ∑ j ∈ (Finset.range r).image e, y j :=
        (Finset.sum_image (hinj.mono hrsub)).symm
      _ < ∑ j, y j := Finset.sum_lt_sum_of_subset (Finset.subset_univ _)
        (Finset.mem_univ (e r)) hnot (hy.1 (e r)) (fun j _ _ => (hy.1 j).le)
      _ = (N : ℝ) := hy.2

/-- See Subsection 3.2 in the paper, the two-sided coefficient consequence of
uniform bounds on individual gaps. This statement uses the existing mass simplex. -/
theorem coefficient_gap_bounds (p : Parameters) (N : ℕ+) (i : Fin (N : ℕ))
    {r : ℕ} (hr : 1 ≤ r) (hrN : r ≤ (N : ℕ) / 2)
    (y : Fin (N : ℕ) → ℝ) (hy : y ∈ Riesz1.gapSimplex N)
    {a b : ℝ} (ha : 0 < a) (hab : ∀ j, a ≤ y j ∧ y j ≤ b) :
    p.val.2 * (p.val.2 + 1) * b ^ (-p.val.2 - 2) * (r : ℝ) ^ (-p.val.2 - 2) ≤
        intervalCoefficient p N ⟨cyclicGapSum N i r y,
          gapSum_mem N i hr (by have := N.pos; omega) y hy⟩ ∧
    intervalCoefficient p N ⟨cyclicGapSum N i r y,
          gapSum_mem N i hr (by have := N.pos; omega) y hy⟩ ≤
        coefficientConstant p.val.2 p.property.2.1 *
          a ^ (-p.val.2 - 2) * (r : ℝ) ^ (-p.val.2 - 2) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hbr := gapSum_bounds N i r y hab
  have hcomp := gapSum_complement_lower N i (by omega : r ≤ (N : ℕ)) y
    (fun j => (hab j).1) hy.2
  have hrNR : 2 * (r : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 2 * r ≤ (N : ℕ) by omega)
  have hb : 0 < b := lt_of_lt_of_le (lt_of_lt_of_le ha (hab i).1) (hab i).2
  have hs := p.property.2.1
  have hB2 := PeriodicPower.bound_pos (p.val.2 + 2) (by linarith)
  have hB3 := PeriodicPower.bound_pos (p.val.2 + 3) (by linarith)
  constructor
  · have hpow := Real.rpow_le_rpow_of_nonpos
      (gapSum_mem N i hr (by have := N.pos; omega) y hy).1 hbr.2
      (show -p.val.2 - 2 ≤ 0 by linarith)
    rw [Real.mul_rpow hb.le hr0.le] at hpow
    exact (by
      nlinarith [mul_le_mul_of_nonneg_left hpow
        (show 0 ≤ p.val.2 * (p.val.2 + 1) by positivity)] :
      p.val.2 * (p.val.2 + 1) * b ^ (-p.val.2 - 2) * (r : ℝ) ^ (-p.val.2 - 2) ≤
        p.val.2 * (p.val.2 + 1) * (cyclicGapSum N i r y) ^ (-p.val.2 - 2)).trans
      (intervalCoefficient_lower p N
        ⟨cyclicGapSum N i r y, gapSum_mem N i hr (by have := N.pos; omega) y hy⟩)
  · have hupper := intervalCoefficient_upper p N
      ⟨cyclicGapSum N i r y, gapSum_mem N i hr (by have := N.pos; omega) y hy⟩
      (mul_pos ha hr0) hbr.1 (by nlinarith)
    rw [Real.mul_rpow ha.le hr0.le] at hupper
    apply hupper.trans
    have hC : p.val.2 * (p.val.2 + 1) *
        PeriodicPower.bound (p.val.2 + 2) (by linarith) ≤
          coefficientConstant p.val.2 hs := by
      unfold coefficientConstant
      have : 0 ≤ p.val.2 * (p.val.2 + 1) * (2 * (p.val.2 + 2) *
          PeriodicPower.bound (p.val.2 + 3) (by linarith)) * 2 ^ (p.val.2 + 3) :=
        by positivity
      linarith
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hC
      (mul_nonneg (Real.rpow_nonneg ha.le (-p.val.2 - 2))
        (Real.rpow_nonneg hr0.le (-p.val.2 - 2)))

/-- The interval sum as a continuous linear functional. -/
def intervalLinear (N : ℕ+) (i : Fin (N : ℕ)) (r : ℕ) :
    EuclideanSpace ℝ (Fin (N : ℕ)) →L[ℝ] ℝ :=
  ∑ a ∈ Finset.range r,
    EuclideanSpace.proj ⟨(i.val + a) % (N : ℕ), Nat.mod_lt _ N.pos⟩

theorem intervalLinear_apply (N : ℕ+) (i : Fin (N : ℕ)) (r : ℕ)
    (y : EuclideanSpace ℝ (Fin (N : ℕ))) :
    intervalLinear N i r y = cyclicGapSum N i r (WithLp.ofLp y) := by
  simp only [intervalLinear, sum_apply, cyclicGapSum]
  rfl

theorem isOpen_gapAmbientDomain (N : ℕ+) : IsOpen (gapAmbientDomain N) := by
  have he : gapAmbientDomain N = ⋂ i : Fin (N : ℕ), ⋂ r : Fin ((N : ℕ) / 2),
      (intervalLinear N i (r.val + 1)) ⁻¹' Ioo (0 : ℝ) (N : ℝ) := by
    ext y
    simp only [mem_iInter, mem_preimage, mem_Ioo]
    constructor
    · intro hy i r
      rw [intervalLinear_apply]
      exact hy i (r.val + 1) (by omega) (by have := r.isLt; omega)
    · intro hy i r hr hu
      have h := hy i ⟨r - 1, by omega⟩
      rw [intervalLinear_apply, show r - 1 + 1 = r by omega] at h
      exact h
  rw [he]
  exact isOpen_iInter_of_finite (fun i => isOpen_iInter_of_finite
    (fun r => isOpen_Ioo.preimage (intervalLinear N i (r.val + 1)).continuous))

/-- Every positive mass-`N` vector is in the ambient domain. -/
theorem simplex_subset_ambient (N : ℕ+) (y : Fin (N : ℕ) → ℝ)
    (hy : y ∈ Riesz1.gapSimplex N) : WithLp.toLp 2 y ∈ gapAmbientDomain N := by
  intro i r hr hu
  exact gapSum_mem N i hr (by have := N.pos; omega) y hy

private theorem kernel_realization (p : Parameters) :
    ∃ K : ℝ → ℝ,
      ContDiffOn ℝ ∞ K {x : ℝ | (x : UnitAddCircle) ≠ 0} ∧
      (∀ x : OffLattice, K x.val =
        kernelAtParameters p ⟨(x.val : UnitAddCircle), x.property⟩) ∧
      (∀ (j : ℕ+) (x : OffLattice),
        iteratedDeriv j K x.val = kernelDerivative p j x) := by
  by_cases h : p.val.2 < 1
  · refine ⟨fun x : ℝ => Riesz1.rieszRepresentative
      ⟨p.val.2, p.property.2.1, h⟩ x, (companionKernelIdentification _).1, ?_, ?_⟩
    · intro x
      simp only [kernelAtParameters, h, ↓reduceDIte, Riesz1.rieszKernel]
    · intro j x
      simp only [kernelDerivative, h, ↓reduceDIte]
  · let s : ShortExponent :=
      ⟨p.val.2, lt_of_le_of_ne (le_of_not_gt h) (Ne.symm p.property.2.2)⟩
    refine ⟨fun x : ℝ => ∑' k : ℤ, |(k : ℝ) + x| ^ (-p.val.2),
      contDiffOn_short_images s, ?_, ?_⟩
    · intro x
      simp only [kernelAtParameters, h, ↓reduceDIte]
      exact (shortKernelLift_eq_tsum_rpow s x).symm.trans (shortKernel_coe s x).symm
    · intro j x
      simp only [kernelDerivative, h, ↓reduceDIte]

/-- See Subsection 3.2 in the paper, derivative clauses: an ambient smooth representative
of the energy, with its first derivative and full bilinear Hessian.
Only its values on `U_N` are identified with physical energies. -/
theorem ambient_derivatives (p : Parameters) (N : ℕ+) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ∀ (y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N})
        (u v : EuclideanSpace ℝ (Fin (N : ℕ))),
        fderiv ℝ W y.val u = (N : ℝ) ^ (-p.val.2 - 1) *
          ∑ i : Fin (N : ℕ), ∑ r : Fin ((N : ℕ) / 2),
            (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
              kernelDerivative p 1 (scaledSeparation N
                ⟨cyclicGapSum N i (r.val + 1) (WithLp.ofLp y.val),
                  y.property i (r.val + 1) (by omega) (by have := r.isLt; omega)⟩) *
                cyclicGapSum N i (r.val + 1) (WithLp.ofLp u) ∧
        fderiv ℝ (fderiv ℝ W) y.val u v =
          ∑ i : Fin (N : ℕ), ∑ r : Fin ((N : ℕ) / 2),
            (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
              intervalCoefficient p N
                ⟨cyclicGapSum N i (r.val + 1) (WithLp.ofLp y.val),
                  y.property i (r.val + 1) (by omega) (by have := r.isLt; omega)⟩ *
                (cyclicGapSum N i (r.val + 1) (WithLp.ofLp u) *
                  cyclicGapSum N i (r.val + 1) (WithLp.ofLp v)) := by
  classical
  obtain ⟨K, hK, hval, hjet⟩ := kernel_realization p
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  let I := Fin (N : ℕ) × Fin ((N : ℕ) / 2)
  let l : I → EuclideanSpace ℝ (Fin (N : ℕ)) →L[ℝ] ℝ :=
    fun q => (N : ℝ)⁻¹ • intervalLinear N q.1 (q.2.val + 1)
  let c : I → ℝ := fun q => (N : ℝ) ^ (-p.val.2) *
    (2 - if 2 * (q.2.val + 1) = (N : ℕ) then 1 else 0)
  let W := fun y => ∑ q : I, c q * K (l q y)
  have hl (q : I) (y : EuclideanSpace ℝ (Fin (N : ℕ))) :
      l q y = cyclicGapSum N q.1 (q.2.val + 1) (WithLp.ofLp y) / N := by
    simp only [l, smul_apply, smul_eq_mul, intervalLinear_apply, div_eq_mul_inv]
    ring
  have harg (y : EuclideanSpace ℝ (Fin (N : ℕ))) (hy : y ∈ gapAmbientDomain N)
      (q : I) : (l q y : UnitAddCircle) ≠ 0 := by
    rw [hl]
    exact (scaledSeparation N
      ⟨cyclicGapSum N q.1 (q.2.val + 1) (WithLp.ofLp y),
        hy q.1 (q.2.val + 1) (by omega) (by have := q.2.isLt; omega)⟩).property
  refine ⟨W, ?_, ?_, ?_⟩
  · apply ContDiffOn.sum
    intro q _
    exact contDiffOn_const.mul (hK.comp (l q).contDiff.contDiffOn (fun y hy => harg y hy q))
  · intro y
    unfold physicalAmbientGapEnergy
    simp only [W, I, c, Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro r _
    have hv := hval (scaledSeparation N
      ⟨cyclicGapSum N i (r.val + 1) (WithLp.ofLp y.val),
        y.property i (r.val + 1) (by omega) (by have := r.isLt; omega)⟩)
    rw [hl]
    rw [show K (cyclicGapSum N i (r.val + 1) (WithLp.ofLp y.val) / N) =
      kernelAtParameters p (interiorCirclePoint
        ⟨cyclicGapSum N i (r.val + 1) (WithLp.ofLp y.val) / N, by
          have hi := y.property i (r.val + 1) (by omega) (by have := r.isLt; omega)
          exact ⟨div_pos hi.1 hN, (div_lt_one hN).mpr hi.2⟩⟩) from hv]
    ring
  · intro y u v
    have hd := finite_linear_potential_derivatives c (fun _ : I => K) l
      (fun _ => {x : ℝ | (x : UnitAddCircle) ≠ 0}) (fun _ => Riesz1.isOpen_nonInt)
      (fun _ => hK.of_le (by simp)) y.val (fun q => harg y.val y.property q) u v
    have hjet' (q : I) (j : ℕ+) :
        iteratedDeriv j K (l q y.val) = kernelDerivative p j
          (scaledSeparation N
            ⟨cyclicGapSum N q.1 (q.2.val + 1) (WithLp.ofLp y.val),
              y.property q.1 (q.2.val + 1) (by omega) (by have := q.2.isLt; omega)⟩) := by
      rw [hl]
      exact hjet j (scaledSeparation N
        ⟨cyclicGapSum N q.1 (q.2.val + 1) (WithLp.ofLp y.val),
          y.property q.1 (q.2.val + 1) (by omega) (by have := q.2.isLt; omega)⟩)
    have hscale1 : (N : ℝ) ^ (-p.val.2 - 1) = (N : ℝ) ^ (-p.val.2) / N := by
      rw [Real.rpow_sub hN, Real.rpow_one]
    have hscale2 : (N : ℝ) ^ (-p.val.2 - 2) = (N : ℝ) ^ (-p.val.2) / (N : ℝ) ^ 2 := by
      rw [Real.rpow_sub hN, Real.rpow_two]
    constructor
    · rw [hd.1, hscale1]
      simp only [I, Fintype.sum_prod_type, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro r _
      have hj := hjet' (i, r) 1
      simp only [PNat.val_ofNat, iteratedDeriv_one] at hj
      rw [hj, hl]
      dsimp [c]
      ring
    · rw [hd.2]
      simp only [I, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro r _
      have hj := hjet' (i, r) 2
      simp only [PNat.val_ofNat, iteratedDeriv_succ, iteratedDeriv_zero] at hj
      rw [hj, hl, hl]
      unfold intervalCoefficient
      rw [hscale2]
      dsimp [c]
      ring

/-- The two nearest images, retained separately for the two-particle tangent estimate. -/
theorem intervalCoefficient_two_images (p : Parameters) (N : ℕ+)
    (L : {L : ℝ // 0 < L ∧ L < (N : ℝ)}) :
    p.val.2 * (p.val.2 + 1) *
      (L.val ^ (-p.val.2 - 2) + ((N : ℝ) - L.val) ^ (-p.val.2 - 2)) ≤
        intervalCoefficient p N L := by
  have hq : 1 < p.val.2 + 2 := by linarith [p.property.2.1]
  have hf := (PeriodicPower.summable_and_le hq
    (lt_min L.property.1 (sub_pos.mpr L.property.2))
    (min_le_left _ _) (min_le_right _ _)).1
  have hsum := hf.sum_le_tsum ({0, -1} : Finset ℤ)
    (fun k _ => Real.rpow_nonneg (abs_nonneg _) _)
  rw [show -(p.val.2 + 2) = -p.val.2 - 2 by ring] at hsum
  norm_num only [Finset.sum_insert, Finset.mem_singleton, neg_eq_zero,
    one_ne_zero, not_false_eq_true, Finset.sum_singleton, Int.cast_zero,
    zero_mul, add_zero, Int.cast_neg, Int.cast_one, neg_mul, one_mul] at hsum
  rw [abs_of_pos L.property.1,
    show L.val + -(N : ℝ) = -((N : ℝ) - L.val) by ring, abs_neg,
    abs_of_pos (sub_pos.mpr L.property.2)] at hsum
  rw [intervalCoefficient_images]
  exact mul_le_mul_of_nonneg_left hsum
    (mul_nonneg p.property.2.1.le (by linarith [p.property.2.1]))

theorem gapSum_one (N : ℕ+) (i : Fin (N : ℕ)) (y : Fin (N : ℕ) → ℝ) :
    cyclicGapSum N i 1 y = y i := by
  simp only [cyclicGapSum, Finset.range_one, Finset.sum_singleton, add_zero,
    Nat.mod_eq_of_lt i.isLt]

private theorem interval_lower_aux (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N})
    (u : EuclideanSpace ℝ (Fin (N : ℕ))) (t : ℝ) (ht : 0 ≤ t)
    (hw : t ≤ 2 - if 2 = (N : ℕ) then (1 : ℝ) else 0) :
    t * (p.val.2 * (p.val.2 + 1)) *
      (∑ i, (y.val i) ^ (-p.val.2 - 2) * (u i) ^ 2) ≤
        ∑ i : Fin (N : ℕ), ∑ r : Fin ((N : ℕ) / 2),
          (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
            intervalCoefficient p N
              ⟨cyclicGapSum N i (r.val + 1) (WithLp.ofLp y.val),
                y.property i (r.val + 1) (by omega) (by have := r.isLt; omega)⟩ *
              (cyclicGapSum N i (r.val + 1) (WithLp.ofLp u)) ^ 2 := by
  have hs := p.property.2.1
  have hcoef := mul_pos hs (by linarith : 0 < p.val.2 + 1)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  let r0 : Fin ((N : ℕ) / 2) := ⟨0, by omega⟩
  have hyi : 0 < y.val i ∧ y.val i < (N : ℝ) := by
    simpa only [gapSum_one] using y.property i 1 (by omega) (by omega)
  have hlow := intervalCoefficient_lower p N ⟨y.val i, hyi⟩
  have hlow' : t * (p.val.2 * (p.val.2 + 1)) *
      ((y.val i) ^ (-p.val.2 - 2) * (u i) ^ 2) ≤
      (2 - if 2 = (N : ℕ) then (1 : ℝ) else 0) *
        intervalCoefficient p N ⟨y.val i, hyi⟩ * (u i) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hlow ht
    have h2 := mul_le_mul_of_nonneg_right hw (intervalCoefficient_pos p N ⟨y.val i, hyi⟩).le
    have hh := mul_le_mul_of_nonneg_right (h1.trans h2) (sq_nonneg (u i))
    nlinarith only [hh]
  apply hlow'.trans
  have hsum := Finset.single_le_sum (f := fun r : Fin ((N : ℕ) / 2) =>
      (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
        intervalCoefficient p N
          ⟨cyclicGapSum N i (r.val + 1) (WithLp.ofLp y.val),
            y.property i (r.val + 1) (by omega) (by have := r.isLt; omega)⟩ *
          (cyclicGapSum N i (r.val + 1) (WithLp.ofLp u)) ^ 2)
    (fun r _ => mul_nonneg (mul_nonneg (by split_ifs <;> norm_num)
      (intervalCoefficient_pos p N _).le) (sq_nonneg _)) (Finset.mem_univ r0)
  simpa only [r0, Nat.zero_add, mul_one, gapSum_one] using hsum

private theorem interval_two_tangent_lower (p : Parameters)
    (y : Fin (2 : ℕ) → ℝ) (hy : y ∈ Riesz1.gapSimplex 2)
    (u : EuclideanSpace ℝ (Fin (2 : ℕ))) (hu : ∑ i, u i = 0) :
    2 * (p.val.2 * (p.val.2 + 1)) *
      (∑ i, y i ^ (-p.val.2 - 2) * (u i) ^ 2) ≤
        ∑ i : Fin (2 : ℕ), ∑ r : Fin (2 / 2),
          (2 - if 2 * (r.val + 1) = 2 then (1 : ℝ) else 0) *
            intervalCoefficient p 2
              ⟨cyclicGapSum 2 i (r.val + 1) y,
                (simplex_subset_ambient 2 y hy) i (r.val + 1)
                  (by omega) (by have := r.isLt; norm_num at *)⟩ *
              (cyclicGapSum 2 i (r.val + 1) (WithLp.ofLp u)) ^ 2 := by
  classical
  have hmass : y 0 + y 1 = 2 := by
    have hh : (∑ i : Fin 2, y i) = 2 := hy.2
    simpa only [Fin.sum_univ_two] using hh
  have hypos : ∀ i : Fin 2, 0 < y i := hy.1
  have hylt : ∀ i : Fin 2, y i < 2 := by
    intro i
    fin_cases i
    · change y 0 < 2
      linarith only [hmass, hypos 1]
    · change y 1 < 2
      linarith only [hmass, hypos 0]
  let L : Fin 2 → {v : ℝ // 0 < v ∧ v < ((2 : ℕ+) : ℝ)} := fun i =>
    ⟨y i, hypos i, by norm_num; exact hylt i⟩
  have hu' : u 0 + u 1 = 0 := by simpa only [Fin.sum_univ_two] using hu
  have hu2 : (u 0) ^ 2 = (u 1) ^ 2 := by
    have hh : u 0 = -u 1 := by linarith only [hu']
    rw [hh, neg_sq]
  have hcore : 2 * (p.val.2 * (p.val.2 + 1)) *
      (∑ i : Fin 2, y i ^ (-p.val.2 - 2) * (u i) ^ 2) ≤
      ∑ i : Fin 2, intervalCoefficient p 2 (L i) * (u i) ^ 2 := by
    have h0 := intervalCoefficient_two_images p 2 (L 0)
    have h1 := intervalCoefficient_two_images p 2 (L 1)
    change p.val.2 * (p.val.2 + 1) *
      (y 0 ^ (-p.val.2 - 2) + (2 - y 0) ^ (-p.val.2 - 2)) ≤
        intervalCoefficient p 2 (L 0) at h0
    change p.val.2 * (p.val.2 + 1) *
      (y 1 ^ (-p.val.2 - 2) + (2 - y 1) ^ (-p.val.2 - 2)) ≤
        intervalCoefficient p 2 (L 1) at h1
    rw [show (2 : ℝ) - y 0 = y 1 by linarith only [hmass]] at h0
    rw [show (2 : ℝ) - y 1 = y 0 by linarith only [hmass]] at h1
    simp only [Fin.sum_univ_two]
    have hh0 := mul_le_mul_of_nonneg_right h0 (sq_nonneg (u 0))
    have hh1 := mul_le_mul_of_nonneg_right h1 (sq_nonneg (u 1))
    rw [hu2] at hh0 ⊢
    nlinarith only [hh0, hh1]
  apply hcore.trans
  apply Finset.sum_le_sum
  intro i _
  let r0 : Fin (2 / 2) := ⟨0, by norm_num⟩
  have hsum := Finset.single_le_sum (f := fun r : Fin (2 / 2) =>
      (2 - if 2 * (r.val + 1) = 2 then (1 : ℝ) else 0) *
        intervalCoefficient p 2
          ⟨cyclicGapSum 2 i (r.val + 1) y,
            (simplex_subset_ambient 2 y hy) i (r.val + 1)
              (by omega) (by have := r.isLt; norm_num at *)⟩ *
          (cyclicGapSum 2 i (r.val + 1) (WithLp.ofLp u)) ^ 2)
    (fun r _ => mul_nonneg (mul_nonneg (by split_ifs <;> norm_num)
      (intervalCoefficient_pos p 2 _).le) (sq_nonneg _)) (Finset.mem_univ r0)
  simp only [r0, Nat.zero_add, mul_one, ↓reduceIte,
    show (2 : ℝ) - 1 = 1 by norm_num, one_mul] at hsum
  have hY : cyclicGapSum 2 i 1 y = y i := gapSum_one 2 i y
  have hU : cyclicGapSum 2 i 1 (WithLp.ofLp u) = u i := gapSum_one 2 i (WithLp.ofLp u)
  have hC : intervalCoefficient p 2
      ⟨cyclicGapSum 2 i 1 y, (simplex_subset_ambient 2 y hy) i 1 (by omega) (by norm_num)⟩ =
        intervalCoefficient p 2 (L i) := by
    apply congrArg (intervalCoefficient p 2)
    exact Subtype.ext hY
  rw [hC, hU] at hsum
  exact hsum

/-- See Subsection 3.2 in the paper, all clauses: exact restriction, derivative and image
identities, positive definite Hessian, the ambient nearest-gap barrier, its
factor two for `N≥3`, and its factor two on the tangent space for `N=2`.
The exponent is exactly `p.val.2 ∈ (0,1) ∪ (1,∞)`. Temperature is unused. -/
theorem restriction_and_derivatives (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    (∀ X : Riesz1.Configuration N, physicalAmbientGapEnergy p N
      ⟨WithLp.toLp 2 (gapVector X), GapChart.gapVector_mem_gapAmbientDomain X⟩ = energy p X) ∧
    (∀ L : {L : ℝ // 0 < L ∧ L < (N : ℝ)},
      intervalCoefficient p N L = p.val.2 * (p.val.2 + 1) *
        ∑' k : ℤ, |L.val + k * (N : ℝ)| ^ (-p.val.2 - 2)) ∧
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      (∀ (y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N})
        (u v : EuclideanSpace ℝ (Fin (N : ℕ))),
        fderiv ℝ W y.val u = (N : ℝ) ^ (-p.val.2 - 1) *
          ∑ i : Fin (N : ℕ), ∑ r : Fin ((N : ℕ) / 2),
            (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
              kernelDerivative p 1 (scaledSeparation N
                ⟨cyclicGapSum N i (r.val + 1) (WithLp.ofLp y.val),
                  y.property i (r.val + 1) (by omega) (by have := r.isLt; omega)⟩) *
                cyclicGapSum N i (r.val + 1) (WithLp.ofLp u) ∧
        fderiv ℝ (fderiv ℝ W) y.val u v =
          ∑ i : Fin (N : ℕ), ∑ r : Fin ((N : ℕ) / 2),
            (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
              intervalCoefficient p N
                ⟨cyclicGapSum N i (r.val + 1) (WithLp.ofLp y.val),
                  y.property i (r.val + 1) (by omega) (by have := r.isLt; omega)⟩ *
                (cyclicGapSum N i (r.val + 1) (WithLp.ofLp u) *
                  cyclicGapSum N i (r.val + 1) (WithLp.ofLp v))) ∧
      (∀ (y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N})
        (u : EuclideanSpace ℝ (Fin (N : ℕ))), u ≠ 0 →
          0 < fderiv ℝ (fderiv ℝ W) y.val u u) ∧
      (∀ (y : Fin (N : ℕ) → ℝ) (hy : y ∈ Riesz1.gapSimplex N)
        (u : EuclideanSpace ℝ (Fin (N : ℕ))),
        p.val.2 * (p.val.2 + 1) * (∑ i, y i ^ (-p.val.2 - 2) * (u i) ^ 2) ≤
          fderiv ℝ (fderiv ℝ W) (WithLp.toLp 2 y) u u) ∧
      (∀ (y : Fin (N : ℕ) → ℝ) (hy : y ∈ Riesz1.gapSimplex N)
        (u : EuclideanSpace ℝ (Fin (N : ℕ))), 3 ≤ (N : ℕ) →
        2 * (p.val.2 * (p.val.2 + 1)) * (∑ i, y i ^ (-p.val.2 - 2) * (u i) ^ 2) ≤
          fderiv ℝ (fderiv ℝ W) (WithLp.toLp 2 y) u u) ∧
      (∀ (y : Fin (N : ℕ) → ℝ) (hy : y ∈ Riesz1.gapSimplex N)
        (u : EuclideanSpace ℝ (Fin (N : ℕ))), (∑ i, u i) = 0 →
        2 * (p.val.2 * (p.val.2 + 1)) * (∑ i, y i ^ (-p.val.2 - 2) * (u i) ^ 2) ≤
          fderiv ℝ (fderiv ℝ W) (WithLp.toLp 2 y) u u) := by
  refine ⟨restriction p N hN, intervalCoefficient_images p N, ?_⟩
  obtain ⟨W, hsm, hval, hd⟩ := ambient_derivatives p N
  have hquad (y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N})
      (u : EuclideanSpace ℝ (Fin (N : ℕ))) := (hd y u u).2
  simp only [← pow_two] at hquad
  have hlow (y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N})
      (u : EuclideanSpace ℝ (Fin (N : ℕ))) :
      p.val.2 * (p.val.2 + 1) * (∑ i, (y.val i) ^ (-p.val.2 - 2) * (u i) ^ 2) ≤
        fderiv ℝ (fderiv ℝ W) y.val u u := by
    rw [hquad]
    simpa only [one_mul] using interval_lower_aux p N hN y u 1 (by norm_num)
      (by split_ifs <;> norm_num)
  have hdouble (y : Fin (N : ℕ) → ℝ) (hy : y ∈ Riesz1.gapSimplex N)
      (u : EuclideanSpace ℝ (Fin (N : ℕ))) (hN3 : 3 ≤ (N : ℕ)) :
      2 * (p.val.2 * (p.val.2 + 1)) * (∑ i, y i ^ (-p.val.2 - 2) * (u i) ^ 2) ≤
        fderiv ℝ (fderiv ℝ W) (WithLp.toLp 2 y) u u := by
    rw [hquad ⟨WithLp.toLp 2 y, simplex_subset_ambient N y hy⟩]
    exact interval_lower_aux p N hN
      ⟨WithLp.toLp 2 y, simplex_subset_ambient N y hy⟩ u 2 (by norm_num)
      (by simp only [ite_eq_right (by omega : ¬2 = (N : ℕ)), sub_zero, le_refl])
  refine ⟨W, hsm, hval, hd, ?_, ?_, hdouble, ?_⟩
  · intro y u hu
    have hnonneg (i : Fin (N : ℕ)) : 0 ≤ (y.val i) ^ (-p.val.2 - 2) * (u i) ^ 2 :=
      mul_nonneg (Real.rpow_nonneg (by
        have hi := y.property i 1 (by omega) (by omega)
        simpa only [gapSum_one] using hi.1.le) _) (sq_nonneg _)
    have hui : ∃ i, u i ≠ 0 := by
      by_contra h
      apply hu
      ext i
      change u i = 0
      exact not_not.mp (not_exists.mp h i)
    obtain ⟨i, hi⟩ := hui
    have hyi : 0 < y.val i := by
      simpa only [gapSum_one] using (y.property i 1 (by omega) (by omega)).1
    have hsum : 0 < ∑ i, (y.val i) ^ (-p.val.2 - 2) * (u i) ^ 2 :=
      lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos hyi _) (sq_pos_of_ne_zero hi))
        (Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i))
    exact (mul_pos (mul_pos p.property.2.1 (by linarith [p.property.2.1])) hsum).trans_le
      (hlow y u)
  · intro y hy u
    exact hlow ⟨WithLp.toLp 2 y, simplex_subset_ambient N y hy⟩ u
  · intro y hy u hu
    by_cases hN3 : 3 ≤ (N : ℕ)
    · exact hdouble y hy u hN3
    · have hN2 : N = 2 := PNat.coe_injective (by norm_num; omega)
      subst N
      rw [hquad ⟨WithLp.toLp 2 y, simplex_subset_ambient 2 y hy⟩]
      exact interval_two_tangent_lower p y hy u hu

/-- See Subsection 3.2 in the paper, all clauses with a single constant chosen
before the period, configuration, interval and rigidity parameter. Temperature
one is used solely to access the parameter interface: the kernel and all
of its derivatives are independent of temperature. -/
theorem coefficient_rigidity (s : Riesz1.RieszExponent) :
    let p : Parameters := ⟨(1, s.val), by
      exact ⟨one_pos, s.property.1, ne_of_lt s.property.2⟩⟩
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (_hN : 2 ≤ (N : ℕ))
      (y : Fin (N : ℕ) → ℝ) (hy : y ∈ Riesz1.gapSimplex N)
      (i : Fin (N : ℕ)) (r : ℕ) (hr : 1 ≤ r) (hrN : r ≤ (N : ℕ) / 2),
      let L : {L : ℝ // 0 < L ∧ L < (N : ℝ)} :=
        ⟨cyclicGapSum N i r y, gapSum_mem N i hr (by have := N.pos; omega) y hy⟩
      let R : {L : ℝ // 0 < L ∧ L < (N : ℝ)} := ⟨r, by
        have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
        have hr2 : 2 * r ≤ (N : ℕ) := by omega
        have hr2' : 2 * (r : ℝ) ≤ (N : ℝ) := by exact_mod_cast hr2
        exact ⟨hr0, by linarith⟩⟩
      (∀ A : ℝ, 1 ≤ A → |L.val - r| ≤ A * (r : ℝ) ^ (s.val / 2) →
        A * (r : ℝ) ^ (s.val / 2) ≤ (r : ℝ) / 2 →
        |intervalCoefficient p N L - intervalCoefficient p N R| ≤
          C * A * (r : ℝ) ^ (-3 - s.val / 2)) ∧
      (∀ a b : ℝ, 0 < a → a ≤ 1 → 1 ≤ b → (∀ j, a ≤ y j ∧ y j ≤ b) →
        s.val * (s.val + 1) * b ^ (-s.val - 2) * (r : ℝ) ^ (-s.val - 2) ≤
          intervalCoefficient p N L ∧
        intervalCoefficient p N L ≤ C * a ^ (-s.val - 2) * (r : ℝ) ^ (-s.val - 2)) ∧
      (∀ A : ℝ, 1 ≤ A → (2 * A) ^ (1 / (1 - s.val / 2)) ≤ (r : ℝ) →
        |L.val - r| ≤ A * (r : ℝ) ^ (s.val / 2) →
        |intervalCoefficient p N L - intervalCoefficient p N R| ≤
          C * A * (r : ℝ) ^ (-3 - s.val / 2)) := by
  let p : Parameters := ⟨(1, s.val), ⟨one_pos, s.property.1, ne_of_lt s.property.2⟩⟩
  refine ⟨coefficientConstant s.val s.property.1,
    coefficientConstant_pos s.val s.property.1, ?_⟩
  intro N hN y hy i r hr hrN
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hr2 : 2 * (r : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 2 * r ≤ (N : ℕ) by omega)
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro A _hA hdev hsmall
    exact coefficient_variation p N hr0 (by linarith) _ hdev hsmall
  · intro a b ha _ha1 _hb hab
    exact coefficient_gap_bounds p N i hr hrN y hy ha hab
  · intro A hA hthreshold hdev
    exact coefficient_variation p N hr0 (by linarith) _ hdev
      (rigidity_threshold s.property.2 hA hr0 hthreshold)

/-- Positive-order kernel derivatives depend only on the exponent. -/
theorem kernelDerivative_eq_of_exponent_eq (p q : Parameters) (h : p.val.2 = q.val.2)
    (j : ℕ+) (x : OffLattice) : kernelDerivative p j x = kernelDerivative q j x := by
  unfold kernelDerivative
  simp only [h]

/-- The physical interval coefficient is independent of the temperature slot
of the parameter interface. -/
theorem intervalCoefficient_eq_of_exponent_eq (p q : Parameters) (h : p.val.2 = q.val.2)
    (N : ℕ+) (L : {L : ℝ // 0 < L ∧ L < (N : ℝ)}) :
    intervalCoefficient p N L = intervalCoefficient q N L := by
  unfold intervalCoefficient
  rw [h, kernelDerivative_eq_of_exponent_eq p q h]

/-- Bridge to the matrix Hessian: its quadratic form is the bilinear
second Fréchet derivative. This identifies the Hessian convention used above
with the convention in physical weak equations. -/
theorem hessianMatrix_quadratic {n : ℕ} {W : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hW : ContDiffAt ℝ 2 W x)
    (u : EuclideanSpace ℝ (Fin n)) :
    (∑ i, ∑ j, u i * hessianMatrix W x i j * u j) =
      fderiv ℝ (fderiv ℝ W) x u u := by
  classical
  have hdf : DifferentiableAt ℝ (fderiv ℝ W) x :=
    (hW.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [← Riesz1.inner_fderiv_gradient hdf u u]
  let T := fderiv ℝ (gradient W) x
  have hu : (∑ j : Fin n, u j • EuclideanSpace.single j 1) = u := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr u
  have hcoord (i : Fin n) : T u i =
      ∑ j : Fin n, (T (EuclideanSpace.single j 1)) i * u j := by
    conv_lhs => rw [← hu, map_sum]
    simp only [map_smul, WithLp.ofLp_sum, Finset.sum_apply,
      WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  change _ = ∑ i, u i * T u i
  simp_rw [hcoord, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [hessianMatrix, T]
  ring

end Riesz2.PhysicalEnergy
