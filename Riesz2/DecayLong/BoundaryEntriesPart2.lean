/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.BoundaryEntries
public import Riesz2.DecayLong.GoodBlocksPart3
public import Riesz2.Frozen.ReferenceIntervalMatrix

/-!
# Density-defined physical crossing coefficients

The crossing coefficients in the proof of Lemma 5.6 are finite sums of
conditional interval coefficients. The conditional measure and ambient
Hessian are those of `GoodBlocks`, on the open retained carrier.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped BigOperators Classical

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.BoundaryEntries

/-- The summand of the ambient interval Hessian, including its
antipodal multiplicity (Subsection 5.1). At physical points its
identification with `PhysicalEnergy.intervalCoefficient` is proved below. -/
def intervalWeight (s : Riesz1.RieszExponent) (N : ℕ+)
    (r : Fin ((N : ℕ) / 2)) (i : Fin (N : ℕ))
    (y : EuclideanSpace ℝ (Fin (N : ℕ))) : ℝ :=
  (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
    ((N : ℝ) ^ (-s.val - 2) *
      iteratedDeriv 2 (fun t : ℝ => Riesz1.rieszRepresentative s t)
        (cyclicGapSum N i (r.val + 1) (WithLp.ofLp y) / (N : ℝ)))

theorem measurable_intervalWeight (s : Riesz1.RieszExponent) (N : ℕ+)
    (r : Fin ((N : ℕ) / 2)) (i : Fin (N : ℕ)) :
    Measurable (intervalWeight s N r i) := by
  apply Measurable.const_mul
  apply Measurable.const_mul
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  apply (measurable_deriv (deriv (fun t : ℝ => Riesz1.rieszRepresentative s t))).comp
  simpa only [PhysicalEnergy.intervalLinear_apply] using
    ((PhysicalEnergy.intervalLinear N i (r.val + 1)).continuous.div_const (N : ℝ)).measurable

/-- Bridge from the differential summand to the existing physical coefficient
on the entire positive simplex, with the antipodal multiplicity. -/
theorem intervalWeight_physical (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (r : Fin ((N : ℕ) / 2)) (i : Fin (N : ℕ))
    (y : EuclideanSpace ℝ (Fin (N : ℕ)))
    (hy : WithLp.ofLp y ∈ Riesz1.gapSimplex N) :
    intervalWeight s N r i y =
      (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
        PhysicalEnergy.intervalCoefficient (ofLong β s) N
          ⟨cyclicGapSum N i (r.val + 1) (WithLp.ofLp y),
            PhysicalEnergy.gapSum_mem N i (by omega)
              (lt_of_le_of_lt (Nat.succ_le_of_lt r.isLt)
                (Nat.div_lt_self N.pos (by norm_num))) _ hy⟩ := by
  simp only [intervalWeight, PhysicalEnergy.intervalCoefficient,
    PhysicalEnergy.kernelDerivative, ofLong, s.property.2, ↓reduceDIte,
    PhysicalEnergy.scaledSeparation, PNat.val_ofNat]

theorem intervalWeight_nonneg (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (r : Fin ((N : ℕ) / 2)) (i : Fin (N : ℕ))
    (y : EuclideanSpace ℝ (Fin (N : ℕ)))
    (hy : WithLp.ofLp y ∈ Riesz1.gapSimplex N) : 0 ≤ intervalWeight s N r i y := by
  rw [intervalWeight_physical β s N r i y hy]
  exact mul_nonneg (by split_ifs <;> norm_num)
    (PhysicalEnergy.intervalCoefficient_pos _ _ _).le

/-- The original ambient Hessian is the sum of these very coefficients. -/
theorem gapHessian_intervalWeight (s : Riesz1.RieszExponent) (N : ℕ+)
    (a b : Fin (N : ℕ)) (y : EuclideanSpace ℝ (Fin (N : ℕ))) :
    GoodBlocks.gapHessian s N a b y =
      ∑ r : Fin ((N : ℕ) / 2), ∑ i : Fin (N : ℕ),
        if a ∈ cyclicIndexInterval N i (r.val + 1) ∧
          b ∈ cyclicIndexInterval N i (r.val + 1) then intervalWeight s N r i y else 0 := rfl

private theorem start_mem (N : ℕ+) (r : Fin ((N : ℕ) / 2)) (i : Fin (N : ℕ)) :
    i ∈ cyclicIndexInterval N i (r.val + 1) := by
  rw [mem_cyclicIndexInterval_iff N i i
    ((Nat.succ_le_of_lt r.isLt).trans (Nat.div_le_self _ _))]
  simp

/-- Each physical interval summand is dominated by a diagonal Hessian entry.
This domination supplies integrability before any conditional sum is split. -/
theorem intervalWeight_le_diagonal (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (r : Fin ((N : ℕ) / 2)) (i : Fin (N : ℕ))
    (y : EuclideanSpace ℝ (Fin (N : ℕ)))
    (hy : WithLp.ofLp y ∈ Riesz1.gapSimplex N) :
    intervalWeight s N r i y ≤ GoodBlocks.gapHessian s N i i y := by
  rw [gapHessian_intervalWeight]
  have ht (q : Fin ((N : ℕ) / 2)) (j : Fin (N : ℕ)) :
      0 ≤ if i ∈ cyclicIndexInterval N j (q.val + 1) ∧
        i ∈ cyclicIndexInterval N j (q.val + 1) then intervalWeight s N q j y else 0 := by
    split_ifs
    · exact intervalWeight_nonneg β s N q j y hy
    · exact le_rfl
  calc
    _ = if i ∈ cyclicIndexInterval N i (r.val + 1) ∧
        i ∈ cyclicIndexInterval N i (r.val + 1) then intervalWeight s N r i y else 0 := by
          rw [ite_eq_left ⟨start_mem N r i, start_mem N r i⟩]
    _ ≤ ∑ j : Fin (N : ℕ), if i ∈ cyclicIndexInterval N j (r.val + 1) ∧
        i ∈ cyclicIndexInterval N j (r.val + 1) then intervalWeight s N r j y else 0 :=
      Finset.single_le_sum (fun j _ => ht r j) (Finset.mem_univ i)
    _ ≤ _ := Finset.single_le_sum
      (fun q _ => Finset.sum_nonneg fun j _ => ht q j) (Finset.mem_univ r)

private theorem fibre_simplex (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    ∀ᵐ z ∂ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x,
      WithLp.ofLp (RetainedSimplex.chart n m ((n + m : ℕ) + 1)
        (Equiv.refl _) (x.val, z)) ∈ Riesz1.gapSimplex ((n : ℕ) + m).succPNat := by
  filter_upwards [ConditionalEnergyMoments.physical_conditional_support
    (ofLong β s) n m n.pos (Equiv.refl _) x] with z hz
  have hd := (Set.ext_iff.mp (RetainedSimplex.fibre_domain n m _ x.property) z).mpr hz
  have hy := (RetainedSimplex.chart_mem_simplex n m _ (Equiv.refl _) _).mpr hd
  exact ⟨hy.1, by simpa only [Nat.succPNat_coe, Nat.cast_succ] using hy.2⟩

/-- Every individual interval coefficient is integrable on every interior
conditional fibre, including the zero-dimensional fibre. -/
theorem integrable_intervalWeight (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (r : Fin (((n : ℕ) + m + 1) / 2)) (i : Fin ((n : ℕ) + m + 1)) :
    Integrable (fun z => intervalWeight s ((n : ℕ) + m).succPNat r i
      (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val, z)))
      (ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x) := by
  apply (GoodBlocks.integrable_chartHessian β s n m n.pos x i i).mono'
    (((measurable_intervalWeight s ((n : ℕ) + m).succPNat r i).comp
      (RetainedSimplex.continuous_chart n m _ (Equiv.refl _)).measurable).comp
        measurable_prodMk_left).aestronglyMeasurable
  filter_upwards [fibre_simplex β s n m x] with z hz
  simpa only [Function.comp_apply, GoodBlocks.chartHessian, Real.norm_of_nonneg
    (intervalWeight_nonneg β s ((n : ℕ) + m).succPNat r i _ hz)] using
    intervalWeight_le_diagonal β s ((n : ℕ) + m).succPNat r i _ hz

/-- See Subsection 5.1 of the paper: the actual density-defined conditional
interval coefficient. The active tilt is constant on this fibre. -/
def conditionalIntervalWeight (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (r : Fin (((n : ℕ) + m + 1) / 2))
    (i : Fin ((n : ℕ) + m + 1))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) : ℝ :=
  ∫ z, intervalWeight s ((n : ℕ) + m).succPNat r i
    (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val, z))
    ∂ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x

theorem measurable_conditionalIntervalWeight (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (r : Fin (((n : ℕ) + m + 1) / 2)) (i : Fin ((n : ℕ) + m + 1)) :
    Measurable (conditionalIntervalWeight β s n m r i) := by
  let f := fun q : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) ×
      EuclideanSpace ℝ (Fin m) => intervalWeight s ((n : ℕ) + m).succPNat r i
        (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (q.1.val, q.2))
  have hf : Measurable f := (measurable_intervalWeight s ((n : ℕ) + m).succPNat r i).comp
    ((RetainedSimplex.continuous_chart n m _ (Equiv.refl _)).measurable.comp
      ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd))
  exact (hf.stronglyMeasurable.integral_kernel_prod_right'
    (κ := ProperMarginalChart.conditionalKernel (ofLong β s) n m n.pos (Equiv.refl _))).measurable

theorem conditionalIntervalWeight_nonneg (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (r : Fin (((n : ℕ) + m + 1) / 2)) (i : Fin ((n : ℕ) + m + 1))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    0 ≤ conditionalIntervalWeight β s n m r i x := by
  apply integral_nonneg_of_ae
  filter_upwards [fibre_simplex β s n m x] with z hz
  exact intervalWeight_nonneg β s ((n : ℕ) + m).succPNat r i _ hz

/-- Exact finite interval expansion of the density-defined matrix.
Linearity uses the pointwise integrability certificate above. -/
theorem conditionalHessian_intervalWeight (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ) (a b : Fin (n : ℕ))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    GoodBlocks.conditionalHessian β s n m a b x =
      ∑ r : Fin (((n : ℕ) + m + 1) / 2), ∑ i : Fin ((n : ℕ) + m + 1),
        if (a.castAdd m).castSucc ∈ cyclicIndexInterval ((n : ℕ) + m).succPNat i (r.val + 1) ∧
          (b.castAdd m).castSucc ∈ cyclicIndexInterval ((n : ℕ) + m).succPNat i (r.val + 1)
        then conditionalIntervalWeight β s n m r i x else 0 := by
  classical
  unfold GoodBlocks.conditionalHessian GoodBlocks.chartHessian
  simp_rw [gapHessian_intervalWeight]
  simp only [Nat.succPNat_coe]
  have hi (r : Fin (((n : ℕ) + m + 1) / 2)) (i : Fin ((n : ℕ) + m + 1)) :
      Integrable (fun z =>
        if (a.castAdd m).castSucc ∈ cyclicIndexInterval ((n : ℕ) + m).succPNat i (r.val + 1) ∧
          (b.castAdd m).castSucc ∈ cyclicIndexInterval ((n : ℕ) + m).succPNat i (r.val + 1)
        then intervalWeight s ((n : ℕ) + m).succPNat r i
          (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val, z)) else 0)
        (ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x) := by
    split_ifs
    · exact integrable_intervalWeight β s n m x r i
    · exact integrable_zero _ _ _
  rw [integral_finsetSum _ (fun r _ => integrable_finsetSum _ (fun i _ => hi r i))]
  apply Finset.sum_congr rfl
  intro r _
  rw [integral_finsetSum _ (fun i _ => hi r i)]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp only [conditionalIntervalWeight, integral_zero]

/-- The active indices as a subset of the ambient cycle. -/
def activeIndices (N : ℕ+) (n : ℕ) : Finset (Fin (N : ℕ)) :=
  Finset.univ.filter fun a => a.val < n

/-- In a window occupying at most half the circle, a short cyclic interval
has the ordinary interval trace if its start is active, and a prefix trace
if its start is exterior. This is the topology step of Subsection 5.1. -/
theorem mem_interval_active (N : ℕ+) {n r : ℕ} (hn : 2 * n ≤ (N : ℕ))
    (hr : 2 * r ≤ (N : ℕ)) (i a : Fin (N : ℕ)) (ha : a.val < n) :
    a ∈ cyclicIndexInterval N i r ↔
      if i.val < n then i.val ≤ a.val ∧ a.val < i.val + r
      else a.val < i.val + r - (N : ℕ) := by
  rw [mem_cyclicIndexInterval_iff N i a (by omega), Fin.val_sub]
  have hi := i.isLt
  have haN := a.isLt
  by_cases hia : i.val ≤ a.val
  · have hmod : ((N : ℕ) - i.val + a.val) % (N : ℕ) = a.val - i.val := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hmod, ite_eq_left (by omega)]
    omega
  · have hmod : ((N : ℕ) - i.val + a.val) % (N : ℕ) = (N : ℕ) - i.val + a.val :=
      Nat.mod_eq_of_lt (by omega)
    rw [hmod]
    split_ifs <;> omega

/-- An interval starting in the active window and crossing its boundary
extends strictly past the right endpoint. Short intervals cannot wrap back
through the whole exterior arc. -/
theorem crossing_active_start (N : ℕ+) {n r : ℕ} (hn : 2 * n ≤ (N : ℕ))
    (hr : 2 * r ≤ (N : ℕ)) (i : Fin (N : ℕ)) (_hi : i.val < n)
    (hc : ¬cyclicIndexInterval N i r ⊆ activeIndices N n) : n < i.val + r := by
  by_contra h
  apply hc
  intro a ha
  obtain ⟨t, ht, he⟩ := Finset.mem_image.mp ha
  have ht := Finset.mem_range.mp ht
  have hsum : i.val + t < (N : ℕ) := by omega
  have hae : a.val = i.val + t := by
    have hh := congrArg Fin.val he
    simpa only [Nat.mod_eq_of_lt hsum] using hh.symm
  simp only [activeIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  omega

/-- The exact trace of a crossing interval whose initial point is active
is its terminal active suffix, including the full window when the start is 0. -/
theorem crossing_active_trace (N : ℕ+) {n r : ℕ} (hn : 2 * n ≤ (N : ℕ))
    (hr : 2 * r ≤ (N : ℕ)) (i : Fin (N : ℕ)) (hi : i.val < n)
    (hc : ¬cyclicIndexInterval N i r ⊆ activeIndices N n) :
    cyclicIndexInterval N i r ∩ activeIndices N n =
      (activeIndices N n).filter fun a => i.val ≤ a.val := by
  have hcross := crossing_active_start N hn hr i hi hc
  ext a
  simp only [Finset.mem_inter, activeIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases ha : a.val < n
  · rw [mem_interval_active N hn hr i a ha, ite_eq_left hi]
    simp only [ha, and_true, true_and]
    omega
  · simp [ha]

/-- The exact active trace of an interval starting in the exterior is a
prefix (possibly empty or full). -/
theorem exterior_start_trace (N : ℕ+) {n r : ℕ} (hn : 2 * n ≤ (N : ℕ))
    (hr : 2 * r ≤ (N : ℕ)) (i : Fin (N : ℕ)) (_hi : n ≤ i.val) :
    cyclicIndexInterval N i r ∩ activeIndices N n =
      activeIndices N (min n (i.val + r - (N : ℕ))) := by
  ext a
  simp only [Finset.mem_inter, activeIndices, Finset.mem_filter, Finset.mem_univ,
    true_and, lt_min_iff]
  by_cases ha : a.val < n
  · rw [mem_interval_active N hn hr i a ha, ite_eq_right (by omega)]
    tauto
  · simp [ha]

/-- Complete geometric classification used in Subsection 5.1.
The alternatives allow empty families of either endpoint type. -/
theorem crossing_trace_cases (N : ℕ+) (n : ℕ+)
    (hn : 2 * (n : ℕ) ≤ (N : ℕ)) {r : ℕ} (hr : 2 * r ≤ (N : ℕ))
    (i : Fin (N : ℕ)) (hc : ¬cyclicIndexInterval N i r ⊆ activeIndices N n) :
    cyclicIndexInterval N i r ∩ activeIndices N n = ∅ ∨
    cyclicIndexInterval N i r ∩ activeIndices N n = activeIndices N n ∨
    (∃ j : Fin ((n : ℕ) - 1), cyclicIndexInterval N i r ∩ activeIndices N n =
      activeIndices N (j.val + 1)) ∨
    (∃ j : Fin ((n : ℕ) - 1), cyclicIndexInterval N i r ∩ activeIndices N n =
      (activeIndices N n).filter fun a => j.val < a.val) := by
  by_cases hi : i.val < (n : ℕ)
  · rw [crossing_active_trace N hn hr i hi hc]
    by_cases hz : i.val = 0
    · right; left
      ext a
      simp [hz]
    · right; right; right
      let j : Fin ((n : ℕ) - 1) := ⟨i.val - 1, by omega⟩
      refine ⟨j, ?_⟩
      ext a
      simp only [Finset.mem_filter]
      change (a ∈ activeIndices N n ∧ i.val ≤ a.val) ↔
        (a ∈ activeIndices N n ∧ i.val - 1 < a.val)
      constructor
      · rintro ⟨ha, hia⟩
        exact ⟨ha, by omega⟩
      · rintro ⟨ha, hia⟩
        exact ⟨ha, by omega⟩
  · rw [exterior_start_trace N hn hr i (by omega)]
    by_cases hfull : (n : ℕ) ≤ i.val + r - (N : ℕ)
    · right; left
      rw [min_eq_left hfull]
    · rw [min_eq_right (by omega)]
      by_cases hz : i.val + r - (N : ℕ) = 0
      · left
        simp [hz, activeIndices]
      · right; right; left
        let j : Fin ((n : ℕ) - 1) := ⟨i.val + r - (N : ℕ) - 1, by omega⟩
        refine ⟨j, ?_⟩
        have he : j.val + 1 = i.val + r - (N : ℕ) := by dsimp [j]; omega
        rw [he]

private theorem activeIndices_eq_iff (N : ℕ+) {a b : ℕ}
    (ha : a ≤ (N : ℕ)) (hb : b ≤ (N : ℕ)) :
    activeIndices N a = activeIndices N b ↔ a = b := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  by_contra hab
  rcases lt_or_gt_of_ne hab with hab | hab
  · let j : Fin (N : ℕ) := ⟨a, by omega⟩
    have hj := Finset.ext_iff.mp h j
    simp only [activeIndices, Finset.mem_filter, Finset.mem_univ, true_and, j] at hj
    omega
  · let j : Fin (N : ℕ) := ⟨b, by omega⟩
    have hj := Finset.ext_iff.mp h j
    simp only [activeIndices, Finset.mem_filter, Finset.mem_univ, true_and, j] at hj
    omega

private theorem prefix_eq_prefix (N : ℕ+) (n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ))
    (j k : Fin ((n : ℕ) - 1)) :
    activeIndices N (j.val + 1) = activeIndices N (k.val + 1) ↔ j = k := by
  rw [activeIndices_eq_iff N (by omega) (by omega)]
  simp only [Fin.ext_iff]
  omega

private theorem suffix_eq_suffix (N : ℕ+) (n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ))
    (j k : Fin ((n : ℕ) - 1)) :
    (activeIndices N n).filter (fun a => j.val < a.val) =
      (activeIndices N n).filter (fun a => k.val < a.val) ↔ j = k := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  apply Fin.ext
  by_contra hjk
  rcases lt_or_gt_of_ne hjk with hjk | hjk
  · let a : Fin (N : ℕ) := ⟨j.val + 1, by have := j.isLt; omega⟩
    have he := Finset.ext_iff.mp h a
    simp only [Finset.mem_filter, activeIndices, Finset.mem_univ, true_and, a] at he
    have := j.isLt
    omega
  · let a : Fin (N : ℕ) := ⟨k.val + 1, by have := k.isLt; omega⟩
    have he := Finset.ext_iff.mp h a
    simp only [Finset.mem_filter, activeIndices, Finset.mem_univ, true_and, a] at he
    have := k.isLt
    omega

private theorem prefix_ne_full (N : ℕ+) (n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ))
    (j : Fin ((n : ℕ) - 1)) : activeIndices N (j.val + 1) ≠ activeIndices N n := by
  intro h
  have he := (activeIndices_eq_iff N (a := j.val + 1)
    (by have := j.isLt; omega) hn).mp h
  have := j.isLt
  omega

private theorem suffix_ne_full (N : ℕ+) (n : ℕ+) (_hn : (n : ℕ) ≤ (N : ℕ))
    (j : Fin ((n : ℕ) - 1)) :
    (activeIndices N n).filter (fun a => j.val < a.val) ≠ activeIndices N n := by
  intro h
  have he := Finset.ext_iff.mp h ⟨0, N.pos⟩
  simp only [Finset.mem_filter, activeIndices, Finset.mem_univ, true_and] at he
  have := n.pos
  simp at he

private theorem prefix_ne_suffix (N : ℕ+) (n : ℕ+)
    (j k : Fin ((n : ℕ) - 1)) :
    activeIndices N (j.val + 1) ≠
      (activeIndices N n).filter (fun a => k.val < a.val) := by
  intro h
  have he := Finset.ext_iff.mp h ⟨0, N.pos⟩
  simp [activeIndices] at he

private theorem prefix_ne_empty (N : ℕ+) (n : ℕ+) (j : Fin ((n : ℕ) - 1)) :
    activeIndices N (j.val + 1) ≠ ∅ := by
  intro h
  have he := Finset.ext_iff.mp h ⟨0, N.pos⟩
  simp [activeIndices] at he

private theorem full_ne_empty (N : ℕ+) (n : ℕ+) : activeIndices N n ≠ ∅ := by
  intro h
  have he := Finset.ext_iff.mp h ⟨0, N.pos⟩
  simp [activeIndices] at he

private theorem suffix_ne_empty (N : ℕ+) (n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ))
    (j : Fin ((n : ℕ) - 1)) :
    (activeIndices N n).filter (fun a => j.val < a.val) ≠ ∅ := by
  intro h
  let a : Fin (N : ℕ) := ⟨j.val + 1, by have := j.isLt; omega⟩
  have he := Finset.ext_iff.mp h a
  simp only [Finset.mem_filter, activeIndices, Finset.mem_univ, true_and,
    Finset.notMem_empty, iff_false, a] at he
  have := j.isLt
  omega

private theorem trace_group_entry (N : ℕ+) (n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ))
    (T : Finset (Fin (N : ℕ)))
    (hT : T = ∅ ∨ T = activeIndices N n ∨
      (∃ j : Fin ((n : ℕ) - 1), T = activeIndices N (j.val + 1)) ∨
      (∃ j : Fin ((n : ℕ) - 1), T =
        (activeIndices N n).filter fun a => j.val < a.val))
    (a b : Fin (n : ℕ)) (c : ℝ) :
    groupedBoundaryMatrix n
      (fun j => if T = activeIndices N (j.val + 1) then c else 0)
      (fun j => if T = (activeIndices N n).filter (fun a => j.val < a.val) then c else 0)
      (if T = activeIndices N n then c else 0) a b =
        if a.castLE hn ∈ T ∧ b.castLE hn ∈ T then c else 0 := by
  rcases hT with h | h | ⟨j, h⟩ | ⟨j, h⟩
  · subst T
    simp [groupedBoundaryMatrix_apply, Ne.symm (full_ne_empty N n),
      fun j => Ne.symm (prefix_ne_empty N n j),
      fun j => Ne.symm (suffix_ne_empty N n hn j)]
  · subst T
    have ha : a.castLE hn ∈ activeIndices N n := by simp [activeIndices]
    have hb : b.castLE hn ∈ activeIndices N n := by simp [activeIndices]
    simp [groupedBoundaryMatrix_apply, ha, hb,
      fun j => Ne.symm (prefix_ne_full N n hn j),
      fun j => Ne.symm (suffix_ne_full N n hn j)]
  · subst T
    simp only [groupedBoundaryMatrix_apply, prefix_eq_prefix N n hn,
      prefix_ne_full N n hn j, prefix_ne_suffix N n j, ↓reduceIte]
    have hs : (∑ k : Fin ((n : ℕ) - 1),
        if a.val ≤ k.val ∧ b.val ≤ k.val then (if j = k then c else 0) else 0) =
        if a.val ≤ j.val ∧ b.val ≤ j.val then c else 0 := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hk
        simp [Ne.symm hk]
      · simp
    rw [hs]
    simp [activeIndices, ite_and]
  · subst T
    simp only [groupedBoundaryMatrix_apply, suffix_eq_suffix N n hn,
      suffix_ne_full N n hn j, fun k => Ne.symm (prefix_ne_suffix N n k j),
      ↓reduceIte]
    have hs : (∑ k : Fin ((n : ℕ) - 1),
        if k.val < a.val ∧ k.val < b.val then (if j = k then c else 0) else 0) =
        if j.val < a.val ∧ j.val < b.val then c else 0 := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hk
        simp [Ne.symm hk]
      · simp
    rw [hs]
    simp [activeIndices, ite_and]

private theorem groupedBoundaryMatrix_sum {ι : Type*} [Fintype ι] (n : ℕ)
    (u v : ι → Fin (n - 1) → ℝ) (d : ι → ℝ) :
    groupedBoundaryMatrix n (fun j => ∑ t, u t j) (fun j => ∑ t, v t j) (∑ t, d t) =
      ∑ t, groupedBoundaryMatrix n (u t) (v t) (d t) := by
  ext a b
  simp only [Matrix.sum_apply, groupedBoundaryMatrix_apply, Finset.sum_add_distrib]
  have hp : (∑ j : Fin (n - 1),
      if a.val ≤ j.val ∧ b.val ≤ j.val then ∑ t, u t j else 0) =
      ∑ t, ∑ j : Fin (n - 1), if a.val ≤ j.val ∧ b.val ≤ j.val then u t j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  have hs : (∑ j : Fin (n - 1),
      if j.val < a.val ∧ j.val < b.val then ∑ t, v t j else 0) =
      ∑ t, ∑ j : Fin (n - 1), if j.val < a.val ∧ j.val < b.val then v t j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  rw [hp, hs]

/-- The physical internal block of Subsection 5.1. The retained
coordinates are consecutive and are embedded by the chart embedding. -/
def physicalInternal (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ := fun a b =>
  ∑ r : Fin (((n : ℕ) + m + 1) / 2), ∑ i : Fin ((n : ℕ) + m + 1),
    if cyclicIndexInterval ((n : ℕ) + m).succPNat i (r.val + 1) ⊆
        activeIndices ((n : ℕ) + m).succPNat n ∧
      (a.castAdd m).castSucc ∈ cyclicIndexInterval ((n : ℕ) + m).succPNat i (r.val + 1) ∧
      (b.castAdd m).castSucc ∈ cyclicIndexInterval ((n : ℕ) + m).succPNat i (r.val + 1)
    then conditionalIntervalWeight β s n m r i x else 0

/-- The physical crossing block of Subsection 5.1, as a finite sum
of the density-defined conditional coefficients. Intervals disjoint from the
active window make their actual zero contribution. -/
def physicalCrossing (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ := fun a b =>
  ∑ r : Fin (((n : ℕ) + m + 1) / 2), ∑ i : Fin ((n : ℕ) + m + 1),
    if ¬cyclicIndexInterval ((n : ℕ) + m).succPNat i (r.val + 1) ⊆
        activeIndices ((n : ℕ) + m).succPNat n ∧
      (a.castAdd m).castSucc ∈ cyclicIndexInterval ((n : ℕ) + m).succPNat i (r.val + 1) ∧
      (b.castAdd m).castSucc ∈ cyclicIndexInterval ((n : ℕ) + m).succPNat i (r.val + 1)
    then conditionalIntervalWeight β s n m r i x else 0

/-- Bridge to `P_I`: the internal and crossing matrices partition
its very interval coefficients, with no change of conditional version. -/
theorem physicalInternal_add_crossing (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (a b : Fin (n : ℕ)) :
    physicalInternal β s n m x a b + physicalCrossing β s n m x a b =
      GoodBlocks.conditionalHessian β s n m a b x := by
  rw [conditionalHessian_intervalWeight]
  unfold physicalInternal physicalCrossing
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all

theorem physicalInternal_nonneg (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (a b : Fin (n : ℕ)) : 0 ≤ physicalInternal β s n m x a b := by
  apply Finset.sum_nonneg
  intro r _
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact conditionalIntervalWeight_nonneg β s n m r i x
  · exact le_rfl

theorem physicalCrossing_nonneg (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (a b : Fin (n : ℕ)) : 0 ≤ physicalCrossing β s n m x a b := by
  apply Finset.sum_nonneg
  intro r _
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact conditionalIntervalWeight_nonneg β s n m r i x
  · exact le_rfl

theorem measurable_physicalCrossing (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (a b : Fin (n : ℕ)) :
    Measurable (fun x => physicalCrossing β s n m x a b) := by
  apply Finset.measurable_sum
  intro r _
  apply Finset.measurable_sum
  intro i _
  split_ifs
  · exact measurable_conditionalIntervalWeight β s n m r i
  · exact measurable_const

theorem physicalCrossing_le_hessian (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (a b : Fin (n : ℕ)) :
    physicalCrossing β s n m x a b ≤ GoodBlocks.conditionalHessian β s n m a b x := by
  rw [← physicalInternal_add_crossing]
  exact le_add_of_nonneg_left (physicalInternal_nonneg β s n m x a b)

/-- Positivity of the actual crossing block, before any coefficient estimate.
Each conditional coefficient multiplies its active indicator square. -/
theorem physicalCrossing_posSemidef (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    (physicalCrossing β s n m x).PosSemidef := by
  let v (r : Fin (((n : ℕ) + m + 1) / 2)) (i : Fin ((n : ℕ) + m + 1))
      (a : Fin (n : ℕ)) : ℝ :=
    if (a.castAdd m).castSucc ∈ cyclicIndexInterval ((n : ℕ) + m).succPNat i (r.val + 1)
    then 1 else 0
  let M : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ :=
    ∑ r : Fin (((n : ℕ) + m + 1) / 2), ∑ i : Fin ((n : ℕ) + m + 1),
      if ¬cyclicIndexInterval ((n : ℕ) + m).succPNat i (r.val + 1) ⊆
          activeIndices ((n : ℕ) + m).succPNat n
      then conditionalIntervalWeight β s n m r i x • Matrix.vecMulVec (v r i) (v r i)
      else 0
  have hM : M.PosSemidef := by
    dsimp only [M]
    apply Matrix.posSemidef_sum
    intro r _
    apply Matrix.posSemidef_sum
    intro i _
    by_cases hc : ¬cyclicIndexInterval ((n : ℕ) + m).succPNat i (r.val + 1) ⊆
        activeIndices ((n : ℕ) + m).succPNat n
    · rw [ite_eq_left hc]
      exact (FiniteMatrixOrder.posSemidef_vecMulVec_self (v r i)).smul
        (conditionalIntervalWeight_nonneg β s n m r i x)
    · rw [ite_eq_right hc]
      exact Matrix.PosSemidef.zero
  have he : physicalCrossing β s n m x = M := by
    ext a b
    simp only [physicalCrossing, M, Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro i _
    by_cases hc : ¬cyclicIndexInterval ((n : ℕ) + m).succPNat i (r.val + 1) ⊆
        activeIndices ((n : ℕ) + m).succPNat n <;>
      by_cases ha : (a.castAdd m).castSucc ∈
        cyclicIndexInterval ((n : ℕ) + m).succPNat i (r.val + 1) <;>
      by_cases hb : (b.castAdd m).castSucc ∈
        cyclicIndexInterval ((n : ℕ) + m).succPNat i (r.val + 1) <;>
      simp [v, hc, ha, hb, Matrix.vecMulVec_apply]
  rwa [he]

/-- See Subsection 5.1 of the paper: sum precisely those conditional interval
coefficients with the prescribed active intersection. The crossing condition
excludes internal intervals even when their trace has the same shape. -/
def physicalGroup (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (T : Finset (Fin ((n : ℕ) + m + 1))) : ℝ :=
  ∑ r : Fin (((n : ℕ) + m + 1) / 2), ∑ i : Fin ((n : ℕ) + m + 1),
    if ¬cyclicIndexInterval ((n : ℕ) + m).succPNat i (r.val + 1) ⊆
        activeIndices ((n : ℕ) + m).succPNat n ∧
      cyclicIndexInterval ((n : ℕ) + m).succPNat i (r.val + 1) ∩
        activeIndices ((n : ℕ) + m).succPNat n = T
    then conditionalIntervalWeight β s n m r i x else 0

/-- The physical prefix coefficients of Subsection 5.1, indexed by cuts. -/
def physicalPrefix (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (j : Fin ((n : ℕ) - 1)) : ℝ :=
  physicalGroup β s n m x (activeIndices ((n : ℕ) + m).succPNat (j.val + 1))

/-- The physical suffix coefficients of Subsection 5.1, indexed by cuts. -/
def physicalSuffix (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (j : Fin ((n : ℕ) - 1)) : ℝ :=
  physicalGroup β s n m x
    ((activeIndices ((n : ℕ) + m).succPNat n).filter fun a => j.val < a.val)

/-- The full-intersection coefficient of the physical crossing block,
including the one-gap case (Subsection 5.1). -/
def physicalFull (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) : ℝ :=
  physicalGroup β s n m x (activeIndices ((n : ℕ) + m).succPNat n)

theorem physicalGroup_nonneg (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (T : Finset (Fin ((n : ℕ) + m + 1))) : 0 ≤ physicalGroup β s n m x T := by
  apply Finset.sum_nonneg
  intro r _
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact conditionalIntervalWeight_nonneg β s n m r i x
  · exact le_rfl

theorem measurable_physicalGroup (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (T : Finset (Fin ((n : ℕ) + m + 1))) :
    Measurable (fun x => physicalGroup β s n m x T) := by
  apply Finset.measurable_sum
  intro r _
  apply Finset.measurable_sum
  intro i _
  split_ifs
  · exact measurable_conditionalIntervalWeight β s n m r i
  · exact measurable_const

/-- Any grouped coefficient is bounded by every crossing entry whose two
labels belong to that group's intersection. -/
theorem physicalGroup_le_crossing (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (T : Finset (Fin ((n : ℕ) + m + 1))) (a b : Fin (n : ℕ))
    (ha : (a.castAdd m).castSucc ∈ T) (hb : (b.castAdd m).castSucc ∈ T) :
    physicalGroup β s n m x T ≤ physicalCrossing β s n m x a b := by
  apply Finset.sum_le_sum
  intro r _
  apply Finset.sum_le_sum
  intro i _
  split_ifs with h h' h'
  · exact le_rfl
  · have haa := (Finset.mem_inter.mp (h.2 ▸ ha)).1
    have hbb := (Finset.mem_inter.mp (h.2 ▸ hb)).1
    exact False.elim (h' ⟨h.1, haa, hbb⟩)
  · exact conditionalIntervalWeight_nonneg β s n m r i x
  · exact le_rfl

theorem physicalFull_le_hessian (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (a b : Fin (n : ℕ)) :
    physicalFull β s n m x ≤ GoodBlocks.conditionalHessian β s n m a b x := by
  apply (physicalGroup_le_crossing β s n m x _ a b ?_ ?_).trans
    (physicalCrossing_le_hessian β s n m x a b)
  · simpa only [activeIndices, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.val_castSucc, Fin.val_castAdd] using a.isLt
  · simpa only [activeIndices, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.val_castSucc, Fin.val_castAdd] using b.isLt

/-- The full-intersection clause of the proof of Lemma 5.6, for the actual physical coefficients.
The constant is one, the exponent is the good-event exponent, and `n=1`
is included. -/
theorem physical_full_bound (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (ε κ₀ : ℝ) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (hx : x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀) :
    physicalFull β s n m x ≤ (n : ℝ) ^ (κ₀ * ε) * (n : ℝ) ^ (-s.val) := by
  let a : Fin (n : ℕ) := ⟨0, n.pos⟩
  let b : Fin (n : ℕ) := ⟨(n : ℕ) - 1, by have := n.pos; omega⟩
  have hdist : Riesz1.cyclicIndexDistance ((n : ℕ) + m).succPNat
      (a.castAdd m).castSucc (b.castAdd m).castSucc = (n : ℕ) - 1 := by
    simp only [Riesz1.cyclicIndexDistance, Fin.val_castSucc, Fin.val_castAdd,
      a, b, Nat.dist, Nat.zero_sub, Nat.sub_zero, zero_add, Nat.succPNat_coe]
    omega
  have he : 1 + (((n : ℕ) - 1 : ℕ) : ℝ) = (n : ℝ) := by
    have he : 1 + ((n : ℕ) - 1) = (n : ℕ) := by have := n.pos; omega
    exact_mod_cast he
  calc
    _ ≤ GoodBlocks.conditionalHessian β s n m a b x := physicalFull_le_hessian β s n m x a b
    _ ≤ _ := by simpa only [hdist, he] using hx.2 a b

/-- See Subsection 5.1 of the paper: the grouped matrix is exactly the actual physical
crossing matrix. This bridges the prefix/suffix algebra to the literal
density-defined conditional Hessian. -/
theorem physicalCrossing_grouped (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    physicalCrossing β s n m x = groupedBoundaryMatrix n
      (physicalPrefix β s n m x) (physicalSuffix β s n m x) (physicalFull β s n m x) := by
  symm
  unfold physicalPrefix physicalSuffix physicalFull physicalGroup
  rw [groupedBoundaryMatrix_sum]
  simp_rw [groupedBoundaryMatrix_sum]
  ext a b
  simp only [Matrix.sum_apply, physicalCrossing]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  by_cases hc : ¬cyclicIndexInterval ((n : ℕ) + m).succPNat i (r.val + 1) ⊆
      activeIndices ((n : ℕ) + m).succPNat n
  · simp only [hc, not_false_eq_true, true_and]
    have hshape := crossing_trace_cases ((n : ℕ) + m).succPNat n hn
      (r := r.val + 1) (by have := r.isLt; simp only [Nat.succPNat_coe]; omega) i hc
    have hnn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ) := by
      simp only [Nat.succPNat_coe]; omega
    have h := trace_group_entry ((n : ℕ) + m).succPNat n hnn _ hshape a b
      (conditionalIntervalWeight β s n m r i x)
    have ha : a.castLE hnn = (a.castAdd m).castSucc := Fin.ext rfl
    have hb : b.castLE hnn = (b.castAdd m).castSucc := Fin.ext rfl
    have haI : (a.castAdd m).castSucc ∈ activeIndices ((n : ℕ) + m).succPNat n := by
      simpa only [activeIndices, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.val_castSucc, Fin.val_castAdd] using a.isLt
    have hbI : (b.castAdd m).castSucc ∈ activeIndices ((n : ℕ) + m).succPNat n := by
      simpa only [activeIndices, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.val_castSucc, Fin.val_castAdd] using b.isLt
    simpa only [ha, hb, Finset.mem_inter, haI, hbI, and_true, Nat.succPNat_coe] using h
  · simp [hc, groupedBoundaryMatrix_apply]

/-- The exact neighboring identity in the proof of Lemma 5.6, now for the physical conditional crossing matrix. -/
theorem physicalCrossing_increment (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (a : Fin (n : ℕ)) (j : Fin ((n : ℕ) - 1)) :
    physicalCrossing β s n m x a ⟨j.val + 1, by omega⟩ -
      physicalCrossing β s n m x a ⟨j.val, by omega⟩ =
        if a.val ≤ j.val then -physicalPrefix β s n m x j else physicalSuffix β s n m x j := by
  rw [physicalCrossing_grouped β s n m hn x]
  exact groupedBoundaryMatrix_increment n _ _ _ a j

/-- The positive-block entry inequality of Lemma 5.6 for the actual conditional crossing matrix. -/
theorem physicalCrossing_entry_sq (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (a b : Fin (n : ℕ)) :
    physicalCrossing β s n m x a b ^ 2 ≤
      physicalCrossing β s n m x a a * physicalCrossing β s n m x b b := by
  rw [physicalCrossing_grouped β s n m hn x]
  exact groupedBoundaryMatrix_entry_sq n _ _ _
    (fun j => physicalGroup_nonneg β s n m x _)
    (fun j => physicalGroup_nonneg β s n m x _)
    (physicalGroup_nonneg β s n m x _) a b

/-- Internal mass calculation in the proof of Lemma 5.6. Removing at most `q` active gaps with
the upper cutoff, when the complement contains at least `q` gaps with the
lower cutoff, gives this uniform complementary-mass ratio. -/
theorem complementary_mass_ratio {n ε q L L' N : ℝ} (hn : 0 < n)
    (hremove : L - L' ≤ q * n ^ ε) (hcomplement : q * n ^ (-ε) ≤ N - L) :
    N - L' ≤ (1 + n ^ (2 * ε)) * (N - L) := by
  have he : n ^ (2 * ε) * n ^ (-ε) = n ^ ε := by
    rw [← Real.rpow_add hn]
    congr 1
    ring
  have hh := mul_le_mul_of_nonneg_left hcomplement (Real.rpow_nonneg hn.le (2 * ε))
  have he' : n ^ (2 * ε) * (q * n ^ (-ε)) = q * n ^ ε := by rw [mul_left_comm, he]
  rw [he'] at hh
  nlinarith

/-- Internal physical shortening comparison in the proof of Lemma 5.6. This retains the exact multiplicities,
so it also applies when shortening leaves an even antipodal length. -/
theorem intervalWeight_shortening (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (r r' : Fin ((N : ℕ) / 2)) (i : Fin (N : ℕ))
    (y : EuclideanSpace ℝ (Fin (N : ℕ))) (hy : WithLp.ofLp y ∈ Riesz1.gapSimplex N)
    (A : ℝ) (hA : 1 ≤ A) (hr : r'.val ≤ r.val)
    (hcomp : (N : ℝ) - cyclicGapSum N i (r'.val + 1) (WithLp.ofLp y) ≤
      A * ((N : ℝ) - cyclicGapSum N i (r.val + 1) (WithLp.ofLp y))) :
    A ^ (-s.val - 2) * intervalWeight s N r i y ≤ 2 * intervalWeight s N r' i y := by
  let L : {L : ℝ // 0 < L ∧ L < (N : ℝ)} :=
    ⟨cyclicGapSum N i (r.val + 1) (WithLp.ofLp y),
      PhysicalEnergy.gapSum_mem N i (by omega)
        (lt_of_le_of_lt (Nat.succ_le_of_lt r.isLt)
          (Nat.div_lt_self N.pos (by norm_num))) _ hy⟩
  let L' : {L : ℝ // 0 < L ∧ L < (N : ℝ)} :=
    ⟨cyclicGapSum N i (r'.val + 1) (WithLp.ofLp y),
      PhysicalEnergy.gapSum_mem N i (by omega)
        (lt_of_le_of_lt (Nat.succ_le_of_lt r'.isLt)
          (Nat.div_lt_self N.pos (by norm_num))) _ hy⟩
  have hshort : L'.val ≤ L.val := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    intro a _ _
    exact (hy.1 _).le
  have h := intervalCoefficient_shortening (ofLong β s) N L L' A hA hshort hcomp
  change A ^ (-s.val - 2) * PhysicalEnergy.intervalCoefficient (ofLong β s) N L ≤
    PhysicalEnergy.intervalCoefficient (ofLong β s) N L' at h
  rw [intervalWeight_physical β s N r i y hy, intervalWeight_physical β s N r' i y hy]
  have hpos : 0 ≤ A ^ (-s.val - 2) * PhysicalEnergy.intervalCoefficient (ofLong β s) N L :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (PhysicalEnergy.intervalCoefficient_pos _ _ _).le
  calc
    _ = (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
      (A ^ (-s.val - 2) * PhysicalEnergy.intervalCoefficient (ofLong β s) N L) := by ring
    _ ≤ 2 * (A ^ (-s.val - 2) * PhysicalEnergy.intervalCoefficient (ofLong β s) N L) := by
      apply mul_le_mul_of_nonneg_right _ hpos
      split_ifs <;> norm_num
    _ ≤ 2 * PhysicalEnergy.intervalCoefficient (ofLong β s) N L' := by linarith
    _ ≤ _ := by
      have hp := (PhysicalEnergy.intervalCoefficient_pos (ofLong β s) N L').le
      split_ifs <;> nlinarith

/-- Internal conditional averaging step of
the proof of Lemma 5.6. A complementary-mass comparison valid
on the physical fibre passes through the actual conditional density. -/
theorem conditionalIntervalWeight_shortening (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (r r' : Fin (((n : ℕ) + m + 1) / 2)) (i : Fin ((n : ℕ) + m + 1))
    (A : ℝ) (hA : 1 ≤ A) (hr : r'.val ≤ r.val)
    (hcomp : ∀ z : EuclideanSpace ℝ (Fin m),
      WithLp.ofLp (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val, z)) ∈
        Riesz1.gapSimplex ((n : ℕ) + m).succPNat →
      ((n : ℝ) + m + 1) - cyclicGapSum ((n : ℕ) + m).succPNat i (r'.val + 1)
        (WithLp.ofLp (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val, z))) ≤
      A * (((n : ℝ) + m + 1) - cyclicGapSum ((n : ℕ) + m).succPNat i (r.val + 1)
        (WithLp.ofLp (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val, z))))) :
    A ^ (-s.val - 2) * conditionalIntervalWeight β s n m r i x ≤
      2 * conditionalIntervalWeight β s n m r' i x := by
  unfold conditionalIntervalWeight
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_mono_ae
    ((integrable_intervalWeight β s n m x r i).const_mul _)
    ((integrable_intervalWeight β s n m x r' i).const_mul _)
  filter_upwards [fibre_simplex β s n m x] with z hz
  apply intervalWeight_shortening β s ((n : ℕ) + m).succPNat r r' i _ hz A hA hr
  simpa only [Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add] using hcomp z hz

/-- The part of the reference Hessian supported on a specified
family of cyclic intervals. The factor two is the Hessian factor in Subsection 5.1.
The even antipodal half-weight and the exact cutoff are retained. -/
def referenceIntervalBlock (s : Riesz1.RieszExponent) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (K : ℕ) (n : ℕ+) (hn : (n : ℕ) ≤ (M : ℕ))
    (family : Finset (Fin (M : ℕ)) → Prop) : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ :=
  fun a b => ∑ i : Fin (M : ℕ),
    ∑ r ∈ (Finset.range ((M : ℕ) / 2 + 1)).filter (fun r => 1 ≤ r ∧ K ≤ r),
      if family (cyclicIndexInterval M i r) then
        2 * ((1 - if 2 * r = (M : ℕ) then (1 / 2 : ℝ) else 0) *
          sampledSecondDifference s M hM ⟨r % (M : ℕ), Nat.mod_lt _ M.pos⟩) *
          (if a.castLE hn ∈ cyclicIndexInterval M i r then 1 else 0) *
          (if b.castLE hn ∈ cyclicIndexInterval M i r then 1 else 0)
      else 0

/-- The actual reference internal block `A^(1)` of Subsection 5.1. -/
def referenceInternal (s : Riesz1.RieszExponent) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (K : ℕ) (n : ℕ+) (hn : (n : ℕ) ≤ (M : ℕ)) : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ :=
  referenceIntervalBlock s M hM K n hn (fun J => J ⊆ activeIndices M n)

/-- The actual reference crossing block `A^(2)` of Subsection 5.1.
Intervals disjoint from the active window contribute zero. -/
def referenceCrossing (s : Riesz1.RieszExponent) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (K : ℕ) (n : ℕ+) (hn : (n : ℕ) ≤ (M : ℕ)) : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ :=
  referenceIntervalBlock s M hM K n hn (fun J => ¬J ⊆ activeIndices M n)

/-- Bridge to the reference object, with its actual normalization.
The internal/crossing split partitions precisely the retained intervals. -/
theorem referenceInternal_add_crossing (s : Riesz1.RieszExponent)
    (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (K : ℕ) (n : ℕ+) (hn : (n : ℕ) ≤ (M : ℕ))
    (a b : Fin (n : ℕ)) :
    referenceInternal s M hM K n hn a b + referenceCrossing s M hM K n hn a b =
      2 * referenceIntervalMatrix s M hM K (a.castLE hn) (b.castLE hn) := by
  unfold referenceInternal referenceCrossing referenceIntervalBlock referenceIntervalMatrix
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro r _
  split_ifs <;> ring

/-- No reference interval crosses the full active cycle. -/
theorem referenceCrossing_full (s : Riesz1.RieszExponent)
    (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (K : ℕ) (hn : (M : ℕ) ≤ (M : ℕ)) :
    referenceCrossing s M hM K M hn = 0 := by
  have hI : activeIndices M M = Finset.univ := by
    ext a
    simp [activeIndices]
  ext a b
  simp [referenceCrossing, referenceIntervalBlock, hI]

/-- See Subsection 5.1 of the paper: the actual difference `P_I^(2) - A^(2)`.
The reference period is explicit. This remainder is defined before
restriction to the good event. -/
def boundaryRemainder (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ :=
  physicalCrossing β s n m x - referenceCrossing s M hM K n hnM

theorem measurable_boundaryRemainder (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (a b : Fin (n : ℕ)) :
    Measurable (fun x => boundaryRemainder β s n m M hM hnM K x a b) :=
  (measurable_physicalCrossing β s n m a b).sub_const _

/-- The single active gap has no endpoint groups. Its physical crossing
entry is exactly its full-intersection coefficient. -/
theorem physicalCrossing_one (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (m : ℕ) (x : AffineSimplex.chartDomain 1 ((1 + m : ℕ) + 1)) :
    physicalCrossing β s 1 m x 0 0 = physicalFull β s 1 m x := by
  have hI : activeIndices (1 + m).succPNat 1 = {(0 : Fin (1 + m + 1))} := by
    ext a
    simp only [activeIndices, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton, Fin.ext_iff, Fin.val_zero]
    omega
  unfold physicalCrossing physicalFull physicalGroup
  simp only [PNat.one_coe] at *
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  have htrace : cyclicIndexInterval (1 + m).succPNat i (r.val + 1) ∩
      activeIndices (1 + m).succPNat 1 = activeIndices (1 + m).succPNat 1 ↔
        (0 : Fin (1 + m + 1)) ∈ cyclicIndexInterval (1 + m).succPNat i (r.val + 1) := by
    rw [hI]
    constructor
    · intro h
      have hz := Finset.mem_inter.mp (h.symm ▸ Finset.mem_singleton_self (0 : Fin (1 + m + 1)))
      exact hz.1
    · exact Finset.inter_singleton_of_mem
  have hz : (Fin.castAdd m (0 : Fin 1)).castSucc = (0 : Fin (1 + m + 1)) := by
    apply Fin.ext
    rfl
  simp only [hz, htrace, and_self]

end Riesz2.BoundaryEntries
