/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Sanity.Geometry
public import Riesz1.Rigidity.Gaps
public import Riesz2.Frozen.Energy

/-! # Cumulative gaps and a physical two-particle energy -/

@[expose] public section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
namespace Riesz2.DefinitionSanity

theorem cumulative_gap_identity {N : ℕ+} (X : Riesz1.Configuration N)
    (i j : Fin (N : ℕ)) (hij : i ≤ j) :
    (∑ a ∈ Finset.univ.filter (fun a : Fin (N : ℕ) => i.val ≤ a.val ∧ a.val < j.val),
      gapVector X a) / (N : ℝ) = X.val j - X.val i := by
  have hs : (∑ a ∈ Finset.univ.filter
      (fun a : Fin (N : ℕ) => i.val ≤ a.val ∧ a.val < j.val), gapVector X a) =
      ∑ a ∈ Finset.Ico i.val j.val, Riesz1.gap X (a : ℤ) := by
    rw [Finset.sum_filter]
    change (∑ a : Fin (N : ℕ), if i.val ≤ a.val ∧ a.val < j.val then
      Riesz1.gap X (a.val : ℤ) else 0) = _
    rw [Fin.sum_univ_eq_sum_range (fun a : ℕ =>
      if i.val ≤ a ∧ a < j.val then Riesz1.gap X (a : ℤ) else 0)]
    rw [← Finset.sum_filter]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hs, Finset.sum_Ico_eq_sub _ (Fin.le_iff_val_le_val.mp hij)]
  have hsum (k : Fin (N : ℕ)) :
      (∑ a ∈ Finset.range k.val, Riesz1.gap X (a : ℤ)) =
        (N : ℝ) * (X.val k - X.val 0) := by
    rw [← show (∑ a ∈ Finset.range k.val, Riesz1.gap X ((0 : ℤ) + a)) =
      ∑ a ∈ Finset.range k.val, Riesz1.gap X (a : ℤ) by simp]
    rw [← Riesz1.blockLength_eq_sum, Riesz1.blockLength]
    simp only [zero_add, Riesz1.cyclicLift_natCast]
    rw [show Riesz1.cyclicLift X 0 = X.val 0 from Riesz1.cyclicLift_natCast X 0]
  rw [hsum i, hsum j]
  have hN : (N : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem pair_gap_energy_actual {N : ℕ+} (χ : ParticlePairData N)
    (X : Riesz1.Configuration N) :
    pairAmbientGapPotential χ (WithLp.toLp 2 (gapVector X)) =
      particlePairEnergy χ (WithLp.toLp 2 X.val) := by
  unfold pairAmbientGapPotential particlePairEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  exact congrArg (χ p) (cumulative_gap_identity X p.val.1 p.val.2 p.property.le)

def equispacedTwo : Riesz1.Configuration 2 :=
  ⟨fun i => (i.val : ℝ) / 2, by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i j hij
      exact div_lt_div_of_pos_right (by exact_mod_cast hij) (by norm_num)
    · norm_num
    · norm_num
    · intro i
      dsimp
      norm_num only [zero_div, zero_add]
      have hi : i.val < 2 := i.isLt
      have hi' : (i.val : ℝ) < 2 := by exact_mod_cast hi
      linarith⟩

theorem equispacedTwo_gaps : gapVector equispacedTwo = fun _ => 1 := by
  funext i
  fin_cases i <;> norm_num [gapVector, gap, Riesz1.cyclicLift, equispacedTwo]

theorem physical_energy_two (β : InverseTemperature) (s : Riesz1.RieszExponent) :
    physicalAmbientGapEnergy (ofLong β s) 2
      ⟨WithLp.toLp 2 (gapVector equispacedTwo), by rw [equispacedTwo_gaps]; exact ambient_ones 2 (by norm_num)⟩ =
      energy (ofLong β s) equispacedTwo := by
  have hy : (⟨WithLp.toLp 2 (gapVector equispacedTwo), by
      rw [equispacedTwo_gaps]; exact ambient_ones 2 (by norm_num)⟩ :
      {y : EuclideanSpace ℝ (Fin ((2 : ℕ+) : ℕ)) // y ∈ gapAmbientDomain 2}) =
      ⟨WithLp.toLp 2 (fun _ => 1), ambient_ones 2 (by norm_num)⟩ := by
    apply Subtype.ext
    exact congrArg (WithLp.toLp 2) equispacedTwo_gaps
  rw [hy]
  unfold physicalAmbientGapEnergy
  change (2 : ℝ) ^ (-s.val) * (∑ i : Fin 2, ∑ r : Fin 1,
      (2 - if 2 * (r.val + 1) = 2 then (1 : ℝ) else 0) *
      kernelAtParameters (ofLong β s) (interiorCirclePoint
        ⟨cyclicGapSum 2 i (r.val + 1) (fun _ => 1) / 2, _⟩)) = _
  simp only [Fin.sum_univ_two, Fin.sum_univ_one]
  norm_num only [Fin.val_zero, Nat.cast_one, one_mul, Nat.cast_zero,
    zero_add, ite_true, sub_self, add_zero, Nat.reduceMul, Nat.reduceAdd, sub_zero]
  simp only [kernel_ofLong]
  norm_num [cyclicGapSum]
  unfold energy
  simp only [ofLong, s.property.2, ↓reduceDIte]
  change _ = (2 : ℝ) ^ (-s.val) * (∑ i : Fin 2, ∑ j ∈ Finset.univ.erase i,
    Riesz1.rieszRepresentative s (((i.val : ℝ) / 2 - (j.val : ℝ) / 2 : ℝ) : UnitAddCircle))
  have h0 : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by ext j; fin_cases j <;> simp
  have h1 : (Finset.univ : Finset (Fin 2)).erase 1 = {0} := by ext j; fin_cases j <;> simp
  rw [Fin.sum_univ_two, h0, h1]
  simp only [Finset.sum_singleton, Riesz1.rieszKernel, interiorCirclePoint]
  norm_num
  have he : ((-(1 / 2) : ℝ) : UnitAddCircle) = ((1 / 2 : ℝ) : UnitAddCircle) := by
    rw [show (-(1 / 2) : ℝ) = 1 / 2 - 1 by norm_num, AddCircle.coe_sub]
    norm_num
  left
  simpa only [AddCircle.coe_neg] using congrArg (Riesz1.rieszRepresentative s) he.symm

end Riesz2.DefinitionSanity
