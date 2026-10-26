/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Sanity.FiniteLaws

/-!
# Validity of the finite Riesz model

See Subsection 1.1 of the paper. The long-range case uses the Riesz 1 theorem.
The short-range case uses the normalization and kernel results in
`Riesz2.Sanity.FiniteLaws`. The common partition function uses these normalizers.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz2

/-- The partition function in either actual exponent regime (Subsection 1.1).
Both branches reuse the existing extended normalizer, with the same inverse temperature
and ordered-pair energy. -/
def partitionFunction (p : Parameters) (N : ℕ+) : ℝ≥0∞ :=
  if h : p.val.2 < 1 then
    Riesz1.partitionFunction ⟨p.val, p.property.1, p.property.2.1, h⟩ N
  else shortPartitionFunction ⟨p.val.1, p.property.1⟩
    ⟨p.val.2, lt_of_le_of_ne (le_of_not_gt h) (Ne.symm p.property.2.2)⟩ N

/-- The common normalizer uses exactly the long-range library normalizer. -/
theorem partitionFunction_ofLong (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) :
    partitionFunction (ofLong β s) N = Riesz1.partitionFunction (longParameters β s) N := by
  simp [partitionFunction, ofLong, longParameters, s.property.2]

/-- The common normalizer uses exactly the short-range normalizer. -/
theorem partitionFunction_ofShort (β : InverseTemperature) (s : ShortExponent) (N : ℕ+) :
    partitionFunction (ofShort β s) N = shortPartitionFunction β s N := by
  simp [partitionFunction, ofShort, not_lt.mpr s.property.le]

/-- The short-range energy is nonnegative (Subsection 1.1). -/
theorem shortEnergy_nonneg (s : ShortExponent) {N : ℕ+} (X : Riesz1.Configuration N) :
    0 ≤ shortEnergy s X :=
  FrozenSanity.shortEnergy_nonneg s X

/-- Measurability in short range (Subsection 1.1). -/
theorem measurable_shortEnergy (s : ShortExponent) (N : ℕ+) :
    Measurable (@shortEnergy s N) :=
  FrozenSanity.measurable_shortEnergy s N

/-- Positivity and finiteness in short range (Subsection 1.1). -/
theorem shortPartitionFunction_valid (β : InverseTemperature) (s : ShortExponent) (N : ℕ+) :
    0 < shortPartitionFunction β s N ∧ shortPartitionFunction β s N < ⊤ :=
  FrozenSanity.shortPartitionFunction_valid β s N

/-- Measurability in both exponent regimes (Subsection 1.1). -/
theorem measurable_energy (p : Parameters) (N : ℕ+) : Measurable (@energy p N) := by
  unfold energy
  split_ifs with h
  · exact Riesz1.measurable_energy _ N
  · exact measurable_shortEnergy _ N

/-- The common normalizer is the extended integral in Subsection 1.1.
In particular its meaning is specified before its positivity or finiteness is used. -/
theorem partitionFunction_eq_lintegral (p : Parameters) (N : ℕ+) :
    partitionFunction p N = ∫⁻ X : Riesz1.Configuration N,
      ENNReal.ofReal (Real.exp (-p.val.1 * energy p X)) ∂Riesz1.configurationVolume N := by
  unfold partitionFunction energy
  split_ifs with h
  · exact Riesz1.partitionFunction_eq_lintegral _ N
  · simp [shortPartitionFunction, shortGibbsWeight, withDensity_apply]

/-- See Subsection 1.1 of the paper: on the whole ordered configuration carrier,
the energy is measurable and finite and the partition integral is strictly positive
and finite, for every positive inverse temperature and every positive integer size.
Finiteness of the real-valued energy is also recorded explicitly in extended-real form.
The subtype `Parameters` is exactly `β > 0`, `s > 0`, `s ≠ 1`. -/
theorem finiteModel_valid (p : Parameters) (N : ℕ+) :
    Measurable (@energy p N) ∧
    (∀ X : Riesz1.Configuration N, ENNReal.ofReal |energy p X| < ⊤) ∧
    0 < partitionFunction p N ∧ partitionFunction p N < ⊤ := by
  refine ⟨measurable_energy p N, fun _ => ENNReal.ofReal_lt_top, ?_⟩
  unfold partitionFunction
  split_ifs with h
  · exact ⟨(Riesz1.modelWellDefined ⟨p.val, p.property.1, p.property.2.1, h⟩ N).1,
      (Riesz1.modelWellDefined ⟨p.val, p.property.1, p.property.2.1, h⟩ N).2.1⟩
  · exact shortPartitionFunction_valid _ _ N

/-- Normalization of the law (Subsection 1.1), as a conclusion for every size. -/
theorem shortGibbsMeasure_probability (β : InverseTemperature) (s : ShortExponent) (N : ℕ+) :
    IsProbabilityMeasure (shortGibbsMeasure β s N) :=
  FrozenSanity.shortGibbsMeasure_probability β s N

/-- The law in either regime is a probability (Subsection 1.1). -/
theorem gibbsMeasure_probability (p : Parameters) (N : ℕ+) :
    IsProbabilityMeasure (gibbsMeasure p N) :=
  FrozenSanity.gibbsMeasure_probability p N

/-- The one-particle energy is the empty pair sum, in both regimes (Subsection 1.1). -/
theorem energy_one (p : Parameters) (X : Riesz1.Configuration 1) : energy p X = 0 := by
  classical
  have : Subsingleton (Fin ((1 : ℕ+) : ℕ)) := by change Subsingleton (Fin 1); infer_instance
  have (i : Fin ((1 : ℕ+) : ℕ)) : IsEmpty {j : Fin ((1 : ℕ+) : ℕ) // j ≠ i} :=
    ⟨fun j => j.property (Subsingleton.elim _ _)⟩
  unfold energy
  split_ifs
  · unfold Riesz1.energy
    rw [Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j hj =>
      ((Finset.mem_erase.mp hj).1 (Subsingleton.elim _ _)).elim)), mul_zero]
  · unfold shortEnergy
    rw [Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ =>
      (j.property (Subsingleton.elim _ _)).elim)), mul_zero]

/-- The one-particle normalizer is one (Subsection 1.1). -/
theorem partitionFunction_one (p : Parameters) : partitionFunction p 1 = 1 := by
  rw [partitionFunction_eq_lintegral]
  simp only [energy_one, mul_zero, Real.exp_zero, ENNReal.ofReal_one,
    lintegral_const, one_mul, Riesz1.configurationVolume_univ]
  norm_num

end Riesz2
