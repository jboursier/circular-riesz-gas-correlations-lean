/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.ConditionalWellPosednessPart2
public import Riesz2.Thermodynamic.FixedLengthDecay
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.MeasurableLIntegral
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Conditional length-averaging errors

Nonnegative conditional integrals retain infinite values. Jensen and Hölder control
their first two moments by unconditional weighted exceptional moments. This is the
measure-theoretic step in the proof of Lemma 6.5.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Riesz2.LengthAveragingFibres.Internal

variable {X : Type*} [MeasurableSpace X]

/-- Jensen for the square, valid also when the second moment is infinite. -/
theorem square_lintegral_le {ν : Measure X} [IsProbabilityMeasure ν]
    {f : X → ℝ≥0∞} (hf : AEMeasurable f ν) :
    (∫⁻ x, f x ∂ν) ^ 2 ≤ ∫⁻ x, f x ^ 2 ∂ν := by
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq ν
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ : (2 : ℝ).HolderConjugate 2) hf
    (aemeasurable_const : AEMeasurable (fun _ : X => (1 : ℝ≥0∞)) ν)
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_one,
    measure_univ, ENNReal.one_rpow] at hh
  have hs := pow_le_pow_left' hh 2
  norm_num only [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] at hs ⊢
  simpa only [ENNReal.rpow_one] using hs

/-- Hölder bounds a restricted second moment by a fourth moment and the
square root of the event probability. No independence is required. -/
theorem restricted_second_moment_le {ν : Measure X}
    {W : X → ℝ≥0∞} (hW : Measurable W) {E : Set X} (hE : MeasurableSet E) :
    (∫⁻ x in E, W x ^ 2 ∂ν) ≤
      (∫⁻ x, W x ^ 4 ∂ν) ^ (1 / 2 : ℝ) * ν E ^ (1 / 2 : ℝ) := by
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq ν
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ : (2 : ℝ).HolderConjugate 2)
    (hW.pow_const 2).aemeasurable
    ((measurable_const.indicator hE).aemeasurable :
      AEMeasurable (E.indicator (fun _ : X => (1 : ℝ≥0∞))) ν)
  have he : (fun x => (W x ^ 2) * E.indicator (fun _ => (1 : ℝ≥0∞)) x) =
      E.indicator (fun x => W x ^ 2) := by
    funext x
    by_cases hx : x ∈ E <;> simp [hx]
  have hp (x : X) : (E.indicator (fun _ : X => (1 : ℝ≥0∞)) x) ^ (2 : ℝ) =
      E.indicator (fun _ : X => (1 : ℝ≥0∞)) x := by
    by_cases hx : x ∈ E <;> simp [hx]
  simpa only [Pi.mul_apply, he, hp, lintegral_indicator hE, lintegral_one,
    Measure.restrict_apply_univ, ENNReal.rpow_two, ← pow_mul,
    show 2 * 2 = 4 from rfl] using hh

/-- The corresponding first-moment Hölder bound. -/
theorem restricted_first_moment_le {ν : Measure X}
    {W : X → ℝ≥0∞} (hW : Measurable W) {E : Set X} (hE : MeasurableSet E) :
    (∫⁻ x in E, W x ∂ν) ≤
      (∫⁻ x, W x ^ 2 ∂ν) ^ (1 / 2 : ℝ) * ν E ^ (1 / 2 : ℝ) := by
  have h := restricted_second_moment_le (ν := ν) (hW.pow_const (1 / 2 : ℝ)) hE
  simp only [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] at h
  norm_num only [Nat.cast_ofNat, one_div, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0),
    ENNReal.rpow_one, show (1 / (2 : ℝ)) * 4 = 2 by norm_num] at h
  simpa only [ENNReal.rpow_two] using h

end Riesz2.LengthAveragingFibres.Internal

namespace Riesz2.LengthAveragingFibres

open AffineSimplex

section PhysicalFibres

variable (p : Parameters) (n m : ℕ) (θ : PhysicalCutoff) (ε : ℝ)

/-- The unnormalized density of the active marginal in Lemma 6.5.
There are `n+1` active gaps and `m+1` exterior gaps. The penalty is precisely
the two-sided penalty at exponent `ε`. The fine tolerance does not enter it. -/
def marginalWeight : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞ :=
  AffineFibre.fibreMass volume
    (ProperMarginalChart.penalizedChartDensity p (n + 1) m (Equiv.refl _) θ
      ((n + 1 : ℝ) ^ (-ε))
      (Finset.univ.image (fun i : Fin (n + 1) => (i.castAdd m).castSucc)) true)

/-- Measurability of the actual marginal density in Lemma 6.5. -/
theorem measurable_marginalWeight : Measurable (marginalWeight p n m θ ε) :=
  AffineFibre.measurable_fibreMass volume
    (ProperMarginalChart.measurable_penalizedChartDensity p (n + 1) m (Equiv.refl _)
      θ (Real.rpow_pos_of_pos (by positivity) _) _ true)

/-- See Lemma 6.5 of the paper: every interior length has a positive finite
normalizer. This assertion includes the point active fibre when `n=0`. -/
theorem fibre_mass (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) :
    (∫⁻ x, marginalWeight p n m θ ε x ∂simplexVolume n L.val) ≠ 0 ∧
      (∫⁻ x, marginalWeight p n m θ ε x ∂simplexVolume n L.val) ≠ ∞ := by
  have h := ConditionalWellPosedness.penalized_marginal_simplex_normalizer
    p n m (Equiv.refl _) L.property.1 L.property.2 θ
    (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < n + 1) (-ε)) Finset.univ true
  exact ⟨h.1.ne', h.2.ne⟩

/-- The explicit length conditional in Lemma 6.5, as a measurable
kernel on the entire open length carrier. No null-fibre choices are made. -/
def fibreKernel : Kernel (Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ))
    (EuclideanSpace ℝ (Fin (n + 1))) where
  toFun L := AffineFibre.normalizedMeasure (simplexVolume n L.val)
    (marginalWeight p n m θ ε) (fibre_mass p n m θ ε L).1 (fibre_mass p n m θ ε L).2
  measurable' := Measure.measurable_of_measurable_coe _ fun E hE => by
    have h := AffineFibre.SumChart.measurable_simplex_conditional_lintegral
      n (Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) (measurable_marginalWeight p n m θ ε)
      (fun L => (fibre_mass p n m θ ε L).1)
      (fun L => (fibre_mass p n m θ ε L).2)
      (measurable_const.indicator hE : Measurable (E.indicator (fun _ => (1 : ℝ≥0∞))))
    simpa only [lintegral_indicator hE, lintegral_one, Measure.restrict_apply_univ] using h

instance fibreKernel_markov : IsMarkovKernel (fibreKernel p n m θ ε) where
  isProbabilityMeasure _ := AffineFibre.isProbabilityMeasure_normalizedMeasure _
    (measurable_marginalWeight p n m θ ε) _ _

/-- See Lemma 6.5 of the paper: all the mass of a length conditional lies on its
literal mass hyperplane. The statement holds at every interior length. -/
theorem sum_eq_ae_fibre (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) :
    ∀ᵐ x ∂fibreKernel p n m θ ε L, ∑ i, x i = L.val := by
  exact (withDensity_absolutelyContinuous _ _)
    (AffineFibre.SumChart.sum_eq_ae_simplexVolume n L.val)

/-- See Subsection 6.3 of the paper: the exceptional remainder for a specified weight
and fine good set, evaluated by the explicit physical fibre integral. -/
def exceptionalMass (W : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞)
    (G : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) : ℝ≥0∞ :=
  ∫⁻ x in Gᶜ, W x ∂fibreKernel p n m θ ε L

/-- Boundary check for Subsection 6.3: there is no exceptional mass when the
good set is the whole carrier, even for an infinite envelope. -/
theorem exceptionalMass_univ (W : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞)
    (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) :
    exceptionalMass p n m θ ε W univ L = 0 := by
  simp [exceptionalMass]

/-- Boundary check for Subsection 6.3: unit weight on the full exceptional
event has mass one at every interior length. -/
theorem exceptionalMass_empty_one (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) :
    exceptionalMass p n m θ ε (fun _ => 1) ∅ L = 1 := by
  have hκ := (fibreKernel_markov p n m θ ε).isProbabilityMeasure L
  simp only [exceptionalMass, compl_empty, Measure.restrict_univ, lintegral_one, hκ.measure_univ]

/-- See Subsection 6.3 of the paper: measurability of conditional exceptional mass
follows before any finiteness estimate. -/
theorem measurable_exceptionalMass
    {W : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞} (hW : Measurable W)
    {G : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hG : MeasurableSet G) :
    Measurable (exceptionalMass p n m θ ε W G) := by
  have h := ((hW.indicator hG.compl).comp measurable_snd).lintegral_kernel_prod_right'
    (κ := fibreKernel p n m θ ε)
  change Measurable (fun L => ∫⁻ x in Gᶜ, W x ∂fibreKernel p n m θ ε L)
  simpa only [Function.comp_def, lintegral_indicator hG.compl] using h

/-- See Lemma 6.5 of the paper: coarea disintegration with the exact Jacobian.
The density here is unnormalized, just as `marginalWeight` is. -/
theorem coarea_disintegration
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in {x | (∑ i, x i) ∈ Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)} ∩
        {x | ∀ i, 0 < x i}, marginalWeight p n m θ ε x * f x =
      (ENNReal.ofReal (Real.sqrt (n + 1)))⁻¹ *
        ∫⁻ L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ),
          (∫⁻ x, marginalWeight p n m θ ε x ∂simplexVolume n L.val) *
            (∫⁻ x, f x ∂fibreKernel p n m θ ε L)
          ∂volume.comap ((↑) : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ) → ℝ) :=
  AffineFibre.SumChart.lintegral_simplex_disintegration n measurableSet_Ioo
    (measurable_marginalWeight p n m θ ε)
    (fun L => (fibre_mass p n m θ ε L).1)
    (fun L => (fibre_mass p n m θ ε L).2) hf

/-- Normalization factor for the active marginal, including the existing
particle-to-gap chart Jacobian. See Lemma 6.5. -/
def marginalScale : ℝ≥0∞ :=
  (tiltNormalizer p ((n + 1) + m).succPNat (⟨n + 1, Nat.succ_pos n⟩ : ℕ+) (by simp; omega) θ ε true)⁻¹ *
    (partitionFunction p ((n + 1) + m).succPNat)⁻¹ *
      ENNReal.ofReal (((n + 1 : ℝ) + m + 1) ^ ((n + 1) + m))⁻¹

/-- The active law at the `n+1` active-gap parameterization. See Lemma 6.5. The target type fixes the ambient measurable space. -/
def activeMeasure : Measure (EuclideanSpace ℝ (Fin (n + 1))) :=
  activeTiltedGapLaw p ((n + 1) + m).succPNat (⟨n + 1, Nat.succ_pos n⟩ : ℕ+)
    (by simp; omega) θ ε true

/-- The density used for length averaging is the active law. -/
theorem active_law_density :
    activeMeasure p n m θ ε =
      marginalScale p n m θ ε • volume.withDensity (marginalWeight p n m θ ε) := by
  classical
  have h := ProperMarginalChart.activeTiltedGapLaw_density p (⟨n + 1, by omega⟩ : ℕ+) m
    (by simp; omega) θ ε true
  have hJ : Finset.univ.map (Fin.castLEEmb (show n + 1 ≤
      (((n + 1) + m).succPNat : ℕ) by simp; omega)) =
      Finset.univ.image (fun i : Fin (n + 1) => (i.castAdd m).castSucc) := by
    rw [Finset.map_eq_image]
    congr 1
  change activeTiltedGapLaw p ((n + 1) + m).succPNat (⟨n + 1, Nat.succ_pos n⟩ : ℕ+) _ θ ε true = _ at h
  simpa only [PNat.mk_coe, Nat.cast_add, Nat.cast_one, smul_smul, mul_assoc,
    marginalScale, marginalWeight, activeMeasure, hJ] using h

/-- Both original normalizers and the chart Jacobian are finite and nonzero. See Lemma 6.5. -/
theorem marginalScale_valid :
    marginalScale p n m θ ε ≠ 0 ∧ marginalScale p n m θ ε ≠ ∞ := by
  have ht := ProperMarginalChart.activeTiltedGapLaw_density_valid p
    (⟨n + 1, Nat.succ_pos n⟩ : ℕ+) m (by simp; omega) θ ε true
  have hz := (finiteModel_valid p ((n + 1) + m).succPNat).2.2
  have hj : (0 : ℝ) < ((n + 1 : ℝ) + m + 1) ^ ((n + 1) + m) := by positivity
  exact ⟨mul_ne_zero (mul_ne_zero (ENNReal.inv_ne_zero.mpr ht.2.1.ne)
    (ENNReal.inv_ne_zero.mpr hz.2.ne)) (ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr hj)),
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr ht.1.ne')
      (ENNReal.inv_ne_top.mpr hz.1.ne'))
      ENNReal.ofReal_ne_top⟩

/-- The coarea density of the normalized active length, on its full open
carrier. See Lemma 6.5. -/
def lengthDensity (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) : ℝ≥0∞ :=
  marginalScale p n m θ ε * (ENNReal.ofReal (Real.sqrt (n + 1)))⁻¹ *
    ∫⁻ x, marginalWeight p n m θ ε x ∂simplexVolume n L.val

/-- See Lemma 6.5 of the paper: the coarea length density is measurable. -/
theorem measurable_lengthDensity : Measurable (lengthDensity p n m θ ε) :=
  measurable_const.mul ((AffineFibre.SumChart.measurable_simplex_lintegral n
    (measurable_marginalWeight p n m θ ε)).comp measurable_subtype_coe)

/-- See Lemma 6.5 of the paper: the normalized density is positive and finite
at every interior length, rather than just almost everywhere. -/
theorem lengthDensity_valid (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) :
    lengthDensity p n m θ ε L ≠ 0 ∧ lengthDensity p n m θ ε L ≠ ∞ := by
  have hc := marginalScale_valid p n m θ ε
  have hz := fibre_mass p n m θ ε L
  have hs : ENNReal.ofReal (Real.sqrt (n + 1)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Real.sqrt_pos.mpr (by positivity))
  exact ⟨mul_ne_zero (mul_ne_zero hc.1 (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)) hz.1,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hc.2 (ENNReal.inv_ne_top.mpr hs)) hz.2⟩

/-- The explicitly normalized coarea length measure. See Lemma 6.5.
Its identification with the sum image is established by disintegration below. -/
def lengthMeasure : Measure (Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) :=
  (volume.comap ((↑) : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ) → ℝ)).withDensity
    (lengthDensity p n m θ ε)

/-- The actual marginal density vanishes off its open active domain. This
uses the existing supported chart density, and never extends the energy. -/
theorem marginalWeight_eq_zero {x : EuclideanSpace ℝ (Fin (n + 1))}
    (hx : x ∉ chartDomain (n + 1) ((n + 1 + m : ℕ) + 1)) :
    marginalWeight p n m θ ε x = 0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  apply Filter.Eventually.of_forall
  intro z
  have hnot : (x, z) ∉ RetainedSimplex.domain (n + 1) m ((n + 1 + m : ℕ) + 1) := by
    intro h
    apply hx
    rw [← RetainedSimplex.fst_image_domain (n + 1) m ((n + 1 + m : ℕ) + 1)]
    exact ⟨(x, z), h, rfl⟩
  exact indicator_of_notMem hnot _

/-- See Lemma 6.5 of the paper: disintegration of the active marginal
against its explicit length measure and every-point fibre kernel. -/
theorem lintegral_disintegration
    {f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f x ∂activeMeasure p n m θ ε) =
      ∫⁻ L, ∫⁻ x, f x ∂fibreKernel p n m θ ε L ∂lengthMeasure p n m θ ε := by
  have hco := coarea_disintegration p n m θ ε hf
  have hdom : {x : EuclideanSpace ℝ (Fin (n + 1)) |
      (∑ i, x i) ∈ Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)} ∩
      {x | ∀ i, 0 < x i} = chartDomain (n + 1) ((n + 1 + m : ℕ) + 1) := by
    ext x
    constructor
    · intro h
      exact ⟨h.2, h.1.2⟩
    · intro h
      exact ⟨⟨Finset.sum_pos (fun i _ => h.1 i) Finset.univ_nonempty, h.2⟩, h.1⟩
  rw [hdom] at hco
  have hsupport : (chartDomain (n + 1) ((n + 1 + m : ℕ) + 1)).indicator
      (fun x => marginalWeight p n m θ ε x * f x) =
      fun x => marginalWeight p n m θ ε x * f x := by
    funext x
    by_cases hx : x ∈ chartDomain (n + 1) ((n + 1 + m : ℕ) + 1)
    · exact indicator_of_mem hx _
    · simp [marginalWeight_eq_zero p n m θ ε hx]
  rw [← lintegral_indicator (isOpen_chartDomain _ _).measurableSet, hsupport] at hco
  have hcond : Measurable (fun L => ∫⁻ x, f x ∂fibreKernel p n m θ ε L) :=
    AffineFibre.SumChart.measurable_simplex_conditional_lintegral n
    (Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) (measurable_marginalWeight p n m θ ε)
    (fun L => (fibre_mass p n m θ ε L).1)
    (fun L => (fibre_mass p n m θ ε L).2) hf
  have hd := congrArg (fun ν : Measure (EuclideanSpace ℝ (Fin (n + 1))) => ∫⁻ x, f x ∂ν)
    (active_law_density p n m θ ε)
  rw [lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_marginalWeight p n m θ ε) hf] at hd
  calc
    _ = marginalScale p n m θ ε * ∫⁻ x, marginalWeight p n m θ ε x * f x := hd
    _ = _ := by
      rw [hco,
    lengthMeasure, lintegral_withDensity_eq_lintegral_mul _
      (measurable_lengthDensity p n m θ ε) hcond]
      simp only [lengthDensity, mul_assoc, Pi.mul_apply]
      have hm := ((AffineFibre.SumChart.measurable_simplex_lintegral n
        (measurable_marginalWeight p n m θ ε)).comp measurable_subtype_coe).mul hcond
      simpa only [Pi.mul_apply, Function.comp_def, mul_assoc] using
        (lintegral_const_mul (marginalScale p n m θ ε *
          (ENNReal.ofReal (Real.sqrt (n + 1)))⁻¹) hm).symm

/-- The explicit coarea length measure is a probability. See Lemma 6.5. -/
theorem lengthMeasure_probability : IsProbabilityMeasure (lengthMeasure p n m θ ε) := by
  have hprob := (ProperMarginalChart.activeTiltedGapLaw_density_valid p (⟨n + 1, Nat.succ_pos n⟩ : ℕ+) m
    (by simp; omega) θ ε true).2.2.1
  have hnorm : (activeMeasure p n m θ ε) Set.univ = 1 := hprob.measure_univ
  constructor
  have h := lintegral_disintegration p n m θ ε (measurable_const (a := (1 : ℝ≥0∞)))
  have hκ (L) : (fibreKernel p n m θ ε L) Set.univ = 1 :=
    ((fibreKernel_markov p n m θ ε).isProbabilityMeasure L).measure_univ
  simpa only [lintegral_one, hκ, hnorm] using h.symm

/-- See Lemma 6.5 of the paper: the explicit coarea length law is the sum image
of the active marginal. -/
theorem lengthMeasure_map :
    (lengthMeasure p n m θ ε).map ((↑) : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ) → ℝ) =
      (activeMeasure p n m θ ε).map (fun x => ∑ i, x i) := by
  have hm : Measurable (fun x : EuclideanSpace ℝ (Fin (n + 1)) => ∑ i, x i) :=
    (continuous_finsetSum _ (fun i _ => PiLp.continuous_apply 2 _ i)).measurable
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf measurable_subtype_coe, lintegral_map hf hm,
    lintegral_disintegration p n m θ ε (f := fun x => f (∑ i, x i)) (hf.comp hm)]
  apply lintegral_congr
  intro L
  have hκ := (fibreKernel_markov p n m θ ε).isProbabilityMeasure L
  have h := lintegral_congr_ae ((sum_eq_ae_fibre p n m θ ε L).mono
    (fun x hx => congrArg f hx))
  simpa only [lintegral_const, hκ.measure_univ, mul_one] using h.symm

/-- See the proof of Lemma 6.5 in the paper, first exceptional moment:
the conditional mass integrates to the actual weighted bad-event mass. -/
theorem exceptional_first_moment
    {W : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞} (hW : Measurable W)
    {G : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hG : MeasurableSet G) :
    (∫⁻ L, exceptionalMass p n m θ ε W G L ∂lengthMeasure p n m θ ε) =
      ∫⁻ x in Gᶜ, W x ∂activeMeasure p n m θ ε := by
  have h := lintegral_disintegration p n m θ ε (hW.indicator hG.compl)
  simpa only [exceptionalMass, lintegral_indicator hG.compl] using h.symm

/-- See the proof of Lemma 6.5 in the paper, conditional Jensen for the
exceptional square. The exceptional set remains inside the integral. -/
theorem exceptional_second_moment_le
    {W : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞} (hW : Measurable W)
    {G : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hG : MeasurableSet G) :
    (∫⁻ L, exceptionalMass p n m θ ε W G L ^ 2 ∂lengthMeasure p n m θ ε) ≤
      ∫⁻ x in Gᶜ, W x ^ 2 ∂activeMeasure p n m θ ε := by
  rw [← lintegral_indicator hG.compl,
    lintegral_disintegration p n m θ ε ((hW.pow_const 2).indicator hG.compl)]
  apply lintegral_mono
  intro L
  have h := Internal.square_lintegral_le
    ((hW.indicator hG.compl).aemeasurable :
      AEMeasurable (Gᶜ.indicator W) (fibreKernel p n m θ ε L))
  have he : (fun x => Gᶜ.indicator W x ^ 2) = Gᶜ.indicator (fun x => W x ^ 2) := by
    funext x
    by_cases hx : x ∈ Gᶜ <;> simp [hx]
  rw [he, lintegral_indicator hG.compl, lintegral_indicator hG.compl] at h
  simpa only [exceptionalMass, lintegral_indicator hG.compl] using h

/-- See the proof of Lemma 6.5 in the paper: Jensen followed by Hölder
for the actual marginal and its explicit coarea length law. -/
theorem exceptional_second_moment_le_fourth
    {W : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞} (hW : Measurable W)
    {G : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hG : MeasurableSet G) :
    (∫⁻ L, exceptionalMass p n m θ ε W G L ^ 2 ∂lengthMeasure p n m θ ε) ≤
      (∫⁻ x, W x ^ 4 ∂activeMeasure p n m θ ε) ^ (1 / 2 : ℝ) *
      (activeMeasure p n m θ ε) Gᶜ ^ (1 / 2 : ℝ) :=
  (exceptional_second_moment_le p n m θ ε hW hG).trans
    (Internal.restricted_second_moment_le hW hG.compl)

/-- See the proof of Lemma 6.5 in the paper: the complete first-plus-second
moment expression, before inserting the coefficient moment and event bounds.
It uses the actual marginal, and is valid even for infinite moments. -/
theorem exceptional_moments_le
    {W : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞} (hW : Measurable W)
    {G : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hG : MeasurableSet G) :
    (∫⁻ L, exceptionalMass p n m θ ε W G L + exceptionalMass p n m θ ε W G L ^ 2
      ∂lengthMeasure p n m θ ε) ≤
      ((∫⁻ x, W x ^ 2 ∂activeMeasure p n m θ ε) ^ (1 / 2 : ℝ) +
        (∫⁻ x, W x ^ 4 ∂activeMeasure p n m θ ε) ^ (1 / 2 : ℝ)) *
        (activeMeasure p n m θ ε) Gᶜ ^ (1 / 2 : ℝ) := by
  rw [lintegral_add_left (measurable_exceptionalMass p n m θ ε hW hG),
    exceptional_first_moment p n m θ ε hW hG, add_mul]
  exact add_le_add (Internal.restricted_first_moment_le hW hG.compl)
    (exceptional_second_moment_le_fourth p n m θ ε hW hG)

/-- See the proof of Lemma 6.5 in the paper: quantitative use of the second
and fourth moments and the full-law exceptional probability. These moment and probability estimates are hypotheses. -/
theorem exceptional_moments_bound_internal
    {W : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞} (hW : Measurable W)
    {G : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hG : MeasurableSet G)
    (A₂ A₄ R : ℝ≥0∞)
    (h₂ : (∫⁻ x, W x ^ 2 ∂activeMeasure p n m θ ε) ≤ A₂ ^ 2)
    (h₄ : (∫⁻ x, W x ^ 4 ∂activeMeasure p n m θ ε) ≤ A₄ ^ 2)
    (hprob : (activeMeasure p n m θ ε) Gᶜ ≤ R) :
    (∫⁻ L, exceptionalMass p n m θ ε W G L + exceptionalMass p n m θ ε W G L ^ 2
      ∂lengthMeasure p n m θ ε) ≤ (A₂ + A₄) * R ^ (1 / 2 : ℝ) := by
  apply (exceptional_moments_le p n m θ ε hW hG).trans
  have hs (A : ℝ≥0∞) : (A ^ 2) ^ (1 / 2 : ℝ) = A := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  exact mul_le_mul
    (add_le_add ((ENNReal.rpow_le_rpow h₂ (by norm_num)).trans_eq (hs A₂))
      ((ENNReal.rpow_le_rpow h₄ (by norm_num)).trans_eq (hs A₄)))
    (ENNReal.rpow_le_rpow hprob (by norm_num)) (by positivity) (by positivity)

/-- See the proof of Lemma 6.5 in the paper: turn polynomial moment bounds
and a stretched-exponential event bound into the explicit conditional-error
bound. The stretched power `δ` is unchanged. The moment and event bounds are hypotheses. -/
theorem exceptional_moments_exponential_internal
    {W : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞} (hW : Measurable W)
    {G : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hG : MeasurableSet G)
    (M₂ M₄ D c δ a : ℝ) (hM₂ : 0 ≤ M₂) (hM₄ : 0 ≤ M₄) (hD : 0 ≤ D)
    (h₂ : (∫⁻ x, W x ^ 2 ∂activeMeasure p n m θ ε) ≤
      (ENNReal.ofReal (M₂ * (n + 1 : ℝ) ^ a)) ^ 2)
    (h₄ : (∫⁻ x, W x ^ 4 ∂activeMeasure p n m θ ε) ≤
      (ENNReal.ofReal (M₄ * (n + 1 : ℝ) ^ a)) ^ 2)
    (hprob : (activeMeasure p n m θ ε) Gᶜ ≤
      ENNReal.ofReal (D * Real.exp (-c * (n + 1 : ℝ) ^ δ))) :
    (∫⁻ L, exceptionalMass p n m θ ε W G L + exceptionalMass p n m θ ε W G L ^ 2
      ∂lengthMeasure p n m θ ε) ≤
      ENNReal.ofReal ((M₂ + M₄) * Real.sqrt D * (n + 1 : ℝ) ^ a *
        Real.exp (-(c / 2) * (n + 1 : ℝ) ^ δ)) := by
  have h := exceptional_moments_bound_internal p n m θ ε hW hG
    (ENNReal.ofReal (M₂ * (n + 1 : ℝ) ^ a))
    (ENNReal.ofReal (M₄ * (n + 1 : ℝ) ^ a))
    (ENNReal.ofReal (D * Real.exp (-c * (n + 1 : ℝ) ^ δ))) h₂ h₄ hprob
  apply h.trans_eq
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ← ENNReal.ofReal_mul (by positivity), Real.mul_rpow hD (Real.exp_pos _).le,
    ← Real.exp_mul, ← Real.sqrt_eq_rpow]
  congr 1
  rw [show (-c * (n + 1 : ℝ) ^ δ) * (1 / 2) =
    -(c / 2) * (n + 1 : ℝ) ^ δ by ring]
  ring

/-- Finite weighted bad-event second moment implies a finite conditional
remainder almost everywhere. In particular `toReal` may subsequently be used
only on this a.e. carrier. The proof of Lemma 6.5. -/
theorem exceptional_finite_ae_internal
    {W : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞} (hW : Measurable W)
    {G : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hG : MeasurableSet G)
    (hfinite : (∫⁻ x in Gᶜ, W x ^ 2 ∂activeMeasure p n m θ ε) < ∞) :
    ∀ᵐ L ∂lengthMeasure p n m θ ε, exceptionalMass p n m θ ε W G L < ∞ := by
  have hlt := (exceptional_second_moment_le p n m θ ε hW hG).trans_lt hfinite
  have h := ae_lt_top ((measurable_exceptionalMass p n m θ ε hW hG).pow_const 2) hlt.ne
  filter_upwards [h] with L hL
  by_contra! htop
  have he : exceptionalMass p n m θ ε W G L = ∞ := top_unique htop
  simp [he] at hL

end PhysicalFibres

section ConditionalSums

variable {H : Type*} [NormedAddCommGroup H]

/-- See the proof of Lemma 6.5 in the paper: transfer the two auxiliary
sums through a conditional comparison, retaining the power of the conditional
exceptional error. -/
theorem conditional_sums_internal (n : ℕ+) (w : Fin (n : ℕ) → ℝ)
    (hw : ∀ j, 0 ≤ w j) (q W A D E F B e P : ℝ)
    (hW : 0 ≤ W)
    (ψ v : Fin (n : ℕ) → H)
    (hweights : (∑ j, w j ^ 2) ≤ W * (n : ℝ) ^ (1 - 2 * q))
    (hweighted : (∑ j, w j * ‖v j‖) ≤ A * (n : ℝ) ^ (-q) * F)
    (hsum : (∑ j, ‖v j‖) ≤ D * F)
    (hcomparison : ‖WithLp.toLp 2 (fun j => ψ j - v j)‖ ≤
      E * (n : ℝ) ^ (-(1 : ℝ) / 2) * F + (n : ℝ) ^ (-P) * B * Real.sqrt e) :
    (∑ j, w j * ‖ψ j‖) ≤
      (A + Real.sqrt W * E) * (n : ℝ) ^ (-q) * F +
        Real.sqrt W * (n : ℝ) ^ (1 / 2 - q - P) * B * Real.sqrt e ∧
    (∑ j, ‖ψ j‖) ≤ (D + E) * F +
      (n : ℝ) ^ (1 / 2 - P) * B * Real.sqrt e := by
  have hn : (0 : ℝ) < n := by positivity
  have hp (a b : ℝ) : (n : ℝ) ^ a * (n : ℝ) ^ b = (n : ℝ) ^ (a + b) :=
    (Real.rpow_add hn a b).symm
  have hroot : Real.sqrt (∑ j, w j ^ 2) ≤
      Real.sqrt W * (n : ℝ) ^ (1 / 2 - q) := by
    apply (Real.sqrt_le_sqrt hweights).trans_eq
    rw [Real.sqrt_mul hW]
    simp_rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_mul hn.le]
    congr 2
    ring
  have herror : 0 ≤ E * (n : ℝ) ^ (-(1 : ℝ) / 2) * F +
      (n : ℝ) ^ (-P) * B * Real.sqrt e :=
    (norm_nonneg _).trans hcomparison
  constructor
  · have hh := FixedLengthDecay.weighted_sum_norm_transfer_internal w hw ψ v _ _
      hweighted hcomparison
    apply hh.trans
    apply (add_le_add_right (mul_le_mul_of_nonneg_right hroot herror) _).trans_eq
    rw [mul_add]
    have he₁ : (1 / 2 - q) + (-(1 : ℝ) / 2) = -q := by ring
    have he₂ : (1 / 2 - q) + -P = 1 / 2 - q - P := by ring
    calc
      _ = A * (n : ℝ) ^ (-q) * F +
          Real.sqrt W * E * ((n : ℝ) ^ (1 / 2 - q) * (n : ℝ) ^ (-(1 : ℝ) / 2)) * F +
          Real.sqrt W * ((n : ℝ) ^ (1 / 2 - q) * (n : ℝ) ^ (-P)) * B * Real.sqrt e := by ring
      _ = _ := by rw [hp, hp, he₁, he₂]; ring
  · have hh := FixedLengthDecay.weighted_sum_norm_transfer_internal
      (fun _ : Fin (n : ℕ) => 1) (fun _ => zero_le_one) ψ v _ _
      (by simpa only [one_mul] using hsum) hcomparison
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at hh
    apply hh.trans_eq
    rw [Real.sqrt_eq_rpow, mul_add]
    have he₁ : (1 / (2 : ℝ)) + (-(1 : ℝ) / 2) = 0 := by ring
    have he₂ : (1 / (2 : ℝ)) + -P = 1 / 2 - P := by ring
    calc
      _ = D * F + E * ((n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-(1 : ℝ) / 2)) * F +
          ((n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (-P)) * B * Real.sqrt e := by ring
      _ = _ := by rw [hp, hp, he₁, he₂, Real.rpow_zero]; ring

/-- See the proof of Lemma 6.5 in the paper: choosing the envelope exponent
once absorbs the conditional exceptional powers in both sums. No polynomial
is absorbed into an already fixed conditional remainder. -/
theorem conditional_sums_absorption_internal (n : ℕ+)
    (q P C A D B e x y : ℝ) (hq : 0 ≤ q) (hP : 1 / 2 ≤ P)
    (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hx : x ≤ A + C * (n : ℝ) ^ (1 / 2 - q - P) * B * Real.sqrt e)
    (hy : y ≤ D + (n : ℝ) ^ (1 / 2 - P) * B * Real.sqrt e) :
    x ≤ A + C * B * Real.sqrt e ∧ y ≤ D + B * Real.sqrt e := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hp₁ : (n : ℝ) ^ (1 / 2 - q - P) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn (by linarith)
  have hp₂ : (n : ℝ) ^ (1 / 2 - P) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn (by linarith)
  constructor
  · apply hx.trans
    exact add_le_add_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_left hp₁ hC).trans_eq (mul_one C)) hB)
        (Real.sqrt_nonneg e)) A
  · apply hy.trans
    exact add_le_add_right (mul_le_mul_of_nonneg_right
      ((mul_le_mul_of_nonneg_right hp₂ hB).trans_eq (one_mul B)) (Real.sqrt_nonneg e)) D

end ConditionalSums

section Multiplier

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} [IsFiniteMeasure ν]

/-- See the proof of Lemma 6.5 in the paper: the globally integrable normal
equation for the multiplier. Integrability of its matrix
pairings is an explicit internal premise. It is not inferred from the local
distributional multiplier statement. This fixes the sign of the source term. -/
theorem multiplier_mean_internal (N : ℕ+) (Q : ScalarFormData ν)
    (M : X → Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (v : Fin (N : ℕ) → Lp ℝ 2 ν) (u : Fin (N : ℕ) → Q.1)
    (hpair : ∀ i j, Integrable (fun x => M x i j * (u j).val x) ν) :
    Integrable (gapMultiplierField N Q M v u) ν ∧
      (∫ x, gapMultiplierField N Q M v u x ∂ν) =
        (N : ℝ)⁻¹ * ((∑ i, ∑ j, ∫ x, M x i j * (u j).val x ∂ν) -
          ∑ i, ∫ x, v i x ∂ν) := by
  have hv (i) : Integrable (fun x => v i x) ν :=
    (Lp.memLp (v i)).integrable (by norm_num)
  have hp (i) : Integrable (fun x => ∑ j, M x i j * (u j).val x) ν :=
    integrable_finsetSum _ (fun j _ => hpair i j)
  have hP := integrable_finsetSum Finset.univ (fun i _ => hp i)
  have hV := integrable_finsetSum Finset.univ (fun i _ => hv i)
  refine ⟨(hP.sub hV).const_mul (N : ℝ)⁻¹, ?_⟩
  simp only [gapMultiplierField]
  rw [integral_const_mul, integral_sub hP hV,
    integral_finsetSum _ (fun i _ => hp i), integral_finsetSum _ (fun i _ => hv i)]
  simp_rw [integral_finsetSum _ (fun j _ => hpair _ j)]

/-- See the proof of Lemma 6.5 in the paper: summing Hessian columns gives
the normal bound from the weighted and unweighted coordinate profiles. This
finite algebraic implication retains both column coefficients separately. -/
theorem normal_column_bound_internal (N : ℕ+)
    (M : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (u w : Fin (N : ℕ) → ℝ) (χ A D : ℝ)
    (hcol : ∀ j, (∑ i, |M i j|) ≤ A + D * w j) :
    |(N : ℝ)⁻¹ * ((∑ i, ∑ j, M i j * u j) - χ)| ≤
      (N : ℝ)⁻¹ * (A * (∑ j, |u j|) + D * (∑ j, w j * |u j|) + |χ|) := by
  have hsum : |∑ i, ∑ j, M i j * u j| ≤
      A * (∑ j, |u j|) + D * (∑ j, w j * |u j|) := by
    calc
      _ ≤ ∑ i, ∑ j, |M i j| * |u j| := by
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro i _
        simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun j => M i j * u j) Finset.univ
      _ = ∑ j, (∑ i, |M i j|) * |u j| := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
      _ ≤ ∑ j, (A + D * w j) * |u j| :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hcol j) (abs_nonneg _))
      _ = _ := by simp only [add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (N : ℝ)⁻¹)]
  exact mul_le_mul_of_nonneg_left
    ((abs_sub _ _).trans (add_le_add_left hsum _)) (by positivity)

end Multiplier

end Riesz2.LengthAveragingFibres
