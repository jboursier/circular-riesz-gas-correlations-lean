/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.LengthAveragingFibres
public import Riesz2.Thermodynamic.InterpolationMatrixPart2
public import Riesz2.Thermodynamic.InterpolantLocalLawsPart4
public import Riesz2.DecayLong.ConditionalForcesPart2
public import Riesz2.DecayShort.ExceptionalEventPart3
import all Riesz2.DecayShort.ExceptionalEventPart4

/-!
# Physical envelopes for conditional length errors

See Subsection 6.3 of the paper. Coefficients are evaluated on their positive retained
carrier, using the conditional coefficients and the literal two-sided penalty Hessian.
The penalty exponent and fine-event tolerance are independent parameters. No extension
of a coefficient outside its carrier is selected.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators Classical

namespace Riesz2.LengthAveragingFibres

/-- See Subsection 6.3 of the paper: the long-range envelope on its full retained carrier.
The exponent `C₀` is selected only after the comparison losses are known. -/
def longEnvelope (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε C₀ : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) : ℝ :=
  (n : ℝ) ^ C₀ * (1 +
    (∑ i, |InterpolationMatrix.penaltyHessian n θ ε x.val i i|) +
    (∑ i, ∑ j, GoodBlocks.conditionalHessian β s n m i j x) +
    (∑ i, ConditionalForces.compensationB β s n m i x) +
    ConditionalForces.compensationC β s n m x)

/-- See Subsection 6.3 of the paper: the short-range envelope. The conditional interval
matrix and its exterior contractions are precisely those in Subsection 4.5. The exterior set and all averaging factors are retained explicitly. -/
def shortEnvelope (p : Parameters) (n : ℕ+) (m : ℕ)
    (θ : PhysicalCutoff) (ε C₀ : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) : ℝ :=
  let hn : (n : ℕ) ≤ (n : ℕ) + m + 1 := by omega
  let A := DecayShort.conditionalIntervalWeight p n m n.pos (Equiv.refl _) x
  let H := IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat
    ((n : ℕ) + m + 1) le_rfl A
  let S := Finset.univ.filter (fun a : Fin ((n : ℕ) + m + 1) => (n : ℕ) ≤ a.val)
  (n : ℝ) ^ C₀ * (1 +
    (∑ i, |InterpolationMatrix.penaltyHessian n θ ε x.val i i|) +
    (∑ i : Fin (n : ℕ), ∑ j : Fin (n : ℕ),
      IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat n hn A i j) +
    (∑ i : Fin (n : ℕ), (m + 1 : ℝ)⁻¹ * ∑ a ∈ S, H (Fin.castLE hn i) a) +
    (m + 1 : ℝ)⁻¹ ^ 2 * ∑ a ∈ S, ∑ b ∈ S, H a b)

/-- See Subsection 6.3 of the paper: the complete long-range fine event, including
both compensation conditions. The finite universal conditions bound the compensation maxima. The last cut never wraps. -/
def longFineEvent (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (η κ : ℝ) :
    Set (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :=
  GoodBlocks.properGoodEvent β s n m η κ ∩
    {x | (∀ i : Fin (n : ℕ),
      ((n : ℝ) + m + 1) ^ s.val *
        (ConditionalForces.compensationC β s n m x +
          ConditionalForces.compensationB β s n m i x) ≤ (n : ℝ) ^ (κ * η)) ∧
      ∀ j : Fin ((n : ℕ) - 1),
        ((n : ℝ) + m + 1) *
          (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) ^ s.val *
          |ConditionalForces.compensationB β s n m ⟨j.val + 1, by omega⟩ x -
            ConditionalForces.compensationB β s n m ⟨j.val, by omega⟩ x| ≤
          (n : ℝ) ^ (κ * η)}

/-- See Subsection 6.3 of the paper: the short-range event uses the existing complete
event, including all six coefficient families, at fine tolerance `η`. -/
def shortFineEvent (p : Parameters) (n : ℕ+) (m : ℕ) (η κ : ℝ) :
    Set (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :=
  DecayShort.ExceptionalEvent.properGoodEvent p n m (by simp; omega)
    η ((n : ℝ) ^ (κ * η))

/-- Measurability of the literal long-range weight in Subsection 6.3. -/
theorem measurable_longEnvelope (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε C₀ : ℝ) :
    Measurable (longEnvelope β s n m θ ε C₀) := by
  apply Measurable.const_mul
  apply Measurable.add
  · apply Measurable.add
    · apply Measurable.add
      · apply Measurable.const_add
        exact Finset.measurable_sum _ fun i _ =>
          ((InterpolationMatrix.measurable_penaltyHessian n θ ε i i).comp
            measurable_subtype_coe).abs
      · exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
          GoodBlocks.measurable_conditionalHessian β s n m i j
    · exact Finset.measurable_sum _ fun i _ =>
        ConditionalForces.measurable_compensationB β s n m i
  · exact ConditionalForces.measurable_compensationC β s n m

/-- Positivity of the literal envelope in Subsection 6.3, before taking any
moments. In particular its real-to-extended conversion loses no sign. -/
theorem longEnvelope_lower (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε C₀ : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    (n : ℝ) ^ C₀ ≤ longEnvelope β s n m θ ε C₀ x := by
  have hP := Finset.sum_nonneg (s := Finset.univ) (fun i _ =>
    Finset.sum_nonneg (s := Finset.univ) fun j _ =>
      GoodBlocks.conditionalHessian_nonneg β s n m i j x)
  have hb := Finset.sum_nonneg (s := Finset.univ) fun i _ =>
    ConditionalForces.compensationB_nonneg β s n m i x
  have hc := ConditionalForces.compensationC_nonneg β s n m x
  have hF := Finset.sum_nonneg (s := Finset.univ) fun i _ =>
    abs_nonneg (InterpolationMatrix.penaltyHessian n θ ε x.val i i)
  unfold longEnvelope
  nlinarith [Real.rpow_pos_of_pos (show (0 : ℝ) < n by exact_mod_cast n.pos) C₀]

private theorem measurable_forall {X ι : Type*} [MeasurableSpace X] [Countable ι]
    {P : ι → X → Prop} (h : ∀ i, MeasurableSet {x | P i x}) :
    MeasurableSet {x | ∀ i, P i x} := by
  simpa only [ofPred_forall] using MeasurableSet.iInter h

/-- Measurability of all long-range fine conditions in Subsection 6.3. -/
theorem measurableSet_longFineEvent (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (η κ : ℝ) :
    MeasurableSet (longFineEvent β s n m η κ) := by
  apply (GoodBlocks.measurableSet_properGoodEvent β s n m η κ).inter
  apply MeasurableSet.inter
  · exact measurable_forall fun i => measurableSet_le
      (((ConditionalForces.measurable_compensationC β s n m).add
        (ConditionalForces.measurable_compensationB β s n m i)).const_mul _)
      measurable_const
  · exact measurable_forall fun j => measurableSet_le
      (((ConditionalForces.measurable_compensationB β s n m ⟨j.val + 1, by omega⟩).sub
        (ConditionalForces.measurable_compensationB β s n m ⟨j.val, by omega⟩)).abs.const_mul _)
      measurable_const

private theorem conditional_matrix_nonneg (p : Parameters) (n : ℕ+) (m k : ℕ)
    (hk : k ≤ (n : ℕ) + m + 1)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (i j : Fin k) :
    0 ≤ IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat k hk
      (DecayShort.conditionalIntervalWeight p n m n.pos (Equiv.refl _) x) i j := by
  apply Finset.sum_nonneg
  intro t _
  apply mul_nonneg
  · exact DecayShort.conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x t
  · unfold IntervalBoundary.rankOne
    split_ifs <;> norm_num

/-- Measurability of the literal short-range weight in Subsection 6.3. -/
theorem measurable_shortEnvelope (p : Parameters) (n : ℕ+) (m : ℕ)
    (θ : PhysicalCutoff) (ε C₀ : ℝ) :
    Measurable (shortEnvelope p n m θ ε C₀) := by
  unfold shortEnvelope
  apply Measurable.const_mul
  apply Measurable.add
  · apply Measurable.add
    · apply Measurable.add
      · apply Measurable.const_add
        exact Finset.measurable_sum _ fun i _ =>
          ((InterpolationMatrix.measurable_penaltyHessian n θ ε i i).comp
            measurable_subtype_coe).abs
      · exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
          DecayShort.measurable_conditional_intervalMatrix p n m n.pos n (by omega) i j
    · exact Finset.measurable_sum _ fun i _ =>
        (Finset.measurable_sum _ fun a _ =>
          DecayShort.measurable_conditional_intervalMatrix p n m n.pos
            ((n : ℕ) + m + 1) le_rfl _ a).const_mul _
  · exact (Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ =>
      DecayShort.measurable_conditional_intervalMatrix p n m n.pos
        ((n : ℕ) + m + 1) le_rfl a b).const_mul _

/-- Positivity of the short-range envelope of Subsection 6.3 at every positive
retained point, including a point exterior (`m = 0`). -/
theorem shortEnvelope_lower (p : Parameters) (n : ℕ+) (m : ℕ)
    (θ : PhysicalCutoff) (ε C₀ : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    (n : ℝ) ^ C₀ ≤ shortEnvelope p n m θ ε C₀ x := by
  dsimp only [shortEnvelope]
  apply le_mul_of_one_le_right (Real.rpow_nonneg (by positivity) _)
  have hP := Finset.sum_nonneg (s := Finset.univ) (fun i _ =>
    Finset.sum_nonneg (s := Finset.univ) fun j _ =>
      conditional_matrix_nonneg p n m n (by omega) x i j)
  have hb := Finset.sum_nonneg (s := Finset.univ) (fun i : Fin (n : ℕ) => fun _ =>
    mul_nonneg (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ m + 1))
      (Finset.sum_nonneg (s := Finset.univ.filter
        (fun a : Fin ((n : ℕ) + m + 1) => (n : ℕ) ≤ a.val))
        (fun a _ => conditional_matrix_nonneg p n m
          ((n : ℕ) + m + 1) le_rfl x (Fin.castLE (by omega) i) a)))
  have hc := mul_nonneg (sq_nonneg ((m + 1 : ℝ)⁻¹))
    (Finset.sum_nonneg (s := Finset.univ.filter
      (fun a : Fin ((n : ℕ) + m + 1) => (n : ℕ) ≤ a.val)) (fun a _ =>
        Finset.sum_nonneg (s := Finset.univ.filter
          (fun b : Fin ((n : ℕ) + m + 1) => (n : ℕ) ≤ b.val)) (fun b _ => conditional_matrix_nonneg p n m
          ((n : ℕ) + m + 1) le_rfl x a b)))
  have hF := Finset.sum_nonneg (s := Finset.univ) fun i _ =>
    abs_nonneg (InterpolationMatrix.penaltyHessian n θ ε x.val i i)
  linarith

section RetainedKernel

variable (p : Parameters) (n m : ℕ) (θ : PhysicalCutoff) (ε : ℝ)

/-- See Lemma 6.5 of the paper: every interior length fibre is carried by the
positive retained chart where the compensated coefficients are defined. -/
theorem retained_support (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) :
    ∀ᵐ x ∂fibreKernel p n m θ ε L,
      x ∈ AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1) := by
  have hS : MeasurableSet (AffineSimplex.massSimplex n L.val) := by
    change MeasurableSet ({x | ∀ i, 0 < x i} ∩ AffineSimplex.massHyperplane n L.val)
    exact (measurable_forall fun i => measurableSet_lt measurable_const
      (EuclideanSpace.proj (𝕜 := ℝ) i).measurable).inter
      (AffineSimplex.isClosed_massHyperplane n L.val).measurableSet
  have hmem : ∀ᵐ x ∂AffineSimplex.simplexVolume n L.val,
      x ∈ AffineSimplex.massSimplex n L.val := by
    rw [AffineSimplex.simplexVolume_eq_restrict]
    exact ae_restrict_mem hS
  have h : ∀ᵐ x ∂fibreKernel p n m θ ε L,
      x ∈ AffineSimplex.massSimplex n L.val :=
    (withDensity_absolutelyContinuous _ _) hmem
  exact h.mono fun x hx => ⟨hx.1, hx.2.trans_lt L.property.2⟩

/-- See Subsection 6.3 of the paper: the existing physical fibre kernel on the
retained carrier. This is a pullback along inclusion, not a new density. -/
def retainedKernel : Kernel (Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ))
    (AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1)) :=
  (fibreKernel p n m θ ε).comapRight
    (MeasurableEmbedding.subtype_coe (AffineSimplex.isOpen_chartDomain _ _).measurableSet)

instance retainedKernel_markov : IsMarkovKernel (retainedKernel p n m θ ε) := by
  apply Kernel.IsMarkovKernel.comapRight
  intro L
  rw [Subtype.range_coe_subtype]
  have h := Measure.restrict_eq_self_of_ae_mem (retained_support p n m θ ε L)
  have hh := congrArg (fun μ => μ Set.univ) h
  change (fibreKernel p n m θ ε L)
    (AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1)) = 1
  simpa only [Measure.restrict_apply_univ, measure_univ] using hh

/-- The pulled-back fibre law has exactly the original law as its image. See Lemma 6.5. -/
theorem map_retainedKernel (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) :
    (retainedKernel p n m θ ε L).map Subtype.val = fibreKernel p n m θ ε L := by
  rw [retainedKernel, Kernel.comapRight_apply,
    map_comap_subtype_coe (AffineSimplex.isOpen_chartDomain _ _).measurableSet]
  exact Measure.restrict_eq_self_of_ae_mem (retained_support p n m θ ε L)

/-- The coarea identity on the coefficient carrier, for every measurable
nonnegative test. See Lemma 6.5 and Subsection 6.3. -/
theorem retained_lintegral_disintegration
    {f : AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1) → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ x, f x ∂(activeMeasure p n m θ ε).comap Subtype.val) =
      ∫⁻ L, ∫⁻ x, f x ∂retainedKernel p n m θ ε L ∂lengthMeasure p n m θ ε := by
  let D := AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1)
  have hD : MeasurableSet D := (AffineSimplex.isOpen_chartDomain _ _).measurableSet
  obtain ⟨g, hg, he⟩ := (MeasurableEmbedding.subtype_coe hD).exists_measurable_extend hf
    (fun _ => inferInstance)
  have hs : ∀ᵐ x ∂activeMeasure p n m θ ε, x ∈ D := by
    rw [ae_iff]
    change (activeMeasure p n m θ ε) Dᶜ = 0
    rw [active_law_density, Measure.smul_apply, smul_eq_mul,
      withDensity_apply _ hD.compl]
    have hz : (∫⁻ x in Dᶜ, marginalWeight p n m θ ε x ∂volume) = 0 := by
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [ae_restrict_mem hD.compl] with x hx
      exact marginalWeight_eq_zero p n m θ ε hx
    rw [hz, mul_zero]
  have hleft : (∫⁻ x, f x ∂(activeMeasure p n m θ ε).comap Subtype.val) =
      ∫⁻ x, g x ∂activeMeasure p n m θ ε := by
    rw [← he]
    change (∫⁻ x : D, g x.val ∂(activeMeasure p n m θ ε).comap Subtype.val) = _
    rw [lintegral_subtype_comap hD,
      Measure.restrict_eq_self_of_ae_mem hs]
  rw [hleft, lintegral_disintegration p n m θ ε hg]
  apply lintegral_congr
  intro L
  rw [← he]
  change _ = ∫⁻ x : D, g x.val ∂retainedKernel p n m θ ε L
  rw [← (MeasurableEmbedding.subtype_coe hD).lintegral_map,
    map_retainedKernel p n m θ ε L]

end RetainedKernel

/-- See Subsection 6.3 of the paper: conditional weighted bad mass on the coefficient
carrier. The kernel is already the literal physical length conditional. -/
def retainedExceptionalMass (p : Parameters) (n m : ℕ) (θ : PhysicalCutoff) (ε : ℝ)
    (W : AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1) → ℝ≥0∞)
    (G : Set (AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1)))
    (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) : ℝ≥0∞ :=
  ∫⁻ x in Gᶜ, W x ∂retainedKernel p n m θ ε L

/-- See Subsection 6.3 of the paper: the exact long-range conditional remainder.
`ε` is the physical penalty exponent and `η` the independent fine tolerance. -/
def longRemainder (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n m : ℕ) (θ : PhysicalCutoff) (ε C₀ η κ : ℝ) :
    Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ) → ℝ≥0∞ :=
  retainedExceptionalMass (ofLong β s) n m θ ε
    (fun x => ENNReal.ofReal (longEnvelope β s n.succPNat m θ ε C₀ x))
    (longFineEvent β s n.succPNat m η κ)

/-- See Subsection 6.3 of the paper: the exact short-range conditional remainder. -/
def shortRemainder (p : Parameters) (n m : ℕ) (θ : PhysicalCutoff)
    (ε C₀ η κ : ℝ) : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ) → ℝ≥0∞ :=
  retainedExceptionalMass p n m θ ε
    (fun x => ENNReal.ofReal (shortEnvelope p n.succPNat m θ ε C₀ x))
    (shortFineEvent p n.succPNat m η κ)

/-- The conditional error is measurable without first assuming a moment
bound, as required in Subsection 6.3. -/
theorem measurable_retainedExceptionalMass (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ)
    {W : AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1) → ℝ≥0∞}
    (hW : Measurable W)
    {G : Set (AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1))}
    (hG : MeasurableSet G) :
    Measurable (retainedExceptionalMass p n m θ ε W G) := by
  have h := ((hW.indicator hG.compl).comp measurable_snd).lintegral_kernel_prod_right'
    (κ := retainedKernel p n m θ ε)
  change Measurable (fun L => ∫⁻ x in Gᶜ, W x ∂retainedKernel p n m θ ε L)
  simpa only [Function.comp_def, lintegral_indicator hG.compl] using h

/-- See Subsection 6.3 of the paper: the exact long-range remainder is measurable. -/
theorem measurable_longRemainder (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n m : ℕ) (θ : PhysicalCutoff) (ε C₀ η κ : ℝ) :
    Measurable (longRemainder β s n m θ ε C₀ η κ) :=
  measurable_retainedExceptionalMass _ _ _ _ _
    (measurable_longEnvelope β s n.succPNat m θ ε C₀).ennreal_ofReal
    (measurableSet_longFineEvent β s n.succPNat m η κ)

/-- See the proof of Lemma 6.5 in the paper: conditional Jensen and
Hölder on the literal retained carrier. All moments remain extended-valued. -/
theorem retained_exceptional_moments_le (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ)
    {W : AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1) → ℝ≥0∞}
    (hW : Measurable W)
    {G : Set (AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1))}
    (hG : MeasurableSet G) :
    let μ := (activeMeasure p n m θ ε).comap Subtype.val
    (∫⁻ L, retainedExceptionalMass p n m θ ε W G L +
      retainedExceptionalMass p n m θ ε W G L ^ 2 ∂lengthMeasure p n m θ ε) ≤
      ((∫⁻ x, W x ^ 2 ∂μ) ^ (1 / 2 : ℝ) +
        (∫⁻ x, W x ^ 4 ∂μ) ^ (1 / 2 : ℝ)) * μ Gᶜ ^ (1 / 2 : ℝ) := by
  intro μ
  have hdis := retained_lintegral_disintegration p n m θ ε
    (hW.indicator hG.compl)
  have hdis₂ := retained_lintegral_disintegration p n m θ ε
    ((hW.pow_const 2).indicator hG.compl)
  simp only [lintegral_indicator hG.compl] at hdis hdis₂
  have hj : (∫⁻ L, retainedExceptionalMass p n m θ ε W G L ^ 2
      ∂lengthMeasure p n m θ ε) ≤ ∫⁻ x in Gᶜ, W x ^ 2 ∂μ := by
    rw [hdis₂]
    apply lintegral_mono
    intro L
    have h := Internal.square_lintegral_le
      (ν := retainedKernel p n m θ ε L) (hW.indicator hG.compl).aemeasurable
    have hp (x) : (Gᶜ.indicator W x) ^ 2 = Gᶜ.indicator (fun y => W y ^ 2) x := by
      by_cases hx : x ∈ Gᶜ <;> simp [hx]
    simpa only [retainedExceptionalMass, hp, lintegral_indicator hG.compl] using h
  rw [lintegral_add_left (measurable_retainedExceptionalMass p n m θ ε hW hG),
    add_mul]
  apply add_le_add
  · rw [show (∫⁻ L, retainedExceptionalMass p n m θ ε W G L
        ∂lengthMeasure p n m θ ε) = ∫⁻ x in Gᶜ, W x ∂μ from hdis.symm]
    exact Internal.restricted_first_moment_le hW hG.compl
  · exact hj.trans (Internal.restricted_second_moment_le hW hG.compl)

/-- See Subsection 6.3 of the paper: increasing the tolerance lowers the upper-gap
penalty. The physical two-sided penalty retains its exponent `ε`. -/
theorem fine_penalty_le (N n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ))
    (θ : PhysicalCutoff) {ε η : ℝ} (hεη : ε ≤ η) (X : Riesz1.Configuration N) :
    physicalGapPenalty N n hn θ η false X ≤ physicalGapPenalty N n hn θ ε true X := by
  have hmono : MonotoneOn θ.val (Ioi (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    · exact θ.property.1.continuousOn.mono Ioi_subset_Ici_self
    · intro x hx
      exact (PhysicalCollision.cutoff_contDiffAt θ (by simpa only [interior_Ioi, Set.mem_Ioi] using hx)).differentiableAt
        (by simp) |>.differentiableWithinAt
    · intro x hx
      exact PhysicalCollision.cutoff_deriv_nonneg θ (by simpa only [interior_Ioi, Set.mem_Ioi] using hx)
  apply Finset.sum_le_sum
  intro i _
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
  apply le_add_of_le_of_nonneg
  · apply hmono
    · exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Riesz1.gap_pos X _)
    · exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Riesz1.gap_pos X _)
    · apply mul_le_mul_of_nonneg_right _ (Riesz1.gap_pos X _).le
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast n.pos : (1 : ℝ) ≤ n)
        (neg_le_neg hεη)
  · exact θ.property.2.2.1 _ (mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (inv_nonneg.mpr (Riesz1.gap_pos X _).le))

/-- See the proof of Lemma 6.5 in the paper: comparison of the actual
physical tilt with an upper-gap tilt at the finer tolerance. This is a
comparison of the measures, valid for all measurable tests. -/
theorem fine_tilt_domination (p : Parameters) (N n : ℕ+)
    (hn : (n : ℕ) ≤ (N : ℕ)) (θ : PhysicalCutoff) {ε η z : ℝ}
    (hεη : ε ≤ η) (hz : 0 < z)
    (hZ : z ≤ NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (physicalGapPenalty N n hn θ ε true)) :
    tiltedParticleMeasure p N n hn θ ε true ≤
      ENNReal.ofReal z⁻¹ • tiltedParticleMeasure p N n hn θ η false := by
  have hnorm : (tiltNormalizer p N n hn θ ε true)⁻¹ ≤ ENNReal.ofReal z⁻¹ := by
    rw [InterpolatingDensities.normalizer_eq, ENNReal.ofReal_inv_of_pos hz]
    exact ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal hZ)
  have hden : (gibbsMeasure p N).withDensity (fun X => ENNReal.ofReal
      (Real.exp (-p.val.1 * physicalGapPenalty N n hn θ ε true X))) ≤
      (gibbsMeasure p N).withDensity (fun X => ENNReal.ofReal
        (Real.exp (-p.val.1 * physicalGapPenalty N n hn θ η false X))) := by
    apply withDensity_mono
    apply Filter.Eventually.of_forall
    intro X
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (fine_penalty_le N n hn θ hεη X)
      (neg_nonpos.mpr p.property.1.le)
  have hupper : (gibbsMeasure p N).withDensity (fun X => ENNReal.ofReal
      (Real.exp (-p.val.1 * physicalGapPenalty N n hn θ η false X))) ≤
      tiltedParticleMeasure p N n hn θ η false := by
    have hZ1 : (1 : ℝ≥0∞) ≤ (tiltNormalizer p N n hn θ η false)⁻¹ := by
      simpa only [inv_one] using
        (ENNReal.inv_le_inv.mpr (DefinitionSanity.tilt_normalizer_valid p N n hn θ η false).2)
    calc
      _ = (1 : ℝ≥0∞) • _ := (one_smul _ _).symm
      _ ≤ _ := by
        unfold tiltedParticleMeasure
        gcongr
  calc
    _ ≤ ENNReal.ofReal z⁻¹ • (gibbsMeasure p N).withDensity (fun X =>
        ENNReal.ofReal (Real.exp (-p.val.1 * physicalGapPenalty N n hn θ ε true X))) := by
      unfold tiltedParticleMeasure
      gcongr
    _ ≤ _ := by gcongr; exact hden.trans hupper

/-- See the proof of Lemma 6.5 in the paper: the fine-tilt comparison
on the exact retained carrier used by the coefficient moment theorems. -/
theorem fine_active_domination (p : Parameters) (n : ℕ+) (m : ℕ)
    (θ : PhysicalCutoff) {ε η z : ℝ} (hεη : ε ≤ η) (hz : 0 < z)
    (hZ : z ≤ NonnegativeTilt.expTiltNormalizer
      (gibbsMeasure p ((n : ℕ) + m).succPNat) p.val.1
      (physicalGapPenalty ((n : ℕ) + m).succPNat n (by simp; omega) θ ε true)) :
    (activeTiltedGapLaw p ((n : ℕ) + m).succPNat n (by simp; omega) θ ε true).comap
      ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ))) ≤
      ENNReal.ofReal z⁻¹ •
        (activeTiltedGapLaw p ((n : ℕ) + m).succPNat n (by simp; omega) θ η false).comap
          ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ))) := by
  let N := ((n : ℕ) + m).succPNat
  have hpart := fine_tilt_domination p N n (by simp [N]; omega) θ hεη hz hZ
  have hm : Measurable (fun X : Riesz1.Configuration N =>
      WithLp.toLp 2 (finiteGapBlock (K := n) X)) :=
    DefinitionSanity.active_projection_measurable N n
  have hmap := Measure.map_mono hpart hm
  rw [Measure.map_smul] at hmap
  swap
  · exact hm.aemeasurable
  have he := MeasurableEmbedding.subtype_coe
    (AffineSimplex.isOpen_chartDomain n ((n + m : ℕ) + 1)).measurableSet
  apply Measure.le_iff.mpr
  intro E hE
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.comap_apply _ he.injective (fun _ h => he.measurableSet_image.mpr h) _ hE,
    Measure.comap_apply _ he.injective (fun _ h => he.measurableSet_image.mpr h) _ hE]
  exact hmap (Subtype.val '' E)

/-- See the proof of Lemma 6.5 in the paper: the domination constant is
uniform in both sizes and on a compact temperature interval. The fine
parameter may be chosen after the physical penalty exponent. -/
theorem compact_fine_active_domination (s ε βlo βhi : ℝ)
    (hs : 0 < s) (hs1 : s ≠ 1) (hε : 0 < ε)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (θ : PhysicalCutoff) :
    ∃ z : ℝ, 0 < z ∧ z ≤ 1 ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (n : ℕ+) (m : ℕ),
      2 ≤ (n : ℕ) + m + 1 → ∀ η : ℝ, ε ≤ η →
      (activeTiltedGapLaw p ((n : ℕ) + m).succPNat n (by simp; omega) θ ε true).comap
        ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ))) ≤
      ENNReal.ofReal z⁻¹ •
        (activeTiltedGapLaw p ((n : ℕ) + m).succPNat n (by simp; omega) θ η false).comap
          ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ))) := by
  obtain ⟨z, hz, hZ⟩ := InterpolantLocalLaws.compact_tilt_normalizer
    s ε βlo βhi hs hs1 hε hlo hle θ
  refine ⟨min z 1, lt_min hz zero_lt_one, min_le_right _ _, ?_⟩
  intro p hp hpl hph n m hN η hεη
  apply fine_active_domination p n m θ hεη (lt_min hz zero_lt_one)
  exact (min_le_left _ _).trans (hZ p hp hpl hph ((n : ℕ) + m).succPNat n hN _)

set_option backward.isDefEq.respectTransparency true in
/-- See Subsection 6.3 of the paper: every coefficient condition of the actual
short-range fine event is measurable. Finiteness of the exterior energy
comes from the conditional moment theorem. -/
private theorem measurableSet_shortFineEvent_internal (p : Parameters)
    (n : ℕ+) (m : ℕ) (η κ : ℝ)
    (hVm : ∀ i : Fin (n : ℕ), Measurable (fun x =>
      (DecayShort.PhysicalFibres.exteriorGradientEnergy p n m n.pos x i).toReal)) :
    MeasurableSet (shortFineEvent p n m η κ) := by
  let hn : (n : ℕ) ≤ (n : ℕ) + m + 1 := by omega
  let A := fun x => DecayShort.conditionalIntervalWeight p n m n.pos (Equiv.refl _) x
  let H := fun x => IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat
    ((n : ℕ) + m + 1) le_rfl (A x)
  let S := Finset.univ.filter (fun a : Fin ((n : ℕ) + m + 1) => (n : ℕ) ≤ a.val)
  have hH (i j : Fin ((n : ℕ) + m + 1)) : Measurable (fun x => H x i j) :=
    DecayShort.measurable_conditional_intervalMatrix p n m n.pos _ le_rfl i j
  have hb (i : Fin (n : ℕ)) : Measurable (fun x => (m + 1 : ℝ)⁻¹ *
      ∑ a ∈ S, H x (Fin.castLE hn i) a) :=
    (Finset.measurable_sum _ fun a _ => hH _ a).const_mul _
  have hc : Measurable (fun x => (m + 1 : ℝ)⁻¹ ^ 2 * ∑ a ∈ S, ∑ b ∈ S, H x a b) :=
    (Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => hH a b).const_mul _
  obtain ⟨hprefix, hsuffix, hfull⟩ :=
    DecayShort.measurable_physical_boundary_coefficients p n m n.pos hn
  unfold shortFineEvent DecayShort.ExceptionalEvent.properGoodEvent
  apply MeasurableSet.inter
  · exact (DecayShort.ExceptionalEvent.measurableSet_goodBlockEvent p.val.2 n
      ((n : ℕ) + m).succPNat η).preimage
        ((PiLp.continuous_ofLp 2 (fun _ : Fin (n : ℕ) => ℝ)).measurable.comp
          measurable_subtype_coe)
  · change MeasurableSet {x |
      (∀ i j : Fin (n : ℕ), IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat
        n hn (A x) i j ≤ (n : ℝ) ^ (κ * η) *
          (1 + (Riesz1.cyclicIndexDistance ((n : ℕ) + m).succPNat
            (Fin.castLE hn i) (Fin.castLE hn j) : ℝ)) ^ (-p.val.2)) ∧
      (∀ k : Fin ((n : ℕ) - 1), IntervalBoundary.prefixCoefficient
        ((n : ℕ) + m).succPNat n hn (A x) (k.val + 1) ≤
          (n : ℝ) ^ (κ * η) * (k.val + 1 : ℕ) ^ (-p.val.2 - 1)) ∧
      (∀ k : Fin ((n : ℕ) - 1), IntervalBoundary.suffixCoefficient
        ((n : ℕ) + m).succPNat n hn (A x) (k.val + 1) ≤
          (n : ℝ) ^ (κ * η) * ((n : ℕ) - (k.val + 1) : ℕ) ^ (-p.val.2 - 1)) ∧
      IntervalBoundary.fullCoefficient ((n : ℕ) + m).succPNat n hn (A x) ≤
        (n : ℝ) ^ (κ * η) * (n : ℝ) ^ (-p.val.2) ∧
      (∀ i : Fin (n : ℕ), (m + 1 : ℝ)⁻¹ * ∑ a ∈ S, H x (Fin.castLE hn i) a +
        (m + 1 : ℝ)⁻¹ ^ 2 * ∑ a ∈ S, ∑ b ∈ S, H x a b ≤
          (n : ℝ) ^ (κ * η) / (((n : ℕ) + m).succPNat : ℝ)) ∧
      ∀ i : Fin (n : ℕ),
        (DecayShort.PhysicalFibres.exteriorGradientEnergy p n m n.pos x i).toReal ≤
          (n : ℝ) ^ (κ * η) * (min (i.val + 1) ((n : ℕ) - i.val) : ℕ) ^ (1 - 2 * p.val.2)}
    refine (measurable_forall fun i => measurable_forall fun j => measurableSet_le
      (DecayShort.measurable_conditional_intervalMatrix p n m n.pos n hn i j)
        measurable_const).inter ?_
    refine (measurable_forall fun (k : Fin ((n : ℕ) - 1)) => measurableSet_le (hprefix (k.val + 1))
      measurable_const).inter ?_
    refine (measurable_forall fun (k : Fin ((n : ℕ) - 1)) => measurableSet_le (hsuffix (k.val + 1))
      measurable_const).inter ?_
    refine (measurableSet_le hfull measurable_const).inter ?_
    exact (measurable_forall fun i => measurableSet_le ((hb i).add hc) measurable_const).inter
      (measurable_forall fun i => measurableSet_le (hVm i) measurable_const)

/-- See Subsection 6.3 of the paper: measurability of the complete short-range fine
set, using the finite exterior-energy profile. -/
theorem measurableSet_shortFineEvent (p : Parameters) (hs : 1 < p.val.2)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (η κ : ℝ) :
    MeasurableSet (shortFineEvent p n m η κ) := by
  let hn : (n : ℕ) ≤ (n : ℕ) + m + 1 := by omega
  obtain ⟨Cθ, hCθ, hcurv, _⟩ := θ.property.2.2.2.2
  obtain ⟨_, _, hV⟩ := DecayShort.activeTilt_conditional_exterior_energy_moments
    p.val.2 p.val.1 p.val.1 1 Cθ hs p.property.1 le_rfl zero_lt_one hCθ
  have hVm (i : Fin (n : ℕ)) : Measurable (fun x =>
      (DecayShort.PhysicalFibres.exteriorGradientEnergy p n m n.pos x i).toReal) :=
    (hV p rfl le_rfl le_rfl n m hn θ hcurv true i 1 le_rfl).1
  exact measurableSet_shortFineEvent_internal p n m η κ hVm

/-- See Subsection 6.3 of the paper: the actual short-range conditional remainder is
measurable at every interior length. -/
theorem measurable_shortRemainder (p : Parameters) (hs : 1 < p.val.2)
    (n m : ℕ) (θ : PhysicalCutoff) (ε C₀ η κ : ℝ) :
    Measurable (shortRemainder p n m θ ε C₀ η κ) :=
  measurable_retainedExceptionalMass _ _ _ _ _
    (measurable_shortEnvelope p n.succPNat m θ ε C₀).ennreal_ofReal
    (measurableSet_shortFineEvent p hs n.succPNat m θ η κ)

/-- The explicit moment degree selected in the proof of Lemma 6.5. Its uses assume `s > 0`. -/
def momentDegree (s : ℝ) : ℝ := 10 * (s + 2) * (1 + 1 / s)

/-- See the proof of Lemma 6.5 in the paper: the displayed `A(s)` bounds
all four degrees incurred by the coefficient and inverse-penalty estimates. -/
theorem momentDegree_bounds {s : ℝ} (hs : 0 < s) :
    0 < momentDegree s ∧ (s + 2) / s ≤ momentDegree s ∧
      (s + 2) + 2 * ((s + 2) / s) ≤ momentDegree s ∧
      4 / s ≤ momentDegree s ∧ 4 ≤ momentDegree s := by
  have hA : momentDegree s = 10 * (s + 2) * (s + 1) / s := by
    unfold momentDegree
    field_simp
  have hD : (s + 2) + 2 * ((s + 2) / s) = (s + 2) ^ 2 / s := by
    field_simp
  rw [hA, hD]
  refine ⟨by positivity, ?_, ?_, ?_, ?_⟩
  · apply (div_le_div_iff_of_pos_right hs).mpr
    nlinarith [sq_nonneg s]
  · apply (div_le_div_iff_of_pos_right hs).mpr
    nlinarith [sq_nonneg s]
  · apply (div_le_div_iff_of_pos_right hs).mpr
    nlinarith [sq_nonneg s]
  · apply (le_div_iff₀ hs).mpr
    nlinarith [sq_nonneg s]

private theorem norm_domination_internal {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) (f : X → ℝ) {z q : ℝ} (hz : 0 < z) (hz1 : z ≤ 1)
    (hq : 1 ≤ q) (hμ : μ ≤ ENNReal.ofReal z⁻¹ • ν) :
    eLpNorm f (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal z⁻¹ * eLpNorm f (ENNReal.ofReal q) ν := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hnorm := (eLpNorm_mono_measure f hμ).trans
    (eLpNorm_smul_measure_le (ENNReal.ofReal z⁻¹) f (ENNReal.ofReal q) ν)
  simp only [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal hq0.le,
    smul_eq_mul] at hnorm
  apply hnorm.trans
  refine mul_le_mul' ?_ le_rfl
  rw [ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr hz.le) (inv_nonneg.mpr hq0.le)]
  apply ENNReal.ofReal_le_ofReal
  calc
    z⁻¹ ^ q⁻¹ ≤ z⁻¹ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le
      ((one_le_inv₀ hz).mpr hz1) ((inv_le_one₀ hq0).mpr hq)
    _ = z⁻¹ := Real.rpow_one _

/-- See the proof of Lemma 6.5 in the paper: compensation moments under
its actual two-sided marginal, with degree `(s+2)/s`, uniform in both
sizes and on compact temperature intervals. The fine tolerance `η` may
exceed the physical exponent `ε`. -/
theorem long_compensation_moments (s : Riesz1.RieszExponent)
    (ε η βlo βhi : ℝ) (hε : 0 < ε) (hεη : ε ≤ η)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n : ℕ+) (m : ℕ), 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ q : ℝ, 1 ≤ q →
      let μ := (activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n
        (by simp; omega) θ ε true).comap
        ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
      (∀ i : Fin (n : ℕ),
        eLpNorm (ConditionalForces.compensationB β s n m i) (ENNReal.ofReal q) μ +
          eLpNorm (ConditionalForces.compensationC β s n m) (ENNReal.ofReal q) μ ≤
            ENNReal.ofReal (C * q ^ ((s.val + 2) / s.val) *
              ((n : ℝ) + m + 1) ^ (-s.val))) ∧
      (∀ i : Fin (n : ℕ), i.val + 1 < (n : ℕ) →
        eLpNorm (fun x => ConditionalForces.compensationB β s n m (i + 1) x -
          ConditionalForces.compensationB β s n m i x) (ENNReal.ofReal q) μ ≤
            ENNReal.ofReal (C * q ^ ((s.val + 2) / s.val) *
              ((n : ℝ) + m + 1)⁻¹ *
              (min (i.val + 1) ((n : ℕ) - i.val) : ℕ) ^ (-s.val))) := by
  obtain ⟨Cθ, hCθ, hcurv, _⟩ := θ.property.2.2.2.2
  obtain ⟨C, hC, hm⟩ := ConditionalForces.compensation_moments
    s βlo βhi η Cθ hlo hle (hε.trans_le hεη) hCθ
  obtain ⟨z, hz, hz1, hdom⟩ := compact_fine_active_domination s.val ε βlo βhi
    s.property.1 (by linarith [s.property.2]) hε hlo hle θ
  refine ⟨z⁻¹ * C, by positivity, ?_⟩
  intro β hβ n m hhalf q hq μ
  let ν := (activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n
    (by simp; omega) θ η false).comap
    ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
  have hμν : μ ≤ ENNReal.ofReal z⁻¹ • ν :=
    hdom (ofLong β s) rfl hβ.1 hβ.2 n m (by have := n.pos; omega) η hεη
  have hnorm (f) := norm_domination_internal μ ν f hz hz1 hq hμν
  have hb := hm β hβ n m hhalf (by simp; omega) θ hcurv q hq
  refine ⟨fun i => ?_, fun i hi => ?_⟩
  · calc
      _ ≤ ENNReal.ofReal z⁻¹ * eLpNorm (ConditionalForces.compensationB β s n m i) (ENNReal.ofReal q) ν +
          ENNReal.ofReal z⁻¹ * eLpNorm (ConditionalForces.compensationC β s n m) (ENNReal.ofReal q) ν :=
        add_le_add (hnorm _) (hnorm _)
      _ ≤ ENNReal.ofReal z⁻¹ * ENNReal.ofReal (C * q ^ ((s.val + 2) / s.val) *
          ((n : ℝ) + m + 1) ^ (-s.val)) := by
        rw [← mul_add]
        exact mul_le_mul' le_rfl (hb.1 i)
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  · apply (hnorm _).trans
    apply (mul_le_mul' le_rfl (hb.2.1 i hi)).trans_eq
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring

private theorem profile_cancel_internal {a w T v : ℝ} (ha : 0 ≤ a)
    (haw : a * w = 1) (hv : v ≤ T * w) : a * v ≤ T := by
  have h := mul_le_mul_of_nonneg_left hv ha
  calc
    a * v ≤ a * (T * w) := h
    _ = T := by rw [mul_left_comm, haw, mul_one]

/-- See the proof of Lemma 6.5 in the paper: the full long-range fine
set, including compensation size and differences, has exponentially small
complement under the actual two-sided marginal. The power is selected
before the temperature interval. -/
theorem long_fine_event_probability (hRig : External.LongRangeRigidityLocallyUniform)
    (s : Riesz1.RieszExponent) (ε η : ℝ) (hε : 0 < ε) (hεη : ε ≤ η)
    (θ : PhysicalCutoff) (βlo βhi : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n : ℕ+) (m : ℕ), 2 ≤ (n : ℕ) → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ κ : ℝ, 1 ≤ κ →
      ((activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n
        (by simp; omega) θ ε true).comap
          ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ))))
        (longFineEvent β s n m η κ)ᶜ ≤ ENNReal.ofReal
          (C * Real.exp (-c * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val η)) := by
  have hη : 0 < η := hε.trans_le hεη
  have hd : 0 < (s.val + 2) / s.val := by have := s.property.1; positivity
  obtain ⟨Cθ, hCθ, hcurv, _⟩ := θ.property.2.2.2.2
  obtain ⟨B, b, hB, hb, hbase⟩ := GoodBlocks.proper_good_event
    hRig s hη hCθ βlo βhi hlo hle
  obtain ⟨M, hM, hm⟩ := long_compensation_moments s ε η βlo βhi hε hεη hlo hle θ
  obtain ⟨D, d, hD, hdpos, hcut⟩ := MomentEvent.finite_moment_cutoffs hd hη hM
  obtain ⟨z, hz, hz1, hdom⟩ := compact_fine_active_domination s.val ε βlo βhi
    s.property.1 (by linarith [s.property.2]) hε hlo hle θ
  refine ⟨z⁻¹ * B + D, min b d, by positivity, lt_min hb hdpos, ?_⟩
  intro β hβ n m hn hhalf κ hκ
  let μ := (activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n
    (by simp; omega) θ ε true).comap
      ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
  let ν := (activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n
    (by simp; omega) θ η false).comap
      ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
  have : IsProbabilityMeasure μ := DecayShort.activeTilt_proper_probability _ _ _ _ _ _ _
  let Y : (Fin (n : ℕ) ⊕ Fin ((n : ℕ) - 1)) →
      AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → ℝ :=
    Sum.elim (fun i x => ConditionalForces.compensationC β s n m x +
      ConditionalForces.compensationB β s n m i x)
      (fun j x => ConditionalForces.compensationB β s n m ⟨j.val + 1, by omega⟩ x -
        ConditionalForces.compensationB β s n m ⟨j.val, by omega⟩ x)
  let w : (Fin (n : ℕ) ⊕ Fin ((n : ℕ) - 1)) → ℝ :=
    Sum.elim (fun _ => ((n : ℝ) + m + 1) ^ (-s.val))
      (fun j => ((n : ℝ) + m + 1)⁻¹ *
        (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) ^ (-s.val))
  have hcard : Fintype.card (Fin (n : ℕ) ⊕ Fin ((n : ℕ) - 1)) ≤ (n : ℕ) ^ 2 := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    nlinarith [Nat.sub_le (n : ℕ) 1]
  have hY (i) : Measurable (Y i) := by
    cases i with
    | inl i =>
      exact (ConditionalForces.measurable_compensationC β s n m).add
        (ConditionalForces.measurable_compensationB β s n m i)
    | inr j =>
      exact (ConditionalForces.measurable_compensationB β s n m _).sub
        (ConditionalForces.measurable_compensationB β s n m _)
  have hw (i) : 0 < w i := by
    cases i with
    | inl i => dsimp only [w, Sum.elim_inl]; positivity
    | inr j =>
      have hδ : 0 < min (j.val + 1) ((n : ℕ) - j.val) := by omega
      dsimp only [w, Sum.elim_inr]
      positivity
  have hnorm (i) (q : ℝ) (hq : 1 ≤ q) : eLpNorm (Y i) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (M * q ^ ((s.val + 2) / s.val) * w i) := by
    have hm₀ := hm β hβ n m hhalf q hq
    cases i with
    | inl i =>
      apply (eLpNorm_add_le (μ := μ)
        (f := ConditionalForces.compensationC β s n m)
        (g := ConditionalForces.compensationB β s n m i)
        (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hq)).trans
      dsimp only [w, Sum.elim_inl]
      rw [add_comm]
      exact hm₀.1 i
    | inr j =>
      let i : Fin (n : ℕ) := ⟨j.val, by omega⟩
      have hi : i.val + 1 < (n : ℕ) := by dsimp [i]; omega
      have he : (i + 1 : Fin (n : ℕ)) = ⟨j.val + 1, by omega⟩ := by
        apply Fin.ext
        have h1 : ((1 : Fin (n : ℕ)) : ℕ) = 1 := by
          change 1 % (n : ℕ) = 1
          exact Nat.mod_eq_of_lt (by omega)
        simp only [Fin.val_add, h1, i]
        exact Nat.mod_eq_of_lt (by omega)
      have hh := hm₀.2 i hi
      rw [he] at hh
      simpa only [Y, w, Sum.elim_inr, i, mul_assoc] using hh
  let E := {x | ∃ i, (n : ℝ) ^ (κ * η) * w i < |Y i x|}
  have hE : μ E ≤ ENNReal.ofReal (D * Real.exp (-d * (n : ℝ) ^ (η / (2 * ((s.val + 2) / s.val))))) :=
    hcut n (by omega) μ Y w κ hcard hY hw hκ hnorm
  have hsub : (longFineEvent β s n m η κ)ᶜ ⊆
      (GoodBlocks.properGoodEvent β s n m η κ)ᶜ ∪ E := by
    intro x hx
    by_cases hg : x ∈ GoodBlocks.properGoodEvent β s n m η κ
    · right
      by_contra he
      have hbound (i) : |Y i x| ≤ (n : ℝ) ^ (κ * η) * w i :=
        le_of_not_gt (fun h => he ⟨i,h⟩)
      apply hx
      refine ⟨hg, ?_, ?_⟩
      · intro i
        apply profile_cancel_internal (by positivity) _
          ((le_abs_self _).trans (hbound (Sum.inl i)))
        dsimp only [w, Sum.elim_inl]
        rw [← Real.rpow_add (by positivity : (0 : ℝ) < n + m + 1)]
        simp only [add_neg_cancel, Real.rpow_zero]
      · intro j
        apply profile_cancel_internal (by positivity) _ (hbound (Sum.inr j))
        dsimp only [w, Sum.elim_inr]
        have hδ : (0 : ℝ) < (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) := by
          exact_mod_cast (show 0 < min (j.val + 1) ((n : ℕ) - j.val) by omega)
        rw [mul_mul_mul_comm, mul_inv_cancel₀ (by positivity : ((n : ℝ) + m + 1) ≠ 0),
          ← Real.rpow_add hδ, add_neg_cancel, Real.rpow_zero, one_mul]
    · exact Or.inl hg
  have hbad : μ (GoodBlocks.properGoodEvent β s n m η κ)ᶜ ≤
      ENNReal.ofReal (z⁻¹ * B * Real.exp (-b * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val η)) := by
    have hd₀ := hdom (ofLong β s) rfl hβ.1 hβ.2 n m (by omega) η hεη
    apply (hd₀ _).trans
    rw [Measure.smul_apply, smul_eq_mul]
    apply (mul_le_mul' le_rfl (hbase β hβ n m hhalf (by simp; omega) θ hcurv κ hκ)).trans_eq
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  have hcomp {a t : ℝ} (ha : min b d ≤ a) (ht : GoodBlocks.coefficientTailPower s.val η ≤ t) :
      Real.exp (-a * (n : ℝ) ^ t) ≤
        Real.exp (-min b d * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val η) := by
    apply Real.exp_le_exp.mpr
    have hp := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast n.pos : (1 : ℝ) ≤ n) ht
    have hh := mul_le_mul ha hp (by positivity) ((lt_min hb hdpos).le.trans ha)
    linarith
  apply ((measure_mono hsub).trans (measure_union_le _ _)).trans
  apply (add_le_add hbad hE).trans
  apply (add_le_add
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (hcomp (min_le_left _ _) le_rfl) (by positivity : 0 ≤ z⁻¹ * B)))
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (hcomp (min_le_right _ _) (min_le_right _ _)) hD.le))).trans_eq
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

/-- See Subsection 6.1 and Subsection 6.3 of the paper: the literal diagonal penalty
has a uniform fourth norm whenever the actual inverse-gap fourth norm is
bounded. This internal implication is independent of the exponent regime. -/
private theorem penalty_fourth_norm_internal (θ : PhysicalCutoff) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ (n : ℕ+) (m : ℕ) (ε : ℝ), 0 ≤ ε →
      ∀ (μ : Measure (AffineSimplex.chartDomain n ((n + m : ℕ) + 1))),
      IsProbabilityMeasure μ → ∀ Ci : ℝ, 0 ≤ Ci →
      (∀ i : Fin (n : ℕ), eLpNorm (fun x => (x.val i)⁻¹ ^ 4) 4 μ ≤ ENNReal.ofReal Ci) →
      ∀ i : Fin (n : ℕ), eLpNorm (fun x =>
        |InterpolationMatrix.penaltyHessian n θ ε x.val i i|) 4 μ ≤
          ENNReal.ofReal (Cp * (1 + Ci)) := by
  obtain ⟨Cp, hCp, hpen⟩ := DecayShort.ExceptionalEvent.internal_penalty_diagonal θ
  refine ⟨Cp,hCp,?_⟩
  intro n m ε hε μ hμ Ci hCi hinv i
  let _ := hμ
  have hone : eLpNorm (fun _ : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) => (1 : ℝ))
      4 μ ≤ ENNReal.ofReal 1 := by simp [eLpNorm_const']
  have hmodel := DecayShort.ExceptionalEvent.scale_four_norm_le μ _ hCp.le
    (DecayShort.ExceptionalEvent.add_four_norm_le μ _ _ zero_le_one hCi hone (hinv i))
  apply (eLpNorm_mono_real
    (((InterpolationMatrix.measurable_penaltyHessian n θ ε i i).comp
      measurable_subtype_coe).abs.aestronglyMeasurable) (fun x => ?_)).trans hmodel
  change ‖|InterpolationMatrix.penaltyHessian n θ ε x.val i i|‖ ≤ _
  rw [Real.norm_eq_abs, abs_abs, abs_of_nonneg
    (InterpolationMatrix.penaltyHessian_diagonal_nonneg n θ ε x.val x.property.1 i)]
  have ha : 0 < (n : ℝ) ^ (-ε) := Real.rpow_pos_of_pos (by positivity) _
  have hsm := DecayShort.PhysicalComparison.penalty_contDiffAt n θ ha true x.val x.property.1
  simp only [↓reduceIte] at hsm
  rw [InterpolationMatrix.penaltyHessian,
    DecayShort.PhysicalComparison.hessianMatrix_entry hsm]
  exact hpen n ((n : ℝ) ^ (-ε)) (by positivity)
    (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast n.pos) (by linarith))
    true x.val x.property.1 i

private theorem aggregate_fourth_norm_internal {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (n : ℕ+)
    (F : Fin (n : ℕ) → X → ℝ) (P : Fin (n : ℕ) → Fin (n : ℕ) → X → ℝ)
    (b : Fin (n : ℕ) → X → ℝ) (c : X → ℝ) (a T : ℝ) (hT : 1 ≤ T)
    (hF : ∀ i, eLpNorm (F i) 4 μ ≤ ENNReal.ofReal T)
    (hP : ∀ i j, eLpNorm (P i j) 4 μ ≤ ENNReal.ofReal T)
    (hb : ∀ i, eLpNorm (b i) 4 μ ≤ ENNReal.ofReal T)
    (hc : eLpNorm c 4 μ ≤ ENNReal.ofReal T) :
    eLpNorm (fun x => (n : ℝ) ^ a *
      (1 + (∑ i, F i x) + (∑ i, ∑ j, P i j x) + (∑ i, b i x) + c x)) 4 μ ≤
        ENNReal.ofReal (5 * T * (n : ℝ) ^ (a + 2)) := by
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hone : eLpNorm (fun _ : X => (1 : ℝ)) 4 μ ≤ ENNReal.ofReal 1 := by
    simp [eLpNorm_const']
  have hFs := DecayShort.ExceptionalEvent.sum_four_norm_le μ F hT0 hF
  have hPs := DecayShort.ExceptionalEvent.sum_four_norm_le μ
    (fun i x => ∑ j, P i j x) (by positivity : 0 ≤ (n : ℝ) * T)
    (fun i : Fin (n : ℕ) => by
      simpa only [Fintype.card_fin] using
        DecayShort.ExceptionalEvent.sum_four_norm_le μ (P i) hT0 (hP i))
  have hBs := DecayShort.ExceptionalEvent.sum_four_norm_le μ b hT0 hb
  simp only [Fintype.card_fin] at hFs hPs hBs
  have hsum := DecayShort.ExceptionalEvent.add_four_norm_le μ _ _ (by positivity) hT0
    (DecayShort.ExceptionalEvent.add_four_norm_le μ _ _ (by positivity) (by positivity)
      (DecayShort.ExceptionalEvent.add_four_norm_le μ _ _ (by positivity) (by positivity)
        (DecayShort.ExceptionalEvent.add_four_norm_le μ _ _ zero_le_one (by positivity) hone hFs)
        hPs) hBs) hc
  have hscale := DecayShort.ExceptionalEvent.scale_four_norm_le μ _
    (show 0 ≤ (n : ℝ) ^ a from Real.rpow_nonneg (by positivity) a) hsum
  apply hscale.trans
  apply ENNReal.ofReal_le_ofReal
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  rw [Real.rpow_add (by positivity : (0 : ℝ) < n), Real.rpow_two]
  have hpoly : 1 + (n : ℝ) * T + (n : ℝ) * ((n : ℝ) * T) + (n : ℝ) * T + T ≤
      5 * T * (n : ℝ) ^ 2 := by
    have hn2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hn2 hT0,
      mul_le_mul_of_nonneg_right hnR hT0]
  nlinarith [mul_le_mul_of_nonneg_left hpoly (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n) a)]

set_option backward.isDefEq.respectTransparency true in
/-- See the proof of Lemma 6.5 in the paper: the exact short-range
`W₀` has a polynomial fourth norm under the literal two-sided active law.
The prefactor is uniform in both volumes and on the temperature interval. The same prefactor works for every subsequently selected exponent `C₀`. -/
theorem shortEnvelope_fourth_norm (s : ℝ) (hs : 1 < s)
    (θ : PhysicalCutoff) (ε βlo βhi : ℝ) (hε : 0 < ε)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (n : ℕ+) (m : ℕ),
      2 * (n : ℕ) ≤ (n : ℕ) + m + 1 → ∀ C₀ : ℝ,
      let μ := (activeTiltedGapLaw p ((n : ℕ) + m).succPNat n
        (by simp; omega) θ ε true).comap
          ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
      eLpNorm (shortEnvelope p n m θ ε C₀) 4 μ ≤
        ENNReal.ofReal (C * (n : ℝ) ^ (C₀ + 2)) := by
  obtain ⟨Cp, hCp, hpen⟩ := penalty_fourth_norm_internal θ
  obtain ⟨Ci, hCi, hinv⟩ := DecayShort.ExceptionalEvent.active_inverse_fourth_moments
    s hs θ βlo βhi ε hlo hle hε
  obtain ⟨Cθ, hCθ, hcurv, _⟩ := θ.property.2.2.2.2
  obtain ⟨MP, hMP, hmP⟩ := DecayShort.activeTilt_conditional_P_moments
    s βlo βhi ε Cθ hs hlo hle hε hCθ
  obtain ⟨MB, hMB, hmB⟩ := DecayShort.activeTilt_exterior_contraction_moments
    s βlo βhi ε Cθ hs hlo hle hε hCθ
  let L := (MP + MB) * (4 : ℝ) ^ ((s + 2) / s)
  let T := 1 + Cp * (1 + Ci) + L
  have hL : 0 < L := by dsimp [L]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨5 * T, by positivity, ?_⟩
  intro p hp hpl hph n m hhalf C₀ μ
  let hn : (n : ℕ) ≤ (n : ℕ) + m + 1 := by omega
  have hN : 2 ≤ (n : ℕ) + m + 1 := by have := n.pos; omega
  have : IsProbabilityMeasure μ := DecayShort.activeTilt_proper_probability p n m hn θ ε true
  let A := fun x => DecayShort.conditionalIntervalWeight p n m n.pos (Equiv.refl _) x
  let P := fun (i j : Fin (n : ℕ)) x => IntervalBoundary.intervalMatrix
    ((n : ℕ) + m).succPNat n hn (A x) i j
  let H := fun x => IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat
    ((n : ℕ) + m + 1) le_rfl (A x)
  let S := Finset.univ.filter (fun a : Fin ((n : ℕ) + m + 1) => (n : ℕ) ≤ a.val)
  let b := fun (i : Fin (n : ℕ)) x => (m + 1 : ℝ)⁻¹ * ∑ a ∈ S, H x (Fin.castLE hn i) a
  let c := fun x => (m + 1 : ℝ)⁻¹ ^ 2 * ∑ a ∈ S, ∑ b ∈ S, H x a b
  have hPbound (i j : Fin (n : ℕ)) : eLpNorm (P i j) 4 μ ≤ ENNReal.ofReal T := by
    have hb := hmP p hp hpl hph n m hn θ hcurv true i j 4 (by norm_num)
    norm_num only [ENNReal.ofReal_ofNat] at hb
    apply hb.trans
    apply ENNReal.ofReal_le_ofReal
    have hw := Real.rpow_le_one_of_one_le_of_nonpos
      (le_add_of_nonneg_right (Nat.cast_nonneg
        (Riesz1.cyclicIndexDistance ((n : ℕ) + m).succPNat (Fin.castLE hn i) (Fin.castLE hn j))))
      (show -s ≤ 0 by linarith)
    have hterm := mul_le_of_le_one_right (by positivity : 0 ≤ MP * (4 : ℝ) ^ ((s + 2) / s)) hw
    have hPL : MP * (4 : ℝ) ^ ((s + 2) / s) ≤ L := by
      dsimp only [L]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hLT : L ≤ T := by
      change L ≤ 1 + Cp * (1 + Ci) + L
      linarith [mul_pos hCp (show 0 < 1 + Ci by linarith)]
    exact hterm.trans (hPL.trans hLT)
  have hbcBound (i : Fin (n : ℕ)) : eLpNorm (b i) 4 μ + eLpNorm c 4 μ ≤ ENNReal.ofReal T := by
    have hb := hmB p hp hpl hph n m hn hhalf θ hcurv true 4 (by norm_num) i
    norm_num only [ENNReal.ofReal_ofNat] at hb
    apply hb.trans
    apply ENNReal.ofReal_le_ofReal
    have hdiv := div_le_self (by positivity : 0 ≤ MB * (4 : ℝ) ^ ((s + 2) / s))
      (show (1 : ℝ) ≤ ((n : ℕ) + m + 1 : ℕ) by exact_mod_cast (show 1 ≤ (n : ℕ) + m + 1 by omega))
    have hBL : MB * (4 : ℝ) ^ ((s + 2) / s) ≤ L := by
      dsimp only [L]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hLT : L ≤ T := by
      change L ≤ 1 + Cp * (1 + Ci) + L
      linarith [mul_pos hCp (show 0 < 1 + Ci by linarith)]
    exact hdiv.trans (hBL.trans hLT)
  have hF (i : Fin (n : ℕ)) :
      eLpNorm (fun x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) =>
        |InterpolationMatrix.penaltyHessian n θ ε x.val i i|) 4 μ ≤ ENNReal.ofReal T := by
    apply (hpen n m ε hε.le μ inferInstance Ci hCi.le (fun j =>
      (DecayShort.ExceptionalEvent.internal_retained_inverse_norm p n m hn θ ε true j).trans
        (hinv p hp hpl hph ((n : ℕ) + m).succPNat n hn hN true j.val)) i).trans
    apply ENNReal.ofReal_le_ofReal
    change Cp * (1 + Ci) ≤ 1 + Cp * (1 + Ci) + L
    linarith
  have hB (i : Fin (n : ℕ)) : eLpNorm (b i) 4 μ ≤ ENNReal.ofReal T :=
    (le_add_right le_rfl).trans (hbcBound i)
  have hc : eLpNorm c 4 μ ≤ ENNReal.ofReal T :=
    (le_add_left le_rfl).trans (hbcBound ⟨0,n.pos⟩)
  have hT1 : 1 ≤ T := by
    change 1 ≤ 1 + Cp * (1 + Ci) + L
    linarith [mul_pos hCp (show 0 < 1 + Ci by linarith)]
  exact aggregate_fourth_norm_internal μ n
    (fun i x => |InterpolationMatrix.penaltyHessian n θ ε x.val i i|)
    P b c C₀ T hT1 hF hPbound hB hc

/-- See the proof of Lemma 6.5 in the paper: inverse-gap fourth norms
under the physical two-sided tilt, in both regimes, with a compact-temperature
constant and with no volume-dependent loss. -/
theorem twoSided_inverse_fourth_norm (s ε βlo βhi : ℝ)
    (hs : 0 < s) (hs1 : s ≠ 1) (hε : 0 < ε)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (n : ℕ+) (m : ℕ),
      2 ≤ (n : ℕ) + m + 1 → ∀ i : Fin (n : ℕ),
      eLpNorm (fun x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) => (x.val i)⁻¹ ^ 4) 4
        ((activeTiltedGapLaw p ((n : ℕ) + m).succPNat n (by simp; omega) θ ε true).comap Subtype.val) ≤
          ENNReal.ofReal C := by
  obtain ⟨z, hz, hZ⟩ := InterpolantLocalLaws.compact_tilt_normalizer
    s ε βlo βhi hs hs1 hε hlo hle θ
  obtain ⟨M, hM, hm⟩ := SingleGapTails.single_gap_moments s βlo βhi hs hs1 hlo hle 4 (by norm_num)
  let Z := min z 1
  have hZpos : 0 < Z := lt_min hz zero_lt_one
  let C := Z⁻¹ * (M * ((4 : ℝ) ^ (4 : ℝ) + (4 : ℝ) ^ (4 / s)))
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro p hp hpl hph n m hN i
  let hn : (n : ℕ) ≤ (n : ℕ) + m + 1 := by omega
  let N := ((n : ℕ) + m).succPNat
  have hnorm : ENNReal.ofReal Z ≤ tiltNormalizer p N n hn θ ε true := by
    rw [InterpolatingDensities.normalizer_eq]
    exact ENNReal.ofReal_le_ofReal ((min_le_left z 1).trans (hZ p hp hpl hph N n hN hn))
  have hg := (le_add_left le_rfl).trans (hm p hp hpl hph N hN i.val 4 (by norm_num)).1
  norm_num only [ENNReal.ofReal_ofNat] at hg
  have he (X : Riesz1.Configuration N) : (gap X i.val)⁻¹ ^ 4 = gap X i.val ^ (-(4 : ℝ)) := by
    rw [Real.rpow_neg (show 0 ≤ gap X i.val from (Riesz1.gap_pos X _).le),
      Real.rpow_ofNat, inv_pow]
  simp_rw [← he] at hg
  have ht := DecayShort.internal_activeTilt_norm_le hZpos (min_le_right z 1) hnorm
    (fun X => (gap X i.val)⁻¹ ^ 4) (q := 4) (by norm_num)
  norm_num only [ENNReal.ofReal_ofNat] at ht
  apply (DecayShort.ExceptionalEvent.internal_retained_inverse_norm p n m hn θ ε true i).trans
    (ht.trans ?_)
  apply (mul_le_mul' le_rfl hg).trans_eq
  rw [← ENNReal.ofReal_mul (by positivity)]
  norm_num only [C, Real.rpow_ofNat]

/-- See the proof of Lemma 6.5 in the paper: polynomial fourth norm of
its exact long-range `W₀` under the two-sided marginal. Both physical volumes
and the later choice of `C₀` are quantified after the uniform prefactor. -/
theorem longEnvelope_fourth_norm (s : Riesz1.RieszExponent)
    (θ : PhysicalCutoff) (ε βlo βhi : ℝ) (hε : 0 < ε)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n : ℕ+) (m : ℕ), 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 → ∀ C₀ : ℝ,
      let μ := (activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n
        (by simp; omega) θ ε true).comap
          ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
      eLpNorm (longEnvelope β s n m θ ε C₀) 4 μ ≤
        ENNReal.ofReal (C * (n : ℝ) ^ (C₀ + 2)) := by
  obtain ⟨Cp, hCp, hpen⟩ := penalty_fourth_norm_internal θ
  obtain ⟨Ci, hCi, hinv⟩ := twoSided_inverse_fourth_norm s.val ε βlo βhi
    s.property.1 (by linarith [s.property.2]) hε hlo hle θ
  obtain ⟨Cθ, hCθ, hcurv, _⟩ := θ.property.2.2.2.2
  obtain ⟨MP, hMP, hmP⟩ := GoodBlocks.tilted_conditional_hessian_moments s
    βlo βhi ε Cθ hlo hle hε hCθ
  obtain ⟨MB, hMB, hmB⟩ := long_compensation_moments s ε ε βlo βhi hε le_rfl hlo hle θ
  obtain ⟨z, hz, hz1, hdom⟩ := compact_fine_active_domination s.val ε βlo βhi
    s.property.1 (by linarith [s.property.2]) hε hlo hle θ
  let L := (z⁻¹ * MP + MB) * (4 : ℝ) ^ ((s.val + 2) / s.val)
  let T := 1 + Cp * (1 + Ci) + L
  have hL : 0 < L := by dsimp [L]; positivity
  have hT1 : 1 ≤ T := by
    change 1 ≤ 1 + Cp * (1 + Ci) + L
    linarith [mul_pos hCp (show 0 < 1 + Ci by linarith)]
  refine ⟨5 * T, by positivity, ?_⟩
  intro β hβ n m hhalf C₀ μ
  have hN : 2 ≤ (n : ℕ) + m + 1 := by have := n.pos; omega
  have : IsProbabilityMeasure μ := DecayShort.activeTilt_proper_probability _ _ _ _ _ _ _
  let ν := (activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n
    (by simp; omega) θ ε false).comap
      ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
  have hμν : μ ≤ ENNReal.ofReal z⁻¹ • ν :=
    hdom (ofLong β s) rfl hβ.1 hβ.2 n m hN ε le_rfl
  have hLT : L ≤ T := by
    change L ≤ 1 + Cp * (1 + Ci) + L
    linarith [mul_pos hCp (show 0 < 1 + Ci by linarith)]
  have hP (i j : Fin (n : ℕ)) :
      eLpNorm (GoodBlocks.conditionalHessian β s n m i j) 4 μ ≤ ENNReal.ofReal T := by
    have ht := norm_domination_internal μ ν (GoodBlocks.conditionalHessian β s n m i j)
      hz hz1 (q := 4) (by norm_num) hμν
    have hh := hmP β hβ n m (by simp; omega) θ hcurv i j 4 (by norm_num)
    norm_num only [ENNReal.ofReal_ofNat] at ht hh
    apply (ht.trans (mul_le_mul' le_rfl hh)).trans
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hw := Real.rpow_le_one_of_one_le_of_nonpos
      (le_add_of_nonneg_right (Nat.cast_nonneg
        (Riesz1.cyclicIndexDistance ((n : ℕ) + m).succPNat
          (i.castAdd m).castSucc (j.castAdd m).castSucc)))
      (show -s.val ≤ 0 from neg_nonpos.mpr s.property.1.le)
    have hterm := mul_le_of_le_one_right
      (by positivity : 0 ≤ MP * (4 : ℝ) ^ ((s.val + 2) / s.val)) hw
    have hPL : z⁻¹ * (MP * (4 : ℝ) ^ ((s.val + 2) / s.val)) ≤ L := by
      dsimp only [L]
      nlinarith [mul_pos hMB (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) ((s.val + 2) / s.val))]
    exact (mul_le_mul_of_nonneg_left hterm (by positivity)).trans (hPL.trans hLT)
  have hbc := (hmB β hβ n m hhalf 4 (by norm_num)).1
  norm_num only [ENNReal.ofReal_ofNat] at hbc
  have hbcBound (i : Fin (n : ℕ)) :
      eLpNorm (ConditionalForces.compensationB β s n m i) 4 μ +
        eLpNorm (ConditionalForces.compensationC β s n m) 4 μ ≤ ENNReal.ofReal T := by
    apply (hbc i).trans
    apply ENNReal.ofReal_le_ofReal
    have hw := Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast (show 1 ≤ (n : ℕ) + m + 1 by omega) : (1 : ℝ) ≤ n + m + 1)
      (neg_nonpos.mpr s.property.1.le)
    have hterm := mul_le_of_le_one_right
      (by positivity : 0 ≤ MB * (4 : ℝ) ^ ((s.val + 2) / s.val)) hw
    have hBL : MB * (4 : ℝ) ^ ((s.val + 2) / s.val) ≤ L := by
      dsimp only [L]
      nlinarith [mul_pos (mul_pos (inv_pos.mpr hz) hMP)
        (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 4) ((s.val + 2) / s.val))]
    exact hterm.trans (hBL.trans hLT)
  have hF (i : Fin (n : ℕ)) : eLpNorm (fun x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) =>
      |InterpolationMatrix.penaltyHessian n θ ε x.val i i|) 4 μ ≤ ENNReal.ofReal T := by
    apply (hpen n m ε hε.le μ inferInstance Ci hCi.le
      (hinv (ofLong β s) rfl hβ.1 hβ.2 n m hN) i).trans
    apply ENNReal.ofReal_le_ofReal
    change Cp * (1 + Ci) ≤ 1 + Cp * (1 + Ci) + L
    linarith
  exact aggregate_fourth_norm_internal μ n
    (fun i x => |InterpolationMatrix.penaltyHessian n θ ε x.val i i|)
    (GoodBlocks.conditionalHessian β s n m) (ConditionalForces.compensationB β s n m)
    (ConditionalForces.compensationC β s n m) C₀ T hT1 hF hP
    (fun i => (le_add_right le_rfl).trans (hbcBound i))
    ((le_add_left le_rfl).trans (hbcBound ⟨0,n.pos⟩))

private theorem raw_moment_internal {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (W : X → ℝ) (hW : Measurable W) (hW0 : ∀ x, 0 ≤ W x)
    (k : ℕ) (hk : k ≠ 0) (T : ℝ)
    (hnorm : eLpNorm W (k : ℝ≥0∞) μ ≤ ENNReal.ofReal T) :
    (∫⁻ x, ENNReal.ofReal (W x) ^ k ∂μ) ≤ ENNReal.ofReal T ^ k := by
  have he := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (p := (k : ℝ≥0))
    (show (k : ℝ≥0) ≠ 0 by exact_mod_cast hk) hW.aestronglyMeasurable
  have hw (x) : ‖W x‖ₑ = ENNReal.ofReal (W x) := Real.enorm_eq_ofReal (hW0 x)
  simp only [NNReal.coe_natCast, ENNReal.coe_natCast, ENNReal.rpow_natCast, hw] at he
  rw [← he]
  exact pow_le_pow_left' hnorm k

/-- See the proof of Lemma 6.5 and equation (6.22) of the paper,
long-range case: the exact conditional remainder has exponentially small
first-plus-second moment. The power is independent of the temperature. `C₀` is any fixed nonnegative envelope exponent. -/
theorem long_bad_remainder (hRig : External.LongRangeRigidityLocallyUniform)
    (s : Riesz1.RieszExponent) (ε η C₀ : ℝ) (hε : 0 < ε) (hεη : ε ≤ η)
    (hC₀ : 0 ≤ C₀) (θ : PhysicalCutoff) (βlo βhi : ℝ)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n m : ℕ), 1 ≤ n → 2 * (n + 1) ≤ n + 1 + m + 1 →
      ∀ κ : ℝ, 1 ≤ κ →
      (∫⁻ L, longRemainder β s n m θ ε C₀ η κ L +
        longRemainder β s n m θ ε C₀ η κ L ^ 2
        ∂lengthMeasure (ofLong β s) n m θ ε) ≤ ENNReal.ofReal
          (C * Real.exp (-c * (n + 1 : ℝ) ^ GoodBlocks.coefficientTailPower s.val η)) := by
  have hδ := GoodBlocks.coefficientTailPower_pos s.property.1 s.property.2 (hε.trans_le hεη)
  obtain ⟨M, hM, hm⟩ := longEnvelope_fourth_norm s θ ε βlo βhi hε hlo hle
  obtain ⟨D, c, hD, hc, hp⟩ := long_fine_event_probability hRig s ε η hε hεη θ βlo βhi hlo hle
  obtain ⟨K, hK, hpoly⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := 2 * (C₀ + 2)) hδ (show c / 4 < c / 2 by linarith)
  refine ⟨(M + M ^ 2) * Real.sqrt D * (K + 1), c / 4, by positivity, by positivity, ?_⟩
  intro β hβ n m hn hhalf κ hκ
  let μ := (activeMeasure (ofLong β s) n m θ ε).comap
    ((↑) : AffineSimplex.chartDomain (n+1) (((n+1+m : ℕ) : ℝ)+1) → EuclideanSpace ℝ (Fin (n+1)))
  have : IsProbabilityMeasure μ := DecayShort.activeTilt_proper_probability (ofLong β s) n.succPNat m
    (by simp; omega) θ ε true
  let W := longEnvelope β s n.succPNat m θ ε C₀
  let G := longFineEvent β s n.succPNat m η κ
  have hW : Measurable W := measurable_longEnvelope β s n.succPNat m θ ε C₀
  have hW0 (x) : 0 ≤ W x :=
    (Real.rpow_nonneg (by positivity) C₀).trans (longEnvelope_lower β s n.succPNat m θ ε C₀ x)
  let T := M * (n + 1 : ℝ) ^ (C₀ + 2)
  have hnorm : eLpNorm W 4 μ ≤ ENNReal.ofReal T := by
    simpa only [μ, W, T, activeMeasure, Nat.succPNat, PNat.mk_coe, Nat.succ_eq_add_one, Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using hm β hβ n.succPNat m hhalf C₀
  have hfour := raw_moment_internal μ W hW hW0 4 (by norm_num) T hnorm
  have htwo := raw_moment_internal μ W hW hW0 2 (by norm_num) T
    ((eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (2 : ℝ≥0∞) ≤ 4)).trans hnorm)
  have hprob : μ Gᶜ ≤ ENNReal.ofReal
      (D * Real.exp (-c * (n + 1 : ℝ) ^ GoodBlocks.coefficientTailPower s.val η)) :=
    by simpa only [μ, G, activeMeasure, Nat.succPNat, PNat.mk_coe, Nat.succ_eq_add_one, Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using
      hp β hβ n.succPNat m (by simp only [Nat.succPNat_coe]; omega) hhalf κ hκ
  have hbase := retained_exceptional_moments_le (ofLong β s) n m θ ε hW.ennreal_ofReal
    (measurableSet_longFineEvent β s n.succPNat m η κ)
  have hs₂ : (ENNReal.ofReal T ^ 2) ^ (1 / 2 : ℝ) = ENNReal.ofReal T := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hs₄ : (ENNReal.ofReal T ^ 4) ^ (1 / 2 : ℝ) = ENNReal.ofReal T ^ 2 := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hbound : (∫⁻ L, longRemainder β s n m θ ε C₀ η κ L +
      longRemainder β s n m θ ε C₀ η κ L ^ 2
        ∂lengthMeasure (ofLong β s) n m θ ε) ≤
      (ENNReal.ofReal T + ENNReal.ofReal T ^ 2) * ENNReal.ofReal
        (D * Real.exp (-c * (n + 1 : ℝ) ^ GoodBlocks.coefficientTailPower s.val η)) ^ (1 / 2 : ℝ) := by
    apply hbase.trans
    apply mul_le_mul'
    · exact add_le_add ((ENNReal.rpow_le_rpow htwo (by norm_num)).trans_eq hs₂)
        ((ENNReal.rpow_le_rpow hfour (by norm_num)).trans_eq hs₄)
    · exact ENNReal.rpow_le_rpow hprob (by norm_num)
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have heq : (ENNReal.ofReal T + ENNReal.ofReal T ^ 2) * ENNReal.ofReal
      (D * Real.exp (-c * (n + 1 : ℝ) ^ GoodBlocks.coefficientTailPower s.val η)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal ((T + T ^ 2) * Real.sqrt D *
        Real.exp (-(c / 2) * (n + 1 : ℝ) ^ GoodBlocks.coefficientTailPower s.val η)) := by
    rw [← ENNReal.ofReal_pow hT0, ← ENNReal.ofReal_add hT0 (sq_nonneg _),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      ← ENNReal.ofReal_mul (by positivity), Real.mul_rpow hD.le (Real.exp_pos _).le,
      ← Real.exp_mul, ← Real.sqrt_eq_rpow]
    congr 1
    rw [show (-c * (n + 1 : ℝ) ^ GoodBlocks.coefficientTailPower s.val η) * (1 / 2) =
      -(c / 2) * (n + 1 : ℝ) ^ GoodBlocks.coefficientTailPower s.val η by ring]
    ring
  refine (hbound.trans_eq heq).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hnR : (1 : ℝ) ≤ n + 1 := by have := Nat.cast_nonneg n (α := ℝ); linarith
  have hsmall : T + T ^ 2 ≤ (M + M ^ 2) * (n + 1 : ℝ) ^ (2 * (C₀ + 2)) := by
    have ha : (n + 1 : ℝ) ^ (C₀ + 2) ≤ (n + 1 : ℝ) ^ (2 * (C₀ + 2)) :=
      Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
    have hpow : T ^ 2 = M ^ 2 * (n + 1 : ℝ) ^ (2 * (C₀ + 2)) := by
      have hp : ((n + 1 : ℝ) ^ (C₀ + 2)) ^ 2 = (n + 1 : ℝ) ^ (2 * (C₀ + 2)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1
        push_cast
        ring
      dsimp only [T]
      rw [mul_pow, hp]
    rw [hpow]
    dsimp only [T]
    nlinarith [mul_le_mul_of_nonneg_left ha hM.le]
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hsmall (Real.sqrt_nonneg D))
      (Real.exp_pos (-(c / 2) * (n + 1 : ℝ) ^ GoodBlocks.coefficientTailPower s.val η)).le
  have habsorb := hpoly (n + 1 : ℝ) hnR
  calc
    _ ≤ (M + M ^ 2) * Real.sqrt D *
        ((n + 1 : ℝ) ^ (2 * (C₀ + 2)) *
          Real.exp (-(c / 2) * (n + 1 : ℝ) ^ GoodBlocks.coefficientTailPower s.val η)) := by
      nlinarith only [hh]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left habsorb
        (by positivity : 0 ≤ (M + M ^ 2) * Real.sqrt D)
      nlinarith [mul_nonneg (by positivity : 0 ≤ (M + M ^ 2) * Real.sqrt D)
        (Real.exp_pos (-(c / 4) * (n + 1 : ℝ) ^ GoodBlocks.coefficientTailPower s.val η)).le]

/-- See the proof of Lemma 6.5 in the paper: the exact long-range
conditional remainder is finite on almost every physical length. This is
proved before any possible real-valued conversion of that remainder. -/
theorem longRemainder_finite_ae (hRig : External.LongRangeRigidityLocallyUniform)
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (n m : ℕ)
    (θ : PhysicalCutoff) (ε η C₀ κ : ℝ) (hε : 0 < ε) (hεη : ε ≤ η)
    (hC₀ : 0 ≤ C₀) (hκ : 1 ≤ κ) (hn : 1 ≤ n)
    (hhalf : 2 * (n + 1) ≤ n + 1 + m + 1) :
    ∀ᵐ L ∂lengthMeasure (ofLong β s) n m θ ε,
      longRemainder β s n m θ ε C₀ η κ L < ∞ := by
  obtain ⟨C, c, _, _, hb⟩ := long_bad_remainder hRig s ε η C₀ hε hεη hC₀
    θ β.val β.val β.property le_rfl
  have hbound := hb β ⟨le_rfl,le_rfl⟩ n m hn hhalf κ hκ
  have hlt : (∫⁻ L, longRemainder β s n m θ ε C₀ η κ L ^ 2
      ∂lengthMeasure (ofLong β s) n m θ ε) < ∞ := by
    apply (lintegral_mono (fun L => le_add_left le_rfl)).trans_lt
    exact hbound.trans_lt ENNReal.ofReal_lt_top
  have ha := ae_lt_top ((measurable_longRemainder β s n m θ ε C₀ η κ).pow_const 2) hlt.ne
  filter_upwards [ha] with L hL
  by_contra! ht
  have he : longRemainder β s n m θ ε C₀ η κ L = ∞ := top_unique ht
  simp only [he, ENNReal.top_pow (by norm_num : 2 ≠ 0), lt_self_iff_false] at hL

end Riesz2.LengthAveragingFibres
