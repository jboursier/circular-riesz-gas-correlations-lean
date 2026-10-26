/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib
public import Riesz1.Gibbs.WellDefined
public import Riesz2.Frozen.BlockObservable
public import Riesz2.Frozen.ConvergesInLawAlong
public import Riesz2.Frozen.GapObservable
public import Riesz2.Frozen.GapSecondMoments
public import Riesz2.Frozen.HasIntensity
public import Riesz2.Frozen.InverseTemperature
public import Riesz2.Frozen.IsMesoscopicSequence
public import Riesz2.Frozen.IsStationary
public import Riesz2.Frozen.LineConfiguration
public import Riesz2.Frozen.LocalConverges
public import Riesz2.Frozen.OffLattice
public import Riesz2.Frozen.OrderedPointDomain
public import Riesz2.Frozen.PalmRegular
public import Riesz2.Frozen.Parameters
public import Riesz2.Frozen.PointProcess
public import Riesz2.Frozen.RootedConfiguration
public import Riesz2.Frozen.ShortExponent
public import Riesz2.Frozen.UniqueRieszLimit
public import Riesz2.Frozen.BlockDerivativeNorm
public import Riesz2.Frozen.ConfigurationMeasurableSpace
public import Riesz2.Frozen.ConfigurationMeasure
public import Riesz2.Frozen.ConvergenceRate
public import Riesz2.Frozen.CoordinateDerivativeNorm
public import Riesz2.Frozen.CorrelationFactor
public import Riesz2.Frozen.Count
public import Riesz2.Frozen.DerivativeSup
public import Riesz2.Frozen.Energy
public import Riesz2.Frozen.ExponentA
public import Riesz2.Frozen.ExponentB
public import Riesz2.Frozen.FiniteGapBlock
public import Riesz2.Frozen.Gap
public import Riesz2.Frozen.GapCorrelation
public import Riesz2.Frozen.GapDerivativeNorm
public import Riesz2.Frozen.GapLaw
public import Riesz2.Frozen.GapVector
public import Riesz2.Frozen.GibbsMeasure
public import Riesz2.Frozen.HyperuniformityRatio
public import Riesz2.Frozen.IntervalCount
public import Riesz2.Frozen.LimitingRieszProcess
public import Riesz2.Frozen.LongParameters
public import Riesz2.Frozen.MicroscopicConfiguration
public import Riesz2.Frozen.MicroscopicLaw
public import Riesz2.Frozen.NumberVariance
public import Riesz2.Frozen.OfLong
public import Riesz2.Frozen.OfShort
public import Riesz2.Frozen.OrderedPoint
public import Riesz2.Frozen.PalmKernel
public import Riesz2.Frozen.PalmMeasure
public import Riesz2.Frozen.PalmSpanVariance
public import Riesz2.Frozen.RepulsionProbability
public import Riesz2.Frozen.RestrictConfiguration
public import Riesz2.Frozen.RootedConfigurations
public import Riesz2.Frozen.RootedGap
public import Riesz2.Frozen.RootedGapBlock
public import Riesz2.Frozen.RootedPalmMeasure
public import Riesz2.Frozen.RootedPoint
public import Riesz2.Frozen.ShortEnergy
public import Riesz2.Frozen.ShortGibbsMeasure
public import Riesz2.Frozen.ShortGibbsWeight
public import Riesz2.Frozen.ShortKernel
public import Riesz2.Frozen.ShortKernelLift
public import Riesz2.Frozen.ShortPartitionFunction
public import Riesz2.Frozen.TotalVariation
public import Riesz2.Frozen.TranslateConfiguration
public import Riesz2.Sanity.PalmMeasurability
public import Riesz1.Frozen.ConvergesInLaw



/-!
# Checks for finite laws and point-process definitions

Normalization, sign, short-range series and counting-variance checks for the
finite laws and point-process definitions, including Campbell normalization.
-/

public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2.FrozenSanity

local instance : MeasurableSpace LineConfiguration := configurationMeasurableSpace

/-- The defining short-range series converges (Subsection 1.1). -/
lemma shortKernelLift_summable (s : ShortExponent) (x : OffLattice) :
    Summable (fun k : ℤ => 1 / |(k : ℝ) + x.val| ^ s.val) :=
  (Real.summable_one_div_int_add_rpow x.val s.val).mpr s.property

/-- The short-range kernel is nonnegative (Subsection 1.1). -/
lemma shortKernelLift_nonneg (s : ShortExponent) (x : OffLattice) :
    0 ≤ shortKernelLift s x :=
  tsum_nonneg (fun _ => div_nonneg zero_le_one (Real.rpow_nonneg (abs_nonneg _) _))

/-- Strict positivity is witnessed by the zero image (Subsection 1.1). -/
lemma shortKernelLift_pos (s : ShortExponent) (x : OffLattice) :
    0 < shortKernelLift s x := by
  have hx : x.val ≠ 0 := by
    intro h
    exact x.property (by simp [h])
  exact (shortKernelLift_summable s x).tsum_pos
    (fun _ => div_nonneg zero_le_one (Real.rpow_nonneg (abs_nonneg _) _)) 0
    (by simpa using one_div_pos.mpr (Real.rpow_pos_of_pos (abs_pos.mpr hx) s.val))

/-- Algebraic image reindexing, used only off collisions by the kernel definitions. -/
lemma imageSum_neg (s x : ℝ) :
    (∑' k : ℤ, 1 / |(k : ℝ) + -x| ^ s) = ∑' k : ℤ, 1 / |(k : ℝ) + x| ^ s := by
  calc
    _ = ∑' k : ℤ, 1 / |((-k : ℤ) : ℝ) + -x| ^ s :=
      ((Equiv.neg ℤ).tsum_eq _).symm
    _ = _ := tsum_congr (fun k => by
      rw [Int.cast_neg, show -(k : ℝ) + -x = -((k : ℝ) + x) by ring, abs_neg])

/-- Algebraic periodicity of the image sum. -/
lemma imageSum_add_int (s x : ℝ) (n : ℤ) :
    (∑' k : ℤ, 1 / |(k : ℝ) + (x + n)| ^ s) =
      ∑' k : ℤ, 1 / |(k : ℝ) + x| ^ s := by
  calc
    _ = ∑' k : ℤ, 1 / |((k + n : ℤ) : ℝ) + x| ^ s :=
      tsum_congr (fun k => by congr 3; push_cast; ring)
    _ = _ := (Equiv.addRight n).tsum_eq (fun k : ℤ => 1 / |(k : ℝ) + x| ^ s)

/-- Evenness on real lifts (Subsection 1.1). -/
lemma shortKernelLift_even (s : ShortExponent) (x : OffLattice) :
    shortKernelLift s ⟨-x.val, by simpa using x.property⟩ = shortKernelLift s x :=
  imageSum_neg s.val x.val

/-- The selected representative still represents the same circle point. -/
lemma centralRep_cast (x : UnitAddCircle) :
    ((Riesz1.centralRep Riesz1.unitLength x : ℝ) : UnitAddCircle) = x := by
  have : Fact (0 < Riesz1.unitLength.val) := ⟨Riesz1.unitLength.property⟩
  exact AddCircle.coe_equivIco

/-- Evenness of the actual short-range circle kernel (Subsection 1.1). -/
lemma shortKernel_even (s : ShortExponent) (x : {x : UnitAddCircle // x ≠ 0}) :
    shortKernel s ⟨-x.val, neg_ne_zero.mpr x.property⟩ = shortKernel s x := by
  have hz : (((Riesz1.centralRep Riesz1.unitLength (-x.val) +
      Riesz1.centralRep Riesz1.unitLength x.val : ℝ)) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_add, centralRep_cast, centralRep_cast, neg_add_cancel]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
  rw [zsmul_eq_mul, mul_one] at hn
  have he : Riesz1.centralRep Riesz1.unitLength (-x.val) =
      -Riesz1.centralRep Riesz1.unitLength x.val + n := by linarith
  unfold shortKernel
  rw [he, imageSum_add_int, imageSum_neg]

/-- Strict positivity of the circle kernel (Subsection 1.1). -/
lemma shortKernel_pos (s : ShortExponent) (x : {x : UnitAddCircle // x ≠ 0}) :
    0 < shortKernel s x :=
  shortKernelLift_pos s ⟨Riesz1.centralRep Riesz1.unitLength x.val, by
    rw [centralRep_cast]
    exact x.property⟩

/-- The singular image is bounded by the kernel, with no collision evaluation. -/
lemma singularTerm_le_shortKernelLift (s : ShortExponent) (x : OffLattice) :
    1 / |x.val| ^ s.val ≤ shortKernelLift s x := by
  simpa [shortKernelLift] using (shortKernelLift_summable s x).le_tsum 0
    (fun k _ => div_nonneg zero_le_one (Real.rpow_nonneg (abs_nonneg _) _))

/-- For compact-set comparisons, a distant image is at most
`2^s |k|^(-s)`. A periodic kernel itself cannot decay at spatial infinity. -/
lemma shortImage_decay (s : ShortExponent) (x : ℝ) (k : ℤ)
    (hk : k ≠ 0) (hfar : 2 * |x| ≤ |(k : ℝ)|) :
    1 / |(k : ℝ) + x| ^ s.val ≤ 2 ^ s.val / |(k : ℝ)| ^ s.val := by
  have hkpos : 0 < |(k : ℝ)| := abs_pos.mpr (by exact_mod_cast hk)
  have htri : |(k : ℝ)| ≤ |(k : ℝ) + x| + |x| := by
    calc
      |(k : ℝ)| = |((k : ℝ) + x) + -x| := by congr 1; ring
      _ ≤ |(k : ℝ) + x| + |-x| := abs_add_le _ _
      _ = _ := by rw [abs_neg]
  have hbase : |(k : ℝ)| / 2 ≤ |(k : ℝ) + x| := by linarith
  calc
    _ ≤ 1 / (|(k : ℝ)| / 2) ^ s.val :=
      one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by positivity) _)
        (Real.rpow_le_rpow (by positivity) hbase (by linarith [s.property]))
    _ = _ := by rw [Real.div_rpow (abs_nonneg _) (by norm_num), one_div_div]

/-- The short-range energy is nonnegative, including the empty sum for one particle. -/
lemma shortEnergy_nonneg (s : ShortExponent) {N : ℕ+} (X : Riesz1.Configuration N) :
    0 ≤ shortEnergy s X := by
  unfold shortEnergy
  apply mul_nonneg (Real.rpow_nonneg (by positivity) _)
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => shortKernelLift_nonneg _ _

/-- Measurability of the finite energy, without a smoothness assumption. -/
lemma measurable_shortEnergy (s : ShortExponent) (N : ℕ+) :
    Measurable (@shortEnergy s N) := by
  unfold shortEnergy
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  change Measurable (fun X : Riesz1.Configuration N =>
    ∑' k : ℤ, 1 / |(k : ℝ) + (X.val i - X.val j.val)| ^ s.val)
  apply Measurable.tsum
  intro k
  have hcoord (i : Fin (N : ℕ)) : Measurable (fun X : Riesz1.Configuration N => X.val i) :=
    (measurable_pi_apply i).comp measurable_subtype_coe
  exact measurable_const.div
    ((measurable_const.add ((hcoord i).sub (hcoord j.val))).abs.pow_const s.val)

/-- Measurability of the short-range density. -/
lemma measurable_shortDensity (β : InverseTemperature) (s : ShortExponent) (N : ℕ+) :
    Measurable (fun X : Riesz1.Configuration N =>
      ENNReal.ofReal (Real.exp (-β.val * shortEnergy s X))) := by
  have hE := measurable_shortEnergy s N
  fun_prop

/-- The short-range partition is a positive finite extended integral, for all sizes. -/
lemma shortPartitionFunction_valid (β : InverseTemperature) (s : ShortExponent) (N : ℕ+) :
    0 < shortPartitionFunction β s N ∧ shortPartitionFunction β s N < ⊤ := by
  have hint : shortPartitionFunction β s N =
      ∫⁻ X : Riesz1.Configuration N,
        ENNReal.ofReal (Real.exp (-β.val * shortEnergy s X)) ∂Riesz1.configurationVolume N := by
    simp [shortPartitionFunction, shortGibbsWeight, withDensity_apply]
  have hv : 0 < Riesz1.configurationVolume N univ := by
    rw [Riesz1.configurationVolume_univ]
    positivity
  have hsupport : Function.support (fun X : Riesz1.Configuration N =>
      ENNReal.ofReal (Real.exp (-β.val * shortEnergy s X))) = univ := by
    ext X
    simp [Real.exp_pos]
  constructor
  · rw [hint, lintegral_pos_iff_support (measurable_shortDensity β s N), hsupport]
    exact hv
  · rw [hint]
    calc
      _ ≤ ∫⁻ _ : Riesz1.Configuration N, (1 : ℝ≥0∞) ∂Riesz1.configurationVolume N := by
        apply lintegral_mono
        intro X
        exact ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr β.property.le) (shortEnergy_nonneg s X)))
      _ < ⊤ := by simp [Riesz1.configurationVolume_univ]

/-- Required normalization check: in particular it holds for every `N≥2`. -/
lemma shortGibbsMeasure_probability (β : InverseTemperature) (s : ShortExponent) (N : ℕ+) :
    IsProbabilityMeasure (shortGibbsMeasure β s N) := by
  obtain ⟨hpos, hfinite⟩ := shortPartitionFunction_valid β s N
  apply isProbabilityMeasure_iff.mpr
  change ((shortPartitionFunction β s N)⁻¹ • shortGibbsWeight β s N) univ = 1
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hpos.ne' hfinite.ne

/-- Both regimes give probability laws, using the library proof in long range. -/
lemma gibbsMeasure_probability (p : Parameters) (N : ℕ+) :
    IsProbabilityMeasure (gibbsMeasure p N) := by
  unfold gibbsMeasure
  split_ifs with h
  · exact (Riesz1.modelWellDefined ⟨p.val, p.property.1, p.property.2.1, h⟩ N).2.2
  · exact shortGibbsMeasure_probability _ _ _

/-- Long-range Gibbs reuse is literal equality, with no translation of temperatures. -/
lemma gibbsMeasure_ofLong (β : InverseTemperature) (s : Riesz1.RieszExponent) (N : ℕ+) :
    gibbsMeasure (ofLong β s) N = Riesz1.gibbsMeasure (longParameters β s) N := by
  simp [gibbsMeasure, ofLong, longParameters, s.property.2]

/-- Least coordinate derivative bounds are taken over a nonempty set. No empty-infimum
value occurs in `coordinateDerivativeNorm` (Theorem 4). -/
lemma coordinateDerivativeBounds_nonempty {K : ℕ+} (G : BlockObservable K)
    (j : Fin (K : ℕ)) :
    {L : ℝ≥0 | ∀ (x : Fin (K : ℕ) → ℝ) (t : ℝ),
      |G.val (Function.update x j t) - G.val x| ≤ (L : ℝ) * |t - x j|}.Nonempty := by
  obtain ⟨L, hL⟩ := G.property
  refine ⟨L, fun x t => ?_⟩
  have hd : dist (Function.update x j t) x ≤ |t - x j| := by
    apply (dist_pi_le_iff (abs_nonneg _)).mpr
    intro k
    by_cases hk : k = j
    · subst k
      simp [Real.dist_eq]
    · simp [Function.update_of_ne hk, abs_nonneg]
  exact (hL.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left hd L.property)

/-- Independent square-integrable observables have zero gap correlation. -/
lemma gapCorrelation_eq_zero_of_independent (p : Parameters) (N : ℕ+) (i j : ℤ)
    (f g : ℝ → ℝ)
    (hind : ProbabilityTheory.IndepFun (fun X => f (Riesz2.gap X i))
      (fun X => g (Riesz2.gap X j)) (gibbsMeasure p N))
    (hf : MemLp (fun X => f (Riesz2.gap X i)) 2 (gibbsMeasure p N))
    (hg : MemLp (fun X => g (Riesz2.gap X j)) 2 (gibbsMeasure p N)) :
    gapCorrelation p N i j f g hf hg = 0 :=
  hind.covariance_eq_zero hf hg

/-- Bounded counts are finite integers. -/
lemma intervalCount_finite (C : LineConfiguration) (a b : ℝ) :
    count C (Ioc a b) < ⊤ := by
  have hf : (C.val ∩ Ioc a b).Finite := (C.property a b).subset (by
    intro x hx
    exact ⟨hx.1, hx.2.1.le, hx.2.2⟩)
  unfold count
  rw [← hf.cast_ncard_eq]
  simp

/-- In particular interval counts are measurable real variables. -/
lemma measurable_intervalCount (a b : ℝ) : Measurable (intervalCount a b) :=
  ENNReal.measurable_toReal.comp (measurable_count _ measurableSet_Ioc (Metric.isBounded_Ioc a b))

/-- The Campbell kernel has exactly one unit of mass per atom in the rooting window. -/
lemma palmKernel_univ (C : LineConfiguration) : palmKernel C univ = count C (Ico 0 1) := by
  unfold palmKernel count
  rw [Measure.sum_apply _ MeasurableSet.univ]
  simp only [measure_univ]
  rw [ENNReal.tsum_one]
  exact congrArg (fun n : ℕ∞ => (n : ℝ≥0∞)) (ENat.card_coe_set_eq (C.val ∩ Ico 0 1))

/-- Intensity one normalizes the Campbell measure. Stationarity identifies it as the Palm law. -/
lemma palmMeasure_probability (P : PointProcess) (hI : HasIntensity P 1) :
    IsProbabilityMeasure (palmMeasure P) := by
  apply isProbabilityMeasure_iff.mpr
  rw [palmMeasure, Measure.bind_apply MeasurableSet.univ measurable_palmKernel.aemeasurable]
  simp_rw [palmKernel_univ]
  simpa using hI (Ico 0 1) measurableSet_Ico (Metric.isBounded_Ico 0 1)

/-- Event-supremum TV is zero on identical finite laws, without choosing an ENNReal metric. -/
lemma totalVariation_self {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] :
    totalVariation μ μ = 0 := by simp [totalVariation]

/-- Two disjoint point masses have TV one, checking the paper's half-L¹ normalization. -/
lemma totalVariation_dirac_zero_one :
    totalVariation (Measure.dirac (0 : ℝ)) (Measure.dirac 1) = 1 := by
  apply le_antisymm
  · apply iSup_le
    intro A
    by_cases h0 : (0 : ℝ) ∈ A.val <;> by_cases h1 : (1 : ℝ) ∈ A.val <;>
      simp [h0, h1]
  · apply le_iSup_of_le ⟨{0}, measurableSet_singleton 0⟩
    norm_num [Measure.dirac_apply' _ (measurableSet_singleton 0)]

/-- The integer lattice is a simple locally finite configuration
(Subsection 1.5). -/
def latticeConfiguration : LineConfiguration :=
  ⟨range (fun k : ℤ => (k : ℝ)), fun a b =>
    ((Set.finite_Icc (⌈a⌉ : ℤ) ⌊b⌋).image (fun k : ℤ => (k : ℝ))).subset (by
      rintro x ⟨⟨k, rfl⟩, ha, hb⟩
      exact ⟨k, ⟨Int.ceil_le.mpr ha, Int.le_floor.mpr hb⟩, rfl⟩)⟩

/-- A unit half-open interval contains exactly one integer lattice point. -/
lemma lattice_intervalCount_one : intervalCount 0 1 latticeConfiguration = 1 := by
  have he : latticeConfiguration.val ∩ Ioc (0 : ℝ) 1 = {1} := by
    ext x
    constructor
    · rintro ⟨⟨k, rfl⟩, ha, hb⟩
      change (0 : ℝ) < (k : ℝ) at ha
      change (k : ℝ) ≤ 1 at hb
      have hk0 : 0 < k := by exact_mod_cast ha
      have hk1 : k ≤ 1 := by exact_mod_cast hb
      have hk : k = 1 := by omega
      simp [hk]
    · intro hx
      have hx1 : x = 1 := hx
      subst x
      exact ⟨⟨1, by norm_num⟩, by norm_num, le_rfl⟩
  simp [intervalCount, count, he]

/-- Required lattice check: a fixed lattice configuration has deterministic counts,
so its variance-to-length ratio is exactly zero for every positive length. -/
lemma lattice_hyperuniformityRatio (R : {R : ℝ // 0 < R}) :
    let P : PointProcess := ⟨Measure.dirac latticeConfiguration, inferInstance⟩
    ∃ h : Integrable (intervalCount 0 R.val) (P : Measure LineConfiguration),
      hyperuniformityRatio P R h = 0 := by
  dsimp only
  have hm := measurable_intervalCount 0 R.val
  have hi : Integrable (intervalCount 0 R.val) (Measure.dirac latticeConfiguration) :=
    integrable_dirac' hm.stronglyMeasurable (by finiteness)
  refine ⟨hi, ?_⟩
  unfold hyperuniformityRatio numberVariance Riesz1.variance
  change (∫⁻ C, ENNReal.ofReal ((intervalCount 0 R.val C -
    ∫ D, intervalCount 0 R.val D ∂Measure.dirac latticeConfiguration) ^ 2)
      ∂Measure.dirac latticeConfiguration) / ENNReal.ofReal R.val = 0
  rw [integral_dirac' _ _ hm.stronglyMeasurable]
  have hz : (∫⁻ C, ENNReal.ofReal ((intervalCount 0 R.val C -
      intervalCount 0 R.val latticeConfiguration) ^ 2) ∂Measure.dirac latticeConfiguration) = 0 := by
    rw [lintegral_dirac' _ (by fun_prop)]
    simp
  rw [hz, ENNReal.zero_div]

/-- Integer and real-indexed bounded-continuous-test conventions agree exactly. -/
lemma convergesInLawAlong_nat_iff (laws : ℕ → Measure ℝ) (limit : Measure ℝ) :
    ConvergesInLawAlong atTop laws limit ↔ Riesz1.ConvergesInLaw laws limit := Iff.rfl

/-- The rooted enumeration fixes zero by definition. -/
lemma rootedPoint_zero (C : RootedConfiguration) : rootedPoint C 0 = 0 := by
  simp [rootedPoint]

/-- The rate exponent is positive throughout both admissible regimes. -/
lemma convergenceRate_pos {s : ℝ} (hs : 0 < s) : 0 < convergenceRate s := by
  unfold convergenceRate exponentA exponentB
  exact mul_pos (lt_min (by positivity) zero_lt_one)
    (div_pos (lt_min hs zero_lt_one) (by norm_num))

/-- At s=1/2 the long-range rate is s²/4=1/16. -/
lemma convergenceRate_one_half : convergenceRate (1 / 2) = 1 / 16 := by
  norm_num [convergenceRate, exponentA, exponentB]

/-- The short-range crossover at s=2 is included and has rate 1/2. -/
lemma convergenceRate_two : convergenceRate 2 = 1 / 2 := by
  norm_num [convergenceRate, exponentA, exponentB]

/-- Increasing s beyond 2 leaves the stated short-range rate at 1/2. -/
lemma convergenceRate_three : convergenceRate 3 = 1 / 2 := by
  norm_num [convergenceRate, exponentA, exponentB]

end Riesz2.FrozenSanity
