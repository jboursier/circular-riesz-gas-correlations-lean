/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Kernel.MeasurableLIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
public import Mathlib.Data.Nat.Dist

/-!
# Theorem 2 (Short-range gap correlations): the definitions

The definitions in this file specify the short-range Gibbs law, cyclic gaps, observables and
covariance factors, and are shared by the challenge and solution.

The definitions below are copied without change, in dependency order, from the files
`Riesz2/Frozen/*.lean` of the library and from `Riesz1/Frozen/*.lean` of the companion
library, inside the namespace `Riesz2Audit.ShortRangeGapCorrelations`. For example, `Riesz2.gibbsMeasure` of the
library is `Riesz2Audit.ShortRangeGapCorrelations.Riesz2.gibbsMeasure` here. This file imports Mathlib only.
-/

@[expose] public section

namespace Riesz2Audit.ShortRangeGapCorrelations

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Cyclic distance between labels. -/
def cyclicIndexDistance (N : ℕ+) (i j : Fin (N : ℕ)) : ℕ :=
  min (Nat.dist i.val j.val) ((N : ℕ) - Nat.dist i.val j.val)


end Riesz1

end


noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- A Lipschitz function ξ : ℝ → ℝ with a measurable representative of its almost-everywhere
derivative ξ'. This encodes the locally absolutely continuous observables with bounded
derivatives in Theorems 1 and 2. -/
@[reducible] def GapObservable :=
  {f : (ℝ → ℝ) × (ℝ → ℝ) //
    (∃ L : ℝ≥0, LipschitzWith L f.1) ∧ AEStronglyMeasurable f.2 volume ∧
    (∀ᵐ x ∂volume, HasDerivAt f.1 (f.2 x) x) ∧ eLpNorm f.2 ∞ volume < ⊤}

end Riesz2

end


noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The parameters (β,s) with β > 0, s > 0 and s ≠ 1, covering both regimes of Subsection 1.1. -/
@[reducible] def Parameters := {p : ℝ × ℝ // 0 < p.1 ∧ 0 < p.2 ∧ p.2 ≠ 1}

end Riesz2

end


noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Ordered lift domain in a fundamental region. -/
def orderedDomain (N : ℕ+) : Set (Fin (N : ℕ) → ℝ) :=
  {x | StrictMono x ∧ 0 ≤ x ⟨0, N.pos⟩ ∧ x ⟨0, N.pos⟩ < 1 ∧
    ∀ i, x i < x ⟨0, N.pos⟩ + 1}


end Riesz1

end


noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Configurations, with unique first lift in [0,1). -/
@[reducible] def Configuration (N : ℕ+) := orderedDomain N


end Riesz1

end


noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- The cyclic lift `x_{j+N} = x_j + 1` of a configuration, for every integer label `j`, computed by
Euclidean division of `j` by `N`. Labels start at zero, so the paper's `x_1` is `cyclicLift X 0`. -/
def cyclicLift {N : ℕ+} (X : Configuration N) (j : ℤ) : ℝ :=
  X.val ⟨(j % (N : ℕ)).toNat, by
    have h := Int.emod_lt_of_pos j (show (0 : ℤ) < (N : ℕ) by exact_mod_cast N.pos)
    exact_mod_cast (Int.toNat_lt (Int.emod_nonneg j (by exact_mod_cast N.ne_zero))).mpr h⟩ +
      (j / (N : ℕ) : ℤ)


end Riesz1

end


noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The microscopic gap N(x_{j+1}−x_j), using the cyclic lifts of `Riesz1`. See Subsection 1.3.
This agrees definitionally with the companion formalization's gap. -/
def gap {N : ℕ+} (X : Riesz1.Configuration N) (j : ℤ) : ℝ :=
  (N : ℝ) * (Riesz1.cyclicLift X (j + 1) - Riesz1.cyclicLift X j)

end Riesz2

end


noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Model parameters. -/
@[reducible] def Parameters : Type :=
  {x : ℝ × ℝ // 0 < x.1 ∧ 0 < x.2 ∧ x.2 < 1}

end Riesz1

end


noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- The range for a Riesz exponent. -/
@[reducible] def RieszExponent := {s : ℝ // 0 < s ∧ s < 1}


end Riesz1

end


noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- The model exponent with its range proofs. -/
def parametersExponent (P : Parameters) : RieszExponent := ⟨P.val.2, P.property.2.1, P.property.2.2⟩


end Riesz1

end


noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Canonical analytic representative, twice Mathlib's even Hurwitz function.
The kernel of the paper is its restriction to x ≠ 0.
The Mathlib value at 0 is an analytic continuation with the collision term omitted. -/
def rieszRepresentative (s : RieszExponent) (x : UnitAddCircle) : ℝ :=
  2 * (HurwitzZeta.hurwitzZetaEven x (s.val : ℂ)).re


end Riesz1

end


noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Energy, ordered pairs counted twice. -/
def energy (s : RieszExponent) {N : ℕ+} (X : Configuration N) : ℝ :=
  (N : ℝ) ^ (-s.val) *
    ∑ i : Fin (N : ℕ), ∑ j ∈ Finset.univ.erase i,
      rieszRepresentative s ((X.val i - X.val j : ℝ) : UnitAddCircle)


end Riesz1

end


noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Lebesgue measure pulled back to the lift domain. -/
def configurationVolume (N : ℕ+) : Measure (Configuration N) :=
  (volume : Measure (Fin (N : ℕ) → ℝ)).comap Subtype.val


end Riesz1

end


noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Unnormalized Gibbs measure. -/
def gibbsWeight (P : Parameters) (N : ℕ+) : Measure (Configuration N) :=
  (configurationVolume N).withDensity (fun X => ENNReal.ofReal (Real.exp (-P.val.1 * energy (parametersExponent P) X)))


end Riesz1

end


noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Extended nonnegative partition function. -/
def partitionFunction (P : Parameters) (N : ℕ+) : ℝ≥0∞ := gibbsWeight P N Set.univ


end Riesz1

end


noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Gibbs law. Finiteness and positivity are separate analytic obligations,
never taken as hypotheses. -/
def gibbsMeasure (P : Parameters) (N : ℕ+) : Measure (Configuration N) :=
  (partitionFunction P N)⁻¹ • gibbsWeight P N


end Riesz1

end


noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The inverse temperature β > 0 of Subsection 1.1. -/
@[reducible] def InverseTemperature := {β : ℝ // 0 < β}

end Riesz2

end


noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The exponent s > 1 of Subsection 1.1. The companion type `Riesz1.RieszExponent` covers 0 < s
< 1. -/
@[reducible] def ShortExponent := {s : ℝ // 1 < s}

end Riesz2

end


noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- Real numbers whose image in the unit circle is nonzero. These are the lifts away from the
collision lattice ℤ on which the kernel of Subsection 1.1 is evaluated. -/
@[reducible] def OffLattice := {x : ℝ // (x : UnitAddCircle) ≠ 0}

end Riesz2

end


noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The absolutely convergent sum g_s(x) = ∑_{k ∈ ℤ}|x+k|^{-s} for s > 1 and x ∉ ℤ. This is the
short-range kernel of equation (1.1), without mean subtraction. -/
def shortKernelLift (s : ShortExponent) (x : OffLattice) : ℝ :=
  ∑' k : ℤ, 1 / |(k : ℝ) + x.val| ^ s.val

end Riesz2

end


noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The energy H_N = N^{-s}∑_{i≠j}g_s(x_i−x_j) for s > 1 in equation (1.2). Both orientations of
each pair are included, using the unsubtracted periodic kernel. -/
def shortEnergy (s : ShortExponent) {N : ℕ+} (X : Riesz1.Configuration N) : ℝ :=
  (N : ℝ) ^ (-s.val) *
    ∑ i : Fin (N : ℕ), ∑ j : {j : Fin (N : ℕ) // j ≠ i},
      shortKernelLift s ⟨X.val i - X.val j.val,
        by
          intro h
          have hi : X.val i ∈ Ico (X.val ⟨0, N.pos⟩) (X.val ⟨0, N.pos⟩ + 1) :=
            ⟨X.property.1.monotone (Fin.zero_le i), X.property.2.2.2 i⟩
          have hj : X.val j.val ∈ Ico (X.val ⟨0, N.pos⟩) (X.val ⟨0, N.pos⟩ + 1) :=
            ⟨X.property.1.monotone (Fin.zero_le j.val), X.property.2.2.2 j.val⟩
          have he : (X.val i : UnitAddCircle) = (X.val j.val : UnitAddCircle) := by
            simpa only [AddCircle.coe_sub, sub_eq_zero] using h
          exact j.property (X.property.1.injective
            ((AddCircle.coe_eq_coe_iff_of_mem_Ico hi hj).mp he)).symm⟩

end Riesz2

end


noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The measure exp(−βH_N) dx for s > 1 on the configuration chart of `Riesz1`. Its
normalization gives the Gibbs law in equation (1.3). -/
def shortGibbsWeight (β : InverseTemperature) (s : ShortExponent) (N : ℕ+) :
    Measure (Riesz1.Configuration N) :=
  (Riesz1.configurationVolume N).withDensity
    (fun X => ENNReal.ofReal (Real.exp (-β.val * shortEnergy s X)))

end Riesz2

end


noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The partition integral Z_{N,β} = ∫ exp(−βH_N) dx for s > 1, with values in ℝ≥0∞. See
equation (1.3). -/
def shortPartitionFunction (β : InverseTemperature) (s : ShortExponent) (N : ℕ+) : ℝ≥0∞ :=
  shortGibbsWeight β s N univ

end Riesz2

end


noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The law G_{N,β} = Z_{N,β}⁻¹ exp(−βH_N) dx for s > 1, as in equation (1.3). Positivity and
finiteness of the normalizer are proved analytically. -/
def shortGibbsMeasure (β : InverseTemperature) (s : ShortExponent) (N : ℕ+) :
    Measure (Riesz1.Configuration N) :=
  (shortPartitionFunction β s N)⁻¹ • shortGibbsWeight β s N

end Riesz2

end


noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The Gibbs law G_{N,β} with density proportional to exp(−βH_N), as in equation (1.3). The
long-range branch uses `Riesz1.gibbsMeasure`. -/
def gibbsMeasure (p : Parameters) (N : ℕ+) : Measure (Riesz1.Configuration N) :=
  if h : p.val.2 < 1 then
    Riesz1.gibbsMeasure ⟨p.val, p.property.1, p.property.2.1, h⟩ N
  else shortGibbsMeasure ⟨p.val.1, p.property.1⟩
    ⟨p.val.2, lt_of_le_of_ne (le_of_not_gt h) (Ne.symm p.property.2.2)⟩ N

end Riesz2

end


noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The L² integrability of ξ, χ and their derivative representatives evaluated at the selected
microscopic gaps. These are the moment conclusions used to state the bounds in Theorems 1
and 2. -/
def GapSecondMoments (p : Parameters) (N : ℕ+) (i j : ℤ) (f g : GapObservable) : Prop :=
  MemLp (fun X => f.val.1 (gap X i)) 2 (gibbsMeasure p N) ∧
  MemLp (fun X => g.val.1 (gap X j)) 2 (gibbsMeasure p N) ∧
  MemLp (fun X => f.val.2 (gap X i)) 2 (gibbsMeasure p N) ∧
  MemLp (fun X => g.val.2 (gap X j)) 2 (gibbsMeasure p N)

end Riesz2

end


noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The Lebesgue essential supremum ‖ξ'‖∞ in Theorems 1 and 2. The definition of `GapObservable`
ensures that it is finite. -/
def derivativeSup (f : GapObservable) : ℝ := (eLpNorm f.val.2 ∞ volume).toReal

end Riesz2

end


noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The norm ‖ξ'(N(x_{i+1}−x_i))‖₂ under G_{N,β}, as used in Theorems 1 and 2. It takes values
in ℝ≥0∞. The decay statements establish its finiteness. -/
def gapDerivativeNorm (p : Parameters) (N : ℕ+) (i : ℤ) (f : GapObservable) : ℝ≥0∞ :=
  eLpNorm (fun X => f.val.2 (gap X i)) 2 (gibbsMeasure p N)

end Riesz2

end


noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The factor ‖ξ'(N(x_{i+1}−x_i))‖₂ + ‖ξ'‖∞ exp(−c d_N(i,j)^δ) in Theorems 1 and 2. The
derivative representative is part of the gap observable. -/
def correlationFactor (p : Parameters) (N : ℕ+) (i : ℤ) (f : GapObservable)
    (c δ : ℝ) (d : ℕ) : ℝ :=
  (gapDerivativeNorm p N i f).toReal +
    derivativeSup f * Real.exp (-c * (d : ℝ) ^ δ)

end Riesz2

end


noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The covariance Cov_{G_{N,β}}[ξ(N(x_{i+1}−x_i)),χ(N(x_{j+1}−x_j))] in Theorems 1 and 2. The
two observables are required to belong to L² of the Gibbs law. -/
def gapCorrelation (p : Parameters) (N : ℕ+) (i j : ℤ) (f g : ℝ → ℝ)
    (_hf : MemLp (fun X => f (gap X i)) 2 (gibbsMeasure p N))
    (_hg : MemLp (fun X => g (gap X j)) 2 (gibbsMeasure p N)) : ℝ :=
  ProbabilityTheory.covariance (fun X => f (gap X i))
    (fun X => g (gap X j)) (gibbsMeasure p N)

end Riesz2

end


noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- The pair (β,s) with β > 0 and s > 1, viewed as parameters of the circular Riesz gas in
Subsection 1.1. -/
def ofShort (β : InverseTemperature) (s : ShortExponent) : Parameters :=
  ⟨(β.val, s.val), β.property, lt_trans zero_lt_one s.property, ne_of_gt s.property⟩

end Riesz2

end

end Riesz2Audit.ShortRangeGapCorrelations

end
