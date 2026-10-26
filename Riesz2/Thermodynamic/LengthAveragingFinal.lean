/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.LengthDerivativeFinal
public import Riesz2.Thermodynamic.LengthAveraging
public import Riesz2.Thermodynamic.LengthOverlap

/-!
# Length averaging and overlap of the length laws

The length-averaging estimate of Lemma 6.5 and the overlap estimate in the proof of
Proposition 6.6 follow by supplying `LengthDerivative.length_averaging_derivative` to
the implications of `LengthAveraging` and `LengthOverlap`. The good event has tolerance
`2 * ε`.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff

namespace Riesz2.LengthAveraging

open LengthAveragingFibres LengthDerivative LengthVariance

/-- See Lemma 6.5 of the paper: the mean and the two-sided variance bounds of
the active length, and the variance bound for the fibre average `m_N` of every
Lipschitz observable supported in the middle half. The loss `κ` is fixed before
`ε`, and the tail power `δ` before the compact temperature interval. -/
theorem length_averaging
    (hz : External.PeriodicZeta) (hRig : External.LongRangeRigidityLocallyUniform)
    (hLC : External.ThermodynamicLogConcavity)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ κ εstar : ℝ, 0 < κ ∧ 0 < εstar ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ εstar → ∃ δ : ℝ, 0 < δ ∧
      ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
        ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
          ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
          ∀ n m : ℕ, 1 ≤ n → 4*(n+1) ≤ n+1+m+1 →
            (n+1 : ℝ)^(2/s) ≤ ((n+1+m : ℕ)+1 : ℝ) →
          let ν := activeMeasure p n m θ ε
          let V := Riesz1.variance ν (fun x => ∑ i, x i)
            (memLp_one_iff_integrable.mp (length_memLp p n m θ ε 1))
          |(∫ x, ∑ i, x i ∂ν)-(n+1 : ℝ)| ≤ C*Real.exp (-c*(n+1 : ℝ)^δ) ∧
            ENNReal.ofReal (c*(n+1 : ℝ)^(min s 1)) ≤ V ∧
            V ≤ ENNReal.ofReal (C*(n+1 : ℝ)^(min s 1+κ*ε)) ∧
          ∀ G : BlockObservable n.succPNat, ∀ J : Finset (Fin (n+1)),
            DependsOnBlockCoordinates G J →
            (∀ i ∈ J, |(i.val : ℝ)+1-(n+1 : ℝ)/2| ≤ (n+1 : ℝ)/4) →
          ∃ hG : MemLp (averagedObservable p n m θ ε G) 2 (lengthMeasure p n m θ ε),
            Real.sqrt ((Riesz1.variance (lengthMeasure p n m θ ε)
              (averagedObservable p n m θ ε G) (by have := lengthMeasure_probability p n m θ ε; exact hG.integrable one_le_two)).toReal) ≤
              C*(n+1 : ℝ)^(κ*ε-min s 1/2)*restrictedBlockDerivativeNorm G J
                (goodBlockEvent s n.succPNat (n+1+m).succPNat (2*ε)) +
              C*Real.exp (-c*(n+1 : ℝ)^δ)*blockDerivativeNorm G := by
  obtain ⟨κ, ε₀, hκ, hε₀, hD⟩ := length_averaging_derivative hz hRig s hs hs1
  refine length_averaging_from_derivative_internal hRig hLC s hs hs1 2 κ ε₀
    (by norm_num) hκ hε₀ fun ε hε hεle => ?_
  obtain ⟨δ, hδ, h⟩ := hD ε hε hεle
  refine ⟨δ, hδ, fun βlo βhi hlo hle θ => ?_⟩
  obtain ⟨C, c, hC, hc, h2⟩ := h βlo βhi hlo hle θ
  refine ⟨C, c, hC, hc, fun p hps hpl hph n m hn h4 hpow G J hdep hmid => ?_⟩
  obtain ⟨H, h1, -, hac, hmem, hbound⟩ := h2 p hps hpl hph n m hn h4 hpow G J hdep hmid
  rw [hps] at hbound
  exact ⟨H, h1, hac, hmem, hbound⟩

end Riesz2.LengthAveraging

namespace Riesz2.LengthOverlap

open LengthAveragingFibres LengthDerivative

/-- See the proof of Proposition 6.6 in the paper: for `N ≤ N'`, the length densities
`f_N` and `f_N'` have overlap mass at least `C⁻¹ n^(-κε)`, and the normalized overlap
density `ρ` averages every Lipschitz middle-half observable to within the stated
error of both active expectations. -/
theorem distinct_overlap
    (hz : External.PeriodicZeta) (hRig : External.LongRangeRigidityLocallyUniform)
    (hLog : External.ThermodynamicLogConcavity)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ κ εstar : ℝ, 0 < κ ∧ 0 < εstar ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ εstar → ∃ δ : ℝ, 0 < δ ∧
      ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
      ∃ n0 : ℕ, 1 ≤ n0 ∧ ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ n m m' : ℕ, n0 ≤ n → m ≤ m' → 4*(n+1) ≤ n+1+m+1 →
        (n+1 : ℝ)^(2/s) ≤ ((n+1+m : ℕ)+1 : ℝ) →
      let f := realLengthDensity p n m θ ε
      let f' := realLengthDensity p n m' θ ε
      let a0 := DensityOverlap.mass volume f f'
      let ρ := fun L => min (f L) (f' L) / a0
      let μρ := volume.withDensity (fun L => ENNReal.ofReal (ρ L))
      C⁻¹*(n+1 : ℝ)^(-κ*ε) ≤ a0 ∧ 0 < a0 ∧
        Measurable ρ ∧ (∀ L, 0 ≤ ρ L) ∧ (∫ L, ρ L) = 1 ∧
        (∀ L, ρ L ≤ a0⁻¹*f L) ∧ (∀ L, ρ L ≤ a0⁻¹*f' L) ∧
      ∀ G : BlockObservable n.succPNat, ∀ J : Finset (Fin (n+1)),
        DependsOnBlockCoordinates G J →
        (∀ i ∈ J, |(i.val : ℝ)+1-(n+1 : ℝ)/2| ≤ (n+1 : ℝ)/4) →
        Integrable (realAveragedObservable p n m θ ε G) μρ ∧
        Integrable (realAveragedObservable p n m' θ ε G) μρ ∧
        |(∫ L, realAveragedObservable p n m θ ε G L ∂μρ) -
          ∫ x, G.val (WithLp.ofLp x) ∂activeMeasure p n m θ ε| +
        |(∫ L, realAveragedObservable p n m' θ ε G L ∂μρ) -
          ∫ x, G.val (WithLp.ofLp x) ∂activeMeasure p n m' θ ε| ≤
          C*(n+1 : ℝ)^(κ*ε-min s 1/2)*restrictedBlockDerivativeNorm G J
            (goodBlockEvent s n.succPNat (n+1+m).succPNat (2*ε)) +
          C*Real.exp (-c*(n+1 : ℝ)^δ)*blockDerivativeNorm G :=
  distinct_overlap_from_averaging_internal hRig hLog s hs hs1 2 (by norm_num)
    (LengthAveraging.length_averaging hz hRig hLog s hs hs1)

end Riesz2.LengthOverlap
