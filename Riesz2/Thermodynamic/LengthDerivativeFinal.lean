/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.LengthAveragingFibresFinal
public import Riesz2.Thermodynamic.LengthDerivativePart5
public import Riesz2.Thermodynamic.LengthDerivativePart6

/-!
# Length derivative of a supported Lipschitz observable

The length derivative estimate in the proof of Lemma 6.5 follows from conditional
remainders in both exponent regimes, the C¹ estimate and the passage to Lipschitz
observables. Constants precede the volumes and observable. The loss precedes epsilon and
the tail power precedes temperature.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace Riesz2.LengthDerivative

open AffineSimplex LengthAveragingFibres

/-- See the proof of Lemma 6.5 in the paper: the short fibre Hessian
is exactly the Hessian of the dimensionless penalized marginal potential. -/
theorem short_hessian_normalization_internal (p : Parameters) (hsp : 1 < p.val.2)
    (n m : ℕ) (θ : PhysicalCutoff) (ε : ℝ) (hε : 0 < ε) :
    let V := fun x : EuclideanSpace ℝ (Fin (n+1)) =>
      p.val.1*∑ i, (θ.val (((n+1 : ℝ)^ε)⁻¹*x i)+
        θ.val (((n+1 : ℝ)^ε)⁻¹*(x i)⁻¹)) -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n+1) m (Equiv.refl _) (x,z)).toReal)
    ∀ x : chartDomain (n+1) ((n+1+m : ℕ)+1),
      p.val.1 • hessianMatrix (fun y => p.val.1⁻¹*V y) x.val =
        hessianMatrix V x.val := by
  intro V
  have hV : ContDiffOn ℝ ∞ V (chartDomain (n+1) ((n+1+m : ℕ)+1)) := by
    simpa only [V, Nat.succPNat_coe, Nat.cast_succ,
        Real.rpow_neg (by positivity : (0 : ℝ) ≤ n+1)] using
      (short_twoSided_matrix_internal p hsp n.succPNat m θ ε hε).1
  intro x
  have hvx : ContDiffAt ℝ 2 V x.val :=
    (hV.contDiffAt ((isOpen_chartDomain _ _).mem_nhds x.property)).of_le (by norm_num)
  ext i j
  change p.val.1*hessianMatrix (fun y => p.val.1⁻¹*V y) x.val i j = _
  rw [DecayShort.PhysicalComparison.hessianMatrix_entry (contDiffAt_const.mul hvx),
    DecayShort.PhysicalComparison.hessianMatrix_entry hvx,
    PhysicalCollision.internal_hessian_const_mul hvx]
  exact mul_inv_cancel_left₀ p.property.1.ne' _

/-- See the proof of Lemma 6.5 in the paper: actual measurable remainders,
with their moments and physical fibre bounds, uniformly in both regimes. -/
theorem fibre_remainder_bounds_internal
    (hz : External.PeriodicZeta) (hRig : External.LongRangeRigidityLocallyUniform)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) : ∃ κ εf : ℝ, 0 < κ ∧ 0 < εf ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ εf → ∃ δf : ℝ, 0 < δf ∧
      ∀ (θ : PhysicalCutoff) (βlo βhi : ℝ), 0 < βlo → βlo ≤ βhi →
      ∃ Cf cf : ℝ, 0 < Cf ∧ 0 < cf ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ n m : ℕ, 1 ≤ n → 4*(n+1) ≤ n+1+m+1 →
        (n+1 : ℝ)^(2/s) ≤ ((n+1+m : ℕ)+1 : ℝ) →
      ∃ e : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ) → ℝ≥0∞,
        Measurable e ∧
        (∫⁻ L, e L+e L^2 ∂lengthMeasure p n m θ ε) ≤
          ENNReal.ofReal (Cf*Real.exp (-cf*(n+1 : ℝ)^δf)) ∧
      ∀ᵐ L ∂lengthMeasure p n m θ ε,
        let P := fun x : EuclideanSpace ℝ (Fin (n+1)) =>
          p.val.1*∑ i, (θ.val ((n+1 : ℝ)^(-ε)*x i)+
            θ.val ((n+1 : ℝ)^(-ε)*(x i)⁻¹)) -
          Real.log (∫ z : EuclideanSpace ℝ (Fin m),
            (ProperMarginalChart.chartDensity p (n+1) m (Equiv.refl _) (x,z)).toReal)
        FibreBoundsInternal (retainedKernel p n m θ ε L) n.succPNat
          (fun x => hessianMatrix P x.val) p.val.2 (κ*ε) Cf (e L) := by
  obtain ⟨hlong, hshort⟩ := length_averaging_fibres hz hRig
  rcases lt_or_gt_of_ne hs1 with hlt | hgt
  · let t : Riesz1.RieszExponent := ⟨s, hs, hlt⟩
    obtain ⟨κ, C₀, εf, hκ, _hC₀, hεf, hf⟩ := hlong t
    refine ⟨κ, εf, hκ, hεf, fun ε hε hsmall => ?_⟩
    obtain ⟨δf, hδf, hf⟩ := hf ε hε hsmall
    refine ⟨δf, hδf, fun θ βlo βhi hlo hle => ?_⟩
    obtain ⟨Cf, cf, hCf, hcf, hf⟩ := hf θ βlo βhi hlo hle
    refine ⟨Cf, cf, hCf, hcf, ?_⟩
    intro p hp hpl hph n m hn hsize hpower
    let β : InverseTemperature := ⟨p.val.1, p.property.1⟩
    have heq : ofLong β t = p := by
      apply Subtype.ext
      exact Prod.ext rfl hp.symm
    have hh := hf β ⟨hpl,hph⟩ n m hn hsize hpower
    refine ⟨longRemainder β t n m θ ε C₀ (2*ε) 1,
      measurable_longRemainder _ _ _ _ _ _ _ _ _, ?_, ?_⟩
    · simpa only [heq] using hh.1
    · simpa only [heq, hp] using hh.2
  · obtain ⟨κ₀, κ, C₀, εf, _hκ₀, hκ, _hC₀, hεf, hf⟩ := hshort s hgt
    refine ⟨κ, εf, hκ, hεf, fun ε hε hsmall => ?_⟩
    obtain ⟨δf, hδf, hf⟩ := hf ε hε hsmall
    refine ⟨δf, hδf, fun θ βlo βhi hlo hle => ?_⟩
    obtain ⟨Cf, cf, hCf, hcf, hf⟩ := hf θ βlo βhi hlo hle
    refine ⟨Cf, cf, hCf, hcf, ?_⟩
    intro p hp hpl hph n m hn hsize hpower
    have hsp : 1 < p.val.2 := hp ▸ hgt
    obtain ⟨hmoment,hfib⟩ := hf p hp hpl hph n m hn hsize hpower
    refine ⟨shortRemainder p n m θ ε C₀ (2*ε) κ₀,
      measurable_shortRemainder p hsp n m θ ε C₀ (2*ε) κ₀, hmoment, ?_⟩
    let V := fun x : EuclideanSpace ℝ (Fin (n+1)) =>
      p.val.1*∑ i, (θ.val (((n+1 : ℝ)^ε)⁻¹*x i)+
        θ.val (((n+1 : ℝ)^ε)⁻¹*(x i)⁻¹)) -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n+1) m (Equiv.refl _) (x,z)).toReal)
    have heq := short_hessian_normalization_internal p hsp n m θ ε hε
    filter_upwards [hfib] with L hL
    change FibreBoundsInternal (retainedKernel p n m θ ε L) n.succPNat
      (fun x : chartDomain (n+1) ((n+1+m : ℕ)+1) => p.val.1 •
        hessianMatrix (fun y => p.val.1⁻¹*V y) x.val) s (κ*ε) Cf
        (shortRemainder p n m θ ε C₀ (2*ε) κ₀ L) at hL
    have hM : (fun x : chartDomain (n+1) ((n+1+m : ℕ)+1) => p.val.1 •
        hessianMatrix (fun y => p.val.1⁻¹*V y) x.val) =
        (fun x => hessianMatrix V x.val) := funext heq
    have hL' := (congrArg (fun M => FibreBoundsInternal (retainedKernel p n m θ ε L)
      n.succPNat M s (κ*ε) Cf (shortRemainder p n m θ ε C₀ (2*ε) κ₀ L)) hM).mp hL
    simpa only [V, hp, Real.rpow_neg (by positivity : (0 : ℝ) ≤ n+1)] using hL'

/-- See the proof of Lemma 6.5 in the paper, both exponent regimes.
Here the active size is `n+1`, the total size is `n+m+2`, and the good event
has fine tolerance `2 ε`. The every-length average is C¹, locally absolutely
continuous, and has the stated finite weighted L² derivative. The loss and
smallness threshold depend only on the exponent. The tail power is chosen
before temperature, and the prefactors are uniform on each positive compact
temperature interval (for the fixed physical cutoff). -/
theorem length_averaging_derivative
    (hz : External.PeriodicZeta) (hRig : External.LongRangeRigidityLocallyUniform)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ κ ε₀ : ℝ, 0 < κ ∧ 0 < ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ δ : ℝ, 0 < δ ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
    ∀ n m : ℕ, 1 ≤ n → 4*(n+1) ≤ n+1+m+1 →
      (n+1 : ℝ)^(2/s) ≤ ((n+1+m : ℕ)+1 : ℝ) →
    ∀ G : BlockObservable n.succPNat, ∀ J : Finset (Fin (n+1)),
      DependsOnBlockCoordinates G J →
      (∀ i ∈ J, |(i.val : ℝ)+1-(n+1 : ℝ)/2| ≤ (n+1 : ℝ)/4) →
    ∃ H : ℝ → ℝ,
      (∀ L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ),
        H L.val = averagedObservable p n m θ ε G L) ∧
      ContDiffOn ℝ 1 H (Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ)) ∧
      (∀ u v : ℝ, u ∈ Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ) →
        v ∈ Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ) →
        AbsolutelyContinuousOnInterval H u v) ∧
      MemLp (fun L => deriv H L.val) 2 (lengthMeasure p n m θ ε) ∧
      (eLpNorm (fun L => deriv H L.val) 2 (lengthMeasure p n m θ ε)).toReal ≤
        C*(n+1 : ℝ)^(κ*ε-min p.val.2 1)*
          restrictedBlockDerivativeNorm G J
            (goodBlockEvent p.val.2 n.succPNat (n+1+m).succPNat (2*ε)) +
        C*Real.exp (-c*(n+1 : ℝ)^δ)*blockDerivativeNorm G := by
  obtain ⟨κ, εf, hκ, hεf, hsource⟩ :=
    fibre_remainder_bounds_internal hz hRig s hs hs1
  obtain ⟨ηstar, astar, hηstar, _hastar, hrate⟩ :=
    c1_length_averaging_derivative_internal hRig s hs hs1 κ
  refine ⟨κ, min εf (ηstar/2), hκ, by positivity, fun ε hε hsmall => ?_⟩
  have hsmallf : ε ≤ εf := hsmall.trans (min_le_left _ _)
  have hη : 0 < 2*ε := by positivity
  have hηsmall : 2*ε ≤ ηstar := by
    have hh := hsmall.trans (min_le_right _ _)
    linarith
  obtain ⟨δf, hδf, hsource⟩ := hsource ε hε hsmallf
  obtain ⟨δ, hδ, hrate⟩ := hrate ε (2*ε) hε hη hηsmall δf hδf
  refine ⟨δ, hδ, fun βlo βhi hlo hle θ => ?_⟩
  obtain ⟨Cf, cf, hCf, hcf, hsource⟩ := hsource θ βlo βhi hlo hle
  obtain ⟨C, c, hC, hc, hrate⟩ := hrate βlo βhi hlo hle θ Cf cf hCf hcf
  refine ⟨C, c, hC, hc, ?_⟩
  intro p hp hpl hph n m hn hsize hpower G J hJ hmiddle
  obtain ⟨e, he, hmoment, hfib⟩ := hsource p hp hpl hph n m hn hsize hpower
  have hC1 := hrate p hp hpl hph n m hn hsize hpower e he hmoment
  have hC1 := hC1 (fun frame => by
    filter_upwards [hfib] with L hL
    refine ⟨hL.1, ?_⟩
    intro Q hQ hcon _hintr i hi χ B hB hχ ψ hψ
    have hi' : |(i.val : ℝ)+1-(n.succPNat : ℝ)/2| ≤ (n.succPNat : ℝ)/4 := by
      simpa only [Nat.succPNat_coe, Nat.cast_succ] using hi
    have hh := (hL.2 Q hQ hcon i hi' χ B hB hχ).2 ψ hψ
    simpa only [Nat.succPNat_coe, Nat.cast_succ] using
      And.intro hh.2.1 (And.intro hh.1 hh.2.2))
  apply middle_half_lipschitz_derivative_of_smooth_internal p n m hn θ ε (2*ε) hη
    J hmiddle C c κ δ hC.le ?_ G hJ
  intro G hG hGJ
  obtain ⟨H, hmean, _hreg, hmem, hbound⟩ := hC1 G hG J hGJ hmiddle
  exact ⟨H, hmean, hmem, hbound⟩

end Riesz2.LengthDerivative
