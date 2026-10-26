/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.JointAdmissibilityComparison

/-!
# Joint canonical-overlap comparison

Strengthened interfaces for Proposition 6.6: the same structural choice retains
original-law exterior typicality throughout the analytic chain.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal ContDiff Topology MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
open Riesz2.JointAdmissibility

namespace Riesz2.TwoVolumeComparison

/-- See Proposition 6.6 of the paper: the analytic conclusion and original exterior
typicality use one choice of A,K. A may exceed a prescribed threshold. -/
theorem physical_conditional_comparison_joint
    (hz : External.PeriodicZeta) (hRig : External.LongRangeRigidityLocallyUniform)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ A K ε₀ κ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧ 0 < κ ∧
    OriginalTypicality s A K ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
    ∀ a d e : ℕ, 1 ≤ a → 4*(a+1) ≤ d+1+a+1 → d ≤ e →
      (a+1 : ℝ)^(2/s) ≤ (d+1+a+1 : ℝ) →
    ∀ (L : ℝ), 0 < L →
    ∀ (y : AffineSimplex.chartDomain (d+1) ((d+1+a : ℕ)+1))
      (z : AffineSimplex.chartDomain (e+1) ((e+1+a : ℕ)+1)),
      InterpolantLocalLaws.admissibleExterior p (d+1) a (by omega) θ ε A K y →
      InterpolantLocalLaws.admissibleExterior p (e+1) a (by omega) θ ε A K z →
      ((d+1+a : ℕ)+1 : ℝ)-∑ i, y.val i = L →
      ((e+1+a : ℕ)+1 : ℝ)-∑ i, z.val i = L →
    ∀ (R : ℕ), R ≤ (a+1)/4 → ((a+1)%4 ≠ 1 ∨ R < (a+1)/4) →
    ∀ G : BlockObservable a.succPNat,
      DependsOnBlockCoordinates G (symmetricMiddleBlock a.succPNat R) →
    let ky := InterpolatingDensities.simplexFibreKernel p (d+1) a (by omega)
      (InterpolatingDensities.exteriorPermutation (d+1) a) θ
      (Real.rpow_pos_of_pos (show (0 : ℝ) < (a+1 : ℕ) by positivity) (-ε))
      (Finset.univ.map (Fin.castLEEmb (show a+1 ≤ d+1+a+1 by omega))) true
    let kz := InterpolatingDensities.simplexFibreKernel p (e+1) a (by omega)
      (InterpolatingDensities.exteriorPermutation (e+1) a) θ
      (Real.rpow_pos_of_pos (show (0 : ℝ) < (a+1 : ℕ) by positivity) (-ε))
      (Finset.univ.map (Fin.castLEEmb (show a+1 ≤ e+1+a+1 by omega))) true
    |(∫ u, G.val (WithLp.ofLp u) ∂ky y) -
        ∫ u, G.val (WithLp.ofLp u) ∂kz z| ≤
      C*(a+1 : ℝ)^(κ*ε-min s 1/2)*
        (restrictedBlockDerivativeNorm G (symmetricMiddleBlock a.succPNat R)
          (goodBlockEvent s a.succPNat (d+1+a).succPNat (K*ε)) +
          Real.exp (-c*(a+1 : ℝ)^δ)*blockDerivativeNorm G) := by
  obtain ⟨A,K,ε₀,κ,hA,hK,hε₀,hκ,htyp,hcomp⟩ :=
    CompatibleComparison.compatible_conditional_comparison_joint hz hRig s hs hs1
  refine ⟨A,K,ε₀,κ,hA,hK,hε₀,hκ,htyp,fun ε hε hsmall => ?_⟩
  obtain ⟨δ,hδ,_,hcomp⟩ := hcomp ε hε hsmall
  refine ⟨δ,hδ,fun βlo βhi hlo hle θ => ?_⟩
  obtain ⟨C,c,hC,hc,hcomp⟩ := hcomp βlo βhi hlo hle θ
  refine ⟨C,c,hC,hc,fun p hps hpl hph a d e ha h4 hde hpow L hL y z hy hz hyL hzL
    R hR hround G hG => ?_⟩
  obtain ⟨_,Ky,Kz,hKy,hKz,h00,h0t,h10,h1t,hbound⟩ :=
    hcomp p hps hpl hph a d e ha h4 hde hpow L hL y z hy hz hyL hzL
  have hh := (hbound G (symmetricMiddleBlock a.succPNat R) hG
    (fun i hi => by
      simpa only [Nat.succPNat_coe, Nat.cast_succ] using
        symmetricMiddleBlock_middle_half a.succPNat R hR hround i hi)).2.2
  dsimp only
  rw [physical_endpoint_expectation p (d+1) a (by omega) θ ε L y hyL Ky hKy G h00 h0t,
    physical_endpoint_expectation p (e+1) a (by omega) θ ε L z hzL Kz hKz G h10 h1t]
  exact hh

/-- See Proposition 6.6 of the paper: the analytic conclusion and original exterior
typicality use one choice of A,K. A may exceed a prescribed threshold. -/
theorem integrated_physical_comparison_internal_joint
    (hz : External.PeriodicZeta) (hRig : External.LongRangeRigidityLocallyUniform)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ A K ε₀ κ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧ 0 < κ ∧
    OriginalTypicality s A K ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ C c H : ℝ, 0 < C ∧ 0 < c ∧ 0 < H ∧
    ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
    ∀ n m m' : ℕ, 1 ≤ n → 4*(n+1) ≤ m+1+n+1 → ∀ (hmm' : m ≤ m'),
      (n+1 : ℝ)^(2/s) ≤ (m+1+n+1 : ℝ) →
    ∀ (ρ : Measure (Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ))), IsProbabilityMeasure ρ →
    ∀ b : ℝ, 0 ≤ b →
      ρ ≤ ENNReal.ofReal b • LengthAveragingFibres.lengthMeasure p n m θ ε →
      ρ.map (largerLength n m m' hmm') ≤
        ENNReal.ofReal b • LengthAveragingFibres.lengthMeasure p n m' θ ε →
    ∀ T₁ T₂ : ℝ,
      (InterpolantLocalLaws.physicalExteriorLaw p (m+1) n θ ε)
        {y | ¬ InterpolantLocalLaws.admissibleExterior p (m+1) n (by omega) θ ε A K y} ≤
          ENNReal.ofReal T₁ →
      (InterpolantLocalLaws.physicalExteriorLaw p (m'+1) n θ ε)
        {z | ¬ InterpolantLocalLaws.admissibleExterior p (m'+1) n (by omega) θ ε A K z} ≤
          ENNReal.ofReal T₂ →
    ∀ R : ℕ, R ≤ (n+1)/4 → ((n+1)%4 ≠ 1 ∨ R < (n+1)/4) →
    ∀ G : BlockObservable n.succPNat,
      DependsOnBlockCoordinates G (symmetricMiddleBlock n.succPNat R) →
    |(∫ L, LengthOverlap.realAveragedObservable p n m θ ε G L.val ∂ρ) -
        ∫ L, LengthOverlap.realAveragedObservable p n m' θ ε G L.val ∂ρ| ≤
      C*(n+1 : ℝ)^(κ*ε-min s 1/2)*
        (restrictedBlockDerivativeNorm G (symmetricMiddleBlock n.succPNat R)
          (goodBlockEvent s n.succPNat (m+1+n).succPNat (K*ε)) +
          Real.exp (-c*(n+1 : ℝ)^δ)*blockDerivativeNorm G) +
      (Real.sqrt (b*(H*blockDerivativeNorm G^2)) +
        Real.sqrt (b*(H*blockDerivativeNorm G^2)))*
        Real.sqrt (b*(max T₁ 0+max T₂ 0)) := by
  obtain ⟨A,K,ε₀,κ,hA,hK,hε₀,hκ,htyp,hcomp⟩ := physical_conditional_comparison_joint hz hRig s hs hs1
  refine ⟨A,K,ε₀,κ,hA,hK,hε₀,hκ,htyp,fun ε hε hsmall => ?_⟩
  obtain ⟨δ,hδ,hcomp⟩ := hcomp ε hε hsmall
  refine ⟨δ,hδ,fun βlo βhi hlo hle θ => ?_⟩
  obtain ⟨C,c,hC,hc,hcomp⟩ := hcomp βlo βhi hlo hle θ
  obtain ⟨H,hH,hm⟩ := compact_conditional_centered_second_moment
    s ε βlo βhi hs hs1 hε hlo hle θ
  refine ⟨C,c,H,hC,hc,hH,fun p hps hpl hph n m m' hn h4 hmm' hpow
    ρ hρ b hb hleft hright T₁ T₂ hT₁ hT₂ R hR hround G hG => ?_⟩
  have : IsProbabilityMeasure ρ := hρ
  have hmF := (hm p hps hpl hph (m+1) n (by omega) G).2
  have hmH := (hm p hps hpl hph (m'+1) n (by omega) G).2
  have hP : 0 ≤ C*(n+1 : ℝ)^(κ*ε-min s 1/2)*
      (restrictedBlockDerivativeNorm G (symmetricMiddleBlock n.succPNat R)
        (goodBlockEvent s n.succPNat (m+1+n).succPNat (K*ε)) +
        Real.exp (-c*(n+1 : ℝ)^δ)*blockDerivativeNorm G) := by
    have hD : 0 ≤ blockDerivativeNorm G := Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _
    have hA : 0 ≤ restrictedBlockDerivativeNorm G (symmetricMiddleBlock n.succPNat R)
        (goodBlockEvent s n.succPNat (m+1+n).succPNat (K*ε)) :=
      Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _
    positivity
  apply physical_common_comparison_internal p n m m' hmm' θ ε ρ b H T₁ T₂ _ A K hb hH.le hP
    hleft hright G hmF hmH hT₁ hT₂
  intro y z hy hz hres
  apply hcomp p hps hpl hph n m m' hn h4 hmm' hpow
    (exteriorLength n m y).val (exteriorLength n m y).property.1 y z hy hz rfl hres.symm
    R hR hround G hG

/-- See Proposition 6.6 of the paper: the analytic conclusion and original exterior
typicality use one choice of A,K. A may exceed a prescribed threshold. -/
theorem overlap_integrated_comparison_internal_joint
    (hz : External.PeriodicZeta) (hRig : External.LongRangeRigidityLocallyUniform)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ A K ε₀ κ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧ 0 < κ ∧
    OriginalTypicality s A K ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ C c H : ℝ, 0 < C ∧ 0 < c ∧ 0 < H ∧
    ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
    ∀ n m m' : ℕ, 1 ≤ n → 4*(n+1) ≤ m+1+n+1 → m ≤ m' →
      (n+1 : ℝ)^(2/s) ≤ (m+1+n+1 : ℝ) →
    let f := LengthOverlap.realLengthDensity p n m θ ε
    let f' := LengthOverlap.realLengthDensity p n m' θ ε
    let a₀ := DensityOverlap.mass volume f f'
    let μρ := volume.withDensity (fun L => ENNReal.ofReal (min (f L) (f' L)/a₀))
    0 < a₀ → ∀ T₁ T₂ : ℝ,
      (InterpolantLocalLaws.physicalExteriorLaw p (m+1) n θ ε)
        {y | ¬ InterpolantLocalLaws.admissibleExterior p (m+1) n (by omega) θ ε A K y} ≤
          ENNReal.ofReal T₁ →
      (InterpolantLocalLaws.physicalExteriorLaw p (m'+1) n θ ε)
        {z | ¬ InterpolantLocalLaws.admissibleExterior p (m'+1) n (by omega) θ ε A K z} ≤
          ENNReal.ofReal T₂ →
    ∀ R : ℕ, R ≤ (n+1)/4 → ((n+1)%4 ≠ 1 ∨ R < (n+1)/4) →
    ∀ G : BlockObservable n.succPNat,
      DependsOnBlockCoordinates G (symmetricMiddleBlock n.succPNat R) →
    |(∫ L, LengthOverlap.realAveragedObservable p n m θ ε G L ∂μρ) -
        ∫ L, LengthOverlap.realAveragedObservable p n m' θ ε G L ∂μρ| ≤
      C*(n+1 : ℝ)^(κ*ε-min s 1/2)*
        (restrictedBlockDerivativeNorm G (symmetricMiddleBlock n.succPNat R)
          (goodBlockEvent s n.succPNat (m+1+n).succPNat (K*ε)) +
          Real.exp (-c*(n+1 : ℝ)^δ)*blockDerivativeNorm G) +
      (Real.sqrt (a₀⁻¹*(H*blockDerivativeNorm G^2)) +
        Real.sqrt (a₀⁻¹*(H*blockDerivativeNorm G^2)))*
        Real.sqrt (a₀⁻¹*(max T₁ 0+max T₂ 0)) := by
  obtain ⟨A,K,ε₀,κ,hA,hK,hε₀,hκ,htyp,hcomp⟩ := integrated_physical_comparison_internal_joint hz hRig s hs hs1
  refine ⟨A,K,ε₀,κ,hA,hK,hε₀,hκ,htyp,fun ε hε hsmall => ?_⟩
  obtain ⟨δ,hδ,hcomp⟩ := hcomp ε hε hsmall
  refine ⟨δ,hδ,fun βlo βhi hlo hle θ => ?_⟩
  obtain ⟨C,c,H,hC,hc,hH,hcomp⟩ := hcomp βlo βhi hlo hle θ
  refine ⟨C,c,H,hC,hc,hH,fun p hps hpl hph n m m' hn h4 hmm' hpow => ?_⟩
  intro f f' a₀ μρ ha₀ T₁ T₂ hT₁ hT₂ R hR hround G hG
  let ρ := μρ.comap (Subtype.val : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ) → ℝ)
  obtain ⟨hρ,_hmap,hleft,hright,hmeans⟩ := overlap_common_carrier p n m m' hmm' θ ε ha₀
  have hh := hcomp p hps hpl hph n m m' hn h4 hmm' hpow ρ hρ
    a₀⁻¹ (inv_nonneg.mpr ha₀.le) hleft hright T₁ T₂ hT₁ hT₂ R hR hround G hG
  rw [(hmeans G).1,(hmeans G).2] at hh
  exact hh

end Riesz2.TwoVolumeComparison
