/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.JointAdmissibilityNative

/-!
# Joint long-range fixed-length decay

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

namespace Riesz2.FixedLengthDecay

/-- See Lemma 6.4 of the paper: the analytic conclusion and original exterior
typicality use one choice of A,K. A may exceed a prescribed threshold.
The auxiliary matrix and field use the least degree of Lemma 5.4, as prescribed by the proof of Lemma 6.4. -/
theorem long_range_fixed_length_decay_joint (hzeta : External.PeriodicZeta)
    (hRig : External.LongRangeRigidityLocallyUniform) (s : Riesz1.RieszExponent) (Areq : ℝ) :
    ∃ A K ε₀ κ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧ 0 < κ ∧ Areq ≤ A ∧
    OriginalTypicality s.val A K ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∃ δ : ℝ, 0 < δ ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    ∀ (a d e : ℕ) (_ha : 1 ≤ a) (_hde : d ≤ e),
    let n := a.succPNat
    let N := ((n : ℕ)+d).succPNat
    ∀ _hN : 4*(n : ℕ) ≤ (N : ℕ), (n : ℝ)^(2/s.val) ≤ (N : ℝ) →
    ∀ (y : AffineSimplex.chartDomain (d+1) ((d+1+a : ℕ)+1))
      (z : AffineSimplex.chartDomain (e+1) ((e+1+a : ℕ)+1)) (L : ℝ),
    ((d+1+a : ℕ)+1 : ℝ)-∑ k, y.val k = L →
    ((e+1+a : ℕ)+1 : ℝ)-∑ k, z.val k = L →
    InterpolantLocalLaws.admissibleExterior (ofLong β s) (d+1) a
      (Nat.succ_le_succ (Nat.zero_le d)) θ ε A K y →
    InterpolantLocalLaws.admissibleExterior (ofLong β s) (e+1) a
      (Nat.succ_le_succ (Nat.zero_le e)) θ ε A K z →
    let Dy := RetainedSimplex.assemble (d+1) a (InterpolatingDensities.exteriorPermutation (d+1) a) y.val ⁻¹'
      gapAmbientDomain (d+1+a).succPNat
    let Dz := RetainedSimplex.assemble (e+1) a (InterpolatingDensities.exteriorPermutation (e+1) a) z.val ⁻¹'
      gapAmbientDomain (e+1+a).succPNat
    ∃ Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ,
      ContDiffOn ℝ ∞ Ky Dy ∧ ContDiffOn ℝ ∞ Kz Dz ∧
      (∀ u (hu : u ∈ Dy), Ky u = physicalAmbientGapEnergy (ofLong β s) (d+1+a).succPNat
        ⟨RetainedSimplex.assemble (d+1) a (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u,hu⟩) ∧
      (∀ u (hu : u ∈ Dz), Kz u = physicalAmbientGapEnergy (ofLong β s) (e+1+a).succPNat
        ⟨RetainedSimplex.assemble (e+1) a (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u,hu⟩) ∧
    ∀ t ∈ Icc (0 : ℝ) 1,
    let Ht := fun u : EuclideanSpace ℝ (Fin (a+1)) =>
      (∑ k, (θ.val ((a+1 : ℝ)^(-ε)*u k)+θ.val ((a+1 : ℝ)^(-ε)*(u k)⁻¹)))+(1-t)*Ky u+t*Kz u
    let μ : Measure (AffineSimplex.massSimplex a L) := (AffineSimplex.simplexVolume a L).comap Subtype.val
    let w := fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal (Real.exp (-β.val*Ht u.val))
    ∃ (h0 : (∫⁻ u, w u ∂μ) ≠ 0) (htop : (∫⁻ u, w u ∂μ) ≠ ⊤),
    ∃ hLN : L < ((n+d : ℕ)+1 : ℝ),
    let ν := (AffineFibre.normalizedMeasure μ w h0 htop).map
      (InterpolationTransport.inclusion a L ((n+d : ℕ)+1) hLN)
    IsProbabilityMeasure ν ∧
    ∀ frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a),
    ∃ Q : ScalarFormData ν, IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
      InterpolationCoefficientBounds.IsIntrinsicFibreForm a L ((n+d : ℕ)+1) hLN frame ν Q ∧
    let H := fun q : AffineSimplex.chartDomain n ((n+d : ℕ)+1) =>
      hessianMatrix (fun u => β.val*Ht u) q.val
    (∀ (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν),
      ∃! ψ : Fin (n : ℕ) → Q.1, WeightedWeakSolution Q H
        (zeroSumComponents (Fin (n : ℕ))) (fun i => if i = i₀ then χ else 0) ψ) ∧
    ∀ (i₀ : Fin (n : ℕ)), |(i₀.val : ℝ)+1-(n : ℝ)/2| ≤ (n : ℝ)/4 →
    ∀ χ : BoundedL2Pairings.boundedSubmodule ν, ∀ ψ : Fin (n : ℕ) → Q.1,
      WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ)))
        (fun i => if i = i₀ then χ.val else 0) ψ →
      (∑ j, InteractionDifferential.boundaryWeight s.val n j*‖(ψ j).val‖) ≤
        C*(n : ℝ)^(κ*ε-s.val/2)*
          (‖χ.val‖+Real.exp (-c*(n : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ ν).toReal) ∧
      (∑ j, ‖(ψ j).val‖) ≤ C*(n : ℝ)^(κ*ε)*
          (‖χ.val‖+Real.exp (-c*(n : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ ν).toReal) := by
  let h : ℕ+ := paperReferenceCutoffExponent s
  obtain ⟨A,K,εbase,κM,γ,hA,hK,hεbase,hκM,hγ,hAA,htyp,hfamily⟩ :=
    long_range_native_physical_inputs_joint hzeta hRig s Areq (h : ℕ)
  have hKpos : 0 < K := by linarith
  obtain ⟨κaux,hκaux,haux⟩ := schur_on_scalar_form_internal hzeta s (κM/K) (γ/K) h
    (div_pos hκM hKpos) (div_pos hγ hKpos)
  let ell := max (κaux*K) (max κM (s.val+2))
  have hell : 0 < ell := lt_of_lt_of_le (mul_pos hκaux hKpos) (le_max_left _ _)
  have heaux : κaux*K ≤ ell := le_max_left _ _
  have heM : κM ≤ ell := (le_max_left _ _).trans (le_max_right _ _)
  have hes : s.val+2 ≤ ell := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨A,K,εbase, max (s.val+2) (4*ell),hA,hK,hεbase,by positivity,hAA,htyp,?_⟩
  intro ε hε hsmall
  obtain ⟨n0,δ,hn0,hδ,_hthreshold,hfamilyNext⟩ := hfamily ε hε hsmall
  clear hfamily
  rename' hfamilyNext => hfamily
  refine ⟨δ,hδ,?_⟩
  intro βlo βhi hlo hle θ
  obtain ⟨C0,c,hC0,hc,hfamilyNext⟩ := hfamily βlo βhi hlo hle θ
  clear hfamily
  rename' hfamilyNext => hfamily
  let Cstar := max C0 1
  have hCstar : 1 ≤ Cstar := le_max_right _ _
  obtain ⟨D,hD,hauxNext⟩ := haux (K*ε) (mul_pos hKpos hε) Cstar hCstar βlo βhi hlo hle
  clear haux
  rename' hauxNext => haux
  let a0 := βlo*min 1 (s.val*(s.val+1))
  have ha0 : 0 < a0 := by have hs := s.property.1; dsimp only [a0]; positivity
  let G := 2*8^(2-s.val)*(2/(1-s.val/2)) + 8^(1+s.val/2)*(2/s.val) + 4^(s.val/2)
  obtain ⟨Ka,hKa,habsorb⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := ell*ε+5/2) (c := c) (c' := c/2) hδ (by linarith)
  let L0 := (G*Real.sqrt (2/(1-s.val)))*(C0+C0)*D
  let K0 := βhi*(Cstar*(1+1/s.val)*(2/(1-s.val)))+(C0+C0)*(2/(1-s.val/2))^2
  let Asq := 3*((2*L0/a0)^2+(1+K0)*D^2/a0+D^2)
  let Tsq := 9*(3*((C0+C0)*Ka)*(2*D+a0⁻¹)*D+((C0+C0)*Ka)*D^2)/a0
  have hK0 : 0 ≤ K0 := by
    have hs := s.property.1
    have hs1 : 0 < 1-s.val := sub_pos.mpr s.property.2
    have hβhi : 0 < βhi := hlo.trans_le hle
    dsimp only [K0]; positivity
  have hAsq : 0 ≤ Asq := by dsimp only [Asq]; positivity
  have hTsq : 0 ≤ Tsq := by dsimp only [Tsq]; positivity
  obtain ⟨C,hC,hrates⟩ := fixed_length_decay_from_comparison_internal
    s.val s.property.1 (ne_of_lt s.property.2) (s.val+2) (4*ell) ε hε.le n0
    a0 D Asq Tsq (2+4*(ell*ε)) (c/2) δ ha0 hD.le hAsq hTsq (by positivity) hδ
  refine ⟨C,(c/2)/4,hC,by positivity,?_⟩
  exact physical_instantiation_internal hzeta hRig s A K εbase κM γ hA hK hεbase hκM hγ hKpos κaux hκaux hell heaux heM hes ε hε hsmall n0 δ hn0 hδ _hthreshold βlo βhi hlo hle θ C0 c hC0 hc hfamily hCstar D hD haux ha0 Ka hKa habsorb hK0 hAsq hTsq C hC hrates

end Riesz2.FixedLengthDecay
