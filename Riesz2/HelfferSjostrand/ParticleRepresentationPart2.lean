/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.ParticleRepresentation
public import Riesz2.HelfferSjostrand.DifferentiatedPoisson

/-!
# Particle existence, minimum and covariance representation

Assemble Proposition 3.2 by the written appeal to the companion
Proposition 3.1: solve the scalar Poisson equation, approximate in its operator
graph, identify the vector-energy limit as its gradient, pass the mixed
equation to all vector tests, and impose the expected rotation normalization.
The companion normalized inverse then gives uniqueness and the quadratic
minimum. Testing the scalar equation gives covariance and variance.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ContDiff Laplacian

namespace Riesz2.ParticleRepresentation

open Riesz1

variable {N : ℕ+} {c : ℝ}

namespace Internal

variable (hN : 2 ≤ (N : ℕ)) (χ : HsPairPotentials N c) (hc : 0 < c)
local notation "μ" => (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))

/-- Identification of the vector graph limit in Proposition 3.2.
The graph approximation assumptions are confined to this internal lemma. -/
theorem gradient_of_approximants (F φ : HsSobolev μ) (f : ℕ → HsTestFunction N)
    (hv : Tendsto (fun k => hsSobolevValue μ
      (hsSobolevOfSmooth μ ⟨(f k).toFun, (f k).smoothOnClosure⟩))
      atTop (𝓝 (hsSobolevValue μ φ)))
    (ha : Tendsto (fun k => (memLp_hsLangevin hN χ (f k) μ).toLp (hsLangevin χ (f k)))
      atTop (𝓝 (poissonCenter μ (hsSobolevValue μ F)))) :
    ∃ u : HsVectorSobolev χ hN hc μ,
      (∀ i : Fin (N : ℕ), hsJetValue μ i u.val =
        (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ (hsSobolevGradient μ φ)) ∧
      HsNonGradientSolves χ hN hc (hsSobolevGradient μ F) u := by
  obtain ⟨ψ, u, hvalue, _, hcoords, hulim⟩ := hsGradient_graph_convergence hN χ hc f
    (hsSobolevValue μ φ) (poissonCenter μ (hsSobolevValue μ F)) hv ha
  have heq : ψ = φ := hsSobolevValue_injective χ hc hvalue
  have hcoords' (i : Fin (N : ℕ)) : hsJetValue μ i u.val =
      (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ (hsSobolevGradient μ φ) := by
    exact (hcoords i).trans (congrArg
      (fun ψ => (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ (hsSobolevGradient μ ψ)) heq)
  exact ⟨u, hcoords', equation_of_graph_limit hN χ hc F f u ha hulim⟩

/-- Operator graph limit in the companion proof of Proposition 3.2,
identified with the prescribed scalar Poisson gradient. -/
theorem gradient_of_poisson {C : ℝ} (hadm : HsAdmissible χ C) (F φ : HsSobolev μ)
    (hφ : HsPoissonSolves χ hc (hsSobolevValue μ F) φ) :
    ∃ u : HsVectorSobolev χ hN hc μ,
      (∀ i : Fin (N : ℕ), hsJetValue μ i u.val =
        (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ (hsSobolevGradient μ φ)) ∧
      HsNonGradientSolves χ hN hc (hsSobolevGradient μ F) u := by
  have hg : (φ, poissonCenter μ (hsSobolevValue μ F)) ∈ hsNeumannGraph μ :=
    (hsPoissonSolves_iff χ hc (hsSobolevValue μ F) φ).mp hφ
  obtain ⟨f, hv, ha⟩ := scalar_graph_approximation hN χ hc hadm φ _ hg
  exact gradient_of_approximants hN χ hc F φ f hv ha

/-- Coordinate values identify the expected rotation mean in
Proposition 3.2. -/
theorem gradient_jet_mean {C : ℝ} (hadm : HsAdmissible χ C) (φ : HsSobolev μ)
    (u : HsVectorSobolev χ hN hc μ)
    (hcoords : ∀ i : Fin (N : ℕ), hsJetValue μ i u.val =
      (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ (hsSobolevGradient μ φ)) :
    hsNonGradientMean χ hN hc μ u = 0 := by
  have hident : hsNonGradientMean χ hN hc μ u = hsL2Mean μ (hsSobolevGradient μ φ) := by
    change hsVectorMean μ u.val = _
    rw [hsVectorMean_eq_sum]
    simp only [hsL2Mean, sum_apply, ContinuousLinearMap.comp_apply]
    exact Finset.sum_congr rfl fun i _ => congrArg (poissonMean μ) (hcoords i)
  exact hident.trans (gradient_mean hN χ hc hadm φ)

/-- The scalar solution and its full particle gradient equation from the
companion Proposition 3.1, used in Proposition 3.2. -/
theorem exists_poisson_gradient {C : ℝ} (hadm : HsAdmissible χ C) (F : HsSobolev μ) :
    ∃ φ : HsSobolev μ, ∃ u : hsMeanZeroVector χ hN hc μ,
      (∫ x, hsSobolevValue μ φ x ∂μ) = 0 ∧
      HsPoissonSolves χ hc (hsSobolevValue μ F) φ ∧
      (∀ i : Fin (N : ℕ), hsJetValue μ i u.val.val =
        (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ (hsSobolevGradient μ φ)) ∧
      HsNonGradientSolves χ hN hc (hsSobolevGradient μ F) u.val := by
  let s := (scalar_poisson_gibbs_existsUnique χ hc
    External.prekopa_leindler hN (hsSobolevValue μ F)).exists
  let φ := s.choose
  have hm := s.choose_spec.1
  have hφ := s.choose_spec.2
  let g := gradient_of_poisson hN χ hc hadm F φ hφ
  let u := g.choose
  have hcoords := g.choose_spec.1
  have hsol := g.choose_spec.2
  exact ⟨φ, ⟨u, gradient_jet_mean hN χ hc hadm φ u hcoords⟩, hm, hφ, hcoords, hsol⟩

/-- Coordinate identification of a completed particle gradient identifies its
L² pairing, as required in Proposition 3.2. -/
theorem pairing_of_gradient_values (φ : HsSobolev μ) (u : HsVectorSobolev χ hN hc μ)
    (hu : ∀ i : Fin (N : ℕ), hsJetValue μ i u.val =
      (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ (hsSobolevGradient μ φ))
    (v : Lp (HsEuclidean N) 2 μ) :
    hsNonGradientPairing μ v u.val = inner ℝ (hsSobolevGradient μ φ) v := by
  rw [hsNonGradientPairing_eq_integral, L2.inner_def]
  have hcoords (i : Fin (N : ℕ)) :
      (hsJetValue μ i u.val : HsConfiguration N → ℝ) =ᵐ[μ]
        fun x => hsSobolevGradient μ φ x i := by
    rw [hu i]
    exact ContinuousLinearMap.coeFn_compLpL (EuclideanSpace.proj (𝕜 := ℝ) i)
      (hsSobolevGradient μ φ)
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr hcoords] with x hx
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [hx i, Real.inner_apply]
  exact mul_comm _ _

/-- Covariance and integrability obtained by testing the scalar equation in
Proposition 3.2, for every H¹ test observable. -/
theorem covariance_of_poisson (F φ : HsSobolev μ)
    (hφ : HsPoissonSolves χ hc (hsSobolevValue μ F) φ)
    (u : HsVectorSobolev χ hN hc μ)
    (hu : ∀ i : Fin (N : ℕ), hsJetValue μ i u.val =
      (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ (hsSobolevGradient μ φ))
    (G : HsSobolev μ) :
    ProbabilityTheory.covariance (hsSobolevValue μ F) (hsSobolevValue μ G) μ =
      hsNonGradientPairing μ (hsSobolevGradient μ G) u.val := by
  rw [DifferentiatedPoisson.covariance_eq_centered_inner,
    ← (hsPoissonSolves_iff χ hc (hsSobolevValue μ F) φ).mp hφ G]
  exact (pairing_of_gradient_values hN χ hc φ u hu (hsSobolevGradient μ G)).symm

/-- Complete assembly of the companion particle Proposition 3.1 used in
Proposition 3.2, including its normalized minimum and both
representation formulas. This internal statement uses the library pair carrier. -/
theorem library_existence_representation {C : ℝ} (hadm : HsAdmissible χ C)
    (F : HsSobolev μ) :
    ∃! u : hsMeanZeroVector χ hN hc μ,
      (∫ x, ∑ i : Fin (N : ℕ), hsJetValue μ i u.val.val x ∂μ) = 0 ∧
      (∃ φ : HsSobolev μ,
        (∫ x, hsSobolevValue μ φ x ∂μ) = 0 ∧
        HsPoissonSolves χ hc (hsSobolevValue μ F) φ ∧
        ∀ i : Fin (N : ℕ), hsJetValue μ i u.val.val =
          (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ (hsSobolevGradient μ φ)) ∧
      HsNonGradientSolves χ hN hc (hsSobolevGradient μ F) u.val ∧
      (∀ w : hsMeanZeroVector χ hN hc μ,
        HsNonGradientSolves χ hN hc (hsSobolevGradient μ F) w.val ↔ w = u) ∧
      (∀ w : hsMeanZeroVector χ hN hc μ,
        (∀ z : hsMeanZeroVector χ hN hc μ,
          hsVectorSobolevForm χ hN hc μ w.val w.val -
            2 * (∫ x, ∑ i : Fin (N : ℕ),
              hsSobolevGradient μ F x i * hsJetValue μ i w.val.val x ∂μ) ≤
          hsVectorSobolevForm χ hN hc μ z.val z.val -
            2 * (∫ x, ∑ i : Fin (N : ℕ),
              hsSobolevGradient μ F x i * hsJetValue μ i z.val.val x ∂μ)) ↔ w = u) ∧
      (∫ x, (hsSobolevValue μ F x - ∫ y, hsSobolevValue μ F y ∂μ) ^ 2 ∂μ) =
        ∫ x, ∑ i : Fin (N : ℕ), hsSobolevGradient μ F x i * hsJetValue μ i u.val.val x ∂μ ∧
      ∀ G : HsSobolev μ,
        ProbabilityTheory.covariance (hsSobolevValue μ F) (hsSobolevValue μ G) μ =
          ∫ x, ∑ i : Fin (N : ℕ), hsSobolevGradient μ G x i * hsJetValue μ i u.val.val x ∂μ := by
  let s := exists_poisson_gradient hN χ hc hadm F
  let φ := s.choose
  let u := s.choose_spec.choose
  have hmφ := s.choose_spec.choose_spec.1
  have hφ := s.choose_spec.choose_spec.2.1
  have hcoords := s.choose_spec.choose_spec.2.2.1
  have hsol := s.choose_spec.choose_spec.2.2.2
  let v : hsMeanZeroL2 μ :=
    ⟨hsSobolevGradient μ F, ParticleRepresentation.Internal.gradient_mean hN χ hc hadm F⟩
  have heq : u = hsInverse External.prekopa_leindler χ hN hc v :=
    hsInverse_unique External.prekopa_leindler χ hN hc v u (fun w => hsol w.val)
  have huniq (w : hsMeanZeroVector χ hN hc μ) :
      HsNonGradientSolves χ hN hc (hsSobolevGradient μ F) w.val ↔ w = u := by
    constructor
    · intro hw
      exact (hsInverse_unique External.prekopa_leindler χ hN hc v w
        (fun z => hw z.val)).trans heq.symm
    · rintro rfl
      exact hsol
  have hcov (G : HsSobolev μ) :
      ProbabilityTheory.covariance (hsSobolevValue μ F) (hsSobolevValue μ G) μ =
        ∫ x, ∑ i : Fin (N : ℕ), hsSobolevGradient μ G x i * hsJetValue μ i u.val.val x ∂μ :=
    (ParticleRepresentation.Internal.covariance_of_poisson hN χ hc F φ hφ u.val hcoords G).trans
      (hsNonGradientPairing_eq_integral μ (hsSobolevGradient μ G) u.val.val)
  refine ⟨u, ⟨?_, ⟨φ, hmφ, hφ, hcoords⟩, hsol, huniq, ?_, ?_, hcov⟩, ?_⟩
  · have hm : hsVectorMean μ u.val.val = 0 := u.property
    rw [hsVectorMean_eq_sum] at hm
    simp_rw [poissonMean_eq_integral] at hm
    rw [integral_finsetSum (f := fun i x => hsJetValue μ i u.val.val x)
      _ (fun i _ => (Lp.memLp _).integrable one_le_two)]
    exact hm
  · intro w
    have hmin := hsInverse_minimizer_iff External.prekopa_leindler χ hN hc v w
    have htarget : w = hsInverse External.prekopa_leindler χ hN hc v ↔ w = u :=
      ⟨fun hw => hw.trans heq.symm, fun hw => hw.trans heq⟩
    simpa only [hsNonGradientFunctional, hsNonGradientPairing_eq_integral] using hmin.trans htarget
  · simpa only [ProbabilityTheory.covariance, pow_two] using hcov F
  · intro w hw
    exact (huniq w).mp hw.2.2.1


end Internal

end Riesz2.ParticleRepresentation

namespace Riesz2

open Riesz1 ParticleRepresentation

variable {N : ℕ+} {c : ℝ} (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
  (χ : ParticlePairData N) (hχ : AdmissibleParticlePairs hN χ c)

local notation "Ξ" => AffineMetric.libraryPairs hχ
local notation "μ" => (hsQuotientGibbsProbability Ξ hc : Measure (HsConfiguration N))

/-- Proposition 3.2 of the paper, by the written appeal to the
companion Proposition 3.1. For every particle H¹ observable, there is a unique
normalized vector-energy solution. It is the gradient of a scalar Poisson
solution, the unique normalized minimum of the displayed quadratic functional,
and represents variance and covariance. The normalization is the expected sum
of coordinates, allowing rotation-dependent observables. The weak equation is
against every vector-energy test, so includes the stated weak Neumann boundary
condition. The quotient probability is the pair Gibbs law transported
to its periodic configuration carrier (`particle_quotient_law` below). -/
theorem particle_existence_representation (F : HsSobolev μ) :
    ∃! u : hsMeanZeroVector Ξ hN hc μ,
      (∫ x, ∑ i : Fin (N : ℕ), hsJetValue μ i u.val.val x ∂μ) = 0 ∧
      (∃ φ : HsSobolev μ,
        (∫ x, hsSobolevValue μ φ x ∂μ) = 0 ∧
        HsPoissonSolves Ξ hc (hsSobolevValue μ F) φ ∧
        ∀ i : Fin (N : ℕ), hsJetValue μ i u.val.val =
          (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ (hsSobolevGradient μ φ)) ∧
      HsNonGradientSolves Ξ hN hc (hsSobolevGradient μ F) u.val ∧
      (∀ w : hsMeanZeroVector Ξ hN hc μ,
        HsNonGradientSolves Ξ hN hc (hsSobolevGradient μ F) w.val ↔ w = u) ∧
      (∀ w : hsMeanZeroVector Ξ hN hc μ,
        (∀ z : hsMeanZeroVector Ξ hN hc μ,
          hsVectorSobolevForm Ξ hN hc μ w.val w.val -
            2 * (∫ x, ∑ i : Fin (N : ℕ),
              hsSobolevGradient μ F x i * hsJetValue μ i w.val.val x ∂μ) ≤
          hsVectorSobolevForm Ξ hN hc μ z.val z.val -
            2 * (∫ x, ∑ i : Fin (N : ℕ),
              hsSobolevGradient μ F x i * hsJetValue μ i z.val.val x ∂μ)) ↔ w = u) ∧
      (∫ x, (hsSobolevValue μ F x - ∫ y, hsSobolevValue μ F y ∂μ) ^ 2 ∂μ) =
        ∫ x, ∑ i : Fin (N : ℕ), hsSobolevGradient μ F x i * hsJetValue μ i u.val.val x ∂μ ∧
      ∀ G : HsSobolev μ,
        ProbabilityTheory.covariance (hsSobolevValue μ F) (hsSobolevValue μ G) μ =
          ∫ x, ∑ i : Fin (N : ℕ), hsSobolevGradient μ G x i * hsJetValue μ i u.val.val x ∂μ := by
  let a := library_admissible hN hc hχ
  exact ParticleRepresentation.Internal.library_existence_representation hN Ξ hc a.choose_spec F

/-- The law in Proposition 3.2 is precisely the particle Gibbs
law, expressed on the periodic quotient used by the companion Proposition 3.1. -/
theorem particle_quotient_law :
    μ = (pairGibbsMeasure χ (pairGibbsWeight_measurable hχ)
      (particle_hessian_normalization hN c hc χ hχ).1).map (hsConfigurationMap N) := by
  rw [pairGibbsMeasure_eq_library hc hχ]
  exact hsQuotientGibbsProbability_eq_map Ξ hc

end Riesz2
