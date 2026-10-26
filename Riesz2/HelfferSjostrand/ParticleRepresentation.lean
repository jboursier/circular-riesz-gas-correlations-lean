/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.AffineMetric
public import Riesz1.HelfferSjostrand.BoundaryCoreQuotient
public import Riesz1.HelfferSjostrand.GradientConvergenceVector
public import Riesz1.HelfferSjostrand.NonGradientEnergy
public import Riesz1.HelfferSjostrand.IntegrationByPartsCutoff
public import Riesz1.HelfferSjostrand.BoundaryCoreAnchoredGeometry
public import Riesz1.Frozen.External.PrekopaLeindlerProof
public import Mathlib.Probability.Moments.Covariance

/-!
# Particle existence and representation: the compact mixed identity

For Proposition 3.2 in the paper, use the companion
paper's Proposition 3.1 on the cyclic particle quotient. This module supplies
the admissibility adapter and integration against arbitrary compact vector
tests. In particular, the mixed identity is stronger than the self-energy
identity used to construct the vector graph limit. The continuation assembles
the solution, normalization, minimum and covariance representation.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ContDiff Laplacian

namespace Riesz2.ParticleRepresentation

open Riesz1

variable {N : ℕ+} {c : ℝ}

/-- The collision implication in the proof of Proposition 3.2:
the all-coefficient criterion implies the companion Assumption 3.1. -/
theorem library_admissible (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    {χ : ParticlePairData N} (hχ : AdmissibleParticlePairs hN χ c) :
    ∃ C : ℝ, HsAdmissible (AffineMetric.libraryPairs hχ) C := by
  obtain ⟨C, hC, hbound⟩ := (particle_hessian_normalization hN c hc χ hχ).2.2
  refine ⟨C, hN, hc, hC, ?_⟩
  simpa only [AffineMetric.libraryPairs_energy, hsBoundaryDistance, hsChamber,
    particleChamber] using hbound

namespace Internal

variable (hN : 2 ≤ (N : ℕ)) (χ : HsPairPotentials N c) (hc : 0 < c)
local notation "μ" => (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))
include hN

/-- Arbitrary scalar components of compact vector tests in the proof of
Proposition 3.2 may be used in the weighted adjoint identity. -/
theorem test_integrationByParts (g : HsTestFunction N) (F : HsSobolev μ)
    (v : HsEuclidean N) :
    (∫ x, hsSmoothValue g.toFun x * inner ℝ (hsSobolevGradient μ F x) v ∂μ) =
      ∫ x, hsSobolevValue μ F x * hsSmoothValue
        (fun y => g.toFun y * fderiv ℝ (hsPairExpression χ) y v -
          fderiv ℝ g.toFun y v) x ∂μ := by
  let ℓ := EuclideanSpace.proj (𝕜 := ℝ) (⟨0, N.pos⟩ : Fin (N : ℕ))
  let ψ := fun y => periodicCutoff (ℓ y) * g.toFun y
  have hψ : ContDiff ℝ ∞ ψ := (contDiff_periodicCutoff.comp ℓ.contDiff).mul g.smooth
  have hψc : HasCompactSupport ψ :=
    hasCompactSupport_hsPeriodicCutoff_mul (g.tsupport_subset_chamber hN)
  have hψU : tsupport ψ ⊆ hsChamber N :=
    tsupport_mul_subset_right.trans (g.tsupport_subset_chamber hN)
  have hp : vectorPeriodize (hsRotationVector N) (hsRotationVector_ne_zero N) ψ hψc =
      g.toFun :=
    vectorPeriodize_periodicCutoff_mul (hsRotationVector_ne_zero N) ℓ
      (by simp [ℓ, hsRotationVector])
      (fun k x => by rw [← hsTranslate_eq_add_rotation]; exact g.periodic k x) hψc
  have hi := hsSobolev_periodized_integrationByParts hN χ hc F hψ hψc hψU v
  dsimp only at hi
  rwa [hp] at hi

/-- The compact adjoint coefficient from the proof of Proposition 3.2
is an actual L² function. No unguarded integral is used in passing to the limit. -/
theorem adjoint_memLp (g : HsTestFunction N) (v : HsEuclidean N) :
    MemLp (hsSmoothValue (fun y => g.toFun y *
      fderiv ℝ (hsPairExpression χ) y v - fderiv ℝ g.toFun y v)) 2 μ := by
  apply memLp_hsLiftPoint (f := fun y => g.toFun y *
    fderiv ℝ (hsPairExpression χ) y v - fderiv ℝ g.toFun y v) μ 2
  exact
    (continuous_hsLocalCoefficient χ g.smooth (g.tsupport_subset_chamber hN) v).continuousOn

/-- The compact weighted adjoint appearing in Proposition 3.2, as an
L² class on the particle quotient. -/
def adjoint (g : HsTestFunction N) (v : HsEuclidean N) : Lp ℝ 2 μ :=
  (adjoint_memLp hN χ hc g v).toLp _

/-- L² form of the compact adjoint identity in Proposition 3.2. -/
theorem adjoint_pairing (g : HsTestFunction N) (F : HsSobolev μ)
    (i : Fin (N : ℕ)) :
    inner ℝ ((EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ (hsSobolevGradient μ F))
        (hsSobolevValue μ (hsSobolevOfSmooth μ ⟨g.toFun, g.smoothOnClosure⟩)) =
      inner ℝ (hsSobolevValue μ F) (adjoint hN χ hc g (EuclideanSpace.single i 1)) := by
  rw [L2.inner_def, L2.inner_def]
  have hi := test_integrationByParts hN χ hc g F (EuclideanSpace.single i 1)
  have he : (∫ x, inner ℝ
      (((EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ (hsSobolevGradient μ F)) x)
      (hsSobolevValue μ (hsSobolevOfSmooth μ ⟨g.toFun, g.smoothOnClosure⟩) x) ∂μ) =
      ∫ x, hsSmoothValue g.toFun x *
        inner ℝ (hsSobolevGradient μ F x) (EuclideanSpace.single i 1) ∂μ := by
    apply integral_congr_ae
    filter_upwards [ContinuousLinearMap.coeFn_compLpL (EuclideanSpace.proj (𝕜 := ℝ) i)
      (hsSobolevGradient μ F), (g.smoothOnClosure.memLp_value μ).coeFn_toLp] with x hp hg
    rw [hp, show hsSobolevValue μ (hsSobolevOfSmooth μ
      ⟨g.toFun, g.smoothOnClosure⟩) x = hsSmoothValue g.toFun x from hg]
    simp [EuclideanSpace.inner_single_right]
  rw [he, hi]
  apply integral_congr_ae
  filter_upwards [(adjoint_memLp hN χ hc g (EuclideanSpace.single i 1)).coeFn_toLp] with x hx
  rw [show adjoint hN χ hc g (EuclideanSpace.single i 1) x = _ from hx, Real.inner_apply]

/-- The full compact vector adjoint in the proof of Proposition 3.2.
Its pairing is continuous in the scalar graph output. -/
def vectorAdjoint (h : HsVectorTest N) : Lp ℝ 2 μ :=
  ∑ i, adjoint hN χ hc (hsGradientSourceOfTest (h i)) (EuclideanSpace.single i 1)

/-- The weak derivatives of an arbitrary H¹ observable give the compact vector
adjoint pairing required in the proof of Proposition 3.2. -/
theorem vector_adjoint_pairing (h : HsVectorTest N) (F : HsSobolev μ) :
    hsNonGradientPairing μ (hsSobolevGradient μ F) (hsVectorJet χ hN hc μ h) =
      inner ℝ (hsSobolevValue μ F) (vectorAdjoint hN χ hc h) := by
  unfold hsNonGradientPairing
  rw [PiLp.inner_apply]
  change (∑ i, inner ℝ ((EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ
    (hsSobolevGradient μ F)) (hsSobolevValue μ (hsTestSobolev μ (h i)))) = _
  simp_rw [vectorAdjoint, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact adjoint_pairing hN χ hc (hsGradientSourceOfTest (h i)) F i

/-- Pointwise mixed commutator in the proof of Proposition 3.2.
The vector test is arbitrary and need not itself be a gradient. -/
theorem compact_mixed_integrand (f : HsTestFunction N) (h : HsVectorTest N)
    {x : HsEuclidean N} (hx : x ∈ hsChamber N) :
    vectorFormIntegrand χ (hsGradientTestTuple hN f) h x =
      ∑ i : Fin (N : ℕ), (inner ℝ (gradient (hsGradientTestDirection hN f
          (EuclideanSpace.single i 1)).toFun x) (gradient (h i).val x) +
        ((hsGradientTestDirection hN (hsLangevinTest hN χ f)
            (EuclideanSpace.single i 1)).toFun x -
          (hsLangevinTest hN χ (hsGradientTestDirection hN f
            (EuclideanSpace.single i 1))).toFun x) * (h i).val x) := by
  have hH := (hsPairExpression_contDiffOn χ).contDiffAt ((isOpen_hsChamber N).mem_nhds hx)
  have hs := hH.isSymmSndFDerivAt (by simp)
  have hex := hsCommutator_linear_coordinates
    ((fderiv ℝ (fderiv ℝ (hsPairExpression χ)) x).flip (gradient f.toFun x))
    (hsTestVector h x)
  change fderiv ℝ (fderiv ℝ (hsPairExpression χ)) x (hsTestVector h x)
    (gradient f.toFun x) = _ at hex
  unfold vectorFormIntegrand
  rw [hsTestVector_gradientTestTuple, hs _ _, hex, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi := langevin_direction_commutator hH f.smooth (EuclideanSpace.single i 1)
  change inner ℝ (gradient (hsGradientTestDirection hN f
      (EuclideanSpace.single i 1)).toFun x) (gradient (h i).val x) +
      fderiv ℝ (fderiv ℝ (hsPairExpression χ)) x (EuclideanSpace.single i 1)
        (gradient f.toFun x) * (h i).val x = _
  rw [← hi]
  rfl

/-- Compact mixed equation of Proposition 3.2, prior to the scalar
graph limit. Integration by parts cancels the componentwise Langevin terms. -/
theorem compact_mixed (f : HsTestFunction N) (h : HsVectorTest N) :
    hsVectorSobolevForm χ hN hc μ (hsVectorJetElt χ hN hc μ (hsGradientTestTuple hN f))
        (hsVectorJetElt χ hN hc μ h) =
      inner ℝ ((memLp_hsLangevin hN χ f μ).toLp (hsLangevin χ f))
        (vectorAdjoint hN χ hc h) := by
  let L := hsLangevinTest hN χ f
  let d (i : Fin (N : ℕ)) := hsGradientTestDirection hN f (EuclideanSpace.single i 1)
  let e (i : Fin (N : ℕ)) := hsGradientTestDirection hN L (EuclideanSpace.single i 1)
  let t (i : Fin (N : ℕ)) := hsGradientSourceOfTest (h i)
  have hgrad (i) : MemLp (hsSmoothGradient ⟨(d i).toFun, (d i).smoothOnClosure⟩) 2 μ :=
    (d i).smoothOnClosure.memLp_gradient μ
  have htgrad (i) : MemLp (hsSmoothGradient ⟨(t i).toFun, (t i).smoothOnClosure⟩) 2 μ :=
    (t i).smoothOnClosure.memLp_gradient μ
  have hgradI (i) : Integrable (fun y => inner ℝ
      (gradient (d i).toFun (hsLiftPoint N y)) (gradient (h i).val (hsLiftPoint N y))) μ :=
    by
      have hi := L2.integrable_inner (𝕜 := ℝ) ((hgrad i).toLp _) ((htgrad i).toLp _)
      apply hi.congr
      filter_upwards [(hgrad i).coeFn_toLp, (htgrad i).coeFn_toLp] with y h1 h2
      rw [h1, h2]
      rfl
  have hval (i) : MemLp (hsTestOnQuotient (t i)) 2 μ := (t i).smoothOnClosure.memLp_value μ
  have he (i) : MemLp (hsTestOnQuotient (e i)) 2 μ := (e i).smoothOnClosure.memLp_value μ
  have hL (i) : MemLp (hsLangevin χ (d i)) 2 μ := memLp_hsLangevin hN χ (d i) μ
  have hp (i) : Integrable (fun y => (hsTestOnQuotient (e i) y -
      hsLangevin χ (d i) y) * hsTestOnQuotient (t i) y) μ :=
    ((he i).sub (hL i)).integrable_mul (hval i)
  have hcancel (i) : (∫ y, inner ℝ (gradient (d i).toFun (hsLiftPoint N y))
        (gradient (h i).val (hsLiftPoint N y)) +
        (hsTestOnQuotient (e i) y - hsLangevin χ (d i) y) *
          hsTestOnQuotient (t i) y ∂μ) =
      ∫ y, hsTestOnQuotient (e i) y * hsTestOnQuotient (t i) y ∂μ := by
    rw [integral_add (hgradI i) (hp i)]
    have hibp := hsIntegrationByParts_smooth hN χ hc (d i) (t i)
    rw [hsGradient_dirichlet_tests] at hibp
    change (∫ y, hsLangevin χ (d i) y * hsTestOnQuotient (t i) y ∂μ) =
      ∫ y, inner ℝ (gradient (d i).toFun (hsLiftPoint N y))
        (gradient (h i).val (hsLiftPoint N y)) ∂μ at hibp
    rw [← hibp]
    simp_rw [sub_mul]
    rw [integral_sub (f := fun y => hsTestOnQuotient (e i) y * hsTestOnQuotient (t i) y)
      (g := fun y => hsLangevin χ (d i) y * hsTestOnQuotient (t i) y)
      ((he i).integrable_mul (hval i))
      ((hL i).integrable_mul (hval i))]
    ring
  rw [hsVectorSobolevForm_jet]
  change (∫ y, vectorFormIntegrand χ (hsGradientTestTuple hN f) h (hsLiftPoint N y) ∂μ) = _
  simp_rw [compact_mixed_integrand hN χ f h (hsLiftPoint_mem_chamber N _)]
  change (∫ y, ∑ i, (inner ℝ (gradient (d i).toFun (hsLiftPoint N y))
    (gradient (h i).val (hsLiftPoint N y)) +
      (hsTestOnQuotient (e i) y - hsLangevin χ (d i) y) *
        hsTestOnQuotient (t i) y) ∂μ) = _
  rw [integral_finsetSum (f := fun i y =>
    inner ℝ (gradient (d i).toFun (hsLiftPoint N y)) (gradient (h i).val (hsLiftPoint N y)) +
      (hsTestOnQuotient (e i) y - hsLangevin χ (d i) y) * hsTestOnQuotient (t i) y)
      _ (fun i _ => (hgradI i).add (hp i))]
  simp_rw [hcancel]
  have hpair := vector_adjoint_pairing hN χ hc h
    (hsSobolevOfSmooth μ ⟨L.toFun, L.smoothOnClosure⟩)
  have hvalL : hsSobolevValue μ (hsSobolevOfSmooth μ ⟨L.toFun, L.smoothOnClosure⟩) =
      (memLp_hsLangevin hN χ f μ).toLp (hsLangevin χ f) := by
    apply Lp.ext
    exact (L.smoothOnClosure.memLp_value μ).coeFn_toLp.trans
      (memLp_hsLangevin hN χ f μ).coeFn_toLp.symm
  rw [← hvalL, ← hpair, hsNonGradientPairing_eq_integral]
  rw [← integral_finsetSum (f := fun i y =>
    hsTestOnQuotient (e i) y * hsTestOnQuotient (t i) y)
    _ (fun i _ => (he i).integrable_mul (hval i))]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr (fun i =>
      hsSobolevValue_hsTestSobolev μ (h i)),
    (L.smoothOnClosure.memLp_gradient μ).coeFn_toLp] with y ht hg
  apply Finset.sum_congr rfl
  intro i _
  rw [show hsSobolevGradient μ (hsSobolevOfSmooth μ
      ⟨L.toFun, L.smoothOnClosure⟩) y = gradient L.toFun (hsLiftPoint N y) from hg,
    hsJetValue_hsVectorJet, ht i]
  exact congrArg (· * (h i).val (hsLiftPoint N y))
    (hsGradientTestTuple_apply hN L (hsLiftPoint N y) i)

/-- Centering the scalar source does not change its compact adjoint pairing in
Proposition 3.2. The adjoint annihilates the unit function. -/
theorem center_adjoint (h : HsVectorTest N) (F : Lp ℝ 2 μ) :
    inner ℝ (poissonCenter μ F) (vectorAdjoint hN χ hc h) =
      inner ℝ F (vectorAdjoint hN χ hc h) := by
  have hi := vector_adjoint_pairing hN χ hc h (hsPoissonUnit μ)
  rw [hsPoissonUnit_gradient, hsNonGradientPairing, map_zero, inner_zero_left,
    hsPoissonUnit_value] at hi
  rw [poissonCenter, inner_sub_left, inner_smul_left, ← hi, mul_zero, sub_zero]

/-- The operator-core approximation used in Proposition 3.2, using
the companion collision theorem, with no assumed graph approximants. -/
theorem scalar_graph_approximation {C : ℝ} (hadm : HsAdmissible χ C)
    (φ : HsSobolev μ) (a : Lp ℝ 2 μ) (hφ : (φ, a) ∈ hsNeumannGraph μ) :
    ∃ f : ℕ → HsTestFunction N,
      Tendsto (fun k => hsSobolevValue μ
        (hsSobolevOfSmooth μ ⟨(f k).toFun, (f k).smoothOnClosure⟩))
        atTop (𝓝 (hsSobolevValue μ φ)) ∧
      Tendsto (fun k => (memLp_hsLangevin hN χ (f k) μ).toLp (hsLangevin χ (f k)))
        atTop (𝓝 a) := by
  have he := (scalar_boundary_core_L3219_quotient_real χ hc hadm).1
  have hp : (hsSobolevValue μ φ, a) ∈
      closure ((hsTestL2Operator χ hc).graph : Set (Lp ℝ 2 μ × Lp ℝ 2 μ)) := by
    change (hsSobolevValue μ φ, a) ∈ (hsTestL2Operator χ hc).graph.topologicalClosure
    rw [(hsTestL2Operator_isClosable χ hc).graph_closure_eq_closure_graph, he,
      hsNeumannL2Operator_graph, mem_hsNeumannL2Graph]
    exact ⟨φ, rfl, hφ⟩
  obtain ⟨p, hpmem, hplim⟩ := mem_closure_iff_seq_limit.mp hp
  have hex (k : ℕ) : ∃ f : HsTestFunction N,
      hsSobolevValue μ (hsSobolevOfSmooth μ ⟨f.toFun, f.smoothOnClosure⟩) = (p k).1 :=
    (mem_hsTestL2Domain μ _).mp ((mem_hsTestL2Operator_graph χ hc _ _).mp (hpmem k)).1
  choose f hf using hex
  have ha (k : ℕ) : (memLp_hsLangevin hN χ (f k) μ).toLp (hsLangevin χ (f k)) = (p k).2 :=
    (hsTestL2Operator χ hc).mem_graph_snd_inj
      (hsTestL2Operator_on_test hN χ hc (f k)) (hpmem k) (hf k)
  refine ⟨f, ?_, ?_⟩
  · simpa only [hf, Function.comp_def] using (continuous_fst.tendsto _).comp hplim
  · simpa only [ha, Function.comp_def] using (continuous_snd.tendsto _).comp hplim

/-- Periodicity gives zero *expected* rotation derivative on the particle test
core in Proposition 3.2. No pointwise tangency is asserted. -/
theorem test_gradient_mean (f : HsTestFunction N) :
    hsL2Mean μ (hsSobolevGradient μ (hsSobolevOfSmooth μ
      ⟨f.toFun, f.smoothOnClosure⟩)) = 0 := by
  let e := hsRotationVector N
  have hcoord (g : HsEuclidean N → ℝ) (x : HsEuclidean N) :
      fderiv ℝ g x e = ∑ i, gradient g x i := by
    calc
      _ = inner ℝ (gradient g x) e := inner_gradient_left.symm
      _ = _ := by
        rw [PiLp.inner_apply]
        simp only [e, hsRotationVector, PiLp.toLp_apply, Real.inner_apply, mul_one]
  have hH (y : HsConfiguration N) : fderiv ℝ (hsPairExpression χ) (hsLiftPoint N y) e = 0 := by
    rw [hcoord]
    exact boundaryCore_gradient_sum χ (hsLiftPoint_mem_chamber N y)
  have hu : (hsSobolevValue μ (hsPoissonUnit μ) : HsConfiguration N → ℝ) =ᵐ[μ]
      fun _ => 1 := by
    rw [hsPoissonUnit_value]
    exact Lp.coeFn_const 2 μ (1 : ℝ)
  have hi := test_integrationByParts hN χ hc f (hsPoissonUnit μ) e
  have hleft : (∫ x, hsSmoothValue f.toFun x *
      inner ℝ (hsSobolevGradient μ (hsPoissonUnit μ) x) e ∂μ) = 0 := by
    rw [hsPoissonUnit_gradient]
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero (HsEuclidean N) 2 μ] with x hx
    simp only [hx, Pi.zero_apply, inner_zero_left, mul_zero]
  have hright : (∫ x, hsSobolevValue μ (hsPoissonUnit μ) x * hsSmoothValue
      (fun y => f.toFun y * fderiv ℝ (hsPairExpression χ) y e - fderiv ℝ f.toFun y e) x ∂μ) =
      -(∫ x, fderiv ℝ f.toFun (hsLiftPoint N x) e ∂μ) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [hu] with x hx
    simp only [hx, hsSmoothValue, hH, mul_zero, zero_sub, one_mul]
  rw [hleft, hright] at hi
  rw [hsL2Mean_eq_integral]
  have hm : (∫ x, ∑ i, hsSobolevGradient μ
      (hsSobolevOfSmooth μ ⟨f.toFun, f.smoothOnClosure⟩) x i ∂μ) =
      ∫ x, fderiv ℝ f.toFun (hsLiftPoint N x) e ∂μ := by
    apply integral_congr_ae
    filter_upwards [(f.smoothOnClosure.memLp_gradient μ).coeFn_toLp] with x hx
    change (∑ i, hsSobolevGradient μ
      (hsSobolevOfSmooth μ ⟨f.toFun, f.smoothOnClosure⟩) x i) = _
    rw [show hsSobolevGradient μ (hsSobolevOfSmooth μ
      ⟨f.toFun, f.smoothOnClosure⟩) x = gradient f.toFun (hsLiftPoint N x) from hx, hcoord]
  rw [hm]
  exact neg_eq_zero.mp hi.symm

/-- The expected rotation normalization in Proposition 3.2 holds for
every particle H¹ function, by density of the companion smooth core. -/
theorem gradient_mean {C : ℝ} (hadm : HsAdmissible χ C) (F : HsSobolev μ) :
    hsL2Mean μ (hsSobolevGradient μ F) = 0 := by
  have hd := (scalar_boundary_core_L3219_quotient_real χ hc hadm).2.2.2
  have hclosed : IsClosed {G : HsSobolev μ | hsL2Mean μ (hsSobolevGradient μ G) = 0} :=
    isClosed_eq ((hsL2Mean μ).continuous.comp (hsSobolevGradient μ).continuous) continuous_const
  apply (hclosed.closure_subset_iff.mpr ?_) (hd F)
  rintro _ ⟨g, rfl⟩
  exact test_gradient_mean hN χ hc g

/-- The compact mixed identity extends to all vector-energy tests in the proof
of Proposition 3.2. This internal helper isolates the density step. -/
theorem full_equation_of_compact (u : HsVectorSobolev χ hN hc μ)
    (v : Lp (HsEuclidean N) 2 μ)
    (hcompact : ∀ h : HsVectorTest N,
      hsVectorSobolevForm χ hN hc μ u (hsVectorJetElt χ hN hc μ h) =
        hsNonGradientPairing μ v (hsVectorJet χ hN hc μ h)) :
    HsNonGradientSolves χ hN hc v u := by
  intro w
  obtain ⟨h, hh⟩ := exists_seq_hsVectorJet χ hN hc μ w
  have hh' : Tendsto (fun k => hsVectorJetElt χ hN hc μ (h k)) atTop (𝓝 w) :=
    tendsto_subtype_rng.mpr hh
  have hleft := ((hsNonGradientFullBilinear χ hN hc μ u).continuous.tendsto w).comp hh'
  have hright := ((hsNonGradientForcing χ hN hc μ v).continuous.tendsto w).comp hh'
  have he (k : ℕ) : hsNonGradientFullBilinear χ hN hc μ u
      (hsVectorJetElt χ hN hc μ (h k)) =
      hsNonGradientForcing χ hN hc μ v (hsVectorJetElt χ hN hc μ (h k)) := by
    exact (hsNonGradientFullBilinear_eq χ hN hc μ _ _).trans (hcompact (h k))
  have hleft' := hleft.congr' (Eventually.of_forall he)
  exact ((hsNonGradientFullBilinear_eq χ hN hc μ u w).symm.trans
    (tendsto_nhds_unique hleft' hright))

/-- Passing the compact adjoint identity through scalar and vector graph
convergence proves the full equation of Proposition 3.2.
Only scalar operator outputs converge. Their gradients are not assumed to. -/
theorem equation_of_graph_limit (F : HsSobolev μ) (f : ℕ → HsTestFunction N)
    (u : HsVectorSobolev χ hN hc μ)
    (ha : Tendsto (fun k => (memLp_hsLangevin hN χ (f k) μ).toLp
      (hsLangevin χ (f k))) atTop (𝓝 (poissonCenter μ (hsSobolevValue μ F))))
    (hu : Tendsto (fun k => hsVectorJetElt χ hN hc μ (hsGradientTestTuple hN (f k)))
      atTop (𝓝 u)) :
    HsNonGradientSolves χ hN hc (hsSobolevGradient μ F) u := by
  apply full_equation_of_compact hN χ hc u (hsSobolevGradient μ F)
  intro h
  have hleft :=
    (((hsNonGradientFullBilinear χ hN hc μ).flip
      (hsVectorJetElt χ hN hc μ h)).continuous.tendsto u).comp hu
  simp only [ContinuousLinearMap.flip_apply, Function.comp_def] at hleft
  have hright := ha.inner (𝕜 := ℝ) (tendsto_const_nhds (x := vectorAdjoint hN χ hc h))
  have he (k : ℕ) : hsNonGradientFullBilinear χ hN hc μ
      (hsVectorJetElt χ hN hc μ (hsGradientTestTuple hN (f k)))
      (hsVectorJetElt χ hN hc μ h) =
        inner ℝ ((memLp_hsLangevin hN χ (f k) μ).toLp (hsLangevin χ (f k)))
          (vectorAdjoint hN χ hc h) :=
    (hsNonGradientFullBilinear_eq χ hN hc μ _ _).trans (compact_mixed hN χ hc (f k) h)
  have hleft' := hleft.congr' (Eventually.of_forall he)
  exact (hsNonGradientFullBilinear_eq χ hN hc μ _ _).symm.trans
    ((tendsto_nhds_unique hleft' hright).trans
      ((center_adjoint hN χ hc h (hsSobolevValue μ F)).trans
        (vector_adjoint_pairing hN χ hc h F).symm))

end Internal

end Riesz2.ParticleRepresentation
