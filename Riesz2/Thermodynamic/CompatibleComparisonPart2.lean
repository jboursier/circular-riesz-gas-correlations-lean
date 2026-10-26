/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.CompatibleComparison
public import Riesz2.ToMathlib.ProperSimplexProjection
public import Riesz2.ToMathlib.RectangularFormTransport

/-!
# Compatible comparison: carrier and tangent transport

Full-domain bridges for the covariance representation in the proof of Proposition 6.6.
All transport uses the existing scalar form, its domain equivalence, and the weak
equation.
-/

public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter ProbabilityTheory Matrix
open scoped BigOperators ENNReal MatrixOrder ContDiff

namespace Riesz2.CompatibleComparison

section Frame

/-- The fixed-length tangent space and the zero-sum Euclidean space
are the same submodule. Only the total affine mass changes. Subsection 6.1, the proof of Proposition 6.6. -/
theorem tangent_eq_gap_internal (a : ℕ) :
    AffineSimplex.Tangent a = gapTangentSpace a.succPNat := by
  ext z
  exact AffineSimplex.mem_hsOrthSubspace_iff a z

/-- See the proof of Proposition 6.6 in the paper: construct the rectangular matrix
of the specified orthonormal frame. It includes precisely the ambient
tangent components, and has no arbitrary choice of a second frame. -/
theorem frame_matrix_internal (a : ℕ)
    (frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a)) :
    ∃ A : Matrix (Fin (a+1)) (Fin a) ℝ,
      A.transpose*A = 1 ∧ A.mulVecLin.range = zeroSumComponents (Fin (a+1)) ∧
        ∀ t : Fin a → ℝ, A *ᵥ t = (frame.symm (WithLp.toLp 2 t)).val := by
  let b : OrthonormalBasis (Fin a) ℝ (AffineSimplex.Tangent a) :=
    OrthonormalBasis.ofRepr frame
  let A : Matrix (Fin (a+1)) (Fin a) ℝ := fun i k => (b k).val i
  have hact (t : Fin a → ℝ) : A *ᵥ t = (frame.symm (WithLp.toLp 2 t)).val := by
    have hh := congrArg (fun z : AffineSimplex.Tangent a => z.val)
      (b.sum_repr_symm (WithLp.toLp 2 t))
    ext i
    simpa only [A, Matrix.mulVec, dotProduct, Submodule.coe_sum, Submodule.coe_smul,
      WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, mul_comm] using
      congrArg (fun z : EuclideanSpace ℝ (Fin (a+1)) => z i) hh
  refine ⟨A, ?_, ?_, hact⟩
  · ext i j
    have hh := b.inner_eq_ite i j
    change (∑ k, (b i).val k*(b j).val k) = if i = j then 1 else 0
    rw [Submodule.coe_inner,PiLp.inner_apply] at hh
    simpa only [Real.inner_apply] using hh
  · ext t
    constructor
    · rintro ⟨v,rfl⟩
      change (∑ i, (A *ᵥ v) i) = 0
      rw [hact]
      exact (AffineSimplex.mem_hsOrthSubspace_iff a _).mp (frame.symm (WithLp.toLp 2 v)).property
    · intro ht
      let z : AffineSimplex.Tangent a := ⟨WithLp.toLp 2 t,
        (AffineSimplex.mem_hsOrthSubspace_iff a _).mpr ht⟩
      refine ⟨WithLp.ofLp (frame z), ?_⟩
      change A *ᵥ WithLp.ofLp (frame z) = t
      rw [hact]
      simp only [WithLp.toLp_ofLp,LinearIsometryEquiv.symm_apply_apply]
      rfl

/-- See the proof of Proposition 6.6 in the paper: the actual ambient Hessian
compresses to the Hessian of its pullback by the specified length-simplex
chart. This applies to the physical interpolant, including its factor β. -/
theorem frame_hessian_internal (a : ℕ) (L : ℝ)
    (frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
    (A : Matrix (Fin (a+1)) (Fin a) ℝ)
    (hA : ∀ t : Fin a → ℝ, A *ᵥ t = (frame.symm (WithLp.toLp 2 t)).val)
    (W : EuclideanSpace ℝ (Fin (a+1)) → ℝ) (x : EuclideanSpace ℝ (Fin a))
    (hW : ContDiffAt ℝ ∞ W (AffineSimplex.centredChart a L (frame.symm x))) :
    A.transpose*hessianMatrix W (AffineSimplex.centredChart a L (frame.symm x))*A =
      hessianMatrix (fun y => W (AffineSimplex.centredChart a L (frame.symm y))) x := by
  let B := (AffineSimplex.Tangent a).subtypeL.comp frame.symm.toContinuousLinearEquiv.toContinuousLinearMap
  change ContDiffAt ℝ ∞ W (B x+AffineSimplex.centre a L) at hW
  have hs : ContDiffAt ℝ ∞ (fun y => W (B y+AffineSimplex.centre a L)) x :=
    hW.comp x (B.contDiff.add contDiff_const).contDiffAt
  have hb (i : Fin a) : B (EuclideanSpace.single i 1) = WithLp.toLp 2 (fun j => A j i) := by
    apply PiLp.ext
    intro j
    have hh := congrFun (hA (Pi.single i 1)) j
    change (frame.symm (EuclideanSpace.single i 1)).val j = A j i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hh.symm

  change A.transpose*hessianMatrix W (B x+AffineSimplex.centre a L)*A =
    hessianMatrix (fun y => W (B y+AffineSimplex.centre a L)) x
  ext i j
  rw [Intrinsic.hessianMatrix_eq_second hs,
    AffineMetricTransport.hessian_comp_affine B (AffineSimplex.centre a L)
      (hW.of_le (by norm_num)), hb, hb,
    Intrinsic.hessianMatrix_bilinear hW]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
  rw [Finset.sum_comm]

end Frame

section Embedding

variable {X Z : Type} [MeasurableSpace X] [MeasurableSpace Z]
  (μ : Measure X) (f : X → Z) (hf : MeasurableEmbedding f)
  (Q : ScalarFormData μ)

local notation "Q'" => ScalarFormEmbedding.form μ f hf Q
local notation "D" => ScalarFormEmbedding.domainEquiv μ f hf Q
local notation "T" => ScalarFormEmbedding.pullback μ f hf

/-- See the proof of Proposition 6.6 in the paper: scalar carrier transport preserves
the entire range-constrained matrix-energy domain, for unbounded matrices. -/
theorem weighted_domain_embedding_iff_internal {ι : Type} [Fintype ι]
    (M : Z → Matrix ι ι ℝ) (S : Submodule ℝ (ι → ℝ)) (u : ι → Q'.1) :
    WeightedFormDomain Q' M S u ↔
      WeightedFormDomain Q (M ∘ f) S (fun i => D (u i)) := by
  have hc := ae_all_iff.mpr (fun i => ScalarFormEmbedding.pullback_ae μ f hf (u i).val)
  have hm : (∀ᵐ z ∂μ.map f, (fun i => (u i).val z) ∈ S) ↔
      ∀ᵐ x ∂μ, (fun i => (D (u i)).val x) ∈ S := by
    rw [hf.ae_map_iff]
    apply eventually_congr
    filter_upwards [hc] with x hx
    have he : (fun i => (u i).val (f x)) = (fun i => (D (u i)).val x) :=
      funext fun i => (hx i).symm
    rw [he]
  exact and_congr hm
    (InterpolationTransport.matrixFieldPair_integrable_iff μ f hf ι M _ _)

/-- See the proof of Proposition 6.6 in the paper: the actual weak equation,
including every finite-energy test and its cross-integrability clause,
transports together with the source and scalar domain. -/
theorem weak_equation_embedding_iff_internal {ι : Type} [Fintype ι]
    (M : Z → Matrix ι ι ℝ) (S : Submodule ℝ (ι → ℝ))
    (v : ι → Lp ℝ 2 (μ.map f)) (u : ι → Q'.1) :
    WeightedWeakSolution Q' M S v u ↔
      WeightedWeakSolution Q (M ∘ f) S (fun i => T (v i)) (fun i => D (u i)) := by
  have he (w : ι → Q'.1) :
      (∑ i, Q'.2 (u i) (w i)) +
        (∫ z, matrixFieldPair M (fun i => (u i).val) (fun i => (w i).val) z ∂μ.map f) =
      (∑ i, Q.2 (D (u i)) (D (w i))) +
        ∫ x, matrixFieldPair (M ∘ f) (fun i => (D (u i)).val)
          (fun i => (D (w i)).val) x ∂μ := by
    rw [InterpolationTransport.matrixFieldPair_integral μ f hf]
    rfl
  have hs (w : ι → Q'.1) :
      (∑ i, inner ℝ (v i) (w i).val) =
        ∑ i, inner ℝ (T (v i)) (D (w i)).val := by
    apply Finset.sum_congr rfl
    intro i _
    exact ((T).inner_map_map _ _).symm
  constructor
  · rintro ⟨hu, hweak⟩
    refine ⟨(weighted_domain_embedding_iff_internal μ f hf Q M S u).mp hu, ?_⟩
    intro w hw
    let w' : ι → Q'.1 := fun i => (D).symm (w i)
    have hw' : WeightedFormDomain Q' M S w' :=
      (weighted_domain_embedding_iff_internal μ f hf Q M S w').mpr (by simpa [w'] using hw)
    obtain ⟨hi, hh⟩ := hweak w' hw'
    refine ⟨?_, ?_⟩
    · have := (InterpolationTransport.matrixFieldPair_integrable_iff μ f hf ι M _ _).mp hi
      change Integrable (matrixFieldPair (M ∘ f) (fun i => (D (u i)).val)
        (fun i => (D (w' i)).val)) μ at this
      simpa only [w', LinearEquiv.apply_symm_apply] using this
    · rw [he, hs] at hh
      simpa [w'] using hh
  · rintro ⟨hu, hweak⟩
    refine ⟨(weighted_domain_embedding_iff_internal μ f hf Q M S u).mpr hu, ?_⟩
    intro w hw
    obtain ⟨hi, hh⟩ := hweak (fun i => D (w i))
      ((weighted_domain_embedding_iff_internal μ f hf Q M S w).mp hw)
    refine ⟨(InterpolationTransport.matrixFieldPair_integrable_iff μ f hf ι M _ _).mpr hi, ?_⟩
    rwa [← he, ← hs] at hh

/-- See the proof of Proposition 6.6 in the paper: the ambient differential pairing
commutes with carrier transport on its actual L² representatives. -/
theorem pairing_integral_embedding_internal {ι : Type} [Fintype ι]
    (b : ι → Lp ℝ 2 (μ.map f)) (u : ι → Q'.1) :
    (∫ z, ∑ i, b i z * (u i).val z ∂μ.map f) =
      ∫ x, ∑ i, T (b i) x * (D (u i)).val x ∂μ := by
  rw [hf.integral_map]
  apply integral_congr_ae
  have hb := ae_all_iff.mpr (fun i => ScalarFormEmbedding.pullback_ae μ f hf (b i))
  have hu := ae_all_iff.mpr (fun i => ScalarFormEmbedding.pullback_ae μ f hf (u i).val)
  filter_upwards [hb,hu] with x hx hy
  apply Finset.sum_congr rfl
  intro i _
  change b i (f x) * (u i).val (f x) = T (b i) x * T (u i).val x
  rw [hx i,hy i]
  rfl

/-- See the proof of Proposition 6.6 in the paper: covariance itself transports,
with the same L² classes as the weak source and differential pairing. -/
theorem covariance_embedding_internal (G K : Lp ℝ 2 (μ.map f)) :
    covariance G K (μ.map f) = covariance (T G) (T K) μ := by
  rw [covariance_map (Lp.aestronglyMeasurable G) (Lp.aestronglyMeasurable K) hf.measurable.aemeasurable]
  unfold covariance
  rw [integral_congr_ae (ScalarFormEmbedding.pullback_ae μ f hf G),
    integral_congr_ae (ScalarFormEmbedding.pullback_ae μ f hf K)]
  apply integral_congr_ae
  filter_upwards [ScalarFormEmbedding.pullback_ae μ f hf G,
    ScalarFormEmbedding.pullback_ae μ f hf K] with x hx hy
  rw [hx,hy]

end Embedding

section Rectangular

open RectangularFormTransport

variable {X ι κ : Type*} [MeasurableSpace X] [Fintype ι] [Fintype κ]
  {μ : Measure X}

/-- See the proof of Proposition 6.6 in the paper: the ambient source pairs with a
tangent test through its rectangular transpose. The ambient source need not
itself have zero sum. -/
theorem source_adjoint_internal (Q : ScalarFormData μ) (A : Matrix ι κ ℝ)
    (v : ι → Lp ℝ 2 μ) (u : κ → Q.1) :
    (∑ i, inner ℝ (v i) (tupleMap A u i).val) =
      ∑ a, inner ℝ (tupleMap A.transpose v a) (u a).val := by
  simp_rw [tupleMap_value]
  simp only [tupleMap, LinearMap.coe_mk, AddHom.coe_mk,
    inner_sum, sum_inner, inner_smul_right, real_inner_smul_left,
    Matrix.transpose_apply]
  rw [Finset.sum_comm]

/-- See the proof of Proposition 6.6 in the paper: rectangular inclusion transports
the full weak equation with an arbitrary ambient source. In particular a
point source stays the literal point source used by Lemma 6.4. -/
theorem weak_equation_rectangular_iff_internal [DecidableEq κ]
    (Q : ScalarFormData μ) (A : Matrix ι κ ℝ) (hA : A.transpose * A = 1)
    (M : X → Matrix ι ι ℝ) (v : ι → Lp ℝ 2 μ) (u : κ → Q.1) :
    WeightedWeakSolution Q M A.mulVecLin.range v (tupleMap A u) ↔
      WeightedWeakSolution Q (fun x => A.transpose * M x * A) ⊤
        (tupleMap A.transpose v) u := by
  have hp (w : κ → Q.1) :
      matrixFieldPair M (fun i => (tupleMap A u i).val) (fun i => (tupleMap A w i).val) =ᵐ[μ]
        matrixFieldPair (fun x => A.transpose * M x * A)
          (fun a => (u a).val) (fun a => (w a).val) := by
    simp_rw [tupleMap_value]
    exact matrixFieldPair_tupleMap A M _ _
  constructor
  · rintro ⟨hu, hw⟩
    refine ⟨(weightedFormDomain_tupleMap Q A M u).mp hu, ?_⟩
    intro w hw'
    obtain ⟨hi, he⟩ := hw (tupleMap A w) ((weightedFormDomain_tupleMap Q A M w).mpr hw')
    refine ⟨hi.congr (hp w), ?_⟩
    rwa [diffusion_tupleMap Q A hA, integral_congr_ae (hp w), source_adjoint_internal Q A] at he
  · rintro ⟨hu, hw⟩
    refine ⟨(weightedFormDomain_tupleMap Q A M u).mpr hu, ?_⟩
    intro w hw'
    let z := tupleMap A.transpose w
    have hrec : tupleMap A z = w := tupleMap_right_inverse Q A hA w hw'.1
    have hz : WeightedFormDomain Q (fun x => A.transpose * M x * A) ⊤ z :=
      (weightedFormDomain_tupleMap Q A M z).mp (hrec.symm ▸ hw')
    obtain ⟨hi, he⟩ := hw z hz
    have hp' := hp z
    rw [hrec] at hp'
    refine ⟨hi.congr hp'.symm, ?_⟩
    rw [← hrec, diffusion_tupleMap Q A hA, integral_congr_ae (hp z), source_adjoint_internal Q A]
    exact he

/-- See the proof of Proposition 6.6 in the paper: unique solvability in compressed
coordinates gives unique ambient solutions for arbitrary sources, without
restricting either solution or test fields to gradients. -/
theorem ambient_existsUnique_internal [DecidableEq κ]
    (Q : ScalarFormData μ) (A : Matrix ι κ ℝ) (hA : A.transpose * A = 1)
    (M : X → Matrix ι ι ℝ) (v : ι → Lp ℝ 2 μ)
    (hsol : ∃! u : κ → Q.1,
      WeightedWeakSolution Q (fun x => A.transpose * M x * A) ⊤ (tupleMap A.transpose v) u) :
    ∃! u : ι → Q.1, WeightedWeakSolution Q M A.mulVecLin.range v u := by
  obtain ⟨u,hu,huniq⟩ := hsol
  refine ⟨tupleMap A u,
    (weak_equation_rectangular_iff_internal Q A hA M v u).mpr hu, ?_⟩
  intro w hw
  have hrec := tupleMap_right_inverse Q A hA w hw.1.1
  have ht : WeightedWeakSolution Q (fun x => A.transpose * M x * A) ⊤
      (tupleMap A.transpose v) (tupleMap A.transpose w) := by
    apply (weak_equation_rectangular_iff_internal Q A hA M v _).mp
    rwa [hrec]
  exact hrec.symm.trans (congrArg (tupleMap A) (huniq _ ht))

/-- See the proof of Proposition 6.6 in the paper: signed ambient pairings use
actual L² representatives and are integrable before any estimate. -/
theorem integral_pairing_adjoint_internal (Q : ScalarFormData μ) (A : Matrix ι κ ℝ)
    (b : ι → Lp ℝ 2 μ) (u : κ → Q.1) :
    Integrable (fun x => ∑ i, b i x * (tupleMap A u i).val x) μ ∧
      (∫ x, ∑ i, b i x * (tupleMap A u i).val x ∂μ) =
        ∑ a, inner ℝ (tupleMap A.transpose b a) (u a).val := by
  have hi (i : ι) : Integrable (fun x => b i x * (tupleMap A u i).val x) μ :=
    (Lp.memLp (b i)).integrable_mul (Lp.memLp (tupleMap A u i).val)
  refine ⟨integrable_finsetSum _ (fun i _ => hi i), ?_⟩
  rw [integral_finsetSum _ (fun i _ => hi i), ← source_adjoint_internal Q A b u]
  apply Finset.sum_congr rfl
  intro i _
  rw [L2.inner_def]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by simp only [Real.inner_apply]

end Rectangular

section Covariance

open RectangularFormTransport

/-- The Euclidean derivative pairing is the sum of its literal L² coordinate
pairings. Used in the proof of Proposition 6.6. -/
theorem derivative_coordinate_pairing_internal {d : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin d))}
    (g h : Lp (EuclideanSpace ℝ (Fin d)) 2 μ) :
    (∫ x, inner ℝ (g x) (h x) ∂μ) =
      ∑ i, inner ℝ (DifferentiatedPoisson.coordinateLp i g)
        (DifferentiatedPoisson.coordinateLp i h) := by
  have hg := ae_all_iff.mpr (fun i => DifferentiatedPoisson.coordinateLp_ae i g)
  have hh := ae_all_iff.mpr (fun i => DifferentiatedPoisson.coordinateLp_ae i h)
  have he : (fun x => inner ℝ (g x) (h x)) =ᵐ[μ]
      fun x => ∑ i, (DifferentiatedPoisson.coordinateLp i g) x *
        (DifferentiatedPoisson.coordinateLp i h) x := by
    filter_upwards [hg,hh] with x hx hy
    simp only [hx,hy,PiLp.inner_apply,Real.inner_apply]
  rw [integral_congr_ae he]
  have hi (i : Fin d) : Integrable (fun x =>
      (DifferentiatedPoisson.coordinateLp i g) x *
        (DifferentiatedPoisson.coordinateLp i h) x) μ :=
    (Lp.memLp (DifferentiatedPoisson.coordinateLp i g)).integrable_mul
      (Lp.memLp (DifferentiatedPoisson.coordinateLp i h))
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [L2.inner_def]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by simp only [Real.inner_apply]

/-- See the proof of Proposition 6.6 in the paper: the orthonormal covariance
solution lifts to a full-domain ambient tangent solution with its actual
ambient source and differential pairing. This internal bridge isolates
the two derivative identifications and Hessian compression to be checked
when applying it to a physical chart. -/
theorem ambient_covariance_lift_internal {d : ℕ} {ι : Type} [Fintype ι]
    {U : Set (EuclideanSpace ℝ (Fin d))} {μ : Measure (EuclideanSpace ℝ (Fin d))}
    {V : EuclideanSpace ℝ (Fin d) → ℝ}
    (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume μ U V)
    (hwell : ConditionalWellPosedness.EuclideanWellPosed hU hB hV)
    (A : Matrix ι (Fin d) ℝ) (hA : A.transpose * A = 1)
    (M : EuclideanSpace ℝ (Fin d) → Matrix ι ι ℝ)
    (hM : (fun x => A.transpose * M x * A) =ᵐ[μ] hessianMatrix V)
    (G K : ScalarForm.Domain (IntrinsicScalarCore.jet hU hB hV))
    (v b : ι → Lp ℝ 2 μ)
    (hv : tupleMap A.transpose v = fun i =>
      DifferentiatedPoisson.coordinateLp i (ScalarForm.deriv _ G))
    (hb : tupleMap A.transpose b = fun i =>
      DifferentiatedPoisson.coordinateLp i (ScalarForm.deriv _ K)) :
    ∃ u : ι → (IntrinsicScalarCore.form hU hB hV).1,
      WeightedWeakSolution (IntrinsicScalarCore.form hU hB hV) M A.mulVecLin.range v u ∧
      Integrable (fun x => ∑ i, b i x * (u i).val x) μ ∧
      covariance (ScalarForm.value _ G) (ScalarForm.value _ K) μ =
        ∫ x, ∑ i, b i x * (u i).val x ∂μ := by
  obtain ⟨ψ,u,_hm,_hg,hu,hcoord,hcov⟩ := hwell.1 G
  let Q := IntrinsicScalarCore.form hU hB hV
  have hu' : WeightedWeakSolution Q (fun x => A.transpose * M x * A) ⊤
      (tupleMap A.transpose v) u := by
    rw [hv]
    exact (MatrixFieldTransport.weak_congr Q hM ⊤ _ u).mpr hu
  refine ⟨tupleMap A u,
    (weak_equation_rectangular_iff_internal Q A hA M v u).mpr hu',
    (integral_pairing_adjoint_internal Q A b u).1, ?_⟩
  rw [(hcov K).2, derivative_coordinate_pairing_internal,
    (integral_pairing_adjoint_internal Q A b u).2, hb]
  apply Finset.sum_congr rfl
  intro i _
  rw [hcoord i, real_inner_comm]

/-- See the proof of Proposition 6.6 in the paper: after identifying the chart
source and differential, the covariance is the sum of the pairings with
the actual ambient point-source solutions. The full tangent uniqueness
and finite-superposition steps use the comparison API. -/
theorem ambient_covariance_point_sources_internal {d : ℕ} (n : ℕ+)
    {U : Set (EuclideanSpace ℝ (Fin d))} {μ : Measure (EuclideanSpace ℝ (Fin d))}
    {V : EuclideanSpace ℝ (Fin d) → ℝ}
    (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume μ U V)
    (hwell : ConditionalWellPosedness.EuclideanWellPosed hU hB hV)
    (A : Matrix (Fin (n : ℕ)) (Fin d) ℝ) (hA : A.transpose*A = 1)
    (hArange : A.mulVecLin.range = zeroSumComponents (Fin (n : ℕ)))
    (M : EuclideanSpace ℝ (Fin d) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (hM : (fun x => A.transpose*M x*A) =ᵐ[μ] hessianMatrix V)
    (hpos : ∀ᵐ x ∂μ, (M x).PosSemidef)
    (hmeas : ∀ i j, Measurable (fun x => M x i j))
    (a : ℝ) (ha : 0 < a)
    (hlower : ∀ᵐ x ∂μ, ∀ t ∈ zeroSumComponents (Fin (n : ℕ)),
      a*(∑ i, t i^2) ≤ ∑ i, ∑ j, t i*M x i j*t j)
    (G K : ScalarForm.Domain (IntrinsicScalarCore.jet hU hB hV))
    (J : Finset (Fin (n : ℕ))) (χ b : Fin (n : ℕ) → Lp ℝ 2 μ)
    (hv : tupleMap A.transpose (fun i => if i ∈ J then χ i else 0) = fun i =>
      DifferentiatedPoisson.coordinateLp i (ScalarForm.deriv _ G))
    (hb : tupleMap A.transpose b = fun i =>
      DifferentiatedPoisson.coordinateLp i (ScalarForm.deriv _ K))
    (ψ : Fin (n : ℕ) → Fin (n : ℕ) → (IntrinsicScalarCore.form hU hB hV).1)
    (hψ : ∀ i ∈ J, WeightedWeakSolution (IntrinsicScalarCore.form hU hB hV)
      M (zeroSumComponents (Fin (n : ℕ))) (fun j => if j = i then χ i else 0) (ψ i)) :
    covariance (ScalarForm.value _ G) (ScalarForm.value _ K) μ =
      ∑ i ∈ J, ∫ x, ∑ j, b j x*(ψ i j).val x ∂μ := by
  obtain ⟨u,hu,_hint,hcov⟩ := ambient_covariance_lift_internal hU hB hV hwell
    A hA M hM G K (fun i => if i ∈ J then χ i else 0) b hv hb
  rw [hArange] at hu
  have he := point_sources_superpose_internal
    (IntrinsicScalarCore.form hU hB hV) (IntrinsicScalarCore.closed_dirichlet hU hB hV)
      n M hpos hmeas a ha hlower J χ ψ hψ u hu
  rw [hcov,he]
  have hval : (fun j => (∑ i ∈ J, ψ i j).val) =
      ∑ i ∈ J, (fun j => (ψ i j).val) := by
    funext j
    simp only [Finset.sum_apply,Submodule.coe_sum]
  simp only [Finset.sum_apply]
  change (∫ x, ∑ j, b j x*(fun j => (∑ i ∈ J, ψ i j).val) j x ∂μ) = _
  rw [hval]
  exact WeightedWeakSuperposition.pairing_finset_sum J b (fun i j => (ψ i j).val)

end Covariance

section Composition

/-- The integrated comparison in the proof of Proposition 6.6 assumes the two
conclusions of Lemma 6.4 and the physical covariance identity `hid`.
Constants precede the size, laws, time, source coordinates and observable
bounds. The polynomial supremum loss and both exceptional terms are
absorbed with the original tail power. -/
theorem integrated_comparison_from_decay_internal
    (s : ℝ) (hs : 0 < s) (Ab Kb T C U κ κb ε c ct δ r bpower : ℝ)
    (hAb : 0 < Ab) (hKb : 0 ≤ Kb) (hT : 0 ≤ T) (hC : 0 < C) (hU : 0 ≤ U)
    (hc : 0 < c) (hct : 0 < ct) (hδ : 0 < δ) :
    ∃ K cf : ℝ, 0 < K ∧ 0 < cf ∧
    ∀ (n N : ℕ+), (n : ℝ)^(2/s) ≤ (N : ℝ) →
    ∀ (X : Type) [MeasurableSpace X] (ν : ℝ → Measure X)
      [∀ t, IsProbabilityMeasure (ν t)]
      (J : Finset (Fin (n : ℕ)))
      (χ : (t : ℝ) → Fin (n : ℕ) → BoundedL2Pairings.boundedSubmodule (ν t))
      (ψ : (t : ℝ) → Fin (n : ℕ) → Fin (n : ℕ) → Lp ℝ 2 (ν t))
      (b : ℝ → Fin (n : ℕ) → X → ℝ) (W : ℝ → X → ℝ)
      (good : ℝ → Set X) (A B : Fin (n : ℕ) → ℝ)
      (β : ℝ) (_hβ : 0 ≤ β) (h : ℝ → ℝ),
      (∀ i ∈ J, 0 ≤ A i) → (∀ i ∈ J, 0 ≤ B i) →
      (∀ t ∈ Icc (0 : ℝ) 1, MeasurableSet (good t)) →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ j, AEStronglyMeasurable (b t j) (ν t)) →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ i ∈ J,
        ∀ᵐ x ∂(ν t).restrict (good t), |(χ t i).val x| ≤ A i) →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ i ∈ J,
        ∀ᵐ x ∂ν t, |(χ t i).val x| ≤ B i) →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ j,
        ∀ᵐ x ∂(ν t).restrict (good t), |b t j x| ≤
          (Ab*(n : ℝ)^(κb*ε))*(InteractionDifferential.boundaryWeight s n j+(n : ℝ)*(N : ℝ)^(-s))) →
      (∀ t ∈ Icc (0 : ℝ) 1, IntegrableOn (W t) (good t)ᶜ (ν t)) →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ j,
        ∀ᵐ x ∂(ν t).restrict (good t)ᶜ, b t j x^2 ≤ (Kb*((n : ℝ)^bpower)^2)*W t x) →
      (∀ t ∈ Icc (0 : ℝ) 1,
        (∫ x in (good t)ᶜ, W t x ∂ν t) ≤ T*Real.exp (-ct*(n : ℝ)^δ)) →
      (∀ t ∈ Icc (0 : ℝ) 1,
        (ν t).real (good t)ᶜ ≤ T*Real.exp (-ct*(n : ℝ)^δ)) →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ i ∈ J, ∀ j,
        ∀ᵐ x ∂ν t, |ψ t i j x| ≤
          (U*(n : ℝ)^r)*(eLpNorm ((χ t i).val : X → ℝ) ∞ (ν t)).toReal) →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ i ∈ J,
        (∑ j, InteractionDifferential.boundaryWeight s n j*‖ψ t i j‖) ≤
          C*(n : ℝ)^(κ*ε-min s 1/2)*
            (‖(χ t i).val‖+Real.exp (-c*(n : ℝ)^δ)*
              (eLpNorm ((χ t i).val : X → ℝ) ∞ (ν t)).toReal) ∧
        (∑ j, ‖ψ t i j‖) ≤ C*(n : ℝ)^(κ*ε)*
            (‖(χ t i).val‖+Real.exp (-c*(n : ℝ)^δ)*
              (eLpNorm ((χ t i).val : X → ℝ) ∞ (ν t)).toReal)) →
      h 1-h 0 = β*∫ t in (0 : ℝ)..1, ∑ i ∈ J,
        ∫ x, ∑ j, b t j x*ψ t i j x ∂ν t →
      |h 1-h 0| ≤ β*K*(n : ℝ)^((κ+κb)*ε-min s 1/2)*
        ((∑ i ∈ J, A i)+Real.exp (-cf*(n : ℝ)^δ)*∑ i ∈ J, B i) := by
  obtain ⟨K,cf,hK,hcf,habsorb⟩ := pairing_rate_absorption_internal
    (2*Ab*C) U Kb T c ct δ ((κ+κb)*ε-min s 1/2) (1+r+bpower)
      (by positivity) hU hKb hT hc hct hδ
  refine ⟨K,cf,hK,hcf,?_⟩
  intro n N hsize X _ ν _ J χ ψ b W good A B β hβ h hA hB hgood hb hχA hχB
    hbgood hW hsq htail hprob hsup hDecay hid
  have hn : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hbound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (i : Fin (n : ℕ)) (hi : i ∈ J) :
      |∫ x, ∑ j, b t j x*ψ t i j x ∂ν t| ≤
        (K*(n : ℝ)^((κ+κb)*ε-min s 1/2))*(A i+Real.exp (-cf*(n : ℝ)^δ)*B i) := by
    have hh := (pairing_from_decay_internal s hs n N hsize (χ t i) (ψ t i) (b t) (W t)
      (hb t ht) (hgood t ht) (A i) (B i) (Ab*(n : ℝ)^(κb*ε)) (Kb*((n : ℝ)^bpower)^2) (T*Real.exp (-ct*(n : ℝ)^δ))
      C κ ε c δ (U*(n : ℝ)^r) (hA i hi) (hB i hi) (by positivity) (by positivity) (by positivity)
      hC.le (by positivity) (hχA t ht i hi) (hχB t ht i hi) (hbgood t ht)
      (hW t ht) (hsq t ht) (htail t ht) (hprob t ht) (hsup t ht i hi) (hDecay t ht i hi)).2
    apply hh.trans
    have hroot : Real.sqrt ((Kb*((n : ℝ)^bpower)^2)*(T*Real.exp (-ct*(n : ℝ)^δ))) =
        (n : ℝ)^bpower*Real.sqrt (Kb*T*Real.exp (-ct*(n : ℝ)^δ)) := by
      rw [show (Kb*((n : ℝ)^bpower)^2)*(T*Real.exp (-ct*(n : ℝ)^δ)) =
        ((n : ℝ)^bpower)^2*(Kb*T*Real.exp (-ct*(n : ℝ)^δ)) by ring,
        Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (Real.rpow_nonneg hn.le _)]
    have he : (n : ℝ)*(U*(n : ℝ)^r)*B i*
        Real.sqrt ((Kb*((n : ℝ)^bpower)^2)*(T*Real.exp (-ct*(n : ℝ)^δ))) =
        U*(n : ℝ)^(1+r+bpower)*Real.sqrt (Kb*T*Real.exp (-ct*(n : ℝ)^δ))*B i := by
      rw [hroot,Real.rpow_add hn (1+r) bpower,Real.rpow_add hn 1 r,Real.rpow_one]
      ring
    have hg : 2*(Ab*(n : ℝ)^(κb*ε))*C*(n : ℝ)^(κ*ε-min s 1/2) =
        2*Ab*C*(n : ℝ)^((κ+κb)*ε-min s 1/2) := by
      rw [show (κ+κb)*ε-min s 1/2 = κb*ε+(κ*ε-min s 1/2) by ring,Real.rpow_add hn]
      ring
    rw [he,hg]
    exact habsorb (n : ℝ) hn1 (A i) (B i) (hA i hi) (hB i hi)
  have hh := integrate_coordinate_pairings_internal J h
    (fun i t => ∫ x, ∑ j, b t j x*ψ t i j x ∂ν t)
    β (K*(n : ℝ)^((κ+κb)*ε-min s 1/2)) (Real.exp (-cf*(n : ℝ)^δ)) hβ A B hid hbound
  exact hh.trans_eq (by ring)

end Composition

end Riesz2.CompatibleComparison
