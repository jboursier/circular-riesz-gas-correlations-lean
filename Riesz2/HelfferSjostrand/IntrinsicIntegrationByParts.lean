/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.IntrinsicLangevin
public import Riesz2.ToMathlib.PeriodicLangevin
public import Riesz2.ToMathlib.IntrinsicScalarForms
public import Riesz2.Frozen.IsNeumannRealization
public import Riesz2.Frozen.HessianMatrix
public import Riesz1.HelfferSjostrand.GradientConvergenceEnergy
public import Riesz1.HelfferSjostrand.QuotientChartGeometry

/-!
# Intrinsic integration by parts

See Subsection 3.1 of the paper: scalar integration by parts, the classical commutator,
and the integrated gradient energy identity in the actual Euclidean metric of
the direction space. Compact tests are connected to the Neumann graph,
and the variational identity is extended to its full generator domain.
The coordinate formula uses the `hessianMatrix`.

For arbitrary periodic potentials, compact tests are unfolded across the
rotation seam. The final pair-potential interfaces reuse the Riesz1 quotient
theorems. Neither construction identifies particle and intrinsic gap generators.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ContDiff Laplacian

namespace Riesz2
namespace Intrinsic

section FrozenGraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} {U : Set E}

omit [BorelSpace E] in
/-- The Neumann graph contains every smooth finite-norm jet (Subsection 3.1). -/
theorem smooth_mem_neumannSobolevGraph {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hv : MemLp f 2 μ) (hg : MemLp (gradient f) 2 μ) :
    (hv.toLp f, hg.toLp (gradient f)) ∈ neumannSobolevGraph μ U :=
  subset_closure ⟨f, hv, hg, ⟨univ, isOpen_univ, subset_univ _, hf.contDiffOn⟩, rfl⟩

omit [BorelSpace E] in
/-- Internal closure principle for the exact graph, with no bounded-domain
assumption. Both test factors are L² classes, so the pairing is continuous. -/
theorem pairing_of_frozen_core (t : Lp E 2 μ) (q : Lp ℝ 2 μ)
    (hcore : ∀ (f : E → ℝ) (hv : MemLp f 2 μ) (hg : MemLp (gradient f) 2 μ),
      (∃ W : Set E, IsOpen W ∧ closure U ⊆ W ∧ ContDiffOn ℝ ∞ f W) →
      inner ℝ (hg.toLp (gradient f)) t = inner ℝ (hv.toLp f) q)
    {F : Lp ℝ 2 μ} {G : Lp E 2 μ} (hFG : (F, G) ∈ neumannSobolevGraph μ U) :
    inner ℝ G t = inner ℝ F q := by
  have hc : IsClosed {p : Lp ℝ 2 μ × Lp E 2 μ |
      inner ℝ p.2 t = inner ℝ p.1 q} :=
    isClosed_eq (continuous_snd.inner continuous_const) (continuous_fst.inner continuous_const)
  have hs : neumannSobolevGraph μ U ⊆
      {p : Lp ℝ 2 μ × Lp E 2 μ | inner ℝ p.2 t = inner ℝ p.1 q} := by
    apply closure_minimal _ hc
    rintro p ⟨f, hv, hg, hf, rfl⟩
    exact hcore f hv hg hf
  exact hs hFG

variable (σ : Measure E) [σ.IsAddHaarMeasure] (hU : IsOpen U)
  {V : E → ℝ} (hV : ContDiffOn ℝ ∞ V U)

include hU hV in
/-- Compact tests pair with every completed Sobolev jet, Subsection 3.1. This uses the intrinsic graph, in the intrinsic metric. -/
theorem integrationByParts_frozenGraph {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U)
    {F : Lp ℝ 2 ((σ.restrict U).tilted (fun x => -V x))}
    {G : Lp E 2 ((σ.restrict U).tilted (fun x => -V x))}
    (hFG : (F, G) ∈ neumannSobolevGraph ((σ.restrict U).tilted (fun x => -V x)) U) :
    (∫ x, F x * langevin V f x ∂((σ.restrict U).tilted (fun x => -V x))) =
      ∫ x, inner ℝ (G x) (gradient f x) ∂((σ.restrict U).tilted (fun x => -V x)) := by
  let ν := (σ.restrict U).tilted (fun x => -V x)
  have hg : MemLp (gradient f) 2 ν := memLp_gradient hf hfc
  have hq : MemLp (langevin V f) 2 ν :=
    (contDiff_langevin hU hV hf hfU).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_langevin V hfc)
  have hcore (φ : E → ℝ) (hv : MemLp φ 2 ν) (hgrad : MemLp (gradient φ) 2 ν)
      (hs : ∃ W : Set E, IsOpen W ∧ closure U ⊆ W ∧ ContDiffOn ℝ ∞ φ W) :
      inner ℝ (hgrad.toLp (gradient φ)) (hg.toLp (gradient f)) =
        inner ℝ (hv.toLp φ) (hq.toLp (langevin V f)) := by
    obtain ⟨W, hW, hUW, hφ⟩ := hs
    have hibp := integrationByParts σ hU hV hf hfc hfU
      (hφ.mono (subset_closure.trans hUW))
    rw [L2.inner_def, L2.inner_def]
    calc
      _ = ∫ x, inner ℝ (gradient φ x) (gradient f x) ∂ν := by
        apply integral_congr_ae
        filter_upwards [hgrad.coeFn_toLp, hg.coeFn_toLp] with x hx hy
        rw [hx, hy]
      _ = ∫ x, φ x * langevin V f x ∂ν := hibp.symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hv.coeFn_toLp, hq.coeFn_toLp] with x hx hy
        rw [hx, hy, Real.inner_apply]
  have he := pairing_of_frozen_core (hg.toLp (gradient f))
    (hq.toLp (langevin V f)) hcore hFG
  rw [L2.inner_def, L2.inner_def] at he
  calc
    _ = ∫ x, inner ℝ (F x) (hq.toLp (langevin V f) x) ∂ν := by
      apply integral_congr_ae
      filter_upwards [hq.coeFn_toLp] with x hx
      rw [hx, Real.inner_apply]
    _ = ∫ x, inner ℝ (G x) (hg.toLp (gradient f) x) ∂ν := he.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hg.coeFn_toLp] with x hx
      rw [hx]

include hU hV in
/-- The compact scalar expression is in the variational Neumann graph of every
realization of the intrinsic Sobolev graph, Subsection 3.1. -/
theorem compact_test_variational
    (Q : ScalarFormData ((σ.restrict U).tilted (fun x => -V x)))
    (hQ : IsNeumannRealization U Q) {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) :
    ∃ (u : Q.1) (hv : MemLp f 2 ((σ.restrict U).tilted (fun x => -V x)))
      (hq : MemLp (langevin V f) 2 ((σ.restrict U).tilted (fun x => -V x))),
      u.val = hv.toLp f ∧ ∀ h : Q.1, Q.2 u h = inner ℝ (hq.toLp (langevin V f)) h.val := by
  let ν := (σ.restrict U).tilted (fun x => -V x)
  have hv : MemLp f 2 ν := hf.continuous.memLp_of_hasCompactSupport hfc
  have hg : MemLp (gradient f) 2 ν := memLp_gradient hf hfc
  have hq : MemLp (langevin V f) 2 ν :=
    (contDiff_langevin hU hV hf hfU).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_langevin V hfc)
  have hfgraph := smooth_mem_neumannSobolevGraph (U := U) hf hv hg
  have hmem : hv.toLp f ∈ Q.1 := (hQ.1 _).mpr ⟨_, hfgraph⟩
  let u : Q.1 := ⟨hv.toLp f, hmem⟩
  refine ⟨u, hv, hq, rfl, fun h => ?_⟩
  obtain ⟨g, hgraph⟩ := (hQ.1 h.val).mp h.property
  rw [hQ.2.2 u h _ g hfgraph hgraph, real_inner_comm]
  have hi := integrationByParts_frozenGraph σ hU hV hf hfc hfU hgraph
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ x, inner ℝ (g x) (gradient f x) ∂ν := by
      apply integral_congr_ae
      filter_upwards [hg.coeFn_toLp] with x hx
      rw [hx]
    _ = ∫ x, h.val x * langevin V f x ∂ν := hi.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hq.coeFn_toLp] with x hx
      rw [hx, Real.inner_apply]
      ring

end FrozenGraph

section FullDomain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsFiniteMeasure μ] {U : Set E}

/-- An intrinsic realization has a dense value domain: interior compact tests
already separate L². No boundedness or positive dimension is required. -/
theorem dense_value_of_realization (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    (Q : ScalarFormData μ) (hQ : IsNeumannRealization U Q) :
    DenseRange (Q.1.subtype : Q.1 → Lp ℝ 2 μ) := by
  apply Riesz1.Internal.denseRange_of_chart_tests μ Q.1.subtype id
    MeasurableEmbedding.id U hU hμ
  intro f hf hfc _hfU
  have hv : MemLp f 2 μ := hf.continuous.memLp_of_hasCompactSupport hfc
  have hg : MemLp (gradient f) 2 μ := memLp_gradient hf hfc
  have hm := (hQ.1 (hv.toLp f)).mpr ⟨_, smooth_mem_neumannSobolevGraph hf hv hg⟩
  exact ⟨⟨hv.toLp f, hm⟩, hv.coeFn_toLp⟩

/-- Extended integration by parts for the full intrinsic Neumann generator,
Subsection 3.1. The operator is the existing unique variational
representative. The supplied gradient classes are in the exact graph. -/
theorem generator_integrationByParts (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    (Q : ScalarFormData μ) (hQ : IsNeumannRealization U Q)
    (f : Riesz1.Internal.formOperatorDomain (Q.1.subtype : Q.1 → Lp ℝ 2 μ)
      (fun a b => Q.2 a b))
    (h : Q.1) (g k : Lp E 2 μ)
    (hg : (f.val.val, g) ∈ neumannSobolevGraph μ U)
    (hk : (h.val, k) ∈ neumannSobolevGraph μ U) :
    (∫ x, h.val x * Riesz1.Internal.formOperator Q.1.subtype
      (dense_value_of_realization hU hμ Q hQ) (fun a b => Q.2 a b) f x ∂μ) =
      ∫ x, inner ℝ (k x) (g x) ∂μ := by
  have he := Riesz1.Internal.formOperator_spec Q.1.subtype
    (dense_value_of_realization hU hμ Q hQ) (fun a b => Q.2 a b) f h
  rw [hQ.2.2 f.val h g k hg hk, L2.inner_def, L2.inner_def] at he
  calc
    _ = ∫ x, inner ℝ
        (Riesz1.Internal.formOperator Q.1.subtype
          (dense_value_of_realization hU hμ Q hQ) (fun a b => Q.2 a b) f x) (h.val x) ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [Real.inner_apply, mul_comm]
    _ = ∫ x, inner ℝ (g x) (k x) ∂μ := he.symm
    _ = _ := integral_congr_ae (Eventually.of_forall fun x => real_inner_comm _ _)

/-- The jet completion has the same closed graph as the definition.
This is a bridge between existing encodings, preserving its derivative metric. -/
theorem mem_frozenGraph_iff_completion
    (hU : IsOpen U) (hbounded : Bornology.IsBounded U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    (F : Lp ℝ 2 μ) (G : Lp E 2 μ) :
    (F, G) ∈ neumannSobolevGraph μ U ↔
      WithLp.toLp 2 (F, G) ∈ ScalarForm.completionSubmodule
        (EuclideanScalarForm.smoothJet hU hbounded hμ) := by
  let e := WithLp.homeomorphProd 2 (Lp ℝ 2 μ) (Lp E 2 μ)
  have hcore : e ⁻¹' {p | ∃ (f : E → ℝ) (hv : MemLp f 2 μ)
      (hg : MemLp (gradient f) 2 μ),
      (∃ W : Set E, IsOpen W ∧ closure U ⊆ W ∧ ContDiffOn ℝ ∞ f W) ∧
      p = (hv.toLp f, hg.toLp (gradient f))} =
      Riesz1.WeightedSobolev.jetCore μ (Riesz1.WeightedSobolev.SmoothNearClosure U) id gradient := by
    ext p
    constructor
    · rintro ⟨f, hv, hg, hf, hp⟩
      refine ⟨f, hf, hv, hg, ?_⟩
      exact congrArg (WithLp.toLp 2) hp
    · rintro ⟨f, hf, hv, hg, rfl⟩
      exact ⟨f, hv, hg, hf, rfl⟩
  change e (WithLp.toLp 2 (F, G)) ∈ neumannSobolevGraph μ U ↔ _
  change WithLp.toLp 2 (F, G) ∈ e ⁻¹' closure _ ↔ _
  rw [e.preimage_closure, hcore]
  change WithLp.toLp 2 (F, G) ∈ closure _ ↔
    WithLp.toLp 2 (F, G) ∈ closure
      ((EuclideanScalarForm.smoothJet hU hbounded hμ).range : Set _)
  rw [EuclideanScalarForm.range_smoothJet hU hbounded hμ]

/-- On a bounded domain the graph is exactly the library's weighted H¹
graph, via the intrinsic completion (Subsection 3.1). -/
theorem mem_frozenGraph_iff_weightedH1
    (hU : IsOpen U) (hbounded : Bornology.IsBounded U) (hμ : ∀ᵐ x ∂μ, x ∈ U)
    (F : Lp ℝ 2 μ) (G : Lp E 2 μ) :
    (F, G) ∈ neumannSobolevGraph μ U ↔
      Riesz1.WeightedSobolev.IsWeightedH1 μ U F G := by
  rw [mem_frozenGraph_iff_completion hU hbounded hμ]
  have he := EuclideanScalarForm.mem_completion_iff hU hbounded hμ
    (F : E → ℝ) (G : E → E) (Lp.memLp F) (Lp.memLp G)
  simpa only [Lp.toLp_coeFn] using he

/-- Compact tests lie in the actual intrinsic variational graph,
Subsection 3.1. This interface is directly usable by the scalar core
and differentiated equation. -/
theorem compact_test_mem_neumannGraph
    (σ : Measure E) [σ.IsAddHaarMeasure] (hU : IsOpen U)
    (hbounded : Bornology.IsBounded U) {V : E → ℝ} (hV : ContDiffOn ℝ ∞ V U)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) :
    let ν := (σ.restrict U).tilted (fun x => -V x)
    let hν : ∀ᵐ x ∂ν, x ∈ U :=
      (tilted_absolutelyContinuous (σ.restrict U) (fun x => -V x)).ae_le
        (ae_restrict_mem hU.measurableSet)
    let J := EuclideanScalarForm.smoothJet hU hbounded hν
    ∃ hq : MemLp (langevin V f) 2 ν,
      (ScalarForm.ofCore J ⟨f, univ, isOpen_univ, subset_univ _, hf.contDiffOn⟩,
        hq.toLp (langevin V f)) ∈ ScalarForm.neumannGraph J := by
  dsimp only
  let ν := (σ.restrict U).tilted (fun x => -V x)
  have hν : ∀ᵐ x ∂ν, x ∈ U :=
    (tilted_absolutelyContinuous (σ.restrict U) (fun x => -V x)).ae_le
      (ae_restrict_mem hU.measurableSet)
  let J := EuclideanScalarForm.smoothJet hU hbounded hν
  have hq : MemLp (langevin V f) 2 ν :=
    (contDiff_langevin hU hV hf hfU).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_langevin V hfc)
  refine ⟨hq, ?_⟩
  apply (ScalarForm.mem_neumannGraph_iff_integral J _ _).mpr
  intro h
  have hh : (ScalarForm.value J h, ScalarForm.deriv J h) ∈ neumannSobolevGraph ν U := by
    apply (mem_frozenGraph_iff_completion hU hbounded hν _ _).mpr
    exact h.property
  have hi := integrationByParts_frozenGraph σ hU hV hf hfc hfU hh
  let c : EuclideanScalarForm.smoothCore U :=
    ⟨f, univ, isOpen_univ, subset_univ _, hf.contDiffOn⟩
  have hg := (Riesz1.WeightedSobolev.memLp_of_smoothNearClosure hbounded hν c.property).2.coeFn_toLp
  change (ScalarForm.deriv J (ScalarForm.ofCore J c) : E → E) =ᵐ[ν] gradient f at hg
  calc
    _ = ∫ x, inner ℝ (ScalarForm.deriv J h x) (gradient f x) ∂ν := by
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      rw [hx, real_inner_comm]
    _ = ∫ x, ScalarForm.value J h x * langevin V f x ∂ν := hi.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hq.coeFn_toLp] with x hx
      rw [hx, mul_comm]

end FullDomain

section Coordinates

/-- The Hessian is the classical symmetric second derivative, Subsection 3.1.
The equality is asserted only where the potential is smooth. -/
theorem hessianMatrix_eq_second {n : ℕ} {V : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hV : ContDiffAt ℝ ∞ V x) (i j : Fin n) :
    hessianMatrix V x i j = fderiv ℝ (fderiv ℝ V) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  have hd := (hV.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have he := Riesz1.inner_fderiv_gradient hd (EuclideanSpace.single j 1)
    (EuclideanSpace.single i 1)
  simp only [EuclideanSpace.inner_single_right, conj_trivial, one_mul] at he
  exact he.trans (hV.isSymmSndFDerivAt (by simp) _ _)

/-- Coordinate commutator with the exact Hessian, Subsection 3.1. -/
theorem coordinate_commutator {n : ℕ} {V f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hV : ContDiffAt ℝ ∞ V x)
    (hf : ContDiff ℝ ∞ f) (i : Fin n) :
    fderiv ℝ (langevin V f) x (EuclideanSpace.single i 1) =
      langevin V (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x +
        ∑ j, hessianMatrix V x i j * gradient f x j := by
  rw [directional_commutator hV hf]
  congr 1
  rw [Riesz1.hsCommutator_linear_coordinates (fderiv ℝ (fderiv ℝ V) x
    (EuclideanSpace.single i 1)) (gradient f x)]
  simp_rw [hessianMatrix_eq_second hV]

/-- The Hessian energy in Subsection 3.1 is the contraction with the exact matrix. This bridges the basis-free smooth energy to the finite matrix API. -/
theorem hessianMatrix_bilinear {n : ℕ} {V : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hV : ContDiffAt ℝ ∞ V x)
    (u v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fderiv ℝ V) x u v = ∑ i, ∑ j, u i * hessianMatrix V x i j * v j := by
  have he : fderiv ℝ (fderiv ℝ V) x u v =
      ∑ i, fderiv ℝ (fderiv ℝ V) x (EuclideanSpace.single i 1) v * u i :=
    Riesz1.hsCommutator_linear_coordinates ((fderiv ℝ (fderiv ℝ V) x).flip v) u
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  rw [Riesz1.hsCommutator_linear_coordinates
    (fderiv ℝ (fderiv ℝ V) x (EuclideanSpace.single i 1)) v, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [hessianMatrix_eq_second hV]
  ring

end Coordinates

section SourceStatement

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- See Subsection 3.1 of the paper, Euclidean/affine part, with every compact-support
identity and explicit finite norms. This includes intrinsic affine direction
spaces of arbitrary dimension. The full-domain identity is
`generator_integrationByParts`. Convexity is a hypothesis of Subsection 3.1. The local
calculus itself works without it. The partition certificates exclude the
zero-measure default of exponential tilting. -/
theorem integrationByParts_commutator
    (σ : Measure E) [σ.IsAddHaarMeasure] {U : Set E} (hU : IsOpen U)
    {V : E → ℝ} (hV : ContDiffOn ℝ ∞ V U) (_hconvex : ConvexOn ℝ U V)
    (hZ : Integrable (fun x => Real.exp (-V x)) (σ.restrict U))
    (hZpos : 0 < ∫ x in U, Real.exp (-V x) ∂σ)
    {f h : E → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hfU : tsupport f ⊆ U) (hh : ContDiff ℝ ∞ h) (hhc : HasCompactSupport h)
    (_hhU : tsupport h ⊆ U) :
    let μ := (σ.restrict U).tilted (fun x => -V x)
    let B := stdOrthonormalBasis ℝ E
    let e := fun x =>
      (∑ i, inner ℝ (gradient (fun y => fderiv ℝ f y (B i)) x)
        (gradient (fun y => fderiv ℝ f y (B i)) x)) +
      fderiv ℝ (fderiv ℝ V) x (gradient f x) (gradient f x)
    IsProbabilityMeasure μ ∧
    Integrable (fun x => h x * langevin V f x) μ ∧
    Integrable (fun x => inner ℝ (gradient h x) (gradient f x)) μ ∧
    (∫ x, h x * langevin V f x ∂μ) = ∫ x, inner ℝ (gradient h x) (gradient f x) ∂μ ∧
    (∀ x ∈ U, ∀ v : E, fderiv ℝ (langevin V f) x v =
      langevin V (fun y => fderiv ℝ f y v) x +
        fderiv ℝ (fderiv ℝ V) x v (gradient f x)) ∧
    ∃ hL : MemLp (langevin V f) 2 μ, Integrable e μ ∧
      (∫ x, e x ∂μ) = ‖hL.toLp (langevin V f)‖ ^ 2 := by
  dsimp only
  let μ := (σ.restrict U).tilted (fun x => -V x)
  have : NeZero (σ.restrict U) := ⟨fun hzero => by
    rw [hzero, integral_zero_measure] at hZpos
    exact (lt_irrefl 0) hZpos⟩
  have hprob := isProbabilityMeasure_tilted hZ
  have hL := contDiff_langevin hU hV hf hfU
  have hi : Integrable (fun x => h x * langevin V f x) μ :=
    (hh.continuous.mul hL.continuous).integrable_of_hasCompactSupport hhc.mul_right
  have hgf : MemLp (gradient f) 2 μ := memLp_gradient hf hfc
  have hgh : MemLp (gradient h) 2 μ := memLp_gradient hh hhc
  have hgi : Integrable (fun x => inner ℝ (gradient h x) (gradient f x)) μ := by
    apply (L2.integrable_inner (𝕜 := ℝ) (hgh.toLp (gradient h)) (hgf.toLp (gradient f))).congr
    filter_upwards [hgh.coeFn_toLp, hgf.coeFn_toLp] with x hx hy
    rw [hx, hy]
  obtain ⟨hm, hei, he⟩ := gradient_energy σ hU hV (stdOrthonormalBasis ℝ E) hf hfc hfU
  refine ⟨hprob, hi, hgi, integrationByParts σ hU hV hf hfc hfU hh.contDiffOn,
    fun x hx v => directional_commutator (hV.contDiffAt (hU.mem_nhds hx)) hf v,
    hm, hei, he.trans ?_⟩
  rw [Riesz1.poisson_norm_sq μ]
  apply integral_congr_ae
  filter_upwards [hm.coeFn_toLp] with x hx
  rw [hx]

end SourceStatement
end Intrinsic

namespace ParticleIntegration

open Riesz1

/-- Normalized integration on the periodic quotient is integration on its
fundamental region. The potential is arbitrary. No pair decomposition is used. -/
theorem quotient_integral {N : ℕ+} (V b : HsEuclidean N → ℝ) :
    (∫ x, hsSmoothValue b x ∂((hsConfigurationVolume N).tilted
      (fun x => -hsSmoothValue V x))) =
      ∫ x, b x ∂((volume.restrict (hsFundamentalRegion N)).tilted (fun x => -V x)) := by
  have hb (a : HsEuclidean N → ℝ) :
      (∫ x, hsSmoothValue a x ∂hsConfigurationVolume N) =
        ∫ x in hsFundamentalRegion N, a x := by
    rw [← (measurePreserving_hsLiftPoint_volume N).map_eq,
      (measurableEmbedding_hsLiftPoint N).integral_map]
    rfl
  rw [integral_tilted, integral_tilted]
  have hz : (∫ x, Real.exp (-hsSmoothValue V x) ∂hsConfigurationVolume N) =
      ∫ x in hsFundamentalRegion N, Real.exp (-V x) := hb (fun x => Real.exp (-V x))
  rw [hz]
  exact hb (fun x => (Real.exp (-V x) /
    (∫ y in hsFundamentalRegion N, Real.exp (-V y))) • b x)

/-- General-potential periodic directional identity, Subsection 3.1.
The cut is treated by a periodized compact test, rather than a boundary term. -/
theorem directional_integrationByParts {N : ℕ+} (hN : 2 ≤ (N : ℕ))
    {V : HsEuclidean N → ℝ} (hV : ContDiffOn ℝ ∞ V (hsChamber N))
    (hVp : ∀ (k : ℤ) x, V (hsTranslate (k : ℝ) x) = V x)
    (f : HsTestFunction N) (h : hsSmoothCore N) (a : HsEuclidean N) :
    let μ := (hsConfigurationVolume N).tilted (fun x => -hsSmoothValue V x)
    (∫ x, hsSmoothValue (fun y => fderiv ℝ f.toFun y a) x *
      hsSmoothValue (fun y => fderiv ℝ h.val y a) x ∂μ) =
      ∫ x, hsSmoothValue h.val x * hsSmoothValue
        (fun y => fderiv ℝ f.toFun y a * fderiv ℝ V y a -
          fderiv ℝ (fun z => fderiv ℝ f.toFun z a) y a) x ∂μ := by
  dsimp only
  let g := fun y => fderiv ℝ f.toFun y a
  let ℓ := EuclideanSpace.proj (𝕜 := ℝ) (⟨0, N.pos⟩ : Fin (N : ℕ))
  let ψ := fun y => periodicCutoff (ℓ y) * g y
  have hg : ContDiff ℝ ∞ g :=
    (f.smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hgU : tsupport g ⊆ hsChamber N :=
    (tsupport_fderiv_apply_subset ℝ a).trans (f.tsupport_subset_chamber hN)
  have hψc : HasCompactSupport ψ := hasCompactSupport_hsPeriodicCutoff_mul hgU
  have hψ : ContDiff ℝ ∞ ψ := (contDiff_periodicCutoff.comp ℓ.contDiff).mul hg
  have hψU : tsupport ψ ⊆ hsChamber N := tsupport_mul_subset_right.trans hgU
  have hgp (k : ℤ) (x : HsEuclidean N) : g (x + (k : ℝ) • hsRotationVector N) = g x :=
    congrArg (fun A : HsEuclidean N →L[ℝ] ℝ => A a)
      (fderiv_periodic_vector (fun k y => by rw [← hsTranslate_eq_add_rotation]; exact f.periodic k y) k x)
  have hP := vectorPeriodize_periodicCutoff_mul (hsRotationVector_ne_zero N) ℓ
    (by simp [ℓ, hsRotationVector]) hgp hψc
  obtain ⟨hhp, W, hW, hUW, hh⟩ := h.property
  have hi := Intrinsic.periodized_integrationByParts volume (hsRotationVector_ne_zero N) ℓ
    (by simp [ℓ, hsRotationVector]) (isOpen_hsChamber N)
    (fun k y => by rw [← hsTranslate_eq_add_rotation]; exact hsTranslate_mem_chamber_iff _ _)
    hV (fun k y => by rw [← hsTranslate_eq_add_rotation]; exact hVp k y)
    hψ hψc hψU (hh.mono (subset_closure.trans hUW))
    (fun k y => by rw [← hsTranslate_eq_add_rotation]; exact hhp k y) a
  dsimp only at hi
  rw [hP] at hi
  have hF : hsFundamentalRegion N = hsChamber N ∩ ℓ ⁻¹' Ico (0 : ℝ) 1 := rfl
  change (∫ x, hsSmoothValue (fun y => g y * fderiv ℝ h.val y a) x
    ∂((hsConfigurationVolume N).tilted (fun x => -hsSmoothValue V x))) =
      ∫ x, hsSmoothValue (fun y => h.val y *
        (g y * fderiv ℝ V y a - fderiv ℝ g y a)) x
        ∂((hsConfigurationVolume N).tilted (fun x => -hsSmoothValue V x))
  rw [quotient_integral, quotient_integral, hF]
  exact hi

/-- General-potential periodic scalar integration by parts, Subsection 3.1.
The test on the right is an arbitrary smooth Neumann core element. -/
theorem general_integrationByParts_core {N : ℕ+} (hN : 2 ≤ (N : ℕ))
    {V : HsEuclidean N → ℝ} (hV : ContDiffOn ℝ ∞ V (hsChamber N))
    (hVp : ∀ (k : ℤ) x, V (hsTranslate (k : ℝ) x) = V x)
    (f : HsTestFunction N) (h : hsSmoothCore N) :
    let μ := (hsConfigurationVolume N).tilted (fun x => -hsSmoothValue V x)
    (∫ x, hsSmoothValue h.val x * hsSmoothValue (Intrinsic.langevin V f.toFun) x ∂μ) =
      ∫ x, inner ℝ (hsSmoothGradient h x)
        (hsSmoothGradient ⟨f.toFun, f.smoothOnClosure⟩ x) ∂μ := by
  dsimp only
  let μ := (hsConfigurationVolume N).tilted (fun x => -hsSmoothValue V x)
  let B := stdOrthonormalBasis ℝ (HsEuclidean N)
  let D := fun (g : HsEuclidean N → ℝ) i x => fderiv ℝ g x (B i)
  let q := fun i x => D f.toFun i x * D V i x - D (D f.toFun i) i x
  have hD (i) : ContDiff ℝ ∞ (D f.toFun i) :=
    (f.smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hs (i) : tsupport (D f.toFun i) ⊆ hsChamber N :=
    (tsupport_fderiv_apply_subset ℝ (B i)).trans (f.tsupport_subset_chamber hN)
  have hq (i) : ContDiff ℝ ∞ (q i) :=
    (WeightedSobolev.contDiff_cutoff_mul (isOpen_hsChamber N) (hD i) (hs i)
      ((hV.fderiv_of_isOpen (isOpen_hsChamber N) (by simp)).clm_apply contDiffOn_const)).sub
      (((hD i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const)
  have hmD (i) : MemLp (hsSmoothValue (D f.toFun i)) 2 μ :=
    memLp_hsLiftPoint μ 2 (hD i).continuous.continuousOn
  have hmh (i) : MemLp (hsSmoothValue (D h.val i)) 2 μ := by
    have hm := (h.property.memLp_gradient μ).inner_const (𝕜 := ℝ) (B i)
    change MemLp (fun x => fderiv ℝ h.val (hsLiftPoint N x) (B i)) 2 μ
    simpa only [hsSmoothGradient, inner_gradient_left] using hm
  have hmq (i) : MemLp (hsSmoothValue (q i)) 2 μ :=
    memLp_hsLiftPoint μ 2 (hq i).continuous.continuousOn
  have hmi (i) : Integrable (fun x => hsSmoothValue h.val x * hsSmoothValue (q i) x) μ :=
    (h.property.memLp_value μ).integrable_mul (hmq i)
  have hmj (i) : Integrable (fun x => hsSmoothValue (D f.toFun i) x * hsSmoothValue (D h.val i) x) μ :=
    (hmD i).integrable_mul (hmh i)
  calc
    _ = ∫ x, ∑ i, hsSmoothValue h.val x * hsSmoothValue (q i) x ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [hsSmoothValue]
      rw [Intrinsic.langevin_eq_sum B f.smooth, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [q, D]
      ring
    _ = ∑ i, ∫ x, hsSmoothValue h.val x * hsSmoothValue (q i) x ∂μ :=
      integral_finsetSum _ (fun i _ => hmi i)
    _ = ∑ i, ∫ x, hsSmoothValue (D f.toFun i) x * hsSmoothValue (D h.val i) x ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      exact (directional_integrationByParts hN hV hVp f h (B i)).symm
    _ = ∫ x, ∑ i, hsSmoothValue (D f.toFun i) x * hsSmoothValue (D h.val i) x ∂μ :=
      (integral_finsetSum _ (fun i _ => hmj i)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [← B.sum_inner_mul_inner]
      simp only [hsSmoothValue, hsSmoothGradient, inner_gradient_left, inner_gradient_right,
        conj_trivial, D, mul_comm]

/-- General-potential periodic integration by parts against every completed
Sobolev test, Subsection 3.1. -/
theorem general_integrationByParts {N : ℕ+} (hN : 2 ≤ (N : ℕ))
    {V : HsEuclidean N → ℝ} (hV : ContDiffOn ℝ ∞ V (hsChamber N))
    (hVp : ∀ (k : ℤ) x, V (hsTranslate (k : ℝ) x) = V x)
    (f : HsTestFunction N)
    (h : HsSobolev ((hsConfigurationVolume N).tilted (fun x => -hsSmoothValue V x))) :
    let μ := (hsConfigurationVolume N).tilted (fun x => -hsSmoothValue V x)
    (∫ x, hsSobolevValue μ h x * hsSmoothValue (Intrinsic.langevin V f.toFun) x ∂μ) =
      ∫ x, inner ℝ (hsSobolevGradient μ h x)
        (hsSmoothGradient ⟨f.toFun, f.smoothOnClosure⟩ x) ∂μ := by
  dsimp only
  let μ := (hsConfigurationVolume N).tilted (fun x => -hsSmoothValue V x)
  have hL := Intrinsic.contDiff_langevin (isOpen_hsChamber N) hV f.smooth
    (f.tsupport_subset_chamber hN)
  apply (Riesz1.Internal.hsSobolev_pairing_of_smooth μ _
    (f.smoothOnClosure.memLp_gradient μ) _
    (memLp_hsLiftPoint μ 2 hL.continuous.continuousOn) _ h).symm
  intro φ
  exact (general_integrationByParts_core hN hV hVp f φ).symm

/-- General-potential periodic energy identity, Subsection 3.1.
The energy is exactly the intrinsic-coordinate expansion of Subsection 3.1 on
the original periodic particle metric, and its integrability is concluded. -/
theorem general_gradient_energy {N : ℕ+} (hN : 2 ≤ (N : ℕ))
    {V : HsEuclidean N → ℝ} (hV : ContDiffOn ℝ ∞ V (hsChamber N))
    (hVp : ∀ (k : ℤ) x, V (hsTranslate (k : ℝ) x) = V x)
    (f : HsTestFunction N) :
    let μ := (hsConfigurationVolume N).tilted (fun x => -hsSmoothValue V x)
    let B := stdOrthonormalBasis ℝ (HsEuclidean N)
    let e := fun y => (∑ i, inner ℝ
      (gradient (fun z => fderiv ℝ f.toFun z (B i)) y)
      (gradient (fun z => fderiv ℝ f.toFun z (B i)) y)) +
      fderiv ℝ (fderiv ℝ V) y (gradient f.toFun y) (gradient f.toFun y)
    ∃ hm : MemLp (hsSmoothValue (Intrinsic.langevin V f.toFun)) 2 μ,
      Integrable (hsSmoothValue e) μ ∧
      (∫ x, hsSmoothValue e x ∂μ) =
        ‖hm.toLp (hsSmoothValue (Intrinsic.langevin V f.toFun))‖ ^ 2 := by
  classical
  dsimp only
  let μ := (hsConfigurationVolume N).tilted (fun x => -hsSmoothValue V x)
  let B := stdOrthonormalBasis ℝ (HsEuclidean N)
  let D := fun (g : HsEuclidean N → ℝ) i x => fderiv ℝ g x (B i)
  let L := Intrinsic.langevin V f.toFun
  let g := fun i => hsGradientTestDirection hN f (B i)
  have hL : ContDiff ℝ ∞ L := Intrinsic.contDiff_langevin (isOpen_hsChamber N) hV f.smooth
    (f.tsupport_subset_chamber hN)
  have hLp (k : ℤ) (x : HsEuclidean N) : L (hsTranslate (k : ℝ) x) = L x := by
    dsimp only [L, Intrinsic.langevin, gradient]
    rw [hsGradient_fderiv_translate hVp, hsGradient_fderiv_translate f.periodic,
      hsGradient_laplacian_translate f.periodic]
  let Lcore : hsSmoothCore N :=
    ⟨L, hLp, univ, isOpen_univ, subset_univ _, hL.contDiffOn⟩
  have hmL : MemLp (hsSmoothValue L) 2 μ := memLp_hsLiftPoint μ 2 hL.continuous.continuousOn
  have hD (i) : ContDiff ℝ ∞ (D f.toFun i) :=
    (f.smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hs (i) : tsupport (D f.toFun i) ⊆ hsChamber N :=
    (tsupport_fderiv_apply_subset ℝ (B i)).trans (f.tsupport_subset_chamber hN)
  have hLD (i) : ContDiff ℝ ∞ (Intrinsic.langevin V (D f.toFun i)) :=
    Intrinsic.contDiff_langevin (isOpen_hsChamber N) hV (hD i) (hs i)
  have hmD (i) : MemLp (hsSmoothValue (D f.toFun i)) 2 μ :=
    memLp_hsLiftPoint μ 2 (hD i).continuous.continuousOn
  have hmLD (i) : MemLp (hsSmoothValue (Intrinsic.langevin V (D f.toFun i))) 2 μ :=
    memLp_hsLiftPoint μ 2 (hLD i).continuous.continuousOn
  have hmDL (i) : MemLp (hsSmoothValue (D L i)) 2 μ :=
    memLp_hsLiftPoint μ 2
      (((hL.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous.continuousOn)
  let A := fun i x => inner ℝ (gradient (D f.toFun i) (hsLiftPoint N x))
    (gradient (D f.toFun i) (hsLiftPoint N x))
  let T := fun i x => (hsSmoothValue (D L i) x -
    hsSmoothValue (Intrinsic.langevin V (D f.toFun i)) x) * hsSmoothValue (D f.toFun i) x
  have hma (i) : Integrable (A i) μ := by
    have hgrad : Continuous (gradient (D f.toFun i)) := (toDual ℝ (HsEuclidean N)).symm.continuous.comp
      ((hD i).continuous_fderiv (by simp))
    have hcont : Continuous (fun y => inner ℝ (gradient (D f.toFun i) y)
        (gradient (D f.toFun i) y)) := hgrad.inner hgrad
    exact (memLp_hsLiftPoint μ 1 hcont.continuousOn).integrable (by norm_num)
  have hmt (i) : Integrable (T i) μ := ((hmDL i).sub (hmLD i)).integrable_mul (hmD i)
  have he : (fun x => (∑ i, A i x) + fderiv ℝ (fderiv ℝ V) (hsLiftPoint N x)
      (gradient f.toFun (hsLiftPoint N x)) (gradient f.toFun (hsLiftPoint N x))) =ᵐ[μ]
      (fun x => ∑ i, (A i x + T i x)) := by
    filter_upwards with x
    rw [Intrinsic.hessian_commutator B
      (hV.contDiffAt ((isOpen_hsChamber N).mem_nhds (hsLiftPoint_mem_chamber N x))) f.smooth,
      Finset.sum_add_distrib]
    rfl
  have hei : Integrable (fun x => ∑ i, (A i x + T i x)) μ :=
    integrable_finsetSum _ (fun i _ => (hma i).add (hmt i))
  refine ⟨hmL, hei.congr he.symm, ?_⟩
  change (∫ x, (∑ i, A i x) + fderiv ℝ (fderiv ℝ V) (hsLiftPoint N x)
    (gradient f.toFun (hsLiftPoint N x)) (gradient f.toFun (hsLiftPoint N x)) ∂μ) = _
  rw [integral_congr_ae he,
    integral_finsetSum (f := fun i x => A i x + T i x) _ (fun i _ => (hma i).add (hmt i))]
  have hi (i) : (∫ x, A i x + T i x ∂μ) =
      ∫ x, hsSmoothValue (D L i) x * hsSmoothValue (D f.toFun i) x ∂μ := by
    rw [integral_add (hma i) (hmt i)]
    have hibp := general_integrationByParts_core hN hV hVp (g i)
      ⟨(g i).toFun, (g i).smoothOnClosure⟩
    change (∫ x, hsSmoothValue (D f.toFun i) x *
      hsSmoothValue (Intrinsic.langevin V (D f.toFun i)) x ∂μ) = ∫ x, A i x ∂μ at hibp
    rw [← hibp]
    have ht : T i = (fun x => hsSmoothValue (D L i) x * hsSmoothValue (D f.toFun i) x) -
        (fun x => hsSmoothValue (D f.toFun i) x *
          hsSmoothValue (Intrinsic.langevin V (D f.toFun i)) x) := by ext x; dsimp [T]; ring
    rw [ht]
    simp only [Pi.sub_apply]
    rw [integral_sub
      (f := fun x => hsSmoothValue (D L i) x * hsSmoothValue (D f.toFun i) x)
      (g := fun x => hsSmoothValue (D f.toFun i) x * hsSmoothValue (Intrinsic.langevin V (D f.toFun i)) x)
      ((hmDL i).integrable_mul (hmD i)) ((hmD i).integrable_mul (hmLD i))]
    ring
  simp_rw [hi]
  rw [← integral_finsetSum
    (f := fun i x => hsSmoothValue (D L i) x * hsSmoothValue (D f.toFun i) x)
    _ (fun i _ => (hmDL i).integrable_mul (hmD i))]
  have hsum (x) : (∑ i, hsSmoothValue (D L i) x * hsSmoothValue (D f.toFun i) x) =
      inner ℝ (hsSmoothGradient Lcore x) (hsSmoothGradient ⟨f.toFun, f.smoothOnClosure⟩ x) := by
    rw [← B.sum_inner_mul_inner]
    simp only [D, hsSmoothValue, hsSmoothGradient, Lcore, inner_gradient_left,
      inner_gradient_right, conj_trivial]
  simp_rw [hsum]
  have hibp := general_integrationByParts_core hN hV hVp f Lcore
  change (∫ x, hsSmoothValue L x * hsSmoothValue L x ∂μ) = _ at hibp
  rw [← hibp, Riesz1.poisson_norm_sq μ]
  apply integral_congr_ae
  filter_upwards [hmL.coeFn_toLp] with x hx
  rw [hx, pow_two]

/-- The general-potential compact expression is in the actual periodic Neumann
graph, Subsection 3.1. Thus the smooth identities concern the realized
generator, rather than merely a formal differential expression. -/
theorem general_test_mem_neumannGraph {N : ℕ+} (hN : 2 ≤ (N : ℕ))
    {V : HsEuclidean N → ℝ} (hV : ContDiffOn ℝ ∞ V (hsChamber N))
    (hVp : ∀ (k : ℤ) x, V (hsTranslate (k : ℝ) x) = V x) (f : HsTestFunction N) :
    let μ := (hsConfigurationVolume N).tilted (fun x => -hsSmoothValue V x)
    ∃ hm : MemLp (hsSmoothValue (Intrinsic.langevin V f.toFun)) 2 μ,
      (hsSobolevOfSmooth μ ⟨f.toFun, f.smoothOnClosure⟩,
        hm.toLp (hsSmoothValue (Intrinsic.langevin V f.toFun))) ∈ hsNeumannGraph μ := by
  dsimp only
  let μ := (hsConfigurationVolume N).tilted (fun x => -hsSmoothValue V x)
  have hL := Intrinsic.contDiff_langevin (isOpen_hsChamber N) hV f.smooth
    (f.tsupport_subset_chamber hN)
  have hm : MemLp (hsSmoothValue (Intrinsic.langevin V f.toFun)) 2 μ :=
    memLp_hsLiftPoint μ 2 hL.continuous.continuousOn
  refine ⟨hm, fun h => ?_⟩
  change hsDirichletForm μ (hsSobolevOfSmooth μ ⟨f.toFun, f.smoothOnClosure⟩) h =
    inner ℝ (hm.toLp (hsSmoothValue (Intrinsic.langevin V f.toFun))) (hsSobolevValue μ h)
  rw [hsDirichletForm_eq_integral, L2.inner_def]
  have hg := (f.smoothOnClosure.memLp_gradient μ).coeFn_toLp
  have hi := general_integrationByParts hN hV hVp f h
  calc
    _ = ∫ x, inner ℝ (hsSobolevGradient μ h x)
        (hsSmoothGradient ⟨f.toFun, f.smoothOnClosure⟩ x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      change hsSobolevGradient μ (hsSobolevOfSmooth μ ⟨f.toFun, f.smoothOnClosure⟩) x = _ at hx
      rw [hx, real_inner_comm]
    _ = ∫ x, hsSobolevValue μ h x * hsSmoothValue (Intrinsic.langevin V f.toFun) x ∂μ := hi.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hm.coeFn_toLp] with x hx
      rw [hx, Real.inner_apply, mul_comm]

/-- See Subsection 3.1 of the paper, arbitrary smooth convex periodic particle potential:
scalar integration by parts for every H¹ test, the full coordinate commutator,
and the integrable vector-energy/L² identity. The positive finite partition
function is part of the Gibbs data. Full-domain integration by parts is
`generator_integrationByParts`, whose variational graph is the library graph. -/
theorem general_identities {N : ℕ+} (hN : 2 ≤ (N : ℕ))
    {V : HsEuclidean N → ℝ} (hV : ContDiffOn ℝ ∞ V (hsChamber N))
    (_hconvex : ConvexOn ℝ (hsChamber N) V)
    (hVp : ∀ (k : ℤ) x, V (hsTranslate (k : ℝ) x) = V x)
    (hZ : Integrable (fun x => Real.exp (-hsSmoothValue V x)) (hsConfigurationVolume N))
    (hZpos : 0 < ∫ x, Real.exp (-hsSmoothValue V x) ∂hsConfigurationVolume N)
    (f : HsTestFunction N) :
    let μ := (hsConfigurationVolume N).tilted (fun x => -hsSmoothValue V x)
    let B := stdOrthonormalBasis ℝ (HsEuclidean N)
    let e := fun y => (∑ i, inner ℝ
      (gradient (fun z => fderiv ℝ f.toFun z (B i)) y)
      (gradient (fun z => fderiv ℝ f.toFun z (B i)) y)) +
      fderiv ℝ (fderiv ℝ V) y (gradient f.toFun y) (gradient f.toFun y)
    IsProbabilityMeasure μ ∧
    (∀ h : HsSobolev μ,
      (∫ x, hsSobolevValue μ h x * hsSmoothValue (Intrinsic.langevin V f.toFun) x ∂μ) =
        ∫ x, inner ℝ (hsSobolevGradient μ h x)
          (hsSmoothGradient ⟨f.toFun, f.smoothOnClosure⟩ x) ∂μ) ∧
    (∀ x ∈ hsChamber N, ∀ i : Fin (N : ℕ),
      fderiv ℝ (Intrinsic.langevin V f.toFun) x (EuclideanSpace.single i 1) =
        Intrinsic.langevin V (fun y => fderiv ℝ f.toFun y (EuclideanSpace.single i 1)) x +
        ∑ j, hessianMatrix V x i j * gradient f.toFun x j) ∧
    ∃ hm : MemLp (hsSmoothValue (Intrinsic.langevin V f.toFun)) 2 μ,
      Integrable (hsSmoothValue e) μ ∧ (∫ x, hsSmoothValue e x ∂μ) =
        ‖hm.toLp (hsSmoothValue (Intrinsic.langevin V f.toFun))‖ ^ 2 := by
  dsimp only
  have : NeZero (hsConfigurationVolume N) := ⟨fun hz => by
    rw [hz, integral_zero_measure] at hZpos
    exact (lt_irrefl 0) hZpos⟩
  refine ⟨isProbabilityMeasure_tilted hZ, general_integrationByParts hN hV hVp f,
    fun x hx i => Intrinsic.coordinate_commutator
      (hV.contDiffAt ((isOpen_hsChamber N).mem_nhds hx)) f.smooth i,
    general_gradient_energy hN hV hVp f⟩

/-- See Subsection 3.1 of the paper, periodic particle scalar identity for the paper's
pair-potential data. Riesz1's theorem already permits every completed H¹ test,
including tests meeting the rotation seam. No collision-barrier hypothesis is
needed for this compact collision-separated identity. -/
theorem integrationByParts {N : ℕ+} {c : ℝ} (hN : 2 ≤ (N : ℕ))
    (χ : Riesz1.HsPairPotentials N c) (hc : 0 < c) (f : Riesz1.HsTestFunction N)
    (h : Riesz1.HsSobolev
      (Riesz1.hsQuotientGibbsProbability χ hc : Measure (Riesz1.HsConfiguration N))) :
    (∫ x, Riesz1.hsLangevin χ f x * Riesz1.hsSobolevValue
      (Riesz1.hsQuotientGibbsProbability χ hc : Measure (Riesz1.HsConfiguration N)) h x
      ∂(Riesz1.hsQuotientGibbsProbability χ hc : Measure (Riesz1.HsConfiguration N))) =
      ∫ x, inner ℝ (Riesz1.hsSmoothGradient ⟨f.toFun, f.smoothOnClosure⟩ x)
        (Riesz1.hsSobolevGradient
          (Riesz1.hsQuotientGibbsProbability χ hc : Measure (Riesz1.HsConfiguration N)) h x)
        ∂(Riesz1.hsQuotientGibbsProbability χ hc : Measure (Riesz1.HsConfiguration N)) :=
  Riesz1.hsIntegrationByParts hN χ hc f h

/-- See Subsection 3.1 of the paper, periodic particle commutator in the original particle
metric. The Hessian is exactly the classical matrix. -/
theorem commutator {N : ℕ+} {c : ℝ} (χ : Riesz1.HsPairPotentials N c)
    (f : Riesz1.HsTestFunction N) {x : Riesz1.HsEuclidean N}
    (hx : x ∈ Riesz1.hsChamber N) (i : Fin (N : ℕ)) :
    fderiv ℝ (Intrinsic.langevin (Riesz1.hsPairExpression χ) f.toFun) x
      (EuclideanSpace.single i 1) =
      Intrinsic.langevin (Riesz1.hsPairExpression χ)
        (fun y => fderiv ℝ f.toFun y (EuclideanSpace.single i 1)) x +
      ∑ j, hessianMatrix (Riesz1.hsPairExpression χ) x i j * gradient f.toFun x j :=
  Intrinsic.coordinate_commutator
    ((Riesz1.hsPairExpression_contDiffOn χ).contDiffAt ((Riesz1.isOpen_hsChamber N).mem_nhds hx))
    f.smooth i

/-- See Subsection 3.1 of the paper, integrated periodic particle commutator. This is the
actual library vector form and L² norm. No new vector-energy encoding is used. -/
theorem gradient_energy {N : ℕ+} {c : ℝ} (hN : 2 ≤ (N : ℕ))
    (χ : Riesz1.HsPairPotentials N c) (hc : 0 < c) (f : Riesz1.HsTestFunction N) :
    let μ : Measure (Riesz1.HsConfiguration N) := Riesz1.hsQuotientGibbsProbability χ hc
    let u := Riesz1.hsVectorJetElt χ hN hc μ (Riesz1.hsGradientTestTuple hN f)
    Riesz1.hsVectorSobolevForm χ hN hc μ u u =
      ‖(Riesz1.memLp_hsLangevin hN χ f μ).toLp (Riesz1.hsLangevin χ f)‖ ^ 2 :=
  Riesz1.hsGradient_vector_energy hN χ hc f

/-- See Subsection 3.1 of the paper, full-domain particle identity, using the library's
Neumann graph on the periodic quotient. -/
theorem generator_integrationByParts {N : ℕ+}
    (μ : Measure (Riesz1.HsConfiguration N)) [IsFiniteMeasure μ]
    (p : Riesz1.hsNeumannGraph μ) (h : Riesz1.HsSobolev μ) :
    (∫ x, p.val.2 x * Riesz1.hsSobolevValue μ h x ∂μ) =
      ∫ x, inner ℝ (Riesz1.hsSobolevGradient μ p.val.1 x)
        (Riesz1.hsSobolevGradient μ h x) ∂μ :=
  (Riesz1.hsNeumannGraph_eq_integral μ p h).symm

end ParticleIntegration
end Riesz2
