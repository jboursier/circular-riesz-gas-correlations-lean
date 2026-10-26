/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.LangevinCommutator
public import Riesz1.ToMathlib.WeightedSobolev.LocalIntegrationByParts
public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Tactic

/-!
# Intrinsic Langevin calculus

Local scalar integration by parts and the integrated smooth commutator on any
finite dimensional real Euclidean space, including a zero dimensional space.
The metric is the supplied inner product. In particular the space may itself
be an affine simplex's direction space. No particle metric is transported.
The directional commutator and local Lebesgue integration by parts are reused
from Riesz1.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ContDiff Laplacian

namespace Riesz2.Intrinsic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The classical scalar expression in the specified Euclidean metric (Subsection 3.1).
Statements below evaluate derivatives of the potential only in its smooth domain.
For compact interior tests the expression vanishes outside their closed support. -/
def langevin (V f : E → ℝ) (x : E) : ℝ :=
  inner ℝ (gradient V x) (gradient f x) - Δ f x

/-- Directional form of the classical commutator, Subsection 3.1.
Smoothness of the potential is needed only at the point of evaluation. -/
theorem directional_commutator {V f : E → ℝ} {x : E}
    (hV : ContDiffAt ℝ ∞ V x) (hf : ContDiff ℝ ∞ f) (v : E) :
    fderiv ℝ (langevin V f) x v =
      langevin V (fun y => fderiv ℝ f y v) x +
        fderiv ℝ (fderiv ℝ V) x v (gradient f x) := by
  have h := Riesz1.langevin_direction_commutator hV hf v
  change fderiv ℝ (langevin V f) x v -
    langevin V (fun y => fderiv ℝ f y v) x = _ at h
  linarith

/-- Local vanishing of a test implies local vanishing of its scalar expression. -/
theorem langevin_zero {V f : E → ℝ} {x : E} (hx : x ∉ tsupport f) :
    langevin V f x = 0 := by
  have he := notMem_tsupport_iff_eventuallyEq.mp hx
  have hg := he.gradient_eq
  have hl := (laplacian_congr_nhds he).eq_of_nhds
  change Δ f x = Δ (fun _ : E => (0 : ℝ)) x at hl
  rw [laplacian_const] at hl
  simp [langevin, hg, hl]

theorem tsupport_langevin_subset (V f : E → ℝ) :
    tsupport (langevin V f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  by_contra h
  exact hx (langevin_zero h)

theorem hasCompactSupport_langevin (V : E → ℝ) {f : E → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (langevin V f) :=
  hf.of_isClosed_subset (isClosed_tsupport _) (tsupport_langevin_subset V f)

/-- The scalar expression is a smooth global interior test even when the potential
has singularities at the boundary. -/
theorem contDiff_langevin {U : Set E} (hU : IsOpen U) {V f : E → ℝ}
    (hV : ContDiffOn ℝ ∞ V U) (hf : ContDiff ℝ ∞ f) (hfU : tsupport f ⊆ U) :
    ContDiff ℝ ∞ (langevin V f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · have hgV := (toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp x
      ((hV.contDiffAt (hU.mem_nhds hx)).fderiv_right (m := ∞) (by simp))
    have hgf := (toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp
      (hf.fderiv_right (m := ∞) (by simp))
    exact (hgV.inner ℝ hgf.contDiffAt).sub (Riesz1.contDiff_laplacian hf).contDiffAt
  · have hxs : x ∉ tsupport f := fun h => hx (hfU h)
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hxs] with y hy
    exact langevin_zero hy

/-- Trace expansion in an arbitrary orthonormal basis. -/
theorem langevin_eq_sum {ι : Type*} [Fintype ι]
    (B : OrthonormalBasis ι ℝ E) {V f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x : E) :
    langevin V f x = ∑ i,
      (fderiv ℝ V x (B i) * fderiv ℝ f x (B i) -
        fderiv ℝ (fun y => fderiv ℝ f y (B i)) x (B i)) := by
  have hd := (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  unfold langevin
  rw [← B.sum_inner_mul_inner (gradient V x) (gradient f x),
    laplacian_eq_iteratedFDeriv_orthonormalBasis f B, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [inner_gradient_left, inner_gradient_right, conj_trivial]
  rw [fderiv_clm_apply (hd x) (differentiableAt_const (B i)), iteratedFDeriv_two_apply]
  simp

/-- Basis expansion of the Hessian term in the differentiated equation. -/
theorem hessian_commutator {ι : Type*} [Fintype ι] (B : OrthonormalBasis ι ℝ E)
    {V f : E → ℝ} {x : E} (hV : ContDiffAt ℝ ∞ V x) (hf : ContDiff ℝ ∞ f) :
    fderiv ℝ (fderiv ℝ V) x (gradient f x) (gradient f x) =
      ∑ i, ((fderiv ℝ (langevin V f) x (B i) -
        langevin V (fun y => fderiv ℝ f y (B i)) x) * fderiv ℝ f x (B i)) := by
  have he := congrArg (fun z => fderiv ℝ (fderiv ℝ V) x z (gradient f x))
    (B.sum_repr (gradient f x))
  simp only [map_sum, map_smul, sum_apply, smul_apply,
    smul_eq_mul, OrthonormalBasis.repr_apply_apply, inner_gradient_right, conj_trivial] at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro i _
  rw [directional_commutator hV hf (B i)]
  ring

section Measure

variable [MeasurableSpace E] [BorelSpace E]
  (σ : Measure E) [σ.IsAddHaarMeasure] {U : Set E} (hU : IsOpen U)
  {V : E → ℝ} (hV : ContDiffOn ℝ ∞ V U)

/-- Compact smooth gradients have finite weighted norm for every finite measure. -/
theorem memLp_gradient {μ : Measure E} [IsFiniteMeasure μ] {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) : MemLp (gradient f) 2 μ := by
  have hc : Continuous (gradient f) :=
    (toDual ℝ E).symm.continuous.comp (hf.continuous_fderiv (by simp))
  exact hc.memLp_of_hasCompactSupport ((hfc.fderiv ℝ).comp_left (map_zero _))

include hU in
/-- A compact interior factor makes a locally continuous product integrable
against any finite measure. No behavior outside the open set is assumed. -/
theorem integrable_cutoff_mul {μ : Measure E} [IsFiniteMeasure μ] {ψ a : E → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U)
    (ha : ContinuousOn a U) : Integrable (fun x => ψ x * a x) μ :=
  (Riesz1.WeightedSobolev.continuous_cutoff_mul hU hψ hψU ha).integrable_of_hasCompactSupport
    hψc.mul_right

include hU hV in
/-- The directional integration by parts formula for the normalized exponential
density. The test is compactly supported inside the smooth domain, whereas the
other function only needs local smoothness. This internal identity remains true
before positivity and finiteness of the normalizer are established. -/
theorem directional_integrationByParts {ψ h : E → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U)
    (hh : ContDiffOn ℝ ∞ h U) (v : E) :
    (∫ x, ψ x * fderiv ℝ h x v ∂((σ.restrict U).tilted (fun x => -V x))) =
      ∫ x, h x * (fderiv ℝ V x v * ψ x - fderiv ℝ ψ x v)
        ∂((σ.restrict U).tilted (fun x => -V x)) := by
  let Z := ∫ x in U, Real.exp (-V x) ∂σ
  let w := fun x => Real.exp (-V x) / Z
  have hw : ContDiffOn ℝ ∞ w U := (hV.neg.exp).div_const Z
  have hi := Riesz1.WeightedSobolev.integral_weighted_fderiv_of_compact_test
    (μ := σ) hU hψ hψc hψU hh hw v
  have hd (x : E) (hx : x ∈ U) :
      fderiv ℝ (fun y => ψ y * w y) x v =
        w x * (fderiv ℝ ψ x v - fderiv ℝ V x v * ψ x) := by
    have hdx := ((hV.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
    have hdw : HasFDerivAt w
        ((Real.exp (-V x) / Z) • (-fderiv ℝ V x)) x := by
      simpa [w, div_eq_mul_inv, smul_smul, mul_comm] using
        (hdx.hasFDerivAt.neg.exp.const_mul Z⁻¹)
    rw [fderiv_fun_mul (hψ.differentiable (by simp) x) hdw.differentiableAt]
    simp only [add_apply, smul_apply, smul_eq_mul, hdw.fderiv, neg_apply]
    dsimp only [w]
    ring
  rw [integral_tilted, integral_tilted]
  change (∫ x in U, w x * (ψ x * fderiv ℝ h x v) ∂σ) =
    ∫ x in U, w x * (h x * (fderiv ℝ V x v * ψ x - fderiv ℝ ψ x v)) ∂σ
  calc
    _ = ∫ x in U, (ψ x * w x) * fderiv ℝ h x v ∂σ :=
      integral_congr_ae (Eventually.of_forall fun x => by ring)
    _ = ∫ x, (ψ x * w x) * fderiv ℝ h x v ∂σ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hψU h))]
        simp)
    _ = -∫ x, h x * fderiv ℝ (fun y => ψ y * w y) x v ∂σ := hi
    _ = ∫ x in U, w x * (h x * (fderiv ℝ V x v * ψ x - fderiv ℝ ψ x v)) ∂σ := by
      rw [← integral_neg]
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U)
        (f := fun x => -(h x * fderiv ℝ (fun y => ψ y * w y) x v))]
      · apply integral_congr_ae
        filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
        rw [hd x hx]
        ring
      · intro x hx
        have hs : tsupport (fun x => fderiv ℝ (fun y => ψ y * w y) x v) ⊆ U :=
          (tsupport_fderiv_apply_subset ℝ v).trans (tsupport_mul_subset_left.trans hψU)
        rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero, neg_zero]

include hU hV in
/-- Compact-support scalar integration by parts in the intrinsic metric,
Subsection 3.1. The second function may be any locally smooth function. -/
theorem integrationByParts {f h : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U)
    (hh : ContDiffOn ℝ ∞ h U) :
    (∫ x, h x * langevin V f x ∂((σ.restrict U).tilted (fun x => -V x))) =
      ∫ x, inner ℝ (gradient h x) (gradient f x)
        ∂((σ.restrict U).tilted (fun x => -V x)) := by
  let μ := (σ.restrict U).tilted (fun x => -V x)
  let B := stdOrthonormalBasis ℝ E
  let D := fun (g : E → ℝ) i x => fderiv ℝ g x (B i)
  have hD (i) : ContDiff ℝ ∞ (D f i) :=
    (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hs (i) : tsupport (D f i) ⊆ U :=
    (tsupport_fderiv_apply_subset ℝ (B i)).trans hfU
  have hc (i) : HasCompactSupport (D f i) := hfc.fderiv_apply ℝ (B i)
  have hd (g : E → ℝ) (hg : ContDiffOn ℝ ∞ g U) (i) : ContinuousOn (D g i) U :=
    (hg.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const
  have hi₁ (i) : Integrable (fun x => D f i x * D h i x) μ :=
    integrable_cutoff_mul hU (hD i).continuous (hc i) (hs i) (hd h hh i)
  have hi₂ (i) : Integrable (fun x => h x *
      (D V i x * D f i x - D (D f i) i x)) μ := by
    have ha := integrable_cutoff_mul (μ := μ) hU (hD i).continuous (hc i) (hs i)
      (hh.continuousOn.mul (hd V hV i))
    have hb := integrable_cutoff_mul (μ := μ) hU
      (((hD i).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
      ((hc i).fderiv_apply ℝ (B i))
      ((tsupport_fderiv_apply_subset ℝ (B i)).trans (hs i)) hh.continuousOn
    convert ha.sub hb using 1
    ext x
    dsimp only [D, Pi.sub_apply, Pi.mul_apply]
    ring
  have hpoint (x) : inner ℝ (gradient h x) (gradient f x) =
      ∑ i, D f i x * D h i x := by
    rw [← B.sum_inner_mul_inner (gradient h x) (gradient f x)]
    apply Finset.sum_congr rfl
    intro i _
    simp only [inner_gradient_left, inner_gradient_right, conj_trivial, D]
    ring
  symm
  calc
    _ = ∫ x, ∑ i, D f i x * D h i x ∂μ :=
      integral_congr_ae (Eventually.of_forall hpoint)
    _ = ∑ i, ∫ x, D f i x * D h i x ∂μ := integral_finsetSum _ (fun i _ => hi₁ i)
    _ = ∑ i, ∫ x, h x * (D V i x * D f i x - D (D f i) i x) ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      exact directional_integrationByParts σ hU hV (hD i) (hc i) (hs i) hh (B i)
    _ = ∫ x, ∑ i, h x * (D V i x * D f i x - D (D f i) i x) ∂μ :=
      (integral_finsetSum _ (fun i _ => hi₂ i)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [langevin_eq_sum B hf x, Finset.mul_sum]

include hU hV in
/-- Integrated smooth commutator in an arbitrary orthonormal basis (Subsection 3.1).
The left side is exactly `q(∇f,∇f)` from Subsection 3.1. The right side is the
square of the scalar source. All quantities are integrable. -/
theorem gradient_energy {ι : Type*} [Fintype ι] (B : OrthonormalBasis ι ℝ E)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) :
    let μ := (σ.restrict U).tilted (fun x => -V x)
    let e := fun x =>
      (∑ i, inner ℝ (gradient (fun y => fderiv ℝ f y (B i)) x)
        (gradient (fun y => fderiv ℝ f y (B i)) x)) +
      fderiv ℝ (fderiv ℝ V) x (gradient f x) (gradient f x)
    MemLp (langevin V f) 2 μ ∧ Integrable e μ ∧
      (∫ x, e x ∂μ) = ∫ x, (langevin V f x) ^ 2 ∂μ := by
  classical
  dsimp only
  let μ := (σ.restrict U).tilted (fun x => -V x)
  let D := fun (g : E → ℝ) i x => fderiv ℝ g x (B i)
  let L := langevin V f
  have hL : ContDiff ℝ ∞ L := contDiff_langevin hU hV hf hfU
  have hcL : HasCompactSupport L := hasCompactSupport_langevin V hfc
  have hmemL : MemLp L 2 μ := hL.continuous.memLp_of_hasCompactSupport hcL
  have hD (i) : ContDiff ℝ ∞ (D f i) :=
    (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hcD (i) : HasCompactSupport (D f i) := hfc.fderiv_apply ℝ (B i)
  have hsD (i) : tsupport (D f i) ⊆ U :=
    (tsupport_fderiv_apply_subset ℝ (B i)).trans hfU
  let A := fun i x => inner ℝ (gradient (D f i) x) (gradient (D f i) x)
  let T := fun i x => (D L i x - langevin V (D f i) x) * D f i x
  have hma (i) : Integrable (A i) μ :=
    (memLp_gradient (μ := μ) (hD i) (hcD i)).norm.integrable_sq.congr
      (Eventually.of_forall fun x => (real_inner_self_eq_norm_sq (gradient (D f i) x)).symm)
  have hmb (i) : MemLp (D f i) 2 μ := (hD i).continuous.memLp_of_hasCompactSupport (hcD i)
  have hml (i) : MemLp (langevin V (D f i)) 2 μ :=
    (contDiff_langevin hU hV (hD i) (hsD i)).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_langevin V (hcD i))
  have hmd (i) : MemLp (D L i) 2 μ :=
    ((hL.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous.memLp_of_hasCompactSupport
      (hcL.fderiv_apply ℝ (B i))
  have hmt (i) : Integrable (T i) μ := ((hmd i).sub (hml i)).integrable_mul (hmb i)
  have hpoint (x : E) (hx : x ∈ U) :
      fderiv ℝ (fderiv ℝ V) x (gradient f x) (gradient f x) = ∑ i, T i x :=
    hessian_commutator B (hV.contDiffAt (hU.mem_nhds hx)) hf
  have hμU : ∀ᵐ x ∂μ, x ∈ U :=
    (tilted_absolutelyContinuous (σ.restrict U) (fun x => -V x)).ae_le
      (ae_restrict_mem hU.measurableSet)
  have he : (fun x => (∑ i, inner ℝ (gradient (D f i) x) (gradient (D f i) x)) +
      fderiv ℝ (fderiv ℝ V) x (gradient f x) (gradient f x)) =ᵐ[μ]
      (fun x => ∑ i, (A i x + T i x)) := by
    filter_upwards [hμU] with x hx
    rw [hpoint x hx, Finset.sum_add_distrib]
  have hei : Integrable (fun x => ∑ i, (A i x + T i x)) μ :=
    integrable_finsetSum _ (fun i _ => (hma i).add (hmt i))
  refine ⟨hmemL, hei.congr he.symm, ?_⟩
  change (∫ x, (∑ i, A i x) + fderiv ℝ (fderiv ℝ V) x (gradient f x) (gradient f x) ∂μ) = _
  rw [integral_congr_ae he,
    integral_finsetSum (f := fun i x => A i x + T i x) _ (fun i _ => (hma i).add (hmt i))]
  have hi (i) : (∫ x, A i x + T i x ∂μ) = ∫ x, D L i x * D f i x ∂μ := by
    rw [integral_add (hma i) (hmt i)]
    have hibp := integrationByParts σ hU hV (hD i) (hcD i) (hsD i) (hD i).contDiffOn
    change (∫ x, D f i x * langevin V (D f i) x ∂μ) = ∫ x, A i x ∂μ at hibp
    rw [← hibp]
    have ht : T i = (fun x => D L i x * D f i x) -
        (fun x => D f i x * langevin V (D f i) x) := by ext x; dsimp [T]; ring
    rw [ht]
    simp only [Pi.sub_apply]
    rw [integral_sub (f := fun x => D L i x * D f i x)
      (g := fun x => D f i x * langevin V (D f i) x)
      ((hmd i).integrable_mul (hmb i)) ((hmb i).integrable_mul (hml i))]
    ring
  simp_rw [hi]
  rw [← integral_finsetSum (f := fun i x => D L i x * D f i x)
    _ (fun i _ => (hmd i).integrable_mul (hmb i))]
  have hsum (x) : (∑ i, D L i x * D f i x) = inner ℝ (gradient L x) (gradient f x) := by
    rw [← B.sum_inner_mul_inner (gradient L x) (gradient f x)]
    simp only [D, inner_gradient_left, inner_gradient_right, conj_trivial]
  simp_rw [hsum]
  have hibp := integrationByParts σ hU hV hf hfc hfU hL.contDiffOn
  change (∫ x, L x * L x ∂μ) = _ at hibp
  simpa only [pow_two] using hibp.symm

end Measure
end Riesz2.Intrinsic
