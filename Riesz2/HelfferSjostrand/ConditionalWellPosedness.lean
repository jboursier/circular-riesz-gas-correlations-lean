/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.MarginalCollision
public import Riesz2.ToMathlib.AffinePullbackEstimates
public import Riesz2.ToMathlib.ConvexTangentHessian
public import Riesz1.ToMathlib.LogConcave.NegativePower

/-!
# Conditional and interpolating laws

Proof interfaces for Appendix A.
The chart, tangent space, physical energy and marginal density are the
existing ones. Constants may depend on the fixed interior length and exteriors.
-/

public section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal

namespace Riesz2.ConditionalWellPosedness

/-- The existing centred chart is smooth on its whole tangent space. -/
theorem centredChart_smooth (n : ℕ) (L : ℝ) :
    ContDiff ℝ ∞ (AffineSimplex.centredChart n L) :=
  (AffineSimplex.Tangent n).subtypeL.contDiff.add contDiff_const

/-- Interior fixed-length fibres lie in the proper marginal domain. -/
theorem fibre_subset_marginal (n : ℕ) {L M : ℝ} (hLM : L < M)
    {z : AffineSimplex.Tangent n}
    (hz : z ∈ AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L) :
    AffineSimplex.centredChart n L z ∈ AffineSimplex.chartDomain (n + 1) M := by
  exact ⟨hz.1, hz.2.trans_lt hLM⟩

set_option backward.isDefEq.respectTransparency false in
/-- The positive fixed-length simplex has an open domain in its tangent space. -/
theorem fibre_isOpen (n : ℕ) (L : ℝ) :
    IsOpen (AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L) := by
  have he : AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L =
      {z | ∀ i, 0 < AffineSimplex.centredChart n L z i} := by
    ext z
    exact and_iff_left (AffineSimplex.sum_centredChart n L z)
  rw [he]
  change IsOpen (Subtype.val ⁻¹' {y : EuclideanSpace ℝ (Fin (n + 1)) |
    ∀ i, 0 < y i + AffineSimplex.centre n L i})
  apply IsOpen.preimage continuous_subtype_val
  simp only [ofPred_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
    ((PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) i).add continuous_const)

/-- The fixed-length simplex remains bounded in the isometric chart. -/
theorem fibre_isBounded (n : ℕ) (L : ℝ) :
    Bornology.IsBounded
      (AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L) := by
  have hs : Bornology.IsBounded (AffineSimplex.massSimplex n L) := by
    rw [← AffineSimplex.image_chart_domain]
    exact (AffineSimplex.tangentMap n).toContinuousLinearMap.lipschitzWith.isBounded_image
      (AffineSimplex.isBounded_chartDomain n L) |>.add
      (Bornology.isBounded_singleton (x := AffineSimplex.chart n L 0)) |>.subset (by
        rintro y ⟨x, hx, rfl⟩
        exact ⟨_, ⟨x, hx, rfl⟩, _, rfl, (AffineSimplex.chart_eq_tangentMap_add n L x).symm⟩)
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hs
  apply Metric.isBounded_iff.mpr
  refine ⟨C, fun x hx y hy => ?_⟩
  rw [← (AffineSimplex.isometry_centredChart n L).dist_eq]
  exact hC hx hy

/-- Convexity of the fixed-length domain uses the same affine mass simplex. -/
theorem fibre_convex (n : ℕ) (L : ℝ) :
    Convex ℝ (AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, AffineSimplex.sum_centredChart n L _⟩
  have he : AffineSimplex.centredChart n L (a • x + b • y) i =
      a * AffineSimplex.centredChart n L x i +
        b * AffineSimplex.centredChart n L y i := by
    simp only [AffineSimplex.centredChart, PiLp.add_apply, PiLp.smul_apply,
      Submodule.coe_add, Submodule.coe_smul, smul_eq_mul]
    have h := congrArg (fun r : ℝ => r * (AffineSimplex.centre n L i)) hab
    nlinarith only [h]
  rw [he]
  exact ElementaryBarriers.pos_of_convex_comb (hx.1 i) (hy.1 i) ha hb hab

/-- Restricting a smooth marginal to an interior fixed length preserves smoothness.
This is the smoothness clause of Appendix A. -/
theorem marginal_fibre_smooth (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin ((n + 1) + m + 1)))
    {L : ℝ} (hL : L < ((n + 1 + m : ℕ) + 1 : ℝ)) :
    ContDiffOn ℝ ∞ (fun z : AffineSimplex.Tangent n =>
      -Real.log (∫ y : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n + 1) m σ
          (AffineSimplex.centredChart n L z, y)).toReal))
      (AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L) := by
  exact (MarginalHessian.physical_marginal_potential_smooth p (n + 1) m
    (by omega) σ).comp (centredChart_smooth n L).contDiffOn
      (fun z hz => fibre_subset_marginal n hL hz)

/-- Strict marginal curvature survives restriction to the zero-sum tangent space.
This is the curvature clause of Appendix A. -/
theorem marginal_fibre_strict_curvature (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin ((n + 1) + m + 1)))
    {L : ℝ} (hL : L < ((n + 1 + m : ℕ) + 1 : ℝ)) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ z ∈ AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L,
        ∀ u : AffineSimplex.Tangent n,
          κ * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (fun z : AffineSimplex.Tangent n =>
            -Real.log (∫ y : EuclideanSpace ℝ (Fin m),
              (ProperMarginalChart.chartDensity p (n + 1) m σ
                (AffineSimplex.centredChart n L z, y)).toReal))) z u u := by
  obtain ⟨κ, hκ, hcurv⟩ := MarginalCollision.marginal_strict_curvature p (n + 1) m
    (by omega) σ
  refine ⟨κ, hκ, fun z hz u => ?_⟩
  have hx := fibre_subset_marginal n hL hz
  have hV := ((MarginalHessian.physical_marginal_potential_smooth p (n + 1) m
    (by omega) σ).contDiffAt
      ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds hx)).of_le
        (by norm_num : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  change κ * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (fun z : AffineSimplex.Tangent n =>
    -Real.log (∫ y : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p (n + 1) m σ
        ((AffineSimplex.Tangent n).subtypeL z + AffineSimplex.centre n L, y)).toReal))) z u u
  rw [AffineMetricTransport.hessian_comp_affine
    (AffineSimplex.Tangent n).subtypeL (AffineSimplex.centre n L) hV]
  exact hcurv _ hx u.val

/-- Convex functions restrict to the fixed-length affine slice. -/
theorem convexOn_fibre_pullback (n : ℕ) {L M : ℝ} (hLM : L < M)
    {W : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hW : ConvexOn ℝ (AffineSimplex.chartDomain (n + 1) M) W) :
    ConvexOn ℝ (AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L)
      (fun z => W (AffineSimplex.centredChart n L z)) := by
  let T : AffineSimplex.Tangent n →ᵃ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    (AffineSimplex.Tangent n).subtype.toAffineMap +
      AffineMap.const ℝ _ (AffineSimplex.centre n L)
  exact (hW.comp_affineMap T).subset (fun z hz => fibre_subset_marginal n hLM hz)
    (fibre_convex n L)

/-- On an interior fixed-length fibre, the exterior-mass barrier is constant.
The remaining inverse-gap barrier has exactly the physical coefficient
`2β`. Appendix A. -/
theorem marginal_fibre_barrier (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin ((n + 1) + m + 1)))
    {L : ℝ} (hL : L < ((n + 1 + m : ℕ) + 1 : ℝ)) :
    ∃ R : AffineSimplex.Tangent n → ℝ,
      ContDiffOn ℝ ∞ R
        (AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L) ∧
      ConvexOn ℝ
        (AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L) R ∧
      ∀ z ∈ AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L,
        -Real.log (∫ y : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity p (n + 1) m σ
            (AffineSimplex.centredChart n L z, y)).toReal) =
        (∑ i, (2 * p.val.1) * (AffineSimplex.centredChart n L z i) ^ (-p.val.2)) + R z := by
  obtain ⟨R, hRs, hRc, he⟩ := MarginalCollision.marginal_barrier_decomposition p
    (n + 1) m (by omega) σ
  let c : ℝ := 2 * p.val.1 * (((n + 1 + m : ℕ) + 1 : ℝ) - L) ^ (-p.val.2)
  refine ⟨fun z => R (AffineSimplex.centredChart n L z) + c,
    (hRs.comp (centredChart_smooth n L).contDiffOn
      (fun z hz => fibre_subset_marginal n hL hz)).add contDiffOn_const,
    (convexOn_fibre_pullback n hL hRc).add_const c, fun z hz => ?_⟩
  have hh := he _ (fibre_subset_marginal n hL hz)
  dsimp only at hh
  rw [hh, AffineSimplex.sum_centredChart,
    ← Finset.mul_sum]
  dsimp only [c]
  ring

/-- Holding exterior mass fixed converts the marginal Hessian envelope into
an envelope involving only active gaps. The tangent chart is isometric. Appendix A. -/
theorem marginal_fibre_hessian_upper (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin ((n + 1) + m + 1)))
    {L : ℝ} (hL : L < ((n + 1 + m : ℕ) + 1 : ℝ)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ z ∈ AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L,
        ∀ u : AffineSimplex.Tangent n,
          fderiv ℝ (fderiv ℝ (fun z : AffineSimplex.Tangent n =>
            -Real.log (∫ y : EuclideanSpace ℝ (Fin m),
              (ProperMarginalChart.chartDensity p (n + 1) m σ
                (AffineSimplex.centredChart n L z, y)).toReal))) z u u ≤
          C * (1 + (⨅ i, AffineSimplex.centredChart n L z i) ^ (-p.val.2 - 2)) * ‖u‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := MarginalCollision.marginal_hessian_upper p (n + 1) m
    (by omega) σ
  let e : ℝ := ((n + 1 + m : ℕ) + 1 : ℝ) - L
  have he : 0 < e := sub_pos.mpr hL
  refine ⟨C * (1 + e ^ (-p.val.2 - 2)), by positivity, fun z hz u => ?_⟩
  let δ := ⨅ i, AffineSimplex.centredChart n L z i
  obtain ⟨i, hi⟩ := ElementaryBarriers.exists_iInf_eq_apply
    (fun i => AffineSimplex.centredChart n L z i)
  have hδ : 0 < δ := by dsimp only [δ]; rw [hi]; exact hz.1 i
  have hx := fibre_subset_marginal n hL hz
  have hV := ((MarginalHessian.physical_marginal_potential_smooth p (n + 1) m
    (by omega) σ).contDiffAt
      ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds hx)).of_le
        (by norm_num : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  change fderiv ℝ (fderiv ℝ (fun z : AffineSimplex.Tangent n =>
    -Real.log (∫ y : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p (n + 1) m σ
        ((AffineSimplex.Tangent n).subtypeL z + AffineSimplex.centre n L, y)).toReal))) z u u ≤ _
  rw [AffineMetricTransport.hessian_comp_affine
    (AffineSimplex.Tangent n).subtypeL (AffineSimplex.centre n L) hV]
  have hb := hbound _ hx (min δ e) (lt_min hδ he)
    (fun j => (min_le_left δ e).trans (ciInf_le (Finite.bddBelow_range _) j))
    (by rw [AffineSimplex.sum_centredChart]; exact min_le_right δ e) u.val
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg ‖u‖)
  have hpow : (min δ e) ^ (-p.val.2 - 2) ≤
      δ ^ (-p.val.2 - 2) + e ^ (-p.val.2 - 2) := by
    rcases le_total δ e with h | h
    · rw [min_eq_left h]; exact le_add_of_nonneg_right (Real.rpow_nonneg he.le _)
    · rw [min_eq_right h]; exact le_add_of_nonneg_left (Real.rpow_nonneg hδ.le _)
  have hdp := Real.rpow_nonneg hδ.le (-p.val.2 - 2)
  have hep := Real.rpow_nonneg he.le (-p.val.2 - 2)
  change C * (1 + (min δ e) ^ (-p.val.2 - 2)) ≤
    (C * (1 + e ^ (-p.val.2 - 2))) * (1 + δ ^ (-p.val.2 - 2))
  nlinarith [mul_nonneg hdp hep]

/-- All amplified collision bounds for unpenalized, interior fixed-length
marginals, with constants chosen after the length. Appendix A.
The estimate is in the Euclidean metric of the zero-sum tangent space. -/
theorem marginal_fibre_collision (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin ((n + 1) + m + 1)))
    {L : ℝ} (hL : L < ((n + 1 + m : ℕ) + 1 : ℝ)) :
    let Ω := AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L
    let V := fun z : AffineSimplex.Tangent n =>
      -Real.log (∫ y : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n + 1) m σ
          (AffineSimplex.centredChart n L z, y)).toReal)
    ∀ A K : ℝ, 0 < A → 0 < K → ∃ D : ℝ, 0 ≤ D ∧ ∀ z ∈ Ω,
      K * (Metric.infDist z (frontier Ω))⁻¹ ^ 2 - D ≤
        A * ‖gradient V z‖ ^ 2 - Laplacian.laplacian V z := by
  intro Ω V
  let : Nontrivial (AffineSimplex.Tangent n) := Module.nontrivial_of_finrank_pos
    (R := ℝ) (by rw [AffineSimplex.finrank_tangent]; omega)
  let T : AffineSimplex.Tangent n →ᵃ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    (AffineSimplex.Tangent n).subtype.toAffineMap +
      AffineMap.const ℝ _ (AffineSimplex.centre n L)
  let ℓ : Fin (n + 1) → AffineSimplex.Tangent n →ᵃ[ℝ] ℝ := fun i =>
    (EuclideanSpace.proj i).toLinearMap.toAffineMap.comp T
  have hℓ (i : Fin (n + 1)) (z : AffineSimplex.Tangent n) :
      ℓ i z = AffineSimplex.centredChart n L z i := rfl
  have hΩ : Ω = {z | ∀ i, 0 < ℓ i z} := by
    ext z
    exact and_iff_left (AffineSimplex.sum_centredChart n L z)
  obtain ⟨R, hRs, hRc, hR⟩ := marginal_fibre_barrier p n m σ hL
  obtain ⟨C, hC, hupper⟩ := marginal_fibre_hessian_upper p n m σ hL
  have hΔ (z) (hz : z ∈ Ω) : Laplacian.laplacian V z ≤
      (n : ℝ) * C * (1 + (⨅ i, ℓ i z) ^ (-p.val.2 - 2)) := by
    have ht := PhysicalCollision.internal_laplacian_le V z
      (C * (1 + (⨅ i, ℓ i z) ^ (-p.val.2 - 2)))
      (by simpa only [hℓ] using hupper z hz)
    simpa only [AffineSimplex.finrank_tangent, mul_assoc] using ht
  have hb := ElementaryBarriers.radial_laplacian_lower ℓ (fun _ => 2 * p.val.1)
    (fun _ => mul_pos (by norm_num) p.property.1) p.property.2.1 hΩ
    (fibre_isBounded n L) R hRc hRs V (by simpa only [hℓ] using hR)
    ((n : ℝ) * C) hΔ
  intro A K hA hK
  obtain ⟨D, hD⟩ := hb A K hA hK
  refine ⟨max D 0, le_max_right _ _, fun z hz => ?_⟩
  have hh := hD z hz
  rw [← inv_pow] at hh
  exact (sub_le_sub_left (le_max_left D 0) _).trans hh

/-- The precise ground-state collision bound of Appendix A on an
unpenalized marginal fibre. Appendix A. -/
theorem marginal_fibre_ground_state (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin ((n + 1) + m + 1)))
    {L : ℝ} (hL : L < ((n + 1 + m : ℕ) + 1 : ℝ)) :
    let Ω := AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L
    let V := fun z : AffineSimplex.Tangent n =>
      -Real.log (∫ y : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n + 1) m σ
          (AffineSimplex.centredChart n L z, y)).toReal)
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z ∈ Ω,
      (Metric.infDist z (frontier Ω))⁻¹ ^ 2 - D ≤
        (1 / 4 : ℝ) * ‖gradient V z‖ ^ 2 -
          (1 / 2 : ℝ) * Laplacian.laplacian V z := by
  intro Ω V
  obtain ⟨D, hD, hb⟩ := marginal_fibre_collision p n m hn σ hL
    (1 / 2) 2 (by norm_num) (by norm_num)
  refine ⟨D / 2, div_nonneg hD (by norm_num), fun z hz => ?_⟩
  have h := hb z hz
  change 2 * (Metric.infDist z (frontier Ω))⁻¹ ^ 2 - D ≤
    (1 / 2 : ℝ) * ‖gradient V z‖ ^ 2 - Laplacian.laplacian V z at h
  linarith only [h]

/-- Internal normalization lemma over a nonempty open convex domain.
The lower bound is the companion library's convex-potential bound. -/
theorem internal_convex_normalizer {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Set E} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty)
    {V : E → ℝ} (hc : ConvexOn ℝ Ω V) (hs : ContinuousOn V Ω) :
    0 < ∫⁻ z in Ω, ENNReal.ofReal (Real.exp (-V z)) ∧
      (∫⁻ z in Ω, ENNReal.ofReal (Real.exp (-V z))) < ⊤ := by
  classical
  let w := fun z => ENNReal.ofReal (Real.exp (-V z))
  have hw : Measurable (Ω.indicator w) := by
    have hm := ENNReal.measurable_ofReal.comp
      (Riesz1.measurable_indicator_of_continuousOn hΩ
        (Real.continuous_exp.comp_continuousOn hs.neg))
    convert hm using 1
    funext x
    by_cases hx : x ∈ Ω <;> simp [hx, w]
  have hsupport : Function.support (Ω.indicator w) = Ω := by
    ext x
    by_cases hx : x ∈ Ω <;> simp [hx, w, Real.exp_pos (-V x)]
  constructor
  · rw [← lintegral_indicator hΩ.measurableSet, lintegral_pos_iff_support hw, hsupport]
    exact hΩ.measure_pos volume hne
  · obtain ⟨c, hbound⟩ := Riesz1.exists_lower_bound_of_convexOn hΩ hb hc
    calc
      (∫⁻ z in Ω, ENNReal.ofReal (Real.exp (-V z))) ≤
          ∫⁻ _z in Ω, ENNReal.ofReal (Real.exp (-c)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hΩ.measurableSet] with z hz
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (neg_le_neg (hbound z hz)))
      _ = ENNReal.ofReal (Real.exp (-c)) * volume Ω := by simp
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hb.measure_lt_top (μ := volume))

/-- The unpenalized marginal density has positive finite mass at every
interior length, including the one-gap fibre. Appendix A.
This statement establishes normalization before using any conditional law. -/
theorem marginal_fibre_normalizer (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin ((n + 1) + m + 1)))
    {L : ℝ} (hL0 : 0 < L) (hL : L < ((n + 1 + m : ℕ) + 1 : ℝ)) :
    let Ω := AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L
    let V := fun z : AffineSimplex.Tangent n =>
      -Real.log (∫ y : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n + 1) m σ
          (AffineSimplex.centredChart n L z, y)).toReal)
    0 < ∫⁻ z in Ω, ENNReal.ofReal (Real.exp (-V z)) ∧
      (∫⁻ z in Ω, ENNReal.ofReal (Real.exp (-V z))) < ⊤ := by
  intro Ω V
  have hΩ := fibre_isOpen n L
  have hs := marginal_fibre_smooth p n m σ hL
  have hc : ConvexOn ℝ Ω V := by
    obtain ⟨κ, hκ, hcurv⟩ := marginal_fibre_strict_curvature p n m σ hL
    apply convexOn_of_tangent_hessian_nonneg (fibre_convex n L)
      (fun x hx => (hs.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp))
      (fun x hx => ((hs.contDiffAt (hΩ.mem_nhds hx)).fderiv_right (m := 1) (by simp)).differentiableAt (by simp))
    intro x hx y _ z _
    exact (mul_nonneg hκ.le (sq_nonneg ‖z - y‖)).trans (hcurv x hx (z - y))
  have hne : Ω.Nonempty := by
    refine ⟨0, ?_⟩
    change AffineSimplex.centredChart n L 0 ∈ AffineSimplex.massSimplex n L
    simpa only [AffineSimplex.centredChart, Submodule.coe_zero, zero_add] using
      AffineSimplex.centre_mem_simplex n hL0
  exact internal_convex_normalizer hΩ (fibre_isBounded n L) hne hc hs.continuousOn

/-- The one-gap branch of Appendix A:
normalizing any finite real potential on the one-gap simplex gives its point
mass. This applies in particular to the specified physical interpolants. -/
theorem one_gap_law {L : ℝ} (hL : 0 < L)
    (V : EuclideanSpace ℝ (Fin 1) → ℝ) :
    ∃ h0 ht, AffineFibre.normalizedMeasure (AffineSimplex.simplexVolume 0 L)
      (fun x => ENNReal.ofReal (Real.exp (-V x))) h0 ht =
        Measure.dirac (AffineSimplex.chart 0 L 0) := by
  have hp : ENNReal.ofReal (Real.exp (-V (AffineSimplex.chart 0 L 0))) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have ht : ENNReal.ofReal (Real.exp (-V (AffineSimplex.chart 0 L 0))) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  refine ⟨by rw [AffineSimplex.simplexVolume_zero hL, lintegral_dirac]; exact hp,
    by rw [AffineSimplex.simplexVolume_zero hL, lintegral_dirac]; exact ht, ?_⟩
  rw [AffineFibre.normalizedMeasure_eq_smul, AffineSimplex.simplexVolume_zero hL,
    lintegral_dirac, dirac_withDensity, smul_smul, ENNReal.inv_mul_cancel hp ht,
    one_smul]

/-- Centered covariances in the one-gap branch of Appendix A vanish for all observables. -/
theorem one_gap_covariance (L : ℝ) (G H : EuclideanSpace ℝ (Fin 1) → ℝ) :
    ProbabilityTheory.covariance G H (Measure.dirac (AffineSimplex.chart 0 L 0)) = 0 := by
  simp [ProbabilityTheory.covariance]

/-- The tangent solution in the one-gap branch of Appendix A is necessarily zero: its entire tangent space is zero. -/
theorem one_gap_tangent (u : AffineSimplex.Tangent 0) : u = 0 := by
  have : Subsingleton (AffineSimplex.Tangent 0) :=
    (Module.finrank_zero_iff (R := ℝ)).mp (AffineSimplex.finrank_tangent 0)
  exact Subsingleton.elim _ _

/-- The exponential of the fibre potential is the actual marginal fibre
mass, with positivity checked before taking its logarithm.
This is the density identification in Appendix A. -/
theorem marginal_fibre_density (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin ((n + 1) + m + 1)))
    {L : ℝ} (hL : L < ((n + 1 + m : ℕ) + 1 : ℝ))
    {z : AffineSimplex.Tangent n}
    (hz : z ∈ AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L) :
    ENNReal.ofReal (Real.exp (-(-Real.log (∫ y : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p (n + 1) m σ
        (AffineSimplex.centredChart n L z, y)).toReal)))) =
      AffineFibre.fibreMass volume (ProperMarginalChart.chartDensity p (n + 1) m σ)
        (AffineSimplex.centredChart n L z) := by
  have hx := fibre_subset_marginal n hL hz
  have hn := MarginalHessian.physical_marginal_normalizer p (n + 1) m (by omega) σ hx
  rw [neg_neg, Real.exp_log hn.2, hn.1]
  exact ENNReal.ofReal_toReal (ProperMarginalChart.fibre_mass p (n + 1) m (by omega) σ hx).2

/-- Smoothness and strict curvature of every allowed penalized marginal
survive fixed-length restriction, with the same penalty data.
These are the regularity and curvature clauses of Appendix A. -/
theorem penalized_marginal_fibre_regular (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin ((n + 1) + m + 1)))
    {L : ℝ} (hL : L < ((n + 1 + m : ℕ) + 1 : ℝ))
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (J : Finset (Fin (n + 1))) (b : Bool) :
    let Ω := AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L
    let V := fun z : AffineSimplex.Tangent n =>
      p.val.1 * ∑ i ∈ J, (θ.val (a * AffineSimplex.centredChart n L z i) +
        if b then θ.val (a * (AffineSimplex.centredChart n L z i)⁻¹) else 0) -
      Real.log (∫ y : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n + 1) m σ
          (AffineSimplex.centredChart n L z, y)).toReal)
    ContDiffOn ℝ ∞ V Ω ∧ ∃ κ : ℝ, 0 < κ ∧ ∀ z ∈ Ω,
      ∀ u : AffineSimplex.Tangent n,
        κ * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) z u u := by
  intro Ω V
  let W := fun t : EuclideanSpace ℝ (Fin (n + 1)) => p.val.1 * ∑ i ∈ J,
    (θ.val (a * t i) + if b then θ.val (a * (t i)⁻¹) else 0) -
      Real.log (∫ y : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n + 1) m σ (t,y)).toReal)
  have hWs : ContDiffOn ℝ ∞ W (AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1)) :=
    MarginalHessian.physical_penalized_marginal_potential_smooth p (n + 1) m
      (by omega) σ θ ha J b
  refine ⟨hWs.comp (centredChart_smooth n L).contDiffOn
    (fun z hz => fibre_subset_marginal n hL hz), ?_⟩
  obtain ⟨κ, hκ, hc⟩ := MarginalCollision.penalized_marginal_strict_curvature p
    (n + 1) m (by omega) σ θ ha J b
  refine ⟨κ, hκ, fun z hz u => ?_⟩
  have hx := fibre_subset_marginal n hL hz
  have hW2 := (hWs.contDiffAt ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds hx)).of_le
    (by norm_num : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  change κ * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (fun z =>
    W ((AffineSimplex.Tangent n).subtypeL z + AffineSimplex.centre n L))) z u u
  rw [AffineMetricTransport.hessian_comp_affine
    (AffineSimplex.Tangent n).subtypeL (AffineSimplex.centre n L) hW2]
  exact hc _ hx u.val

/-- Positive finite normalization for every allowed penalized marginal
at every interior fixed length, including the one-gap fibre. Appendix A. -/
theorem penalized_marginal_fibre_normalizer (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin ((n + 1) + m + 1)))
    {L : ℝ} (hL0 : 0 < L) (hL : L < ((n + 1 + m : ℕ) + 1 : ℝ))
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (J : Finset (Fin (n + 1))) (b : Bool) :
    let Ω := AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L
    let V := fun z : AffineSimplex.Tangent n =>
      p.val.1 * ∑ i ∈ J, (θ.val (a * AffineSimplex.centredChart n L z i) +
        if b then θ.val (a * (AffineSimplex.centredChart n L z i)⁻¹) else 0) -
      Real.log (∫ y : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n + 1) m σ
          (AffineSimplex.centredChart n L z, y)).toReal)
    0 < ∫⁻ z in Ω, ENNReal.ofReal (Real.exp (-V z)) ∧
      (∫⁻ z in Ω, ENNReal.ofReal (Real.exp (-V z))) < ⊤ := by
  intro Ω V
  obtain ⟨hs, κ, hκ, hcurv⟩ := penalized_marginal_fibre_regular p n m σ hL θ ha J b
  have hΩ := fibre_isOpen n L
  have hc : ConvexOn ℝ Ω V := by
    apply convexOn_of_tangent_hessian_nonneg (fibre_convex n L)
      (fun x hx => (hs.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp))
      (fun x hx => ((hs.contDiffAt (hΩ.mem_nhds hx)).fderiv_right (m := 1)
        (by simp)).differentiableAt (by simp))
    intro x hx y _ z _
    exact (mul_nonneg hκ.le (sq_nonneg ‖z - y‖)).trans (hcurv x hx (z - y))
  have hne : Ω.Nonempty := by
    refine ⟨0, ?_⟩
    change AffineSimplex.centredChart n L 0 ∈ AffineSimplex.massSimplex n L
    simpa only [AffineSimplex.centredChart, Submodule.coe_zero, zero_add] using
      AffineSimplex.centre_mem_simplex n hL0
  exact internal_convex_normalizer hΩ (fibre_isBounded n L) hne hc hs.continuousOn

/-- The same active penalty at both endpoints is smooth on every compatible
fixed-length fibre. Its scale is an arbitrary positive real number. -/
theorem fibre_penalty_smooth (n : ℕ) (L : ℝ)
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (J : Finset (Fin (n + 1))) (b : Bool) :
    ContDiffOn ℝ ∞ (fun z : AffineSimplex.Tangent n =>
      ∑ i ∈ J, (θ.val (a * AffineSimplex.centredChart n L z i) +
        if b then θ.val (a * (AffineSimplex.centredChart n L z i)⁻¹) else 0))
      (AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L) := by
  have hP := (MarginalCollision.active_penalty_smooth_convex (n + 1) (L + 1) θ ha J b).1
  exact hP.comp (centredChart_smooth n L).contDiffOn
    (fun z hz => fibre_subset_marginal n (by linarith : L < L + 1) hz)

/-- Compatible positive exteriors assemble with every active simplex point
into a full physical simplex. No typicality condition is used. -/
theorem assemble_fixed_exterior_mem (n m : ℕ)
    (σ : Equiv.Perm (Fin ((n + 1) + m + 1))) {L : ℝ}
    (y : EuclideanSpace ℝ (Fin (m + 1))) (hy : ∀ j, 0 < y j)
    (hcompat : L + ∑ j, y j = ((n + 1 + m : ℕ) + 1 : ℝ))
    {z : AffineSimplex.Tangent n}
    (hz : z ∈ AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L) :
    RetainedSimplex.assemble (n + 1) m σ (AffineSimplex.centredChart n L z) y ∈
      AffineSimplex.massSimplex ((n + 1) + m) ((n + 1 + m : ℕ) + 1) := by
  rw [RetainedSimplex.assemble, RetainedSimplex.reindex_mem_simplex]
  constructor
  · intro i
    exact Fin.addCases (m := n + 1) (n := m + 1) (fun j : Fin (n + 1) => by simpa only [RetainedSimplex.join_left] using hz.1 j)
      (fun j : Fin (m + 1) => by simpa only [RetainedSimplex.join_right] using hy j) i
  · change (∑ i : Fin ((n + 1) + (m + 1)),
      RetainedSimplex.join (n + 1) (m + 1) (AffineSimplex.centredChart n L z, y) i) = _
    rw [RetainedSimplex.sum_join (n + 1) (m + 1), AffineSimplex.sum_centredChart]
    exact hcompat

/-- Fixing exterior coordinates is a smooth affine operation in the
existing retained-coordinate chart, for every real active mass. -/
theorem assemble_fixed_exterior_smooth (n m : ℕ)
    (σ : Equiv.Perm (Fin ((n + 1) + m + 1))) (L : ℝ)
    (y : EuclideanSpace ℝ (Fin (m + 1))) :
    ContDiff ℝ ∞ (fun z : AffineSimplex.Tangent n =>
      RetainedSimplex.assemble (n + 1) m σ (AffineSimplex.centredChart n L z) y) := by
  have hG : ContDiff ℝ ∞ (fun z : AffineSimplex.Tangent n =>
      RetainedSimplex.join (n + 1) (m + 1) (AffineSimplex.centredChart n L z, y)) := by
    apply (contDiff_piLp 2).mpr
    intro i
    refine Fin.addCases (m := n + 1) (n := m + 1) (fun j => ?_) (fun j => ?_) i
    · simp only [RetainedSimplex.join_left]
      exact (EuclideanSpace.proj j).contDiff.comp (centredChart_smooth n L)
    · simp only [RetainedSimplex.join_right]
      exact contDiff_const
  exact (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ).contDiff.comp hG

/-- Fixed-exterior energies have smooth realizations agreeing with the
ambient extension on their entire physical fibre.
This is the smoothness clause of Appendix A. -/
theorem fixed_exterior_smooth (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin ((n + 1) + m + 1))) {L : ℝ}
    (y : EuclideanSpace ℝ (Fin (m + 1))) (hy : ∀ j, 0 < y j)
    (hcompat : L + ∑ j, y j = ((n + 1 + m : ℕ) + 1 : ℝ)) :
    ∃ K : AffineSimplex.Tangent n → ℝ,
      ContDiffOn ℝ ∞ K
        (AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L) ∧
      ∀ z (hz : z ∈ AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L),
        K z = physicalAmbientGapEnergy p (n + 1 + m).succPNat
          ⟨RetainedSimplex.assemble (n + 1) m σ (AffineSimplex.centredChart n L z) y,
            PhysicalEnergy.simplex_subset_ambient _ _
              (by
                have hh := assemble_fixed_exterior_mem n m σ y hy hcompat hz
                rw [AffineSimplex.massSimplex_physical] at hh
                exact hh)⟩ := by
  obtain ⟨W, hs, hv, _⟩ := PhysicalEnergy.ambient_derivatives p (n + 1 + m).succPNat
  let F := fun z : AffineSimplex.Tangent n =>
    RetainedSimplex.assemble (n + 1) m σ (AffineSimplex.centredChart n L z) y
  have hF : ContDiff ℝ ∞ F := assemble_fixed_exterior_smooth n m σ L y
  refine ⟨fun z => W (F z), hs.comp hF.contDiffOn (fun z hz =>
    PhysicalEnergy.simplex_subset_ambient _ _
      (by
                have hh := assemble_fixed_exterior_mem n m σ y hy hcompat hz
                rw [AffineSimplex.massSimplex_physical] at hh
                exact hh)), fun z hz => ?_⟩
  exact hv ⟨_, PhysicalEnergy.simplex_subset_ambient _ _
    (by
                have hh := assemble_fixed_exterior_mem n m σ y hy hcompat hz
                rw [AffineSimplex.massSimplex_physical] at hh
                exact hh)⟩

/-- The fixed-exterior physical energy has the common active
barrier `2∑xᵢ⁻ˢ`, independently of the fixed positive exterior.
This supplies the endpoint convex decomposition for Appendix A. -/
theorem fixed_exterior_barrier (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin ((n + 1) + m + 1))) {L : ℝ}
    (y : EuclideanSpace ℝ (Fin (m + 1))) (hy : ∀ j, 0 < y j)
    (hcompat : L + ∑ j, y j = ((n + 1 + m : ℕ) + 1 : ℝ)) :
    ∃ K : AffineSimplex.Tangent n → ℝ,
      ContDiffOn ℝ ∞ K
        (AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L) ∧
      (∀ z (hz : z ∈ AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L),
        K z = physicalAmbientGapEnergy p (n + 1 + m).succPNat
          ⟨RetainedSimplex.assemble (n + 1) m σ (AffineSimplex.centredChart n L z) y,
            PhysicalEnergy.simplex_subset_ambient _ _ (by
              have hh := assemble_fixed_exterior_mem n m σ y hy hcompat hz
              rw [AffineSimplex.massSimplex_physical] at hh
              exact hh)⟩) ∧
      ConvexOn ℝ (AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L)
        (fun z => K z - 2 * ∑ i, (AffineSimplex.centredChart n L z i) ^ (-p.val.2)) := by
  obtain ⟨W, hs, hv, hc⟩ := RemovableGapBarrier.nearest_gap_barrier_convex p
    (n + 1 + m).succPNat (by simp only [Nat.succPNat_coe]; omega)
  let T : AffineSimplex.Tangent n →ᵃ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    (AffineSimplex.Tangent n).subtype.toAffineMap +
      AffineMap.const ℝ _ (AffineSimplex.centre n L)
  let F : AffineSimplex.Tangent n →ᵃ[ℝ] EuclideanSpace ℝ (Fin ((n + 1) + m + 1)) :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ).toLinearEquiv.toLinearMap.toAffineMap.comp
      ((RetainedSimplex.join (n + 1) (m + 1)).toLinearMap.toAffineMap.comp
        (T.prod (AffineMap.const ℝ _ y)))
  have hF (z) : F z = RetainedSimplex.assemble (n + 1) m σ
      (AffineSimplex.centredChart n L z) y := rfl
  have hmem (z) (hz : z ∈ AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L) :
      WithLp.ofLp (F z) ∈ Riesz1.gapSimplex (n + 1 + m).succPNat := by
    have hh := assemble_fixed_exterior_mem n m σ y hy hcompat hz
    rw [AffineSimplex.massSimplex_physical] at hh
    exact hh
  have hsm := hs.comp (assemble_fixed_exterior_smooth n m σ L y).contDiffOn
    (fun z hz => PhysicalEnergy.simplex_subset_ambient _ _ (hmem z hz))
  refine ⟨fun z => W (F z), hsm, fun z hz => hv ⟨_,
    PhysicalEnergy.simplex_subset_ambient _ _ (hmem z hz)⟩, ?_⟩
  have hsum (z : AffineSimplex.Tangent n) :
      (∑ j, (F z j) ^ (-p.val.2)) =
        (∑ i, (AffineSimplex.centredChart n L z i) ^ (-p.val.2)) +
          ∑ j, (y j) ^ (-p.val.2) := by
    change (∑ j, (RetainedSimplex.join (n + 1) (m + 1)
      (AffineSimplex.centredChart n L z, y) (σ.symm j)) ^ (-p.val.2)) = _
    have he := σ.symm.sum_comp (fun j =>
      (RetainedSimplex.join (n + 1) (m + 1)
        (AffineSimplex.centredChart n L z, y) j) ^ (-p.val.2))
    rw [he]
    change (∑ i : Fin ((n + 1) + (m + 1)),
      (RetainedSimplex.join (n + 1) (m + 1) (AffineSimplex.centredChart n L z, y) i) ^
        (-p.val.2)) = _
    rw [Fin.sum_univ_add]
    simp only [RetainedSimplex.join_left, RetainedSimplex.join_right]
  have hr := ((hc.comp_affineMap F).subset (fun z hz => hmem z hz)
    (fibre_convex n L)).add_const (2 * ∑ j, (y j) ^ (-p.val.2))
  apply hr.congr
  intro z _
  change (W (F z) - 2 * ∑ j, (F z j) ^ (-p.val.2)) +
    2 * (∑ j, (y j) ^ (-p.val.2)) = _
  rw [hsum]
  ring

/-- Smoothness and convexity of the physical inverse-gap barrier on the
existing isometric simplex chart. -/
theorem fibre_barrier_smooth_convex (n : ℕ) (L : ℝ) {s : ℝ} (hs : 0 < s) :
    let Ω := AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L
    let B := fun z : AffineSimplex.Tangent n =>
      2 * ∑ i, (AffineSimplex.centredChart n L z i) ^ (-s)
    ContDiffOn ℝ ∞ B Ω ∧ ConvexOn ℝ Ω B := by
  intro Ω B
  let T : AffineSimplex.Tangent n →ᵃ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    (AffineSimplex.Tangent n).subtype.toAffineMap +
      AffineMap.const ℝ _ (AffineSimplex.centre n L)
  let ℓ : Fin (n + 1) → AffineSimplex.Tangent n →ᵃ[ℝ] ℝ := fun i =>
    (EuclideanSpace.proj i).toLinearMap.toAffineMap.comp T
  have hi (i : Fin (n + 1)) : ConvexOn ℝ Ω
      (fun z => (AffineSimplex.centredChart n L z i) ^ (-s)) :=
    ((Riesz1.convexOn_rpow_neg_Ioi hs).comp_affineMap (ℓ i)).subset
      (fun z hz => hz.1 i) (fibre_convex n L)
  constructor
  · change ContDiffOn ℝ ∞ (fun z : AffineSimplex.Tangent n =>
      2 * ∑ i, (AffineSimplex.centredChart n L z i) ^ (-s)) Ω
    apply contDiffOn_const.mul
    apply ContDiffOn.sum
    intro i _
    have hi : ContDiff ℝ ∞ (fun z : AffineSimplex.Tangent n =>
        AffineSimplex.centredChart n L z i) :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp (centredChart_smooth n L)
    exact hi.contDiffOn.rpow_const_of_ne
      (fun (z : AffineSimplex.Tangent n) (hz : z ∈ Ω) => (hz.1 i).ne')
  · refine ⟨fibre_convex n L, fun x hx y hy a b ha hb hab => ?_⟩
    change 2 * (∑ i, (AffineSimplex.centredChart n L (a • x + b • y) i) ^ (-s)) ≤ _
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hi i).2 hx hy ha hb hab)
    simp only [Finset.sum_add_distrib, smul_eq_mul, ← Finset.mul_sum] at hh
    dsimp only [B]
    simp only [smul_eq_mul]
    nlinarith only [hh]

/-- Internal strict-curvature estimate from a convex remainder after
subtracting the common active barrier. Its explicit constant is independent
of the remainder and hence of an interpolation parameter. -/
theorem internal_fibre_strict_curvature (n : ℕ) {L s c : ℝ}
    (_hL : 0 < L) (hs : 0 < s) (hc : 0 < c)
    {V : AffineSimplex.Tangent n → ℝ}
    (hVs : ContDiffOn ℝ ∞ V
      (AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L))
    (hRc : ConvexOn ℝ
      (AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L)
      (fun z => V z - c * ∑ i, (AffineSimplex.centredChart n L z i) ^ (-s))) :
    ∀ z ∈ AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L,
      ∀ u : AffineSimplex.Tangent n,
        (c * (s * (s + 1)) * L ^ (-s - 2)) * ‖u‖ ^ 2 ≤
          fderiv ℝ (fderiv ℝ V) z u u := by
  let Ω := AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L
  let T : AffineSimplex.Tangent n →ᵃ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    (AffineSimplex.Tangent n).subtype.toAffineMap +
      AffineMap.const ℝ _ (AffineSimplex.centre n L)
  let ℓ : Fin (n + 1) → AffineSimplex.Tangent n →ᵃ[ℝ] ℝ := fun i =>
    (EuclideanSpace.proj i).toLinearMap.toAffineMap.comp T
  let B := fun z : AffineSimplex.Tangent n => ∑ i, c * (ℓ i z) ^ (-s)
  let R := fun z => V z - B z
  have hBeq : B = fun z => c * ∑ i, (AffineSimplex.centredChart n L z i) ^ (-s) := by
    funext z
    rw [Finset.mul_sum]
    rfl
  have hBs : ContDiffOn ℝ ∞ B Ω := by
    apply ContDiffOn.sum
    intro i _
    apply contDiffOn_const.mul
    have hi : ContDiff ℝ ∞ (fun z : AffineSimplex.Tangent n =>
        AffineSimplex.centredChart n L z i) :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp (centredChart_smooth n L)
    exact hi.contDiffOn.rpow_const_of_ne
      (fun (z : AffineSimplex.Tangent n) (hz : z ∈ Ω) => (hz.1 i).ne')
  have hRs : ContDiffOn ℝ ∞ R Ω := hVs.sub hBs
  have hRc' : ConvexOn ℝ Ω R := by simpa only [R, hBeq] using hRc
  intro z hz u
  have hB2 := (hBs.contDiffAt ((fibre_isOpen n L).mem_nhds hz)).of_le
    (by norm_num : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  have hR2 := (hRs.contDiffAt ((fibre_isOpen n L).mem_nhds hz)).of_le
    (by norm_num : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  have hRn := Riesz1.fderiv_fderiv_nonneg_of_convexOn (fibre_isOpen n L)
    (fibre_convex n L) hRc' (hRs.of_le (by norm_num)) hz u
  have he : V = fun w => B w + R w := by funext w; dsimp only [R]; ring
  have hh := MarginalCollision.internal_barrier_hessian ℓ (fun _ => c) s
    (fun i => hz.1 i) u u
  change fderiv ℝ (fderiv ℝ B) z u u = _ at hh
  rw [he, PhysicalCollision.internal_hessian_add hB2 hR2 u u, hh]
  have hcoef : 0 ≤ c * (s * (s + 1)) := by positivity
  have hsum : (c * (s * (s + 1)) * L ^ (-s - 2)) * ‖u‖ ^ 2 ≤
      ∑ i, c * (s * (s + 1)) * (ℓ i z) ^ (-s - 2) *
        ((ℓ i).linear u * (ℓ i).linear u) := by
    change (c * (s * (s + 1)) * L ^ (-s - 2)) * ‖u.val‖ ^ 2 ≤ _
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hi : AffineSimplex.centredChart n L z i ≤ L := by
      calc
        _ ≤ ∑ j, AffineSimplex.centredChart n L z j :=
          Finset.single_le_sum (fun j _ => (hz.1 j).le) (Finset.mem_univ i)
        _ = L := AffineSimplex.sum_centredChart n L z
    have hp := Real.rpow_le_rpow_of_nonpos (hz.1 i) hi (by linarith : -s - 2 ≤ 0)
    have hlin : (ℓ i).linear u = u.val i := by simp [ℓ, T]
    rw [hlin]
    change (c * (s * (s + 1)) * L ^ (-s - 2)) * (u.val i) ^ 2 ≤
      c * (s * (s + 1)) * (AffineSimplex.centredChart n L z i) ^ (-s - 2) *
        (u.val i * u.val i)
    rw [← pow_two]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hcoef) (sq_nonneg _)
  linarith only [hsum, hRn]

/-- Shared-penalty compatible interpolants: exact endpoint energies,
smoothness, strict curvature uniform in `t`, a common active barrier, and
positive finite normalization for all `0 ≤ t ≤ 1`. These are clauses of Appendix A. -/
theorem compatible_interpolation_regular (p : Parameters) (n m r : ℕ)
    (σ : Equiv.Perm (Fin ((n + 1) + m + 1)))
    (τ : Equiv.Perm (Fin ((n + 1) + r + 1))) {L : ℝ} (hL : 0 < L)
    (y : EuclideanSpace ℝ (Fin (m + 1))) (hy : ∀ j, 0 < y j)
    (z : EuclideanSpace ℝ (Fin (r + 1))) (hz : ∀ j, 0 < z j)
    (hcompatY : L + ∑ j, y j = ((n + 1 + m : ℕ) + 1 : ℝ))
    (hcompatZ : L + ∑ j, z j = ((n + 1 + r : ℕ) + 1 : ℝ))
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (J : Finset (Fin (n + 1))) (b : Bool) :
    let Ω := AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L
    let P := fun w : AffineSimplex.Tangent n => ∑ i ∈ J,
      (θ.val (a * AffineSimplex.centredChart n L w i) +
        if b then θ.val (a * (AffineSimplex.centredChart n L w i)⁻¹) else 0)
    ∃ Ky Kz : AffineSimplex.Tangent n → ℝ,
      (∀ w (hw : w ∈ Ω), Ky w = physicalAmbientGapEnergy p (n + 1 + m).succPNat
        ⟨RetainedSimplex.assemble (n + 1) m σ (AffineSimplex.centredChart n L w) y,
          PhysicalEnergy.simplex_subset_ambient _ _ (by
            have hh := assemble_fixed_exterior_mem n m σ y hy hcompatY hw
            rw [AffineSimplex.massSimplex_physical] at hh
            exact hh)⟩) ∧
      (∀ w (hw : w ∈ Ω), Kz w = physicalAmbientGapEnergy p (n + 1 + r).succPNat
        ⟨RetainedSimplex.assemble (n + 1) r τ (AffineSimplex.centredChart n L w) z,
          PhysicalEnergy.simplex_subset_ambient _ _ (by
            have hh := assemble_fixed_exterior_mem n r τ z hz hcompatZ hw
            rw [AffineSimplex.massSimplex_physical] at hh
            exact hh)⟩) ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        let V := fun w => p.val.1 * (P w + (1 - t) * Ky w + t * Kz w)
        ContDiffOn ℝ ∞ V Ω ∧
        (∀ w ∈ Ω, ∀ u : AffineSimplex.Tangent n,
          (2 * p.val.1 * (p.val.2 * (p.val.2 + 1)) * L ^ (-p.val.2 - 2)) * ‖u‖ ^ 2 ≤
            fderiv ℝ (fderiv ℝ V) w u u) ∧
        ConvexOn ℝ Ω (fun w => V w - 2 * p.val.1 *
          ∑ i, (AffineSimplex.centredChart n L w i) ^ (-p.val.2)) ∧
        (0 < ∫⁻ w in Ω, ENNReal.ofReal (Real.exp (-V w))) ∧
          (∫⁻ w in Ω, ENNReal.ofReal (Real.exp (-V w))) < ⊤ := by
  intro Ω P
  obtain ⟨Ky, hKys, hKy, hKyc⟩ := fixed_exterior_barrier p n m σ y hy hcompatY
  obtain ⟨Kz, hKzs, hKz, hKzc⟩ := fixed_exterior_barrier p n r τ z hz hcompatZ
  have hPs := fibre_penalty_smooth n L θ ha J b
  have hPc := convexOn_fibre_pullback n (show L < L + 1 by linarith)
    (MarginalCollision.active_penalty_smooth_convex (n + 1) (L + 1) θ ha J b).2
  obtain ⟨hBs, hBc⟩ := fibre_barrier_smooth_convex n L p.property.2.1
  refine ⟨Ky, Kz, hKy, hKz, fun t ht => ?_⟩
  intro V
  have hVs : ContDiffOn ℝ ∞ V Ω := contDiffOn_const.mul
    ((hPs.add (contDiffOn_const.mul hKys)).add (contDiffOn_const.mul hKzs))
  have hRc := (hPc.add ((hKyc.smul (by linarith only [ht.2] : 0 ≤ 1 - t)).add
    (hKzc.smul ht.1))).smul p.property.1.le
  have hVc : ConvexOn ℝ Ω (fun w => V w - 2 * p.val.1 *
      ∑ i, (AffineSimplex.centredChart n L w i) ^ (-p.val.2)) := by
    apply hRc.congr
    intro w _
    dsimp only [V, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hVconvex : ConvexOn ℝ Ω V := by
    apply (hVc.add (hBc.smul p.property.1.le)).congr
    intro w _
    dsimp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hne : Ω.Nonempty := by
    refine ⟨0, ?_⟩
    change AffineSimplex.centredChart n L 0 ∈ AffineSimplex.massSimplex n L
    simpa only [AffineSimplex.centredChart, Submodule.coe_zero, zero_add] using
      AffineSimplex.centre_mem_simplex n hL
  have hcurv := internal_fibre_strict_curvature n hL p.property.2.1
    (mul_pos (by norm_num : (0 : ℝ) < 2) p.property.1) hVs hVc
  exact ⟨hVs, hcurv, hVc, internal_convex_normalizer (fibre_isOpen n L)
    (fibre_isBounded n L) hne hVconvex hVs.continuousOn⟩

/-- Every interior fixed-length marginal has positive finite mass with
respect to the actual Hausdorff simplex volume. The factor-one isometric
chart identifies this with the preceding tangent-space normalization. Appendix A. -/
theorem marginal_simplex_normalizer (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin ((n + 1) + m + 1)))
    {L : ℝ} (hL0 : 0 < L) (hL : L < ((n + 1 + m : ℕ) + 1 : ℝ)) :
    let w := AffineFibre.fibreMass volume (ProperMarginalChart.chartDensity p (n + 1) m σ)
    0 < ∫⁻ x, w x ∂AffineSimplex.simplexVolume n L ∧
      (∫⁻ x, w x ∂AffineSimplex.simplexVolume n L) < ⊤ := by
  intro w
  have he : (∫⁻ x, w x ∂AffineSimplex.simplexVolume n L) =
      ∫⁻ z in AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L,
        ENNReal.ofReal (Real.exp (-(-Real.log (∫ y : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity p (n + 1) m σ
            (AffineSimplex.centredChart n L z, y)).toReal)))) := by
    rw [AffineSimplex.lintegral_centredChart]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (fibre_isOpen n L).measurableSet] with z hz
    exact (marginal_fibre_density p n m σ hL hz).symm
  rw [he]
  exact marginal_fibre_normalizer p n m σ hL0 hL

/-- Explicit disintegration of the physical marginal density by active
length. Every interior length uses its positive finite Hausdorff-volume
normalization, rather than an almost-everywhere choice of a conditional.
This is the coarea-density clause of Appendix A. -/
theorem marginal_length_disintegration (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin ((n + 1) + m + 1))) :
    let I := Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)
    let w := AffineFibre.fibreMass volume (ProperMarginalChart.chartDensity p (n + 1) m σ)
    ∃ (h0 : ∀ L : I, (∫⁻ x, w x ∂AffineSimplex.simplexVolume n L.val) ≠ 0)
      (ht : ∀ L : I, (∫⁻ x, w x ∂AffineSimplex.simplexVolume n L.val) ≠ ⊤),
      ∀ f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞, Measurable f →
        ∫⁻ x in {x | (∑ i, x i) ∈ I} ∩ {x | ∀ i, 0 < x i}, w x * f x =
          (ENNReal.ofReal (Real.sqrt (n + 1)))⁻¹ *
            ∫⁻ L : I, (∫⁻ x, w x ∂AffineSimplex.simplexVolume n L.val) *
              (∫⁻ x, f x ∂AffineFibre.normalizedMeasure
                (AffineSimplex.simplexVolume n L.val) w (h0 L) (ht L))
              ∂(volume.comap ((↑) : I → ℝ)) := by
  intro I w
  have hmass (L : I) := marginal_simplex_normalizer p n m σ L.property.1 L.property.2
  let h0 := fun L : I => (hmass L).1.ne'
  let ht := fun L : I => (hmass L).2.ne
  refine ⟨h0, ht, fun f hf => ?_⟩
  exact AffineFibre.SumChart.lintegral_simplex_disintegration n measurableSet_Ioo
    (AffineFibre.measurable_fibreMass volume (ProperMarginalChart.measurable_chartDensity p (n + 1) m σ))
    h0 ht hf

end Riesz2.ConditionalWellPosedness
