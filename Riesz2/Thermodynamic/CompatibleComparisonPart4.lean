/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.CompatibleComparisonPart2
public import Riesz2.ToMathlib.ProperSimplexProjection
public import Riesz2.ToMathlib.ConvexInwardMollification
public import Riesz2.Frozen.DependsOnBlockCoordinates

/-!
# Lipschitz approximation for compatible conditional comparison

Inward mollification preserves the good-set derivative norm on the same event and every
supported coordinate. Expectation convergence holds on each normalized Hausdorff
fixed-length law. This gives the passage from smooth to Lipschitz observables in the
proof of Proposition 6.6.
-/

public section
noncomputable section

open MeasureTheory Set Filter Metric
open scoped ContDiff Topology NNReal ENNReal BigOperators

namespace Riesz2.CompatibleComparison

/-- See Lemma 6.5 and the proof of Proposition 6.6 of the paper: inward convolution
preserves both derivative sums and the given coordinate support.
The error estimate is uniform on bounded sets, including each length simplex. -/
theorem exists_restricted_smooth_approximation_internal {n : ℕ+}
    (G : BlockObservable n) (J : Finset (Fin (n : ℕ)))
    (hJ : DependsOnBlockCoordinates G J)
    (A : Set (Fin (n : ℕ) → ℝ)) (hA : Convex ℝ A)
    (c : Fin (n : ℕ) → ℝ) (hc : c ∈ interior A) :
    ∃ (φ : ℕ → BlockObservable n) (C : ℝ≥0) (r : ℝ), 0 < r ∧
      (∀ k, ContDiff ℝ ∞ (φ k).val) ∧
      (∀ k, DependsOnBlockCoordinates (φ k) J) ∧
      (∀ k S, restrictedBlockDerivativeNorm (φ k) S A ≤ restrictedBlockDerivativeNorm G S A) ∧
      (∀ k, blockDerivativeNorm (φ k) ≤ blockDerivativeNorm G) ∧
      (∀ k x, |(φ k).val x-G.val x| ≤ (C : ℝ)/(k+1)*(r+‖c-x‖)) ∧
      (∀ x, Tendsto (fun k => (φ k).val x) atTop (𝓝 (G.val x))) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hc)
  obtain ⟨C, hG⟩ := G.property
  let t : ℕ → ℝ := fun k => 1/(k+1)
  have ht k : 0 < t k := by dsimp [t]; positivity
  have ht1 k : t k ≤ 1 := by
    dsimp [t]
    exact (div_le_one (by positivity)).mpr (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
  let b (k : ℕ) : ContDiffBump (0 : Fin (n : ℕ) → ℝ) :=
    { rIn := t k*r/2
      rOut := t k*r
      rIn_pos := half_pos (mul_pos (ht k) hr)
      rIn_lt_rOut := half_lt_self (mul_pos (ht k) hr) }
  let φ : ℕ → BlockObservable n := fun k =>
    ⟨ConvexInwardMollification.mollify G.val hG.continuous.locallyIntegrable c (t k) (b k),
      ⟨C, ConvexInwardMollification.lipschitzWith hG c (ht k).le (ht1 k) (b k)⟩⟩
  have hrestricted k j :
      (sInf {D : ℝ≥0 | ∀ x u, x ∈ A → Function.update x j u ∈ A →
        |(φ k).val (Function.update x j u)-(φ k).val x| ≤ (D : ℝ)*|u-x j|} : ℝ≥0) ≤
      sInf {D : ℝ≥0 | ∀ x u, x ∈ A → Function.update x j u ∈ A →
        |G.val (Function.update x j u)-G.val x| ≤ (D : ℝ)*|u-x j|} := by
    apply csInf_le (OrderBot.bddBelow _)
    intro x u hx hu
    exact ConvexInwardMollification.coordinate_bound hG hA hball (ht k) (ht1 k)
      (b k) le_rfl j (NNReal.coe_nonneg _) (restricted_coordinate_bound_internal G A j) x u hx hu
  have hglobal k j : coordinateDerivativeNorm (φ k) j ≤ coordinateDerivativeNorm G j := by
    apply csInf_le (OrderBot.bddBelow _)
    intro x u
    exact ConvexInwardMollification.coordinate_bound hG (convex_univ : Convex ℝ univ)
      (subset_univ (ball c r)) (ht k) (ht1 k) (b k) le_rfl j
      (coordinateDerivativeNorm G j).coe_nonneg
      (fun x u _ _ => InterpolatingDensities.coordinate_bound G j x u) x u (mem_univ _) (mem_univ _)
  have he k x : |(φ k).val x-G.val x| ≤ (C : ℝ)/(k+1)*(r+‖c-x‖) := by
    have hh := ConvexInwardMollification.error_bound hG c (ht k).le (b k) x
    exact hh.trans_eq (by dsimp [b, t]; ring)
  refine ⟨φ, C, r, hr, fun k => ConvexInwardMollification.contDiff hG c (t k) (b k),
    fun k => ConvexInwardMollification.dependsOn hG.continuous.locallyIntegrable c (t k) (b k) (J : Set (Fin (n : ℕ))) hJ,
    ?_, ?_, he, ?_⟩
  · intro k S
    exact Finset.sum_le_sum fun j _ => NNReal.coe_le_coe.mpr (hrestricted k j)
  · intro k
    exact Finset.sum_le_sum fun j _ => NNReal.coe_le_coe.mpr (hglobal k j)
  · intro x
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun k => (he k x))
    have hh : Tendsto (fun k : ℕ => (1 : ℝ)/(k+1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa [div_eq_mul_inv] using (hh.const_mul (C : ℝ)).mul_const (r+‖c-x‖)

/-- See the proof of Proposition 6.6 in the paper: the approximation preserves the
restricted norm on the same fine event, including its boundary. -/
theorem fine_restricted_smooth_approximation (s η : ℝ) (hη : 0 < η) (n N : ℕ+)
    (hn : 2 ≤ (n : ℕ)) (hN : (n : ℕ) < (N : ℕ))
    (G : BlockObservable n) (J : Finset (Fin (n : ℕ))) (hJ : DependsOnBlockCoordinates G J) :
    ∃ (φ : ℕ → BlockObservable n) (C : ℝ≥0) (r : ℝ), 0 < r ∧
      (∀ k, ContDiff ℝ ∞ (φ k).val) ∧
      (∀ k, DependsOnBlockCoordinates (φ k) J) ∧
      (∀ k S, restrictedBlockDerivativeNorm (φ k) S (goodBlockEvent s n N η) ≤
        restrictedBlockDerivativeNorm G S (goodBlockEvent s n N η)) ∧
      (∀ k, blockDerivativeNorm (φ k) ≤ blockDerivativeNorm G) ∧
      (∀ k x, |(φ k).val x-G.val x| ≤ (C : ℝ)/(k+1)*(r+‖(fun _ => 1)-x‖)) ∧
      (∀ x, Tendsto (fun k => (φ k).val x) atTop (𝓝 (G.val x))) :=
  exists_restricted_smooth_approximation_internal G J hJ _
    (InterpolantLocalLaws.convex_goodBlockEvent s n N η) _
    (one_mem_interior_fine_event s η hη n N hn hN)

/-- See the proof of Proposition 6.6 in the paper: every block observable is integrable
on every finite law on the literal positive length simplex. -/
theorem simplex_integrable_internal (n : ℕ) {L : ℝ} (hL : 0 < L)
    (G : BlockObservable n.succPNat) (μ : Measure (AffineSimplex.massSimplex n L))
    [IsFiniteMeasure μ] :
    Integrable (fun x => G.val (WithLp.ofLp x.val)) μ := by
  obtain ⟨C, hG⟩ := G.property
  have hc : Continuous (fun x : AffineSimplex.massSimplex n L =>
      G.val (WithLp.ofLp x.val)) := hG.continuous.comp (by fun_prop)
  apply Integrable.of_bound hc.aestronglyMeasurable (|G.val 0|+blockDerivativeNorm G*L)
  exact Eventually.of_forall fun x => block_bound_on_simplex n hL G x.val x.property

/-- See the proof of Proposition 6.6 in the paper: pointwise approximation with bounded
coordinate norms and a bounded value at zero passes to expectations on each
fixed-length law. No derivative is evaluated on a null hyperplane. -/
theorem simplex_integral_tendsto_internal (n : ℕ) {L : ℝ} (hL : 0 < L)
    (G : BlockObservable n.succPNat) (φ : ℕ → BlockObservable n.succPNat)
    (μ : Measure (AffineSimplex.massSimplex n L)) [IsFiniteMeasure μ]
    (B : ℝ) (hB : ∀ k, |(φ k).val 0| ≤ B)
    (hD : ∀ k, blockDerivativeNorm (φ k) ≤ blockDerivativeNorm G)
    (hp : ∀ x, Tendsto (fun k => (φ k).val x) atTop (𝓝 (G.val x))) :
    Tendsto (fun k => ∫ x, (φ k).val (WithLp.ofLp x.val) ∂μ) atTop
      (𝓝 (∫ x, G.val (WithLp.ofLp x.val) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => B+blockDerivativeNorm G*L)
  · intro k
    exact (simplex_integrable_internal n hL (φ k) μ).aestronglyMeasurable
  · exact integrable_const _
  · intro k
    exact Eventually.of_forall fun x => (block_bound_on_simplex n hL (φ k) x.val x.property).trans
      (add_le_add (hB k) (mul_le_mul_of_nonneg_right (hD k) hL.le))
  · exact Eventually.of_forall fun x => hp _

/-- See Subsection 6.1, Lemma 6.5 and the proof of Proposition 6.6 of the paper:
a single smooth supported sequence preserves both derivative norms on
the same fine event and converges in expectation on every literal normalized
Hausdorff fixed-length law. Normalization arguments exclude junk integrals. -/
theorem normalized_restricted_smooth_approximation (s η : ℝ) (hη : 0 < η)
    (n : ℕ) (N : ℕ+) (hn : 2 ≤ n+1) (hN : n+1 < (N : ℕ))
    (G : BlockObservable n.succPNat) (J : Finset (Fin (n+1)))
    (hJ : DependsOnBlockCoordinates G J) :
    ∃ φ : ℕ → BlockObservable n.succPNat,
      (∀ k, ContDiff ℝ ∞ (φ k).val) ∧
      (∀ k, DependsOnBlockCoordinates (φ k) J) ∧
      (∀ k S, restrictedBlockDerivativeNorm (φ k) S (goodBlockEvent s n.succPNat N η) ≤
        restrictedBlockDerivativeNorm G S (goodBlockEvent s n.succPNat N η)) ∧
      (∀ k, blockDerivativeNorm (φ k) ≤ blockDerivativeNorm G) ∧
      (∀ x, Tendsto (fun k => (φ k).val x) atTop (𝓝 (G.val x))) ∧
      ∀ (L : ℝ), 0 < L → ∀ (w : AffineSimplex.massSimplex n L → ℝ≥0∞), Measurable w →
      ∀ (h0 : (∫⁻ x, w x ∂(AffineSimplex.simplexVolume n L).comap Subtype.val) ≠ 0)
        (ht : (∫⁻ x, w x ∂(AffineSimplex.simplexVolume n L).comap Subtype.val) ≠ ⊤),
      let μ := AffineFibre.normalizedMeasure
        ((AffineSimplex.simplexVolume n L).comap Subtype.val) w h0 ht
      (∀ k, Integrable (fun x => (φ k).val (WithLp.ofLp x.val)) μ) ∧
      Integrable (fun x => G.val (WithLp.ofLp x.val)) μ ∧
      Tendsto (fun k => ∫ x, (φ k).val (WithLp.ofLp x.val) ∂μ) atTop
        (𝓝 (∫ x, G.val (WithLp.ofLp x.val) ∂μ)) := by
  obtain ⟨φ, C, r, hr, hs, hj, ha, hd, he, hp⟩ :=
    fine_restricted_smooth_approximation s η hη n.succPNat N hn hN G J hJ
  refine ⟨φ, hs, hj, ha, hd, hp, ?_⟩
  intro L hL w hw h0 ht
  let μ := AffineFibre.normalizedMeasure
    ((AffineSimplex.simplexVolume n L).comap Subtype.val) w h0 ht
  have : IsProbabilityMeasure μ := AffineFibre.isProbabilityMeasure_normalizedMeasure _ hw h0 ht
  refine ⟨fun k => simplex_integrable_internal n hL (φ k) μ,
    simplex_integrable_internal n hL G μ, ?_⟩
  apply simplex_integral_tendsto_internal n hL G φ μ
    (|G.val 0|+(C : ℝ)*(r+‖(fun _ : Fin (n+1) => (1 : ℝ))‖)) _ hd hp
  intro k
  have hh := he k 0
  simp only [sub_zero] at hh
  have hdiv : (C : ℝ)/(k+1) ≤ C := div_le_self C.coe_nonneg (by
    have := Nat.cast_nonneg (α := ℝ) k
    linarith)
  have hmul := mul_le_mul_of_nonneg_right hdiv
    (add_nonneg hr.le (norm_nonneg (fun _ : Fin (n+1) => (1 : ℝ))))
  calc
    |(φ k).val 0| ≤ |(φ k).val 0-G.val 0|+|G.val 0| := by
      simpa only [sub_add_cancel] using abs_add_le ((φ k).val 0-G.val 0) (G.val 0)
    _ ≤ _ := by linarith [hh.trans hmul]

/-- See the proof of Proposition 6.6 in the paper, internal smooth-to-Lipschitz passage
on the same two literal normalized fixed-length laws. The smooth hypothesis is
exactly the displayed comparison conclusion, with the same good-set norm,
global norm, coefficient, exponent and exponential remainder. The constants and their quantifier order are preserved. -/
theorem lipschitz_comparison_of_smooth_internal (s η : ℝ) (hη : 0 < η)
    (n : ℕ) (N : ℕ+) (hn : 2 ≤ n+1) (hN : n+1 < (N : ℕ))
    (L : ℝ) (hL : 0 < L) (J : Finset (Fin (n+1)))
    (w z : AffineSimplex.massSimplex n L → ℝ≥0∞) (hw : Measurable w) (hz : Measurable z)
    (hw0 : (∫⁻ x, w x ∂(AffineSimplex.simplexVolume n L).comap Subtype.val) ≠ 0)
    (hwt : (∫⁻ x, w x ∂(AffineSimplex.simplexVolume n L).comap Subtype.val) ≠ ⊤)
    (hz0 : (∫⁻ x, z x ∂(AffineSimplex.simplexVolume n L).comap Subtype.val) ≠ 0)
    (hzt : (∫⁻ x, z x ∂(AffineSimplex.simplexVolume n L).comap Subtype.val) ≠ ⊤)
    (C c κ ε δ : ℝ) (hC : 0 ≤ C) :
    let μ := AffineFibre.normalizedMeasure
      ((AffineSimplex.simplexVolume n L).comap Subtype.val) w hw0 hwt
    let ν := AffineFibre.normalizedMeasure
      ((AffineSimplex.simplexVolume n L).comap Subtype.val) z hz0 hzt
    (∀ G : BlockObservable n.succPNat, ContDiff ℝ ∞ G.val → DependsOnBlockCoordinates G J →
      |(∫ x, G.val (WithLp.ofLp x.val) ∂μ)-(∫ x, G.val (WithLp.ofLp x.val) ∂ν)| ≤
        C*((n+1 : ℕ) : ℝ)^(κ*ε-min s 1/2)*
          (restrictedBlockDerivativeNorm G J (goodBlockEvent s n.succPNat N η)+
            Real.exp (-c*((n+1 : ℕ) : ℝ)^δ)*blockDerivativeNorm G)) →
    ∀ G : BlockObservable n.succPNat, DependsOnBlockCoordinates G J →
      Integrable (fun x => G.val (WithLp.ofLp x.val)) μ ∧
      Integrable (fun x => G.val (WithLp.ofLp x.val)) ν ∧
      |(∫ x, G.val (WithLp.ofLp x.val) ∂μ)-(∫ x, G.val (WithLp.ofLp x.val) ∂ν)| ≤
        C*((n+1 : ℕ) : ℝ)^(κ*ε-min s 1/2)*
          (restrictedBlockDerivativeNorm G J (goodBlockEvent s n.succPNat N η)+
            Real.exp (-c*((n+1 : ℕ) : ℝ)^δ)*blockDerivativeNorm G) := by
  dsimp only
  intro hSmooth G hJ
  obtain ⟨φ, hs, hj, ha, hd, _, hconv⟩ :=
    normalized_restricted_smooth_approximation s η hη n N hn hN G J hJ
  obtain ⟨_, hiμ, htμ⟩ := hconv L hL w hw hw0 hwt
  obtain ⟨_, hiν, htν⟩ := hconv L hL z hz hz0 hzt
  refine ⟨hiμ, hiν, ?_⟩
  apply le_of_tendsto (htμ.sub htν).abs
  apply Eventually.of_forall
  intro k
  refine (hSmooth (φ k) (hs k) (hj k)).trans ?_
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (Real.rpow_nonneg (by positivity) _))
  exact add_le_add (ha k J) (mul_le_mul_of_nonneg_left (hd k) (Real.exp_pos _).le)

end Riesz2.CompatibleComparison
