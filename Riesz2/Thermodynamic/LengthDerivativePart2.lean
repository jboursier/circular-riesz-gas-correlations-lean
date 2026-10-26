/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.LengthDerivative
public import Riesz2.Thermodynamic.LengthAveragingFibresPart2
public import Riesz2.Thermodynamic.LengthAveragingFibresPart3
public import Riesz2.ToMathlib.KernelSquareNorm

/-!
# Length derivatives: fixed-chart normalization and integrated errors

Steps in the proof of Lemma 6.5. The physical observable is identified with its
normalized integral on the fixed zero-sum tangent space. Conditional source norms and
extended exceptional errors are integrated against the coarea length law. The multiplier
implication assumes physical differentiation and the marginal-fibre covariance
representation.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace Riesz2.LengthDerivative

open LengthAveragingFibres AffineSimplex

variable (p : Parameters) (n m : ℕ) (θ : PhysicalCutoff) (ε : ℝ)

/-- See the proof of Lemma 6.5 in the paper: the actual zero-extended
marginal density has the same mass on the moving simplex and on the fixed
zero-sum tangent space. The centered chart has Jacobian one. -/
theorem centred_mass (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) :
    (∫⁻ z : Tangent n, marginalWeight p n m θ ε (centredChart n L.val z)) =
      ∫⁻ x, marginalWeight p n m θ ε x ∂simplexVolume n L.val := by
  classical
  let Ω := centredChart n L.val ⁻¹' massSimplex n L.val
  have hΩ : MeasurableSet Ω := (ConditionalWellPosedness.fibre_isOpen n L.val).measurableSet
  rw [lintegral_centredChart, ← lintegral_indicator hΩ]
  apply lintegral_congr
  intro z
  by_cases hz : z ∈ Ω
  · exact (indicator_of_mem hz
      (fun z : Tangent n => marginalWeight p n m θ ε (centredChart n L.val z))).symm
  · rw [indicator_of_notMem hz]
    apply marginalWeight_eq_zero
    intro hx
    exact hz ⟨hx.1, sum_centredChart n L.val z⟩

/-- See Lemma 6.5 of the paper: the fixed-chart physical normalizer is positive
and finite at every interior length, including dimension zero. -/
theorem centred_mass_valid (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) :
    (∫⁻ z : Tangent n, marginalWeight p n m θ ε (centredChart n L.val z)) ≠ 0 ∧
      (∫⁻ z : Tangent n, marginalWeight p n m θ ε (centredChart n L.val z)) ≠ ⊤ := by
  rw [centred_mass]
  exact fibre_mass p n m θ ε L

/-- See the proof of Lemma 6.5 in the paper: the fixed-coordinate
normalized law maps to the existing physical fibre kernel. The density
already vanishes off the positive fibre, so the reference measure is fixed
volume on the whole tangent space. -/
theorem fibreKernel_eq_centred_map
    (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) :
    fibreKernel p n m θ ε L =
      (AffineFibre.normalizedMeasure (volume : Measure (Tangent n))
        (fun z => marginalWeight p n m θ ε (centredChart n L.val z))
        (centred_mass_valid p n m θ ε L).1
        (centred_mass_valid p n m θ ε L).2).map (centredChart n L.val) := by
  classical
  let Ω := centredChart n L.val ⁻¹' massSimplex n L.val
  let w := fun z : Tangent n => marginalWeight p n m θ ε (centredChart n L.val z)
  have hΩ : MeasurableSet Ω := (ConditionalWellPosedness.fibre_isOpen n L.val).measurableSet
  have hzero : Ω.indicator w = w := by
    funext z
    by_cases hz : z ∈ Ω
    · exact indicator_of_mem hz _
    · rw [indicator_of_notMem hz]
      symm
      apply marginalWeight_eq_zero
      intro hx
      exact hz ⟨hx.1, sum_centredChart n L.val z⟩
  have hmass : (∫⁻ z in Ω, w z) = ∫⁻ z, w z := by
    rw [← lintegral_indicator hΩ, hzero]
  have h0 : (∫⁻ z in Ω, w z) ≠ 0 :=
    hmass ▸ (centred_mass_valid p n m θ ε L).1
  have ht : (∫⁻ z in Ω, w z) ≠ ⊤ :=
    hmass ▸ (centred_mass_valid p n m θ ε L).2
  have hmap := AffineFibre.normalizedMeasure_map (volume.restrict Ω)
    (isometry_centredChart n L.val).isClosedEmbedding.measurableEmbedding
    (measurable_marginalWeight p n m θ ε) h0 ht
  have he : AffineFibre.normalizedMeasure (volume.restrict Ω) w h0 ht =
      AffineFibre.normalizedMeasure volume w
        (centred_mass_valid p n m θ ε L).1 (centred_mass_valid p n m θ ε L).2 := by
    rw [AffineFibre.normalizedMeasure_eq_smul, AffineFibre.normalizedMeasure_eq_smul,
      hmass, ← withDensity_indicator hΩ, hzero]
  change AffineFibre.normalizedMeasure (simplexVolume n L.val)
    (marginalWeight p n m θ ε) _ _ = _
  simpa only [Ω, ← simplexVolume_eq_centredChart_map] using
    hmap.trans (congrArg (fun ν => ν.map (centredChart n L.val)) he)

/-- See Lemma 6.5 of the paper: the real fixed-chart normalizer is integrable
and strictly positive. Its extended integral is finite before taking real
values, and the equality holds at every interior length. -/
theorem centred_real_mass (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) :
    Integrable (fun z : Tangent n =>
      (marginalWeight p n m θ ε (centredChart n L.val z)).toReal) volume ∧
    0 < ∫ z : Tangent n,
      (marginalWeight p n m θ ε (centredChart n L.val z)).toReal := by
  have hm : Measurable (fun z : Tangent n =>
      marginalWeight p n m θ ε (centredChart n L.val z)) :=
    (measurable_marginalWeight p n m θ ε).comp
    (isometry_centredChart n L.val).continuous.measurable
  have hfinite := ae_lt_top hm (centred_mass_valid p n m θ ε L).2
  refine ⟨integrable_toReal_of_lintegral_ne_top hm.aemeasurable
    (centred_mass_valid p n m θ ε L).2, ?_⟩
  rw [integral_toReal hm.aemeasurable hfinite]
  exact ENNReal.toReal_pos (centred_mass_valid p n m θ ε L).1
    (centred_mass_valid p n m θ ε L).2

/-- See the proof of Lemma 6.5 in the paper: the actual averaged
observable is the fixed-chart quotient. Both weighted integrals are
integrable and the denominator is positive at every interior length. -/
theorem averagedObservable_centred_ratio
    (G : BlockObservable (⟨n + 1, Nat.succ_pos n⟩ : ℕ+))
    (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) :
    Integrable (fun z : Tangent n =>
      (marginalWeight p n m θ ε (centredChart n L.val z)).toReal *
        G.val (WithLp.ofLp (centredChart n L.val z))) volume ∧
    averagedObservable p n m θ ε G L =
      (∫ z : Tangent n,
        (marginalWeight p n m θ ε (centredChart n L.val z)).toReal *
          G.val (WithLp.ofLp (centredChart n L.val z))) /
      (∫ z : Tangent n,
        (marginalWeight p n m θ ε (centredChart n L.val z)).toReal) := by
  let w := fun z : Tangent n => marginalWeight p n m θ ε (centredChart n L.val z)
  let g := fun z : Tangent n => G.val (WithLp.ofLp (centredChart n L.val z))
  have hm : Measurable w := (measurable_marginalWeight p n m θ ε).comp
    (isometry_centredChart n L.val).continuous.measurable
  have hg : Measurable g := G.property.choose_spec.continuous.measurable.comp
    ((WithLp.measurable_ofLp 2 _).comp
      (isometry_centredChart n L.val).continuous.measurable)
  have hg0 : Measurable (fun x : EuclideanSpace ℝ (Fin (n + 1)) => G.val (WithLp.ofLp x)) :=
    G.property.choose_spec.continuous.measurable.comp (WithLp.measurable_ofLp 2 _)
  have h0 := (centred_mass_valid p n m θ ε L).1
  have ht := (centred_mass_valid p n m θ ε L).2
  have hfinite := ae_lt_top hm ht
  have hiG := observable_integrable_fibre p n m θ ε G L
  rw [fibreKernel_eq_centred_map] at hiG
  have hi : Integrable g (AffineFibre.normalizedMeasure volume w h0 ht) :=
    (integrable_map_measure hg0.aestronglyMeasurable
      (isometry_centredChart n L.val).continuous.measurable.aemeasurable).mp hiG
  have hinum : Integrable (fun z => (w z).toReal * g z) volume := by
    rw [AffineFibre.normalizedMeasure_eq_smul,
      integrable_smul_measure (ENNReal.inv_ne_zero.mpr ht) (ENNReal.inv_ne_top.mpr h0),
      integrable_withDensity_iff_integrable_smul₀' hm.aemeasurable hfinite] at hi
    exact hi
  refine ⟨hinum, ?_⟩
  change (∫ x, G.val (WithLp.ofLp x) ∂fibreKernel p n m θ ε L) = _
  rw [fibreKernel_eq_centred_map,
    integral_map (isometry_centredChart n L.val).continuous.measurable.aemeasurable
      hg0.aestronglyMeasurable,
    AffineFibre.normalizedMeasure_eq_smul, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul₀ hm.aemeasurable hfinite,
    ENNReal.toReal_inv]
  change (∫⁻ z, w z).toReal⁻¹ * (∫ z, (w z).toReal * g z) = _
  rw [← integral_toReal hm.aemeasurable hfinite]
  exact (div_eq_inv_mul _ _).symm

/-- See the proof of Lemma 6.5 in the paper, source disintegration:
the L² norm in length of the fibre source norm is the actual marginal
source norm. This is an equality, with finiteness concluded. -/
theorem source_norm_disintegration
    {χ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (hχ : Measurable χ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x, |χ x| ≤ B) :
    MemLp (fun L => Real.sqrt (∫ x, χ x ^ 2 ∂fibreKernel p n m θ ε L)) 2
      (lengthMeasure p n m θ ε) ∧
    (eLpNorm (fun L => Real.sqrt (∫ x, χ x ^ 2 ∂fibreKernel p n m θ ε L)) 2
      (lengthMeasure p n m θ ε)).toReal =
        (eLpNorm χ 2 (activeMeasure p n m θ ε)).toReal := by
  have := lengthMeasure_probability p n m θ ε
  simpa only [← activeMeasure_eq_comp p n m θ ε] using
    KernelSquareNorm.conditional_norm (lengthMeasure p n m θ ε)
      (fibreKernel p n m θ ε) hχ hB hb

/-- See the proof of Lemma 6.5 in the paper, the integrated multiplier
step. Its explicit internal premises are the source good-set bounds, the
conditional error moment and the pointwise multiplier estimate. -/
theorem integrated_multiplier_internal {ι : Type*} [Fintype ι]
    (χ : ι → EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (hχ : ∀ i, Measurable (χ i))
    {A : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hA : MeasurableSet A)
    (D B : ι → ℝ) (hD : ∀ i, 0 ≤ D i) (hB : ∀ i, 0 ≤ B i)
    (hgood : ∀ i, ∀ᵐ x ∂(activeMeasure p n m θ ε).restrict A, |χ i x| ≤ D i)
    (hb : ∀ i x, |χ i x| ≤ B i)
    {e : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ) → ℝ≥0∞} (he : Measurable e)
    {R : ℝ} (hR : 0 ≤ R)
    (hmoment : (∫⁻ L, e L + e L ^ 2 ∂lengthMeasure p n m θ ε) ≤ ENNReal.ofReal R)
    {a C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    {d : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ) → ℝ}
    (hd : AEStronglyMeasurable d (lengthMeasure p n m θ ε))
    (hbound : ∀ᵐ L ∂lengthMeasure p n m θ ε, |d L| ≤ ∑ i,
      (a * Real.sqrt (∫ x, χ i x ^ 2 ∂fibreKernel p n m θ ε L) +
        C * B i * (Real.sqrt (e L).toReal + (e L).toReal))) :
    MemLp d 2 (lengthMeasure p n m θ ε) ∧
      (eLpNorm d 2 (lengthMeasure p n m θ ε)).toReal ≤
        a * (∑ i, D i) +
          (a * Real.sqrt ((activeMeasure p n m θ ε).real Aᶜ) +
            2 * C * Real.sqrt R) * ∑ i, B i := by
  have := lengthMeasure_probability p n m θ ε
  have hg : ∀ i, ∀ᵐ x ∂((fibreKernel p n m θ ε) ∘ₘ
      lengthMeasure p n m θ ε).restrict A, |χ i x| ≤ D i := by
    simpa only [← activeMeasure_eq_comp p n m θ ε] using hgood
  simpa only [← activeMeasure_eq_comp p n m θ ε] using
    KernelSquareNorm.multiplier_bound (lengthMeasure p n m θ ε)
      (fibreKernel p n m θ ε) χ hχ hA D B hD hB hg hb he hR hmoment ha hC hd hbound

/-- See the proof of Lemma 6.5 in the paper: finite superposition of
the scalar mean multipliers, retaining the negative sign. Only the individual
multiplier estimates and the signed derivative identity are assumed in this
internal composition theorem. -/
theorem integrated_point_sources_internal {ι : Type*} [Fintype ι]
    (χ : ι → EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (hχ : ∀ i, Measurable (χ i))
    {A : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hA : MeasurableSet A)
    (D B : ι → ℝ) (hD : ∀ i, 0 ≤ D i) (hB : ∀ i, 0 ≤ B i)
    (hgood : ∀ i, ∀ᵐ x ∂(activeMeasure p n m θ ε).restrict A, |χ i x| ≤ D i)
    (hb : ∀ i x, |χ i x| ≤ B i)
    {e : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ) → ℝ≥0∞} (he : Measurable e)
    {R : ℝ} (hR : 0 ≤ R)
    (hmoment : (∫⁻ L, e L + e L ^ 2 ∂lengthMeasure p n m θ ε) ≤ ENNReal.ofReal R)
    {a C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    (lam : ι → Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ) → ℝ)
    (hlam : ∀ᵐ L ∂lengthMeasure p n m θ ε, ∀ i, |lam i L| ≤
      a * Real.sqrt (∫ x, χ i x ^ 2 ∂fibreKernel p n m θ ε L) +
        C * B i * (Real.sqrt (e L).toReal + (e L).toReal))
    {d : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ) → ℝ}
    (hd : AEStronglyMeasurable d (lengthMeasure p n m θ ε))
    (hsign : ∀ᵐ L ∂lengthMeasure p n m θ ε, d L = -∑ i, lam i L) :
    MemLp d 2 (lengthMeasure p n m θ ε) ∧
      (eLpNorm d 2 (lengthMeasure p n m θ ε)).toReal ≤
        a * (∑ i, D i) +
          (a * Real.sqrt ((activeMeasure p n m θ ε).real Aᶜ) +
            2 * C * Real.sqrt R) * ∑ i, B i := by
  apply integrated_multiplier_internal p n m θ ε χ hχ hA D B hD hB hgood hb
    he hR hmoment ha hC hd
  filter_upwards [hlam, hsign] with L hL hs
  rw [hs, abs_neg]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hL i)

/-- See the proof of Lemma 6.5 in the paper: the exact long-range
exceptional remainder has a stretched-exponential second-norm error. The tail
power is `coefficientTailPower s η`, fixed before the temperature interval.
This proves the exceptional-error integration step without a conditional
probability assumption at individual lengths. -/
theorem long_remainder_L2 (hRig : External.LongRangeRigidityLocallyUniform)
    (s : Riesz1.RieszExponent) (η C₀ : ℝ) (hε : 0 < ε) (hεη : ε ≤ η)
    (hC₀ : 0 ≤ C₀) (βlo βhi : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ n m : ℕ, 1 ≤ n → 2 * (n + 1) ≤ n + 1 + m + 1 →
      ∀ κ : ℝ, 1 ≤ κ →
      MemLp (fun L => Real.sqrt (longRemainder β s n m θ ε C₀ η κ L).toReal +
        (longRemainder β s n m θ ε C₀ η κ L).toReal) 2
          (lengthMeasure (ofLong β s) n m θ ε) ∧
      (eLpNorm (fun L => Real.sqrt (longRemainder β s n m θ ε C₀ η κ L).toReal +
        (longRemainder β s n m θ ε C₀ η κ L).toReal) 2
          (lengthMeasure (ofLong β s) n m θ ε)).toReal ≤
        C * Real.exp (-c * (n + 1 : ℝ) ^ GoodBlocks.coefficientTailPower s.val η) := by
  obtain ⟨A, b, hA, hb, hmoment⟩ :=
    long_bad_remainder hRig s ε η C₀ hε hεη hC₀ θ βlo βhi hlo hle
  refine ⟨2 * Real.sqrt A, b / 2, by positivity, by positivity,
    fun β hβ n m hn hhalf κ hκ => ?_⟩
  have h := KernelSquareNorm.sqrt_add_toReal
    (lengthMeasure (ofLong β s) n m θ ε)
    (measurable_longRemainder β s n m θ ε C₀ η κ)
    (by positivity) (hmoment β hβ n m hn hhalf κ hκ)
  refine ⟨h.2.1, h.2.2.trans_eq ?_⟩
  rw [Real.sqrt_mul hA.le]
  have hroot (t : ℝ) : Real.sqrt (Real.exp (-b * t)) = Real.exp (-(b / 2) * t) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    ring
  rw [hroot]
  ring

/-- See the proof of Lemma 6.5 in the paper: the long-range physical
normal multiplier is globally integrable on almost every length fibre.
The normal equation has the sign and inverse-temperature normalization of
the multiplier. This uses the physical Hessian pairings. -/
theorem long_multiplier_mean_internal (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (hε : 0 < ε) (hhalf : 2 * (n + 1) ≤ n + 1 + m + 1) :
    let p := ofLong β s
    let F := fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
      ∑ i, (θ.val (((n + 1 : ℝ) ^ ε)⁻¹ * y i) +
        θ.val (((n + 1 : ℝ) ^ ε)⁻¹ * (y i)⁻¹))
    let K := fun y => β.val⁻¹ * (β.val * F y -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n + 1) m (Equiv.refl _) (y,z)).toReal))
    ∀ᵐ L ∂lengthMeasure p n m θ ε,
      ∀ (Q : ScalarFormData (retainedKernel p n m θ ε L))
        (v : Fin (n + 1) → Lp ℝ 2 (retainedKernel p n m θ ε L))
        (u : Fin (n + 1) → Q.1),
      let M := fun x : chartDomain (n + 1) ((n + 1 + m : ℕ) + 1) =>
        β.val • hessianMatrix K x.val
      Integrable (gapMultiplierField n.succPNat Q M v u) (retainedKernel p n m θ ε L) ∧
      (∫ x, gapMultiplierField n.succPNat Q M v u x ∂retainedKernel p n m θ ε L) =
        (n + 1 : ℝ)⁻¹ *
          ((∑ i, ∑ j, ∫ x, M x i j * (u j).val x ∂retainedKernel p n m θ ε L) -
            ∑ i, ∫ x, v i x ∂retainedKernel p n m θ ε L) := by
  intro p F K
  filter_upwards [long_global_pairings β s n m θ ε hε hhalf] with L hL
  intro Q v u M
  have hpair (i j : Fin (n + 1)) :
      Integrable (fun x => M x i j * (u j).val x) (retainedKernel p n m θ ε L) := by
    simpa [M, K, F, p, ofLong] using (hL i j).2 (u j).val
  simpa only [Nat.succPNat_coe, Nat.cast_succ] using
    multiplier_mean_internal n.succPNat Q M v u hpair

/-- See the proof of Lemma 6.5 in the paper: the same globally
integrable normal equation for the actual short-range marginal fibre.
Integrability is a conclusion of the physical coefficient estimates. -/
theorem short_multiplier_mean_internal (hs : 1 < p.val.2)
    (hε : 0 < ε) (hhalf : 2 * (n + 1) ≤ n + 1 + m + 1) :
    let F := fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
      ∑ i, (θ.val (((n + 1 : ℝ) ^ ε)⁻¹ * y i) +
        θ.val (((n + 1 : ℝ) ^ ε)⁻¹ * (y i)⁻¹))
    let K := fun y => p.val.1⁻¹ * (p.val.1 * F y -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n + 1) m (Equiv.refl _) (y,z)).toReal))
    ∀ᵐ L ∂lengthMeasure p n m θ ε,
      ∀ (Q : ScalarFormData (retainedKernel p n m θ ε L))
        (v : Fin (n + 1) → Lp ℝ 2 (retainedKernel p n m θ ε L))
        (u : Fin (n + 1) → Q.1),
      let M := fun x : chartDomain (n + 1) ((n + 1 + m : ℕ) + 1) =>
        p.val.1 • hessianMatrix K x.val
      Integrable (gapMultiplierField n.succPNat Q M v u) (retainedKernel p n m θ ε L) ∧
      (∫ x, gapMultiplierField n.succPNat Q M v u x ∂retainedKernel p n m θ ε L) =
        (n + 1 : ℝ)⁻¹ *
          ((∑ i, ∑ j, ∫ x, M x i j * (u j).val x ∂retainedKernel p n m θ ε L) -
            ∑ i, ∫ x, v i x ∂retainedKernel p n m θ ε L) := by
  intro F K
  filter_upwards [short_global_pairings p hs n m θ ε hε hhalf] with L hL
  intro Q v u M
  have hpair (i j : Fin (n + 1)) :
      Integrable (fun x => M x i j * (u j).val x) (retainedKernel p n m θ ε L) := by
    simpa only [M, Matrix.smul_apply, smul_eq_mul] using (hL i j).2 (u j).val
  simpa only [Nat.succPNat_coe, Nat.cast_succ] using
    multiplier_mean_internal n.succPNat Q M v u hpair

end Riesz2.LengthDerivative
