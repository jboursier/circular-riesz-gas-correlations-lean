/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.LengthAveragingFibresPart2
public import Riesz2.Thermodynamic.InterpolantLocalLawsPart4
public import Riesz2.DecayShort.IntervalCoefficientsPart3
public import Riesz2.HelfferSjostrand.ConditionalEnergyMomentsPart3
public import Riesz2.Frozen.SymmetricMiddleBlock
public import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Common-length exterior kernels for the two-volume comparison

Supporting steps for Proposition 6.6. The exterior kernel is constructed from the
every-length coarea law and the physical exterior conditional, so its definition has no
exceptional-length choices.
-/

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Riesz2.TwoVolumeComparison

/-- See Proposition 6.6 of the paper: the rounded symmetric support has
distance at least `n/8` from either endpoint, including both integer endpoints. -/
theorem symmetricMiddleBlock_boundary (n : ℕ+) (hn : 8 ≤ (n : ℕ))
    (K : ℕ) (hK : K ≤ (n : ℕ) / 4) (i : Fin (n : ℕ))
    (hi : i ∈ symmetricMiddleBlock n K) :
    (n : ℕ) ≤ 8 * (i.val + 1) ∧ (n : ℕ) ≤ 8 * ((n : ℕ) - i.val) := by
  simp only [symmetricMiddleBlock, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  omega

/-- See Proposition 6.6 of the paper, normalization and integrability clauses
of the comparison proposition, before any decay estimate. -/
theorem comparison_valid (p : Parameters) (n N N' : ℕ+)
    (hn : (n : ℕ) ≤ (N : ℕ)) (hn' : (n : ℕ) ≤ (N' : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ) :
    let μ := tiltedParticleMeasure p N n hn θ ε true
    let μ' := tiltedParticleMeasure p N' n hn' θ ε true
    0 < tiltNormalizer p N n hn θ ε true ∧
      tiltNormalizer p N n hn θ ε true < ⊤ ∧
      0 < tiltNormalizer p N' n hn' θ ε true ∧
      tiltNormalizer p N' n hn' θ ε true < ⊤ ∧
      IsProbabilityMeasure μ ∧ IsProbabilityMeasure μ' ∧
      ∀ G : BlockObservable n,
        Integrable (fun X => G.val (finiteGapBlock X)) μ ∧
          Integrable (fun X => G.val (finiteGapBlock X)) μ' := by
  have h := InterpolatingDensities.tilt_valid p N n hn θ ε true
  have h' := InterpolatingDensities.tilt_valid p N' n hn' θ ε true
  have := h.2.2
  have := h'.2.2
  exact ⟨h.1, h.2.1.trans_lt (by simp), h'.1, h'.2.1.trans_lt (by simp), h.2.2, h'.2.2, fun G =>
    ⟨InterpolatingDensities.block_integrable N n G _,
      InterpolatingDensities.block_integrable N' n G _⟩⟩

section Exterior

variable (p : Parameters) (n m : ℕ) (θ : PhysicalCutoff) (ε : ℝ)

/-- See Proposition 6.6 of the paper: first draw the active block on its
length fibre, then the exterior in the existing physical conditional law.
The active chart has `n+1` gaps, and the exterior has `m` free coordinates. -/
def lengthChartKernel :
    Kernel (Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ))
      (AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1) ×
        EuclideanSpace ℝ (Fin m)) :=
  (Kernel.id ×ₖ ProperMarginalChart.conditionalKernel p (n + 1) m (by omega)
    (Equiv.refl _)) ∘ₖ LengthAveragingFibres.retainedKernel p n m θ ε

instance lengthChartKernel_markov : IsMarkovKernel (lengthChartKernel p n m θ ε) := by
  unfold lengthChartKernel
  infer_instance

/-- The full exterior, including its last dependent gap. This is the
existing affine simplex chart, applied at the complementary length. -/
def exteriorChart
    (q : AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1) ×
      EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin (m + 1)) :=
  AffineSimplex.chart m (((n + 1 + m : ℕ) + 1 : ℝ) - ∑ i, q.1.val i) q.2

theorem measurable_exteriorChart : Measurable (exteriorChart n m) := by
  exact (AffineFibre.SumChart.totalChart m).continuous.measurable.comp
    ((measurable_const.sub (Finset.measurable_sum _ fun i _ =>
      (PiLp.continuous_apply 2 _ i).measurable.comp
        (measurable_subtype_coe.comp measurable_fst))).prodMk measurable_snd)

/-- See Proposition 6.6 of the paper: the explicit full exterior conditional
at each interior active length. Its last coordinate is not discarded. -/
def lengthExteriorKernel :
    Kernel (Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ))
      (EuclideanSpace ℝ (Fin (m + 1))) :=
  (lengthChartKernel p n m θ ε).map (exteriorChart n m)

instance lengthExteriorKernel_markov :
    IsMarkovKernel (lengthExteriorKernel p n m θ ε) :=
  Kernel.IsMarkovKernel.map _ (measurable_exteriorChart n m)

/-- The construction of the exterior kernel unfolds as two explicit
physical integrals, for every interior length and every nonnegative test. -/
theorem lintegral_lengthExteriorKernel
    (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ))
    {f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y, f y ∂lengthExteriorKernel p n m θ ε L) =
      ∫⁻ x, ∫⁻ z, f (exteriorChart n m (x, z))
        ∂ProperMarginalChart.conditionalKernel p (n + 1) m (by omega) (Equiv.refl _) x
        ∂LengthAveragingFibres.retainedKernel p n m θ ε L := by
  rw [lengthExteriorKernel, Kernel.lintegral_map _ (measurable_exteriorChart n m) L hf,
    lengthChartKernel]
  rw [Kernel.lintegral_comp _ _ L (show Measurable (fun q => f (exteriorChart n m q)) from
    hf.comp (measurable_exteriorChart n m))]
  apply lintegral_congr
  intro x
  exact Kernel.lintegral_id_prod (hf.comp (measurable_exteriorChart n m)) _ x

/-- See Proposition 6.6 of the paper: the active mass remains the prescribed
length when the physical exterior is added. -/
theorem active_mass_ae_lengthChartKernel
    (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) :
    ∀ᵐ q ∂lengthChartKernel p n m θ ε L, ∑ i, q.1.val i = L.val := by
  have hx : ∀ᵐ x ∂LengthAveragingFibres.retainedKernel p n m θ ε L,
      ∑ i, x.val i = L.val := by
    have hh := LengthAveragingFibres.sum_eq_ae_fibre p n m θ ε L
    rw [← LengthAveragingFibres.map_retainedKernel p n m θ ε L] at hh
    exact (ae_map_iff measurable_subtype_coe.aemeasurable
      (measurableSet_eq_fun (Finset.measurable_sum _ fun i _ =>
        (PiLp.continuous_apply 2 _ i).measurable) measurable_const)).mp hh
  unfold lengthChartKernel
  apply Kernel.ae_comp_of_ae_ae
  · exact measurableSet_eq_fun (Finset.measurable_sum _ fun i _ =>
      (PiLp.continuous_apply 2 _ i).measurable.comp
        (measurable_subtype_coe.comp measurable_fst)) measurable_const
  · filter_upwards [hx] with x hx
    rw [Kernel.prod_apply, Kernel.id_apply]
    apply (Measure.ae_prod_iff_ae_ae ?_).mpr
    · simpa only [ae_dirac_eq, Filter.eventually_pure] using
        (ae_of_all (ProperMarginalChart.conditionalKernel p (n + 1) m
          (by omega) (Equiv.refl _) x) fun _ => hx)
    · exact measurableSet_eq_fun (Finset.measurable_sum _ fun i _ =>
        (PiLp.continuous_apply 2 _ i).measurable.comp
          (measurable_subtype_coe.comp measurable_fst)) measurable_const

/-- See Proposition 6.6 of the paper: every sampled exterior has the
complementary length, including on length fibres of zero marginal measure. -/
theorem exterior_mass_ae
    (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) :
    ∀ᵐ y ∂lengthExteriorKernel p n m θ ε L,
      ∑ i, y i = ((n + 1 + m : ℕ) + 1 : ℝ) - L.val := by
  rw [lengthExteriorKernel, Kernel.map_apply _ (measurable_exteriorChart n m)]
  apply (ae_map_iff (measurable_exteriorChart n m).aemeasurable
    (measurableSet_eq_fun (Finset.measurable_sum _ fun i _ =>
      (PiLp.continuous_apply 2 _ i).measurable) measurable_const)).mpr
  filter_upwards [active_mass_ae_lengthChartKernel p n m θ ε L] with q hq
  change (∑ i, AffineSimplex.chart m _ q.2 i) = _
  rw [AffineSimplex.sum_chart, hq]

/-- See Proposition 6.6 of the paper: the full exterior lies in its
positive mass simplex at every interior active length. -/
theorem exterior_positive_ae
    (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) :
    ∀ᵐ y ∂lengthExteriorKernel p n m θ ε L, ∀ i, 0 < y i := by
  have hP : MeasurableSet {y : EuclideanSpace ℝ (Fin (m + 1)) | ∀ i, 0 < y i} :=
    by
      simpa only [ofPred_forall] using MeasurableSet.iInter
        (fun i : Fin (m + 1) => measurableSet_lt (measurable_const (a := (0 : ℝ)))
          (PiLp.continuous_apply 2 (fun _ : Fin (m + 1) => ℝ) i).measurable)
  rw [lengthExteriorKernel, Kernel.map_apply _ (measurable_exteriorChart n m)]
  apply (ae_map_iff (measurable_exteriorChart n m).aemeasurable hP).mpr
  unfold lengthChartKernel
  apply Kernel.ae_comp_of_ae_ae (hP.preimage (measurable_exteriorChart n m))
  apply ae_of_all
  intro x
  rw [Kernel.prod_apply, Kernel.id_apply]
  apply (Measure.ae_prod_iff_ae_ae (hP.preimage (measurable_exteriorChart n m))).mpr
  simp only [ae_dirac_eq, Filter.eventually_pure]
  filter_upwards [ConditionalEnergyMoments.physical_conditional_support p (n + 1) m
    (by omega) (Equiv.refl _) x] with z hz
  exact ((AffineSimplex.chart_mem_simplex_iff m _ z).mpr hz).1

/-- See Proposition 6.6 of the paper: mixing the chart kernel over the
original length law recovers the retained marginal and its physical exterior
conditional. The identity applies to arbitrary measurable tests. -/
theorem lengthChartKernel_comp_lengthMeasure :
    lengthChartKernel p n m θ ε ∘ₘ LengthAveragingFibres.lengthMeasure p n m θ ε =
      ((LengthAveragingFibres.activeMeasure p n m θ ε).comap Subtype.val) ⊗ₘ
        ProperMarginalChart.conditionalKernel p (n + 1) m (by omega) (Equiv.refl _) := by
  have he : LengthAveragingFibres.retainedKernel p n m θ ε ∘ₘ
      LengthAveragingFibres.lengthMeasure p n m θ ε =
      (LengthAveragingFibres.activeMeasure p n m θ ε).comap Subtype.val := by
    apply Measure.ext_of_lintegral
    intro f hf
    rw [Measure.lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable]
    exact (LengthAveragingFibres.retained_lintegral_disintegration p n m θ ε hf).symm
  rw [lengthChartKernel, ← Measure.comp_assoc, he]
  have := LengthAveragingFibres.lengthMeasure_probability p n m θ ε
  have : IsProbabilityMeasure
      ((LengthAveragingFibres.activeMeasure p n m θ ε).comap
        ((↑) : AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1) → _)) := by
    rw [← he]
    infer_instance
  exact (Measure.compProd_eq_comp_prod _ _).symm

/-- The exterior mixture is the full exterior image of the original joint
active/exterior law, with the dependent last exterior coordinate retained. -/
theorem lengthExteriorKernel_comp_lengthMeasure :
    lengthExteriorKernel p n m θ ε ∘ₘ LengthAveragingFibres.lengthMeasure p n m θ ε =
      (((LengthAveragingFibres.activeMeasure p n m θ ε).comap Subtype.val) ⊗ₘ
        ProperMarginalChart.conditionalKernel p (n + 1) m (by omega) (Equiv.refl _)).map
          (exteriorChart n m) := by
  rw [lengthExteriorKernel, ← Measure.map_comp _ _ (measurable_exteriorChart n m),
    lengthChartKernel_comp_lengthMeasure]

/-- See Proposition 6.6 of the paper: the length mixture of the explicit
joint kernel is the coordinate image of the two-sided tilt. -/
theorem physical_lengthChart_disintegration :
    (tiltedParticleMeasure p ((n + 1) + m).succPNat n.succPNat (by simp; omega) θ ε true).map
      (fun X : Riesz1.Configuration ((n + 1) + m).succPNat =>
        RetainedSimplex.coordinates (n + 1) m (Equiv.refl _) (WithLp.toLp 2 (gapVector X))) =
      (lengthChartKernel p n m θ ε ∘ₘ LengthAveragingFibres.lengthMeasure p n m θ ε).map
        (fun q => (q.1.val, q.2)) := by
  rw [lengthChartKernel_comp_lengthMeasure]
  exact DecayShort.activeTilt_proper_disintegration p n.succPNat m (by simp; omega) θ ε true

end Exterior

section TwoExteriors

variable (p : Parameters) (n m m' : ℕ) (hmm' : m ≤ m') (θ : PhysicalCutoff) (ε : ℝ)

/-- The inclusion of the smaller interior length interval in the larger one. -/
def largerLength (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) :
    Ioo (0 : ℝ) ((n + 1 + m' : ℕ) + 1 : ℝ) :=
  ⟨L.val, L.property.1, L.property.2.trans_le (by
    exact_mod_cast (show n + 1 + m + 1 ≤ n + 1 + m' + 1 by omega))⟩

theorem measurable_largerLength : Measurable (largerLength n m m' hmm') :=
  measurable_subtype_coe.subtype_mk

/-- See Proposition 6.6 of the paper: the actual conditional exterior
product kernel at a common active length. The two draws are independent
conditional on that length. -/
def commonLengthExteriorKernel :
    Kernel (Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ))
      (EuclideanSpace ℝ (Fin (m + 1)) × EuclideanSpace ℝ (Fin (m' + 1))) :=
  lengthExteriorKernel p n m θ ε ×ₖ
    (lengthExteriorKernel p n m' θ ε).comap
      (largerLength n m m' hmm') (measurable_largerLength n m m' hmm')

instance commonLengthExteriorKernel_markov :
    IsMarkovKernel (commonLengthExteriorKernel p n m m' hmm' θ ε) := by
  unfold commonLengthExteriorKernel
  infer_instance

/-- See Proposition 6.6 of the paper: both independent exteriors have
exactly the same complementary active length. -/
theorem commonLengthExteriorKernel_compatible_mass
    (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) :
    ∀ᵐ q ∂commonLengthExteriorKernel p n m m' hmm' θ ε L,
      ((n + 1 + m : ℕ) + 1 : ℝ) - (∑ i, q.1 i) = L.val ∧
      ((n + 1 + m' : ℕ) + 1 : ℝ) - (∑ i, q.2 i) = L.val := by
  rw [commonLengthExteriorKernel, Kernel.prod_apply, Kernel.comap_apply]
  apply (Measure.ae_prod_iff_ae_ae ?_).mpr
  · filter_upwards [exterior_mass_ae p n m θ ε L] with y hy
    filter_upwards [exterior_mass_ae p n m' θ ε (largerLength n m m' hmm' L)] with z hz
    change (∑ i, z i) = ((n + 1 + m' : ℕ) + 1 : ℝ) - L.val at hz
    constructor <;> linarith
  · apply MeasurableSet.inter
    · exact measurableSet_eq_fun (measurable_const.sub
        (Finset.measurable_sum _ fun i _ =>
          (PiLp.continuous_apply 2 _ i).measurable.comp measurable_fst)) measurable_const
    · exact measurableSet_eq_fun (measurable_const.sub
        (Finset.measurable_sum _ fun i _ =>
          (PiLp.continuous_apply 2 _ i).measurable.comp measurable_snd)) measurable_const

end TwoExteriors

/-- See Proposition 6.6 of the paper, the bounded-size argument: first
moments control a centered observable by its derivative sum. -/
theorem centered_expectation_le (N n : ℕ+) (G : BlockObservable n)
    (μ : Measure (Riesz1.Configuration N)) [IsProbabilityMeasure μ]
    (M : ℝ) (hm : ∀ j : Fin (n : ℕ),
      Integrable (fun X => gap X j.val) μ ∧ (∫ X, gap X j.val ∂μ) ≤ M) :
    |(∫ X, G.val (finiteGapBlock X) ∂μ) - G.val (fun _ => 1)| ≤
      (M + 1) * blockDerivativeNorm G := by
  classical
  let a := fun j => (coordinateDerivativeNorm G j : ℝ)
  have hi := InterpolatingDensities.block_integrable N n G μ
  have hH : Integrable (fun X => ∑ j, a j * (gap X j.val + 1)) μ :=
    integrable_finsetSum _ fun j _ => ((hm j).1.add (integrable_const 1)).const_mul (a j)
  calc
    _ = |∫ X, G.val (finiteGapBlock X) - G.val (fun _ => 1) ∂μ| := by
      rw [integral_sub hi (integrable_const _), integral_const, probReal_univ, one_smul]
    _ ≤ ∫ X, |G.val (finiteGapBlock X) - G.val (fun _ => 1)| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ X, ∑ j, a j * (gap X j.val + 1) ∂μ := by
      apply integral_mono_ae (hi.sub (integrable_const _)).abs hH
      apply ae_of_all
      intro X
      apply (InterpolatingDensities.block_bound G (fun _ => 1) (finiteGapBlock X)).trans
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg _)
      change |gap X j.val - 1| ≤ gap X j.val + 1
      have hg : 0 < gap X j.val := Riesz1.gap_pos X j.val
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    _ = ∑ j, a j * ((∫ X, gap X j.val ∂μ) + 1) := by
      rw [integral_finsetSum]
      rotate_left
      · intro j _
        exact ((hm j).1.add (integrable_const 1)).const_mul (a j)
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul, integral_add (hm j).1 (integrable_const 1), integral_const,
        probReal_univ, one_smul]
    _ ≤ ∑ j, a j * (M + 1) := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (add_le_add (hm j).2 (le_refl 1)) (NNReal.coe_nonneg _)
    _ = (M + 1) * blockDerivativeNorm G := by
      rw [← Finset.sum_mul, mul_comm]
      rfl

/-- See Proposition 6.6 of the paper: the direct global comparison needed
for all bounded active sizes, uniformly in both ambient volumes and on a
compact positive temperature interval. No overlap assumption is used. -/
theorem compact_global_comparison (s ε βlo βhi : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (hε : 0 < ε) (hlo : 0 < βlo) (hle : βlo ≤ βhi) (θ : PhysicalCutoff) :
    ∃ B : ℝ, 0 < B ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ N N' n : ℕ+,
      2 ≤ (N : ℕ) → 2 ≤ (N' : ℕ) →
      ∀ (hn : (n : ℕ) ≤ (N : ℕ)) (hn' : (n : ℕ) ≤ (N' : ℕ)),
      ∀ G : BlockObservable n,
        |(∫ X, G.val (finiteGapBlock X) ∂tiltedParticleMeasure p N n hn θ ε true) -
          (∫ X, G.val (finiteGapBlock X) ∂tiltedParticleMeasure p N' n hn' θ ε true)| ≤
            B * blockDerivativeNorm G := by
  obtain ⟨M, hM, hm⟩ := InterpolantLocalLaws.compact_tilted_gap_moments s ε βlo βhi
    hs hs1 hε hlo hle θ 1 (by norm_num)
  refine ⟨2 * (M + 1), by positivity, fun p hps hpl hph N N' n hN hN' hn hn' G => ?_⟩
  have first (V : ℕ+) (hV : 2 ≤ (V : ℕ)) (hnV : (n : ℕ) ≤ (V : ℕ)) :
      |(∫ X, G.val (finiteGapBlock X) ∂tiltedParticleMeasure p V n hnV θ ε true) -
        G.val (fun _ => 1)| ≤ (M + 1) * blockDerivativeNorm G := by
    have := (InterpolatingDensities.tilt_valid p V n hnV θ ε true).2.2
    apply centered_expectation_le V n G _ M
    intro j
    have hg : Integrable (fun X : Riesz1.Configuration V => gap X j.val)
        (tiltedParticleMeasure p V n hnV θ ε true) := by
      apply (integrable_const (V : ℝ)).mono' (Riesz1.measurable_gap j.val).aestronglyMeasurable
      apply ae_of_all
      intro X
      simpa only [Real.norm_eq_abs, abs_of_pos (Riesz1.gap_pos X j.val)] using
        Riesz1.gap_le_N X j.val
    refine ⟨hg, ?_⟩
    have hb := (le_add_right (le_refl _)).trans (hm p hps hpl hph V n hV hnV j.val)
    simp only [Real.rpow_one] at hb
    rw [← ofReal_integral_eq_lintegral_ofReal hg
      (ae_of_all _ fun X => (Riesz1.gap_pos X j.val).le)] at hb
    exact (ENNReal.ofReal_le_ofReal_iff hM.le).mp hb
  calc
    _ ≤ |(∫ X, G.val (finiteGapBlock X) ∂tiltedParticleMeasure p N n hn θ ε true) -
        G.val (fun _ => 1)| +
        |G.val (fun _ => 1) -
          (∫ X, G.val (finiteGapBlock X) ∂tiltedParticleMeasure p N' n hn' θ ε true)| :=
      abs_sub_le _ _ _
    _ ≤ (M + 1) * blockDerivativeNorm G + (M + 1) * blockDerivativeNorm G := by
      rw [abs_sub_comm (G.val (fun _ => 1))]
      exact add_le_add (first N hN hn) (first N' hN' hn')
    _ = _ := by ring

end Riesz2.TwoVolumeComparison
