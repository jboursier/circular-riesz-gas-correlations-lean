/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.BoundaryEntriesPart2
public import Riesz2.DecayLong.GlobalSums
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# Physical compensation coefficients on conditional fibres

The coefficients of Subsection 5.1 use the physical conditional
law and ambient Hessian. The exterior has `m + 1` gaps and `m` free coordinates.
In particular its averaging vector is defined also when `m = 0`.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical ProbabilityTheory

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.ConditionalForces

/-- See Subsection 5.1 of the paper: the uniform exterior vector `1_{Iᶜ}/(N-n)`,
with `N = n + m + 1`. -/
def compensationVector (n m : ℕ) (a : Fin (n + m + 1)) : ℝ :=
  if a.val < n then 0 else (m + 1 : ℝ)⁻¹

theorem compensationVector_nonneg (n m : ℕ) (a : Fin (n + m + 1)) :
    0 ≤ compensationVector n m a := by
  unfold compensationVector
  split_ifs <;> positivity

theorem compensationVector_active (n m : ℕ) (a : Fin n) :
    compensationVector n m (a.castAdd m).castSucc = 0 := by
  simp [compensationVector, a.isLt]

theorem compensationVector_exterior (n m : ℕ) (a : Fin (m + 1)) :
    compensationVector n m (a.natAdd n) = (m + 1 : ℝ)⁻¹ := by
  simp [compensationVector, Fin.val_natAdd]

theorem compensationVector_sum (n m : ℕ) :
    ∑ a, compensationVector n m a = 1 := by
  change (∑ a : Fin (n + (m + 1)),
    if a.val < n then (0 : ℝ) else (m + 1 : ℝ)⁻¹) = 1
  rw [Fin.sum_univ_add (a := n) (b := m + 1)]
  simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.is_lt, ↓reduceIte,
    not_lt_of_ge (Nat.le_add_right _ _), Finset.sum_const_zero, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, zero_add]
  push_cast
  exact mul_inv_cancel₀ (by positivity)

theorem compensationVector_le (n m : ℕ) (hn : 2 * n ≤ n + m + 1)
    (a : Fin (n + m + 1)) :
    compensationVector n m a ≤ 2 / (n + m + 1 : ℝ) := by
  have hN : (0 : ℝ) < n + m + 1 := by positivity
  have hcmp : (n + m + 1 : ℝ) ≤ 2 * (m + 1 : ℝ) := by
    exact_mod_cast (show n + m + 1 ≤ 2 * (m + 1) by omega)
  unfold compensationVector
  split_ifs
  · positivity
  · apply (le_div_iff₀ hN).mpr
    apply (inv_mul_le_iff₀ (by positivity : (0 : ℝ) < m + 1)).mpr
    linarith

/-- See Subsection 5.1 of the paper: `bᵢ = E[(H q)ᵢ]`, on every interior fibre.
The finite sums are integrable by `integrable_chartHessian`. -/
def compensationB (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (i : Fin (n : ℕ))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) : ℝ :=
  ∫ z, ∑ a, GoodBlocks.chartHessian s n m (i.castAdd m).castSucc a (x.val, z) *
    compensationVector n m a
    ∂ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x

/-- See Subsection 5.1 of the paper: `c = E[qᵀ H q]`, on every interior fibre. -/
def compensationC (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) : ℝ :=
  ∫ z, ∑ a, ∑ b, compensationVector n m a *
    GoodBlocks.chartHessian s n m a b (x.val, z) * compensationVector n m b
    ∂ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x

/-- See Subsection 5.1 of the paper: the exact compensation matrix `Qᵢⱼ = -bᵢ-bⱼ+c`. -/
def compensationQ (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (i j : Fin (n : ℕ))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) : ℝ :=
  -compensationB β s n m i x - compensationB β s n m j x + compensationC β s n m x

theorem integrable_compensationB (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (i : Fin (n : ℕ))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    Integrable (fun z => ∑ a, GoodBlocks.chartHessian s n m
      (i.castAdd m).castSucc a (x.val, z) * compensationVector n m a)
      (ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x) :=
  integrable_finsetSum _ fun a _ =>
    (GoodBlocks.integrable_chartHessian β s n m n.pos x _ a).mul_const _

theorem integrable_compensationC (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    Integrable (fun z => ∑ a, ∑ b, compensationVector n m a *
      GoodBlocks.chartHessian s n m a b (x.val, z) * compensationVector n m b)
      (ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x) :=
  integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ =>
    ((GoodBlocks.integrable_chartHessian β s n m n.pos x a b).const_mul _).mul_const _

theorem measurable_compensationB (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (i : Fin (n : ℕ)) :
    Measurable (compensationB β s n m i) := by
  have hf : Measurable (fun q : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) ×
      EuclideanSpace ℝ (Fin m) => ∑ a, GoodBlocks.chartHessian s n m
        (i.castAdd m).castSucc a (q.1.val, q.2) * compensationVector n m a) := by
    apply Finset.measurable_sum
    intro a _
    exact ((GoodBlocks.measurable_chartHessian s n m _ a).comp
      ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)).mul_const _
  exact (hf.stronglyMeasurable.integral_kernel_prod_right'
    (κ := ProperMarginalChart.conditionalKernel (ofLong β s) n m n.pos (Equiv.refl _))).measurable

theorem measurable_compensationC (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) : Measurable (compensationC β s n m) := by
  have hf : Measurable (fun q : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) ×
      EuclideanSpace ℝ (Fin m) => ∑ a, ∑ b, compensationVector n m a *
        GoodBlocks.chartHessian s n m a b (q.1.val, q.2) * compensationVector n m b) := by
    apply Finset.measurable_sum
    intro a _
    apply Finset.measurable_sum
    intro b _
    exact (((GoodBlocks.measurable_chartHessian s n m a b).comp
      ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)).const_mul _).mul_const _
  exact (hf.stronglyMeasurable.integral_kernel_prod_right'
    (κ := ProperMarginalChart.conditionalKernel (ofLong β s) n m n.pos (Equiv.refl _))).measurable

private theorem fibre_simplex (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    ∀ᵐ z ∂ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x,
      WithLp.ofLp (RetainedSimplex.chart n m ((n + m : ℕ) + 1)
        (Equiv.refl _) (x.val, z)) ∈ Riesz1.gapSimplex ((n : ℕ) + m).succPNat := by
  filter_upwards [ConditionalEnergyMoments.physical_conditional_support
    (ofLong β s) n m n.pos (Equiv.refl _) x] with z hz
  have hd := (Set.ext_iff.mp (RetainedSimplex.fibre_domain n m _ x.property) z).mpr hz
  have hy := (RetainedSimplex.chart_mem_simplex n m _ (Equiv.refl _) _).mpr hd
  exact ⟨hy.1, by simpa only [Nat.succPNat_coe, Nat.cast_succ] using hy.2⟩

theorem compensationB_nonneg (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (i : Fin (n : ℕ))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    0 ≤ compensationB β s n m i x := by
  apply integral_nonneg_of_ae
  filter_upwards [fibre_simplex β s n m x] with z hz
  exact Finset.sum_nonneg fun a _ => mul_nonneg
    (GoodBlocks.gapHessian_nonneg β s _ _ _ _ hz) (compensationVector_nonneg _ _ _)

theorem compensationC_nonneg (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    0 ≤ compensationC β s n m x := by
  apply integral_nonneg_of_ae
  filter_upwards [fibre_simplex β s n m x] with z hz
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
    mul_nonneg (mul_nonneg (compensationVector_nonneg _ _ _)
      (GoodBlocks.gapHessian_nonneg β s _ _ _ _ hz)) (compensationVector_nonneg _ _ _)

/-- The compensation cancels exactly in a column difference, as used in
the proof of Lemma 5.8. -/
theorem compensationQ_sub (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (i j l : Fin (n : ℕ))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    compensationQ β s n m i j x - compensationQ β s n m i l x =
      compensationB β s n m l x - compensationB β s n m j x := by
  unfold compensationQ
  ring

/-- See Lemma 5.7 in the paper, the second inequality of
equation (5.24): positivity of the actual compensation coefficient suffices. -/
theorem compensated_crossing_le (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (i : Fin (n : ℕ))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    β.val⁻¹ * (BoundaryEntries.physicalCrossing β s n m x i i -
      2 * compensationB β s n m i x + compensationC β s n m x) ≤
    β.val⁻¹ * (BoundaryEntries.physicalCrossing β s n m x i i +
      compensationC β s n m x) := by
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr β.property.le)
  linarith [compensationB_nonneg β s n m i x]

/-- A nonnegative finite weighted sum has the sum of the individual moment
bounds as an upper bound, for every exponent at least one. -/
private theorem finite_weighted_norm_internal {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) {p : ℝ≥0∞} (hp : 1 ≤ p) (f : ι → Ω → ℝ)
    (w A : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hA : ∀ i, 0 ≤ A i)
    (hf : ∀ i, eLpNorm (f i) p μ ≤ ENNReal.ofReal (A i)) :
    eLpNorm (fun x => ∑ i, f i x * w i) p μ ≤
      ENNReal.ofReal (∑ i, A i * w i) := by
  classical
  have hterm (i : ι) : eLpNorm (fun x => f i x * w i) p μ ≤
      ENNReal.ofReal (A i * w i) := by
    have he : (fun x => f i x * w i) = w i • f i := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [he, eLpNorm_const_smul, Real.enorm_eq_ofReal (hw i)]
    apply (mul_le_mul le_rfl (hf i) (by positivity) (by positivity)).trans_eq
    rw [← ENNReal.ofReal_mul (hw i), mul_comm]
  calc
    _ ≤ ∑ i, eLpNorm (fun x => f i x * w i) p μ := by
      simpa only [Finset.sum_fn] using
        (eLpNorm_sum_le (f := fun i x => f i x * w i) (s := Finset.univ) hp)
    _ ≤ ∑ i, ENNReal.ofReal (A i * w i) := Finset.sum_le_sum fun i _ => hterm i
    _ = _ := (ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (hA i) (hw i)).symm


/-- Conditional Jensen for a measurable observable of the actual full gap
vector, using the physical disintegration and the tilted law. -/
theorem conditional_gap_observable_eLpNorm_le (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ)
    (f : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ) (hf : Measurable f)
    {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm (fun x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) =>
      ∫ z, f (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val, z))
        ∂ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x)
      (ENNReal.ofReal p)
      ((activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n hn θ ε false).comap
        ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
          EuclideanSpace ℝ (Fin (n : ℕ)))) ≤
    eLpNorm (fun X : Riesz1.Configuration ((n : ℕ) + m).succPNat =>
      f (WithLp.toLp 2 (gapVector X))) (ENNReal.ofReal p)
      (tiltedParticleMeasure (ofLong β s) ((n : ℕ) + m).succPNat n hn θ ε false) := by
  let μ := (activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n hn θ ε false).comap
    ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
  let K := ProperMarginalChart.conditionalKernel (ofLong β s) n m n.pos (Equiv.refl _)
  let g := f ∘ RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _)
  let inc := fun q : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) ×
      EuclideanSpace ℝ (Fin m) => (q.1.val, q.2)
  have hi : Measurable inc :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  have hg : Measurable g := hf.comp (RetainedSimplex.continuous_chart n m _ _).measurable
  have : IsProbabilityMeasure μ := GoodBlocks.proper_active_probability _ _ _ _ _ _
  have hc : Measurable (fun X : Riesz1.Configuration ((n : ℕ) + m).succPNat =>
      RetainedSimplex.coordinates n m (Equiv.refl _) (WithLp.toLp 2 (gapVector X))) :=
    (RetainedSimplex.continuous_coordinates n m (Equiv.refl _)).measurable.comp
      ((PiLp.volume_preserving_toLp _).measurable.comp (Riesz1.measurable_gapVector _))
  have hJ := GoodBlocks.proper_disintegration (ofLong β s) n m hn θ ε
  change _ = (μ ⊗ₘ K).map inc at hJ
  have hnorm : eLpNorm (g ∘ inc) (ENNReal.ofReal p) (μ ⊗ₘ K) =
      eLpNorm (fun X : Riesz1.Configuration ((n : ℕ) + m).succPNat =>
      f (WithLp.toLp 2 (gapVector X))) (ENNReal.ofReal p)
        (tiltedParticleMeasure (ofLong β s) ((n : ℕ) + m).succPNat n hn θ ε false) := by
    rw [← eLpNorm_map_measure hg.aestronglyMeasurable hi.aemeasurable, ← hJ,
      eLpNorm_map_measure hg.aestronglyMeasurable hc.aemeasurable]
    apply eLpNorm_congr_ae
    exact ae_of_all _ fun X => by
      dsimp only [g, Function.comp_def]
      rw [GoodBlocks.retained_chart_gapVector]
  exact (eLpNorm_integral_kernel_le μ K (hg.comp hi) hp).trans_eq hnorm

/-- The interval q-mass bound used in Lemma 5.7 of the paper. -/
private theorem interval_q_mass (n m : ℕ) (hn : 2 * n ≤ n + m + 1)
    (a : Fin (n + m + 1)) (r : Fin ((n + m + 1) / 2)) :
    0 ≤ (∑ b ∈ cyclicIndexInterval (n + m).succPNat a (r.val + 1), compensationVector n m b) ∧
    (∑ b ∈ cyclicIndexInterval (n + m).succPNat a (r.val + 1), compensationVector n m b) ≤
      2 / (n + m + 1 : ℝ) * (r.val + 1 : ℝ) := by
  refine ⟨Finset.sum_nonneg (fun b _ => compensationVector_nonneg n m b), ?_⟩
  calc
    _ ≤ ∑ _b ∈ cyclicIndexInterval (n + m).succPNat a (r.val + 1),
        2 / (n + m + 1 : ℝ) := Finset.sum_le_sum fun b _ => compensationVector_le n m hn b
    _ ≤ _ := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact_mod_cast (show (cyclicIndexInterval (n + m).succPNat a (r.val + 1)).card ≤ r.val + 1 from
        (Finset.card_image_le).trans_eq (Finset.card_range _))

/-- The size sum in Lemma 5.7: `s < 1` makes the length sum
at most `N^(1-s)/(1-s)`. -/
private theorem compensation_length_sum (s : Riesz1.RieszExponent) (N : ℕ+) :
    (∑ r : Fin ((N : ℕ) / 2), (r.val + 1 : ℝ) ^ (-s.val)) ≤
      (N : ℝ) ^ (1 - s.val) / (1 - s.val) := by
  by_cases h : (N : ℕ) / 2 = 0
  · rw [h]
    simp only [Fin.sum_univ_zero]
    exact div_nonneg (Real.rpow_nonneg (by positivity) _) (by linarith [s.property.2])
  have hh := sum_range_one_add_rpow_le_of_lt_one s.property.1 s.property.2
    (by omega : 1 ≤ (N : ℕ) / 2)
  rw [← Fin.sum_univ_eq_sum_range] at hh
  have he : (fun r : Fin ((N : ℕ) / 2) => (1 + (r.val : ℝ)) ^ (-s.val)) =
      (fun r => (r.val + 1 : ℝ) ^ (-s.val)) := by funext r; rw [add_comm]
  rw [he] at hh
  exact hh.trans (div_le_div_of_nonneg_right
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.div_le_self (N : ℕ) 2)
      (by linarith [s.property.2])) (by linarith [s.property.2]))

/-- The two size counts in Lemma 5.7, before conditional Jensen.
There are `r` intervals through a label and `N` intervals in total. -/
private theorem compensation_interval_size_norm_internal {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Riesz1.RieszExponent) (n m : ℕ)
    (hn : 2 * n ≤ n + m + 1) {p B : ℝ} (hp : 1 ≤ p) (hB : 0 ≤ B)
    (F : Fin ((n + m + 1) / 2) → Fin (n + m + 1) → Ω → ℝ)
    (hF : ∀ r a, eLpNorm (F r a) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (B * (r.val + 1 : ℝ) ^ (-s.val - 2))) :
    let J := fun (r : Fin ((n + m + 1) / 2)) (a : Fin (n + m + 1)) =>
      cyclicIndexInterval (n + m).succPNat a (r.val + 1)
    let w := fun r a => ∑ b ∈ J r a, compensationVector n m b
    (∀ i : Fin (n + m + 1),
      eLpNorm (fun x => ∑ r, ∑ a, if i ∈ J r a then F r a x * w r a else 0)
        (ENNReal.ofReal p) μ ≤ ENNReal.ofReal
          (4 * B / (1 - s.val) * (n + m + 1 : ℝ) ^ (-s.val))) ∧
      eLpNorm (fun x => ∑ r, ∑ a, F r a x * (w r a) ^ 2)
        (ENNReal.ofReal p) μ ≤ ENNReal.ofReal
          (4 * B / (1 - s.val) * (n + m + 1 : ℝ) ^ (-s.val)) := by
  classical
  dsimp only
  let N : ℕ+ := (n + m).succPNat
  let J := fun (r : Fin ((n + m + 1) / 2)) (a : Fin (n + m + 1)) =>
    cyclicIndexInterval N a (r.val + 1)
  let w := fun r a => ∑ b ∈ J r a, compensationVector n m b
  let U := fun r : Fin ((n + m + 1) / 2) => (r.val + 1 : ℝ)
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have hw (r a) : 0 ≤ w r a ∧ w r a ≤ 2 / (n + m + 1 : ℝ) * U r := interval_q_mass n m hn a r
  have hU (r) : 0 < U r := by dsimp [U]; positivity
  have hcount (r : Fin ((n + m + 1) / 2)) (i : Fin (n + m + 1)) :
      (∑ a : Fin (n + m + 1), if i ∈ J r a then (1 : ℝ) else 0) = U r := by
    have h := cyclicIndexInterval_pair_count N (r := r.val + 1)
      (by have := r.isLt; dsimp [N]; omega) i i
    have he : (∑ a : Fin (n + m + 1), if i ∈ J r a then (1 : ℝ) else 0) =
        ∑ a : Fin (n + m + 1), (if i ∈ J r a then (1 : ℝ) else 0) *
          (if i ∈ J r a then 1 else 0) := by
      apply Finset.sum_congr rfl; intro a _; split_ifs <;> norm_num
    calc
      _ = ∑ a : Fin (n+m+1), (if i ∈ J r a then (1 : ℝ) else 0) *
          (if i ∈ J r a then 1 else 0) := he
      _ = ((r.val + 1 - Riesz1.cyclicIndexDistance N i i : ℕ) : ℝ) := h
      _ = _ := by
        simp only [U, Riesz1.cyclicIndexDistance, Nat.dist_self, Nat.zero_min,
          Nat.sub_zero, Nat.cast_add, Nat.cast_one]
  have hpower (r) : U r * U r * U r ^ (-s.val - 2) = U r ^ (-s.val) := by
    rw [← sq, ← Real.rpow_two, ← Real.rpow_add (hU r)]
    congr 1; ring
  have hsum (W : Fin ((n + m + 1) / 2) → Fin (n + m + 1) → ℝ)
      (hW : ∀ r a, 0 ≤ W r a)
      (hc : ∀ r, (∑ a, B * U r ^ (-s.val - 2) * W r a) ≤
        4 * B / (n + m + 1 : ℝ) * U r ^ (-s.val)) :
      eLpNorm (fun x => ∑ r, ∑ a, F r a x * W r a) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (4 * B / (1 - s.val) * (n + m + 1 : ℝ) ^ (-s.val)) := by
    have hnorm (r) := finite_weighted_norm_internal μ hpE (F r) (W r)
      (fun _ => B * U r ^ (-s.val - 2)) (hW r) (fun _ => by positivity) (hF r)
    calc
      _ ≤ ∑ r, eLpNorm (fun x => ∑ a, F r a x * W r a) (ENNReal.ofReal p) μ := by
        simpa only [Finset.sum_fn] using eLpNorm_sum_le
          (f := fun r x => ∑ a, F r a x * W r a) (s := Finset.univ) hpE
      _ ≤ ∑ r, ENNReal.ofReal (∑ a, B * U r ^ (-s.val - 2) * W r a) :=
        Finset.sum_le_sum fun r _ => hnorm r
      _ = ENNReal.ofReal (∑ r, ∑ a, B * U r ^ (-s.val - 2) * W r a) :=
        (ENNReal.ofReal_sum_of_nonneg fun r _ => Finset.sum_nonneg fun a _ =>
          mul_nonneg (mul_nonneg hB (Real.rpow_nonneg (hU r).le _)) (hW r a)).symm
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        apply (Finset.sum_le_sum fun r _ => hc r).trans
        rw [← Finset.mul_sum]
        have hlength : (∑ r : Fin ((n+m+1)/2), U r ^ (-s.val)) ≤
            (n+m+1 : ℝ) ^ (1-s.val) / (1-s.val) := by
          simpa only [N, U, Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using compensation_length_sum s N
        have ht := mul_le_mul_of_nonneg_left hlength
          (by positivity : 0 ≤ 4 * B / (n + m + 1 : ℝ))
        apply ht.trans_eq
        rw [show 1 - s.val = 1 + (-s.val) by ring,
          Real.rpow_add (by positivity : (0 : ℝ) < n+m+1), Real.rpow_one]
        field_simp
  change (∀ i, eLpNorm (fun x => ∑ r, ∑ a, if i ∈ J r a then F r a x * w r a else 0)
    (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (4*B/(1-s.val)*(n+m+1 : ℝ)^(-s.val))) ∧
    eLpNorm (fun x => ∑ r, ∑ a, F r a x * (w r a)^2) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (4*B/(1-s.val)*(n+m+1 : ℝ)^(-s.val))
  constructor
  · intro i
    have he (x) : (∑ r, ∑ a, if i ∈ J r a then F r a x * w r a else 0) =
        ∑ r, ∑ a, F r a x * (if i ∈ J r a then w r a else 0) := by
      apply Finset.sum_congr rfl; intro r _
      apply Finset.sum_congr rfl; intro a _
      split_ifs <;> simp
    simp_rw [he]
    apply hsum (fun r a => if i ∈ J r a then w r a else 0)
      (fun r a => by split_ifs; exact (hw r a).1; exact le_rfl)
    intro r
    calc
      _ ≤ ∑ a, B * U r ^ (-s.val - 2) *
          (if i ∈ J r a then 2 / (n + m + 1 : ℝ) * U r else 0) := by
        apply Finset.sum_le_sum; intro a _
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        split_ifs; exact (hw r a).2; exact le_rfl
      _ = (2 * B / (n + m + 1 : ℝ)) * U r ^ (-s.val) := by
        have he (a) : B * U r ^ (-s.val - 2) * (if i ∈ J r a then 2 / (n + m + 1 : ℝ) * U r else 0) =
            (B * U r ^ (-s.val - 2) * (2 / (n + m + 1 : ℝ) * U r)) * (if i ∈ J r a then 1 else 0) := by
          split_ifs <;> ring
        simp_rw [he]
        rw [← Finset.mul_sum, hcount]
        calc
          _ = (2 * B / (n + m + 1 : ℝ)) * (U r * U r * U r ^ (-s.val - 2)) := by ring
          _ = _ := by rw [hpower]
      _ ≤ _ := by
        gcongr
        norm_num
  · apply hsum (fun r a => (w r a) ^ 2) (fun _ _ => sq_nonneg _)
    intro r
    calc
      _ ≤ ∑ _a : Fin (n + m + 1), B * U r ^ (-s.val - 2) * (2 / (n + m + 1 : ℝ) * U r) ^ 2 :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (hw r a).1 (hw r a).2 2) (by positivity)
      _ = 4 * B / (n + m + 1 : ℝ) * U r ^ (-s.val) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        calc
          _ = (4 * B / (n + m + 1 : ℝ)) * (U r * U r * U r ^ (-s.val - 2)) := by field_simp; ring
          _ = _ := by rw [hpower]

/-- Expanding the Hessian contraction into intervals for Lemma 5.7. -/
private theorem particle_compensation_row (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n m : ℕ) (i : Fin (n + m + 1))
    (X : Riesz1.Configuration (n + m).succPNat) :
    (∑ b, GoodBlocks.particleHessian (ofLong β s) (n + m).succPNat i b X * compensationVector n m b) =
    ∑ r : Fin ((n + m + 1) / 2), ∑ a : Fin (n + m + 1),
      if i ∈ cyclicIndexInterval (n + m).succPNat a (r.val + 1) then
        GoodBlocks.particleCoefficient (ofLong β s) (n + m).succPNat a.val
          (r.val + 1) (by omega) (by have := r.isLt; simpa only [Nat.succPNat_coe] using Nat.succ_le_of_lt r.isLt) X *
        (∑ b ∈ cyclicIndexInterval (n + m).succPNat a (r.val + 1), compensationVector n m b) else 0 := by
  simp only [GoodBlocks.particleHessian, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  by_cases hi : i ∈ cyclicIndexInterval (n + m).succPNat a (r.val + 1)
  · simp only [hi, true_and, ↓reduceIte, Finset.mul_sum]
    simp_rw [ite_mul, zero_mul]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext b; simp
    · intro b _; rfl
  · simp only [hi, false_and, ↓reduceIte, zero_mul, Finset.sum_const_zero]

/-- The second contraction counts every interval once in Lemma 5.7. -/
private theorem particle_compensation_scalar (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n m : ℕ)
    (X : Riesz1.Configuration (n + m).succPNat) :
    (∑ a, ∑ b, compensationVector n m a *
      GoodBlocks.particleHessian (ofLong β s) (n + m).succPNat a b X * compensationVector n m b) =
    ∑ r : Fin ((n + m + 1) / 2), ∑ a : Fin (n + m + 1),
      GoodBlocks.particleCoefficient (ofLong β s) (n + m).succPNat a.val
        (r.val + 1) (by omega) (by have := r.isLt; simpa only [Nat.succPNat_coe] using Nat.succ_le_of_lt r.isLt) X *
        (∑ b ∈ cyclicIndexInterval (n + m).succPNat a (r.val + 1), compensationVector n m b) ^ 2 := by
  simp_rw [mul_assoc, ← Finset.mul_sum, particle_compensation_row,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [← Finset.mul_sum, ← Finset.sum_mul]
  let w : ℝ := ∑ b ∈ cyclicIndexInterval (n+m).succPNat a (r.val+1), compensationVector n m b
  let c : ℝ := GoodBlocks.particleCoefficient (ofLong β s) (n+m).succPNat a.val
    (r.val+1) (by omega) (by have := r.isLt; simpa only [Nat.succPNat_coe] using Nat.succ_le_of_lt r.isLt) X
  change w * (c * w) = c * w ^ 2
  ring

/-- See Lemma 5.7 in the paper, the `bᵢ,c` size clause.
The constant is uniform in the sizes and the moment exponent, locally uniform
in temperature, and the moment degree is exactly `(s + 2) / s`. The active law
is the law transported to its open carrier. The proof follows
Lemma 5.7 of the paper, using its two interval counts. -/
theorem compensation_size_moments (s : Riesz1.RieszExponent)
    (βlo βhi ε Cθ : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi)
    (hε : 0 < ε) (hCθ : 1 ≤ Cθ) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n : ℕ+) (m : ℕ), 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ (p : ℝ), 1 ≤ p →
      let μ := (activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n hn θ ε false).comap
        ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
          EuclideanSpace ℝ (Fin (n : ℕ)))
      ∀ i : Fin (n : ℕ),
        eLpNorm (compensationB β s n m i) (ENNReal.ofReal p) μ +
          eLpNorm (compensationC β s n m) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (C * p ^ ((s.val + 2) / s.val) *
          ((n : ℝ) + m + 1) ^ (-s.val)) := by
  obtain ⟨D, hD, hH⟩ := GoodBlocks.tilted_coefficient_moments s.val βlo βhi ε Cθ
    s.property.1 hlo hle hε hCθ
  have hs : 0 < 1 - s.val := sub_pos.mpr s.property.2
  refine ⟨8 * D / (1 - s.val), by positivity, ?_⟩
  intro β hβ n m hper hn θ hcurv p hp
  dsimp only
  let N : ℕ+ := ((n : ℕ) + m).succPNat
  let μ := (activeTiltedGapLaw (ofLong β s) N n hn θ ε false).comap
    ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
      EuclideanSpace ℝ (Fin (n : ℕ)))
  let ρ := tiltedParticleMeasure (ofLong β s) N n hn θ ε false
  let M := 4 * (D * p ^ ((s.val + 2) / s.val)) / (1 - s.val) *
    ((n : ℝ) + m + 1) ^ (-s.val)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hN : 2 ≤ (N : ℕ) := by dsimp [N]; have := n.pos; omega
  have hcounts := compensation_interval_size_norm_internal ρ s n m hper hp
    (by positivity : 0 ≤ D * p ^ ((s.val + 2) / s.val))
    (fun r a => GoodBlocks.particleCoefficient (ofLong β s) N a.val (r.val + 1)
      (by omega) (by have := r.isLt; dsimp [N]; omega))
    (fun r a => by
      simpa only [Nat.cast_add, Nat.cast_one] using
        hH (ofLong β s) rfl hβ.1 hβ.2 N n hN hn θ hcurv a.val
          (r.val + 1) (by omega) (by have := r.isLt; dsimp [N]; omega) p hp)
  have hnorm : (∀ i, eLpNorm (fun X => ∑ a,
      GoodBlocks.particleHessian (ofLong β s) N i a X * compensationVector n m a)
      (ENNReal.ofReal p) ρ ≤ ENNReal.ofReal M) ∧
      eLpNorm (fun X => ∑ a, ∑ b, compensationVector n m a *
        GoodBlocks.particleHessian (ofLong β s) N a b X * compensationVector n m b)
        (ENNReal.ofReal p) ρ ≤ ENNReal.ofReal M := by
    constructor
    · intro i
      refine (eLpNorm_congr_ae (ae_of_all ρ (fun X =>
        particle_compensation_row β s n m i X))).le.trans ?_
      exact hcounts.1 i
    · refine (eLpNorm_congr_ae (ae_of_all ρ (fun X =>
        particle_compensation_scalar β s n m X))).le.trans ?_
      exact hcounts.2
  have hb (i : Fin (n : ℕ)) :
      eLpNorm (compensationB β s n m i) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal M := by
    let f := fun y => ∑ a, GoodBlocks.gapHessian s N (i.castAdd m).castSucc a y *
      compensationVector n m a
    have hf : Measurable f := Finset.measurable_sum _ fun a _ =>
      (GoodBlocks.measurable_gapHessian s N _ a).mul_const _
    have hj := conditional_gap_observable_eLpNorm_le β s n m hn θ ε f hf hp
    change eLpNorm (compensationB β s n m i) (ENNReal.ofReal p) μ ≤ _ at hj
    apply hj.trans
    have he : (fun X : Riesz1.Configuration N => f (WithLp.toLp 2 (gapVector X))) =
        (fun X => ∑ a, GoodBlocks.particleHessian (ofLong β s) N
          (i.castAdd m).castSucc a X * compensationVector n m a) := by
      funext X
      simp only [f, GoodBlocks.gapHessian_particle β]
    rw [he]
    exact hnorm.1 _
  have hc : eLpNorm (compensationC β s n m) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal M := by
    let f := fun y => ∑ a, ∑ b, compensationVector n m a *
      GoodBlocks.gapHessian s N a b y * compensationVector n m b
    have hf : Measurable f := Finset.measurable_sum _ fun a _ =>
      Finset.measurable_sum _ fun b _ =>
        ((GoodBlocks.measurable_gapHessian s N a b).const_mul _).mul_const _
    have hj := conditional_gap_observable_eLpNorm_le β s n m hn θ ε f hf hp
    change eLpNorm (compensationC β s n m) (ENNReal.ofReal p) μ ≤ _ at hj
    apply hj.trans
    have he : (fun X : Riesz1.Configuration N => f (WithLp.toLp 2 (gapVector X))) =
        (fun X => ∑ a, ∑ b, compensationVector n m a *
          GoodBlocks.particleHessian (ofLong β s) N a b X * compensationVector n m b) := by
      funext X
      simp only [f, GoodBlocks.gapHessian_particle β]
    rw [he]
    exact hnorm.2
  intro i
  apply (add_le_add (hb i) hc).trans_eq
  rw [← ENNReal.ofReal_add hM hM]
  congr 1
  dsimp [M]
  ring

/-- See the proof of Lemma 5.8 in the paper, the `Qᵢⱼ` size clause,
with the two literal boundary depths and the same moment degree. -/
theorem compensationQ_size_moments (s : Riesz1.RieszExponent)
    (βlo βhi ε Cθ : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi)
    (hε : 0 < ε) (hCθ : 1 ≤ Cθ) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n : ℕ+) (m : ℕ), 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ (p : ℝ), 1 ≤ p →
      let μ := (activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n hn θ ε false).comap
        ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
          EuclideanSpace ℝ (Fin (n : ℕ)))
      ∀ i j : Fin (n : ℕ),
        eLpNorm (compensationQ β s n m i j) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (C * p ^ ((s.val + 2) / s.val) *
          (min (i.val + 1) ((n : ℕ) - i.val) : ℕ) ^ (-s.val / 2) *
          (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) ^ (-s.val / 2)) := by
  obtain ⟨D, hD, hb⟩ := compensation_size_moments s βlo βhi ε Cθ hlo hle hε hCθ
  refine ⟨3 * D, by positivity, ?_⟩
  intro β hβ n m hper hn θ hcurv p hp
  dsimp only
  let μ := (activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n hn θ ε false).comap
    ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
      EuclideanSpace ℝ (Fin (n : ℕ)))
  let M := D * p ^ ((s.val + 2) / s.val) * ((n : ℝ) + m + 1) ^ (-s.val)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hB (i : Fin (n : ℕ)) :
      eLpNorm (compensationB β s n m i) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal M :=
    (le_self_add).trans (hb β hβ n m hper hn θ hcurv p hp i)
  have hC (i : Fin (n : ℕ)) :
      eLpNorm (compensationC β s n m) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal M :=
    (le_add_self).trans (hb β hβ n m hper hn θ hcurv p hp i)
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  intro i j
  have he : compensationQ β s n m i j =
      (-compensationB β s n m i - compensationB β s n m j) + compensationC β s n m := rfl
  rw [he]
  have hnorm : eLpNorm ((-compensationB β s n m i - compensationB β s n m j) +
      compensationC β s n m) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (3 * M) := by
    apply (eLpNorm_add_le hpE).trans
    apply (add_le_add (eLpNorm_sub_le hpE) le_rfl).trans
    rw [eLpNorm_neg]
    apply (add_le_add (add_le_add (hB i) (hB j)) (hC i)).trans_eq
    rw [← ENNReal.ofReal_add hM hM, ← ENNReal.ofReal_add (add_nonneg hM hM) hM]
    congr 1
    ring
  apply hnorm.trans
  apply ENNReal.ofReal_le_ofReal
  have hN : (0 : ℝ) < (n : ℝ) + m + 1 := by positivity
  have hdepth (k : Fin (n : ℕ)) :
      0 < ((min (k.val + 1) ((n : ℕ) - k.val) : ℕ) : ℝ) ∧
      ((min (k.val + 1) ((n : ℕ) - k.val) : ℕ) : ℝ) ≤ (n : ℝ) + m + 1 := by
    have hk := k.isLt
    constructor
    · exact_mod_cast (show 0 < min (k.val + 1) ((n : ℕ) - k.val) by omega)
    · exact_mod_cast (show min (k.val + 1) ((n : ℕ) - k.val) ≤ (n : ℕ) + m + 1 by omega)
  have hpow : ((n : ℝ) + m + 1) ^ (-s.val) ≤
      ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val / 2) *
      ((min (j.val + 1) ((n : ℕ) - j.val) : ℕ) : ℝ) ^ (-s.val / 2) := by
    have hhalf : ((n : ℝ) + m + 1) ^ (-s.val) =
        ((n : ℝ) + m + 1) ^ (-s.val / 2) * ((n : ℝ) + m + 1) ^ (-s.val / 2) := by
      rw [← Real.rpow_add hN]
      congr 1
      ring
    rw [hhalf]
    exact mul_le_mul
      (Real.rpow_le_rpow_of_nonpos (hdepth i).1 (hdepth i).2 (by linarith [s.property.1]))
      (Real.rpow_le_rpow_of_nonpos (hdepth j).1 (hdepth j).2 (by linarith [s.property.1]))
      (by positivity) (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hpow
    (by positivity : 0 ≤ 3 * D * p ^ ((s.val + 2) / s.val))
  simpa only [M, mul_assoc] using hmul

/-- The smallest exterior chart is a point law. The compensation coefficients
are therefore the Hessian contractions at that point. -/
theorem compensation_point (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (i : Fin (n : ℕ))
    (x : AffineSimplex.chartDomain n ((n + 0 : ℕ) + 1)) :
    compensationB β s n 0 i x =
      ∑ a, GoodBlocks.chartHessian s n 0 (i.castAdd 0).castSucc a (x.val, 0) *
        compensationVector n 0 a ∧
    compensationC β s n 0 x =
      ∑ a, ∑ b, compensationVector n 0 a *
        GoodBlocks.chartHessian s n 0 a b (x.val, 0) * compensationVector n 0 b := by
  unfold compensationB compensationC
  rw [ProperMarginalChart.conditionalMeasure_point]
  simp only [integral_dirac, and_self]

end Riesz2.ConditionalForces
