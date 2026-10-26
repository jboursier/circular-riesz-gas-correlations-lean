/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.ConditionalEnergyMomentsPart3
public import Riesz2.DecayShort.LocalLawPart4

/-!
# Physical exterior fibres

The positive exterior chart is used as the carrier, so every evaluation of the
physical energy or of an interval coefficient is at an actual positive
mass configuration. Restriction to this carrier preserves the physical
conditional probability. These are interfaces for Lemma 4.7 and
the pointwise finiteness clause of Subsection 4.5.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ContDiff

namespace Riesz2.DecayShort.PhysicalFibres

/-- The full configuration reconstructed from a positive physical exterior fibre.
This map uses the retained chart and the ambient energy domain. -/
def configuration (n m : ℕ) (σ : Equiv.Perm (Fin (n + m + 1)))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (z : AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ i, x.val i)) :
    {y : EuclideanSpace ℝ (Fin (n + m + 1)) // y ∈ gapAmbientDomain (n + m).succPNat} :=
  ⟨RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ (x.val, z.val),
    ProperMarginalChart.simplex_ambient _
      ((RetainedSimplex.chart_mem_simplex n m _ σ _).mpr
        ((Set.ext_iff.mp (RetainedSimplex.fibre_domain n m _ x.property) z.val).mpr z.property))⟩

/-- The physical conditional probability on its positive exterior carrier.
It is the pullback of the law along the subtype inclusion. -/
def measure (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    Measure (AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ i, x.val i)) :=
  (ProperMarginalChart.conditionalMeasure p n m hn σ x).comap Subtype.val

/-- Restricting the conditional law to its positive carrier loses no mass. -/
theorem map_measure (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    (measure p n m hn σ x).map Subtype.val =
      ProperMarginalChart.conditionalMeasure p n m hn σ x := by
  rw [measure, map_comap_subtype_coe (AffineSimplex.isOpen_chartDomain _ _).measurableSet]
  exact Measure.restrict_eq_self_of_ae_mem
    (ConditionalEnergyMoments.physical_conditional_support p n m hn σ x)

/-- The supported physical fibre is a probability at every interior retained point. -/
theorem measure_probability (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    IsProbabilityMeasure (measure p n m hn σ x) := by
  let := ProperMarginalChart.conditionalMeasure_probability p n m hn σ x
  apply (MeasurableEmbedding.subtype_coe
    (AffineSimplex.isOpen_chartDomain _ _).measurableSet).isProbabilityMeasure_comap
  simpa only [Subtype.range_coe] using
    ConditionalEnergyMoments.physical_conditional_support p n m hn σ x

/-- The reconstruction is continuous on the entire positive fibre. -/
theorem continuous_configuration (n m : ℕ) (σ : Equiv.Perm (Fin (n + m + 1)))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    Continuous (configuration n m σ x) := by
  apply Continuous.subtype_mk
  exact (RetainedSimplex.continuous_chart n m _ σ).comp
    (continuous_const.prodMk continuous_subtype_val)

set_option backward.isDefEq.respectTransparency false in
/-- All full coordinates of a reconstructed exterior point form a positive mass
configuration, including every active coordinate. -/
theorem configuration_mem_simplex (n m : ℕ) (σ : Equiv.Perm (Fin (n + m + 1)))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (z : AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ i, x.val i)) :
    WithLp.ofLp (configuration n m σ x z).val ∈ Riesz1.gapSimplex (n + m).succPNat := by
  have hs := (RetainedSimplex.chart_mem_simplex n m _ σ _).mpr
    ((Set.ext_iff.mp (RetainedSimplex.fibre_domain n m _ x.property) z.val).mpr z.property)
  refine ⟨hs.1, ?_⟩
  simpa only [configuration, Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add] using hs.2

/-- See Subsection 4.5 of the paper, pointwise inverse moments needed for the interval
coefficients. These are Bochner integrability assertions at every
retained point, obtained from the physical conditional energy moments. -/
theorem integrable_coordinate_inverse (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (a : Fin (n + m + 1)) :
    Integrable (fun z => ((configuration n m σ x z).val a) ^ (-p.val.2 - 2))
      (measure p n m hn σ x) := by
  classical
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ (fun i : Fin n => x.val i)
    Finset.univ_nonempty
  let δ := min (x.val i) (((n + m : ℕ) + 1) - ∑ j, x.val j)
  have hδ : 0 < δ := lt_min (x.property.1 i) (sub_pos.mpr x.property.2)
  obtain ⟨W, _, _, C, _, hmom⟩ :=
    ConditionalEnergyMoments.physical_conditional_moments p n m hn
  obtain ⟨z₀, _, _, _, _, hm⟩ := hmom σ x
  have hg := ((hm δ hδ (fun j => (min_le_left _ _).trans
    (hi j (Finset.mem_univ j))) (min_le_right _ _)).2 a).1
  rw [← map_measure p n m hn σ x] at hg
  have he := hg.comp_measurable
    (show Measurable (Subtype.val : AffineSimplex.chartDomain m
      (((n + m : ℕ) + 1) - ∑ i, x.val i) → EuclideanSpace ℝ (Fin m)) from measurable_subtype_coe)
  exact he

set_option backward.isDefEq.respectTransparency false in
/-- See Lemma 4.7 of the paper, upper-only curvature and C² regularity clauses.
For the actual marginal potential divided by inverse temperature the bound
is `n^(-(s+2)h)`, so `A = 1` and `q₀ = s+2`, independent of `h`. -/
theorem upper_marginal_curvature (p : Parameters) (hs : 1 < p.val.2)
    (n m : ℕ) (hn : 1 ≤ n) (θ : PhysicalCutoff) (h : ℝ) (hh : 0 < h) :
    let R : {R : ℝ // 0 < R} := ⟨(n : ℝ) ^ h, Real.rpow_pos_of_pos (by exact_mod_cast hn) h⟩
    let J := Finset.univ.image (fun i : Fin n => (i.castAdd m).castSucc)
    let D := ProperMarginalChart.penalizedChartDensity p n m (Equiv.refl _) θ R.val⁻¹ J false
    let K := fun x => p.val.1⁻¹ * (-Real.log (AffineFibre.fibreMass volume D x).toReal)
    ContDiffOn ℝ 2 K (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) ∧
      ∀ x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
        ∀ v : EuclideanSpace ℝ (Fin n),
          (n : ℝ) ^ (-(p.val.2 + 2) * h) * ‖v‖ ^ 2 ≤
            fderiv ℝ (fderiv ℝ K) x v v := by
  intro R J D K
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  have hR : 1 ≤ (R : ℝ) := Real.one_le_rpow hnR hh.le
  obtain ⟨hV, hH⟩ := upperTilt_marginal_hessian p hs n m hn (Equiv.refl _) θ R hR
  refine ⟨contDiffOn_const.mul hV, fun x hx v => ?_⟩
  have hVx : ContDiffAt ℝ 2 (fun x => -Real.log (AffineFibre.fibreMass volume D x).toReal) x :=
    hV.contDiffAt ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds hx)
  rw [PhysicalCollision.internal_hessian_const_mul hVx]
  have ht := mul_le_mul_of_nonneg_left (hH x hx v) (inv_nonneg.mpr p.property.1.le)
  have he : p.val.1⁻¹ * (p.val.1 * R.val ^ (-p.val.2 - 2) * ‖v‖ ^ 2) =
      (n : ℝ) ^ (-(p.val.2 + 2) * h) * ‖v‖ ^ 2 := by
    rw [← mul_assoc, inv_mul_cancel_left₀ p.property.1.ne']
    dsimp only [R]
    rw [← Real.rpow_mul hnpos.le]
    congr 2
    ring
  exact he ▸ ht

end Riesz2.DecayShort.PhysicalFibres
