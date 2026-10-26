/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.IntervalCoefficients
public import Riesz2.DecayLong.GoodBlocksPart2
public import Riesz2.DecayLong.GoodBlocksPart3

/-!
# Physical coefficient measurability and interval moments

See Subsection 4.4 and Subsection 4.5 of the paper. These bridges connect the supported
physical coefficients to the particle interval estimates.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff ENNReal ProbabilityTheory

namespace Riesz2.DecayShort

/-- See Subsection 4.4 of the paper: the physical coefficient is the positive image
series at every point of its ambient carrier. -/
theorem intervalWeight_images (p : Parameters) (N : ℕ+)
    (t : Fin (N : ℕ) × Fin ((N : ℕ) / 2))
    (y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N}) :
    intervalWeight p N t y =
      (2 - if 2 * (t.2.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
        (p.val.2 * (p.val.2 + 1) *
          ∑' k : ℤ, |PhysicalEnergy.intervalLinear N t.1 (t.2.val + 1) y.val +
            k * (N : ℝ)| ^ (-p.val.2 - 2)) := by
  rw [intervalWeight, PhysicalEnergy.intervalCoefficient_images,
    PhysicalEnergy.intervalLinear_apply]

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 4.4 of the paper: integral formula in the exterior chart.
The image expression is used only under the supported physical law. Its
ordinary integral is the already proved finite conditional coefficient. -/
theorem conditionalIntervalWeight_images (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (t : Fin (n + m + 1) × Fin ((n + m + 1) / 2)) :
    conditionalIntervalWeight p n m hn σ x t =
      ∫ z : EuclideanSpace ℝ (Fin m),
        (2 - if 2 * (t.2.val + 1) = n + m + 1 then (1 : ℝ) else 0) *
          (p.val.2 * (p.val.2 + 1) * ∑' k : ℤ,
            |PhysicalEnergy.intervalLinear (n + m).succPNat t.1 (t.2.val + 1)
              (RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ (x.val,z)) +
              k * ((n + m + 1 : ℕ) : ℝ)| ^ (-p.val.2 - 2))
        ∂ProperMarginalChart.conditionalMeasure p n m hn σ x := by
  rw [← PhysicalFibres.map_measure p n m hn σ x,
    (MeasurableEmbedding.subtype_coe (AffineSimplex.isOpen_chartDomain _ _).measurableSet).integral_map]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => intervalWeight_images p (n + m).succPNat t
    (PhysicalFibres.configuration n m σ x z)

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 4.4 of the paper: measurability of the actual conditional interval
coefficient as a function of the retained point. -/
theorem measurable_conditionalIntervalWeight (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    (t : Fin (n + m + 1) × Fin ((n + m + 1) / 2)) :
    Measurable (fun x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) =>
      conditionalIntervalWeight p n m hn σ x t) := by
  let f := fun q : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) ×
      EuclideanSpace ℝ (Fin m) =>
    (2 - if 2 * (t.2.val + 1) = n + m + 1 then (1 : ℝ) else 0) *
      (p.val.2 * (p.val.2 + 1) * ∑' k : ℤ,
        |PhysicalEnergy.intervalLinear (n + m).succPNat t.1 (t.2.val + 1)
          (RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ (q.1.val,q.2)) +
          k * ((n + m + 1 : ℕ) : ℝ)| ^ (-p.val.2 - 2))
  have hf : Measurable f := by
    apply Measurable.const_mul
    apply Measurable.const_mul
    apply Measurable.tsum
    intro k
    exact (((PhysicalEnergy.intervalLinear (n + m).succPNat t.1 (t.2.val + 1)).continuous.measurable.comp
      ((RetainedSimplex.continuous_chart n m _ σ).measurable.comp
        ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd))).add_const _).abs.pow_const _
  have he := (hf.stronglyMeasurable.integral_kernel_prod_right'
    (κ := ProperMarginalChart.conditionalKernel p n m hn σ)).measurable
  convert he using 1
  funext x
  exact conditionalIntervalWeight_images p n m hn σ x t

/-- See Subsection 4.5 of the paper: particle evaluation of the supported physical
coefficient agrees with the interval coefficient, including the
even antipodal weight. -/
theorem intervalWeight_gapVector (p : Parameters) (N : ℕ+)
    (t : Fin (N : ℕ) × Fin ((N : ℕ) / 2)) (X : Riesz1.Configuration N) :
    intervalWeight p N t ⟨WithLp.toLp 2 (gapVector X),
      GapChart.gapVector_mem_gapAmbientDomain X⟩ =
      GoodBlocks.particleCoefficient p N t.1.val (t.2.val + 1)
        (by omega) (by have := t.2.isLt; omega) X := by
  rw [GoodBlocks.particleCoefficient_gapVector]
  rfl

/-- See Subsection 4.5 of the paper, interval input under the upper active tilt.
The prefactor is uniform on compact temperature intervals and the degree
`(s+2)/s` precedes every volume and norm exponent. This is a bridge to the
estimate, with the physical coefficient on the left. -/
theorem upperTilt_interval_moments (s βlo βhi h Cθ : ℝ) (hs : 1 < s)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (hh : 0 < h) (hCθ : 1 ≤ Cθ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (N n : ℕ+), 2 ≤ (N : ℕ) →
      ∀ (hn : (n : ℕ) ≤ (N : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ (t : Fin (N : ℕ) × Fin ((N : ℕ) / 2)) (q : ℝ), 1 ≤ q →
        eLpNorm (fun X : Riesz1.Configuration N => intervalWeight p N t
          ⟨WithLp.toLp 2 (gapVector X), GapChart.gapVector_mem_gapAmbientDomain X⟩)
          (ENNReal.ofReal q) (tiltedParticleMeasure p N n hn θ h false) ≤
            ENNReal.ofReal (C * q ^ ((s + 2) / s) * (t.2.val + 1 : ℝ) ^ (-s - 2)) := by
  obtain ⟨C, hC, hb⟩ := GoodBlocks.tilted_coefficient_moments s βlo βhi h Cθ
    (by linarith) hlo hle hh hCθ
  refine ⟨C, hC, fun p hp hpl hph N n hN hn θ hcurv t q hq => ?_⟩
  simp_rw [intervalWeight_gapVector]
  simpa only [Nat.cast_add, Nat.cast_one] using
    hb p hp hpl hph N n hN hn θ hcurv t.1.val (t.2.val + 1)
      (by omega) (by have := t.2.isLt; omega) q hq

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 4.5 of the paper, conditional interval input under the upper
active tilt. Conditional Jensen is applied to the actual disintegration,
so the bound holds under the retained marginal. -/
theorem upperTilt_conditional_interval_moments (s βlo βhi h Cθ : ℝ) (hs : 1 < s)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (hh : 0 < h) (hCθ : 1 ≤ Cθ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (n : ℕ+) (m : ℕ)
      (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ (t : Fin ((n : ℕ) + m + 1) × Fin (((n : ℕ) + m + 1) / 2)) (q : ℝ), 1 ≤ q →
        eLpNorm (fun x => conditionalIntervalWeight p n m n.pos (Equiv.refl _) x t)
          (ENNReal.ofReal q)
          ((activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ h false).comap
            ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
              EuclideanSpace ℝ (Fin (n : ℕ)))) ≤
            ENNReal.ofReal (C * q ^ ((s + 2) / s) * (t.2.val + 1 : ℝ) ^ (-s - 2)) := by
  obtain ⟨C, hC, hb⟩ := GoodBlocks.tilted_coefficient_moments s βlo βhi h Cθ
    (by linarith) hlo hle hh hCθ
  refine ⟨C, hC, fun p hp hpl hph n m hn θ hcurv t q hq => ?_⟩
  let μ := (activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ h false).comap
    ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
  let K := ProperMarginalChart.conditionalKernel p n m n.pos (Equiv.refl _)
  let f := fun w : EuclideanSpace ℝ (Fin (n : ℕ)) × EuclideanSpace ℝ (Fin m) =>
    (2 - if 2 * (t.2.val + 1) = (n : ℕ) + m + 1 then (1 : ℝ) else 0) *
      (p.val.2 * (p.val.2 + 1) * ∑' k : ℤ,
        |PhysicalEnergy.intervalLinear ((n : ℕ) + m).succPNat t.1 (t.2.val + 1)
          (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) w) +
          k * (((n : ℕ) + m + 1 : ℕ) : ℝ)| ^ (-p.val.2 - 2))
  have hf : Measurable f := by
    apply Measurable.const_mul
    apply Measurable.const_mul
    apply Measurable.tsum
    intro k
    exact (((PhysicalEnergy.intervalLinear ((n : ℕ) + m).succPNat t.1 (t.2.val + 1)).continuous.measurable.comp
      (RetainedSimplex.continuous_chart n m _ (Equiv.refl _)).measurable).add_const _).abs.pow_const _
  let inc := fun w : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) ×
    EuclideanSpace ℝ (Fin m) => (w.1.val,w.2)
  have hi : Measurable inc :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  let : IsProbabilityMeasure μ := GoodBlocks.proper_active_probability p n m hn θ h
  have hJ := GoodBlocks.proper_disintegration p n m hn θ h
  change _ = (μ ⊗ₘ K).map inc at hJ
  have hc : Measurable (fun X : Riesz1.Configuration ((n : ℕ) + m).succPNat =>
      RetainedSimplex.coordinates n m (Equiv.refl _) (WithLp.toLp 2 (gapVector X))) :=
    (RetainedSimplex.continuous_coordinates n m (Equiv.refl _)).measurable.comp
      ((PiLp.volume_preserving_toLp _).measurable.comp (Riesz1.measurable_gapVector _))
  have htN : t.2.val + 1 ≤ (((n : ℕ) + m).succPNat : ℕ) / 2 := by
    simpa only [Nat.succPNat_coe, Nat.succ_eq_add_one] using Nat.succ_le_of_lt t.2.isLt
  have hnorm : eLpNorm (f ∘ inc) (ENNReal.ofReal q) (μ ⊗ₘ K) =
      eLpNorm (GoodBlocks.particleCoefficient p ((n : ℕ) + m).succPNat t.1.val
        (t.2.val + 1) (by omega) htN) (ENNReal.ofReal q)
        (tiltedParticleMeasure p ((n : ℕ) + m).succPNat n hn θ h false) := by
    rw [← eLpNorm_map_measure hf.aestronglyMeasurable hi.aemeasurable, ← hJ,
      eLpNorm_map_measure hf.aestronglyMeasurable hc.aemeasurable]
    apply eLpNorm_congr_ae
    apply ae_of_all
    intro X
    dsimp only [Function.comp_def, f]
    rw [GoodBlocks.retained_chart_gapVector, PhysicalEnergy.intervalLinear_apply,
      GapChart.cyclicGapSum_gapVector, GoodBlocks.particleCoefficient_images]
    simp only [Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add]
  have hj := eLpNorm_integral_kernel_le μ K (hf.comp hi) hq
  have he : (fun x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) =>
      ∫ z, (f ∘ inc) (x,z) ∂K x) =
      fun x => conditionalIntervalWeight p n m n.pos (Equiv.refl _) x t := by
    funext x
    exact (conditionalIntervalWeight_images p n m n.pos (Equiv.refl _) x t).symm
  rw [he, hnorm] at hj
  apply hj.trans
  simpa only [Nat.cast_add, Nat.cast_one] using
    hb p hp hpl hph ((n : ℕ) + m).succPNat n
      (by simp only [Nat.succPNat_coe]; have := n.pos; omega) hn θ hcurv t.1.val
      (t.2.val + 1) (by omega) htN q hq

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 4.4 of the paper: all boundary coefficients are measurable
functions of the retained point, with no exceptional-point choice. -/
theorem measurable_physical_boundary_coefficients (p : Parameters) (n m : ℕ)
    (hn : 1 ≤ n) (hsize : n ≤ n + m + 1) :
    (∀ k, Measurable (fun x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) =>
      IntervalBoundary.prefixCoefficient (n + m).succPNat n hsize
        (conditionalIntervalWeight p n m hn (Equiv.refl _) x) k)) ∧
    (∀ k, Measurable (fun x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) =>
      IntervalBoundary.suffixCoefficient (n + m).succPNat n hsize
        (conditionalIntervalWeight p n m hn (Equiv.refl _) x) k)) ∧
    Measurable (fun x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) =>
      IntervalBoundary.fullCoefficient (n + m).succPNat n hsize
        (conditionalIntervalWeight p n m hn (Equiv.refl _) x)) := by
  classical
  refine ⟨fun k => ?_, fun k => ?_, ?_⟩
  all_goals
    apply Finset.measurable_sum
    intro t _
    split_ifs <;> first
      | exact measurable_conditionalIntervalWeight p n m hn (Equiv.refl _) t
      | exact measurable_const

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 4.5 of the paper, the sharp `P` entry profile under the upper
active tilt. This uses the physical finite conditional coefficients and
the ambient cyclic distance, including the diagonal and one-gap block. -/
theorem upperTilt_conditional_P_moments (s βlo βhi h Cθ : ℝ) (hs : 1 < s)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (hh : 0 < h) (hCθ : 1 ≤ Cθ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (n : ℕ+) (m : ℕ)
      (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ (i j : Fin (n : ℕ)) (q : ℝ), 1 ≤ q →
        eLpNorm (fun x => IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat n hn
          (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x) i j)
          (ENNReal.ofReal q)
          ((activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ h false).comap
            ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
              EuclideanSpace ℝ (Fin (n : ℕ)))) ≤
            ENNReal.ofReal (C * q ^ ((s + 2) / s) *
              (1 + (Riesz1.cyclicIndexDistance ((n : ℕ) + m).succPNat
                (Fin.castLE hn i) (Fin.castLE hn j) : ℝ)) ^ (-s)) := by
  obtain ⟨C, hC, hb⟩ := upperTilt_conditional_interval_moments s βlo βhi h Cθ hs hlo hle hh hCθ
  have hs0 : 0 < s := by linarith
  refine ⟨C * (1 + 1 / s), mul_pos hC (by positivity), ?_⟩
  intro p hp hpl hph n m hn θ hcurv i j q hq
  let μ := (activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ h false).comap
    ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
  let A := fun a r x => conditionalIntervalWeight p n m n.pos (Equiv.refl _) x (a,r)
  have hcoeff (a : Fin ((n : ℕ) + m + 1)) (r : Fin (((n : ℕ) + m + 1) / 2)) :
      eLpNorm (A a r) (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal ((C * q ^ ((s + 2) / s)) * (r.val + 1 : ℝ) ^ (-s - 2)) :=
    hb p hp hpl hph n m hn θ hcurv (a,r) q hq
  have hnorm := interval_matrix_eLpNorm_le μ ((n : ℕ) + m).succPNat
    (by linarith : 0 < s) hq (by positivity : 0 ≤ C * q ^ ((s + 2) / s))
    A hcoeff (Fin.castLE hn i) (Fin.castLE hn j)
  have he : (fun x => IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat n hn
      (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x) i j) =
      fun x => ∑ r : Fin (((n : ℕ) + m + 1) / 2), ∑ a : Fin ((n : ℕ) + m + 1),
        if Fin.castLE hn i ∈ cyclicIndexInterval ((n : ℕ) + m).succPNat a (r.val + 1) ∧
          Fin.castLE hn j ∈ cyclicIndexInterval ((n : ℕ) + m).succPNat a (r.val + 1)
        then A a r x else 0 := by
    classical
    funext x
    rw [IntervalBoundary.intervalMatrix, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro a _
    dsimp only [IntervalBoundary.rankOne, IntervalBoundary.trace, A]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hi : Fin.castLE hn i ∈ cyclicIndexInterval ((n : ℕ) + m).succPNat a (r.val + 1) <;>
      by_cases hj : Fin.castLE hn j ∈ cyclicIndexInterval ((n : ℕ) + m).succPNat a (r.val + 1) <;>
      simp only [hi, hj, and_self, and_false, false_and, ↓reduceIte, mul_one, mul_zero]
  rw [he]
  refine hnorm.trans_eq ?_
  congr 1
  ring

end Riesz2.DecayShort
