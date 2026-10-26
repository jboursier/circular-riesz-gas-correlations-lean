/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.GoodBlocksPart2
public import Riesz2.HelfferSjostrand.ConditionalEnergyMomentsPart3
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Riesz2.ToMathlib.KernelLpContraction

/-!
# Proper-window physical conditional Hessians

See Subsection 5.1 of the paper. The differential expressions use the
existing real representative of the long-range kernel. Physical evaluations
are on the positive simplex. The conditional laws are the pointwise
physical laws, including zero-dimensional exterior charts.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology ContDiff ProbabilityTheory

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.GoodBlocks

/-- The ordinary second-derivative expression for the ambient interval matrix.
On the physical simplex this is the ambient Hessian of Subsection 5.1, as shown
by `gapHessian_particle` and `particleHessian_eq_second`. -/
def gapHessian (s : Riesz1.RieszExponent) (N : ℕ+) (a b : Fin (N : ℕ))
    (y : EuclideanSpace ℝ (Fin (N : ℕ))) : ℝ :=
  ∑ r : Fin ((N : ℕ) / 2), ∑ i : Fin (N : ℕ),
    if a ∈ cyclicIndexInterval N i (r.val + 1) ∧
      b ∈ cyclicIndexInterval N i (r.val + 1) then
      (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
        ((N : ℝ) ^ (-s.val - 2) * iteratedDeriv 2 (fun t : ℝ => Riesz1.rieszRepresentative s t)
          (cyclicGapSum N i (r.val + 1) (WithLp.ofLp y) / (N : ℝ)))
    else 0

theorem measurable_gapHessian (s : Riesz1.RieszExponent) (N : ℕ+)
    (a b : Fin (N : ℕ)) : Measurable (gapHessian s N a b) := by
  classical
  apply Finset.measurable_sum
  intro r _
  apply Finset.measurable_sum
  intro i _
  by_cases h : a ∈ cyclicIndexInterval N i (r.val + 1) ∧ b ∈ cyclicIndexInterval N i (r.val + 1)
  · simp only [h, and_self, ↓reduceIte]
    apply Measurable.const_mul
    apply Measurable.const_mul
    simp only [iteratedDeriv_succ, iteratedDeriv_zero]
    apply (measurable_deriv (deriv (fun t : ℝ => Riesz1.rieszRepresentative s t))).comp
    simpa only [PhysicalEnergy.intervalLinear_apply] using
      ((PhysicalEnergy.intervalLinear N i (r.val + 1)).continuous.div_const (N : ℝ)).measurable
  · simp only [h, ↓reduceIte]
    exact measurable_const

/-- Identification with the particle Hessian, including the antipodal
multiplicity and the two-particle case. -/
theorem gapHessian_particle (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (a b : Fin (N : ℕ)) (X : Riesz1.Configuration N) :
    gapHessian s N a b (WithLp.toLp 2 (gapVector X)) =
      particleHessian (ofLong β s) N a b X := by
  classical
  unfold gapHessian particleHessian
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : a ∈ cyclicIndexInterval N i (r.val + 1) ∧ b ∈ cyclicIndexInterval N i (r.val + 1)
  · simp only [h, and_self, ↓reduceIte]
    rw [particleCoefficient_gapVector]
    simp only [PhysicalEnergy.intervalCoefficient, PhysicalEnergy.kernelDerivative,
      ofLong, s.property.2, ↓reduceDIte,
      PhysicalEnergy.scaledSeparation, PNat.val_ofNat]
  · simp only [h, ↓reduceIte]

/-- On every positive mass simplex the differential expression is the
energy interval coefficient sum. -/
theorem gapHessian_simplex (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (a b : Fin (N : ℕ))
    (y : EuclideanSpace ℝ (Fin (N : ℕ)))
    (hy : WithLp.ofLp y ∈ Riesz1.gapSimplex N) :
    gapHessian s N a b y =
      ∑ r : Fin ((N : ℕ) / 2), ∑ i : Fin (N : ℕ),
        if a ∈ cyclicIndexInterval N i (r.val + 1) ∧
          b ∈ cyclicIndexInterval N i (r.val + 1) then
          (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
            PhysicalEnergy.intervalCoefficient (ofLong β s) N
              ⟨cyclicGapSum N i (r.val + 1) (WithLp.ofLp y),
                PhysicalEnergy.gapSum_mem N i (by omega)
                  (lt_of_le_of_lt (Nat.succ_le_of_lt r.isLt) (Nat.div_lt_self N.pos (by norm_num))) _ hy⟩
        else 0 := by
  simp only [gapHessian, PhysicalEnergy.intervalCoefficient,
    PhysicalEnergy.kernelDerivative, ofLong,
    s.property.2, ↓reduceDIte, PhysicalEnergy.scaledSeparation, PNat.val_ofNat]

theorem gapHessian_nonneg (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (a b : Fin (N : ℕ))
    (y : EuclideanSpace ℝ (Fin (N : ℕ)))
    (hy : WithLp.ofLp y ∈ Riesz1.gapSimplex N) :
    0 ≤ gapHessian s N a b y := by
  rw [gapHessian_simplex β s N a b y hy]
  apply Finset.sum_nonneg
  intro r _
  apply Finset.sum_nonneg
  intro i _
  by_cases h : a ∈ cyclicIndexInterval N i (r.val + 1) ∧ b ∈ cyclicIndexInterval N i (r.val + 1)
  · simp only [h, and_self, ↓reduceIte]
    exact mul_nonneg (by split_ifs <;> norm_num)
      (PhysicalEnergy.intervalCoefficient_pos _ _ _).le
  · simp only [h, ↓reduceIte, le_refl]

/-- A deterministic domination used for pointwise conditional integrability
in Subsection 5.1. Its constant may depend on the fixed total size. -/
theorem gapHessian_inverse_bound (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) :
    ∃ C : ℝ, 0 < C ∧ ∀ a b (y : EuclideanSpace ℝ (Fin (N : ℕ))),
      WithLp.ofLp y ∈ Riesz1.gapSimplex N →
      ‖gapHessian s N a b y‖ ≤ C * ∑ j, (y j) ^ (-s.val - 2) := by
  classical
  let K := PhysicalEnergy.coefficientConstant s.val s.property.1
  have hK : 0 < K := PhysicalEnergy.coefficientConstant_pos _ _
  refine ⟨2 * K * (N : ℝ) * ((N : ℕ) / 2 : ℕ) + 1, by positivity, ?_⟩
  intro a b y hy
  obtain ⟨j, hj⟩ := ElementaryBarriers.exists_iInf_eq_apply (fun j : Fin (N : ℕ) => y j)
  let δ : ℝ := ⨅ j : Fin (N : ℕ), y j
  have hδ : 0 < δ := by rw [show δ = y j from hj]; exact hy.1 j
  have hδy (i : Fin (N : ℕ)) : δ ≤ y i := ciInf_le (Finite.bddBelow_range _) i
  have hs : 0 ≤ ∑ j, (y j) ^ (-s.val - 2) :=
    Finset.sum_nonneg fun j _ => Real.rpow_nonneg (hy.1 j).le _
  have hδsum : δ ^ (-s.val - 2) ≤ ∑ j, (y j) ^ (-s.val - 2) := by
    rw [show δ = y j from hj]
    exact Finset.single_le_sum (fun i _ => Real.rpow_nonneg (hy.1 i).le _)
      (Finset.mem_univ j)
  rw [Real.norm_of_nonneg (gapHessian_nonneg β s N a b y hy),
    gapHessian_simplex β s N a b y hy]
  have hentry (r : Fin ((N : ℕ) / 2)) (i : Fin (N : ℕ)) :
      PhysicalEnergy.intervalCoefficient (ofLong β s) N
        ⟨cyclicGapSum N i (r.val + 1) (WithLp.ofLp y),
          PhysicalEnergy.gapSum_mem N i (by omega)
            (lt_of_le_of_lt (Nat.succ_le_of_lt r.isLt) (Nat.div_lt_self N.pos (by norm_num))) _ hy⟩ ≤
        K * ∑ j, (y j) ^ (-s.val - 2) := by
    have h := (PhysicalEnergy.coefficient_gap_bounds (ofLong β s) N i
      (r := r.val + 1) (by omega) (Nat.succ_le_of_lt r.isLt) _ hy hδ
      (b := (N : ℝ)) (fun i => ⟨hδy i, by
        have hh := Finset.single_le_sum (fun j _ => (hy.1 j).le) (Finset.mem_univ i)
        rwa [hy.2] at hh⟩)).2
    change _ ≤ K * δ ^ (-s.val - 2) * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2) at h
    have hp : ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (show 1 ≤ r.val + 1 by omega))
        (by linarith [s.property.1])
    exact h.trans ((mul_le_of_le_one_right (by positivity) hp).trans
      (mul_le_mul_of_nonneg_left hδsum hK.le))
  calc
    _ ≤ ∑ _r : Fin ((N : ℕ) / 2), ∑ _i : Fin (N : ℕ),
        2 * K * ∑ j, (y j) ^ (-s.val - 2) := by
      apply Finset.sum_le_sum
      intro r _
      apply Finset.sum_le_sum
      intro i _
      by_cases h : a ∈ cyclicIndexInterval N i (r.val + 1) ∧ b ∈ cyclicIndexInterval N i (r.val + 1)
      · simp only [h, and_self, ↓reduceIte]
        have hm : (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) ≤ 2 := by
          split_ifs <;> norm_num
        have hc := (PhysicalEnergy.intervalCoefficient_pos (ofLong β s) N
          ⟨cyclicGapSum N i (r.val + 1) (WithLp.ofLp y), PhysicalEnergy.gapSum_mem N i (by omega)
            (lt_of_le_of_lt (Nat.succ_le_of_lt r.isLt) (Nat.div_lt_self N.pos (by norm_num))) _ hy⟩).le
        nlinarith [hentry r i]
      · simp only [h, ↓reduceIte]
        positivity
    _ = (2 * K * (N : ℝ) * ((N : ℕ) / 2 : ℕ)) * ∑ j, (y j) ^ (-s.val - 2) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ ≤ _ := by nlinarith

/-- See Subsection 5.1 of the paper: identification on the entire physical simplex
with the ambient second derivative of the physical energy. -/
theorem gapHessian_eq_second (β : InverseTemperature) (s : Riesz1.RieszExponent) (N : ℕ+) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy (ofLong β s) N y) ∧
      ∀ (y : EuclideanSpace ℝ (Fin (N : ℕ))), WithLp.ofLp y ∈ Riesz1.gapSimplex N →
        ∀ a b : Fin (N : ℕ),
          fderiv ℝ (fderiv ℝ W) y (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) =
            gapHessian s N a b y := by
  classical
  obtain ⟨W, hW, hv, hjet⟩ := PhysicalEnergy.ambient_derivatives (ofLong β s) N
  refine ⟨W, hW, hv, fun y hy a b => ?_⟩
  rw [(hjet ⟨y, PhysicalEnergy.simplex_subset_ambient N _ hy⟩ _ _).2,
    gapHessian_simplex β s N a b y hy, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  have hsingle (a : Fin (N : ℕ)) : cyclicGapSum N i (r.val + 1)
      (WithLp.ofLp (EuclideanSpace.single a (1 : ℝ))) =
        if a ∈ cyclicIndexInterval N i (r.val + 1) then 1 else 0 := by
    convert cyclicGapSum_single N i a
      ((Nat.succ_le_of_lt r.isLt).trans (Nat.div_le_self _ _)) using 1
    congr 1
    ext j
    simp [EuclideanSpace.single, eq_comm]
  rw [hsingle a, hsingle b]
  by_cases ha : a ∈ cyclicIndexInterval N i (r.val + 1) <;>
    by_cases hb : b ∈ cyclicIndexInterval N i (r.val + 1) <;>
    simp only [ha, hb, and_self, and_false, false_and, ↓reduceIte, mul_one, mul_zero]

/-- The ambient entry in retained/exterior coordinates. -/
def chartHessian (s : Riesz1.RieszExponent) (n m : ℕ)
    (a b : Fin (n + m + 1))
    (q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) : ℝ :=
  gapHessian s (n + m).succPNat a b
    (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) q)

theorem measurable_chartHessian (s : Riesz1.RieszExponent) (n m : ℕ)
    (a b : Fin (n + m + 1)) : Measurable (chartHessian s n m a b) :=
  (measurable_gapHessian s (n + m).succPNat a b).comp
    (RetainedSimplex.continuous_chart n m _ (Equiv.refl _)).measurable

/-- See Subsection 5.1 of the paper: the singular ambient Hessian is integrable on
**every** interior physical fibre. This includes point fibres. -/
theorem integrable_chartHessian (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n m : ℕ) (hn : 1 ≤ n)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (a b : Fin (n + m + 1)) :
    Integrable (fun z => chartHessian s n m a b (x.val, z))
      (ProperMarginalChart.conditionalMeasure (ofLong β s) n m hn (Equiv.refl _) x) := by
  classical
  let ρ := ProperMarginalChart.conditionalMeasure (ofLong β s) n m hn (Equiv.refl _) x
  let c := fun z : EuclideanSpace ℝ (Fin m) =>
    RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val, z)
  obtain ⟨W, _, _, C₀, _, hm⟩ :=
    ConditionalEnergyMoments.physical_conditional_moments (ofLong β s) n m hn
  obtain ⟨_, _, _, _, _, hm⟩ := hm (Equiv.refl _) x
  have hL : 0 < ((n + m : ℕ) + 1 : ℝ) - ∑ i, x.val i := sub_pos.mpr x.property.2
  have hex : ∃ δ : ℝ, 0 < δ ∧ (∀ i, δ ≤ x.val i) ∧
      δ ≤ ((n + m : ℕ) + 1 : ℝ) - ∑ i, x.val i := by
    let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    obtain ⟨i, hi⟩ := ElementaryBarriers.exists_iInf_eq_apply (fun i : Fin n => x.val i)
    refine ⟨min (⨅ i : Fin n, x.val i) _, lt_min ?_ hL,
      fun j => (min_le_left _ _).trans (ciInf_le (Finite.bddBelow_range _) j), min_le_right _ _⟩
    rw [hi]
    exact x.property.1 i
  obtain ⟨δ, hδ, hδx, hδL⟩ := hex
  have hi (j : Fin (n + m + 1)) : Integrable (fun z => (c z j) ^ (-s.val - 2)) ρ :=
    ((hm δ hδ hδx hδL).2 j).1
  obtain ⟨C, _, hC⟩ := gapHessian_inverse_bound β s (n + m).succPNat
  have hmajor : Integrable (fun z => C * ∑ j, (c z j) ^ (-s.val - 2)) ρ :=
    (integrable_finsetSum _ (fun j _ => hi j)).const_mul C
  apply hmajor.mono' ((measurable_chartHessian s n m a b).comp
    measurable_prodMk_left).aestronglyMeasurable
  filter_upwards [ConditionalEnergyMoments.physical_conditional_support
    (ofLong β s) n m hn (Equiv.refl _) x] with z hz
  have hd := (Set.ext_iff.mp (RetainedSimplex.fibre_domain n m _ x.property) z).mpr hz
  have hy := (RetainedSimplex.chart_mem_simplex n m _ (Equiv.refl _) _).mpr hd
  apply hC a b (c z)
  exact ⟨hy.1, by simpa only [c, Nat.succPNat_coe, Nat.cast_succ] using hy.2⟩

/-- See Subsection 5.1 of the paper: the density-defined conditional ambient matrix
on its entire open carrier. The integrability certificate is
`integrable_chartHessian`. No almost-everywhere version is selected. -/
def conditionalHessian (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (a b : Fin (n : ℕ))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) : ℝ :=
  ∫ z, chartHessian s n m (a.castAdd m).castSucc (b.castAdd m).castSucc (x.val, z)
    ∂ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x

theorem measurable_conditionalHessian (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ) (a b : Fin (n : ℕ)) :
    Measurable (conditionalHessian β s n m a b) := by
  let f := fun q : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) ×
      EuclideanSpace ℝ (Fin m) =>
    chartHessian s n m (a.castAdd m).castSucc (b.castAdd m).castSucc (q.1.val, q.2)
  have hf : Measurable f := (measurable_chartHessian s n m _ _).comp
    ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
  exact (hf.stronglyMeasurable.integral_kernel_prod_right'
    (κ := ProperMarginalChart.conditionalKernel (ofLong β s) n m n.pos (Equiv.refl _))).measurable

/-- See Subsection 5.1 of the paper: the same conditional matrix is the integral
against the normalized **intrinsic exterior simplex volume**, including
its area factor. This is an equality at every interior retained point. -/
theorem conditionalHessian_exterior (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (a b : Fin (n : ℕ))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    let ρ := AffineFibre.normalizedMeasure
      (AffineSimplex.simplexVolume m (((n + m : ℕ) + 1) - ∑ i, x.val i))
      (fun y => ProperMarginalChart.density (ofLong β s) ((n : ℕ) + m)
        (RetainedSimplex.assemble n m (Equiv.refl _) x.val y))
      (ProperMarginalChart.exterior_mass_valid (ofLong β s) n m n.pos
        (Equiv.refl _) x.property).1
      (ProperMarginalChart.exterior_mass_valid (ofLong β s) n m n.pos
        (Equiv.refl _) x.property).2
    conditionalHessian β s n m a b x =
      ∫ y, gapHessian s ((n : ℕ) + m).succPNat (a.castAdd m).castSucc (b.castAdd m).castSucc
        (RetainedSimplex.assemble n m (Equiv.refl _) x.val y) ∂ρ := by
  dsimp only
  rw [ProperMarginalChart.conditionalMeasure_exterior (ofLong β s) n m n.pos (Equiv.refl _) x]
  have hf : Measurable (fun y => gapHessian s ((n : ℕ) + m).succPNat
      (a.castAdd m).castSucc (b.castAdd m).castSucc
        (RetainedSimplex.assemble n m (Equiv.refl _) x.val y)) :=
    (measurable_gapHessian s _ _ _).comp
      (RetainedSimplex.continuous_assemble n m (Equiv.refl _) x.val).measurable
  rw [integral_map (AffineSimplex.continuous_chart m _).measurable.aemeasurable
    hf.aestronglyMeasurable]
  simp only [RetainedSimplex.assemble_chart, conditionalHessian, chartHessian]

/-- See Subsection 5.1 of the paper: no negative entry is introduced by conditioning. -/
theorem conditionalHessian_nonneg (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (a b : Fin (n : ℕ))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    0 ≤ conditionalHessian β s n m a b x := by
  apply integral_nonneg_of_ae
  filter_upwards [ConditionalEnergyMoments.physical_conditional_support
    (ofLong β s) n m n.pos (Equiv.refl _) x] with z hz
  apply gapHessian_nonneg β s ((n : ℕ) + m).succPNat
  have hd := (Set.ext_iff.mp (RetainedSimplex.fibre_domain n m _ x.property) z).mpr hz
  have hy := (RetainedSimplex.chart_mem_simplex n m _ (Equiv.refl _) _).mpr hd
  exact ⟨hy.1, by simpa only [Nat.succPNat_coe, Nat.cast_succ] using hy.2⟩

/-- The smallest proper window has a point exterior law, and its matrix
is the actual ambient entry at that point. -/
theorem conditionalHessian_point (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (a b : Fin (n : ℕ))
    (x : AffineSimplex.chartDomain n ((n + 0 : ℕ) + 1)) :
    conditionalHessian β s n 0 a b x =
      chartHessian s n 0 (a.castAdd 0).castSucc (b.castAdd 0).castSucc (x.val, 0) := by
  unfold conditionalHessian
  rw [ProperMarginalChart.conditionalMeasure_point]
  exact integral_dirac _ _

/-- Every proper pair of source sizes is represented by exactly one exterior
free dimension. In particular the `n,m` interfaces omit no permitted `N,n`. -/
theorem proper_size_parametrization (N n : ℕ+) (hn : (n : ℕ) < (N : ℕ)) :
    ∃! m : ℕ, N = ((n : ℕ) + m).succPNat := by
  refine ⟨(N : ℕ) - (n : ℕ) - 1, ?_, ?_⟩
  · apply PNat.eq
    simp only [Nat.succPNat_coe]
    omega
  · intro m hm
    have he := congrArg PNat.val hm
    simp only [Nat.succPNat_coe] at he
    omega

/-- The actual marginal and its pointwise conditional kernel,
with all chart-volume and tilt-normalization factors cancelled. -/
theorem proper_disintegration (p : Parameters) (n : ℕ+) (m : ℕ)
    (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (θ : PhysicalCutoff) (ε : ℝ) :
    (tiltedParticleMeasure p ((n : ℕ) + m).succPNat n hn θ ε false).map
      (fun X : Riesz1.Configuration ((n : ℕ) + m).succPNat =>
        RetainedSimplex.coordinates n m (Equiv.refl _) (WithLp.toLp 2 (gapVector X))) =
      (((activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ ε false).comap
        ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
          EuclideanSpace ℝ (Fin (n : ℕ)))) ⊗ₘ
        ProperMarginalChart.conditionalKernel p n m n.pos (Equiv.refl _)).map
          (fun q => (q.1.val, q.2)) := by
  let K := ProperMarginalChart.conditionalKernel p n m n.pos (Equiv.refl _)
  let B := AffineSimplex.chartDomain n ((n + m : ℕ) + 1)
  let μ₀ : Measure B :=
    (tiltNormalizer p ((n : ℕ) + m).succPNat n hn θ ε false)⁻¹ •
      (partitionFunction p ((n : ℕ) + m).succPNat)⁻¹ •
        ENNReal.ofReal ((n + m + 1 : ℝ) ^ ((n : ℕ) + m))⁻¹ •
          (((volume : Measure (EuclideanSpace ℝ (Fin (n : ℕ)))).comap
            ((↑) : B → EuclideanSpace ℝ (Fin (n : ℕ)))).withDensity
              (fun x => AffineFibre.fibreMass volume
                (ProperMarginalChart.penalizedChartDensity p n m (Equiv.refl _) θ
                  ((n : ℝ) ^ (-ε)) (Finset.univ.map (Fin.castLEEmb hn)) false) x.val))
  have hj := ProperMarginalChart.tilted_coordinates_disintegration p n m n.pos
    (Equiv.refl _) n hn θ ε false (fun i hi => by
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
      exact ⟨j, Fin.ext rfl⟩)
  have hinc : Measurable (fun q : B × EuclideanSpace ℝ (Fin m) => (q.1.val, q.2)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  have hj' : (tiltedParticleMeasure p ((n : ℕ) + m).succPNat n hn θ ε false).map
      (fun X : Riesz1.Configuration ((n : ℕ) + m).succPNat =>
        RetainedSimplex.coordinates n m (Equiv.refl _) (WithLp.toLp 2 (gapVector X))) =
      (μ₀ ⊗ₘ K).map (fun q => (q.1.val, q.2)) := by
    simpa only [μ₀, Measure.compProd_smul_left,
      Measure.map_smul _ hinc.aemeasurable] using hj
  have hbase : activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ ε false =
      μ₀.map ((↑) : B → EuclideanSpace ℝ (Fin (n : ℕ))) := by
    have he := congrArg (Measure.map Prod.fst) hj'
    have hc : Measurable (fun X : Riesz1.Configuration ((n : ℕ) + m).succPNat =>
        RetainedSimplex.coordinates n m (Equiv.refl _) (WithLp.toLp 2 (gapVector X))) :=
      (RetainedSimplex.continuous_coordinates n m (Equiv.refl _)).measurable.comp
        ((PiLp.volume_preserving_toLp _).measurable.comp (Riesz1.measurable_gapVector _))
    rw [Measure.map_map measurable_fst hc, Measure.map_map measurable_fst hinc] at he
    have hcoords : (fun X : Riesz1.Configuration ((n : ℕ) + m).succPNat =>
        (RetainedSimplex.coordinates n m (Equiv.refl _) (WithLp.toLp 2 (gapVector X))).1) =
        fun X => WithLp.toLp 2 (finiteGapBlock X) := by
      funext X
      ext i
      rw [RetainedSimplex.coordinates_retained]
      rfl
    simp only [Function.comp_def] at he
    rw [hcoords] at he
    change activeTiltedGapLaw p _ n hn θ ε false = _ at he
    refine he.trans ?_
    change (μ₀ ⊗ₘ K).map (Subtype.val ∘ Prod.fst) = _
    rw [← Measure.map_map measurable_subtype_coe measurable_fst]
    change ((μ₀ ⊗ₘ K).fst).map _ = _
    rw [Measure.fst_compProd]
  rw [hbase, (MeasurableEmbedding.subtype_coe
    (AffineSimplex.isOpen_chartDomain n _).measurableSet).comap_map]
  exact hj'

/-- Reconstructing particle gaps in the retained chart changes no ambient
coordinate, including the dependent final exterior gap. -/
theorem retained_chart_gapVector (n : ℕ+) (m : ℕ)
    (X : Riesz1.Configuration ((n : ℕ) + m).succPNat) :
    RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _)
      (RetainedSimplex.coordinates n m (Equiv.refl _) (WithLp.toLp 2 (gapVector X))) =
        WithLp.toLp 2 (gapVector X) := by
  have hrefl (y : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1))) :
      LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.refl _) y = y := by
    ext i
    rfl
  simp only [RetainedSimplex.chart, RetainedSimplex.coordinates, Equiv.refl_symm,
    hrefl, LinearEquiv.apply_symm_apply]
  apply AffineSimplex.chart_coordinates
  have hs : WithLp.toLp 2 (gapVector X) ∈
      AffineSimplex.massSimplex ((n : ℕ) + m) ((n + m : ℕ) + 1) :=
    (GapChart.gapVector_eq_chart ((n : ℕ) + m) X).symm ▸
      (AffineSimplex.chart_mem_simplex_iff _ _ _).mpr (GapChart.gaps ((n : ℕ) + m) X).property
  exact hs.2

/-- The actual active law has mass one on its open carrier. -/
theorem proper_active_probability (p : Parameters) (n : ℕ+) (m : ℕ)
    (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (θ : PhysicalCutoff) (ε : ℝ) :
    IsProbabilityMeasure ((activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ ε false).comap
      ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
        EuclideanSpace ℝ (Fin (n : ℕ)))) := by
  have : IsProbabilityMeasure (tiltedParticleMeasure p ((n : ℕ) + m).succPNat n hn θ ε false) :=
    DefinitionSanity.tilted_probability _ _ _ _ _ _ _
  have : IsProbabilityMeasure (activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ ε false) :=
    DefinitionSanity.active_tilted_probability _ _ _ _ _ _ _
  have hc : Measurable (fun X : Riesz1.Configuration ((n : ℕ) + m).succPNat =>
      RetainedSimplex.coordinates n m (Equiv.refl _) (WithLp.toLp 2 (gapVector X))) :=
    (RetainedSimplex.continuous_coordinates n m (Equiv.refl _)).measurable.comp
      ((PiLp.volume_preserving_toLp _).measurable.comp (Riesz1.measurable_gapVector _))
  have hi : Measurable (fun q : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) ×
      EuclideanSpace ℝ (Fin m) => (q.1.val, q.2)) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  have hh := congrArg (fun μ => μ univ) (proper_disintegration p n m hn θ ε)
  simp only [Measure.map_apply hc MeasurableSet.univ,
    Measure.map_apply hi MeasurableSet.univ, preimage_univ, measure_univ,
    Measure.compProd_apply MeasurableSet.univ, measure_univ,
    lintegral_one] at hh
  exact ⟨hh.symm⟩

/-- Bridge from the retained chart to the `properMarginalDomain`. Rewriting by the domain equality transports
every conditional-matrix norm and event below to this carrier. The
law is the same `activeTiltedGapLaw` on both sides. -/
theorem proper_active_frozen_carrier (p : Parameters) (n : ℕ+) (m : ℕ)
    (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (θ : PhysicalCutoff) (ε : ℝ) :
    HEq ((activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ ε false).comap
      ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ))))
      ((activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ ε false).comap
        ((↑) : properMarginalDomain n ((n : ℕ) + m).succPNat → EuclideanSpace ℝ (Fin (n : ℕ)))) := by
  have he (S T : Set (EuclideanSpace ℝ (Fin (n : ℕ)))) (h : S = T) :
      HEq ((activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ ε false).comap
        ((↑) : S → EuclideanSpace ℝ (Fin (n : ℕ))))
        ((activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ ε false).comap
          ((↑) : T → EuclideanSpace ℝ (Fin (n : ℕ)))) := by
    subst T
    rfl
  exact he _ _ (ProperMarginalChart.baseDomain_eq_properMarginalDomain n m)

/-- See Subsection 5.1 of the paper, complete proper-window conditional Hessian
moment clause. The measure is exactly the active law, transported
only to its open carrier. The transport preserves the moment degree and spatial power. -/
theorem tilted_conditional_hessian_moments (s : Riesz1.RieszExponent)
    (βlo βhi ε Cθ : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi)
    (hε : 0 < ε) (hCθ : 1 ≤ Cθ) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n : ℕ+) (m : ℕ)
        (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (θ : PhysicalCutoff),
        (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
        ∀ (a b : Fin (n : ℕ)) (q : ℝ), 1 ≤ q →
          eLpNorm (conditionalHessian β s n m a b) (ENNReal.ofReal q)
            ((activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n hn θ ε false).comap
              ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
                EuclideanSpace ℝ (Fin (n : ℕ)))) ≤ ENNReal.ofReal
                  (C * q ^ ((s.val + 2) / s.val) *
                    (1 + (Riesz1.cyclicIndexDistance ((n : ℕ) + m).succPNat
                      (a.castAdd m).castSucc (b.castAdd m).castSucc : ℝ)) ^ (-s.val)) := by
  obtain ⟨C, hC, hmom⟩ := tilted_hessian_moments s.val βlo βhi ε Cθ
    s.property.1 hlo hle hε hCθ
  refine ⟨C, hC, fun β hβ n m hn θ hcurv a b q hq => ?_⟩
  let μ := (activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n hn θ ε false).comap
    ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
  let K := ProperMarginalChart.conditionalKernel (ofLong β s) n m n.pos (Equiv.refl _)
  let f := chartHessian s n m (a.castAdd m).castSucc (b.castAdd m).castSucc
  let inc := fun q : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) ×
      EuclideanSpace ℝ (Fin m) => (q.1.val, q.2)
  have hi : Measurable inc :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  have hf : Measurable f := measurable_chartHessian s n m _ _
  have : IsProbabilityMeasure μ := proper_active_probability _ _ _ _ _ _
  have hc : Measurable (fun X : Riesz1.Configuration ((n : ℕ) + m).succPNat =>
      RetainedSimplex.coordinates n m (Equiv.refl _) (WithLp.toLp 2 (gapVector X))) :=
    (RetainedSimplex.continuous_coordinates n m (Equiv.refl _)).measurable.comp
      ((PiLp.volume_preserving_toLp _).measurable.comp (Riesz1.measurable_gapVector _))
  have hJ := proper_disintegration (ofLong β s) n m hn θ ε
  change _ = (μ ⊗ₘ K).map inc at hJ
  have hnorm : eLpNorm (f ∘ inc) (ENNReal.ofReal q) (μ ⊗ₘ K) =
      eLpNorm (particleHessian (ofLong β s) ((n : ℕ) + m).succPNat
        (a.castAdd m).castSucc (b.castAdd m).castSucc) (ENNReal.ofReal q)
          (tiltedParticleMeasure (ofLong β s) ((n : ℕ) + m).succPNat n hn θ ε false) := by
    rw [← eLpNorm_map_measure hf.aestronglyMeasurable hi.aemeasurable, ← hJ,
      eLpNorm_map_measure hf.aestronglyMeasurable hc.aemeasurable]
    apply eLpNorm_congr_ae
    exact ae_of_all _ fun X => by
      dsimp only [f, Function.comp_def, chartHessian]
      rw [retained_chart_gapVector, gapHessian_particle]
  have hjensen := eLpNorm_integral_kernel_le μ K (hf.comp hi) hq
  change eLpNorm (conditionalHessian β s n m a b) (ENNReal.ofReal q) μ ≤ _ at hjensen
  rw [hnorm] at hjensen
  exact hjensen.trans (hmom (ofLong β s) rfl hβ.1 hβ.2 ((n : ℕ) + m).succPNat n
    (by simp only [Nat.succPNat_coe]; have := n.pos; omega) hn θ hcurv _ _ q hq)

/-- The coordinate and interval clauses of Subsection 5.1 for a proper
window. The last inequality prevents wrapping through the exterior. -/
def properBlockEvent (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ) (ε : ℝ) :
    Set (EuclideanSpace ℝ (Fin (n : ℕ))) :=
  {x | (∀ i, (n : ℝ) ^ (-ε) ≤ x i ∧ x i ≤ (n : ℝ) ^ ε) ∧
    ∀ (j : Fin (n : ℕ)) (k : Fin ((n : ℕ) + 1)),
      1 ≤ k.val → k.val ≤ ((n : ℕ) + m + 1) / 2 → j.val + k.val ≤ (n : ℕ) →
      |cyclicGapSum n j k.val (WithLp.ofLp x) - (k.val : ℝ)| ≤
        (n : ℝ) ^ ε * (k.val : ℝ) ^ (s.val / 2)}

private theorem measurable_forall {A ι : Type*} [MeasurableSpace A] [Countable ι]
    {P : ι → A → Prop} (h : ∀ i, MeasurableSet {x | P i x}) :
    MeasurableSet {x | ∀ i, P i x} := by
  simpa only [ofPred_forall] using MeasurableSet.iInter h

theorem measurableSet_properBlockEvent (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (ε : ℝ) : MeasurableSet (properBlockEvent s n m ε) := by
  apply MeasurableSet.inter
  · exact measurable_forall fun i =>
      (measurableSet_le measurable_const (EuclideanSpace.proj (𝕜 := ℝ) i).measurable).inter
        (measurableSet_le (EuclideanSpace.proj (𝕜 := ℝ) i).measurable measurable_const)
  · apply measurable_forall
    intro j
    apply measurable_forall
    intro k
    apply MeasurableSet.imp (measurable_const (a := 1 ≤ k.val)).setOf
    apply MeasurableSet.imp (measurable_const (a := k.val ≤ ((n : ℕ) + m + 1) / 2)).setOf
    apply MeasurableSet.imp (measurable_const (a := j.val + k.val ≤ (n : ℕ))).setOf
    simpa only [PhysicalEnergy.intervalLinear_apply] using measurableSet_le
      (((PhysicalEnergy.intervalLinear n j k.val).continuous.measurable).sub_const (k.val : ℝ)).abs
        (measurable_const (a := (n : ℝ) ^ ε * (k.val : ℝ) ^ (s.val / 2)))

/-- See Subsection 5.1 of the paper: the complete proper-window good event, on the
actual open carrier. Its matrix uses the everywhere density-defined version. -/
def properGoodEvent (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (ε κ : ℝ) :
    Set (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :=
  {x | x.val ∈ properBlockEvent s n m ε ∧ ∀ a b : Fin (n : ℕ),
    conditionalHessian β s n m a b x ≤ (n : ℝ) ^ (κ * ε) *
      (1 + (Riesz1.cyclicIndexDistance ((n : ℕ) + m).succPNat
        (a.castAdd m).castSucc (b.castAdd m).castSucc : ℝ)) ^ (-s.val)}

theorem measurableSet_properGoodEvent (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ) (ε κ : ℝ) :
    MeasurableSet (properGoodEvent β s n m ε κ) :=
  ((measurableSet_properBlockEvent s n m ε).preimage measurable_subtype_coe).inter
    (measurable_forall fun a => measurable_forall fun b =>
      measurableSet_le (measurable_conditionalHessian β s n m a b) measurable_const)

/-- An interval contained in the active window has exactly its original
particle block length. No reduction modulo the active size changes it. -/
theorem active_cyclicGapSum (n : ℕ+) (m : ℕ)
    (X : Riesz1.Configuration ((n : ℕ) + m).succPNat)
    (j : Fin (n : ℕ)) (k : ℕ) (hjk : j.val + k ≤ (n : ℕ)) :
    cyclicGapSum n j k (finiteGapBlock X) = Riesz1.blockLength X j.val k := by
  rw [Riesz1.blockLength_eq_sum]
  unfold cyclicGapSum
  apply Finset.sum_congr rfl
  intro a ha
  have ha' := Finset.mem_range.mp ha
  have hmod : (j.val + a) % (n : ℕ) = j.val + a := Nat.mod_eq_of_lt (by omega)
  simp only [finiteGapBlock, hmod, Nat.cast_add]
  rfl

/-- The good-block probability estimate on the proper marginal,
restricted only by change of carrier to its open support. -/
theorem proper_block_event (hRig : External.LongRangeRigidityLocallyUniform)
    (s : Riesz1.RieszExponent) {ε Cθ : ℝ} (hε : 0 < ε) (hCθ : 1 ≤ Cθ)
    (βlo βhi : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n : ℕ+) (m : ℕ), 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ((activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n hn θ ε false).comap
        ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
          EuclideanSpace ℝ (Fin (n : ℕ))))
            {x | x.val ∉ properBlockEvent s n m ε} ≤
              ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ blockTailPower s.val ε)) := by
  obtain ⟨C, c, hC, hc, _, hblocks⟩ := uniform_good_blocks hRig s hε hCθ βlo βhi hlo hle
  refine ⟨C, c, hC, hc, fun β hβ n m hper hn θ hcurv => ?_⟩
  let B := AffineSimplex.chartDomain n ((n + m : ℕ) + 1)
  let E := (properBlockEvent s n m ε)ᶜ
  have hE : MeasurableSet E := (measurableSet_properBlockEvent _ _ _ _).compl
  have hsub : ((↑) : B → EuclideanSpace ℝ (Fin (n : ℕ))) ''
      {x : B | x.val ∈ E} ⊆ E := by rintro _ ⟨x, hx, rfl⟩; exact hx
  rw [(MeasurableEmbedding.subtype_coe (AffineSimplex.isOpen_chartDomain n _).measurableSet).comap_apply]
  refine (measure_mono hsub).trans ?_
  rw [activeTiltedGapLaw, Measure.map_apply (DefinitionSanity.active_projection_measurable _ _) hE]
  have hbad := (hblocks β hβ ((n : ℕ) + m).succPNat n
    (by simp only [Nat.succPNat_coe]; have := n.pos; omega) hn
    (Or.inr (by simpa only [Nat.succPNat_coe] using hper)) θ hcurv).1
  refine (measure_mono ?_).trans hbad
  intro X hX hgood
  apply hX
  refine ⟨hgood.1, fun j k hk hkN hjk => ?_⟩
  change |cyclicGapSum n j k.val (finiteGapBlock X) - (k.val : ℝ)| ≤ _
  rw [active_cyclicGapSum n m X j k.val hjk]
  exact hgood.2 j k hk hkN (Or.inl hjk)

/-- See Subsection 5.1 of the paper, the proper-window exceptional probability.
The exponent is exactly `coefficientTailPower`, chosen before temperature.
The prefactors are uniform on every closed positive temperature interval. -/
theorem proper_good_event (hRig : External.LongRangeRigidityLocallyUniform)
    (s : Riesz1.RieszExponent) {ε Cθ : ℝ} (hε : 0 < ε) (hCθ : 1 ≤ Cθ)
    (βlo βhi : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n : ℕ+) (m : ℕ), 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ κ : ℝ, 1 ≤ κ →
      ((activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n hn θ ε false).comap
        ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
          EuclideanSpace ℝ (Fin (n : ℕ)))) (properGoodEvent β s n m ε κ)ᶜ ≤
            ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ coefficientTailPower s.val ε)) := by
  classical
  obtain ⟨B, b, hB, hb, hblocks⟩ := proper_block_event hRig s hε hCθ βlo βhi hlo hle
  obtain ⟨M, hM, hmom⟩ := tilted_conditional_hessian_moments s βlo βhi ε Cθ hlo hle hε hCθ
  have hA : 0 < (s.val + 2) / s.val := by have := s.property.1; positivity
  obtain ⟨D, d, hD, hd, hcut⟩ := MomentEvent.finite_moment_cutoffs hA hε hM
  refine ⟨B + D, min b d, by positivity, lt_min hb hd, ?_⟩
  intro β hβ n m hper hn θ hcurv κ hκ
  let μ := (activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n hn θ ε false).comap
    ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
  have : IsProbabilityMeasure μ := proper_active_probability _ _ _ _ _ _
  let Y : (Fin (n : ℕ) × Fin (n : ℕ)) →
      AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → ℝ :=
    fun ab => conditionalHessian β s n m ab.1 ab.2
  let w : (Fin (n : ℕ) × Fin (n : ℕ)) → ℝ := fun ab =>
    (1 + (Riesz1.cyclicIndexDistance ((n : ℕ) + m).succPNat
      (ab.1.castAdd m).castSucc (ab.2.castAdd m).castSucc : ℝ)) ^ (-s.val)
  let E : Set (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :=
    {x | ∃ ab, (n : ℝ) ^ (κ * ε) * w ab < |Y ab x|}
  have hcoeff := hcut n n.pos μ Y w κ (by simp [sq])
    (fun ab => measurable_conditionalHessian _ _ _ _ _ _)
    (fun ab => by dsimp [w]; positivity) hκ
    (fun ab q hq => hmom β hβ n m hn θ hcurv ab.1 ab.2 q hq)
  let G : Set (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :=
    {x | x.val ∉ properBlockEvent s n m ε}
  have hgap : μ G ≤ ENNReal.ofReal (B * Real.exp (-b * (n : ℝ) ^ blockTailPower s.val ε)) :=
    hblocks β hβ n m hper hn θ hcurv
  have hsub : (properGoodEvent β s n m ε κ)ᶜ ⊆ G ∪ E := by
    intro x hx
    by_cases hg : x ∈ G
    · exact Or.inl hg
    · right
      have hblock : x.val ∈ properBlockEvent s n m ε := Classical.not_not.mp hg
      have hnot : ¬ ∀ a b : Fin (n : ℕ), conditionalHessian β s n m a b x ≤
          (n : ℝ) ^ (κ * ε) * (1 + (Riesz1.cyclicIndexDistance ((n : ℕ) + m).succPNat
            (a.castAdd m).castSucc (b.castAdd m).castSucc : ℝ)) ^ (-s.val) :=
        fun hp => hx ⟨hblock, hp⟩
      obtain ⟨a, b, hab⟩ : ∃ a b : Fin (n : ℕ),
          (n : ℝ) ^ (κ * ε) * (1 + (Riesz1.cyclicIndexDistance ((n : ℕ) + m).succPNat
            (a.castAdd m).castSucc (b.castAdd m).castSucc : ℝ)) ^ (-s.val) <
              conditionalHessian β s n m a b x := by
        simpa only [not_forall, not_le] using hnot
      exact ⟨(a, b), hab.trans_le (le_abs_self _)⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hcompare (a t C₀ : ℝ) (ha : min b d ≤ a)
      (ht : coefficientTailPower s.val ε ≤ t) (hC₀ : 0 ≤ C₀) :
      ENNReal.ofReal (C₀ * Real.exp (-a * (n : ℝ) ^ t)) ≤
        ENNReal.ofReal (C₀ * Real.exp (-(min b d) * (n : ℝ) ^ coefficientTailPower s.val ε)) := by
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hC₀
    apply Real.exp_le_exp.mpr
    have ha0 : 0 ≤ a := (lt_min hb hd).le.trans ha
    have hh := mul_le_mul ha (Real.rpow_le_rpow_of_exponent_le hn1 ht)
      (by positivity : 0 ≤ (n : ℝ) ^ coefficientTailPower s.val ε) ha0
    linarith
  calc
    μ (properGoodEvent β s n m ε κ)ᶜ ≤ μ (G ∪ E) := measure_mono hsub
    _ ≤ μ G + μ E := measure_union_le _ _
    _ ≤ ENNReal.ofReal (B * Real.exp (-b * (n : ℝ) ^ blockTailPower s.val ε)) +
        ENNReal.ofReal (D * Real.exp (-d * (n : ℝ) ^ (ε / (2 * ((s.val + 2) / s.val))))) :=
      add_le_add hgap hcoeff
    _ ≤ _ := by
      have hh := add_le_add
        (hcompare b (blockTailPower s.val ε) B (min_le_left _ _) (min_le_left _ _) hB.le)
        (hcompare d (ε / (2 * ((s.val + 2) / s.val))) D (min_le_right _ _) (min_le_right _ _) hD.le)
      refine hh.trans_eq ?_
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- See Subsection 5.1 of the paper, the proper-window exceptional restricted `L²`
conclusion, on the complete coefficient-augmented bad event and with the
same temperature-independent stretched-exponential power. -/
theorem proper_exceptional_hessian (hRig : External.LongRangeRigidityLocallyUniform)
    (s : Riesz1.RieszExponent) {ε Cθ : ℝ} (hε : 0 < ε) (hCθ : 1 ≤ Cθ)
    (βlo βhi : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n : ℕ+) (m : ℕ), 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ κ : ℝ, 1 ≤ κ → ∀ a b : Fin (n : ℕ),
        eLpNorm (conditionalHessian β s n m a b) 2
          (((activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n hn θ ε false).comap
            ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
              EuclideanSpace ℝ (Fin (n : ℕ)))).restrict (properGoodEvent β s n m ε κ)ᶜ) ≤
            ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ coefficientTailPower s.val ε)) := by
  obtain ⟨B, c, hB, hc, hprob⟩ := proper_good_event hRig s hε hCθ βlo βhi hlo hle
  obtain ⟨M, hM, hmom⟩ := tilted_conditional_hessian_moments s βlo βhi ε Cθ hlo hle hε hCθ
  refine ⟨M * (4 : ℝ) ^ ((s.val + 2) / s.val) * B ^ (1 / 4 : ℝ), c / 4,
    by positivity, by positivity, ?_⟩
  intro β hβ n m hper hn θ hcurv κ hκ a b
  have hsp : (1 + (Riesz1.cyclicIndexDistance ((n : ℕ) + m).succPNat
      (a.castAdd m).castSucc (b.castAdd m).castSucc : ℝ)) ^ (-s.val) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact le_add_of_nonneg_right (Nat.cast_nonneg _))
      (by have := s.property.1; linarith)
  have h4 : eLpNorm (conditionalHessian β s n m a b) 4
      ((activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n hn θ ε false).comap
        ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
          EuclideanSpace ℝ (Fin (n : ℕ)))) ≤
        ENNReal.ofReal (M * (4 : ℝ) ^ ((s.val + 2) / s.val)) := by
    have hh := hmom β hβ n m hn θ hcurv a b 4 (by norm_num)
    norm_num only [ENNReal.ofReal_ofNat] at hh
    refine hh.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_of_le_one_right (by positivity) hsp
  have hh := MomentEvent.restricted_two_norm_le (measurable_conditionalHessian _ _ _ _ _ _)
    (properGoodEvent β s n m ε κ)ᶜ
    (t := c * (n : ℝ) ^ coefficientTailPower s.val ε) (by positivity) hB.le h4
    (by simpa only [neg_mul] using hprob β hβ n m hper hn θ hcurv κ hκ)
  convert hh using 1
  congr 3
  ring

/-- See Subsection 5.1 of the paper, all moment and exceptional-set clauses together.
The coefficient moments cover every active size. The two following conjuncts
are the full-cycle and proper-window alternatives of Subsection 5.1.
For a proper window `N = n + m + 1`. The lemma `proper_size_parametrization` proves
that this parametrization covers every source size. All constants precede
`β` in an arbitrary compact positive interval, and every `κ ≥ 1` works. -/
theorem coefficient_moments_and_exceptional_sets
    (hRig : External.LongRangeRigidityLocallyUniform)
    (s : Riesz1.RieszExponent) {ε Cθ : ℝ} (hε : 0 < ε) (hCθ : 1 ≤ Cθ)
    (βlo βhi : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      (∀ (N n : ℕ+), 2 ≤ (N : ℕ) → ∀ (hn : (n : ℕ) ≤ (N : ℕ)) (θ : PhysicalCutoff),
        (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
        ∀ (j : ℤ) (r : ℕ) (hr : 1 ≤ r) (hrN : r ≤ (N : ℕ) / 2) (q : ℝ), 1 ≤ q →
          eLpNorm (particleCoefficient (ofLong β s) N j r hr hrN) (ENNReal.ofReal q)
            (tiltedParticleMeasure (ofLong β s) N n hn θ ε false) ≤
              ENNReal.ofReal (C * q ^ ((s.val + 2) / s.val) * (r : ℝ) ^ (-s.val - 2))) ∧
      (∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ θ : PhysicalCutoff,
        (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
        ∀ κ : ℝ, 1 ≤ κ →
        let μ := tiltedParticleMeasure (ofLong β s) N N le_rfl θ ε false
        let E := (fullGoodEvent (ofLong β s) N ε κ)ᶜ
        (∀ (a b : Fin (N : ℕ)) (q : ℝ), 1 ≤ q →
          eLpNorm (particleHessian (ofLong β s) N a b) (ENNReal.ofReal q) μ ≤
            ENNReal.ofReal (C * q ^ ((s.val + 2) / s.val) *
              (1 + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-s.val))) ∧
        μ E ≤ ENNReal.ofReal (C * Real.exp (-c * (N : ℝ) ^ coefficientTailPower s.val ε)) ∧
        ∀ a b : Fin (N : ℕ), eLpNorm (particleHessian (ofLong β s) N a b) 2 (μ.restrict E) ≤
          ENNReal.ofReal (C * Real.exp (-c * (N : ℝ) ^ coefficientTailPower s.val ε))) ∧
      (∀ (n : ℕ+) (m : ℕ), 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
        ∀ (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (θ : PhysicalCutoff),
        (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
        ∀ κ : ℝ, 1 ≤ κ →
        let μ := (activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n hn θ ε false).comap
          ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
        let E := (properGoodEvent β s n m ε κ)ᶜ
        (∀ (a b : Fin (n : ℕ)) (q : ℝ), 1 ≤ q →
          eLpNorm (conditionalHessian β s n m a b) (ENNReal.ofReal q) μ ≤
            ENNReal.ofReal (C * q ^ ((s.val + 2) / s.val) *
              (1 + (Riesz1.cyclicIndexDistance ((n : ℕ) + m).succPNat
                (a.castAdd m).castSucc (b.castAdd m).castSucc : ℝ)) ^ (-s.val))) ∧
        μ E ≤ ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ coefficientTailPower s.val ε)) ∧
        ∀ a b : Fin (n : ℕ), eLpNorm (conditionalHessian β s n m a b) 2 (μ.restrict E) ≤
          ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ coefficientTailPower s.val ε))) := by
  obtain ⟨A, hA, ha⟩ := tilted_coefficient_moments s.val βlo βhi ε Cθ
    s.property.1 hlo hle hε hCθ
  obtain ⟨F, hF, hf⟩ := tilted_hessian_moments s.val βlo βhi ε Cθ
    s.property.1 hlo hle hε hCθ
  obtain ⟨P, hP, hp⟩ := tilted_conditional_hessian_moments s βlo βhi ε Cθ hlo hle hε hCθ
  obtain ⟨B, b, hB, hb, hfb⟩ := full_good_event hRig s hε hCθ βlo βhi hlo hle
  obtain ⟨D, d, hD, hd, hfd⟩ := full_exceptional_hessian hRig s hε hCθ βlo βhi hlo hle
  obtain ⟨E, e, hE, he, hpe⟩ := proper_good_event hRig s hε hCθ βlo βhi hlo hle
  obtain ⟨G, g, hG, hg, hpg⟩ := proper_exceptional_hessian hRig s hε hCθ βlo βhi hlo hle
  let C := A + F + P + B + D + E + G
  let c := min (min b d) (min e g)
  have hC : 0 < C := by dsimp [C]; positivity
  have hc : 0 < c := lt_min (lt_min hb hd) (lt_min he hg)
  have hAC : A ≤ C := by dsimp [C]; linarith
  have hFC : F ≤ C := by dsimp [C]; linarith
  have hPC : P ≤ C := by dsimp [C]; linarith
  have hBC : B ≤ C := by dsimp [C]; linarith
  have hDC : D ≤ C := by dsimp [C]; linarith
  have hEC : E ≤ C := by dsimp [C]; linarith
  have hGC : G ≤ C := by dsimp [C]; linarith
  have hcb : c ≤ b := (min_le_left _ _).trans (min_le_left _ _)
  have hcd : c ≤ d := (min_le_left _ _).trans (min_le_right _ _)
  have hce : c ≤ e := (min_le_right _ _).trans (min_le_left _ _)
  have hcg : c ≤ g := (min_le_right _ _).trans (min_le_right _ _)
  have hm {D q w : ℝ} (hDC : D ≤ C) (hq : 0 ≤ q) (hw : 0 ≤ w) :
      ENNReal.ofReal (D * q ^ ((s.val + 2) / s.val) * w) ≤
        ENNReal.ofReal (C * q ^ ((s.val + 2) / s.val) * w) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hDC (Real.rpow_nonneg hq _)) hw)
  have ht {D d t : ℝ} (hDC : D ≤ C) (hcd : c ≤ d) (ht : 0 ≤ t) :
      ENNReal.ofReal (D * Real.exp (-d * t)) ≤ ENNReal.ofReal (C * Real.exp (-c * t)) := by
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul hDC _ (Real.exp_pos _).le hC.le
    apply Real.exp_le_exp.mpr
    simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right hcd ht)
  refine ⟨C, c, hC, hc, fun β hβ => ⟨?_, ?_, ?_⟩⟩
  · intro N n hN hn θ hcurv j r hr hrN q hq
    exact (ha (ofLong β s) rfl hβ.1 hβ.2 N n hN hn θ hcurv j r hr hrN q hq).trans
      (hm hAC (by linarith) (by positivity))
  · intro N hN θ hcurv κ hκ
    dsimp only
    refine ⟨fun a b q hq => ?_, ?_, fun a b => ?_⟩
    · exact (hf (ofLong β s) rfl hβ.1 hβ.2 N N hN le_rfl θ hcurv a b q hq).trans
        (hm hFC (by linarith) (by positivity))
    · exact (hfb β hβ N hN θ hcurv κ hκ).trans (ht hBC hcb (by positivity))
    · exact (hfd β hβ N hN θ hcurv κ hκ a b).trans (ht hDC hcd (by positivity))
  · intro n m hper hn θ hcurv κ hκ
    dsimp only
    refine ⟨fun a b q hq => ?_, ?_, fun a b => ?_⟩
    · exact (hp β hβ n m hn θ hcurv a b q hq).trans (hm hPC (by linarith) (by positivity))
    · exact (hpe β hβ n m hper hn θ hcurv κ hκ).trans (ht hEC hce (by positivity))
    · exact (hpg β hβ n m hper hn θ hcurv κ hκ a b).trans (ht hGC hcg (by positivity))

end Riesz2.GoodBlocks
