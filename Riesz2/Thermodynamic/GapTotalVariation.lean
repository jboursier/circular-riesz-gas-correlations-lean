/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.GapLimit
public import Riesz2.Frozen.External.LogConcaveConvergence
public import Riesz2.ToMathlib.WeightedTotalVariation
public import Riesz2.ToMathlib.DensityTestVariation
public import Riesz2.ToMathlib.VarianceFullSupport
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Total variation of fixed gap marginals

See the proof of Theorem 3. The composition uses the ordinary-gap Cauchy estimate,
nondegeneracy and absolute continuity of the limiting law. The log-concave density
convergence result is an explicit hypothesis.
-/

public section
noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace BoundedContinuousFunction

namespace Riesz2

/-- Step 2 of the proof of Theorem 3: the Cule–Samworth density convergence
result supplies
ordinary block TV and a log-concave representative. Weighted tests are obtained
separately by second-moment truncation in Step 3. -/
theorem gapBlock_totalVariation_of_density_internal
    (hconvergence : External.LogConcaveConvergence)
    (k : ℕ) (hk : 1 ≤ k)
    (P : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin k)))
    (Q : ProbabilityMeasure (EuclideanSpace ℝ (Fin k)))
    (hweak : Tendsto P atTop (𝓝 Q))
    (hfinite : ∀ n, ∃ f : EuclideanSpace ℝ (Fin k) → ℝ,
      Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∫⁻ x, ENNReal.ofReal (f x)) = 1 ∧
      ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) ∧
      (P n).toMeasure = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hlimit : ∃ g : EuclideanSpace ℝ (Fin k) → ℝ,
      Measurable g ∧ (∀ x, 0 ≤ g x) ∧ (∫⁻ x, ENNReal.ofReal (g x)) = 1 ∧
      Q.toMeasure = volume.withDensity (fun x => ENNReal.ofReal (g x))) :
    (∃ g : EuclideanSpace ℝ (Fin k) → ℝ,
      Measurable g ∧ (∀ x, 0 ≤ g x) ∧ (∫⁻ x, ENNReal.ofReal (g x)) = 1 ∧
      ConcaveOn ℝ {x | 0 < g x} (fun x => Real.log (g x)) ∧
      Q.toMeasure = volume.withDensity (fun x => ENNReal.ofReal (g x))) ∧
    Tendsto (fun n => totalVariation (P n).toMeasure Q.toMeasure) atTop (𝓝 0) := by
  choose f hf using hfinite
  obtain ⟨g, hgm, hg0, hg1, hQg⟩ := hlimit
  have hw : ∀ φ : EuclideanSpace ℝ (Fin k) →ᵇ ℝ,
      Tendsto (fun n => ∫ x, φ x ∂volume.withDensity (fun x => ENNReal.ofReal (f n x)))
        atTop (𝓝 (∫ x, φ x ∂volume.withDensity (fun x => ENNReal.ofReal (g x)))) := by
    intro φ
    simpa only [← (hf _).2.2.2.2, ← hQg] using
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak φ)
  obtain ⟨⟨g', hg', hlc, heq⟩, hL1, _⟩ := (hconvergence k hk).1 f g
    (fun n => ⟨⟨(hf n).1, (hf n).2.1, (hf n).2.2.1⟩, (hf n).2.2.2.1⟩)
    ⟨hgm, hg0, hg1⟩ hw
  have hQg' : Q.toMeasure = volume.withDensity (fun x => ENNReal.ofReal (g' x)) :=
    hQg.trans (withDensity_congr_ae (heq.fun_comp ENNReal.ofReal)).symm
  refine ⟨⟨g', hg'.1, hg'.2.1, hg'.2.2, hlc, hQg'⟩, ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL1
    (fun _ => bot_le) (fun n => ?_)
  have hp : IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (f n x))) := by
    rw [← (hf n).2.2.2.2]; exact (P n).prop
  have hq : IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (g x))) := by
    rw [← hQg]; exact Q.prop
  have hb := totalVariation_density_le volume (hf n).1 (hf n).2.1 hgm hg0
  simpa only [← (hf n).2.2.2.2, ← hQg] using hb

local notation "Gaps" => (ℤ → Ioi (0 : ℝ))
local notation "gapProj" => (fun (k : ℕ) (a : ℤ) (y : Gaps) =>
  (WithLp.toLp 2 (fun j : Fin k => (y (a + (Fin.val j : ℤ)) : ℝ)) : EuclideanSpace ℝ (Fin k)))
local notation "gapMarginal" => (fun (q : ProbabilityMeasure Gaps) (k : ℕ) (a : ℤ) =>
  ProbabilityMeasure.map q (gapProj k a))

/-- Continuity of the actual finite-coordinate projection of positive gaps. -/
lemma continuous_gap_block_projection_internal (k : ℕ) (a : ℤ) :
    Continuous (gapProj k a) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi fun _ =>
    continuous_subtype_val.comp (continuous_apply _))

/-- Block projection transports integrability without changing gap coordinates. -/
lemma integrable_gap_block_coordinate_internal
    (q : ProbabilityMeasure Gaps) (k : ℕ) (a : ℤ) (i : Fin k)
    (hi : Integrable (fun y : Gaps => (y (a + (i.val : ℤ)) : ℝ)) q) :
    Integrable (fun x : EuclideanSpace ℝ (Fin k) => x i) (gapMarginal q k a) := by
  change Integrable _ (q.toMeasure.map (gapProj k a))
  exact (integrable_map_measure (by fun_prop)
    (continuous_gap_block_projection_internal k a).measurable.aemeasurable).mpr hi

/-- Shift invariance identifies every consecutive block law with the zero-based one. -/
lemma gap_block_law_shift_internal (q : ProbabilityMeasure Gaps)
    (k : ℕ) (a : ℤ) (hs : q.map (gapIndexShift a) = q) :
    gapMarginal q k a = gapMarginal q k 0 := by
  apply ProbabilityMeasure.toMeasure_injective
  change q.toMeasure.map (gapProj k a) = q.toMeasure.map (gapProj k 0)
  have h := congrArg (fun t : ProbabilityMeasure Gaps =>
    t.toMeasure.map (gapProj k 0)) hs
  rw [ProbabilityMeasure.toMeasure_map, Measure.map_map
    (continuous_gap_block_projection_internal k 0).measurable
    (gapIndexShift a).continuous.measurable] at h
  simpa only [Function.comp_def, gapIndexShift_apply, zero_add] using h

/-- The Euclidean block law is the pushforward of the finite gap block.
No additional finite-gap encoding is introduced. -/
lemma gap_block_law_finiteGapBlock_internal (p : Parameters) (N K : ℕ+) :
    (gapMarginal (periodicGapLaw p N) (K : ℕ) 0).toMeasure =
      ((gibbsMeasure p N).map (finiteGapBlock (K := K))).map (WithLp.toLp 2) := by
  have hm : Measurable (fun y : Gaps => fun j : Fin (K : ℕ) => (y (j.val : ℤ) : ℝ)) :=
    Measurable.of_eval fun j => measurable_subtype_coe.comp (measurable_pi_apply _)
  rw [← periodicGapLaw_map_finiteGapBlock p N K,
    Measure.map_map (PiLp.continuous_toLp 2 _).measurable hm]
  change (periodicGapLaw p N).toMeasure.map (gapProj (K : ℕ) 0) = _
  simp only [Function.comp_def, zero_add]

/-- Boundary case of the proof of Theorem 3:
all probability laws of the empty block agree, so their event distance is zero. -/
lemma empty_gap_block_totalVariation_internal (q q' : ProbabilityMeasure Gaps) (a : ℤ) :
    totalVariation (gapMarginal q 0 a).toMeasure (gapMarginal q' 0 a).toMeasure = 0 := by
  have heq : gapMarginal q 0 a = gapMarginal q' 0 a := by
    apply ProbabilityMeasure.toMeasure_injective
    ext A
    by_cases hA : A = ∅
    · simp only [hA, measure_empty]
    · have hne : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hA
      have hAu : A = univ := Set.eq_univ_of_forall fun x => by
        obtain ⟨y, hy⟩ := hne
        rwa [Subsingleton.elim x y]
      simp only [hAu, measure_univ]
  simp only [heq, totalVariation, tsub_self, add_zero, iSup_const]

/-- The empty block has the constant unit density on zero-dimensional
Euclidean space, with full affine support and log-concavity. -/
lemma empty_gap_block_density_internal (q : ProbabilityMeasure Gaps) (a : ℤ) :
    (affineSpan ℝ (gapMarginal q 0 a).toMeasure.support = ⊤) ∧
    ∃ g : EuclideanSpace ℝ (Fin 0) → ℝ,
      Measurable g ∧ (∀ x, 0 ≤ g x) ∧ (∫⁻ x, ENNReal.ofReal (g x)) = 1 ∧
      ConcaveOn ℝ {x | 0 < g x} (fun x => Real.log (g x)) ∧
      (gapMarginal q 0 a).toMeasure = volume.withDensity (fun x => ENNReal.ofReal (g x)) := by
  have hsupp : ∀ᵐ x ∂(gapMarginal q 0 a).toMeasure,
      x ∈ (gapMarginal q 0 a).toMeasure.support := Measure.support_mem_ae
  obtain ⟨z, hz⟩ := hsupp.exists
  constructor
  · apply top_unique
    intro x _
    rw [Subsingleton.elim x z]
    exact subset_affineSpan ℝ _ hz
  · refine ⟨fun _ => 1, measurable_const, fun _ => zero_le_one, ?_, ?_, ?_⟩
    · simp [volume_euclideanSpace_eq_dirac]
    · simpa using (concaveOn_const (0 : ℝ) convex_univ : ConcaveOn ℝ univ (fun _ : EuclideanSpace ℝ (Fin 0) => (0 : ℝ)))
    · simp only [ENNReal.ofReal_one, withDensity_const, one_smul, volume_euclideanSpace_eq_dirac]
      ext A
      by_cases hA : A = ∅
      · simp only [hA, measure_empty]
      · have hne : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hA
        have hAu : A = univ := Set.eq_univ_of_forall fun x => by
          obtain ⟨y, hy⟩ := hne
          rwa [Subsingleton.elim x y]
        simp only [hAu, measure_univ, Measure.dirac_apply_of_mem (mem_univ _)]

/-- See the proof of Theorem 3 in the paper, internal composition
from the ordinary-gap Cauchy estimate, nondegeneracy and absolute continuity
of the limit. All consecutive blocks, including the empty block, are included. -/
theorem convergence_gap_total_variation_from_predecessors_internal
    (hcomparison :
      ∀ (p : Parameters) (ζ : ℝ), 0 < ζ → ∃ C : ℝ, 0 < C ∧
        ∀ (n N N' : ℕ+) (_ : 2 ≤ (n : ℕ)),
          (N : ℕ) ≤ (N' : ℕ) → 4 * (n : ℕ) ≤ (N : ℕ) →
          (n : ℝ) ^ (2 / p.val.2) ≤ (N : ℝ) →
          ∀ (G : BlockObservable n) (J : Finset (Fin (n : ℕ))),
            MiddleConsecutiveBlock n J → DependsOnBlockCoordinates G J →
            Integrable (fun X : Riesz1.Configuration N => G.val (finiteGapBlock X))
              (gibbsMeasure p N) ∧
            Integrable (fun X : Riesz1.Configuration N' => G.val (finiteGapBlock X))
              (gibbsMeasure p N') ∧
            |(∫ X : Riesz1.Configuration N, G.val (finiteGapBlock X) ∂gibbsMeasure p N) -
              (∫ X : Riesz1.Configuration N', G.val (finiteGapBlock X) ∂gibbsMeasure p N')| ≤
              C * (n : ℝ) ^ (-min p.val.2 1 / 2 + ζ) * blockDerivativeNorm G)
    (hnondegeneracy : ∀ (p : Parameters) (q : ProbabilityMeasure Gaps),
      Tendsto (fun n : ℕ => periodicGapLaw p n.succPNat) atTop (𝓝 q) →
      ∀ k : ℕ, 1 ≤ k → ∃ c : ℝ, 0 < c ∧
        (∀ (N : ℕ+), 2 * k + 2 ≤ (N : ℕ) → ∀ u : EuclideanSpace ℝ (Fin k),
          ∃ hi : Integrable (fun x : EuclideanSpace ℝ (Fin k) => ⟪u, x⟫_ℝ)
            (gapMarginal (periodicGapLaw p N) k 0),
          ENNReal.ofReal (c * ‖u‖ ^ 2) ≤ Riesz1.variance
            (gapMarginal (periodicGapLaw p N) k 0).toMeasure (fun x => ⟪u, x⟫_ℝ) hi) ∧
        (∀ u : EuclideanSpace ℝ (Fin k),
          ∃ hi : Integrable (fun x : EuclideanSpace ℝ (Fin k) => ⟪u, x⟫_ℝ)
            (gapMarginal q k 0),
          ENNReal.ofReal (c * ‖u‖ ^ 2) ≤ Riesz1.variance
            (gapMarginal q k 0).toMeasure (fun x => ⟪u, x⟫_ℝ) hi) ∧
        (∀ (N : ℕ+), k < (N : ℕ) → ∃ f : EuclideanSpace ℝ (Fin k) → ℝ,
          Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∫⁻ x, ENNReal.ofReal (f x)) = 1 ∧
          ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) ∧
          (gapMarginal (periodicGapLaw p N) k 0).toMeasure =
            volume.withDensity (fun x => ENNReal.ofReal (f x))))
    (hdensity : ∀ (k : ℕ), 1 ≤ k →
      ∀ (f : ℕ → EuclideanSpace ℝ (Fin k) → ℝ),
      (∀ n, Measurable (f n) ∧ (∀ x, 0 ≤ f n x) ∧
        (∫⁻ x, ENNReal.ofReal (f n x)) = 1 ∧
        ConcaveOn ℝ {x | 0 < f n x} (fun x => Real.log (f n x))) →
      ∀ Q : ProbabilityMeasure (EuclideanSpace ℝ (Fin k)),
      (∀ φ : EuclideanSpace ℝ (Fin k) →ᵇ ℝ,
        Tendsto (fun n => ∫ x, φ x ∂volume.withDensity (fun x => ENNReal.ofReal (f n x)))
          atTop (𝓝 (∫ x, φ x ∂Q))) →
      affineSpan ℝ Q.toMeasure.support = ⊤ →
      ∃ g : EuclideanSpace ℝ (Fin k) → ℝ,
        Measurable g ∧ (∀ x, 0 ≤ g x) ∧ (∫⁻ x, ENNReal.ofReal (g x)) = 1 ∧
        Q.toMeasure = volume.withDensity (fun x => ENNReal.ofReal (g x)))
    (hconvergence : External.LogConcaveConvergence) (p : Parameters) :
    ∃! q : ProbabilityMeasure Gaps,
      Tendsto (fun n : ℕ => periodicGapLaw p n.succPNat) atTop (𝓝 q) ∧
      ∀ (k : ℕ) (a : ℤ),
        (affineSpan ℝ (gapMarginal q k a).toMeasure.support = ⊤) ∧
        (∃ g : EuclideanSpace ℝ (Fin k) → ℝ,
          Measurable g ∧ (∀ x, 0 ≤ g x) ∧ (∫⁻ x, ENNReal.ofReal (g x)) = 1 ∧
          ConcaveOn ℝ {x | 0 < g x} (fun x => Real.log (g x)) ∧
          (gapMarginal q k a).toMeasure = volume.withDensity (fun x => ENNReal.ofReal (g x))) ∧
        Tendsto (fun n : ℕ => totalVariation
          (gapMarginal (periodicGapLaw p n.succPNat) k a).toMeasure
          (gapMarginal q k a).toMeasure) atTop (𝓝 0) ∧
        (∀ i : Fin k,
          (∀ (N : ℕ+) (F : EuclideanSpace ℝ (Fin k) → ℝ),
            Measurable F → (∀ x, |F x| ≤ 1) →
            Integrable (fun x => x i * F x) (gapMarginal (periodicGapLaw p N) k a) ∧
              Integrable (fun x => x i * F x) (gapMarginal q k a)) ∧
          Tendsto (fun n : ℕ => ⨆ F : {F : EuclideanSpace ℝ (Fin k) → ℝ //
              Measurable F ∧ ∀ x, |F x| ≤ 1},
            ENNReal.ofReal |(∫ x, x i * F.val x ∂gapMarginal (periodicGapLaw p n.succPNat) k a) -
              (∫ x, x i * F.val x ∂gapMarginal q k a)|) atTop (𝓝 0)) := by
  obtain ⟨q, hq, _⟩ := convergence_gap_limit_from_cauchy_internal hcomparison p
  refine ⟨q, ⟨hq.1, ?_⟩, ?_⟩
  · intro k a
    by_cases hk : 1 ≤ k
    ·
      let Q := gapMarginal q k 0
      let P := fun n : ℕ => gapMarginal (periodicGapLaw p (n + (k + 1)).succPNat) k 0
      have hQshift : gapMarginal q k a = Q :=
        gap_block_law_shift_internal q k a (hq.2.1 a)
      have hPshift (n : ℕ) : gapMarginal
          (periodicGapLaw p (n + (k + 1)).succPNat) k a = P n :=
        gap_block_law_shift_internal _ k a (periodicGapLaw_shift p _ (by simp only [Nat.succPNat_coe]; omega) a)
      have hweak : Tendsto P atTop (𝓝 Q) :=
        ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
          ((tendsto_add_atTop_iff_nat (k + 1)).mpr hq.1)
          (continuous_gap_block_projection_internal k 0)
      obtain ⟨c, hc, _, hcov, hfinite⟩ := hnondegeneracy p q hq.1 k hk
      choose hiu hbound using hcov
      have hspan : affineSpan ℝ Q.toMeasure.support = ⊤ :=
        affineSpan_support_eq_top_of_variance_pos Q hiu (fun u hu =>
          (ENNReal.ofReal_pos.mpr (mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hu)))).trans_le
            (hbound u))
      have hfiniteP (n : ℕ) := hfinite (n + (k + 1)).succPNat (by simp only [Nat.succPNat_coe]; omega)
      choose f hf using hfiniteP
      have hfdata (n : ℕ) :=
        And.intro (hf n).1 (And.intro (hf n).2.1 (And.intro (hf n).2.2.1 (hf n).2.2.2.1))
      have hweakf : ∀ φ : EuclideanSpace ℝ (Fin k) →ᵇ ℝ,
          Tendsto (fun n => ∫ x, φ x ∂volume.withDensity (fun x => ENNReal.ofReal (f n x)))
            atTop (𝓝 (∫ x, φ x ∂Q)) := by
        intro φ
        simpa only [← (hf _).2.2.2.2] using
          ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak φ
      have hlimit := hdensity k hk f hfdata Q hweakf hspan
      obtain ⟨D, hD, hmom, hlimitMom⟩ := hq.2.2.2.1 2 (by norm_num)
      have hiFinite (N : ℕ+) (i : ℤ) :
          Integrable (fun y : Gaps => (y i : ℝ)) (periodicGapLaw p N) :=
        (gapCoordinate_memLp_two_internal _ i
          (((le_add_right le_rfl).trans (hmom N i)).trans_lt ENNReal.ofReal_lt_top)).integrable
            (by norm_num)
      obtain ⟨hg, hTV⟩ := gapBlock_totalVariation_of_density_internal
        hconvergence k hk P Q hweak (fun n => ⟨f n, hf n⟩) hlimit
      have hcoord (ρ : ProbabilityMeasure Gaps) (i : Fin k)
          (hb : (∫⁻ y : Gaps, ENNReal.ofReal ((y (i.val : ℤ) : ℝ) ^ (2 : ℝ)) ∂ρ) ≤
            ENNReal.ofReal D) :
          MemLp (fun x : EuclideanSpace ℝ (Fin k) => x i) 2 (gapMarginal ρ k 0) ∧
            (∫ x : EuclideanSpace ℝ (Fin k), (x i) ^ 2 ∂gapMarginal ρ k 0) ≤ D := by
        have hy := gapCoordinate_memLp_two_internal ρ i.val (hb.trans_lt ENNReal.ofReal_lt_top)
        have hi : MemLp (fun x : EuclideanSpace ℝ (Fin k) => x i) 2 (gapMarginal ρ k 0) :=
          (memLp_map_measure_iff (by fun_prop)
            (continuous_gap_block_projection_internal k 0).measurable.aemeasurable).mpr
            (by simpa only [Function.comp_def, zero_add] using hy)
        refine ⟨hi, ?_⟩
        rw [ProbabilityMeasure.toMeasure_map, integral_map
          (continuous_gap_block_projection_internal k 0).measurable.aemeasurable (by fun_prop)]
        change (∫ y : Gaps, (y (0 + (i.val : ℤ)) : ℝ) ^ 2 ∂ρ) ≤ D
        simp only [zero_add]
        rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => sq_nonneg _)
          hy.integrable_sq.aestronglyMeasurable]
        apply ENNReal.toReal_le_of_le_ofReal hD.le
        simpa only [Real.rpow_two] using hb
      have hweighted (i : Fin k) :=
        weighted_testSup_tendsto_of_totalVariation_and_second_moment_internal
          (fun n => (P n).toMeasure) Q.toMeasure (w := fun x => x i) (by fun_prop)
          (fun n => (hcoord _ i ((le_add_right le_rfl).trans (hmom _ _))).1)
          (hcoord q i ((le_add_right le_rfl).trans (hlimitMom _))).1 hTV
          (Eventually.of_forall fun n =>
            (hcoord _ i ((le_add_right le_rfl).trans (hmom _ _))).2)
      refine ⟨by simpa only [hQshift] using hspan,
        by simpa only [hQshift] using hg, ?_, ?_⟩
      · apply (tendsto_add_atTop_iff_nat (k + 1)).mp
        simpa only [hPshift, hQshift] using hTV
      · intro i
        refine ⟨?_, ?_⟩
        · intro N F hFm hFb
          exact ⟨(integrable_gap_block_coordinate_internal _ k a i (hiFinite N _)).mul_bdd
              hFm.aestronglyMeasurable
              (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hFb x),
            (integrable_gap_block_coordinate_internal _ k a i (hq.2.2.1 _).1).mul_bdd
              hFm.aestronglyMeasurable
              (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hFb x)⟩
        · apply (tendsto_add_atTop_iff_nat (k + 1)).mp
          simpa only [hPshift, hQshift] using hweighted i
    · have hk0 : k = 0 := by omega
      subst k
      obtain ⟨hs, hd⟩ := empty_gap_block_density_internal q a
      refine ⟨hs, hd, ?_, fun i => Fin.elim0 i⟩
      simpa only [empty_gap_block_totalVariation_internal] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
  · intro q' hq'
    exact tendsto_nhds_unique hq'.1 hq.1

end Riesz2
