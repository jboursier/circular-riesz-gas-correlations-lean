/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Constructions.Projective
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic

/-!
# Bounded Lipschitz tests for finite blocks of two-sided gaps

See the proof of Theorem 3 in the paper, with the distance convention of Subsection 6.3.
The space of a block of length `k` is `EuclideanSpace ℝ (Fin k)`. The test class
includes all bounded one-Lipschitz functions. The companion library's `Riesz1.BLTest`
additionally requires differentiability and is therefore a different test class.
-/

public section

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology NNReal BoundedContinuousFunction

namespace Riesz2

variable {k : ℕ}

/-- The bounded-Lipschitz distance from Subsection 6.3, on finite gap blocks.
It is the supremum over `|f| ≤ 1` and Lipschitz constant at most one. -/
def boundedLipschitzDistance
    (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin k))) : ℝ :=
  sSup {a : ℝ | ∃ f : EuclideanSpace ℝ (Fin k) →ᵇ ℝ,
    ‖f‖ ≤ 1 ∧ LipschitzWith 1 f ∧ a = |(∫ x, f x ∂μ) - ∫ x, f x ∂ν|}

private lemma test_integral_abs_le (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin k)))
    (f : EuclideanSpace ℝ (Fin k) →ᵇ ℝ) (hf : ‖f‖ ≤ 1) :
    |∫ x, f x ∂μ| ≤ 1 := by
  simpa [Real.norm_eq_abs, Measure.real] using
    (norm_integral_le_of_norm_le_const (μ := (μ : Measure _))
      (ae_of_all _ fun x => (f.norm_coe_le_norm x).trans hf))

private lemma test_differences_bddAbove
    (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin k))) :
    BddAbove {a : ℝ | ∃ f : EuclideanSpace ℝ (Fin k) →ᵇ ℝ,
      ‖f‖ ≤ 1 ∧ LipschitzWith 1 f ∧ a = |(∫ x, f x ∂μ) - ∫ x, f x ∂ν|} := by
  refine ⟨2, ?_⟩
  rintro a ⟨f, hf, _, rfl⟩
  calc
    |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ |∫ x, f x ∂μ| + |∫ x, f x ∂ν| := abs_sub _ _
    _ ≤ 2 := by linarith [test_integral_abs_le μ f hf, test_integral_abs_le ν f hf]

private lemma zero_mem_test_differences
    (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin k))) :
    0 ∈ {a : ℝ | ∃ f : EuclideanSpace ℝ (Fin k) →ᵇ ℝ,
      ‖f‖ ≤ 1 ∧ LipschitzWith 1 f ∧ a = |(∫ x, f x ∂μ) - ∫ x, f x ∂ν|} := by
  refine ⟨0, by simp, ?_, by simp⟩
  exact (LipschitzWith.const (0 : ℝ)).weaken (by norm_num)

/-- The supremum defining the block bounded-Lipschitz distance is nonnegative. -/
lemma boundedLipschitzDistance_nonneg
    (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin k))) :
    0 ≤ boundedLipschitzDistance μ ν :=
  le_csSup (test_differences_bddAbove μ ν) (zero_mem_test_differences μ ν)

/-- Every normalized bounded Lipschitz integral difference is bounded by the distance. -/
lemma abs_integral_sub_le_boundedLipschitzDistance
    (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin k)))
    (f : EuclideanSpace ℝ (Fin k) →ᵇ ℝ) (hf : ‖f‖ ≤ 1) (hl : LipschitzWith 1 f) :
    |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ boundedLipschitzDistance μ ν :=
  le_csSup (test_differences_bddAbove μ ν) ⟨f, hf, hl, rfl⟩

/-- A uniform bound on the normalized test integrals bounds their supremum. -/
lemma boundedLipschitzDistance_le
    (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin k))) {a : ℝ}
    (ha : ∀ f : EuclideanSpace ℝ (Fin k) →ᵇ ℝ, ‖f‖ ≤ 1 → LipschitzWith 1 f →
      |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ a) :
    boundedLipschitzDistance μ ν ≤ a := by
  apply csSup_le ⟨0, zero_mem_test_differences μ ν⟩
  rintro b ⟨f, hf, hl, rfl⟩
  exact ha f hf hl

private lemma level_integrableOn
    (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin k)))
    (g : EuclideanSpace ℝ (Fin k) →ᵇ ℝ) (a b : ℝ) :
    IntegrableOn (fun t => (ν : Measure _).real {x | t ≤ g x}) (Ioc a b) := by
  apply Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne
  · apply (Measurable.ennreal_toReal (Antitone.measurable ?_)).aestronglyMeasurable
    exact fun s t hst => measure_mono (fun _ hx => hst.trans hx)
  · apply ae_of_all
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact (measureReal_mono (subset_univ _)).trans (by simp)

/-- The layer-cake estimate behind uniform control of the test class. -/
private lemma integral_le_of_lp_lt
    (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin k)))
    (f : EuclideanSpace ℝ (Fin k) →ᵇ ℝ) (hf : ‖f‖ ≤ 1) (hl : LipschitzWith 1 f)
    {ε : ℝ} (hε : 0 < ε)
    (hμν : levyProkhorovEDist μ.toMeasure ν.toMeasure < ENNReal.ofReal ε) :
    (∫ x, f x ∂μ) ≤ (∫ x, f x ∂ν) + 3 * ε := by
  let h : EuclideanSpace ℝ (Fin k) →ᵇ ℝ := f + BoundedContinuousFunction.const _ 1
  let g : EuclideanSpace ℝ (Fin k) →ᵇ ℝ := h + BoundedContinuousFunction.const _ ε
  have hn (x) : 0 ≤ h x := by
    have := f.neg_norm_le_apply x
    change 0 ≤ f x + 1
    linarith
  have gn (x) : 0 ≤ g x := by
    change 0 ≤ h x + ε
    linarith [hn x]
  have hh : ‖h‖ ≤ 2 := by
    apply (BoundedContinuousFunction.norm_le (by norm_num)).2
    intro x
    change ‖f x + 1‖ ≤ 2
    calc
      ‖f x + 1‖ ≤ ‖f x‖ + ‖(1 : ℝ)‖ := norm_add_le _ _
      _ ≤ 2 := by have := f.norm_coe_le_norm x; norm_num at *; linarith
  have hnorm : ‖h‖ ≤ ‖g‖ := by
    apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).2
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hn x)]
    have := g.apply_le_norm x
    change h x + ε ≤ ‖g‖ at this
    linarith
  have thick_sub (t : ℝ) : thickening ε {x | t ≤ h x} ⊆ {x | t ≤ g x} := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp hx
    have hdist := hl.dist_le_mul y x
    rw [NNReal.coe_one, one_mul, Real.dist_eq] at hdist
    have hdiff := (le_abs_self (f y - f x)).trans hdist
    change t ≤ f y + 1 at hy
    change t ≤ f x + 1 + ε
    rw [dist_comm] at hxy
    linarith
  have hlevel :
      (∫ t in Ioc 0 ‖h‖, (ν : Measure _).real (thickening ε {x | t ≤ h x})) ≤
        ∫ t in Ioc 0 ‖h‖, (ν : Measure _).real {x | t ≤ g x} := by
    apply integral_mono_of_nonneg
      (ae_of_all _ fun _ => measureReal_nonneg) (level_integrableOn ν g _ _)
    exact ae_of_all _ fun t => measureReal_mono (thick_sub t)
  have hextend :
      (∫ t in Ioc 0 ‖h‖, (ν : Measure _).real {x | t ≤ g x}) ≤ ∫ x, g x ∂ν := by
    rw [BoundedContinuousFunction.integral_eq_integral_meas_le g ν (ae_of_all _ gn)]
    apply setIntegral_mono_set (level_integrableOn ν g _ _)
      (ae_of_all _ fun _ => measureReal_nonneg)
    exact ae_of_all _ fun _ hx => ⟨hx.1, hx.2.trans hnorm⟩
  have hb := BoundedContinuousFunction.integral_le_of_levyProkhorovEDist_lt
    (μ : Measure _) (ν : Measure _) hε hμν h (ae_of_all _ hn)
  have hs : (∫ x, h x ∂μ) ≤ (∫ x, g x ∂ν) + 2 * ε := by
    calc
      _ ≤ _ := hb
      _ ≤ (∫ x, g x ∂ν) + ε * ‖h‖ := add_le_add (hlevel.trans hextend) le_rfl
      _ ≤ _ := by nlinarith
  have ih (ρ : ProbabilityMeasure (EuclideanSpace ℝ (Fin k))) :
      (∫ x, h x ∂ρ) = (∫ x, f x ∂ρ) + 1 := by
    change (∫ x, f x + 1 ∂ρ) = _
    rw [integral_add (f.integrable _) (integrable_const _)]; simp
  have ig : (∫ x, g x ∂ν) = (∫ x, h x ∂ν) + ε := by
    change (∫ x, h x + ε ∂ν) = _
    rw [integral_add (h.integrable _) (integrable_const _)]; simp
  rw [ig, ih μ, ih ν] at hs
  linarith

/-- A small Lévy–Prokhorov distance controls the entire normalized Lipschitz test class. -/
private lemma boundedLipschitzDistance_le_of_lp_lt
    (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin k))) {ε : ℝ} (hε : 0 < ε)
    (hμν : levyProkhorovEDist μ.toMeasure ν.toMeasure < ENNReal.ofReal ε) :
    boundedLipschitzDistance μ ν ≤ 3 * ε := by
  apply boundedLipschitzDistance_le
  intro f hf hl
  apply abs_le.mpr
  have h₁ := integral_le_of_lp_lt μ ν f hf hl hε hμν
  have h₂ := integral_le_of_lp_lt ν μ f hf hl hε
    (by simpa only [levyProkhorovEDist_comm] using hμν)
  constructor <;> linarith

/-- Weak convergence controls the supremum, rather than merely each fixed test. -/
lemma tendsto_boundedLipschitzDistance_of_tendsto
    {μs : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin k))}
    {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin k))}
    (h : Tendsto μs atTop (𝓝 μ)) :
    Tendsto (fun n => boundedLipschitzDistance (μs n) μ) atTop (𝓝 0) := by
  have hLP := LevyProkhorov.continuous_ofMeasure_probabilityMeasure.tendsto μ |>.comp h
  have hd := tendsto_iff_dist_tendsto_zero.mp hLP
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : 0 < ε / 6 := by positivity
  filter_upwards [hd.eventually_lt_const he] with n hn
  have hreal : levyProkhorovDist (μs n).toMeasure μ.toMeasure < ε / 6 := hn
  have hext : levyProkhorovEDist (μs n).toMeasure μ.toMeasure < ENNReal.ofReal (ε / 6) := by
    apply (ENNReal.toReal_lt_toReal (levyProkhorovEDist_ne_top _ _) ENNReal.ofReal_ne_top).mp
    simpa only [levyProkhorovDist, ENNReal.toReal_ofReal he.le] using hreal
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (boundedLipschitzDistance_nonneg _ _)]
  exact (boundedLipschitzDistance_le_of_lp_lt _ _ he hext).trans_lt (by linarith)

/-- Rescaling an arbitrary bounded Lipschitz test reduces it to the normalized class. -/
private lemma scaled_integral_sub_le
    (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin k)))
    (f : EuclideanSpace ℝ (Fin k) →ᵇ ℝ) {L : ℝ≥0} (hl : LipschitzWith L f) :
    |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤
      max 1 (max ‖f‖ (L : ℝ)) * boundedLipschitzDistance μ ν := by
  let C := max 1 (max ‖f‖ (L : ℝ))
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hCf : ‖f‖ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCL : (L : ℝ) ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  let g : EuclideanSpace ℝ (Fin k) →ᵇ ℝ := C⁻¹ • f
  have hg : ‖g‖ ≤ 1 := by
    change ‖C⁻¹ • f‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hC)]
    exact (inv_mul_le_one₀ hC).mpr hCf
  have hgl : LipschitzWith 1 g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (C⁻¹ * f x) (C⁻¹ * f y) ≤ (1 : ℝ≥0) * dist x y
    rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hC)]
    have hb := hl.dist_le_mul x y
    rw [Real.dist_eq] at hb
    calc
      C⁻¹ * |f x - f y| ≤ C⁻¹ * ((L : ℝ) * dist x y) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hC.le)
      _ = (C⁻¹ * (L : ℝ)) * dist x y := by ring
      _ ≤ 1 * dist x y :=
        mul_le_mul_of_nonneg_right ((inv_mul_le_one₀ hC).mpr hCL) dist_nonneg
      _ = _ := by simp
  have hb := abs_integral_sub_le_boundedLipschitzDistance μ ν g hg hgl
  have heq : |(∫ x, g x ∂μ) - ∫ x, g x ∂ν| =
      C⁻¹ * |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| := by
    change |(∫ x, C⁻¹ • f x ∂μ) - ∫ x, C⁻¹ • f x ∂ν| = _
    rw [integral_smul, integral_smul, smul_eq_mul, smul_eq_mul, ← mul_sub, abs_mul,
      abs_of_pos (inv_pos.mpr hC)]
  rw [heq] at hb
  have hc := mul_le_mul_of_nonneg_left hb hC.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul] using hc

/-- Vanishing bounded-Lipschitz distance implies weak convergence. -/
lemma tendsto_of_tendsto_boundedLipschitzDistance
    {μs : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin k))}
    {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin k))}
    (h : Tendsto (fun n => boundedLipschitzDistance (μs n) μ) atTop (𝓝 0)) :
    Tendsto μs atTop (𝓝 μ) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro f hb ⟨L, hl⟩
  let g : EuclideanSpace ℝ (Fin k) →ᵇ ℝ :=
    ⟨⟨f, hl.continuous⟩, hb⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp_rw [Real.dist_eq]
  have he : Tendsto (fun n => max 1 (max ‖g‖ (L : ℝ)) *
      boundedLipschitzDistance (μs n) μ) atTop (𝓝 0) := by
    simpa using h.const_mul (max 1 (max ‖g‖ (L : ℝ)))
  exact squeeze_zero (fun _ => abs_nonneg _) (fun n => scaled_integral_sub_le (μs n) μ g hl) he

/-- Bounded Lipschitz integrals determine a finite-dimensional probability law.
This includes the empty block, which is useful in the cylinder-set argument. -/
lemma eq_of_bounded_lipschitz_integral_eq
    (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin k)))
    (h : ∀ f : EuclideanSpace ℝ (Fin k) →ᵇ ℝ, (∃ L, LipschitzWith L f) →
      (∫ x, f x ∂μ) = ∫ x, f x ∂ν) : μ = ν := by
  have hconv : Tendsto (fun _ : ℕ => μ) atTop (𝓝 ν) := by
    apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
    intro f hb ⟨L, hl⟩
    let g : EuclideanSpace ℝ (Fin k) →ᵇ ℝ := ⟨⟨f, hl.continuous⟩, hb⟩
    change Tendsto (fun _ : ℕ => ∫ x, g x ∂μ) atTop (𝓝 (∫ x, g x ∂ν))
    rw [h g ⟨L, hl⟩]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique tendsto_const_nhds hconv

/-- The distance vanishes on identical laws. -/
lemma boundedLipschitzDistance_self
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin k))) :
    boundedLipschitzDistance μ μ = 0 := by
  apply le_antisymm _ (boundedLipschitzDistance_nonneg _ _)
  apply boundedLipschitzDistance_le
  intro f _ _
  simp

/-- Symmetry of the finite-block bounded-Lipschitz distance. -/
lemma boundedLipschitzDistance_comm
    (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin k))) :
    boundedLipschitzDistance μ ν = boundedLipschitzDistance ν μ := by
  simp only [boundedLipschitzDistance, abs_sub_comm]

/-- Triangle inequality, also used to transfer Gaussian approximation bounds in the
thermodynamic limit. -/
lemma boundedLipschitzDistance_triangle
    (μ ν ρ : ProbabilityMeasure (EuclideanSpace ℝ (Fin k))) :
    boundedLipschitzDistance μ ρ ≤ boundedLipschitzDistance μ ν + boundedLipschitzDistance ν ρ := by
  apply boundedLipschitzDistance_le
  intro f hf hl
  calc
    |(∫ x, f x ∂μ) - ∫ x, f x ∂ρ| ≤
        |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| + |(∫ x, f x ∂ν) - ∫ x, f x ∂ρ| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add (abs_integral_sub_le_boundedLipschitzDistance μ ν f hf hl)
      (abs_integral_sub_le_boundedLipschitzDistance ν ρ f hf hl)

/-- The normalized test class separates probability measures. -/
lemma boundedLipschitzDistance_eq_zero_iff
    (μ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin k))) :
    boundedLipschitzDistance μ ν = 0 ↔ μ = ν := by
  constructor
  · intro h
    apply eq_of_bounded_lipschitz_integral_eq μ ν
    intro f ⟨L, hl⟩
    have hb := scaled_integral_sub_le μ ν f hl
    rw [h, mul_zero] at hb
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hb (abs_nonneg _)))
  · rintro rfl
    exact boundedLipschitzDistance_self μ

/-- See the proof of Theorem 3 in the paper: on `ℝ^k`, the bounded-Lipschitz
supremum tends to zero exactly when all bounded continuous test integrals converge. -/
theorem convergence_weak_tests (k : ℕ) (_hk : 1 ≤ k)
    (μs : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin k)))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin k))) :
    (Tendsto (fun n => boundedLipschitzDistance (μs n) μ) atTop (𝓝 0) ↔
      ∀ f : EuclideanSpace ℝ (Fin k) →ᵇ ℝ,
        Tendsto (fun n => ∫ x, f x ∂μs n) atTop (𝓝 (∫ x, f x ∂μ))) ∧
    (∀ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin k)),
      (∀ f : EuclideanSpace ℝ (Fin k) →ᵇ ℝ, (∃ L, LipschitzWith L f) →
        (∫ x, f x ∂ν) = ∫ x, f x ∂μ) → ν = μ) := by
  constructor
  · rw [← ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    exact ⟨tendsto_of_tendsto_boundedLipschitzDistance,
      tendsto_boundedLipschitzDistance_of_tendsto⟩
  · exact fun ν hν => eq_of_bounded_lipschitz_integral_eq ν μ hν

/-- See Subsection 6.3 of the paper: coordinatewise logarithm identifies the positive gap product
with a countable product of real lines, with their product topologies. -/
def gapSequenceLogHomeomorph : (ℤ → Ioi (0 : ℝ)) ≃ₜ (ℤ → ℝ) :=
  Homeomorph.piCongrRight fun _ => Real.expOrderIso.toHomeomorph.symm

/-- The logarithmic coordinates of the product homeomorphism are the usual real logarithms. -/
lemma gapSequenceLogHomeomorph_apply (u : ℤ → Ioi (0 : ℝ)) (j : ℤ) :
    gapSequenceLogHomeomorph u j = Real.log (u j) :=
  (Real.log_of_pos (u j).property).symm

/-- See Subsection 6.3 of the paper: the product sigma-algebra is precisely the product topology's
Borel sigma-algebra. -/
lemma gapSequence_borel :
    (inferInstance : MeasurableSpace (ℤ → Ioi (0 : ℝ))) = borel (ℤ → Ioi (0 : ℝ)) :=
  BorelSpace.measurable_eq

/-- See Subsection 6.3 of the paper: two-sided positive gap sequences form a Polish space. -/
lemma gapSequence_polishSpace : PolishSpace (ℤ → Ioi (0 : ℝ)) :=
  gapSequenceLogHomeomorph.isClosedEmbedding.polishSpace

/-- The finite-block consequence of the proof of Theorem 3:
bounded Lipschitz cylinder tests determine a law on two-sided real sequences. -/
lemma realSequence_eq_of_bounded_lipschitz_cylinders
    (μ ν : ProbabilityMeasure (ℤ → ℝ))
    (h : ∀ (k : ℕ) (labels : Fin k → ℤ) (f : EuclideanSpace ℝ (Fin k) →ᵇ ℝ),
      (∃ L, LipschitzWith L f) →
      (∫ u : ℤ → ℝ, f (WithLp.toLp 2 (fun i => u (labels i))) ∂μ) =
        ∫ u : ℤ → ℝ, f (WithLp.toLp 2 (fun i => u (labels i))) ∂ν) : μ = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  let P := fun I : Finset ℤ => μ.toMeasure.map I.restrict
  have hμ : IsProjectiveLimit μ.toMeasure P := fun _ => rfl
  have hν : IsProjectiveLimit ν.toMeasure P := by
    intro I
    let e : (I → ℝ) ≃ᵐ EuclideanSpace ℝ (Fin (Fintype.card I)) :=
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card I) => ℝ) (Fintype.equivFin I)).trans
        (MeasurableEquiv.toLp 2 (Fin (Fintype.card I) → ℝ))
    let p := fun u : ℤ → ℝ => e (I.restrict u)
    have hp : Measurable p := e.measurable.comp (Finset.measurable_restrict I)
    have hpval (u : ℤ → ℝ) : p u =
        WithLp.toLp 2 (fun i => u ((Fintype.equivFin I).symm i : ℤ)) := by
      apply WithLp.ofLp_injective
      funext i
      change Equiv.piCongrLeft (fun _ : Fin (Fintype.card I) => ℝ)
        (Fintype.equivFin I) (I.restrict u) i = _
      simp [Equiv.piCongrLeft_apply, Finset.restrict_def]
    have hm : μ.map p = ν.map p := by
      apply eq_of_bounded_lipschitz_integral_eq
      intro f hf
      rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
        integral_map hp.aemeasurable f.continuous.aestronglyMeasurable,
        integral_map hp.aemeasurable f.continuous.aestronglyMeasurable]
      simp_rw [hpval]
      exact h (Fintype.card I) (fun i => ((Fintype.equivFin I).symm i : ℤ)) f hf
    have hm' := congrArg ProbabilityMeasure.toMeasure hm
    change μ.toMeasure.map p = ν.toMeasure.map p at hm'
    apply e.measurableEmbedding.map_injective
    change (ν.toMeasure.map I.restrict).map e = (μ.toMeasure.map I.restrict).map e
    have hr : Measurable (I.restrict : (ℤ → ℝ) → (I → ℝ)) := Finset.measurable_restrict I
    rw [Measure.map_map e.measurable hr, Measure.map_map e.measurable hr]
    exact hm'.symm
  exact hμ.unique hν

/-- Bounded Lipschitz cylinder tests determine a law on the two-sided positive gap carrier
of Subsection 6.3. No regularity of a putative infinite-volume gap law is required. -/
theorem gapSequence_eq_of_bounded_lipschitz_cylinders
    (μ ν : ProbabilityMeasure (ℤ → Ioi (0 : ℝ)))
    (h : ∀ (k : ℕ) (labels : Fin k → ℤ) (f : EuclideanSpace ℝ (Fin k) →ᵇ ℝ),
      (∃ L, LipschitzWith L f) →
      (∫ u : ℤ → Ioi (0 : ℝ), f (WithLp.toLp 2 (fun i => (u (labels i) : ℝ))) ∂μ) =
        ∫ u : ℤ → Ioi (0 : ℝ), f (WithLp.toLp 2 (fun i => (u (labels i) : ℝ))) ∂ν) : μ = ν := by
  let c := fun u : ℤ → Ioi (0 : ℝ) => fun i => (u i : ℝ)
  have hc : MeasurableEmbedding c := by
    have hs : MeasurableSet {u : ℤ → ℝ | ∀ i, 0 < u i} :=
      by
        simp only [ofPred_forall]
        exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)
    exact (MeasurableEmbedding.subtype_coe hs).comp
      MeasurableEquiv.subtypePiEquivPi.symm.measurableEmbedding
  have hm : μ.map c = ν.map c := by
    apply realSequence_eq_of_bounded_lipschitz_cylinders
    intro k labels f hf
    have hp : Measurable (fun u : ℤ → ℝ =>
        f (WithLp.toLp 2 (fun i => u (labels i)))) :=
      f.continuous.measurable.comp <| (WithLp.measurable_toLp 2 _).comp <|
        Measurable.of_eval (fun i => measurable_pi_apply (labels i))
    rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
      integral_map hc.measurable.aemeasurable hp.aestronglyMeasurable,
      integral_map hc.measurable.aemeasurable hp.aestronglyMeasurable]
    exact h k labels f hf
  apply ProbabilityMeasure.toMeasure_injective
  exact hc.map_injective (congrArg ProbabilityMeasure.toMeasure hm)

end Riesz2
