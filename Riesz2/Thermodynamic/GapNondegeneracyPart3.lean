/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.GapNondegeneracy
public import Riesz1.ToMathlib.VarianceThreeTerm

/-!
# Moment passage for fixed-block nondegeneracy

The truncation passage in the proof of Theorem 3 uses the finite covariance estimate and
the ordinary-gap Cauchy estimate as hypotheses.
-/

public section
noncomputable section

open MeasureTheory Filter Set Finset
open scoped ENNReal Topology BigOperators InnerProductSpace BoundedContinuousFunction

namespace Riesz2.GapNondegeneracy

local notation "Gaps" => (ℤ → Ioi (0 : ℝ))

/-- The fourth power of a finite weighted sum is controlled by the sum of
coordinate fourth powers. This includes the empty block and zero weights. -/
theorem weighted_sum_fourth_le (k : ℕ) (a x : Fin k → ℝ) :
    ((∑ i, a i * x i) ^ 2) ^ 2 ≤
      (∑ i, a i ^ 2) ^ 2 * (k : ℝ) * ∑ i, (x i ^ 2) ^ 2 := by
  have h₁ := sum_mul_sq_le_sq_mul_sq univ a x
  have h₂ := sum_mul_sq_le_sq_mul_sq univ (fun _ : Fin k => (1 : ℝ))
    (fun i => x i ^ 2)
  simp only [one_mul, one_pow, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h₂
  calc
    _ ≤ ((∑ i, a i ^ 2) * ∑ i, x i ^ 2) ^ 2 :=
      pow_le_pow_left₀ (sq_nonneg _) h₁ 2
    _ = (∑ i, a i ^ 2) ^ 2 * (∑ i, x i ^ 2) ^ 2 := mul_pow _ _ _
    _ ≤ (∑ i, a i ^ 2) ^ 2 * ((k : ℝ) * ∑ i, (x i ^ 2) ^ 2) :=
      mul_le_mul_of_nonneg_left h₂ (sq_nonneg _)
    _ = _ := by ring

/-- A coordinate fourth-moment bound is an integrability assertion,
before any real-valued expectation is used. -/
theorem gap_fourth_integrable_internal (q : ProbabilityMeasure Gaps) (i : ℤ)
    {D : ℝ} (hD : 0 ≤ D)
    (h : (∫⁻ y : Gaps, ENNReal.ofReal ((y i : ℝ) ^ (4 : ℝ)) ∂q) ≤
      ENNReal.ofReal D) :
    Integrable (fun y : Gaps => ((y i : ℝ) ^ 2) ^ 2) q ∧
      (∫ y : Gaps, ((y i : ℝ) ^ 2) ^ 2 ∂q) ≤ D := by
  have hm : Measurable (fun y : Gaps => ((y i : ℝ) ^ 2) ^ 2) := by fun_prop
  have he (y : Gaps) : (y i : ℝ) ^ (4 : ℝ) = ((y i : ℝ) ^ 2) ^ 2 := by
    rw [show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast]
    ring
  simp_rw [he] at h
  have hi : Integrable (fun y : Gaps => ((y i : ℝ) ^ 2) ^ 2) q :=
    (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
      (ae_of_all _ fun y => sq_nonneg _)).mp (h.trans_lt ENNReal.ofReal_lt_top).ne
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y => sq_nonneg _)
    hm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal hD h

/-- Uniform coordinate fourth moments control every weighted block's fourth
moment. This is the domination needed for the truncation argument. -/
theorem weighted_block_fourth_bound_internal (q : ProbabilityMeasure Gaps)
    (k : ℕ) (a : EuclideanSpace ℝ (Fin k)) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ i : Fin k,
      (∫⁻ y : Gaps, ENNReal.ofReal ((y i.val : ℝ) ^ (4 : ℝ)) ∂q) ≤
        ENNReal.ofReal D) :
    MemLp (fun y : Gaps => (∑ i, a i * (y i.val : ℝ)) ^ 2) 2 q ∧
      (∫ y : Gaps, ((∑ i, a i * (y i.val : ℝ)) ^ 2) ^ 2 ∂q) ≤
        (∑ i, a i ^ 2) ^ 2 * (k : ℝ) * ((k : ℝ) * D) := by
  let B := (∑ i, a i ^ 2) ^ 2 * (k : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hi (i : Fin k) := gap_fourth_integrable_internal q i.val hD0 (hD i)
  have hsum : Integrable (fun y : Gaps => ∑ i : Fin k, ((y i.val : ℝ) ^ 2) ^ 2) q :=
    integrable_finsetSum _ fun i _ => (hi i).1
  have hdom (y : Gaps) : ((∑ i, a i * (y i.val : ℝ)) ^ 2) ^ 2 ≤
      B * ∑ i : Fin k, ((y i.val : ℝ) ^ 2) ^ 2 :=
    weighted_sum_fourth_le k (fun i => a i) (fun i => (y i.val : ℝ))
  have hm : Continuous (fun y : Gaps => ∑ i, a i * (y i.val : ℝ)) := by fun_prop
  have hg : Integrable (fun y : Gaps => ((∑ i, a i * (y i.val : ℝ)) ^ 2) ^ 2) q := by
    apply (hsum.const_mul B).mono' ((hm.pow 2).pow 2).measurable.aestronglyMeasurable
    exact ae_of_all _ fun y => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hdom y
  refine ⟨(memLp_two_iff_integrable_sq (hm.pow 2).measurable.aestronglyMeasurable).mpr hg, ?_⟩
  calc
    _ ≤ ∫ y : Gaps, B * ∑ i : Fin k, ((y i.val : ℝ) ^ 2) ^ 2 ∂q :=
      integral_mono hg (hsum.const_mul B) hdom
    _ = B * ∑ i : Fin k, ∫ y : Gaps, ((y i.val : ℝ) ^ 2) ^ 2 ∂q := by
      rw [integral_const_mul, integral_finsetSum _ fun i _ => (hi i).1]
    _ ≤ B * ∑ _i : Fin k, D :=
      mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => (hi i).2) hB
    _ = _ := by simp [B]

/-- See the proof of Theorem 3 in the paper: uniform fourth gap
moments pass the first and second moments of every weighted block to every
weak limit. No density assumption on the limit is used. -/
theorem weighted_block_moments_tendsto_internal (p : Parameters) (V : ℕ → ℕ+)
    (hV : ∀ n, 2 ≤ (V n : ℕ)) (q : ProbabilityMeasure Gaps)
    (hq : Tendsto (fun n => periodicGapLaw p (V n)) atTop (𝓝 q))
    (k : ℕ) (a : EuclideanSpace ℝ (Fin k)) :
    let A := fun y : Gaps => ∑ i : Fin k, a i * (y i.val : ℝ)
    (∀ n, MemLp A 2 (periodicGapLaw p (V n))) ∧ MemLp A 2 q ∧
      Tendsto (fun n => ∫ y, A y ∂periodicGapLaw p (V n)) atTop (𝓝 (∫ y, A y ∂q)) ∧
      Tendsto (fun n => ∫ y, (A y) ^ 2 ∂periodicGapLaw p (V n))
        atTop (𝓝 (∫ y, (A y) ^ 2 ∂q)) := by
  intro A
  obtain ⟨D, hD, hf, hqD⟩ := periodicGapLaw_limit_moment_bound p V hV q hq 4 (by norm_num)
  have hμ4 (n) := weighted_block_fourth_bound_internal (periodicGapLaw p (V n)) k a hD.le
    (fun i => (le_add_of_nonneg_right (by positivity)).trans (hf (V n) (hV n) i.val))
  have hq4 := weighted_block_fourth_bound_internal q k a hD.le
    (fun i => (le_add_of_nonneg_right (by positivity)).trans (hqD i.val))
  have hA : Continuous A := by dsimp [A]; fun_prop
  have hμ2 (n) : MemLp A 2 (periodicGapLaw p (V n)) :=
    (memLp_two_iff_integrable_sq hA.measurable.aestronglyMeasurable).mpr
      ((hμ4 n).1.integrable (by norm_num))
  have hq2 : MemLp A 2 q :=
    (memLp_two_iff_integrable_sq hA.measurable.aestronglyMeasurable).mpr
      (hq4.1.integrable (by norm_num))
  let C := (∑ i, a i ^ 2) ^ 2 * (k : ℝ) * ((k : ℝ) * D)
  have hbound (n) : (∫ y, A y ^ 2 ∂periodicGapLaw p (V n)) ≤ 1 + C := by
    have hb := integral_mono (hμ2 n).integrable_sq
      ((integrable_const (1 : ℝ)).add (hμ4 n).1.integrable_sq)
      (fun y : Gaps => show A y ^ 2 ≤ 1 + (A y ^ 2) ^ 2 by
        nlinarith [sq_nonneg (A y ^ 2 - 1)])
    simp only [Pi.add_apply] at hb
    rw [integral_add (integrable_const (1 : ℝ)) (hμ4 n).1.integrable_sq] at hb
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hb
    have hb4 := (hμ4 n).2
    dsimp only [C]
    linarith
  have hw := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hq
  exact ⟨hμ2, hq2,
    WeakMomentTruncation.integral_tendsto_of_uniform_second_moment_internal
      hw hA hμ2 hq2 (Eventually.of_forall hbound),
    WeakMomentTruncation.integral_tendsto_of_uniform_second_moment_internal
      hw (hA.pow 2) (fun n => (hμ4 n).1) hq4.1
      (Eventually.of_forall fun n => (hμ4 n).2)⟩

/-- See the proof of Theorem 3 in the paper: centered second moments
converge after fourth-moment truncation, and all variances are finite. -/
theorem weighted_block_variance_tendsto_internal (p : Parameters) (V : ℕ → ℕ+)
    (hV : ∀ n, 2 ≤ (V n : ℕ)) (q : ProbabilityMeasure Gaps)
    (hq : Tendsto (fun n => periodicGapLaw p (V n)) atTop (𝓝 q))
    (k : ℕ) (a : EuclideanSpace ℝ (Fin k)) :
    let A := fun y : Gaps => ∑ i : Fin k, a i * (y i.val : ℝ)
    (∀ n, MemLp A 2 (periodicGapLaw p (V n))) ∧ MemLp A 2 q ∧
      Tendsto (fun n => ∫ y, (A y - ∫ z, A z ∂periodicGapLaw p (V n)) ^ 2
        ∂periodicGapLaw p (V n)) atTop (𝓝 (∫ y, (A y - ∫ z, A z ∂q) ^ 2 ∂q)) := by
  intro A
  obtain ⟨hμ, hν, hm, hs⟩ := weighted_block_moments_tendsto_internal p V hV q hq k a
  refine ⟨hμ, hν, ?_⟩
  have hv := hs.sub (hm.pow 2)
  have he (μ : ProbabilityMeasure Gaps) (h : MemLp A 2 μ) :
      (∫ y, (A y - ∫ z, A z ∂μ) ^ 2 ∂μ) =
        (∫ y, A y ^ 2 ∂μ) - (∫ y, A y ∂μ) ^ 2 := by
    rw [← ProbabilityTheory.variance_eq_integral h.aemeasurable,
      ProbabilityTheory.variance_eq_sub h]
    rfl
  simp_rw [he q hν, he _ (hμ _)]
  exact hv

/-- Internal finite-volume transport for the proof of Theorem 3. The hypothesis is exactly the ordinary
Gibbs covariance estimate, and the conclusion uses its periodic pushforward. -/
theorem periodic_covariance_of_gibbs_internal (p : Parameters) (k : ℕ) (c : ℝ)
    (hfinite : ∀ (N : ℕ+), 2 * k + 2 ≤ (N : ℕ) →
      ∀ u : EuclideanSpace ℝ (Fin k),
        let A := fun X : Riesz1.Configuration N => ∑ i : Fin k, u i * gap X i.val
        MemLp A 2 (gibbsMeasure p N) ∧
          c * ‖u‖ ^ 2 ≤ ∫ X, (A X - ∫ Z, A Z ∂gibbsMeasure p N) ^ 2 ∂gibbsMeasure p N) :
    ∀ (N : ℕ+), 2 * k + 2 ≤ (N : ℕ) → ∀ u : EuclideanSpace ℝ (Fin k),
      let A := fun y : Gaps => ∑ i : Fin k, u i * (y i.val : ℝ)
      MemLp A 2 (periodicGapLaw p N) ∧
        c * ‖u‖ ^ 2 ≤ ∫ y, (A y - ∫ z, A z ∂periodicGapLaw p N) ^ 2
          ∂periodicGapLaw p N := by
  intro N hN u A
  obtain ⟨hi, hb⟩ := hfinite N hN u
  have hm : Continuous A := by dsimp [A]; fun_prop
  constructor
  · rw [periodicGapLaw_toMeasure]
    exact (memLp_map_measure_iff hm.measurable.aestronglyMeasurable
      (measurable_periodicGapSequence N).aemeasurable).mpr hi
  · rw [integral_periodicGapLaw p N hm.measurable,
      integral_periodicGapLaw p N (f := fun y =>
        (A y - ∫ X, A (periodicGapSequence X) ∂gibbsMeasure p N) ^ 2)
        (show Continuous (fun y =>
          (A y - ∫ X, A (periodicGapSequence X) ∂gibbsMeasure p N) ^ 2) from
          (hm.sub continuous_const).pow 2).measurable]
    exact hb

/-- See the proof of Theorem 3 in the paper, internal passage of the
finite covariance estimate to the weak limit. The same positive constant
works for every finite volume and every direction in the limiting block. -/
theorem common_covariance_lower_bound_internal
    (hfinite : ∀ (p : Parameters) (k : ℕ), 1 ≤ k →
      ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ+), 2 * k + 2 ≤ (N : ℕ) →
        ∀ u : EuclideanSpace ℝ (Fin k),
          let A := fun X : Riesz1.Configuration N => ∑ i : Fin k, u i * gap X i.val
          MemLp A 2 (gibbsMeasure p N) ∧
            c * ‖u‖ ^ 2 ≤ ∫ X, (A X - ∫ Z, A Z ∂gibbsMeasure p N) ^ 2 ∂gibbsMeasure p N)
    (p : Parameters) (q : ProbabilityMeasure Gaps)
    (hq : Tendsto (fun n : ℕ => periodicGapLaw p n.succPNat) atTop (𝓝 q))
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ c : ℝ, 0 < c ∧
      (∀ (N : ℕ+), 2 * k + 2 ≤ (N : ℕ) → ∀ u : EuclideanSpace ℝ (Fin k),
        let A := fun y : Gaps => ∑ i : Fin k, u i * (y i.val : ℝ)
        MemLp A 2 (periodicGapLaw p N) ∧
          c * ‖u‖ ^ 2 ≤ ∫ y, (A y - ∫ z, A z ∂periodicGapLaw p N) ^ 2
            ∂periodicGapLaw p N) ∧
      (∀ u : EuclideanSpace ℝ (Fin k),
        let A := fun y : Gaps => ∑ i : Fin k, u i * (y i.val : ℝ)
        MemLp A 2 q ∧ c * ‖u‖ ^ 2 ≤ ∫ y, (A y - ∫ z, A z ∂q) ^ 2 ∂q) := by
  obtain ⟨c, hc, hf⟩ := hfinite p k hk
  have hp := periodic_covariance_of_gibbs_internal p k c hf
  refine ⟨c, hc, hp, fun u => ?_⟩
  let V : ℕ → ℕ+ := fun n => (n + (2 * k + 1)).succPNat
  have hV (n) : 2 ≤ (V n : ℕ) := by change 2 ≤ n + (2 * k + 1) + 1; omega
  have hqV : Tendsto (fun n => periodicGapLaw p (V n)) atTop (𝓝 q) :=
    (tendsto_add_atTop_iff_nat (2 * k + 1)).mpr hq
  obtain ⟨_, hi, ht⟩ := weighted_block_variance_tendsto_internal p V hV q hqV k u
  refine ⟨hi, ge_of_tendsto ht (Eventually.of_forall fun n => ?_)⟩
  exact (hp (V n) (by change 2 * k + 2 ≤ n + (2 * k + 1) + 1; omega) u).2

local notation "blockProj" => (fun (k : ℕ) (y : Gaps) =>
  (WithLp.toLp 2 (fun i : Fin k => (y (Fin.val i : ℤ) : ℝ)) : EuclideanSpace ℝ (Fin k)))
local notation "blockLaw" => (fun (q : ProbabilityMeasure Gaps) (k : ℕ) =>
  ProbabilityMeasure.map q (blockProj k))

/-- The actual Euclidean block projection sends a weighted gap sum to its
inner-product observable, with finite extended variance. -/
theorem block_variance_transport_internal (q : ProbabilityMeasure Gaps)
    (k : ℕ) (u : EuclideanSpace ℝ (Fin k))
    (h : MemLp (fun y : Gaps => ∑ i : Fin k, u i * (y i.val : ℝ)) 2 q) :
    ∃ hi : Integrable (fun x : EuclideanSpace ℝ (Fin k) => ⟪u, x⟫_ℝ) (blockLaw q k),
      Riesz1.variance (blockLaw q k).toMeasure (fun x => ⟪u, x⟫_ℝ) hi =
        ENNReal.ofReal (∫ y : Gaps,
          ((∑ i : Fin k, u i * (y i.val : ℝ)) -
            ∫ z : Gaps, ∑ i : Fin k, u i * (z i.val : ℝ) ∂q) ^ 2 ∂q) ∧
      Riesz1.variance (blockLaw q k).toMeasure (fun x => ⟪u, x⟫_ℝ) hi < ∞ := by
  let A := fun y : Gaps => ∑ i : Fin k, u i * (y i.val : ℝ)
  have he (y : Gaps) : ⟪u, blockProj k y⟫_ℝ = A y := by
    simp [PiLp.inner_apply, A, mul_comm]
  have hm : Continuous (blockProj k) :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i =>
      continuous_subtype_val.comp (continuous_apply _))
  have hinner : Continuous (fun x : EuclideanSpace ℝ (Fin k) => ⟪u, x⟫_ℝ) := by fun_prop
  have hmem : MemLp (fun x : EuclideanSpace ℝ (Fin k) => ⟪u, x⟫_ℝ) 2
      (blockLaw q k) := by
    change MemLp _ 2 (q.toMeasure.map (blockProj k))
    apply (memLp_map_measure_iff hinner.measurable.aestronglyMeasurable
      hm.measurable.aemeasurable).mpr
    simpa only [Function.comp_def, he] using h
  refine ⟨hmem.integrable (by norm_num), ?_, ?_⟩
  · unfold Riesz1.variance
    change (∫⁻ x, ENNReal.ofReal ((⟪u, x⟫_ℝ - ∫ z, ⟪u, z⟫_ℝ
      ∂q.toMeasure.map (blockProj k)) ^ 2) ∂q.toMeasure.map (blockProj k)) = _
    rw [integral_map hm.measurable.aemeasurable hinner.measurable.aestronglyMeasurable]
    rw [lintegral_map (by fun_prop) hm.measurable]
    simp_rw [he]
    exact (ofReal_integral_eq_lintegral_ofReal
      (h.sub (memLp_const _)).integrable_sq (ae_of_all _ fun y => sq_nonneg _)).symm
  · exact (Riesz1.variance_ne_top_of_memLp _ hmem).lt_top

/-- The nondegeneracy conclusion in the proof of Theorem 3 holds for every
weak limit, assuming the finite-volume covariance bound. The conclusion
includes finite-volume log-concave densities for the total variation argument. -/
theorem block_nondegeneracy_from_finite_internal
    (hfinite : ∀ (p : Parameters) (k : ℕ), 1 ≤ k →
      ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ+), 2 * k + 2 ≤ (N : ℕ) →
        ∀ u : EuclideanSpace ℝ (Fin k),
          let A := fun X : Riesz1.Configuration N => ∑ i : Fin k, u i * gap X i.val
          MemLp A 2 (gibbsMeasure p N) ∧
            c * ‖u‖ ^ 2 ≤ ∫ X, (A X - ∫ Z, A Z ∂gibbsMeasure p N) ^ 2 ∂gibbsMeasure p N)
    (p : Parameters) (q : ProbabilityMeasure Gaps)
    (hq : Tendsto (fun n : ℕ => periodicGapLaw p n.succPNat) atTop (𝓝 q))
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ c : ℝ, 0 < c ∧
      (∀ (N : ℕ+), 2 * k + 2 ≤ (N : ℕ) → ∀ u : EuclideanSpace ℝ (Fin k),
        ∃ hi : Integrable (fun x : EuclideanSpace ℝ (Fin k) => ⟪u, x⟫_ℝ)
          (blockLaw (periodicGapLaw p N) k),
        ENNReal.ofReal (c * ‖u‖ ^ 2) ≤ Riesz1.variance
          (blockLaw (periodicGapLaw p N) k).toMeasure (fun x => ⟪u, x⟫_ℝ) hi) ∧
      (∀ u : EuclideanSpace ℝ (Fin k),
        ∃ hi : Integrable (fun x : EuclideanSpace ℝ (Fin k) => ⟪u, x⟫_ℝ) (blockLaw q k),
        ENNReal.ofReal (c * ‖u‖ ^ 2) ≤
          Riesz1.variance (blockLaw q k).toMeasure (fun x => ⟪u, x⟫_ℝ) hi) ∧
      (∀ (N : ℕ+), k < (N : ℕ) → ∃ f : EuclideanSpace ℝ (Fin k) → ℝ,
        Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∫⁻ x, ENNReal.ofReal (f x)) = 1 ∧
        ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) ∧
        (blockLaw (periodicGapLaw p N) k).toMeasure =
          volume.withDensity (fun x => ENNReal.ofReal (f x))) := by
  obtain ⟨c, hc, hf, hlim⟩ := common_covariance_lower_bound_internal hfinite p q hq k hk
  refine ⟨c, hc, ?_, ?_, fun N hN => periodicGapLaw_block_logConcave_density p N k hk hN⟩
  · intro N hN u
    obtain ⟨hi, he, _⟩ := block_variance_transport_internal (periodicGapLaw p N) k u (hf N hN u).1
    exact ⟨hi, he.symm ▸ ENNReal.ofReal_le_ofReal (hf N hN u).2⟩
  · intro u
    obtain ⟨hi, he, _⟩ := block_variance_transport_internal q k u (hlim u).1
    exact ⟨hi, he.symm ▸ ENNReal.ofReal_le_ofReal (hlim u).2⟩

/-- The Cauchy estimate and finite-volume covariance bound give the
nondegeneracy conclusions in the proof of Theorem 3: a unique two-sided
gap limit, a common positive lower constant for each block and finite
log-concave densities for every volume larger than the block. -/
theorem convergence_nondegeneracy_from_predecessors_internal
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
    (hfinite : ∀ (p : Parameters) (k : ℕ), 1 ≤ k →
      ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ+), 2 * k + 2 ≤ (N : ℕ) →
        ∀ u : EuclideanSpace ℝ (Fin k),
          let A := fun X : Riesz1.Configuration N => ∑ i : Fin k, u i * gap X i.val
          MemLp A 2 (gibbsMeasure p N) ∧
            c * ‖u‖ ^ 2 ≤ ∫ X, (A X - ∫ Z, A Z ∂gibbsMeasure p N) ^ 2 ∂gibbsMeasure p N)
    (p : Parameters) :
    ∃! q : ProbabilityMeasure Gaps,
      Tendsto (fun n : ℕ => periodicGapLaw p n.succPNat) atTop (𝓝 q) ∧
      ∀ k : ℕ, 1 ≤ k → ∃ c : ℝ, 0 < c ∧
        (∀ (N : ℕ+), 2 * k + 2 ≤ (N : ℕ) → ∀ u : EuclideanSpace ℝ (Fin k),
          ∃ hi : Integrable (fun x : EuclideanSpace ℝ (Fin k) => ⟪u, x⟫_ℝ)
            (blockLaw (periodicGapLaw p N) k),
          ENNReal.ofReal (c * ‖u‖ ^ 2) ≤ Riesz1.variance
            (blockLaw (periodicGapLaw p N) k).toMeasure (fun x => ⟪u, x⟫_ℝ) hi) ∧
        (∀ u : EuclideanSpace ℝ (Fin k),
          ∃ hi : Integrable (fun x : EuclideanSpace ℝ (Fin k) => ⟪u, x⟫_ℝ) (blockLaw q k),
          ENNReal.ofReal (c * ‖u‖ ^ 2) ≤
            Riesz1.variance (blockLaw q k).toMeasure (fun x => ⟪u, x⟫_ℝ) hi) ∧
        (∀ (N : ℕ+), k < (N : ℕ) → ∃ f : EuclideanSpace ℝ (Fin k) → ℝ,
          Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∫⁻ x, ENNReal.ofReal (f x)) = 1 ∧
          ConcaveOn ℝ {x | 0 < f x} (fun x => Real.log (f x)) ∧
          (blockLaw (periodicGapLaw p N) k).toMeasure =
            volume.withDensity (fun x => ENNReal.ofReal (f x))) := by
  obtain ⟨q, hq, _⟩ := convergence_gap_limit_from_cauchy_internal hcomparison p
  refine ⟨q, ⟨hq.1, fun k hk => block_nondegeneracy_from_finite_internal hfinite p q hq.1 k hk⟩,
    fun q' hq' => tendsto_nhds_unique hq'.1 hq.1⟩

end Riesz2.GapNondegeneracy
