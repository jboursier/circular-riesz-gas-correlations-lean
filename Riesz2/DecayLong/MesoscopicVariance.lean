/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Bridges.GapFluctuations
public import Riesz2.Frozen.FiniteGapBlock
import Riesz2.Sanity.FiniteLaws
public import Riesz1.Frozen.Variance
public import Riesz1.Rigidity.GapLawMoments
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Finite gap moments and mesoscopic variance normalization

Finite moments and normalization for Lemma 5.19. The block is the sum of
`finiteGapBlock`, and its extended variance is `Riesz1.variance`.
The variance limit follows from second-moment convergence of the normalized
gap laws in `MesoscopicVariancePart2` and `MesoscopicVariancePart3`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Riesz2.MesoscopicVariance

/-- See Corollary 1.1 of the paper, used in
the proof of Theorem 1: the limiting variance
is strictly positive throughout the full long-range parameter interval. -/
theorem limiting_variance_pos (β : InverseTemperature) (s : Riesz1.RieszExponent) :
    0 < Riesz1.countVariance (longParameters β s) := by
  have hs : 0 < s.val := s.property.1
  have hβ : 0 < β.val := β.property
  have hangle : 0 < Real.pi * s.val / 2 := by positivity
  have hhalf : Real.pi * s.val / 2 < Real.pi / 2 := by
    nlinarith [s.property.2, Real.pi_pos]
  change 0 < Real.cos (Real.pi * s.val / 2) / Real.sin (Real.pi * s.val / 2) /
    (2 * β.val * Real.pi * s.val)
  exact div_pos
    (div_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hhalf⟩)
      (Real.sin_pos_of_mem_Ioo ⟨hangle, by linarith [Real.pi_pos]⟩))
    (by positivity)

/-- See Subsection 1.7 and Subsection 5.7 of the paper: the sum of the block is
exactly the existing companion span. This bridge includes full-cycle
blocks and blocks longer than a period. -/
theorem finiteGapBlock_sum_eq_blockLength {N K : ℕ+} (X : Riesz1.Configuration N) :
    (∑ j : Fin (K : ℕ), finiteGapBlock X j) = Riesz1.blockLength X 0 K := by
  change (∑ j : Fin (K : ℕ), Riesz1.gap X (j.val : ℤ)) = _
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => Riesz1.gap X (j : ℤ)) (K : ℕ)]
  simpa only [zero_add] using (Riesz1.blockLength_eq_sum X 0 K).symm

/-- See Subsection 5.7 of the paper: every finite block has all finite moments.
The estimate uses bounded physical gaps and the actual Gibbs probability.
It is valid even for a singleton system. -/
theorem finiteGapBlock_sum_memLp (p : Parameters) (N K : ℕ+) (q : ℝ≥0∞) :
    MemLp (fun X : Riesz1.Configuration N => ∑ j : Fin (K : ℕ), finiteGapBlock X j)
      q (gibbsMeasure p N) := by
  have := FrozenSanity.gibbsMeasure_probability p N
  apply memLp_finsetSum
  intro j _
  apply MemLp.of_bound (C := (N : ℝ))
  · exact (Riesz1.measurable_gap (j.val : ℤ)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun X => by
      change ‖Riesz1.gap X (j.val : ℤ)‖ ≤ (N : ℝ)
      rw [Real.norm_eq_abs, abs_of_pos (Riesz1.gap_pos X _)]
      exact Riesz1.gap_le_N X _

/-- See Subsection 5.7 of the paper: first-moment validity for the finite
block sum, including all positive particle and block sizes. -/
theorem integrable_finiteGapBlock_sum (p : Parameters) (N K : ℕ+) :
    Integrable (fun X : Riesz1.Configuration N => ∑ j : Fin (K : ℕ), finiteGapBlock X j)
      (gibbsMeasure p N) := by
  have := FrozenSanity.gibbsMeasure_probability p N
  exact (finiteGapBlock_sum_memLp p N K 2).integrable (by norm_num)

/-- See Lemma 5.19, the
centering identity: a block of `K` microscopic gaps has expectation `K`.
This reuses the companion first-moment theorem. -/
theorem integral_finiteGapBlock_sum (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N K : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    (∫ X : Riesz1.Configuration N, ∑ j : Fin (K : ℕ), finiteGapBlock X j
      ∂gibbsMeasure (ofLong β s) N) = (K : ℝ) := by
  simp_rw [finiteGapBlock_sum_eq_blockLength]
  rw [gibbsMeasure_ofLong]
  exact Riesz1.integral_blockLength_gibbsMeasure (longParameters β s) N hN 0 K

/-- See Subsection 5.7 of the paper: the block variance is finite, and its real
value is the centered square integral. Integrability is proved before
converting the extended integral to a real value. -/
theorem finiteGapBlock_variance_finite (p : Parameters) (N K : ℕ+) :
    let S := fun X : Riesz1.Configuration N => ∑ j : Fin (K : ℕ), finiteGapBlock X j
    let h := integrable_finiteGapBlock_sum p N K
    Riesz1.variance (gibbsMeasure p N) S h < ⊤ ∧
      (Riesz1.variance (gibbsMeasure p N) S h).toReal =
        ∫ X, (S X - ∫ Y, S Y ∂gibbsMeasure p N) ^ 2 ∂gibbsMeasure p N := by
  have := FrozenSanity.gibbsMeasure_probability p N
  dsimp only
  have hmem := finiteGapBlock_sum_memLp p N K 2
  have hi := (hmem.sub (memLp_const
    (∫ X : Riesz1.Configuration N, ∑ j : Fin (K : ℕ), finiteGapBlock X j
      ∂gibbsMeasure p N))).integrable_sq
  have he := ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun X => sq_nonneg
      ((∑ j : Fin (K : ℕ), finiteGapBlock X j) -
        ∫ Y, ∑ j : Fin (K : ℕ), finiteGapBlock Y j ∂gibbsMeasure p N))
  simp only [Pi.sub_apply] at he
  unfold Riesz1.variance
  rw [← he]
  exact ⟨ENNReal.ofReal_lt_top, ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)⟩

/-- See Lemma 5.19, exact
normalization: `V_N(K)/K^s` is the second moment of the centered block
divided by `K^(s/2)`. All power bases are strictly positive. -/
theorem finiteGapBlock_normalized_second_moment
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (N K : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    let μ := gibbsMeasure (ofLong β s) N
    let S := fun X : Riesz1.Configuration N => ∑ j : Fin (K : ℕ), finiteGapBlock X j
    let h := integrable_finiteGapBlock_sum (ofLong β s) N K
    (Riesz1.variance μ S h).toReal / (K : ℝ) ^ s.val =
      ∫ X, ((S X - (K : ℝ)) / (K : ℝ) ^ (s.val / 2)) ^ 2 ∂μ := by
  dsimp only
  rw [(finiteGapBlock_variance_finite (ofLong β s) N K).2,
    integral_finiteGapBlock_sum β s N K hN]
  have hpow : ((K : ℝ) ^ (s.val / 2)) ^ 2 = (K : ℝ) ^ s.val := by
    rw [← Real.rpow_two, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ K)]
    congr 1
    ring
  simp_rw [div_pow, hpow]
  exact (integral_div _ _).symm

/-- Assembly of the variance limit of Lemma 5.19 from finite moments,
normalization and second-moment convergence of the normalized block laws. -/
theorem variance_limit_of_normalized_moments_internal
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (N K : ℕ → ℕ+)
    (hN : ∀ n, 2 ≤ (N n : ℕ))
    (hsecond : Tendsto (fun n =>
      ∫ X : Riesz1.Configuration (N n),
        (((∑ j : Fin (K n : ℕ), finiteGapBlock X j) - (K n : ℝ)) /
          (K n : ℝ) ^ (s.val / 2)) ^ 2 ∂gibbsMeasure (ofLong β s) (N n))
      atTop (𝓝 (Riesz1.countVariance (longParameters β s)))) :
    Tendsto (fun n =>
      let S := fun X : Riesz1.Configuration (N n) =>
        ∑ j : Fin (K n : ℕ), finiteGapBlock X j
      let h := integrable_finiteGapBlock_sum (ofLong β s) (N n) (K n)
      (Riesz1.variance (gibbsMeasure (ofLong β s) (N n)) S h).toReal /
        (K n : ℝ) ^ s.val) atTop (𝓝 (Riesz1.countVariance (longParameters β s))) := by
  simpa only [finiteGapBlock_normalized_second_moment β s _ _ (hN _)] using hsecond

end Riesz2.MesoscopicVariance

end
