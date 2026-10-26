/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.ConvergesInLawAlong
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import Riesz2.Thermodynamic.GapWeakTests

/-!
# A joint mesoscopic diagonal for laws and variances

The two diagonal passages in the proof of Corollary 1.1 in the
manuscript use the same volume for the whole law and the variance.
The one-dimensional Euclidean encoding uses the existing block BL distance.
-/

public section
noncomputable section

open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

namespace Riesz2

/-- Corollary 1.1: one volume satisfies both approximation requirements,
with a vanishing size-to-volume ratio. The two errors are bounded by `1/(j+1)`
by the construction, before taking limits. -/
theorem exists_joint_mesoscopic_diagonal
    {W : Type*} {k : ℕ}
    (F : W → ℕ+ → ProbabilityMeasure (EuclideanSpace ℝ (Fin k)))
    (G : W → ProbabilityMeasure (EuclideanSpace ℝ (Fin k)))
    (V : W → ℕ+ → ℝ) (v size : W → ℝ) (hsize : ∀ w, 0 ≤ size w)
    (hfixed : ∀ w, Tendsto (fun n : ℕ => F w n.succPNat) atTop (𝓝 (G w)))
    (hvar : ∀ w, Tendsto (fun n : ℕ => V w n.succPNat) atTop (𝓝 (v w)))
    (w : ℕ → W) :
    ∃ N : ℕ → ℕ+,
      Tendsto (fun j => (N j : ℕ)) atTop atTop ∧
      Tendsto (fun j => size (w j) / (N j : ℝ)) atTop (𝓝 0) ∧
      (∀ j : ℕ, (j + 1 : ℝ) * size (w j) ≤ (N j : ℝ) ∧
        boundedLipschitzDistance (F (w j) (N j)) (G (w j)) ≤ (j + 1 : ℝ)⁻¹ ∧
        |V (w j) (N j) - v (w j)| ≤ (j + 1 : ℝ)⁻¹) := by
  have herr (a : W) : Tendsto (fun n : ℕ =>
      max (boundedLipschitzDistance (F a n.succPNat) (G a))
        |V a n.succPNat - v a|) atTop (𝓝 0) := by
    have h₁ := tendsto_boundedLipschitzDistance_of_tendsto (hfixed a)
    have h₂ : Tendsto (fun n : ℕ => |V a n.succPNat - v a|) atTop (𝓝 0) := by
      simpa only [Real.dist_eq] using tendsto_iff_dist_tendsto_zero.mp (hvar a)
    simpa only [max_self] using h₁.max h₂
  have hchoose (j : ℕ) : ∃ n : ℕ, j ≤ n ∧
      (j + 1 : ℝ) * size (w j) ≤ (n.succPNat : ℝ) ∧
      max (boundedLipschitzDistance (F (w j) n.succPNat) (G (w j)))
        |V (w j) n.succPNat - v (w j)| ≤ (j + 1 : ℝ)⁻¹ := by
    obtain ⟨a, ha⟩ := eventually_atTop.mp
      ((herr (w j)).eventually_lt_const (show 0 < (j + 1 : ℝ)⁻¹ by positivity))
    obtain ⟨b, hb⟩ := exists_nat_gt ((j + 1 : ℝ) * size (w j))
    refine ⟨max a (max j b), le_max_of_le_right (le_max_left _ _), ?_,
      (ha _ (le_max_left _ _)).le⟩
    have hn : b ≤ max a (max j b) := le_max_of_le_right (le_max_right _ _)
    exact hb.le.trans (by exact_mod_cast hn.trans (Nat.le_succ _))
  choose n hn hs he using hchoose
  refine ⟨fun j => (n j).succPNat,
    tendsto_atTop_mono (fun j => (hn j).trans (Nat.le_succ _)) tendsto_id, ?_, ?_⟩
  · apply squeeze_zero (fun j => div_nonneg (hsize _) (by positivity))
      (fun j => ?_) (show Tendsto (fun j : ℕ => (j + 1 : ℝ)⁻¹) atTop (𝓝 0) from by
        simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact (div_le_iff₀ (by positivity)).mpr
      ((le_inv_mul_iff₀ (by positivity : (0 : ℝ) < j + 1)).mpr (hs j))
  · exact fun j => ⟨hs j, (le_max_left _ _).trans (he j), (le_max_right _ _).trans (he j)⟩

/-- Corollary 1.1: transfer law and variance along a single diagonal
at each sequence of windows, using the BL triangle inequality. -/
theorem joint_law_variance_mesoscopic_limit_internal
    {W : Type*} {k : ℕ} {l : Filter W} [l.IsCountablyGenerated]
    (F : W → ℕ+ → ProbabilityMeasure (EuclideanSpace ℝ (Fin k)))
    (G : W → ProbabilityMeasure (EuclideanSpace ℝ (Fin k)))
    (V : W → ℕ+ → ℝ) (v size scale : W → ℝ)
    (hscale : ∀ w, |scale w| ≤ 1) (hsize : ∀ w, 0 ≤ size w)
    (hfixed : ∀ w, Tendsto (fun n : ℕ => F w n.succPNat) atTop (𝓝 (G w)))
    (hvar : ∀ w, Tendsto (fun n : ℕ => V w n.succPNat) atTop (𝓝 (v w)))
    (Q : ProbabilityMeasure (EuclideanSpace ℝ (Fin k))) (a : ℝ)
    (hfinite : ∀ (w : ℕ → W) (N : ℕ → ℕ+), Tendsto w atTop l →
      Tendsto (fun j => size (w j) / (N j : ℝ)) atTop (𝓝 0) →
      Tendsto (fun j => F (w j) (N j)) atTop (𝓝 Q) ∧
      Tendsto (fun j => scale (w j) * V (w j) (N j)) atTop (𝓝 a)) :
    Tendsto (fun w => (G w, scale w * v w)) l (𝓝 (Q, a)) := by
  apply Filter.tendsto_of_seq_tendsto
  intro w hw
  obtain ⟨N, _, hratio, herror⟩ :=
    exists_joint_mesoscopic_diagonal F G V v size hsize hfixed hvar w
  obtain ⟨hLaw, hVar⟩ := hfinite w N hw hratio
  have hrate : Tendsto (fun j : ℕ => (j + 1 : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hBL := tendsto_boundedLipschitzDistance_of_tendsto hLaw
  have hG : Tendsto (fun j => G (w j)) atTop (𝓝 Q) := by
    apply tendsto_of_tendsto_boundedLipschitzDistance
    have hb (j) : boundedLipschitzDistance (G (w j)) Q ≤
        (j + 1 : ℝ)⁻¹ + boundedLipschitzDistance (F (w j) (N j)) Q := by
      apply (boundedLipschitzDistance_triangle _ (F (w j) (N j)) _).trans
      apply add_le_add_left
      simpa only [boundedLipschitzDistance_comm] using (herror j).2.1
    exact squeeze_zero (fun _ => boundedLipschitzDistance_nonneg _ _) hb
      (by simpa only [zero_add] using hrate.add hBL)
  have hv : Tendsto (fun j => scale (w j) * v (w j)) atTop (𝓝 a) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hb (j) : dist (scale (w j) * v (w j)) a ≤
        (j + 1 : ℝ)⁻¹ + dist (scale (w j) * V (w j) (N j)) a := by
      apply (dist_triangle _ (scale (w j) * V (w j) (N j)) _).trans
      apply add_le_add_left
      rw [Real.dist_eq, ← mul_sub, abs_mul]
      calc
        |scale (w j)| * |v (w j) - V (w j) (N j)| ≤
            1 * |v (w j) - V (w j) (N j)| :=
          mul_le_mul_of_nonneg_right (hscale _) (abs_nonneg _)
        _ ≤ _ := by simpa only [one_mul, abs_sub_comm] using (herror j).2.2
    exact squeeze_zero (fun _ => dist_nonneg) hb
      (by simpa only [zero_add] using hrate.add (tendsto_iff_dist_tendsto_zero.mp hVar))
  exact hG.prodMk_nhds hv

/-- Corollary 1.1: encode a real probability law on one-dimensional
Euclidean space to use the already proved bounded-Lipschitz distance API. -/
def realLawEuclidean (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin 1)) :=
  ProbabilityMeasure.map (⟨μ, inferInstance⟩ : ProbabilityMeasure ℝ)
    (OrthonormalBasis.singleton (Fin 1) ℝ).repr

/-- Corollary 1.1: bounded-continuous-test convergence of real laws
implies weak convergence of their one-dimensional Euclidean encodings. -/
theorem realLawEuclidean_tendsto_internal
    {W : Type*} {l : Filter W} (μ : W → Measure ℝ) (ν : Measure ℝ)
    (h : ConvergesInLawAlong l μ ν) :
    letI : ∀ w, IsProbabilityMeasure (μ w) := h.1
    letI : IsProbabilityMeasure ν := h.2.1
    Tendsto (fun w => realLawEuclidean (μ w)) l (𝓝 (realLawEuclidean ν)) := by
  let := h.1
  let := h.2.1
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  let g : ℝ →ᵇ ℝ := f.compContinuous
    ⟨(OrthonormalBasis.singleton (Fin 1) ℝ).repr,
      (OrthonormalBasis.singleton (Fin 1) ℝ).repr.continuous⟩
  have he (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
      (∫ x, f x ∂realLawEuclidean ρ) = ∫ x, g x ∂ρ := by
    change (∫ x, f x ∂ρ.map (OrthonormalBasis.singleton (Fin 1) ℝ).repr) = _
    rw [integral_map (OrthonormalBasis.singleton (Fin 1) ℝ).repr.continuous.measurable.aemeasurable
      f.continuous.aestronglyMeasurable]
    rfl
  simpa only [he] using h.2.2 g

/-- Corollary 1.1: the Euclidean encoding retains every bounded
continuous real test, so its weak convergence gives the literal real-law CLT. -/
theorem convergesInLawAlong_of_realLawEuclidean_tendsto_internal
    {W : Type*} {l : Filter W} (μ : W → Measure ℝ) (ν : Measure ℝ)
    [∀ w, IsProbabilityMeasure (μ w)] [IsProbabilityMeasure ν]
    (h : Tendsto (fun w => realLawEuclidean (μ w)) l (𝓝 (realLawEuclidean ν))) :
    ConvergesInLawAlong l μ ν := by
  refine ⟨fun _ => inferInstance, inferInstance, fun f => ?_⟩
  let g : EuclideanSpace ℝ (Fin 1) →ᵇ ℝ := f.compContinuous
    ⟨(OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm,
      (OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm.continuous⟩
  have ht := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h g
  change Tendsto (fun i => ∫ x, f x ∂μ i) l (𝓝 (∫ x, f x ∂ν))
  have he (ρ : Measure ℝ) [IsProbabilityMeasure ρ] : (∫ x, g x ∂realLawEuclidean ρ) =
      ∫ x, f x ∂ρ := by
    change (∫ x, g x ∂ρ.map (OrthonormalBasis.singleton (Fin 1) ℝ).repr) = _
    rw [integral_map (OrthonormalBasis.singleton (Fin 1) ℝ).repr.continuous.measurable.aemeasurable
      g.continuous.aestronglyMeasurable]
    congr 1
    funext x
    exact congrArg f ((OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm_apply_apply x)
  simpa only [he] using ht

/-- Corollary 1.1: the joint law/variance diagonal for literal real
laws, with an optional bounded variance normalization. The volume is selected
using the unnormalized variance error, as in the Palm paragraph. -/
theorem joint_real_law_variance_mesoscopic_limit_internal
    {W : Type*} {l : Filter W} [l.IsCountablyGenerated]
    (F : W → ℕ+ → Measure ℝ) (G : W → Measure ℝ)
    (V : W → ℕ+ → ℝ) (v size scale : W → ℝ)
    (hscale : ∀ w, |scale w| ≤ 1) (hsize : ∀ w, 0 ≤ size w)
    (hfixed : ∀ w, ConvergesInLawAlong atTop (fun n : ℕ => F w n.succPNat) (G w))
    (hvar : ∀ w, Tendsto (fun n : ℕ => V w n.succPNat) atTop (𝓝 (v w)))
    (Q : Measure ℝ) (hQ : IsProbabilityMeasure Q) (a : ℝ)
    (hfinite : ∀ (w : ℕ → W) (N : ℕ → ℕ+), Tendsto w atTop l →
      Tendsto (fun j => size (w j) / (N j : ℝ)) atTop (𝓝 0) →
      ConvergesInLawAlong atTop (fun j => F (w j) (N j)) Q ∧
      Tendsto (fun j => scale (w j) * V (w j) (N j)) atTop (𝓝 a)) :
    ConvergesInLawAlong l G Q ∧
      Tendsto (fun w => scale w * v w) l (𝓝 a) := by
  have hF (w : W) (N : ℕ+) : IsProbabilityMeasure (F w N) := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero N.ne_zero
    have he : n.succPNat = N := PNat.eq hn.symm
    rw [← he]
    exact (hfixed w).1 n
  let := hF
  let hG : ∀ w, IsProbabilityMeasure (G w) := fun w => (hfixed w).2.1
  let := hQ
  have ht := joint_law_variance_mesoscopic_limit_internal
    (fun w N => realLawEuclidean (F w N)) (fun w => realLawEuclidean (G w))
    V v size scale hscale hsize
    (fun w => realLawEuclidean_tendsto_internal _ _ (hfixed w)) hvar
    (realLawEuclidean Q) a (fun w N hw hr =>
      ⟨realLawEuclidean_tendsto_internal _ _ (hfinite w N hw hr).1,
        (hfinite w N hw hr).2⟩)
  exact ⟨convergesInLawAlong_of_realLawEuclidean_tendsto_internal G Q
    ((continuous_fst.tendsto _).comp ht), (continuous_snd.tendsto _).comp ht⟩

end Riesz2
