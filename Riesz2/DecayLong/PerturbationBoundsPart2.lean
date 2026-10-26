/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.PerturbationBounds
public import Riesz2.DecayLong.PhysicalCorePart2
public import Riesz2.ToMathlib.KernelCovarianceBounds

/-!
# Integrated physical covariance bounds

The covariance component of Lemma 5.8 is integrated
on the literal physical tilted marginal. All moments and exceptional
pairings refer to the existing conditional law and compensation vector.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped BigOperators ContDiff ENNReal

namespace Riesz2.ConditionalForces

set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

/-- See the proof of Lemma 5.8 in the paper, with one force-increment
prefactor on each compact temperature interval. The bound follows from
the explicit inverse-temperature factor in the adjacent BL estimate. -/
theorem conditional_force_variances_uniform (s : Riesz1.RieszExponent)
    (κ₀ : ℝ) (hκ₀ : 0 < κ₀) :
    ∃ κ > 0, ∀ (ε βlo βhi : ℝ), 0 < ε → 0 < βlo → βlo ≤ βhi →
      ∃ C > 0, ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n : ℕ+) (m : ℕ), 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∃ U : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ,
        ContDiffOn ℝ ∞ U (gapAmbientDomain ((n : ℕ) + m).succPNat) ∧
        (∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) //
            y ∈ gapAmbientDomain ((n : ℕ) + m).succPNat},
          U y.val = β.val * physicalAmbientGapEnergy (ofLong β s) ((n : ℕ) + m).succPNat y) ∧
        ∀ x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
          let q := WithLp.toLp 2 (compensationVector n m)
          let Xi := fun (i : Fin (n : ℕ)) z => β.val⁻¹ *
            (fderiv ℝ U (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z))
                (EuclideanSpace.single (i.castAdd m).castSucc 1) -
              fderiv ℝ U (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) q)
          let μ := ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x
          (∀ i : Fin (n : ℕ),
            Riesz1.WeightedSobolev.IsWeightedH1 μ
              (AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ a, x.val a)) (Xi i) (gradient (Xi i)) ∧
            (∫ z, (Xi i z - ∫ w, Xi i w ∂μ) ^ 2 ∂μ) ≤
              β.val⁻¹ * (BoundaryEntries.physicalCrossing β s n m x i i -
                2 * compensationB β s n m i x + compensationC β s n m x) ∧
            β.val⁻¹ * (BoundaryEntries.physicalCrossing β s n m x i i -
                2 * compensationB β s n m i x + compensationC β s n m x) ≤
              β.val⁻¹ * (BoundaryEntries.physicalCrossing β s n m x i i + compensationC β s n m x)) ∧
          (x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀ → ∀ j l : Fin (n : ℕ),
            let F := fun z => Xi j z - Xi l z
            MemLp F 2 μ ∧ Real.sqrt (∫ z, (F z - ∫ w, F w ∂μ) ^ 2 ∂μ) ≤
              C * (n : ℝ) ^ (κ * ε) * (Nat.dist j.val l.val : ℝ) *
                (min (min (j.val + 1) ((n : ℕ) - j.val))
                  (min (l.val + 1) ((n : ℕ) - l.val)) : ℕ) ^ (-1 - s.val / 2)) := by
  classical
  let κ := κ₀ + 2 * s.val + 10
  have hκ : 0 < κ := by dsimp only [κ]; linarith [s.property.1]
  refine ⟨κ, hκ, fun ε βlo βhi hε hlo _hle => ?_⟩
  let K := 128 * (2 : ℝ) ^ (s.val + 3) * (1 + (2 : ℝ) ^ (s.val + 1)) * βlo⁻¹
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (by positivity) (inv_nonneg.mpr hlo.le)
  refine ⟨K + 1, by linarith only [hK], fun β hβ n m hn => ?_⟩
  obtain ⟨U, hUs, hUv, hg⟩ := physical_tangent_scores_H1 (ofLong β s) n m n.pos
  refine ⟨U, hUs, hUv, fun x => ?_⟩
  intro q Xi μ
  have : IsProbabilityMeasure μ :=
    ProperMarginalChart.conditionalMeasure_probability (ofLong β s) n m n.pos (Equiv.refl _) x
  let c := fun z => RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)
  let Q := AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ a, x.val a)
  have hXi (i : Fin (n : ℕ)) :
      Riesz1.WeightedSobolev.IsWeightedH1 μ Q (Xi i) (gradient (Xi i)) := by
    let e := EuclideanSpace.single (i.castAdd m).castSucc (1 : ℝ)
    let d := β.val⁻¹ • (e - q)
    have hsum : (∑ a, d a) = 0 := by
      simp only [d, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, ← Finset.mul_sum,
        Finset.sum_sub_distrib]
      have he : (∑ a, e a) = 1 := by simp [e, EuclideanSpace.single, PiLp.single_apply]
      rw [he, show (∑ a, q a) = 1 from compensationVector_sum n m, sub_self, mul_zero]
    have hgraph := hg (Equiv.refl _) x d hsum
    have heq : (fun z => fderiv ℝ U (c z) d) = Xi i := by
      funext z
      simp only [d, map_smul, map_sub, smul_eq_mul]
      rfl
    change Riesz1.WeightedSobolev.IsWeightedH1 μ Q
      (fun z => fderiv ℝ U (c z) d) (gradient (fun z => fderiv ℝ U (c z) d)) at hgraph
    rw [heq] at hgraph
    exact hgraph
  refine ⟨fun i => ⟨hXi i, ?_, compensated_crossing_le β s n m i x⟩, fun hx j l => ?_⟩
  · have hh := physical_force_variance_internal β s n m U hUs hUv x i
    have heq : (fun z => β.val⁻¹ * fderiv ℝ U (c z)
        (EuclideanSpace.single (i.castAdd m).castSucc 1 - q)) = Xi i := by
      funext z
      simp only [map_sub]
      rfl
    have hi := hXi i
    rw [← heq] at hi
    exact heq ▸ hh hi
  · have hstep (k : Fin (n : ℕ)) (hk : k.val + 1 < (n : ℕ)) :
        let F := fun z => Xi k z - Xi (k + 1) z
        (∫ z, (F z - ∫ w, F w ∂μ) ^ 2 ∂μ) ≤
          K * (n : ℝ) ^ (κ * ε) *
            (min (k.val + 1) ((n : ℕ) - k.val) : ℕ) ^ (-2 * (1 + s.val / 2)) := by
      let j : Fin ((n : ℕ) - 1) := ⟨k.val, by omega⟩
      let i : Fin ((n : ℕ) + m + 1) := ⟨j.val, by have := j.isLt; omega⟩
      let p : Fin ((n : ℕ) + m + 1) := ⟨j.val + 1, by have := j.isLt; omega⟩
      let d := EuclideanSpace.single i (1 : ℝ) - EuclideanSpace.single p 1
      let A := fun z => β.val⁻¹ * fderiv ℝ U (c z) d
      have hsum : ∑ a, (β.val⁻¹ • d) a = 0 := by
        simp only [PiLp.smul_apply, smul_eq_mul, ← Finset.mul_sum, d, PiLp.sub_apply,
          Finset.sum_sub_distrib]
        simp [EuclideanSpace.single, PiLp.single_apply]
      have hgraph := hg (Equiv.refl _) x (β.val⁻¹ • d) hsum
      have heA : (fun z => fderiv ℝ U (c z) (β.val⁻¹ • d)) = A := by
        funext z
        simp only [map_smul, smul_eq_mul]
        rfl
      change Riesz1.WeightedSobolev.IsWeightedH1 μ Q
        (fun z => fderiv ℝ U (c z) (β.val⁻¹ • d))
        (gradient (fun z => fderiv ℝ U (c z) (β.val⁻¹ • d))) at hgraph
      rw [heA] at hgraph
      have hvar := physical_adjacent_variance_internal β s n m ε κ₀ hε.le hn U hUs hUv x hx j hgraph
      let ρ := (2 : ℝ) ^ (-s.val - 3) * (n : ℝ) ^ (-(2 * (s.val + 2)) * ε) *
        (min (j.val + 1) ((n : ℕ) - j.val) : ℕ)
      let a : Fin (n : ℕ) := ⟨j.val, by have := j.isLt; omega⟩
      let b : Fin (n : ℕ) := ⟨j.val + 1, by have := j.isLt; omega⟩
      let S := BoundaryEntries.physicalCrossing β s n m x
      change (∫ z, (A z - ∫ w, A w ∂μ) ^ 2 ∂μ) ≤
        β.val⁻¹ * ρ⁻¹ * (S a a - S a b - S b a + S b b) at hvar
      have hρ : 0 ≤ ρ := by dsimp only [ρ]; positivity
      have hbound := mul_le_mul_of_nonneg_left
        (physical_adjacent_crossing_bound_internal β s n m ε κ₀ hε.le hn x hx j)
        (mul_nonneg (inv_nonneg.mpr β.property.le) (inv_nonneg.mpr hρ))
      have hfinal := hvar.trans hbound
      have hδ : (0 : ℝ) < (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) := by
        exact_mod_cast (show 0 < min (j.val + 1) ((n : ℕ) - j.val) by have := j.isLt; omega)
      have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
      change (∫ z, (A z - ∫ w, A w ∂μ) ^ 2 ∂μ) ≤
        β.val⁻¹ * ((2 : ℝ) ^ (-s.val - 3) * (n : ℝ) ^ (-(2 * (s.val + 2)) * ε) *
          (min (j.val + 1) ((n : ℕ) - j.val) : ℕ))⁻¹ *
          ((128 * (1 + (2 : ℝ) ^ (s.val + 1))) * (n : ℝ) ^ ((κ₀ + 6) * ε) *
            (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) ^ (-1 - s.val)) at hfinal
      rw [adjacent_profile_algebra_internal β.val s.val ε κ₀ (n : ℝ)
        (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) hn0 hδ] at hfinal
      have hp : ((k + 1).castAdd m).castSucc = p := by
        apply Fin.ext
        exact Fin.val_add_one_of_lt' hk
      have hi : (k.castAdd m).castSucc = i := Fin.ext rfl
      have heq : (fun z => Xi k z - Xi (k + 1) z) = A := by
        funext z
        dsimp only [Xi, A, d, c]
        rw [map_sub, hi, hp]
        ring
      intro F
      rw [show F = A from heq]
      have hexp : -2 * (1 + s.val / 2) = -2 - s.val := by ring
      rw [hexp]
      apply hfinal.trans
      dsimp only [K]
      gcongr
      exact hβ.1
    have ht : 0 ≤ 1 + s.val / 2 := by linarith [s.property.1]
    have hh := centered_variance_telescoping_internal μ n Xi (fun i => (hXi i).1)
      K (κ * ε) (1 + s.val / 2) hK (mul_nonneg hκ.le hε.le) ht hstep j l
    have hexp : -(1 + s.val / 2) = -1 - s.val / 2 := by ring
    simpa only [hexp] using hh

end Riesz2.ConditionalForces

namespace Riesz2.PerturbationBounds

set_option backward.isDefEq.respectTransparency false

/-- See Lemma 5.8 of the paper: the conditional compensated-force
covariance is measurable in the retained coordinates. -/
theorem measurable_physical_covariance (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (U : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ)
    (i j : Fin (n : ℕ)) :
    let q := WithLp.toLp 2 (ConditionalForces.compensationVector n m)
    let Xi := fun (i : Fin (n : ℕ)) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) z =>
      β.val⁻¹ * (fderiv ℝ U
        (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z))
          (EuclideanSpace.single (i.castAdd m).castSucc 1) -
        fderiv ℝ U (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) q)
    Measurable (fun x => ProbabilityTheory.covariance (Xi i x) (Xi j x)
      (ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x)) := by
  intro q Xi
  have hXi (a : Fin (n : ℕ)) : Measurable
      (fun z : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) × EuclideanSpace ℝ (Fin m) =>
        Xi a z.1 z.2) :=
    ((((measurable_fderiv_apply_const ℝ U (EuclideanSpace.single (a.castAdd m).castSucc 1)).sub
      (measurable_fderiv_apply_const ℝ U q)).comp
        ((RetainedSimplex.continuous_chart n m _ (Equiv.refl _)).measurable.comp
          ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd))).const_mul _)
  exact KernelCovarianceBounds.measurable_covariance
    (ProperMarginalChart.conditionalKernel (ofLong β s) n m n.pos (Equiv.refl _)) (hXi i) (hXi j)

/-- The diagonal variance envelope on the refined physical event in
Lemma 5.8. The explicit bound is uniform for all
inverse temperatures at least `βlo`. -/
theorem variance_depth_bound (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (βlo ε κ₀ : ℝ) (hlo : 0 < βlo) (hβ : βlo ≤ β.val)
    (hε : 0 < ε) (_hκ₀ : 1 ≤ κ₀) (n : ℕ+) (m : ℕ)
    (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (hx : x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀)
    (hc : ConditionalForces.compensationC β s n m x ≤
      (n : ℝ) ^ (κ₀ * ε) * ((n : ℝ) + m + 1) ^ (-s.val))
    (i : Fin (n : ℕ)) :
    β.val⁻¹ * (BoundaryEntries.physicalCrossing β s n m x i i +
      ConditionalForces.compensationC β s n m x) ≤
      βlo⁻¹ * (128 * (5 / Real.log 2 + 4) * (Real.log 2 + 1 / ε) + 1) *
        (n : ℝ) ^ ((κ₀ + 7) * ε) *
        ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log (2 * (n : ℝ)) ≤ (Real.log 2 + 1 / ε) * (n : ℝ) ^ ε := by
    have hln := Real.log_le_rpow_div hn0.le hε
    have hp := Real.one_le_rpow hn1 hε.le
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0.ne']
    rw [div_eq_mul_inv] at hln
    rw [one_div]
    nlinarith [mul_le_mul_of_nonneg_left hp hlog2.le]
  have hdepth : (0 : ℝ) < (min (i.val + 1) ((n : ℕ) - i.val) : ℕ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (depth_bounds n i).1)
  have hdN : ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ≤
      (n : ℝ) + m + 1 := by
    exact_mod_cast ((depth_bounds n i).2.trans (show (n : ℕ) ≤ (n : ℕ) + m + 1 by omega))
  have hN := Real.rpow_le_rpow_of_nonpos hdepth hdN (neg_nonpos.mpr s.property.1.le)
  have hc' : ConditionalForces.compensationC β s n m x ≤
      (n : ℝ) ^ ((κ₀ + 7) * ε) *
        ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val) := by
    apply hc.trans
    exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith)) hN
      (by positivity) (by positivity)
  have hdiag := BoundaryEntries.physical_diagonal_bound β s ε κ₀ hε.le n m hn x hx i
  have hp : (n : ℝ) ^ ((κ₀ + 6) * ε) * (n : ℝ) ^ ε =
      (n : ℝ) ^ ((κ₀ + 7) * ε) := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  have hdiag' : BoundaryEntries.physicalCrossing β s n m x i i ≤
      (128 * (5 / Real.log 2 + 4) * (Real.log 2 + 1 / ε)) *
        (n : ℝ) ^ ((κ₀ + 7) * ε) *
        ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val) := by
    apply hdiag.trans
    calc
      _ ≤ (128 * (5 / Real.log 2 + 4)) * (n : ℝ) ^ ((κ₀ + 6) * ε) *
          ((Real.log 2 + 1 / ε) * (n : ℝ) ^ ε) *
          ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val) := by gcongr
      _ = _ := by rw [← hp]; ring
  have hβinv : β.val⁻¹ ≤ βlo⁻¹ := (inv_le_inv₀ β.property hlo).mpr hβ
  calc
    _ ≤ βlo⁻¹ * (BoundaryEntries.physicalCrossing β s n m x i i +
        ConditionalForces.compensationC β s n m x) := mul_le_mul_of_nonneg_right hβinv
      (add_nonneg (BoundaryEntries.physicalCrossing_nonneg β s n m x i i)
        (ConditionalForces.compensationC_nonneg β s n m x))
    _ ≤ βlo⁻¹ * ((128 * (5 / Real.log 2 + 4) * (Real.log 2 + 1 / ε) + 1) *
        (n : ℝ) ^ ((κ₀ + 7) * ε) *
        ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hlo.le)
      nlinarith only [hdiag', hc']
    _ = _ := by ring

/-- Elementary square-root bookkeeping for the boundary-depth envelope.
The extra size loss is harmless and avoids a size-dependent prefactor. -/
theorem sqrt_depth_internal {V n a d s : ℝ} (hV : 0 ≤ V) (hn : 1 ≤ n)
    (ha : 0 ≤ a) (hd : 0 < d) :
    Real.sqrt (V * n ^ a * d ^ (-s)) ≤ (V + 1) * n ^ a * d ^ (-s / 2) := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hnp : 1 ≤ n ^ a := Real.one_le_rpow hn ha
  have hpow : (d ^ (-s / 2)) ^ 2 = d ^ (-s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd.le]
    congr 1
    push_cast
    ring
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, mul_pow, hpow]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul (by nlinarith [sq_nonneg V] : V ≤ (V + 1) ^ 2)
    (by nlinarith [sq_nonneg (n ^ a)] : n ^ a ≤ (n ^ a) ^ 2) (by positivity) (sq_nonneg _)

/-- Internal moment transfer for the physical covariance component of
Lemma 5.8. The supplied pointwise envelope is discharged by
`physical_covariance_envelopes` in the integrated theorem below. -/
theorem covariance_moment_internal (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (ν : Measure (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)))
    (Y : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → ℝ) (i j : Fin (n : ℕ))
    (hY : Measurable Y) (p : ℝ≥0∞) (hp : 1 ≤ p) (H C : ℝ) (hH : 0 ≤ H) (hC : 0 ≤ C)
    (hi : eLpNorm (GoodBlocks.conditionalHessian β s n m i i) p ν ≤ ENNReal.ofReal H)
    (hj : eLpNorm (GoodBlocks.conditionalHessian β s n m j j) p ν ≤ ENNReal.ofReal H)
    (hc : eLpNorm (ConditionalForces.compensationC β s n m) p ν ≤ ENNReal.ofReal C)
    (hb : ∀ x, |Y x| ≤
      Real.sqrt (β.val⁻¹ * (BoundaryEntries.physicalCrossing β s n m x i i +
        ConditionalForces.compensationC β s n m x)) *
      Real.sqrt (β.val⁻¹ * (BoundaryEntries.physicalCrossing β s n m x j j +
        ConditionalForces.compensationC β s n m x))) :
    eLpNorm Y p ν ≤ ENNReal.ofReal (2 * β.val⁻¹ * (H + C)) := by
  let a := fun k x => β.val⁻¹ * (GoodBlocks.conditionalHessian β s n m k k x +
    ConditionalForces.compensationC β s n m x)
  have ha (k) x : 0 ≤ a k x := mul_nonneg (inv_nonneg.mpr β.property.le)
    (add_nonneg (GoodBlocks.conditionalHessian_nonneg β s n m k k x)
      (ConditionalForces.compensationC_nonneg β s n m x))
  have hnorm (k) (hk : eLpNorm (GoodBlocks.conditionalHessian β s n m k k) p ν ≤
      ENNReal.ofReal H) : eLpNorm (a k) p ν ≤ ENNReal.ofReal (β.val⁻¹ * (H + C)) := by
    change eLpNorm (β.val⁻¹ • (GoodBlocks.conditionalHessian β s n m k k +
      ConditionalForces.compensationC β s n m)) p ν ≤ _
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg (inv_nonneg.mpr β.property.le),
      ENNReal.ofReal_mul (inv_nonneg.mpr β.property.le)]
    exact mul_le_mul le_rfl (((eLpNorm_add_le hp).trans (add_le_add hk hc)).trans_eq
      (ENNReal.ofReal_add hH hC).symm) (by positivity) (by positivity)
  have hbound x : |Y x| ≤ Real.sqrt (a i x) * Real.sqrt (a j x) := by
    apply (hb x).trans
    dsimp only [a]
    apply mul_le_mul _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    · apply Real.sqrt_le_sqrt
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr β.property.le)
      linarith [BoundaryEntries.physicalCrossing_le_hessian β s n m x i i]
    · apply Real.sqrt_le_sqrt
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr β.property.le)
      linarith [BoundaryEntries.physicalCrossing_le_hessian β s n m x j j]
  have hβ0 : 0 ≤ β.val⁻¹ := inv_nonneg.mpr β.property.le
  have hh := KernelCovarianceBounds.envelope_norm hp hY (by positivity : 0 ≤ β.val⁻¹ * (H + C))
    (by positivity : 0 ≤ β.val⁻¹ * (H + C)) (ha i) (ha j) hbound (hnorm i hi) (hnorm j hj)
  convert hh using 1; congr 1; ring

/-- See Lemma 5.8 of the paper, pointwise conditional covariance
envelopes with prefactors uniform on compact temperature intervals. -/
theorem uniform_covariance_envelopes (s : Riesz1.RieszExponent)
    (κ₀ : ℝ) (hκ₀ : 0 < κ₀) :
    ∃ κ > 0, ∀ (ε βlo βhi : ℝ), 0 < ε → 0 < βlo → βlo ≤ βhi →
      ∃ C > 0, ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n : ℕ+) (m : ℕ), 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∃ U : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ,
        ContDiffOn ℝ ∞ U (gapAmbientDomain ((n : ℕ) + m).succPNat) ∧
        (∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) //
            y ∈ gapAmbientDomain ((n : ℕ) + m).succPNat},
          U y.val = β.val * physicalAmbientGapEnergy (ofLong β s) ((n : ℕ) + m).succPNat y) ∧
        ∀ x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
          let q := WithLp.toLp 2 (ConditionalForces.compensationVector n m)
          let Xi := fun (i : Fin (n : ℕ)) z => β.val⁻¹ *
            (fderiv ℝ U (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z))
                (EuclideanSpace.single (i.castAdd m).castSucc 1) -
              fderiv ℝ U (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) q)
          let μ := ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x
          let v := fun i => Real.sqrt (β.val⁻¹ *
            (BoundaryEntries.physicalCrossing β s n m x i i +
              ConditionalForces.compensationC β s n m x))
          (∀ i : Fin (n : ℕ), MemLp (Xi i) 2 μ) ∧
          (∀ i j : Fin (n : ℕ), |ProbabilityTheory.covariance (Xi i) (Xi j) μ| ≤ v i * v j) ∧
          (x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀ → ∀ i j l : Fin (n : ℕ),
            |ProbabilityTheory.covariance (Xi i) (Xi j) μ -
              ProbabilityTheory.covariance (Xi i) (Xi l) μ| ≤
              v i * (C * (n : ℝ) ^ (κ * ε) * (Nat.dist j.val l.val : ℝ) *
                (min (min (j.val + 1) ((n : ℕ) - j.val))
                  (min (l.val + 1) ((n : ℕ) - l.val)) : ℕ) ^ (-1 - s.val / 2))) := by
  obtain ⟨κ, hκ, ht⟩ := ConditionalForces.conditional_force_variances_uniform s κ₀ hκ₀
  refine ⟨κ, hκ, fun ε βlo βhi hε hlo hle => ?_⟩
  obtain ⟨C, hC, hb⟩ := ht ε βlo βhi hε hlo hle
  refine ⟨C, hC, fun β hβ n m hper => ?_⟩
  obtain ⟨U, hU, hv, hf⟩ := hb β hβ n m hper
  refine ⟨U, hU, hv, fun x => ?_⟩
  intro q Xi μ v
  have : IsProbabilityMeasure μ :=
    ProperMarginalChart.conditionalMeasure_probability (ofLong β s) n m n.pos (Equiv.refl _) x
  obtain ⟨hvar, hdiff⟩ := hf x
  have hLp (i : Fin (n : ℕ)) : MemLp (Xi i) 2 μ := (hvar i).1.1
  have hs (i : Fin (n : ℕ)) :
      Real.sqrt (∫ z, (Xi i z - ∫ w, Xi i w ∂μ) ^ 2 ∂μ) ≤ v i :=
    Real.sqrt_le_sqrt ((hvar i).2.1.trans (hvar i).2.2)
  refine ⟨hLp, fun i j => ?_, fun hx i j l => ?_⟩
  · exact (CovarianceCauchySchwarz.abs_covariance_le (hLp i) (hLp j)).trans
      (mul_le_mul (hs i) (hs j) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  · rw [← ProbabilityTheory.covariance_fun_sub_right (hLp i) (hLp j) (hLp l)]
    exact (CovarianceCauchySchwarz.abs_covariance_le (hLp i) ((hLp j).sub (hLp l))).trans
      (mul_le_mul (hs i) (hdiff hx j l).2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))


/-- Internal scalar bookkeeping shared by the two covariance profiles. -/
theorem covariance_profile_algebra_internal {n ε a k J B C u v r w : ℝ}
    (hn : 1 ≤ n) (hε : 0 < ε) (ha : 0 ≤ a) (hk : 0 ≤ k)
    (_hJ : 0 ≤ J) (_hB : 0 ≤ B) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hr : 0 ≤ r) (hw : 0 ≤ w) (hC1 : J ^ 2 ≤ C) (hC2 : J * B ≤ C) :
    (J * n ^ (a * ε) * u) * (J * n ^ (a * ε) * v) ≤
      C * n ^ ((2 * (k + a)) * ε) * u * v ∧
    (J * n ^ (a * ε) * u) * (B * n ^ (k * ε) * r * w) ≤
      C * n ^ ((2 * (k + a)) * ε) * r * u * w := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hC : 0 ≤ C := (sq_nonneg J).trans hC1
  have he : n ^ (a * ε) * n ^ (a * ε) ≤ n ^ ((2 * (k + a)) * ε) := by
    rw [← Real.rpow_add hn0]
    apply Real.rpow_le_rpow_of_exponent_le hn
    nlinarith only [mul_nonneg hk hε.le]
  have hi : n ^ (a * ε) * n ^ (k * ε) ≤ n ^ ((2 * (k + a)) * ε) := by
    rw [← Real.rpow_add hn0]
    apply Real.rpow_le_rpow_of_exponent_le hn
    nlinarith only [mul_nonneg hk hε.le, mul_nonneg ha hε.le]
  constructor
  · calc
      _ = J ^ 2 * (n ^ (a * ε) * n ^ (a * ε)) * u * v := by ring
      _ ≤ _ := by gcongr
  · calc
      _ = (J * B) * (n ^ (a * ε) * n ^ (k * ε)) * r * u * w := by ring
      _ ≤ _ := by gcongr

/-- See Lemma 5.8 of the paper, complete covariance multiplication
component: both pairings, absolute integrability, and the prescribed
exceptional exponent. The loss exponent is chosen before temperature.
The prefactors are uniform on each compact positive temperature interval. -/
theorem covariance_bilinear (hRig : External.LongRangeRigidityLocallyUniform)
    (s : Riesz1.RieszExponent) (κ₀ : ℝ) (hκ₀ : 1 ≤ κ₀) :
    ∃ κ > 0, ∀ (ε Cθ βlo βhi : ℝ),
      0 < ε → 1 ≤ Cθ → 0 < βlo → βlo ≤ βhi →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n : ℕ+) (m : ℕ), 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∃ U : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ,
        ContDiffOn ℝ ∞ U (gapAmbientDomain ((n : ℕ) + m).succPNat) ∧
        (∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) //
            y ∈ gapAmbientDomain ((n : ℕ) + m).succPNat},
          U y.val = β.val * physicalAmbientGapEnergy (ofLong β s) ((n : ℕ) + m).succPNat y) ∧
        let ν := (activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n hn θ ε false).comap
          ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
        let q := WithLp.toLp 2 (ConditionalForces.compensationVector n m)
        let Xi := fun (i : Fin (n : ℕ)) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) z =>
          β.val⁻¹ * (fderiv ℝ U
            (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z))
              (EuclideanSpace.single (i.castAdd m).castSucc 1) -
            fderiv ℝ U (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) q)
        let Y := fun i j x => ProbabilityTheory.covariance (Xi i x) (Xi j x)
          (ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x)
        (∀ x i, MemLp (Xi i x) 2
          (ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x)) ∧
        ∀ (φ η : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → ℝ) (Mφ Mη : ℝ),
          Measurable φ → Measurable η → 0 ≤ Mφ → 0 ≤ Mη →
          (∀ᵐ x ∂ν, |φ x| ≤ Mφ) → (∀ᵐ x ∂ν, |η x| ≤ Mη) →
        ∀ i j l : Fin (n : ℕ),
          let d := fun a : Fin (n : ℕ) => ((min (a.val + 1) ((n : ℕ) - a.val) : ℕ) : ℝ)
          let L := Real.sqrt (∫ x, φ x ^ 2 ∂ν) * Real.sqrt (∫ x, η x ^ 2 ∂ν)
          let E := C * Real.exp (-c * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη)
          Integrable (fun x => φ x * η x * Y i j x) ν ∧
          |∫ x, φ x * η x * Y i j x ∂ν| ≤
            C * (n : ℝ) ^ (κ * ε) * (d i) ^ (-s.val / 2) * (d j) ^ (-s.val / 2) * L + E ∧
          Integrable (fun x => φ x * η x * (Y i j x - Y i l x)) ν ∧
          |∫ x, φ x * η x * (Y i j x - Y i l x) ∂ν| ≤
            C * (n : ℝ) ^ (κ * ε) * (Nat.dist j.val l.val : ℝ) *
              (d i) ^ (-s.val / 2) * (min (d j) (d l)) ^ (-1 - s.val / 2) * L + E := by
  obtain ⟨k, hk, henv⟩ := uniform_covariance_envelopes s κ₀ (by linarith)
  let κ := 2 * (k + κ₀ + 7)
  have hκ : 0 < κ := by dsimp [κ]; linarith
  refine ⟨κ, hκ, fun ε Cθ βlo βhi hε hCθ hlo hle => ?_⟩
  obtain ⟨B, hB, hb⟩ := henv ε βlo βhi hε hlo hle
  obtain ⟨H, hH, hhmom⟩ := GoodBlocks.tilted_conditional_hessian_moments s βlo βhi ε Cθ
    hlo hle hε hCθ
  obtain ⟨A, hA, hamom⟩ := ConditionalForces.compensation_moments s βlo βhi ε Cθ
    hlo hle hε hCθ
  obtain ⟨D, c, hD, hc, hgood⟩ := refined_good_event hRig s βlo βhi ε Cθ
    hlo hle hε hCθ
  have hβinv : 0 < βlo⁻¹ := inv_pos.mpr hlo
  let V := βlo⁻¹ * (128 * (5 / Real.log 2 + 4) * (Real.log 2 + 1 / ε) + 1)
  have hV : 0 ≤ V := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [V]
    positivity
  let J := V + 1
  have hJ : 0 < J := by dsimp [J]; linarith
  let M := 2 * βlo⁻¹ * ((H + A) * (2 : ℝ) ^ ((s.val + 2) / s.val))
  have hM : 0 < M := by dsimp [M]; positivity
  let C := J ^ 2 + J * B + 2 * M * Real.sqrt D + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, c / 2, hC, by positivity, ?_⟩
  intro β hβ n m hper hn θ hcurv
  have hβ0 : 0 < β.val := β.property
  have hβinv : 0 < βlo⁻¹ := inv_pos.mpr hlo
  obtain ⟨U, hU, hv, he⟩ := hb β hβ n m hper
  refine ⟨U, hU, hv, ?_⟩
  intro ν q Xi Y
  have : IsProbabilityMeasure ν := GoodBlocks.proper_active_probability _ _ _ _ _ _
  have hmeas (i j) : Measurable (Y i j) := measurable_physical_covariance β s n m U i j
  have hLp (x) (i) := (he x).1 i
  refine ⟨hLp, ?_⟩
  intro φ η Mφ Mη hφ hη hMφ hMη hφM hηM i j l d L E
  have hφ2 : MemLp φ 2 ν := MemLp.of_bound hφ.aestronglyMeasurable Mφ
    (by simpa only [Real.norm_eq_abs] using hφM)
  have hη2 : MemLp η 2 ν := MemLp.of_bound hη.aestronglyMeasurable Mη
    (by simpa only [Real.norm_eq_abs] using hηM)
  let G := GoodBlocks.properGoodEvent β s n m ε κ₀ ∩
    {x | ConditionalForces.compensationC β s n m x ≤
      (n : ℝ) ^ (κ₀ * ε) * ((n : ℝ) + m + 1) ^ (-s.val)}
  obtain ⟨hG, hprob⟩ := hgood β hβ n m hper hn θ hcurv κ₀ κ₀ hκ₀ hκ₀
  change MeasurableSet G at hG
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hdh (a : Fin (n : ℕ)) : 0 < d a := by
    dsimp [d]
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (depth_bounds n a).1)
  have hvb (x) (hx : x ∈ G) (a : Fin (n : ℕ)) :
      Real.sqrt (β.val⁻¹ * (BoundaryEntries.physicalCrossing β s n m x a a +
        ConditionalForces.compensationC β s n m x)) ≤
        J * (n : ℝ) ^ ((κ₀ + 7) * ε) * (d a) ^ (-s.val / 2) :=
    (Real.sqrt_le_sqrt (variance_depth_bound β s βlo ε κ₀ hlo hβ.1 hε hκ₀ n m hper x
      hx.1 hx.2 a)).trans (sqrt_depth_internal hV hn1 (by nlinarith) (hdh a))
  have hHnorm (a : Fin (n : ℕ)) :
      eLpNorm (GoodBlocks.conditionalHessian β s n m a a) 2 ν ≤
        ENNReal.ofReal (H * (2 : ℝ) ^ ((s.val + 2) / s.val)) := by
    have hh := hhmom β hβ n m hn θ hcurv a a 2 (by norm_num)
    norm_num only [ENNReal.ofReal_ofNat] at hh
    apply hh.trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_of_le_one_right (by positivity)
      (Real.rpow_le_one_of_one_le_of_nonpos (by
        exact le_add_of_nonneg_right (Nat.cast_nonneg _))
        (by linarith [s.property.1]))
  have hCnorm : eLpNorm (ConditionalForces.compensationC β s n m) 2 ν ≤
      ENNReal.ofReal (A * (2 : ℝ) ^ ((s.val + 2) / s.val)) := by
    have hh := (le_add_self).trans
      ((hamom β hβ n m hper hn θ hcurv 2 (by norm_num)).1 i)
    norm_num only [ENNReal.ofReal_ofNat] at hh
    apply hh.trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_of_le_one_right (by positivity)
      (Real.rpow_le_one_of_one_le_of_nonpos (by
        linarith [Nat.cast_nonneg (α := ℝ) m])
        (by linarith [s.property.1]))
  have hnorm (a b : Fin (n : ℕ)) : eLpNorm (Y a b) 2 ν ≤ ENNReal.ofReal M := by
    have hh := covariance_moment_internal β s n m ν (Y a b) a b (hmeas a b) 2 (by norm_num)
      (H * (2 : ℝ) ^ ((s.val + 2) / s.val)) (A * (2 : ℝ) ^ ((s.val + 2) / s.val))
      (by positivity) (by positivity) (hHnorm a) (hHnorm b) hCnorm
      (fun x => (he x).2.1 a b)
    apply hh.trans
    apply ENNReal.ofReal_le_ofReal
    dsimp [M]
    calc
      _ = 2 * β.val⁻¹ * ((H + A) * (2 : ℝ) ^ ((s.val + 2) / s.val)) := by ring
      _ ≤ _ := by
        gcongr
        exact hβ.1
  have hnormdiff : eLpNorm (fun x => Y i j x - Y i l x) 2 ν ≤ ENNReal.ofReal (2 * M) := by
    apply (eLpNorm_sub_le (by norm_num)).trans
    apply (add_le_add (hnorm i j) (hnorm i l)).trans_eq
    rw [← ENNReal.ofReal_add hM.le hM.le]
    congr 1
    ring
  have hC1 : J ^ 2 ≤ C := by
    dsimp only [C]
    nlinarith only [mul_nonneg hJ.le hB.le, mul_nonneg hM.le (Real.sqrt_nonneg D)]
  have hC2 : J * B ≤ C := by
    dsimp only [C]
    nlinarith only [sq_nonneg J, mul_nonneg hM.le (Real.sqrt_nonneg D)]
  have halg := covariance_profile_algebra_internal hn1 hε
    (show 0 ≤ κ₀ + 7 by linarith only [hκ₀]) hk.le hJ.le hB.le
    (show 0 ≤ (d i) ^ (-s.val / 2) by positivity)
    (show 0 ≤ (d j) ^ (-s.val / 2) by positivity)
    (show 0 ≤ (Nat.dist j.val l.val : ℝ) by positivity)
    (show 0 ≤ (min (d j) (d l)) ^ (-1 - s.val / 2) by positivity) hC1 hC2
  have hentry (x) (hx : x ∈ G) : |Y i j x| ≤
      C * (n : ℝ) ^ (κ * ε) * (d i) ^ (-s.val / 2) * (d j) ^ (-s.val / 2) :=
    ((he x).2.1 i j).trans ((mul_le_mul (hvb x hx i) (hvb x hx j)
      (Real.sqrt_nonneg _) (by positivity)).trans (by
        simpa only [κ, add_assoc] using halg.1))
  have hdiff (x) (hx : x ∈ G) : |Y i j x - Y i l x| ≤
      C * (n : ℝ) ^ (κ * ε) * (Nat.dist j.val l.val : ℝ) *
        (d i) ^ (-s.val / 2) * (min (d j) (d l)) ^ (-1 - s.val / 2) := by
    have hh := (he x).2.2 hx.1 i j l
    simp only [Nat.cast_min] at hh
    apply hh.trans
    apply (mul_le_mul_of_nonneg_right (hvb x hx i) (by positivity)).trans
    simpa only [κ, d, Nat.cast_min, add_assoc] using halg.2
  have herror : 2 * M * Real.sqrt D *
      Real.exp (-(c / 2) * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη) ≤ E := by
    dsimp only [E]
    gcongr
    dsimp [C]
    nlinarith only [sq_nonneg J, mul_nonneg hJ.le hB.le]
  obtain ⟨hI, hbd⟩ := KernelCovarianceBounds.event_pair hG (hmeas i j) hφ hη
    (by positivity) hM.le hD.le hMφ hMη hφM hηM hφ2 hη2 hentry (hnorm i j) hprob
  obtain ⟨hI', hbd'⟩ := KernelCovarianceBounds.event_pair hG ((hmeas i j).sub (hmeas i l)) hφ hη
    (by positivity) (by positivity : 0 ≤ 2 * M) hD.le hMφ hMη hφM hηM hφ2 hη2
    hdiff hnormdiff hprob
  refine ⟨hI, hbd.trans (add_le_add le_rfl ?_), hI', hbd'.trans (add_le_add le_rfl herror)⟩
  apply (show M * Real.sqrt D * Real.exp (-(c / 2) * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) *
      (Mφ * Mη) ≤ 2 * M * Real.sqrt D *
        Real.exp (-(c / 2) * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη) by gcongr; linarith).trans herror

/-- See Lemma 5.8 of the paper, reference part of the freezing error.
A crude period-polynomial bound suffices because the reference period is
polynomial in the retained size. It includes the empty truncation and the
antipodal half-weight of the definition. -/
theorem reference_freezing_bound (s : Riesz1.RieszExponent) :
    ∃ C > 0, ∀ (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (K : ℕ) (i j : Fin (M : ℕ)),
      |referenceIntervalMatrix s M hM K i j| ≤ C * (M : ℝ) ^ 2 := by
  classical
  obtain ⟨_, C, _, hC, hc⟩ := sampledSecondDifference_bounds s
  refine ⟨C, hC, fun M hM K i j => ?_⟩
  let S := (Finset.range ((M : ℕ) / 2 + 1)).filter (fun r => 1 ≤ r ∧ K ≤ r)
  have hcoeff (r : ℕ) (hr : r ∈ S) :
      0 ≤ (1 - if 2 * r = (M : ℕ) then (1 / 2 : ℝ) else 0) *
        sampledSecondDifference s M hM ⟨r % (M : ℕ), Nat.mod_lt _ M.pos⟩ ∧
      (1 - if 2 * r = (M : ℕ) then (1 / 2 : ℝ) else 0) *
        sampledSecondDifference s M hM ⟨r % (M : ℕ), Nat.mod_lt _ M.pos⟩ ≤ C := by
    have hr1 : 1 ≤ r := (Finset.mem_filter.mp hr).2.1
    have hrl : r < (M : ℕ) := by
      have := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
      omega
    let k : Fin (M : ℕ) := ⟨r % (M : ℕ), Nat.mod_lt _ M.pos⟩
    have hk : k ≠ 0 := by
      intro hk
      have he := congrArg Fin.val hk
      simp only [k, Fin.val_zero, Nat.mod_eq_of_lt hrl] at he
      omega
    have hd : (1 : ℝ) ≤ (Riesz1.cyclicIndexDistance M k 0 : ℝ) := by
      exact_mod_cast (show 1 ≤ Riesz1.cyclicIndexDistance M k 0 by
        have hn : Riesz1.cyclicIndexDistance M k 0 ≠ 0 :=
          fun h => hk ((cyclicIndexDistance_eq_zero_iff k 0).mp h)
        omega)
    have hs0 := (sampledSecondDifference_pos s M hM hk).le
    have hsC : sampledSecondDifference s M hM k ≤ C :=
      (hc M hM k hk).2.trans (mul_le_of_le_one_right hC.le
        (Real.rpow_le_one_of_one_le_of_nonpos hd (by linarith [s.property.1])))
    have hf : 0 ≤ (1 - if 2 * r = (M : ℕ) then (1 / 2 : ℝ) else 0) ∧
        (1 - if 2 * r = (M : ℕ) then (1 / 2 : ℝ) else 0) ≤ 1 := by
      split_ifs <;> norm_num
    exact ⟨mul_nonneg hf.1 hs0, (mul_le_of_le_one_left hs0 hf.2).trans hsC⟩
  have hterm (a : Fin (M : ℕ)) (r : ℕ) (hr : r ∈ S) :
      0 ≤ (1 - if 2 * r = (M : ℕ) then (1 / 2 : ℝ) else 0) *
        sampledSecondDifference s M hM ⟨r % (M : ℕ), Nat.mod_lt _ M.pos⟩ *
        (if i ∈ cyclicIndexInterval M a r then 1 else 0) *
        (if j ∈ cyclicIndexInterval M a r then 1 else 0) ∧
      (1 - if 2 * r = (M : ℕ) then (1 / 2 : ℝ) else 0) *
        sampledSecondDifference s M hM ⟨r % (M : ℕ), Nat.mod_lt _ M.pos⟩ *
        (if i ∈ cyclicIndexInterval M a r then 1 else 0) *
        (if j ∈ cyclicIndexInterval M a r then 1 else 0) ≤ C := by
    have hh := hcoeff r hr
    split_ifs <;> simp_all only [mul_one, mul_zero, le_refl, hC.le, and_self, ite_true, ite_false]
  have hnonneg : 0 ≤ referenceIntervalMatrix s M hM K i j := by
    apply Finset.sum_nonneg
    intro a _
    exact Finset.sum_nonneg (fun r hr => (hterm a r hr).1)
  rw [abs_of_nonneg hnonneg]
  have hcard : (S.card : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast ((Finset.card_le_card (Finset.filter_subset _ _)).trans
      (show (Finset.range ((M : ℕ) / 2 + 1)).card ≤ (M : ℕ) by
        rw [Finset.card_range]; omega))
  calc
    _ ≤ ∑ _a : Fin (M : ℕ), ∑ _r ∈ S, C := by
      apply Finset.sum_le_sum
      intro a _
      exact Finset.sum_le_sum (fun r hr => (hterm a r hr).2)
    _ = (M : ℝ) * (S.card : ℝ) * C := by simp only [Finset.sum_const, nsmul_eq_mul,
        Finset.card_univ, Fintype.card_fin]; ring
    _ ≤ (M : ℝ) * (M : ℝ) * C := by gcongr
    _ = _ := by ring

/-- See Lemma 5.8 of the paper, the entire exceptional freezing
component on proper windows, with both column pairings. The reference
period obeys the construction-scale bound of Subsection 5.1. -/
theorem proper_freezing_bilinear (hRig : External.LongRangeRigidityLocallyUniform)
    (s : Riesz1.RieszExponent) (ε Cθ βlo βhi : ℝ)
    (hε : 0 < ε) (hCθ : 1 ≤ Cθ) (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n : ℕ+) (m : ℕ), 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ),
      (M : ℝ) ≤ 3 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
      ∀ κ₀ : ℝ, 1 ≤ κ₀ →
      let ν := (activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n hn θ ε false).comap
        ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
      let E := (GoodBlocks.properGoodEvent β s n m ε κ₀)ᶜ
      let F := fun i j x => PhysicalCore.forcingHessian n θ ε x.val i j +
        GoodBlocks.conditionalHessian β s n m i j x -
        2 * referenceIntervalMatrix s M hM K (i.castLE hnM) (j.castLE hnM)
      ∀ (φ η : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → ℝ) (Mφ Mη : ℝ),
        Measurable φ → Measurable η → 0 ≤ Mφ → 0 ≤ Mη →
        (∀ᵐ x ∂ν, |φ x| ≤ Mφ) → (∀ᵐ x ∂ν, |η x| ≤ Mη) →
      ∀ i j l : Fin (n : ℕ),
        IntegrableOn (fun x => φ x * η x * F i j x) E ν ∧
        |∫ x in E, φ x * η x * F i j x ∂ν| ≤
          C * Real.exp (-c * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη) ∧
        IntegrableOn (fun x => φ x * η x * (F i j x - F i l x)) E ν ∧
        |∫ x in E, φ x * η x * (F i j x - F i l x) ∂ν| ≤
          C * Real.exp (-c * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη) := by
  obtain ⟨R, hR, href⟩ := reference_freezing_bound s
  obtain ⟨H, hH, hhmom⟩ := GoodBlocks.tilted_conditional_hessian_moments s βlo βhi ε Cθ
    hlo hle hε hCθ
  obtain ⟨D, b, hD, hb, hgood⟩ := GoodBlocks.proper_good_event hRig s hε hCθ βlo βhi hlo hle
  let B := 2 * (1 / 2 + 1 / s.val)
  have hB : 0 ≤ B := by
    have hs := s.property.1
    dsimp [B]
    positivity
  have hδ := GoodBlocks.coefficientTailPower_pos s.property.1 s.property.2 hε
  obtain ⟨A, hA, habsorb⟩ := MomentEvent.exists_rpow_mul_exp_neg_le (a := B)
    (c := b / 4) (c' := b / 8) hδ (by linarith only [hb])
  let T := Cθ + H * (4 : ℝ) ^ ((s.val + 2) / s.val) + 18 * R
  have hT : 0 < T := by
    have hCθ0 : 0 < Cθ := by linarith only [hCθ]
    dsimp [T]
    positivity
  let Q := T * D ^ (1 / 4 : ℝ) * (A + 1)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  refine ⟨2 * Q, b / 8, by positivity, by positivity, ?_⟩
  intro β hβ n m hper hn θ hcurv M hM hnM K hscale κ₀ hκ₀ ν E F φ η Mφ Mη
    hφ hη hMφ hMη hφM hηM i j l
  have : IsProbabilityMeasure ν := GoodBlocks.proper_active_probability _ _ _ _ _ _
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hnp : 1 ≤ (n : ℝ) ^ B := Real.one_le_rpow hn1 hB
  have hMpow : (M : ℝ) ^ 2 ≤ 9 * (n : ℝ) ^ B := by
    have hh := pow_le_pow_left₀ (by positivity) hscale 2
    rw [mul_pow] at hh
    have hp : ((n : ℝ) ^ (1 / 2 + 1 / s.val)) ^ 2 = (n : ℝ) ^ B := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
      congr 1
      dsimp [B]
      ring
    simpa only [hp, show (3 : ℝ) ^ 2 = 9 by norm_num] using hh
  have hFmeas (a b) : Measurable (F a b) :=
    (((PhysicalCore.measurable_forcingHessian n θ ε a b).comp measurable_subtype_coe).add
      (GoodBlocks.measurable_conditionalHessian β s n m a b)).sub measurable_const
  have hforcing (a b : Fin (n : ℕ)) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
      |PhysicalCore.forcingHessian n θ ε x.val a b| ≤ Cθ := by
    rw [PhysicalCore.forcingHessian_apply n m θ ε x a b]
    split_ifs
    · have hh := hcurv ((n : ℝ) ^ (-ε) * x.val a)
        (mul_pos (Real.rpow_pos_of_pos hn0 _) (x.property.1 a))
      have hp : 1 ≤ ((n : ℝ) ^ ε) ^ 2 := one_le_pow₀ (Real.one_le_rpow hn1 hε.le)
      rw [abs_of_nonneg (div_nonneg hh.1 (sq_nonneg _))]
      apply (div_le_iff₀ (by positivity : 0 < ((n : ℝ) ^ ε) ^ 2)).mpr
      exact hh.2.trans (le_mul_of_one_le_right (by linarith only [hCθ]) hp)
    · simpa only [abs_zero] using (show 0 ≤ Cθ by linarith only [hCθ])
  have hnorm4 (a b : Fin (n : ℕ)) : eLpNorm (F a b) 4 ν ≤ ENNReal.ofReal (T * (n : ℝ) ^ B) := by
    have hf := eLpNorm_le_of_ae_bound (p := 4)
      (((PhysicalCore.measurable_forcingHessian n θ ε a b).comp
        measurable_subtype_coe).aestronglyMeasurable (μ := ν))
      (ae_of_all ν fun x => by simpa only [Real.norm_eq_abs, Function.comp_apply] using hforcing a b x)
    simp only [measure_univ, ENNReal.one_rpow, one_mul] at hf
    have hh := hhmom β hβ n m hn θ hcurv a b 4 (by norm_num)
    norm_num only [ENNReal.ofReal_ofNat] at hh
    have hh' : eLpNorm (GoodBlocks.conditionalHessian β s n m a b) 4 ν ≤
        ENNReal.ofReal (H * (4 : ℝ) ^ ((s.val + 2) / s.val)) := hh.trans
      (ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (by positivity)
        (Real.rpow_le_one_of_one_le_of_nonpos
          (le_add_of_nonneg_right (Nat.cast_nonneg _)) (by linarith [s.property.1]))))
    have hr := eLpNorm_le_of_ae_bound (p := 4) (μ := ν)
      (f := fun _ => 2 * referenceIntervalMatrix s M hM K (a.castLE hnM) (b.castLE hnM))
      measurable_const.aestronglyMeasurable (ae_of_all ν fun _ => show
        ‖2 * referenceIntervalMatrix s M hM K (a.castLE hnM) (b.castLE hnM)‖ ≤
          2 * R * (M : ℝ) ^ 2 by
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
            exact (mul_le_mul_of_nonneg_left (href M hM K (a.castLE hnM) (b.castLE hnM))
              (by norm_num)).trans_eq (by ring))
    simp only [measure_univ, ENNReal.one_rpow, one_mul] at hr
    apply ((eLpNorm_sub_le (by norm_num)).trans
      (add_le_add (eLpNorm_add_le (by norm_num)) le_rfl)).trans
    apply (add_le_add (add_le_add hf hh') hr).trans
    rw [← ENNReal.ofReal_add (by linarith only [hCθ]) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (Cθ + H * (4 : ℝ) ^ ((s.val + 2) / s.val)) * (n : ℝ) ^ B +
          2 * R * (9 * (n : ℝ) ^ B) := by
        exact add_le_add (le_mul_of_one_le_right (by positivity) hnp)
          (mul_le_mul_of_nonneg_left hMpow (by positivity))
      _ = _ := by dsimp [T]; ring
  have hnorm (a z : Fin (n : ℕ)) : eLpNorm (F a z) 2 (ν.restrict E) ≤
      ENNReal.ofReal (Q * Real.exp (-(b / 8) * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε)) := by
    have hh := MomentEvent.restricted_two_norm_le (hFmeas a z) E
      (show 0 ≤ T * (n : ℝ) ^ B by positivity) hD.le (hnorm4 a z)
      (by simpa only [neg_mul] using hgood β hβ n m hper hn θ hcurv κ₀ hκ₀)
    apply hh.trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _ = T * D ^ (1 / 4 : ℝ) * ((n : ℝ) ^ B *
          Real.exp (-(b / 4) * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε)) := by
        rw [show -(b * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) / 4 =
          -(b / 4) * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε by ring]
        ring
      _ ≤ T * D ^ (1 / 4 : ℝ) * (A *
          Real.exp (-(b / 8) * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε)) :=
        mul_le_mul_of_nonneg_left (habsorb (n : ℝ) hn1) (by positivity)
      _ ≤ Q * Real.exp (-(b / 8) * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) := by
        dsimp [Q]
        have he := Real.exp_pos (-(b / 8) * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε)
        nlinarith only [mul_pos hT (Real.rpow_pos_of_pos hD (1 / 4 : ℝ)), he]
  have hdiffnorm : eLpNorm (fun x => F i j x - F i l x) 2 (ν.restrict E) ≤
      ENNReal.ofReal (2 * Q * Real.exp (-(b / 8) * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε)) := by
    apply (eLpNorm_sub_le (by norm_num)).trans
    apply (add_le_add (hnorm i j) (hnorm i l)).trans_eq
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  obtain ⟨hi, hbd⟩ := KernelCovarianceBounds.restricted_pair (hFmeas i j) hφ hη
    (by positivity) hMφ hMη hφM hηM (hnorm i j)
  obtain ⟨hi', hbd'⟩ := KernelCovarianceBounds.restricted_pair ((hFmeas i j).sub (hFmeas i l)) hφ hη
    (by positivity) hMφ hMη hφM hηM hdiffnorm
  refine ⟨hi, hbd.trans ?_, hi', hbd'⟩
  gcongr
  linarith only [hQ]

end Riesz2.PerturbationBounds
