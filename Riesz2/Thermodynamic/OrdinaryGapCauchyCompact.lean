/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.OrdinaryGapCauchyV2
public import Riesz2.Thermodynamic.LengthVariancePart2
public import Riesz2.Frozen.TwoVolumeComparisonV2
public import Riesz2.ToMathlib.ComparisonRates

/-!
# Compact-temperature ordinary gap comparison

The untilted comparison in Proposition 6.6 of the paper, with the strict support radius
and constants chosen before β.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Riesz2.OrdinaryGapCauchyV2
open OrdinaryGapCauchy

open InterpolatingDensities in
/-- Proposition 6.6 of the paper, the expectation estimate following
equation (6.27): removing the tilt costs an exponential times the global derivative
sum. Its explicit tail power depends only on `s, ε`, before the temperature
interval and the cutoff are chosen. -/
theorem tilt_expectation_fixed_power_locallyUniform (s ε βlo βhi : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (hε : 0 < ε) (θ : PhysicalCutoff) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ N n : ℕ+, 2 ≤ (N : ℕ) → ∀ hn : (n : ℕ) ≤ (N : ℕ), ∀ G : BlockObservable n,
        Integrable (fun X => G.val (finiteGapBlock X)) (gibbsMeasure p N) ∧
        Integrable (fun X => G.val (finiteGapBlock X)) (tiltedParticleMeasure p N n hn θ ε true) ∧
        |(∫ X, G.val (finiteGapBlock X) ∂tiltedParticleMeasure p N n hn θ ε true) -
          (∫ X, G.val (finiteGapBlock X) ∂gibbsMeasure p N)| ≤
            C * Real.exp (-c * (n : ℝ) ^ (ε * min s 1)) * blockDerivativeNorm G := by
  obtain ⟨A, c, hA, hc, hrate⟩ := LengthVariance.compact_penalty_support
    s ε βlo βhi hs hε hlo hle θ
  obtain ⟨z, hz, hnorm⟩ := InterpolantLocalLaws.compact_tilt_normalizer
    s ε βlo βhi hs hs1 hε hlo hle θ
  obtain ⟨L, hL, hm⟩ := SingleGapTails.single_gap_moments s βlo βhi hs hs1 hlo hle 1 (by norm_num)
  let δ := ε * min s 1
  let K := L * (2 + (2 : ℝ) ^ (1 / s))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let C := z⁻¹ * (Real.sqrt A + A) * (K + 1)
  have hC : 0 < C := mul_pos (mul_pos (inv_pos.mpr hz) (by positivity)) (by linarith)
  refine ⟨C, c / 2, hC, by positivity, fun p hps hpl hph N n hN hn G => ?_⟩
  have : IsProbabilityMeasure (gibbsMeasure p N) := gibbsMeasure_probability p N
  have : IsProbabilityMeasure (tiltedParticleMeasure p N n hn θ ε true) :=
    (tilt_valid p N n hn θ ε true).2.2
  have hiμ := block_integrable N n G (gibbsMeasure p N)
  have hiQ := block_integrable N n G (tiltedParticleMeasure p N n hn θ ε true)
  refine ⟨hiμ, hiQ, ?_⟩
  have hgapnorm (j : Fin (n : ℕ)) : eLpNorm (fun X : Riesz1.Configuration N => gap X j.val) 2
      (gibbsMeasure p N) ≤ ENNReal.ofReal K := by
    have ht := (hm p hps hpl hph N hN j.val 2 (by norm_num)).1
    simp only [Real.rpow_one, ENNReal.ofReal_ofNat] at ht
    exact (le_add_of_nonneg_right zero_le).trans ht
  obtain ⟨hf, hfnorm⟩ := internal_centered_block_norm (gibbsMeasure p N) G
    (finiteGapBlock (K := n)) (fun j => Riesz1.measurable_gap j.val) hK hgapnorm
  have hR : 0 ≤ (n : ℝ) ^ ε := by positivity
  have hG := DecayShort.activeGapPenalty_measurable (N := N) θ hR true (activeLabels N n hn)
  have hG0 := DecayShort.activeGapPenalty_nonneg (N := N) θ hR true (activeLabels N n hn)
  rw [activeGapPenalty_eq] at hG hG0
  have hrare := hrate p hps hpl hph N n hN hn
  have hZ := hnorm p hps hpl hph N n hN hn
  let q := A * Real.exp (-c * (n : ℝ) ^ δ)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have he := NonnegativeTilt.abs_integral_expTilt_sub_le hG p.property.1.le hG0 hf hrare
  have heq : NonnegativeTilt.expTilt (gibbsMeasure p N) p.val.1
      (physicalGapPenalty N n hn θ ε true) = tiltedParticleMeasure p N n hn θ ε true := rfl
  rw [heq, integral_sub hiQ (integrable_const _), integral_sub hiμ (integrable_const _)] at he
  simp only [integral_const, probReal_univ, one_smul, sub_sub_sub_cancel_right] at he
  apply he.trans
  have hZi : (NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (physicalGapPenalty N n hn θ ε true))⁻¹ ≤ z⁻¹ := inv_anti₀ hz hZ
  have hroot : Real.sqrt q = Real.sqrt A * Real.exp (-(c / 2) * (n : ℝ) ^ δ) := by
    apply (Real.sqrt_eq_iff_eq_sq hq (by positivity)).mpr
    rw [mul_pow, Real.sq_sqrt hA.le, ← Real.exp_nat_mul]
    dsimp only [q]
    congr 2
    ring
  have hq' : q ≤ A * Real.exp (-(c / 2) * (n : ℝ) ^ δ) := by
    apply mul_le_mul_of_nonneg_left _ hA.le
    apply Real.exp_le_exp.mpr
    have hp : 0 ≤ (n : ℝ) ^ δ := by positivity
    nlinarith
  have hs : Real.sqrt q + q ≤ (Real.sqrt A + A) * Real.exp (-(c / 2) * (n : ℝ) ^ δ) := by
    rw [hroot]
    nlinarith
  calc
    _ ≤ (z⁻¹ * ((Real.sqrt A + A) * Real.exp (-(c / 2) * (n : ℝ) ^ δ))) *
        ((K + 1) * blockDerivativeNorm G) := by
      apply mul_le_mul _ hfnorm (Real.sqrt_nonneg _) (by positivity)
      exact mul_le_mul hZi hs (by positivity) (by positivity)
    _ = _ := by dsimp [C]; ring

/-- Proposition 6.6 of the paper, second assertion of equation (6.26):
the ordinary laws retain the restricted derivative norm and an exponential
remainder on the full symmetric support. Structural parameters and the tail
power precede the compact temperature interval, as for the tilted assertion. -/
theorem ordinary_gap_comparison_good_set_locallyUniform :
    ∀ s : {s : ℝ // 0 < s ∧ s ≠ 1},
    ∃ Kₛ κ ε₀ : ℝ, 1 < Kₛ ∧ 0 < κ ∧ 0 < ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    ∀ _θ : PhysicalCutoff, ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    let p : Parameters := ⟨(β.val, s.val), β.property, s.property⟩
    ∀ (n N N' : ℕ+) (_ : 2 ≤ (n : ℕ)),
      (N : ℕ) ≤ (N' : ℕ) → 4 * (n : ℕ) ≤ (N : ℕ) →
      (n : ℝ) ^ (2 / s.val) ≤ (N : ℝ) →
    ∀ K : ℕ, K ≤ (n : ℕ) / 4 →
      ((n : ℕ) % 4 ≠ 1 ∨ K < (n : ℕ) / 4) → ∀ G : BlockObservable n,
      DependsOnBlockCoordinates G (symmetricMiddleBlock n K) →
      Integrable (fun X : Riesz1.Configuration N => G.val (finiteGapBlock X))
        (gibbsMeasure p N) ∧
      Integrable (fun X : Riesz1.Configuration N' => G.val (finiteGapBlock X))
        (gibbsMeasure p N') ∧
      |(∫ X : Riesz1.Configuration N, G.val (finiteGapBlock X) ∂gibbsMeasure p N) -
        (∫ X : Riesz1.Configuration N', G.val (finiteGapBlock X) ∂gibbsMeasure p N')| ≤
        C * (n : ℝ) ^ (κ * ε - min s.val 1 / 2) *
          (restrictedBlockDerivativeNorm G (symmetricMiddleBlock n K)
              (goodBlockEvent s.val n N (Kₛ * ε)) +
            Real.exp (-c * (n : ℝ) ^ δ) * blockDerivativeNorm G) := by
  intro s
  obtain ⟨Ks, κ, ε₀, hKs, hκ, hε₀, hcompare⟩ := Riesz2.twoVolumeComparisonV2 s
  refine ⟨Ks, κ, ε₀, hKs, hκ, hε₀, ?_⟩
  intro ε hε hsmall
  obtain ⟨δ, hδ, hcompare⟩ := hcompare ε hε hsmall
  let d := ε * min s.val 1
  have hd : 0 < d := mul_pos hε (lt_min s.property.1 zero_lt_one)
  refine ⟨min d δ, lt_min hd hδ, ?_⟩
  intro θ βlo βhi hlo hle
  obtain ⟨C, c, hC, hc, hcompare⟩ := hcompare θ βlo βhi hlo hle
  obtain ⟨A, b, hA, hb, htilt⟩ := tilt_expectation_fixed_power_locallyUniform
    s.val ε βlo βhi s.property.1 s.property.2 hlo hle hε θ
  let q := κ * ε - min s.val 1 / 2
  obtain ⟨D, e, hD, he, hcombine⟩ := ComparisonRates.combine_errors
    q d δ (2 * A) C b c hd hδ (by positivity) hC.le hb hc
  refine ⟨D, e, hD, he, ?_⟩
  intro β hβ p n N N' hn hNN' hnN hscale K hK hstrict G hG
  have hN : 2 ≤ (N : ℕ) := by omega
  have hN' : 2 ≤ (N' : ℕ) := by omega
  have hnle : (n : ℕ) ≤ (N : ℕ) := by omega
  have hnle' : (n : ℕ) ≤ (N' : ℕ) := by omega
  have ht := hcompare β hβ n N N' hn hNN' hnN hscale hnle hnle'
  have ht := ht.2.2.2.2.2.2 K hK hstrict G hG
  have htN := htilt p rfl hβ.1 hβ.2 N n hN hnle G
  have htN' := htilt p rfl hβ.1 hβ.2 N' n hN' hnle' G
  refine ⟨htN.1, htN'.1, ?_⟩
  apply hcombine (n : ℝ)
    (restrictedBlockDerivativeNorm G (symmetricMiddleBlock n K)
      (goodBlockEvent s.val n N (Ks * ε))) (blockDerivativeNorm G)
    (∫ X : Riesz1.Configuration N, G.val (finiteGapBlock X) ∂gibbsMeasure p N)
    (∫ X : Riesz1.Configuration N', G.val (finiteGapBlock X) ∂gibbsMeasure p N')
    (∫ X, G.val (finiteGapBlock X) ∂tiltedParticleMeasure p N n hnle θ ε true)
    (∫ X, G.val (finiteGapBlock X) ∂tiltedParticleMeasure p N' n hnle' θ ε true)
    (by exact_mod_cast n.pos) (by unfold restrictedBlockDerivativeNorm; positivity)
    (by unfold blockDerivativeNorm; positivity) _ ht.2.2
  have hsum := add_le_add htN.2.2 htN'.2.2
  have hnonneg : 0 ≤ (2 * A) * (n : ℝ) ^ q *
      restrictedBlockDerivativeNorm G (symmetricMiddleBlock n K)
        (goodBlockEvent s.val n N (Ks * ε)) := by
    unfold restrictedBlockDerivativeNorm
    positivity
  dsimp only [d] at hsum ⊢
  nlinarith only [hsum, hnonneg]

/-- Proposition 6.6 of the paper, ordinary gap expectations:
specialize the good-set comparison to the global derivative norm, uniformly
on the temperature interval. The support translation uses radius `k-1`, as
in the written proof of Theorem 3. -/
theorem ordinary_gap_cauchy_locallyUniform
    (s : {s : ℝ // 0 < s ∧ s ≠ 1}) (ζ : ℝ) (hζ : 0 < ζ)
    (βlo βhi : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C : ℝ, 0 < C ∧
    ∀ p : Parameters, p.val.2 = s.val → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
    ∀ (n N N' : ℕ+) (_ : 2 ≤ (n : ℕ)),
      (N : ℕ) ≤ (N' : ℕ) → 4 * (n : ℕ) ≤ (N : ℕ) →
      (n : ℝ) ^ (2 / s.val) ≤ (N : ℝ) →
      ∀ (G : BlockObservable n) (J : Finset (Fin (n : ℕ))),
        MiddleConsecutiveBlock n J → DependsOnBlockCoordinates G J →
        Integrable (fun X : Riesz1.Configuration N => G.val (finiteGapBlock X))
          (gibbsMeasure p N) ∧
        Integrable (fun X : Riesz1.Configuration N' => G.val (finiteGapBlock X))
          (gibbsMeasure p N') ∧
        |(∫ X : Riesz1.Configuration N, G.val (finiteGapBlock X) ∂gibbsMeasure p N) -
          (∫ X : Riesz1.Configuration N', G.val (finiteGapBlock X) ∂gibbsMeasure p N')| ≤
          C * (n : ℝ) ^ (-min s.val 1 / 2 + ζ) * blockDerivativeNorm G := by
  classical
  obtain ⟨Ks, κ, ε₀, hKs, hκ, hε₀, hcompare⟩ :=
    ordinary_gap_comparison_good_set_locallyUniform s
  let ε := min (ε₀ / 2) (ζ / (2 * κ))
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hε₀' : ε < ε₀ := (min_le_left _ _).trans_lt (by linarith)
  have hκε : κ * ε ≤ ζ := by
    have hh := min_le_right (ε₀ / 2) (ζ / (2 * κ))
    have hh' := (le_div_iff₀ (by positivity : 0 < 2 * κ)).mp hh
    dsimp only [ε]
    nlinarith
  obtain ⟨δ, hδ, hcompare⟩ := hcompare ε hε hε₀'
  obtain ⟨θ⟩ := DefinitionSanity.physicalCutoff_nonempty
  obtain ⟨C, c, hC, hc, hcompare⟩ := hcompare θ βlo βhi hlo hle
  let q := -min s.val 1 / 2 + ζ
  refine ⟨2 * C, by positivity, ?_⟩
  intro p hps hpl hph
  let β : InverseTemperature := ⟨p.val.1, p.property.1⟩
  have hp : (⟨(β.val, s.val), β.property, s.property⟩ : Parameters) = p := by
    apply Subtype.ext
    simp only [β, ← hps]
  have hcompare := hcompare β ⟨hpl, hph⟩
  change ∀ (n N N' : ℕ+) (_ : 2 ≤ (n : ℕ)), _ at hcompare
  rw [hp] at hcompare
  intro n N N' hn hNN' hnN hscale G J hJ hG
  have hN : 2 ≤ (N : ℕ) := by omega
  have hN' : 2 ≤ (N' : ℕ) := by omega
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ (n : ℕ) by omega)
  have hD (H : BlockObservable n) : 0 ≤ blockDerivativeNorm H := by
    unfold blockDerivativeNorm; positivity
  have hsymmetric (K : ℕ) (hK : K ≤ (n : ℕ) / 4)
      (hKstrict : (n : ℕ) % 4 ≠ 1 ∨ K < (n : ℕ) / 4) (H : BlockObservable n)
      (hH : DependsOnBlockCoordinates H (symmetricMiddleBlock n K)) :
      |(∫ X : Riesz1.Configuration N, H.val (finiteGapBlock X) ∂gibbsMeasure p N) -
        (∫ X : Riesz1.Configuration N', H.val (finiteGapBlock X) ∂gibbsMeasure p N')| ≤
        (2 * C) * (n : ℝ) ^ q * blockDerivativeNorm H := by
    have ht := hcompare n N N' hn hNN' hnN hscale K hK hKstrict H hH
    have hrestricted := restricted_le_global H (symmetricMiddleBlock n K)
      (goodBlockEvent s.val n N (Ks * ε))
    have hexp : Real.exp (-c * (n : ℝ) ^ δ) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ (n : ℝ) ^ δ := by positivity
      nlinarith
    have hpower : (n : ℝ) ^ (κ * ε - min s.val 1 / 2) ≤ (n : ℝ) ^ q :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [q]; linarith)
    calc
      _ ≤ C * (n : ℝ) ^ (κ * ε - min s.val 1 / 2) *
          (blockDerivativeNorm H + 1 * blockDerivativeNorm H) := by
        apply ht.2.2.trans
        gcongr
        exact hD H
      _ ≤ 2 * C * (n : ℝ) ^ q * blockDerivativeNorm H := by
        nlinarith [mul_le_mul_of_nonneg_right hpower
          (mul_nonneg hC.le (hD H))]
  have := gibbsMeasure_probability p N
  have := gibbsMeasure_probability p N'
  refine ⟨InterpolatingDensities.block_integrable N n G _,
    InterpolatingDensities.block_integrable N' n G _, ?_⟩
  obtain ⟨a, k, hk, hak, hJeq, _⟩ := hJ
  by_cases hk0 : k = 0
  · have hconst : ∀ x, G.val x = G.val 0 := by
      intro x
      apply hG
      intro i hi
      have hi' : a ≤ i.val ∧ i.val < a + k := by simpa [hJeq] using hi
      omega
    simp only [hconst, integral_const, probReal_univ, smul_eq_mul, one_mul, sub_self, abs_zero]
    exact mul_nonneg (by positivity) (hD G)
  · have hkpos : 1 ≤ k := by omega
    let b := (n : ℕ) / 2 - 1
    have hb : b + k ≤ (n : ℕ) := by dsimp [b]; omega
    have hG' : DependsOnBlockCoordinates G
        (Finset.univ.filter (fun i => a ≤ i.val ∧ i.val < a + k)) := by
      simpa [← hJeq] using hG
    obtain ⟨H, hH, hnorm, hint⟩ := interval_transport a b k hak hb G hG'
    have hsupport : DependsOnBlockCoordinates H (symmetricMiddleBlock n (k - 1)) := by
      intro x y hxy
      apply hH
      intro i hi
      apply hxy
      have hi' : b ≤ i.val ∧ i.val < b + k := by simpa using hi
      simp only [symmetricMiddleBlock, Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp [b] at hi'
      omega
    have hh := hsymmetric (k - 1) (by omega) (Or.inr (by omega)) H hsupport
    rw [hint p N hN, hint p N' hN'] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hnorm (by positivity))

end Riesz2.OrdinaryGapCauchyV2
