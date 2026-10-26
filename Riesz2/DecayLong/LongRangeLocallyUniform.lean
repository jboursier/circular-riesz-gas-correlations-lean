/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.LongRangeResult
public import Riesz2.DecayLong.UpperCorrelations

/-!
# Local uniformity in inverse temperature

The constants convention in the Notation subsection of the paper (Subsection 1.9) means that on each closed interval `0 < βlo ≤ βhi`, one positive
upper constant and one positive lower rate work for every temperature in that
interval. The stretched-exponential power is chosen before the interval.
For the negative covariance, the starting volume may still depend on β and
the mesoscopic sequence. Taking the singleton interval `[β, β]` recovers the
fixed-temperature interface without changing its quantifiers.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2.LowerCorrelations

/-- The negative bound in Theorem 1 of the paper,
uniform on a compact temperature interval. The proof uses Lemma 5.19
and the same separated blocks. Only the limiting coefficient is bounded using βhi. -/
theorem separated_block_covariance_lower_locallyUniform
    (s : Riesz1.RieszExponent) (βlo βhi : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi → ∀ n : ℕ → ℕ,
      Tendsto (fun m => (n m : ℝ)) atTop atTop →
      Tendsto (fun m => (n m : ℝ) / (Riesz1.particleNumber m : ℝ)) atTop (𝓝 0) →
      ∀ᶠ m in atTop, ∃ i j : Fin (Riesz1.particleNumber m : ℕ),
        (n m : ℝ) / 2 ≤ (Riesz1.cyclicIndexDistance (Riesz1.particleNumber m) i j : ℝ) ∧
        (Riesz1.cyclicIndexDistance (Riesz1.particleNumber m) i j : ℝ) ≤ (n m : ℝ) ∧
        ProbabilityTheory.covariance (fun X => Riesz2.gap X (i.val : ℤ))
          (fun X => Riesz2.gap X (j.val : ℤ))
          (gibbsMeasure (ofLong β s) (Riesz1.particleNumber m)) ≤
          -c₀ * (Riesz1.cyclicIndexDistance (Riesz1.particleNumber m) i j : ℝ) ^ (s.val - 2) := by
  let βmax : InverseTemperature := ⟨βhi, hlo.trans_le hle⟩
  have hβmax : 0 < βmax.val := βmax.property
  have hπ := Real.pi_pos
  have hσ : 0 < Riesz1.countVariance (longParameters βmax s) :=
    Riesz2.MesoscopicVariance.limiting_variance_pos βmax s
  have hs0 : 0 < s.val := s.property.1
  have hs1 : s.val < 1 := s.property.2
  have hconc := Riesz2.ToMathlib.one_add_half_rpow_lt_two_three_quarters_rpow hs0 hs1
  let F : ℝ := 1 + (1 / 2 : ℝ)^s.val - 2*(3 / 4 : ℝ)^s.val
  have hF : F < 0 := by dsimp [F]; linarith
  let Lmax : ℝ := Riesz1.countVariance (longParameters βmax s)*F/2
  have hLmax : Lmax < 0 := div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hσ hF) two_pos
  have h2pos : (0 : ℝ) < (2 : ℝ)^(s.val-2) := Real.rpow_pos_of_pos two_pos _
  refine ⟨-(8*Lmax*(2 : ℝ)^(s.val-2)), ?_, ?_⟩
  · have ht := mul_neg_of_neg_of_pos (by linarith : 8*Lmax < 0) h2pos
    linarith
  intro β hβ n hn hnratio
  have hβpos : 0 < β.val := β.property
  set σ := Riesz1.countVariance (longParameters β s) with hσdef
  set L : ℝ := σ * (1 + (1 / 2 : ℝ)^s.val - 2*(3 / 4 : ℝ)^s.val)/2 with hLdef
  have hσle : Riesz1.countVariance (longParameters βmax s) ≤ σ := by
    have hnum : 0 ≤ Real.cos (Real.pi*s.val/2)/Real.sin (Real.pi*s.val/2) := by
      have hprod := mul_nonneg hσ.le (show 0 ≤ 2*βmax.val*Real.pi*s.val by positivity)
      change 0 ≤ (Real.cos (Real.pi*s.val/2)/Real.sin (Real.pi*s.val/2) /
        (2*βmax.val*Real.pi*s.val))*(2*βmax.val*Real.pi*s.val) at hprod
      rwa [div_mul_cancel₀ _ (by positivity)] at hprod
    apply div_le_div_of_nonneg_left hnum (by positivity : 0 < 2*β.val*Real.pi*s.val)
    change 2*β.val*Real.pi*s.val ≤ 2*βhi*Real.pi*s.val
    gcongr
    exact hβ.2
  have hLle : L ≤ Lmax := by
    have ht := mul_le_mul_of_nonpos_right hσle hF.le
    dsimp only [Lmax]
    change σ*F/2 ≤ _
    linarith
  have hL : L < 0 := hLle.trans_lt hLmax
  have hr1 : Tendsto (fun m => (n m : ℝ) / (n m : ℝ)) atTop (𝓝 1) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hn.eventually_gt_atTop 0] with m hm
    exact (div_self hm.ne').symm
  have V1 := tendsto_blockCov_scaled β s n n 1 one_pos hn hnratio hr1
  have V2 := tendsto_blockCov_scaled β s n (fun m => n m - 2 * (n m / 4)) (1 / 2) (by norm_num) hn
    hnratio (tendsto_sub_two_quarter_ratio n hn)
  have V3 := tendsto_blockCov_scaled β s n (fun m => n m - n m / 4) (3 / 4) (by norm_num) hn
    hnratio (tendsto_sub_quarter_ratio n hn)
  have hlim := ((V1.add V2).sub (V3.const_mul 2)).div_const 2
  have hLval : (σ * (1 : ℝ) ^ s.val + σ * (1 / 2 : ℝ) ^ s.val -
      2 * (σ * (3 / 4 : ℝ) ^ s.val)) / 2 = L := by
    rw [Real.one_rpow, hLdef]
    ring
  rw [hLval] at hlim
  have hΨ : Tendsto (fun m => ProbabilityTheory.covariance
      (gapBlock (Riesz1.particleNumber m) 0 (n m / 4))
      (gapBlock (Riesz1.particleNumber m) (n m - n m / 4) (n m / 4))
      (gibbsMeasure (ofLong β s) (Riesz1.particleNumber m)) / (n m : ℝ) ^ s.val) atTop (𝓝 L) := by
    refine Tendsto.congr' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with m hm1
    have hN : 2 ≤ (Riesz1.particleNumber m : ℕ) := by
      show 2 ≤ m + 1
      omega
    rw [covariance_separated_identity β s m (n m) hN (by omega)]
    ring
  have hΨlt := (tendsto_order.1 hΨ).2 (Lmax / 2) (by linarith only [hLle,hLmax])
  have h2n : ∀ᶠ m in atTop, 2 * n m ≤ (Riesz1.particleNumber m : ℕ) := by
    filter_upwards [(tendsto_order.1 hnratio).2 (1 / 2 : ℝ) (by norm_num),
      hn.eventually_gt_atTop 0] with m h hpos
    have hp : (0 : ℝ) < ((Riesz1.particleNumber m : ℕ) : ℝ) := by
      show (0 : ℝ) < ((m + 1 : ℕ) : ℝ)
      positivity
    rw [div_lt_iff₀ hp] at h
    have h' : ((2 * n m : ℕ) : ℝ) < (((Riesz1.particleNumber m : ℕ)) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h'.le
  have h4 : ∀ᶠ m in atTop, 4 ≤ n m := by
    filter_upwards [hn.eventually_ge_atTop (4 : ℝ)] with m hm
    exact_mod_cast hm
  filter_upwards [hΨlt, h2n, h4] with m hΨm h2nm h4m
  have hn0 : (0 : ℝ) < n m := by exact_mod_cast (show 0 < n m by omega)
  have hns : 0 < (n m : ℝ) ^ s.val := Real.rpow_pos_of_pos hn0 _
  have hT : ProbabilityTheory.covariance (gapBlock (Riesz1.particleNumber m) 0 (n m / 4))
      (gapBlock (Riesz1.particleNumber m) (n m - n m / 4) (n m / 4))
      (gibbsMeasure (ofLong β s) (Riesz1.particleNumber m)) ≤ Lmax / 2 * (n m : ℝ) ^ s.val := by
    rw [div_lt_iff₀ hns] at hΨm
    exact hΨm.le
  have hT0 : Lmax / 2 * (n m : ℝ) ^ s.val ≤ 0 := by
    have := Real.rpow_nonneg hn0.le s.val
    nlinarith only [hLmax, mul_nonpos_of_nonpos_of_nonneg hLmax.le this]
  obtain ⟨i, j, hd1, hd2, hcov⟩ := exists_separated_pair (ofLong β s)
    (Riesz1.particleNumber m) (n m) h4m h2nm _ hT0 hT
  refine ⟨i, j, hd1, hd2, ?_⟩
  have hk := two_rpow_mul_le_rpow s.val hn0 hd1 (by linarith)
  have hL8 : 8 * Lmax < 0 := by linarith only [hLmax]
  have hfin := mul_le_mul_of_nonpos_left hk hL8.le
  have hid := sixteen_half_rpow_div_sq Lmax s.val hn0
  nlinarith

end Riesz2.LowerCorrelations

namespace Riesz2

open Riesz2.DecayShort.ShortRangeResult

/-- Theorem 1 of the paper, read with the Notation
subsection's constants convention: upper constants and the negative lower
constant are locally uniform in β. The mesoscopic starting index is chosen
separately for each temperature and sequence. -/
theorem longRangeGapCorrelations_locallyUniform (hzeta : External.PeriodicZeta)
    (hRig : External.LongRangeRigidityLocallyUniform) :
  ∀ s : Riesz1.RieszExponent,
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
        ∀ (N : ℕ+) (i j : Fin (N : ℕ)) (f g : GapObservable),
          let p := ofLong β s
          let d := Riesz1.cyclicIndexDistance N i j
          ∃ hMom : GapSecondMoments p N i.val j.val f g,
          |gapCorrelation p N i.val j.val f.val.1 g.val.1 hMom.1 hMom.2.1| ≤
            C / (1 + (d : ℝ)) ^ (2 - s.val - ε) *
              correlationFactor p N i.val f c δ d * correlationFactor p N j.val g c δ d) ∧
    (∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
      ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ n : ℕ+ → ℕ+, IsMesoscopicSequence n → ∃ m₀ : ℕ,
        ∀ m : ℕ, m₀ ≤ m →
          let N := Riesz1.particleNumber m
          ∃ i j : Fin (N : ℕ),
            (n N : ℝ) / 2 ≤ (Riesz1.cyclicIndexDistance N i j : ℝ) ∧
            (Riesz1.cyclicIndexDistance N i j : ℝ) ≤ (n N : ℝ) ∧
            ∃ hi : MemLp (fun X => gap X i.val) 2 (gibbsMeasure (ofLong β s) N),
            ∃ hj : MemLp (fun X => gap X j.val) 2 (gibbsMeasure (ofLong β s) N),
            gapCorrelation (ofLong β s) N i.val j.val id id hi hj ≤
              -c₀ * (Riesz1.cyclicIndexDistance N i j : ℝ) ^ (s.val - 2)) := by
  intro s
  constructor
  · intro ε hε
    obtain ⟨δ, hδ, hupper⟩ :=
      DecayLong.UpperCorrelations.decay_gap_correlations_upper_locallyUniform_by_threshold hzeta hRig s ε hε
    refine ⟨δ, hδ, ?_⟩
    intro βlo βhi hlo hle
    obtain ⟨C,c,hC,hc,hupper⟩ := hupper βlo βhi hlo hle
    refine ⟨C,c,hC,hc,?_⟩
    intro β hβ N i j f g
    by_cases hN : 2 ≤ (N : ℕ)
    · obtain ⟨hMom, hbound⟩ := hupper β hβ N hN i j f g
      refine ⟨hMom, ?_⟩
      have hexp : -(2 - s.val) + ε = -(2 - s.val - ε) := by ring
      simpa only [hexp, Real.rpow_neg (by positivity :
        (0 : ℝ) ≤ 1 + (Riesz1.cyclicIndexDistance N i j : ℝ)), div_eq_mul_inv] using hbound
    · have he : N = 1 := PNat.eq (by change (N : ℕ) = 1; have := N.pos; omega)
      subst N
      refine ⟨internal_gapSecondMoments_one (ofLong β s) _ _ f g, ?_⟩
      rw [internal_gapCorrelation_one (ofLong β s) _ _ f g
        (internal_gapSecondMoments_one (ofLong β s) _ _ f g), abs_zero]
      exact mul_nonneg
        (mul_nonneg (div_nonneg hC.le (Real.rpow_nonneg (by positivity) _))
          (internal_correlationFactor_nonneg ..))
        (internal_correlationFactor_nonneg ..)
  · intro βlo βhi hlo hle
    obtain ⟨c₀,hc₀,hlower⟩ := LowerCorrelations.separated_block_covariance_lower_locallyUniform
      s βlo βhi hlo hle
    refine ⟨c₀,hc₀,?_⟩
    intro β hβ n hn
    have htop : Tendsto (fun m => (n (Riesz1.particleNumber m) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_iff.mpr hn.1
    obtain ⟨m₀, hm₀⟩ := eventually_atTop.1
      (hlower β hβ (fun m => (n (Riesz1.particleNumber m) : ℕ)) htop hn.2)
    refine ⟨m₀, ?_⟩
    intro m hm
    obtain ⟨i, j, hdlo, hdhi, hcov⟩ := hm₀ m hm
    refine ⟨i, j, hdlo, hdhi,
      LowerCorrelations.gap_memLp (ofLong β s) _ _,
      LowerCorrelations.gap_memLp (ofLong β s) _ _, ?_⟩
    exact hcov

end Riesz2
