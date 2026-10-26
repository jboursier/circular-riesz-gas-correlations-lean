/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.ShortRangeResult
public import Riesz2.DecayShort.ShortRangeResultPart2
public import Riesz2.DecayShort.ShortRangeResultPart3
public import Riesz2.DecayShort.ShortRangeResultPart4
public import Riesz2.DecayShort.ShortRangeResultPart6
public import Riesz2.DecayShort.GapObservableApproximation
public import Riesz2.Sanity.SmoothCutoff
public import Riesz1.Variance.APrioriRotationTranslationLabels

/-!
# Short-range gap correlations

Theorem 2 of the paper, using the physical covariance representations,
cyclic transport, two scales, and quantitative removal of the upper tilt.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace Riesz2.DecayShort.ShortRangeResultPart5

set_option backward.isDefEq.respectTransparency false in
/-- The full-cycle covariance estimate in the proof of Theorem 2,
with the loss and exceptional exponent chosen before temperature. The law,
ambient Hessian and tangent source are the physical ones. -/
theorem full_covariance_decay :
    ∀ s : ShortExponent, ∃ q : ℝ, 0 < q ∧
      ∀ h : ℝ, 0 < h → ∃ δ : ℝ, 0 < δ ∧
      ∀ θ : PhysicalCutoff, ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
      ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
      ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      let p := ofShort β s
      ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (b : Bool)
        (i j : Fin (N : ℕ)) (f g : GapObservable),
        let ν := fullIntrinsicTiltedGapLaw p N θ h b
        ENNReal.ofReal |covariance
          (fun X : Riesz1.Configuration N => f.val.1 (gap X i.val))
          (fun X : Riesz1.Configuration N => g.val.1 (gap X j.val))
          (tiltedParticleMeasure p N N le_rfl θ h b)| ≤
          ENNReal.ofReal (A*(N : ℝ)^(q*h)*
            ((1+(Riesz1.cyclicIndexDistance N i j : ℝ))^(-s.val)+(N : ℝ)⁻¹)) *
            (eLpNorm (fun z => f.val.2 (1+z.val i)) 2 ν+
              ENNReal.ofReal (Real.exp (-c*(N : ℝ)^δ))*
                ENNReal.ofReal (derivativeSup f)) *
            eLpNorm (fun z => g.val.2 (1+z.val j)) 2 ν := by
  intro s
  obtain ⟨q,hq,hdec⟩ := PhysicalDecay.full_physical_decay_compact s
  refine ⟨q,hq,fun h hh => ?_⟩
  obtain ⟨δ,hδ,hdec⟩ := hdec h hh
  refine ⟨δ,hδ,fun θ βlo βhi hlo hle => ?_⟩
  obtain ⟨A,c,hA,hc,hdec⟩ := hdec θ βlo βhi hlo hle
  refine ⟨A,c,hA,hc,fun β hβ => ?_⟩
  intro p N hN b i j f g ν
  obtain ⟨_,_,_,W,Q,hW,hval,hV,hQ,_,_,hdec⟩ := hdec β hβ N hN b
  obtain ⟨χ,η,hχ,hη,hχb,_,_,_,u,hu,hcov⟩ :=
    ShortRangeResultPart3.internal_full_coordinate_covariance p hN θ h b
      W hW hval Q hV hQ i j f g
  have hχt : eLpNorm χ ∞ ν < ⊤ := hχb.trans_lt ENNReal.ofReal_lt_top
  have hb := (hdec i χ hχt).2 u hu j
  have hnormχ : ENNReal.ofReal ‖χ‖ = eLpNorm (fun z => f.val.2 (1+z.val i)) 2 ν := by
    rw [ofReal_norm,Lp.enorm_def,eLpNorm_congr_ae hχ]
  have hnormη : ENNReal.ofReal ‖η‖ = eLpNorm (fun z => g.val.2 (1+z.val j)) 2 ν := by
    rw [ofReal_norm,Lp.enorm_def,eLpNorm_congr_ae hη]
  have hdist := Riesz1.cyclicIndexDistance_comm' N j i
  rw [hnormχ, hdist] at hb
  rw [← ShortRangeResultPart3.full_covariance_pullback p θ h b i j f g,hcov]
  calc
    ENNReal.ofReal |inner ℝ η (u j).val| ≤ ENNReal.ofReal (‖η‖*‖(u j).val‖) :=
      ENNReal.ofReal_le_ofReal (abs_real_inner_le_norm _ _)
    _ = ENNReal.ofReal ‖(u j).val‖ * eLpNorm (fun z => g.val.2 (1+z.val j)) 2 ν := by
      rw [ENNReal.ofReal_mul (norm_nonneg _),hnormη,mul_comm]
    _ ≤ _ := mul_le_mul' (hb.trans (mul_le_mul' le_rfl
      (add_le_add le_rfl (mul_le_mul' le_rfl hχb)))) le_rfl

/-- A pair at cyclic distance at most `n/4-1` fits in the middle half of
one cyclic interval. See the proof of Theorem 2 in the paper.
Negative starts, wrapping intervals and coincident labels are included. -/
theorem pair_window (N : ℕ+) (i j : Fin (N : ℕ)) (k : ℕ) (hk : 0 < k)
    (hd : Riesz1.cyclicIndexDistance N i j < k) :
    ∃ (a : ℤ) (u v : Fin (4*k)),
      Riesz1.labelOf N (a+u.val) = i ∧ Riesz1.labelOf N (a+v.val) = j ∧
      4*k ≤ 4*(u.val+1) ∧ 4*(u.val+1) ≤ 3*(4*k) ∧
      4*k ≤ 4*(v.val+1) ∧ 4*(v.val+1) ≤ 3*(4*k) ∧
      |(v.val : ℝ)-(u.val : ℝ)| = (Riesz1.cyclicIndexDistance N i j : ℝ) := by
  obtain ⟨t,ht,htd⟩ := Riesz1.APG.exists_shift_of_cyclicIndexDistance (N := N) i j
  have habs : |t| < (k : ℤ) := by
    rw [Int.abs_eq_natAbs,htd]
    exact_mod_cast hd
  have htlo := (abs_lt.mp habs).1
  have hthi := (abs_lt.mp habs).2
  let v : ℕ := ((2*k : ℕ)+t : ℤ).toNat
  have hv : (v : ℤ) = (2*k : ℕ)+t := Int.toNat_of_nonneg (by omega)
  refine ⟨(i.val : ℤ)-(2*k : ℕ),⟨2*k,by omega⟩,⟨v,by omega⟩,?_,?_,
    by dsimp; omega,by dsimp; omega,by dsimp; omega,by dsimp; omega,?_⟩
  · simp only [Nat.cast_mul,Nat.cast_ofNat,sub_add_cancel,Riesz1.labelOf_natCast]
  · simpa only [show (i.val : ℤ)-(2*k : ℕ)+(v : ℤ) = (i.val : ℤ)+t by omega] using ht
  · have he : ((v : ℤ)-(2*k : ℕ)) = t := by omega
    have hh := congrArg (fun x : ℤ => (x : ℝ)) he
    push_cast at hh
    change |(v : ℝ)-(2*k : ℕ)| = _
    push_cast
    rw [hh,← Int.cast_abs,Int.abs_eq_natAbs,htd]
    norm_cast

/-- The upper-only forcing is supported on the upper one-gap tail.
See the proof of Theorem 2 in the paper. This sharper form avoids temperature
dependence of the exceptional exponent. -/
theorem upper_penalty_mass (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) (R : ℝ) (hR : 0 < R) (I : Finset (Fin (N : ℕ))) :
    (gibbsMeasure p N).real {X | activeGapPenalty θ R false I X ≠ 0} ≤
      3*(I.card : ℝ)*Real.exp (-(Real.log 2/8)*R) := by
  have := gibbsMeasure_probability p N
  have hsub : {X | activeGapPenalty θ R false I X ≠ 0} ⊆
      ⋃ i ∈ I, {X | R/2 ≤ gap X i.val} := by
    intro X hX
    have hex : ∃ i ∈ I, θ.val (gap X i.val/R) ≠ 0 := by
      by_contra! he
      apply hX
      simp only [activeGapPenalty,Bool.false_eq_true,ite_false,add_zero]
      exact Finset.sum_eq_zero he
    obtain ⟨i,hi,hne⟩ := hex
    simp only [mem_iUnion,mem_ofPred_eq]
    refine ⟨i,hi,?_⟩
    have ht := half_lt_of_cutoff_ne_zero θ
      (div_nonneg (Riesz1.gap_pos X i.val).le hR.le) hne
    have := (lt_div_iff₀ hR).mp ht
    change 1/2*R < gap X i.val at this
    linarith
  calc
    _ ≤ (gibbsMeasure p N).real (⋃ i ∈ I, {X | R/2 ≤ gap X i.val}) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ i ∈ I, (gibbsMeasure p N).real {X | R/2 ≤ gap X i.val} :=
      measureReal_biUnion_finset_le I _
    _ ≤ ∑ _i ∈ I, 3*Real.exp (-(Real.log 2/8)*R) := by
      apply Finset.sum_le_sum
      intro i _
      convert measureReal_le_of_le_ofReal (by positivity)
        (gap_upper_tail p N hN i.val (R/2)) using 1
      congr 2
      ring
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]; ring

/-- A positive half-normalizer gives a density bound for arbitrary real
functions, including non-Borel derivative representatives. Internal measure
comparison used by the proof of Theorem 2. -/
theorem internal_tilt_norm (p : Parameters) (N : ℕ+) (θ : PhysicalCutoff)
    (R : ℝ) (hR : 0 ≤ R) (I : Finset (Fin (N : ℕ)))
    (hz : 1/2 ≤ NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (activeGapPenalty θ R false I)) (F : Riesz1.Configuration N → ℝ) :
    eLpNorm F 2 (activeTilt p N θ R false I) ≤ 2*eLpNorm F 2 (gibbsMeasure p N) := by
  have := gibbsMeasure_probability p N
  have hG := activeGapPenalty_measurable θ hR false I
  have hG0 := activeGapPenalty_nonneg θ hR false I
  have hz0 : 0 < NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (activeGapPenalty θ R false I) := lt_of_lt_of_le (by norm_num) hz
  have hzinv : (NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (activeGapPenalty θ R false I))⁻¹ ≤ 2 := by
    have := inv_anti₀ (by norm_num : (0 : ℝ)<1/2) hz
    norm_num at this ⊢
    exact this
  have hμ : activeTilt p N θ R false I ≤ (2 : ℝ≥0∞) • gibbsMeasure p N := by
    rw [activeTilt,NonnegativeTilt.expTilt_eq_withDensity hG p.property.1.le hG0,
      ← withDensity_const]
    apply withDensity_mono
    apply ae_of_all
    intro X
    change ENNReal.ofReal _ ≤ 2
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
    apply ENNReal.ofReal_le_ofReal
    exact (mul_le_of_le_one_right (inv_nonneg.mpr hz0.le)
      (NonnegativeTilt.exp_neg_mul_le_one p.property.1.le hG0 X)).trans hzinv
  have hb := (eLpNorm_mono_measure F hμ).trans
    (eLpNorm_smul_measure_le 2 F 2 (gibbsMeasure p N))
  apply hb.trans
  change (2 : ℝ≥0∞)^((1/(2 : ℝ≥0∞)).toReal)*_ ≤ _
  apply mul_le_mul' _ le_rfl
  have he : (1/(2 : ℝ≥0∞)).toReal = (1/2 : ℝ) := by norm_num
  rw [he]
  exact (ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num : (1/2 : ℝ) ≤ 1)).trans
    (by simp)

/-- Above a threshold depending only on the forcing exponent, the upper
tilt has normalizer at least one half. See the proof of Theorem 2 in the paper.
The threshold is uniform in temperature, cutoff, size and active labels. -/
theorem upper_tilt_threshold (h : ℝ) (hh : 0 < h) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ (p : Parameters) (N : ℕ+), 2 ≤ (N : ℕ) →
      ∀ (θ : PhysicalCutoff) (I : Finset (Fin (N : ℕ))), K ≤ I.card →
        (gibbsMeasure p N).real
          {X | activeGapPenalty θ ((I.card : ℝ)^h) false I X ≠ 0} ≤
            3*(I.card : ℝ)*Real.exp (-(Real.log 2/8)*(I.card : ℝ)^h) ∧
        3*(I.card : ℝ)*Real.exp (-(Real.log 2/8)*(I.card : ℝ)^h) ≤ 1/2 ∧
        1/2 ≤ NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
          (activeGapPenalty θ ((I.card : ℝ)^h) false I) := by
  have ha : 0 < Real.log 2/8 := div_pos (Real.log_pos one_lt_two) (by norm_num)
  obtain ⟨B,hB,hpoly⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := 1) (c := Real.log 2/8) (c' := Real.log 2/16) hh (by linarith)
  obtain ⟨K,hK⟩ := exists_threshold_exp (Kq := 3*B) hh
    (show 0 < Real.log 2/16 by linarith)
  refine ⟨max K 2,le_max_right _ _,fun p N hN θ I hI => ?_⟩
  have := gibbsMeasure_probability p N
  have hi : (1 : ℝ) ≤ I.card := by exact_mod_cast (show 1 ≤ I.card by omega)
  have hm := upper_penalty_mass p N hN θ ((I.card : ℝ)^h)
    (Real.rpow_pos_of_pos (by linarith) _) I
  have hsmall : 3*(I.card : ℝ)*Real.exp (-(Real.log 2/8)*(I.card : ℝ)^h) ≤ 1/2 := by
    have hb := hpoly (I.card : ℝ) hi
    rw [Real.rpow_one] at hb
    calc
      _ ≤ (3*B)*Real.exp (-(Real.log 2/16)*(I.card : ℝ)^h) := by linarith
      _ ≤ _ := hK I.card (by omega)
  have hnorm := NonnegativeTilt.one_sub_expTiltNormalizer_le
    (μ := gibbsMeasure p N)
    (activeGapPenalty_measurable θ (Real.rpow_nonneg (Nat.cast_nonneg I.card) h) false I)
    p.property.1.le (activeGapPenalty_nonneg θ
      (Real.rpow_nonneg (Nat.cast_nonneg I.card) h) false I)
  exact ⟨hm,hsmall,by linarith⟩

/-- Quantitative covariance removal for the upper-only tilt in
Theorem 2 of the paper. The exponent is exactly the prescribed forcing
exponent `h`. The rate `log 2/32` is independent of temperature. -/
theorem upper_tilt_covariance_locallyUniform (s βlo βhi h : ℝ) (hs : 1 < s)
    (hβ : 0 < βlo) (hβhi : βlo ≤ βhi) (hh : 0 < h) :
    ∃ D : ℝ, 0 < D ∧ ∀ (p : Parameters), p.val.2 = s → p.val.1 ∈ Icc βlo βhi →
      ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (θ : PhysicalCutoff)
        (I : Finset (Fin (N : ℕ))), 1 ≤ I.card →
        3*(I.card : ℝ)*Real.exp (-(Real.log 2/8)*(I.card : ℝ)^h) ≤ 1/2 →
        ∀ (f g : GapObservable) (i j : ℤ),
          |covariance (fun X => f.val.1 (gap X i)) (fun X => g.val.1 (gap X j))
              (gibbsMeasure p N) -
            covariance (fun X => f.val.1 (gap X i)) (fun X => g.val.1 (gap X j))
              (activeTilt p N θ ((I.card : ℝ)^h) false I)| ≤
            D*Real.exp (-(Real.log 2/32)*(I.card : ℝ)^h)*derivativeSup f*derivativeSup g := by
  obtain ⟨D2,hD2,hm2⟩ := gap_moment_bound_locallyUniform (s := s) (βlo := βlo) (βhi := βhi) (by linarith)
    (ne_of_gt hs) hβ hβhi 2 (by norm_num)
  obtain ⟨D4,hD4,hm4⟩ := gap_moment_bound_locallyUniform (s := s) (βlo := βlo) (βhi := βhi) (by linarith)
    (ne_of_gt hs) hβ hβhi 4 (by norm_num)
  have ha : 0 < Real.log 2/8 := div_pos (Real.log_pos one_lt_two) (by norm_num)
  obtain ⟨B,hB,hpoly⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := 1) (c := Real.log 2/16) (c' := Real.log 2/32) hh (by linarith)
  let M := Real.sqrt (8*D4+8)+6*(2*D2+2)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨4*Real.sqrt 3*B*M+1,by positivity,fun p hps hpβ N hN θ I hI hsmall f g i j => ?_⟩
  have := gibbsMeasure_probability p N
  have hn1 : (1 : ℝ) ≤ I.card := by exact_mod_cast hI
  have hn0 : 0 < (I.card : ℝ) := lt_of_lt_of_le zero_lt_one hn1
  have hR : 1 ≤ (I.card : ℝ)^h := Real.one_le_rpow hn1 hh.le
  let q := 3*(I.card : ℝ)*Real.exp (-(Real.log 2/8)*(I.card : ℝ)^h)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := by dsimp [q]; linarith
  have hmass := upper_penalty_mass p N hN θ ((I.card : ℝ)^h)
    (Real.rpow_pos_of_pos hn0 h) I
  have hnorm := NonnegativeTilt.one_sub_expTiltNormalizer_le (μ := gibbsMeasure p N)
    (activeGapPenalty_measurable θ (Real.rpow_nonneg hn0.le h) false I)
    p.property.1.le (activeGapPenalty_nonneg θ (Real.rpow_nonneg hn0.le h) false I)
  have hz : 1/2 ≤ NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (activeGapPenalty θ ((I.card : ℝ)^h) false I) := by linarith
  let K := (NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (activeGapPenalty θ ((I.card : ℝ)^h) false I))⁻¹*(Real.sqrt q+q)
  have hz0 : 0 < NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (activeGapPenalty θ ((I.card : ℝ)^h) false I) := lt_of_lt_of_le (by norm_num) hz
  have hzinv : (NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (activeGapPenalty θ ((I.card : ℝ)^h) false I))⁻¹ ≤ 2 := by
    simpa using inv_anti₀ (by norm_num : (0 : ℝ)<1/2) hz
  have hsq1 : Real.sqrt q ≤ 1 := (Real.sqrt_le_sqrt hq1).trans_eq (by norm_num)
  have hqsq : q ≤ Real.sqrt q := by
    nlinarith only [Real.mul_self_sqrt hq0, Real.sqrt_nonneg q,hsq1]
  have hK0 : 0 ≤ K := mul_nonneg (inv_nonneg.mpr hz0.le) (by positivity)
  have hKsq : K ≤ 4*Real.sqrt q := by
    dsimp [K]
    calc
      _ ≤ 2*(Real.sqrt q+q) := mul_le_mul_of_nonneg_right hzinv (by positivity)
      _ ≤ _ := by linarith only [hqsq]
  have hK4 : K ≤ 4 := by linarith only [hKsq,hsq1]
  have hD (r D : ℝ)
      (hm : ∀ k : ℤ, Integrable (fun X : Riesz1.Configuration N => gap X k^r)
        (gibbsMeasure p N) ∧
        Integrable (fun X : Riesz1.Configuration N => gap X k^(-r)) (gibbsMeasure p N) ∧
        (∫ X, gap X k^r ∂gibbsMeasure p N)+(∫ X, gap X k^(-r) ∂gibbsMeasure p N) ≤ D)
      (k : ℤ) : ∫ X, gap X k^r ∂gibbsMeasure p N ≤ D := by
    have ht := (hm k).2.2
    have hnn : 0 ≤ ∫ X, gap X k^(-r) ∂gibbsMeasure p N := integral_nonneg
      (fun X => Real.rpow_nonneg (Riesz1.gap_pos X k).le (-r))
    linarith only [ht,hnn]
  have hb := covariance_activeTilt_pair_le p θ hR false I (by norm_num : (0 : ℝ)<1/2)
    hz hmass (rfl : K = _) f g i j
    (hm2 p hps hpβ N hN i).1 (hm2 p hps hpβ N hN j).1
    (hm4 p hps hpβ N hN i).1 (hm4 p hps hpβ N hN j).1
    (hD 2 D2 (hm2 p hps hpβ N hN) i)
    (hD 2 D2 (hm2 p hps hpβ N hN) j)
    (hD 4 D4 (hm4 p hps hpβ N hN) i)
    (hD 4 D4 (hm4 p hps hpβ N hN) j)
  have hcoeff : Real.sqrt (8*D4+8)+(2+K)*(2*D2+2) ≤ M := by
    dsimp [M]
    nlinarith only [hK4,hD2]
  have hsqrt : Real.sqrt q ≤ Real.sqrt 3*(I.card : ℝ)*
      Real.exp (-(Real.log 2/16)*(I.card : ℝ)^h) := by
    have he : Real.exp (-(Real.log 2/8)*(I.card : ℝ)^h) =
        (Real.exp (-(Real.log 2/16)*(I.card : ℝ)^h))^2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    dsimp [q]
    rw [he,Real.sqrt_mul (by positivity),Real.sqrt_sq (Real.exp_pos _).le,
      Real.sqrt_mul (by norm_num)]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    nlinarith only [Real.sq_sqrt hn0.le,Real.sqrt_nonneg (I.card : ℝ),hn1]
  have hpoly' := hpoly (I.card : ℝ) hn1
  rw [Real.rpow_one] at hpoly'
  have hsqrt' : Real.sqrt q ≤ Real.sqrt 3*B*
      Real.exp (-(Real.log 2/32)*(I.card : ℝ)^h) := by
    calc
      _ ≤ _ := hsqrt
      _ ≤ _ := by nlinarith only [hpoly',Real.sqrt_nonneg (3 : ℝ)]
  have hU : 0 ≤ derivativeSup f := ENNReal.toReal_nonneg
  have hV : 0 ≤ derivativeSup g := ENNReal.toReal_nonneg
  calc
    _ ≤ K*(derivativeSup f*derivativeSup g)*
        (Real.sqrt (8*D4+8)+(2+K)*(2*D2+2)) := hb
    _ ≤ (4*Real.sqrt q)*(derivativeSup f*derivativeSup g)*M := by
      apply mul_le_mul _ hcoeff (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right hKsq (mul_nonneg hU hV)
    _ = Real.sqrt q*(4*M*(derivativeSup f*derivativeSup g)) := by ring
    _ ≤ (Real.sqrt 3*B*Real.exp (-(Real.log 2/32)*(I.card : ℝ)^h))*
        (4*M*(derivativeSup f*derivativeSup g)) :=
      mul_le_mul_of_nonneg_right hsqrt' (by positivity)
    _ = (4*Real.sqrt 3*B*M)*Real.exp (-(Real.log 2/32)*(I.card : ℝ)^h)*
        derivativeSup f*derivativeSup g := by ring
    _ ≤ _ := by
      gcongr
      exact le_add_of_nonneg_right zero_le_one

/-- Singleton specialization of tilt removal in Theorem 2. -/
theorem upper_tilt_covariance (s β h : ℝ) (hs : 1 < s) (hβ : 0 < β) (hh : 0 < h) :
    ∃ D : ℝ, 0 < D ∧ ∀ (p : Parameters), p.val.2 = s → p.val.1 = β →
      ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (θ : PhysicalCutoff)
        (I : Finset (Fin (N : ℕ))), 1 ≤ I.card →
        3*(I.card : ℝ)*Real.exp (-(Real.log 2/8)*(I.card : ℝ)^h) ≤ 1/2 →
        ∀ (f g : GapObservable) (i j : ℤ),
          |covariance (fun X => f.val.1 (gap X i)) (fun X => g.val.1 (gap X j))
              (gibbsMeasure p N) -
            covariance (fun X => f.val.1 (gap X i)) (fun X => g.val.1 (gap X j))
              (activeTilt p N θ ((I.card : ℝ)^h) false I)| ≤
            D*Real.exp (-(Real.log 2/32)*(I.card : ℝ)^h)*derivativeSup f*derivativeSup g := by
  obtain ⟨D,hD,hremove⟩ := upper_tilt_covariance_locallyUniform s β β h hs hβ le_rfl hh
  exact ⟨D,hD,fun p hps hpβ => hremove p hps (by rw [hpβ]; exact ⟨le_rfl,le_rfl⟩)⟩

/-- Internal derivative comparison under the actual upper tilt, including
all Lebesgue-a.e. representatives. See the proof of Theorem 2 in the paper. -/
theorem internal_tilt_derivative (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) (R : ℝ) (hR : 0 ≤ R) (I : Finset (Fin (N : ℕ)))
    (hz : 1/2 ≤ NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (activeGapPenalty θ R false I)) (i : Fin (N : ℕ)) (f : GapObservable) :
    eLpNorm (fun X => f.val.2 (gap X i.val)) 2 (activeTilt p N θ R false I) ≤
        2*gapDerivativeNorm p N i.val f ∧
    eLpNorm (fun X => f.val.2 (gap X i.val)) ∞ (activeTilt p N θ R false I) ≤
        ENNReal.ofReal (derivativeSup f) := by
  refine ⟨internal_tilt_norm p N θ R hR I hz _,?_⟩
  have hg : (gibbsMeasure p N).map (fun X => gap X i.val) ≪ volume := by
    obtain ⟨ρ,_,_,_,hρ⟩ := GapDensities.gapLaw_marginal_density p N hN i
    have hvec : Measurable (gapVector (N := N)) := Riesz1.measurable_gapVector N
    rw [show (gibbsMeasure p N).map (fun X => gap X i.val) =
        (gapLaw p N).map (fun y => y i) by
      rw [gapLaw,Measure.map_map (measurable_pi_apply i) hvec]; rfl,hρ]
    exact withDensity_absolutelyContinuous _ _
  have ht : activeTilt p N θ R false I ≪ gibbsMeasure p N :=
    Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
  have := activeTilt_isProbabilityMeasure p θ hR false I
  exact (ShortRangeResultPart3.internal_derivative_memLp (Riesz1.measurable_gap _)
    ((ht.map (Riesz1.measurable_gap _)).trans hg) f).2

/-- Exact intrinsic-to-particle derivative seminorm transport in the full
branch of the proof of Theorem 2. -/
theorem full_derivative_norm (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) (h : ℝ) (b : Bool) (i : Fin (N : ℕ)) (f : GapObservable) :
    eLpNorm (fun z : gapTangentSpace N => f.val.2 (1+z.val i)) 2
        (fullIntrinsicTiltedGapLaw p N θ h b) =
      eLpNorm (fun X => f.val.2 (gap X i.val)) 2
        (tiltedParticleMeasure p N N le_rfl θ h b) := by
  have := PhysicalDecay.full_physical_wellposed p N hN θ h b
  have hp := this.2.2.1
  have : IsProbabilityMeasure (fullIntrinsicTiltedGapLaw p N θ h b) := hp
  have hf := (ShortRangeResultPart3.internal_derivative_memLp (by fun_prop)
    (ShortRangeResultPart3.full_coordinate_absolutelyContinuous p hN θ h b i) f).1
  rw [PhysicalDecay.full_intrinsic_tilted_eq_map] at hf ⊢
  rw [eLpNorm_map_measure hf.aestronglyMeasurable
    (DefinitionSanity.intrinsic_projection_measurable N).aemeasurable]
  congr 1
  funext X
  exact congrArg f.val.2 (congrArg (fun y : EuclideanSpace ℝ (Fin (N : ℕ)) => y i)
    (PhysicalDecay.internal_full_chart_gap N X))

/-- Rounding a distance window to a multiple of four preserves the polynomial
scale and leaves room for both labels. See the proof of Theorem 2 in the paper.
The optional minimum `K` permits the half-normalizer threshold. -/
theorem rounded_scale (r p : ℝ) (hr : 1 ≤ r) (hp : 1 ≤ p) (K : ℕ) (hK : 1 ≤ K) :
    let k := max K ⌈4*r^p⌉₊
    0 < k ∧ r < (k : ℝ) ∧ r^p ≤ (4*k : ℕ) ∧
      (4*k : ℕ) ≤ (4*(K : ℝ)+20)*r^p := by
  intro k
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hrp : 1 ≤ r^p := Real.one_le_rpow hr (by linarith)
  have hrrp : r ≤ r^p := by
    simpa using Real.rpow_le_rpow_of_exponent_le hr hp
  have hceil : 4*r^p ≤ (⌈4*r^p⌉₊ : ℝ) := Nat.le_ceil _
  have hceil' : (⌈4*r^p⌉₊ : ℝ) < 4*r^p+1 := Nat.ceil_lt_add_one (by positivity)
  have hkK : K ≤ k := le_max_left _ _
  have hkceil : ⌈4*r^p⌉₊ ≤ k := le_max_right _ _
  have hkceilR : (⌈4*r^p⌉₊ : ℝ) ≤ k := by exact_mod_cast hkceil
  have hkupper : (k : ℝ) ≤ (K : ℝ)+(⌈4*r^p⌉₊ : ℝ) := by
    exact_mod_cast (show max K ⌈4*r^p⌉₊ ≤ K+⌈4*r^p⌉₊ by omega)
  have hKpow : (K : ℝ) ≤ K*r^p := le_mul_of_one_le_right (by positivity) hrp
  refine ⟨by omega,by linarith,?_,?_⟩ <;> push_cast
  · linarith
  · nlinarith only [hkupper,hceil',hKpow,hrp]

/-- The proper covariance estimate on an arbitrary cyclic active interval,
expressed on the particle tilt, as used in the proof of Theorem 2.
All seminorms retain their measures. -/
theorem proper_cyclic_covariance_decay :
    ∀ s : ShortExponent, ∃ q : ℝ, 0 < q ∧
      ∀ h : ℝ, 0 < h → ∃ δ : ℝ, 0 < δ ∧
      ∀ θ : PhysicalCutoff, ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
      ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
      ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      let p := ofShort β s
      ∀ (N n : ℕ+), 4 ≤ (N : ℕ) → 2 ≤ (n : ℕ) →
        2*(n : ℕ) ≤ (N : ℕ) → ∀ (_hn : (n : ℕ) ≤ (N : ℕ)) (b : Bool) (a : ℤ),
        let μ := activeTilt p N θ ((n : ℝ)^h) b (cyclicInterval N a n)
        ∀ i : Fin (n : ℕ), (n : ℕ) ≤ 4*(i.val+1) →
          4*(i.val+1) ≤ 3*(n : ℕ) → ∀ (j : Fin (n : ℕ)) (f g : GapObservable),
          ENNReal.ofReal |covariance (fun X => f.val.1 (gap X (a+i.val)))
            (fun X => g.val.1 (gap X (a+j.val))) μ| ≤
            ENNReal.ofReal (A*(n : ℝ)^(q*h)*
              ((1+|(j.val : ℝ)-(i.val : ℝ)|)^(-s.val)+
                (n : ℝ)^(-(s.val-1/2))+(N : ℝ)^(-(1/2 : ℝ)))) *
              (eLpNorm (fun X => f.val.2 (gap X (a+i.val))) 2 μ+
                ENNReal.ofReal (Real.exp (-c*(n : ℝ)^δ))*
                  eLpNorm (fun X => f.val.2 (gap X (a+i.val))) ∞ μ) *
              eLpNorm (fun X => g.val.2 (gap X (a+j.val))) 2 μ := by
  intro s
  obtain ⟨q,hq,hdec⟩ := ShortRangeResultPart2.proper_covariance_decay s
  refine ⟨q,hq,fun h hh => ?_⟩
  obtain ⟨δ,hδ,hdec⟩ := hdec h hh
  refine ⟨δ,hδ,fun θ βlo βhi hlo hle => ?_⟩
  obtain ⟨A,c,hA,hc,hdec⟩ := hdec θ βlo βhi hlo hle
  refine ⟨A,c,hA,hc,fun β hβ => ?_⟩
  intro p N n hN hn2 hhalf hn b a μ i hil hir j f g
  obtain ⟨_,_,hf,hg,hb⟩ := hdec β hβ N n hN hn2 hhalf hn b i hil hir j f g
  have hN2 : 2 ≤ (N : ℕ) := by omega
  have hnf := ShortRangeResult.internal_eLpNorm_cyclicInterval p hN2 hn θ h b a
    hf.aestronglyMeasurable 2
  have hng := ShortRangeResult.internal_eLpNorm_cyclicInterval p hN2 hn θ h b a
    hg.aestronglyMeasurable 2
  have hnft := ShortRangeResult.internal_eLpNorm_cyclicInterval p hN2 hn θ h b a
    hf.aestronglyMeasurable ∞
  change eLpNorm (fun X => f.val.2 (gap X (a+i.val))) 2 μ = _ at hnf
  change eLpNorm (fun X => g.val.2 (gap X (a+j.val))) 2 μ = _ at hng
  change eLpNorm (fun X => f.val.2 (gap X (a+i.val))) ∞ μ = _ at hnft
  rw [← hnf,← hng,← hnft,← ShortRangeResult.covariance_cyclicInterval p hN2 hn θ h b a f g i j] at hb
  exact hb

/-- Internal conversion of the extended covariance estimate, with the
two derivative norms compared to the unforced norms. Supporting
the proof of Theorem 2. All finiteness premises are explicit. -/
theorem internal_real_bound {x T E U : ℝ} {a b a' b' u' : ℝ≥0∞}
    (hT : 0 ≤ T) (hE : 0 ≤ E) (hU : 0 ≤ U) (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (ha' : a' ≤ 2*a) (hb' : b' ≤ 2*b) (hu' : u' ≤ ENNReal.ofReal U)
    (hx : ENNReal.ofReal |x| ≤ ENNReal.ofReal T*(a'+ENNReal.ofReal E*u')*b') :
    |x| ≤ T*(2*a.toReal+E*U)*(2*b.toReal) := by
  have hn : 0 ≤ T*(2*a.toReal+E*U)*(2*b.toReal) := by positivity
  have hc : ENNReal.ofReal |x| ≤ ENNReal.ofReal T*
      (2*a+ENNReal.ofReal E*ENNReal.ofReal U)*(2*b) :=
    hx.trans (mul_le_mul' (mul_le_mul' le_rfl
      (add_le_add ha' (mul_le_mul' le_rfl hu'))) hb')
  have he : ENNReal.ofReal (T*(2*a.toReal+E*U)*(2*b.toReal)) =
      ENNReal.ofReal T*(2*a+ENNReal.ofReal E*ENNReal.ofReal U)*(2*b) := by
    rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul hT,
      ENNReal.ofReal_add (by positivity) (mul_nonneg hE hU),ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_mul hE,ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_toReal ha,ENNReal.ofReal_toReal hb]
    norm_num
  rw [← he] at hc
  have ht := ENNReal.toReal_le_of_le_ofReal hn hc
  simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using ht

/-- Comparison of exponential remainders across the chosen scales.
Internal numerical step of the proof of Theorem 2. -/
theorem internal_exp_mono {d L δ h c c' : ℝ} (hd : 0 ≤ d) (hL : 1 ≤ L)
    (hdL : d ≤ L) (hδ : 0 ≤ δ) (hδh : δ ≤ h) (hc : 0 ≤ c)
    (hcc : c' ≤ c) :
    Real.exp (-c*L^h) ≤ Real.exp (-c'*d^δ) := by
  have hp : d^δ ≤ L^h := (Real.rpow_le_rpow hd hdL hδ).trans
    (Real.rpow_le_rpow_of_exponent_le hL hδh)
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left hp hc
  have hc' := mul_le_mul_of_nonneg_right hcc (Real.rpow_nonneg hd δ)
  linarith only [hm,hc']

/-- Absorb the covariance-removal error into two exponential factors and
the algebraic distance weight. See the proof of Theorem 2 in the paper.
The rate and exponent stay fixed before any volume is chosen. -/
theorem error_absorption (s δ c : ℝ) (hδ : 0 < δ) (hc : 0 < c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ d r L h : ℝ, 0 ≤ d → 1 ≤ r → d ≤ r →
      r ≤ L → δ ≤ h →
      Real.exp (-c*L^h) ≤ B*r^(-s)*(Real.exp (-(c/4)*d^δ))^2 := by
  obtain ⟨B,hB,hpoly⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := s) (c := c) (c' := c/2) hδ (by linarith)
  refine ⟨B,hB,fun d r L h hd hr hdr hrL hδh => ?_⟩
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have he := hpoly r hr
  have he' : Real.exp (-c*r^δ) ≤ B*r^(-s)*Real.exp (-(c/2)*r^δ) := by
    have hm := mul_le_mul_of_nonneg_left he (Real.rpow_nonneg hr0.le (-s))
    have hcancel : r^(-s)*r^s = 1 := by rw [← Real.rpow_add hr0]; simp
    simpa only [← mul_assoc,hcancel,one_mul,mul_comm (r^(-s)) B] using hm
  have hs := internal_exp_mono hd hr hdr hδ.le le_rfl (show 0 ≤ c/2 by linarith) le_rfl
  have hs' : Real.exp (-(c/2)*d^δ) = (Real.exp (-(c/4)*d^δ))^2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  calc
    _ ≤ Real.exp (-c*r^δ) := internal_exp_mono hr0.le (hr.trans hrL) hrL hδ.le hδh hc.le le_rfl
    _ ≤ _ := he'
    _ ≤ _ := by rw [← hs']; exact mul_le_mul_of_nonneg_left hs (by positivity)

/-- Internal last real-algebra step of the proof of Theorem 2:
the mixed terms cover the source error, and the product of exponential
remainders covers the covariance perturbation. -/
theorem internal_product_bound {x T P E Z D F A B U V C : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hP : 0 ≤ P) (hE : 0 ≤ E) (hZ : 0 ≤ Z) (hD : 0 ≤ D)
    (_hF : 0 ≤ F) (hC : 0 ≤ C)
    (hT : T ≤ C*P) (hEZ : E ≤ Z) (herror : F ≤ D*P*Z^2)
    (hx : |x| ≤ T*(2*A+E*U)*(2*B)+F*U*V) :
    |x| ≤ (4*C+D)*P*(A+U*Z)*(B+V*Z) := by
  have hsrc : T*(2*A+E*U)*(2*B) ≤ 4*C*P*(A+U*Z)*B := by
    calc
      _ ≤ (C*P)*(2*A+E*U)*(2*B) := by gcongr
      _ ≤ (C*P)*(2*(A+U*Z))*(2*B) := by
        gcongr
        nlinarith only [hEZ,hE,hZ,hU]
      _ = _ := by ring
  have herr := mul_le_mul_of_nonneg_right herror (mul_nonneg hU hV)
  have hterm₁ : C*P*(A+U*Z)*B ≤ C*P*(A+U*Z)*(B+V*Z) :=
    mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mul_nonneg hV hZ)) (by positivity)
  have hterm₂ : D*P*Z^2*(U*V) ≤ D*P*(A+U*Z)*(B+V*Z) := by
    calc
      _ = D*P*(U*Z)*(V*Z) := by ring
      _ ≤ _ := mul_le_mul
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hA) (mul_nonneg hD hP))
        (le_add_of_nonneg_left hB) (mul_nonneg hV hZ) (by positivity)
  nlinarith only [hx,hsrc,herr,hterm₁,hterm₂]

/-- Comparison of the bounded-size factors with any chosen positive rate
and exponent. Internal boundary step of the proof of Theorem 2. -/
theorem internal_bounded_factor (p : Parameters) (N : ℕ+) (i : ℤ) (f : GapObservable)
    (d : ℕ) (K c δ : ℝ) (hc : 0 ≤ c) (hδ : 0 < δ) (hdK : (d : ℝ) ≤ K) :
    correlationFactor p N i f 1 1 d ≤
      Real.exp (c*K^δ)*correlationFactor p N i f c δ d := by
  have hK : 0 ≤ K := (Nat.cast_nonneg d).trans hdK
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg d) hdK hδ.le
  have hM : 1 ≤ Real.exp (c*K^δ) := Real.one_le_exp (by positivity)
  have hE : 1 ≤ Real.exp (c*K^δ)*Real.exp (-c*(d : ℝ)^δ) := by
    rw [← Real.exp_add]
    apply Real.one_le_exp
    nlinarith only [mul_le_mul_of_nonneg_left hpow hc]
  have hD : Real.exp (-1*(d : ℝ)^(1 : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr
    (by simp)
  dsimp only [correlationFactor]
  have hA := le_mul_of_one_le_left (ENNReal.toReal_nonneg (a := gapDerivativeNorm p N i f)) hM
  have hU := mul_le_mul_of_nonneg_left (hD.trans hE) (show 0 ≤ derivativeSup f from ENNReal.toReal_nonneg)
  calc
    _ ≤ Real.exp (c*K^δ)*(gapDerivativeNorm p N i f).toReal+
        derivativeSup f*(Real.exp (c*K^δ)*Real.exp (-c*(d : ℝ)^δ)) := add_le_add hA hU
    _ = _ := by ring

/-- Bounded-size completion at the rate and exponent chosen by the unbounded
argument of Theorem 2 of the paper, uniformly in temperature. -/
theorem bounded_sizes_locallyUniform (s : ShortExponent) (ε c δ : ℝ) (hε : 0 < ε)
    (hc : 0 < c) (hδ : 0 < δ) (K : ℕ+) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : InverseTemperature) (N : ℕ+), (N : ℕ) ≤ K →
      ∀ (i j : Fin (N : ℕ)) (f g : GapObservable),
        let p := ofShort β s
        let d := Riesz1.cyclicIndexDistance N i j
        ∃ hMom : GapSecondMoments p N i.val j.val f g,
        |gapCorrelation p N i.val j.val f.val.1 g.val.1 hMom.1 hMom.2.1| ≤
          C*((1+(d : ℝ))^(-s.val+ε)+(N : ℝ)^(-1+ε))*
            correlationFactor p N i.val f c δ d*correlationFactor p N j.val g c δ d := by
  obtain ⟨C₀,hC₀,hbound⟩ := ShortRangeResultPart6.paper_bounded_sizes_one s ε hε K
  let M := Real.exp (c*(K : ℝ)^δ)
  refine ⟨C₀*M^2,by dsimp [M]; positivity,fun β N hNK i j f g => ?_⟩
  intro p d
  obtain ⟨hm,hb⟩ := hbound β N hNK i j f g
  have hdK : (d : ℝ) ≤ K := by
    have hi := i.isLt
    have hj := j.isLt
    have hn : d ≤ (N : ℕ) := by dsimp [d,Riesz1.cyclicIndexDistance]; omega
    exact_mod_cast hn.trans hNK
  have hf := internal_bounded_factor p N i.val f d K c δ hc.le hδ hdK
  have hg := internal_bounded_factor p N j.val g d K c δ hc.le hδ hdK
  have hcf := ShortRangeResult.internal_correlationFactor_nonneg p N i.val f c δ d
  have hM0 : 0 ≤ M := Real.exp_nonneg _
  refine ⟨hm,hb.trans ?_⟩
  change C₀*_ *correlationFactor p N i.val f 1 1 d*correlationFactor p N j.val g 1 1 d ≤ _
  calc
    _ ≤ C₀*((1+(d : ℝ))^(-s.val+ε)+(N : ℝ)^(-1+ε))*
        (M*correlationFactor p N i.val f c δ d)*(M*correlationFactor p N j.val g c δ d) := by
      apply mul_le_mul _ hg (ShortRangeResult.internal_correlationFactor_nonneg ..) (by positivity)
      exact mul_le_mul_of_nonneg_left hf (by positivity)
    _ = _ := by ring

/-- Fixed-temperature specialization for Theorem 2 of the paper. -/
theorem bounded_sizes (s : ShortExponent) (ε c δ : ℝ) (hε : 0 < ε)
    (hc : 0 < c) (hδ : 0 < δ) (K : ℕ+) (β : InverseTemperature) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), (N : ℕ) ≤ K →
      ∀ (i j : Fin (N : ℕ)) (f g : GapObservable),
        let p := ofShort β s
        let d := Riesz1.cyclicIndexDistance N i j
        ∃ hMom : GapSecondMoments p N i.val j.val f g,
        |gapCorrelation p N i.val j.val f.val.1 g.val.1 hMom.1 hMom.2.1| ≤
          C*((1+(d : ℝ))^(-s.val+ε)+(N : ℝ)^(-1+ε))*
            correlationFactor p N i.val f c δ d*correlationFactor p N j.val g c δ d := by
  obtain ⟨C,hC,hbound⟩ := bounded_sizes_locallyUniform s ε c δ hε hc hδ K
  exact ⟨C,hC,hbound β⟩

/-- Triangle inequality for covariance removal in the proof of Theorem 2. -/
theorem internal_remove_real {x y B E : ℝ} (hy : |y| ≤ B) (he : |x-y| ≤ E) :
    |x| ≤ B+E := by
  calc
    _ ≤ |y|+|x-y| := by
      simpa only [sub_add_cancel] using (abs_add_le (x-y) y).trans_eq (add_comm _ _)
    _ ≤ _ := add_le_add hy he

/-- Full-system physical decay followed by removal of the upper tilt.
Theorem 2 of the paper: the explicit perturbation exponent is
the forcing exponent, and the physical exponent precedes temperature. -/
theorem full_unforced_decay_locallyUniform :
    ∀ s : ShortExponent, ∃ q : ℝ, 0 < q ∧
      ∀ h : ℝ, 0 < h → ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℕ, 2 ≤ K ∧
      ∀ (_θ : PhysicalCutoff) (βlo βhi : ℝ), 0 < βlo → βlo ≤ βhi →
      ∃ A c D : ℝ, 0 < A ∧ 0 < c ∧ 0 < D ∧
      ∀ (β : InverseTemperature), β.val ∈ Icc βlo βhi → ∀ (N : ℕ+), K ≤ (N : ℕ) → ∀ (i j : Fin (N : ℕ)) (f g : GapObservable),
        let p := ofShort β s
        let d := Riesz1.cyclicIndexDistance N i j
        |covariance (fun X => f.val.1 (gap X i.val)) (fun X => g.val.1 (gap X j.val))
            (gibbsMeasure p N)| ≤
          A*(N : ℝ)^(q*h)*((1+(d : ℝ))^(-s.val)+(N : ℝ)⁻¹)*
            (2*(gapDerivativeNorm p N i.val f).toReal+
              Real.exp (-c*(N : ℝ)^δ)*derivativeSup f)*
            (2*(gapDerivativeNorm p N j.val g).toReal)+
          D*Real.exp (-(Real.log 2/32)*(N : ℝ)^h)*derivativeSup f*derivativeSup g := by
  intro s
  obtain ⟨q,hq,hdec⟩ := full_covariance_decay s
  refine ⟨q,hq,fun h hh => ?_⟩
  obtain ⟨δ,hδ,hdec⟩ := hdec h hh
  obtain ⟨K,hK,hthreshold⟩ := upper_tilt_threshold h hh
  refine ⟨δ,hδ,K,hK,fun θ βlo βhi hlo hle => ?_⟩
  obtain ⟨A,c,hA,hc,hdec⟩ := hdec θ βlo βhi hlo hle
  obtain ⟨D,hD,hremove⟩ := upper_tilt_covariance_locallyUniform s.val βlo βhi h s.property hlo hle hh
  refine ⟨A,c,D,hA,hc,hD,fun β hβ N hNK i j f g => ?_⟩
  intro p d
  have hN : 2 ≤ (N : ℕ) := hK.trans hNK
  have hcfull : (Finset.univ : Finset (Fin (N : ℕ))).card = (N : ℕ) := by simp
  have hfirst : Finset.univ.map (Fin.castLEEmb (le_refl (N : ℕ))) =
      (Finset.univ : Finset (Fin (N : ℕ))) := by ext k; simp
  have he : activeTilt p N θ ((N : ℝ)^h) false Finset.univ =
      tiltedParticleMeasure p N N le_rfl θ h false := by
    rw [← hfirst,activeTilt_firstGapSet]
  obtain ⟨_,hsmall,hz⟩ := hthreshold p N hN θ Finset.univ (by simpa using hNK)
  rw [hcfull] at hsmall hz
  have hf := internal_tilt_derivative p N hN θ ((N : ℝ)^h)
    (Real.rpow_nonneg (by positivity) h) Finset.univ hz i f
  have hg := internal_tilt_derivative p N hN θ ((N : ℝ)^h)
    (Real.rpow_nonneg (by positivity) h) Finset.univ hz j g
  have hb := hdec β hβ N hN false i j f g
  dsimp only at hb
  rw [full_derivative_norm p N hN θ h false i f,
    full_derivative_norm p N hN θ h false j g,← he] at hb
  have hm := ShortRangeResult.internal_gapSecondMoments p N i j f g
  have hreal := internal_real_bound (by positivity) (Real.exp_nonneg _)
    (show 0 ≤ derivativeSup f from ENNReal.toReal_nonneg)
    hm.2.2.1.eLpNorm_ne_top hm.2.2.2.eLpNorm_ne_top hf.1 hg.1 le_rfl hb
  have hr := hremove p rfl hβ N hN θ Finset.univ (by rw [hcfull]; omega)
    (by simpa only [hcfull] using hsmall) f g i.val j.val
  rw [hcfull] at hr
  exact internal_remove_real hreal hr

/-- Singleton specialization for Theorem 2 of the paper. -/
theorem full_unforced_decay :
    ∀ s : ShortExponent, ∃ q : ℝ, 0 < q ∧
      ∀ h : ℝ, 0 < h → ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℕ, 2 ≤ K ∧
      ∀ (_θ : PhysicalCutoff) (β : InverseTemperature),
      ∃ A c D : ℝ, 0 < A ∧ 0 < c ∧ 0 < D ∧
      ∀ (N : ℕ+), K ≤ (N : ℕ) → ∀ (i j : Fin (N : ℕ)) (f g : GapObservable),
        let p := ofShort β s
        let d := Riesz1.cyclicIndexDistance N i j
        |covariance (fun X => f.val.1 (gap X i.val)) (fun X => g.val.1 (gap X j.val))
            (gibbsMeasure p N)| ≤
          A*(N : ℝ)^(q*h)*((1+(d : ℝ))^(-s.val)+(N : ℝ)⁻¹)*
            (2*(gapDerivativeNorm p N i.val f).toReal+
              Real.exp (-c*(N : ℝ)^δ)*derivativeSup f)*
            (2*(gapDerivativeNorm p N j.val g).toReal)+
          D*Real.exp (-(Real.log 2/32)*(N : ℝ)^h)*derivativeSup f*derivativeSup g := by
  intro s
  obtain ⟨q,hq,hdec⟩ := full_unforced_decay_locallyUniform s
  refine ⟨q,hq,fun h hh => ?_⟩
  obtain ⟨δ,hδ,K,hK,hdec⟩ := hdec h hh
  refine ⟨δ,hδ,K,hK,fun θ β => ?_⟩
  obtain ⟨A,c,D,hA,hc,hD,hdec⟩ := hdec θ β.val β.val β.property le_rfl
  exact ⟨A,c,D,hA,hc,hD,hdec β ⟨le_rfl,le_rfl⟩⟩

/-- Internal periodic-label identity, retaining the gap definition.
See the proof of Theorem 2 in the paper. -/
theorem internal_gap_label {N : ℕ+} (X : Riesz1.Configuration N) (t : ℤ) :
    gap X t = gap X ((Riesz1.labelOf N t).val : ℤ) := gap_eq_gapVector_labelOf X t

/-- Proper cyclic-window decay followed by upper-tilt removal. Theorem 2 of the paper. This retains the actual finite-volume errors and
the derivative norms of the unforced particle law, for every integer start. -/
theorem proper_unforced_decay_locallyUniform :
    ∀ s : ShortExponent, ∃ q : ℝ, 0 < q ∧
      ∀ h : ℝ, 0 < h → ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℕ, 2 ≤ K ∧
      ∀ (_θ : PhysicalCutoff) (βlo βhi : ℝ), 0 < βlo → βlo ≤ βhi →
      ∃ A c D : ℝ, 0 < A ∧ 0 < c ∧ 0 < D ∧
      ∀ (β : InverseTemperature), β.val ∈ Icc βlo βhi → ∀ (N n : ℕ+), 4 ≤ (N : ℕ) → K ≤ (n : ℕ) → 2*(n : ℕ) ≤ (N : ℕ) →
      ∀ (_hn : (n : ℕ) ≤ (N : ℕ)) (a : ℤ) (i : Fin (n : ℕ)),
      (n : ℕ) ≤ 4*(i.val+1) → 4*(i.val+1) ≤ 3*(n : ℕ) →
      ∀ (j : Fin (n : ℕ)) (f g : GapObservable),
        let p := ofShort β s
        |covariance (fun X => f.val.1 (gap X (a+i.val)))
            (fun X => g.val.1 (gap X (a+j.val))) (gibbsMeasure p N)| ≤
          A*(n : ℝ)^(q*h)*((1+|(j.val : ℝ)-(i.val : ℝ)|)^(-s.val)+
            (n : ℝ)^(-(s.val-1/2))+(N : ℝ)^(-(1/2 : ℝ)))*
            (2*(gapDerivativeNorm p N (a+i.val) f).toReal+
              Real.exp (-c*(n : ℝ)^δ)*derivativeSup f)*
            (2*(gapDerivativeNorm p N (a+j.val) g).toReal)+
          D*Real.exp (-(Real.log 2/32)*(n : ℝ)^h)*derivativeSup f*derivativeSup g := by
  intro s
  obtain ⟨q,hq,hdec⟩ := proper_cyclic_covariance_decay s
  refine ⟨q,hq,fun h hh => ?_⟩
  obtain ⟨δ,hδ,hdec⟩ := hdec h hh
  obtain ⟨K,hK,hthreshold⟩ := upper_tilt_threshold h hh
  refine ⟨δ,hδ,K,hK,fun θ βlo βhi hlo hle => ?_⟩
  obtain ⟨A,c,hA,hc,hdec⟩ := hdec θ βlo βhi hlo hle
  obtain ⟨D,hD,hremove⟩ := upper_tilt_covariance_locallyUniform s.val βlo βhi h s.property hlo hle hh
  refine ⟨A,c,D,hA,hc,hD,fun β hβ N n hN hnK hhalf hn a i hil hir j f g => ?_⟩
  intro p
  have hN2 : 2 ≤ (N : ℕ) := by omega
  have hcard := card_cyclicInterval a hn
  obtain ⟨_,hsmall,hz⟩ := hthreshold p N hN2 θ (cyclicInterval N a n) (by rwa [hcard])
  rw [hcard] at hsmall hz
  let u := Riesz1.labelOf N (a+i.val)
  let v := Riesz1.labelOf N (a+j.val)
  have hfi := internal_tilt_derivative p N hN2 θ ((n : ℝ)^h)
    (Real.rpow_nonneg (by positivity) h) (cyclicInterval N a n) hz u f
  have hgj := internal_tilt_derivative p N hN2 θ ((n : ℝ)^h)
    (Real.rpow_nonneg (by positivity) h) (cyclicInterval N a n) hz v g
  have hf : eLpNorm (fun X => f.val.2 (gap X (a+i.val))) 2
        (activeTilt p N θ ((n : ℝ)^h) false (cyclicInterval N a n)) ≤
      2*gapDerivativeNorm p N (a+i.val) f := by
    simpa only [gapDerivativeNorm,u,← internal_gap_label] using hfi.1
  have hft : eLpNorm (fun X => f.val.2 (gap X (a+i.val))) ∞
        (activeTilt p N θ ((n : ℝ)^h) false (cyclicInterval N a n)) ≤
      ENNReal.ofReal (derivativeSup f) := by
    simpa only [u,← internal_gap_label] using hfi.2
  have hg : eLpNorm (fun X => g.val.2 (gap X (a+j.val))) 2
        (activeTilt p N θ ((n : ℝ)^h) false (cyclicInterval N a n)) ≤
      2*gapDerivativeNorm p N (a+j.val) g := by
    simpa only [gapDerivativeNorm,v,← internal_gap_label] using hgj.1
  have hm := ShortRangeResult.internal_gapSecondMoments p N u v f g
  have hmfi : gapDerivativeNorm p N (a+i.val) f ≠ ⊤ := by
    simpa only [gapDerivativeNorm,u,← internal_gap_label] using hm.2.2.1.eLpNorm_ne_top
  have hmgj : gapDerivativeNorm p N (a+j.val) g ≠ ⊤ := by
    simpa only [gapDerivativeNorm,v,← internal_gap_label] using hm.2.2.2.eLpNorm_ne_top
  have hb := hdec β hβ N n hN (by omega) hhalf hn false a i hil hir j f g
  have hreal := internal_real_bound (by positivity) (Real.exp_nonneg _)
    (show 0 ≤ derivativeSup f from ENNReal.toReal_nonneg) hmfi hmgj hf hg hft hb
  have hr := hremove p rfl hβ N hN2 θ (cyclicInterval N a n) (by rw [hcard]; have := n.pos; omega)
    (by simpa only [hcard] using hsmall) f g (a+i.val) (a+j.val)
  rw [hcard] at hr
  exact internal_remove_real hreal hr

/-- Singleton specialization for Theorem 2 of the paper. -/
theorem proper_unforced_decay :
    ∀ s : ShortExponent, ∃ q : ℝ, 0 < q ∧
      ∀ h : ℝ, 0 < h → ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℕ, 2 ≤ K ∧
      ∀ (_θ : PhysicalCutoff) (β : InverseTemperature),
      ∃ A c D : ℝ, 0 < A ∧ 0 < c ∧ 0 < D ∧
      ∀ (N n : ℕ+), 4 ≤ (N : ℕ) → K ≤ (n : ℕ) → 2*(n : ℕ) ≤ (N : ℕ) →
      ∀ (_hn : (n : ℕ) ≤ (N : ℕ)) (a : ℤ) (i : Fin (n : ℕ)),
      (n : ℕ) ≤ 4*(i.val+1) → 4*(i.val+1) ≤ 3*(n : ℕ) →
      ∀ (j : Fin (n : ℕ)) (f g : GapObservable),
        let p := ofShort β s
        |covariance (fun X => f.val.1 (gap X (a+i.val)))
            (fun X => g.val.1 (gap X (a+j.val))) (gibbsMeasure p N)| ≤
          A*(n : ℝ)^(q*h)*((1+|(j.val : ℝ)-(i.val : ℝ)|)^(-s.val)+
            (n : ℝ)^(-(s.val-1/2))+(N : ℝ)^(-(1/2 : ℝ)))*
            (2*(gapDerivativeNorm p N (a+i.val) f).toReal+
              Real.exp (-c*(n : ℝ)^δ)*derivativeSup f)*
            (2*(gapDerivativeNorm p N (a+j.val) g).toReal)+
          D*Real.exp (-(Real.log 2/32)*(n : ℝ)^h)*derivativeSup f*derivativeSup g := by
  intro s
  obtain ⟨q,hq,hdec⟩ := proper_unforced_decay_locallyUniform s
  refine ⟨q,hq,fun h hh => ?_⟩
  obtain ⟨δ,hδ,K,hK,hdec⟩ := hdec h hh
  refine ⟨δ,hδ,K,hK,fun θ β => ?_⟩
  obtain ⟨A,c,D,hA,hc,hD,hdec⟩ := hdec θ β.val β.val β.property le_rfl
  exact ⟨A,c,D,hA,hc,hD,hdec β ⟨le_rfl,le_rfl⟩⟩

/-- Internal numerical completion at either the proper or full scale.
See the proof of Theorem 2 in the paper. -/
theorem internal_scale_finish {s x A B U V T P C D D₀ J d r L δ h t c c₀ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hD₀ : 0 ≤ D₀) (hJ : 0 ≤ J)
    (hd : 0 ≤ d) (hr : 1 ≤ r) (hdr : d ≤ r) (hrL : r ≤ L)
    (hδ : 0 < δ) (hδt : δ ≤ t) (hc₀ : 0 ≤ c₀) (hcc₀ : c ≤ c₀)
    (hc : c ≤ Real.log 2/128) (hDD₀ : D ≤ D₀)
    (hP : 0 ≤ P) (hweight : r^(-s) ≤ P)
    (hT : T ≤ C*P)
    (herror : Real.exp (-(Real.log 2/32)*L^h) ≤
      J*r^(-s)*(Real.exp (-(Real.log 2/128)*d^δ))^2)
    (hx : |x| ≤ T*(2*A+Real.exp (-c₀*L^t)*U)*(2*B)+
      D*Real.exp (-(Real.log 2/32)*L^h)*U*V) :
    |x| ≤ (4*C+D₀*J)*P*(A+U*Real.exp (-c*d^δ))*(B+V*Real.exp (-c*d^δ)) := by
  have hEZ := internal_exp_mono hd (hr.trans hrL) (hdr.trans hrL) hδ.le hδt hc₀ hcc₀
  have hZ : Real.exp (-(Real.log 2/128)*d^δ) ≤ Real.exp (-c*d^δ) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hd δ)]
  have herr : D*Real.exp (-(Real.log 2/32)*L^h) ≤
      (D₀*J)*P*(Real.exp (-c*d^δ))^2 := by
    calc
      _ ≤ D₀*(J*r^(-s)*(Real.exp (-(Real.log 2/128)*d^δ))^2) :=
        mul_le_mul hDD₀ herror (Real.exp_nonneg _) hD₀
      _ ≤ D₀*(J*P*(Real.exp (-c*d^δ))^2) := by gcongr
      _ = _ := by ring
  exact internal_product_bound hA hB hU hV hP (Real.exp_nonneg _) (Real.exp_nonneg _)
    (mul_nonneg hD₀ hJ) (by positivity) hC hT hEZ herr hx

/-- Theorem 2 of the paper, with compact-temperature constants.
For smooth observables, split at the printed distance threshold before
choosing a window. The general theorem below passes to the approximation limit. -/
theorem smooth_short_range_gap_correlations_locallyUniform :
  ∀ s : ShortExponent, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi → ∀ (N : ℕ+) (i j : Fin (N : ℕ)) (f g : GapObservable),
        ContDiff ℝ ∞ f.val.1 → ContDiff ℝ ∞ g.val.1 →
        let p := ofShort β s
        let d := Riesz1.cyclicIndexDistance N i j
        ∃ hMom : GapSecondMoments p N i.val j.val f g,
        |gapCorrelation p N i.val j.val f.val.1 g.val.1 hMom.1 hMom.2.1| ≤
          C * ((1 + (d : ℝ)) ^ (-s.val + ε) + (N : ℝ) ^ (-1 + ε)) *
            correlationFactor p N i.val f c δ d * correlationFactor p N j.val g c δ d := by
  intro s ε hε
  obtain ⟨q₁,hq₁,hproper⟩ := proper_unforced_decay_locallyUniform s
  obtain ⟨q₂,hq₂,hfull⟩ := full_unforced_decay_locallyUniform s
  obtain ⟨ρ,h,hρ,_hρpaper,hρs',hρs,hh,ha₁,ha₂,hpa₁,hpa₂⟩ :=
    ShortRangeResultPart6.paper_scale_parameters s.val ε q₁ q₂ s.property hε hq₁.le hq₂.le
  let δ₀ := 1/(2*ρ)
  have hρpos : 0 < ρ := by linarith
  have hδ₀ : 0 < δ₀ := by dsimp [δ₀]; positivity
  have hρδ₀ : ρ*δ₀ < 1 := by dsimp [δ₀]; field_simp; linarith
  have hsδ₀ : 2*s.val*δ₀ < 1 := by
    dsimp [δ₀]
    rw [mul_one_div]
    exact (div_lt_one (by positivity : 0 < 2*ρ)).mpr (by linarith only [hρs,hρpos])
  obtain ⟨δ₁,hδ₁,K₁,hK₁,hproper⟩ := hproper h hh
  obtain ⟨δ₂,hδ₂,K₂,hK₂,hfull⟩ := hfull h hh
  let δ := min δ₁ (min δ₂ h)
  have hδ : 0 < δ := lt_min hδ₁ (lt_min hδ₂ hh)
  have hδ₁' : δ ≤ δ₁ := min_le_left _ _
  have hδ₂' : δ ≤ δ₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hδh : δ ≤ h := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨θ⟩ := DefinitionSanity.physicalCutoff_nonempty
  refine ⟨δ,hδ,fun βlo βhi hlo hle => ?_⟩
  obtain ⟨A₁,c₁,D₁,hA₁,hc₁,hD₁,hproper⟩ := hproper θ βlo βhi hlo hle
  obtain ⟨A₂,c₂,D₂,hA₂,hc₂,hD₂,hfull⟩ := hfull θ βlo βhi hlo hle
  let K := max K₁ K₂
  have hK : 2 ≤ K := hK₁.trans (le_max_left _ _)
  let B : ℝ := 4*(K : ℝ)+20
  have hB : 0 < B := by dsimp [B]; positivity
  let C₁ := (2+2^s.val)*A₁*B^(q₁*h)
  let C₂ := A₂
  let C₀ := C₁+C₂
  let D₀ := D₁+D₂
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  have hC₂ : 0 < C₂ := by dsimp [C₂]; positivity
  have hC₀ : 0 < C₀ := add_pos hC₁ hC₂
  have hD₀ : 0 < D₀ := add_pos hD₁ hD₂
  let c := min c₁ (min c₂ (Real.log 2/128))
  have hc : 0 < c := lt_min hc₁ (lt_min hc₂
    (div_pos (Real.log_pos one_lt_two) (by norm_num)))
  have hcc₁ : c ≤ c₁ := min_le_left _ _
  have hcc₂ : c ≤ c₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hca : c ≤ Real.log 2/128 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨J,hJ,herror⟩ := error_absorption s.val δ (Real.log 2/32) hδ
    (div_pos (Real.log_pos one_lt_two) (by norm_num))
  rw [show Real.log 2/32/4 = Real.log 2/128 by ring] at herror
  let L := max K ⌈(2*B*2^ρ)^2⌉₊
  have hKL : K ≤ L := le_max_left _ _
  obtain ⟨Cₛ,hCₛ,hsmall⟩ := bounded_sizes_locallyUniform s ε c δ hε hc hδ ⟨L,by omega⟩
  let C := 4*C₀+D₀*J+Cₛ+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,c,hC,hc,fun β hβ N i j f g _hf _hg => ?_⟩
  intro p d
  have hfacf := ShortRangeResult.internal_correlationFactor_nonneg p N i.val f c δ d
  have hfacg := ShortRangeResult.internal_correlationFactor_nonneg p N j.val g c δ d
  let P := (1+(d : ℝ))^(-s.val+ε)+(N : ℝ)^(-1+ε)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  by_cases hNK : (N : ℕ) ≤ L
  · obtain ⟨hm,hb⟩ := hsmall β N hNK i j f g
    refine ⟨hm,hb.trans ?_⟩
    change Cₛ*P*_ * _ ≤ C*P*_ * _
    gcongr
    dsimp [C]
    linarith only [hC₀,mul_nonneg hD₀.le hJ]
  have hKN : K ≤ (N : ℕ) := by omega
  have hN : 2 ≤ (N : ℕ) := hK.trans hKN
  have hdN : d+1 ≤ (N : ℕ) := by
    have hi := i.isLt
    have hj := j.isLt
    dsimp [d,Riesz1.cyclicIndexDistance,Nat.dist]
    omega
  let r : ℝ := 1+(d : ℝ)
  have hr : 1 ≤ r := by dsimp [r]; exact le_add_of_nonneg_right (Nat.cast_nonneg d)
  have hdr : (d : ℝ) ≤ r := by dsimp [r]; linarith
  have hrN : r ≤ (N : ℝ) := by
    change 1+(d : ℝ) ≤ (N : ℝ)
    exact_mod_cast (show 1+d ≤ (N : ℕ) by omega)
  have hweight : r^(-s.val) ≤ P := by
    exact (Real.rpow_le_rpow_of_exponent_le hr (by linarith only [hε])).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _))
  have hweight' : r^(-s.val+ε) ≤ P := le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _)
  have hm := ShortRangeResult.internal_gapSecondMoments p N i j f g
  refine ⟨hm,?_⟩
  change |covariance (fun X => f.val.1 (gap X i.val)) (fun X => g.val.1 (gap X j.val))
    (gibbsMeasure p N)| ≤ C*P*correlationFactor p N i.val f c δ d*correlationFactor p N j.val g c δ d
  suffices hbound : |covariance (fun X => f.val.1 (gap X i.val)) (fun X => g.val.1 (gap X j.val))
      (gibbsMeasure p N)| ≤ (4*C₀+D₀*J)*P*
        correlationFactor p N i.val f c δ d*correlationFactor p N j.val g c δ d by
    apply hbound.trans
    gcongr
    dsimp [C]
    linarith only [hCₛ]
  by_cases hnear : (d : ℝ) ≤ (N : ℝ)^δ₀
  · let k := max K ⌈4*r^ρ⌉₊
    obtain ⟨hk,hrk,hnlower,hnupper⟩ := rounded_scale r ρ hr hρ K (by omega)
    let n : ℕ+ := ⟨4*k,by positivity⟩
    have hnlo : r^ρ ≤ (n : ℝ) := hnlower
    have hnup : (n : ℝ) ≤ B*r^ρ := hnupper
    have hrn : r ≤ (n : ℝ) := by
      have hkr : (k : ℝ) ≤ (4*k : ℕ) := by push_cast; linarith only [Nat.cast_nonneg k (α := ℝ)]
      exact hrk.le.trans hkr
    have hnk : K ≤ (n : ℕ) := by dsimp [n,k]; omega
    have hlarge : (2*B*2^ρ)^2 ≤ (N : ℝ) := by
      have ht := Nat.le_ceil ((2*B*2^ρ)^2)
      have hnL : (L : ℝ) ≤ N := by exact_mod_cast (show L ≤ (N : ℕ) by omega)
      have hceilL : (⌈(2*B*2^ρ)^2⌉₊ : ℝ) ≤ L := by
        exact_mod_cast (show ⌈(2*B*2^ρ)^(2:ℕ)⌉₊ ≤ L from le_max_right _ _)
      linarith
    have hhalfR : 2*(n : ℝ) ≤ N :=
      ShortRangeResultPart6.paper_window_fit hρpos hB (Nat.cast_nonneg d)
        (by exact_mod_cast N.pos) hnup hnear hlarge
    have hhalf : 2*(n : ℕ) ≤ (N : ℕ) := by exact_mod_cast hhalfR
    have hnN : (n : ℕ) ≤ (N : ℕ) := by omega
    have hdk : d < k := by exact_mod_cast (show (d : ℝ) < k by dsimp [r] at hrk; linarith)
    obtain ⟨a,u,v,hu,hv,hil,hir,_,_,hdist⟩ := pair_window N i j k hk hdk
    have hei (X : Riesz1.Configuration N) : gap X (a+u.val) = gap X i.val := by
      rw [internal_gap_label X (a+u.val),hu]
    have hej (X : Riesz1.Configuration N) : gap X (a+v.val) = gap X j.val := by
      rw [internal_gap_label X (a+v.val),hv]
    have hb := hproper β hβ N n (by have := n.pos; omega) ((le_max_left K₁ K₂).trans hnk)
      hhalf hnN a u hil hir v f g
    dsimp only at hb
    simp only [gapDerivativeNorm,hei,hej,hdist] at hb
    have hNerr := ShortRangeResultPart6.paper_near_exterior (lt_trans zero_lt_one s.property)
      hδ₀.le (Nat.cast_nonneg d) (by exact_mod_cast N.pos) hnear
      (by nlinarith only [hsδ₀])
    have ht := ShortRangeResultPart6.paper_near_profile s.property hr hnlo hnup
      hNerr (by positivity) hρs' ha₁ hpa₁ hB.le
    have hT : A₁*(n : ℝ)^(q₁*h)*
        (r^(-s.val)+(n : ℝ)^(-(s.val-1/2))+(N : ℝ)^(-(1/2 : ℝ))) ≤ C₀*P := by
      calc
        _ = A₁*((n : ℝ)^(q₁*h)*(r^(-s.val)+(n : ℝ)^(-(s.val-1/2))+(N : ℝ)^(-(1/2 : ℝ)))) := by ring
        _ ≤ A₁*((2+2^s.val)*B^(q₁*h)*r^(-s.val+ε)) := mul_le_mul_of_nonneg_left ht hA₁.le
        _ = C₁*r^(-s.val+ε) := by dsimp [C₁]; ring
        _ ≤ _ := mul_le_mul (le_add_of_nonneg_right hC₂.le) hweight' (by positivity) hC₀.le
    exact internal_scale_finish (s := s.val) (r := r) (L := (n : ℝ)) (δ := δ) (c := c)
      ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      hC₀.le hD₁.le hD₀.le hJ (Nat.cast_nonneg d) hr hdr hrn hδ hδ₁' hc₁.le hcc₁ hca
      (le_add_of_nonneg_right hD₂.le) hP hweight hT
      (herror d r n h (Nat.cast_nonneg d) hr hdr hrn hδh) hb
  · have hNupper : (N : ℝ) ≤ r^(2*ρ) := by
      have ht := Real.rpow_le_rpow (by positivity : 0 ≤ (N : ℝ)^δ₀)
        ((le_of_not_ge hnear).trans hdr) (by positivity : 0 ≤ 2*ρ)
      rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ N)] at ht
      have he : δ₀*(2*ρ) = 1 := by dsimp [δ₀]; field_simp
      simpa only [he,Real.rpow_one] using ht
    have haε : q₂*h ≤ ε := (le_mul_of_one_le_left ha₂ (by linarith : 1 ≤ 2*ρ)).trans hpa₂
    have ht := ShortRangeResultPart6.paper_far_profile (s := s.val) hr
      (show (1 : ℝ) ≤ N by exact_mod_cast N.pos)
      (show (N : ℝ) ≤ 1*r^(2*ρ) by simpa only [one_mul] using hNupper)
      ha₂ hpa₂ haε (by norm_num : (0 : ℝ) ≤ 1)
    simp only [Real.one_rpow,max_self,one_mul] at ht
    have hT : A₂*(N : ℝ)^(q₂*h)*(r^(-s.val)+(N : ℝ)⁻¹) ≤ C₀*P := by
      calc
        _ = A₂*((N : ℝ)^(q₂*h)*(r^(-s.val)+(N : ℝ)⁻¹)) := by ring
        _ ≤ A₂*P := mul_le_mul_of_nonneg_left ht hA₂.le
        _ = C₂*P := rfl
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₁.le) hP
    have hb := hfull β hβ N ((le_max_right K₁ K₂).trans hKN) i j f g
    exact internal_scale_finish (s := s.val) (r := r) (L := (N : ℝ)) (δ := δ) (c := c)
      ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      hC₀.le hD₂.le hD₀.le hJ (Nat.cast_nonneg d) hr hdr hrN hδ hδ₂' hc₂.le hcc₂ hca
      (le_add_of_nonneg_left hD₁.le) hP hweight hT
      (herror d r N h (Nat.cast_nonneg d) hr hdr hrN hδh) hb

/-- Theorem 2 of the paper, with compact-temperature constants.
First apply the estimate to smooth observables, then pass to the limit in
covariances and derivative L² norms, retaining the essential derivative bounds. -/
theorem paper_short_range_gap_correlations_locallyUniform :
  ∀ s : ShortExponent, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi → ∀ (N : ℕ+) (i j : Fin (N : ℕ)) (f g : GapObservable),
        let p := ofShort β s
        let d := Riesz1.cyclicIndexDistance N i j
        ∃ hMom : GapSecondMoments p N i.val j.val f g,
        |gapCorrelation p N i.val j.val f.val.1 g.val.1 hMom.1 hMom.2.1| ≤
          C * ((1 + (d : ℝ)) ^ (-s.val + ε) + (N : ℝ) ^ (-1 + ε)) *
            correlationFactor p N i.val f c δ d * correlationFactor p N j.val g c δ d := by
  intro s ε hε
  obtain ⟨δ, hδ, hsmooth⟩ := smooth_short_range_gap_correlations_locallyUniform s ε hε
  refine ⟨δ, hδ, fun βlo βhi hlo hle => ?_⟩
  obtain ⟨C, c, hC, hc, hsmooth⟩ := hsmooth βlo βhi hlo hle
  refine ⟨C, c, hC, hc, fun β hβ N i j f g => ?_⟩
  by_cases hN : 2 ≤ (N : ℕ)
  · let p := ofShort β s
    let d := Riesz1.cyclicIndexDistance N i j
    have hm := ShortRangeResult.internal_gapSecondMoments p N i j f g
    refine ⟨hm, ?_⟩
    apply GapObservableApproximation.internal_transfer p N hN i j
      (C * ((1 + (d : ℝ)) ^ (-s.val + ε) + (N : ℝ) ^ (-1 + ε))) c δ
      (mul_nonneg hC.le (add_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.rpow_nonneg (by positivity) _))) d _ f g
    intro F G hF hG
    obtain ⟨_, hbound⟩ := hsmooth β hβ N i j F G hF hG
    exact hbound
  · have he : N = 1 := PNat.eq (by change (N : ℕ) = 1; have := N.pos; omega)
    subst N
    simpa only [PNat.val_ofNat, Nat.cast_one] using
      ShortRangeResult.internal_shortRange_one s β ε C c δ hC.le i j f g

/-- Fixed-temperature specialization of Theorem 2 of the paper. -/
theorem short_range_gap_correlations :
  ∀ s : ShortExponent, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ β : InverseTemperature, ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (N : ℕ+) (i j : Fin (N : ℕ)) (f g : GapObservable),
        let p := ofShort β s
        let d := Riesz1.cyclicIndexDistance N i j
        ∃ hMom : GapSecondMoments p N i.val j.val f g,
        |gapCorrelation p N i.val j.val f.val.1 g.val.1 hMom.1 hMom.2.1| ≤
          C * ((1 + (d : ℝ)) ^ (-s.val + ε) + (N : ℝ) ^ (-1 + ε)) *
            correlationFactor p N i.val f c δ d * correlationFactor p N j.val g c δ d := by
  intro s ε hε
  obtain ⟨δ,hδ,hbound⟩ := paper_short_range_gap_correlations_locallyUniform s ε hε
  refine ⟨δ,hδ,fun β => ?_⟩
  obtain ⟨C,c,hC,hc,hbound⟩ := hbound β.val β.val β.property le_rfl
  exact ⟨C,c,hC,hc,hbound β ⟨le_rfl,le_rfl⟩⟩

end Riesz2.DecayShort.ShortRangeResultPart5
