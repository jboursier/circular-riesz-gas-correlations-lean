/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.ShortRangeResult

/-!
# Distance-threshold arithmetic for the short-range theorem

The scale choices, proper-window errors and full-cycle losses in the proof
of Theorem 2 of the paper.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace Riesz2.DecayShort.ShortRangeResultPart6

/-- Scale and tilt choices in the proof of Theorem 2 of the paper.
The threshold exponent is chosen independently of temperature. -/
theorem paper_scale_parameters (s ε q₁ q₂ : ℝ) (hs : 1 < s) (hε : 0 < ε)
    (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) :
    ∃ p h : ℝ, 1 ≤ p ∧ s / (s-1/2) < p ∧ s ≤ p*(s-1/2) ∧
      2*s < p ∧ 0 < h ∧ 0 ≤ q₁*h ∧ 0 ≤ q₂*h ∧
      p*(q₁*h) ≤ ε ∧ (2*p)*(q₂*h) ≤ ε := by
  let p := 4*s
  let Q := q₁+q₂+1
  have hp : 0 < p := by dsimp [p]; linarith
  have hQ : 0 < Q := by dsimp [Q]; linarith
  let h := ε/(4*p*Q)
  have hh : 0 < h := div_pos hε (by positivity)
  have he : p*h*Q = ε/4 := by dsimp [h]; field_simp
  refine ⟨p,h,by dsimp [p]; linarith,?_,by dsimp [p]; nlinarith only [hs],
    by dsimp [p]; linarith,hh,mul_nonneg hq₁ hh.le,mul_nonneg hq₂ hh.le,?_,?_⟩
  · apply (div_lt_iff₀ (by linarith : 0 < s-1/2)).mpr
    dsimp [p]
    nlinarith only [hs]
  · have hm := mul_le_mul_of_nonneg_left (show q₁ ≤ Q by dsimp [Q]; linarith) (mul_pos hp hh).le
    nlinarith only [hm,he,hε]
  · have hm := mul_le_mul_of_nonneg_left (show q₂ ≤ Q by dsimp [Q]; linarith) (mul_pos hp hh).le
    nlinarith only [hm,he,hε]

/-- The near window in Theorem 2 fits for large volumes.
Here the paper threshold is `d ≤ N^(1/(2*p))`. Rounding contributes `B`. -/
theorem paper_window_fit {p B d n N : ℝ}
    (hp : 0 < p) (hB : 0 < B) (hd : 0 ≤ d) (hN : 1 ≤ N)
    (hn : n ≤ B*(1+d)^p) (hnear : d ≤ N^(1/(2*p)))
    (hlarge : (2*B*2^p)^2 ≤ N) : 2*n ≤ N := by
  have hN0 : 0 < N := by linarith
  have hpow1 : 1 ≤ N^(1/(2*p)) := Real.one_le_rpow hN (by positivity)
  have hpw : (1+d)^p ≤ 2^p*N^(1/2 : ℝ) := by
    have ht := Real.rpow_le_rpow (by linarith : 0 ≤ 1+d)
      (show 1+d ≤ 2*N^(1/(2*p)) by linarith) hp.le
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity),
      ← Real.rpow_mul hN0.le] at ht
    have he : 1/(2*p)*p = (1/2 : ℝ) := by field_simp
    rwa [he] at ht
  have hsquare : (N^(1/2 : ℝ))^2 = N := by
    rw [← Real.sqrt_eq_rpow,Real.sq_sqrt hN0.le]
  have hroot : 2*B*2^p ≤ N^(1/2 : ℝ) := by
    nlinarith only [hlarge,hsquare,Real.rpow_nonneg hN0.le (1/2 : ℝ),
      mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hB) (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) p)]
  have ht := mul_nonneg (sub_nonneg.mpr hroot) (Real.rpow_nonneg hN0.le (1/2 : ℝ))
  have hn' := mul_le_mul_of_nonneg_left hpw hB.le
  nlinarith only [hn,hn',ht,hsquare]

/-- The distance threshold controls the exterior error in Theorem 2.
Only `2*s*δ₀ ≤ 1` is required, independently of the window exponent. -/
theorem paper_near_exterior {s δ₀ d N : ℝ} (hs : 0 < s) (hδ₀ : 0 ≤ δ₀)
    (hd : 0 ≤ d) (hN : 1 ≤ N) (hnear : d ≤ N^δ₀) (hδs : δ₀*s ≤ 1/2) :
    N^(-(1/2 : ℝ)) ≤ 2^s*(1+d)^(-s) := by
  have hN0 : 0 < N := by linarith
  have hx : 0 < N^δ₀ := Real.rpow_pos_of_pos hN0 _
  have h1 : 1 ≤ N^δ₀ := Real.one_le_rpow hN hδ₀
  have ht := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < 1+d)
    (show 1+d ≤ 2*N^δ₀ by linarith) (by linarith : -s ≤ 0)
  have he : 2^s*(2*N^δ₀)^(-s) = N^(δ₀*(-s)) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx.le,
      ← mul_assoc,← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      add_neg_cancel,Real.rpow_zero,one_mul,← Real.rpow_mul hN0.le]
  calc
    _ ≤ N^(δ₀*(-s)) := Real.rpow_le_rpow_of_exponent_le hN (by nlinarith only [hδs])
    _ = 2^s*(2*N^δ₀)^(-s) := he.symm
    _ ≤ _ := mul_le_mul_of_nonneg_left ht (by positivity)

/-- Near-profile absorption in Theorem 2, using its distance threshold. -/
theorem paper_near_profile {s ε p a r n N B : ℝ}
    (hs : 1 < s) (hr : 1 ≤ r) (hn : r^p ≤ n) (hupper : n ≤ B*r^p)
    (hNerr : N^(-(1/2 : ℝ)) ≤ 2^s*r^(-s)) (hN : 0 ≤ N) (hps : s ≤ p*(s-1/2))
    (ha : 0 ≤ a) (hpa : p*a ≤ ε) (hB : 0 ≤ B) :
    n^a*(r^(-s)+n^(-(s-1/2))+N^(-(1/2 : ℝ))) ≤
      (2+2^s)*B^a*r^(-s+ε) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hrp0 : 0 < r^p := Real.rpow_pos_of_pos hr0 p
  have hn0 : 0 < n := hrp0.trans_le hn
  have hnerr : n^(-(s-1/2)) ≤ r^(-s) := by
    calc
      _ ≤ (r^p)^(-(s-1/2)) := Real.rpow_le_rpow_of_nonpos hrp0 hn (by linarith)
      _ = r^(p*(-(s-1/2))) := (Real.rpow_mul hr0.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hr (by nlinarith only [hps])
  have hloss : n^a ≤ B^a*r^ε := by
    calc
      _ ≤ (B*r^p)^a := Real.rpow_le_rpow hn0.le hupper ha
      _ = B^a*r^(p*a) := by rw [Real.mul_rpow hB hrp0.le,← Real.rpow_mul hr0.le]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hr hpa) (Real.rpow_nonneg hB _)
  calc
    _ ≤ (B^a*r^ε)*((2+2^s)*r^(-s)) := mul_le_mul hloss
      (by linarith only [hnerr,hNerr]) (by positivity) (by positivity)
    _ = _ := by rw [mul_mul_mul_comm,← Real.rpow_add hr0]; ring_nf

/-- Full-profile loss absorption in Theorem 2. -/
theorem paper_far_profile {s ε p a r N B : ℝ}
    (hr : 1 ≤ r) (hN : 1 ≤ N) (hupper : N ≤ B*r^p)
    (ha : 0 ≤ a) (hpa : p*a ≤ ε) (haε : a ≤ ε) (hB : 0 ≤ B) :
    N^a*(r^(-s)+N⁻¹) ≤ max (B^a) 1*(r^(-s+ε)+N^(-1+ε)) := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hloss : N^a ≤ B^a*r^ε := by
    calc
      _ ≤ (B*r^p)^a := Real.rpow_le_rpow hN0.le hupper ha
      _ = B^a*r^(p*a) := by
        rw [Real.mul_rpow hB (Real.rpow_nonneg hr0.le _),← Real.rpow_mul hr0.le]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hr hpa) (Real.rpow_nonneg hB _)
  have hfirst : N^a*r^(-s) ≤ B^a*r^(-s+ε) := by
    calc
      _ ≤ (B^a*r^ε)*r^(-s) := mul_le_mul_of_nonneg_right hloss (by positivity)
      _ = _ := by rw [mul_assoc,← Real.rpow_add hr0]; ring_nf
  have hsecond : N^a*N⁻¹ ≤ N^(-1+ε) := by
    rw [← Real.rpow_neg_one,← Real.rpow_add hN0]
    exact Real.rpow_le_rpow_of_exponent_le hN (by linarith only [haε])
  calc
    _ = N^a*r^(-s)+N^a*N⁻¹ := mul_add ..
    _ ≤ B^a*r^(-s+ε)+N^(-1+ε) := add_le_add hfirst hsecond
    _ ≤ _ := by
      rw [mul_add]
      exact add_le_add
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
        (le_mul_of_one_le_left (by positivity) (le_max_right _ _))

/-- Temperature-independent bounded volumes in Theorem 2. -/
theorem paper_bounded_sizes_one (s : ShortExponent) (ε : ℝ) (hε : 0 < ε)
    (K : ℕ+) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : InverseTemperature) (N : ℕ+), (N : ℕ) ≤ (K : ℕ) →
      ∀ (i j : Fin (N : ℕ)) (f g : GapObservable),
      let p := ofShort β s
      let d := Riesz1.cyclicIndexDistance N i j
      ∃ hMom : GapSecondMoments p N i.val j.val f g,
        |gapCorrelation p N i.val j.val f.val.1 g.val.1 hMom.1 hMom.2.1| ≤
          C * ((1 + (d : ℝ)) ^ (-s.val + ε) + (N : ℝ) ^ (-1 + ε)) *
            correlationFactor p N i.val f 1 1 d * correlationFactor p N j.val g 1 1 d := by
  let C : ℝ := 2 * ((K : ℝ) + 1) ^ 2 * (K : ℝ) * Real.exp (2 * (K : ℝ))
  have hK : (0 : ℝ) < K := by positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro β N hNK i j f g p d
  have hUf : 0 ≤ derivativeSup f := ENNReal.toReal_nonneg
  have hUg : 0 ≤ derivativeSup g := ENNReal.toReal_nonneg
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hNK' : (N : ℝ) ≤ K := by exact_mod_cast hNK
  have hdK : (d : ℝ) ≤ K := by
    have hd : d ≤ (N : ℕ) := by
      have hi := i.isLt
      have hj := j.isLt
      dsimp only [d, Riesz1.cyclicIndexDistance]
      omega
    exact_mod_cast hd.trans hNK
  let P : ℝ := (1 + (d : ℝ)) ^ (-s.val + ε) + (N : ℝ) ^ (-1 + ε)
  have hP : (K : ℝ)⁻¹ ≤ P := by
    calc
      (K : ℝ)⁻¹ ≤ (N : ℝ)⁻¹ := inv_anti₀ (by positivity) hNK'
      _ = (N : ℝ) ^ (-1 : ℝ) := (Real.rpow_neg_one _).symm
      _ ≤ (N : ℝ) ^ (-1 + ε) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
      _ ≤ P := le_add_of_nonneg_left (Real.rpow_nonneg (by positivity) _)
  have hP0 : 0 ≤ P := (inv_nonneg.mpr hK.le).trans hP
  have hfactor (f : GapObservable) (k : ℤ) :
      derivativeSup f * Real.exp (-(K : ℝ)) ≤ correlationFactor p N k f 1 1 d := by
    apply le_trans _ (le_add_of_nonneg_left ENNReal.toReal_nonneg)
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    apply Real.exp_le_exp.mpr
    simpa only [neg_mul, one_mul, Real.rpow_one] using neg_le_neg hdK
  have hcf := ShortRangeResult.internal_correlationFactor_nonneg p N i.val f 1 1 d
  have hcg := ShortRangeResult.internal_correlationFactor_nonneg p N j.val g 1 1 d
  have hprod : (derivativeSup f * Real.exp (-(K : ℝ))) *
      (derivativeSup g * Real.exp (-(K : ℝ))) ≤
      correlationFactor p N i.val f 1 1 d * correlationFactor p N j.val g 1 1 d :=
    mul_le_mul (hfactor f _) (hfactor g _) (by positivity) hcf
  have hlow : (2 * ((K : ℝ) + 1) ^ 2) * (derivativeSup f * derivativeSup g) ≤
      C * P * (correlationFactor p N i.val f 1 1 d *
        correlationFactor p N j.val g 1 1 d) := by
    have he : Real.exp (2 * (K : ℝ)) *
        (Real.exp (-(K : ℝ)) * Real.exp (-(K : ℝ))) = 1 := by
      rw [← Real.exp_add, ← Real.exp_add]
      rw [show 2 * (K : ℝ) + (-(K : ℝ) + -(K : ℝ)) = 0 by ring, Real.exp_zero]
    calc
      _ = C * (K : ℝ)⁻¹ * ((derivativeSup f * Real.exp (-(K : ℝ))) *
          (derivativeSup g * Real.exp (-(K : ℝ)))) := by
        dsimp only [C]
        calc
          _ = (2 * ((K : ℝ) + 1)^2) * (derivativeSup f * derivativeSup g) *
              ((K : ℝ) * (K : ℝ)⁻¹) *
              (Real.exp (2 * (K : ℝ)) * (Real.exp (-(K : ℝ)) *
                Real.exp (-(K : ℝ)))) := by rw [mul_inv_cancel₀ hK.ne', he]; ring
          _ = _ := by ring
      _ ≤ C * P * ((derivativeSup f * Real.exp (-(K : ℝ))) *
          (derivativeSup g * Real.exp (-(K : ℝ)))) := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left hprod (mul_nonneg hC.le hP0)
  refine ⟨ShortRangeResult.internal_gapSecondMoments p N i j f g, ?_⟩
  change |covariance (fun X => f.val.1 (gap X i.val))
    (fun X => g.val.1 (gap X j.val)) (gibbsMeasure p N)| ≤ _
  have hnK : ((N : ℝ) + 1)^2 ≤ ((K : ℝ) + 1)^2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  calc
    _ ≤ 2 * ((N : ℝ) + 1)^2 * derivativeSup f * derivativeSup g :=
      ShortRangeResult.internal_covariance_bound p N i j f g
    _ ≤ 2 * ((K : ℝ) + 1)^2 * derivativeSup f * derivativeSup g := by
      gcongr
    _ = (2 * ((K : ℝ) + 1)^2) * (derivativeSup f * derivativeSup g) := by ring
    _ ≤ _ := by simpa only [P, mul_assoc] using hlow

end Riesz2.DecayShort.ShortRangeResultPart6
