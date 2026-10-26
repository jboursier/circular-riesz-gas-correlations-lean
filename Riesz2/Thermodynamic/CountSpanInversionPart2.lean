/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.CountSpanInversion
public import Riesz2.Thermodynamic.StationaryBias
public import Riesz2.ToMathlib.ComparisonRates
public import Riesz2.ToMathlib.WeakLawPerturbation
public import Riesz2.ToMathlib.StretchedCutoffRates
public import Riesz2.Thermodynamic.FiniteCountLimitsPart2

/-!
# Quantitative count inversion

The integer scales and probability assembly for the proof of Corollary 1.1, on the
existing suspension strip.
-/

public section
noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace Riesz2

local instance countSpanInversionPart2ConfigurationMeasurableSpace :
    MeasurableSpace LineConfiguration := configurationMeasurableSpace

/-- A sublinear power, with any fixed coefficient, is eventually below the
linear scale. This supplies the half-period room in count inversion. -/
theorem count_inversion_sublinear_scale (a A : ℝ) (ha : a < 1) :
    ∀ᶠ K : ℕ in atTop, A * (K : ℝ) ^ a ≤ (K : ℝ) / 2 := by
  have ht : Tendsto (fun K : ℕ => A * (K : ℝ) ^ (a - 1)) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by linarith : 0 < -(a - 1))).comp
      tendsto_natCast_atTop_atTop).const_mul A
  filter_upwards [ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2),
    eventually_ge_atTop 1] with K hk hK
  have hpos : 0 < (K : ℝ) := by exact_mod_cast hK
  have hh := mul_le_mul_of_nonneg_right hk.le hpos.le
  have he : (K : ℝ) ^ (a - 1) * K = (K : ℝ) ^ a := by
    calc
      _ = (K : ℝ) ^ (a - 1) * (K : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add hpos]
        congr 1
        ring
  rw [mul_assoc, he] at hh
  linarith

/-- See the proof of Corollary 1.1 in the paper: rounding leaves room
for both bracketing spans and every local block whenever `N ≥ 8K`.
The local block cutoff is twice the bracket radius, covering both sides. -/
theorem count_inversion_integer_scales (a η : ℝ) (hη : 0 < η)
    (hηa : η ≤ a) (ha : a < 1) :
    ∀ᶠ K : ℕ in atTop,
      let J := ⌈4 * (K : ℝ) ^ a⌉₊
      let h₀ := ⌈(K : ℝ) ^ η⌉₊
      1 ≤ K ∧ 1 ≤ h₀ ∧ h₀ ≤ K - J ∧ J ≤ K ∧
      K + J ≤ 2 * K ∧ h₀ ≤ (K + J) - (K - J) ∧
      (J : ℝ) ≤ 5 * (K : ℝ) ^ a ∧ (h₀ : ℝ) ≤ 2 * (K : ℝ) ^ η := by
  filter_upwards [count_inversion_sublinear_scale a 5 ha,
    count_inversion_sublinear_scale η 2 (hηa.trans_lt ha), eventually_ge_atTop 1]
      with K hlarge hsmall hK
  dsimp only
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hpa : 1 ≤ (K : ℝ) ^ a := Real.one_le_rpow hk (hη.le.trans hηa)
  have hpη : 1 ≤ (K : ℝ) ^ η := Real.one_le_rpow hk hη.le
  have hJ : (⌈4 * (K : ℝ) ^ a⌉₊ : ℝ) ≤ 5 * (K : ℝ) ^ a :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ 4 * (K : ℝ) ^ a)).le.trans (by linarith)
  have hh : (⌈(K : ℝ) ^ η⌉₊ : ℝ) ≤ 2 * (K : ℝ) ^ η :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ (K : ℝ) ^ η)).le.trans (by linarith)
  have hJK : ⌈4 * (K : ℝ) ^ a⌉₊ ≤ K := by exact_mod_cast (show (⌈4 * (K : ℝ) ^ a⌉₊ : ℝ) ≤ (K : ℝ) by linarith)
  have hsum : ⌈(K : ℝ) ^ η⌉₊ + ⌈4 * (K : ℝ) ^ a⌉₊ ≤ K := by
    exact_mod_cast (show (⌈(K : ℝ) ^ η⌉₊ : ℝ) + ⌈4 * (K : ℝ) ^ a⌉₊ ≤ K by linarith)
  have hηJ : ⌈(K : ℝ) ^ η⌉₊ ≤ ⌈4 * (K : ℝ) ^ a⌉₊ := by
    apply Nat.ceil_mono
    have := Real.rpow_le_rpow_of_exponent_le hk hηa
    linarith [Real.rpow_nonneg (by positivity : 0 ≤ (K : ℝ)) a]
  have hh1 : 1 ≤ ⌈(K : ℝ) ^ η⌉₊ := by
    exact_mod_cast (hpη.trans (Nat.le_ceil _))
  exact ⟨hK, hh1, by omega, hJK, by omega, by omega, hJ, hh⟩

/-- See the proof of Corollary 1.1 in the paper: the two endpoint
failures are rigidity failures, with strictness at the upper endpoint. -/
theorem count_inversion_endpoint_failure_subsets_internal
    (K J : ℕ) (hJ : J ≤ K) (α η : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hηα : η ≤ α) (hK : 1 ≤ K)
    (hJlo : 4 * (K : ℝ) ^ α ≤ J) :
    {y : ℤ → Ioi (0 : ℝ) | (K : ℝ) <
        gapSequenceSpan y 1 (K - J) + (K : ℝ) ^ η} ⊆
      {y | ((K - J : ℕ) : ℝ) ^ α <
        |gapSequenceSpan y 1 (K - J) - (K - J : ℕ)|} ∧
    {y : ℤ → Ioi (0 : ℝ) | gapSequenceSpan y 1 (K + J) ≤ K} ⊆
      {y | ((K + J : ℕ) : ℝ) ^ α <
        |gapSequenceSpan y 1 (K + J) - (K + J : ℕ)|} := by
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hp : 0 < (K : ℝ) ^ α := Real.rpow_pos_of_pos (by positivity) _
  have hd : (K : ℝ) ^ η ≤ (K : ℝ) ^ α := Real.rpow_le_rpow_of_exponent_le hk hηα
  have hl : ((K - J : ℕ) : ℝ) ^ α ≤ (K : ℝ) ^ α :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.sub_le K J) hα
  have hr : ((K + J : ℕ) : ℝ) ^ α ≤ 2 * (K : ℝ) ^ α := by
    calc
      _ ≤ (2 * (K : ℝ)) ^ α := Real.rpow_le_rpow (by positivity)
        (by exact_mod_cast (show K + J ≤ 2 * K by omega)) hα
      _ = (2 : ℝ) ^ α * (K : ℝ) ^ α := Real.mul_rpow (by norm_num) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (by simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hα1)
        hp.le
  have hc : ((K - J : ℕ) : ℝ) = (K : ℝ) - J := Nat.cast_sub hJ
  constructor
  · intro y hy
    change ((K - J : ℕ) : ℝ) ^ α < |gapSequenceSpan y 1 (K - J) - (K - J : ℕ)|
    have hb := le_abs_self (gapSequenceSpan y 1 (K - J) - (K - J : ℕ))
    change (K : ℝ) < _ at hy
    rw [hc] at hb ⊢
    rw [hc] at hl
    linarith
  · intro y hy
    change gapSequenceSpan y 1 (K + J) ≤ (K : ℝ) at hy
    change ((K + J : ℕ) : ℝ) ^ α < |gapSequenceSpan y 1 (K + J) - (K + J : ℕ)|
    have hb := neg_le_abs (gapSequenceSpan y 1 (K + J) - (K + J : ℕ))
    push_cast at hb hr ⊢
    linarith

/-- See the proof of Corollary 1.1 in the paper: the optimized error
threshold follows from the rounded scales, with a constant independent of `K`. -/
theorem count_inversion_error_power (s η : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (hη : 0 < η) (hηsmall : η < 1 / 4)
    (K J h₀ : ℕ) (hK : 1 ≤ K)
    (hJ : (J : ℝ) ≤ 5 * (K : ℝ) ^ (s / 2 + 2 * η))
    (hh : (h₀ : ℝ) ≤ 2 * (K : ℝ) ^ η) :
    2 * (K : ℝ) ^ η + (2 * h₀ + ((K + J) - (K - J) : ℕ) ^ (s / 2 + η)) ≤
      (6 + (10 : ℝ) ^ (s / 2 + η)) * (K : ℝ) ^ (s ^ 2 / 4 + 4 * η) := by
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hk0 : 0 < (K : ℝ) := by positivity
  have hα : 0 ≤ s / 2 + η := by positivity
  have hηe : η ≤ s ^ 2 / 4 + 4 * η := by nlinarith [sq_nonneg s]
  have hae : (s / 2 + 2 * η) * (s / 2 + η) ≤ s ^ 2 / 4 + 4 * η := by
    nlinarith [mul_pos hη (show 0 < 1 - s by linarith), sq_nonneg η]
  have hH : (((K + J) - (K - J) : ℕ) : ℝ) ≤ 2 * J := by
    exact_mod_cast (show (K + J) - (K - J) ≤ 2 * J by omega)
  have hpow : (((K + J) - (K - J) : ℕ) : ℝ) ^ (s / 2 + η) ≤
      (10 : ℝ) ^ (s / 2 + η) * (K : ℝ) ^ (s ^ 2 / 4 + 4 * η) := by
    calc
      _ ≤ (10 * (K : ℝ) ^ (s / 2 + 2 * η)) ^ (s / 2 + η) :=
        Real.rpow_le_rpow (by positivity) (by linarith) hα
      _ = (10 : ℝ) ^ (s / 2 + η) *
          (K : ℝ) ^ ((s / 2 + 2 * η) * (s / 2 + η)) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hk0.le]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hk hae) (by positivity)
  have hd := Real.rpow_le_rpow_of_exponent_le hk hηe
  nlinarith

/-- See the proof of Corollary 1.1 in the paper: an explicit polynomial
prefactor bounds the simultaneous good-event failure. All tests use the rigidity and one-gap tails on their actual half-period range. -/
theorem periodicGapLaw_count_inversion_good_bound
    (s : Riesz1.RieszExponent) (β : InverseTemperature) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ s.val / 2 + 2 * η₀ < 1 ∧ η₀ < 1 / 4 ∧
      ∀ η : ℝ, 0 < η → η < η₀ → ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
        ∀ᶠ K : ℕ in atTop, ∀ N : ℕ+, 8 * K ≤ (N : ℕ) →
          let J := ⌈4 * (K : ℝ) ^ (s.val / 2 + 2 * η)⌉₊
          let h₀ := ⌈(K : ℝ) ^ η⌉₊
          (periodicGapLaw (ofLong β s) N).toMeasure
            (countInversionGoodGaps K
              (2 * h₀ + (((K + J) - (K - J) : ℕ) : ℝ) ^ (s.val / 2 + η))
              ((K : ℝ) ^ η) (K - J) (K + J))ᶜ ≤
            ENNReal.ofReal (A * (K : ℝ) ^ (2 : ℝ) *
              Real.exp (-c * (K : ℝ) ^ (η ^ 2 / (4 * (s.val + 2))))) := by
  let p := ofLong β s
  obtain ⟨ηr, hηr, hsmallr, hrig⟩ := periodicGapLaw_finite_rigidity p
  obtain ⟨ηb, hηb, hsmallb, hblock⟩ := periodicGapLaw_simultaneous_block_rigidity p
  obtain ⟨Cg, cg, hCg, hcg, hgap⟩ := periodicGapLaw_upper_gap_tail p
  have hp : p.val.2 = s.val := rfl
  let η₀ := min (min ηr ηb) ((1 - s.val) / 16)
  have hη₀ : 0 < η₀ := lt_min (lt_min hηr hηb) (by linarith [s.property.2])
  have hη₀small : η₀ ≤ (1 - s.val) / 16 := min_le_right _ _
  refine ⟨η₀, hη₀, by linarith [s.property.2], by linarith [s.property.1],
    fun η hη hηη₀ => ?_⟩
  have hηr' : η < ηr := hηη₀.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hηb' : η < ηb := hηη₀.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  obtain ⟨Cr, cr, hCr, hcr, hr⟩ := hrig η hη hηr'
  obtain ⟨Cb, cb, hCb, hcb, hb⟩ := hblock η hη hηb'
  simp only [hp, min_eq_left s.property.2.le] at hr hb
  let b := η / (4 * (s.val + 2))
  let δ := η ^ 2 / (4 * (s.val + 2))
  let c := min cg (min cr cb)
  let C := Cg + Cr + Cb
  have hc : 0 < c := lt_min hcg (lt_min hcr hcb)
  have hC : 0 < C := by dsimp [C]; positivity
  have hη1 : η < 1 := by linarith [s.property.1]
  have hb0 : 0 < b := div_pos hη (by linarith [s.property.1])
  have hδ : 0 < δ := div_pos (sq_pos_of_pos hη) (by linarith [s.property.1])
  have hδη : δ ≤ η := by
    dsimp [δ]
    apply (div_le_iff₀ (by linarith [s.property.1] : 0 < 4 * (s.val + 2))).mpr
    nlinarith [mul_pos hη s.property.1]
  have heq : η * b = δ := by dsimp [b, δ]; ring
  refine ⟨14 * C, c, by positivity, hc, ?_⟩
  filter_upwards [count_inversion_integer_scales (s.val / 2 + 2 * η) η hη
    (by linarith [s.property.1]) (by linarith [s.property.2]), eventually_ge_atTop 1]
    with K hsc hK
  dsimp only at hsc ⊢
  intro N hKN
  let J := ⌈4 * (K : ℝ) ^ (s.val / 2 + 2 * η)⌉₊
  let h₀ := ⌈(K : ℝ) ^ η⌉₊
  let l := K - J
  let r := K + J
  have hsc' : 1 ≤ K ∧ 1 ≤ h₀ ∧ h₀ ≤ l ∧ J ≤ K ∧ r ≤ 2 * K ∧
      h₀ ≤ r - l ∧ (J : ℝ) ≤ 5 * (K : ℝ) ^ (s.val / 2 + 2 * η) ∧
      (h₀ : ℝ) ≤ 2 * (K : ℝ) ^ η := hsc
  obtain ⟨_, hh1, hhl, hJK, hrK, hhH, hJhi, hhhi⟩ := hsc'
  have hlK : l ≤ K := Nat.sub_le _ _
  have hKr : K ≤ r := by dsimp [r]; omega
  have hN : 2 ≤ (N : ℕ) := by omega
  have hlN : l ≤ (N : ℕ) / 2 := by omega
  have hrN : r ≤ (N : ℕ) / 2 := by omega
  have hHN : r - l ≤ (N : ℕ) / 2 := by omega
  have hα : 0 ≤ s.val / 2 + η := by linarith only [s.property.1, hη]
  have hα1 : s.val / 2 + η ≤ 1 := by linarith [s.property.2]
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hJlo : 4 * (K : ℝ) ^ (s.val / 2 + η) ≤ J := by
    exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hk (by linarith)) (by norm_num)).trans (Nat.le_ceil _)
  obtain ⟨hlo, hhi⟩ := count_inversion_endpoint_failure_subsets_internal K J hJK
    (s.val / 2 + η) η hα hα1 (by linarith [s.property.1]) hK hJlo
  let Q := C * Real.exp (-c * (K : ℝ) ^ δ)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hscale : (K : ℝ) ^ δ ≤ (h₀ : ℝ) ^ b := by
    calc
      _ = ((K : ℝ) ^ η) ^ b := by rw [← Real.rpow_mul (by positivity), heq]
      _ ≤ _ := Real.rpow_le_rpow (by positivity) (Nat.le_ceil _) hb0.le
  have htail (d v V : ℝ) (hd : c ≤ d) (hV : V ≤ C) (hv : (K : ℝ) ^ δ ≤ v) :
      V * Real.exp (-d * v) ≤ Q := by
    apply mul_le_mul hV (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hC.le
    have hd0 : 0 ≤ d := hc.le.trans hd
    have := mul_le_mul hd hv (by positivity : 0 ≤ (K : ℝ) ^ δ) hd0
    linarith
  have hsingle (i : ℕ) : (periodicGapLaw p N).toMeasure
      {y | (K : ℝ) ^ η < (y (i : ℤ) : ℝ)} ≤ ENNReal.ofReal Q := by
    apply (hgap N hN i ((K : ℝ) ^ η) (Real.one_le_rpow hk hη.le)).trans
    exact ENNReal.ofReal_le_ofReal (htail cg ((K : ℝ) ^ η) Cg
      (min_le_left _ _) (by dsimp [C]; linarith)
      (Real.rpow_le_rpow_of_exponent_le hk hδη))
  have hspan (k : ℕ) (hk0 : h₀ ≤ k) (hkN : k ≤ (N : ℕ) / 2) :
      (periodicGapLaw p N).toMeasure {y | (k : ℝ) ^ (s.val / 2 + η) <
        |gapSequenceSpan y 1 k - k|} ≤ ENNReal.ofReal Q := by
    apply (hr N hN k (by omega) hkN 1).trans
    exact ENNReal.ofReal_le_ofReal (htail cr ((k : ℝ) ^ b) Cr
      ((min_le_right _ _).trans (min_le_left _ _)) (by dsimp [C]; linarith)
      (hscale.trans (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hk0) hb0.le)))
  have hlow : (periodicGapLaw p N).toMeasure
      {y | (K : ℝ) < gapSequenceSpan y 1 l + (K : ℝ) ^ η} ≤ ENNReal.ofReal Q :=
    (measure_mono hlo).trans (hspan l hhl hlN)
  have hhigh : (periodicGapLaw p N).toMeasure
      {y | gapSequenceSpan y 1 r ≤ K} ≤ ENNReal.ofReal Q :=
    (measure_mono hhi).trans (hspan r (hhl.trans (hlK.trans hKr)) hrN)
  have hblocks : (periodicGapLaw p N).toMeasure
      (⋃ i ∈ Finset.range (r + 1), ⋃ h ∈ Finset.Icc h₀ (r - l),
        {y | (h : ℝ) ^ (s.val / 2 + η) < |gapSequenceSpan y (1 + (i : ℤ)) h - h|}) ≤
      ENNReal.ofReal (((r + 1 : ℕ) : ℝ) * (Finset.Icc h₀ (r - l)).card * Q) := by
    apply (hb N hN r (r - l) h₀ hh1 hHN).trans
    apply ENNReal.ofReal_le_ofReal
    dsimp only [Q]
    have ht := htail cb ((h₀ : ℝ) ^ b) Cb
      ((min_le_right _ _).trans (min_le_right _ _)) (by dsimp [C]; linarith) hscale
    simpa only [mul_assoc, b, Q] using mul_le_mul_of_nonneg_left ht
      (show 0 ≤ ((r + 1 : ℕ) : ℝ) * (Finset.Icc h₀ (r - l)).card by positivity)
  have hgapunion : (periodicGapLaw p N).toMeasure
      (⋃ i ∈ Finset.range (r + 1), {y | (K : ℝ) ^ η < (y (i : ℤ) : ℝ)}) ≤
        ENNReal.ofReal (((r + 1 : ℕ) : ℝ) * Q) := by
    apply (measure_biUnion_finset_le _ _).trans
    calc
      _ ≤ ∑ _i ∈ Finset.range (r + 1), ENNReal.ofReal Q :=
        Finset.sum_le_sum fun i _ => hsingle i
      _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg (r + 1)), ENNReal.ofReal_natCast]
  have hbad := countInversionGoodGaps_compl_subset_long_failures_internal
    (K : ℝ) ((K : ℝ) ^ η) (s.val / 2 + η) l r h₀ hh1 hhH hα hα1
  have hbound : (periodicGapLaw p N).toMeasure
      (countInversionGoodGaps K (2 * h₀ + ((r - l : ℕ) : ℝ) ^ (s.val / 2 + η))
        ((K : ℝ) ^ η) l r)ᶜ ≤
      ENNReal.ofReal (((r + 1 : ℕ) : ℝ) * Q + Q + Q +
        ((r + 1 : ℕ) : ℝ) * (Finset.Icc h₀ (r - l)).card * Q) := by
    apply (measure_mono hbad).trans
    apply ((measure_union_le _ _).trans (add_le_add
      ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)).trans
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) hQ, ENNReal.ofReal_add (by positivity) hQ]
    exact add_le_add (add_le_add (add_le_add hgapunion hlow) hhigh) hblocks
  have hr1 : ((r + 1 : ℕ) : ℝ) ≤ 3 * K := by
    exact_mod_cast (show r + 1 ≤ 3 * K by omega)
  have hcard : ((Finset.Icc h₀ (r - l)).card : ℝ) ≤ 3 * K := by
    have hcard' : (Finset.Icc h₀ (r - l)).card ≤ r - l + 1 := by
      rw [Nat.card_Icc]
      omega
    exact_mod_cast (show (Finset.Icc h₀ (r - l)).card ≤ 3 * K by omega)
  apply hbound.trans (ENNReal.ofReal_le_ofReal ?_)
  change _ ≤ 14 * C * (K : ℝ) ^ (2 : ℝ) * Real.exp (-c * (K : ℝ) ^ δ)
  rw [Real.rpow_two]
  have hm : ((r + 1 : ℕ) : ℝ) * (Finset.Icc h₀ (r - l)).card ≤ 9 * (K : ℝ) ^ 2 := by
    have ht := mul_le_mul hr1 hcard (by positivity) (by positivity : (0 : ℝ) ≤ 3 * K)
    nlinarith only [ht]
  have hcoef : ((r + 1 : ℕ) : ℝ) + 2 +
      ((r + 1 : ℕ) : ℝ) * (Finset.Icc h₀ (r - l)).card ≤ 14 * (K : ℝ) ^ 2 := by
    nlinarith only [hm, hr1, hk, sq_nonneg ((K : ℝ) - 1)]
  have ht := mul_le_mul_of_nonneg_right hcoef hQ
  dsimp only [Q] at ht
  nlinarith only [ht]

/-- See the proof of Corollary 1.1 in the paper, its exact exceptional
probability and exponent, for every `K ≥ 1` and `N ≥ 8K`. The sampling law is
literally the product measure restricted to the first-particle strip. -/
theorem hyper_riesz_count_inversion (s : Riesz1.RieszExponent) (β : InverseTemperature) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ s.val ^ 2 / 4 + 4 * η₀ < s.val / 2 ∧
      ∀ η : ℝ, 0 < η → η < η₀ → ∃ C c δ : ℝ,
        0 < C ∧ 0 < c ∧ 0 < δ ∧ ∀ (K : ℕ), 1 ≤ K →
          ∀ (N : ℕ+), 8 * K ≤ (N : ℕ) →
            ((((gibbsMeasure (ofLong β s) N).map configurationReconstructionGaps).prod
              volume).restrict gapSuspensionStrip)
              {z : reconstructibleGapSequences × ℝ |
                C * (K : ℝ) ^ (s.val ^ 2 / 4 + 4 * η) <
                  |gapSequenceSpan z.1.val 1 K - K +
                    (intervalCount 0 K (gapSuspensionConfiguration z) - K)|} ≤
              ENNReal.ofReal (C * Real.exp (-c * (K : ℝ) ^ δ)) := by
  obtain ⟨ηg, hηg, hηga, hηgsmall, hgood⟩ := periodicGapLaw_count_inversion_good_bound s β
  let η₀ := min (ηg / 2) ((s.val / 2 - s.val ^ 2 / 4) / 8)
  have hs : 0 < s.val := s.property.1
  have hs1 : s.val < 1 := s.property.2
  have hdiff : 0 < s.val / 2 - s.val ^ 2 / 4 := by nlinarith
  have hη₀ : 0 < η₀ := lt_min (half_pos hηg) (by positivity)
  have hη₀g : η₀ ≤ ηg / 2 := min_le_left _ _
  have hη₀s : η₀ ≤ (s.val / 2 - s.val ^ 2 / 4) / 8 := min_le_right _ _
  refine ⟨η₀, hη₀, by linarith, fun η hη hηsmall => ?_⟩
  have hηg' : η < ηg := by linarith only [hηsmall, hη₀g, hηg]
  have hηquarter : η < 1 / 4 := hηg'.trans hηgsmall
  obtain ⟨A, c, hA, hc, hgood⟩ := hgood η hη hηg'
  let δ := η ^ 2 / (4 * (s.val + 2))
  have hδ : 0 < δ := div_pos (sq_pos_of_pos hη) (by linarith only [hs])
  obtain ⟨B, hB, habsorb⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := 2) (δ := δ) hδ (show c / 2 < c by linarith only [hc])
  obtain ⟨D, hD, hmom⟩ := periodicGapLaw_moment_bound (ofLong β s) 2 (by norm_num)
  let E := 6 + (10 : ℝ) ^ (s.val / 2 + η)
  let T := Real.sqrt D * Real.sqrt (A * B)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  obtain ⟨K₀, hK₀⟩ := eventually_atTop.mp (hgood.and
    (count_inversion_integer_scales (s.val / 2 + 2 * η) η hη
      (by linarith only [hs, hη]) (by linarith only [hηg', hηga])))
  obtain ⟨F, hF, hfinite⟩ := ComparisonRates.bounded_sizes_remainder K₀ 1 0 (c / 4) δ
  let C := E + T + F + 1
  have hE : 0 < E := by dsimp [E]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hEC : E ≤ C := by dsimp [C]; linarith only [hT, hF]
  have hTC : T ≤ C := by dsimp [C]; linarith only [hE, hF]
  have hFC : F ≤ C := by dsimp [C]; linarith only [hE, hT]
  refine ⟨C, c / 4, δ, hC, by positivity, hδ, fun K hK N hKN => ?_⟩
  let p := ofLong β s
  let q := (gibbsMeasure p N).map configurationReconstructionGaps
  let P := (q.prod volume).restrict gapSuspensionStrip
  have countInversionPart2GibbsProbability : IsProbabilityMeasure (gibbsMeasure p N) :=
    gibbsMeasure_probability p N
  have countInversionPart2BaseProbability : IsProbabilityMeasure q := by
    dsimp only [q]
    infer_instance
  have countInversionPart2StripProbability : IsProbabilityMeasure P :=
    finite_suspensionStrip_probability p N
  by_cases hlarge : K₀ ≤ K
  · obtain ⟨hg, hsc⟩ := hK₀ K hlarge
    let J := ⌈4 * (K : ℝ) ^ (s.val / 2 + 2 * η)⌉₊
    let h₀ := ⌈(K : ℝ) ^ η⌉₊
    let B₀ := 2 * h₀ + (((K + J) - (K - J) : ℕ) : ℝ) ^ (s.val / 2 + η)
    let G := countInversionGoodGaps K B₀ ((K : ℝ) ^ η) (K - J) (K + J)
    let Bad : Set reconstructibleGapSequences := {y | y.val ∉ G}
    have hBad : MeasurableSet Bad :=
      (measurableSet_countInversionGoodGaps _ _ _ _ _).compl.preimage measurable_subtype_coe
    have hqval : q.map Subtype.val = (periodicGapLaw p N).toMeasure := by
      dsimp only [q]
      rw [Measure.map_map measurable_subtype_coe (measurable_configurationReconstructionGaps N)]
      rfl
    have hqbad : q Bad ≤ ENNReal.ofReal (A * B * Real.exp (-(c / 2) * (K : ℝ) ^ δ)) := by
      have he : q Bad = (periodicGapLaw p N).toMeasure Gᶜ := by
        rw [← hqval, Measure.map_apply measurable_subtype_coe
          (measurableSet_countInversionGoodGaps _ _ _ _ _).compl]
        rfl
      rw [he]
      apply (hg N hKN).trans (ENNReal.ofReal_le_ofReal ?_)
      have ht := mul_le_mul_of_nonneg_left
        (habsorb (K : ℝ) (by exact_mod_cast hK)) hA.le
      simpa only [mul_assoc] using ht
    have hqreal : q.real Bad ≤ A * B * Real.exp (-(c / 2) * (K : ℝ) ^ δ) :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hqbad
    have hsecond : (∫⁻ y, ENNReal.ofReal ((y.val 0 : ℝ) ^ (2 : ℝ)) ∂q) ≤
        ENNReal.ofReal D := by
      have hm : Measurable (fun y : ℤ → Ioi (0 : ℝ) =>
          ENNReal.ofReal ((y 0 : ℝ) ^ (2 : ℝ))) := by fun_prop
      rw [← lintegral_map hm measurable_subtype_coe, hqval]
      exact (le_add_right le_rfl).trans (hmom N (by omega) 0)
    have hbias := length_biased_event_le_sqrt_internal q D hD.le hsecond Bad hBad
    have hsc' : 1 ≤ K ∧ 1 ≤ h₀ ∧ h₀ ≤ K - J ∧ J ≤ K ∧ K + J ≤ 2 * K ∧
        h₀ ≤ (K + J) - (K - J) ∧
        (J : ℝ) ≤ 5 * (K : ℝ) ^ (s.val / 2 + 2 * η) ∧
        (h₀ : ℝ) ≤ 2 * (K : ℝ) ^ η := hsc
    have herr : 2 * (K : ℝ) ^ η + B₀ ≤ C * (K : ℝ) ^ (s.val ^ 2 / 4 + 4 * η) :=
      (count_inversion_error_power s.val η hs hs1 hη hηquarter K J h₀ hK
        hsc'.2.2.2.2.2.2.1 hsc'.2.2.2.2.2.2.2).trans
        (mul_le_mul_of_nonneg_right hEC (by positivity))
    have hsub : {z : reconstructibleGapSequences × ℝ |
        C * (K : ℝ) ^ (s.val ^ 2 / 4 + 4 * η) <
          |gapSequenceSpan z.1.val 1 K - K +
            (intervalCount 0 K (gapSuspensionConfiguration z) - K)|} ⊆
        {z | 2 * (K : ℝ) ^ η + B₀ <
          |gapSequenceSpan z.1.val 1 K - K +
            (intervalCount 0 K (gapSuspensionConfiguration z) - K)|} :=
      fun _ hz => herr.trans_lt hz
    apply (measure_mono hsub).trans
    apply (count_inversion_failure_measure_le_internal q K B₀ ((K : ℝ) ^ η)
      (by positivity) K (K - J) (K + J) (Nat.sub_le _ _) (by omega)).trans
    apply hbias.trans (ENNReal.ofReal_le_ofReal ?_)
    have hsqrt : Real.sqrt (Real.exp (-(c / 2) * (K : ℝ) ^ δ)) =
        Real.exp (-(c / 4) * (K : ℝ) ^ δ) := by
      rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
      congr 1
      ring
    calc
      _ ≤ Real.sqrt D * Real.sqrt (A * B * Real.exp (-(c / 2) * (K : ℝ) ^ δ)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hqreal) (Real.sqrt_nonneg D)
      _ = T * Real.exp (-(c / 4) * (K : ℝ) ^ δ) := by
        rw [Real.sqrt_mul (mul_nonneg hA.le hB), hsqrt]
        exact (mul_assoc _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hTC (Real.exp_pos _).le
  · have hunit : P {z : reconstructibleGapSequences × ℝ |
        C * (K : ℝ) ^ (s.val ^ 2 / 4 + 4 * η) <
          |gapSequenceSpan z.1.val 1 K - K +
            (intervalCount 0 K (gapSuspensionConfiguration z) - K)|} ≤ 1 :=
      prob_le_one
    apply hunit.trans
    have ht := hfinite K hK (by omega)
    simp only [Real.rpow_zero, mul_one] at ht
    exact (show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp).le.trans
      (ENNReal.ofReal_le_ofReal (ht.trans
        (mul_le_mul_of_nonneg_right hFC (Real.exp_pos _).le)))

/-- See the proof of Corollary 1.1 in the paper: the finite spatial count
CLT on the exact first-particle sampling strip. Inside the strict quarter-period
window the periodic count agrees pointwise with the finite arc statistic. -/
theorem suspension_spatial_countCLT (s : Riesz1.RieszExponent) (β : InverseTemperature)
    (N : ℕ → ℕ+) (R : ℕ → ℝ) (hR : ∀ j, 0 < R j)
    (hTop : Tendsto R atTop atTop)
    (hRN : Tendsto (fun j => R j / (N j : ℝ)) atTop (𝓝 0)) :
    ConvergesInLawAlong atTop
      (fun j => (((((gibbsMeasure (ofLong β s) (N j)).map
        configurationReconstructionGaps).prod volume).restrict gapSuspensionStrip).map
        (fun z => (R j) ^ (-s.val / 2) *
          (intervalCount 0 (R j) (gapSuspensionConfiguration z) - R j))))
      (Riesz1.normalLaw (Real.toNNReal (Riesz1.countVariance (longParameters β s)))) := by
  let p := ofLong β s
  let P : ℕ → Measure (reconstructibleGapSequences × ℝ) := fun j =>
    ((((gibbsMeasure p (N j)).map configurationReconstructionGaps).prod volume).restrict
      gapSuspensionStrip)
  have suspensionCountCLTProbability (j : ℕ) : IsProbabilityMeasure (P j) :=
    finite_suspensionStrip_probability p (N j)
  have hm (j : ℕ) : Measurable (fun z : reconstructibleGapSequences × ℝ =>
      (R j) ^ (-s.val / 2) * (intervalCount 0 (R j) (gapSuspensionConfiguration z) - R j)) :=
    (((measurable_intervalCount 0 (R j)).comp measurable_gapSuspensionConfiguration).sub_const _).const_mul _
  have hfinite := (finiteIntervalCount_pairs_limit β s N R hR hTop hRN).2.1
  have he : ∀ᶠ j : ℕ in atTop,
      (P j).map (fun z => (R j) ^ (-s.val / 2) *
        (intervalCount 0 (R j) (gapSuspensionConfiguration z) - R j)) =
      (gibbsMeasure p (N j)).map (fun X => (R j) ^ (-s.val / 2) *
        (finiteIntervalCount (N j) (R j) X - R j)) := by
    filter_upwards [hRN.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 4)] with j hj
    have hsub : Ioc (0 : ℝ) (R j) ⊆ Icc (-(R j)) (R j) :=
      fun x hx => ⟨by linarith [hx.1, hR j], hx.2⟩
    have hpoint (X : Riesz1.Configuration (N j)) :
        intervalCount 0 (R j) (periodicSpatialConfiguration X) = finiteIntervalCount (N j) (R j) X := by
      rw [← intervalCount_restrictConfiguration 0 (R j) (R j) hsub,
        periodicSpatialConfiguration_restrict_eq_microscopic X (R j)
          (by have := (div_lt_iff₀ (show (0 : ℝ) < N j by positivity)).mp hj; linarith),
        intervalCount_restrictConfiguration 0 (R j) (R j) hsub,
        finiteIntervalCount_eq_intervalCount (N j) (R j) (hR j) hj]
    calc
      _ = ((P j).map gapSuspensionConfiguration).map
          (fun C => (R j) ^ (-s.val / 2) * (intervalCount 0 (R j) C - R j)) := by
        rw [Measure.map_map (((measurable_intervalCount 0 (R j)).sub_const _).const_mul _)
          measurable_gapSuspensionConfiguration]
        rfl
      _ = (periodicSpatialLaw p (N j)).map
          (fun C => (R j) ^ (-s.val / 2) * (intervalCount 0 (R j) C - R j)) := by
        rw [show (P j).map gapSuspensionConfiguration = periodicSpatialLaw p (N j) from
          finite_suspensionStrip_spatial_law p (N j)]
      _ = _ := by
        rw [periodicSpatialLaw, Measure.map_map
          (((measurable_intervalCount 0 (R j)).sub_const _).const_mul _)
          (measurable_periodicSpatialConfiguration (N j))]
        congr 1
        funext X
        simp only [Function.comp_def, hpoint]
  refine ⟨fun j => by change IsProbabilityMeasure ((P j).map _); infer_instance,
    hfinite.2.1, fun f => ?_⟩
  apply (hfinite.2.2 f).congr'
  filter_upwards [he] with j hj
  rw [show (gibbsMeasure p (N j)).map _ = (P j).map _ from hj.symm]

/-- See the proof of Corollary 1.1 in the paper, the selected-span
Gaussian limit along every mesoscopic pair. This is obtained directly from
spatial counts and the quantitative inversion error. Gaussian symmetry handles
its sign. -/
theorem hyper_riesz_selected_spanCLT (s : Riesz1.RieszExponent) (β : InverseTemperature)
    (N K : ℕ → ℕ+) (hK : Tendsto (fun j => (K j : ℕ)) atTop atTop)
    (hKN : Tendsto (fun j => (K j : ℝ) / (N j : ℝ)) atTop (𝓝 0)) :
    ConvergesInLawAlong atTop
      (fun j => (((((gibbsMeasure (ofLong β s) (N j)).map
        configurationReconstructionGaps).prod volume).restrict gapSuspensionStrip).map
        (fun z => (K j : ℝ) ^ (-s.val / 2) * (gapSequenceSpan z.1.val 1 (K j) - K j))))
      (Riesz1.normalLaw (Real.toNNReal (Riesz1.countVariance (longParameters β s)))) := by
  let p := ofLong β s
  let P : ℕ → Measure (reconstructibleGapSequences × ℝ) := fun j =>
    ((((gibbsMeasure p (N j)).map configurationReconstructionGaps).prod volume).restrict
      gapSuspensionStrip)
  have selectedSpanCLTProbability (j : ℕ) : IsProbabilityMeasure (P j) :=
    finite_suspensionStrip_probability p (N j)
  let X : ℕ → reconstructibleGapSequences × ℝ → ℝ := fun j z =>
    -(K j : ℝ) ^ (-s.val / 2) * (intervalCount 0 (K j) (gapSuspensionConfiguration z) - K j)
  let Y : ℕ → reconstructibleGapSequences × ℝ → ℝ := fun j z =>
    (K j : ℝ) ^ (-s.val / 2) * (gapSequenceSpan z.1.val 1 (K j) - K j)
  have hX (j : ℕ) : Measurable (X j) :=
    (((measurable_intervalCount 0 (K j)).comp measurable_gapSuspensionConfiguration).sub_const _).const_mul _
  have hY (j : ℕ) : Measurable (Y j) :=
    ((((continuous_gapSequenceSpan 1 (K j)).measurable.comp
      (measurable_subtype_coe.comp measurable_fst)).sub_const _).const_mul _)
  let ν := Riesz1.normalLaw (Real.toNNReal (Riesz1.countVariance (longParameters β s)))
  have hcounts := suspension_spatial_countCLT s β N (fun j => (K j : ℝ))
    (fun j => by positivity) (tendsto_natCast_atTop_atTop.comp hK) hKN
  have hnegative : ConvergesInLawAlong atTop (fun j => (P j).map (X j)) ν := by
    have ht := convergesInLawAlong_map_mul hcounts
      (c := fun _ => (-1 : ℝ)) (a := -1) tendsto_const_nhds
    have hn : ν.map (fun x => (-1 : ℝ) * x) = ν := by
      simp only [ν, Riesz1.normalLaw, neg_one_mul, ProbabilityTheory.gaussianReal_map_neg, neg_zero]
    rw [show (Riesz1.normalLaw (Real.toNNReal (Riesz1.countVariance (longParameters β s)))).map
        (fun x => (-1 : ℝ) * x) = ν from hn] at ht
    have he (j : ℕ) : ((P j).map (fun z => (K j : ℝ) ^ (-s.val / 2) *
        (intervalCount 0 (K j) (gapSuspensionConfiguration z) - K j))).map
        (fun x => (-1 : ℝ) * x) = (P j).map (X j) := by
      have hm : Measurable (fun z : reconstructibleGapSequences × ℝ =>
          (K j : ℝ) ^ (-s.val / 2) *
            (intervalCount 0 (K j) (gapSuspensionConfiguration z) - K j)) := by
        simpa only [Function.comp_def] using
          ((((measurable_intervalCount 0 (K j)).comp measurable_gapSuspensionConfiguration).sub_const
            (K j : ℝ)).const_mul ((K j : ℝ) ^ (-s.val / 2)))
      rw [Measure.map_map (by fun_prop) hm]
      congr 1
      funext z
      dsimp [X]
      ring
    change ConvergesInLawAlong atTop (fun j => ((P j).map (fun z =>
      (K j : ℝ) ^ (-s.val / 2) *
        (intervalCount 0 (K j) (gapSuspensionConfiguration z) - K j))).map
        (fun x => (-1 : ℝ) * x)) ν at ht
    simpa only [he] using ht
  obtain ⟨η₀, hη₀, hsmall, hbound⟩ := hyper_riesz_count_inversion s β
  let η := η₀ / 2
  obtain ⟨C, c, δ, hC, hc, hδ, hbound⟩ := hbound η (half_pos hη₀) (half_lt_self hη₀)
  let e := s.val ^ 2 / 4 + 4 * η
  have he : e - s.val / 2 < 0 := by dsimp [e, η]; linarith only [hsmall, hη₀]
  let r : ℕ → ℝ := fun j => C * (K j : ℝ) ^ (e - s.val / 2)
  let b : ℕ → ℝ := fun j => C * Real.exp (-c * (K j : ℝ) ^ δ)
  have hr : Tendsto r atTop (𝓝 0) := by
    simpa [r, Function.comp_def] using ((tendsto_rpow_neg_atTop (neg_pos.mpr he)).comp
      (tendsto_natCast_atTop_atTop.comp hK)).const_mul C
  have hb : Tendsto b atTop (𝓝 0) := by
    simpa [b, Function.comp_def] using
      ((StretchedCutoff.tendsto_power_mul_exp hδ hc 0).comp
        (tendsto_natCast_atTop_atTop.comp hK)).const_mul C
  apply convergesInLawAlong_of_error_bound P X Y hX hY ν hnegative r b hr hb
  filter_upwards [hKN.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 8)] with j hj
  have hKN' : 8 * (K j : ℕ) ≤ (N j : ℕ) := by
    have hn : 0 < (N j : ℝ) := by positivity
    have ht := (div_lt_iff₀ hn).mp hj
    exact_mod_cast (show (8 : ℝ) * K j ≤ N j by linarith only [ht])
  refine ⟨by dsimp [r]; positivity, by dsimp [b]; positivity, ?_⟩
  have hscale : 0 < (K j : ℝ) ^ (-s.val / 2) := Real.rpow_pos_of_pos (by positivity) _
  have hevent : {z | r j < |Y j z - X j z|} =
      {z : reconstructibleGapSequences × ℝ | C * (K j : ℝ) ^ e <
        |gapSequenceSpan z.1.val 1 (K j) - K j +
          (intervalCount 0 (K j) (gapSuspensionConfiguration z) - K j)|} := by
    ext z
    have hp : C * (K j : ℝ) ^ (e - s.val / 2) =
        (K j : ℝ) ^ (-s.val / 2) * (C * (K j : ℝ) ^ e) := by
      rw [← mul_assoc, mul_comm ((K j : ℝ) ^ (-s.val / 2)) C, mul_assoc,
        ← Real.rpow_add (by positivity : 0 < (K j : ℝ))]
      congr 2
      ring
    have hd : Y j z - X j z = (K j : ℝ) ^ (-s.val / 2) *
        (gapSequenceSpan z.1.val 1 (K j) - K j +
          (intervalCount 0 (K j) (gapSuspensionConfiguration z) - K j)) := by dsimp [X, Y]; ring
    simp only [mem_ofPred_eq, r, hp, hd, abs_mul, abs_of_pos hscale,
      mul_lt_mul_iff_right₀ hscale]
  rw [hevent]
  exact hbound (K j) (K j).pos (N j) hKN'

/-- See Subsection 6.4 of the paper: the marginal gap law of first-particle sampling
is exactly `Y₀ dq_N`, on the existing positive two-sided gap carrier. -/
theorem finite_suspensionStrip_gap_law (p : Parameters) (N : ℕ+) :
    (((((gibbsMeasure p N).map configurationReconstructionGaps).prod volume).restrict
      gapSuspensionStrip).map (fun z => z.1.val)) =
      (periodicGapLaw p N).toMeasure.withDensity
        (fun y => ENNReal.ofReal (y 0 : ℝ)) := by
  let q := (gibbsMeasure p N).map configurationReconstructionGaps
  have countInversionGapLawGibbsProbability : IsProbabilityMeasure (gibbsMeasure p N) :=
    gibbsMeasure_probability p N
  have countInversionGapLawBaseProbability : IsProbabilityMeasure q := by
    dsimp [q]
    infer_instance
  have hval : q.map Subtype.val = (periodicGapLaw p N).toMeasure := by
    dsimp only [q]
    rw [Measure.map_map measurable_subtype_coe (measurable_configurationReconstructionGaps N)]
    rfl
  calc
    _ = (((q.prod volume).restrict gapSuspensionStrip).map Prod.fst).map Subtype.val := by
      rw [Measure.map_map measurable_subtype_coe measurable_fst]
      rfl
    _ = (q.withDensity (fun y => ENNReal.ofReal (y.val 0 : ℝ))).map Subtype.val := by
      rw [suspensionStrip_map_fst]
    _ = (q.map Subtype.val).withDensity (fun y => ENNReal.ofReal (y 0 : ℝ)) :=
      Riesz1.map_withDensity_comp (F := (Subtype.val : reconstructibleGapSequences →
        ℤ → Ioi (0 : ℝ))) (g := fun y : ℤ → Ioi (0 : ℝ) => ENNReal.ofReal (y 0 : ℝ))
        q measurable_subtype_coe
        ((measurable_subtype_coe.comp (measurable_pi_apply 0)).ennreal_ofReal)
    _ = _ := by rw [hval]

/-- See the proof of Corollary 1.1 in the paper, its Gaussian conclusion
under the literal length-biased law `d q̂_N = Y₀ d q_N`. The strip theorem and
the gap-law theorem therefore describe the same selected span. -/
theorem hyper_riesz_length_biased_spanCLT (s : Riesz1.RieszExponent) (β : InverseTemperature)
    (N K : ℕ → ℕ+) (hK : Tendsto (fun j => (K j : ℕ)) atTop atTop)
    (hKN : Tendsto (fun j => (K j : ℝ) / (N j : ℝ)) atTop (𝓝 0)) :
    ConvergesInLawAlong atTop
      (fun j => ((periodicGapLaw (ofLong β s) (N j)).toMeasure.withDensity
        (fun y => ENNReal.ofReal (y 0 : ℝ))).map
          (fun y => (K j : ℝ) ^ (-s.val / 2) * (gapSequenceSpan y 1 (K j) - K j)))
      (Riesz1.normalLaw (Real.toNNReal (Riesz1.countVariance (longParameters β s)))) := by
  have he (j : ℕ) :
      (((((gibbsMeasure (ofLong β s) (N j)).map configurationReconstructionGaps).prod
        volume).restrict gapSuspensionStrip).map
          (fun z => (K j : ℝ) ^ (-s.val / 2) * (gapSequenceSpan z.1.val 1 (K j) - K j))) =
      ((periodicGapLaw (ofLong β s) (N j)).toMeasure.withDensity
        (fun y => ENNReal.ofReal (y 0 : ℝ))).map
          (fun y => (K j : ℝ) ^ (-s.val / 2) * (gapSequenceSpan y 1 (K j) - K j)) := by
    have hm : Measurable (fun y : ℤ → Ioi (0 : ℝ) =>
        (K j : ℝ) ^ (-s.val / 2) * (gapSequenceSpan y 1 (K j) - K j)) :=
      ((continuous_gapSequenceSpan 1 (K j)).measurable.sub_const (K j : ℝ)).const_mul _
    have hp : Measurable (fun z : reconstructibleGapSequences × ℝ => z.1.val) :=
      measurable_subtype_coe.comp measurable_fst
    rw [← finite_suspensionStrip_gap_law, Measure.map_map hm hp]
    rfl
  simpa only [he] using hyper_riesz_selected_spanCLT s β N K hK hKN

end Riesz2
