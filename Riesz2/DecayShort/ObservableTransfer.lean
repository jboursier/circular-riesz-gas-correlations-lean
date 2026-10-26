/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.LocalLaw
public import Riesz2.Frozen.GapObservable
public import Riesz2.Frozen.GapSecondMoments
public import Riesz2.Preliminaries.GapDensities
public import Riesz2.Frozen.PhysicalGapPenalty
public import Riesz2.Frozen.TiltNormalizer
public import Riesz2.Frozen.TiltedParticleMeasure
public import Riesz2.Frozen.DerivativeSup
public import Riesz2.Frozen.GapLaw
public import Riesz2.Frozen.GapVector
public import Riesz2.ToMathlib.LipschitzDerivativeBound
public import Riesz2.ToMathlib.CutoffQuadraticBound
public import Riesz2.ToMathlib.NonnegativeGibbsTilt
public import Riesz2.ToMathlib.TiltedCovariancePerturbation
public import Riesz2.ToMathlib.ObservableCenteredMoments
public import Riesz2.ToMathlib.MomentEventBounds
public import Riesz2.ToMathlib.StretchedCutoffRates
public import Riesz2.ToMathlib.ExponentialPowerMoments
public import Mathlib.Tactic

/-!
# Short-range observable transfer

This file proves removal of the active forcing in the proof of Theorem 2 with the
derivative norms. The active forcing is `∑_{i ∈ I} (f_R(x_i) + ι f̂_R(x_i))` with
`f_R(t) = θ(t / R)`, `f̂_R(t) = θ(1 / (R t))` and `R = n^h`, where `n = |I|`. Its tilt is the
Gibbs law tilted by `e^{-β F}`, as in `expTilt`.

The argument has four inputs. The penalty is nonnegative, and its support lies in the union of
the events `{gap_i ≥ R/2}` and `{gap_i ≤ 2/R}`. The normalizer is bounded below by Jensen's
inequality for small `n` and by `1 - μ{F ≠ 0}` for large `n`. The one-gap moments are uniform in
the configuration size. The Lipschitz bound of an observable comes from its almost everywhere
derivative.
-/

public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace Riesz2.DecayShort

/-- The active gap penalty of Subsection 4.4 on a finite set `I` of gap labels. With
`R > 0` it is `∑_{i ∈ I} (θ(gap_i / R) + ι θ(1 / (R gap_i)))`, where the second summand is
present exactly when `ι` is true. -/
@[expose] noncomputable def activeGapPenalty {N : ℕ+} (θ : PhysicalCutoff) (R : ℝ) (ι : Bool)
    (I : Finset (Fin (N : ℕ))) (X : Riesz1.Configuration N) : ℝ :=
  ∑ i ∈ I, (θ.val (gap X i.val / R) + if ι then θ.val (1 / (R * gap X i.val)) else 0)

/-- The active tilt of Subsection 4.4 on the configurations of `N` particles: the Gibbs
law tilted by `e^{-β F}` with `β = p.val.1`. -/
@[expose] noncomputable def activeTilt (p : Parameters) (N : ℕ+) (θ : PhysicalCutoff) (R : ℝ) (ι : Bool)
    (I : Finset (Fin (N : ℕ))) : Measure (Riesz1.Configuration N) :=
  NonnegativeTilt.expTilt (gibbsMeasure p N) p.val.1 (activeGapPenalty θ R ι I)

/-! ### Cutoff facts -/

theorem cutoff_nonneg (θ : PhysicalCutoff) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ θ.val t :=
  θ.property.2.2.1 t ht

theorem cutoff_eq_zero_of_le_half (θ : PhysicalCutoff) {t : ℝ} (ht : 0 ≤ t) (h : t ≤ 1 / 2) :
    θ.val t = 0 :=
  θ.property.2.2.2.1 t ⟨ht, h⟩

theorem half_lt_of_cutoff_ne_zero (θ : PhysicalCutoff) {t : ℝ} (ht : 0 ≤ t)
    (h : θ.val t ≠ 0) : 1 / 2 < t :=
  lt_of_not_ge fun hle => h (cutoff_eq_zero_of_le_half θ ht hle)

theorem measurable_cutoff_comp (θ : PhysicalCutoff) {Ω : Type*} [MeasurableSpace Ω]
    {g : Ω → ℝ} (hg : Measurable g) (hg0 : ∀ ω, 0 ≤ g ω) :
    Measurable (fun ω => θ.val (g ω)) := by
  have hθ : Continuous (fun t : Ici (0 : ℝ) => θ.val t.val) :=
    continuousOn_iff_continuous_domRestrict.mp θ.property.1.continuousOn
  have hf : Measurable (fun ω => (⟨g ω, hg0 ω⟩ : Ici (0 : ℝ))) := hg.subtype_mk
  exact hθ.measurable.comp hf

/-! ### The active penalty -/

theorem activeGapPenalty_nonneg {N : ℕ+} (θ : PhysicalCutoff) {R : ℝ} (hR : 0 ≤ R) (ι : Bool)
    (I : Finset (Fin (N : ℕ))) (X : Riesz1.Configuration N) :
    0 ≤ activeGapPenalty θ R ι I X := by
  unfold activeGapPenalty
  apply Finset.sum_nonneg
  intro i _
  apply add_nonneg
  · exact cutoff_nonneg θ (div_nonneg (Riesz1.gap_pos X i.val).le hR)
  · cases ι
    · simp
    · simp only [ite_true]
      exact cutoff_nonneg θ (div_nonneg zero_le_one (mul_nonneg hR (Riesz1.gap_pos X i.val).le))

theorem activeGapPenalty_measurable {N : ℕ+} (θ : PhysicalCutoff) {R : ℝ} (hR : 0 ≤ R)
    (ι : Bool) (I : Finset (Fin (N : ℕ))) :
    Measurable (activeGapPenalty (N := N) θ R ι I) := by
  unfold activeGapPenalty
  apply Finset.measurable_sum
  intro i _
  apply Measurable.add
  · exact measurable_cutoff_comp θ ((Riesz1.measurable_gap i.val).div_const R)
      (fun X => div_nonneg (Riesz1.gap_pos X i.val).le hR)
  · cases ι
    · simp
    · simp only [ite_true]
      exact measurable_cutoff_comp θ (measurable_const.div
        ((Riesz1.measurable_gap i.val).const_mul R))
        (fun X => div_nonneg zero_le_one (mul_nonneg hR (Riesz1.gap_pos X i.val).le))

/-- For positive `R` and `g` with `R g < 2`, the power `(R/2)^s` is at most `g^(-s)`. -/
theorem half_rpow_le_rpow_neg {s R g : ℝ} (hs : 0 ≤ s) (hR : 0 < R) (hg : 0 < g)
    (hRg : R * g < 2) : (R / 2) ^ s ≤ g ^ (-s) := by
  rw [Real.rpow_neg hg.le, ← one_div, le_div_iff₀ (Real.rpow_pos_of_pos hg s),
    ← Real.mul_rpow (by positivity) hg.le]
  apply Real.rpow_le_one (by positivity) _ hs
  nlinarith

/-- The penalty is nonzero only when some selected gap is above `R / 2`, or, for `ι = true`,
some selected gap is at most `2 / R` in the sense of the inverse power `g^(-s)`. -/
theorem activeGapPenalty_ne_zero_subset {N : ℕ+} (θ : PhysicalCutoff) (s : ℝ) {R : ℝ}
    (hs : 0 ≤ s) (hR : 0 < R) (ι : Bool) (I : Finset (Fin (N : ℕ))) :
    {X : Riesz1.Configuration N | activeGapPenalty θ R ι I X ≠ 0} ⊆
      ⋃ i ∈ I, ({X | R / 2 ≤ gap X i.val} ∪
        {X | (R / 2) ^ s ≤ gap X i.val ^ (-s)}) := by
  intro X hX
  have hsome : ∃ i ∈ I, θ.val (gap X i.val / R) +
      (if ι then θ.val (1 / (R * gap X i.val)) else 0) ≠ 0 := by
    by_contra h
    simp only [not_exists, not_and, ne_eq, not_not] at h
    exact hX (Finset.sum_eq_zero fun i hi => h i hi)
  obtain ⟨i, hi, hne⟩ := hsome
  have hg : 0 < gap X i.val := Riesz1.gap_pos X i.val
  simp only [mem_iUnion, mem_union, Set.mem_ofPred_eq]
  refine ⟨i, hi, ?_⟩
  by_cases h1 : θ.val (gap X i.val / R) ≠ 0
  · left
    have hc := half_lt_of_cutoff_ne_zero θ (div_nonneg hg.le hR.le) h1
    rw [lt_div_iff₀ hR] at hc
    linarith
  · right
    have h1' : θ.val (gap X i.val / R) = 0 := not_not.mp h1
    have hite : (if ι then θ.val (1 / (R * gap X i.val)) else 0) ≠ 0 := by
      intro h0
      apply hne
      rw [h1', h0, add_zero]
    cases ι
    · simp at hite
    · simp only [ite_true] at hite
      have hpos : 0 < R * gap X i.val := mul_pos hR hg
      have hc := half_lt_of_cutoff_ne_zero θ (div_nonneg zero_le_one hpos.le) hite
      have hRg : R * gap X i.val < 2 := by
        have := (lt_div_iff₀ hpos).mp hc
        linarith
      exact half_rpow_le_rpow_neg hs hR hg hRg

/-- The active tilt is a probability measure, for every nonnegative parameter `R`. -/
theorem activeTilt_isProbabilityMeasure {N : ℕ+} (p : Parameters) (θ : PhysicalCutoff)
    {R : ℝ} (hR : 0 ≤ R) (ι : Bool) (I : Finset (Fin (N : ℕ))) :
    IsProbabilityMeasure (activeTilt p N θ R ι I) := by
  have := gibbsMeasure_probability p N
  exact NonnegativeTilt.expTilt_isProbabilityMeasure (activeGapPenalty_measurable θ hR ι I)
    p.property.1.le (activeGapPenalty_nonneg θ hR ι I)

/-! ### Tail bounds for one gap -/

/-- The upper tail of one gap from its exponential moment. -/
theorem gap_upper_tail (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (j : ℤ) (u : ℝ) :
    gibbsMeasure p N {X | u ≤ gap X j} ≤
      ENNReal.ofReal (3 * Real.exp (-(Real.log 2 / 4) * u)) := by
  have := gibbsMeasure_probability p N
  have he := SingleGapTails.exponential_moment p N hN j
  exact ExponentialPower.closed_tail
    (div_pos (Real.log_pos one_lt_two) (by norm_num)) he.1 he.2 u

/-- The lower tail of one gap in the inverse power `gap^(-s)`, with a rate `β` that is fixed
by the inverse temperature. -/
theorem gap_inverse_tail {s β : ℝ} (hs : 0 < s) (hβ : 0 < β) :
    ∃ A : ℝ, 0 < A ∧ ∀ (p : Parameters), p.val.2 = s → p.val.1 = β →
      ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (j : ℤ) (u : ℝ),
        gibbsMeasure p N {X | u ≤ gap X j ^ (-s)} ≤
          ENNReal.ofReal (A * Real.exp (-β * u)) := by
  obtain ⟨A, hA, hmom⟩ := SingleGapTails.inverse_exponential_moment s β β hs hβ le_rfl
  refine ⟨A, hA, fun p hps hpb N hN j u => ?_⟩
  have := gibbsMeasure_probability p N
  obtain ⟨hi, hint⟩ := hmom p hps hpb.ge hpb.le N hN j
  exact ExponentialPower.closed_tail hβ hi hint u

/-- A probability bound converts to a bound on the real measure. -/
theorem measureReal_le_of_le_ofReal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {A : Set Ω} {b : ℝ} (hb : 0 ≤ b) (h : μ A ≤ ENNReal.ofReal b) :
    μ.real A ≤ b :=
  ENNReal.toReal_le_of_le_ofReal hb h

/-- The mass of `{F ≠ 0}` for the active penalty, through the one-gap tails. The inverse-gap
event is included whether or not `ι` is true. -/
theorem activeGapPenalty_measureReal_le {N : ℕ+} (p : Parameters) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) {s β A R : ℝ} (hs : 0 ≤ s) (hR : 0 < R) (hA0 : 0 ≤ A)
    (hA : ∀ (j : ℤ) (u : ℝ), gibbsMeasure p N {X | u ≤ gap X j ^ (-s)} ≤
      ENNReal.ofReal (A * Real.exp (-β * u))) (ι : Bool) (I : Finset (Fin (N : ℕ))) :
    (gibbsMeasure p N).real {X | activeGapPenalty θ R ι I X ≠ 0} ≤
      I.card * (3 * Real.exp (-(Real.log 2 / 4) * (R / 2)) +
        A * Real.exp (-β * (R / 2) ^ s)) := by
  have := gibbsMeasure_probability p N
  have hsub := activeGapPenalty_ne_zero_subset θ s hs hR ι I (N := N)
  calc
    (gibbsMeasure p N).real {X | activeGapPenalty θ R ι I X ≠ 0}
        ≤ (gibbsMeasure p N).real (⋃ i ∈ I, ({X | R / 2 ≤ gap X i.val} ∪
            {X | (R / 2) ^ s ≤ gap X i.val ^ (-s)})) :=
          measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ i ∈ I, (gibbsMeasure p N).real ({X | R / 2 ≤ gap X i.val} ∪
            {X | (R / 2) ^ s ≤ gap X i.val ^ (-s)}) := measureReal_biUnion_finset_le I _
    _ ≤ ∑ i ∈ I, (3 * Real.exp (-(Real.log 2 / 4) * (R / 2)) +
            A * Real.exp (-β * (R / 2) ^ s)) := by
        apply Finset.sum_le_sum
        intro i _
        have hu := measureReal_le_of_le_ofReal (μ := gibbsMeasure p N)
          (A := {X | R / 2 ≤ gap X i.val}) (b := 3 * Real.exp (-(Real.log 2 / 4) * (R / 2)))
          (by positivity) (gap_upper_tail p N hN i.val (R / 2))
        have hv := measureReal_le_of_le_ofReal (μ := gibbsMeasure p N)
          (A := {X | (R / 2) ^ s ≤ gap X i.val ^ (-s)})
          (b := A * Real.exp (-β * (R / 2) ^ s)) (by positivity) (hA i.val ((R / 2) ^ s))
        refine (measureReal_union_le _ _).trans ?_
        linarith
    _ = I.card * (3 * Real.exp (-(Real.log 2 / 4) * (R / 2)) +
          A * Real.exp (-β * (R / 2) ^ s)) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-! ### Quadratic bounds on the penalty and the normalizer -/

/-- One active summand is at most `K (gap² + gap^(-2))`, when the cutoff grows at most like
`K t²` and `R ≥ 1`. -/
theorem activeGap_term_le {N : ℕ+} (θ : PhysicalCutoff) {K R : ℝ} (hK : 0 ≤ K)
    (hKθ : ∀ t : ℝ, 0 ≤ t → θ.val t ≤ K * t ^ 2) (hR : 1 ≤ R) (ι : Bool)
    (X : Riesz1.Configuration N) (i : Fin (N : ℕ)) :
    θ.val (gap X i.val / R) + (if ι then θ.val (1 / (R * gap X i.val)) else 0) ≤
      K * (gap X i.val ^ (2 : ℝ) + gap X i.val ^ (-(2 : ℝ))) := by
  have hg : 0 < gap X i.val := Riesz1.gap_pos X i.val
  have hR0 : 0 < R := by linarith
  have hneg : gap X i.val ^ (-(2 : ℝ)) = (gap X i.val ^ 2)⁻¹ := by
    rw [Real.rpow_neg hg.le, Real.rpow_two]
  have h1 : θ.val (gap X i.val / R) ≤ K * gap X i.val ^ (2 : ℝ) := by
    have hnn : 0 ≤ gap X i.val / R := div_nonneg hg.le hR0.le
    calc
      θ.val (gap X i.val / R) ≤ K * (gap X i.val / R) ^ 2 := hKθ _ hnn
      _ ≤ K * gap X i.val ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnn (div_le_self hg.le hR) 2) hK
      _ = K * gap X i.val ^ (2 : ℝ) := by rw [Real.rpow_two]
  have h2 : (if ι then θ.val (1 / (R * gap X i.val)) else 0) ≤
      K * gap X i.val ^ (-(2 : ℝ)) := by
    cases ι
    · simp only [Bool.false_eq_true, ite_false]
      exact mul_nonneg hK (Real.rpow_nonneg hg.le _)
    · simp only [ite_true]
      have hRg : 0 < R * gap X i.val := mul_pos hR0 hg
      have hsq : (1 / (R * gap X i.val)) ^ 2 ≤ (gap X i.val ^ 2)⁻¹ := by
        rw [div_pow, one_pow, one_div]
        apply inv_anti₀ (by positivity : (0 : ℝ) < gap X i.val ^ 2)
        have hR2 : 1 ≤ R ^ 2 := by nlinarith
        calc
          gap X i.val ^ 2 = 1 * gap X i.val ^ 2 := (one_mul _).symm
          _ ≤ R ^ 2 * gap X i.val ^ 2 := mul_le_mul_of_nonneg_right hR2 (sq_nonneg _)
          _ = (R * gap X i.val) ^ 2 := by ring
      calc
        θ.val (1 / (R * gap X i.val)) ≤ K * (1 / (R * gap X i.val)) ^ 2 :=
          hKθ _ (div_nonneg zero_le_one hRg.le)
        _ ≤ K * (gap X i.val ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hsq hK
        _ = K * gap X i.val ^ (-(2 : ℝ)) := by rw [hneg]
  linarith [mul_add K (gap X i.val ^ (2 : ℝ)) (gap X i.val ^ (-(2 : ℝ)))]

/-- The active penalty is integrable and its mean is at most `|I| K D`, when every one-gap
moment `E gap² + E gap^(-2)` is at most `D`. -/
theorem integral_activeGapPenalty_le {N : ℕ+} (p : Parameters) (θ : PhysicalCutoff)
    {K R D : ℝ} (hK : 0 ≤ K) (hKθ : ∀ t : ℝ, 0 ≤ t → θ.val t ≤ K * t ^ 2) (hR : 1 ≤ R)
    (hmom : ∀ j : ℤ, Integrable (fun X : Riesz1.Configuration N => gap X j ^ (2 : ℝ))
        (gibbsMeasure p N) ∧
      Integrable (fun X : Riesz1.Configuration N => gap X j ^ (-(2 : ℝ))) (gibbsMeasure p N) ∧
      (∫ X, gap X j ^ (2 : ℝ) ∂gibbsMeasure p N) +
        (∫ X, gap X j ^ (-(2 : ℝ)) ∂gibbsMeasure p N) ≤ D) (ι : Bool)
    (I : Finset (Fin (N : ℕ))) :
    Integrable (activeGapPenalty θ R ι I) (gibbsMeasure p N) ∧
      ∫ X, activeGapPenalty θ R ι I X ∂gibbsMeasure p N ≤ I.card * (K * D) := by
  have := gibbsMeasure_probability p N
  have hR0 : 0 ≤ R := by linarith
  let H : Riesz1.Configuration N → ℝ := fun X =>
    ∑ i ∈ I, K * (gap X i.val ^ (2 : ℝ) + gap X i.val ^ (-(2 : ℝ)))
  have hterm : ∀ i ∈ I, Integrable (fun X : Riesz1.Configuration N =>
      K * (gap X i.val ^ (2 : ℝ) + gap X i.val ^ (-(2 : ℝ)))) (gibbsMeasure p N) :=
    fun i _ => ((hmom i.val).1.add (hmom i.val).2.1).const_mul K
  have hHint : Integrable H (gibbsMeasure p N) := integrable_finsetSum I hterm
  have hGmeas := activeGapPenalty_measurable θ hR0 ι I
  have hG_le : ∀ X, activeGapPenalty θ R ι I X ≤ H X := fun X =>
    Finset.sum_le_sum fun i _ => activeGap_term_le θ hK hKθ hR ι X i
  have hG_nonneg : ∀ X, 0 ≤ activeGapPenalty θ R ι I X := fun X =>
    activeGapPenalty_nonneg θ hR0 ι I X
  have hG_int : Integrable (activeGapPenalty θ R ι I) (gibbsMeasure p N) :=
    Integrable.mono' hHint hGmeas.aestronglyMeasurable
      (ae_of_all _ fun X => by
        rw [Real.norm_of_nonneg (hG_nonneg X)]
        exact hG_le X)
  refine ⟨hG_int, ?_⟩
  have hHsum : ∫ X, H X ∂gibbsMeasure p N =
      ∑ i ∈ I, ∫ X, K * (gap X i.val ^ (2 : ℝ) + gap X i.val ^ (-(2 : ℝ)))
        ∂gibbsMeasure p N :=
    integral_finsetSum I hterm
  calc
    ∫ X, activeGapPenalty θ R ι I X ∂gibbsMeasure p N ≤ ∫ X, H X ∂gibbsMeasure p N :=
        integral_mono hG_int hHint hG_le
    _ = ∑ i ∈ I, K * ((∫ X, gap X i.val ^ (2 : ℝ) ∂gibbsMeasure p N) +
          ∫ X, gap X i.val ^ (-(2 : ℝ)) ∂gibbsMeasure p N) := by
        rw [hHsum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_const_mul, integral_add (hmom i.val).1 (hmom i.val).2.1]
    _ ≤ ∑ i ∈ I, K * D := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hmom i.val).2.2 hK
    _ = I.card * (K * D) := by rw [Finset.sum_const, nsmul_eq_mul]

/-- The normalizer of the active tilt is at least `exp(-β |I| K D)`. -/
theorem expTiltNormalizer_ge_of_card {N : ℕ+} (p : Parameters) (θ : PhysicalCutoff)
    {K R D : ℝ} (hK : 0 ≤ K) (hKθ : ∀ t : ℝ, 0 ≤ t → θ.val t ≤ K * t ^ 2) (hR : 1 ≤ R)
    (hmom : ∀ j : ℤ, Integrable (fun X : Riesz1.Configuration N => gap X j ^ (2 : ℝ))
        (gibbsMeasure p N) ∧
      Integrable (fun X : Riesz1.Configuration N => gap X j ^ (-(2 : ℝ))) (gibbsMeasure p N) ∧
      (∫ X, gap X j ^ (2 : ℝ) ∂gibbsMeasure p N) +
        (∫ X, gap X j ^ (-(2 : ℝ)) ∂gibbsMeasure p N) ≤ D) (ι : Bool)
    (I : Finset (Fin (N : ℕ))) :
    Real.exp (-p.val.1 * (I.card * (K * D))) ≤
      NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1 (activeGapPenalty θ R ι I) := by
  have := gibbsMeasure_probability p N
  have hR0 : 0 ≤ R := by linarith
  have hb : 0 ≤ p.val.1 := p.property.1.le
  obtain ⟨hint, hmean⟩ := integral_activeGapPenalty_le p θ hK hKθ hR hmom ι I
  have hjen := NonnegativeTilt.exp_neg_mul_integral_le_expTiltNormalizer
    (μ := gibbsMeasure p N) (activeGapPenalty_measurable θ hR0 ι I) hb
    (activeGapPenalty_nonneg θ hR0 ι I) hint
  refine le_trans (Real.exp_le_exp.mpr ?_) hjen
  nlinarith [p.property.1]

/-! ### Uniform moments of one gap and the tilt -/

/-- Uniform bound on the positive and inverse moments `E gap^r + E gap^(-r)`, for every
configuration size at least two and temperature in a positive compact interval.
This is the moment input for Theorem 2 of the paper. -/
theorem gap_moment_bound_locallyUniform {s βlo βhi : ℝ} (hs : 0 < s) (hs1 : s ≠ 1)
    (hβ : 0 < βlo) (hβhi : βlo ≤ βhi) (r : ℝ)
    (hr : 0 < r) :
    ∃ D : ℝ, 0 < D ∧ ∀ (p : Parameters), p.val.2 = s → p.val.1 ∈ Icc βlo βhi →
      ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (j : ℤ),
        Integrable (fun X : Riesz1.Configuration N => gap X j ^ r) (gibbsMeasure p N) ∧
        Integrable (fun X : Riesz1.Configuration N => gap X j ^ (-r)) (gibbsMeasure p N) ∧
        (∫ X, gap X j ^ r ∂gibbsMeasure p N) + (∫ X, gap X j ^ (-r) ∂gibbsMeasure p N) ≤ D := by
  obtain ⟨D, hD, hmom⟩ := SingleGapTails.single_gap_moment_integrals s βlo βhi hs hs1 hβ hβhi r hr
  refine ⟨D, hD, fun p hps hpb N hN j => ?_⟩
  obtain ⟨hi1, hi2, hle⟩ := hmom p hps hpb.1 hpb.2 N hN j
  refine ⟨hi1, hi2, ?_⟩
  have hm1 : Measurable (fun X : Riesz1.Configuration N => gap X j ^ r) :=
    (Riesz1.measurable_gap j).pow_const r
  have hm2 : Measurable (fun X : Riesz1.Configuration N => gap X j ^ (-r)) :=
    (Riesz1.measurable_gap j).pow_const (-r)
  have hnn1 : 0 ≤ᵐ[gibbsMeasure p N] fun X => gap X j ^ r :=
    ae_of_all _ fun X => Real.rpow_nonneg (Riesz1.gap_pos X j).le r
  have hnn2 : 0 ≤ᵐ[gibbsMeasure p N] fun X => gap X j ^ (-r) :=
    ae_of_all _ fun X => Real.rpow_nonneg (Riesz1.gap_pos X j).le (-r)
  rw [integral_eq_lintegral_of_nonneg_ae hnn1 hm1.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae hnn2 hm2.aestronglyMeasurable,
    ← ENNReal.toReal_add (ENNReal.add_ne_top.mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle)).1
      (ENNReal.add_ne_top.mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle)).2]
  exact ENNReal.toReal_le_of_le_ofReal hD.le hle

/-- Fixed-temperature specialization of the moments for Theorem 2. -/
theorem gap_moment_bound {s β : ℝ} (hs : 0 < s) (hs1 : s ≠ 1) (hβ : 0 < β) (r : ℝ)
    (hr : 0 < r) :
    ∃ D : ℝ, 0 < D ∧ ∀ (p : Parameters), p.val.2 = s → p.val.1 = β →
      ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (j : ℤ),
        Integrable (fun X : Riesz1.Configuration N => gap X j ^ r) (gibbsMeasure p N) ∧
        Integrable (fun X : Riesz1.Configuration N => gap X j ^ (-r)) (gibbsMeasure p N) ∧
        (∫ X, gap X j ^ r ∂gibbsMeasure p N) + (∫ X, gap X j ^ (-r) ∂gibbsMeasure p N) ≤ D := by
  obtain ⟨D,hD,hmom⟩ := gap_moment_bound_locallyUniform hs hs1 hβ le_rfl r hr
  exact ⟨D,hD,fun p hps hpb => hmom p hps (by rw [hpb]; exact ⟨le_rfl,le_rfl⟩)⟩

/-- The total variation distance between the Gibbs law and its active tilt is at most the
mass of the event where the penalty is nonzero. -/
theorem totalVariation_activeTilt_le {N : ℕ+} (p : Parameters) (θ : PhysicalCutoff) {R : ℝ}
    (hR : 0 ≤ R) (ι : Bool) (I : Finset (Fin (N : ℕ))) :
    letI := gibbsMeasure_probability p N
    letI := activeTilt_isProbabilityMeasure p θ hR ι I
    Riesz2.totalVariation (gibbsMeasure p N) (activeTilt p N θ R ι I) ≤
      ENNReal.ofReal ((gibbsMeasure p N).real {X | activeGapPenalty θ R ι I X ≠ 0}) := by
  have := gibbsMeasure_probability p N
  exact NonnegativeTilt.totalVariation_expTilt_le (activeGapPenalty_measurable θ hR ι I)
    p.property.1.le (activeGapPenalty_nonneg θ hR ι I)

/-- The `L²` norm of a function of one active gap under the active tilt is at most
`√(z0⁻¹)` times its `L²` norm under the Gibbs law, when the normalizer is at least `z0`. -/
theorem eLpNorm_activeTilt_le {N : ℕ+} (p : Parameters) (θ : PhysicalCutoff) {R : ℝ}
    (hR : 0 ≤ R) (ι : Bool) (I : Finset (Fin (N : ℕ))) {z0 : ℝ} (hz0 : 0 < z0)
    (hz : z0 ≤ NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (activeGapPenalty θ R ι I))
    (a : ℝ → ℝ) (ha : Measurable a) (i : ℤ) :
    eLpNorm (fun X => a (gap X i)) 2 (activeTilt p N θ R ι I) ≤
      ENNReal.ofReal (Real.sqrt z0⁻¹) * eLpNorm (fun X => a (gap X i)) 2 (gibbsMeasure p N) := by
  have := gibbsMeasure_probability p N
  have hb : 0 ≤ p.val.1 := p.property.1.le
  have hG := activeGapPenalty_measurable θ hR ι I
  have hG0 := activeGapPenalty_nonneg θ hR ι I
  have hf : Measurable (fun X : Riesz1.Configuration N => a (gap X i)) :=
    ha.comp (Riesz1.measurable_gap i)
  have hkey : ∫⁻ X, ‖a (gap X i)‖ₑ ^ (2 : ℝ) ∂(activeTilt p N θ R ι I) ≤
      ENNReal.ofReal z0⁻¹ * ∫⁻ X, ‖a (gap X i)‖ₑ ^ (2 : ℝ) ∂(gibbsMeasure p N) := by
    unfold activeTilt
    refine (NonnegativeTilt.lintegral_expTilt_le hG hb hG0
      (hf.enorm.pow_const _)).trans (mul_le_mul_of_nonneg_right ?_ zero_le)
    rw [NonnegativeTilt.lintegral_normalizer_eq hG hb hG0]
    calc
      (ENNReal.ofReal (NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
          (activeGapPenalty θ R ι I)))⁻¹ ≤ (ENNReal.ofReal z0)⁻¹ :=
        ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal hz)
      _ = ENNReal.ofReal z0⁻¹ := (ENNReal.ofReal_inv_of_pos hz0).symm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  calc
    (∫⁻ X, ‖a (gap X i)‖ₑ ^ (2 : ℝ) ∂(activeTilt p N θ R ι I)) ^ (1 / (2 : ℝ))
        ≤ (ENNReal.ofReal z0⁻¹ * ∫⁻ X, ‖a (gap X i)‖ₑ ^ (2 : ℝ) ∂(gibbsMeasure p N)) ^
          (1 / (2 : ℝ)) := ENNReal.rpow_le_rpow hkey (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt z0⁻¹) *
          (∫⁻ X, ‖a (gap X i)‖ₑ ^ (2 : ℝ) ∂(gibbsMeasure p N)) ^ (1 / (2 : ℝ)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr hz0.le) (by norm_num),
          Real.sqrt_eq_rpow]

/-! ### The covariance of two observables under the active tilt -/

/-- The covariance of two observables of single active gaps changes under the active tilt by at
most `K U V (√(8 D₄ + 8) + (2 + K)(2 D₂ + 2))`, where `U` and `V` are the Lipschitz constants,
`K = Z⁻¹ (√q + q)`, and `q` bounds the mass of the event where the penalty is nonzero. -/
theorem covariance_activeTilt_pair_le {N : ℕ+} (p : Parameters) (θ : PhysicalCutoff) {R : ℝ}
    (hR1 : 1 ≤ R) (ι : Bool) (I : Finset (Fin (N : ℕ))) {z0 q D2 D4 K : ℝ}
    (hz0 : 0 < z0)
    (hz : z0 ≤ NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (activeGapPenalty θ R ι I))
    (hq : (gibbsMeasure p N).real {X | activeGapPenalty θ R ι I X ≠ 0} ≤ q)
    (hK : K = (NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (activeGapPenalty θ R ι I))⁻¹ * (Real.sqrt q + q))
    (ξ χ : GapObservable) (i j : ℤ)
    (hgi2 : Integrable (fun X : Riesz1.Configuration N => gap X i ^ (2 : ℝ)) (gibbsMeasure p N))
    (hgj2 : Integrable (fun X : Riesz1.Configuration N => gap X j ^ (2 : ℝ)) (gibbsMeasure p N))
    (hgi4 : Integrable (fun X : Riesz1.Configuration N => gap X i ^ (4 : ℝ)) (gibbsMeasure p N))
    (hgj4 : Integrable (fun X : Riesz1.Configuration N => gap X j ^ (4 : ℝ)) (gibbsMeasure p N))
    (hD2i : ∫ X, gap X i ^ (2 : ℝ) ∂gibbsMeasure p N ≤ D2)
    (hD2j : ∫ X, gap X j ^ (2 : ℝ) ∂gibbsMeasure p N ≤ D2)
    (hD4i : ∫ X, gap X i ^ (4 : ℝ) ∂gibbsMeasure p N ≤ D4)
    (hD4j : ∫ X, gap X j ^ (4 : ℝ) ∂gibbsMeasure p N ≤ D4) :
    |ProbabilityTheory.covariance (fun X => ξ.val.1 (gap X i)) (fun X => χ.val.1 (gap X j))
        (gibbsMeasure p N) -
      ProbabilityTheory.covariance (fun X => ξ.val.1 (gap X i)) (fun X => χ.val.1 (gap X j))
        (activeTilt p N θ R ι I)| ≤
      K * (derivativeSup ξ * derivativeSup χ) *
        (Real.sqrt (8 * D4 + 8) + (2 + K) * (2 * D2 + 2)) := by
  have hμ := gibbsMeasure_probability p N
  have hR0 : 0 ≤ R := by linarith
  have := activeTilt_isProbabilityMeasure p θ hR0 ι I
  have hb : 0 ≤ p.val.1 := p.property.1.le
  have hG := activeGapPenalty_measurable θ hR0 ι I
  have hG0 := activeGapPenalty_nonneg θ hR0 ι I
  have hq0 : 0 ≤ q := measureReal_nonneg.trans hq
  have hz_pos : 0 < NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (activeGapPenalty θ R ι I) := lt_of_lt_of_le hz0 hz
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg (inv_nonneg.mpr hz_pos.le) (add_nonneg (Real.sqrt_nonneg _) hq0)
  have hgi_m : Measurable (fun X : Riesz1.Configuration N => gap X i) :=
    Riesz1.measurable_gap i
  have hgj_m : Measurable (fun X : Riesz1.Configuration N => gap X j) :=
    Riesz1.measurable_gap j
  have hA_m : Measurable (fun X : Riesz1.Configuration N => ξ.val.1 (gap X i) - ξ.val.1 1) :=
    ((CenteredObservable.continuous_observable ξ).measurable.comp hgi_m).sub_const _
  have hB_m : Measurable (fun X : Riesz1.Configuration N => χ.val.1 (gap X j) - χ.val.1 1) :=
    ((CenteredObservable.continuous_observable χ).measurable.comp hgj_m).sub_const _
  have hA_int := (CenteredObservable.integrable_sq_sub_and_integral_le ξ hgi_m hgi2).1
  have hB_int := (CenteredObservable.integrable_sq_sub_and_integral_le χ hgj_m hgj2).1
  have hA2 : MemLp (fun X : Riesz1.Configuration N => ξ.val.1 (gap X i) - ξ.val.1 1) 2
      (gibbsMeasure p N) := (memLp_two_iff_integrable_sq hA_m.aestronglyMeasurable).mpr hA_int
  have hB2 : MemLp (fun X : Riesz1.Configuration N => χ.val.1 (gap X j) - χ.val.1 1) 2
      (gibbsMeasure p N) := (memLp_two_iff_integrable_sq hB_m.aestronglyMeasurable).mpr hB_int
  have hAB_int := (CenteredObservable.integrable_sq_mul_and_integral_le ξ χ hgi_m hgj_m hgi4 hgj4).1
  have hAB2 : MemLp (fun X : Riesz1.Configuration N =>
      (ξ.val.1 (gap X i) - ξ.val.1 1) * (χ.val.1 (gap X j) - χ.val.1 1)) 2 (gibbsMeasure p N) :=
    (memLp_two_iff_integrable_sq (hA_m.mul hB_m).aestronglyMeasurable).mpr hAB_int
  -- The centered observables are `L²` under the active tilt, by the normalizer lower bound.
  have hL2A := eLpNorm_activeTilt_le p θ hR0 ι I hz0 hz (fun x => ξ.val.1 x - ξ.val.1 1)
    (((CenteredObservable.continuous_observable ξ).measurable).sub_const _) i
  have hL2B := eLpNorm_activeTilt_le p θ hR0 ι I hz0 hz (fun x => χ.val.1 x - χ.val.1 1)
    (((CenteredObservable.continuous_observable χ).measurable).sub_const _) j
  have hAQ : MemLp (fun X : Riesz1.Configuration N => ξ.val.1 (gap X i) - ξ.val.1 1) 2
      (activeTilt p N θ R ι I) :=
    lt_of_le_of_lt hL2A (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hA2.eLpNorm_lt_top)
  have hBQ : MemLp (fun X : Riesz1.Configuration N => χ.val.1 (gap X j) - χ.val.1 1) 2
      (activeTilt p N θ R ι I) :=
    lt_of_le_of_lt hL2B (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hB2.eLpNorm_lt_top)
  -- Integrability of the uncentered observables, needed for the shift identities.
  have hξ_μ : Integrable (fun X : Riesz1.Configuration N => ξ.val.1 (gap X i))
      (gibbsMeasure p N) :=
    ((hA2.integrable one_le_two).add (integrable_const (ξ.val.1 1))).congr
      (ae_of_all _ fun X => by simp)
  have hχ_μ : Integrable (fun X : Riesz1.Configuration N => χ.val.1 (gap X j))
      (gibbsMeasure p N) :=
    ((hB2.integrable one_le_two).add (integrable_const (χ.val.1 1))).congr
      (ae_of_all _ fun X => by simp)
  have hξ_Q : Integrable (fun X : Riesz1.Configuration N => ξ.val.1 (gap X i))
      (activeTilt p N θ R ι I) :=
    ((hAQ.integrable one_le_two).add (integrable_const (ξ.val.1 1))).congr
      (ae_of_all _ fun X => by simp)
  have hχ_Q : Integrable (fun X : Riesz1.Configuration N => χ.val.1 (gap X j))
      (activeTilt p N θ R ι I) :=
    ((hBQ.integrable one_le_two).add (integrable_const (χ.val.1 1))).congr
      (ae_of_all _ fun X => by simp)
  -- The shift identities for the covariances.
  have e_μ : ProbabilityTheory.covariance (fun X => ξ.val.1 (gap X i))
      (fun X => χ.val.1 (gap X j)) (gibbsMeasure p N) =
      ProbabilityTheory.covariance (fun X => ξ.val.1 (gap X i) - ξ.val.1 1)
        (fun X => χ.val.1 (gap X j) - χ.val.1 1) (gibbsMeasure p N) := by
    rw [ProbabilityTheory.covariance_sub_const_right hχ_μ, ProbabilityTheory.covariance_sub_const_left hξ_μ]
  have e_Q : ProbabilityTheory.covariance (fun X => ξ.val.1 (gap X i))
      (fun X => χ.val.1 (gap X j)) (activeTilt p N θ R ι I) =
      ProbabilityTheory.covariance (fun X => ξ.val.1 (gap X i) - ξ.val.1 1)
        (fun X => χ.val.1 (gap X j) - χ.val.1 1) (activeTilt p N θ R ι I) := by
    rw [ProbabilityTheory.covariance_sub_const_right hχ_Q, ProbabilityTheory.covariance_sub_const_left hξ_Q]
  rw [e_μ, e_Q]
  -- The mean changes, from the tilt estimate with the scale `K`.
  have hA' : |∫ X, (ξ.val.1 (gap X i) - ξ.val.1 1) ∂activeTilt p N θ R ι I -
      ∫ X, (ξ.val.1 (gap X i) - ξ.val.1 1) ∂gibbsMeasure p N| ≤
      K * Real.sqrt (∫ X, (ξ.val.1 (gap X i) - ξ.val.1 1) ^ 2 ∂gibbsMeasure p N) := by
    rw [hK]
    exact NonnegativeTilt.abs_integral_expTilt_sub_le hG hb hG0 hA2 hq
  have hB' : |∫ X, (χ.val.1 (gap X j) - χ.val.1 1) ∂activeTilt p N θ R ι I -
      ∫ X, (χ.val.1 (gap X j) - χ.val.1 1) ∂gibbsMeasure p N| ≤
      K * Real.sqrt (∫ X, (χ.val.1 (gap X j) - χ.val.1 1) ^ 2 ∂gibbsMeasure p N) := by
    rw [hK]
    exact NonnegativeTilt.abs_integral_expTilt_sub_le hG hb hG0 hB2 hq
  have hAB' : |∫ X, (ξ.val.1 (gap X i) - ξ.val.1 1) * (χ.val.1 (gap X j) - χ.val.1 1)
      ∂activeTilt p N θ R ι I -
      ∫ X, (ξ.val.1 (gap X i) - ξ.val.1 1) * (χ.val.1 (gap X j) - χ.val.1 1)
        ∂gibbsMeasure p N| ≤
      K * Real.sqrt (∫ X, ((ξ.val.1 (gap X i) - ξ.val.1 1) *
        (χ.val.1 (gap X j) - χ.val.1 1)) ^ 2 ∂gibbsMeasure p N) := by
    rw [hK]
    exact NonnegativeTilt.abs_integral_expTilt_sub_le hG hb hG0 hAB2 hq
  have hcov := TiltedCovariance.abs_covariance_sub_covariance_le (gibbsMeasure p N)
    (activeTilt p N θ R ι I) hK0 hA2 hB2 hAQ hBQ hA' hB' hAB'
  refine hcov.trans ?_
  -- Scale estimates for the three `L²` norms.
  have hU0 : 0 ≤ derivativeSup ξ := ENNReal.toReal_nonneg
  have hV0 : 0 ≤ derivativeSup χ := ENNReal.toReal_nonneg
  have hD2_0 : 0 ≤ D2 := le_trans
    (integral_nonneg fun X => Real.rpow_nonneg (Riesz1.gap_pos X i).le _) hD2i
  have hD4_0 : 0 ≤ D4 := le_trans
    (integral_nonneg fun X => Real.rpow_nonneg (Riesz1.gap_pos X i).le _) hD4i
  have hy0 : 0 ≤ 2 * D2 + 2 := by linarith
  have hsA : Real.sqrt (∫ X, (ξ.val.1 (gap X i) - ξ.val.1 1) ^ 2 ∂gibbsMeasure p N) ≤
      derivativeSup ξ * Real.sqrt (2 * D2 + 2) := by
    have h1 := (CenteredObservable.integrable_sq_sub_and_integral_le ξ hgi_m hgi2).2
    calc
      _ ≤ Real.sqrt (derivativeSup ξ ^ 2 * (2 * D2 + 2)) :=
        Real.sqrt_le_sqrt (le_trans h1 (mul_le_mul_of_nonneg_left (by linarith [hD2i])
          (sq_nonneg _)))
      _ = derivativeSup ξ * Real.sqrt (2 * D2 + 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hU0]
  have hsB : Real.sqrt (∫ X, (χ.val.1 (gap X j) - χ.val.1 1) ^ 2 ∂gibbsMeasure p N) ≤
      derivativeSup χ * Real.sqrt (2 * D2 + 2) := by
    have h1 := (CenteredObservable.integrable_sq_sub_and_integral_le χ hgj_m hgj2).2
    calc
      _ ≤ Real.sqrt (derivativeSup χ ^ 2 * (2 * D2 + 2)) :=
        Real.sqrt_le_sqrt (le_trans h1 (mul_le_mul_of_nonneg_left (by linarith [hD2j])
          (sq_nonneg _)))
      _ = derivativeSup χ * Real.sqrt (2 * D2 + 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hV0]
  have hsAB : Real.sqrt (∫ X, ((ξ.val.1 (gap X i) - ξ.val.1 1) *
      (χ.val.1 (gap X j) - χ.val.1 1)) ^ 2 ∂gibbsMeasure p N) ≤
      derivativeSup ξ * derivativeSup χ * Real.sqrt (8 * D4 + 8) := by
    have h1 := (CenteredObservable.integrable_sq_mul_and_integral_le ξ χ hgi_m hgj_m hgi4 hgj4).2
    calc
      _ ≤ Real.sqrt ((derivativeSup ξ * derivativeSup χ) ^ 2 * (8 * D4 + 8)) :=
        Real.sqrt_le_sqrt (le_trans h1 (by
          have h2 : 4 * ∫ X, gap X i ^ (4 : ℝ) ∂gibbsMeasure p N +
              4 * ∫ X, gap X j ^ (4 : ℝ) ∂gibbsMeasure p N + 8 ≤ 8 * D4 + 8 := by
            linarith [hD4i, hD4j]
          have h3 : derivativeSup ξ ^ 2 * derivativeSup χ ^ 2 *
              (4 * ∫ X, gap X i ^ (4 : ℝ) ∂gibbsMeasure p N +
                4 * ∫ X, gap X j ^ (4 : ℝ) ∂gibbsMeasure p N + 8) ≤
              derivativeSup ξ ^ 2 * derivativeSup χ ^ 2 * (8 * D4 + 8) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
          nlinarith [h3]))
      _ = derivativeSup ξ * derivativeSup χ * Real.sqrt (8 * D4 + 8) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_nonneg hU0 hV0)]
  have hprod : derivativeSup ξ * Real.sqrt (2 * D2 + 2) *
      (derivativeSup χ * Real.sqrt (2 * D2 + 2)) = derivativeSup ξ * derivativeSup χ *
        (2 * D2 + 2) := by
    have hy := Real.mul_self_sqrt hy0
    calc
      _ = derivativeSup ξ * derivativeSup χ *
          (Real.sqrt (2 * D2 + 2) * Real.sqrt (2 * D2 + 2)) := by ring
      _ = derivativeSup ξ * derivativeSup χ * (2 * D2 + 2) := by rw [hy]
  calc
    _ ≤ K * (derivativeSup ξ * derivativeSup χ * Real.sqrt (8 * D4 + 8) +
          (2 + K) * (derivativeSup ξ * Real.sqrt (2 * D2 + 2) *
            (derivativeSup χ * Real.sqrt (2 * D2 + 2)))) := by
        apply mul_le_mul_of_nonneg_left _ hK0
        apply add_le_add hsAB
        exact mul_le_mul_of_nonneg_left (mul_le_mul hsA hsB (Real.sqrt_nonneg _)
          (mul_nonneg hU0 (Real.sqrt_nonneg _))) (by linarith)
    _ = K * (derivativeSup ξ * derivativeSup χ) *
        (Real.sqrt (8 * D4 + 8) + (2 + K) * (2 * D2 + 2)) := by
        rw [hprod]
        ring

/-- The derivative composed with one gap is square integrable under the Gibbs law, and so is the
centered observable. The two `MemLp` conclusions of `GapSecondMoments` follow from the
absolute continuity of the one-gap marginal. -/
theorem gapSecondMoments_observable (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (ξ χ : GapObservable) (i j : Fin (N : ℕ))
    (hgi2 : Integrable (fun X : Riesz1.Configuration N => gap X i.val ^ (2 : ℝ))
      (gibbsMeasure p N))
    (hgj2 : Integrable (fun X : Riesz1.Configuration N => gap X j.val ^ (2 : ℝ))
      (gibbsMeasure p N)) :
    GapSecondMoments p N i.val j.val ξ χ := by
  have := gibbsMeasure_probability p N
  have hac : ∀ k : Fin (N : ℕ), Measure.map (fun X : Riesz1.Configuration N => gap X k.val)
      (gibbsMeasure p N) ≪ volume := by
    intro k
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, N = (m + 1).succPNat :=
      ⟨(N : ℕ) - 2, PNat.eq (by simp only [Nat.succPNat_coe]; omega)⟩
    have h := GapDensities.gapLaw_marginal_absolutelyContinuous p m k
    have heq : Measure.map (fun X : Riesz1.Configuration (m + 1).succPNat => gap X k.val)
        (gibbsMeasure p (m + 1).succPNat) =
        Measure.map (fun g : Fin ((m + 1).succPNat : ℕ) → ℝ => g k)
          (gapLaw p (m + 1).succPNat) := by
      unfold gapLaw
      have hm : Measurable (Riesz2.gapVector (N := (m + 1).succPNat)) :=
        Riesz1.measurable_gapVector _
      rw [Measure.map_map (measurable_pi_apply k) hm]
      rfl
    rw [heq]
    exact h
  have hbd : ∀ (ζ : GapObservable) (k : Fin (N : ℕ)),
      MemLp (fun X : Riesz1.Configuration N => ζ.val.2 (gap X k.val)) 2 (gibbsMeasure p N) := by
    intro ζ k
    have hmk : Measurable (fun X : Riesz1.Configuration N => gap X k.val) :=
      Riesz1.measurable_gap _
    have hae : AEStronglyMeasurable (fun X : Riesz1.Configuration N => ζ.val.2 (gap X k.val))
        (gibbsMeasure p N) :=
      (ζ.property.2.1.mono_ac (hac k)).comp_measurable hmk
    have hbound : ∀ᵐ X ∂gibbsMeasure p N, ‖ζ.val.2 (gap X k.val)‖ ≤ derivativeSup ζ := by
      have h1 := CenteredObservable.ae_abs_derivative_le ζ
      have h2 : ∀ᵐ y ∂(Measure.map (fun X : Riesz1.Configuration N => gap X k.val)
          (gibbsMeasure p N)), |ζ.val.2 y| ≤ derivativeSup ζ := (hac k).ae_le h1
      filter_upwards [ae_of_ae_map hmk.aemeasurable h2] with X hX
      rw [Real.norm_eq_abs]
      exact hX
    exact MemLp.of_bound hae (derivativeSup ζ) hbound
  have hA_meas : Measurable (fun X : Riesz1.Configuration N => ξ.val.1 (gap X i.val) -
      ξ.val.1 1) :=
    (((CenteredObservable.continuous_observable ξ).measurable.comp
      (Riesz1.measurable_gap i.val))).sub_const _
  have hB_meas : Measurable (fun X : Riesz1.Configuration N => χ.val.1 (gap X j.val) -
      χ.val.1 1) :=
    (((CenteredObservable.continuous_observable χ).measurable.comp
      (Riesz1.measurable_gap j.val))).sub_const _
  have hA2 : MemLp (fun X : Riesz1.Configuration N => ξ.val.1 (gap X i.val) - ξ.val.1 1) 2
      (gibbsMeasure p N) :=
    (memLp_two_iff_integrable_sq hA_meas.aestronglyMeasurable).mpr
      (CenteredObservable.integrable_sq_sub_and_integral_le ξ (Riesz1.measurable_gap i.val)
        hgi2).1
  have hB2 : MemLp (fun X : Riesz1.Configuration N => χ.val.1 (gap X j.val) - χ.val.1 1) 2
      (gibbsMeasure p N) :=
    (memLp_two_iff_integrable_sq hB_meas.aestronglyMeasurable).mpr
      (CenteredObservable.integrable_sq_sub_and_integral_le χ (Riesz1.measurable_gap j.val)
        hgj2).1
  have hξL2 : MemLp (fun X : Riesz1.Configuration N => ξ.val.1 (gap X i.val)) 2
      (gibbsMeasure p N) := by
    have e : (fun X : Riesz1.Configuration N => ξ.val.1 (gap X i.val)) =
        fun X => (ξ.val.1 (gap X i.val) - ξ.val.1 1) + ξ.val.1 1 := by
      funext X
      ring
    rw [e]
    exact hA2.add (memLp_const _)
  have hχL2 : MemLp (fun X : Riesz1.Configuration N => χ.val.1 (gap X j.val)) 2
      (gibbsMeasure p N) := by
    have e : (fun X : Riesz1.Configuration N => χ.val.1 (gap X j.val)) =
        fun X => (χ.val.1 (gap X j.val) - χ.val.1 1) + χ.val.1 1 := by
      funext X
      ring
    rw [e]
    exact hB2.add (memLp_const _)
  unfold GapSecondMoments
  exact ⟨hξL2, hχL2, hbd ξ i, hbd χ j⟩

/-! ### Constants and the main theorem -/

/-- The mass of `{F ≠ 0}` is at most `|I| (3 + A) e^{-c₁ R}`, once `R ≥ 1` and `c₁` is below the
two rates of the one-gap tails. -/
theorem activeGap_mass_le_exp {N : ℕ+} (p : Parameters) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) {s β A R c1 : ℝ} (hs : 1 < s) (hβ : 0 < β) (hA0 : 0 ≤ A)
    (hR : 1 ≤ R) (hc1a : c1 ≤ Real.log 2 / 8) (hc1b : c1 ≤ β / 2 ^ s)
    (hA : ∀ (j : ℤ) (u : ℝ), gibbsMeasure p N {X | u ≤ gap X j ^ (-s)} ≤
      ENNReal.ofReal (A * Real.exp (-β * u))) (ι : Bool) (I : Finset (Fin (N : ℕ))) :
    (gibbsMeasure p N).real {X | activeGapPenalty θ R ι I X ≠ 0} ≤
      I.card * ((3 + A) * Real.exp (-c1 * R)) := by
  have hR0 : 0 ≤ R := by linarith
  have h := activeGapPenalty_measureReal_le p hN θ (s := s) (β := β) (A := A) (R := R)
    (by linarith) (by linarith) hA0 hA ι I
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  have e1 : Real.exp (-(Real.log 2 / 4) * (R / 2)) ≤ Real.exp (-c1 * R) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hc1a hR0])
  have hRs : R ≤ R ^ s := by
    have h1 := Real.rpow_le_rpow_of_exponent_le hR hs.le
    simpa using h1
  have hdiv : R / 2 ^ s ≤ (R / 2) ^ s := by
    rw [Real.div_rpow hR0 (by norm_num)]
    exact div_le_div_of_nonneg_right hRs (by positivity)
  have e2 : Real.exp (-β * (R / 2) ^ s) ≤ Real.exp (-c1 * R) := by
    apply Real.exp_le_exp.mpr
    have h1 : c1 * R ≤ β / 2 ^ s * R := mul_le_mul_of_nonneg_right hc1b hR0
    have h2 : β / 2 ^ s * R ≤ β * (R / 2) ^ s := by
      calc
        β / 2 ^ s * R = β * (R / 2 ^ s) := by ring
        _ ≤ β * (R / 2) ^ s := mul_le_mul_of_nonneg_left hdiv hβ.le
    nlinarith
  calc
    3 * Real.exp (-(Real.log 2 / 4) * (R / 2)) + A * Real.exp (-β * (R / 2) ^ s)
        ≤ 3 * Real.exp (-c1 * R) + A * Real.exp (-c1 * R) :=
          add_le_add (mul_le_mul_of_nonneg_left e1 (by norm_num))
            (mul_le_mul_of_nonneg_left e2 hA0)
    _ = (3 + A) * Real.exp (-c1 * R) := by ring

/-- A geometric-type threshold: a constant times `exp(-c n^δ)` is at most `1/2` for all large
`n`. -/
theorem exists_threshold_exp {Kq c δ : ℝ} (hδ : 0 < δ) (hc : 0 < c) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → Kq * Real.exp (-c * (n : ℝ) ^ δ) ≤ 1 / 2 := by
  have h1 := StretchedCutoff.tendsto_power_mul_exp hδ hc 0
  have h2 : Tendsto (fun n : ℕ => Kq * Real.exp (-c * (n : ℝ) ^ δ)) atTop (𝓝 0) := by
    have h3 := (h1.comp tendsto_natCast_atTop_atTop).const_mul Kq
    simpa [Function.comp_def, Real.rpow_zero, one_mul, mul_zero] using h3
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp
    (h2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  exact ⟨n0, fun n hn => (hn0 n hn).le⟩

/-- The main estimate of the proof of Theorem 2. For each cutoff `θ`, there are
constants `C, c, δ > 0`, depending on `s`, `β`, `h` and `θ`, such that for every inverse-temperature
parameter `p` with `p.val.2 = s` and `p.val.1 = β`, every `ι`, every `N ≥ 2`, and every active set
`I` with `1 ≤ |I|` and `2 |I| ≤ N` or `|I| = N`, with `R = |I|^h`:
* the total variation between the gap law and its active tilt is at most `C e^{-c R}`.
* for all observables `ξ`, `χ` and labels `i, j ∈ I`, the covariance of `ξ(x_i)` and `χ(x_j)`
  changes by at most `C e^{-c R} U V`, where `U, V` are the essential suprema of the derivatives.
* for every measurable `a`, the `L²` norm of `a(x_i)` under the tilt is at most `C` times its
  `L²` norm under the Gibbs law. -/
theorem activeTilt_observable_transfer (s β h : ℝ) (hs : 1 < s) (hβ : 0 < β) (hh : 0 < h)
    (θ : PhysicalCutoff) :
    ∃ C c δ : ℝ, 0 < C ∧ 0 < c ∧ 0 < δ ∧
      ∀ (p : Parameters), p.val.2 = s → p.val.1 = β →
        ∀ (ι : Bool) (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (I : Finset (Fin (N : ℕ))), I.Nonempty →
          (2 * I.card ≤ (N : ℕ) ∨ I.card = (N : ℕ)) →
          letI := gibbsMeasure_probability p N
          letI : IsProbabilityMeasure (gapLaw p N) := by unfold gapLaw; infer_instance
          letI := activeTilt_isProbabilityMeasure p θ (Real.rpow_nonneg (Nat.cast_nonneg I.card) h) ι I
          totalVariation (gapLaw p N)
            ((activeTilt p N θ ((I.card : ℝ) ^ h) ι I).map (gapVector (N := N))) ≤
            ENNReal.ofReal (C * Real.exp (-c * (I.card : ℝ) ^ δ)) ∧
          (∀ (ξ χ : GapObservable) (i j : Fin (N : ℕ)), i ∈ I → j ∈ I →
            GapSecondMoments p N i.val j.val ξ χ ∧
            |ProbabilityTheory.covariance (fun X => ξ.val.1 (gap X i.val))
                (fun X => χ.val.1 (gap X j.val)) (gibbsMeasure p N) -
              ProbabilityTheory.covariance (fun X => ξ.val.1 (gap X i.val))
                (fun X => χ.val.1 (gap X j.val)) (activeTilt p N θ ((I.card : ℝ) ^ h) ι I)| ≤
              C * Real.exp (-c * (I.card : ℝ) ^ δ) * derivativeSup ξ * derivativeSup χ) ∧
          (∀ (a : ℝ → ℝ), Measurable a → ∀ i ∈ I,
            eLpNorm (fun X => a (gap X i.val)) 2
                (activeTilt p N θ ((I.card : ℝ) ^ h) ι I) ≤
              ENNReal.ofReal C * eLpNorm (fun X => a (gap X i.val)) 2 (gibbsMeasure p N)) := by
  -- Constants from the one-gap inputs, the cutoff growth, and the rate.
  obtain ⟨Kθ, hKθ0, hKθ⟩ := PhysicalCutoff.exists_sq_bound θ
  obtain ⟨Aβ, hAβ0, hAβ⟩ := gap_inverse_tail (s := s) (β := β) (by linarith) hβ
  obtain ⟨D2, hD2, hmom2⟩ := gap_moment_bound (s := s) (β := β) (by linarith)
    (ne_of_gt hs) hβ 2 (by norm_num)
  obtain ⟨D4, hD4, hmom4⟩ := gap_moment_bound (s := s) (β := β) (by linarith)
    (ne_of_gt hs) hβ 4 (by norm_num)
  obtain ⟨c1, hc1, hc1a, hc1b⟩ : ∃ c1 : ℝ, 0 < c1 ∧ c1 ≤ Real.log 2 / 8 ∧ c1 ≤ β / 2 ^ s :=
    ⟨min (Real.log 2 / 8) (β / 2 ^ s),
      lt_min (div_pos (Real.log_pos one_lt_two) (by norm_num)) (div_pos hβ (by positivity)),
      min_le_left _ _, min_le_right _ _⟩
  obtain ⟨K1, hK1_0, hK1⟩ := MomentEvent.exists_rpow_mul_exp_neg_le (a := 1) (c := c1)
    (c' := c1 / 2) (δ := h) hh (by linarith)
  obtain ⟨Kq, hKq_def⟩ : ∃ Kq : ℝ, Kq = (3 + Aβ) * K1 := ⟨_, rfl⟩
  have hKq0 : 0 ≤ Kq := by rw [hKq_def]; exact mul_nonneg (by linarith) hK1_0
  obtain ⟨n0, hn0⟩ := exists_threshold_exp (Kq := Kq) (c := c1 / 2) (δ := h) hh (by linarith)
  obtain ⟨z0, hz0, hz0_half, hz0_jensen⟩ : ∃ z0 : ℝ, 0 < z0 ∧ z0 ≤ 1 / 2 ∧
      z0 ≤ Real.exp (-β * ((n0 : ℝ) * (Kθ * D2))) :=
    ⟨min (1 / 2) (Real.exp (-β * ((n0 : ℝ) * (Kθ * D2)))), lt_min (by norm_num) (Real.exp_pos _),
      min_le_left _ _, min_le_right _ _⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = (1 + Real.sqrt Kq) / z0 := ⟨_, rfl⟩
  obtain ⟨C2, hC2⟩ : ∃ C2 : ℝ, C2 = (Real.sqrt Kq + Kq) / z0 := ⟨_, rfl⟩
  obtain ⟨Mcov, hMcov⟩ : ∃ M : ℝ, M = Real.sqrt (8 * D4 + 8) + (2 + C2) * (2 * D2 + 2) :=
    ⟨_, rfl⟩
  obtain ⟨Ccov, hCcov⟩ : ∃ K : ℝ, K = κ * Real.sqrt Kq * Mcov := ⟨_, rfl⟩
  obtain ⟨CL, hCL⟩ : ∃ K : ℝ, K = Real.sqrt z0⁻¹ := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ K : ℝ, K = Kq + CL + Ccov + 1 := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := by rw [hκ]; exact div_nonneg (by positivity) hz0.le
  have hC20 : 0 ≤ C2 := by rw [hC2]; exact div_nonneg (by positivity) hz0.le
  have hMcov0 : 0 ≤ Mcov := by
    rw [hMcov]
    exact add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by linarith) (by linarith))
  have hCcov0 : 0 ≤ Ccov := by
    rw [hCcov]
    exact mul_nonneg (mul_nonneg hκ0 (Real.sqrt_nonneg _)) hMcov0
  have hCL0 : 0 ≤ CL := by rw [hCL]; exact Real.sqrt_nonneg _
  have hCL_le : CL ≤ C := by rw [hC]; linarith
  have hKq_le : Kq ≤ C := by rw [hC]; linarith
  have hC_pos : 0 < C := by rw [hC]; linarith
  refine ⟨C, c1 / 4, h, hC_pos, div_pos hc1 (by norm_num), hh, ?_⟩
  intro p hps hpβ ι N hN I hI hcard
  have hμ : IsProbabilityMeasure (gibbsMeasure p N) := gibbsMeasure_probability p N
  have : IsProbabilityMeasure (gapLaw p N) := by unfold gapLaw; infer_instance
  have := activeTilt_isProbabilityMeasure p θ (Real.rpow_nonneg (Nat.cast_nonneg I.card) h) ι I
  have hcard' : (1 : ℝ) ≤ (I.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hI
  have hR1 : 1 ≤ (I.card : ℝ) ^ h := Real.one_le_rpow hcard' hh.le
  have hR0 : 0 ≤ (I.card : ℝ) ^ h := Real.rpow_nonneg (Nat.cast_nonneg _) h
  have hb : 0 ≤ p.val.1 := p.property.1.le
  have hG := activeGapPenalty_measurable θ hR0 ι I
  have hG0 := activeGapPenalty_nonneg θ hR0 ι I
  -- The mass of the event where the penalty is nonzero.
  obtain ⟨q, hq_def⟩ : ∃ q : ℝ, q = Kq * Real.exp (-(c1 / 2) * ((I.card : ℝ) ^ h)) := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq_def]; exact mul_nonneg hKq0 (Real.exp_pos _).le
  have hq : (gibbsMeasure p N).real {X | activeGapPenalty θ ((I.card : ℝ) ^ h) ι I X ≠ 0} ≤ q := by
    have h1 := activeGap_mass_le_exp p hN θ hs hβ hAβ0.le hR1 hc1a hc1b
      (fun j u => hAβ p hps hpβ N hN j u) ι I
    have h2 := hK1 (I.card : ℝ) hcard'
    rw [Real.rpow_one] at h2
    rw [hq_def, hKq_def]
    calc
      (gibbsMeasure p N).real {X | activeGapPenalty θ ((I.card : ℝ) ^ h) ι I X ≠ 0}
          ≤ I.card * ((3 + Aβ) * Real.exp (-c1 * ((I.card : ℝ) ^ h))) := h1
      _ = (3 + Aβ) * ((I.card : ℝ) * Real.exp (-c1 * ((I.card : ℝ) ^ h))) := by ring
      _ ≤ (3 + Aβ) * (K1 * Real.exp (-(c1 / 2) * ((I.card : ℝ) ^ h))) :=
          mul_le_mul_of_nonneg_left h2 (by linarith)
      _ = (3 + Aβ) * K1 * Real.exp (-(c1 / 2) * ((I.card : ℝ) ^ h)) := by ring
  -- The normalizer is bounded below uniformly.
  have hz : z0 ≤ NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (activeGapPenalty θ ((I.card : ℝ) ^ h) ι I) := by
    rcases le_total I.card n0 with hn | hn
    · have hJ := expTiltNormalizer_ge_of_card p θ hKθ0 hKθ hR1
        (fun j => hmom2 p hps hpβ N hN j) ι I
      have hexp : -p.val.1 * ((I.card : ℝ) * (Kθ * D2)) = -β * ((I.card : ℝ) * (Kθ * D2)) := by
        rw [hpβ]
      rw [hexp] at hJ
      have hle : Real.exp (-β * ((n0 : ℝ) * (Kθ * D2))) ≤
          Real.exp (-β * ((I.card : ℝ) * (Kθ * D2))) := by
        apply Real.exp_le_exp.mpr
        have hn' : (I.card : ℝ) ≤ (n0 : ℝ) := by exact_mod_cast hn
        have hK : 0 ≤ β * (Kθ * D2) := mul_nonneg hβ.le (mul_nonneg hKθ0 hD2.le)
        linarith [mul_le_mul_of_nonneg_right hn' hK]
      linarith
    · have hqh : q ≤ 1 / 2 := by
        rw [hq_def]
        exact hn0 I.card hn
      have hone := NonnegativeTilt.one_sub_expTiltNormalizer_le (μ := gibbsMeasure p N) hG hb hG0
      linarith [hq]
  -- The total variation between the gap law and the active tilt.
  have htv : totalVariation (gapLaw p N)
      ((activeTilt p N θ ((I.card : ℝ) ^ h) ι I).map (gapVector (N := N))) ≤
      ENNReal.ofReal (C * Real.exp (-(c1 / 4) * ((I.card : ℝ) ^ h))) := by
    have h1 : totalVariation (gapLaw p N)
        ((activeTilt p N θ ((I.card : ℝ) ^ h) ι I).map (gapVector (N := N))) ≤
        totalVariation (gibbsMeasure p N) (activeTilt p N θ ((I.card : ℝ) ^ h) ι I) :=
      NonnegativeTilt.totalVariation_map_le (gibbsMeasure p N) (activeTilt p N θ ((I.card : ℝ) ^ h) ι I)
        (gapVector (N := N)) (Riesz1.measurable_gapVector N)
    have h2 : totalVariation (gibbsMeasure p N) (activeTilt p N θ ((I.card : ℝ) ^ h) ι I) ≤
        ENNReal.ofReal ((gibbsMeasure p N).real
          {X | activeGapPenalty θ ((I.card : ℝ) ^ h) ι I X ≠ 0}) :=
      totalVariation_activeTilt_le p θ hR0 ι I
    have h3 : ENNReal.ofReal ((gibbsMeasure p N).real
          {X | activeGapPenalty θ ((I.card : ℝ) ^ h) ι I X ≠ 0}) ≤
        ENNReal.ofReal (C * Real.exp (-(c1 / 4) * ((I.card : ℝ) ^ h))) := by
      apply ENNReal.ofReal_le_ofReal
      refine hq.trans ?_
      rw [hq_def]
      apply mul_le_mul hKq_le (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hC_pos.le
      nlinarith
    exact h1.trans (h2.trans h3)
  -- The `L²` bound, from the normalizer lower bound.
  have hL2 : ∀ a : ℝ → ℝ, Measurable a → ∀ i ∈ I,
      eLpNorm (fun X => a (gap X i.val)) 2 (activeTilt p N θ ((I.card : ℝ) ^ h) ι I) ≤
        ENNReal.ofReal C * eLpNorm (fun X => a (gap X i.val)) 2 (gibbsMeasure p N) := by
    intro a ha i _
    refine (eLpNorm_activeTilt_le p θ hR0 ι I hz0 hz a ha (i.val : ℤ)).trans ?_
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (by rw [← hCL]; exact hCL_le))
      zero_le
  refine ⟨htv, ?_, hL2⟩
  intro ξ χ i j hi hj
  refine ⟨gapSecondMoments_observable p N hN ξ χ i j (hmom2 p hps hpβ N hN (i.val : ℤ)).1
    (hmom2 p hps hpβ N hN (j.val : ℤ)).1, ?_⟩
  have hU0 : 0 ≤ derivativeSup ξ := ENNReal.toReal_nonneg
  have hV0 : 0 ≤ derivativeSup χ := ENNReal.toReal_nonneg
  have hD2of : ∀ k : ℤ, ∫ X, gap X k ^ (2 : ℝ) ∂gibbsMeasure p N ≤ D2 := by
    intro k
    have h1 := (hmom2 p hps hpβ N hN k).2.2
    have h2 : 0 ≤ ∫ X, gap X k ^ (-(2 : ℝ)) ∂gibbsMeasure p N :=
      integral_nonneg fun X => Real.rpow_nonneg (Riesz1.gap_pos X k).le _
    linarith
  have hD4of : ∀ k : ℤ, ∫ X, gap X k ^ (4 : ℝ) ∂gibbsMeasure p N ≤ D4 := by
    intro k
    have h1 := (hmom4 p hps hpβ N hN k).2.2
    have h2 : 0 ≤ ∫ X, gap X k ^ (-(4 : ℝ)) ∂gibbsMeasure p N :=
      integral_nonneg fun X => Real.rpow_nonneg (Riesz1.gap_pos X k).le _
    linarith
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N)
      p.val.1 (activeGapPenalty θ ((I.card : ℝ) ^ h) ι I))⁻¹ * (Real.sqrt q + q) := ⟨_, rfl⟩
  have hpair := covariance_activeTilt_pair_le p θ hR1 ι I hz0 hz hq hK ξ χ (i.val : ℤ) (j.val : ℤ)
    (hmom2 p hps hpβ N hN _).1 (hmom2 p hps hpβ N hN _).1 (hmom4 p hps hpβ N hN _).1
    (hmom4 p hps hpβ N hN _).1 (hD2of _) (hD2of _) (hD4of _) (hD4of _)
  -- Scale estimates on `K` and on `√q`.
  have hq_le_Kq : q ≤ Kq := by
    rw [hq_def]
    exact mul_le_of_le_one_right hKq0 (Real.exp_le_one_iff.mpr
      (by linarith [mul_nonneg (show (0 : ℝ) ≤ c1 / 2 by linarith) hR0]))
  have hsqKq : Real.sqrt q ≤ Real.sqrt Kq := Real.sqrt_le_sqrt hq_le_Kq
  have hqle : q ≤ Real.sqrt Kq * Real.sqrt q := by
    have hself := Real.mul_self_sqrt hq0
    calc
      q = Real.sqrt q * Real.sqrt q := hself.symm
      _ ≤ Real.sqrt Kq * Real.sqrt q :=
        mul_le_mul_of_nonneg_right hsqKq (Real.sqrt_nonneg _)
  have hzinv : (NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (activeGapPenalty θ ((I.card : ℝ) ^ h) ι I))⁻¹ ≤ z0⁻¹ := inv_anti₀ hz0 hz
  have hKle1 : K ≤ κ * Real.sqrt q := by
    rw [hK, hκ]
    calc
      _ ≤ z0⁻¹ * (Real.sqrt q + q) :=
        mul_le_mul_of_nonneg_right hzinv (add_nonneg (Real.sqrt_nonneg _) hq0)
      _ ≤ z0⁻¹ * ((1 + Real.sqrt Kq) * Real.sqrt q) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hz0.le)
        linarith [hqle, show (1 + Real.sqrt Kq) * Real.sqrt q = Real.sqrt q + Real.sqrt Kq * Real.sqrt q by ring]
      _ = (1 + Real.sqrt Kq) / z0 * Real.sqrt q := by ring
  have hKle2 : K ≤ C2 := by
    rw [hK, hC2]
    calc
      _ ≤ z0⁻¹ * (Real.sqrt q + q) :=
        mul_le_mul_of_nonneg_right hzinv (add_nonneg (Real.sqrt_nonneg _) hq0)
      _ ≤ z0⁻¹ * (Real.sqrt Kq + Kq) :=
        mul_le_mul_of_nonneg_left (add_le_add hsqKq hq_le_Kq) (inv_nonneg.mpr hz0.le)
      _ = (Real.sqrt Kq + Kq) / z0 := by ring
  have hK0' : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg (inv_nonneg.mpr (hz0.trans_le hz).le) (add_nonneg (Real.sqrt_nonneg _) hq0)
  have hy0 : 0 ≤ 2 * D2 + 2 := by linarith
  have hA : K * (Real.sqrt (8 * D4 + 8) + (2 + K) * (2 * D2 + 2)) ≤
      (κ * Real.sqrt q) * (Real.sqrt (8 * D4 + 8) + (2 + C2) * (2 * D2 + 2)) := by
    apply mul_le_mul hKle1 _ (add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by linarith) hy0))
      (mul_nonneg hκ0 (Real.sqrt_nonneg _))
    have hfac : (2 + K) * (2 * D2 + 2) ≤ (2 + C2) * (2 * D2 + 2) :=
      mul_le_mul_of_nonneg_right (by linarith [hKle2]) hy0
    linarith [hfac]
  have hsq : Real.sqrt q = Real.sqrt Kq * Real.exp (-(c1 / 4) * ((I.card : ℝ) ^ h)) := by
    have hE : Real.exp (-(c1 / 2) * ((I.card : ℝ) ^ h)) =
        Real.exp (-(c1 / 4) * ((I.card : ℝ) ^ h)) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hq_def, hE, Real.sqrt_mul hKq0, Real.sqrt_sq (Real.exp_pos _).le]
  have hCcov_le : Ccov ≤ C := by rw [hC]; linarith
  calc
    _ ≤ K * (derivativeSup ξ * derivativeSup χ) *
        (Real.sqrt (8 * D4 + 8) + (2 + K) * (2 * D2 + 2)) := hpair
    _ = (derivativeSup ξ * derivativeSup χ) *
        (K * (Real.sqrt (8 * D4 + 8) + (2 + K) * (2 * D2 + 2))) := by ring
    _ ≤ (derivativeSup ξ * derivativeSup χ) *
        ((κ * Real.sqrt q) * (Real.sqrt (8 * D4 + 8) + (2 + C2) * (2 * D2 + 2))) :=
      mul_le_mul_of_nonneg_left hA (mul_nonneg hU0 hV0)
    _ = (derivativeSup ξ * derivativeSup χ) *
        (Ccov * Real.exp (-(c1 / 4) * ((I.card : ℝ) ^ h))) := by
      rw [hsq, hCcov, hMcov]
      ring
    _ ≤ (derivativeSup ξ * derivativeSup χ) *
        (C * Real.exp (-(c1 / 4) * ((I.card : ℝ) ^ h))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCcov_le (Real.exp_pos _).le)
        (mul_nonneg hU0 hV0)
    _ = C * Real.exp (-(c1 / 4) * ((I.card : ℝ) ^ h)) * derivativeSup ξ * derivativeSup χ := by
      ring

/-! ### Agreement with the first-block objects -/

/-- The active tilt is the normalized tilt of the Gibbs law by the active penalty. -/
theorem activeTilt_eq_expTilt (p : Parameters) (N : ℕ+) (θ : PhysicalCutoff) (R : ℝ)
    (ι : Bool) (I : Finset (Fin (N : ℕ))) :
    activeTilt p N θ R ι I =
      NonnegativeTilt.expTilt (gibbsMeasure p N) p.val.1 (activeGapPenalty θ R ι I) :=
  rfl

/-- On the first `n` labels, the active penalty with `R = n^ε` is the `physicalGapPenalty` with parameter `ε` (Subsection 4.4, with `I = {1, …, n}`). -/
theorem activeGapPenalty_firstGapSet {N n : ℕ+} (hn : (n : ℕ) ≤ (N : ℕ)) (θ : PhysicalCutoff)
    (ε : ℝ) (ι : Bool) :
    activeGapPenalty θ ((n : ℝ) ^ ε) ι (Finset.univ.map (Fin.castLEEmb hn)) =
      physicalGapPenalty N n hn θ ε ι := by
  funext X
  unfold activeGapPenalty physicalGapPenalty
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hR : (n : ℝ) ^ (-ε) = ((n : ℝ) ^ ε)⁻¹ := Real.rpow_neg (Nat.cast_nonneg _) ε
  have h1 : gap X ((Fin.castLEEmb hn i : Fin (N : ℕ)) : ℕ) / ((n : ℝ) ^ ε) =
      ((n : ℝ) ^ ε)⁻¹ * gap X (i : ℕ) := by
    rw [div_eq_inv_mul]
    try rfl
  have h2 : 1 / ((n : ℝ) ^ ε * gap X ((Fin.castLEEmb hn i : Fin (N : ℕ)) : ℕ)) =
      ((n : ℝ) ^ ε)⁻¹ * (gap X (i : ℕ))⁻¹ := by
    rw [one_div, mul_inv]
    try rfl
  rw [hR, h1, h2]

/-- The active tilt on the first `n` labels is the tilted particle measure. -/
theorem activeTilt_firstGapSet (p : Parameters) (N n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ) (ι : Bool) :
    activeTilt p N θ ((n : ℝ) ^ ε) ι (Finset.univ.map (Fin.castLEEmb hn)) =
      tiltedParticleMeasure p N n hn θ ε ι := by
  rw [activeTilt_eq_expTilt, activeGapPenalty_firstGapSet hn θ ε ι]
  rfl

end Riesz2.DecayShort
