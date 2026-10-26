/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.LengthAveragingFibresPart2
public import Riesz2.Thermodynamic.FixedLengthDecayPart2
public import Riesz2.DecayShort.PhysicalComparisonPart3
import all Riesz2.DecayShort.ExceptionalEventPart4

/-!
# Short conditional length errors and normal estimates

Supporting estimates for the proof of Lemma 6.5. The fine tolerance is independent of
the physical penalty exponent.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators Classical ContDiff

namespace Riesz2.LengthAveragingFibres

/-- Internal monotonicity of all six coefficient thresholds in Subsection 4.4. The boundary profiles remain the literal profiles. -/
theorem short_coefficient_event_mono_internal (p : Parameters) (n : ℕ+) (m : ℕ)
    (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) {D E : ℝ} (hDE : D ≤ E) :
    DecayShort.ExceptionalEvent.coefficientEvent p n m hn D ⊆
      DecayShort.ExceptionalEvent.coefficientEvent p n m hn E := by
  intro x hx
  rcases hx with ⟨hP, hp, hs, hf, hb, hv⟩
  refine ⟨fun i j => (hP i j).trans ?_, fun k => (hp k).trans ?_,
    fun k => (hs k).trans ?_, hf.trans ?_, fun i => (hb i).trans ?_,
    fun i => (hv i).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right hDE (Real.rpow_nonneg (by positivity) _)
  · exact mul_le_mul_of_nonneg_right hDE (Real.rpow_nonneg (by positivity) _)
  · exact mul_le_mul_of_nonneg_right hDE (Real.rpow_nonneg (by positivity) _)
  · exact mul_le_mul_of_nonneg_right hDE (Real.rpow_nonneg (by positivity) _)
  · exact div_le_div_of_nonneg_right hDE (by positivity)
  · exact mul_le_mul_of_nonneg_right hDE (Real.rpow_nonneg (by positivity) _)

/-- See the proof of Lemma 6.5 in the paper: probability of the exact
short fine event under the physical two-sided law. Its loss exponent is
chosen before either tolerance or temperature. Only the prefactors used
to cover finitely many small sizes depend on the temperature interval. -/
theorem short_fine_event_probability (s : ℝ) (hs : 1 < s) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ η →
      ∀ (θ : PhysicalCutoff) (βlo βhi : ℝ), 0 < βlo → βlo ≤ βhi →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ (n : ℕ+) (m : ℕ), 2 ≤ (n : ℕ) →
      2 * (n : ℕ) ≤ (n : ℕ) + m + 1 → ∀ κ : ℝ, κ₀ ≤ κ →
      let μ := (activeTiltedGapLaw p ((n : ℕ) + m).succPNat n (by simp; omega)
        θ ε true).comap
          ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
      μ (shortFineEvent p n m η κ)ᶜ ≤
        ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ δ)) := by
  obtain ⟨k, hk, hprob⟩ := DecayShort.ExceptionalEvent.proper_good_event_probability s hs
  refine ⟨k + 1, by linarith, fun η hη => ?_⟩
  obtain ⟨δ, hδ, htail⟩ := hprob η hη
  refine ⟨δ, hδ, fun ε hε hεη θ βlo βhi hlo hle => ?_⟩
  obtain ⟨A, C, c, hA, hC, hc, ht⟩ := htail θ βlo βhi hlo hle
  obtain ⟨z, hz, _, hdom⟩ := compact_fine_active_domination s ε βlo βhi
    (by linarith) hs.ne' hε hlo hle θ
  let R := max 2 (A ^ η⁻¹)
  let D := C + Real.exp (c * R ^ δ)
  have hD : 0 < D := add_pos hC (Real.exp_pos _)
  refine ⟨z⁻¹ * D, c, by positivity, hc, ?_⟩
  intro p hp hpl hph n m hn hhalf κ hκ μ
  let ν := (activeTiltedGapLaw p ((n : ℕ) + m).succPNat n (by simp; omega)
    θ η false).comap
      ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
  have : IsProbabilityMeasure ν := DecayShort.activeTilt_proper_probability _ _ _ _ _ _ _
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hν : ν (shortFineEvent p n m η κ)ᶜ ≤
      ENNReal.ofReal (D * Real.exp (-c * (n : ℝ) ^ δ)) := by
    by_cases hlarge : R ≤ (n : ℝ)
    · have hAn : A ≤ (n : ℝ) ^ η := by
        have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ A ^ η⁻¹)
          ((le_max_right 2 _).trans hlarge) hη.le
        rwa [Real.rpow_inv_rpow (by linarith : 0 ≤ A) hη.ne'] at hpow
      have hthreshold : A * (n : ℝ) ^ (k * η) ≤ (n : ℝ) ^ (κ * η) := by
        calc
          _ ≤ (n : ℝ) ^ η * (n : ℝ) ^ (k * η) :=
            mul_le_mul_of_nonneg_right hAn (Real.rpow_nonneg hn0.le _)
          _ = (n : ℝ) ^ ((k + 1) * η) := by
            rw [← Real.rpow_add hn0]
            congr 1
            ring
          _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1
            (mul_le_mul_of_nonneg_right hκ hη.le)
      have hsub : DecayShort.ExceptionalEvent.properGoodEvent p n m
          (by simp; omega) η (A * (n : ℝ) ^ (k * η)) ⊆ shortFineEvent p n m η κ := by
        intro x hx
        exact ⟨hx.1, short_coefficient_event_mono_internal p n m _ hthreshold hx.2⟩
      apply (measure_mono (compl_subset_compl.mpr hsub)).trans
      apply (ht p hp hpl hph n m (by simp; omega) (by omega) hhalf false).trans
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact le_add_of_nonneg_right (Real.exp_pos _).le
    · have hnR : (n : ℝ) ≤ R := (lt_of_not_ge hlarge).le
      have hpow := Real.rpow_le_rpow hn0.le hnR hδ.le
      have he : 1 ≤ Real.exp (c * R ^ δ) * Real.exp (-c * (n : ℝ) ^ δ) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp
        nlinarith
      apply (prob_le_one (μ := ν)).trans
      apply ENNReal.one_le_ofReal.mpr
      exact he.trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left hC.le) (Real.exp_pos _).le)
  have hμν := hdom p hp hpl hph n m (by omega) η hεη
  apply (hμν (shortFineEvent p n m η κ)ᶜ).trans
  rw [Measure.smul_apply, smul_eq_mul]
  apply (mul_le_mul' le_rfl hν).trans_eq
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hz.le)]
  congr 1
  ring

/-- Internal moment conversion for the proof of Lemma 6.5:
a finite retained norm bounds its nonnegative raw moment. -/
theorem retained_raw_moment_internal {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (W : X → ℝ) (hW : Measurable W) (hW0 : ∀ x, 0 ≤ W x)
    (k : ℕ) (hk : k ≠ 0) (T : ℝ)
    (hnorm : eLpNorm W (k : ℝ≥0∞) μ ≤ ENNReal.ofReal T) :
    (∫⁻ x, ENNReal.ofReal (W x) ^ k ∂μ) ≤ ENNReal.ofReal T ^ k := by
  have he := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (p := (k : ℝ≥0))
    (show (k : ℝ≥0) ≠ 0 by exact_mod_cast hk) hW.aestronglyMeasurable
  have hw (x) : ‖W x‖ₑ = ENNReal.ofReal (W x) := Real.enorm_eq_ofReal (hW0 x)
  simp only [NNReal.coe_natCast, ENNReal.coe_natCast, ENNReal.rpow_natCast, hw] at he
  rw [← he]
  exact pow_le_pow_left' hnorm k

/-- See the proof of Lemma 6.5 and equation (6.22) of the paper,
short-range case: the literal conditional error has a stretched-exponential
first-plus-second moment. The loss and power are chosen before temperature. The physical penalty continues to use `ε`, independently of `η`. -/
theorem short_bad_remainder (s : ℝ) (hs : 1 < s) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ ε C₀ : ℝ, 0 < ε → ε ≤ η → 0 ≤ C₀ →
      ∀ (θ : PhysicalCutoff) (βlo βhi : ℝ), 0 < βlo → βlo ≤ βhi →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ (n m : ℕ), 1 ≤ n → 2 * (n + 1) ≤ n + 1 + m + 1 →
      ∀ κ : ℝ, κ₀ ≤ κ →
      (∫⁻ L, shortRemainder p n m θ ε C₀ η κ L +
        shortRemainder p n m θ ε C₀ η κ L ^ 2
        ∂lengthMeasure p n m θ ε) ≤ ENNReal.ofReal
          (C * Real.exp (-c * (n + 1 : ℝ) ^ δ)) := by
  obtain ⟨κ₀, hκ₀, ht⟩ := short_fine_event_probability s hs
  refine ⟨κ₀, hκ₀, fun η hη => ?_⟩
  obtain ⟨δ, hδ, hprob⟩ := ht η hη
  refine ⟨δ, hδ, fun ε C₀ hε hεη hC₀ θ βlo βhi hlo hle => ?_⟩
  obtain ⟨M, hM, hm⟩ := shortEnvelope_fourth_norm s hs θ ε βlo βhi hε hlo hle
  obtain ⟨D, c, hD, hc, hp⟩ := hprob ε hε hεη θ βlo βhi hlo hle
  obtain ⟨K, hK, hpoly⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := 2 * (C₀ + 2)) hδ (show c / 4 < c / 2 by linarith)
  refine ⟨(M + M ^ 2) * Real.sqrt D * (K + 1), c / 4, by positivity, by positivity, ?_⟩
  intro p hpS hpl hph n m hn hhalf κ hκ
  let μ := (activeMeasure p n m θ ε).comap
    ((↑) : AffineSimplex.chartDomain (n+1) (((n+1+m : ℕ) : ℝ)+1) → EuclideanSpace ℝ (Fin (n+1)))
  have : IsProbabilityMeasure μ := DecayShort.activeTilt_proper_probability p n.succPNat m
    (by simp; omega) θ ε true
  let W := shortEnvelope p n.succPNat m θ ε C₀
  let G := shortFineEvent p n.succPNat m η κ
  have hW : Measurable W := measurable_shortEnvelope p n.succPNat m θ ε C₀
  have hW0 (x) : 0 ≤ W x :=
    (Real.rpow_nonneg (by positivity) C₀).trans (shortEnvelope_lower p n.succPNat m θ ε C₀ x)
  let T := M * (n + 1 : ℝ) ^ (C₀ + 2)
  have hnorm : eLpNorm W 4 μ ≤ ENNReal.ofReal T := by
    simpa only [μ, W, T, activeMeasure, Nat.succPNat, PNat.mk_coe, Nat.succ_eq_add_one, Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using hm p hpS hpl hph n.succPNat m hhalf C₀
  have hfour := retained_raw_moment_internal μ W hW hW0 4 (by norm_num) T hnorm
  have htwo := retained_raw_moment_internal μ W hW hW0 2 (by norm_num) T
    ((eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (2 : ℝ≥0∞) ≤ 4)).trans hnorm)
  have hprob : μ Gᶜ ≤ ENNReal.ofReal
      (D * Real.exp (-c * (n + 1 : ℝ) ^ δ)) :=
    by simpa only [μ, G, activeMeasure, Nat.succPNat, PNat.mk_coe, Nat.succ_eq_add_one, Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using
      hp p hpS hpl hph n.succPNat m (by simp only [Nat.succPNat_coe]; omega) hhalf κ hκ
  have hbase := retained_exceptional_moments_le p n m θ ε hW.ennreal_ofReal
    (measurableSet_shortFineEvent p (by rw [hpS]; exact hs) n.succPNat m θ η κ)
  have hs₂ : (ENNReal.ofReal T ^ 2) ^ (1 / 2 : ℝ) = ENNReal.ofReal T := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hs₄ : (ENNReal.ofReal T ^ 4) ^ (1 / 2 : ℝ) = ENNReal.ofReal T ^ 2 := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hbound : (∫⁻ L, shortRemainder p n m θ ε C₀ η κ L +
      shortRemainder p n m θ ε C₀ η κ L ^ 2
        ∂lengthMeasure p n m θ ε) ≤
      (ENNReal.ofReal T + ENNReal.ofReal T ^ 2) * ENNReal.ofReal
        (D * Real.exp (-c * (n + 1 : ℝ) ^ δ)) ^ (1 / 2 : ℝ) := by
    apply hbase.trans
    apply mul_le_mul'
    · exact add_le_add ((ENNReal.rpow_le_rpow htwo (by norm_num)).trans_eq hs₂)
        ((ENNReal.rpow_le_rpow hfour (by norm_num)).trans_eq hs₄)
    · exact ENNReal.rpow_le_rpow hprob (by norm_num)
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have heq : (ENNReal.ofReal T + ENNReal.ofReal T ^ 2) * ENNReal.ofReal
      (D * Real.exp (-c * (n + 1 : ℝ) ^ δ)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal ((T + T ^ 2) * Real.sqrt D *
        Real.exp (-(c / 2) * (n + 1 : ℝ) ^ δ)) := by
    rw [← ENNReal.ofReal_pow hT0, ← ENNReal.ofReal_add hT0 (sq_nonneg _),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      ← ENNReal.ofReal_mul (by positivity), Real.mul_rpow hD.le (Real.exp_pos _).le,
      ← Real.exp_mul, ← Real.sqrt_eq_rpow]
    congr 1
    rw [show (-c * (n + 1 : ℝ) ^ δ) * (1 / 2) =
      -(c / 2) * (n + 1 : ℝ) ^ δ by ring]
    ring
  refine (hbound.trans_eq heq).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hnR : (1 : ℝ) ≤ n + 1 := by have := Nat.cast_nonneg n (α := ℝ); linarith
  have hsmall : T + T ^ 2 ≤ (M + M ^ 2) * (n + 1 : ℝ) ^ (2 * (C₀ + 2)) := by
    have ha : (n + 1 : ℝ) ^ (C₀ + 2) ≤ (n + 1 : ℝ) ^ (2 * (C₀ + 2)) :=
      Real.rpow_le_rpow_of_exponent_le hnR (by linarith)
    have hpow : T ^ 2 = M ^ 2 * (n + 1 : ℝ) ^ (2 * (C₀ + 2)) := by
      have hp : ((n + 1 : ℝ) ^ (C₀ + 2)) ^ 2 = (n + 1 : ℝ) ^ (2 * (C₀ + 2)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1
        push_cast
        ring
      dsimp only [T]
      rw [mul_pow, hp]
    rw [hpow]
    dsimp only [T]
    nlinarith [mul_le_mul_of_nonneg_left ha hM.le]
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hsmall (Real.sqrt_nonneg D))
      (Real.exp_pos (-(c / 2) * (n + 1 : ℝ) ^ δ)).le
  have habsorb := hpoly (n + 1 : ℝ) hnR
  calc
    _ ≤ (M + M ^ 2) * Real.sqrt D *
        ((n + 1 : ℝ) ^ (2 * (C₀ + 2)) *
          Real.exp (-(c / 2) * (n + 1 : ℝ) ^ δ)) := by
      nlinarith only [hh]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left habsorb
        (by positivity : 0 ≤ (M + M ^ 2) * Real.sqrt D)
      nlinarith [mul_nonneg (by positivity : 0 ≤ (M + M ^ 2) * Real.sqrt D)
        (Real.exp_pos (-(c / 4) * (n + 1 : ℝ) ^ δ)).le]


/-- See the proof of Lemma 6.5 in the paper: the actual marginal
Hessian is dominated globally by the general physical envelope. The factor `n^(-C₀)`
is retained, including away from the fine event. No cutoff of the Hessian
or omission of its conditional covariance is made. -/
theorem marginal_hessian_envelope (p : Parameters)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε C₀ : ℝ) (hε : 0 < ε) :
    let F := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      ∑ i, (θ.val (((n : ℝ) ^ ε)⁻¹ * y i) +
        θ.val (((n : ℝ) ^ ε)⁻¹ * (y i)⁻¹))
    let K := fun y => p.val.1⁻¹ * (p.val.1 * F y -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,z)).toReal))
    ∀ x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
      ‖fderiv ℝ (fderiv ℝ K) x.val‖ ≤
        (n : ℝ) ^ (2 - C₀) * shortEnvelope p n m θ ε C₀ x := by
  intro F K x
  let hn : (n : ℕ) ≤ (n : ℕ) + m + 1 := by omega
  let A := DecayShort.conditionalIntervalWeight p n m n.pos (Equiv.refl _) x
  let H := IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat
    ((n : ℕ) + m + 1) le_rfl A
  let S := Finset.univ.filter (fun a : Fin ((n : ℕ) + m + 1) => (n : ℕ) ≤ a.val)
  let P := IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat n hn A
  let c := (m + 1 : ℝ)⁻¹ ^ 2 * ∑ a ∈ S, ∑ b ∈ S, H a b
  let b := fun i : Fin (n : ℕ) => (m + 1 : ℝ)⁻¹ * ∑ a ∈ S, H (Fin.castLE hn i) a
  let B := 1 + (∑ i, |InterpolationMatrix.penaltyHessian n θ ε x.val i i|) +
    (∑ i, ∑ j, P i j) + (∑ i, b i) + c
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  obtain ⟨_, _, _, hK, _⟩ := DecayShort.PhysicalFibres.active_marginal_hessian
    p n m n.pos θ (by positivity : 0 < ((n : ℝ) ^ ε)⁻¹) true
  change ContDiffOn ℝ ∞ K _ at hK
  have hxK := hK.contDiffAt ((AffineSimplex.isOpen_chartDomain n _).mem_nhds x.property)
  let V := fun y => p.val.1 * F y - Real.log (∫ z : EuclideanSpace ℝ (Fin m),
    (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,z)).toReal)
  have hV : ContDiffAt ℝ 2 V x.val := by
    have hh := (MarginalHessian.physical_penalized_marginal_potential_smooth p n m n.pos
      (Equiv.refl _) θ (by positivity : 0 < ((n : ℝ) ^ ε)⁻¹) Finset.univ true).contDiffAt
        ((AffineSimplex.isOpen_chartDomain n _).mem_nhds x.property)
    simpa [V, F] using hh.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  obtain ⟨cCurv, hcCurv, hcurv⟩ := MarginalCollision.penalized_marginal_strict_curvature
    p n m n.pos (Equiv.refl _) θ (by positivity : 0 < ((n : ℝ) ^ ε)⁻¹) Finset.univ true
  have hpos (v) : 0 ≤ fderiv ℝ (fderiv ℝ K) x.val v v := by
    have hv : 0 ≤ fderiv ℝ (fderiv ℝ V) x.val v v := by
      simpa [V, F] using (mul_nonneg hcCurv.le (sq_nonneg ‖v‖)).trans (hcurv x.val x.property v)
    change 0 ≤ fderiv ℝ (fderiv ℝ (fun y => p.val.1⁻¹ * V y)) x.val v v
    rw [PhysicalCollision.internal_hessian_const_mul hV]
    exact mul_nonneg (inv_nonneg.mpr p.property.1.le) hv
  have hP0 (i j) : 0 ≤ P i j := by
    apply Finset.sum_nonneg
    intro t _
    apply mul_nonneg
    · exact DecayShort.conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x t
    · unfold IntervalBoundary.rankOne
      split_ifs <;> norm_num
  have hH0 (i j) : 0 ≤ H i j := by
    apply Finset.sum_nonneg
    intro t _
    apply mul_nonneg
    · exact DecayShort.conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x t
    · unfold IntervalBoundary.rankOne
      split_ifs <;> norm_num
  have hb0 : 0 ≤ ∑ i, b i := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => hH0 _ a)
  have hc0 : 0 ≤ c := mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun a _ =>
    Finset.sum_nonneg fun b _ => hH0 a b)
  have hdiag (i : Fin (n : ℕ)) :
      fderiv ℝ (fderiv ℝ K) x.val (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) ≤ B := by
    have hd := DecayShort.ExceptionalEvent.proper_hessian_diagonal_upper p n m n.pos θ ε hε true x i
    change _ ≤ fderiv ℝ (fderiv ℝ F) x.val _ _ +
      H (Fin.castLE hn i) (Fin.castLE hn i) + c at hd
    have hPi : H (Fin.castLE hn i) (Fin.castLE hn i) = P i i := by
      unfold H P IntervalBoundary.intervalMatrix IntervalBoundary.rankOne IntervalBoundary.trace
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.castLE_refl]
    rw [hPi] at hd
    change fderiv ℝ (fderiv ℝ K) x.val (EuclideanSpace.single i 1)
      (EuclideanSpace.single i 1) ≤ fderiv ℝ (fderiv ℝ F) x.val
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) + P i i + c at hd
    have hFsm : ContDiffAt ℝ 2 F x.val := by
      simpa only [F, ↓reduceIte] using DecayShort.PhysicalComparison.penalty_contDiffAt n θ
        (inv_pos.mpr (Real.rpow_pos_of_pos hn0 ε)) true x.val x.property.1
    have hFentry : InterpolationMatrix.penaltyHessian n θ ε x.val i i =
        fderiv ℝ (fderiv ℝ F) x.val (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
      simpa only [InterpolationMatrix.penaltyHessian, Real.rpow_neg hn0.le, F] using
        DecayShort.PhysicalComparison.hessianMatrix_entry hFsm i i
    have hFi := Finset.single_le_sum (s := Finset.univ)
      (fun j _ => abs_nonneg (InterpolationMatrix.penaltyHessian n θ ε x.val j j)) (Finset.mem_univ i)
    have hPiSum : P i i ≤ ∑ k, ∑ j, P k j :=
      (Finset.single_le_sum (s := Finset.univ) (fun j _ => hP0 i j) (Finset.mem_univ i)).trans
        (Finset.single_le_sum (s := Finset.univ)
          (fun k _ => Finset.sum_nonneg fun j _ => hP0 k j) (Finset.mem_univ i))
    rw [hFentry] at hFi
    dsimp only [B]
    linarith [le_abs_self (fderiv ℝ (fderiv ℝ F) x.val
      (EuclideanSpace.single i 1) (EuclideanSpace.single i 1))]
  have hnorm := DecayShort.ExceptionalEvent.norm_le_card_mul_trace
    (fderiv ℝ (fderiv ℝ K) x.val) (hxK.isSymmSndFDerivAt (by norm_num)) hpos
  have htrace : (∑ i, fderiv ℝ (fderiv ℝ K) x.val
      (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) ≤ (n : ℝ) * B := by
    calc
      _ ≤ ∑ _i : Fin (n : ℕ), B := Finset.sum_le_sum fun i _ => hdiag i
      _ = _ := by simp
  have hbound : ‖fderiv ℝ (fderiv ℝ K) x.val‖ ≤ (n : ℝ) ^ 2 * B := by
    apply hnorm.trans
    simp only [Fintype.card_fin]
    nlinarith [mul_le_mul_of_nonneg_left htrace hn0.le]
  apply hbound.trans_eq
  change (n : ℝ) ^ 2 * B = (n : ℝ) ^ (2 - C₀) * ((n : ℝ) ^ C₀ * B)
  rw [← mul_assoc, ← Real.rpow_add hn0, sub_add_cancel, Real.rpow_two]

/-- Internal coarea step of the proof of Lemma 6.5:
a retained L² function belongs to L² on almost every literal length fibre.
The exceptional null set is chosen before any test field on that fibre. -/
theorem retained_memLp_two_ae_internal (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ)
    (W : AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1) → ℝ)
    (hW : Measurable W)
    (hW2 : eLpNorm W 2 ((activeMeasure p n m θ ε).comap Subtype.val) < (∞ : ℝ≥0∞)) :
    ∀ᵐ L ∂lengthMeasure p n m θ ε, MemLp W 2 (retainedKernel p n m θ ε L) := by
  have hf : Measurable (fun x => ‖W x‖ₑ ^ (2 : ℕ)) := hW.enorm.pow_const 2
  have hglobal := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞))
    hW.aestronglyMeasurable).mp hW2
  norm_num only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at hglobal
  rw [retained_lintegral_disintegration p n m θ ε hf] at hglobal
  have hmeas : Measurable (fun L => ∫⁻ x, ‖W x‖ₑ ^ (2 : ℕ) ∂retainedKernel p n m θ ε L) := by
    simpa only [Function.comp_def] using
      (hf.comp measurable_snd).lintegral_kernel_prod_right' (κ := retainedKernel p n m θ ε)
  filter_upwards [ae_lt_top hmeas hglobal.ne] with L hL
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ (∞ : ℝ≥0∞))
    hW.aestronglyMeasurable).mpr
  simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using hL

/-- See the proof of Lemma 6.5 in the paper: the exact short envelope
belongs to L² on almost every physical length fibre, for every fixed real
envelope exponent. This conclusion precedes all choices of fibre tests. -/
theorem shortEnvelope_memLp_two_ae (p : Parameters) (hs : 1 < p.val.2)
    (n m : ℕ) (θ : PhysicalCutoff) (ε C₀ : ℝ) (hε : 0 < ε)
    (hhalf : 2 * (n + 1) ≤ n + 1 + m + 1) :
    ∀ᵐ L ∂lengthMeasure p n m θ ε,
      MemLp (shortEnvelope p n.succPNat m θ ε C₀) 2 (retainedKernel p n m θ ε L) := by
  obtain ⟨C, _, hb⟩ := shortEnvelope_fourth_norm p.val.2 hs θ ε p.val.1 p.val.1
    hε p.property.1 le_rfl
  have : IsProbabilityMeasure ((activeMeasure p n m θ ε).comap
      ((↑) : AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1) →
        EuclideanSpace ℝ (Fin (n + 1)))) :=
    DecayShort.activeTilt_proper_probability p n.succPNat m (by simp; omega) θ ε true
  apply retained_memLp_two_ae_internal p n m θ ε _
    (measurable_shortEnvelope p n.succPNat m θ ε C₀)
  apply (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (2 : ℝ≥0∞) ≤ 4)).trans_lt
  exact (hb p rfl le_rfl le_rfl n.succPNat m hhalf C₀).trans_lt ENNReal.ofReal_lt_top

/-- See the proof of Lemma 6.5 in the paper: the exact short remainder
is finite almost everywhere. Finiteness needs no event probability estimate
and holds for every fine threshold and every fixed envelope exponent. -/
theorem shortRemainder_finite_ae (p : Parameters) (hs : 1 < p.val.2)
    (n m : ℕ) (θ : PhysicalCutoff) (ε C₀ η κ : ℝ) (hε : 0 < ε)
    (hhalf : 2 * (n + 1) ≤ n + 1 + m + 1) :
    ∀ᵐ L ∂lengthMeasure p n m θ ε, shortRemainder p n m θ ε C₀ η κ L < (∞ : ℝ≥0∞) := by
  filter_upwards [shortEnvelope_memLp_two_ae p hs n m θ ε C₀ hε hhalf] with L hL
  have : IsProbabilityMeasure (retainedKernel p n m θ ε L) := inferInstance
  have hInt := hL.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hnn (x : AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1)) :
      0 ≤ shortEnvelope p n.succPNat m θ ε C₀ x :=
    (Real.rpow_nonneg (by positivity) C₀).trans (shortEnvelope_lower p n.succPNat m θ ε C₀ x)
  have hfinite := (lintegral_ofReal_ne_top_iff_integrable hInt.aestronglyMeasurable
    (ae_of_all _ hnn)).mpr hInt
  exact (lintegral_mono' Measure.restrict_le_self le_rfl).trans_lt hfinite.lt_top

/-- See the proof of Lemma 6.5 in the paper: global integrability of
every short physical Hessian pairing on almost every length fibre. The
null set is independent of the L² field to be paired with the Hessian.
In particular this justifies using the global normal equation on these
fibres, beyond the compact-test multiplier identity. -/
theorem short_global_pairings (p : Parameters) (hs : 1 < p.val.2)
    (n m : ℕ) (θ : PhysicalCutoff) (ε : ℝ) (hε : 0 < ε)
    (hhalf : 2 * (n + 1) ≤ n + 1 + m + 1) :
    let F := fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
      ∑ i, (θ.val (((n + 1 : ℝ) ^ ε)⁻¹ * y i) +
        θ.val (((n + 1 : ℝ) ^ ε)⁻¹ * (y i)⁻¹))
    let K := fun y => p.val.1⁻¹ * (p.val.1 * F y -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n + 1) m (Equiv.refl _) (y,z)).toReal))
    ∀ᵐ L ∂lengthMeasure p n m θ ε,
      ∀ i j : Fin (n + 1),
        MemLp (fun x => hessianMatrix K x.val i j) 2 (retainedKernel p n m θ ε L) ∧
        ∀ u : Lp ℝ 2 (retainedKernel p n m θ ε L),
          Integrable (fun x => p.val.1 * hessianMatrix K x.val i j * u x)
            (retainedKernel p n m θ ε L) := by
  intro F K
  obtain ⟨hK, _⟩ := DecayShort.PhysicalFibres.active_marginal_curvature p hs
    (n + 1) m (by omega) (Equiv.refl _) θ ε hε true
  have hK' : ContDiffOn ℝ ∞ K (AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1)) := by
    simpa only [K, F, Nat.cast_add, Nat.cast_one, ite_true] using hK
  filter_upwards [shortEnvelope_memLp_two_ae p hs n m θ ε 0 hε hhalf] with L hL
  intro i j
  have hm := DecayShort.PhysicalComparison.measurable_hessianMatrix
    (AffineSimplex.isOpen_chartDomain (n + 1) _) hK' i j
  have hpoint (x : AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1)) :
      ‖hessianMatrix K x.val i j‖ ≤
        (n + 1 : ℝ) ^ (2 : ℝ) * shortEnvelope p n.succPNat m θ ε 0 x := by
    have hxK := (hK'.contDiffAt ((AffineSimplex.isOpen_chartDomain (n + 1) _).mem_nhds
      x.property)).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
    rw [DecayShort.PhysicalComparison.hessianMatrix_entry hxK]
    have h₁ := (fderiv ℝ (fderiv ℝ K) x.val (EuclideanSpace.single j 1)).unit_le_opNorm
      (EuclideanSpace.single i 1)
      (show ‖EuclideanSpace.single i (1 : ℝ)‖ ≤ 1 by simp)
    have h₂ := (fderiv ℝ (fderiv ℝ K) x.val).unit_le_opNorm
      (EuclideanSpace.single j 1)
      (show ‖EuclideanSpace.single j (1 : ℝ)‖ ≤ 1 by simp)
    apply (h₁.trans h₂).trans
    simpa only [Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one, sub_zero, K, F] using
      marginal_hessian_envelope p n.succPNat m θ ε 0 hε x
  have hM : MemLp (fun x => hessianMatrix K x.val i j) 2
      (retainedKernel p n m θ ε L) :=
    (hL.const_mul ((n + 1 : ℝ) ^ (2 : ℝ))).mono' hm.aestronglyMeasurable
      (ae_of_all _ hpoint)
  refine ⟨hM, fun u => ?_⟩
  exact (hM.const_mul p.val.1).integrable_mul (Lp.memLp u)

/-- Internal physical maximum-principle step of the proof of Lemma 6.5. The Hessian and its coercivity are derived
from the actual short marginal. The scalar form and its weak solution are
the inputs for this form-level helper. The component subspace is arbitrary. -/
theorem short_solution_bound_internal (p : Parameters) (hs : 1 < p.val.2)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε : ℝ) (hε : 0 < ε)
    (ρ : Measure (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)))
    (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q) :
    let F := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      ∑ i, (θ.val (((n : ℝ) ^ ε)⁻¹ * y i) +
        θ.val (((n : ℝ) ^ ε)⁻¹ * (y i)⁻¹))
    let K := fun y => p.val.1⁻¹ * (p.val.1 * F y -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,z)).toReal))
    let M := fun x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) =>
      p.val.1 • hessianMatrix K x.val
    ∀ (S : Submodule ℝ (Fin (n : ℕ) → ℝ)) (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ρ)
      (B : ℝ), 0 ≤ B → (∀ᵐ x ∂ρ, |χ x| ≤ B) → ∀ u : Fin (n : ℕ) → Q.1,
      WeightedWeakSolution Q M S (fun i => if i = i₀ then χ else 0) u →
      ∀ j, ∀ᵐ x ∂ρ, |(u j).val x| ≤
        p.val.1⁻¹ * (n : ℝ) ^ ((p.val.2 + 2) * ε) * B := by
  intro F K M S i₀ χ B hB hχ u hu
  obtain ⟨hK, hcurv⟩ := DecayShort.PhysicalFibres.active_marginal_curvature p hs
    n m n.pos (Equiv.refl _) θ ε hε true
  change ContDiffOn ℝ ∞ K _ at hK
  let c := p.val.1 * (n : ℝ) ^ (-(p.val.2 + 2) * ε)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hc : 0 < c := by dsimp only [c]; exact mul_pos p.property.1 (Real.rpow_pos_of_pos hn0 _)
  have hm (i j) : Measurable (fun x => M x i j) :=
    (DecayShort.PhysicalComparison.measurable_hessianMatrix
      (AffineSimplex.isOpen_chartDomain n _) hK i j).const_mul _
  have hM : ∀ᵐ x ∂ρ, (∀ i j, M x i j = M x j i) ∧
      ∀ z : Fin (n : ℕ) → ℝ,
        c * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j := by
    apply ae_of_all
    intro x
    have hxK := (hK.contDiffAt ((AffineSimplex.isOpen_chartDomain n _).mem_nhds
      x.property)).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
    refine ⟨fun i j => congrArg (fun t => p.val.1 * t)
      (DecayShort.PhysicalComparison.hessianMatrix_symm hxK i j), fun z => ?_⟩
    have hh := PhysicalEnergy.hessianMatrix_quadratic hxK (WithLp.toLp 2 z)
    have hb := mul_le_mul_of_nonneg_left (hcurv x.val x.property (WithLp.toLp 2 z))
      p.property.1.le
    change p.val.1 * ((n : ℝ) ^ (-(p.val.2 + 2) * ε) * ‖WithLp.toLp 2 z‖ ^ 2) ≤
      p.val.1 * fderiv ℝ (fderiv ℝ K) x.val (WithLp.toLp 2 z) (WithLp.toLp 2 z) at hb
    rw [← hh] at hb
    simpa only [M, c, Matrix.smul_apply, smul_eq_mul, PiLp.norm_sq_eq_of_L2,
      Real.norm_eq_abs, sq_abs, ← Finset.mul_sum, mul_assoc, mul_left_comm] using hb
  have hb := (FixedLengthDecay.point_source_ae_bound_internal Q hQ M hm c hc hM
    S i₀ χ B hB hχ u hu).2
  have hcInv : c⁻¹ = p.val.1⁻¹ * (n : ℝ) ^ ((p.val.2 + 2) * ε) := by
    dsimp only [c]
    rw [mul_inv, ← Real.rpow_neg hn0.le]
    congr 2
    ring
  simpa only [hcInv] using hb

/-- Internal normal-equation bookkeeping for equation (6.24).
The global Hessian loss, maximum-principle loss, component sum and normal
division are all retained until the single condition `a + 3 ≤ C₀`.
 -/
theorem exceptional_normal_absorption_internal (n : ℕ+) (β a C₀ W B χ : ℝ)
    (hβ : 0 < β) (ha : 0 ≤ a) (hC₀ : a + 3 ≤ C₀) (hB : 0 ≤ B)
    (hW : (n : ℝ) ^ C₀ ≤ W)
    (M : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ) (u : Fin (n : ℕ) → ℝ)
    (hM : ∀ i j, |M i j| ≤ β * (n : ℝ) ^ (2 - C₀) * W)
    (hu : ∀ j, |u j| ≤ β⁻¹ * (n : ℝ) ^ a * B) (hχ : |χ| ≤ B) :
    |(n : ℝ)⁻¹ * ((∑ i, ∑ j, M i j * u j) - χ)| ≤ 2 * B * W := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hW1 : 1 ≤ W := (Real.one_le_rpow hn1 (by linarith : 0 ≤ C₀)).trans hW
  let A := β * (n : ℝ) ^ (2 - C₀) * W
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hcol (j) : (∑ i, |M i j|) ≤ (n : ℝ) * A := by
    calc
      _ ≤ ∑ _i : Fin (n : ℕ), A := Finset.sum_le_sum fun i _ => hM i j
      _ = _ := by simp
  have hnormal := normal_column_bound_internal n M u (fun _ => 0) χ ((n : ℝ) * A) 0
    (fun j => by simpa only [mul_zero, add_zero] using hcol j)
  simp only [zero_mul, Finset.sum_const_zero, add_zero] at hnormal
  have hsum : (∑ j, |u j|) ≤ (n : ℝ) * (β⁻¹ * (n : ℝ) ^ a * B) := by
    calc
      _ ≤ ∑ _j : Fin (n : ℕ), β⁻¹ * (n : ℝ) ^ a * B :=
        Finset.sum_le_sum fun j _ => hu j
      _ = _ := by simp
  have hpow : (n : ℝ) ^ (2 - C₀) * (n : ℝ) ^ a * (n : ℝ) ≤ 1 := by
    calc
      _ = (n : ℝ) ^ ((2 - C₀) + a + 1) := by
        rw [Real.rpow_add hn0, Real.rpow_add hn0, Real.rpow_one]
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  have hcancel : (n : ℝ)⁻¹ * ((n : ℝ) * A *
        ((n : ℝ) * (β⁻¹ * (n : ℝ) ^ a * B))) =
      ((n : ℝ) ^ (2 - C₀) * (n : ℝ) ^ a * (n : ℝ)) * B * W := by
    dsimp only [A]
    field_simp
  have hmatrix : (n : ℝ)⁻¹ * ((n : ℝ) * A * (∑ j, |u j|)) ≤ B * W := by
    calc
      _ ≤ (n : ℝ)⁻¹ * ((n : ℝ) * A * ((n : ℝ) * (β⁻¹ * (n : ℝ) ^ a * B))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (by positivity)) (by positivity)
      _ = _ := hcancel
      _ ≤ B * W := by nlinarith [mul_le_mul_of_nonneg_right hpow (by positivity : 0 ≤ B * W)]
  have hsource : (n : ℝ)⁻¹ * |χ| ≤ B * W := by
    calc
      _ ≤ (n : ℝ)⁻¹ * B := mul_le_mul_of_nonneg_left hχ (by positivity)
      _ ≤ B := mul_le_of_le_one_left hB (inv_le_one_of_one_le₀ hn1)
      _ ≤ B * W := le_mul_of_one_le_right hB hW1
  exact hnormal.trans (by nlinarith only [hmatrix, hsource])

/-- Internal short-range exceptional part of equation (6.24).
The maximum principle and global normal-pairing integrability are proved
for the actual marginal Hessian. Any `C₀ ≥ s + 5` absorbs these exceptional
losses when `ε ≤ 1`. -/
theorem short_exceptional_multiplier_internal (p : Parameters) (hs : 1 < p.val.2)
    (n m : ℕ) (θ : PhysicalCutoff) (ε C₀ η κ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hC₀ : p.val.2 + 5 ≤ C₀) (hhalf : 2 * (n + 1) ≤ n + 1 + m + 1) :
    let F := fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
      ∑ i, (θ.val (((n + 1 : ℝ) ^ ε)⁻¹ * y i) +
        θ.val (((n + 1 : ℝ) ^ ε)⁻¹ * (y i)⁻¹))
    let K := fun y => p.val.1⁻¹ * (p.val.1 * F y -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n + 1) m (Equiv.refl _) (y,z)).toReal))
    let M := fun x : AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1) =>
      p.val.1 • hessianMatrix K x.val
    ∀ᵐ L ∂lengthMeasure p n m θ ε,
      let ρ := retainedKernel p n m θ ε L
      ∀ (Q : ScalarFormData ρ), IsClosedScalarDirichletForm Q →
      ∀ (S : Submodule ℝ (Fin (n + 1) → ℝ)) (i₀ : Fin (n + 1)) (χ : Lp ℝ 2 ρ)
        (B : ℝ), 0 ≤ B → (∀ᵐ x ∂ρ, |χ x| ≤ B) → ∀ u : Fin (n + 1) → Q.1,
        WeightedWeakSolution Q M S (fun i => if i = i₀ then χ else 0) u →
        let Λ := gapMultiplierField n.succPNat Q M (fun i => if i = i₀ then χ else 0) u
        shortRemainder p n m θ ε C₀ η κ L < (∞ : ℝ≥0∞) ∧
        Integrable Λ ρ ∧
        |∫ x in (shortFineEvent p n.succPNat m η κ)ᶜ, Λ x ∂ρ| ≤
          2 * B * (shortRemainder p n m θ ε C₀ η κ L).toReal := by
  intro F K M
  obtain ⟨hK, _⟩ := DecayShort.PhysicalFibres.active_marginal_curvature p hs
    (n + 1) m (by omega) (Equiv.refl _) θ ε hε true
  have hK' : ContDiffOn ℝ ∞ K (AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1)) := by
    simpa only [K, F, Nat.cast_add, Nat.cast_one, ite_true] using hK
  filter_upwards [shortEnvelope_memLp_two_ae p hs n m θ ε C₀ hε hhalf,
    shortRemainder_finite_ae p hs n m θ ε C₀ η κ hε hhalf,
    short_global_pairings p hs n m θ ε hε hhalf] with L hW2 hfin hpairs
  intro ρ Q hQ S i₀ χ B hB hχ u hu Λ
  have hpair (i j) : Integrable (fun x => M x i j * (u j).val x) ρ := (hpairs i j).2 (u j).val
  have hΛ : Integrable Λ ρ :=
    (multiplier_mean_internal n.succPNat Q M (fun i => if i = i₀ then χ else 0) u hpair).1
  have huB : ∀ j, ∀ᵐ x ∂ρ, |(u j).val x| ≤
      p.val.1⁻¹ * (n + 1 : ℝ) ^ ((p.val.2 + 2) * ε) * B := by
    simpa only [Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one, F, K, M] using
      short_solution_bound_internal p hs n.succPNat m θ ε hε ρ Q hQ S i₀ χ B hB hχ u
        (by simpa only [Nat.succPNat_coe, Nat.cast_succ, M, K, F] using hu)
  let W := shortEnvelope p n.succPNat m θ ε C₀
  have hW0 (x) : 0 ≤ W x :=
    (Real.rpow_nonneg (by positivity) C₀).trans (shortEnvelope_lower p n.succPNat m θ ε C₀ x)
  have hentry (x : AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1)) (i j) :
      |M x i j| ≤ p.val.1 * (n + 1 : ℝ) ^ (2 - C₀) * W x := by
    have hxK := (hK'.contDiffAt ((AffineSimplex.isOpen_chartDomain (n + 1) _).mem_nhds
      x.property)).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
    have h₁ := (fderiv ℝ (fderiv ℝ K) x.val (EuclideanSpace.single j 1)).unit_le_opNorm
      (EuclideanSpace.single i 1) (show ‖EuclideanSpace.single i (1 : ℝ)‖ ≤ 1 by simp)
    have h₂ := (fderiv ℝ (fderiv ℝ K) x.val).unit_le_opNorm
      (EuclideanSpace.single j 1) (show ‖EuclideanSpace.single j (1 : ℝ)‖ ≤ 1 by simp)
    have hh : |hessianMatrix K x.val i j| ≤ (n + 1 : ℝ) ^ (2 - C₀) * W x := by
      rw [DecayShort.PhysicalComparison.hessianMatrix_entry hxK]
      apply (h₁.trans h₂).trans
      simpa only [Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one, K, F, W] using
        marginal_hessian_envelope p n.succPNat m θ ε C₀ hε x
    change |p.val.1 * hessianMatrix K x.val i j| ≤ _
    rw [abs_mul, abs_of_pos p.property.1]
    exact (mul_le_mul_of_nonneg_left hh p.property.1.le).trans_eq (by ring)
  have hbound : ∀ᵐ x ∂ρ, |Λ x| ≤ 2 * B * W x := by
    filter_upwards [ae_all_iff.mpr huB, hχ, Lp.coeFn_zero ℝ 2 ρ] with x hx hχx hz
    have hv : (∑ i, (if i = i₀ then χ else 0 : Lp ℝ 2 ρ) x) = χ x := by
      simp only [apply_ite (fun f : Lp ℝ 2 ρ => f x), hz, Pi.zero_apply,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    change |(n.succPNat : ℝ)⁻¹ * ((∑ i, ∑ j, M x i j * (u j).val x) -
      ∑ i, (if i = i₀ then χ else 0 : Lp ℝ 2 ρ) x)| ≤ _
    rw [hv]
    apply exceptional_normal_absorption_internal n.succPNat p.val.1
      ((p.val.2 + 2) * ε) C₀ (W x) B (χ x) p.property.1 (by positivity)
      (by nlinarith [mul_le_mul_of_nonneg_left hε1 (by linarith : 0 ≤ p.val.2 + 2)]) hB
      (shortEnvelope_lower p n.succPNat m θ ε C₀ x) (M x) (fun j => (u j).val x)
    · simpa only [Nat.succPNat_coe, Nat.cast_succ] using hentry x
    · simpa only [Nat.succPNat_coe, Nat.cast_succ] using hx
    · exact hχx
  let G := shortFineEvent p n.succPNat m η κ
  have hIW : Integrable W (ρ.restrict Gᶜ) :=
    (hW2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).mono_measure Measure.restrict_le_self
  have he : (∫ x in Gᶜ, W x ∂ρ) = (shortRemainder p n m θ ε C₀ η κ L).toReal :=
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hW0) hIW.aestronglyMeasurable
  refine ⟨hfin, hΛ, ?_⟩
  have hi := norm_integral_le_of_norm_le (f := Λ) (μ := ρ.restrict Gᶜ) (hIW.const_mul (2 * B))
    (ae_restrict_of_ae (hbound.mono fun x hx => by simpa only [Real.norm_eq_abs] using hx))
  rw [integral_const_mul, he, Real.norm_eq_abs] at hi
  exact hi

/-- Internal bridge of the proof of Lemma 6.5:
changing the active penalty exponent changes only the active diagonal
Hessian. The conditional score covariance and compensation terms remain
exactly the same. Both exponents are allowed on their whole real carrier. -/
theorem marginal_penalty_difference_internal (p : Parameters) (n : ℕ+) (m : ℕ)
    (θ : PhysicalCutoff) (ε η : ℝ) :
    let F := fun (h : ℝ) (y : EuclideanSpace ℝ (Fin (n : ℕ))) =>
      ∑ i, (θ.val (((n : ℝ) ^ h)⁻¹ * y i) +
        θ.val (((n : ℝ) ^ h)⁻¹ * (y i)⁻¹))
    let K := fun h y => p.val.1⁻¹ * (p.val.1 * F h y -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,z)).toReal))
    ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (i j),
      hessianMatrix (K ε) x.val i j - hessianMatrix (F ε) x.val i j =
        hessianMatrix (K η) x.val i j - hessianMatrix (F η) x.val i j := by
  intro F K x i j
  let V := fun y => p.val.1⁻¹ * -Real.log (∫ z : EuclideanSpace ℝ (Fin m),
    (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,z)).toReal)
  have hV : ContDiffAt ℝ 2 V x.val := by
    apply (contDiffAt_const.mul
      ((MarginalHessian.physical_marginal_potential_smooth p n m n.pos (Equiv.refl _)).contDiffAt
        ((AffineSimplex.isOpen_chartDomain n _).mem_nhds x.property))).of_le
    norm_num
  have he (h : ℝ) : K h = fun y => F h y + V y := by
    funext y
    dsimp only [K, V]
    field_simp [p.property.1.ne']
    ring
  have hh (h : ℝ) : hessianMatrix (K h) x.val i j - hessianMatrix (F h) x.val i j =
      fderiv ℝ (fderiv ℝ V) x.val (EuclideanSpace.single j 1) (EuclideanSpace.single i 1) := by
    have hF : ContDiffAt ℝ 2 (F h) x.val := by
      simpa only [F, ite_true] using DecayShort.PhysicalComparison.penalty_contDiffAt n θ
        (by positivity : 0 < ((n : ℝ) ^ h)⁻¹) true x.val x.property.1
    rw [he h, DecayShort.PhysicalComparison.hessianMatrix_entry (hF.add hV),
      DecayShort.PhysicalComparison.hessianMatrix_entry hF,
      PhysicalCollision.internal_hessian_add hF hV]
    ring
  exact (hh ε).trans (hh η).symm

/-- See the proof of Lemma 6.5 in the paper: the physical penalty at
`ε` has the required fine-event diagonal bound at the independent tolerance
`η`. Only the inverse-gap cutoff is used. No rigidity interval is assumed. -/
theorem penalty_fine_bound (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ+) (ε η : ℝ), 0 ≤ ε → 0 ≤ η →
      ∀ x : EuclideanSpace ℝ (Fin (n : ℕ)), (∀ i, (n : ℝ) ^ (-η) ≤ x i) →
      ∀ i j, |InterpolationMatrix.penaltyHessian n θ ε x i j| ≤
        if i = j then C * (n : ℝ) ^ (4 * η) else 0 := by
  obtain ⟨C, hC, hb⟩ := InterpolationCoercivity.forcing_entry_bound θ
  refine ⟨C, hC, ?_⟩
  intro n ε η hε hη x hx i j
  rcases n with ⟨n, hn⟩
  cases n with
  | zero => omega
  | succ a =>
      simpa only [InterpolationMatrix.penaltyHessian, PNat.mk_coe, Nat.cast_add, Nat.cast_one] using
        hb a ε η hε hη x
          (by simpa only [PNat.mk_coe, Nat.cast_add, Nat.cast_one] using hx) i j

/-- See the proof of Lemma 6.5 in the paper, short column calculation
before absorbing the two scalar sums. This is the physical Hessian on the
exact fine event with the separate physical penalty `ε`. All score and
exterior profiles, including the constant lower-order terms, are retained.
The first prefactor depends only on the cutoff, the second on `p`. -/
theorem short_fine_hessian_columns (p : Parameters) (hs : 1 < p.val.2)
    (θ : PhysicalCutoff) :
    ∃ Cp Cr : ℝ, 0 < Cp ∧ 0 < Cr ∧ ∀ (n : ℕ+) (m : ℕ),
      4 ≤ (n : ℕ) + m + 1 → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ ε η κ : ℝ, 0 ≤ ε → 0 < η →
      let F := fun (h : ℝ) (y : EuclideanSpace ℝ (Fin (n : ℕ))) =>
        ∑ i, (θ.val (((n : ℝ) ^ h)⁻¹ * y i) +
          θ.val (((n : ℝ) ^ h)⁻¹ * (y i)⁻¹))
      let K := fun h y => p.val.1⁻¹ * (p.val.1 * F h y -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,z)).toReal))
      ∀ x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
        x ∈ shortFineEvent p n m η κ → ∀ j,
        let D := (n : ℝ) ^ (κ * η)
        let N : ℝ := ((n : ℕ) + m + 1 : ℕ)
        let w := DecayShort.ConditionalScores.weight p.val.2 (n := (n : ℕ))
        let S := ∑ i, w i
        (∑ i, |hessianMatrix (K ε) x.val i j|) ≤
          Cp * (n : ℝ) ^ (4 * η) +
            D * (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-p.val.2)) +
            3 * D * (n : ℝ) / N + p.val.1 * Cr * D *
              ((S + (n : ℝ) * N ^ (-(1 / 2 : ℝ))) * w j +
                N ^ (-(1 / 2 : ℝ)) * S + (n : ℝ) / N) := by
  obtain ⟨Cp, hCp, hpen⟩ := penalty_fine_bound θ
  obtain ⟨Cr, hCr, hres⟩ := DecayShort.PhysicalComparison.frozen_difference_entry_bound p hs
  refine ⟨Cp, Cr, hCp, hCr, ?_⟩
  intro n m hN hhalf ε η κ hε hη F K x hx j D N w S
  let hn : (n : ℕ) ≤ (n : ℕ) + m + 1 := by omega
  let A := DecayShort.conditionalIntervalWeight p n m n.pos (Equiv.refl _) x
  let P := IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat n hn A
  let I := IntervalBoundary.internalMatrix ((n : ℕ) + m).succPNat n hn A
  let E := IntervalBoundary.boundaryMatrix ((n : ℕ) + m).succPNat n hn A
  have hD : 0 ≤ D := Real.rpow_nonneg (by positivity) _
  have hx' : x ∈ DecayShort.ExceptionalEvent.properGoodEvent p n m hn η D := hx
  have hdecomp := IntervalBoundary.internal_add_boundary ((n : ℕ) + m).succPNat n hn A
  have hP0 (i k) : 0 ≤ P i k := IntervalBoundary.intervalMatrix_nonneg
    ((n : ℕ) + m).succPNat n hn A
    (DecayShort.conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x) i k
  have hresid (i) : |hessianMatrix (K ε) x.val i j - hessianMatrix (F ε) x.val i j - P i j| ≤
      3 * D / N + p.val.1 * Cr * D *
        (w i * w j + N ^ (-(1 / 2 : ℝ)) * (w i + w j) + N⁻¹) := by
    have hb := (hres n m hN hhalf θ η true D hD x i j).1
    rw [ite_eq_left hx'] at hb
    change |(DecayShort.PhysicalComparison.frozenPhysicalMatrix p n m θ η true D x -
      DecayShort.PhysicalComparison.frozenInternalMatrix p n m θ η true D x) i j - E i j| ≤ _ at hb
    have hchange := marginal_penalty_difference_internal p n m θ ε η x i j
    change hessianMatrix (K ε) x.val i j - hessianMatrix (F ε) x.val i j =
      hessianMatrix (K η) x.val i j - hessianMatrix (F η) x.val i j at hchange
    rw [hchange]
    have hPi : P i j = I i j + E i j := congrArg (fun M => M i j) hdecomp.symm
    unfold DecayShort.PhysicalComparison.frozenPhysicalMatrix
      DecayShort.PhysicalComparison.frozenInternalMatrix at hb
    simp only [ite_eq_left hx', Matrix.sub_apply, Matrix.add_apply, ite_true] at hb
    change |(hessianMatrix (K η) x.val i j - (hessianMatrix (F η) x.val i j + I i j)) - E i j| ≤ _ at hb
    convert hb using 1
    congr 1
    rw [hPi]
    ring
  have hentry (i) : |hessianMatrix (K ε) x.val i j| ≤
      |hessianMatrix (F ε) x.val i j| + P i j +
      (3 * D / N + p.val.1 * Cr * D *
        (w i * w j + N ^ (-(1 / 2 : ℝ)) * (w i + w j) + N⁻¹)) := by
    have hb := hresid i
    have ht := abs_add_le (hessianMatrix (K ε) x.val i j - hessianMatrix (F ε) x.val i j - P i j)
      (hessianMatrix (F ε) x.val i j + P i j)
    rw [show (hessianMatrix (K ε) x.val i j - hessianMatrix (F ε) x.val i j - P i j) +
      (hessianMatrix (F ε) x.val i j + P i j) = hessianMatrix (K ε) x.val i j by ring] at ht
    have hf := abs_add_le (hessianMatrix (F ε) x.val i j) (P i j)
    rw [abs_of_nonneg (hP0 i j)] at hf
    linarith
  have hFsum : (∑ i, |hessianMatrix (F ε) x.val i j|) ≤ Cp * (n : ℝ) ^ (4 * η) := by
    have hb (i) := hpen n ε η hε hη.le x.val (fun k => (hx.1.2.1 k).1) i j
    have he : (fun y => ∑ i, (θ.val (((n : ℝ) ^ ε)⁻¹ * y i) +
        θ.val (((n : ℝ) ^ ε)⁻¹ * (y i)⁻¹))) = F ε := rfl
    simp only [InterpolationMatrix.penaltyHessian, Real.rpow_neg (by positivity : (0 : ℝ) ≤ n), he] at hb
    exact (Finset.sum_le_sum fun i _ => hb i).trans_eq (by simp)
  have hPsum := (DecayShort.PhysicalComparison.complete_schur_bounds p hs n m D hD x hx.2).2 j
  apply (Finset.sum_le_sum fun i _ => hentry i).trans
  simp only [Finset.sum_add_distrib]
  have he : (∑ i : Fin (n : ℕ), (3 * D / N + p.val.1 * Cr * D *
        (w i * w j + N ^ (-(1 / 2 : ℝ)) * (w i + w j) + N⁻¹))) =
      3 * D * (n : ℝ) / N + p.val.1 * Cr * D *
        ((S + (n : ℝ) * N ^ (-(1 / 2 : ℝ))) * w j + N ^ (-(1 / 2 : ℝ)) * S + (n : ℝ) / N) := by
    simp only [S, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum, ← Finset.sum_mul, div_eq_mul_inv]
    ring
  simp only [Finset.sum_add_distrib] at he
  rw [he]
  linarith

/-- See Subsection 6.3 of the paper: the general physical conditional interval
coefficient agrees with the long-range coefficient on its complete positive
retained carrier. The physical exterior probability and antipodal factor
are preserved. -/
theorem long_interval_coefficient_bridge (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (a : Fin ((n : ℕ) + m + 1)) (r : Fin (((n : ℕ) + m + 1) / 2)) :
    DecayShort.conditionalIntervalWeight (ofLong β s) n m n.pos (Equiv.refl _) x (a,r) =
      BoundaryEntries.conditionalIntervalWeight β s n m r a x := by
  let g := fun z : EuclideanSpace ℝ (Fin m) => BoundaryEntries.intervalWeight s
    ((n : ℕ) + m).succPNat r a
      (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z))
  have hg : Measurable g := (BoundaryEntries.measurable_intervalWeight s ((n : ℕ) + m).succPNat r a).comp
    ((RetainedSimplex.continuous_chart n m _ (Equiv.refl _)).measurable.comp
      (measurable_const.prodMk measurable_id))
  unfold DecayShort.conditionalIntervalWeight BoundaryEntries.conditionalIntervalWeight
  change _ = ∫ z, g z ∂ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x
  rw [← DecayShort.PhysicalFibres.map_measure (ofLong β s) n m n.pos (Equiv.refl _) x,
    integral_map measurable_subtype_coe.aemeasurable hg.aestronglyMeasurable]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  simpa only [DecayShort.intervalWeight, g, DecayShort.PhysicalFibres.configuration] using
    (BoundaryEntries.intervalWeight_physical β s ((n : ℕ) + m).succPNat r a
      (DecayShort.PhysicalFibres.configuration n m (Equiv.refl _) x z).val
      (DecayShort.PhysicalFibres.configuration_mem_simplex n m (Equiv.refl _) x z)).symm

/-- See Subsection 6.3 of the paper: the long-range `P_I` is exactly the complete
conditional interval matrix, with its inherited ambient labels. -/
theorem long_conditional_hessian_bridge (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (i j : Fin (n : ℕ)) :
    GoodBlocks.conditionalHessian β s n m i j x =
      IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat n (by simp; omega)
        (DecayShort.conditionalIntervalWeight (ofLong β s) n m n.pos (Equiv.refl _) x) i j := by
  rw [BoundaryEntries.conditionalHessian_intervalWeight]
  unfold IntervalBoundary.intervalMatrix
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro a _
  rw [long_interval_coefficient_bridge]
  unfold IntervalBoundary.rankOne IntervalBoundary.trace
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hi : Fin.castLE (show (n : ℕ) ≤ (n : ℕ) + m + 1 by omega) i = (i.castAdd m).castSucc :=
    Fin.ext rfl
  have hj : Fin.castLE (show (n : ℕ) ≤ (n : ℕ) + m + 1 by omega) j = (j.castAdd m).castSucc :=
    Fin.ext rfl
  rw [hi, hj]
  split_ifs <;> ring

/-- See Subsection 6.3 of the paper: every ambient conditional Hessian entry is
the existing general interval matrix. The proof uses finite integrals of
the original long-range interval coefficients, without changing carriers. -/
theorem long_ambient_conditional_bridge (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (a b : Fin ((n : ℕ) + m + 1)) :
    (∫ z, GoodBlocks.chartHessian s n m a b (x.val,z)
      ∂ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x) =
      IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat ((n : ℕ) + m + 1) le_rfl
        (DecayShort.conditionalIntervalWeight (ofLong β s) n m n.pos (Equiv.refl _) x) a b := by
  let c := fun (r : Fin (((n : ℕ) + m + 1) / 2)) (i : Fin ((n : ℕ) + m + 1)) =>
    if a ∈ cyclicIndexInterval ((n : ℕ) + m).succPNat i (r.val + 1) ∧
      b ∈ cyclicIndexInterval ((n : ℕ) + m).succPNat i (r.val + 1) then (1 : ℝ) else 0
  have he : (fun z => GoodBlocks.chartHessian s n m a b (x.val,z)) = fun z =>
      ∑ r, ∑ i, BoundaryEntries.intervalWeight s ((n : ℕ) + m).succPNat r i
        (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) * c r i := by
    funext z
    simp only [GoodBlocks.chartHessian, BoundaryEntries.gapHessian_intervalWeight, c,
      mul_ite, mul_one, mul_zero]
  rw [he, (ConditionalForces.integral_interval_sum_internal β s n m x c).2]
  unfold IntervalBoundary.intervalMatrix
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  rw [long_interval_coefficient_bridge]
  simp only [c, IntervalBoundary.rankOne, IntervalBoundary.trace, Finset.mem_filter,
    Finset.mem_univ, true_and, Fin.castLE_refl]

/-- See Subsection 6.3 of the paper: the long compensation row is the exact
exterior contraction in the general envelope. -/
theorem long_compensationB_bridge (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (i : Fin (n : ℕ)) :
    let H := IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat
        ((n : ℕ) + m + 1) le_rfl
          (DecayShort.conditionalIntervalWeight (ofLong β s) n m n.pos (Equiv.refl _) x)
    ConditionalForces.compensationB β s n m i x =
      (m + 1 : ℝ)⁻¹ * ∑ a ∈ Finset.univ.filter
        (fun a : Fin ((n : ℕ) + m + 1) => (n : ℕ) ≤ a.val), H (i.castAdd m).castSucc a := by
  intro H
  rw [ConditionalForces.compensationB, integral_finsetSum _ (fun a _ =>
    (GoodBlocks.integrable_chartHessian β s n m n.pos x (i.castAdd m).castSucc a).mul_const _)]
  simp_rw [integral_mul_const, long_ambient_conditional_bridge]
  simp only [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  unfold ConditionalForces.compensationVector
  split_ifs <;> first | omega | ring

/-- See Subsection 6.3 of the paper: the long compensation scalar is the exact
double exterior contraction in the general envelope. -/
theorem long_compensationC_bridge (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    let H := IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat
        ((n : ℕ) + m + 1) le_rfl
          (DecayShort.conditionalIntervalWeight (ofLong β s) n m n.pos (Equiv.refl _) x)
    let S := Finset.univ.filter (fun a : Fin ((n : ℕ) + m + 1) => (n : ℕ) ≤ a.val)
    ConditionalForces.compensationC β s n m x =
      (m + 1 : ℝ)⁻¹ ^ 2 * ∑ a ∈ S, ∑ b ∈ S, H a b := by
  intro H S
  have hi (a b) := ((GoodBlocks.integrable_chartHessian β s n m n.pos x a b).const_mul
    (ConditionalForces.compensationVector n m a)).mul_const (ConditionalForces.compensationVector n m b)
  rw [ConditionalForces.compensationC, integral_finsetSum _
    (fun a _ => integrable_finsetSum _ (fun b _ => hi a b))]
  simp_rw [integral_finsetSum _ (fun b _ => hi _ b), integral_mul_const, integral_const_mul,
    long_ambient_conditional_bridge]
  simp only [S, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : (n : ℕ) ≤ a.val
  · rw [ite_eq_left ha, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    unfold ConditionalForces.compensationVector
    split_ifs <;> first | omega | ring
  · rw [ite_eq_right ha, mul_zero]
    apply Finset.sum_eq_zero
    intro b _
    simp only [ConditionalForces.compensationVector, ite_eq_left (lt_of_not_ge ha), zero_mul]

/-- See Subsection 6.3 of the paper: the two existing envelope formulas coincide
in the long regime. This is a proved identification of their coefficients,
including both compensation contractions and the actual two-sided penalty. -/
theorem longEnvelope_eq_shortEnvelope (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε C₀ : ℝ)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    longEnvelope β s n m θ ε C₀ x = shortEnvelope (ofLong β s) n m θ ε C₀ x := by
  simp only [longEnvelope, shortEnvelope, long_conditional_hessian_bridge,
    long_compensationB_bridge, long_compensationC_bridge]
  rfl

/-- See the proof of Lemma 6.5 in the paper: the exact long envelope is
L² on almost every physical length fibre. -/
theorem longEnvelope_memLp_two_ae (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n m : ℕ) (θ : PhysicalCutoff) (ε C₀ : ℝ) (hε : 0 < ε)
    (hhalf : 2 * (n + 1) ≤ n + 1 + m + 1) :
    ∀ᵐ L ∂lengthMeasure (ofLong β s) n m θ ε,
      MemLp (longEnvelope β s n.succPNat m θ ε C₀) 2
        (retainedKernel (ofLong β s) n m θ ε L) := by
  obtain ⟨C, _, hb⟩ := longEnvelope_fourth_norm s θ ε β.val β.val hε β.property le_rfl
  have : IsProbabilityMeasure ((activeMeasure (ofLong β s) n m θ ε).comap
      ((↑) : AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1) →
        EuclideanSpace ℝ (Fin (n + 1)))) :=
    DecayShort.activeTilt_proper_probability _ n.succPNat m (by simp; omega) θ ε true
  apply retained_memLp_two_ae_internal (ofLong β s) n m θ ε _
    (measurable_longEnvelope β s n.succPNat m θ ε C₀)
  apply (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (2 : ℝ≥0∞) ≤ 4)).trans_lt
  exact (hb β ⟨le_rfl, le_rfl⟩ n.succPNat m hhalf C₀).trans_lt ENNReal.ofReal_lt_top

/-- See the proof of Lemma 6.5 in the paper: global integrability of
every long physical Hessian pairing on almost every length fibre. The null
set precedes the choice of the L² field. Conditional covariance is retained
through the exact physical-envelope identification. -/
theorem long_global_pairings (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n m : ℕ) (θ : PhysicalCutoff) (ε : ℝ) (hε : 0 < ε)
    (hhalf : 2 * (n + 1) ≤ n + 1 + m + 1) :
    let p := ofLong β s
    let F := fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
      ∑ i, (θ.val (((n + 1 : ℝ) ^ ε)⁻¹ * y i) +
        θ.val (((n + 1 : ℝ) ^ ε)⁻¹ * (y i)⁻¹))
    let K := fun y => p.val.1⁻¹ * (p.val.1 * F y -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n + 1) m (Equiv.refl _) (y,z)).toReal))
    ∀ᵐ L ∂lengthMeasure p n m θ ε,
      ∀ i j : Fin (n + 1),
        MemLp (fun x => hessianMatrix K x.val i j) 2 (retainedKernel p n m θ ε L) ∧
        ∀ u : Lp ℝ 2 (retainedKernel p n m θ ε L),
          Integrable (fun x => p.val.1 * hessianMatrix K x.val i j * u x)
            (retainedKernel p n m θ ε L) := by
  intro p F K
  obtain ⟨_, _, _, hK, _⟩ := DecayShort.PhysicalFibres.active_marginal_hessian p
    (n + 1) m (by omega) θ (by positivity : 0 < ((n + 1 : ℝ) ^ ε)⁻¹) true
  have hK' : ContDiffOn ℝ ∞ K (AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1)) := by
    simpa only [K, F, ite_true] using hK
  filter_upwards [longEnvelope_memLp_two_ae β s n m θ ε 0 hε hhalf] with L hL
  intro i j
  have hm := DecayShort.PhysicalComparison.measurable_hessianMatrix
    (AffineSimplex.isOpen_chartDomain (n + 1) _) hK' i j
  have hpoint (x : AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1)) :
      ‖hessianMatrix K x.val i j‖ ≤
        (n + 1 : ℝ) ^ (2 : ℝ) * longEnvelope β s n.succPNat m θ ε 0 x := by
    have hxK := (hK'.contDiffAt ((AffineSimplex.isOpen_chartDomain (n + 1) _).mem_nhds
      x.property)).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
    rw [DecayShort.PhysicalComparison.hessianMatrix_entry hxK]
    have h₁ := (fderiv ℝ (fderiv ℝ K) x.val (EuclideanSpace.single j 1)).unit_le_opNorm
      (EuclideanSpace.single i 1) (show ‖EuclideanSpace.single i (1 : ℝ)‖ ≤ 1 by simp)
    have h₂ := (fderiv ℝ (fderiv ℝ K) x.val).unit_le_opNorm
      (EuclideanSpace.single j 1) (show ‖EuclideanSpace.single j (1 : ℝ)‖ ≤ 1 by simp)
    apply (h₁.trans h₂).trans
    rw [longEnvelope_eq_shortEnvelope]
    simpa only [Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one, sub_zero, K, F] using
      marginal_hessian_envelope p n.succPNat m θ ε 0 hε x
  have hM : MemLp (fun x => hessianMatrix K x.val i j) 2
      (retainedKernel p n m θ ε L) :=
    (hL.const_mul ((n + 1 : ℝ) ^ (2 : ℝ))).mono' hm.aestronglyMeasurable (ae_of_all _ hpoint)
  exact ⟨hM, fun u => (hM.const_mul p.val.1).integrable_mul (Lp.memLp u)⟩

end Riesz2.LengthAveragingFibres
