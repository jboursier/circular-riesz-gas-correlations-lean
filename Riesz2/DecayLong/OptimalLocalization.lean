/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.ReferenceComparisonPart2

/-!
# Analytic support for the constrained localization improvement

Finite superposition and near/far summation estimates in the proof of
Proposition 5.15. These composition lemmas take point-source estimates
as inputs.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Finset
open scoped BigOperators Classical Fin.NatCast

namespace Riesz2.OptimalLocalization

/-- Finite superposition in the proof of Proposition 5.15,
retaining separate value and gradient exponents. Every weak solution has the
same estimates, by coercive uniqueness on the form domain. -/
theorem superposition_internal {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (s : Riesz1.RieszExponent) (n m : ℕ+) (hm : 2 ≤ (m : ℕ))
    (K : ℕ) (C κ γ ε β : ℝ) (hC : 1 ≤ C) (hβ : 0 < β)
    (M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M)
    (A G B : ℝ)
    (hp : ∀ (χ : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ)),
      ∃ u : Fin (m : ℕ) → Q.1,
        WeightedWeakSolution Q (fun x => β • M x) ⊤
          (fun i => if i = i₀ then χ else 0) u ∧
        ∀ j, ‖(u j).val‖ ≤ B * weightRadius m j i₀ ^ (-A) * ‖χ‖ ∧
          Real.sqrt (Q.2 (u j) (u j)) ≤ B * weightRadius m j i₀ ^ (-G) * ‖χ‖)
    (f : Fin (m : ℕ) → Lp ℝ 2 ν) :
    (∃! u : Fin (m : ℕ) → Q.1,
      WeightedWeakSolution Q (fun x => β • M x) ⊤ f u) ∧
    ∀ u : Fin (m : ℕ) → Q.1,
      WeightedWeakSolution Q (fun x => β • M x) ⊤ f u →
      ∀ j, ‖(u j).val‖ ≤ B * ∑ i, weightRadius m j i ^ (-A) * ‖f i‖ ∧
        Real.sqrt (Q.2 (u j) (u j)) ≤ B * ∑ i, weightRadius m j i ^ (-G) * ‖f i‖ := by
  choose v hv hb using fun i => hp (f i) i
  let z := fun j => ∑ i, v i j
  have hz : WeightedWeakSolution Q (fun x => β • M x) ⊤ f z := by
    simpa only [Finset.sum_ite_eq, Finset.mem_univ, ite_true] using
      LocalizedBoundary.weak_sum_internal Q (fun x => β • M x)
        (SchurRestriction.periodized_scaled_measurable β hM)
        (SchurRestriction.periodized_scaled_bounded β hM)
        (fun i j => if j = i then f i else 0) v hv
  have he := (AbstractEquation.existence_energy Q hQ β hβ M hM.1 _
    (SchurRestriction.periodized_mass_pos hC)
    (hM.2.1.mono fun _ hx => ⟨hx.1, hx.2.2.1⟩) ⊤ f).1
  refine ⟨he, fun u hu j => ?_⟩
  rw [he.unique hu hz]
  constructor
  · calc
      ‖(z j).val‖ ≤ ∑ i, ‖(v i j).val‖ := by
        simpa only [z, Submodule.coe_sum] using norm_sum_le univ (fun i => (v i j).val)
      _ ≤ ∑ i, B * weightRadius m j i ^ (-A) * ‖f i‖ := sum_le_sum fun i _ => (hb i j).1
      _ = _ := by simp only [mul_assoc, mul_sum]
  · calc
      Real.sqrt (Q.2 (z j) (z j)) ≤ ∑ i, Real.sqrt (Q.2 (v i j) (v i j)) :=
        LocalizedBoundary.energy_sqrt_sum_internal Q hQ univ (fun i => v i j)
      _ ≤ ∑ i, B * weightRadius m j i ^ (-G) * ‖f i‖ := sum_le_sum fun i _ => (hb i j).2
      _ = _ := by simp only [mul_assoc, mul_sum]

/-- Near/far splitting in the proof of Proposition 5.15.
The central source envelope is used only inside distance `R/64`. Outside,
the total source mass suffices. -/
theorem convolution_split_internal {V : Type*} [NormedAddCommGroup V]
    (N : ℕ+) (j : Fin (N : ℕ)) (t a R T S : ℝ)
    (ht : 0 ≤ t) (hR : 16 ≤ R) (hT : 0 ≤ T)
    (f : Fin (N : ℕ) → V)
    (hmass : (∑ i, ‖f i‖) ≤ T * R ^ (-a))
    (hcentral : ∀ i, (Riesz1.cyclicIndexDistance N i j : ℝ) ≤ R / 64 →
      ‖f i‖ ≤ T * R ^ (-(1+a)))
    (hshell : (∑ i ∈ univ.filter (fun i => weightRadius N i j ≤ R),
      weightRadius N i j ^ (-t)) ≤ S) :
    (∑ i, weightRadius N j i ^ (-t) * ‖f i‖) ≤
      T * (S * R ^ (-(1+a)) + 64 ^ t * R ^ (-(t+a))) := by
  let J := univ.filter (fun i : Fin (N : ℕ) =>
    (Riesz1.cyclicIndexDistance N i j : ℝ) ≤ R / 64)
  have hRp : 0 < R := by linarith
  have hw (i : Fin (N : ℕ)) : 0 ≤ weightRadius N j i ^ (-t) := by
    exact Real.rpow_nonneg (le_trans zero_le_one (one_le_weightRadius N j i)) _
  have hs : (∑ i ∈ J, weightRadius N j i ^ (-t)) ≤ S := by
    have hsub : J ⊆ univ.filter (fun i => weightRadius N i j ≤ R) := by
      intro i hi
      simp only [J, mem_filter, mem_univ, true_and] at hi ⊢
      unfold weightRadius
      linarith
    simp_rw [show ∀ i, weightRadius N j i = weightRadius N i j from
      fun i => by simp only [weightRadius, cyclicIndexDistance_comm' N j i]]
    exact (sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ =>
      Real.rpow_nonneg (le_trans zero_le_one (one_le_weightRadius N i j)) _)).trans hshell
  have hn : (∑ i ∈ J, weightRadius N j i ^ (-t) * ‖f i‖) ≤
      T * S * R ^ (-(1+a)) := by
    calc
      _ ≤ ∑ i ∈ J, weightRadius N j i ^ (-t) * (T * R ^ (-(1+a))) :=
        sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
          (hcentral i (mem_filter.mp hi).2) (hw i)
      _ = (∑ i ∈ J, weightRadius N j i ^ (-t)) * (T * R ^ (-(1+a))) := by rw [sum_mul]
      _ ≤ S * (T * R ^ (-(1+a))) := mul_le_mul_of_nonneg_right hs (by positivity)
      _ = _ := by ring
  have hf : (∑ i ∈ Jᶜ, weightRadius N j i ^ (-t) * ‖f i‖) ≤
      T * 64 ^ t * R ^ (-(t+a)) := by
    have hwi (i : Fin (N : ℕ)) (hi : i ∈ Jᶜ) :
        weightRadius N j i ^ (-t) ≤ 64 ^ t * R ^ (-t) := by
      have hdi : R / 64 < (Riesz1.cyclicIndexDistance N i j : ℝ) := by
        simpa only [J, mem_compl, mem_filter, mem_univ, true_and, not_le] using hi
      have hd : R / 64 ≤ weightRadius N j i := by
        rw [weightRadius_eq_comm]
        linarith
      calc
        _ ≤ (R / 64) ^ (-t) := Real.rpow_le_rpow_of_nonpos (by positivity) hd (by linarith)
        _ = _ := by
          rw [Real.div_rpow hRp.le (by norm_num), div_eq_mul_inv,
            ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 64), neg_neg]
          ring
    calc
      _ ≤ ∑ i ∈ Jᶜ, (64 ^ t * R ^ (-t)) * ‖f i‖ :=
        sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hwi i hi) (norm_nonneg _)
      _ = (64 ^ t * R ^ (-t)) * ∑ i ∈ Jᶜ, ‖f i‖ := by rw [mul_sum]
      _ ≤ (64 ^ t * R ^ (-t)) * (T * R ^ (-a)) :=
        mul_le_mul_of_nonneg_left
          ((sum_le_sum_of_subset_of_nonneg (subset_univ Jᶜ)
            (fun i _ _ => norm_nonneg (f i))).trans hmass) (by positivity)
      _ = _ := by rw [show -(t+a) = -t + -a by ring, Real.rpow_add hRp]; ring
  rw [← sum_add_sum_compl J (fun i => weightRadius N j i ^ (-t) * ‖f i‖)]
  convert add_le_add hn hf using 1; ring

/-- Unified cyclic shell bound for the proof of Proposition 5.15.
The logarithm is explicit at exponent one. It does not change the power.
There is no constraint relating `R` to the component count. -/
theorem shell_bound_internal (t : ℝ) (ht : 0 < t) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (j : Fin (N : ℕ)) (R : ℝ), 1 ≤ R →
      (∑ i ∈ univ.filter (fun i => weightRadius N i j ≤ R),
        weightRadius N i j ^ (-t)) ≤
      C * (1 + Real.log (2 * R)) * R ^ (max (1-t) 0) := by
  rcases lt_trichotomy t 1 with h | h | h
  · refine ⟨2 / (1-t), by positivity, fun N j R hR => ?_⟩
    rw [max_eq_left (by linarith : 0 ≤ 1-t)]
    have hlog : 0 ≤ Real.log (2*R) := Real.log_nonneg (by linarith)
    have hs := sum_weightRadius_le_of_lt_one N j ht h hR
    apply hs.trans
    have hh := mul_le_mul_of_nonneg_left (show 1 ≤ 1 + Real.log (2*R) by linarith)
      (show 0 ≤ 2 / (1-t) * R ^ (1-t) by positivity)
    convert hh using 1 <;> ring
  · subst t
    refine ⟨2 * (1 + 1 / Real.log 2), by positivity, fun N j R hR => ?_⟩
    simp only [sub_self, max_self, Real.rpow_zero, mul_one]
    have hs := sum_weightRadius_le_of_one N j hR
    have hC : 0 ≤ 2 * (1 + 1 / Real.log 2) := by positivity
    nlinarith only [hs, hC]
  · let C := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-t)
    have hC : 0 ≤ C := by dsimp only [C]; positivity
    refine ⟨C + 1, by positivity, fun N j R hR => ?_⟩
    rw [max_eq_right (by linarith : 1-t ≤ 0), Real.rpow_zero, mul_one]
    have hs := sum_weightRadius_le_of_gt_one N j h hR
    have hlog : 0 ≤ Real.log (2*R) := Real.log_nonneg (by linarith)
    change _ ≤ (C+1) * (1 + Real.log (2*R))
    nlinarith only [hs, hC, hlog, mul_nonneg hC hlog]

/-- Comparison-source convolution in the proof of Proposition 5.15.
The two-power estimate preceding equation (5.72) holds in all three
regimes of the exponent. -/
theorem source_convolution_internal (t : ℝ) (ht : 0 < t) :
    ∃ C : ℝ, 0 < C ∧ ∀ {V : Type*} [NormedAddCommGroup V]
      (N : ℕ+) (j : Fin (N : ℕ)) (a R T : ℝ), 16 ≤ R → 0 ≤ T →
      ∀ f : Fin (N : ℕ) → V,
      (∑ i, ‖f i‖) ≤ T * R ^ (-a) →
      (∀ i, (Riesz1.cyclicIndexDistance N i j : ℝ) ≤ R / 64 →
        ‖f i‖ ≤ T * R ^ (-(1+a))) →
      (∑ i, weightRadius N j i ^ (-t) * ‖f i‖) ≤
        C * T * (1 + Real.log (2*R)) *
          (R ^ (-(1+a)) + R ^ (-(t+a))) := by
  obtain ⟨B, hB, hb⟩ := shell_bound_internal t ht
  refine ⟨B + 64 ^ t, by positivity, ?_⟩
  intro V _ N j a R T hR hT f hmass hcentral
  have hRp : 0 < R := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hlog : 1 ≤ 1 + Real.log (2*R) := by
    have := Real.log_nonneg (by linarith : 1 ≤ 2*R)
    linarith
  have hnear : R ^ (max (1-t) 0) * R ^ (-(1+a)) ≤
      R ^ (-(1+a)) + R ^ (-(t+a)) := by
    by_cases h : t ≤ 1
    · rw [max_eq_left (by linarith : 0 ≤ 1-t), ← Real.rpow_add hRp,
        show (1-t) + -(1+a) = -(t+a) by ring]
      exact le_add_of_nonneg_left (Real.rpow_nonneg hRp.le _)
    · rw [max_eq_right (by linarith : 1-t ≤ 0), Real.rpow_zero, one_mul]
      exact le_add_of_nonneg_right (Real.rpow_nonneg hRp.le _)
  have he := convolution_split_internal N j t a R T
    (B * (1 + Real.log (2*R)) * R ^ (max (1-t) 0)) ht.le hR hT
    f hmass hcentral (hb N j R hR1)
  have hnear' : T * (B * (1 + Real.log (2*R)) * R ^ (max (1-t) 0) * R ^ (-(1+a))) ≤
      B * T * (1 + Real.log (2*R)) * (R ^ (-(1+a)) + R ^ (-(t+a))) := by
    have hh := mul_le_mul_of_nonneg_left hnear
      (show 0 ≤ B * T * (1 + Real.log (2*R)) by positivity)
    convert hh using 1; ring
  have hfar : T * (64 ^ t * R ^ (-(t+a))) ≤
      64 ^ t * T * (1 + Real.log (2*R)) * (R ^ (-(1+a)) + R ^ (-(t+a))) := by
    have hpow : 0 ≤ R ^ (-(1+a)) := by positivity
    have hh := mul_le_mul_of_nonneg_left
      (show R ^ (-(t+a)) ≤ (1 + Real.log (2*R)) *
        (R ^ (-(1+a)) + R ^ (-(t+a))) by
        nlinarith only [hlog, hpow, Real.rpow_nonneg hRp.le (-(t+a)),
          mul_nonneg (show 0 ≤ Real.log (2*R) from by linarith) hpow])
      (show 0 ≤ 64 ^ t * T by positivity)
    convert hh using 1 <;> ring
  calc
    _ ≤ _ := he
    _ = T * (B * (1 + Real.log (2*R)) * R ^ (max (1-t) 0) * R ^ (-(1+a))) +
        T * (64 ^ t * R ^ (-(t+a))) := by ring
    _ ≤ _ := add_le_add hnear' hfar
    _ = _ := by ring

/-- The comparison error's value and gradient bounds in the proof of Proposition 5.15, before absorbing the logarithm. The
point-source estimates are internal inputs on the actual localized matrix.
Coercive uniqueness identifies their finite superposition with any given error. -/
theorem comparison_error_internal
    (s : Riesz1.RieszExponent) (A G : ℝ) (hA : 0 < A) (hG : 0 < G) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω)
      (Q : ScalarFormData ν) (_hQ : IsClosedScalarDirichletForm Q)
      (n m : ℕ+) (hm : 2 ≤ (m : ℕ)) (K : ℕ)
      (Cstar κ γ ε β : ℝ), 1 ≤ Cstar → 0 < β →
    ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κ γ ε M →
    ∀ B : ℝ, 0 ≤ B →
    (∀ (χ : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ)),
      ∃ u : Fin (m : ℕ) → Q.1,
        WeightedWeakSolution Q (fun x => β • M x) ⊤
          (fun i => if i = i₀ then χ else 0) u ∧
        ∀ j, ‖(u j).val‖ ≤ B * weightRadius m j i₀ ^ (-A) * ‖χ‖ ∧
          Real.sqrt (Q.2 (u j) (u j)) ≤ B * weightRadius m j i₀ ^ (-G) * ‖χ‖) →
    ∀ (g : Fin (m : ℕ) → Lp ℝ 2 ν) (e : Fin (m : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β • M x) ⊤ g e →
    ∀ (j : Fin (m : ℕ)) (R T : ℝ), 16 ≤ R → 0 ≤ T →
    (∑ i, ‖g i‖) ≤ T * R ^ (-(1-s.val)) →
    (∀ i, (Riesz1.cyclicIndexDistance m i j : ℝ) ≤ R / 64 →
      ‖g i‖ ≤ T * R ^ (-(2-s.val))) →
    ‖(e j).val‖ ≤ C * B * T * (1 + Real.log (2*R)) *
      (R ^ (-(2-s.val)) + R ^ (-(A+1-s.val))) ∧
    Real.sqrt (Q.2 (e j) (e j)) ≤ C * B * T * (1 + Real.log (2*R)) *
      (R ^ (-(2-s.val)) + R ^ (-(G+1-s.val))) := by
  obtain ⟨CA, hCA, hconvA⟩ := source_convolution_internal A hA
  obtain ⟨CG, hCG, hconvG⟩ := source_convolution_internal G hG
  refine ⟨CA+CG, by positivity, ?_⟩
  intro Ω _ ν Q hQ n m hm K Cstar κ γ ε β hCstar hβ M hM B hB hp g e he j R T hR hT hmass hcentral
  obtain ⟨hv, hg⟩ := (superposition_internal Q hQ s n m hm K Cstar κ γ ε β
    hCstar hβ M hM A G B hp g).2 e he j
  have hcentral' : ∀ i, (Riesz1.cyclicIndexDistance m i j : ℝ) ≤ R / 64 →
      ‖g i‖ ≤ T * R ^ (-(1+(1-s.val))) := by
    simpa only [show 1+(1-s.val)=2-s.val by ring] using hcentral
  have hca := hconvA m j (1-s.val) R T hR hT g hmass hcentral'
  have hcg := hconvG m j (1-s.val) R T hR hT g hmass hcentral'
  rw [show 1+(1-s.val)=2-s.val by ring, show A+(1-s.val)=A+1-s.val by ring] at hca
  rw [show 1+(1-s.val)=2-s.val by ring, show G+(1-s.val)=G+1-s.val by ring] at hcg
  have hlog : 0 ≤ 1+Real.log (2*R) := by
    have := Real.log_nonneg (by linarith : 1 ≤ 2*R)
    linarith
  constructor
  · calc
      _ ≤ B * (CA * T * (1+Real.log (2*R)) *
          (R ^ (-(2-s.val)) + R ^ (-(A+1-s.val)))) :=
        hv.trans (mul_le_mul_of_nonneg_left hca hB)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right (show CA ≤ CA+CG by linarith)
          (show 0 ≤ B*T*(1+Real.log (2*R))*
            (R ^ (-(2-s.val)) + R ^ (-(A+1-s.val))) by positivity)
        convert hh using 1 <;> ring
  · calc
      _ ≤ B * (CG * T * (1+Real.log (2*R)) *
          (R ^ (-(2-s.val)) + R ^ (-(G+1-s.val)))) :=
        hg.trans (mul_le_mul_of_nonneg_left hcg hB)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right (show CG ≤ CA+CG by linarith)
          (show 0 ≤ B*T*(1+Real.log (2*R))*
            (R ^ (-(2-s.val)) + R ^ (-(G+1-s.val))) by positivity)
        convert hh using 1 <;> ring

/-- Minimum-exponent saturation and conversion to `1+R` in the proof of Proposition 5.15. The power is evaluated at `R ≥ 1`.
This covers equal exponents and already saturated endpoints. -/
theorem two_power_saturation_internal (R p q t : ℝ) (hR : 1 ≤ R)
    (ht : 0 ≤ t) (hp : t ≤ p) (hq : t ≤ q) :
    R ^ (-p) + R ^ (-q) ≤ (2 * 2 ^ t) * (1+R) ^ (-t) := by
  have hRp : 0 < R := by linarith
  have hmon (v : ℝ) (hv : t ≤ v) : R ^ (-v) ≤ R ^ (-t) :=
    Real.rpow_le_rpow_of_exponent_le hR (by linarith)
  have hscale : R ^ (-t) ≤ 2 ^ t * (1+R) ^ (-t) := by
    have hh := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < (1+R)/2)
      (show (1+R)/2 ≤ R by linarith) (show -t ≤ 0 by linarith)
    have heq : ((1+R)/2) ^ (-t) = 2 ^ t * (1+R) ^ (-t) := by
      rw [Real.div_rpow (by linarith : 0 ≤ 1+R) (by norm_num),
        div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), neg_neg]
      ring
    exact hh.trans_eq heq
  have hh := add_le_add ((hmon p hp).trans hscale) ((hmon q hq).trans hscale)
  convert hh using 1; ring

/-- Absorb the comparison convolution's logarithm into one fixed additional
loss exponent, as required by Subsection 5.4. The separation
radius may be any real number up to the original period. -/
theorem logarithmic_loss_internal (s : Riesz1.RieszExponent) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ+), 2 ≤ (n : ℕ) → 2 ≤ (m : ℕ) →
      (m : ℝ) ≤ 2 * (n : ℝ) ^ (1/2+1/s.val) →
      ∀ R : ℝ, 1 ≤ R → R ≤ (m : ℝ) →
      1+Real.log (2*R) ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨C, hc⟩ := log_bound_global s.val 1 1 ε s.property.1 s.property.2
    zero_lt_one zero_le_one hε
  refine ⟨max C 0 + 1, by positivity, fun n m hn hm hmn R hR hRm => ?_⟩
  have hlog : Real.log (2*R) ≤ Real.log (2*(m : ℝ)) :=
    Real.log_le_log (by linarith) (by linarith)
  have hb := hc n m hn hm hmn
  simp only [Real.rpow_one, one_mul] at hb
  have hpow : 1 ≤ (n : ℝ) ^ ε :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ (n : ℕ) by omega)) hε.le
  have hmul := mul_le_mul_of_nonneg_right (le_max_left C 0)
    (Real.rpow_nonneg (by positivity : 0 ≤ (n : ℝ)) ε)
  nlinarith only [hlog, hb, hpow, hmul]

/-- The small-separation part of the proof of Proposition 5.15.
An unweighted estimate with loss `k` gains any fixed nonnegative spatial
exponent `t` on `R < max(16,n^(D ε))`, at loss `k + D t`.
No lower bound on `R` other than nonnegativity is needed. -/
theorem small_distance_internal (n ε D k t R B F x : ℝ)
    (hn : 1 ≤ n) (hε : 0 ≤ ε) (hD : 0 ≤ D) (ht : 0 ≤ t)
    (hR0 : 0 ≤ R) (hR : R < max 16 (n ^ (D*ε)))
    (hB : 0 ≤ B) (hF : 0 ≤ F) (hx : x ≤ B * n ^ (k*ε) * F) :
    x ≤ (17 ^ t * B) * n ^ ((k+D*t)*ε) * (1+R) ^ (-t) * F := by
  have hnp : 0 < n := by linarith
  have hpow : 1 ≤ n ^ (D*ε) := Real.one_le_rpow hn (mul_nonneg hD hε)
  have hrad : 1+R ≤ 17 * n ^ (D*ε) := by
    rcases lt_max_iff.mp hR with h | h
    · linarith
    · linarith
  have he : (1+R) ^ t ≤ 17 ^ t * n ^ (D*t*ε) := by
    calc
      _ ≤ (17 * n ^ (D*ε)) ^ t := Real.rpow_le_rpow (by linarith) hrad ht
      _ = _ := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 17)
          (Real.rpow_nonneg hnp.le _), ← Real.rpow_mul hnp.le]
        congr 2
        ring
  have hcancel : (1+R) ^ t * (1+R) ^ (-t) = 1 := by
    rw [← Real.rpow_add (by linarith : 0 < 1+R), add_neg_cancel, Real.rpow_zero]
  have hh := mul_le_mul_of_nonneg_right he
    (show 0 ≤ B * n ^ (k*ε) * (1+R) ^ (-t) * F by positivity)
  have hnpow : n ^ ((k+D*t)*ε) = n ^ (k*ε) * n ^ (D*t*ε) := by
    rw [show (k+D*t)*ε = k*ε + D*t*ε by ring, Real.rpow_add hnp]
  rw [hnpow]
  calc
    x ≤ B * n ^ (k*ε) * F := hx
    _ = (1+R) ^ t * (B * n ^ (k*ε) * (1+R) ^ (-t) * F) := by
      calc
        _ = (B*n^(k*ε)*F) * ((1+R)^t * (1+R)^(-t)) := by rw [hcancel, mul_one]
        _ = _ := by ring
    _ ≤ _ := hh
    _ = _ := by ring

/-- Addition of the boundary, reference and error profiles at one component
in the proof of Proposition 5.15. This arithmetic lemma is
used for both the value norm and the square root of the Dirichlet energy.
The two error exponents saturate at the requested target `t`.
All decomposition hypotheses remain internal. -/
theorem assemble_profile_internal (R p q t Z P E x z φ e : ℝ)
    (hR : 1 ≤ R) (ht : 0 ≤ t) (hp : t ≤ p) (hq : t ≤ q)
    (hZ : 0 ≤ Z) (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hx : x ≤ z+φ+e) (hz : z ≤ Z * R ^ (-p)) (hφ : φ ≤ P * R ^ (-p))
    (he : e ≤ E * (R ^ (-p) + R ^ (-q))) :
    x ≤ (2 ^ t * (Z+P+2*E)) * (1+R) ^ (-t) := by
  have htR := two_power_saturation_internal R p q t hR ht hp hq
  have hpR := two_power_saturation_internal R p p t hR ht hp hp
  have hzR : Z * R ^ (-p) ≤ Z * 2 ^ t * (1+R) ^ (-t) := by
    have hh := mul_le_mul_of_nonneg_left hpR hZ
    nlinarith only [hh]
  have hφR : P * R ^ (-p) ≤ P * 2 ^ t * (1+R) ^ (-t) := by
    have hh := mul_le_mul_of_nonneg_left hpR hP
    nlinarith only [hh]
  have heR := mul_le_mul_of_nonneg_left htR hE
  nlinarith only [hx, hz, hφ, he, hzR, hφR, heR]

/-- Loss bookkeeping for the two error profiles in the proof of Proposition 5.15. Absorbing the sole logarithm adds exactly
one to the loss exponent, independently of ε and of every prefactor. -/
theorem error_loss_internal (s : Riesz1.RieszExponent) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ+), 2 ≤ (n : ℕ) → 2 ≤ (m : ℕ) →
      (m : ℝ) ≤ 2 * (n : ℝ) ^ (1/2+1/s.val) →
      ∀ R p q t B k x : ℝ, 1 ≤ R → R ≤ (m : ℝ) →
      0 ≤ t → t ≤ p → t ≤ q → 0 ≤ B →
      x ≤ B * (n : ℝ) ^ (k*ε) * (1+Real.log (2*R)) *
        (R ^ (-p) + R ^ (-q)) →
      x ≤ (C * 2 * 2 ^ t * B) * (n : ℝ) ^ ((k+1)*ε) * (1+R) ^ (-t) := by
  obtain ⟨C, hC, hc⟩ := logarithmic_loss_internal s ε hε
  refine ⟨C, hC, fun n m hn hm hmn R p q t B k x hR hRm ht hp hq hB hx => ?_⟩
  have hlog := hc n m hn hm hmn R hR hRm
  have hsat := two_power_saturation_internal R p q t hR ht hp hq
  have hlog0 : 0 ≤ 1+Real.log (2*R) := by
    have := Real.log_nonneg (by linarith : 1 ≤ 2*R)
    linarith
  calc
    x ≤ B * (n : ℝ) ^ (k*ε) * (1+Real.log (2*R)) *
        (R ^ (-p) + R ^ (-q)) := hx
    _ ≤ B * (n : ℝ) ^ (k*ε) * (C * (n : ℝ) ^ ε) *
        ((2 * 2 ^ t) * (1+R) ^ (-t)) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hlog (by positivity)) hsat
        (by positivity) (by positivity)
    _ = _ := by
      rw [show (k+1)*ε = k*ε+ε by ring,
        Real.rpow_add (by positivity : 0 < (n : ℝ))]
      ring

end Riesz2.OptimalLocalization
