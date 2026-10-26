/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.UnconstrainedGlobalDecay
public import Riesz2.Frozen.IsEuclideanGibbsPotential
public import Riesz2.Frozen.IsNeumannRealization
public import Riesz2.Frozen.InverseTemperature
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Finite bootstrap for optimal localization

The base case comes from the global estimates. A finite induction
combines the constrained and unrestricted localization improvements,
which are arguments of the composition lemma.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Riesz2.OptimalLocalizationBootstrap

/-- One equation mode of the internal uniform assertion in Subsection 5.5.
The conjunction of the two modes is the induction property. The scalar forms and matrices are those of Subsection 5.5. The loss exponent precedes ε, the
matrix prefactor, and the compact temperature interval. -/
def UniformEstimate (s : Riesz1.RieszExponent) (A G : ℝ) (b : Bool) : Prop :=
  ∀ (κₛ γₛ : ℝ) (M₀ : ℕ+),
    0 < κₛ → 0 < γₛ → ∃ κ : ℝ, 0 < κ ∧
    ∀ ε : ℝ, 0 < ε → ∀ Cₛ : ℝ, 1 ≤ Cₛ →
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
      ∃ C : ℝ, 0 < C ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n m : ℕ+) (_ : 2 ≤ (n : ℕ)) (hm : 2 ≤ (m : ℕ)),
        (n : ℕ) ≤ (m : ℕ) → (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
        let K := (Nat.floor ((n : ℝ) ^ ε)) ^ (M₀ : ℕ)
        1 ≤ K → 4 * K ≤ (m : ℕ) →
        ∀ (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d)))
          (ν : Measure (EuclideanSpace ℝ (Fin d))),
          IsOpen Ω → Convex ℝ Ω → Bornology.IsBounded Ω → Ω.Nonempty →
          IsProbabilityMeasure ν →
          (∃ V : EuclideanSpace ℝ (Fin d) → ℝ,
            IsEuclideanGibbsPotential volume ν Ω V 2) →
          ∀ Q : ScalarFormData ν, IsNeumannRealization Ω Q →
            IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
          ∀ M : EuclideanSpace ℝ (Fin d) → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
            PeriodizedMatrixBounds (ν := ν) s n m hm K Cₛ κₛ γₛ ε M →
            ∀ (i₀ : Fin (m : ℕ)) (χ : Lp ℝ 2 ν),
              let S := if b then zeroSumComponents (Fin (m : ℕ)) else ⊤
              (∃! u : Fin (m : ℕ) → Q.1, WeightedWeakSolution Q
                (fun x => β.val • M x) S (fun i => if i = i₀ then χ else 0) u) ∧
              (∀ u : Fin (m : ℕ) → Q.1, WeightedWeakSolution Q
                  (fun x => β.val • M x) S (fun i => if i = i₀ then χ else 0) u →
                ∀ j : Fin (m : ℕ),
                  ‖(u j).val‖ ≤ C * (n : ℝ) ^ (κ * ε) *
                    (1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ)) ^ (-A) * ‖χ‖ ∧
                  Real.sqrt (Q.2 (u j) (u j)) ≤ C * (n : ℝ) ^ (κ * ε) *
                    (1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ)) ^ (-G) * ‖χ‖)

/-- Taking one component of a weighted value/energy estimate, as used in
Proposition 5.15. The radii are positive, so their inverse powers are defined. -/
theorem component_bounds_internal {X : Type*} [MeasurableSpace X] {ν : Measure X}
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (m : ℕ+) (i₀ : Fin (m : ℕ)) (A G B : ℝ) (u : Fin (m : ℕ) → Q.1)
    (h : Real.sqrt (∑ i, (weightRadius m i i₀ ^ A * ‖(u i).val‖) ^ 2) +
      Real.sqrt (∑ i, weightRadius m i i₀ ^ (2 * G) * Q.2 (u i) (u i)) ≤ B) :
    ∀ j, ‖(u j).val‖ ≤ B * weightRadius m j i₀ ^ (-A) ∧
      Real.sqrt (Q.2 (u j) (u j)) ≤ B * weightRadius m j i₀ ^ (-G) := by
  intro j
  have hr : 0 < weightRadius m j i₀ := lt_of_lt_of_le zero_lt_one (one_le_weightRadius _ _ _)
  have hv : weightRadius m j i₀ ^ A * ‖(u j).val‖ ≤ B := by
    have hh := Real.sqrt_le_sqrt (Finset.single_le_sum
      (fun i (_ : i ∈ Finset.univ) => sq_nonneg (weightRadius m i i₀ ^ A * ‖(u i).val‖))
      (Finset.mem_univ j))
    rw [Real.sqrt_sq (by positivity)] at hh
    linarith [Real.sqrt_nonneg (∑ i, weightRadius m i i₀ ^ (2 * G) * Q.2 (u i) (u i))]
  have hg : weightRadius m j i₀ ^ G * Real.sqrt (Q.2 (u j) (u j)) ≤ B := by
    have hh := Real.sqrt_le_sqrt (Finset.single_le_sum
      (fun i (_ : i ∈ Finset.univ) => mul_nonneg (Real.rpow_nonneg
        (le_trans zero_le_one (one_le_weightRadius m i i₀)) (2 * G)) (hQ.2.2.1 (u i)))
      (Finset.mem_univ j))
    rw [show weightRadius m j i₀ ^ (2 * G) = (weightRadius m j i₀ ^ G) ^ 2 by
      rw [mul_comm (2 : ℝ), Real.rpow_mul hr.le, Real.rpow_two],
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)] at hh
    linarith [Real.sqrt_nonneg (∑ i, (weightRadius m i i₀ ^ A * ‖(u i).val‖) ^ 2)]
  constructor
  · have hh := mul_le_mul_of_nonneg_right hv (Real.rpow_nonneg hr.le (-A))
    simpa only [mul_assoc, ← Real.rpow_add hr, add_neg_cancel, Real.rpow_zero, mul_one,
      mul_comm (weightRadius m j i₀ ^ A)] using hh
  · have hh := mul_le_mul_of_nonneg_right hg (Real.rpow_nonneg hr.le (-G))
    calc
      Real.sqrt (Q.2 (u j) (u j)) =
          (weightRadius m j i₀ ^ G * Real.sqrt (Q.2 (u j) (u j))) *
            weightRadius m j i₀ ^ (-G) := by
        rw [mul_right_comm, ← Real.rpow_add hr, add_neg_cancel, Real.rpow_zero, one_mul]
      _ ≤ _ := hh

/-- Base exponents in Proposition 5.15, obtained from
Lemma 5.13 and Lemma 5.14 without localization hypotheses. -/
theorem base_internal (hzeta : External.PeriodicZeta) (s : Riesz1.RieszExponent) :
    ∀ b, UniformEstimate s (3 / 2 - s.val) (1 - s.val / 2) b := by
  intro b κₛ γₛ M₀ hκₛ hγₛ
  cases b
  · obtain ⟨κ, hκ, he⟩ := UnconstrainedGlobalDecay.global_bis hzeta s κₛ γₛ hκₛ hγₛ M₀
    refine ⟨κ, hκ, fun ε hε Cₛ hCₛ βlo βhi hβlo hβhi => ?_⟩
    obtain ⟨C, hC, he⟩ := he ε hε Cₛ hCₛ βlo hβlo βhi hβhi
    refine ⟨C, hC, ?_⟩
    intro β hβ n m hn hm hnm hmn K hK hKm d Ω ν hΩo hΩc hΩb hΩn hν hV Q hQN hQ hQc M hM i₀ χ
    have : IsProbabilityMeasure ν := hν
    obtain ⟨v, hv, _⟩ := he ν Q hQ hQc n m hm hn hnm hmn hK hKm M hM
      β.val hβ.1 hβ.2 χ i₀
    have hl : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
        ∀ z : Fin (m : ℕ) → ℝ,
          Cₛ⁻¹ * (n : ℝ) ^ (-κₛ * ε) * (∑ i, z i ^ 2) ≤
            ∑ i, ∑ j, z i * M x i j * z j :=
      hM.2.1.mono (fun _ hx => ⟨hx.1, hx.2.2.1⟩)
    have huniq := (AbstractEquation.existence_energy Q hQ β.val β.property M hM.1 _
      (SchurRestriction.periodized_mass_pos hCₛ) hl ⊤ (fun i => if i = i₀ then χ else 0)).1
    refine ⟨huniq, fun u hu j => ?_⟩
    have huv : u = v := huniq.unique hu hv.1
    subst u
    have hb := component_bounds_internal Q hQ m i₀ _ _ _ v hv.2 j
    constructor
    · convert hb.1 using 1; dsimp only [weightRadius]; ring
    · convert hb.2 using 1; dsimp only [weightRadius]; ring
  · obtain ⟨κ, hκ, he⟩ := GlobalDecay.global_decay hzeta s κₛ γₛ hκₛ hγₛ M₀
    refine ⟨κ, hκ, fun ε hε Cₛ hCₛ βlo βhi hβlo hβhi => ?_⟩
    obtain ⟨C, hC, he⟩ := he ε hε Cₛ hCₛ βlo hβlo βhi hβhi
    refine ⟨C, hC, ?_⟩
    intro β hβ n m hn hm hnm hmn K hK hKm d Ω ν hΩo hΩc hΩb hΩn hν hV Q hQN hQ hQc M hM i₀ χ
    have : IsProbabilityMeasure ν := hν
    obtain ⟨v, hv, _⟩ := he ν Q hQ hQc n m hm hn hnm hmn hK hKm M hM
      β.val hβ.1 hβ.2 χ i₀
    have hl : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
        ∀ z : Fin (m : ℕ) → ℝ,
          Cₛ⁻¹ * (n : ℝ) ^ (-κₛ * ε) * (∑ i, z i ^ 2) ≤
            ∑ i, ∑ j, z i * M x i j * z j :=
      hM.2.1.mono (fun _ hx => ⟨hx.1, hx.2.2.1⟩)
    have huniq := (AbstractEquation.existence_energy Q hQ β.val β.property M hM.1 _
      (SchurRestriction.periodized_mass_pos hCₛ) hl (zeroSumComponents _) (fun i => if i = i₀ then χ else 0)).1
    refine ⟨huniq, fun u hu j => ?_⟩
    have huv : u = v := huniq.unique hu hv.1
    subst u
    obtain ⟨lam, hlam, hfull, hest, hrest⟩ := hv.2
    have hb := component_bounds_internal Q hQ m i₀ _ _ _ v hest j
    constructor
    · convert hb.1 using 1; dsimp only [weightRadius]; ring
    · convert hb.2 using 1; dsimp only [weightRadius]; ring

/-- A saturated exponent remains saturated after a positive increment. -/
theorem min_step_internal (cap x δ : ℝ) (hδ : 0 ≤ δ) :
    min cap (min cap x + δ) = min cap (x + δ) := by
  by_cases hx : x ≤ cap
  · rw [min_eq_right hx]
  · rw [min_eq_left (le_of_not_ge hx), min_eq_left (by linarith),
      min_eq_left (by linarith)]

/-- The finite exponent induction in Proposition 5.15.
Exactly `⌈1 / (2 * (1 - s))⌉` steps suffice, including when the ceiling
is attained exactly. All intermediate exponents obey both step ranges. -/
theorem finite_saturation_internal (s : Riesz1.RieszExponent) (P : ℝ → ℝ → Prop)
    (hbase : P (3 / 2 - s.val) (1 - s.val / 2))
    (hstep : ∀ A G : ℝ, 3 / 2 - s.val ≤ A → A ≤ 2 - s.val →
      1 - s.val / 2 ≤ G → G ≤ (3 - s.val) / 2 → G ≤ A →
      P A G → P (min (2 - s.val) (A + 1 - s.val))
        (min ((3 - s.val) / 2) (G + 1 - s.val))) :
    P (2 - s.val) ((3 - s.val) / 2) := by
  have hδ : 0 < 1 - s.val := sub_pos.mpr s.property.2
  have hind : ∀ k : ℕ,
      P (min (2 - s.val) (3 / 2 - s.val + (k : ℝ) * (1 - s.val)))
        (min ((3 - s.val) / 2) (1 - s.val / 2 + (k : ℝ) * (1 - s.val))) := by
    intro k
    induction k with
    | zero => simpa [min_eq_right (show 3 / 2 - s.val ≤ 2 - s.val by linarith),
        min_eq_right (show 1 - s.val / 2 ≤ (3 - s.val) / 2 by linarith)] using hbase
    | succ k ih =>
      have hk : 0 ≤ (k : ℝ) * (1 - s.val) := mul_nonneg (Nat.cast_nonneg k) hδ.le
      have hh := hstep _ _ (le_min (by linarith) (by linarith)) (min_le_left _ _)
        (le_min (by linarith) (by linarith)) (min_le_left _ _)
        (min_le_min (by linarith [s.property.2]) (by linarith [s.property.2])) ih
      have hA :
          min (2 - s.val)
            (min (2 - s.val) (3 / 2 - s.val + (k : ℝ) * (1 - s.val)) + 1 - s.val) =
          min (2 - s.val) (3 / 2 - s.val + ((k + 1 : ℕ) : ℝ) * (1 - s.val)) := by
        rw [show min (2 - s.val) (3 / 2 - s.val + (k : ℝ) * (1 - s.val)) + 1 - s.val =
          min (2 - s.val) (3 / 2 - s.val + (k : ℝ) * (1 - s.val)) + (1 - s.val) by ring,
          min_step_internal _ _ _ hδ.le, Nat.cast_add, Nat.cast_one]
        congr 1; ring
      have hG :
          min ((3 - s.val) / 2)
            (min ((3 - s.val) / 2) (1 - s.val / 2 + (k : ℝ) * (1 - s.val)) + 1 - s.val) =
          min ((3 - s.val) / 2) (1 - s.val / 2 + ((k + 1 : ℕ) : ℝ) * (1 - s.val)) := by
        rw [show min ((3 - s.val) / 2) (1 - s.val / 2 + (k : ℝ) * (1 - s.val)) + 1 - s.val =
          min ((3 - s.val) / 2) (1 - s.val / 2 + (k : ℝ) * (1 - s.val)) + (1 - s.val) by ring,
          min_step_internal _ _ _ hδ.le, Nat.cast_add, Nat.cast_one]
        congr 1; ring
      rwa [hA, hG] at hh
  let T := Nat.ceil (1 / (2 * (1 - s.val)))
  have hT : 1 / (2 * (1 - s.val)) ≤ (T : ℝ) := Nat.le_ceil _
  have hhalf : (1 / 2 : ℝ) ≤ (T : ℝ) * (1 - s.val) := by
    have hh := (div_le_iff₀ (show 0 < 2 * (1 - s.val) by positivity)).mp hT
    linarith
  simpa only [min_eq_left (show 2 - s.val ≤ 3 / 2 - s.val + (T : ℝ) * (1 - s.val) by linarith),
    min_eq_left (show (3 - s.val) / 2 ≤ 1 - s.val / 2 + (T : ℝ) * (1 - s.val) by linarith)]
    using hind T

/-- Composition of the constrained and unrestricted improvements in the proof
of Proposition 5.15. These improvements are hypotheses with the exponent
ranges of Subsection 5.5. The conclusion includes unique existence and
the stated order of constants. -/
theorem optimal_decay_of_steps_internal (hzeta : External.PeriodicZeta)
    (hconstrained : ∀ (s : Riesz1.RieszExponent) (A G : ℝ),
      3 / 2 - s.val ≤ A → A ≤ 2 - s.val →
      1 - s.val / 2 ≤ G → G ≤ (3 - s.val) / 2 → G ≤ A →
      (∀ b, UniformEstimate s A G b) →
      UniformEstimate s (min (2 - s.val) (A + 1 - s.val))
        (min ((3 - s.val) / 2) (G + 1 - s.val)) true)
    (hunconstrained : ∀ (s : Riesz1.RieszExponent) (A G : ℝ),
      3 / 2 - s.val ≤ A → A ≤ 2 - s.val →
      1 - s.val / 2 ≤ G → G ≤ (3 - s.val) / 2 → G ≤ A →
      (∀ b, UniformEstimate s A G b) →
      UniformEstimate s (min (2 - s.val) (A + 1 - s.val))
        (min ((3 - s.val) / 2) (G + 1 - s.val)) false) :
  ∀ (s : Riesz1.RieszExponent) (κₛ γₛ : ℝ) (M₀ : ℕ+),
    0 < κₛ → 0 < γₛ → ∃ κ : ℝ, 0 < κ ∧
    ∀ ε : ℝ, 0 < ε → ∀ Cₛ : ℝ, 1 ≤ Cₛ →
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
      ∃ C : ℝ, 0 < C ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n m : ℕ+) (_ : 2 ≤ (n : ℕ)) (hm : 2 ≤ (m : ℕ)),
        (n : ℕ) ≤ (m : ℕ) → (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
        let K := (Nat.floor ((n : ℝ) ^ ε)) ^ (M₀ : ℕ)
        1 ≤ K → 4 * K ≤ (m : ℕ) →
        ∀ (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d)))
          (ν : Measure (EuclideanSpace ℝ (Fin d))),
          IsOpen Ω → Convex ℝ Ω → Bornology.IsBounded Ω → Ω.Nonempty →
          IsProbabilityMeasure ν →
          (∃ V : EuclideanSpace ℝ (Fin d) → ℝ,
            IsEuclideanGibbsPotential volume ν Ω V 2) →
          ∀ Q : ScalarFormData ν, IsNeumannRealization Ω Q →
            IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
          ∀ M : EuclideanSpace ℝ (Fin d) → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
            PeriodizedMatrixBounds (ν := ν) s n m hm K Cₛ κₛ γₛ ε M →
            ∀ (i₀ : Fin (m : ℕ)) (χ : Lp ℝ 2 ν) (b : Bool),
              let S := if b then zeroSumComponents (Fin (m : ℕ)) else ⊤
              (∃! u : Fin (m : ℕ) → Q.1, WeightedWeakSolution Q
                (fun x => β.val • M x) S (fun i => if i = i₀ then χ else 0) u) ∧
              (∀ u : Fin (m : ℕ) → Q.1, WeightedWeakSolution Q
                  (fun x => β.val • M x) S (fun i => if i = i₀ then χ else 0) u →
                ∀ j : Fin (m : ℕ),
                  ‖(u j).val‖ ≤ C * (n : ℝ) ^ (κ * ε) *
                    (1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ)) ^ (-(2 - s.val)) * ‖χ‖ ∧
                  Real.sqrt (Q.2 (u j) (u j)) ≤ C * (n : ℝ) ^ (κ * ε) *
                    (1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ)) ^ (-(3 - s.val) / 2) * ‖χ‖) := by
  intro s κₛ γₛ M₀ hκₛ hγₛ
  have hfinal : ∀ b, UniformEstimate s (2 - s.val) ((3 - s.val) / 2) b := by
    apply finite_saturation_internal s (fun A G => ∀ b, UniformEstimate s A G b)
      (base_internal hzeta s)
    intro A G hA hA' hG hG' hGA h b
    cases b
    · exact hunconstrained s A G hA hA' hG hG' hGA h
    · exact hconstrained s A G hA hA' hG hG' hGA h
  obtain ⟨κt, hκt, ht⟩ := hfinal true κₛ γₛ M₀ hκₛ hγₛ
  obtain ⟨κf, hκf, hf⟩ := hfinal false κₛ γₛ M₀ hκₛ hγₛ
  refine ⟨κt + κf, by positivity, fun ε hε Cₛ hCₛ βlo βhi hβlo hβhi => ?_⟩
  obtain ⟨Ct, hCt, ht⟩ := ht ε hε Cₛ hCₛ βlo βhi hβlo hβhi
  obtain ⟨Cf, hCf, hf⟩ := hf ε hε Cₛ hCₛ βlo βhi hβlo hβhi
  refine ⟨Ct + Cf, by positivity, ?_⟩
  intro β hβ n m hn hm hnm hmn K hK hKm d Ω ν hΩo hΩc hΩb hΩn hν hV Q hQN hQ hQc M hM i₀ χ b S
  have hnt : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have htf : Ct * (n : ℝ) ^ (κt * ε) ≤ (Ct + Cf) * (n : ℝ) ^ ((κt + κf) * ε) := by
    apply mul_le_mul (by linarith) _ (by positivity) (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le hnt (by nlinarith)
  have hff : Cf * (n : ℝ) ^ (κf * ε) ≤ (Ct + Cf) * (n : ℝ) ^ ((κt + κf) * ε) := by
    apply mul_le_mul (by linarith) _ (by positivity) (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le hnt (by nlinarith)
  cases b
  · obtain ⟨hex, he⟩ := hf β hβ n m hn hm hnm hmn hK hKm d Ω ν
      hΩo hΩc hΩb hΩn hν hV Q hQN hQ hQc M hM i₀ χ
    refine ⟨hex, fun u hu j => ?_⟩
    obtain ⟨hv, hg⟩ := he u hu j
    constructor
    · exact hv.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hff (by positivity)) (norm_nonneg χ))
    · have hg' := hg.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hff (by positivity)) (norm_nonneg χ))
      simpa only [neg_div] using hg'
  · obtain ⟨hex, he⟩ := ht β hβ n m hn hm hnm hmn hK hKm d Ω ν
      hΩo hΩc hΩb hΩn hν hV Q hQN hQ hQc M hM i₀ χ
    refine ⟨hex, fun u hu j => ?_⟩
    obtain ⟨hv, hg⟩ := he u hu j
    constructor
    · exact hv.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right htf (by positivity)) (norm_nonneg χ))
    · have hg' := hg.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right htf (by positivity)) (norm_nonneg χ))
      simpa only [neg_div] using hg'

end Riesz2.OptimalLocalizationBootstrap
