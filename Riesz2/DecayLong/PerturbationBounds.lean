/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.ConditionalForcesPart6
public import Riesz2.ToMathlib.PolynomialProfileTruncation
public import Riesz2.ToMathlib.CovarianceCauchySchwarz

/-!
# Physical perturbation pairings

Bilinear estimates for the density-defined compensation coefficients and
the physical boundary remainder in Lemma 5.8.
All coefficients reuse the physical definitions. The exceptional
power is `GoodBlocks.coefficientTailPower`, chosen before temperature.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped BigOperators ContDiff

namespace Riesz2.PerturbationBounds

set_option backward.isDefEq.respectTransparency false

/-- Boundary depths in Subsection 5.1 are positive and at most the
retained size, including an endpoint and a singleton block. -/
theorem depth_bounds (n : ℕ+) (i : Fin (n : ℕ)) :
    1 ≤ min (i.val + 1) ((n : ℕ) - i.val) ∧
      min (i.val + 1) ((n : ℕ) - i.val) ≤ (n : ℕ) := by
  have := i.isLt
  omega

/-- The entry profile of Lemma 5.8 is positive and
bounded by one, so no zero-base real power is used. -/
theorem entry_profile_bounds (s : Riesz1.RieszExponent) (n : ℕ+)
    (i j : Fin (n : ℕ)) :
    0 < ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val / 2) *
      ((min (j.val + 1) ((n : ℕ) - j.val) : ℕ) : ℝ) ^ (-s.val / 2) ∧
    ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val / 2) *
      ((min (j.val + 1) ((n : ℕ) - j.val) : ℕ) : ℝ) ^ (-s.val / 2) ≤ 1 := by
  have hd (a : Fin (n : ℕ)) : (1 : ℝ) ≤ (min (a.val + 1) ((n : ℕ) - a.val) : ℕ) :=
    by exact_mod_cast (depth_bounds n a).1
  constructor
  · exact mul_pos (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (hd i)) _)
      (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (hd j)) _)
  · have hneg : -s.val / 2 ≤ 0 := by linarith [s.property.1]
    exact (mul_le_mul
      (Real.rpow_le_one_of_one_le_of_nonpos (hd i) hneg)
      (Real.rpow_le_one_of_one_le_of_nonpos (hd j) hneg) (by positivity) zero_le_one).trans_eq
        (one_mul _)

/-- The column-difference profile in Lemma 5.8 is
positive for distinct columns and is at most the retained size. -/
theorem increment_profile_bounds (s : Riesz1.RieszExponent) (n : ℕ+)
    (i j l : Fin (n : ℕ)) (hjl : j ≠ l) :
    0 < (Nat.dist j.val l.val : ℝ) *
      ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val / 2) *
      (min (min (j.val + 1) ((n : ℕ) - j.val))
        (min (l.val + 1) ((n : ℕ) - l.val)) : ℕ) ^ (-1 - s.val / 2) ∧
    (Nat.dist j.val l.val : ℝ) *
      ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val / 2) *
      (min (min (j.val + 1) ((n : ℕ) - j.val))
        (min (l.val + 1) ((n : ℕ) - l.val)) : ℕ) ^ (-1 - s.val / 2) ≤ n := by
  have hd (a : Fin (n : ℕ)) : (1 : ℝ) ≤ (min (a.val + 1) ((n : ℕ) - a.val) : ℕ) :=
    by exact_mod_cast (depth_bounds n a).1
  have hmin : (1 : ℝ) ≤ (min (min (j.val + 1) ((n : ℕ) - j.val))
      (min (l.val + 1) ((n : ℕ) - l.val)) : ℕ) := by
    exact_mod_cast (le_min (depth_bounds n j).1 (depth_bounds n l).1)
  have hdist : 0 < Nat.dist j.val l.val := by
    have hne : j.val ≠ l.val := fun h => hjl (Fin.ext h)
    unfold Nat.dist; omega
  have hdistn : (Nat.dist j.val l.val : ℝ) ≤ n := by
    have hj := j.isLt
    have hl := l.isLt
    exact_mod_cast (show Nat.dist j.val l.val ≤ (n : ℕ) by unfold Nat.dist; omega)
  constructor
  · exact mul_pos (mul_pos (by exact_mod_cast hdist)
      (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (hd i)) _))
      (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hmin) _)
  · have ha := Real.rpow_le_one_of_one_le_of_nonpos (hd i)
      (show -s.val / 2 ≤ 0 by linarith [s.property.1])
    have hb := Real.rpow_le_one_of_one_le_of_nonpos hmin
      (show -1 - s.val / 2 ≤ 0 by linarith [s.property.1])
    calc
      _ ≤ (Nat.dist j.val l.val : ℝ) * 1 * 1 := by gcongr
      _ ≤ n := by simpa only [mul_one] using hdistn

/-- See Lemma 5.8 of the paper, compensation component: both entry
and ordinary column-difference pairings, with the full exceptional term.
The loss is one, and all prefactors are uniform on each compact positive
temperature interval. This theorem concerns the literal `Q`.
-/
theorem compensation_bilinear (s : Riesz1.RieszExponent)
    (βlo βhi ε Cθ : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi)
    (hε : 0 < ε) (hCθ : 1 ≤ Cθ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n : ℕ+) (m : ℕ), 2 ≤ (n : ℕ) →
      2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      let ν := (activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n hn θ ε false).comap
        ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
          EuclideanSpace ℝ (Fin (n : ℕ)))
      ∀ (φ η : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → ℝ)
        (Mφ Mη : ℝ), Measurable φ → Measurable η → 0 ≤ Mφ → 0 ≤ Mη →
        (∀ᵐ x ∂ν, |φ x| ≤ Mφ) → (∀ᵐ x ∂ν, |η x| ≤ Mη) →
      ∀ i j l : Fin (n : ℕ),
        let d := fun a : Fin (n : ℕ) => ((min (a.val + 1) ((n : ℕ) - a.val) : ℕ) : ℝ)
        let L := Real.sqrt (∫ x, φ x ^ 2 ∂ν) * Real.sqrt (∫ x, η x ^ 2 ∂ν)
        let E := C * Real.exp (-c * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη)
        Integrable (fun x => φ x * η x * ConditionalForces.compensationQ β s n m i j x) ν ∧
        |∫ x, φ x * η x * ConditionalForces.compensationQ β s n m i j x ∂ν| ≤
          C * (n : ℝ) ^ ε * (d i) ^ (-s.val / 2) * (d j) ^ (-s.val / 2) * L + E ∧
        Integrable (fun x => φ x * η x * (ConditionalForces.compensationQ β s n m i j x -
          ConditionalForces.compensationQ β s n m i l x)) ν ∧
        |∫ x, φ x * η x * (ConditionalForces.compensationQ β s n m i j x -
            ConditionalForces.compensationQ β s n m i l x) ∂ν| ≤
          C * (n : ℝ) ^ ε * (Nat.dist j.val l.val : ℝ) *
            (d i) ^ (-s.val / 2) * (min (d j) (d l)) ^ (-1 - s.val / 2) * L + E := by
  obtain ⟨D, hD, hmom⟩ := ConditionalForces.compensation_moments s βlo βhi ε Cθ hlo hle hε hCθ
  have hA : 0 < (s.val + 2) / s.val := by have := s.property.1; positivity
  obtain ⟨c, C, hc, hC, ht⟩ := PolynomialProfileTruncation.moment_truncation_ae
    (A := (s.val + 2) / s.val) (ε := ε) (κ := 1) (C := max D 1) (B := 1)
    hA hε zero_lt_one (le_max_right _ _)
  refine ⟨C, c, hC, hc, ?_⟩
  intro β hβ n m hn2 hper hn θ hcurv ν φ η Mφ Mη hφ hη hMφ hMη hφM hηM i j l d L E
  have : IsProbabilityMeasure ν := GoodBlocks.proper_active_probability _ _ _ _ _ _
  have hQ (a b : Fin (n : ℕ)) : Measurable (ConditionalForces.compensationQ β s n m a b) :=
    ((ConditionalForces.measurable_compensationB β s n m a).neg.sub
      (ConditionalForces.measurable_compensationB β s n m b)).add
      (ConditionalForces.measurable_compensationC β s n m)
  have hmoment (p : ℝ) (hp : 1 ≤ p) := hmom β hβ n m hper hn θ hcurv p hp
  have htE : C * Real.exp (-c * (n : ℝ) ^ (1 * ε / (2 * ((s.val + 2) / s.val)))) *
      (Mφ * Mη) ≤ E := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ (n : ℕ) by omega)
    have hd : GoodBlocks.coefficientTailPower s.val ε ≤ ε / (2 * ((s.val + 2) / s.val)) :=
      min_le_right _ _
    dsimp only [E]
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg hMφ hMη)
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.exp_le_exp.mpr
    simp only [one_mul]
    simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn1 hd) hc.le)
  let w := (d i) ^ (-s.val / 2) * (d j) ^ (-s.val / 2)
  have hw := entry_profile_bounds s n i j
  have hwN : w ≤ (n : ℝ) ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    exact hw.2.trans (by exact_mod_cast (show 1 ≤ (n : ℕ) by omega))
  obtain ⟨hi, hb⟩ := ht n hn2 ν w hw.1 hwN
    (ConditionalForces.compensationQ β s n m i j) φ η Mφ Mη (hQ i j) hφ hη hMφ hMη
    hφM hηM (fun p hp => ((hmoment p hp).2.2.1 i j).trans
      (ENNReal.ofReal_le_ofReal (by
        calc
          _ = D * p ^ ((s.val + 2) / s.val) * w := by dsimp [w, d]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left D 1) (by positivity)) hw.1.le)))
  have hb' : |∫ x, φ x * η x * ConditionalForces.compensationQ β s n m i j x ∂ν| ≤
      C * (n : ℝ) ^ ε * (d i) ^ (-s.val / 2) * (d j) ^ (-s.val / 2) * L + E := by
    apply hb.trans
    simpa only [one_mul, w, mul_assoc, L] using add_le_add_right htE
      (C * (n : ℝ) ^ ε * (d i) ^ (-s.val / 2) * (d j) ^ (-s.val / 2) * L)
  refine ⟨hi, hb', ?_, ?_⟩
  · by_cases hjl : j = l
    · subst l
      simp only [sub_self, mul_zero]
      exact integrable_zero _ _ _
    · let v := (Nat.dist j.val l.val : ℝ) * (d i) ^ (-s.val / 2) *
        (min (d j) (d l)) ^ (-1 - s.val / 2)
      have hv := increment_profile_bounds s n i j l hjl
      have hv' : 0 < v ∧ v ≤ (n : ℝ) ^ (1 : ℝ) := by
        simpa only [v, d, Nat.cast_min, Real.rpow_one] using hv
      exact (ht n hn2 ν v hv'.1 hv'.2 _ φ η Mφ Mη ((hQ i j).sub (hQ i l))
        hφ hη hMφ hMη hφM hηM (fun p hp => ((hmoment p hp).2.2.2 i j l).trans
          (ENNReal.ofReal_le_ofReal (by
            calc
              _ = D * p ^ ((s.val + 2) / s.val) * v := by
                dsimp [v, d]; simp only [Nat.cast_min]; ring
              _ ≤ _ := mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (le_max_left D 1) (by positivity)) hv'.1.le)))).1
  · by_cases hjl : j = l
    · subst l
      simp only [sub_self, mul_zero, integral_zero, abs_zero, Nat.dist_self, Nat.cast_zero,
        zero_mul, zero_add]
      dsimp only [E]
      positivity
    · let v := (Nat.dist j.val l.val : ℝ) * (d i) ^ (-s.val / 2) *
        (min (d j) (d l)) ^ (-1 - s.val / 2)
      have hv := increment_profile_bounds s n i j l hjl
      have hv' : 0 < v ∧ v ≤ (n : ℝ) ^ (1 : ℝ) := by
        simpa only [v, d, Nat.cast_min, Real.rpow_one] using hv
      have hb := (ht n hn2 ν v hv'.1 hv'.2 _ φ η Mφ Mη ((hQ i j).sub (hQ i l))
        hφ hη hMφ hMη hφM hηM (fun p hp => ((hmoment p hp).2.2.2 i j l).trans
          (ENNReal.ofReal_le_ofReal (by
            calc
              _ = D * p ^ ((s.val + 2) / s.val) * v := by
                dsimp [v, d]; simp only [Nat.cast_min]; ring
              _ ≤ _ := mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (le_max_left D 1) (by positivity)) hv'.1.le)))).2
      apply hb.trans
      simpa only [one_mul, v, mul_assoc, L] using add_le_add_right htE
        (C * (n : ℝ) ^ ε * (Nat.dist j.val l.val : ℝ) * (d i) ^ (-s.val / 2) *
          (min (d j) (d l)) ^ (-1 - s.val / 2) * L)

/-- See Lemma 5.8 of the paper, boundary multiplication component.
This gives both pairings on the good set for arbitrary square integrable
scalar tests. The loss exponent is fixed before temperature and tolerance.
-/
theorem boundary_bilinear (s : Riesz1.RieszExponent) (κ₀ : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ∀ β : InverseTemperature,
      ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ+) (m : ℕ),
      2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ),
      2 * (n : ℕ) ≤ (M : ℕ) →
      ∀ (ν : Measure (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)))
        (φ η : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → ℝ),
      Measurable φ → Measurable η → MemLp φ 2 ν → MemLp η 2 ν →
      ∀ i j l : Fin (n : ℕ),
        let G := GoodBlocks.properGoodEvent β s n m ε κ₀
        let R := BoundaryEntries.boundaryRemainder β s n m M hM hnM K
        let d := fun a : Fin (n : ℕ) => ((min (a.val + 1) ((n : ℕ) - a.val) : ℕ) : ℝ)
        let L := Real.sqrt (∫ x, φ x ^ 2 ∂ν) * Real.sqrt (∫ x, η x ^ 2 ∂ν)
        IntegrableOn (fun x => φ x * η x * R x i j) G ν ∧
        |∫ x in G, φ x * η x * R x i j ∂ν| ≤
          C * (n : ℝ) ^ (κ * ε) * (d i) ^ (-s.val / 2) * (d j) ^ (-s.val / 2) * L ∧
        IntegrableOn (fun x => φ x * η x * (R x i j - R x i l)) G ν ∧
        |∫ x in G, φ x * η x * (R x i j - R x i l) ∂ν| ≤
          C * (n : ℝ) ^ (κ * ε) * (Nat.dist j.val l.val : ℝ) *
            (d i) ^ (-s.val / 2) * (min (d j) (d l)) ^ (-1 - s.val / 2) * L := by
  obtain ⟨κ, hκ, ht⟩ := BoundaryEntries.boundary_intervals s κ₀
  refine ⟨κ, hκ, fun ε hε β => ?_⟩
  obtain ⟨C, hC, hb⟩ := ht ε hε β
  refine ⟨C, hC, ?_⟩
  intro n m hper M hM hnM K hhalf ν φ η hφ hη hφ2 hη2 i j l G R d L
  have hG : MeasurableSet G := GoodBlocks.measurableSet_properGoodEvent β s n m ε κ₀
  have hR (a b : Fin (n : ℕ)) : Measurable (fun x => R x a b) :=
    (BoundaryEntries.measurable_physicalCrossing β s n m a b).sub measurable_const
  obtain ⟨hi, hentry⟩ := PolynomialProfileTruncation.bounded_coefficient_pair
    hG (hR i j)
    (show 0 ≤ C * (n : ℝ) ^ (κ * ε) * (d i) ^ (-s.val / 2) * (d j) ^ (-s.val / 2) by positivity)
    (fun x hx => (hb n m hper M hM hnM K hhalf x hx i j l).1) hφ hη hφ2 hη2
  obtain ⟨hi', hinc⟩ := PolynomialProfileTruncation.bounded_coefficient_pair
    hG ((hR i j).sub (hR i l))
    (show 0 ≤ C * (n : ℝ) ^ (κ * ε) * (Nat.dist j.val l.val : ℝ) *
      (d i) ^ (-s.val / 2) * (min (d j) (d l)) ^ (-1 - s.val / 2) by positivity)
    (fun x hx => (hb n m hper M hM hnM K hhalf x hx i j l).2) hφ hη hφ2 hη2
  exact ⟨hi, hentry, hi', hinc⟩

/-- See Lemma 5.8 of the paper, refined event used for the covariance
component. Intersecting the physical good event with the compensation
cutoff preserves its exact temperature-independent stretched exponential
power. Both cutoff losses may be fixed before temperature.
-/
theorem refined_good_event (hRig : External.LongRangeRigidityLocallyUniform)
    (s : Riesz1.RieszExponent) (βlo βhi ε Cθ : ℝ)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (hε : 0 < ε) (hCθ : 1 ≤ Cθ) :
    ∃ D c : ℝ, 0 < D ∧ 0 < c ∧
      ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n : ℕ+) (m : ℕ), 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ κ₀ κ : ℝ, 1 ≤ κ₀ → 1 ≤ κ →
      let ν := (activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n hn θ ε false).comap
        ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
          EuclideanSpace ℝ (Fin (n : ℕ)))
      let G := GoodBlocks.properGoodEvent β s n m ε κ₀ ∩
        {x | ConditionalForces.compensationC β s n m x ≤
          (n : ℝ) ^ (κ * ε) * ((n : ℝ) + m + 1) ^ (-s.val)}
      MeasurableSet G ∧ ν Gᶜ ≤
        ENNReal.ofReal (D * Real.exp (-c * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε)) := by
  obtain ⟨B, b, hB, hb, hgood⟩ := GoodBlocks.proper_good_event hRig s hε hCθ βlo βhi hlo hle
  obtain ⟨C, hC, hmom⟩ := ConditionalForces.compensation_moments s βlo βhi ε Cθ hlo hle hε hCθ
  have hA : 0 < (s.val + 2) / s.val := by have := s.property.1; positivity
  obtain ⟨D, hD, htail⟩ := MomentEvent.moment_cutoff_tail hA hε hC
  refine ⟨B + D, min b 1, by positivity, lt_min hb zero_lt_one, ?_⟩
  intro β hβ n m hper hn θ hcurv κ₀ κ hκ₀ hκ ν G
  have : IsProbabilityMeasure ν := GoodBlocks.proper_active_probability _ _ _ _ _ _
  have hmeas : MeasurableSet G :=
    (GoodBlocks.measurableSet_properGoodEvent β s n m ε κ₀).inter
      (measurableSet_le (ConditionalForces.measurable_compensationC β s n m) measurable_const)
  refine ⟨hmeas, ?_⟩
  let t := (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε
  have hbad := hgood β hβ n m hper hn θ hcurv κ₀ hκ₀
  have hcut := htail n n.pos ν (ConditionalForces.compensationC β s n m)
    (ConditionalForces.measurable_compensationC β s n m) (((n : ℝ) + m + 1) ^ (-s.val)) κ
    (by positivity) hκ (fun p hp => (le_add_self).trans
      ((hmom β hβ n m hper hn θ hcurv p hp).1 ⟨0, n.pos⟩))
  have heq : Gᶜ = (GoodBlocks.properGoodEvent β s n m ε κ₀)ᶜ ∪
      {x | (n : ℝ) ^ (κ * ε) * ((n : ℝ) + m + 1) ^ (-s.val) <
        |ConditionalForces.compensationC β s n m x|} := by
    ext x
    simp only [G, mem_compl_iff, mem_inter_iff, mem_union, mem_ofPred_eq,
      abs_of_nonneg (ConditionalForces.compensationC_nonneg β s n m x), not_and_or, not_le]
  have ht : t ≤ (n : ℝ) ^ (ε / (2 * ((s.val + 2) / s.val))) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast n.pos) (min_le_right _ _)
  have hbad' : B * Real.exp (-b * t) ≤ B * Real.exp (-(min b 1) * t) := by
    gcongr
    exact min_le_left _ _
  have hcut' : D * Real.exp (-(n : ℝ) ^ (ε / (2 * ((s.val + 2) / s.val)))) ≤
      D * Real.exp (-(min b 1) * t) := by
    apply mul_le_mul_of_nonneg_left _ hD.le
    apply Real.exp_le_exp.mpr
    have hmin : min b 1 * t ≤ (n : ℝ) ^ (ε / (2 * ((s.val + 2) / s.val))) :=
      (mul_le_of_le_one_left (by dsimp [t]; positivity) (min_le_right b 1)).trans ht
    linarith
  rw [heq]
  calc
    _ ≤ ν (GoodBlocks.properGoodEvent β s n m ε κ₀)ᶜ +
        ν {x | (n : ℝ) ^ (κ * ε) * ((n : ℝ) + m + 1) ^ (-s.val) <
          |ConditionalForces.compensationC β s n m x|} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (B * Real.exp (-b * t)) +
        ENNReal.ofReal (D * Real.exp (-(n : ℝ) ^ (ε / (2 * ((s.val + 2) / s.val))))) :=
      add_le_add hbad hcut
    _ ≤ ENNReal.ofReal (B * Real.exp (-(min b 1) * t)) +
        ENNReal.ofReal (D * Real.exp (-(min b 1) * t)) :=
      add_le_add (ENNReal.ofReal_le_ofReal hbad') (ENNReal.ofReal_le_ofReal hcut')
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

/-- See Lemma 5.8 of the paper, conditional covariance component
before integration over the retained coordinates. This proves the entry
envelope on the whole carrier and the sharper column-difference envelope
on the physical good event. The forces realize the ambient energy,
and their finite second moments are part of the conclusion.
-/
theorem physical_covariance_envelopes (s : Riesz1.RieszExponent)
    (κ₀ : ℝ) (hκ₀ : 0 < κ₀) :
    ∃ κ > 0, ∀ (β : InverseTemperature) (ε : ℝ), 0 < ε →
      ∃ C > 0, ∀ (n : ℕ+) (m : ℕ), 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
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
  obtain ⟨κ, hκ, ht⟩ := ConditionalForces.conditional_force_variances s κ₀ hκ₀
  refine ⟨κ, hκ, fun β ε hε => ?_⟩
  obtain ⟨C, hC, hb⟩ := ht β ε hε
  refine ⟨C, hC, fun n m hper => ?_⟩
  obtain ⟨U, hU, hv, hf⟩ := hb n m hper
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

end Riesz2.PerturbationBounds
