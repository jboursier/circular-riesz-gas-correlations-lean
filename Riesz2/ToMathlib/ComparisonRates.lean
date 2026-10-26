/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.MomentEventBounds

/-!
# Combining polynomial and stretched exponential comparison rates

Absorption keeps the power of the stretched exponential unchanged.
The finite-size estimate needs no restriction on the polynomial exponent.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace Riesz2.ComparisonRates

/-- A global bounded-size estimate is absorbed into the exponential
remainder, including when the polynomial prefactor has a negative power. -/
theorem bounded_sizes_remainder (n₀ : ℕ) (B q c δ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → n ≤ n₀ →
      B ≤ C * (n : ℝ) ^ q * Real.exp (-c * (n : ℝ) ^ δ) := by
  classical
  let w := fun k : ℕ => (k + 1 : ℝ) ^ q * Real.exp (-c * (k + 1 : ℝ) ^ δ)
  let C := 1 + ∑ k ∈ Finset.range n₀, |B / w k|
  have hC : 0 < C := by
    dsimp only [C]
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  refine ⟨C, hC, fun n hn hn₀ => ?_⟩
  have hk : n - 1 ∈ Finset.range n₀ := Finset.mem_range.mpr (by omega)
  have hw : 0 < w (n - 1) := by dsimp [w]; positivity
  have hh : |B / w (n - 1)| ≤ C := by
    have hs := Finset.single_le_sum (f := fun k => |B / w k|)
      (fun _ _ => abs_nonneg _) hk
    dsimp only [C]
    linarith
  have hb : B ≤ C * w (n - 1) := (div_le_iff₀ hw).mp ((le_abs_self _).trans hh)
  have he : (n - 1 : ℕ) + 1 = n := by omega
  have he' : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by exact_mod_cast he
  simpa only [w, he', mul_assoc] using hb

/-- Put an additive exponential error inside the polynomial prefactor.
The rate is halved. Its power is retained, independently of the constants. -/
theorem factor_remainder (q δ C₁ C₂ c : ℝ)
    (hδ : 0 < δ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ x A D : ℝ, 1 ≤ x → 0 ≤ A → 0 ≤ D →
      C₁ * x ^ q * A + C₂ * Real.exp (-c * x ^ δ) * D ≤
        C * x ^ q * (A + Real.exp (-(c / 2) * x ^ δ) * D) := by
  obtain ⟨K, hK, hbound⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := -q) hδ (show c / 2 < c by linarith)
  refine ⟨C₁ + C₂ * K + 1, by positivity, fun x A D hx hA hD => ?_⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have he : Real.exp (-c * x ^ δ) ≤ x ^ q * (K * Real.exp (-(c / 2) * x ^ δ)) := by
    have hh := mul_le_mul_of_nonneg_left (hbound x hx) (Real.rpow_nonneg hx0.le q)
    have hp : x ^ q * x ^ (-q) = 1 := by rw [← Real.rpow_add hx0]; simp
    simpa only [← mul_assoc, hp, one_mul] using hh
  have h₁ : C₁ * x ^ q * A ≤ (C₁ + C₂ * K + 1) * x ^ q * A := by
    gcongr
    nlinarith [mul_nonneg hC₂ hK]
  have h₂ : C₂ * Real.exp (-c * x ^ δ) * D ≤
      (C₁ + C₂ * K + 1) * x ^ q * Real.exp (-(c / 2) * x ^ δ) * D := by
    calc
      _ ≤ C₂ * (x ^ q * (K * Real.exp (-(c / 2) * x ^ δ))) * D := by gcongr
      _ = (C₂ * K) * x ^ q * Real.exp (-(c / 2) * x ^ δ) * D := by ring
      _ ≤ _ := by gcongr; linarith
  exact (add_le_add h₁ h₂).trans_eq (by ring)

/-- Combine the sum of two averaging errors with the comparison of the
two common-base averages. The tail power is the minimum of the input
powers, chosen without reference to their prefactors. -/
theorem combine_errors (q δ₁ δ₂ C₁ C₂ c₁ c₂ : ℝ)
    (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ x A D u v a b : ℝ,
      1 ≤ x → 0 ≤ A → 0 ≤ D →
      |a-u| + |b-v| ≤ C₁*x^q*A + C₁*Real.exp (-c₁*x^δ₁)*D →
      |a-b| ≤ C₂*x^q*(A + Real.exp (-c₂*x^δ₂)*D) →
      |u-v| ≤ C*x^q*(A + Real.exp (-c*x^(min δ₁ δ₂))*D) := by
  let c₀ := min c₁ c₂
  let δ := min δ₁ δ₂
  have hc₀ : 0 < c₀ := lt_min hc₁ hc₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  obtain ⟨C₀, hC₀, hfactor⟩ := factor_remainder q δ C₁ C₁ c₀ hδ hC₁ hC₁ hc₀
  refine ⟨C₀+C₂, c₀/2, by positivity, by positivity, ?_⟩
  intro x A D u v a b hx hA hD havg hcomp
  have htail (d c : ℝ) (hd : δ ≤ d) (hc : c₀ ≤ c) :
      Real.exp (-c*x^d) ≤ Real.exp (-(c₀/2)*x^δ) := by
    apply Real.exp_le_exp.mpr
    have hp := Real.rpow_le_rpow_of_exponent_le hx hd
    have hc' : c₀/2 ≤ c := by linarith
    have ht := mul_le_mul hc' hp (by positivity : 0 ≤ x^δ) (by linarith : 0 ≤ c)
    linarith
  have htail₁ : Real.exp (-c₁*x^δ₁) ≤ Real.exp (-c₀*x^δ) := by
    apply Real.exp_le_exp.mpr
    have hp := Real.rpow_le_rpow_of_exponent_le hx (min_le_left δ₁ δ₂)
    have ht := mul_le_mul (min_le_left c₁ c₂) hp (by positivity : 0 ≤ x^δ) hc₁.le
    linarith
  have ha' : |a-u| + |b-v| ≤
      C₀*x^q*(A+Real.exp (-(c₀/2)*x^δ)*D) :=
    (havg.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htail₁ hC₁) hD))).trans
        (hfactor x A D hx hA hD)
  have hb' : |a-b| ≤ C₂*x^q*(A+Real.exp (-(c₀/2)*x^δ)*D) := by
    apply hcomp.trans
    exact mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (htail δ₂ c₂ (min_le_right _ _) (min_le_right _ _)) hD))
      (mul_nonneg hC₂ (Real.rpow_nonneg (by positivity) _))
  have htri : |u-v| ≤ (|a-u|+|b-v|)+|a-b| := by
    have hh := (abs_sub_le u a v).trans
      (add_le_add le_rfl (abs_sub_le a b v))
    rw [abs_sub_comm u a] at hh
    linarith
  exact htri.trans ((add_le_add ha' hb').trans_eq (by dsimp [δ]; ring))

/-- Absorb the overlap loss in the exceptional-event estimate. Both the
second moment and the bad probability carry the domination factor `b`.
Its polynomial bound is absorbed while retaining the tail power `δ`. -/
theorem exceptional_overlap_loss (r q δ A H T c : ℝ)
    (hδ : 0 < δ) (hA : 0 ≤ A) (hH : 0 ≤ H) (hT : 0 ≤ T) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ x b D : ℝ, 1 ≤ x → 0 ≤ b → b ≤ A*x^r → 0 ≤ D →
      (Real.sqrt (b*(H*D^2))+Real.sqrt (b*(H*D^2))) *
        Real.sqrt (b*(T*Real.exp (-c*x^δ)+T*Real.exp (-c*x^δ))) ≤
          C*x^q*Real.exp (-(c/4)*x^δ)*D := by
  obtain ⟨K, hK, hpoly⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := r-q) (δ := δ) (c := c/2) (c' := c/4) hδ (by linarith)
  let B := 2*A*Real.sqrt H*Real.sqrt (2*T)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B*K+1, by positivity, fun x b D hx hb hbA hD => ?_⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have he : Real.sqrt (Real.exp (-c*x^δ)) = Real.exp (-(c/2)*x^δ) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
    congr 1
    ring
  have hs₁ : Real.sqrt (b*(H*D^2)) = Real.sqrt b*Real.sqrt H*D := by
    rw [Real.sqrt_mul hb, Real.sqrt_mul hH, Real.sqrt_sq hD, mul_assoc]
  have hs₂ : Real.sqrt (b*(T*Real.exp (-c*x^δ)+T*Real.exp (-c*x^δ))) =
      Real.sqrt b*Real.sqrt (2*T)*Real.exp (-(c/2)*x^δ) := by
    rw [show T*Real.exp (-c*x^δ)+T*Real.exp (-c*x^δ) =
        (2*T)*Real.exp (-c*x^δ) by ring,
      Real.sqrt_mul hb, Real.sqrt_mul (by positivity : 0 ≤ 2*T), he, mul_assoc]
  rw [hs₁, hs₂]
  have hrate : x^r*Real.exp (-(c/2)*x^δ) ≤ x^q*(K*Real.exp (-(c/4)*x^δ)) := by
    have hh := mul_le_mul_of_nonneg_left (hpoly x hx) (Real.rpow_nonneg hx0.le q)
    have hp : x^q*x^(r-q) = x^r := by rw [← Real.rpow_add hx0]; congr 1; ring
    simpa only [← mul_assoc, hp] using hh
  calc
    _ = 2*b*Real.sqrt H*Real.sqrt (2*T)*Real.exp (-(c/2)*x^δ)*D := by
      have heq := Real.sq_sqrt hb
      calc
        _ = 2*(Real.sqrt b)^2*Real.sqrt H*Real.sqrt (2*T)*Real.exp (-(c/2)*x^δ)*D := by ring
        _ = _ := by rw [heq]
    _ ≤ B*(x^r*Real.exp (-(c/2)*x^δ))*D := by
      have hh := mul_le_mul_of_nonneg_right hbA
        (show 0 ≤ 2*Real.sqrt H*Real.sqrt (2*T)*Real.exp (-(c/2)*x^δ)*D by positivity)
      dsimp only [B]
      nlinarith only [hh]
    _ ≤ B*(x^q*(K*Real.exp (-(c/4)*x^δ)))*D :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrate hB) hD
    _ ≤ (B*K+1)*x^q*Real.exp (-(c/4)*x^δ)*D := by
      have hh : 0 ≤ x^q*Real.exp (-(c/4)*x^δ)*D := by positivity
      nlinarith only [hh]

end Riesz2.ComparisonRates
