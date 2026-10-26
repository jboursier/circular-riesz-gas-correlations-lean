/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.UnconstrainedGlobalDecay
public import Riesz2.DecayLong.LocalizedBoundaryPart7

/-!
# The unrestricted localization improvement

The unrestricted improvement in the proof of Proposition 5.15 is assembled
from the constrained improvement and the current point-source estimates.
Finite superpositions remain in the full scalar form domains.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Finset
open scoped BigOperators Classical

namespace Riesz2.OptimalLocalizationUnconstrained

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

/-- The regularized cyclic radius is at most the cycle size, also at size two. -/
theorem radius_le_size (m : ℕ+) (hm : 2 ≤ (m : ℕ)) (i j : Fin (m : ℕ)) :
    weightRadius m i j ≤ (m : ℝ) := by
  have hd := Riesz1.APG.cyclicIndexDistance_le_half (N := m) i j
  have hh : 1 + Riesz1.cyclicIndexDistance m i j ≤ (m : ℕ) := by omega
  dsimp only [weightRadius]
  exact_mod_cast hh

/-- See the proof of Proposition 5.15 in the paper: a cyclic profile has its
summable, logarithmic and subcritical bounds in one uniform expression. -/
theorem profile_sum (u : ℝ) (hu : 0 < u) :
    ∃ B : ℝ, 0 < B ∧ ∀ (m : ℕ+) (_hm : 2 ≤ (m : ℕ)) (j : Fin (m : ℕ)),
      (∑ i, weightRadius m j i ^ (-u)) ≤
        B * (1 + Real.log (2 * (m : ℝ))) * (1 + (m : ℝ) ^ (1 - u)) := by
  obtain ⟨B, hB, hb⟩ := weight_sums_bound u hu
  refine ⟨B, hB, fun m hm j => ?_⟩
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ (m : ℕ) by omega)
  have hlog : 0 ≤ Real.log (2 * (m : ℝ)) := Real.log_nonneg (by linarith)
  have hp : 0 ≤ (m : ℝ) ^ (1 - u) := by positivity
  have hfilter : univ.filter (fun i => weightRadius m i j ≤ (m : ℝ)) = univ := by
    apply filter_eq_self.mpr
    exact fun i _ => radius_le_size m hm i j
  have heq : (∑ i, weightRadius m j i ^ (-u)) = ∑ i, weightRadius m i j ^ (-u) := by
    apply sum_congr rfl
    intro i _
    congr 1
    exact weightRadius_eq_comm m j i
  rw [heq]
  have hh := hb m hm (m : ℝ) hm1 le_rfl j
  rw [hfilter] at hh
  rcases lt_trichotomy u 1 with h | h | h
  · have hL : 1 ≤ 1 + Real.log (2 * (m : ℝ)) := by linarith
    calc
      _ ≤ B * (m : ℝ) ^ (1 - u) := hh.1 h
      _ ≤ B * ((1 + Real.log (2 * (m : ℝ))) * (1 + (m : ℝ) ^ (1 - u))) := by
        apply mul_le_mul_of_nonneg_left _ hB.le
        nlinarith only [mul_nonneg (show 0 ≤ Real.log (2 * (m : ℝ)) from hlog)
          (show 0 ≤ 1 + (m : ℝ) ^ (1 - u) by positivity)]
      _ = _ := by ring
  · calc
      _ ≤ B * Real.log (2 * (m : ℝ)) := hh.2.1 h
      _ ≤ B * ((1 + Real.log (2 * (m : ℝ))) * (1 + (m : ℝ) ^ (1 - u))) := by
        apply mul_le_mul_of_nonneg_left _ hB.le
        nlinarith only [mul_nonneg (show 0 ≤ 1 + Real.log (2 * (m : ℝ)) by positivity) hp]
      _ = _ := by ring
  · calc
      _ ≤ B := (hh.2.2 h).1
      _ ≤ B * ((1 + Real.log (2 * (m : ℝ))) * (1 + (m : ℝ) ^ (1 - u))) := by
        have hp1 : 1 ≤ 1 + (m : ℝ) ^ (1 - u) := by linarith
        have hL1 : 1 ≤ 1 + Real.log (2 * (m : ℝ)) := by linarith
        have hh := one_le_mul_of_one_le_of_one_le hL1 hp1
        nlinarith only [hh, hB]
      _ = _ := by ring

/-- See the proof of Proposition 5.15 in the paper: multiplication of the
profile sum by the constant-mode source size gains exactly `1 - s`.
The logarithmic loss costs one fixed power of `n^ε`. -/
theorem scaled_profile_sum (s : Riesz1.RieszExponent) (u : ℝ) (hu : 0 < u)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, 0 < L ∧ ∀ (n m : ℕ+) (_hm : 2 ≤ (m : ℕ)),
      2 ≤ (n : ℕ) → (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
      ∀ j : Fin (m : ℕ),
      (m : ℝ) ^ (-(2 - s.val)) * (∑ i, weightRadius m j i ^ (-u)) ≤
        L * (n : ℝ) ^ ε *
          ((m : ℝ) ^ (-(2 - s.val)) + (m : ℝ) ^ (-(u + 1 - s.val))) := by
  obtain ⟨B, hB, hb⟩ := profile_sum u hu
  obtain ⟨D, hd⟩ := log_bound_global s.val 1 1 ε s.property.1 s.property.2
    zero_lt_one zero_le_one hε
  refine ⟨B * (1 + |D|), by positivity, fun n m hm hn hmn j => ?_⟩
  have hm0 : (0 : ℝ) < m := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ (n : ℕ) by omega)
  have hP : 1 ≤ (n : ℝ) ^ ε := Real.one_le_rpow hn1 hε.le
  have hlog : Real.log (2 * (m : ℝ)) ≤ |D| * (n : ℝ) ^ ε := by
    have hh := hd (n : ℕ) (m : ℕ) hn hm hmn
    simp only [Real.rpow_one, one_mul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_abs_self D) (by positivity))
  have hL : 1 + Real.log (2 * (m : ℝ)) ≤ (1 + |D|) * (n : ℝ) ^ ε := by
    nlinarith only [hP, hlog]
  have hexp : (m : ℝ) ^ (-(2 - s.val)) * (1 + (m : ℝ) ^ (1 - u)) =
      (m : ℝ) ^ (-(2 - s.val)) + (m : ℝ) ^ (-(u + 1 - s.val)) := by
    rw [mul_add, mul_one, ← Real.rpow_add hm0]
    congr 2
    ring
  calc
    _ ≤ (m : ℝ) ^ (-(2 - s.val)) *
        (B * (1 + Real.log (2 * (m : ℝ))) * (1 + (m : ℝ) ^ (1 - u))) :=
      mul_le_mul_of_nonneg_left (hb m hm j) (by positivity)
    _ ≤ (m : ℝ) ^ (-(2 - s.val)) *
        (B * ((1 + |D|) * (n : ℝ) ^ ε) * (1 + (m : ℝ) ^ (1 - u))) := by
      gcongr
    _ = _ := by rw [← hexp]; ring

/-- See the proof of Proposition 5.15 in the paper: every size power in the
remainder is bounded by the improved power of a target radius. -/
theorem size_power_le_radius (m r p q : ℝ) (hr : 1 ≤ r) (hrm : r ≤ m)
    (hq : 0 ≤ q) (hqp : q ≤ p) : m ^ (-p) ≤ r ^ (-q) := by
  have hm1 : 1 ≤ m := hr.trans hrm
  exact (Real.rpow_le_rpow_of_exponent_le hm1 (neg_le_neg hqp)).trans
    (Real.rpow_le_rpow_of_nonpos (by linarith) hrm (neg_nonpos.mpr hq))

/-- Finite source superposition for the proof of Proposition 5.15,
retaining the separate value and energy profiles of the induction hypothesis. -/
theorem superposition_internal (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (m : ℕ+) (M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hMb : ∃ B : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ B)
    (A G D : ℝ)
    (hp : ∀ (χ : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ)),
      ∃ u : Fin (m : ℕ) → Q.1,
        WeightedWeakSolution Q M ⊤ (fun i => if i = i₀ then χ else 0) u ∧
        ∀ j, ‖(u j).val‖ ≤ D * weightRadius m j i₀ ^ (-A) * ‖χ‖ ∧
          Real.sqrt (Q.2 (u j) (u j)) ≤ D * weightRadius m j i₀ ^ (-G) * ‖χ‖)
    (f : Fin (m : ℕ) → Lp ℝ 2 ν) :
    ∃ u : Fin (m : ℕ) → Q.1, WeightedWeakSolution Q M ⊤ f u ∧
      ∀ j, ‖(u j).val‖ ≤ D * ∑ i, weightRadius m j i ^ (-A) * ‖f i‖ ∧
        Real.sqrt (Q.2 (u j) (u j)) ≤ D * ∑ i, weightRadius m j i ^ (-G) * ‖f i‖ := by
  choose u hu hb using fun i => hp (f i) i
  let z := fun j => ∑ i, u i j
  have hz : WeightedWeakSolution Q M ⊤ f z := by
    simpa only [Finset.sum_ite_eq, Finset.mem_univ, ite_true] using
      LocalizedBoundary.weak_sum_internal Q M hMm hMb _ u hu
  refine ⟨z, hz, fun j => ⟨?_, ?_⟩⟩
  · calc
      _ ≤ ∑ i, ‖(u i j).val‖ := by
        simpa only [z, Submodule.coe_sum] using norm_sum_le univ (fun i => (u i j).val)
      _ ≤ ∑ i, D * weightRadius m j i ^ (-A) * ‖f i‖ := sum_le_sum fun i _ => (hb i j).1
      _ = _ := by simp only [mul_sum, mul_assoc]
  · calc
      _ ≤ ∑ i, Real.sqrt (Q.2 (u i j) (u i j)) :=
        LocalizedBoundary.energy_sqrt_sum_internal Q hQ univ (fun i => u i j)
      _ ≤ ∑ i, D * weightRadius m j i ^ (-G) * ‖f i‖ := sum_le_sum fun i _ => (hb i j).2
      _ = _ := by simp only [mul_sum, mul_assoc]

/-- The literal row-error source in the proof of Proposition 5.15
has an L² component bound. The row bound is an almost-everywhere bound. -/
theorem row_source_norm_internal (m : ℕ+) (β B : ℝ) (hβ : 0 ≤ β) (_hB : 0 ≤ B)
    (E : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hrow : ∀ᵐ x ∂ν, ∀ i, ∑ j, |E x i j| ≤ B)
    (f : Lp ℝ 2 ν) (g : Fin (m : ℕ) → Lp ℝ 2 ν)
    (hg : ∀ i, ∀ᵐ x ∂ν, g i x = -β * f x * ∑ j, E x i j) :
    ∀ i, ‖g i‖ ≤ (β * B) * ‖f‖ := by
  intro i
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hrow, hg i] with x hx hgx
  rw [hgx]
  simp only [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hβ]
  calc
    β * |f x| * |∑ j, E x i j| ≤ β * |f x| * B :=
      mul_le_mul_of_nonneg_left ((abs_sum_le_sum_abs _ _).trans (hx i)) (by positivity)
    _ = _ := by ring

/-- Summing the current point-source profile against a componentwise small
source gives the improved radius power. This includes the exponent-one case
through the explicit logarithmic loss in `scaled_profile_sum`. -/
theorem convolution_improvement_internal (s : Riesz1.RieszExponent)
    (n m : ℕ+) (hm : 2 ≤ (m : ℕ)) (i₀ j : Fin (m : ℕ))
    (u q ε D B L F : ℝ) (hD : 0 ≤ D) (hB : 0 ≤ B) (hL : 0 ≤ L) (hF : 0 ≤ F)
    (hq : 0 ≤ q) (hqp : q ≤ 2 - s.val) (hqu : q ≤ u + 1 - s.val)
    (hprofile : (m : ℝ) ^ (-(2 - s.val)) * (∑ i, weightRadius m j i ^ (-u)) ≤
      L * (n : ℝ) ^ ε *
        ((m : ℝ) ^ (-(2 - s.val)) + (m : ℝ) ^ (-(u + 1 - s.val))))
    (a : Fin (m : ℕ) → ℝ)
    (ha : ∀ i, a i ≤ B * (m : ℝ) ^ (-(2 - s.val)) * F) :
    D * (∑ i, weightRadius m j i ^ (-u) * a i) ≤
      (2 * D * B * L * (n : ℝ) ^ ε) * weightRadius m j i₀ ^ (-q) * F := by
  have hr := one_le_weightRadius m j i₀
  have hrm := radius_le_size m hm j i₀
  have hp := size_power_le_radius (m : ℝ) _ (2 - s.val) q hr hrm hq hqp
  have hu := size_power_le_radius (m : ℝ) _ (u + 1 - s.val) q hr hrm hq hqu
  calc
    _ ≤ D * (∑ i, weightRadius m j i ^ (-u) *
        (B * (m : ℝ) ^ (-(2 - s.val)) * F)) := by
      apply mul_le_mul_of_nonneg_left _ hD
      exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (ha i) (by
        exact Real.rpow_nonneg (zero_le_one.trans (one_le_weightRadius m j i)) _)
    _ = (D * B * F) * ((m : ℝ) ^ (-(2 - s.val)) *
        (∑ i, weightRadius m j i ^ (-u))) := by rw [← sum_mul]; ring
    _ ≤ (D * B * F) * (L * (n : ℝ) ^ ε *
        ((m : ℝ) ^ (-(2 - s.val)) + (m : ℝ) ^ (-(u + 1 - s.val)))) :=
      mul_le_mul_of_nonneg_left hprofile (by positivity)
    _ ≤ (D * B * F) * (L * (n : ℝ) ^ ε *
        (weightRadius m j i₀ ^ (-q) + weightRadius m j i₀ ^ (-q))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left (add_le_add hp hu) (by positivity)
    _ = _ := by ring

/-- See the proof of Proposition 5.15 in the paper: the correction equation
gains the unrestricted improved exponents by superposition and uniqueness.
The hypotheses are the current point-source estimates. -/
theorem remainder_improvement_internal (s : Riesz1.RieszExponent)
    (n m : ℕ+) (hm : 2 ≤ (m : ℕ)) (i₀ : Fin (m : ℕ))
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hMb : ∃ B : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ B)
    (β a : ℝ) (hβ : 0 < β) (ha : 0 < a)
    (hl : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
      ∀ z : Fin (m : ℕ) → ℝ, a * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j)
    (A G ε D B L F : ℝ) (hD : 0 ≤ D) (hB : 0 ≤ B) (hL : 0 ≤ L) (hF : 0 ≤ F)
    (hA : 0 ≤ A + 1 - s.val) (hG : 0 ≤ G + 1 - s.val)
    (hp : ∀ (χ : Lp ℝ 2 ν) (i : Fin (m : ℕ)),
      ∃ z : Fin (m : ℕ) → Q.1,
        WeightedWeakSolution Q (fun x => β • M x) ⊤ (fun k => if k = i then χ else 0) z ∧
        ∀ j, ‖(z j).val‖ ≤ D * weightRadius m j i ^ (-A) * ‖χ‖ ∧
          Real.sqrt (Q.2 (z j) (z j)) ≤ D * weightRadius m j i ^ (-G) * ‖χ‖)
    (hsa : ∀ j, (m : ℝ) ^ (-(2 - s.val)) * (∑ i, weightRadius m j i ^ (-A)) ≤
      L * (n : ℝ) ^ ε *
        ((m : ℝ) ^ (-(2 - s.val)) + (m : ℝ) ^ (-(A + 1 - s.val))))
    (hsg : ∀ j, (m : ℝ) ^ (-(2 - s.val)) * (∑ i, weightRadius m j i ^ (-G)) ≤
      L * (n : ℝ) ^ ε *
        ((m : ℝ) ^ (-(2 - s.val)) + (m : ℝ) ^ (-(G + 1 - s.val))))
    (g : Fin (m : ℕ) → Lp ℝ 2 ν)
    (hg : ∀ i, ‖g i‖ ≤ B * (m : ℝ) ^ (-(2 - s.val)) * F)
    (w : Fin (m : ℕ) → Q.1)
    (hw : WeightedWeakSolution Q (fun x => β • M x) ⊤ g w) :
    ∀ j, ‖(w j).val‖ ≤ (2 * D * B * L * (n : ℝ) ^ ε) *
        weightRadius m j i₀ ^ (-(min (2 - s.val) (A + 1 - s.val))) * F ∧
      Real.sqrt (Q.2 (w j) (w j)) ≤ (2 * D * B * L * (n : ℝ) ^ ε) *
        weightRadius m j i₀ ^ (-(min ((3 - s.val) / 2) (G + 1 - s.val))) * F := by
  obtain ⟨z, hz, hb⟩ := superposition_internal Q hQ m (fun x => β • M x)
    (fun i j => (hMm i j).const_mul β) (by
      obtain ⟨B₀, hb₀⟩ := hMb
      refine ⟨β * B₀, hb₀.mono (fun x hx i j => ?_)⟩
      simpa only [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hβ] using
        mul_le_mul_of_nonneg_left (hx i j) hβ.le) A G D hp g
  have huniq := (AbstractEquation.existence_energy Q hQ β hβ M hMm a ha hl ⊤ g).1
  have hzw : z = w := huniq.unique hz hw
  subst z
  intro j
  constructor
  · exact (hb j).1.trans (convolution_improvement_internal s n m hm i₀ j
      A (min (2 - s.val) (A + 1 - s.val)) ε D B L F hD hB hL hF
      (le_min (by linarith [s.property.2]) hA) (min_le_left _ _) (min_le_right _ _)
      (hsa j) (fun i => ‖g i‖) hg)
  · exact (hb j).2.trans (convolution_improvement_internal s n m hm i₀ j
      G (min ((3 - s.val) / 2) (G + 1 - s.val)) ε D B L F hD hB hL hF
      (le_min (by linarith [s.property.2]) hG)
      ((min_le_left _ _).trans (by linarith [s.property.2])) (min_le_right _ _)
      (hsg j) (fun i => ‖g i‖) hg)

/-- Adding the constrained field, the scalar correction and the remainder
retains both improved profiles in the proof of Proposition 5.15.
This lemma uses the exact decomposition, including the scalar gradient term. -/
theorem assemble_internal (s : Riesz1.RieszExponent) (m : ℕ+) (hm : 2 ≤ (m : ℕ))
    (i₀ : Fin (m : ℕ)) (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (A G Dv Df Dw F : ℝ) (hDf : 0 ≤ Df) (hF : 0 ≤ F)
    (hA : 0 ≤ A + 1 - s.val) (hG : 0 ≤ G + 1 - s.val)
    (u v : Fin (m : ℕ) → Q.1) (f : Q.1)
    (hv : ∀ j, ‖(v j).val‖ ≤ Dv *
        weightRadius m j i₀ ^ (-(min (2 - s.val) (A + 1 - s.val))) * F ∧
      Real.sqrt (Q.2 (v j) (v j)) ≤ Dv *
        weightRadius m j i₀ ^ (-(min ((3 - s.val) / 2) (G + 1 - s.val))) * F)
    (hf : ‖f.val‖ ≤ Df * (m : ℝ) ^ (-(2 - s.val)) * F)
    (hfg : Real.sqrt (Q.2 f f) ≤ Df * (m : ℝ) ^ (-(3 - s.val) / 2) * F)
    (hw : ∀ j, ‖(u j - v j - f).val‖ ≤ Dw *
        weightRadius m j i₀ ^ (-(min (2 - s.val) (A + 1 - s.val))) * F ∧
      Real.sqrt (Q.2 (u j - v j - f) (u j - v j - f)) ≤ Dw *
        weightRadius m j i₀ ^ (-(min ((3 - s.val) / 2) (G + 1 - s.val))) * F) :
    ∀ j, ‖(u j).val‖ ≤ (Dv + Df + Dw) *
        weightRadius m j i₀ ^ (-(min (2 - s.val) (A + 1 - s.val))) * F ∧
      Real.sqrt (Q.2 (u j) (u j)) ≤ (Dv + Df + Dw) *
        weightRadius m j i₀ ^ (-(min ((3 - s.val) / 2) (G + 1 - s.val))) * F := by
  intro j
  have hr := one_le_weightRadius m j i₀
  have hrm := radius_le_size m hm j i₀
  have hfv : ‖f.val‖ ≤ Df *
      weightRadius m j i₀ ^ (-(min (2 - s.val) (A + 1 - s.val))) * F := by
    exact hf.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (size_power_le_radius (m : ℝ) _ _ _ hr hrm
        (le_min (by linarith [s.property.2]) hA) (min_le_left _ _)) hDf) hF)
  have hfgr : Real.sqrt (Q.2 f f) ≤ Df *
      weightRadius m j i₀ ^ (-(min ((3 - s.val) / 2) (G + 1 - s.val))) * F := by
    apply hfg.trans
    have hh := size_power_le_radius (m : ℝ) _ ((3 - s.val) / 2) _ hr hrm
      (le_min (by linarith [s.property.2]) hG) (min_le_left _ _)
    rw [show -((3 - s.val) / 2) = -(3 - s.val) / 2 by ring] at hh
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hDf) hF
  have hid : (v j + f) + (u j - v j - f) = u j := by abel
  constructor
  · have ht : ‖(u j).val‖ ≤ ‖(v j).val‖ + ‖f.val‖ + ‖(u j - v j - f).val‖ := by
      conv_lhs => rw [← hid]
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    have hb := add_le_add (add_le_add (hv j).1 hfv) (hw j).1
    exact ht.trans (hb.trans_eq (by ring))
  · have ht : Real.sqrt (Q.2 (u j) (u j)) ≤
        Real.sqrt (Q.2 (v j) (v j)) + Real.sqrt (Q.2 f f) +
          Real.sqrt (Q.2 (u j - v j - f) (u j - v j - f)) := by
      conv_lhs => rw [← hid]
      exact (LocalizedBoundary.energy_sqrt_add_internal Q hQ _ _).trans
        (add_le_add (LocalizedBoundary.energy_sqrt_add_internal Q hQ _ _) le_rfl)
    have hb := add_le_add (add_le_add (hv j).2 hfgr) (hw j).2
    exact ht.trans (hb.trans_eq (by ring))

/-- Uniform constant bookkeeping for the proof of Proposition 5.15.
Prefactors enter the final prefactor. The loss exponent depends only on the
preceding fixed loss exponents and an additional unit for logarithms. -/
theorem loss_assembly_internal (n : ℕ+) (ε κc κm κp κe Cc Cm Cp Ce βhi L : ℝ)
    (hε : 0 < ε) (hκc : 0 < κc) (hκm : 0 < κm) (hκp : 0 < κp) (hκe : 0 < κe)
    (hCc : 0 ≤ Cc) (hCm : 0 ≤ Cm) (hCp : 0 ≤ Cp) (hCe : 0 ≤ Ce)
    (hβhi : 0 ≤ βhi) (hL : 0 ≤ L) :
    let k := κc + κm + κp + κe + 1
    Cc * (n : ℝ) ^ (κc * ε) + Cm * (n : ℝ) ^ (κm * ε) +
      2 * (Cp * (n : ℝ) ^ (κp * ε)) *
        (βhi * (Ce * (n : ℝ) ^ (κe * ε)) * (Cm * (n : ℝ) ^ (κm * ε))) * L *
        (n : ℝ) ^ ε ≤
      (Cc + Cm + 2 * Cp * βhi * Ce * Cm * L) * (n : ℝ) ^ (k * ε) := by
  intro k
  have hn0 : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hpc : (n : ℝ) ^ (κc * ε) ≤ (n : ℝ) ^ (k * ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (mul_le_mul_of_nonneg_right
      (by dsimp only [k]; linarith) hε.le)
  have hpm : (n : ℝ) ^ (κm * ε) ≤ (n : ℝ) ^ (k * ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (mul_le_mul_of_nonneg_right
      (by dsimp only [k]; linarith) hε.le)
  have hpr : (n : ℝ) ^ ((κp + κe + κm + 1) * ε) ≤ (n : ℝ) ^ (k * ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (mul_le_mul_of_nonneg_right
      (by dsimp only [k]; linarith) hε.le)
  have hid : 2 * (Cp * (n : ℝ) ^ (κp * ε)) *
      (βhi * (Ce * (n : ℝ) ^ (κe * ε)) * (Cm * (n : ℝ) ^ (κm * ε))) * L *
      (n : ℝ) ^ ε = (2 * Cp * βhi * Ce * Cm * L) *
        (n : ℝ) ^ ((κp + κe + κm + 1) * ε) := by
    rw [show (κp + κe + κm + 1) * ε = ((κp * ε + κe * ε) + κm * ε) + ε by ring,
      Real.rpow_add hn0, Real.rpow_add hn0, Real.rpow_add hn0]
    ring
  rw [hid]
  have hh := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hpc hCc)
    (mul_le_mul_of_nonneg_left hpm hCm))
    (mul_le_mul_of_nonneg_left hpr (by positivity : 0 ≤ 2 * Cp * βhi * Ce * Cm * L))
  exact hh.trans_eq (by ring)

/-- See the proof of Proposition 5.15 in the paper, composed under the exact
preceding constrained conclusion. The local predicate `P a g b` is the
mode-specific uniform assertion of Subsection 5.5. Its conjunction for both
Booleans is the current induction property. Unique existence is included by
coercivity. -/
theorem unconstrained_step_internal (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ)
    (hκstar : 0 < κstar) (hγstar : 0 < γstar) (M₀ : ℕ+)
    (A G : ℝ) (hAlo : 3 / 2 - s.val ≤ A) (_hAhi : A ≤ 2 - s.val)
    (hGlo : 1 - s.val / 2 ≤ G) (_hGhi : G ≤ (3 - s.val) / 2) (_hGA : G ≤ A) :
    let P := fun (a g : ℝ) (b : Bool) =>
      ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε →
      ∀ Cstar : ℝ, 1 ≤ Cstar →
      ∀ βlo : ℝ, 0 < βlo → ∀ βhi : ℝ, βlo ≤ βhi →
      ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
        (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
      ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ)),
      2 ≤ (n : ℕ) → (n : ℕ) ≤ (m : ℕ) →
      (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
      let K := ⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ)
      1 ≤ K → 4 * K ≤ (m : ℕ) →
      ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
      PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M →
      ∀ β : ℝ, βlo ≤ β → β ≤ βhi →
      ∀ (i₀ : Fin (m : ℕ)) (χ : Lp ℝ 2 ν),
      ∃! u : Fin (m : ℕ) → Q.1,
        WeightedWeakSolution Q (fun x => β • M x)
          (if b then zeroSumComponents _ else ⊤)
          (fun i => if i = i₀ then χ else 0) u ∧
        ∀ j, ‖(u j).val‖ ≤ C * (n : ℝ) ^ (κ * ε) * weightRadius m j i₀ ^ (-a) * ‖χ‖ ∧
          Real.sqrt (Q.2 (u j) (u j)) ≤
            C * (n : ℝ) ^ (κ * ε) * weightRadius m j i₀ ^ (-g) * ‖χ‖
    (P A G true ∧ P A G false) →
      P (min (2 - s.val) (A + 1 - s.val))
        (min ((3 - s.val) / 2) (G + 1 - s.val)) true →
      P (min (2 - s.val) (A + 1 - s.val))
        (min ((3 - s.val) / 2) (G + 1 - s.val)) false := by
  intro P hcurrent hconstrained
  obtain ⟨κp, hκp, hp⟩ := hcurrent.2
  obtain ⟨κc, hκc, hc⟩ := hconstrained
  obtain ⟨κm, hκm, hm⟩ := UnconstrainedGlobalDecay.global_bis_mean hzeta s
    κstar γstar hκstar hγstar M₀
  obtain ⟨κe, hκe, he⟩ := global_error_differences s κstar γstar hκstar.le hγstar.le M₀
  refine ⟨κc + κm + κp + κe + 1, by positivity,
    fun ε hε Cstar hCstar βlo hβlo βhi hβhi => ?_⟩
  obtain ⟨Cp, hCp, hp⟩ := hp ε hε Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Cc, hCc, hc⟩ := hc ε hε Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Cm, hCm, hm⟩ := hm ε hε Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Ce, hCe, he⟩ := he ε hε Cstar hCstar
  have hA : 0 < A := by linarith only [hAlo, s.property.2]
  have hG : 0 < G := by linarith only [hGlo, s.property.2]
  obtain ⟨La, hLa, hsa⟩ := scaled_profile_sum s A hA ε hε
  obtain ⟨Lg, hLg, hsg⟩ := scaled_profile_sum s G hG ε hε
  let L := La + Lg
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hβhi0 : 0 < βhi := hβlo.trans_le hβhi
  let C := Cc + Cm + 2 * Cp * βhi * Ce * Cm * L
  have hCe0 : 0 ≤ Ce := zero_le_one.trans hCe
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Ω _ ν _ Q hQ hQc n m hm2 hn hnm hmn K hK hKm M hM β hβl hβu i₀ χ
  have hβ : 0 < β := hβlo.trans_le hβl
  let Dp := Cp * (n : ℝ) ^ (κp * ε)
  let Dc := Cc * (n : ℝ) ^ (κc * ε)
  let Dm := Cm * (n : ℝ) ^ (κm * ε)
  let Be := Ce * (n : ℝ) ^ (κe * ε)
  let B := βhi * Be * Dm
  have hDp : 0 ≤ Dp := by dsimp only [Dp]; positivity
  have hDm : 0 ≤ Dm := by dsimp only [Dm]; positivity
  have hBe : 0 ≤ Be := by dsimp only [Be]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  obtain ⟨u, ⟨hu, v, lam, f, hvc, _, _, _, _, _, hf, hfg, _, ⟨g, hg, hgeq⟩, _⟩, _⟩ :=
    hm ν Q hQ hQc n m hm2 hn hnm hmn hK hKm M hM β hβl hβu χ i₀
  obtain ⟨vc, ⟨hvc', hvcest⟩, _⟩ :=
    hc ν Q hQ hQc n m hm2 hn hnm hmn hK hKm M hM β hβl hβu i₀ χ
  let a := Cstar⁻¹ * (n : ℝ) ^ (-κstar * ε)
  have ha : 0 < a := SchurRestriction.periodized_mass_pos hCstar
  have hl : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
      ∀ z : Fin (m : ℕ) → ℝ, a * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j :=
    hM.2.1.mono (fun _ hx => ⟨hx.1, hx.2.2.1⟩)
  have huniqC := (AbstractEquation.existence_energy Q hQ β hβ M hM.1 a ha hl
    (zeroSumComponents _) (fun i => if i = i₀ then χ else 0)).1
  have hvc_eq : vc = v := huniqC.unique hvc' hvc
  subst vc
  have hpoint : ∀ (ζ : Lp ℝ 2 ν) (i : Fin (m : ℕ)),
      ∃ z : Fin (m : ℕ) → Q.1,
        WeightedWeakSolution Q (fun x => β • M x) ⊤ (fun k => if k = i then ζ else 0) z ∧
        ∀ j, ‖(z j).val‖ ≤ Dp * weightRadius m j i ^ (-A) * ‖ζ‖ ∧
          Real.sqrt (Q.2 (z j) (z j)) ≤ Dp * weightRadius m j i ^ (-G) * ‖ζ‖ := by
    intro ζ i
    obtain ⟨z, hz, _⟩ := hp ν Q hQ hQc n m hm2 hn hnm hmn hK hKm M hM β hβl hβu i ζ
    exact ⟨z, hz⟩
  obtain ⟨_, _, _, _, _, _, heae⟩ := he n m hm2 hn hnm hmn hK hKm ν M hM
  have hrow : ∀ᵐ x ∂ν, ∀ i, ∑ j, |(M x - (2 : ℝ) • rieszMatrix s m hm2) i j| ≤ Be :=
    heae.mono (fun _ hx => hx.2.2.2.1)
  have hgB : ∀ i, ‖g i‖ ≤ B * (m : ℝ) ^ (-(2 - s.val)) * ‖χ‖ := by
    intro i
    have hg₁ := row_source_norm_internal m β Be hβ.le hBe
      (fun x => M x - (2 : ℝ) • rieszMatrix s m hm2) hrow f.val g hg i
    have hg₂ := mul_le_mul_of_nonneg_left hf (mul_nonneg hβ.le hBe)
    have hg₃ : (β * Be) * (Dm * (m : ℝ) ^ (-(2 - s.val)) * ‖χ‖) ≤
        (βhi * Be) * (Dm * (m : ℝ) ^ (-(2 - s.val)) * ‖χ‖) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hβu hBe) (by positivity)
    exact hg₁.trans (hg₂.trans (hg₃.trans_eq (by dsimp only [B]; ring)))
  have hsa' (j) : (m : ℝ) ^ (-(2 - s.val)) * (∑ i, weightRadius m j i ^ (-A)) ≤
      L * (n : ℝ) ^ ε *
        ((m : ℝ) ^ (-(2 - s.val)) + (m : ℝ) ^ (-(A + 1 - s.val))) := by
    apply (hsa n m hm2 hn hmn j).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (by dsimp only [L]; linarith only [hLg]) (by positivity)
  have hsg' (j) : (m : ℝ) ^ (-(2 - s.val)) * (∑ i, weightRadius m j i ^ (-G)) ≤
      L * (n : ℝ) ^ ε *
        ((m : ℝ) ^ (-(2 - s.val)) + (m : ℝ) ^ (-(G + 1 - s.val))) := by
    apply (hsg n m hm2 hn hmn j).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (by dsimp only [L]; linarith only [hLa]) (by positivity)
  have hAinc : 0 ≤ A + 1 - s.val := by linarith only [hA, s.property.2]
  have hGinc : 0 ≤ G + 1 - s.val := by linarith only [hG, s.property.2]
  have hrem := remainder_improvement_internal s n m hm2 i₀ Q hQ M hM.1
    (SchurRestriction.periodized_bounded hM) β a hβ ha hl A G ε Dp B L ‖χ‖
    hDp hB hL (norm_nonneg χ) hAinc hGinc hpoint hsa' hsg' g hgB
    (fun j => u j - v j - f) hgeq
  have hfinal := assemble_internal s m hm2 i₀ Q hQ A G Dc Dm
    (2 * Dp * B * L * (n : ℝ) ^ ε) ‖χ‖ hDm (norm_nonneg χ) hAinc hGinc
    u v f hvcest hf hfg hrem
  have hcoef : Dc + Dm + 2 * Dp * B * L * (n : ℝ) ^ ε ≤
      C * (n : ℝ) ^ ((κc + κm + κp + κe + 1) * ε) :=
    loss_assembly_internal n ε κc κm κp κe Cc Cm Cp Ce βhi L hε hκc hκm hκp hκe
      hCc.le hCm.le hCp.le hCe0 hβhi0.le hL
  have huniq := (AbstractEquation.existence_energy Q hQ β hβ M hM.1 a ha hl
    ⊤ (fun i => if i = i₀ then χ else 0)).1
  refine ⟨u, ⟨hu, fun j => ⟨?_, ?_⟩⟩, fun z hz => huniq.unique hz.1 hu⟩
  · exact (hfinal j).1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (by
        exact Real.rpow_nonneg (zero_le_one.trans (one_le_weightRadius m j i₀)) _))
      (norm_nonneg χ))
  · exact (hfinal j).2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (by
        exact Real.rpow_nonneg (zero_le_one.trans (one_le_weightRadius m j i₀)) _))
      (norm_nonneg χ))

end Riesz2.OptimalLocalizationUnconstrained
