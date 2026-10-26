/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.LocalizedMatrixPart4
public import Riesz2.DecayLong.LocalizedMatrixPart5
public import Riesz2.DecayLong.LocalizedBoundaryPart5

/-!
# Preservation under localization

Preservation of matrix bounds and analytic estimates in the proof of
Proposition 5.15. The cyclic window, capped period, retained interval
matrix and remainder use the constructions of Subsection 5.5. All four
analytic estimates use the original scalar form and the same reference
cutoff. Constants precede every size and window.
-/

public section
noncomputable section
open MeasureTheory Finset Riesz2.IntervalBoundary
open scoped BigOperators Classical Fin.NatCast Matrix

namespace Riesz2.LocalizedMatrix

/-- See the proof of Proposition 5.15 in the paper: separation makes the original
integer reference cutoff admissible in the new period, including at R = 16. -/
theorem window_reference_cutoff_admissible (s : Riesz1.RieszExponent)
    (n m : ℕ+) (ε : ℝ) (hε : 0 < ε) (M₀ : ℕ+)
    (j i₀ : Fin (m : ℕ)) (hR : 16 ≤ Riesz1.cyclicIndexDistance m j i₀)
    (hsep : (n : ℝ) ^ ((8 * (M₀ : ℕ)) * ε) ≤
      (Riesz1.cyclicIndexDistance m j i₀ : ℝ)) :
    1 ≤ ⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ) ∧
      4 * (⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ)) ≤ (windowPeriod s m j i₀ : ℕ) := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hnpos : (0 : ℝ) < n := by positivity
  have ht : 1 ≤ (n : ℝ) ^ ((M₀ : ℕ) * ε) :=
    Real.one_le_rpow hn (by positivity)
  have hpow : ((n : ℝ) ^ ((M₀ : ℕ) * ε)) ^ (8 : ℕ) ≤
      (Riesz1.cyclicIndexDistance m j i₀ : ℝ) := by
    rw [← Real.rpow_mul_natCast hnpos.le]
    convert hsep using 1
    congr 1
    ring
  have hc := window_cutoff_admissible s m j i₀ hR ht hpow
  have hK := GlobalReferenceErrorInternal.cutoff_power_le n ε 1 (by norm_num) M₀
  rw [Real.rpow_one, mul_one] at hK
  have hceil : ⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ) ≤
      ⌈(n : ℝ) ^ ((M₀ : ℕ) * ε)⌉₊ := by
    exact_mod_cast hK.trans (Nat.le_ceil _)
  have hfloor : 1 ≤ ⌊(n : ℝ) ^ ε⌋₊ :=
    (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hn hε.le)
  exact ⟨one_le_pow₀ hfloor, by omega⟩

/-- See the proof of Proposition 5.15 in the paper: the boundary row estimate
holds for every parent interval witness. Its prefactor precedes the scalar
space, so it can be combined with the independently assembled matrix bounds. -/
theorem window_remainder_for_witness_internal (s : Riesz1.RieszExponent) :
    ∃ Cp : ℝ, 0 < Cp ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
      (n m : ℕ+) (hm : 2 ≤ (m : ℕ)) (K : ℕ) (C κ γ ε : ℝ), 1 ≤ C →
    ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M →
    ∀ A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → Ω → ℝ,
    (∀ᵐ x ∂ν, intervalMatrix m m le_rfl (fun t => A t x) = M x) →
    ∀ (j i₀ : Fin (m : ℕ)) (hR : 16 ≤ Riesz1.cyclicIndexDistance m j i₀),
    let n₀ := windowSize m j i₀
    let m₀ := windowPeriod s m j i₀
    let hm₀ : 2 ≤ (m₀ : ℕ) := by
      have := two_windowSize_lt_period s m j i₀ hR
      have := (windowSize m j i₀).pos
      change 2 ≤ (windowPeriod s m j i₀ : ℕ)
      omega
    let hn : (n₀ : ℕ) ≤ (m : ℕ) := by
      have := (window_size_bounds m j i₀ hR).2.2.2
      change (windowSize m j i₀ : ℕ) ≤ (m : ℕ)
      omega
    let hn₀ : (n₀ : ℕ) ≤ (m₀ : ℕ) := by
      have := two_windowSize_lt_period s m j i₀ hR
      change (windowSize m j i₀ : ℕ) ≤ (windowPeriod s m j i₀ : ℕ)
      omega
    let b := j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ))
    let P := fun x (i l : Fin (n₀ : ℕ)) => M x (i.castLE hn + b) (l.castLE hn + b)
    ∀ᵐ x ∂ν, ∀ l : Fin (n₀ : ℕ),
      Real.sqrt (∑ i : Fin (n₀ : ℕ),
        (remainder s m m₀ n₀ hm₀ hn hn₀ K (fun t => A (t.1 + b, t.2)) P x l i) ^ 2) ≤
      (4 * Real.sqrt (2 + 1 / (1 + s.val)) * (C * (n : ℝ) ^ (κ * ε)) + Cp) *
        ((min (l.val + 1) ((n₀ : ℕ) - l.val) : ℕ) : ℝ) ^ (-(1 + s.val) / 2) := by
  obtain ⟨Cp, hCp, hb⟩ := remainder_row_bound_internal s
  refine ⟨Cp, hCp, ?_⟩
  intro Ω _ ν n m hm K C κ γ ε hC M hM A hA j i₀ hR
  dsimp only
  let n₀ := windowSize m j i₀
  let m₀ := windowPeriod s m j i₀
  let b : Fin (m : ℕ) := j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ))
  have hn : 4 * (n₀ : ℕ) ≤ (m : ℕ) := (window_size_bounds m j i₀ hR).2.2.2
  have hn₀ : 2 * (n₀ : ℕ) < (m₀ : ℕ) := two_windowSize_lt_period s m j i₀ hR
  have hm₀ : 4 ≤ (m₀ : ℕ) := by
    have := (window_size_bounds m j i₀ hR).1
    change 5 ≤ (n₀ : ℕ) at this
    omega
  have hscale : m₀ = m ∨ (n₀ : ℝ) ^ (1 / 2 + 1 / s.val) ≤ (m₀ : ℝ) := by
    by_cases h : m₀ = m
    · exact Or.inl h
    · exact Or.inr (power_le_windowPeriod_of_lt s m j i₀
        (lt_of_le_of_ne (windowPeriod_le_parent s m j i₀)
          (fun he => h (Subtype.ext he))))
  filter_upwards [hA, periodizedMatrixBounds_truncated_error s n m hm K C κ γ ε
    (by linarith : 0 ≤ C) M hM] with x hx he
  have henv (p w : Fin (m : ℕ)) :
      |intervalMatrix m m le_rfl
        ((fun t => A (t.1 + b, t.2) x) - BoundaryEntries.referenceWeight s m hm K) p w| ≤
        (C * (n : ℝ) ^ (κ * ε)) *
          (1 + (Riesz1.cyclicIndexDistance m p w : ℝ)) ^ (-1 - s.val / 2) := by
    have hcoef : ((fun t => A (t.1 + b, t.2) x) - BoundaryEntries.referenceWeight s m hm K) =
        (fun t => ((fun u => A u x) - BoundaryEntries.referenceWeight s m hm K) (t.1 + b, t.2)) := rfl
    rw [hcoef, intervalMatrix_translate, intervalMatrix_sub, hx,
      intervalMatrix_referenceWeight, Matrix.sub_apply]
    simpa only [distance_add, show -(1 + s.val / 2) = -1 - s.val / 2 by ring] using he (p + b) (w + b)
  intro l
  have hh := hb m m₀ n₀ hm hm₀ (windowPeriod_le_parent s m j i₀) hn hn₀ hscale K
    (fun t => A (t.1 + b, t.2) x) (C * (n : ℝ) ^ (κ * ε)) (by positivity) henv l
  have hprincipal (i k : Fin (n₀ : ℕ)) :
      M x (i.castLE (by omega : (n₀ : ℕ) ≤ (m : ℕ)) + b)
        (k.castLE (by omega : (n₀ : ℕ) ≤ (m : ℕ)) + b) =
        intervalMatrix m n₀ (by omega) (fun t => A (t.1 + b, t.2) x) i k := by
    rw [intervalMatrix_restrict,
      intervalMatrix_translate m (fun t => A t x), hx]
  simp only [remainder, Matrix.sub_apply]
  convert hh using 1
  congr 1
  apply sum_congr rfl
  intro i _
  change (M x (l.castLE (by omega : (n₀ : ℕ) ≤ (m : ℕ)) + b)
      (i.castLE (by omega : (n₀ : ℕ) ≤ (m : ℕ)) + b) -
      internalMatrix m n₀ (by omega) (fun t => A (t.1 + b, t.2) x) l i -
      BoundaryEntries.referenceCrossing s m₀ (by omega) K n₀ (by omega) l i) ^ 2 = _
  rw [hprincipal l i, intervalMatrix_symm m n₀ (by omega) _ l i,
    internalMatrix_symm m n₀ (by omega) _ l i,
    BoundaryEntries.referenceCrossing_eq_boundaryMatrix,
    boundaryMatrix_symm m₀ n₀ (by omega) _ l i]

/-- See Subsection 5.4 of the paper: a finite family of uniform losses is bounded
by one common prefactor and exponent. -/
theorem loss_mono_internal {n ε c C k κ : ℝ} (hn : 1 ≤ n) (hε : 0 ≤ ε)
    (hc : 0 ≤ c) (hcC : c ≤ C) (hk : k ≤ κ) :
    c * n ^ (k * ε) ≤ C * n ^ (κ * ε) :=
  mul_le_mul hcC (Real.rpow_le_rpow_of_exponent_le hn
    (mul_le_mul_of_nonneg_right hk hε)) (by positivity) (hc.trans hcC)

/-- See the proof of Proposition 5.15 in the paper. The localized matrix
satisfies every matrix hypothesis, its remainder has the displayed
boundary row norm, and the elliptic, derivative, constrained global and
unrestricted global estimates hold with one parent-scale loss. The source
index below is arbitrary on the new component cycle. The probability space,
scalar form, its domain and its diffusion pairing are unchanged.

The structural exponents and D precede all prefactors and ε. The derivative
weight γ is free. Only its analytic loss may depend on γ. Constants are uniform
over the closed positive temperature interval and over all windows, including
both branches of the period cap. -/
theorem localization (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (κstar γstar : ℝ) (M₀ : ℕ+) (hκstar : 0 < κstar) (hγstar : 0 < γstar) :
    ∃ κloc γloc D : ℝ, 0 < κloc ∧ 0 < γloc ∧ 0 < D ∧
    ∀ γ : ℝ, 1 / 2 ≤ γ → ∃ κ : ℝ, 0 < κ ∧
    ∀ Cstar : ℝ, 1 ≤ Cstar → ∃ Cloc : ℝ, 1 ≤ Cloc ∧
    ∀ ε : ℝ, 0 < ε → ∀ βlo : ℝ, 0 < βlo → ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
      (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
    ∀ (n m : ℕ+) (_hn : 2 ≤ (n : ℕ)) (hm : 2 ≤ (m : ℕ)),
    (n : ℕ) ≤ (m : ℕ) → (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
    let K := ⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ)
    ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M →
    ∃ A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → Ω → ℝ,
      (∀ t, Measurable (A t)) ∧
      (∀ᵐ x ∂ν, (∀ t, 0 ≤ A t x) ∧ intervalMatrix m m le_rfl (fun t => A t x) = M x) ∧
      ∀ (j i₀ : Fin (m : ℕ)) (hR : 16 ≤ Riesz1.cyclicIndexDistance m j i₀),
      (n : ℝ) ^ (D * ε) ≤ (Riesz1.cyclicIndexDistance m j i₀ : ℝ) →
      let n₀ := windowSize m j i₀
      let m₀ := windowPeriod s m j i₀
      let hm₀ : 2 ≤ (m₀ : ℕ) := by
        have := two_windowSize_lt_period s m j i₀ hR
        have := (windowSize m j i₀).pos
        change 2 ≤ (windowPeriod s m j i₀ : ℕ)
        omega
      let hn : (n₀ : ℕ) ≤ (m : ℕ) := by
        have := (window_size_bounds m j i₀ hR).2.2.2
        change (windowSize m j i₀ : ℕ) ≤ (m : ℕ)
        omega
      let hn₀ : (n₀ : ℕ) ≤ (m₀ : ℕ) := by
        have := two_windowSize_lt_period s m j i₀ hR
        change (windowSize m j i₀ : ℕ) ≤ (windowPeriod s m j i₀ : ℕ)
        omega
      let b := j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ))
      let ε₀ := ε * Real.log (n : ℝ) / Real.log (n₀ : ℝ)
      let Ml := matrix s m m₀ n₀ hm₀ hn hn₀ K (fun t => A (t.1 + b, t.2))
      let P := fun x (i l : Fin (n₀ : ℕ)) => M x (i.castLE hn + b) (l.castLE hn + b)
      let loss := C * (n : ℝ) ^ (κ * ε)
      PeriodizedMatrixBounds (ν := ν) s n₀ m₀ hm₀ K Cloc κloc γloc ε₀ Ml ∧
      Cloc * (n₀ : ℝ) ^ (κloc * ε₀) ≤ loss ∧
      (1 ≤ K ∧ 4 * K ≤ (m₀ : ℕ)) ∧
      (∀ᵐ x ∂ν, ∀ l : Fin (n₀ : ℕ),
        Real.sqrt (∑ i : Fin (n₀ : ℕ),
          (remainder s m m₀ n₀ hm₀ hn hn₀ K (fun t => A (t.1 + b, t.2)) P x l i) ^ 2) ≤
          loss * ((min (l.val + 1) ((n₀ : ℕ) - l.val) : ℕ) : ℝ) ^ (-(1 + s.val) / 2)) ∧
      ∀ β : ℝ, βlo ≤ β → β ≤ βhi →
      (∀ (χ : Lp ℝ 2 ν) (a : Fin (m₀ : ℕ)) (u : Fin (m₀ : ℕ) → Q.1),
        WeightedWeakSolution Q (fun x => β • Ml x) (zeroSumComponents _)
          (fun i => if i = a then χ else 0) u →
        let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
          constructor <;> linarith [s.property.1, s.property.2]⟩
        let H := Matrix.of (fun a b : Fin (m₀ : ℕ) => sampledRieszKernel sh m₀ hm₀ (b - a))
        let F := fun x => (∑ i, |(H *ᵥ (fun k => (u k).val x)) i| ^
          (1 - s.val / 2)⁻¹) ^ (1 - s.val / 2)
        let w₁ := fun i => 1 + (Riesz1.cyclicIndexDistance m₀ i a : ℝ) ^ (1 / 2 : ℝ)
        let w₂ := fun i => 1 + (Riesz1.cyclicIndexDistance m₀ i a : ℝ) ^ (3 / 2 - s.val)
        Integrable (fun x => ∑ i, (w₁ i * (u i).val x) ^ 2) ν ∧
        Integrable (fun x => ∑ i, (w₂ i * (u i).val x) ^ 2) ν ∧
        Integrable (fun x => F x ^ 2) ν ∧
        Real.sqrt (∫ x, F x ^ 2 ∂ν) ≤ loss *
          (‖χ‖ + Real.sqrt (∫ x, ∑ i, (w₁ i * (u i).val x) ^ 2 ∂ν)) ^ s.val *
          (Real.sqrt (∫ x, ∑ i, (w₂ i * (u i).val x) ^ 2 ∂ν)) ^ (1 - s.val)) ∧
      (∀ (χ : Q.1) (a : Fin (m₀ : ℕ)) (u : Fin (m₀ : ℕ) → Q.1),
        WeightedWeakSolution Q (fun x => β • Ml x) (zeroSumComponents _)
          (fun i => if i = a then χ.val else 0) u →
        let t := γ / 2 + 1 / 4
        let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
          constructor <;> linarith [s.property.1, s.property.2]⟩
        let p := (1 - s.val / 2)⁻¹
        let V := fun x => (∑ i, |(rieszMatrix sh m₀ hm₀ *ᵥ
          (fun k => (u k).val x)) i| ^ p) ^ (1 / p)
        let Xρ := fun ρ => Real.sqrt (∑ i, (weightRadius m₀ i a ^ ρ * ‖(u i).val‖) ^ 2)
        ∃ lam : Lp ℝ 2 ν,
          (∀ᵐ x ∂ν, lam x = gapMultiplierField m₀ Q (fun x => β • Ml x)
            (fun i => if i = a then χ.val else 0) u x) ∧
          WeightedWeakSolution Q (fun x => β • Ml x) ⊤
            (fun i => (if i = a then χ.val else 0) + lam) u ∧
          Integrable (fun x => V x ^ 2) ν ∧
          ∀ η : ℝ, 0 < η → η < 1 / 4 →
            (∑ i, weightRadius m₀ i a ^ (2 * t) * Q.2 (u i) (u i)) ≤
              loss * (‖χ.val‖ ^ 2 + Xρ γ *
                (η ^ (3 - s.val) * Xρ (3 / 2 - s.val) +
                  η⁻¹ * Real.sqrt (Real.log (2 * (m₀ : ℝ))) *
                    Real.sqrt (∫ x, V x ^ 2 ∂ν) + (m₀ : ℝ) * ‖lam‖))) ∧
      (∀ (χ : Lp ℝ 2 ν) (a : Fin (m₀ : ℕ)),
        (∃! u : Fin (m₀ : ℕ) → Q.1,
          WeightedWeakSolution Q (fun x => β • Ml x) (zeroSumComponents _)
            (fun i => if i = a then χ else 0) u) ∧
        ∀ u : Fin (m₀ : ℕ) → Q.1,
        WeightedWeakSolution Q (fun x => β • Ml x) (zeroSumComponents _)
          (fun i => if i = a then χ else 0) u →
        ∃ lam : Lp ℝ 2 ν,
          (∀ᵐ x ∂ν, lam x = gapMultiplierField m₀ Q (fun x => β • Ml x)
            (fun i => if i = a then χ else 0) u x) ∧
          WeightedWeakSolution Q (fun x => β • Ml x) ⊤
            (fun i => (if i = a then χ else 0) + lam) u ∧
          Real.sqrt (∑ i, (weightRadius m₀ i a ^ (3 / 2 - s.val) * ‖(u i).val‖) ^ 2) +
            Real.sqrt (∑ i, weightRadius m₀ i a ^ (2 * (1 - s.val / 2)) * Q.2 (u i) (u i)) ≤
              loss * ‖χ‖ ∧
          ‖lam‖ ≤ loss * (m₀ : ℝ)⁻¹ * ‖χ‖ ∧
          loss * (m₀ : ℝ)⁻¹ * ‖χ‖ ≤ loss * (n₀ : ℝ)⁻¹ * ‖χ‖) ∧
      (∀ (χ : Lp ℝ 2 ν) (a : Fin (m₀ : ℕ)),
        (∃! u : Fin (m₀ : ℕ) → Q.1,
          WeightedWeakSolution Q (fun x => β • Ml x) ⊤
            (fun i => if i = a then χ else 0) u) ∧
        ∀ u : Fin (m₀ : ℕ) → Q.1,
        WeightedWeakSolution Q (fun x => β • Ml x) ⊤
          (fun i => if i = a then χ else 0) u →
        Real.sqrt (∑ i, (weightRadius m₀ i a ^ (3 / 2 - s.val) * ‖(u i).val‖) ^ 2) +
          Real.sqrt (∑ i, weightRadius m₀ i a ^ (2 * (1 - s.val / 2)) * Q.2 (u i) (u i)) ≤
            loss * ‖χ‖) := by
  obtain ⟨kl, gl, Dm, hkl, hgl, hDm, hmat⟩ :=
    localized_periodizedMatrixBounds s κstar γstar M₀ hκstar hγstar
  let D : ℝ := Dm + 8 * (M₀ : ℕ)
  refine ⟨kl, gl, D, hkl, hgl, by dsimp [D]; positivity, ?_⟩
  intro γ hγ
  obtain ⟨ke, hke, he⟩ := Analytic.elliptic_L2 hz s kl gl hkl hgl M₀
  obtain ⟨kd, hkd, hd⟩ := Analytic.derivative_transfer_internal hz s γ hγ kl gl hkl
  obtain ⟨kg, hkg, hg⟩ := Analytic.global_decay_bounds hz s kl gl hkl hgl M₀
  obtain ⟨ku, hku, hu⟩ := Analytic.global_bis hz s kl gl hkl hgl M₀
  let k : ℝ := κstar + kl + ke + kd + kg + ku + 1
  have hk : 0 < k := by dsimp [k]; positivity
  have hks : κstar ≤ k := by dsimp [k]; linarith
  have hklk : kl ≤ k := by dsimp [k]; linarith
  have hkek : ke ≤ k := by dsimp [k]; linarith
  have hkdk : kd ≤ k := by dsimp [k]; linarith
  have hkgk : kg ≤ k := by dsimp [k]; linarith
  have hkuk : ku ≤ k := by dsimp [k]; linarith
  refine ⟨k, hk, fun Cs hCs => ?_⟩
  obtain ⟨Cl, hCl, hmat⟩ := hmat Cs hCs
  refine ⟨Cl, hCl, fun ε hε βlo hβlo βhi hβhi => ?_⟩
  let emin : ℝ := ε / (3 / 2 + 1 / s.val)
  have hemin : 0 < emin := by dsimp [emin]; exact div_pos hε (by positivity [s.property.1])
  obtain ⟨Ce, hCe, he⟩ := he emin hemin Cl hCl βlo hβlo
  obtain ⟨Cd, hCd, hd⟩ := hd Cl hCl βlo hβlo βhi hβhi
  obtain ⟨Cg, hCg, hg⟩ := hg emin hemin Cl hCl βlo hβlo βhi hβhi
  obtain ⟨Cu, hCu, hu⟩ := hu emin hemin Cl hCl βlo hβlo βhi hβhi
  obtain ⟨Cp, hCp, hrow⟩ := window_remainder_for_witness_internal s
  let Cr : ℝ := 4 * Real.sqrt (2 + 1 / (1 + s.val)) * Cs + Cp
  have hCr : 0 ≤ Cr := by dsimp [Cr]; positivity
  let C : ℝ := 1 + Cl + Ce + Cd + Cg + Cu + Cr
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hClC : Cl ≤ C := by dsimp [C]; linarith
  have hCeC : Ce ≤ C := by dsimp [C]; linarith
  have hCdC : Cd ≤ C := by dsimp [C]; linarith
  have hCgC : Cg ≤ C := by dsimp [C]; linarith
  have hCuC : Cu ≤ C := by dsimp [C]; linarith
  have hCrC : Cr ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro Ω _ ν _ Q hQ hQc n m hn hm hnm hmn K M hM
  obtain ⟨A, hA, hrep, hlocal⟩ := hmat ν ε hε n m hn hm M hM
  refine ⟨A, hA, hrep, ?_⟩
  intro j i₀ hR hsep
  dsimp only
  let n₀ := windowSize m j i₀
  let m₀ := windowPeriod s m j i₀
  have hw := window_size_bounds m j i₀ hR
  have hn₀ : 2 ≤ (n₀ : ℕ) := by change 2 ≤ (windowSize m j i₀ : ℕ); omega
  have hn₀m₀ : (n₀ : ℕ) ≤ (m₀ : ℕ) := by
    have := two_windowSize_lt_period s m j i₀ hR
    change (windowSize m j i₀ : ℕ) ≤ (windowPeriod s m j i₀ : ℕ)
    omega
  have hm₀ : 2 ≤ (m₀ : ℕ) := by omega
  let b := j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ))
  let ε₀ := ε * Real.log (n : ℝ) / Real.log (n₀ : ℝ)
  let Ml := matrix s m m₀ n₀ hm₀ (by change (windowSize m j i₀ : ℕ) ≤ (m : ℕ); omega)
    hn₀m₀ K (fun t => A (t.1 + b, t.2))
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ (n : ℕ))
  have hsep_m : (n : ℝ) ^ (Dm * ε) ≤ (Riesz1.cyclicIndexDistance m j i₀ : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hn1
      (mul_le_mul_of_nonneg_right (by dsimp [D]; linarith only [show (0 : ℝ) ≤ 8 * (M₀ : ℕ) by positivity]) hε.le)).trans hsep
  have hsep_K : (n : ℝ) ^ ((8 * (M₀ : ℕ)) * ε) ≤
      (Riesz1.cyclicIndexDistance m j i₀ : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hn1
      (mul_le_mul_of_nonneg_right (by dsimp [D]; linarith) hε.le)).trans hsep
  have hMl : PeriodizedMatrixBounds (ν := ν) s n₀ m₀ hm₀ K Cl kl gl ε₀ Ml :=
    hlocal j i₀ hR hsep_m
  obtain ⟨hε₀, hεlower, hloss, hcut⟩ := Analytic.window_loss_parameters s n m hn hmn j i₀ hR ε hε
  have hcut' : ⌊(n₀ : ℝ) ^ ε₀⌋₊ ^ (M₀ : ℕ) = K := hcut M₀
  have hK := window_reference_cutoff_admissible s n m ε hε M₀ j i₀ hR hsep_K
  change 1 ≤ K ∧ 4 * K ≤ (m₀ : ℕ) at hK
  have hlocal_size := Analytic.windowPeriod_analytic_upper s m j i₀
  let loss := C * (n : ℝ) ^ (k * ε)
  have hbound (c q : ℝ) (hc : 0 ≤ c) (hcC : c ≤ C) (hq : q ≤ k) :
      c * (n₀ : ℝ) ^ (q * ε₀) ≤ loss := by
    rw [hloss q]
    exact loss_mono_internal hn1 hε.le hc hcC hq
  have hrowloss : 4 * Real.sqrt (2 + 1 / (1 + s.val)) * (Cs * (n : ℝ) ^ (κstar * ε)) + Cp ≤ loss := by
    have hone : 1 ≤ (n : ℝ) ^ (κstar * ε) := Real.one_le_rpow hn1 (by positivity)
    calc
      _ ≤ Cr * (n : ℝ) ^ (κstar * ε) := by
        dsimp only [Cr]
        have hh := mul_le_mul_of_nonneg_left hone hCp.le
        nlinarith only [hh]
      _ ≤ loss := loss_mono_internal hn1 hε.le hCr hCrC hks
  refine ⟨hMl, hbound Cl kl (by linarith) hClC hklk, hK, ?_, ?_⟩
  · have hr := hrow ν n m hm K Cs κstar γstar ε hCs M hM A
      (hrep.mono fun _ hx => hx.2) j i₀ hR
    filter_upwards [hr] with x hx
    intro l
    exact (hx l).trans (mul_le_mul_of_nonneg_right hrowloss (by positivity))
  · intro β hβloβ hββhi
    have hβ : 0 < β := hβlo.trans_le hβloβ
    have hMl' : PeriodizedMatrixBounds (ν := ν) s n₀ m₀ hm₀
        (⌊(n₀ : ℝ) ^ ε₀⌋₊ ^ (M₀ : ℕ)) Cl kl gl ε₀ Ml := by rw [hcut']; exact hMl
    have heBound := hbound Ce ke hCe.le hCeC hkek
    have hdBound : Cd * (n : ℝ) ^ (kd * ε) ≤ loss :=
      loss_mono_internal hn1 hε.le hCd.le hCdC hkdk
    have hgBound := hbound Cg kg hCg.le hCgC hkgk
    have huBound := hbound Cu ku hCu.le hCuC hkuk
    have hsolve (S : Submodule ℝ (Fin (m₀ : ℕ) → ℝ)) (χ : Lp ℝ 2 ν) (a : Fin (m₀ : ℕ)) :
        ∃! u : Fin (m₀ : ℕ) → Q.1,
          WeightedWeakSolution Q (fun x => β • Ml x) S (fun i => if i = a then χ else 0) u := by
      exact (AbstractEquation.existence_energy Q hQ β hβ Ml hMl.1
        _ (SchurRestriction.periodized_mass_pos hCl)
        (hMl.2.1.mono fun _ hx => ⟨hx.1, hx.2.2.1⟩) S _).1
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro χ a u hsol
      have hh := he ε₀ hεlower β hβloβ ν n₀ m₀ hm₀ hn₀m₀
        (by have hp := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n₀) (1 / 2 + 1 / s.val)
            linarith [hlocal_size])
        (by rw [hcut']; omega) Ml hMl' Q hQ hQc a χ u hsol
      dsimp only at hh ⊢
      refine ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.trans ?_⟩
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right heBound (by positivity)) (by positivity)
    · intro χ a u hsol
      obtain ⟨lam, hlam, hfull, hV, hb⟩ :=
        hd ε hε ν Q hQ n n₀ m₀ hm₀ K hn hn₀ Ml hMl β hβloβ hββhi χ a u hsol
      refine ⟨lam, hlam, hfull, hV, fun η hη hηquarter => (hb η hη hηquarter).trans ?_⟩
      apply mul_le_mul_of_nonneg_right hdBound
      positivity
    · intro χ a
      refine ⟨hsolve (zeroSumComponents _) χ a, fun u hsol => ?_⟩
      obtain ⟨lam, hlam, hfull, hv, hl, _⟩ :=
        hg ε₀ hεlower ν Q hQ hQc n₀ m₀ hm₀ hn₀ hn₀m₀ hlocal_size
          (by rw [hcut']; exact hK.1) (by rw [hcut']; exact hK.2)
          Ml hMl' β hβloβ hββhi χ a u hsol
      refine ⟨lam, hlam, hfull,
        hv.trans (mul_le_mul_of_nonneg_right hgBound (norm_nonneg χ)),
        hl.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hgBound (by positivity))
          (norm_nonneg χ)), ?_⟩
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg χ)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (inv_le_inv₀ (by positivity : (0 : ℝ) < m₀) (by positivity : (0 : ℝ) < n₀)).mpr
        (by exact_mod_cast hn₀m₀)
    · intro χ a
      obtain ⟨u, ⟨hsol, hb⟩, _⟩ :=
        hu ε₀ hεlower ν Q hQ hQc n₀ m₀ hm₀ hn₀ hn₀m₀ hlocal_size
          (by rw [hcut']; exact hK.1) (by rw [hcut']; exact hK.2)
          Ml hMl' β hβloβ hββhi χ a
      have huniq := hsolve ⊤ χ a
      refine ⟨huniq, fun v hv => ?_⟩
      have hvu : v = u := huniq.unique hv hsol
      subst v
      exact hb.trans (mul_le_mul_of_nonneg_right huBound (norm_nonneg χ))

end Riesz2.LocalizedMatrix
