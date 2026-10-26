/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.EllipticPrimitivePart2
public import Riesz2.DecayLong.DiscreteInterpolationPart2
public import Riesz2.Frozen.IsConservativeScalarForm

/-!
# Periodized elliptic regularity

See Lemma 5.9 of the paper. The finite Fourier interpolation and primitive
estimates are combined in the original scalar form domain. All sequence
norms use counting measure. The constants are uniform for temperatures
bounded below, and the loss exponent is selected before the temperature
and the small loss parameter.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Matrix

namespace Riesz2.EllipticRegularity

/-- Logarithm absorption for the exact period bound of Subsection 5.1, used
in Lemma 5.9. The prefactor may depend on the small loss. -/
theorem log_absorption (s : Riesz1.RieszExponent) {ε A : ℝ}
    (hε : 0 < ε) (hA : 0 < A) :
    ∃ D : ℝ, 0 < D ∧ ∀ (n m : ℕ+),
      (m : ℝ) ≤ 3 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
      Real.log (2 * (m : ℝ)) ^ A ≤ D * (n : ℝ) ^ ε := by
  let a : ℝ := 1 / 2 + 1 / s.val
  let η := ε / A
  have ha : 0 < a := by
    dsimp only [a]
    have hs := s.property.1
    positivity
  have hη : 0 < η := div_pos hε hA
  let B := Real.log 6 + a / η
  have hB : 0 < B := add_pos (Real.log_pos (by norm_num)) (div_pos ha hη)
  refine ⟨B ^ A, Real.rpow_pos_of_pos hB _, fun n m hmn => ?_⟩
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast n.pos
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast n.pos
  have hm1 : 1 ≤ (m : ℝ) := by exact_mod_cast m.pos
  have hnη : 1 ≤ (n : ℝ) ^ η := Real.one_le_rpow hn1 hη.le
  have hl : Real.log (2 * (m : ℝ)) ≤ Real.log 6 + a * Real.log n := by
    calc
      _ ≤ Real.log (6 * (n : ℝ) ^ a) :=
        Real.log_le_log (by positivity) (by dsimp only [a] at *; linarith)
      _ = _ := by
        rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hn0 _).ne',
          Real.log_rpow hn0]
  have hb : Real.log (2 * (m : ℝ)) ≤ B * (n : ℝ) ^ η := by
    have hlogn := mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hn0.le hη) ha.le
    have hlog6 := mul_le_mul_of_nonneg_left hnη
      (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 6))
    have hlogn' : a * Real.log n ≤ (a / η) * (n : ℝ) ^ η := by
      convert hlogn using 1; ring
    dsimp only [B]
    nlinarith
  calc
    _ ≤ (B * (n : ℝ) ^ η) ^ A :=
      Real.rpow_le_rpow (Real.log_nonneg (by linarith)) hb hA.le
    _ = B ^ A * (n : ℝ) ^ ε := by
      rw [Real.mul_rpow hB.le (Real.rpow_nonneg hn0.le _),
        ← Real.rpow_mul hn0.le]
      congr 2
      exact div_mul_cancel₀ ε hA.ne'

/-- The absorbed angular primitive estimate equation (5.32) in the proof of
Lemma 5.9 of the paper. The paper's period bound absorbs the logarithm
into `C n^(κ ε)`, with κ chosen before ε. As in the paper's constants convention,
C may depend on ε and is uniform for β bounded below. The spatial weight is
exactly `(1+d)^(1/2)`, and both squared energies are integrable. -/
theorem elliptic_primitive_angular (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (κstar γstar : ℝ) (hκstar : 0 < κstar) (M₀ : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (ε : ℝ), 0 < ε →
    ∀ (Cstar : ℝ), 1 ≤ Cstar → ∀ βlo : ℝ, 0 < βlo → ∃ C : ℝ, 0 < C ∧
    ∀ (β : ℝ), βlo ≤ β →
    ∀ {α : Type*} [MeasurableSpace α] (ν : Measure α)
      (n m : ℕ+) (hm : 2 ≤ (m : ℕ))
      (_hmn : (m : ℝ) ≤ 3 * (n : ℝ) ^ (1 / 2 + 1 / s.val))
      (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ),
    PeriodizedMatrixBounds (ν := ν) s n m hm (⌊(n : ℝ) ^ ε⌋₊ ^ M₀)
      Cstar κstar γstar ε M →
    ∀ (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q →
    ∀ (χ : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents (Fin (m : ℕ)))
      (fun i => if i = i₀ then χ else 0) u →
    let J := fun x => DiscreteInterpolation.angularPrimitive m (3 / 2 - s.val)
      (fun j => ((u j).val x : ℂ))
    let w := fun j => Riesz2.weightRadius m j i₀ ^ (1 / 2 : ℝ)
    Integrable (fun x => ∑ i, ‖J x i‖ ^ 2) ν ∧
    Integrable (fun x => ∑ j, (w j * (u j).val x) ^ 2) ν ∧
      Real.sqrt (∫ x, ∑ i, ‖J x i‖ ^ 2 ∂ν) ≤
        C * (n : ℝ) ^ (κ * ε) *
          (‖χ‖ + Real.sqrt (∫ x, ∑ j, (w j * (u j).val x) ^ 2 ∂ν)) := by
  obtain ⟨κ, hκ, hp⟩ := EllipticPrimitive.elliptic_primitive_angular_radius
    hz s κstar γstar hκstar M₀
  refine ⟨κ + 1, by linarith, fun ε hε Cstar hCstar βlo hβlo => ?_⟩
  obtain ⟨C, hC, hp⟩ := hp ε hε Cstar hCstar βlo hβlo
  obtain ⟨D, hD, hd⟩ := log_absorption s hε (A := 1) zero_lt_one
  refine ⟨C * D, mul_pos hC hD, fun β hβ {α} _ ν n m hm hmn M hM Q hQ χ i₀ u hu => ?_⟩
  obtain ⟨hJ, hw, hb⟩ := hp β hβ ν n m hm M hM Q hQ χ i₀ u hu
  refine ⟨hJ, hw, hb.trans ?_⟩
  have hn : 0 < (n : ℝ) := by positivity
  have hl : Real.log (2 * (m : ℝ)) ≤ D * (n : ℝ) ^ ε := by
    simpa only [Real.rpow_one] using hd n m hmn
  calc
    _ ≤ C * (n : ℝ) ^ (κ * ε) * (D * (n : ℝ) ^ ε) *
        (‖χ‖ + Real.sqrt (∫ x, ∑ j,
          (weightRadius m j i₀ ^ (1 / 2 : ℝ) * (u j).val x) ^ 2 ∂ν)) := by
      gcongr
    _ = _ := by
      rw [show (κ + 1) * ε = κ * ε + ε by ring, Real.rpow_add hn]
      ring

/-- The angular interpolation and primitive `ℓ¹` estimate, integrated
over an arbitrary scalar measure. This is the Hölder step in
Lemma 5.9 of the paper. Zero endpoint norms are included. -/
theorem integrated_interpolation_angular (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent) :
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    ∃ C : ℝ, 0 < C ∧ ∀ {α : Type*} [MeasurableSpace α] (ν : Measure α)
      (m : ℕ+) (hm : 2 ≤ (m : ℕ)) (u : Fin (m : ℕ) → Lp ℝ 2 ν),
      (∀ᵐ x ∂ν, ∑ i, u i x = 0) → ∀ i₀ : Fin (m : ℕ),
      let H := Matrix.of (fun a b : Fin (m : ℕ) => sampledRieszKernel sh m hm (b - a))
      let F := fun x => (∑ i, |(H *ᵥ (fun j => u j x)) i| ^
        (1 - s.val / 2)⁻¹) ^ (1 - s.val / 2)
      let J := fun x => DiscreteInterpolation.angularPrimitive m (3 / 2 - s.val)
        (fun j => (u j x : ℂ))
      let w := fun j => 1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (3 / 2 - s.val)
      Integrable (fun x => F x ^ 2) ν ∧
        Real.sqrt (∫ x, F x ^ 2 ∂ν) ≤
          C * Real.log (2 * (m : ℝ)) ^ ((3 - s.val) / 2) *
            (Real.sqrt (∫ x, ∑ j, (w j * u j x) ^ 2 ∂ν)) ^ (1 - s.val) *
            (Real.sqrt (∫ x, ∑ i, ‖J x i‖ ^ 2 ∂ν)) ^ s.val := by
  dsimp only
  obtain ⟨Cg, hCg, hgn⟩ := DiscreteInterpolation.elliptic_GN_angular hz s
  obtain ⟨Cl, hCl, hlone⟩ := EllipticPrimitive.elliptic_lone s
  refine ⟨Cg * Cl ^ (1 - s.val), by positivity, fun {α} _ ν m hm u hu i₀ => ?_⟩
  let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
    constructor <;> linarith [s.property.1, s.property.2]⟩
  let H := Matrix.of (fun a b : Fin (m : ℕ) => sampledRieszKernel sh m hm (b - a))
  let F := fun x => (∑ i, |(H *ᵥ (fun j => u j x)) i| ^
    (1 - s.val / 2)⁻¹) ^ (1 - s.val / 2)
  let J := fun x => DiscreteInterpolation.angularPrimitive m (3 / 2 - s.val)
    (fun j => (u j x : ℂ))
  let w := fun j => 1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (3 / 2 - s.val)
  let f := fun x => ∑ j, (w j * u j x) ^ 2
  let g := fun x => ∑ i, ‖J x i‖ ^ 2
  let L := Real.log (2 * (m : ℝ))
  have hL : 0 < L := Real.log_pos (by
    have : (1 : ℝ) ≤ m := by exact_mod_cast m.pos
    linarith)
  let D := Cg * L * (Cl * Real.sqrt L) ^ (1 - s.val)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hf0 (x) : 0 ≤ f x := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hg0 (x) : 0 ≤ g x := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hf := (CyclicFourierL2.weighted_integral_sq w u).1
  have hg := DiscreteInterpolation.angularPrimitive_energy_integrable m (3 / 2 - s.val) u
  have hFm : AEStronglyMeasurable F ν := by
    apply AEMeasurable.aestronglyMeasurable
    apply AEMeasurable.pow_const
    apply Finset.aemeasurable_fun_sum
    intro i _
    have hm : AEMeasurable (fun x => (H *ᵥ (fun j => u j x)) i) ν := by
      change AEMeasurable (fun x => ∑ j, H i j * u j x) ν
      exact Finset.aemeasurable_fun_sum Finset.univ (fun j _ =>
        (aemeasurable_const : AEMeasurable (fun _ : α => H i j) ν).mul
          (Lp.aestronglyMeasurable (u j)).aemeasurable)
    simpa only [Real.norm_eq_abs] using hm.norm.pow_const (1 - s.val / 2)⁻¹
  have hsq : ∀ᵐ x ∂ν, F x ^ 2 ≤ D ^ 2 * (f x ^ (1 - s.val) * g x ^ s.val) := by
    filter_upwards [hu] with x hx
    have h1 := hgn m hm (fun j => u j x) hx
    let Hs := Matrix.of (fun a b : Fin (m : ℕ) => sampledRieszKernel s m hm (b - a))
    have h1' : F x ≤ Cg * L * (∑ i, |(Hs *ᵥ (fun j => u j x)) i|) ^
        (1 - s.val) * g x ^ (s.val / 2) := by
      simpa only [F, H, sh, Hs, L, g, J, apply_ite, ite_mul, Complex.ofReal_zero, zero_mul] using h1
    have h2 := hlone m hm (fun j => u j x) hx i₀
    have h3 := Real.rpow_le_rpow (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) h2
      (by linarith [s.property.2] : 0 ≤ 1 - s.val)
    have hb : F x ≤ D * f x ^ ((1 - s.val) / 2) * g x ^ (s.val / 2) := by
      calc
        _ ≤ Cg * L * ((Cl * Real.sqrt L * Real.sqrt (f x)) ^ (1 - s.val)) *
            g x ^ (s.val / 2) :=
          h1'.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h3 (mul_nonneg hCg.le hL.le))
              (Real.rpow_nonneg (hg0 x) _))
        _ = _ := by
          rw [Real.mul_rpow (by positivity : 0 ≤ Cl * Real.sqrt L) (Real.sqrt_nonneg _),
            Real.sqrt_eq_rpow (f x), ← Real.rpow_mul (hf0 x)]
          dsimp only [D]
          rw [show (1 / 2 : ℝ) * (1 - s.val) = (1 - s.val) / 2 by ring]
          ring
    calc
      _ ≤ (D * f x ^ ((1 - s.val) / 2) * g x ^ (s.val / 2)) ^ 2 :=
        pow_le_pow_left₀ (by dsimp only [F]; positivity) hb 2
      _ = _ := by
        rw [mul_pow, mul_pow, ← Real.rpow_natCast (f x ^ _),
          ← Real.rpow_mul (hf0 x), ← Real.rpow_natCast (g x ^ _),
          ← Real.rpow_mul (hg0 x)]
        norm_num only [Nat.cast_ofNat]
        ring_nf
  have hgeom : Integrable (fun x => f x ^ (1 - s.val) * g x ^ s.val) ν ∧
      (∫ x, f x ^ (1 - s.val) * g x ^ s.val ∂ν) ≤
        (∫ x, f x ∂ν) ^ (1 - s.val) * (∫ x, g x ∂ν) ^ s.val := by
    have ha : 0 < 1 - s.val := by linarith [s.property.2]
    have hpq : Real.HolderConjugate (1 - s.val)⁻¹ s.val⁻¹ := by
      apply Real.holderConjugate_iff.mpr
      constructor
      · exact (one_lt_inv₀ ha).mpr (by linarith [s.property.1])
      · simp
    have hfm : AEStronglyMeasurable (fun x => f x ^ (1 - s.val)) ν :=
      (hf.aestronglyMeasurable.aemeasurable.pow_const _).aestronglyMeasurable
    have hgm : AEStronglyMeasurable (fun x => g x ^ s.val) ν :=
      (hg.aestronglyMeasurable.aemeasurable.pow_const _).aestronglyMeasurable
    have hfp (x) : (f x ^ (1 - s.val)) ^ (1 - s.val)⁻¹ = f x := by
      rw [← Real.rpow_mul (hf0 x), mul_inv_cancel₀ ha.ne', Real.rpow_one]
    have hgp (x) : (g x ^ s.val) ^ s.val⁻¹ = g x := by
      rw [← Real.rpow_mul (hg0 x), mul_inv_cancel₀ s.property.1.ne', Real.rpow_one]
    have hfLp : MemLp (fun x => f x ^ (1 - s.val)) (ENNReal.ofReal (1 - s.val)⁻¹) ν := by
      apply (integrable_norm_rpow_iff hfm (by simp [s.property.2]) (by simp)).mp
      simpa only [ENNReal.toReal_ofReal (inv_nonneg.mpr ha.le),
        Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hf0 _) _), hfp] using hf
    have hgLp : MemLp (fun x => g x ^ s.val) (ENNReal.ofReal s.val⁻¹) ν := by
      apply (integrable_norm_rpow_iff hgm (by simp [s.property.1]) (by simp)).mp
      simpa only [ENNReal.toReal_ofReal (inv_nonneg.mpr s.property.1.le),
        Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hg0 _) _), hgp] using hg
    have : ENNReal.HolderConjugate (ENNReal.ofReal (1 - s.val)⁻¹)
        (ENNReal.ofReal s.val⁻¹) := hpq.ennrealOfReal
    refine ⟨hfLp.integrable_mul hgLp, ?_⟩
    have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
      (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (hf0 x) _))
      (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (hg0 x) _)) hfLp hgLp
    simpa only [hfp, hgp, one_div, inv_inv] using h
  have hresult : Integrable (fun x => F x ^ 2) ν ∧
      Real.sqrt (∫ x, F x ^ 2 ∂ν) ≤
        D * (Real.sqrt (∫ x, f x ∂ν)) ^ (1 - s.val) *
          (Real.sqrt (∫ x, g x ∂ν)) ^ s.val := by
    obtain ⟨hi, hle⟩ := hgeom
    have hFi : Integrable (fun x => F x ^ 2) ν :=
      (hi.const_mul (D ^ 2)).mono' (hFm.pow 2) (hsq.mono (fun x hx => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (F x))] using hx))
    refine ⟨hFi, ?_⟩
    have hbound := (integral_mono_ae hFi (hi.const_mul (D ^ 2)) hsq).trans
      (by simpa only [integral_const_mul] using
        mul_le_mul_of_nonneg_left hle (sq_nonneg D))
    have hfint : 0 ≤ ∫ x, f x ∂ν := integral_nonneg hf0
    have hgint : 0 ≤ ∫ x, g x ∂ν := integral_nonneg hg0
    calc
      _ ≤ Real.sqrt (D ^ 2 * ((∫ x, f x ∂ν) ^ (1 - s.val) * (∫ x, g x ∂ν) ^ s.val)) :=
        Real.sqrt_le_sqrt hbound
      _ = _ := by
        rw [Real.sqrt_mul (sq_nonneg D), Real.sqrt_sq hD,
          Real.sqrt_mul (Real.rpow_nonneg hfint _)]
        simp only [Real.sqrt_eq_rpow, ← Real.rpow_mul hfint, ← Real.rpow_mul hgint]
        ring_nf
  obtain ⟨hi, hb⟩ := hresult
  refine ⟨hi, ?_⟩
  have hDeq : D = Cg * Cl ^ (1 - s.val) * L ^ ((3 - s.val) / 2) := by
    dsimp only [D]
    rw [Real.mul_rpow hCl.le (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
      ← Real.rpow_mul hL.le]
    calc
      _ = Cg * Cl ^ (1 - s.val) * (L ^ (1 : ℝ) * L ^ (1 / 2 * (1 - s.val))) := by
        rw [Real.rpow_one]; ring
      _ = _ := by rw [← Real.rpow_add hL]; congr 2; ring
  simpa only [hDeq] using hb

/-- The L²-source extension at the end of the proof of Lemma 5.9: the exact periodized elliptic estimate,
with `p = (1-s/2)⁻¹` and the literal weights `L_(1/2)` and `L_(3/2-s)`.
The loss exponent precedes `ε` and `β`. The prefactor is uniform for
`β ≥ βlo > 0`. Finiteness of all three mixed norms is asserted explicitly.
The equation is the constrained weak equation, which eliminates the
scalar multiplier by testing against zero-sum fields. -/
theorem elliptic_L2 (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (κstar γstar : ℝ) (hκstar : 0 < κstar) (_hγstar : 0 < γstar) (M₀ : ℕ+) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε →
    ∀ Cstar : ℝ, 1 ≤ Cstar → ∀ βlo : ℝ, 0 < βlo → ∃ C : ℝ, 0 < C ∧
    ∀ β : ℝ, βlo ≤ β →
    ∀ {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
      (n m : ℕ+) (hm : 2 ≤ (m : ℕ)),
    (n : ℕ) ≤ (m : ℕ) →
    (m : ℝ) ≤ 3 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
    ⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ) ≤ (m : ℕ) / 4 →
    ∀ M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm (⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ))
      Cstar κstar γstar ε M →
    ∀ Q : ScalarFormData ν, IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
    ∀ (i₀ : Fin (m : ℕ)) (χ : Lp ℝ 2 ν) (u : Fin (m : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents (Fin (m : ℕ)))
      (fun i => if i = i₀ then χ else 0) u →
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    let H := Matrix.of (fun a b : Fin (m : ℕ) => sampledRieszKernel sh m hm (b - a))
    let F := fun x => (∑ i, |(H *ᵥ (fun j => (u j).val x)) i| ^
      (1 - s.val / 2)⁻¹) ^ (1 - s.val / 2)
    let w₁ := fun j => 1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (1 / 2 : ℝ)
    let w₂ := fun j => 1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (3 / 2 - s.val)
    Integrable (fun x => ∑ j, (w₁ j * (u j).val x) ^ 2) ν ∧
    Integrable (fun x => ∑ j, (w₂ j * (u j).val x) ^ 2) ν ∧
    Integrable (fun x => F x ^ 2) ν ∧
      Real.sqrt (∫ x, F x ^ 2 ∂ν) ≤
        C * (n : ℝ) ^ (κ * ε) *
          (‖χ‖ + Real.sqrt (∫ x, ∑ j, (w₁ j * (u j).val x) ^ 2 ∂ν)) ^ s.val *
          (Real.sqrt (∫ x, ∑ j, (w₂ j * (u j).val x) ^ 2 ∂ν)) ^ (1 - s.val) := by
  obtain ⟨κp, hκp, hp⟩ := elliptic_primitive_angular hz s κstar γstar hκstar M₀
  obtain ⟨Ci, hCi, hi⟩ := integrated_interpolation_angular hz s
  refine ⟨κp * s.val + 1, by nlinarith [s.property.1], fun ε hε Cstar hCstar βlo hβlo => ?_⟩
  obtain ⟨Cp, hCp, hp⟩ := hp ε hε Cstar hCstar βlo hβlo
  obtain ⟨D, hD, hlog⟩ := log_absorption s hε
    (by linarith [s.property.2] : 0 < (3 - s.val) / 2)
  refine ⟨Ci * Cp ^ s.val * D, by positivity,
    fun β hβ {α} _ ν _ n m hm _hnm hmn _hK M hM Q hQ _hQc i₀ χ u hu => ?_⟩
  obtain ⟨hJ, hwr, hprimitive₀⟩ := hp β hβ ν n m hm hmn M hM Q hQ χ i₀ u hu
  let w₁ := fun j => 1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (1 / 2 : ℝ)
  have hw₁ := (CyclicFourierL2.weighted_integral_sq w₁ (fun j => (u j).val)).1
  have hwle (j : Fin (m : ℕ)) : weightRadius m j i₀ ^ (1 / 2 : ℝ) ≤ w₁ j := by
    dsimp only [w₁]
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    have hd : 0 ≤ (Riesz1.cyclicIndexDistance m j i₀ : ℝ) := Nat.cast_nonneg _
    have hs := Real.sq_sqrt hd
    change 1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ≤
      (1 + Real.sqrt (Riesz1.cyclicIndexDistance m j i₀ : ℝ)) ^ 2
    nlinarith [Real.sqrt_nonneg (Riesz1.cyclicIndexDistance m j i₀ : ℝ)]
  have hprimitive := hprimitive₀.trans (mul_le_mul_of_nonneg_left
    (add_le_add_right (Real.sqrt_le_sqrt (integral_mono hwr hw₁ (fun x => by
      apply Finset.sum_le_sum
      intro j _
      rw [mul_pow, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Real.rpow_nonneg (by unfold weightRadius; positivity) _)
          (hwle j) 2) (sq_nonneg _)))) ‖χ‖) (by positivity))
  have hsum : ∀ᵐ x ∂ν, ∑ i, (u i).val x = 0 := hu.1.1
  obtain ⟨hF, hinterp⟩ := hi ν m hm (fun j => (u j).val) hsum i₀
  let L := Real.log (2 * (m : ℝ))
  let X := Real.sqrt (∫ x, ∑ j,
    ((1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (3 / 2 - s.val)) * (u j).val x) ^ 2 ∂ν)
  let Z := ‖χ‖ + Real.sqrt (∫ x, ∑ j,
    ((1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (1 / 2 : ℝ)) * (u j).val x) ^ 2 ∂ν)
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast n.pos
  have hL : 0 < L := Real.log_pos (by
    have : (1 : ℝ) ≤ m := by exact_mod_cast m.pos
    linarith)
  have hX : 0 ≤ X := Real.sqrt_nonneg _
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hw₂ := (CyclicFourierL2.weighted_integral_sq
    (fun j => 1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (3 / 2 - s.val))
    (fun j => (u j).val)).1
  refine ⟨hw₁, hw₂, hF, ?_⟩
  have hpPow := Real.rpow_le_rpow (Real.sqrt_nonneg _) hprimitive s.property.1.le
  have hbound := hinterp.trans (mul_le_mul_of_nonneg_left hpPow
    (by positivity : 0 ≤ Ci * L ^ ((3 - s.val) / 2) * X ^ (1 - s.val)))
  have heq : Ci * L ^ ((3 - s.val) / 2) * X ^ (1 - s.val) *
      (Cp * (n : ℝ) ^ (κp * ε) * Z) ^ s.val =
      Ci * Cp ^ s.val * L ^ ((3 - s.val) / 2) *
        (n : ℝ) ^ (κp * s.val * ε) * Z ^ s.val * X ^ (1 - s.val) := by
    rw [Real.mul_rpow (by positivity : 0 ≤ Cp * (n : ℝ) ^ (κp * ε)) hZ,
      Real.mul_rpow hCp.le (Real.rpow_nonneg hn0.le _), ← Real.rpow_mul hn0.le]
    rw [show κp * ε * s.val = κp * s.val * ε by ring]
    ring
  have hlog' := hlog n m hmn
  calc
    _ ≤ Ci * L ^ ((3 - s.val) / 2) * X ^ (1 - s.val) *
        (Cp * (n : ℝ) ^ (κp * ε) * Z) ^ s.val := hbound
    _ = _ := heq
    _ ≤ Ci * Cp ^ s.val * (D * (n : ℝ) ^ ε) *
        (n : ℝ) ^ (κp * s.val * ε) * Z ^ s.val * X ^ (1 - s.val) := by
      gcongr
    _ = _ := by
      rw [show (κp * s.val + 1) * ε = ε + κp * s.val * ε by ring,
        Real.rpow_add hn0]
      ring

/-- See Lemma 5.9 of the paper: the exact periodized elliptic estimate,
with `p = (1-s/2)⁻¹` and the literal weights `L_(1/2)` and `L_(3/2-s)`.
The loss exponent precedes `ε` and `β`. The prefactor is uniform for
`β ≥ βlo > 0`. Finiteness of all three mixed norms is asserted explicitly.
The equation is the constrained weak equation, which eliminates the
scalar multiplier by testing against zero-sum fields. -/
theorem elliptic (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (κstar γstar : ℝ) (hκstar : 0 < κstar) (_hγstar : 0 < γstar) (M₀ : ℕ+) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε →
    ∀ Cstar : ℝ, 1 ≤ Cstar → ∀ βlo : ℝ, 0 < βlo → ∃ C : ℝ, 0 < C ∧
    ∀ β : ℝ, βlo ≤ β →
    ∀ {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
      (n m : ℕ+) (hm : 2 ≤ (m : ℕ)),
    (n : ℕ) ≤ (m : ℕ) →
    (m : ℝ) ≤ 3 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
    ⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ) ≤ (m : ℕ) / 4 →
    ∀ M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm (⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ))
      Cstar κstar γstar ε M →
    ∀ Q : ScalarFormData ν, IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
    ∀ (i₀ : Fin (m : ℕ)) (χ : Q.1) (u : Fin (m : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents (Fin (m : ℕ)))
      (fun i => if i = i₀ then χ.val else 0) u →
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    let H := Matrix.of (fun a b : Fin (m : ℕ) => sampledRieszKernel sh m hm (b - a))
    let F := fun x => (∑ i, |(H *ᵥ (fun j => (u j).val x)) i| ^
      (1 - s.val / 2)⁻¹) ^ (1 - s.val / 2)
    let w₁ := fun j => 1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (1 / 2 : ℝ)
    let w₂ := fun j => 1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (3 / 2 - s.val)
    Integrable (fun x => ∑ j, (w₁ j * (u j).val x) ^ 2) ν ∧
    Integrable (fun x => ∑ j, (w₂ j * (u j).val x) ^ 2) ν ∧
    Integrable (fun x => F x ^ 2) ν ∧
      Real.sqrt (∫ x, F x ^ 2 ∂ν) ≤
        C * (n : ℝ) ^ (κ * ε) *
          (‖χ.val‖ + Real.sqrt (∫ x, ∑ j, (w₁ j * (u j).val x) ^ 2 ∂ν)) ^ s.val *
          (Real.sqrt (∫ x, ∑ j, (w₂ j * (u j).val x) ^ 2 ∂ν)) ^ (1 - s.val) := by
  obtain ⟨κ, hκ, h⟩ := elliptic_L2 hz s κstar γstar hκstar _hγstar M₀
  refine ⟨κ, hκ, fun ε hε Cstar hCstar βlo hβlo => ?_⟩
  obtain ⟨C, hC, h⟩ := h ε hε Cstar hCstar βlo hβlo
  refine ⟨C, hC, fun β hβ {α} _ ν _ n m hm hnm hmn hK M hM Q hQ hQc i₀ χ u hu => ?_⟩
  exact h β hβ ν n m hm hnm hmn hK M hM Q hQ hQc i₀ χ.val u hu

end Riesz2.EllipticRegularity
