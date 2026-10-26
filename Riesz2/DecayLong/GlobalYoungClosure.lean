/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.GlobalDecayPart2
public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# The four Young absorptions in the global decay estimate

The scalar inequalities in Step 5 of the proof of Lemma 5.13. The choice
of eta precedes four separate Young absorptions.
-/

@[expose] public section
noncomputable section

namespace Riesz2.GlobalDecay

/-- The exact eta of Lemma 5.13, Step 5, its admissible range, its
quadratic absorption coefficient and a polynomial bound for its inverse. -/
theorem paper_eta_internal (s A : ℝ) (hs : 0 < s) (hs1 : s < 1) (hA : 1 ≤ A) :
    let η := (64 * A ^ 2) ^ (-(3 - s)⁻¹)
    0 < η ∧ η < 1 / 4 ∧ A ^ 2 * η ^ (3 - s) = 1 / 64 ∧
      η⁻¹ ≤ 8 * A ^ 2 := by
  dsimp only
  let b := 64 * A ^ 2
  have hA0 : 0 < A := by linarith
  have hb : 0 < b := by dsimp [b]; positivity
  have hb64 : 64 ≤ b := by dsimp [b]; nlinarith
  have ht : 0 < 3 - s := by linarith
  have hp : (b ^ (-(3 - s)⁻¹)) ^ (3 - s) = b⁻¹ := by
    rw [← Real.rpow_mul hb.le, neg_mul, inv_mul_cancel₀ ht.ne', Real.rpow_neg_one]
  have hη : 0 < b ^ (-(3 - s)⁻¹) := Real.rpow_pos_of_pos hb _
  have hη4 : b ^ (-(3 - s)⁻¹) < 1 / 4 := by
    apply (Real.rpow_lt_rpow_iff hη.le (by norm_num) ht).mp
    rw [hp]
    have hi : b⁻¹ ≤ (64 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hb64
    have hh := Real.rpow_lt_rpow_of_exponent_gt
      (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1)
      (show 3 - s < 3 by linarith)
    norm_num only [Real.rpow_ofNat, one_div, inv_pow] at hh
    exact hi.trans_lt (by norm_num at hh ⊢; exact hh)
  have hcoef : A ^ 2 * (b ^ (-(3 - s)⁻¹)) ^ (3 - s) = 1 / 64 := by
    rw [hp]
    dsimp [b]
    field_simp
  have hinv : (b ^ (-(3 - s)⁻¹))⁻¹ ≤ 8 * A ^ 2 := by
    rw [Real.rpow_neg hb.le, inv_inv]
    have ht2 : (3 - s)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
    calc
      b ^ (3 - s)⁻¹ ≤ b ^ (2 : ℝ)⁻¹ :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) ht2
      _ ≤ 8 * A ^ 2 := by
        apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg hb.le _) (by positivity) (by norm_num : (0 : ℝ) < 2)).mp
        rw [Real.rpow_inv_rpow hb.le (by norm_num), Real.rpow_two]
        dsimp [b]
        nlinarith [sq_nonneg (A ^ 2 - 1)]
  exact ⟨hη, hη4, hcoef, hinv⟩

/-- Lemma 5.13, Step 5: insert the second weighted estimate into the
first at exactly `(64 A²)^(-1/(3-s))`, retaining a polynomial coefficient. -/
theorem combine_weighted_energy_paper (s A F X Z P Y : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (hA : 1 ≤ A)
    (hF : 0 ≤ F) (hX : 0 ≤ X) (hZ : 0 ≤ Z) (hP : 0 ≤ P)
    (hfirst : X ^ 2 ≤ A * (X * (F + Z + P) + Y))
    (hsecond : ∀ η : ℝ, 0 < η → η < 1 / 4 →
      Y ≤ A * (F ^ 2 + X * (η ^ (3 - s) * X + η⁻¹ * P + F + Z))) :
    X ^ 2 ≤ 16 * A ^ 4 * (F ^ 2 + X * (F + Z + P)) := by
  let η := (64 * A ^ 2) ^ (-(3 - s)⁻¹)
  obtain ⟨hη, hη4, hcoef, hinv⟩ := paper_eta_internal s A hs hs1 hA
  have hy := hsecond η hη hη4
  have hA0 : 0 ≤ A := by linarith
  have hraw := mul_le_mul_of_nonneg_left hy hA0
  have hsmall := congrArg (fun q => q * X ^ 2) hcoef
  have hi := mul_le_mul_of_nonneg_left hinv
    (show 0 ≤ A ^ 2 * X * P by positivity)
  have hsimpl : X ^ 2 ≤ X ^ 2 / 64 +
      (A + A ^ 2) * X * (F + Z + P) + 8 * A ^ 4 * X * P + A ^ 2 * F ^ 2 := by
    nlinarith only [hfirst, hraw, hsmall, hi,
      mul_nonneg (sq_nonneg A) (mul_nonneg hX hP)]
  have hAA : A ≤ A ^ 4 := by nlinarith [sq_nonneg (A ^ 2 - 1)]
  have hA2 : A ^ 2 ≤ A ^ 4 := by nlinarith [sq_nonneg (A ^ 2 - 1)]
  have h₁ := mul_le_mul_of_nonneg_right (add_le_add hAA hA2)
    (show 0 ≤ X * (F + Z + P) by positivity)
  have h₂ := mul_le_mul_of_nonneg_right hA2 (sq_nonneg F)
  have h₃ : 8 * A ^ 4 * X * P ≤ 8 * A ^ 4 * X * (F + Z + P) :=
    mul_le_mul_of_nonneg_left (by linarith : P ≤ F + Z + P) (by positivity)
  nlinarith only [hsimpl, h₁, h₂, h₃,
    mul_nonneg (by positivity : 0 ≤ A ^ 4) (sq_nonneg F),
    mul_nonneg (by positivity : 0 ≤ A ^ 4 * X) (by positivity : 0 ≤ F + Z + P)]

/-- Internal normalized form of the four Young absorptions in Lemma 5.13,
Step 5. For its `θ = 1/(3-2s)`, the last exponent is precisely
`2-s(2-2s)/(3-2s)`. The polynomial constants precede the energy constant. -/
theorem four_monomial_young_closure (s θ : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ D r : ℝ, 1 ≤ D ∧ 0 < r ∧ ∀ A x z p : ℝ,
      1 ≤ A → 0 ≤ x → 0 ≤ z →
      x ^ 2 ≤ 16 * A ^ 4 * (1 + x * (1 + z + p)) →
      z ≤ A * x ^ θ → p ≤ A * (1 + z) ^ s * x ^ (1 - s) →
      x + 1 ≤ D * A ^ r := by
  let δ := s * (1 - θ)
  let q := 2 / δ
  let r := 6 * q
  let c := (16 : ℝ) ^ q * 16 ^ q
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ < 1 := by dsimp [δ]; nlinarith
  have hq : 0 < q := by dsimp [q]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨34 + 8 * c, r, by linarith, hr, ?_⟩
  intro A x z p hA hx hz he hzi hpi
  have hA0 : 0 < A := by linarith
  have hAr : 1 ≤ A ^ r := Real.one_le_rpow hA hr.le
  have h4r : A ^ 4 ≤ A ^ r := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hA
    dsimp [r, q]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hδ).mpr
    nlinarith
  have hpow (t : ℝ) (ht : 0 < t) : x * x ^ t = x ^ (1 + t) := by
    rw [Real.rpow_add' hx (by linarith : 1 + t ≠ 0), Real.rpow_one]
  have hAs : A ^ s ≤ A := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hA hs1.le
  have hzs : z ^ s ≤ A * x ^ (θ * s) := by
    calc
      z ^ s ≤ (A * x ^ θ) ^ s := Real.rpow_le_rpow hz hzi hs.le
      _ = A ^ s * x ^ (θ * s) := by
        rw [Real.mul_rpow hA0.le (Real.rpow_nonneg hx _), ← Real.rpow_mul hx]
      _ ≤ _ := mul_le_mul_of_nonneg_right hAs (Real.rpow_nonneg hx _)
  have hbase : (1 + z) ^ s ≤ 1 + A * x ^ (θ * s) := by
    have hh := Real.rpow_add_le_add_rpow (by norm_num : (0 : ℝ) ≤ 1) hz hs.le hs1.le
    simp only [Real.one_rpow] at hh
    exact hh.trans (add_le_add_right hzs 1)
  have hprod : x ^ (θ * s) * x ^ (1 - s) = x ^ (1 - δ) := by
    rw [← Real.rpow_add' hx (by nlinarith : θ * s + (1 - s) ≠ 0)]
    congr 1
    dsimp [δ]
    ring
  have hpb : p ≤ A * x ^ (1 - s) + A ^ 2 * x ^ (1 - δ) := by
    calc
      p ≤ A * (1 + A * x ^ (θ * s)) * x ^ (1 - s) :=
        hpi.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbase hA0.le) (Real.rpow_nonneg hx _))
      _ = A * x ^ (1 - s) + A ^ 2 * (x ^ (θ * s) * x ^ (1 - s)) := by ring
      _ = _ := by rw [hprod]
  have hxz : x * z ≤ A * x ^ (1 + θ) := by
    have hh := mul_le_mul_of_nonneg_left hzi hx
    calc
      x * z ≤ x * (A * x ^ θ) := hh
      _ = A * (x * x ^ θ) := by ring
      _ = _ := by rw [hpow θ hθ]
  have hxp : x * p ≤ A * x ^ (2 - s) + A ^ 2 * x ^ (2 - δ) := by
    have hh := mul_le_mul_of_nonneg_left hpb hx
    calc
      x * p ≤ x * (A * x ^ (1 - s) + A ^ 2 * x ^ (1 - δ)) := hh
      _ = _ := by
        rw [mul_add, ← mul_assoc x A, mul_comm x A, mul_assoc,
          hpow (1 - s) (by linarith), ← mul_assoc x (A ^ 2), mul_comm x (A ^ 2),
          mul_assoc, hpow (1 - δ) (by linarith)]
        rw [show 1 + (1 - s) = 2 - s by ring,
          show 1 + (1 - δ) = 2 - δ by ring]
  have h46 : A ^ 4 ≤ A ^ 6 := pow_le_pow_right₀ hA (by norm_num)
  have h56 : A ^ 5 ≤ A ^ 6 := pow_le_pow_right₀ hA (by norm_num)
  have hmon : x ^ 2 ≤ 16 * A ^ 4 + 16 * A ^ 6 *
      (x ^ (1 : ℝ) + x ^ (1 + θ) + x ^ (2 - s) + x ^ (2 - δ)) := by
    have hb := mul_le_mul_of_nonneg_left (add_le_add hxz hxp)
      (show 0 ≤ 16 * A ^ 4 by positivity)
    have h₁ := mul_le_mul_of_nonneg_right h46 hx
    have h₂ := mul_le_mul_of_nonneg_right h56 (Real.rpow_nonneg hx (1 + θ))
    have h₃ := mul_le_mul_of_nonneg_right h56 (Real.rpow_nonneg hx (2 - s))
    rw [Real.rpow_one]
    nlinarith only [he, hb, h₁, h₂, h₃]
  -- Each monomial gets its own X²/16 allowance. Only their coefficient
  -- remainders, rather than the monomials, share a common polynomial bound.
  have young (t : ℝ) (ht : 0 < t) (hgap : δ ≤ 2 - t) :
      16 * A ^ 6 * x ^ t ≤ x ^ 2 / 16 + c * A ^ r := by
    have ht2 : t < 2 := by linarith
    have hg : 0 < 2 - t := by linarith
    have heq : 2 / (2 - t) ≤ q := by
      exact div_le_div_of_nonneg_left (by norm_num) hδ hgap
    have het : t / (2 - t) ≤ q :=
      (div_le_div_of_nonneg_right ht2.le hg.le).trans heq
    have h16 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 16) het
    have hB : (16 * A ^ 6) ^ (2 / (2 - t)) ≤ 16 ^ q * A ^ r := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 16) (by positivity),
        ← Real.rpow_natCast, ← Real.rpow_mul hA0.le]
      apply mul_le_mul
        (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 16) heq)
        (Real.rpow_le_rpow_of_exponent_le hA (by dsimp [r]; linarith))
        (Real.rpow_nonneg hA0.le _) (Real.rpow_nonneg (by norm_num) _)
    have hh := subquadratic_absorption t ht ht2 (16 * A ^ 6) 1 x
      (by positivity) (by norm_num) hx
    simp only [Real.one_rpow, one_pow, mul_one] at hh
    apply hh.trans
    apply add_le_add_right
    calc
      _ ≤ 16 ^ q * (16 ^ q * A ^ r) := mul_le_mul h16 hB
        (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by norm_num) _)
      _ = c * A ^ r := by dsimp [c]; ring
  have hy₁ := young 1 (by norm_num) (by linarith)
  have hy₂ := young (1 + θ) (by linarith) (by dsimp [δ]; nlinarith)
  have hy₃ := young (2 - s) (by linarith) (by dsimp [δ]; nlinarith)
  have hy₄ := young (2 - δ) (by linarith) (by linarith)
  have hb : x ^ 2 ≤ (32 + 8 * c) * A ^ r := by
    have hh := mul_le_mul_of_nonneg_left h4r (by norm_num : (0 : ℝ) ≤ 16)
    nlinarith only [hmon, hy₁, hy₂, hy₃, hy₄, hh, mul_nonneg hc (Real.rpow_nonneg hA0.le r)]
  nlinarith only [hb, hAr, sq_nonneg (x - 1)]

/-- Internal homogeneous scalar closure for Lemma 5.13, Step 5, using
the exact eta and four separate Young absorptions. The zero-source case
is supplied by the unweighted equation in `global_decay_bounds`. -/
theorem scalar_young_closure_internal (s θ : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ D r : ℝ, 1 ≤ D ∧ 0 < r ∧ ∀ A F U X Z P Y : ℝ,
      1 ≤ A → 0 < F → 0 ≤ U → 0 ≤ X → 0 ≤ Z → 0 ≤ P →
      U ≤ A * F → Z ≤ U ^ (1 - θ) * X ^ θ →
      P ≤ A * (F + Z) ^ s * X ^ (1 - s) →
      X ^ 2 ≤ A * (X * (F + Z + P) + Y) →
      (∀ η : ℝ, 0 < η → η < 1 / 4 →
        Y ≤ A * (F ^ 2 + X * (η ^ (3 - s) * X + η⁻¹ * P + F + Z))) →
      F + X ≤ D * A ^ r * F := by
  obtain ⟨D, r, hD, hr, hclose⟩ := four_monomial_young_closure s θ hs hs1 hθ hθ1
  refine ⟨D, r, hD, hr, ?_⟩
  intro A F U X Z P Y hA hF hU hX hZ hP hUF hzi hpi he hy
  let x := X / F
  let z := Z / F
  let p := P / F
  have hx : 0 ≤ x := div_nonneg hX hF.le
  have hz : 0 ≤ z := div_nonneg hZ hF.le
  have hxx : F * x = X := by dsimp [x]; field_simp
  have hzz : F * z = Z := by dsimp [z]; field_simp
  have hpp : F * p = P := by dsimp [p]; field_simp
  have hom (u v a : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
      (F * u) ^ a * (F * v) ^ (1 - a) = F * (u ^ a * v ^ (1 - a)) := by
    rw [Real.mul_rpow hF.le hu, Real.mul_rpow hF.le hv]
    calc
      _ = (F ^ a * F ^ (1 - a)) * (u ^ a * v ^ (1 - a)) := by ring
      _ = _ := by rw [← Real.rpow_add hF]; norm_num
  have hz' : z ≤ A * x ^ θ := by
    have haθ : A ^ (1 - θ) ≤ A := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hA
        (show 1 - θ ≤ 1 by linarith)
    have hb := hzi.trans (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hU hUF (by linarith : 0 ≤ 1 - θ)) (by positivity))
    rw [← hxx, mul_comm A F] at hb
    have hid : (F * A) ^ (1 - θ) * (F * x) ^ θ = F * (A ^ (1 - θ) * x ^ θ) := by
      simpa only [show 1 - (1 - θ) = θ by ring] using hom A x (1 - θ) (by linarith) hx
    rw [hid, ← hzz] at hb
    apply (mul_le_mul_iff_right₀ hF).mp
    exact hb.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right haθ (by positivity)) hF.le)
  have hp' : p ≤ A * (1 + z) ^ s * x ^ (1 - s) := by
    have hb := hpi
    rw [← hzz, ← hxx, show F + F * z = F * (1 + z) by ring] at hb
    have hid := hom (1 + z) x s (by positivity) hx
    have hb' : F * p ≤ F * (A * (1 + z) ^ s * x ^ (1 - s)) := by
      rw [← hpp] at hb
      calc
        F * p ≤ A * ((F * (1 + z)) ^ s * (F * x) ^ (1 - s)) := by nlinarith only [hb]
        _ = _ := by rw [hid]; ring
    exact (mul_le_mul_iff_right₀ hF).mp hb'
  have he' := combine_weighted_energy_paper s A F X Z P Y hs hs1 hA hF.le hX hZ hP he hy
  have hn : x ^ 2 ≤ 16 * A ^ 4 * (1 + x * (1 + z + p)) := by
    rw [← hxx, ← hzz, ← hpp] at he'
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hF)).mp
    nlinarith only [he']
  have hh := mul_le_mul_of_nonneg_left (hclose A x z p hA hx hz hn hz' hp') hF.le
  rw [mul_add, mul_one, hxx] at hh
  nlinarith only [hh]

end Riesz2.GlobalDecay
