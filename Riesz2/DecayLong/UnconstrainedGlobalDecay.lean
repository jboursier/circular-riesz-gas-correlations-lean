/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.GlobalDecayPart3

/-!
# Unconstrained global decay and its constant-mode correction

The unconstrained estimate of Lemma 5.14 and its constant-mode correction
in Subsection 5.4. The scalar resolvent and vector equations use the same
scalar form domain.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter
open scoped BigOperators Matrix

namespace Riesz2.UnconstrainedGlobalDecay

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
  {ν : Measure Ω}

/-- Subtraction on the full bounded matrix form domain, used in Subsection 5.4. -/
theorem weak_sub_internal (Q : ScalarFormData ν) (M : Ω → Matrix ι ι ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hMb : ∃ B : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ B)
    (g h : ι → Lp ℝ 2 ν) (u v : ι → Q.1)
    (hu : WeightedWeakSolution Q M ⊤ g u)
    (hv : WeightedWeakSolution Q M ⊤ h v) :
    WeightedWeakSolution Q M ⊤ (fun i => g i - h i) (fun i => u i - v i) := by
  refine ⟨(BoundedMatrixForms.domain_iff Q M hMm hMb ⊤ _).mpr
    (Eventually.of_forall (fun _ => Submodule.mem_top)), ?_⟩
  intro z hz
  have he := hu.2 z hz
  have hf := hv.2 z hz
  have hp : matrixFieldPair M (fun i => (u i - v i).val) (fun i => (z i).val) =ᵐ[ν]
      fun x => matrixFieldPair M (fun i => (u i).val) (fun i => (z i).val) x -
        matrixFieldPair M (fun i => (v i).val) (fun i => (z i).val) x := by
    filter_upwards [ae_all_iff.mpr (fun i => Lp.coeFn_sub (u i).val (v i).val)] with x hx
    simp only [matrixFieldPair, Submodule.coe_sub, hx, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  refine ⟨BoundedMatrixForms.integrable_pair M hMm hMb _ _, ?_⟩
  rw [integral_congr_ae hp, integral_sub he.1 hf.1]
  simp only [map_sub, LinearMap.sub_apply, Finset.sum_sub_distrib, inner_sub_left]
  linarith only [he.2, hf.2]

/-- Scalar shifted resolvent on the whole domain, with both energy bounds.
This supplies the uniquely specified scalar correction of Subsection 5.4. -/
theorem scalar_resolvent_internal (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (b : ℝ) (hb : 0 < b) (g : Lp ℝ 2 ν) :
    ∃! f : Q.1,
      (∀ z : Q.1, Q.2 f z + b * inner ℝ f.val z.val = inner ℝ g z.val) ∧
      ‖f.val‖ ≤ b⁻¹ * ‖g‖ ∧
      Real.sqrt (Q.2 f f) ≤ Real.sqrt b⁻¹ * ‖g‖ := by
  let f := ScalarFormHilbert.equiv Q hQ (ScalarFormHilbert.shiftedSolution Q hQ b hb g)
  have he (z : Q.1) : Q.2 f z + b * inner ℝ f.val z.val = inner ℝ g z.val :=
    ScalarFormHilbert.shiftedSolution_solves Q hQ b hb g ((ScalarFormHilbert.equiv Q hQ).symm z)
  have hn : ‖f.val‖ ≤ b⁻¹ * ‖g‖ :=
    ScalarFormHilbert.shiftedSolution_value_norm_le Q hQ b hb g
  refine ⟨f, ⟨he, hn, ?_⟩, ?_⟩
  · have he' := he f
    rw [real_inner_self_eq_norm_sq] at he'
    have hpair := real_inner_le_norm g f.val
    have hprod := mul_le_mul_of_nonneg_left hn (norm_nonneg g)
    have hsq : Q.2 f f ≤ b⁻¹ * ‖g‖ ^ 2 := by
      nlinarith only [he', hpair, hprod, mul_nonneg hb.le (sq_nonneg ‖f.val‖)]
    have hroot := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_mul (inv_nonneg.mpr hb.le), Real.sqrt_sq (norm_nonneg g)] at hroot
  · intro k hk
    have hh := ScalarFormHilbert.shiftedSolution_unique Q hQ b hb g
      ((ScalarFormHilbert.equiv Q hQ).symm k) (fun z => hk.1 _)
    exact congrArg (ScalarFormHilbert.equiv Q hQ) hh

/-- Both weighted seminorms obey a uniform triangle bound, including zero energy.
The weights act on component indices only, as in Subsection 5.4. -/
theorem weighted_triangle_internal (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (a b : ι → ℝ) (hb : ∀ i, 0 ≤ b i)
    (u v : ι → Q.1) :
    Real.sqrt (∑ i, (a i * ‖(u i + v i).val‖) ^ 2) ≤
      2 * (Real.sqrt (∑ i, (a i * ‖(u i).val‖) ^ 2) +
        Real.sqrt (∑ i, (a i * ‖(v i).val‖) ^ 2)) ∧
    Real.sqrt (∑ i, b i * Q.2 (u i + v i) (u i + v i)) ≤
      2 * (Real.sqrt (∑ i, b i * Q.2 (u i) (u i)) +
        Real.sqrt (∑ i, b i * Q.2 (v i) (v i))) := by
  have hsqrt (A B D : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
      (h : D ≤ 2 * A + 2 * B) : Real.sqrt D ≤ 2 * (Real.sqrt A + Real.sqrt B) := by
    nlinarith only [Real.sq_sqrt hA, Real.sq_sqrt hB, Real.sq_sqrt hD,
      Real.sqrt_nonneg A, Real.sqrt_nonneg B, Real.sqrt_nonneg D,
      mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B), h]
  constructor
  · apply hsqrt _ _ _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hn := norm_add_le (u i).val (v i).val
    have hh : ‖(u i + v i).val‖ ^ 2 ≤ 2 * ‖(u i).val‖ ^ 2 + 2 * ‖(v i).val‖ ^ 2 := by
      change ‖(u i).val + (v i).val‖ ^ 2 ≤ _
      nlinarith [norm_nonneg ((u i).val + (v i).val), norm_nonneg (u i).val,
        norm_nonneg (v i).val, sq_nonneg (‖(u i).val‖ - ‖(v i).val‖)]
    nlinarith only [mul_le_mul_of_nonneg_left hh (sq_nonneg (a i))]
  · apply hsqrt _ _ _ (Finset.sum_nonneg (fun i _ => mul_nonneg (hb i) (hQ.2.2.1 _)))
      (Finset.sum_nonneg (fun i _ => mul_nonneg (hb i) (hQ.2.2.1 _)))
      (Finset.sum_nonneg (fun i _ => mul_nonneg (hb i) (hQ.2.2.1 _)))
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hh : Q.2 (u i + v i) (u i + v i) ≤ 2 * Q.2 (u i) (u i) + 2 * Q.2 (v i) (v i) := by
      have hn := hQ.2.2.1 (u i - v i)
      simp only [map_sub, LinearMap.sub_apply] at hn
      simp only [map_add, LinearMap.add_apply]
      linarith only [hn]
    nlinarith only [mul_le_mul_of_nonneg_left hh (hb i)]


/-- Lifting a scalar resolvent to the constant component vector retains the
entire row error. This is the exact equation subtraction in Subsection 5.4. -/
theorem lift_scalar_internal (Q : ScalarFormData ν) (M : Ω → Matrix ι ι ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hMb : ∃ B : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ B)
    (hsym : ∀ᵐ x ∂ν, ∀ i j, M x i j = M x j i)
    (b : ℝ) (f : Q.1) (g : Lp ℝ 2 ν) (p : ι → Lp ℝ 2 ν)
    (hp : ∀ i, ∀ᵐ x ∂ν, p i x = ((∑ j, M x i j) - b) * f.val x)
    (hf : ∀ z : Q.1, Q.2 f z + b * inner ℝ f.val z.val = inner ℝ g z.val) :
    WeightedWeakSolution Q M ⊤ (fun i => g + p i) (fun _ => f) := by
  refine ⟨(BoundedMatrixForms.domain_iff Q M hMm hMb ⊤ _).mpr
    (Eventually.of_forall (fun _ => Submodule.mem_top)), ?_⟩
  intro z _
  have hpair : matrixFieldPair M (fun _ : ι => f.val) (fun i => (z i).val) =ᵐ[ν]
      fun x => ∑ i, (b * (f.val x * (z i).val x) + p i x * (z i).val x) := by
    filter_upwards [hsym, ae_all_iff.mpr hp] with x hs hx
    simp only [matrixFieldPair]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [hx i]
    calc
      _ = (∑ j, M x i j) * f.val x * (z i).val x := by
        rw [Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        rw [hs j i]
        ring
      _ = _ := by ring
  have hinner (a c : Lp ℝ 2 ν) : (∫ x, a x * c x ∂ν) = inner ℝ a c := by
    rw [L2.inner_def]
    simp only [Real.inner_apply]
  have hint : (∫ x, matrixFieldPair M (fun _ : ι => f.val) (fun i => (z i).val) x ∂ν) =
      ∑ i, (b * inner ℝ f.val (z i).val + inner ℝ (p i) (z i).val) := by
    rw [integral_congr_ae hpair, integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      rw [integral_add, integral_const_mul, hinner, hinner]
      · exact ((Lp.memLp f.val).integrable_mul (Lp.memLp (z i).val)).const_mul b
      · exact (Lp.memLp (p i)).integrable_mul (Lp.memLp (z i).val)
    · intro i _
      exact (((Lp.memLp f.val).integrable_mul (Lp.memLp (z i).val)).const_mul b).add
        ((Lp.memLp (p i)).integrable_mul (Lp.memLp (z i).val))
  refine ⟨BoundedMatrixForms.integrable_pair M hMm hMb _ _, ?_⟩
  rw [hint, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_add_left]
  linarith only [hf (z i)]

/-- Replication on the complete component cycle has its exact counting-measure
normalization. No loss depending on the scalar dimension occurs. -/
theorem replication_norm_internal (m : ℕ+) (Q : ScalarFormData ν) (f : Q.1) :
    Real.sqrt (∑ _ : Fin (m : ℕ), ‖f.val‖ ^ 2) = Real.sqrt (m : ℝ) * ‖f.val‖ ∧
    Real.sqrt (∑ _ : Fin (m : ℕ), Q.2 f f) = Real.sqrt (m : ℝ) * Real.sqrt (Q.2 f f) := by
  simp [Finset.sum_const, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ m),
    Real.sqrt_sq (norm_nonneg f.val)]

/-- Scalar power bookkeeping in the proof of Lemma 5.14. The multiplier's
factor m⁻¹ is retained before using the positive reference row mass. -/
theorem scalar_powers_internal (s m c βlo β ell D F : ℝ)
    (hm : 1 ≤ m) (hc : 0 < c) (hβlo : 0 < βlo) (hβ : βlo ≤ β)
    (hell : c * m ^ (1 - s) ≤ ell) (_hD : 0 ≤ D) (_hF : 0 ≤ F)
    (L f g : ℝ) (hL0 : 0 ≤ L) (hL : L ≤ D * m⁻¹ * F)
    (hf : f ≤ (β * ell)⁻¹ * L) (hg : g ≤ Real.sqrt (β * ell)⁻¹ * L) :
    f ≤ (βlo * c)⁻¹ * D * m ^ (-(2 - s)) * F ∧
    g ≤ Real.sqrt (βlo * c)⁻¹ * D * m ^ (-(3 - s) / 2) * F := by
  have hm0 : 0 < m := by linarith
  have hβ0 : 0 < β := hβlo.trans_le hβ
  have hell0 : 0 < ell := (mul_pos hc (Real.rpow_pos_of_pos hm0 _)).trans_le hell
  have hbl : βlo * c * m ^ (1 - s) ≤ β * ell := by
    nlinarith only [mul_le_mul hβ hell (by positivity) hβ0.le]
  have hi : (β * ell)⁻¹ ≤ (βlo * c)⁻¹ * m ^ (s - 1) := by
    calc
      _ ≤ (βlo * c * m ^ (1 - s))⁻¹ :=
        inv_anti₀ (by positivity : 0 < βlo * c * m ^ (1 - s)) hbl
      _ = _ := by
        rw [mul_inv, ← Real.rpow_neg hm0.le]
        rw [show -(1 - s) = s - 1 by ring]
  constructor
  · calc
      f ≤ ((βlo * c)⁻¹ * m ^ (s - 1)) * (D * m⁻¹ * F) :=
        hf.trans (mul_le_mul hi hL hL0 (by positivity))
      _ = _ := by
        rw [← Real.rpow_neg_one m, show -(2 - s) = (s - 1) + (-1) by ring,
          Real.rpow_add hm0]
        ring
  · calc
      g ≤ Real.sqrt ((βlo * c)⁻¹ * m ^ (s - 1)) * (D * m⁻¹ * F) :=
        hg.trans (mul_le_mul (Real.sqrt_le_sqrt hi) hL hL0 (by positivity))
      _ = _ := by
        have hsqrt : Real.sqrt (m ^ (s - 1)) = m ^ ((s - 1) * (1 / 2)) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hm0.le]
        rw [Real.sqrt_mul (by positivity : 0 ≤ (βlo * c)⁻¹), hsqrt,
          ← Real.rpow_neg_one m,
          show -(3 - s) / 2 = (s - 1) * (1 / 2) + (-1) by ring, Real.rpow_add hm0]
        ring


/-- Exact remainder equation and its unweighted energy estimate, the algebraic
part of the proof of Lemma 5.14. All additional bounds are internal. -/
theorem remainder_internal (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (m : ℕ+) (M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hMb : ∃ B : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ B)
    (β a : ℝ) (hβ : 0 < β) (ha : 0 < a)
    (hl : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
      ∀ z : Fin (m : ℕ) → ℝ, a * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j)
    (H : Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ) (ell B : ℝ)
    (hH : ∀ i, ∑ j, H i j = ell) (hB : 0 ≤ B)
    (hrow : ∀ᵐ x ∂ν, ∀ i, ∑ j, |(M x - H) i j| ≤ B)
    (χ lam : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ)) (u v : Fin (m : ℕ) → Q.1)
    (hu : WeightedWeakSolution Q (fun x => β • M x) ⊤
      (fun i => if i = i₀ then χ else 0) u)
    (hv : WeightedWeakSolution Q (fun x => β • M x) ⊤
      (fun i => (if i = i₀ then χ else 0) + lam) v)
    (f : Q.1) (hf : ∀ z : Q.1,
      Q.2 f z + (β * ell) * inner ℝ f.val z.val = inner ℝ (-lam) z.val) :
    ∃ g : Fin (m : ℕ) → Lp ℝ 2 ν,
      (∀ i, ∀ᵐ x ∂ν, g i x = -β * f.val x * ∑ j, (M x - H) i j) ∧
      WeightedWeakSolution Q (fun x => β • M x) ⊤ g
        (fun i => u i - v i - f) ∧
      Real.sqrt (∑ i, ‖(u i - v i - f).val‖ ^ 2) +
        Real.sqrt (∑ i, Q.2 (u i - v i - f) (u i - v i - f)) ≤
          (1 + 2 * (β * a)⁻¹) * (β * B) * Real.sqrt (m : ℝ) * ‖f.val‖ := by
  let d := fun (i : Fin (m : ℕ)) (x : Ω) => β * ((∑ j, M x i j) - ell)
  have hd (i) : Measurable (d i) :=
    ((Finset.measurable_sum _ (fun j _ => hMm i j)).sub_const ell).const_mul β
  have hdsum (i) (x : Ω) : d i x = β * ∑ j, (M x - H) i j := by
    simp only [d, Matrix.sub_apply, Finset.sum_sub_distrib, hH]
  have hdb (i) : ∀ᵐ x ∂ν, |d i x| ≤ β * B := by
    filter_upwards [hrow] with x hx
    rw [hdsum, abs_mul, abs_of_pos hβ]
    exact mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (hx i)) hβ.le
  have hex (i) := BoundedMatrixModes.exists_multiplier (d i) (hd i) (β * B)
    (mul_nonneg hβ.le hB) (hdb i) f.val
  choose p hp hpn using hex
  have hPm : ∀ i j, Measurable (fun x => (β • M x) i j) :=
    fun i j => (hMm i j).const_mul β
  have hPb : ∃ b : ℝ, ∀ᵐ x ∂ν, ∀ i j, |(β • M x) i j| ≤ b := by
    obtain ⟨b, hb⟩ := hMb
    refine ⟨β * b, hb.mono (fun x hx i j => ?_)⟩
    simpa only [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hβ] using
      mul_le_mul_of_nonneg_left (hx i j) hβ.le
  have hPs : ∀ᵐ x ∂ν, ∀ i j, (β • M x) i j = (β • M x) j i :=
    hl.mono (fun _ hx i j => by simp only [Matrix.smul_apply, smul_eq_mul, hx.1 i j])
  have hp' (i) : ∀ᵐ x ∂ν, p i x = ((∑ j, (β • M x) i j) - β * ell) * f.val x := by
    filter_upwards [hp i] with x hx
    rw [hx]
    simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, d]
    ring
  have hrep := lift_scalar_internal Q (fun x => β • M x) hPm hPb hPs
    (β * ell) f (-lam) p hp' hf
  have hw := weak_sub_internal Q (fun x => β • M x) hPm hPb _ _ u v hu hv
  have hr := weak_sub_internal Q (fun x => β • M x) hPm hPb _ _ _ _ hw hrep
  have hr' : WeightedWeakSolution Q (fun x => β • M x) ⊤ (fun i => -p i)
      (fun i => u i - v i - f) := by
    convert hr using 1
    funext i
    abel
  have he := (AbstractEquation.existence_energy Q hQ β hβ M hMm a ha hl ⊤
    (fun i => -p i)).2 _ hr'
  have hsource : ‖(WithLp.toLp 2 (fun i => -p i) :
      PiLp 2 (fun _ : Fin (m : ℕ) => Lp ℝ 2 ν))‖ ≤ Real.sqrt (m : ℝ) * (β * B * ‖f.val‖) := by
    rw [PiLp.norm_eq_of_L2]
    have hh := Real.sqrt_le_sqrt (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      pow_le_pow_left₀ (norm_nonneg (-p i)) (by simpa only [norm_neg] using hpn i) 2))
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ m),
      Real.sqrt_sq (by positivity : 0 ≤ β * B * ‖f.val‖)] using hh
  have hi : (Real.sqrt (β * a))⁻¹ ≤ 1 + (β * a)⁻¹ := by
    rw [← Real.sqrt_inv]
    nlinarith only [Real.sq_sqrt (by positivity : 0 ≤ (β * a)⁻¹),
      Real.sqrt_nonneg ((β * a)⁻¹)]
  refine ⟨fun i => -p i, fun i => ?_, hr', ?_⟩
  · filter_upwards [Lp.coeFn_neg (p i), hp i] with x hx hpix
    rw [hx, Pi.neg_apply, hpix, hdsum]
    ring
  · have hvn := he.1.trans (mul_le_mul_of_nonneg_left hsource (by positivity))
    have hgn := he.2.trans (mul_le_mul hi hsource (norm_nonneg _) (by positivity))
    rw [PiLp.norm_eq_of_L2] at hvn
    change Real.sqrt (∑ i, ‖(u i - v i - f).val‖ ^ 2) ≤ _ at hvn
    nlinarith only [hvn, hgn]


/-- On a finite cycle both weights are bounded by the corresponding power of
its size. This is the last step of Lemma 5.14. -/
theorem weight_bound_internal (m : ℕ+) (hm : 2 ≤ (m : ℕ)) (i₀ : Fin (m : ℕ))
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (u : Fin (m : ℕ) → Q.1) :
    Real.sqrt (∑ i, (weightRadius m i i₀ ^ ρ * ‖(u i).val‖) ^ 2) ≤
      (m : ℝ) ^ ρ * Real.sqrt (∑ i, ‖(u i).val‖ ^ 2) ∧
    Real.sqrt (∑ i, weightRadius m i i₀ ^ (2 * ρ) * Q.2 (u i) (u i)) ≤
      (m : ℝ) ^ ρ * Real.sqrt (∑ i, Q.2 (u i) (u i)) := by
  have hw (i) : weightRadius m i i₀ ≤ (m : ℝ) := by
    have hd := Riesz1.APG.cyclicIndexDistance_le_half (N := m) i i₀
    have hn : 1 + Riesz1.cyclicIndexDistance m i i₀ ≤ (m : ℕ) := by omega
    dsimp only [weightRadius]
    exact_mod_cast hn
  have hw0 (i) : 0 ≤ weightRadius m i i₀ := (zero_le_one.trans (one_le_weightRadius m i i₀))
  have hwp (i) : weightRadius m i i₀ ^ ρ ≤ (m : ℝ) ^ ρ :=
    Real.rpow_le_rpow (by linarith [one_le_weightRadius m i i₀]) (hw i) hρ
  constructor
  · have hh := GlobalDecay.weighted_norm_mono_internal (fun i => (u i).val)
      (fun i => weightRadius m i i₀ ^ ρ) (fun _ => 1) ((m : ℝ) ^ ρ) (by positivity)
      (fun i => Real.rpow_nonneg (hw0 i) _) (fun _ => by norm_num)
      (fun i => by simpa only [mul_one] using hwp i)
    simpa only [one_mul] using hh
  · have hpow (x : ℝ) (hx : 0 ≤ x) : x ^ (2 * ρ) = (x ^ ρ) ^ 2 := by
      rw [← Real.rpow_two, ← Real.rpow_mul hx]
      congr 1
      ring
    have hp (i) : weightRadius m i i₀ ^ (2 * ρ) ≤ ((m : ℝ) ^ ρ) ^ 2 := by
      rw [hpow _ (hw0 i)]
      exact pow_le_pow_left₀ (Real.rpow_nonneg (hw0 i) _) (hwp i) 2
    have hs := Real.sqrt_le_sqrt (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_right (hp i) (hQ.2.2.1 (u i))))
    rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (by positivity : 0 ≤ (m : ℝ) ^ ρ)] at hs
    exact hs

/-- The remainder and the replicated scalar estimates give both unweighted
correction bounds of the proof of Lemma 5.14. -/
theorem correction_triangle_internal (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (s : Riesz1.RieszExponent)
    (m : ℕ+) (T F : ℝ) (hT : 1 ≤ T) (hF : 0 ≤ F)
    (u v : Fin (m : ℕ) → Q.1) (f : Q.1)
    (hf : ‖f.val‖ ≤ T ^ 2 * (m : ℝ) ^ (-(2 - s.val)) * F)
    (hfg : Real.sqrt (Q.2 f f) ≤ T ^ 2 * (m : ℝ) ^ (-(3 - s.val) / 2) * F)
    (hr : Real.sqrt (∑ i, ‖(u i - v i - f).val‖ ^ 2) +
      Real.sqrt (∑ i, Q.2 (u i - v i - f) (u i - v i - f)) ≤
        T ^ 4 * (m : ℝ) ^ (-(3 / 2 - s.val)) * F) :
    Real.sqrt (∑ i, ‖(u i - v i).val‖ ^ 2) ≤
      4 * T ^ 4 * (m : ℝ) ^ (-(3 / 2 - s.val)) * F ∧
    Real.sqrt (∑ i, Q.2 (u i - v i) (u i - v i)) ≤
      4 * T ^ 4 * (m : ℝ) ^ (-(1 - s.val / 2)) * F := by
  have hm0 : (0 : ℝ) < m := by positivity
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast m.pos
  have hT24 : T ^ 2 ≤ T ^ 4 := pow_le_pow_right₀ hT (by norm_num)
  have hrep := replication_norm_internal m Q f
  have hrepv : Real.sqrt (∑ _ : Fin (m : ℕ), ‖f.val‖ ^ 2) ≤
      T ^ 4 * (m : ℝ) ^ (-(3 / 2 - s.val)) * F := by
    rw [hrep.1]
    calc
      _ ≤ Real.sqrt (m : ℝ) * (T ^ 2 * (m : ℝ) ^ (-(2 - s.val)) * F) :=
        mul_le_mul_of_nonneg_left hf (Real.sqrt_nonneg _)
      _ = T ^ 2 * (m : ℝ) ^ (-(3 / 2 - s.val)) * F := by
        rw [Real.sqrt_eq_rpow, show -(3 / 2 - s.val) = 1 / 2 + (-(2 - s.val)) by ring,
          Real.rpow_add hm0]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hT24 (by positivity)) hF
  have hrepg : Real.sqrt (∑ _ : Fin (m : ℕ), Q.2 f f) ≤
      T ^ 4 * (m : ℝ) ^ (-(1 - s.val / 2)) * F := by
    rw [hrep.2]
    calc
      _ ≤ Real.sqrt (m : ℝ) * (T ^ 2 * (m : ℝ) ^ (-(3 - s.val) / 2) * F) :=
        mul_le_mul_of_nonneg_left hfg (Real.sqrt_nonneg _)
      _ = T ^ 2 * (m : ℝ) ^ (-(1 - s.val / 2)) * F := by
        rw [Real.sqrt_eq_rpow,
          show -(1 - s.val / 2) = 1 / 2 + (-(3 - s.val) / 2) by ring, Real.rpow_add hm0]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hT24 (by positivity)) hF
  have hmono : T ^ 4 * (m : ℝ) ^ (-(3 / 2 - s.val)) * F ≤
      T ^ 4 * (m : ℝ) ^ (-(1 - s.val / 2)) * F :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hm1 (by linarith [s.property.2])) (by positivity)) hF
  have ht := weighted_triangle_internal Q hQ (fun _ => 1) (fun _ => 1)
    (fun _ => by norm_num) (fun i => u i - v i - f) (fun _ => f)
  simp only [sub_add_cancel, one_mul] at ht
  constructor
  · nlinarith only [ht.1, hr, hrepv, Real.sqrt_nonneg (∑ i, Q.2 (u i - v i - f) (u i - v i - f))]
  · nlinarith only [ht.2, hr, hrepg, hmono, Real.sqrt_nonneg (∑ i, ‖(u i - v i - f).val‖ ^ 2)]


/-- Normalized scalar and remainder bounds for the proof of Lemma 5.14.
The comparison premises belong only to this internal assembly lemma. -/
theorem correction_bounds_internal (s : Riesz1.RieszExponent) (m : ℕ+)
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hMb : ∃ B : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ B)
    (β a : ℝ) (hβ : 0 < β) (ha : 0 < a)
    (hl : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
      ∀ z : Fin (m : ℕ) → ℝ, a * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j)
    (H : Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ) (ell c βlo T Be : ℝ)
    (hH : ∀ i, ∑ j, H i j = ell) (hc : 0 < c) (hβlo : 0 < βlo) (hβloβ : βlo ≤ β)
    (hell : c * (m : ℝ) ^ (1 - s.val) ≤ ell) (hT : 1 ≤ T)
    (hRT : (βlo * c)⁻¹ ≤ T) (hRsT : Real.sqrt (βlo * c)⁻¹ ≤ T)
    (henergyT : 1 + 2 * (β * a)⁻¹ ≤ T) (hBe : 0 ≤ Be)
    (hrow : ∀ᵐ x ∂ν, ∀ i, ∑ j, |(M x - H) i j| ≤ Be) (hβBe : β * Be ≤ T)
    (χ lam : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ)) (u v : Fin (m : ℕ) → Q.1)
    (hu : WeightedWeakSolution Q (fun x => β • M x) ⊤ (fun i => if i = i₀ then χ else 0) u)
    (hvfull : WeightedWeakSolution Q (fun x => β • M x) ⊤
      (fun i => (if i = i₀ then χ else 0) + lam) v)
    (hlamT : ‖lam‖ ≤ T * (m : ℝ)⁻¹ * ‖χ‖) :
    ∃ (f : Q.1) (g : Fin (m : ℕ) → Lp ℝ 2 ν),
      (∀ z : Q.1, Q.2 f z + (β * ell) * inner ℝ f.val z.val = inner ℝ (-lam) z.val) ∧
      ‖f.val‖ ≤ T ^ 2 * (m : ℝ) ^ (-(2 - s.val)) * ‖χ‖ ∧
      Real.sqrt (Q.2 f f) ≤ T ^ 2 * (m : ℝ) ^ (-(3 - s.val) / 2) * ‖χ‖ ∧
      (∀ i, ∀ᵐ x ∂ν, g i x = -β * f.val x * ∑ j, (M x - H) i j) ∧
      WeightedWeakSolution Q (fun x => β • M x) ⊤ g (fun i => u i - v i - f) ∧
      Real.sqrt (∑ i, ‖(u i - v i - f).val‖ ^ 2) +
        Real.sqrt (∑ i, Q.2 (u i - v i - f) (u i - v i - f)) ≤
          T ^ 4 * (m : ℝ) ^ (-(3 / 2 - s.val)) * ‖χ‖ ∧
      Real.sqrt (∑ i, ‖(u i - v i).val‖ ^ 2) ≤
        4 * T ^ 4 * (m : ℝ) ^ (-(3 / 2 - s.val)) * ‖χ‖ ∧
      Real.sqrt (∑ i, Q.2 (u i - v i) (u i - v i)) ≤
        4 * T ^ 4 * (m : ℝ) ^ (-(1 - s.val / 2)) * ‖χ‖ := by
  have hm0 : (0 : ℝ) < m := by positivity
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast m.pos
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hell0 : 0 < ell := (by positivity : 0 < c * (m : ℝ) ^ (1 - s.val)).trans_le hell
  obtain ⟨f, ⟨hfeq, hfn, hfgn⟩, _⟩ := scalar_resolvent_internal Q hQ (β * ell) (mul_pos hβ hell0) (-lam)
  simp only [norm_neg] at hfn hfgn
  obtain ⟨hf, hfg⟩ := scalar_powers_internal s.val m c βlo β ell T ‖χ‖ hm1 hc hβlo hβloβ hell
    hT0 (norm_nonneg χ) ‖lam‖ ‖f.val‖ (Real.sqrt (Q.2 f f)) (norm_nonneg _) hlamT hfn hfgn
  have hfT : ‖f.val‖ ≤ T ^ 2 * (m : ℝ) ^ (-(2 - s.val)) * ‖χ‖ := by
    have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hRT hT0)
      (by positivity : 0 ≤ (m : ℝ) ^ (-(2 - s.val)) * ‖χ‖)
    nlinarith only [hf, hb]
  have hfgT : Real.sqrt (Q.2 f f) ≤ T ^ 2 * (m : ℝ) ^ (-(3 - s.val) / 2) * ‖χ‖ := by
    have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hRsT hT0)
      (by positivity : 0 ≤ (m : ℝ) ^ (-(3 - s.val) / 2) * ‖χ‖)
    nlinarith only [hfg, hb]
  obtain ⟨g, hg, hgeq, hgest⟩ := remainder_internal Q hQ m M hMm
    hMb β a hβ ha hl H ell Be hH hBe hrow
    χ lam i₀ u v hu hvfull f hfeq
  have hrT : Real.sqrt (∑ i, ‖(u i - v i - f).val‖ ^ 2) +
      Real.sqrt (∑ i, Q.2 (u i - v i - f) (u i - v i - f)) ≤
        T ^ 4 * (m : ℝ) ^ (-(3 / 2 - s.val)) * ‖χ‖ := by
    have hcoef : (1 + 2 * (β * a)⁻¹) * (β * Be) ≤ T ^ 2 := by
      nlinarith only [mul_le_mul henergyT hβBe (by positivity : 0 ≤ β * Be) hT0]
    have hh := mul_le_mul hcoef hfT (norm_nonneg f.val) (sq_nonneg T)
    have hh' := mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg (m : ℝ))
    have hid : Real.sqrt (m : ℝ) *
        (T ^ 2 * (T ^ 2 * (m : ℝ) ^ (-(2 - s.val)) * ‖χ‖)) =
          T ^ 4 * (m : ℝ) ^ (-(3 / 2 - s.val)) * ‖χ‖ := by
      rw [Real.sqrt_eq_rpow, show -(3 / 2 - s.val) = 1 / 2 + (-(2 - s.val)) by ring,
        Real.rpow_add hm0]
      ring
    rw [hid] at hh'
    exact hgest.trans (by nlinarith only [hh'])
  obtain ⟨hwT, hwgT⟩ := correction_triangle_internal Q hQ s m T ‖χ‖ hT
    (norm_nonneg _) u v f hfT hfgT hrT
  exact ⟨f, g, hfeq, hfT, hfgT, hg, hgeq, hrT, hwT, hwgT⟩

/-- Uniform loss bookkeeping for the proof of Lemma 5.14. -/
theorem loss_bounds_internal (n : ℕ+) (ε κv κe κstar Cv Ce Cstar βlo βhi β c : ℝ)
    (hε : 0 < ε) (hκv : 0 < κv) (hκe : 0 < κe) (hκstar : 0 < κstar)
    (hCv : 0 < Cv) (hCe : 1 ≤ Ce) (hCstar : 1 ≤ Cstar)
    (hβlo : 0 < βlo) (hβhi : βlo ≤ βhi) (hβloβ : βlo ≤ β) (hc : 0 < c) :
    let k := κv + κe + κstar
    let R := (βlo * c)⁻¹
    let D := 2 + Cv + βhi * Ce + 2 * βlo⁻¹ * Cstar + R + Real.sqrt R
    let T := D * (n : ℝ) ^ (k * ε)
    let a := Cstar⁻¹ * (n : ℝ) ^ (-κstar * ε)
    let A := 4 * D ^ 4 * (n : ℝ) ^ (4 * k * ε)
    1 ≤ T ∧ A = 4 * T ^ 4 ∧
    Cv * (n : ℝ) ^ (κv * ε) ≤ T ∧ βhi * Ce * (n : ℝ) ^ (κe * ε) ≤ T ∧
    R ≤ T ∧ Real.sqrt R ≤ T ∧ 1 + 2 * (β * a)⁻¹ ≤ T ∧
    T ≤ A ∧ T ^ 2 ≤ A ∧ T ^ 4 ≤ A := by
  let k := κv + κe + κstar
  have hk : 0 < k := by dsimp [k]; positivity
  let R := (βlo * c)⁻¹
  let D := 2 + Cv + βhi * Ce + 2 * βlo⁻¹ * Cstar + R + Real.sqrt R
  let T := D * (n : ℝ) ^ (k * ε)
  let a := Cstar⁻¹ * (n : ℝ) ^ (-κstar * ε)
  let A := 4 * D ^ 4 * (n : ℝ) ^ (4 * k * ε)
  have hβhi0 := hβlo.trans_le hβhi
  have hR : 0 < R := by dsimp [R]; positivity
  have hβCe : 0 ≤ βhi * Ce := mul_nonneg hβhi0.le (by linarith only [hCe])
  have hiC : 0 ≤ 2 * βlo⁻¹ * Cstar := by positivity
  have hD : 1 ≤ D := by
    dsimp only [D]
    linarith only [hCv, hβCe, hiC, hR, Real.sqrt_nonneg R]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by positivity
  have hP : 1 ≤ (n : ℝ) ^ (k * ε) := Real.one_le_rpow hn1 (mul_nonneg hk.le hε.le)
  have hT : 1 ≤ T := one_le_mul_of_one_le_of_one_le hD hP
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hT24 : T ^ 2 ≤ T ^ 4 := pow_le_pow_right₀ hT (by norm_num)
  have hT14 : T ≤ T ^ 4 := by
    simpa only [pow_one] using (pow_le_pow_right₀ hT (by norm_num : 1 ≤ (4 : ℕ)))
  have hAT : A = 4 * T ^ 4 := by
    dsimp only [A, T]
    have hp : ((n : ℝ) ^ (k * ε)) ^ 4 = (n : ℝ) ^ (4 * k * ε) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
      congr 1
      norm_num
      ring
    rw [mul_pow, hp]
    ring
  have hcoeff (t d : ℝ) (ht : t ≤ k) (hd : d ≤ D) :
      d * (n : ℝ) ^ (t * ε) ≤ T :=
    mul_le_mul hd (Real.rpow_le_rpow_of_exponent_le hn1
      (mul_le_mul_of_nonneg_right ht hε.le)) (by positivity) (by linarith only [hD])
  have hCvT : Cv * (n : ℝ) ^ (κv * ε) ≤ T := hcoeff κv Cv
    (by dsimp [k]; linarith only [hκe, hκstar])
    (by dsimp only [D]; linarith only [hCv, hβCe, hiC, hR, Real.sqrt_nonneg R])
  have hCeT : βhi * Ce * (n : ℝ) ^ (κe * ε) ≤ T := hcoeff κe (βhi * Ce)
    (by dsimp [k]; linarith only [hκv, hκstar]) (by dsimp only [D]; linarith only [hCv, hβCe, hiC, hR, Real.sqrt_nonneg R])
  have hRT : R ≤ T := by
    have hd : R ≤ D := by dsimp only [D]; linarith only [hCv, hβCe, hiC, hR, Real.sqrt_nonneg R]
    exact hd.trans (by nlinarith only [hP, hD])
  have hRsT : Real.sqrt R ≤ T := by
    have hd : Real.sqrt R ≤ D := by dsimp only [D]; linarith only [hCv, hβCe, hiC, hR, Real.sqrt_nonneg R]
    exact hd.trans (by nlinarith only [hP, hD])
  have hinv : (β * a)⁻¹ ≤ βlo⁻¹ * Cstar * (n : ℝ) ^ (κstar * ε) := by
    have hid : (β * a)⁻¹ = β⁻¹ * Cstar * (n : ℝ) ^ (κstar * ε) := by
      dsimp [a]
      rw [mul_inv_rev, mul_inv_rev, inv_inv, ← Real.rpow_neg hn0.le,
        neg_mul, neg_neg]
      ring
    rw [hid]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (inv_anti₀ hβlo hβloβ) (by linarith only [hCstar]))
      (by positivity)
  have henergyT : 1 + 2 * (β * a)⁻¹ ≤ T := by
    have hh := hcoeff κstar (1 + 2 * βlo⁻¹ * Cstar)
      (by dsimp [k]; linarith only [hκv, hκe]) (by dsimp only [D]; linarith only [hCv, hβCe, hiC, hR, Real.sqrt_nonneg R])
    have hp := Real.one_le_rpow hn1 (mul_nonneg hκstar.le hε.le)
    nlinarith only [hh, hinv, hp]
  have hTA : T ≤ A := by rw [hAT]; nlinarith only [hT14, hT]
  have hT2A : T ^ 2 ≤ A := by rw [hAT]; nlinarith only [hT24, sq_nonneg T]
  have hT4A : T ^ 4 ≤ A := by rw [hAT]; nlinarith only [sq_nonneg (T ^ 2)]
  exact ⟨hT, hAT, hCvT, hCeT, hRT, hRsT, henergyT, hTA, hT2A, hT4A⟩

/-- See the proof of Lemma 5.14 in the paper (Quantitative constant-mode correction).
All seven estimates, the scalar resolvent equation and the exact remainder
source are included. Solutions are constructed on the full form domain.
The common loss exponent precedes ε, the structural prefactor and temperature.
The nested equations uniquely specify v and f, as in Subsection 5.4. -/
theorem global_bis_mean (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ)
    (hκstar : 0 < κstar) (hγstar : 0 < γstar) (M₀ : ℕ+) :
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
    ∀ (χ : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ)),
    let ell := 2 * ∑ k, sampledRieszKernel s m hm k
    let H := (2 : ℝ) • rieszMatrix s m hm
    let A := C * (n : ℝ) ^ (κ * ε)
    ∃! u : Fin (m : ℕ) → Q.1,
      WeightedWeakSolution Q (fun x => β • M x) ⊤
        (fun i => if i = i₀ then χ else 0) u ∧
      ∃ (v : Fin (m : ℕ) → Q.1) (lam : Lp ℝ 2 ν) (f : Q.1),
        WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _)
          (fun i => if i = i₀ then χ else 0) v ∧
        (∀ᵐ x ∂ν, lam x = gapMultiplierField m Q (fun x => β • M x)
          (fun i => if i = i₀ then χ else 0) v x) ∧
        WeightedWeakSolution Q (fun x => β • M x) ⊤
          (fun i => (if i = i₀ then χ else 0) + lam) v ∧
        (∀ z : Q.1, Q.2 f z + (β * ell) * inner ℝ f.val z.val = inner ℝ (-lam) z.val) ∧
        Real.sqrt (∑ i, (weightRadius m i i₀ ^ (3 / 2 - s.val) * ‖(v i).val‖) ^ 2) +
          Real.sqrt (∑ i, weightRadius m i i₀ ^ (2 * (1 - s.val / 2)) * Q.2 (v i) (v i)) ≤
            A * ‖χ‖ ∧
        (m : ℝ) * ‖lam‖ ≤ A * ‖χ‖ ∧
        ‖f.val‖ ≤ A * (m : ℝ) ^ (-(2 - s.val)) * ‖χ‖ ∧
        Real.sqrt (Q.2 f f) ≤ A * (m : ℝ) ^ (-(3 - s.val) / 2) * ‖χ‖ ∧
        WeightedWeakSolution Q (fun x => β • M x) ⊤ (fun _ => -lam) (fun i => u i - v i) ∧
        (∃ g : Fin (m : ℕ) → Lp ℝ 2 ν,
          (∀ i, ∀ᵐ x ∂ν, g i x = -β * f.val x * ∑ j, (M x - H) i j) ∧
          WeightedWeakSolution Q (fun x => β • M x) ⊤ g (fun i => u i - v i - f)) ∧
        Real.sqrt (∑ i, ‖(u i - v i - f).val‖ ^ 2) +
          Real.sqrt (∑ i, Q.2 (u i - v i - f) (u i - v i - f)) ≤
            A * (m : ℝ) ^ (-(3 / 2 - s.val)) * ‖χ‖ ∧
        Real.sqrt (∑ i, ‖(u i - v i).val‖ ^ 2) ≤
          A * (m : ℝ) ^ (-(3 / 2 - s.val)) * ‖χ‖ ∧
        Real.sqrt (∑ i, Q.2 (u i - v i) (u i - v i)) ≤
          A * (m : ℝ) ^ (-(1 - s.val / 2)) * ‖χ‖ := by
  obtain ⟨κv, hκv, hv⟩ := GlobalDecay.global_decay hzeta s κstar γstar hκstar hγstar M₀
  obtain ⟨κe, hκe, he⟩ := global_error_differences s κstar γstar hκstar.le hγstar.le M₀
  obtain ⟨c, Cmass, hc, _, hmass⟩ := global_reference_mass_bounds s
  let k := κv + κe + κstar
  have hk : 0 < k := by dsimp [k]; positivity
  refine ⟨4 * k, by positivity, fun ε hε Cstar hCstar βlo hβlo βhi hβhi => ?_⟩
  obtain ⟨Cv, hCv, hv⟩ := hv ε hε Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Ce, hCe, he⟩ := he ε hε Cstar hCstar
  let R := (βlo * c)⁻¹
  let D := 2 + Cv + βhi * Ce + 2 * βlo⁻¹ * Cstar + R + Real.sqrt R
  have hβhi0 := hβlo.trans_le hβhi
  have hR : 0 < R := by dsimp [R]; positivity
  have hβCe : 0 ≤ βhi * Ce := mul_nonneg hβhi0.le (by linarith only [hCe])
  have hiC : 0 ≤ 2 * βlo⁻¹ * Cstar := by positivity
  have hD : 1 ≤ D := by
    dsimp only [D]
    linarith only [hCv, hβCe, hiC, hR, Real.sqrt_nonneg R]
  refine ⟨4 * D ^ 4, by positivity, ?_⟩
  intro Ω _ ν _ Q hQ hQc n m hm hn hnm hmn K hK hKm M hM β hβloβ hββhi χ i₀ ell H A
  let T := D * (n : ℝ) ^ (k * ε)
  let a := Cstar⁻¹ * (n : ℝ) ^ (-κstar * ε)
  have ha : 0 < a := SchurRestriction.periodized_mass_pos hCstar
  have hβ : 0 < β := hβlo.trans_le hβloβ
  have hm0 : (0 : ℝ) < m := by positivity
  obtain ⟨hT, hAT, hCvT, hCeT, hRT, hRsT, henergyT, hTA, hT2A, hT4A⟩ :=
    loss_bounds_internal n ε κv κe κstar Cv Ce Cstar βlo βhi β c
      hε hκv hκe hκstar hCv hCe hCstar hβlo hβhi hβloβ hc
  have hAT' : A = 4 * T ^ 4 := hAT
  have hl : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
      ∀ z : Fin (m : ℕ) → ℝ,
        a * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j :=
    hM.2.1.mono (fun _ hx => ⟨hx.1, hx.2.2.1⟩)
  obtain ⟨u, hu, huniq⟩ := (AbstractEquation.existence_energy Q hQ β hβ M hM.1 a ha hl ⊤
    (fun i => if i = i₀ then χ else 0)).1
  obtain ⟨v, ⟨hvc, lam, hlam, hvfull, hvest, hlamest, _⟩, _⟩ :=
    hv ν Q hQ hQc n m hm hn hnm hmn hK hKm M hM β hβloβ hββhi χ i₀
  have hlamT : ‖lam‖ ≤ T * (m : ℝ)⁻¹ * ‖χ‖ := hlamest.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCvT (by positivity)) (norm_nonneg χ))
  have hvT : Real.sqrt (∑ i, (weightRadius m i i₀ ^ (3 / 2 - s.val) * ‖(v i).val‖) ^ 2) +
      Real.sqrt (∑ i, weightRadius m i i₀ ^ (2 * (1 - s.val / 2)) * Q.2 (v i) (v i)) ≤
        T * ‖χ‖ := hvest.trans (mul_le_mul_of_nonneg_right hCvT (norm_nonneg χ))
  have hell : c * (m : ℝ) ^ (1 - s.val) ≤ ell := by
    have hh := (hmass m hm i₀).1
    simpa only [ell, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, rieszMatrix_row_sum] using hh
  obtain ⟨ae, B, _, _, _, _, heae⟩ := he n m hm hn hnm hmn hK hKm ν M hM
  let Be := Ce * (n : ℝ) ^ (κe * ε)
  have hBe : 0 ≤ Be := by dsimp [Be]; positivity
  have hrow : ∀ᵐ x ∂ν, ∀ i, ∑ j, |(M x - H) i j| ≤ Be :=
    heae.mono (fun _ hx => hx.2.2.2.1)
  have hH (i) : ∑ j, H i j = ell := by
    simp only [H, ell, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, rieszMatrix_row_sum]
  have hβBe : β * Be ≤ T := by
    have hb : β * Be ≤ βhi * Be := mul_le_mul_of_nonneg_right hββhi hBe
    apply hb.trans
    calc
      βhi * Be = βhi * Ce * (n : ℝ) ^ (κe * ε) := by dsimp only [Be]; ring
      _ ≤ T := hCeT
  obtain ⟨f, g, hfeq, hfT, hfgT, hg, hgeq, hrT, hwT, hwgT⟩ :=
    correction_bounds_internal s m Q hQ M hM.1 (SchurRestriction.periodized_bounded hM)
      β a hβ ha hl H ell c βlo T Be hH hc hβlo hβloβ hell hT hRT hRsT henergyT hBe
      hrow hβBe χ lam i₀ u v hu hvfull hlamT
  have hw : WeightedWeakSolution Q (fun x => β • M x) ⊤ (fun _ => -lam)
      (fun i => u i - v i) := by
    have hh := weak_sub_internal Q _ (SchurRestriction.periodized_scaled_measurable β hM)
      (SchurRestriction.periodized_scaled_bounded β hM) _ _ u v hu hvfull
    convert hh using 1
    funext i
    abel
  refine ⟨u, ⟨hu, v, lam, f, hvc, hlam, hvfull, hfeq,
    hvT.trans (mul_le_mul_of_nonneg_right hTA (norm_nonneg χ)), ?_, ?_, ?_,
    hw, ⟨g, hg, hgeq⟩, ?_, ?_, ?_⟩, fun z hz => huniq z hz.1⟩
  · have hh := mul_le_mul_of_nonneg_left hlamT hm0.le
    have hid : (m : ℝ) * (T * (m : ℝ)⁻¹ * ‖χ‖) = T * ‖χ‖ := by field_simp
    rw [hid] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hTA (norm_nonneg χ))
  · exact hfT.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hT2A (by positivity)) (norm_nonneg χ))
  · exact hfgT.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hT2A (by positivity)) (norm_nonneg χ))
  · exact hrT.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hT4A (by positivity)) (norm_nonneg χ))
  · rw [hAT']
    exact hwT
  · rw [hAT']
    exact hwgT


/-- See Lemma 5.14 of the paper (Global decay, unconstrained equation).
Unique weak solvability and the weighted value and gradient bound for every L²
source. Constants are uniform on any compact positive temperature interval. -/
theorem global_bis (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ)
    (hκstar : 0 < κstar) (hγstar : 0 < γstar) (M₀ : ℕ+) :
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
    ∀ (χ : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ)),
    ∃! u : Fin (m : ℕ) → Q.1,
      WeightedWeakSolution Q (fun x => β • M x) ⊤
        (fun i => if i = i₀ then χ else 0) u ∧
      Real.sqrt (∑ i, (weightRadius m i i₀ ^ (3 / 2 - s.val) * ‖(u i).val‖) ^ 2) +
        Real.sqrt (∑ i, weightRadius m i i₀ ^ (2 * (1 - s.val / 2)) * Q.2 (u i) (u i)) ≤
          C * (n : ℝ) ^ (κ * ε) * ‖χ‖ := by
  obtain ⟨κ, hκ, hmean⟩ := global_bis_mean hzeta s κstar γstar hκstar hγstar M₀
  refine ⟨κ, hκ, fun ε hε Cstar hCstar βlo hβlo βhi hβhi => ?_⟩
  obtain ⟨C, hC, hmean⟩ := hmean ε hε Cstar hCstar βlo hβlo βhi hβhi
  refine ⟨6 * C, by positivity, ?_⟩
  intro Ω _ ν _ Q hQ hQc n m hm hn hnm hmn K hK hKm M hM β hβloβ hββhi χ i₀
  obtain ⟨u, ⟨hu, v, lam, f, _, _, _, _, hvEst, _, _, _, _, _, _, hwEst, hwgEst⟩, _⟩ :=
    hmean ν Q hQ hQc n m hm hn hnm hmn hK hKm M hM β hβloβ hββhi χ i₀
  let A := C * (n : ℝ) ^ (κ * ε)
  have hm0 : (0 : ℝ) < m := by positivity
  have hα : 0 ≤ 3 / 2 - s.val := by linarith only [s.property.2]
  have hb : 0 ≤ 1 - s.val / 2 := by linarith only [s.property.2]
  have hvalue := (weight_bound_internal m hm i₀ Q hQ _ hα (fun i => u i - v i)).1
  have hgrad := (weight_bound_internal m hm i₀ Q hQ _ hb (fun i => u i - v i)).2
  have hcancel (ρ : ℝ) : (m : ℝ) ^ ρ * (A * (m : ℝ) ^ (-ρ) * ‖χ‖) = A * ‖χ‖ := by
    calc
      _ = A * ((m : ℝ) ^ ρ * (m : ℝ) ^ (-ρ)) * ‖χ‖ := by ring
      _ = _ := by rw [← Real.rpow_add hm0, add_neg_cancel, Real.rpow_zero, mul_one]
  have hwv : Real.sqrt (∑ i, (weightRadius m i i₀ ^ (3 / 2 - s.val) * ‖(u i - v i).val‖) ^ 2) ≤
      A * ‖χ‖ := by
    have hh := mul_le_mul_of_nonneg_left hwEst (by positivity : 0 ≤ (m : ℝ) ^ (3 / 2 - s.val))
    exact hvalue.trans (hh.trans_eq (hcancel _))
  have hwg : Real.sqrt (∑ i, weightRadius m i i₀ ^ (2 * (1 - s.val / 2)) *
      Q.2 (u i - v i) (u i - v i)) ≤ A * ‖χ‖ := by
    have hh := mul_le_mul_of_nonneg_left hwgEst (by positivity : 0 ≤ (m : ℝ) ^ (1 - s.val / 2))
    exact hgrad.trans (hh.trans_eq (hcancel _))
  have ht := weighted_triangle_internal Q hQ
    (fun i => weightRadius m i i₀ ^ (3 / 2 - s.val))
    (fun i => weightRadius m i i₀ ^ (2 * (1 - s.val / 2)))
    (fun i => Real.rpow_nonneg (by linarith only [one_le_weightRadius m i i₀]) _)
    v (fun i => u i - v i)
  have hadd (i) : v i + (u i - v i) = u i := by abel
  simp only [hadd] at ht
  have hfinal : Real.sqrt (∑ i, (weightRadius m i i₀ ^ (3 / 2 - s.val) * ‖(u i).val‖) ^ 2) +
      Real.sqrt (∑ i, weightRadius m i i₀ ^ (2 * (1 - s.val / 2)) * Q.2 (u i) (u i)) ≤
        (6 * C) * (n : ℝ) ^ (κ * ε) * ‖χ‖ := by
    have hh : Real.sqrt (∑ i, (weightRadius m i i₀ ^ (3 / 2 - s.val) * ‖(u i).val‖) ^ 2) +
        Real.sqrt (∑ i, weightRadius m i i₀ ^ (2 * (1 - s.val / 2)) * Q.2 (u i) (u i)) ≤
          6 * A * ‖χ‖ := by
      nlinarith only [ht.1, ht.2, hvEst, hwv, hwg]
    convert hh using 1
    dsimp only [A]
    ring
  have hl : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
      ∀ z : Fin (m : ℕ) → ℝ,
        (Cstar⁻¹ * (n : ℝ) ^ (-κstar * ε)) * (∑ i, z i ^ 2) ≤
          ∑ i, ∑ j, z i * M x i j * z j :=
    hM.2.1.mono (fun _ hx => ⟨hx.1, hx.2.2.1⟩)
  have huniq := (AbstractEquation.existence_energy Q hQ β (hβlo.trans_le hβloβ)
    M hM.1 _ (SchurRestriction.periodized_mass_pos hCstar) hl ⊤
    (fun i => if i = i₀ then χ else 0)).1
  exact ⟨u, ⟨hu, hfinal⟩, fun z hz => huniq.unique hz.1 hu⟩

end Riesz2.UnconstrainedGlobalDecay
