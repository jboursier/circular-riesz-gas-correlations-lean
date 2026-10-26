/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.OptimalLocalizationPart5
public import Riesz2.DecayLong.PhysicalCorePart7
public import Riesz2.ToMathlib.BoundedMatrixModes

/-!
# The mean of an unrestricted periodic lift

Supporting identities and estimates for the proof of Proposition 5.18. All
scalar equations act on the scalar form domain.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators

namespace Riesz2.PhysicalMean

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι] {ν : Measure X}

/-- Internal summation identity for the proof of Proposition 5.18. The error
is constructed in L² from the row errors of the symmetric reference. The
weak equation is tested on the entire scalar form domain. -/
theorem sum_equation_internal (Q : ScalarFormData ν)
    (M : X → Matrix ι ι ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hMb : ∃ B : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ B)
    (H : Matrix ι ι ℝ) (ell B : ℝ) (hB : 0 ≤ B)
    (hrow : ∀ i, ∑ j, H i j = ell)
    (herr : ∀ᵐ x ∂ν, ∀ i, |∑ j, (M x i j - H i j)| ≤ B)
    (f : ι → Lp ℝ 2 ν) (u : ι → Q.1)
    (hu : WeightedWeakSolution Q M ⊤ f u) :
    ∃ g : Lp ℝ 2 ν,
      (∀ᵐ x ∂ν, g x = ∑ i, ∑ j, (u i).val x * (M x i j - H i j)) ∧
      ‖g‖ ≤ B * ∑ i, ‖(u i).val‖ ∧
      ∀ w : Q.1, Q.2 (∑ i, u i) w +
        ell * inner ℝ (∑ i, (u i).val) w.val =
          inner ℝ ((∑ i, f i) - g) w.val := by
  classical
  let d : ι → X → ℝ := fun i x => ∑ j, (M x i j - H i j)
  have hd (i) : Measurable (d i) :=
    Finset.measurable_sum _ (fun j _ => (hMm i j).sub measurable_const)
  have hex (i) := BoundedMatrixModes.exists_multiplier (d i) (hd i) B hB
    (herr.mono (fun x hx => hx i)) (u i).val
  choose g hg hgn using hex
  have hgv : ∀ᵐ x ∂ν, (∑ i, g i) x = ∑ i, ∑ j,
      (u i).val x * (M x i j - H i j) := by
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ g, ae_all_iff.mpr hg] with x hs hx
    rw [hs]
    apply Finset.sum_congr rfl
    intro i _
    rw [hx i]
    dsimp only [d]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  refine ⟨∑ i, g i, hgv, ?_, ?_⟩
  · calc
      _ ≤ ∑ i, ‖g i‖ := norm_sum_le _ _
      _ ≤ ∑ i, B * ‖(u i).val‖ := Finset.sum_le_sum (fun i _ => hgn i)
      _ = _ := (Finset.mul_sum _ _ _).symm
  intro w
  have hw : WeightedFormDomain Q M ⊤ (fun _ : ι => w) :=
    (BoundedMatrixForms.domain_iff Q M hMm hMb ⊤ _).mpr
      (Eventually.of_forall (fun _ => Submodule.mem_top))
  have ht := hu.2 (fun _ => w) hw
  have hq : (∑ i, Q.2 (u i) w) = Q.2 (∑ i, u i) w := by
    simp only [map_sum, LinearMap.sum_apply]
  have hf : (∑ i, inner ℝ (f i) w.val) = inner ℝ (∑ i, f i) w.val :=
    (sum_inner _ _ _).symm
  have huv : ∀ᵐ x ∂ν, (∑ i, (u i).val) x = ∑ i, (u i).val x :=
    Lp.coeFn_fun_finsetSum Finset.univ _
  have hp : matrixFieldPair M (fun i => (u i).val) (fun _ => w.val) =ᵐ[ν]
      fun x => ell * ((∑ i, (u i).val) x * w.val x) + (∑ i, g i) x * w.val x := by
    filter_upwards [hgv, huv] with x hgx hux
    rw [hgx, hux]
    simp only [matrixFieldPair]
    have he (i) : ∑ j, (u i).val x * M x i j * w.val x =
        ell * (u i).val x * w.val x +
          (∑ j, (u i).val x * (M x i j - H i j)) * w.val x := by
      have hs : ∑ j, (M x i j - H i j) = (∑ j, M x i j) - ell := by
        rw [Finset.sum_sub_distrib, hrow]
      rw [← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum, hs]
      ring
    simp_rw [he]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum]
    ring
  have hi := integral_congr_ae hp
  rw [integral_add, integral_const_mul] at hi
  · have hinner (v : Lp ℝ 2 ν) : (∫ x, v x * w.val x ∂ν) = inner ℝ v w.val := by
      rw [L2.inner_def]
      simp only [Real.inner_apply]
    rw [hinner, hinner] at hi
    rw [hq, hf, hi] at ht
    rw [inner_sub_left]
    linarith [ht.2]
  · exact ((Lp.memLp _).integrable_mul (Lp.memLp w.val)).const_mul ell
  · exact (Lp.memLp _).integrable_mul (Lp.memLp w.val)

/-- Testing the scalar summed equation gives its positive-mass resolvent
estimate. This is an internal energy step of the proof of Proposition 5.18. -/
theorem scalar_mean_norm_internal (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (b : ℝ) (hb : 0 < b)
    (g : Lp ℝ 2 ν) (u : Q.1)
    (hu : ∀ w : Q.1, Q.2 u w + b * inner ℝ u.val w.val = inner ℝ g w.val) :
    ‖u.val‖ ≤ b⁻¹ * ‖g‖ := by
  have he := hu u
  rw [real_inner_self_eq_norm_sq] at he
  have hi := real_inner_le_norm g u.val
  have hp := hQ.2.2.1 u
  by_cases hz : ‖u.val‖ = 0
  · rw [hz]; positivity
  have hn : 0 < ‖u.val‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  rw [inv_mul_eq_div, le_div_iff₀ hb]
  nlinarith

end Riesz2.PhysicalMean

namespace Riesz2.PhysicalMean

/-- Middle-half labels are separated from the exterior of the active
window, including the wrap around the component cycle. The source labels
are one based, so the inequalities contain `i₀.val + 1`. -/
theorem exterior_distance_internal (n m : ℕ+) (hnm : 2 * (n : ℕ) ≤ (m : ℕ))
    (i₀ : Fin (n : ℕ))
    (hlo : (n : ℝ) / 4 ≤ (i₀.val : ℝ) + 1)
    (hhi : (i₀.val : ℝ) + 1 ≤ 3 * (n : ℝ) / 4)
    (j : Fin (m : ℕ)) (hj : (n : ℕ) ≤ j.val) :
    (n : ℝ) / 4 ≤
      (Riesz1.cyclicIndexDistance m j (i₀.castLE (by omega)) : ℝ) := by
  have hi : i₀.val ≤ j.val := by have := i₀.isLt; omega
  have hdist : Nat.dist j.val i₀.val = j.val - i₀.val := by
    rw [Nat.dist_comm]; exact Nat.dist_eq_sub_of_le hi
  have hd : j.val - i₀.val ≤ (m : ℕ) := by have := j.isLt; omega
  simp only [Riesz1.cyclicIndexDistance, Fin.val_castLE, hdist, Nat.cast_min,
    Nat.cast_sub hi, Nat.cast_sub hd, le_min_iff]
  have hjr : (n : ℝ) ≤ (j.val : ℝ) := by exact_mod_cast hj
  have hmr : (j.val : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast j.isLt
  constructor <;> linarith

/-- The full and exterior sums of the summable value profile. The tail
factor is uniform in both periods and has no logarithmic loss. -/
theorem profile_sums_internal (s : Riesz1.RieszExponent) :
    ∃ B D : ℝ, 0 < B ∧ 0 < D ∧
      ∀ (n m : ℕ+) (hnm : 2 * (n : ℕ) ≤ (m : ℕ))
        (i₀ : Fin (n : ℕ)),
        (n : ℝ) / 4 ≤ (i₀.val : ℝ) + 1 →
        (i₀.val : ℝ) + 1 ≤ 3 * (n : ℝ) / 4 →
        (∑ j : Fin (m : ℕ), weightRadius m j (i₀.castLE (by omega)) ^ (-(2-s.val))) ≤ B ∧
        (∑ j ∈ Finset.univ.filter (fun j : Fin (m : ℕ) => (n : ℕ) ≤ j.val),
          weightRadius m j (i₀.castLE (by omega)) ^ (-(2-s.val))) ≤
            D * (n : ℝ) ^ (-(1-s.val)) := by
  let t := 2-s.val
  let B := 2 * (∑' k : ℕ, (1 + (k : ℝ)) ^ (-t))
  let D := 2 * (1 + 1/(t-1)) * (4 : ℝ) ^ (t-1)
  have ht : 1 < t := by dsimp only [t]; linarith [s.property.2]
  have hS : 0 < ∑' k : ℕ, (1 + (k : ℝ)) ^ (-t) :=
    (summable_one_add_rpow_neg ht).tsum_pos
      (fun k => Real.rpow_nonneg (by positivity) _) 0 (by simp)
  refine ⟨B,D,by dsimp only [B]; positivity,by dsimp only [D]; positivity,?_⟩
  intro n m hnm i₀ hlo hhi
  let i : Fin (m : ℕ) := i₀.castLE (by omega)
  constructor
  · simpa only [B,t,weightRadius,cyclicIndexDistance_comm'] using
      sum_le_two_mul_tsum_cyclicIndexDistance m i (fun k => by positivity)
        (summable_one_add_rpow_neg ht)
  let R := max 1 ((n : ℝ)/4)
  have hR : 1 ≤ R := le_max_left _ _
  have hn0 : (0 : ℝ) < n := by positivity
  have hext : Finset.univ.filter (fun j : Fin (m : ℕ) => (n : ℕ) ≤ j.val) ⊆
      Finset.univ.filter (fun j => R ≤ weightRadius m j i) := by
    intro j hj
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,max_le (one_le_weightRadius m j i) ?_⟩
    have hd := exterior_distance_internal n m hnm i₀ hlo hhi j (Finset.mem_filter.mp hj).2
    exact hd.trans (by dsimp only [weightRadius,i]; linarith)
  have hp : R ^ (1-t) ≤ ((n : ℝ)/4) ^ (1-t) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (le_max_right _ _) (by linarith)
  have hscale : ((n : ℝ)/4) ^ (1-t) = (4 : ℝ) ^ (t-1) * (n : ℝ) ^ (-(1-s.val)) := by
    rw [Real.div_rpow hn0.le (by norm_num),div_eq_mul_inv,← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
    rw [show 1-t = -(1-s.val) by dsimp only [t]; ring,
      show -(-(1-s.val)) = t-1 by dsimp only [t]; ring, mul_comm]
  calc
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j => R ≤ weightRadius m j i),
        weightRadius m j i ^ (-t) :=
      Finset.sum_le_sum_of_subset_of_nonneg hext
        (fun j _ _ => Real.rpow_nonneg (by linarith [one_le_weightRadius m j i]) _)
    _ ≤ 2 * (1+1/(t-1)) * R ^ (1-t) := sum_weightRadius_tail_le m i ht hR
    _ ≤ 2 * (1+1/(t-1)) * (((n : ℝ)/4) ^ (1-t)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = D * (n : ℝ) ^ (-(1-s.val)) := by rw [hscale]; dsimp only [D]; ring

/-- The active sum is the total sum minus the exterior sum, with the
original active labels. This is the exact second identity of
the proof of Proposition 5.18, independent of the scalar measure. -/
theorem active_sum_internal {V : Type*} [AddCommGroup V]
    (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ)) (u : Fin (m : ℕ) → V) :
    (∑ i : Fin (n : ℕ), u (i.castLE hnm)) = (∑ j, u j) -
      ∑ j ∈ Finset.univ.filter (fun j : Fin (m : ℕ) => (n : ℕ) ≤ j.val), u j := by
  classical
  have ha : (∑ j ∈ Finset.univ.filter (fun j : Fin (m : ℕ) => j.val < (n : ℕ)), u j) =
      ∑ i : Fin (n : ℕ), u (i.castLE hnm) := by
    symm
    apply Finset.sum_bij (fun i _ => i.castLE hnm)
    · intro i _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.isLt⟩
    · intro i _ j _ hij
      exact Fin.ext (congrArg (fun k : Fin (m : ℕ) => k.val) hij)
    · intro j hj
      exact ⟨⟨j.val,(Finset.mem_filter.mp hj).2⟩,Finset.mem_univ _,Fin.ext rfl⟩
    · intro i _; rfl
  have hs := Finset.sum_filter_add_sum_filter_not
    (s := Finset.univ) (p := fun j : Fin (m : ℕ) => j.val < (n : ℕ)) u
  rw [ha] at hs
  simp only [not_lt] at hs
  exact eq_sub_iff_add_eq.mpr hs

end Riesz2.PhysicalMean

namespace Riesz2.PhysicalMean

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- Internal assembly of the scalar mean estimate in the proof of Proposition 5.18.
The profile and row bounds are inputs to this lemma. The quantitative periodized theorem below obtains them from the
decay and reference-error results. -/
theorem mean_from_profile_internal (s : Riesz1.RieszExponent)
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (n m : ℕ+) (hnm : 2 * (n : ℕ) ≤ (m : ℕ))
    (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν)
    (β ell c A B D Be : ℝ) (hβ : 0 < β) (hc : 0 < c)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (_hD : 0 ≤ D) (hBe : 0 ≤ Be)
    (hell : c * (m : ℝ) ^ (1-s.val) ≤ ell)
    (M : X → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hMb : ∃ b : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ b)
    (H : Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hrow : ∀ i, ∑ j, H i j = ell)
    (herr : ∀ᵐ x ∂ν, ∀ i, ∑ j, |M x i j - H i j| ≤ Be)
    (u : Fin (m : ℕ) → Q.1)
    (hu : WeightedWeakSolution Q (fun x => β • M x) ⊤
      (fun i => if i = i₀.castLE (by omega) then χ else 0) u)
    (hpoint : ∀ j, ‖(u j).val‖ ≤
      A * weightRadius m j (i₀.castLE (by omega)) ^ (-(2-s.val)) * ‖χ‖)
    (hsum : (∑ j, weightRadius m j (i₀.castLE (by omega)) ^ (-(2-s.val))) ≤ B)
    (htail : (∑ j ∈ Finset.univ.filter (fun j : Fin (m : ℕ) => (n : ℕ) ≤ j.val),
      weightRadius m j (i₀.castLE (by omega)) ^ (-(2-s.val))) ≤
        D * (n : ℝ) ^ (-(1-s.val))) :
    (∑ j, ‖(u j).val‖) ≤ A * B * ‖χ‖ ∧
    ∃ g : Lp ℝ 2 ν,
      (∀ᵐ x ∂ν, g x = β * ∑ i, ∑ j, (u i).val x * (M x i j - H i j)) ∧
      ‖g‖ ≤ β * Be * (A * B * ‖χ‖) ∧
      (∀ w : Q.1, Q.2 (∑ j, u j) w +
        (β*ell) * inner ℝ (∑ j, (u j).val) w.val = inner ℝ (χ-g) w.val) ∧
      ‖∑ j, (u j).val‖ ≤ (β*c)⁻¹ * (1+β*Be*A*B) *
        (n : ℝ) ^ (-(1-s.val)) * ‖χ‖ ∧
      ‖∑ i : Fin (n : ℕ), (u (i.castLE (by omega))).val‖ ≤
        ((β*c)⁻¹ * (1+β*Be*A*B) + A*D) *
          (n : ℝ) ^ (-(1-s.val)) * ‖χ‖ := by
  classical
  have hsumu : (∑ j, ‖(u j).val‖) ≤ A*B*‖χ‖ := by
    calc
      _ ≤ ∑ j, A * weightRadius m j (i₀.castLE (by omega)) ^ (-(2-s.val)) * ‖χ‖ :=
        Finset.sum_le_sum (fun j _ => hpoint j)
      _ = A * (∑ j, weightRadius m j (i₀.castLE (by omega)) ^ (-(2-s.val))) * ‖χ‖ := by
        simp only [Finset.mul_sum, Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hA) (norm_nonneg χ)
  have hβMm : ∀ i j, Measurable (fun x => (β • M x) i j) :=
    fun i j => (hMm i j).const_mul β
  have hβMb : ∃ b : ℝ, ∀ᵐ x ∂ν, ∀ i j, |(β • M x) i j| ≤ b := by
    obtain ⟨b,hb⟩ := hMb
    refine ⟨β*b,hb.mono (fun x hx i j => ?_)⟩
    simpa only [Matrix.smul_apply,smul_eq_mul,abs_mul,abs_of_pos hβ] using
      mul_le_mul_of_nonneg_left (hx i j) hβ.le
  have hβrow (i) : ∑ j, (β • H) i j = β*ell := by
    simp only [Matrix.smul_apply,smul_eq_mul,← Finset.mul_sum,hrow]
  have hβerr : ∀ᵐ x ∂ν, ∀ i,
      |∑ j, ((β • M x) i j - (β • H) i j)| ≤ β*Be := by
    filter_upwards [herr] with x hx i
    simp only [Matrix.smul_apply,smul_eq_mul,← mul_sub,← Finset.mul_sum,
      abs_mul,abs_of_pos hβ]
    exact mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (hx i)) hβ.le
  obtain ⟨g,hg,hgn,hgeq⟩ := sum_equation_internal Q (fun x => β • M x) hβMm hβMb
    (β • H) (β*ell) (β*Be) (mul_nonneg hβ.le hBe) hβrow hβerr
    (fun i => if i = i₀.castLE (by omega) then χ else 0) u hu
  have hg' : ∀ᵐ x ∂ν, g x = β * ∑ i, ∑ j, (u i).val x * (M x i j - H i j) := by
    filter_upwards [hg] with x hx
    rw [hx]
    simp only [Matrix.smul_apply,smul_eq_mul,← mul_sub,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hgn' := hgn.trans (mul_le_mul_of_nonneg_left hsumu (mul_nonneg hβ.le hBe))
  have heq : ∀ w : Q.1, Q.2 (∑ j, u j) w +
      (β*ell) * inner ℝ (∑ j, (u j).val) w.val = inner ℝ (χ-g) w.val := by
    simpa only [Finset.sum_ite_eq',Finset.mem_univ,ite_true] using hgeq
  have hell0 : 0 < ell :=
    (mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)).trans_le hell
  have hscalar := scalar_mean_norm_internal Q hQ (β*ell) (mul_pos hβ hell0) (χ-g) (∑ j,u j)
    (by simpa only [Submodule.coe_sum] using heq)
  have hinv : (β*ell)⁻¹ ≤ (β*c)⁻¹ * (m : ℝ) ^ (-(1-s.val)) := by
    have hh := inv_anti₀ (mul_pos hβ (mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)))
      (mul_le_mul_of_nonneg_left hell hβ.le)
    apply hh.trans_eq
    rw [← mul_assoc,mul_inv_rev,← Real.rpow_neg (by positivity : (0 : ℝ) ≤ m)]
    ring
  have hpow : (m : ℝ) ^ (-(1-s.val)) ≤ (n : ℝ) ^ (-(1-s.val)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity)
      (by exact_mod_cast (show (n : ℕ) ≤ (m : ℕ) by omega)) (by linarith [s.property.2])
  have hnorm : ‖χ-g‖ ≤ (1+β*Be*A*B)*‖χ‖ := by
    apply (norm_sub_le _ _).trans
    have hh := add_le_add_left hgn' ‖χ‖
    convert hh using 1 <;> ring
  have hT : ‖∑ j, (u j).val‖ ≤
      (β*c)⁻¹*(1+β*Be*A*B)*(n : ℝ)^(-(1-s.val))*‖χ‖ := by
    have hh := hscalar.trans (mul_le_mul hinv hnorm (norm_nonneg _) (by positivity))
    have hh' := mul_le_mul_of_nonneg_left hpow
      (by positivity : 0 ≤ (β*c)⁻¹ * (1+β*Be*A*B) * ‖χ‖)
    simpa only [Submodule.coe_sum,mul_assoc,mul_left_comm,mul_comm] using hh.trans
      (by simpa only [mul_assoc,mul_left_comm,mul_comm] using hh')
  have htailu : ‖∑ j ∈ Finset.univ.filter (fun j : Fin (m : ℕ) => (n : ℕ) ≤ j.val),
      (u j).val‖ ≤ A*D*(n : ℝ)^(-(1-s.val))*‖χ‖ := by
    calc
      _ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin (m : ℕ) => (n : ℕ) ≤ j.val), ‖(u j).val‖ :=
        norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin (m : ℕ) => (n : ℕ) ≤ j.val),
          A * weightRadius m j (i₀.castLE (by omega)) ^ (-(2-s.val)) * ‖χ‖ :=
        Finset.sum_le_sum (fun j _ => hpoint j)
      _ = A * (∑ j ∈ Finset.univ.filter (fun j : Fin (m : ℕ) => (n : ℕ) ≤ j.val),
          weightRadius m j (i₀.castLE (by omega)) ^ (-(2-s.val))) * ‖χ‖ := by
        simp only [Finset.mul_sum,Finset.sum_mul]
      _ ≤ A*(D*(n : ℝ)^(-(1-s.val)))*‖χ‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htail hA) (norm_nonneg χ)
      _ = _ := by ring
  refine ⟨hsumu,g,hg',hgn',heq,hT,?_⟩
  rw [active_sum_internal n m (by omega) (fun j => (u j).val)]
  exact (norm_sub_le _ _).trans ((add_le_add hT htailu).trans_eq (by ring))

end Riesz2.PhysicalMean

namespace Riesz2.PhysicalMean

/-- Loss bookkeeping for the proof of Proposition 5.18. The two structural exponents
add. The input prefactors and the temperature interval enter only the
final prefactor. -/
theorem mean_loss_internal (n : ℕ+) (ε kv ke Cv Ce B D c βlo βhi β : ℝ)
    (hε : 0 ≤ ε) (hkv : 0 ≤ kv) (hke : 0 ≤ ke)
    (hCv : 0 ≤ Cv) (hCe : 0 ≤ Ce) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hc : 0 < c) (hβlo : 0 < βlo) (hβl : βlo ≤ β) (hβh : β ≤ βhi) :
    let A := Cv*(n : ℝ)^(kv*ε)
    let Be := Ce*(n : ℝ)^(ke*ε)
    let P := (n : ℝ)^((kv+ke)*ε)
    A ≤ Cv*P ∧ A*B ≤ (Cv*B)*P ∧
      ((β*c)⁻¹*(1+β*Be*A*B)+A*D) ≤
        ((βlo*c)⁻¹*(1+βhi*Ce*Cv*B)+Cv*D)*P := by
  intro A Be P
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by positivity
  have hβ : 0 < β := hβlo.trans_le hβl
  have hβhi : 0 < βhi := hβ.trans_le hβh
  have hP : 1 ≤ P := Real.one_le_rpow hn1 (by positivity)
  have hPv : (n : ℝ)^(kv*ε) ≤ P :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith only [mul_nonneg hke hε])
  have hA : A ≤ Cv*P := mul_le_mul_of_nonneg_left hPv hCv
  have hAB := mul_le_mul_of_nonneg_right hA hB
  have hpowers : (n : ℝ)^(ke*ε)*(n : ℝ)^(kv*ε) = P := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  have hprod : β*Be*A*B ≤ (βhi*Ce*Cv*B)*P := by
    calc
      _ = (β*Ce*Cv*B)*((n : ℝ)^(ke*ε)*(n : ℝ)^(kv*ε)) := by dsimp only [A,Be]; ring
      _ = (β*Ce*Cv*B)*P := by rw [hpowers]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hβh hCe) hCv) hB) (by positivity)
  have hsource : 1+β*Be*A*B ≤ (1+βhi*Ce*Cv*B)*P := by nlinarith only [hP,hprod]
  have hinv : (β*c)⁻¹ ≤ (βlo*c)⁻¹ :=
    inv_anti₀ (mul_pos hβlo hc) (mul_le_mul_of_nonneg_right hβl hc.le)
  have hm := mul_le_mul hinv hsource (by positivity : 0 ≤ 1+β*Be*A*B) (by positivity)
  have hd := mul_le_mul_of_nonneg_right hA hD
  refine ⟨hA,by simpa only [mul_assoc,mul_left_comm,mul_comm] using hAB,?_⟩
  calc
    _ ≤ (βlo*c)⁻¹*((1+βhi*Ce*Cv*B)*P)+(Cv*P)*D := add_le_add hm hd
    _ = _ := by ring

/-- The periodized analytic part of the proof of Proposition 5.18, with
all estimates obtained from the structural assumptions. This is
an internal theorem: the final physical carrier/Schur specialization is
separate. The loss exponent precedes epsilon, the matrix prefactor and
the compact positive temperature interval. -/
theorem periodized_mean_internal (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ)
    (hκstar : 0 < κstar) (hγstar : 0 < γstar) (M₀ : ℕ+) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ∀ Cstar : ℝ, 1 ≤ Cstar →
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    ∀ (n m : ℕ+) (hn : 2 ≤ (n : ℕ)) (hm : 2 ≤ (m : ℕ)),
      ∀ (_hnm : 2*(n : ℕ) ≤ (m : ℕ)),
      (m : ℝ) ≤ 2*(n : ℝ)^(1/2+1/s.val) →
      let K := ⌊(n : ℝ)^ε⌋₊^(M₀ : ℕ)
      1 ≤ K → 4*K ≤ (m : ℕ) →
    ∀ (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d)))
      (ν : Measure (EuclideanSpace ℝ (Fin d))),
      IsOpen Ω → Convex ℝ Ω → Bornology.IsBounded Ω → Ω.Nonempty →
      IsProbabilityMeasure ν →
      (∃ V : EuclideanSpace ℝ (Fin d) → ℝ,
        IsEuclideanGibbsPotential volume ν Ω V 2) →
    ∀ Q : ScalarFormData ν, IsNeumannRealization Ω Q →
      IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
    ∀ M : EuclideanSpace ℝ (Fin d) → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
      PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M →
    ∀ (i₀ : Fin (n : ℕ)), (n : ℝ)/4 ≤ (i₀.val : ℝ)+1 →
      (i₀.val : ℝ)+1 ≤ 3*(n : ℝ)/4 → ∀ χ : Lp ℝ 2 ν,
      let i := i₀.castLE (by omega)
      let H := (2 : ℝ) • rieszMatrix s m hm
      let ell := 2 * ∑ k, sampledRieszKernel s m hm k
      (∃! u : Fin (m : ℕ) → Q.1, WeightedWeakSolution Q
        (fun x => β.val • M x) ⊤ (fun j => if j=i then χ else 0) u) ∧
      ∀ u : Fin (m : ℕ) → Q.1, WeightedWeakSolution Q
        (fun x => β.val • M x) ⊤ (fun j => if j=i then χ else 0) u →
        (∀ j, ‖(u j).val‖ ≤ C*(n : ℝ)^(κ*ε)*
          weightRadius m j i ^ (-(2-s.val))*‖χ‖) ∧
        (∑ j, ‖(u j).val‖) ≤ C*(n : ℝ)^(κ*ε)*‖χ‖ ∧
        (∑ j : Fin (n : ℕ), u (j.castLE (by omega))) = (∑ j,u j) -
          ∑ j ∈ Finset.univ.filter (fun j : Fin (m : ℕ) => (n : ℕ) ≤ j.val), u j ∧
        ∃ g : Lp ℝ 2 ν,
          (∀ᵐ x ∂ν, g x = β.val * ∑ a, ∑ b, (u a).val x * (M x a b - H a b)) ∧
          (∀ w : Q.1, Q.2 (∑ j,u j) w + (β.val*ell)*inner ℝ (∑ j,(u j).val) w.val =
            inner ℝ (χ-g) w.val) ∧
          ‖∑ j : Fin (n : ℕ), (u (j.castLE (by omega))).val‖ ≤
            C*(n : ℝ)^(κ*ε)*(n : ℝ)^(-(1-s.val))*‖χ‖ := by
  obtain ⟨kv,hkv,hdecay⟩ := OptimalLocalizationPart5.optimal_pointwise_decay hzeta
    s κstar γstar M₀ hκstar hγstar
  obtain ⟨ke,hke,herror⟩ := global_error_differences s κstar γstar hκstar.le hγstar.le M₀
  obtain ⟨B,D,hB,hD,hsums⟩ := profile_sums_internal s
  obtain ⟨c,_,hc,_,hmass⟩ := global_reference_mass_bounds s
  refine ⟨kv+ke,add_pos hkv hke,?_⟩
  intro ε hε Cstar hCstar βlo βhi hβlo hβhi
  obtain ⟨Cv,hCv,hdecay⟩ := hdecay ε hε Cstar hCstar βlo βhi hβlo hβhi
  obtain ⟨Ce,hCe,herror⟩ := herror ε hε Cstar hCstar
  let Cm := (βlo*c)⁻¹*(1+βhi*Ce*Cv*B)+Cv*D
  let C := 1+Cv+Cv*B+Cm
  have hβhi0 : 0 < βhi := hβlo.trans_le hβhi
  have hCe0 : 0 < Ce := zero_lt_one.trans_le hCe
  have hCm : 0 < Cm := by dsimp only [Cm]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  have hCvC : Cv ≤ C := by dsimp only [C]; linarith [mul_pos hCv hB]
  have hCBC : Cv*B ≤ C := by dsimp only [C]; linarith
  have hCmC : Cm ≤ C := by dsimp only [C]; linarith [mul_pos hCv hB]
  refine ⟨C,hC,?_⟩
  intro β hβ n m hn hm hnm hmn K hK hKm d Ω ν hΩ hcΩ hbΩ hnΩ hν hV Q hreal hQ hcons M hM i₀ hlo hhi χ i H ell
  have hd := hdecay β hβ n m hn hm (by omega) hmn hK hKm d Ω ν
    hΩ hcΩ hbΩ hnΩ hν hV Q hreal hQ hcons M hM i χ false
  simp only [Bool.false_eq_true,ite_false] at hd
  refine ⟨hd.1,?_⟩
  intro u hu
  have hp (j) : ‖(u j).val‖ ≤ Cv*(n : ℝ)^(kv*ε)*weightRadius m j i ^ (-(2-s.val))*‖χ‖ :=
    (hd.2 u hu j).1
  obtain ⟨_,_,_,_,_,_,he⟩ := herror n m hm hn (by omega) hmn hK hKm ν M hM
  have herr : ∀ᵐ x ∂ν, ∀ a, ∑ b, |M x a b-H a b| ≤ Ce*(n : ℝ)^(ke*ε) :=
    he.mono (fun _ hx => hx.2.2.2.1)
  have hell : c*(m : ℝ)^(1-s.val) ≤ ell := by
    simpa only [ell,Matrix.smul_apply,smul_eq_mul,← Finset.mul_sum,rieszMatrix_row_sum]
      using (hmass m hm i).1
  have hrow (a) : ∑ b, H a b = ell := by
    simp only [H,ell,Matrix.smul_apply,smul_eq_mul,← Finset.mul_sum,rieszMatrix_row_sum]
  obtain ⟨hsum,htail⟩ := hsums n m hnm i₀ hlo hhi
  obtain ⟨hsumu,g,hg,_,hgeq,_,hmean⟩ := mean_from_profile_internal s Q hQ n m hnm i₀ χ
    β.val ell c (Cv*(n : ℝ)^(kv*ε)) B D (Ce*(n : ℝ)^(ke*ε)) β.property hc
    (by positivity) hB.le hD.le (by positivity) hell M hM.1
    (SchurRestriction.periodized_bounded hM) H hrow herr u hu hp hsum htail
  obtain ⟨hA,hAB,hCmcoef⟩ := mean_loss_internal n ε kv ke Cv Ce B D c βlo βhi β.val
    hε.le hkv.le hke.le hCv.le hCe0.le hB.le hD.le hc hβlo hβ.1 hβ.2
  have hCvP := mul_le_mul_of_nonneg_right hCvC
    (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n) ((kv+ke)*ε))
  have hBCP := mul_le_mul_of_nonneg_right hCBC
    (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n) ((kv+ke)*ε))
  have hCmP := mul_le_mul_of_nonneg_right hCmC
    (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n) ((kv+ke)*ε))
  refine ⟨fun j => (hp j).trans ?_,hsumu.trans ?_,
    active_sum_internal n m (by omega) u,g,hg,hgeq,hmean.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hA.trans hCvP)
      (by dsimp only [weightRadius]; positivity)) (norm_nonneg χ)
  · exact mul_le_mul_of_nonneg_right (hAB.trans hBCP) (norm_nonneg χ)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hCmcoef.trans hCmP)
      (by positivity)) (norm_nonneg χ)

end Riesz2.PhysicalMean

namespace Riesz2.PhysicalMean

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- The point source on the active block extends to the same point source
on the entire component cycle. This connects the literal Schur source to
the unrestricted localization theorem. -/
theorem extend_point_source_internal (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
    (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν) :
    (SchurRestriction.extendSource n m hnm
      (WithLp.toLp 2 (fun i => if i=i₀ then χ else 0))).ofLp =
      (fun j => if j=i₀.castLE hnm then χ else 0) := by
  classical
  funext j
  rw [show (SchurRestriction.extendSource n m hnm
      (WithLp.toLp 2 (fun i => if i=i₀ then χ else 0))).ofLp j =
      (SchurRestriction.extendSource n m hnm
        (WithLp.toLp 2 (fun i => if i=i₀ then χ else 0))) j from rfl,
    LocalizedFieldPart4.extendSource_apply_internal]
  by_cases hj : j.val < (n : ℕ)
  · rw [dite_eq_left hj]
    by_cases he : (⟨j.val,hj⟩ : Fin (n : ℕ)) = i₀
    · have he' : j = i₀.castLE hnm :=
        Fin.ext (congrArg (fun k : Fin (n : ℕ) => k.val) he)
      simp only [ite_eq_left he,ite_eq_left he']
    · have he' : j ≠ i₀.castLE hnm := fun h =>
        he (Fin.ext (congrArg (fun k : Fin (m : ℕ) => k.val) h))
      simp only [ite_eq_right he,ite_eq_right he']
  · have he : j ≠ i₀.castLE hnm := by
      intro h
      subst j
      exact hj i₀.isLt
    rw [dite_eq_right hj,ite_eq_right he]

/-- See the proof of Proposition 5.18 in the paper, exact restriction step, reusing
Lemma 5.4. Every full weak solution and every active Schur solution
with the same point source have exactly the same active components. -/
theorem schur_components_internal (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q)
    (s : Riesz1.RieszExponent) (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
    (hm : 2 ≤ (m : ℕ)) (K : ℕ) (C κ γ ε β : ℝ) (hC : 1 ≤ C) (hβ : 0 < β)
    (M : X → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M)
    (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν)
    (u : Fin (m : ℕ) → Q.1) (v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ)
    (hu : WeightedWeakSolution Q (fun x => β • M x) ⊤
      (fun j => if j=i₀.castLE hnm then χ else 0) u)
    (hv : ∀ w, SchurRestriction.schurForm Q hQ n m hnm s hm K C κ γ ε β hC hβ M hM v w =
      inner ℝ (WithLp.toLp 2 (fun i => if i=i₀ then χ else 0))
        (OperatorSchur.vectorValues Q hQ w)) :
    ∀ i : Fin (n : ℕ), u (i.castLE hnm) = MatrixEnergy.vectorEquiv Q hQ v i := by
  have hu' : WeightedWeakSolution Q (fun x => β • M x) ⊤
      (SchurRestriction.extendSource n m hnm
        (WithLp.toLp 2 (fun i => if i=i₀ then χ else 0))).ofLp u := by
    rwa [extend_point_source_internal n m hnm i₀ χ]
  have he := (SchurRestriction.schur_restriction_weak Q hQ n m hnm s hm K C κ γ ε β hC hβ M hM
    (WithLp.toLp 2 (fun i => if i=i₀ then χ else 0))).2.2 u v hu' hv
  have ha := congrArg Prod.fst he
  intro i
  have hr := SchurRestriction.assemble_restrict_apply Q hQ n m hnm
    ((MatrixEnergy.vectorEquiv Q hQ).symm u) i
  rw [ha] at hr
  have hr' := congrArg (ScalarFormHilbert.equiv Q hQ) hr.symm
  change (MatrixEnergy.vectorEquiv Q hQ ((MatrixEnergy.vectorEquiv Q hQ).symm u))
    (i.castLE hnm) = MatrixEnergy.vectorEquiv Q hQ v i at hr'
  simpa only [LinearEquiv.apply_symm_apply] using hr'

end Riesz2.PhysicalMean
