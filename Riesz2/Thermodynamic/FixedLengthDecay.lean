/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.InteractionDifferential
public import Riesz2.DecayLong.PhysicalPerturbation
public import Riesz2.DecayLong.LocalizedFieldPart4
public import Riesz2.ToMathlib.ConstrainedNormalMultiplier
public import Riesz2.ToMathlib.CoerciveSolutionMaps
public import Riesz2.DecayShort.OptimalDecay
public import Riesz2.ToMathlib.SummedWeakEquation

/-!
# Fixed-length tangent comparison

Steps of Lemma 6.4, including the small-size case. Boundary weights and scalar and
matrix form domains use the definitions in the code.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace Riesz2.FixedLengthDecay

/-- See Lemma 6.4 of the paper: the literal boundary weights are at most one,
including both endpoints and the smallest active block. -/
theorem boundaryWeight_le_one (s : ℝ) (hs : 0 < s) (n : ℕ+)
    (j : Fin (n : ℕ)) : InteractionDifferential.boundaryWeight s n j ≤ 1 := by
  have hd : (1 : ℝ) ≤ (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) := by
    have := j.isLt
    exact_mod_cast (show 1 ≤ min (j.val + 1) ((n : ℕ) - j.val) by omega)
  apply Real.rpow_le_one_of_one_le_of_nonpos hd
  have : min s 1 ≤ s := min_le_left _ _
  rcases le_total s 1 with h | h
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right h]
    linarith

/-- See Lemma 6.4 of the paper: the long-range squared boundary weights
have exactly the power `n^(1-s)`. -/
theorem long_boundary_square_sum (s : Riesz1.RieszExponent) (n : ℕ+) :
    (∑ j, InteractionDifferential.boundaryWeight s.val n j ^ 2) ≤
      (2 / (1 - s.val)) * (n : ℝ) ^ (1 - s.val) := by
  have he (j : Fin (n : ℕ)) :
      InteractionDifferential.boundaryWeight s.val n j ^ 2 =
        (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) ^ (-s.val) := by
    rw [InteractionDifferential.boundaryWeight_long s.property.2,
      ← Real.rpow_mul_natCast (InteractionDifferential.boundary_distance_pos n j).le]
    congr 1
    ring
  simp_rw [he]
  exact LocalizedBoundary.boundary_weight_sum_internal n s.val s.property.1 s.property.2

/-- See Lemma 6.4 of the paper: the short-range squared boundary weights
are summable uniformly in the active size. The sum starts at one. -/
theorem short_boundary_square_sum (s : ℝ) (hs : 1 < s) (n : ℕ+) :
    (∑ j, InteractionDifferential.boundaryWeight s n j ^ 2) ≤
      2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(2 * s - 1)) := by
  let p := 2 * s - 1
  have hp : 1 < p := by dsimp [p]; linarith
  have he (j : Fin (n : ℕ)) :
      InteractionDifferential.boundaryWeight s n j ^ 2 =
        (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) ^ (-p) := by
    rw [InteractionDifferential.boundaryWeight_short hs,
      ← Real.rpow_mul_natCast (InteractionDifferential.boundary_distance_pos n j).le]
    congr 1
    dsimp [p]
    ring
  simp_rw [he]
  have hb := LocalizedFieldPart4.endpoint_profile_sum_internal n
    (fun k => (k : ℝ) ^ (-p)) (fun k => Real.rpow_nonneg (Nat.cast_nonneg k) _)
  have hsum : (∑ k ∈ Finset.Icc 1 (n : ℕ), (k : ℝ) ^ (-p)) ≤
      ∑' k : ℕ, (1 + (k : ℝ)) ^ (-p) := by
    have heq : (∑ k ∈ Finset.Icc 1 (n : ℕ), (k : ℝ) ^ (-p)) =
        ∑ k ∈ Finset.range (n : ℕ), (1 + (k : ℝ)) ^ (-p) := by
      rw [show Finset.Icc 1 (n : ℕ) = Finset.Ico 1 ((n : ℕ) + 1) by
        ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
        Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
      simp only [Nat.cast_add, Nat.cast_one]
    rw [heq]
    exact (summable_one_add_rpow_neg hp).sum_le_tsum _
      (fun k _ => Real.rpow_nonneg (by positivity) _)
  exact hb.trans (mul_le_mul_of_nonneg_left hsum (by norm_num))

section FiniteNorms

variable {ι H : Type*} [Fintype ι] [NormedAddCommGroup H]

/-- See Lemma 6.4 of the paper: weighted component sums are bounded by the
Euclidean norm of the component norms, with the exact weight factor. -/
theorem weighted_sum_norm_le (w : ι → ℝ) (u : ι → H) :
    (∑ i, w i * ‖u i‖) ≤
      Real.sqrt (∑ i, w i ^ 2) * ‖WithLp.toLp 2 u‖ := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ w (fun i => ‖u i‖)
  have hr := Real.sqrt_le_sqrt hh
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_mul
    (Finset.sum_nonneg (fun i _ => sq_nonneg (w i)))] at hr
  rw [PiLp.norm_eq_of_L2]
  exact (le_abs_self _).trans hr

/-- See Lemma 6.4 of the paper: the unweighted error costs precisely `√n`. -/
theorem sum_norm_le (u : ι → H) :
    (∑ i, ‖u i‖) ≤ Real.sqrt (Fintype.card ι : ℝ) * ‖WithLp.toLp 2 u‖ := by
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] using weighted_sum_norm_le (fun _ => 1) u

/-- See Lemma 6.4 of the paper: transfer an auxiliary weighted sum through
a vector L² comparison. This uses the actual vector difference. -/
theorem weighted_sum_norm_transfer_internal (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (ψ v : ι → H) (A D : ℝ) (hv : (∑ i, w i * ‖v i‖) ≤ A)
    (he : ‖WithLp.toLp 2 (fun i => ψ i - v i)‖ ≤ D) :
    (∑ i, w i * ‖ψ i‖) ≤ A + Real.sqrt (∑ i, w i ^ 2) * D := by
  calc
    _ ≤ ∑ i, w i * (‖v i‖ + ‖ψ i - v i‖) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hw i)
      have hh := norm_add_le (v i) (ψ i - v i)
      simpa only [add_sub_cancel] using hh
    _ = (∑ i, w i * ‖v i‖) + ∑ i, w i * ‖ψ i - v i‖ := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ ≤ A + Real.sqrt (∑ i, w i ^ 2) * D :=
      add_le_add hv ((weighted_sum_norm_le w _).trans
        (mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg _)))

end FiniteNorms

section Comparison

variable {V H : Type*} [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup H] [Module ℝ H]

/-- The tangent subtraction identity of Lemma 6.4.
Both equations use one form carrier, and the correction has the same
normal component as the auxiliary solution. -/
theorem tangent_comparison_identity_internal
    (E A : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (f : V →ₗ[ℝ] ℝ)
    (S : Submodule ℝ V) (ψ v r : V)
    (hz : v - r ∈ S) (hψ : ψ ∈ S)
    (hphysical : ∀ w ∈ S, E ψ w = f w)
    (haux : ∀ w ∈ S, A v w = f w) :
    let u := v - r - ψ
    u ∈ S ∧ E u u = (E v u - A v u) - E r u := by
  intro u
  have hu : u ∈ S := S.sub_mem hz hψ
  refine ⟨hu, ?_⟩
  have he := hphysical u hu
  have ha := haux u hu
  dsimp only [u] at he ha ⊢
  simp only [map_sub, LinearMap.sub_apply] at he ha ⊢
  linarith only [he, ha]

/-- Energy comparison in Lemma 6.4. Positivity applied to
`u+r` proves the required Young bound directly, including degenerate
correction energy. -/
theorem tangent_comparison_bound_internal
    (E : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsym : ∀ x y, E x y = E y x) (hnonneg : ∀ x, 0 ≤ E x x)
    (J : V →ₗ[ℝ] H) (u r : V) (a L τ R : ℝ)
    (ha : 0 < a) (hL : 0 ≤ L) (hτ : 0 ≤ τ) (hR : 0 ≤ R)
    (hcoerc : a * ‖J u‖ ^ 2 ≤ E u u)
    (hres : E u u + E r u ≤ L * ‖J u‖ + τ)
    (hr : E r r ≤ R) :
    ‖J u‖ ≤ 2 * L / a + Real.sqrt ((2 * τ + R) / a) := by
  have hpos := hnonneg (u + r)
  simp only [map_add, LinearMap.add_apply] at hpos
  rw [hsym u r] at hpos
  have he : a * ‖J u‖ ^ 2 ≤ 2 * L * ‖J u‖ + 2 * τ + R := by
    linarith only [hcoerc, hres, hpos, hr]
  let b := Real.sqrt ((2 * τ + R) / a)
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hb2 : a * b ^ 2 = 2 * τ + R := by
    dsimp only [b]
    rw [Real.sq_sqrt (by positivity), mul_div_cancel₀ _ ha.ne']
  have hl : 0 ≤ 2 * L / a := by positivity
  have hdiv : a * (2 * L / a) = 2 * L := mul_div_cancel₀ _ ha.ne'
  have hbase : ‖J u‖ ^ 2 ≤ (2 * L / a) * ‖J u‖ + b ^ 2 := by
    apply (mul_le_mul_iff_right₀ ha).mp
    rw [mul_add, ← mul_assoc, hdiv, hb2]
    simpa only [add_assoc] using he
  by_contra! h
  have hd : 0 < ‖J u‖ - (2 * L / a + b) := by linarith
  have hprod : 0 < (‖J u‖ - (2 * L / a + b)) * (‖J u‖ + b) :=
    mul_pos hd (by have := norm_nonneg (J u); linarith only [hd, hl, hb])
  nlinarith only [hbase, hprod, mul_nonneg hl hb]

end Comparison

section SmallSizes

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- See Lemma 6.4 of the paper: the Euclidean norm of a one-coordinate L²
source is its scalar L² norm, without any differentiability assumption. -/
theorem point_source_norm (n : ℕ+) (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν) :
    ‖WithLp.toLp 2 (fun i : Fin (n : ℕ) => if i = i₀ then χ else 0)‖ = ‖χ‖ := by
  rw [PiLp.norm_eq_of_L2]
  simp only [apply_ite norm, norm_zero, ite_pow, zero_pow (by omega : 2 ≠ 0),
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Real.sqrt_sq (norm_nonneg _)]

/-- Direct tangent coercivity in the small-size branch of
Lemma 6.4. This is the weak equation on its
natural energy domain. Only a lower physical curvature bound is used. -/
theorem tangent_coercivity_sums_internal (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (n : ℕ+)
    (H : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (hHm : ∀ i j, Measurable (fun x => H x i j))
    (hH : ∀ᵐ x ∂ν, (H x).PosSemidef)
    (a : ℝ) (ha : 0 < a)
    (hlower : ∀ᵐ x ∂ν, ∀ z ∈ zeroSumComponents (Fin (n : ℕ)),
      a * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * H x i j * z j)
    (s : ℝ) (hs : 0 < s) (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν)
    (ψ : Fin (n : ℕ) → Q.1)
    (hψ : WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ)))
      (fun i => if i = i₀ then χ else 0) ψ) :
    ‖WithLp.toLp 2 (fun i => (ψ i).val)‖ ≤ a⁻¹ * ‖χ‖ ∧
    (∑ j, InteractionDifferential.boundaryWeight s n j * ‖(ψ j).val‖) ≤
      Real.sqrt (n : ℝ) * (a⁻¹ * ‖χ‖) ∧
    (∑ j, ‖(ψ j).val‖) ≤ Real.sqrt (n : ℝ) * (a⁻¹ * ‖χ‖) := by
  have he := MatrixEnergy.weightedWeakSolution_unique Q hQ H
    (zeroSumComponents (Fin (n : ℕ))) hH a ha hlower hHm _ ψ hψ
  have hn := MatrixEnergy.solution_value_norm_le Q hQ H
    (zeroSumComponents (Fin (n : ℕ))) hH a ha hlower
    (WithLp.toLp 2 (fun i => if i = i₀ then χ else 0))
  have hv : MatrixEnergy.values Q hQ H (zeroSumComponents (Fin (n : ℕ))) hH
      (MatrixEnergy.solution Q hQ H (zeroSumComponents (Fin (n : ℕ))) hH
        a ha hlower (WithLp.toLp 2 (fun i => if i = i₀ then χ else 0))) =
      WithLp.toLp 2 (fun i => (ψ i).val) := by
    apply PiLp.ext
    intro i
    rw [MatrixEnergy.values_apply, he]
  rw [hv, point_source_norm] at hn
  have hsum : (∑ j, ‖(ψ j).val‖) ≤ Real.sqrt (n : ℝ) * (a⁻¹ * ‖χ‖) := by
    have hh := sum_norm_le (fun i => (ψ i).val)
    simp only [Fintype.card_fin] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _))
  refine ⟨hn, ?_, hsum⟩
  apply le_trans (Finset.sum_le_sum (fun j _ => ?_)) hsum
  exact mul_le_of_le_one_left (norm_nonneg _) (boundaryWeight_le_one s hs n j)

/-- Finite-size absorption in Lemma 6.4.
The enlarged prefactor depends on the threshold alone. The loss and tail
exponents stay unchanged. Both coordinate sums are covered at once. -/
theorem small_size_absorption_internal (n n₀ κ ε q C F B c δ x : ℝ)
    (hn : 1 ≤ n) (hn₀ : n ≤ n₀) (hq : 0 ≤ q) (hC : 0 ≤ C)
    (hF : 0 ≤ F) (hB : 0 ≤ B)
    (hx : x ≤ Real.sqrt n * (C * n ^ (κ * ε) * F)) :
    x ≤ (C * n₀ ^ (q + 1 / 2)) * n ^ (κ * ε - q) *
      (F + Real.exp (-c * n ^ δ) * B) := by
  have hn0 : 0 < n := by linarith
  have hn₀0 : 0 < n₀ := hn0.trans_le hn₀
  have hpow : n ^ (q + 1 / 2) ≤ n₀ ^ (q + 1 / 2) :=
    Real.rpow_le_rpow hn0.le hn₀ (by linarith)
  have he : Real.sqrt n * (C * n ^ (κ * ε) * F) =
      (C * n ^ (q + 1 / 2)) * n ^ (κ * ε - q) * F := by
    calc
      _ = C * (n ^ ((1 : ℝ) / 2) * n ^ (κ * ε)) * F := by
        rw [Real.sqrt_eq_rpow]; ring
      _ = C * (n ^ (q + 1 / 2) * n ^ (κ * ε - q)) * F := by
        rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
        rw [show q + 1 / 2 + (κ * ε - q) = (1 : ℝ) / 2 + κ * ε by ring]
      _ = _ := by ring
  apply hx.trans
  rw [he]
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC) (by positivity))
    (le_add_of_nonneg_right (mul_nonneg (Real.exp_pos _).le hB)) hF (by positivity)

end SmallSizes

section AuxiliaryWeights

/-- See Lemma 6.4 of the paper: a summable profile centred in the middle
half has a boundary-weighted sum of order `n⁻q`, for `0<q<1`.
Both the value profile and its total sum are retained as distinct inputs. -/
theorem auxiliary_weighted_sum_internal (n : ℕ+) (i₀ : Fin (n : ℕ))
    (hlo : (n : ℝ) / 4 ≤ (i₀.val : ℝ) + 1)
    (hhi : (i₀.val : ℝ) + 1 ≤ 3 * (n : ℝ) / 4)
    (p q D F : ℝ) (hp : 1 ≤ p) (hq : 0 < q) (hq1 : q < 1)
    (hD : 0 ≤ D) (hF : 0 ≤ F)
    (a : Fin (n : ℕ) → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hvalue : ∀ j, a j ≤ D * F * (1 + (Nat.dist j.val i₀.val : ℝ)) ^ (-p))
    (hsum : (∑ j, a j) ≤ D * F) :
    (∑ j, (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) ^ (-q) * a j) ≤
      (8 ^ p * (2 / (1 - q)) + 8 ^ q) * D * F * (n : ℝ) ^ (-q) := by
  let d := fun j : Fin (n : ℕ) => ((min (j.val + 1) ((n : ℕ) - j.val) : ℕ) : ℝ)
  let B := Finset.univ.filter (fun j : Fin (n : ℕ) => d j ≤ (n : ℝ) / 8)
  have hn0 : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hd (j) : 0 < d j := InteractionDifferential.boundary_distance_pos n j
  have hscale (t : ℝ) : ((n : ℝ) / 8) ^ (-t) = 8 ^ t * (n : ℝ) ^ (-t) := by
    rw [Real.div_rpow hn0.le (by norm_num : (0 : ℝ) ≤ 8),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8), div_inv_eq_mul, mul_comm]
  have hbvalue (j) (hj : j ∈ B) :
      a j ≤ D * F * (8 ^ p * (n : ℝ) ^ (-p)) := by
    have hs := PhysicalPerturbation.boundary_separation_internal n i₀ j hlo hhi
      (Finset.mem_filter.mp hj).2
    apply (hvalue j).trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hD hF)
    rw [← hscale]
    exact Real.rpow_le_rpow_of_nonpos (by positivity)
      (by linarith : (n : ℝ) / 8 ≤ 1 + (Nat.dist j.val i₀.val : ℝ)) (by linarith)
  have hbweights : (∑ j ∈ B, (d j) ^ (-q)) ≤
      (2 / (1 - q)) * (n : ℝ) ^ (1 - q) := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun j _ _ => Real.rpow_nonneg (hd j).le _)).trans
    exact LocalizedBoundary.boundary_weight_sum_internal n q hq hq1
  have hb : (∑ j ∈ B, (d j) ^ (-q) * a j) ≤
      (8 ^ p * (2 / (1 - q))) * D * F * (n : ℝ) ^ (-q) := by
    calc
      _ ≤ ∑ j ∈ B, (d j) ^ (-q) * (D * F * (8 ^ p * (n : ℝ) ^ (-p))) :=
        Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hbvalue j hj) (by positivity))
      _ = (D * F * (8 ^ p * (n : ℝ) ^ (-p))) * ∑ j ∈ B, (d j) ^ (-q) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ (D * F * (8 ^ p * (n : ℝ) ^ (-p))) *
          ((2 / (1 - q)) * (n : ℝ) ^ (1 - q)) :=
        mul_le_mul_of_nonneg_left hbweights (by positivity)
      _ = (8 ^ p * (2 / (1 - q))) * D * F * (n : ℝ) ^ (1 - q - p) := by
        have he : (n : ℝ) ^ (-p) * (n : ℝ) ^ (1 - q) = (n : ℝ) ^ (1 - q - p) := by
          rw [← Real.rpow_add hn0]; congr 1; ring
        calc
          _ = (8 ^ p * (2 / (1 - q))) * D * F *
              ((n : ℝ) ^ (-p) * (n : ℝ) ^ (1 - q)) := by ring
          _ = _ := by rw [he]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)) (by positivity)
  have hu : (∑ j ∈ Bᶜ, (d j) ^ (-q) * a j) ≤
      8 ^ q * (n : ℝ) ^ (-q) * (D * F) := by
    calc
      _ ≤ ∑ j ∈ Bᶜ, (8 ^ q * (n : ℝ) ^ (-q)) * a j := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' : (n : ℝ) / 8 < d j := by
          simpa only [B, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ,
            true_and, not_le] using hj
        apply mul_le_mul_of_nonneg_right _ (ha j)
        rw [← hscale]
        exact Real.rpow_le_rpow_of_nonpos (by positivity) hj'.le (by linarith)
      _ = (8 ^ q * (n : ℝ) ^ (-q)) * ∑ j ∈ Bᶜ, a j := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((Finset.sum_le_univ_sum_of_nonneg ha).trans hsum) (by positivity)
  have hsplit := Finset.sum_add_sum_compl B (fun j => (d j) ^ (-q) * a j)
  change (∑ j, (d j) ^ (-q) * a j) ≤ _
  rw [← hsplit]
  exact (add_le_add hb hu).trans_eq (by ring)

/-- Long-range auxiliary weighted estimate in Lemma 6.4,
from the literal value and unweighted conclusions of the proof of Lemma 6.4. -/
theorem long_auxiliary_weighted_sum_internal (s : Riesz1.RieszExponent)
    (n : ℕ+) (i₀ : Fin (n : ℕ))
    (hi₀ : |(i₀.val : ℝ) + 1 - (n : ℝ) / 2| ≤ (n : ℝ) / 4)
    (D F : ℝ) (hD : 0 ≤ D) (hF : 0 ≤ F)
    (a : Fin (n : ℕ) → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hvalue : ∀ j, a j ≤ D * (1 + (Nat.dist j.val i₀.val : ℝ)) ^ (s.val - 2) * F)
    (hsum : (∑ j, a j) ≤ D * F) :
    (∑ j, InteractionDifferential.boundaryWeight s.val n j * a j) ≤
      (8 ^ (2 - s.val) * (2 / (1 - s.val / 2)) + 8 ^ (s.val / 2)) *
        D * F * (n : ℝ) ^ (-s.val / 2) := by
  have hcent := abs_le.mp hi₀
  simp_rw [InteractionDifferential.boundaryWeight_long s.property.2]
  have hh := auxiliary_weighted_sum_internal n i₀ (by linarith) (by linarith)
    (2 - s.val) (s.val / 2) D F (by linarith [s.property.2])
    (by linarith [s.property.1]) (by linarith [s.property.2]) hD hF a ha
    (fun j => by simpa only [show -(2 - s.val) = s.val - 2 by ring,
      mul_assoc, mul_left_comm, mul_comm] using hvalue j) hsum
  simpa only [neg_div] using hh

/-- Short-range auxiliary weighted estimate sufficient for Lemma 6.4. Domination by the half-power boundary weight avoids a
logarithmic endpoint split and gives the required `n⁻¹ᐟ²` directly. -/
theorem short_auxiliary_weighted_sum_internal (s : ℝ) (hs : 1 < s)
    (n : ℕ+) (i₀ : Fin (n : ℕ))
    (hi₀ : |(i₀.val : ℝ) + 1 - (n : ℝ) / 2| ≤ (n : ℝ) / 4)
    (D F : ℝ) (hD : 0 ≤ D) (hF : 0 ≤ F)
    (a : Fin (n : ℕ) → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hvalue : ∀ j, a j ≤ D * (1 + (Nat.dist j.val i₀.val : ℝ)) ^ (-s) * F)
    (hsum : (∑ j, a j) ≤ D * F) :
    (∑ j, InteractionDifferential.boundaryWeight s n j * a j) ≤
      (4 * 8 ^ s + Real.sqrt 8) * D * F * (n : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hcent := abs_le.mp hi₀
  have hh := auxiliary_weighted_sum_internal n i₀ (by linarith) (by linarith)
    s (1 / 2) D F hs.le (by norm_num) (by norm_num) hD hF a ha
    (fun j => by simpa only [mul_assoc, mul_left_comm, mul_comm] using hvalue j) hsum
  have hdom : (∑ j, InteractionDifferential.boundaryWeight s n j * a j) ≤
      ∑ j, (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) ^ (-(1 / 2 : ℝ)) * a j := by
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_right _ (ha j)
    rw [InteractionDifferential.boundaryWeight_short hs]
    have hd : (1 : ℝ) ≤ (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) := by
      have := j.isLt
      exact_mod_cast (show 1 ≤ min (j.val + 1) ((n : ℕ) - j.val) by omega)
    exact Real.rpow_le_rpow_of_exponent_le hd (by linarith)
  apply hdom.trans
  have hc : (2 : ℝ) / (1 - 1 / 2) = 4 := by norm_num
  rw [hc, ← Real.sqrt_eq_rpow] at hh
  simpa only [neg_div, mul_comm] using hh

end AuxiliaryWeights

section NaturalComparison

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- Integrable physical coefficients pair integrably with bounded L²
fields, as used in Lemma 6.4 to put the auxiliary field and
its mean correction in the physical energy domain. -/
theorem bounded_matrix_pair_integrable {ι : Type*} [Fintype ι]
    (M : X → Matrix ι ι ℝ) (hM : ∀ i j, Integrable (fun x => M x i j) ν)
    (v w : ι → Lp ℝ 2 ν) (B C : ℝ)
    (hv : ∀ i, ∀ᵐ x ∂ν, |v i x| ≤ B)
    (hw : ∀ i, ∀ᵐ x ∂ν, |w i x| ≤ C) :
    Integrable (matrixFieldPair M v w) ν := by
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact ((hM i j).bdd_mul (Lp.aestronglyMeasurable (v i))
    (by simpa only [Real.norm_eq_abs] using hv i)).mul_bdd
      (Lp.aestronglyMeasurable (w j)) (by simpa only [Real.norm_eq_abs] using hw j)

/-- See Lemma 6.4 of the paper: bounded auxiliary scalar-form tuples have
finite physical matrix energy when its entries are integrable. The
physical matrix may have unbounded entries. -/
theorem bounded_tuple_physical_domain_internal (Q : ScalarFormData ν)
    {ι : Type*} [Fintype ι] (M : X → Matrix ι ι ℝ)
    (hM : ∀ i j, Integrable (fun x => M x i j) ν)
    (v : ι → Q.1) (B : ℝ) (hv : ∀ i, ∀ᵐ x ∂ν, |(v i).val x| ≤ B) :
    WeightedFormDomain Q M ⊤ v :=
  ⟨ae_of_all _ (fun _ => Submodule.mem_top),
    bounded_matrix_pair_integrable M hM _ _ B B hv hv⟩

/-- See Lemma 6.4 of the paper: the mean correction remains bounded by
the auxiliary component bound, including every finite active size. -/
theorem normal_component_bound_internal (Q : ScalarFormData ν) (n : ℕ+)
    (v : Fin (n : ℕ) → Q.1) (B : ℝ)
    (hv : ∀ i, ∀ᵐ x ∂ν, |(v i).val x| ≤ B) :
    ∀ᵐ x ∂ν, |((n : ℝ)⁻¹ • ∑ i, v i : Q.1).val x| ≤ B := by
  have hs := PhysicalPerturbation.sum_ae_bound_internal (fun i => (v i).val) B hv
  have hn : (0 : ℝ) < n := by positivity
  filter_upwards [hs, Lp.coeFn_smul (n : ℝ)⁻¹ (∑ i, (v i).val)] with x hx hm
  simp only [Submodule.coe_smul, Submodule.coe_sum, hm, Pi.smul_apply,
    smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hn)]
  have he : (n : ℝ)⁻¹ * ((n : ℝ) * B) = B := by field_simp
  have hh := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hn.le)
  simpa only [Fintype.card_fin, he] using hh

/-- Exact vector mass of the mean correction in Lemma 6.4.
It uses the Euclidean component norm, rather than the supremum norm. -/
theorem normal_value_norm (Q : ScalarFormData ν) (n : ℕ+) (S : Q.1) :
    ‖WithLp.toLp 2 (fun _i : Fin (n : ℕ) => ((n : ℝ)⁻¹ • S).val)‖ =
      (n : ℝ) ^ (-(1 : ℝ) / 2) * ‖S.val‖ := by
  have hn : (0 : ℝ) < n := by positivity
  have hs : ‖WithLp.toLp 2 (fun _i : Fin (n : ℕ) => ((n : ℝ)⁻¹ • S).val)‖ ^ 2 =
      (n : ℝ)⁻¹ * ‖S.val‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Submodule.coe_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hn), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hh := congrArg Real.sqrt hs
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (inv_nonneg.mpr hn.le),
    Real.sqrt_sq (norm_nonneg _)] at hh
  have he : Real.sqrt (n : ℝ)⁻¹ = (n : ℝ) ^ (-(1 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul hn.le]
    congr 1
    ring
  rwa [he] at hh

/-- The projection used in Lemma 6.4 is tangent in the
actual scalar form carrier. This asserts no projection in a matrix
energy domain. -/
theorem subtract_mean_sum_zero (Q : ScalarFormData ν) (n : ℕ+)
    (v : Fin (n : ℕ) → Q.1) :
    (∑ i : Fin (n : ℕ), (v i - (n : ℝ)⁻¹ • ∑ j, v j)) = 0 := by
  simpa only [ConstrainedNormalMultiplier.projectTuple] using
    ConstrainedNormalMultiplier.tuple_sum_zero n Q
    (ConstrainedNormalMultiplier.projectTuple n Q v)
    (ConstrainedNormalMultiplier.projectTuple_zeroSum n Q v)

/-- Exact normal diffusion energy in Lemma 6.4.
The scalar energy is the entire intrinsic form, with no derivative
realization chosen. -/
theorem normal_diffusion_energy (Q : ScalarFormData ν) (n : ℕ+) (S : Q.1) :
    (∑ _i : Fin (n : ℕ), Q.2 ((n : ℝ)⁻¹ • S) ((n : ℝ)⁻¹ • S)) =
      (n : ℝ)⁻¹ * Q.2 S S := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : (n : ℝ) ≠ 0 := by positivity
  field_simp

/-- Exact normal-field energy identity in Lemma 6.4.
The integral on the right is proved integrable from the existing natural
domain. -/
theorem normal_energy_identity_internal (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (n : ℕ+)
    (H : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (hH : ∀ᵐ x ∂ν, (H x).PosSemidef)
    (S : Q.1) (r : MatrixEnergy.Natural Q hQ H ⊤ hH)
    (hr : ∀ i, MatrixEnergy.tuple Q hQ H ⊤ hH r i = (n : ℝ)⁻¹ • S) :
    Integrable (fun x => S.val x ^ 2 * (∑ i, ∑ j, H x i j)) ν ∧
      MatrixEnergy.weakForm Q hQ H ⊤ hH r r =
        (n : ℝ)⁻¹ * Q.2 S S +
          (n : ℝ)⁻¹ ^ 2 * ∫ x, S.val x ^ 2 * (∑ i, ∑ j, H x i j) ∂ν := by
  let t := MatrixEnergy.tuple Q hQ H ⊤ hH
  let g := fun x => S.val x ^ 2 * (∑ i, ∑ j, H x i j)
  have hp : matrixFieldPair H (fun i => (t r i).val) (fun i => (t r i).val) =ᵐ[ν]
      fun x => (n : ℝ)⁻¹ ^ 2 * g x := by
    filter_upwards [Lp.coeFn_smul (n : ℝ)⁻¹ S.val] with x hx
    have hv (i) : (t r i).val x = (n : ℝ)⁻¹ * S.val x := by
      change (MatrixEnergy.tuple Q hQ H ⊤ hH r i).val x = _
      rw [hr]
      exact hx
    simp only [matrixFieldPair, hv]
    dsimp only [g]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hi : Integrable (fun x => (n : ℝ)⁻¹ ^ 2 * g x) ν :=
    (MatrixEnergy.integrable_pair Q hQ H ⊤ hH r r).congr hp
  have hg : Integrable g ν := (integrable_const_mul_iff
    (isUnit_iff_ne_zero.mpr (by positivity : (n : ℝ)⁻¹ ^ 2 ≠ 0)) g).mp hi
  refine ⟨hg, ?_⟩
  rw [MatrixEnergy.weakForm_apply, integral_congr_ae hp, integral_const_mul]
  congr 1
  simp_rw [hr]
  exact normal_diffusion_energy Q n S

/-- Good-set and exceptional normal energy in Lemma 6.4.
Only a first absolute coefficient moment on the exceptional set is
needed. This is supplied by its weighted local law. -/
theorem normal_energy_estimate_internal (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (n : ℕ+)
    (H : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (hH : ∀ᵐ x ∂ν, (H x).PosSemidef)
    (S : Q.1) (r : MatrixEnergy.Natural Q hQ H ⊤ hH)
    (hr : ∀ i, MatrixEnergy.tuple Q hQ H ⊤ hH r i = (n : ℝ)⁻¹ • S)
    (G : Set X) (hG : MeasurableSet G) (K B Tail : ℝ) (hK : 0 ≤ K)
    (hSB : ∀ᵐ x ∂ν, |S.val x| ≤ B)
    (hgood : ∀ᵐ x ∂ν.restrict G, (∑ i, ∑ j, H x i j) ≤ K)
    (hbad : IntegrableOn (fun x => |∑ i, ∑ j, H x i j|) Gᶜ ν)
    (hbadmass : (∫ x in Gᶜ, |∑ i, ∑ j, H x i j| ∂ν) ≤ Tail) :
    MatrixEnergy.weakForm Q hQ H ⊤ hH r r ≤
      (n : ℝ)⁻¹ * Q.2 S S + (n : ℝ)⁻¹ ^ 2 * (K * ‖S.val‖ ^ 2 + B ^ 2 * Tail) := by
  obtain ⟨hi, he⟩ := normal_energy_identity_internal Q hQ n H hH S r hr
  have hS : Integrable (fun x => S.val x ^ 2) ν := (Lp.memLp S.val).integrable_sq
  have hnorm : (∫ x, S.val x ^ 2 ∂ν) = ‖S.val‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by simp only [Real.inner_apply, pow_two])
  have hg : (∫ x in G, S.val x ^ 2 * (∑ i, ∑ j, H x i j) ∂ν) ≤ K * ‖S.val‖ ^ 2 := by
    calc
      _ ≤ ∫ x in G, K * S.val x ^ 2 ∂ν := by
        apply integral_mono_ae hi.restrict ((hS.const_mul K).restrict)
        filter_upwards [hgood] with x hx
        nlinarith only [mul_le_mul_of_nonneg_left hx (sq_nonneg (S.val x))]
      _ = K * ∫ x in G, S.val x ^ 2 ∂ν := integral_const_mul _ _
      _ ≤ K * ∫ x, S.val x ^ 2 ∂ν := mul_le_mul_of_nonneg_left
        (integral_mono_measure Measure.restrict_le_self
          (ae_of_all _ (fun x => sq_nonneg (S.val x))) hS) hK
      _ = _ := by rw [hnorm]
  have hb : (∫ x in Gᶜ, S.val x ^ 2 * (∑ i, ∑ j, H x i j) ∂ν) ≤ B ^ 2 * Tail := by
    calc
      _ ≤ ∫ x in Gᶜ, B ^ 2 * |∑ i, ∑ j, H x i j| ∂ν := by
        apply integral_mono_ae hi.restrict (hbad.const_mul (B ^ 2))
        filter_upwards [ae_restrict_of_ae hSB] with x hx
        have hB : 0 ≤ B := (abs_nonneg _).trans hx
        have hs : S.val x ^ 2 ≤ B ^ 2 := by
          nlinarith only [sq_abs (S.val x), sq_le_sq₀ (abs_nonneg _) hB |>.mpr hx]
        exact (mul_le_mul_of_nonneg_left (le_abs_self _) (sq_nonneg _)).trans
          (mul_le_mul_of_nonneg_right hs (abs_nonneg _))
      _ = B ^ 2 * ∫ x in Gᶜ, |∑ i, ∑ j, H x i j| ∂ν := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hbadmass (sq_nonneg _)
  rw [he, ← integral_add_compl hG hi]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add hg hb) (by positivity))

/-- Tangent comparison on the existing natural physical energy space,
supporting Lemma 6.4. The physical matrix can be unbounded.
The auxiliary and normal fields must have finite physical energy before
this lemma is used, so every test and integral is legitimate. -/
theorem natural_tangent_comparison_internal (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (n : ℕ+)
    (H : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (hH : ∀ᵐ x ∂ν, (H x).PosSemidef)
    (a : ℝ) (ha : 0 < a)
    (hlower : ∀ᵐ x ∂ν, ∀ z : Fin (n : ℕ) → ℝ,
      a * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * H x i j * z j)
    (f : Fin (n : ℕ) → Lp ℝ 2 ν)
    (ψ v r : MatrixEnergy.Natural Q hQ H ⊤ hH)
    (hψ : WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ))) f
      (MatrixEnergy.tuple Q hQ H ⊤ hH ψ))
    (hz : ∑ i, MatrixEnergy.tuple Q hQ H ⊤ hH (v - r) i = 0)
    (A : MatrixEnergy.Natural Q hQ H ⊤ hH →L[ℝ]
      MatrixEnergy.Natural Q hQ H ⊤ hH →L[ℝ] ℝ)
    (haux : ∀ w : MatrixEnergy.Natural Q hQ H ⊤ hH,
      A v w = ∑ i, inner ℝ (f i) (MatrixEnergy.tuple Q hQ H ⊤ hH w i).val)
    (L τ R : ℝ) (hL : 0 ≤ L) (hτ : 0 ≤ τ) (hR : 0 ≤ R)
    (hpert : |MatrixEnergy.weakForm Q hQ H ⊤ hH v (v - r - ψ) - A v (v - r - ψ)| ≤
      L * ‖MatrixEnergy.values Q hQ H ⊤ hH (v - r - ψ)‖ + τ)
    (hr : MatrixEnergy.weakForm Q hQ H ⊤ hH r r ≤ R) :
    ‖MatrixEnergy.values Q hQ H ⊤ hH (ψ - v)‖ ≤
      2 * L / a + Real.sqrt ((2 * τ + R) / a) +
        ‖MatrixEnergy.values Q hQ H ⊤ hH r‖ := by
  let u := v - r - ψ
  let t := MatrixEnergy.tuple Q hQ H ⊤ hH
  let J := MatrixEnergy.values Q hQ H ⊤ hH
  let E := MatrixEnergy.weakForm Q hQ H ⊤ hH
  have hsψ : (∑ i, t ψ i) = 0 :=
    ConstrainedNormalMultiplier.tuple_sum_zero n Q _ hψ.1.1
  have hsu : (∑ i, t u i) = 0 := by
    simp only [u, map_sub, Pi.sub_apply, Finset.sum_sub_distrib]
    change ((∑ i, t v i) - ∑ i, t r i) - ∑ i, t ψ i = 0
    have hz' : (∑ i, t v i) - ∑ i, t r i = 0 := by
      simpa only [map_sub, Pi.sub_apply, Finset.sum_sub_distrib] using hz
    rw [hz', hsψ, sub_zero]
  have hutan : ∀ᵐ x ∂ν, (fun i => (t u i).val x) ∈ zeroSumComponents (Fin (n : ℕ)) := by
    have hval : (∑ i, (t u i).val) = 0 := by
      rw [← Submodule.coe_sum, hsu, Submodule.coe_zero]
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => (t u i).val),
      Lp.coeFn_zero ℝ 2 ν] with x hx hz
    change (∑ i, (t u i).val x) = 0
    simpa only [Pi.zero_apply] using hx.symm.trans ((congrArg (fun f : Lp ℝ 2 ν => f x) hval).trans hz)
  have hdu : WeightedFormDomain Q H (zeroSumComponents (Fin (n : ℕ))) (t u) :=
    ⟨hutan, (MatrixEnergy.tuple_mem Q hQ H ⊤ hH u).2⟩
  have heψ : E ψ u = ∑ i, inner ℝ (f i) (t u i).val := by
    change MatrixEnergy.weakForm Q hQ H ⊤ hH ψ u = _
    rw [MatrixEnergy.weakForm_apply]
    exact (hψ.2 (t u) hdu).2
  have hid : E u u + E r u = E v u - A v u := by
    have he := heψ.trans (haux u).symm
    change E (v - r - ψ) u + E r u = _
    simp only [map_sub, sub_apply] at ⊢
    rw [he]
    ring
  have hcoerc : a * ‖J u‖ ^ 2 ≤ E u u :=
    MatrixEnergy.weakForm_mass_bound Q hQ H ⊤ hH a
      (hlower.mono (fun x hx z _ => hx z)) u
  have hres : E u u + E r u ≤ L * ‖J u‖ + τ := by
    rw [hid]
    exact (le_abs_self _).trans hpert
  have hcomp := tangent_comparison_bound_internal E.toLinearMap₁₂
    (MatrixEnergy.weakForm_symm Q hQ H ⊤ hH)
    (MatrixEnergy.weakForm_nonneg Q hQ H ⊤ hH) J.toLinearMap u r a L τ R
    ha hL hτ hR hcoerc hres hr
  have heq : ψ - v = -(u + r) := by dsimp only [u]; abel
  rw [heq, map_neg, norm_neg, map_add]
  exact (norm_add_le (J u) (J r)).trans (add_le_add hcomp le_rfl)

end NaturalComparison

section LongPerturbation

variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H]

/-- Column subtraction and the final row Cauchy--Schwarz step of
Lemma 6.4. The entry and increment premises are precisely
the bilinear estimates used from Subsection 6.1. The source value and mean
premises are those used from the proof of Lemma 6.4. The exceptional term
retains its explicit finite factor `3n²`. -/
theorem long_perturbation_pairing_internal (s : Riesz1.RieszExponent)
    (n m : ℕ+) (hnm : 2 * (n : ℕ) ≤ (m : ℕ)) (i₀ : Fin (n : ℕ))
    (hi₀ : |(i₀.val : ℝ) + 1 - (n : ℝ) / 2| ≤ (n : ℝ) / 4)
    (u : Fin (n : ℕ) → H) (v : Fin (n : ℕ) → V)
    (b : Fin (n : ℕ) → Fin (n : ℕ) → V →ₗ[ℝ] ℝ)
    (D F P Err : ℝ) (hD : 0 ≤ D) (hF : 0 ≤ F) (hP : 0 ≤ P) (hErr : 0 ≤ Err)
    (hvalue : ∀ k, ‖v k‖ ≤
      D * (1 + (Nat.dist k.val i₀.val : ℝ)) ^ (s.val - 2) * F)
    (hsum : ‖∑ k, v k‖ ≤ D * (n : ℝ) ^ (-(1 - s.val)) * F)
    (hentry : ∀ j k l,
      |b j l (v k)| ≤ P *
        (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) ^ (-s.val / 2) *
        (min (l.val + 1) ((n : ℕ) - l.val) : ℕ) ^ (-s.val / 2) *
        ‖u j‖ * ‖v k‖ + Err)
    (hincrement : ∀ j k,
      |b j k (v k) - b j i₀ (v k)| ≤ P *
        (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) ^ (-s.val / 2) *
        (Nat.dist k.val i₀.val : ℝ) *
        (min ((min (k.val + 1) ((n : ℕ) - k.val) : ℕ) : ℝ)
          ((min (i₀.val + 1) ((n : ℕ) - i₀.val) : ℕ) : ℝ)) ^ (-1 - s.val / 2) *
        ‖u j‖ * ‖v k‖ + Err)
    (hmean : ∀ j,
      |b j i₀ (∑ k, v k)| ≤ P *
        (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) ^ (-s.val / 2) *
        (min (i₀.val + 1) ((n : ℕ) - i₀.val) : ℕ) ^ (-s.val / 2) *
        ‖u j‖ * ‖∑ k, v k‖ + (n : ℝ) * Err) :
    let K := 2 * 8 ^ (2 - s.val) * (2 / (1 - s.val / 2)) +
      8 ^ (1 + s.val / 2) * (2 / s.val) + 4 ^ (s.val / 2)
    |∑ j, ∑ k, b j k (v k)| ≤
      (K * Real.sqrt (2 / (1 - s.val))) * P * D * F *
        (n : ℝ) ^ (-(1 : ℝ) / 2) * ‖WithLp.toLp 2 u‖ +
          3 * (n : ℝ) ^ 2 * Err := by
  intro K
  let w := InteractionDifferential.boundaryWeight s.val n
  have hw (j) : w j = (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) ^ (-s.val / 2) :=
    InteractionDifferential.boundaryWeight_long s.property.2 n j
  have hK : 0 ≤ K := by
    dsimp only [K]
    have hs := s.property.1
    have hden : 0 < 1 - s.val / 2 := by linarith [s.property.2]
    positivity
  have hcent := abs_le.mp hi₀
  have hrow (j : Fin (n : ℕ)) : |∑ k, b j k (v k)| ≤
      K * P * D * F * (n : ℝ) ^ (-1 + s.val / 2) * (w j * ‖u j‖) +
        3 * (n : ℝ) * Err := by
    have hh := PhysicalPerturbation.cancellation_from_source_bounds_internal s n m hnm i₀
      (by linarith) (by linarith) (fun k => b j k) v (by simp only [map_sum])
      (fun k => ‖v k‖) ‖∑ k, v k‖ D F (P * w j * ‖u j‖) Err ((n : ℝ) * Err)
      hD hF (mul_nonneg (mul_nonneg hP
        (InteractionDifferential.boundaryWeight_pos s.val n j).le) (norm_nonneg _)) hErr
      (fun k => by simpa only [show -(2 - s.val) = s.val - 2 by ring,
        mul_assoc, mul_left_comm, mul_comm] using hvalue k) hsum
      (fun k l => by simpa only [hw, mul_assoc, mul_left_comm, mul_comm] using hentry j k l)
      (fun k => by simpa only [hw, mul_assoc, mul_left_comm, mul_comm] using hincrement j k)
      (by simpa only [hw, mul_assoc, mul_left_comm, mul_comm] using hmean j)
    exact hh.trans_eq (by dsimp only [K]; ring)
  have hnorm : (∑ j, w j * ‖u j‖) ≤
      Real.sqrt (2 / (1 - s.val)) * (n : ℝ) ^ ((1 - s.val) / 2) *
        ‖WithLp.toLp 2 u‖ := by
    apply (weighted_sum_norm_le w u).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply (Real.sqrt_le_sqrt (long_boundary_square_sum s n)).trans_eq
    rw [Real.sqrt_mul (by have := s.property.2; positivity)]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ n)]
    congr 1
    ring
  have hn : (0 : ℝ) < n := by positivity
  have hp : (n : ℝ) ^ (-1 + s.val / 2) * (n : ℝ) ^ ((1 - s.val) / 2) =
      (n : ℝ) ^ (-(1 : ℝ) / 2) := by
    rw [← Real.rpow_add hn]
    congr 1
    ring
  calc
    _ ≤ ∑ j, |∑ k, b j k (v k)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, (K * P * D * F * (n : ℝ) ^ (-1 + s.val / 2) * (w j * ‖u j‖) +
        3 * (n : ℝ) * Err) := Finset.sum_le_sum (fun j _ => hrow j)
    _ = (K * P * D * F * (n : ℝ) ^ (-1 + s.val / 2)) * (∑ j, w j * ‖u j‖) +
        3 * (n : ℝ) ^ 2 * Err := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ ≤ (K * P * D * F * (n : ℝ) ^ (-1 + s.val / 2)) *
        (Real.sqrt (2 / (1 - s.val)) * (n : ℝ) ^ ((1 - s.val) / 2) *
          ‖WithLp.toLp 2 u‖) + 3 * (n : ℝ) ^ 2 * Err :=
      add_le_add (mul_le_mul_of_nonneg_left hnorm (by positivity)) le_rfl
    _ = _ := by
      calc
        _ = (K * Real.sqrt (2 / (1 - s.val))) * P * D * F *
            ((n : ℝ) ^ (-1 + s.val / 2) * (n : ℝ) ^ ((1 - s.val) / 2)) *
              ‖WithLp.toLp 2 u‖ + 3 * (n : ℝ) ^ 2 * Err := by ring
        _ = _ := by rw [hp]

end LongPerturbation

section ShortMean

open InitialDecay

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι] {ν : Measure X}

/-- The short-range mean and mean-gradient step of Lemma 6.4. Summability of the reciprocal distortion weights turns
the Lemma 4.4 estimate into bounds on the actual
scalar-form sum. This retains the whole intrinsic gradient energy. -/
theorem short_mean_from_weighted_estimate_internal (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (g : ComponentGeometry ι) (i₀ : ι)
    (α D : ℝ) (hα : 1 / 2 < α) (v : ι → Q.1)
    (hweighted :
      ‖WithLp.toLp 2 (fun i => distortionWeight g i₀ α i • (v i).val)‖ +
        Real.sqrt (∑ i, Q.2 (distortionWeight g i₀ α i • v i)
          (distortionWeight g i₀ α i • v i)) ≤ D) :
    let C := Real.sqrt (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(2 * α)))
    (∑ i, ‖(v i).val‖) + Real.sqrt (Q.2 (∑ i, v i) (∑ i, v i)) ≤ C * D ∧
      ‖(∑ i, v i).val‖ + Real.sqrt (Q.2 (∑ i, v i) (∑ i, v i)) ≤ C * D := by
  intro C
  have hv := OptimalDecay.Internal.sum_le_weighted g i₀ α hα
    (fun i => ‖(v i).val‖) (fun _ => norm_nonneg _)
  have hmass : Real.sqrt (∑ i, (distortionWeight g i₀ α i * ‖(v i).val‖) ^ 2) =
      ‖WithLp.toLp 2 (fun i => distortionWeight g i₀ α i • (v i).val)‖ := by
    rw [PiLp.norm_eq_of_L2]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (distortionWeight_pos _ _ _ _)]
  rw [hmass] at hv
  have he := OptimalDecay.Internal.sum_le_weighted g i₀ α hα
    (fun i => Real.sqrt (Q.2 (v i) (v i))) (fun _ => Real.sqrt_nonneg _)
  have hform : (∑ i, (distortionWeight g i₀ α i * Real.sqrt (Q.2 (v i) (v i))) ^ 2) =
      ∑ i, Q.2 (distortionWeight g i₀ α i • v i) (distortionWeight g i₀ α i • v i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_pow, Real.sq_sqrt (hQ.2.2.1 _)]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hform] at he
  have hs := SummedWeakEquation.sqrt_energy_sum_le Q hQ Finset.univ v
  have hboth : (∑ i, ‖(v i).val‖) + Real.sqrt (Q.2 (∑ i, v i) (∑ i, v i)) ≤ C * D := by
    apply (add_le_add hv (hs.trans he)).trans
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left hweighted (Real.sqrt_nonneg _)
  refine ⟨hboth, ?_⟩
  apply le_trans (add_le_add ?_ le_rfl) hboth
  simpa only [Submodule.coe_sum] using norm_sum_le Finset.univ (fun i => (v i).val)

end ShortMean

section DecayAssembly

variable {H : Type*} [NormedAddCommGroup H]

/-- Final weighted and unweighted norm assembly for Lemma 6.4. An auxiliary profile with boundary exponent `q`, a
boundary-square estimate with power `1-2q`, and a vector error of order
`n⁻¹ᐟ²` give both displayed source conclusions. -/
theorem decay_sums_from_comparison_internal (n : ℕ+) (w : Fin (n : ℕ) → ℝ)
    (hw : ∀ i, 0 ≤ w i) (q W A D E F G : ℝ)
    (hW : 0 ≤ W) (hA : 0 ≤ A) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hFG : F ≤ G) (hG : 0 ≤ G)
    (ψ v : Fin (n : ℕ) → H)
    (hweight : (∑ i, w i ^ 2) ≤ W * (n : ℝ) ^ (1 - 2 * q))
    (hvweight : (∑ i, w i * ‖v i‖) ≤ A * (n : ℝ) ^ (-q) * F)
    (hvsum : (∑ i, ‖v i‖) ≤ D * F)
    (herror : ‖WithLp.toLp 2 (fun i => ψ i - v i)‖ ≤
      E * (n : ℝ) ^ (-(1 : ℝ) / 2) * G) :
    (∑ i, w i * ‖ψ i‖) ≤ (A + Real.sqrt W * E) * (n : ℝ) ^ (-q) * G ∧
      (∑ i, ‖ψ i‖) ≤ (D + E) * G := by
  have hn : (0 : ℝ) < n := by positivity
  have hsqrt : Real.sqrt (∑ i, w i ^ 2) ≤
      Real.sqrt W * (n : ℝ) ^ ((1 : ℝ) / 2 - q) := by
    apply (Real.sqrt_le_sqrt hweight).trans_eq
    rw [Real.sqrt_mul hW]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn.le]
    congr 1
    ring
  have hp : (n : ℝ) ^ ((1 : ℝ) / 2 - q) * (n : ℝ) ^ (-(1 : ℝ) / 2) =
      (n : ℝ) ^ (-q) := by
    rw [← Real.rpow_add hn]
    congr 1
    ring
  have hcancel : Real.sqrt (n : ℝ) * (n : ℝ) ^ (-(1 : ℝ) / 2) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn,
      show (1 : ℝ) / 2 + -(1 : ℝ) / 2 = 0 by ring, Real.rpow_zero]
  constructor
  · have ht := weighted_sum_norm_transfer_internal w hw ψ v _ _ hvweight herror
    apply ht.trans
    calc
      _ ≤ A * (n : ℝ) ^ (-q) * G +
          (Real.sqrt W * (n : ℝ) ^ ((1 : ℝ) / 2 - q)) *
            (E * (n : ℝ) ^ (-(1 : ℝ) / 2) * G) :=
        add_le_add (mul_le_mul_of_nonneg_left hFG (by positivity))
          (mul_le_mul_of_nonneg_right hsqrt (by positivity))
      _ = _ := by
        calc
          _ = A * (n : ℝ) ^ (-q) * G + Real.sqrt W * E *
              ((n : ℝ) ^ ((1 : ℝ) / 2 - q) * (n : ℝ) ^ (-(1 : ℝ) / 2)) * G := by ring
          _ = _ := by rw [hp]; ring
  · have ht := weighted_sum_norm_transfer_internal (fun _ : Fin (n : ℕ) => 1)
      (fun _ => zero_le_one) ψ v _ _
      (by simpa only [one_mul] using hvsum) herror
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] at ht
    apply ht.trans
    calc
      _ ≤ D * G + Real.sqrt (n : ℝ) * (E * (n : ℝ) ^ (-(1 : ℝ) / 2) * G) :=
        add_le_add (mul_le_mul_of_nonneg_left hFG hD) le_rfl
      _ = D * G + E * (Real.sqrt (n : ℝ) * (n : ℝ) ^ (-(1 : ℝ) / 2)) * G := by ring
      _ = _ := by rw [hcancel]; ring

/-- See Lemma 6.4 of the paper, long-range final assembly from the
auxiliary value and total-sum conclusions of the proof of Lemma 6.4 and a
comparison in the actual vector norm. -/
theorem long_decay_sums_internal (s : Riesz1.RieszExponent) (n : ℕ+)
    (i₀ : Fin (n : ℕ))
    (hi₀ : |(i₀.val : ℝ) + 1 - (n : ℝ) / 2| ≤ (n : ℝ) / 4)
    (D E F G : ℝ) (hD : 0 ≤ D) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hFG : F ≤ G) (hG : 0 ≤ G) (ψ v : Fin (n : ℕ) → H)
    (hvalue : ∀ j, ‖v j‖ ≤
      D * (1 + (Nat.dist j.val i₀.val : ℝ)) ^ (s.val - 2) * F)
    (hsum : (∑ j, ‖v j‖) ≤ D * F)
    (herror : ‖WithLp.toLp 2 (fun j => ψ j - v j)‖ ≤
      E * (n : ℝ) ^ (-(1 : ℝ) / 2) * G) :
    let K := 8 ^ (2 - s.val) * (2 / (1 - s.val / 2)) + 8 ^ (s.val / 2)
    (∑ j, InteractionDifferential.boundaryWeight s.val n j * ‖ψ j‖) ≤
      (K * D + Real.sqrt (2 / (1 - s.val)) * E) * (n : ℝ) ^ (-s.val / 2) * G ∧
    (∑ j, ‖ψ j‖) ≤ (D + E) * G := by
  intro K
  have hK : 0 ≤ K := by
    dsimp only [K]
    have hden : 0 < 1 - s.val / 2 := by linarith [s.property.2]
    positivity
  have hv := long_auxiliary_weighted_sum_internal s n i₀ hi₀ D F hD hF
    (fun j => ‖v j‖) (fun j => norm_nonneg _) hvalue hsum
  have hw := long_boundary_square_sum s n
  have hh := decay_sums_from_comparison_internal n
    (InteractionDifferential.boundaryWeight s.val n)
    (fun j => (InteractionDifferential.boundaryWeight_pos _ _ _).le)
    (s.val / 2) (2 / (1 - s.val)) (K * D) D E F G
    (by have := s.property.2; positivity) (mul_nonneg hK hD) hD hE hFG hG ψ v
    (by simpa only [show (1 : ℝ) - 2 * (s.val / 2) = 1 - s.val by ring] using hw)
    (by simpa only [K, neg_div, mul_assoc, mul_left_comm, mul_comm] using hv) hsum herror
  simpa only [neg_div] using hh

/-- See Lemma 6.4 of the paper, short-range final assembly. The only
vector comparison error is `n⁻¹ᐟ²`. Square summability of the literal
boundary weights preserves that exponent. -/
theorem short_decay_sums_internal (s : ℝ) (hs : 1 < s) (n : ℕ+)
    (i₀ : Fin (n : ℕ))
    (hi₀ : |(i₀.val : ℝ) + 1 - (n : ℝ) / 2| ≤ (n : ℝ) / 4)
    (D E F G : ℝ) (hD : 0 ≤ D) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hFG : F ≤ G) (hG : 0 ≤ G) (ψ v : Fin (n : ℕ) → H)
    (hvalue : ∀ j, ‖v j‖ ≤ D * (1 + (Nat.dist j.val i₀.val : ℝ)) ^ (-s) * F)
    (hsum : (∑ j, ‖v j‖) ≤ D * F)
    (herror : ‖WithLp.toLp 2 (fun j => ψ j - v j)‖ ≤
      E * (n : ℝ) ^ (-(1 : ℝ) / 2) * G) :
    let W := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(2 * s - 1))
    (∑ j, InteractionDifferential.boundaryWeight s n j * ‖ψ j‖) ≤
      ((4 * 8 ^ s + Real.sqrt 8) * D + Real.sqrt W * E) *
        (n : ℝ) ^ (-(1 : ℝ) / 2) * G ∧
    (∑ j, ‖ψ j‖) ≤ (D + E) * G := by
  intro W
  have hW : 0 ≤ W := mul_nonneg (by norm_num)
    (tsum_nonneg (fun k => Real.rpow_nonneg (by positivity) _))
  have hv := short_auxiliary_weighted_sum_internal s hs n i₀ hi₀ D F hD hF
    (fun j => ‖v j‖) (fun j => norm_nonneg _) hvalue hsum
  have hh := decay_sums_from_comparison_internal n
    (InteractionDifferential.boundaryWeight s n)
    (fun j => (InteractionDifferential.boundaryWeight_pos _ _ _).le)
    (1 / 2) W ((4 * 8 ^ s + Real.sqrt 8) * D) D E F G
    hW (by positivity) hD hE hFG hG ψ v
    (by simpa only [show (1 : ℝ) - 2 * (1 / 2) = 0 by ring, Real.rpow_zero, mul_one]
      using short_boundary_square_sum s hs n)
    (by simpa only [neg_div, mul_assoc, mul_left_comm, mul_comm] using hv) hsum herror
  simpa only [neg_div] using hh

end DecayAssembly

end Riesz2.FixedLengthDecay
