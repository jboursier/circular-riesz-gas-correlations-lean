/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.DerivativeCommutatorsPart2
public import Riesz2.ToMathlib.FiniteSchurBounds

/-!
# The four regions of the endpoint commutator

The proof of Lemma 5.12 in the paper splits
pairs according to the output radius, then according to distance (large
output radius) or input radius (small output radius).
-/

@[expose] public section

noncomputable section

open scoped BigOperators Fin.NatCast Matrix
open Finset

attribute [local instance] Classical.propDecidable

namespace Riesz2.GlobalEndpointRegions

/-- Lemma 5.12: the comparable radii in the first region. -/
theorem near_geometry {x y d : ℝ} (hd : |x - y| ≤ d) (hnear : d ≤ x / 2) :
    x / 2 ≤ y ∧ y ≤ 3 * x / 2 ∧ d ≤ y := by
  rw [abs_sub_le_iff] at hd
  constructor
  · linarith [hd.1]
  constructor <;> linarith [hd.1, hd.2]

/-- Lemma 5.12: mean-value estimate after dividing by
the input weight, on comparable radii. -/
theorem near_power_difference (a : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ {x y d : ℝ}, 0 < x → 0 < y →
      |x - y| ≤ d → d ≤ x / 2 →
      |x ^ a - y ^ a| / y ^ a ≤ C * d / x := by
  obtain ⟨C, hC, hc⟩ := DerivativeCommutators.retained_power_difference a
  refine ⟨4 * C, by positivity, ?_⟩
  intro x y d hx hy hd hn
  obtain ⟨hxy, hyx, _⟩ := near_geometry hd hn
  have hpow : x ^ a ≤ 4 * y ^ a := by
    calc
      x ^ a ≤ (2 * y) ^ a := Real.rpow_le_rpow hx.le (by linarith) ha
      _ = (2 : ℝ) ^ a * y ^ a := Real.mul_rpow (by norm_num) hy.le
      _ ≤ 4 * y ^ a := by
        gcongr
        exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) ha2).trans_eq
          (by norm_num)
  have hdiff := (hc hx hy hxy (by linarith)).trans
    (mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ C * x ^ (a - 1)))
  rw [div_le_iff₀ (Real.rpow_pos_of_pos hy a)]
  rw [Real.rpow_sub_one hx.ne'] at hdiff
  have hd0 : 0 ≤ d := (abs_nonneg _).trans hd
  calc
    _ ≤ C * (x ^ a / x) * d := hdiff
    _ ≤ C * (4 * y ^ a / x) * d := by gcongr
    _ = _ := by ring

/-- Lemma 5.12: the first moment of the decay kernel
on a ball, using the cyclic shell bound with exponent `p - 1`. -/
theorem near_shell_sum {p T : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (N : ℕ+) (i : Fin (N : ℕ)) (hT : 1 ≤ T) :
    (∑ j ∈ univ.filter (fun j => (Riesz1.cyclicIndexDistance N i j : ℝ) ≤ T),
      (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (1 - p)) ≤
      (4 / (2 - p)) * T ^ (2 - p) := by
  have hs := sum_weightRadius_le_of_lt_one N i
    (t := p - 1) (R := 2 * T) (by linarith) (by linarith) (by linarith)
  have hsub : univ.filter (fun j => (Riesz1.cyclicIndexDistance N i j : ℝ) ≤ T) ⊆
      univ.filter (fun j => weightRadius N j i ≤ 2 * T) := by
    intro j hj
    rw [mem_filter] at hj ⊢
    refine ⟨mem_univ _, ?_⟩
    rw [weightRadius_eq_comm]
    linarith [hj.2]
  have heq (j : Fin (N : ℕ)) :
      (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (1 - p) =
      weightRadius N j i ^ (-(p - 1)) := by
    rw [weightRadius_eq_comm]
    congr 1
    ring
  simp_rw [heq]
  refine (sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ =>
    Real.rpow_nonneg (by linarith [one_le_weightRadius N j i]) _)).trans
    (hs.trans ?_)
  have htwo : (2 : ℝ) ^ (2 - p) ≤ 2 := by
    calc
      _ ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one _
  rw [Real.mul_rpow (by norm_num) (by linarith : 0 ≤ T)]
  convert mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right htwo (by positivity : 0 ≤ T ^ (2 - p)))
    (by positivity : 0 ≤ 2 / (2 - p)) using 1 <;> ring_nf

/-- Lemma 5.12: clamping the column radius against the
cutoff gives the same small Schur factor as the row estimate. -/
theorem clamped_power {p R y : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (hR : 0 < R) (hy : 0 < y) :
    y ^ (2 - p) / max R y ≤ R ^ (1 - p) := by
  by_cases h : y ≤ R
  · rw [max_eq_left h, div_le_iff₀ hR]
    calc
      _ ≤ R ^ (2 - p) := Real.rpow_le_rpow hy.le h (by linarith)
      _ = _ := by rw [← Real.rpow_add_one hR.ne']; congr 1; ring
  · rw [max_eq_right (le_of_not_ge h), ← Real.rpow_sub_one hy.ne']
    convert Real.rpow_le_rpow_of_nonpos hR (le_of_not_ge h) (by linarith : 1 - p ≤ 0)
      using 1
    congr 1
    ring

/-- Lemma 5.12: row and column Schur sums in the
large-radius, short-distance region, after the mean-value estimate. -/
theorem near_schur_sums {p : ℝ} (hp : 1 < p) (hp2 : p < 2)
    (N : ℕ+) (i₀ : Fin (N : ℕ)) {R : ℝ} (hR : 1 ≤ R) :
    let r := fun i => weightRadius N i i₀
    let d := fun i j => (Riesz1.cyclicIndexDistance N i j : ℝ)
    let K := fun i j => if R ≤ r i ∧ d i j ≤ r i / 2
      then (1 + d i j) ^ (1 - p) / r i else 0
    (∀ i, ∑ j, K i j ≤ (8 / (2 - p)) * R ^ (1 - p)) ∧
      (∀ j, ∑ i, K i j ≤ (8 / (2 - p)) * R ^ (1 - p)) := by
  classical
  dsimp only
  let r := fun i => weightRadius N i i₀
  let d := fun i j => (Riesz1.cyclicIndexDistance N i j : ℝ)
  have hr i : 1 ≤ r i := one_le_weightRadius N i i₀
  have hd i j : |r i - r j| ≤ d i j :=
    DerivativeCommutators.weightRadius_lipschitz N i₀ i j
  have hR0 : 0 < R := by linarith
  have hp0 : 0 < 2 - p := by linarith
  have hkernel i j : 0 ≤ (1 + d i j) ^ (1 - p) := by
    apply Real.rpow_nonneg
    dsimp [d]
    positivity
  constructor
  · intro i
    change (∑ j, if R ≤ r i ∧ d i j ≤ r i / 2 then
      (1 + d i j) ^ (1 - p) / r i else 0) ≤ _
    by_cases hi : R ≤ r i
    · have hs := near_shell_sum hp hp2 N i (hr i)
      have hsum : (∑ j, if R ≤ r i ∧ d i j ≤ r i / 2 then
          (1 + d i j) ^ (1 - p) / r i else 0) ≤
          (∑ j ∈ univ.filter (fun j => d i j ≤ r i),
            (1 + d i j) ^ (1 - p)) / r i := by
        rw [sum_div, sum_filter]
        apply sum_le_sum
        intro j _
        split_ifs with hj hk hk
        · exact le_rfl
        · exfalso
          exact hk (by linarith [hj.2, hr i])
        · exact div_nonneg (hkernel i j) (by linarith [hr i])
        · exact le_rfl
      calc
        _ ≤ _ := hsum
        _ ≤ ((4 / (2 - p)) * r i ^ (2 - p)) / r i :=
          div_le_div_of_nonneg_right hs (by linarith [hr i])
        _ = (4 / (2 - p)) * r i ^ (1 - p) := by
          rw [mul_div_assoc, ← Real.rpow_sub_one (by linarith [hr i] : r i ≠ 0)]
          congr 2
          ring
        _ ≤ (4 / (2 - p)) * R ^ (1 - p) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos hR0 hi (by linarith)) (by positivity)
        _ ≤ _ := by gcongr; linarith
    · simp only [hi, false_and, ↓reduceIte, sum_const_zero]
      positivity
  · intro j
    have hs := near_shell_sum hp hp2 N j (hr j)
    have hmax : 0 < max R (r j) := lt_of_lt_of_le hR0 (le_max_left _ _)
    have hsum : (∑ i, if R ≤ r i ∧ d i j ≤ r i / 2 then
        (1 + d i j) ^ (1 - p) / r i else 0) ≤
        2 * (∑ i ∈ univ.filter (fun i => d j i ≤ r j),
          (1 + d j i) ^ (1 - p)) / max R (r j) := by
      rw [sum_filter, mul_sum, sum_div]
      apply sum_le_sum
      intro i _
      have hsym : d j i = d i j := by dsimp [d]; rw [cyclicIndexDistance_comm' N j i]
      by_cases h : R ≤ r i ∧ d i j ≤ r i / 2
      · obtain ⟨_, hy, hdist⟩ := near_geometry (hd i j) h.2
        have hden : max R (r j) ≤ 2 * r i := max_le (by linarith [h.1, hr i]) (by linarith)
        simp only [h, ↓reduceIte, hsym, hdist]
        apply (div_le_iff₀ (by linarith [hr i] : 0 < r i)).mpr
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hmax).mpr
        convert mul_le_mul_of_nonneg_left hden (hkernel i j) using 1; ring
      · simp only [h, ↓reduceIte]
        split_ifs <;> positivity
    change (∑ i, if R ≤ r i ∧ d i j ≤ r i / 2 then
      (1 + d i j) ^ (1 - p) / r i else 0) ≤ _
    calc
      _ ≤ _ := hsum
      _ ≤ 2 * ((4 / (2 - p)) * r j ^ (2 - p)) / max R (r j) := by gcongr
      _ = (8 / (2 - p)) * (r j ^ (2 - p) / max R (r j)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (clamped_power hp hp2 hR0 (by linarith [hr j])) (by positivity)

/-- Euclidean norm notation for the regional proof of
Lemma 5.12. -/
def norm₂ {ι : Type*} [Fintype ι] (u : ι → ℝ) : ℝ := ‖WithLp.toLp 2 u‖

/-- Lemma 5.12: Euclidean norm in the paper's coordinates. -/
theorem norm₂_eq {ι : Type*} [Fintype ι] (u : ι → ℝ) :
    norm₂ u = Real.sqrt (∑ i, u i ^ 2) := by
  simp [norm₂, PiLp.norm_eq_sum, Real.sqrt_eq_rpow, Real.norm_eq_abs]

/-- Internal finite Schur conversion used in Lemma 5.12. -/
theorem internal_weighted_schur {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (w v : ι → ℝ) (hw : ∀ j, 0 < w j)
    {H : ℝ} (hH : 0 ≤ H)
    (hrow : ∀ i, ∑ j, |K i j| / w j ≤ H)
    (hcol : ∀ j, ∑ i, |K i j| / w j ≤ H) :
    norm₂ (fun i => ∑ j, K i j * v j) ≤ H * norm₂ (fun j => w j * v j) := by
  have h := FiniteSchurBounds.sqrt_sum_sq_norm_le
    (fun i j => K i j / w j) (fun j => w j * v j) hH
    (fun i => by simpa only [abs_div, abs_of_pos (hw _)] using hrow i)
    (fun j => by simpa only [abs_div, abs_of_pos (hw _)] using hcol j)
  have heq i j : K i j / w j * (w j * v j) = K i j * v j := by
    field_simp [(hw j).ne']
  simpa only [smul_eq_mul, Real.norm_eq_abs, sq_abs, heq, norm₂_eq] using h

/-- Lemma 5.12: the first region, by the mean-value
estimate and the row and column Schur tests. -/
theorem large_near {p : ℝ} (hp : 1 < p) (hp2 : p < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (i₀ : Fin (N : ℕ))
      (B : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
      (Bstar : ℝ), 0 ≤ Bstar →
      (∀ i j, |B i j| ≤ Bstar * (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-p)) →
      ∀ R : ℝ, 1 ≤ R → ∀ v : Fin (N : ℕ) → ℝ,
      let r := fun i => weightRadius N i i₀
      norm₂ (fun i => ∑ j, if R ≤ r i ∧
        (Riesz1.cyclicIndexDistance N i j : ℝ) ≤ r i / 2 then
        (r i ^ (p - 1 / 2) - r j ^ (p - 1 / 2)) * B i j * v j else 0) ≤
        C * Bstar * R ^ (1 - p) * norm₂ (fun j => r j ^ (p - 1 / 2) * v j) := by
  classical
  obtain ⟨C, hC, hc⟩ := near_power_difference (p - 1 / 2) (by linarith) (by linarith)
  refine ⟨C * (8 / (2 - p)), by positivity, ?_⟩
  intro N i₀ B Bstar hB hdec R hR v
  dsimp only
  let r := fun i => weightRadius N i i₀
  let d := fun i j => (Riesz1.cyclicIndexDistance N i j : ℝ)
  let K := fun i j => if R ≤ r i ∧ d i j ≤ r i / 2 then
    (r i ^ (p - 1 / 2) - r j ^ (p - 1 / 2)) * B i j else 0
  let A := fun i j => if R ≤ r i ∧ d i j ≤ r i / 2 then
    (1 + d i j) ^ (1 - p) / r i else 0
  have hr i : 0 < r i := by linarith [one_le_weightRadius N i i₀]
  have hA i j : |K i j| / r j ^ (p - 1 / 2) ≤ C * Bstar * A i j := by
    dsimp only [K, A]
    split_ifs with h
    · have hd := DerivativeCommutators.weightRadius_lipschitz N i₀ i j
      have hm := hc (hr i) (hr j) hd h.2
      have hd0 : 0 ≤ d i j := Nat.cast_nonneg _
      have hD : 0 < 1 + d i j := by linarith
      rw [abs_mul]
      calc
        _ = (|r i ^ (p - 1 / 2) - r j ^ (p - 1 / 2)| /
            r j ^ (p - 1 / 2)) * |B i j| := by ring
        _ ≤ (|r i ^ (p - 1 / 2) - r j ^ (p - 1 / 2)| /
            r j ^ (p - 1 / 2)) * (Bstar * (1 + d i j) ^ (-p)) := by
          exact mul_le_mul_of_nonneg_left (hdec i j)
            (div_nonneg (abs_nonneg _) (Real.rpow_pos_of_pos (hr j) _).le)
        _ ≤ (C * d i j / r i) * (Bstar * (1 + d i j) ^ (-p)) :=
          mul_le_mul_of_nonneg_right hm (by positivity)
        _ ≤ (C * (1 + d i j) / r i) * (Bstar * (1 + d i j) ^ (-p)) :=
          mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left (by linarith : d i j ≤ 1 + d i j) hC.le)
              (hr i).le) (by positivity)
        _ = _ := by
          rw [show (1 + d i j) ^ (1 - p) =
            (1 + d i j) * (1 + d i j) ^ (-p) by
              rw [show 1 - p = 1 + -p by ring, Real.rpow_add hD, Real.rpow_one]]
          ring
    · simp
  obtain ⟨hrow, hcol⟩ := near_schur_sums hp hp2 N i₀ hR
  have h := internal_weighted_schur K (fun j => r j ^ (p - 1 / 2)) v
    (fun j => Real.rpow_pos_of_pos (hr j) _)
    (H := (C * (8 / (2 - p))) * Bstar * R ^ (1 - p)) (by positivity)
    (fun i => (sum_le_sum fun j _ => hA i j).trans (by
      rw [← mul_sum]
      convert mul_le_mul_of_nonneg_left (hrow i) (by positivity : 0 ≤ C * Bstar) using 1
      ring))
    (fun j => (sum_le_sum fun i _ => hA i j).trans (by
      rw [← mul_sum]
      convert mul_le_mul_of_nonneg_left (hcol j) (by positivity : 0 ≤ C * Bstar) using 1
      ring))
  convert h using 2
  funext i
  apply sum_congr rfl
  intro j _
  dsimp only [K, r, d]
  split_ifs <;> simp

/-- Internal weighted Cauchy–Schwarz step of
Lemma 5.12, in squared form. -/
theorem internal_rank_one {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (a b u : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hK : ∀ i j, |K i j| ≤ a i * b j) :
    norm₂ (fun i => ∑ j, K i j * u j) ≤
      Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ j, b j ^ 2) * norm₂ u := by
  have hcs := sum_mul_sq_le_sq_mul_sq univ b (fun j => |u j|)
  simp only [sq_abs] at hcs
  have hsum : (∑ i, (∑ j, K i j * u j) ^ 2) ≤
      (∑ i, a i ^ 2) * ((∑ j, b j ^ 2) * ∑ j, u j ^ 2) := by
    rw [sum_mul]
    apply sum_le_sum
    intro i _
    have hpoint : |∑ j, K i j * u j| ≤ a i * ∑ j, b j * |u j| := by
      calc
        _ ≤ ∑ j, |K i j * u j| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, (a i * b j) * |u j| := by
          simp only [abs_mul]
          exact sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hK i j) (abs_nonneg _)
        _ = _ := by rw [mul_sum]; apply sum_congr rfl; intro j _; ring
    have hn : 0 ≤ a i * ∑ j, b j * |u j| :=
      mul_nonneg (ha i) (sum_nonneg fun j _ => mul_nonneg (hb j) (abs_nonneg _))
    have hsq := (sq_le_sq₀ (abs_nonneg _) hn).mpr hpoint
    rw [sq_abs, mul_pow] at hsq
    exact hsq.trans (mul_le_mul_of_nonneg_left hcs (sq_nonneg _))
  have hs := Real.sqrt_le_sqrt hsum
  rw [Real.sqrt_mul (sum_nonneg fun _ _ => sq_nonneg _),
    Real.sqrt_mul (sum_nonneg fun _ _ => sq_nonneg _)] at hs
  simpa only [norm₂_eq, mul_assoc] using hs

/-- Lemma 5.12: on the far part of a large row, the
output-weight monomial has degree exactly minus one half. -/
theorem far_output_power {p x d : ℝ} (hp : 0 < p) (hx : 0 < x)
    (hd : x / 2 < d) :
    x ^ (p - 1 / 2) * (1 + d) ^ (-p) ≤
      (2 : ℝ) ^ p * x ^ (-(1 / 2 : ℝ)) := by
  have hD : 0 < 1 + d := by linarith
  have hscale : (x / 2) ^ (-p) = (2 : ℝ) ^ p * x ^ (-p) := by
    rw [Real.div_rpow hx.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    simp only [div_eq_mul_inv, inv_inv]
    ring
  calc
    _ ≤ x ^ (p - 1 / 2) * (x / 2) ^ (-p) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_pos_of_pos hx _).le
      exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    _ = _ := by
      rw [hscale]
      rw [show x ^ (p - 1 / 2) * ((2 : ℝ) ^ p * x ^ (-p)) =
        (2 : ℝ) ^ p * (x ^ (p - 1 / 2) * x ^ (-p)) by ring,
        ← Real.rpow_add hx]
      congr 2
      ring

/-- Lemma 5.12: the tail Schur sum, uniformly in the
centre and cutoff, for distances larger than half the cutoff. -/
theorem far_shell_sum {p R : ℝ} (hp : 1 < p) (hR : 1 ≤ R)
    (N : ℕ+) (i : Fin (N : ℕ)) :
    (∑ j ∈ univ.filter (fun j => R / 2 < (Riesz1.cyclicIndexDistance N i j : ℝ)),
      (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-p)) ≤
      ((3 : ℝ) ^ p * (2 * (2 + 1 / (p - 1)))) * R ^ (1 - p) := by
  have hR0 : 0 < R := by linarith
  have hs := DerivativeCommutators.sum_row_scale_rpow_le N i hp hR
  calc
    _ ≤ ∑ j, (3 : ℝ) ^ p * (R + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-p) := by
      rw [sum_filter]
      apply sum_le_sum
      intro j _
      let d : ℝ := Riesz1.cyclicIndexDistance N i j
      have hd : 0 ≤ d := Nat.cast_nonneg _
      split_ifs with h
      · have hpow : ((R + d) / 3) ^ (-p) =
            (3 : ℝ) ^ p * (R + d) ^ (-p) := by
          rw [Real.div_rpow (by positivity) (by norm_num),
            Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
          simp only [div_eq_mul_inv, inv_inv]
          ring
        change (1 + d) ^ (-p) ≤ (3 : ℝ) ^ p * (R + d) ^ (-p)
        rw [← hpow]
        apply Real.rpow_le_rpow_of_nonpos (by positivity) (by dsimp [d] at *; linarith)
          (by linarith)
      · positivity
    _ = (3 : ℝ) ^ p * ∑ j, (R + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-p) :=
      (mul_sum _ _ _).symm
    _ ≤ (3 : ℝ) ^ p * ((2 * (2 + 1 / (p - 1))) * R ^ (1 - p)) := by gcongr
    _ = _ := by ring

/-- Internal scaled Cauchy–Schwarz estimate for
Lemma 5.12. -/
theorem internal_rank_one_scaled {ι : Type*} [Fintype ι]
    (K : ι → ι → ℝ) (a b u : ι → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hK : ∀ i j, |K i j| ≤ C * a i * b j) :
    norm₂ (fun i => ∑ j, K i j * u j) ≤
      C * (Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ j, b j ^ 2)) * norm₂ u := by
  have h := internal_rank_one K (fun i => C * a i) b u
    (fun i => mul_nonneg hC (ha i)) hb hK
  simp only [mul_pow, ← mul_sum, Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC] at h
  simpa only [mul_assoc] using h

/-- Lemma 5.12: the full harmonic radius sum. -/
theorem full_harmonic (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (i₀ : Fin (N : ℕ)) :
    (∑ i, (weightRadius N i i₀)⁻¹) ≤
      2 * (1 + 1 / Real.log 2) * Real.log (2 * (N : ℝ)) := by
  have hall : (univ.filter (fun i => weightRadius N i i₀ ≤ (N : ℝ))) = univ := by
    apply filter_true_of_mem
    intro i _
    have h := Riesz1.APG.cyclicIndexDistance_le_half (N := N) i i₀
    have : 1 + Riesz1.cyclicIndexDistance N i i₀ ≤ (N : ℕ) := by omega
    simpa only [weightRadius, Nat.cast_add, Nat.cast_one] using
      (show ((1 + Riesz1.cyclicIndexDistance N i i₀ : ℕ) : ℝ) ≤ (N : ℝ) by exact_mod_cast this)
  have h := sum_weightRadius_le_of_one N i₀ (R := (N : ℝ)) (by exact_mod_cast N.pos)
  simpa only [hall, Real.rpow_neg_one] using h

/-- Lemma 5.12: at most twice the radius many small rows. -/
theorem small_row_count (N : ℕ+) (i₀ : Fin (N : ℕ)) {R : ℝ} (hR : 1 ≤ R) :
    ((univ.filter (fun i => weightRadius N i i₀ < R)).card : ℝ) ≤ 2 * R := by
  have h := sum_weightRadius_le_range N i₀ (t := 0) hR
  simp only [neg_zero, Real.rpow_zero, sum_const, nsmul_eq_mul, mul_one, card_range] at h
  have hsub : univ.filter (fun i => weightRadius N i i₀ < R) ⊆
      univ.filter (fun i => weightRadius N i i₀ ≤ R) := by
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2.le⟩
  exact (Nat.cast_le.mpr (card_le_card hsub)).trans (h.trans (by
    gcongr
    exact Nat.floor_le (by linarith)))

/-- Lemma 5.12: the output-weight term on the second
region, bounded by two harmonic sums and weighted Cauchy–Schwarz. -/
theorem large_far_output {p : ℝ} (hp : 1 < p)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (i₀ : Fin (N : ℕ))
    (B : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    {Bstar : ℝ} (hB : 0 ≤ Bstar)
    (hdec : ∀ i j, |B i j| ≤ Bstar * (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-p))
    (R : ℝ) (v : Fin (N : ℕ) → ℝ) :
    let r := fun i => weightRadius N i i₀
    norm₂ (fun i => ∑ j, if R ≤ r i ∧ r i / 2 <
      (Riesz1.cyclicIndexDistance N i j : ℝ) then
      r i ^ (p - 1 / 2) * B i j * v j else 0) ≤
      ((2 : ℝ) ^ p * (2 * (1 + 1 / Real.log 2))) * Bstar *
        Real.log (2 * (N : ℝ)) * norm₂ (fun j => r j ^ (1 / 2 : ℝ) * v j) := by
  classical
  dsimp only
  let r := fun i => weightRadius N i i₀
  let K := fun i j => if R ≤ r i ∧ r i / 2 <
    (Riesz1.cyclicIndexDistance N i j : ℝ) then
    r i ^ (p - 1 / 2) * B i j / Real.sqrt (r j) else 0
  let w := fun i => (Real.sqrt (r i))⁻¹
  have hr i : 0 < r i := by linarith [one_le_weightRadius N i i₀]
  have hw i : 0 ≤ w i := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hK i j : |K i j| ≤ ((2 : ℝ) ^ p * Bstar) * w i * w j := by
    dsimp only [K]
    split_ifs with h
    · rw [abs_div, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (hr i) _),
        abs_of_pos (Real.sqrt_pos.mpr (hr j))]
      calc
        _ ≤ r i ^ (p - 1 / 2) *
          (Bstar * (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-p)) /
            Real.sqrt (r j) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hdec i j) (Real.rpow_pos_of_pos (hr i) _).le)
            (Real.sqrt_nonneg _)
        _ = Bstar * (r i ^ (p - 1 / 2) *
          (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-p)) /
            Real.sqrt (r j) := by ring
        _ ≤ Bstar * ((2 : ℝ) ^ p * r i ^ (-(1 / 2 : ℝ))) / Real.sqrt (r j) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (far_output_power (p := p) (by linarith) (hr i) h.2) hB) (Real.sqrt_nonneg _)
        _ = _ := by
          simp only [w, Real.rpow_neg (hr i).le, ← Real.sqrt_eq_rpow]
          ring
    · simp only [abs_zero]
      positivity
  have h := internal_rank_one_scaled K w w (fun j => Real.sqrt (r j) * v j)
    (by positivity) hw hw hK
  have heq i : (∑ j, K i j * (Real.sqrt (r j) * v j)) =
      ∑ j, if R ≤ r i ∧ r i / 2 < (Riesz1.cyclicIndexDistance N i j : ℝ)
      then r i ^ (p - 1 / 2) * B i j * v j else 0 := by
    apply sum_congr rfl
    intro j _
    dsimp only [K]
    split_ifs
    · field_simp [ne_of_gt (Real.sqrt_pos.mpr (hr j))]
    · simp
  simp_rw [heq, ← sq] at h
  rw [Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)] at h
  have hwsq : (∑ i, w i ^ 2) ≤ 2 * (1 + 1 / Real.log 2) * Real.log (2 * (N : ℝ)) := by
    simp only [w, inv_pow, Real.sq_sqrt (hr _).le]
    exact full_harmonic N hN i₀
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    _ ≤ _ := h
    _ ≤ ((2 : ℝ) ^ p * Bstar) *
        (2 * (1 + 1 / Real.log 2) * Real.log (2 * (N : ℝ))) *
        norm₂ (fun j => Real.sqrt (r j) * v j) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hwsq (by positivity)) (norm_nonneg _)
    _ = _ := by simp_rw [Real.sqrt_eq_rpow]; ring

/-- Internal tail Schur step of Lemma 5.12. -/
theorem internal_tail_schur {p R : ℝ} (hp : 1 < p) (hR : 1 ≤ R)
    (N : ℕ+) (B : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    {Bstar : ℝ} (hB : 0 ≤ Bstar)
    (hdec : ∀ i j, |B i j| ≤ Bstar * (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-p))
    (P : Fin (N : ℕ) → Fin (N : ℕ) → Prop)
    (ρ : Fin (N : ℕ) → ℝ) (hρ : ∀ i, 1 ≤ ρ i)
    (hP : ∀ i j, P i j → R ≤ ρ i ∧ ρ i / 2 < (Riesz1.cyclicIndexDistance N i j : ℝ))
    (u : Fin (N : ℕ) → ℝ) :
    norm₂ (fun i => ∑ j, if P i j then B i j * u j else 0) ≤
      ((3 : ℝ) ^ p * (2 * (2 + 1 / (p - 1)))) * Bstar * R ^ (1 - p) * norm₂ u := by
  classical
  let K := fun i j => if P i j then B i j else 0
  let H := ((3 : ℝ) ^ p * (2 * (2 + 1 / (p - 1)))) * Bstar * R ^ (1 - p)
  have hdom i j (L : ℝ)
      (hL : P i j → L / 2 < (Riesz1.cyclicIndexDistance N i j : ℝ)) :
      |K i j| ≤ Bstar *
      (if L / 2 < (Riesz1.cyclicIndexDistance N i j : ℝ) then
        (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-p) else 0) := by
    dsimp only [K]
    by_cases h : P i j
    · simp only [h, hL h, ↓reduceIte]
      exact hdec i j
    · simp only [h, ↓reduceIte, abs_zero]
      split_ifs <;> positivity
  have hrow i : ∑ j, |K i j| ≤ H := by
    by_cases hi : R ≤ ρ i
    · have hs : (∑ j, |K i j|) ≤
          ((3 : ℝ) ^ p * (2 * (2 + 1 / (p - 1)))) * Bstar * (ρ i) ^ (1 - p) := by
        refine (sum_le_sum fun j _ => hdom i j (ρ i) (fun h => (hP i j h).2)).trans ?_
        rw [← mul_sum, ← sum_filter]
        convert mul_le_mul_of_nonneg_left (far_shell_sum hp (hρ i) N i) hB using 1
        ring
      refine hs.trans ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow_of_nonpos (by linarith : 0 < R) hi (by linarith)
    · have hempty j : ¬ P i j := fun h => hi (hP i j h).1
      simp only [K, hempty, ↓reduceIte, abs_zero, sum_const_zero]
      dsimp [H]
      positivity
  have hcol j : ∑ i, |K i j| ≤ H := by
    refine (sum_le_sum fun i _ => hdom i j R (by
      intro h
      obtain ⟨h₁, h₂⟩ := hP i j h
      linarith)).trans ?_
    simp_rw [cyclicIndexDistance_comm' N _ j]
    rw [← mul_sum, ← sum_filter]
    convert mul_le_mul_of_nonneg_left (far_shell_sum hp hR N j) hB using 1
    ring
  have h := FiniteSchurBounds.sqrt_sum_sq_norm_le K u (by dsimp [H]; positivity) hrow hcol
  simp only [smul_eq_mul, Real.norm_eq_abs, sq_abs, ← norm₂_eq] at h
  convert h using 2
  funext i
  apply sum_congr rfl
  intro j _
  dsimp only [K]
  split_ifs <;> simp

/-- Lemma 5.12: the input-weight monomial on the
second region has small row and column tail sums. -/
theorem large_far_input {p R : ℝ} (hp : 1 < p) (hR : 1 ≤ R)
    (N : ℕ+) (i₀ : Fin (N : ℕ))
    (B : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    {Bstar : ℝ} (hB : 0 ≤ Bstar)
    (hdec : ∀ i j, |B i j| ≤ Bstar * (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-p))
    (v : Fin (N : ℕ) → ℝ) :
    let r := fun i => weightRadius N i i₀
    norm₂ (fun i => ∑ j, if R ≤ r i ∧ r i / 2 <
      (Riesz1.cyclicIndexDistance N i j : ℝ) then
      B i j * (r j ^ (p - 1 / 2) * v j) else 0) ≤
      ((3 : ℝ) ^ p * (2 * (2 + 1 / (p - 1)))) * Bstar * R ^ (1 - p) *
        norm₂ (fun j => r j ^ (p - 1 / 2) * v j) := by
  classical
  dsimp only
  have h := internal_tail_schur hp hR N B hB hdec
    (fun i j => R ≤ weightRadius N i i₀ ∧ weightRadius N i i₀ / 2 <
      (Riesz1.cyclicIndexDistance N i j : ℝ))
    (fun i => weightRadius N i i₀) (fun i => one_le_weightRadius N i i₀)
    (by intro i j h; exact h)
    (fun j => weightRadius N j i₀ ^ (p - 1 / 2) * v j)
  convert h using 2
  funext i
  apply sum_congr rfl
  intro j _
  split_ifs <;> rfl

/-- Lemma 5.12: the restricted harmonic sum and the
absorption of its logarithm by the positive power `4 - 2p = 2s`. -/
theorem small_harmonic {p : ℝ} (hp2 : p < 2) :
    ∃ H : ℝ, 0 < H ∧ ∀ (N : ℕ+) (i₀ : Fin (N : ℕ)) (R : ℝ), 1 ≤ R →
      (∑ j ∈ univ.filter (fun j => weightRadius N j i₀ ≤ 4 * R),
        (weightRadius N j i₀)⁻¹) ≤ H * R ^ (4 - 2 * p) := by
  let q := 4 - 2 * p
  have hq : 0 < q := by dsimp [q]; linarith
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(2 * (1 + 1 / Real.log 2)) * (8 : ℝ) ^ q / q, by positivity, ?_⟩
  intro N i₀ R hR
  have hR0 : 0 < R := by linarith
  have hs := sum_weightRadius_le_of_one N i₀ (R := 4 * R) (by linarith)
  simp only [Real.rpow_neg_one] at hs
  refine hs.trans ?_
  calc
    _ ≤ (2 * (1 + 1 / Real.log 2)) * ((8 * R) ^ q / q) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      convert Real.log_le_rpow_div (x := 8 * R) (by positivity) hq using 1; ring_nf
    _ = _ := by rw [Real.mul_rpow (by norm_num) hR0.le]; ring

/-- Internal power bookkeeping for the small/near region of
Lemma 5.12. -/
theorem small_near_scaling {p R H : ℝ} (hR : 0 < R) (hH : 0 ≤ H) :
    (4 * R) ^ (p - 1 / 2) *
      (Real.sqrt (2 * R) * Real.sqrt (H * R ^ (4 - 2 * p))) =
      ((4 : ℝ) ^ (p - 1 / 2) * Real.sqrt (2 * H)) * R ^ 2 := by
  rw [Real.mul_rpow (by norm_num) hR.le,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_mul hH]
  simp only [Real.sqrt_eq_rpow, ← Real.rpow_mul hR.le]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hH]
  calc
    _ = ((4 : ℝ) ^ (p - 1 / 2) * ((2 : ℝ) ^ (1 / 2 : ℝ) * H ^ (1 / 2 : ℝ))) *
      ((R ^ (p - 1 / 2) * R ^ (1 / 2 : ℝ)) * R ^ ((4 - 2 * p) * (1 / 2))) := by ring
    _ = _ := by
      rw [← Real.rpow_add hR, ← Real.rpow_add hR]
      rw [show p - 1 / 2 + 1 / 2 + (4 - 2 * p) * (1 / 2) = 2 by ring,
        Real.rpow_two]

/-- Lemma 5.12: the third region, using its small row
count, its restricted harmonic sum, and weighted Cauchy–Schwarz. -/
theorem small_near {p : ℝ} (hp : 1 < p) (hp2 : p < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (i₀ : Fin (N : ℕ))
      (B : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
      (Bstar : ℝ), 0 ≤ Bstar →
      (∀ i j, |B i j| ≤ Bstar * (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-p)) →
      ∀ R : ℝ, 1 ≤ R → ∀ v : Fin (N : ℕ) → ℝ,
      let r := fun i => weightRadius N i i₀
      norm₂ (fun i => ∑ j, if r i < R ∧ r j ≤ 4 * R then
        (r i ^ (p - 1 / 2) - r j ^ (p - 1 / 2)) * B i j * v j else 0) ≤
        C * Bstar * R ^ 2 * norm₂ (fun j => r j ^ (1 / 2 : ℝ) * v j) := by
  classical
  obtain ⟨H, hH, hh⟩ := small_harmonic hp2
  refine ⟨(4 : ℝ) ^ (p - 1 / 2) * Real.sqrt (2 * H), by positivity, ?_⟩
  intro N i₀ B Bstar hB hdec R hR v
  dsimp only
  let r := fun i => weightRadius N i i₀
  let a := fun i => if r i < R then (1 : ℝ) else 0
  let b := fun j => if r j ≤ 4 * R then (Real.sqrt (r j))⁻¹ else 0
  let K := fun i j => if r i < R ∧ r j ≤ 4 * R then
    (r i ^ (p - 1 / 2) - r j ^ (p - 1 / 2)) * B i j / Real.sqrt (r j) else 0
  have hr i : 0 < r i := by linarith [one_le_weightRadius N i i₀]
  have hR0 : 0 < R := by linarith
  have ha i : 0 ≤ a i := by dsimp [a]; split_ifs <;> norm_num
  have hb j : 0 ≤ b j := by dsimp [b]; split_ifs <;> positivity
  have hK i j : |K i j| ≤ (Bstar * (4 * R) ^ (p - 1 / 2)) * a i * b j := by
    dsimp only [K, a, b]
    by_cases hi : r i < R
    · by_cases hj : r j ≤ 4 * R
      · simp only [hi, hj, and_self, ↓reduceIte, mul_one]
        have hd : (1 : ℝ) ≤ 1 + (Riesz1.cyclicIndexDistance N i j : ℝ) := by
          have := Nat.cast_nonneg (α := ℝ) (Riesz1.cyclicIndexDistance N i j)
          linarith
        have hB' : |B i j| ≤ Bstar := (hdec i j).trans (by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left
            (Real.rpow_le_one_of_one_le_of_nonpos hd (by linarith : -p ≤ 0)) hB)
        have hi' := Real.rpow_le_rpow (hr i).le (by linarith : r i ≤ 4 * R)
          (by linarith : 0 ≤ p - 1 / 2)
        have hj' := Real.rpow_le_rpow (hr j).le hj (by linarith : 0 ≤ p - 1 / 2)
        have hdiff : |r i ^ (p - 1 / 2) - r j ^ (p - 1 / 2)| ≤
            (4 * R) ^ (p - 1 / 2) := by
          rw [abs_sub_le_iff]
          constructor <;> linarith [Real.rpow_pos_of_pos (hr i) (p - 1 / 2),
            Real.rpow_pos_of_pos (hr j) (p - 1 / 2)]
        rw [abs_div, abs_mul, abs_of_pos (Real.sqrt_pos.mpr (hr j)), ← div_eq_mul_inv]
        apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
        nlinarith [mul_le_mul hdiff hB' (abs_nonneg _) (by positivity)]
      · simp [hi, hj]
    · simp [hi]
  have h := internal_rank_one_scaled K a b (fun j => Real.sqrt (r j) * v j)
    (by positivity) ha hb hK
  have hasq : (∑ i, a i ^ 2) ≤ 2 * R := by
    simpa only [a, ite_pow, one_pow, zero_pow (by norm_num : 2 ≠ 0),
      ← sum_filter, sum_const, nsmul_eq_mul, mul_one] using small_row_count N i₀ hR
  have hbsq : (∑ j, b j ^ 2) ≤ H * R ^ (4 - 2 * p) := by
    simpa only [b, ite_pow, inv_pow, Real.sq_sqrt (hr _).le,
      zero_pow (by norm_num : 2 ≠ 0), ← sum_filter] using hh N i₀ R hR
  have heq i : (∑ j, K i j * (Real.sqrt (r j) * v j)) =
      ∑ j, if r i < R ∧ r j ≤ 4 * R then
        (r i ^ (p - 1 / 2) - r j ^ (p - 1 / 2)) * B i j * v j else 0 := by
    apply sum_congr rfl
    intro j _
    dsimp only [K]
    split_ifs
    · field_simp [ne_of_gt (Real.sqrt_pos.mpr (hr j))]
    · simp
  simp_rw [heq] at h
  calc
    _ ≤ _ := h
    _ ≤ (Bstar * (4 * R) ^ (p - 1 / 2)) *
        (Real.sqrt (2 * R) * Real.sqrt (H * R ^ (4 - 2 * p))) *
        norm₂ (fun j => Real.sqrt (r j) * v j) := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul (Real.sqrt_le_sqrt hasq) (Real.sqrt_le_sqrt hbsq)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [mul_assoc Bstar, small_near_scaling hR0 hH.le]
      simp_rw [Real.sqrt_eq_rpow]
      ring

/-- Lemma 5.12: the small/far normalized entry is
bounded by an inverse input radius, using `d ≥ r_j - r_i`. -/
theorem small_far_power {p x y d : ℝ} (hp : 1 < p)
    (hx : 0 < x) (hy : 0 < y) (hxy : x < y / 4) (hd : |x - y| ≤ d) :
    |x ^ (p - 1 / 2) - y ^ (p - 1 / 2)| * (1 + d) ^ (-p) / Real.sqrt y ≤
      (2 : ℝ) ^ p * y⁻¹ := by
  have hle : x ≤ y := by linarith
  have hdiff : |x ^ (p - 1 / 2) - y ^ (p - 1 / 2)| ≤ y ^ (p - 1 / 2) := by
    rw [abs_sub_comm, abs_of_nonneg
      (sub_nonneg.mpr (Real.rpow_le_rpow hx.le hle (by linarith)))]
    linarith [Real.rpow_pos_of_pos hx (p - 1 / 2)]
  have hdist : y / 2 < d := by
    rw [abs_sub_le_iff] at hd
    linarith [hd.2]
  have hD : 0 < 1 + d := by linarith
  calc
    _ ≤ y ^ (p - 1 / 2) * (1 + d) ^ (-p) / Real.sqrt y :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hdiff (Real.rpow_pos_of_pos hD _).le) (Real.sqrt_nonneg _)
    _ ≤ ((2 : ℝ) ^ p * y ^ (-(1 / 2 : ℝ))) / Real.sqrt y :=
      div_le_div_of_nonneg_right
        (far_output_power (p := p) (by linarith) hy hdist) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.rpow_neg hy.le, ← Real.sqrt_eq_rpow]
      rw [div_eq_mul_inv, mul_assoc, ← sq, inv_pow, Real.sq_sqrt hy.le]

/-- Lemma 5.12: the fourth region, by the square
summable inverse-radius kernel and the small output-row count. -/
theorem small_far {p R : ℝ} (hp : 1 < p) (hR : 1 ≤ R)
    (N : ℕ+) (i₀ : Fin (N : ℕ))
    (B : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    {Bstar : ℝ} (hB : 0 ≤ Bstar)
    (hdec : ∀ i j, |B i j| ≤ Bstar * (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-p))
    (v : Fin (N : ℕ) → ℝ) :
    let r := fun i => weightRadius N i i₀
    norm₂ (fun i => ∑ j, if r i < R ∧ 4 * R < r j then
      (r i ^ (p - 1 / 2) - r j ^ (p - 1 / 2)) * B i j * v j else 0) ≤
      ((2 : ℝ) ^ p * Real.sqrt 8) * Bstar *
        norm₂ (fun j => r j ^ (1 / 2 : ℝ) * v j) := by
  classical
  dsimp only
  let r := fun i => weightRadius N i i₀
  let a := fun i => if r i < R then (1 : ℝ) else 0
  let b := fun j => if 4 * R < r j then (r j)⁻¹ else 0
  let K := fun i j => if r i < R ∧ 4 * R < r j then
    (r i ^ (p - 1 / 2) - r j ^ (p - 1 / 2)) * B i j / Real.sqrt (r j) else 0
  have hr i : 0 < r i := by linarith [one_le_weightRadius N i i₀]
  have hR0 : 0 < R := by linarith
  have ha i : 0 ≤ a i := by dsimp [a]; split_ifs <;> norm_num
  have hb j : 0 ≤ b j := by
    dsimp only [b]
    split_ifs
    · exact inv_nonneg.mpr (hr j).le
    · exact le_rfl
  have hK i j : |K i j| ≤ ((2 : ℝ) ^ p * Bstar) * a i * b j := by
    dsimp only [K, a, b]
    by_cases hi : r i < R
    · by_cases hj : 4 * R < r j
      · simp only [hi, hj, and_self, ↓reduceIte, mul_one]
        rw [abs_div, abs_mul, abs_of_pos (Real.sqrt_pos.mpr (hr j))]
        have hD : 0 < 1 + (Riesz1.cyclicIndexDistance N i j : ℝ) := by positivity
        calc
          _ ≤ |r i ^ (p - 1 / 2) - r j ^ (p - 1 / 2)| *
              (Bstar * (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-p)) /
              Real.sqrt (r j) := by gcongr; exact hdec i j
          _ = Bstar * (|r i ^ (p - 1 / 2) - r j ^ (p - 1 / 2)| *
              (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-p) / Real.sqrt (r j)) := by ring
          _ ≤ Bstar * ((2 : ℝ) ^ p * (r j)⁻¹) :=
            mul_le_mul_of_nonneg_left (small_far_power hp (hr i) (hr j) (by linarith)
              (DerivativeCommutators.weightRadius_lipschitz N i₀ i j)) hB
          _ = _ := by ring
      · simp [hi, hj]
    · simp [hi]
  have h := internal_rank_one_scaled K a b (fun j => Real.sqrt (r j) * v j)
    (by positivity) ha hb hK
  have hasq : (∑ i, a i ^ 2) ≤ 2 * R := by
    simpa only [a, ite_pow, one_pow, zero_pow (by norm_num : 2 ≠ 0),
      ← sum_filter, sum_const, nsmul_eq_mul, mul_one] using small_row_count N i₀ hR
  have hbsq : (∑ j, b j ^ 2) ≤ 4 * R⁻¹ := by
    have hs := sum_weightRadius_tail_le N i₀ (t := 2) (by norm_num) hR
    norm_num only [show (1 : ℝ) - 2 = -1 by norm_num, Real.rpow_neg_one,
      show (2 : ℝ) - 1 = 1 by norm_num, div_one] at hs
    calc
      _ = ∑ j ∈ univ.filter (fun j => 4 * R < r j), (r j) ^ (-(2 : ℝ)) := by
        simp only [b, ite_pow, zero_pow (by norm_num : 2 ≠ 0), sum_filter,
          Real.rpow_neg (hr _).le, Real.rpow_two, inv_pow]
      _ ≤ ∑ j ∈ univ.filter (fun j => R ≤ r j), (r j) ^ (-(2 : ℝ)) := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro j hj
          exact mem_filter.mpr ⟨mem_univ _, by linarith [(mem_filter.mp hj).2]⟩
        · intro j _ _
          exact (Real.rpow_pos_of_pos (hr j) _).le
      _ ≤ _ := hs
  have heq i : (∑ j, K i j * (Real.sqrt (r j) * v j)) =
      ∑ j, if r i < R ∧ 4 * R < r j then
        (r i ^ (p - 1 / 2) - r j ^ (p - 1 / 2)) * B i j * v j else 0 := by
    apply sum_congr rfl
    intro j _
    dsimp only [K]
    split_ifs
    · field_simp [ne_of_gt (Real.sqrt_pos.mpr (hr j))]
    · simp
  simp_rw [heq] at h
  calc
    _ ≤ _ := h
    _ ≤ ((2 : ℝ) ^ p * Bstar) *
        (Real.sqrt (2 * R) * Real.sqrt (4 * R⁻¹)) *
        norm₂ (fun j => Real.sqrt (r j) * v j) := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul (Real.sqrt_le_sqrt hasq) (Real.sqrt_le_sqrt hbsq)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [← Real.sqrt_mul (by positivity : 0 ≤ 2 * R),
        show 2 * R * (4 * R⁻¹) = 8 by field_simp; norm_num]
      simp_rw [Real.sqrt_eq_rpow]
      ring

/-- Internal triangle inequality for the assembly of the four regions in
Lemma 5.12. -/
theorem internal_norm₂_add {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    norm₂ (u + v) ≤ norm₂ u + norm₂ v :=
  norm_add_le (WithLp.toLp 2 u) (WithLp.toLp 2 v)

/-- Internal subtraction inequality for the two monomials in the
second region of Lemma 5.12. -/
theorem internal_norm₂_sub {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    norm₂ (u - v) ≤ norm₂ u + norm₂ v :=
  norm_sub_le (WithLp.toLp 2 u) (WithLp.toLp 2 v)

/-- Lemma 5.12, equation (5.41): add the four
restricted-operator estimates in the written order, retaining the literal
quadratic cutoff remainder. -/
theorem endpoint_estimate (p : ℝ) (hp : 1 < p) (hp2 : p < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (_hN : 2 ≤ (N : ℕ))
      (i₀ : Fin (N : ℕ)) (B : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
      (Bstar : ℝ), 0 < Bstar →
      (∀ i j, |B i j| ≤ Bstar * (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-p)) →
      ∀ R : ℝ, 1 ≤ R → ∀ v : Fin (N : ℕ) → ℝ,
      norm₂ (fun i => weightRadius N i i₀ ^ (p - 1 / 2) * (B *ᵥ v) i -
        (B *ᵥ (fun j => weightRadius N j i₀ ^ (p - 1 / 2) * v j)) i) ≤
        C * Bstar * R ^ (1 - p) *
          norm₂ (fun j => weightRadius N j i₀ ^ (p - 1 / 2) * v j) +
        C * Bstar * (R ^ 2 + Real.log (2 * (N : ℝ))) *
          norm₂ (fun j => weightRadius N j i₀ ^ (1 / 2 : ℝ) * v j) := by
  classical
  obtain ⟨C₁, hC₁, h₁⟩ := large_near hp hp2
  obtain ⟨C₃, hC₃, h₃⟩ := small_near hp hp2
  let A := (2 : ℝ) ^ p * (2 * (1 + 1 / Real.log 2))
  let D := (3 : ℝ) ^ p * (2 * (2 + 1 / (p - 1)))
  let F := (2 : ℝ) ^ p * Real.sqrt 8
  let C := C₁ + D + A + C₃ + F + 1
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 0 < A := by dsimp [A]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hF : 0 < F := by dsimp [F]; positivity
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro N hN i₀ B Bstar hB hdec R hR v
  let r := fun i => weightRadius N i i₀
  let d := fun i j => (Riesz1.cyclicIndexDistance N i j : ℝ)
  let f₁ := fun i => ∑ j, if R ≤ r i ∧ d i j ≤ r i / 2 then
    (r i ^ (p - 1 / 2) - r j ^ (p - 1 / 2)) * B i j * v j else 0
  let f₂o := fun i => ∑ j, if R ≤ r i ∧ r i / 2 < d i j then
    r i ^ (p - 1 / 2) * B i j * v j else 0
  let f₂i := fun i => ∑ j, if R ≤ r i ∧ r i / 2 < d i j then
    B i j * (r j ^ (p - 1 / 2) * v j) else 0
  let f₃ := fun i => ∑ j, if r i < R ∧ r j ≤ 4 * R then
    (r i ^ (p - 1 / 2) - r j ^ (p - 1 / 2)) * B i j * v j else 0
  let f₄ := fun i => ∑ j, if r i < R ∧ 4 * R < r j then
    (r i ^ (p - 1 / 2) - r j ^ (p - 1 / 2)) * B i j * v j else 0
  let X := norm₂ (fun j => r j ^ (p - 1 / 2) * v j)
  let Y := norm₂ (fun j => r j ^ (1 / 2 : ℝ) * v j)
  have hX : 0 ≤ X := norm_nonneg _
  have hY : 0 ≤ Y := norm_nonneg _
  have hb₁ : norm₂ f₁ ≤ C₁ * Bstar * R ^ (1 - p) * X := h₁ N i₀ B Bstar hB.le hdec R hR v
  have hb₂o : norm₂ f₂o ≤ A * Bstar * Real.log (2 * (N : ℝ)) * Y :=
    large_far_output hp N hN i₀ B hB.le hdec R v
  have hb₂i : norm₂ f₂i ≤ D * Bstar * R ^ (1 - p) * X :=
    large_far_input hp hR N i₀ B hB.le hdec v
  have hb₃ : norm₂ f₃ ≤ C₃ * Bstar * R ^ 2 * Y := h₃ N i₀ B Bstar hB.le hdec R hR v
  have hb₄ : norm₂ f₄ ≤ F * Bstar * Y := small_far hp hR N i₀ B hB.le hdec v
  have heq : (fun i => r i ^ (p - 1 / 2) * (B *ᵥ v) i -
      (B *ᵥ (fun j => r j ^ (p - 1 / 2) * v j)) i) =
      ((f₁ + (f₂o - f₂i)) + f₃) + f₄ := by
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, f₁, f₂o, f₂i, f₃, f₄,
      Matrix.mulVec, dotProduct, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    by_cases hi : R ≤ r i
    · by_cases hj : d i j ≤ r i / 2
      · simp only [hi, hj, not_lt.mpr hi, not_lt.mpr hj, and_self, and_false,
          false_and, ↓reduceIte]
        ring
      · simp only [hi, hj, lt_of_not_ge hj, not_lt.mpr hi, and_self, and_false,
          false_and, ↓reduceIte]
        ring
    · by_cases hj : r j ≤ 4 * R
      · simp only [hi, hj, lt_of_not_ge hi, not_lt.mpr hj, true_and, false_and, ↓reduceIte]
        ring
      · simp only [hi, hj, lt_of_not_ge hi, lt_of_not_ge hj, and_self, and_false,
          false_and, ↓reduceIte]
        ring
  have htri : norm₂ (fun i => r i ^ (p - 1 / 2) * (B *ᵥ v) i -
      (B *ᵥ (fun j => r j ^ (p - 1 / 2) * v j)) i) ≤
      norm₂ f₁ + (norm₂ f₂o + norm₂ f₂i) + norm₂ f₃ + norm₂ f₄ := by
    rw [heq]
    linarith [internal_norm₂_add (f₁ + (f₂o - f₂i) + f₃) f₄,
      internal_norm₂_add (f₁ + (f₂o - f₂i)) f₃,
      internal_norm₂_add f₁ (f₂o - f₂i), internal_norm₂_sub f₂o f₂i]
  have hR2 : 1 ≤ R ^ 2 := by nlinarith
  have hLN : 0 ≤ Real.log (2 * (N : ℝ)) := by
    apply Real.log_nonneg
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hcoef : A * Real.log (2 * (N : ℝ)) + C₃ * R ^ 2 + F ≤
      C * (R ^ 2 + Real.log (2 * (N : ℝ))) := by
    have hCA : 0 ≤ C - A := by dsimp [C]; linarith
    have hCC : 0 ≤ C - C₃ - F := by dsimp [C]; linarith
    nlinarith [mul_nonneg hCA hLN, mul_nonneg hCC (sq_nonneg R),
      mul_nonneg hF.le (sub_nonneg.mpr hR2)]
  have hmain : (C₁ + D) * Bstar * R ^ (1 - p) * X ≤ C * Bstar * R ^ (1 - p) * X := by
    apply mul_le_mul_of_nonneg_right _ hX
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ hB.le
    dsimp [C]
    linarith
  have herr := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef hB.le) hY
  change norm₂ (fun i => r i ^ (p - 1 / 2) * (B *ᵥ v) i -
    (B *ᵥ (fun j => r j ^ (p - 1 / 2) * v j)) i) ≤
    C * Bstar * R ^ (1 - p) * X + C * Bstar * (R ^ 2 + Real.log (2 * (N : ℝ))) * Y
  linarith

end Riesz2.GlobalEndpointRegions
