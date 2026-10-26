/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.InitialDecayPart2
public import Riesz2.ToMathlib.BoundedMatrixModes
public import Riesz2.ToMathlib.FiniteSchurBounds

/-!
# Optimal short-range point-source decay

The weighted estimate is paired across a component cutoff. Long jumps use
the matrix entry bound. Short jumps crossing the cutoff are far from both
sources. This proves the point-source decay of Proposition 4.5.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal

namespace Riesz2.OptimalDecay.Internal

open ComponentGeometryBounds InitialDecay

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The elementary weighted Cauchy–Schwarz inequality used at both sources. -/
theorem sum_le_weighted (g : ComponentGeometry ι) (i₀ : ι) (a : ℝ)
    (ha : 1 / 2 < a) (b : ι → ℝ) (_hb : ∀ i, 0 ≤ b i) :
    ∑ i, b i ≤ Real.sqrt (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(2 * a))) *
      Real.sqrt (∑ i, (distortionWeight g i₀ a i * b i) ^ 2) := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun i => distortionWeight g i₀ (-a) i)
    (fun i => distortionWeight g i₀ a i * b i)
  have he (i : ι) : distortionWeight g i₀ (-a) i *
      (distortionWeight g i₀ a i * b i) = b i := by
    rw [distortionWeight_neg]
    field_simp [(distortionWeight_pos g i₀ a i).ne']
  simp_rw [he] at hcs
  apply hcs.trans
  gcongr
  have hh := sum_radius_sq_le g i₀ (show -a < -(1 / 2) by linarith)
  simpa only [distortionWeight, neg_mul, mul_neg, neg_neg] using hh

omit [DecidableEq ι] in
/-- Bilinear Schur estimate on the inherited line/cycle geometry. -/
theorem kernel_bilinear (g : ComponentGeometry ι) (s : ℝ) (hs : 1 < s)
    (u v : ι → ℝ) (_hu : ∀ i, 0 ≤ u i) (_hv : ∀ i, 0 ≤ v i) :
    (∑ i, ∑ j, (1 + componentDistance g i j) ^ (-s) * u i * v j) ≤
      (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s)) *
        Real.sqrt (∑ i, u i ^ 2) * Real.sqrt (∑ i, v i ^ 2) := by
  let K := fun i j => (1 + componentDistance g i j) ^ (-s)
  let S := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hK (i j : ι) : 0 ≤ K i j := by
    dsimp [K]; exact Real.rpow_nonneg (by linarith [nonneg g i j]) _
  have hr (i : ι) : ∑ j, |K i j| ≤ S := by
    simp_rw [abs_of_nonneg (hK i _)]
    exact sum_power_le g i hs
  have hc (j : ι) : ∑ i, |K i j| ≤ S := by
    simpa only [K, symm g] using hr j
  have hh := FiniteSchurBounds.sqrt_sum_sq_norm_le K v hS hr hc
  simp only [Real.norm_eq_abs, sq_abs] at hh
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ u (fun i => ∑ j, K i j * v j)
  calc
    _ = ∑ i, u i * ∑ j, K i j * v j := by
      simp only [Finset.mul_sum]; apply Finset.sum_congr rfl
      intro i _; apply Finset.sum_congr rfl; intro j _; ring
    _ ≤ Real.sqrt (∑ i, u i ^ 2) * Real.sqrt (∑ i, (∑ j, K i j * v j) ^ 2) := hcs
    _ ≤ Real.sqrt (∑ i, u i ^ 2) * (S * Real.sqrt (∑ i, v i ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg _)
    _ = _ := by ring

omit [Fintype ι] [DecidableEq ι] in
/-- A cutoff crossing of length less than R/6 lies far from both sources. -/
theorem crossing_radii (g : ComponentGeometry ι) (i₀ j i k : ι)
    (R : ℝ) (hR : componentDistance g j i₀ = R)
    (hcross : (componentDistance g i i₀ ≤ R / 2) ≠
      (componentDistance g k i₀ ≤ R / 2))
    (hnear : componentDistance g i k < R / 6) :
    R / 3 ≤ componentDistance g i i₀ ∧ R / 3 ≤ componentDistance g k j := by
  have h₁ := triangle g k i i₀
  have h₂ := triangle g i k i₀
  have h₃ := triangle g j k i₀
  rw [symm g k i] at h₁
  rw [hR, symm g j k] at h₃
  by_cases hi : componentDistance g i i₀ ≤ R / 2
  · have hk : ¬componentDistance g k i₀ ≤ R / 2 := fun hk => hcross (propext ⟨fun _ => hk, fun _ => hi⟩)
    constructor <;> linarith [not_le.mp hk]
  · have hk : componentDistance g k i₀ ≤ R / 2 := by
      by_contra hk
      exact hcross (propext ⟨fun h => False.elim (hi h), fun h => False.elim (hk h)⟩)
    constructor <;> linarith [not_le.mp hi]

/-- Inverse powers at a fixed fraction of R, with positive bases throughout. -/
theorem inverse_power_fraction (a R x : ℝ) (ha : 0 ≤ a) (hR : 1 ≤ R)
    (hx : R / 6 ≤ x) :
    (1 + x) ^ (-a) ≤ 6 ^ a * R ^ (-a) := by
  have hR0 : 0 < R := by linarith
  calc
    _ ≤ (R / 6) ^ (-a) := Real.rpow_le_rpow_of_nonpos (by positivity)
      (by linarith) (by linarith)
    _ = _ := by
      rw [Real.div_rpow hR0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 6)]
      simp only [div_inv_eq_mul, mul_comm]

omit [DecidableEq ι] in
/-- Cutoff matrix estimate. The squared weighted decay is sufficient when
2a ≥ s. Its constant is independent of the cardinality and ambient diameter. -/
theorem cutoff_bilinear (g : ComponentGeometry ι) (i₀ j : ι) (s a R : ℝ)
    (hs : 1 < s) (ha : 1 / 2 < a) (has : s ≤ 2 * a)
    (hR : 1 ≤ R) (hRdist : componentDistance g j i₀ = R)
    (u v : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) :
    let σ := fun i => if componentDistance g i i₀ ≤ R / 2 then (1 : ℝ) else 0
    (∑ i, ∑ k, |σ i - σ k| * (1 + componentDistance g i k) ^ (-s) * u i * v k) ≤
      (6 ^ s * (2 * ∑' l : ℕ, (1 + (l : ℝ)) ^ (-(2 * a))) +
        6 ^ (2 * a) * (2 * ∑' l : ℕ, (1 + (l : ℝ)) ^ (-s))) * R ^ (-s) *
      Real.sqrt (∑ i, (distortionWeight g i₀ a i * u i) ^ 2) *
      Real.sqrt (∑ k, (distortionWeight g j a k * v k) ^ 2) := by
  intro σ
  let U := fun i => distortionWeight g i₀ a i * u i
  let V := fun k => distortionWeight g j a k * v k
  have hU (i : ι) : 0 ≤ U i := mul_nonneg (distortionWeight_pos g i₀ a i).le (hu i)
  have hV (k : ι) : 0 ≤ V k := mul_nonneg (distortionWeight_pos g j a k).le (hv k)
  have hterm (i k : ι) :
      |σ i - σ k| * (1 + componentDistance g i k) ^ (-s) * u i * v k ≤
      6 ^ s * R ^ (-s) * (u i * v k) +
        6 ^ (2 * a) * R ^ (-s) * (1 + componentDistance g i k) ^ (-s) * U i * V k := by
    have hki : 0 ≤ (1 + componentDistance g i k) ^ (-s) :=
      Real.rpow_nonneg (by linarith [nonneg g i k]) _
    have hu0 := hu i
    have hv0 := hv k
    have hU0 := hU i
    have hV0 := hV k
    by_cases he : (componentDistance g i i₀ ≤ R / 2) = (componentDistance g k i₀ ≤ R / 2)
    · have hσ : σ i = σ k := by simp only [σ, he]
      rw [hσ, sub_self, abs_zero, zero_mul, zero_mul, zero_mul]
      positivity
    have habs : |σ i - σ k| = 1 := by
      by_cases hi : componentDistance g i i₀ ≤ R / 2
      · have hk : ¬componentDistance g k i₀ ≤ R / 2 := fun hk => he (propext ⟨fun _ => hk, fun _ => hi⟩)
        simp [σ, hi, hk]
      · have hk : componentDistance g k i₀ ≤ R / 2 := by
          by_contra hk
          exact he (propext ⟨fun h => False.elim (hi h), fun h => False.elim (hk h)⟩)
        simp [σ, hi, hk]
    rw [habs, one_mul]
    by_cases hfar : R / 6 ≤ componentDistance g i k
    · have hh := inverse_power_fraction s R (componentDistance g i k) (by linarith) hR hfar
      have hh' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (hu i)) (hv k)
      have hn : 0 ≤ 6 ^ (2 * a) * R ^ (-s) * (1 + componentDistance g i k) ^ (-s) * U i * V k := by positivity
      exact hh'.trans (by nlinarith only [hn])
    · obtain ⟨hi, hk⟩ := crossing_radii g i₀ j i k R hRdist he (not_le.mp hfar)
      have hi' := inverse_power_fraction a R (componentDistance g i i₀) (by linarith) hR (by linarith)
      have hk' := inverse_power_fraction a R (componentDistance g k j) (by linarith) hR (by linarith)
      have heU : u i = (1 + componentDistance g i i₀) ^ (-a) * U i := by
        dsimp [U, distortionWeight]
        rw [Real.rpow_neg (by linarith [nonneg g i i₀])]
        field_simp [(Real.rpow_pos_of_pos (show 0 < 1 + componentDistance g i i₀ by linarith [nonneg g i i₀]) a).ne']
      have heV : v k = (1 + componentDistance g k j) ^ (-a) * V k := by
        dsimp [V, distortionWeight]
        rw [Real.rpow_neg (by linarith [nonneg g k j])]
        field_simp [(Real.rpow_pos_of_pos (show 0 < 1 + componentDistance g k j by linarith [nonneg g k j]) a).ne']
      have hp : (6 ^ a * R ^ (-a)) * (6 ^ a * R ^ (-a)) ≤ 6 ^ (2 * a) * R ^ (-s) := by
        calc
          _ = 6 ^ (2 * a) * R ^ (-(2 * a)) := by
            rw [show 2 * a = a + a by ring, Real.rpow_add (by norm_num),
              neg_add, Real.rpow_add (by linarith)]
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hR (by linarith)) (by positivity)
      have hprod : u i * v k ≤ (6 ^ (2 * a) * R ^ (-s)) * U i * V k := by
        calc
          _ = ((1 + componentDistance g i i₀) ^ (-a) *
              (1 + componentDistance g k j) ^ (-a)) * U i * V k := by conv_lhs => rw [heU, heV]
                                                                      ring
          _ ≤ ((6 ^ a * R ^ (-a)) * (6 ^ a * R ^ (-a))) * U i * V k := by
            apply mul_le_mul_of_nonneg_right _ hV0
            apply mul_le_mul_of_nonneg_right _ hU0
            exact mul_le_mul hi' hk' (Real.rpow_nonneg (by linarith [nonneg g k j]) _) (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp hU0) hV0
      have hm := mul_le_mul_of_nonneg_left hprod hki
      have hn : 0 ≤ 6 ^ s * R ^ (-s) * (u i * v k) := by positivity
      nlinarith only [hm, hn]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hterm i k
  simp only [Finset.sum_add_distrib] at hsum
  have hu1 := sum_le_weighted g i₀ a ha u hu
  have hv1 := sum_le_weighted g j a ha v hv
  have hbil := kernel_bilinear g s hs U V hU hV
  have hS : 0 ≤ 2 * ∑' l : ℕ, (1 + (l : ℝ)) ^ (-(2 * a)) := by positivity
  have hfar : (∑ i, ∑ k, 6 ^ s * R ^ (-s) * (u i * v k)) ≤
      6 ^ s * R ^ (-s) * (2 * ∑' l : ℕ, (1 + (l : ℝ)) ^ (-(2 * a))) *
        Real.sqrt (∑ i, U i ^ 2) * Real.sqrt (∑ k, V k ^ 2) := by
    have hh := mul_le_mul hu1 hv1 (Finset.sum_nonneg fun k _ => hv k)
      (by positivity : 0 ≤ Real.sqrt (2 * ∑' l : ℕ, (1 + (l : ℝ)) ^ (-(2 * a))) *
        Real.sqrt (∑ i, (distortionWeight g i₀ a i * u i) ^ 2))
    have hsq := Real.sq_sqrt hS
    calc
      _ = (6 ^ s * R ^ (-s)) * ((∑ i, u i) * ∑ k, v k) := by rw [Finset.sum_mul]; simp_rw [Finset.mul_sum]
      _ ≤ (6 ^ s * R ^ (-s)) *
          ((Real.sqrt (2 * ∑' l : ℕ, (1 + (l : ℝ)) ^ (-(2 * a))) * Real.sqrt (∑ i, U i ^ 2)) *
          (Real.sqrt (2 * ∑' l : ℕ, (1 + (l : ℝ)) ^ (-(2 * a))) * Real.sqrt (∑ k, V k ^ 2))) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by
        calc
          _ = (6 ^ s * R ^ (-s)) *
              (Real.sqrt (2 * ∑' l : ℕ, (1 + (l : ℝ)) ^ (-(2 * a)))) ^ 2 *
              (Real.sqrt (∑ i, U i ^ 2) * Real.sqrt (∑ k, V k ^ 2)) := by ring
          _ = _ := by rw [hsq]; ring
  have hnear : (∑ i, ∑ k, 6 ^ (2 * a) * R ^ (-s) *
      (1 + componentDistance g i k) ^ (-s) * U i * V k) ≤
        6 ^ (2 * a) * R ^ (-s) * (2 * ∑' l : ℕ, (1 + (l : ℝ)) ^ (-s)) *
          Real.sqrt (∑ i, U i ^ 2) * Real.sqrt (∑ k, V k ^ 2) := by
    have hh := mul_le_mul_of_nonneg_left hbil (show 0 ≤ 6 ^ (2 * a) * R ^ (-s) by positivity)
    simpa only [Finset.mul_sum, mul_assoc] using hh
  dsimp only [U, V] at hfar hnear
  nlinarith only [hsum, hfar, hnear]

end Riesz2.OptimalDecay.Internal

namespace Riesz2.OptimalDecay.Internal

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι]
  {ν : Measure α}

/-- Bounded measurable coefficients make each scalar matrix pairing integrable. -/
theorem entry_integrable (d : α → ℝ) (hd : Measurable d) (B : ℝ)
    (hb : ∀ᵐ x ∂ν, |d x| ≤ B) (f g : Lp ℝ 2 ν) :
    Integrable (fun x => f x * d x * g x) ν := by
  have hh := ((Lp.memLp f).integrable_mul (Lp.memLp g)).bdd_mul
    hd.aestronglyMeasurable (hb.mono fun x hx => by simpa only [Real.norm_eq_abs] using hx)
  simpa only [Pi.mul_apply, mul_left_comm, mul_assoc] using hh

/-- L² bound on a single matrix entry pairing. Its integrability is proved above. -/
theorem entry_bound (d : α → ℝ) (hd : Measurable d) (B : ℝ)
    (hB : 0 ≤ B) (hb : ∀ᵐ x ∂ν, |d x| ≤ B) (f g : Lp ℝ 2 ν) :
    |∫ x, f x * d x * g x ∂ν| ≤ B * ‖f‖ * ‖g‖ := by
  obtain ⟨w, hw, hn⟩ := BoundedMatrixModes.exists_multiplier d hd B hB hb f
  have he : (∫ x, f x * d x * g x ∂ν) = inner ℝ w g := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hw] with x hx
    simp only [Real.inner_apply, hx]
    ring
  rw [he]
  exact (abs_real_inner_le_norm w g).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg _))

omit [DecidableEq ι] in
/-- Expanding a matrix pairing with constant component coefficients. -/
theorem weighted_pair_expansion (M : α → Matrix ι ι ℝ)
    (hm : ∀ i j, Measurable (fun x => M x i j))
    (B : ℝ) (hb : ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ B)
    (u v : ι → Lp ℝ 2 ν) (c : ι → ℝ) :
    (∫ x, matrixFieldPair M u (fun i => c i • v i) x ∂ν) =
      ∑ i, ∑ j, c j * ∫ x, u i x * M x i j * v j x ∂ν := by
  have hae : ∀ᵐ x ∂ν, ∀ j, (c j • v j) x = c j * v j x := by
    apply ae_all_iff.mpr
    intro j
    simpa only [Filter.EventuallyEq, Pi.smul_apply, smul_eq_mul] using Lp.coeFn_smul (c j) (v j)
  have he : (fun x => matrixFieldPair M u (fun i => c i • v i) x) =ᵐ[ν]
      (fun x => ∑ i, ∑ j, c j * (u i x * M x i j * v j x)) := by
    filter_upwards [hae] with x hx
    unfold matrixFieldPair
    apply Finset.sum_congr rfl
    intro i _; apply Finset.sum_congr rfl; intro j _
    rw [hx]; ring
  rw [integral_congr_ae he, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      exact integral_const_mul _ _
    · intro j _
      exact (entry_integrable _ (hm i j) B (hb.mono fun x hx => hx i j) _ _).const_mul _
  · intro i _
    exact integrable_finsetSum _ fun j _ =>
      (entry_integrable _ (hm i j) B (hb.mono fun x hx => hx i j) _ _).const_mul _

/-- The exact commutator identity on the full weak domain. Constant
component cutoffs preserve the scalar domain and all matrix pairings are finite. -/
theorem cutoff_pairing (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (M : α → Matrix ι ι ℝ)
    (hm : ∀ i j, Measurable (fun x => M x i j))
    (B : ℝ) (hb : ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ B)
    (hsym : ∀ᵐ x ∂ν, ∀ i j, M x i j = M x j i)
    (i₀ j : ι) (χ η : Lp ℝ 2 ν) (u v : ι → Q.1)
    (hu : WeightedWeakSolution Q M ⊤ (fun i => if i = i₀ then χ else 0) u)
    (hv : WeightedWeakSolution Q M ⊤ (fun i => if i = j then η else 0) v)
    (c : ι → ℝ) (hc₀ : c i₀ = 0) (hcj : c j = 1) :
    inner ℝ η (u j).val = ∑ i, ∑ k, (c i - c k) *
      ∫ x, (u i).val x * M x i k * (v k).val x ∂ν := by
  have hdom (w : ι → Q.1) : WeightedFormDomain Q M ⊤ w :=
    (BoundedMatrixForms.domain_iff Q M hm ⟨B, hb⟩ ⊤ w).mpr
      (Eventually.of_forall fun _ => Submodule.mem_top)
  have heu := (hu.2 (fun i => c i • v i) (hdom _)).2
  have hev := (hv.2 (fun i => c i • u i) (hdom _)).2
  have hr₀ : (∑ i, inner ℝ (if i = i₀ then χ else 0) ((c i • v i : Q.1).val)) = 0 := by
    rw [Finset.sum_eq_single i₀]
    · simp [hc₀]
    · intro i _ hi; simp [hi]
    · simp
  have hrj : (∑ i, inner ℝ (if i = j then η else 0) ((c i • u i : Q.1).val)) =
      inner ℝ η (u j).val  := by
    rw [Finset.sum_eq_single j]
    · simp [hcj]
    · intro i _ hi; simp [hi]
    · simp
  rw [hr₀] at heu
  rw [hrj] at hev
  simp only [Submodule.coe_smul] at heu hev
  rw [weighted_pair_expansion M hm B hb] at heu hev
  have hd : (∑ i, Q.2 (u i) (c i • v i)) = ∑ i, Q.2 (v i) (c i • u i) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [map_smul, smul_eq_mul, hQ.2.1 (u i) (v i)]
  have ht (i k : ι) : (∫ x, (v i).val x * M x i k * (u k).val x ∂ν) =
      ∫ x, (u k).val x * M x k i * (v i).val x ∂ν := by
    apply integral_congr_ae
    filter_upwards [hsym] with x hx
    rw [hx i k]; ring
  simp_rw [ht] at hev
  rw [Finset.sum_comm] at hev
  rw [hd] at heu
  calc
    _ = (∑ i, ∑ k, c i * ∫ x, (u i).val x * M x i k * (v k).val x ∂ν) -
        ∑ i, ∑ k, c k * ∫ x, (u i).val x * M x i k * (v k).val x ∂ν := by linarith
    _ = _ := by simp only [sub_mul, Finset.sum_sub_distrib]

end Riesz2.OptimalDecay.Internal

namespace Riesz2.OptimalDecay.Internal

open ComponentGeometryBounds InitialDecay

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι]
  {ν : Measure α}

omit [DecidableEq ι] in
/-- The finite weighted square sum is the norm of the existing Hilbert product. -/
theorem weighted_norm_eq (g : ComponentGeometry ι) (i₀ : ι) (a : ℝ)
    (v : ι → Lp ℝ 2 ν) :
    Real.sqrt (∑ i, (distortionWeight g i₀ a i * ‖v i‖) ^ 2) =
      ‖WithLp.toLp 2 (fun i => distortionWeight g i₀ a i • v i)‖ := by
  rw [← Real.sqrt_sq (norm_nonneg (WithLp.toLp 2 (fun i => distortionWeight g i₀ a i • v i))),
    PiLp.norm_sq_eq_of_L2]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (distortionWeight_pos g i₀ a i)]

/-- Pairing two weak point-source solutions across the component cutoff gives
the full exponent s as soon as their weighted exponent is at least s/2. -/
theorem point_source_cutoff_bound (s a : ℝ) (hs : 1 < s)
    (ha : 1 / 2 < a) (has : s ≤ 2 * a)
    (g : ComponentGeometry ι) (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (M : α → Matrix ι ι ℝ)
    (hm : ∀ i k, Measurable (fun x => M x i k))
    (B : ℝ) (hB : 0 ≤ B)
    (hentry : ∀ᵐ x ∂ν, ∀ i k, |M x i k| ≤ B * (1 + componentDistance g i k) ^ (-s))
    (hsym : ∀ᵐ x ∂ν, ∀ i k, M x i k = M x k i)
    (i₀ j : ι) (hR : 1 ≤ componentDistance g j i₀)
    (χ η : Lp ℝ 2 ν) (u v : ι → Q.1)
    (hu : WeightedWeakSolution Q M ⊤ (fun i => if i = i₀ then χ else 0) u)
    (hv : WeightedWeakSolution Q M ⊤ (fun i => if i = j then η else 0) v) :
    |inner ℝ η (u j).val| ≤
      B * (6 ^ s * (2 * ∑' l : ℕ, (1 + (l : ℝ)) ^ (-(2 * a))) +
        6 ^ (2 * a) * (2 * ∑' l : ℕ, (1 + (l : ℝ)) ^ (-s))) *
      (componentDistance g j i₀) ^ (-s) *
        ‖WithLp.toLp 2 (fun i => distortionWeight g i₀ a i • (u i).val)‖ *
        ‖WithLp.toLp 2 (fun k => distortionWeight g j a k • (v k).val)‖ := by
  let R := componentDistance g j i₀
  let c := fun i => if componentDistance g i i₀ ≤ R / 2 then (0 : ℝ) else 1
  let σ := fun i => if componentDistance g i i₀ ≤ R / 2 then (1 : ℝ) else 0
  have hc₀ : c i₀ = 0 := by simp [c, self, show 0 ≤ R / 2 by dsimp [R]; positivity]
  have hcj : c j = 1 := by simp [c, show ¬componentDistance g j i₀ ≤ R / 2 by dsimp [R] at *; linarith]
  have hb : ∀ᵐ x ∂ν, ∀ i k, |M x i k| ≤ B := by
    filter_upwards [hentry] with x hx i k
    exact (hx i k).trans (mul_le_of_le_one_right hB
      (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [nonneg g i k]) (by linarith)))
  have hid := cutoff_pairing Q hQ M hm B hb hsym i₀ j χ η u v hu hv c hc₀ hcj
  have hc (i k : ι) : |c i - c k| = |σ i - σ k| := by
    dsimp [c, σ]; split_ifs <;> norm_num
  have hn (i k : ι) := entry_bound (fun x => M x i k) (hm i k)
    (B * (1 + componentDistance g i k) ^ (-s))
    (mul_nonneg hB (Real.rpow_nonneg (by linarith [nonneg g i k]) _))
    (hentry.mono fun x hx => hx i k) (u i).val (v k).val
  have hh := cutoff_bilinear g i₀ j s a R hs ha has hR rfl
    (fun i => ‖(u i).val‖) (fun k => ‖(v k).val‖)
    (fun i => norm_nonneg _) (fun k => norm_nonneg _)
  change (∑ i, ∑ k, |σ i - σ k| * (1 + componentDistance g i k) ^ (-s) *
    ‖(u i).val‖ * ‖(v k).val‖) ≤ _ at hh
  rw [weighted_norm_eq, weighted_norm_eq] at hh
  calc
    _ = |∑ i, ∑ k, (c i - c k) * ∫ x, (u i).val x * M x i k * (v k).val x ∂ν| := congrArg abs hid
    _ ≤ ∑ i, ∑ k, |(c i - c k) * ∫ x, (u i).val x * M x i k * (v k).val x ∂ν| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ B * ∑ i, ∑ k, |σ i - σ k| * (1 + componentDistance g i k) ^ (-s) *
        ‖(u i).val‖ * ‖(v k).val‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul, hc]
      convert mul_le_mul_of_nonneg_left (hn i k) (abs_nonneg (σ i - σ k)) using 1; ring
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh hB

end Riesz2.OptimalDecay.Internal

namespace Riesz2.OptimalDecay

open ComponentGeometryBounds InitialDecay

/-- Uniform form of Proposition 4.5. The proof pairs two
weighted solutions across a cutoff, obtaining the optimal exponent in one step.
The polynomial degree precedes the matrix loss, spaces and all source data. -/
theorem optimal_decay_uniform (s β : ℝ) (hs : 1 < s) (hβ : 0 < β) :
    ∃ r C : ℝ, 0 ≤ r ∧ 1 ≤ C ∧
      ∀ (α ι : Type*) [MeasurableSpace α] [Fintype ι] [DecidableEq ι]
        (ν : Measure α) [IsProbabilityMeasure ν]
        (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q →
        IsConservativeScalarForm Q → ∀ (g : ComponentGeometry ι) (B : ℝ), 1 ≤ B →
        ∀ M : α → Matrix ι ι ℝ, (∀ i j, Measurable (fun x => M x i j)) →
        (∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
          (∀ z : ι → ℝ, B⁻¹ * ∑ i, z i ^ 2 ≤ ∑ i, ∑ j, z i * M x i j * z j) ∧
          (∀ i j, |M x i j| ≤ B * (1 + componentDistance g i j) ^ (-s))) →
        ∀ (i₀ : ι) (χ : Lp ℝ 2 ν),
          (∃! u : ι → Q.1, WeightedWeakSolution Q (fun x => β • M x) ⊤
            (fun i => if i = i₀ then χ else 0) u) ∧
          (∀ u : ι → Q.1, WeightedWeakSolution Q (fun x => β • M x) ⊤
              (fun i => if i = i₀ then χ else 0) u → ∀ j : ι,
            ‖(u j).val‖ ≤ C * B ^ r * (1 + componentDistance g j i₀) ^ (-s) * ‖χ‖) := by
  let a := (3 * s - 1) / 4
  have ha : 1 / 2 < a := by dsimp [a]; linarith
  have has : a < s - 1 / 2 := by dsimp [a]; linarith
  have ha₂ : s ≤ 2 * a := by dsimp [a]; linarith
  obtain ⟨r, L, hr, hL, hweighted⟩ := initial_decay_uniform s a β hs ha has hβ
  let D := 6 ^ s * (2 * ∑' l : ℕ, (1 + (l : ℝ)) ^ (-(2 * a))) +
    6 ^ (2 * a) * (2 * ∑' l : ℕ, (1 + (l : ℝ)) ^ (-s))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let C := 1 + 2 ^ s * (L + β * D * L ^ 2)
  have hL0 : 0 ≤ L := by linarith
  have hC : 1 ≤ C := by
    have hn : 0 ≤ 2 ^ s * (L + β * D * L ^ 2) := by positivity
    dsimp [C]; linarith
  refine ⟨2 * r + 1, C, by positivity, hC, ?_⟩
  intro α ι _ _ _ ν _ Q hQ hcons g B hB M hm hM i₀ χ
  have hB0 : 0 < B := by linarith
  have hinit := hweighted α ι ν Q hQ hcons g B hB M hm hM i₀ χ
  refine ⟨hinit.1, ?_⟩
  intro u hu j
  have hwu := (hinit.2 u hu).trans' (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  have hnormu : ‖(u j).val‖ ≤ L * B ^ r * ‖χ‖ := by
    have hj := PiLp.norm_apply_le
      (WithLp.toLp 2 (fun i => distortionWeight g i₀ a i • (u i).val)) j
    have hw : 1 ≤ distortionWeight g i₀ a j :=
      Real.one_le_rpow (by linarith [nonneg g j i₀]) (by linarith)
    have hj' : distortionWeight g i₀ a j * ‖(u j).val‖ ≤
        ‖WithLp.toLp 2 (fun i => distortionWeight g i₀ a i • (u i).val)‖ := by
      simpa only [WithLp.ofLp_toLp, norm_smul, Real.norm_eq_abs,
        abs_of_pos (distortionWeight_pos g i₀ a j)] using hj
    exact (le_mul_of_one_le_left (norm_nonneg _) hw).trans (hj'.trans hwu)
  have hBp : B ^ r ≤ B ^ (2 * r + 1) :=
    Real.rpow_le_rpow_of_exponent_le hB (by linarith)
  by_cases hR : 1 ≤ componentDistance g j i₀
  · obtain ⟨v, hv, _⟩ := (hweighted α ι ν Q hQ hcons g B hB M hm hM j (u j).val).1
    have hwv := ((hweighted α ι ν Q hQ hcons g B hB M hm hM j (u j).val).2 v hv).trans'
      (le_add_of_nonneg_right (Real.sqrt_nonneg _))
    have he := Internal.point_source_cutoff_bound s a hs ha ha₂ g Q hQ (fun x => β • M x)
      (AbstractEnergy.scaled_measurable β M hm) (β * B) (by positivity)
      (hM.mono fun x hx i k => by
        simpa only [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hβ, mul_assoc] using
          mul_le_mul_of_nonneg_left (hx.2.2 i k) hβ.le)
      (hM.mono fun x hx i k => by
        simp only [Matrix.smul_apply, smul_eq_mul, hx.1 i k])
      i₀ j hR χ (u j).val u v hu hv
    rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at he
    have he' : ‖(u j).val‖ ^ 2 ≤
        β * D * L ^ 2 * B ^ (2 * r + 1) *
          (componentDistance g j i₀) ^ (-s) * ‖χ‖ * ‖(u j).val‖ := by
      calc
        _ ≤ (β * B) * D * (componentDistance g j i₀) ^ (-s) *
            (L * B ^ r * ‖χ‖) * (L * B ^ r * ‖(u j).val‖) := by
          exact he.trans (mul_le_mul (mul_le_mul_of_nonneg_left hwu (by positivity)) hwv
            (norm_nonneg _) (by positivity))
        _ = _ := by
          rw [show 2 * r + 1 = r + r + 1 by ring,
            Real.rpow_add hB0, Real.rpow_add hB0, Real.rpow_one]
          ring
    have hpoint : ‖(u j).val‖ ≤ β * D * L ^ 2 * B ^ (2 * r + 1) *
        (componentDistance g j i₀) ^ (-s) * ‖χ‖ := by
      by_cases hz : ‖(u j).val‖ = 0
      · rw [hz]; positivity
      · exact (mul_le_mul_iff_left₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz))).mp
          (by nlinarith only [he'])
    have hRpow : (componentDistance g j i₀) ^ (-s) ≤
        2 ^ s * (1 + componentDistance g j i₀) ^ (-s) := by
      have heq : ((1 + componentDistance g j i₀) / 2) ^ (-s) =
          2 ^ s * (1 + componentDistance g j i₀) ^ (-s) := by
        rw [Real.div_rpow (by linarith [nonneg g j i₀]) (by norm_num),
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
      rw [← heq]
      exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    calc
      _ ≤ β * D * L ^ 2 * B ^ (2 * r + 1) *
          (2 ^ s * (1 + componentDistance g j i₀) ^ (-s)) * ‖χ‖ :=
        hpoint.trans (by gcongr)
      _ ≤ C * B ^ (2 * r + 1) * (1 + componentDistance g j i₀) ^ (-s) * ‖χ‖ := by
        have hc : β * D * L ^ 2 * 2 ^ s ≤ C := by dsimp [C]; nlinarith [show 0 ≤ 2 ^ s * L by positivity]
        calc
          _ = (β * D * L ^ 2 * 2 ^ s) * B ^ (2 * r + 1) *
              (1 + componentDistance g j i₀) ^ (-s) * ‖χ‖ := by ring
          _ ≤ _ := by gcongr
  · have hR0 := nonneg g j i₀
    have hpow : 1 ≤ 2 ^ s * (1 + componentDistance g j i₀) ^ (-s) := by
      rw [Real.rpow_neg (by linarith)]
      apply (le_mul_inv_iff₀ (Real.rpow_pos_of_pos (by linarith : 0 < 1 + componentDistance g j i₀) s)).mpr
      simp only [one_mul]
      exact Real.rpow_le_rpow (by linarith) (by linarith [not_le.mp hR]) (by linarith)
    have hc : 2 ^ s * L ≤ C := by
      dsimp [C]
      nlinarith [show 0 ≤ 2 ^ s * (β * D * L ^ 2) by positivity]
    calc
      _ ≤ L * B ^ r * ‖χ‖ := hnormu
      _ ≤ (2 ^ s * (1 + componentDistance g j i₀) ^ (-s)) * (L * B ^ (2 * r + 1) * ‖χ‖) := by
        exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBp hL0) (norm_nonneg χ)).trans
          (le_mul_of_one_le_left (by positivity) hpow)
      _ ≤ _ := by
        calc
          _ = (2 ^ s * L) * B ^ (2 * r + 1) * (1 + componentDistance g j i₀) ^ (-s) * ‖χ‖ := by ring
          _ ≤ _ := by gcongr

end Riesz2.OptimalDecay

namespace Riesz2.OptimalDecay

/-- See Proposition 4.5 of the paper:
unique existence on the full weak domain and the optimal component estimate.
The loss exponent precedes h, A, every size, geometry, form and source. -/
theorem optimal_point_source_decay :
  ∀ (s : ShortExponent) (β : InverseTemperature) (q : ℝ),
    0 ≤ q → ∃ r : ℝ, 0 ≤ r ∧ ∀ h : ℝ, 0 < h → ∀ A : ℝ, 1 ≤ A →
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ (n : ℕ+) (ι : Type) [Fintype ι] [DecidableEq ι],
      Fintype.card ι ≤ (n : ℕ) → ∀ g : ComponentGeometry ι,
      ∀ (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d)))
        (ν : Measure (EuclideanSpace ℝ (Fin d))),
        IsOpen Ω → Convex ℝ Ω → Ω.Nonempty → IsProbabilityMeasure ν → ν Ωᶜ = 0 →
        ∀ Q : ScalarFormData ν, IsNeumannRealization Ω Q →
          IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
          ∀ M : EuclideanSpace ℝ (Fin d) → Matrix ι ι ℝ,
            SummableCoerciveMatrix (ρ := ν) s n h A q g M →
            ∀ (i₀ : ι) (χ : Lp ℝ 2 ν),
              (∃! u : ι → Q.1, WeightedWeakSolution Q
                (fun x => β.val • M x) ⊤ (fun i => if i = i₀ then χ else 0) u) ∧
              (∀ u : ι → Q.1, WeightedWeakSolution Q
                  (fun x => β.val • M x) ⊤ (fun i => if i = i₀ then χ else 0) u →
                ∀ j : ι, ‖(u j).val‖ ≤ C * (n : ℝ) ^ (r * h) *
                  (1 + componentDistance g j i₀) ^ (-s.val) * ‖χ‖) := by
  intro s β q hq
  obtain ⟨r, C, hr, hC, hbound⟩ := optimal_decay_uniform s.val β.val s.property β.property
  refine ⟨q * r, mul_nonneg hq hr, ?_⟩
  intro h hh A hA
  have hA0 : 0 < A := by linarith
  refine ⟨C * A ^ r, one_le_mul_of_one_le_of_one_le hC (Real.one_le_rpow hA hr), ?_⟩
  intro n ι _ _ _hcard g d Ω ν _hopen _hconvex _hne hν _hsupp Q _hreal hQ hcons M hM i₀ χ
  have : IsProbabilityMeasure ν := hν
  have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.property
  have hn0 : (0 : ℝ) < (n : ℝ) := by positivity
  have hB : 1 ≤ A * (n : ℝ) ^ (q * h) :=
    one_le_mul_of_one_le_of_one_le hA (Real.one_le_rpow hn (mul_nonneg hq hh.le))
  have he := hbound (EuclideanSpace ℝ (Fin d)) ι ν Q hQ hcons g
    (A * (n : ℝ) ^ (q * h)) hB M hM.1 hM.2 i₀ χ
  have hfactor : C * (A * (n : ℝ) ^ (q * h)) ^ r =
      (C * A ^ r) * (n : ℝ) ^ ((q * r) * h) := by
    rw [Real.mul_rpow hA0.le (by positivity), ← Real.rpow_mul hn0.le,
      show (q * h) * r = (q * r) * h by ring]
    ring
  simpa only [hfactor] using he

end Riesz2.OptimalDecay

namespace Riesz2.OptimalDecay

/-- The target window of Subsection 4.2, with the inherited distance. -/
def targetWindow {ι : Type*} [Fintype ι] (g : ComponentGeometry ι)
    (i₀ j : ι) : Finset ι :=
  Finset.univ.filter fun k => componentDistance g k j ≤ componentDistance g j i₀ / 3

/-- The exterior forcing of Subsection 4.2, as an actual measurable
function wherever the matrix entries are measurable. No inverse is selected. -/
def exteriorSource {α ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ℝ) (M : α → Matrix ι ι ℝ) (J : Finset ι)
    (u : ι → α → ℝ) (l : ι) (x : α) : ℝ :=
  -β * ∑ k ∈ Jᶜ, M x l k * u k x

/-- Distance to the nonempty exterior in Subsection 4.2. The finite
minimum is the inherited distance, including on sparse subsets. -/
def exteriorRadius {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ComponentGeometry ι) (J : Finset ι) (hne : Jᶜ.Nonempty) (l : ι) : ℝ :=
  1 + Jᶜ.inf' hne (fun k => componentDistance g l k)

end Riesz2.OptimalDecay

namespace Riesz2.OptimalDecay.Internal

open ComponentGeometryBounds InitialDecay

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A finite inherited subset has the same power-tail bound as its ambient
line or cycle, even when its closest exterior label is very far away. -/
theorem subset_power_tail (g : ComponentGeometry ι) (l : ι) (S : Finset ι)
    (p D : ℝ) (hp : 1 < p) (hD : 1 ≤ D)
    (hS : ∀ k ∈ S, D ≤ 1 + componentDistance g l k) :
    ∑ k ∈ S, (1 + componentDistance g l k) ^ (-p) ≤
      2 * (1 + 1 / (p - 1)) * D ^ (1 - p) := by
  let f := fun k : ℕ => if D ≤ 1 + (k : ℝ) then (1 + (k : ℝ)) ^ (-p) else 0
  have hf (k : ℕ) : 0 ≤ f k := by dsimp [f]; split_ifs <;> positivity
  have hsum : Summable f := by
    apply Summable.of_nonneg_of_le hf _ (summable_one_add_rpow_neg hp)
    intro k; dsimp [f]; split_ifs
    · exact le_rfl
    · positivity
  have he (k : ι) (hk : k ∈ S) : (1 + componentDistance g l k) ^ (-p) =
      f ⌊componentDistance g l k⌋₊ := by
    obtain ⟨m, hm⟩ := exists_nat g l k
    simp only [hm, Nat.floor_natCast]
    exact (ite_eq_left (by simpa only [hm] using hS k hk)).symm
  calc
    _ = ∑ k ∈ S, f ⌊componentDistance g l k⌋₊ := Finset.sum_congr rfl he
    _ ≤ ∑ k, f ⌊componentDistance g l k⌋₊ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ => hf _)
    _ ≤ 2 * ∑' k, f k := sum_profile_le g l f hf hsum
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (tsum_tail_indicator_le hp hD) (by norm_num : (0 : ℝ) ≤ 2)
      simpa only [mul_assoc] using hh

/-- The exterior is nonempty because it contains the source index. -/
theorem source_mem_exterior (g : ComponentGeometry ι) (i₀ j : ι)
    (hR : 0 < componentDistance g j i₀) : i₀ ∈ (targetWindow g i₀ j)ᶜ := by
  simp only [targetWindow, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [symm g i₀ j]
  linarith

/-- The minimum defining the exterior radius is positive and below each
candidate distance, in particular the distance to the source. -/
theorem exteriorRadius_bounds (g : ComponentGeometry ι) (J : Finset ι)
    (hne : Jᶜ.Nonempty) (l : ι) :
    1 ≤ exteriorRadius g J hne l ∧
      ∀ k ∈ Jᶜ, exteriorRadius g J hne l ≤ 1 + componentDistance g l k := by
  constructor
  · unfold exteriorRadius
    have hh : 0 ≤ Jᶜ.inf' hne (fun k => componentDistance g l k) :=
      Finset.le_inf' hne (fun k => componentDistance g l k) (fun k _ => nonneg g l k)
    linarith
  · intro k hk
    simpa only [exteriorRadius, add_comm] using add_le_add_left
      (Finset.inf'_le (fun k => componentDistance g l k) hk) 1

end Riesz2.OptimalDecay.Internal

namespace Riesz2.OptimalDecay.Internal

open ComponentGeometryBounds InitialDecay

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exterior convolution bound following from the optimal component profile.
It retains the true distance to the exterior, with no density assumption on E. -/
theorem exterior_convolution (s : ℝ) (hs : 1 < s) (g : ComponentGeometry ι)
    (i₀ j l : ι) (hR : 6 ≤ componentDistance g j i₀)
    (hl : l ∈ targetWindow g i₀ j)
    (hne : (targetWindow g i₀ j)ᶜ.Nonempty) :
    ∑ k ∈ (targetWindow g i₀ j)ᶜ,
      (1 + componentDistance g l k) ^ (-s) * (1 + componentDistance g k i₀) ^ (-s) ≤
      6 ^ s * (componentDistance g j i₀) ^ (-s) *
        ((2 * ∑' m : ℕ, (1 + (m : ℝ)) ^ (-s)) +
          (2 * (1 + 1 / (s - 1))) * (exteriorRadius g (targetWindow g i₀ j) hne l) ^ (1 - s)) := by
  let R := componentDistance g j i₀
  let J := targetWindow g i₀ j
  let D := exteriorRadius g J hne l
  have hR1 : 1 ≤ R := by dsimp [R]; linarith
  have hlR : componentDistance g l j ≤ R / 3 := (Finset.mem_filter.mp hl).2
  have h₁ := triangle g j l i₀
  rw [symm g j l] at h₁
  have ht (k : ι) :
      (1 + componentDistance g l k) ^ (-s) * (1 + componentDistance g k i₀) ^ (-s) ≤
      (6 ^ s * R ^ (-s)) * (1 + componentDistance g k i₀) ^ (-s) +
        (6 ^ s * R ^ (-s)) * (1 + componentDistance g l k) ^ (-s) := by
    have hk0 : 0 ≤ (1 + componentDistance g k i₀) ^ (-s) :=
      Real.rpow_nonneg (by linarith [nonneg g k i₀]) _
    have hl0 : 0 ≤ (1 + componentDistance g l k) ^ (-s) :=
      Real.rpow_nonneg (by linarith [nonneg g l k]) _
    by_cases hk : componentDistance g k i₀ ≤ R / 3
    · have hdist : R / 6 ≤ componentDistance g l k := by
        have hh := triangle g l k i₀
        change R ≤ componentDistance g l j + componentDistance g l i₀ at h₁
        linarith
      have hh := mul_le_mul_of_nonneg_right
        (inverse_power_fraction s R (componentDistance g l k) (by linarith) hR1 hdist) hk0
      exact hh.trans (le_add_of_nonneg_right (by positivity))
    · have hh := mul_le_mul_of_nonneg_left
        (inverse_power_fraction s R (componentDistance g k i₀) (by linarith) hR1 (by linarith [not_le.mp hk])) hl0
      nlinarith [show 0 ≤ (6 ^ s * R ^ (-s)) * (1 + componentDistance g k i₀) ^ (-s) by positivity]
  have hsum := Finset.sum_le_sum fun k (_ : k ∈ Jᶜ) => ht k
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hS : (∑ k ∈ Jᶜ, (1 + componentDistance g k i₀) ^ (-s)) ≤
      2 * ∑' m : ℕ, (1 + (m : ℝ)) ^ (-s) := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun k _ _ =>
      Real.rpow_nonneg (by linarith [nonneg g k i₀]) _)).trans
    simpa only [symm g] using sum_power_le g i₀ hs
  have hD := exteriorRadius_bounds g J hne l
  have htail := subset_power_tail g l Jᶜ s D hs hD.1 hD.2
  apply hsum.trans
  calc
    _ ≤ (6 ^ s * R ^ (-s)) * (2 * ∑' m : ℕ, (1 + (m : ℝ)) ^ (-s)) +
        (6 ^ s * R ^ (-s)) * (2 * (1 + 1 / (s - 1)) * D ^ (1 - s)) :=
      add_le_add (mul_le_mul_of_nonneg_left hS (by positivity))
        (mul_le_mul_of_nonneg_left htail (by positivity))
    _ = _ := by dsimp [R, D]; ring

/-- Conversion of the stronger exterior convolution profile to the exponents
α₀ and t of the proof of Proposition 4.5. -/
theorem exterior_profile (s a R D : ℝ) (ha : a ≤ s - 1 / 2)
    (hR : 1 ≤ R) (hD : 1 ≤ D) (hDR : D ≤ 2 * R) :
    R ^ (-s) * D ^ (1 - s) ≤ 2 ^ (1 / 2 : ℝ) * R ^ (-a) * D ^ (-(s - 1 / 2)) := by
  have hR0 : 0 < R := by linarith
  have hD0 : 0 < D := by linarith
  calc
    _ = (R ^ (-s) * D ^ (1 / 2 : ℝ)) * D ^ (-(s - 1 / 2)) := by
      rw [mul_assoc, ← Real.rpow_add hD0]
      congr 2
      ring
    _ ≤ (R ^ (-s) * (2 * R) ^ (1 / 2 : ℝ)) * D ^ (-(s - 1 / 2)) := by gcongr
    _ = 2 ^ (1 / 2 : ℝ) * R ^ (-(s - 1 / 2)) * D ^ (-(s - 1 / 2)) := by
      rw [Real.mul_rpow (by norm_num) hR0.le]
      have he : -s + (1 / 2 : ℝ) = -(s - 1 / 2) := by ring
      rw [← he, Real.rpow_add hR0]
      ring
    _ ≤ _ := by gcongr

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}

/-- The exterior source of Subsection 4.2 belongs to L² and has the
finite Minkowski bound with the original entry envelope. -/
theorem exists_exterior_source (β s B : ℝ) (hβ : 0 < β) (hB : 0 ≤ B)
    (g : ComponentGeometry ι) (M : α → Matrix ι ι ℝ)
    (hm : ∀ i k, Measurable (fun x => M x i k))
    (he : ∀ᵐ x ∂ν, ∀ i k, |M x i k| ≤ B * (1 + componentDistance g i k) ^ (-s))
    (J : Finset ι) (u : ι → Lp ℝ 2 ν) (l : ι) :
    ∃ V : Lp ℝ 2 ν, (∀ᵐ x ∂ν, V x = exteriorSource β M J (fun k => u k) l x) ∧
      ‖V‖ ≤ β * B * ∑ k ∈ Jᶜ, (1 + componentDistance g l k) ^ (-s) * ‖u k‖ := by
  have hex (k : ι) := BoundedMatrixModes.exists_multiplier (fun x => M x l k) (hm l k)
    (B * (1 + componentDistance g l k) ^ (-s))
    (mul_nonneg hB (Real.rpow_nonneg (by linarith [nonneg g l k]) _))
    (he.mono fun x hx => hx l k) (u k)
  choose w hw hn using hex
  let V : Lp ℝ 2 ν := -β • ∑ k ∈ Jᶜ, w k
  have hV : ∀ᵐ x ∂ν, V x = exteriorSource β M J (fun k => u k) l x := by
    filter_upwards [Lp.coeFn_smul (-β) (∑ k ∈ Jᶜ, w k),
      Lp.coeFn_fun_finsetSum Jᶜ w, ae_all_iff.mpr hw] with x hx hs hw
    dsimp [V]
    rw [hx]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hs]
    simp only [exteriorSource]
    congr 1
    exact Finset.sum_congr rfl (fun k _ => hw k)
  refine ⟨V, hV, ?_⟩
  calc
    _ = β * ‖∑ k ∈ Jᶜ, w k‖ := by rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hβ]
    _ ≤ β * ∑ k ∈ Jᶜ, ‖w k‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hβ.le
    _ ≤ β * ∑ k ∈ Jᶜ, (B * (1 + componentDistance g l k) ^ (-s)) * ‖u k‖ := by gcongr with k; exact hn k
    _ = _ := by simp only [Finset.mul_sum, mul_assoc]

end Riesz2.OptimalDecay.Internal

namespace Riesz2.OptimalDecay.Internal

/-- Combining the two exterior profiles with a single constant. -/
theorem exterior_profile_sum (s a R D S T : ℝ) (ha : a ≤ s - 1 / 2)
    (hR : 1 ≤ R) (hD : 1 ≤ D) (hDR : D ≤ 2 * R) (hS : 0 ≤ S) (hT : 0 ≤ T) :
    6 ^ s * R ^ (-s) * (S + T * D ^ (1 - s)) ≤
      (6 ^ s * (S + T * 2 ^ (1 / 2 : ℝ))) *
        (R ^ (-s) + R ^ (-a) * D ^ (-(s - 1 / 2))) := by
  have hp := exterior_profile s a R D ha hR hD hDR
  have hR0 : 0 < R := by linarith
  have hD0 : 0 < D := by linarith
  calc
    _ = 6 ^ s * (S * R ^ (-s) + T * (R ^ (-s) * D ^ (1 - s))) := by ring
    _ ≤ 6 ^ s * (S * R ^ (-s) + T *
        (2 ^ (1 / 2 : ℝ) * R ^ (-a) * D ^ (-(s - 1 / 2)))) := by gcongr
    _ ≤ _ := by
      have h₁ : 0 ≤ S * (R ^ (-a) * D ^ (-(s - 1 / 2))) := by positivity
      have h₂ : 0 ≤ T * 2 ^ (1 / 2 : ℝ) * R ^ (-s) := by positivity
      have hh : S * R ^ (-s) + T * (2 ^ (1 / 2 : ℝ) * R ^ (-a) * D ^ (-(s - 1 / 2))) ≤
          (S + T * 2 ^ (1 / 2 : ℝ)) * (R ^ (-s) + R ^ (-a) * D ^ (-(s - 1 / 2))) := by
        nlinarith only [h₁, h₂]
      convert mul_le_mul_of_nonneg_left hh (show 0 ≤ 6 ^ s by positivity) using 1; ring

end Riesz2.OptimalDecay.Internal

namespace Riesz2.OptimalDecay

open ComponentGeometryBounds InitialDecay

/-- See the proof of Proposition 4.5 in the paper, in uniform matrix-loss form.
Both the exterior-source estimate and improved pointwise exponent follow
from the cutoff argument. -/
theorem optimal_illus_step_uniform (s β : ℝ) (hs : 1 < s) (hβ : 0 < β) :
    ∃ r C : ℝ, 0 ≤ r ∧ 1 ≤ C ∧
      ∀ (α ι : Type*) [MeasurableSpace α] [Fintype ι] [DecidableEq ι]
        (ν : Measure α) [IsProbabilityMeasure ν]
        (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q →
        IsConservativeScalarForm Q → ∀ (g : ComponentGeometry ι) (B : ℝ), 1 ≤ B →
        ∀ M : α → Matrix ι ι ℝ, (∀ i j, Measurable (fun x => M x i j)) →
        (∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
          (∀ z : ι → ℝ, B⁻¹ * ∑ i, z i ^ 2 ≤ ∑ i, ∑ j, z i * M x i j * z j) ∧
          (∀ i j, |M x i j| ≤ B * (1 + componentDistance g i j) ^ (-s))) →
        ∀ (a : ℝ), s - 1 / 2 - min ((s - 1) / 4) (1 / 4) ≤ a →
        ∀ (i₀ : ι) (χ : Lp ℝ 2 ν) (u : ι → Q.1),
          WeightedWeakSolution Q (fun x => β • M x) ⊤
            (fun i => if i = i₀ then χ else 0) u →
        ∀ j : ι, 6 ≤ componentDistance g j i₀ →
          (∀ (l : ι), l ∈ targetWindow g i₀ j →
            ∀ hne : (targetWindow g i₀ j)ᶜ.Nonempty,
            ∃ V : Lp ℝ 2 ν,
              (∀ᵐ x ∂ν, V x = exteriorSource β M (targetWindow g i₀ j)
                (fun k => (u k).val) l x) ∧
              ‖V‖ ≤ C * B ^ r * ‖χ‖ *
                ((componentDistance g j i₀) ^ (-s) +
                  (componentDistance g j i₀) ^ (-(s - 1 / 2 - min ((s - 1) / 4) (1 / 4))) *
                    (exteriorRadius g (targetWindow g i₀ j) hne l) ^ (-(s - 1 / 2)))) ∧
          ‖(u j).val‖ ≤ C * B ^ r *
            (1 + componentDistance g j i₀) ^ (-min s (a + s - 1)) * ‖χ‖ := by
  obtain ⟨r, L, hr, hL, hopt⟩ := optimal_decay_uniform s β hs hβ
  let S := 2 * ∑' m : ℕ, (1 + (m : ℝ)) ^ (-s)
  let T := 2 * (1 + 1 / (s - 1))
  let D := 6 ^ s * (S + T * 2 ^ (1 / 2 : ℝ))
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hL0 : 0 ≤ L := by linarith
  let C := 1 + L + β * L * D
  have hC : 1 ≤ C := by dsimp [C]; nlinarith [show 0 ≤ β * L * D by positivity]
  refine ⟨r + 1, C, by positivity, hC, ?_⟩
  intro α ι _ _ _ ν _ Q hQ hcons g B hB M hm hM a _ha i₀ χ u hu j hR
  have hB0 : 0 < B := by linarith
  have hoptu := (hopt α ι ν Q hQ hcons g B hB M hm hM i₀ χ).2 u hu
  have hpow : B ^ r ≤ B ^ (r + 1) := Real.rpow_le_rpow_of_exponent_le hB (by linarith)
  have hR1 : 1 ≤ componentDistance g j i₀ := by linarith
  constructor
  · intro l hl hne
    obtain ⟨V, hV, hn⟩ := Internal.exists_exterior_source β s B hβ hB0.le g M hm
      (hM.mono fun _ hx => hx.2.2) (targetWindow g i₀ j) (fun k => (u k).val) l
    refine ⟨V, hV, ?_⟩
    let R := componentDistance g j i₀
    let δ := exteriorRadius g (targetWindow g i₀ j) hne l
    let a₀ := s - 1 / 2 - min ((s - 1) / 4) (1 / 4)
    have hδ := Internal.exteriorRadius_bounds g (targetWindow g i₀ j) hne l
    have hR0 : 0 < R := by dsimp [R]; linarith
    have hδ0 : 0 < δ := by dsimp [δ]; linarith [hδ.1]
    have hδR : δ ≤ 2 * R := by
      have hh := hδ.2 i₀ (Internal.source_mem_exterior g i₀ j (by linarith))
      have ht := triangle g l j i₀
      have hlR := (Finset.mem_filter.mp hl).2
      dsimp [δ, R] at *
      linarith
    have ha₀ : a₀ ≤ s - 1 / 2 := by
      have hh : 0 ≤ min ((s - 1) / 4) (1 / 4) := by positivity
      dsimp [a₀]; linarith
    have hconv := Internal.exterior_convolution s hs g i₀ j l hR hl hne
    have hprof := Internal.exterior_profile_sum s a₀ R δ S T ha₀ hR1 hδ.1 hδR hS hT
    have hsum : (∑ k ∈ (targetWindow g i₀ j)ᶜ,
        (1 + componentDistance g l k) ^ (-s) * ‖(u k).val‖) ≤
        (L * B ^ r * ‖χ‖) *
          (D * (R ^ (-s) + R ^ (-a₀) * δ ^ (-(s - 1 / 2)))) := by
      calc
        _ ≤ ∑ k ∈ (targetWindow g i₀ j)ᶜ,
            (1 + componentDistance g l k) ^ (-s) *
              (L * B ^ r * (1 + componentDistance g k i₀) ^ (-s) * ‖χ‖) := by
          apply Finset.sum_le_sum
          intro k _
          exact mul_le_mul_of_nonneg_left (hoptu k)
            (Real.rpow_nonneg (by linarith [nonneg g l k]) _)
        _ = (L * B ^ r * ‖χ‖) * ∑ k ∈ (targetWindow g i₀ j)ᶜ,
            (1 + componentDistance g l k) ^ (-s) * (1 + componentDistance g k i₀) ^ (-s) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hconv.trans hprof) (by positivity)
    calc
      _ ≤ β * B * ((L * B ^ r * ‖χ‖) *
          (D * (R ^ (-s) + R ^ (-a₀) * δ ^ (-(s - 1 / 2))))) :=
        hn.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
      _ = (β * L * D) * B ^ (r + 1) * ‖χ‖ *
          (R ^ (-s) + R ^ (-a₀) * δ ^ (-(s - 1 / 2))) := by
        rw [Real.rpow_add hB0, Real.rpow_one]; ring
      _ ≤ _ := by
        have hc : β * L * D ≤ C := by dsimp [C]; linarith
        change _ ≤ C * B ^ (r + 1) * ‖χ‖ * (R ^ (-s) + R ^ (-a₀) * δ ^ (-(s - 1 / 2)))
        gcongr
  · have hc : L ≤ C := by dsimp [C]; nlinarith [show 0 ≤ β * L * D by positivity]
    have hp : (1 + componentDistance g j i₀) ^ (-s) ≤
        (1 + componentDistance g j i₀) ^ (-min s (a + s - 1)) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [nonneg g j i₀])
        (neg_le_neg (min_le_left _ _))
    exact (hoptu j).trans (by gcongr)

end Riesz2.OptimalDecay

namespace Riesz2.OptimalDecay

/-- See the proof of Proposition 4.5 in the paper. The exterior-source estimate
and improved pointwise exponent have polynomial losses in the standing
matrix parameters. The cutoff argument proves these without induction. -/
theorem optimal_illus_step (s : ShortExponent) (β : InverseTemperature)
    (q : ℝ) (hq : 0 ≤ q) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ h : ℝ, 0 < h → ∀ A : ℝ, 1 ≤ A →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ (n : ℕ+) (α ι : Type*)
        [MeasurableSpace α] [Fintype ι] [DecidableEq ι],
        Fintype.card ι ≤ (n : ℕ) → ∀ (g : ComponentGeometry ι)
          (ν : Measure α) [IsProbabilityMeasure ν] (Q : ScalarFormData ν),
        IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
        ∀ M : α → Matrix ι ι ℝ, SummableCoerciveMatrix (ρ := ν) s n h A q g M →
        ∀ a : ℝ, s.val - 1 / 2 - min ((s.val - 1) / 4) (1 / 4) ≤ a →
        ∀ (i₀ : ι) (χ : Lp ℝ 2 ν) (u : ι → Q.1),
          WeightedWeakSolution Q (fun x => β.val • M x) ⊤
            (fun i => if i = i₀ then χ else 0) u →
        ∀ j : ι, 6 ≤ componentDistance g j i₀ →
          (targetWindow g i₀ j)ᶜ.Nonempty ∧
          (∀ (l : ι), l ∈ targetWindow g i₀ j →
            ∀ hne : (targetWindow g i₀ j)ᶜ.Nonempty,
            ∃ V : Lp ℝ 2 ν,
              (∀ᵐ x ∂ν, V x = exteriorSource β.val M (targetWindow g i₀ j)
                (fun k => (u k).val) l x) ∧
              ‖V‖ ≤ C * (n : ℝ) ^ (r * h) * ‖χ‖ *
                ((componentDistance g j i₀) ^ (-s.val) +
                  (componentDistance g j i₀) ^ (-(s.val - 1 / 2 - min ((s.val - 1) / 4) (1 / 4))) *
                    (exteriorRadius g (targetWindow g i₀ j) hne l) ^ (-(s.val - 1 / 2)))) ∧
          ‖(u j).val‖ ≤ C * (n : ℝ) ^ (r * h) *
            (1 + componentDistance g j i₀) ^ (-min s.val (a + s.val - 1)) * ‖χ‖ := by
  obtain ⟨r, C, hr, hC, hbound⟩ := optimal_illus_step_uniform s.val β.val s.property β.property
  refine ⟨q * r, mul_nonneg hq hr, ?_⟩
  intro h hh A hA
  have hA0 : 0 < A := by linarith
  refine ⟨C * A ^ r, one_le_mul_of_one_le_of_one_le hC (Real.one_le_rpow hA hr), ?_⟩
  intro n α ι _ _ _ _hcard g ν _ Q hQ hcons M hM a ha i₀ χ u hu j hR
  have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.property
  have hn0 : (0 : ℝ) < (n : ℝ) := by positivity
  have hB : 1 ≤ A * (n : ℝ) ^ (q * h) :=
    one_le_mul_of_one_le_of_one_le hA (Real.one_le_rpow hn (mul_nonneg hq hh.le))
  have he := hbound α ι ν Q hQ hcons g (A * (n : ℝ) ^ (q * h)) hB M hM.1 hM.2
    a ha i₀ χ u hu j hR
  have hfactor : C * (A * (n : ℝ) ^ (q * h)) ^ r =
      (C * A ^ r) * (n : ℝ) ^ ((q * r) * h) := by
    rw [Real.mul_rpow hA0.le (by positivity), ← Real.rpow_mul hn0.le,
      show (q * h) * r = (q * r) * h by ring]
    ring
  refine ⟨⟨i₀, Internal.source_mem_exterior g i₀ j (by linarith)⟩, ?_⟩
  simpa only [hfactor] using he

end Riesz2.OptimalDecay

namespace Riesz2.OptimalDecay.Internal

/-- See the proof of Proposition 4.5 in the paper, retaining its internal
principal-subset induction hypothesis. The exponents of both polynomial losses
precede h, and their prefactors precede all sizes, matrices and source data.
The independent cutoff proof establishes the step without using that hypothesis. -/
theorem bootstrap_step_of_induction (s : ShortExponent) (β : InverseTemperature)
    (q p : ℝ) (hq : 0 ≤ q) (_hp : 0 ≤ p) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ h : ℝ, 0 < h → ∀ A : ℝ, 1 ≤ A →
      ∀ K : ℝ, 1 ≤ K → ∃ C : ℝ, 1 ≤ C ∧ ∀ (n : ℕ+) (α ι : Type*)
        [MeasurableSpace α] [Fintype ι] [DecidableEq ι],
        Fintype.card ι ≤ (n : ℕ) → ∀ (g : ComponentGeometry ι)
          (ν : Measure α) [IsProbabilityMeasure ν] (Q : ScalarFormData ν),
        IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
        ∀ M : α → Matrix ι ι ℝ, SummableCoerciveMatrix (ρ := ν) s n h A q g M →
        ∀ a : ℝ, s.val - 1 / 2 - min ((s.val - 1) / 4) (1 / 4) ≤ a →
        (∀ (S : Finset ι) (i₀ j : S) (χ : Lp ℝ 2 ν) (u : S → Q.1),
          WeightedWeakSolution Q (fun x (i k : S) => β.val * M x i.val k.val) ⊤
            (fun i => if i = i₀ then χ else 0) u →
          ‖(u j).val‖ ≤ K * (n : ℝ) ^ (p * h) *
            (1 + componentDistance g j.val i₀.val) ^ (-a) * ‖χ‖) →
        ∀ (i₀ : ι) (χ : Lp ℝ 2 ν) (u : ι → Q.1),
          WeightedWeakSolution Q (fun x => β.val • M x) ⊤
            (fun i => if i = i₀ then χ else 0) u →
        ∀ j : ι, 6 ≤ componentDistance g j i₀ →
          (targetWindow g i₀ j)ᶜ.Nonempty ∧
          (∀ (l : ι), l ∈ targetWindow g i₀ j →
            ∀ hne : (targetWindow g i₀ j)ᶜ.Nonempty,
            ∃ V : Lp ℝ 2 ν,
              (∀ᵐ x ∂ν, V x = exteriorSource β.val M (targetWindow g i₀ j)
                (fun k => (u k).val) l x) ∧
              ‖V‖ ≤ C * (n : ℝ) ^ (r * h) * ‖χ‖ *
                ((componentDistance g j i₀) ^ (-s.val) +
                  (componentDistance g j i₀) ^ (-(s.val - 1 / 2 - min ((s.val - 1) / 4) (1 / 4))) *
                    (exteriorRadius g (targetWindow g i₀ j) hne l) ^ (-(s.val - 1 / 2)))) ∧
          ‖(u j).val‖ ≤ C * (n : ℝ) ^ (r * h) *
            (1 + componentDistance g j i₀) ^ (-min s.val (a + s.val - 1)) * ‖χ‖ := by
  obtain ⟨r, hr, hstep⟩ := optimal_illus_step s β q hq
  refine ⟨r, hr, ?_⟩
  intro h hh A hA K _hK
  obtain ⟨C, hC, hbound⟩ := hstep h hh A hA
  refine ⟨C, hC, ?_⟩
  intro n α ι _ _ _ hcard g ν _ Q hQ hcons M hM a ha _hind i₀ χ u hu j hR
  exact hbound n α ι hcard g ν Q hQ hcons M hM a ha i₀ χ u hu j hR

end Riesz2.OptimalDecay.Internal
