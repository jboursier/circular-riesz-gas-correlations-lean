/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.OptimalLocalizationPart5
public import Riesz2.HelfferSjostrand.MaximumPrincipleNeumann
public import Riesz2.ToMathlib.SummedWeakEquation

/-!
# Auxiliary means on a fixed scalar simplex

In the proof of Lemma 6.4, a full-component equation has a scalar summed equation with
reference mass of order `m^(1-s)`. Subtracting the exterior gives the active mean and
its intrinsic form energy. The coefficient hypotheses are the bounds of Subsection 6.1.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical ENNReal

namespace Riesz2.AuxiliaryMean

/-- Geometry in the proof of Lemma 6.4: the embedded active block
has its ordinary index distance when the period is at least twice its size. -/
theorem active_distance (n m : ℕ+) (hnm : 2 * (n : ℕ) ≤ (m : ℕ))
    (i j : Fin (n : ℕ)) :
    Riesz1.cyclicIndexDistance m (i.castLE (by omega)) (j.castLE (by omega)) =
      Nat.dist i.val j.val := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Riesz1.cyclicIndexDistance, Fin.val_castLE]
  unfold Nat.dist
  omega

/-- Geometry in the proof of Lemma 6.4, with a one-based source label.
Every exterior component is at least `n/4` away, including across the seam
of the enlarged cycle. -/
theorem exterior_distance (n m : ℕ+) (hnm : 2 * (n : ℕ) ≤ (m : ℕ))
    (i₀ : Fin (n : ℕ))
    (hi₀ : |(i₀.val : ℝ) + 1 - (n : ℝ) / 2| ≤ (n : ℝ) / 4)
    (j : Fin (m : ℕ)) (hj : (n : ℕ) ≤ j.val) :
    (n : ℝ) / 4 ≤
      (Riesz1.cyclicIndexDistance m j (i₀.castLE (by omega)) : ℝ) := by
  have hi := i₀.isLt
  have hjm := j.isLt
  have hcent := abs_le.mp hi₀
  have hd : Nat.dist j.val i₀.val = j.val - i₀.val := by
    unfold Nat.dist
    omega
  have hle : i₀.val ≤ j.val := by omega
  have hdm : j.val - i₀.val ≤ (m : ℕ) := by omega
  simp only [Riesz1.cyclicIndexDistance, Fin.val_castLE, hd, Nat.cast_min,
    Nat.cast_sub hdm, Nat.cast_sub hle]
  apply le_min
  · have hnj : (n : ℝ) ≤ j.val := by exact_mod_cast hj
    linarith
  · have hjm' : (j.val : ℝ) + 1 ≤ m := by exact_mod_cast hjm
    linarith

/-- Summability used by the proof of Lemma 6.4. The bound is uniform
in the cycle and source label. In particular it covers the smallest periods. -/
theorem profile_sum_le (m : ℕ+) (i₀ : Fin (m : ℕ)) (p : ℝ) (hp : 1 < p) :
    (∑ j, weightRadius m j i₀ ^ (-p)) ≤
      2 * ∑' r : ℕ, (1 + (r : ℝ)) ^ (-p) := by
  simpa only [weightRadius, cyclicIndexDistance_comm' m i₀] using
    sum_le_two_mul_tsum_cyclicIndexDistance m i₀
      (fun r => (Real.rpow_pos_of_pos (by positivity : 0 < 1 + (r : ℝ)) (-p)).le)
      (summable_one_add_rpow_neg hp)

/-- Exterior power tail in the proof of Lemma 6.4. The added one in
the radius makes the estimate valid also for `n = 2,3`. -/
theorem exterior_profile_sum_le (n m : ℕ+) (hnm : 2 * (n : ℕ) ≤ (m : ℕ))
    (i₀ : Fin (n : ℕ))
    (hi₀ : |(i₀.val : ℝ) + 1 - (n : ℝ) / 2| ≤ (n : ℝ) / 4)
    (p : ℝ) (hp : 1 < p) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin (m : ℕ) => (n : ℕ) ≤ j.val),
      weightRadius m j (i₀.castLE (by omega)) ^ (-p)) ≤
      (2 * (1 + 1 / (p - 1)) * 4 ^ (p - 1)) * (n : ℝ) ^ (1 - p) := by
  let c : Fin (m : ℕ) := i₀.castLE (by omega)
  have hsub : Finset.univ.filter (fun j : Fin (m : ℕ) => (n : ℕ) ≤ j.val) ⊆
      Finset.univ.filter (fun j => 1 + (n : ℝ) / 4 ≤ weightRadius m j c) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    simpa only [weightRadius, c, add_comm] using
      add_le_add_left (exterior_distance n m hnm i₀ hi₀ j hj) 1
  have htail := sum_weightRadius_tail_le m c hp
    (show 1 ≤ 1 + (n : ℝ) / 4 by
      have hn : (0 : ℝ) < n := by positivity
      linarith)
  have hpow : (1 + (n : ℝ) / 4) ^ (1 - p) ≤
      4 ^ (p - 1) * (n : ℝ) ^ (1 - p) := by
    calc
      _ ≤ ((n : ℝ) / 4) ^ (1 - p) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      _ = _ := by
        rw [Real.div_rpow (by positivity : (0 : ℝ) ≤ n) (by norm_num : (0 : ℝ) ≤ 4),
          div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
        rw [show -(1 - p) = p - 1 by ring, mul_comm]
  calc
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j => 1 + (n : ℝ) / 4 ≤ weightRadius m j c),
        weightRadius m j c ^ (-p) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ =>
        Real.rpow_nonneg (zero_le_one.trans (one_le_weightRadius m j c)) _)
    _ ≤ 2 * (1 + 1 / (p - 1)) * (1 + (n : ℝ) / 4) ^ (1 - p) := htail
    _ ≤ 2 * (1 + 1 / (p - 1)) * (4 ^ (p - 1) * (n : ℝ) ^ (1 - p)) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring

/-- The literal active restriction and exterior sum partition all components.
This is the subtraction identity in the proof of Lemma 6.4. -/
theorem active_sum_eq {V : Type*} [AddCommGroup V]
    (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ)) (u : Fin (m : ℕ) → V) :
    (∑ i : Fin (n : ℕ), u (i.castLE hnm)) =
      (∑ j, u j) - ∑ j ∈ Finset.univ.filter (fun j : Fin (m : ℕ) => (n : ℕ) ≤ j.val), u j := by
  have he : (∑ i : Fin (n : ℕ), u (i.castLE hnm)) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin (m : ℕ) => j.val < (n : ℕ)), u j := by
    apply Finset.sum_bij (fun i _ => i.castLE hnm)
    · intro i _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castLE]
      exact i.isLt
    · intro i _ j _ he
      have hh : i.val = j.val := congrArg (fun k : Fin (m : ℕ) => k.val) he
      exact Fin.ext hh
    · intro j hj
      exact ⟨⟨j.val, (Finset.mem_filter.mp hj).2⟩, Finset.mem_univ _, Fin.ext rfl⟩
    · intro _ _; rfl
  rw [he, eq_sub_iff_add_eq]
  have hp := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun j : Fin (m : ℕ) => j.val < (n : ℕ)) u
  simpa only [not_lt] using hp

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- Summed equation and its two scalar estimates in the proof of Lemma 6.4. The full reference mass is kept exactly. -/
theorem summed_estimates_internal (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (m : ℕ+)
    (M : X → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hMb : ∃ B : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ B)
    (H : Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ) (b B : ℝ)
    (hb : 0 < b) (hB : 0 ≤ B) (hrow : ∀ i, ∑ j, H i j = b)
    (herror : ∀ᵐ x ∂ν, ∀ i, |∑ j, (M x i j - H i j)| ≤ B)
    (i₀ : Fin (m : ℕ)) (χ : Lp ℝ 2 ν) (u : Fin (m : ℕ) → Q.1)
    (hu : WeightedWeakSolution Q M ⊤ (fun i => if i = i₀ then χ else 0) u) :
    ‖(∑ i, u i).val‖ ≤ b⁻¹ * (‖χ‖ + B * ∑ i, ‖(u i).val‖) ∧
      Real.sqrt (Q.2 (∑ i, u i) (∑ i, u i)) ≤
        (Real.sqrt b)⁻¹ * (‖χ‖ + B * ∑ i, ‖(u i).val‖) := by
  obtain ⟨g, _, hgn, he⟩ := SummedWeakEquation.summed_equation Q M hMm hMb
    H b hrow B hB herror (fun i => if i = i₀ then χ else 0) u hu
  have hf : (∑ i : Fin (m : ℕ), if i = i₀ then χ else 0) = χ := by simp
  have hval : (∑ i, u i).val = ∑ i, (u i).val := by simp
  rw [hf, ← hval] at he
  have hs := SummedWeakEquation.scalar_estimates Q hQ b hb (χ - g) (∑ i, u i) he
  have hg : ‖χ - g‖ ≤ ‖χ‖ + B * ∑ i, ‖(u i).val‖ :=
    (norm_sub_le _ _).trans (add_le_add le_rfl hgn)
  exact ⟨hs.1.trans (mul_le_mul_of_nonneg_left hg (by positivity)),
    hs.2.trans (mul_le_mul_of_nonneg_left hg (by positivity))⟩

/-- Full and exterior profile sums, followed by subtraction, in the proof of Lemma 6.4. This helper is independent of the physical coefficient
construction. In particular its gradient is the entire scalar form gradient. -/
theorem subtract_exterior_internal (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q)
    (n m : ℕ+) (hnm : 2 * (n : ℕ) ≤ (m : ℕ)) (i₀ : Fin (n : ℕ))
    (hi₀ : |(i₀.val : ℝ) + 1 - (n : ℝ) / 2| ≤ (n : ℝ) / 4)
    (p q A F : ℝ) (hp : 1 < p) (hq : 1 < q) (hA : 0 ≤ A) (hF : 0 ≤ F)
    (u : Fin (m : ℕ) → Q.1)
    (hv : ∀ j, ‖(u j).val‖ ≤ A * weightRadius m j (i₀.castLE (by omega)) ^ (-p) * F)
    (hg : ∀ j, Real.sqrt (Q.2 (u j) (u j)) ≤
      A * weightRadius m j (i₀.castLE (by omega)) ^ (-q) * F) :
    let v := fun i : Fin (n : ℕ) => u (i.castLE (by omega))
    let S := ∑ i, v i
    (∀ j : Fin (n : ℕ), ‖(v j).val‖ ≤
      A * (1 + (Nat.dist j.val i₀.val : ℝ)) ^ (-p) * F) ∧
    (∑ j, ‖(v j).val‖) ≤ A * (2 * ∑' r : ℕ, (1 + (r : ℝ)) ^ (-p)) * F ∧
    ‖S.val‖ ≤ ‖(∑ j, u j).val‖ +
      A * (2 * (1 + 1 / (p - 1)) * 4 ^ (p - 1)) * (n : ℝ) ^ (1 - p) * F ∧
    Real.sqrt (Q.2 S S) ≤ Real.sqrt (Q.2 (∑ j, u j) (∑ j, u j)) +
      A * (2 * (1 + 1 / (q - 1)) * 4 ^ (q - 1)) * (n : ℝ) ^ (1 - q) * F := by
  intro v S
  let c : Fin (m : ℕ) := i₀.castLE (by omega)
  let E := Finset.univ.filter (fun j : Fin (m : ℕ) => (n : ℕ) ≤ j.val)
  have hfull : (∑ j, ‖(u j).val‖) ≤ A * (2 * ∑' r : ℕ, (1 + (r : ℝ)) ^ (-p)) * F := by
    calc
      _ ≤ ∑ j, A * weightRadius m j c ^ (-p) * F := Finset.sum_le_sum fun j _ => hv j
      _ = A * (∑ j, weightRadius m j c ^ (-p)) * F := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (profile_sum_le m c p hp) hA) hF
  have htail (r : ℝ) (hr : 1 < r) (f : Fin (m : ℕ) → ℝ)
      (hf : ∀ j, f j ≤ A * weightRadius m j c ^ (-r) * F) :
      (∑ j ∈ E, f j) ≤
        A * (2 * (1 + 1 / (r - 1)) * 4 ^ (r - 1)) * (n : ℝ) ^ (1 - r) * F := by
    calc
      _ ≤ ∑ j ∈ E, A * weightRadius m j c ^ (-r) * F := Finset.sum_le_sum fun j _ => hf j
      _ = A * (∑ j ∈ E, weightRadius m j c ^ (-r)) * F := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ A * ((2 * (1 + 1 / (r - 1)) * 4 ^ (r - 1)) * (n : ℝ) ^ (1 - r)) * F :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (exterior_profile_sum_le n m hnm i₀ hi₀ r hr) hA) hF
      _ = _ := by ring
  have hS : S = (∑ j, u j) - ∑ j ∈ E, u j := active_sum_eq n m (by omega) u
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    simpa only [v, weightRadius, active_distance n m hnm] using hv (j.castLE (by omega))
  · have hh := active_sum_eq n m (by omega) (fun j => ‖(u j).val‖)
    have hE : 0 ≤ ∑ j ∈ E, ‖(u j).val‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
    change (∑ j : Fin (n : ℕ), ‖(u (j.castLE (by omega))).val‖) ≤ _
    rw [hh]
    exact (sub_le_self _ hE).trans hfull
  · have hnorm : ‖(∑ j ∈ E, u j).val‖ ≤
        A * (2 * (1 + 1 / (p - 1)) * 4 ^ (p - 1)) * (n : ℝ) ^ (1 - p) * F := by
      simpa only [Submodule.coe_sum] using
        (norm_sum_le E (fun j => (u j).val)).trans (htail p hp (fun j => ‖(u j).val‖) hv)
    rw [hS, Submodule.coe_sub]
    exact (norm_sub_le _ _).trans (add_le_add le_rfl hnorm)
  · rw [hS]
    exact (SummedWeakEquation.sqrt_energy_sub_le Q hQ _ _).trans
      (add_le_add le_rfl ((SummedWeakEquation.sqrt_energy_sum_le Q hQ E u).trans
        (htail q hq (fun j => Real.sqrt (Q.2 (u j) (u j))) hg)))

/-- The positive reference row mass yields the two powers required by
the proof of Lemma 6.4, without an inverse at a zero mass. -/
theorem reference_mass_powers_internal (s c βlo β ell n m D F a g : ℝ)
    (hc : 0 < c) (hβlo : 0 < βlo) (hβ : βlo ≤ β)
    (hn : 0 < n) (hnm : n ≤ m) (hs : s < 1)
    (hell : c * m ^ (1 - s) ≤ ell) (hD : 0 ≤ D) (hF : 0 ≤ F)
    (ha : a ≤ (β * ell)⁻¹ * (D * F))
    (hg : g ≤ (Real.sqrt (β * ell))⁻¹ * (D * F)) :
    a ≤ (βlo * c)⁻¹ * D * n ^ (-(1 - s)) * F ∧
      g ≤ (Real.sqrt (βlo * c))⁻¹ * D * n ^ (-(1 - s) / 2) * F := by
  have hm : 0 < m := hn.trans_le hnm
  have hβpos := hβlo.trans_le hβ
  have hellpos : 0 < ell := (mul_pos hc (Real.rpow_pos_of_pos hm _)).trans_le hell
  have hmass : βlo * c * m ^ (1 - s) ≤ β * ell := by
    calc
      _ = βlo * (c * m ^ (1 - s)) := by ring
      _ ≤ β * ell := mul_le_mul hβ hell (by positivity) hβpos.le
  have hinv : (β * ell)⁻¹ ≤ (βlo * c)⁻¹ * n ^ (-(1 - s)) := by
    calc
      _ ≤ (βlo * c * m ^ (1 - s))⁻¹ := inv_anti₀ (by positivity) hmass
      _ = (βlo * c)⁻¹ * m ^ (-(1 - s)) := by
        rw [mul_inv, ← Real.rpow_neg hm.le]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hn hnm (by linarith)) (by positivity)
  have hinvsqrt : (Real.sqrt (β * ell))⁻¹ ≤
      (Real.sqrt (βlo * c))⁻¹ * n ^ (-(1 - s) / 2) := by
    rw [← Real.sqrt_inv]
    apply (Real.sqrt_le_sqrt hinv).trans_eq
    rw [Real.sqrt_mul (by positivity : 0 ≤ (βlo * c)⁻¹), Real.sqrt_inv,
      Real.sqrt_eq_rpow (n ^ (-(1 - s))), ← Real.rpow_mul hn.le]
    congr 2
    ring
  constructor
  · convert ha.trans (mul_le_mul_of_nonneg_right hinv (mul_nonneg hD hF)) using 1
    ring
  · convert hg.trans (mul_le_mul_of_nonneg_right hinvsqrt (mul_nonneg hD hF)) using 1
    ring

/-- The lifted maximum principle and restriction in Lemma 6.4 in the paper. The bounded open Neumann realization
supplies the chain rule of Proposition 3.6. Restriction can
only decrease the Euclidean norm of the component vector. -/
theorem supremum_restriction_internal (d : ℕ)
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ν]
    (Q : ScalarFormData ν) (_hQ : IsClosedScalarDirichletForm Q)
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hν : ∀ᵐ x ∂ν, x ∈ Ω)
    (hreal : IsNeumannRealization Ω Q)
    (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
    (M : EuclideanSpace ℝ (Fin d) → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (c : ℝ) (hc : 0 < c)
    (hM : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
      ∀ z : Fin (m : ℕ) → ℝ,
        c * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j)
    (i₀ : Fin (m : ℕ)) (χ : Lp ℝ 2 ν) (u : Fin (m : ℕ) → Q.1)
    (hu : WeightedWeakSolution Q M ⊤ (fun i => if i = i₀ then χ else 0) u) :
    eLpNorm (fun x => (WithLp.toLp 2 (fun i : Fin (n : ℕ) =>
      (u (i.castLE hnm)).val x) : EuclideanSpace ℝ (Fin (n : ℕ)))) ∞ ν ≤
      ENNReal.ofReal c⁻¹ * eLpNorm χ ∞ ν := by
  have hfull := maximumPrinciple_neumann hΩ hb hν Q hreal M hMm c hc hM
    ⊤ (fun i => if i = i₀ then χ else 0) u hu
  have hsrc : eLpNorm (fun x => (WithLp.toLp 2
      (fun i : Fin (m : ℕ) => (if i = i₀ then χ else 0 : Lp ℝ 2 ν) x) :
      EuclideanSpace ℝ (Fin (m : ℕ)))) ∞ ν = eLpNorm χ ∞ ν := by
    apply eLpNorm_congr_norm_ae
    · exact (VectorRadial.memLp_values _).aestronglyMeasurable
    · exact Lp.aestronglyMeasurable χ
    filter_upwards [Lp.coeFn_zero ℝ 2 ν] with x hx
    rw [PiLp.norm_eq_of_L2]
    simp only [apply_ite (fun f : Lp ℝ 2 ν => f x), hx, Pi.zero_apply, norm_zero,
      apply_ite norm, ite_pow, zero_pow (by omega : 2 ≠ 0),
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Real.sqrt_sq (norm_nonneg _)]
  rw [hsrc] at hfull
  apply le_trans ?_ hfull
  apply eLpNorm_mono_ae
  · exact (VectorRadial.memLp_values (fun i : Fin (n : ℕ) => (u (i.castLE hnm)).val)).aestronglyMeasurable
  exact ae_of_all _ fun x => by
    rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
    apply Real.sqrt_le_sqrt
    have he := active_sum_eq n m hnm (fun j => ‖(u j).val x‖ ^ 2)
    have hE : 0 ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin (m : ℕ) => (n : ℕ) ≤ j.val),
        ‖(u j).val x‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [he]
    exact sub_le_self _ hE

/-- Analytic implication in Lemma 6.4 of the paper
(the proof of Lemma 6.4), isolated from
the physical coefficient construction of Subsection 6.1. The only quantitative
matrix premise is its interval/coercivity/reference predicate.
All five auxiliary estimates, including the intrinsic mean energy and the
Euclidean component supremum, are conclusions. The loss exponent precedes
the tolerance and the compact temperature interval. -/
theorem auxiliary_estimates_of_coefficients_internal (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ) (M₀ : ℕ+)
    (hκstar : 0 < κstar) (hγstar : 0 < γstar) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ∀ Cstar : ℝ, 1 ≤ Cstar →
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    ∀ (n m : ℕ+) (hn : 2 ≤ (n : ℕ)) (hm : 2 ≤ (m : ℕ)),
    ∀ (_hnm : 2 * (n : ℕ) ≤ (m : ℕ)),
      (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
    let K := ⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ)
    1 ≤ K → 4 * K ≤ (m : ℕ) →
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
    ∀ i₀ : Fin (n : ℕ), |(i₀.val : ℝ) + 1 - (n : ℝ) / 2| ≤ (n : ℝ) / 4 →
    ∀ χ : Lp ℝ 2 ν,
    let c : Fin (m : ℕ) := i₀.castLE (by omega)
    (∃! u : Fin (m : ℕ) → Q.1, WeightedWeakSolution Q
      (fun x => β.val • M x) ⊤ (fun i => if i = c then χ else 0) u) ∧
    ∀ u : Fin (m : ℕ) → Q.1, WeightedWeakSolution Q
      (fun x => β.val • M x) ⊤ (fun i => if i = c then χ else 0) u →
    let v := fun i : Fin (n : ℕ) => u (i.castLE (by omega))
    let S := ∑ i, v i
    (∀ j : Fin (n : ℕ), ‖(v j).val‖ ≤ C * (n : ℝ) ^ (κ * ε) *
      (1 + (Nat.dist j.val i₀.val : ℝ)) ^ (s.val - 2) * ‖χ‖) ∧
    (∑ j, ‖(v j).val‖) ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ ∧
    ‖S.val‖ ≤ C * (n : ℝ) ^ (κ * ε - (1 - s.val)) * ‖χ‖ ∧
    Real.sqrt (Q.2 S S) ≤ C * (n : ℝ) ^ (κ * ε - (1 - s.val) / 2) * ‖χ‖ ∧
    eLpNorm (fun x => (WithLp.toLp 2 (fun i => (v i).val x) :
      EuclideanSpace ℝ (Fin (n : ℕ)))) ∞ ν ≤
        ENNReal.ofReal (C * (n : ℝ) ^ (κ * ε)) * eLpNorm χ ∞ ν := by
  obtain ⟨κp, hκp, hpoint⟩ := OptimalLocalizationPart5.optimal_pointwise_decay hzeta
    s κstar γstar M₀ hκstar hγstar
  obtain ⟨κe, hκe, herror⟩ := global_error_differences s κstar γstar hκstar.le hγstar.le (M₀ : ℕ)
  obtain ⟨c₀, C₀, hc₀, _, hmass⟩ := global_reference_mass_bounds s
  let κ := κp + κe + κstar
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  refine ⟨κ, hκ, fun ε hε Cstar hCstar βlo βhi hβlo hβhi => ?_⟩
  obtain ⟨Cp, hCp, hpoint⟩ := hpoint ε hε Cstar hCstar βlo βhi hβlo hβhi
  obtain ⟨Ce, hCe, herror⟩ := herror ε hε Cstar hCstar
  let D := 2 * ∑' r : ℕ, (1 + (r : ℝ)) ^ (-(2 - s.val))
  let Tv := 2 * (1 + 1 / (1 - s.val)) * 4 ^ (1 - s.val)
  let Tg := 2 * (1 + 1 / ((3 - s.val) / 2 - 1)) * 4 ^ ((3 - s.val) / 2 - 1)
  let B := 1 + βhi * Ce * Cp * D
  let V := (βlo * c₀)⁻¹ * B
  let G := (Real.sqrt (βlo * c₀))⁻¹ * B
  let C := 1 + Cp + Cp * D + V + Cp * Tv + G + Cp * Tg + βlo⁻¹ * Cstar
  have hD : 0 ≤ D := mul_nonneg (by norm_num) (tsum_nonneg fun _ => by positivity)
  have hs1 : 0 < 1 - s.val := sub_pos.mpr s.property.2
  have hqt : 0 < (3 - s.val) / 2 - 1 := by linarith [s.property.2]
  have hTv : 0 < Tv := by dsimp only [Tv]; positivity
  have hTg : 0 < Tg := by dsimp only [Tg]; positivity
  have hβhi0 : 0 < βhi := hβlo.trans_le hβhi
  have hCe0 : 0 < Ce := zero_lt_one.trans_le hCe
  have hB : 0 < B := by dsimp only [B]; positivity
  have hV : 0 < V := by dsimp only [V]; positivity
  have hG : 0 < G := by dsimp only [G]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro β hβ n m hn hm hnm hmn K hK hKm d Ω ν hΩ hconv hbound hne hprob hpot Q hreal hQ hQc M hM i₀ hi₀ χ c
  let : IsProbabilityMeasure ν := hprob
  have hβpos : 0 < β.val := β.property
  have hnm' : (n : ℕ) ≤ (m : ℕ) := by omega
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by positivity
  let L := (n : ℝ) ^ (κ * ε)
  let Ap := Cp * (n : ℝ) ^ (κp * ε)
  let Be := Ce * (n : ℝ) ^ (κe * ε)
  have hL : 1 ≤ L := Real.one_le_rpow hn1 (mul_nonneg hκ.le hε.le)
  have hAp : 0 ≤ Ap := by dsimp only [Ap]; positivity
  have hBe : 0 ≤ Be := by dsimp only [Be]; positivity
  have hk₁ : κp ≤ κ := by dsimp only [κ]; linarith
  have hk₂ : κp + κe ≤ κ := by dsimp only [κ]; linarith
  have hApL : Ap ≤ Cp * L :=
    LocalizedMatrix.loss_mono_internal hn1 hε.le hCp.le le_rfl hk₁
  have hprod : Be * Ap ≤ Ce * Cp * L := by
    calc
      _ = Ce * Cp * (n : ℝ) ^ ((κp + κe) * ε) := by
        dsimp only [Be, Ap]
        rw [add_mul, Real.rpow_add hn0]
        ring
      _ ≤ _ := LocalizedMatrix.loss_mono_internal hn1 hε.le (by positivity) le_rfl hk₂
  have hpoint' := hpoint β hβ n m hn hm hnm' hmn hK hKm d Ω ν
    hΩ hconv hbound hne hprob hpot Q hreal hQ hQc M hM c χ false
  dsimp only [Bool.false_eq_true, ↓reduceIte] at hpoint'
  refine ⟨hpoint'.1, ?_⟩
  intro u hu v S
  have huest := hpoint'.2 u hu
  have hv : ∀ j, ‖(u j).val‖ ≤ Ap * weightRadius m j c ^ (-(2 - s.val)) * ‖χ‖ :=
    fun j => (huest j).1
  have hg : ∀ j, Real.sqrt (Q.2 (u j) (u j)) ≤
      Ap * weightRadius m j c ^ (-((3 - s.val) / 2)) * ‖χ‖ := by
    intro j
    simpa only [Ap, weightRadius, neg_div] using (huest j).2
  have hsum : (∑ j, ‖(u j).val‖) ≤ Ap * D * ‖χ‖ := by
    calc
      _ ≤ ∑ j, Ap * weightRadius m j c ^ (-(2 - s.val)) * ‖χ‖ :=
        Finset.sum_le_sum fun j _ => hv j
      _ = Ap * (∑ j, weightRadius m j c ^ (-(2 - s.val))) * ‖χ‖ := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (profile_sum_le m c (2 - s.val) (by linarith [s.property.2])) hAp) (norm_nonneg χ)
  obtain ⟨a, Be₀, _, _, _, _, herr⟩ := herror n m hm hn hnm' hmn hK hKm ν M hM
  let H := (2 : ℝ) • rieszMatrix s m hm
  let ell := 2 * ∑ j, sampledRieszKernel s m hm j
  have hrow : ∀ i, ∑ j, (β.val • H) i j = β.val * ell := by
    intro i
    simp only [H, ell, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, rieszMatrix_row_sum]
  have hell : c₀ * (m : ℝ) ^ (1 - s.val) ≤ ell := by
    simpa only [ell, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, rieszMatrix_row_sum] using
      (hmass m hm c).1
  have hellpos : 0 < ell := (mul_pos hc₀ (Real.rpow_pos_of_pos (by positivity) _)).trans_le hell
  have herows : ∀ᵐ x ∂ν, ∀ i, |∑ j, (β.val • M x - β.val • H) i j| ≤ β.val * Be := by
    filter_upwards [herr] with x hx
    intro i
    have hh := hx.2.2.2.1 i
    calc
      _ = β.val * |∑ j, (M x - H) i j| := by
        simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, ← mul_sub,
          ← Finset.mul_sum, abs_mul, abs_of_pos β.property]
      _ ≤ β.val * ∑ j, |(M x - H) i j| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) β.property.le
      _ ≤ _ := mul_le_mul_of_nonneg_left hh β.property.le
  have hscalar := summed_estimates_internal Q hQ m (fun x => β.val • M x)
    (SchurRestriction.periodized_scaled_measurable β.val hM)
    (SchurRestriction.periodized_scaled_bounded β.val hM)
    (β.val • H) (β.val * ell) (β.val * Be) (by positivity) (by positivity)
    hrow herows c χ u hu
  have hsource : ‖χ‖ + β.val * Be * ∑ j, ‖(u j).val‖ ≤ B * L * ‖χ‖ := by
    have ht := mul_le_mul_of_nonneg_left hsum (show 0 ≤ β.val * Be by positivity)
    have ht' : β.val * Be * (Ap * D * ‖χ‖) ≤ βhi * Ce * Cp * L * D * ‖χ‖ := by
      calc
        _ = β.val * (Be * Ap) * D * ‖χ‖ := by ring
        _ ≤ βhi * (Ce * Cp * L) * D * ‖χ‖ := by gcongr; exact hβ.2
        _ = _ := by ring
    have hf := mul_le_mul_of_nonneg_right hL (norm_nonneg χ)
    dsimp only [B]
    nlinarith only [ht, ht', hf]
  have hfull := reference_mass_powers_internal s.val c₀ βlo β.val ell (n : ℝ) (m : ℝ)
    (B * L) ‖χ‖ ‖(∑ j, u j).val‖ (Real.sqrt (Q.2 (∑ j, u j) (∑ j, u j)))
    hc₀ hβlo hβ.1 hn0 (by exact_mod_cast hnm') s.property.2 hell (by positivity) (norm_nonneg χ)
    (hscalar.1.trans (mul_le_mul_of_nonneg_left hsource (by positivity)))
    (hscalar.2.trans (mul_le_mul_of_nonneg_left hsource (by positivity)))
  have hsub := subtract_exterior_internal Q hQ n m hnm i₀ hi₀
    (2 - s.val) ((3 - s.val) / 2) Ap ‖χ‖ (by linarith [s.property.2])
    (by linarith [s.property.2]) hAp (norm_nonneg χ) u hv hg
  have hpD : 0 ≤ Cp * D := mul_nonneg hCp.le hD
  have hpTv : 0 ≤ Cp * Tv := by positivity
  have hpTg : 0 ≤ Cp * Tg := by positivity
  have hβC : 0 ≤ βlo⁻¹ * Cstar := by positivity
  have hpointC : Cp ≤ C := by dsimp only [C]; linarith
  have hsumC : Cp * D ≤ C := by dsimp only [C]; linarith
  have hvC : V + Cp * Tv ≤ C := by dsimp only [C]; linarith
  have hgC : G + Cp * Tg ≤ C := by dsimp only [C]; linarith
  have hsupC : βlo⁻¹ * Cstar ≤ C := by dsimp only [C]; linarith
  have hloss : Ap ≤ C * L := hApL.trans (mul_le_mul_of_nonneg_right hpointC (by positivity))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    have he := (hsub.1 j).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hloss (by positivity)) (norm_nonneg χ))
    simpa only [show -(2 - s.val) = s.val - 2 by ring] using he
  · exact hsub.2.1.trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hApL hD) (norm_nonneg χ)).trans
      (by nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        hsumC (show 0 ≤ L by positivity)) (norm_nonneg χ)]))
  · have hh := hsub.2.2.1.trans (add_le_add hfull.1 le_rfl)
    have ht := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hApL hTv.le) (by positivity : 0 ≤ (n : ℝ) ^ (1 - (2 - s.val))))
      (norm_nonneg χ)
    have hpow : (n : ℝ) ^ (κ * ε - (1 - s.val)) = L * (n : ℝ) ^ (-(1 - s.val)) := by
      dsimp only [L]
      rw [sub_eq_add_neg, Real.rpow_add hn0]
    rw [hpow]
    have hc := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hvC (show 0 ≤ L by positivity)) (by positivity : 0 ≤ (n : ℝ) ^ (-(1 - s.val)))) (norm_nonneg χ)
    dsimp only [V, Tv] at hc
    rw [show 1 - (2 - s.val) = -(1 - s.val) by ring] at ht hh
    rw [show 2 - s.val - 1 = 1 - s.val by ring] at hh
    dsimp only [Tv] at ht
    change ‖S.val‖ ≤ _ at hh
    nlinarith only [hh, ht, hc]
  · have hh := hsub.2.2.2.trans (add_le_add hfull.2 le_rfl)
    have ht := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hApL hTg.le) (by positivity : 0 ≤ (n : ℝ) ^ (1 - (3 - s.val) / 2)))
      (norm_nonneg χ)
    have hpow : (n : ℝ) ^ (κ * ε - (1 - s.val) / 2) = L * (n : ℝ) ^ (-(1 - s.val) / 2) := by
      dsimp only [L]
      rw [sub_eq_add_neg, Real.rpow_add hn0, neg_div]
    rw [hpow]
    have hc := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hgC (show 0 ≤ L by positivity)) (by positivity : 0 ≤ (n : ℝ) ^ (-(1 - s.val) / 2))) (norm_nonneg χ)
    dsimp only [G, Tg] at hc
    rw [show 1 - (3 - s.val) / 2 = -(1 - s.val) / 2 by ring] at ht hh
    dsimp only [Tg] at ht
    change Real.sqrt (Q.2 S S) ≤ _ at hh
    nlinarith only [hh, ht, hc]
  · let a₀ := β.val * (Cstar⁻¹ * (n : ℝ) ^ (-κstar * ε))
    have ha₀ : 0 < a₀ := mul_pos β.property (SchurRestriction.periodized_mass_pos hCstar)
    have hlower := SchurRestriction.periodized_scaled_lower β.val β.property hM
    have hsym := hM.2.1
    have hcoerc : ∀ᵐ x ∂ν, (∀ i j, (β.val • M x) i j = (β.val • M x) j i) ∧
        ∀ z : Fin (m : ℕ) → ℝ,
          a₀ * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * (β.val • M x) i j * z j := by
      filter_upwards [hsym, hlower] with x hx hy
      exact ⟨fun i j => by simp only [Matrix.smul_apply, hx.1 i j], hy⟩
    have hsupp : ∀ᵐ x ∂ν, x ∈ Ω := by
      obtain ⟨V, hV⟩ := hpot
      rw [hV.2.2.2]
      apply Measure.smul_absolutelyContinuous.ae_le
      exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hΩ.measurableSet)
    have hh := supremum_restriction_internal d ν Q hQ Ω hΩ hbound hsupp hreal
      n m hnm' (fun x => β.val • M x)
      (SchurRestriction.periodized_scaled_measurable β.val hM) a₀ ha₀ hcoerc c χ u hu
    have ha : a₀⁻¹ ≤ βlo⁻¹ * Cstar * (n : ℝ) ^ (κstar * ε) := by
      have he : a₀⁻¹ = β.val⁻¹ * Cstar * (n : ℝ) ^ (κstar * ε) := by
        dsimp only [a₀]
        rw [mul_inv, mul_inv, inv_inv, ← Real.rpow_neg hn0.le,
          show -(-κstar * ε) = κstar * ε by ring]
        ring
      rw [he]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (inv_anti₀ hβlo hβ.1) (by linarith : 0 ≤ Cstar)) (by positivity)
    have hk : κstar ≤ κ := by dsimp only [κ]; linarith
    have hlast := ha.trans (LocalizedMatrix.loss_mono_internal hn1 hε.le (by positivity) hsupC hk)
    exact hh.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hlast) le_rfl)

/-- The point source in the proof of Lemma 6.4 extends by zero to the
same point source on the enlarged cycle. -/
theorem extend_point_source_internal (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
    (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν) :
    (SchurRestriction.extendSource n m hnm
      (WithLp.toLp 2 (fun i : Fin (n : ℕ) => if i = i₀ then χ else 0))).ofLp =
      fun i => if i = i₀.castLE hnm then χ else 0 := by
  funext i
  rw [ReferenceComparisonPart2.extendSource_sum_internal]
  rw [Finset.sum_eq_single i₀]
  · simp only [ite_true]
  · intro j _ hj
    rw [ite_eq_right hj]
    exact ite_self _
  · simp

/-- See the proof of Lemma 6.4 in the paper, Schur lift. The active inverse is the
already constructed reduced form. Its unique solution is literally the
restriction of the lifted full weak solution, for any scalar form domain. -/
theorem schur_lift_point_source_internal (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q)
    (s : Riesz1.RieszExponent) (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
    (hm : 2 ≤ (m : ℕ)) (K : ℕ) (Cstar κstar γstar ε β : ℝ)
    (hCstar : 1 ≤ Cstar) (hβ : 0 < β)
    (M : X → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M)
    (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν) :
    let f : PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν) :=
      WithLp.toLp 2 (fun i => if i = i₀ then χ else 0)
    let Abar := SchurRestriction.schurForm Q hQ n m hnm s hm K
      Cstar κstar γstar ε β hCstar hβ M hM
    (∃! v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ,
      ∀ w, Abar v w = inner ℝ f (OperatorSchur.vectorValues Q hQ w)) ∧
    ∀ v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ,
      (∀ w, Abar v w = inner ℝ f (OperatorSchur.vectorValues Q hQ w)) →
      ∃ u : Fin (m : ℕ) → Q.1,
        WeightedWeakSolution Q (fun x => β • M x) ⊤
          (fun i => if i = i₀.castLE hnm then χ else 0) u ∧
        ∀ i : Fin (n : ℕ), u (i.castLE hnm) = MatrixEnergy.vectorEquiv Q hQ v i := by
  intro f Abar
  obtain ⟨⟨u, hu, _⟩, hv, hsplit⟩ := SchurRestriction.schur_restriction_weak Q hQ
    n m hnm s hm K Cstar κstar γstar ε β hCstar hβ M hM f
  refine ⟨hv, fun v hv => ⟨u, ?_, ?_⟩⟩
  · simpa only [f, extend_point_source_internal] using hu
  · intro i
    have hs := congrArg Prod.fst (hsplit u v hu hv)
    have hi := SchurRestriction.assemble_restrict_apply Q hQ n m hnm
      ((MatrixEnergy.vectorEquiv Q hQ).symm u) i
    have hi' := congrArg (fun z : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ => z i) hs
    have he := congrArg (ScalarFormHilbert.equiv Q hQ) (hi.symm.trans hi')
    exact he

/-- The auxiliary estimate in the proof of Lemma 6.4 assumes the long-range
coefficient clause of Subsection 6.1. Here `Abar` is the Schur form, so the
unique variational solution is `Abar⁻¹ (χ eᵢ₀)`. -/
theorem schur_auxiliary_estimates_internal (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ) (M₀ : ℕ+)
    (hκstar : 0 < κstar) (hγstar : 0 < γstar) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ∀ Cstar : ℝ, ∀ hCstar : 1 ≤ Cstar,
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    ∀ (n m : ℕ+) (hn : 2 ≤ (n : ℕ)) (hm : 2 ≤ (m : ℕ)),
    ∀ (hnm : 2 * (n : ℕ) ≤ (m : ℕ)),
      (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
    let K := ⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ)
    1 ≤ K → 4 * K ≤ (m : ℕ) →
    ∀ (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d)))
      (ν : Measure (EuclideanSpace ℝ (Fin d))),
      IsOpen Ω → Convex ℝ Ω → Bornology.IsBounded Ω → Ω.Nonempty →
      IsProbabilityMeasure ν →
      (∃ V : EuclideanSpace ℝ (Fin d) → ℝ,
        IsEuclideanGibbsPotential volume ν Ω V 2) →
    ∀ (Q : ScalarFormData ν), IsNeumannRealization Ω Q →
    ∀ (hQ : IsClosedScalarDirichletForm Q), IsConservativeScalarForm Q →
    ∀ (M : EuclideanSpace ℝ (Fin d) → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
      (hM : PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M),
    ∀ i₀ : Fin (n : ℕ), |(i₀.val : ℝ) + 1 - (n : ℝ) / 2| ≤ (n : ℝ) / 4 →
    ∀ χ : Lp ℝ 2 ν,
    let f : PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν) :=
      WithLp.toLp 2 (fun i => if i = i₀ then χ else 0)
    let Abar := SchurRestriction.schurForm Q hQ n m (by omega) s hm K
      Cstar κstar γstar ε β.val hCstar β.property M hM
    (∃! v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ,
      ∀ w, Abar v w = inner ℝ f (OperatorSchur.vectorValues Q hQ w)) ∧
    ∀ v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ,
      (∀ w, Abar v w = inner ℝ f (OperatorSchur.vectorValues Q hQ w)) →
    let v' := MatrixEnergy.vectorEquiv Q hQ v
    let S := ∑ i, v' i
    (∀ j : Fin (n : ℕ), ‖(v' j).val‖ ≤ C * (n : ℝ) ^ (κ * ε) *
      (1 + (Nat.dist j.val i₀.val : ℝ)) ^ (s.val - 2) * ‖χ‖) ∧
    (∑ j, ‖(v' j).val‖) ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ ∧
    ‖S.val‖ ≤ C * (n : ℝ) ^ (κ * ε - (1 - s.val)) * ‖χ‖ ∧
    Real.sqrt (Q.2 S S) ≤ C * (n : ℝ) ^ (κ * ε - (1 - s.val) / 2) * ‖χ‖ ∧
    eLpNorm (fun x => (WithLp.toLp 2 (fun i => (v' i).val x) :
      EuclideanSpace ℝ (Fin (n : ℕ)))) ∞ ν ≤
        ENNReal.ofReal (C * (n : ℝ) ^ (κ * ε)) * eLpNorm χ ∞ ν := by
  obtain ⟨κ, hκ, hbounds⟩ := auxiliary_estimates_of_coefficients_internal hzeta s κstar γstar
    M₀ hκstar hγstar
  refine ⟨κ, hκ, fun ε hε Cstar hCstar βlo βhi hβlo hβhi => ?_⟩
  obtain ⟨C, hC, hbounds⟩ := hbounds ε hε Cstar hCstar βlo βhi hβlo hβhi
  refine ⟨C, hC, ?_⟩
  intro β hβ n m hn hm hnm hmn K hK hKm d Ω ν hΩ hconv hbound hne hprob hpot
    Q hreal hQ hQc M hM i₀ hi₀ χ f Abar
  obtain ⟨hex, hlift⟩ := schur_lift_point_source_internal Q hQ s n m (by omega)
    hm K Cstar κstar γstar ε β.val hCstar β.property M hM i₀ χ
  refine ⟨hex, ?_⟩
  intro v hv v' S
  obtain ⟨u, hu, heq⟩ := hlift v hv
  have he := (hbounds β hβ n m hn hm hnm hmn hK hKm d Ω ν hΩ hconv hbound hne
    hprob hpot Q hreal hQ hQc M hM i₀ hi₀ χ).2 u hu
  simpa only [heq] using he

/-- See Subsection 6.1 of the paper: the actual capped interpolation period satisfies
both size requirements of the optimal decay theorem. No asymptotic threshold
on the active block is used. -/
theorem interpolation_period_bounds_internal (s : Riesz1.RieszExponent)
    (n N : ℕ+) (hN : 4 * (n : ℕ) ≤ (N : ℕ)) :
    let m := min (N : ℕ) (max (2 * (n : ℕ)) ⌈(n : ℝ) ^ (1 / 2 + 1 / s.val)⌉₊)
    2 * (n : ℕ) ≤ m ∧ (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) := by
  intro m
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have ha : 1 ≤ 1 / 2 + 1 / s.val := by
    have hh : 1 < 1 / s.val := (lt_div_iff₀ s.property.1).mpr (by linarith [s.property.2])
    linarith
  have hn : (n : ℝ) ≤ (n : ℝ) ^ (1 / 2 + 1 / s.val) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 ha
  have hp : 1 ≤ (n : ℝ) ^ (1 / 2 + 1 / s.val) := hn1.trans hn
  refine ⟨le_min (by omega) (le_max_left _ _), ?_⟩
  have hm : m ≤ max (2 * (n : ℕ)) ⌈(n : ℝ) ^ (1 / 2 + 1 / s.val)⌉₊ := min_le_right _ _
  apply (show (m : ℝ) ≤ (max (2 * (n : ℕ)) ⌈(n : ℝ) ^ (1 / 2 + 1 / s.val)⌉₊ : ℕ) by exact_mod_cast hm).trans
  rw [Nat.cast_max]
  apply max_le
  · norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    linarith
  · have hh := Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n)
      (1 / 2 + 1 / s.val))
    linarith

/-- See Subsection 6.1 of the paper: the prescribed floor cutoff is admissible on
every enlarged period, including `n=2,3`. The stated smallness range in that
definition implies the weaker product condition used here. -/
theorem interpolation_cutoff_bounds_internal (n m : ℕ+) (hn : 2 ≤ (n : ℕ))
    (hnm : 2 * (n : ℕ) ≤ (m : ℕ)) (η : ℝ) (h : ℕ)
    (hη : 0 ≤ η) (hsmall : (h : ℝ) * η ≤ 1 / 4) :
    let K := ⌊(n : ℝ) ^ η⌋₊ ^ h
    1 ≤ K ∧ 4 * K ≤ (m : ℕ) := by
  intro K
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by positivity
  have hfloor : 1 ≤ ⌊(n : ℝ) ^ η⌋₊ :=
    (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hn1 hη)
  have hK : 1 ≤ K := one_le_pow₀ hfloor
  have hupper : (K : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
    have hh := GlobalReferenceErrorInternal.cutoff_power_le n η 1 zero_le_one h
    simp only [Real.rpow_one, mul_one] at hh
    exact hh.trans (Real.rpow_le_rpow_of_exponent_le hn1 hsmall)
  have hhalf : 2 * K ≤ (n : ℕ) := by
    by_cases hn4 : 4 ≤ (n : ℕ)
    · have hn4R : (4 : ℝ) ≤ n := by exact_mod_cast hn4
      have hsqrt : Real.sqrt (n : ℝ) ≤ (n : ℝ) / 2 := by
        have hs := Real.sq_sqrt hn0.le
        have hs0 := Real.sqrt_nonneg (n : ℝ)
        nlinarith [mul_nonneg hn0.le (sub_nonneg.mpr hn4R)]
      have hquarter : (n : ℝ) ^ (1 / 4 : ℝ) ≤ Real.sqrt (n : ℝ) := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
      have hh := hupper.trans (hquarter.trans hsqrt)
      have hnat : (2 * K : ℕ) ≤ (n : ℕ) := by
        have hr : (2 : ℝ) * K ≤ n := by linarith
        exact_mod_cast hr
      exact hnat
    · have hn16 : (n : ℝ) < 16 := by
        have hn4' : (n : ℕ) < 4 := by omega
        exact_mod_cast (show (n : ℕ) < 16 by omega)
      have hp4 : ((n : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = (n : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
        norm_num
      have hp2 : (n : ℝ) ^ (1 / 4 : ℝ) < 2 := by
        by_contra hh
        have hh' := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (le_of_not_gt hh) 4
        norm_num only [show (2 : ℝ) ^ 4 = 16 by norm_num] at hh'
        linarith
      have hK2 : K < 2 := by exact_mod_cast (hupper.trans_lt hp2)
      omega
  exact ⟨hK, by omega⟩

end Riesz2.AuxiliaryMean
