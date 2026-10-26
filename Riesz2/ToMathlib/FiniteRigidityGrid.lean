/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic

/-!
# Finite dyadic sampling of positive exponents

The grid is selected using only its endpoints, before any scale or temperature.
This supplies the finite-grid step in Appendix C.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Riesz2.FiniteRigidityGrid

/-- A single finite dyadic grid approximates every target in a fixed
positive interval from below, with a loss of at most two. -/
theorem exists_grid {l u : ℝ} (hl : 0 < l) (hu : 0 < u) :
    ∃ J : ℕ, ∀ q : ℝ, l ≤ q → q ≤ u →
      ∃ j : Fin (J + 1), q / 2 ≤ u * (1 / 2 : ℝ) ^ j.val ∧
        u * (1 / 2 : ℝ) ^ j.val ≤ q := by
  obtain ⟨J, hJ⟩ := exists_pow_lt_of_lt_one (div_pos hl hu)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hJl : u * (1 / 2 : ℝ) ^ J ≤ l := by
    have h := (lt_div_iff₀ hu).mp hJ
    nlinarith
  refine ⟨J, fun q hlq hqu => ?_⟩
  have he : ∃ j : ℕ, u * (1 / 2 : ℝ) ^ j ≤ q := ⟨J, hJl.trans hlq⟩
  let j := Nat.find he
  have hj : u * (1 / 2 : ℝ) ^ j ≤ q := Nat.find_spec he
  have hjJ : j ≤ J := Nat.find_min' he (hJl.trans hlq)
  refine ⟨⟨j, by omega⟩, ?_, hj⟩
  change q / 2 ≤ u * (1 / 2 : ℝ) ^ j
  cases hj0 : j with
  | zero => simpa only [hj0, pow_zero, mul_one] using (by linarith : q / 2 ≤ u)
  | succ k =>
    have hk : ¬u * (1 / 2 : ℝ) ^ k ≤ q := Nat.find_min he (by dsimp [j] at hj0; omega)
    have hk' := lt_of_not_ge hk
    rw [pow_succ]
    nlinarith

/-- The selected parameter simultaneously fits the deviation threshold
and gives a scale-independent lower bound for the tail exponent.
Here `t = log k / log n`, and the large-block range is `η/2 ≤ t ≤ 1`. -/
theorem exists_scale_grid {η u : ℝ} (hη : 0 < η) (hu : 0 < u)
    (hηu : η / 2 ≤ u) (hu1 : u ≤ 1) :
    ∃ J : ℕ, ∀ t : ℝ, η / 2 ≤ t → t ≤ 1 →
      ∃ j : Fin (J + 1),
        0 < u * (1 / 2 : ℝ) ^ j.val ∧
        u * (1 / 2 : ℝ) ^ j.val ≤ u ∧
        t * (u * (1 / 2 : ℝ) ^ j.val) ≤ η / 2 ∧
        η * u / 4 ≤ t * (u * (1 / 2 : ℝ) ^ j.val) := by
  obtain ⟨J, hJ⟩ := exists_grid (l := η / 2) (by positivity) hu
  refine ⟨J, fun t ht ht1 => ?_⟩
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  let q := min u (η / (2 * t))
  have hq : η / 2 ≤ q := le_min hηu (by
    apply (le_div_iff₀ (by positivity : 0 < 2 * t)).mpr
    nlinarith)
  obtain ⟨j, hjl, hju⟩ := hJ q hq (min_le_left _ _)
  refine ⟨j, by positivity, hju.trans (min_le_left _ _), ?_, ?_⟩
  · have hb := hju.trans (min_le_right _ _)
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * t)).mp hb
    nlinarith
  · by_cases hcap : u ≤ η / (2 * t)
    · dsimp only [q] at hjl
      rw [min_eq_left hcap] at hjl
      nlinarith [mul_le_mul_of_nonneg_right ht hu.le,
        mul_le_mul_of_nonneg_left hjl ht0.le]
    · dsimp only [q] at hjl
      rw [min_eq_right (le_of_not_ge hcap)] at hjl
      have hh := (div_le_iff₀ (by positivity : 0 < 2 * t)).mp
        (show η / (2 * t) ≤ 2 * (u * (1 / 2 : ℝ) ^ j.val) by linarith)
      nlinarith

/-- The finite grid controls both real powers on every large block.
The lower bound on the tail power is linear in `η`. -/
theorem exists_power_grid {η u d : ℝ} (hη : 0 < η) (hu : 0 < u)
    (hηu : η / 2 ≤ u) (hu1 : u ≤ 1) (hd : 0 < d) :
    ∃ J : ℕ, ∀ n k : ℝ, 1 < n → n ^ (η / 2) ≤ k → k ≤ n →
      ∃ j : Fin (J + 1),
        0 < u * (1 / 2 : ℝ) ^ j.val ∧
        u * (1 / 2 : ℝ) ^ j.val ≤ u ∧
        k ^ (u * (1 / 2 : ℝ) ^ j.val) ≤ n ^ (η / 2) ∧
        n ^ (η * u / (4 * d)) ≤ k ^ (u * (1 / 2 : ℝ) ^ j.val / d) := by
  obtain ⟨J, hJ⟩ := exists_scale_grid hη hu hηu hu1
  refine ⟨J, fun n k hn hk hkn => ?_⟩
  have hn0 : 0 < n := lt_trans zero_lt_one hn
  have hlogn : 0 < Real.log n := Real.log_pos hn
  have hk0 : 0 < k := lt_of_lt_of_le (Real.rpow_pos_of_pos hn0 _) hk
  let t := Real.log k / Real.log n
  have ht : η / 2 ≤ t := by
    apply (le_div_iff₀ hlogn).mpr
    have h := Real.log_le_log (Real.rpow_pos_of_pos hn0 _) hk
    rw [Real.log_rpow hn0] at h
    nlinarith
  have ht1 : t ≤ 1 := by
    apply (div_le_iff₀ hlogn).mpr
    simpa using Real.log_le_log hk0 hkn
  obtain ⟨j, hj0, hju, hjth, hjtail⟩ := hJ t ht ht1
  have hlog : Real.log k = t * Real.log n := by
    dsimp [t]
    field_simp
  refine ⟨j, hj0, hju, ?_, ?_⟩
  · rw [Real.rpow_def_of_pos hk0, Real.rpow_def_of_pos hn0]
    apply Real.exp_le_exp.mpr
    rw [hlog]
    nlinarith [mul_le_mul_of_nonneg_right hjth hlogn.le]
  · rw [Real.rpow_def_of_pos hk0, Real.rpow_def_of_pos hn0]
    apply Real.exp_le_exp.mpr
    have he : Real.log k * (u * (1 / 2 : ℝ) ^ j.val / d) =
        (t * (u * (1 / 2 : ℝ) ^ j.val)) / d * Real.log n := by
      rw [hlog]
      ring
    rw [he]
    have h := div_le_div_of_nonneg_right hjtail hd.le
    have hh := mul_le_mul_of_nonneg_right h hlogn.le
    convert hh using 1
    ring

/-- A finite set of stretched-exponential estimates admits common positive
constants. No uniformity in an infinite exponent family is assumed. -/
theorem internal_uniform_finite_tails {ι A : Type*} {Ω : A → Type*}
    [Fintype ι] [Nonempty ι] [∀ a, MeasurableSpace (Ω a)]
    (μ : ∀ a, Measure (Ω a)) (E : ∀ (_i : ι) a, Set (Ω a))
    (v : ι → A → ℝ) (hv : ∀ i a, 0 ≤ v i a)
    (h : ∀ i, ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ a,
      μ a (E i a) ≤ ENNReal.ofReal (C * Real.exp (-c * v i a))) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ i a,
      μ a (E i a) ≤ ENNReal.ofReal (C * Real.exp (-c * v i a)) := by
  classical
  choose C c hC hc htail using h
  let C₀ := Finset.univ.sup' Finset.univ_nonempty C
  let c₀ := Finset.univ.inf' Finset.univ_nonempty c
  have hC₀ : 0 < C₀ := (hC (Classical.arbitrary ι)).trans_le
    (Finset.le_sup' C (Finset.mem_univ _))
  have hc₀ : 0 < c₀ := (Finset.lt_inf'_iff _).mpr (fun i _ => hc i)
  refine ⟨C₀, c₀, hC₀, hc₀, fun i a => (htail i a).trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  have hCc : C i ≤ C₀ := Finset.le_sup' C (Finset.mem_univ _)
  have hcc : c₀ ≤ c i := Finset.inf'_le c (Finset.mem_univ _)
  exact mul_le_mul hCc (Real.exp_le_exp.mpr (by nlinarith [hv i a]))
    (Real.exp_pos _).le hC₀.le

/-- Finite-grid amplification for large blocks. This internal interface
allows arbitrary families of laws and block masses. The supplied rigidity
estimates have their constants before every member of the family. -/
theorem internal_large_block_tails {A : Type*} {Ω : A → Type*}
    [∀ a, MeasurableSpace (Ω a)]
    (μ : ∀ a, Measure (Ω a)) (S : ∀ a, ℕ → Ω a → ℝ) (R : A → ℕ)
    {σ η u d : ℝ} (hη : 0 < η) (hu : 0 < u) (hηu : η / 2 ≤ u)
    (hu1 : u ≤ 1) (hd : 0 < d)
    (hRig : ∀ b : ℝ, 0 < b → b ≤ u → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ a k, 1 ≤ k → k ≤ R a →
        μ a {ω | (k : ℝ) ^ (σ + b) ≤ |S a k ω - k|} ≤
          ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ (b / d)))) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (a : A) (n k : ℕ), 2 ≤ n → 1 ≤ k → k ≤ R a →
        (n : ℝ) ^ (η / 2) ≤ k → k ≤ n →
        μ a {ω | (n : ℝ) ^ η * (k : ℝ) ^ σ < |S a k ω - k|} ≤
          ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ (η * u / (4 * d)))) := by
  obtain ⟨J, hJ⟩ := exists_power_grid hη hu hηu hu1 hd
  let b := fun j : Fin (J + 1) => u * (1 / 2 : ℝ) ^ j.val
  have hb0 (j) : 0 < b j := by dsimp [b]; positivity
  have hbu (j) : b j ≤ u := by
    dsimp [b]
    exact mul_le_of_le_one_right hu.le
      (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  let E := fun j (q : A × ℕ) =>
    {ω | (q.2 : ℝ) ^ (σ + b j) ≤ |S q.1 q.2 ω - q.2|}
  let v := fun j (q : A × ℕ) => (q.2 : ℝ) ^ (b j / d)
  -- Restrict the parameter carrier instead of asking for estimates outside
  -- the admissible block range.
  let T := {q : A × ℕ // 1 ≤ q.2 ∧ q.2 ≤ R q.1}
  obtain ⟨C, c, hC, hc, htail⟩ := internal_uniform_finite_tails
    (ι := Fin (J + 1)) (A := T)
    (fun q => μ q.val.1) (fun j q => E j q.val) (fun j q => v j q.val)
    (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) (by
      intro j
      obtain ⟨C, c, hC, hc, ht⟩ := hRig (b j) (hb0 j) (hbu j)
      exact ⟨C, c, hC, hc, fun q => ht q.val.1 q.val.2 q.property.1 q.property.2⟩)
  refine ⟨C, c, hC, hc, fun a n k hn hk hkR hnk hkn => ?_⟩
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  obtain ⟨j, _, _, hjth, hjtail⟩ := hJ n k hn1 hnk (by exact_mod_cast hkn)
  have hsmall : (n : ℝ) ^ (η / 2) ≤ (n : ℝ) ^ η :=
    Real.rpow_le_rpow_of_exponent_le hn1.le (by linarith)
  have hsub : {ω | (n : ℝ) ^ η * (k : ℝ) ^ σ < |S a k ω - k|} ⊆ E j (a, k) := by
    intro ω hω
    change (k : ℝ) ^ (σ + b j) ≤ _
    rw [Real.rpow_add hk0]
    have hpow : (k : ℝ) ^ b j ≤ (n : ℝ) ^ η := hjth.trans hsmall
    have hmul := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hk0.le σ)
    exact (by nlinarith :
      (k : ℝ) ^ σ * (k : ℝ) ^ b j ≤ (n : ℝ) ^ η * (k : ℝ) ^ σ).trans hω.le
  refine (measure_mono hsub).trans ((htail j ⟨(a, k), hk, hkR⟩).trans ?_)
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  change -c * (k : ℝ) ^ (b j / d) ≤ _
  nlinarith

/-- The containing-block scale exists eventually. All bounds needed for
short blocks are explicit, including its fit inside an `n`-block. -/
theorem containing_block_scale {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 4) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 2 ≤ n →
      ∃ h : ℕ, 1 ≤ h ∧ h ≤ n ∧
        (n : ℝ) ^ (η / 2) ≤ h ∧ 2 * (h : ℝ) ≤ (n : ℝ) ^ η := by
  have he : ∀ᶠ n : ℕ in atTop,
      4 ≤ (n : ℝ) ^ (η / 2) ∧ 4 ≤ (n : ℝ) ^ (1 - η / 2) := by
    apply Filter.Eventually.and
    · exact ((tendsto_rpow_atTop (by positivity : 0 < η / 2)).comp
        tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 4)
    · exact ((tendsto_rpow_atTop (by linarith : 0 < 1 - η / 2)).comp
        tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 4)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp he
  refine ⟨n₀, fun n hn hn2 => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  obtain ⟨hp, hq⟩ := hn₀ n hn
  let p := (n : ℝ) ^ (η / 2)
  let h := ⌈p⌉₊
  have hph : p ≤ h := Nat.le_ceil p
  have hhp : (h : ℝ) ≤ 2 * p := by
    have hlt := Nat.ceil_lt_add_one (Real.rpow_nonneg hn0.le (η / 2))
    dsimp [h, p]
    linarith
  have hpq : p * (n : ℝ) ^ (1 - η / 2) = n := by
    dsimp [p]
    rw [← Real.rpow_add hn0]
    rw [show η / 2 + (1 - η / 2) = 1 by ring, Real.rpow_one]
  have hpp : p * p = (n : ℝ) ^ η := by
    dsimp [p]
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  have hp0 : 0 < p := Real.rpow_pos_of_pos hn0 _
  have hhn : (h : ℝ) ≤ n := by nlinarith [mul_le_mul_of_nonneg_left hq hp0.le]
  have hh0 : (0 : ℝ) < h := hp0.trans_le hph
  have hh1 : 1 ≤ h := by exact_mod_cast (show (0 : ℕ) < h by exact_mod_cast hh0)
  refine ⟨h, hh1, by exact_mod_cast hhn, hph, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hp hp0.le]

/-- A short-block deviation forces a deviation of its containing block.
Only positivity and monotonicity of the actual block masses are used.
This is an internal probability estimate, with its rigidity input explicit. -/
theorem internal_short_block_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : ℕ → Ω → ℝ) {σ η b d C c : ℝ}
    (hσ : 0 ≤ σ) (hb : 0 < b) (hd : 0 < d) (hc : 0 < c) (hC : 0 ≤ C)
    (hsmall : σ + b ≤ 1) (hS : ∀ k ω, 0 ≤ S k ω)
    (hmono : ∀ ω, Monotone (fun k => S k ω))
    {n k h : ℕ} (hk : 1 ≤ k) (hh : 1 ≤ h) (hkh : k ≤ h)
    (hscale : (n : ℝ) ^ (η / 2) ≤ h) (hupper : 2 * (h : ℝ) ≤ (n : ℝ) ^ η)
    (hRig : μ {ω | (h : ℝ) ^ (σ + b) ≤ |S h ω - h|} ≤
      ENNReal.ofReal (C * Real.exp (-c * (h : ℝ) ^ (b / d)))) :
    μ {ω | (n : ℝ) ^ η * (k : ℝ) ^ σ < |S k ω - k|} ≤
      ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ (η * b / (2 * d)))) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hkpow : 1 ≤ (k : ℝ) ^ σ := Real.one_le_rpow hk1 hσ
  have hnη0 : 0 ≤ (n : ℝ) ^ η := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsub : {ω | (n : ℝ) ^ η * (k : ℝ) ^ σ < |S k ω - k|} ⊆
      {ω | (h : ℝ) ^ (σ + b) ≤ |S h ω - h|} := by
    intro ω hω
    have hkr : (k : ℝ) ≤ h := by exact_mod_cast hkh
    have hth : (n : ℝ) ^ η ≤ (n : ℝ) ^ η * (k : ℝ) ^ σ := by
      nlinarith [mul_le_mul_of_nonneg_left hkpow hnη0]
    have hkT : (k : ℝ) ≤ (n : ℝ) ^ η * (k : ℝ) ^ σ := by linarith
    have hpos : (n : ℝ) ^ η * (k : ℝ) ^ σ < S k ω - k := by
      by_contra h
      have hle := abs_le.mpr
        (show -((n : ℝ) ^ η * (k : ℝ) ^ σ) ≤ S k ω - k ∧
          S k ω - k ≤ (n : ℝ) ^ η * (k : ℝ) ^ σ from
            ⟨by linarith [hS k ω], le_of_not_gt h⟩)
      exact (not_lt_of_ge hle) hω
    have hhpow : (h : ℝ) ^ (σ + b) ≤ h :=
      (Real.rpow_le_rpow_of_exponent_le hh1 hsmall).trans_eq (Real.rpow_one _)
    have hmass := hmono ω hkh
    have hfinal : (h : ℝ) ^ (σ + b) ≤ S h ω - h := by linarith
    exact hfinal.trans (le_abs_self _)
  refine (measure_mono hsub).trans (hRig.trans ?_)
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.mpr
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg n) _) hscale
    (show 0 ≤ b / d by positivity)
  rw [← Real.rpow_mul (Nat.cast_nonneg n)] at hp
  have hid : η / 2 * (b / d) = η * b / (2 * d) := by ring
  rw [hid] at hp
  nlinarith

/-- Amplification of a family of rigidity estimates to all block sizes.
The tail power is `η*u/(4*d)`: its coefficient is fixed before `η`.
The constants depend on only finitely many input exponents. -/
theorem internal_all_block_tails {A : Type*} {Ω : A → Type*}
    [∀ a, MeasurableSpace (Ω a)]
    (μ : ∀ a, Measure (Ω a)) (S : ∀ a, ℕ → Ω a → ℝ) (R : A → ℕ)
    {σ η u d : ℝ} (hσ : 0 ≤ σ) (hη : 0 < η) (hη1 : η ≤ 1 / 4)
    (hu : 0 < u) (hηu : η / 2 ≤ u) (hu1 : u ≤ 1) (hd : 0 < d)
    (hsmall : σ + u ≤ 1)
    (hS : ∀ a k ω, 0 ≤ S a k ω) (hmono : ∀ a ω, Monotone (fun k => S a k ω))
    (hRig : ∀ b : ℝ, 0 < b → b ≤ u → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ a k, 1 ≤ k → k ≤ R a →
        μ a {ω | (k : ℝ) ^ (σ + b) ≤ |S a k ω - k|} ≤
          ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ (b / d)))) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ n₀ : ℕ,
      ∀ (a : A) (n k : ℕ), n₀ ≤ n → 2 ≤ n → n ≤ R a → 1 ≤ k → k ≤ n →
        μ a {ω | (n : ℝ) ^ η * (k : ℝ) ^ σ < |S a k ω - k|} ≤
          ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ (η * u / (4 * d)))) := by
  obtain ⟨Cl, cl, hCl, hcl, hl⟩ := internal_large_block_tails μ S R
    hη hu hηu hu1 hd hRig
  obtain ⟨Cs, cs, hCs, hcs, hs⟩ := hRig (u / 2) (by positivity) (by linarith)
  obtain ⟨n₀, hscale⟩ := containing_block_scale hη hη1
  let C := max Cl Cs
  let c := min cl cs
  have hC : 0 < C := hCl.trans_le (le_max_left _ _)
  have hc : 0 < c := lt_min hcl hcs
  have hcompare (D e v : ℝ) (hD : D ≤ C) (he : c ≤ e) (hv : 0 ≤ v) :
      ENNReal.ofReal (D * Real.exp (-e * v)) ≤
        ENNReal.ofReal (C * Real.exp (-c * v)) := by
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul hD (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_pos _).le hC.le
  refine ⟨C, c, hC, hc, n₀, fun a n k hn hn2 hnR hk hkn => ?_⟩
  obtain ⟨h, hh, hhn, hpow, hupp⟩ := hscale n hn hn2
  by_cases hlarge : (n : ℝ) ^ (η / 2) ≤ k
  · exact (hl a n k hn2 hk (hkn.trans hnR) hlarge hkn).trans
      (hcompare Cl cl _ (le_max_left _ _) (min_le_left _ _) (by positivity))
  · have hkh : k ≤ h := by
      have hkr : (k : ℝ) < h := (lt_of_not_ge hlarge).trans_le hpow
      exact_mod_cast hkr.le
    have hbound := internal_short_block_tail (μ a) (S a) hσ
      (show 0 < u / 2 by positivity) hd hcs hCs.le
      (show σ + u / 2 ≤ 1 by linarith) (hS a) (hmono a)
      hk hh hkh hpow hupp (hs a h hh (hhn.trans hnR))
    have heq : η * (u / 2) / (2 * d) = η * u / (4 * d) := by ring
    rw [heq] at hbound
    exact hbound.trans
      (hcompare Cs cs _ (le_max_right _ _) (min_le_right _ _) (by positivity))

/-- The all-size version of finite-grid amplification. Bounded sizes use
only that each law is a probability, without modifying the tail power. -/
theorem internal_all_block_tails_all_sizes {A : Type*} {Ω : A → Type*}
    [∀ a, MeasurableSpace (Ω a)]
    (μ : ∀ a, Measure (Ω a)) (S : ∀ a, ℕ → Ω a → ℝ) (R : A → ℕ)
    (hμ : ∀ a, IsProbabilityMeasure (μ a))
    {σ η u d : ℝ} (hσ : 0 ≤ σ) (hη : 0 < η) (hη1 : η ≤ 1 / 4)
    (hu : 0 < u) (hηu : η / 2 ≤ u) (hu1 : u ≤ 1) (hd : 0 < d)
    (hsmall : σ + u ≤ 1)
    (hS : ∀ a k ω, 0 ≤ S a k ω) (hmono : ∀ a ω, Monotone (fun k => S a k ω))
    (hRig : ∀ b : ℝ, 0 < b → b ≤ u → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ a k, 1 ≤ k → k ≤ R a →
        μ a {ω | (k : ℝ) ^ (σ + b) ≤ |S a k ω - k|} ≤
          ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ (b / d)))) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (a : A) (n k : ℕ), 2 ≤ n → n ≤ R a → 1 ≤ k → k ≤ n →
        μ a {ω | (n : ℝ) ^ η * (k : ℝ) ^ σ < |S a k ω - k|} ≤
          ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ (η * u / (4 * d)))) := by
  obtain ⟨C, c, hC, hc, n₀, ht⟩ := internal_all_block_tails μ S R
    hσ hη hη1 hu hηu hu1 hd hsmall hS hmono hRig
  let δ := η * u / (4 * d)
  let D := C + Real.exp (c * (n₀ : ℝ) ^ δ)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, c, hD, hc, fun a n k hn hnR hk hkn => ?_⟩
  by_cases hn₀ : n₀ ≤ n
  · refine (ht a n k hn₀ hn hnR hk hkn).trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    dsimp [D]
    linarith [Real.exp_pos (c * (n₀ : ℝ) ^ δ)]
  · have := hμ a
    apply (prob_le_one (μ := μ a)).trans
    change (1 : ℝ≥0∞) ≤ ENNReal.ofReal (D * Real.exp (-c * (n : ℝ) ^ δ))
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have hp : (n : ℝ) ^ δ ≤ (n₀ : ℝ) ^ δ :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (by omega : n ≤ n₀))
        (show 0 ≤ δ by dsimp [δ]; positivity)
    have he : 1 ≤ Real.exp (c * (n₀ : ℝ) ^ δ) * Real.exp (-c * (n : ℝ) ^ δ) := by
      rw [← Real.exp_add, ← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      nlinarith
    have hCD : Real.exp (c * (n₀ : ℝ) ^ δ) ≤ D := by dsimp [D]; linarith
    exact he.trans (mul_le_mul_of_nonneg_right hCD (Real.exp_pos _).le)

end Riesz2.FiniteRigidityGrid
