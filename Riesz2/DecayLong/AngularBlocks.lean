/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.DiscreteInterpolationPart2

/-!
# Smooth blocks supported in angular annuli

The partition in the proof of Lemma 5.9 is constructed with a narrow
smooth cutoff of the sine radius. Its support lies in the angular annulus
`[t,4t]`. This avoids requiring smoothness of angular distance at the antipode.
-/

@[expose] public section
noncomputable section

open Set Filter Topology
open scoped BigOperators ContDiff

namespace Riesz2.DiscreteInterpolation

local instance angularBlocksPeriodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

namespace AngularCutoff

/-- The narrower cutoff for the angular annuli in Lemma 5.9 of the paper:
one up to 1, zero from 5/4, and smooth on the whole line. -/
def cutoff (x : ℝ) : ℝ := CutoffApproximation.scalarCutoff (4 * x - 3)

/-- Smoothness of the cutoff used by Lemma 5.9 of the paper. -/
theorem cutoff_contDiff : ContDiff ℝ ∞ cutoff :=
  CutoffApproximation.scalarCutoff_contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

/-- Positivity of the cutoff in Lemma 5.9 of the paper. -/
theorem cutoff_nonneg (x : ℝ) : 0 ≤ cutoff x := CutoffApproximation.scalarCutoff_nonneg _

/-- The cutoff of Lemma 5.9 of the paper is at most one. -/
theorem cutoff_le_one (x : ℝ) : cutoff x ≤ 1 := CutoffApproximation.scalarCutoff_le_one _

/-- Monotonicity of the cutoff in Lemma 5.9 of the paper. -/
theorem cutoff_antitone : Antitone cutoff := by
  intro x y h
  exact CutoffApproximation.scalarCutoff_antitone (by linarith)

/-- The inner plateau for the partition of Lemma 5.9 of the paper. -/
theorem cutoff_eq_one {x : ℝ} (hx : x ≤ 1) : cutoff x = 1 :=
  CutoffApproximation.scalarCutoff_eq_one (by linarith)

/-- The outer plateau for the partition of Lemma 5.9 of the paper. -/
theorem cutoff_eq_zero {x : ℝ} (hx : 5 / 4 ≤ x) : cutoff x = 0 :=
  CutoffApproximation.scalarCutoff_eq_zero (by linarith)

/-- All derivatives of the fixed narrow cutoff in Lemma 5.9 of the paper
are bounded before any scale or cycle is chosen. -/
theorem cutoff_derivative_bound (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, |iteratedDeriv k cutoff x| ≤ C := by
  obtain ⟨C, hC, hb⟩ := CutoffApproximation.scalarCutoff_derivative_bound k
  refine ⟨4 ^ k * C, by positivity, fun x => ?_⟩
  have hc : ContDiff ℝ ∞ (fun y : ℝ => CutoffApproximation.scalarCutoff (y + -3)) :=
    CutoffApproximation.scalarCutoff_contDiff.comp (contDiff_id.add contDiff_const)
  have he := congrFun (iteratedDeriv_comp_const_mul (n := k)
    (hc.of_le (by simp)) (4 : ℝ)) x
  change iteratedDeriv k (fun y => CutoffApproximation.scalarCutoff (4 * y + -3)) x = _ at he
  change |iteratedDeriv k (fun y => CutoffApproximation.scalarCutoff (4 * y - 3)) x| ≤ _
  simp only [sub_eq_add_neg, he, iteratedDeriv_comp_add_const, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 ^ k)]
  exact mul_le_mul_of_nonneg_left (hb _) (by positivity)

/-- The radial cutoff step of Lemma 5.9 of the paper. -/
def shell (t : ℝ) (_ht : 0 < t) (r : ℝ) : ℝ := cutoff (r / (2 * t)) - cutoff (r / t)

/-- The radial cutoff step of Lemma 5.9 of the paper. -/
theorem shell_contDiff (t : ℝ) (ht : 0 < t) : ContDiff ℝ ∞ (shell t ht) :=
  (cutoff_contDiff.comp (contDiff_id.div_const _)).sub
    (cutoff_contDiff.comp (contDiff_id.div_const _))

/-- The radial cutoff step of Lemma 5.9 of the paper. -/
theorem shell_nonneg {t : ℝ} (ht : 0 < t) (r : ℝ) : 0 ≤ shell t ht r := by
  by_cases hr : r ≤ t
  · have h1 : r / t ≤ 1 := (div_le_one ht).mpr hr
    have h2 : r / (2 * t) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    simp only [shell, cutoff_eq_one h1, cutoff_eq_one h2, sub_self, le_refl]
  · apply sub_nonneg.mpr
    apply cutoff_antitone
    exact div_le_div_of_nonneg_left (by linarith) ht (by linarith)

/-- The radial cutoff step of Lemma 5.9 of the paper. -/
theorem shell_le_one (t r : ℝ) (ht : 0 < t) : shell t ht r ≤ 1 := by
  unfold shell
  linarith [cutoff_le_one (r / (2 * t)), cutoff_nonneg (r / t)]

/-- The radial cutoff step of Lemma 5.9 of the paper. -/
theorem shell_eq_zero_of_le {t r : ℝ} (ht : 0 < t) (hr : r ≤ t) : shell t ht r = 0 := by
  have h1 : r / t ≤ 1 := (div_le_one ht).mpr hr
  have h2 : r / (2 * t) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  simp only [shell, cutoff_eq_one h1, cutoff_eq_one h2, sub_self]

/-- The radial cutoff step of Lemma 5.9 of the paper. -/
theorem shell_eq_zero_of_ge {t r : ℝ} (ht : 0 < t) (hr : (5 / 2) * t ≤ r) :
    shell t ht r = 0 := by
  have h1 : 5 / 4 ≤ r / t := (le_div_iff₀ ht).mpr (by linarith)
  have h2 : 5 / 4 ≤ r / (2 * t) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  simp only [shell, cutoff_eq_zero h1, cutoff_eq_zero h2, sub_self]

/-- Exact rescaling of every derivative. For Lemma 5.9 of the paper. -/
theorem iteratedDeriv_scaledCutoff (k : ℕ) (t r : ℝ) :
    iteratedDeriv k (fun x => cutoff (x / t)) r =
      t⁻¹ ^ k * iteratedDeriv k cutoff (r / t) := by
  simpa only [div_eq_mul_inv, mul_comm _ t⁻¹] using
    congrFun (iteratedDeriv_comp_const_mul
      (cutoff_contDiff.of_le (by simp)) t⁻¹) r

/-- All-order derivative bounds for radial dyadic shells, uniform over positive scales. For Lemma 5.9 of the paper. -/
theorem shell_derivative_bound (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t (ht : 0 < t), ∀ r,
      |iteratedDeriv k (shell t ht) r| ≤ C / t ^ k := by
  obtain ⟨B, hB, hb⟩ := cutoff_derivative_bound k
  refine ⟨2 * B, by positivity, fun t ht r => ?_⟩
  have hscale : (2 * t)⁻¹ ^ k ≤ t⁻¹ ^ k :=
    pow_le_pow_left₀ (by positivity) (inv_anti₀ ht (by linarith)) k
  have h1 : |iteratedDeriv k (fun x => cutoff (x / (2 * t))) r| ≤
      t⁻¹ ^ k * B := by
    rw [iteratedDeriv_scaledCutoff, abs_mul, abs_of_nonneg (by positivity)]
    exact (mul_le_mul_of_nonneg_left (hb _) (by positivity)).trans
      (mul_le_mul_of_nonneg_right hscale hB.le)
  have h2 : |iteratedDeriv k (fun x => cutoff (x / t)) r| ≤ t⁻¹ ^ k * B := by
    rw [iteratedDeriv_scaledCutoff, abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hb _) (by positivity)
  have he := iteratedDeriv_sub (n := k) (x := r)
    ((cutoff_contDiff.comp (contDiff_id.div_const (2 * t))).of_le (by simp)).contDiffAt
    ((cutoff_contDiff.comp (contDiff_id.div_const t)).of_le (by simp)).contDiffAt
  change |iteratedDeriv k ((fun x => cutoff (x / (2 * t))) -
    (fun x => cutoff (x / t))) r| ≤ _
  dsimp only [Function.comp_def, id_eq] at he
  rw [he]
  calc
    _ ≤ |iteratedDeriv k (fun x => cutoff (x / (2 * t))) r| +
        |iteratedDeriv k (fun x => cutoff (x / t)) r| := abs_sub _ _
    _ ≤ t⁻¹ ^ k * B + t⁻¹ ^ k * B := add_le_add h1 h2
    _ = (2 * B) / t ^ k := by rw [div_eq_mul_inv, inv_pow]; ring

/-- The finite dyadic decomposition telescopes, including the empty family. For Lemma 5.9 of the paper. -/
theorem sum_shell (t r : ℝ) (ht : 0 < t) (n : ℕ) :
    (∑ j ∈ Finset.range n, shell ((2 : ℝ) ^ j * t) (by positivity) r) =
      cutoff (r / (2 ^ n * t)) - cutoff (r / t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, shell]
    have he : (2 : ℝ) * (2 ^ n * t) = 2 ^ (n + 1) * t := by ring
    rw [he]
    ring

/-- A finite shell family is a partition of unity wherever the endpoint cutoffs
are respectively one and zero. This is the scalar telescoping in Lemma 5.9 of the paper. -/
theorem sum_shell_eq_one {t r : ℝ} (ht : 0 < t) (n : ℕ)
    (hlo : 2 * t ≤ r) (hhi : r ≤ 2 ^ n * t) :
    (∑ j ∈ Finset.range n, shell ((2 : ℝ) ^ j * t) (by positivity) r) = 1 := by
  rw [sum_shell t r ht, cutoff_eq_one ((div_le_one (by positivity)).mpr hhi),
    cutoff_eq_zero ((le_div_iff₀ ht).mpr (by linarith)), sub_zero]


end AngularCutoff

/-- The angular block in Lemma 5.9 of the paper, using the fixed
smooth cutoff and radial shell. -/
def angularBlock (t : ℝ) (ht : 0 < t) (θ : ℝ) : ℝ :=
  AngularCutoff.shell t ht (frequencyRadius θ)

/-- The explicit blocks in Lemma 5.9 of the paper are periodic. -/
theorem periodic_angularBlock (t : ℝ) (ht : 0 < t) :
    Function.Periodic (angularBlock t ht) (2 * Real.pi) :=
  periodic_frequencyRadius.comp (AngularCutoff.shell t ht)

/-- The block has precisely the required annular support enclosure. For Lemma 5.9 of the paper. -/
theorem angularBlock_support_sine {t : ℝ} (ht : 0 < t) :
    Function.support (angularBlock t ht) ⊆
      {θ | t ≤ frequencyRadius θ ∧ frequencyRadius θ ≤ (5 / 2) * t} := by
  intro θ hθ
  constructor
  · by_contra h
    exact hθ (AngularCutoff.shell_eq_zero_of_le ht (le_of_not_ge h))
  · by_contra h
    exact hθ (AngularCutoff.shell_eq_zero_of_ge ht (le_of_not_ge h))

/-- Every block takes values in `[0,1]`. For Lemma 5.9 of the paper. -/
theorem angularBlock_bounds (t : ℝ) (ht : 0 < t) (θ : ℝ) :
    0 ≤ angularBlock t ht θ ∧ angularBlock t ht θ ≤ 1 :=
  ⟨AngularCutoff.shell_nonneg ht _, AngularCutoff.shell_le_one _ _ ht⟩

/-- A block vanishes on a neighborhood of every zero of the radius.
This is the seam cancellation in Lemma 5.9 of the paper. -/
theorem angularBlock_eventually_zero {t θ : ℝ} (ht : 0 < t)
    (hθ : frequencyRadius θ < t) :
    angularBlock t ht =ᶠ[𝓝 θ] (fun _ => 0) := by
  filter_upwards [continuous_frequencyRadius.continuousAt.eventually (gt_mem_nhds hθ)] with y hy
  exact AngularCutoff.shell_eq_zero_of_le ht hy.le

/-- The explicit angular blocks of Lemma 5.9 of the paper are smooth at the seam as
well as at every nonzero frequency. -/
theorem angularBlock_contDiff (t : ℝ) (ht : 0 < t) :
    ContDiff ℝ ∞ (angularBlock t ht) := by
  apply contDiff_iff_contDiffAt.mpr
  intro θ
  by_cases hθ : Real.sin (θ / 2) = 0
  · have he : frequencyRadius θ < t := by simpa [frequencyRadius, hθ] using ht
    exact contDiffAt_const.congr_of_eventuallyEq (angularBlock_eventually_zero ht he)
  · apply (AngularCutoff.shell_contDiff t ht).contDiffAt.comp θ
    exact contDiffAt_const.mul
      ((Real.contDiff_sin.comp (contDiff_id.div_const 2)).contDiffAt.norm ℝ hθ)

/-- The blocks in Lemma 5.9 of the paper have support in its literal
angular annuli `[t,4t]`. Their narrower sine support has outer radius `(5/2)t`. -/
theorem angularBlock_support {t : ℝ} (ht : 0 < t) :
    Function.support (angularBlock t ht) ⊆
      {θ | t ≤ FourierMultiplierKernels.angularRadius θ ∧
        FourierMultiplierKernels.angularRadius θ ≤ 4 * t} := by
  intro θ hθ
  obtain ⟨hlo, hhi⟩ := angularBlock_support_sine ht hθ
  let y := AddCircle.equivIco (2 * Real.pi) 0 (θ : AddCircle (2 * Real.pi))
  have hcoe : (y.val : AddCircle (2 * Real.pi)) = (θ : AddCircle (2 * Real.pi)) :=
    AddCircle.coe_equivIco
  have hr : frequencyRadius y.val = frequencyRadius θ :=
    congrArg periodic_frequencyRadius.lift hcoe
  have hρ : FourierMultiplierKernels.angularRadius y.val =
      FourierMultiplierKernels.angularRadius θ := congrArg norm hcoe
  have hy : y.val ∈ Icc (0 : ℝ) (2 * Real.pi) := ⟨y.property.1, by simpa using y.property.2.le⟩
  change t ≤ FourierMultiplierKernels.angularRadius θ ∧
    FourierMultiplierKernels.angularRadius θ ≤ 4 * t
  rw [← hρ, FourierMultiplierKernels.angularRadius_eq_min hy]
  refine ⟨hlo.trans (by rw [← hr]; exact radius_le_endpointDistance hy), ?_⟩
  calc
    _ ≤ Real.pi / 2 * frequencyRadius y.val := endpointDistance_le_radius hy
    _ ≤ Real.pi / 2 * ((5 / 2) * t) := by rw [hr]; gcongr
    _ ≤ 4 * t := by nlinarith [Real.pi_lt_d2]

/-- Exact dyadic reconstruction at all angles outside the discarded lowest
cutoff. This includes every nonzero cycle frequency. For Lemma 5.9 of the paper. -/
theorem sum_angularBlock (N : ℕ+) (θ : ℝ)
    (hθ : 2 * dyadicScale N 0 ≤ frequencyRadius θ) :
    (∑ j ∈ Finset.range (dyadicDepth N + 1),
      angularBlock (dyadicScale N j) (dyadicScale_pos N j) θ) = 1 := by
  have hρ : frequencyRadius θ ≤ 2 := by
    dsimp [frequencyRadius]
    nlinarith [abs_le.mpr (And.intro (Real.neg_one_le_sin (θ / 2))
      (Real.sin_le_one (θ / 2)))]
  calc
    _ = ∑ j ∈ Finset.range (dyadicDepth N + 1),
        AngularCutoff.shell ((2 : ℝ) ^ j * dyadicScale N 0)
          (mul_pos (by positivity) (dyadicScale_pos N 0)) (frequencyRadius θ) := by
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [angularBlock, AngularCutoff.shell]
      rw [dyadicScale_eq_pow_mul N j]
    _ = 1 := AngularCutoff.sum_shell_eq_one (dyadicScale_pos N 0)
      (dyadicDepth N + 1) hθ (by rw [dyadicScale_top]; exact hρ)

/-- The blocks of Lemma 5.9 of the paper sum to one at every nonzero cycle frequency. -/
theorem sum_angularBlock_cycleAngle (N : ℕ+) (k : Fin (N : ℕ)) (hk : k ≠ 0) :
    (∑ j ∈ Finset.range (dyadicDepth N + 1),
      angularBlock (dyadicScale N j) (dyadicScale_pos N j) (cycleAngle N k)) = 1 := by
  apply sum_angularBlock
  have hN : (0 : ℝ) < N := by positivity
  have hs := dyadicScale_zero_le N
  have hρ := cycle_frequencyRadius_lower N k hk
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * N)] at hs
  rw [div_le_iff₀ hN] at hρ
  nlinarith

/-- Every block kills the constant mode. For Lemma 5.9 of the paper. -/
theorem angularBlock_cycleAngle_zero (N : ℕ+) (t : ℝ) (ht : 0 < t) :
    angularBlock t ht (cycleAngle N 0) = 0 := by
  apply AngularCutoff.shell_eq_zero_of_le ht
  simpa [cycleAngle, frequencyRadius] using ht.le

/-- The finite partition in Lemma 5.9 of the paper reconstructs every
zero-sum vector, with the Fourier sign and normalization. -/
theorem angularBlock_reconstruction (N : ℕ+) (w : Fin (N : ℕ) → ℂ)
    (hw : ∑ i, w i = 0) (i : Fin (N : ℕ)) :
    (∑ j ∈ Finset.range (dyadicDepth N + 1),
      cycleFourierInv N (fun k =>
        (angularBlock (dyadicScale N j) (dyadicScale_pos N j) (cycleAngle N k) : ℂ) *
          cycleFourier N w k) i) = w i := by
  have hzero : cycleFourier N w 0 = 0 := by
    simpa only [cycleFourier, cycleAngle, Fin.val_zero, Nat.cast_zero, mul_zero,
      zero_div, Complex.ofReal_zero, Complex.exp_zero, mul_one] using hw
  calc
    _ = (N : ℂ)⁻¹ * ∑ k : Fin (N : ℕ),
        (∑ j ∈ Finset.range (dyadicDepth N + 1),
          (angularBlock (dyadicScale N j) (dyadicScale_pos N j) (cycleAngle N k) : ℂ)) *
            cycleFourier N w k *
              Complex.exp (-(Complex.I * ((i : ℕ) : ℂ) * (cycleAngle N k : ℂ))) := by
      simp only [cycleFourierInv, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_comm
    _ = cycleFourierInv N (cycleFourier N w) i := by
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k = 0
      · simp only [hk, hzero, mul_zero, zero_mul]
      · rw [← Complex.ofReal_sum, sum_angularBlock_cycleAngle N k hk,
          Complex.ofReal_one, one_mul]
    _ = w i := cycleFourierInv_cycleFourier w i

/-- The angular shell derivative bounds in Lemma 5.9 of the paper. -/
theorem angularBlock_derivative_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ t (ht : 0 < t), t ≤ 1 → ∀ j : ℕ, j ≤ 2 →
      ∀ x ∈ Ioo (0 : ℝ) (2 * Real.pi),
        |iteratedDeriv j (angularBlock t ht) x| ≤ C / t ^ j := by
  obtain ⟨C₁, hC₁, hb₁⟩ := AngularCutoff.shell_derivative_bound 1
  obtain ⟨C₂, hC₂, hb₂⟩ := AngularCutoff.shell_derivative_bound 2
  refine ⟨1 + C₁ + C₂, by positivity, fun t ht ht1 j hj x hx => ?_⟩
  let r : ℝ → ℝ := fun y => 2 * Real.sin (y / 2)
  have hr : ContDiff ℝ ∞ r := contDiff_const.mul
    (Real.contDiff_sin.comp (contDiff_id.div_const 2))
  have hd (y : ℝ) : HasDerivAt r (Real.cos (y / 2)) y := by
    convert (((hasDerivAt_id y).div_const 2).sin.const_mul 2) using 1
    all_goals dsimp [r, id]
    all_goals ring_nf
  have hd₂ (y : ℝ) : HasDerivAt (deriv r) (-Real.sin (y / 2) / 2) y := by
    have he : deriv r = fun z => Real.cos (z / 2) := funext (fun z => (hd z).deriv)
    rw [he]
    convert (((hasDerivAt_id y).div_const 2).cos) using 1
    all_goals dsimp [r, id]
    all_goals ring_nf
  have hdr : |deriv r x| ≤ 1 := by
    rw [(hd x).deriv]
    exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hdr₂ : |iteratedDeriv 2 r x| ≤ 1 := by
    simp only [iteratedDeriv_succ, iteratedDeriv_zero, (hd₂ x).deriv]
    rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have := abs_le.mpr ⟨Real.neg_one_le_sin (x / 2), Real.sin_le_one (x / 2)⟩
    linarith
  have he : angularBlock t ht =ᶠ[𝓝 x] (AngularCutoff.shell t ht ∘ r) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    simp only [angularBlock, Function.comp_apply, frequencyRadius_eq_sin hy, r]
  rw [he.iteratedDeriv_eq j]
  have hs := AngularCutoff.shell_contDiff t ht
  interval_cases j
  · simp only [iteratedDeriv_zero, Function.comp_apply, pow_zero, div_one]
    have h := AngularCutoff.shell_le_one t (r x) ht
    rw [abs_of_nonneg (AngularCutoff.shell_nonneg ht _)]
    linarith
  · simp only [iteratedDeriv_one]
    rw [deriv_comp x (hs.differentiable (by simp)).differentiableAt
      (hr.differentiable (by simp)).differentiableAt, abs_mul]
    have hb : |deriv (AngularCutoff.shell t ht) (r x)| ≤ C₁ / t := by
      simpa only [iteratedDeriv_one, pow_one] using hb₁ t ht (r x)
    calc
      _ ≤ (C₁ / t) * 1 := mul_le_mul hb hdr (abs_nonneg _) (by positivity)
      _ ≤ _ := by
        simp only [pow_one, mul_one]
        exact div_le_div_of_nonneg_right (by linarith) ht.le
  · rw [iteratedDeriv_comp_two (hs.of_le (by simp)).contDiffAt
      (hr.of_le (by simp)).contDiffAt]
    calc
      _ ≤ |iteratedDeriv 2 (AngularCutoff.shell t ht) (r x)| * |deriv r x| ^ 2 +
          |deriv (AngularCutoff.shell t ht) (r x)| * |iteratedDeriv 2 r x| := by
        exact (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_pow, abs_mul])
      _ ≤ (C₂ / t ^ 2) * 1 ^ 2 + (C₁ / t) * 1 := by
        apply add_le_add
        · exact mul_le_mul (hb₂ t ht (r x)) (pow_le_pow_left₀ (abs_nonneg _) hdr 2)
            (by positivity) (by positivity)
        · exact mul_le_mul (by simpa only [iteratedDeriv_one, pow_one] using hb₁ t ht (r x))
            hdr₂ (abs_nonneg _) (by positivity)
      _ ≤ _ := by
        simp only [one_pow, mul_one]
        apply (div_le_div_of_nonneg_right (by linarith : C₂ + C₁ ≤ 1 + C₁ + C₂)
          (sq_nonneg t)).trans' _
        rw [add_div]
        apply add_le_add_right
        exact div_le_div_of_nonneg_left hC₁.le (sq_pos_of_pos ht) (by nlinarith)


/-- All real lifts satisfy the uniform derivative bounds for the blocks in
Lemma 5.9 of the paper, including every copy of the angular seam. -/
theorem angularBlock_derivative_bounds_global :
    ∃ C : ℝ, 0 < C ∧ ∀ t (ht : 0 < t), t ≤ 1 → ∀ j : ℕ, j ≤ 2 → ∀ x : ℝ,
      |iteratedDeriv j (angularBlock t ht) x| ≤ C / t ^ j := by
  obtain ⟨C, hC, hb⟩ := angularBlock_derivative_bounds
  refine ⟨C, hC, fun t ht ht1 j hj x => ?_⟩
  by_cases hx : frequencyRadius x < t
  · rw [(angularBlock_eventually_zero ht hx).iteratedDeriv_eq j]
    have hzero : iteratedDeriv j (fun _ : ℝ => (0 : ℝ)) x = 0 := by
      cases j <;> simp
    rw [hzero, abs_zero]
    positivity
  · let y := AddCircle.equivIco (2 * Real.pi) 0 (x : AddCircle (2 * Real.pi))
    have hcoe : (y.val : AddCircle (2 * Real.pi)) = (x : AddCircle (2 * Real.pi)) :=
      AddCircle.coe_equivIco
    have hr : frequencyRadius y.val = frequencyRadius x :=
      congrArg periodic_frequencyRadius.lift hcoe
    have hy0 : 0 < y.val := by
      apply lt_of_le_of_ne y.property.1
      intro he
      have hz0 : frequencyRadius y.val = 0 := by
        simp only [← he, frequencyRadius, zero_div, Real.sin_zero, abs_zero, mul_zero]
      exact hx (by rw [← hr, hz0]; exact ht)
    have hy : y.val ∈ Ioo 0 (2 * Real.pi) := ⟨hy0, by simpa using y.property.2⟩
    have hshift : (fun z : ℝ => angularBlock t ht (z + (y.val - x))) =
        angularBlock t ht := by
      funext z
      have hc : ((z + (y.val - x) : ℝ) : AddCircle (2 * Real.pi)) =
          (z : AddCircle (2 * Real.pi)) := by
        rw [AddCircle.coe_add, AddCircle.coe_sub, hcoe, sub_self, add_zero]
      exact congrArg (periodic_angularBlock t ht).lift hc
    have hder := congrFun (iteratedDeriv_comp_add_const j (angularBlock t ht) (y.val - x)) x
    rw [hshift, show x + (y.val - x) = y.val by ring] at hder
    exact hder ▸ hb t ht ht1 j hj y.val hy

/-- The dyadic scales in Lemma 5.9 of the paper lie between `1/(8N)`
and one. Together with `dyadicDepth_log_bound` this gives its scale and count bounds. -/
theorem angularBlock_scale_bounds (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    {j : ℕ} (hj : j ≤ dyadicDepth N) :
    (8 * (N : ℝ))⁻¹ ≤ dyadicScale N j ∧ dyadicScale N j ≤ 1 := by
  have hc : 0 < Nat.clog 2 (N : ℕ) := Nat.clog_pos (by norm_num) (by omega)
  have hp := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) (by omega : 1 < (N : ℕ))
  have hpow : (2 : ℝ) ^ Nat.clog 2 (N : ℕ) ≤ 2 * (N : ℝ) := by
    have he : Nat.clog 2 (N : ℕ) = (Nat.clog 2 (N : ℕ) - 1) + 1 := by omega
    rw [he, pow_succ]
    have hp' : (2 : ℝ) ^ (Nat.clog 2 (N : ℕ) - 1) < (N : ℝ) := by exact_mod_cast hp
    linarith
  have hbase : (8 * (N : ℝ))⁻¹ ≤ dyadicScale N 0 := by
    simp only [dyadicScale, Nat.cast_zero, zero_sub, zpow_neg, zpow_natCast]
    apply inv_anti₀ (by positivity)
    dsimp only [dyadicDepth]
    rw [pow_add]
    norm_num only [pow_succ, pow_zero, mul_one]
    nlinarith
  refine ⟨hbase.trans ?_, dyadicScale_le_one N hj⟩
  rw [dyadicScale_eq_pow_mul N j]
  exact le_mul_of_one_le_left (dyadicScale_pos N 0).le (one_le_pow₀ (by norm_num))

end Riesz2.DiscreteInterpolation
