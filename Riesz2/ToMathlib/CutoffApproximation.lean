/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.IntrinsicScalarForms
public import Riesz1.ToMathlib.MollifierExistence
public import Riesz1.ToMathlib.MollifierPointwise.Smoothing
public import Riesz1.ToMathlib.WeightedSobolev.GraphLimits
public import Riesz1.ToMathlib.WeightedSobolev.LipschitzH1
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Cutoffs and approximation in scalar form norms

Scalar shells supply the radial cutoffs of Subsection 5.3. All scales are
explicit positive parameters. The mollifier and Sobolev spaces are the Riesz 1
objects. Form approximation uses the scalar jet completion.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff BigOperators NNReal

namespace Riesz2.CutoffApproximation

/-- A fixed nonincreasing smooth cutoff, as required by Subsection 5.3.
It is one up to 1 and zero from 2 onwards. -/
def scalarCutoff (x : ℝ) : ℝ := Real.smoothTransition (2 - x)

theorem scalarCutoff_contDiff : ContDiff ℝ ∞ scalarCutoff :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

theorem scalarCutoff_nonneg (x : ℝ) : 0 ≤ scalarCutoff x :=
  Real.smoothTransition.nonneg _

theorem scalarCutoff_le_one (x : ℝ) : scalarCutoff x ≤ 1 :=
  Real.smoothTransition.le_one _

theorem scalarCutoff_antitone : Antitone scalarCutoff := by
  intro x y hxy
  exact Real.smoothTransition.monotone (by linarith)

theorem scalarCutoff_eq_one {x : ℝ} (hx : x ≤ 1) : scalarCutoff x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem scalarCutoff_eq_zero {x : ℝ} (hx : 2 ≤ x) : scalarCutoff x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

/-- Positive-order derivatives vanish off the transition interval. -/
theorem scalarCutoff_iteratedDeriv_eq_zero (k : ℕ) (hk : 0 < k) {x : ℝ}
    (hx : x < 1 ∨ 2 < x) : iteratedDeriv k scalarCutoff x = 0 := by
  rcases hx with hx | hx
  · have he : scalarCutoff =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
      filter_upwards [eventually_lt_nhds hx] with y hy
      exact scalarCutoff_eq_one hy.le
    rw [he.iteratedDeriv_eq k, iteratedDeriv_const]
    simp [hk.ne']
  · have he : scalarCutoff =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      exact scalarCutoff_eq_zero hy.le
    rw [he.iteratedDeriv_eq k, iteratedDeriv_const]
    simp [hk.ne']

/-- Every derivative has a bound fixed before choosing any scale. -/
theorem scalarCutoff_derivative_bound (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, |iteratedDeriv k scalarCutoff x| ≤ C := by
  by_cases hk : k = 0
  · subst k
    exact ⟨1, one_pos, fun x => by
      simpa only [iteratedDeriv_zero, abs_of_nonneg (scalarCutoff_nonneg x)] using
        scalarCutoff_le_one x⟩
  have hc : Continuous (iteratedDeriv k scalarCutoff) :=
    scalarCutoff_contDiff.continuous_iteratedDeriv k (by simp)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (1 : ℝ) 2) hc.continuousOn
  refine ⟨max B 0 + 1, by positivity, fun x => ?_⟩
  by_cases hx : x ∈ Icc (1 : ℝ) 2
  · have hb : |iteratedDeriv k scalarCutoff x| ≤ B := by
      simpa only [Real.norm_eq_abs] using hB x hx
    exact hb.trans (by linarith [le_max_left B 0])
  · rw [scalarCutoff_iteratedDeriv_eq_zero k (Nat.pos_of_ne_zero hk) (by
      simpa only [mem_Icc, not_and_or, not_le] using hx), abs_zero]
    positivity

/-- The radial shell from Subsection 5.3, with an explicit scale. -/
def shell (t : ℝ) (_ht : 0 < t) (r : ℝ) : ℝ := scalarCutoff (r / (2 * t)) - scalarCutoff (r / t)

theorem shell_contDiff (t : ℝ) (ht : 0 < t) : ContDiff ℝ ∞ (shell t ht) :=
  (scalarCutoff_contDiff.comp (contDiff_id.div_const _)).sub
    (scalarCutoff_contDiff.comp (contDiff_id.div_const _))

theorem shell_nonneg {t : ℝ} (ht : 0 < t) (r : ℝ) : 0 ≤ shell t ht r := by
  by_cases hr : r ≤ t
  · have h1 : r / t ≤ 1 := (div_le_one ht).mpr hr
    have h2 : r / (2 * t) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    simp only [shell, scalarCutoff_eq_one h1, scalarCutoff_eq_one h2, sub_self, le_refl]
  · apply sub_nonneg.mpr
    apply scalarCutoff_antitone
    exact div_le_div_of_nonneg_left (by linarith) ht (by linarith)

theorem shell_le_one (t r : ℝ) (ht : 0 < t) : shell t ht r ≤ 1 := by
  unfold shell
  linarith [scalarCutoff_le_one (r / (2 * t)), scalarCutoff_nonneg (r / t)]

theorem shell_eq_zero_of_le {t r : ℝ} (ht : 0 < t) (hr : r ≤ t) : shell t ht r = 0 := by
  have h1 : r / t ≤ 1 := (div_le_one ht).mpr hr
  have h2 : r / (2 * t) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  simp only [shell, scalarCutoff_eq_one h1, scalarCutoff_eq_one h2, sub_self]

theorem shell_eq_zero_of_ge {t r : ℝ} (ht : 0 < t) (hr : 4 * t ≤ r) :
    shell t ht r = 0 := by
  have h1 : 2 ≤ r / t := (le_div_iff₀ ht).mpr (by linarith)
  have h2 : 2 ≤ r / (2 * t) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  simp only [shell, scalarCutoff_eq_zero h1, scalarCutoff_eq_zero h2, sub_self]

/-- Shells are supported in the prescribed closed annulus. -/
theorem shell_tsupport_subset {t : ℝ} (ht : 0 < t) :
    tsupport (shell t ht) ⊆ Icc t (4 * t) := by
  apply closure_minimal _ isClosed_Icc
  intro r hr
  by_contra hc
  have hne : shell t ht r ≠ 0 := hr
  have hd : r < t ∨ 4 * t < r := by
    simpa only [mem_Icc, not_and_or, not_le] using hc
  rcases hd with h | h
  · exact hne (shell_eq_zero_of_le ht h.le)
  · exact hne (shell_eq_zero_of_ge ht h.le)

theorem shell_hasCompactSupport {t : ℝ} (ht : 0 < t) : HasCompactSupport (shell t ht) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (shell_tsupport_subset ht)

/-- Exact rescaling of every derivative. The scale is not hidden in a choice. -/
theorem iteratedDeriv_scaledCutoff (k : ℕ) (t r : ℝ) :
    iteratedDeriv k (fun x => scalarCutoff (x / t)) r =
      t⁻¹ ^ k * iteratedDeriv k scalarCutoff (r / t) := by
  simpa only [div_eq_mul_inv, mul_comm _ t⁻¹] using
    congrFun (iteratedDeriv_comp_const_mul
      (scalarCutoff_contDiff.of_le (by simp)) t⁻¹) r

/-- All-order derivative bounds for radial dyadic shells, uniform over positive scales. -/
theorem shell_derivative_bound (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t (ht : 0 < t), ∀ r,
      |iteratedDeriv k (shell t ht) r| ≤ C / t ^ k := by
  obtain ⟨B, hB, hb⟩ := scalarCutoff_derivative_bound k
  refine ⟨2 * B, by positivity, fun t ht r => ?_⟩
  have hscale : (2 * t)⁻¹ ^ k ≤ t⁻¹ ^ k :=
    pow_le_pow_left₀ (by positivity) (inv_anti₀ ht (by linarith)) k
  have h1 : |iteratedDeriv k (fun x => scalarCutoff (x / (2 * t))) r| ≤
      t⁻¹ ^ k * B := by
    rw [iteratedDeriv_scaledCutoff, abs_mul, abs_of_nonneg (by positivity)]
    exact (mul_le_mul_of_nonneg_left (hb _) (by positivity)).trans
      (mul_le_mul_of_nonneg_right hscale hB.le)
  have h2 : |iteratedDeriv k (fun x => scalarCutoff (x / t)) r| ≤ t⁻¹ ^ k * B := by
    rw [iteratedDeriv_scaledCutoff, abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hb _) (by positivity)
  have he := iteratedDeriv_sub (n := k) (x := r)
    ((scalarCutoff_contDiff.comp (contDiff_id.div_const (2 * t))).of_le (by simp)).contDiffAt
    ((scalarCutoff_contDiff.comp (contDiff_id.div_const t)).of_le (by simp)).contDiffAt
  change |iteratedDeriv k ((fun x => scalarCutoff (x / (2 * t))) -
    (fun x => scalarCutoff (x / t))) r| ≤ _
  dsimp only [Function.comp_def, id_eq] at he
  rw [he]
  calc
    _ ≤ |iteratedDeriv k (fun x => scalarCutoff (x / (2 * t))) r| +
        |iteratedDeriv k (fun x => scalarCutoff (x / t)) r| := abs_sub _ _
    _ ≤ t⁻¹ ^ k * B + t⁻¹ ^ k * B := add_le_add h1 h2
    _ = (2 * B) / t ^ k := by rw [div_eq_mul_inv, inv_pow]; ring

/-- The finite dyadic decomposition telescopes, including the empty family. -/
theorem sum_shell (t r : ℝ) (ht : 0 < t) (n : ℕ) :
    (∑ j ∈ Finset.range n, shell ((2 : ℝ) ^ j * t) (by positivity) r) =
      scalarCutoff (r / (2 ^ n * t)) - scalarCutoff (r / t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, shell]
    have he : (2 : ℝ) * (2 ^ n * t) = 2 ^ (n + 1) * t := by ring
    rw [he]
    ring

/-- A finite shell family is a partition of unity wherever the endpoint cutoffs
are respectively one and zero. This is the scalar telescoping in Subsection 5.3. -/
theorem sum_shell_eq_one {t r : ℝ} (ht : 0 < t) (n : ℕ)
    (hlo : 2 * t ≤ r) (hhi : r ≤ 2 ^ n * t) :
    (∑ j ∈ Finset.range n, shell ((2 : ℝ) ^ j * t) (by positivity) r) = 1 := by
  rw [sum_shell t r ht, scalarCutoff_eq_one ((div_le_one (by positivity)).mpr hhi),
    scalarCutoff_eq_zero ((le_div_iff₀ ht).mpr hlo), sub_zero]

/-- A compact smooth interval cutoff with an explicit transition width.
For `a ≤ b`, it equals one on `[a,b]`. Its support lies in `[a-ε,b+ε]`.
The formula has its literal meaning also for unordered endpoints. -/
def intervalCutoff (a b ε : ℝ) (_hε : 0 < ε) (x : ℝ) : ℝ :=
  scalarCutoff ((a - x) / ε + 1) * scalarCutoff ((x - b) / ε + 1)

theorem intervalCutoff_contDiff (a b ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ ∞ (intervalCutoff a b ε hε) :=
  (scalarCutoff_contDiff.comp
    (((contDiff_const.sub contDiff_id).div_const ε).add contDiff_const)).mul
    (scalarCutoff_contDiff.comp
      (((contDiff_id.sub contDiff_const).div_const ε).add contDiff_const))

theorem intervalCutoff_bounds (a b ε x : ℝ) (hε : 0 < ε) :
    0 ≤ intervalCutoff a b ε hε x ∧ intervalCutoff a b ε hε x ≤ 1 := by
  refine ⟨mul_nonneg (scalarCutoff_nonneg _) (scalarCutoff_nonneg _), ?_⟩
  change scalarCutoff _ * scalarCutoff _ ≤ 1
  exact (mul_le_mul_of_nonneg_left (scalarCutoff_le_one _) (scalarCutoff_nonneg _)).trans
    (by simpa only [mul_one] using scalarCutoff_le_one ((a - x) / ε + 1))

theorem intervalCutoff_eq_one {a b ε x : ℝ} (hε : 0 < ε) (hx : x ∈ Icc a b) :
    intervalCutoff a b ε hε x = 1 := by
  have h₁ : (a - x) / ε + 1 ≤ 1 := by
    have := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx.1) hε.le
    linarith
  have h₂ : (x - b) / ε + 1 ≤ 1 := by
    have := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx.2) hε.le
    linarith
  rw [intervalCutoff, scalarCutoff_eq_one h₁, scalarCutoff_eq_one h₂, mul_one]

theorem intervalCutoff_eq_zero {a b ε x : ℝ} (hε : 0 < ε)
    (hx : x ≤ a - ε ∨ b + ε ≤ x) : intervalCutoff a b ε hε x = 0 := by
  rcases hx with hx | hx
  · have h₁ : 2 ≤ (a - x) / ε + 1 := by
      have := (le_div_iff₀ hε).mpr (show 1 * ε ≤ a - x by linarith)
      linarith
    rw [intervalCutoff, scalarCutoff_eq_zero h₁, zero_mul]
  · have h₂ : 2 ≤ (x - b) / ε + 1 := by
      have := (le_div_iff₀ hε).mpr (show 1 * ε ≤ x - b by linarith)
      linarith
    rw [intervalCutoff, scalarCutoff_eq_zero h₂, mul_zero]

theorem intervalCutoff_tsupport_subset {a b ε : ℝ} (hε : 0 < ε) :
    tsupport (intervalCutoff a b ε hε) ⊆ Icc (a - ε) (b + ε) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hn
  have he : x < a - ε ∨ b + ε < x := by
    simpa only [mem_Icc, not_and_or, not_le] using hn
  exact hx (intervalCutoff_eq_zero hε (he.imp le_of_lt le_of_lt))

theorem intervalCutoff_hasCompactSupport {a b ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (intervalCutoff a b ε hε) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (intervalCutoff_tsupport_subset hε)

/-- Interval cutoff derivatives cost at most `C/ε`, with the same `C` for all
endpoints and all positive transition widths. -/
theorem intervalCutoff_deriv_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ a b ε (hε : 0 < ε), ∀ x,
      |deriv (intervalCutoff a b ε hε) x| ≤ C / ε := by
  obtain ⟨B, hB, hb⟩ := scalarCutoff_derivative_bound 1
  have hb' (x : ℝ) : |deriv scalarCutoff x| ≤ B := by
    simpa only [iteratedDeriv_one] using hb x
  refine ⟨2 * B, by positivity, fun a b ε hε x => ?_⟩
  have h₁ := ((scalarCutoff_contDiff.differentiable (by simp) _).hasDerivAt.comp x
    ((((hasDerivAt_id x).const_sub a).div_const ε).add_const 1))
  have h₂ := ((scalarCutoff_contDiff.differentiable (by simp) _).hasDerivAt.comp x
    ((((hasDerivAt_id x).sub_const b).div_const ε).add_const 1))
  have hd := (h₁.mul h₂).deriv
  dsimp only [Function.comp_def, id_eq] at hd
  change deriv (intervalCutoff a b ε hε) x = _ at hd
  rw [hd]
  have hbl : |scalarCutoff ((a - x) / ε + 1)| ≤ 1 := by
    rw [abs_of_nonneg (scalarCutoff_nonneg _)]
    exact scalarCutoff_le_one _
  have hbr : |scalarCutoff ((x - b) / ε + 1)| ≤ 1 := by
    rw [abs_of_nonneg (scalarCutoff_nonneg _)]
    exact scalarCutoff_le_one _
  calc
    _ ≤ |deriv scalarCutoff ((a - x) / ε + 1) * (-1 / ε)| *
        |scalarCutoff ((x - b) / ε + 1)| +
        |scalarCutoff ((a - x) / ε + 1)| *
        |deriv scalarCutoff ((x - b) / ε + 1) * (1 / ε)| := by
      simpa only [abs_mul] using abs_add_le
        ((deriv scalarCutoff ((a - x) / ε + 1) * (-1 / ε)) *
          scalarCutoff ((x - b) / ε + 1))
        (scalarCutoff ((a - x) / ε + 1) *
          (deriv scalarCutoff ((x - b) / ε + 1) * (1 / ε)))
    _ ≤ (B / ε) * 1 + 1 * (B / ε) := by
      have hd₁ : |deriv scalarCutoff ((a - x) / ε + 1) * (-1 / ε)| ≤ B / ε := by
        rw [abs_mul, abs_div, abs_neg, abs_one, abs_of_pos hε]
        simpa only [div_eq_mul_inv, one_mul] using
          mul_le_mul_of_nonneg_right (hb' _) (inv_nonneg.mpr hε.le)
      have hd₂ : |deriv scalarCutoff ((x - b) / ε + 1) * (1 / ε)| ≤ B / ε := by
        rw [abs_mul, abs_div, abs_one, abs_of_pos hε]
        simpa only [div_eq_mul_inv, one_mul] using
          mul_le_mul_of_nonneg_right (hb' _) (inv_nonneg.mpr hε.le)
      exact add_le_add (mul_le_mul hd₁ hbr (abs_nonneg _) (by positivity))
        (mul_le_mul hbl hd₂ (abs_nonneg _) (by positivity))
    _ = 2 * B / ε := by ring

/-- Mollification preserves the classical derivative bound. The mollifier is
Riesz1's normalized compactly supported kernel. -/
theorem mollifyLine_deriv_bound {ρ u : ℝ → ℝ} (hρ : Riesz1.IsMollifier ρ)
    (hu : ContDiff ℝ 1 u) {M₀ M₁ h : ℝ} (hh : 0 < h)
    (hb₀ : ∀ x, |u x| ≤ M₀) (hb₁ : ∀ x, |deriv u x| ≤ M₁) (x : ℝ) :
    |deriv (Riesz1.mollifyLine ρ h u) x| ≤ M₁ := by
  rw [(Riesz1.hasDerivAt_mollifyLine_of_bounded hρ hh hu hb₀ hb₁ x).deriv,
    ← Riesz1.mollifyLine_eq]
  exact Riesz1.abs_mollifyLine_le_of_bound hρ hh hb₁ x

/-- Mollification of bounded `C¹` functions converges in both parts of the
weighted scalar form norm, for every finite Borel measure on the line.
No lower bound or continuity of its density is required. The bounds are
uniform over the sequence of positive radii. -/
theorem mollifyLine_form_convergence {ρ u : ℝ → ℝ} (hρ : Riesz1.IsMollifier ρ)
    (hu : ContDiff ℝ 1 u) {M₀ M₁ : ℝ}
    (hb₀ : ∀ x, |u x| ≤ M₀) (hb₁ : ∀ x, |deriv u x| ≤ M₁)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (h : ℕ → ℝ)
    (hh : ∀ k, 0 < h k) (hl : Tendsto h atTop (𝓝 0)) :
    (∀ k, ContDiff ℝ ∞ (Riesz1.mollifyLine ρ (h k) u)) ∧
    (∀ k x, |Riesz1.mollifyLine ρ (h k) u x| ≤ M₀) ∧
    (∀ k x, |deriv (Riesz1.mollifyLine ρ (h k) u) x| ≤ M₁) ∧
    Tendsto (fun k => ∫⁻ x, ‖Riesz1.mollifyLine ρ (h k) u x - u x‖ₑ ^ 2 ∂μ)
      atTop (𝓝 0) ∧
    Tendsto (fun k => ∫⁻ x,
      ‖deriv (Riesz1.mollifyLine ρ (h k) u) x - deriv u x‖ₑ ^ 2 ∂μ)
      atTop (𝓝 0) := by
  have hc k : ContDiff ℝ ∞ (Riesz1.mollifyLine ρ (h k) u) :=
    Riesz1.contDiff_mollifyLine_of_locallyIntegrable hρ (hh k) hu.continuous.locallyIntegrable
  have hbd k x : |deriv (Riesz1.mollifyLine ρ (h k) u) x| ≤ M₁ :=
    mollifyLine_deriv_bound hρ hu (hh k) hb₀ hb₁ x
  have hbc k x : |Riesz1.mollifyLine ρ (h k) u x| ≤ M₀ :=
    Riesz1.abs_mollifyLine_le_of_bound hρ (hh k) hb₀ x
  have hm k : MemLp (Riesz1.mollifyLine ρ (h k) u) 2 μ :=
    MemLp.of_bound (hc k).continuous.aestronglyMeasurable M₀
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hbc k x)
  have hmd k : MemLp (deriv (Riesz1.mollifyLine ρ (h k) u)) 2 μ :=
    MemLp.of_bound ((hc k).continuous_deriv (by simp)).aestronglyMeasurable M₁
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hbd k x)
  have hu₀ : MemLp u 2 μ := MemLp.of_bound hu.continuous.aestronglyMeasurable M₀
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb₀ x)
  have hu₁ : MemLp (deriv u) 2 μ :=
    MemLp.of_bound hu.continuous_deriv_one.aestronglyMeasurable M₁
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb₁ x)
  have hgt : Tendsto h atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hl, Eventually.of_forall hh⟩
  refine ⟨hc, hbc, hbd, ?_, ?_⟩
  · apply (Riesz1.WeightedSobolev.tendsto_toLp_iff_lintegral_sq _ hm _ hu₀).mp
    apply Riesz1.WeightedSobolev.tendsto_toLp_of_dominated hm hu₀ (memLp_const M₀)
      (fun k => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => (Riesz1.tendsto_mollifyLine_fun hρ hu.continuous x).comp hgt)
    · simpa only [Real.norm_eq_abs] using hbc k x
    · simpa only [Real.norm_eq_abs] using hb₀ x
  · apply (Riesz1.WeightedSobolev.tendsto_toLp_iff_lintegral_sq _ hmd _ hu₁).mp
    apply Riesz1.WeightedSobolev.tendsto_toLp_of_dominated hmd hu₁ (memLp_const M₁)
      (fun k => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · simpa only [Real.norm_eq_abs] using hbd k x
    · simpa only [Real.norm_eq_abs] using hb₁ x
    · have hd := (Riesz1.tendsto_mollifyLine_deriv hρ hu x).comp hgt
      exact hd.congr fun k =>
        (Riesz1.hasDerivAt_mollifyLine_of_bounded hρ (hh k) hu hb₀ hb₁ x).deriv.symm

namespace Internal

variable {Ω V : Type*} [MeasurableSpace Ω] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {μ : Measure Ω}

/-- Internal multiplier criterion for cutoff approximation. It applies also to
infinite measures, provided the field has finite L² norm. -/
theorem cutoff_smul_l2_convergence {θ : ℕ → Ω → ℝ}
    (hθ : ∀ k, AEStronglyMeasurable (θ k) μ)
    (hb : ∀ k, ∀ᵐ x ∂μ, |θ k x| ≤ 1)
    (hl : ∀ᵐ x ∂μ, Tendsto (fun k => θ k x) atTop (𝓝 1))
    {G : Ω → V} (hG : MemLp G 2 μ) :
    (∀ k, MemLp (fun x => θ k x • G x) 2 μ) ∧
    Tendsto (fun k => ∫⁻ x, ‖θ k x • G x - G x‖ₑ ^ 2 ∂μ) atTop (𝓝 0) := by
  have hm k : MemLp (fun x => θ k x • G x) 2 μ := by
    apply hG.of_le_mul (c := 1) ((hθ k).smul hG.aestronglyMeasurable)
    filter_upwards [hb k] with x hx
    change ‖θ k x • G x‖ ≤ 1 * ‖G x‖
    simpa only [norm_smul, Real.norm_eq_abs, one_mul] using
      mul_le_mul_of_nonneg_right hx (norm_nonneg (G x))
  refine ⟨hm, (Riesz1.WeightedSobolev.tendsto_toLp_iff_lintegral_sq _ hm _ hG).mp ?_⟩
  apply Riesz1.WeightedSobolev.tendsto_toLp_of_dominated hm hG hG.norm
  · intro k
    filter_upwards [hb k] with x hx
    simpa only [norm_smul, Real.norm_eq_abs, one_mul] using
      mul_le_mul_of_nonneg_right hx (norm_nonneg (G x))
  · exact Eventually.of_forall fun _ => le_rfl
  · filter_upwards [hl] with x hx
    simpa only [one_smul] using hx.smul (tendsto_const_nhds (x := G x))

/-- Internal boundary approximation criterion. With the product gradient
`θₖ G + F Dₖ`, bounded cutoffs tending to one converge in both parts of the
weighted form norm as soon as the boundary error `F Dₖ` tends to zero in L².
Applications supply their own cutoff-gradient identity and boundary estimate.
No claim about arbitrary boundary weights is implicit here. -/
theorem cutoff_jet_convergence {θ : ℕ → Ω → ℝ}
    (hθ : ∀ k, AEStronglyMeasurable (θ k) μ)
    (hb : ∀ k, ∀ᵐ x ∂μ, |θ k x| ≤ 1)
    (hl : ∀ᵐ x ∂μ, Tendsto (fun k => θ k x) atTop (𝓝 1))
    {F : Ω → ℝ} {G : Ω → V} (hF : MemLp F 2 μ) (hG : MemLp G 2 μ)
    (D : ℕ → Ω → V) (hD : ∀ k, MemLp (fun x => F x • D k x) 2 μ)
    (hboundary : Tendsto (fun k => ∫⁻ x, ‖F x • D k x‖ₑ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫⁻ x, ‖θ k x * F x - F x‖ₑ ^ 2 ∂μ) atTop (𝓝 0) ∧
    Tendsto (fun k => ∫⁻ x, ‖(θ k x • G x + F x • D k x) - G x‖ₑ ^ 2 ∂μ)
      atTop (𝓝 0) := by
  obtain ⟨hm, hml⟩ := cutoff_smul_l2_convergence hθ hb hl hG
  refine ⟨by simpa only [smul_eq_mul] using
    (cutoff_smul_l2_convergence hθ hb hl hF).2, ?_⟩
  have hg := (Riesz1.WeightedSobolev.tendsto_toLp_iff_lintegral_sq _ hm _ hG).mpr hml
  have hz : Tendsto (fun k => (hD k).toLp (fun x => F x • D k x)) atTop (𝓝 0) := by
    have ht := (Riesz1.WeightedSobolev.tendsto_toLp_iff_lintegral_sq _ hD
      (fun _ => (0 : V)) MemLp.zero).mpr (by simpa only [sub_zero] using hboundary)
    change Tendsto (fun k => (hD k).toLp (fun x => F x • D k x)) atTop
      (𝓝 ((MemLp.zero : MemLp (0 : Ω → V) 2 μ).toLp 0)) at ht
    simpa only [MemLp.toLp_zero] using ht
  have hsum k := (hm k).add (hD k)
  apply (Riesz1.WeightedSobolev.tendsto_toLp_iff_lintegral_sq _ hsum _ hG).mp
  have ht := hg.add hz
  simp only [add_zero] at ht
  exact ht.congr fun k => (MemLp.toLp_add (hm k) (hD k)).symm

end Internal

section FormApproximation

variable {Ω C G : Type*} [MeasurableSpace Ω] [AddCommGroup C] [Module ℝ C]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] {μ : Measure Ω}
  (J : C →ₗ[ℝ] ScalarForm.Jet μ G)

/-- Every element of the scalar jet completion has a sequence from its prescribed
core converging in the form norm. This does not impose a boundary condition. -/
theorem exists_core_approximation (f : ScalarForm.Domain J) :
    ∃ c : ℕ → C, Tendsto (fun k => ScalarForm.ofCore J (c k)) atTop (𝓝 f) := by
  obtain ⟨a, ha, hl⟩ := mem_closure_iff_seq_limit.mp (ScalarForm.denseRange_ofCore J f)
  choose c hc using ha
  exact ⟨c, hl.congr fun k => (hc k).symm⟩

/-- The approximating core sequence converges in mass and Dirichlet energy
simultaneously, with their sum equal to the squared form norm. -/
theorem exists_core_form_convergence (f : ScalarForm.Domain J) :
    ∃ c : ℕ → C, Tendsto (fun k =>
      ‖ScalarForm.value J (ScalarForm.ofCore J (c k) - f)‖ ^ 2 +
      ScalarForm.energy J (ScalarForm.ofCore J (c k) - f)
        (ScalarForm.ofCore J (c k) - f)) atTop (𝓝 0) := by
  obtain ⟨c, hc⟩ := exists_core_approximation J f
  refine ⟨c, ?_⟩
  have ht := (hc.sub (tendsto_const_nhds (x := f))).norm.pow 2
  simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    ScalarForm.norm_sq] using ht

end FormApproximation

section LipschitzBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsFiniteMeasure μ] {U : Set E}

/-- A Lipschitz observable with its actual a.e. gradient belongs to the landed
form domain, for every finite absolutely continuous weight on a bounded set.
This is a bridge to Riesz1, including weights singular at the boundary. -/
theorem lipschitz_mem_form (hU : IsOpen U) (hb : Bornology.IsBounded U)
    (hμ : ∀ᵐ x ∂μ, x ∈ U) (hac : μ ≪ volume)
    {F : E → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) :
    ∃ (h₀ : MemLp F 2 μ) (h₁ : MemLp (gradient F) 2 μ),
      WithLp.toLp 2 (h₀.toLp F, h₁.toLp (gradient F)) ∈
        ScalarForm.completionSubmodule (EuclideanScalarForm.smoothJet hU hb hμ) := by
  have h := Riesz1.WeightedSobolev.isWeightedH1_of_lipschitz hb hμ hac hF
  exact ⟨h.1, h.2.1,
    (EuclideanScalarForm.mem_completion_iff hU hb hμ F (gradient F) h.1 h.2.1).mpr h⟩

end LipschitzBridge

end Riesz2.CutoffApproximation
