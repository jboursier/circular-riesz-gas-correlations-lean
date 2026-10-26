/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.AngularBlocks
public import Riesz2.DecayLong.AngularPrimitiveBasic

/-!
# Angular block endpoint estimates

The ratio kernel and the counting measure L¹ and L² block bounds in the
proof of Lemma 5.9 of the paper, using actual smooth blocks supported
in angular annuli and the angular fractional primitive.
-/

@[expose] public section
noncomputable section

open Set Filter Topology
open scoped BigOperators ContDiff

namespace Riesz2.DiscreteInterpolation

local instance angularEstimatesPeriodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The localized symbol ratio in Lemma 5.9 of the paper.
On the punctured circle it is `p_t S_(s/2) / S_s`, expressed using the
reciprocal symbols. At the origin its block factor is zero, as it
is on a whole neighborhood of that point. -/
def angularSymbolRatio (s : Riesz1.RieszExponent) (t : ℝ) (ht : 0 < t)
    (x : AddCircle (2 * Real.pi)) : ℝ :=
  let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
    constructor <;> linarith [s.property.1, s.property.2]⟩
  (periodic_angularBlock t ht).lift x *
    reciprocalRieszSymbol s x / reciprocalRieszSymbol sh x

/-- The localized ratio agrees with the intended multiplier on its exact
open angular domain. For Lemma 5.9 of the paper. -/
theorem angularSymbolRatio_coe (s : Riesz1.RieszExponent) (t : ℝ) (ht : 0 < t)
    (θ : Ioo (0 : ℝ) (2 * Real.pi)) :
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    angularSymbolRatio s t ht (θ.val : AddCircle (2 * Real.pi)) =
      angularBlock t ht θ.val * (latticeRieszSymbol sh θ / latticeRieszSymbol s θ) := by
  dsimp only [angularSymbolRatio]
  rw [Function.Periodic.lift_coe, reciprocalRieszSymbol_coe, reciprocalRieszSymbol_coe]
  simp only [div_eq_mul_inv, inv_inv]
  ring

/-- The localized ratio has the same annular support as its actual block. For Lemma 5.9 of the paper. -/
theorem angularSymbolRatio_support (s : Riesz1.RieszExponent) (t : ℝ) (ht : 0 < t) :
    Function.support (fun θ : ℝ => angularSymbolRatio s t ht
      (θ : AddCircle (2 * Real.pi))) ⊆
        {θ | t ≤ FourierMultiplierKernels.angularRadius θ ∧ FourierMultiplierKernels.angularRadius θ ≤ 4 * t} := by
  intro θ hθ
  apply angularBlock_support ht
  intro he
  apply hθ
  simp only [angularSymbolRatio, Function.Periodic.lift_coe, he, zero_mul, zero_div]

/-- Near every point below the block support the localized ratio is
identically zero, including the angular seam. For Lemma 5.9 of the paper. -/
theorem angularSymbolRatio_eventually_zero (s : Riesz1.RieszExponent)
    {t θ : ℝ} (ht : 0 < t) (hθ : frequencyRadius θ < t) :
    (fun y : ℝ => angularSymbolRatio s t ht (y : AddCircle (2 * Real.pi))) =ᶠ[𝓝 θ]
      (fun _ => 0) := by
  filter_upwards [angularBlock_eventually_zero ht hθ] with y hy
  simp only [angularSymbolRatio, Function.Periodic.lift_coe, hy, zero_mul, zero_div]

/-- The localized ratio is smooth on the whole real lift, including every
copy of the seam. This supplies the periodic extension step implicit in
the proof of Lemma 5.9 of the paper. -/
theorem angularSymbolRatio_contDiff (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (t : ℝ) (ht : 0 < t) :
    ContDiff ℝ ∞ (fun y : ℝ => angularSymbolRatio s t ht
      (y : AddCircle (2 * Real.pi))) := by
  let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
    constructor <;> linarith [s.property.1, s.property.2]⟩
  let B : ℝ → ℝ := fun y => angularSymbolRatio s t ht (y : AddCircle (2 * Real.pi))
  have hcell (y : ℝ) (hy : y ∈ Ioo 0 (2 * Real.pi)) : ContDiffAt ℝ ∞ B y := by
    have hs := (reciprocalRieszSymbol_contDiffOn hz s).contDiffAt (isOpen_Ioo.mem_nhds hy)
    have hh := (reciprocalRieszSymbol_contDiffOn hz sh).contDiffAt (isOpen_Ioo.mem_nhds hy)
    have hne : reciprocalRieszSymbol sh (y : AddCircle (2 * Real.pi)) ≠ 0 := by
      rw [reciprocalRieszSymbol_coe sh ⟨y, hy⟩]
      exact inv_ne_zero (latticeRieszSymbol_pos sh _).ne'
    exact ((angularBlock_contDiff t ht).contDiffAt.mul hs).div hh hne
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : frequencyRadius x < t
  · exact contDiffAt_const.congr_of_eventuallyEq (angularSymbolRatio_eventually_zero s ht hx)
  · let y := AddCircle.equivIco (2 * Real.pi) 0 (x : AddCircle (2 * Real.pi))
    have hcoe : (y.val : AddCircle (2 * Real.pi)) = (x : AddCircle (2 * Real.pi)) :=
      AddCircle.coe_equivIco
    have hr : frequencyRadius y.val = frequencyRadius x :=
      congrArg periodic_frequencyRadius.lift hcoe
    have hy0 : 0 < y.val := by
      apply lt_of_le_of_ne y.property.1
      intro he
      have hz0 : frequencyRadius y.val = 0 := by simp only [← he, frequencyRadius, zero_div,
        Real.sin_zero, abs_zero, mul_zero]
      exact hx (by rw [← hr, hz0]; exact ht)
    have hy : y.val ∈ Ioo 0 (2 * Real.pi) := ⟨hy0, by simpa using y.property.2⟩
    have hshift : (fun z : ℝ => B (z + (y.val - x))) = B := by
      funext z
      apply congrArg (angularSymbolRatio s t ht)
      rw [AddCircle.coe_add, AddCircle.coe_sub, hcoe, sub_self, add_zero]
    have hc : ContDiffAt ℝ ∞ (fun z : ℝ => B (z + (y.val - x))) x := by
      have hc : ContDiffAt ℝ ∞ B (x + (y.val - x)) := by
        convert hcell y.val hy using 1; ring
      exact hc.comp x (contDiffAt_id.add contDiffAt_const)
    rwa [hshift] at hc

/-- All localized-ratio derivatives needed by the kernel lemma, uniformly
in the angular variable and the scale (Lemma 5.9 of the paper). -/
theorem angularSymbolRatio_derivative_bounds (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ t (ht : 0 < t), t ≤ 1 → ∀ j : ℕ, j ≤ 2 → ∀ x : ℝ,
      |iteratedDeriv j (fun y : ℝ => angularSymbolRatio s t ht
        (y : AddCircle (2 * Real.pi))) x| ≤ C * t ^ (-s.val / 2) / t ^ j := by
  obtain ⟨D, hD, hd⟩ := angularBlock_derivative_bounds
  obtain ⟨F, hF, heq, C, hC, hb⟩ := symbol_ratio_annular_derivative_bounds hz s
  refine ⟨4 * D * C, by positivity, fun t ht ht1 j hj x => ?_⟩
  let B : ℝ → ℝ := fun y => angularSymbolRatio s t ht (y : AddCircle (2 * Real.pi))
  have hcell (y : ℝ) (hy : y ∈ Ioo 0 (2 * Real.pi))
      (hρ : t ≤ frequencyRadius y) :
      |iteratedDeriv j B y| ≤ 4 * D * C * t ^ (-s.val / 2) / t ^ j := by
    have he : B =ᶠ[𝓝 y] (angularBlock t ht * F) := by
      filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz'
      exact (angularSymbolRatio_coe s t ht ⟨z, hz'⟩).trans
        (congrArg (angularBlock t ht z * ·) (heq ⟨z, hz'⟩).symm)
    rw [he.iteratedDeriv_eq j, iteratedDeriv_mul
      ((angularBlock_contDiff t ht).of_le (by simp)).contDiffAt
      ((hF.of_le (by simp)).contDiffAt (isOpen_Ioo.mem_nhds hy))]
    have hterm (i : ℕ) (hi : i ∈ Finset.range (j + 1)) :
        |(j.choose i : ℝ) * iteratedDeriv i (angularBlock t ht) y *
          iteratedDeriv (j - i) F y| ≤
        (j.choose i : ℝ) * (D * C * t ^ (-s.val / 2) / t ^ j) := by
      have hij : i ≤ j := by have := Finset.mem_range.mp hi; omega
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      calc
        _ ≤ ((j.choose i : ℝ) * (D / t ^ i)) *
            (C * t ^ (-s.val / 2 - ((j - i : ℕ) : ℝ))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hd t ht ht1 i (hij.trans hj) y hy)
            (Nat.cast_nonneg _)) (hb t ht (j - i) (by omega) ⟨y, hy⟩ hρ)
              (abs_nonneg _) (by positivity)
        _ = _ := by
          rw [← Real.rpow_natCast t i, ← Real.rpow_natCast t j, Nat.cast_sub hij]
          simp only [div_eq_mul_inv, ← Real.rpow_neg ht.le]
          have he : -(i : ℝ) + (-s.val / 2 - ((j : ℝ) - i)) =
              -s.val / 2 + -(j : ℝ) := by ring
          calc
            _ = ((j.choose i : ℝ) * D * C) *
                (t ^ (-(i : ℝ)) * t ^ (-s.val / 2 - ((j : ℝ) - i))) := by ring_nf
            _ = _ := by rw [← Real.rpow_add ht, he, Real.rpow_add ht]; ring_nf
    calc
      _ ≤ ∑ i ∈ Finset.range (j + 1),
          |(j.choose i : ℝ) * iteratedDeriv i (angularBlock t ht) y *
            iteratedDeriv (j - i) F y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * (D * C * t ^ (-s.val / 2) / t ^ j) := Finset.sum_le_sum hterm
      _ = (2 : ℝ) ^ j * (D * C * t ^ (-s.val / 2) / t ^ j) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose j
      _ ≤ 4 * (D * C * t ^ (-s.val / 2) / t ^ j) :=
        mul_le_mul_of_nonneg_right
          ((pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj).trans_eq (by norm_num))
          (by positivity)
      _ = _ := by ring
  by_cases hx : frequencyRadius x < t
  · rw [(angularSymbolRatio_eventually_zero s ht hx).iteratedDeriv_eq j]
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
    have hshift : (fun z : ℝ => B (z + (y.val - x))) = B := by
      funext z
      apply congrArg (angularSymbolRatio s t ht)
      rw [AddCircle.coe_add, AddCircle.coe_sub, hcoe, sub_self, add_zero]
    have hder := congrFun (iteratedDeriv_comp_add_const j B (y.val - x)) x
    rw [hshift, show x + (y.val - x) = y.val by ring] at hder
    exact hder ▸ hcell y.val hy (by rw [hr]; exact le_of_not_gt hx)

/-- The annular ratio has a counting-measure cyclic kernel bounded by
`C(s) t^(-s/2)`, the localized analytic step of Lemma 5.9 of the paper. -/
theorem angularSymbolRatio_kernel_bound (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ t (ht : 0 < t), t ≤ 1 → ∀ (N : ℕ+), 2 ≤ (N : ℕ) →
      (∑ i : Fin (N : ℕ), ‖cycleFourierInv N (fun k =>
        (angularSymbolRatio s t ht (cycleAngle N k : AddCircle (2 * Real.pi)) : ℂ)) i‖)
          ≤ C * t ^ (-s.val / 2) := by
  obtain ⟨C, hC, hb⟩ := angularSymbolRatio_derivative_bounds hz s
  obtain ⟨K, hK, hk⟩ := FourierMultiplierKernels.localized_fourierMultiplier_kernel_circle
  refine ⟨K * C, by positivity, fun t ht ht1 N hN => ?_⟩
  let B : ℝ → ℝ := fun y => angularSymbolRatio s t ht (y : AddCircle (2 * Real.pi))
  have hB : ContDiff ℝ ∞ B := angularSymbolRatio_contDiff hz s t ht
  have hc : Continuous (fun x : AddCircle (2 * Real.pi) =>
      (angularSymbolRatio s t ht x : ℂ)) :=
    (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (2 * Real.pi))).continuous_iff.mpr
      (Complex.continuous_ofReal.comp hB.continuous)
  let b : C(AddCircle (2 * Real.pi), ℂ) := ⟨_, hc⟩
  have hbc : ContDiff ℝ ∞ (fun y : ℝ => b (y : AddCircle (2 * Real.pi))) :=
    Complex.ofRealCLM.contDiff.comp hB
  have hs : Function.support (fun y : ℝ => b (y : AddCircle (2 * Real.pi))) ⊆
      {θ | t ≤ FourierMultiplierKernels.angularRadius θ ∧ FourierMultiplierKernels.angularRadius θ ≤ 4 * t} := by
    intro y hy
    apply angularSymbolRatio_support s t ht
    simpa only [b, ContinuousMap.coe_mk, Function.mem_support, Complex.ofReal_ne_zero] using hy
  have hd (j : ℕ) (hj : j ≤ 2) (x : ℝ) :
      ‖iteratedDeriv j (fun y : ℝ => b (y : AddCircle (2 * Real.pi))) x‖ ≤
        (C * t ^ (-s.val / 2)) / t ^ j := by
    have he := iteratedDeriv_smul_const (n := j) (x := x)
      (hB.of_le (by simp)).contDiffAt (1 : ℂ)
    simp only [Complex.real_smul, mul_one] at he
    change ‖iteratedDeriv j (fun y : ℝ => (B y : ℂ)) x‖ ≤ _
    rw [he, Complex.norm_real, Real.norm_eq_abs]
    exact hb t ht ht1 j hj x
  have h := hk (C * t ^ (-s.val / 2)) (by positivity) N hN t ht b
    (hbc.of_le (by simp)) hs hd
  have hkernel : (∑ i : Fin (N : ℕ), ‖cycleFourierInv N (fun k =>
      (angularSymbolRatio s t ht (cycleAngle N k : AddCircle (2 * Real.pi)) : ℂ)) i‖) ≤
      K * C * t ^ (-s.val / 2) := by
    simpa only [b, ContinuousMap.coe_mk, mul_assoc] using h
  exact hkernel

/-- The `ℓ¹` block estimate in Lemma 5.9 of the paper, using the
actual sampled kernel on both sides. -/
theorem angular_block_l1 (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent) :
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    ∃ C : ℝ, 0 < C ∧ ∀ t (ht : 0 < t), t ≤ 1 →
      ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (u : Fin (N : ℕ) → ℂ),
      let w := cycleConvolution N (fun i => (sampledRieszKernel sh N hN i : ℂ)) u
      let v := cycleConvolution N (fun i => (sampledRieszKernel s N hN i : ℂ)) u
      (∑ i, ‖cycleFourierInv N (fun k =>
        (angularBlock t ht (cycleAngle N k) : ℂ) * cycleFourier N w k) i‖) ≤
          C * t ^ (-s.val / 2) * (∑ i, ‖v i‖) := by
  dsimp only
  let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
    constructor <;> linarith [s.property.1, s.property.2]⟩
  obtain ⟨C, hC, hb⟩ := angularSymbolRatio_kernel_bound hz s
  refine ⟨C, hC, fun t ht ht1 N hN u => ?_⟩
  let w := cycleConvolution N (fun i => (sampledRieszKernel sh N hN i : ℂ)) u
  let v := cycleConvolution N (fun i => (sampledRieszKernel s N hN i : ℂ)) u
  have he (k : Fin (N : ℕ)) :
      (angularBlock t ht (cycleAngle N k) : ℂ) * cycleFourier N w k =
        (angularSymbolRatio s t ht (cycleAngle N k : AddCircle (2 * Real.pi)) : ℂ) *
          cycleFourier N v k := by
    by_cases hk : k = 0
    · subst k
      simp only [angularBlock_cycleAngle_zero, Complex.ofReal_zero, zero_mul]
      have he : angularSymbolRatio s t ht (cycleAngle N 0 : AddCircle (2 * Real.pi)) = 0 := by
        simp only [angularSymbolRatio, Function.Periodic.lift_coe,
          angularBlock_cycleAngle_zero, zero_mul, zero_div]
      rw [he, Complex.ofReal_zero, zero_mul]
    · rw [show cycleFourier N w k = _ from cycleFourier_convolution _ _ k,
        show cycleFourier N v k = _ from cycleFourier_convolution _ _ k,
        sampledRieszKernel_nonzero_eigenvalue sh N hN k hk,
        sampledRieszKernel_nonzero_eigenvalue s N hN k hk,
        angularSymbolRatio_coe s t ht ⟨cycleAngle N k, cycleAngle_mem_Ioo N k hk⟩]
      push_cast
      have hne : (latticeRieszSymbol s ⟨cycleAngle N k, cycleAngle_mem_Ioo N k hk⟩ : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (latticeRieszSymbol_pos s _).ne'
      dsimp only [sh]
      field_simp
  change (∑ i, ‖cycleFourierInv N (fun k =>
    (angularBlock t ht (cycleAngle N k) : ℂ) * cycleFourier N w k) i‖) ≤
      C * t ^ (-s.val / 2) * (∑ i, ‖v i‖)
  simp_rw [he]
  rw [multiplier_eq_convolution]
  exact (cycleConvolution_l1 N _ v).trans
    (mul_le_mul_of_nonneg_right (hb t ht ht1 N hN) (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))

/-- The `ℓ²` multiplier envelope in the proof of Lemma 5.9 of the paper. -/
theorem angular_symbol_primitive_annular_bound (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    ∃ C : ℝ, 0 < C ∧ ∀ t (ht : 0 < t),
      ∀ θ : Ioo (0 : ℝ) (2 * Real.pi),
        |angularBlock t ht θ.val * latticeRieszSymbol sh θ *
          FourierMultiplierKernels.angularRadius θ.val ^ (3 / 2 - s.val)| ≤ C * t ^ ((1 - s.val) / 2) := by
  dsimp only
  let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
    constructor <;> linarith [s.property.1, s.property.2]⟩
  obtain ⟨_, C, _, hC, hb⟩ := latticeRieszSymbol_power_bounds hz sh
  let r := (1 - s.val) / 2
  have hr : 0 < r := by dsimp [r]; linarith [s.property.2]
  refine ⟨C * (4 : ℝ) ^ r, by positivity, fun t ht θ => ?_⟩
  by_cases hp : angularBlock t ht θ.val = 0
  · simp only [hp, zero_mul, abs_zero]
    positivity
  · have hθ := angularBlock_support ht hp
    have hρ : 0 < FourierMultiplierKernels.angularRadius θ.val := ht.trans_le hθ.1
    rw [abs_mul, abs_mul, abs_of_nonneg (angularBlock_bounds t ht θ.val).1,
      abs_of_pos (latticeRieszSymbol_pos sh θ), abs_of_pos (Real.rpow_pos_of_pos hρ _)]
    have hb' : latticeRieszSymbol sh θ ≤
        C * FourierMultiplierKernels.angularRadius θ.val ^ (sh.val - 1) := by
      simpa only [FourierMultiplierKernels.angularRadius_eq_min
        ⟨θ.property.1.le, θ.property.2.le⟩, symbolEndpointDistance] using (hb θ).2
    calc
      _ ≤ (1 * (C * FourierMultiplierKernels.angularRadius θ.val ^ (sh.val - 1))) *
          FourierMultiplierKernels.angularRadius θ.val ^ (3 / 2 - s.val) :=
        mul_le_mul_of_nonneg_right (mul_le_mul (angularBlock_bounds t ht θ.val).2 hb'
          (latticeRieszSymbol_pos sh θ).le (by norm_num)) (by positivity)
      _ = C * FourierMultiplierKernels.angularRadius θ.val ^ r := by
        rw [one_mul, mul_assoc, ← Real.rpow_add hρ]
        congr 2
        dsimp [sh, r]
        ring
      _ ≤ C * (4 * t) ^ r := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hρ.le hθ.2 hr.le) hC.le
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) ht.le]; ring

/-- The `ℓ²` block estimate in Lemma 5.9 of the paper. The last
inverse transform is exactly the multiplier defining `J_(3/2-s)` in
Subsection 5.2. Its zero mode is explicitly removed. -/
theorem angular_block_l2 (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent) :
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    ∃ C : ℝ, 0 < C ∧ ∀ t (ht : 0 < t),
      ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (u : Fin (N : ℕ) → ℂ),
      let w := cycleConvolution N (fun i => (sampledRieszKernel sh N hN i : ℂ)) u
      let J := angularPrimitive N (3 / 2 - s.val) u
      (∑ i, ‖cycleFourierInv N (fun k =>
        (angularBlock t ht (cycleAngle N k) : ℂ) * cycleFourier N w k) i‖ ^ 2) ^ (1 / 2 : ℝ) ≤
          C * t ^ ((1 - s.val) / 2) * (∑ i, ‖J i‖ ^ 2) ^ (1 / 2 : ℝ) := by
  dsimp only
  let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
    constructor <;> linarith [s.property.1, s.property.2]⟩
  obtain ⟨C, hC, hb⟩ := angular_symbol_primitive_annular_bound hz s
  refine ⟨C, hC, fun t ht N hN u => ?_⟩
  let w := cycleConvolution N (fun i => (sampledRieszKernel sh N hN i : ℂ)) u
  let J := angularPrimitive N (3 / 2 - s.val) u
  let b : Fin (N : ℕ) → ℂ := fun k =>
    (angularBlock t ht (cycleAngle N k) : ℂ) *
      cycleFourier N (fun i => (sampledRieszKernel sh N hN i : ℂ)) k *
        (FourierMultiplierKernels.angularRadius (cycleAngle N k) ^ (3 / 2 - s.val) : ℝ)
  have hbm (k : Fin (N : ℕ)) : ‖b k‖ ≤ C * t ^ ((1 - s.val) / 2) := by
    by_cases hk : k = 0
    · subst k
      simp only [b, angularBlock_cycleAngle_zero, Complex.ofReal_zero,
        zero_mul, norm_zero]
      positivity
    · dsimp only [b]
      rw [sampledRieszKernel_nonzero_eigenvalue sh N hN k hk, ← Complex.ofReal_mul,
        ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs]
      exact hb t ht ⟨cycleAngle N k, cycleAngle_mem_Ioo N k hk⟩
  have he (k : Fin (N : ℕ)) :
      (angularBlock t ht (cycleAngle N k) : ℂ) * cycleFourier N w k =
        b k * cycleFourier N J k := by
    dsimp only [J, angularPrimitive]
    rw [cycleFourier_cycleFourierInv]
    simp only [angularPrimitiveSymbol]
    by_cases hk : k = 0
    · subst k
      simp only [angularBlock_cycleAngle_zero, Complex.ofReal_zero, zero_mul,
        ite_true, mul_zero]
    · rw [ite_eq_right hk, show cycleFourier N w k = _ from cycleFourier_convolution _ _ k]
      have hρ : 0 < FourierMultiplierKernels.angularRadius (cycleAngle N k) := by
        obtain ⟨hr, hc, _⟩ := angularRadius_cycle_comparison N k hk
        exact hr.trans_le hc
      have hpow : (FourierMultiplierKernels.angularRadius (cycleAngle N k) ^ (3 / 2 - s.val) : ℝ) *
          FourierMultiplierKernels.angularRadius (cycleAngle N k) ^ (-(3 / 2 - s.val)) = 1 := by
        rw [← Real.rpow_add hρ, add_neg_cancel, Real.rpow_zero]
      have hpowc : (FourierMultiplierKernels.angularRadius (cycleAngle N k) ^ (3 / 2 - s.val) : ℝ) *
          (FourierMultiplierKernels.angularRadius (cycleAngle N k) ^ (-(3 / 2 - s.val)) : ℝ) = (1 : ℂ) := by
        exact_mod_cast hpow
      dsimp only [b]
      symm
      calc
        _ = ((angularBlock t ht (cycleAngle N k) : ℂ) *
            cycleFourier N (fun i => (sampledRieszKernel sh N hN i : ℂ)) k) *
            ((FourierMultiplierKernels.angularRadius (cycleAngle N k) ^ (3 / 2 - s.val) : ℝ) *
              (FourierMultiplierKernels.angularRadius (cycleAngle N k) ^ (-(3 / 2 - s.val)) : ℝ)) *
              cycleFourier N u k := by ring
        _ = _ := by rw [hpowc]; ring
  change (∑ i, ‖cycleFourierInv N (fun k =>
    (angularBlock t ht (cycleAngle N k) : ℂ) * cycleFourier N w k) i‖ ^ 2) ^ (1 / 2 : ℝ) ≤
      C * t ^ ((1 - s.val) / 2) * (∑ i, ‖J i‖ ^ 2) ^ (1 / 2 : ℝ)
  simp_rw [he]
  have hh := Real.rpow_le_rpow
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (multiplier_l2_sq N b J (by positivity) hbm) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  simp only [one_div] at hh ⊢
  have hroot : ((C * t ^ ((1 - s.val) / 2)) ^ 2) ^ (2 : ℝ)⁻¹ =
      C * t ^ ((1 - s.val) / 2) := by
    simpa only [Nat.cast_ofNat] using Real.pow_rpow_inv_natCast
      (by positivity : 0 ≤ C * t ^ ((1 - s.val) / 2)) (by norm_num : (2 : ℕ) ≠ 0)
  rw [Real.mul_rpow (sq_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)), hroot] at hh
  exact hh


end Riesz2.DiscreteInterpolation
