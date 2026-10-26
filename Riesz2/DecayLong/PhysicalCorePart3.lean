/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.PhysicalCorePart2
public import Riesz2.ToMathlib.CenteredFourthOrderError
public import Riesz2.ToMathlib.PeriodicPowerTailComparison
public import Riesz2.Preliminaries.InverseIntervalKernelPart2

/-!
# Physical and sampled interval coefficients

The coefficient comparison used by the proof of Lemma 5.4, including
the regularized unit interval and a change of period. The coefficients are
the existing physical derivative and sampled second difference.
-/

public section
noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Riesz2.PhysicalCore

/-- See the proof of Lemma 5.4 in the paper (coefficient comparison): the lattice
curvature differs from the continuous power curvature by a fourth-order
error. The first site uses its prescribed regularization explicitly. -/
theorem lattice_curvature_error (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℤ, k ≠ 0 →
      |latticeRieszCurvature s k - s.val * (s.val + 1) * |(k : ℝ)| ^ (-s.val - 2)| ≤
        C * |(k : ℝ)| ^ (-s.val - 4) := by
  have hs : 0 < s.val := s.property.1
  let D := s.val * (s.val + 1) * (s.val + 2) * (s.val + 3) *
    (1 / 2 : ℝ) ^ (-s.val - 4) / 12
  let B := |(2 : ℝ) ^ (-s.val) - s.val * (s.val + 1)|
  refine ⟨1 + B + D, by dsimp only [B, D]; positivity, ?_⟩
  have hpos (r : ℤ) (hr : 1 ≤ r) :
      |latticeRieszCurvature s r - s.val * (s.val + 1) * (r : ℝ) ^ (-s.val - 2)| ≤
        (1 + B + D) * (r : ℝ) ^ (-s.val - 4) := by
    by_cases h1 : r = 1
    · subst r
      simp only [latticeRieszCurvature_one, Int.cast_one, Real.one_rpow, mul_one]
      change B ≤ 1 + B + D
      have hD : 0 ≤ D := by dsimp only [D]; positivity
      linarith
    · have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast (show (2 : ℤ) ≤ r by omega)
      have h := centeredSecondDifference_neg_rpow_error s.property.1.le hr2
      have he : latticeRieszCurvature s r =
          ((r : ℝ) + 1) ^ (-s.val) + ((r : ℝ) - 1) ^ (-s.val) -
            2 * (r : ℝ) ^ (-s.val) := by
        simp only [latticeRieszCurvature, latticeRieszKernel,
          show r + 1 ≠ 0 by omega, show r - 1 ≠ 0 by omega,
          show r ≠ 0 by omega, ite_false, Int.cast_add, Int.cast_sub, Int.cast_one,
          abs_of_pos (show (0 : ℝ) < r by linarith),
          abs_of_pos (show (0 : ℝ) < r + 1 by linarith),
          abs_of_pos (show (0 : ℝ) < r - 1 by linarith)]
      rw [he]
      exact h.trans (mul_le_mul_of_nonneg_right
        (by change D ≤ 1 + B + D; dsimp only [B]; linarith [abs_nonneg ((2 : ℝ) ^ (-s.val) - s.val * (s.val + 1))])
        (Real.rpow_nonneg (by linarith) _))
  intro k hk
  rcases lt_or_gt_of_ne hk with hn | hp
  · have h := hpos (-k) (by omega)
    simpa only [latticeRieszCurvature_even, Int.cast_neg,
      abs_of_neg (show (k : ℝ) < 0 by exact_mod_cast hn)] using h
  · simpa only [abs_of_pos (show (0 : ℝ) < k by exact_mod_cast hp)] using hpos k (by omega)

private theorem image_distance {r M : ℝ} (hr : 0 < r) (hM : 2 * r ≤ M) (k : ℤ) :
    r ≤ |r + k * M| := by
  have hM0 : 0 ≤ M := by linarith
  rcases le_total (0 : ℤ) k with hk | hk
  · have hkR : (0 : ℝ) ≤ k := by exact_mod_cast hk
    rw [abs_of_nonneg (by positivity)]
    nlinarith
  · by_cases h0 : k = 0
    · subst k; simpa only [Int.cast_zero, zero_mul, add_zero, abs_of_pos hr] using le_rfl (a := r)
    · have hkR : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
      have hmul := mul_le_mul_of_nonneg_right hkR (by linarith : 0 ≤ M)
      rw [abs_of_neg (by linarith : r + (k : ℝ) * M < 0)]
      linarith

/-- See the proof of Lemma 5.4 in the paper: the actual sampled second difference and
the continuous physical coefficient at the same period differ by
`C r^(-s-4)`, uniformly in the period, also at the regularized site `r=1`. -/
theorem sampled_coefficient_error (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : InverseTemperature) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
      (r : ℕ) (hr : 1 ≤ r) (hrM : 2 * r ≤ (M : ℕ)),
      let R : {L : ℝ // 0 < L ∧ L < (M : ℝ)} := ⟨r, by
        have hp : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
        have hh : 2 * (r : ℝ) ≤ M := by exact_mod_cast hrM
        exact ⟨hp, by linarith⟩⟩
      |sampledSecondDifference s M hM ⟨r, by omega⟩ -
        PhysicalEnergy.intervalCoefficient (ofLong β s) M R| ≤ C * (r : ℝ) ^ (-s.val - 4) := by
  obtain ⟨D, hD, hb⟩ := lattice_curvature_error s
  have hp : 1 < s.val + 4 := by linarith [s.property.1]
  refine ⟨D * PeriodicPower.bound (s.val + 4) hp,
    mul_pos hD (PeriodicPower.bound_pos _ hp), ?_⟩
  intro β M hM r hr hrM R
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hhalf : 2 * (r : ℝ) ≤ M := by exact_mod_cast hrM
  have ht := PeriodicPower.summable_and_le hp hr0 le_rfl (by linarith : (r : ℝ) ≤ M - r)
  have hs := PeriodicPower.summable_and_le (show 1 < s.val + 2 by linarith [s.property.1])
    hr0 le_rfl (by linarith : (r : ℝ) ≤ M - r)
  have he (k : ℤ) : (((r : ℤ) + k * (M : ℕ) : ℤ) : ℝ) = (r : ℝ) + k * M := by
    push_cast; rfl
  have hne (k : ℤ) : (r : ℤ) + k * (M : ℕ) ≠ 0 := by
    intro hz
    have hh := image_distance hr0 hhalf k
    rw [← he, hz] at hh
    norm_num at hh
    linarith
  have hcurv := (summable_norm_latticeRieszCurvature_images s M r).of_norm
  have hcont : Summable (fun k : ℤ => s.val * (s.val + 1) *
      |(r : ℝ) + k * M| ^ (-s.val - 2)) := by
    simpa only [show -(s.val + 2) = -s.val - 2 by ring] using hs.1.mul_left (s.val * (s.val + 1))
  have hmajor : Summable (fun k : ℤ => D * |(r : ℝ) + k * M| ^ (-s.val - 4)) := by
    simpa only [show -(s.val + 4) = -s.val - 4 by ring] using ht.1.mul_left D
  rw [sampledSecondDifference_periodization, PhysicalEnergy.intervalCoefficient_images]
  change |(∑' k : ℤ, latticeRieszCurvature s (↑r + k * ↑M)) -
    s.val * (s.val + 1) * ∑' k : ℤ, |(r : ℝ) + k * M| ^ (-s.val - 2)| ≤ _
  rw [← tsum_mul_left, ← hcurv.tsum_sub hcont, ← Real.norm_eq_abs]
  calc
    ‖∑' k : ℤ, (latticeRieszCurvature s (↑r + k * ↑M) -
        s.val * (s.val + 1) * |(r : ℝ) + k * M| ^ (-s.val - 2))‖ ≤
        ∑' k : ℤ, D * |(r : ℝ) + k * M| ^ (-s.val - 4) := by
      apply (norm_tsum_le_tsum_norm (hcurv.sub hcont).norm).trans
      apply (hcurv.sub hcont).norm.tsum_le_tsum _ hmajor
      intro k
      simpa only [Real.norm_eq_abs, he] using hb _ (hne k)
    _ = D * ∑' k : ℤ, |(r : ℝ) + k * M| ^ (-s.val - 4) := tsum_mul_left
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left ht.2 hD.le
      simpa only [show -(s.val + 4) = -s.val - 4 by ring, mul_assoc] using hh

/-- See the proof of Lemma 5.4 in the paper: changing the physical period changes
the actual derivative coefficient by at most `C M^(-s-2)`. Both evaluations
have a certified positive separation, and the constant precedes both periods. -/
theorem physical_coefficient_period_error (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : InverseTemperature) (N M : ℕ+)
      (_hM : 2 ≤ (M : ℕ)) (hMN : (M : ℕ) ≤ (N : ℕ))
      (x : ℝ) (hx : 0 < x) (hhalf : 2 * x ≤ (M : ℝ)),
      |PhysicalEnergy.intervalCoefficient (ofLong β s) N ⟨x, hx, by
          have hm : (M : ℝ) ≤ N := by exact_mod_cast hMN
          linarith⟩ -
        PhysicalEnergy.intervalCoefficient (ofLong β s) M ⟨x, hx, by linarith⟩| ≤
        C * (M : ℝ) ^ (-s.val - 2) := by
  obtain ⟨C, hC, hb⟩ := PeriodicPower.different_period_error
    (show 1 < s.val + 2 by linarith [s.property.1])
  have hs : 0 < s.val * (s.val + 1) := mul_pos s.property.1 (by linarith [s.property.1])
  refine ⟨s.val * (s.val + 1) * C, mul_pos hs hC, ?_⟩
  intro β N M hM hMN x hx hhalf
  rw [PhysicalEnergy.intervalCoefficient_images, PhysicalEnergy.intervalCoefficient_images]
  change |s.val * (s.val + 1) * _ - s.val * (s.val + 1) * _| ≤ _
  rw [← mul_sub, abs_mul, abs_of_pos hs]
  have h := hb (N := (N : ℝ)) (M := (M : ℝ))
    (by exact_mod_cast hM) (by exact_mod_cast hMN) hx hhalf
  have h' := mul_le_mul_of_nonneg_left h hs.le
  simpa only [ofLong, show -(s.val + 2) = -s.val - 2 by ring, mul_assoc] using h'

namespace Internal

/-- A physical short interval contained in a proper half-window does not
wrap through the exterior. This connects the physical and reference labels. -/
theorem internal_endpoints (N : ℕ+) (n : ℕ) (hn : 2 * n ≤ (N : ℕ))
    (i : Fin (N : ℕ)) (r : ℕ) (hr : 1 ≤ r) (_hrN : 2 * r ≤ (N : ℕ))
    (hi : ∀ j ∈ cyclicIndexInterval N i r, j.val < n) :
    i.val < n ∧ i.val + r ≤ n := by
  classical
  have hi0 : i ∈ cyclicIndexInterval N i r := by
    apply Finset.mem_image.mpr
    refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
    apply Fin.ext
    simp only [add_zero, Nat.mod_eq_of_lt i.isLt]
  have hin := hi i hi0
  refine ⟨hin, ?_⟩
  by_contra h
  have hnN : n < (N : ℕ) := by have := N.pos; omega
  have ht : n - i.val < r := by omega
  have hmem : (⟨n, hnN⟩ : Fin (N : ℕ)) ∈ cyclicIndexInterval N i r := by
    apply Finset.mem_image.mpr
    refine ⟨n - i.val, Finset.mem_range.mpr ht, ?_⟩
    apply Fin.ext
    simp only [show i.val + (n - i.val) = n by omega, Nat.mod_eq_of_lt hnN]
  have hh := hi ⟨n, hnN⟩ hmem
  change n < n at hh
  omega

/-- Internal interval sums in the physical chart equal the literal active
gap sum used by the good-event rigidity clause. -/
theorem internal_gapSum_active (n : ℕ+) (m : ℕ)
    (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (x : EuclideanSpace ℝ (Fin (n : ℕ)))
    (r : Fin (((n : ℕ) + m + 1) / 2)) (i : Fin ((n : ℕ) + m + 1))
    (hi : IntervalBoundary.IsInternal ((n : ℕ) + m).succPNat n (i, r)) :
    let j : Fin (n : ℕ) := ⟨i.val, (internal_endpoints ((n : ℕ) + m).succPNat n hn i (r.val + 1)
      (by omega) (by have := r.isLt; simp only [Nat.succPNat_coe]; omega) hi).1⟩
    cyclicGapSum ((n : ℕ) + m).succPNat i (r.val + 1)
      (WithLp.ofLp (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x, 0))) =
      cyclicGapSum n j (r.val + 1) (WithLp.ofLp x) := by
  intro j
  have he := internal_endpoints ((n : ℕ) + m).succPNat n hn i (r.val + 1)
    (by omega) (by have := r.isLt; simp only [Nat.succPNat_coe]; omega) hi
  unfold cyclicGapSum
  apply Finset.sum_congr rfl
  intro a ha
  have ha' := Finset.mem_range.mp ha
  have hai : i.val + a < (n : ℕ) := by omega
  have haiN : i.val + a < (n : ℕ) + m + 1 := by omega
  simp only [Nat.succPNat_coe, Nat.mod_eq_of_lt haiN,
    show j.val = i.val from rfl, Nat.mod_eq_of_lt hai]
  let b : Fin (n : ℕ) := ⟨i.val + a, hai⟩
  change RetainedSimplex.chart n m _ (Equiv.refl _) (x, 0) _ = x b
  exact RetainedSimplex.chart_retained n m _ (Equiv.refl _) x 0 b

/-- The three coefficient errors in the proof of Lemma 5.4, before
cyclic relabelling and summing intervals. The first term is physical
rigidity, the second is the fourth-order discretization error, and the
third comes from a change of period. At equal periods the third term is zero. -/
theorem physical_sampled_error (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : InverseTemperature) (N M : ℕ+)
      (hM : 2 ≤ (M : ℕ)) (_hMN : (M : ℕ) ≤ (N : ℕ))
      (r : ℕ) (hr : 1 ≤ r) (hrM : 2 * r ≤ (M : ℕ))
      (L : {L : ℝ // 0 < L ∧ L < (N : ℝ)}) (A : ℝ),
      |L.val - r| ≤ A * (r : ℝ) ^ (s.val / 2) →
      A * (r : ℝ) ^ (s.val / 2) ≤ (r : ℝ) / 2 →
      |PhysicalEnergy.intervalCoefficient (ofLong β s) N L -
        sampledSecondDifference s M hM ⟨r, by omega⟩| ≤
        C * (A * (r : ℝ) ^ (-3 - s.val / 2) + (r : ℝ) ^ (-s.val - 4) +
          if N = M then 0 else (M : ℝ) ^ (-s.val - 2)) := by
  obtain ⟨D, hD, hd⟩ := sampled_coefficient_error s
  obtain ⟨E, hE, he⟩ := physical_coefficient_period_error s
  let B := PhysicalEnergy.coefficientConstant s.val s.property.1
  have hB : 0 < B := PhysicalEnergy.coefficientConstant_pos s.val s.property.1
  let C := B + D + E
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro β N M hM hMN r hr hrM L A hdev hsmall
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hhalf : 2 * (r : ℝ) ≤ M := by exact_mod_cast hrM
  have hMN' : (M : ℝ) ≤ N := by exact_mod_cast hMN
  let R : {x : ℝ // 0 < x ∧ x < (N : ℝ)} := ⟨r, hr0, by linarith⟩
  let S : {x : ℝ // 0 < x ∧ x < (M : ℝ)} := ⟨r, hr0, by linarith⟩
  have h₁ := PhysicalEnergy.coefficient_variation (ofLong β s) N hr0
    (by linarith : (r : ℝ) ≤ N / 2) L hdev hsmall
  change |PhysicalEnergy.intervalCoefficient (ofLong β s) N L -
    PhysicalEnergy.intervalCoefficient (ofLong β s) N R| ≤ B * A * (r : ℝ) ^ (-3 - s.val / 2) at h₁
  have h₂ : |PhysicalEnergy.intervalCoefficient (ofLong β s) N R -
      PhysicalEnergy.intervalCoefficient (ofLong β s) M S| ≤
      E * (if N = M then 0 else (M : ℝ) ^ (-s.val - 2)) := by
    by_cases hNM : N = M
    · subst N
      simp only [R, S, sub_self, abs_zero, ↓reduceIte, mul_zero, le_refl]
    · simpa only [hNM, ↓reduceIte, R, S] using he β N M hM hMN r hr0 hhalf
  have h₃ := hd β M hM r hr hrM
  change |sampledSecondDifference s M hM ⟨r, by omega⟩ -
    PhysicalEnergy.intervalCoefficient (ofLong β s) M S| ≤ D * (r : ℝ) ^ (-s.val - 4) at h₃
  have hA : 0 ≤ A := by
    have hh := abs_nonneg (L.val - r)
    have hp := Real.rpow_pos_of_pos hr0 (s.val / 2)
    nlinarith
  have hp₁ : 0 ≤ A * (r : ℝ) ^ (-3 - s.val / 2) := mul_nonneg hA (Real.rpow_nonneg hr0.le _)
  have hp₂ : 0 ≤ (r : ℝ) ^ (-s.val - 4) := Real.rpow_nonneg hr0.le _
  have hp₃ : 0 ≤ (if N = M then 0 else (M : ℝ) ^ (-s.val - 2)) := by split_ifs <;> positivity
  have hsum : |PhysicalEnergy.intervalCoefficient (ofLong β s) N L -
      sampledSecondDifference s M hM ⟨r, by omega⟩| ≤
      (B * A * (r : ℝ) ^ (-3 - s.val / 2) +
        E * (if N = M then 0 else (M : ℝ) ^ (-s.val - 2))) +
        D * (r : ℝ) ^ (-s.val - 4) := by
    calc
      _ ≤ |PhysicalEnergy.intervalCoefficient (ofLong β s) N L -
          PhysicalEnergy.intervalCoefficient (ofLong β s) M S| +
          |PhysicalEnergy.intervalCoefficient (ofLong β s) M S -
            sampledSecondDifference s M hM ⟨r, by omega⟩| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add ((abs_sub_le _ (PhysicalEnergy.intervalCoefficient (ofLong β s) N R) _).trans
        (add_le_add h₁ h₂)) (by rw [abs_sub_comm]; exact h₃)
  apply hsum.trans
  dsimp only [C]
  nlinarith [mul_nonneg hB.le hp₂, mul_nonneg hB.le hp₃,
    mul_nonneg hD.le hp₁, mul_nonneg hD.le hp₃,
    mul_nonneg hE.le hp₁, mul_nonneg hE.le hp₂]

/-- The actual internal conditional coefficient comparison of the proof of Lemma 5.4, on the density-defined good event. Antipodal multiplicity
is retained literally. The threshold inequality is an internal input here.
The final matrix theorem must derive it from its cutoff. -/
theorem internal_coefficient_sampled_error (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : InverseTemperature) (n : ℕ+) (m : ℕ)
      (_hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
      (_hMN : (M : ℕ) ≤ (n : ℕ) + m + 1) (ε κ₀ : ℝ)
      (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
      (_hx : x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀)
      (r : Fin (((n : ℕ) + m + 1) / 2)) (i : Fin ((n : ℕ) + m + 1))
      (_hi : IntervalBoundary.IsInternal ((n : ℕ) + m).succPNat n (i, r))
      (hrM : 2 * (r.val + 1) ≤ (M : ℕ)),
      (n : ℝ) ^ ε * ((r.val + 1 : ℕ) : ℝ) ^ (s.val / 2) ≤
        ((r.val + 1 : ℕ) : ℝ) / 2 →
      |BoundaryEntries.conditionalIntervalWeight β s n m r i x -
        (2 - if 2 * (r.val + 1) = (n : ℕ) + m + 1 then (1 : ℝ) else 0) *
          sampledSecondDifference s M hM ⟨r.val + 1, by omega⟩| ≤
        C * ((n : ℝ) ^ ε * ((r.val + 1 : ℕ) : ℝ) ^ (-3 - s.val / 2) +
          ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 4) +
          if ((n : ℕ) + m).succPNat = M then 0 else (M : ℝ) ^ (-s.val - 2)) := by
  obtain ⟨C, hC, hb⟩ := physical_sampled_error s
  refine ⟨2 * C, by positivity, ?_⟩
  intro β n m hn M hM hMN ε κ₀ x hx r i hi hrM hsmall
  let N := ((n : ℕ) + m).succPNat
  have hrN : 2 * (r.val + 1) ≤ (N : ℕ) := by
    have := r.isLt
    simp only [N, Nat.succPNat_coe]
    omega
  have hend := internal_endpoints N n hn i (r.val + 1) (by omega) hrN hi
  let j : Fin (n : ℕ) := ⟨i.val, hend.1⟩
  let k : Fin ((n : ℕ) + 1) := ⟨r.val + 1, by omega⟩
  let L := cyclicGapSum N i (r.val + 1)
    (WithLp.ofLp (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val, 0)))
  have hdev : |L - (r.val + 1 : ℕ)| ≤
      (n : ℝ) ^ ε * ((r.val + 1 : ℕ) : ℝ) ^ (s.val / 2) := by
    have h := hx.1.2 j k (by dsimp only [k]; omega)
      (by dsimp only [k]; have := r.isLt; omega) (by dsimp only [j, k]; omega)
    dsimp only [L]
    rw [internal_gapSum_active n m hn x.val r i hi]
    exact h
  have h := hb β N M hM hMN (r.val + 1) (by omega) hrM
    ⟨L, internal_gapSum_mem β s n m x r i hi⟩ ((n : ℝ) ^ ε) hdev hsmall
  let w : ℝ := 2 - if 2 * (r.val + 1) = (N : ℕ) then 1 else 0
  have hw : 0 ≤ w ∧ w ≤ 2 := by dsimp only [w]; split_ifs <;> norm_num
  rw [internal_coefficient_formula β s n m x r i hi]
  change |w * PhysicalEnergy.intervalCoefficient (ofLong β s) N ⟨L, _⟩ - w * _| ≤ _
  rw [← mul_sub, abs_mul, abs_of_nonneg hw.1]
  have hnonneg : 0 ≤ C * ((n : ℝ) ^ ε * ((r.val + 1 : ℕ) : ℝ) ^ (-3 - s.val / 2) +
      ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 4) +
      if N = M then 0 else (M : ℝ) ^ (-s.val - 2)) :=
    (abs_nonneg _).trans h
  exact (mul_le_mul_of_nonneg_left h hw.1).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hw.2 hnonneg)

end Internal
end Riesz2.PhysicalCore
