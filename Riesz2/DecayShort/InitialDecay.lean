/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.ComponentDistance
public import Riesz2.ToMathlib.CyclicDistance
public import Riesz2.ToMathlib.RpowPartialSums
public import Riesz2.DecayShort.AbstractEnergy
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Short-range distortion weights and inherited geometry

These bridges transport the cyclic geometry to the line/cycle
encoding. In particular the estimates retain the ambient labels on subsets.
No bound on the diameter or on the cardinality of the component set is used.
The distortion weights are those of Subsection 4.1.
`commutator_estimate_sqrt_local` proves Lemma 4.3 of the paper,
uniformly over inherited subsets, with the sharp square-root local loss.
`commutation_estimate` is a corollary. The final
internal lemmas justify weighted weak testing for Lemma 4.4.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace Riesz2.ComponentGeometryBounds

variable {ι : Type*}

/-- The inherited distance is nonnegative. -/
theorem nonneg (g : ComponentGeometry ι) (i j : ι) :
    0 ≤ componentDistance g i j := by
  rcases g with e | ⟨m, e⟩
  · exact abs_nonneg _
  · exact Nat.cast_nonneg _

/-- The inherited distance vanishes at the centre. -/
theorem self (g : ComponentGeometry ι) (i : ι) :
    componentDistance g i i = 0 := by
  rcases g with e | ⟨m, e⟩
  · simp [componentDistance]
  · simp [componentDistance, Riesz2.cyclicIndexDistance_self]

/-- Symmetry is retained by both ambient embeddings. -/
theorem symm (g : ComponentGeometry ι) (i j : ι) :
    componentDistance g i j = componentDistance g j i := by
  rcases g with e | ⟨m, e⟩
  · exact abs_sub_comm _ _
  · simp [componentDistance, Riesz1.cyclicIndexDistance, Nat.dist_comm]

/-- The inherited distance satisfies the triangle inequality. -/
theorem triangle (g : ComponentGeometry ι) (i j k : ι) :
    componentDistance g i k ≤ componentDistance g i j + componentDistance g j k := by
  rcases g with e | ⟨m, e⟩
  · exact abs_sub_le _ _ _
  · simp only [componentDistance]
    exact_mod_cast Riesz2.cyclicIndexDistance_triangle (e i) (e j) (e k)

/-- The radius `1 + d(i,i₀)` is a one-Lipschitz function of the label. -/
theorem abs_radius_sub_le (g : ComponentGeometry ι) (i₀ i j : ι) :
    |(1 + componentDistance g i i₀) - (1 + componentDistance g j i₀)| ≤
      componentDistance g i j := by
  rw [abs_le]
  constructor
  · have h := triangle g j i i₀
    rw [symm g j i] at h
    linarith
  · have h := triangle g i j i₀
    linarith

/-- Inherited distances are integer-valued, including on a sparsely embedded subset. -/
theorem exists_nat (g : ComponentGeometry ι) (i j : ι) :
    ∃ k : ℕ, componentDistance g i j = k := by
  rcases g with e | ⟨m, e⟩
  · refine ⟨(e i - e j).natAbs, ?_⟩
    change |(e i : ℝ) - (e j : ℝ)| = _
    rw [← Int.cast_sub, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  · exact ⟨_, rfl⟩

variable [Fintype ι]

/-- Every shell in a component geometry has at most two points.
This includes the zero and antipodal shells and arbitrary inherited subsets. -/
theorem card_shell_le_two (g : ComponentGeometry ι) (i : ι) (k : ℕ) :
    (Finset.univ.filter fun j => componentDistance g i j = k).card ≤ 2 := by
  classical
  rcases g with e | ⟨m, e⟩
  · let S := Finset.univ.filter fun j => componentDistance (Sum.inl e) i j = k
    have hsub : S.image e ⊆ {e i + (k : ℤ), e i - (k : ℤ)} := by
      intro a ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
      have hj' := (Finset.mem_filter.mp hj).2
      change |(e i : ℝ) - (e j : ℝ)| = (k : ℝ) at hj'
      have hz : |e i - e j| = (k : ℤ) := by exact_mod_cast hj'
      rcases (abs_eq (Int.natCast_nonneg k)).mp hz with hz | hz
      · apply Finset.mem_insert.mpr
        right
        apply Finset.mem_singleton.mpr
        omega
      · apply Finset.mem_insert.mpr
        left
        omega
    calc S.card = (S.image e).card := (Finset.card_image_of_injective S e.injective).symm
      _ ≤ ({e i + (k : ℤ), e i - (k : ℤ)} : Finset ℤ).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two
  · let S := Finset.univ.filter fun j => componentDistance (Sum.inr ⟨m, e⟩) i j = k
    have hsub : S.image e ⊆ Riesz2.cyclicShell m (e i) k := by
      intro a ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
      have hj' := (Finset.mem_filter.mp hj).2
      simp only [componentDistance] at hj'
      have hk : Riesz1.cyclicIndexDistance m (e i) (e j) = k := by exact_mod_cast hj'
      simp only [Riesz2.cyclicShell, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hk
    calc S.card = (S.image e).card := (Finset.card_image_of_injective S e.injective).symm
      _ ≤ (Riesz2.cyclicShell m (e i) k).card := Finset.card_le_card hsub
      _ ≤ 2 := Riesz2.card_cyclicShell_le_two (e i) k

/-- A nonnegative summable radial profile has a uniform finite sum, by shell counting. -/
theorem sum_profile_le (g : ComponentGeometry ι) (i : ι) (f : ℕ → ℝ)
    (hf : ∀ k, 0 ≤ f k) (hs : Summable f) :
    ∑ j, f ⌊componentDistance g i j⌋₊ ≤ 2 * ∑' k, f k := by
  classical
  let R := Finset.univ.image (fun j => ⌊componentDistance g i j⌋₊)
  have hm : ∀ j ∈ (Finset.univ : Finset ι), ⌊componentDistance g i j⌋₊ ∈ R := by
    intro j hj
    exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hm]
  calc (∑ k ∈ R, ∑ j ∈ Finset.univ.filter
        (fun j => ⌊componentDistance g i j⌋₊ = k), f ⌊componentDistance g i j⌋₊)
      ≤ ∑ k ∈ R, 2 * f k := by
        apply Finset.sum_le_sum
        intro k _
        have he : (Finset.univ.filter fun j => ⌊componentDistance g i j⌋₊ = k) =
            (Finset.univ.filter fun j => componentDistance g i j = k) := by
          ext j
          obtain ⟨l, hl⟩ := exists_nat g i j
          simp [hl]
        rw [Finset.sum_congr rfl (fun j hj => congrArg f (Finset.mem_filter.mp hj).2),
          Finset.sum_const, nsmul_eq_mul, he]
        apply mul_le_mul_of_nonneg_right _ (hf k)
        exact_mod_cast card_shell_le_two g i k
    _ = 2 * ∑ k ∈ R, f k := (Finset.mul_sum ..).symm
    _ ≤ 2 * ∑' k, f k := by
      exact mul_le_mul_of_nonneg_left (hs.sum_le_tsum R (fun k _ => hf k)) (by norm_num)

/-- The summable power bound is uniform in the ambient size and the inherited subset. -/
theorem sum_power_le (g : ComponentGeometry ι) (i : ι) {t : ℝ} (ht : 1 < t) :
    ∑ j, (1 + componentDistance g i j) ^ (-t) ≤
      2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-t) := by
  have h := sum_profile_le g i (fun k => (1 + (k : ℝ)) ^ (-t))
    (fun k => Real.rpow_nonneg (by positivity) _) (Riesz2.summable_one_add_rpow_neg ht)
  convert h using 1
  apply Finset.sum_congr rfl
  intro j _
  obtain ⟨k, hk⟩ := exists_nat g i j
  simp [hk]

/-- A ball in the inherited geometry contains at most two labels per integer radius. -/
theorem card_ball_le (g : ComponentGeometry ι) (i : ι) {R : ℝ} (hR : 0 ≤ R) :
    ((Finset.univ.filter fun j => componentDistance g i j ≤ R).card : ℝ) ≤ 2 * (R + 1) := by
  classical
  let S := Finset.univ.filter fun j => componentDistance g i j ≤ R
  have hm : ∀ j ∈ S, ⌊componentDistance g i j⌋₊ ∈ Finset.range (⌊R⌋₊ + 1) := by
    intro j hj
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le
      (Nat.floor_mono (Finset.mem_filter.mp hj).2))
  have hc := Finset.card_eq_sum_card_fiberwise hm
  have hb : S.card ≤ 2 * (⌊R⌋₊ + 1) := by
    rw [hc]
    calc _ ≤ ∑ k ∈ Finset.range (⌊R⌋₊ + 1), 2 := by
          apply Finset.sum_le_sum
          intro k _
          have hsub : (S.filter fun j => ⌊componentDistance g i j⌋₊ = k) ⊆
              (Finset.univ.filter fun j => componentDistance g i j = k) := by
            intro j hj
            obtain ⟨l, hl⟩ := exists_nat g i j
            have hk := (Finset.mem_filter.mp hj).2
            simpa [hl] using hk
          exact (Finset.card_le_card hsub).trans (card_shell_le_two g i k)
      _ = _ := by simp [Nat.mul_comm]
  have hcast : (S.card : ℝ) ≤ 2 * ((⌊R⌋₊ : ℝ) + 1) := by exact_mod_cast hb
  exact hcast.trans (by linarith [Nat.floor_le hR])

/-- Square sums of radial powers, with a constant uniform over inherited subsets. -/
theorem sum_radius_sq_le (g : ComponentGeometry ι) (i₀ : ι)
    {p : ℝ} (hp : p < -(1 / 2)) :
    ∑ i, ((1 + componentDistance g i i₀) ^ p) ^ 2 ≤
      2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(-2 * p)) := by
  have he : (∑ i, ((1 + componentDistance g i i₀) ^ p) ^ 2) =
      ∑ i, (1 + componentDistance g i₀ i) ^ (-(-2 * p)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Real.rpow_mul_natCast (by linarith [nonneg g i i₀]), symm g i i₀]
    congr 1
    norm_num
    ring
  rw [he]
  exact sum_power_le g i₀ (by linarith)

end Riesz2.ComponentGeometryBounds

namespace Riesz2.InitialDecay.Internal

/-- Uniform bound for a real power on the fixed comparison interval. -/
theorem rpow_le_two_rpow_abs {x p : ℝ} (hx : x ∈ Set.Icc (1 / 2 : ℝ) 2) :
    x ^ p ≤ 2 ^ |p| := by
  have hx0 : 0 < x := by linarith [hx.1]
  rcases le_total 0 p with hp | hp
  · rw [abs_of_nonneg hp]
    exact Real.rpow_le_rpow hx0.le hx.2 hp
  · rw [abs_of_nonpos hp]
    calc x ^ p ≤ (1 / 2 : ℝ) ^ p :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hx.1 hp
      _ = 2 ^ (-p) := by rw [one_div, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num)]

/-- Mean-value bound for a distortion ratio on the comparison interval. -/
theorem rpow_sub_one_le {x : ℝ} (a : ℝ) (hx : x ∈ Set.Icc (1 / 2 : ℝ) 2) :
    |x ^ a - 1| ≤ (|a| * 2 ^ |a - 1|) * |x - 1| := by
  have hd : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 2,
      DifferentiableAt ℝ (fun t : ℝ => t ^ a) t := by
    intro t ht
    exact (Real.hasDerivAt_rpow_const (Or.inl (by linarith [ht.1]))).differentiableAt
  have hb : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 2,
      ‖deriv (fun t : ℝ => t ^ a) t‖ ≤ |a| * 2 ^ |a - 1| := by
    intro t ht
    rw [Real.deriv_rpow_const, norm_mul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith [ht.1]) _)]
    exact mul_le_mul_of_nonneg_left (rpow_le_two_rpow_abs ht) (abs_nonneg a)
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_Icc _ _)
    (by norm_num : (1 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 2) hx
  simpa only [Real.one_rpow, Real.norm_eq_abs] using hh

/-- A ratio in `[1/2,2]` has a fractional modulus with any exponent in `(0,1]`.
The strict exponent bound is used for summability. -/
theorem rpow_sub_one_le_fractional {x ρ : ℝ} (a : ℝ)
    (hx : x ∈ Set.Icc (1 / 2 : ℝ) 2) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    |x ^ a - 1| ≤ (|a| * 2 ^ |a - 1|) * |x - 1| ^ ρ := by
  have hsmall : |x - 1| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  have hp : |x - 1| ≤ |x - 1| ^ ρ := by
    by_cases hz : x - 1 = 0
    · simp [hz, Real.zero_rpow hρ.ne']
    · have hp0 : 0 < |x - 1| := abs_pos.mpr hz
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_ge hp0 hsmall hρ1
  exact (rpow_sub_one_le a hx).trans
    (mul_le_mul_of_nonneg_left hp (by positivity))

end Riesz2.InitialDecay.Internal

namespace Riesz2.InitialDecay

variable {ι : Type*}

/-- See Subsection 4.1 of the paper: the positive distortion weight on each component.
The geometry supplies the inherited distance, including on subsets. -/
def distortionWeight (g : ComponentGeometry ι) (i₀ : ι) (a : ℝ) (i : ι) : ℝ :=
  (1 + componentDistance g i i₀) ^ a

/-- Distortion weights are strictly positive for every real exponent. -/
theorem distortionWeight_pos (g : ComponentGeometry ι) (i₀ : ι) (a : ℝ) (i : ι) :
    0 < distortionWeight g i₀ a i := by
  apply Real.rpow_pos_of_pos
  linarith [ComponentGeometryBounds.nonneg g i i₀]

/-- The weight of the point source is exactly one. -/
theorem distortionWeight_center (g : ComponentGeometry ι) (i₀ : ι) (a : ℝ) :
    distortionWeight g i₀ a i₀ = 1 := by
  simp [distortionWeight, ComponentGeometryBounds.self]

/-- The negative exponent is the actual inverse of the distortion weight. -/
theorem distortionWeight_neg (g : ComponentGeometry ι) (i₀ : ι) (a : ℝ) (i : ι) :
    distortionWeight g i₀ (-a) i = (distortionWeight g i₀ a i)⁻¹ := by
  exact Real.rpow_neg (by linarith [ComponentGeometryBounds.nonneg g i i₀]) a

/-- Distortion weights compose additively in the exponent. -/
theorem distortionWeight_add (g : ComponentGeometry ι) (i₀ : ι) (a b : ℝ) (i : ι) :
    distortionWeight g i₀ (a + b) i =
      distortionWeight g i₀ a i * distortionWeight g i₀ b i := by
  exact Real.rpow_add (by linarith [ComponentGeometryBounds.nonneg g i i₀]) a b

variable [Fintype ι] [DecidableEq ι]

/-- The diagonal matrix `Wₐ` of Subsection 4.1. -/
def distortionMatrix (g : ComponentGeometry ι) (i₀ : ι) (a : ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal (distortionWeight g i₀ a)

/-- The diagonal matrix at the negative exponent is a two-sided inverse. -/
theorem distortionMatrix_mul_neg (g : ComponentGeometry ι) (i₀ : ι) (a : ℝ) :
    distortionMatrix g i₀ a * distortionMatrix g i₀ (-a) = 1 := by
  rw [distortionMatrix, distortionMatrix, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [distortionWeight_neg, ne_of_gt (distortionWeight_pos g i₀ a i)]
  · simp [Matrix.diagonal, hij]

/-- Entrywise form of the distortion commutator in Lemma 4.3, without any symmetry requirement on the matrix. -/
theorem commutator_entry (g : ComponentGeometry ι) (i₀ : ι) (a : ℝ)
    (M : Matrix ι ι ℝ) (i j : ι) :
    (distortionMatrix g i₀ a * M * distortionMatrix g i₀ (-a) - M) i j =
      M i j * (distortionWeight g i₀ a i / distortionWeight g i₀ a j - 1) := by
  simp only [distortionMatrix, Matrix.sub_apply, Matrix.diagonal_mul,
    Matrix.mul_diagonal, distortionWeight_neg, div_eq_mul_inv]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- The ratio of two distortion weights is controlled by the distance between
their labels. This estimate retains the original ambient metric. -/
theorem distortionWeight_ratio_le (g : ComponentGeometry ι) (i₀ : ι)
    {a : ℝ} (ha : 0 ≤ a) (i j : ι) :
    distortionWeight g i₀ a i / distortionWeight g i₀ a j ≤
      (1 + componentDistance g i j) ^ a := by
  have hi := ComponentGeometryBounds.nonneg g i i₀
  have hj := ComponentGeometryBounds.nonneg g j i₀
  have hd := ComponentGeometryBounds.nonneg g i j
  have ht := ComponentGeometryBounds.triangle g i j i₀
  have hbase : (1 + componentDistance g i i₀) /
      (1 + componentDistance g j i₀) ≤ 1 + componentDistance g i j := by
    rw [div_le_iff₀ (by linarith : 0 < 1 + componentDistance g j i₀)]
    nlinarith [mul_nonneg hd hj]
  unfold distortionWeight
  rw [← Real.div_rpow (by linarith) (by linarith)]
  apply Real.rpow_le_rpow (by positivity) hbase ha

/-- A square-summable column envelope for the commutator. The condition
`a < s - 1/2` in Lemma 4.3 is exactly what makes
the square of this envelope summable. -/
theorem commutator_entry_bound (g : ComponentGeometry ι) (i₀ : ι)
    {a s B : ℝ} (ha : 0 ≤ a) (hB : 0 ≤ B) (M : Matrix ι ι ℝ)
    (hM : ∀ i j, |M i j| ≤ B * (1 + componentDistance g i j) ^ (-s))
    (i j : ι) :
    |(distortionMatrix g i₀ a * M * distortionMatrix g i₀ (-a) - M) i j| ≤
      2 * B * (1 + componentDistance g i j) ^ (a - s) := by
  have hd := ComponentGeometryBounds.nonneg g i j
  have hb : 0 < 1 + componentDistance g i j := by linarith
  have hw : 0 ≤ distortionWeight g i₀ a i / distortionWeight g i₀ a j :=
    div_nonneg (distortionWeight_pos g i₀ a i).le (distortionWeight_pos g i₀ a j).le
  have hp : 1 ≤ (1 + componentDistance g i j) ^ a :=
    Real.one_le_rpow (by linarith) ha
  have hr : |distortionWeight g i₀ a i / distortionWeight g i₀ a j - 1| ≤
      2 * (1 + componentDistance g i j) ^ a := by
    apply (abs_sub _ _).trans
    rw [abs_of_nonneg hw, abs_one]
    linarith [distortionWeight_ratio_le g i₀ ha i j]
  rw [commutator_entry, abs_mul]
  calc |M i j| * |distortionWeight g i₀ a i / distortionWeight g i₀ a j - 1|
      ≤ (B * (1 + componentDistance g i j) ^ (-s)) *
          (2 * (1 + componentDistance g i j) ^ a) :=
        mul_le_mul (hM i j) hr (abs_nonneg _) (by positivity)
    _ = 2 * B * (1 + componentDistance g i j) ^ (a - s) := by
      rw [sub_eq_add_neg, Real.rpow_add hb]
      ring

/-- Uniform squared column and row bounds for the distortion commutator.
This is the local part of Lemma 4.3. -/
theorem commutator_column_sq_le (g : ComponentGeometry ι) (i₀ : ι)
    {a s B : ℝ} (ha : 0 ≤ a) (has : a < s - 1 / 2) (hB : 0 ≤ B)
    (M : Matrix ι ι ℝ)
    (hM : ∀ i j, |M i j| ≤ B * (1 + componentDistance g i j) ^ (-s)) (j : ι) :
    ∑ i, ((distortionMatrix g i₀ a * M * distortionMatrix g i₀ (-a) - M) i j) ^ 2 ≤
      8 * B ^ 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(2 * (s - a))) := by
  calc (∑ i, ((distortionMatrix g i₀ a * M * distortionMatrix g i₀ (-a) - M) i j) ^ 2)
      ≤ ∑ i, 4 * B ^ 2 * (1 + componentDistance g j i) ^ (-(2 * (s - a))) := by
        apply Finset.sum_le_sum
        intro i _
        have h := commutator_entry_bound g i₀ ha hB M hM i j
        have hh := mul_self_le_mul_self (abs_nonneg _) h
        rw [← pow_two, sq_abs] at hh
        have hp : (1 + componentDistance g i j) ^ (a - s) *
            (1 + componentDistance g i j) ^ (a - s) =
            (1 + componentDistance g i j) ^ (-(2 * (s - a))) := by
          rw [← Real.rpow_add (by linarith [ComponentGeometryBounds.nonneg g i j])]
          congr 1
          ring
        rw [ComponentGeometryBounds.symm g j i]
        nlinarith [hp]
    _ = 4 * B ^ 2 * ∑ i, (1 + componentDistance g j i) ^ (-(2 * (s - a))) :=
      (Finset.mul_sum ..).symm
    _ ≤ 4 * B ^ 2 * (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(2 * (s - a)))) := by
      apply mul_le_mul_of_nonneg_left (ComponentGeometryBounds.sum_power_le g j (by linarith))
      positivity
    _ = _ := by ring

/-- The comparable-radii part of Lemma 4.3.
Its radial decay loss is any exponent at most one. Summing the right side
will require `ρ < s - 1`. -/
theorem comparable_commutator_entry_bound (g : ComponentGeometry ι) (i₀ : ι)
    {a s B K ρ : ℝ} (hB : 0 ≤ B) (hK : 0 < K) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (M : Matrix ι ι ℝ)
    (hM : ∀ i j, |M i j| ≤ B * (1 + componentDistance g i j) ^ (-s))
    (i j : ι)
    (hcomp : (1 + componentDistance g i i₀) /
      (1 + componentDistance g j i₀) ∈ Set.Icc (1 / 2 : ℝ) 2)
    (hjK : K ≤ 1 + componentDistance g j i₀) :
    |(distortionMatrix g i₀ a * M * distortionMatrix g i₀ (-a) - M) i j| ≤
      (|a| * 2 ^ |a - 1|) * B * K ^ (-ρ) *
        (1 + componentDistance g i j) ^ (-(s - ρ)) := by
  have hi0 : 0 < 1 + componentDistance g i i₀ := by
    linarith [ComponentGeometryBounds.nonneg g i i₀]
  have hj0 : 0 < 1 + componentDistance g j i₀ := by
    linarith [ComponentGeometryBounds.nonneg g j i₀]
  have hd0 : 0 < 1 + componentDistance g i j := by
    linarith [ComponentGeometryBounds.nonneg g i j]
  have hr : |(1 + componentDistance g i i₀) / (1 + componentDistance g j i₀) - 1| ≤
      (1 + componentDistance g i j) / K := by
    have ht := ComponentGeometryBounds.abs_radius_sub_le g i₀ i j
    calc _ = |(1 + componentDistance g i i₀) - (1 + componentDistance g j i₀)| /
          (1 + componentDistance g j i₀) := by
            rw [div_sub_one hj0.ne', abs_div, abs_of_pos hj0]
      _ ≤ componentDistance g i j / (1 + componentDistance g j i₀) :=
        div_le_div_of_nonneg_right ht hj0.le
      _ ≤ (1 + componentDistance g i j) / K := by
        calc _ ≤ (1 + componentDistance g i j) / (1 + componentDistance g j i₀) :=
              div_le_div_of_nonneg_right (by linarith) hj0.le
          _ ≤ _ := div_le_div_of_nonneg_left hd0.le hK hjK
  have hp := Real.rpow_le_rpow (abs_nonneg _) hr hρ.le
  have hh := (Internal.rpow_sub_one_le_fractional a hcomp hρ hρ1).trans
    (mul_le_mul_of_nonneg_left hp (by positivity))
  have hw : distortionWeight g i₀ a i / distortionWeight g i₀ a j =
      ((1 + componentDistance g i i₀) / (1 + componentDistance g j i₀)) ^ a := by
    exact (Real.div_rpow hi0.le hj0.le a).symm
  rw [commutator_entry, abs_mul, hw]
  calc _ ≤ (B * (1 + componentDistance g i j) ^ (-s)) *
        ((|a| * 2 ^ |a - 1|) * ((1 + componentDistance g i j) / K) ^ ρ) :=
      mul_le_mul (hM i j) hh (abs_nonneg _) (by positivity)
    _ = _ := by
      rw [Real.div_rpow hd0.le hK.le, div_eq_mul_inv, ← Real.rpow_neg hK.le,
        show -(s - ρ) = ρ + -s by ring, Real.rpow_add hd0]
      ring

/-- The growing-ratio part of Lemma 4.3 factors
into two radial profiles. Their squares are summable when
`1/2 < a` and `a + ρ < s - 1/2`. -/
theorem separated_commutator_entry_bound (g : ComponentGeometry ι) (i₀ : ι)
    {a s B K ρ : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (hB : 0 ≤ B)
    (hK : 0 < K) (hρ : 0 ≤ ρ) (M : Matrix ι ι ℝ)
    (hM : ∀ i j, |M i j| ≤ B * (1 + componentDistance g i j) ^ (-s))
    (i j : ι)
    (hsep : 2 * (1 + componentDistance g j i₀) ≤ 1 + componentDistance g i i₀)
    (hiK : K ≤ 1 + componentDistance g i i₀) :
    |(distortionMatrix g i₀ a * M * distortionMatrix g i₀ (-a) - M) i j| ≤
      2 ^ s * B * K ^ (-ρ) *
        (1 + componentDistance g i i₀) ^ (a + ρ - s) *
        (1 + componentDistance g j i₀) ^ (-a) := by
  let r := 1 + componentDistance g i i₀
  let t := 1 + componentDistance g j i₀
  let D := 1 + componentDistance g i j
  have hr : 0 < r := by dsimp [r]; linarith [ComponentGeometryBounds.nonneg g i i₀]
  have ht : 0 < t := by dsimp [t]; linarith [ComponentGeometryBounds.nonneg g j i₀]
  have hD : 0 < D := by dsimp [D]; linarith [ComponentGeometryBounds.nonneg g i j]
  have ht1 : t ≤ r := by change 2 * t ≤ r at hsep; linarith
  have hDr : r / 2 ≤ D := by
    have hh := ComponentGeometryBounds.abs_radius_sub_le g i₀ i j
    change |r - t| ≤ componentDistance g i j at hh
    rw [abs_of_nonneg (sub_nonneg.mpr ht1)] at hh
    change 2 * t ≤ r at hsep
    dsimp [D]
    linarith
  have hpow : D ^ (-s) ≤ 2 ^ s * r ^ (-s) := by
    calc D ^ (-s) ≤ (r / 2) ^ (-s) :=
          Real.rpow_le_rpow_of_nonpos (div_pos hr two_pos) hDr (by linarith)
      _ = _ := by
        rw [Real.div_rpow hr.le (by norm_num),
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) s, div_inv_eq_mul]
        ring
  have hw1 : 1 ≤ r ^ a / t ^ a := by
    rw [le_div_iff₀ (Real.rpow_pos_of_pos ht a), one_mul]
    exact Real.rpow_le_rpow ht.le ht1 ha
  have hw : |distortionWeight g i₀ a i / distortionWeight g i₀ a j - 1| ≤
      r ^ a / t ^ a := by
    change |r ^ a / t ^ a - 1| ≤ r ^ a / t ^ a
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hkr : r ^ (-ρ) ≤ K ^ (-ρ) :=
    Real.rpow_le_rpow_of_nonpos hK hiK (by linarith)
  have he : r ^ (-s) * (r ^ a / t ^ a) =
      r ^ (-ρ) * r ^ (a + ρ - s) * t ^ (-a) := by
    calc _ = r ^ (-s + a) * t ^ (-a) := by
          rw [Real.rpow_add hr, Real.rpow_neg ht.le, div_eq_mul_inv]
          ring
      _ = _ := by
        rw [← Real.rpow_add hr]
        congr 1
        congr 1
        ring
  rw [commutator_entry, abs_mul]
  calc _ ≤ (B * D ^ (-s)) * (r ^ a / t ^ a) :=
      mul_le_mul (hM i j) hw (abs_nonneg _) (by positivity)
    _ ≤ (B * (2 ^ s * r ^ (-s))) * (r ^ a / t ^ a) := by
      gcongr
    _ = (2 ^ s * B) * (r ^ (-ρ) * r ^ (a + ρ - s) * t ^ (-a)) := by
      calc _ = (2 ^ s * B) * (r ^ (-s) * (r ^ a / t ^ a)) := by ring
        _ = _ := by rw [he]
    _ ≤ (2 ^ s * B) * (K ^ (-ρ) * r ^ (a + ρ - s) * t ^ (-a)) := by
      gcongr
    _ = _ := by ring

end Riesz2.InitialDecay

namespace Riesz2.InitialDecay

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Reversing a decreasing weight ratio only increases its absolute distortion.
The transpose retains the original entry, so no symmetry of `M` is assumed. -/
theorem commutator_transpose_le (g : ComponentGeometry ι) (i₀ : ι)
    {a : ℝ} (ha : 0 ≤ a) (M : Matrix ι ι ℝ) (i j : ι)
    (hij : componentDistance g i i₀ ≤ componentDistance g j i₀) :
    |(distortionMatrix g i₀ a * M * distortionMatrix g i₀ (-a) - M) i j| ≤
      |(distortionMatrix g i₀ a * M.transpose * distortionMatrix g i₀ (-a) - M.transpose) j i| := by
  let x := distortionWeight g i₀ a i
  let y := distortionWeight g i₀ a j
  have hx : 0 < x := distortionWeight_pos g i₀ a i
  have hy : 0 < y := distortionWeight_pos g i₀ a j
  have hxy : x ≤ y := Real.rpow_le_rpow
    (by linarith [ComponentGeometryBounds.nonneg g i i₀]) (by linarith) ha
  rw [commutator_entry, commutator_entry, Matrix.transpose_apply, abs_mul, abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg (M i j))
  change |x / y - 1| ≤ |y / x - 1|
  rw [abs_of_nonpos (by rw [sub_nonpos, div_le_one hy]; exact hxy),
    abs_of_nonneg (by rw [sub_nonneg, le_div_iff₀ hx, one_mul]; exact hxy)]
  have hleft : -(x / y - 1) = (y - x) / y := by field_simp; ring
  have hright : y / x - 1 = (y - x) / x := by field_simp
  rw [hleft, hright]
  exact div_le_div_of_nonneg_left (sub_nonneg.mpr hxy) hx hxy

/-- Exterior entries are bounded by one summable distance kernel and two
products of square-summable radial profiles. This is the complete entrywise
decomposition in Lemma 4.3. -/
theorem exterior_commutator_entry_bound (g : ComponentGeometry ι) (i₀ : ι)
    {a s B K ρ : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (hB : 0 ≤ B)
    (hK : 0 < K) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (M : Matrix ι ι ℝ)
    (hM : ∀ i j, |M i j| ≤ B * (1 + componentDistance g i j) ^ (-s))
    (i j : ι) (hiK : K ≤ 1 + componentDistance g i i₀)
    (hjK : K ≤ 1 + componentDistance g j i₀) :
    |(distortionMatrix g i₀ a * M * distortionMatrix g i₀ (-a) - M) i j| ≤
      (|a| * 2 ^ |a - 1|) * B * K ^ (-ρ) *
        (1 + componentDistance g i j) ^ (-(s - ρ)) +
      2 ^ s * B * K ^ (-ρ) *
        ((1 + componentDistance g i i₀) ^ (a + ρ - s) *
            (1 + componentDistance g j i₀) ^ (-a) +
          (1 + componentDistance g j i₀) ^ (a + ρ - s) *
            (1 + componentDistance g i i₀) ^ (-a)) := by
  have hi : 0 < 1 + componentDistance g i i₀ := by
    linarith [ComponentGeometryBounds.nonneg g i i₀]
  have hj : 0 < 1 + componentDistance g j i₀ := by
    linarith [ComponentGeometryBounds.nonneg g j i₀]
  have hn1 : 0 ≤ (|a| * 2 ^ |a - 1|) * B * K ^ (-ρ) *
      (1 + componentDistance g i j) ^ (-(s - ρ)) := by
    have hd := ComponentGeometryBounds.nonneg g i j
    positivity
  have hn2 : 0 ≤ 2 ^ s * B * K ^ (-ρ) *
      (1 + componentDistance g i i₀) ^ (a + ρ - s) *
      (1 + componentDistance g j i₀) ^ (-a) := by positivity
  have hn3 : 0 ≤ 2 ^ s * B * K ^ (-ρ) *
      (1 + componentDistance g j i₀) ^ (a + ρ - s) *
      (1 + componentDistance g i i₀) ^ (-a) := by positivity
  by_cases hfar : 2 * (1 + componentDistance g j i₀) ≤ 1 + componentDistance g i i₀
  · have hh := separated_commutator_entry_bound g i₀ ha hs hB hK hρ.le M hM i j hfar hiK
    nlinarith only [hh, hn1, hn3]
  by_cases hrev : 2 * (1 + componentDistance g i i₀) ≤ 1 + componentDistance g j i₀
  · have hMt : ∀ i j, |M.transpose i j| ≤ B * (1 + componentDistance g i j) ^ (-s) := by
      intro i j
      simpa only [Matrix.transpose_apply, ComponentGeometryBounds.symm g j i] using hM j i
    have hh := (commutator_transpose_le g i₀ ha M i j (by linarith)).trans
      (separated_commutator_entry_bound g i₀ ha hs hB hK hρ.le M.transpose hMt j i hrev hjK)
    nlinarith only [hh, hn1, hn2]
  · have hcomp : (1 + componentDistance g i i₀) / (1 + componentDistance g j i₀) ∈
        Set.Icc (1 / 2 : ℝ) 2 := by
      constructor
      · rw [le_div_iff₀ hj]
        linarith
      · rw [div_le_iff₀ hj]
        linarith
    exact (comparable_commutator_entry_bound g i₀ hB hK hρ hρ1 M hM i j hcomp hjK).trans
      (le_add_of_nonneg_right (by positivity))

end Riesz2.InitialDecay

namespace Riesz2.InitialDecay.Internal

variable {ι : Type*} [Fintype ι]

/-- Finite Schur's estimate for a nonnegative kernel. No symmetry or
positivity of the matrix whose entries it bounds is needed. -/
theorem schur_quadratic_le (H : ι → ι → ℝ) (hH : ∀ i j, 0 ≤ H i j)
    (R C : ℝ) (hR : ∀ i, ∑ j, H i j ≤ R) (hC : ∀ j, ∑ i, H i j ≤ C)
    (u : ι → ℝ) :
    ∑ i, ∑ j, |u i| * H i j * |u j| ≤ (R + C) / 2 * ∑ i, u i ^ 2 := by
  have hr : (∑ i, ∑ j, H i j * u i ^ 2) ≤ R * ∑ i, u i ^ 2 := by
    calc _ = ∑ i, (∑ j, H i j) * u i ^ 2 := by simp only [Finset.sum_mul]
      _ ≤ ∑ i, R * u i ^ 2 := by
        exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hR i) (sq_nonneg _)
      _ = _ := (Finset.mul_sum ..).symm
  have hc : (∑ i, ∑ j, H i j * u j ^ 2) ≤ C * ∑ i, u i ^ 2 := by
    rw [Finset.sum_comm]
    calc _ = ∑ j, (∑ i, H i j) * u j ^ 2 := by simp only [Finset.sum_mul]
      _ ≤ ∑ j, C * u j ^ 2 := by
        exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hC j) (sq_nonneg _)
      _ = _ := (Finset.mul_sum ..).symm
  have hp : 2 * (∑ i, ∑ j, |u i| * H i j * |u j|) ≤
      (∑ i, ∑ j, H i j * u i ^ 2) + (∑ i, ∑ j, H i j * u j ^ 2) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    have hh := mul_nonneg (hH i j) (sq_nonneg (|u i| - |u j|))
    simp only [sub_sq, sq_abs] at hh
    nlinarith only [hh]
  nlinarith

/-- The product of two square-summable radial profiles bounds the associated
rank-one quadratic form. This is the separated-radii Cauchy–Schwarz step. -/
theorem rankOne_quadratic_le (P Q : ι → ℝ) (_hP : ∀ i, 0 ≤ P i)
    (hQ : ∀ i, 0 ≤ Q i) (u : ι → ℝ) :
    ∑ i, ∑ j, |u i| * (P i * Q j) * |u j| ≤
      Real.sqrt (∑ i, P i ^ 2) * Real.sqrt (∑ i, Q i ^ 2) * ∑ i, u i ^ 2 := by
  have hp := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ P (fun i => |u i|)
  have hq := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ Q (fun i => |u i|)
  simp only [sq_abs] at hp hq
  have hprod := mul_le_mul hp hq
    (Finset.sum_nonneg fun i _ => mul_nonneg (hQ i) (abs_nonneg _)) (by positivity)
  calc _ = (∑ i, P i * |u i|) * (∑ j, Q j * |u j|) := by
        symm
        rw [Finset.sum_mul]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ ≤ _ := hprod.trans_eq (by
      have hsq := Real.sq_sqrt (Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (u i)))
      calc _ = Real.sqrt (∑ i, P i ^ 2) * Real.sqrt (∑ i, Q i ^ 2) *
            (Real.sqrt (∑ i, u i ^ 2)) ^ 2 := by ring
        _ = _ := by rw [hsq])

/-- Uniform squared column bounds control the part touching a fixed set of
source labels. Only the size of that local set enters. -/
theorem local_columns_le (A : Matrix ι ι ℝ) (L : ℝ) (_hL : 0 ≤ L)
    (hA : ∀ j, ∑ i, A i j ^ 2 ≤ L) (S : Finset ι) (u : ι → ℝ) :
    ∑ j ∈ S, (∑ i, |u i| * |A i j|) * |u j| ≤
      Real.sqrt L * Real.sqrt (∑ i, u i ^ 2) *
        Real.sqrt (S.card : ℝ) * Real.sqrt (∑ j ∈ S, u j ^ 2) := by
  have hcol (j : ι) : (∑ i, |u i| * |A i j|) ≤
      Real.sqrt L * Real.sqrt (∑ i, u i ^ 2) := by
    have hh := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (fun i => |u i|) (fun i => |A i j|)
    simp only [sq_abs] at hh
    exact hh.trans (by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hA j)) (Real.sqrt_nonneg _))
  have hs : ∑ j ∈ S, |u j| ≤ Real.sqrt (S.card : ℝ) * Real.sqrt (∑ j ∈ S, u j ^ 2) := by
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, sq_abs] using
      Real.sum_mul_le_sqrt_mul_sqrt S (fun _ => (1 : ℝ)) (fun j => |u j|)
  calc _ ≤ ∑ j ∈ S, (Real.sqrt L * Real.sqrt (∑ i, u i ^ 2)) * |u j| :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hcol j) (abs_nonneg _)
    _ = (Real.sqrt L * Real.sqrt (∑ i, u i ^ 2)) * ∑ j ∈ S, |u j| :=
      (Finset.mul_sum ..).symm
    _ ≤ (Real.sqrt L * Real.sqrt (∑ i, u i ^ 2)) *
        (Real.sqrt (S.card : ℝ) * Real.sqrt (∑ j ∈ S, u j ^ 2)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

/-- Glue an exterior quadratic bound to uniform squared row and column bounds.
The local vector norm appears with one power, as required for absorption. -/
theorem local_exterior_quadratic_le [DecidableEq ι]
    (A : Matrix ι ι ℝ) (H : ι → ι → ℝ) (hH : ∀ i j, 0 ≤ H i j)
    (S : Finset ι) (hA : ∀ i ∉ S, ∀ j ∉ S, |A i j| ≤ H i j)
    (R L : ℝ) (hL : 0 ≤ L)
    (hcol : ∀ j, ∑ i, A i j ^ 2 ≤ L) (hrow : ∀ i, ∑ j, A i j ^ 2 ≤ L)
    (u : ι → ℝ)
    (hquad : (∑ i, ∑ j, |u i| * H i j * |u j|) ≤ R * ∑ i, u i ^ 2) :
    |∑ i, ∑ j, u i * A i j * u j| ≤
      R * ∑ i, u i ^ 2 + 2 * Real.sqrt L * Real.sqrt (∑ i, u i ^ 2) *
        Real.sqrt (S.card : ℝ) * Real.sqrt (∑ j ∈ S, u j ^ 2) := by
  have hp (i j : ι) : |u i| * |A i j| * |u j| ≤
      |u i| * H i j * |u j| +
        (if j ∈ S then |u i| * |A i j| * |u j| else 0) +
        (if i ∈ S then |u i| * |A i j| * |u j| else 0) := by
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
    · simp only [hi, hj, ↓reduceIte]
      nlinarith [mul_nonneg (mul_nonneg (abs_nonneg (u i)) (hH i j)) (abs_nonneg (u j)),
        mul_nonneg (mul_nonneg (abs_nonneg (u i)) (abs_nonneg (A i j))) (abs_nonneg (u j))]
    · simp only [hi, hj, ↓reduceIte, add_zero]
      exact le_add_of_nonneg_left
        (mul_nonneg (mul_nonneg (abs_nonneg _) (hH i j)) (abs_nonneg _))
    · simp only [hi, hj, ↓reduceIte, add_zero]
      exact le_add_of_nonneg_left
        (mul_nonneg (mul_nonneg (abs_nonneg _) (hH i j)) (abs_nonneg _))
    · simp only [hi, hj, ↓reduceIte, add_zero]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hA i hi j hj) (abs_nonneg _)) (abs_nonneg _)
  have habs : |∑ i, ∑ j, u i * A i j * u j| ≤
      ∑ i, ∑ j, |u i| * |A i j| * |u j| := by
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans_eq
        (by simp only [abs_mul]))
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hp i j))
  have hc := local_columns_le A L hL hcol S u
  have hr := local_columns_le A.transpose L hL hrow S u
  have he : (∑ i, ∑ j,
      (|u i| * H i j * |u j| +
        (if j ∈ S then |u i| * |A i j| * |u j| else 0) +
        (if i ∈ S then |u i| * |A i j| * |u j| else 0))) =
      (∑ i, ∑ j, |u i| * H i j * |u j|) +
        (∑ j ∈ S, (∑ i, |u i| * |A i j|) * |u j|) +
        (∑ i ∈ S, (∑ j, |u j| * |A.transpose j i|) * |u i|) := by
    simp only [Finset.sum_add_distrib]
    congr 1
    · congr 1
      rw [Finset.sum_comm]
      simp [Finset.sum_ite_irrel, Finset.sum_mul]
    · simp [Finset.sum_ite_irrel, Finset.mul_sum, mul_comm, mul_left_comm]
  rw [he] at hsum
  linarith [habs.trans hsum]

/-- Sum the distance kernel and the two separated radial kernels together.
All three bounds are independent of the ambient size and of the subset. -/
theorem composite_kernel_quadratic_le (g : ComponentGeometry ι) (i₀ : ι)
    {t p q c d : ℝ} (ht : 1 < t) (hp : p < -(1 / 2)) (hq : q < -(1 / 2))
    (hc : 0 ≤ c) (hd : 0 ≤ d) (u : ι → ℝ) :
    (∑ i, ∑ j, |u i| *
        (c * (1 + componentDistance g i j) ^ (-t) + d *
          ((1 + componentDistance g i i₀) ^ p * (1 + componentDistance g j i₀) ^ q +
            (1 + componentDistance g j i₀) ^ p * (1 + componentDistance g i i₀) ^ q)) * |u j|) ≤
      (c * (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-t)) +
        2 * d * Real.sqrt (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(-2 * p))) *
          Real.sqrt (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(-2 * q)))) * ∑ i, u i ^ 2 := by
  let P := fun i => (1 + componentDistance g i i₀) ^ p
  let Q := fun i => (1 + componentDistance g i i₀) ^ q
  let D := fun i j => (1 + componentDistance g i j) ^ (-t)
  let F := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(-2 * p))
  let G := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(-2 * q))
  let T := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-t)
  have hP (i : ι) : 0 ≤ P i := Real.rpow_nonneg (by linarith [ComponentGeometryBounds.nonneg g i i₀]) _
  have hQ (i : ι) : 0 ≤ Q i := Real.rpow_nonneg (by linarith [ComponentGeometryBounds.nonneg g i i₀]) _
  have hD (i j : ι) : 0 ≤ D i j := Real.rpow_nonneg (by linarith [ComponentGeometryBounds.nonneg g i j]) _
  have hPs : ∑ i, P i ^ 2 ≤ F := ComponentGeometryBounds.sum_radius_sq_le g i₀ hp
  have hQs : ∑ i, Q i ^ 2 ≤ G := ComponentGeometryBounds.sum_radius_sq_le g i₀ hq
  have hR (i : ι) : ∑ j, D i j ≤ T := ComponentGeometryBounds.sum_power_le g i ht
  have hC (j : ι) : ∑ i, D i j ≤ T := by
    simpa only [D, ComponentGeometryBounds.symm g] using ComponentGeometryBounds.sum_power_le g j ht
  have hdist := schur_quadratic_le D hD T T hR hC u
  have hdist' : (∑ i, ∑ j, |u i| * D i j * |u j|) ≤ T * ∑ i, u i ^ 2 := by
    convert hdist using 1
    ring
  have hPQ : (∑ i, ∑ j, |u i| * (P i * Q j) * |u j|) ≤
      Real.sqrt F * Real.sqrt G * ∑ i, u i ^ 2 := by
    apply (rankOne_quadratic_le P Q hP hQ u).trans
    gcongr
  have hQP : (∑ i, ∑ j, |u i| * (P j * Q i) * |u j|) ≤
      Real.sqrt F * Real.sqrt G * ∑ i, u i ^ 2 := by
    have he : (∑ i, ∑ j, |u i| * (P j * Q i) * |u j|) =
        ∑ i, ∑ j, |u i| * (Q i * P j) * |u j| := by
      simp only [mul_comm (P _)]
    rw [he, mul_comm (Real.sqrt F) (Real.sqrt G)]
    apply (rankOne_quadratic_le Q P hQ hP u).trans
    gcongr
  have he : (∑ i, ∑ j, |u i| * (c * D i j + d * (P i * Q j + P j * Q i)) * |u j|) =
      c * (∑ i, ∑ j, |u i| * D i j * |u j|) +
        d * ((∑ i, ∑ j, |u i| * (P i * Q j) * |u j|) +
          (∑ i, ∑ j, |u i| * (P j * Q i) * |u j|)) := by
    simp only [Finset.mul_sum, mul_add, add_mul, Finset.sum_add_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    · congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
        apply Finset.sum_congr rfl <;> intro j _ <;> ring
  change (∑ i, ∑ j, |u i| * (c * D i j + d * (P i * Q j + P j * Q i)) * |u j|) ≤ _
  rw [he]
  have h1 := mul_le_mul_of_nonneg_left hdist' hc
  have h2 := mul_le_mul_of_nonneg_left (add_le_add hPQ hQP) hd
  change _ ≤ (c * T + 2 * d * Real.sqrt F * Real.sqrt G) * ∑ i, u i ^ 2
  nlinarith only [h1, h2]

end Riesz2.InitialDecay.Internal

namespace Riesz2.InitialDecay

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The squared row counterpart of the uniform column envelope. -/
theorem commutator_row_sq_le (g : ComponentGeometry ι) (i₀ : ι)
    {a s B : ℝ} (ha : 0 ≤ a) (has : a < s - 1 / 2) (hB : 0 ≤ B)
    (M : Matrix ι ι ℝ)
    (hM : ∀ i j, |M i j| ≤ B * (1 + componentDistance g i j) ^ (-s)) (i : ι) :
    ∑ j, ((distortionMatrix g i₀ a * M * distortionMatrix g i₀ (-a) - M) i j) ^ 2 ≤
      8 * B ^ 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(2 * (s - a))) := by
  calc _ ≤ ∑ j, 4 * B ^ 2 * (1 + componentDistance g i j) ^ (-(2 * (s - a))) := by
        apply Finset.sum_le_sum
        intro j _
        have h := commutator_entry_bound g i₀ ha hB M hM i j
        have hh := mul_self_le_mul_self (abs_nonneg _) h
        rw [← pow_two, sq_abs] at hh
        have hp : (1 + componentDistance g i j) ^ (a - s) *
            (1 + componentDistance g i j) ^ (a - s) =
            (1 + componentDistance g i j) ^ (-(2 * (s - a))) := by
          rw [← Real.rpow_add (by linarith [ComponentGeometryBounds.nonneg g i j])]
          congr 1
          ring
        nlinarith [hp]
    _ = 4 * B ^ 2 * ∑ j, (1 + componentDistance g i j) ^ (-(2 * (s - a))) :=
      (Finset.mul_sum ..).symm
    _ ≤ 4 * B ^ 2 * (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(2 * (s - a)))) := by
      apply mul_le_mul_of_nonneg_left (ComponentGeometryBounds.sum_power_le g i (by linarith))
      positivity
    _ = _ := by ring

omit [Fintype ι] [DecidableEq ι] in
/-- Lemma 4.3 of the paper:
the sharp commutator estimate with local loss `K^(1/2)`. The constant depends
only on `s`, `a`, and `ρ`, uniformly over all inherited interval/cycle geometries,
matrices and nonnegative entry bounds. Euclidean norms are finite square sums. -/
theorem commutator_estimate_sqrt_local (s a ρ : ℝ) (_hs : 1 < s)
    (ha : 1 / 2 < a) (has : a < s - 1 / 2) (hρ : 0 < ρ)
    (hρ1 : ρ < 1) (hρa : ρ < s - 1 / 2 - a) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ι : Type*) [Fintype ι] [DecidableEq ι] (g : ComponentGeometry ι) (i₀ : ι)
        (B : ℝ), 0 ≤ B → ∀ M : Matrix ι ι ℝ,
        (∀ i j, |M i j| ≤ B * (1 + componentDistance g i j) ^ (-s)) →
        ∀ K : ℝ, 1 ≤ K → ∀ u : ι → ℝ,
          |∑ i, ∑ j, u i *
              (distortionMatrix g i₀ a * M * distortionMatrix g i₀ (-a) - M) i j * u j| ≤
            C * B * K ^ (-ρ) * (∑ i, u i ^ 2) +
              C * B * K ^ (1 / 2 : ℝ) * Real.sqrt (∑ i, u i ^ 2) *
                Real.sqrt (∑ j ∈ Finset.univ.filter (fun j => componentDistance g j i₀ ≤ 2 * K),
                  u j ^ 2) := by
  have hρs : ρ < s - 1 := by linarith
  let p := a + ρ - s
  let q := -a
  let T := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(s - ρ))
  let F := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(-2 * p))
  let G := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(-2 * q))
  let J := ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(2 * (s - a)))
  let E := (|a| * 2 ^ |a - 1|) * T + 2 * 2 ^ s * Real.sqrt F * Real.sqrt G
  let Z := 2 * Real.sqrt (8 * J) * Real.sqrt 6
  have ht0 : 0 ≤ T := mul_nonneg (by norm_num) (tsum_nonneg fun k => by positivity)
  have hj0 : 0 ≤ J := tsum_nonneg fun k => by positivity
  have he0 : 0 ≤ E := by dsimp [E]; positivity
  have hz0 : 0 ≤ Z := by dsimp [Z]; positivity
  refine ⟨1 + E + Z, by linarith, ?_⟩
  intro ι _ _ g i₀ B hB M hM K hK u
  have hK0 : 0 < K := by linarith
  let A := distortionMatrix g i₀ a * M * distortionMatrix g i₀ (-a) - M
  let S := Finset.univ.filter (fun j => componentDistance g j i₀ ≤ 2 * K)
  let H := fun i j => (|a| * 2 ^ |a - 1|) * B * K ^ (-ρ) *
      (1 + componentDistance g i j) ^ (-(s - ρ)) +
    2 ^ s * B * K ^ (-ρ) *
      ((1 + componentDistance g i i₀) ^ p * (1 + componentDistance g j i₀) ^ q +
        (1 + componentDistance g j i₀) ^ p * (1 + componentDistance g i i₀) ^ q)
  have hH (i j : ι) : 0 ≤ H i j := by
    have hi := ComponentGeometryBounds.nonneg g i i₀
    have hj := ComponentGeometryBounds.nonneg g j i₀
    have hd := ComponentGeometryBounds.nonneg g i j
    dsimp [H]
    positivity
  have hA : ∀ i ∉ S, ∀ j ∉ S, |A i j| ≤ H i j := by
    intro i hi j hj
    have hi' : 2 * K < componentDistance g i i₀ := by simpa [S] using hi
    have hj' : 2 * K < componentDistance g j i₀ := by simpa [S] using hj
    exact exterior_commutator_entry_bound g i₀ (by linarith) (by linarith) hB hK0 hρ hρ1.le M hM i j
      (by linarith) (by linarith)
  have hquad : (∑ i, ∑ j, |u i| * H i j * |u j|) ≤
      (E * B * K ^ (-ρ)) * ∑ i, u i ^ 2 := by
    have hh := Internal.composite_kernel_quadratic_le g i₀
      (t := s - ρ) (p := p) (q := q)
      (c := (|a| * 2 ^ |a - 1|) * B * K ^ (-ρ)) (d := 2 ^ s * B * K ^ (-ρ))
      (by linarith) (by dsimp [p]; linarith) (by dsimp [q]; linarith)
      (by positivity) (by positivity) u
    convert hh using 1
    dsimp [E, T, F, G]
    ring
  have hc (j : ι) : ∑ i, A i j ^ 2 ≤ 8 * B ^ 2 * J :=
    commutator_column_sq_le g i₀ (by linarith) has hB M hM j
  have hr (i : ι) : ∑ j, A i j ^ 2 ≤ 8 * B ^ 2 * J :=
    commutator_row_sq_le g i₀ (by linarith) has hB M hM i
  have hh := Internal.local_exterior_quadratic_le A H hH S hA
    (E * B * K ^ (-ρ)) (8 * B ^ 2 * J) (by positivity) hc hr u hquad
  have hball : (S.card : ℝ) ≤ 6 * K := by
    have hb := ComponentGeometryBounds.card_ball_le g i₀ (R := 2 * K) (by linarith)
    have heq : S = Finset.univ.filter (fun j => componentDistance g i₀ j ≤ 2 * K) := by
      simp only [S, ComponentGeometryBounds.symm g]
    rw [← heq] at hb
    nlinarith
  have hsqrt : Real.sqrt (S.card : ℝ) ≤ Real.sqrt 6 * K ^ (1 / 2 : ℝ) := by
    apply (Real.sqrt_le_sqrt hball).trans_eq
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow K]
  have hL : Real.sqrt (8 * B ^ 2 * J) = B * Real.sqrt (8 * J) := by
    rw [show 8 * B ^ 2 * J = B ^ 2 * (8 * J) by ring,
      Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB]
  rw [hL] at hh
  have hloc : 2 * (B * Real.sqrt (8 * J)) * Real.sqrt (∑ i, u i ^ 2) *
      Real.sqrt (S.card : ℝ) * Real.sqrt (∑ j ∈ S, u j ^ 2) ≤
      Z * B * K ^ (1 / 2 : ℝ) * Real.sqrt (∑ i, u i ^ 2) * Real.sqrt (∑ j ∈ S, u j ^ 2) := by
    dsimp [Z]
    calc _ ≤ 2 * (B * Real.sqrt (8 * J)) * Real.sqrt (∑ i, u i ^ 2) *
          (Real.sqrt 6 * K ^ (1 / 2 : ℝ)) * Real.sqrt (∑ j ∈ S, u j ^ 2) := by gcongr
      _ = _ := by ring
  have hCE : E ≤ 1 + E + Z := by linarith
  have hCZ : Z ≤ 1 + E + Z := by linarith
  have hval : E * B * K ^ (-ρ) * (∑ i, u i ^ 2) ≤
      (1 + E + Z) * B * K ^ (-ρ) * (∑ i, u i ^ 2) := by gcongr
  have hlocal : Z * B * K ^ (1 / 2 : ℝ) * Real.sqrt (∑ i, u i ^ 2) *
      Real.sqrt (∑ j ∈ S, u j ^ 2) ≤
      (1 + E + Z) * B * K ^ (1 / 2 : ℝ) * Real.sqrt (∑ i, u i ^ 2) *
        Real.sqrt (∑ j ∈ S, u j ^ 2) := by gcongr
  exact (hh.trans (add_le_add le_rfl hloc)).trans (add_le_add hval hlocal)

omit [Fintype ι] [DecidableEq ι] in
/-- See Lemma 4.3 of the paper: commutation estimate, with constants
chosen before the component type, geometry, centre, coefficient bound, matrix,
cutoff and vector. The Euclidean squared norms are written as finite square sums.
The local norm is the square root of the square sum on `d(·,i₀) ≤ 2K`.
This compatibility form of Lemma 4.3 follows
from the sharp estimate with `q = 1/2`. -/
theorem commutation_estimate (s a ρ : ℝ) (hs : 1 < s)
    (ha : 1 / 2 < a) (has : a < s - 1 / 2) (hρ : 0 < ρ)
    (_hρs : ρ < s - 1) (hρ1 : ρ < 1) (hρa : ρ < s - 1 / 2 - a) :
    ∃ C q : ℝ, 0 < C ∧ 0 < q ∧
      ∀ (ι : Type*) [Fintype ι] [DecidableEq ι] (g : ComponentGeometry ι) (i₀ : ι)
        (B : ℝ), 0 ≤ B → ∀ M : Matrix ι ι ℝ,
        (∀ i j, |M i j| ≤ B * (1 + componentDistance g i j) ^ (-s)) →
        ∀ K : ℝ, 1 ≤ K → ∀ u : ι → ℝ,
          |∑ i, ∑ j, u i *
              (distortionMatrix g i₀ a * M * distortionMatrix g i₀ (-a) - M) i j * u j| ≤
            C * B * K ^ (-ρ) * (∑ i, u i ^ 2) +
              C * B * (1 + K) ^ q * Real.sqrt (∑ i, u i ^ 2) *
                Real.sqrt (∑ j ∈ Finset.univ.filter (fun j => componentDistance g j i₀ ≤ 2 * K),
                  u j ^ 2) := by
  obtain ⟨C, hC, hcomm⟩ := commutator_estimate_sqrt_local s a ρ hs ha has hρ hρ1 hρa
  refine ⟨C, 1 / 2, hC, by norm_num, ?_⟩
  intro ι _ _ g i₀ B hB M hM K hK u
  apply (hcomm ι g i₀ B hB M hM K hK u).trans
  gcongr
  linarith

end Riesz2.InitialDecay

namespace Riesz2.InitialDecay.Internal

open MeasureTheory Filter

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]
  {ν : Measure α}

/-- Constant component weights preserve the whole scalar form domain.
The identity is the diffusion commutation in Subsection 4.1, and is
valid for every scalar bilinear form, without a smoothness restriction. -/
theorem weighted_diffusion_identity (Q : ScalarFormData ν) (w : ι → ℝ) (u v : ι → Q.1) :
    (∑ i, Q.2 (w i • u i) (w i • v i)) =
      ∑ i, Q.2 (u i) ((w i * w i) • v i) := by
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- Matrix energy is finite on all weighted scalar-domain tuples whenever
the coefficient quadratic form is bounded and nonnegative. This justifies
the weighted tests of Lemma 4.4 on the whole form domain. -/
theorem weighted_test_mem_formDomain (Q : ScalarFormData ν)
    (M : α → Matrix ι ι ℝ) (hMmeas : ∀ i j, Measurable (fun x => M x i j))
    (b : ℝ)
    (hM : ∀ᵐ x ∂ν, ∀ z : ι → ℝ,
      0 ≤ (∑ i, ∑ j, z i * M x i j * z j) ∧
      (∑ i, ∑ j, z i * M x i j * z j) ≤ b * ∑ i, z i ^ 2)
    (w : ι → ℝ) (u : ι → Q.1) :
    WeightedFormDomain Q M ⊤ (fun i => w i • u i) :=
  (AbstractEnergy.bounded_formDomain_iff Q M hMmeas b hM ⊤ _).mpr
    (Eventually.of_forall fun _ => Submodule.mem_top)

/-- Testing the weak equation with squared constant component weights.
The matrix cross integral is finite by the equation itself. This is
the exact diffusion identity needed before applying commutation under the integral. -/
theorem weighted_weak_test (Q : ScalarFormData ν)
    (M : α → Matrix ι ι ℝ) (hMmeas : ∀ i j, Measurable (fun x => M x i j))
    (b : ℝ)
    (hM : ∀ᵐ x ∂ν, ∀ z : ι → ℝ,
      0 ≤ (∑ i, ∑ j, z i * M x i j * z j) ∧
      (∑ i, ∑ j, z i * M x i j * z j) ≤ b * ∑ i, z i ^ 2)
    (w : ι → ℝ) (f : ι → Lp ℝ 2 ν) (u : ι → Q.1)
    (hu : WeightedWeakSolution Q M ⊤ f u) :
    Integrable (matrixFieldPair M (fun i => (u i).val)
      (fun i => (((w i * w i) • u i) : Q.1).val)) ν ∧
    (∑ i, Q.2 (w i • u i) (w i • u i)) +
      (∫ x, matrixFieldPair M (fun i => (u i).val)
        (fun i => (((w i * w i) • u i) : Q.1).val) x ∂ν) =
          ∑ i, inner ℝ (f i) (((w i * w i) • u i) : Q.1).val := by
  have hh := hu.2 (fun i => (w i * w i) • u i)
    (weighted_test_mem_formDomain Q M hMmeas b hM (fun i => w i * w i) u)
  rw [← weighted_diffusion_identity Q w u u] at hh
  exact hh

/-- A point source is unchanged by the distortion, since its central weight
equals one. This checks the right side of Lemma 4.4. -/
theorem weighted_point_source_pair [DecidableEq ι] (Q : ScalarFormData ν) (g : ComponentGeometry ι)
    (i₀ : ι) (a : ℝ) (χ : Lp ℝ 2 ν) (u : ι → Q.1) :
    (∑ i, inner ℝ (if i = i₀ then χ else 0)
      (((distortionWeight g i₀ a i * distortionWeight g i₀ a i) • u i) : Q.1).val) =
      inner ℝ χ (u i₀).val := by
  rw [Finset.sum_eq_single i₀]
  · simp [distortionWeight_center]
  · intro i _ hi
    simp [hi]
  · simp

/-- Conjugating the matrix in the squared-weight test. The equality is a.e.,
so it respects the representatives of the L² classes. Symmetry is used
only to transpose the original weak pairing. -/
theorem weighted_matrixPair_identity [DecidableEq ι]
    (g : ComponentGeometry ι) (i₀ : ι) (a : ℝ)
    (M : α → Matrix ι ι ℝ) (hM : ∀ᵐ x ∂ν, ∀ i j, M x i j = M x j i)
    (u : ι → Lp ℝ 2 ν) :
    matrixFieldPair M u
        (fun i => (distortionWeight g i₀ a i * distortionWeight g i₀ a i) • u i) =ᵐ[ν]
      fun x => ∑ i, ∑ j,
        (distortionWeight g i₀ a i * u i x) *
          (distortionMatrix g i₀ a * M x * distortionMatrix g i₀ (-a)) i j *
            (distortionWeight g i₀ a j * u j x) := by
  have hae : ∀ᵐ x ∂ν, ∀ i,
      ((distortionWeight g i₀ a i * distortionWeight g i₀ a i) • u i) x =
        (distortionWeight g i₀ a i * distortionWeight g i₀ a i) * u i x := by
    apply ae_all_iff.mpr
    intro i
    simpa only [Filter.EventuallyEq, Pi.smul_apply, smul_eq_mul] using
      (Lp.coeFn_smul (distortionWeight g i₀ a i * distortionWeight g i₀ a i) (u i))
  filter_upwards [hM, hae] with x hx hw
  simp only [matrixFieldPair, hw, distortionMatrix, Matrix.diagonal_mul,
    Matrix.mul_diagonal, distortionWeight_neg]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hx j i]
  have hj : distortionWeight g i₀ a j ≠ 0 := (distortionWeight_pos g i₀ a j).ne'
  field_simp

/-- The exact point-source weak energy identity after distortion. This proves
the testing and domain part of Lemma 4.4. -/
theorem distorted_weak_energy_identity [DecidableEq ι]
    (Q : ScalarFormData ν) (g : ComponentGeometry ι) (i₀ : ι) (a : ℝ)
    (M : α → Matrix ι ι ℝ) (hMmeas : ∀ i j, Measurable (fun x => M x i j))
    (b : ℝ) (hsym : ∀ᵐ x ∂ν, ∀ i j, M x i j = M x j i)
    (hM : ∀ᵐ x ∂ν, ∀ z : ι → ℝ,
      0 ≤ (∑ i, ∑ j, z i * M x i j * z j) ∧
      (∑ i, ∑ j, z i * M x i j * z j) ≤ b * ∑ i, z i ^ 2)
    (χ : Lp ℝ 2 ν) (u : ι → Q.1)
    (hu : WeightedWeakSolution Q M ⊤ (fun i => if i = i₀ then χ else 0) u) :
    let F := fun x => ∑ i, ∑ j,
      (distortionWeight g i₀ a i * (u i).val x) *
        (distortionMatrix g i₀ a * M x * distortionMatrix g i₀ (-a)) i j *
          (distortionWeight g i₀ a j * (u j).val x)
    Integrable F ν ∧
      (∑ i, Q.2 (distortionWeight g i₀ a i • u i) (distortionWeight g i₀ a i • u i)) +
        (∫ x, F x ∂ν) = inner ℝ χ (u i₀).val := by
  have hh := weighted_weak_test Q M hMmeas b hM (distortionWeight g i₀ a)
    (fun i => if i = i₀ then χ else 0) u hu
  have he := weighted_matrixPair_identity g i₀ a M hsym (fun i => (u i).val)
  have he' : matrixFieldPair M (fun i => (u i).val)
      (fun i => (((distortionWeight g i₀ a i * distortionWeight g i₀ a i) • u i) : Q.1).val) =ᵐ[ν]
      fun x => ∑ i, ∑ j,
        (distortionWeight g i₀ a i * (u i).val x) *
          (distortionMatrix g i₀ a * M x * distortionMatrix g i₀ (-a)) i j *
            (distortionWeight g i₀ a j * (u j).val x) := he
  refine ⟨hh.1.congr he', ?_⟩
  rw [← integral_congr_ae he', hh.2]
  exact weighted_point_source_pair Q g i₀ a χ u

end Riesz2.InitialDecay.Internal
