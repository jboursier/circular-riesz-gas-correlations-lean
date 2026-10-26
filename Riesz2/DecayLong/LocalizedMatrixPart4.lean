/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.LocalizedMatrixPart3

/-!
# Uniform matrix bounds at the localized scale

Assembly of the matrix clauses of the proof of Proposition 5.15.
The scalar probability space is unchanged throughout.
-/

public section
noncomputable section

open MeasureTheory Finset Riesz2.IntervalBoundary
open scoped BigOperators Classical Fin.NatCast MatrixOrder

namespace Riesz2.LocalizedMatrix

/-- See the proof of Proposition 5.15 in the paper: the logarithmic local
parameter gives exactly the original loss at every real exponent. -/
theorem local_loss_identity {n n₀ : ℝ} (hn : 0 < n) (hn₀ : 1 < n₀)
    (ε a : ℝ) :
    n₀ ^ (a * (ε * Real.log n / Real.log n₀)) = n ^ (a * ε) := by
  rw [Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos hn]
  congr 1
  field_simp [(Real.log_pos hn₀).ne']

/-- See the proof of Proposition 5.15 in the paper: the local small parameter
is positive on its entire used carrier. -/
theorem local_parameter_pos {n n₀ ε : ℝ} (hn : 1 < n) (hn₀ : 1 < n₀)
    (hε : 0 < ε) : 0 < ε * Real.log n / Real.log n₀ :=
  div_pos (mul_pos hε (Real.log_pos hn)) (Real.log_pos hn₀)

/-- See the proof of Proposition 5.15 in the paper: the floor cutoff is
literally unchanged at the logarithmic local parameter, for every integer power. -/
theorem local_cutoff_identity {n n₀ : ℝ} (hn : 0 < n) (hn₀ : 1 < n₀)
    (ε : ℝ) (M₀ : ℕ) :
    ⌊n₀ ^ (ε * Real.log n / Real.log n₀)⌋₊ ^ M₀ = ⌊n ^ ε⌋₊ ^ M₀ := by
  have hh := local_loss_identity hn hn₀ ε 1
  simp only [one_mul] at hh
  rw [hh]

/-- See the proof of Proposition 5.15 in the paper: an eighth-power separation
makes the rounded lower cutoff fit every actual local period, including the
smallest window. -/
theorem window_cutoff_admissible (s : Riesz1.RieszExponent) (m : ℕ+)
    (j i₀ : Fin (m : ℕ)) (hR : 16 ≤ Riesz1.cyclicIndexDistance m j i₀)
    {t : ℝ} (ht : 1 ≤ t)
    (hsep : t ^ (8 : ℕ) ≤ (Riesz1.cyclicIndexDistance m j i₀ : ℝ)) :
    1 ≤ ⌈t⌉₊ ∧ ⌈t⌉₊ ≤ (windowPeriod s m j i₀ : ℕ) / 4 := by
  have hsize := window_size_bounds m j i₀ hR
  have hstrict := two_windowSize_lt_period s m j i₀ hR
  have hceilpos : 1 ≤ ⌈t⌉₊ := by
    exact_mod_cast (show (1 : ℝ) ≤ (⌈t⌉₊ : ℝ) from ht.trans (Nat.le_ceil t))
  refine ⟨hceilpos, ?_⟩
  by_cases ht2 : t ≤ 2
  · have hc : ⌈t⌉₊ ≤ 2 := Nat.ceil_le.mpr ht2
    omega
  · have ht2 : 2 < t := lt_of_not_ge ht2
    have hsq : 4 < t ^ 2 := by nlinarith
    have hfour : 16 < t ^ 4 := by nlinarith [sq_nonneg (t ^ 2 - 4)]
    have hlarge : 16 * (t + 1) ≤ t ^ 8 := by
      have hf : t + 1 ≤ t ^ 4 := by nlinarith [sq_nonneg (t ^ 2 - 1)]
      nlinarith [sq_nonneg (t ^ 4 - 16)]
    have hc := Nat.ceil_lt_add_one (by linarith : 0 ≤ t)
    have hmreal : 4 * (⌈t⌉₊ : ℝ) < (windowPeriod s m j i₀ : ℝ) := by
      have hs : (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ≤
          8 * (windowSize m j i₀ : ℝ) := by linarith [hsize.2.1]
      have hm : 2 * (windowSize m j i₀ : ℝ) < (windowPeriod s m j i₀ : ℝ) := by
        exact_mod_cast hstrict
      linarith
    have hc' : 4 * ⌈t⌉₊ < (windowPeriod s m j i₀ : ℕ) := by exact_mod_cast hmreal
    omega

/-- See the proof of Proposition 5.15 in the paper: replacement coefficients
are measurable over the original scalar space. -/
theorem localizedWeight_measurable {Ω : Type*} [MeasurableSpace Ω]
    (s : Riesz1.RieszExponent) (m m₀ : ℕ+) (hm₀ : 2 ≤ (m₀ : ℕ))
    (hle : (m₀ : ℕ) ≤ (m : ℕ)) (n K : ℕ)
    (A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → Ω → ℝ)
    (hA : ∀ t, Measurable (A t)) (t) :
    Measurable (fun x => localizedWeight s m m₀ hm₀ hle n K (fun u => A u x) t) := by
  unfold localizedWeight
  split_ifs
  · exact hA _
  · exact measurable_const

/-- See the proof of Proposition 5.15 in the paper: the full interval matrix
has exactly the cyclic-sum quadratic representation. -/
theorem intervalMatrix_quadratic (m : ℕ+)
    (A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → ℝ) (z : Fin (m : ℕ) → ℝ) :
    (∑ i, ∑ l, z i * intervalMatrix m m le_rfl A i l * z l) =
      ∑ i, ∑ r, A (i, r) * (cyclicGapSum m i (r.val + 1) z) ^ 2 := by
  have hfull : internalMatrix m m le_rfl A = intervalMatrix m m le_rfl A := by
    ext i l
    simp only [internalMatrix, intervalMatrix]
    apply sum_congr rfl
    intro t _
    rw [ite_eq_left (show IsInternal m m t from fun j _ => j.isLt)]
  rw [← hfull, internalMatrix_quadratic]
  simp only [show ∀ t, IsInternal m m t from fun _ j _ => j.isLt, ite_true,
    Fintype.sum_prod_type]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro r _
  congr 2
  rw [← sum_cyclicIndexInterval_eq_cyclicGapSum m i (by have := r.isLt; omega)]
  congr 1
  ext l
  simp [trace]

/-- See the proof of Proposition 5.15 in the paper: retaining a quarter-block
is determined by the parent matrix, even when its interval witness is not unique.
This allows the entry estimate and the coefficient bounds to use the
same matrix without choosing a second encoding. -/
theorem internalMatrix_eq_of_intervalMatrix_eq_internal (m : ℕ+) (n : ℕ+)
    (hn : 4 * (n : ℕ) ≤ (m : ℕ))
    (A B : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → ℝ)
    (h : intervalMatrix m m le_rfl A = intervalMatrix m m le_rfl B) :
    internalMatrix m n (by omega) A = internalMatrix m n (by omega) B := by
  ext i l
  have hord (i l : Fin (n : ℕ)) (hil : i.val ≤ l.val) :
      internalMatrix m n (by omega) A i l = internalMatrix m n (by omega) B i l := by
    rw [internalMatrix_inclusion_exclusion m (by have := n.pos; omega) A i l hil,
      internalMatrix_inclusion_exclusion m (by have := n.pos; omega) B i l hil, h]
  by_cases hil : i.val ≤ l.val
  · exact hord i l hil
  · rw [internalMatrix_symm m n (by omega) A i l, internalMatrix_symm m n (by omega) B i l]
    exact hord l i (by omega)

/-- See the proof of Proposition 5.15 in the paper: the localized matrix is
independent of the chosen parent interval representation. -/
theorem matrix_eq_of_intervalMatrix_eq_internal {Ω : Type*}
    (s : Riesz1.RieszExponent) (m m₀ n₀ : ℕ+)
    (hm₀ : 2 ≤ (m₀ : ℕ)) (hn : (n₀ : ℕ) ≤ (m : ℕ))
    (hn₀ : (n₀ : ℕ) ≤ (m₀ : ℕ)) (hq : 4 * (n₀ : ℕ) ≤ (m : ℕ)) (K : ℕ)
    (A B : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → Ω → ℝ) (x : Ω)
    (h : intervalMatrix m m le_rfl (fun t => A t x) =
      intervalMatrix m m le_rfl (fun t => B t x)) (b : Fin (m : ℕ)) :
    matrix s m m₀ n₀ hm₀ hn hn₀ K (fun t => A (t.1 + b, t.2)) x =
      matrix s m m₀ n₀ hm₀ hn hn₀ K (fun t => B (t.1 + b, t.2)) x := by
  have hr : intervalMatrix m m le_rfl (fun t => A (t.1 + b, t.2) x) =
      intervalMatrix m m le_rfl (fun t => B (t.1 + b, t.2) x) := by
    ext i l
    rw [intervalMatrix_translate m (fun t => A t x),
      intervalMatrix_translate m (fun t => B t x), h]
  have hi := internalMatrix_eq_of_intervalMatrix_eq_internal m n₀ hq _ _ hr
  ext i l
  simp only [matrix]
  split_ifs <;> first | rw [hi] | rfl

/-- See the proof of Proposition 5.15 in the paper: all cutoff and coercivity
losses are fixed powers of the common loss variable. -/
theorem coercivity_loss_internal {s κ L C B c₀ h k : ℝ}
    (hκ : 0 ≤ κ) (_hL : 0 ≤ L) (hs : 0 < 1 + s)
    (hC : 0 < C) (hB : 0 < B) (hc₀ : 0 < c₀) (hh : 1 ≤ h)
    (hk : 0 < k) (hku : k ≤ 2 * h ^ L) :
    (c₀ * min 1 (C⁻¹ / B) * (2 : ℝ) ^ (-1 - s)) * h ^ (-(κ + L * (1 + s))) ≤
      c₀ * min 1 (C⁻¹ * h ^ (-κ) / B) * k ^ (-1 - s) := by
  have hh0 : 0 < h := by linarith
  have hu : h ^ (-κ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hh (by linarith)
  have hq0 : 0 ≤ min 1 (C⁻¹ / B) := le_min (by norm_num) (by positivity)
  have hq : min 1 (C⁻¹ / B) * h ^ (-κ) ≤ min 1 (C⁻¹ * h ^ (-κ) / B) := by
    apply le_min
    · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans
        (by simpa using hu)
    · calc
        _ ≤ (C⁻¹ / B) * h ^ (-κ) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
        _ = _ := by ring
  have hp : (2 * h ^ L) ^ (-1 - s) ≤ k ^ (-1 - s) :=
    Real.rpow_le_rpow_of_nonpos hk hku (by linarith)
  have heq : (c₀ * min 1 (C⁻¹ / B) * (2 : ℝ) ^ (-1 - s)) *
      h ^ (-(κ + L * (1 + s))) =
      c₀ * (min 1 (C⁻¹ / B) * h ^ (-κ)) * (2 * h ^ L) ^ (-1 - s) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hh0.le,
      show L * (-1 - s) = -(L * (1 + s)) by ring,
      show -(κ + L * (1 + s)) = -κ + -(L * (1 + s)) by ring,
      Real.rpow_add hh0]
    ring
  rw [heq]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hq hc₀.le) hp
    (by positivity) (mul_nonneg hc₀.le (le_min (by norm_num) (by positivity)))

/-- See the proof of Proposition 5.15 in the paper: assemble the predicate from the replacement family. This internal interface records the
coefficient, entry and order data separately for use by the uniform theorem. -/
theorem periodizedMatrixBounds_of_local_data_internal
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (s : Riesz1.RieszExponent) (m m₀ n₀ : ℕ+)
    (hm₀ : 2 ≤ (m₀ : ℕ)) (hle : (m₀ : ℕ) ≤ (m : ℕ))
    (hn₀ : 2 * (n₀ : ℕ) < (m₀ : ℕ)) (K : ℕ) (C κ γ ε : ℝ)
    (A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → Ω → ℝ)
    (hA : ∀ t, Measurable (A t))
    (hdata : ∀ᵐ x ∂ν,
      (∀ t, let w := localizedWeight s m m₀ hm₀ hle n₀ K (fun u => A u x) t
        0 ≤ w ∧ w ≤ C * (n₀ : ℝ) ^ (κ * ε) * (t.2.val + 1 : ℝ) ^ (-s.val - 2) ∧
        ((n₀ : ℝ) ^ (γ * ε) ≤ (t.2.val + 1 : ℝ) →
          C⁻¹ * (n₀ : ℝ) ^ (-κ * ε) * (t.2.val + 1 : ℝ) ^ (-s.val - 2) ≤ w)) ∧
      (C⁻¹ * (n₀ : ℝ) ^ (-κ * ε)) •
          (1 : Matrix (Fin (m₀ : ℕ)) (Fin (m₀ : ℕ)) ℝ) ≤
        matrix s m m₀ n₀ hm₀ (by omega) (by omega) K A x ∧
      (∀ i l : Fin (n₀ : ℕ), i.val ≤ l.val →
        |matrix s m m₀ n₀ hm₀ (by omega) (by omega) K A x
            (i.castLE (by omega)) (l.castLE (by omega)) -
          ((2 : ℝ) • referenceIntervalMatrix s m₀ hm₀ K)
            (i.castLE (by omega)) (l.castLE (by omega))| ≤
          C * (n₀ : ℝ) ^ (κ * ε) *
            (1 + ((l.val - i.val : ℕ) : ℝ)) ^ (-1 - s.val / 2))) :
    PeriodizedMatrixBounds (ν := ν) s n₀ m₀ hm₀ K C κ γ ε
      (matrix s m m₀ n₀ hm₀ (by omega) (by omega) K A) := by
  let W := fun t x => localizedWeight s m m₀ hm₀ hle n₀ K (fun u => A u x) t
  have hW (t) : Measurable (W t) := localizedWeight_measurable s m m₀ hm₀ hle n₀ K A hA t
  have heq (x : Ω) : intervalMatrix m₀ m₀ le_rfl (fun t => W t x) =
      matrix s m m₀ n₀ hm₀ (by omega) (by omega) K A x :=
    localizedWeight_matrix s m m₀ n₀ hm₀ hle hn₀ K A x
  have hsym (x : Ω) (i l) :
      matrix s m m₀ n₀ hm₀ (by omega) (by omega) K A x i l =
        matrix s m m₀ n₀ hm₀ (by omega) (by omega) K A x l i := by
    rw [← heq]
    exact intervalMatrix_symm m₀ m₀ le_rfl _ i l
  refine ⟨?_, ?_, ?_⟩
  · intro i l
    simp_rw [← heq]
    unfold intervalMatrix
    exact Finset.measurable_sum _ (fun t _ => (hW t).mul_const _)
  · filter_upwards [hdata] with x hx
    refine ⟨hsym x, matrix_exterior s m m₀ n₀ hm₀ (by omega) (by omega) K A x, ?_, ?_⟩
    · have hh : (matrix s m m₀ n₀ hm₀ (by omega) (by omega) K A x).IsHermitian := by
        rw [Matrix.IsHermitian]
        ext i l
        simpa only [Matrix.conjTranspose_apply, star_trivial] using hsym x l i
      have hc := (FiniteMatrixOrder.smul_one_le_iff hh _).mp hx.2.1
      intro z
      simpa only [dotProduct, Matrix.mulVec, mul_sum, mul_assoc, sq] using hc z
    · intro i l hi hl
      let i' : Fin (n₀ : ℕ) := ⟨i.val, hi⟩
      let l' : Fin (n₀ : ℕ) := ⟨l.val, hl⟩
      have hi' : i'.castLE (by omega : (n₀ : ℕ) ≤ (m₀ : ℕ)) = i := Fin.ext rfl
      have hl' : l'.castLE (by omega : (n₀ : ℕ) ≤ (m₀ : ℕ)) = l := Fin.ext rfl
      have hdist : Riesz1.cyclicIndexDistance m₀ i l = Nat.dist i.val l.val := by
        simp only [Riesz1.cyclicIndexDistance]
        have hd : 2 * Nat.dist i.val l.val ≤ (m₀ : ℕ) := by
          unfold Nat.dist
          omega
        omega
      by_cases hil : i.val ≤ l.val
      · have hh := hx.2.2 i' l' hil
        simpa only [hi', hl', hdist, Nat.dist_eq_sub_of_le hil] using hh
      · have hil : l.val ≤ i.val := by omega
        have hh := hx.2.2 l' i' hil
        have hsref : ((2 : ℝ) • referenceIntervalMatrix s m₀ hm₀ K) l i =
            ((2 : ℝ) • referenceIntervalMatrix s m₀ hm₀ K) i l := by
          rw [← intervalMatrix_referenceWeight]
          exact intervalMatrix_symm m₀ m₀ le_rfl _ l i
        simpa only [hi', hl', hsym x l i, hsref, hdist,
          Nat.dist_comm i.val l.val, Nat.dist_eq_sub_of_le hil] using hh
  · refine ⟨fun i r => W (i, r), fun i r => hW (i, r), ?_⟩
    filter_upwards [hdata] with x hx
    refine ⟨?_, ?_⟩
    · intro i r
      simpa only [Nat.cast_add, Nat.cast_one] using hx.1 (i, r)
    · intro z
      rw [← heq]
      exact intervalMatrix_quadratic m₀ (fun t => W t x) z

/-- See the proof of Proposition 5.15 in the paper: the internal-entry
and different-period estimates apply to each given coefficient witness, with
one prefactor chosen before any scalar space or measure. -/
theorem window_entry_comparison_internal (s : Riesz1.RieszExponent) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ (m : ℕ+) (hm : 2 ≤ (m : ℕ)) (K : ℕ)
      (A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → ℝ) (P : ℝ), 0 ≤ P →
      (∀ i l, |intervalMatrix m m le_rfl A i l -
          ((2 : ℝ) • referenceIntervalMatrix s m hm K) i l| ≤
        P * (1 + (Riesz1.cyclicIndexDistance m i l : ℝ)) ^ (-1 - s.val / 2)) →
      ∀ (j i₀ : Fin (m : ℕ)) (hR : 16 ≤ Riesz1.cyclicIndexDistance m j i₀),
      let n₀ := windowSize m j i₀
      let m₀ := windowPeriod s m j i₀
      let hm₀ : 2 ≤ (m₀ : ℕ) := by
        have := two_windowSize_lt_period s m j i₀ hR
        have := (windowSize m j i₀).pos
        change 2 ≤ (windowPeriod s m j i₀ : ℕ)
        omega
      let hn : (n₀ : ℕ) ≤ (m : ℕ) := by
        change (windowSize m j i₀ : ℕ) ≤ (m : ℕ)
        have := (window_size_bounds m j i₀ hR).2.2.2
        omega
      let hn₀ : (n₀ : ℕ) ≤ (m₀ : ℕ) := by
        change (windowSize m j i₀ : ℕ) ≤ (windowPeriod s m j i₀ : ℕ)
        have := two_windowSize_lt_period s m j i₀ hR
        omega
      let b := j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ))
      ∀ i l : Fin (n₀ : ℕ), i.val ≤ l.val →
      |matrix s m m₀ n₀ hm₀ hn hn₀ K (fun t (_ : Unit) => A (t.1 + b, t.2)) ()
          (i.castLE hn₀) (l.castLE hn₀) -
        ((2 : ℝ) • referenceIntervalMatrix s m₀ hm₀ K) (i.castLE hn₀) (l.castLE hn₀)| ≤
        (4 * P + Cp) * (1 + ((l.val - i.val : ℕ) : ℝ)) ^ (-1 - s.val / 2) := by
  obtain ⟨Cp, hCp, hp⟩ := referenceInternal_different_period s
  refine ⟨Cp, hCp, fun m hm K A P hP hE j i₀ hR => ?_⟩
  dsimp only
  intro i l hil
  let n₀ := windowSize m j i₀
  let m₀ := windowPeriod s m j i₀
  let b := j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ))
  have hquarter : 4 * (n₀ : ℕ) ≤ (m : ℕ) := (window_size_bounds m j i₀ hR).2.2.2
  have hstrict : 2 * (n₀ : ℕ) < (m₀ : ℕ) := two_windowSize_lt_period s m j i₀ hR
  have hle : (m₀ : ℕ) ≤ (m : ℕ) := windowPeriod_le_parent s m j i₀
  have hm₀ : 2 ≤ (m₀ : ℕ) := by have := n₀.pos; omega
  let B := A - BoundaryEntries.referenceWeight s m hm K
  have hB (p w : Fin (m : ℕ)) :
      |intervalMatrix m m le_rfl (fun t => B (t.1 + b, t.2)) p w| ≤
        P * (1 + (Riesz1.cyclicIndexDistance m p w : ℝ)) ^ (-(1 + s.val / 2)) := by
    rw [intervalMatrix_translate]
    rw [show intervalMatrix m m le_rfl B =
        intervalMatrix m m le_rfl A - (2 : ℝ) • referenceIntervalMatrix s m hm K by
      rw [show B = A - BoundaryEntries.referenceWeight s m hm K from rfl,
        intervalMatrix_sub, intervalMatrix_referenceWeight], Matrix.sub_apply]
    simpa only [distance_add, show -(1 + s.val / 2) = -1 - s.val / 2 by ring]
      using hE (p + b) (w + b)
  have hparent := internalMatrix_entry_bound_internal m hquarter
    (fun t => B (t.1 + b, t.2)) P (1 + s.val / 2) hP
    (by linarith [s.property.1]) hB i l hil
  have hcoef : (fun t => B (t.1 + b, t.2)) =
      (fun t => A (t.1 + b, t.2)) - BoundaryEntries.referenceWeight s m hm K := rfl
  rw [hcoef, internalMatrix_sub, internalMatrix_referenceWeight, Matrix.sub_apply] at hparent
  have hdiff : |BoundaryEntries.referenceInternal s m hm K n₀ (by omega) i l -
      BoundaryEntries.referenceInternal s m₀ hm₀ K n₀ (by omega) i l| ≤
      Cp * (1 + ((l.val - i.val : ℕ) : ℝ)) ^ (-1 - s.val / 2) := by
    by_cases hc : (m₀ : ℕ) = (m : ℕ)
    · have heq : m₀ = m := Subtype.ext hc
      simp only [heq, sub_self, abs_zero]
      positivity
    · have hcap : (m₀ : ℕ) < (m : ℕ) := by omega
      have hscale := power_le_windowPeriod_of_lt s m j i₀ hcap
      have h₁ := hp m m₀ n₀ hm hm₀ hle hstrict K i l
      have h₂ := mul_le_mul_of_nonneg_left
        (period_error_absorption s n₀ m₀ hscale (d := l.val - i.val)
          (by
            have hl : l.val < (n₀ : ℕ) := l.isLt
            omega)) hCp.le
      exact h₁.trans (by simpa only [mul_assoc] using h₂)
  rw [matrix_reference_error]
  have htri := abs_sub_le
    (internalMatrix m n₀ (by omega) (fun t => A (t.1 + b, t.2)) i l)
    (BoundaryEntries.referenceInternal s m hm K n₀ (by omega) i l)
    (BoundaryEntries.referenceInternal s m₀ hm₀ K n₀ (by omega) i l)
  rw [show -(1 + s.val / 2) = -1 - s.val / 2 by ring] at hparent
  linarith only [htri, hparent, hdiff]

/-- See the proof of Proposition 5.15 in the paper, matrix clauses: uniform
assembly of `PeriodizedMatrixBounds` at the actual window
size and capped period. The exponents and separation power precede the parent
prefactor and small parameter. The new prefactor precedes all sizes and windows.
The cutoff is unchanged and the scalar measure is the original measure. -/
theorem localized_periodizedMatrixBounds (s : Riesz1.RieszExponent) (κ γ : ℝ) (M₀ : ℕ+)
    (hκ : 0 < κ) (hγ : 0 < γ) :
    ∃ κloc γloc D : ℝ, 0 < κloc ∧ 0 < γloc ∧ 0 < D ∧
    ∀ C : ℝ, 1 ≤ C → ∃ Cloc : ℝ, 1 ≤ Cloc ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω),
    ∀ ε : ℝ, 0 < ε → ∀ (n m : ℕ+) (_hn : 2 ≤ (n : ℕ)) (hm : 2 ≤ (m : ℕ)),
    let K := ⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ)
    ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M →
    ∃ A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → Ω → ℝ,
      (∀ t, Measurable (A t)) ∧
      (∀ᵐ x ∂ν, (∀ t, 0 ≤ A t x) ∧ intervalMatrix m m le_rfl (fun t => A t x) = M x) ∧
      ∀ (j i₀ : Fin (m : ℕ)) (hR : 16 ≤ Riesz1.cyclicIndexDistance m j i₀),
      (n : ℝ) ^ (D * ε) ≤ (Riesz1.cyclicIndexDistance m j i₀ : ℝ) →
      let n₀ := windowSize m j i₀
      let m₀ := windowPeriod s m j i₀
      let hm₀ : 2 ≤ (m₀ : ℕ) := by
        have := two_windowSize_lt_period s m j i₀ hR
        have := (windowSize m j i₀).pos
        change 2 ≤ (windowPeriod s m j i₀ : ℕ)
        omega
      let b := j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ))
      let ε₀ := ε * Real.log (n : ℝ) / Real.log (n₀ : ℝ)
      PeriodizedMatrixBounds (ν := ν) s n₀ m₀ hm₀ K Cloc κloc γloc ε₀
        (matrix s m m₀ n₀ hm₀
          (by
            change (windowSize m j i₀ : ℕ) ≤ (m : ℕ)
            have := (window_size_bounds m j i₀ hR).2.2.2
            omega)
          (by
            change (windowSize m j i₀ : ℕ) ≤ (windowPeriod s m j i₀ : ℕ)
            have := two_windowSize_lt_period s m j i₀ hR
            omega)
          K (fun t => A (t.1 + b, t.2))) := by
  let L : ℝ := (M₀ : ℕ) + γ + 1
  let kl : ℝ := κ + L * (1 + s.val)
  have hL : 0 < L := by dsimp [L]; positivity
  have hLM : (M₀ : ℕ) ≤ L := by dsimp [L]; linarith
  have hLγ : γ ≤ L := by dsimp [L]; linarith [show (0 : ℝ) ≤ (M₀ : ℕ) by positivity]
  have hkl : κ ≤ kl := by dsimp [kl]; nlinarith [s.property.1]
  obtain ⟨B, c₀, hB, hc₀, hcoer⟩ := localized_coercivity_internal s
  obtain ⟨Bu, hBu, hupper⟩ := localizedWeight_upper_internal s
  obtain ⟨cr, hcr, hlower⟩ := referenceWeight_lower s
  obtain ⟨Cp, hCp, hentry⟩ := window_entry_comparison_internal s
  refine ⟨kl, L, 8 * L, lt_of_lt_of_le hκ hkl, hL, by positivity, ?_⟩
  intro C hC
  have hCpos : 0 < C := by linarith
  let d : ℝ := c₀ * min 1 (C⁻¹ / B) * (2 : ℝ) ^ (-1 - s.val)
  have hd : 0 < d := by dsimp [d]; positivity
  let Cl : ℝ := 1 + (C + Bu) + (4 * C + Cp) + C + cr⁻¹ + d⁻¹
  have hCl : 1 ≤ Cl := by dsimp [Cl]; linarith [inv_pos.mpr hcr, inv_pos.mpr hd]
  have hClpos : 0 < Cl := by linarith
  have hClu : C + Bu ≤ Cl := by dsimp [Cl]; linarith [inv_pos.mpr hcr, inv_pos.mpr hd]
  have hCle : 4 * C + Cp ≤ Cl := by dsimp [Cl]; linarith [inv_pos.mpr hcr, inv_pos.mpr hd]
  have hClC : C ≤ Cl := by dsimp [Cl]; linarith [inv_pos.mpr hcr, inv_pos.mpr hd]
  have hClcr : cr⁻¹ ≤ Cl := by dsimp [Cl]; linarith [inv_pos.mpr hcr, inv_pos.mpr hd]
  have hCld : d⁻¹ ≤ Cl := by dsimp [Cl]; linarith [inv_pos.mpr hcr, inv_pos.mpr hd]
  have hinvC : Cl⁻¹ ≤ C⁻¹ := (inv_le_inv₀ hClpos hCpos).mpr hClC
  have hinvcr : Cl⁻¹ ≤ cr := by
    simpa only [inv_inv] using (inv_le_inv₀ hClpos (inv_pos.mpr hcr)).mpr hClcr
  have hinvd : Cl⁻¹ ≤ d := by
    simpa only [inv_inv] using (inv_le_inv₀ hClpos (inv_pos.mpr hd)).mpr hCld
  refine ⟨Cl, hCl, ?_⟩
  intro Ω inst ν ε hε n m hn hm K M hM
  obtain ⟨a, ha, hrep⟩ := periodizedMatrixBounds_entry_representation s n m hm K C κ γ ε M hM
  let A := fun t : Fin (m : ℕ) × Fin ((m : ℕ) / 2) => a t.1 t.2
  have hA (t) : Measurable (A t) := ha t.1 t.2
  have hrep' : ∀ᵐ x ∂ν, (∀ t, 0 ≤ A t x) ∧
      intervalMatrix m m le_rfl (fun t => A t x) = M x := by
    filter_upwards [hrep] with x hx
    refine ⟨fun t => (hx.1 t.1 t.2).1, ?_⟩
    ext i l
    rw [intervalMatrix_entries]
    exact (hx.2 i l).symm
  refine ⟨A, hA, hrep', ?_⟩
  intro j i₀ hR hsep
  dsimp only
  let n₀ := windowSize m j i₀
  let m₀ := windowPeriod s m j i₀
  have hsize := window_size_bounds m j i₀ hR
  have hstrict : 2 * (n₀ : ℕ) < (m₀ : ℕ) := two_windowSize_lt_period s m j i₀ hR
  have hle : (m₀ : ℕ) ≤ (m : ℕ) := windowPeriod_le_parent s m j i₀
  have hm₀ : 2 ≤ (m₀ : ℕ) := by have := n₀.pos; omega
  have hquarter : 4 * (n₀ : ℕ) ≤ (m : ℕ) := hsize.2.2.2
  let b := j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ))
  let ε₀ := ε * Real.log (n : ℝ) / Real.log (n₀ : ℝ)
  let h : ℝ := (n : ℝ) ^ ε
  have hnpos : (0 : ℝ) < n := by positivity
  have hh : 1 ≤ h := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ (n : ℕ))) hε.le
  have hhpos : 0 < h := by linarith
  have hn₀nat : 1 < (n₀ : ℕ) := by change 1 < (windowSize m j i₀ : ℕ); omega
  have hn₀ : (1 : ℝ) < n₀ := by exact_mod_cast hn₀nat
  have hloss (q : ℝ) : (n₀ : ℝ) ^ (q * ε₀) = h ^ q := by
    rw [local_loss_identity hnpos hn₀, ← Real.rpow_mul hnpos.le]
    congr 1
    ring
  have hparent (q : ℝ) : (n : ℝ) ^ (q * ε) = h ^ q := by
    rw [← Real.rpow_mul hnpos.le]
    congr 1
    ring
  have hK : (K : ℝ) ≤ h ^ L := by
    have hhK := GlobalReferenceErrorInternal.cutoff_power_le n ε 1 (by norm_num) M₀
    rw [Real.rpow_one] at hhK
    have hKM : (K : ℝ) ≤ h ^ ((M₀ : ℕ) : ℝ) := by
      simpa only [hparent, mul_one] using hhK
    exact hKM.trans (Real.rpow_le_rpow_of_exponent_le hh hLM)
  have hγ : (n : ℝ) ^ (γ * ε) ≤ h ^ L := by
    rw [hparent]
    exact Real.rpow_le_rpow_of_exponent_le hh hLγ
  let Ks := max K ⌈(n : ℝ) ^ (γ * ε)⌉₊
  have hKs : Ks ≤ ⌈h ^ L⌉₊ := by
    apply max_le
    · exact_mod_cast hK.trans (Nat.le_ceil _)
    · exact Nat.ceil_mono hγ
  have hsep' : (h ^ L) ^ (8 : ℕ) ≤ (Riesz1.cyclicIndexDistance m j i₀ : ℝ) := by
    rw [← Real.rpow_mul_natCast hhpos.le, ← Real.rpow_mul hnpos.le]
    convert hsep using 1
    congr 1
    ring
  have hcut := window_cutoff_admissible s m j i₀ hR
    (Real.one_le_rpow hh hL.le) hsep'
  have hKsone : 1 ≤ Ks := by
    have hpowone : 1 ≤ (n : ℝ) ^ (γ * ε) := by rw [hparent]; exact Real.one_le_rpow hh (by linarith)
    have hc := Nat.le_ceil ((n : ℝ) ^ (γ * ε))
    have : 1 ≤ ⌈(n : ℝ) ^ (γ * ε)⌉₊ := by exact_mod_cast hpowone.trans hc
    exact this.trans (le_max_right _ _)
  have hKsupper : (Ks : ℝ) ≤ 2 * h ^ L := by
    have hct := Nat.ceil_lt_add_one (show 0 ≤ h ^ L by positivity)
    have hcast : (Ks : ℝ) ≤ (⌈h ^ L⌉₊ : ℝ) := by exact_mod_cast hKs
    have ho : 1 ≤ h ^ L := Real.one_le_rpow hh hL.le
    linarith
  have hu : h ^ κ ≤ h ^ kl := Real.rpow_le_rpow_of_exponent_le hh hkl
  have ho : 1 ≤ h ^ kl := Real.one_le_rpow hh (le_trans hκ.le hkl)
  have hneg : h ^ (-kl) ≤ h ^ (-κ) :=
    Real.rpow_le_rpow_of_exponent_le hh (by linarith)
  have hnegone : h ^ (-kl) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hh (by linarith)
  have hupperloss : C * h ^ κ + Bu ≤ Cl * h ^ kl := by
    calc
      _ ≤ (C + Bu) * h ^ kl := by nlinarith [mul_le_mul_of_nonneg_left hu hCpos.le]
      _ ≤ _ := mul_le_mul_of_nonneg_right hClu (by positivity)
  have hentryloss : 4 * (C * h ^ κ) + Cp ≤ Cl * h ^ kl := by
    calc
      _ ≤ (4 * C + Cp) * h ^ kl := by nlinarith [mul_le_mul_of_nonneg_left hu hCpos.le]
      _ ≤ _ := mul_le_mul_of_nonneg_right hCle (by positivity)
  have hlowerloss : Cl⁻¹ * h ^ (-kl) ≤ C⁻¹ * h ^ (-κ) :=
    mul_le_mul hinvC hneg (by positivity) (by positivity)
  have hlowerref : Cl⁻¹ * h ^ (-kl) ≤ cr := by
    exact (mul_le_mul_of_nonneg_left hnegone (by positivity)).trans (by simpa using hinvcr)
  apply periodizedMatrixBounds_of_local_data_internal s m m₀ n₀ hm₀ hle hstrict K Cl kl L ε₀
    (fun t => A (t.1 + b, t.2)) (fun t => hA _)
  filter_upwards [hrep, hrep',
    periodizedMatrixBounds_truncated_error s n m hm K C κ γ ε hCpos.le M hM]
    with x hx hxrep herror
  have hnonneg (t : Fin (m : ℕ) × Fin ((m : ℕ) / 2)) : 0 ≤ A (t.1 + b, t.2) x := hxrep.1 _
  have hparentupper (t : Fin (m : ℕ) × Fin ((m : ℕ) / 2)) : A (t.1 + b, t.2) x ≤
      C * h ^ κ * (t.2.val + 1 : ℝ) ^ (-s.val - 2) := by
    simpa only [A, Nat.cast_add, Nat.cast_one, hparent] using (hx.1 (t.1 + b) t.2).2.1
  have hparentlower (t : Fin (m : ℕ) × Fin ((m : ℕ) / 2)) (ht : Ks ≤ t.2.val + 1) :
      (C⁻¹ * h ^ (-κ)) * (t.2.val + 1 : ℝ) ^ (-s.val - 2) ≤ A (t.1 + b, t.2) x := by
    have hthr : (n : ℝ) ^ (γ * ε) ≤ ((t.2.val + 1 : ℕ) : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right K _).trans ht)
    simpa only [A, Nat.cast_add, Nat.cast_one, hparent] using (hx.1 (t.1 + b) t.2).2.2 hthr
  refine ⟨?_, ?_, ?_⟩
  · intro t
    dsimp only
    rw [hloss kl, hloss (-kl), hloss L]
    refine ⟨localizedWeight_nonneg s m m₀ hm₀ hle n₀ K _ hnonneg t, ?_, ?_⟩
    · have hhupper := hupper m m₀ hm₀ hle n₀ K
        (fun u => A (u.1 + b, u.2) x) (C * h ^ κ) (by positivity) hparentupper t
      exact hhupper.trans (mul_le_mul_of_nonneg_right hupperloss (by positivity))
    · intro ht
      unfold localizedWeight
      split_ifs
      · have hthr : (n : ℝ) ^ (γ * ε) ≤ ((t.2.val + 1 : ℕ) : ℝ) := by
          simpa only [Nat.cast_add, Nat.cast_one] using hγ.trans ht
        have hhlo := (hx.1 (t.1.castLE hle + b)
          (t.2.castLE (Nat.div_le_div_right hle))).2.2 hthr
        have hmul := mul_le_mul_of_nonneg_right hlowerloss
          (show 0 ≤ (t.2.val + 1 : ℝ) ^ (-s.val - 2) by positivity)
        exact hmul.trans (by simpa only [Fin.val_castLE, Nat.cast_add, Nat.cast_one, hparent] using hhlo)
      · have hlen : K ≤ t.2.val + 1 := by
          exact_mod_cast hK.trans ht
        exact (mul_le_mul_of_nonneg_right hlowerref (by positivity)).trans
          (hlower m₀ hm₀ K t hlen)
  · have hhcoer := hcoer m m₀ n₀ hm₀ hle hstrict K Ks (le_max_left _ _) hKsone
      (hKs.trans hcut.2) (fun t => A (t.1 + b, t.2) x) hnonneg
      (C⁻¹ * h ^ (-κ)) (by positivity) hparentlower
    have harith := coercivity_loss_internal hκ.le hL.le
      (by linarith [s.property.1] : 0 < 1 + s.val) hCpos hB hc₀ hh
      (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hKsone) : (0 : ℝ) < Ks) hKsupper
    have hcoeff : Cl⁻¹ * h ^ (-kl) ≤
        c₀ * min 1 (C⁻¹ * h ^ (-κ) / B) * (Ks : ℝ) ^ (-1 - s.val) := by
      exact (mul_le_mul_of_nonneg_right hinvd (by positivity)).trans harith
    rw [show -kl * ε₀ = (-kl) * ε₀ by rfl, hloss]
    have horder := smul_le_smul_of_nonneg_right hcoeff
      (Matrix.nonneg_iff_posSemidef.mpr (Matrix.PosSemidef.one : Matrix.PosSemidef
        (1 : Matrix (Fin (m₀ : ℕ)) (Fin (m₀ : ℕ)) ℝ)))
    exact horder.trans hhcoer
  · intro i l hil
    have hpentry := hentry m hm K (fun t => A t x) (C * (n : ℝ) ^ (κ * ε))
      (by positivity) (by simpa only [hxrep.2] using herror) j i₀ hR i l hil
    rw [hloss]
    have hhentry : |matrix s m m₀ n₀ hm₀ (by omega) (by omega) K
        (fun t => A (t.1 + b, t.2)) x (i.castLE (by omega)) (l.castLE (by omega)) -
        ((2 : ℝ) • referenceIntervalMatrix s m₀ hm₀ K) (i.castLE (by omega))
          (l.castLE (by omega))| ≤
        (4 * (C * h ^ κ) + Cp) * (1 + ((l.val - i.val : ℕ) : ℝ)) ^ (-1 - s.val / 2) := by
      convert hpentry using 1
      · rfl
      · rw [hparent]
    exact hhentry.trans (mul_le_mul_of_nonneg_right hentryloss (by positivity))

end Riesz2.LocalizedMatrix
