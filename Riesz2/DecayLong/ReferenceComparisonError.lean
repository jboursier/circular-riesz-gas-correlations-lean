/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.LocalizedField
public import Riesz2.DecayLong.ReferenceOperatorKernelPart3
public import Riesz2.DecayLong.LocalizedMatrixPart6
public import Riesz2.ToMathlib.BoundedWeakSubtraction

/-!
# Source of the reference comparison error

The comparison error source in the proof of Proposition 5.15. The
composition lemmas take reference-solution estimates as inputs, using the
full reference matrix and the original scalar weak equation.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Finset
open scoped BigOperators Classical Fin.NatCast

namespace Riesz2.ReferenceComparisonError

/-- See the proof of Proposition 5.15 in the paper: the far portion of a row is
at distance at least `R / 64`, including nonintegral splitting radii. -/
theorem far_row_weight_internal (s : Riesz1.RieszExponent) (N : ℕ+)
    (R : ℝ) (hR : 0 < R) (c i l : Fin (N : ℕ))
    (hi : (Riesz1.cyclicIndexDistance N i c : ℝ) ≤ R / 64)
    (hl : ¬ (Riesz1.cyclicIndexDistance N l c : ℝ) ≤ R / 32) :
    (1 + (Riesz1.cyclicIndexDistance N i l : ℝ)) ^ (-1 - s.val / 2) ≤
      (64 : ℝ) ^ (1 + s.val / 2) * R ^ (-1 - s.val / 2) := by
  have ht : (Riesz1.cyclicIndexDistance N l c : ℝ) ≤
      (Riesz1.cyclicIndexDistance N i l : ℝ) +
        (Riesz1.cyclicIndexDistance N i c : ℝ) := by
    exact_mod_cast (cyclicIndexDistance_triangle l i c).trans_eq
      (by rw [cyclicIndexDistance_comm' N l i])
  have hd : R / 64 ≤ 1 + (Riesz1.cyclicIndexDistance N i l : ℝ) := by
    push Not at hl
    linarith
  calc
    _ ≤ (R / 64) ^ (-1 - s.val / 2) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hd (by linarith [s.property.1])
    _ = _ := by
      rw [Real.div_rpow hR.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 64)]
      rw [show -(-1 - s.val / 2) = 1 + s.val / 2 by ring]
      ring

/-- See the proof of Proposition 5.15 in the paper: the far contribution has
exponent `2 - s/2`, which is stronger than `2 - s`. -/
theorem far_power_absorption_internal (s : Riesz1.RieszExponent)
    (R : ℝ) (hR : 1 ≤ R) :
    R ^ (-1 - s.val / 2) * R ^ (-(1 - s.val)) ≤ R ^ (-(2 - s.val)) := by
  rw [← Real.rpow_add (by linarith : 0 < R)]
  exact Real.rpow_le_rpow_of_exponent_le hR (by linarith [s.property.1])

/-- See the proof of Proposition 5.15 in the paper: finite near/far convolution
estimate. The mass and central value assumptions are the two reference
estimates used in the proof. -/
theorem convolution_central_internal {V : Type*} [NormedAddCommGroup V]
    (s : Riesz1.RieszExponent) (N : ℕ+) (c : Fin (N : ℕ))
    (R T : ℝ) (hR : 1 ≤ R) (hT : 0 ≤ T) (φ : Fin (N : ℕ) → V)
    (hmass : (∑ l, ‖φ l‖) ≤ T * R ^ (-(1 - s.val)))
    (hcentral : ∀ l, (Riesz1.cyclicIndexDistance N l c : ℝ) ≤ R / 32 →
      ‖φ l‖ ≤ T * R ^ (-(2 - s.val)))
    (i : Fin (N : ℕ)) (hi : (Riesz1.cyclicIndexDistance N i c : ℝ) ≤ R / 64) :
    (∑ l, (1 + (Riesz1.cyclicIndexDistance N i l : ℝ)) ^ (-1 - s.val / 2) * ‖φ l‖) ≤
      (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-1 - s.val / 2) +
        (64 : ℝ) ^ (1 + s.val / 2)) * T * R ^ (-(2 - s.val)) := by
  let S := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-1 - s.val / 2)
  let w := fun l => (1 + (Riesz1.cyclicIndexDistance N i l : ℝ)) ^ (-1 - s.val / 2)
  let J := univ.filter (fun l : Fin (N : ℕ) => (Riesz1.cyclicIndexDistance N l c : ℝ) ≤ R / 32)
  have hw (l) : 0 ≤ w l := by dsimp only [w]; positivity
  have hsum : (∑ l, w l) ≤ S := by
    exact sum_le_two_mul_tsum_cyclicIndexDistance N i
      (g := fun k : ℕ => (1 + (k : ℝ)) ^ (-1 - s.val / 2)) (fun _ => by positivity)
      (by
        rw [show -1 - s.val / 2 = -(1 + s.val / 2) by ring]
        exact summable_one_add_rpow_neg (by linarith [s.property.1]))
  have hnear : (∑ l ∈ J, w l * ‖φ l‖) ≤ S * T * R ^ (-(2 - s.val)) := by
    calc
      _ ≤ ∑ l ∈ J, w l * (T * R ^ (-(2 - s.val))) := by
        apply sum_le_sum
        intro l hl
        exact mul_le_mul_of_nonneg_left (hcentral l (mem_filter.mp hl).2) (hw l)
      _ = (∑ l ∈ J, w l) * (T * R ^ (-(2 - s.val))) := by rw [sum_mul]
      _ ≤ S * (T * R ^ (-(2 - s.val))) :=
        mul_le_mul_of_nonneg_right ((sum_le_sum_of_subset_of_nonneg (subset_univ J)
          (fun l _ _ => hw l)).trans hsum) (by positivity)
      _ = _ := by ring
  have hfar : (∑ l ∈ Jᶜ, w l * ‖φ l‖) ≤
      (64 : ℝ) ^ (1 + s.val / 2) * T * R ^ (-(2 - s.val)) := by
    have ht : ∀ l ∈ Jᶜ, w l ≤ (64 : ℝ) ^ (1 + s.val / 2) * R ^ (-1 - s.val / 2) := by
      intro l hl
      apply far_row_weight_internal s N R (by linarith) c i l hi
      simpa only [J, mem_compl, mem_filter, mem_univ, true_and] using hl
    calc
      _ ≤ ∑ l ∈ Jᶜ, ((64 : ℝ) ^ (1 + s.val / 2) * R ^ (-1 - s.val / 2)) * ‖φ l‖ :=
        sum_le_sum fun l hl => mul_le_mul_of_nonneg_right (ht l hl) (norm_nonneg _)
      _ = ((64 : ℝ) ^ (1 + s.val / 2) * R ^ (-1 - s.val / 2)) * ∑ l ∈ Jᶜ, ‖φ l‖ := by rw [mul_sum]
      _ ≤ ((64 : ℝ) ^ (1 + s.val / 2) * R ^ (-1 - s.val / 2)) * (T * R ^ (-(1 - s.val))) :=
        mul_le_mul_of_nonneg_left
          ((sum_le_sum_of_subset_of_nonneg (subset_univ Jᶜ)
            (fun l _ _ => norm_nonneg (φ l))).trans hmass) (by positivity)
      _ = ((64 : ℝ) ^ (1 + s.val / 2) * T) *
          (R ^ (-1 - s.val / 2) * R ^ (-(1 - s.val))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (far_power_absorption_internal s R hR) (by positivity)
  have hsplit := sum_add_sum_compl J (fun l => w l * ‖φ l‖)
  change (∑ l, w l * ‖φ l‖) ≤ _
  rw [← hsplit]
  convert add_le_add hnear hfar using 1
  dsimp only [S]
  ring

/-- See the proof of Proposition 5.15 in the paper: construct the literal source
`-β E φ` in L², with the separate deterministic entry envelopes retained. -/
theorem source_exists_internal {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (s : Riesz1.RieszExponent) (N : ℕ+) (β A : ℝ) (hβ : 0 ≤ β) (hA : 0 ≤ A)
    (E : Ω → Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (hEm : ∀ i l, Measurable (fun x => E x i l))
    (hE : ∀ᵐ x ∂ν, ∀ i l, |E x i l| ≤
      A * (1 + (Riesz1.cyclicIndexDistance N i l : ℝ)) ^ (-1 - s.val / 2))
    (φ : Fin (N : ℕ) → Lp ℝ 2 ν) :
    ∃ g : Fin (N : ℕ) → Lp ℝ 2 ν,
      (∀ i, ∀ᵐ x ∂ν, g i x = -β * ∑ l, E x i l * φ l x) ∧
      (∀ i, ‖g i‖ ≤ β * A *
        ∑ l, (1 + (Riesz1.cyclicIndexDistance N i l : ℝ)) ^ (-1 - s.val / 2) * ‖φ l‖) := by
  have hex (i : Fin (N : ℕ)) := LocalizedField.bounded_row_source_internal univ
    (fun x l => -β * E x i l) (fun l => (hEm i l).const_mul _)
    (fun l => β * A * (1 + (Riesz1.cyclicIndexDistance N i l : ℝ)) ^ (-1 - s.val / 2))
    (fun _ => by positivity)
    (hE.mono (fun x hx l => by
      rw [abs_mul, abs_neg, abs_of_nonneg hβ]
      convert mul_le_mul_of_nonneg_left (hx i l) hβ using 1
      ring)) φ
  choose g hg hgn using hex
  refine ⟨g, ?_, ?_⟩
  · intro i
    filter_upwards [hg i] with x hx
    rw [hx, mul_sum]
    exact sum_congr rfl fun l _ => by ring
  · intro i
    convert hgn i using 1
    rw [mul_sum]
    exact sum_congr rfl fun l _ => by ring

/-- See the proof of Proposition 5.15 in the paper: both source bounds follow
from entry decay and the reference mass/central estimates, with one common
explicit coefficient independent of the cycle length. -/
theorem source_bounds_internal {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (s : Riesz1.RieszExponent) (N : ℕ+) (c : Fin (N : ℕ))
    (β A R T : ℝ) (hβ : 0 ≤ β) (hA : 0 ≤ A) (hR : 1 ≤ R) (hT : 0 ≤ T)
    (φ g : Fin (N : ℕ) → Lp ℝ 2 ν)
    (hgn : ∀ i, ‖g i‖ ≤ β * A *
      ∑ l, (1 + (Riesz1.cyclicIndexDistance N i l : ℝ)) ^ (-1 - s.val / 2) * ‖φ l‖)
    (hmass : (∑ l, ‖φ l‖) ≤ T * R ^ (-(1 - s.val)))
    (hcentral : ∀ l, (Riesz1.cyclicIndexDistance N l c : ℝ) ≤ R / 32 →
      ‖φ l‖ ≤ T * R ^ (-(2 - s.val))) :
    let S := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-1 - s.val / 2)
    let B := β * A * (1 + S + (64 : ℝ) ^ (1 + s.val / 2)) * T
    (∑ i, ‖g i‖) ≤ B * R ^ (-(1 - s.val)) ∧
      ∀ i, (Riesz1.cyclicIndexDistance N i c : ℝ) ≤ R / 64 →
        ‖g i‖ ≤ B * R ^ (-(2 - s.val)) := by
  intro S B
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hcol (l : Fin (N : ℕ)) :
      (∑ i, (1 + (Riesz1.cyclicIndexDistance N i l : ℝ)) ^ (-1 - s.val / 2)) ≤ S := by
    simp_rw [cyclicIndexDistance_comm' N _ l]
    exact sum_le_two_mul_tsum_cyclicIndexDistance N l
      (g := fun k : ℕ => (1 + (k : ℝ)) ^ (-1 - s.val / 2)) (fun _ => by positivity)
      (by
        rw [show -1 - s.val / 2 = -(1 + s.val / 2) by ring]
        exact summable_one_add_rpow_neg (by linarith [s.property.1]))
  constructor
  · calc
      _ ≤ ∑ i, β * A * ∑ l,
          (1 + (Riesz1.cyclicIndexDistance N i l : ℝ)) ^ (-1 - s.val / 2) * ‖φ l‖ := sum_le_sum fun i _ => hgn i
      _ = β * A * ∑ l, (∑ i, (1 + (Riesz1.cyclicIndexDistance N i l : ℝ)) ^ (-1 - s.val / 2)) * ‖φ l‖ := by
        rw [← mul_sum, sum_comm]
        simp_rw [sum_mul]
      _ ≤ β * A * ∑ l, S * ‖φ l‖ := by gcongr with l; exact hcol l
      _ = β * A * S * (∑ l, ‖φ l‖) := by rw [← mul_sum]; ring
      _ ≤ β * A * S * (T * R ^ (-(1 - s.val))) := mul_le_mul_of_nonneg_left hmass (by positivity)
      _ ≤ B * R ^ (-(1 - s.val)) := by
        dsimp only [B]
        have hb : S ≤ 1 + S + (64 : ℝ) ^ (1 + s.val / 2) := by
          have : 0 ≤ (64 : ℝ) ^ (1 + s.val / 2) := by positivity
          linarith
        convert mul_le_mul_of_nonneg_left hb (show 0 ≤ β * A * T * R ^ (-(1 - s.val)) by positivity) using 1 <;> ring
  · intro i hi
    have hn := (hgn i).trans (mul_le_mul_of_nonneg_left
      (convolution_central_internal s N c R T hR hT φ hmass hcentral i hi) (by positivity : 0 ≤ β * A))
    apply hn.trans
    dsimp only [B]
    have hb : S + (64 : ℝ) ^ (1 + s.val / 2) ≤ 1 + S + (64 : ℝ) ^ (1 + s.val / 2) := by linarith
    convert mul_le_mul_of_nonneg_left hb (show 0 ≤ β * A * T * R ^ (-(2 - s.val)) by positivity) using 1 <;> ring

/-- See the proof of Proposition 5.15 in the paper: restore the full reference
on the local cycle, with a loss measured in the parent size. The cutoff
and logarithmic local parameter are the existing localization choices.
The exponent precedes ε and the coefficient prefactor. -/
theorem local_full_error_internal (s : Riesz1.RieszExponent)
    (κloc γloc : ℝ) (hκloc : 0 ≤ κloc) (M₀ : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ Cloc : ℝ, 1 ≤ Cloc →
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
    ∀ (n n₀ m₀ : ℕ+) (_hn₀ : 1 < (n₀ : ℝ)) (hm₀ : 2 ≤ (m₀ : ℕ)),
    let K := ⌊(n : ℝ) ^ ε⌋₊ ^ M₀
    1 ≤ K →
    ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
      (Ml : Ω → Matrix (Fin (m₀ : ℕ)) (Fin (m₀ : ℕ)) ℝ),
    PeriodizedMatrixBounds (ν := ν) s n₀ m₀ hm₀ K Cloc κloc γloc
      (ε * Real.log (n : ℝ) / Real.log (n₀ : ℝ)) Ml →
    ∀ᵐ x ∂ν, ∀ i l,
      |Ml x i l - ((2 : ℝ) • referenceIntervalMatrix s m₀ hm₀ 1) i l| ≤
        C * (n : ℝ) ^ (κ * ε) *
          (1 + (Riesz1.cyclicIndexDistance m₀ i l : ℝ)) ^ (-1 - s.val / 2) := by
  obtain ⟨B, hB, hbounds⟩ := global_reference_error_estimates s
  let q := 1 + s.val / 2
  let S := ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s.val - 1)
  let κ := κloc + (M₀ : ℝ) * q + 1
  have hq : 0 < q := by dsimp only [q]; linarith [s.property.1]
  refine ⟨κ, by dsimp only [κ]; positivity, ?_⟩
  intro Cloc hCloc
  let C := Cloc + 4 * B * S
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro ε hε n n₀ m₀ hn₀ hm₀ K hK Ω _ ν Ml hMl
  have hnp : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hloc := LocalizedMatrix.local_loss_identity hnp hn₀ ε κloc
  have hcoeff : Cloc * (n₀ : ℝ) ^ (κloc * (ε * Real.log (n : ℝ) / Real.log (n₀ : ℝ))) +
      4 * B * S * (K : ℝ) ^ q ≤ C * (n : ℝ) ^ (κ * ε) := by
    rw [hloc]
    have hk1 : κloc ≤ κ := by
      dsimp only [κ]
      linarith [mul_nonneg (Nat.cast_nonneg M₀) hq.le]
    have hk2 : (M₀ : ℝ) * q ≤ κ := by dsimp only [κ]; linarith
    have h1 := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn1 (mul_le_mul_of_nonneg_right hk1 hε.le))
      (show 0 ≤ Cloc by linarith)
    have h2 := mul_le_mul_of_nonneg_left
      ((GlobalReferenceErrorInternal.cutoff_power_le n ε q hq.le M₀).trans
        (Real.rpow_le_rpow_of_exponent_le hn1 (mul_le_mul_of_nonneg_right hk2 hε.le)))
      (show 0 ≤ 4 * B * S by positivity)
    dsimp only [C]
    nlinarith only [h1, h2]
  filter_upwards [hbounds n₀ m₀ hm₀ K hK Cloc (by linarith) κloc γloc
    (ε * Real.log (n : ℝ) / Real.log (n₀ : ℝ)) ν Ml hMl] with x hx
  intro i l
  have hh := (hx.1 i l).trans (mul_le_mul_of_nonneg_right hcoeff
    (show 0 ≤ (1 + (Riesz1.cyclicIndexDistance m₀ i l : ℝ)) ^ (-q) by positivity))
  rw [ReferenceOperatorKernel.reference_eq s m₀ hm₀] at hh
  simpa only [Matrix.sub_apply, q, show -(1 + s.val / 2) = -1 - s.val / 2 by ring] using hh

/-- See the proof of Proposition 5.15 in the paper: internal composition with
exactly the mass, central value and central gradient conclusions of
the proof of Proposition 5.15. The reference solution is the full
finite kernel inverse, including the constant component mode. The other two weak equations come from the boundary decomposition.

The loss exponent precedes all prefactors and ε. The bound is uniform for
positive β bounded above by `βhi`. -/
theorem comparison_error_of_reference_estimates_internal (s : Riesz1.RieszExponent)
    (κloc γloc κφ : ℝ) (hκloc : 0 ≤ κloc) (hκφ : 0 ≤ κφ) (M₀ : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ Cloc : ℝ, 1 ≤ Cloc →
    ∀ Cφ : ℝ, 0 < Cφ → ∀ βhi : ℝ, 0 < βhi →
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
    ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
      (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q),
    ∀ (n n₀ m₀ : ℕ+) (_hn₀ : 1 < (n₀ : ℝ)) (hm₀ : 2 ≤ (m₀ : ℕ)),
    let K := ⌊(n : ℝ) ^ ε⌋₊ ^ M₀
    1 ≤ K →
    ∀ Ml : Ω → Matrix (Fin (m₀ : ℕ)) (Fin (m₀ : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n₀ m₀ hm₀ K Cloc κloc γloc
      (ε * Real.log (n : ℝ) / Real.log (n₀ : ℝ)) Ml →
    ∀ β : InverseTemperature, β.val ≤ βhi →
    ∀ (χ : Lp ℝ 2 ν) (c : Fin (m₀ : ℕ)) (R : ℝ), 16 ≤ R →
    ∀ (f b : Fin (m₀ : ℕ) → Lp ℝ 2 ν) (ψ₀ z : Fin (m₀ : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β.val • Ml x) ⊤ (fun i => f i + b i) ψ₀ →
    WeightedWeakSolution Q (fun x => β.val • Ml x) ⊤ b z →
    let φ := fun i => ∑ k, ScalarFormHilbert.equiv Q hQ
      (FiniteFormReferenceKernel.solutionKernel Q hQ _
        (ReferenceOperatorKernelPart3.reference_posDef s β m₀ hm₀) i k (f k))
    ((∑ i, ‖(φ i).val‖) ≤ Cφ * (n : ℝ) ^ (κφ * ε) * ‖χ‖ * R ^ (-(1 - s.val)) ∧
      ∀ i, (Riesz1.cyclicIndexDistance m₀ i c : ℝ) ≤ R / 32 →
        ‖(φ i).val‖ ≤ Cφ * (n : ℝ) ^ (κφ * ε) * ‖χ‖ * R ^ (-(2 - s.val)) ∧
        Real.sqrt (Q.2 (φ i) (φ i)) ≤
          Cφ * (n : ℝ) ^ (κφ * ε) * ‖χ‖ * R ^ (-(3 - s.val) / 2)) →
    ∃ g : Fin (m₀ : ℕ) → Lp ℝ 2 ν,
      (∀ i, ∀ᵐ x ∂ν, g i x = -β.val * ∑ l,
        (Ml x i l - ((2 : ℝ) • referenceIntervalMatrix s m₀ hm₀ 1) i l) * (φ l).val x) ∧
      WeightedWeakSolution Q (fun x => β.val • Ml x) ⊤ g
        (fun i => ψ₀ i - z i - φ i) ∧
      (∑ i, ‖g i‖) ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ * R ^ (-(1 - s.val)) ∧
      ∀ i, (Riesz1.cyclicIndexDistance m₀ i c : ℝ) ≤ R / 64 →
        ‖g i‖ ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ * R ^ (-(2 - s.val)) := by
  obtain ⟨κE, hκE, herror⟩ := local_full_error_internal s κloc γloc hκloc M₀
  refine ⟨κE + κφ, by positivity, ?_⟩
  intro Cloc hCloc Cφ hCφ βhi hβhi
  obtain ⟨CE, hCE, herror⟩ := herror Cloc hCloc
  let S := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-1 - s.val / 2)
  let Z := 1 + S + (64 : ℝ) ^ (1 + s.val / 2)
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hZ : 0 < Z := by dsimp only [Z]; positivity
  let C := βhi * CE * Z * Cφ
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro ε hε Ω _ ν Q hQ n n₀ m₀ hn₀ hm₀ K hK Ml hMl β hβ χ c R hR f b ψ₀ z hψ hz φ hφ
  let A := CE * (n : ℝ) ^ (κE * ε)
  let T := Cφ * (n : ℝ) ^ (κφ * ε) * ‖χ‖
  let H₀ := (2 : ℝ) • referenceIntervalMatrix s m₀ hm₀ 1
  let E := fun x => Ml x - H₀
  have hE := herror ε hε n n₀ m₀ hn₀ hm₀ hK ν Ml hMl
  have hEm (i l) : Measurable (fun x => E x i l) := (hMl.1 i l).sub measurable_const
  obtain ⟨g, hg, hgn⟩ := source_exists_internal s m₀ β.val A β.property.le
    (by dsimp only [A]; positivity) E hEm hE (fun i => (φ i).val)
  have hbounds := source_bounds_internal s m₀ c β.val A R T β.property.le
    (by dsimp only [A]; positivity) (by linarith) (by dsimp only [T]; positivity)
    (fun i => (φ i).val) g hgn hφ.1 (fun i hi => (hφ.2 i hi).1)
  have hcoeff : β.val * A * Z * T ≤ C * (n : ℝ) ^ ((κE + κφ) * ε) * ‖χ‖ := by
    calc
      _ ≤ βhi * A * Z * T := by gcongr
      _ = _ := by
        dsimp only [A, T, C]
        rw [show (κE + κφ) * ε = κE * ε + κφ * ε by ring,
          Real.rpow_add (by positivity : (0 : ℝ) < n)]
        ring
  have hMm := SchurRestriction.periodized_scaled_measurable β.val hMl
  have hMb := SchurRestriction.periodized_scaled_bounded β.val hMl
  let H := (2 * β.val) • referenceIntervalMatrix s m₀ hm₀ 1
  have hHm (i l : Fin (m₀ : ℕ)) : Measurable (fun _ : Ω => H i l) := measurable_const
  have hHb : ∃ B : ℝ, ∀ᵐ _x : Ω ∂ν, ∀ i l, |H i l| ≤ B := by
    refine ⟨∑ i, ∑ l, |H i l|, Eventually.of_forall (fun _ i l => ?_)⟩
    exact (single_le_sum (fun l _ => abs_nonneg (H i l)) (mem_univ l)).trans
      (single_le_sum (fun i _ => sum_nonneg (fun l _ => abs_nonneg (H i l))) (mem_univ i))
  have hMs : ∀ᵐ x ∂ν, ∀ i l, (β.val • Ml x) i l = (β.val • Ml x) l i := by
    filter_upwards [hMl.2.1] with x hx i l
    simp only [Matrix.smul_apply, smul_eq_mul, hx.1 i l]
  have hHs : ∀ᵐ _x : Ω ∂ν, ∀ i l, H i l = H l i := by
    apply Eventually.of_forall
    intro _ i l
    dsimp only [H]
    rw [← ReferenceOperatorKernel.reference_eq s m₀ hm₀]
    exact congrArg (fun a : ℝ => (2 * β.val) * a)
      (by simpa using congrFun (congrFun (rieszMatrix_posDef s m₀ hm₀).1 l) i)
  have hφsol := ReferenceOperatorKernelPart3.referenceInverse_weightedWeakSolution Q hQ s β m₀ hm₀ f
  have hgpair : ∀ᵐ x ∂ν, ∀ i, g i x = ∑ l, (H i l - (β.val • Ml x) i l) * (φ l).val x := by
    filter_upwards [ae_all_iff.mpr hg] with x hx i
    rw [hx i, mul_sum]
    apply sum_congr rfl
    intro l _
    dsimp only [E, H₀, H, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have heq := BoundedWeakSubtraction.comparison_equation Q (fun x => β.val • Ml x)
    (fun _ => H) hMm hHm hMb hHb hMs hHs f b g ψ₀ z φ hψ hz hφsol hgpair
  refine ⟨g, hg, heq, ?_, ?_⟩
  · exact hbounds.1.trans (mul_le_mul_of_nonneg_right hcoeff (by positivity))
  · intro i hi
    exact (hbounds.2 i hi).trans (mul_le_mul_of_nonneg_right hcoeff (by positivity))

/-- See the proof of Proposition 5.15 in the paper: the localized matrix bounds
hold for the actual coefficient witness returned by the boundary construction.
The matrix is independent of the interval representation. -/
theorem localization_for_representation_internal (s : Riesz1.RieszExponent)
    (κstar γstar : ℝ) (M₀ : ℕ+) (hκstar : 0 < κstar) (hγstar : 0 < γstar) :
    ∃ κloc γloc D : ℝ, 0 < κloc ∧ 0 < γloc ∧ 0 < D ∧
    ∀ Cstar : ℝ, 1 ≤ Cstar → ∃ Cloc : ℝ, 1 ≤ Cloc ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
      (ε : ℝ), 0 < ε → ∀ (n m : ℕ+), 2 ≤ (n : ℕ) →
    ∀ hm : 2 ≤ (m : ℕ),
    let K := ⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ)
    ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M →
    ∀ A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → Ω → ℝ,
    (∀ t, Measurable (A t)) →
    (∀ᵐ x ∂ν, IntervalBoundary.intervalMatrix m m le_rfl (fun t => A t x) = M x) →
    ∀ (j i₀ : Fin (m : ℕ)) (hR : 16 ≤ Riesz1.cyclicIndexDistance m j i₀),
    (n : ℝ) ^ (D * ε) ≤ (Riesz1.cyclicIndexDistance m j i₀ : ℝ) →
    let n₀ := LocalizedMatrix.windowSize m j i₀
    let m₀ := LocalizedMatrix.windowPeriod s m j i₀
    let hn : (n₀ : ℕ) ≤ (m : ℕ) := by
      have := (LocalizedMatrix.window_size_bounds m j i₀ hR).2.2.2
      dsimp only [n₀]; omega
    let hn₀ : (n₀ : ℕ) ≤ (m₀ : ℕ) := by
      have := LocalizedMatrix.two_windowSize_lt_period s m j i₀ hR
      dsimp only [n₀, m₀]; omega
    let hm₀ : 2 ≤ (m₀ : ℕ) := by
      have := LocalizedMatrix.two_windowSize_lt_period s m j i₀ hR
      have := n₀.pos
      dsimp only [n₀, m₀] at *; omega
    let b := j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ))
    PeriodizedMatrixBounds (ν := ν) s n₀ m₀ hm₀ K Cloc κloc γloc
      (ε * Real.log (n : ℝ) / Real.log (n₀ : ℝ))
      (LocalizedMatrix.matrix s m m₀ n₀ hm₀ hn hn₀ K (fun t => A (t.1 + b, t.2))) := by
  obtain ⟨κloc, γloc, D, hκloc, hγloc, hD, hlocal⟩ :=
    LocalizedMatrix.localized_periodizedMatrixBounds s κstar γstar M₀ hκstar hγstar
  refine ⟨κloc, γloc, D, hκloc, hγloc, hD, ?_⟩
  intro Cstar hCstar
  obtain ⟨Cloc, hCloc, hlocal⟩ := hlocal Cstar hCstar
  refine ⟨Cloc, hCloc, ?_⟩
  intro Ω _ ν ε hε n m hn hm K M hM A hAm hArep j i₀ hR hsep n₀ m₀ hnp hn₀ hm₀ b
  obtain ⟨B, hBm, hBrep, hb⟩ := hlocal ν ε hε n m hn hm M hM
  have heq :
      (LocalizedMatrix.matrix s m m₀ n₀ hm₀ hnp hn₀ K (fun t => B (t.1 + b, t.2))) =ᵐ[ν]
      (LocalizedMatrix.matrix s m m₀ n₀ hm₀ hnp hn₀ K (fun t => A (t.1 + b, t.2))) := by
    filter_upwards [hBrep, hArep] with x hx hy
    exact LocalizedMatrix.matrix_eq_of_intervalMatrix_eq_internal s m m₀ n₀ hm₀ hnp hn₀
      (LocalizedMatrix.window_size_bounds m j i₀ hR).2.2.2 K B A x (hx.2.trans hy.symm) b
  exact LocalizedBoundary.periodized_bounds_congr_internal s n₀ m₀ hm₀ K Cloc κloc γloc
    (ε * Real.log (n : ℝ) / Real.log (n₀ : ℝ)) _ _ (hb j i₀ hR hsep)
    (LocalizedBoundary.localized_matrix_measurable_internal s m m₀ n₀ hm₀ hnp hn₀ K _
      (fun t => hAm _)) heq

end Riesz2.ReferenceComparisonError
