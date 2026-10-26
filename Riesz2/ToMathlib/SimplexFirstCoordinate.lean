/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.AffineSimplexCharts
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Splitting the first free coordinate of a simplex chart

These are changes of coordinates for `AffineSimplex.chart`, with Lebesgue
Jacobian one. The remaining coordinates may have dimension zero.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Riesz2.AffineSimplex

/-- Separate the first coordinate, retaining Euclidean coordinates on the fibre. -/
def splitFirst (n : ℕ) : (Fin (n + 1) → ℝ) ≃ₗ[ℝ]
    ℝ × EuclideanSpace ℝ (Fin n) where
  toFun x := (x 0, WithLp.toLp 2 (Fin.tail x))
  invFun p := Fin.cons p.1 (WithLp.ofLp p.2)
  left_inv x := by ext i; exact Fin.cases rfl (fun j => rfl) i
  right_inv p := by cases p; rfl
  map_add' x y := rfl
  map_smul' a x := rfl

theorem splitFirst_symm_apply (n : ℕ) (p : ℝ × EuclideanSpace ℝ (Fin n)) :
    (splitFirst n).symm p = Fin.cons p.1 (WithLp.ofLp p.2) := rfl

theorem chart_convex_combination (n : ℕ) (L : ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) {a b : ℝ} (hab : a + b = 1) :
    chart n L (a • x + b • y) = a • chart n L x + b • chart n L y := by
  rw [chart_eq_tangentMap_add n L (a • x + b • y),
    chart_eq_tangentMap_add n L x, chart_eq_tangentMap_add n L y]
  simp only [map_add, map_smul, smul_add]
  have he : a • chart n L 0 + b • chart n L 0 = chart n L 0 := by
    rw [← add_smul, hab, one_smul]
  calc
    _ = a • tangentMap n x + b • tangentMap n y +
        (a • chart n L 0 + b • chart n L 0) := congrArg
          (fun z => a • tangentMap n x + b • tangentMap n y + z) he.symm
    _ = _ := by abel

theorem measurePreserving_splitFirst (n : ℕ) :
    MeasurePreserving (splitFirst n) := by
  have h := ((MeasurePreserving.id (volume : Measure ℝ)).prod
    (PiLp.volume_preserving_toLp (Fin n))).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
  change MeasurePreserving (fun x : Fin (n + 1) → ℝ =>
    (x 0, WithLp.toLp 2 (Fin.tail x))) volume volume
  convert h using 1
  funext x
  rfl

/-- Projection of the positive simplex chart onto its first coordinate. -/
theorem fst_image_splitFirst_domain (n : ℕ) (L : ℝ) :
    Prod.fst '' ((fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
      WithLp.toLp 2 ((splitFirst n).symm p)) ⁻¹' chartDomain (n + 1) L) = Ioo 0 L := by
  ext u
  constructor
  · rintro ⟨p, hp, rfl⟩
    change (∀ i, 0 < (Fin.cons p.1 (WithLp.ofLp p.2) : Fin (n + 1) → ℝ) i) ∧
      (∑ i, (Fin.cons p.1 (WithLp.ofLp p.2) : Fin (n + 1) → ℝ) i) < L at hp
    have ht : 0 ≤ ∑ i, p.2 i := Finset.sum_nonneg (fun i _ => (hp.1 i.succ).le)
    refine ⟨hp.1 0, ?_⟩
    rw [Fin.sum_univ_succ] at hp
    simpa only [Fin.cons_zero, Fin.cons_succ] using lt_of_le_of_lt
      (le_add_of_nonneg_right ht) hp.2
  · intro hu
    let z : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2
      (fun _ => (L - u) / (n + 1 : ℝ))
    refine ⟨(u, z), ?_, rfl⟩
    change (∀ i, 0 < (Fin.cons u (WithLp.ofLp z) : Fin (n + 1) → ℝ) i) ∧
      (∑ i, (Fin.cons u (WithLp.ofLp z) : Fin (n + 1) → ℝ) i) < L
    have hn : (0 : ℝ) < n + 1 := by positivity
    have hd : 0 < (L - u) / (n + 1 : ℝ) := div_pos (sub_pos.mpr hu.2) hn
    constructor
    · intro i
      exact Fin.cases hu.1 (fun _ => hd) i
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, z,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have he := (div_mul_cancel₀ (L - u) hn.ne')
      nlinarith

theorem convex_chartDomain (n : ℕ) (L : ℝ) : Convex ℝ (chartDomain n L) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    change 0 < a * x i + b * y i
    have hpos : 0 < a ∨ 0 < b := by rcases lt_or_eq_of_le ha with h | h; exact Or.inl h; right; linarith
    rcases hpos with h | h
    · exact add_pos_of_pos_of_nonneg (mul_pos h (hx.1 i)) (mul_nonneg hb (hy.1 i).le)
    · exact add_pos_of_nonneg_of_pos (mul_nonneg ha (hx.1 i).le) (mul_pos h (hy.1 i))
  · change (∑ i, (a * x i + b * y i)) < L
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    calc
      a * (∑ i, x i) + b * (∑ i, y i) < a * L + b * L := by
        rcases lt_or_eq_of_le ha with h | h
        · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hx.2 h)
            (mul_le_mul_of_nonneg_left hy.2.le hb)
        · have hb' : 0 < b := by linarith
          exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hx.2.le ha)
            (mul_lt_mul_of_pos_left hy.2 hb')
      _ = L := by rw [← add_mul, hab, one_mul]

theorem isBounded_chartDomain (n : ℕ) (L : ℝ) :
    Bornology.IsBounded (chartDomain n L) := by
  have hsub : WithLp.ofLp '' chartDomain n L ⊆
      Set.Icc (fun _ : Fin n => (0 : ℝ)) (fun _ => L) := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨fun i => (hx.1 i).le, fun i => ?_⟩
    exact (Finset.single_le_sum (fun j _ => (hx.1 j).le) (Finset.mem_univ i)).trans hx.2.le
  have hi := ((isCompact_Icc (a := fun _ : Fin n => (0 : ℝ))
    (b := fun _ => L)).image (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ))).isBounded
  apply hi.subset
  intro x hx
  exact ⟨WithLp.ofLp x, hsub ⟨x, hx, rfl⟩, rfl⟩

end Riesz2.AffineSimplex
