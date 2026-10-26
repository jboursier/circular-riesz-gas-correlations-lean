/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.OrdinaryGapCauchy

/-!
# Ordinary gap expectations using the support range

See the proof of Proposition 6.6 in the paper. Consecutive supports are moved centrally
under the ordinary Gibbs laws before applying the tilted comparison.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace Riesz2.OrdinaryGapCauchyV2

open OrdinaryGapCauchy

/-- See the proof of Proposition 6.6 in the paper: a backward cyclic shift moves
an interval support left without wrapping. -/
theorem depends_shift_left {n : ℕ+} (G : BlockObservable n) (a k : ℕ)
    (hG : DependsOnBlockCoordinates G
      (Finset.univ.filter (fun i => a + 1 ≤ i.val ∧ i.val < a + 1 + k))) :
    DependsOnBlockCoordinates (relabel G (finRotate (n : ℕ)))
      (Finset.univ.filter (fun i => a ≤ i.val ∧ i.val < a + k)) := by
  intro x y hxy
  apply hG
  intro i hi
  have hi' : a + 1 ≤ i.val ∧ i.val < a + 1 + k := by simpa using hi
  have hne : i ≠ 0 := by intro h; have hz : i.val = 0 := congrArg Fin.val h; omega
  apply hxy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    coe_finRotate_symm_of_ne_zero hne]
  omega

/-- See the proof of Proposition 6.6 in the paper: a forward cyclic shift moves
an interval support right when its last coordinate stays in the active block. -/
theorem depends_shift_right {n : ℕ+} (G : BlockObservable n) (a k : ℕ)
    (hak : a + k < (n : ℕ))
    (hG : DependsOnBlockCoordinates G
      (Finset.univ.filter (fun i => a ≤ i.val ∧ i.val < a + k))) :
    DependsOnBlockCoordinates (relabel G (finRotate (n : ℕ)).symm)
      (Finset.univ.filter (fun i => a + 1 ≤ i.val ∧ i.val < a + 1 + k)) := by
  intro x y hxy
  apply hG
  intro i hi
  have hi' : a ≤ i.val ∧ i.val < a + k := by simpa using hi
  have hval : ((finRotate (n : ℕ)) i).val = i.val + 1 := by
    have hn : 1 < (n : ℕ) := by omega
    rw [finRotate_apply, Fin.val_add]
    have hone : ((1 : Fin (n : ℕ)) : ℕ) = 1 := by
      change 1 % (n : ℕ) = 1
      exact Nat.mod_eq_of_lt hn
    rw [hone, Nat.mod_eq_of_lt (by omega)]
  change x ((finRotate (n : ℕ)) i) = y ((finRotate (n : ℕ)) i)
  apply hxy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, hval]
  omega

/-- See the proof of Proposition 6.6 in the paper: forward support translation
preserves ordinary expectations, by undoing the backward translation. -/
theorem integral_shift_right (p : Parameters) (n N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (G : BlockObservable n) (a k : ℕ) (hak : a + k < (n : ℕ))
    (hG : DependsOnBlockCoordinates G
      (Finset.univ.filter (fun i => a ≤ i.val ∧ i.val < a + k))) :
    (∫ X : Riesz1.Configuration N,
      (relabel G (finRotate (n : ℕ)).symm).val (finiteGapBlock X) ∂gibbsMeasure p N) =
    ∫ X : Riesz1.Configuration N, G.val (finiteGapBlock X) ∂gibbsMeasure p N := by
  have h := integral_relabel_cycle p n N hN
    (relabel G (finRotate (n : ℕ)).symm) _ (depends_shift_right G a k hak hG)
    (by intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi; omega)
  have he : relabel (relabel G (finRotate (n : ℕ)).symm) (finRotate (n : ℕ)) = G := by
    apply Subtype.ext
    funext x
    change G.val ((x ∘ (finRotate (n : ℕ)).symm) ∘ (finRotate (n : ℕ))) = G.val x
    apply congrArg G.val
    funext i
    simp
  rw [he] at h
  exact h.symm

/-- See the proof of Proposition 6.6 in the paper: any consecutive support can
be placed at another interval of the same length. The ordinary expectations
in every volume and temperature agree, and the global derivative sum decreases. -/
theorem interval_transport {n : ℕ+} (a b k : ℕ)
    (ha : a + k ≤ (n : ℕ)) (hb : b + k ≤ (n : ℕ))
    (G : BlockObservable n)
    (hG : DependsOnBlockCoordinates G
      (Finset.univ.filter (fun i => a ≤ i.val ∧ i.val < a + k))) :
    ∃ H : BlockObservable n,
      DependsOnBlockCoordinates H
        (Finset.univ.filter (fun i => b ≤ i.val ∧ i.val < b + k)) ∧
      blockDerivativeNorm H ≤ blockDerivativeNorm G ∧
      ∀ (p : Parameters) (N : ℕ+), 2 ≤ (N : ℕ) →
        (∫ X : Riesz1.Configuration N, H.val (finiteGapBlock X) ∂gibbsMeasure p N) =
        ∫ X : Riesz1.Configuration N, G.val (finiteGapBlock X) ∂gibbsMeasure p N := by
  induction a generalizing G with
  | zero =>
    induction b with
    | zero => exact ⟨G, hG, le_rfl, fun _ _ _ => rfl⟩
    | succ b ih =>
      obtain ⟨H, hH, hnorm, hint⟩ := ih (by omega)
      refine ⟨relabel H (finRotate (n : ℕ)).symm,
        depends_shift_right H b k (by omega) hH,
        (relabel_norm_le H _).trans hnorm, ?_⟩
      intro p N hN
      exact (integral_shift_right p n N hN H b k (by omega) hH).trans (hint p N hN)
  | succ a ih =>
    let H := relabel G (finRotate (n : ℕ))
    have hH := depends_shift_left G a k hG
    obtain ⟨F, hF, hnorm, hint⟩ := ih (by omega) H hH
    refine ⟨F, hF, hnorm.trans (relabel_norm_le G _), ?_⟩
    intro p N hN
    exact (hint p N hN).trans (integral_relabel_cycle p n N hN G _ hG
      (by intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi; omega))

end Riesz2.OrdinaryGapCauchyV2
