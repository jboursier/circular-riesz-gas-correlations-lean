/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.PaperPhysicalComparisonPart3

/-!
# Uniform bounds for the paper's two matrices

The full matrix verification after equation (4.13), with
polynomial degree chosen before the tilt scale and every temperature.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal ContDiff Topology

namespace Riesz2.DecayShort
open PhysicalComparison

set_option backward.isDefEq.respectTransparency false in
/-- The deterministic matrix verification following equation (4.13)
in the paper, with its constants uniform in the tilt scale and volumes.
See Proposition 4.10 and Subsection 4.5 of the paper.
Both the exponent and prefactor precede every inverse temperature. -/
theorem paper_uniform_matrix_bounds (s : ℝ) (hs : 1 < s)
    (κ : ℝ) (_hκ : 0 ≤ κ) :
    ∃ q : ℝ, 0 ≤ q ∧ ∀ (θ : PhysicalCutoff) (h : ℝ), 0 < h →
      ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : Parameters), p.val.2 = s → ∀ (n : ℕ+) (m : ℕ) (U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ),
        (∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) //
          y ∈ gapAmbientDomain ((n : ℕ)+m).succPNat},
          U y.val = p.val.1*physicalAmbientGapEnergy p ((n : ℕ)+m).succPNat y) →
        2 ≤ (n : ℕ) + m + 1 → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 → ∀ b : Bool,
        let D := A * (n : ℝ) ^ (κ * h)
        let M := paperFrozenInteriorMatrix p n m U θ h b D
        let H := paperFrozenPhysicalMatrix p n m U θ h b D
        let hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ) := by
          simp only [Nat.succPNat_coe]; omega
        let P := fun x => IntervalBoundary.boundaryMatrix ((n : ℕ) + m).succPNat n hn
          (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
        let g : ComponentGeometry (Fin (n : ℕ)) := Sum.inl
          ⟨fun i => (i.val : ℤ), fun i j hij => Fin.ext (Int.ofNat_inj.mp hij)⟩
        (∀ ρ : Measure (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)),
          SummableCoerciveMatrix (ρ := ρ) ⟨s,hs⟩ n h C q g M) ∧
        (∀ x (z : Fin (n : ℕ) → ℝ),
          (C * (n : ℝ) ^ (q * h))⁻¹ * (∑ i, z i ^ 2) ≤
            (∑ i, ∑ j, z i * H x i j * z j) ∧
          (∑ i, ∑ j, z i * H x i j * z j) ≤
            C * (n : ℝ) ^ (q * h) * (∑ i, z i ^ 2)) ∧
        (∀ x, x ∈ paperProperGoodEvent p n m U h D →
          (∀ i, ∑ j, |P x i j| ≤ C * (n : ℝ) ^ (q * h)) ∧
          (∀ j, ∑ i, |P x i j| ≤ C * (n : ℝ) ^ (q * h)) ∧
          ∀ i j, (n : ℝ) / 8 ≤ (ConditionalScores.boundaryDistance j : ℝ) →
            P x i j ≤ C * (n : ℝ) ^ (q * h) * (n : ℝ) ^ (-s)) := by
  let q := max (s + 2) (max 4 κ)
  have hq4 : 4 ≤ q := (le_max_left 4 κ).trans (le_max_right _ _)
  have hqκ : κ ≤ q := (le_max_right 4 κ).trans (le_max_right _ _)
  have hqs : s + 2 ≤ q := le_max_left _ _
  refine ⟨q, by linarith, ?_⟩
  intro θ h hh A hA
  obtain ⟨Ci,hCi,hentry⟩ := paperFrozenInteriorMatrix_entry_bound θ
  obtain ⟨Cp,hCp,hupper⟩ := paperFrozenPhysicalMatrix_upper θ
  let S := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s)
  let K := 2 * (8 : ℝ) ^ s
  let C := 1 + Ci + Cp + A + 2 * A * (S + 1) + K * A + S * A
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hA0 : 0 ≤ A := by linarith
  have hC1 : 1 ≤ C := by
    dsimp only [C]
    nlinarith [mul_nonneg hK hA0, mul_nonneg hS hA0,
      mul_nonneg hA0 (show 0 ≤ S + 1 by linarith)]
  have hCe : 1 + A + Ci ≤ C := by
    dsimp only [C]
    nlinarith [mul_nonneg hK hA0, mul_nonneg hS hA0,
      mul_nonneg hA0 (show 0 ≤ S + 1 by linarith)]
  have hCu : 1 + Cp + 2 * A * (S + 1) ≤ C := by
    dsimp only [C]
    nlinarith [mul_nonneg hK hA0, mul_nonneg hS hA0]
  have hCb : A * S ≤ C := by
    dsimp only [C]
    nlinarith [mul_nonneg hK hA0, mul_nonneg hA0 (show 0 ≤ S + 1 by linarith)]
  have hCk : K * A ≤ C := by
    dsimp only [C]
    nlinarith [mul_nonneg hS hA0, mul_nonneg hA0 (show 0 ≤ S + 1 by linarith)]
  refine ⟨C,hC1,?_⟩
  intro p hp
  subst s
  have hs : 1 < p.val.2 := hs
  intro n m U hv hN hhalf b D M H hn P g
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hqpow : 1 ≤ (n : ℝ) ^ (q * h) := Real.one_le_rpow hn1 (by nlinarith)
  have hpowκ : (n : ℝ) ^ (κ * h) ≤ (n : ℝ) ^ (q * h) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (mul_le_mul_of_nonneg_right hqκ hh.le)
  have hpow4 : (n : ℝ) ^ (4 * h) ≤ (n : ℝ) ^ (q * h) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (mul_le_mul_of_nonneg_right hq4 hh.le)
  have hD : 0 ≤ D := mul_nonneg hA0 (Real.rpow_nonneg hn0.le _)
  have hC0 : 0 < C := by linarith
  have hlower : (C * (n : ℝ) ^ (q * h))⁻¹ ≤
      (n : ℝ) ^ (-(p.val.2 + 2) * h) := by
    rw [show -(p.val.2 + 2) * h = -((p.val.2 + 2) * h) by ring, Real.rpow_neg hn0.le]
    apply (inv_le_inv₀ (by positivity) (Real.rpow_pos_of_pos hn0 _)).mpr
    exact (Real.rpow_le_rpow_of_exponent_le hn1
      (mul_le_mul_of_nonneg_right hqs hh.le)).trans
      (le_mul_of_one_le_left (Real.rpow_nonneg hn0.le _) hC1)
  have hcoeff : 1 + D + Ci * (n : ℝ) ^ (4 * h) ≤ C * (n : ℝ) ^ (q * h) := by
    calc
      _ ≤ (1 + A + Ci) * (n : ℝ) ^ (q * h) := by
        dsimp only [D]
        nlinarith [mul_le_mul_of_nonneg_left hpowκ hA0,
          mul_le_mul_of_nonneg_left hpow4 hCi.le]
      _ ≤ _ := mul_le_mul_of_nonneg_right hCe (Real.rpow_nonneg hn0.le _)
  have hphysical : 1 + Cp * (n : ℝ) ^ (4 * h) + D * (S + 1) ≤
      C * (n : ℝ) ^ (q * h) := by
    calc
      _ ≤ (1 + Cp + 2 * A * (S + 1)) * (n : ℝ) ^ (q * h) := by
        dsimp only [D]
        nlinarith [mul_le_mul_of_nonneg_left hpow4 hCp.le,
          mul_le_mul_of_nonneg_left hpowκ (show 0 ≤ 2 * A * (S + 1) by positivity)]
      _ ≤ _ := mul_le_mul_of_nonneg_right hCu (Real.rpow_nonneg hn0.le _)
  have hbound : D * S ≤ C * (n : ℝ) ^ (q * h) := by
    calc
      _ = (A * S) * (n : ℝ) ^ (κ * h) := by dsimp only [D]; ring
      _ ≤ (A * S) * (n : ℝ) ^ (q * h) := mul_le_mul_of_nonneg_left hpowκ (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hCb (Real.rpow_nonneg hn0.le _)
  obtain ⟨hmH,hmM,hsH,hsM⟩ := paperFrozenMatrices_measurable_symmetric p hs n m U θ h hh b D
  refine ⟨fun ρ => ⟨hmM, ae_of_all ρ fun x => ⟨hsM x, ?_, ?_⟩⟩, ?_, ?_⟩
  · intro z
    exact (mul_le_mul_of_nonneg_right hlower (Finset.sum_nonneg fun i _ => sq_nonneg (z i))).trans
      (paperFrozenInteriorMatrix_lower p hs n m U (by omega) θ h hh b D x z)
  · intro i j
    apply (hentry p n m U hhalf h hh b D hD x i j).trans
    apply mul_le_mul_of_nonneg_right hcoeff
    exact Real.rpow_nonneg (by positivity) _
  · intro x z
    constructor
    · exact (mul_le_mul_of_nonneg_right hlower (Finset.sum_nonneg fun i _ => sq_nonneg (z i))).trans
        (paperFrozenPhysicalMatrix_lower p hs n m U θ h hh b D x z)
    · exact (hupper p hs n m U hv hN hhalf h hh b D hD x z).trans
        (mul_le_mul_of_nonneg_right hphysical (Finset.sum_nonneg fun i _ => sq_nonneg (z i)))
  · intro x hx
    obtain ⟨hr,hc⟩ := paper_boundary_schur_bounds p hs n m U h D hD x hx
    refine ⟨fun i => (hr i).trans hbound, fun j => (hc j).trans hbound, ?_⟩
    intro i j hj
    apply (paper_boundary_bulk_entries p hs n m U h D hD x hx i j hj).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hn0.le _)
    calc
      _ = (K * A) * (n : ℝ) ^ (κ * h) := by dsimp only [K, D]; ring
      _ ≤ (K * A) * (n : ℝ) ^ (q * h) := mul_le_mul_of_nonneg_left hpowκ (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hCk (Real.rpow_nonneg hn0.le _)

open ConditionalScores


end Riesz2.DecayShort
