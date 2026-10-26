/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.InterpolantLocalLawsPart8
public import Riesz2.HelfferSjostrand.PhysicalEnergy

/-!
# A finite-volume obstruction to uniform interpolation coefficients

For the exterior geometry of Subsection 6.1, the prefix and suffix conditions permit a
collapsing exterior cluster when `n = 2`, `N = 8`. The short-interval ambient extension
then has an unbounded coefficient from the image at the other end of the period.
-/

public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ContDiff

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.InterpolationCoefficients

/-- The six exterior gaps in the finite-volume example for Subsection 6.1. The four middle gaps form the collapsing cluster. -/
def collapsingExterior (ρ : ℝ) : EuclideanSpace ℝ (Fin 6) :=
  WithLp.toLp 2 ![3 - 2 * ρ, ρ, ρ, ρ, ρ, 3 - 2 * ρ]

/-- The complete eight-gap vector, with active gaps exactly equal to one. -/
def collapsingGaps (ρ : ℝ) : Fin 8 → ℝ :=
  ![1, 1, 3 - 2 * ρ, ρ, ρ, ρ, ρ, 3 - 2 * ρ]

/-- The exterior has the fixed residual active length two. -/
theorem collapsingExterior_sum (ρ : ℝ) :
    ∑ i, collapsingExterior ρ i = 6 := by
  simp [collapsingExterior, Fin.sum_univ_succ]
  ring

/-- Positivity holds for every member of the collapsing family. -/
theorem collapsingExterior_positive {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ ≤ 1 / 8) :
    ∀ i, 0 < collapsingExterior ρ i := by
  intro i
  fin_cases i <;> simp [collapsingExterior] <;> linarith

/-- The exterior lies in the same positive carrier used by admissibility. -/
theorem collapsingExterior_carrier {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ ≤ 1 / 8) :
    collapsingExterior ρ ∈ AffineSimplex.chartDomain 6 8 := by
  exact ⟨collapsingExterior_positive hρ hρ', by rw [collapsingExterior_sum]; norm_num⟩

/-- The actual positive mass-eight simplex contains this family. -/
theorem collapsingGaps_simplex {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ ≤ 1 / 8) :
    collapsingGaps ρ ∈ Riesz1.gapSimplex 8 := by
  change (∀ i : Fin 8, 0 < collapsingGaps ρ i) ∧
    (∑ i : Fin 8, collapsingGaps ρ i) = 8
  constructor
  · intro i
    fin_cases i <;> simp [collapsingGaps] <;> linarith
  · simp [collapsingGaps, Fin.sum_univ_succ]
    ring

/-- All prefix and suffix deviations are at most two, uniformly in the
collapsing parameter. -/
theorem collapsingExterior_rank_deviations {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ ≤ 1 / 8)
    (r : ℕ) (hr : 1 ≤ r) (hr' : r ≤ 6) :
    |(∑ i ∈ Finset.univ.filter (fun i : Fin 6 => i.val < r),
        collapsingExterior ρ i) - r| ≤ 2 ∧
    |(∑ i ∈ Finset.univ.filter (fun i : Fin 6 => 6 - r ≤ i.val),
        collapsingExterior ρ i) - r| ≤ 2 := by
  interval_cases r <;>
    norm_num [collapsingExterior, Finset.sum_filter, Fin.sum_univ_succ, abs_le] <;>
      (repeat' constructor) <;> linarith

/-- Finite-volume example for Subsection 6.1: every geometric condition of
Subsection 6.1 holds for this family, for every positive tolerance. -/
theorem collapsingExterior_geometry {ρ ε : ℝ} (hρ : 0 < ρ) (hρ' : ρ ≤ 1 / 8)
    (hε : 0 ≤ ε) :
    InterpolantLocalLaws.exteriorGeometry 2 ε 6 1 (collapsingExterior ρ) := by
  constructor
  · rw [collapsingExterior_sum]
    norm_num
    positivity
  · intro r hr hr'
    obtain ⟨hp, hs⟩ := collapsingExterior_rank_deviations hρ hρ' r hr hr'
    have h2 : 1 ≤ (2 : ℝ) ^ ε := Real.one_le_rpow (by norm_num) hε
    have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hrpow : 1 ≤ (r : ℝ) ^ (min (2 : ℝ) 1 / 2 + ε) :=
      Real.one_le_rpow hrR (by norm_num; linarith)
    have hbound : 2 ≤ 4 * (2 : ℝ) ^ ε * (r : ℝ) ^ (min (2 : ℝ) 1 / 2 + ε) := by
      nlinarith
    exact ⟨hp.trans hbound, hs.trans hbound⟩

/-- The active vector is in every positive-tolerance rigidity event. -/
theorem active_ones_good {η : ℝ} (hη : 0 ≤ η) :
    (fun _ : Fin 2 => (1 : ℝ)) ∈ goodBlockEvent 2 2 8 η := by
  refine ⟨by norm_num, ?_, ?_⟩
  · intro i
    exact ⟨Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith),
      Real.one_le_rpow (by norm_num) hη⟩
  · intro a b hab hb
    change b ≤ 2 at hb
    rw [Finset.sum_filter]
    change |(∑ i : Fin 2, if a ≤ i.val ∧ i.val < b then (1 : ℝ) else 0) -
      (b - a : ℕ)| ≤ _
    rw [Fin.sum_univ_two]
    interval_cases b <;> interval_cases a <;>
      norm_num [Fin.sum_univ_succ, Finset.sum_filter] <;> positivity

/-- The exceptional weight remains exactly three at the active vector. -/
theorem active_ones_weight :
    InterpolantLocalLaws.exceptionalWeight 2 (n := 2)
      (fun _ : Fin 2 => (1 : ℝ)) = 3 := by
  norm_num [InterpolantLocalLaws.exceptionalWeight]

/-- The antipodal interval beginning at the last exterior gap has length
arbitrarily close to the full period, although its rank is only four. -/
theorem collapsing_interval_length (ρ : ℝ) :
    cyclicGapSum 8 7 4 (collapsingGaps ρ) = 8 - 4 * ρ := by
  change (∑ a ∈ Finset.range 4, collapsingGaps ρ ⟨(7 + a) % 8, _⟩) = _
  norm_num [Finset.sum_range_succ, collapsingGaps, Fin.reduceFinMk]
  ring

/-- The complementary image gives a lower bound on the physical coefficient. -/
theorem intervalCoefficient_complement_lower (p : Parameters) (N : ℕ+)
    (L : {L : ℝ // 0 < L ∧ L < (N : ℝ)}) :
    p.val.2 * (p.val.2 + 1) * ((N : ℝ) - L.val) ^ (-p.val.2 - 2) ≤
      PhysicalEnergy.intervalCoefficient p N L := by
  rw [PhysicalEnergy.intervalCoefficient_images]
  have hs : 1 < p.val.2 + 2 := by linarith [p.property.2.1]
  have hδ : 0 < min L.val ((N : ℝ) - L.val) :=
    lt_min L.property.1 (sub_pos.mpr L.property.2)
  have hsum := (PeriodicPower.summable_and_le hs hδ
    (min_le_left _ _) (min_le_right _ _)).1
  have hterm := hsum.le_tsum (-1 : ℤ)
    (fun k _ => Real.rpow_nonneg (abs_nonneg (L.val + k * (N : ℝ))) (-(p.val.2 + 2)))
  have he : |L.val + (-1 : ℤ) * (N : ℝ)| = (N : ℝ) - L.val := by
    rw [Int.cast_neg, Int.cast_one, neg_one_mul,
      abs_of_neg (by linarith [L.property.2])]
    ring
  rw [he] at hterm
  simp only [show -(p.val.2 + 2) = -p.val.2 - 2 by ring] at hterm
  exact mul_le_mul_of_nonneg_left hterm (by have := p.property.2.1; positivity)

/-- Finite-volume example for Subsection 6.1: the interval coefficient in this
geometrically admissible family diverges at least as `6 (4ρ)⁻⁴` for `s=2`. -/
theorem collapsing_coefficient_lower (p : Parameters) (hs : p.val.2 = 2)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ ≤ 1 / 8) :
    6 * (4 * ρ) ^ (-(4 : ℝ)) ≤
      PhysicalEnergy.intervalCoefficient p 8
        ⟨8 - 4 * ρ, by change 0 < 8 - 4 * ρ ∧ 8 - 4 * ρ < 8; constructor <;> linarith⟩ := by
  have h := intervalCoefficient_complement_lower p 8
    ⟨8 - 4 * ρ, by change 0 < 8 - 4 * ρ ∧ 8 - 4 * ρ < 8; constructor <;> linarith⟩
  norm_num [hs, show (8 : ℝ) - (8 - 4 * ρ) = 4 * ρ by ring] at h ⊢
  exact h

/-- The coefficient blowup is unbounded, with a witness at fixed sizes.
This is a deterministic obstruction for Subsection 6.1. -/
theorem collapsing_coefficient_unbounded (p : Parameters) (hs : p.val.2 = 2)
    (B : ℝ) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ ≤ 1 / 8),
      B < PhysicalEnergy.intervalCoefficient p 8
        ⟨8 - 4 * ρ, by change 0 < 8 - 4 * ρ ∧ 8 - 4 * ρ < 8; constructor <;> linarith⟩ := by
  let a := |B| + 1
  have ha : 1 ≤ a := by dsimp only [a]; linarith [abs_nonneg B]
  have ha0 : 0 < a := by linarith
  let ρ := 1 / (8 * a)
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hρ' : ρ ≤ 1 / 8 := by
    dsimp only [ρ]
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  refine ⟨ρ, hρ, hρ', lt_of_lt_of_le ?_ (collapsing_coefficient_lower p hs hρ hρ')⟩
  have he : (4 * ρ) ^ (-(4 : ℝ)) = (2 * a) ^ 4 := by
    rw [Real.rpow_neg (by positivity), Real.rpow_ofNat]
    dsimp only [ρ]
    field_simp
    ring
  rw [he]
  have ha2 : a ≤ a ^ 2 := by nlinarith
  have ha4 : a ^ 2 ≤ a ^ 4 := by nlinarith [sq_nonneg (a ^ 2 - 1)]
  have hB : B < a := by dsimp only [a]; linarith [le_abs_self B]
  nlinarith

/-- The divergent coefficient occurs in the actual ambient Hessian of the
energy, in the first active coordinate. -/
theorem collapsing_ambient_hessian (p : Parameters) (hs : p.val.2 = 2) :
    ∃ W : EuclideanSpace ℝ (Fin 8) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain 8) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin 8) // y ∈ gapAmbientDomain 8},
        W y.val = physicalAmbientGapEnergy p 8 y) ∧
      ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 / 8 →
        let u : EuclideanSpace ℝ (Fin 8) := WithLp.toLp 2 (Pi.single 0 1)
        6 * (4 * ρ) ^ (-(4 : ℝ)) ≤
          fderiv ℝ (fderiv ℝ W) (WithLp.toLp 2 (collapsingGaps ρ)) u u := by
  obtain ⟨W, hWs, hWv, hd⟩ := PhysicalEnergy.ambient_derivatives p 8
  refine ⟨W, hWs, hWv, fun ρ hρ hρ' => ?_⟩
  let x : {y : EuclideanSpace ℝ (Fin 8) // y ∈ gapAmbientDomain 8} :=
    ⟨WithLp.toLp 2 (collapsingGaps ρ),
      PhysicalEnergy.simplex_subset_ambient 8 _ (collapsingGaps_simplex hρ hρ')⟩
  let u : EuclideanSpace ℝ (Fin 8) := WithLp.toLp 2 (Pi.single 0 1)
  change 6 * (4 * ρ) ^ (-(4 : ℝ)) ≤ fderiv ℝ (fderiv ℝ W) x.val u u
  rw [(hd x u u).2]
  let F := fun (i : Fin 8) (r : Fin 4) =>
    (2 - if 2 * (r.val + 1) = 8 then (1 : ℝ) else 0) *
      PhysicalEnergy.intervalCoefficient p 8
        ⟨cyclicGapSum 8 i (r.val + 1) (collapsingGaps ρ),
          x.property i (r.val + 1) (by omega) (by change r.val + 1 ≤ 8 / 2; omega)⟩ *
      (cyclicGapSum 8 i (r.val + 1) (WithLp.ofLp u)) ^ 2
  have hF (i : Fin 8) (r : Fin 4) : 0 ≤ F i r := by
    have hc := (PhysicalEnergy.intervalCoefficient_pos p 8
      ⟨cyclicGapSum 8 i (r.val + 1) (collapsingGaps ρ),
        x.property i (r.val + 1) (by omega) (by change r.val + 1 ≤ 8 / 2; omega)⟩).le
    dsimp only [F]
    split_ifs <;> norm_num only [sub_self, sub_zero, zero_mul, sub_eq_add_neg] <;> positivity
  have hsum : F 7 3 ≤ ∑ i, ∑ r, F i r :=
    (Finset.single_le_sum (fun r _ => hF 7 r) (Finset.mem_univ 3)).trans
      (Finset.single_le_sum
        (fun i _ => Finset.sum_nonneg (fun r _ => hF i r)) (Finset.mem_univ 7))
  have hselected : F 7 3 = PhysicalEnergy.intervalCoefficient p 8
      ⟨8 - 4 * ρ, by change 0 < 8 - 4 * ρ ∧ 8 - 4 * ρ < 8; constructor <;> linarith⟩ := by
    dsimp only [F]
    norm_num
    have hu : cyclicGapSum 8 7 4 (WithLp.ofLp u) = 1 := by
      change (∑ a ∈ Finset.range 4, (Pi.single 0 (1 : ℝ) : Fin 8 → ℝ)
        ⟨(7 + a) % 8, _⟩) = 1
      rw [show (4 : ℕ) = 3 + 1 from rfl, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
      norm_num [cyclicGapSum, Finset.sum_range_succ, u, Pi.single_apply]
    rw [hu, one_pow, mul_one]
    congr 1
    exact Subtype.ext (collapsing_interval_length ρ)
  apply (collapsing_coefficient_lower p hs hρ hρ').trans
  rw [← hselected]
  convert hsum using 1
  simp only [F, pow_two, x, PNat.val_ofNat]

end Riesz2.InterpolationCoefficients
