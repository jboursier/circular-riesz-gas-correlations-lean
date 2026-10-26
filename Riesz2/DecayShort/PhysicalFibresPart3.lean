/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.IntervalCoefficientsPart2
public import Riesz2.DecayShort.PhysicalFibresPart2

/-!
# Higher physical fibre moments

See Subsection 4.5 of the paper: inverse powers of arbitrary order at every retained
point, using the actual physical energy and the conditional probability.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ContDiff
namespace Riesz2.DecayShort.PhysicalFibres

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 4.5 of the paper, fixed-fibre input: every inverse coordinate
power is integrable at every interior retained point, including point fibres.
No almost-everywhere choice of a conditional expectation is involved. -/
theorem integrable_coordinate_inverse_power (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (a : Fin (n + m + 1)) (u : ℝ) (hu : 0 < u) :
    Integrable (fun z => ((configuration n m σ x z).val a) ^ (-u))
      (measure p n m hn σ x) := by
  obtain ⟨W, _, hv, hmom⟩ :=
    ConditionalEnergyMoments.physical_chart_energy_moments p n m hn
  obtain ⟨C₀, _, hlower⟩ := ConditionalEnergyMoments.physical_inverse_gap_bound
    p (n + m).succPNat (by simp only [Nat.succPNat_coe]; omega)
  let c := fun z => (configuration n m σ x z).val
  let U := fun z => p.val.1 * W (c z)
  let μ := measure p n m hn σ x
  let r := u / p.val.2
  have hr : 0 < r := div_pos hu p.property.2.1
  obtain ⟨z₀, hz₀, hmin, _, _, hp⟩ := hmom σ x
  let b := p.val.1 * W (RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ (x.val, z₀)) + C₀
  let w := fun z => U z -
    p.val.1 * W (RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ (x.val, z₀))
  have hsimplex := configuration_mem_simplex n m σ x
  have hlow (z) : 0 ≤ U z + C₀ ∧ ∀ j, (c z j) ^ (-p.val.2) ≤
      (U z + C₀) / (2 * p.val.1) := by
    have ht := hlower (c z) (hsimplex z)
    dsimp only at ht
    rwa [← hv ⟨c z, PhysicalEnergy.simplex_subset_ambient _ _ (hsimplex z)⟩] at ht
  have hb : 0 ≤ b := by
    have hs := (RetainedSimplex.chart_mem_simplex n m _ σ _).mpr
      ((Set.ext_iff.mp (RetainedSimplex.fibre_domain n m _ x.property) z₀).mpr hz₀)
    have hs' : WithLp.ofLp (RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ
        (x.val,z₀)) ∈ Riesz1.gapSimplex (n + m).succPNat :=
      ⟨hs.1, by simpa only [Nat.succPNat_coe, Nat.cast_succ] using hs.2⟩
    have ht := (hlower _ hs').1
    change 0 ≤ p.val.1 * physicalAmbientGapEnergy p (n + m).succPNat
      ⟨_, PhysicalEnergy.simplex_subset_ambient _ _ hs'⟩ + C₀ at ht
    rwa [← hv ⟨_, PhysicalEnergy.simplex_subset_ambient _ _ hs'⟩] at ht
  have hw (z) : 0 ≤ w z := by
    have hz := (configuration_mem_simplex n m σ x z)
    have hm := hmin z.property
    exact sub_nonneg.mpr hm
  have hi : Integrable (fun z => w z ^ r) μ := by
    have hi := (hp r hr).1
    rw [← map_measure p n m hn σ x] at hi
    exact hi.comp_measurable measurable_subtype_coe
  have hμ : IsProbabilityMeasure μ := measure_probability p n m hn σ x
  let A := (2 : ℝ) ^ r / (2 * p.val.1) ^ r
  have hmajor : Integrable (fun z => A * (w z ^ r + b ^ r)) μ :=
    (hi.add (integrable_const _)).const_mul A
  have hmeas : Measurable (fun z => (c z a) ^ (-u)) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) a).continuous.comp
      ((continuous_configuration n m σ x).subtype_val)).measurable.pow_const _
  apply hmajor.mono' hmeas.aestronglyMeasurable
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ((hsimplex z).1 a).le _)]
  have hβ := p.property.1
  have hex : -p.val.2 * r = -u := by dsimp [r]; field_simp [ne_of_gt p.property.2.1]
  calc
    _ = ((c z a) ^ (-p.val.2)) ^ r := by
      rw [← Real.rpow_mul ((hsimplex z).1 a).le, hex]
    _ ≤ ((U z + C₀) / (2 * p.val.1)) ^ r :=
      Real.rpow_le_rpow (Real.rpow_nonneg ((hsimplex z).1 a).le _) ((hlow z).2 a) hr.le
    _ = (w z + b) ^ r / (2 * p.val.1) ^ r := by
      rw [Real.div_rpow (hlow z).1 (by linarith [p.property.1])]
      congr 2
      dsimp [w, b]
      ring
    _ ≤ (2 ^ r * (w z ^ r + b ^ r)) / (2 * p.val.1) ^ r :=
      div_le_div_of_nonneg_right
        (by
          have hdom : w z + b ≤ 2 * max (w z) b := by
            linarith [le_max_left (w z) b, le_max_right (w z) b]
          calc
            _ ≤ (2 * max (w z) b) ^ r := Real.rpow_le_rpow (add_nonneg (hw z) hb) hdom hr.le
            _ = 2 ^ r * max (w z ^ r) (b ^ r) := by
              rw [Real.mul_rpow (by norm_num) (le_max_of_le_left (hw z)),
                Real.rpow_max (hw z) hb hr.le]
            _ ≤ _ := mul_le_mul_of_nonneg_left
              (max_le (by linarith [Real.rpow_nonneg hb r])
                (by linarith [Real.rpow_nonneg (hw z) r])) (by positivity))
        (by positivity)
    _ = _ := by dsimp [A]; ring


set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 4.5 of the paper, fixed-fibre input: each physical interval
coefficient is square integrable, at every retained point. -/
theorem memLp_intervalWeight_two (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (t : Fin (n + m + 1) × Fin ((n + m + 1) / 2)) :
    MemLp (fun z => intervalWeight p (n + m).succPNat t
      (configuration n m σ x z)) 2 (measure p n m hn σ x) := by
  have hs := configuration_mem_simplex n m σ x
  have hmeas (a : Fin (n + m + 1)) :
      Measurable (fun z => ((configuration n m σ x z).val a) ^ (-p.val.2 - 2)) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) a).continuous.comp
      (continuous_configuration n m σ x).subtype_val).measurable.pow_const _
  have hi (a : Fin (n + m + 1)) :
      MemLp (fun z => ((configuration n m σ x z).val a) ^ (-p.val.2 - 2)) 2
        (measure p n m hn σ x) := by
    apply (memLp_two_iff_integrable_sq (hmeas a).aestronglyMeasurable).mpr
    have hi := integrable_coordinate_inverse_power p n m hn σ x a (2 * (p.val.2 + 2))
      (by linarith [p.property.2.1])
    apply hi.congr
    apply ae_of_all
    intro z
    dsimp only
    rw [← Real.rpow_two, ← Real.rpow_mul ((hs z).1 a).le]
    congr 1
    ring
  have hb : MemLp (fun z => 2 * PhysicalEnergy.coefficientConstant p.val.2 p.property.2.1 *
      ∑ a, ((configuration n m σ x z).val a) ^ (-p.val.2 - 2)) 2
        (measure p n m hn σ x) :=
    (memLp_finsetSum _ (fun a _ => hi a)).const_mul _
  apply hb.mono' ((measurable_intervalWeight p (n + m).succPNat t).comp
    (continuous_configuration n m σ x).measurable).aestronglyMeasurable
  apply ae_of_all
  intro z
  dsimp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_pos (intervalWeight_pos p _ _ _)]
  exact intervalWeight_le_inverseSum p (n + m).succPNat t _ (hs z)

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 4.5 of the paper, fixed-fibre input: a smooth realization of the
ambient energy has square-integrable Hessian entries in all ambient
directions, including exterior labels, at every retained point. -/
theorem ambient_hessian_square_integrable (p : Parameters) (n m : ℕ) (hn : 1 ≤ n) :
    ∃ W : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain (n + m).succPNat) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
          y ∈ gapAmbientDomain (n + m).succPNat},
        W y.val = physicalAmbientGapEnergy p (n + m).succPNat y) ∧
      ∀ (σ : Equiv.Perm (Fin (n + m + 1)))
        (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (a b : Fin (n + m + 1)),
        Integrable (fun z => (fderiv ℝ (fderiv ℝ W) (configuration n m σ x z).val
          (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)) ^ 2)
          (measure p n m hn σ x) := by
  classical
  obtain ⟨W, hW, hv, hj⟩ := PhysicalEnergy.ambient_derivatives p (n + m).succPNat
  change (EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ) at W
  simp only [Nat.succPNat_coe] at hW hv hj
  refine ⟨W, hW, hv, fun σ x a b => ?_⟩
  have hg (i : Fin (n + m + 1)) (r : ℕ) (hr : r ≤ n + m + 1)
      (j : Fin (n + m + 1)) :
      cyclicGapSum (n + m).succPNat i r (WithLp.ofLp (EuclideanSpace.single j (1 : ℝ))) =
        if j ∈ cyclicIndexInterval (n + m).succPNat i r then 1 else 0 := by
    convert cyclicGapSum_single (n + m).succPNat i j hr using 1
    congr 1
    ext k
    simp [EuclideanSpace.single, PiLp.single_apply, eq_comm]
  let K := fun t : Fin (n + m + 1) × Fin ((n + m + 1) / 2) =>
    (if a ∈ cyclicIndexInterval (n + m).succPNat t.1 (t.2.val + 1) then (1 : ℝ) else 0) *
      (if b ∈ cyclicIndexInterval (n + m).succPNat t.1 (t.2.val + 1) then 1 else 0)
  have he : (fun z => fderiv ℝ (fderiv ℝ W) (configuration n m σ x z).val
      (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)) =
      fun z => ∑ t, intervalWeight p (n + m).succPNat t (configuration n m σ x z) * K t := by
    funext z
    rw [show fderiv ℝ (fderiv ℝ W) _ _ _ = _ from (hj _ _ _).2, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro r _
    rw [hg i _ (by have := r.isLt; omega), hg i _ (by have := r.isLt; omega)]
    rfl
  have hm : MemLp (fun z => fderiv ℝ (fderiv ℝ W) (configuration n m σ x z).val
      (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)) 2
        (measure p n m hn σ x) := by
    rw [he]
    exact memLp_finsetSum _ (fun t _ => (memLp_intervalWeight_two p n m hn σ x t).mul_const _)
  exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mp hm

set_option backward.isDefEq.respectTransparency false in
/-- Finiteness of the conditional exterior gradient energy in Subsection 4.5
at every retained point. The realization is smooth and agrees with the
physical energy throughout its ambient carrier. -/
theorem exterior_gradient_energy_finite (p : Parameters) (n m : ℕ) (hn : 1 ≤ n) :
    ∃ W : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain (n + m).succPNat) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
          y ∈ gapAmbientDomain (n + m).succPNat},
        W y.val = physicalAmbientGapEnergy p (n + m).succPNat y) ∧
      ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (i : Fin n),
        let V := fun z => ∑ a : Fin (n + m + 1), if n ≤ a.val then
          ((configuration n m (Equiv.refl _) x z).val a) ^ (p.val.2 + 2) *
            (fderiv ℝ (fderiv ℝ W) (configuration n m (Equiv.refl _) x z).val
              (EuclideanSpace.single (Fin.castLE (by omega) i) 1)
              (EuclideanSpace.single a 1)) ^ 2 else 0
        Integrable V (measure p n m hn (Equiv.refl _) x) ∧
          (∫⁻ z, ENNReal.ofReal (V z) ∂measure p n m hn (Equiv.refl _) x) < ⊤ := by
  classical
  obtain ⟨W, hW, hv, hsq⟩ := ambient_hessian_square_integrable p n m hn
  refine ⟨W, hW, hv, fun x i => ?_⟩
  intro V
  let c := fun z => (configuration n m (Equiv.refl _) x z).val
  have hs := configuration_mem_simplex n m (Equiv.refl _) x
  have hi (a : Fin (n + m + 1)) : Integrable (fun z =>
      (c z a) ^ (p.val.2 + 2) * (fderiv ℝ (fderiv ℝ W) (c z)
        (EuclideanSpace.single (Fin.castLE (by omega) i) 1)
        (EuclideanSpace.single a 1)) ^ 2) (measure p n m hn (Equiv.refl _) x) := by
    let f := fun z => (fderiv ℝ (fderiv ℝ W) (c z)
      (EuclideanSpace.single (Fin.castLE (by omega) i) 1) (EuclideanSpace.single a 1)) ^ 2
    have hf := hsq (Equiv.refl _) x (Fin.castLE (by omega) i) a
    have hm : Measurable (fun z => (c z a) ^ (p.val.2 + 2)) :=
      ((EuclideanSpace.proj (𝕜 := ℝ) a).continuous.comp
        (continuous_configuration n m (Equiv.refl _) x).subtype_val).measurable.pow_const _
    apply (hf.const_mul (((n + m + 1 : ℕ) : ℝ) ^ (p.val.2 + 2))).mono'
      (hm.aestronglyMeasurable.mul hf.aestronglyMeasurable)
    apply ae_of_all
    intro z
    have hle : c z a ≤ ((n + m + 1 : ℕ) : ℝ) := by
      have hh := (Finset.single_le_sum (s := Finset.univ)
        (fun j _ => ((hs z).1 j).le) (Finset.mem_univ a)).trans_eq (hs z).2
      exact hh
    dsimp only [Pi.mul_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (Real.rpow_nonneg ((hs z).1 a).le _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow ((hs z).1 a).le hle (by linarith [p.property.2.1])) (sq_nonneg _)
  have hV : Integrable V (measure p n m hn (Equiv.refl _) x) := by
    apply integrable_finsetSum
    intro a _
    split_ifs
    · exact hi a
    · exact integrable_zero _ _ _
  refine ⟨hV, ?_⟩
  have hnn : ∀ z, 0 ≤ V z := by
    intro z
    apply Finset.sum_nonneg
    intro a _
    split_ifs
    · exact mul_nonneg (Real.rpow_nonneg ((hs z).1 a).le _) (sq_nonneg _)
    · exact le_rfl
  rw [← ofReal_integral_eq_lintegral_ofReal hV (ae_of_all _ hnn)]
  exact ENNReal.ofReal_lt_top

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 4.4 and Subsection 4.5 of the paper: the full ambient conditional
interval matrix is the mean actual Hessian, including exterior indices.
Finite contractions of this identity identify the `b_i` and `c` formulas. -/
theorem ambient_hessian_conditional_entries (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    :
    ∃ W : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain (n + m).succPNat) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
          y ∈ gapAmbientDomain (n + m).succPNat},
        W y.val = physicalAmbientGapEnergy p (n + m).succPNat y) ∧
      ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (i j : Fin (n + m + 1)),
        let f := fun z => fderiv ℝ (fderiv ℝ W)
          (PhysicalFibres.configuration n m (Equiv.refl _) x z).val
          (EuclideanSpace.single (i) 1)
          (EuclideanSpace.single (j) 1)
        Integrable f (PhysicalFibres.measure p n m hn (Equiv.refl _) x) ∧
          (∫ z, f z ∂PhysicalFibres.measure p n m hn (Equiv.refl _) x) =
            IntervalBoundary.intervalMatrix (n + m).succPNat (n + m + 1) le_rfl
              (conditionalIntervalWeight p n m hn (Equiv.refl _) x) i j := by
  classical
  have gapSum_single (N : ℕ+) (a b : Fin (N : ℕ)) (r : ℕ) (hr : r ≤ (N : ℕ)) :
      cyclicGapSum N a r (WithLp.ofLp (EuclideanSpace.single b (1 : ℝ))) =
        if b ∈ cyclicIndexInterval N a r then 1 else 0 := by
    convert cyclicGapSum_single N a b hr using 1
    congr 1
    ext j
    simp [EuclideanSpace.single, PiLp.single_apply, eq_comm]
  obtain ⟨W, hW, hv, hj⟩ := PhysicalEnergy.ambient_derivatives p (n + m).succPNat
  change (EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ) at W
  simp only [Nat.succPNat_coe] at hW hv hj
  refine ⟨W, hW, hv, fun x i j => ?_⟩
  dsimp only
  let f := fun z => fderiv ℝ (fderiv ℝ W)
    (PhysicalFibres.configuration n m (Equiv.refl _) x z).val
    (EuclideanSpace.single (i) 1)
    (EuclideanSpace.single (j) 1)
  let K : (Fin (n + m + 1) × Fin ((n + m + 1) / 2)) → ℝ := fun t =>
    IntervalBoundary.rankOne
      (IntervalBoundary.trace (n + m).succPNat (n + m + 1) le_rfl t.1 (t.2.val + 1)) i j
  have he : f = fun z => ∑ t : Fin (n + m + 1) × Fin ((n + m + 1) / 2),
      intervalWeight p (n + m).succPNat t
        (PhysicalFibres.configuration n m (Equiv.refl _) x z) * K t := by
    funext z
    rw [show f z = _ from (hj _ _ _).2, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro r _
    rw [gapSum_single (n + m).succPNat a _ _ (Nat.le_trans (Nat.succ_le_of_lt r.isLt) (Nat.div_le_self _ _)),
      gapSum_single (n + m).succPNat a _ _ (Nat.le_trans (Nat.succ_le_of_lt r.isLt) (Nat.div_le_self _ _))]
    dsimp only [intervalWeight, K, IntervalBoundary.rankOne, IntervalBoundary.trace]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hii : Fin.castLE (le_rfl : n + m + 1 ≤ n + m + 1) i = i := Fin.ext rfl
    have hjj : Fin.castLE (le_rfl : n + m + 1 ≤ n + m + 1) j = j := Fin.ext rfl
    rw [hii, hjj]
    by_cases hi : i ∈ cyclicIndexInterval (n + m).succPNat a (r.val + 1) <;>
      by_cases hj : j ∈ cyclicIndexInterval (n + m).succPNat a (r.val + 1) <;>
      simp [hi, hj]
  have hg (t : Fin (n + m + 1) × Fin ((n + m + 1) / 2)) :
      Integrable (fun z => intervalWeight p (n + m).succPNat t
        (PhysicalFibres.configuration n m (Equiv.refl _) x z) * K t)
          (PhysicalFibres.measure p n m hn (Equiv.refl _) x) :=
    (integrable_intervalWeight p n m hn (Equiv.refl _) x t).mul_const _
  refine ⟨?_, ?_⟩
  · change Integrable f _
    rw [he]
    exact integrable_finsetSum _ (fun t _ => hg t)
  · change (∫ z, f z ∂_) = _
    rw [he, integral_finsetSum _ (fun t _ => hg t)]
    simp only [integral_mul_const, conditionalIntervalWeight, IntervalBoundary.intervalMatrix, K]
    rfl

end Riesz2.DecayShort.PhysicalFibres
