/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.IntervalCoefficientsPart4
public import Riesz1.ToMathlib.WeightedSobolev.L2Facts

/-!
# Exterior score weights and inverse-energy estimates

Deterministic and covariance estimates for Subsection 4.4.
The inverse-energy bounds apply to the ambient Hessian restricted
to any exterior tangent subspace.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators ContDiff

namespace Riesz2.DecayShort.ConditionalScores

/-- See Subsection 4.5 of the paper: distance of a zero-based active label to the exterior. -/
def boundaryDistance {n : ℕ} (i : Fin n) : ℕ := min (i.val + 1) (n - i.val)

/-- See Subsection 4.5 of the paper: the fixed score weight, independent of every probability law. -/
def weight (s : ℝ) {n : ℕ} (i : Fin n) : ℝ :=
  (boundaryDistance i : ℝ) ^ (-(s - 1 / 2))

theorem boundaryDistance_pos {n : ℕ} (i : Fin n) : 0 < boundaryDistance i := by
  unfold boundaryDistance
  omega

theorem weight_pos (s : ℝ) {n : ℕ} (i : Fin n) : 0 < weight s i :=
  Real.rpow_pos_of_pos (by exact_mod_cast boundaryDistance_pos i) _

/-- The square of the fixed weight is exactly the exterior-energy profile. -/
theorem weight_sq (s : ℝ) {n : ℕ} (i : Fin n) :
    weight s i ^ 2 = (boundaryDistance i : ℝ) ^ (1 - 2 * s) := by
  unfold weight
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  push_cast
  ring

/-- Boundary check for Subsection 4.5: the sole active score has weight one. -/
theorem weight_single (s : ℝ) (i : Fin 1) : weight s i = 1 := by
  simp [weight, boundaryDistance]

private theorem complete_square {a g v : ℝ} (ha : 0 < a) :
    2 * g * v - a * v ^ 2 ≤ g ^ 2 / a := by
  apply (le_div_iff₀ ha).mpr
  nlinarith [sq_nonneg (g - a * v)]

/-- Internal inverse-compression estimate used in Subsection 4.4.
The exterior tangent constraint can only decrease the variational inverse
energy. The estimate keeps all the prescribed gap weights. -/
theorem internal_diagonal_inverse_bound {k : ℕ} (s β : ℝ) (hs : 1 < s) (hβ : 0 < β)
    (y : Fin k → ℝ) (hy : ∀ a, 0 < y a) (g : Fin k → ℝ)
    (T : Submodule ℝ (EuclideanSpace ℝ (Fin k)))
    (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ)
    (hA : ∀ v : T, β * (2 * (s * (s + 1))) *
      (∑ a, (y a) ^ (-s - 2) * (v.val a) ^ 2) ≤ A v.val v.val) :
    sSup (Set.range fun v : T => 2 * (∑ a, g a * v.val a) - A v.val v.val) ≤
      (β * (2 * (s * (s + 1))))⁻¹ * ∑ a, (y a) ^ (s + 2) * (g a) ^ 2 := by
  have hα : 0 < β * (2 * (s * (s + 1))) := by positivity
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨v, rfl⟩
  calc
    _ ≤ 2 * (∑ a, g a * v.val a) - β * (2 * (s * (s + 1))) *
        (∑ a, (y a) ^ (-s - 2) * (v.val a) ^ 2) := sub_le_sub_left (hA v) _
    _ = ∑ a, (2 * g a * v.val a -
        (β * (2 * (s * (s + 1))) * (y a) ^ (-s - 2)) * (v.val a) ^ 2) := by
      simp only [Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro a _ <;> ring
    _ ≤ ∑ a, (g a) ^ 2 / (β * (2 * (s * (s + 1))) * (y a) ^ (-s - 2)) :=
      Finset.sum_le_sum fun a _ => complete_square (mul_pos hα (Real.rpow_pos_of_pos (hy a) _))
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [div_eq_mul_inv, mul_inv_rev, ← Real.rpow_neg (hy a).le]
      rw [show -(-s - 2) = s + 2 by ring]
      ring

/-- Internal compensation-score estimate used in Subsection 4.4.
For a positive symmetric Hessian the inverse energy of the differential
`v ↦ A(q,v)` on any tangent subspace is at most `A(q,q)`. -/
theorem internal_compensation_inverse_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (A : E →L[ℝ] E →L[ℝ] ℝ)
    (hA : ∀ v, 0 ≤ A v v) (hAs : ∀ u v, A u v = A v u)
    (T : Submodule ℝ E) (q : E) :
    sSup (Set.range fun v : T => 2 * A q v.val - A v.val v.val) ≤ A q q := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨v, rfl⟩
  have ht := hA (q - v.val)
  simp only [map_sub, sub_apply] at ht
  rw [hAs v.val q] at ht
  linarith

/-- The actual smooth physical Hessian has the doubled nearest-neighbour
lower bound needed by the two inverse estimates, at every positive fibre
point. -/
theorem physical_nearest_pair_bound (p : Parameters) (n m : ℕ) (_hn : 1 ≤ n)
    (hN : 3 ≤ n + m + 1) :
    ∃ W : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain (n + m).succPNat) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
          y ∈ gapAmbientDomain (n + m).succPNat},
        W y.val = physicalAmbientGapEnergy p (n + m).succPNat y) ∧
      ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
        (z : AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ i, x.val i))
        (v : EuclideanSpace ℝ (Fin (n + m + 1))),
        2 * (p.val.2 * (p.val.2 + 1)) *
          (∑ a, ((PhysicalFibres.configuration n m (Equiv.refl _) x z).val a) ^
            (-p.val.2 - 2) * (v a) ^ 2) ≤
          fderiv ℝ (fderiv ℝ W) (PhysicalFibres.configuration n m (Equiv.refl _) x z).val v v := by
  obtain ⟨_, _, W, hW, hv, _, _, _, hd, _⟩ :=
    PhysicalEnergy.restriction_and_derivatives p (n + m).succPNat (by simp; omega)
  refine ⟨W, hW, hv, fun x z v => ?_⟩
  exact hd _ (PhysicalFibres.configuration_mem_simplex n m (Equiv.refl _) x z) v hN

set_option backward.isDefEq.respectTransparency false in
/-- Fixed-fibre integrability input for Subsection 4.4.
Every ambient score of the physical energy is square integrable
at every retained point. In particular this includes every `Fᵢ`, the
uniform exterior score `G`, and their differences. The realization `U`
is beta times the energy. Its derivative is divided by beta.
This proves finite variances without assuming Sobolev membership. -/
theorem physical_scores_memLp_two (p : Parameters) (n m : ℕ) (hn : 1 ≤ n) :
    ∃ U : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain (n + m).succPNat) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
          y ∈ gapAmbientDomain (n + m).succPNat},
        U y.val = p.val.1 * physicalAmbientGapEnergy p (n + m).succPNat y) ∧
      ∀ (σ : Equiv.Perm (Fin (n + m + 1)))
        (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
        (v : EuclideanSpace ℝ (Fin (n + m + 1))),
        MemLp (fun z => p.val.1⁻¹ * fderiv ℝ U
          (PhysicalFibres.configuration n m σ x z).val v) 2
          (PhysicalFibres.measure p n m hn σ x) := by
  classical
  obtain ⟨U, hU, hv, ht⟩ := MarginalHessian.physical_energy_tensors p (n + m).succPNat
  change (EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ) at U
  simp only [Nat.succPNat_coe] at hU hv ht
  obtain ⟨C, hC, hbound⟩ := ht 1
  refine ⟨U, hU, hv, fun σ x v => ?_⟩
  let c := fun z => (PhysicalFibres.configuration n m σ x z).val
  let μ := PhysicalFibres.measure p n m hn σ x
  let r := 2 * (p.val.2 + 1)
  have hr : 0 < r := by dsimp [r]; linarith [p.property.2.1]
  have hci (a : Fin (n + m + 1)) : Integrable (fun z => (c z a) ^ (-r)) μ :=
    PhysicalFibres.integrable_coordinate_inverse_power p n m hn σ x a r hr
  have hmajor : Integrable (fun z => C ^ 2 * ‖v‖ ^ 2 * ∑ a, (c z a) ^ (-r)) μ :=
    (integrable_finsetSum Finset.univ (fun a _ => hci a)).const_mul _
  have hcf : Measurable (fun z => fderiv ℝ U (c z) v) :=
    (measurable_fderiv_apply_const ℝ U v).comp
      (PhysicalFibres.continuous_configuration n m σ x).subtype_val.measurable
  have hs := PhysicalFibres.configuration_mem_simplex n m σ x
  have hsq : Integrable (fun z => (fderiv ℝ U (c z) v) ^ 2) μ := by
    apply hmajor.mono' (hcf.pow_const 2).aestronglyMeasurable
    apply ae_of_all
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    obtain ⟨a, _, ha⟩ := Finset.exists_min_image Finset.univ (fun a => c z a)
      (Finset.univ_nonempty : (Finset.univ : Finset (Fin (n + m + 1))).Nonempty)
    have hδ : 0 < c z a := (hs z).1 a
    have hb := hbound (c z) (hs z) (c z a) hδ (fun b => ha b (Finset.mem_univ b))
    simp only [PNat.val_ofNat, Nat.cast_one, norm_iteratedFDeriv_one] at hb
    have he : ‖fderiv ℝ U (c z) v‖ ≤ C * (c z a) ^ (-p.val.2 - 1) * ‖v‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
    have he2 := pow_le_pow_left₀ (norm_nonneg _) he 2
    have hpow : ((c z a) ^ (-p.val.2 - 1)) ^ 2 = (c z a) ^ (-r) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
      congr 1
      dsimp [r]
      ring
    rw [Real.norm_eq_abs, sq_abs, mul_pow, mul_pow, hpow] at he2
    apply he2.trans
    have hsum : (c z a) ^ (-r) ≤ ∑ b, (c z b) ^ (-r) :=
      Finset.single_le_sum (fun b _ => Real.rpow_nonneg ((hs z).1 b).le _) (Finset.mem_univ a)
    nlinarith [mul_le_mul_of_nonneg_left hsum (mul_nonneg (sq_nonneg C) (sq_nonneg ‖v‖))]
  exact ((memLp_two_iff_integrable_sq hcf.aestronglyMeasurable).mpr hsq).const_mul _

section Covariance
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Internal Cauchy–Schwarz interface, with explicit second moments. -/
theorem internal_abs_covariance_le {F G : Ω → ℝ} (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    |ProbabilityTheory.covariance F G μ| ≤
      Real.sqrt (∫ z, (F z - ∫ y, F y ∂μ) ^ 2 ∂μ) *
        Real.sqrt (∫ z, (G z - ∫ y, G y ∂μ) ^ 2 ∂μ) := by
  exact Riesz1.WeightedSobolev.abs_integral_mul_le_sqrt
    (hF.sub (memLp_const _)) (hG.sub (memLp_const _))

/-- Internal consequence of variance bounds for Subsection 4.4.
The weights are the fixed weights from Subsection 4.5. This is a
conditional helper, not the physical Brascamp–Lieb theorem. -/
theorem internal_score_covariances {n : ℕ} (s C D N : ℝ) (hC : 0 ≤ C)
    (hD : 0 ≤ D) (hN : 0 < N) (F : Fin n → Ω → ℝ) (G : Ω → ℝ)
    (hF : ∀ i, MemLp (F i) 2 μ) (hG : MemLp G 2 μ)
    (hVF : ∀ i, (∫ z, (F i z - ∫ y, F i y ∂μ) ^ 2 ∂μ) ≤
      C * D * (boundaryDistance i : ℝ) ^ (1 - 2 * s))
    (hVG : (∫ z, (G z - ∫ y, G y ∂μ) ^ 2 ∂μ) ≤ C * D / N) :
    (∀ i j, |ProbabilityTheory.covariance (F i) (F j) μ| ≤
      C * D * weight s i * weight s j) ∧
    (∀ i, |ProbabilityTheory.covariance (F i) G μ| ≤
      C * D * N ^ (-(1 / 2 : ℝ)) * weight s i) := by
  have hCD : 0 ≤ C * D := mul_nonneg hC hD
  have hf (i) : Real.sqrt (∫ z, (F i z - ∫ y, F i y ∂μ) ^ 2 ∂μ) ≤
      Real.sqrt (C * D) * weight s i := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨mul_nonneg (Real.sqrt_nonneg _) (weight_pos s i).le, ?_⟩
    rw [mul_pow, Real.sq_sqrt hCD, weight_sq]
    exact hVF i
  have hg : Real.sqrt (∫ z, (G z - ∫ y, G y ∂μ) ^ 2 ∂μ) ≤
      Real.sqrt (C * D) * N ^ (-(1 / 2 : ℝ)) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt hCD, ← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    norm_num
    simpa only [Real.rpow_neg_one, div_eq_mul_inv] using hVG
  constructor
  · intro i j
    apply (internal_abs_covariance_le (hF i) (hF j)).trans
    have hb := mul_le_mul (hf i) (hf j) (Real.sqrt_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (weight_pos s i).le)
    apply hb.trans_eq
    calc
      _ = Real.sqrt (C * D) ^ 2 * weight s i * weight s j := by ring
      _ = _ := by rw [Real.sq_sqrt hCD]
  · intro i
    apply (internal_abs_covariance_le (hF i) hG).trans
    have hb := mul_le_mul (hf i) hg (Real.sqrt_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (weight_pos s i).le)
    apply hb.trans_eq
    calc
      _ = Real.sqrt (C * D) ^ 2 * N ^ (-(1 / 2 : ℝ)) * weight s i := by ring
      _ = _ := by rw [Real.sq_sqrt hCD]

end Covariance
end Riesz2.DecayShort.ConditionalScores
