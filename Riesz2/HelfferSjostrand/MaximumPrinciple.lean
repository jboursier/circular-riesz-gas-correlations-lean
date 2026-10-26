/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.VectorRadialCompositionPart4
public import Riesz2.Frozen.WeightedWeakSolution
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Maximum principle for vector closed-form equations

The radial test works in the matrix-energy domain on any fixed
component subspace. The finite-radius estimate implies the extended essential
supremum estimate, including sources with infinite essential supremum.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2.MaximumPrinciple

/-- Internal quadratic comparison for the radial test in
Proposition 3.6. -/
theorem Internal.radial_residual_lower {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) (c : ℝ) (R : ℝ≥0)
    (hM : ∀ z : ι → ℝ, c * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M i j * z j)
    (z v : EuclideanSpace ℝ ι) (hv : ‖v‖ ≤ c * R) :
    c * ‖VectorRadial.truncate R z‖ ^ 2 ≤
      (∑ i, ∑ j, z i * M i j * VectorRadial.truncate R z j) -
        ∑ i, v i * VectorRadial.truncate R z i := by
  have hq := mul_le_mul_of_nonneg_left (hM z.ofLp)
    (VectorRadial.coefficient_nonneg R z)
  have hi := VectorRadial.inner_source_truncate_lower R c z v hv
  have he : inner ℝ (c • z) (VectorRadial.truncate R z) =
      VectorRadial.coefficient R z * (c * ∑ i, z i ^ 2) := by
    simp only [PiLp.inner_apply, Real.inner_apply, VectorRadial.truncate,
      PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hm : (∑ i, ∑ j, z i * M i j * VectorRadial.truncate R z j) =
      VectorRadial.coefficient R z * (∑ i, ∑ j, z i * M i j * z j) := by
    simp only [VectorRadial.truncate, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [inner_sub_left, he] at hi
  rw [hm]
  have hvh : inner ℝ v (VectorRadial.truncate R z) =
      ∑ i, v i * VectorRadial.truncate R z i := by
    simp only [PiLp.inner_apply, Real.inner_apply]
  rw [hvh] at hi
  exact hi.trans (sub_le_sub_right hq _)

/-- Internal residual argument of Proposition 3.6 of the paper.
An admissible radial test with nonnegative diffusion pairing forces its excess
to vanish. Both the abstract and weak-chain-rule constructions use this step. -/
theorem Internal.bound_of_admissible_radial_test {α ι : Type*}
    [MeasurableSpace α] [Fintype ι] {ρ : Measure α}
    (Q : ScalarFormData ρ) (M : α → Matrix ι ι ℝ)
    (c : ℝ) (hc : 0 < c)
    (hM : ∀ᵐ x ∂ρ, (∀ i j, M x i j = M x j i) ∧
      ∀ z : ι → ℝ, c * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j)
    (S : Submodule ℝ (ι → ℝ)) (v : ι → Lp ℝ 2 ρ) (u : ι → Q.1)
    (hu : WeightedWeakSolution Q M S v u) (R : ℝ≥0)
    (hv : ∀ᵐ x ∂ρ,
      ‖(WithLp.toLp 2 (fun i => v i x) : EuclideanSpace ℝ ι)‖ ≤ c * R)
    (h : ι → Q.1)
    (hh : ∀ i, (h i).val = VectorRadial.truncateValues R (fun j => (u j).val) i)
    (hdom : WeightedFormDomain Q M S h) (hpos : 0 ≤ ∑ i, Q.2 (u i) (h i)) :
    ∀ᵐ x ∂ρ, ‖(WithLp.toLp 2 (fun i => (u i).val x) :
      EuclideanSpace ℝ ι)‖ ≤ R := by
  classical
  obtain ⟨hcross, heq⟩ := hu.2 h hdom
  let F : α → ℝ := fun x =>
    matrixFieldPair M (fun i => (u i).val) (fun i => (h i).val) x -
      ∑ i, v i x * (h i).val x
  have hprod (i : ι) : Integrable (fun x => v i x * (h i).val x) ρ :=
    (Lp.memLp _).integrable_mul (Lp.memLp _)
  have hF : Integrable F ρ := hcross.sub (integrable_finsetSum _ (fun i _ => hprod i))
  have hrep : ∀ᵐ x ∂ρ,
      (WithLp.toLp 2 (fun i => (h i).val x) : EuclideanSpace ℝ ι) =
        VectorRadial.truncate R (WithLp.toLp 2 (fun i => (u i).val x)) := by
    filter_upwards [VectorRadial.truncateValues_ae R (fun i => (u i).val)] with x hx
    ext i
    simpa only [hh, VectorRadial.truncate, PiLp.smul_apply, smul_eq_mul] using hx i
  have hlower : ∀ᵐ x ∂ρ,
      c * ‖(WithLp.toLp 2 (fun i => (h i).val x) : EuclideanSpace ℝ ι)‖ ^ 2 ≤ F x := by
    filter_upwards [hM, hv, hrep] with x hx hvx hhx
    have hi := Internal.radial_residual_lower (M x) c R hx.2
      (WithLp.toLp 2 (fun i => (u i).val x))
      (WithLp.toLp 2 (fun i => v i x)) hvx
    change _ ≤ matrixFieldPair M _ _ x - _
    rw [← hhx] at hi
    exact hi
  have hnonneg : ∀ᵐ x ∂ρ, 0 ≤ F x := hlower.mono (fun x hx =>
    (mul_nonneg hc.le (sq_nonneg _)).trans hx)
  have hsource : (∫ x, (∑ i, v i x * (h i).val x) ∂ρ) =
      ∑ i, inner ℝ (v i) (h i).val := by
    rw [integral_finsetSum _ (fun i _ => hprod i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [L2.inner_def]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by simp only [Real.inner_apply])
  have hzero : ∫ x, F x ∂ρ = 0 := by
    have he : (∫ x, F x ∂ρ) = -(∑ i, Q.2 (u i) (h i)) := by
      rw [show (∫ x, F x ∂ρ) =
        (∫ x, matrixFieldPair M (fun i => (u i).val) (fun i => (h i).val) x ∂ρ) -
        ∫ x, (∑ i, v i x * (h i).val x) ∂ρ from
        integral_sub hcross (integrable_finsetSum _ (fun i _ => hprod i)), hsource]
      linarith
    have hp := integral_nonneg_of_ae hnonneg
    linarith
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnonneg hF).mp hzero
  filter_upwards [hz, hlower, hrep] with x hzx hlx hhx
  have hn : ‖(WithLp.toLp 2 (fun i => (h i).val x) : EuclideanSpace ℝ ι)‖ = 0 := by
    have hs : ‖(WithLp.toLp 2 (fun i => (h i).val x) : EuclideanSpace ℝ ι)‖ ^ 2 ≤ 0 := by
      rw [hzx] at hlx
      exact nonpos_of_mul_nonpos_right hlx hc
    nlinarith [norm_nonneg (WithLp.toLp 2 (fun i => (h i).val x) : EuclideanSpace ℝ ι)]
  rw [hhx, VectorRadial.norm_truncate] at hn
  have := le_max_right 0
    (‖(WithLp.toLp 2 (fun i => (u i).val x) : EuclideanSpace ℝ ι)‖ - R)
  linarith

/-- Internal finite-radius form of Proposition 3.6: a source
bounded by `c R` gives a solution bounded by `R`. Tests stay in the given fixed
subspace. No projection into an unbounded matrix domain is used. -/
theorem Internal.bound_of_source_bound {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {ρ : Measure α} (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q)
    (M : α → Matrix ι ι ℝ) (hMmeas : ∀ i j, Measurable (fun x => M x i j))
    (c : ℝ) (hc : 0 < c)
    (hM : ∀ᵐ x ∂ρ, (∀ i j, M x i j = M x j i) ∧
      ∀ z : ι → ℝ, c * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j)
    (S : Submodule ℝ (ι → ℝ)) (v : ι → Lp ℝ 2 ρ) (u : ι → Q.1)
    (hu : WeightedWeakSolution Q M S v u) (R : ℝ≥0)
    (hv : ∀ᵐ x ∂ρ,
      ‖(WithLp.toLp 2 (fun i => v i x) : EuclideanSpace ℝ ι)‖ ≤ c * R) :
    ∀ᵐ x ∂ρ, ‖(WithLp.toLp 2 (fun i => (u i).val x) :
      EuclideanSpace ℝ ι)‖ ≤ R := by
  classical
  have hpsd : ∀ᵐ x ∂ρ, (M x).PosSemidef := by
    filter_upwards [hM] with x hx
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    refine ⟨?_, fun z => ?_⟩
    · ext i j
      exact hx.1 j i
    · have hp : 0 ≤ c * ∑ i, z i ^ 2 :=
        mul_nonneg hc.le (Finset.sum_nonneg (fun i _ => sq_nonneg _))
      have := hp.trans (hx.2 z)
      simpa only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum, mul_assoc]
        using this
  obtain ⟨h, hh, hdom, hpos, _⟩ :=
    VectorRadial.admissible_truncation Q hQ R u M S hMmeas hpsd hu.1
  exact Internal.bound_of_admissible_radial_test Q M c hc hM S v u hu R hv
    h hh hdom hpos

end Riesz2.MaximumPrinciple

namespace Riesz2

/-- See Proposition 3.6 of the paper: the maximum principle,
with Euclidean essential suprema, arbitrary fixed component subspaces and
possibly unbounded sources. -/
theorem maximumPrinciple_closedForm :
  ∀ (d : ℕ) (ρ : Measure (EuclideanSpace ℝ (Fin d))),
    IsProbabilityMeasure ρ → ∀ Q : ScalarFormData ρ,
    IsClosedScalarDirichletForm Q →
    ∀ (m : ℕ+) (M : EuclideanSpace ℝ (Fin d) → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ),
      (∀ i j, Measurable (fun x => M x i j)) → ∀ c : ℝ, 0 < c →
      (∀ᵐ x ∂ρ, (∀ i j, M x i j = M x j i) ∧
        ∀ z : Fin (m : ℕ) → ℝ,
          c * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j) →
      ∀ (S : Submodule ℝ (Fin (m : ℕ) → ℝ)) (v : Fin (m : ℕ) → Lp ℝ 2 ρ)
        (u : Fin (m : ℕ) → Q.1),
        WeightedWeakSolution Q M S v u →
        eLpNorm (fun x => WithLp.toLp 2 (fun i => (u i).val x)) ∞ ρ ≤
          ENNReal.ofReal c⁻¹ * eLpNorm (fun x => WithLp.toLp 2 (fun i => v i x)) ∞ ρ := by
  intro d ρ _ Q hQ m M hMmeas c hc hM S v u hu
  let V := fun x => (WithLp.toLp 2 (fun i => v i x) : EuclideanSpace ℝ (Fin (m : ℕ)))
  let U := fun x => (WithLp.toLp 2 (fun i => (u i).val x) :
    EuclideanSpace ℝ (Fin (m : ℕ)))
  have hVm : AEStronglyMeasurable V ρ := (VectorRadial.memLp_values v).aestronglyMeasurable
  have hUm : AEStronglyMeasurable U ρ :=
    (VectorRadial.memLp_values (fun i => (u i).val)).aestronglyMeasurable
  change eLpNorm U ∞ ρ ≤ ENNReal.ofReal c⁻¹ * eLpNorm V ∞ ρ
  by_cases htop : eLpNorm V ∞ ρ = ⊤
  · rw [htop, ENNReal.mul_top (by positivity)]
    exact le_top
  let B : ℝ := (eLpNorm V ∞ ρ).toReal
  let R : ℝ≥0 := ⟨c⁻¹ * B, mul_nonneg (inv_nonneg.mpr hc.le) ENNReal.toReal_nonneg⟩
  have hv : ∀ᵐ x ∂ρ, ‖V x‖ ≤ B := by
    have h := ae_le_eLpNormEssSup (f := V) (μ := ρ)
    rw [← eLpNorm_exponent_top hVm] at h
    filter_upwards [h] with x hx
    have ht := ENNReal.toReal_mono htop hx
    simpa only [enorm_eq_nnnorm, ENNReal.coe_toReal, coe_nnnorm, B] using ht
  have hvR : ∀ᵐ x ∂ρ, ‖V x‖ ≤ c * R := by
    have he : c * (R : ℝ) = B := by
      change c * (c⁻¹ * B) = B
      rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    simpa only [he] using hv
  have huR := MaximumPrinciple.Internal.bound_of_source_bound Q hQ M hMmeas c hc hM S v u hu R hvR
  calc
    eLpNorm U ∞ ρ = eLpNormEssSup U ρ := eLpNorm_exponent_top hUm
    _ ≤ ENNReal.ofReal R := eLpNormEssSup_le_of_ae_bound huR
    _ = ENNReal.ofReal c⁻¹ * eLpNorm V ∞ ρ := by
      change ENNReal.ofReal (c⁻¹ * B) = _
      rw [ENNReal.ofReal_mul (inv_nonneg.mpr hc.le), ENNReal.ofReal_toReal htop]

end Riesz2
