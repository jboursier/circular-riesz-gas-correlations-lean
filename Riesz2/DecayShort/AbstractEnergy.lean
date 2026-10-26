/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.CoerciveSolutionMaps
public import Riesz2.HelfferSjostrand.MaximumPrinciple
public import Riesz2.Frozen.IsConservativeScalarForm
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Abstract short-range energy

See the proof of Lemma 4.4 in the paper. The inverse is the existing coercive solution
map for the weak equation with matrix `β • M`. Bounded coefficients make its
natural matrix-energy domain the entire scalar form domain with the prescribed
component constraint. Component and base dimensions are independent, and the
component type may be empty. Restricting the tests to a fixed component subspace
expresses orthogonal compression of both matrix and source.

The helper estimates work for any closed scalar Dirichlet form. The main theorem
retains probability and conservativity from Assumptions 4.1.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set InnerProductSpace
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2.AbstractEnergy

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]
  {ρ : Measure α}

/-- Scaling the quadratic pairing introduces exactly one factor of β. -/
theorem matrixFieldPair_smul (β : ℝ) (M : α → Matrix ι ι ℝ)
    (u v : ι → Lp ℝ 2 ρ) (x : α) :
    matrixFieldPair (fun y => β • M y) u v x = β * matrixFieldPair M u v x := by
  simp only [matrixFieldPair, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Bounded nonnegative quadratic forms have finite energy on every Sobolev tuple.
This is the whole-domain bridge in Lemma 4.4. -/
theorem bounded_formDomain_iff (Q : ScalarFormData ρ)
    (M : α → Matrix ι ι ℝ) (hMmeas : ∀ i j, Measurable (fun x => M x i j))
    (b : ℝ)
    (hM : ∀ᵐ x ∂ρ, ∀ z : ι → ℝ,
      0 ≤ (∑ i, ∑ j, z i * M x i j * z j) ∧
      (∑ i, ∑ j, z i * M x i j * z j) ≤ b * ∑ i, z i ^ 2)
    (S : Submodule ℝ (ι → ℝ)) (u : ι → Q.1) :
    WeightedFormDomain Q M S u ↔ ∀ᵐ x ∂ρ, (fun i => (u i).val x) ∈ S := by
  classical
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  have hm : AEStronglyMeasurable
      (matrixFieldPair M (fun i => (u i).val) (fun i => (u i).val)) ρ := by
    unfold matrixFieldPair
    exact Finset.aestronglyMeasurable_fun_sum _ (fun i _ =>
      Finset.aestronglyMeasurable_fun_sum _ (fun j _ =>
        ((Lp.memLp (u i).val).aestronglyMeasurable.mul
          (hMmeas i j).aestronglyMeasurable).mul
          (Lp.memLp (u j).val).aestronglyMeasurable))
  apply ((integrable_finsetSum _ (fun i _ =>
    (Lp.memLp (u i).val).integrable_sq)).const_mul b).mono_nonneg hm
  · exact hM.mono (fun x hx => (hx (fun i => (u i).val x)).1)
  · exact hM.mono (fun x hx => (hx (fun i => (u i).val x)).2)

omit [Fintype ι] in
/-- Measurability is preserved by the physical temperature factor. -/
theorem scaled_measurable (β : ℝ) (M : α → Matrix ι ι ℝ)
    (hM : ∀ i j, Measurable (fun x => M x i j)) :
    ∀ i j, Measurable (fun x => (β • M x) i j) := by
  intro i j
  exact (hM i j).const_mul β

/-- The lower matrix bound, scaled by β, on any fixed component subspace. -/
theorem scaled_lower (β a : ℝ) (hβ : 0 ≤ β) (M : α → Matrix ι ι ℝ)
    (hM : ∀ᵐ x ∂ρ, ∀ z : ι → ℝ,
      a * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j)
    (S : Submodule ℝ (ι → ℝ)) :
    ∀ᵐ x ∂ρ, ∀ z ∈ S, (β * a) * (∑ i, z i ^ 2) ≤
      ∑ i, ∑ j, z i * (β • M x) i j * z j := by
  filter_upwards [hM] with x hx z _
  have ht := mul_le_mul_of_nonneg_left (hx z) hβ
  simpa only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc,
    mul_left_comm] using ht

/-- Symmetry and a positive lower bound give matrix positivity on the natural energy domain. -/
theorem scaled_posSemidef (β a : ℝ) (hβ : 0 ≤ β) (ha : 0 ≤ a)
    (M : α → Matrix ι ι ℝ)
    (hM : ∀ᵐ x ∂ρ, (∀ i j, M x i j = M x j i) ∧
      ∀ z : ι → ℝ, a * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j) :
    ∀ᵐ x ∂ρ, (β • M x).PosSemidef := by
  filter_upwards [hM] with x hx
  apply Matrix.PosSemidef.smul _ hβ
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, fun z => ?_⟩
  · ext i j
    exact hx.1 j i
  · have hn := (mul_nonneg ha (Finset.sum_nonneg (fun i _ => sq_nonneg (z i)))).trans
      (hx.2 z)
    simpa only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum, mul_assoc]
      using hn

/-- The bounded-source estimate for arbitrary base and component types. It uses the
radial-test maximum principle, including fixed component subspaces. -/
theorem weakSolution_eLpNorm_top_le (Q : ScalarFormData ρ)
    (hQ : IsClosedScalarDirichletForm Q)
    (M : α → Matrix ι ι ℝ) (hMmeas : ∀ i j, Measurable (fun x => M x i j))
    (c : ℝ) (hc : 0 < c)
    (hM : ∀ᵐ x ∂ρ, (∀ i j, M x i j = M x j i) ∧
      ∀ z : ι → ℝ, c * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j)
    (S : Submodule ℝ (ι → ℝ)) (f : ι → Lp ℝ 2 ρ) (u : ι → Q.1)
    (hu : WeightedWeakSolution Q M S f u) :
    eLpNorm (fun x => WithLp.toLp 2 (fun i => (u i).val x)) ∞ ρ ≤
      ENNReal.ofReal c⁻¹ * eLpNorm (fun x => WithLp.toLp 2 (fun i => f i x)) ∞ ρ := by
  let F := fun x => (WithLp.toLp 2 (fun i => f i x) : EuclideanSpace ℝ ι)
  let U := fun x => (WithLp.toLp 2 (fun i => (u i).val x) : EuclideanSpace ℝ ι)
  have hFm := (VectorRadial.memLp_values f).aestronglyMeasurable
  have hUm := (VectorRadial.memLp_values (fun i => (u i).val)).aestronglyMeasurable
  change eLpNorm U ∞ ρ ≤ ENNReal.ofReal c⁻¹ * eLpNorm F ∞ ρ
  by_cases htop : eLpNorm F ∞ ρ = ⊤
  · rw [htop, ENNReal.mul_top (by positivity)]
    exact le_top
  let B : ℝ := (eLpNorm F ∞ ρ).toReal
  let R : ℝ≥0 := ⟨c⁻¹ * B, mul_nonneg (inv_nonneg.mpr hc.le) ENNReal.toReal_nonneg⟩
  have hf : ∀ᵐ x ∂ρ, ‖F x‖ ≤ c * R := by
    have h := ae_le_eLpNormEssSup (f := F) (μ := ρ)
    rw [← eLpNorm_exponent_top hFm] at h
    filter_upwards [h] with x hx
    have ht := ENNReal.toReal_mono htop hx
    have he : c * (R : ℝ) = B := by
      change c * (c⁻¹ * B) = B
      rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    rw [he]
    simpa only [enorm_eq_nnnorm, ENNReal.coe_toReal, coe_nnnorm, B] using ht
  have huR := MaximumPrinciple.Internal.bound_of_source_bound
    Q hQ M hMmeas c hc hM S f u hu R hf
  calc
    eLpNorm U ∞ ρ = eLpNormEssSup U ρ := eLpNorm_exponent_top hUm
    _ ≤ ENNReal.ofReal R := eLpNormEssSup_le_of_ae_bound huR
    _ = ENNReal.ofReal c⁻¹ * eLpNorm F ∞ ρ := by
      change ENNReal.ofReal (c⁻¹ * B) = _
      rw [ENNReal.ofReal_mul (inv_nonneg.mpr hc.le), ENNReal.ofReal_toReal htop]

/-- See the proof of Lemma 4.4 in the paper: existence on the whole form domain,
linearity, self-adjointness, sharp value and diffusion bounds, and the Euclidean
essential-supremum bound. The arbitrary fixed subspace `S` gives the compressed
problem. `S = ⊤` is the unrestricted problem. No bound depends on either dimension.
The square-root factor is `(β a)⁻¹ᐟ²`. -/
theorem illustrative_energy (β : ℝ) (hβ : 0 < β) [IsProbabilityMeasure ρ]
    (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q)
    (_hconserv : IsConservativeScalarForm Q)
    (M : α → Matrix ι ι ℝ) (hMmeas : ∀ i j, Measurable (fun x => M x i j))
    (a b : ℝ) (ha : 0 < a) (_hab : a ≤ b)
    (hM : ∀ᵐ x ∂ρ, (∀ i j, M x i j = M x j i) ∧
      ∀ z : ι → ℝ,
        a * (∑ i, z i ^ 2) ≤ (∑ i, ∑ j, z i * M x i j * z j) ∧
        (∑ i, ∑ j, z i * M x i j * z j) ≤ b * (∑ i, z i ^ 2))
    (S : Submodule ℝ (ι → ℝ)) :
    (∀ u : ι → Q.1, WeightedFormDomain Q (fun x => β • M x) S u ↔
      ∀ᵐ x ∂ρ, (fun i => (u i).val x) ∈ S) ∧
    ∃ T : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ) →L[ℝ] PiLp 2 (fun _ : ι => Lp ℝ 2 ρ),
      IsSelfAdjoint T ∧ ∀ f : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ),
        ∃ u : ι → Q.1,
          WeightedWeakSolution Q (fun x => β • M x) S f.ofLp u ∧
          (∀ w, WeightedWeakSolution Q (fun x => β • M x) S f.ofLp w → w = u) ∧
          T f = WithLp.toLp 2 (fun i => (u i).val) ∧
          ‖T f‖ ≤ (β * a)⁻¹ * ‖f‖ ∧
          Real.sqrt (∑ i, Q.2 (u i) (u i)) ≤ (Real.sqrt (β * a))⁻¹ * ‖f‖ ∧
          eLpNorm (fun x => WithLp.toLp 2 (fun i => (u i).val x)) ∞ ρ ≤
            ENNReal.ofReal (β * a)⁻¹ *
              eLpNorm (fun x => WithLp.toLp 2 (fun i => f i x)) ∞ ρ := by
  classical
  have hlow : ∀ᵐ x ∂ρ, (∀ i j, M x i j = M x j i) ∧
      ∀ z : ι → ℝ, a * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j :=
    hM.mono (fun x hx => ⟨hx.1, fun z => (hx.2 z).1⟩)
  have hpsd := scaled_posSemidef β a hβ.le ha.le M hlow
  have hl := scaled_lower β a hβ.le M (hlow.mono (fun x hx => hx.2)) S
  have hmeas := scaled_measurable β M hMmeas
  have hpos := mul_pos hβ ha
  have hall := scaled_lower β a hβ.le M (hlow.mono (fun x hx => hx.2)) ⊤
  refine ⟨?_, MatrixEnergy.l2Inverse Q hQ (fun x => β • M x) S hpsd
    (β * a) hpos hl, ?_, ?_⟩
  · intro u
    apply bounded_formDomain_iff Q (fun x => β • M x) hmeas (β * b) _ S u
    filter_upwards [hM] with x hx z
    have hn := (mul_nonneg ha.le (Finset.sum_nonneg (fun i _ => sq_nonneg (z i)))).trans
      (hx.2 z).1
    have hu := mul_le_mul_of_nonneg_left (hx.2 z).2 hβ.le
    have hscale' : (∑ i, ∑ j, z i * (β • M x) i j * z j) =
        β * (∑ i, ∑ j, z i * M x i j * z j) := by
      simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hscale']
    exact ⟨mul_nonneg hβ.le hn, by simpa only [mul_assoc] using hu⟩
  · apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    exact MatrixEnergy.l2Inverse_symmetric Q hQ (fun x => β • M x) S hpsd (β * a) hpos hl
  · intro f
    let u := MatrixEnergy.tuple Q hQ (fun x => β • M x) S hpsd
      (MatrixEnergy.solution Q hQ (fun x => β • M x) S hpsd (β * a) hpos hl f)
    have hu : WeightedWeakSolution Q (fun x => β • M x) S f.ofLp u :=
      MatrixEnergy.solution_weightedWeakSolution Q hQ (fun x => β • M x) S hpsd
        (β * a) hpos hl hmeas f.ofLp
    refine ⟨u, hu, ?_, rfl, ?_, ?_, ?_⟩
    · exact fun w hw => MatrixEnergy.weightedWeakSolution_unique Q hQ
        (fun x => β • M x) S hpsd (β * a) hpos hl hmeas f.ofLp w hw
    · exact MatrixEnergy.l2Inverse_norm_le Q hQ (fun x => β • M x) S hpsd
        (β * a) hpos hl f
    · exact MatrixEnergy.solution_gradient_le Q hQ (fun x => β • M x) S hpsd
        (β * a) hpos hl f
    · apply weakSolution_eLpNorm_top_le Q hQ (fun x => β • M x) hmeas
        (β * a) hpos _ S f.ofLp u hu
      filter_upwards [hlow, hall] with x hx hlx
      refine ⟨?_, ?_⟩
      · intro i j
        change β * M x i j = β * M x j i
        rw [hx.1 i j]
      · exact fun z => hlx z (Submodule.mem_top)

end Riesz2.AbstractEnergy
