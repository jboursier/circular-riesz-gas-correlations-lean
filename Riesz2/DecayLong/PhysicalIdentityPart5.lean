/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.PhysicalIdentityPart4
public import Riesz2.DecayLong.PhysicalCorePart4

/-!
# Physical auxiliary solvability and comparison

Common-domain harmonic elimination for Subsection 5.1, using the
actual proper core and its proved lower bound from the proof of Lemma 5.4.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators MatrixOrder

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.PhysicalIdentity.Internal

/-- A bounded matrix on a measure-preserving carrier gives a continuous
multiplication form on the original scalar Sobolev product, with any finite
component set. Only scalar values are pulled back. -/
theorem carrier_matrix_form {α X ι : Type*} [MeasurableSpace α] [MeasurableSpace X]
    [Fintype ι] {ν : Measure α} {μ : Measure X} (f : X → α)
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (hco : MeasurePreserving f μ ν)
    (A : X → Matrix ι ι ℝ)
    (hm : ∀ i j, Measurable (fun x => A x i j))
    (hb : ∃ b : ℝ, 0 ≤ b ∧ ∀ x i j, |A x i j| ≤ b) :
    ∃ B : MatrixEnergy.Vector (ι := ι) Q hQ →L[ℝ]
        MatrixEnergy.Vector (ι := ι) Q hQ →L[ℝ] ℝ,
      ∀ u v,
        let P := fun x : X =>
          ∑ i, ∑ j, (MatrixEnergy.vectorEquiv Q hQ u i).val (f x) * A x i j *
            (MatrixEnergy.vectorEquiv Q hQ v j).val (f x)
        Integrable P μ ∧
        B u v = ∫ x, P x ∂μ := by
  let J : ScalarFormHilbert.Space Q hQ →L[ℝ] Lp ℝ 2 μ :=
    (Lp.compMeasurePreservingₗᵢ ℝ f hco).toContinuousLinearMap.comp
      (ScalarFormHilbert.value Q hQ)
  obtain ⟨b, hb0, hb⟩ := hb
  have hs (f : ScalarFormHilbert.Space Q hQ) :
      Integrable (fun x => b * (J f x) ^ 2) μ ∧
        (∫ x, b * (J f x) ^ 2 ∂μ) ≤ b * ‖f‖ ^ 2 := by
    have hi : Integrable (fun x => (J f x) ^ 2) μ := by
      apply ((Lp.memLp (J f)).integrable_mul (Lp.memLp (J f))).congr
      exact ae_of_all μ fun x => (pow_two (J f x)).symm
    have he : (∫ x, (J f x) ^ 2 ∂μ) = ‖J f‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards with x
      simp only [Real.inner_apply, pow_two]
    have hn : ‖J f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
      have hnorm : ‖J f‖ = ‖(ScalarFormHilbert.equiv Q hQ f).val‖ :=
        Lp.norm_compMeasurePreserving _ hco
      rw [hnorm, ScalarFormHilbert.norm_sq]
      exact le_add_of_nonneg_right (hQ.2.2.1 _)
    refine ⟨hi.const_mul b, ?_⟩
    rw [integral_const_mul, he]
    exact mul_le_mul_of_nonneg_left hn hb0
  have hex (i j : ι) := PhysicalFormDomain.Internal.exists_entry_form
    J (fun _ => b) (fun x => A x i j) (hm i j).aestronglyMeasurable
    (ae_of_all μ (fun x => hb x i j)) b hb0 hs
  choose E hE using hex
  let B : MatrixEnergy.Vector (ι := ι) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := ι) Q hQ →L[ℝ] ℝ :=
    ∑ i, ∑ j, (E i j).bilinearComp (PiLp.proj 2 _ i) (PiLp.proj 2 _ j)
  refine ⟨B, fun u v => ?_⟩
  have heq : (fun x : X => ∑ i, ∑ j, A x i j * J (u i) x * J (v j) x) =ᵐ[μ]
      (fun x : X => ∑ i, ∑ j,
        (MatrixEnergy.vectorEquiv Q hQ u i).val (f x) * A x i j *
          (MatrixEnergy.vectorEquiv Q hQ v j).val (f x)) := by
    filter_upwards [ae_all_iff.mpr (fun i => Lp.coeFn_compMeasurePreserving
        (ScalarFormHilbert.value Q hQ (u i)) hco),
      ae_all_iff.mpr (fun j => Lp.coeFn_compMeasurePreserving
        (ScalarFormHilbert.value Q hQ (v j)) hco)] with x hx hy
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change A x i j * (Lp.compMeasurePreserving _ hco (ScalarFormHilbert.value Q hQ (u i))) x *
      (Lp.compMeasurePreserving _ hco (ScalarFormHilbert.value Q hQ (v j))) x = _
    rw [hx i, hy j]
    change A x i j * (MatrixEnergy.vectorEquiv Q hQ u i).val (f x) *
      (MatrixEnergy.vectorEquiv Q hQ v j).val (f x) = _
    ring
  have hi : Integrable (fun x : X => ∑ i, ∑ j, A x i j * J (u i) x * J (v j) x) μ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hE i j (u i) (v j)).1
  refine ⟨hi.congr heq, ?_⟩
  rw [← integral_congr_ae heq, integral_finsetSum]
  · simp only [B, sum_apply, ContinuousLinearMap.bilinearComp_apply,
      PiLp.proj_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl fun j _ => (hE i j (u i) (v j)).2
    · exact fun j _ => (hE i j (u i) (v j)).1
  · exact fun i _ => integrable_finsetSum _ fun j _ => (hE i j (u i) (v j)).1


end Riesz2.PhysicalIdentity.Internal

namespace Riesz2.PhysicalIdentity.Internal

/-- The L² mass is unchanged by pulling back along a measure-preserving
carrier. This also justifies the integrability needed for matrix lower bounds. -/
theorem carrier_mass {α X ι : Type*} [MeasurableSpace α] [MeasurableSpace X]
    [Fintype ι] {ν : Measure α} {μ : Measure X} (f : X → α)
    (hco : MeasurePreserving f μ ν) (hf : MeasurableEmbedding f)
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (u : MatrixEnergy.Vector (ι := ι) Q hQ) :
    Integrable (fun x => ∑ i, ((MatrixEnergy.vectorEquiv Q hQ u i).val (f x)) ^ 2) μ ∧
      (∫ x, ∑ i, ((MatrixEnergy.vectorEquiv Q hQ u i).val (f x)) ^ 2 ∂μ) =
        ‖OperatorSchur.vectorValues Q hQ u‖ ^ 2 := by
  have hi (i : ι) : Integrable (fun x =>
      ((MatrixEnergy.vectorEquiv Q hQ u i).val (f x)) ^ 2) μ :=
    hco.integrable_comp_of_integrable
      (Lp.memLp (MatrixEnergy.vectorEquiv Q hQ u i).val).integrable_sq
  refine ⟨integrable_finsetSum _ (fun i _ => hi i), ?_⟩
  rw [integral_finsetSum _ (fun i _ => hi i), PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro i _
  rw [OperatorSchur.vectorValues_apply, ← real_inner_self_eq_norm_sq, L2.inner_def]
  have hc := hco.integral_comp hf (fun x => ((MatrixEnergy.vectorEquiv Q hQ u i).val x) ^ 2)
  simpa only [Function.comp_def, Real.inner_apply, sq] using hc

/-- Internal pullback lower-bound bridge. The scalar energy is the original
one. The coefficient lower bound is integrated on its actual carrier. -/
theorem carrier_form_lower {α X ι : Type*} [MeasurableSpace α] [MeasurableSpace X]
    [Fintype ι] {ν : Measure α} {μ : Measure X} (f : X → α)
    (hco : MeasurePreserving f μ ν) (hf : MeasurableEmbedding f)
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (M : X → Matrix ι ι ℝ) (a : ℝ)
    (hl : ∀ x (t : ι → ℝ), a * (∑ i, t i ^ 2) ≤
      ∑ i, ∑ j, t i * M x i j * t j)
    (H : MatrixEnergy.Vector (ι := ι) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := ι) Q hQ →L[ℝ] ℝ)
    (hH : ∀ u v,
      let P := fun x => ∑ i, ∑ j,
        (MatrixEnergy.vectorEquiv Q hQ u i).val (f x) * M x i j *
          (MatrixEnergy.vectorEquiv Q hQ v j).val (f x)
      Integrable P μ ∧ H u v = ∫ x, P x ∂μ)
    (u : MatrixEnergy.Vector (ι := ι) Q hQ) :
    a * ‖OperatorSchur.vectorValues Q hQ u‖ ^ 2 ≤ H u u := by
  obtain ⟨hi, he⟩ := carrier_mass f hco hf Q hQ u
  rw [(hH u u).2, ← he, ← integral_const_mul]
  exact integral_mono (hi.const_mul a) (hH u u).1 (fun x => hl x _)

end Riesz2.PhysicalIdentity.Internal

namespace Riesz2.PhysicalIdentity.Internal

/-- See the proof of Lemma 5.4 (ambient form domain): the
actual full proper core is a symmetric coercive form on the original scalar
Sobolev product. The component period and physical dimension are independent. -/
theorem proper_lifted_form (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : 2 * (n : ℕ) ≤ (M : ℕ))
    (K : ℕ) (hK : 1 ≤ K) (hKM : K ≤ (M : ℕ) / 4)
    (θ : PhysicalCutoff) (ε κ₀ : ℝ) (hε : 0 ≤ ε)
    {ν : Measure (EuclideanSpace ℝ (Fin (n : ℕ)))}
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (hco : MeasurePreserving
      ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
      (ν.comap ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))) ν) :
    ∃ F : MatrixEnergy.Vector (ι := Fin (M : ℕ)) Q hQ →L[ℝ]
        MatrixEnergy.Vector (ι := Fin (M : ℕ)) Q hQ →L[ℝ] ℝ,
      ∃ c : ℝ, 0 < c ∧ (∀ u v, F u v = F v u) ∧
        (∀ u, c * ‖u‖ ^ 2 ≤ F u u) ∧
        ∀ u v,
          let Ω := AffineSimplex.chartDomain n ((n + m : ℕ) + 1)
          let P := fun x : Ω => ∑ i, ∑ j,
            (MatrixEnergy.vectorEquiv Q hQ u i).val x.val *
              PhysicalCore.properMatrix β s n m M hM (by omega) K θ ε κ₀ x i j *
              (MatrixEnergy.vectorEquiv Q hQ v j).val x.val
          Integrable P (ν.comap ((↑) : Ω → EuclideanSpace ℝ (Fin (n : ℕ)))) ∧
            F u v = OperatorSchur.vectorEnergy Q hQ u v + β.val *
              ∫ x, P x ∂ν.comap ((↑) : Ω → EuclideanSpace ℝ (Fin (n : ℕ))) := by
  let Ω := AffineSimplex.chartDomain n ((n + m : ℕ) + 1)
  let μ := ν.comap ((↑) : Ω → EuclideanSpace ℝ (Fin (n : ℕ)))
  let A := PhysicalCore.properMatrix β s n m M hM (by omega) K θ ε κ₀
  obtain ⟨H, hH⟩ := carrier_matrix_form ((↑) : Ω → EuclideanSpace ℝ (Fin (n : ℕ)))
    Q hQ hco A (PhysicalCore.measurable_properMatrix β s n m M hM (by omega) K θ ε κ₀)
    (PhysicalCore.properMatrix_bounded β s n m M hM (by omega) K θ ε κ₀)
  obtain ⟨a, ha, hl⟩ := PhysicalCore.properMatrix_truncated_coercivity s
  let b := a * (n : ℝ) ^ (-(s.val + 2) * ε) * (K : ℝ) ^ (-1 - s.val)
  have hb : 0 < b := by
    have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
    dsimp only [b]
    positivity
  have hlo (x : Ω) (t : Fin (M : ℕ) → ℝ) : b * (∑ i, t i ^ 2) ≤
      ∑ i, ∑ j, t i * A x i j * t j := by
    have hx := (FiniteMatrixOrder.smul_one_le_iff
      (PhysicalCore.properMatrix_posSemidef β s n m hn M hM hnM K θ ε κ₀ x).isHermitian b).mp
        (hl β n m hn M hM hnM K hK hKM θ ε κ₀ hε x) t
    simpa only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, sq] using hx
  have hHlo (u) := carrier_form_lower ((↑) : Ω → EuclideanSpace ℝ (Fin (n : ℕ)))
    hco (MeasurableEmbedding.subtype_coe (AffineSimplex.isOpen_chartDomain n _).measurableSet)
    Q hQ A b hlo H hH u
  let F := OperatorSchur.vectorEnergy (ι := Fin (M : ℕ)) Q hQ + β.val • H
  have hen (u) : (β.val * b) * ‖OperatorSchur.vectorValues Q hQ u‖ ^ 2 +
      OperatorSchur.vectorEnergy Q hQ u u ≤ F u u := by
    have hh := mul_le_mul_of_nonneg_left (hHlo u) β.property.le
    change _ ≤ OperatorSchur.vectorEnergy Q hQ u u + β.val * H u u
    nlinarith only [hh]
  refine ⟨F, min 1 (β.val * b), lt_min zero_lt_one (mul_pos β.property hb), ?_,
    graph_form_coercive Q hQ F _ hen, ?_⟩
  · intro u v
    change OperatorSchur.vectorEnergy Q hQ u v + β.val * H u v =
      OperatorSchur.vectorEnergy Q hQ v u + β.val * H v u
    have hsym : OperatorSchur.vectorEnergy Q hQ u v = OperatorSchur.vectorEnergy Q hQ v u := by
      simp only [OperatorSchur.vectorEnergy_apply]
      exact Finset.sum_congr rfl (fun i _ => hQ.2.1 _ _)
    rw [hsym, (hH u v).2, (hH v u).2]
    congr 1
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [A]
    rw [PhysicalCore.properMatrix_symmetric β s n m M hM (by omega) K θ ε κ₀ x j i]
    ring
  · intro u v P
    exact ⟨(hH u v).1, by
      change OperatorSchur.vectorEnergy Q hQ u v + β.val * H u v = _
      rw [(hH u v).2]⟩

end Riesz2.PhysicalIdentity.Internal

namespace Riesz2.PhysicalIdentity.Internal

/-- An exterior test sees only the literal reference blocks, on the actual
carrier. Zero L² classes are handled almost everywhere before integration. -/
theorem carrier_exterior_pair {α X : Type*} [MeasurableSpace α] [MeasurableSpace X]
    {ν : Measure α} {μ : Measure X} (f : X → α) (hco : MeasurePreserving f μ ν)
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (n M : ℕ+) (hnM : (n : ℕ) ≤ (M : ℕ))
    (A : X → Matrix (Fin (M : ℕ)) (Fin (M : ℕ)) ℝ)
    (H : Matrix (Fin (M : ℕ)) (Fin (M : ℕ)) ℝ)
    (he : ∀ x i j, (n : ℕ) ≤ j.val → A x i j = H i j)
    (u : MatrixEnergy.Vector (ι := Fin (M : ℕ)) Q hQ)
    (w : MatrixEnergy.Vector (ι := Fin ((M : ℕ) - (n : ℕ))) Q hQ) :
    (fun x => ∑ i, ∑ j, (MatrixEnergy.vectorEquiv Q hQ u i).val (f x) * A x i j *
      (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n M hnM (0,w)) j).val (f x)) =ᵐ[μ]
    (fun x => matrixFieldPair (fun _ : α => H)
      (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val)
      (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n M hnM (0,w)) i).val) (f x)) := by
  simp only [matrixFieldPair]
  filter_upwards [hco.quasiMeasurePreserving.ae (Lp.coeFn_zero ℝ 2 ν)] with x hx
  have hz : (0 : Lp ℝ 2 ν) (f x) = 0 := by simpa only [Pi.zero_apply] using hx
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : (n : ℕ) ≤ j.val
  · rw [he x i j hj]
  · rw [SchurRestriction.exterior_values_zero Q hQ n M hnM w j (by omega)]
    change _ * _ * (0 : Lp ℝ 2 ν) (f x) = _ * _ * (0 : Lp ℝ 2 ν) (f x)
    rw [hz, mul_zero, mul_zero]

end Riesz2.PhysicalIdentity.Internal

namespace Riesz2.PhysicalIdentity

/-- See Subsection 5.1 of the paper: uniform physical curvature on the actual marginal
law, in the matrix interface used by the common-domain comparison. -/
theorem proper_physical_lower (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε : ℝ) (hε : 0 ≤ ε) :
    let p := ofLong β s
    let hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ) := by simp; omega
    let ν := activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ ε false
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      β.val * ∑ i, θ.val ((n : ℝ) ^ (-ε) * x i) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal)
    let a := min 1 (s.val * (s.val + 1)) * (n : ℝ) ^ (-(s.val + 2) * ε)
    0 < a ∧ ∀ᵐ x ∂ν, ∀ t : Fin (n : ℕ) → ℝ,
      (β.val * a) * (∑ i, t i ^ 2) ≤ ∑ i, ∑ j, t i * hessianMatrix V x i j * t j := by
  intro p hn ν V a
  have ha : 0 < a := mul_pos
    (lt_min zero_lt_one (mul_pos s.property.1 (by linarith [s.property.1])))
    (Real.rpow_pos_of_pos (by exact_mod_cast n.pos) _)
  have hlo : ∀ᵐ x ∂ν, ∀ t : Fin (n : ℕ) → ℝ,
      (β.val * a) * (∑ i, t i ^ 2) ≤ ∑ i, ∑ j, t i * hessianMatrix V x i j * t j := by
    have hpot := PhysicalFormDomain.proper_gibbs_potential β s n m θ ε
    filter_upwards [IntrinsicScalarCore.supported (AffineSimplex.isOpen_chartDomain n _) hpot] with x hx
    intro t
    have hsmooth := hpot.1.contDiffAt ((AffineSimplex.isOpen_chartDomain n _).mem_nhds hx)
    have h := (proper_scaled_curvature β s n m θ ε hε).2 x hx (WithLp.toLp 2 t)
    rw [← PhysicalEnergy.hessianMatrix_quadratic (hsmooth.of_le (by norm_num)),
      EuclideanSpace.real_norm_sq_eq] at h
    convert h using 1 <;> dsimp only [a, V, p, ofLong]
    ring
  exact ⟨ha,hlo⟩

namespace Internal

/-- Sum a field supported on the first `n` indices using its original labels. -/
theorem sum_active {R : Type*} [AddCommMonoid R] (n M : ℕ+) (hnM : (n : ℕ) ≤ (M : ℕ))
    (f : Fin (M : ℕ) → R) (hf : ∀ i, (n : ℕ) ≤ i.val → f i = 0) :
    (∑ i, f i) = ∑ i : Fin (n : ℕ), f (i.castLE hnM) := by
  have he := Fintype.sum_equiv (finCongr (Nat.add_sub_of_le hnM))
    (fun i => f ((finCongr (Nat.add_sub_of_le hnM)) i)) f (fun _ => rfl)
  rw [← he, Fin.sum_univ_add]
  have hz : (∑ i : Fin ((M : ℕ) - (n : ℕ)),
      f ((finCongr (Nat.add_sub_of_le hnM)) (Fin.natAdd (n : ℕ) i))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    apply hf
    change (n : ℕ) ≤ (n : ℕ) + i.val
    omega
  rw [hz, add_zero]
  exact Finset.sum_congr rfl (fun i _ => congrArg f (Fin.ext rfl))

/-- Zero extension identifies the actual full proper-core pairing with its
active pairing on the carrier, before any integration. -/
theorem proper_active_pair (β : InverseTemperature) (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    {ν : Measure (EuclideanSpace ℝ (Fin (n : ℕ)))}
    (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : (n : ℕ) ≤ (M : ℕ))
    (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ)
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (hco : MeasurePreserving
      ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
      (ν.comap ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))) ν)
    (u v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ) :
    (fun x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) => ∑ i, ∑ j,
      (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n M hnM (u,0)) i).val x.val *
        PhysicalCore.properMatrix β s n m M hM hnM K θ ε κ₀ x i j *
        (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n M hnM (v,0)) j).val x.val) =ᵐ[ν.comap
          ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))]
    (fun x => ∑ i, ∑ j, (MatrixEnergy.vectorEquiv Q hQ u i).val x.val *
      PhysicalCore.properActive β s n m M hM hnM K θ ε κ₀ x i j *
      (MatrixEnergy.vectorEquiv Q hQ v j).val x.val) := by
  let J := SchurRestriction.assemble Q hQ n M hnM
  have hz (w : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ) (i : Fin (M : ℕ))
      (hi : (n : ℕ) ≤ i.val) : (MatrixEnergy.vectorEquiv Q hQ (J (w,0)) i).val = 0 := by
    change (ScalarFormHilbert.equiv Q hQ (J (w,0) i)).val = 0
    let j : Fin ((M : ℕ) - (n : ℕ)) := ⟨i.val - (n : ℕ),by omega⟩
    have hlabel : (finCongr (Nat.add_sub_of_le hnM)) (Fin.natAdd (n : ℕ) j) = i := Fin.ext (by change (n : ℕ) + (i.val - (n : ℕ)) = i.val; omega)
    change (ScalarFormHilbert.equiv Q hQ
      (SchurRestriction.join Q hQ n ((M : ℕ) - (n : ℕ)) (w,0)
        ((finCongr (Nat.add_sub_of_le hnM)).symm i))).val = 0
    rw [← hlabel, Equiv.symm_apply_apply, SchurRestriction.join_right_apply]
    simp only [PiLp.zero_apply,map_zero,Submodule.coe_zero]
  filter_upwards [hco.quasiMeasurePreserving.ae (Lp.coeFn_zero ℝ 2 ν)] with x hx
  have hx0 : (0 : Lp ℝ 2 ν) x.val = 0 := by simpa only [Pi.zero_apply] using hx
  rw [sum_active n M hnM _ (fun i hi => by
    rw [hz u i hi,hx0]
    simp only [zero_mul,Finset.sum_const_zero])]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_active n M hnM _ (fun j hj => by rw [hz v j hj,hx0,mul_zero])]
  apply Finset.sum_congr rfl
  intro j _
  rw [PhysicalCore.properMatrix_active]
  change (ScalarFormHilbert.equiv Q hQ (J (u,0) (i.castLE hnM))).val x.val * _ *
    (ScalarFormHilbert.equiv Q hQ (J (v,0) (j.castLE hnM))).val x.val = _
  rw [SchurRestriction.assemble_left_apply,SchurRestriction.assemble_left_apply]
  rfl

/-- Internal active restriction of a literal lifted integral form. The
zero-extension calculation is made before integrating on the carrier. -/
theorem proper_active_form (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : (n : ℕ) ≤ (M : ℕ))
    (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ)
    {ν : Measure (EuclideanSpace ℝ (Fin (n : ℕ)))}
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (hco : MeasurePreserving
      ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
      (ν.comap ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))) ν)
    (B : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ] ℝ)
    (hB : ∀ u v,
      let P := fun x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) => ∑ i, ∑ j,
        (MatrixEnergy.vectorEquiv Q hQ u i).val x.val *
          PhysicalCore.properActive β s n m M hM hnM K θ ε κ₀ x i j *
          (MatrixEnergy.vectorEquiv Q hQ v j).val x.val
      Integrable P (ν.comap ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))) ∧
        B u v = ∫ x, P x ∂ν.comap ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ))))
    (F : MatrixEnergy.Vector (ι := Fin (M : ℕ)) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := Fin (M : ℕ)) Q hQ →L[ℝ] ℝ)
    (hF : ∀ u v,
      let P := fun x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) => ∑ i, ∑ j,
        (MatrixEnergy.vectorEquiv Q hQ u i).val x.val *
          PhysicalCore.properMatrix β s n m M hM hnM K θ ε κ₀ x i j *
          (MatrixEnergy.vectorEquiv Q hQ v j).val x.val
      Integrable P (ν.comap ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))) ∧
        F u v = OperatorSchur.vectorEnergy Q hQ u v + β.val *
          ∫ x, P x ∂ν.comap ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))) :
    ∀ u v,
      F (SchurRestriction.assemble Q hQ n M hnM (u,0))
        (SchurRestriction.assemble Q hQ n M hnM (v,0)) =
        OperatorSchur.vectorEnergy Q hQ u v + β.val * B u v := by
  intro u v
  rw [(hF _ _).2, integral_congr_ae
    (Internal.proper_active_pair β s n m M hM hnM K θ ε κ₀ Q hQ hco u v)]
  have hBi := (hB u v).2
  rw [← hBi, OperatorSchur.vectorEnergy_apply, SchurRestriction.assemble_energy]
  simp only [map_zero,Pi.zero_apply,Finset.sum_const_zero,add_zero]
  rw [OperatorSchur.vectorEnergy_apply]


/-- Internal harmonic elimination for the actual proper core on an existing
ambient physical scalar form. All coercivity is proved from the core
lower bound. The exterior response and correction retain their reference
integral equations. -/
theorem proper_auxiliary_forms (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : 2 * (n : ℕ) ≤ (M : ℕ))
    (K : ℕ) (hK : 1 ≤ K) (hKM : K ≤ (M : ℕ) / 4)
    (θ : PhysicalCutoff) (ε κ₀ : ℝ) (hε : 0 ≤ ε)
    {ν : Measure (EuclideanSpace ℝ (Fin (n : ℕ)))}
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (hco : MeasurePreserving
      ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
      (ν.comap ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))) ν) :
    let Ω := AffineSimplex.chartDomain n ((n + m : ℕ) + 1)
    let μ := ν.comap ((↑) : Ω → EuclideanSpace ℝ (Fin (n : ℕ)))
    ∃ (F : MatrixEnergy.Vector (ι := Fin (M : ℕ)) Q hQ →L[ℝ]
            MatrixEnergy.Vector (ι := Fin (M : ℕ)) Q hQ →L[ℝ] ℝ)
          (S G : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ]
            MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ] ℝ)
          (R : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ]
            MatrixEnergy.Vector (ι := Fin ((M : ℕ) - (n : ℕ))) Q hQ),
          (∀ u v,
            let P := fun x : Ω => ∑ i, ∑ j,
              (MatrixEnergy.vectorEquiv Q hQ u i).val x.val *
                PhysicalCore.properMatrix β s n m M hM (by omega) K θ ε κ₀ x i j *
                (MatrixEnergy.vectorEquiv Q hQ v j).val x.val
            Integrable P μ ∧ F u v = OperatorSchur.vectorEnergy Q hQ u v + β.val * ∫ x, P x ∂μ) ∧
          (∀ u v, G u v = G v u) ∧ (∀ u, 0 ≤ G u u) ∧
          (∀ u v, S u v = F (SchurRestriction.assemble Q hQ n M (by omega) (u,0))
            (SchurRestriction.assemble Q hQ n M (by omega) (v,0)) - G u v) ∧
          (∀ u w,
            let P := fun z z' => fun x : Ω => matrixFieldPair
              (fun _ : EuclideanSpace ℝ (Fin (n : ℕ)) => (2 : ℝ) • referenceIntervalMatrix s M hM K)
              (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n M (by omega) z) i).val)
              (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n M (by omega) z') i).val) x.val
            Integrable (P (0,R u) (0,w)) μ ∧ Integrable (P (u,0) (0,w)) μ ∧
              β.val⁻¹ * OperatorSchur.vectorEnergy Q hQ (R u) w +
                (∫ x, P (0,R u) (0,w) x ∂μ) = ∫ x, P (u,0) (0,w) x ∂μ) ∧
          (∀ u v,
            let P := fun x : Ω => matrixFieldPair
              (fun _ : EuclideanSpace ℝ (Fin (n : ℕ)) => (2 : ℝ) • referenceIntervalMatrix s M hM K)
              (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n M (by omega) (v,0)) i).val)
              (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n M (by omega) (0,R u)) i).val) x.val
            Integrable P μ ∧ G u v = β.val * ∫ x, P x ∂μ) ∧
          (∃ c : ℝ, 0 < c ∧ ∀ u, c * ‖u‖ ^ 2 ≤ S u u) := by
  intro Ω μ
  obtain ⟨F, c, hc, hs, hl, hF⟩ := Internal.proper_lifted_form β s n m hn M hM hnM
    K hK hKM θ ε κ₀ hε Q hQ hco
  let k := (M : ℕ) - (n : ℕ)
  let J := SchurRestriction.assemble Q hQ n M (by omega : (n : ℕ) ≤ (M : ℕ))
  let Eiso := SchurRestriction.castIso Q hQ n M (by omega : (n : ℕ) ≤ (M : ℕ))
  let F' := F.bilinearComp Eiso.toContinuousLinearEquiv.toContinuousLinearMap
    Eiso.toContinuousLinearEquiv.toContinuousLinearMap
  have hF' (u : MatrixEnergy.Vector (ι := Fin ((n : ℕ) + k)) Q hQ) : c * ‖u‖ ^ 2 ≤ F' u u := by
    simpa only [F', ContinuousLinearMap.bilinearComp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.norm_map] using hl (Eiso u)
  let A := SchurRestriction.active Q hQ n k F'
  let E := SchurRestriction.exteriorForm Q hQ n k F'
  let C := SchurRestriction.cross Q hQ n k F'
  have hE : ∀ w, c * ‖w‖ ^ 2 ≤ E w w := SchurRestriction.exterior_coercive Q hQ n k F' c hF'
  let R := OperatorSchur.exterior E C c hc hE
  let G := C.flip.comp R
  let S := OperatorSchur.reduced A E C c hc hE
  have hR (u w) : E (R u) w = C u w := OperatorSchur.exterior_solves E C c hc hE u w
  have hEs (z w) : E z w = E w z := hs _ _
  have hfull (u z) : c * (‖u‖ ^ 2 + ‖z‖ ^ 2) ≤ OperatorSchur.blockForm A E C (u,z) (u,z) := by
    rw [SchurRestriction.blockForm_eq Q hQ n k F' (fun u v => hs _ _),
      ← SchurRestriction.join_norm_sq]
    exact hF' _
  have hS (u) : c * ‖u‖ ^ 2 ≤ S u u := OperatorSchur.reduced_coercive A E C c hc hE c hc.le hfull u
  let H := (2 : ℝ) • referenceIntervalMatrix s M hM K
  let P := fun z z' => fun x : Ω => matrixFieldPair
    (fun _ : EuclideanSpace ℝ (Fin (n : ℕ)) => H)
    (fun i => (MatrixEnergy.vectorEquiv Q hQ (J z) i).val)
    (fun i => (MatrixEnergy.vectorEquiv Q hQ (J z') i).val) x.val
  have href (z w) :
      (fun x : Ω => ∑ i, ∑ j, (MatrixEnergy.vectorEquiv Q hQ (J z) i).val x.val *
        PhysicalCore.properMatrix β s n m M hM (by omega) K θ ε κ₀ x i j *
        (MatrixEnergy.vectorEquiv Q hQ (J (0,w)) j).val x.val) =ᵐ[μ] P z (0,w) :=
    Internal.carrier_exterior_pair _ hco Q hQ n M (by omega) _ H
      (fun x i j hj => PhysicalCore.properMatrix_exterior β s n m M hM (by omega)
        K θ ε κ₀ x i j (Or.inr hj)) (J z) w
  have hPi (z w) : Integrable (P z (0,w)) μ := (hF (J z) (J (0,w))).1.congr (href z w)
  have hEc (z w) : E z w = OperatorSchur.vectorEnergy Q hQ z w + β.val * ∫ x, P (0,z) (0,w) x ∂μ := by
    change F (J (0,z)) (J (0,w)) = _
    rw [(hF _ _).2, integral_congr_ae (href (0,z) w), OperatorSchur.vectorEnergy_apply,
      SchurRestriction.assemble_energy]
    simp only [map_zero, Pi.zero_apply, Finset.sum_const_zero, zero_add]
    rw [OperatorSchur.vectorEnergy_apply]
  have hCc (u w) : C u w = β.val * ∫ x, P (u,0) (0,w) x ∂μ := by
    change F (J (u,0)) (J (0,w)) = _
    rw [(hF _ _).2, integral_congr_ae (href (u,0) w), OperatorSchur.vectorEnergy_apply,
      SchurRestriction.assemble_energy]
    simp only [map_zero, Pi.zero_apply, LinearMap.zero_apply, Finset.sum_const_zero, zero_add, add_zero]
  refine ⟨F,S,G,R,hF,?_,?_,(fun _ _ => rfl),?_,?_,c,hc,hS⟩
  · intro u v
    change C v (R u) = C u (R v)
    rw [← hR v (R u), ← hR u (R v), hEs]
  · intro u
    change 0 ≤ C u (R u)
    rw [← hR u (R u)]
    exact (mul_nonneg hc.le (sq_nonneg _)).trans (hE _)
  · intro u w P'
    refine ⟨hPi (0,R u) w, hPi (u,0) w, ?_⟩
    have he := hR u w
    rw [hEc, hCc] at he
    have he' := congrArg (fun t : ℝ => β.val⁻¹ * t) he
    simpa only [mul_add, ← mul_assoc, inv_mul_cancel₀ β.property.ne', one_mul, P', P, H] using he'
  · intro u v P'
    exact ⟨hPi (v,0) (R u), hCc v (R u)⟩

end Internal

/-- See Subsection 5.1 of the paper (proper auxiliary solvability): the actual proper
core yields a coercive auxiliary form and its unique solution for every L²
source, on the original ambient physical Sobolev domain. The response is
identified by the literal reference exterior equation with diffusion β⁻¹.
The full lifted form is identified with the actual proper core integral.
The physical and auxiliary equations both have unique solutions. Subtraction
and testing give the physical energy bound with the explicit mass
`min(1,s(s+1)) n^(-(s+2)ε)`. No periodized coefficient or entry-error estimate
is assumed. This theorem covers the proper-window clause. -/
theorem proper_comparison (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (θ : PhysicalCutoff) (ε κ₀ : ℝ) (hε : 0 ≤ ε)
    (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : 2 * (n : ℕ) ≤ (M : ℕ))
    (K : ℕ) (hK : 1 ≤ K) (hKM : K ≤ (M : ℕ) / 4) :
    let p := ofLong β s
    let hnp : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ) := by simp; omega
    let ν := activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hnp θ ε false
    let Ω := AffineSimplex.chartDomain n ((n + m : ℕ) + 1)
    let μ := ν.comap ((↑) : Ω → EuclideanSpace ℝ (Fin (n : ℕ)))
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      β.val * ∑ i, θ.val ((n : ℝ) ^ (-ε) * x i) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal)
    let a := min 1 (s.val * (s.val + 1)) * (n : ℝ) ^ (-(s.val + 2) * ε)
    ∃ Q : ScalarFormData ν, IsNeumannRealization Ω Q ∧
      ∃ hQ : IsClosedScalarDirichletForm Q,
        (∀ (W : Submodule ℝ (Fin (n : ℕ) → ℝ)) (u : Fin (n : ℕ) → Q.1),
          WeightedFormDomain Q (hessianMatrix V) W u ↔
            ∀ᵐ x ∂ν, (fun i => (u i).val x) ∈ W) ∧
        ∃ (F : MatrixEnergy.Vector (ι := Fin (M : ℕ)) Q hQ →L[ℝ]
            MatrixEnergy.Vector (ι := Fin (M : ℕ)) Q hQ →L[ℝ] ℝ)
          (S G Aphys T : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ]
            MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ] ℝ)
          (R : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ]
            MatrixEnergy.Vector (ι := Fin ((M : ℕ) - (n : ℕ))) Q hQ),
          (∀ u v,
            let P := fun x : Ω => ∑ i, ∑ j,
              (MatrixEnergy.vectorEquiv Q hQ u i).val x.val *
                PhysicalCore.properMatrix β s n m M hM (by omega) K θ ε κ₀ x i j *
                (MatrixEnergy.vectorEquiv Q hQ v j).val x.val
            Integrable P μ ∧ F u v = OperatorSchur.vectorEnergy Q hQ u v + β.val * ∫ x, P x ∂μ) ∧
          (∀ u v, G u v = G v u) ∧ (∀ u, 0 ≤ G u u) ∧
          (∀ u v, S u v = F (SchurRestriction.assemble Q hQ n M (by omega) (u,0))
            (SchurRestriction.assemble Q hQ n M (by omega) (v,0)) - G u v) ∧
          (∀ u w,
            let P := fun z z' => fun x : Ω => matrixFieldPair
              (fun _ : EuclideanSpace ℝ (Fin (n : ℕ)) => (2 : ℝ) • referenceIntervalMatrix s M hM K)
              (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n M (by omega) z) i).val)
              (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n M (by omega) z') i).val) x.val
            Integrable (P (0,R u) (0,w)) μ ∧ Integrable (P (u,0) (0,w)) μ ∧
              β.val⁻¹ * OperatorSchur.vectorEnergy Q hQ (R u) w +
                (∫ x, P (0,R u) (0,w) x ∂μ) = ∫ x, P (u,0) (0,w) x ∂μ) ∧
          (∀ u v,
            let P := fun x : Ω => matrixFieldPair
              (fun _ : EuclideanSpace ℝ (Fin (n : ℕ)) => (2 : ℝ) • referenceIntervalMatrix s M hM K)
              (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n M (by omega) (v,0)) i).val)
              (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n M (by omega) (0,R u)) i).val) x.val
            Integrable P μ ∧ G u v = β.val * ∫ x, P x ∂μ) ∧
          (∃ c : ℝ, 0 < c ∧ ∀ u, c * ‖u‖ ^ 2 ≤ S u u) ∧
          Aphys = S + T ∧
          (∀ u v,
            let U := fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val
            let W := fun i => (MatrixEnergy.vectorEquiv Q hQ v i).val
            let A₀ := PhysicalCore.properActive β s n m M hM (by omega) K θ ε κ₀
            let P := fun x : Ω => ∑ i, ∑ j, U i x.val * A₀ x i j * W j x.val
            let D := fun x : Ω => ∑ i, ∑ j,
              U i x.val * (hessianMatrix V x.val i j - β.val * A₀ x i j) * W j x.val
            Integrable (matrixFieldPair (hessianMatrix V) U W) ν ∧
              Aphys u v = OperatorSchur.vectorEnergy Q hQ u v +
                ∫ x, matrixFieldPair (hessianMatrix V) U W x ∂ν ∧
              T u v = Aphys u v - F (SchurRestriction.assemble Q hQ n M (by omega) (u,0))
                (SchurRestriction.assemble Q hQ n M (by omega) (v,0)) + G u v ∧
              Integrable P μ ∧ S u v = OperatorSchur.vectorEnergy Q hQ u v +
                β.val * (∫ x, P x ∂μ) - G u v ∧
              Integrable D μ ∧ T u v = (∫ x, D x ∂μ) + G u v) ∧
          (∀ f : PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν),
            (∃! v, ∀ z, S v z = inner ℝ f (OperatorSchur.vectorValues Q hQ z)) ∧
            (∃! ψ, ∀ z, Aphys ψ z = inner ℝ f (OperatorSchur.vectorValues Q hQ z))) ∧
          0 < a ∧ ∀ (f : PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν)) (v ψ),
            (∀ z, S v z = inner ℝ f (OperatorSchur.vectorValues Q hQ z)) →
            (∀ z, Aphys ψ z = inner ℝ f (OperatorSchur.vectorValues Q hQ z)) →
            (∀ z, Aphys (v - ψ) z = T v z) ∧
              β.val * a * ‖OperatorSchur.vectorValues Q hQ (v - ψ)‖ ^ 2 +
                OperatorSchur.vectorEnergy Q hQ (v - ψ) (v - ψ) ≤ T v (v - ψ) := by
  intro p hnp ν Ω μ V a
  obtain ⟨Q, hreal, hQ, hdom, Hphys, hHphys, hcore⟩ := proper_core_forms β s n m θ ε κ₀
  have hco : MeasurePreserving ((↑) : Ω → EuclideanSpace ℝ (Fin (n : ℕ))) μ ν := by
    refine ⟨measurable_subtype_coe, ?_⟩
    rw [map_comap_subtype_coe (AffineSimplex.isOpen_chartDomain n _).measurableSet]
    exact Measure.restrict_eq_self_of_ae_mem (IntrinsicScalarCore.supported
      (AffineSimplex.isOpen_chartDomain n _) (PhysicalFormDomain.proper_gibbs_potential β s n m θ ε))
  obtain ⟨F,S,G,R,hF,hGs,hG0,hSform,hR,hG,c,hc,hS⟩ :=
    Internal.proper_auxiliary_forms β s n m hn M hM hnM K hK hKM θ ε κ₀ hε Q hQ hco
  obtain ⟨B,Dmul,hHD,hBD⟩ := hcore M hM (by omega) K
  have hFa := Internal.proper_active_form β s n m M hM (by omega) K θ ε κ₀ Q hQ hco B
    (fun u v => ⟨(hBD u v).1,(hBD u v).2.1⟩) F hF
  let Aphys := OperatorSchur.vectorEnergy Q hQ + Hphys
  let T := Aphys - S
  have hident : Aphys = S + T := by dsimp only [T]; abel
  obtain ⟨ha,hlo⟩ := proper_physical_lower β s n m θ ε hε
  have hsolve := Internal.form_source_comparison Q hQ (hessianMatrix V) Hphys hHphys
    (β.val * a) (mul_pos β.property ha) hlo S T hident
  refine ⟨Q,hreal,hQ,hdom,F,S,G,Aphys,T,R,hF,hGs,hG0,hSform,hR,hG,
    ⟨c,hc,hS⟩,hident,?_,?_,ha,hsolve.2⟩
  · intro u v U W A₀ P D
    obtain ⟨hPi,hBi,hDi,hDi'⟩ := hBD u v
    refine ⟨(hHphys u v).1, ?_, ?_, hPi, ?_, hDi, ?_⟩
    · change OperatorSchur.vectorEnergy Q hQ u v + Hphys u v = _
      rw [(hHphys u v).2]
    · change Aphys u v - S u v = _
      rw [hSform]
      ring
    · rw [hSform,hFa,hBi]
    · change Aphys u v - S u v = _
      rw [hSform,hFa]
      have he := congrArg (fun L => L u v) hHD
      change Hphys u v = β.val * B u v + Dmul u v at he
      change OperatorSchur.vectorEnergy Q hQ u v + Hphys u v -
        (OperatorSchur.vectorEnergy Q hQ u v + β.val * B u v - G u v) = _
      rw [he,hDi']
      ring
  · intro f
    refine ⟨?_, hsolve.1 f⟩
    simpa only [CoerciveSolution.forcing_apply] using CoerciveSolution.inverse_existsUnique
      S c hc hS (CoerciveSolution.forcing (OperatorSchur.vectorValues Q hQ) f)

end Riesz2.PhysicalIdentity
