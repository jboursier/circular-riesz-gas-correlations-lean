/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.FixedLengthDecayPart2
public import Riesz2.Thermodynamic.InterpolationPerturbation
public import Riesz2.Thermodynamic.InterpolationMatrixPart2
public import Riesz2.ToMathlib.BoundedL2Pairings

/-!
# Fixed-length comparison: bounded perturbation tests

Internal helpers for Lemma 6.4. Multiplication coefficients may be unbounded. Linearity
is asserted on the submodule of bounded L² classes, with all cross integrals justified
before finite column expansion.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical MatrixOrder ENNReal

namespace Riesz2.FixedLengthDecay

section Tensors

variable {X ι : Type*} [MeasurableSpace X]
  {ν : Measure X}

/-- See Subsection 6.1 of the paper: tensorization is additive in the scalar source. -/
theorem tensor_add_internal (a : ι → ℝ) (f g : Lp ℝ 2 ν) :
    BoundarySchurBounds.tensor a (f + g) =
      BoundarySchurBounds.tensor a f + BoundarySchurBounds.tensor a g := by
  apply PiLp.ext
  intro i
  exact smul_add _ _ _

/-- See Subsection 6.1 of the paper: tensorization is homogeneous in the scalar source. -/
theorem tensor_smul_internal (a : ι → ℝ) (c : ℝ) (f : Lp ℝ 2 ν) :
    BoundarySchurBounds.tensor a (c • f) = c • BoundarySchurBounds.tensor a f := by
  apply PiLp.ext
  intro i
  exact smul_comm _ _ _

/-- See Subsection 6.1 of the paper: a signed reference-column difference is exact. -/
theorem tensor_sub_column_internal (a b : ι → ℝ) (f : Lp ℝ 2 ν) :
    BoundarySchurBounds.tensor (a - b) f =
      BoundarySchurBounds.tensor a f - BoundarySchurBounds.tensor b f := by
  apply PiLp.ext
  intro i
  exact sub_smul _ _ _

end Tensors

section NativePerturbation

variable (β : InverseTemperature) (s : Riesz1.RieszExponent)
  (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (m : ℕ+) (hm : 2 ≤ (m : ℕ))
  (hnm : (n : ℕ) ≤ (m : ℕ)) (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ (m : ℕ) / 4)
  (θ : PhysicalCutoff) (ε η t : ℝ)
  (ν : Measure (AffineSimplex.chartDomain n ((n+d : ℕ)+1)))
  (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
  (P : AffineSimplex.chartDomain n ((n+d : ℕ)+1) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)

local notation "Y" => InterpolationMatrix.multiplicationPart β s n d e hde m hm hnm k θ ε η t P
local notation "R" => InterpolationMatrix.referenceResolvent ν Q hQ s β m hm k hk hkm n
local notation "Bnd" => BoundedL2Pairings.boundedSubmodule ν

/-- See Lemma 6.4 of the paper: the native perturbation has linear scalar
rows on the entire bounded L² submodule. Its multiplication coefficient
is integrable, rather than assumed bounded as an L² operator. -/
theorem perturbation_rows_internal
    (hY : ∀ i j, Integrable (fun x => Y x i j) ν)
    (u : Fin (n : ℕ) → Bnd) :
    ∃ b : Fin (n : ℕ) → Fin (n : ℕ) → Bnd →ₗ[ℝ] ℝ,
      ∀ j i f, b j i f =
        (∫ x, (u j).val x * Y x j i * f.val x ∂ν) +
        InterpolationMatrix.schurPointPair ν Q hQ s β m hm k hk hkm n
          (u j).val f.val (j.castLE hnm) (i.castLE hnm) := by
  let b (j i : Fin (n : ℕ)) : Bnd →ₗ[ℝ] ℝ :=
    { toFun := fun f => BoundedL2Pairings.coefficientPair _ (hY j i) (u j) f +
        InterpolationMatrix.schurPointPair ν Q hQ s β m hm k hk hkm n
          (u j).val f.val (j.castLE hnm) (i.castLE hnm)
      map_add' := by
        intro f g
        simp only [map_add, Submodule.coe_add, InterpolationMatrix.schurPointPair,
          tensor_add_internal, map_add, inner_add_right, mul_add]
        ring
      map_smul' := by
        intro c f
        simp only [map_smul, Submodule.coe_smul, InterpolationMatrix.schurPointPair,
          tensor_smul_internal, map_smul, inner_smul_right, RingHom.id_apply, smul_eq_mul]
        ring }
  exact ⟨b, fun _ _ _ => rfl⟩

/-- See Lemma 6.4 of the paper: finite column expansion of the actual full
perturbation pairing, including its full-domain exterior resolvent. -/
theorem perturbation_column_expansion_internal
    (hY : ∀ i j, Integrable (fun x => Y x i j) ν)
    (u v : Fin (n : ℕ) → Bnd) :
    ∃ hint : Integrable (matrixFieldPair Y (fun i => (u i).val) (fun i => (v i).val)) ν,
      InterpolationMatrix.perturbationPair β s n d e hde m hm hnm k hk hkm
        θ ε η t ν Q hQ P (fun i => (u i).val) (fun i => (v i).val) hint =
      ∑ j, ∑ i, ((∫ x, (u j).val x * Y x j i * (v i).val x ∂ν) +
        InterpolationMatrix.schurPointPair ν Q hQ s β m hm k hk hkm n
          (u j).val (v i).val (j.castLE hnm) (i.castLE hnm)) := by
  have hi (j i : Fin (n : ℕ)) :=
    BoundedL2Pairings.integrable_product _ (hY j i) (u j) (v i)
  have hint : Integrable (matrixFieldPair Y (fun i => (u i).val) (fun i => (v i).val)) ν :=
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ => hi j i
  refine ⟨hint, ?_⟩
  have hmul : (∫ x, matrixFieldPair Y (fun i => (u i).val) (fun i => (v i).val) x ∂ν) =
      ∑ j, ∑ i, ∫ x, (u j).val x * Y x j i * (v i).val x ∂ν := by
    change (∫ x, ∑ j, ∑ i, (u j).val x * Y x j i * (v i).val x ∂ν) = _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      exact integral_finsetSum _ fun i _ => hi j i
    · intro j _
      exact integrable_finsetSum _ fun i _ => hi j i
  let a := fun j => BoundarySchurBounds.tensor
    (InterpolationMatrix.referenceColumn s m hm k n (j.castLE hnm)) (u j).val
  let b := fun i => BoundarySchurBounds.tensor
    (InterpolationMatrix.referenceColumn s m hm k n (i.castLE hnm)) (v i).val
  let J := OperatorSchur.vectorValues (ι := InterpolationMatrix.exteriorIndices m n) Q hQ
  have hschur : β.val ^ 2 * inner ℝ (∑ j, a j) (J (R (∑ i, b i))) =
      ∑ j, ∑ i, β.val ^ 2 * inner ℝ (a j) (J (R (b i))) := by
    rw [map_sum, map_sum, sum_inner]
    simp only [inner_sum, Finset.mul_sum]
  change (∫ x, matrixFieldPair Y (fun i => (u i).val) (fun i => (v i).val) x ∂ν) +
    β.val ^ 2 * inner ℝ (∑ j, a j) (J (R (∑ i, b i))) = _
  rw [hmul, hschur]
  simp only [Finset.sum_add_distrib]
  rfl

/-- See Lemma 6.4 of the paper: the difference of the native scalar rows
has precisely the signed column-increment Schur contribution. -/
theorem perturbation_row_increment_internal
    (hY : ∀ i j, Integrable (fun x => Y x i j) ν)
    (φ f : Bnd) (j i l : Fin (n : ℕ)) :
    ((∫ x, φ.val x * Y x j i * f.val x ∂ν) +
      InterpolationMatrix.schurPointPair ν Q hQ s β m hm k hk hkm n
        φ.val f.val (j.castLE hnm) (i.castLE hnm)) -
    ((∫ x, φ.val x * Y x j l * f.val x ∂ν) +
      InterpolationMatrix.schurPointPair ν Q hQ s β m hm k hk hkm n
        φ.val f.val (j.castLE hnm) (l.castLE hnm)) =
    (∫ x, φ.val x * f.val x * (Y x j i - Y x j l) ∂ν) +
      InterpolationMatrix.schurIncrementPair ν Q hQ s β m hm k hk hkm n
        φ.val f.val (j.castLE hnm) (i.castLE hnm) (l.castLE hnm) := by
  rw [add_sub_add_comm, ← integral_sub
    (BoundedL2Pairings.integrable_product _ (hY j i) φ f)
    (BoundedL2Pairings.integrable_product _ (hY j l) φ f)]
  congr 1
  · apply integral_congr_ae
    exact ae_of_all _ fun x => by ring
  · simp only [InterpolationMatrix.schurPointPair, InterpolationMatrix.schurIncrementPair,
      tensor_sub_column_internal, map_sub, inner_sub_right, mul_sub]

end NativePerturbation

section NaturalDefect

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- See Lemma 6.4 of the paper: subtract a bounded auxiliary multiplication
form on the existing physical natural carrier, without a boundedness
assumption on the physical coefficients. -/
theorem natural_matrix_defect_internal (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H A : X → Matrix ι ι ℝ) (hH : ∀ᵐ x ∂ν, (H x).PosSemidef)
    (hAm : ∀ i j, Measurable (fun x => A x i j))
    (hAb : ∃ b : ℝ, ∀ᵐ x ∂ν, ∀ i j, |A x i j| ≤ b)
    (hA : ∀ᵐ x ∂ν, (A x).PosSemidef)
    (u v : MatrixEnergy.Natural Q hQ H ⊤ hH) :
    let b := MatrixEnergy.base (ι := ι) (κ := ι)
      (MatrixEnergy.vectorValue Q hQ) (fun x => CFC.sqrt (H x)) ⊤
    let U := fun i => (MatrixEnergy.tuple Q hQ H ⊤ hH u i).val
    let V := fun i => (MatrixEnergy.tuple Q hQ H ⊤ hH v i).val
    Integrable (matrixFieldPair (fun x => H x - A x) U V) ν ∧
      MatrixEnergy.weakForm Q hQ H ⊤ hH u v -
        BoundedMatrixForms.form Q hQ A hAm hAb hA (b u) (b v) =
          ∫ x, matrixFieldPair (fun x => H x - A x) U V x ∂ν := by
  intro b U V
  have he : matrixFieldPair (fun x => H x - A x) U V =ᵐ[ν]
      fun x => matrixFieldPair H U V x - matrixFieldPair A U V x := by
    apply ae_of_all
    intro x
    simp only [matrixFieldPair, Matrix.sub_apply, mul_sub, sub_mul,
      Finset.sum_sub_distrib]
  have hi := MatrixEnergy.integrable_pair Q hQ H ⊤ hH u v
  have ha := BoundedMatrixForms.integrable_pair A hAm hAb U V
  refine ⟨(hi.sub ha).congr he.symm, ?_⟩
  have ht (w : MatrixEnergy.Natural Q hQ H ⊤ hH) :
      MatrixEnergy.vectorEquiv Q hQ (b w) = MatrixEnergy.tuple Q hQ H ⊤ hH w := rfl
  rw [MatrixEnergy.weakForm_apply, BoundedMatrixForms.form_apply, ht, ht,
    add_sub_add_left_eq_sub, ← integral_sub hi ha]
  exact integral_congr_ae he.symm

end NaturalDefect

section PhysicalDefect

variable (β : InverseTemperature) (s : Riesz1.RieszExponent)
  (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (m : ℕ+) (hm : 2 ≤ (m : ℕ))
  (hnm : (n : ℕ) ≤ (m : ℕ)) (k : ℕ)
  (θ : PhysicalCutoff) (ε η t : ℝ)
  (ν : Measure (AffineSimplex.chartDomain n ((n+d : ℕ)+1)))
  (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
  (P : AffineSimplex.chartDomain n ((n+d : ℕ)+1) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)

local notation "A0" => fun x => β.val •
  InterpolationMatrix.activeBlock β s n d e hde m hm hnm k θ ε η t x
local notation "M" => InterpolationMatrix.matrix β s n d e hde m hm hnm k θ ε η t
local notation "H" => fun x : AffineSimplex.chartDomain n ((n+d : ℕ)+1) =>
  β.val • (InterpolationMatrix.penaltyHessian n θ ε (Subtype.val x) + P x)
local notation "Y" => InterpolationMatrix.multiplicationPart β s n d e hde m hm hnm k θ ε η t P

/-- See Lemma 6.4 of the paper: the all-size matrix clause of
Subsection 6.1 supplies all three inputs to the active bounded-matrix form. -/
theorem active_form_data_internal (C κ γ : ℝ) (hC : 1 ≤ C)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm k C κ γ η M) :
    (∀ i j, Measurable (fun x => A0 x i j)) ∧
    (∃ b : ℝ, ∀ᵐ x ∂ν, ∀ i j, |A0 x i j| ≤ b) ∧
    (∀ᵐ x ∂ν, (A0 x).PosSemidef) := by
  have he (x) : (β.val • M x).submatrix (Fin.castLE hnm) (Fin.castLE hnm) = A0 x := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.smul_apply,
      InterpolationMatrix.matrix_active]
  refine ⟨fun i j => (InterpolationMatrix.measurable_activeBlock
    β s n d e hde m hm hnm k θ ε η t i j).const_mul β.val, ?_, ?_⟩
  · obtain ⟨b, hb⟩ := SchurRestriction.periodized_scaled_bounded β.val hM
    exact ⟨b, hb.mono fun x hx i j => by
      have hh := hx (i.castLE hnm) (j.castLE hnm)
      simpa only [Matrix.smul_apply, InterpolationMatrix.matrix_active] using hh⟩
  · filter_upwards [SchurRestriction.periodized_scaled_psd β.val β.property hC hM] with x hx
    have hh := hx.submatrix (Fin.castLE hnm)
    rw [he x] at hh
    exact hh

/-- See Lemma 6.4 of the paper: exact multiplication defect on the physical
natural form domain. The two scalar diffusion forms cancel literally.
Integrability of the defect follows from the two existing cross pairings. -/
theorem physical_multiplication_defect_internal
    (hH : ∀ᵐ x ∂ν, (H x).PosSemidef)
    (hAm : ∀ i j, Measurable (fun x => A0 x i j))
    (hAb : ∃ b : ℝ, ∀ᵐ x ∂ν, ∀ i j, |A0 x i j| ≤ b)
    (hA : ∀ᵐ x ∂ν, (A0 x).PosSemidef)
    (u v : MatrixEnergy.Natural Q hQ H ⊤ hH) :
    let b := MatrixEnergy.base (ι := Fin (n : ℕ)) (κ := Fin (n : ℕ))
      (MatrixEnergy.vectorValue Q hQ) (fun x => CFC.sqrt (H x)) ⊤
    let U := fun i => (MatrixEnergy.tuple Q hQ H ⊤ hH u i).val
    let V := fun i => (MatrixEnergy.tuple Q hQ H ⊤ hH v i).val
    Integrable (matrixFieldPair Y U V) ν ∧
      MatrixEnergy.weakForm Q hQ H ⊤ hH u v -
        BoundedMatrixForms.form Q hQ A0 hAm hAb hA (b u) (b v) =
          ∫ x, matrixFieldPair Y U V x ∂ν := by
  have he : Y = fun x => H x - A0 x := by
    funext x
    rw [InterpolationMatrix.multiplicationPart_eq_defect, smul_sub]
  rw [he]
  exact natural_matrix_defect_internal Q hQ H A0 hH hAm hAb hA u v

end PhysicalDefect

section NormalRows

/-- See Lemma 6.4 of the paper: the long-range auxiliary normal row bound
follows from the interval clause of Subsection 6.1, on the entire
scalar carrier. The component period contributes no factor. -/
theorem periodized_active_normal_rows_internal {X : Type*} [MeasurableSpace X]
    {ν : Measure X} (s : Riesz1.RieszExponent) (n m : ℕ+)
    (hm : 2 ≤ (m : ℕ)) (hnm : 2 * (n : ℕ) ≤ (m : ℕ))
    (k : ℕ) (C κ γ η : ℝ) (hC : 0 ≤ C)
    (M : X → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm k C κ γ η M) :
    ∀ᵐ x ∂ν, (∑ i : Fin (n : ℕ), ∑ j : Fin (n : ℕ),
      M x (i.castLE (by omega)) (j.castLE (by omega))) ≤
      (C * (1 + 1 / s.val) * (2 / (1 - s.val))) *
        (n : ℝ) ^ (κ * η) * (n : ℝ) ^ (2 - s.val) := by
  obtain ⟨a, _, ha⟩ := DerivativeCommutators.periodized_interval_entries s n m hm k C κ γ η M hM
  filter_upwards [ha] with x hx
  have he (i j : Fin (n : ℕ)) :
      M x (i.castLE (by omega)) (j.castLE (by omega)) ≤
        (C * (n : ℝ) ^ (κ * η)) * (1 + 1 / s.val) *
          weightRadius m (i.castLE (by omega)) (j.castLE (by omega)) ^ (-s.val) := by
    apply (le_abs_self _).trans
    rw [hx.2]
    exact PhysicalCore.Internal.signed_interval_entry_bound m s.property.1
      (by positivity) (fun i r => a i r x)
      (fun i r => by simpa only [abs_of_nonneg (hx.1 i r).1,
        Nat.cast_add, Nat.cast_one] using (hx.1 i r).2.1) _ _
  have hr (i : Fin (n : ℕ)) :
      (∑ j : Fin (n : ℕ), M x (i.castLE (by omega)) (j.castLE (by omega))) ≤
        ((C * (n : ℝ) ^ (κ * η)) * (1 + 1 / s.val)) *
          ((2 / (1 - s.val)) * (n : ℝ) ^ (1 - s.val)) := by
    apply (Finset.sum_le_sum fun j _ => he i j).trans
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left
      (LocalizedBoundary.active_weight_sum_internal n m hnm i s.val s.property.1 s.property.2)
      (by have := s.property.1; positivity)
  apply (Finset.sum_le_sum fun i _ => hr i).trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hp : (n : ℝ) * (n : ℝ) ^ (1 - s.val) = (n : ℝ) ^ (2 - s.val) := by
    nth_rw 1 [← Real.rpow_one (n : ℝ)]
    rw [← Real.rpow_add (by positivity : (0 : ℝ) < n)]
    congr 1
    ring
  calc
    _ = (C * (1 + 1 / s.val) * (2 / (1 - s.val))) * (n : ℝ) ^ (κ * η) *
        ((n : ℝ) * (n : ℝ) ^ (1 - s.val)) := by ring
    _ = _ := by rw [hp]

/-- See Lemma 6.4 of the paper: the exceptional weight is bounded on the
actual rigidity event, including the smallest active sizes. -/
theorem exceptionalWeight_good_bound_internal (s : Riesz1.RieszExponent)
    (n : ℕ+) (d : ℕ) (η : ℝ)
    (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1))
    (hx : x ∈ InterpolationMatrix.goodSet s n d η) :
    InterpolantLocalLaws.exceptionalWeight s.val (WithLp.ofLp x.val) ≤
      1 + (n : ℝ) * (n : ℝ) ^ (η * (4 * s.val + 12)) := by
  have hx' := hx.2.1
  have hb (i : Fin (n : ℕ)) :
      (x.val i) ^ (-4 * s.val - 12) ≤ (n : ℝ) ^ (η * (4 * s.val + 12)) := by
    have hh := Real.rpow_le_rpow_of_nonpos
      (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < n) (-η))
      (hx' i).1 (by linarith [s.property.1] : -4 * s.val - 12 ≤ 0)
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ n)] at hh
    simpa only [show -η * (-4 * s.val - 12) = η * (4 * s.val + 12) by ring] using hh
  change 1 + (∑ i, (x.val i) ^ (-4 * s.val - 12)) ≤ _
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ _i : Fin (n : ℕ), (n : ℝ) ^ (η * (4 * s.val + 12)) :=
      Finset.sum_le_sum fun i _ => hb i
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- See Lemma 6.4 of the paper: the exceptional weighted-tail conclusion
implies integrability of the whole weight. Its good branch is proved
bounded, rather than assumed to have any moments. -/
theorem exceptionalWeight_integrable_internal (s : Riesz1.RieszExponent)
    (n : ℕ+) (d : ℕ) (η : ℝ)
    (ν : Measure (AffineSimplex.chartDomain n ((n+d : ℕ)+1))) [IsProbabilityMeasure ν]
    (hbad : IntegrableOn
      (fun x => InterpolantLocalLaws.exceptionalWeight s.val (WithLp.ofLp x.val))
      (InterpolationMatrix.goodSet s n d η)ᶜ ν) :
    Integrable (fun x => InterpolantLocalLaws.exceptionalWeight s.val (WithLp.ofLp x.val)) ν := by
  have hm := InterpolantLocalLaws.measurable_exceptionalWeight s.val
    (fun x : AffineSimplex.chartDomain n ((n+d : ℕ)+1) => WithLp.ofLp x.val)
    (fun i => (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable.comp measurable_subtype_coe)
  have hg : IntegrableOn
      (fun x => InterpolantLocalLaws.exceptionalWeight s.val (WithLp.ofLp x.val))
      (InterpolationMatrix.goodSet s n d η) ν := by
    apply (integrable_const (1 + (n : ℝ) * (n : ℝ) ^ (η * (4 * s.val + 12)))).mono'
      hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem (InterpolationMatrix.measurableSet_goodSet s n d η)] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans
      (InterpolantLocalLaws.one_le_exceptionalWeight s.val _ (fun i => (x.property.1 i).le)))]
    exact exceptionalWeight_good_bound_internal s n d η x hx
  have hh := integrableOn_union.mpr ⟨hg, hbad⟩
  simpa only [union_compl_self, integrableOn_univ] using hh

end NormalRows

section ReferenceSchur

variable {X : Type} [MeasurableSpace X] (ν : Measure X)
  (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
  (s : Riesz1.RieszExponent) (β : InverseTemperature)
  (n m : ℕ+) (hm : 2 ≤ (m : ℕ)) (hnm : (n : ℕ) ≤ (m : ℕ))
  (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ (m : ℕ) / 4)

local notation "Eidx" => InterpolationMatrix.exteriorIndices m n
local notation "J" => OperatorSchur.vectorValues (ι := Eidx) Q hQ
local notation "JA" => OperatorSchur.vectorValues (ι := Fin (n : ℕ)) Q hQ
local notation "D" => InterpolationMatrix.referenceExteriorForm ν Q hQ s β m hm k hk hkm n
local notation "R" => InterpolationMatrix.referenceResolvent ν Q hQ s β m hm k hk hkm n

/-- See Subsection 6.1 of the paper: the reference tensor sum is a continuous
linear coupling on all active L² classes, with its exact factor β. -/
theorem reference_coupling_map_internal :
    ∃ T : PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν) →L[ℝ]
      PiLp 2 (fun _ : Eidx => Lp ℝ 2 ν),
    ∀ f, T f = β.val • ∑ i : Fin (n : ℕ), BoundarySchurBounds.tensor
      (InterpolationMatrix.referenceColumn s m hm k n (i.castLE hnm)) (f i) := by
  let T : PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν) →L[ℝ]
      PiLp 2 (fun _ : Eidx => Lp ℝ 2 ν) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Eidx => Lp ℝ 2 ν)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun a => ∑ i : Fin (n : ℕ),
        (β.val * InterpolationMatrix.referenceColumn s m hm k n (i.castLE hnm) a) •
          PiLp.proj 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν) i)
  refine ⟨T, fun f => ?_⟩
  apply PiLp.ext
  intro a
  change (∑ i : Fin (n : ℕ),
    ((β.val * InterpolationMatrix.referenceColumn s m hm k n (i.castLE hnm) a) •
      PiLp.proj 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν) i)) f = _
  simp only [sum_apply, smul_apply,
    PiLp.proj_apply]
  change (∑ i, (β.val * InterpolationMatrix.referenceColumn s m hm k n (i.castLE hnm) a) • f i) =
    β.val • (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Eidx => Lp ℝ 2 ν) a)
      (∑ i : Fin (n : ℕ), WithLp.toLp 2
        (fun b => InterpolationMatrix.referenceColumn s m hm k n (i.castLE hnm) b • f i))
  rw [map_sum, Finset.smul_sum]
  simp only [PiLp.proj_apply, smul_smul]

/-- See Lemma 6.4 of the paper: the full reference resolvent is positive
on every L² exterior source, in its original scalar form. -/
theorem reference_resolvent_positive_internal
    (f : PiLp 2 (fun _ : Eidx => Lp ℝ 2 ν)) :
    0 ≤ inner ℝ f (J (R f)) := by
  rw [← InterpolationMatrix.referenceResolvent_solves ν Q hQ s β m hm k hk hkm n f (R f)]
  exact MatrixEnergy.weakForm_nonneg Q hQ _ ⊤ _ _

/-- See Subsection 6.1 of the paper: the operator Schur reduction and the native
reference resolvent have exactly the same pairing, including β². This
uses uniqueness on the entire exterior form domain. -/
theorem reference_reduced_pair_internal
    (T : PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν) →L[ℝ]
      PiLp 2 (fun _ : Eidx => Lp ℝ 2 ν))
    (hT : ∀ f, T f = β.val • ∑ i : Fin (n : ℕ), BoundarySchurBounds.tensor
      (InterpolationMatrix.referenceColumn s m hm k n (i.castLE hnm)) (f i))
    (A : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ] ℝ)
    (a : ℝ) (ha : 0 < a) (hD : ∀ w, a * ‖w‖ ^ 2 ≤ D w w)
    (u v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ) :
    OperatorSchur.reduced A D (OperatorSchur.coupling JA J T) a ha hD u v =
      A u v - β.val ^ 2 * inner ℝ
        (∑ i : Fin (n : ℕ), BoundarySchurBounds.tensor
          (InterpolationMatrix.referenceColumn s m hm k n (i.castLE hnm)) (JA u i))
        (J (R (∑ i : Fin (n : ℕ), BoundarySchurBounds.tensor
          (InterpolationMatrix.referenceColumn s m hm k n (i.castLE hnm)) (JA v i)))) := by
  have he : OperatorSchur.exterior D (OperatorSchur.coupling JA J T) a ha hD u =
      R (T (JA u)) := by
    have hh := CoerciveSolution.inverse_unique D a ha hD
      (OperatorSchur.coupling JA J T u) (R (T (JA u)))
      (fun w => InterpolationMatrix.referenceResolvent_solves ν Q hQ s β m hm k hk hkm n _ w)
    exact hh.symm
  rw [OperatorSchur.reduced_apply, he, OperatorSchur.coupling_apply, hT, hT]
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
  rw [InterpolationMatrix.referenceResolvent_pair_symmetric ν Q hQ s β m hm k hk hkm n]
  ring

end ReferenceSchur

section PhysicalSchur

variable (β : InverseTemperature) (s : Riesz1.RieszExponent)
  (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (m : ℕ+) (hm : 2 ≤ (m : ℕ))
  (hnm : (n : ℕ) ≤ (m : ℕ)) (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ (m : ℕ) / 4)
  (θ : PhysicalCutoff) (ε η t : ℝ)
  (ν : Measure (AffineSimplex.chartDomain n ((n+d : ℕ)+1)))
  (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
  (P : AffineSimplex.chartDomain n ((n+d : ℕ)+1) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)

local notation "A0" => fun x => β.val •
  InterpolationMatrix.activeBlock β s n d e hde m hm hnm k θ ε η t x
local notation "H" => fun x : AffineSimplex.chartDomain n ((n+d : ℕ)+1) =>
  β.val • (InterpolationMatrix.penaltyHessian n θ ε (Subtype.val x) + P x)
local notation "Y" => InterpolationMatrix.multiplicationPart β s n d e hde m hm hnm k θ ε η t P
local notation "Eidx" => InterpolationMatrix.exteriorIndices m n
local notation "J" => OperatorSchur.vectorValues (ι := Eidx) Q hQ
local notation "JA" => OperatorSchur.vectorValues (ι := Fin (n : ℕ)) Q hQ
local notation "D" => InterpolationMatrix.referenceExteriorForm ν Q hQ s β m hm k hk hkm n

/-- See Lemma 6.4 of the paper: the physical natural form minus the pulled
back native Schur reduction is precisely the existing full perturbation
pairing. All multiplication integrals are proved finite on this domain.
The coupling map is supplied by `reference_coupling_map_internal`. -/
theorem physical_schur_comparison_internal
    (hH : ∀ᵐ x ∂ν, (H x).PosSemidef)
    (hAm : ∀ i j, Measurable (fun x => A0 x i j))
    (hAb : ∃ b : ℝ, ∀ᵐ x ∂ν, ∀ i j, |A0 x i j| ≤ b)
    (hA : ∀ᵐ x ∂ν, (A0 x).PosSemidef)
    (T : PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν) →L[ℝ]
      PiLp 2 (fun _ : Eidx => Lp ℝ 2 ν))
    (hT : ∀ f, T f = β.val • ∑ i : Fin (n : ℕ), BoundarySchurBounds.tensor
      (InterpolationMatrix.referenceColumn s m hm k n (i.castLE hnm)) (f i))
    (a : ℝ) (ha : 0 < a) (hD : ∀ w, a * ‖w‖ ^ 2 ≤ D w w)
    (u v : MatrixEnergy.Natural Q hQ H ⊤ hH) :
    let b := MatrixEnergy.base (ι := Fin (n : ℕ)) (κ := Fin (n : ℕ))
      (MatrixEnergy.vectorValue Q hQ) (fun x => CFC.sqrt (H x)) ⊤
    let A := BoundedMatrixForms.form Q hQ A0 hAm hAb hA
    let U := fun i => (MatrixEnergy.tuple Q hQ H ⊤ hH u i).val
    let V := fun i => (MatrixEnergy.tuple Q hQ H ⊤ hH v i).val
    ∃ hint : Integrable (matrixFieldPair Y U V) ν,
      MatrixEnergy.weakForm Q hQ H ⊤ hH u v -
        OperatorSchur.reduced A D (OperatorSchur.coupling JA J T) a ha hD (b u) (b v) =
      InterpolationMatrix.perturbationPair β s n d e hde m hm hnm k hk hkm
        θ ε η t ν Q hQ P U V hint := by
  intro b A U V
  obtain ⟨hint, hdef⟩ := physical_multiplication_defect_internal β s n d e hde m hm hnm k
    θ ε η t ν Q hQ P hH hAm hAb hA u v
  refine ⟨hint, ?_⟩
  rw [reference_reduced_pair_internal ν Q hQ s β n m hm hnm k hk hkm T hT A a ha hD]
  change MatrixEnergy.weakForm Q hQ H ⊤ hH u v - (A (b u) (b v) -
    β.val ^ 2 * inner ℝ
      (∑ i : Fin (n : ℕ), BoundarySchurBounds.tensor
        (InterpolationMatrix.referenceColumn s m hm k n (i.castLE hnm)) (U i))
      (OperatorSchur.vectorValues Q hQ (InterpolationMatrix.referenceResolvent ν Q hQ s β m hm k hk hkm n
        (∑ i : Fin (n : ℕ), BoundarySchurBounds.tensor
          (InterpolationMatrix.referenceColumn s m hm k n (i.castLE hnm)) (V i))))) = _
  unfold InterpolationMatrix.perturbationPair
  linarith only [hdef]

/-- See Lemma 6.4 of the paper: the whole-simplex square conclusion of
Subsection 6.1 and the actual exceptional weighted tail imply
integrability of every physical Hessian coefficient. -/
theorem physical_coefficients_integrable_internal [IsProbabilityMeasure ν]
    (hPm : ∀ i j, Measurable (fun x => P x i j))
    (B : ℝ) (_hB : 0 ≤ B)
    (hsq : ∀ x, ∀ i j, |P x i j| ^ 2 +
      |InterpolationMatrix.penaltyHessian n θ ε x.val i j| ^ 2 ≤
      B * (n : ℝ) ^ B * InterpolantLocalLaws.exceptionalWeight s.val (WithLp.ofLp x.val))
    (hbad : IntegrableOn
      (fun x => InterpolantLocalLaws.exceptionalWeight s.val (WithLp.ofLp x.val))
      (InterpolationMatrix.goodSet s n d η)ᶜ ν) :
    ∀ i j, Integrable (fun x => H x i j) ν := by
  have hW := exceptionalWeight_integrable_internal s n d η ν hbad
  intro i j
  have hm : Measurable (fun x => H x i j) :=
    (((InterpolationMatrix.measurable_penaltyHessian n θ ε i j).comp measurable_subtype_coe).add
      (hPm i j)).const_mul β.val
  have hs : Integrable (fun x => (H x i j) ^ 2) ν := by
    apply (hW.const_mul (2 * β.val ^ 2 * (B * (n : ℝ) ^ B))).mono'
      (hm.pow_const 2).aestronglyMeasurable
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs, abs_sq]
    have hh := hsq x i j
    simp only [sq_abs] at hh
    have hab : (InterpolationMatrix.penaltyHessian n θ ε x.val i j + P x i j) ^ 2 ≤
        2 * (B * (n : ℝ) ^ B *
          InterpolantLocalLaws.exceptionalWeight s.val (WithLp.ofLp x.val)) := by
      nlinarith [sq_nonneg (InterpolationMatrix.penaltyHessian n θ ε x.val i j - P x i j)]
    have hb := mul_le_mul_of_nonneg_left hab (sq_nonneg β.val)
    simpa only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, mul_pow,
      mul_assoc, mul_left_comm, mul_comm] using hb
  exact MomentEvent.integrable_of_integrable_sq hm hs

/-- See Lemma 6.4 of the paper: the exact matrix and square-envelope
conclusions of Subsection 6.1, together with the weighted local
law, supply every coefficient-integrability input of the bounded-row
construction and of the physical normal-energy comparison. -/
theorem physical_perturbation_coefficients_integrable_internal [IsProbabilityMeasure ν]
    (C κ γ : ℝ) (hC : 1 ≤ C)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm k C κ γ η
      (InterpolationMatrix.matrix β s n d e hde m hm hnm k θ ε η t))
    (hPm : ∀ i j, Measurable (fun x => P x i j))
    (B : ℝ) (hB : 0 ≤ B)
    (hsq : ∀ x, ∀ i j, |P x i j| ^ 2 +
      |InterpolationMatrix.penaltyHessian n θ ε x.val i j| ^ 2 ≤
      B * (n : ℝ) ^ B * InterpolantLocalLaws.exceptionalWeight s.val (WithLp.ofLp x.val))
    (hbad : IntegrableOn
      (fun x => InterpolantLocalLaws.exceptionalWeight s.val (WithLp.ofLp x.val))
      (InterpolationMatrix.goodSet s n d η)ᶜ ν) :
    (∀ i j, Integrable (fun x => H x i j) ν) ∧
    (∀ i j, Integrable (fun x => Y x i j) ν) := by
  have hHi := physical_coefficients_integrable_internal β s n d θ ε η ν P hPm B hB hsq hbad
  obtain ⟨hAm, ⟨b, hb⟩, _⟩ := active_form_data_internal β s n d e hde m hm hnm k
    θ ε η t ν C κ γ hC hM
  have hAi (i j : Fin (n : ℕ)) : Integrable (fun x => A0 x i j) ν :=
    (integrable_const b).mono' (hAm i j).aestronglyMeasurable
      (hb.mono fun x hx => by simpa only [Real.norm_eq_abs] using hx i j)
  have he : Y = fun x => H x - A0 x := by
    funext x
    rw [InterpolationMatrix.multiplicationPart_eq_defect, smul_sub]
  refine ⟨hHi, ?_⟩
  intro i j
  rw [he]
  exact (hHi i j).sub (hAi i j)

end PhysicalSchur

section NormalForm

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- See Lemma 6.4 of the paper: the normal energy of the bounded active
form uses the actual scalar mean and the entire intrinsic diffusion. -/
theorem bounded_normal_energy_internal (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (n : ℕ+)
    (A : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (hAm : ∀ i j, Measurable (fun x => A x i j))
    (hAb : ∃ b : ℝ, ∀ᵐ x ∂ν, ∀ i j, |A x i j| ≤ b)
    (hA : ∀ᵐ x ∂ν, (A x).PosSemidef)
    (S : Q.1) (v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ)
    (hv : ∀ i, MatrixEnergy.vectorEquiv Q hQ v i = (n : ℝ)⁻¹ • S)
    (K : ℝ) (hrow : ∀ᵐ x ∂ν, (∑ i, ∑ j, A x i j) ≤ K) :
    BoundedMatrixForms.form Q hQ A hAm hAb hA v v ≤
      (n : ℝ)⁻¹ * Q.2 S S + K * ‖((n : ℝ)⁻¹ • S).val‖ ^ 2 := by
  rw [BoundedMatrixForms.form_apply]
  simp_rw [hv]
  rw [normal_diffusion_energy]
  apply add_le_add le_rfl
  let f : Lp ℝ 2 ν := ((n : ℝ)⁻¹ • S).val
  have he : matrixFieldPair A (fun _ : Fin (n : ℕ) => f) (fun _ : Fin (n : ℕ) => f) =
      fun x => f x ^ 2 * ∑ i, ∑ j, A x i j := by
    funext x
    simp only [matrixFieldPair, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hi := BoundedMatrixForms.integrable_pair A hAm hAb
    (fun _ : Fin (n : ℕ) => f) (fun _ : Fin (n : ℕ) => f)
  have hf : Integrable (fun x => f x ^ 2) ν := (Lp.memLp f).integrable_sq
  have hn : (∫ x, f x ^ 2 ∂ν) = ‖f‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    exact integral_congr_ae (ae_of_all _ fun x => by simp only [Real.inner_apply, pow_two])
  change (∫ x, matrixFieldPair A (fun _ => f) (fun _ => f) x ∂ν) ≤ K * ‖f‖ ^ 2
  calc
    _ ≤ ∫ x, K * f x ^ 2 ∂ν := by
      apply integral_mono_ae hi (hf.const_mul K)
      rw [he]
      filter_upwards [hrow] with x hx
      nlinarith only [mul_le_mul_of_nonneg_left hx (sq_nonneg (f x))]
    _ = _ := by rw [integral_const_mul, hn]

end NormalForm

section NormalPerturbation

variable (β : InverseTemperature) (s : Riesz1.RieszExponent)
  (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (m : ℕ+) (hm : 2 ≤ (m : ℕ))
  (hnm : (n : ℕ) ≤ (m : ℕ)) (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ (m : ℕ) / 4)
  (θ : PhysicalCutoff) (ε η t : ℝ)
  (ν : Measure (AffineSimplex.chartDomain n ((n+d : ℕ)+1)))
  (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
  (P : AffineSimplex.chartDomain n ((n+d : ℕ)+1) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)

local notation "Y" => InterpolationMatrix.multiplicationPart β s n d e hde m hm hnm k θ ε η t P
local notation "w" => InteractionDifferential.boundaryWeight s.val n
local notation "Bnd" => BoundedL2Pairings.boundedSubmodule ν

/-- See Lemma 6.4 of the paper: sum the exact point-pair conclusion of
Subsection 6.1 on a constant normal tuple. Both endpoint weights
are retained, and the exceptional term has exactly the finite factor n². -/
theorem normal_perturbation_bound_internal
    (hY : ∀ i j, Integrable (fun x => Y x i j) ν)
    (f : Bnd) (A Err U : ℝ)
    (hpoint : ∀ j i : Fin (n : ℕ),
      |(∫ x, f.val x * Y x j i * f.val x ∂ν) +
        InterpolationMatrix.schurPointPair ν Q hQ s β m hm k hk hkm n
          f.val f.val (j.castLE hnm) (i.castLE hnm)| ≤
      A * w j * w i * ‖f.val‖ ^ 2 + Err * U ^ 2) :
    ∃ hint : Integrable (matrixFieldPair Y (fun _ => f.val) (fun _ => f.val)) ν,
      InterpolationMatrix.perturbationPair β s n d e hde m hm hnm k hk hkm
        θ ε η t ν Q hQ P (fun _ => f.val) (fun _ => f.val) hint ≤
      A * (∑ j, w j) ^ 2 * ‖f.val‖ ^ 2 + (n : ℝ) ^ 2 * Err * U ^ 2 := by
  obtain ⟨hint, hexp⟩ := perturbation_column_expansion_internal β s n d e hde m hm hnm k hk hkm
    θ ε η t ν Q hQ P hY (fun _ => f) (fun _ => f)
  refine ⟨hint, ?_⟩
  rw [hexp]
  apply (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ =>
    (le_abs_self _).trans (hpoint j i)).trans_eq
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

end NormalPerturbation

section PhysicalNormal

variable (β : InverseTemperature) (s : Riesz1.RieszExponent)
  (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (m : ℕ+) (hm : 2 ≤ (m : ℕ))
  (hnm : 2 * (n : ℕ) ≤ (m : ℕ)) (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ (m : ℕ) / 4)
  (θ : PhysicalCutoff) (ε η t : ℝ)
  (ν : Measure (AffineSimplex.chartDomain n ((n+d : ℕ)+1)))
  (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
  (P : AffineSimplex.chartDomain n ((n+d : ℕ)+1) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)

local notation "A0" => fun x => β.val •
  InterpolationMatrix.activeBlock β s n d e hde m hm (by omega) k θ ε η t x
local notation "H" => fun x : AffineSimplex.chartDomain n ((n+d : ℕ)+1) =>
  β.val • (InterpolationMatrix.penaltyHessian n θ ε (Subtype.val x) + P x)
local notation "Y" => InterpolationMatrix.multiplicationPart β s n d e hde m hm (by omega) k θ ε η t P
local notation "M" => InterpolationMatrix.matrix β s n d e hde m hm (by omega) k θ ε η t
local notation "w" => InteractionDifferential.boundaryWeight s.val n

/-- See Lemma 6.4 of the paper: physical long-range normal energy from the
literal all-size matrix conclusion and the literal point-test perturbation
bound of Subsection 6.1. Positivity removes the Schur correction. -/
theorem physical_long_normal_energy_internal
    (C κ γ : ℝ) (hC : 1 ≤ C)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm k C κ γ η M)
    (hH : ∀ᵐ x ∂ν, (H x).PosSemidef)
    (hY : ∀ i j, Integrable (fun x => Y x i j) ν)
    (S : Q.1) (r : MatrixEnergy.Natural Q hQ H ⊤ hH)
    (hr : ∀ i, MatrixEnergy.tuple Q hQ H ⊤ hH r i = (n : ℝ)⁻¹ • S)
    (A Err U : ℝ)
    (hf : ∀ᵐ x ∂ν, |((n : ℝ)⁻¹ • S).val x| ≤ U)
    (hpoint : ∀ j i : Fin (n : ℕ),
      |(∫ x, ((n : ℝ)⁻¹ • S).val x * Y x j i * ((n : ℝ)⁻¹ • S).val x ∂ν) +
        InterpolationMatrix.schurPointPair ν Q hQ s β m hm k hk hkm n
          ((n : ℝ)⁻¹ • S).val ((n : ℝ)⁻¹ • S).val (j.castLE (by omega)) (i.castLE (by omega))| ≤
      A * w j * w i * ‖((n : ℝ)⁻¹ • S).val‖ ^ 2 + Err * U ^ 2) :
    MatrixEnergy.weakForm Q hQ H ⊤ hH r r ≤
      (n : ℝ)⁻¹ * Q.2 S S +
      ((β.val * (C * (1 + 1 / s.val) * (2 / (1 - s.val))) *
          (n : ℝ) ^ (κ * η) * (n : ℝ) ^ (2 - s.val)) + A * (∑ j, w j) ^ 2) *
        ‖((n : ℝ)⁻¹ • S).val‖ ^ 2 + (n : ℝ) ^ 2 * Err * U ^ 2 := by
  obtain ⟨hAm, hAb, hA⟩ := active_form_data_internal β s n d e hde m hm (by omega) k
    θ ε η t ν C κ γ hC hM
  let b := MatrixEnergy.base (ι := Fin (n : ℕ)) (κ := Fin (n : ℕ))
    (MatrixEnergy.vectorValue Q hQ) (fun x => CFC.sqrt (H x)) ⊤
  let f : BoundedL2Pairings.boundedSubmodule ν := ⟨((n : ℝ)⁻¹ • S).val, U, hf⟩
  let K := (β.val * (C * (1 + 1 / s.val) * (2 / (1 - s.val)))) *
    (n : ℝ) ^ (κ * η) * (n : ℝ) ^ (2 - s.val)
  have hrow := periodized_active_normal_rows_internal s n m hm hnm k C κ γ η
    (zero_le_one.trans hC) M hM
  have hrowA : ∀ᵐ x ∂ν, (∑ i, ∑ j, A0 x i j) ≤ K := by
    filter_upwards [hrow] with x hx
    have hh := mul_le_mul_of_nonneg_left hx β.property.le
    simpa only [K, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum,
      InterpolationMatrix.matrix_active, mul_assoc] using hh
  have hAf := bounded_normal_energy_internal Q hQ n A0 hAm hAb hA S (b r)
    (fun i => hr i) K hrowA
  obtain ⟨hint, hbound⟩ := normal_perturbation_bound_internal β s n d e hde m hm (by omega) k hk hkm
    θ ε η t ν Q hQ P hY f A Err U hpoint
  obtain ⟨_, hdef⟩ := physical_multiplication_defect_internal β s n d e hde m hm (by omega) k
    θ ε η t ν Q hQ P hH hAm hAb hA r r
  simp only [hr] at hdef
  let F := ∑ i : Fin (n : ℕ), BoundarySchurBounds.tensor
    (InterpolationMatrix.referenceColumn s m hm k n (i.castLE (by omega))) f.val
  have hpos := mul_nonneg (sq_nonneg β.val)
    (reference_resolvent_positive_internal ν Q hQ s β n m hm k hk hkm F)
  have hcompare : MatrixEnergy.weakForm Q hQ H ⊤ hH r r ≤
      BoundedMatrixForms.form Q hQ A0 hAm hAb hA (b r) (b r) +
      InterpolationMatrix.perturbationPair β s n d e hde m hm (by omega) k hk hkm
        θ ε η t ν Q hQ P (fun _ => f.val) (fun _ => f.val) hint := by
    unfold InterpolationMatrix.perturbationPair
    change 0 ≤ β.val ^ 2 * inner ℝ F
      (OperatorSchur.vectorValues Q hQ
        (InterpolationMatrix.referenceResolvent ν Q hQ s β m hm k hk hkm n F)) at hpos
    linarith only [hdef, hpos]
  apply hcompare.trans
  exact (add_le_add hAf hbound).trans_eq (by dsimp only [K, f]; ring)

end PhysicalNormal

section LongColumnBound

variable (β : InverseTemperature) (s : Riesz1.RieszExponent)
  (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (m : ℕ+) (hm : 2 ≤ (m : ℕ))
  (hnm : 2 * (n : ℕ) ≤ (m : ℕ)) (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ (m : ℕ) / 4)
  (θ : PhysicalCutoff) (ε η t : ℝ)
  (ν : Measure (AffineSimplex.chartDomain n ((n+d : ℕ)+1)))
  (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
  (P : AffineSimplex.chartDomain n ((n+d : ℕ)+1) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)

local notation "Y" => InterpolationMatrix.multiplicationPart β s n d e hde m hm (by omega) k θ ε η t P
local notation "Bnd" => BoundedL2Pairings.boundedSubmodule ν
local notation "w" => InteractionDifferential.boundaryWeight s.val n
local notation "ess" => fun f : Bnd => ENNReal.toReal
  (eLpNorm (fun x => (Subtype.val f) x) ∞ ν)

/-- See Lemma 6.4 of the paper: apply the exact point and increment bounds
to the native perturbation, with its linearity domain and its finite
column expansion proved. The value and mean hypotheses are the two
corresponding conclusions of the proof of Lemma 6.4. -/
theorem native_long_perturbation_pairing_internal
    (hY : ∀ i j, Integrable (fun x => Y x i j) ν)
    (u v : Fin (n : ℕ) → Bnd) (i₀ : Fin (n : ℕ))
    (hi₀ : |(i₀.val : ℝ) + 1 - (n : ℝ) / 2| ≤ (n : ℝ) / 4)
    (D F A Err U V : ℝ) (hD : 0 ≤ D) (hF : 0 ≤ F)
    (hA : 0 ≤ A) (hErr : 0 ≤ Err) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hu : ∀ j, ∀ᵐ x ∂ν, |(u j).val x| ≤ U)
    (hv : ∀ i, ∀ᵐ x ∂ν, |(v i).val x| ≤ V)
    (hvalue : ∀ i, ‖(v i).val‖ ≤
      D * (1 + (Nat.dist i.val i₀.val : ℝ)) ^ (s.val - 2) * F)
    (hsum : ‖∑ i, (v i).val‖ ≤ D * (n : ℝ) ^ (-(1 - s.val)) * F)
    (hpoint : ∀ (j i : Fin (n : ℕ)) (f : Bnd),
      |(∫ x, (u j).val x * Y x j i * f.val x ∂ν) +
        InterpolationMatrix.schurPointPair ν Q hQ s β m hm k hk hkm n
          (u j).val f.val (j.castLE (by omega)) (i.castLE (by omega))| ≤
      A * w j * w i * ‖(u j).val‖ * ‖f.val‖ + Err * ess (u j) * ess f)
    (hinc : ∀ (j i l : Fin (n : ℕ)) (f : Bnd),
      |(∫ x, (u j).val x * f.val x * (Y x j i - Y x j l) ∂ν) +
        InterpolationMatrix.schurIncrementPair ν Q hQ s β m hm k hk hkm n
          (u j).val f.val (j.castLE (by omega)) (i.castLE (by omega)) (l.castLE (by omega))| ≤
      A * w j * (Nat.dist i.val l.val : ℝ) *
        (min ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ)
          ((min (l.val + 1) ((n : ℕ) - l.val) : ℕ) : ℝ)) ^ (-1 - s.val / 2) *
          ‖(u j).val‖ * ‖f.val‖ + Err * ess (u j) * ess f) :
    let K := 2 * 8 ^ (2 - s.val) * (2 / (1 - s.val / 2)) +
      8 ^ (1 + s.val / 2) * (2 / s.val) + 4 ^ (s.val / 2)
    ∃ hint : Integrable (matrixFieldPair Y (fun i => (u i).val) (fun i => (v i).val)) ν,
      |InterpolationMatrix.perturbationPair β s n d e hde m hm (by omega) k hk hkm
        θ ε η t ν Q hQ P (fun i => (u i).val) (fun i => (v i).val) hint| ≤
      (K * Real.sqrt (2 / (1 - s.val))) * A * D * F *
        (n : ℝ) ^ (-(1 : ℝ) / 2) * ‖WithLp.toLp 2 (fun i => (u i).val)‖ +
          3 * (n : ℝ) ^ 2 * (Err * U * V) := by
  intro K
  obtain ⟨b, hb⟩ := perturbation_rows_internal β s n d e hde m hm (by omega) k hk hkm
    θ ε η t ν Q hQ P hY u
  have hrest (j : Fin (n : ℕ)) (f : Bnd) (B : ℝ) (hB : 0 ≤ B)
      (hf : ∀ᵐ x ∂ν, |f.val x| ≤ B) : Err * ess (u j) * ess f ≤ Err * U * B := by
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (BoundedL2Pairings.essentialNorm_le (u j) U hU (hu j)) hErr)
      (BoundedL2Pairings.essentialNorm_le f B hB hf) ENNReal.toReal_nonneg (mul_nonneg hErr hU)
  have hsumB : ∀ᵐ x ∂ν, |(∑ i, v i).val x| ≤ (n : ℝ) * V := by
    simpa only [Submodule.coe_sum, Fintype.card_fin] using
      PhysicalPerturbation.sum_ae_bound_internal (fun i => (v i).val) V hv
  have hnorm (f : Bnd) : ‖f‖ = ‖f.val‖ := rfl
  have hsum' : ‖∑ i, v i‖ ≤ D * (n : ℝ) ^ (-(1 - s.val)) * F := by
    rw [hnorm, Submodule.coe_sum]
    exact hsum
  have hh := long_perturbation_pairing_internal s n m hnm i₀ hi₀
    (fun i => (u i).val) v b D F A (Err * U * V) hD hF hA (by positivity)
    hvalue hsum' (fun j i l => ?_)
    (fun j i => ?_) (fun j => ?_)
  · obtain ⟨hint, hexp⟩ := perturbation_column_expansion_internal β s n d e hde m hm (by omega)
      k hk hkm θ ε η t ν Q hQ P hY u v
    refine ⟨hint, ?_⟩
    rw [hexp]
    simp_rw [← hb]
    exact hh
  · rw [hb]
    have hp := (hpoint j l (v i)).trans (add_le_add le_rfl (hrest j (v i) V hV (hv i)))
    simpa only [InteractionDifferential.boundaryWeight_long s.property.2, hnorm] using hp
  · rw [hb, hb, perturbation_row_increment_internal β s n d e hde m hm (by omega)
      k hk hkm θ ε η t ν Q hQ P hY (u j) (v i) j i i₀]
    have hp := (hinc j i i₀ (v i)).trans (add_le_add le_rfl (hrest j (v i) V hV (hv i)))
    simpa only [InteractionDifferential.boundaryWeight_long s.property.2, hnorm] using hp
  · rw [hb]
    have hp := (hpoint j i₀ (∑ i, v i)).trans
      (add_le_add le_rfl (hrest j (∑ i, v i) ((n : ℝ) * V) (by positivity) hsumB))
    have her : Err * U * ((n : ℝ) * V) = (n : ℝ) * (Err * U * V) := by ring
    rw [her] at hp
    simpa only [InteractionDifferential.boundaryWeight_long s.property.2, hnorm] using hp

end LongColumnBound

section RateAssembly

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- See Lemma 6.4 of the paper: simplify the physical normal-energy shape
using the actual boundary sum. This produces precisely n⁻ˢ times the
mean square, before the auxiliary mean estimates are inserted. -/
theorem long_normal_energy_shape_internal (Q : ScalarFormData ν)
    (s : Riesz1.RieszExponent) (n : ℕ+) (S : Q.1)
    (E K A Err U : ℝ) (hA : 0 ≤ A)
    (hE : E ≤ (n : ℝ)⁻¹ * Q.2 S S +
      (K * (n : ℝ) ^ (2 - s.val) + A *
        (∑ j, InteractionDifferential.boundaryWeight s.val n j) ^ 2) *
        ‖((n : ℝ)⁻¹ • S).val‖ ^ 2 + (n : ℝ) ^ 2 * Err * U ^ 2) :
    E ≤ (n : ℝ)⁻¹ * Q.2 S S +
      (K + A * (2 / (1 - s.val / 2)) ^ 2) * (n : ℝ) ^ (-s.val) * ‖S.val‖ ^ 2 +
      (n : ℝ) ^ 2 * Err * U ^ 2 := by
  have hn : (0 : ℝ) < n := by positivity
  let B := 2 / (1 - s.val / 2)
  have hden : 0 < 1 - s.val / 2 := by linarith [s.property.2]
  have hB : 0 ≤ B := (div_pos (by norm_num : (0 : ℝ) < 2) hden).le
  have hw : (∑ j, InteractionDifferential.boundaryWeight s.val n j) ≤
      B * (n : ℝ) ^ (1 - s.val / 2) := by
    simp_rw [InteractionDifferential.boundaryWeight_long s.property.2]
    simpa only [neg_div] using LocalizedBoundary.boundary_weight_sum_internal n (s.val / 2)
      (by linarith [s.property.1]) (by linarith [s.property.2])
  have hw2 : (∑ j, InteractionDifferential.boundaryWeight s.val n j) ^ 2 ≤
      B ^ 2 * (n : ℝ) ^ (2 - s.val) := by
    have hh := (sq_le_sq₀ (Finset.sum_nonneg fun j _ =>
      (InteractionDifferential.boundaryWeight_pos s.val n j).le) (by positivity)).mpr hw
    apply hh.trans_eq
    rw [mul_pow, ← Real.rpow_mul_natCast hn.le]
    congr 2
    norm_num
    ring
  have hnS : ‖((n : ℝ)⁻¹ • S).val‖ ^ 2 = (n : ℝ) ^ (-2 : ℝ) * ‖S.val‖ ^ 2 := by
    simp only [Submodule.coe_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hn), mul_pow]
    rw [← Real.rpow_neg_one, ← Real.rpow_mul_natCast hn.le]
    norm_num
  have hp : (n : ℝ) ^ (2 - s.val) * (n : ℝ) ^ (-2 : ℝ) = (n : ℝ) ^ (-s.val) := by
    rw [← Real.rpow_add hn]
    congr 1
    ring
  apply hE.trans
  apply add_le_add _ le_rfl
  apply add_le_add le_rfl
  calc
    _ ≤ (K * (n : ℝ) ^ (2 - s.val) + A * (B ^ 2 * (n : ℝ) ^ (2 - s.val))) *
        ‖((n : ℝ)⁻¹ • S).val‖ ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hw2 hA)) (sq_nonneg _)
    _ = (K + A * B ^ 2) * ((n : ℝ) ^ (2 - s.val) * (n : ℝ) ^ (-2 : ℝ)) * ‖S.val‖ ^ 2 := by
      rw [hnS]
      ring
    _ = _ := by rw [hp]

/-- The mean and mean-gradient estimates in the proof of Lemma 6.4 give the normal-energy power n^(−2+s). The loss
parameter remains symbolic, so this step does not alter quantifier order. -/
theorem long_mean_energy_rate_internal (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (s : Riesz1.RieszExponent)
    (n : ℕ+) (S : Q.1) (D F loss K Tail E : ℝ)
    (hD : 0 ≤ D) (hF : 0 ≤ F) (hK : 0 ≤ K)
    (hmean : ‖S.val‖ ≤ D * (n : ℝ) ^ (loss - (1 - s.val)) * F)
    (hgrad : Real.sqrt (Q.2 S S) ≤ D * (n : ℝ) ^ (loss - (1 - s.val) / 2) * F)
    (hE : E ≤ (n : ℝ)⁻¹ * Q.2 S S + K * (n : ℝ) ^ (-s.val) * ‖S.val‖ ^ 2 + Tail) :
    E ≤ (1 + K) * D ^ 2 * (n : ℝ) ^ (2 * loss - 2 + s.val) * F ^ 2 + Tail := by
  have hn : (0 : ℝ) < n := by positivity
  have hmean2 := (sq_le_sq₀ (norm_nonneg S.val) (by positivity)).mpr hmean
  have hgrad2 := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mpr hgrad
  rw [Real.sq_sqrt (hQ.2.2.1 S)] at hgrad2
  have hp (a b : ℝ) : (n : ℝ) ^ a * (D * (n : ℝ) ^ b * F) ^ 2 =
      D ^ 2 * (n : ℝ) ^ (a + 2 * b) * F ^ 2 := by
    calc
      _ = D ^ 2 * ((n : ℝ) ^ a * ((n : ℝ) ^ b) ^ 2) * F ^ 2 := by ring
      _ = _ := by
        rw [← Real.rpow_mul_natCast hn.le, ← Real.rpow_add hn]
        norm_num [mul_comm b 2]
  calc
    E ≤ (n : ℝ)⁻¹ * (D * (n : ℝ) ^ (loss - (1 - s.val) / 2) * F) ^ 2 +
        K * (n : ℝ) ^ (-s.val) * (D * (n : ℝ) ^ (loss - (1 - s.val)) * F) ^ 2 + Tail := by
      apply hE.trans
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hgrad2 (inv_nonneg.mpr hn.le))
        (mul_le_mul_of_nonneg_left hmean2 (by positivity))) le_rfl
    _ = _ := by
      rw [← Real.rpow_neg_one, hp, mul_assoc K, hp,
        show -1 + 2 * (loss - (1 - s.val) / 2) = 2 * loss - 2 + s.val by ring,
        show -s.val + 2 * (loss - (1 - s.val)) = 2 * loss - 2 + s.val by ring]
      ring

end RateAssembly

section ExteriorReindex

/-- See Subsection 6.1 of the paper: the explicit canonical equivalence between
the two existing exterior index carriers. It also covers empty exteriors. -/
def exteriorIndexEquiv_internal (n : ℕ) (m : ℕ+) :
    Fin ((m : ℕ) - n) ≃ InterpolationMatrix.exteriorIndices m n where
  toFun i := ⟨⟨n + i.val, by have := i.isLt; omega⟩, by
    simp only [InterpolationMatrix.exteriorIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    omega⟩
  invFun j := ⟨j.val.val - n, by
    have hj : n ≤ j.val.val := (Finset.mem_filter.mp j.property).2
    have := j.val.isLt
    omega⟩
  left_inv i := by apply Fin.ext; dsimp; omega
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    have hj : n ≤ j.val.val := (Finset.mem_filter.mp j.property).2
    dsimp
    omega

/-- See Subsection 6.1 of the paper: the Schur assembly evaluated at the
canonical exterior label is the original exterior component. -/
theorem assemble_right_apply_internal {X : Type*} [MeasurableSpace X] {ν : Measure X}
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
    (u : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ)
    (z : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ)
    (i : Fin ((m : ℕ) - (n : ℕ))) :
    SchurRestriction.assemble Q hQ n m hnm (u, z)
      (exteriorIndexEquiv_internal n m i).val = z i := by
  change SchurRestriction.join Q hQ n ((m : ℕ) - (n : ℕ)) (u, z)
    (Fin.cast (Nat.add_sub_of_le hnm).symm (exteriorIndexEquiv_internal n m i).val) = z i
  have hi : Fin.cast (Nat.add_sub_of_le hnm).symm (exteriorIndexEquiv_internal n m i).val =
      Fin.natAdd (n : ℕ) i := Fin.ext rfl
  rw [hi, SchurRestriction.join_right_apply]

end ExteriorReindex

end Riesz2.FixedLengthDecay
