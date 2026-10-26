/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.StaticSchurBound
public import Mathlib.Analysis.Normed.Operator.Banach
public import Riesz2.Frozen.PeriodizedMatrixBounds

/-!
# Abstract long-range Schur restriction

The bounded-coefficient form-domain bridge is provided by `StaticSchurBound`.
This module constructs the Schur form of Subsection 5.1 from the literal
periodized matrix and proves Lemma 5.4. Its coercivity follows the
paper's finite static minimization, exterior inverse comparison, and scalar
energy estimate before Lax–Milgram and block elimination.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Matrix
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace Riesz2.SchurRestriction

variable {α : Type*} [MeasurableSpace α] {ρ : Measure α}
  (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q)

/-- Isometric splitting into the first n and last k components, on the common
scalar form domain. Empty exterior blocks are included. -/
def joinIso (n k : ℕ) :
    WithLp 2 (MatrixEnergy.Vector (ι := Fin n) Q hQ ×
      MatrixEnergy.Vector (ι := Fin k) Q hQ) ≃ₗᵢ[ℝ]
        MatrixEnergy.Vector (ι := Fin (n + k)) Q hQ :=
  (PiLp.sumPiLpEquivProdLpPiLp 2
    (fun _ : Fin n ⊕ Fin k => ScalarFormHilbert.Space Q hQ)).symm.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ (ScalarFormHilbert.Space Q hQ) finSumFinEquiv)

/-- Reassembly of the two blocks as a continuous linear equivalence. -/
def join (n k : ℕ) :
    (MatrixEnergy.Vector (ι := Fin n) Q hQ × MatrixEnergy.Vector (ι := Fin k) Q hQ) ≃L[ℝ]
      MatrixEnergy.Vector (ι := Fin (n + k)) Q hQ :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.trans (joinIso Q hQ n k).toContinuousLinearEquiv

theorem join_norm_sq (n k : ℕ) (u : MatrixEnergy.Vector (ι := Fin n) Q hQ)
    (z : MatrixEnergy.Vector (ι := Fin k) Q hQ) :
    ‖join Q hQ n k (u, z)‖ ^ 2 = ‖u‖ ^ 2 + ‖z‖ ^ 2 := by
  change ‖joinIso Q hQ n k (WithLp.toLp 2 (u, z))‖ ^ 2 = _
  rw [(joinIso Q hQ n k).norm_map]
  exact WithLp.prod_norm_sq_eq_of_L2 _

theorem join_left_apply (n k : ℕ) (u : MatrixEnergy.Vector (ι := Fin n) Q hQ)
    (z : MatrixEnergy.Vector (ι := Fin k) Q hQ) (i : Fin n) :
    join Q hQ n k (u, z) (Fin.castAdd k i) = u i := by
  simp [join, joinIso, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

theorem join_right_apply (n k : ℕ) (u : MatrixEnergy.Vector (ι := Fin n) Q hQ)
    (z : MatrixEnergy.Vector (ι := Fin k) Q hQ) (i : Fin k) :
    join Q hQ n k (u, z) (Fin.natAdd n i) = z i := by
  simp [join, joinIso, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

/-- The two zero-extension maps into the full product form domain. -/
def left (n k : ℕ) : MatrixEnergy.Vector (ι := Fin n) Q hQ →L[ℝ]
    MatrixEnergy.Vector (ι := Fin (n + k)) Q hQ :=
  (join Q hQ n k).toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ _ _)

/-- Zero extension of the exterior block. -/
def right (n k : ℕ) : MatrixEnergy.Vector (ι := Fin k) Q hQ →L[ℝ]
    MatrixEnergy.Vector (ι := Fin (n + k)) Q hQ :=
  (join Q hQ n k).toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ _ _)

theorem join_eq_add (n k : ℕ) (u : MatrixEnergy.Vector (ι := Fin n) Q hQ)
    (z : MatrixEnergy.Vector (ι := Fin k) Q hQ) :
    join Q hQ n k (u, z) = left Q hQ n k u + right Q hQ n k z := by
  change join Q hQ n k (u, z) = join Q hQ n k (u, 0) + join Q hQ n k (0, z)
  rw [← map_add]
  simp only [Prod.mk_add_mk, add_zero, zero_add]

section Blocks

variable (n k : ℕ)
  (F : MatrixEnergy.Vector (ι := Fin (n + k)) Q hQ →L[ℝ]
    MatrixEnergy.Vector (ι := Fin (n + k)) Q hQ →L[ℝ] ℝ)

/-- Active diagonal form, including the scalar diffusion. -/
def active := F.bilinearComp (left Q hQ n k) (left Q hQ n k)

/-- Exterior diagonal form, including the scalar diffusion. -/
def exteriorForm := F.bilinearComp (right Q hQ n k) (right Q hQ n k)

/-- Off-diagonal coupling. Disjoint component supports remove its diffusion part. -/
def cross := F.bilinearComp (left Q hQ n k) (right Q hQ n k)

theorem blockForm_eq (hs : ∀ u v, F u v = F v u)
    (u v : MatrixEnergy.Vector (ι := Fin n) Q hQ)
    (z w : MatrixEnergy.Vector (ι := Fin k) Q hQ) :
    OperatorSchur.blockForm (active Q hQ n k F) (exteriorForm Q hQ n k F)
      (cross Q hQ n k F) (u, z) (v, w) =
      F (join Q hQ n k (u, z)) (join Q hQ n k (v, w)) := by
  rw [OperatorSchur.blockForm_apply, join_eq_add, join_eq_add]
  simp only [map_add, _root_.add_apply]
  change F (left Q hQ n k u) (left Q hQ n k v) +
      F (left Q hQ n k u) (right Q hQ n k w) +
      F (left Q hQ n k v) (right Q hQ n k z) +
      F (right Q hQ n k z) (right Q hQ n k w) = _
  rw [hs (right Q hQ n k z) (left Q hQ n k v)]
  ring

include hQ in
theorem exterior_coercive (c : ℝ)
    (hF : ∀ u, c * ‖u‖ ^ 2 ≤ F u u)
    (z : MatrixEnergy.Vector (ι := Fin k) Q hQ) :
    c * ‖z‖ ^ 2 ≤ exteriorForm Q hQ n k F z z := by
  have he := join_norm_sq Q hQ n k 0 z
  have hl := hF (right Q hQ n k z)
  change c * ‖z‖ ^ 2 ≤ F (right Q hQ n k z) (right Q hQ n k z)
  simpa only [norm_zero, zero_pow (by omega : 2 ≠ 0), zero_add,
    show right Q hQ n k z = join Q hQ n k (0, z) from rfl, he] using hl

include hQ in
/-- Internal elimination helper for Lemma 5.4. The full and reduced
forms are solved separately by Lax–Milgram. The concrete specialization
derives reduced coercivity by the written finite static comparison. -/
theorem form_restriction_of_schur_coercive (hs : ∀ u v, F u v = F v u) (c : ℝ) (hc : 0 < c)
    (hF : ∀ u, c * ‖u‖ ^ 2 ≤ F u u)
    (hS : ∀ u, c * ‖u‖ ^ 2 ≤ OperatorSchur.reduced
      (active Q hQ n k F) (exteriorForm Q hQ n k F) (cross Q hQ n k F) c hc
      (exterior_coercive Q hQ n k F c hF) u u)
    (f : StrongDual ℝ (MatrixEnergy.Vector (ι := Fin n) Q hQ)) :
    let A := active Q hQ n k F
    let D := exteriorForm Q hQ n k F
    let C := cross Q hQ n k F
    let hD := exterior_coercive Q hQ n k F c hF
    let S := OperatorSchur.reduced A D C c hc hD
    (∃! u : MatrixEnergy.Vector (ι := Fin (n + k)) Q hQ,
      ∀ v, F u v = f ((join Q hQ n k).symm v).1) ∧
    (∃! u : MatrixEnergy.Vector (ι := Fin n) Q hQ, ∀ v, S u v = f v) ∧
    ∀ u : MatrixEnergy.Vector (ι := Fin (n + k)) Q hQ,
      (∀ v, F u v = f ((join Q hQ n k).symm v).1) →
      ((join Q hQ n k).symm u).2 =
        -OperatorSchur.exterior D C c hc hD ((join Q hQ n k).symm u).1 ∧
      ∀ v, S ((join Q hQ n k).symm u).1 v = f v := by
  dsimp only
  let A := active Q hQ n k F
  let D := exteriorForm Q hQ n k F
  let C := cross Q hQ n k F
  let hD := exterior_coercive Q hQ n k F c hF
  let S := OperatorSchur.reduced A D C c hc hD
  let ffull : StrongDual ℝ (MatrixEnergy.Vector (ι := Fin (n + k)) Q hQ) :=
    f.comp ((ContinuousLinearMap.fst ℝ _ _).comp (join Q hQ n k).symm.toContinuousLinearMap)
  obtain ⟨u₀, hu₀, huniq⟩ := CoerciveSolution.inverse_existsUnique F c hc hF ffull
  refine ⟨⟨u₀, hu₀, huniq⟩, CoerciveSolution.inverse_existsUnique S c hc hS f, ?_⟩
  intro u hu
  apply (OperatorSchur.zero_exterior_source_iff A D C c hc hD f _ _).mp
  rintro ⟨v, w⟩
  rw [blockForm_eq Q hQ n k F hs, ContinuousLinearEquiv.apply_symm_apply]
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using hu (join Q hQ n k (v, w))

end Blocks

section PeriodizedBounds

variable {s : Riesz1.RieszExponent} {n m : ℕ+} {hm : 2 ≤ (m : ℕ)}
  {K : ℕ} {C κ γ ε : ℝ} {M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ}

/-- The periodized assumptions imply essential boundedness of
every entry. This uses the active error bound and the fixed exterior blocks. -/
theorem periodized_bounded
    (hP : PeriodizedMatrixBounds (ν := ρ) s n m hm K C κ γ ε M) :
    ∃ b : ℝ, ∀ᵐ x ∂ρ, ∀ i j, |M x i j| ≤ b := by
  let H := (2 : ℝ) • referenceIntervalMatrix s m hm K
  let w := fun i j => |H i j| + |C * (n : ℝ) ^ (κ * ε) *
    (1 + (Riesz1.cyclicIndexDistance m i j : ℝ)) ^ (-1 - s.val / 2)|
  refine ⟨∑ i, ∑ j, w i j, ?_⟩
  filter_upwards [hP.2.1] with x hx
  intro i j
  have hnon : ∀ i j, 0 ≤ w i j := fun i j => add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hij : |M x i j| ≤ w i j := by
    by_cases h : (n : ℕ) ≤ i.val ∨ (n : ℕ) ≤ j.val
    · rw [hx.2.1 i j h]
      exact le_add_of_nonneg_right (abs_nonneg _)
    · have hi : i.val < (n : ℕ) := by omega
      have hj : j.val < (n : ℕ) := by omega
      have he := (hx.2.2.2 i j hi hj).trans (le_abs_self _)
      have ht : |M x i j| ≤ |M x i j - H i j| + |H i j| := by
        simpa only [Real.norm_eq_abs, sub_add_cancel] using
          norm_add_le (M x i j - H i j) (H i j)
      dsimp only [w]
      linarith
  exact hij.trans ((Finset.single_le_sum (fun j _ => hnon i j) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun j _ => hnon i j)) (Finset.mem_univ i)))

/-- The numerical coercivity constant in the assumptions is strictly
positive, without a threshold on the system size. -/
theorem periodized_mass_pos (hC : 1 ≤ C) :
    0 < C⁻¹ * (n : ℝ) ^ (-κ * ε) :=
  mul_pos (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hC))
    (Real.rpow_pos_of_pos (by exact_mod_cast n.pos) _)

/-- Scaling the literal periodized matrix by β preserves positivity and gives
the exact source coercivity constant β C⁻¹ n^(-κ ε). -/
theorem periodized_scaled_lower (β : ℝ) (hβ : 0 < β)
    (hP : PeriodizedMatrixBounds (ν := ρ) s n m hm K C κ γ ε M) :
    ∀ᵐ x ∂ρ, ∀ z : Fin (m : ℕ) → ℝ,
      (β * (C⁻¹ * (n : ℝ) ^ (-κ * ε))) * (∑ i, z i ^ 2) ≤
        ∑ i, ∑ j, z i * (β • M x) i j * z j := by
  filter_upwards [hP.2.1] with x hx
  intro z
  calc
    _ = β * (C⁻¹ * (n : ℝ) ^ (-κ * ε) * (∑ i, z i ^ 2)) := by ring
    _ ≤ β * (∑ i, ∑ j, z i * M x i j * z j) :=
      mul_le_mul_of_nonneg_left (hx.2.2.1 z) hβ.le
    _ = _ := by
      simp only [Finset.mul_sum, Matrix.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem periodized_scaled_psd (β : ℝ) (hβ : 0 < β) (hC : 1 ≤ C)
    (hP : PeriodizedMatrixBounds (ν := ρ) s n m hm K C κ γ ε M) :
    ∀ᵐ x ∂ρ, (β • M x).PosSemidef := by
  filter_upwards [hP.2.1, periodized_scaled_lower β hβ hP] with x hx hl
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨?_, fun z => ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, Matrix.smul_apply, smul_eq_mul]
    rw [hx.1 j i]
  · have hp : 0 ≤ β * (C⁻¹ * (n : ℝ) ^ (-κ * ε)) * ∑ i, z i ^ 2 :=
      mul_nonneg (mul_pos hβ (periodized_mass_pos (n := n) (κ := κ) (ε := ε) hC)).le
        (Finset.sum_nonneg (fun i _ => sq_nonneg _))
    simpa only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum, mul_assoc]
      using hp.trans (hl z)

theorem periodized_scaled_measurable (β : ℝ)
    (hP : PeriodizedMatrixBounds (ν := ρ) s n m hm K C κ γ ε M) (i j) :
    Measurable (fun x => (β • M x) i j) :=
  measurable_const.mul (hP.1 i j)

theorem periodized_scaled_bounded (β : ℝ)
    (hP : PeriodizedMatrixBounds (ν := ρ) s n m hm K C κ γ ε M) :
    ∃ b : ℝ, ∀ᵐ x ∂ρ, ∀ i j, |(β • M x) i j| ≤ b := by
  obtain ⟨b, hb⟩ := periodized_bounded hP
  refine ⟨|β| * b, hb.mono (fun x hx i j => ?_)⟩
  simpa only [Matrix.smul_apply, smul_eq_mul, abs_mul] using
    mul_le_mul_of_nonneg_left (hx i j) (abs_nonneg β)

end PeriodizedBounds

section ConcreteRestriction

variable (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))

/-- Identification n + (m - n) = m only relabels components. -/
def castIso : MatrixEnergy.Vector (ι := Fin ((n : ℕ) + ((m : ℕ) - (n : ℕ)))) Q hQ ≃ₗᵢ[ℝ]
    MatrixEnergy.Vector (ι := Fin (m : ℕ)) Q hQ :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ (ScalarFormHilbert.Space Q hQ)
    (finCongr (Nat.add_sub_of_le hnm))

/-- Reassemble an active field and an exterior field on their original m labels. -/
def assemble :
    (MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ ×
      MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ) ≃L[ℝ]
      MatrixEnergy.Vector (ι := Fin (m : ℕ)) Q hQ :=
  (join Q hQ n ((m : ℕ) - (n : ℕ))).trans (castIso Q hQ n m hnm).toContinuousLinearEquiv

theorem assemble_left_apply
    (u : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ)
    (z : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ) (i : Fin (n : ℕ)) :
    assemble Q hQ n m hnm (u, z) (Fin.castLE hnm i) = u i := by
  change (join Q hQ n ((m : ℕ) - (n : ℕ)) (u, z))
    (Fin.cast (Nat.add_sub_of_le hnm).symm (Fin.castLE hnm i)) = u i
  have hi : Fin.cast (Nat.add_sub_of_le hnm).symm (Fin.castLE hnm i) =
      Fin.castAdd ((m : ℕ) - (n : ℕ)) i := Fin.ext rfl
  rw [hi, join_left_apply]

/-- Lemma 5.4, exterior coordinates retain their original labels. -/
theorem assemble_right_apply
    (u : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ)
    (z : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ)
    (i : Fin ((m : ℕ) - (n : ℕ))) :
    assemble Q hQ n m hnm (u, z) (StaticSchurBound.blockIndex n m hnm (.inr i)) = z i := by
  change (join Q hQ n ((m : ℕ) - (n : ℕ)) (u, z)) (Fin.natAdd (n : ℕ) i) = z i
  exact join_right_apply Q hQ _ _ u z i

/-- Lemma 5.4, pointwise matrix pairings in the original labels are
exactly the finite block pairings. -/
theorem assemble_pair_reindex
    (P : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (u v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ)
    (z w : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ) (x : α) :
    matrixFieldPair P
      (fun i => (MatrixEnergy.vectorEquiv Q hQ (assemble Q hQ n m hnm (u,z)) i).val)
      (fun i => (MatrixEnergy.vectorEquiv Q hQ (assemble Q hQ n m hnm (v,w)) i).val) x =
    Sum.elim (fun i => OperatorSchur.vectorValues Q hQ u i x)
      (fun i => OperatorSchur.vectorValues Q hQ z i x) ⬝ᵥ
      ((P x).submatrix (StaticSchurBound.blockIndex n m hnm) (StaticSchurBound.blockIndex n m hnm) *ᵥ
        Sum.elim (fun i => OperatorSchur.vectorValues Q hQ v i x)
          (fun i => OperatorSchur.vectorValues Q hQ w i x)) := by
  let e := StaticSchurBound.blockIndex n m hnm
  have he (a : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ)
      (b : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ) (i) :
      (MatrixEnergy.vectorEquiv Q hQ (assemble Q hQ n m hnm (a,b)) (e i)).val x =
        Sum.elim (fun i => OperatorSchur.vectorValues Q hQ a i x)
          (fun i => OperatorSchur.vectorValues Q hQ b i x) i := by
    cases i with
    | inl i =>
      change (ScalarFormHilbert.equiv Q hQ (assemble Q hQ n m hnm (a,b) (Fin.castLE hnm i))).val x = _
      rw [assemble_left_apply]
      rfl
    | inr i =>
      change (ScalarFormHilbert.equiv Q hQ (assemble Q hQ n m hnm (a,b) (e (.inr i)))).val x = _
      rw [assemble_right_apply]
      rfl
  simp only [matrixFieldPair, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  rw [he, he]
  simp only [Matrix.submatrix_apply]
  ring

/-- Lemma 5.4, the active multiplication form is the finite block A₀. -/
theorem assemble_pair_left
    (P : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (u v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ) :
    matrixFieldPair P
      (fun i => (MatrixEnergy.vectorEquiv Q hQ (assemble Q hQ n m hnm (u,0)) i).val)
      (fun i => (MatrixEnergy.vectorEquiv Q hQ (assemble Q hQ n m hnm (v,0)) i).val) =ᵐ[ρ]
    (fun x => StaticSchurBound.fieldPair (StaticSchurBound.activeMatrix n m hnm (P x))
      (OperatorSchur.vectorValues Q hQ u).ofLp (OperatorSchur.vectorValues Q hQ v).ofLp x) := by
  filter_upwards [Lp.coeFn_zero ℝ 2 ρ] with x hx
  rw [assemble_pair_reindex]
  simp only [map_zero, PiLp.zero_apply, hx, Pi.zero_apply]
  simp [StaticSchurBound.fieldPair, StaticSchurBound.activeMatrix, dotProduct, Matrix.mulVec,
    Fintype.sum_sum_type]

/-- Lemma 5.4, the off-diagonal multiplication form is the finite block B. -/
theorem assemble_pair_cross
    (P : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (u : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ)
    (z : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ) :
    matrixFieldPair P
      (fun i => (MatrixEnergy.vectorEquiv Q hQ (assemble Q hQ n m hnm (u,0)) i).val)
      (fun i => (MatrixEnergy.vectorEquiv Q hQ (assemble Q hQ n m hnm (0,z)) i).val) =ᵐ[ρ]
    (fun x => StaticSchurBound.fieldPair (StaticSchurBound.crossMatrix n m hnm (P x))
      (OperatorSchur.vectorValues Q hQ u).ofLp (OperatorSchur.vectorValues Q hQ z).ofLp x) := by
  filter_upwards [Lp.coeFn_zero ℝ 2 ρ] with x hx
  rw [assemble_pair_reindex]
  simp only [map_zero, PiLp.zero_apply, hx, Pi.zero_apply]
  simp [StaticSchurBound.fieldPair, StaticSchurBound.crossMatrix, dotProduct, Matrix.mulVec,
    Fintype.sum_sum_type]

/-- Lemma 5.4, the exterior multiplication form is the finite block D. -/
theorem assemble_pair_exterior
    (P : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (z w : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ) :
    matrixFieldPair P
      (fun i => (MatrixEnergy.vectorEquiv Q hQ (assemble Q hQ n m hnm (0,z)) i).val)
      (fun i => (MatrixEnergy.vectorEquiv Q hQ (assemble Q hQ n m hnm (0,w)) i).val) =ᵐ[ρ]
    (fun x => StaticSchurBound.fieldPair (StaticSchurBound.exteriorMatrix n m hnm (P x))
      (OperatorSchur.vectorValues Q hQ z).ofLp (OperatorSchur.vectorValues Q hQ w).ofLp x) := by
  filter_upwards [Lp.coeFn_zero ℝ 2 ρ] with x hx
  rw [assemble_pair_reindex]
  simp only [map_zero, PiLp.zero_apply, hx, Pi.zero_apply]
  simp [StaticSchurBound.fieldPair, StaticSchurBound.exteriorMatrix, dotProduct, Matrix.mulVec,
    Fintype.sum_sum_type]

theorem assemble_restrict_apply
    (u : MatrixEnergy.Vector (ι := Fin (m : ℕ)) Q hQ) (i : Fin (n : ℕ)) :
    ((assemble Q hQ n m hnm).symm u).1 i = u (Fin.castLE hnm i) := by
  have he := assemble_left_apply Q hQ n m hnm
    ((assemble Q hQ n m hnm).symm u).1 ((assemble Q hQ n m hnm).symm u).2 i
  simpa only [Prod.mk.eta, ContinuousLinearEquiv.apply_symm_apply] using he.symm

/-- Scalar diffusion splits into its two diagonal blocks under reassembly. -/
theorem assemble_energy
    (u v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ)
    (z w : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ) :
    (∑ i, Q.2 (MatrixEnergy.vectorEquiv Q hQ (assemble Q hQ n m hnm (u, z)) i)
      (MatrixEnergy.vectorEquiv Q hQ (assemble Q hQ n m hnm (v, w)) i)) =
      (∑ i, Q.2 (MatrixEnergy.vectorEquiv Q hQ u i) (MatrixEnergy.vectorEquiv Q hQ v i)) +
      ∑ i, Q.2 (MatrixEnergy.vectorEquiv Q hQ z i) (MatrixEnergy.vectorEquiv Q hQ w i) := by
  have he := Fintype.sum_equiv (finCongr (Nat.add_sub_of_le hnm))
    (fun i => Q.2 (MatrixEnergy.vectorEquiv Q hQ
      (join Q hQ n ((m : ℕ) - (n : ℕ)) (u, z)) i)
      (MatrixEnergy.vectorEquiv Q hQ (join Q hQ n ((m : ℕ) - (n : ℕ)) (v, w)) i))
    (fun i => Q.2 (MatrixEnergy.vectorEquiv Q hQ (assemble Q hQ n m hnm (u, z)) i)
      (MatrixEnergy.vectorEquiv Q hQ (assemble Q hQ n m hnm (v, w)) i))
    (fun _ => by rfl)
  rw [← he, Fin.sum_univ_add]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _
  · change Q.2 (ScalarFormHilbert.equiv Q hQ
        (join Q hQ n ((m : ℕ) - (n : ℕ)) (u, z) (Fin.castAdd _ i)))
        (ScalarFormHilbert.equiv Q hQ
        (join Q hQ n ((m : ℕ) - (n : ℕ)) (v, w) (Fin.castAdd _ i))) = _
    rw [join_left_apply, join_left_apply]
    rfl
  · change Q.2 (ScalarFormHilbert.equiv Q hQ
        (join Q hQ n ((m : ℕ) - (n : ℕ)) (u, z) (Fin.natAdd _ i)))
        (ScalarFormHilbert.equiv Q hQ
        (join Q hQ n ((m : ℕ) - (n : ℕ)) (v, w) (Fin.natAdd _ i))) = _
    rw [join_right_apply, join_right_apply]
    rfl

/-- An exterior field extended to the original m labels vanishes on every
active component, as an L² class. -/
theorem exterior_values_zero
    (z : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ)
    (i : Fin (m : ℕ)) (hi : i.val < (n : ℕ)) :
    (MatrixEnergy.vectorEquiv Q hQ (assemble Q hQ n m hnm (0, z)) i).val = 0 := by
  let j : Fin (n : ℕ) := ⟨i.val, hi⟩
  have hij : Fin.castLE hnm j = i := Fin.ext rfl
  change (ScalarFormHilbert.equiv Q hQ (assemble Q hQ n m hnm (0, z) i)).val = 0
  rw [← hij, assemble_left_apply]
  simp only [PiLp.zero_apply, map_zero, Submodule.coe_zero]

/-- Restriction of ambient L² values to the original active labels. -/
def restrictValues : PiLp 2 (fun _ : Fin (m : ℕ) => Lp ℝ 2 ρ) →L[ℝ]
    PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ρ) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n : ℕ) => Lp ℝ 2 ρ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => PiLp.proj 2 _ (Fin.castLE hnm i)))

/-- Extension by zero from the active labels. Using the adjoint of coordinate
restriction gives exactly the orthogonal inclusion (f,0) in ambient L². -/
def extendSource : PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ρ) →L[ℝ]
    PiLp 2 (fun _ : Fin (m : ℕ) => Lp ℝ 2 ρ) :=
  (restrictValues (ρ := ρ) n m hnm).adjoint

theorem source_pair (f : PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ρ))
    (u : MatrixEnergy.Vector (ι := Fin (m : ℕ)) Q hQ) :
    inner ℝ (extendSource n m hnm f) (OperatorSchur.vectorValues Q hQ u) =
      inner ℝ f (OperatorSchur.vectorValues Q hQ ((assemble Q hQ n m hnm).symm u).1) := by
  rw [extendSource, ContinuousLinearMap.adjoint_inner_left]
  congr 1
  apply PiLp.ext
  intro i
  exact congrArg (fun z : ScalarFormHilbert.Space Q hQ => ScalarFormHilbert.value Q hQ z)
    (assemble_restrict_apply Q hQ n m hnm u i).symm

variable (s : Riesz1.RieszExponent) (hm : 2 ≤ (m : ℕ)) (K : ℕ)
  (C κ γ ε β : ℝ) (hC : 1 ≤ C) (hβ : 0 < β)
  (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
  (hP : PeriodizedMatrixBounds (ν := ρ) s n m hm K C κ γ ε M)

/-- The full form β M + L on the entire product H¹(ν)^m, using the matrix field and the proved bounded-domain equivalence. -/
def periodizedForm := BoundedMatrixForms.form Q hQ (fun x => β • M x)
  (periodized_scaled_measurable β hP) (periodized_scaled_bounded β hP)
  (periodized_scaled_psd β hβ hC hP)

/-- The full equation with active source f is the weak equation
with its L² source extended by zero. All matrix cross integrals are included. -/
theorem periodizedForm_equation_iff
    (u : MatrixEnergy.Vector (ι := Fin (m : ℕ)) Q hQ)
    (f : PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ρ)) :
    (∀ w, periodizedForm Q hQ n m s hm K C κ γ ε β hC hβ M hP u w =
      inner ℝ f (OperatorSchur.vectorValues Q hQ ((assemble Q hQ n m hnm).symm w).1)) ↔
      WeightedWeakSolution Q (fun x => β • M x) ⊤ (extendSource n m hnm f).ofLp
        (MatrixEnergy.vectorEquiv Q hQ u) := by
  have he := BoundedMatrixForms.equation_iff Q hQ (fun x => β • M x)
    (periodized_scaled_measurable β hP) (periodized_scaled_bounded β hP)
    (periodized_scaled_psd β hβ hC hP) u (extendSource n m hnm f).ofLp
  simpa only [WithLp.toLp_ofLp, source_pair, periodizedForm] using he

/-- Pairing with an exterior field uses the literal constant reference blocks
from the periodized assumptions. No coefficient is differentiated. -/
theorem exterior_pair_reference
    (hP' : PeriodizedMatrixBounds (ν := ρ) s n m hm K C κ γ ε M)
    (u v : Fin (m : ℕ) → Lp ℝ 2 ρ)
    (hv : ∀ j : Fin (m : ℕ), j.val < (n : ℕ) → v j = 0) :
    matrixFieldPair (fun x => β • M x) u v =ᵐ[ρ]
      matrixFieldPair (fun _ => β • ((2 : ℝ) • referenceIntervalMatrix s m hm K)) u v := by
  filter_upwards [hP'.2.1, Lp.coeFn_zero ℝ 2 ρ] with x hx hz
  simp only [Pi.zero_apply] at hz
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : (n : ℕ) ≤ j.val
  · simp only [Matrix.smul_apply, smul_eq_mul, hx.2.1 i j (Or.inr hj)]
  · rw [hv j (by omega), hz, mul_zero, mul_zero]

/-- Pulling a real scalar out of a finite matrix pairing and its integral does
not split any unbounded signed coefficient sum. -/
theorem integral_pair_smul {ι : Type*} [Fintype ι]
    (P : α → Matrix ι ι ℝ) (b : ℝ) (u v : ι → Lp ℝ 2 ρ) :
    (∫ x, matrixFieldPair (fun x => b • P x) u v x ∂ρ) =
      b * ∫ x, matrixFieldPair P u v x ∂ρ := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  simp only [matrixFieldPair, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- This is the full form expressed in the n + (m - n) component order. -/
def splitForm := (periodizedForm Q hQ n m s hm K C κ γ ε β hC hβ M hP).bilinearComp
  (castIso Q hQ n m hnm).toContinuousLinearEquiv.toContinuousLinearMap
  (castIso Q hQ n m hnm).toContinuousLinearEquiv.toContinuousLinearMap

/-- The off-diagonal block has no scalar diffusion term, and its matrix term
is exactly the fixed reference coupling β C. -/
theorem cross_reference
    (u : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ)
    (z : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ) :
    cross Q hQ n ((m : ℕ) - (n : ℕ))
      (splitForm Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP) u z =
      ∫ x, matrixFieldPair
        (fun _ => β • ((2 : ℝ) • referenceIntervalMatrix s m hm K))
        (fun i => (MatrixEnergy.vectorEquiv Q hQ (assemble Q hQ n m hnm (u, 0)) i).val)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ (assemble Q hQ n m hnm (0, z)) i).val) x ∂ρ := by
  change BoundedMatrixForms.form Q hQ (fun x => β • M x) _ _ _
    (assemble Q hQ n m hnm (u, 0)) (assemble Q hQ n m hnm (0, z)) = _
  rw [BoundedMatrixForms.form_apply, assemble_energy]
  simp only [map_zero, Pi.zero_apply, LinearMap.zero_apply, Finset.sum_const_zero,
    zero_add, add_zero]
  exact integral_congr_ae (exterior_pair_reference n m s hm K C κ γ ε β M hP
    _ _ (exterior_values_zero Q hQ n m hnm z))

/-- The exterior diagonal form is precisely β D + L, with D the constant
reference block and the original scalar diffusion coefficient one. -/
theorem exteriorForm_reference
    (z w : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ) :
    exteriorForm Q hQ n ((m : ℕ) - (n : ℕ))
      (splitForm Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP) z w =
      (∑ i, Q.2 (MatrixEnergy.vectorEquiv Q hQ z i) (MatrixEnergy.vectorEquiv Q hQ w i)) +
      ∫ x, matrixFieldPair
        (fun _ => β • ((2 : ℝ) • referenceIntervalMatrix s m hm K))
        (fun i => (MatrixEnergy.vectorEquiv Q hQ (assemble Q hQ n m hnm (0, z)) i).val)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ (assemble Q hQ n m hnm (0, w)) i).val) x ∂ρ := by
  change BoundedMatrixForms.form Q hQ (fun x => β • M x) _ _ _
    (assemble Q hQ n m hnm (0, z)) (assemble Q hQ n m hnm (0, w)) = _
  rw [BoundedMatrixForms.form_apply, assemble_energy]
  simp only [map_zero, Pi.zero_apply, Finset.sum_const_zero, zero_add]
  congr 1
  exact integral_congr_ae (exterior_pair_reference n m s hm K C κ γ ε β M hP
    _ _ (exterior_values_zero Q hQ n m hnm w))

/-- Lemma 5.4, the active form is βA₀ plus the scalar diffusion energy. -/
theorem active_block_form
    (u v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ) :
    active Q hQ n ((m : ℕ) - (n : ℕ))
      (splitForm Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP) u v =
    OperatorSchur.vectorEnergy Q hQ u v + β * ∫ x,
      StaticSchurBound.fieldPair (StaticSchurBound.activeMatrix n m hnm (M x))
        (OperatorSchur.vectorValues Q hQ u).ofLp (OperatorSchur.vectorValues Q hQ v).ofLp x ∂ρ := by
  change BoundedMatrixForms.form Q hQ (fun x => β • M x) _ _ _
    (assemble Q hQ n m hnm (u,0)) (assemble Q hQ n m hnm (v,0)) = _
  rw [BoundedMatrixForms.form_apply, assemble_energy, integral_pair_smul,
    OperatorSchur.vectorEnergy_apply]
  simp only [map_zero, Pi.zero_apply, Finset.sum_const_zero, add_zero]
  congr 1
  exact congrArg (fun t : ℝ => β * t)
    (integral_congr_ae (assemble_pair_left Q hQ n m hnm M u v))

/-- Lemma 5.4, the fixed coupling βB has the general L² source βBᵀu. -/
theorem cross_block_form
    (u : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ)
    (z : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ) :
    cross Q hQ n ((m : ℕ) - (n : ℕ))
      (splitForm Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP) u z =
    β * inner ℝ (WithLp.toLp 2 (StaticSchurBound.fieldMul
      (StaticSchurBound.crossMatrix n m hnm ((2 : ℝ) • referenceIntervalMatrix s m hm K))ᵀ
      (OperatorSchur.vectorValues Q hQ u).ofLp)) (OperatorSchur.vectorValues Q hQ z) := by
  rw [cross_reference, integral_pair_smul]
  congr 1
  rw [← StaticSchurBound.fieldMul_transpose_pair]
  exact integral_congr_ae (assemble_pair_cross Q hQ n m hnm _ u z)

/-- Lemma 5.4, the exterior form is βD plus the nonnegative scalar diffusion. -/
theorem exterior_block_form
    (z w : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ) :
    exteriorForm Q hQ n ((m : ℕ) - (n : ℕ))
      (splitForm Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP) z w =
    OperatorSchur.vectorEnergy Q hQ z w + β * ∫ x,
      StaticSchurBound.fieldPair
        (StaticSchurBound.exteriorMatrix n m hnm ((2 : ℝ) • referenceIntervalMatrix s m hm K))
        (OperatorSchur.vectorValues Q hQ z).ofLp (OperatorSchur.vectorValues Q hQ w).ofLp x ∂ρ := by
  rw [exteriorForm_reference, integral_pair_smul, OperatorSchur.vectorEnergy_apply]
  congr 1
  exact congrArg (fun t : ℝ => β * t)
    (integral_congr_ae (assemble_pair_exterior Q hQ n m hnm _ z w))

theorem splitForm_coercive (u : MatrixEnergy.Vector
    (ι := Fin ((n : ℕ) + ((m : ℕ) - (n : ℕ)))) Q hQ) :
    min 1 (β * (C⁻¹ * (n : ℝ) ^ (-κ * ε))) * ‖u‖ ^ 2 ≤
      splitForm Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP u u := by
  have he := BoundedMatrixForms.form_coercive Q hQ (fun x => β • M x)
    (periodized_scaled_measurable β hP) (periodized_scaled_bounded β hP)
    (periodized_scaled_psd β hβ hC hP) _ (periodized_scaled_lower β hβ hP)
    (castIso Q hQ n m hnm u)
  simpa only [splitForm, periodizedForm, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv,
    LinearIsometryEquiv.norm_map] using he

include hC hβ in
/-- The positive full-form coercivity constant used to construct the exterior
resolvent and the Schur form. -/
theorem coercivity_pos : 0 < min 1 (β * (C⁻¹ * (n : ℝ) ^ (-κ * ε))) :=
  lt_min zero_lt_one (mul_pos hβ (periodized_mass_pos (n := n) (κ := κ) (ε := ε) hC))

/-- See Subsection 5.1 of the paper: β A₀ + L - β B R_D C, as a continuous bilinear
form on all active scalar form-domain tuples. Its exterior inverse is built
on the whole exterior form domain, including the empty exterior when m = n. -/
def schurForm :=
  let F := splitForm Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP
  let c := min 1 (β * (C⁻¹ * (n : ℝ) ^ (-κ * ε)))
  OperatorSchur.reduced (active Q hQ n ((m : ℕ) - (n : ℕ)) F)
    (exteriorForm Q hQ n ((m : ℕ) - (n : ℕ)) F)
    (cross Q hQ n ((m : ℕ) - (n : ℕ)) F) c
    (coercivity_pos n C κ ε β hC hβ)
    (exterior_coercive Q hQ n ((m : ℕ) - (n : ℕ)) F c
      (splitForm_coercive Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP))

/-- The exterior response R_D C. The factors β in the off-diagonal block and
in β D + L cancel, so this is (D + β⁻¹ L)⁻¹ C. -/
def exteriorResponse :=
  let F := splitForm Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP
  let c := min 1 (β * (C⁻¹ * (n : ℝ) ^ (-κ * ε)))
  OperatorSchur.exterior (exteriorForm Q hQ n ((m : ℕ) - (n : ℕ)) F)
    (cross Q hQ n ((m : ℕ) - (n : ℕ)) F) c
    (coercivity_pos n C κ ε β hC hβ)
    (exterior_coercive Q hQ n ((m : ℕ) - (n : ℕ)) F c
      (splitForm_coercive Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP))

/-- See Subsection 5.1 of the paper: the exterior response is the full-form solution
of (D + β⁻¹ L)z = C u, with the constant reference blocks from the periodized assumptions. This proves the normalization of R_D used by the
restriction theorem, rather than assuming a resolvent comparison. -/
theorem exterior_resolvent_equation
    (u : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ)
    (w : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ) :
    let z := exteriorResponse Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP u
    β⁻¹ * (∑ i, Q.2 (MatrixEnergy.vectorEquiv Q hQ z i) (MatrixEnergy.vectorEquiv Q hQ w i)) +
      (∫ x, matrixFieldPair (fun _ => (2 : ℝ) • referenceIntervalMatrix s m hm K)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ (assemble Q hQ n m hnm (0, z)) i).val)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ (assemble Q hQ n m hnm (0, w)) i).val) x ∂ρ) =
      ∫ x, matrixFieldPair (fun _ => (2 : ℝ) • referenceIntervalMatrix s m hm K)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ (assemble Q hQ n m hnm (u, 0)) i).val)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ (assemble Q hQ n m hnm (0, w)) i).val) x ∂ρ := by
  let F := splitForm Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP
  let c := min 1 (β * (C⁻¹ * (n : ℝ) ^ (-κ * ε)))
  have he := OperatorSchur.exterior_solves
    (exteriorForm Q hQ n ((m : ℕ) - (n : ℕ)) F)
    (cross Q hQ n ((m : ℕ) - (n : ℕ)) F) c
    (coercivity_pos n C κ ε β hC hβ)
    (exterior_coercive Q hQ n ((m : ℕ) - (n : ℕ)) F c
      (splitForm_coercive Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP)) u w
  rw [exteriorForm_reference, cross_reference] at he
  simp only [integral_pair_smul] at he
  have he' := congrArg (fun t : ℝ => β⁻¹ * t) he
  simpa only [exteriorResponse, F, c, integral_pair_smul, mul_add, ← mul_assoc,
    inv_mul_cancel₀ hβ.ne', one_mul] using he'

/-- Lemma 5.4, second item: the actual exterior resolvent βD + L lies
between zero and β⁻¹D⁻¹ in quadratic form, for every exterior L² field.
The assertion also covers a zero scalar measure and a zero-dimensional exterior. -/
theorem exterior_resolvent_le_static_inverse
    (f : PiLp 2 (fun _ : Fin ((m : ℕ) - (n : ℕ)) => Lp ℝ 2 ρ)) :
    let F := splitForm Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP
    let E := exteriorForm Q hQ n ((m : ℕ) - (n : ℕ)) F
    let c := min 1 (β * (C⁻¹ * (n : ℝ) ^ (-κ * ε)))
    let hE := exterior_coercive Q hQ n ((m : ℕ) - (n : ℕ)) F c
      (splitForm_coercive Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP)
    let J := OperatorSchur.vectorValues (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ
    let z := CoerciveSolution.solution E c (coercivity_pos n C κ ε β hC hβ) hE J f
    let D := StaticSchurBound.exteriorMatrix n m hnm ((2 : ℝ) • referenceIntervalMatrix s m hm K)
    0 ≤ inner ℝ f (J z) ∧ inner ℝ f (J z) ≤
      β⁻¹ * ∫ x, StaticSchurBound.fieldPair D⁻¹ f.ofLp f.ofLp x ∂ρ := by
  by_cases hρ : ρ = 0
  · have hf : f = 0 := by
      apply PiLp.ext
      intro i
      apply Lp.ext
      simp [hρ, Filter.EventuallyEq]
    simp [hf, hρ]
  have : NeZero ρ := ⟨hρ⟩
  let D := StaticSchurBound.exteriorMatrix n m hnm ((2 : ℝ) • referenceIntervalMatrix s m hm K)
  have hstatic := StaticSchurBound.periodized_static_schur_lower s n m hnm hm K C κ γ ε hC M hP
  have hD : D.PosDef := hstatic.exists.choose_spec.1
  apply StaticSchurBound.internal_exterior_resolvent_le_static_inverse D hD β hβ
  intro z
  rw [exterior_block_form]
  exact le_add_of_nonneg_left (OperatorSchur.vectorEnergy_nonneg Q hQ z)

/-- Lemma 5.4, second item: integrate equation (5.14), compare the exterior
resolvent with D⁻¹, and add the original scalar diffusion. This follows the
written static Schur proof and retains both the mass and the diffusion energy. -/
theorem schur_mass_energy_via_static_inverse
    (u : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ) :
    β * (C⁻¹ * (n : ℝ) ^ (-κ * ε)) * ‖OperatorSchur.vectorValues Q hQ u‖ ^ 2 +
      OperatorSchur.vectorEnergy Q hQ u u ≤
      schurForm Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP u u := by
  by_cases hρ : ρ = 0
  · have hu : u = 0 := by
      apply PiLp.ext
      intro i
      apply (ScalarFormHilbert.equiv Q hQ).injective
      simp only [PiLp.zero_apply, map_zero]
      apply Subtype.ext
      apply Lp.ext
      simp [hρ, Filter.EventuallyEq]
    simp [hu]
  have : NeZero ρ := ⟨hρ⟩
  let H := (2 : ℝ) • referenceIntervalMatrix s m hm K
  let B := StaticSchurBound.crossMatrix n m hnm H
  let D := StaticSchurBound.exteriorMatrix n m hnm H
  let a := C⁻¹ * (n : ℝ) ^ (-κ * ε)
  let F := splitForm Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP
  let E := exteriorForm Q hQ n ((m : ℕ) - (n : ℕ)) F
  let T := cross Q hQ n ((m : ℕ) - (n : ℕ)) F
  let c := min 1 (β * a)
  have hc : 0 < c := coercivity_pos n C κ ε β hC hβ
  let hE := exterior_coercive Q hQ n ((m : ℕ) - (n : ℕ)) F c
    (splitForm_coercive Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP)
  let U := OperatorSchur.vectorValues Q hQ u
  let g := WithLp.toLp 2 (StaticSchurBound.fieldMul Bᵀ U.ofLp)
  let J := OperatorSchur.vectorValues (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ
  let r := OperatorSchur.exterior E T c hc hE u
  have hstatic := StaticSchurBound.periodized_static_schur_lower s n m hnm hm K C κ γ ε hC M hP
  have hT (w) : T u w = inner ℝ (β • g) (J w) := by
    rw [real_inner_smul_left]
    exact cross_block_form Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP u w
  have hr : r = CoerciveSolution.solution E c hc hE J (β • g) := by
    exact CoerciveSolution.inverse_unique E c hc hE
      (CoerciveSolution.forcing J (β • g)) r
      (fun w => (OperatorSchur.exterior_solves E T c hc hE u w).trans (hT w))
  have hres := exterior_resolvent_le_static_inverse Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP (β • g)
  dsimp only at hres
  rw [← hr, StaticSchurBound.integral_fieldPair_smul] at hres
  have hcorrection : T u r ≤ β * ∫ x, StaticSchurBound.fieldPair D⁻¹ g.ofLp g.ofLp x ∂ρ := by
    rw [hT]
    convert hres.2 using 1
    field_simp
    rfl
  have hAint : Integrable (fun x => StaticSchurBound.fieldPair
      (StaticSchurBound.activeMatrix n m hnm (M x)) U.ofLp U.ofLp x) ρ :=
    (BoundedMatrixForms.integrable_pair M hP.1 (periodized_bounded hP)
      (fun i => (MatrixEnergy.vectorEquiv Q hQ (assemble Q hQ n m hnm (u,0)) i).val)
      (fun i => (MatrixEnergy.vectorEquiv Q hQ (assemble Q hQ n m hnm (u,0)) i).val)).congr
      (assemble_pair_left Q hQ n m hnm M u u)
  have hGint := StaticSchurBound.integrable_fieldPair D⁻¹ g.ofLp g.ofLp
  have hmass : Integrable (fun x => (fun i => U i x) ⬝ᵥ (fun i => U i x)) ρ :=
    integrable_finsetSum _ (fun i _ => (Lp.memLp (U i)).integrable_mul (Lp.memLp (U i)))
  have hnorm : ‖U‖ ^ 2 = ∫ x, (fun i => U i x) ⬝ᵥ (fun i => U i x) ∂ρ := by
    rw [← real_inner_self_eq_norm_sq, StaticSchurBound.inner_eq_integral_dot]
  have hintegrated : a * ‖U‖ ^ 2 ≤
      (∫ x, StaticSchurBound.fieldPair (StaticSchurBound.activeMatrix n m hnm (M x)) U.ofLp U.ofLp x ∂ρ) -
      ∫ x, StaticSchurBound.fieldPair D⁻¹ g.ofLp g.ofLp x ∂ρ := by
    rw [hnorm, ← integral_const_mul, ← integral_sub hAint hGint]
    apply integral_mono_ae (hmass.const_mul a) (hAint.sub hGint)
    filter_upwards [hstatic, StaticSchurBound.fieldMul_coe Bᵀ U.ofLp] with x hx hg
    have hg' : (fun i => g i x) = Bᵀ *ᵥ (fun i => U i x) := funext hg
    simpa only [StaticSchurBound.fieldPair, Pi.sub_apply, hg'] using hx.2 (fun i => U i x)
  have hactive := active_block_form Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP u u
  have hschur : schurForm Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP u u =
      active Q hQ n ((m : ℕ) - (n : ℕ)) F u u - T u r := rfl
  have hm := mul_le_mul_of_nonneg_left hintegrated hβ.le
  rw [hschur, hactive]
  change β * a * ‖U‖ ^ 2 + OperatorSchur.vectorEnergy Q hQ u u ≤ _
  linarith

/-- Lemma 5.4, second item: the written static comparison is coercive
on the complete active Sobolev product, with diffusion coefficient one. -/
theorem schur_coercive_via_static_inverse
    (u : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ) :
    min 1 (β * (C⁻¹ * (n : ℝ) ^ (-κ * ε))) * ‖u‖ ^ 2 ≤
      schurForm Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP u u := by
  have h := schur_mass_energy_via_static_inverse Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP u
  have h₁ := mul_le_mul_of_nonneg_right
    (min_le_left 1 (β * (C⁻¹ * (n : ℝ) ^ (-κ * ε))))
    (OperatorSchur.vectorEnergy_nonneg Q hQ u)
  have h₂ := mul_le_mul_of_nonneg_right
    (min_le_right 1 (β * (C⁻¹ * (n : ℝ) ^ (-κ * ε))))
    (sq_nonneg ‖OperatorSchur.vectorValues Q hQ u‖)
  rw [OperatorSchur.vector_norm_sq Q hQ u]
  linarith

/-- See Lemma 5.4 of the paper: for every active L² source the full and Schur
equations have unique unrestricted solutions. Their active components agree,
and the exterior component is -R_D C applied to that same solution. The full
equation is tested on every element of H¹(ν)^m, with source (f,0).

The hypotheses are `PeriodizedMatrixBounds`. The argument also covers m = n and arbitrary point sources χ eᵢ. -/
theorem schur_restriction (f : PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ρ)) :
    let F := periodizedForm Q hQ n m s hm K C κ γ ε β hC hβ M hP
    let S := schurForm Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP
    let R := exteriorResponse Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP
    let J := assemble Q hQ n m hnm
    (∃! u : MatrixEnergy.Vector (ι := Fin (m : ℕ)) Q hQ,
      ∀ w, F u w = inner ℝ f (OperatorSchur.vectorValues Q hQ (J.symm w).1)) ∧
    (∃! v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ,
      ∀ w, S v w = inner ℝ f (OperatorSchur.vectorValues Q hQ w)) ∧
    ∀ (u : MatrixEnergy.Vector (ι := Fin (m : ℕ)) Q hQ)
      (v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ),
      (∀ w, F u w = inner ℝ f (OperatorSchur.vectorValues Q hQ (J.symm w).1)) →
      (∀ w, S v w = inner ℝ f (OperatorSchur.vectorValues Q hQ w)) →
      J.symm u = (v, -R v) := by
  dsimp only
  let E := castIso Q hQ n m hnm
  let F := periodizedForm Q hQ n m s hm K C κ γ ε β hC hβ M hP
  let G := splitForm Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP
  let c := min 1 (β * (C⁻¹ * (n : ℝ) ^ (-κ * ε)))
  let b := CoerciveSolution.forcing (OperatorSchur.vectorValues Q hQ) f
  have hs : ∀ u v, G u v = G v u := by
    intro u v
    exact BoundedMatrixForms.form_symmetric Q hQ (fun x => β • M x)
      (periodized_scaled_measurable β hP) (periodized_scaled_bounded β hP)
      (periodized_scaled_psd β hβ hC hP) _ _
  have hr := form_restriction_of_schur_coercive Q hQ n ((m : ℕ) - (n : ℕ)) G hs c
    (coercivity_pos n C κ ε β hC hβ)
    (splitForm_coercive Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP)
    (schur_coercive_via_static_inverse Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP) b
  rcases hr with ⟨⟨u₀, hu₀, huniq⟩, hv, hres⟩
  have hchange (u : MatrixEnergy.Vector (ι := Fin (m : ℕ)) Q hQ) :
      (∀ w, F u w = inner ℝ f
        (OperatorSchur.vectorValues Q hQ ((assemble Q hQ n m hnm).symm w).1)) ↔
      (∀ w, G (E.symm u) w = b ((join Q hQ n ((m : ℕ) - (n : ℕ))).symm w).1) := by
    constructor
    · intro hu w
      have he := hu (E w)
      simpa only [G, F, E, b, CoerciveSolution.forcing_apply, splitForm, ContinuousLinearMap.bilinearComp_apply,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv,
        ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.apply_symm_apply,
        assemble, ContinuousLinearEquiv.symm_trans_apply, ContinuousLinearEquiv.trans_apply,
        LinearIsometryEquiv.symm_apply_apply] using he
    · intro hu w
      have he := hu (E.symm w)
      simpa only [G, F, E, b, CoerciveSolution.forcing_apply, splitForm, ContinuousLinearMap.bilinearComp_apply,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv,
        ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.apply_symm_apply,
        assemble, ContinuousLinearEquiv.symm_trans_apply, ContinuousLinearEquiv.trans_apply] using he
  refine ⟨⟨E u₀, (hchange _).mpr ?_, ?_⟩, hv, ?_⟩
  · simpa only [LinearIsometryEquiv.symm_apply_apply] using hu₀
  · intro u hu
    exact E.symm.injective ((huniq (E.symm u) ((hchange u).mp hu)).trans
      (E.symm_apply_apply u₀).symm)
  · intro u v hu hv'
    obtain ⟨hz, he⟩ := hres (E.symm u) ((hchange u).mp hu)
    have heq := hv.unique he hv'
    apply Prod.ext
    · exact heq
    · simpa only [heq, assemble, ContinuousLinearEquiv.symm_trans_apply,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        LinearIsometryEquiv.coe_symm_toContinuousLinearEquiv, exteriorResponse, G, c, E] using hz

/-- See Lemma 5.4 of the paper, in the weak-solution interface. The full
solution is a literal tuple in the scalar domain, with literal equality
as uniqueness. The Schur equation acts on the complete active Sobolev product. -/
theorem schur_restriction_weak (f : PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ρ)) :
    let S := schurForm Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP
    let R := exteriorResponse Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP
    let J := assemble Q hQ n m hnm
    (∃! u : Fin (m : ℕ) → Q.1,
      WeightedWeakSolution Q (fun x => β • M x) ⊤ (extendSource n m hnm f).ofLp u) ∧
    (∃! v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ,
      ∀ w, S v w = inner ℝ f (OperatorSchur.vectorValues Q hQ w)) ∧
    ∀ (u : Fin (m : ℕ) → Q.1) (v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ),
      WeightedWeakSolution Q (fun x => β • M x) ⊤ (extendSource n m hnm f).ofLp u →
      (∀ w, S v w = inner ℝ f (OperatorSchur.vectorValues Q hQ w)) →
      J.symm ((MatrixEnergy.vectorEquiv Q hQ).symm u) = (v, -R v) := by
  rcases schur_restriction Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP f with
    ⟨⟨u₀, hu₀, huniq⟩, hv, hres⟩
  have hiff := periodizedForm_equation_iff Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP
  refine ⟨⟨MatrixEnergy.vectorEquiv Q hQ u₀, (hiff u₀ f).mp hu₀, ?_⟩, hv, ?_⟩
  · intro u hu
    have he := huniq ((MatrixEnergy.vectorEquiv Q hQ).symm u)
      ((hiff _ f).mpr (by simpa only [LinearEquiv.apply_symm_apply] using hu))
    simpa only [LinearEquiv.apply_symm_apply] using congrArg (MatrixEnergy.vectorEquiv Q hQ) he
  · intro u v hu hv'
    exact hres ((MatrixEnergy.vectorEquiv Q hQ).symm u) v
      ((hiff _ f).mpr (by simpa only [LinearEquiv.apply_symm_apply] using hu)) hv'

/-- The full-cycle case has the zero-dimensional exterior space.
Its exterior response vanishes without evaluating a matrix inverse. -/
theorem exteriorResponse_eq_zero (hmn : (m : ℕ) = (n : ℕ))
    (u : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ) :
    exteriorResponse Q hQ n m hnm s hm K C κ γ ε β hC hβ M hP u = 0 := by
  have hk : (m : ℕ) - (n : ℕ) = 0 := Nat.sub_eq_zero_of_le hmn.le
  have : IsEmpty (Fin ((m : ℕ) - (n : ℕ))) := by
    rw [hk]
    infer_instance
  exact Subsingleton.elim _ _

end ConcreteRestriction

end Riesz2.SchurRestriction
