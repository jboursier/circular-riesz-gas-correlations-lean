/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.ColumnSubtractionPart2
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Riesz2.ToMathlib.BoundedL2Pairings

/-!
# Bounded-input multiplication and Schur operators

The operators used in Lemma 5.17, Proposition 5.18, and
Lemma 6.4 act on actual bounded vector fields and have integrable
outputs, even when their multiplication coefficients are unbounded.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter
open scoped BigOperators ENNReal Classical

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.BoundedPerturbationOperator

open ColumnSubtraction

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} {n : ℕ}

/-- The finite-measure inclusion needed for Lemma 5.17,
with its linear structure retained. -/
def inclusion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [IsFiniteMeasure ν] (p q : ℝ≥0∞) (h : q ≤ p) : Lp E p ν →ₗ[ℝ] Lp E q ν where
  toFun f := ((Lp.memLp f).mono_exponent h).toLp f
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (f+g)).mono_exponent h),
      Lp.coeFn_add f g, Lp.coeFn_add (((Lp.memLp f).mono_exponent h).toLp f)
        (((Lp.memLp g).mono_exponent h).toLp g),
      MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent h),
      MemLp.coeFn_toLp ((Lp.memLp g).mono_exponent h)] with x h₁ h₂ h₃ h₄ h₅
    simp only [h₁,h₂,h₃,h₄,h₅,Pi.add_apply]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (c • f)).mono_exponent h),
      Lp.coeFn_smul c f,
      Lp.coeFn_smul c (((Lp.memLp f).mono_exponent h).toLp f),
      MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent h)] with x h₁ h₂ h₃ h₄
    simp only [RingHom.id_apply,h₁,h₂,h₃,h₄,Pi.smul_apply]

/-- The inclusion in Lemma 5.17 preserves representatives. -/
theorem inclusion_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [IsFiniteMeasure ν] (p q : ℝ≥0∞) (h : q ≤ p) (f : Lp E p ν) :
    inclusion p q h f =ᵐ[ν] f := MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent h)

/-- The bounded scalar class used in Lemma 5.17, as an
actual bounded L² class for the existing physical pairing API. -/
def boundedScalar [IsFiniteMeasure ν] : Lp ℝ ∞ ν →ₗ[ℝ]
    BoundedL2Pairings.boundedSubmodule ν where
  toFun f := ⟨inclusion ∞ 2 (by simp) f, ‖f‖, by
    filter_upwards [inclusion_ae ∞ 2 (by simp) f,
      ae_le_lpNorm_exponent_top (Lp.memLp f)] with x hx hb
    simpa only [hx,Real.norm_eq_abs,← toReal_eLpNorm,← Lp.norm_def] using hb⟩
  map_add' f g := Subtype.ext (map_add (inclusion ∞ 2 (by simp)) f g)
  map_smul' c f := Subtype.ext (map_smul (inclusion ∞ 2 (by simp)) c f)

/-- The bounded scalar carrier in Lemma 5.17 has the
canonical L² value. -/
theorem boundedScalar_val [IsFiniteMeasure ν] (f : Lp ℝ ∞ ν) :
    (boundedScalar f).val = toL2 f := rfl

/-- The finite essential norm in Lemma 5.17 agrees with
the norm used by the existing bounded-L² pairing interface. -/
theorem boundedScalar_essentialNorm [IsFiniteMeasure ν] (f : Lp ℝ ∞ ν) :
    (eLpNorm ((boundedScalar f).val : X → ℝ) ∞ ν).toReal = ‖f‖ := by
  change (eLpNorm (inclusion (E := ℝ) ∞ 2 (by simp) f : X → ℝ) ∞ ν).toReal = _
  rw [eLpNorm_congr_ae (inclusion_ae ∞ 2 (by simp) f)]
  exact (Lp.norm_def f).symm

/-- Scalar coordinates of a bounded field, in the L² source space of
its Schur resolvent, as used in Proposition 5.18 and Lemma 6.4. -/
def source [IsFiniteMeasure ν] :
    Lp (EuclideanSpace ℝ (Fin n)) ∞ ν →ₗ[ℝ]
      PiLp 2 (fun _ : Fin n => Lp ℝ 2 ν) :=
  (WithLp.linearEquiv 2 ℝ _).symm.toLinearMap.comp
    (LinearMap.pi fun i => (inclusion ∞ 2 (by simp)).comp (coordinate ∞ i))

/-- The source coordinates in Lemma 5.17 are the
canonical L² representatives. -/
theorem source_apply [IsFiniteMeasure ν]
    (v : Lp (EuclideanSpace ℝ (Fin n)) ∞ ν) (i : Fin n) :
    source v i = toL2 (coordinate ∞ i v) := rfl

/-- Multiplication by an integrable scalar coefficient on the entire
bounded-input domain in Lemma 5.17. -/
def multiply (Y : X → ℝ) (hY : Integrable Y ν) : Lp ℝ ∞ ν →ₗ[ℝ] Lp ℝ 1 ν :=
  (((ContinuousLinearMap.mul ℝ ℝ).holderₗ ν ∞ 1 1).flip ((memLp_one_iff_integrable.mpr hY).toLp Y))

/-- The multiplication output in Lemma 5.17 is the
pointwise product, almost everywhere. -/
theorem multiply_ae (Y : X → ℝ) (hY : Integrable Y ν) (f : Lp ℝ ∞ ν) :
    multiply Y hY f =ᵐ[ν] fun x => f x * Y x := by
  filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 1) f ((memLp_one_iff_integrable.mpr hY).toLp Y),
    (memLp_one_iff_integrable.mpr hY).coeFn_toLp] with x hx hy
  change ((ContinuousLinearMap.mul ℝ ℝ).holder 1 f
    ((memLp_one_iff_integrable.mpr hY).toLp Y)) x = _
  simpa only [ContinuousLinearMap.mul_apply',hy] using hx

/-- The multiplication part of the operators in Proposition 5.18 and
Lemma 6.4, with no boundedness assumption on their coefficients. -/
def multiplication (Y : X → Matrix (Fin n) (Fin n) ℝ)
    (hY : ∀ i k, Integrable (fun x => Y x i k) ν) :
    Lp (EuclideanSpace ℝ (Fin n)) ∞ ν →ₗ[ℝ]
      Lp (EuclideanSpace ℝ (Fin n)) 1 ν :=
  ∑ i, (injection 1 i).comp (∑ k, (multiply (fun x => Y x i k) (hY i k)).comp
    (coordinate ∞ k))

/-- Lift a full L² Schur correction to the bounded/integrable spaces
of Lemma 5.17. -/
def schur [IsFiniteMeasure ν]
    (S : PiLp 2 (fun _ : Fin n => Lp ℝ 2 ν) →L[ℝ]
      PiLp 2 (fun _ : Fin n => Lp ℝ 2 ν)) :
    Lp (EuclideanSpace ℝ (Fin n)) ∞ ν →ₗ[ℝ]
      Lp (EuclideanSpace ℝ (Fin n)) 1 ν :=
  ∑ i, (injection 1 i).comp ((inclusion 2 1 (by norm_num)).comp
    ((PiLp.proj 2 (fun _ : Fin n => Lp ℝ 2 ν) i).toLinearMap.comp
      (S.toLinearMap.comp source)))

/-- The whole bounded-input operator of Lemma 5.17,
instantiated by the multiplication-plus-Schur form in both applications. -/
def operator [IsFiniteMeasure ν]
    (Y : X → Matrix (Fin n) (Fin n) ℝ)
    (hY : ∀ i k, Integrable (fun x => Y x i k) ν)
    (S : PiLp 2 (fun _ : Fin n => Lp ℝ 2 ν) →L[ℝ]
      PiLp 2 (fun _ : Fin n => Lp ℝ 2 ν)) :
    Lp (EuclideanSpace ℝ (Fin n)) ∞ ν →ₗ[ℝ]
      Lp (EuclideanSpace ℝ (Fin n)) 1 ν := multiplication Y hY + schur S

/-- Testing one output column in Lemma 5.17 is the
literal scalar expectation. -/
theorem pairing_injection (u : Lp (EuclideanSpace ℝ (Fin n)) ∞ ν)
    (i : Fin n) (f : Lp ℝ 1 ν) :
    pairing u (injection 1 i f) = ∫ x, (coordinate ∞ i u) x * f x ∂ν := by
  rw [pairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [injection_ae 1 i f, coordinate_ae ∞ i u] with x hx hi
  rw [hx,hi]
  simp [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,mul_comm]

/-- Multiplication in Lemma 5.17 has the physical
matrix pairing, and every scalar summand is integrable. -/
theorem pairing_multiplication (Y : X → Matrix (Fin n) (Fin n) ℝ)
    (hY : ∀ i k, Integrable (fun x => Y x i k) ν)
    (u v : Lp (EuclideanSpace ℝ (Fin n)) ∞ ν) :
    pairing u (multiplication Y hY v) =
      ∑ i, ∑ k, ∫ x, (coordinate ∞ i u) x * Y x i k *
        (coordinate ∞ k v) x ∂ν := by
  simp only [multiplication,LinearMap.sum_apply,LinearMap.comp_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [pairing_injection]
  apply integral_congr_ae
  filter_upwards [multiply_ae (fun x => Y x i k) (hY i k) (coordinate ∞ k v)] with x hx
  rw [hx]
  ring

/-- The Schur output in Lemma 5.17 has its original
L² pairing on the whole resolvent domain. -/
theorem pairing_schur [IsFiniteMeasure ν]
    (S : PiLp 2 (fun _ : Fin n => Lp ℝ 2 ν) →L[ℝ]
      PiLp 2 (fun _ : Fin n => Lp ℝ 2 ν))
    (u v : Lp (EuclideanSpace ℝ (Fin n)) ∞ ν) :
    pairing u (schur S v) = inner ℝ (source u) (S (source v)) := by
  simp only [schur,LinearMap.sum_apply,LinearMap.comp_apply,map_sum,
    ContinuousLinearMap.coe_coe,PiLp.proj_apply]
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [pairing_injection,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [inclusion_ae 2 1 (by norm_num) (S (source v) i),
    toL2_ae (coordinate ∞ i u)] with x hx hu
  simp only [source_apply,hx,hu,RCLike.inner_apply,conj_trivial,mul_comm]

/-- Identification of the complete bounded-input operator in
Lemma 5.17 with the two physical form contributions. -/
theorem pairing_operator [IsFiniteMeasure ν]
    (Y : X → Matrix (Fin n) (Fin n) ℝ)
    (hY : ∀ i k, Integrable (fun x => Y x i k) ν)
    (S : PiLp 2 (fun _ : Fin n => Lp ℝ 2 ν) →L[ℝ]
      PiLp 2 (fun _ : Fin n => Lp ℝ 2 ν))
    (u v : Lp (EuclideanSpace ℝ (Fin n)) ∞ ν) :
    pairing u (operator Y hY S v) =
      (∑ i, ∑ k, ∫ x, (coordinate ∞ i u) x * Y x i k *
        (coordinate ∞ k v) x ∂ν) + inner ℝ (source u) (S (source v)) := by
  rw [operator,LinearMap.add_apply,map_add,pairing_multiplication,pairing_schur]

/-- Coordinate injection in Lemma 5.17 has precisely
one nonzero scalar column. -/
theorem coordinate_injection (p : ℝ≥0∞) (i k : Fin n) (f : Lp ℝ p ν) :
    coordinate p i (injection p k f) = if i=k then f else 0 := by
  by_cases h : i=k
  · subst i
    apply Lp.ext
    filter_upwards [coordinate_ae p k (injection p k f),injection_ae p k f] with x hx hy
    simp [hx,hy]
  · apply Lp.ext
    filter_upwards [coordinate_ae p i (injection p k f),injection_ae p k f,
      Lp.coeFn_zero ℝ p ν] with x hx hy hz
    rw [ite_eq_right h]
    change _ = (0 : Lp ℝ p ν) x
    rw [hz]
    simp [hx,hy,h]

/-- A single source in Lemma 5.17 becomes a single
coordinate in the original L² resolvent space. -/
theorem source_injection [IsFiniteMeasure ν] (i : Fin n) (f : Lp ℝ ∞ ν) :
    source (injection ∞ i f) = PiLp.single 2 i (toL2 f) := by
  apply PiLp.ext
  intro k
  change inclusion ∞ 2 (by simp) (coordinate ∞ k (injection ∞ i f)) = _
  rw [coordinate_injection]
  by_cases h : k=i
  · simp [h,inclusion,toL2]
  · simp [h]

/-- The L² source norm in Lemma 5.17 is exactly the
L² norm of the original vector field. -/
theorem source_norm [IsFiniteMeasure ν]
    (u : Lp (EuclideanSpace ℝ (Fin n)) ∞ ν) : ‖source u‖ = ‖toL2 u‖ := by
  have hh := sum_coordinate_norm_sq u
  change (∑ i, ‖source u i‖^2) = ‖toL2 u‖^2 at hh
  rw [← PiLp.norm_sq_eq_of_L2] at hh
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hh

/-- Testing the constructed operator on source columns in
Lemma 5.17 gives the physical point pairing. -/
theorem pairing_operator_injections [IsFiniteMeasure ν]
    (Y : X → Matrix (Fin n) (Fin n) ℝ)
    (hY : ∀ i k, Integrable (fun x => Y x i k) ν)
    (S : PiLp 2 (fun _ : Fin n => Lp ℝ 2 ν) →L[ℝ]
      PiLp 2 (fun _ : Fin n => Lp ℝ 2 ν))
    (φ ψ : Lp ℝ ∞ ν) (i k : Fin n) :
    pairing (injection ∞ i φ) (operator Y hY S (injection ∞ k ψ)) =
      (∫ x, φ x * Y x i k * ψ x ∂ν) +
        inner ℝ (PiLp.single 2 i (toL2 φ)) (S (PiLp.single 2 k (toL2 ψ))) := by
  rw [pairing_operator,source_injection,source_injection]
  congr 1
  have hterm (j l : Fin n) :
      (∫ x, (coordinate ∞ j (injection ∞ i φ)) x * Y x j l *
        (coordinate ∞ l (injection ∞ k ψ)) x ∂ν) =
        if j=i then (if l=k then (∫ x, φ x * Y x i k * ψ x ∂ν) else 0) else 0 := by
    by_cases hj : j=i <;> by_cases hl : l=k
    · subst j; subst l; simp only [coordinate_injection,ite_true]
    · subst j
      rw [coordinate_injection,coordinate_injection,ite_eq_left rfl,ite_eq_right hl]
      simp only [hl,ite_true,ite_false]
      apply integral_eq_zero_of_ae
      filter_upwards [Lp.coeFn_zero ℝ ∞ ν] with x hx
      simp only [hx,Pi.zero_apply,mul_zero]
    · rw [coordinate_injection,ite_eq_right hj]
      simp only [hj,ite_false]
      apply integral_eq_zero_of_ae
      filter_upwards [Lp.coeFn_zero ℝ ∞ ν] with x hx
      simp only [hx,Pi.zero_apply,zero_mul]
    · rw [coordinate_injection,ite_eq_right hj]
      simp only [hj,ite_false]
      apply integral_eq_zero_of_ae
      filter_upwards [Lp.coeFn_zero ℝ ∞ ν] with x hx
      simp only [hx,Pi.zero_apply,zero_mul]
  simp_rw [hterm]
  simp

/-- The reference-column coupling used by Proposition 5.18 and Lemma 6.4
is a continuous linear map on the entire active L² space. -/
def coupling {ι : Type*} [Fintype ι] (a : Fin n → ι → ℝ) :
    PiLp 2 (fun _ : Fin n => Lp ℝ 2 ν) →L[ℝ] PiLp 2 (fun _ : ι => Lp ℝ 2 ν) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => Lp ℝ 2 ν)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j => ∑ i, a i j • PiLp.proj 2 (fun _ : Fin n => Lp ℝ 2 ν) i)

/-- The coupling in Lemma 5.17 is the written sum of
reference columns times their scalar sources. -/
theorem coupling_apply {ι : Type*} [Fintype ι] (a : Fin n → ι → ℝ)
    (f : PiLp 2 (fun _ : Fin n => Lp ℝ 2 ν)) (j : ι) :
    coupling a f j = ∑ i, a i j • f i := by
  simp [coupling]

/-- A column source in Lemma 5.17 produces exactly
its reference tensor in the exterior space. -/
theorem coupling_single {ι : Type*} [Fintype ι] (a : Fin n → ι → ℝ)
    (i : Fin n) (f : Lp ℝ 2 ν) :
    coupling a (PiLp.single 2 i f) = WithLp.toLp 2 (fun j => a i j • f) := by
  apply PiLp.ext
  intro j
  simp [coupling_apply,PiLp.single_apply,smul_ite]

/-- The full Schur correction used in Lemma 5.17:
compose the coupling, exterior resolvent and transpose coupling. -/
def reduced {ι : Type*} [Fintype ι] (a : Fin n → ι → ℝ)
    (K : PiLp 2 (fun _ : ι => Lp ℝ 2 ν) →L[ℝ] PiLp 2 (fun _ : ι => Lp ℝ 2 ν))
    (β : ℝ) : PiLp 2 (fun _ : Fin n => Lp ℝ 2 ν) →L[ℝ]
      PiLp 2 (fun _ : Fin n => Lp ℝ 2 ν) :=
  β^2 • (coupling a).adjoint.comp (K.comp (coupling a))

/-- The reduced operator in Lemma 5.17 retains the
original exterior resolvent pairing, including the temperature factor. -/
theorem inner_reduced {ι : Type*} [Fintype ι] (a : Fin n → ι → ℝ)
    (K : PiLp 2 (fun _ : ι => Lp ℝ 2 ν) →L[ℝ] PiLp 2 (fun _ : ι => Lp ℝ 2 ν))
    (β : ℝ) (u v : PiLp 2 (fun _ : Fin n => Lp ℝ 2 ν)) :
    inner ℝ u (reduced a K β v) = β^2 * inner ℝ (coupling a u) (K (coupling a v)) := by
  simp only [reduced,smul_apply,ContinuousLinearMap.comp_apply,
    inner_smul_right,ContinuousLinearMap.adjoint_inner_right]

/-- The original bounded scalar tests of Lemma 5.17
are bounded almost everywhere by their finite essential norm. -/
theorem bounded_ae_essentialNorm (f : BoundedL2Pairings.boundedSubmodule ν) :
    ∀ᵐ x ∂ν, |f.val x| ≤ (eLpNorm (f.val : X → ℝ) ∞ ν).toReal := by
  simpa only [Real.norm_eq_abs,← toReal_eLpNorm] using
    ae_le_lpNorm_exponent_top (BoundedL2Pairings.memLp_top f)

/-- The same bounded scalar in Lemma 5.17, now with
its actual L∞ norm, starting from the existing bounded-L² carrier. -/
def ofBoundedScalar : BoundedL2Pairings.boundedSubmodule ν →ₗ[ℝ] Lp ℝ ∞ ν where
  toFun f := (BoundedL2Pairings.memLp_top f).toLp f.val
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(BoundedL2Pairings.memLp_top (f+g)).coeFn_toLp,
      (BoundedL2Pairings.memLp_top f).coeFn_toLp,
      (BoundedL2Pairings.memLp_top g).coeFn_toLp,
      Lp.coeFn_add f.val g.val,
      Lp.coeFn_add ((BoundedL2Pairings.memLp_top f).toLp f.val)
        ((BoundedL2Pairings.memLp_top g).toLp g.val)] with x h₁ h₂ h₃ h₄ h₅
    rw [h₁,h₅]
    simp only [Pi.add_apply]
    rw [h₂,h₃]
    exact h₄
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(BoundedL2Pairings.memLp_top (c • f)).coeFn_toLp,
      (BoundedL2Pairings.memLp_top f).coeFn_toLp,Lp.coeFn_smul c f.val,
      Lp.coeFn_smul c ((BoundedL2Pairings.memLp_top f).toLp f.val)] with x h₁ h₂ h₃ h₄
    simp only [RingHom.id_apply]
    rw [h₁,h₄]
    simp only [Pi.smul_apply]
    rw [h₂]
    exact h₃

/-- The L∞ conversion in Lemma 5.17 preserves the
existing scalar representative. -/
theorem ofBoundedScalar_ae (f : BoundedL2Pairings.boundedSubmodule ν) :
    ofBoundedScalar f =ᵐ[ν] f.val := (BoundedL2Pairings.memLp_top f).coeFn_toLp

/-- The L∞ conversion in Lemma 5.17 preserves the
existing L² class. -/
theorem toL2_ofBoundedScalar [IsFiniteMeasure ν]
    (f : BoundedL2Pairings.boundedSubmodule ν) : toL2 (ofBoundedScalar f) = f.val := by
  apply Lp.ext
  exact (toL2_ae (ofBoundedScalar f)).trans (ofBoundedScalar_ae f)

/-- The vector field of Lemma 5.17 assembled from
bounded physical scalar coordinates. -/
def field (v : Fin n → BoundedL2Pairings.boundedSubmodule ν) :
    Lp (EuclideanSpace ℝ (Fin n)) ∞ ν := ∑ i, injection ∞ i (ofBoundedScalar (v i))

/-- Every coordinate of the bounded field in Lemma 5.17
is its original bounded physical scalar coordinate. -/
theorem coordinate_field (v : Fin n → BoundedL2Pairings.boundedSubmodule ν)
    (i : Fin n) : coordinate ∞ i (field v) = ofBoundedScalar (v i) := by
  simp [field,map_sum,coordinate_injection]

/-- The L² source of the field in Lemma 5.17 is exactly
the original physical tuple, with no change of norm or measure. -/
theorem source_field [IsFiniteMeasure ν]
    (v : Fin n → BoundedL2Pairings.boundedSubmodule ν) :
    source (field v) = WithLp.toLp 2 (fun i => (v i).val) := by
  apply PiLp.ext
  intro i
  rw [source_apply,coordinate_field,toL2_ofBoundedScalar]

/-- The small coordinate sum of Lemma 5.17 is precisely
the original scalar L² sum. -/
theorem toL2_coordinateSum_field [IsFiniteMeasure ν]
    (v : Fin n → BoundedL2Pairings.boundedSubmodule ν) :
    toL2 (coordinateSum ∞ (field v)) = ∑ i, (v i).val := by
  change inclusion ∞ 2 (by simp) (coordinateSum ∞ (field v)) = _
  simp only [coordinateSum,LinearMap.sum_apply,map_sum,coordinate_field]
  apply Finset.sum_congr rfl
  intro i _
  exact toL2_ofBoundedScalar (v i)

/-- The bounded-input operator in Lemma 5.17 identifies
with the original physical integrals on bounded L² tuples. -/
theorem pairing_operator_fields [IsFiniteMeasure ν]
    (Y : X → Matrix (Fin n) (Fin n) ℝ)
    (hY : ∀ i k, Integrable (fun x => Y x i k) ν)
    (S : PiLp 2 (fun _ : Fin n => Lp ℝ 2 ν) →L[ℝ]
      PiLp 2 (fun _ : Fin n => Lp ℝ 2 ν))
    (u v : Fin n → BoundedL2Pairings.boundedSubmodule ν) :
    pairing (field u) (operator Y hY S (field v)) =
      (∑ i, ∑ k, ∫ x, (u i).val x * Y x i k * (v k).val x ∂ν) +
        inner ℝ (WithLp.toLp 2 (fun i => (u i).val))
          (S (WithLp.toLp 2 (fun i => (v i).val))) := by
  rw [pairing_operator,source_field,source_field]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  simp only [coordinate_field]
  apply integral_congr_ae
  filter_upwards [ofBoundedScalar_ae (u i),ofBoundedScalar_ae (v k)] with x hu hv
  rw [hu,hv]

/-- The essential bound used in Lemma 5.17 controls
the norm of a converted bounded scalar class. -/
theorem ofBoundedScalar_norm_le (f : BoundedL2Pairings.boundedSubmodule ν)
    (B : ℝ) (hB : 0 ≤ B) (hf : ∀ᵐ x ∂ν, |f.val x| ≤ B) :
    ‖ofBoundedScalar f‖ ≤ B := by
  rw [Lp.norm_def,eLpNorm_congr_ae (ofBoundedScalar_ae f)]
  exact BoundedL2Pairings.essentialNorm_le f B hB hf

/-- Injection of one scalar column in Lemma 5.17
preserves its essential norm. -/
theorem injection_norm (i : Fin n) (f : Lp ℝ ∞ ν) : ‖injection ∞ i f‖ = ‖f‖ := by
  apply le_antisymm
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [injection_ae ∞ i f] with x hx
    simp [hx,norm_smul]
  · simpa only [coordinate_injection,ite_true] using
      coordinate_norm_le ∞ i (injection ∞ i f)

/-- A coordinatewise essential bound gives a polynomial vector bound
for the exceptional remainder in Lemma 5.17. -/
theorem field_norm_le (v : Fin n → BoundedL2Pairings.boundedSubmodule ν)
    (B : ℝ) (hB : 0 ≤ B) (hv : ∀ i, ∀ᵐ x ∂ν, |(v i).val x| ≤ B) :
    ‖field v‖ ≤ (n : ℝ)*B := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i : Fin n, B := Finset.sum_le_sum fun i _ =>
      (injection_norm i (ofBoundedScalar (v i))).le.trans
        (ofBoundedScalar_norm_le (v i) B hB (hv i))
    _ = _ := by simp

/-- The reversed exterior pairing in Proposition 5.18 is represented by
the adjoint resolvent, without adding a symmetry assumption. -/
theorem inner_reduced_adjoint {ι : Type*} [Fintype ι] (a : Fin n → ι → ℝ)
    (K : PiLp 2 (fun _ : ι => Lp ℝ 2 ν) →L[ℝ] PiLp 2 (fun _ : ι => Lp ℝ 2 ν))
    (β : ℝ) (u v : PiLp 2 (fun _ : Fin n => Lp ℝ 2 ν)) :
    inner ℝ u (reduced a K.adjoint β v) =
      β^2 * inner ℝ (coupling a v) (K (coupling a u)) := by
  rw [inner_reduced,ContinuousLinearMap.adjoint_inner_right,real_inner_comm]

end Riesz2.BoundedPerturbationOperator
