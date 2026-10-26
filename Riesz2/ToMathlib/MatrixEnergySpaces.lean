/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.IsClosedScalarDirichletForm
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Riesz2.Frozen.WeightedWeakSolution
public import Riesz2.Frozen.ZeroSumComponents
public import Riesz2.ToMathlib.IntrinsicScalarForms
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Measurable
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Tactic

/-!
# Complete finite matrix-energy spaces

Form domains for Subsections 3.1, 3.5, 5.1 and Lemma 4.4.

`ScalarFormHilbert.Space` equips the scalar domain with its complete form metric.
`MatrixEnergy.Space` is the closed graph of a possibly unbounded rectangular
matrix multiplier, intersected with a fixed component subspace.
`MatrixEnergy.Natural` uses the measurable positive square root and is
equivalent to `WeightedFormDomain`.

The continuous weak form agrees with `WeightedWeakSolution`.
All cross terms are integrable. The graph norm is mass plus diffusion plus matrix
energy. A coercive matrix bound on the constrained components gives coercivity
in this norm. Component and base dimensions are independent.
Empty component sets and arbitrary measures are allowed.
The final bridge identifies the scalar jet completion with the scalar form
domain and preserves its form metric.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Topology

namespace Riesz2.ScalarFormHilbert

variable {α : Type*} [MeasurableSpace α] {ρ : Measure α}

/-- The existing scalar domain, equipped below with its form metric. -/
def Space (Q : ScalarFormData ρ) (_hQ : IsClosedScalarDirichletForm Q) : Type _ := Q.1

variable (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q)

instance : AddCommGroup (Space Q hQ) := inferInstanceAs (AddCommGroup Q.1)
instance : Module ℝ (Space Q hQ) := inferInstanceAs (Module ℝ Q.1)

/-- Identity of the form-domain carrier with the domain. -/
def equiv : Space Q hQ ≃ₗ[ℝ] Q.1 := LinearEquiv.refl ℝ Q.1

/-- Positive definite form consisting of mass plus scalar energy. -/
@[instance_reducible] def innerCore : InnerProductSpace.Core ℝ (Space Q hQ) where
  inner f g := inner ℝ (equiv Q hQ f).val (equiv Q hQ g).val + Q.2 (equiv Q hQ f) (equiv Q hQ g)
  conj_inner_symm f g := by
    simp only [conj_trivial, real_inner_comm, hQ.2.1]
  re_inner_nonneg f := add_nonneg real_inner_self_nonneg (hQ.2.2.1 _)
  add_left f g h := by simp [map_add, inner_add_left]; ring
  smul_left f g a := by simp [map_smul, real_inner_smul_left]; ring
  definite f hf := by
    have hv : inner ℝ (equiv Q hQ f).val (equiv Q hQ f).val = 0 :=
      le_antisymm (by linarith [hQ.2.2.1 (equiv Q hQ f)]) real_inner_self_nonneg
    exact (equiv Q hQ).injective (Subtype.ext (inner_self_eq_zero.mp hv))

instance : NormedAddCommGroup (Space Q hQ) := (innerCore Q hQ).toNormedAddCommGroup
instance : InnerProductSpace ℝ (Space Q hQ) := InnerProductSpace.ofCore (innerCore Q hQ).toCore

/-- Scalar mass plus energy is the square of the form norm. -/
theorem norm_sq (f : Space Q hQ) :
    ‖f‖ ^ 2 = ‖(equiv Q hQ f).val‖ ^ 2 + Q.2 (equiv Q hQ f) (equiv Q hQ f) := by
  rw [← real_inner_self_eq_norm_sq]
  change inner ℝ (equiv Q hQ f).val (equiv Q hQ f).val + Q.2 _ _ = _
  rw [real_inner_self_eq_norm_sq]

/-- Inclusion of the scalar form domain into L². -/
def value : Space Q hQ →L[ℝ] Lp ℝ 2 ρ :=
  (((Q.1).subtype).comp (equiv Q hQ).toLinearMap).mkContinuous 1 (fun f => by
    simp only [one_mul]
    change ‖(equiv Q hQ f).val‖ ≤ ‖f‖
    have hn := norm_sq Q hQ f
    have he := hQ.2.2.1 (equiv Q hQ f)
    nlinarith [norm_nonneg f, norm_nonneg (equiv Q hQ f).val])

theorem value_apply (f : Space Q hQ) : value Q hQ f = (equiv Q hQ f).val := rfl

theorem value_injective : Function.Injective (value Q hQ) := by
  intro f g he
  exact (equiv Q hQ).injective (Subtype.ext he)

/-- The bilinear energy in the original encoding. -/
theorem inner_eq (f g : Space Q hQ) :
    inner ℝ f g = inner ℝ (value Q hQ f) (value Q hQ g) +
      Q.2 (equiv Q hQ f) (equiv Q hQ g) := rfl

instance : CompleteSpace (Space Q hQ) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro f hf
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete ((value Q hQ).lipschitzWith.cauchySeq_comp hf)
  have hc : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ i j : ℕ, k ≤ i → k ≤ j →
      ‖(equiv Q hQ (f i)).val - (equiv Q hQ (f j)).val‖ ^ 2 +
        Q.2 (equiv Q hQ (f i) - equiv Q hQ (f j)) (equiv Q hQ (f i) - equiv Q hQ (f j)) < ε := by
    intro ε hε
    obtain ⟨k, hk⟩ := Metric.cauchySeq_iff.mp hf (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
    refine ⟨k, fun i j hi hj => ?_⟩
    have h := hk i hi j hj
    rw [dist_eq_norm] at h
    have hs := norm_sq Q hQ (f i - f j)
    change ‖f i - f j‖ ^ 2 = ‖(equiv Q hQ (f i)).val - (equiv Q hQ (f j)).val‖ ^ 2 + Q.2 (equiv Q hQ (f i) - equiv Q hQ (f j)) (equiv Q hQ (f i) - equiv Q hQ (f j)) at hs
    nlinarith [Real.sq_sqrt hε.le, norm_nonneg (f i - f j)]
  obtain ⟨g, hg, he⟩ := hQ.2.2.2.1 (fun k => equiv Q hQ (f k)) u hu hc
  refine ⟨(equiv Q hQ).symm g, ?_⟩
  have hv : Tendsto (fun k => ‖value Q hQ (f k) - g.val‖ ^ 2) atTop (𝓝 0) := by
    have := (hu.sub (tendsto_const_nhds (x := u))).norm.pow 2
    simpa [hg] using this
  have hn : Tendsto (fun k => ‖f k - (equiv Q hQ).symm g‖ ^ 2) atTop (𝓝 0) := by
    convert hv.add he using 1
    · ext k
      rw [norm_sq]
      simp only [map_sub, LinearEquiv.apply_symm_apply, Submodule.coe_sub, value_apply]
    · norm_num
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have := hn.sqrt
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using this

end Riesz2.ScalarFormHilbert

namespace Riesz2.MatrixEnergy

open Set
open scoped BigOperators ENNReal

variable {α ι κ H : Type*} [MeasurableSpace α] {ρ : Measure α}

/-- Simultaneous a.e. convergence of a subsequence of finitely many L² sequences.
No finiteness assumption on the measure is needed. -/
theorem exists_subseq_ae [Fintype ι] (f : ℕ → ι → Lp ℝ 2 ρ) (g : ι → Lp ℝ 2 ρ)
    (h : ∀ i, Tendsto (fun n => f n i) atTop (𝓝 (g i))) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂ρ,
      ∀ i, Tendsto (fun n => f (ns n) i x) atTop (𝓝 (g i x)) := by
  classical
  have aux (s : Finset ι) : ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂ρ,
      ∀ i ∈ s, Tendsto (fun n => f (ns n) i x) atTop (𝓝 (g i x)) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨id, strictMono_id, Eventually.of_forall (by simp)⟩
    | @insert i s hi ih =>
      obtain ⟨ns, hns, hn⟩ := ih
      obtain ⟨ms, hms, hm⟩ :=
        (tendstoInMeasure_of_tendsto_Lp ((h i).comp hns.tendsto_atTop)).exists_seq_tendsto_ae
      refine ⟨ns ∘ ms, hns.comp hms, ?_⟩
      filter_upwards [hn, hm] with x hx hy
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hy
      · exact (hx j hj).comp hms.tendsto_atTop
  obtain ⟨ns, hns, hn⟩ := aux Finset.univ
  exact ⟨ns, hns, hn.mono (by simp)⟩

section ClosedGraph

variable [Fintype ι] [Fintype κ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (v : ι → H →L[ℝ] Lp ℝ 2 ρ)

/-- Scalar Sobolev data together with all matrix-multiplier components. -/
abbrev Jet := WithLp 2 (H × PiLp 2 (fun _ : κ => Lp ℝ 2 ρ))

/-- The scalar value of a jet. -/
def input (i : ι) : Jet (κ := κ) (ρ := ρ) (H := H) →L[ℝ] Lp ℝ 2 ρ :=
  (v i).comp (WithLp.fstL 2 ℝ _ _)

/-- One matrix-energy component of a jet. -/
def output (k : κ) : Jet (κ := κ) (ρ := ρ) (H := H) →L[ℝ] Lp ℝ 2 ρ :=
  (PiLp.proj 2 (fun _ : κ => Lp ℝ 2 ρ) k).comp (WithLp.sndL 2 ℝ _ _)

variable (B : α → Matrix κ ι ℝ) (S : Submodule ℝ (ι → ℝ))

set_option backward.isDefEq.respectTransparency false in
/-- The full constrained graph of multiplication by `B`. It is not a core closure.
`B` may be rectangular or unbounded, and the component space is independent of the base. -/
def graph : Submodule ℝ (Jet (κ := κ) (ρ := ρ) (H := H)) where
  carrier := {z | ∀ᵐ x ∂ρ, (fun i => input v i z x) ∈ S ∧
    ∀ k, output k z x = ∑ i, B x k i * input v i z x}
  zero_mem' := by
    have hz : ∀ᵐ x ∂ρ, ∀ i : ι ⊕ κ, (0 : Lp ℝ 2 ρ) x = 0 :=
      ae_all_iff.mpr (fun _ => Lp.coeFn_zero ℝ 2 ρ)
    filter_upwards [hz] with x hx
    have hi : (fun i => input (κ := κ) v i 0 x) = (fun _ => (0 : ℝ)) := funext (fun i => by simpa only [map_zero] using hx (.inl i))
    refine ⟨hi ▸ S.zero_mem, fun k => ?_⟩
    rw [map_zero, hx (.inr k)]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [map_zero, hx (.inl i), mul_zero]
  add_mem' := by
    intro z w hz hw
    have hi : ∀ᵐ x ∂ρ, ∀ i, input v i (z + w) x = input v i z x + input v i w x :=
      ae_all_iff.mpr (fun i => by simpa only [map_add, Filter.EventuallyEq, Pi.add_apply] using Lp.coeFn_add (input v i z) (input v i w))
    have ho : ∀ᵐ x ∂ρ, ∀ k, output k (z + w) x = output k z x + output k w x :=
      ae_all_iff.mpr (fun k => by simpa only [map_add, Filter.EventuallyEq, Pi.add_apply] using Lp.coeFn_add (output k z) (output k w))
    filter_upwards [hz, hw, hi, ho] with x hx hy hix hox
    refine ⟨?_, fun k => ?_⟩
    · convert S.add_mem hx.1 hy.1 using 1
      funext i
      exact hix i
    · simp only [hox, hx.2, hy.2, hix, mul_add, Finset.sum_add_distrib]
  smul_mem' := by
    intro a z hz
    have hi : ∀ᵐ x ∂ρ, ∀ i, input v i (a • z) x = a * input v i z x :=
      ae_all_iff.mpr (fun i => by simpa only [map_smul, Filter.EventuallyEq, Pi.smul_apply, smul_eq_mul] using Lp.coeFn_smul a (input v i z))
    have ho : ∀ᵐ x ∂ρ, ∀ k, output k (a • z) x = a * output k z x :=
      ae_all_iff.mpr (fun k => by simpa only [map_smul, Filter.EventuallyEq, Pi.smul_apply, smul_eq_mul] using Lp.coeFn_smul a (output k z))
    filter_upwards [hz, hi, ho] with x hx hix hox
    refine ⟨?_, fun k => ?_⟩
    · convert S.smul_mem a hx.1 using 1
      funext i
      exact hix i
    · simp only [hox, hx.2, hix, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)

/-- Matrix multiplication has a closed graph, including every fixed component constraint.
Measurability is needed to identify the domain, but not for closedness of the graph. -/
theorem isClosed_graph : IsClosed (graph v B S : Set (Jet (κ := κ) (ρ := ρ) (H := H))) := by
  apply isSeqClosed_iff_isClosed.mp
  intro w z hw ht
  let c : ι ⊕ κ → Jet (κ := κ) (ρ := ρ) (H := H) →L[ℝ] Lp ℝ 2 ρ :=
    Sum.elim (input v) output
  obtain ⟨ns, hns, hn⟩ := exists_subseq_ae (fun n i => c i (w n)) (fun i => c i z)
    (fun i => ((c i).continuous.tendsto _).comp ht)
  have hm : ∀ᵐ x ∂ρ, ∀ n, (fun i => input v i (w (ns n)) x) ∈ S ∧
      ∀ k, output k (w (ns n)) x = ∑ i, B x k i * input v i (w (ns n)) x :=
    ae_all_iff.mpr (fun n => hw (ns n))
  filter_upwards [hn, hm] with x hx hy
  refine ⟨?_, fun k => ?_⟩
  · exact S.closed_of_finiteDimensional.mem_of_tendsto
      (tendsto_pi_nhds.mpr (fun i => hx (.inl i))) (Eventually.of_forall (fun n => (hy n).1))
  · have hlim := tendsto_finsetSum Finset.univ (fun i _ =>
        (tendsto_const_nhds (x := B x k i)).mul (hx (.inl i)))
    exact tendsto_nhds_unique (hx (.inr k))
      (hlim.congr' (Eventually.of_forall (fun n => ((hy n).2 k).symm)))

/-- The full constrained matrix graph with its Hilbert graph norm. -/
abbrev Space := graph v B S

instance completeSpace [CompleteSpace H] : CompleteSpace (Space v B S) :=
  (isClosed_graph v B S).completeSpace_coe

/-- Sobolev coordinate of a matrix graph element. -/
def base : Space v B S →L[ℝ] H :=
  (WithLp.fstL 2 ℝ _ _).comp (graph v B S).subtypeL

/-- Matrix multiplier coordinate of a graph element. -/
def multiplier : Space v B S →L[ℝ] PiLp 2 (fun _ : κ => Lp ℝ 2 ρ) :=
  (WithLp.sndL 2 ℝ _ _).comp (graph v B S).subtypeL

/-- All value components, bundled with the finite Hilbert product metric. -/
def allValues : Space v B S →L[ℝ] PiLp 2 (fun _ : ι => Lp ℝ 2 ρ) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => Lp ℝ 2 ρ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => (input v i).comp (graph v B S).subtypeL))

/-- The multiplier is determined by the Sobolev coordinate. No extra graph points exist. -/
theorem base_injective :
    Function.Injective (base v B S) := by
  intro z w he
  apply Subtype.ext
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext he
  apply PiLp.ext
  intro k
  apply Lp.ext
  filter_upwards [z.property, w.property] with x hx hy
  change output k z.val x = output k w.val x
  rw [hx.2 k, hy.2 k]
  exact Finset.sum_congr rfl (fun i _ => by
    have := congrArg (fun u : H => v i u x) he
    change B x k i * input v i z.val x = B x k i * input v i w.val x
    exact congrArg (B x k i * ·) this)

/-- The full graph norm has precisely its two expected squared terms. -/
theorem norm_sq (z : Space v B S) :
    ‖z‖ ^ 2 = ‖base v B S z‖ ^ 2 + ‖multiplier v B S z‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 z.val

/-- The Hilbert pairing is the Sobolev pairing plus the matrix multiplier pairing. -/
theorem inner_eq (z w : Space v B S) :
    inner ℝ z w = inner ℝ (base v B S z) (base v B S w) +
      inner ℝ (multiplier v B S z) (multiplier v B S w) :=
  WithLp.prod_inner_apply z.val w.val

end ClosedGraph

section Factorization

open Matrix

variable [Fintype ι] [Fintype κ]

/-- The double sum is the usual matrix bilinear pairing. -/
theorem matrixFieldPair_eq_dot (M : α → Matrix ι ι ℝ)
    (u w : ι → Lp ℝ 2 ρ) (x : α) :
    matrixFieldPair M u w x = (fun i => u i x) ⬝ᵥ (M x *ᵥ fun i => w i x) := by
  simp only [matrixFieldPair, dotProduct, mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

/-- Gram factorization identifies all cross pairings, not just the diagonal energy. -/
theorem matrixFieldPair_factor (M : α → Matrix ι ι ℝ) (B : α → Matrix κ ι ℝ)
    {x : α} (hB : (B x)ᵀ * B x = M x) (u w : ι → Lp ℝ 2 ρ) :
    matrixFieldPair M u w x =
      ∑ k, (∑ i, B x k i * u i x) * (∑ i, B x k i * w i x) := by
  rw [matrixFieldPair_eq_dot, ← hB, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  rfl

/-- A measurable Gram factor is L² exactly when the diagonal energy is integrable. -/
theorem integrable_iff_memLp_factor (M : α → Matrix ι ι ℝ) (B : α → Matrix κ ι ℝ)
    (hB : ∀ k i, AEStronglyMeasurable (fun x => B x k i) ρ)
    (hfactor : ∀ᵐ x ∂ρ, (B x)ᵀ * B x = M x) (u : ι → Lp ℝ 2 ρ) :
    Integrable (matrixFieldPair M u u) ρ ↔
      ∀ k, MemLp (fun x => ∑ i, B x k i * u i x) 2 ρ := by
  classical
  have hm k : AEStronglyMeasurable (fun x => ∑ i, B x k i * u i x) ρ :=
    Finset.aestronglyMeasurable_fun_sum Finset.univ (fun i _ => (hB k i).mul (Lp.aestronglyMeasurable (u i)))
  have he : matrixFieldPair M u u =ᵐ[ρ]
      fun x => ∑ k, (∑ i, B x k i * u i x) ^ 2 := by
    filter_upwards [hfactor] with x hx
    simpa only [sq] using matrixFieldPair_factor M B hx u u
  rw [integrable_congr he]
  constructor
  · intro h k
    apply (memLp_two_iff_integrable_sq (hm k)).mpr
    apply h.mono' ((hm k).pow 2)
    exact Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      change (∑ i, B x k i * u i x) ^ 2 ≤ ∑ k, (∑ i, B x k i * u i x) ^ 2
      exact Finset.single_le_sum (f := fun j => (∑ i, B x j i * u i x) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ k))
  · intro h
    exact integrable_finsetSum _ (fun k _ => (h k).integrable_sq)

end Factorization

section NaturalSpace

open Matrix ScalarFormHilbert
open scoped MatrixOrder Matrix.Norms.L2Operator

variable [Fintype ι] [DecidableEq ι]

-- The measurable structure is the entrywise one, with the unchanged product topology.
local instance : MeasurableSpace (Matrix ι ι ℝ) :=
  inferInstanceAs (MeasurableSpace (ι → ι → ℝ))
local instance : BorelSpace (Matrix ι ι ℝ) :=
  inferInstanceAs (BorelSpace (ι → ι → ℝ))

variable (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q)

/-- The finite Hilbert product of the existing scalar form domains. -/
abbrev Vector := PiLp 2 (fun _ : ι => ScalarFormHilbert.Space Q hQ)

/-- Value of one component of a finite Sobolev vector. -/
def vectorValue (i : ι) : Vector (ι := ι) Q hQ →L[ℝ] Lp ℝ 2 ρ :=
  (ScalarFormHilbert.value Q hQ).comp (PiLp.proj 2 _ i)

/-- The original tuple of scalar-domain elements underlying a Sobolev vector. -/
def vectorEquiv : Vector (ι := ι) Q hQ ≃ₗ[ℝ] (ι → Q.1) :=
  (WithLp.linearEquiv 2 ℝ _).trans (LinearEquiv.piCongrRight (fun _ => ScalarFormHilbert.equiv Q hQ))

/-- Canonical square-root factorization of a nonnegative real matrix. -/
theorem sqrt_factor (M : Matrix ι ι ℝ) (hM : M.PosSemidef) :
    (CFC.sqrt M)ᵀ * CFC.sqrt M = M := by
  have hs : (CFC.sqrt M).PosSemidef := (CFC.sqrt_nonneg M).posSemidef
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial, hs.isHermitian.eq,
    CFC.sqrt_mul_sqrt_self M hM.nonneg]

/-- Measurability of each entry of the canonical positive square root. -/
theorem measurable_sqrt_entries (M : α → Matrix ι ι ℝ)
    (hM : ∀ i j, Measurable (fun x => M x i j)) (i j : ι) :
    Measurable (fun x => CFC.sqrt (M x) i j) := by
  have h : Measurable M := measurable_pi_iff.mpr (fun i => measurable_pi_iff.mpr (hM i))
  exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (CFC.measurable_sqrt.comp h))

variable (M : α → Matrix ι ι ℝ) (S : Submodule ℝ (ι → ℝ))

/-- Natural matrix-energy space for an a.e. nonnegative matrix, with fixed component
constraint. Its carrier is the closed square-root graph. The equivalence `naturalEquiv`
identifies it with `WeightedFormDomain`. -/
abbrev Natural (_hM : ∀ᵐ x ∂ρ, (M x).PosSemidef) := Space (vectorValue (ι := ι) Q hQ) (fun x => CFC.sqrt (M x)) S

variable (hM : ∀ᵐ x ∂ρ, (M x).PosSemidef)

/-- Tuple of scalar-domain elements represented by a graph element. -/
def tuple : Natural Q hQ M S hM →ₗ[ℝ] (ι → Q.1) :=
  { toFun := fun z => vectorEquiv Q hQ (WithLp.ofLp z.val).1
    map_add' := fun _ _ => (vectorEquiv Q hQ).map_add _ _
    map_smul' := fun a _ => (vectorEquiv Q hQ).map_smul a _ }

/-- The L² values of the tuple are the graph's input coordinates. -/
theorem tuple_value (z : Natural Q hQ M S hM) (i : ι) :
    (tuple Q hQ M S hM z i).val = input (vectorValue Q hQ) i z.val := rfl

/-- The matrix cross integrand equals the L² multiplier cross integrand a.e. -/
theorem pair_ae (z w : Natural Q hQ M S hM) :
    matrixFieldPair M (fun i => (tuple Q hQ M S hM z i).val)
      (fun i => (tuple Q hQ M S hM w i).val) =ᵐ[ρ]
      fun x => ∑ i, output i z.val x * output i w.val x := by
  filter_upwards [hM, z.property, w.property] with x hx hz hw
  rw [matrixFieldPair_factor M (fun y => CFC.sqrt (M y)) (sqrt_factor (M x) hx)]
  exact Finset.sum_congr rfl (fun i _ => by rw [hz.2 i, hw.2 i]; rfl)

/-- Matrix cross terms are integrable on the entire natural domain. -/
theorem integrable_pair (z w : Natural Q hQ M S hM) :
    Integrable (matrixFieldPair M (fun i => (tuple Q hQ M S hM z i).val)
      (fun i => (tuple Q hQ M S hM w i).val)) ρ := by
  apply (integrable_congr (pair_ae Q hQ M S hM z w)).mpr
  exact integrable_finsetSum _ (fun i _ => by
    simpa only [Real.inner_apply] using L2.integrable_inner (𝕜 := ℝ) (output i z.val) (output i w.val))

/-- Every graph element belongs to the existing `WeightedFormDomain`. -/
theorem tuple_mem (z : Natural Q hQ M S hM) :
    WeightedFormDomain Q M S (tuple Q hQ M S hM z) := by
  refine ⟨?_, integrable_pair Q hQ M S hM z z⟩
  filter_upwards [z.property] with x hx
  exact hx.1

/-- Uniqueness of the graph representative of a tuple. -/
theorem tuple_injective : Function.Injective (tuple Q hQ M S hM) := by
  intro z w h
  apply base_injective (vectorValue Q hQ) (fun x => CFC.sqrt (M x)) S
  exact (vectorEquiv Q hQ).injective h

/-- The natural graph contains every finite-energy tuple, including unbounded
measurable coefficients and arbitrary component constraints. -/
theorem exists_tuple (hMmeas : ∀ i j, Measurable (fun x => M x i j))
    (u : ι → Q.1)
    (hu : WeightedFormDomain Q M S u) : ∃ z : Natural Q hQ M S hM, tuple Q hQ M S hM z = u := by
  let B : α → Matrix ι ι ℝ := fun x => CFC.sqrt (M x)
  have hB i j : AEStronglyMeasurable (fun x => B x i j) ρ :=
    (measurable_sqrt_entries M hMmeas i j).aestronglyMeasurable
  have hf : ∀ᵐ x ∂ρ, (B x)ᵀ * B x = M x := hM.mono (fun x hx => sqrt_factor (M x) hx)
  have hL := (integrable_iff_memLp_factor M B hB hf (fun i => (u i).val)).mp hu.2
  let e : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ) :=
    WithLp.toLp 2 (fun i => (hL i).toLp (fun x => ∑ j, B x i j * (u j).val x))
  let z : Jet (κ := ι) (ρ := ρ) (H := Vector Q hQ) :=
    WithLp.toLp 2 ((vectorEquiv Q hQ).symm u, e)
  have hz : z ∈ graph (vectorValue Q hQ) B S := by
    have he : ∀ᵐ x ∂ρ, ∀ i, output i z x = ∑ j, B x i j * (u j).val x :=
      ae_all_iff.mpr (fun i => (hL i).coeFn_toLp)
    filter_upwards [hu.1, he] with x hx hy
    exact ⟨hx, hy⟩
  exact ⟨⟨z, hz⟩, (vectorEquiv Q hQ).apply_symm_apply u⟩

/-- The image of the complete graph as a submodule of the scalar tuples. -/
def domainSubmodule : Submodule ℝ (ι → Q.1) := (tuple Q hQ M S hM).range

/-- The submodule carrier is exactly the finite-energy predicate (Subsection 3.5). -/
theorem mem_domainSubmodule_iff (hMmeas : ∀ i j, Measurable (fun x => M x i j))
    (u : ι → Q.1) :
    u ∈ domainSubmodule Q hQ M S hM ↔ WeightedFormDomain Q M S u := by
  constructor
  · rintro ⟨z, rfl⟩
    exact tuple_mem Q hQ M S hM z
  · exact exists_tuple Q hQ M S hM hMmeas u

/-- Linear identification of the complete graph with the entire domain.
The graph metric, rather than the inherited L² metric on the image, is complete. -/
def naturalEquiv : Natural Q hQ M S hM ≃ₗ[ℝ] domainSubmodule Q hQ M S hM :=
  LinearEquiv.ofInjective (tuple Q hQ M S hM) (tuple_injective Q hQ M S hM)

/-- Simultaneous L² values of a natural-domain vector. -/
def values : Natural Q hQ M S hM →L[ℝ] PiLp 2 (fun _ : ι => Lp ℝ 2 ρ) :=
  allValues (ι := ι) (κ := ι) (H := Vector Q hQ)
    (vectorValue (ι := ι) Q hQ) (fun x => CFC.sqrt (M x)) S

theorem values_apply (z : Natural Q hQ M S hM) (i : ι) :
    values Q hQ M S hM z i = (tuple Q hQ M S hM z i).val := rfl

/-- Matrix pairing is the inner product of the multiplier components, including all
off-diagonal cross terms (Subsection 3.5, Lemma 4.4). -/
theorem integral_pair_eq (z w : Natural Q hQ M S hM) :
    (∫ x, matrixFieldPair M (fun i => (tuple Q hQ M S hM z i).val)
      (fun i => (tuple Q hQ M S hM w i).val) x ∂ρ) =
      inner ℝ (multiplier (vectorValue Q hQ) (fun x => CFC.sqrt (M x)) S z)
        (multiplier (vectorValue Q hQ) (fun x => CFC.sqrt (M x)) S w) := by
  rw [integral_congr_ae (pair_ae Q hQ M S hM z w), PiLp.inner_apply,
    integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [L2.inner_def]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by
      change output i z.val x * output i w.val x = inner ℝ (output i z.val x) (output i w.val x)
      rw [Real.inner_apply, mul_comm])
  · intro i _
    simpa only [Real.inner_apply, mul_comm] using
      L2.integrable_inner (𝕜 := ℝ) (output i z.val) (output i w.val)

/-- The graph pairing is mass plus diffusion plus matrix energy. -/
theorem natural_inner_eq (z w : Natural Q hQ M S hM) :
    inner ℝ z w = inner ℝ (values Q hQ M S hM z) (values Q hQ M S hM w) +
      ((∑ i, Q.2 (tuple Q hQ M S hM z i) (tuple Q hQ M S hM w i)) +
        ∫ x, matrixFieldPair M (fun i => (tuple Q hQ M S hM z i).val)
          (fun i => (tuple Q hQ M S hM w i).val) x ∂ρ) := by
  rw [inner_eq, ← integral_pair_eq Q hQ M S hM, PiLp.inner_apply, PiLp.inner_apply]
  simp only [ScalarFormHilbert.inner_eq, Finset.sum_add_distrib, values_apply]
  rw [add_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The full weak form as a continuous bilinear map in the complete graph norm.
Subtracting mass from the graph inner product leaves diffusion plus matrix energy. -/
def weakForm : Natural Q hQ M S hM →L[ℝ] Natural Q hQ M S hM →L[ℝ] ℝ :=
  let a : Natural Q hQ M S hM →L[ℝ] Natural Q hQ M S hM →L[ℝ] ℝ := innerSL ℝ (E := Natural Q hQ M S hM)
  let b : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ) →L[ℝ] PiLp 2 (fun _ : ι => Lp ℝ 2 ρ) →L[ℝ] ℝ := innerSL ℝ (E := PiLp 2 (fun _ : ι => Lp ℝ 2 ρ))
  a - b.bilinearComp (values Q hQ M S hM) (values Q hQ M S hM)

/-- This continuous bilinear map is exactly the weak pairing. -/
theorem weakForm_apply (z w : Natural Q hQ M S hM) :
    weakForm Q hQ M S hM z w =
      (∑ i, Q.2 (tuple Q hQ M S hM z i) (tuple Q hQ M S hM w i)) +
        ∫ x, matrixFieldPair M (fun i => (tuple Q hQ M S hM z i).val)
          (fun i => (tuple Q hQ M S hM w i).val) x ∂ρ := by
  change inner ℝ z w - inner ℝ (values Q hQ M S hM z) (values Q hQ M S hM w) = _
  rw [natural_inner_eq]
  ring

theorem weakForm_symm (z w : Natural Q hQ M S hM) :
    weakForm Q hQ M S hM z w = weakForm Q hQ M S hM w z := by
  change inner ℝ z w - inner ℝ (values Q hQ M S hM z) (values Q hQ M S hM w) =
    inner ℝ w z - inner ℝ (values Q hQ M S hM w) (values Q hQ M S hM z)
  rw [real_inner_comm z w, real_inner_comm (values Q hQ M S hM z)]

theorem weakForm_nonneg (z : Natural Q hQ M S hM) :
    0 ≤ weakForm Q hQ M S hM z z := by
  rw [weakForm_apply, integral_pair_eq]
  exact add_nonneg (Finset.sum_nonneg (fun i _ => hQ.2.2.1 _)) real_inner_self_nonneg

/-- Every L² source gives a continuous functional on the graph form domain. -/
def sourcePairing (f : ι → Lp ℝ 2 ρ) : Natural Q hQ M S hM →L[ℝ] ℝ :=
  (innerSL ℝ (WithLp.toLp 2 f)).comp (values Q hQ M S hM)

theorem sourcePairing_apply (f : ι → Lp ℝ 2 ρ) (z : Natural Q hQ M S hM) :
    sourcePairing Q hQ M S hM f z = ∑ i, inner ℝ (f i) (tuple Q hQ M S hM z i).val := rfl

/-- Exact bridge to the weak equation, with its entire test domain and explicit
cross-integrability conjunct (Subsection 3.5, Lemma 4.4, Subsection 5.1). -/
theorem weightedWeakSolution_iff (hMmeas : ∀ i j, Measurable (fun x => M x i j))
    (f : ι → Lp ℝ 2 ρ) (z : Natural Q hQ M S hM) :
    WeightedWeakSolution Q M S f (tuple Q hQ M S hM z) ↔
      ∀ w : Natural Q hQ M S hM,
        weakForm Q hQ M S hM z w = sourcePairing Q hQ M S hM f w := by
  constructor
  · intro hz w
    rw [weakForm_apply, sourcePairing_apply]
    exact (hz.2 _ (tuple_mem Q hQ M S hM w)).2
  · intro hz
    refine ⟨tuple_mem Q hQ M S hM z, fun u hu => ?_⟩
    obtain ⟨w, rfl⟩ := exists_tuple Q hQ M S hM hMmeas u hu
    exact ⟨integrable_pair Q hQ M S hM z w,
      (weakForm_apply Q hQ M S hM z w).symm.trans ((hz w).trans (sourcePairing_apply Q hQ M S hM f w))⟩

/-- Form norm identity for the complete natural domain. -/
theorem natural_norm_sq (z : Natural Q hQ M S hM) :
    ‖z‖ ^ 2 = ‖values Q hQ M S hM z‖ ^ 2 + weakForm Q hQ M S hM z z := by
  rw [← real_inner_self_eq_norm_sq, natural_inner_eq, ← weakForm_apply,
    real_inner_self_eq_norm_sq]

/-- The L² embedding is a contraction in the graph norm. -/
theorem norm_values_le (z : Natural Q hQ M S hM) : ‖values Q hQ M S hM z‖ ≤ ‖z‖ := by
  have hn := natural_norm_sq Q hQ M S hM z
  have he := weakForm_nonneg Q hQ M S hM z
  nlinarith [norm_nonneg z, norm_nonneg (values Q hQ M S hM z)]

/-- The mass term uses the Euclidean component metric, independently of the base. -/
theorem mass_self_integral (z : Natural Q hQ M S hM) :
    ‖values Q hQ M S hM z‖ ^ 2 =
      ∫ x, ∑ i, (tuple Q hQ M S hM z i).val x ^ 2 ∂ρ := by
  rw [PiLp.norm_sq_eq_of_L2, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [values_apply, ← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by dsimp only; rw [Real.inner_apply, sq])
  · intro i _
    exact (Lp.memLp (tuple Q hQ M S hM z i).val).integrable_sq

/-- A lower matrix bound on the constrained component space gives the matching integral
bound. Positivity is required only on the actual constrained vectors. -/
theorem matrix_lower_bound (a : ℝ)
    (ha : ∀ᵐ x ∂ρ, ∀ t ∈ S,
      a * (∑ i, t i ^ 2) ≤ ∑ i, ∑ j, t i * M x i j * t j)
    (z : Natural Q hQ M S hM) :
    a * ‖values Q hQ M S hM z‖ ^ 2 ≤
      ∫ x, matrixFieldPair M (fun i => (tuple Q hQ M S hM z i).val)
        (fun i => (tuple Q hQ M S hM z i).val) x ∂ρ := by
  have hi : Integrable (fun x => ∑ i, (tuple Q hQ M S hM z i).val x ^ 2) ρ :=
    integrable_finsetSum _ (fun i _ => (Lp.memLp (tuple Q hQ M S hM z i).val).integrable_sq)
  rw [mass_self_integral, ← integral_const_mul]
  apply integral_mono_ae (hi.const_mul a) (integrable_pair Q hQ M S hM z z)
  filter_upwards [ha, (tuple_mem Q hQ M S hM z).1] with x hx hz
  exact hx _ hz

/-- Coercivity of the full weak form in the complete graph norm. This applies to
arbitrary unbounded measurable matrices, and to their fixed-subspace restrictions. -/
theorem weakForm_coercivity (a : ℝ) (ha : 0 < a)
    (hlower : ∀ᵐ x ∂ρ, ∀ t ∈ S,
      a * (∑ i, t i ^ 2) ≤ ∑ i, ∑ j, t i * M x i j * t j)
    (z : Natural Q hQ M S hM) :
    (a / (1 + a)) * ‖z‖ ^ 2 ≤ weakForm Q hQ M S hM z z := by
  have hl := matrix_lower_bound Q hQ M S hM a hlower z
  have he : 0 ≤ ∑ i, Q.2 (tuple Q hQ M S hM z i) (tuple Q hQ M S hM z i) :=
    Finset.sum_nonneg (fun i _ => hQ.2.2.1 _)
  have hq := weakForm_apply Q hQ M S hM z z
  have hn := natural_norm_sq Q hQ M S hM z
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : 0 < 1 + a)]
  nlinarith

/-- Empty component spaces are handled by the same construction, without any
inhabited-index assumption in graph closedness. -/
theorem natural_eq_zero_of_isEmpty [IsEmpty ι] (z : Natural Q hQ M S hM) : z = 0 := by
  apply tuple_injective Q hQ M S hM
  funext i
  exact isEmptyElim i

/-- Closed component constraints include the fixed zero-sum subspace used by gap equations. -/
theorem tuple_zeroSum (z : Natural Q hQ M (zeroSumComponents ι) hM) :
    ∀ᵐ x ∂ρ, ∑ i, (tuple Q hQ M (zeroSumComponents ι) hM z i).val x = 0 :=
  (tuple_mem Q hQ M (zeroSumComponents ι) hM z).1

end NaturalSpace
end Riesz2.MatrixEnergy

namespace Riesz2.ScalarFormHilbert

variable {α C G : Type*} [MeasurableSpace α] {ρ : Measure α}
  [AddCommGroup C] [Module ℝ C] [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q)
  (J : C →ₗ[ℝ] ScalarForm.Jet ρ G)

/-- Internal realization bridge from the scalar jet completion to the
scalar carrier, once their values and bilinear energies have been identified.
The bridge preserves the complete form metric, not merely the L² metric. -/
def completionEquiv (e : ScalarForm.Domain J ≃ₗ[ℝ] Q.1)
    (hv : ∀ f, (e f).val = ScalarForm.value J f)
    (he : ∀ f g, Q.2 (e f) (e g) = ScalarForm.energy J f g) :
    ScalarForm.Domain J ≃ₗᵢ[ℝ] Space Q hQ where
  toLinearEquiv := e.trans (equiv Q hQ).symm
  norm_map' f := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq]
    change ‖(e f).val‖ ^ 2 + Q.2 (e f) (e f) = ‖f‖ ^ 2
    rw [hv, he]
    exact (ScalarForm.norm_sq J f).symm

theorem completionEquiv_value (e : ScalarForm.Domain J ≃ₗ[ℝ] Q.1)
    (hv : ∀ f, (e f).val = ScalarForm.value J f)
    (he : ∀ f g, Q.2 (e f) (e g) = ScalarForm.energy J f g) (f : ScalarForm.Domain J) :
    value Q hQ (completionEquiv Q hQ J e hv he f) = ScalarForm.value J f := hv f

end Riesz2.ScalarFormHilbert
