/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.DifferentiatedPoissonPart2
public import Riesz2.HelfferSjostrand.VectorCorePart2
public import Riesz1.ToMathlib.Variational.QuadraticMinimum

/-!
# The differentiated equation on the full intrinsic vector domain

The differentiated weak equation on the full natural domain, covariance,
and unique minimization in the proof of Proposition 3.3.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff Laplacian BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace Riesz2.DifferentiatedPoisson

open IntrinsicScalarCore MatrixEnergy

variable {d : ℕ}
variable {U : Set (EuclideanSpace ℝ (Fin d))}
  {ρ : Measure (EuclideanSpace ℝ (Fin d))} {V : EuclideanSpace ℝ (Fin d) → ℝ}
  (hU : IsOpen U) (hB : Bornology.IsBounded U)
  (hV : IsEuclideanGibbsPotential volume ρ U V)

local notation "J" => jet hU hB hV
local notation "VectorJet" => PiLp 2 (fun _ : Fin d => ScalarForm.Domain J)
local notation "Ambient" => MatrixEnergy.Jet (κ := Fin d) (ρ := ρ) (H := VectorJet)
local notation "v" => VectorCore.componentValue (ι := Fin d) hU hB hV
local notation "B" => (fun x => CFC.sqrt (hessianMatrix V x))
local notation "Core" => VectorCore.compactGraph hU hB hV B ⊤
local notation "Completed" => VectorCore.compactCompletion hU hB hV B ⊤

local instance : NormedAddCommGroup (ScalarForm.Domain J) := inferInstance
local instance : NormedAddCommGroup VectorJet := inferInstance
local instance : NormedAddCommGroup Ambient := inferInstance
local instance : InnerProductSpace ℝ (ScalarForm.Domain J) := inferInstance
local instance : InnerProductSpace ℝ VectorJet := PiLp.innerProductSpace _
local instance : NormedSpace ℝ (ScalarForm.Domain J) := inferInstance
local instance : NormedSpace ℝ VectorJet := inferInstance
local instance : NormedSpace ℝ (PiLp 2 (fun _ : Fin d => Lp ℝ 2 ρ)) := inferInstance
local instance : InnerProductSpace ℝ Ambient := inferInstance
local instance : InnerProductSpace ℝ (PiLp 2 (fun _ : Fin d => Lp ℝ 2 ρ)) := PiLp.innerProductSpace _
local instance : NormedSpace ℝ Ambient := inferInstance
local instance : CompleteSpace VectorJet := inferInstance
local instance : CompleteSpace Ambient := inferInstance
local instance : NormedSpace ℝ Core := inferInstance
local instance : NormedSpace ℝ Completed := inferInstance
local instance : InnerProductSpace ℝ Core := inferInstance
local instance : InnerProductSpace ℝ Completed := inferInstance

/-- Continuous representation of the vector form on the existing ambient jets, as used in the proof of Proposition 3.3. On the multiplier graph its value is
the diffusion pairing plus the Hessian cross integral. -/
def mixedPair : Ambient →L[ℝ] Ambient →L[ℝ] ℝ :=
  let a : Ambient →L[ℝ] Ambient →L[ℝ] ℝ := innerSL ℝ (E := Ambient)
  let b : Lp ℝ 2 ρ →L[ℝ] Lp ℝ 2 ρ →L[ℝ] ℝ := innerSL ℝ (E := Lp ℝ 2 ρ)
  a - ∑ i : Fin d, b.bilinearComp (input (κ := Fin d) v i) (input (κ := Fin d) v i)

set_option backward.isDefEq.respectTransparency false in
/-- Ambient mixed pairing in coordinates, as used in the proof of Proposition 3.3. -/
theorem mixedPair_apply (z w : Ambient) :
    mixedPair hU hB hV z w =
      (∑ i, ScalarForm.energy J ((WithLp.ofLp z).1 i) ((WithLp.ofLp w).1 i)) +
      ∑ i, inner ℝ (output i z) (output i w) := by
  simp only [mixedPair, sub_apply, sum_apply, ContinuousLinearMap.bilinearComp_apply]
  change inner ℝ z w - (∑ i : Fin d, inner ℝ (input v i z) (input v i w)) = _
  change ((∑ i : Fin d, inner ℝ ((WithLp.ofLp z).1 i) ((WithLp.ofLp w).1 i)) +
    (∑ i : Fin d, inner ℝ (output i z) (output i w))) -
    (∑ i : Fin d, inner ℝ (input v i z) (input v i w)) = _
  have hi := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ =>
    ScalarForm.inner_eq J ((WithLp.ofLp z).1 i) ((WithLp.ofLp w).1 i))
  rw [Finset.sum_add_distrib] at hi
  rw [hi]
  change ((∑ i, inner ℝ (input v i z) (input v i w)) +
    (∑ i, ScalarForm.energy J ((WithLp.ofLp z).1 i) ((WithLp.ofLp w).1 i))) +
    (∑ i, inner ℝ (output i z) (output i w)) -
    (∑ i, inner ℝ (input v i z) (input v i w)) = _
  ring

/-- Mixed Hessian integrability and its multiplier formula on the whole natural
square-root graph, as used in the proof of Proposition 3.3. -/
theorem graph_mixed_matrix
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef)
    (z w : Ambient) (hz : z ∈ graph v B ⊤) (hw : w ∈ graph v B ⊤) :
    Integrable (matrixFieldPair (hessianMatrix V) (fun i => input v i z)
      (fun i => input v i w)) ρ ∧
    (∫ x, matrixFieldPair (hessianMatrix V) (fun i => input v i z)
      (fun i => input v i w) x ∂ρ) = ∑ i, inner ℝ (output i z) (output i w) := by
  have he : matrixFieldPair (hessianMatrix V) (fun i => input v i z)
      (fun i => input v i w) =ᵐ[ρ] fun x => ∑ i, output i z x * output i w x := by
    filter_upwards [hM, hz, hw] with x hx hy ht
    rw [matrixFieldPair_factor (hessianMatrix V) B (sqrt_factor _ hx)]
    exact Finset.sum_congr rfl (fun i _ => by rw [hy.2 i, ht.2 i])
  have hi (i : Fin d) : Integrable (fun x => output i z x * output i w x) ρ :=
    (Lp.memLp (output i z)).integrable_mul (Lp.memLp (output i w))
  refine ⟨(integrable_finsetSum _ (fun i _ => hi i)).congr he.symm, ?_⟩
  rw [integral_congr_ae he, integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [L2.inner_def]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by dsimp only; rw [Real.inner_apply, mul_comm])

/-- The continuous representation is the full physical mixed form, as used in the proof of Proposition 3.3. -/
theorem mixedPair_graph
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef)
    (z w : Ambient) (hz : z ∈ graph v B ⊤) (hw : w ∈ graph v B ⊤) :
    mixedPair hU hB hV z w =
      (∑ i, ScalarForm.energy J ((WithLp.ofLp z).1 i) ((WithLp.ofLp w).1 i)) +
      ∫ x, matrixFieldPair (hessianMatrix V) (fun i => input v i z)
        (fun i => input v i w) x ∂ρ := by
  rw [mixedPair_apply, (graph_mixed_matrix hU hB hV hM z w hz hw).2]

/-- Coordinate form of the compact commutator with an actual graph output, as used in the proof of Proposition 3.3. -/
theorem compact_coordinate_pair (f h : compactTests U) (i : Fin d)
    (a : Lp ℝ 2 ρ)
    (ha : (ScalarForm.ofCore J f.val, a) ∈ ScalarForm.neumannGraph J)
    (q : Lp ℝ 2 ρ)
    (hq : q =ᵐ[ρ] fun x => fderiv ℝ V x (EuclideanSpace.single i 1) * h.val.val x -
      fderiv ℝ h.val.val x (EuclideanSpace.single i 1)) :
    ScalarForm.energy J (ScalarForm.ofCore J
      (compactDerivative f (EuclideanSpace.single i 1)).val)
      (ScalarForm.ofCore J h.val) +
      (∫ x, h.val.val x * (∑ j, hessianMatrix V x i j * gradient f.val.val x j) ∂ρ) =
      inner ℝ a q := by
  obtain ⟨b, hb, hbae⟩ := compact_mem_graph hU hB hV f
  have hab : a = b := by
    apply (operator hU hB hV).mem_graph_snd_inj
    · rw [operator, ScalarForm.l2Operator_graph, ScalarForm.mem_l2Graph_iff]
      exact ⟨_, rfl, ha⟩
    · rw [operator, ScalarForm.l2Operator_graph, ScalarForm.mem_l2Graph_iff]
      exact ⟨_, rfl, hb⟩
    · rfl
  have he := (compact_mixed_commutator hU hV f h i).2
  have hd : ScalarForm.energy J (ScalarForm.ofCore J
      (compactDerivative f (EuclideanSpace.single i 1)).val)
      (ScalarForm.ofCore J h.val) = ∫ x, inner ℝ
      (gradient (fun y => fderiv ℝ f.val.val y (EuclideanSpace.single i 1)) x)
      (gradient h.val.val x) ∂ρ := by
    rw [ScalarForm.energy_integral]
    apply integral_congr_ae
    filter_upwards [(core_ae hU hB hV
      (compactDerivative f (EuclideanSpace.single i 1)).val).2,
      (core_ae hU hB hV h.val).2] with x hx hy
    rw [hx, hy]
    rfl
  rw [hd, he, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hbae, hq] with x hx hy
  rw [hab, hx, hy, Real.inner_apply]
  rfl

/-- Every compact graph test has compact scalar representatives in each
coordinate, as used in the proof of Proposition 3.3. -/
theorem compactGraph_components (w : Core) :
    ∃ t : Fin d → compactTests U, ∀ i,
      (WithLp.ofLp w.val).1 i = ScalarForm.ofCore J (t i).val := by
  have hw : ∀ i, (WithLp.ofLp w.val).1 i ∈ compactFormDomain hU hB hV := w.property.2
  have ht : ∀ i, ∃ t : compactTests U,
      ScalarForm.ofCore J t.val = (WithLp.ofLp w.val).1 i := by
    intro i
    obtain ⟨t, ht, he⟩ := hw i
    exact ⟨⟨t, ht⟩, he⟩
  choose t ht using ht
  exact ⟨t, fun i => (ht i).symm⟩

/-- Symmetry converts the mixed Hessian integrand into the coordinate
commutator sum, as used in the proof of Proposition 3.3. -/
theorem compact_vector_matrix_ae
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef)
    (f : compactTests U) (w : Core) (t : Fin d → compactTests U)
    (ht : ∀ i, (WithLp.ofLp w.val).1 i = ScalarForm.ofCore J (t i).val) :
    matrixFieldPair (hessianMatrix V)
      (fun i => input v i (compactGradientLift hU hB hV hM f).val)
      (fun i => input v i w.val) =ᵐ[ρ]
      fun x => ∑ i, (t i).val.val x *
        (∑ j, hessianMatrix V x i j * gradient f.val.val x j) := by
  have hg := ae_all_iff.mpr (fun i => compactGradientBase_ae hU hB hV f i)
  have hw := ae_all_iff.mpr (fun i => (core_ae hU hB hV (t i).val).1)
  filter_upwards [hM, hg, hw] with x hx hy hz
  have hv (i : Fin d) : input v i w.val x = (t i).val.val x := by
    change ScalarForm.value J ((WithLp.ofLp w.val).1 i) x = _
    rw [ht i]
    exact hz i
  have hf (i : Fin d) : input v i (compactGradientLift hU hB hV hM f).val x =
      gradient f.val.val x i := by
    change v i (compactGraphBase hU hB hV _ (compactGradientLift hU hB hV hM f)) x = _
    rw [compactGradientLift_base]
    exact hy i
  simp only [matrixFieldPair, hv, hf]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hs : hessianMatrix V x j i = hessianMatrix V x i j := by
    have hh := congrArg (fun M : Matrix (Fin d) (Fin d) ℝ => M i j) hx.1
    simpa only [Matrix.conjTranspose_apply, star_trivial] using hh
  rw [hs]
  ring

/-- The full compact form is the sum of the coordinate commutator forms, as used in the proof of Proposition 3.3. -/
theorem mixedPair_compact_sum
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef)
    (f : compactTests U) (w : Core) (t : Fin d → compactTests U)
    (ht : ∀ i, (WithLp.ofLp w.val).1 i = ScalarForm.ofCore J (t i).val) :
    mixedPair hU hB hV (compactGradientLift hU hB hV hM f).val w.val =
      ∑ i, (ScalarForm.energy J (ScalarForm.ofCore J
        (compactDerivative f (EuclideanSpace.single i 1)).val)
        (ScalarForm.ofCore J (t i).val) +
        ∫ x, (t i).val.val x *
          (∑ j, hessianMatrix V x i j * gradient f.val.val x j) ∂ρ) := by
  have he := compact_vector_matrix_ae hU hB hV hM f w t ht
  have hi (i : Fin d) : Integrable (fun x => (t i).val.val x *
      (∑ j, hessianMatrix V x i j * gradient f.val.val x j)) ρ :=
    (compact_mixed_commutator hU hV f (t i) i).1
  have hd (i : Fin d) : (WithLp.ofLp (compactGradientLift hU hB hV hM f).val).1 i =
      ScalarForm.ofCore J (compactDerivative f (EuclideanSpace.single i 1)).val := by
    exact congrArg (fun u : VectorJet => u i) (compactGradientLift_base hU hB hV hM f)
  rw [mixedPair_graph hU hB hV hM _ _
    (compactGradientLift hU hB hV hM f).property.1 w.property.1]
  rw [integral_congr_ae he]
  rw [integral_finsetSum Finset.univ (fun i _ => hi i), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [hd i, ht i]

set_option backward.isDefEq.respectTransparency false in
/-- Summing the coordinate commutators gives the mixed equation for every
compact vector test, as used in the proof of Proposition 3.3. -/
theorem compact_vector_pair
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef)
    (w : Core) :
    ∃ q : Lp ℝ 2 ρ,
      (∀ (f : compactTests U) (a : Lp ℝ 2 ρ),
        (ScalarForm.ofCore J f.val, a) ∈ ScalarForm.neumannGraph J →
        mixedPair hU hB hV (compactGradientLift hU hB hV hM f).val w.val = inner ℝ a q) ∧
      ∀ F : ScalarForm.Domain J,
        (∑ i, inner ℝ (coordinateLp i (ScalarForm.deriv J F)) (input v i w.val)) =
          inner ℝ (ScalarForm.value J F) q := by
  obtain ⟨t, ht⟩ := compactGraph_components hU hB hV w
  choose q hq hpair using (fun i => compact_adjoint_pairing hU hB hV (t i) i)
  refine ⟨∑ i, q i, ?_, ?_⟩
  · intro f a ha
    rw [mixedPair_compact_sum hU hB hV hM f w t ht, inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact compact_coordinate_pair hU hB hV f (t i) i a ha (q i) (hq i)
  · intro F
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    change inner ℝ (coordinateLp i (ScalarForm.deriv J F))
      (ScalarForm.value J ((WithLp.ofLp w.val).1 i)) = _
    rw [ht i]
    exact hpair i F

/-- The source functional on the existing graph jets, as used in the proof of Proposition 3.3. -/
def gradientPair (G : ScalarForm.Domain J) : Ambient →L[ℝ] ℝ :=
  ∑ i : Fin d, (innerSL ℝ (coordinateLp i (ScalarForm.deriv J G))).comp
    (input (κ := Fin d) v i)

/-- Coordinate evaluation of the source functional, as used in the proof of Proposition 3.3. -/
theorem gradientPair_apply (G : ScalarForm.Domain J) (w : Ambient) :
    gradientPair hU hB hV G w =
      ∑ i, inner ℝ (coordinateLp i (ScalarForm.deriv J G)) (input v i w) := by
  simp only [gradientPair, sum_apply, ContinuousLinearMap.comp_apply]
  rfl

/-- Constants annihilate a compact weighted adjoint, so centering the source
does not change its pairing, as used in the proof of Proposition 3.3. -/
theorem centered_adjoint_pair (G : ScalarForm.Domain J) (w : Ambient) (q : Lp ℝ 2 ρ)
    (hq : ∀ F : ScalarForm.Domain J,
      (∑ i, inner ℝ (coordinateLp i (ScalarForm.deriv J F)) (input v i w)) =
        inner ℝ (ScalarForm.value J F) q) :
    inner ℝ (@Riesz1.poissonCenter _ _ ρ (probability hV) (ScalarForm.value J G)) q =
      gradientPair hU hB hV G w := by
  have := probability hV
  let one := EuclideanScalarForm.constant hU hB (supported hU hV) 1
  have hone : ScalarForm.value J one = Lp.const 2 ρ (1 : ℝ) := by
    apply Lp.ext
    exact (EuclideanScalarForm.value_constant hU hB (supported hU hV) 1).trans
      (Lp.coeFn_const 2 ρ (1 : ℝ)).symm
  have hd : ScalarForm.deriv J one = 0 :=
    EuclideanScalarForm.deriv_constant hU hB (supported hU hV) 1
  have hz : inner ℝ (Lp.const 2 ρ (1 : ℝ)) q = 0 := by
    have hh := hq one
    rw [hone, hd] at hh
    simpa only [map_zero, inner_zero_left, Finset.sum_const_zero] using hh.symm
  rw [Riesz1.poissonCenter, inner_sub_left, real_inner_smul_left, hz, mul_zero, sub_zero]
  rw [gradientPair_apply]
  exact (hq G).symm

/-- Passing compact mixed equations to a scalar graph limit, as used in the proof of Proposition 3.3. Only generator outputs converge on the right. -/
theorem compact_limit_equation
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef)
    (G : ScalarForm.Domain J) (c : ℕ → compactTests U) (b : ℕ → Lp ℝ 2 ρ)
    (hb : ∀ k, (ScalarForm.ofCore J (c k).val, b k) ∈ ScalarForm.neumannGraph J)
    (ha : Tendsto b atTop
      (𝓝 (@Riesz1.poissonCenter _ _ ρ (probability hV) (ScalarForm.value J G))))
    (z : Ambient)
    (hz : Tendsto (fun k => (compactGradientLift hU hB hV hM (c k)).val) atTop (𝓝 z))
    (w : Core) : mixedPair hU hB hV z w.val = gradientPair hU hB hV G w.val := by
  obtain ⟨q, hq, hpair⟩ := compact_vector_pair hU hB hV hM w
  have hl := (((mixedPair hU hB hV).flip w.val).continuous.tendsto z).comp hz
  have hr := ha.inner tendsto_const_nhds (𝕜 := ℝ) (g := fun _ => q)
  have hr' := hr.congr' (Eventually.of_forall (fun k => (hq (c k) (b k) (hb k)).symm))
  exact (tendsto_nhds_unique hl hr').trans
    (centered_adjoint_pair hU hB hV G w.val q hpair)

/-- Continuous closure of the compact test equation, as used in the proof of Proposition 3.3. -/
theorem extend_vector_tests (G : ScalarForm.Domain J) (z : Ambient)
    (hz : ∀ w : Core, mixedPair hU hB hV z w.val = gradientPair hU hB hV G w.val) :
    ∀ w : Completed, mixedPair hU hB hV z w.val = gradientPair hU hB hV G w.val := by
  have hh : closure (Core : Set Ambient) ⊆
      {w | mixedPair hU hB hV z w = gradientPair hU hB hV G w} :=
    closure_minimal (fun w hw => hz ⟨w, hw⟩)
      (isClosed_eq (mixedPair hU hB hV z).continuous (gradientPair hU hB hV G).continuous)
  exact fun w => hh w.property

/-- Completion of graph approximants with their gradient values, as used in the proof of Proposition 3.3. -/
theorem gradient_limit_of_approximants
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef)
    (c : ℕ → compactTests U) (b : ℕ → Lp ℝ 2 ρ) (ψ : ScalarForm.Domain J)
    (hb : ∀ k, (ScalarForm.ofCore J (c k).val, b k) ∈ ScalarForm.neumannGraph J)
    (hg : Tendsto (fun k => ScalarForm.deriv J (ScalarForm.ofCore J (c k).val))
      atTop (𝓝 (ScalarForm.deriv J ψ))) (hbc : CauchySeq b) :
    ∃ z : Completed,
      (∀ i, input v i z.val = coordinateLp i (ScalarForm.deriv J ψ)) ∧
      Tendsto (fun k => (compactGradientLift hU hB hV hM (c k)).val) atTop (𝓝 z.val) := by
  have hc := compactGradientLift_cauchy hU hB hV hM c b hb hg.cauchySeq hbc
  obtain ⟨z, hz⟩ := compactGradientLift_exists_limit hU hB hV hM c hc
  exact ⟨z, compactGradientLift_limit_values hU hB hV hM c ψ z hz hg, hz⟩

/-- Simultaneous value identification and closed weak equation for the vector
limit, as used in the proof of Proposition 3.3. -/
theorem gradient_limit_equation
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef)
    (G ψ : ScalarForm.Domain J) (c : ℕ → compactTests U) (b : ℕ → Lp ℝ 2 ρ)
    (hb : ∀ k, (ScalarForm.ofCore J (c k).val, b k) ∈ ScalarForm.neumannGraph J)
    (ha : Tendsto b atTop
      (𝓝 (@Riesz1.poissonCenter _ _ ρ (probability hV) (ScalarForm.value J G))))
    (hg : Tendsto (fun k => ScalarForm.deriv J (ScalarForm.ofCore J (c k).val))
      atTop (𝓝 (ScalarForm.deriv J ψ))) :
    ∃ z : Completed,
      (∀ i, input v i z.val = coordinateLp i (ScalarForm.deriv J ψ)) ∧
      ∀ w : Completed,
        mixedPair hU hB hV z.val w.val = gradientPair hU hB hV G w.val := by
  obtain ⟨z, hv, hz⟩ := gradient_limit_of_approximants hU hB hV hM c b ψ hb hg ha.cauchySeq
  have ht := compact_limit_equation hU hB hV hM G c b hb ha z.val hz
  exact ⟨z, hv, extend_vector_tests hU hB hV G z.val ht⟩

set_option backward.isDefEq.respectTransparency false in
/-- Internal graph-to-vector equation for the proof of Proposition 3.3, including the exact gradient values. -/
theorem gradient_graph_equation [Nontrivial (EuclideanSpace ℝ (Fin d))]
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef)
    {C : ℝ} (hC : 0 ≤ C)
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹ ^ 2 - C ≤
      ‖gradient V x‖ ^ 2 / 4 - Δ V x / 2)
    (G ψ : ScalarForm.Domain J)
    (hψ : (ψ, @Riesz1.poissonCenter _ _ ρ (probability hV) (ScalarForm.value J G)) ∈
      ScalarForm.neumannGraph J) :
    ∃ z : Completed,
      (∀ i, input v i z.val = coordinateLp i (ScalarForm.deriv J ψ)) ∧
      ∀ w : Completed,
        mixedPair hU hB hV z.val w.val = gradientPair hU hB hV G w.val := by
  obtain ⟨c, b, hb, _, ha, hg⟩ :=
    graph_approximation_with_gradient hU hB hV hC hbar ψ _ hψ
  exact gradient_limit_equation hU hB hV hM G ψ c b hb ha hg

/-- Symmetry of the continuous vector form, as used in the proof of Proposition 3.3. -/
theorem mixedPair_symm (z w : Ambient) :
    mixedPair hU hB hV z w = mixedPair hU hB hV w z := by
  rw [mixedPair_apply, mixedPair_apply]
  congr 1
  · exact Finset.sum_congr rfl (fun i _ => ScalarForm.energy_symm J _ _)
  · exact Finset.sum_congr rfl (fun i _ => real_inner_comm _ _)

/-- Nonnegativity of the represented vector form, as used in the proof of Proposition 3.3. -/
theorem mixedPair_nonneg (z : Ambient) : 0 ≤ mixedPair hU hB hV z z := by
  rw [mixedPair_apply]
  exact add_nonneg (Finset.sum_nonneg (fun i _ => ScalarForm.energy_nonneg J _))
    (Finset.sum_nonneg (fun i _ => real_inner_self_nonneg))

/-- Full mass-plus-form norm identity on the existing jets, as used in the proof of Proposition 3.3. -/
theorem mixedPair_norm_sq (z : Ambient) :
    ‖z‖ ^ 2 = (∑ i, ‖input v i z‖ ^ 2) + mixedPair hU hB hV z z := by
  simp only [mixedPair, sub_apply, sum_apply, ContinuousLinearMap.bilinearComp_apply]
  change ‖z‖ ^ 2 = (∑ i, ‖input v i z‖ ^ 2) +
    (inner ℝ z z - ∑ i, inner ℝ (input v i z) (input v i z))
  simp only [real_inner_self_eq_norm_sq]
  ring

include hU hV in
/-- Strict intrinsic curvature as the coordinate quadratic lower bound for the
Hessian, as used in the proof of Proposition 3.3. -/
theorem hessian_coordinate_lower {κ : ℝ}
    (hH : ∀ x ∈ U, ∀ e, κ * ‖e‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x e e)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ U) (t : Fin d → ℝ) :
    κ * (∑ i, t i ^ 2) ≤ ∑ i, ∑ j, t i * hessianMatrix V x i j * t j := by
  have hh := hH x hx (WithLp.toLp 2 t)
  rw [Intrinsic.hessianMatrix_bilinear (hV.1.contDiffAt (hU.mem_nhds hx))] at hh
  simpa only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs] using hh

/-- Curvature controls the full L² mass by the Hessian integral for every
natural graph field, as used in the proof of Proposition 3.3. -/
theorem graph_matrix_lower
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef) {κ : ℝ}
    (hH : ∀ x ∈ U, ∀ e, κ * ‖e‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x e e)
    (z : Ambient) (hz : z ∈ graph v B ⊤) :
    κ * (∑ i, ‖input v i z‖ ^ 2) ≤
      ∫ x, matrixFieldPair (hessianMatrix V) (fun i => input v i z)
        (fun i => input v i z) x ∂ρ := by
  have hi (i : Fin d) := (Lp.memLp (input v i z)).integrable_sq
  have hm : (∑ i, ‖input v i z‖ ^ 2) = ∫ x, ∑ i, (input v i z x) ^ 2 ∂ρ := by
    rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
    exact Finset.sum_congr rfl (fun i _ => Riesz1.poisson_norm_sq ρ (input v i z))
  rw [hm, ← integral_const_mul]
  apply integral_mono_ae ((integrable_finsetSum _ (fun i _ => hi i)).const_mul κ)
    (graph_mixed_matrix hU hB hV hM z z hz hz).1
  filter_upwards [supported hU hV] with x hx
  exact hessian_coordinate_lower hU hV hH x hx (fun i => input v i z x)

/-- Coercivity in the entire vector graph norm, as used in the proof of Proposition 3.3. -/
theorem mixedPair_coercive
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef) {κ : ℝ} (hκ : 0 < κ)
    (hH : ∀ x ∈ U, ∀ e, κ * ‖e‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x e e)
    (z : Ambient) (hz : z ∈ graph v B ⊤) :
    (κ / (1 + κ)) * ‖z‖ ^ 2 ≤ mixedPair hU hB hV z z := by
  have hl := graph_matrix_lower hU hB hV hM hH z hz
  have hd : 0 ≤ ∑ i, ScalarForm.energy J ((WithLp.ofLp z).1 i) ((WithLp.ofLp z).1 i) :=
    Finset.sum_nonneg (fun i _ => ScalarForm.energy_nonneg J _)
  have he := mixedPair_graph hU hB hV hM z z hz hz
  have hn := mixedPair_norm_sq hU hB hV z
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : 0 < 1 + κ)]
  nlinarith

/-- Quadratic expansion at a vector weak solution, as used in the proof of Proposition 3.3. -/
theorem vector_energy_identity (G : ScalarForm.Domain J) (z : Completed)
    (hz : ∀ w : Completed,
      mixedPair hU hB hV z.val w.val = gradientPair hU hB hV G w.val)
    (w : Completed) :
    mixedPair hU hB hV w.val w.val - 2 * gradientPair hU hB hV G w.val =
      (mixedPair hU hB hV z.val z.val - 2 * gradientPair hU hB hV G z.val) +
      mixedPair hU hB hV (w - z).val (w - z).val := by
  have he := Riesz1.Internal.quadratic_pairing_identity (mixedPair hU hB hV)
    z.val w.val (gradientPair hU hB hV G z.val) (gradientPair hU hB hV G w.val)
    (hz z) (hz w) (mixedPair_symm hU hB hV w.val z.val)
  have hu := hz z
  change _ = _ + mixedPair hU hB hV (w.val - z.val) (w.val - z.val)
  linarith only [he, hu]

/-- Strict positivity of the full vector form on its graph, as used in the proof of Proposition 3.3. -/
theorem mixedPair_eq_zero
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef) {κ : ℝ} (hκ : 0 < κ)
    (hH : ∀ x ∈ U, ∀ e, κ * ‖e‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x e e)
    (z : Ambient) (hz : z ∈ graph v B ⊤)
    (he : mixedPair hU hB hV z z = 0) : z = 0 := by
  have hl := mixedPair_coercive hU hB hV hM hκ hH z hz
  have hp : 0 < κ / (1 + κ) := div_pos hκ (by linarith)
  have hs : ‖z‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖z‖]
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg z])

/-- The vector weak solution is the unique minimizer in the complete domain, as used in the proof of Proposition 3.3. -/
theorem vector_unique_minimum
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef) {κ : ℝ} (hκ : 0 < κ)
    (hH : ∀ x ∈ U, ∀ e, κ * ‖e‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x e e)
    (G : ScalarForm.Domain J) (z : Completed)
    (hz : ∀ w : Completed,
      mixedPair hU hB hV z.val w.val = gradientPair hU hB hV G w.val)
    (w : Completed) :
    mixedPair hU hB hV z.val z.val - 2 * gradientPair hU hB hV G z.val ≤
      mixedPair hU hB hV w.val w.val - 2 * gradientPair hU hB hV G w.val ∧
    (mixedPair hU hB hV w.val w.val - 2 * gradientPair hU hB hV G w.val =
      mixedPair hU hB hV z.val z.val - 2 * gradientPair hU hB hV G z.val → w = z) := by
  have he := vector_energy_identity hU hB hV G z hz w
  have hn := mixedPair_nonneg hU hB hV (w - z).val
  refine ⟨by linarith, fun hh => ?_⟩
  have hg := VectorCore.compactCompletion_le_graph hU hB hV B ⊤ (w - z).property
  have hzero : mixedPair hU hB hV (w - z).val (w - z).val = 0 := by linarith
  have hv := mixedPair_eq_zero hU hB hV hM hκ hH (w - z).val hg hzero
  exact sub_eq_zero.mp (Subtype.ext hv)

/-- The original scalar value equivalence applied coordinatewise to an existing
vector jet. This is a bridge to the carrier, as used in the proof of Proposition 3.3. -/
def graphTuple (z : Ambient) : Fin d → (form hU hB hV).1 := fun i =>
  ScalarForm.valueEquiv J (value_injective hU hB hV) ((WithLp.ofLp z).1 i)

/-- Exact values of the graph tuple, as used in the proof of Proposition 3.3. -/
theorem graphTuple_value (z : Ambient) (i : Fin d) :
    (graphTuple hU hB hV z i).val = input v i z := rfl

/-- The energy is the original scalar diffusion energy, as used in the proof of Proposition 3.3. -/
theorem graphTuple_energy (z w : Ambient) (i : Fin d) :
    (form hU hB hV).2 (graphTuple hU hB hV z i) (graphTuple hU hB hV w i) =
      ScalarForm.energy J ((WithLp.ofLp z).1 i) ((WithLp.ofLp w).1 i) :=
  ScalarForm.realization_energy J (value_injective hU hB hV) _ _

/-- Every completed graph field belongs to the full finite-energy domain, as used in the proof of Proposition 3.3. -/
theorem graphTuple_mem
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef) (z : Completed) :
    WeightedFormDomain (form hU hB hV) (hessianMatrix V) ⊤ (graphTuple hU hB hV z.val) := by
  have hg := VectorCore.compactCompletion_le_graph hU hB hV B ⊤ z.property
  exact ⟨Eventually.of_forall fun _ => Submodule.mem_top,
    (graph_mixed_matrix hU hB hV hM z.val z.val hg hg).1⟩

/-- The entire natural domain is represented by the original compact
completion, as used in the proof of Proposition 3.3. -/
theorem exists_graphTuple [Nontrivial (EuclideanSpace ℝ (Fin d))]
    {C : ℝ} (hC : 0 ≤ C)
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹ ^ 2 - C ≤
      ‖gradient V x‖ ^ 2 / 4 - Δ V x / 2)
    (hM : ∀ x ∈ U, (hessianMatrix V x).PosSemidef)
    (u : Fin d → (form hU hB hV).1)
    (hu : WeightedFormDomain (form hU hB hV) (hessianMatrix V) ⊤ u) :
    ∃ z : Completed, graphTuple hU hB hV z.val = u := by
  obtain ⟨z, hz⟩ := (VectorCore.finite_energy_iff_compactCompletion hU hB hV hC hbar
    (hessianMatrix V) (VectorCore.continuousOn_hessianMatrix hU hV.1) hM u).mp hu
  refine ⟨z, funext fun i => Subtype.ext (hz i)⟩

/-- Mixed-form identity, as used in the proof of Proposition 3.3. -/
theorem mixedPair_frozen
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef) (z w : Completed) :
    mixedPair hU hB hV z.val w.val =
      (∑ i, (form hU hB hV).2 (graphTuple hU hB hV z.val i) (graphTuple hU hB hV w.val i)) +
      ∫ x, matrixFieldPair (hessianMatrix V)
        (fun i => (graphTuple hU hB hV z.val i).val)
        (fun i => (graphTuple hU hB hV w.val i).val) x ∂ρ := by
  simp only [graphTuple_energy, graphTuple_value]
  exact mixedPair_graph hU hB hV hM z.val w.val
    (VectorCore.compactCompletion_le_graph hU hB hV B ⊤ z.property)
    (VectorCore.compactCompletion_le_graph hU hB hV B ⊤ w.property)

/-- The completed equation tests against the entire natural
domain, with cross-integrability, as used in the proof of Proposition 3.3. -/
theorem frozen_gradient_equation [Nontrivial (EuclideanSpace ℝ (Fin d))]
    {C : ℝ} (hC : 0 ≤ C)
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹ ^ 2 - C ≤
      ‖gradient V x‖ ^ 2 / 4 - Δ V x / 2)
    (hM : ∀ x ∈ U, (hessianMatrix V x).PosSemidef)
    (G : ScalarForm.Domain J) (z : Completed)
    (hz : ∀ w : Completed,
      mixedPair hU hB hV z.val w.val = gradientPair hU hB hV G w.val) :
    WeightedWeakSolution (form hU hB hV) (hessianMatrix V) ⊤
      (fun i => coordinateLp i (ScalarForm.deriv J G)) (graphTuple hU hB hV z.val) := by
  have hm : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef :=
    (supported hU hV).mono fun x hx => hM x hx
  refine ⟨graphTuple_mem hU hB hV hm z, fun u hu => ?_⟩
  obtain ⟨w, rfl⟩ := exists_graphTuple hU hB hV hC hbar hM u hu
  refine ⟨(graph_mixed_matrix hU hB hV hm z.val w.val
    (VectorCore.compactCompletion_le_graph hU hB hV B ⊤ z.property)
    (VectorCore.compactCompletion_le_graph hU hB hV B ⊤ w.property)).1, ?_⟩
  exact (mixedPair_frozen hU hB hV hm z w).symm.trans
    ((hz w).trans (gradientPair_apply hU hB hV G w.val))

/-- The variational functional equals its continuous graph
representation, as used in the proof of Proposition 3.3. -/
theorem frozen_functional_eq
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef)
    (G : ScalarForm.Domain J) (w : Completed) :
    (∑ i, (form hU hB hV).2 (graphTuple hU hB hV w.val i) (graphTuple hU hB hV w.val i)) +
      (∫ x, matrixFieldPair (hessianMatrix V)
        (fun i => (graphTuple hU hB hV w.val i).val)
        (fun i => (graphTuple hU hB hV w.val i).val) x ∂ρ) -
      2 * (∑ i, inner ℝ (coordinateLp i (ScalarForm.deriv J G))
        (graphTuple hU hB hV w.val i).val) =
      mixedPair hU hB hV w.val w.val - 2 * gradientPair hU hB hV G w.val := by
  exact congrArg₂ (fun a b : ℝ => a - 2 * b)
    (mixedPair_frozen hU hB hV hM w w).symm (gradientPair_apply hU hB hV G w.val).symm

/-- Unique minimization over every field in the natural domain, as used in the proof of Proposition 3.3. -/
theorem frozen_unique_minimum [Nontrivial (EuclideanSpace ℝ (Fin d))]
    {C : ℝ} (hC : 0 ≤ C)
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹ ^ 2 - C ≤
      ‖gradient V x‖ ^ 2 / 4 - Δ V x / 2)
    (hM : ∀ x ∈ U, (hessianMatrix V x).PosSemidef) {κ : ℝ} (hκ : 0 < κ)
    (hH : ∀ x ∈ U, ∀ e, κ * ‖e‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x e e)
    (G : ScalarForm.Domain J) (z : Completed)
    (hz : ∀ w : Completed,
      mixedPair hU hB hV z.val w.val = gradientPair hU hB hV G w.val)
    (u : Fin d → (form hU hB hV).1)
    (hu : WeightedFormDomain (form hU hB hV) (hessianMatrix V) ⊤ u) :
    let vG := fun i => coordinateLp i (ScalarForm.deriv J G)
    let uz := graphTuple hU hB hV z.val
    let Ju := (∑ i, (form hU hB hV).2 (u i) (u i)) +
      (∫ x, matrixFieldPair (hessianMatrix V) (fun i => (u i).val) (fun i => (u i).val) x ∂ρ) -
        2 * (∑ i, inner ℝ (vG i) (u i).val)
    let Jz := (∑ i, (form hU hB hV).2 (uz i) (uz i)) +
      (∫ x, matrixFieldPair (hessianMatrix V) (fun i => (uz i).val) (fun i => (uz i).val) x ∂ρ) -
        2 * (∑ i, inner ℝ (vG i) (uz i).val)
    Jz ≤ Ju ∧ (Ju = Jz → u = uz) := by
  have hm : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef :=
    (supported hU hV).mono fun x hx => hM x hx
  obtain ⟨w, rfl⟩ := exists_graphTuple hU hB hV hC hbar hM u hu
  have hh := vector_unique_minimum hU hB hV hm hκ hH G z hz w
  have hfw := frozen_functional_eq hU hB hV hm G w
  have hfz := frozen_functional_eq hU hB hV hm G z
  dsimp only
  refine ⟨by linarith only [hh.1, hfw, hfz], fun he => ?_⟩
  have heq : mixedPair hU hB hV w.val w.val - 2 * gradientPair hU hB hV G w.val =
      mixedPair hU hB hV z.val z.val - 2 * gradientPair hU hB hV G z.val := by
    linarith only [he, hfw, hfz]
  exact congrArg (fun t : Completed => graphTuple hU hB hV t.val) (hh.2 heq)

include hU hV in
/-- Pointwise nonnegative intrinsic curvature gives the Hessian
positivity needed by the natural-domain bridge, as used in the proof of Proposition 3.3. -/
theorem hessian_posSemidef_on
    (hH : ∀ x ∈ U, ∀ e, 0 ≤ fderiv ℝ (fderiv ℝ V) x e e) :
    ∀ x ∈ U, (hessianMatrix V x).PosSemidef := by
  intro x hx
  have hs := hV.1.contDiffAt (hU.mem_nhds hx)
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial,
      Intrinsic.hessianMatrix_eq_second hs]
    exact hs.isSymmSndFDerivAt (by simp) _ _
  · intro t
    have hh := hH x hx (WithLp.toLp 2 t)
    rw [Intrinsic.hessianMatrix_bilinear hs] at hh
    simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
      Finset.mul_sum, mul_assoc] using hh

/-- See the proof of Proposition 3.3 in the paper, in orthonormal intrinsic
coordinates: the centered scalar solution has its gradient in the entire vector energy domain, solves the differentiated weak equation for every vector
test, represents every covariance, and uniquely minimizes the full functional.
The result holds on every bounded open convex domain with the stated barrier,
including convex polytopes of positive dimension. -/
theorem exists_differentiated_poisson (hd : 1 ≤ d)
    (hc : Convex ℝ U) {κ : ℝ} (hκ : 0 < κ)
    (hH : ∀ x ∈ U, ∀ e, κ * ‖e‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x e e)
    {C : ℝ} (hC : 0 ≤ C)
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹ ^ 2 - C ≤
      ‖gradient V x‖ ^ 2 / 4 - Δ V x / 2)
    (G : ScalarForm.Domain J) :
    ∃ ψ : ScalarForm.Domain J, ∃ u : Fin d → (form hU hB hV).1,
      (∫ x, ScalarForm.value J ψ x ∂ρ) = 0 ∧
      (ψ, @Riesz1.poissonCenter _ _ ρ (probability hV) (ScalarForm.value J G)) ∈
        ScalarForm.neumannGraph J ∧
      WeightedWeakSolution (form hU hB hV) (hessianMatrix V) ⊤
        (fun i => coordinateLp i (ScalarForm.deriv J G)) u ∧
      (∀ i, (u i).val = coordinateLp i (ScalarForm.deriv J ψ)) ∧
      (∀ K : ScalarForm.Domain J,
        Integrable (fun x => inner ℝ (ScalarForm.deriv J ψ x) (ScalarForm.deriv J K x)) ρ ∧
        ProbabilityTheory.covariance (ScalarForm.value J G) (ScalarForm.value J K) ρ =
          ∫ x, inner ℝ (ScalarForm.deriv J ψ x) (ScalarForm.deriv J K x) ∂ρ) ∧
      ∀ w : Fin d → (form hU hB hV).1,
        WeightedFormDomain (form hU hB hV) (hessianMatrix V) ⊤ w →
        let vG := fun i => coordinateLp i (ScalarForm.deriv J G)
        let Ju := (∑ i, (form hU hB hV).2 (u i) (u i)) +
          (∫ x, matrixFieldPair (hessianMatrix V) (fun i => (u i).val) (fun i => (u i).val) x ∂ρ) -
            2 * (∑ i, inner ℝ (vG i) (u i).val)
        let Jw := (∑ i, (form hU hB hV).2 (w i) (w i)) +
          (∫ x, matrixFieldPair (hessianMatrix V) (fun i => (w i).val) (fun i => (w i).val) x ∂ρ) -
            2 * (∑ i, inner ℝ (vG i) (w i).val)
        Ju ≤ Jw ∧ (Jw = Ju → w = u) := by
  have : NeZero d := ⟨by omega⟩
  have hm := hessian_posSemidef_on hU hV (fun x hx e =>
    (mul_nonneg hκ.le (sq_nonneg ‖e‖)).trans (hH x hx e))
  have hma : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef :=
    (supported hU hV).mono fun x hx => hm x hx
  obtain ⟨ψ, hmean, hψ, hcov⟩ := exists_poisson_covariance hU hB hc hV hκ hH (ScalarForm.value J G)
  obtain ⟨z, hv, hz⟩ := gradient_graph_equation hU hB hV hma hC hbar G ψ hψ
  refine ⟨ψ, graphTuple hU hB hV z.val, hmean, hψ,
    frozen_gradient_equation hU hB hV hC hbar hm G z hz, hv, hcov, ?_⟩
  exact frozen_unique_minimum hU hB hV hC hbar hm hκ hH G z hz

end Riesz2.DifferentiatedPoisson
