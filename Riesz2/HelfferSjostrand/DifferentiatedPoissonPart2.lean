/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.DifferentiatedPoisson
public import Riesz2.HelfferSjostrand.VectorCore

/-!
# The gradient in the intrinsic vector completion

Steps in the proof of Proposition 3.3. The weak gradient belongs to the
compact vector completion and the natural finite-energy domain. The compact
mixed commutator and scalar weighted adjoint pairing are also proved.
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
local notation "v" => VectorCore.componentValue (ι := Fin d) hU hB hV

local instance : InnerProductSpace ℝ (ScalarForm.Domain J) := inferInstance
local instance : InnerProductSpace ℝ VectorJet := PiLp.innerProductSpace _
local instance : NormedSpace ℝ (ScalarForm.Domain J) := inferInstance
local instance : NormedSpace ℝ VectorJet := inferInstance
local instance : NormedSpace ℝ (PiLp 2 (fun _ : Fin d => Lp ℝ 2 ρ)) := inferInstance
local instance : NormedSpace ℝ
    (MatrixEnergy.Jet (κ := Fin d) (ρ := ρ) (H := VectorJet)) := inferInstance
local instance : CompleteSpace VectorJet := inferInstance
local instance : CompleteSpace
    (MatrixEnergy.Jet (κ := Fin d) (ρ := ρ) (H := VectorJet)) := inferInstance

/-- Coordinate extraction on vector-valued L², used in the proof of Proposition 3.3. -/
def coordinateLp (i : Fin d) : Lp (EuclideanSpace ℝ (Fin d)) 2 ρ →L[ℝ] Lp ℝ 2 ρ :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).compLpL 2 ρ

omit hU hB hV in
/-- The L² coordinate map has the actual pointwise coordinates, as used in the proof of Proposition 3.3. -/
theorem coordinateLp_ae (i : Fin d) (g : Lp (EuclideanSpace ℝ (Fin d)) 2 ρ) :
    coordinateLp (ρ := ρ) i g =ᵐ[ρ] fun x => g x i :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).coeFn_compLpL g

/-- Compact directional differentiation is linear, as used in the proof of Proposition 3.3. -/
def compactDerivativeLinear (e : EuclideanSpace ℝ (Fin d)) : compactTests U →ₗ[ℝ] compactTests U where
  toFun f := compactDerivative f e
  map_add' f g := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact congrArg (fun L : (EuclideanSpace ℝ (Fin d)) →L[ℝ] ℝ => L e)
      (fderiv_add (f.property.1.differentiable (by simp) x)
        (g.property.1.differentiable (by simp) x))
  map_smul' a f := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact congrArg (fun L : (EuclideanSpace ℝ (Fin d)) →L[ℝ] ℝ => L e)
      (fderiv_const_smul (f.property.1.differentiable (by simp) x) a)

/-- The compact gradient as a tuple in the existing scalar jet completion, as used in the proof of Proposition 3.3. -/
def compactGradientBase : compactTests U →ₗ[ℝ] VectorJet :=
  (WithLp.linearEquiv 2 ℝ _).symm.toLinearMap.comp
    (LinearMap.pi (fun i => (ScalarForm.ofCore J).comp
      ((compactTests U).subtype.comp
        (compactDerivativeLinear (EuclideanSpace.single i 1)))))

/-- Values of the compact gradient are the coordinates of the actual weak
gradient, as used in the proof of Proposition 3.3. -/
theorem compactGradientBase_value (f : compactTests U) (i : Fin d) :
    v i (compactGradientBase hU hB hV f) =
      coordinateLp (ρ := ρ) i (ScalarForm.deriv J (ScalarForm.ofCore J f.val)) := by
  have := probability hV
  apply Lp.ext
  have hf := (Riesz1.WeightedSobolev.memLp_of_smoothNearClosure hB
    (supported hU hV) f.val.property).2.coeFn_toLp
  have hi := (Riesz1.WeightedSobolev.memLp_of_smoothNearClosure hB
    (supported hU hV) (compactDerivative f (EuclideanSpace.single i 1)).val.property).1.coeFn_toLp
  filter_upwards [hf, hi, coordinateLp_ae i
    (ScalarForm.deriv J (ScalarForm.ofCore J f.val))] with x hx hy hz
  change ScalarForm.deriv J (ScalarForm.ofCore J f.val) x = gradient f.val.val x at hx
  change v i (compactGradientBase hU hB hV f) x =
    fderiv ℝ f.val.val x (EuclideanSpace.single i 1) at hy
  rw [hy, hz, hx, ← inner_gradient_left, EuclideanSpace.inner_single_right]
  simp only [one_mul, conj_trivial]

/-- The Hessian has measurable entries even when the ambient extension
of the potential is unrestricted, as used in the proof of Proposition 3.3. -/
theorem measurable_hessian_entries (i j : Fin d) :
    Measurable (fun x => hessianMatrix V x i j) :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).continuous.measurable.comp
    (measurable_fderiv_apply_const ℝ (gradient V) (EuclideanSpace.single j 1))

include hU hV in
/-- Nonnegative curvature on the actual Gibbs support gives positivity of the
Hessian, as used in the proof of Proposition 3.3. -/
theorem hessian_posSemidef
    (hH : ∀ x ∈ U, ∀ e, 0 ≤ fderiv ℝ (fderiv ℝ V) x e e) :
    ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef := by
  filter_upwards [supported hU hV] with x hx
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

/-- Pointwise values of the compact gradient, as used in the proof of Proposition 3.3. -/
theorem compactGradientBase_ae (f : compactTests U) (i : Fin d) :
    v i (compactGradientBase hU hB hV f) =ᵐ[ρ]
      fun x => gradient f.val.val x i := by
  have := probability hV
  rw [compactGradientBase_value]
  have hf := (Riesz1.WeightedSobolev.memLp_of_smoothNearClosure hB
    (supported hU hV) f.val.property).2.coeFn_toLp
  filter_upwards [coordinateLp_ae i (ScalarForm.deriv J (ScalarForm.ofCore J f.val)), hf]
    with x hx hy
  exact hx.trans (congrArg (fun e : EuclideanSpace ℝ (Fin d) => e i) hy)

/-- Internal lift of a compact gradient to the square-root graph in
the proof of Proposition 3.3. The base determines the lift uniquely. -/
theorem exists_compactGradientGraph
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef) (f : compactTests U) :
    ∃ z : VectorCore.compactGraph hU hB hV
        (fun x => CFC.sqrt (hessianMatrix V x)) ⊤,
      (WithLp.ofLp z.val).1 = compactGradientBase hU hB hV f := by
  obtain ⟨u, hu, hue⟩ := compact_gradient_finite_energy hU hB hV f
  have hv (i : Fin d) : (u i).val = v i (compactGradientBase hU hB hV f) :=
    Lp.ext ((hue i).trans (compactGradientBase_ae hU hB hV f i).symm)
  let B := fun x => CFC.sqrt (hessianMatrix V x)
  have hL := (integrable_iff_memLp_factor (hessianMatrix V) B
    (fun i j => (measurable_sqrt_entries (hessianMatrix V)
      measurable_hessian_entries i j).aestronglyMeasurable)
    (hM.mono (fun x hx => sqrt_factor _ hx)) (fun i => (u i).val)).mp hu.2
  let e : PiLp 2 (fun _ : Fin d => Lp ℝ 2 ρ) := WithLp.toLp 2
    (fun i => (hL i).toLp (fun x => ∑ j, B x i j * (u j).val x))
  let z : MatrixEnergy.Jet (κ := Fin d) (ρ := ρ) (H := VectorJet) :=
    WithLp.toLp 2 (compactGradientBase hU hB hV f, e)
  have hz : z ∈ VectorCore.compactGraph hU hB hV B ⊤ := by
    constructor
    · have he := ae_all_iff.mpr (fun i => (hL i).coeFn_toLp)
      filter_upwards [he] with x hx
      refine ⟨Submodule.mem_top, fun i => ?_⟩
      change e i x = ∑ j, B x i j * v j (compactGradientBase hU hB hV f) x
      change (hL i).toLp (fun y => ∑ j, B y i j * (u j).val y) x = _
      exact (hx i).trans (Finset.sum_congr rfl (fun j _ =>
        congrArg (fun t : Lp ℝ 2 ρ => B x i j * t x) (hv j)))
    · intro i
      exact ⟨(compactDerivative f (EuclideanSpace.single i 1)).val,
        (compactDerivative f (EuclideanSpace.single i 1)).property, rfl⟩
  exact ⟨⟨z, hz⟩, rfl⟩

/-- The base projection of the existing compact vector graph, as used in the proof of Proposition 3.3. -/
def compactGraphBase (B : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) :
    VectorCore.compactGraph hU hB hV B ⊤ →ₗ[ℝ] VectorJet :=
  (WithLp.fstL 2 ℝ _ _).toLinearMap.comp
    (VectorCore.compactGraph hU hB hV B ⊤).subtype

/-- Uniqueness of the multiplier lift, as used in the proof of Proposition 3.3. -/
theorem compactGraphBase_injective
    (B : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ) :
    Function.Injective (compactGraphBase hU hB hV B) := by
  intro z w he
  have hh := MatrixEnergy.base_injective v B ⊤
    (a₁ := ⟨z.val, z.property.1⟩) (a₂ := ⟨w.val, w.property.1⟩) he
  apply Subtype.ext
  exact congrArg (fun y : MatrixEnergy.Space v B ⊤ => y.val) hh

/-- The unique point of the compact square-root graph with the prescribed
compact gradient base, as used in the proof of Proposition 3.3. -/
def compactGradientPoint (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef)
    (f : compactTests U) : VectorCore.compactGraph hU hB hV
      (fun x => CFC.sqrt (hessianMatrix V x)) ⊤ :=
  (exists_compactGradientGraph hU hB hV hM f).choose

/-- Base identification for the proof of Proposition 3.3. -/
theorem compactGradientPoint_base
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef) (f : compactTests U) :
    compactGraphBase hU hB hV _ (compactGradientPoint hU hB hV hM f) =
      compactGradientBase hU hB hV f :=
  (exists_compactGradientGraph hU hB hV hM f).choose_spec

/-- Additivity of the uniquely specified compact lift, as used in the proof of Proposition 3.3. -/
theorem compactGradientPoint_add
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef) (f g : compactTests U) :
    compactGradientPoint hU hB hV hM (f + g) =
      compactGradientPoint hU hB hV hM f + compactGradientPoint hU hB hV hM g := by
  apply compactGraphBase_injective hU hB hV (fun x => CFC.sqrt (hessianMatrix V x))
  exact (compactGradientPoint_base hU hB hV hM (f + g)).trans
    (((compactGradientBase hU hB hV).map_add f g).trans
      ((congrArg₂ (· + ·) (compactGradientPoint_base hU hB hV hM f)
        (compactGradientPoint_base hU hB hV hM g)).symm.trans
          ((compactGraphBase hU hB hV _).map_add _ _).symm))

/-- Homogeneity of the uniquely specified compact lift, as used in the proof of Proposition 3.3. -/
theorem compactGradientPoint_smul
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef) (a : ℝ) (f : compactTests U) :
    compactGradientPoint hU hB hV hM (a • f) =
      a • compactGradientPoint hU hB hV hM f := by
  apply compactGraphBase_injective hU hB hV (fun x => CFC.sqrt (hessianMatrix V x))
  rw [(compactGraphBase hU hB hV _).map_smul a (compactGradientPoint hU hB hV hM f)]
  rw [compactGradientPoint_base, compactGradientPoint_base]
  exact (compactGradientBase hU hB hV).map_smul a f

/-- The compact gradient as a linear map into the existing matrix graph, as used in the proof of Proposition 3.3. -/
def compactGradientLift (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef) :
    compactTests U →ₗ[ℝ] VectorCore.compactGraph hU hB hV
      (fun x => CFC.sqrt (hessianMatrix V x)) ⊤ where
  toFun := compactGradientPoint hU hB hV hM
  map_add' := compactGradientPoint_add hU hB hV hM
  map_smul' := compactGradientPoint_smul hU hB hV hM

/-- Base of the compact lift, as used in the proof of Proposition 3.3. -/
theorem compactGradientLift_base
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef) (f : compactTests U) :
    compactGraphBase hU hB hV _ (compactGradientLift hU hB hV hM f) =
      compactGradientBase hU hB hV f :=
  (exists_compactGradientGraph hU hB hV hM f).choose_spec

omit hU hB hV in
/-- Coordinate extraction preserves the full Euclidean L² mass, as used in the proof of Proposition 3.3. -/
theorem sum_coordinateLp_norm_sq (g : Lp (EuclideanSpace ℝ (Fin d)) 2 ρ) :
    ∑ i, ‖coordinateLp (ρ := ρ) i g‖ ^ 2 = ‖g‖ ^ 2 := by
  simp_rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  rw [← integral_finsetSum]
  · apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr (fun i => coordinateLp_ae i g)] with x hx
    simp only [hx, PiLp.inner_apply]
  · intro i _
    exact L2.integrable_inner _ _

/-- Integral of the Hessian pairing in the compact graph is the exact
multiplier mass, as used in the proof of Proposition 3.3. -/
theorem compactGraph_matrix_integral
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef)
    (z : VectorCore.compactGraph hU hB hV
      (fun x => CFC.sqrt (hessianMatrix V x)) ⊤) :
    (∫ x, matrixFieldPair (hessianMatrix V) (fun i => input v i z.val)
      (fun i => input v i z.val) x ∂ρ) = ∑ i, ‖output i z.val‖ ^ 2 := by
  have he : matrixFieldPair (hessianMatrix V) (fun i => input v i z.val)
      (fun i => input v i z.val) =ᵐ[ρ] fun x => ∑ i, (output i z.val x) ^ 2 := by
    filter_upwards [hM, z.property.1] with x hx hz
    rw [matrixFieldPair_factor (hessianMatrix V) (fun y => CFC.sqrt (hessianMatrix V y))
      (sqrt_factor _ hx)]
    simp only [← hz.2, sq]
  rw [integral_congr_ae he, integral_finsetSum]
  · exact Finset.sum_congr rfl (fun i _ => (Riesz1.poisson_norm_sq ρ (output i z.val)).symm)
  · intro i _
    exact (Lp.memLp (output i z.val)).integrable_sq

/-- Full norm of a compact graph element: mass, diffusion, and Hessian energy, as used in the proof of Proposition 3.3. -/
theorem compactGraph_norm_sq
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef)
    (z : VectorCore.compactGraph hU hB hV
      (fun x => CFC.sqrt (hessianMatrix V x)) ⊤) :
    ‖z‖ ^ 2 = (∑ i, ‖input v i z.val‖ ^ 2) +
      (∑ i, ScalarForm.energy J ((WithLp.ofLp z.val).1 i)
        ((WithLp.ofLp z.val).1 i)) +
      ∫ x, matrixFieldPair (hessianMatrix V) (fun i => input v i z.val)
        (fun i => input v i z.val) x ∂ρ := by
  rw [compactGraph_matrix_integral hU hB hV hM]
  have hn : ‖z‖ ^ 2 = ‖(WithLp.ofLp z.val).1‖ ^ 2 +
      ‖(WithLp.ofLp z.val).2‖ ^ 2 := WithLp.prod_norm_sq_eq_of_L2 z.val
  have hn₁ := PiLp.norm_sq_eq_of_L2
    (fun _ : Fin d => ScalarForm.Domain J) (WithLp.ofLp z.val).1
  have hn₂ := PiLp.norm_sq_eq_of_L2
    (fun _ : Fin d => Lp ℝ 2 ρ) (WithLp.ofLp z.val).2
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ =>
    ScalarForm.norm_sq J ((WithLp.ofLp z.val).1 i))
  rw [Finset.sum_add_distrib] at hs
  exact hn.trans (congrArg₂ (· + ·) (hn₁.trans hs) hn₂)

/-- The compact Bochner identity in the coordinate basis of the Hessian, as used in the proof of Proposition 3.3. -/
theorem compact_gradient_energy_coordinates (f : compactTests U) (a : Lp ℝ 2 ρ)
    (ha : (ScalarForm.ofCore J f.val, a) ∈ ScalarForm.neumannGraph J) :
    let e := fun x => (∑ i : Fin d, ‖gradient
      (fun y => fderiv ℝ f.val.val y (EuclideanSpace.single i 1)) x‖ ^ 2) +
      fderiv ℝ (fderiv ℝ V) x (gradient f.val.val x) (gradient f.val.val x)
    Integrable e ρ ∧ (∫ x, e x ∂ρ) = ‖a‖ ^ 2 := by
  have := probability hV
  have hρ := IntrinsicScalarPoisson.gibbs_eq_tilted hU hV
  obtain ⟨hm, hi, he⟩ := Intrinsic.gradient_energy volume hU hV.1
    (EuclideanSpace.basisFun (Fin d) ℝ) f.property.1 f.property.2.1 f.property.2.2
  rw [← hρ] at hm hi he
  simp only [EuclideanSpace.basisFun_apply, real_inner_self_eq_norm_sq] at hi he
  obtain ⟨b, hb, hbae⟩ := compact_mem_graph hU hB hV f
  have hab : a = b := by
    apply (operator hU hB hV).mem_graph_snd_inj
    · rw [operator, ScalarForm.l2Operator_graph, ScalarForm.mem_l2Graph_iff]
      exact ⟨_, rfl, ha⟩
    · rw [operator, ScalarForm.l2Operator_graph, ScalarForm.mem_l2Graph_iff]
      exact ⟨_, rfl, hb⟩
    · rfl
  refine ⟨hi, he.trans ?_⟩
  rw [hab, Riesz1.poisson_norm_sq]
  apply integral_congr_ae
  filter_upwards [hbae] with x hx
  exact congrArg (· ^ 2) hx.symm

/-- Actual value and derivative of a smooth core jet, used to identify all
terms in the proof of Proposition 3.3. -/
theorem core_ae (f : EuclideanScalarForm.smoothCore U) :
    (ScalarForm.value J (ScalarForm.ofCore J f) =ᵐ[ρ] f.val) ∧
    (ScalarForm.deriv J (ScalarForm.ofCore J f) =ᵐ[ρ] gradient f.val) := by
  have := probability hV
  exact ⟨(Riesz1.WeightedSobolev.memLp_of_smoothNearClosure hB
    (supported hU hV) f.property).1.coeFn_toLp,
    (Riesz1.WeightedSobolev.memLp_of_smoothNearClosure hB
      (supported hU hV) f.property).2.coeFn_toLp⟩

/-- Values of the compact lift, as used in the proof of Proposition 3.3. -/
theorem compactGradientLift_value
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef)
    (f : compactTests U) (i : Fin d) :
    input v i (compactGradientLift hU hB hV hM f).val =
      coordinateLp i (ScalarForm.deriv J (ScalarForm.ofCore J f.val)) := by
  change v i (compactGraphBase hU hB hV _ (compactGradientLift hU hB hV hM f)) = _
  exact (congrArg (v i) (compactGradientLift_base hU hB hV hM f)).trans
    (compactGradientBase_value hU hB hV f i)

/-- Diffusion energy of one compact-gradient coordinate, as used in the proof of Proposition 3.3. -/
theorem compactGradientLift_diffusion
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef)
    (f : compactTests U) (i : Fin d) :
    ScalarForm.energy J ((WithLp.ofLp (compactGradientLift hU hB hV hM f).val).1 i)
      ((WithLp.ofLp (compactGradientLift hU hB hV hM f).val).1 i) =
      ∫ x, ‖gradient (fun y => fderiv ℝ f.val.val y
        (EuclideanSpace.single i 1)) x‖ ^ 2 ∂ρ := by
  change ScalarForm.energy J (compactGraphBase hU hB hV _
    (compactGradientLift hU hB hV hM f) i) (compactGraphBase hU hB hV _
      (compactGradientLift hU hB hV hM f) i) = _
  rw [compactGradientLift_base, ScalarForm.energy_integral]
  apply integral_congr_ae
  filter_upwards [(core_ae hU hB hV
    (compactDerivative f (EuclideanSpace.single i 1)).val).2] with x hx
  change inner ℝ (ScalarForm.deriv J (ScalarForm.ofCore J
    (compactDerivative f (EuclideanSpace.single i 1)).val) x)
    (ScalarForm.deriv J (ScalarForm.ofCore J
      (compactDerivative f (EuclideanSpace.single i 1)).val) x) = _
  rw [hx, real_inner_self_eq_norm_sq]
  rfl

/-- The compact graph's matrix energy is the actual Hessian contraction, as used in the proof of Proposition 3.3. -/
theorem compactGradientLift_matrix_ae
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef) (f : compactTests U) :
    matrixFieldPair (hessianMatrix V)
      (fun i => input v i (compactGradientLift hU hB hV hM f).val)
      (fun i => input v i (compactGradientLift hU hB hV hM f).val) =ᵐ[ρ]
      fun x => fderiv ℝ (fderiv ℝ V) x (gradient f.val.val x) (gradient f.val.val x) := by
  have he := ae_all_iff.mpr (fun i => compactGradientBase_ae hU hB hV f i)
  filter_upwards [supported hU hV, he] with x hx hy
  rw [Intrinsic.hessianMatrix_bilinear (hV.1.contDiffAt (hU.mem_nhds hx))]
  change (∑ i, ∑ j, v i (compactGraphBase hU hB hV _
    (compactGradientLift hU hB hV hM f)) x * hessianMatrix V x i j *
      v j (compactGraphBase hU hB hV _ (compactGradientLift hU hB hV hM f)) x) = _
  rw [compactGradientLift_base]
  simp only [hy]

/-- Full compact vector energy is generator-output mass, as used in the proof of Proposition 3.3. -/
theorem compactGradientLift_energy
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef)
    (f : compactTests U) (a : Lp ℝ 2 ρ)
    (ha : (ScalarForm.ofCore J f.val, a) ∈ ScalarForm.neumannGraph J) :
    (∑ i, ScalarForm.energy J
      ((WithLp.ofLp (compactGradientLift hU hB hV hM f).val).1 i)
      ((WithLp.ofLp (compactGradientLift hU hB hV hM f).val).1 i)) +
      ∫ x, matrixFieldPair (hessianMatrix V)
        (fun i => input v i (compactGradientLift hU hB hV hM f).val)
        (fun i => input v i (compactGradientLift hU hB hV hM f).val) x ∂ρ = ‖a‖ ^ 2 := by
  have := probability hV
  have hi (i : Fin d) : Integrable (fun x => ‖gradient
      (fun y => fderiv ℝ f.val.val y (EuclideanSpace.single i 1)) x‖ ^ 2) ρ :=
    (Intrinsic.memLp_gradient (compactDerivative f (EuclideanSpace.single i 1)).property.1
      (compactDerivative f (EuclideanSpace.single i 1)).property.2.1).norm.integrable_sq
  have he := compact_gradient_energy_coordinates hU hB hV f a ha
  have hsum := integrable_finsetSum Finset.univ (fun i _ => hi i)
  have hmat : Integrable (fun x => fderiv ℝ (fderiv ℝ V) x
      (gradient f.val.val x) (gradient f.val.val x)) ρ := by
    convert he.1.sub hsum using 1
    ext x
    dsimp only [Pi.sub_apply]
    ring
  simp_rw [compactGradientLift_diffusion]
  rw [integral_congr_ae (compactGradientLift_matrix_ae hU hB hV hM f),
    ← integral_finsetSum Finset.univ (fun i _ => hi i), ← integral_add hsum hmat]
  exact he.2

/-- The compact-gradient lift has exactly mass plus generator-output energy.
This is the norm identity in the proof of Proposition 3.3. -/
theorem compactGradientLift_norm_sq
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef)
    (f : compactTests U) (a : Lp ℝ 2 ρ)
    (ha : (ScalarForm.ofCore J f.val, a) ∈ ScalarForm.neumannGraph J) :
    ‖compactGradientLift hU hB hV hM f‖ ^ 2 =
      ‖ScalarForm.deriv J (ScalarForm.ofCore J f.val)‖ ^ 2 + ‖a‖ ^ 2 := by
  have hn := compactGraph_norm_sq hU hB hV hM (compactGradientLift hU hB hV hM f)
  have hv := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ =>
    congrArg (fun g : Lp ℝ 2 ρ => ‖g‖ ^ 2) (compactGradientLift_value hU hB hV hM f i))
  have he := compactGradientLift_energy hU hB hV hM f a ha
  have hv' := hv.trans (sum_coordinateLp_norm_sq (ScalarForm.deriv J (ScalarForm.ofCore J f.val)))
  exact hn.trans ((add_assoc _ _ _).trans (congrArg₂ (· + ·) hv' he))

/-- Difference version of the compact norm identity, as used in the proof of Proposition 3.3. -/
theorem compactGradientLift_sub_norm_sq
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef)
    (f g : compactTests U) (a b : Lp ℝ 2 ρ)
    (ha : (ScalarForm.ofCore J f.val, a) ∈ ScalarForm.neumannGraph J)
    (hb : (ScalarForm.ofCore J g.val, b) ∈ ScalarForm.neumannGraph J) :
    ‖compactGradientLift hU hB hV hM f - compactGradientLift hU hB hV hM g‖ ^ 2 =
      ‖ScalarForm.deriv J (ScalarForm.ofCore J f.val) -
        ScalarForm.deriv J (ScalarForm.ofCore J g.val)‖ ^ 2 + ‖a - b‖ ^ 2 := by
  have hg : (ScalarForm.ofCore J (f - g).val, a - b) ∈
      ScalarForm.neumannGraph J := by
    have hh := (ScalarForm.neumannGraph J).sub_mem ha hb
    simpa only [Submodule.coe_sub, map_sub, Prod.mk_sub_mk] using hh
  have he := compactGradientLift_norm_sq hU hB hV hM (f - g) (a - b) hg
  have hcore : ScalarForm.ofCore J (f - g).val =
      ScalarForm.ofCore J f.val - ScalarForm.ofCore J g.val :=
    (ScalarForm.ofCore J).map_sub f.val g.val
  have hgrad : ScalarForm.deriv J (ScalarForm.ofCore J (f - g).val) =
      ScalarForm.deriv J (ScalarForm.ofCore J f.val) -
        ScalarForm.deriv J (ScalarForm.ofCore J g.val) :=
    (congrArg (ScalarForm.deriv J) hcore).trans ((ScalarForm.deriv J).map_sub _ _)
  have hlift : compactGradientLift hU hB hV hM (f - g) =
      compactGradientLift hU hB hV hM f - compactGradientLift hU hB hV hM g :=
    (compactGradientLift hU hB hV hM).map_sub f g
  have hn := congrArg (fun t : VectorCore.compactGraph hU hB hV
    (fun x => CFC.sqrt (hessianMatrix V x)) ⊤ => ‖t‖ ^ 2) hlift
  have hd := congrArg (fun t : Lp (EuclideanSpace ℝ (Fin d)) 2 ρ =>
    ‖t‖ ^ 2 + ‖a - b‖ ^ 2) hgrad
  exact hn.symm.trans (he.trans hd)

omit hU hB hV in
/-- Internal metric lemma used for the completion step of the proof of Proposition 3.3. -/
theorem cauchySeq_of_squared_distances
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedAddCommGroup Z] (f : ℕ → X) (g : ℕ → Y) (h : ℕ → Z)
    (he : ∀ k l, ‖f k - f l‖ ^ 2 = ‖g k - g l‖ ^ 2 + ‖h k - h l‖ ^ 2)
    (hg : CauchySeq g) (hh : CauchySeq h) : CauchySeq f := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := Metric.cauchySeq_iff.mp hg (ε / 2) (by positivity)
  obtain ⟨m, hm⟩ := Metric.cauchySeq_iff.mp hh (ε / 2) (by positivity)
  refine ⟨max n m, fun k hk l hl => ?_⟩
  have hk₁ := hn k (le_trans (le_max_left _ _) hk) l (le_trans (le_max_left _ _) hl)
  have hk₂ := hm k (le_trans (le_max_right _ _) hk) l (le_trans (le_max_right _ _) hl)
  rw [dist_eq_norm] at hk₁ hk₂ ⊢
  nlinarith [he k l, norm_nonneg (f k - f l), norm_nonneg (g k - g l),
    norm_nonneg (h k - h l)]

/-- Compact scalar graph approximants give a Cauchy sequence in the full
vector norm, as used in the proof of Proposition 3.3. -/
theorem compactGradientLift_cauchy
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef)
    (c : ℕ → compactTests U) (b : ℕ → Lp ℝ 2 ρ)
    (hb : ∀ k, (ScalarForm.ofCore J (c k).val, b k) ∈ ScalarForm.neumannGraph J)
    (hc : CauchySeq (fun k => ScalarForm.deriv J (ScalarForm.ofCore J (c k).val)))
    (hbc : CauchySeq b) :
    CauchySeq (fun k => compactGradientLift hU hB hV hM (c k)) :=
  cauchySeq_of_squared_distances _ _ _
    (fun k l => compactGradientLift_sub_norm_sq hU hB hV hM
      (c k) (c l) (b k) (b l) (hb k) (hb l)) hc hbc

/-- Internal completion step for the proof of Proposition 3.3:
a Cauchy sequence of compact gradients has a limit in the existing closure. -/
theorem compactGradientLift_exists_limit
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef)
    (c : ℕ → compactTests U)
    (hc : CauchySeq (fun k => compactGradientLift hU hB hV hM (c k))) :
    ∃ z : VectorCore.compactCompletion hU hB hV
        (fun x => CFC.sqrt (hessianMatrix V x)) ⊤,
      Tendsto (fun k => (compactGradientLift hU hB hV hM (c k)).val) atTop (𝓝 z.val) := by
  let Z := VectorCore.compactCompletion hU hB hV
    (fun x => CFC.sqrt (hessianMatrix V x)) ⊤
  let g : ℕ → Z := fun k => ⟨(compactGradientLift hU hB hV hM (c k)).val,
    Submodule.le_topologicalClosure _ (compactGradientLift hU hB hV hM (c k)).property⟩
  have hgc : CauchySeq g := by
    rw [Metric.cauchySeq_iff] at hc ⊢
    exact hc
  have : CompleteSpace Z :=
    (Submodule.isClosed_topologicalClosure
      (VectorCore.compactGraph hU hB hV (fun x => CFC.sqrt (hessianMatrix V x)) ⊤)).completeSpace_coe
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hgc
  exact ⟨z, (Z.subtypeL.continuous.tendsto z).comp hz⟩

/-- Internal uniqueness-of-L²-limits step for the proof of Proposition 3.3. -/
theorem compactGradientLift_limit_values
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef)
    (c : ℕ → compactTests U) (ψ : ScalarForm.Domain J)
    (z : VectorCore.compactCompletion hU hB hV
      (fun x => CFC.sqrt (hessianMatrix V x)) ⊤)
    (hz : Tendsto (fun k => (compactGradientLift hU hB hV hM (c k)).val)
      atTop (𝓝 z.val))
    (hg : Tendsto (fun k => ScalarForm.deriv J (ScalarForm.ofCore J (c k).val))
      atTop (𝓝 (ScalarForm.deriv J ψ))) :
    ∀ i, input v i z.val = coordinateLp i (ScalarForm.deriv J ψ) := by
  intro i
  have h₁ := ((input v i).continuous.tendsto z.val).comp hz
  have h₂ := ((coordinateLp (ρ := ρ) i).continuous.tendsto _).comp hg
  apply tendsto_nhds_unique h₁
  apply h₂.congr'
  exact Eventually.of_forall (fun k => (compactGradientLift_value hU hB hV hM (c k) i).symm)

/-- The gradient in the existing vector completion, as used in the proof of Proposition 3.3, with its exact L² values. -/
theorem gradient_mem_compactCompletion [Nontrivial (EuclideanSpace ℝ (Fin d))]
    (hM : ∀ᵐ x ∂ρ, (hessianMatrix V x).PosSemidef)
    {C : ℝ} (hC : 0 ≤ C)
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹ ^ 2 - C ≤
      ‖gradient V x‖ ^ 2 / 4 - Δ V x / 2)
    (ψ : ScalarForm.Domain J) (a : Lp ℝ 2 ρ)
    (hψ : (ψ, a) ∈ ScalarForm.neumannGraph J) :
    ∃ z : VectorCore.compactCompletion hU hB hV
        (fun x => CFC.sqrt (hessianMatrix V x)) ⊤,
      ∀ i, input v i z.val = coordinateLp i (ScalarForm.deriv J ψ) := by
  obtain ⟨c, b, hb, _, ha, hg⟩ :=
    graph_approximation_with_gradient hU hB hV hC hbar ψ a hψ
  have hc := compactGradientLift_cauchy hU hB hV hM c b hb hg.cauchySeq ha.cauchySeq
  obtain ⟨z, hz⟩ := compactGradientLift_exists_limit hU hB hV hM c hc
  exact ⟨z, compactGradientLift_limit_values hU hB hV hM c ψ z hz hg⟩

/-- Domain part of the proof of Proposition 3.3, with the
finite-energy predicate and values equal to the weak gradient. -/
theorem gradient_finite_energy [Nontrivial (EuclideanSpace ℝ (Fin d))]
    {κ : ℝ} (hκ : 0 < κ)
    (hH : ∀ x ∈ U, ∀ e, κ * ‖e‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x e e)
    {C : ℝ} (hC : 0 ≤ C)
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹ ^ 2 - C ≤
      ‖gradient V x‖ ^ 2 / 4 - Δ V x / 2)
    (ψ : ScalarForm.Domain J) (a : Lp ℝ 2 ρ)
    (hψ : (ψ, a) ∈ ScalarForm.neumannGraph J) :
    ∃ u : Fin d → (form hU hB hV).1,
      WeightedFormDomain (form hU hB hV) (hessianMatrix V) ⊤ u ∧
      ∀ i, (u i).val = coordinateLp i (ScalarForm.deriv J ψ) := by
  have hM := hessian_posSemidef hU hV (fun x hx e =>
    (mul_nonneg hκ.le (sq_nonneg ‖e‖)).trans (hH x hx e))
  obtain ⟨z, hz⟩ := gradient_mem_compactCompletion hU hB hV hM hC hbar ψ a hψ
  obtain ⟨u, hu, hv⟩ := VectorCore.compactCompletion_finite_energy hU hB hV
    (hessianMatrix V) ⊤ measurable_hessian_entries hM z
  exact ⟨u, hu, fun i => (hv i).trans (hz i)⟩

/-- Existence, vector-domain membership and covariance in the proof of
Proposition 3.3. Sources range over all L², and tests over all H¹. -/
theorem exists_poisson_gradient_covariance [Nontrivial (EuclideanSpace ℝ (Fin d))]
    (hc : Convex ℝ U) {κ : ℝ} (hκ : 0 < κ)
    (hH : ∀ x ∈ U, ∀ e, κ * ‖e‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x e e)
    {C : ℝ} (hC : 0 ≤ C)
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹ ^ 2 - C ≤
      ‖gradient V x‖ ^ 2 / 4 - Δ V x / 2)
    (G : Lp ℝ 2 ρ) :
    ∃ ψ : ScalarForm.Domain J, ∃ u : Fin d → (form hU hB hV).1,
      (∫ x, ScalarForm.value J ψ x ∂ρ) = 0 ∧
      (ψ, @Riesz1.poissonCenter _ _ ρ (probability hV) G) ∈ ScalarForm.neumannGraph J ∧
      WeightedFormDomain (form hU hB hV) (hessianMatrix V) ⊤ u ∧
      (∀ i, (u i).val = coordinateLp i (ScalarForm.deriv J ψ)) ∧
      ∀ K : ScalarForm.Domain J,
        Integrable (fun x => inner ℝ (ScalarForm.deriv J ψ x)
          (ScalarForm.deriv J K x)) ρ ∧
        ProbabilityTheory.covariance G (ScalarForm.value J K) ρ =
          ∫ x, inner ℝ (ScalarForm.deriv J ψ x) (ScalarForm.deriv J K x) ∂ρ := by
  obtain ⟨ψ, hm, hψ, hcov⟩ := exists_poisson_covariance hU hB hc hV hκ hH G
  obtain ⟨u, hu, hv⟩ := gradient_finite_energy hU hB hV hκ hH hC hbar ψ _ hψ
  exact ⟨ψ, u, hm, hψ, hu, hv, hcov⟩

include hU hV in
/-- The mixed compact commutator identity in the proof of Proposition 3.3. Each coordinate test is arbitrary, rather
than itself a gradient. The generator is paired with a compact weighted
adjoint derivative, so this identity needs no convergence of source gradients. -/
theorem compact_mixed_commutator (f h : compactTests U) (i : Fin d) :
    let e : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single i 1
    let Df := fun y => fderiv ℝ f.val.val y e
    let T := fun x => h.val.val x *
      (∑ j, hessianMatrix V x i j * gradient f.val.val x j)
    Integrable T ρ ∧
    (∫ x, inner ℝ (gradient Df x) (gradient h.val.val x) ∂ρ) +
      (∫ x, T x ∂ρ) =
      ∫ x, Intrinsic.langevin V f.val.val x *
        (fderiv ℝ V x e * h.val.val x - fderiv ℝ h.val.val x e) ∂ρ := by
  have := probability hV
  dsimp only
  let e : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single i 1
  let Df := fun y => fderiv ℝ f.val.val y e
  let Lf := Intrinsic.langevin V f.val.val
  let Ld := Intrinsic.langevin V Df
  have hLf := Intrinsic.contDiff_langevin hU hV.1 f.property.1 f.property.2.2
  have hLc := Intrinsic.hasCompactSupport_langevin V f.property.2.1
  have hd : ContDiff ℝ ∞ Df := (compactDerivative f e).property.1
  have hdc : HasCompactSupport Df := (compactDerivative f e).property.2.1
  have hdU : tsupport Df ⊆ U := (compactDerivative f e).property.2.2
  have hLd := Intrinsic.contDiff_langevin hU hV.1 hd hdU
  have hLdc := Intrinsic.hasCompactSupport_langevin V hdc
  have hmemh : MemLp h.val.val 2 ρ :=
    h.property.1.continuous.memLp_of_hasCompactSupport h.property.2.1
  have hmemd : MemLp (fun x => fderiv ℝ Lf x e) 2 ρ :=
    ((hLf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous.memLp_of_hasCompactSupport
      (hLc.fderiv_apply ℝ e)
  have hmemLd : MemLp Ld 2 ρ := hLd.continuous.memLp_of_hasCompactSupport hLdc
  have he : (fun x => h.val.val x * fderiv ℝ Lf x e) =ᵐ[ρ]
      fun x => h.val.val x * Ld x + h.val.val x *
        (∑ j, hessianMatrix V x i j * gradient f.val.val x j) := by
    filter_upwards [supported hU hV] with x hx
    have hh := Intrinsic.coordinate_commutator
      (hV.1.contDiffAt (hU.mem_nhds hx)) f.property.1 i
    change fderiv ℝ Lf x e = Ld x + _ at hh
    rw [hh, mul_add]
  have hi₁ := hmemh.integrable_mul hmemd
  have hi₂ := hmemh.integrable_mul hmemLd
  have hiT : Integrable (fun x => h.val.val x *
      (∑ j, hessianMatrix V x i j * gradient f.val.val x j)) ρ := by
    apply (hi₁.sub hi₂).congr
    filter_upwards [he] with x hx
    dsimp only [Pi.sub_apply, Pi.mul_apply]
    linarith
  have hρ := IntrinsicScalarPoisson.gibbs_eq_tilted hU hV
  have h₁ := Intrinsic.integrationByParts volume hU hV.1 hd hdc hdU
    h.property.1.contDiffOn
  have h₂ := Intrinsic.directional_integrationByParts volume hU hV.1
    h.property.1 h.property.2.1 h.property.2.2 hLf.contDiffOn e
  rw [← hρ] at h₁ h₂
  refine ⟨hiT, ?_⟩
  calc
    _ = (∫ x, h.val.val x * Ld x ∂ρ) + ∫ x,
        h.val.val x * (∑ j, hessianMatrix V x i j * gradient f.val.val x j) ∂ρ := by
      congr 1
      exact (h₁.trans (integral_congr_ae (μ := ρ) (Eventually.of_forall
        (fun x => real_inner_comm (gradient Df x) (gradient h.val.val x))))).symm
    _ = ∫ x, h.val.val x * fderiv ℝ Lf x e ∂ρ := by
      exact (integral_add hi₂ hiT).symm.trans (integral_congr_ae he.symm)
    _ = _ := h₂

/-- The compact weighted adjoint derivative is an L² test, and pairs with
the weak gradient of every H¹ element, as used in the proof of Proposition 3.3. This is the scalar limit identity needed
on the right-hand side of the mixed compact commutator. -/
theorem compact_adjoint_pairing (h : compactTests U) (i : Fin d) :
    ∃ q : Lp ℝ 2 ρ,
      (q =ᵐ[ρ] fun x => fderiv ℝ V x (EuclideanSpace.single i 1) * h.val.val x -
        fderiv ℝ h.val.val x (EuclideanSpace.single i 1)) ∧
      ∀ F : ScalarForm.Domain J,
        inner ℝ (coordinateLp i (ScalarForm.deriv J F))
          (ScalarForm.value J (ScalarForm.ofCore J h.val)) =
          inner ℝ (ScalarForm.value J F) q := by
  have := probability hV
  let e : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single i 1
  let Q := fun x => h.val.val x * fderiv ℝ V x e - fderiv ℝ h.val.val x e
  have hqc : Continuous Q :=
    (Riesz1.WeightedSobolev.continuous_cutoff_mul hU h.property.1.continuous
      h.property.2.2 ((hV.1.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const)).sub
          ((h.property.1.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hq : MemLp Q 2 ρ := Riesz1.WeightedSobolev.memLp_of_continuousOn_closure hB
    (supported hU hV) hqc.continuousOn
  let q := hq.toLp Q
  refine ⟨q, ?_, ?_⟩
  · filter_upwards [hq.coeFn_toLp] with x hx
    change q x = _ at hx ⊢
    rw [hx]
    dsimp only [Q]
    ring
  have hcore (f : EuclideanScalarForm.smoothCore U) :
      inner ℝ (coordinateLp i (ScalarForm.deriv J (ScalarForm.ofCore J f)))
        (ScalarForm.value J (ScalarForm.ofCore J h.val)) =
      inner ℝ (ScalarForm.value J (ScalarForm.ofCore J f)) q := by
    obtain ⟨W, hW, hUW, hf⟩ := f.property
    have he := Intrinsic.directional_integrationByParts volume hU hV.1
      h.property.1 h.property.2.1 h.property.2.2
      (hf.mono (subset_closure.trans hUW)) e
    rw [← IntrinsicScalarPoisson.gibbs_eq_tilted hU hV] at he
    rw [L2.inner_def, L2.inner_def]
    calc
      _ = ∫ x, h.val.val x * fderiv ℝ f.val x e ∂ρ := by
        apply integral_congr_ae
        filter_upwards [coordinateLp_ae i (ScalarForm.deriv J (ScalarForm.ofCore J f)),
          (core_ae hU hB hV f).2, (core_ae hU hB hV h.val).1] with x hx hy hz
        rw [Real.inner_apply, hz, hx, hy]
        rw [← inner_gradient_left, EuclideanSpace.inner_single_right]
        simp only [one_mul, conj_trivial]
        ring
      _ = ∫ x, f.val x * Q x ∂ρ := by
        convert he using 1
        apply integral_congr_ae
        exact Eventually.of_forall (fun x => by dsimp only [Q]; ring)
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [(core_ae hU hB hV f).1, hq.coeFn_toLp] with x hx hy
        rw [Real.inner_apply, hx, hy]
  have hh := (ScalarForm.denseRange_ofCore J).equalizer
    (((coordinateLp (ρ := ρ) i).continuous.comp (ScalarForm.deriv J).continuous).inner continuous_const)
    ((ScalarForm.value J).continuous.inner continuous_const) (funext hcore)
  exact fun F => congrFun hh F

end Riesz2.DifferentiatedPoisson
