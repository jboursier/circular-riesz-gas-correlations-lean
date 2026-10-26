/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.PhysicalDecay
import all Riesz2.DecayShort.PhysicalComparisonPart4
public import Riesz2.ToMathlib.NaturalMatrixPerturbation

/-!
# Proper physical short-range comparison

The bounded auxiliary solution and its actual matrix-action residual for
Proposition 4.10, on the physical active marginal law.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal

namespace Riesz2.DecayShort.PhysicalDecay

open PhysicalComparison

private theorem internal_euclidean_norm_le_sum {n : ℕ} (z : EuclideanSpace ℝ (Fin n)) :
    ‖z‖ ≤ ∑ i, |z i| := by
  have he : z = ∑ i, z i • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    simp [EuclideanSpace.single, Pi.single_apply]
  conv_lhs => rw [he]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul]
  simp [EuclideanSpace.single, PiLp.norm_single]

/-- Internal matrix-action realization for Proposition 4.10.
A scalar L² entry envelope and a pointwise Euclidean bound on the field
produce the actual residual, with its a.e. identity and product L² bound. -/
theorem internal_action_of_envelope {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {n : ℕ} (M : α → Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, Measurable (fun x => M x i j))
    (T : α → ℝ) (hT : MemLp T 2 ν) (hT0 : ∀ᵐ x ∂ν, 0 ≤ T x)
    (u : Fin n → Lp ℝ 2 ν) (R : ℝ) (hR : 0 ≤ R)
    (hentry : ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ T x)
    (hu : ∀ᵐ x ∂ν, ‖(WithLp.toLp 2 (fun i => u i x) : EuclideanSpace ℝ (Fin n))‖ ≤ R) :
    ∃ g : Fin n → Lp ℝ 2 ν,
      (∀ᵐ x ∂ν, ∀ i, g i x = ∑ j, M x i j * u j x) ∧
      ‖WithLp.toLp 2 g‖ ≤ (n : ℝ)^2 * R * (eLpNorm T 2 ν).toReal := by
  let c := (n : ℝ)^2 * R
  let G : Lp ℝ 2 ν := c • hT.toLp T
  have hG : ∀ᵐ x ∂ν, G x = c * T x := by
    filter_upwards [Lp.coeFn_smul c (hT.toLp T), hT.coeFn_toLp] with x hx hy
    change G x = c * (hT.toLp T) x at hx
    rw [hx, hy]
  obtain ⟨g,hg,hbound⟩ := internal_action_l2 M hM u G (by
    filter_upwards [hG,hT0,hentry,hu] with x hx hTx hMx hux
    rw [hx]
    apply (internal_euclidean_norm_le_sum _).trans
    calc
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, T x * R := by
        apply Finset.sum_le_sum
        intro i _
        change |∑ j, M x i j * u j x| ≤ _
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul (hMx i j)
          ((PiLp.norm_apply_le (WithLp.toLp 2 (fun i => u i x)) j).trans hux)
          (abs_nonneg _) hTx
      _ = c * T x := by simp only [Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]; dsimp only [c]; ring)
  refine ⟨g,hg,hbound.trans_eq ?_⟩
  rw [norm_smul, Real.norm_of_nonneg (show 0 ≤ c by dsimp [c]; positivity), Lp.norm_toLp]

/-- Internal subtype transport in Proposition 4.10.
A supported measure admits a measurable projection onto its retained
carrier, preserving its actual pullback measure and the point a.e. -/
theorem internal_retained_projection {E : Type*} [MeasurableSpace E]
    (ν : Measure E) (U : Set E) (hU : MeasurableSet U) (hne : U.Nonempty)
    (hsupport : ∀ᵐ x ∂ν, x ∈ U) :
    ∃ τ : E → U, MeasurePreserving τ ν (ν.comap ((↑) : U → E)) ∧
      (∀ x : U, τ x.val = x) ∧ (∀ᵐ x ∂ν, (τ x).val = x) := by
  obtain ⟨τ,hτ,hleft⟩ := hU.exists_measurable_proj hne
  have hmap : (ν.comap ((↑) : U → E)).map ((↑) : U → E) = ν := by
    rw [map_comap_subtype_coe hU, Measure.restrict_eq_self_of_ae_mem hsupport]
  refine ⟨τ,⟨hτ,?_⟩,hleft,hsupport.mono fun x hx => ?_⟩
  · calc
      ν.map τ = ((ν.comap ((↑) : U → E)).map ((↑) : U → E)).map τ := congrArg (Measure.map τ) hmap.symm
      _ = (ν.comap ((↑) : U → E)).map (τ ∘ ((↑) : U → E)) := Measure.map_map hτ measurable_subtype_coe
      _ = ν.comap ((↑) : U → E) := by
        have he : τ ∘ ((↑) : U → E) = id := funext hleft
        rw [he,Measure.map_id]
  · exact congrArg Subtype.val (hleft ⟨x,hx⟩)

private theorem internal_hessian_affine {n : ℕ}
    {K : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hK : ContDiffAt ℝ 2 K x) (β k : ℝ) :
    hessianMatrix (fun y => β*K y+k) x = β • hessianMatrix K x := by
  have he : fderiv ℝ (fun y => β*K y+k) = fderiv ℝ (fun y => β*K y) :=
    funext fun _ => fderiv_add_const k
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [hessianMatrix_entry ((contDiffAt_const.mul hK).add contDiffAt_const),hessianMatrix_entry hK,
    he,PhysicalCollision.internal_hessian_const_mul hK]

set_option backward.isDefEq.respectTransparency false in
/-- Internal realization for Proposition 4.10, retaining
the exact additive normalization and the physical curvature certificate.
The scalar form is the closed conservative Neumann realization of the
active Euclidean law. -/
theorem internal_proper_realization (p : Parameters) (hs : 1 < p.val.2)
    (n : ℕ+) (m : ℕ) (hn : (n : ℕ) ≤ (((n : ℕ)+m).succPNat : ℕ))
    (θ : PhysicalCutoff) (h : ℝ) (hh : 0 < h) (b : Bool) :
    let ν := activeTiltedGapLaw p ((n : ℕ)+m).succPNat n hn θ h b
    let U := AffineSimplex.chartDomain n ((n+m : ℕ)+1)
    let F := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      ∑ i, (θ.val (((n : ℝ)^h)⁻¹*x i) +
        if b then θ.val (((n : ℝ)^h)⁻¹*(x i)⁻¹) else 0)
    let K := fun x => p.val.1⁻¹*(p.val.1*F x-
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal))
    let a := p.val.1*(n : ℝ)^(-(p.val.2+2)*h)
    ∃ (V : EuclideanSpace ℝ (Fin (n : ℕ)) → ℝ) (k : ℝ) (Q : ScalarFormData ν),
      (∀ x, V x = p.val.1*K x+k) ∧
      IsEuclideanGibbsPotential volume ν U V ∧ IsNeumannRealization U Q ∧
      IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
      (∀ᵐ x ∂ν, x ∈ U) ∧
      (∀ᵐ x ∂ν, (hessianMatrix V x).PosSemidef) ∧
      (∀ᵐ x ∂ν, ∀ z : Fin (n : ℕ) → ℝ,
        a*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*hessianMatrix V x i j*z j) ∧
      (∀ x ∈ U, hessianMatrix V x = p.val.1 • hessianMatrix K x) ∧
      ∀ f : Fin (n : ℕ) → Lp ℝ 2 ν,
        ∃! u : Fin (n : ℕ) → Q.1, WeightedWeakSolution Q (hessianMatrix V) ⊤ f u := by
  intro ν U F K a
  obtain ⟨V,k,hVk,hG⟩ := proper_physical_gibbs p hs n m hn θ h hh b
  change (∀ x, V x = p.val.1*K x+k) at hVk
  rw [← ProperMarginalChart.baseDomain_eq_properMarginalDomain n m] at hG
  have hU : IsOpen U := AffineSimplex.isOpen_chartDomain _ _
  have hB : Bornology.IsBounded U := AffineSimplex.isBounded_chartDomain _ _
  let Q := IntrinsicScalarCore.form hU hB hG
  have hQ := IntrinsicScalarCore.closed_dirichlet hU hB hG
  obtain ⟨hK,hcurv⟩ := PhysicalFibres.active_marginal_curvature p hs n m n.pos
    (Equiv.refl _) θ h hh b
  change ContDiffOn ℝ (⊤ : ℕ∞) K U at hK
  have ha : 0 < a := mul_pos p.property.1
    (Real.rpow_pos_of_pos (by exact_mod_cast n.pos) _)
  have hH (x) (hx : x ∈ U) (u : EuclideanSpace ℝ (Fin (n : ℕ))) :
      a*‖u‖^2 ≤ fderiv ℝ (fderiv ℝ V) x u u := by
    have he : fderiv ℝ V = fderiv ℝ (fun y => p.val.1*K y) := by
      rw [funext hVk]
      exact funext fun _ => fderiv_add_const k
    rw [he,PhysicalCollision.internal_hessian_const_mul
      ((hK.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num))]
    simpa only [a,mul_assoc] using mul_le_mul_of_nonneg_left (hcurv x hx u) p.property.1.le
  have hsupp := IntrinsicScalarCore.supported hU hG
  have hHb : ∀ᵐ x ∂ν, (hessianMatrix V x).PosSemidef := hsupp.mono fun x hx =>
    DifferentiatedPoisson.hessian_posSemidef_on hU hG
      (fun x hx u => (mul_nonneg ha.le (sq_nonneg ‖u‖)).trans (hH x hx u)) x hx
  have hl : ∀ᵐ x ∂ν, ∀ z : Fin (n : ℕ) → ℝ,
      a*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*hessianMatrix V x i j*z j :=
    hsupp.mono fun x hx z => DifferentiatedPoisson.hessian_coordinate_lower hU hG hH x hx z
  refine ⟨V,k,Q,hVk,hG,IntrinsicScalarCore.realization hU hB hG,hQ,
    IntrinsicScalarCore.conservative hU hB hG,hsupp,hHb,hl,?_,?_⟩
  · intro x hx
    rw [funext hVk]
    exact internal_hessian_affine ((hK.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num)) _ _
  · intro f
    exact MatrixEnergy.weightedWeakSolution_existsUnique Q hQ (hessianMatrix V) ⊤ hHb a ha
      (hl.mono fun x hx z _ => hx z) DifferentiatedPoisson.measurable_hessian_entries f

end Riesz2.DecayShort.PhysicalDecay
