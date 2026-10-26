/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.PhysicalFormDomain
public import Riesz2.ToMathlib.NonnegativeFormBound
public import Riesz2.ToMathlib.NeumannScalarDirichlet
public import Riesz2.HelfferSjostrand.IntrinsicIntegrationByParts
public import Riesz2.HelfferSjostrand.DifferentiatedPoissonPart3
public import Riesz2.Preliminaries.TruncatedCoercivity

/-!
# Physical Sobolev Hessian pairings

See Subsection 5.1 of the paper, using the actual completed Neumann
gradient graph and the physical tilted laws.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped ENNReal ContDiff Topology Laplacian

namespace Riesz2.PhysicalFormDomain.Internal
variable {ι : Type*} [Fintype ι]
/-- Every entry of a positive matrix is bounded by its trace. -/
theorem entry_le_trace {M : Matrix ι ι ℝ} (hM : M.PosSemidef) (i j : ι) :
    |M i j| ≤ M.trace := by
  classical
  have hd (k : ι) : M k k ≤ M.trace :=
    Finset.single_le_sum (f := fun k => M k k) (fun k _ => hM.diag_nonneg) (Finset.mem_univ k)
  have hs : M j i = M i j := by
    simpa only [Matrix.conjTranspose_apply, star_trivial] using congrFun (congrFun hM.1 i) j
  have hp := hM.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j 1)
  have hm := hM.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
  simp [Matrix.mulVec_add, Matrix.mulVec_sub, dotProduct_add, dotProduct_sub,
    Matrix.mulVec_single, hs] at hp hm
  exact abs_le.mpr ⟨by linarith [hd i, hd j], by linarith [hd i, hd j]⟩
end Riesz2.PhysicalFormDomain.Internal
namespace Riesz2.PhysicalFormDomain.Internal
variable {α H : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Young's inequality makes a trace-dominated scalar mixed pairing integrable. -/
theorem mixed_entry_bound (J : H →L[ℝ] Lp ℝ 2 μ)
    (w a : α → ℝ) (ha : AEStronglyMeasurable a μ)
    (hbound : ∀ᵐ x ∂μ, |a x| ≤ w x)
    (C : ℝ) (_hC : 0 ≤ C)
    (hscalar : ∀ f : H, Integrable (fun x => w x * (J f x) ^ 2) μ ∧
      (∫ x, w x * (J f x) ^ 2 ∂μ) ≤ C * ‖f‖ ^ 2) (f g : H) :
    Integrable (fun x => a x * J f x * J g x) μ ∧
      |∫ x, a x * J f x * J g x ∂μ| ≤ C * (‖f‖ ^ 2 + ‖g‖ ^ 2) / 2 := by
  have hi := ((hscalar f).1.add (hscalar g).1).div_const 2
  have he : ∀ᵐ x ∂μ, ‖a x * J f x * J g x‖ ≤
      (w x * (J f x) ^ 2 + w x * (J g x) ^ 2) / 2 := by
    filter_upwards [hbound] with x hx
    have hw : 0 ≤ w x := (abs_nonneg _).trans hx
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have hy := mul_le_mul_of_nonneg_right hx (mul_nonneg (abs_nonneg (J f x)) (abs_nonneg (J g x)))
    have hz := mul_nonneg hw (sq_nonneg (|J f x| - |J g x|))
    simp only [sub_sq, sq_abs] at hz
    nlinarith only [hy, hz]
  have hf : Integrable (fun x => a x * J f x * J g x) μ :=
    hi.mono' ((ha.mul (Lp.aestronglyMeasurable _)).mul (Lp.aestronglyMeasurable _)) he
  refine ⟨hf, ?_⟩
  calc
    _ ≤ ∫ x, ‖a x * J f x * J g x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, (w x * (J f x) ^ 2 + w x * (J g x) ^ 2) / 2 ∂μ :=
      integral_mono_ae hf.norm hi he
    _ = ((∫ x, w x * (J f x) ^ 2 ∂μ) + (∫ x, w x * (J g x) ^ 2 ∂μ)) / 2 := by
      rw [integral_div, integral_add (hscalar f).1 (hscalar g).1]
    _ ≤ _ := by linarith [(hscalar f).2, (hscalar g).2]
end Riesz2.PhysicalFormDomain.Internal
namespace Riesz2.PhysicalFormDomain.Internal
variable {H K : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
/-- Rescaling converts a quadratic bilinear bound into the product bound. -/
theorem bilinear_bound_of_sq (B : H →ₗ[ℝ] K →ₗ[ℝ] ℝ) (C : ℝ) (_hC : 0 ≤ C)
    (h : ∀ f g, |B f g| ≤ C * (‖f‖ ^ 2 + ‖g‖ ^ 2) / 2) (f : H) (g : K) :
    ‖B f g‖ ≤ C * ‖f‖ * ‖g‖ := by
  by_cases hf : f = 0
  · simp [hf]
  by_cases hg : g = 0
  · simp [hg]
  have hnf : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hng : 0 < ‖g‖ := norm_pos_iff.mpr hg
  have hh := h (‖f‖⁻¹ • f) (‖g‖⁻¹ • g)
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, norm_smul,
    Real.norm_eq_abs, abs_inv, abs_of_pos hnf, abs_of_pos hng, inv_mul_cancel₀ hnf.ne',
    inv_mul_cancel₀ hng.ne', one_pow, abs_mul] at hh
  have hx := (mul_le_mul_of_nonneg_right hh (mul_nonneg hnf.le hng.le))
  have he : ‖g‖⁻¹ * (‖f‖⁻¹ * |B f g|) * (‖f‖ * ‖g‖) = |B f g| := by
    field_simp
  rw [he] at hx
  norm_num only [show (1 + 1 : ℝ) = 2 by norm_num, mul_div_cancel_right₀ C (by norm_num : (2 : ℝ) ≠ 0)] at hx
  simpa only [Real.norm_eq_abs, mul_assoc] using hx
end Riesz2.PhysicalFormDomain.Internal
namespace Riesz2.PhysicalFormDomain.Internal
variable {α H : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
set_option backward.isDefEq.respectTransparency false in
/-- A scalar multiplication form dominated by a bounded nonnegative form is continuous. -/
theorem exists_entry_form (J : H →L[ℝ] Lp ℝ 2 μ)
    (w a : α → ℝ) (ha : AEStronglyMeasurable a μ)
    (hbound : ∀ᵐ x ∂μ, |a x| ≤ w x)
    (C : ℝ) (hC : 0 ≤ C)
    (hscalar : ∀ f : H, Integrable (fun x => w x * (J f x) ^ 2) μ ∧
      (∫ x, w x * (J f x) ^ 2 ∂μ) ≤ C * ‖f‖ ^ 2) :
    ∃ B : H →L[ℝ] H →L[ℝ] ℝ, ∀ f g,
      Integrable (fun x => a x * J f x * J g x) μ ∧
      B f g = ∫ x, a x * J f x * J g x ∂μ := by
  let F := fun f g : H => ∫ x, a x * J f x * J g x ∂μ
  have hi (f g : H) := (mixed_entry_bound J w a ha hbound C hC hscalar f g).1
  have hadd (f g k : H) : F (f + g) k = F f k + F g k := by
    rw [← integral_add (hi f k) (hi g k)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add (J f) (J g)] with x hx
    simp only [map_add, hx, Pi.add_apply]
    ring
  have hsmul (c : ℝ) (f g : H) : F (c • f) g = c • F f g := by
    rw [smul_eq_mul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c (J f)] with x hx
    simp only [map_smul, hx, Pi.smul_apply, smul_eq_mul]
    ring
  have hadd' (f g k : H) : F f (g + k) = F f g + F f k := by
    rw [← integral_add (hi f g) (hi f k)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add (J g) (J k)] with x hx
    simp only [map_add, hx, Pi.add_apply]
    ring
  have hsmul' (c : ℝ) (f g : H) : F f (c • g) = c • F f g := by
    rw [smul_eq_mul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c (J g)] with x hx
    simp only [map_smul, hx, Pi.smul_apply, smul_eq_mul]
    ring
  let B := LinearMap.mk₂ ℝ F hadd hsmul hadd' hsmul'
  have hb : ∀ f g, ‖B f g‖ ≤ C * ‖f‖ * ‖g‖ :=
    bilinear_bound_of_sq B C hC (fun f g => (mixed_entry_bound J w a ha hbound C hC hscalar f g).2)
  exact ⟨B.mkContinuous₂ C hb, fun f g => ⟨hi f g, rfl⟩⟩
end Riesz2.PhysicalFormDomain.Internal
namespace Riesz2.PhysicalFormDomain.Internal
variable {α ι : Type*} [MeasurableSpace α] [Fintype ι] {ρ : Measure α}
set_option backward.isDefEq.respectTransparency false in
/-- Trace domination gives the entire matrix domain and a continuous mixed form. -/
theorem exists_matrix_form (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q)
    (M : α → Matrix ι ι ℝ) (w : α → ℝ)
    (hM : ∀ i j, AEStronglyMeasurable (fun x => M x i j) ρ)
    (hbound : ∀ᵐ x ∂ρ, ∀ i j, |M x i j| ≤ w x)
    (C : ℝ) (hC : 0 ≤ C)
    (hscalar : ∀ f : Q.1, Integrable (fun x => w x * (f.val x) ^ 2) ρ ∧
      (∫ x, w x * (f.val x) ^ 2 ∂ρ) ≤ C * (‖f.val‖ ^ 2 + Q.2 f f)) :
    (∀ (S : Submodule ℝ (ι → ℝ)) (u : ι → Q.1),
      WeightedFormDomain Q M S u ↔ ∀ᵐ x ∂ρ, (fun i => (u i).val x) ∈ S) ∧
    ∃ B : (ι → ScalarFormHilbert.Space Q hQ) →L[ℝ]
        (ι → ScalarFormHilbert.Space Q hQ) →L[ℝ] ℝ,
      ∀ u v : ι → Q.1, Integrable (matrixFieldPair M (fun i => (u i).val) (fun i => (v i).val)) ρ ∧
        B (fun i => (ScalarFormHilbert.equiv Q hQ).symm (u i))
          (fun i => (ScalarFormHilbert.equiv Q hQ).symm (v i)) =
          ∫ x, matrixFieldPair M (fun i => (u i).val) (fun i => (v i).val) x ∂ρ := by
  have hscalar' (f : ScalarFormHilbert.Space Q hQ) :
      Integrable (fun x => w x * (ScalarFormHilbert.value Q hQ f x) ^ 2) ρ ∧
      (∫ x, w x * (ScalarFormHilbert.value Q hQ f x) ^ 2 ∂ρ) ≤ C * ‖f‖ ^ 2 := by
    rw [ScalarFormHilbert.norm_sq]
    exact hscalar (ScalarFormHilbert.equiv Q hQ f)
  have hentry (i j : ι) := exists_entry_form (ScalarFormHilbert.value Q hQ)
    w (fun x => M x i j) (hM i j) (hbound.mono fun x hx => hx i j) C hC hscalar'
  choose b hb using hentry
  have hi (u v : ι → Q.1) (i j : ι) :
      Integrable (fun x => (u i).val x * M x i j * (v j).val x) ρ := by
    have h := (hb i j ((ScalarFormHilbert.equiv Q hQ).symm (u i))
      ((ScalarFormHilbert.equiv Q hQ).symm (v j))).1
    convert h using 1
    funext x
    change (u i).val x * M x i j * (v j).val x = M x i j * (u i).val x * (v j).val x
    ring
  have hp (u v : ι → Q.1) :
      Integrable (matrixFieldPair M (fun i => (u i).val) (fun i => (v i).val)) ρ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi u v i j
  refine ⟨fun S u => ⟨fun h => h.1, fun h => ⟨h, hp u u⟩⟩, ?_⟩
  let B : (ι → ScalarFormHilbert.Space Q hQ) →L[ℝ]
      (ι → ScalarFormHilbert.Space Q hQ) →L[ℝ] ℝ :=
    ∑ i, ∑ j, (b i j).bilinearComp (ContinuousLinearMap.proj i) (ContinuousLinearMap.proj j)
  refine ⟨B, fun u v => ⟨hp u v, ?_⟩⟩
  simp only [B, sum_apply, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.proj_apply]
  change (∑ i, ∑ j, b i j ((ScalarFormHilbert.equiv Q hQ).symm (u i))
    ((ScalarFormHilbert.equiv Q hQ).symm (v j))) = _
  rw [show (∫ x, matrixFieldPair M (fun i => (u i).val) (fun i => (v i).val) x ∂ρ) =
      ∑ i, ∑ j, ∫ x, (u i).val x * M x i j * (v j).val x ∂ρ by
    change (∫ x, ∑ i, ∑ j, (u i).val x * M x i j * (v j).val x ∂ρ) = _
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi u v i j))]
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ (fun j _ => hi u v i j)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [(hb i j _ _).2]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change M x i j * (u i).val x * (v j).val x = (u i).val x * M x i j * (v j).val x
    ring
end Riesz2.PhysicalFormDomain.Internal

namespace Riesz2.PhysicalFormDomain

namespace Internal

/-- Transfer the scalar bound to the value-domain encoding. -/
theorem scalar_bound_on_form {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    {Ω : Set E} {ρ : Measure E} {V : E → ℝ}
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hV : IsEuclideanGibbsPotential volume ρ Ω V)
    (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ x ∈ Ω, Δ V x ≤ (1 / 4 : ℝ) * ‖gradient V x‖ ^ 2 + C)
    (ht : ∀ x ∈ Ω, 0 ≤ Δ V x)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ x ∈ Ω, (Metric.infDist x (frontier Ω))⁻¹ ^ 2 - B ≤
      ‖gradient V x‖ ^ 2 / 4 - Δ V x / 2)
    (f : (IntrinsicScalarCore.form hΩ hbounded hV).1) :
    Integrable (fun x => Δ V x * (f.val x) ^ 2) ρ ∧
      (∫ x, Δ V x * (f.val x) ^ 2 ∂ρ) ≤
        (2 + 2 * C) * (‖f.val‖ ^ 2 + (IntrinsicScalarCore.form hΩ hbounded hV).2 f f) := by
  let J := IntrinsicScalarCore.jet hΩ hbounded hV
  let e := ScalarForm.valueEquiv J (IntrinsicScalarCore.value_injective hΩ hbounded hV)
  let g := e.symm f
  have he : ScalarForm.value J g = f.val := by
    exact congrArg Subtype.val (e.apply_symm_apply f)
  have hn : ‖g‖ ^ 2 = ‖f.val‖ ^ 2 + (IntrinsicScalarCore.form hΩ hbounded hV).2 f f := by
    rw [ScalarForm.norm_sq, he]
    rfl
  have hh := NonnegativeFormBound.gibbs_trace_bound hΩ hbounded hV C hC hc ht B hB hb g
  change Integrable (fun x => Δ V x * (ScalarForm.value J g x) ^ 2) ρ ∧ _ at hh
  rwa [he, hn] at hh

end Internal

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 5.1 of the paper, scalar estimate for proper marginals.
The form is a realization of the entire Neumann graph. Integrability
is concluded for every Sobolev value. All proper marginals are covered. -/
theorem proper_scalar_trace_bound (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε : ℝ) :
    let p := ofLong β s
    let hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ) := by simp; omega
    let ρ := activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ ε false
    let Ω := AffineSimplex.chartDomain n ((n + m : ℕ) + 1)
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      p.val.1 * ∑ i, θ.val ((n : ℝ) ^ (-ε) * x i) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal)
    ∃ Q : ScalarFormData ρ, IsNeumannRealization Ω Q ∧ IsClosedScalarDirichletForm Q ∧
      ∃ C : ℝ, 0 < C ∧ ∀ f : Q.1,
        Integrable (fun x => Δ V x * (f.val x) ^ 2) ρ ∧
        (∫ x, Δ V x * (f.val x) ^ 2 ∂ρ) ≤ C * (‖f.val‖ ^ 2 + Q.2 f f) := by
  intro p hn ρ Ω V
  have : NeZero (n : ℕ) := ⟨by exact_mod_cast n.pos.ne'⟩
  have hV := proper_gibbs_potential β s n m θ ε
  obtain ⟨hsm, ht, hs, B, hB, hb⟩ := proper_trace_inputs β s n m n.pos θ ε
  obtain ⟨C, hC, hc⟩ := hs (1 / 4) (by norm_num)
  let hΩ := AffineSimplex.isOpen_chartDomain n ((n + m : ℕ) + 1)
  let hbounded := AffineSimplex.isBounded_chartDomain n ((n + m : ℕ) + 1)
  refine ⟨IntrinsicScalarCore.form hΩ hbounded hV,
    IntrinsicScalarCore.realization hΩ hbounded hV,
    IntrinsicScalarCore.closed_dirichlet hΩ hbounded hV, 2 + 2 * C, by linarith only [hC], ?_⟩
  exact Internal.scalar_bound_on_form hΩ hbounded hV C hC hc ht B hB hb

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 5.1 of the paper, intrinsic scalar estimate on the full
cycle, with the literal full physical ambient extension and tilted law. -/
theorem full_intrinsic_scalar_trace_bound (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (θ : PhysicalCutoff) (ε : ℝ) :
    let p := ofLong β s
    let ρ := fullIntrinsicTiltedGapLaw p N θ ε false
    ∃ U : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        U y.val = fullPhysicalPotentialValue p N hN θ ε false y) ∧
      let V := fun z : gapTangentSpace N => U (WithLp.toLp 2 (fun i => 1 + z.val i))
      ∃ Q : ScalarFormData ρ, IsNeumannRealization (intrinsicGapDomain N) Q ∧
        IsClosedScalarDirichletForm Q ∧
        ∃ C : ℝ, 0 < C ∧ ∀ f : Q.1,
          Integrable (fun z => Δ V z * (f.val z) ^ 2) ρ ∧
          (∫ z, Δ V z * (f.val z) ^ 2 ∂ρ) ≤ C * (‖f.val‖ ^ 2 + Q.2 f f) := by
  intro p ρ
  have : Nontrivial (gapTangentSpace N) := PhysicalCollision.tangent_nontrivial N hN
  obtain ⟨U, hU, hv, hg, ht, hs, B, hB, hb⟩ := full_trace_inputs β s N hN θ ε
  obtain ⟨C, hC, hc⟩ := hs (1 / 4) (by norm_num)
  let hΩ := AffineMetric.intrinsicGapDomain_isOpen N
  let hbounded := PhysicalCollision.intrinsicGapDomain_bounded N
  refine ⟨U, hU, hv, IntrinsicScalarCore.form hΩ hbounded hg,
    IntrinsicScalarCore.realization hΩ hbounded hg,
    IntrinsicScalarCore.closed_dirichlet hΩ hbounded hg, 2 + 2 * C, by linarith only [hC], ?_⟩
  exact Internal.scalar_bound_on_form hΩ hbounded hg C hC hc ht B hB hb

namespace Internal

/-- The matrix trace is the classical Laplacian at a smooth point. -/
theorem hessian_trace {n : ℕ} {V : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hV : ContDiffAt ℝ ∞ V x) :
    (hessianMatrix V x).trace = Δ V x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis V
    (EuclideanSpace.basisFun (Fin n) ℝ)]
  simp only [Matrix.trace, Matrix.diag, Intrinsic.hessianMatrix_eq_second hV,
    EuclideanSpace.basisFun_apply, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]

end Internal

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 5.1 of the paper, complete proper-marginal clause.
The scalar trace estimate, equality of the whole finite-energy domain
with the constrained Sobolev space, and continuity of all mixed Hessian
pairings hold for the literal physical law and Hessian. In particular the
unconstrained component space is the entire vector Sobolev space. -/
theorem proper_form_domain (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε : ℝ) :
    let p := ofLong β s
    let hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ) := by simp; omega
    let ρ := activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ ε false
    let Ω := AffineSimplex.chartDomain n ((n + m : ℕ) + 1)
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      p.val.1 * ∑ i, θ.val ((n : ℝ) ^ (-ε) * x i) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal)
    ∃ Q : ScalarFormData ρ, IsNeumannRealization Ω Q ∧
      ∃ hQ : IsClosedScalarDirichletForm Q,
        (∃ C : ℝ, 0 < C ∧ ∀ f : Q.1,
          Integrable (fun x => Δ V x * (f.val x) ^ 2) ρ ∧
          (∫ x, Δ V x * (f.val x) ^ 2 ∂ρ) ≤ C * (‖f.val‖ ^ 2 + Q.2 f f)) ∧
        (∀ (S : Submodule ℝ (Fin (n : ℕ) → ℝ)) (u : Fin (n : ℕ) → Q.1),
          WeightedFormDomain Q (hessianMatrix V) S u ↔
            ∀ᵐ x ∂ρ, (fun i => (u i).val x) ∈ S) ∧
        ∃ B : (Fin (n : ℕ) → ScalarFormHilbert.Space Q hQ) →L[ℝ]
            (Fin (n : ℕ) → ScalarFormHilbert.Space Q hQ) →L[ℝ] ℝ,
          ∀ u v : Fin (n : ℕ) → Q.1,
            Integrable (matrixFieldPair (hessianMatrix V)
              (fun i => (u i).val) (fun i => (v i).val)) ρ ∧
            B (fun i => (ScalarFormHilbert.equiv Q hQ).symm (u i))
              (fun i => (ScalarFormHilbert.equiv Q hQ).symm (v i)) =
              ∫ x, matrixFieldPair (hessianMatrix V)
                (fun i => (u i).val) (fun i => (v i).val) x ∂ρ := by
  intro p hn ρ Ω V
  obtain ⟨Q, hreal, hQ, C, hC, hc⟩ := proper_scalar_trace_bound β s n m θ ε
  have hV := proper_gibbs_potential β s n m θ ε
  have ha : 0 < (n : ℝ) ^ (-ε) := Real.rpow_pos_of_pos (by exact_mod_cast n.pos) _
  obtain ⟨hprob, hnorm, hsm, ⟨κ, hκ, hcurv⟩, hrest⟩ :=
    MarginalCollision.proper_marginal_collision_criterion p n m n.pos
      (Equiv.refl _) θ ha Finset.univ false
  have hΩeq : properMarginalDomain ⟨(n : ℕ), n.pos⟩ ((n : ℕ) + m).succPNat = Ω := by
    ext x
    simp only [properMarginalDomain, Ω, AffineSimplex.chartDomain,
      Nat.succPNat_coe, Nat.cast_succ, PNat.mk_coe]
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero, ← sub_eq_add_neg, hΩeq] at hcurv
  have hH (x) (hx : x ∈ Ω) (u) : 0 ≤ fderiv ℝ (fderiv ℝ V) x u u :=
    (mul_nonneg hκ.le (sq_nonneg ‖u‖)).trans (hcurv x hx u)
  have hbound : ∀ᵐ x ∂ρ, ∀ i j, |hessianMatrix V x i j| ≤ Δ V x := by
    filter_upwards [IntrinsicScalarCore.supported (AffineSimplex.isOpen_chartDomain _ _) hV] with x hx
    intro i j
    have hM := DifferentiatedPoisson.hessian_posSemidef_on
      (AffineSimplex.isOpen_chartDomain _ _) hV hH x hx
    rw [← Internal.hessian_trace (hV.1.contDiffAt ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds hx))]
    exact Internal.entry_le_trace hM i j
  obtain ⟨hd, B, hB⟩ := Internal.exists_matrix_form Q hQ (hessianMatrix V) (Δ V)
    (fun i j => (DifferentiatedPoisson.measurable_hessian_entries i j).aestronglyMeasurable)
    hbound C hC.le hc
  exact ⟨Q, hreal, hQ, ⟨C, hC, hc⟩, hd, B, hB⟩

end Riesz2.PhysicalFormDomain

namespace Riesz2.PhysicalFormDomain.Internal

/-- Parseval on the actual zero-sum tangent space, with its normal component removed. -/
theorem tangent_parseval (N : ℕ+) (v : EuclideanSpace ℝ (Fin (N : ℕ))) :
    (∑ k, (∑ i, v i * (stdOrthonormalBasis ℝ (gapTangentSpace N) k).val i) ^ 2) =
      ‖v‖ ^ 2 - (∑ i, v i) ^ 2 / (N : ℝ) := by
  let a := (∑ i, v i) / (N : ℝ)
  let q : gapTangentSpace N := ⟨WithLp.toLp 2 (fun i => v i - a), by
    change (∑ i, (v i - a)) = 0
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, a]
    field_simp
    ring⟩
  let b := stdOrthonormalBasis ℝ (gapTangentSpace N)
  have hi (k) : inner ℝ q (b k) = ∑ i, v i * (b k).val i := by
    change (∑ i, (b k).val i * (v i - a)) = _
    rw [show (∑ i, (b k).val i * (v i - a)) =
      (∑ i, v i * (b k).val i) - a * ∑ i, (b k).val i by
        simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_comm]]
    rw [(b k).property, mul_zero, sub_zero]
  have hnorm : ‖q‖ ^ 2 = ‖v‖ ^ 2 - (∑ i, v i) ^ 2 / (N : ℝ) := by
    rw [← Submodule.norm_coe, EuclideanSpace.real_norm_sq_eq,
      EuclideanSpace.real_norm_sq_eq]
    change (∑ i, (v i - a) ^ 2) = _
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [show (∑ i, 2 * v i * a) = 2 * (∑ i, v i) * a by
      simp only [Finset.mul_sum, Finset.sum_mul]]
    dsimp only [a]
    field_simp
    ring
  rw [← hnorm, ← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner]
  apply Finset.sum_congr rfl
  intro k _
  change (∑ i, v i * (b k).val i) ^ 2 = inner ℝ q (b k) * inner ℝ (b k) q
  simp only [real_inner_comm q (b k), hi k, pow_two]

/-- The intrinsic squared size of an interval functional is r(1-r/N). -/
theorem interval_tangent_parseval (N : ℕ+) (i : Fin (N : ℕ)) {r : ℕ}
    (hr : r ≤ (N : ℕ)) :
    (∑ k, cyclicGapSum N i r
      (WithLp.ofLp (stdOrthonormalBasis ℝ (gapTangentSpace N) k).val) ^ 2) =
      (r : ℝ) * (1 - (r : ℝ) / N) := by
  classical
  let v : EuclideanSpace ℝ (Fin (N : ℕ)) :=
    WithLp.toLp 2 (fun j => if j ∈ cyclicIndexInterval N i r then 1 else 0)
  have hv (u : EuclideanSpace ℝ (Fin (N : ℕ))) :
      (∑ j, v j * u j) = cyclicGapSum N i r (WithLp.ofLp u) := by
    simp only [v, ite_mul, one_mul, zero_mul, Finset.sum_ite_mem,
      Finset.univ_inter]
    exact sum_cyclicIndexInterval_eq_cyclicGapSum N i hr _
  have hn : ‖v‖ ^ 2 = (r : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [v, ite_pow, one_pow, zero_pow (by omega : 2 ≠ 0),
      Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one,
      card_cyclicIndexInterval N i hr]
  have hs : (∑ j, v j) = (r : ℝ) := by
    simp only [v, Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_const, nsmul_eq_mul, mul_one, card_cyclicIndexInterval N i hr]
  have h := tangent_parseval N v
  simp_rw [hv] at h
  rw [hn, hs] at h
  rw [h]
  ring
end Riesz2.PhysicalFormDomain.Internal
namespace Riesz2.PhysicalFormDomain.Internal

/-- Nonnegative rank-one trace comparisons sum without losing the factor two. -/
theorem rankOne_trace_comparison (N : ℕ+) {κ : Type*} [Fintype κ]
    (B : EuclideanSpace ℝ (Fin (N : ℕ)) →L[ℝ]
      EuclideanSpace ℝ (Fin (N : ℕ)) →L[ℝ] ℝ)
    (L : κ → EuclideanSpace ℝ (Fin (N : ℕ)) →L[ℝ] ℝ) (c : κ → ℝ)
    (hc : ∀ k, 0 ≤ c k)
    (hB : ∀ u, B u u = ∑ k, c k * (L k u) ^ 2)
    (hL : ∀ k, (∑ i, (L k (EuclideanSpace.single i 1)) ^ 2) ≤
      2 * ∑ j, (L k (stdOrthonormalBasis ℝ (gapTangentSpace N) j).val) ^ 2) :
    (∑ i, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) ≤
      2 * ∑ j, B (stdOrthonormalBasis ℝ (gapTangentSpace N) j).val
        (stdOrthonormalBasis ℝ (gapTangentSpace N) j).val := by
  simp_rw [hB]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun j k => c k * _)]
  simp_rw [← Finset.mul_sum]
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ => by nlinarith only [mul_le_mul_of_nonneg_left (hL k) (hc k)]

/-- An interval of length at most half the cycle loses at most half its squared size. -/
theorem interval_trace_comparison (N : ℕ+) (i : Fin (N : ℕ)) {r : ℕ}
    (hr : r ≤ (N : ℕ) / 2) :
    (∑ j, (PhysicalEnergy.intervalLinear N i r (EuclideanSpace.single j 1)) ^ 2) ≤
      2 * ∑ k, (PhysicalEnergy.intervalLinear N i r
        (stdOrthonormalBasis ℝ (gapTangentSpace N) k).val) ^ 2 := by
  classical
  have hrN : r ≤ (N : ℕ) := hr.trans (Nat.div_le_self _ _)
  have hsingle (j) : PhysicalEnergy.intervalLinear N i r (EuclideanSpace.single j 1) =
      if j ∈ cyclicIndexInterval N i r then 1 else 0 := by
    rw [PhysicalEnergy.intervalLinear_apply]
    convert cyclicGapSum_single N i j hrN using 1
    congr 1
    funext a
    simp only [PiLp.single_apply]
  simp_rw [hsingle, PhysicalEnergy.intervalLinear_apply]
  rw [interval_tangent_parseval N i hrN]
  simp only [ite_pow, one_pow, zero_pow (by omega : 2 ≠ 0),
    Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one,
    card_cyclicIndexInterval N i hrN]
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hhalf : (2 : ℝ) * r ≤ N := by exact_mod_cast (show 2 * r ≤ (N : ℕ) by omega)
  have hdiv : (r : ℝ) / N ≤ 1 / 2 := (div_le_iff₀ hN).mpr (by linarith)
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  nlinarith only [mul_nonneg hr0 (sub_nonneg.mpr hdiv)]

/-- A forcing singleton loses at most half its squared size when N is at least two. -/
theorem singleton_trace_comparison (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (i : Fin (N : ℕ)) :
    (∑ j, ((EuclideanSpace.single j (1 : ℝ)) i) ^ 2) ≤
      2 * ∑ k, ((stdOrthonormalBasis ℝ (gapTangentSpace N) k).val i) ^ 2 := by
  classical
  have h := tangent_parseval N (EuclideanSpace.single i 1)
  simp only [PiLp.single_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, PiLp.norm_single,
    Real.norm_eq_abs, abs_one, one_pow] at h
  rw [h]
  simp only [PiLp.single_apply, ite_pow, one_pow,
    zero_pow (by omega : 2 ≠ 0), Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hi : (1 : ℝ) / N ≤ 1 / 2 :=
    (div_le_iff₀ (by linarith : (0 : ℝ) < N)).mpr (by linarith)
  linarith
end Riesz2.PhysicalFormDomain.Internal
namespace Riesz2.PhysicalFormDomain.Internal
set_option backward.isDefEq.respectTransparency false in
/-- The full potential has its literal nonnegative interval and singleton Hessian decomposition. -/
theorem full_rankOne_representation (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ)
    (U : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ)
    (hv : ∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
      U y.val = fullPhysicalPotentialValue p N hN θ ε false y)
    (y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N}) :
    ∃ c : (Fin (N : ℕ) × Fin ((N : ℕ) / 2)) ⊕ Fin (N : ℕ) → ℝ,
      (∀ k, 0 ≤ c k) ∧ ∀ u : EuclideanSpace ℝ (Fin (N : ℕ)),
        fderiv ℝ (fderiv ℝ U) y.val u u =
          ∑ k, c k * (Sum.elim
            (fun t : Fin (N : ℕ) × Fin ((N : ℕ) / 2) =>
              PhysicalEnergy.intervalLinear N t.1 (t.2.val + 1))
            (fun i : Fin (N : ℕ) => EuclideanSpace.proj (𝕜 := ℝ) i) k u) ^ 2 := by
  classical
  obtain ⟨W, hW, hw, hd⟩ := PhysicalEnergy.ambient_derivatives p N
  let a := (N : ℝ) ^ (-ε)
  let g := fun t => θ.val (a * t)
  let P := fun x : EuclideanSpace ℝ (Fin (N : ℕ)) => ∑ i, g (x i)
  have ha : 0 < a := Real.rpow_pos_of_pos (by exact_mod_cast N.pos) _
  have hy (i) : 0 < y.val i := by
    simpa only [PhysicalEnergy.gapSum_one] using (y.property i 1 (by omega) (by omega)).1
  have hg (i) : ContDiffAt ℝ ∞ g (y.val i) :=
    (PhysicalCollision.cutoff_contDiffAt θ (mul_pos ha (hy i))).comp (y.val i) (contDiffAt_const.mul contDiffAt_id)
  have hPi (i) : ContDiffAt ℝ ∞ (fun x : EuclideanSpace ℝ (Fin (N : ℕ)) => g (x i)) y.val :=
    ContDiffAt.comp (f := fun x : EuclideanSpace ℝ (Fin (N : ℕ)) => x i) (g := g)
      y.val (hg i) (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt
  have hP : ContDiffAt ℝ ∞ P y.val := by
    apply ContDiffAt.sum
    intro i _
    exact hPi i
  have hpquad (u : EuclideanSpace ℝ (Fin (N : ℕ))) :
      fderiv ℝ (fderiv ℝ P) y.val u u = ∑ i, deriv (deriv g) (y.val i) * (u i) ^ 2 := by
    rw [PhysicalCollision.internal_hessian_sum Finset.univ _ (fun i _ => (hPi i).of_le (by simp)) u]
    apply Finset.sum_congr rfl
    intro i _
    have h := PhysicalCollision.internal_scalar_affine_hessian g (EuclideanSpace.proj (𝕜 := ℝ) i)
      0 (by simpa only [add_zero, PiLp.proj_apply] using (hg i).of_le (by simp)) u
    simpa only [add_zero, PiLp.proj_apply] using h
  have heq : U =ᶠ[𝓝 y.val] (fun x => p.val.1 * (W x + P x)) := by
    filter_upwards [(PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds y.property] with x hx
    rw [hv ⟨x,hx⟩, hw ⟨x,hx⟩]
    simp only [fullPhysicalPotentialValue, Bool.false_eq_true, ↓reduceIte, add_zero]
    rfl
  let c : (Fin (N : ℕ) × Fin ((N : ℕ) / 2)) ⊕ Fin (N : ℕ) → ℝ :=
    Sum.elim (fun t => p.val.1 *
      ((2 - if 2 * (t.2.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
        PhysicalEnergy.intervalCoefficient p N
          ⟨cyclicGapSum N t.1 (t.2.val + 1) (WithLp.ofLp y.val),
            y.property _ _ (by omega) (by have := t.2.isLt; omega)⟩))
      (fun i => p.val.1 * deriv (deriv g) (y.val i))
  refine ⟨c, ?_, ?_⟩
  · intro k
    cases k with
    | inl t =>
      dsimp only [c, Sum.elim_inl]
      apply mul_nonneg p.property.1.le
      apply mul_nonneg
      · split_ifs <;> norm_num
      · exact (PhysicalEnergy.intervalCoefficient_pos p N _).le
    | inr i =>
      obtain ⟨C, hC, hc⟩ := PhysicalCollision.upper_penalty_curvature θ
      exact mul_nonneg p.property.1.le (hc a (y.val i) ha (hy i)).1
  · intro u
    have hWy : ContDiffAt ℝ 2 W y.val :=
      (hW.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds y.property)).of_le (by simp)
    rw [heq.fderiv.fderiv_eq, PhysicalCollision.internal_hessian_const_mul (hWy.add (hP.of_le (by simp))),
      PhysicalCollision.internal_hessian_add hWy (hP.of_le (by simp)), (hd y u u).2, hpquad,
      Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp only [c, Sum.elim_inl, Sum.elim_inr, PhysicalEnergy.intervalLinear_apply,
      PiLp.proj_apply, mul_add, Finset.mul_sum, mul_assoc, ← pow_two]
end Riesz2.PhysicalFormDomain.Internal
namespace Riesz2.PhysicalFormDomain.Internal
set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 5.1 of the paper: the ambient physical trace is at most twice the intrinsic trace. -/
theorem full_trace_comparison (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ) (U : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ)
    (hU : ContDiffOn ℝ ∞ U (gapAmbientDomain N))
    (hv : ∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
      U y.val = fullPhysicalPotentialValue p N hN θ ε false y)
    (z : gapTangentSpace N) (hz : z ∈ intrinsicGapDomain N) :
    let y := WithLp.toLp 2 (fun i => 1 + z.val i)
    let V := fun z : gapTangentSpace N => U (WithLp.toLp 2 (fun i => 1 + z.val i))
    (hessianMatrix U y).PosSemidef ∧ 0 ≤ Δ U y ∧ Δ U y ≤ 2 * Δ V z := by
  intro y V
  have hy : y ∈ gapAmbientDomain N := PhysicalEnergy.simplex_subset_ambient N _
    (PhysicalCollision.intrinsic_chart_mem_simplex N hz)
  have hUy := hU.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hy)
  obtain ⟨c, hc, hquad⟩ := full_rankOne_representation p N hN θ ε U hv ⟨y,hy⟩
  let L := Sum.elim
    (fun t : Fin (N : ℕ) × Fin ((N : ℕ) / 2) => PhysicalEnergy.intervalLinear N t.1 (t.2.val + 1))
    (fun i : Fin (N : ℕ) => EuclideanSpace.proj (𝕜 := ℝ) i)
  have hn (u : EuclideanSpace ℝ (Fin (N : ℕ))) : 0 ≤ fderiv ℝ (fderiv ℝ U) y u u := by
    rw [hquad]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hc k) (sq_nonneg _)
  have hM : (hessianMatrix U y).PosSemidef := by
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    constructor
    · ext i j
      simp only [Matrix.conjTranspose_apply, star_trivial, Intrinsic.hessianMatrix_eq_second hUy]
      exact hUy.isSymmSndFDerivAt (by simp) _ _
    · intro t
      have h := hn (WithLp.toLp 2 t)
      rw [Intrinsic.hessianMatrix_bilinear hUy] at h
      simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
        Finset.mul_sum, mul_assoc] using h
  refine ⟨hM, Riesz2.PhysicalFormDomain.Internal.laplacian_nonneg U y hn, ?_⟩
  have hchart (u v : gapTangentSpace N) :
      fderiv ℝ (fderiv ℝ V) z u v = fderiv ℝ (fderiv ℝ U) y u.val v.val := by
    have he : (fun w : gapTangentSpace N => U ((gapTangentSpace N).subtypeL w +
        WithLp.toLp 2 (fun _ => (1 : ℝ)))) = V := by
      funext w
      congr 1
      ext i
      change w.val i + 1 = 1 + w.val i
      ring
    have hy' : (gapTangentSpace N).subtypeL z + WithLp.toLp 2 (fun _ => (1 : ℝ)) = y := by
      ext i
      change z.val i + 1 = 1 + z.val i
      ring
    have h := AffineMetricTransport.hessian_comp_affine (gapTangentSpace N).subtypeL
      (WithLp.toLp 2 (fun _ => (1 : ℝ))) (by rw [hy']; exact hUy.of_le (by simp)) u v
    rwa [he, hy'] at h
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis U
      (EuclideanSpace.basisFun (Fin (N : ℕ)) ℝ),
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis V
      (stdOrthonormalBasis ℝ (gapTangentSpace N))]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    EuclideanSpace.basisFun_apply, hchart]
  apply rankOne_trace_comparison N _ L c hc hquad
  intro k
  cases k with
  | inl t => exact interval_trace_comparison N t.1 (Nat.succ_le_of_lt t.2.isLt)
  | inr i => exact singleton_trace_comparison N hN i
end Riesz2.PhysicalFormDomain.Internal

namespace Riesz2.PhysicalFormDomain.Internal

/-- Scaling a nonnegative scalar multiplication form preserves its bound. -/
theorem scale_scalar_bound {α : Type*} [MeasurableSpace α] {ρ : Measure α}
    (Q : ScalarFormData ρ) (w : α → ℝ) (C : ℝ)
    (h : ∀ f : Q.1, Integrable (fun x => w x * (f.val x) ^ 2) ρ ∧
      (∫ x, w x * (f.val x) ^ 2 ∂ρ) ≤ C * (‖f.val‖ ^ 2 + Q.2 f f))
    (a : ℝ) (ha : 0 ≤ a) (f : Q.1) :
    Integrable (fun x => (a * w x) * (f.val x) ^ 2) ρ ∧
      (∫ x, (a * w x) * (f.val x) ^ 2 ∂ρ) ≤ (a * C) * (‖f.val‖ ^ 2 + Q.2 f f) := by
  have he : (∫ x, (a * w x) * (f.val x) ^ 2 ∂ρ) =
      a * (∫ x, w x * (f.val x) ^ 2 ∂ρ) := by simp only [mul_assoc, integral_const_mul]
  refine ⟨by simpa only [mul_assoc] using (h f).1.const_mul a, ?_⟩
  exact he.le.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (h f).2 ha)

/-- A nonnegative matrix with dominated trace inherits the scalar form bound,
its whole natural domain, and continuous mixed pairings. -/
theorem exists_matrix_form_of_trace {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    {ρ : Measure α} (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q)
    (M : α → Matrix ι ι ℝ) (w : α → ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hM : ∀ᵐ x ∂ρ, (M x).PosSemidef ∧ (M x).trace ≤ w x)
    (C : ℝ) (hC : 0 ≤ C)
    (hscalar : ∀ f : Q.1, Integrable (fun x => w x * (f.val x) ^ 2) ρ ∧
      (∫ x, w x * (f.val x) ^ 2 ∂ρ) ≤ C * (‖f.val‖ ^ 2 + Q.2 f f)) :
    (∀ f : Q.1, Integrable (fun x => (M x).trace * (f.val x) ^ 2) ρ ∧
      (∫ x, (M x).trace * (f.val x) ^ 2 ∂ρ) ≤ C * (‖f.val‖ ^ 2 + Q.2 f f)) ∧
    (∀ (S : Submodule ℝ (ι → ℝ)) (u : ι → Q.1), WeightedFormDomain Q M S u ↔
      ∀ᵐ x ∂ρ, (fun i => (u i).val x) ∈ S) ∧
    ∃ B : (ι → ScalarFormHilbert.Space Q hQ) →L[ℝ]
        (ι → ScalarFormHilbert.Space Q hQ) →L[ℝ] ℝ,
      ∀ u v : ι → Q.1,
        Integrable (matrixFieldPair M (fun i => (u i).val) (fun i => (v i).val)) ρ ∧
        B (fun i => (ScalarFormHilbert.equiv Q hQ).symm (u i))
          (fun i => (ScalarFormHilbert.equiv Q hQ).symm (v i)) =
          ∫ x, matrixFieldPair M (fun i => (u i).val) (fun i => (v i).val) x ∂ρ := by
  have hbound : ∀ᵐ x ∂ρ, ∀ i j, |M x i j| ≤ w x :=
    hM.mono fun x hx i j => (entry_le_trace hx.1 i j).trans hx.2
  obtain ⟨hd, B, hB⟩ := exists_matrix_form Q hQ M w
    (fun i j => (hMm i j).aestronglyMeasurable) hbound C hC hscalar
  refine ⟨?_, hd, B, hB⟩
  intro f
  have htrm : AEStronglyMeasurable (fun x => (M x).trace) ρ :=
    (Finset.measurable_sum _ (fun i _ => hMm i i)).aestronglyMeasurable
  have hmajor : ∀ᵐ x ∂ρ, ‖(M x).trace * (f.val x) ^ 2‖ ≤ w x * (f.val x) ^ 2 := by
    filter_upwards [hM] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx.1.trace_nonneg (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right hx.2 (sq_nonneg _)
  have hi := (hscalar f).1.mono'
    (htrm.mul ((Lp.aestronglyMeasurable f.val).pow 2)) hmajor
  refine ⟨hi, (integral_mono_ae hi (hscalar f).1 ?_).trans (hscalar f).2⟩
  exact hM.mono fun x hx => mul_le_mul_of_nonneg_right hx.2 (sq_nonneg _)

/-- The factor-two comparison holds almost everywhere for the actual full tilted law. -/
theorem full_ae_trace_comparison (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ) (U : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ)
    (hU : ContDiffOn ℝ ∞ U (gapAmbientDomain N))
    (hv : ∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
      U y.val = fullPhysicalPotentialValue p N hN θ ε false y) :
    let V := fun z : gapTangentSpace N => U (WithLp.toLp 2 (fun i => 1 + z.val i))
    let M := fun z : gapTangentSpace N => hessianMatrix U (WithLp.toLp 2 (fun i => 1 + z.val i))
    ∀ᵐ z ∂fullIntrinsicTiltedGapLaw p N θ ε false,
      (M z).PosSemidef ∧ (M z).trace ≤ 2 * Δ V z := by
  intro V M
  have hV := PhysicalCollision.internal_full_gap_gibbs N p hN θ ε false U hU hv
  filter_upwards [IntrinsicScalarCore.supported (AffineMetric.intrinsicGapDomain_isOpen N) hV] with z hz
  have hy : WithLp.toLp 2 (fun i => 1 + z.val i) ∈ gapAmbientDomain N :=
    PhysicalEnergy.simplex_subset_ambient N _ (PhysicalCollision.intrinsic_chart_mem_simplex N hz)
  have hh := full_trace_comparison p N hN θ ε U hU hv z hz
  refine ⟨hh.1, ?_⟩
  exact (hessian_trace
    (hU.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hy))).le.trans hh.2.2

end Riesz2.PhysicalFormDomain.Internal

namespace Riesz2.PhysicalFormDomain

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 5.1 of the paper, complete full-cycle clause.
The ambient trace and all unrestricted ambient component pairings are
bounded using intrinsic scalar derivatives. The finite-energy domain is
exactly the constrained vector Sobolev space, for any fixed component
subspace, including the whole ambient space and the zero-sum space. -/
theorem full_form_domain (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (θ : PhysicalCutoff) (ε : ℝ) :
    let p := ofLong β s
    let ρ := fullIntrinsicTiltedGapLaw p N θ ε false
    ∃ U : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        U y.val = fullPhysicalPotentialValue p N hN θ ε false y) ∧
      let M := fun z : gapTangentSpace N =>
        hessianMatrix U (WithLp.toLp 2 (fun i => 1 + z.val i))
      ∃ Q : ScalarFormData ρ, IsNeumannRealization (intrinsicGapDomain N) Q ∧
        ∃ hQ : IsClosedScalarDirichletForm Q,
          (∃ C : ℝ, 0 < C ∧ ∀ f : Q.1,
            Integrable (fun z => (M z).trace * (f.val z) ^ 2) ρ ∧
            (∫ z, (M z).trace * (f.val z) ^ 2 ∂ρ) ≤ C * (‖f.val‖ ^ 2 + Q.2 f f)) ∧
          (∀ (S : Submodule ℝ (Fin (N : ℕ) → ℝ)) (u : Fin (N : ℕ) → Q.1),
            WeightedFormDomain Q M S u ↔ ∀ᵐ z ∂ρ, (fun i => (u i).val z) ∈ S) ∧
          ∃ B : (Fin (N : ℕ) → ScalarFormHilbert.Space Q hQ) →L[ℝ]
              (Fin (N : ℕ) → ScalarFormHilbert.Space Q hQ) →L[ℝ] ℝ,
            ∀ u v : Fin (N : ℕ) → Q.1,
              Integrable (matrixFieldPair M (fun i => (u i).val) (fun i => (v i).val)) ρ ∧
              B (fun i => (ScalarFormHilbert.equiv Q hQ).symm (u i))
                (fun i => (ScalarFormHilbert.equiv Q hQ).symm (v i)) =
                ∫ z, matrixFieldPair M (fun i => (u i).val) (fun i => (v i).val) z ∂ρ := by
  intro p ρ
  obtain ⟨U, hU, hv, Q, hreal, hQ, C, hC, hc⟩ :=
    full_intrinsic_scalar_trace_bound β s N hN θ ε
  let Y := fun z : gapTangentSpace N => WithLp.toLp 2 (fun i => 1 + z.val i)
  let V := fun z => U (Y z)
  let M := fun z => hessianMatrix U (Y z)
  have hMm (i j : Fin (N : ℕ)) : Measurable (fun z => M z i j) :=
    (DifferentiatedPoisson.measurable_hessian_entries i j).comp
      (PhysicalCollision.intrinsic_chart_contDiff N).continuous.measurable
  have ht : ∀ᵐ z ∂ρ, (M z).PosSemidef ∧ (M z).trace ≤ 2 * Δ V z :=
    Internal.full_ae_trace_comparison p N hN θ ε U hU hv
  have hscalar : ∀ f : Q.1,
      Integrable (fun z => (2 * Δ V z) * (f.val z) ^ 2) ρ ∧
        (∫ z, (2 * Δ V z) * (f.val z) ^ 2 ∂ρ) ≤ (2 * C) * (‖f.val‖ ^ 2 + Q.2 f f) :=
    Internal.scale_scalar_bound Q (Δ V) C hc 2 (by norm_num)
  have hdata := Internal.exists_matrix_form_of_trace (α := gapTangentSpace N)
    (ι := Fin (N : ℕ)) (ρ := ρ) Q hQ M
    (fun z => 2 * Δ V z) hMm ht (2 * C) (mul_nonneg (by norm_num) hC.le) hscalar
  obtain ⟨htrace, hdom, B, hB⟩ := hdata
  exact ⟨U, hU, hv, Q, hreal, hQ, ⟨2 * C, by positivity, htrace⟩, hdom, B, hB⟩

end Riesz2.PhysicalFormDomain
