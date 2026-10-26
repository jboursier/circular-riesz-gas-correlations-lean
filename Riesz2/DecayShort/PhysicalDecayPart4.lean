/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.PhysicalDecay
public import Riesz2.HelfferSjostrand.PhysicalCollisionPart2
public import Riesz2.DecayShort.MultiplierControl

/-!
# Full-cycle physical equation

Supporting results for Proposition 4.10. The ambient
potential is the physical short-interval extension, including the
antipodal normalization for two particles. The scalar form is intrinsic. The vector constraint is the zero-sum component space.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology ContDiff

namespace Riesz2.DecayShort.PhysicalDecay

private theorem internal_penalty_smooth {N : ℕ+} (θ : PhysicalCutoff)
    {a : ℝ} (ha : 0 < a) (b : Bool)
    {x : EuclideanSpace ℝ (Fin (N : ℕ))} (hx : ∀ i, 0 < x i) :
    ContDiffAt ℝ ∞ (fun y : EuclideanSpace ℝ (Fin (N : ℕ)) =>
      ∑ i, (θ.val (a*y i) + if b then θ.val (a*(y i)⁻¹) else 0)) x := by
  apply ContDiffAt.sum
  intro i _
  have hi : ContDiffAt ℝ ∞ (fun y : EuclideanSpace ℝ (Fin (N : ℕ)) => y i) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt
  have hup := (PhysicalCollision.cutoff_contDiffAt θ (mul_pos ha (hx i))).comp x
    (contDiffAt_const.mul hi)
  cases b
  · simpa only [Bool.false_eq_true, ↓reduceIte, add_zero,Function.comp_def] using hup
  · simpa only [↓reduceIte,Function.comp_def,Pi.inv_apply] using hup.add ((PhysicalCollision.cutoff_contDiffAt θ (mul_pos ha (inv_pos.mpr (hx i)))).comp x
      (contDiffAt_const.mul (hi.inv (hx i).ne')))

private theorem internal_penalty_nonneg {N : ℕ+} (θ : PhysicalCutoff)
    {a : ℝ} (ha : 0 < a) (b : Bool)
    {x : EuclideanSpace ℝ (Fin (N : ℕ))} (hx : ∀ i, 0 < x i)
    (u : EuclideanSpace ℝ (Fin (N : ℕ))) :
    0 ≤ fderiv ℝ (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin (N : ℕ)) =>
      ∑ i, (θ.val (a*y i) + if b then θ.val (a*(y i)⁻¹) else 0))) x u u := by
  let R : {R : ℝ // 0 < R} := ⟨a⁻¹, inv_pos.mpr ha⟩
  let U : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ := fun y => ∑ i, θ.val (a*y i)
  let I : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ := fun y => ∑ i, θ.val (a*(y i)⁻¹)
  have hU : ContDiffAt ℝ 2 U x := by
    simpa only [U, R, div_inv_eq_mul, mul_comm] using
      upperGapPenalty_contDiffAt θ R Finset.univ x hx
  have hu : 0 ≤ fderiv ℝ (fderiv ℝ U) x u u := by
    have he := upperGapPenalty_hessian θ R Finset.univ x hx u u
    have hθ := θ.property.2.2.2.2.choose_spec.2.1
    rw [show fderiv ℝ (fderiv ℝ U) x u u =
      ∑ i ∈ Finset.univ, deriv (deriv θ.val) (x i / R) / R.val^2 * (u i*u i) from
      (by simpa only [U, R, div_inv_eq_mul, mul_comm] using he)]
    exact Finset.sum_nonneg fun i _ => mul_nonneg
      (div_nonneg (hθ _ (div_pos (hx i) R.property)).1 (sq_nonneg _)) (mul_self_nonneg _)
  have hIx : x ∈ AffineSimplex.chartDomain (N : ℕ) ((∑ i, x i)+1) := ⟨hx,by linarith⟩
  have hI := PhysicalFibres.inverse_retained_penalty (N : ℕ) ((∑ i, x i)+1) θ ha
  have hi : 0 ≤ fderiv ℝ (fderiv ℝ I) x u u :=
    Riesz1.fderiv_fderiv_nonneg_of_convexOn
      (AffineSimplex.isOpen_chartDomain _ _) (AffineSimplex.convex_chartDomain _ _)
      hI.2 (hI.1.of_le (by simp)) hIx u
  cases b
  · simpa only [Bool.false_eq_true, ↓reduceIte, add_zero] using hu
  · have he : (fun y : EuclideanSpace ℝ (Fin (N : ℕ)) =>
        ∑ i, (θ.val (a*y i) + if true then θ.val (a*(y i)⁻¹) else 0)) =
        fun y => U y + I y := by funext y; simp only [↓reduceIte,Finset.sum_add_distrib,U,I]
    rw [he,PhysicalCollision.internal_hessian_add hU
      ((hI.1.of_le (by simp)).contDiffAt ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds hIx))]
    exact add_nonneg hu hi

/-- Ambient realization and a quantitative full-cycle energy bound for
Proposition 4.10. Both penalties are allowed. The bound
uses only the nearest image and holds for every ambient direction. In particular it covers the two-particle tangent equation. -/
theorem full_physical_matrix_lower (p : Parameters) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (θ : PhysicalCutoff) (h : ℝ) (b : Bool) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = fullPhysicalPotentialValue p N hN θ h b y) ∧
      IsEuclideanGibbsPotential volume (fullIntrinsicTiltedGapLaw p N θ h b)
        (intrinsicGapDomain N)
        (fun z => W (WithLp.toLp 2 (fun i => 1 + z.val i))) ∧
      ∀ z ∈ intrinsicGapDomain N, ∀ t : Fin (N : ℕ) → ℝ,
        (p.val.1*(p.val.2*(p.val.2+1))*(N : ℝ)^(-p.val.2-2)) * (∑ i, t i^2) ≤
          ∑ i, ∑ j, t i * hessianMatrix W
            (WithLp.toLp 2 (fun i => 1 + z.val i)) i j * t j := by
  classical
  obtain ⟨W₀,hW₀,hval₀,_,_,hlow,_⟩ := (PhysicalEnergy.restriction_and_derivatives p N hN).2.2
  let a := (N : ℝ)^(-h)
  have ha : 0 < a := Real.rpow_pos_of_pos (by positivity) _
  let P := fun y : EuclideanSpace ℝ (Fin (N : ℕ)) =>
    ∑ i, (θ.val (a*y i) + if b then θ.val (a*(y i)⁻¹) else 0)
  let W := fun y => p.val.1*(W₀ y+P y)
  have hpos (y : EuclideanSpace ℝ (Fin (N : ℕ))) (hy : y ∈ gapAmbientDomain N) (i) : 0 < y i := by
    simpa only [PhysicalEnergy.gapSum_one] using (hy i 1 (by omega) (by omega)).1
  have hW : ContDiffOn ℝ ∞ W (gapAmbientDomain N) := by
    apply contDiffOn_const.mul (hW₀.add _)
    intro y hy
    exact (internal_penalty_smooth θ ha b (hpos y hy)).contDiffWithinAt
  have hval (y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N}) :
      W y.val = fullPhysicalPotentialValue p N hN θ h b y := by
    dsimp only [W,P,a,fullPhysicalPotentialValue]
    rw [hval₀ y]
  refine ⟨W,hW,hval,PhysicalCollision.internal_full_gap_gibbs N p hN θ h b W hW hval,?_⟩
  intro z hz t
  let x := WithLp.toLp 2 (fun i => 1 + z.val i)
  let u := WithLp.toLp 2 t
  have hy := PhysicalCollision.intrinsic_chart_mem_simplex N hz
  have hx : x ∈ gapAmbientDomain N := PhysicalEnergy.simplex_subset_ambient N _ hy
  have hs₀ : ContDiffAt ℝ 2 W₀ x :=
    (hW₀.of_le (by simp)).contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hx)
  have hsP : ContDiffAt ℝ 2 P x := (internal_penalty_smooth θ ha b (hpos x hx)).of_le (by simp)
  have he : fderiv ℝ (fderiv ℝ W) x u u = p.val.1 *
      (fderiv ℝ (fderiv ℝ W₀) x u u + fderiv ℝ (fderiv ℝ P) x u u) := by
    rw [PhysicalCollision.internal_hessian_const_mul (hs₀.add hsP),
      PhysicalCollision.internal_hessian_add hs₀ hsP]
  have hweight : (N : ℝ)^(-p.val.2-2)*(∑ i, t i^2) ≤
      ∑ i, (1+z.val i)^(-p.val.2-2)*t i^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos (hz i)
      (PhysicalCollision.gap_le_mass N hz i) (by linarith [p.property.2.1])) (sq_nonneg _)
  have hh := hlow (fun i => 1+z.val i) hy u
  have hp := internal_penalty_nonneg θ ha b (hpos x hx) u
  have hc : 0 ≤ p.val.2*(p.val.2+1) :=
    mul_nonneg p.property.2.1.le (by linarith [p.property.2.1])
  have hh' := mul_le_mul_of_nonneg_left hweight hc
  have hfin : (p.val.2*(p.val.2+1))*(N : ℝ)^(-p.val.2-2)*(∑ i,t i^2) ≤
      fderiv ℝ (fderiv ℝ W₀) x u u + fderiv ℝ (fderiv ℝ P) x u u := by
    change _ ≤ fderiv ℝ (fderiv ℝ W₀) x u u at hh
    dsimp only [u] at hh
    nlinarith only [hh,hh',hp]
  have hw₂ : ContDiffAt ℝ 2 W x :=
    (hW.of_le (by simp)).contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hx)
  rw [show (∑ i, ∑ j, t i*hessianMatrix W x i j*t j) = fderiv ℝ (fderiv ℝ W) x u u from
    PhysicalEnergy.hessianMatrix_quadratic hw₂ u,he]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hfin p.property.1.le

/-- Analytic full-cycle conclusions of Proposition 4.10:
the tilted law, the smooth ambient physical potential, the closed
conservative intrinsic Neumann form, and unique tangent solutions for
all L² vector sources. The displayed energy bound holds at every `N≥2`.
No boundedness or exceptional-set assumption is imposed on a source. -/
theorem full_physical_wellposed (p : Parameters) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (θ : PhysicalCutoff) (h : ℝ) (b : Bool) :
    let ν := fullIntrinsicTiltedGapLaw p N θ h b
    let a := p.val.1*(p.val.2*(p.val.2+1))*(N : ℝ)^(-p.val.2-2)
    0 < tiltNormalizer p N N (le_refl _) θ h b ∧
      tiltNormalizer p N N (le_refl _) θ h b < ⊤ ∧ IsProbabilityMeasure ν ∧
    ∃ (W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ) (Q : ScalarFormData ν),
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = fullPhysicalPotentialValue p N hN θ h b y) ∧
      IsEuclideanGibbsPotential volume ν (intrinsicGapDomain N)
        (fun z => W (WithLp.toLp 2 (fun i => 1 + z.val i))) ∧
      IsNeumannRealization (intrinsicGapDomain N) Q ∧
      IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
      ∀ f : Fin (N : ℕ) → Lp ℝ 2 ν,
      let M := fun z : gapTangentSpace N => hessianMatrix W
        (WithLp.toLp 2 (fun i => 1 + z.val i))
      (∃! u : Fin (N : ℕ) → Q.1,
        WeightedWeakSolution Q M (zeroSumComponents _) f u) ∧
      ∀ u : Fin (N : ℕ) → Q.1,
        WeightedWeakSolution Q M (zeroSumComponents _) f u →
        ‖WithLp.toLp 2 (fun i => (u i).val)‖ ≤ a⁻¹*‖WithLp.toLp 2 f‖ := by
  classical
  intro ν a
  obtain ⟨hZ,hZ1⟩ := DefinitionSanity.tilt_normalizer_valid p N N (le_refl _) θ h b
  have hprob := DefinitionSanity.full_intrinsic_tilted_probability p N θ h b
  refine ⟨hZ,hZ1.trans_lt ENNReal.one_lt_top,hprob,?_⟩
  obtain ⟨W,hW,hval,hG,hlower⟩ := full_physical_matrix_lower p N hN θ h b
  have hU := AffineMetric.intrinsicGapDomain_isOpen N
  have hB := PhysicalCollision.intrinsicGapDomain_bounded N
  let Q := IntrinsicScalarCore.form hU hB hG
  have hQ := IntrinsicScalarCore.closed_dirichlet hU hB hG
  have ha : 0 < a := mul_pos (mul_pos p.property.1
    (mul_pos p.property.2.1 (by linarith [p.property.2.1])))
    (Real.rpow_pos_of_pos (by positivity) _)
  let M := fun z : gapTangentSpace N => hessianMatrix W
    (WithLp.toLp 2 (fun i => 1 + z.val i))
  have hMm : ∀ i j, Measurable (fun z => M z i j) := fun i j =>
    (DifferentiatedPoisson.measurable_hessian_entries (V := W) i j).comp
      (PhysicalCollision.intrinsic_chart_contDiff N).continuous.measurable
  have hHb : ∀ᵐ z ∂ν, (M z).PosSemidef := by
    filter_upwards [IntrinsicScalarCore.supported hU hG] with z hz
    have hx := PhysicalEnergy.simplex_subset_ambient N _
      (PhysicalCollision.intrinsic_chart_mem_simplex N hz)
    have hs := hW.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hx)
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    constructor
    · ext i j
      simp only [M,Matrix.conjTranspose_apply,star_trivial,Intrinsic.hessianMatrix_eq_second hs]
      exact hs.isSymmSndFDerivAt (by simp) _ _
    · intro t
      have hh := (mul_nonneg ha.le (Finset.sum_nonneg fun i _ => sq_nonneg (t i))).trans
        (hlower z hz t)
      simpa only [M,dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,
        Finset.mul_sum,mul_assoc] using hh
  have hlow : ∀ᵐ z ∂ν, ∀ t ∈ zeroSumComponents (Fin (N : ℕ)),
      a*(∑ i,t i^2) ≤ ∑ i,∑ j,t i*M z i j*t j :=
    (IntrinsicScalarCore.supported hU hG).mono fun z hz t _ => hlower z hz t
  refine ⟨W,Q,hW,hval,hG,IntrinsicScalarCore.realization hU hB hG,hQ,
    IntrinsicScalarCore.conservative hU hB hG,fun f => ?_⟩
  refine ⟨MatrixEnergy.weightedWeakSolution_existsUnique Q hQ M
    (zeroSumComponents _) hHb a ha hlow hMm f,?_⟩
  intro u hu
  have he := MatrixEnergy.weightedWeakSolution_unique Q hQ M
    (zeroSumComponents _) hHb a ha hlow hMm f u hu
  have hn := MatrixEnergy.solution_value_norm_le Q hQ M
    (zeroSumComponents _) hHb a ha hlow (WithLp.toLp 2 f)
  convert hn using 1
  apply congrArg norm
  apply PiLp.ext
  intro i
  rw [MatrixEnergy.values_apply,he]

/-- The complete small-volume branch of Proposition 4.10.
For `N=2,3` the energy estimate gives the cyclic decay profile even for
arbitrary L² sources. Its prefactor is independent of the cutoff and
penalty scale. No large-volume exceptional probability is needed. -/
theorem full_physical_decay_two_three (p : Parameters) :
    ∃ A : ℝ, 0 < A ∧ ∀ (θ : PhysicalCutoff) (h : ℝ)
      (N : ℕ+) (hN : 2 ≤ (N : ℕ)), (N : ℕ) ≤ 3 → ∀ b : Bool,
    let ν := fullIntrinsicTiltedGapLaw p N θ h b
    0 < tiltNormalizer p N N (le_refl _) θ h b ∧
      tiltNormalizer p N N (le_refl _) θ h b < ⊤ ∧ IsProbabilityMeasure ν ∧
    ∃ (W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ) (Q : ScalarFormData ν),
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = fullPhysicalPotentialValue p N hN θ h b y) ∧
      IsEuclideanGibbsPotential volume ν (intrinsicGapDomain N)
        (fun z => W (WithLp.toLp 2 (fun i => 1 + z.val i))) ∧
      IsNeumannRealization (intrinsicGapDomain N) Q ∧
      IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
      ∀ (i₀ : Fin (N : ℕ)) (χ : Lp ℝ 2 ν),
      let M := fun z : gapTangentSpace N => hessianMatrix W
        (WithLp.toLp 2 (fun i => 1 + z.val i))
      (∃! u : Fin (N : ℕ) → Q.1,
        WeightedWeakSolution Q M (zeroSumComponents _)
          (fun i => if i=i₀ then χ else 0) u) ∧
      ∀ u : Fin (N : ℕ) → Q.1,
        WeightedWeakSolution Q M (zeroSumComponents _)
          (fun i => if i=i₀ then χ else 0) u →
        ∀ j : Fin (N : ℕ), ‖(u j).val‖ ≤
          A*((1+(Riesz1.cyclicIndexDistance N j i₀ : ℝ))^(-p.val.2)+(N : ℝ)⁻¹)*‖χ‖ := by
  classical
  let a₃ := p.val.1*(p.val.2*(p.val.2+1))*(3 : ℝ)^(-p.val.2-2)
  have ha₃ : 0 < a₃ := mul_pos (mul_pos p.property.1
    (mul_pos p.property.2.1 (by linarith [p.property.2.1])))
    (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨3*a₃⁻¹,by positivity,?_⟩
  intro θ h N hN hN3 b ν
  obtain ⟨hZ,hZt,hprob,W,Q,hW,hval,hG,hreal,hQ,hcons,hsol⟩ :=
    full_physical_wellposed p N hN θ h b
  refine ⟨hZ,hZt,hprob,W,Q,hW,hval,hG,hreal,hQ,hcons,?_⟩
  intro i₀ χ M
  refine ⟨(hsol (fun i => if i=i₀ then χ else 0)).1,?_⟩
  intro u hu j
  have hn := (hsol (fun i => if i=i₀ then χ else 0)).2 u hu
  have hf : ‖WithLp.toLp 2 (fun i : Fin (N : ℕ) => if i=i₀ then χ else 0)‖ = ‖χ‖ := by
    convert PiLp.norm_single 2 (fun _ : Fin (N : ℕ) => Lp ℝ 2 ν) i₀ χ using 1
    congr 1
    apply PiLp.ext
    intro i
    simp only [PiLp.single_apply]
  rw [hf] at hn
  have hpow := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < N)
    (show (N : ℝ) ≤ 3 by exact_mod_cast hN3) (by linarith [p.property.2.1] : -p.val.2-2 ≤ 0)
  have ha : a₃ ≤ p.val.1*(p.val.2*(p.val.2+1))*(N : ℝ)^(-p.val.2-2) :=
    mul_le_mul_of_nonneg_left hpow (mul_nonneg p.property.1.le
      (mul_nonneg p.property.2.1.le (by linarith [p.property.2.1])))
  have hnorm : ‖(u j).val‖ ≤ a₃⁻¹*‖χ‖ := (PiLp.norm_apply_le
    (WithLp.toLp 2 (fun i => (u i).val)) j).trans (hn.trans
      (mul_le_mul_of_nonneg_right (inv_anti₀ ha₃ ha) (norm_nonneg _)))
  have hN0 : (0 : ℝ) < N := by positivity
  have hinv : (1/3 : ℝ) ≤ (N : ℝ)⁻¹ := by
    simpa only [one_div] using inv_anti₀ hN0 (show (N : ℝ) ≤ 3 by exact_mod_cast hN3)
  have hprofile : (1/3 : ℝ) ≤
      (1+(Riesz1.cyclicIndexDistance N j i₀ : ℝ))^(-p.val.2)+(N : ℝ)⁻¹ :=
    hinv.trans (le_add_of_nonneg_left (Real.rpow_nonneg (by positivity) _))
  apply hnorm.trans
  have hp := mul_le_mul_of_nonneg_left hprofile (show 0 ≤ 3*a₃⁻¹ by positivity)
  have he : a₃⁻¹ ≤ 3*a₃⁻¹*
      ((1+(Riesz1.cyclicIndexDistance N j i₀ : ℝ))^(-p.val.2)+(N : ℝ)⁻¹) := by
    nlinarith only [hp]
  exact mul_le_mul_of_nonneg_right he (norm_nonneg _)

/-- The full-cycle auxiliary matrix of the proof of Proposition 4.10: the physical interaction plus penalty Hessian on
`fullGoodEvent`, and the prescribed identity on its complement. This is
an auxiliary comparison field, with the prescribed exceptional
coefficients, on the entire particle configuration carrier. -/
def fullFrozenMatrix (p : Parameters) (N : ℕ+) (θ : PhysicalCutoff)
    (h : ℝ) (b : Bool) (D : ℝ) (X : Riesz1.Configuration N) :
    Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ := by
  classical
  let F := fun y : EuclideanSpace ℝ (Fin (N : ℕ)) =>
    ∑ i, (θ.val (((N : ℝ)^h)⁻¹*y i) + if b then θ.val (((N : ℝ)^h)⁻¹*(y i)⁻¹) else 0)
  exact if X ∈ ExceptionalEvent.fullGoodEvent p N h D then
    Matrix.of (fun i j => GoodBlocks.particleHessian p N i j X) + hessianMatrix F (WithLp.toLp 2 (gapVector X))
    else 1

/-- Measurability of the existing full-cycle good event, needed for the
auxiliary field in Proposition 4.10. -/
theorem measurableSet_fullGoodEvent (p : Parameters) (N : ℕ+) (h D : ℝ) :
    MeasurableSet (ExceptionalEvent.fullGoodEvent p N h D) := by
  have hall {ι : Type} [Countable ι] {P : ι → Riesz1.Configuration N → Prop}
      (hm : ∀ i, MeasurableSet {X | P i X}) : MeasurableSet {X | ∀ i, P i X} := by
    simpa only [ofPred_forall] using MeasurableSet.iInter hm
  unfold ExceptionalEvent.fullGoodEvent
  simp only [ofPred_and]
  refine (hall fun i => (measurableSet_le measurable_const (DefinitionSanity.gap_measurable _)).inter
    (measurableSet_le (DefinitionSanity.gap_measurable _) measurable_const)).inter
    ((hall fun (a : Fin (N : ℕ)) => hall fun (r : Fin ((N : ℕ)/2)) => ?_).inter
      (hall fun (i : Fin (N : ℕ)) => hall fun (j : Fin (N : ℕ)) => ?_))
  · exact measurableSet_le
      (((Finset.measurable_sum _ fun i _ => DefinitionSanity.gap_measurable _).sub measurable_const).abs)
      measurable_const
  · exact measurableSet_le (GoodBlocks.measurable_particleHessian p N _ _) measurable_const

/-- The full-cycle auxiliary matrix is measurable and symmetric everywhere,
for both penalties (Proposition 4.10). -/
theorem fullFrozenMatrix_measurable_symmetric (p : Parameters) (N : ℕ+)
    (θ : PhysicalCutoff) (h : ℝ) (b : Bool) (D : ℝ) :
    (∀ i j, Measurable (fun X => fullFrozenMatrix p N θ h b D X i j)) ∧
    (∀ X i j, fullFrozenMatrix p N θ h b D X i j = fullFrozenMatrix p N θ h b D X j i) := by
  classical
  let F := fun y : EuclideanSpace ℝ (Fin (N : ℕ)) =>
    ∑ i, (θ.val (((N : ℝ)^h)⁻¹*y i) + if b then θ.val (((N : ℝ)^h)⁻¹*(y i)⁻¹) else 0)
  have hy : Measurable (fun X : Riesz1.Configuration N => WithLp.toLp 2 (gapVector X)) :=
    (WithLp.measurable_toLp 2 _).comp (Riesz1.measurable_gapVector N)
  constructor
  · intro i j
    have he : (fun X => fullFrozenMatrix p N θ h b D X i j) =
        fun X => if X ∈ ExceptionalEvent.fullGoodEvent p N h D then
          GoodBlocks.particleHessian p N i j X + hessianMatrix F (WithLp.toLp 2 (gapVector X)) i j
          else (1 : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ) i j := by
      funext X
      by_cases hx : X ∈ ExceptionalEvent.fullGoodEvent p N h D
      · simp only [fullFrozenMatrix,ite_eq_left hx,Matrix.add_apply,Matrix.of_apply,F]
      · simp only [fullFrozenMatrix,ite_eq_right hx]
    rw [he]
    exact Measurable.ite (measurableSet_fullGoodEvent p N h D)
      ((GoodBlocks.measurable_particleHessian p N i j).add
        ((DifferentiatedPoisson.measurable_hessian_entries (V := F) i j).comp hy))
      measurable_const

  · intro X i j
    have hF := PhysicalComparison.penalty_contDiffAt (N : ℕ) θ
      (inv_pos.mpr (Real.rpow_pos_of_pos (show (0 : ℝ) < N by exact_mod_cast N.pos) h)) b
      (WithLp.toLp 2 (gapVector X)) (fun i => Riesz1.gap_pos X i.val)
    change (if X ∈ ExceptionalEvent.fullGoodEvent p N h D then
      Matrix.of (fun i j => GoodBlocks.particleHessian p N i j X) + hessianMatrix F
        (WithLp.toLp 2 (gapVector X)) else 1) i j =
      (if X ∈ ExceptionalEvent.fullGoodEvent p N h D then
      Matrix.of (fun i j => GoodBlocks.particleHessian p N i j X) + hessianMatrix F
        (WithLp.toLp 2 (gapVector X)) else 1) j i
    by_cases hx : X ∈ ExceptionalEvent.fullGoodEvent p N h D
    · simp only [ite_eq_left hx,Matrix.add_apply,Matrix.of_apply]
      rw [GoodBlocks.particleHessian_symmetric p N i j X,
        PhysicalComparison.hessianMatrix_symm hF i j]
    · rw [ite_eq_right hx]
      exact (Matrix.isSymm_one.apply i j).symm

/-- The full-cycle auxiliary physical matrix is uniformly coercive with a
polynomial loss on the whole ambient component space, including `N=2`.
This is the deterministic lower bound used in Proposition 4.10, before the zero-sum compression. -/
theorem fullFrozenMatrix_lower (p : Parameters) (hs : 1 < p.val.2)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (θ : PhysicalCutoff)
    (h : ℝ) (hh : 0 < h) (b : Bool) (D : ℝ)
    (X : Riesz1.Configuration N) (t : Fin (N : ℕ) → ℝ) :
    (N : ℝ)^(-(p.val.2+2)*h)*(∑ i,t i^2) ≤
      ∑ i,∑ j,t i*fullFrozenMatrix p N θ h b D X i j*t j := by
  classical
  let F := fun y : EuclideanSpace ℝ (Fin (N : ℕ)) =>
    ∑ i, (θ.val (((N : ℝ)^h)⁻¹*y i) + if b then θ.val (((N : ℝ)^h)⁻¹*(y i)⁻¹) else 0)
  let y := WithLp.toLp 2 (gapVector X)
  let u := WithLp.toLp 2 t
  have hy := GapChart.gapVector_mem_gapAmbientDomain X
  have hN0 : (0 : ℝ) < N := by positivity
  by_cases hx : X ∈ ExceptionalEvent.fullGoodEvent p N h D
  · obtain ⟨W,hW,hw,_,_,hlow,_⟩ := (PhysicalEnergy.restriction_and_derivatives p N hN).2.2
    obtain ⟨V,hV,hv,hjet⟩ := GoodBlocks.particleHessian_eq_matrix p N
    have he : W =ᶠ[𝓝 y] V := by
      filter_upwards [(PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hy] with z hz
      exact (hw ⟨z,hz⟩).trans (hv ⟨z,hz⟩).symm
    have hbase := hlow (gapVector X) (show gapVector X ∈ Riesz1.gapSimplex N from ⟨fun i => Riesz1.gap_pos X i.val, DefinitionSanity.actual_gap_sum X⟩) u
    rw [he.fderiv.fderiv_eq,← PhysicalEnergy.hessianMatrix_quadratic
      ((hV.of_le (by simp)).contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hy)) u] at hbase
    simp only [u,hjet] at hbase
    have hweights : (N : ℝ)^(-(p.val.2+2)*h)*(∑ i,t i^2) ≤
        ∑ i,gap X i.val^(-p.val.2-2)*t i^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      have hupper : gap X i.val ≤ (N : ℝ)^h := (hx.1 i).2
      have hp := Real.rpow_le_rpow_of_nonpos (Riesz1.gap_pos X i.val) hupper
        (show -p.val.2-2 ≤ 0 by linarith)
      rw [← Real.rpow_mul hN0.le] at hp
      have hmul : h*(-p.val.2-2) = -(p.val.2+2)*h := by ring
      rw [hmul] at hp
      exact mul_le_mul_of_nonneg_right hp (sq_nonneg _)
    have hc : 1 ≤ p.val.2*(p.val.2+1) := by nlinarith
    have hsum : 0 ≤ ∑ i,gap X i.val^(-p.val.2-2)*t i^2 := by
      exact Finset.sum_nonneg fun i _ => mul_nonneg (Real.rpow_nonneg (Riesz1.gap_pos X i.val).le _) (sq_nonneg _)
    have hbase' := hweights.trans ((le_mul_of_one_le_left hsum hc).trans hbase)
    have hF := PhysicalComparison.penalty_contDiffAt (N : ℕ) θ
      (inv_pos.mpr (Real.rpow_pos_of_pos hN0 h)) b y (fun i => Riesz1.gap_pos X i.val)
    have hp : 0 ≤ ∑ i,∑ j,t i*hessianMatrix F y i j*t j := by
      rw [PhysicalEnergy.hessianMatrix_quadratic hF u]
      exact internal_penalty_nonneg θ (inv_pos.mpr (Real.rpow_pos_of_pos hN0 h)) b
        (fun i => Riesz1.gap_pos X i.val) u
    change _ ≤ ∑ i,∑ j,t i*(if X ∈ ExceptionalEvent.fullGoodEvent p N h D then
      Matrix.of (fun i j => GoodBlocks.particleHessian p N i j X) + hessianMatrix F y else 1) i j*t j
    rw [ite_eq_left hx]
    simp only [Matrix.add_apply,mul_add,add_mul,Finset.sum_add_distrib]
    exact hbase'.trans (le_add_of_nonneg_right hp)
  · have hpow : (N : ℝ)^(-(p.val.2+2)*h) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast N.pos)
        (by nlinarith [p.property.2.1])
    simpa only [fullFrozenMatrix,ite_eq_right hx,Matrix.one_apply,mul_ite,ite_mul,
      mul_one,mul_zero,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte,← pow_two] using
      mul_le_of_le_one_left (Finset.sum_nonneg (s := Finset.univ) fun i _ => sq_nonneg (t i)) hpow

/-- Summable cyclic entry bounds for the full auxiliary physical Hessian
in Proposition 4.10. Its diagonal penalty costs only
`N^(4h)`. Off-diagonal entries retain the physical cyclic profile. -/
theorem fullFrozenMatrix_entry_bound (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Parameters) (N : ℕ+) (h : ℝ), 0 < h →
      ∀ (b : Bool) (D : ℝ), 1 ≤ D → ∀ (X : Riesz1.Configuration N) (i j : Fin (N : ℕ)),
      |fullFrozenMatrix p N θ h b D X i j| ≤
        (D+C*(N : ℝ)^(4*h))*(1+(Riesz1.cyclicIndexDistance N i j : ℝ))^(-p.val.2) := by
  classical
  obtain ⟨C,hC,hdiag⟩ := ExceptionalEvent.internal_penalty_diagonal θ
  refine ⟨2*C,by positivity,?_⟩
  intro p N h hh b D hD X i j
  let F := fun y : EuclideanSpace ℝ (Fin (N : ℕ)) =>
    ∑ i, (θ.val (((N : ℝ)^h)⁻¹*y i) + if b then θ.val (((N : ℝ)^h)⁻¹*(y i)⁻¹) else 0)
  let y := WithLp.toLp 2 (gapVector X)
  have hN0 : (0 : ℝ) < N := by positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hR : 1 ≤ (N : ℝ)^h := Real.one_le_rpow hN1 hh.le
  have ha : 0 < ((N : ℝ)^h)⁻¹ := inv_pos.mpr (Real.rpow_pos_of_pos hN0 h)
  have hFx := PhysicalComparison.penalty_contDiffAt (N : ℕ) θ ha b y
    (fun i => Riesz1.gap_pos X i.val)
  by_cases hx : X ∈ ExceptionalEvent.fullGoodEvent p N h D
  · have hpen (i) : |hessianMatrix F y i i| ≤ 2*C*(N : ℝ)^(4*h) := by
      have hl : ((N : ℝ)^h)⁻¹ ≤ gap X i.val := by
        simpa only [Real.rpow_neg hN0.le] using (hx.1 i).1
      have hi : (gap X i.val)⁻¹ ≤ (N : ℝ)^h := by
        have ht := inv_anti₀ ha hl
        simpa only [inv_inv] using ht
      have h4 : (gap X i.val)⁻¹^4 ≤ (N : ℝ)^(4*h) := by
        have ht := pow_le_pow_left₀ (inv_nonneg.mpr (Riesz1.gap_pos X i.val).le) hi 4
        calc
          _ ≤ ((N : ℝ)^h)^4 := ht
          _ = (N : ℝ)^(4*h) := by
            rw [← Real.rpow_natCast,← Real.rpow_mul hN0.le]
            congr 1
            ring
      have hp : 1 ≤ (N : ℝ)^(4*h) := Real.one_le_rpow hN1 (by positivity)
      have hn : 0 ≤ hessianMatrix F y i i := by
        rw [PhysicalComparison.hessianMatrix_entry hFx]
        exact internal_penalty_nonneg θ ha b (fun i => Riesz1.gap_pos X i.val) _
      rw [abs_of_nonneg hn,PhysicalComparison.hessianMatrix_entry hFx]
      have hd := hdiag (N : ℕ) _ ha (inv_le_one_of_one_le₀ hR) b y
        (fun i => Riesz1.gap_pos X i.val) i
      change _ ≤ C*(1+(gap X i.val)⁻¹^4) at hd
      nlinarith only [hd,mul_le_mul_of_nonneg_left h4 hC.le,mul_le_mul_of_nonneg_left hp hC.le]
    change |(if X ∈ ExceptionalEvent.fullGoodEvent p N h D then
      Matrix.of (fun i j => GoodBlocks.particleHessian p N i j X) + hessianMatrix F y else 1) i j| ≤ _
    rw [ite_eq_left hx,Matrix.add_apply,Matrix.of_apply]
    have hI : |GoodBlocks.particleHessian p N i j X| ≤
        D*(1+(Riesz1.cyclicIndexDistance N i j : ℝ))^(-p.val.2) := by
      rw [abs_of_nonneg (GoodBlocks.particleHessian_nonneg p N i j X)]
      exact hx.2.2 i j
    apply (abs_add_le _ _).trans
    by_cases hij : i=j
    · subst j
      simpa only [cyclicIndexDistance_self,Nat.cast_zero,add_zero,Real.one_rpow,mul_one] using
        add_le_add hI (hpen i)
    · rw [PhysicalComparison.penalty_hessian_off_diagonal (N : ℕ) θ ha b y
        (fun i => Riesz1.gap_pos X i.val) i j hij,abs_zero,add_zero]
      exact hI.trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (by positivity)) (Real.rpow_nonneg (by positivity) _))
  · change |(if X ∈ ExceptionalEvent.fullGoodEvent p N h D then
      Matrix.of (fun i j => GoodBlocks.particleHessian p N i j X) + hessianMatrix F y else 1) i j| ≤ _
    rw [ite_eq_right hx,Matrix.one_apply]
    by_cases hij : i=j
    · subst j
      simp only [↓reduceIte,abs_one,cyclicIndexDistance_self,Nat.cast_zero,
        add_zero,Real.one_rpow,mul_one]
      exact hD.trans (le_add_of_nonneg_right (by positivity))
    · simp only [hij,↓reduceIte,abs_zero]
      positivity

/-- Internal full-cycle auxiliary estimate in Proposition 4.10.
The complete cyclic profile and the `N⁻¹` multiplier bound follow from the
multiplier theorem on every common scalar form. The measurable map
allows any realization of the configuration coefficients on that scalar base. -/
theorem internal_full_auxiliary_decay (p : Parameters) (hs : 1 < p.val.2)
    (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ (θ : PhysicalCutoff) (A : ℝ), 1 ≤ A →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ (h : ℝ), 0 < h → ∀ (N : ℕ+), 2 ≤ (N : ℕ) →
      ∀ (b : Bool) (α : Type*) [MeasurableSpace α]
        (τ : α → Riesz1.Configuration N), Measurable τ →
      ∀ (ν : Measure α) [IsProbabilityMeasure ν] (Q : ScalarFormData ν),
        IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
      ∀ (i₀ : Fin (N : ℕ)) (χ : Lp ℝ 2 ν),
      let M := fun x => p.val.1 • fullFrozenMatrix p N θ h b (A*(N : ℝ)^(κ*h)) (τ x)
      let f := fun i => if i=i₀ then χ else 0
      (∃! u : Fin (N : ℕ) → Q.1,
        WeightedWeakSolution Q M (zeroSumComponents _) f u) ∧
      ∀ u : Fin (N : ℕ) → Q.1,
        WeightedWeakSolution Q M (zeroSumComponents _) f u →
        ∃ l : Lp ℝ 2 ν,
          (∀ᵐ x ∂ν, l x = gapMultiplierField N Q M f u x) ∧
          ‖l‖ ≤ C*(N : ℝ)^(r*h)*(N : ℝ)⁻¹*‖χ‖ ∧
          ∀ j : Fin (N : ℕ), ‖(u j).val‖ ≤ C*(N : ℝ)^(r*h)*
            ((1+(Riesz1.cyclicIndexDistance N j i₀ : ℝ))^(-p.val.2)+(N : ℝ)⁻¹)*‖χ‖ := by
  classical
  obtain ⟨r,C₀,hr,hC₀,hdec⟩ := MultiplierControl.control_lambda_uniform p.val.2 p.val.1 hs p.property.1
  let k := κ+p.val.2+6
  have hk : 0 ≤ k := by dsimp [k]; linarith
  refine ⟨r*k,mul_nonneg hr hk,fun θ A hA => ?_⟩
  obtain ⟨Cθ,hCθ,hentry⟩ := fullFrozenMatrix_entry_bound θ
  let E := A+Cθ+1
  have hE : 1 ≤ E := by dsimp [E]; linarith
  have hE0 : 0 < E := lt_of_lt_of_le zero_lt_one hE
  have hEr : 1 ≤ E^r := Real.one_le_rpow hE hr
  refine ⟨C₀*E^r,(by nlinarith only [hC₀,hEr,mul_nonneg (by linarith : 0 ≤ C₀-1) (by linarith : 0 ≤ E^r-1)]),fun h hh N hN b α _ τ hτ ν _ Q hQ hcons i₀ χ => ?_⟩
  let B := E*(N : ℝ)^(k*h)
  let H := fun x => fullFrozenMatrix p N θ h b (A*(N : ℝ)^(κ*h)) (τ x)
  have hN0 : (0 : ℝ) < N := by positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hpow : 1 ≤ (N : ℝ)^(k*h) := Real.one_le_rpow hN1 (mul_nonneg hk hh.le)
  have hB : 1 ≤ B := by
    dsimp only [B]
    nlinarith only [hE,hpow,mul_nonneg (by linarith : 0 ≤ E-1) (by linarith : 0 ≤ (N : ℝ)^(k*h)-1)]
  have hD : 1 ≤ A*(N : ℝ)^(κ*h) := by
    have hp := Real.one_le_rpow hN1 (mul_nonneg hκ hh.le)
    nlinarith only [hA,hp,mul_nonneg (by linarith : 0 ≤ A-1) (by linarith : 0 ≤ (N : ℝ)^(κ*h)-1)]
  have hpm (t : ℝ) (ht : t ≤ k) : (N : ℝ)^(t*h) ≤ (N : ℝ)^(k*h) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (mul_le_mul_of_nonneg_right ht hh.le)
  have hκk : κ ≤ k := by dsimp [k]; linarith
  have h4k : 4 ≤ k := by dsimp [k]; linarith
  have hsk : p.val.2+2 ≤ k := by dsimp [k]; linarith
  have hBb : (N : ℝ)^((p.val.2+2)*h) ≤ B := (hpm _ hsk).trans
    (le_mul_of_one_le_left (by positivity) hE)
  have hBi : B⁻¹ ≤ (N : ℝ)^(-(p.val.2+2)*h) := by
    have hi := inv_anti₀ (Real.rpow_pos_of_pos hN0 ((p.val.2+2)*h)) hBb
    simpa only [← Real.rpow_neg hN0.le,neg_mul] using hi
  have hm := fullFrozenMatrix_measurable_symmetric p N θ h b (A*(N : ℝ)^(κ*h))
  have hHm : ∀ i j, Measurable (fun x => H x i j) := fun i j => (hm.1 i j).comp hτ
  have hbounds : ∀ᵐ x ∂ν, (∀ i j,H x i j=H x j i) ∧
      (∀ t : Fin (N : ℕ) → ℝ, B⁻¹*(∑ i,t i^2) ≤ ∑ i,∑ j,t i*H x i j*t j) ∧
      ∀ i j,|H x i j| ≤ B*(1+(Riesz1.cyclicIndexDistance N i j : ℝ))^(-p.val.2) := by
    apply ae_of_all
    intro x
    refine ⟨hm.2 (τ x),fun t => ?_,fun i j => ?_⟩
    · exact (mul_le_mul_of_nonneg_right hBi (Finset.sum_nonneg fun i _ => sq_nonneg (t i))).trans
        (fullFrozenMatrix_lower p hs N hN θ h hh b _ (τ x) t)
    · apply (hentry p N h hh b _ hD (τ x) i j).trans
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
      have h₁ := mul_le_mul_of_nonneg_left (hpm κ hκk) (show 0 ≤ A by linarith)
      have h₂ := mul_le_mul_of_nonneg_left (hpm 4 h4k) hCθ.le
      change A*(N : ℝ)^(κ*h)+Cθ*(N : ℝ)^(4*h) ≤ E*(N : ℝ)^(k*h)
      dsimp only [E]
      nlinarith only [h₁,h₂,Real.rpow_nonneg hN0.le (k*h)]
  let g : ComponentGeometry (Fin (N : ℕ)) := Sum.inr ⟨N,Function.Embedding.refl _⟩
  have hex := hdec α ν N Q hQ hcons g B hB H hHm hbounds i₀ χ
  have he : C₀*B^r = C₀*E^r*(N : ℝ)^((r*k)*h) := by
    dsimp only [B]
    rw [Real.mul_rpow hE0.le (Real.rpow_nonneg hN0.le _),← Real.rpow_mul hN0.le]
    rw [show k*h*r = (r*k)*h by ring]
    ring
  refine ⟨hex.1,fun u hu => ?_⟩
  obtain ⟨l,hl,hln,hcomp⟩ := hex.2 u hu
  rw [he] at hln hcomp
  exact ⟨l,hl,hln,hcomp⟩

/-- Internal identification in Proposition 4.10: on the
existing full good event the auxiliary field is exactly the ambient
physical Hessian, with temperature included. Agreement of the potential
on all of the open ambient domain fixes every normal derivative. -/
theorem internal_fullFrozenMatrix_eq_physical (p : Parameters) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (θ : PhysicalCutoff) (h : ℝ) (b : Bool) (D : ℝ)
    (W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ)
    (hW : ContDiffOn ℝ ∞ W (gapAmbientDomain N))
    (hval : ∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
      W y.val = fullPhysicalPotentialValue p N hN θ h b y)
    (X : Riesz1.Configuration N) (hX : X ∈ ExceptionalEvent.fullGoodEvent p N h D) :
    hessianMatrix W (WithLp.toLp 2 (gapVector X)) = p.val.1 • fullFrozenMatrix p N θ h b D X := by
  classical
  let F := fun y : EuclideanSpace ℝ (Fin (N : ℕ)) =>
    ∑ i, (θ.val (((N : ℝ)^h)⁻¹*y i) + if b then θ.val (((N : ℝ)^h)⁻¹*(y i)⁻¹) else 0)
  obtain ⟨V,hV,hv,hjet⟩ := GoodBlocks.particleHessian_eq_second p N
  have hx := GapChart.gapVector_mem_gapAmbientDomain X
  have he : W =ᶠ[𝓝 (WithLp.toLp 2 (gapVector X))] (fun y => p.val.1*(V y+F y)) := by
    filter_upwards [(PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hx] with y hy
    exact (hval ⟨y,hy⟩).trans
      (ExceptionalEvent.internal_full_physical_realization p N hN θ h b V hv ⟨y,hy⟩).symm
  have hsW : ContDiffAt ℝ 2 W (WithLp.toLp 2 (gapVector X)) := (hW.of_le (by simp)).contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hx)
  have hsV : ContDiffAt ℝ 2 V (WithLp.toLp 2 (gapVector X)) := (hV.of_le (by simp)).contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hx)
  have hsF := PhysicalComparison.penalty_contDiffAt (N : ℕ) θ
    (inv_pos.mpr (Real.rpow_pos_of_pos (show (0 : ℝ) < N by positivity) h)) b
    (WithLp.toLp 2 (gapVector X)) (fun i => Riesz1.gap_pos X i.val)
  ext i j
  rw [PhysicalComparison.hessianMatrix_entry hsW,he.fderiv.fderiv_eq,
    PhysicalCollision.internal_hessian_const_mul (hsV.add hsF),
    PhysicalCollision.internal_hessian_add hsV hsF,hjet]
  change _ = p.val.1*(fullFrozenMatrix p N θ h b D X i j)
  simp only [fullFrozenMatrix,ite_eq_left hX,Matrix.add_apply,Matrix.of_apply]
  rw [GoodBlocks.particleHessian_symmetric p N j i X,
    ← PhysicalComparison.hessianMatrix_entry hsF]

/-- Internal fixed-tangent maximum estimate for the full auxiliary field
in Proposition 4.10. The same scalar form and every fixed
component constraint are allowed. This applies the radial maximum
principle directly, without estimating a normal multiplier. -/
theorem internal_full_auxiliary_maximum (p : Parameters) (hs : 1 < p.val.2)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (θ : PhysicalCutoff)
    (h : ℝ) (hh : 0 < h) (b : Bool) (D : ℝ)
    {α : Type*} [MeasurableSpace α] (τ : α → Riesz1.Configuration N) (hτ : Measurable τ)
    (ν : Measure α) (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (S : Submodule ℝ (Fin (N : ℕ) → ℝ)) (f : Fin (N : ℕ) → Lp ℝ 2 ν)
    (u : Fin (N : ℕ) → Q.1)
    (hu : WeightedWeakSolution Q (fun x => p.val.1 • fullFrozenMatrix p N θ h b D (τ x)) S f u) :
    eLpNorm (fun x => WithLp.toLp 2 (fun i => (u i).val x)) ∞ ν ≤
      ENNReal.ofReal ((p.val.1*(N : ℝ)^(-(p.val.2+2)*h))⁻¹)*
        eLpNorm (fun x => WithLp.toLp 2 (fun i => f i x)) ∞ ν := by
  have hm := fullFrozenMatrix_measurable_symmetric p N θ h b D
  let M := fun x => fullFrozenMatrix p N θ h b D (τ x)
  have hMm : ∀ i j, Measurable (fun x => M x i j) := fun i j => (hm.1 i j).comp hτ
  have hlow : ∀ᵐ x ∂ν, ∀ t : Fin (N : ℕ) → ℝ,
      (N : ℝ)^(-(p.val.2+2)*h)*(∑ i,t i^2) ≤ ∑ i,∑ j,t i*M x i j*t j :=
    ae_of_all _ fun x => fullFrozenMatrix_lower p hs N hN θ h hh b D (τ x)
  have hl := AbstractEnergy.scaled_lower p.val.1 ((N : ℝ)^(-(p.val.2+2)*h))
    p.property.1.le M hlow ⊤
  apply AbstractEnergy.weakSolution_eLpNorm_top_le Q hQ (fun x => p.val.1 • M x)
    (AbstractEnergy.scaled_measurable p.val.1 M hMm) _
    (mul_pos p.property.1 (Real.rpow_pos_of_pos (by positivity) _)) _ S f u hu
  filter_upwards [hl] with x hx
  refine ⟨fun i j => ?_,fun t => hx t (Submodule.mem_top)⟩
  simp only [Matrix.smul_apply,smul_eq_mul,hm.2 (τ x) i j,M]

end Riesz2.DecayShort.PhysicalDecay
