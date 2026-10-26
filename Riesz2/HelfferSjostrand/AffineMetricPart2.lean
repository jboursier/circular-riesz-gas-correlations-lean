/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.AffineMetric
public import Riesz2.ToMathlib.AffineMetricTransport
public import Riesz2.ToMathlib.AffineCollisionCriterion
public import Riesz2.ToMathlib.InfDistFrontier
public import Riesz2.Frozen.IntrinsicGapLaw
public import Riesz2.Frozen.IsEuclideanGibbsPotential
public import Riesz1.HelfferSjostrand.RieszAdmissibleBounds
public import Riesz1.HelfferSjostrand.BoundaryCoreAnchoredGeometry
public import Riesz2.ToMathlib.AffineFibreDisintegration
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Intrinsic derivatives and collision transport

Continuation of Subsection 3.2 and Lemma A.1, using the pair
potential and the affine equivalence constructed in `AffineMetric`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Finset
open scoped ENNReal Topology RealInnerProductSpace

namespace Riesz2.AffineMetric

variable {N : ℕ+}

local notation "W(" χ ")" =>
  (fun y : gapTangentSpace _ => pairAmbientGapPotential χ
    (WithLp.toLp 2 (fun i => 1 + (Subtype.val y) i)))
local notation "H(" χ ")" => (fun z : gapTangentSpace _ => particlePairEnergy χ (Subtype.val z))

/-- See Subsection 3.2 of the paper: the inverse affine formula for the potential,
valid on the entire intrinsic carrier. -/
theorem pairPotential_inverse (χ : ParticlePairData N) (y : gapTangentSpace N) :
    W(χ) y = H(χ) ((gapLinearEquiv N).symm (y - gapOffset N)) := by
  have he : intrinsicParticleGapMap N ((gapLinearEquiv N).symm (y - gapOffset N)) = y := by
    rw [intrinsicParticleGapMap_eq, ContinuousLinearEquiv.apply_symm_apply, sub_add_cancel]
  calc
    W(χ) y = W(χ) (intrinsicParticleGapMap N ((gapLinearEquiv N).symm (y - gapOffset N))) :=
      congrArg W(χ) he.symm
    _ = _ := pairPotential_intrinsicParticleGapMap χ _

/-- See Subsection 3.2 of the paper: smoothness of the particle potential on the orthogonal chamber. -/
theorem contDiffAt_intrinsicParticlePotential {hN : 2 ≤ (N : ℕ)}
    {χ : ParticlePairData N} {c : ℝ} (h : AdmissibleParticlePairs hN χ c)
    {z : gapTangentSpace N} (hz : z.val ∈ particleChamber N) :
    ContDiffAt ℝ (⊤ : ℕ∞) H(χ) z := by
  have hH := (Riesz1.hsPairExpression_contDiffOn (libraryPairs h)).contDiffAt
    ((Riesz1.isOpen_hsChamber N).mem_nhds hz)
  rw [libraryPairs_energy] at hH
  exact hH.comp z (gapTangentSpace N).subtypeL.contDiff.contDiffAt

/-- See Subsection 3.2 of the paper: smoothness in the isometric gap chart. -/
theorem contDiffAt_intrinsicGapPotential {hN : 2 ≤ (N : ℕ)}
    {χ : ParticlePairData N} {c : ℝ} (h : AdmissibleParticlePairs hN χ c)
    {y : gapTangentSpace N} (hy : y ∈ intrinsicGapDomain N) :
    ContDiffAt ℝ (⊤ : ℕ∞) W(χ) y := by
  let z := (gapLinearEquiv N).symm (y - gapOffset N)
  have hzT : intrinsicParticleGapMap N z = y := by
    rw [intrinsicParticleGapMap_eq, ContinuousLinearEquiv.apply_symm_apply, sub_add_cancel]
  have hz : z.val ∈ particleChamber N :=
    (intrinsicParticleGapMap_mem_iff N z).mp (hzT.symm ▸ hy)
  have hH := contDiffAt_intrinsicParticlePotential h hz
  have hi : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : gapTangentSpace N => (gapLinearEquiv N).symm (y - gapOffset N)) :=
    (gapLinearEquiv N).symm.contDiff.comp (contDiff_id.sub contDiff_const)
  simpa only [Function.comp_def, ← pairPotential_inverse] using hH.comp y hi.contDiffAt

/-- See Subsection 3.2 of the paper: the differential transforms by the cyclic difference map. -/
theorem fderiv_intrinsicParticlePotential {hN : 2 ≤ (N : ℕ)}
    {χ : ParticlePairData N} {c : ℝ} (h : AdmissibleParticlePairs hN χ c)
    {z : gapTangentSpace N} (hz : z.val ∈ particleChamber N) :
    fderiv ℝ H(χ) z = (fderiv ℝ W(χ) (intrinsicParticleGapMap N z)).comp
      (gapLinearEquiv N).toContinuousLinearMap := by
  have hw := (contDiffAt_intrinsicGapPotential h
    ((intrinsicParticleGapMap_mem_iff N z).mpr hz)).differentiableAt (by simp)
  simpa only [Function.comp_def, pairPotential_intrinsicParticleGapMap] using
    (hw.hasFDerivAt.comp z (hasFDerivAt_intrinsicParticleGapMap N z)).fderiv

/-- See Subsection 3.2 of the paper: `∇H = Bᵀ ∇W` in the orthogonal quotient. -/
theorem gradient_intrinsicParticlePotential {hN : 2 ≤ (N : ℕ)}
    {χ : ParticlePairData N} {c : ℝ} (h : AdmissibleParticlePairs hN χ c)
    {z : gapTangentSpace N} (hz : z.val ∈ particleChamber N) :
    gradient H(χ) z = (gapLinearEquiv N).toContinuousLinearMap.adjoint
      (gradient W(χ) (intrinsicParticleGapMap N z)) := by
  apply ext_inner_right ℝ
  intro u
  rw [inner_gradient_left, ContinuousLinearMap.adjoint_inner_left,
    inner_gradient_left, fderiv_intrinsicParticlePotential h hz]
  rfl

/-- See Subsection 3.2 of the paper: the Hessian transforms by bilinear pullback. -/
theorem hessian_intrinsicParticlePotential {hN : 2 ≤ (N : ℕ)}
    {χ : ParticlePairData N} {c : ℝ} (h : AdmissibleParticlePairs hN χ c)
    {z : gapTangentSpace N} (hz : z.val ∈ particleChamber N)
    (u v : gapTangentSpace N) :
    fderiv ℝ (fderiv ℝ H(χ)) z u v =
      fderiv ℝ (fderiv ℝ W(χ)) (intrinsicParticleGapMap N z)
        (gapLinearEquiv N u) (gapLinearEquiv N v) := by
  have hw := (contDiffAt_intrinsicGapPotential h
    ((intrinsicParticleGapMap_mem_iff N z).mpr hz)).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ (⊤ : ℕ∞))
  rw [intrinsicParticleGapMap_eq] at hw ⊢
  have hf : (fun z => W(χ) (gapLinearEquiv N z + gapOffset N)) = H(χ) := by
    funext z
    rw [← intrinsicParticleGapMap_eq]
    exact pairPotential_intrinsicParticleGapMap χ z
  have hr := AffineMetricTransport.hessian_comp_affine
    (gapLinearEquiv N).toContinuousLinearMap (gapOffset N) hw u v
  change fderiv ℝ (fderiv ℝ (fun z => W(χ) (gapLinearEquiv N z + gapOffset N))) z u v = _ at hr
  rw [hf] at hr
  exact hr

/-- Restricting the particle potential to the tangent space restricts its Hessian. -/
theorem hessian_restrict_particlePotential {hN : 2 ≤ (N : ℕ)}
    {χ : ParticlePairData N} {c : ℝ} (h : AdmissibleParticlePairs hN χ c)
    {z : gapTangentSpace N} (hz : z.val ∈ particleChamber N)
    (u v : gapTangentSpace N) :
    fderiv ℝ (fderiv ℝ H(χ)) z u v =
      fderiv ℝ (fderiv ℝ (particlePairEnergy χ)) z.val u.val v.val := by
  have hh := (Riesz1.hsPairExpression_contDiffOn (libraryPairs h)).contDiffAt
    ((Riesz1.isOpen_hsChamber N).mem_nhds hz)
  rw [libraryPairs_energy] at hh
  simpa only [Submodule.subtypeL_apply, add_zero] using AffineMetricTransport.hessian_comp_affine
    (gapTangentSpace N).subtypeL 0
      (by simpa only [Submodule.subtypeL_apply, add_zero] using (hh.of_le
        (by norm_num : (2 : WithTop ℕ∞) ≤ (⊤ : ℕ∞)))) u v

/-- See Subsection 3.2 of the paper: the intrinsic Hessian has curvature at least `c/(2N)`. -/
theorem intrinsicGapPotential_curvature {hN : 2 ≤ (N : ℕ)}
    {χ : ParticlePairData N} {c : ℝ} (hc : 0 < c) (h : AdmissibleParticlePairs hN χ c)
    {y : gapTangentSpace N} (hy : y ∈ intrinsicGapDomain N) (u : gapTangentSpace N) :
    c / (2 * (N : ℝ)) * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ W(χ)) y u u := by
  let z := (gapLinearEquiv N).symm (y - gapOffset N)
  let v := (gapLinearEquiv N).symm u
  have hzT : intrinsicParticleGapMap N z = y := by
    rw [intrinsicParticleGapMap_eq, ContinuousLinearEquiv.apply_symm_apply, sub_add_cancel]
  have hz := (intrinsicParticleGapMap_mem_iff N z).mp (hzT.symm ▸ hy)
  have hh := ((particle_hessian_normalization hN c hc χ h).2.1 z.val hz).2 v |>.2
  rw [← hessian_restrict_particlePotential h hz, hessian_intrinsicParticlePotential h hz,
    hzT, show gapLinearEquiv N v = u from (gapLinearEquiv N).apply_symm_apply u] at hh
  have hn := norm_gapLinearEquiv_le N v
  rw [show gapLinearEquiv N v = u from (gapLinearEquiv N).apply_symm_apply u] at hn
  have hsq := mul_self_le_mul_self (norm_nonneg u) hn
  have hNpos : 0 < (N : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsq (le_of_lt (div_pos hc (by positivity : 0 < 2 * (N : ℝ))))
  have he : c / (2 * (N : ℝ)) * (2 * (N : ℝ) * ‖v‖) ^ 2 =
      2 * (N : ℝ) * c * ‖v‖ ^ 2 := by field_simp
  rw [← pow_two, ← pow_two, he] at hmul
  exact hmul.trans hh

/-- The centering map is the library's orthogonal projection, on values. -/
theorem centeredGapChart_eq_orthComp (x : EuclideanSpace ℝ (Fin (N : ℕ))) :
    (centeredGapChart N x).val = (Riesz1.hsOrthComp N x).val := by
  rw [Riesz1.hsOrthComp_coe]
  ext i
  simp only [centeredGapChart, Riesz1.hsUnitVector, Riesz1.hsRotationVector,
    PiLp.sub_apply, PiLp.smul_apply, PiLp.inner_apply,
    smul_eq_mul, RCLike.inner_apply, conj_trivial, mul_one, ← Finset.mul_sum]
  have hs : Real.sqrt (N : ℕ) ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
  have hn : Real.sqrt (N : ℕ) ≠ 0 := (Riesz1.sqrt_N_pos N).ne'
  field_simp
  rw [hs]
  ring

/-- Orthogonal centering does not increase distances. -/
theorem dist_centeredGapChart_le (x y : EuclideanSpace ℝ (Fin (N : ℕ))) :
    dist (centeredGapChart N x) (centeredGapChart N y) ≤ dist x y := by
  rw [Subtype.dist_eq, centeredGapChart_eq_orthComp, centeredGapChart_eq_orthComp,
    dist_eq_norm, Riesz1.hsOrthComp_sub, dist_eq_norm]
  have hh := Riesz1.norm_sq_hsOrthComp N (x - y)
  nlinarith [norm_nonneg (Riesz1.hsOrthComp N (x - y)).val, norm_nonneg (x - y),
    sq_nonneg (inner ℝ (x - y) (Riesz1.hsUnitVector N))]

/-- Centering fixes a tangent vector. -/
theorem centeredGapChart_coe (z : gapTangentSpace N) : centeredGapChart N z.val = z := by
  apply Subtype.ext
  ext i
  change z.val i - (∑ j, z.val j) / (N : ℝ) = z.val i
  rw [show ∑ j, z.val j = 0 from z.property]
  simp

/-- Centering preserves membership in the collision chamber, including its complement. -/
theorem centeredGapChart_mem_chamber_iff (x : EuclideanSpace ℝ (Fin (N : ℕ))) :
    (centeredGapChart N x).val ∈ particleChamber N ↔ x ∈ particleChamber N := by
  rw [centeredGapChart_val_eq_translate]
  exact Riesz1.hsTranslate_mem_chamber_iff _ x

/-- The quotient collision complement is nonempty when there are at least two particles. -/
theorem quotient_chamber_compl_nonempty (hN : 2 ≤ (N : ℕ)) :
    ({z : gapTangentSpace N | z.val ∈ particleChamber N}ᶜ).Nonempty := by
  obtain ⟨x, hx⟩ := Riesz1.hsChamber_compl_nonempty hN
  exact ⟨centeredGapChart N x, fun h => hx ((centeredGapChart_mem_chamber_iff x).mp h)⟩

/-- See Subsection 3.2 of the paper: the particle collision distance equals the distance in the
orthogonal quotient, because centering preserves the collision complement and contracts. -/
theorem particle_infDist_eq_quotient (hN : 2 ≤ (N : ℕ)) (z : gapTangentSpace N) :
    Metric.infDist z.val (particleChamber N)ᶜ =
      Metric.infDist z {w : gapTangentSpace N | w.val ∈ particleChamber N}ᶜ := by
  apply le_antisymm
  · rw [Metric.le_infDist (quotient_chamber_compl_nonempty hN)]
    intro w hw
    exact Metric.infDist_le_dist_of_mem hw
  · apply (Metric.le_infDist (show (particleChamber N)ᶜ.Nonempty from
      Riesz1.hsChamber_compl_nonempty hN)).mpr
    intro x hx
    have hcx : centeredGapChart N x ∈
        {w : gapTangentSpace N | w.val ∈ particleChamber N}ᶜ :=
      fun h => hx ((centeredGapChart_mem_chamber_iff x).mp h)
    calc
      _ ≤ dist z (centeredGapChart N x) := Metric.infDist_le_dist_of_mem hcx
      _ ≤ dist z.val x := by
        simpa only [centeredGapChart_coe] using dist_centeredGapChart_le z.val x

/-- See Subsection 3.2 of the paper: both singular-value comparisons for collision distance. -/
theorem intrinsicGap_boundary_distances (hN : 2 ≤ (N : ℕ)) (z : gapTangentSpace N) :
    Metric.infDist (intrinsicParticleGapMap N z) (intrinsicGapDomain N)ᶜ ≤
        ‖(gapLinearEquiv N).toContinuousLinearMap‖ *
          Metric.infDist z.val (particleChamber N)ᶜ ∧
      Metric.infDist z.val (particleChamber N)ᶜ ≤
        ‖(gapLinearEquiv N).symm.toContinuousLinearMap‖ *
          Metric.infDist (intrinsicParticleGapMap N z) (intrinsicGapDomain N)ᶜ := by
  have hQ : IsOpen {z : gapTangentSpace N | z.val ∈ particleChamber N} :=
    (Riesz1.isOpen_hsChamber N).preimage continuous_subtype_val
  have himage : (fun z => gapLinearEquiv N z + gapOffset N) ''
      {z : gapTangentSpace N | z.val ∈ particleChamber N}ᶜ = (intrinsicGapDomain N)ᶜ := by
    change particleGapHomeomorph N '' _ = _
    rw [(particleGapHomeomorph N).image_compl]
    congr 1
    simp only [particleGapHomeomorph_apply]
    exact (intrinsicParticleGapMap_bijOn N).image_eq
  have hr := AffineMetricTransport.infDist_affine_image_bounds (gapLinearEquiv N)
    (gapOffset N) hQ.isClosed_compl (quotient_chamber_compl_nonempty hN) z
  rw [himage, ← intrinsicParticleGapMap_eq, ← particle_infDist_eq_quotient hN] at hr
  exact hr

/-- See Subsection 3.2 of the paper: the inverse-chart Hessian is the particle Hessian
on the inverse images of its two directions. -/
theorem hessian_intrinsicGapPotential {hN : 2 ≤ (N : ℕ)}
    {χ : ParticlePairData N} {c : ℝ} (h : AdmissibleParticlePairs hN χ c)
    {z : gapTangentSpace N} (hz : z.val ∈ particleChamber N)
    (u v : gapTangentSpace N) :
    fderiv ℝ (fderiv ℝ W(χ)) (intrinsicParticleGapMap N z) u v =
      fderiv ℝ (fderiv ℝ (particlePairEnergy χ)) z.val
        ((gapLinearEquiv N).symm u).val ((gapLinearEquiv N).symm v).val := by
  rw [← hessian_restrict_particlePotential h hz,
    hessian_intrinsicParticlePotential h hz,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- The ambient and orthogonal particle gradients agree after the canonical inclusion. -/
theorem gradient_restrict_particlePotential {hN : 2 ≤ (N : ℕ)}
    {χ : ParticlePairData N} {c : ℝ} (h : AdmissibleParticlePairs hN χ c)
    {z : gapTangentSpace N} (hz : z.val ∈ particleChamber N) :
    (gradient H(χ) z).val = gradient (particlePairEnergy χ) z.val := by
  have hgmem : gradient (particlePairEnergy χ) z.val ∈ gapTangentSpace N := by
    rw [← libraryPairs_energy h]
    exact Riesz1.boundaryCore_gradient_sum (libraryPairs h) hz
  let g : gapTangentSpace N := ⟨gradient (particlePairEnergy χ) z.val, hgmem⟩
  have hgrad : gradient H(χ) z = g := by
    apply ext_inner_right ℝ
    intro u
    rw [inner_gradient_left]
    have hd := (Riesz1.hasFDerivAt_hsPairExpression (libraryPairs h) hz).differentiableAt
    rw [libraryPairs_energy] at hd
    have he := (hd.hasFDerivAt.comp z (gapTangentSpace N).subtypeL.hasFDerivAt).fderiv
    simp only [Function.comp_def] at he
    rw [he]
    change fderiv ℝ (particlePairEnergy χ) z.val u.val = inner ℝ g.val u.val
    exact (inner_gradient_left).symm
  exact congrArg Subtype.val hgrad

/-- See Lemma A.1 of the paper: the particle gradient is bounded by `‖B‖` times the
gap gradient, with the actual Euclidean metric on both tangent spaces. -/
theorem particle_gradient_norm_le {hN : 2 ≤ (N : ℕ)}
    {χ : ParticlePairData N} {c : ℝ} (h : AdmissibleParticlePairs hN χ c)
    {z : gapTangentSpace N} (hz : z.val ∈ particleChamber N) :
    ‖gradient (particlePairEnergy χ) z.val‖ ≤
      (2 * (N : ℝ)) * ‖gradient W(χ) (intrinsicParticleGapMap N z)‖ := by
  rw [← gradient_restrict_particlePotential h hz, Submodule.norm_coe,
    gradient_intrinsicParticlePotential h hz]
  calc
    _ ≤ ‖(gapLinearEquiv N).toContinuousLinearMap.adjoint‖ *
        ‖gradient W(χ) (intrinsicParticleGapMap N z)‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖(gapLinearEquiv N).toContinuousLinearMap‖ *
        ‖gradient W(χ) (intrinsicParticleGapMap N z)‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ _ := mul_le_mul_of_nonneg_right (opNorm_gapLinearEquiv_le N) (norm_nonneg _)

/-- The library's exact trace formula in the pair convention. -/
theorem particlePairEnergy_laplacian {hN : 2 ≤ (N : ℕ)}
    {χ : ParticlePairData N} {c : ℝ} (h : AdmissibleParticlePairs hN χ c)
    {x : EuclideanSpace ℝ (Fin (N : ℕ))} (hx : x ∈ particleChamber N) :
    Laplacian.laplacian (particlePairEnergy χ) x =
      4 * ∑ p : {p : Fin (N : ℕ) × Fin (N : ℕ) // p.1 < p.2},
        deriv (deriv (χ p)) (x p.val.2 - x p.val.1) := by
  rw [← libraryPairs_energy h, Riesz1.laplacian_hsPairExpression (libraryPairs h) hx]
  congr 1
  rw [sum_pairs]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_subtype (univ.filter (i < ·)) (p := fun j => i < j) (by simp)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [libraryPairs, symmetricPairFamily_apply χ j.property]

/-- The Riesz representer of a pair separation is a tangent vector of squared norm two. -/
theorem exists_pairSeparationVector (i j : Fin (N : ℕ)) (hij : i < j) :
    ∃ r : gapTangentSpace N, ‖r‖ ^ 2 = 2 ∧
      ∀ v : gapTangentSpace N, inner ℝ r v = v.val j - v.val i := by
  classical
  let r : gapTangentSpace N :=
    ⟨EuclideanSpace.single j 1 - EuclideanSpace.single i 1, by
      change (∑ k : Fin (N : ℕ),
        ((EuclideanSpace.single j (1 : ℝ) : EuclideanSpace ℝ (Fin (N : ℕ))) k -
          (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin (N : ℕ))) k)) = 0
      simp [Finset.sum_sub_distrib, PiLp.single_apply]⟩
  have hrnorm : ‖r‖ ^ 2 = 2 := by
    rw [← real_inner_self_eq_norm_sq]
    change inner ℝ r.val r.val = 2
    dsimp only [r]
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    norm_num [EuclideanSpace.inner_single_left, PiLp.single_apply, hij.ne, hij.ne']
  have hr (v : gapTangentSpace N) : inner ℝ r v = v.val j - v.val i := by
    change inner ℝ r.val v.val = _
    simp only [r, inner_sub_left, EuclideanSpace.inner_single_left, map_one, one_mul]
  exact ⟨r, hrnorm, hr⟩

/-- Parseval for a pair separation after the inverse cyclic difference map.
The bound is independent of the configuration. -/
theorem sum_inverse_separation_sq_le {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (gapTangentSpace N))
    (i j : Fin (N : ℕ)) (hij : i < j) :
    (∑ a, (((gapLinearEquiv N).symm (b a)).val j -
      ((gapLinearEquiv N).symm (b a)).val i) ^ 2) ≤
        2 * ‖(gapLinearEquiv N).symm.toContinuousLinearMap‖ ^ 2 := by
  obtain ⟨r, hrnorm, hr⟩ := exists_pairSeparationVector i j hij
  have he : (∑ a, (((gapLinearEquiv N).symm (b a)).val j -
      ((gapLinearEquiv N).symm (b a)).val i) ^ 2) =
      ‖(gapLinearEquiv N).symm.toContinuousLinearMap.adjoint r‖ ^ 2 := by
    rw [← b.sum_sq_inner_left]
    apply Finset.sum_congr rfl
    intro a _
    rw [ContinuousLinearMap.adjoint_inner_left, hr]
    rfl
  rw [he]
  have hn := ContinuousLinearMap.le_opNorm
    (gapLinearEquiv N).symm.toContinuousLinearMap.adjoint r
  rw [ContinuousLinearMap.adjoint.norm_map] at hn
  have hs := mul_self_le_mul_self (norm_nonneg _) hn
  simpa only [← pow_two, mul_pow, hrnorm, mul_comm] using hs

/-- See Lemma A.1 of the paper: positivity of the pair curvatures gives the uniform
trace comparison `ΔW ≤ ‖B⁻¹‖² ΔH`. -/
theorem intrinsicGapPotential_laplacian_le {hN : 2 ≤ (N : ℕ)}
    {χ : ParticlePairData N} {c : ℝ} (hc : 0 < c) (h : AdmissibleParticlePairs hN χ c)
    {z : gapTangentSpace N} (hz : z.val ∈ particleChamber N) :
    Laplacian.laplacian W(χ) (intrinsicParticleGapMap N z) ≤
      ‖(gapLinearEquiv N).symm.toContinuousLinearMap‖ ^ 2 *
        Laplacian.laplacian (particlePairEnergy χ) z.val := by
  let b := stdOrthonormalBasis ℝ (gapTangentSpace N)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b,
    particlePairEnergy_laplacian h hz]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp_rw [hessian_intrinsicGapPotential h hz, particlePairEnergy_hessian h hz, ← pow_two]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  calc
    _ ≤ 2 * ∑ p : {p : Fin (N : ℕ) × Fin (N : ℕ) // p.1 < p.2},
        deriv (deriv (χ p)) (z.val p.val.2 - z.val p.val.1) *
          (2 * ‖(gapLinearEquiv N).symm.toContinuousLinearMap‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro p _
      have hp : 0 ≤ deriv (deriv (χ p)) (z.val p.val.2 - z.val p.val.1) :=
        hc.le.trans ((h.1 p).2.1 _ (Riesz1.hsChamber_separation_mem hz p.property))
      exact mul_le_mul_of_nonneg_left
        (sum_inverse_separation_sq_le b p.val.1 p.val.2 p.property) hp
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- See Lemma A.1 of the paper: every positive collision coefficient survives the affine
metric change. Constants depend only on the fixed data and the three coefficients. -/
theorem intrinsicGap_collision_bound (hN : 2 ≤ (N : ℕ)) (c : ℝ) (hc : 0 < c)
    (χ : ParticlePairData N) (h : AdmissibleParticlePairs hN χ c)
    (a b k : ℝ) (ha : 0 < a) (hb : 0 < b) (hk : 0 < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ intrinsicGapDomain N,
      k * (Metric.infDist y (intrinsicGapDomain N)ᶜ)⁻¹ ^ 2 - C ≤
        a * ‖gradient W(χ) y‖ ^ 2 - b * Laplacian.laplacian W(χ) y := by
  let M : ℝ := 2 * (N : ℝ)
  let K : ℝ := max (‖(gapLinearEquiv N).symm.toContinuousLinearMap‖ ^ 2) 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨C, hC, hbound⟩ := particle_collision_bound hc h (a / M ^ 2) (b * K) (k * K)
    (div_pos ha (sq_pos_of_pos hM)) (mul_pos hb hK) (mul_pos hk hK)
  refine ⟨C, hC, fun y hy => ?_⟩
  let z := (gapLinearEquiv N).symm (y - gapOffset N)
  have hzT : intrinsicParticleGapMap N z = y := by
    rw [intrinsicParticleGapMap_eq, ContinuousLinearEquiv.apply_symm_apply, sub_add_cancel]
  have hz := (intrinsicParticleGapMap_mem_iff N z).mp (hzT.symm ▸ hy)
  have hg := particle_gradient_norm_le h hz
  have hl := intrinsicGapPotential_laplacian_le hc h hz
  have hd := (intrinsicGap_boundary_distances hN z).2
  rw [hzT] at hg hl hd
  let dp := Metric.infDist z.val (particleChamber N)ᶜ
  let dy := Metric.infDist y (intrinsicGapDomain N)ᶜ
  have hp : 0 < dp := Riesz1.hsBoundaryDistance_pos hN hz
  have hypos : 0 < dy := by
    have hn : 0 ≤ dy := Metric.infDist_nonneg
    by_contra hdy
    have hzero : dy = 0 := le_antisymm (le_of_not_gt hdy) hn
    change dp ≤ ‖(gapLinearEquiv N).symm.toContinuousLinearMap‖ * dy at hd
    rw [hzero, mul_zero] at hd
    exact (not_le_of_gt hp) hd
  have hd2 : dp ^ 2 ≤ K * dy ^ 2 := by
    have hs := mul_self_le_mul_self hp.le hd
    change dp * dp ≤ (‖(gapLinearEquiv N).symm.toContinuousLinearMap‖ * dy) *
      (‖(gapLinearEquiv N).symm.toContinuousLinearMap‖ * dy) at hs
    have hm := mul_le_mul_of_nonneg_right (le_max_left
      (‖(gapLinearEquiv N).symm.toContinuousLinearMap‖ ^ 2) 1) (sq_nonneg dy)
    nlinarith
  have hdinv : dy⁻¹ ^ 2 ≤ K * dp⁻¹ ^ 2 := by
    rw [inv_pow, inv_pow, inv_eq_one_div, inv_eq_one_div, mul_one_div]
    apply (le_div_iff₀ (sq_pos_of_pos hp)).mpr
    rw [one_div_mul_eq_div]
    exact (div_le_iff₀ (sq_pos_of_pos hypos)).mpr hd2
  have hg2 := mul_self_le_mul_self (norm_nonneg _) hg
  have hgcoeff : (a / M ^ 2) * ‖gradient (particlePairEnergy χ) z.val‖ ^ 2 ≤
      a * ‖gradient W(χ) y‖ ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hg2 (le_of_lt (div_pos ha (sq_pos_of_pos hM)))
    have he : a / M ^ 2 * (M * ‖gradient W(χ) y‖) ^ 2 =
        a * ‖gradient W(χ) y‖ ^ 2 := by field_simp
    rw [← pow_two, ← pow_two, he] at hm
    exact hm
  have hlcoeff : b * Laplacian.laplacian W(χ) y ≤
      b * K * Laplacian.laplacian (particlePairEnergy χ) z.val := by
    have hlap := particlePairEnergy_laplacian_nonneg hc h hz
    have hmax := mul_le_mul_of_nonneg_right (le_max_left
      (‖(gapLinearEquiv N).symm.toContinuousLinearMap‖ ^ 2) 1) hlap
    have hh := mul_le_mul_of_nonneg_left (hl.trans hmax) hb.le
    simpa only [mul_assoc] using hh
  have hdist := mul_le_mul_of_nonneg_left hdinv hk.le
  have hbnd := hbound z.val hz
  change k * dy⁻¹ ^ 2 - C ≤ _
  change k * K * dp⁻¹ ^ 2 - C ≤ _ at hbnd
  nlinarith

/-- See Lemma A.1 of the paper: the intrinsic Schrödinger collision barrier and its
particle-metric counterpart, with finite nonnegative constants. -/
theorem intrinsicGap_collision_criterion (hN : 2 ≤ (N : ℕ)) (c : ℝ) (hc : 0 < c)
    (χ : ParticlePairData N) (h : AdmissibleParticlePairs hN χ c) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ intrinsicGapDomain N,
      (Metric.infDist y (intrinsicGapDomain N)ᶜ)⁻¹ ^ 2 - C ≤
        ‖gradient W(χ) y‖ ^ 2 / 4 - Laplacian.laplacian W(χ) y / 2) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ particleChamber N,
      (Metric.infDist x (particleChamber N)ᶜ)⁻¹ ^ 2 - C ≤
        ‖gradient (particlePairEnergy χ) x‖ ^ 2 / 4 -
          Laplacian.laplacian (particlePairEnergy χ) x / 2) := by
  constructor
  · obtain ⟨C, hC, hb⟩ := intrinsicGap_collision_bound hN c hc χ h
      (1 / 4) (1 / 2) 1 (by norm_num) (by norm_num) (by norm_num)
    refine ⟨C, hC, fun y hy => ?_⟩
    simpa only [one_mul, one_div_mul_eq_div] using hb y hy
  · obtain ⟨C, hC, hb⟩ := particle_collision_bound hc h
      (1 / 4) (1 / 2) 1 (by norm_num) (by norm_num) (by norm_num)
    refine ⟨C, hC, fun x hx => ?_⟩
    simpa only [one_mul, one_div_mul_eq_div] using hb x hx

/-- Canonical isometric identification with the library's orthogonal space.
This changes only the subtype certificate, not the vector or metric. -/
def orthTangentEquiv (N : ℕ+) : Riesz1.hsOrthSubspace N ≃ₗᵢ[ℝ] gapTangentSpace N where
  toLinearEquiv :=
    { toFun := fun z => ⟨z.val, by rw [gapTangentSpace_eq_orth]; exact z.property⟩
      invFun := fun z => ⟨z.val, by rw [← gapTangentSpace_eq_orth]; exact z.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  norm_map' := fun _ => rfl

/-- See Subsection 3.2 of the paper: the gap law is the affine image of the
library's orthogonal Gibbs law. -/
theorem intrinsicGapLaw_eq_map_radial (hN : 2 ≤ (N : ℕ)) (c : ℝ) (hc : 0 < c)
    (χ : ParticlePairData N) (h : AdmissibleParticlePairs hN χ c) :
    intrinsicGapLaw (pairGibbsMeasure χ (pairGibbsWeight_measurable h)
        (particle_hessian_normalization hN c hc χ h).1) =
      (Riesz1.hsRadialProbability (libraryPairs h) hc : Measure _).map
        (fun z => intrinsicParticleGapMap N (orthTangentEquiv N z)) := by
  let μ := pairGibbsMeasure χ (pairGibbsWeight_measurable h)
    (particle_hessian_normalization hN c hc χ h).1
  have hrad : (μ.map (Riesz1.hsConfigCoord N)).map Prod.fst =
      (Riesz1.hsRadialProbability (libraryPairs h) hc : Measure _) := by
    rw [particle_rotation_product_law hN c hc χ h, Measure.map_fst_prod,
      measure_univ, one_smul]
  have hm : Measurable (fun z => intrinsicParticleGapMap N (orthTangentEquiv N z)) := by
    have he : (fun z => intrinsicParticleGapMap N (orthTangentEquiv N z)) =
        (particleGapHomeomorph N) ∘ orthTangentEquiv N := by
      funext z
      exact (particleGapHomeomorph_apply _ _).symm
    rw [he]
    exact (particleGapHomeomorph N).measurable.comp (orthTangentEquiv N).continuous.measurable
  rw [← hrad, Measure.map_map hm measurable_fst,
    Measure.map_map (hm.comp measurable_fst) (Riesz1.measurable_hsConfigCoord N)]
  apply congrArg (fun f => μ.map f)
  funext X
  change centeredGapChart N (WithLp.toLp 2 (gapVector X)) =
    intrinsicParticleGapMap N (orthTangentEquiv N (Riesz1.hsConfigCoord N X).1)
  unfold intrinsicParticleGapMap
  congr 1
  change WithLp.toLp 2 (gapVector X) = WithLp.toLp 2
    (Riesz1.hsGap (Riesz1.hsOrthComp N (WithLp.toLp 2 X.val)).val)
  rw [← centeredGapChart_eq_orthComp, centeredGapChart_val_eq_translate,
    Riesz1.hsGap_translate, Riesz1.hsGap_eq_gapVector]
  rfl

/-- See Subsection 3.2 of the paper: the constant Jacobian of the affine gap chart, for
intrinsic Euclidean volume. -/
theorem particleGapHomeomorph_map_volume (N : ℕ+) :
    (volume : Measure (gapTangentSpace N)).map (particleGapHomeomorph N) =
      ENNReal.ofReal |(LinearMap.det (gapLinearEquiv N).toLinearEquiv.toLinearMap)⁻¹| • volume := by
  have hd : LinearMap.det (gapLinearEquiv N).toLinearEquiv.toLinearMap ≠ 0 :=
    (gapLinearEquiv N).toLinearEquiv.isUnit_det'.ne_zero
  have he : (particleGapHomeomorph N : gapTangentSpace N → gapTangentSpace N) =
      (fun y => y + gapOffset N) ∘ (gapLinearEquiv N) := rfl
  rw [he, ← Measure.map_map (by fun_prop) (gapLinearEquiv N).continuous.measurable,
    show volume.map (gapLinearEquiv N) =
      ENNReal.ofReal |(LinearMap.det (gapLinearEquiv N).toLinearEquiv.toLinearMap)⁻¹| • volume from
      Measure.map_linearMap_addHaar_eq_smul_addHaar volume hd,
    Measure.map_smul _ (by fun_prop), Measure.IsAddRightInvariant.map_add_right_eq_self]

/-- See Subsection 3.2 of the paper: the intrinsic law has the normalized Gibbs density
of the gap potential, relative to intrinsic Euclidean volume. -/
theorem intrinsicGapLaw_gibbsPotential (hN : 2 ≤ (N : ℕ)) (c : ℝ) (hc : 0 < c)
    (χ : ParticlePairData N) (h : AdmissibleParticlePairs hN χ c) :
    IsEuclideanGibbsPotential volume
      (intrinsicGapLaw (pairGibbsMeasure χ (pairGibbsWeight_measurable h)
        (particle_hessian_normalization hN c hc χ h).1))
      (intrinsicGapDomain N) W(χ) := by
  let A : Riesz1.hsOrthSubspace N ≃ₜ gapTangentSpace N :=
    (orthTangentEquiv N).toHomeomorph.trans (particleGapHomeomorph N)
  let J := ENNReal.ofReal |(LinearMap.det (gapLinearEquiv N).toLinearEquiv.toLinearMap)⁻¹|
  let w : gapTangentSpace N → ℝ≥0∞ := (intrinsicGapDomain N).indicator
    (fun y => ENNReal.ofReal (Real.exp (-W(χ) y)))
  have hd : LinearMap.det (gapLinearEquiv N).toLinearEquiv.toLinearMap ≠ 0 :=
    (gapLinearEquiv N).toLinearEquiv.isUnit_det'.ne_zero
  have hJ : J ≠ 0 := (ENNReal.ofReal_pos.mpr (abs_pos.mpr (inv_ne_zero hd))).ne'
  have hJt : J ≠ ⊤ := ENNReal.ofReal_ne_top
  have hAv : (volume : Measure (Riesz1.hsOrthSubspace N)).map A = J • volume := by
    change volume.map ((particleGapHomeomorph N) ∘ orthTangentEquiv N) = _
    rw [← Measure.map_map (particleGapHomeomorph N).measurable
      (orthTangentEquiv N).continuous.measurable,
      (orthTangentEquiv N).measurePreserving.map_eq, particleGapHomeomorph_map_volume]
  have hcomp : (fun z => w (A z)) = Riesz1.hsRadialDensity (libraryPairs h) := by
    funext z
    have hmem : A z ∈ intrinsicGapDomain N ↔ z ∈ Riesz1.hsRadialDomain N := by
      change particleGapHomeomorph N (orthTangentEquiv N z) ∈ intrinsicGapDomain N ↔ _
      rw [particleGapHomeomorph_apply]
      exact intrinsicParticleGapMap_mem_iff N (orthTangentEquiv N z)
    by_cases hz : z ∈ Riesz1.hsRadialDomain N
    · have he : A z = intrinsicParticleGapMap N (orthTangentEquiv N z) :=
        particleGapHomeomorph_apply _ _
      dsimp only [w]
      rw [indicator_of_mem (hmem.mpr hz), Riesz1.hsRadialDensity, indicator_of_mem hz]
      rw [he]
      rw [pairPotential_intrinsicParticleGapMap, libraryPairs_energy]
      rfl
    · rw [show w (A z) = 0 from indicator_of_notMem (fun hy => hz (hmem.mp hy)) _,
        Riesz1.hsRadialDensity, indicator_of_notMem hz]
  have hw : Measurable w := by
    have he : w = (Riesz1.hsRadialDensity (libraryPairs h)) ∘ A.symm := by
      funext y
      rw [← hcomp]
      simp
    rw [he]
    exact (Riesz1.measurable_hsRadialDensity _).comp A.symm.measurable
  have hmass : (∫⁻ z, w (A z)) = Riesz1.hsRadialMeasure (libraryPairs h) univ := by
    rw [hcomp, Riesz1.hsRadialMeasure, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
  have h0 : (∫⁻ z, w (A z)) ≠ 0 :=
    hmass ▸ Riesz1.hsRadialMeasure_univ_ne_zero _
  have ht : (∫⁻ z, w (A z)) ≠ ⊤ :=
    hmass ▸ Riesz1.hsRadialMeasure_univ_ne_top _ hc
  have hmass' : J * (∫⁻ y, w y) = ∫⁻ z, w (A z) := by
    rw [← A.measurableEmbedding.lintegral_map w, hAv, lintegral_smul_measure, smul_eq_mul]
  have hZ0 : (∫⁻ y, w y) ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmass'
    exact h0 hmass'.symm
  have hZt : (∫⁻ y, w y) ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top hJ] at hmass'
    exact ht hmass'.symm
  have hnorm := AffineFibre.normalizedMeasure_map volume A.measurableEmbedding hw h0 ht
  simp only [hAv] at hnorm
  rw [AffineFibre.normalizedMeasure_smul_measure volume w hZ0 hZt hJ hJt] at hnorm
  have hrad : AffineFibre.normalizedMeasure volume (fun z => w (A z)) h0 ht =
      (Riesz1.hsRadialProbability (libraryPairs h) hc : Measure _) := by
    rw [AffineFibre.normalizedMeasure_eq_smul, hmass, hcomp]
    rfl
  rw [hrad] at hnorm
  have hΩ : MeasurableSet (intrinsicGapDomain N) := by
    have he := (intrinsicParticleGapMap_bijOn N).image_eq
    have hopen := (particleGapHomeomorph N).isOpenMap _
      ((Riesz1.isOpen_hsChamber N).preimage continuous_subtype_val)
    simp only [particleGapHomeomorph_apply] at hopen
    change IsOpen (intrinsicParticleGapMap N ''
      {z : gapTangentSpace N | z.val ∈ particleChamber N}) at hopen
    rw [he] at hopen
    exact hopen.measurableSet
  refine ⟨fun y hy => (contDiffAt_intrinsicGapPotential h hy).contDiffWithinAt, ?_⟩
  have hZ : (∫⁻ y, w y) =
      ∫⁻ y in intrinsicGapDomain N, ENNReal.ofReal (Real.exp (-W(χ) y)) :=
    lintegral_indicator hΩ _
  refine ⟨?_, ?_, ?_⟩
  · rw [← hZ]
    exact pos_iff_ne_zero.mpr hZ0
  · rw [← hZ]
    exact lt_top_iff_ne_top.mpr hZt
  · rw [intrinsicGapLaw_eq_map_radial hN c hc χ h]
    have hA : (fun z => intrinsicParticleGapMap N (orthTangentEquiv N z)) = A := by
      funext z
      exact (particleGapHomeomorph_apply _ _).symm
    rw [hA]
    rw [← hnorm, AffineFibre.normalizedMeasure_eq_smul, hZ]
    congr 1
    exact withDensity_indicator hΩ _

/-- The full intrinsic simplex is open in its direction space. -/
theorem intrinsicGapDomain_isOpen (N : ℕ+) : IsOpen (intrinsicGapDomain N) := by
  have hopen := (particleGapHomeomorph N).isOpenMap _
    ((Riesz1.isOpen_hsChamber N).preimage continuous_subtype_val)
  simp only [particleGapHomeomorph_apply] at hopen
  change IsOpen (intrinsicParticleGapMap N ''
    {z : gapTangentSpace N | z.val ∈ particleChamber N}) at hopen
  rwa [(intrinsicParticleGapMap_bijOn N).image_eq] at hopen

/-- The collision complement of the full intrinsic simplex is nonempty for `N ≥ 2`. -/
theorem intrinsicGapDomain_compl_nonempty (hN : 2 ≤ (N : ℕ)) :
    (intrinsicGapDomain N)ᶜ.Nonempty := by
  obtain ⟨z, hz⟩ := quotient_chamber_compl_nonempty hN
  exact ⟨intrinsicParticleGapMap N z,
    fun h => hz ((intrinsicParticleGapMap_mem_iff N z).mp h)⟩

/-- See Subsection 3.2 of the paper: the singular-value distance bounds, stated on the actual
frontiers of the two relatively open quotient domains. -/
theorem intrinsicGap_frontier_distances (hN : 2 ≤ (N : ℕ))
    {z : gapTangentSpace N} (hz : z.val ∈ particleChamber N) :
    Metric.infDist (intrinsicParticleGapMap N z) (frontier (intrinsicGapDomain N)) ≤
        ‖(gapLinearEquiv N).toContinuousLinearMap‖ *
          Metric.infDist z (frontier {w : gapTangentSpace N | w.val ∈ particleChamber N}) ∧
      Metric.infDist z (frontier {w : gapTangentSpace N | w.val ∈ particleChamber N}) ≤
        ‖(gapLinearEquiv N).symm.toContinuousLinearMap‖ *
          Metric.infDist (intrinsicParticleGapMap N z) (frontier (intrinsicGapDomain N)) := by
  have hQ : IsOpen {z : gapTangentSpace N | z.val ∈ particleChamber N} :=
    (Riesz1.isOpen_hsChamber N).preimage continuous_subtype_val
  rw [infDist_frontier_eq_infDist_compl (intrinsicGapDomain_isOpen N)
      ((intrinsicParticleGapMap_mem_iff N z).mpr hz) (intrinsicGapDomain_compl_nonempty hN),
    infDist_frontier_eq_infDist_compl hQ hz (quotient_chamber_compl_nonempty hN),
    ← particle_infDist_eq_quotient hN]
  exact intrinsicGap_boundary_distances hN z

/-- See Subsection 3.2 of the paper: no artificial rotation cut enters either boundary distance. -/
theorem particle_frontier_distance_eq_quotient (hN : 2 ≤ (N : ℕ))
    {z : gapTangentSpace N} (hz : z.val ∈ particleChamber N) :
    Metric.infDist z.val (frontier (particleChamber N)) =
      Metric.infDist z (frontier {w : gapTangentSpace N | w.val ∈ particleChamber N}) := by
  have hP : IsOpen (particleChamber N) := Riesz1.isOpen_hsChamber N
  have hQ : IsOpen {z : gapTangentSpace N | z.val ∈ particleChamber N} :=
    hP.preimage continuous_subtype_val
  rw [infDist_frontier_eq_infDist_compl hP hz (Riesz1.hsChamber_compl_nonempty hN),
    infDist_frontier_eq_infDist_compl hQ hz (quotient_chamber_compl_nonempty hN),
    particle_infDist_eq_quotient hN]

/-- See Subsection 3.2 of the paper, complete: affine bijection, invertible derivative, uniform
independent common rotation, potential and Gibbs density identities, both chain rules,
intrinsic curvature, and singular-value boundary-distance comparisons. -/
theorem affine_gap_map (hN : 2 ≤ (N : ℕ)) (c : ℝ) (hc : 0 < c)
    (χ : ParticlePairData N) (h : AdmissibleParticlePairs hN χ c) :
    Set.BijOn (intrinsicParticleGapMap N)
      {z : gapTangentSpace N | z.val ∈ particleChamber N} (intrinsicGapDomain N) ∧
    Function.Bijective (gapLinearEquiv N) ∧
    (∀ z, HasFDerivAt (intrinsicParticleGapMap N) (gapLinearEquiv N).toContinuousLinearMap z) ∧
    ((pairGibbsMeasure χ (pairGibbsWeight_measurable h)
        (particle_hessian_normalization hN c hc χ h).1).map (Riesz1.hsConfigCoord N) =
      (Riesz1.hsRadialProbability (libraryPairs h) hc : Measure (Riesz1.hsOrthSubspace N)).prod
        (Riesz1.hsUniformCircle N : Measure (AddCircle (Real.sqrt (N : ℕ))))) ∧
    (∀ z : gapTangentSpace N, W(χ) (intrinsicParticleGapMap N z) = H(χ) z) ∧
    IsEuclideanGibbsPotential volume
      (intrinsicGapLaw (pairGibbsMeasure χ (pairGibbsWeight_measurable h)
        (particle_hessian_normalization hN c hc χ h).1))
      (intrinsicGapDomain N) W(χ) ∧
    (∀ z : gapTangentSpace N, z.val ∈ particleChamber N →
      gradient H(χ) z = (gapLinearEquiv N).toContinuousLinearMap.adjoint
        (gradient W(χ) (intrinsicParticleGapMap N z)) ∧
      ∀ u v : gapTangentSpace N, fderiv ℝ (fderiv ℝ H(χ)) z u v =
        fderiv ℝ (fderiv ℝ W(χ)) (intrinsicParticleGapMap N z)
          (gapLinearEquiv N u) (gapLinearEquiv N v)) ∧
    (∀ y ∈ intrinsicGapDomain N, ∀ u : gapTangentSpace N,
      c / (2 * (N : ℝ)) * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ W(χ)) y u u) ∧
    (∀ z : gapTangentSpace N, z.val ∈ particleChamber N →
      Metric.infDist (intrinsicParticleGapMap N z) (frontier (intrinsicGapDomain N)) ≤
          ‖(gapLinearEquiv N).toContinuousLinearMap‖ *
            Metric.infDist z (frontier {w : gapTangentSpace N | w.val ∈ particleChamber N}) ∧
        Metric.infDist z (frontier {w : gapTangentSpace N | w.val ∈ particleChamber N}) ≤
          ‖(gapLinearEquiv N).symm.toContinuousLinearMap‖ *
            Metric.infDist (intrinsicParticleGapMap N z) (frontier (intrinsicGapDomain N))) := by
  refine ⟨intrinsicParticleGapMap_bijOn N, (gapLinearEquiv N).bijective,
    hasFDerivAt_intrinsicParticleGapMap N, particle_rotation_product_law hN c hc χ h,
    pairPotential_intrinsicParticleGapMap χ, intrinsicGapLaw_gibbsPotential hN c hc χ h,
    ?_, (fun _ hy => intrinsicGapPotential_curvature hc h hy), ?_⟩
  · exact fun z hz => ⟨gradient_intrinsicParticlePotential h hz,
      hessian_intrinsicParticlePotential h hz⟩
  · exact fun _ hz => intrinsicGap_frontier_distances hN hz

/-- See Lemma A.1 of the paper, complete: all positive coefficients in the intrinsic
collision estimate and the particular Schrödinger barriers in both metrics. Distances
are to the actual collision frontiers, and all constants precede the configuration. -/
theorem collision_metric_transport (hN : 2 ≤ (N : ℕ)) (c : ℝ) (hc : 0 < c)
    (χ : ParticlePairData N) (h : AdmissibleParticlePairs hN χ c) :
    (∀ a b k : ℝ, 0 < a → 0 < b → 0 < k →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ intrinsicGapDomain N,
        k * (Metric.infDist y (frontier (intrinsicGapDomain N)))⁻¹ ^ 2 - C ≤
          a * ‖gradient W(χ) y‖ ^ 2 - b * Laplacian.laplacian W(χ) y) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ intrinsicGapDomain N,
      (Metric.infDist y (frontier (intrinsicGapDomain N)))⁻¹ ^ 2 - C ≤
        ‖gradient W(χ) y‖ ^ 2 / 4 - Laplacian.laplacian W(χ) y / 2) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ particleChamber N,
      (Metric.infDist x (frontier (particleChamber N)))⁻¹ ^ 2 - C ≤
        ‖gradient (particlePairEnergy χ) x‖ ^ 2 / 4 -
          Laplacian.laplacian (particlePairEnergy χ) x / 2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b k ha hb hk
    obtain ⟨C, hC, hbound⟩ := intrinsicGap_collision_bound hN c hc χ h a b k ha hb hk
    refine ⟨C, hC, fun y hy => ?_⟩
    rw [infDist_frontier_eq_infDist_compl (intrinsicGapDomain_isOpen N) hy
      (intrinsicGapDomain_compl_nonempty hN)]
    exact hbound y hy
  · obtain ⟨C, hC, hbound⟩ := (intrinsicGap_collision_criterion hN c hc χ h).1
    refine ⟨C, hC, fun y hy => ?_⟩
    rw [infDist_frontier_eq_infDist_compl (intrinsicGapDomain_isOpen N) hy
      (intrinsicGapDomain_compl_nonempty hN)]
    exact hbound y hy
  · obtain ⟨C, hC, hbound⟩ := (intrinsicGap_collision_criterion hN c hc χ h).2
    refine ⟨C, hC, fun x hx => ?_⟩
    have hP : IsOpen (particleChamber N) := Riesz1.isOpen_hsChamber N
    rw [infDist_frontier_eq_infDist_compl hP hx (Riesz1.hsChamber_compl_nonempty hN)]
    exact hbound x hx

/-- Lemma A.1, Step 1, of the paper: the all-coefficient
collision condition is equivalent in the particle rotation quotient and
the intrinsic gap simplex, for every smooth convex factorized potential.
No pair-potential structure or collision estimate is assumed. -/
theorem gap_collision_criterion_iff (hN : 2 ≤ (N : ℕ))
    (f : gapTangentSpace N → ℝ) (hf : ContDiffOn ℝ 2 f (intrinsicGapDomain N))
    (hc : ConvexOn ℝ {z : gapTangentSpace N | z.val ∈ particleChamber N}
      (fun z => f (intrinsicParticleGapMap N z))) :
    allCoefficientCollisionCriterion
        {z : gapTangentSpace N | z.val ∈ particleChamber N}
        (fun z => f (intrinsicParticleGapMap N z)) ↔
      allCoefficientCollisionCriterion (intrinsicGapDomain N) f := by
  have himage : (fun z => gapLinearEquiv N z + gapOffset N) ''
      {z : gapTangentSpace N | z.val ∈ particleChamber N} = intrinsicGapDomain N := by
    simpa only [← intrinsicParticleGapMap_eq] using (intrinsicParticleGapMap_bijOn N).image_eq
  have hQ : IsOpen {z : gapTangentSpace N | z.val ∈ particleChamber N} :=
    (Riesz1.isOpen_hsChamber N).preimage continuous_subtype_val
  have h := allCoefficientCollisionCriterion_affine_iff_of_convex_pullback
    (gapLinearEquiv N) (gapOffset N) hQ (quotient_chamber_compl_nonempty hN)
    (himage.symm ▸ hf) (by simpa only [← intrinsicParticleGapMap_eq] using hc)
  rw [himage] at h
  simpa only [← intrinsicParticleGapMap_eq] using h

end Riesz2.AffineMetric
