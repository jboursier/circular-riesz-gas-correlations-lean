/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.PhysicalIdentity
public import Riesz2.DecayLong.PhysicalCore
public import Riesz2.DecayLong.ConditionalForces
import all Riesz2.HelfferSjostrand.MarginalHessianPart5

/-!
# Identification of the physical multiplication defect

The conditional coefficients below are the existing density-defined
coefficients. Smooth realizations are used only on the full open ambient
domain, so their first and second derivatives are uniquely determined.
This supplies the multiplication part of Subsection 5.1.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ContDiff Topology Classical

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.PhysicalIdentity
namespace Internal

/-- The normalized Hessian of any realization of the ambient
energy is the physical matrix, in all ambient directions. -/
theorem normalized_ambient_hessian (β : InverseTemperature)
    (s : Riesz1.RieszExponent) (N : ℕ+)
    (U : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ)
    (hv : ∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
      U y.val = β.val * physicalAmbientGapEnergy (ofLong β s) N y)
    (y : EuclideanSpace ℝ (Fin (N : ℕ)))
    (hy : WithLp.ofLp y ∈ Riesz1.gapSimplex N)
    (u v : EuclideanSpace ℝ (Fin (N : ℕ))) :
    β.val⁻¹ * fderiv ℝ (fderiv ℝ U) y u v =
      ∑ a, ∑ b, u a * GoodBlocks.gapHessian s N a b y * v b := by
  obtain ⟨W, hW, hw, hjet⟩ := GoodBlocks.gapHessian_eq_second β s N
  have hyU := PhysicalEnergy.simplex_subset_ambient N _ hy
  have heq : U =ᶠ[𝓝 y] fun z => β.val * W z := by
    filter_upwards [(PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hyU] with z hz
    rw [hv ⟨z,hz⟩, hw ⟨z,hz⟩]
  have hs := hW.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hyU)
  rw [heq.fderiv.fderiv_eq,
    PhysicalCollision.internal_hessian_const_mul (hs.of_le (by norm_num)),
    inv_mul_cancel_left₀ β.property.ne', Intrinsic.hessianMatrix_bilinear hs]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Intrinsic.hessianMatrix_eq_second hs, hjet y hy a b]

/-- The append vector in the moving-fibre calculation is the existing
uniform exterior compensation vector, including the point-fibre case. -/
theorem compensationVector_eq_append (n m : ℕ) :
    WithLp.toLp 2 (Fin.append (fun _ : Fin n => (0 : ℝ))
      (fun _ : Fin (m + 1) => (m + 1 : ℝ)⁻¹)) =
      (WithLp.toLp 2 (ConditionalForces.compensationVector n m) :
        EuclideanSpace ℝ (Fin (n + m + 1))) := by
  apply congrArg (WithLp.toLp 2)
  funext a
  refine Fin.addCases (fun i => ?_) (fun i => ?_) a
  · simp [ConditionalForces.compensationVector, i.isLt]
  · simp [ConditionalForces.compensationVector, Fin.val_natAdd]

/-- The actual conditional is supported on the positive mass simplex. -/
theorem conditional_simplex (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    ∀ᵐ z ∂ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x,
      WithLp.ofLp (RetainedSimplex.chart n m ((n + m : ℕ) + 1)
        (Equiv.refl _) (x.val,z)) ∈ Riesz1.gapSimplex ((n : ℕ) + m).succPNat := by
  filter_upwards [ConditionalEnergyMoments.physical_conditional_support
    (ofLong β s) n m n.pos (Equiv.refl _) x] with z hz
  have hd := (Set.ext_iff.mp (RetainedSimplex.fibre_domain n m _ x.property) z).mpr hz
  have hy := (RetainedSimplex.chart_mem_simplex n m _ (Equiv.refl _) _).mpr hd
  exact ⟨hy.1, by simpa only [Nat.succPNat_coe, Nat.cast_succ] using hy.2⟩

/-- Transport the moving-fibre Hessian average to the literal conditional
chart, before contracting it with any ambient directions. -/
theorem shifted_hessian_mean (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ)
    (U : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ)
    (hv : ∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) //
        y ∈ gapAmbientDomain ((n : ℕ) + m).succPNat},
      U y.val = β.val * physicalAmbientGapEnergy (ofLong β s) ((n : ℕ) + m).succPNat y)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (ρ : Measure (EuclideanSpace ℝ (Fin m)))
    (hmap : ρ.map (fun z => z + AffineSimplex.coordinates m
      (AffineSimplex.centre m (((n + m : ℕ) + 1) - ∑ i, x.val i))) =
      ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x)
    (u v : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1))) :
    (∫ z, β.val⁻¹ * fderiv ℝ (fderiv ℝ U)
      (MarginalHessian.compensatedChart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) u v ∂ρ) =
    ∫ z, ∑ a, ∑ b, u a * GoodBlocks.chartHessian s n m a b (x.val,z) * v b
      ∂ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x := by
  let c := AffineSimplex.coordinates m
    (AffineSimplex.centre m (((n + m : ℕ) + 1) - ∑ i, x.val i))
  let G := fun z : EuclideanSpace ℝ (Fin m) =>
    ∑ a, ∑ b, u a * GoodBlocks.chartHessian s n m a b (x.val,z) * v b
  have hG : Measurable G := by
    apply Finset.measurable_sum
    intro a _
    apply Finset.measurable_sum
    intro b _
    exact (((GoodBlocks.measurable_chartHessian s n m a b).comp
      (measurable_const.prodMk measurable_id)).const_mul _).mul_const _
  change _ = ∫ z, G z ∂_
  rw [← hmap]
  change _ = ∫ z, G z ∂ρ.map (fun z => z + c)
  have hchange : (∫ z, G z ∂ρ.map (fun z => z + c)) = ∫ z, G (z + c) ∂ρ :=
    integral_map (show AEMeasurable (fun z => z + c) ρ from
      (measurable_id.add_const c).aemeasurable) hG.aestronglyMeasurable
  rw [hchange]
  have hs := conditional_simplex β s n m x
  rw [← hmap] at hs
  apply integral_congr_ae
  filter_upwards [ae_of_ae_map (measurable_id.add_const c).aemeasurable hs] with z hz
  rw [MarginalHessian.compensatedChart_eq_shift]
  change β.val⁻¹ * fderiv ℝ (fderiv ℝ U)
    (RetainedSimplex.chart n m _ (Equiv.refl _) (x.val,z+c)) u v = G (z+c)
  exact normalized_ambient_hessian β s ((n : ℕ) + m).succPNat U hv _ hz u v

end Internal

/-- See Subsection 5.1 of the paper, coefficient identification on every proper
physical fibre. The ambient potential realizes the energy on its
whole open domain. The Hessian, compensation and conditional covariance
are all identified with the existing unshifted physical conditional law.
The forces are square integrable, including on a point fibre. -/
theorem proper_hessian_expansion (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε : ℝ) :
    let p := ofLong β s
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      β.val * ∑ i, θ.val ((n : ℝ) ^ (-ε) * x i) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal)
    ∃ U : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain ((n : ℕ) + m).succPNat) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) //
          y ∈ gapAmbientDomain ((n : ℕ) + m).succPNat},
        U y.val = β.val * physicalAmbientGapEnergy p ((n : ℕ) + m).succPNat y) ∧
      ∀ x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
        let μ := ProperMarginalChart.conditionalMeasure p n m n.pos (Equiv.refl _) x
        let q := WithLp.toLp 2 (ConditionalForces.compensationVector n m)
        let Xi := fun i z => β.val⁻¹ *
          (fderiv ℝ U (RetainedSimplex.chart n m ((n + m : ℕ) + 1)
            (Equiv.refl _) (x.val,z)) (EuclideanSpace.single (i.castAdd m).castSucc 1) -
           fderiv ℝ U (RetainedSimplex.chart n m ((n + m : ℕ) + 1)
            (Equiv.refl _) (x.val,z)) q)
        (∀ i : Fin (n : ℕ), MemLp (Xi i) 2 μ) ∧
        ∀ i j : Fin (n : ℕ),
          hessianMatrix V x.val i j =
            β.val * (PhysicalCore.forcingHessian n θ ε x.val i j +
              GoodBlocks.conditionalHessian β s n m i j x +
              ConditionalForces.compensationQ β s n m i j x) -
            β.val ^ 2 * ProbabilityTheory.covariance (Xi i) (Xi j) μ := by
  intro p V
  obtain ⟨U, hU, hv, hK, hmain⟩ := MovingFibre.moving_fibre β s n m n.pos θ ε
  refine ⟨U, hU, hv, fun x => ?_⟩
  intro μ q Xi
  let c := AffineSimplex.coordinates m
    (AffineSimplex.centre m (((n + m : ℕ) + 1) - ∑ i, x.val i))
  let e := fun i : Fin (n : ℕ) => EuclideanSpace.single (i.castAdd m).castSucc (1 : ℝ)
  let y := fun z => MarginalHessian.compensatedChart n m
    ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)
  let B := fun z u v => β.val⁻¹ * fderiv ℝ (fderiv ℝ U) (y z) u v
  let X := fun i z => β.val⁻¹ * (fderiv ℝ U (y z) (e i) - fderiv ℝ U (y z) q)
  obtain ⟨ρ, hρ, hmap, hBi, hX, he⟩ := hmain x
  change ρ.map (fun z => z+c) = μ at hmap
  simp only [Internal.compensationVector_eq_append] at hX he
  have hX' (i : Fin (n : ℕ)) : MemLp (X i) 2 ρ := hX i
  have hmeas (i : Fin (n : ℕ)) : Measurable (Xi i) := by
    exact (((measurable_fderiv_apply_const ℝ U (e i)).sub
      (measurable_fderiv_apply_const ℝ U q)).comp
        ((RetainedSimplex.continuous_chart n m _ (Equiv.refl _)).measurable.comp
          (measurable_const.prodMk measurable_id))).const_mul _
  have hXi (i : Fin (n : ℕ)) : (fun z => Xi i (z+c)) = X i := by
    funext z
    dsimp only [Xi, X, y, e]
    rw [MarginalHessian.compensatedChart_eq_shift]
    rfl
  have hLp (i : Fin (n : ℕ)) : MemLp (Xi i) 2 μ := by
    rw [← hmap]
    apply (memLp_map_measure_iff (hmeas i).aestronglyMeasurable
      (show AEMeasurable (fun z => z+c) ρ from (measurable_id.add_const c).aemeasurable)).mpr
    simpa only [Function.comp_def, hXi] using hX' i
  refine ⟨hLp, fun i j => ?_⟩
  have hcov : ProbabilityTheory.covariance (Xi i) (Xi j) μ =
      ProbabilityTheory.covariance (X i) (X j) ρ := by
    rw [← hmap]
    have ht := ProbabilityTheory.covariance_map_fun
      (μ := ρ) (Z := fun z => z+c) (hmeas i).aestronglyMeasurable
      (hmeas j).aestronglyMeasurable (measurable_id.add_const c).aemeasurable
    simpa only [hXi] using ht
  have hP (i j : Fin (n : ℕ)) : (∫ z, B z (e i) (e j) ∂ρ) =
      GoodBlocks.conditionalHessian β s n m i j x := by
    rw [Internal.shifted_hessian_mean β s n m U hv x ρ hmap]
    simp only [e, PiLp.single_apply, ite_mul, one_mul, zero_mul, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rfl
  have hB (i : Fin (n : ℕ)) : (∫ z, B z (e i) q ∂ρ) =
      ConditionalForces.compensationB β s n m i x := by
    rw [Internal.shifted_hessian_mean β s n m U hv x ρ hmap]
    simp only [e, PiLp.single_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rfl
  have hC : (∫ z, B z q q ∂ρ) = ConditionalForces.compensationC β s n m x := by
    rw [Internal.shifted_hessian_mean β s n m U hv x ρ hmap]
    rfl
  have h := he i j
  change fderiv ℝ (fderiv ℝ (fun t => β.val⁻¹ * V t)) x.val
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      fderiv ℝ (fderiv ℝ (fun t : EuclideanSpace ℝ (Fin (n : ℕ)) =>
        ∑ k, θ.val ((n : ℝ) ^ (-ε) * t k))) x.val
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
      (∫ z, B z (e i) (e j) ∂ρ) - (∫ z, B z (e i) q ∂ρ) -
      (∫ z, B z (e j) q ∂ρ) + (∫ z, B z q q ∂ρ) -
      β.val * ProbabilityTheory.covariance (X i) (X j) ρ at h
  have hVs := (PhysicalFormDomain.proper_gibbs_potential β s n m θ ε).1.contDiffAt
    ((AffineSimplex.isOpen_chartDomain n _).mem_nhds x.property)
  change ContDiffAt ℝ ∞ V x.val at hVs
  have hFs := (PhysicalCore.forcing_smooth n m θ ε).contDiffAt
    ((AffineSimplex.isOpen_chartDomain n _).mem_nhds x.property)
  rw [PhysicalCollision.internal_hessian_const_mul (hVs.of_le (by norm_num)),
    ← Intrinsic.hessianMatrix_eq_second hVs, ← Intrinsic.hessianMatrix_eq_second hFs,
    hP, hB, hB, hC, ← hcov] at h
  dsimp only [PhysicalCore.forcingHessian, ConditionalForces.compensationQ]
  have hb := β.property.ne'
  field_simp at h
  nlinarith only [h]

/-- See Subsection 5.1 of the paper: the expanded signed multiplication part of
the perturbation is exactly the physical Hessian minus the core.
The equality holds pointwise on both freezing branches, before integration.
The Schur correction is an additional bounded nonlocal form. -/
theorem proper_multiplication_defect (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ) :
    let p := ofLong β s
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      β.val * ∑ i, θ.val ((n : ℝ) ^ (-ε) * x i) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal)
    ∃ U : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain ((n : ℕ) + m).succPNat) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) //
          y ∈ gapAmbientDomain ((n : ℕ) + m).succPNat},
        U y.val = β.val * physicalAmbientGapEnergy p ((n : ℕ) + m).succPNat y) ∧
      ∀ x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
        let μ := ProperMarginalChart.conditionalMeasure p n m n.pos (Equiv.refl _) x
        let q := WithLp.toLp 2 (ConditionalForces.compensationVector n m)
        let Xi := fun i z => β.val⁻¹ *
          (fderiv ℝ U (RetainedSimplex.chart n m ((n + m : ℕ) + 1)
            (Equiv.refl _) (x.val,z)) (EuclideanSpace.single (i.castAdd m).castSucc 1) -
           fderiv ℝ U (RetainedSimplex.chart n m ((n + m : ℕ) + 1)
            (Equiv.refl _) (x.val,z)) q)
        (∀ i : Fin (n : ℕ), MemLp (Xi i) 2 μ) ∧
        ∀ (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : (n : ℕ) ≤ (M : ℕ))
          (K : ℕ) (i j : Fin (n : ℕ)),
          hessianMatrix V x.val i j -
            β.val * PhysicalCore.properActive β s n m M hM hnM K θ ε κ₀ x i j =
          β.val * (if x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀ then
              BoundaryEntries.boundaryRemainder β s n m M hM hnM K x i j
            else PhysicalCore.forcingHessian n θ ε x.val i j +
              GoodBlocks.conditionalHessian β s n m i j x -
              2 * referenceIntervalMatrix s M hM K (i.castLE hnM) (j.castLE hnM)) +
          β.val * ConditionalForces.compensationQ β s n m i j x -
          β.val ^ 2 * ProbabilityTheory.covariance (Xi i) (Xi j) μ := by
  intro p V
  obtain ⟨U, hU, hv, h⟩ := proper_hessian_expansion β s n m θ ε
  refine ⟨U, hU, hv, fun x => ?_⟩
  intro μ q Xi
  obtain ⟨hLp, hH⟩ := h x
  refine ⟨hLp, fun M hM hnM K i j => ?_⟩
  have he := PhysicalCore.properActive_defect β s n m M hM hnM K θ ε κ₀ x i j
  rw [hH i j, ← he]
  ring

end Riesz2.PhysicalIdentity
