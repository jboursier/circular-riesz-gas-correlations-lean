/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.PhysicalFibresPart2
public import Riesz2.HelfferSjostrand.PhysicalCollisionPart2
public import Riesz2.Frozen.OfLong

/-!
# Moving physical fibres

See Subsection 5.1 of the paper. The compensated calculus is valid for every
physical exponent, so its long-range specialization uses the same charts,
conditional probabilities, and ambient energy. Here `N = n + m + 1`.
The parameter `m` is the dimension of the exterior fibre, whose number of gaps is `m + 1`.
The displayed potential differs from the normalized density potential by
an additive constant, identified by `moving_fibre_density` below.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

namespace Riesz2.MovingFibre

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 5.1 of the paper, proper-marginal clause, in the constant-volume
centred exterior chart. The four mean Hessians are `P_ij`, `b_i`, `b_j`,
and `c`. The compensated forces are `Xi`. All four expectations and the
covariance are finite. The translated exterior probability is the literal
physical conditional. This also covers proper marginals larger than half
the volume and arbitrary real cutoff scales. -/
theorem moving_fibre (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n m : ℕ) (hn : 1 ≤ n) (θ : PhysicalCutoff) (ε : ℝ) :
    let p := ofLong β s
    let a := (n : ℝ) ^ (-ε)
    let F := fun x : EuclideanSpace ℝ (Fin n) =>
      ∑ i, θ.val (a * x i)
    let K := fun x => p.val.1⁻¹ * (p.val.1 * F x -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal))
    ∃ U : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain (n + m).succPNat) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
          y ∈ gapAmbientDomain (n + m).succPNat},
        U y.val = p.val.1 * physicalAmbientGapEnergy p (n + m).succPNat y) ∧
      ContDiffOn ℝ ∞ K (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) ∧
      ∀ x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
        let c₀ := AffineSimplex.coordinates m
          (AffineSimplex.centre m (((n + m : ℕ) + 1) - ∑ i, x.val i))
        ∃ ρ : Measure (EuclideanSpace ℝ (Fin m)),
          IsProbabilityMeasure ρ ∧
          ρ.map (fun z => z+c₀) =
            ProperMarginalChart.conditionalMeasure p n m hn (Equiv.refl _) x ∧
          let y := fun z => MarginalHessian.compensatedChart n m
            ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)
          let q := WithLp.toLp 2 (Fin.append (fun _ : Fin n => (0 : ℝ))
            (fun _ : Fin (m + 1) => (m + 1 : ℝ)⁻¹))
          let e := fun i : Fin n => EuclideanSpace.single (i.castAdd m).castSucc (1 : ℝ)
          let B := fun z u v => p.val.1⁻¹ * fderiv ℝ (fderiv ℝ U) (y z) u v
          let Xi := fun i z => p.val.1⁻¹ * (fderiv ℝ U (y z) (e i) - fderiv ℝ U (y z) q)
          (∀ u v, Integrable (fun z => B z u v) ρ) ∧
          (∀ i, MemLp (Xi i) 2 ρ) ∧
          ∀ i j : Fin n,
            fderiv ℝ (fderiv ℝ K) x.val (EuclideanSpace.single i 1)
                (EuclideanSpace.single j 1) =
              fderiv ℝ (fderiv ℝ F) x.val (EuclideanSpace.single i 1)
                (EuclideanSpace.single j 1) +
              (∫ z, B z (e i) (e j) ∂ρ) - (∫ z, B z (e i) q ∂ρ) -
              (∫ z, B z (e j) q ∂ρ) + (∫ z, B z q q ∂ρ) -
              p.val.1 * ProbabilityTheory.covariance (Xi i) (Xi j) ρ := by
  intro p a F K
  have ha : 0 < a := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  simpa only [F, K, Bool.false_eq_true, ↓reduceIte, add_zero] using
    DecayShort.PhysicalFibres.active_marginal_hessian p n m hn θ ha false

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 5.1 of the paper: identification with the active tilted
law via its actual positive finite fibre density. The potential is minus
the logarithm of that density divided by inverse temperature. The additive
normalizing constant has no effect on its Hessian. -/
theorem moving_fibre_density (β : InverseTemperature) (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ))
    (θ : PhysicalCutoff) (h : ℝ) (b : Bool)
    {x : EuclideanSpace ℝ (Fin (n : ℕ))}
    (hx : x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    let p := ofLong β s
    let D := ProperMarginalChart.penalizedChartDensity p n m (Equiv.refl _) θ
      ((n : ℝ) ^ (-h)) (Finset.univ.map (Fin.castLEEmb hn)) b
    AffineFibre.fibreMass volume D x ≠ 0 ∧
      AffineFibre.fibreMass volume D x ≠ ⊤ ∧
      p.val.1⁻¹ * (p.val.1 * ∑ i : Fin (n : ℕ),
        (θ.val (((n : ℝ) ^ h)⁻¹ * x i) +
          if b then θ.val (((n : ℝ) ^ h)⁻¹ * (x i)⁻¹) else 0) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal)) =
        -p.val.1⁻¹ * Real.log (AffineFibre.fibreMass volume D x).toReal := by
  intro p
  exact DecayShort.PhysicalFibres.active_marginal_potential_density p n m hn θ h b hx

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 5.1 of the paper, full-cycle clause. The ambient extension is
literally the forcing plus the physical energy. Its Hessian is their
sum in every ambient direction. The intrinsic Gibbs certificate identifies
the full tilted law and supplies its finite positive normalizer. -/
theorem moving_fibre_full (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (θ : PhysicalCutoff) (ε : ℝ) :
    let p := ofLong β s
    let F := fun y : EuclideanSpace ℝ (Fin (N : ℕ)) =>
      ∑ i, θ.val ((N : ℝ) ^ (-ε) * y i)
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ContDiffOn ℝ ∞ (fun y => F y + W y) (gapAmbientDomain N) ∧
      IsEuclideanGibbsPotential volume (fullIntrinsicTiltedGapLaw p N θ ε false)
        (intrinsicGapDomain N) (fun z : gapTangentSpace N =>
          p.val.1 * (F (WithLp.toLp 2 (fun i => 1 + z.val i)) +
            W (WithLp.toLp 2 (fun i => 1 + z.val i)))) ∧
      ∀ y ∈ gapAmbientDomain N, ∀ u v : EuclideanSpace ℝ (Fin (N : ℕ)),
        fderiv ℝ (fderiv ℝ (fun y => F y + W y)) y u v =
          fderiv ℝ (fderiv ℝ F) y u v + fderiv ℝ (fderiv ℝ W) y u v := by
  intro p F
  obtain ⟨W, hW, hv, _⟩ := PhysicalEnergy.ambient_derivatives p N
  have hF : ContDiffOn ℝ ∞ F (gapAmbientDomain N) := by
    apply ContDiffOn.sum
    intro i _ y hy
    have hi : 0 < y i := by
      have hh := (hy i 1 (by omega) (by omega)).1
      simpa only [PhysicalEnergy.gapSum_one] using hh
    exact ((PhysicalCollision.cutoff_contDiffAt θ
      (mul_pos (Real.rpow_pos_of_pos (by exact_mod_cast N.pos) _) hi)).comp y
        (contDiffAt_const.mul (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt)).contDiffWithinAt
  have hval : ∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
      p.val.1 * (F y.val + W y.val) = fullPhysicalPotentialValue p N hN θ ε false y := by
    intro y
    simp only [fullPhysicalPotentialValue, Bool.false_eq_true, ↓reduceIte, add_zero, F, hv]
    ring
  refine ⟨W, hW, hv, hF.add hW,
    PhysicalCollision.internal_full_gap_gibbs N p hN θ ε false
      (fun y => p.val.1 * (F y + W y)) (contDiffOn_const.mul (hF.add hW)) hval, ?_⟩
  intro y hy u v
  exact PhysicalCollision.internal_hessian_add
    ((hF.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hy)).of_le (by norm_num))
    ((hW.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hy)).of_le (by norm_num)) u v

end Riesz2.MovingFibre
