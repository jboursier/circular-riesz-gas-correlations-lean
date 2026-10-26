/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.IntervalCoefficients
public import Riesz2.HelfferSjostrand.MarginalHessianPart5
public import Riesz2.HelfferSjostrand.PaperMarginalHessian
import all Riesz2.HelfferSjostrand.MarginalHessianPart5

/-!
# Differentiation of the short-range physical marginal

See Lemma 4.7 of the paper: the actual active marginal, with either allowed
penalty, has all-order regularity and a uniform lower Hessian bound.
-/

public section
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace Riesz2.DecayShort.PhysicalFibres

set_option backward.isDefEq.respectTransparency false in
/-- The inverse part of the active penalty is smooth and convex on the
entire retained domain (Appendix B and Lemma 4.7). -/
theorem inverse_retained_penalty (n : ℕ) (L : ℝ) (θ : PhysicalCutoff)
    {a : ℝ} (ha : 0 < a) :
    ContDiffOn ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) =>
      ∑ i, θ.val (a * (x i)⁻¹)) (AffineSimplex.chartDomain n L) ∧
    ConvexOn ℝ (AffineSimplex.chartDomain n L)
      (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, θ.val (a * (x i)⁻¹)) :=
  PaperMarginalHessian.paper_inverse_retained_penalty n L θ ha

set_option backward.isDefEq.respectTransparency false in
/-- See Lemma 4.7 of the paper, both active tilts: all-order regularity and
the global lower Hessian bound, with `A = 1` and `q₀ = s+2` independent
of `h`. The potential is the negative logarithm of the physical marginal
density divided by beta, up to its irrelevant normalizing constant. -/
theorem active_marginal_curvature (p : Parameters) (hs : 1 < p.val.2)
    (n m : ℕ) (hn : 1 ≤ n) (σ : Equiv.Perm (Fin (n + m + 1)))
    (θ : PhysicalCutoff) (h : ℝ) (hh : 0 < h) (b : Bool) :
    let a := ((n : ℝ) ^ h)⁻¹
    let P := fun x : EuclideanSpace ℝ (Fin n) =>
      ∑ i, (θ.val (a * x i) + if b then θ.val (a * (x i)⁻¹) else 0)
    let K := fun x => p.val.1⁻¹ * (p.val.1 * P x -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p n m σ (x,z)).toReal))
    ContDiffOn ℝ ∞ K (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) ∧
      ∀ x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
        ∀ v : EuclideanSpace ℝ (Fin n),
          (n : ℝ) ^ (-(p.val.2 + 2) * h) * ‖v‖ ^ 2 ≤
            fderiv ℝ (fderiv ℝ K) x v v := by
  have hmin : min 1 (p.val.2*(p.val.2+1)) = 1 := min_eq_left (by nlinarith only [hs])
  simpa only [hmin,one_mul] using
    PaperMarginalHessian.paper_marginal_hessian p n m hn σ θ h hh b

set_option backward.isDefEq.respectTransparency false in
/-- Internal bridge for Lemma 4.7: any smooth realization of
beta times the energy has integrable ambient Hessian on every
physical fibre, in all directions. The realization premises identify the
energy. They assume no derivative formula or moment estimate. -/
theorem internal_integrable_ambient_hessian (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    (U : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ)
    (hval : ∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
        y ∈ gapAmbientDomain (n + m).succPNat},
      U y.val = p.val.1 * physicalAmbientGapEnergy p (n + m).succPNat y)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (u v : EuclideanSpace ℝ (Fin (n + m + 1))) :
    Integrable (fun z => fderiv ℝ (fderiv ℝ U)
      (RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ (x.val,z)) u v)
      (ProperMarginalChart.conditionalMeasure p n m hn σ x) := by
  classical
  obtain ⟨W, hW, hv, hj⟩ := PhysicalEnergy.ambient_derivatives p (n + m).succPNat
  change (EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ) at W
  simp only [Nat.succPNat_coe] at hW hv hj
  let inc := (Subtype.val : AffineSimplex.chartDomain m
    (((n + m : ℕ) + 1) - ∑ i, x.val i) → EuclideanSpace ℝ (Fin m))
  rw [← map_measure p n m hn σ x]
  apply (MeasurableEmbedding.subtype_coe
    (AffineSimplex.isOpen_chartDomain _ _).measurableSet).integrable_map_iff.mpr
  have he (z : AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ i, x.val i)) :
      fderiv ℝ (fderiv ℝ U) (configuration n m σ x z).val u v =
        p.val.1 * ∑ t : Fin (n + m + 1) × Fin ((n + m + 1) / 2),
          intervalWeight p (n + m).succPNat t (configuration n m σ x z) *
            (cyclicGapSum (n + m).succPNat t.1 (t.2.val + 1) (WithLp.ofLp u) *
              cyclicGapSum (n + m).succPNat t.1 (t.2.val + 1) (WithLp.ofLp v)) := by
    let y := configuration n m σ x z
    have heq : U =ᶠ[𝓝 y.val] (fun t => p.val.1 * W t) := by
      filter_upwards [(PhysicalEnergy.isOpen_gapAmbientDomain _).mem_nhds y.property] with t ht
      rw [hval ⟨t,ht⟩, hv ⟨t,ht⟩]
    rw [heq.fderiv.fderiv_eq, PhysicalCollision.internal_hessian_const_mul
      ((hW.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain _).mem_nhds y.property)).of_le
        (by norm_num)), (hj y u v).2, Fintype.sum_prod_type]
    rfl
  have hi := (integrable_finsetSum Finset.univ (fun t _ =>
    (integrable_intervalWeight p n m hn σ x t).mul_const
      (cyclicGapSum (n + m).succPNat t.1 (t.2.val + 1) (WithLp.ofLp u) *
        cyclicGapSum (n + m).succPNat t.1 (t.2.val + 1) (WithLp.ofLp v)))).const_mul p.val.1
  exact hi.congr (Eventually.of_forall (fun z => (he z).symm))

/-- See Subsection 4.4 of the paper: the fixed-fibre derivative is the active
coordinate derivative minus uniform exterior compensation. -/
theorem compensated_direction_single (n m : ℕ) (i : Fin n) :
    MarginalHessian.compensatedDirection n m (Equiv.refl _)
      (EuclideanSpace.single i 1) =
        EuclideanSpace.single (i.castAdd m).castSucc 1 -
          WithLp.toLp 2 (Fin.append (fun _ : Fin n => (0 : ℝ))
            (fun _ : Fin (m + 1) => (m + 1 : ℝ)⁻¹)) := by
  ext k
  refine Fin.addCases (m := n) (n := m + 1) (fun j => ?_) (fun j => ?_) k
  · have hret := MarginalHessian.compensatedDirection_retained n m (Equiv.refl _)
      (EuclideanSpace.single i 1) j
    simp only [Equiv.refl_apply] at hret
    rw [show j.castAdd (m + 1) = (j.castAdd m).castSucc from rfl, hret]
    simp only [EuclideanSpace.single, PiLp.single_apply, PiLp.sub_apply,
      show (j.castAdd m).castSucc = j.castAdd (m + 1) from rfl,
      Fin.append, Fin.addCases_left]
    simp only [show (i.castAdd m).castSucc = i.castAdd (m + 1) from rfl,
      Fin.castAdd_inj, sub_zero]
  · have hext := MarginalHessian.compensatedDirection_exterior n m (Equiv.refl _)
      (EuclideanSpace.single i 1) j
    simp only [Equiv.refl_apply] at hext
    rw [hext]
    have hne : j.natAdd n ≠ (i.castAdd m).castSucc := by
      intro hij
      have hvals := congrArg Fin.val hij
      simp only [Fin.val_natAdd, Fin.val_castSucc, Fin.val_castAdd] at hvals
      omega
    simp [EuclideanSpace.single, PiLp.single_apply, Fin.append, hne, div_eq_mul_inv]

set_option backward.isDefEq.respectTransparency false in
/-- Internal translation bridge: every ambient energy Hessian is integrable
also on the fixed compensated hyperplane used in Lemma 4.7. -/
theorem internal_integrable_shifted_hessian (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (U : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ)
    (hv : ∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
        y ∈ gapAmbientDomain (n + m).succPNat},
      U y.val = p.val.1 * physicalAmbientGapEnergy p (n + m).succPNat y)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (ρ : Measure (EuclideanSpace ℝ (Fin m)))
    (hmap : ρ.map (fun z => z + AffineSimplex.coordinates m
        (AffineSimplex.centre m (((n + m : ℕ) + 1) - ∑ i, x.val i))) =
      ProperMarginalChart.conditionalMeasure p n m hn (Equiv.refl _) x)
    (u v : EuclideanSpace ℝ (Fin (n + m + 1))) :
    Integrable (fun z => fderiv ℝ (fderiv ℝ U)
      (MarginalHessian.compensatedChart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) u v) ρ := by
  let c := AffineSimplex.coordinates m
    (AffineSimplex.centre m (((n + m : ℕ) + 1) - ∑ i, x.val i))
  have he := internal_integrable_ambient_hessian p n m hn (Equiv.refl _) U hv x u v
  rw [← hmap] at he
  have he' := he.comp_measurable (measurable_id.add_const c)
  convert he' using 1
  funext z
  congr 1
  rw [MarginalHessian.compensatedChart_eq_shift]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- See Lemma 4.7 of the paper, the compensated Hessian identity. All separated
ambient Hessians are integrable and all compensated scores belong to L².
The exterior law is written in its fixed centred chart. Its translation
is proved to equal the actual physical conditional law. `B` and `Xi` are
respectively the Hessian and compensated force of the unscaled energy,
whose beta-scaled smooth realization is `U`. -/
theorem active_marginal_hessian (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a) (b : Bool) :
    let F := fun x : EuclideanSpace ℝ (Fin n) =>
      ∑ i, (θ.val (a * x i) + if b then θ.val (a * (x i)⁻¹) else 0)
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
  intro F K
  obtain ⟨U, hU, hv, hsm, hmain⟩ :=
    MarginalHessian.physical_penalized_compensated_marginal_calculus p n m hn
      (Equiv.refl _) θ ha Finset.univ b
  refine ⟨U, hU, hv, contDiffOn_const.mul hsm, fun x => ?_⟩
  intro c₀
  let ρ := AffineFibre.normalizedMeasure volume
    (fun z => ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x.val,z+c₀))
    (by rw [lintegral_add_right_eq_self
      (fun z : EuclideanSpace ℝ (Fin m) => ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x.val,z)) c₀]; exact
      (ProperMarginalChart.fibre_mass p n m hn (Equiv.refl _) x.property).1)
    (by rw [lintegral_add_right_eq_self
      (fun z : EuclideanSpace ℝ (Fin m) => ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x.val,z)) c₀]; exact
      (ProperMarginalChart.fibre_mass p n m hn (Equiv.refl _) x.property).2)
  have hρ : IsProbabilityMeasure ρ := by
    dsimp only [ρ]
    apply AffineFibre.isProbabilityMeasure_normalizedMeasure volume
    exact (ProperMarginalChart.measurable_chartDensity p n m (Equiv.refl _)).comp
      (measurable_const.prodMk (measurable_id.add_const c₀))
  obtain ⟨hmap, hL2, hTi, hderiv, _⟩ := hmain x
  refine ⟨ρ, hρ, hmap, ?_⟩
  intro y q e B Xi
  have hBi (u v) : Integrable (fun z => B z u v) ρ :=
    (internal_integrable_shifted_hessian p n m hn U hv x ρ hmap u v).const_mul p.val.1⁻¹
  have hsupp := ConditionalEnergyMoments.physical_conditional_support p n m hn (Equiv.refl _) x
  rw [← hmap] at hsupp
  have hy : ∀ᵐ z ∂ρ, y z ∈ gapAmbientDomain (n + m).succPNat := by
    filter_upwards [ae_of_ae_map (measurable_id.add_const c₀).aemeasurable hsupp] with z hz
    change MarginalHessian.compensatedChart n m ((n + m : ℕ) + 1)
      (Equiv.refl _) (x.val,z) ∈ gapAmbientDomain (n + m).succPNat
    rw [MarginalHessian.compensatedChart_eq_shift]
    change RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _)
      (x.val,z+c₀) ∈ gapAmbientDomain (n + m).succPNat
    exact (configuration n m (Equiv.refl _) x ⟨z+c₀,hz⟩).property
  let H := fun z t => U (MarginalHessian.compensatedChart n m
    ((n + m : ℕ) + 1) (Equiv.refl _) (t,z))
  have hjets : ∀ᵐ z ∂ρ, ∀ i j : Fin n,
      fderiv ℝ (H z) x.val (EuclideanSpace.single i 1) =
          fderiv ℝ U (y z) (e i) - fderiv ℝ U (y z) q ∧
      fderiv ℝ (fderiv ℝ (H z)) x.val (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) =
        fderiv ℝ (fderiv ℝ U) (y z) (e i) (e j) -
        fderiv ℝ (fderiv ℝ U) (y z) (e i) q -
        fderiv ℝ (fderiv ℝ U) (y z) (e j) q +
        fderiv ℝ (fderiv ℝ U) (y z) q q := by
    filter_upwards [hy] with z hz
    intro i j
    have hUz := (hU.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain _).mem_nhds hz))
    obtain ⟨hg, hh⟩ := MarginalHessian.internal_compensated_energy_derivatives n m
      ((n + m : ℕ) + 1) (Equiv.refl _) x.val z (hUz.of_le (by norm_num))
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    rw [compensated_direction_single n m i] at hg hh
    rw [compensated_direction_single n m j] at hh
    constructor
    · simpa only [map_sub] using hg
    · simp only [map_sub, sub_apply] at hh
      rw [hUz.isSymmSndFDerivAt (by norm_num) q (e j)] at hh
      exact hh.trans (by ring)
  have hXi (i) : (fun z => Xi i z) =ᵐ[ρ]
      (fun z => p.val.1⁻¹ * fderiv ℝ (H z) x.val (EuclideanSpace.single i 1)) :=
    hjets.mono fun z hz => congrArg (fun t : ℝ => p.val.1⁻¹ * t) (hz i i).1.symm
  refine ⟨hBi, fun i => MemLp.ae_eq (hXi i).symm
    ((hL2 (EuclideanSpace.single i 1)).const_mul p.val.1⁻¹), fun i j => ?_⟩
  let ei := EuclideanSpace.single i (1 : ℝ)
  let ej := EuclideanSpace.single j (1 : ℝ)
  have hKx : ContDiffAt ℝ 2 (fun x => p.val.1 * F x -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal)) x.val :=
    hsm.contDiffAt ((AffineSimplex.isOpen_chartDomain n _).mem_nhds x.property) |>.of_le (by norm_num)
  have hcov : ProbabilityTheory.covariance (Xi i) (Xi j) ρ =
      p.val.1⁻¹ * (p.val.1⁻¹ * ProbabilityTheory.covariance
        (fun z => fderiv ℝ (H z) x.val ei) (fun z => fderiv ℝ (H z) x.val ej) ρ) := by
    have hc : ProbabilityTheory.covariance (Xi i) (Xi j) ρ =
        ProbabilityTheory.covariance
          (fun z => p.val.1⁻¹ * fderiv ℝ (H z) x.val ei)
          (fun z => p.val.1⁻¹ * fderiv ℝ (H z) x.val ej) ρ := by
      unfold ProbabilityTheory.covariance
      rw [integral_congr_ae (hXi i), integral_congr_ae (hXi j)]
      apply integral_congr_ae
      filter_upwards [hXi i, hXi j] with z hi hj
      rw [hi, hj]
    rw [hc, ProbabilityTheory.covariance_const_mul_left,
      ProbabilityTheory.covariance_const_mul_right]
  have hmean : p.val.1⁻¹ * (∫ z, fderiv ℝ (fderiv ℝ (H z)) x.val ei ej ∂ρ) =
      (∫ z, B z (e i) (e j) ∂ρ) - (∫ z, B z (e i) q ∂ρ) -
      (∫ z, B z (e j) q ∂ρ) + (∫ z, B z q q ∂ρ) := by
    rw [← integral_const_mul]
    have heq : (fun z => p.val.1⁻¹ * fderiv ℝ (fderiv ℝ (H z)) x.val ei ej) =ᵐ[ρ]
        (fun z => B z (e i) (e j) - B z (e i) q - B z (e j) q + B z q q) := by
      filter_upwards [hjets] with z hz
      rw [(hz i j).2]
      dsimp only [B]
      ring
    rw [integral_congr_ae heq]
    have h₁ := integral_add (((hBi (e i) (e j)).sub (hBi (e i) q)).sub (hBi (e j) q))
      (hBi q q)
    have h₂ := integral_sub ((hBi (e i) (e j)).sub (hBi (e i) q)) (hBi (e j) q)
    simp only [Pi.sub_apply] at h₁ h₂
    rw [h₁, h₂, integral_sub (hBi (e i) (e j)) (hBi (e i) q)]
  change fderiv ℝ (fderiv ℝ (fun x => p.val.1⁻¹ * (p.val.1 * F x - _))) x.val ei ej = _
  have hd : fderiv ℝ (fderiv ℝ (fun x => p.val.1 * F x -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal))) x.val ei ej =
      p.val.1 * fderiv ℝ (fderiv ℝ F) x.val ei ej +
        (∫ z, fderiv ℝ (fderiv ℝ (H z)) x.val ei ej ∂ρ) -
        ProbabilityTheory.covariance (fun z => fderiv ℝ (H z) x.val ei)
          (fun z => fderiv ℝ (H z) x.val ej) ρ := (hderiv ei ej).2
  rw [PhysicalCollision.internal_hessian_const_mul hKx, hd]
  rw [hcov, mul_sub, mul_add, hmean, inv_mul_cancel_left₀ p.property.1.ne',
    mul_inv_cancel_left₀ p.property.1.ne']
  ring

/-- See Lemma 4.7 of the paper, all clauses, for both active tilts. The
explicit global curvature gives `A = 1` and `q₀ = s+2`, uniformly in all
volumes and independently of `h`. The fixed centred exterior law is
identified with the physical conditional, and the displayed identity is
`H = F'' + P - bᵢ - bⱼ + c - beta Cov(Xiᵢ,Xiⱼ)`.

The parameterization `N = n+m+1` includes every proper retained set and
in particular the ranges `N ≥ 4`, `1 ≤ n ≤ N/2`. -/
theorem fixed_exterior_differentiation (p : Parameters) (hs : 1 < p.val.2) (n m : ℕ) (hn : 1 ≤ n)
    (θ : PhysicalCutoff) (h : ℝ) (hh : 0 < h) (b : Bool) :
    let a := ((n : ℝ) ^ h)⁻¹
    let F := fun x : EuclideanSpace ℝ (Fin n) =>
      ∑ i, (θ.val (a * x i) + if b then θ.val (a * (x i)⁻¹) else 0)
    let K := fun x => p.val.1⁻¹ * (p.val.1 * F x -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal))
    ∃ U : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain (n + m).succPNat) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
          y ∈ gapAmbientDomain (n + m).succPNat},
        U y.val = p.val.1 * physicalAmbientGapEnergy p (n + m).succPNat y) ∧
      ContDiffOn ℝ ∞ K (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) ∧
      (∀ x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
        ∀ v : EuclideanSpace ℝ (Fin n),
          (n : ℝ) ^ (-(p.val.2 + 2) * h) * ‖v‖ ^ 2 ≤
            fderiv ℝ (fderiv ℝ K) x v v) ∧
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
  intro a F K
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : 0 < a := inv_pos.mpr (Real.rpow_pos_of_pos hnpos h)
  obtain ⟨U, hU, hv, hsm, hmain⟩ := active_marginal_hessian p n m hn θ ha b
  obtain ⟨_, hcurv⟩ := active_marginal_curvature p hs n m hn (Equiv.refl _) θ h hh b
  exact ⟨U, hU, hv, hsm, hcurv, hmain⟩

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 4.4 and Lemma 4.7 of the paper: the potential in
`fixed_exterior_differentiation` is exactly minus beta inverse times the
logarithm of the physical penalized fibre density. The finite positive
fibre mass and `ProperMarginalChart.activeTiltedGapLaw_density` identify
this with the active marginal, up to a normalizing constant. -/
theorem active_marginal_potential_density (p : Parameters) (n : ℕ+) (m : ℕ)
    (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ))
    (θ : PhysicalCutoff) (h : ℝ) (b : Bool)
    {x : EuclideanSpace ℝ (Fin (n : ℕ))}
    (hx : x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
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
  classical
  intro D
  change (n : ℕ) ≤ (n : ℕ) + m + 1 at hn
  let J : Finset (Fin ((n : ℕ) + m + 1)) := Finset.univ.map (Fin.castLEEmb hn)
  have hJ : ∀ i ∈ J, ∃ j : Fin (n : ℕ), i = (Equiv.refl _) (j.castAdd m).castSucc := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    exact ⟨j, Fin.ext rfl⟩
  let F := ∑ i : Fin (n : ℕ), (θ.val ((n : ℝ) ^ (-h) * x i) +
    if b then θ.val ((n : ℝ) ^ (-h) * (x i)⁻¹) else 0)
  have hsum : (∑ i ∈ J,
      (θ.val ((n : ℝ) ^ (-h) * RetainedSimplex.chart n m ((n + m : ℕ) + 1)
        (Equiv.refl _) (x,0) i) +
        if b then θ.val ((n : ℝ) ^ (-h) * (RetainedSimplex.chart n m ((n + m : ℕ) + 1)
          (Equiv.refl _) (x,0) i)⁻¹) else 0)) = F := by
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro i _
    rw [show Fin.castLEEmb hn i = (Equiv.refl _) (i.castAdd m).castSucc from Fin.ext rfl,
      RetainedSimplex.chart_retained]
  have hmass : AffineFibre.fibreMass volume D x =
      ENNReal.ofReal (Real.exp (-p.val.1 * F)) *
        AffineFibre.fibreMass volume (ProperMarginalChart.chartDensity p n m (Equiv.refl _)) x := by
    change (∫⁻ z : EuclideanSpace ℝ (Fin m),
      ProperMarginalChart.penalizedChartDensity p n m (Equiv.refl _) θ
        ((n : ℝ) ^ (-h)) J b (x,z)) = _
    simp_rw [ProperMarginalChart.penalizedChartDensity_eq_mul p n m (Equiv.refl _)
      θ ((n : ℝ) ^ (-h)) J b hJ, hsum]
    exact lintegral_const_mul _ ((ProperMarginalChart.measurable_chartDensity p n m
      (Equiv.refl _)).comp measurable_prodMk_left)
  obtain ⟨h0, ht⟩ := ProperMarginalChart.penalized_fibre_mass p n m n.pos
    (Equiv.refl _) θ ((n : ℝ) ^ (-h)) J b hJ hx
  have hpos := (MarginalHessian.physical_marginal_normalizer p n m n.pos (Equiv.refl _) hx).2
  refine ⟨h0, ht, ?_⟩
  rw [hmass, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _),
    ← (MarginalHessian.physical_marginal_normalizer p n m n.pos (Equiv.refl _) hx).1,
    Real.log_mul (Real.exp_ne_zero _) hpos.ne', Real.log_exp]
  dsimp only [F]
  rw [Real.rpow_neg (show (0 : ℝ) ≤ n from le_of_lt (by exact_mod_cast n.pos))]
  ring

end Riesz2.DecayShort.PhysicalFibres
