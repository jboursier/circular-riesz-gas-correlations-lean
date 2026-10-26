/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.MarginalHessianPart5
import all Riesz2.HelfferSjostrand.MarginalHessianPart5
public import Riesz2.HelfferSjostrand.ConditionalEnergyMomentsPart3
public import Riesz2.HelfferSjostrand.PhysicalCollisionPart2
public import Riesz2.HelfferSjostrand.ElementaryBarriers
public import Riesz2.ToMathlib.MarginalBarrierSubtraction

/-!
# Collision bounds for proper physical marginals

See Appendix A of the paper, on the retained-coordinate marginal density.
The exterior dimension is `m`. Its number of gaps is `m + 1`, including
point fibres at `m = 0`. All constants concern fixed volume and parameters.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace Riesz2.MarginalCollision

/-- Internal exterior-coordinate identity for Appendix A. -/
theorem internal_sum_split (n m : ℕ) (L : ℝ)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    (q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) (f : ℝ → ℝ) :
    (∑ a, f (RetainedSimplex.chart n m L σ q a)) =
      (∑ i, f (q.1 i)) +
        ∑ a : Fin (m + 1), f (RetainedSimplex.chart n m L σ q (σ (a.natAdd n))) := by
  rw [← Equiv.sum_comp σ]
  change (∑ a : Fin (n + (m + 1)), f (RetainedSimplex.chart n m L σ q (σ a))) = _
  rw [Fin.sum_univ_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg f (RetainedSimplex.chart_retained n m L σ q.1 q.2 i)

/-- Internal constant-mass identity for the exterior coordinates. -/
theorem internal_exterior_mass (n m : ℕ) (L : ℝ)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    {q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)}
    (hq : q ∈ RetainedSimplex.domain n m L) :
    (∑ a : Fin (m + 1), RetainedSimplex.chart n m L σ q (σ (a.natAdd n))) =
      L - ∑ i, q.1 i := by
  have hs := ((RetainedSimplex.chart_mem_simplex n m L σ q).mpr hq).2
  have ht := internal_sum_split n m L σ q id
  simp only [id_eq] at ht
  rw [ht] at hs
  linarith

/-- Internal convexity step of Appendix A: the joint residual
remaining after removing the active face barriers and the exterior mass
barrier is convex, including the two-particle and point-fibre cases. -/
theorem internal_joint_residual_convex (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) :
    ∃ W : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain (n + m).succPNat) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
          y ∈ gapAmbientDomain (n + m).succPNat},
        W y.val = physicalAmbientGapEnergy p (n + m).succPNat y) ∧
      ConvexOn ℝ (RetainedSimplex.domain n m ((n + m : ℕ) + 1))
        (fun q => p.val.1 * W (RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ q) -
          2 * p.val.1 * ((∑ i, (q.1 i) ^ (-p.val.2)) +
            (((n + m : ℕ) + 1) - ∑ i, q.1 i) ^ (-p.val.2))) := by
  obtain ⟨W, hW, hv, hc⟩ := RemovableGapBarrier.nearest_gap_barrier_convex p
    (n + m).succPNat (by simp only [Nat.succPNat_coe]; omega)
  let L : ℝ := ((n + m : ℕ) + 1)
  let Q := RetainedSimplex.domain n m L
  let c := RetainedSimplex.chart n m L σ
  have hs (q) (hq : q ∈ Q) :
      WithLp.ofLp (c q) ∈ Riesz1.gapSimplex (n + m).succPNat := by
    have h := (RetainedSimplex.chart_mem_simplex n m L σ q).mpr hq
    exact ⟨h.1, by simpa only [Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, L, c] using h.2⟩
  have hrem : ConvexOn ℝ Q (fun q => W (c q) - 2 * ∑ a, (c q a) ^ (-p.val.2)) := by
    refine ⟨RetainedSimplex.convex_domain n m L, fun q hq r hr a b ha hb hab => ?_⟩
    change W (c (a • q + b • r)) - _ ≤ _
    rw [show c (a • q + b • r) = a • c q + b • c r from
      RetainedSimplex.chart_convex_combination n m L σ q r hab]
    exact hc.2 (hs q hq) (hs r hr) ha hb hab
  let e := fun (q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))
    (a : Fin (m + 1)) => c q (σ (a.natAdd n))
  have hepos (q) (hq : q ∈ Q) : ∀ a : Fin (m + 1), 0 < e q a :=
    fun a => (hs q hq).1 _
  have hecomb (q r) (a b : ℝ) (hab : a + b = 1) :
      e (a • q + b • r) = a • e q + b • e r := by
    funext i
    simp only [e, c, RetainedSimplex.chart_convex_combination n m L σ q r hab,
      PiLp.add_apply, PiLp.smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hmass : ConvexOn ℝ Q (fun q => (∑ a : Fin (m + 1), (e q a) ^ (-p.val.2)) -
      (∑ a : Fin (m + 1), e q a) ^ (-p.val.2)) := by
    refine ⟨RetainedSimplex.convex_domain n m L, fun q hq r hr a b ha hb hab => ?_⟩
    have hh := (ElementaryBarriers.convexOn_exterior_mass_barrier
      (m := m + 1) (by omega) p.property.2.1).2 (hepos q hq) (hepos r hr) ha hb hab
    rw [← hecomb q r a b hab] at hh
    exact hh
  refine ⟨W, hW, hv, ?_⟩
  apply ((hrem.add (hmass.smul (by norm_num : (0 : ℝ) ≤ 2))).smul p.property.1.le).congr
  intro q hq
  dsimp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, c, e]
  rw [internal_sum_split n m L σ q (fun t => t ^ (-p.val.2)),
    internal_exterior_mass n m L σ hq]
  ring

/-- Internal bridge to the physical density, independent of the choice of
smooth realization of the energy. -/
theorem internal_chart_density_real (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    {W : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ}
    (hv : ∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
        y ∈ gapAmbientDomain (n + m).succPNat},
      W y.val = physicalAmbientGapEnergy p (n + m).succPNat y)
    (q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :
    (ProperMarginalChart.chartDensity p n m σ q).toReal =
      (RetainedSimplex.domain n m ((n + m : ℕ) + 1)).indicator
        (fun q => Real.exp (-p.val.1 * W
          (RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ q))) q := by
  classical
  by_cases hq : q ∈ RetainedSimplex.domain n m ((n + m : ℕ) + 1)
  · have hy := (RetainedSimplex.chart_mem_simplex n m _ σ q).mpr hq
    simp only [ProperMarginalChart.chartDensity, indicator_of_mem hq,
      ProperMarginalChart.density, dite_eq_left hy, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
    rw [hv ⟨_, ProperMarginalChart.simplex_ambient _ hy⟩]
  · simp only [ProperMarginalChart.chartDensity, indicator_of_notMem hq, ENNReal.toReal_zero]

/-- See Appendix A of the paper, the full removable-barrier decomposition of every
unforced proper marginal. The convex remainder is the actual negative log
marginal minus the displayed barriers. Smoothness is also concluded. -/
theorem marginal_barrier_decomposition (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) :
    let V := fun x => -Real.log (∫ z : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p n m σ (x,z)).toReal)
    ∃ R : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiffOn ℝ ∞ R (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) ∧
      ConvexOn ℝ (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) R ∧
      ∀ x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
        V x = 2 * p.val.1 * (∑ i, (x i) ^ (-p.val.2)) +
          2 * p.val.1 * (((n + m : ℕ) + 1) - ∑ i, x i) ^ (-p.val.2) + R x := by
  intro V
  let B := fun x : EuclideanSpace ℝ (Fin n) =>
    2 * p.val.1 * ((∑ i, (x i) ^ (-p.val.2)) +
      (((n + m : ℕ) + 1) - ∑ i, x i) ^ (-p.val.2))
  obtain ⟨W, hW, hv, hc⟩ := internal_joint_residual_convex p n m hn σ
  have hconv := MarginalBarrier.convex_subtraction
    (RetainedSimplex.isOpen_domain n m _) (RetainedSimplex.convex_domain n m _)
    (RetainedSimplex.isBounded_domain n m _)
    (fun q => p.val.1 * W (RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ q)) B hc
  rw [RetainedSimplex.fst_image_domain] at hconv
  have he : (fun x => -Real.log (∫ z : EuclideanSpace ℝ (Fin m),
      (RetainedSimplex.domain n m ((n + m : ℕ) + 1)).indicator
        (fun q => Real.exp (-(p.val.1 * W (RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ q))))
        (x,z)) - B x) = fun x => V x - B x := by
    funext x
    simp only [V, internal_chart_density_real p n m σ hv, neg_mul]
  rw [he] at hconv
  have hB : ContDiffOn ℝ ∞ B (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) := by
    apply contDiffOn_const.mul
    apply ContDiffOn.add
    · apply ContDiffOn.sum
      intro i _
      exact (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffOn.rpow_const_of_ne
        (fun x hx => (hx.1 i).ne')
    · have hL : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin n) =>
          ((n + m : ℕ) + 1) - ∑ i, x i) :=
        contDiff_const.sub (ContDiff.sum fun i _ => (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff)
      exact hL.contDiffOn.rpow_const_of_ne (fun x hx => (sub_pos.mpr hx.2).ne')
  refine ⟨fun x => V x - B x,
    (MarginalHessian.physical_marginal_potential_smooth p n m hn σ).sub hB, hconv, ?_⟩
  intro x _
  dsimp only [B]
  ring

/-- Affine face coordinates of the proper marginal domain. The extra face
is the remaining exterior mass, rather than an exterior gap coordinate. -/
def face (n : ℕ) (L : ℝ) : Option (Fin n) → EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] ℝ
  | none => AffineMap.const ℝ _ L -
      (∑ i : Fin n, (EuclideanSpace.proj (𝕜 := ℝ) i).toLinearMap).toAffineMap
  | some i => (EuclideanSpace.proj (𝕜 := ℝ) i).toLinearMap.toAffineMap

theorem face_none (n : ℕ) (L : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    face n L none x = L - ∑ i, x i := by simp [face]

theorem face_some (n : ℕ) (L : ℝ) (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    face n L (some i) x = x i := rfl

/-- The finite face description is exactly the proper domain. -/
theorem domain_eq_faces (n : ℕ) (L : ℝ) :
    AffineSimplex.chartDomain n L = {x | ∀ i, 0 < face n L i x} := by
  ext x
  simp only [AffineSimplex.chartDomain, mem_ofPred_eq, Option.forall,
    face_none, face_some, sub_pos]
  exact and_comm

/-- The minimum in Appendix A includes both the active gap faces
and the exterior-mass face. It is strictly positive at every interior point. -/
theorem minimum_face_pos (n : ℕ) (L : ℝ) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ AffineSimplex.chartDomain n L) :
    0 < ⨅ i, face n L i x := by
  obtain ⟨i, hi⟩ := ElementaryBarriers.exists_iInf_eq_apply (fun i => face n L i x)
  rw [hi]
  exact (domain_eq_faces n L ▸ hx) i

/-- The face minimum is the displayed `min (minᵢ xᵢ) L` in Appendix A. The nonempty retained set prevents an empty infimum. -/
theorem minimum_face_eq (n : ℕ) (hn : 1 ≤ n) (L : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    (⨅ i, face n L i x) = min (⨅ i, x i) (L - ∑ i, x i) := by
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  apply le_antisymm
  · apply le_min
    · apply le_ciInf
      intro i
      exact ciInf_le (Finite.bddBelow_range (fun j => face n L j x)) (some i)
    · simpa only [face_none] using
        ciInf_le (Finite.bddBelow_range (fun j => face n L j x)) none
  · apply le_ciInf
    intro i
    cases i with
    | none => simpa only [face_none] using min_le_right (⨅ i, x i) (L - ∑ i, x i)
    | some i => exact (min_le_left _ _).trans (ciInf_le (Finite.bddBelow_range _) i)

/-- See Appendix A of the paper, the boundary gradient lower bound for every
unforced proper marginal, with constants independent of its interior point. -/
theorem marginal_gradient_lower (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
        c * (min (⨅ i, x i) (((n + m : ℕ) + 1) - ∑ i, x i)) ^ (-p.val.2 - 1) - C ≤
          ‖gradient (fun t => -Real.log (∫ z : EuclideanSpace ℝ (Fin m),
            (ProperMarginalChart.chartDensity p n m σ (t,z)).toReal)) x‖ := by
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨R, hRs, hRc, he⟩ := marginal_barrier_decomposition p n m hn σ
  have hsum (x : EuclideanSpace ℝ (Fin n)) :
      (∑ j, (2 * p.val.1) * (face n ((n + m : ℕ) + 1) j x) ^ (-p.val.2)) =
        2 * p.val.1 * (∑ i, (x i) ^ (-p.val.2)) +
          2 * p.val.1 * (((n + m : ℕ) + 1) - ∑ i, x i) ^ (-p.val.2) := by
    rw [Fintype.sum_option]
    simp only [face_none, face_some, ← Finset.mul_sum]
    ring
  obtain ⟨c, C, hc, hC, hg⟩ := ElementaryBarriers.radial_gradient_lower
    (face n ((n + m : ℕ) + 1)) (fun _ => 2 * p.val.1)
    (fun _ => mul_pos (by norm_num) p.property.1) p.property.2.1
    (domain_eq_faces n _) (AffineSimplex.isBounded_chartDomain n _)
    R hRc hRs (fun t => -Real.log (∫ z : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p n m σ (t,z)).toReal))
      (fun x hx => by rw [hsum]; exact he x hx)
  refine ⟨c, C, hc, hC, fun x hx => ?_⟩
  simpa only [minimum_face_eq n hn] using hg x hx

/-- Internal affine barrier Hessian, evaluated only where every face is
positive. This is the second-order form of the radial calculus. -/
theorem internal_barrier_hessian {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι]
    (ℓ : ι → E →ᵃ[ℝ] ℝ) (a : ι → ℝ) (s : ℝ) {x : E}
    (hx : ∀ i, 0 < ℓ i x) (u v : E) :
    fderiv ℝ (fderiv ℝ (fun y => ∑ i, a i * (ℓ i y) ^ (-s))) x u v =
      ∑ i, a i * (s * (s + 1)) * (ℓ i x) ^ (-s - 2) *
        ((ℓ i).linear u * (ℓ i).linear v) := by
  let L := fun i => LinearMap.toContinuousLinearMap (ℓ i).linear
  have hd (i : ι) (y : E) : HasFDerivAt (fun y => ℓ i y) (L i) y := by
    have he : (fun y => ℓ i y) = fun y => L i y + ℓ i 0 := by
      funext z
      exact congrFun (AffineMap.decomp (ℓ i)) z
    rw [he]
    exact (L i).hasFDerivAt.add_const _
  let J := fun y => ∑ i, (a i * (-s) * (ℓ i y) ^ (-s - 1)) • L i
  have hJ : HasFDerivAt J
      (∑ i, ((a i * (-s) * (-s - 1) * (ℓ i x) ^ (-s - 1 - 1)) • L i).smulRight (L i)) x := by
    apply HasFDerivAt.fun_sum
    intro i _
    have h := (((hd i x).rpow_const (p := -s - 1) (Or.inl (hx i).ne')).const_mul
      (a i * (-s))).smul_const (L i)
    convert h using 1
    ext w v
    simp only [ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul]
    ring
  have hnear : ∀ᶠ y in 𝓝 x, ∀ i, 0 < ℓ i y :=
    eventually_all.mpr fun i => (hd i x).continuousAt (isOpen_Ioi.mem_nhds (hx i))
  have he : fderiv ℝ (fun y => ∑ i, a i * (ℓ i y) ^ (-s)) =ᶠ[𝓝 x] J := by
    filter_upwards [hnear] with y hy
    ext w
    have hh := ElementaryBarriers.fderiv_potential_apply
      (ℓ := ℓ) (a := a) (s := s) (R := fun _ => 0)
      (fun i => (hy i).ne') (differentiableAt_const 0) w
    simpa only [fderiv_fun_const, Pi.zero_apply, zero_apply, add_zero,
      J, sum_apply, smul_apply, smul_eq_mul, L] using hh
  rw [he.fderiv_eq, hJ.fderiv]
  simp only [sum_apply, ContinuousLinearMap.smulRight_apply,
    smul_apply, smul_eq_mul, L]
  change (∑ i, a i * -s * (-s - 1) * (ℓ i x) ^ (-s - 1 - 1) *
    (ℓ i).linear u * (ℓ i).linear v) = _
  apply Finset.sum_congr rfl
  intro i _
  rw [show -s - 1 - 1 = -s - 2 by ring]
  ring

/-- Smoothness of a finite affine inverse-power barrier on its positive
face domain. Used internally in Appendix A. -/
theorem internal_barrier_smooth {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι]
    (ℓ : ι → E →ᵃ[ℝ] ℝ) (a : ι → ℝ) (s : ℝ) :
    ContDiffOn ℝ ∞ (fun x => ∑ i, a i * (ℓ i x) ^ (-s))
      {x | ∀ i, 0 < ℓ i x} := by
  apply ContDiffOn.sum
  intro i _
  apply contDiffOn_const.mul
  have hℓ : ContDiff ℝ ∞ (fun x => ℓ i x) := by
    have he : (fun x => ℓ i x) =
        fun x => LinearMap.toContinuousLinearMap (ℓ i).linear x + ℓ i 0 := by
      funext x
      exact congrFun (AffineMap.decomp (ℓ i)) x
    rw [he]
    exact (LinearMap.toContinuousLinearMap (ℓ i).linear).contDiff.add contDiff_const
  exact hℓ.contDiffOn.rpow_const_of_ne (fun x hx => (hx i).ne')

/-- See Appendix A of the paper: every proper unforced marginal has strictly
positive Euclidean curvature. The constant depends only on fixed data. -/
theorem marginal_strict_curvature (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
      ∀ u : EuclideanSpace ℝ (Fin n),
        κ * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (fun t =>
          -Real.log (∫ z : EuclideanSpace ℝ (Fin m),
            (ProperMarginalChart.chartDensity p n m σ (t,z)).toReal))) x u u := by
  obtain ⟨R, hRs, hRc, he⟩ := marginal_barrier_decomposition p n m hn σ
  let L : ℝ := ((n + m : ℕ) + 1)
  let Ω := AffineSimplex.chartDomain n L
  let B := fun x : EuclideanSpace ℝ (Fin n) =>
    ∑ j, (2 * p.val.1) * (face n L j x) ^ (-p.val.2)
  have hL : 0 < L := by dsimp [L]; positivity
  let κ := 2 * p.val.1 * (p.val.2 * (p.val.2 + 1)) * L ^ (-p.val.2 - 2)
  have hκ : 0 < κ := by dsimp [κ]; have := p.property.1; have := p.property.2.1; positivity
  have hBs : ContDiffOn ℝ ∞ B Ω := by
    dsimp only [Ω]
    rw [domain_eq_faces]
    exact internal_barrier_smooth (face n L) (fun _ => 2 * p.val.1) p.val.2
  have hsum (x : EuclideanSpace ℝ (Fin n)) : B x =
      2 * p.val.1 * (∑ i, (x i) ^ (-p.val.2)) +
        2 * p.val.1 * (L - ∑ i, x i) ^ (-p.val.2) := by
    dsimp only [B]
    rw [Fintype.sum_option]
    simp only [face_none, face_some, ← Finset.mul_sum]
    ring
  refine ⟨κ, hκ, fun x hx u => ?_⟩
  have hpos : ∀ j, 0 < face n L j x := by
    have hx' : x ∈ AffineSimplex.chartDomain n L := hx
    rwa [domain_eq_faces] at hx'
  have hR2 : ContDiffAt ℝ 2 R x :=
    (hRs.contDiffAt ((AffineSimplex.isOpen_chartDomain n L).mem_nhds hx)).of_le (by norm_num)
  have hB2 : ContDiffAt ℝ 2 B x :=
    (hBs.contDiffAt ((AffineSimplex.isOpen_chartDomain n L).mem_nhds hx)).of_le (by norm_num)
  have hRnonneg := Riesz1.fderiv_fderiv_nonneg_of_convexOn
    (AffineSimplex.isOpen_chartDomain n L) (AffineSimplex.convex_chartDomain n L)
    hRc (hRs.of_le (by norm_num)) hx u
  have hnear : (fun t => -Real.log (∫ z : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p n m σ (t,z)).toReal)) =ᶠ[𝓝 x]
        fun t => B t + R t := by
    filter_upwards [(AffineSimplex.isOpen_chartDomain n L).mem_nhds hx] with t ht
    rw [hsum]
    exact he t ht
  rw [hnear.fderiv.fderiv_eq,
    PhysicalCollision.internal_hessian_add hB2 hR2 u u]
  have hB := internal_barrier_hessian (face n L) (fun _ => 2 * p.val.1) p.val.2 hpos u u
  change fderiv ℝ (fderiv ℝ B) x u u = _ at hB
  rw [hB, Fintype.sum_option]
  have hn0 : 0 ≤ 2 * p.val.1 * (p.val.2 * (p.val.2 + 1)) *
      (face n L none x) ^ (-p.val.2 - 2) *
        ((face n L none).linear u * (face n L none).linear u) := by
    have := p.property.1
    have := p.property.2.1
    apply mul_nonneg _ (mul_self_nonneg _)
    apply mul_nonneg _ (Real.rpow_nonneg (hpos none).le _)
    positivity
  have hsumle : κ * ‖u‖ ^ 2 ≤
      ∑ i : Fin n, 2 * p.val.1 * (p.val.2 * (p.val.2 + 1)) *
        (face n L (some i) x) ^ (-p.val.2 - 2) *
          ((face n L (some i)).linear u * (face n L (some i)).linear u) := by
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hi : x i ≤ L := by
      exact (Finset.single_le_sum (fun j _ => (hx.1 j).le)
        (Finset.mem_univ i)).trans hx.2.le
    have hp := Real.rpow_le_rpow_of_nonpos (hx.1 i) hi
      (by linarith [p.property.2.1] : -p.val.2 - 2 ≤ 0)
    change κ * (u i) ^ 2 ≤
      2 * p.val.1 * (p.val.2 * (p.val.2 + 1)) * (x i) ^ (-p.val.2 - 2) * (u i * u i)
    dsimp only [κ]
    rw [← pow_two]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply mul_le_mul_of_nonneg_left hp
    have := p.property.1
    have := p.property.2.1
    positivity
  linarith

/-- Internal physical Hessian envelope for Appendix A. The
bound uses the sum of all full-gap inverse powers, so it can be integrated
using the conditional moments without estimating a random minimum. -/
theorem internal_physical_hessian_envelope (p : Parameters) (N : ℕ+) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (U : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ),
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        U y.val = p.val.1 * physicalAmbientGapEnergy p N y) →
      ∀ y : EuclideanSpace ℝ (Fin (N : ℕ)),
        WithLp.ofLp y ∈ Riesz1.gapSimplex N → ∀ w : EuclideanSpace ℝ (Fin (N : ℕ)),
        fderiv ℝ (fderiv ℝ U) y w w ≤
          C * (∑ a, (y a) ^ (-p.val.2 - 2)) * ‖w‖ ^ 2 := by
  obtain ⟨U₀, hU₀, hv₀, hb⟩ := MarginalHessian.physical_energy_tensors p N
  obtain ⟨C, hC, hbound⟩ := hb (2 : ℕ+)
  refine ⟨C, hC, fun U hv y hy w => ?_⟩
  have ha := PhysicalEnergy.simplex_subset_ambient N _ hy
  have he : U =ᶠ[𝓝 y] U₀ := by
    filter_upwards [(PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds ha] with z hz
    exact (hv ⟨z,hz⟩).trans (hv₀ ⟨z,hz⟩).symm
  rw [he.fderiv.fderiv_eq]
  obtain ⟨j, hj⟩ := Finite.exists_min (fun a : Fin (N : ℕ) => y a)
  have ht := hbound y hy (y j) (hy.1 j) hj
  have hsum : (y j) ^ (-p.val.2 - 2) ≤ ∑ a, (y a) ^ (-p.val.2 - 2) :=
    Finset.single_le_sum (fun a _ => Real.rpow_nonneg (hy.1 a).le _) (Finset.mem_univ j)
  have hv := (iteratedFDeriv ℝ 2 U₀ y).le_opNorm ![w,w]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.prod_univ_two, Real.norm_eq_abs, ← pow_two] at hv
  calc
    fderiv ℝ (fderiv ℝ U₀) y w w ≤ |fderiv ℝ (fderiv ℝ U₀) y w w| := le_abs_self _
    _ ≤ ‖iteratedFDeriv ℝ 2 U₀ y‖ * ‖w‖ ^ 2 := hv
    _ ≤ (C * (y j) ^ (-p.val.2 - 2)) * ‖w‖ ^ 2 :=
      mul_le_mul_of_nonneg_right ht (sq_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsum hC.le) (sq_nonneg _)

/-- See Appendix A of the paper: the Hessian upper bound for the actual proper
marginal. Its scale is any positive common lower bound for the retained
gaps and remaining mass. Conditional integrability is supplied by physical
energy moments, rather than assumed. -/
theorem marginal_hessian_upper (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
      ∀ δ : ℝ, 0 < δ → (∀ i, δ ≤ x i) →
        δ ≤ ((n + m : ℕ) + 1) - ∑ i, x i →
      ∀ u : EuclideanSpace ℝ (Fin n),
        fderiv ℝ (fderiv ℝ (fun t => -Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity p n m σ (t,z)).toReal))) x u u ≤
            C * (1 + δ ^ (-p.val.2 - 2)) * ‖u‖ ^ 2 := by
  obtain ⟨Ce, hCe, henv⟩ := internal_physical_hessian_envelope p (n + m).succPNat
  obtain ⟨W, _, _, Cm, hCm, hm⟩ :=
    ConditionalEnergyMoments.physical_conditional_moments p n m hn
  obtain ⟨U, hU, hv, _, hcalc⟩ := MarginalHessian.physical_compensated_marginal_calculus p n m hn σ
  let A := MarginalHessian.compensatedDirection n m σ
  let D := Ce * ‖A‖ ^ 2
  let C := D * ((n + m + 1 : ℕ) : ℝ) * Cm + 1
  have hD : 0 ≤ D := mul_nonneg hCe.le (sq_nonneg _)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, fun x hx δ hδ hδx hδL u => ?_⟩
  let xs : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) := ⟨x,hx⟩
  let c := AffineSimplex.coordinates m
    (AffineSimplex.centre m (((n + m : ℕ) + 1) - ∑ i, x i))
  let ρ := AffineFibre.normalizedMeasure volume
    (fun z => ProperMarginalChart.chartDensity p n m σ (x,z+c))
    (by rw [lintegral_add_right_eq_self (fun z => ProperMarginalChart.chartDensity p n m σ (x,z)) c]
        exact (ProperMarginalChart.fibre_mass p n m hn σ hx).1)
    (by rw [lintegral_add_right_eq_self (fun z => ProperMarginalChart.chartDensity p n m σ (x,z)) c]
        exact (ProperMarginalChart.fibre_mass p n m hn σ hx).2)
  let μ := ProperMarginalChart.conditionalMeasure p n m hn σ xs
  let Y := fun z => RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ (x,z)
  let H := fun z t => U (MarginalHessian.compensatedChart n m ((n + m : ℕ) + 1) σ (t,z))
  obtain ⟨hmap, hL2, hTi, hder, _⟩ := hcalc xs
  change ρ.map (fun z => z+c) = μ at hmap
  have hshift : Measurable (fun z : EuclideanSpace ℝ (Fin m) => z+c) :=
    measurable_id.add measurable_const
  have hsμ := ConditionalEnergyMoments.physical_conditional_support p n m hn σ xs
  change ∀ᵐ z ∂μ, z ∈ AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ i, x i) at hsμ
  have hsmap := hsμ
  rw [← hmap] at hsmap
  have hsρ := ae_of_ae_map hshift.aemeasurable hsmap
  have hy (z) (hz : z ∈ AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ i, x i)) :
      WithLp.ofLp (Y z) ∈ Riesz1.gapSimplex (n + m).succPNat := by
    have hq := (Set.ext_iff.mp (RetainedSimplex.fibre_domain n m _ hx) z).mpr hz
    have hh := (RetainedSimplex.chart_mem_simplex n m _ σ (x,z)).mpr hq
    exact ⟨hh.1, by simpa only [Y, Nat.succPNat_coe, Nat.cast_succ] using hh.2⟩
  obtain ⟨z₀, _, _, _, _, hmδ⟩ := hm σ xs
  have hmoment := (hmδ δ hδ hδx hδL).2
  have hF (a : Fin (n + m + 1)) :
      Integrable (fun z => (Y (z+c) a) ^ (-p.val.2 - 2)) ρ ∧
        (∫ z, (Y (z+c) a) ^ (-p.val.2 - 2) ∂ρ) ≤ Cm * (1 + δ ^ (-p.val.2 - 2)) := by
    obtain ⟨hi, hb⟩ := hmoment a
    change Integrable (fun z => (Y z a) ^ (-p.val.2 - 2)) μ at hi
    have hmF : Measurable (fun z => (Y z a) ^ (-p.val.2 - 2)) := by
      have hY : Continuous Y := (RetainedSimplex.continuous_chart n m _ σ).comp
        (continuous_const.prodMk continuous_id)
      exact ((EuclideanSpace.proj (𝕜 := ℝ) a).continuous.comp hY).measurable.pow_const _
    have hnF : ∀ᵐ z ∂μ, 0 ≤ (Y z a) ^ (-p.val.2 - 2) :=
      hsμ.mono fun z hz => Real.rpow_nonneg ((hy z hz).1 a).le _
    rw [← ofReal_integral_eq_lintegral_ofReal hi hnF] at hb
    have hreal : (∫ z, (Y z a) ^ (-p.val.2 - 2) ∂μ) ≤ Cm * (1 + δ ^ (-p.val.2 - 2)) :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hb
    have hi' : Integrable (fun z => (Y (z+c) a) ^ (-p.val.2 - 2)) ρ := by
      rw [← hmap] at hi
      exact hi.comp_measurable hshift
    refine ⟨hi', ?_⟩
    rw [← hmap] at hreal
    rwa [integral_map hshift.aemeasurable hmF.aestronglyMeasurable] at hreal
  let F := fun z => ∑ a, (Y (z+c) a) ^ (-p.val.2 - 2)
  have hFi : Integrable F ρ := integrable_finsetSum _ (fun a _ => (hF a).1)
  have hFb : (∫ z, F z ∂ρ) ≤ ((n + m + 1 : ℕ) : ℝ) * Cm * (1 + δ ^ (-p.val.2 - 2)) := by
    rw [show F = fun z => ∑ a, (Y (z+c) a) ^ (-p.val.2 - 2) from rfl,
      integral_finsetSum _ (fun a _ => (hF a).1)]
    calc
      _ ≤ ∑ _a : Fin (n + m + 1), Cm * (1 + δ ^ (-p.val.2 - 2)) :=
        Finset.sum_le_sum (fun a _ => (hF a).2)
      _ = _ := by simp [mul_assoc]
  have hTbound : ∀ᵐ z ∂ρ, fderiv ℝ (fderiv ℝ (H z)) x u u ≤ D * F z * ‖u‖ ^ 2 := by
    filter_upwards [hsρ] with z hz
    have hys := hy (z+c) hz
    have hec : MarginalHessian.compensatedChart n m ((n + m : ℕ) + 1) σ (x,z) = Y (z+c) := by
      rw [MarginalHessian.compensatedChart_eq_shift]
      unfold MarginalHessian.compensatedShift
      rfl
    have hya := PhysicalEnergy.simplex_subset_ambient (n + m).succPNat _ hys
    have hUs : ContDiffAt ℝ 2 U (MarginalHessian.compensatedChart n m ((n + m : ℕ) + 1) σ (x,z)) := by
      rw [hec]
      exact (hU.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain _).mem_nhds hya)).of_le (by norm_num)
    have hd := (MarginalHessian.internal_compensated_energy_derivatives n m ((n + m : ℕ) + 1)
      σ x z hUs u u).2
    change fderiv ℝ (fderiv ℝ (H z)) x u u = _ at hd
    rw [hd, hec]
    have henv' := henv U hv (Y (z+c)) hys (A u)
    have hAn := pow_le_pow_left₀ (norm_nonneg (A u)) (A.le_opNorm u) 2
    rw [mul_pow] at hAn
    have hFpos : 0 ≤ F z := Finset.sum_nonneg fun a _ => Real.rpow_nonneg ((hys.1 a).le) _
    calc
      _ ≤ Ce * F z * ‖A u‖ ^ 2 := henv'
      _ ≤ Ce * F z * (‖A‖ ^ 2 * ‖u‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hAn (mul_nonneg hCe.le hFpos)
      _ = _ := by dsimp only [D]; ring
  have hmajor : Integrable (fun z => D * F z * ‖u‖ ^ 2) ρ := (hFi.const_mul D).mul_const _
  have hcov : 0 ≤ ProbabilityTheory.covariance
      (fun z => fderiv ℝ (H z) x u) (fun z => fderiv ℝ (H z) x u) ρ :=
    integral_nonneg fun _ => mul_self_nonneg _
  have hCC : D * ((n + m + 1 : ℕ) : ℝ) * Cm ≤ C := by dsimp only [C]; linarith
  rw [(hder u u).2]
  calc
    _ ≤ ∫ z, fderiv ℝ (fderiv ℝ (H z)) x u u ∂ρ := sub_le_self _ hcov
    _ ≤ ∫ z, D * F z * ‖u‖ ^ 2 ∂ρ := integral_mono_ae (hTi u u) hmajor hTbound
    _ = D * (∫ z, F z ∂ρ) * ‖u‖ ^ 2 := by rw [integral_mul_const, integral_const_mul]
    _ ≤ D * (((n + m + 1 : ℕ) : ℝ) * Cm * (1 + δ ^ (-p.val.2 - 2))) * ‖u‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hFb hD) (sq_nonneg _)
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCC (show 0 ≤ 1 + δ ^ (-p.val.2 - 2) by positivity))
        (sq_nonneg ‖u‖)
      nlinarith only [hh]

/-- See Appendix A of the paper: the boundary Laplacian upper bound for every
unforced proper marginal, in ordinary retained Euclidean coordinates. -/
theorem marginal_laplacian_upper (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
      Laplacian.laplacian (fun t => -Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p n m σ (t,z)).toReal)) x ≤
          C * (1 + (min (⨅ i, x i) (((n + m : ℕ) + 1) - ∑ i, x i)) ^ (-p.val.2 - 2)) := by
  obtain ⟨C, hC, hb⟩ := marginal_hessian_upper p n m hn σ
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  refine ⟨n * C, mul_pos hnR hC, fun x hx => ?_⟩
  let δ := ⨅ i, face n ((n + m : ℕ) + 1) i x
  have hδ := minimum_face_pos n ((n + m : ℕ) + 1) hx
  have hδx (i : Fin n) : δ ≤ x i :=
    ciInf_le (Finite.bddBelow_range (fun j => face n ((n + m : ℕ) + 1) j x)) (some i)
  have hδL : δ ≤ ((n + m : ℕ) + 1) - ∑ i, x i := by
    simpa only [face_none] using
      ciInf_le (Finite.bddBelow_range (fun j => face n ((n + m : ℕ) + 1) j x)) none
  have hh := PhysicalCollision.internal_laplacian_le _ x
    (C * (1 + δ ^ (-p.val.2 - 2))) (hb x hx δ hδ hδx hδL)
  simpa only [finrank_euclideanSpace_fin, δ, minimum_face_eq n hn, mul_assoc] using hh

/-- See Appendix A of the paper: the full all-coefficient collision bound for
unforced proper marginals. In particular `A = 1/2`, `K = 2`, followed by
division by two, gives the ground-state potential criterion of
Appendix A. The domain is the proper marginal domain. -/
theorem unforced_marginal_collision (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) :
    let V := fun t => -Real.log (∫ z : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p n m σ (t,z)).toReal)
    ∀ A K : ℝ, 0 < A → 0 < K → ∃ D : ℝ, 0 ≤ D ∧
      ∀ x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
        K * (Metric.infDist x (frontier (AffineSimplex.chartDomain n ((n + m : ℕ) + 1))) ^ 2)⁻¹ - D ≤
          A * ‖gradient V x‖ ^ 2 - Laplacian.laplacian V x := by
  intro V A K hA hK
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨R, hRs, hRc, he⟩ := marginal_barrier_decomposition p n m hn σ
  obtain ⟨C, _, hΔ⟩ := marginal_laplacian_upper p n m hn σ
  have hsum (x : EuclideanSpace ℝ (Fin n)) :
      (∑ j, (2 * p.val.1) * (face n ((n + m : ℕ) + 1) j x) ^ (-p.val.2)) =
        2 * p.val.1 * (∑ i, (x i) ^ (-p.val.2)) +
          2 * p.val.1 * (((n + m : ℕ) + 1) - ∑ i, x i) ^ (-p.val.2) := by
    rw [Fintype.sum_option]
    simp only [face_none, face_some, ← Finset.mul_sum]
    ring
  obtain ⟨D, hD⟩ := ElementaryBarriers.radial_laplacian_lower
    (face n ((n + m : ℕ) + 1)) (fun _ => 2 * p.val.1)
    (fun _ => mul_pos (by norm_num) p.property.1) p.property.2.1
    (domain_eq_faces n _) (AffineSimplex.isBounded_chartDomain n _)
    R hRc hRs V (fun x hx => by rw [hsum]; exact he x hx) C
    (by simpa only [minimum_face_eq n hn] using hΔ) A K hA hK
  refine ⟨max D 0, le_max_right _ _, fun x hx => ?_⟩
  exact (sub_le_sub_left (le_max_left D 0) _).trans (hD x hx)

/-- See Appendix A of the paper on a proper retained domain: the active
penalty is smooth and convex, with the empty active set included. -/
theorem active_penalty_smooth_convex (n : ℕ) (L : ℝ) (θ : PhysicalCutoff)
    {a : ℝ} (ha : 0 < a) (J : Finset (Fin n)) (b : Bool) :
    let P := fun x : EuclideanSpace ℝ (Fin n) => ∑ i ∈ J,
      (θ.val (a * x i) + if b then θ.val (a * (x i)⁻¹) else 0)
    ContDiffOn ℝ ∞ P (AffineSimplex.chartDomain n L) ∧
      ConvexOn ℝ (AffineSimplex.chartDomain n L) P := by
  intro P
  have hφ : ConvexOn ℝ (Ioi (0 : ℝ)) (fun t => θ.val (a * t) +
      if b then θ.val (a * t⁻¹) else 0) := by
    cases b
    · simpa only [Bool.false_eq_true, ↓reduceIte, add_zero] using
        PhysicalCollision.upper_penalty_convex θ ha
    · simpa only [↓reduceIte, Pi.add_def, div_eq_mul_inv] using
        (PhysicalCollision.upper_penalty_convex θ ha).add (PhysicalCollision.inverse_penalty_convex θ ha)
  constructor
  · apply ContDiffOn.sum
    intro i _ x hx
    have hi : ContDiffAt ℝ ∞ (fun t : EuclideanSpace ℝ (Fin n) => t i) x :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt
    have hu := (PhysicalCollision.cutoff_contDiffAt θ (mul_pos ha (hx.1 i))).comp x
      (contDiffAt_const.mul hi)
    cases b
    · simpa only [Bool.false_eq_true, ↓reduceIte, add_zero, Function.comp_def] using hu.contDiffWithinAt
    · have hv := (PhysicalCollision.cutoff_contDiffAt θ (mul_pos ha (inv_pos.mpr (hx.1 i)))).comp x
        (contDiffAt_const.mul (hi.inv (hx.1 i).ne'))
      simpa only [↓reduceIte, Function.comp_def, Pi.inv_apply] using (hu.add hv).contDiffWithinAt
  · refine ⟨AffineSimplex.convex_chartDomain n L, fun x hx y hy α β hα hβ hab => ?_⟩
    have hh := Finset.sum_le_sum (s := J) (fun i _ => hφ.2 (hx.1 i) (hy.1 i) hα hβ hab)
    simpa only [P, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, Finset.mul_sum, mul_add] using hh

/-- See Appendix A of the paper: every allowed active penalty preserves the
strict curvature of the actual proper marginal, at the original constant. -/
theorem penalized_marginal_strict_curvature (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff)
    {a : ℝ} (ha : 0 < a) (J : Finset (Fin n)) (b : Bool) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
      ∀ u : EuclideanSpace ℝ (Fin n),
        κ * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (fun t =>
          p.val.1 * ∑ i ∈ J, (θ.val (a * t i) + if b then θ.val (a * (t i)⁻¹) else 0) -
            Real.log (∫ z : EuclideanSpace ℝ (Fin m),
              (ProperMarginalChart.chartDensity p n m σ (t,z)).toReal))) x u u := by
  obtain ⟨κ, hκ, hc⟩ := marginal_strict_curvature p n m hn σ
  obtain ⟨hPs, hPc⟩ := active_penalty_smooth_convex n ((n + m : ℕ) + 1) θ ha J b
  have hVs := MarginalHessian.physical_marginal_potential_smooth p n m hn σ
  refine ⟨κ, hκ, fun x hx u => ?_⟩
  have hP2 := (hPs.contDiffAt ((AffineSimplex.isOpen_chartDomain n _).mem_nhds hx)).of_le
    (show (2 : WithTop ℕ∞) ≤ ∞ by simp)
  have hV2 := (hVs.contDiffAt ((AffineSimplex.isOpen_chartDomain n _).mem_nhds hx)).of_le
    (show (2 : WithTop ℕ∞) ≤ ∞ by simp)
  have hβP : ContDiffAt ℝ 2 (fun t => p.val.1 *
      ∑ i ∈ J, (θ.val (a * t i) + if b then θ.val (a * (t i)⁻¹) else 0)) x :=
    contDiffAt_const.mul hP2
  have hh := PhysicalCollision.internal_hessian_add hβP hV2 u u
  rw [PhysicalCollision.internal_hessian_const_mul hP2] at hh
  change κ * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (fun t =>
    p.val.1 * ∑ i ∈ J, (θ.val (a * t i) + if b then θ.val (a * (t i)⁻¹) else 0) +
      -Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p n m σ (t,z)).toReal))) x u u
  rw [hh]
  have hnP := Riesz1.fderiv_fderiv_nonneg_of_convexOn
    (AffineSimplex.isOpen_chartDomain n _) (AffineSimplex.convex_chartDomain n _)
    hPc (hPs.of_le (by norm_num)) hx u
  exact (hc x hx u).trans (le_add_of_nonneg_left (mul_nonneg p.property.1.le hnP))

/-- See Appendix A of the paper: physical face singularities and active inverse
penalties add in a radial derivative before taking the gradient norm.
This prevents cancellation at simultaneous collisions. -/
theorem penalized_marginal_gradient_lower (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff)
    {a : ℝ} (ha : 0 < a) (J : Finset (Fin n)) (b : Bool) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
      c * ((⨅ j, face n ((n + m : ℕ) + 1) j x) ^ (-p.val.2 - 1) +
        if b then ∑ i ∈ J, (x i)⁻¹ ^ 3 else 0) - C ≤
      ‖gradient (fun t => p.val.1 * ∑ i ∈ J,
        (θ.val (a * t i) + if b then θ.val (a * (t i)⁻¹) else 0) -
          Real.log (∫ z : EuclideanSpace ℝ (Fin m),
            (ProperMarginalChart.chartDensity p n m σ (t,z)).toReal)) x‖ := by
  classical
  obtain ⟨R₀, hR₀s, hR₀c, he₀⟩ := marginal_barrier_decomposition p n m hn σ
  let L : ℝ := ((n + m : ℕ) + 1)
  let Ω := AffineSimplex.chartDomain n L
  let x₀ : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun _ => 1)
  have hx₀ : x₀ ∈ Ω := by
    constructor
    · intro i; exact one_pos
    · change (∑ _i : Fin n, (1 : ℝ)) < L
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      dsimp only [L]
      push_cast
      linarith [show (0 : ℝ) ≤ m from Nat.cast_nonneg m]
  have hf₀ (j : Option (Fin n)) : 1 ≤ face n L j x₀ := by
    cases j with
    | some i => change (1 : ℝ) ≤ 1; exact le_rfl
    | none => simp only [face_none, x₀, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
              dsimp only [L]
              push_cast
              linarith [show (0 : ℝ) ≤ m from Nat.cast_nonneg m]
  let P := fun t : EuclideanSpace ℝ (Fin n) => ∑ i ∈ J, θ.val (a * t i)
  let Q := fun t : EuclideanSpace ℝ (Fin n) => ∑ i ∈ J, θ.val (a / t i)
  have hPs : ContDiffOn ℝ ∞ P Ω := by
    simpa only [Bool.false_eq_true, ↓reduceIte, add_zero] using
      (active_penalty_smooth_convex n L θ ha J false).1
  have hPc : ConvexOn ℝ Ω P := by
    simpa only [Bool.false_eq_true, ↓reduceIte, add_zero] using
      (active_penalty_smooth_convex n L θ ha J false).2
  let R := fun t => R₀ t + p.val.1 * P t
  have hRs : ContDiffOn ℝ ∞ R Ω := hR₀s.add (contDiffOn_const.mul hPs)
  have hRc : ConvexOn ℝ Ω R := hR₀c.add (hPc.smul p.property.1.le)
  have hRd (t) (ht : t ∈ Ω) : DifferentiableAt ℝ R t :=
    (hRs.contDiffAt ((AffineSimplex.isOpen_chartDomain n L).mem_nhds ht)).differentiableAt (by simp)
  obtain ⟨r, hr⟩ := (AffineSimplex.isBounded_chartDomain n L).subset_closedBall x₀
  let D := max r 1
  have hD : 0 < D := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hnorm (t) (ht : t ∈ Ω) : ‖t - x₀‖ ≤ D :=
    (show ‖t - x₀‖ ≤ r from by simpa only [Metric.mem_closedBall, dist_eq_norm] using hr ht).trans
      (le_max_left r 1)
  obtain ⟨c₀, C₀, hc₀, hC₀, hp⟩ := PhysicalCollision.internal_power_radial p.property.2.1
    (show 0 < 2 * p.val.1 by have := p.property.1; positivity)
  obtain ⟨c₁, C₁, hc₁, hC₁, hq⟩ := PhysicalCollision.inverse_penalty_radial θ ha one_pos
  let c₂ := min c₀ (p.val.1 * c₁)
  have hc₂ : 0 < c₂ := lt_min hc₀ (mul_pos p.property.1 hc₁)
  let B := ((n + 1 : ℕ) : ℝ) * C₀ + p.val.1 * J.card * C₁ + ‖fderiv ℝ R x₀‖ * D + 1
  have hB : 0 < B := by dsimp only [B]; have := p.property.1; positivity
  refine ⟨c₂ / D, B / D, div_pos hc₂ hD, div_pos hB hD, fun x hx => ?_⟩
  let V := fun t => p.val.1 * ∑ i ∈ J,
    (θ.val (a * t i) + if b then θ.val (a * (t i)⁻¹) else 0) -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m), (ProperMarginalChart.chartDensity p n m σ (t,z)).toReal)
  let T := fun t => (∑ j, (2 * p.val.1) * (face n L j t) ^ (-p.val.2)) + R t
  have hnear : V =ᶠ[𝓝 x] fun t => T t + if b then p.val.1 * Q t else 0 := by
    filter_upwards [(AffineSimplex.isOpen_chartDomain n L).mem_nhds hx] with t ht
    have h := he₀ t ht
    dsimp only [V, T, R, P, Q]
    rw [Fintype.sum_option]
    simp only [face_none, face_some, ← Finset.mul_sum]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, add_zero,
      Finset.sum_add_distrib, div_eq_mul_inv] <;> linarith only [h]
  have hQd : HasFDerivAt Q
      (∑ i ∈ J, deriv (fun t => θ.val (a / t)) (x i) • EuclideanSpace.proj (𝕜 := ℝ) i) x := by
    apply HasFDerivAt.fun_sum
    intro i _
    have hi : HasDerivAt (fun t => θ.val (a / t)) (deriv (fun t => θ.val (a / t)) (x i)) (x i) :=
      (PhysicalCollision.inverse_penalty_hasDerivAt θ ha (hx.1 i)).differentiableAt.hasDerivAt
    exact HasDerivAt.comp_hasFDerivAt (h₂ := fun t : ℝ => θ.val (a / t))
      (f := fun t : EuclideanSpace ℝ (Fin n) => t i) x hi
      ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt :
        HasFDerivAt (fun t : EuclideanSpace ℝ (Fin n) => t i) _ x)
  have hTd : DifferentiableAt ℝ T x := by
    have hBs : ContDiffOn ℝ ∞ (fun t => ∑ j, (2 * p.val.1) * (face n L j t) ^ (-p.val.2)) Ω := by
      dsimp only [Ω]
      rw [domain_eq_faces]
      exact internal_barrier_smooth (face n L) (fun _ => 2 * p.val.1) p.val.2
    exact ((hBs.contDiffAt ((AffineSimplex.isOpen_chartDomain n L).mem_nhds hx)).differentiableAt
      (by simp)).add (hRd x hx)
  have hfdT := ElementaryBarriers.fderiv_potential_apply
    (ℓ := face n L) (a := fun _ => 2 * p.val.1) (s := p.val.2)
    (fun j => ((domain_eq_faces n L ▸ hx) j).ne') (hRd x hx) (x - x₀)
  change fderiv ℝ T x (x - x₀) = _ at hfdT
  have hpower (j) : c₀ * (face n L j x) ^ (-p.val.2 - 1) - C₀ ≤
      (2 * p.val.1 * (-p.val.2) * (face n L j x) ^ (-p.val.2 - 1)) *
        (LinearMap.toContinuousLinearMap (face n L j).linear) (x - x₀) := by
    rw [ElementaryBarriers.linear_sub_eq]
    have hj : 0 < face n L j x := (domain_eq_faces n L ▸ hx) j
    have h := hp (face n L j x) hj
    have hneg : 2 * p.val.1 * (-p.val.2) * (face n L j x) ^ (-p.val.2 - 1) ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by have := p.property.1; positivity)
          (neg_nonpos.mpr p.property.2.1.le)) (Real.rpow_nonneg hj.le _)
    have ht := mul_le_mul_of_nonpos_left (show face n L j x - face n L j x₀ ≤ face n L j x - 1 by
      linarith [hf₀ j]) hneg
    exact h.trans ht
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hpower j)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_option, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum] at hsum
  have hR := ElementaryBarriers.convex_fderiv_sub_lower hRc hx hx₀ (hRd x hx) (hRd x₀ hx₀) (hnorm x hx)
  have hQ := Finset.sum_le_sum (s := J) (fun i _ => hq (x i) (hx.1 i))
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hQ
  have hfdQ : fderiv ℝ Q x (x - x₀) = ∑ i ∈ J,
      deriv (fun t => θ.val (a / t)) (x i) * (x i - 1) := by
    rw [hQd.fderiv]
    simp only [sum_apply, smul_apply, smul_eq_mul, EuclideanSpace.coe_proj, PiLp.sub_apply, x₀]
  rw [← hfdQ] at hQ
  have hfdV : fderiv ℝ V x (x - x₀) = fderiv ℝ T x (x - x₀) +
      if b then p.val.1 * fderiv ℝ Q x (x - x₀) else 0 := by
    rw [hnear.fderiv_eq]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
    · simp only [↓reduceIte]
      rw [fderiv_fun_add hTd (hQd.differentiableAt.const_mul p.val.1),
        fderiv_const_mul hQd.differentiableAt]
      rfl
  obtain ⟨j, hj⟩ := ElementaryBarriers.exists_iInf_eq_apply (fun j => face n L j x)
  have hmin : (⨅ j, face n L j x) ^ (-p.val.2 - 1) ≤ ∑ j, (face n L j x) ^ (-p.val.2 - 1) := by
    rw [hj]
    exact Finset.single_le_sum (fun i _ => Real.rpow_nonneg ((domain_eq_faces n L ▸ hx) i).le _)
      (Finset.mem_univ j)
  have hcoeff := mul_le_mul_of_nonneg_left hmin hc₂.le
  have hcoef₀ := mul_le_mul_of_nonneg_right (min_le_left c₀ (p.val.1 * c₁))
    (show 0 ≤ ∑ j, (face n L j x) ^ (-p.val.2 - 1) from
      Finset.sum_nonneg fun j _ => Real.rpow_nonneg ((domain_eq_faces n L ▸ hx) j).le _)
  have hcoef₁ := mul_le_mul_of_nonneg_right (min_le_right c₀ (p.val.1 * c₁))
    (show 0 ≤ ∑ i ∈ J, (x i)⁻¹ ^ 3 from
      Finset.sum_nonneg fun i _ => pow_nonneg (inv_nonneg.mpr (hx.1 i).le) 3)
  have hlow : c₂ * ((⨅ j, face n L j x) ^ (-p.val.2 - 1) +
      if b then ∑ i ∈ J, (x i)⁻¹ ^ 3 else 0) - B ≤ fderiv ℝ V x (x - x₀) := by
    rw [hfdV, hfdT]
    have hQβ := mul_le_mul_of_nonneg_left hQ p.property.1.le
    have hβC : 0 ≤ p.val.1 * J.card * C₁ :=
      mul_nonneg (mul_nonneg p.property.1.le (Nat.cast_nonneg _)) hC₁.le
    dsimp only [B]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, add_zero] <;>
      linarith only [hsum, hR, hQβ, hcoeff, hcoef₀, hcoef₁, hβC]
  have hop := (fderiv ℝ V x).le_opNorm (x - x₀)
  rw [Real.norm_eq_abs] at hop
  have hgn : ‖gradient V x‖ = ‖fderiv ℝ V x‖ := by rw [gradient, LinearIsometryEquiv.norm_map]
  have hupper : fderiv ℝ V x (x - x₀) ≤ ‖gradient V x‖ * D := by
    rw [← hgn] at hop
    exact (le_abs_self _).trans (hop.trans
      (mul_le_mul_of_nonneg_left (hnorm x hx) (norm_nonneg _)))
  change c₂ / D * _ - B / D ≤ ‖gradient V x‖
  rw [div_mul_eq_mul_div, ← sub_div, div_le_iff₀ hD]
  linarith only [hlow, hupper]

/-- Internal retained-coordinate penalty Hessian bound. The constant is
independent of the interior point. Active inverse penalties have order four. -/
theorem internal_penalty_hessian_upper (n : ℕ) (L : ℝ) (θ : PhysicalCutoff)
    {a : ℝ} (ha : 0 < a) (J : Finset (Fin n)) (b : Bool) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ AffineSimplex.chartDomain n L,
      ∀ u : EuclideanSpace ℝ (Fin n),
      fderiv ℝ (fderiv ℝ (fun t => ∑ i ∈ J,
        (θ.val (a * t i) + if b then θ.val (a * (t i)⁻¹) else 0))) x u u ≤
          C * (1 + if b then ∑ i ∈ J, (x i)⁻¹ ^ 4 else 0) * ‖u‖ ^ 2 := by
  obtain ⟨C₀, hC₀, hup⟩ := PhysicalCollision.upper_penalty_curvature θ
  obtain ⟨C₁, hC₁, hinv⟩ := PhysicalCollision.inverse_penalty_curvature θ
  let C := C₀ * a ^ 2 * J.card + C₁ * a ^ 2 + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, fun x hx u => ?_⟩
  let φ : ℝ → ℝ := fun t => θ.val (a * t) + if b then θ.val (a / t) else 0
  have hφ (t : ℝ) (ht : 0 < t) : ContDiffAt ℝ ∞ φ t := by
    have hu := (PhysicalCollision.cutoff_contDiffAt θ (mul_pos ha ht)).comp t
      (contDiffAt_const.mul contDiffAt_id)
    cases b
    · simpa only [φ, Bool.false_eq_true, ↓reduceIte, add_zero, Function.comp_def] using hu
    · have hi := (PhysicalCollision.cutoff_contDiffAt θ (div_pos ha ht)).comp t
        (contDiffAt_const.div contDiffAt_id ht.ne')
      simpa only [φ, ↓reduceIte, Function.comp_def, Pi.div_apply] using hu.add hi
  have hφ'' (t : ℝ) (ht : 0 < t) : deriv (deriv φ) t ≤
      C₀ * a ^ 2 + if b then C₁ * a ^ 2 * t⁻¹ ^ 4 else 0 := by
    cases b
    · simpa only [φ, Bool.false_eq_true, ↓reduceIte, add_zero] using (hup a t ha ht).2
    · have hu := (PhysicalCollision.cutoff_contDiffAt θ (mul_pos ha ht)).comp t
        (contDiffAt_const.mul contDiffAt_id)
      have hi := (PhysicalCollision.cutoff_contDiffAt θ (div_pos ha ht)).comp t
        (contDiffAt_const.div contDiffAt_id ht.ne')
      have hh := PhysicalCollision.internal_hessian_add (hu.of_le (by simp)) (hi.of_le (by simp)) 1 1
      simp only [PhysicalCollision.internal_scalar_hessian, mul_one, Function.comp_def] at hh
      change deriv (deriv (fun t => θ.val (a * t) + θ.val (a / t))) t ≤ _
      rw [hh]
      exact add_le_add (hup a t ha ht).2 (hinv a t ha ht).2
  have hi (i : Fin n) : ContDiffAt ℝ 2
      (fun t : EuclideanSpace ℝ (Fin n) => φ (t i)) x :=
    ((hφ _ (hx.1 i)).comp x (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt).of_le (by simp)
  have hterm (i : Fin n) :
      fderiv ℝ (fderiv ℝ (fun t : EuclideanSpace ℝ (Fin n) => φ (t i))) x u u ≤
        (C₀ * a ^ 2 + if b then C₁ * a ^ 2 * (x i)⁻¹ ^ 4 else 0) * ‖u‖ ^ 2 := by
    have hh := PhysicalCollision.internal_scalar_affine_hessian φ (EuclideanSpace.proj (𝕜 := ℝ) i) 0
      (z := x) (by simpa only [EuclideanSpace.coe_proj, add_zero] using (hφ _ (hx.1 i)).of_le (by simp)) u
    simp only [add_zero, EuclideanSpace.coe_proj] at hh
    rw [hh]
    have hsq : (u i) ^ 2 ≤ ‖u‖ ^ 2 := by
      have ht := PiLp.norm_apply_le (p := (2 : ENNReal)) u i
      rw [Real.norm_eq_abs] at ht
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) ht 2
    have hnn : 0 ≤ C₀ * a ^ 2 + if b then C₁ * a ^ 2 * (x i)⁻¹ ^ 4 else 0 := by
      cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, add_zero] <;> positivity
    exact mul_le_mul (hφ'' _ (hx.1 i)) hsq (sq_nonneg _) hnn
  change fderiv ℝ (fderiv ℝ (fun t => ∑ i ∈ J, φ (t i))) x u u ≤ _
  rw [PhysicalCollision.internal_hessian_sum J _ (fun i _ => hi i) u]
  apply (Finset.sum_le_sum (s := J) (fun i _ => hterm i)).trans
  rw [← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg ‖u‖)
  have h₀ : C₀ * a ^ 2 * J.card ≤ C := by
    dsimp only [C]; linarith [mul_nonneg hC₁.le (sq_nonneg a)]
  have h₁ : C₁ * a ^ 2 ≤ C := by
    dsimp only [C]
    have : 0 ≤ C₀ * a ^ 2 * J.card :=
      mul_nonneg (mul_nonneg hC₀.le (sq_nonneg a)) (Nat.cast_nonneg J.card)
    linarith
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
    nlinarith only [h₀]
  · simp only [↓reduceIte, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
    have hs : 0 ≤ ∑ i ∈ J, (x i)⁻¹ ^ 4 := Finset.sum_nonneg fun i _ => pow_nonneg (inv_nonneg.mpr (hx.1 i).le) _
    nlinarith only [h₀, mul_le_mul_of_nonneg_right h₁ hs]

/-- See Appendix A of the paper: the penalized marginal trace has physical
order `s + 2` and active inverse-penalty order four. -/
theorem penalized_marginal_laplacian_upper (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff)
    {a : ℝ} (ha : 0 < a) (J : Finset (Fin n)) (b : Bool) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
      Laplacian.laplacian (fun t => p.val.1 * ∑ i ∈ J,
        (θ.val (a * t i) + if b then θ.val (a * (t i)⁻¹) else 0) -
          Real.log (∫ z : EuclideanSpace ℝ (Fin m),
            (ProperMarginalChart.chartDensity p n m σ (t,z)).toReal)) x ≤
      C * (1 + (⨅ j, face n ((n + m : ℕ) + 1) j x) ^ (-p.val.2 - 2) +
        if b then ∑ i ∈ J, (x i)⁻¹ ^ 4 else 0) := by
  obtain ⟨C₀, hC₀, hΔ⟩ := marginal_laplacian_upper p n m hn σ
  obtain ⟨Cp, hCp, hp⟩ := internal_penalty_hessian_upper n ((n + m : ℕ) + 1) θ ha J b
  let E := p.val.1 * n * Cp
  have hE : 0 ≤ E := by dsimp [E]; have := p.property.1; positivity
  refine ⟨C₀ + E, by positivity, fun x hx => ?_⟩
  let P := fun t : EuclideanSpace ℝ (Fin n) => ∑ i ∈ J,
    (θ.val (a * t i) + if b then θ.val (a * (t i)⁻¹) else 0)
  let V := fun t => -Real.log (∫ z : EuclideanSpace ℝ (Fin m),
    (ProperMarginalChart.chartDensity p n m σ (t,z)).toReal)
  have hP2 : ContDiffAt ℝ 2 P x :=
    ((active_penalty_smooth_convex n ((n + m : ℕ) + 1) θ ha J b).1.contDiffAt
      ((AffineSimplex.isOpen_chartDomain n _).mem_nhds hx)).of_le (by norm_num)
  have hV2 : ContDiffAt ℝ 2 V x :=
    ((MarginalHessian.physical_marginal_potential_smooth p n m hn σ).contDiffAt
      ((AffineSimplex.isOpen_chartDomain n _).mem_nhds hx)).of_le (by norm_num)
  have hh := PhysicalCollision.internal_laplacian_le P x _ (hp x hx)
  simp only [finrank_euclideanSpace_fin] at hh
  have hsum := (hP2.const_smul p.val.1).laplacian_add hV2
  have hmul := InnerProductSpace.laplacian_smul p.val.1 hP2
  change Laplacian.laplacian (fun y => p.val.1 • P y) x = p.val.1 • Laplacian.laplacian P x at hmul
  rw [hmul] at hsum
  change Laplacian.laplacian (fun t => p.val.1 * P t + V t) x =
    p.val.1 * Laplacian.laplacian P x + Laplacian.laplacian V x at hsum
  change Laplacian.laplacian (fun t => p.val.1 * P t + V t) x ≤ _
  rw [hsum]
  have h₀ := hΔ x hx
  rw [← minimum_face_eq n hn] at h₀
  have h₁ := mul_le_mul_of_nonneg_left hh p.property.1.le
  have hX := Real.rpow_nonneg (minimum_face_pos n ((n + m : ℕ) + 1) hx).le (-p.val.2 - 2)
  have hY : 0 ≤ if b then ∑ i ∈ J, (x i)⁻¹ ^ 4 else 0 := by
    cases b
    · exact le_rfl
    · exact Finset.sum_nonneg fun i _ => pow_nonneg (inv_nonneg.mpr (hx.1 i).le) _
  have hm₀ := mul_nonneg hC₀.le hY
  have hm₁ := mul_nonneg hE hX
  dsimp only [E] at hm₁ ⊢
  nlinarith only [h₀, h₁, hm₀, hm₁]

/-- Mixed-power absorption on the proper polytope,
using the physical marginal estimates. -/
theorem internal_mixed_collision (n : ℕ) (hn : 1 ≤ n) (L : ℝ) {s : ℝ} (hs : 0 < s)
    (J : Finset (Fin n)) (b : Bool) (V : EuclideanSpace ℝ (Fin n) → ℝ)
    {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hg : ∀ x ∈ AffineSimplex.chartDomain n L,
      c * ((⨅ j, face n L j x) ^ (-s - 1) + if b then ∑ i ∈ J, (x i)⁻¹ ^ 3 else 0) - C ≤
        ‖gradient V x‖)
    (hΔ : ∀ x ∈ AffineSimplex.chartDomain n L,
      Laplacian.laplacian V x ≤ C *
        (1 + (⨅ j, face n L j x) ^ (-s - 2) + if b then ∑ i ∈ J, (x i)⁻¹ ^ 4 else 0)) :
    ∀ A K : ℝ, 0 < A → 0 < K → ∃ D : ℝ, 0 ≤ D ∧
      ∀ x ∈ AffineSimplex.chartDomain n L,
        K * (Metric.infDist x (frontier (AffineSimplex.chartDomain n L)))⁻¹ ^ 2 - D ≤
          A * ‖gradient V x‖ ^ 2 - Laplacian.laplacian V x := by
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  intro A K hA hK
  let α := A * c ^ 2 / 4
  have hα : 0 < α := by positivity
  obtain ⟨G, hG, hlip⟩ := AffinePolytope.exists_lipschitz (face n L)
  obtain ⟨D₀, hD₀⟩ := RpowDomination.exists_bound hs hα hC.le
    (show 0 ≤ K * G ^ 2 by positivity)
  obtain ⟨D₁, hD₁⟩ := PhysicalCollision.internal_inverse_sum_absorption J hα hC.le
  let E := D₀ + (if b then D₁ else 0) + A * C ^ 2
  refine ⟨max E 0, le_max_right _ _, fun x hx => ?_⟩
  let δ := ⨅ j, face n L j x
  let X := δ ^ (-s - 1)
  let Y := if b then ∑ i ∈ J, (x i)⁻¹ ^ 3 else 0
  let Z := if b then ∑ i ∈ J, (x i)⁻¹ ^ 4 else 0
  have hδ : 0 < δ := minimum_face_pos n L hx
  have hX : 0 ≤ X := Real.rpow_nonneg hδ.le _
  have hY : 0 ≤ Y := by
    cases b
    · exact le_rfl
    · exact Finset.sum_nonneg fun i _ => pow_nonneg (inv_nonneg.mpr (hx.1 i).le) _
  have hinv : C * Z ≤ α * Y ^ 2 + if b then D₁ else 0 := by
    cases b
    · simp only [Y, Z, Bool.false_eq_true, ↓reduceIte, mul_zero, zero_pow, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, add_zero, le_refl]
    · exact hD₁ (fun i => x i) (fun i _ => hx.1 i)
  have hdom := hD₀ δ hδ
  have hd := AffinePolytope.div_le_infDist_frontier (face n L) (domain_eq_faces n L)
    (AffineSimplex.isBounded_chartDomain n L) hG hlip hx
  have hdpos : 0 < δ / G := div_pos hδ hG
  have hdsq := pow_le_pow_left₀ hdpos.le hd 2
  have hdist : (Metric.infDist x (frontier (AffineSimplex.chartDomain n L)))⁻¹ ^ 2 ≤ G ^ 2 * (δ ^ 2)⁻¹ := by
    have hh := inv_anti₀ (pow_pos hdpos 2) hdsq
    have he : ((δ / G) ^ 2)⁻¹ = G ^ 2 * (δ ^ 2)⁻¹ := by field_simp
    simpa only [he, inv_pow] using hh
  have hKdist := mul_le_mul_of_nonneg_left hdist hK.le
  have hgrad := ElementaryBarriers.sq_half_sub_le_sq
    (show 0 ≤ c * (X + Y) from mul_nonneg hc.le (add_nonneg hX hY)) (hg x hx)
  have hAgrad := mul_le_mul_of_nonneg_left hgrad hA.le
  have hxy : 0 ≤ α * X * Y := mul_nonneg (mul_nonneg hα.le hX) hY
  have hlead : α * X ^ 2 + α * Y ^ 2 ≤ A * (c * (X + Y)) ^ 2 / 2 := by
    dsimp only [α] at hxy ⊢
    nlinarith only [hxy, sq_nonneg X, sq_nonneg Y,
      mul_nonneg (mul_nonneg hA.le (sq_nonneg c)) (sq_nonneg X),
      mul_nonneg (mul_nonneg hA.le (sq_nonneg c)) (sq_nonneg Y)]
  have htrace := hΔ x hx
  change Laplacian.laplacian V x ≤ C * (1 + δ ^ (-s - 2) + Z) at htrace
  change C * (1 + δ ^ (-s - 2)) + K * G ^ 2 * (δ ^ 2)⁻¹ ≤ α * X ^ 2 + D₀ at hdom
  have hE : E ≤ max E 0 := le_max_left _ _
  dsimp only [E] at hE
  linarith only [hdom, hinv, hKdist, hAgrad, hlead, htrace, hE]

/-- See Appendix A of the paper, every allowed active penalty: the actual proper
marginal satisfies the all-coefficient intrinsic collision criterion. This
includes an empty active set, upper penalties and two-sided penalties. -/
theorem penalized_marginal_collision (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff)
    {a : ℝ} (ha : 0 < a) (J : Finset (Fin n)) (b : Bool) :
    let V := fun t => p.val.1 * ∑ i ∈ J,
      (θ.val (a * t i) + if b then θ.val (a * (t i)⁻¹) else 0) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity p n m σ (t,z)).toReal)
    ∀ A K : ℝ, 0 < A → 0 < K → ∃ D : ℝ, 0 ≤ D ∧
      ∀ x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
        K * (Metric.infDist x (frontier (AffineSimplex.chartDomain n ((n + m : ℕ) + 1))))⁻¹ ^ 2 - D ≤
          A * ‖gradient V x‖ ^ 2 - Laplacian.laplacian V x := by
  intro V
  obtain ⟨c, Cg, hc, hCg, hg⟩ := penalized_marginal_gradient_lower p n m hn σ θ ha J b
  obtain ⟨CΔ, hCΔ, hΔ⟩ := penalized_marginal_laplacian_upper p n m hn σ θ ha J b
  let C := max Cg CΔ
  have hC : 0 < C := lt_of_lt_of_le hCg (le_max_left _ _)
  apply internal_mixed_collision n hn ((n + m : ℕ) + 1) p.property.2.1 J b V hc hC
  · intro x hx
    exact (sub_le_sub_left (le_max_left Cg CΔ) _).trans (hg x hx)
  · intro x hx
    apply (hΔ x hx).trans
    apply mul_le_mul_of_nonneg_right (le_max_right Cg CΔ)
    have hδ := Real.rpow_nonneg (minimum_face_pos n ((n + m : ℕ) + 1) hx).le (-p.val.2 - 2)
    have hsum : 0 ≤ if b then ∑ i ∈ J, (x i)⁻¹ ^ 4 else 0 := by
      cases b
      · exact le_rfl
      · exact Finset.sum_nonneg fun i _ => pow_nonneg (inv_nonneg.mpr (hx.1 i).le) _
    linarith

/-- See Appendix A of the paper, complete proper marginal collision criterion.
The actual marginal on the Euclidean domain is smooth, strictly
convex, and satisfies the all-coefficient collision bound and the precise
ground-state bound of Appendix A, for every allowed active penalty.
The unforced marginal has the removable active/exterior-mass barrier
decomposition and both stated boundary derivative estimates. The parameters
`N = n + m + 1`, `n ≥ 1`, cover every proper marginal, including point fibres. -/
theorem proper_marginal_collision_criterion (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) (θ : PhysicalCutoff)
    {a : ℝ} (ha : 0 < a) (J : Finset (Fin n)) (b : Bool) :
    let Ω := properMarginalDomain ⟨n, by omega⟩ (n + m).succPNat
    let V₀ := fun t => -Real.log (∫ z : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p n m σ (t,z)).toReal)
    let V := fun t => p.val.1 * ∑ i ∈ J,
      (θ.val (a * t i) + if b then θ.val (a * (t i)⁻¹) else 0) + V₀ t
    (∃ R : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiffOn ℝ ∞ R Ω ∧ ConvexOn ℝ Ω R ∧ ∀ x ∈ Ω,
        V₀ x = 2 * p.val.1 * (∑ i, (x i) ^ (-p.val.2)) +
          2 * p.val.1 * (((n + m : ℕ) + 1) - ∑ i, x i) ^ (-p.val.2) + R x) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x ∈ Ω,
      let δ := min (⨅ i, x i) (((n + m : ℕ) + 1) - ∑ i, x i)
      c * δ ^ (-p.val.2 - 1) - C ≤ ‖gradient V₀ x‖ ∧
        Laplacian.laplacian V₀ x ≤ C * (1 + δ ^ (-p.val.2 - 2))) ∧
    ContDiffOn ℝ ∞ V Ω ∧
    (∃ κ : ℝ, 0 < κ ∧ ∀ x ∈ Ω, ∀ u : EuclideanSpace ℝ (Fin n),
      κ * ‖u‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x u u) ∧
    (∀ A K : ℝ, 0 < A → 0 < K → ∃ D : ℝ, 0 ≤ D ∧ ∀ x ∈ Ω,
      K * (Metric.infDist x (frontier Ω))⁻¹ ^ 2 - D ≤
        A * ‖gradient V x‖ ^ 2 - Laplacian.laplacian V x) ∧
    (∃ D : ℝ, 0 ≤ D ∧ ∀ x ∈ Ω,
      (Metric.infDist x (frontier Ω))⁻¹ ^ 2 - D ≤
        (1 / 4 : ℝ) * ‖gradient V x‖ ^ 2 - (1 / 2 : ℝ) * Laplacian.laplacian V x) := by
  intro Ω V₀ V
  have hΩ : Ω = AffineSimplex.chartDomain n ((n + m : ℕ) + 1) := by
    simp only [Ω, properMarginalDomain, AffineSimplex.chartDomain, PNat.mk_coe, Nat.succPNat_coe,
      Nat.cast_add, Nat.cast_succ]
  rw [hΩ]
  have hc := penalized_marginal_collision p n m hn σ θ ha J b
  refine ⟨marginal_barrier_decomposition p n m hn σ, ?_,
    MarginalHessian.physical_penalized_marginal_potential_smooth p n m hn σ θ ha J b,
    penalized_marginal_strict_curvature p n m hn σ θ ha J b, hc, ?_⟩
  · obtain ⟨c, Cg, hcp, hCg, hg⟩ := marginal_gradient_lower p n m hn σ
    obtain ⟨CΔ, hCΔ, hΔ⟩ := marginal_laplacian_upper p n m hn σ
    refine ⟨c, max Cg CΔ, hcp, lt_of_lt_of_le hCg (le_max_left _ _), fun x hx => ?_⟩
    constructor
    · exact (sub_le_sub_left (le_max_left Cg CΔ) _).trans (hg x hx)
    · apply (hΔ x hx).trans
      apply mul_le_mul_of_nonneg_right (le_max_right Cg CΔ)
      have hδ := minimum_face_pos n ((n + m : ℕ) + 1) hx
      rw [minimum_face_eq n hn] at hδ
      exact add_nonneg zero_le_one (Real.rpow_nonneg hδ.le _)
  · obtain ⟨D, hD, hb⟩ := hc (1 / 2) 2 (by norm_num) (by norm_num)
    refine ⟨D / 2, div_nonneg hD (by norm_num), fun x hx => ?_⟩
    have h := hb x hx
    change (Metric.infDist x (frontier (AffineSimplex.chartDomain n ((n + m : ℕ) + 1))))⁻¹ ^ 2 - D / 2 ≤
      (1 / 4 : ℝ) * ‖gradient V x‖ ^ 2 - (1 / 2 : ℝ) * Laplacian.laplacian V x
    change 2 * (Metric.infDist x (frontier (AffineSimplex.chartDomain n ((n + m : ℕ) + 1))))⁻¹ ^ 2 - D ≤
      (1 / 2 : ℝ) * ‖gradient V x‖ ^ 2 - Laplacian.laplacian V x at h
    linarith only [h]

end Riesz2.MarginalCollision
