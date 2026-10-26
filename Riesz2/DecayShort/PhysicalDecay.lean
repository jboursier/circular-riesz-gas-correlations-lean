/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.PhysicalComparisonPart4
public import Riesz2.ToMathlib.NeumannScalarDirichlet
public import Riesz2.HelfferSjostrand.DifferentiatedPoissonPart3

/-!
# Physical short-range decay

Supporting steps for Proposition 4.10, using the actual
auxiliary physical matrix and the scalar form. The
proper-marginal auxiliary estimate keeps both the internal-boundary and
exterior-size errors.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace Riesz2.DecayShort.PhysicalDecay

open PhysicalComparison

/-- Internal final absorption step of Proposition 4.10.
An exponentially small additive correction can be placed inside any
positive profile bounded below by a fixed inverse power. This covers
both the proper profile and the full-cycle profile. -/
theorem internal_insert_exponential_error {t δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (n P F G e : ℝ), 1 ≤ n → 0 ≤ P → 0 ≤ F → 0 ≤ G →
      n^(-t) ≤ e →
      P*e*F+P*Real.exp (-c*n^δ)*G ≤
        B*P*e*(F+Real.exp (-(c/2)*n^δ)*G) := by
  obtain ⟨D,hD,hbound⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := t) (c := c) (c' := c/2) hδ (by linarith)
  refine ⟨1+D,by linarith,?_⟩
  intro n P F G e hn hP hF hG he
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have he0 : 0 ≤ e := (Real.rpow_pos_of_pos hn0 (-t)).le.trans he
  have hpow : n^(-t)*n^t = 1 := by rw [← Real.rpow_add hn0]; simp
  have htail : Real.exp (-c*n^δ) ≤ D*e*Real.exp (-(c/2)*n^δ) := by
    have hh := mul_le_mul_of_nonneg_left (hbound n hn) (Real.rpow_nonneg hn0.le (-t))
    have hmul := mul_le_mul_of_nonneg_left he hD
    have hmul' := mul_le_mul_of_nonneg_right hmul (Real.exp_pos (-(c/2)*n^δ)).le
    calc
      _ = n^(-t)*(n^t*Real.exp (-c*n^δ)) := by rw [← mul_assoc,hpow,one_mul]
      _ ≤ n^(-t)*(D*Real.exp (-(c/2)*n^δ)) := hh
      _ ≤ D*e*Real.exp (-(c/2)*n^δ) := by nlinarith only [hmul']
  have htail' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htail hP) hG
  have hpos₁ : 0 ≤ D*(P*e*F) := by positivity
  have hpos₂ : 0 ≤ P*e*Real.exp (-(c/2)*n^δ)*G := by positivity
  nlinarith only [htail',hpos₁,hpos₂]

end Riesz2.DecayShort.PhysicalDecay

namespace Riesz2.DecayShort.PhysicalDecay

open Set

private theorem internal_gibbs_of_normalized_density {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    (σ ρ : Measure E) [IsProbabilityMeasure ρ] (U : Set E) (hU : MeasurableSet U)
    (V : E → ℝ) (hV : ContDiffOn ℝ (⊤ : ℕ∞) V U)
    (f : E → ℝ≥0∞) (C : ℝ≥0∞) (hCt : C ≠ ⊤)
    (hρ : ρ = C • σ.withDensity f)
    (hdensity : U.indicator (fun x => ENNReal.ofReal (Real.exp (-V x))) =
      fun x => C*f x) : IsEuclideanGibbsPotential σ ρ U V := by
  have hmeasure : (σ.restrict U).withDensity
      (fun x => ENNReal.ofReal (Real.exp (-V x))) = ρ := by
    calc
      _ = σ.withDensity (U.indicator (fun x => ENNReal.ofReal (Real.exp (-V x)))) :=
        (withDensity_indicator hU _).symm
      _ = σ.withDensity (fun x => C*f x) := congrArg (Measure.withDensity σ) hdensity
      _ = C • σ.withDensity f := withDensity_smul' C f hCt
      _ = ρ := hρ.symm
  have hmass : (∫⁻ x, ENNReal.ofReal (Real.exp (-V x)) ∂σ.restrict U) = 1 := by
    have ht := congrArg (fun μ : Measure E => μ univ) hmeasure
    simpa only [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,measure_univ] using ht
  refine ⟨hV,?_,?_,?_⟩
  · rw [hmass]; exact zero_lt_one
  · rw [hmass]; exact ENNReal.one_lt_top
  · rw [hmass,inv_one,one_smul,hmeasure]

set_option backward.isDefEq.respectTransparency false in
/-- The actual proper physical law in Proposition 4.10
has a smooth Gibbs potential. The potential differs by a constant from
beta times the exact marginal potential used in the auxiliary matrix.
Both penalties and the point exterior fibre are included. -/
theorem proper_physical_gibbs (p : Parameters) (hs : 1 < p.val.2)
    (n : ℕ+) (m : ℕ) (hn : (n : ℕ) ≤ (((n : ℕ)+m).succPNat : ℕ))
    (θ : PhysicalCutoff) (h : ℝ) (hh : 0 < h) (b : Bool) :
    let F := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      ∑ i, (θ.val (((n : ℝ)^h)⁻¹*x i) +
        if b then θ.val (((n : ℝ)^h)⁻¹*(x i)⁻¹) else 0)
    let K := fun x => p.val.1⁻¹*(p.val.1*F x-
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal))
    ∃ (V : EuclideanSpace ℝ (Fin (n : ℕ)) → ℝ) (k : ℝ),
      (∀ x, V x = p.val.1*K x+k) ∧
      IsEuclideanGibbsPotential volume
        (activeTiltedGapLaw p ((n : ℕ)+m).succPNat n hn θ h b)
        (properMarginalDomain n ((n : ℕ)+m).succPNat) V := by
  classical
  intro F K
  let N := ((n : ℕ)+m).succPNat
  let U := AffineSimplex.chartDomain n ((n+m : ℕ)+1)
  let D := ProperMarginalChart.penalizedChartDensity p n m (Equiv.refl _) θ
    ((n : ℝ)^(-h)) (Finset.univ.map (Fin.castLEEmb hn)) b
  let f := AffineFibre.fibreMass volume D
  let ν := activeTiltedGapLaw p N n hn θ h b
  let C := (tiltNormalizer p N n hn θ h b)⁻¹ * (partitionFunction p N)⁻¹ *
    ENNReal.ofReal (((n+m+1 : ℝ)^((n : ℕ)+m))⁻¹)
  have hU : IsOpen U := AffineSimplex.isOpen_chartDomain _ _
  obtain ⟨hZ0,hZt,hprob,hν⟩ := ProperMarginalChart.activeTiltedGapLaw_density_valid p n m hn θ h b
  have : IsProbabilityMeasure ν := hprob
  obtain ⟨_,_,hP0,hPt⟩ := finiteModel_valid p N
  have hJ : 0 < ((n+m+1 : ℝ)^((n : ℕ)+m)) := by positivity
  have hJ0 : ENNReal.ofReal (((n+m+1 : ℝ)^((n : ℕ)+m))⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr hJ)).ne'
  have hC0 : C ≠ 0 := by
    dsimp only [C]
    exact mul_ne_zero (mul_ne_zero (ENNReal.inv_ne_zero.mpr hZt.ne)
      (ENNReal.inv_ne_zero.mpr hPt.ne)) hJ0
  have hCt : C ≠ ⊤ := by
    dsimp only [C]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hZ0.ne')
      (ENNReal.inv_ne_top.mpr hP0.ne')) ENNReal.ofReal_ne_top
  have hCpos : 0 < C.toReal := ENNReal.toReal_pos hC0 hCt
  have hν' : ν = C • volume.withDensity f := by
    simpa only [ν,C,f,D,N,smul_smul,mul_assoc] using hν
  let V := fun x => p.val.1*K x-Real.log C.toReal
  have hV : ContDiffOn ℝ (⊤ : ℕ∞) V U := by
    have hk := (PhysicalFibres.active_marginal_curvature p hs n m n.pos
      (Equiv.refl _) θ h hh b).1
    exact (contDiffOn_const.mul hk).sub contDiffOn_const
  have hval (x) (hx : x ∈ U) : ENNReal.ofReal (Real.exp (-V x)) = C*f x := by
    obtain ⟨hf0,hft,hK⟩ := PhysicalFibres.active_marginal_potential_density p n m hn θ h b hx
    change K x = -p.val.1⁻¹*Real.log (f x).toReal at hK
    have hp : p.val.1 ≠ 0 := p.property.1.ne'
    have he : -V x = Real.log (f x).toReal+Real.log C.toReal := by
      dsimp only [V]
      rw [hK]
      field_simp
      ring
    rw [he,Real.exp_add,Real.exp_log (ENNReal.toReal_pos hf0 hft),
      Real.exp_log hCpos,ENNReal.ofReal_mul (ENNReal.toReal_nonneg),
      ENNReal.ofReal_toReal hft,ENNReal.ofReal_toReal hCt,mul_comm]
  have hoff (x) (hx : x ∉ U) : f x = 0 := by
    change (∫⁻ z : EuclideanSpace ℝ (Fin m), D (x,z)) = 0
    calc
      _ = ∫⁻ _z : EuclideanSpace ℝ (Fin m), (0 : ℝ≥0∞) := by
        apply lintegral_congr
        intro z
        have hz : (x,z) ∉ RetainedSimplex.domain n m ((n+m : ℕ)+1) := by
          intro hz
          obtain ⟨hxpos,hzpos,hsum⟩ := (RetainedSimplex.mem_domain n m _ (x,z)).mp hz
          have hzsum : 0 ≤ ∑ i, z i := Finset.sum_nonneg fun i _ => (hzpos i).le
          exact hx ⟨hxpos,by linarith⟩
        exact indicator_of_notMem hz _
      _ = 0 := lintegral_zero
  have hdensity : U.indicator (fun x => ENNReal.ofReal (Real.exp (-V x))) =
      fun x => C*f x := by
    funext x
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx,hval x hx]
    · rw [indicator_of_notMem hx,hoff x hx,mul_zero]
  refine ⟨V,-Real.log C.toReal,fun _ => by dsimp only [V]; ring,?_⟩
  rw [← ProperMarginalChart.baseDomain_eq_properMarginalDomain n m]
  exact internal_gibbs_of_normalized_density volume ν U hU.measurableSet V hV f C hCt hν' hdensity

set_option backward.isDefEq.respectTransparency false in
/-- The proper-law analytic conclusions of Proposition 4.10:
positive finite tilt normalization, the smooth physical Gibbs potential,
its closed conservative Neumann form, and unique natural-energy weak
solvability for every L² source. No exceptional-set or decay estimate is
assumed here. The case of a single exterior gap is included. -/
theorem proper_physical_wellposed (p : Parameters) (hs : 1 < p.val.2)
    (n : ℕ+) (m : ℕ) (hn : (n : ℕ) ≤ (((n : ℕ)+m).succPNat : ℕ))
    (θ : PhysicalCutoff) (h : ℝ) (hh : 0 < h) (b : Bool) :
    let N := ((n : ℕ)+m).succPNat
    let ν := activeTiltedGapLaw p N n hn θ h b
    0 < tiltNormalizer p N n hn θ h b ∧ tiltNormalizer p N n hn θ h b < ⊤ ∧
      IsProbabilityMeasure ν ∧
      ∃ (V : EuclideanSpace ℝ (Fin (n : ℕ)) → ℝ) (Q : ScalarFormData ν),
        IsEuclideanGibbsPotential volume ν (properMarginalDomain n N) V ∧
        IsNeumannRealization (properMarginalDomain n N) Q ∧
        IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
        ∀ f : Fin (n : ℕ) → Lp ℝ 2 ν,
          ∃! u : Fin (n : ℕ) → Q.1, WeightedWeakSolution Q (hessianMatrix V) ⊤ f u := by
  intro N ν
  obtain ⟨hz,ht,hprob,_⟩ := ProperMarginalChart.activeTiltedGapLaw_density_valid p n m hn θ h b
  refine ⟨hz,ht,hprob,?_⟩
  let U := AffineSimplex.chartDomain n ((n+m : ℕ)+1)
  let F := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
    ∑ i, (θ.val (((n : ℝ)^h)⁻¹*x i) +
      if b then θ.val (((n : ℝ)^h)⁻¹*(x i)⁻¹) else 0)
  let K := fun x => p.val.1⁻¹*(p.val.1*F x-
    Real.log (∫ z : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal))
  obtain ⟨V,k,hVk,hG⟩ := proper_physical_gibbs p hs n m hn θ h hh b
  change (∀ x, V x = p.val.1*K x+k) at hVk
  rw [← ProperMarginalChart.baseDomain_eq_properMarginalDomain n m] at hG ⊢
  have hU : IsOpen U := AffineSimplex.isOpen_chartDomain _ _
  have hB : Bornology.IsBounded U := AffineSimplex.isBounded_chartDomain _ _
  let Q := IntrinsicScalarCore.form hU hB hG
  have hQ : IsClosedScalarDirichletForm Q := IntrinsicScalarCore.closed_dirichlet hU hB hG
  refine ⟨V,Q,hG,IntrinsicScalarCore.realization hU hB hG,hQ,
    IntrinsicScalarCore.conservative hU hB hG,?_⟩
  obtain ⟨hK,hcurv⟩ := PhysicalFibres.active_marginal_curvature p hs n m n.pos
    (Equiv.refl _) θ h hh b
  change ContDiffOn ℝ (⊤ : ℕ∞) K U at hK
  let a := p.val.1*(n : ℝ)^(-(p.val.2+2)*h)
  have ha : 0 < a := mul_pos p.property.1 (Real.rpow_pos_of_pos (by exact_mod_cast n.pos) _)
  have hH (x) (hx : x ∈ U) (u : EuclideanSpace ℝ (Fin (n : ℕ))) :
      a*‖u‖^2 ≤ fderiv ℝ (fderiv ℝ V) x u u := by
    have he : fderiv ℝ V = fderiv ℝ (fun y => p.val.1*K y) := by
      rw [funext hVk]
      funext y
      exact fderiv_add_const k
    rw [he,PhysicalCollision.internal_hessian_const_mul
      ((hK.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num))]
    change p.val.1*((n : ℝ)^(-(p.val.2+2)*h))*‖u‖^2 ≤
      p.val.1*fderiv ℝ (fderiv ℝ K) x u u
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hcurv x hx u) p.property.1.le
  have hM : ∀ᵐ x ∂ν, (hessianMatrix V x).PosSemidef :=
    (IntrinsicScalarCore.supported hU hG).mono fun x hx =>
      DifferentiatedPoisson.hessian_posSemidef_on hU hG
        (fun x hx u => (mul_nonneg ha.le (sq_nonneg ‖u‖)).trans (hH x hx u)) x hx
  have hlower : ∀ᵐ x ∂ν, ∀ t ∈ (⊤ : Submodule ℝ (Fin (n : ℕ) → ℝ)),
      a*(∑ i, t i^2) ≤ ∑ i, ∑ j, t i*hessianMatrix V x i j*t j :=
    (IntrinsicScalarCore.supported hU hG).mono fun x hx t _ =>
      DifferentiatedPoisson.hessian_coordinate_lower hU hG hH x hx t
  intro f
  exact MatrixEnergy.weightedWeakSolution_existsUnique Q hQ (hessianMatrix V) ⊤ hM a ha hlower
    DifferentiatedPoisson.measurable_hessian_entries f

end Riesz2.DecayShort.PhysicalDecay
