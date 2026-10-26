/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.AffineObservableSobolev
public import Riesz2.DecayShort.PhysicalDecayPart7
public import Riesz2.HelfferSjostrand.MarginalCollision
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Uniqueness of Gibbs potentials and Neumann realizations

The interfaces determine the scalar form uniquely and the
potential up to a constant on an open domain. These facts allow the covariance
representation in Theorem 2 to use the very same witnesses
as the physical decay theorem.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Riesz2.GibbsPotentialComparison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} {U : Set E}

omit [BorelSpace E] in
/-- The Neumann graph determines its whole scalar form, including
mixed energies (Subsection 4.1). -/
theorem neumannRealization_unique (Q R : ScalarFormData μ)
    (hQ : IsNeumannRealization U Q) (hR : IsNeumannRealization U R) : Q = R := by
  have hD : Q.1 = R.1 := by
    ext f
    exact (hQ.1 f).trans (hR.1 f).symm
  obtain ⟨D, q⟩ := Q
  obtain ⟨D', r⟩ := R
  dsimp only at hD
  subst D'
  congr 1
  ext f g
  obtain ⟨df, hf⟩ := (hQ.1 f.val).mp f.property
  obtain ⟨dg, hg⟩ := (hQ.1 g.val).mp g.property
  exact (hQ.2.2 f g df dg hf hg).trans (hR.2.2 f g df dg hf hg).symm

/-- Two smooth Gibbs potentials of the same law differ by a constant on
their open domain (Appendix A). No connectedness is needed because
the density normalization is global. -/
theorem potential_eqOn_add_const (hU : IsOpen U) {V W : E → ℝ}
    (hV : IsEuclideanGibbsPotential volume μ U V)
    (hW : IsEuclideanGibbsPotential volume μ U W) :
    ∃ c : ℝ, EqOn V (fun x => W x + c) U := by
  let ZV := ∫⁻ x, ENNReal.ofReal (Real.exp (-V x)) ∂volume.restrict U
  let ZW := ∫⁻ x, ENNReal.ofReal (Real.exp (-W x)) ∂volume.restrict U
  have hZv : 0 < ZV := hV.2.1
  have hZw : 0 < ZW := hW.2.1
  have hZvt : ZV ≠ ⊤ := hV.2.2.1.ne
  have hZwt : ZW ≠ ⊤ := hW.2.2.1.ne
  let fv := fun x => ZV⁻¹ * ENNReal.ofReal (Real.exp (-V x))
  let fw := fun x => ZW⁻¹ * ENNReal.ofReal (Real.exp (-W x))
  have hfv : ContinuousOn fv U :=
    (ENNReal.continuous_const_mul (ENNReal.inv_ne_top.mpr hZv.ne')).comp_continuousOn
      (ENNReal.continuous_ofReal.comp_continuousOn
        (Real.continuous_exp.comp_continuousOn hV.1.continuousOn.neg))
  have hfw : ContinuousOn fw U :=
    (ENNReal.continuous_const_mul (ENNReal.inv_ne_top.mpr hZw.ne')).comp_continuousOn
      (ENNReal.continuous_ofReal.comp_continuousOn
        (Real.continuous_exp.comp_continuousOn hW.1.continuousOn.neg))
  have he : (volume.restrict U).withDensity fv = (volume.restrict U).withDensity fw := by
    rw [show (volume.restrict U).withDensity fv =
        ZV⁻¹ • (volume.restrict U).withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))
      from withDensity_smul' _ _ (ENNReal.inv_ne_top.mpr hZv.ne')]
    rw [show (volume.restrict U).withDensity fw =
        ZW⁻¹ • (volume.restrict U).withDensity (fun x => ENNReal.ofReal (Real.exp (-W x)))
      from withDensity_smul' _ _ (ENNReal.inv_ne_top.mpr hZw.ne')]
    exact hV.2.2.2.symm.trans hW.2.2.2
  have hae : fv =ᵐ[volume.restrict U] fw :=
    (withDensity_eq_iff_of_sigmaFinite
      (hfv.aemeasurable hU.measurableSet) (hfw.aemeasurable hU.measurableSet)).mp he
  have hall := Measure.eqOn_open_of_ae_eq hae hU hfv hfw
  refine ⟨Real.log ZW.toReal - Real.log ZV.toReal, fun x hx => ?_⟩
  have hvpos : 0 < ZV.toReal := ENNReal.toReal_pos hZv.ne' hZvt
  have hwpos : 0 < ZW.toReal := ENNReal.toReal_pos hZw.ne' hZwt
  have hr := congrArg ENNReal.toReal (hall hx)
  change (ZV⁻¹ * ENNReal.ofReal (Real.exp (-V x))).toReal =
    (ZW⁻¹ * ENNReal.ofReal (Real.exp (-W x))).toReal at hr
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hr
  have hl := congrArg Real.log hr
  rw [Real.log_mul (inv_ne_zero hvpos.ne') (Real.exp_ne_zero _),
    Real.log_mul (inv_ne_zero hwpos.ne') (Real.exp_ne_zero _),
    Real.log_inv, Real.log_inv, Real.log_exp, Real.log_exp] at hl
  linarith

/-- Absolutely continuous Euclidean laws have absolutely continuous
coordinate marginals, including dimension one (Theorem 1). -/
theorem coordinate_absolutelyContinuous {ι : Type*} [Fintype ι]
    {ν : Measure (EuclideanSpace ℝ ι)} (hν : ν ≪ volume) (i : ι) :
    ν.map (fun x => x i) ≪ volume := by
  have hp := (Measure.quasiMeasurePreserving_eval (fun _ : ι => (volume : Measure ℝ)) i).comp
    (PiLp.volume_preserving_ofLp ι).quasiMeasurePreserving
  exact (hν.map (by fun_prop)).trans hp.absolutelyContinuous

end Riesz2.GibbsPotentialComparison

namespace Riesz2.GibbsPotentialComparison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {U : Set E} {V W : E → ℝ}

/-- Adding a constant on an open domain changes none of the derivatives
in the physical covariance equation, Theorem 2. -/
theorem derivatives_eq_of_eqOn_add_const (hU : IsOpen U) {c : ℝ}
    (h : EqOn V (fun x => W x + c) U) (x : E) (hx : x ∈ U) :
    fderiv ℝ V x = fderiv ℝ W x ∧
    fderiv ℝ (fderiv ℝ V) x = fderiv ℝ (fderiv ℝ W) x ∧
    gradient V x = gradient W x ∧
    Laplacian.laplacian V x = Laplacian.laplacian W x := by
  have he : V =ᶠ[𝓝 x] (fun y => W y + c) :=
    (hU.eventually_mem hx).mono fun y hy => h hy
  have hd : fderiv ℝ V =ᶠ[𝓝 x] fderiv ℝ W :=
    he.fderiv.trans (Eventually.of_forall fun y => fderiv_add_const c)
  have hdd := hd.fderiv_eq (𝕜 := ℝ)
  refine ⟨hd.eq_of_nhds, hdd, congrArg (InnerProductSpace.toDual ℝ E).symm hd.eq_of_nhds, ?_⟩
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, hdd]

end Riesz2.GibbsPotentialComparison

namespace Riesz2.DecayShort.ShortRangeResultPart2

open GibbsPotentialComparison

set_option backward.isDefEq.respectTransparency false in
/-- Internal witness bridge for Theorem 2: every Gibbs
potential for the actual proper tilted marginal has the established strict
curvature and collision barrier. These are proved for the physical potential
and transferred by density uniqueness, including point exterior fibres. -/
theorem internal_proper_analytic (p : Parameters) (hs : 1 < p.val.2)
    (n : ℕ+) (m : ℕ) (hn : (n : ℕ) ≤ (((n : ℕ)+m).succPNat : ℕ))
    (θ : PhysicalCutoff) (h : ℝ) (hh : 0 < h) (b : Bool)
    (V : EuclideanSpace ℝ (Fin (n : ℕ)) → ℝ)
    (hV : IsEuclideanGibbsPotential volume
      (activeTiltedGapLaw p ((n : ℕ)+m).succPNat n hn θ h b)
      (properMarginalDomain n ((n : ℕ)+m).succPNat) V) :
    (∃ κ : ℝ, 0 < κ ∧ ∀ x ∈ properMarginalDomain n ((n : ℕ)+m).succPNat,
      ∀ e, κ * ‖e‖^2 ≤ fderiv ℝ (fderiv ℝ V) x e e) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ properMarginalDomain n ((n : ℕ)+m).succPNat,
      (Metric.infDist x (frontier (properMarginalDomain n ((n : ℕ)+m).succPNat)))⁻¹^2-C ≤
        ‖gradient V x‖^2/4-Laplacian.laplacian V x/2) := by
  classical
  let U := properMarginalDomain n ((n : ℕ)+m).succPNat
  have hU : IsOpen U := by
    dsimp only [U]
    rw [← ProperMarginalChart.baseDomain_eq_properMarginalDomain n m]
    exact AffineSimplex.isOpen_chartDomain _ _
  let P := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
    p.val.1 * ∑ i, (θ.val (((n : ℝ)^h)⁻¹*x i) +
      if b then θ.val (((n : ℝ)^h)⁻¹*(x i)⁻¹) else 0) -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal)
  obtain ⟨W,k,hW,hG⟩ := PhysicalDecay.proper_physical_gibbs p hs n m hn θ h hh b
  obtain ⟨c,hc⟩ := potential_eqOn_add_const hU hV hG
  have he : EqOn V (fun x => P x+(k+c)) U := by
    intro x hx
    change V x = P x+(k+c)
    rw [hc hx]
    change W x+c = P x+(k+c)
    rw [hW x]
    change p.val.1*(p.val.1⁻¹*P x)+k+c = P x+(k+c)
    rw [mul_inv_cancel_left₀ p.property.1.ne']
    ring
  have ha : 0 < ((n : ℝ)^h)⁻¹ := inv_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)
  obtain ⟨_,_,_,⟨κ,hκ,hH⟩,_,⟨C,hC,hbar⟩⟩ :=
    MarginalCollision.proper_marginal_collision_criterion p n m n.pos
      (Equiv.refl _) θ ha Finset.univ b
  change (∀ x ∈ U, ∀ e, κ*‖e‖^2 ≤ fderiv ℝ (fderiv ℝ P) x e e) at hH
  change (∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹^2-C ≤
    (1/4 : ℝ)*‖gradient P x‖^2-(1/2 : ℝ)*Laplacian.laplacian P x) at hbar
  refine ⟨⟨κ,hκ,fun x hx e => ?_⟩,⟨C,hC,fun x hx => ?_⟩⟩
  · rw [(derivatives_eq_of_eqOn_add_const hU he x hx).2.1]
    exact hH x hx e
  · obtain ⟨_,_,hg,hΔ⟩ := derivatives_eq_of_eqOn_add_const hU he x hx
    rw [hg,hΔ]
    convert hbar x hx using 1; ring

set_option backward.isDefEq.respectTransparency false in
/-- Internal covariance representation for the actual proper tilted marginal
in Theorem 2. It uses any physical Gibbs and Neumann
witnesses, hence the exact witnesses supplied by physical decay. Observable
and derivative L² membership are conclusions. -/
theorem internal_proper_coordinate_covariance (p : Parameters) (hs : 1 < p.val.2)
    (n : ℕ+) (m : ℕ) (hn : (n : ℕ) ≤ (((n : ℕ)+m).succPNat : ℕ))
    (θ : PhysicalCutoff) (h : ℝ) (hh : 0 < h) (b : Bool)
    (V : EuclideanSpace ℝ (Fin (n : ℕ)) → ℝ)
    (Q : ScalarFormData (activeTiltedGapLaw p ((n : ℕ)+m).succPNat n hn θ h b))
    (hV : IsEuclideanGibbsPotential volume
      (activeTiltedGapLaw p ((n : ℕ)+m).succPNat n hn θ h b)
      (properMarginalDomain n ((n : ℕ)+m).succPNat) V)
    (hQ : IsNeumannRealization (properMarginalDomain n ((n : ℕ)+m).succPNat) Q)
    (i j : Fin (n : ℕ)) (f g : GapObservable) :
    let ν := activeTiltedGapLaw p ((n : ℕ)+m).succPNat n hn θ h b
    ∃ χ η : Lp ℝ 2 ν,
      χ =ᵐ[ν] (fun x => f.val.2 (x i)) ∧ η =ᵐ[ν] (fun x => g.val.2 (x j)) ∧
      eLpNorm χ ∞ ν < ⊤ ∧ eLpNorm η ∞ ν < ⊤ ∧
      MemLp (fun x => f.val.1 (x i)) 2 ν ∧ MemLp (fun x => g.val.1 (x j)) 2 ν ∧
      ∃ u : Fin (n : ℕ) → Q.1,
        WeightedWeakSolution Q (hessianMatrix V) ⊤ (fun k => if k=i then χ else 0) u ∧
        ProbabilityTheory.covariance (fun x => f.val.1 (x i)) (fun x => g.val.1 (x j)) ν =
          inner ℝ η (u j).val := by
  intro ν
  let U := properMarginalDomain n ((n : ℕ)+m).succPNat
  have hU : IsOpen U := by
    dsimp only [U]
    rw [← ProperMarginalChart.baseDomain_eq_properMarginalDomain n m]
    exact AffineSimplex.isOpen_chartDomain _ _
  have hB : Bornology.IsBounded U := by
    dsimp only [U]
    rw [← ProperMarginalChart.baseDomain_eq_properMarginalDomain n m]
    exact AffineSimplex.isBounded_chartDomain _ _
  have hc : Convex ℝ U := by
    dsimp only [U]
    rw [← ProperMarginalChart.baseDomain_eq_properMarginalDomain n m]
    exact AffineSimplex.convex_chartDomain _ _
  obtain ⟨⟨κ,hκ,hH⟩,⟨C,hC,hbar⟩⟩ := internal_proper_analytic p hs n m hn θ h hh b V hV
  have hac : ν ≪ volume := by
    dsimp only [ν]
    rw [hV.2.2.2]
    exact Measure.smul_absolutelyContinuous.trans ((withDensity_absolutelyContinuous _ _).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self))
  have hi := coordinate_absolutelyContinuous hac i
  have hj := coordinate_absolutelyContinuous hac j
  obtain ⟨Lf,hf⟩ := f.property.1
  obtain ⟨Lg,hg⟩ := g.property.1
  have hQeq : Q = IntrinsicScalarCore.form hU hB hV :=
    neumannRealization_unique Q _ hQ (IntrinsicScalarCore.realization hU hB hV)
  subst Q
  obtain ⟨χ,η,hχ,hη,hF,hG,u,hu,hcov⟩ :=
    AffineObservableSobolev.internal_coordinate_covariance n.pos hU hB hc hV hκ hH
      hC hbar i j hf hg f.property.2.2.1 g.property.2.2.1 hi hj
  refine ⟨χ,η,hχ,hη,?_,?_,hF,hG,u,hu,hcov⟩
  · rw [eLpNorm_congr_ae hχ]
    have hm : Measurable (fun x : EuclideanSpace ℝ (Fin (n : ℕ)) => x i) := by fun_prop
    change eLpNorm (f.val.2 ∘ (fun x : EuclideanSpace ℝ (Fin (n : ℕ)) => x i)) ∞ ν < ⊤
    rw [eLpNorm_exponent_top (f.property.2.1.comp_quasiMeasurePreserving ⟨hm,hi⟩)]
    apply (eLpNormEssSup_le_of_ae_enorm_bound
      (ae_of_ae_map hm.aemeasurable (hi.ae_le
        (enorm_ae_le_eLpNormEssSup f.val.2 volume)))).trans_lt
    exact eLpNormEssSup_le_eLpNorm_top.trans_lt f.property.2.2.2
  · rw [eLpNorm_congr_ae hη]
    have hm : Measurable (fun x : EuclideanSpace ℝ (Fin (n : ℕ)) => x j) := by fun_prop
    change eLpNorm (g.val.2 ∘ (fun x : EuclideanSpace ℝ (Fin (n : ℕ)) => x j)) ∞ ν < ⊤
    rw [eLpNorm_exponent_top (g.property.2.1.comp_quasiMeasurePreserving ⟨hm,hj⟩)]
    apply (eLpNormEssSup_le_of_ae_enorm_bound
      (ae_of_ae_map hm.aemeasurable (hj.ae_le
        (enorm_ae_le_eLpNormEssSup g.val.2 volume)))).trans_lt
    exact eLpNormEssSup_le_eLpNorm_top.trans_lt g.property.2.2.2

end Riesz2.DecayShort.ShortRangeResultPart2

namespace Riesz2.DecayShort.ShortRangeResultPart2

set_option backward.isDefEq.respectTransparency false in
/-- Internal version of the proper covariance bridge with the size
parameters `N,n`, Theorem 2. It covers every proper
block, not only blocks of size at most half the system. -/
theorem internal_proper_coordinate_covariance_of_lt
    (p : Parameters) (hs : 1 < p.val.2) (N n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ))
    (hlt : (n : ℕ) < (N : ℕ)) (θ : PhysicalCutoff) (h : ℝ) (hh : 0 < h) (b : Bool)
    (V : EuclideanSpace ℝ (Fin (n : ℕ)) → ℝ)
    (Q : ScalarFormData (activeTiltedGapLaw p N n hn θ h b))
    (hV : IsEuclideanGibbsPotential volume (activeTiltedGapLaw p N n hn θ h b)
      (properMarginalDomain n N) V)
    (hQ : IsNeumannRealization (properMarginalDomain n N) Q)
    (i j : Fin (n : ℕ)) (f g : GapObservable) :
    let ν := activeTiltedGapLaw p N n hn θ h b
    ∃ χ η : Lp ℝ 2 ν,
      χ =ᵐ[ν] (fun x => f.val.2 (x i)) ∧ η =ᵐ[ν] (fun x => g.val.2 (x j)) ∧
      eLpNorm χ ∞ ν < ⊤ ∧ eLpNorm η ∞ ν < ⊤ ∧
      MemLp (fun x => f.val.1 (x i)) 2 ν ∧ MemLp (fun x => g.val.1 (x j)) 2 ν ∧
      ∃ u : Fin (n : ℕ) → Q.1,
        WeightedWeakSolution Q (hessianMatrix V) ⊤ (fun k => if k=i then χ else 0) u ∧
        ProbabilityTheory.covariance (fun x => f.val.1 (x i)) (fun x => g.val.1 (x j)) ν =
          inner ℝ η (u j).val := by
  obtain ⟨m,he⟩ : ∃ m : ℕ, ((n : ℕ)+m).succPNat = N := by
    refine ⟨(N : ℕ)-(n : ℕ)-1,?_⟩
    apply PNat.coe_injective
    change (n : ℕ)+((N : ℕ)-(n : ℕ)-1)+1 = (N : ℕ)
    omega
  subst N
  exact internal_proper_coordinate_covariance p hs n m hn θ h hh b V Q hV hQ i j f g

/-- The actual proper tilted marginal has the coordinate covariance
representation used in Theorem 2, with its physical
potential, its whole Neumann form, and the point source. All analytic
properties and all L² membership statements are conclusions. -/
theorem proper_coordinate_covariance
    (p : Parameters) (hs : 1 < p.val.2) (N n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ))
    (hlt : (n : ℕ) < (N : ℕ)) (θ : PhysicalCutoff) (h : ℝ) (hh : 0 < h) (b : Bool) :
    let ν := activeTiltedGapLaw p N n hn θ h b
    IsProbabilityMeasure ν ∧
    ∃ (V : EuclideanSpace ℝ (Fin (n : ℕ)) → ℝ) (Q : ScalarFormData ν),
      IsEuclideanGibbsPotential volume ν (properMarginalDomain n N) V ∧
      IsNeumannRealization (properMarginalDomain n N) Q ∧
      IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
      ∀ (i j : Fin (n : ℕ)) (f g : GapObservable),
        ∃ χ η : Lp ℝ 2 ν,
          χ =ᵐ[ν] (fun x => f.val.2 (x i)) ∧ η =ᵐ[ν] (fun x => g.val.2 (x j)) ∧
          eLpNorm χ ∞ ν < ⊤ ∧ eLpNorm η ∞ ν < ⊤ ∧
          MemLp (fun x => f.val.1 (x i)) 2 ν ∧ MemLp (fun x => g.val.1 (x j)) 2 ν ∧
          ∃ u : Fin (n : ℕ) → Q.1,
            WeightedWeakSolution Q (hessianMatrix V) ⊤ (fun k => if k=i then χ else 0) u ∧
            ProbabilityTheory.covariance (fun x => f.val.1 (x i)) (fun x => g.val.1 (x j)) ν =
              inner ℝ η (u j).val := by
  obtain ⟨m,he⟩ : ∃ m : ℕ, ((n : ℕ)+m).succPNat = N := by
    refine ⟨(N : ℕ)-(n : ℕ)-1,?_⟩
    apply PNat.coe_injective
    change (n : ℕ)+((N : ℕ)-(n : ℕ)-1)+1 = (N : ℕ)
    omega
  subst N
  obtain ⟨_,_,hprob,V,Q,hV,hQ,hclosed,hcons,_⟩ :=
    PhysicalDecay.proper_physical_wellposed p hs n m hn θ h hh b
  exact ⟨hprob,V,Q,hV,hQ,hclosed,hcons,
    internal_proper_coordinate_covariance p hs n m hn θ h hh b V Q hV hQ⟩

set_option backward.isDefEq.respectTransparency false in
/-- The proper-marginal covariance estimate used in Theorem 2. The loss and stretched-exponential exponents retain
the temperature-independent quantifier order of Proposition 4.10.
Both finite-volume errors are present. The norms are the actual derivative
norms under the tilted marginal, and observable L² membership is
concluded before evaluating the covariance. -/
theorem proper_covariance_decay :
    ∀ s : ShortExponent, ∃ q : ℝ, 0 < q ∧
      ∀ h : ℝ, 0 < h → ∃ δ : ℝ, 0 < δ ∧
      ∀ θ : PhysicalCutoff, ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
      ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
      ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      let p := ofShort β s
      ∀ (N n : ℕ+), 4 ≤ (N : ℕ) → 2 ≤ (n : ℕ) →
        2*(n : ℕ) ≤ (N : ℕ) → ∀ (hn : (n : ℕ) ≤ (N : ℕ)) (b : Bool),
        let ν := activeTiltedGapLaw p N n hn θ h b
        ∀ i : Fin (n : ℕ), (n : ℕ) ≤ 4*(i.val+1) →
          4*(i.val+1) ≤ 3*(n : ℕ) → ∀ (j : Fin (n : ℕ)) (f g : GapObservable),
          MemLp (fun x => f.val.1 (x i)) 2 ν ∧ MemLp (fun x => g.val.1 (x j)) 2 ν ∧
          MemLp (fun x => f.val.2 (x i)) 2 ν ∧ MemLp (fun x => g.val.2 (x j)) 2 ν ∧
          ENNReal.ofReal |ProbabilityTheory.covariance
            (fun x => f.val.1 (x i)) (fun x => g.val.1 (x j)) ν| ≤
            ENNReal.ofReal (A*(n : ℝ)^(q*h)*
              ((1+|(j.val : ℝ)-(i.val : ℝ)|)^(-s.val)+
                (n : ℝ)^(-(s.val-1/2))+(N : ℝ)^(-(1/2 : ℝ)))) *
              (eLpNorm (fun x => f.val.2 (x i)) 2 ν+
                ENNReal.ofReal (Real.exp (-c*(n : ℝ)^δ))*
                  eLpNorm (fun x => f.val.2 (x i)) ∞ ν) *
              eLpNorm (fun x => g.val.2 (x j)) 2 ν := by
  intro s
  obtain ⟨q,hq,hdec⟩ := PhysicalDecay.proper_physical_decay_compact s
  refine ⟨q,hq,fun h hh => ?_⟩
  obtain ⟨δ,hδ,hdec⟩ := hdec h hh
  refine ⟨δ,hδ,fun θ βlo βhi hlo hle => ?_⟩
  obtain ⟨A,c,hA,hc,hdec⟩ := hdec θ βlo βhi hlo hle
  refine ⟨A,c,hA,hc,fun β hβ => ?_⟩
  intro p N n hN hn2 hhalf hn b ν i hil hir j f g
  obtain ⟨_,_,_,V,Q,hV,hQ,_,_,hdec⟩ := hdec β hβ N n hN hn2 hhalf hn b
  obtain ⟨χ,η,hχ,hη,hχb,_,hF,hG,u,hu,hcov⟩ :=
    internal_proper_coordinate_covariance_of_lt p s.property N n hn
      (by have := n.pos; omega) θ h hh b V Q hV hQ i j f g
  refine ⟨hF,hG,(Lp.memLp χ).ae_eq hχ,(Lp.memLp η).ae_eq hη,?_⟩
  have hbound := (hdec i hil hir χ hχb).2 u hu j
  have hnormχ : ENNReal.ofReal ‖χ‖ = eLpNorm (fun x => f.val.2 (x i)) 2 ν := by
    rw [ofReal_norm,Lp.enorm_def,eLpNorm_congr_ae hχ]
  have hnormη : ENNReal.ofReal ‖η‖ = eLpNorm (fun x => g.val.2 (x j)) 2 ν := by
    rw [ofReal_norm,Lp.enorm_def,eLpNorm_congr_ae hη]
  rw [hnormχ,eLpNorm_congr_ae hχ] at hbound
  rw [hcov]
  calc
    ENNReal.ofReal |inner ℝ η (u j).val| ≤ ENNReal.ofReal (‖η‖*‖(u j).val‖) :=
      ENNReal.ofReal_le_ofReal (abs_real_inner_le_norm _ _)
    _ = ENNReal.ofReal ‖(u j).val‖ * eLpNorm (fun x => g.val.2 (x j)) 2 ν := by
      rw [ENNReal.ofReal_mul (norm_nonneg _),hnormη,mul_comm]
    _ ≤ _ := mul_le_mul' hbound le_rfl

end Riesz2.DecayShort.ShortRangeResultPart2
