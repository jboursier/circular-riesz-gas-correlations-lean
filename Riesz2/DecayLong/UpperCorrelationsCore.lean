/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.ProperMarginalDecay
public import Riesz2.DecayLong.FullCycleComparisonPart2
public import Riesz2.DecayLong.ObservableTransfer
public import Riesz2.DecayShort.ShortRangeResultPart5

/-!
# Upper long-range gap covariances

See the proof of Theorem 1 in the paper, including second moments.
The physical response estimates are paired with the literal observable derivatives.
The exceptional-set power is retained before temperature is chosen. A proper cyclic
window and full-cycle comparison are available for the threshold assembly.
Both branches preserve the derivative factors under the unforced physical law.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal BigOperators Topology

namespace Riesz2.DecayLong.UpperCorrelations

open Riesz2.DecayShort GibbsPotentialComparison PhysicalCore
open Riesz2.DecayShort.ShortRangeResultPart5

set_option backward.isDefEq.respectTransparency false

/-- Physical curvature and collision bounds for the actual proper marginal,
supporting the proof of Theorem 1. -/
theorem internal_proper_analytic (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (hn : (n : ℕ) ≤ (((n : ℕ)+m).succPNat : ℕ))
    (θ : PhysicalCutoff) (h : ℝ) (_hh : 0 < h)
    (V : EuclideanSpace ℝ (Fin (n : ℕ)) → ℝ)
    (hV : IsEuclideanGibbsPotential volume
      (activeTiltedGapLaw (ofLong β s) ((n : ℕ)+m).succPNat n hn θ h false)
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
    β.val * ∑ i, (θ.val (((n : ℝ)^h)⁻¹*x i) +
      if false then θ.val (((n : ℝ)^h)⁻¹*(x i)⁻¹) else 0) -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (x,z)).toReal)
  have hG := PhysicalFormDomain.proper_gibbs_potential β s n m θ h
  have hepow : (n : ℝ)^(-h) = ((n : ℝ)^h)⁻¹ := Real.rpow_neg (by positivity) h
  have hdomain : properMarginalDomain n ((n : ℕ)+m).succPNat =
      AffineSimplex.chartDomain n ((n+m : ℕ)+1) := by
    rw [← ProperMarginalChart.baseDomain_eq_properMarginalDomain n m]
  have hP : IsEuclideanGibbsPotential volume
      (activeTiltedGapLaw (ofLong β s) ((n : ℕ)+m).succPNat n hn θ h false) U P := by
    simpa only [P, U, hdomain, hepow, ofLong, Bool.false_eq_true, ↓reduceIte, add_zero] using hG
  obtain ⟨c,hc⟩ := potential_eqOn_add_const hU hV hP
  have he : EqOn V (fun x => P x+c) U := hc
  have ha : 0 < ((n : ℝ)^h)⁻¹ := inv_pos.mpr (Real.rpow_pos_of_pos (by positivity) _)
  obtain ⟨_,_,_,⟨κ,hκ,hH⟩,_,⟨C,hC,hbar⟩⟩ :=
    MarginalCollision.proper_marginal_collision_criterion (ofLong β s) n m n.pos
      (Equiv.refl _) θ ha Finset.univ false
  change (∀ x ∈ U, ∀ e, κ*‖e‖^2 ≤ fderiv ℝ (fderiv ℝ P) x e e) at hH
  change (∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹^2-C ≤
    (1/4 : ℝ)*‖gradient P x‖^2-(1/2 : ℝ)*Laplacian.laplacian P x) at hbar
  refine ⟨⟨κ,hκ,fun x hx e => ?_⟩,⟨C,hC,fun x hx => ?_⟩⟩
  · rw [(derivatives_eq_of_eqOn_add_const hU he x hx).2.1]
    exact hH x hx e
  · obtain ⟨_,_,hg,hΔ⟩ := derivatives_eq_of_eqOn_add_const hU he x hx
    rw [hg,hΔ]
    convert hbar x hx using 1; ring

/-- Internal covariance representation for the actual proper tilted marginal
in the proof of Theorem 1. It uses any physical Gibbs and Neumann
witnesses, hence the exact witnesses supplied by physical decay. Observable
and derivative L² membership are conclusions. -/
theorem internal_proper_coordinate_covariance (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (hn : (n : ℕ) ≤ (((n : ℕ)+m).succPNat : ℕ))
    (θ : PhysicalCutoff) (h : ℝ) (hh : 0 < h)
    (V : EuclideanSpace ℝ (Fin (n : ℕ)) → ℝ)
    (Q : ScalarFormData (activeTiltedGapLaw (ofLong β s) ((n : ℕ)+m).succPNat n hn θ h false))
    (hV : IsEuclideanGibbsPotential volume
      (activeTiltedGapLaw (ofLong β s) ((n : ℕ)+m).succPNat n hn θ h false)
      (properMarginalDomain n ((n : ℕ)+m).succPNat) V)
    (hQ : IsNeumannRealization (properMarginalDomain n ((n : ℕ)+m).succPNat) Q)
    (i j : Fin (n : ℕ)) (f g : GapObservable) :
    let ν := activeTiltedGapLaw (ofLong β s) ((n : ℕ)+m).succPNat n hn θ h false
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
  obtain ⟨⟨κ,hκ,hH⟩,⟨C,hC,hbar⟩⟩ := internal_proper_analytic β s n m hn θ h hh V hV
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


/-- Size-interface bridge for the proper covariance representation in
the proof of Theorem 1. -/
theorem internal_proper_coordinate_covariance_of_lt
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (N n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ))
    (hlt : (n : ℕ) < (N : ℕ)) (θ : PhysicalCutoff) (h : ℝ) (hh : 0 < h)
    (V : EuclideanSpace ℝ (Fin (n : ℕ)) → ℝ)
    (Q : ScalarFormData (activeTiltedGapLaw (ofLong β s) N n hn θ h false))
    (hV : IsEuclideanGibbsPotential volume (activeTiltedGapLaw (ofLong β s) N n hn θ h false)
      (properMarginalDomain n N) V)
    (hQ : IsNeumannRealization (properMarginalDomain n N) Q)
    (i j : Fin (n : ℕ)) (f g : GapObservable) :
    let ν := activeTiltedGapLaw (ofLong β s) N n hn θ h false
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
  exact internal_proper_coordinate_covariance β s n m hn θ h hh V Q hV hQ i j f g

/-- The proper-window step in Theorem 1 of the paper.
Proper tilted covariance decay supporting the proof of Theorem 1, with an explicit temperature-independent
exceptional power. All observable and derivative second moments are concluded. -/
theorem proper_covariance_decay (hzeta : External.PeriodicZeta)
    (hRig : External.LongRangeRigidityLocallyUniform) (s : Riesz1.RieszExponent) :
    ∃ hstar q : ℝ, 0 < hstar ∧ 0 < q ∧
      ∀ h : ℝ, 0 < h → h ≤ hstar →
      ∀ θ : PhysicalCutoff, ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
      ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
      ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      let p := ofLong β s
      ∀ (N n : ℕ+), 16 ≤ (n : ℕ) →
        2*(n : ℕ) ≤ (N : ℕ) → ∀ (hn : (n : ℕ) ≤ (N : ℕ)),
        let ν := activeTiltedGapLaw p N n hn θ h false
        ∀ i : Fin (n : ℕ), (n : ℕ) ≤ 4*(i.val+1) →
          4*(i.val+1) ≤ 3*(n : ℕ) → ∀ (j : Fin (n : ℕ)) (f g : GapObservable),
          MemLp (fun x => f.val.1 (x i)) 2 ν ∧ MemLp (fun x => g.val.1 (x j)) 2 ν ∧
          MemLp (fun x => f.val.2 (x i)) 2 ν ∧ MemLp (fun x => g.val.2 (x j)) 2 ν ∧
          ENNReal.ofReal |covariance (fun x => f.val.1 (x i)) (fun x => g.val.1 (x j)) ν| ≤
            ENNReal.ofReal (A*(n : ℝ)^(q*h)*
              ((1+|(j.val : ℝ)-(i.val : ℝ)|)^(-(2-s.val))+(n : ℝ)^(-(1/2 : ℝ)))) *
              (eLpNorm (fun x => f.val.2 (x i)) 2 ν+
                ENNReal.ofReal (Real.exp (-c*(n : ℝ)^GoodBlocks.coefficientTailPower s.val h))*
                  eLpNorm (fun x => f.val.2 (x i)) ∞ ν) *
              eLpNorm (fun x => g.val.2 (x j)) 2 ν := by
  obtain ⟨ε₀,q,hε₀,hq,hdec⟩ := ProperMarginalDecay.admissible_decay_internal hzeta hRig s
  refine ⟨min ε₀ (paperCutoffThreshold s),q,lt_min hε₀ (paperCutoffThreshold_pos s),hq,fun h hh hsmall θ βlo βhi hlo hle => ?_⟩
  obtain ⟨A,c,hA,hc,hdec⟩ := hdec θ h hh (hsmall.trans (min_le_left _ _)) βlo βhi hlo hle
  refine ⟨A,c,hA,hc,fun β hβ => ?_⟩
  intro p N n hn16 hhalf hn ν i hil hir j f g
  obtain ⟨m,he⟩ : ∃ m : ℕ, ((n : ℕ)+m).succPNat = N := by
    refine ⟨(N : ℕ)-(n : ℕ)-1,?_⟩
    apply PNat.coe_injective
    change (n : ℕ)+((N : ℕ)-(n : ℕ)-1)+1 = (N : ℕ)
    have := n.pos
    omega
  subst N
  obtain ⟨hK,hKn⟩ := ProperMarginalDecay.cutoff_admissible_internal n h
    (paperReferenceCutoffExponent s) hn16 hh
    (paperCutoffThreshold_mul_degree_le_half s hh.le (hsmall.trans (min_le_right _ _)))
  have hnN : 2*(n : ℕ) ≤ (n : ℕ)+m+1 := by simpa only [Nat.succPNat_coe] using hhalf
  have hKM : 4*⌊(n : ℝ)^h⌋₊^(paperReferenceCutoffExponent s : ℕ) ≤ (properReferencePeriod s n ((n : ℕ)+m).succPNat : ℕ) :=
    hKn.trans (by have := (PhysicalCore.properReferencePeriod_bounds s n ((n : ℕ)+m).succPNat hnN).1; omega)
  obtain ⟨Q,hreal,hclosed,hcons,_,hbound⟩ := hdec β hβ n m (by omega) hnN hK hKM
  obtain ⟨_,_,_,V,Q,hV,hQ,_,_,hdec'⟩ := ProperMarginalDecay.complete_chart_internal
    β s n m θ h q A c (GoodBlocks.coefficientTailPower s.val h) hh.le hA
      Q hreal hclosed hcons hbound
  obtain ⟨χ,η,hχ,hη,hχb,_,hF,hG,u,hu,hcov⟩ :=
    internal_proper_coordinate_covariance β s n m hn θ h hh V Q hV hQ i j f g
  refine ⟨hF,hG,(Lp.memLp χ).ae_eq hχ,(Lp.memLp η).ae_eq hη,?_⟩
  have hb := (hdec' i hil hir χ (Or.inr hχb)).2 u hu j
  have hnormχ : ENNReal.ofReal ‖χ‖ = eLpNorm (fun x => f.val.2 (x i)) 2 ν := by
    rw [ofReal_norm,Lp.enorm_def,eLpNorm_congr_ae hχ]
  have hnormη : ENNReal.ofReal ‖η‖ = eLpNorm (fun x => g.val.2 (x j)) 2 ν := by
    rw [ofReal_norm,Lp.enorm_def,eLpNorm_congr_ae hη]
  rw [hnormχ,eLpNorm_congr_ae hχ] at hb
  rw [hcov]
  calc
    ENNReal.ofReal |inner ℝ η (u j).val| ≤ ENNReal.ofReal (‖η‖*‖(u j).val‖) :=
      ENNReal.ofReal_le_ofReal (abs_real_inner_le_norm _ _)
    _ = ENNReal.ofReal ‖(u j).val‖ * eLpNorm (fun x => g.val.2 (x j)) 2 ν := by
      rw [ENNReal.ofReal_mul (norm_nonneg _),hnormη,mul_comm]
    _ ≤ _ := mul_le_mul' hb le_rfl

/-- The full-cycle step in Theorem 1 of the paper,
using the fixed cutoff of Lemma 5.4. Polynomial absorption puts the response error under the
same distance weight as its main term. Internal numerical step supporting
the proof of Theorem 1. -/
theorem full_error_profile_internal {p a δ c : ℝ} (hp : 0 ≤ p) (ha : 0 ≤ a)
    (hδ : 0 < δ) (hc : 0 < c) :
    ∃ D : ℝ, 0 < D ∧ ∀ n d : ℝ, 1 ≤ n → 0 ≤ d → d ≤ n →
      Real.exp (-c*n^δ) ≤ D*n^a*(1+d)^(-p)*Real.exp (-(c/2)*n^δ) := by
  obtain ⟨B,hB,hbound⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := p) (c := c) (c' := c/2) hδ (by linarith)
  refine ⟨2^p*(B+1),by positivity,fun n d hn hd hdn => ?_⟩
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hr0 : 0 < 1+d := by positivity
  have hw : (1+d)^p ≤ 2^p*n^p := by
    calc
      _ ≤ (2*n)^p := Real.rpow_le_rpow (by positivity) (by linarith) hp
      _ = _ := Real.mul_rpow (by norm_num) hn0.le
  have he := mul_le_mul_of_nonneg_right hw (Real.exp_nonneg (-c*n^δ))
  have he' := mul_le_mul_of_nonneg_left (hbound n hn) (show 0 ≤ (2 : ℝ)^p by positivity)
  have hcanc : (1+d)^(-p)*(1+d)^p = 1 := by rw [← Real.rpow_add hr0]; simp
  rw [← mul_assoc] at he'
  have ht := mul_le_mul_of_nonneg_left (he.trans he') (Real.rpow_nonneg hr0.le (-p))
  have hbase : Real.exp (-c*n^δ) ≤
      (2^p*B)*(1+d)^(-p)*Real.exp (-(c/2)*n^δ) := by
    simpa only [← mul_assoc,hcanc,one_mul,mul_comm,mul_left_comm] using ht
  have hfactor : 2^p*B ≤ 2^p*(B+1)*n^a := by
    apply (mul_le_mul_of_nonneg_left (show B ≤ B+1 by linarith) (by positivity)).trans
    exact le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hn ha)
  exact hbase.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hfactor (by positivity)) (Real.exp_nonneg _))

/-- The full-cycle step of Theorem 1 of the paper,
using the degree and forcing threshold prescribed by Lemma 5.4.
The full-cycle covariance estimate supports the proof of Theorem 1. The admissible forcing threshold and
loss exponent precede temperature, and the exceptional power is explicit. -/
theorem full_covariance_decay (hzeta : External.PeriodicZeta)
    (hRig : External.LongRangeRigidityLocallyUniform) (s : Riesz1.RieszExponent) :
    ∃ hstar q : ℝ, 0 < hstar ∧ 0 < q ∧
      ∀ h : ℝ, 0 < h → h < hstar →
      ∀ θ : PhysicalCutoff, ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
      ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
      ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      let p := ofLong β s
      ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (i j : Fin (N : ℕ)) (f g : GapObservable),
        let ν := fullIntrinsicTiltedGapLaw p N θ h false
        ENNReal.ofReal |covariance
          (fun X : Riesz1.Configuration N => f.val.1 (gap X i.val))
          (fun X => g.val.1 (gap X j.val))
          (tiltedParticleMeasure p N N le_rfl θ h false)| ≤
          ENNReal.ofReal (A*(N : ℝ)^(q*h)*
            (1+(Riesz1.cyclicIndexDistance N i j : ℝ))^(-(2-s.val))) *
            (eLpNorm (fun z => f.val.2 (1+z.val i)) 2 ν+
              ENNReal.ofReal (Real.exp (-c*(N : ℝ)^GoodBlocks.coefficientTailPower s.val h))*
                ENNReal.ofReal (derivativeSup f)) *
            eLpNorm (fun z => g.val.2 (1+z.val j)) 2 ν := by
  obtain ⟨hstar,q,hhstar,hq,hdec⟩ :=
    FullCycleComparison.decay_gap_correlations_full_cycle hzeta hRig s
      (paperReferenceCutoffExponent s)
  refine ⟨min hstar (paperCutoffThreshold s),q,
    lt_min hhstar (paperCutoffThreshold_pos s),hq,fun h hh hsmall θ βlo βhi hlo hle => ?_⟩
  obtain ⟨A,c,hA,hc,hdec⟩ :=
    (hdec h hh (hsmall.trans_le (min_le_left _ _))).2 θ βlo βhi hlo hle
  have hp : 0 ≤ 2-s.val := by linarith [s.property.2]
  have hδ := GoodBlocks.coefficientTailPower_pos s.property.1 s.property.2 hh
  obtain ⟨D,hD,herror⟩ := full_error_profile_internal hp (mul_nonneg hq.le hh.le) hδ hc
  refine ⟨A*(D+1),c/2,by positivity,by positivity,fun β hβ => ?_⟩
  intro p N hN i j f g ν
  obtain ⟨_,_,_,W,Q,hW,hval,hV,hQ,_,_,hdec⟩ := hdec β hβ N hN
  obtain ⟨χ,η,hχ,hη,hχb,_,_,_,u,hu,hcov⟩ :=
    ShortRangeResultPart3.internal_full_coordinate_covariance p hN θ h false
      W hW hval Q hV hQ i j f g
  have hχt : eLpNorm χ ∞ ν < ⊤ := hχb.trans_lt ENNReal.ofReal_lt_top
  have hb := (hdec i χ hχt).2 u hu j
  have hnormχ : ENNReal.ofReal ‖χ‖ = eLpNorm (fun z => f.val.2 (1+z.val i)) 2 ν := by
    rw [ofReal_norm,Lp.enorm_def,eLpNorm_congr_ae hχ]
  have hnormη : ENNReal.ofReal ‖η‖ = eLpNorm (fun z => g.val.2 (1+z.val j)) 2 ν := by
    rw [ofReal_norm,Lp.enorm_def,eLpNorm_congr_ae hη]
  have hdist := Riesz1.cyclicIndexDistance_comm' N j i
  rw [hdist] at hb
  have hsup : (eLpNorm χ ∞ ν).toReal ≤ derivativeSup f := by
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hχb
    rw [ENNReal.toReal_ofReal (show 0 ≤ derivativeSup f from ENNReal.toReal_nonneg)] at ht
    exact ht
  have hdN : (Riesz1.cyclicIndexDistance N i j : ℝ) ≤ (N : ℝ) := by
    have he := Riesz1.APG.cyclicIndexDistance_le_half i j
    exact_mod_cast (show Riesz1.cyclicIndexDistance N i j ≤ (N : ℕ) by omega)
  have he := herror (N : ℝ) (Riesz1.cyclicIndexDistance N i j : ℝ)
    (by exact_mod_cast N.pos) (by positivity) hdN
  let T := (N : ℝ)^(q*h)*(1+(Riesz1.cyclicIndexDistance N i j : ℝ))^(-(2-s.val))
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hsrc : Real.exp (-c*(N : ℝ)^GoodBlocks.coefficientTailPower s.val h)*
      (eLpNorm χ ∞ ν).toReal ≤
      D*T*Real.exp (-(c/2)*(N : ℝ)^GoodBlocks.coefficientTailPower s.val h)*derivativeSup f :=
    by simpa only [T, mul_assoc] using
      mul_le_mul he hsup ENNReal.toReal_nonneg (by positivity)
  have hfnonneg : 0 ≤ derivativeSup f := ENNReal.toReal_nonneg
  have hn : ‖(u j).val‖ ≤ A*(D+1)*T*
      (‖χ‖+Real.exp (-(c/2)*(N : ℝ)^GoodBlocks.coefficientTailPower s.val h)*derivativeSup f) := by
    have hmain : A*T*‖χ‖ ≤ A*(D+1)*T*‖χ‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg χ)
      exact mul_le_mul_of_nonneg_right (by nlinarith only [mul_pos hA hD]) hT
    have herr := mul_le_mul_of_nonneg_left hsrc hA.le
    have hbT : ‖(u j).val‖ ≤ A*T*‖χ‖+
        A*(Real.exp (-c*(N : ℝ)^GoodBlocks.coefficientTailPower s.val h)*
          (eLpNorm χ ∞ ν).toReal) := by simpa only [T, mul_assoc] using hb
    have hrest : 0 ≤ A*T*(Real.exp (-(c/2)*(N : ℝ)^GoodBlocks.coefficientTailPower s.val h)*derivativeSup f) := by positivity
    nlinarith only [hbT,hmain,herr,hrest]
  have hb' := ENNReal.ofReal_le_ofReal hn
  dsimp only [T] at hb'
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (norm_nonneg _) (by positivity),
    ENNReal.ofReal_mul (Real.exp_nonneg _), hnormχ] at hb'
  rw [← ShortRangeResultPart3.full_covariance_pullback p θ h false i j f g,hcov]
  calc
    ENNReal.ofReal |inner ℝ η (u j).val| ≤ ENNReal.ofReal (‖η‖*‖(u j).val‖) :=
      ENNReal.ofReal_le_ofReal (abs_real_inner_le_norm _ _)
    _ = ENNReal.ofReal ‖(u j).val‖ * eLpNorm (fun z => g.val.2 (1+z.val j)) 2 ν := by
      rw [ENNReal.ofReal_mul (norm_nonneg _),hnormη,mul_comm]
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul' hb' le_rfl

/-- Compact-temperature moments for Lemma 2.1 of the paper.
Uniform bound on the positive and inverse moments `E gap^r + E gap^(-r)`, for every
configuration size at least two and every parameter with the fixed exponent and temperature. -/
theorem gap_moment_bound_locallyUniform {s βlo βhi : ℝ} (hs : 0 < s) (hs1 : s ≠ 1)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (r : ℝ)
    (hr : 0 < r) :
    ∃ D : ℝ, 0 < D ∧ ∀ (p : Parameters), p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (j : ℤ),
        Integrable (fun X : Riesz1.Configuration N => gap X j ^ r) (gibbsMeasure p N) ∧
        Integrable (fun X : Riesz1.Configuration N => gap X j ^ (-r)) (gibbsMeasure p N) ∧
        (∫ X, gap X j ^ r ∂gibbsMeasure p N) + (∫ X, gap X j ^ (-r) ∂gibbsMeasure p N) ≤ D := by
  obtain ⟨D, hD, hmom⟩ := SingleGapTails.single_gap_moment_integrals s βlo βhi hs hs1 hlo hle r hr
  refine ⟨D, hD, fun p hps hpl hph N hN j => ?_⟩
  obtain ⟨hi1, hi2, hle⟩ := hmom p hps hpl hph N hN j
  refine ⟨hi1, hi2, ?_⟩
  have hm1 : Measurable (fun X : Riesz1.Configuration N => gap X j ^ r) :=
    (Riesz1.measurable_gap j).pow_const r
  have hm2 : Measurable (fun X : Riesz1.Configuration N => gap X j ^ (-r)) :=
    (Riesz1.measurable_gap j).pow_const (-r)
  have hnn1 : 0 ≤ᵐ[gibbsMeasure p N] fun X => gap X j ^ r :=
    ae_of_all _ fun X => Real.rpow_nonneg (Riesz1.gap_pos X j).le r
  have hnn2 : 0 ≤ᵐ[gibbsMeasure p N] fun X => gap X j ^ (-r) :=
    ae_of_all _ fun X => Real.rpow_nonneg (Riesz1.gap_pos X j).le (-r)
  rw [integral_eq_lintegral_of_nonneg_ae hnn1 hm1.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae hnn2 hm2.aestronglyMeasurable,
    ← ENNReal.toReal_add (ENNReal.add_ne_top.mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle)).1
      (ENNReal.add_ne_top.mp (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle)).2]
  exact ENNReal.toReal_le_of_le_ofReal hD.le hle

/-- Tilt removal in the proof of Theorem 1 of the paper,
with constants uniform on the temperature interval. Covariance removal at the explicit forcing power and universal rate,
supporting the proof of Theorem 1. -/
theorem upper_tilt_covariance_locallyUniform (s βlo βhi h : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (hlo : 0 < βlo) (hle : βlo ≤ βhi) (hh : 0 < h) :
    ∃ D : ℝ, 0 < D ∧ ∀ (p : Parameters), p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (θ : PhysicalCutoff)
        (I : Finset (Fin (N : ℕ))), 1 ≤ I.card →
        3*(I.card : ℝ)*Real.exp (-(Real.log 2/8)*(I.card : ℝ)^h) ≤ 1/2 →
        ∀ (f g : GapObservable) (i j : ℤ),
          |covariance (fun X => f.val.1 (gap X i)) (fun X => g.val.1 (gap X j))
              (gibbsMeasure p N) -
            covariance (fun X => f.val.1 (gap X i)) (fun X => g.val.1 (gap X j))
              (activeTilt p N θ ((I.card : ℝ)^h) false I)| ≤
            D*Real.exp (-(Real.log 2/32)*(I.card : ℝ)^h)*derivativeSup f*derivativeSup g := by
  obtain ⟨D2,hD2,hm2⟩ := gap_moment_bound_locallyUniform (s := s) (βlo := βlo) (βhi := βhi) (by linarith)
    (ne_of_lt hs1) hlo hle 2 (by norm_num)
  obtain ⟨D4,hD4,hm4⟩ := gap_moment_bound_locallyUniform (s := s) (βlo := βlo) (βhi := βhi) (by linarith)
    (ne_of_lt hs1) hlo hle 4 (by norm_num)
  have ha : 0 < Real.log 2/8 := div_pos (Real.log_pos one_lt_two) (by norm_num)
  obtain ⟨B,hB,hpoly⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := 1) (c := Real.log 2/16) (c' := Real.log 2/32) hh (by linarith)
  let M := Real.sqrt (8*D4+8)+6*(2*D2+2)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨4*Real.sqrt 3*B*M+1,by positivity,fun p hps hpl hph N hN θ I hI hsmall f g i j => ?_⟩
  have := gibbsMeasure_probability p N
  have hn1 : (1 : ℝ) ≤ I.card := by exact_mod_cast hI
  have hn0 : 0 < (I.card : ℝ) := lt_of_lt_of_le zero_lt_one hn1
  have hR : 1 ≤ (I.card : ℝ)^h := Real.one_le_rpow hn1 hh.le
  let q := 3*(I.card : ℝ)*Real.exp (-(Real.log 2/8)*(I.card : ℝ)^h)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q ≤ 1 := by dsimp [q]; linarith
  have hmass := upper_penalty_mass p N hN θ ((I.card : ℝ)^h)
    (Real.rpow_pos_of_pos hn0 h) I
  have hnorm := NonnegativeTilt.one_sub_expTiltNormalizer_le (μ := gibbsMeasure p N)
    (activeGapPenalty_measurable θ (Real.rpow_nonneg hn0.le h) false I)
    p.property.1.le (activeGapPenalty_nonneg θ (Real.rpow_nonneg hn0.le h) false I)
  have hz : 1/2 ≤ NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (activeGapPenalty θ ((I.card : ℝ)^h) false I) := by linarith
  let K := (NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (activeGapPenalty θ ((I.card : ℝ)^h) false I))⁻¹*(Real.sqrt q+q)
  have hz0 : 0 < NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (activeGapPenalty θ ((I.card : ℝ)^h) false I) := lt_of_lt_of_le (by norm_num) hz
  have hzinv : (NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (activeGapPenalty θ ((I.card : ℝ)^h) false I))⁻¹ ≤ 2 := by
    simpa using inv_anti₀ (by norm_num : (0 : ℝ)<1/2) hz
  have hsq1 : Real.sqrt q ≤ 1 := (Real.sqrt_le_sqrt hq1).trans_eq (by norm_num)
  have hqsq : q ≤ Real.sqrt q := by
    nlinarith only [Real.mul_self_sqrt hq0, Real.sqrt_nonneg q,hsq1]
  have hK0 : 0 ≤ K := mul_nonneg (inv_nonneg.mpr hz0.le) (by positivity)
  have hKsq : K ≤ 4*Real.sqrt q := by
    dsimp [K]
    calc
      _ ≤ 2*(Real.sqrt q+q) := mul_le_mul_of_nonneg_right hzinv (by positivity)
      _ ≤ _ := by linarith only [hqsq]
  have hK4 : K ≤ 4 := by linarith only [hKsq,hsq1]
  have hD (r D : ℝ)
      (hm : ∀ k : ℤ, Integrable (fun X : Riesz1.Configuration N => gap X k^r)
        (gibbsMeasure p N) ∧
        Integrable (fun X : Riesz1.Configuration N => gap X k^(-r)) (gibbsMeasure p N) ∧
        (∫ X, gap X k^r ∂gibbsMeasure p N)+(∫ X, gap X k^(-r) ∂gibbsMeasure p N) ≤ D)
      (k : ℤ) : ∫ X, gap X k^r ∂gibbsMeasure p N ≤ D := by
    have ht := (hm k).2.2
    have hnn : 0 ≤ ∫ X, gap X k^(-r) ∂gibbsMeasure p N := integral_nonneg
      (fun X => Real.rpow_nonneg (Riesz1.gap_pos X k).le (-r))
    linarith only [ht,hnn]
  have hb := covariance_activeTilt_pair_le p θ hR false I (by norm_num : (0 : ℝ)<1/2)
    hz hmass (rfl : K = _) f g i j
    (hm2 p hps hpl hph N hN i).1 (hm2 p hps hpl hph N hN j).1
    (hm4 p hps hpl hph N hN i).1 (hm4 p hps hpl hph N hN j).1
    (hD 2 D2 (hm2 p hps hpl hph N hN) i)
    (hD 2 D2 (hm2 p hps hpl hph N hN) j)
    (hD 4 D4 (hm4 p hps hpl hph N hN) i)
    (hD 4 D4 (hm4 p hps hpl hph N hN) j)
  have hcoeff : Real.sqrt (8*D4+8)+(2+K)*(2*D2+2) ≤ M := by
    dsimp [M]
    nlinarith only [hK4,hD2]
  have hsqrt : Real.sqrt q ≤ Real.sqrt 3*(I.card : ℝ)*
      Real.exp (-(Real.log 2/16)*(I.card : ℝ)^h) := by
    have he : Real.exp (-(Real.log 2/8)*(I.card : ℝ)^h) =
        (Real.exp (-(Real.log 2/16)*(I.card : ℝ)^h))^2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    dsimp [q]
    rw [he,Real.sqrt_mul (by positivity),Real.sqrt_sq (Real.exp_pos _).le,
      Real.sqrt_mul (by norm_num)]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    nlinarith only [Real.sq_sqrt hn0.le,Real.sqrt_nonneg (I.card : ℝ),hn1]
  have hpoly' := hpoly (I.card : ℝ) hn1
  rw [Real.rpow_one] at hpoly'
  have hsqrt' : Real.sqrt q ≤ Real.sqrt 3*B*
      Real.exp (-(Real.log 2/32)*(I.card : ℝ)^h) := by
    calc
      _ ≤ _ := hsqrt
      _ ≤ _ := by nlinarith only [hpoly',Real.sqrt_nonneg (3 : ℝ)]
  have hU : 0 ≤ derivativeSup f := ENNReal.toReal_nonneg
  have hV : 0 ≤ derivativeSup g := ENNReal.toReal_nonneg
  calc
    _ ≤ K*(derivativeSup f*derivativeSup g)*
        (Real.sqrt (8*D4+8)+(2+K)*(2*D2+2)) := hb
    _ ≤ (4*Real.sqrt q)*(derivativeSup f*derivativeSup g)*M := by
      apply mul_le_mul _ hcoeff (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right hKsq (mul_nonneg hU hV)
    _ = Real.sqrt q*(4*M*(derivativeSup f*derivativeSup g)) := by ring
    _ ≤ (Real.sqrt 3*B*Real.exp (-(Real.log 2/32)*(I.card : ℝ)^h))*
        (4*M*(derivativeSup f*derivativeSup g)) :=
      mul_le_mul_of_nonneg_right hsqrt' (by positivity)
    _ = (4*Real.sqrt 3*B*M)*Real.exp (-(Real.log 2/32)*(I.card : ℝ)^h)*
        derivativeSup f*derivativeSup g := by ring
    _ ≤ _ := by
      gcongr
      exact le_add_of_nonneg_right zero_le_one

/-- Proper tilted covariance decay on any cyclic block, supporting
the proof of Theorem 1. -/
theorem proper_cyclic_covariance_decay (hzeta : External.PeriodicZeta)
    (hRig : External.LongRangeRigidityLocallyUniform) (s : Riesz1.RieszExponent) :
    ∃ hstar q : ℝ, 0 < hstar ∧ 0 < q ∧
      ∀ h : ℝ, 0 < h → h ≤ hstar →
      ∀ θ : PhysicalCutoff, ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
      ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
      ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      let p := ofLong β s
      ∀ (N n : ℕ+), 4 ≤ (N : ℕ) → 16 ≤ (n : ℕ) →
        2*(n : ℕ) ≤ (N : ℕ) → ∀ (_hn : (n : ℕ) ≤ (N : ℕ)) (a : ℤ),
        let μ := activeTilt p N θ ((n : ℝ)^h) false (cyclicInterval N a n)
        ∀ i : Fin (n : ℕ), (n : ℕ) ≤ 4*(i.val+1) →
          4*(i.val+1) ≤ 3*(n : ℕ) → ∀ (j : Fin (n : ℕ)) (f g : GapObservable),
          ENNReal.ofReal |covariance (fun X => f.val.1 (gap X (a+i.val)))
            (fun X => g.val.1 (gap X (a+j.val))) μ| ≤
            ENNReal.ofReal (A*(n : ℝ)^(q*h)*
              ((1+|(j.val : ℝ)-(i.val : ℝ)|)^(-(2-s.val))+
                (n : ℝ)^(-(1/2 : ℝ)))) *
              (eLpNorm (fun X => f.val.2 (gap X (a+i.val))) 2 μ+
                ENNReal.ofReal (Real.exp (-c*(n : ℝ)^GoodBlocks.coefficientTailPower s.val h))*
                  eLpNorm (fun X => f.val.2 (gap X (a+i.val))) ∞ μ) *
              eLpNorm (fun X => g.val.2 (gap X (a+j.val))) 2 μ := by
  obtain ⟨hstar,q,hhstar,hq,hdec⟩ := proper_covariance_decay hzeta hRig s
  refine ⟨hstar,q,hhstar,hq,fun h hh hsmall θ βlo βhi hlo hle => ?_⟩
  obtain ⟨A,c,hA,hc,hdec⟩ := hdec h hh hsmall θ βlo βhi hlo hle
  refine ⟨A,c,hA,hc,fun β hβ => ?_⟩
  intro p N n hN hn2 hhalf hn a μ i hil hir j f g
  obtain ⟨_,_,hf,hg,hb⟩ := hdec β hβ N n hn2 hhalf hn i hil hir j f g
  have hN2 : 2 ≤ (N : ℕ) := by omega
  have hnf := ShortRangeResult.internal_eLpNorm_cyclicInterval p hN2 hn θ h false a
    hf.aestronglyMeasurable 2
  have hng := ShortRangeResult.internal_eLpNorm_cyclicInterval p hN2 hn θ h false a
    hg.aestronglyMeasurable 2
  have hnft := ShortRangeResult.internal_eLpNorm_cyclicInterval p hN2 hn θ h false a
    hf.aestronglyMeasurable ∞
  change eLpNorm (fun X => f.val.2 (gap X (a+i.val))) 2 μ = _ at hnf
  change eLpNorm (fun X => g.val.2 (gap X (a+j.val))) 2 μ = _ at hng
  change eLpNorm (fun X => f.val.2 (gap X (a+i.val))) ∞ μ = _ at hnft
  rw [← hnf,← hng,← hnft,← ShortRangeResult.covariance_cyclicInterval p hN2 hn θ h false a f g i j] at hb
  exact hb

/-- The full-cycle tilt-removal step of Theorem 1 of the paper.
Full-system response followed by quantitative tilt removal, supporting
the proof of Theorem 1. -/
theorem full_unforced_decay_locallyUniform (hzeta : External.PeriodicZeta)
    (hRig : External.LongRangeRigidityLocallyUniform) (s : Riesz1.RieszExponent) :
    ∃ hstar q : ℝ, 0 < hstar ∧ 0 < q ∧
      ∀ h : ℝ, 0 < h → h < hstar → ∃ K : ℕ, 2 ≤ K ∧
      ∀ (_θ : PhysicalCutoff) (βlo βhi : ℝ), 0 < βlo → βlo ≤ βhi →
      ∃ A c D : ℝ, 0 < A ∧ 0 < c ∧ 0 < D ∧
      ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi → ∀ (N : ℕ+), K ≤ (N : ℕ) → ∀ (i j : Fin (N : ℕ)) (f g : GapObservable),
        let p := ofLong β s
        let d := Riesz1.cyclicIndexDistance N i j
        |covariance (fun X => f.val.1 (gap X i.val)) (fun X => g.val.1 (gap X j.val))
            (gibbsMeasure p N)| ≤
          A*(N : ℝ)^(q*h)*((1+(d : ℝ))^(-(2-s.val)))*
            (2*(gapDerivativeNorm p N i.val f).toReal+
              Real.exp (-c*(N : ℝ)^GoodBlocks.coefficientTailPower s.val h)*derivativeSup f)*
            (2*(gapDerivativeNorm p N j.val g).toReal)+
          D*Real.exp (-(Real.log 2/32)*(N : ℝ)^h)*derivativeSup f*derivativeSup g := by
  obtain ⟨hstar,q,hhstar,hq,hdec⟩ := full_covariance_decay hzeta hRig s
  refine ⟨hstar,q,hhstar,hq,fun h hh hsmall => ?_⟩
  have hdec := hdec h hh hsmall
  obtain ⟨K,hK,hthreshold⟩ := upper_tilt_threshold h hh
  refine ⟨K,hK,fun θ βlo βhi hlo hle => ?_⟩
  obtain ⟨A,c,hA,hc,hdec⟩ := hdec θ βlo βhi hlo hle
  obtain ⟨D,hD,hremove⟩ := upper_tilt_covariance_locallyUniform s.val βlo βhi h s.property.1 s.property.2 hlo hle hh
  refine ⟨A,c,D,hA,hc,hD,fun β hβ N hNK i j f g => ?_⟩
  intro p d
  have hN : 2 ≤ (N : ℕ) := hK.trans hNK
  have hcfull : (Finset.univ : Finset (Fin (N : ℕ))).card = (N : ℕ) := by simp
  have hfirst : Finset.univ.map (Fin.castLEEmb (le_refl (N : ℕ))) =
      (Finset.univ : Finset (Fin (N : ℕ))) := by ext k; simp
  have he : activeTilt p N θ ((N : ℝ)^h) false Finset.univ =
      tiltedParticleMeasure p N N le_rfl θ h false := by
    rw [← hfirst,activeTilt_firstGapSet]
  obtain ⟨_,hsmall,hz⟩ := hthreshold p N hN θ Finset.univ (by simpa using hNK)
  rw [hcfull] at hsmall hz
  have hf := internal_tilt_derivative p N hN θ ((N : ℝ)^h)
    (Real.rpow_nonneg (by positivity) h) Finset.univ hz i f
  have hg := internal_tilt_derivative p N hN θ ((N : ℝ)^h)
    (Real.rpow_nonneg (by positivity) h) Finset.univ hz j g
  have hb := hdec β hβ N hN i j f g
  dsimp only at hb
  rw [full_derivative_norm p N hN θ h false i f,
    full_derivative_norm p N hN θ h false j g,← he] at hb
  have hm := ShortRangeResult.internal_gapSecondMoments p N i j f g
  have hreal := internal_real_bound (by positivity) (Real.exp_nonneg _)
    (show 0 ≤ derivativeSup f from ENNReal.toReal_nonneg)
    hm.2.2.1.eLpNorm_ne_top hm.2.2.2.eLpNorm_ne_top hf.1 hg.1 le_rfl hb
  have hr := hremove p rfl hβ.1 hβ.2 N hN θ Finset.univ (by rw [hcfull]; omega)
    (by simpa only [hcfull] using hsmall) f g i.val j.val
  rw [hcfull] at hr
  exact internal_remove_real hreal hr

/-- The proper-window tilt-removal step of Theorem 1 of the paper.
Proper-window response followed by quantitative tilt removal, supporting
the proof of Theorem 1. -/
theorem proper_unforced_decay_locallyUniform (hzeta : External.PeriodicZeta)
    (hRig : External.LongRangeRigidityLocallyUniform) (s : Riesz1.RieszExponent) :
    ∃ hstar q : ℝ, 0 < hstar ∧ 0 < q ∧
      ∀ h : ℝ, 0 < h → h ≤ hstar → ∃ K : ℕ, 16 ≤ K ∧
      ∀ (_θ : PhysicalCutoff) (βlo βhi : ℝ), 0 < βlo → βlo ≤ βhi →
      ∃ A c D : ℝ, 0 < A ∧ 0 < c ∧ 0 < D ∧
      ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi → ∀ (N n : ℕ+), 4 ≤ (N : ℕ) → K ≤ (n : ℕ) → 2*(n : ℕ) ≤ (N : ℕ) →
      ∀ (_hn : (n : ℕ) ≤ (N : ℕ)) (a : ℤ) (i : Fin (n : ℕ)),
      (n : ℕ) ≤ 4*(i.val+1) → 4*(i.val+1) ≤ 3*(n : ℕ) →
      ∀ (j : Fin (n : ℕ)) (f g : GapObservable),
        let p := ofLong β s
        |covariance (fun X => f.val.1 (gap X (a+i.val)))
            (fun X => g.val.1 (gap X (a+j.val))) (gibbsMeasure p N)| ≤
          A*(n : ℝ)^(q*h)*((1+|(j.val : ℝ)-(i.val : ℝ)|)^(-(2-s.val))+
            (n : ℝ)^(-(1/2 : ℝ)))*
            (2*(gapDerivativeNorm p N (a+i.val) f).toReal+
              Real.exp (-c*(n : ℝ)^GoodBlocks.coefficientTailPower s.val h)*derivativeSup f)*
            (2*(gapDerivativeNorm p N (a+j.val) g).toReal)+
          D*Real.exp (-(Real.log 2/32)*(n : ℝ)^h)*derivativeSup f*derivativeSup g := by
  obtain ⟨hstar,q,hhstar,hq,hdec⟩ := proper_cyclic_covariance_decay hzeta hRig s
  refine ⟨hstar,q,hhstar,hq,fun h hh hsmall => ?_⟩
  have hdec := hdec h hh hsmall
  obtain ⟨K,hK,hthreshold⟩ := upper_tilt_threshold h hh
  refine ⟨max K 16,le_max_right _ _,fun θ βlo βhi hlo hle => ?_⟩
  obtain ⟨A,c,hA,hc,hdec⟩ := hdec θ βlo βhi hlo hle
  obtain ⟨D,hD,hremove⟩ := upper_tilt_covariance_locallyUniform s.val βlo βhi h s.property.1 s.property.2 hlo hle hh
  refine ⟨A,c,D,hA,hc,hD,fun β hβ N n hN hnK hhalf hn a i hil hir j f g => ?_⟩
  intro p
  have hN2 : 2 ≤ (N : ℕ) := by omega
  have hcard := card_cyclicInterval a hn
  obtain ⟨_,hsmall,hz⟩ := hthreshold p N hN2 θ (cyclicInterval N a n) (by rw [hcard]; omega)
  rw [hcard] at hsmall hz
  let u := Riesz1.labelOf N (a+i.val)
  let v := Riesz1.labelOf N (a+j.val)
  have hfi := internal_tilt_derivative p N hN2 θ ((n : ℝ)^h)
    (Real.rpow_nonneg (by positivity) h) (cyclicInterval N a n) hz u f
  have hgj := internal_tilt_derivative p N hN2 θ ((n : ℝ)^h)
    (Real.rpow_nonneg (by positivity) h) (cyclicInterval N a n) hz v g
  have hf : eLpNorm (fun X => f.val.2 (gap X (a+i.val))) 2
        (activeTilt p N θ ((n : ℝ)^h) false (cyclicInterval N a n)) ≤
      2*gapDerivativeNorm p N (a+i.val) f := by
    simpa only [gapDerivativeNorm,u,← internal_gap_label] using hfi.1
  have hft : eLpNorm (fun X => f.val.2 (gap X (a+i.val))) ∞
        (activeTilt p N θ ((n : ℝ)^h) false (cyclicInterval N a n)) ≤
      ENNReal.ofReal (derivativeSup f) := by
    simpa only [u,← internal_gap_label] using hfi.2
  have hg : eLpNorm (fun X => g.val.2 (gap X (a+j.val))) 2
        (activeTilt p N θ ((n : ℝ)^h) false (cyclicInterval N a n)) ≤
      2*gapDerivativeNorm p N (a+j.val) g := by
    simpa only [gapDerivativeNorm,v,← internal_gap_label] using hgj.1
  have hm := ShortRangeResult.internal_gapSecondMoments p N u v f g
  have hmfi : gapDerivativeNorm p N (a+i.val) f ≠ ⊤ := by
    simpa only [gapDerivativeNorm,u,← internal_gap_label] using hm.2.2.1.eLpNorm_ne_top
  have hmgj : gapDerivativeNorm p N (a+j.val) g ≠ ⊤ := by
    simpa only [gapDerivativeNorm,v,← internal_gap_label] using hm.2.2.2.eLpNorm_ne_top
  have hb := hdec β hβ N n hN (by omega) hhalf hn a i hil hir j f g
  have hreal := internal_real_bound (by positivity) (Real.exp_nonneg _)
    (show 0 ≤ derivativeSup f from ENNReal.toReal_nonneg) hmfi hmgj hf hg hft hb
  have hr := hremove p rfl hβ.1 hβ.2 N hN2 θ (cyclicInterval N a n) (by rw [hcard]; have := n.pos; omega)
    (by simpa only [hcard] using hsmall) f g (a+i.val) (a+j.val)
  rw [hcard] at hr
  exact internal_remove_real hreal hr

/-- The distance profile absorbs a polynomial volume loss whenever that
volume is bounded by a power of distance. Internal step supporting the proof of Theorem 1. -/
theorem profile_loss_internal {p ε ρ a r n B : ℝ}
    (hr : 1 ≤ r) (hn : 0 < n) (hupper : n ≤ B*r^ρ)
    (ha : 0 ≤ a) (hρa : ρ*a ≤ ε) (hB : 0 ≤ B) :
    n^a*r^(-p) ≤ B^a*r^(-p+ε) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hloss : n^a ≤ B^a*r^ε := by
    calc
      _ ≤ (B*r^ρ)^a := Real.rpow_le_rpow hn.le hupper ha
      _ = B^a*r^(ρ*a) := by
        rw [Real.mul_rpow hB (Real.rpow_nonneg hr0.le _),← Real.rpow_mul hr0.le]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hr hρa) (Real.rpow_nonneg hB _)
  calc
    _ ≤ (B^a*r^ε)*r^(-p) := mul_le_mul_of_nonneg_right hloss (by positivity)
    _ = _ := by rw [mul_assoc,← Real.rpow_add hr0]; ring_nf

/-- A proper block of polynomial size absorbs its inverse-square-root
error, supporting the proof of Theorem 1. -/
theorem near_profile_internal {p ε ρ a r n B : ℝ}
    (hr : 1 ≤ r) (hn : r^ρ ≤ n) (hupper : n ≤ B*r^ρ)
    (hρp : 2*p ≤ ρ) (ha : 0 ≤ a) (hρa : ρ*a ≤ ε) (hB : 0 ≤ B) :
    n^a*(r^(-p)+n^(-(1/2 : ℝ))) ≤ 2*B^a*r^(-p+ε) := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hnr : 0 < r^ρ := Real.rpow_pos_of_pos hr0 ρ
  have hn0 : 0 < n := hnr.trans_le hn
  have herr : n^(-(1/2 : ℝ)) ≤ r^(-p) := by
    calc
      _ ≤ (r^ρ)^(-(1/2 : ℝ)) := Real.rpow_le_rpow_of_nonpos hnr hn (by norm_num)
      _ = r^(ρ*(-(1/2 : ℝ))) := (Real.rpow_mul hr0.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hr (by linarith)
  have hloss := profile_loss_internal (p := p) hr hn0 hupper ha hρa hB
  have hm := mul_le_mul_of_nonneg_left herr (Real.rpow_nonneg hn0.le a)
  nlinarith only [hloss,hm]

/-- The bounded-size reduction in Theorem 1 of the paper.
Bounded sizes, for arbitrary positive rate and exponent, supporting
the proof of Theorem 1. Finiteness is a conclusion,
including every choice of the a.e. derivative representative. -/
theorem bounded_sizes_uniform (s : Riesz1.RieszExponent) (ε c δ : ℝ) (hε : 0 < ε)
    (hc : 0 < c) (hδ : 0 < δ) (K : ℕ+) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : InverseTemperature) (N : ℕ+), (N : ℕ) ≤ K →
      ∀ (i j : Fin (N : ℕ)) (f g : GapObservable),
        let p := ofLong β s
        let d := Riesz1.cyclicIndexDistance N i j
        ∃ hMom : GapSecondMoments p N i.val j.val f g,
        |gapCorrelation p N i.val j.val f.val.1 g.val.1 hMom.1 hMom.2.1| ≤
          C*(1+(d : ℝ))^(-(2-s.val)+ε)*
            correlationFactor p N i.val f c δ d*correlationFactor p N j.val g c δ d := by
  let B := (1+(K : ℝ))^(2-s.val)
  let E := Real.exp (2*c*(K : ℝ)^δ)
  let C := 2*((K : ℝ)+1)^2*B*E
  have hB : 0 < B := by dsimp [B]; positivity
  have hE : 0 < E := Real.exp_pos _
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,fun β N hNK i j f g => ?_⟩
  intro p d
  have hNK' : (N : ℝ) ≤ K := by exact_mod_cast hNK
  have hdK : (d : ℝ) ≤ K := by
    have he := Riesz1.APG.cyclicIndexDistance_le_half i j
    exact_mod_cast (show d ≤ (K : ℕ) by dsimp [d]; omega)
  let P := (1+(d : ℝ))^(-(2-s.val)+ε)
  have hr : 1 ≤ 1+(d : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg d)
  have hp : 0 ≤ 2-s.val := by linarith [s.property.2]
  have hP : 1 ≤ B*P := by
    have hw : (1+(K : ℝ))^(-(2-s.val)) ≤ P :=
      (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)).trans
        (Real.rpow_le_rpow_of_exponent_le hr (by linarith))
    have hm := mul_le_mul_of_nonneg_left hw hB.le
    have he : B*(1+(K : ℝ))^(-(2-s.val)) = 1 := by
      dsimp [B]
      rw [← Real.rpow_add (by positivity : 0 < 1+(K : ℝ)),add_neg_cancel,Real.rpow_zero]
    rwa [he] at hm
  have hfactor (f : GapObservable) (k : ℤ) :
      derivativeSup f*Real.exp (-c*(K : ℝ)^δ) ≤ correlationFactor p N k f c δ d := by
    apply le_trans _ (le_add_of_nonneg_left ENNReal.toReal_nonneg)
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    apply Real.exp_le_exp.mpr
    have ht := Real.rpow_le_rpow (Nat.cast_nonneg d) hdK hδ.le
    nlinarith only [mul_le_mul_of_nonneg_left ht hc.le]
  have hf : 0 ≤ derivativeSup f := ENNReal.toReal_nonneg
  have hg : 0 ≤ derivativeSup g := ENNReal.toReal_nonneg
  have hprod := mul_le_mul (hfactor f i.val) (hfactor g j.val) (by positivity)
    (ShortRangeResult.internal_correlationFactor_nonneg p N i.val f c δ d)
  have he : E*(Real.exp (-c*(K : ℝ)^δ)*Real.exp (-c*(K : ℝ)^δ)) = 1 := by
    dsimp [E]
    rw [← Real.exp_add,← Real.exp_add]
    rw [show 2*c*(K : ℝ)^δ+(-c*(K : ℝ)^δ+ -c*(K : ℝ)^δ) = 0 by ring, Real.exp_zero]
  have hprod' : derivativeSup f*derivativeSup g ≤
      E*(correlationFactor p N i.val f c δ d*correlationFactor p N j.val g c δ d) := by
    have ht := mul_le_mul_of_nonneg_left hprod hE.le
    calc
      _ = E*((derivativeSup f*Real.exp (-c*(K : ℝ)^δ))*
          (derivativeSup g*Real.exp (-c*(K : ℝ)^δ))) := by
        rw [show E*((derivativeSup f*Real.exp (-c*(K : ℝ)^δ))*
          (derivativeSup g*Real.exp (-c*(K : ℝ)^δ))) =
          (E*(Real.exp (-c*(K : ℝ)^δ)*Real.exp (-c*(K : ℝ)^δ)))*(derivativeSup f*derivativeSup g) by ring,he,one_mul]
      _ ≤ _ := ht
  refine ⟨ShortRangeResult.internal_gapSecondMoments p N i j f g,?_⟩
  have hb := ShortRangeResult.internal_covariance_bound p N i j f g
  change |covariance _ _ _| ≤ _
  calc
    _ ≤ 2*((K : ℝ)+1)^2*(derivativeSup f*derivativeSup g) :=
      hb.trans (by
        rw [mul_assoc (2*((N : ℝ)+1)^2)]
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hf hg)
        gcongr)
    _ ≤ 2*((K : ℝ)+1)^2*(E*(correlationFactor p N i.val f c δ d*
        correlationFactor p N j.val g c δ d)) :=
      mul_le_mul_of_nonneg_left hprod' (by positivity)
    _ ≤ C*P*correlationFactor p N i.val f c δ d*correlationFactor p N j.val g c δ d := by
      have ht := mul_le_mul_of_nonneg_left hP
        (show 0 ≤ 2*((K : ℝ)+1)^2*E*(correlationFactor p N i.val f c δ d*
          correlationFactor p N j.val g c δ d) from by
            apply mul_nonneg (by positivity)
            exact mul_nonneg (ShortRangeResult.internal_correlationFactor_nonneg ..)
              (ShortRangeResult.internal_correlationFactor_nonneg ..))
      dsimp only [C]
      nlinarith only [ht]

end Riesz2.DecayLong.UpperCorrelations
