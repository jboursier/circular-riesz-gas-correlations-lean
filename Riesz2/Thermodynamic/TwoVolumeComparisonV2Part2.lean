/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.JointAdmissibilityIntegrated

/-!
# Comparison of two tilted volumes

See Proposition 6.6 of the paper. Original exterior admissibility and fixed comparison
share their structural parameters.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace Riesz2.TwoVolumeComparison

/-- See Subsection 6.1 and Lemma 6.5 of the paper: the chart active expectation is the
literal tilted particle expectation, with the finite gap block. -/
theorem active_particle_expectation (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) (G : BlockObservable n.succPNat) :
    (∫ x, G.val (WithLp.ofLp x) ∂LengthAveragingFibres.activeMeasure p n m θ ε) =
      ∫ X, G.val (finiteGapBlock X) ∂tiltedParticleMeasure p ((n+1)+m).succPNat
        n.succPNat (by simp only [Nat.succPNat_coe]; omega) θ ε true := by
  have hmap : Measurable (fun X : Riesz1.Configuration ((n+1)+m).succPNat =>
      WithLp.toLp 2 (finiteGapBlock (K := n.succPNat) X)) :=
    (WithLp.measurable_toLp 2 _).comp
      (Measurable.of_eval fun i => Riesz1.measurable_gap i.val)
  have hG : AEStronglyMeasurable (fun x : EuclideanSpace ℝ (Fin (n+1)) =>
      G.val (WithLp.ofLp x)) (LengthAveragingFibres.activeMeasure p n m θ ε) :=
    (G.property.choose_spec.continuous.measurable.comp
      (WithLp.measurable_ofLp 2 _)).aestronglyMeasurable
  exact (integral_map hmap.aemeasurable hG).trans (integral_congr_ae
    (ae_of_all _ fun X => congrArg G.val (WithLp.ofLp_toLp 2 (finiteGapBlock X))))

/-- See Subsection 6.1 of the paper: transporting the chart expectation along an
ambient size equality does not change the tilted particle expectation. -/
theorem active_particle_expectation_of_size (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) (N : ℕ+)
    (hN : ((n+1)+m).succPNat = N) (hn : (n.succPNat : ℕ) ≤ (N : ℕ))
    (G : BlockObservable n.succPNat) :
    (∫ x, G.val (WithLp.ofLp x) ∂LengthAveragingFibres.activeMeasure p n m θ ε) =
      ∫ X, G.val (finiteGapBlock X) ∂tiltedParticleMeasure p N n.succPNat hn θ ε true := by
  subst N
  exact active_particle_expectation p n m θ ε G

/-- See Proposition 6.6 of the paper: above the overlap threshold, the
original tilted active laws obey the complete comparison estimate. The
admissibility tails are supplied for the same A,K as fixed comparison.
All structural choices precede ε and every tail power precedes β. -/
theorem large_sizes_comparison
    (hz : External.PeriodicZeta) (hRig : External.LongRangeRigidityLocallyUniform)
    (hLog : External.ThermodynamicLogConcavity)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ Kₛ κ ε₀ : ℝ, 1 < Kₛ ∧ 0 < κ ∧ 0 < ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    ∀ θ : PhysicalCutoff, ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
    ∀ n m m' : ℕ, n₀ ≤ n → m ≤ m' → 4*(n+1) ≤ n+1+m+1 →
      (n+1 : ℝ)^(2/s) ≤ ((n+1+m : ℕ)+1 : ℝ) →
    ∀ R : ℕ, R ≤ (n+1)/4 → ((n+1)%4 ≠ 1 ∨ R < (n+1)/4) →
    ∀ G : BlockObservable n.succPNat,
      DependsOnBlockCoordinates G (symmetricMiddleBlock n.succPNat R) →
    |(∫ x, G.val (WithLp.ofLp x) ∂LengthAveragingFibres.activeMeasure p n m θ ε) -
        ∫ x, G.val (WithLp.ofLp x) ∂LengthAveragingFibres.activeMeasure p n m' θ ε| ≤
      C*(n+1 : ℝ)^(κ*ε-min s 1/2)*
        (restrictedBlockDerivativeNorm G (symmetricMiddleBlock n.succPNat R)
          (goodBlockEvent s n.succPNat (n+1+m).succPNat (Kₛ*ε)) +
          Real.exp (-c*(n+1 : ℝ)^δ)*blockDerivativeNorm G) := by
  obtain ⟨A,K,εd,κd,hA,hK,hεd,hκd,htyp,hcomp⟩ :=
    overlap_integrated_comparison_internal_joint hz hRig s hs hs1
  obtain ⟨κo,εo,hκo,hεo,hover⟩ := rounded_overlap_internal hz hRig hLog s hs hs1
  let Kₛ := max K 2
  let κ := max κd κo
  have hKₛ : 1 < Kₛ := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _)
  have hκ : 0 < κ := hκd.trans_le (le_max_left _ _)
  refine ⟨Kₛ,κ,min εd εo,hKₛ,hκ,lt_min hεd hεo,?_⟩
  intro ε hε hsmall
  have hεd' := hsmall.trans_le (min_le_left _ _)
  have hεo' := hsmall.trans_le (min_le_right _ _)
  obtain ⟨δd,hδd,hcomp⟩ := hcomp ε hε hεd'
  obtain ⟨δt,hδt,htyp⟩ := htyp ε hε hεd'
  obtain ⟨δo,hδo,hover⟩ := hover ε hε hεo'.le
  refine ⟨min δo (min δd δt),lt_min hδo (lt_min hδd hδt),?_⟩
  intro θ βlo βhi hlo hle
  obtain ⟨Cd,cd,H,hCd,hcd,hH,hcomp⟩ := hcomp βlo βhi hlo hle θ
  obtain ⟨Ct,ct,hCt,hct,htyp⟩ := htyp βlo βhi hlo hle θ
  obtain ⟨n₀,hn₀,Co,co,hCo,hco,hover⟩ := hover βlo βhi hlo hle θ
  let q := κ*ε-min s 1/2
  obtain ⟨Cb,cb,hCb,hcb,hbad⟩ := ComparisonRates.comparison_with_overlap_loss
    q (κo*ε) δd δt Cd cd H Ct ct Co hδd hδt hCd.le hcd hH.le hCt.le hct hCo.le
  obtain ⟨C,c,hC,hc,hcombine⟩ := ComparisonRates.combine_errors
    q δo (min δd δt) Co Cb co cb hδo (lt_min hδd hδt) hCo.le hCb.le hco hcb
  refine ⟨n₀,hn₀,C,c,hC,hc,?_⟩
  intro p hps hpl hph n m m' hn hmm' h4 hpow R hR hround G hG
  have hn1 : 1 ≤ n := hn₀.trans hn
  have hx : (1 : ℝ) ≤ n+1 := by have := Nat.cast_nonneg n (α := ℝ); linarith
  have hD : 0 ≤ blockDerivativeNorm G := Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _
  let D := blockDerivativeNorm G
  let Ag := restrictedBlockDerivativeNorm G (symmetricMiddleBlock n.succPNat R)
    (goodBlockEvent s n.succPNat (n+1+m).succPNat (Kₛ*ε))
  have hAg : 0 ≤ Ag := Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _
  have hκd' : κd*ε-min s 1/2 ≤ q := by
    dsimp [q,κ]; nlinarith [le_max_left κd κo]
  have hκo' : κo*ε-min s 1/2 ≤ q := by
    dsimp [q,κ]; nlinarith [le_max_right κd κo]
  obtain ⟨hlower,ha₀,_hmeas,_hnonneg,_hone,_hdom,_hdom',havg⟩ :=
    hover p hps hpl hph n m m' hn hmm' h4 hpow
  let f := LengthOverlap.realLengthDensity p n m θ ε
  let f' := LengthOverlap.realLengthDensity p n m' θ ε
  let a₀ := DensityOverlap.mass volume f f'
  let μρ := volume.withDensity (fun L => ENNReal.ofReal (min (f L) (f' L)/a₀))
  have hbinv : a₀⁻¹ ≤ Co*(n+1 : ℝ)^(κo*ε) :=
    ComparisonRates.inverse_overlap_bound ha₀ hCo (by positivity) (by simpa only [neg_mul] using hlower)
  let T := Ct*Real.exp (-ct*(n+1 : ℝ)^δt)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hT₁ := htyp p hps hpl hph (m+1) n (by omega) hn1 (by omega)
    (by simpa only [Nat.cast_add,Nat.cast_one,add_assoc,add_left_comm,add_comm] using hpow)
  have hpow' : (n+1 : ℝ)^(2/s) ≤ ((m'+1+n : ℕ)+1 : ℝ) := by
    apply hpow.trans
    exact_mod_cast (show n+1+m+1 ≤ m'+1+n+1 by omega)
  have hT₂ := htyp p hps hpl hph (m'+1) n (by omega) hn1 (by omega) hpow'
  have hint := hcomp p hps hpl hph n m m' hn1 (by omega) hmm'
    (by simpa only [Nat.cast_add,Nat.cast_one,add_assoc,add_left_comm,add_comm] using hpow) ha₀ T T hT₁ hT₂ R hR hround G hG
  have hperiod : (m+1+n).succPNat = (n+1+m).succPNat := by congr 1; omega
  simp only [hperiod, max_eq_left hT] at hint
  have hnormd : restrictedBlockDerivativeNorm G (symmetricMiddleBlock n.succPNat R)
      (goodBlockEvent s n.succPNat (n+1+m).succPNat (K*ε)) ≤ Ag :=
    restricted_good_norm_mono s G _ (mul_le_mul_of_nonneg_right (le_max_left _ _) hε.le)
  have hinto : |(∫ L, LengthOverlap.realAveragedObservable p n m θ ε G L ∂μρ) -
      ∫ L, LengthOverlap.realAveragedObservable p n m' θ ε G L ∂μρ| ≤
      Cd*(n+1 : ℝ)^q*(Ag+Real.exp (-cd*(n+1 : ℝ)^δd)*D) +
      (Real.sqrt (a₀⁻¹*(H*D^2))+Real.sqrt (a₀⁻¹*(H*D^2)))*
        Real.sqrt (a₀⁻¹*(T+T)) := by
    apply hint.trans
    dsimp only [D,a₀,f,f']
    apply add_le_add _ le_rfl
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx hκd') hCd.le
    · exact add_le_add hnormd le_rfl
    · exact add_nonneg (Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _)
        (mul_nonneg (Real.exp_pos _).le hD)
    · positivity
  have hcommon := hbad (n+1) a₀⁻¹ Ag D _ _ hx (inv_nonneg.mpr ha₀.le) hbinv hAg hD hinto
  obtain ⟨_hi,_hi',hav⟩ := havg R hR hround G hG
  have hnormo : restrictedBlockDerivativeNorm G (symmetricMiddleBlock n.succPNat R)
      (goodBlockEvent s n.succPNat (n+1+m).succPNat (2*ε)) ≤ Ag :=
    restricted_good_norm_mono s G _ (mul_le_mul_of_nonneg_right (le_max_right _ _) hε.le)
  have hav' : |(∫ L, LengthOverlap.realAveragedObservable p n m θ ε G L ∂μρ) -
        ∫ x, G.val (WithLp.ofLp x) ∂LengthAveragingFibres.activeMeasure p n m θ ε| +
      |(∫ L, LengthOverlap.realAveragedObservable p n m' θ ε G L ∂μρ) -
        ∫ x, G.val (WithLp.ofLp x) ∂LengthAveragingFibres.activeMeasure p n m' θ ε| ≤
      Co*(n+1 : ℝ)^q*Ag+Co*Real.exp (-co*(n+1 : ℝ)^δo)*D := by
    apply hav.trans
    dsimp only [D]
    apply add_le_add _ le_rfl
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx hκo') hCo.le)
      hnormo (Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _) (by positivity)
  exact hcombine (n+1) Ag D _ _ _ _ hx hAg hD hav' hcommon

end Riesz2.TwoVolumeComparison

namespace Riesz2

/-- See Proposition 6.6 of the paper: the complete
comparison of the two tilted volumes, with normalization and integrability.
The structural losses precede ε and the positive tail power precedes β. -/
theorem twoVolumeComparisonV2_proof (hz : External.PeriodicZeta)
    (hRig : External.LongRangeRigidityLocallyUniform)
    (hLog : External.ThermodynamicLogConcavity) :
  ∀ s : {s : ℝ // 0 < s ∧ s ≠ 1},
    ∃ Kₛ κ ε₀ : ℝ, 1 < Kₛ ∧ 0 < κ ∧ 0 < ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    ∀ θ : PhysicalCutoff, ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    let p : Parameters := ⟨(β.val, s.val), β.property, s.property⟩
    ∀ (n N N' : ℕ+) (_ : 2 ≤ (n : ℕ)),
      (N : ℕ) ≤ (N' : ℕ) → 4 * (n : ℕ) ≤ (N : ℕ) →
      (n : ℝ) ^ (2 / s.val) ≤ (N : ℝ) →
      ∀ (hn : (n : ℕ) ≤ (N : ℕ)) (hn' : (n : ℕ) ≤ (N' : ℕ)),
      let μ := tiltedParticleMeasure p N n hn θ ε true
      let μ' := tiltedParticleMeasure p N' n hn' θ ε true
      0 < tiltNormalizer p N n hn θ ε true ∧ tiltNormalizer p N n hn θ ε true < ⊤ ∧
      0 < tiltNormalizer p N' n hn' θ ε true ∧ tiltNormalizer p N' n hn' θ ε true < ⊤ ∧
      IsProbabilityMeasure μ ∧ IsProbabilityMeasure μ' ∧
      ∀ (K : ℕ), K ≤ (n : ℕ) / 4 →
        ((n : ℕ) % 4 ≠ 1 ∨ K < (n : ℕ) / 4) → ∀ G : BlockObservable n,
        DependsOnBlockCoordinates G (symmetricMiddleBlock n K) →
        Integrable (fun X => G.val (finiteGapBlock X)) μ ∧
        Integrable (fun X => G.val (finiteGapBlock X)) μ' ∧
        |(∫ X, G.val (finiteGapBlock X) ∂μ) - (∫ X, G.val (finiteGapBlock X) ∂μ')| ≤
          C * (n : ℝ) ^ (κ * ε - min s.val 1 / 2) *
            (restrictedBlockDerivativeNorm G (symmetricMiddleBlock n K)
                (goodBlockEvent s.val n N (Kₛ * ε)) +
              Real.exp (-c * (n : ℝ) ^ δ) * blockDerivativeNorm G)
 := by
  intro s
  obtain ⟨Kₛ,κ,ε₀,hKₛ,hκ,hε₀,hlarge⟩ :=
    TwoVolumeComparison.large_sizes_comparison hz hRig hLog s.val s.property.1 s.property.2
  refine ⟨Kₛ,κ,ε₀,hKₛ,hκ,hε₀,?_⟩
  intro ε hε hεsmall
  obtain ⟨δ,hδ,hlarge⟩ := hlarge ε hε hεsmall
  refine ⟨δ,hδ,?_⟩
  intro θ βlo βhi hlo hle
  obtain ⟨n₀,hn₀,Cb,c,hCb,hc,hlarge⟩ := hlarge θ βlo βhi hlo hle
  obtain ⟨Cs,hCs,hsmall⟩ := TwoVolumeComparison.bounded_sizes_comparison_internal
    s.val ε βlo βhi (κ*ε-min s.val 1/2) c δ (Kₛ*ε)
    s.property.1 s.property.2 hε hlo hle θ (n₀+1)
  refine ⟨Cb+Cs,c,add_pos hCb hCs,hc,?_⟩
  intro β hβ p n N N' hn2 hNN' h4 hpower hn hn' μ μ'
  obtain ⟨hZ,hZt,hZ',hZt',hμ,hμ',hints⟩ :=
    TwoVolumeComparison.comparison_valid p n N N' hn hn' θ ε
  refine ⟨hZ,hZt,hZ',hZt',hμ,hμ',?_⟩
  intro K hK hround G hG
  refine ⟨(hints G).1,(hints G).2,?_⟩
  have hN2 : 2 ≤ (N : ℕ) := by omega
  have hN'2 : 2 ≤ (N' : ℕ) := by omega
  have hD : 0 ≤ blockDerivativeNorm G := Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _
  have hA : 0 ≤ restrictedBlockDerivativeNorm G (symmetricMiddleBlock n K)
      (goodBlockEvent s.val n N (Kₛ*ε)) := Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _
  have hfactor : 0 ≤ (n : ℝ)^(κ*ε-min s.val 1/2)*
      (restrictedBlockDerivativeNorm G (symmetricMiddleBlock n K)
        (goodBlockEvent s.val n N (Kₛ*ε))+
        Real.exp (-c*(n : ℝ)^δ)*blockDerivativeNorm G) := by positivity
  by_cases hbig : n₀ ≤ (n : ℕ)-1
  · rcases n with ⟨k,hk⟩
    obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    let m := (N : ℕ)-(a+1)-1
    let m' := (N' : ℕ)-(a+1)-1
    have hNEq : ((a+1)+m).succPNat = N := by
      apply PNat.eq
      dsimp [m]
      change 4*(a+1) ≤ (N : ℕ) at h4
      omega
    have hN'Eq : ((a+1)+m').succPNat = N' := by
      apply PNat.eq
      dsimp [m']
      change 4*(a+1) ≤ (N : ℕ) at h4
      omega
    have hfour : 4*(a+1) ≤ a+1+m+1 := by
      simpa only [← hNEq,Nat.succPNat_coe,PNat.mk_coe,Nat.succ_eq_add_one] using h4
    have hpow : (a+1 : ℝ)^(2/s.val) ≤ ((a+1+m : ℕ)+1 : ℝ) := by
      simpa only [← hNEq,PNat.mk_coe,Nat.succPNat_coe,Nat.cast_succ] using hpower
    have hmm' : m ≤ m' := by dsimp [m,m']; omega
    have ha : n₀ ≤ a := by change n₀ ≤ a+1-1 at hbig; omega
    have he := hlarge p rfl hβ.1 hβ.2 a m m' ha hmm' hfour hpow K hK hround G hG
    rw [TwoVolumeComparison.active_particle_expectation_of_size p a m θ ε N hNEq hn G,
      TwoVolumeComparison.active_particle_expectation_of_size p a m' θ ε N' hN'Eq hn' G] at he
    have he' : |(∫ X, G.val (finiteGapBlock X) ∂μ) -
        ∫ X, G.val (finiteGapBlock X) ∂μ'| ≤
        Cb*((⟨a.succ,hk⟩ : ℕ+) : ℝ)^(κ*ε-min s.val 1/2)*
          (restrictedBlockDerivativeNorm G (symmetricMiddleBlock ⟨a.succ,hk⟩ K)
            (goodBlockEvent s.val ⟨a.succ,hk⟩ N (Kₛ*ε))+
            Real.exp (-c*((⟨a.succ,hk⟩ : ℕ+) : ℝ)^δ)*blockDerivativeNorm G) := by
      rw [hNEq] at he
      dsimp only [μ,μ']
      simpa only [Nat.succPNat,PNat.mk_coe,Nat.cast_succ] using he
    apply he'.trans
    simpa only [PNat.mk_coe,Nat.cast_succ,mul_assoc] using
      mul_le_mul_of_nonneg_right (show Cb ≤ Cb+Cs by linarith) hfactor
  · have he := hsmall p rfl hβ.1 hβ.2 N N' n hN2 hN'2 (by omega) hn hn' G
      (symmetricMiddleBlock n K)
    apply he.trans
    simpa only [PNat.mk_coe,Nat.cast_succ,mul_assoc] using
      mul_le_mul_of_nonneg_right (show Cs ≤ Cb+Cs by linarith) hfactor

end Riesz2
