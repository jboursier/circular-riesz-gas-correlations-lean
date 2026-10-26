/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.JointAdmissibilityFamily

/-!
# Joint compatible conditional comparison

Strengthened interfaces for Proposition 6.6: the same structural choice retains
original-law exterior typicality throughout the analytic chain.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal ContDiff Topology MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
open Riesz2.JointAdmissibility

namespace Riesz2.CompatibleComparison

/-- See the proof of Proposition 6.6 in the paper: the analytic conclusion and original exterior
typicality use one choice of A,K. A may exceed a prescribed threshold. -/
theorem compatible_conditional_comparison_joint (hzeta : External.PeriodicZeta)
    (hRig : External.LongRangeRigidityLocallyUniform) (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ A K ε₀ κ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧ 0 < κ ∧
    OriginalTypicality s A K ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    K*ε+min s 1/2 ≤ 1 ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
    ∀ a d e : ℕ, 1 ≤ a → 4*(a+1) ≤ d+1+a+1 → d ≤ e →
      (a+1 : ℝ)^(2/s) ≤ (d+1+a+1 : ℝ) →
    ∀ (L : ℝ), 0 < L →
    ∀ (y : AffineSimplex.chartDomain (d+1) ((d+1+a : ℕ)+1))
      (z : AffineSimplex.chartDomain (e+1) ((e+1+a : ℕ)+1)),
      InterpolantLocalLaws.admissibleExterior p (d+1) a (by omega) θ ε A K y →
      InterpolantLocalLaws.admissibleExterior p (e+1) a (by omega) θ ε A K z →
      ((d+1+a : ℕ)+1 : ℝ)-∑ i, y.val i = L →
      ((e+1+a : ℕ)+1 : ℝ)-∑ i, z.val i = L →
    (∀ x : Fin (a+1) → ℝ,
      x ∈ goodBlockEvent s a.succPNat (d+1+a).succPNat (K*ε) ↔
      (∀ i, (a+1 : ℝ)^(-(K*ε)) ≤ x i ∧ x i ≤ (a+1 : ℝ)^(K*ε)) ∧
      ∀ l r : ℕ, l < r → r ≤ a+1 →
        |(∑ i ∈ Finset.univ.filter (fun i : Fin (a+1) => l ≤ i.val ∧ i.val < r), x i)-
          (r-l : ℕ)| ≤ (a+1 : ℝ)^(K*ε)*(r-l : ℕ)^(min s 1/2)) ∧
    ∃ Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ,
      (∀ u (hu : RetainedSimplex.assemble (d+1) a
        (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u ∈
          gapAmbientDomain (d+1+a).succPNat),
        Ky u = physicalAmbientGapEnergy p (d+1+a).succPNat
          ⟨RetainedSimplex.assemble (d+1) a
            (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u,hu⟩) ∧
      (∀ u (hu : RetainedSimplex.assemble (e+1) a
        (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u ∈
          gapAmbientDomain (e+1+a).succPNat),
        Kz u = physicalAmbientGapEnergy p (e+1+a).succPNat
          ⟨RetainedSimplex.assemble (e+1) a
            (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u,hu⟩) ∧
    let σ := (AffineSimplex.simplexVolume a L).comap Subtype.val
    let P := fun u : AffineSimplex.massSimplex a L =>
      ∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u.val i)+θ.val ((a+1 : ℝ)^(-ε)*(u.val i)⁻¹))
    let w := fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal (Real.exp (-(p.val.1*(P u+Ky u.val))))
    let z' := fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal (Real.exp (-(p.val.1*(P u+Kz u.val))))
    ∃ (hw0 : (∫⁻ u, w u ∂σ) ≠ 0) (hwt : (∫⁻ u, w u ∂σ) ≠ ⊤)
      (hz0 : (∫⁻ u, z' u ∂σ) ≠ 0) (hzt : (∫⁻ u, z' u ∂σ) ≠ ⊤),
    let ρy := AffineFibre.normalizedMeasure σ w hw0 hwt
    let ρz := AffineFibre.normalizedMeasure σ z' hz0 hzt
    ∀ (G : BlockObservable a.succPNat) (J : Finset (Fin (a+1))),
      DependsOnBlockCoordinates G J →
      (∀ i ∈ J, |(i.val : ℝ)+1-(a+1 : ℝ)/2| ≤ (a+1 : ℝ)/4) →
      Integrable (fun u => G.val (WithLp.ofLp u.val)) ρy ∧
      Integrable (fun u => G.val (WithLp.ofLp u.val)) ρz ∧
      |(∫ u, G.val (WithLp.ofLp u.val) ∂ρy)-(∫ u, G.val (WithLp.ofLp u.val) ∂ρz)| ≤
        C*(a+1 : ℝ)^(κ*ε-min s 1/2)*
          (restrictedBlockDerivativeNorm G J (goodBlockEvent s a.succPNat (d+1+a).succPNat (K*ε))+
            Real.exp (-c*(a+1 : ℝ)^δ)*blockDerivativeNorm G) := by
  obtain ⟨A,K,εc,κd,hA,hK,hεc,hκd,htyp,hcommon⟩ := common_physical_family_internal_joint hzeta hRig s hs hs1
  obtain ⟨κb,hκb,hcoeff⟩ := physical_differential_bounds_uniform_internal s hs hs1 K hK
  have hσ1 : min s 1/2 ≤ (1 : ℝ)/2 := div_le_div_of_nonneg_right (min_le_right s 1) (by norm_num)
  have hσs : min s 1/2 ≤ s/2 := div_le_div_of_nonneg_right (min_le_left s 1) (by norm_num)
  have hthreshold : 0 < min (1-min s 1/2) (s-min s 1/2)/4 := by
    apply div_pos (lt_min (by linarith) (by linarith)) (by norm_num)
  have hKpos : 0 < K := lt_trans zero_lt_one hK
  have hcutoff : 0 < (1-min s 1/2)/(2*K) := div_pos (by linarith) (by positivity)
  refine ⟨A,K,min εc (min (min (1-min s 1/2) (s-min s 1/2)/4)
    ((1-min s 1/2)/(2*K))),κd+κb,hA,hK,lt_min hεc (lt_min hthreshold hcutoff),
    add_pos hκd hκb,htyp.restrict (min_le_left _ _),?_⟩
  intro ε hε hε₀
  have hεc' : ε < εc := lt_of_lt_of_le hε₀ (min_le_left _ _)
  have hεrest := lt_of_lt_of_le hε₀ (min_le_right _ _)
  have hεdiff := lt_of_lt_of_le hεrest (min_le_left _ _)
  have hεcut := lt_of_lt_of_le hεrest (min_le_right _ _)
  obtain ⟨Cb,hCb,hcb⟩ := hcoeff ε hε hεdiff
  obtain ⟨δ,hδ,hdata⟩ := hcommon ε hε hεc'
  have hεfine : K*ε+min s 1/2 ≤ 1 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 2*K)).mp hεcut
    nlinarith
  refine ⟨δ,hδ,hεfine,?_⟩
  intro βlo βhi hβlo hβorder θ
  obtain ⟨Ct,ct,Cd,cd,hCt,hct,hCd,hcd,hfamily⟩ := hdata βlo βhi hβlo hβorder θ
  obtain ⟨Cf,cf,hCf,hcf,hcomparison⟩ := physical_smooth_family_comparison_internal
    s hs βlo Cb κb Ct ct Cd cd δ κd ε hβlo hCb hCt hct hCd hcd hδ hε
  have hβhi : 0 < βhi := lt_of_lt_of_le hβlo hβorder
  refine ⟨βhi*Cf,cf,mul_pos hβhi hCf,hcf,?_⟩
  intro p hps hβ hβhi' a d e ha hsize hde hpower L hL y z hy hz hyL hzL
  obtain ⟨Ky,Kz,hKy,hKz,Bcarrier,hLN,hfam⟩ := hfamily p hps hβ hβhi' a d e ha hsize hde hpower
    L hL y z hy hz hyL hzL
  have hfine : ∀ x : Fin (a+1) → ℝ,
      x ∈ goodBlockEvent s a.succPNat (d+1+a).succPNat (K*ε) ↔
      (∀ i, (a+1 : ℝ)^(-(K*ε)) ≤ x i ∧ x i ≤ (a+1 : ℝ)^(K*ε)) ∧
      ∀ l r : ℕ, l < r → r ≤ a+1 →
        |(∑ i ∈ Finset.univ.filter (fun i : Fin (a+1) => l ≤ i.val ∧ i.val < r), x i)-
          (r-l : ℕ)| ≤ (a+1 : ℝ)^(K*ε)*(r-l : ℕ)^(min s 1/2) := by
    have h4 : 4*(a+1 : ℝ) ≤ (d+1+a+1 : ℝ) := by exact_mod_cast hsize
    have h2 : 2*(a.succPNat : ℝ) < ((d+1+a).succPNat : ℝ) := by
      simp only [Nat.succPNat_coe,Nat.cast_succ,Nat.cast_add]
      nlinarith [Nat.cast_nonneg (α := ℝ) a]
    intro x
    simpa only [Nat.succPNat_coe,Nat.cast_succ] using
      fine_event_without_volume_cutoff s (K*ε) a.succPNat (d+1+a).succPNat hεfine h2 x
  refine ⟨hfine,Ky,Kz,hKy,hKz,?_⟩
  intro σ P w z'
  let frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a) :=
    ((stdOrthonormalBasis ℝ (AffineSimplex.Tangent a)).reindex
      (finCongr (AffineSimplex.finrank_tangent a))).repr
  obtain ⟨μ,hμ,hV,Q,hν,hQ,hform,htail,hdec⟩ := hfam frame
  let H := fun (t : ℝ) (u : EuclideanSpace ℝ (Fin (a+1))) => p.val.1*
    ((∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u i)+θ.val ((a+1 : ℝ)^(-ε)*(u i)⁻¹)))+
      (1-t)*Ky u+t*Kz u)
  let U := frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
  let ν := fun t => ((μ t).comap (Subtype.val : U → _)).map
    (InterpolationTransport.orthonormalInclusion a L _ hLN frame)
  have hKys := physical_realization_smooth_internal p a d y Ky hKy
  have hKzs := physical_realization_smooth_internal p a e z Kz hKz
  obtain ⟨h00,h0t,he0⟩ := physical_normalized_chart_internal p a d e θ ε L y z hyL hzL
    Ky Kz hKys hKzs 0 _ hLN frame (μ 0) (hV 0 (by norm_num))
  obtain ⟨h10,h1t,he1⟩ := physical_normalized_chart_internal p a d e θ ε L y z hyL hzL
    Ky Kz hKys hKzs 1 _ hLN frame (μ 1) (hV 1 (by norm_num))
  simp only [zero_mul,one_mul,sub_zero,sub_self,add_zero] at h00 h0t he0 h10 h1t he1
  refine ⟨h00,h0t,h10,h1t,?_⟩
  have hw : Measurable w := by
    have hc : Continuous (fun u : AffineSimplex.massSimplex a L => H 0 u.val) :=
      continuous_iff_continuousAt.mpr fun u =>
        (physical_interpolant_smooth_internal p a d e θ ε L y z hyL hzL Ky Kz
          hKys hKzs 0 u.val u.property).continuousAt.comp continuous_subtype_val.continuousAt
    simpa only [H,w,P,Pi.neg_apply,zero_mul,one_mul,sub_zero,add_zero] using hc.neg.measurable.exp.ennreal_ofReal
  have hz' : Measurable z' := by
    have hc : Continuous (fun u : AffineSimplex.massSimplex a L => H 1 u.val) :=
      continuous_iff_continuousAt.mpr fun u =>
        (physical_interpolant_smooth_internal p a d e θ ε L y z hyL hzL Ky Kz
          hKys hKzs 1 u.val u.property).continuousAt.comp continuous_subtype_val.continuousAt
    simpa only [H,z',P,Pi.neg_apply,zero_mul,one_mul,sub_self,zero_add,add_zero] using hc.neg.measurable.exp.ennreal_ofReal
  apply included_lipschitz_comparison_internal s (K*ε) (mul_pos hKpos hε) a ha
    (d+1+a).succPNat (by simp only [Nat.succPNat_coe]; omega) L hL Bcarrier hLN w z' hw hz'
    h00 h0t h10 h1t (βhi*Cf) cf (κd+κb) ε δ (mul_pos hβhi hCf).le
  intro G hsG J hJ hmiddle
  have hh := hcomparison p a d e ha θ L hL y z hyL hzL Ky Kz hKy hKz hps hβ hpower Bcarrier hLN frame
    (K*ε) (mul_pos hKpos hε) (by simp only [Nat.succPNat_coe]; omega)
    (by simpa only [Nat.succPNat_coe,Nat.cast_succ,Nat.cast_add,Nat.cast_one] using
      hcb a d e ha hsize hde hpower p hps θ A L hA y z hy hz hyL hzL Ky Kz hKy hKz)
    μ hμ hV Q hν hQ hform htail hdec G hsG J hJ hmiddle
  dsimp only at hh
  rw [he0,he1] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_right
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hβhi' hCf.le) (by positivity)
  · have hnonneg : 0 ≤ restrictedBlockDerivativeNorm G J
        (goodBlockEvent s a.succPNat (d+1+a).succPNat (K*ε)) := by
      unfold restrictedBlockDerivativeNorm
      exact Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _
    have hb : 0 ≤ blockDerivativeNorm G := by
      unfold blockDerivativeNorm
      positivity
    exact add_nonneg hnonneg (mul_nonneg (Real.exp_pos _).le hb)

end Riesz2.CompatibleComparison
