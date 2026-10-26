/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.UpperCorrelationsCore

/-!
# The distance threshold in the proof of Theorem 1

The proof of Theorem 1 of the paper uses a proper
window when `1 + d ≤ N^δ₀`, and the full cycle otherwise. Here `ρ > 2(2-s)`
and `δ₀ = 1/(2ρ)`. Bounded volumes are absorbed uniformly in temperature.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal BigOperators Topology

namespace Riesz2.DecayLong.UpperCorrelations

open Riesz2.DecayShort GibbsPotentialComparison PhysicalCore
open Riesz2.DecayShort.ShortRangeResultPart5

set_option backward.isDefEq.respectTransparency false

/-- The window chosen in the near regime of Theorem 1
of the paper fits into half the system for all sufficiently large volumes. -/
theorem threshold_window_fit_internal {ρ B r n N : ℝ}
    (hρ : 0 < ρ) (hB : 0 < B) (hr : 0 ≤ r) (hN : 0 < N)
    (hn : n ≤ B*r^ρ) (hnear : r ≤ N^(1/(2*ρ)))
    (hlarge : (2*B)^2 ≤ N) : 2*n ≤ N := by
  have hp : r^ρ ≤ N^(1/2 : ℝ) := by
    have ht := Real.rpow_le_rpow hr hnear hρ.le
    rw [← Real.rpow_mul hN.le] at ht
    have he : 1/(2*ρ)*ρ = (1/2 : ℝ) := by field_simp
    rwa [he] at ht
  have hsquare : (N^(1/2 : ℝ))^2 = N := by
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hN.le]
  have hsqrt : 0 ≤ N^(1/2 : ℝ) := by positivity
  have hroot : 2*B ≤ N^(1/2 : ℝ) := by nlinarith only [hlarge,hsquare,hsqrt,hB]
  have ht := mul_nonneg (sub_nonneg.mpr hroot) hsqrt
  have hn' := mul_le_mul_of_nonneg_left hp hB.le
  nlinarith only [hn,hn',ht,hsquare]

/-- The upper bound of Theorem 1 of the paper,
with the printed switch at `r = N^δ₀` and constants uniform on a temperature interval.
See the proof of Theorem 1 in the paper: physical gap
covariance decay, including second moments. The stretched-exponential power
is chosen before temperature. Both factors use the unforced derivative norms. -/
theorem decay_gap_correlations_upper_locallyUniform_by_threshold (hzeta : External.PeriodicZeta)
    (hRig : External.LongRangeRigidityLocallyUniform) :
  ∀ s : Riesz1.RieszExponent, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (i j : Fin (N : ℕ)) (f g : GapObservable),
        let p := ofLong β s
        let d := Riesz1.cyclicIndexDistance N i j
        ∃ hMom : GapSecondMoments p N i.val j.val f g,
        |gapCorrelation p N i.val j.val f.val.1 g.val.1 hMom.1 hMom.2.1| ≤
          C * (1 + (d : ℝ)) ^ (-(2-s.val) + ε) *
            correlationFactor p N i.val f c δ d * correlationFactor p N j.val g c δ d := by
  intro s ε hε
  obtain ⟨hstar₁,q₁,hhstar₁,hq₁,hproper⟩ := proper_unforced_decay_locallyUniform hzeta hRig s
  obtain ⟨hstar₂,q₂,hhstar₂,hq₂,hfull⟩ := full_unforced_decay_locallyUniform hzeta hRig s
  have hp : 1 < 2-s.val := by linarith [s.property.2]
  let ρ := 4*(2-s.val)
  have hρ : 1 ≤ ρ := by dsimp [ρ]; linarith only [hp]
  have hρstrict : 2*(2-s.val) < ρ := by dsimp [ρ]; linarith only [hp]
  have hρs : 2*(2-s.val) ≤ ρ := hρstrict.le
  let Q := q₁+q₂+1
  have hQ : 0 < Q := by dsimp [Q]; positivity
  let h₀ := ε/(4*ρ*Q)
  have hh₀ : 0 < h₀ := by dsimp [h₀]; positivity
  have he : ρ*h₀*Q = ε/4 := by dsimp [h₀]; field_simp
  have hpa₁₀ : ρ*(q₁*h₀) ≤ ε/2 := by
    have ht := mul_le_mul_of_nonneg_left (show q₁ ≤ Q by dsimp [Q]; linarith only [hq₂])
      (show 0 ≤ ρ*h₀ by positivity)
    nlinarith only [ht,he,hε]
  have hpa₂₀ : ρ*(q₂*h₀) ≤ ε/2 := by
    have ht := mul_le_mul_of_nonneg_left (show q₂ ≤ Q by dsimp [Q]; linarith only [hq₁])
      (show 0 ≤ ρ*h₀ by positivity)
    nlinarith only [ht,he,hε]
  let δ₀ := 1/(2*ρ)
  have hρpos : 0 < ρ := by linarith
  have hδ₀ : 0 < δ₀ := by dsimp [δ₀]; positivity
  have hρδ₀ : ρ*δ₀ < 1 := by
    dsimp [δ₀]
    field_simp
    linarith
  let h := min h₀ (min hstar₁ hstar₂/2)
  have hh : 0 < h := lt_min hh₀ (by positivity)
  have hh₀' : h ≤ h₀ := min_le_left _ _
  have hh₁ : h ≤ hstar₁ :=
    (min_le_right _ _).trans (by linarith [min_le_left hstar₁ hstar₂,hhstar₁])
  have hh₂ : h < hstar₂ :=
    (min_le_right _ _).trans_lt (by linarith [min_le_right hstar₁ hstar₂,hhstar₂])
  have ha₁ : 0 ≤ q₁*h := mul_nonneg hq₁.le hh.le
  have ha₂ : 0 ≤ q₂*h := mul_nonneg hq₂.le hh.le
  have hpa₁ : ρ*(q₁*h) ≤ ε := by
    have ht := (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh₀' hq₁.le) hρpos.le).trans hpa₁₀
    linarith
  have hpa₂ : (2*ρ)*(q₂*h) ≤ ε := by
    have ht := (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh₀' hq₂.le) hρpos.le).trans hpa₂₀
    nlinarith only [ht]
  obtain ⟨K₁,hK₁,hproper⟩ := hproper h hh hh₁
  obtain ⟨K₂,hK₂,hfull⟩ := hfull h hh hh₂
  let δA := GoodBlocks.coefficientTailPower s.val h
  have hδA : 0 < δA := GoodBlocks.coefficientTailPower_pos s.property.1 s.property.2 hh
  let δ := min δA h
  have hδ : 0 < δ := lt_min hδA hh
  have hδ₁' : δ ≤ δA := min_le_left _ _
  have hδ₂' : δ ≤ δA := min_le_left _ _
  have hδh : δ ≤ h := min_le_right _ _
  obtain ⟨θ⟩ := DefinitionSanity.physicalCutoff_nonempty
  refine ⟨δ,hδ,fun βlo βhi hlo hle => ?_⟩
  obtain ⟨A₁,c₁,D₁,hA₁,hc₁,hD₁,hproper⟩ := hproper θ βlo βhi hlo hle
  obtain ⟨A₂,c₂,D₂,hA₂,hc₂,hD₂,hfull⟩ := hfull θ βlo βhi hlo hle
  let K := max K₁ K₂
  have hK : 16 ≤ K := hK₁.trans (le_max_left _ _)
  let B : ℝ := 4*(K : ℝ)+20
  have hB : 0 < B := by dsimp [B]; positivity
  let C₁ := 2*A₁*B^(q₁*h)
  let C₂ := A₂
  let C₀ := C₁+C₂
  let D₀ := D₁+D₂
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  have hC₂ : 0 < C₂ := by dsimp [C₂]; positivity
  have hC₀ : 0 < C₀ := add_pos hC₁ hC₂
  have hD₀ : 0 < D₀ := add_pos hD₁ hD₂
  let c := min c₁ (min c₂ (Real.log 2/128))
  have hc : 0 < c := lt_min hc₁ (lt_min hc₂
    (div_pos (Real.log_pos one_lt_two) (by norm_num)))
  have hcc₁ : c ≤ c₁ := min_le_left _ _
  have hcc₂ : c ≤ c₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hca : c ≤ Real.log 2/128 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨J,hJ,herror⟩ := error_absorption (2-s.val) δ (Real.log 2/32) hδ
    (div_pos (Real.log_pos one_lt_two) (by norm_num))
  rw [show Real.log 2/32/4 = Real.log 2/128 by ring] at herror
  let L := max K ⌈(2*B)^2⌉₊
  obtain ⟨Cₛ,hCₛ,hsmall⟩ := bounded_sizes_uniform s ε c δ hε hc hδ ⟨L,by
    have := le_max_left K ⌈(2*B)^2⌉₊
    omega⟩
  let C := 4*C₀+D₀*J+Cₛ+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,c,hC,hc,fun β hβ N _hN2 i j f g => ?_⟩
  intro p d
  have hfacf := ShortRangeResult.internal_correlationFactor_nonneg p N i.val f c δ d
  have hfacg := ShortRangeResult.internal_correlationFactor_nonneg p N j.val g c δ d
  let P := (1+(d : ℝ))^(-(2-s.val)+ε)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  by_cases hNK : (N : ℕ) ≤ L
  · obtain ⟨hm,hb⟩ := hsmall β N hNK i j f g
    refine ⟨hm,hb.trans ?_⟩
    change Cₛ*P*_ * _ ≤ C*P*_ * _
    gcongr
    dsimp [C]
    linarith only [hC₀,mul_nonneg hD₀.le hJ]
  have hKN : K ≤ (N : ℕ) := by
    have := le_max_left K ⌈(2*B)^2⌉₊
    omega
  have hN : 2 ≤ (N : ℕ) := by omega
  have hdN : d+1 ≤ (N : ℕ) := by
    have hi := i.isLt
    have hj := j.isLt
    dsimp [d,Riesz1.cyclicIndexDistance,Nat.dist]
    omega
  let r : ℝ := 1+(d : ℝ)
  have hr : 1 ≤ r := by dsimp [r]; exact le_add_of_nonneg_right (Nat.cast_nonneg d)
  have hdr : (d : ℝ) ≤ r := by dsimp [r]; linarith
  have hrN : r ≤ (N : ℝ) := by
    change 1+(d : ℝ) ≤ (N : ℝ)
    exact_mod_cast (show 1+d ≤ (N : ℕ) by omega)
  have hweight : r^(-(2-s.val)) ≤ P :=
    Real.rpow_le_rpow_of_exponent_le hr (by linarith only [hε])
  have hweight' : r^(-(2-s.val)+ε) ≤ P := le_rfl
  let k := max K ⌈4*r^ρ⌉₊
  obtain ⟨hk,hrk,hnlower,hnupper⟩ := rounded_scale r ρ hr hρ K (by omega)
  let n : ℕ+ := ⟨4*k,by positivity⟩
  have hnlo : r^ρ ≤ (n : ℝ) := hnlower
  have hnup : (n : ℝ) ≤ B*r^ρ := hnupper
  have hrn : r ≤ (n : ℝ) := by
    have hkr : (k : ℝ) ≤ (4*k : ℕ) := by push_cast; linarith only [Nat.cast_nonneg k (α := ℝ)]
    exact hrk.le.trans hkr
  have hnk : K ≤ (n : ℕ) := by dsimp [n,k]; omega
  have hm := ShortRangeResult.internal_gapSecondMoments p N i j f g
  refine ⟨hm,?_⟩
  change |covariance (fun X => f.val.1 (gap X i.val)) (fun X => g.val.1 (gap X j.val))
    (gibbsMeasure p N)| ≤ C*P*correlationFactor p N i.val f c δ d*correlationFactor p N j.val g c δ d
  suffices hbound : |covariance (fun X => f.val.1 (gap X i.val)) (fun X => g.val.1 (gap X j.val))
      (gibbsMeasure p N)| ≤ (4*C₀+D₀*J)*P*
        correlationFactor p N i.val f c δ d*correlationFactor p N j.val g c δ d by
    apply hbound.trans
    gcongr
    dsimp [C]
    linarith only [hCₛ]
  by_cases hnear : r ≤ (N : ℝ)^δ₀
  · have hlarge : (2*B)^2 ≤ (N : ℝ) := by
      have ht : ⌈(2*B)^2⌉₊ ≤ (N : ℕ) := by
        have := le_max_right K ⌈(2*B)^2⌉₊
        omega
      exact (Nat.le_ceil _).trans (by exact_mod_cast ht)
    have hhalf : 2*(n : ℕ) ≤ (N : ℕ) := by
      have ht := threshold_window_fit_internal hρpos hB (by positivity : 0 ≤ r)
        (by positivity : (0 : ℝ) < N) hnup hnear hlarge
      exact_mod_cast ht
    have hnN : (n : ℕ) ≤ (N : ℕ) := by omega
    have hdk : d < k := by exact_mod_cast (show (d : ℝ) < k by dsimp [r] at hrk; linarith)
    obtain ⟨a,u,v,hu,hv,hil,hir,_,_,hdist⟩ := pair_window N i j k hk hdk
    have hei (X : Riesz1.Configuration N) : gap X (a+u.val) = gap X i.val := by
      rw [internal_gap_label X (a+u.val),hu]
    have hej (X : Riesz1.Configuration N) : gap X (a+v.val) = gap X j.val := by
      rw [internal_gap_label X (a+v.val),hv]
    have hb := hproper β hβ N n (by have := n.pos; omega) ((le_max_left K₁ K₂).trans hnk)
      hhalf hnN a u hil hir v f g
    dsimp only at hb
    simp only [gapDerivativeNorm,hei,hej,hdist] at hb
    have ht := near_profile_internal hr hnlo hnup hρs ha₁ hpa₁ hB.le
    have hT : A₁*(n : ℝ)^(q₁*h)*
        (r^(-(2-s.val))+(n : ℝ)^(-(1/2 : ℝ))) ≤ C₀*P := by
      calc
        _ = A₁*((n : ℝ)^(q₁*h)*(r^(-(2-s.val))+(n : ℝ)^(-(1/2 : ℝ)))) := by ring
        _ ≤ A₁*(2*B^(q₁*h)*r^(-(2-s.val)+ε)) := mul_le_mul_of_nonneg_left ht hA₁.le
        _ = C₁*r^(-(2-s.val)+ε) := by dsimp [C₁]; ring
        _ ≤ _ := mul_le_mul (le_add_of_nonneg_right hC₂.le) hweight' (by positivity) hC₀.le
    exact internal_scale_finish (s := 2-s.val) (r := r) (L := (n : ℝ)) (δ := δ) (c := c)
      ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      hC₀.le hD₁.le hD₀.le hJ (Nat.cast_nonneg d) hr hdr hrn hδ hδ₁' hc₁.le hcc₁ hca
      (le_add_of_nonneg_right hD₂.le) hP hweight hT
      (herror d r n h (Nat.cast_nonneg d) hr hdr hrn hδh) hb
  · have hNupper : (N : ℝ) ≤ 1*r^(2*ρ) := by
      have ht := Real.rpow_le_rpow (by positivity : 0 ≤ (N : ℝ)^δ₀)
        (le_of_not_ge hnear) (by positivity : 0 ≤ 2*ρ)
      rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ N)] at ht
      have he : δ₀*(2*ρ) = 1 := by dsimp [δ₀]; field_simp
      simpa only [he,Real.rpow_one,one_mul] using ht
    have ht := profile_loss_internal (p := 2-s.val) hr
      (show (0 : ℝ) < N by positivity) hNupper ha₂ hpa₂ (by norm_num : (0 : ℝ) ≤ 1)
    simp only [Real.one_rpow,one_mul] at ht
    have hT : A₂*(N : ℝ)^(q₂*h)*r^(-(2-s.val)) ≤ C₀*P := by
      calc
        _ = A₂*((N : ℝ)^(q₂*h)*r^(-(2-s.val))) := by ring
        _ ≤ A₂*P := mul_le_mul_of_nonneg_left ht hA₂.le
        _ = C₂*P := rfl
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₁.le) hP
    have hb := hfull β hβ N ((le_max_right K₁ K₂).trans hKN) i j f g
    exact internal_scale_finish (s := 2-s.val) (r := r) (L := (N : ℝ)) (δ := δ) (c := c)
      ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      hC₀.le hD₂.le hD₀.le hJ (Nat.cast_nonneg d) hr hdr hrN hδ hδ₂' hc₂.le hcc₂ hca
      (le_add_of_nonneg_left hD₁.le) hP hweight hT
      (herror d r N h (Nat.cast_nonneg d) hr hdr hrN hδh) hb


/-- The fixed-temperature upper estimate in Theorem 1
of the paper, with its written `r = N^δ₀` regime switch. -/
theorem decay_gap_correlations_upper_by_threshold (hzeta : External.PeriodicZeta)
    (hRig : External.LongRangeRigidityLocallyUniform) :
  ∀ s : Riesz1.RieszExponent, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ β : InverseTemperature, ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ (i j : Fin (N : ℕ)) (f g : GapObservable),
        let p := ofLong β s
        let d := Riesz1.cyclicIndexDistance N i j
        ∃ hMom : GapSecondMoments p N i.val j.val f g,
        |gapCorrelation p N i.val j.val f.val.1 g.val.1 hMom.1 hMom.2.1| ≤
          C * (1 + (d : ℝ)) ^ (-(2-s.val) + ε) *
            correlationFactor p N i.val f c δ d * correlationFactor p N j.val g c δ d := by
  intro s ε hε
  obtain ⟨δ,hδ,h⟩ := decay_gap_correlations_upper_locallyUniform_by_threshold hzeta hRig s ε hε
  refine ⟨δ,hδ,fun β => ?_⟩
  obtain ⟨C,c,hC,hc,h⟩ := h β.val β.val β.property le_rfl
  exact ⟨C,c,hC,hc,h β ⟨le_rfl,le_rfl⟩⟩

end Riesz2.DecayLong.UpperCorrelations
