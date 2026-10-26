/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.ConvexEnergyMoments
public import Riesz2.HelfferSjostrand.ConditionalEnergyMomentsPart2
public import Riesz2.HelfferSjostrand.ProperMarginalChart

/-!
# Physical conditional energy moments

Convex scaling applied to the actual physical conditional laws in arbitrary
retained-coordinate charts, including point fibres. See Appendix A of the paper.
-/

public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal ContDiff

namespace Riesz2.ConditionalEnergyMoments
open ConvexEnergy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Internal form of Appendix A: subtracting an attained minimum
preserves the normalized Gibbs law and gives exponential and positive moments. -/
private theorem gibbs_moments_of_minimum (μ : Measure E) [μ.IsAddHaarMeasure]
    {Q : Set E} (hQ : MeasurableSet Q) {U : E → ℝ} (hUm : Measurable U)
    (hU : ConvexOn ℝ Q U) {y₀ : E} (hy₀ : y₀ ∈ Q) (hmin : IsMinOn U Q y₀)
    (h0 : (∫⁻ y in Q, ENNReal.ofReal (Real.exp (-U y)) ∂μ) ≠ 0)
    (ht : (∫⁻ y in Q, ENNReal.ofReal (Real.exp (-U y)) ∂μ) ≠ ⊤) :
    let ρ := AffineFibre.normalizedMeasure (μ.restrict Q)
      (fun y => ENNReal.ofReal (Real.exp (-U y))) h0 ht
    (∫⁻ y, ENNReal.ofReal (Real.exp ((U y - U y₀) / 2)) ∂ρ) ≤
        (2 : ℝ≥0∞) ^ Module.finrank ℝ E ∧
      Integrable (fun y => Real.exp ((U y - U y₀) / 2)) ρ ∧
      ∀ p : ℝ, 0 < p → Integrable (fun y => (U y - U y₀) ^ p) ρ ∧
        ∫ y, (U y - U y₀) ^ p ∂ρ ≤ (2 : ℝ) ^ Module.finrank ℝ E *
          (p / Real.exp 1) ^ p / (1 / 2 : ℝ) ^ p := by
  intro ρ
  let w : E → ℝ := fun y => U y - U y₀
  let c := ENNReal.ofReal (Real.exp (U y₀))
  have hc0 : c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have hct : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have he : (fun y => ENNReal.ofReal (Real.exp (-w y))) =
      fun y => c * ENNReal.ofReal (Real.exp (-U y)) := by
    funext y
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    congr 2
    dsimp [w]
    ring
  have hw0 : (∫⁻ y in Q, ENNReal.ofReal (Real.exp (-w y)) ∂μ) ≠ 0 := by
    rw [he, lintegral_const_mul _ (by fun_prop)]
    exact mul_ne_zero hc0 h0
  have hwt : (∫⁻ y in Q, ENNReal.ofReal (Real.exp (-w y)) ∂μ) ≠ ⊤ := by
    rw [he, lintegral_const_mul _ (by fun_prop)]
    exact ENNReal.mul_ne_top hct ht
  have hr : AffineFibre.normalizedMeasure (μ.restrict Q)
      (fun y => ENNReal.ofReal (Real.exp (-w y))) hw0 hwt = ρ := by
    simp only [he]
    exact normalizedMeasure_const_mul (μ.restrict Q) (by fun_prop) h0 ht hc0 hct
  have hw : ConvexOn ℝ Q w := hU.sub (concaveOn_const (U y₀) hU.1)
  have hwz : w y₀ = 0 := sub_self _
  have hwn : ∀ y ∈ Q, 0 ≤ w y := fun y hy => sub_nonneg.mpr (hmin hy)
  have hwm : Measurable w := hUm.sub_const _
  have hle := exponential_moment_le μ hQ hwm hw hy₀ hwz hw0 hwt
  have hi := integrable_exponential μ hQ hwm hw hy₀ hwz hw0 hwt
  rw [hr] at hle hi
  refine ⟨hle, hi, fun p hp => ?_⟩
  have hm := positive_moments μ hQ hwm hw hy₀ hwz hwn hw0 hwt hp
  change Integrable (fun y => w y ^ p) _ ∧ _ at hm
  rwa [hr] at hm



private theorem retained_chart_coordinates (n m : ℕ) (L : ℝ) (σ : Equiv.Perm (Fin (n + m + 1)))
    {y : EuclideanSpace ℝ (Fin (n + m + 1))} (hy : ∑ i, y i = L) :
    RetainedSimplex.chart n m L σ (RetainedSimplex.coordinates n m σ y) = y := by
  unfold RetainedSimplex.chart RetainedSimplex.coordinates
  rw [(RetainedSimplex.join n m).apply_symm_apply]
  have hs : LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ.symm y ∈
      AffineSimplex.massHyperplane (n + m) L := by
    change (∑ i, y (σ i)) = L
    rw [Equiv.sum_comp σ]
    exact hy
  rw [AffineSimplex.chart_coordinates _ _ hs]
  simp [← LinearIsometryEquiv.piLpCongrLeft_symm]

set_option backward.isDefEq.respectTransparency false in
/-- See Appendix A of the paper: every actual physical conditional has an attained
minimum and the sharp exponential energy moment. Every positive centered
energy moment is integrable and bounded uniformly in the retained data.
The exterior has `m + 1` gaps, hence free dimension `m`. -/
theorem physical_chart_energy_moments (p : Parameters) (n m : ℕ) (hn : 1 ≤ n) :
    ∃ W : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain (n + m).succPNat) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
          y ∈ gapAmbientDomain (n + m).succPNat},
        W y.val = physicalAmbientGapEnergy p (n + m).succPNat y) ∧
      ∀ (σ : Equiv.Perm (Fin (n + m + 1)))
        (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)),
        let Q := AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ i, x.val i)
        let U := fun z => p.val.1 * W (RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ (x.val, z))
        let ρ := ProperMarginalChart.conditionalMeasure p n m hn σ x
        ∃ z₀ ∈ Q, IsMinOn U Q z₀ ∧
          (∫⁻ z, ENNReal.ofReal (Real.exp ((U z - U z₀) / 2)) ∂ρ) ≤ (2 : ℝ≥0∞) ^ m ∧
          Integrable (fun z => Real.exp ((U z - U z₀) / 2)) ρ ∧
          ∀ r : ℝ, 0 < r → Integrable (fun z => (U z - U z₀) ^ r) ρ ∧
            ∫ z, (U z - U z₀) ^ r ∂ρ ≤ (2 : ℝ) ^ m *
              (r / Real.exp 1) ^ r / (1 / 2 : ℝ) ^ r := by
  classical
  obtain ⟨W, hW, hv, hmin⟩ := physical_fibre_minimum p (n + m).succPNat
    (by simp only [Nat.succPNat_coe]; omega)
  obtain ⟨V, _, hV, _, _, hc⟩ := RemovableGapBarrier.selected_gap_barrier_convex p
    (n + m).succPNat (by simp only [Nat.succPNat_coe]; omega)
  have hconv : ConvexOn ℝ (WithLp.ofLp ⁻¹' Riesz1.gapSimplex (n + m).succPNat) W :=
    hc.congr fun y hy => by
      have ha := PhysicalEnergy.simplex_subset_ambient (n + m).succPNat _ hy
      exact (hV ⟨y, ha⟩).trans (hv ⟨y, ha⟩).symm
  refine ⟨W, hW, hv, fun σ x => ?_⟩
  dsimp only
  let L : ℝ := ((n + m : ℕ) + 1) - ∑ i, x.val i
  let Q := AffineSimplex.chartDomain m L
  let c := fun z : EuclideanSpace ℝ (Fin m) =>
    RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ (x.val, z)
  let U := fun z => p.val.1 * W (c z)
  let ρ := ProperMarginalChart.conditionalMeasure p n m hn σ x
  have hQ : MeasurableSet Q := (AffineSimplex.isOpen_chartDomain m L).measurableSet
  have hdom (z : EuclideanSpace ℝ (Fin m)) : z ∈ Q ↔
      (x.val, z) ∈ RetainedSimplex.domain n m ((n + m : ℕ) + 1) := by
    exact (Set.ext_iff.mp (RetainedSimplex.fibre_domain n m _ x.property) z).symm
  have hs (z : EuclideanSpace ℝ (Fin m)) (hz : z ∈ Q) :
      WithLp.ofLp (c z) ∈ Riesz1.gapSimplex (n + m).succPNat := by
    have h := (RetainedSimplex.chart_mem_simplex n m _ σ _).mpr ((hdom z).mp hz)
    exact ⟨h.1, by simpa only [Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one, c] using h.2⟩
  have hximage : x.val ∈ Prod.fst '' RetainedSimplex.domain n m ((n + m : ℕ) + 1) := by
    rw [RetainedSimplex.fst_image_domain]
    exact x.property
  obtain ⟨⟨u, z⟩, hz, hu⟩ := hximage
  change u = x.val at hu
  subst u
  have hzQ : z ∈ Q := (hdom z).mpr hz
  let e := fun i : Fin n => σ (i.castAdd m).castSucc
  obtain ⟨y, hy, hyI, hym⟩ := hmin (Set.range e) (c z) (hs z hzQ)
  let q := RetainedSimplex.coordinates n m σ y
  have hqfst : q.1 = x.val := by
    ext i
    change (RetainedSimplex.coordinates n m σ y).1 i = _
    rw [RetainedSimplex.coordinates_retained]
    exact (hyI (e i) ⟨i, rfl⟩).trans
      (RetainedSimplex.chart_retained n m _ σ x.val z i)
  have hcinv : RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ q = y :=
    retained_chart_coordinates n m _ σ (by
      simpa only [Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using hy.2)
  have hczero : c q.2 = y := by
    change RetainedSimplex.chart n m _ σ (x.val, q.2) = y
    rw [← hqfst]
    exact hcinv
  have hqQ : q.2 ∈ Q := by
    apply (hdom _).mpr
    apply (RetainedSimplex.chart_mem_simplex n m _ σ _).mp
    change c q.2 ∈ AffineSimplex.massSimplex (n + m) ((n + m : ℕ) + 1)
    rw [hczero]
    exact ⟨hy.1, by simpa only [Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using hy.2⟩
  have hminU : IsMinOn U Q q.2 := by
    intro t ht
    have hmem : c t ∈ {v | WithLp.ofLp v ∈ Riesz1.gapSimplex (n + m).succPNat ∧
        ∀ i ∈ Set.range e, v i = c z i} := by
      refine ⟨hs t ht, ?_⟩
      rintro i ⟨j, rfl⟩
      rw [RetainedSimplex.chart_retained, RetainedSimplex.chart_retained]
    have hh : p.val.1 * W y ≤ p.val.1 * W (c t) := hym hmem
    change U q.2 ≤ U t
    simpa only [U, hczero] using hh
  have hUconv : ConvexOn ℝ Q U := by
    refine ⟨AffineSimplex.convex_chartDomain m L, fun a ha b hb u v hu hv' huv => ?_⟩
    have he : c (u • a + v • b) = u • c a + v • c b := by
      have hp : (u • (x.val, a) + v • (x.val, b)) = (x.val, u • a + v • b) := by
        ext i <;> simp [← add_smul, huv]
      have hh := RetainedSimplex.chart_convex_combination n m ((n + m : ℕ) + 1) σ (x.val, a) (x.val, b) huv
      rw [hp] at hh
      exact hh
    change p.val.1 * W (c (u • a + v • b)) ≤ _
    rw [he]
    exact (hconv.smul p.property.1.le).2 (hs a ha) (hs b hb) hu hv' huv
  have hUc : ContinuousOn U Q := continuousOn_const.mul
    (hW.continuousOn.comp
      ((RetainedSimplex.continuous_chart n m _ σ).comp (continuous_const.prodMk continuous_id)).continuousOn
      (fun t ht => PhysicalEnergy.simplex_subset_ambient _ _ (hs t ht)))
  let T := Q.indicator U
  have hTm : Measurable T := hUc.measurable_piecewise continuousOn_const hQ
  have heT : EqOn U T Q := fun t ht => (Set.indicator_of_mem ht U).symm
  have hTconv : ConvexOn ℝ Q T := hUconv.congr heT
  have hTmin : IsMinOn T Q q.2 := by
    intro t ht
    change T q.2 ≤ T t
    rw [← heT hqQ, ← heT ht]
    exact hminU ht
  have hden : (fun t => ProperMarginalChart.chartDensity p n m σ (x.val, t)) =
      Q.indicator (fun t => ENNReal.ofReal (Real.exp (-T t))) := by
    funext t
    by_cases ht : t ∈ Q
    · have hdm := (hdom t).mp ht
      have hsimplex := (RetainedSimplex.chart_mem_simplex n m _ σ _).mpr hdm
      simp only [ProperMarginalChart.chartDensity, indicator_of_mem hdm,
        ProperMarginalChart.density, dite_eq_left hsimplex, indicator_of_mem ht]
      rw [← hv ⟨c t, PhysicalEnergy.simplex_subset_ambient _ _ (hs t ht)⟩,
        ← heT ht]
      congr 2
      change -p.val.1 * W (c t) = -(p.val.1 * W (c t))
      ring
    · simp only [ProperMarginalChart.chartDensity, indicator_of_notMem ht,
        indicator_of_notMem (fun h => ht ((hdom t).mpr h))]
  obtain ⟨h0, htop⟩ := ProperMarginalChart.fibre_mass p n m hn σ x.property
  change (∫⁻ t, ProperMarginalChart.chartDensity p n m σ (x.val, t)) ≠ 0 at h0
  change (∫⁻ t, ProperMarginalChart.chartDensity p n m σ (x.val, t)) ≠ ⊤ at htop
  rw [hden, lintegral_indicator hQ] at h0 htop
  have hr : ρ = AffineFibre.normalizedMeasure (volume.restrict Q)
      (fun t => ENNReal.ofReal (Real.exp (-T t))) h0 htop := by
    dsimp only [ρ, ProperMarginalChart.conditionalMeasure]
    simp only [hden]
    exact AffineFibre.normalizedMeasure_indicator volume hQ _ h0 htop
  have hae : ∀ᵐ t ∂ρ, t ∈ Q := by
    rw [hr]
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hQ)
  have heae : T =ᵐ[ρ] U := hae.mono fun t ht => (heT ht).symm
  have hm := gibbs_moments_of_minimum volume hQ hTm hTconv hqQ hTmin h0 htop
  dsimp only at hm
  rw [← hr] at hm
  have hTeq : T q.2 = U q.2 := (heT hqQ).symm
  have hexpae : (fun t => Real.exp ((T t - T q.2) / 2)) =ᵐ[ρ]
      fun t => Real.exp ((U t - U q.2) / 2) :=
    heae.mono fun t ht => by dsimp only; rw [ht, hTeq]
  refine ⟨q.2, hqQ, hminU, ?_, hm.2.1.congr hexpae, fun r hr' => ?_⟩
  · change (∫⁻ t, ENNReal.ofReal (Real.exp ((U t - U q.2) / 2)) ∂ρ) ≤ _
    calc
      _ = ∫⁻ t, ENNReal.ofReal (Real.exp ((T t - T q.2) / 2)) ∂ρ :=
        lintegral_congr_ae (hexpae.symm.mono fun _ h => congrArg ENNReal.ofReal h)
      _ ≤ _ := by simpa only [finrank_euclideanSpace_fin] using hm.1
  · have haep : (fun t => (T t - T q.2) ^ r) =ᵐ[ρ] fun t => (U t - U q.2) ^ r :=
      heae.mono fun t ht => by dsimp only; rw [ht, hTeq]
    obtain ⟨hi, hb⟩ := hm.2.2 r hr'
    exact ⟨hi.congr haep, (integral_congr_ae haep).symm.trans_le (by simpa using hb)⟩



/-- The actual physical conditional is supported on its open exterior simplex,
for every retained point, including a zero-dimensional exterior chart. -/
theorem physical_conditional_support (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1)))
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    ∀ᵐ z ∂ProperMarginalChart.conditionalMeasure p n m hn σ x,
      z ∈ AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ i, x.val i) := by
  classical
  unfold ProperMarginalChart.conditionalMeasure AffineFibre.normalizedMeasure
  apply (ae_withDensity_iff (AffineFibre.measurable_normalizedDensity volume
    ((ProperMarginalChart.measurable_chartDensity p n m σ).comp measurable_prodMk_left) _ _)).mpr
  apply Filter.Eventually.of_forall
  intro z hz
  by_contra hnot
  have hd : (x.val, z) ∉ RetainedSimplex.domain n m ((n + m : ℕ) + 1) := by
    intro h
    exact hnot ((Set.ext_iff.mp (RetainedSimplex.fibre_domain n m _ x.property) z).mp h)
  simp only [AffineFibre.normalizedDensity, Function.comp_def, ProperMarginalChart.chartDensity,
    indicator_of_notMem hd, mul_zero, ne_eq, not_true_eq_false] at hz

set_option backward.isDefEq.respectTransparency false in
private theorem chart_trial_upper (p : Parameters) (n m : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : Equiv.Perm (Fin (n + m + 1)))
      (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
      (δ : ℝ), 0 < δ → (∀ i, δ ≤ x.val i) →
      δ ≤ ((n + m : ℕ) + 1) - ∑ i, x.val i →
      let L := ((n + m : ℕ) + 1) - ∑ i, x.val i
      let z : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun _ => L / (m + 1 : ℝ))
      z ∈ AffineSimplex.chartDomain m L ∧
        ∀ W : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ,
          (∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
            y ∈ gapAmbientDomain (n + m).succPNat},
            W y.val = physicalAmbientGapEnergy p (n + m).succPNat y) →
          p.val.1 * W (RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ (x.val, z)) ≤
            C * (1 + δ ^ (-p.val.2)) := by
  obtain ⟨C, hC, hbound⟩ := physical_energy_upper p (n + m).succPNat
    (by simp only [Nat.succPNat_coe]; omega)
  let N : ℝ := ((n + m : ℕ) + 1)
  have hN : 0 < N := by dsimp [N]; positivity
  have hN1 : 1 ≤ N := by dsimp [N]; linarith [Nat.cast_nonneg (α := ℝ) (n + m)]
  refine ⟨C * N ^ p.val.2, by positivity, fun σ x δ hδ hδx hδL => ?_⟩
  dsimp only
  let L : ℝ := N - ∑ i, x.val i
  let z : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun _ => L / (m + 1 : ℝ))
  have hL : 0 < L := hδ.trans_le hδL
  have hm : (0 : ℝ) < m + 1 := by positivity
  have hzsum : ∑ i, z i = m * (L / (m + 1 : ℝ)) := by simp [z]
  have heL : L - ∑ i, z i = L / (m + 1 : ℝ) := by
    rw [hzsum]
    field_simp
    ring
  have hz : z ∈ AffineSimplex.chartDomain m L := by
    refine ⟨fun _ => div_pos hL hm, ?_⟩
    have hh : 0 < L / (m + 1 : ℝ) := div_pos hL hm
    linarith [heL]
  refine ⟨hz, fun W hv => ?_⟩
  let y := RetainedSimplex.chart n m N σ (x.val, z)
  have hdomain : (x.val, z) ∈ RetainedSimplex.domain n m N :=
    (Set.ext_iff.mp (RetainedSimplex.fibre_domain n m N x.property) z).mpr hz
  have hys := (RetainedSimplex.chart_mem_simplex n m N σ _).mpr hdomain
  have hy : WithLp.ofLp y ∈ Riesz1.gapSimplex (n + m).succPNat := by
    refine ⟨hys.1, ?_⟩
    simpa only [N, Nat.succPNat_coe, Nat.cast_succ] using hys.2
  have hmN : (m + 1 : ℝ) ≤ N := by dsimp [N]; push_cast; linarith
  have hlow : δ / N ≤ L / (m + 1 : ℝ) := by
    apply (div_le_div_iff₀ hN hm).mpr
    exact (mul_le_mul_of_nonneg_left hmN hδ.le).trans
      (mul_le_mul_of_nonneg_right hδL hN.le)
  have hylo (i : Fin (n + m + 1)) : δ / N ≤ y i := by
    change δ / N ≤ AffineSimplex.chart (n + m) N (RetainedSimplex.join n m (x.val, z)) (σ.symm i)
    refine Fin.lastCases ?_ (fun j => ?_) (σ.symm i)
    · rw [AffineSimplex.chart_last, RetainedSimplex.sum_join]
      have hh : N - ((∑ i, x.val i) + ∑ i, z i) = L - ∑ i, z i := by dsimp [L]; ring
      rw [hh, heL]
      exact hlow
    · rw [AffineSimplex.chart_castSucc]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · rw [RetainedSimplex.join_left]
        exact (div_le_self hδ.le hN1).trans (hδx j)
      · rw [RetainedSimplex.join_right]
        exact hlow
  have hb := hbound y hy (δ / N) (div_pos hδ hN) hylo
  rw [← hv ⟨y, PhysicalEnergy.simplex_subset_ambient _ _ hy⟩] at hb
  have hepow : (δ / N) ^ (-p.val.2) = N ^ p.val.2 * δ ^ (-p.val.2) := by
    rw [Real.div_rpow hδ.le hN.le, Real.rpow_neg hN.le, div_inv_eq_mul]
    ring
  rw [hepow] at hb
  have hh : C * (N ^ p.val.2 * δ ^ (-p.val.2)) ≤
      C * N ^ p.val.2 * (1 + δ ^ (-p.val.2)) := by
    nlinarith [show 0 ≤ C * N ^ p.val.2 by positivity]
  exact hb.trans hh



private theorem rpow_sum_bound {a b r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r) :
    (a + b) ^ r ≤ (2 : ℝ) ^ r * (a ^ r + b ^ r) := by
  have hab : a + b ≤ 2 * max a b := by linarith [le_max_left a b, le_max_right a b]
  calc
    _ ≤ (2 * max a b) ^ r := Real.rpow_le_rpow (add_nonneg ha hb) hab hr
    _ = 2 ^ r * max (a ^ r) (b ^ r) := by
      rw [Real.mul_rpow (by norm_num) (le_max_of_le_left ha), Real.rpow_max ha hb hr]
    _ ≤ _ := mul_le_mul_of_nonneg_left (max_le
      (by linarith [Real.rpow_nonneg hb r]) (by linarith [Real.rpow_nonneg ha r])) (by positivity)

set_option backward.isDefEq.respectTransparency false in
/-- See Appendix A of the paper, all clauses for the actual physical exterior law.
Constants precede the retained labels and data. Every positive lower bound on
active gaps and exterior mass is allowed, in particular their minimum `δ`.
There are `m + 1` exterior gaps, so the exponential factor is exactly `2 ^ m`.
All inverse moments are extended integrals. Their integrability is concluded. -/
theorem physical_conditional_moments (p : Parameters) (n m : ℕ) (hn : 1 ≤ n) :
    ∃ W : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain (n + m).succPNat) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
          y ∈ gapAmbientDomain (n + m).succPNat},
        W y.val = physicalAmbientGapEnergy p (n + m).succPNat y) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ (σ : Equiv.Perm (Fin (n + m + 1)))
        (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)),
        let Q := AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ i, x.val i)
        let U := fun z => p.val.1 * W (RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ (x.val, z))
        let ρ := ProperMarginalChart.conditionalMeasure p n m hn σ x
        ∃ z₀ ∈ Q, IsMinOn U Q z₀ ∧
          (∫⁻ z, ENNReal.ofReal (Real.exp ((U z - U z₀) / 2)) ∂ρ) ≤ (2 : ℝ≥0∞) ^ m ∧
          Integrable (fun z => Real.exp ((U z - U z₀) / 2)) ρ ∧
          ∀ δ : ℝ, 0 < δ → (∀ i, δ ≤ x.val i) →
            δ ≤ ((n + m : ℕ) + 1) - ∑ i, x.val i →
            U z₀ ≤ C * (1 + δ ^ (-p.val.2)) ∧
            ∀ a : Fin (n + m + 1),
              Integrable (fun z =>
                (RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ (x.val, z) a) ^ (-p.val.2 - 2)) ρ ∧
              (∫⁻ z, ENNReal.ofReal
                ((RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ (x.val, z) a) ^ (-p.val.2 - 2)) ∂ρ) ≤
                ENNReal.ofReal (C * (1 + δ ^ (-p.val.2 - 2))) := by
  obtain ⟨W, hW, hv, hmom⟩ := physical_chart_energy_moments p n m hn
  obtain ⟨Cu, hCu, htrial⟩ := chart_trial_upper p n m hn
  obtain ⟨C₀, hC₀, hlower⟩ := physical_inverse_gap_bound p (n + m).succPNat
    (by simp only [Nat.succPNat_coe]; omega)
  have hβ : 0 < p.val.1 := p.property.1
  let r : ℝ := (p.val.2 + 2) / p.val.2
  have hr : 0 < r := div_pos (by linarith [p.property.2.1]) p.property.2.1
  let A : ℝ := (2 : ℝ) ^ r / (2 * p.val.1) ^ r
  let M : ℝ := (2 : ℝ) ^ m * (r / Real.exp 1) ^ r / (1 / 2 : ℝ) ^ r
  let B : ℝ := (Cu + C₀) ^ r * 2 ^ r
  have hA : 0 < A := by dsimp [A]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  let C : ℝ := Cu + A * (M + B) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hCuC : Cu ≤ C := by dsimp [C]; linarith [show 0 ≤ A * (M + B) by positivity]
  have hAC : A * (M + B) ≤ C := by dsimp [C]; linarith
  refine ⟨W, hW, hv, C, hC, fun σ x => ?_⟩
  dsimp only
  let Q := AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ i, x.val i)
  let c := fun z : EuclideanSpace ℝ (Fin m) =>
    RetainedSimplex.chart n m ((n + m : ℕ) + 1) σ (x.val, z)
  let U := fun z => p.val.1 * W (c z)
  let ρ := ProperMarginalChart.conditionalMeasure p n m hn σ x
  obtain ⟨z₀, hz₀, hmin, he, hei, hp⟩ := hmom σ x
  change z₀ ∈ Q at hz₀
  change IsMinOn U Q z₀ at hmin
  have hs (z : EuclideanSpace ℝ (Fin m)) (hz : z ∈ Q) :
      WithLp.ofLp (c z) ∈ Riesz1.gapSimplex (n + m).succPNat := by
    have hd := (Set.ext_iff.mp (RetainedSimplex.fibre_domain n m _ x.property) z).mpr hz
    have hy := (RetainedSimplex.chart_mem_simplex n m _ σ _).mpr hd
    exact ⟨hy.1, by simpa only [c, Nat.succPNat_coe, Nat.cast_succ] using hy.2⟩
  have hlow (z : EuclideanSpace ℝ (Fin m)) (hz : z ∈ Q) :
      0 ≤ U z + C₀ ∧ ∀ a, (c z a) ^ (-p.val.2) ≤ (U z + C₀) / (2 * p.val.1) := by
    have hh := hlower (c z) (hs z hz)
    dsimp only at hh
    rwa [← hv ⟨c z, PhysicalEnergy.simplex_subset_ambient _ _ (hs z hz)⟩] at hh
  have hae : ∀ᵐ z ∂ρ, z ∈ Q := physical_conditional_support p n m hn σ x
  have : IsProbabilityMeasure ρ := ProperMarginalChart.conditionalMeasure_probability p n m hn σ x
  have hbn : 0 ≤ U z₀ + C₀ := (hlow z₀ hz₀).1
  let w := fun z => U z - U z₀
  have hwn (z : EuclideanSpace ℝ (Fin m)) (hz : z ∈ Q) : 0 ≤ w z :=
    sub_nonneg.mpr (hmin hz)
  obtain ⟨hwi, hwm⟩ := hp r hr
  change Integrable (fun z => w z ^ r) ρ at hwi
  change (∫ z, w z ^ r ∂ρ) ≤ M at hwm
  refine ⟨z₀, hz₀, hmin, he, hei, fun δ hδ hδx hδL => ?_⟩
  obtain ⟨htQ, htu⟩ := htrial σ x δ hδ hδx hδL
  have hb : U z₀ ≤ Cu * (1 + δ ^ (-p.val.2)) :=
    (hmin htQ).trans (htu W hv)
  refine ⟨hb.trans (mul_le_mul_of_nonneg_right hCuC (by positivity)), fun a => ?_⟩
  have hbshift : U z₀ + C₀ ≤ (Cu + C₀) * (1 + δ ^ (-p.val.2)) := by
    have hd := Real.rpow_nonneg hδ.le (-p.val.2)
    nlinarith [mul_nonneg hC₀.le hd]
  have hbp : (U z₀ + C₀) ^ r ≤ B * (1 + δ ^ (-p.val.2 - 2)) := by
    calc
      _ ≤ ((Cu + C₀) * (1 + δ ^ (-p.val.2))) ^ r := Real.rpow_le_rpow hbn hbshift hr.le
      _ = (Cu + C₀) ^ r * (1 + δ ^ (-p.val.2)) ^ r :=
        Real.mul_rpow (by positivity) (by positivity)
      _ ≤ (Cu + C₀) ^ r * (2 ^ r * (1 ^ r + (δ ^ (-p.val.2)) ^ r)) :=
        mul_le_mul_of_nonneg_left (rpow_sum_bound (by norm_num) (by positivity) hr.le) (by positivity)
      _ = _ := by
        rw [Real.one_rpow, ← Real.rpow_mul hδ.le]
        have hex : -p.val.2 * r = -p.val.2 - 2 := by dsimp [r]; field_simp [ne_of_gt p.property.2.1]; ring
        rw [hex]
        dsimp [B]
        ring
  have hinv (z : EuclideanSpace ℝ (Fin m)) (hz : z ∈ Q) :
      (c z a) ^ (-p.val.2 - 2) ≤ A * (w z ^ r + (U z₀ + C₀) ^ r) := by
    have hypos := (hs z hz).1 a
    have hex : -p.val.2 * r = -p.val.2 - 2 := by dsimp [r]; field_simp [ne_of_gt p.property.2.1]; ring
    calc
      _ = ((c z a) ^ (-p.val.2)) ^ r := by rw [← Real.rpow_mul hypos.le, hex]
      _ ≤ ((U z + C₀) / (2 * p.val.1)) ^ r :=
        Real.rpow_le_rpow (by positivity) ((hlow z hz).2 a) hr.le
      _ = (w z + (U z₀ + C₀)) ^ r / (2 * p.val.1) ^ r := by
        rw [Real.div_rpow (hlow z hz).1 (by positivity)]
        congr 2
        dsimp [w]
        ring
      _ ≤ (2 ^ r * (w z ^ r + (U z₀ + C₀) ^ r)) / (2 * p.val.1) ^ r :=
        div_le_div_of_nonneg_right (rpow_sum_bound (hwn z hz) hbn hr.le) (by positivity)
      _ = _ := by dsimp [A]; ring
  have hmajor : Integrable (fun z => A * (w z ^ r + (U z₀ + C₀) ^ r)) ρ :=
    (hwi.add (integrable_const _)).const_mul A
  have hi : Integrable (fun z => (c z a) ^ (-p.val.2 - 2)) ρ := by
    have hc : Continuous c := (RetainedSimplex.continuous_chart n m _ σ).comp
      (continuous_const.prodMk continuous_id)
    have hmeas : Measurable (fun z => (c z a) ^ (-p.val.2 - 2)) :=
      ((EuclideanSpace.proj (𝕜 := ℝ) a).continuous.comp hc).measurable.pow_const _
    apply hmajor.mono' hmeas.aestronglyMeasurable
    filter_upwards [hae] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg ((hs z hz).1 a).le _)]
    exact hinv z hz
  have hint : (∫ z, (c z a) ^ (-p.val.2 - 2) ∂ρ) ≤ C * (1 + δ ^ (-p.val.2 - 2)) := by
    calc
      _ ≤ ∫ z, A * (w z ^ r + (U z₀ + C₀) ^ r) ∂ρ :=
        integral_mono_ae hi hmajor (hae.mono fun z hz => hinv z hz)
      _ = A * ((∫ z, w z ^ r ∂ρ) + (U z₀ + C₀) ^ r) := by
        rw [integral_const_mul, integral_add hwi (integrable_const _), integral_const]
        simp
      _ ≤ A * (M + B * (1 + δ ^ (-p.val.2 - 2))) :=
        mul_le_mul_of_nonneg_left (add_le_add hwm hbp) hA.le
      _ ≤ A * (M + B) * (1 + δ ^ (-p.val.2 - 2)) := by
        nlinarith [mul_nonneg hM (Real.rpow_nonneg hδ.le (-p.val.2 - 2))]
      _ ≤ _ := mul_le_mul_of_nonneg_right hAC (by positivity)
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (hae.mono fun z hz => Real.rpow_nonneg ((hs z hz).1 a).le _)]
  exact ENNReal.ofReal_le_ofReal hint

end Riesz2.ConditionalEnergyMoments
