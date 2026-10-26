/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.ConditionalScoresPart2
public import Riesz2.Bridges.ConvexMeasureInputs
public import Riesz2.ToMathlib.AffineMetricTransport
public import Riesz2.DecayLong.ConditionalForces
public import Riesz2.DecayShort.ExceptionalEvent

/-!
# Conditional score variances on the physical exterior chart

The affine exterior coordinates in Subsection 4.4 have their
actual pullback Hessian. All normal derivatives are those of the ambient energy, and all integrals use the existing physical conditional law.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators ContDiff InnerProductSpace

namespace Riesz2.DecayShort.ConditionalScores

set_option backward.isDefEq.respectTransparency false in
/-- Internal metric fact for Subsection 4.4: the exterior chart differential
vanishes on retained coordinates and cannot decrease the Euclidean norm. -/
theorem internal_exterior_chart_metric (n m : ℕ) (x : EuclideanSpace ℝ (Fin n)) (L : ℝ) :
    ∃ C : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin (n + m + 1)),
      (∀ z, RetainedSimplex.chart n m L (Equiv.refl _) (x,z) =
        C z + RetainedSimplex.chart n m L (Equiv.refl _) (x,0)) ∧
      (∀ z (i : Fin n), C z (Fin.castLE (by omega) i) = 0) ∧
      (∀ z, ‖z‖ ^ 2 ≤ ‖C z‖ ^ 2) := by
  obtain ⟨C,hC⟩ := internal_exterior_chart_affine n m (Equiv.refl _) x L
  refine ⟨C,hC,?_,?_⟩
  · intro z i
    have h := congrArg (fun y : EuclideanSpace ℝ (Fin (n + m + 1)) =>
      y ((i.castAdd m).castSucc)) (hC z)
    simp only [PiLp.add_apply] at h
    change AffineSimplex.chart (n + m) L (RetainedSimplex.join n m (x,z))
      (i.castAdd m).castSucc = C z (i.castAdd m).castSucc +
        AffineSimplex.chart (n + m) L (RetainedSimplex.join n m (x,0))
          (i.castAdd m).castSucc at h
    rw [AffineSimplex.chart_castSucc, AffineSimplex.chart_castSucc,
      RetainedSimplex.join_left, RetainedSimplex.join_left] at h
    change x i = C z ((i.castAdd m).castSucc) + x i at h
    have hi : Fin.castLE (by omega) i = (i.castAdd m).castSucc := Fin.ext rfl
    rw [hi]
    linarith
  · intro z
    have hcoord (i : Fin m) : C z ((i.natAdd n).castSucc) = z i := by
      have h := congrArg (fun y : EuclideanSpace ℝ (Fin (n + m + 1)) =>
        y ((i.natAdd n).castSucc)) (hC z)
      change AffineSimplex.chart (n + m) L (RetainedSimplex.join n m (x,z))
        (i.natAdd n).castSucc = C z (i.natAdd n).castSucc +
          AffineSimplex.chart (n + m) L (RetainedSimplex.join n m (x,0))
            (i.natAdd n).castSucc at h
      rw [AffineSimplex.chart_castSucc, AffineSimplex.chart_castSucc,
        RetainedSimplex.join_right, RetainedSimplex.join_right] at h
      simp only [PiLp.zero_apply] at h
      linarith
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_castSucc, Fin.sum_univ_add]
    have ht : 0 ≤ ∑ i : Fin n, C z (i.castAdd m).castSucc ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    simp only [hcoord]
    linarith [sq_nonneg (C z (Fin.last (n + m)))]

set_option backward.isDefEq.respectTransparency false in
private theorem conditional_density (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (U : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ)
    (hv : ∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
        y ∈ gapAmbientDomain (n + m).succPNat},
      U y.val = p.val.1 * physicalAmbientGapEnergy p (n + m).succPNat y)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    let Ω := AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ i, x.val i)
    let V := fun z => U (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z))
    ProperMarginalChart.conditionalMeasure p n m hn (Equiv.refl _) x =
      (volume.restrict Ω).withDensity
        (fun z => ENNReal.ofReal (Real.exp (-V z) / ∫ y in Ω, Real.exp (-V y))) := by
  classical
  intro Ω V
  have hΩ := (AffineSimplex.isOpen_chartDomain m
    (((n + m : ℕ) + 1) - ∑ i, x.val i)).measurableSet
  have hd : (fun z => ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x.val,z)) =
      Ω.indicator (fun z => ENNReal.ofReal (Real.exp (-V z))) := by
    funext z
    have hf := Set.ext_iff.mp (RetainedSimplex.fibre_domain n m
      ((n + m : ℕ) + 1) x.property) z
    by_cases hz : z ∈ Ω
    · have hq : (x.val,z) ∈ RetainedSimplex.domain n m ((n + m : ℕ) + 1) := hf.mpr hz
      have hs := (RetainedSimplex.chart_mem_simplex n m ((n + m : ℕ) + 1)
        (Equiv.refl _) _).mpr hq
      simp only [ProperMarginalChart.chartDensity, indicator_of_mem hq,
        ProperMarginalChart.density, dite_eq_left hs, indicator_of_mem hz]
      rw [show V z = p.val.1 * physicalAmbientGapEnergy p (n + m).succPNat
        ⟨_, ProperMarginalChart.simplex_ambient _ hs⟩ from hv ⟨_, _⟩]
      congr 2
      ring
    · have hq : (x.val,z) ∉ RetainedSimplex.domain n m ((n + m : ℕ) + 1) :=
        fun hh => hz (hf.mp hh)
      simp only [ProperMarginalChart.chartDensity, indicator_of_notMem hq,
        indicator_of_notMem hz]
  obtain ⟨h0,ht⟩ := ProperMarginalChart.fibre_mass p n m hn (Equiv.refl _) x.property
  change (∫⁻ z, ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x.val,z)) ≠ 0 at h0
  change (∫⁻ z, ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x.val,z)) ≠ ⊤ at ht
  rw [hd, lintegral_indicator hΩ] at h0 ht
  have hρ : ProperMarginalChart.conditionalMeasure p n m hn (Equiv.refl _) x =
      AffineFibre.normalizedMeasure (volume.restrict Ω)
        (fun z => ENNReal.ofReal (Real.exp (-V z))) h0 ht := by
    unfold ProperMarginalChart.conditionalMeasure
    simp only [hd]
    exact AffineFibre.normalizedMeasure_indicator volume hΩ _ h0 ht
  have hm : AEMeasurable (fun z => ENNReal.ofReal (Real.exp (-V z))) (volume.restrict Ω) := by
    have hw0 : AEMeasurable
        (fun z => ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x.val,z)) volume :=
      ((ProperMarginalChart.measurable_chartDensity p n m (Equiv.refl _)).comp
        measurable_prodMk_left).aemeasurable
    have hw := hw0.restrict (s := Ω)
    rw [hd] at hw
    exact hw.congr (by filter_upwards [ae_restrict_mem hΩ] with z hz; exact indicator_of_mem hz _)
  have hZ := integral_toReal hm (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)
  simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hZ
  have hZpos : 0 < ∫ z in Ω, Real.exp (-V z) := by
    rw [hZ]
    exact ENNReal.toReal_pos h0 ht
  have hmass : (∫⁻ z in Ω, ENNReal.ofReal (Real.exp (-V z))) =
      ENNReal.ofReal (∫ z in Ω, Real.exp (-V z)) := by
    rw [hZ, ENNReal.ofReal_toReal ht]
  rw [hρ]
  unfold AffineFibre.normalizedMeasure AffineFibre.normalizedDensity
  rw [hmass]
  congr 1
  funext z
  rw [← ENNReal.ofReal_inv_of_pos hZpos,
    ← ENNReal.ofReal_mul (inv_nonneg.mpr hZpos.le), div_eq_inv_mul]

set_option backward.isDefEq.respectTransparency false in
/-- Internal curvature input for Subsection 4.4, valid for every smooth
realization of beta times the physical energy. -/
theorem internal_ambient_curvature (p : Parameters) (n m : ℕ) (hN : 3 ≤ n + m + 1)
    (U : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ)
    (hv : ∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
        y ∈ gapAmbientDomain (n + m).succPNat},
      U y.val = p.val.1 * physicalAmbientGapEnergy p (n + m).succPNat y)
    (y : EuclideanSpace ℝ (Fin (n + m + 1)))
    (hy : WithLp.ofLp y ∈ Riesz1.gapSimplex (n + m).succPNat)
    (v : EuclideanSpace ℝ (Fin (n + m + 1))) :
    p.val.1 * (2 * (p.val.2 * (p.val.2 + 1))) *
      (∑ a, y a ^ (-p.val.2 - 2) * (v a) ^ 2) ≤ fderiv ℝ (fderiv ℝ U) y v v := by
  obtain ⟨_, _, W, hW, hw, _, _, _, hl, _⟩ :=
    PhysicalEnergy.restriction_and_derivatives p (n + m).succPNat (by simp; omega)
  change (EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ) at W
  simp only [Nat.succPNat_coe] at hW hw hl
  have hya : y ∈ gapAmbientDomain (n + m).succPNat :=
    PhysicalEnergy.simplex_subset_ambient _ _ hy
  have he : U =ᶠ[𝓝 y] fun z => p.val.1 * W z := by
    filter_upwards [(PhysicalEnergy.isOpen_gapAmbientDomain _).mem_nhds hya] with z hz
    rw [hv ⟨z,hz⟩, hw ⟨z,hz⟩]
  rw [he.fderiv.fderiv_eq, PhysicalCollision.internal_hessian_const_mul
    ((hW.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain _).mem_nhds hya)).of_le
      (by norm_num))]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hl _ hy v hN) p.property.1.le

/-- Internal affine chain rule for the actual exterior score in Subsection 4.4. -/
theorem internal_score_differential {E D : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup D] [InnerProductSpace ℝ D] [CompleteSpace D]
    (C : D →L[ℝ] E) (b v : E) (a : ℝ) (U : E → ℝ) (z h : D)
    (hU : ContDiffAt ℝ 2 U (C z + b)) :
    inner ℝ (gradient (fun y => a * fderiv ℝ U (C y + b) v) z) h =
      a * fderiv ℝ (fderiv ℝ U) (C z + b) v (C h) := by
  have hd := ((hU.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.comp z (C.hasFDerivAt.add_const b)
  have hF := (hd.clm_apply (hasFDerivAt_const v z)).const_mul a
  rw [inner_gradient_left]
  erw [hF.fderiv]
  simp only [smul_apply, add_apply, ContinuousLinearMap.comp_apply, zero_apply,
    map_zero, zero_add, ContinuousLinearMap.flip_apply, smul_eq_mul]
  rw [hU.isSymmSndFDerivAt (by norm_num) (C h) v]

set_option backward.isDefEq.respectTransparency false in
private theorem physical_bl (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (hN : 3 ≤ n + m + 1) (hm : 1 ≤ m)
    (U : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ)
    (hU : ContDiffOn ℝ ∞ U (gapAmbientDomain (n + m).succPNat))
    (hv : ∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
        y ∈ gapAmbientDomain (n + m).succPNat},
      U y.val = p.val.1 * physicalAmbientGapEnergy p (n + m).succPNat y)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (F : EuclideanSpace ℝ (Fin m) → ℝ)
    (hF : Riesz1.WeightedSobolev.IsWeightedH1
      (ProperMarginalChart.conditionalMeasure p n m hn (Equiv.refl _) x)
      (AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ i, x.val i)) F (gradient F)) :
    let V := fun z => U (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z))
    let μ := ProperMarginalChart.conditionalMeasure p n m hn (Equiv.refl _) x
    (∫ z, (F z - ∫ y, F y ∂μ) ^ 2 ∂μ) ≤
      ∫ z, sSup (Set.range fun h : EuclideanSpace ℝ (Fin m) =>
        2 * inner ℝ (gradient F z) h - fderiv ℝ (fderiv ℝ V) z h h) ∂μ ∧
    Integrable (fun z => sSup (Set.range fun h : EuclideanSpace ℝ (Fin m) =>
      2 * inner ℝ (gradient F z) h - fderiv ℝ (fderiv ℝ V) z h h)) μ := by
  classical
  intro V μ
  let Ω := AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ i, x.val i)
  let c := fun z => RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)
  obtain ⟨C,hc,_,hnorm⟩ := internal_exterior_chart_metric n m x.val ((n + m : ℕ) + 1)
  have hce : c = fun z => C z + c 0 := funext hc
  have hs (z) (hz : z ∈ Ω) : WithLp.ofLp (c z) ∈ Riesz1.gapSimplex (n + m).succPNat :=
    PhysicalFibres.configuration_mem_simplex n m (Equiv.refl _) x ⟨z,hz⟩
  have ha (z) (hz : z ∈ Ω) : c z ∈ gapAmbientDomain (n + m).succPNat :=
    PhysicalEnergy.simplex_subset_ambient _ _ (hs z hz)
  have hUa (z) (hz : z ∈ Ω) : ContDiffAt ℝ 2 U (c z) :=
    (hU.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain _).mem_nhds (ha z hz))).of_le
      (by norm_num)
  have hV : ContDiffOn ℝ 2 V Ω := by
    apply (hU.of_le (by norm_num)).comp _ ha
    rw [hce]
    exact (C.contDiff.add contDiff_const).contDiffOn
  have hH (z) (hz : z ∈ Ω) (h) : fderiv ℝ (fderiv ℝ V) z h h =
      fderiv ℝ (fderiv ℝ U) (c z) (C h) (C h) := by
    change fderiv ℝ (fderiv ℝ (fun z => U (c z))) z h h = _
    rw [hce]
    exact AffineMetricTransport.hessian_comp_affine C (c 0)
      (by rw [← hc]; exact hUa z hz) h h
  let α := p.val.1 * (2 * (p.val.2 * (p.val.2 + 1)))
  let κ := α * ((n + m + 1 : ℕ) : ℝ) ^ (-p.val.2 - 2)
  have hα : 0 < α := by
    dsimp [α]
    have hβ := p.property.1
    have hs := p.property.2.1
    positivity
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hlow (z) (hz : z ∈ Ω) (h) : κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) z h h := by
    rw [hH z hz]
    have hsum : ((n + m + 1 : ℕ) : ℝ) ^ (-p.val.2 - 2) * ‖C h‖ ^ 2 ≤
        ∑ a, c z a ^ (-p.val.2 - 2) * (C h a) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply Real.rpow_le_rpow_of_nonpos ((hs z hz).1 a) _ (by linarith [p.property.2.1])
      exact (Finset.single_le_sum (fun j _ => ((hs z hz).1 j).le)
        (Finset.mem_univ a)).trans_eq (hs z hz).2
    calc
      _ ≤ κ * ‖C h‖ ^ 2 := mul_le_mul_of_nonneg_left (hnorm h) hκ.le
      _ ≤ α * (∑ a, c z a ^ (-p.val.2 - 2) * (C h a) ^ 2) := by
        dsimp only [κ]
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hsum hα.le
      _ ≤ _ := internal_ambient_curvature p n m hN U hv (c z) (hs z hz) (C h)
  have hne : Ω.Nonempty := by
    have hx : x.val ∈ Prod.fst '' RetainedSimplex.domain n m ((n + m : ℕ) + 1) := by
      rw [RetainedSimplex.fst_image_domain]
      exact x.property
    obtain ⟨⟨a,z⟩, hz, he⟩ := hx
    change a = x.val at he
    subst a
    exact ⟨z, (Set.ext_iff.mp (RetainedSimplex.fibre_domain n m _ x.property) z).mp hz⟩
  have hb := euclidean_brascamp_lieb hm (AffineSimplex.isBounded_chartDomain m _)
    (AffineSimplex.isOpen_chartDomain m _) hne (AffineSimplex.convex_chartDomain m _)
    hV hκ hlow μ (conditional_density p n m hn U hv x)
  exact ⟨(hb.2.2.2.1 F (gradient F) hF).1, (hb.2.2.2.1 F (gradient F) hF).2.1⟩

/-- See Subsection 4.4 of the paper, the physical Brascamp–Lieb inequality for every
ambient score on every positive exterior chart of positive dimension.
The score's weighted H¹ membership and the inverse-energy integrability
are conclusions. -/
theorem physical_scores_brascamp_lieb (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (hN : 3 ≤ n + m + 1) (hm : 1 ≤ m) :
    ∃ U : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain (n + m).succPNat) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
          y ∈ gapAmbientDomain (n + m).succPNat},
        U y.val = p.val.1 * physicalAmbientGapEnergy p (n + m).succPNat y) ∧
      ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
        (v : EuclideanSpace ℝ (Fin (n + m + 1))),
        let F := fun z => p.val.1⁻¹ * fderiv ℝ U
          (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) v
        let V := fun z => U (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z))
        let μ := ProperMarginalChart.conditionalMeasure p n m hn (Equiv.refl _) x
        Riesz1.WeightedSobolev.IsWeightedH1 μ
          (AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ i, x.val i)) F (gradient F) ∧
        (∫ z, (F z - ∫ y, F y ∂μ) ^ 2 ∂μ) ≤
          ∫ z, sSup (Set.range fun h : EuclideanSpace ℝ (Fin m) =>
            2 * inner ℝ (gradient F z) h - fderiv ℝ (fderiv ℝ V) z h h) ∂μ ∧
        Integrable (fun z => sSup (Set.range fun h : EuclideanSpace ℝ (Fin m) =>
          2 * inner ℝ (gradient F z) h - fderiv ℝ (fderiv ℝ V) z h h)) μ := by
  obtain ⟨U,hU,hv,hF⟩ := physical_scores_weightedH1 p n m hn
  exact ⟨U,hU,hv,fun x v => ⟨hF (Equiv.refl _) x v,
    physical_bl p n m hn hN hm U hU hv x _ (hF (Equiv.refl _) x v)⟩⟩

private theorem bilinear_coordinates {k : ℕ}
    (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ)
    (u v : EuclideanSpace ℝ (Fin k)) :
    A u v = ∑ a, A u (EuclideanSpace.single a 1) * v a := by
  have hv : v = ∑ a, v a • EuclideanSpace.single a (1 : ℝ) := by
    ext b
    simp [EuclideanSpace.single, Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, smul_eq_mul, mul_comm]

/-- Internal restricted inverse estimate for Subsection 4.4. The retained
coordinates contribute exactly zero, so its upper bound uses only exterior
Hessian entries, as required by Subsection 4.5. -/
theorem internal_exterior_diagonal_bound {k : ℕ} (n : ℕ) (s β : ℝ)
    (hs : 0 < s) (hβ : 0 < β) (y : Fin k → ℝ) (hy : ∀ a, 0 < y a)
    (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) →L[ℝ] ℝ)
    (hA : ∀ v, β * (2 * (s * (s + 1))) *
      (∑ a, y a ^ (-s - 2) * (v a) ^ 2) ≤ A v v)
    (i : Fin k) (v : EuclideanSpace ℝ (Fin k)) (hv : ∀ a, a.val < n → v a = 0) :
    2 * (β⁻¹ * A (EuclideanSpace.single i 1) v) - A v v ≤
      (β * (2 * (s * (s + 1))))⁻¹ * ∑ a : Fin k, if n ≤ a.val then
        y a ^ (s + 2) * (β⁻¹ * A (EuclideanSpace.single i 1) (EuclideanSpace.single a 1)) ^ 2
        else 0 := by
  classical
  let α := β * (2 * (s * (s + 1)))
  have hα : 0 < α := by dsimp [α]; positivity
  rw [bilinear_coordinates A (EuclideanSpace.single i 1) v]
  calc
    _ ≤ 2 * (β⁻¹ * ∑ a, A (EuclideanSpace.single i 1) (EuclideanSpace.single a 1) * v a) -
        α * (∑ a, y a ^ (-s - 2) * (v a) ^ 2) := sub_le_sub_left (hA v) _
    _ = ∑ a, (2 * (β⁻¹ * A (EuclideanSpace.single i 1) (EuclideanSpace.single a 1)) * v a -
        (α * y a ^ (-s - 2)) * (v a) ^ 2) := by
      simp only [Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro a _ <;> ring
    _ ≤ ∑ a, if n ≤ a.val then
        α⁻¹ * (y a ^ (s + 2) * (β⁻¹ * A (EuclideanSpace.single i 1)
          (EuclideanSpace.single a 1)) ^ 2) else 0 := by
      apply Finset.sum_le_sum
      intro a _
      split_ifs with ha
      · let g := β⁻¹ * A (EuclideanSpace.single i 1) (EuclideanSpace.single a 1)
        have hpos : 0 < α * y a ^ (-s - 2) := mul_pos hα (Real.rpow_pos_of_pos (hy a) _)
        have hsq : 2 * g * v a - (α * y a ^ (-s - 2)) * (v a) ^ 2 ≤
            g ^ 2 / (α * y a ^ (-s - 2)) := by
          apply (le_div_iff₀ hpos).mpr
          nlinarith [sq_nonneg (g - (α * y a ^ (-s - 2)) * v a)]
        apply hsq.trans_eq
        rw [div_eq_mul_inv, mul_inv_rev, ← Real.rpow_neg (hy a).le,
          show -(-s - 2) = s + 2 by ring]
        ring
      · rw [hv a (by omega)]
        ring_nf
        exact le_rfl
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      split_ifs <;> simp [α]

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 4.4 of the paper, the all-point individual-score variance bound.
The coefficient is the explicit `1 / (2βs(s+1))`, and the right side is
the existing nonnegative exterior gradient energy. In particular the
right side has no retained-coordinate contributions. -/
theorem physical_individual_score_variance (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (hN : 3 ≤ n + m + 1) (hm : 1 ≤ m) :
    ∃ U : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain (n + m).succPNat) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
          y ∈ gapAmbientDomain (n + m).succPNat},
        U y.val = p.val.1 * physicalAmbientGapEnergy p (n + m).succPNat y) ∧
      ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (i : Fin n),
        let F := fun z => p.val.1⁻¹ * fderiv ℝ U
          (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z))
            (EuclideanSpace.single (Fin.castLE (by omega) i) 1)
        let μ := ProperMarginalChart.conditionalMeasure p n m hn (Equiv.refl _) x
        MemLp F 2 μ ∧ (∫ z, (F z - ∫ y, F y ∂μ) ^ 2 ∂μ) ≤
          (p.val.1 * (2 * (p.val.2 * (p.val.2 + 1))))⁻¹ *
            (PhysicalFibres.exteriorGradientEnergy p n m hn x i).toReal := by
  classical
  obtain ⟨U,hU,hv,hBL⟩ := physical_scores_brascamp_lieb p n m hn hN hm
  refine ⟨U,hU,hv,fun x i => ?_⟩
  intro F μ
  let c := fun z => RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)
  let Ω := AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ a, x.val a)
  let V := fun z => U (c z)
  let W := fun y => p.val.1⁻¹ * U y
  have hWv : ∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
      y ∈ gapAmbientDomain (n + m).succPNat},
      W y.val = physicalAmbientGapEnergy p (n + m).succPNat y := by
    intro y
    dsimp only [W]
    rw [hv y, inv_mul_cancel_left₀ p.property.1.ne']
  let e : EuclideanSpace ℝ (Fin (n + m + 1)) :=
    EuclideanSpace.single (Fin.castLE (by omega) i) (1 : ℝ)
  obtain ⟨hF,hvar,hint⟩ := hBL x e
  refine ⟨hF.1, hvar.trans ?_⟩
  obtain ⟨C,hc,hactive,_⟩ := internal_exterior_chart_metric n m x.val ((n + m : ℕ) + 1)
  have hce : c = fun z => C z + c 0 := funext hc
  have hs (z) (hz : z ∈ Ω) : WithLp.ofLp (c z) ∈ Riesz1.gapSimplex (n + m).succPNat :=
    PhysicalFibres.configuration_mem_simplex n m (Equiv.refl _) x ⟨z,hz⟩
  have hUa (z) (hz : z ∈ Ω) : ContDiffAt ℝ 2 U (c z) :=
    (hU.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain _).mem_nhds
      (PhysicalEnergy.simplex_subset_ambient _ _ (hs z hz)))).of_le (by norm_num)
  have hW (z) (hz : z ∈ Ω) (u v) :
      fderiv ℝ (fderiv ℝ W) (c z) u v = p.val.1⁻¹ * fderiv ℝ (fderiv ℝ U) (c z) u v :=
    PhysicalCollision.internal_hessian_const_mul (hUa z hz) _ u v
  let B := fun z => ∑ a : Fin (n + m + 1), if n ≤ a.val then
    c z a ^ (p.val.2 + 2) * (fderiv ℝ (fderiv ℝ W) (c z) e (EuclideanSpace.single a 1)) ^ 2 else 0
  have hBi := PhysicalFibres.exteriorGradientEnergy_finite p n m hn W hWv x i
  have hB : Integrable B μ := by
    dsimp only [μ]
    rw [← PhysicalFibres.map_measure p n m hn (Equiv.refl _) x]
    apply (MeasurableEmbedding.subtype_coe
      (AffineSimplex.isOpen_chartDomain _ _).measurableSet).integrable_map_iff.mpr
    exact hBi.1
  have hBint : (∫ z, B z ∂μ) = (PhysicalFibres.exteriorGradientEnergy p n m hn x i).toReal := by
    have he := integral_map (measurable_subtype_coe.aemeasurable)
      (by rw [PhysicalFibres.map_measure p n m hn (Equiv.refl _) x]; exact hB.aestronglyMeasurable)
    rw [PhysicalFibres.map_measure p n m hn (Equiv.refl _) x] at he
    exact he.trans hBi.2.2.2.symm
  have hbound : ∀ᵐ z ∂μ, sSup (Set.range fun h : EuclideanSpace ℝ (Fin m) =>
      2 * inner ℝ (gradient F z) h - fderiv ℝ (fderiv ℝ V) z h h) ≤
      (p.val.1 * (2 * (p.val.2 * (p.val.2 + 1))))⁻¹ * B z := by
    filter_upwards [ConditionalEnergyMoments.physical_conditional_support
      p n m hn (Equiv.refl _) x] with z hz
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨h,rfl⟩
    have hg : inner ℝ (gradient F z) h =
        p.val.1⁻¹ * fderiv ℝ (fderiv ℝ U) (c z) e (C h) := by
      have he : F = fun y => p.val.1⁻¹ * fderiv ℝ U (C y + c 0) e := by
        funext y
        rw [← hc]
      rw [he]
      have hh := internal_score_differential C (c 0) e p.val.1⁻¹ U z h
        (by rw [← hc]; exact hUa z hz)
      have hcz : c z = C z + c 0 := hc z
      simpa only [← hcz] using hh
    have hH : fderiv ℝ (fderiv ℝ V) z h h =
        fderiv ℝ (fderiv ℝ U) (c z) (C h) (C h) := by
      dsimp only [V]
      rw [hce]
      exact AffineMetricTransport.hessian_comp_affine C (c 0)
        (by rw [← hc]; exact hUa z hz) h h
    dsimp only
    rw [hg,hH]
    have ht := internal_exterior_diagonal_bound n p.val.2 p.val.1 p.property.2.1 p.property.1
      (fun a => c z a) (hs z hz).1 (fderiv ℝ (fderiv ℝ U) (c z))
      (internal_ambient_curvature p n m hN U hv (c z) (hs z hz))
      (Fin.castLE (by omega) i) (C h) (by
        intro a ha
        have hi : Fin.castLE (by omega) (⟨a.val,ha⟩ : Fin n) = a := Fin.ext rfl
        rw [← hi]
        exact hactive h _)
    apply ht.trans_eq
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    dsimp only [B]
    split_ifs <;> first | rw [hW z hz] | rfl
  have hmono := integral_mono_ae hint (hB.const_mul _) hbound
  rw [integral_const_mul, hBint] at hmono
  exact hmono

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 4.4 of the paper, compensation inverse-energy estimate, in the
more general form valid for every constant ambient direction. The exact
factor is beta to the power minus two for the beta-scaled potential. -/
theorem physical_directional_score_variance (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (hN : 3 ≤ n + m + 1) (hm : 1 ≤ m) :
    ∃ U : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain (n + m).succPNat) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
          y ∈ gapAmbientDomain (n + m).succPNat},
        U y.val = p.val.1 * physicalAmbientGapEnergy p (n + m).succPNat y) ∧
      ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
        (v : EuclideanSpace ℝ (Fin (n + m + 1))),
        let c := fun z => RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)
        let F := fun z => p.val.1⁻¹ * fderiv ℝ U (c z) v
        let μ := ProperMarginalChart.conditionalMeasure p n m hn (Equiv.refl _) x
        MemLp F 2 μ ∧ Integrable (fun z => fderiv ℝ (fderiv ℝ U) (c z) v v) μ ∧
          (∫ z, (F z - ∫ y, F y ∂μ) ^ 2 ∂μ) ≤
            p.val.1⁻¹ ^ 2 * ∫ z, fderiv ℝ (fderiv ℝ U) (c z) v v ∂μ := by
  classical
  obtain ⟨U,hU,hv,hBL⟩ := physical_scores_brascamp_lieb p n m hn hN hm
  refine ⟨U,hU,hv,fun x v => ?_⟩
  intro c F μ
  obtain ⟨hF,hvar,hint⟩ := hBL x v
  have hI := PhysicalFibres.internal_integrable_ambient_hessian p n m hn (Equiv.refl _) U hv x v v
  refine ⟨hF.1,hI,hvar.trans ?_⟩
  let Ω := AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ a, x.val a)
  let V := fun z => U (c z)
  obtain ⟨C,hc,_,_⟩ := internal_exterior_chart_metric n m x.val ((n + m : ℕ) + 1)
  have hce : c = fun z => C z + c 0 := funext hc
  have hs (z) (hz : z ∈ Ω) : WithLp.ofLp (c z) ∈ Riesz1.gapSimplex (n + m).succPNat :=
    PhysicalFibres.configuration_mem_simplex n m (Equiv.refl _) x ⟨z,hz⟩
  have hUa (z) (hz : z ∈ Ω) : ContDiffAt ℝ 2 U (c z) :=
    (hU.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain _).mem_nhds
      (PhysicalEnergy.simplex_subset_ambient _ _ (hs z hz)))).of_le (by norm_num)
  have hbound : ∀ᵐ z ∂μ, sSup (Set.range fun h : EuclideanSpace ℝ (Fin m) =>
      2 * inner ℝ (gradient F z) h - fderiv ℝ (fderiv ℝ V) z h h) ≤
      p.val.1⁻¹ ^ 2 * fderiv ℝ (fderiv ℝ U) (c z) v v := by
    filter_upwards [ConditionalEnergyMoments.physical_conditional_support
      p n m hn (Equiv.refl _) x] with z hz
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨h,rfl⟩
    dsimp only
    have hg : inner ℝ (gradient F z) h =
        p.val.1⁻¹ * fderiv ℝ (fderiv ℝ U) (c z) v (C h) := by
      have he : F = fun y => p.val.1⁻¹ * fderiv ℝ U (C y + c 0) v := by
        funext y
        rw [← hc]
      rw [he]
      have hh := internal_score_differential C (c 0) v p.val.1⁻¹ U z h
        (by rw [← hc]; exact hUa z hz)
      have hcz : c z = C z + c 0 := hc z
      simpa only [← hcz] using hh
    have hH : fderiv ℝ (fderiv ℝ V) z h h =
        fderiv ℝ (fderiv ℝ U) (c z) (C h) (C h) := by
      dsimp only [V]
      rw [hce]
      exact AffineMetricTransport.hessian_comp_affine C (c 0)
        (by rw [← hc]; exact hUa z hz) h h
    rw [hg,hH]
    let A := fderiv ℝ (fderiv ℝ U) (c z)
    have hpos (w) : 0 ≤ A w w :=
      (mul_nonneg (by have hβ := p.property.1; have hs := p.property.2.1; positivity)
        (Finset.sum_nonneg fun a _ => mul_nonneg
          (Real.rpow_nonneg ((hs z hz).1 a).le _) (sq_nonneg _))).trans
            (internal_ambient_curvature p n m hN U hv (c z) (hs z hz) w)
    have ht := hpos (p.val.1⁻¹ • v - C h)
    simp only [map_sub, sub_apply, map_smul, smul_apply, smul_eq_mul] at ht
    have hsym : A (C h) v = A v (C h) :=
      (hUa z hz).isSymmSndFDerivAt (by norm_num) (C h) v
    rw [hsym] at ht
    change 2 * (p.val.1⁻¹ * A v (C h)) - A (C h) (C h) ≤ p.val.1⁻¹ ^ 2 * A v v
    nlinarith only [ht]
  have hmono := integral_mono_ae hint (hI.const_mul (p.val.1⁻¹ ^ 2)) hbound
  rw [integral_const_mul] at hmono
  exact hmono

set_option backward.isDefEq.respectTransparency false in
/-- Internal bridge for Subsection 4.4: every directional
conditional Hessian mean is the contraction of the existing finite
conditional interval matrix. The integrability is part of the conclusion. -/
theorem internal_conditional_hessian_bilinear (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (U : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ)
    (hv : ∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
        y ∈ gapAmbientDomain (n + m).succPNat},
      U y.val = p.val.1 * physicalAmbientGapEnergy p (n + m).succPNat y)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (u v : EuclideanSpace ℝ (Fin (n + m + 1))) :
    let μ := ProperMarginalChart.conditionalMeasure p n m hn (Equiv.refl _) x
    let H := IntervalBoundary.intervalMatrix (n + m).succPNat (n + m + 1) le_rfl
      (conditionalIntervalWeight p n m hn (Equiv.refl _) x)
    Integrable (fun z => fderiv ℝ (fderiv ℝ U)
      (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) u v) μ ∧
    (∫ z, fderiv ℝ (fderiv ℝ U)
      (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) u v ∂μ) =
        p.val.1 * ∑ a, ∑ b, u a * H a b * v b := by
  classical
  intro μ H
  let c := fun z => RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)
  obtain ⟨W,hW,hw,hentry⟩ := PhysicalFibres.ambient_hessian_conditional_entries p n m hn
  have he (z : AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ a, x.val a)) :
      fderiv ℝ (fderiv ℝ U) (c z.val) =
        p.val.1 • fderiv ℝ (fderiv ℝ W) (c z.val) := by
    have hz : c z.val ∈ gapAmbientDomain (n + m).succPNat :=
      (PhysicalFibres.configuration n m (Equiv.refl _) x z).property
    have heq : U =ᶠ[𝓝 (c z.val)] fun y => p.val.1 * W y := by
      filter_upwards [(PhysicalEnergy.isOpen_gapAmbientDomain _).mem_nhds hz] with y hy
      rw [hv ⟨y,hy⟩, hw ⟨y,hy⟩]
    ext a b
    rw [heq.fderiv.fderiv_eq]
    exact PhysicalCollision.internal_hessian_const_mul
      ((hW.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain _).mem_nhds hz)).of_le
        (by norm_num)) _ a b
  have hcoord (A : EuclideanSpace ℝ (Fin (n + m + 1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (n + m + 1)) →L[ℝ] ℝ) :
      A u v = ∑ a, ∑ b, u a * A (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) * v b := by
    have hu : u = ∑ a, u a • EuclideanSpace.single a (1 : ℝ) := by
      ext b
      simp [EuclideanSpace.single, Pi.single_apply]
    conv_lhs => rw [hu]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [bilinear_coordinates, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hs (z : AffineSimplex.chartDomain m (((n + m : ℕ) + 1) - ∑ a, x.val a)) :
      fderiv ℝ (fderiv ℝ U) (c z.val) u v = p.val.1 *
        ∑ a, ∑ b, u a * fderiv ℝ (fderiv ℝ W) (c z.val)
          (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) * v b := by
    rw [he z]
    simp only [smul_apply, smul_eq_mul]
    rw [hcoord]
  have hsmall (a b) : Integrable (fun z => u a * fderiv ℝ (fderiv ℝ W) (c z.val)
      (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) * v b)
      (PhysicalFibres.measure p n m hn (Equiv.refl _) x) :=
    ((hentry x a b).1.const_mul _).mul_const _
  have hiU := PhysicalFibres.internal_integrable_ambient_hessian p n m hn (Equiv.refl _) U hv x u v
  refine ⟨hiU,?_⟩
  have hmap := integral_map (μ := PhysicalFibres.measure p n m hn (Equiv.refl _) x)
    (f := fun z => fderiv ℝ (fderiv ℝ U) (c z) u v) measurable_subtype_coe.aemeasurable
    (by rw [PhysicalFibres.map_measure p n m hn (Equiv.refl _) x]; exact hiU.aestronglyMeasurable)
  rw [PhysicalFibres.map_measure p n m hn (Equiv.refl _) x] at hmap
  rw [hmap, integral_congr_ae (ae_of_all _ hs), integral_const_mul]
  congr 1
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hsmall a b]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_finsetSum _ fun b _ => hsmall a b]
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_mul_const, integral_const_mul]
  have hj := (hentry x a b).2
  change (∫ z, fderiv ℝ (fderiv ℝ W) (c z.val)
    (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)
      ∂PhysicalFibres.measure p n m hn (Equiv.refl _) x) = H a b at hj
  rw [hj]

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 4.4 of the paper: the exact compensation variance bound
`Var(G) ≤ β⁻¹ c`, with the uniform exterior vector and the conditional interval matrix defining `c`. -/
theorem physical_compensation_score_variance (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (hN : 3 ≤ n + m + 1) (hm : 1 ≤ m) :
    ∃ U : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain (n + m).succPNat) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
          y ∈ gapAmbientDomain (n + m).succPNat},
        U y.val = p.val.1 * physicalAmbientGapEnergy p (n + m).succPNat y) ∧
      ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)),
        let q := WithLp.toLp 2 (ConditionalForces.compensationVector n m)
        let G := fun z => p.val.1⁻¹ * fderiv ℝ U
          (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) q
        let μ := ProperMarginalChart.conditionalMeasure p n m hn (Equiv.refl _) x
        let H := IntervalBoundary.intervalMatrix (n + m).succPNat (n + m + 1) le_rfl
          (conditionalIntervalWeight p n m hn (Equiv.refl _) x)
        let S := Finset.univ.filter (fun a : Fin (n + m + 1) => n ≤ a.val)
        MemLp G 2 μ ∧ (∫ z, (G z - ∫ y, G y ∂μ) ^ 2 ∂μ) ≤
          p.val.1⁻¹ * ((m + 1 : ℝ)⁻¹ ^ 2 * ∑ a ∈ S, ∑ b ∈ S, H a b) := by
  classical
  obtain ⟨U,hU,hv,hvar⟩ := physical_directional_score_variance p n m hn hN hm
  refine ⟨U,hU,hv,fun x => ?_⟩
  intro q G μ H S
  obtain ⟨hG,_,hb⟩ := hvar x q
  refine ⟨hG,?_⟩
  have he := (internal_conditional_hessian_bilinear p n m hn U hv x q q).2
  change (∫ z, fderiv ℝ (fderiv ℝ U)
    (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) q q ∂μ) =
    p.val.1 * ∑ a, ∑ b, q a * H a b * q b at he
  have hsum : (∑ a, ∑ b, q a * H a b * q b) =
      (m + 1 : ℝ)⁻¹ ^ 2 * ∑ a ∈ S, ∑ b ∈ S, H a b := by
    have hq (a : Fin (n + m + 1)) : q a = if n ≤ a.val then (m + 1 : ℝ)⁻¹ else 0 := by
      dsimp only [q, ConditionalForces.compensationVector]
      split_ifs <;> first | rfl | omega
    simp_rw [hq]
    simp only [S, Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs with ha
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> ring
    · simp
  rw [he,hsum] at hb
  apply hb.trans_eq
  rw [pow_two, mul_assoc, inv_mul_cancel_left₀ p.property.1.ne']

set_option backward.isDefEq.respectTransparency false in
private theorem scores_ae_eq (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (U W : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ)
    (hv : ∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
        y ∈ gapAmbientDomain (n + m).succPNat}, U y.val = W y.val)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (v : EuclideanSpace ℝ (Fin (n + m + 1))) :
    (fun z => p.val.1⁻¹ * fderiv ℝ U
      (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) v) =ᵐ[
        ProperMarginalChart.conditionalMeasure p n m hn (Equiv.refl _) x]
    (fun z => p.val.1⁻¹ * fderiv ℝ W
      (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) v) := by
  filter_upwards [ConditionalEnergyMoments.physical_conditional_support
    p n m hn (Equiv.refl _) x] with z hz
  let y := PhysicalFibres.configuration n m (Equiv.refl _) x ⟨z,hz⟩
  have he : U =ᶠ[𝓝 y.val] W := by
    filter_upwards [(PhysicalEnergy.isOpen_gapAmbientDomain _).mem_nhds y.property] with a ha
    exact hv ⟨a,ha⟩
  change p.val.1⁻¹ * fderiv ℝ U y.val v = p.val.1⁻¹ * fderiv ℝ W y.val v
  rw [he.fderiv_eq]

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 4.4 of the paper, all its variance and covariance clauses.
The two unconditional variances hold at every retained point. On the
coefficient portion of the good event (hence on the full good event),
the covariances have the fixed weights of Subsection 4.5 and the required
`N⁻¹/²` factor. The constant depends only on inverse temperature and
exponent. The truncation level may be `A n^(κh)` for either active tilt. -/
theorem conditional_score_bounds (p : Parameters) (hs : 1 < p.val.2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ+) (m : ℕ),
      4 ≤ (n : ℕ) + m + 1 → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∃ U : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ,
        ContDiffOn ℝ ∞ U (gapAmbientDomain ((n : ℕ) + m).succPNat) ∧
        (∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) //
            y ∈ gapAmbientDomain ((n : ℕ) + m).succPNat},
          U y.val = p.val.1 * physicalAmbientGapEnergy p ((n : ℕ) + m).succPNat y) ∧
        ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)),
          let μ := ProperMarginalChart.conditionalMeasure p n m n.pos (Equiv.refl _) x
          let F := fun (i : Fin (n : ℕ)) z => p.val.1⁻¹ * fderiv ℝ U
            (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z))
              (EuclideanSpace.single (Fin.castLE (by omega) i) 1)
          let G := fun z => p.val.1⁻¹ * fderiv ℝ U
            (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z))
              (WithLp.toLp 2 (ConditionalForces.compensationVector n m))
          let H := IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat
            ((n : ℕ) + m + 1) le_rfl (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
          let S := Finset.univ.filter (fun a : Fin ((n : ℕ) + m + 1) => (n : ℕ) ≤ a.val)
          let c := (m + 1 : ℝ)⁻¹ ^ 2 * ∑ a ∈ S, ∑ b ∈ S, H a b
          (∀ i, MemLp (F i) 2 μ ∧ (∫ z, (F i z - ∫ y, F i y ∂μ) ^ 2 ∂μ) ≤
            C * (PhysicalFibres.exteriorGradientEnergy p n m n.pos x i).toReal) ∧
          MemLp G 2 μ ∧ (∫ z, (G z - ∫ y, G y ∂μ) ^ 2 ∂μ) ≤ p.val.1⁻¹ * c ∧
          ∀ D : ℝ, 0 ≤ D → x ∈ ExceptionalEvent.coefficientEvent p n m (by simp; omega) D →
            (∀ i j, |ProbabilityTheory.covariance (F i) (F j) μ| ≤
              C * D * weight p.val.2 i * weight p.val.2 j) ∧
            (∀ i, |ProbabilityTheory.covariance (F i) G μ| ≤
              C * D * (((n : ℕ) + m + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * weight p.val.2 i) ∧
            (∫ z, (G z - ∫ y, G y ∂μ) ^ 2 ∂μ) ≤ C * D / (((n : ℕ) + m + 1 : ℕ) : ℝ) := by
  classical
  let α := p.val.1 * (2 * (p.val.2 * (p.val.2 + 1)))
  let C := α⁻¹ + p.val.1⁻¹ + 1
  have hα : 0 < α := by dsimp [α]; have hβ := p.property.1; positivity
  have hC : 0 < C := by dsimp [C]; have hβ := p.property.1; positivity
  have hαC : α⁻¹ ≤ C := by dsimp [C]; have := inv_pos.mpr p.property.1; linarith
  have hβC : p.val.1⁻¹ ≤ C := by dsimp [C]; have := inv_pos.mpr hα; linarith
  refine ⟨C,hC,fun n m hN hhalf => ?_⟩
  have hm : 1 ≤ m := by have := n.pos; omega
  obtain ⟨U,hU,hv,hFi⟩ := physical_individual_score_variance p n m n.pos (by omega) hm
  obtain ⟨W,_,hw,hGi⟩ := physical_compensation_score_variance p n m n.pos (by omega) hm
  refine ⟨U,hU,hv,fun x => ?_⟩
  intro μ F G H S c
  let q := WithLp.toLp 2 (ConditionalForces.compensationVector n m)
  let G' := fun z => p.val.1⁻¹ * fderiv ℝ W
    (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) q
  have heq : G =ᵐ[μ] G' := scores_ae_eq p n m n.pos U W
    (fun y => (hv y).trans (hw y).symm) x q
  have hmean : (∫ z, G z ∂μ) = ∫ z, G' z ∂μ := integral_congr_ae heq
  have hvar : (∫ z, (G z - ∫ y, G y ∂μ) ^ 2 ∂μ) =
      ∫ z, (G' z - ∫ y, G' y ∂μ) ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [heq] with z hz
    rw [hz,hmean]
  have hG : MemLp G 2 μ := MemLp.ae_eq heq.symm (hGi x).1
  have hVG : (∫ z, (G z - ∫ y, G y ∂μ) ^ 2 ∂μ) ≤ p.val.1⁻¹ * c := by
    rw [hvar]
    exact (hGi x).2
  have hF (i) : MemLp (F i) 2 μ ∧ (∫ z, (F i z - ∫ y, F i y ∂μ) ^ 2 ∂μ) ≤
      C * (PhysicalFibres.exteriorGradientEnergy p n m n.pos x i).toReal :=
    ⟨(hFi x i).1, (hFi x i).2.trans (mul_le_mul_of_nonneg_right hαC (ENNReal.toReal_nonneg))⟩
  refine ⟨hF,hG,hVG,fun D hD hx => ?_⟩
  have hHN (a b) : 0 ≤ H a b := by
    unfold H IntervalBoundary.intervalMatrix
    apply Finset.sum_nonneg
    intro t _
    apply mul_nonneg (conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x t)
    unfold IntervalBoundary.rankOne
    split_ifs <;> norm_num
  have hbn (i : Fin (n : ℕ)) : 0 ≤ (m + 1 : ℝ)⁻¹ *
      ∑ a ∈ S, H (Fin.castLE (by omega) i) a :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => hHN _ a)
  have hcn : 0 ≤ c := mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun a _ =>
    Finset.sum_nonneg fun b _ => hHN a b)
  have hcD : c ≤ D / (((n : ℕ) + m + 1 : ℕ) : ℝ) := by
    let i : Fin (n : ℕ) := ⟨0,n.pos⟩
    have ht := hx.2.2.2.2.1 i
    exact (le_add_of_nonneg_left (hbn i)).trans ht
  have hVFD (i) : (∫ z, (F i z - ∫ y, F i y ∂μ) ^ 2 ∂μ) ≤
      C * D * (boundaryDistance i : ℝ) ^ (1 - 2 * p.val.2) := by
    apply (hF i).2.trans
    have ht := mul_le_mul_of_nonneg_left (hx.2.2.2.2.2 i) hC.le
    simpa only [boundaryDistance, mul_assoc] using ht
  have hVGD : (∫ z, (G z - ∫ y, G y ∂μ) ^ 2 ∂μ) ≤
      C * D / (((n : ℕ) + m + 1 : ℕ) : ℝ) := by
    apply hVG.trans
    calc
      _ ≤ C * c := mul_le_mul_of_nonneg_right hβC hcn
      _ ≤ _ := by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hcD hC.le
  have : IsProbabilityMeasure μ := ProperMarginalChart.conditionalMeasure_probability p n m n.pos (Equiv.refl _) x
  have hc := internal_score_covariances p.val.2 C D (((n : ℕ) + m + 1 : ℕ) : ℝ)
    hC.le hD (by positivity) F G (fun i => (hF i).1) hG hVFD hVGD
  exact ⟨hc.1,hc.2,hVGD⟩

end Riesz2.DecayShort.ConditionalScores
