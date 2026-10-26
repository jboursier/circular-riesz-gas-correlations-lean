/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.PhysicalDecayPart4
public import Riesz2.DecayShort.PhysicalDecayPart2

/-!
# Full-cycle comparison on the intrinsic law

Supported transport and the physical residual for Proposition 4.10.
All scalar forms retain the intrinsic gap metric.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology ContDiff

namespace Riesz2.DecayShort.PhysicalDecay

/-- Internal chart identity for Proposition 4.10. -/
theorem internal_full_chart_gap (N : ℕ+) (X : Riesz1.Configuration N) :
    WithLp.toLp 2 (fun i => 1 +
      (centeredGapChart N (WithLp.toLp 2 (gapVector X))).val i) =
        WithLp.toLp 2 (gapVector X) := by
  ext i
  change 1 + (gap X i.val - (∑ j : Fin (N : ℕ), gap X j.val) / (N : ℝ)) = gap X i.val
  rw [DefinitionSanity.actual_gap_sum, div_self (show (N : ℝ) ≠ 0 by positivity)]
  ring

/-- Actual supported measure transport for Proposition 4.10.
The full intrinsic law is the image by the centered microscopic gap map. -/
theorem full_intrinsic_tilted_eq_map (p : Parameters) (N : ℕ+)
    (θ : PhysicalCutoff) (h : ℝ) (b : Bool) :
    fullIntrinsicTiltedGapLaw p N θ h b =
      (tiltedParticleMeasure p N N le_rfl θ h b).map
        (fun X => centeredGapChart N (WithLp.toLp 2 (gapVector X))) := by
  let T := fun X : Riesz1.Configuration N =>
    centeredGapChart N (WithLp.toLp 2 (gapVector X))
  change ((tiltedParticleMeasure p N N le_rfl θ h b).map
    (fun X => WithLp.toLp 2 (gapVector X))).comap
      (fun z : gapTangentSpace N => WithLp.toLp 2 (fun i => 1+z.val i)) = _
  have he : (fun X : Riesz1.Configuration N => WithLp.toLp 2 (gapVector X)) =
      (fun z : gapTangentSpace N => WithLp.toLp 2 (fun i => 1+z.val i)) ∘ T :=
    funext (fun X => (internal_full_chart_gap N X).symm)
  rw [he, ← Measure.map_map (DefinitionSanity.full_chart_embedding N).measurable
    (DefinitionSanity.intrinsic_projection_measurable N),
    (DefinitionSanity.full_chart_embedding N).comap_map]

set_option backward.isDefEq.respectTransparency false in
/-- Canonical rotation-zero reconstruction on the positive intrinsic
domain, supporting Proposition 4.10. -/
theorem internal_full_gap_section (N : ℕ+) :
    ∃ ρ : intrinsicGapDomain N → Riesz1.Configuration N,
      Measurable ρ ∧ ∀ z : intrinsicGapDomain N,
        WithLp.toLp 2 (gapVector (ρ z)) =
          WithLp.toLp 2 (fun i => 1+z.val.val i) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n.succPNat :=
    ⟨N.natPred, (PNat.succPNat_natPred N).symm⟩
  let G := fun z : intrinsicGapDomain n.succPNat =>
    WithLp.toLp 2 (fun i => 1+z.val.val i)
  have hG (z : intrinsicGapDomain n.succPNat) :
      G z ∈ AffineSimplex.massSimplex n (n+1) := by
    simpa only [G, AffineSimplex.massSimplex, Riesz1.gapSimplex, Set.mem_ofPred_eq,
      Nat.succPNat_coe, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using
      PhysicalCollision.intrinsic_chart_mem_simplex n.succPNat z.property
  let d : intrinsicGapDomain n.succPNat → GapChart.Domain n := fun z =>
    ⟨fun i => G z i.castSucc, by
      have ht := AffineSimplex.chart_mem_simplex_iff n (n+1)
        (WithLp.toLp 2 (fun i : Fin n => G z i.castSucc))
      apply ht.mp
      have he := AffineSimplex.chart_coordinates n (n+1) (y := G z) (hG z).2
      change AffineSimplex.chart n (n+1) (AffineSimplex.coordinates n (G z)) ∈ _
      rw [he]
      exact hG z⟩
  have hd : Measurable d := by
    apply Measurable.subtype_mk
    apply Measurable.of_eval
    intro i
    change Measurable (fun z : intrinsicGapDomain n.succPNat => 1+z.val.val i.castSucc)
    fun_prop
  refine ⟨GapChart.reconstruct n ∘ d, (GapChart.measurable_reconstruct n).comp hd,?_⟩
  intro z
  rw [Function.comp_apply, GapChart.gapVector_eq_chart, GapChart.gaps_reconstruct]
  exact AffineSimplex.chart_coordinates n (n+1) (y := G z) (hG z).2

/-- Internal a.e. reconstruction for Proposition 4.10.
Only the positive supported domain is reconstructed. -/
theorem internal_full_intrinsic_projection (p : Parameters) (N : ℕ+)
    (θ : PhysicalCutoff) (h : ℝ) (b : Bool) :
    ∃ τ : gapTangentSpace N → Riesz1.Configuration N, Measurable τ ∧
      ∀ᵐ z ∂fullIntrinsicTiltedGapLaw p N θ h b,
        WithLp.toLp 2 (gapVector (τ z)) = WithLp.toLp 2 (fun i => 1+z.val i) := by
  let ν := fullIntrinsicTiltedGapLaw p N θ h b
  have hsupp : ∀ᵐ z ∂ν, z ∈ intrinsicGapDomain N := by
    dsimp only [ν]
    rw [full_intrinsic_tilted_eq_map]
    apply (ae_map_iff (DefinitionSanity.intrinsic_projection_measurable N).aemeasurable
      (AffineMetric.intrinsicGapDomain_isOpen N).measurableSet).mpr
    apply ae_of_all
    intro X i
    have he := congrArg (fun y : EuclideanSpace ℝ (Fin (N : ℕ)) => y i)
      (internal_full_chart_gap N X)
    change 1+(centeredGapChart N (WithLp.toLp 2 (gapVector X))).val i = gap X i.val at he
    rw [he]
    exact DefinitionSanity.gap_positive X i.val
  have hne : (intrinsicGapDomain N).Nonempty := ⟨0, by intro i; simp⟩
  obtain ⟨π,hπ,_,hπval⟩ := internal_retained_projection ν (intrinsicGapDomain N)
    (AffineMetric.intrinsicGapDomain_isOpen N).measurableSet hne hsupp
  obtain ⟨ρ,hρ,hgap⟩ := internal_full_gap_section N
  refine ⟨ρ ∘ π,hρ.comp hπ.measurable,?_⟩
  filter_upwards [hπval] with z hz
  simpa only [Function.comp_apply,hz] using hgap (π z)

/-- Gap invariance of the full good event in Proposition 4.10. -/
theorem fullGoodEvent_iff_of_gapVector_eq (p : Parameters) (N : ℕ+) (h D : ℝ)
    (X Y : Riesz1.Configuration N) (hxy : gapVector X = gapVector Y) :
    X ∈ ExceptionalEvent.fullGoodEvent p N h D ↔
      Y ∈ ExceptionalEvent.fullGoodEvent p N h D := by
  have hg (i : Fin (N : ℕ)) : gap X i.val = gap Y i.val := congrFun hxy i
  obtain ⟨W,_,_,hjet⟩ := GoodBlocks.particleHessian_eq_second p N
  have hH (i j) : GoodBlocks.particleHessian p N i j X =
      GoodBlocks.particleHessian p N i j Y := by
    rw [← hjet X i j, ← hjet Y i j, hxy]
  simp only [ExceptionalEvent.fullGoodEvent, mem_ofPred_eq, hg, hH]

/-- Gap invariance of the actual auxiliary matrix in Proposition 4.10. -/
theorem fullFrozenMatrix_eq_of_gapVector_eq (p : Parameters) (N : ℕ+)
    (θ : PhysicalCutoff) (h : ℝ) (b : Bool) (D : ℝ)
    (X Y : Riesz1.Configuration N) (hxy : gapVector X = gapVector Y) :
    fullFrozenMatrix p N θ h b D X = fullFrozenMatrix p N θ h b D Y := by
  classical
  obtain ⟨W,_,_,hjet⟩ := GoodBlocks.particleHessian_eq_second p N
  have hH (i j) : GoodBlocks.particleHessian p N i j X =
      GoodBlocks.particleHessian p N i j Y := by
    rw [← hjet X i j, ← hjet Y i j, hxy]
  simp only [fullFrozenMatrix, fullGoodEvent_iff_of_gapVector_eq p N h D X Y hxy, hxy, hH]

/-- Internal norm transport for Proposition 4.10.
Every measurable gap observable has its original particle-law norm after
supported reconstruction. No invariance of the particle scalar metric is used. -/
theorem internal_full_gap_norm_transport (p : Parameters) (N : ℕ+)
    (θ : PhysicalCutoff) (h : ℝ) (b : Bool)
    (τ : gapTangentSpace N → Riesz1.Configuration N) (hτ : Measurable τ)
    (hgap : ∀ᵐ z ∂fullIntrinsicTiltedGapLaw p N θ h b,
      WithLp.toLp 2 (gapVector (τ z)) = WithLp.toLp 2 (fun i => 1+z.val i))
    (f : Riesz1.Configuration N → ℝ) (hf : Measurable f)
    (hinv : ∀ X Y : Riesz1.Configuration N, gapVector X = gapVector Y → f X = f Y)
    (a : ℝ≥0∞) :
    eLpNorm (f ∘ τ) a (fullIntrinsicTiltedGapLaw p N θ h b) =
      eLpNorm f a (tiltedParticleMeasure p N N le_rfl θ h b) := by
  let T := fun X : Riesz1.Configuration N => centeredGapChart N (WithLp.toLp 2 (gapVector X))
  have hT := DefinitionSanity.intrinsic_projection_measurable N
  rw [full_intrinsic_tilted_eq_map] at hgap ⊢
  rw [eLpNorm_map_measure ((hf.comp hτ).aestronglyMeasurable) hT.aemeasurable]
  apply eLpNorm_congr_ae
  filter_upwards [ae_of_ae_map hT.aemeasurable hgap] with X hx
  change f (τ (T X)) = f X
  apply hinv
  apply WithLp.toLp_injective 2
  exact hx.trans (internal_full_chart_gap N X)

/-- Internal derivative identification for Proposition 4.10.
Agreement on the open ambient domain determines the complete ambient Hessian. -/
theorem internal_full_physical_second (p : Parameters) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (θ : PhysicalCutoff) (h : ℝ) (b : Bool)
    (W V : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ)
    (hval : ∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
      W y.val = fullPhysicalPotentialValue p N hN θ h b y)
    (hV : ContDiffOn ℝ ∞ V (gapAmbientDomain N))
    (hv : ∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
      V y.val = physicalAmbientGapEnergy p N y)
    (X : Riesz1.Configuration N) :
    let F := fun y : EuclideanSpace ℝ (Fin (N : ℕ)) =>
      ∑ i, (θ.val (((N : ℝ)^h)⁻¹*y i) + if b then θ.val (((N : ℝ)^h)⁻¹*(y i)⁻¹) else 0)
    fderiv ℝ (fderiv ℝ W) (WithLp.toLp 2 (gapVector X)) =
      p.val.1 • fderiv ℝ (fderiv ℝ (fun y => V y+F y)) (WithLp.toLp 2 (gapVector X)) := by
  intro F
  let x := WithLp.toLp 2 (gapVector X)
  have hx := GapChart.gapVector_mem_gapAmbientDomain X
  have he : W =ᶠ[𝓝 x] (fun y => p.val.1*(V y+F y)) := by
    filter_upwards [(PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hx] with y hy
    exact (hval ⟨y,hy⟩).trans
      (ExceptionalEvent.internal_full_physical_realization p N hN θ h b V hv ⟨y,hy⟩).symm
  have hsV : ContDiffAt ℝ 2 V x :=
    (hV.of_le (by simp)).contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hx)
  have hsF := PhysicalComparison.penalty_contDiffAt (N : ℕ) θ
    (inv_pos.mpr (Real.rpow_pos_of_pos (show (0 : ℝ) < N by positivity) h)) b
    x (fun i => Riesz1.gap_pos X i.val)
  rw [he.fderiv.fderiv_eq]
  ext u v
  exact PhysicalCollision.internal_hessian_const_mul (hsV.add hsF) p.val.1 u v

set_option backward.isDefEq.respectTransparency false in
/-- Full-cycle exceptional envelope for Proposition 4.10.
It includes the identity prescription and absorbs every prescribed polynomial.
The statement applies to every exact smooth physical representative. -/
theorem internal_full_exceptional_envelope (p : Parameters) (hs : 1 < p.val.2) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ h : ℝ, 0 < h → ∃ δ : ℝ, 0 < δ ∧
      ∀ θ : PhysicalCutoff, ∃ A : ℝ, 1 ≤ A ∧ ∀ a : ℝ,
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (N : ℕ+) (hN : 4 ≤ (N : ℕ)) (b : Bool)
        (W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ),
        (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
          W y.val = fullPhysicalPotentialValue p N (by omega) θ h b y) →
        let μ := tiltedParticleMeasure p N N le_rfl θ h b
        let E := (ExceptionalEvent.fullGoodEvent p N h (A*(N : ℝ)^(κ*h)))ᶜ
        let Z := E.indicator (fun X =>
          ‖fderiv ℝ (fderiv ℝ W) (WithLp.toLp 2 (gapVector X))‖/p.val.1+1)
        Measurable Z ∧ MemLp Z 2 μ ∧
          (N : ℝ)^a*(eLpNorm Z 2 μ).toReal ≤ C*Real.exp (-c*(N : ℝ)^δ) := by
  classical
  obtain ⟨κ,hκ,hprob⟩ := ExceptionalEvent.full_good_event_probability p.val.2 hs
  refine ⟨κ,hκ,fun h hh => ?_⟩
  obtain ⟨δ,hδ,hprob⟩ := hprob h hh
  refine ⟨δ,hδ,fun θ => ?_⟩
  obtain ⟨A,B,c,hA,hB,hc,hprob⟩ := hprob θ p.val.1 p.val.1 p.property.1 le_rfl
  obtain ⟨M,hM,hmom⟩ := ExceptionalEvent.full_hessian_fourth_moments
    p.val.2 hs θ p.val.1 p.val.1 h p.property.1 le_rfl hh
  refine ⟨A,hA,fun a => ?_⟩
  obtain ⟨C,hC,hbound⟩ := ExceptionalEvent.internal_weighted_exceptional
    (d := 3) (a := a) hδ hc hB (show 0 < M+1 by linarith)
  refine ⟨C,c/8,hC,by positivity,?_⟩
  intro N hN b W hval μ E Z
  let _ : IsProbabilityMeasure μ := DefinitionSanity.tilted_probability p N N le_rfl θ h b
  obtain ⟨V,hV,hv,hmom⟩ := hmom p rfl le_rfl le_rfl N hN
  let F := fun y : EuclideanSpace ℝ (Fin (N : ℕ)) =>
    ∑ i, (θ.val (((N : ℝ)^h)⁻¹*y i) + if b then θ.val (((N : ℝ)^h)⁻¹*(y i)⁻¹) else 0)
  let T := fun X : Riesz1.Configuration N =>
    ‖fderiv ℝ (fderiv ℝ (fun y => V y+F y)) (WithLp.toLp 2 (gapVector X))‖
  obtain ⟨hT,hTm,hTn⟩ := hmom b
  change Measurable T at hT
  change MemLp T 4 μ at hTm
  have he (X : Riesz1.Configuration N) :
      ‖fderiv ℝ (fderiv ℝ W) (WithLp.toLp 2 (gapVector X))‖/p.val.1+1 = T X+1 := by
    rw [internal_full_physical_second p N (by omega) θ h b W V hval hV hv X]
    have hn := norm_smul_of_nonneg p.property.1.le
      (fderiv ℝ (fderiv ℝ (fun y => V y+F y)) (WithLp.toLp 2 (gapVector X)))
    change ‖p.val.1 • fderiv ℝ (fderiv ℝ (fun y => V y+F y))
      (WithLp.toLp 2 (gapVector X))‖/p.val.1+1 = T X+1
    rw [hn]
    dsimp only [T,F]
    field_simp [p.property.1.ne']
  have hZeq : Z = E.indicator (fun X => T X+1) := by
    change E.indicator _ = E.indicator _
    congr 1
    exact funext he
  have hE : MeasurableSet E := (measurableSet_fullGoodEvent p N h _).compl
  have hS : Measurable (fun X => T X+1) := hT.add measurable_const
  have hnorm : eLpNorm (fun X => T X+1) 4 μ ≤ ENNReal.ofReal ((M+1)*(N : ℝ)^3) := by
    have hone : eLpNorm (fun _ : Riesz1.Configuration N => (1 : ℝ)) 4 μ = 1 := by
      simp [eLpNorm_const', (by norm_num : (4 : ℝ≥0∞) ≠ 0),
        (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)]
    refine (eLpNorm_add_le (by norm_num)).trans ((add_le_add hTn hone.le).trans ?_)
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
    have hp : (1 : ℝ) ≤ (N : ℝ)^3 := one_le_pow₀ hN1
    nlinarith
  have hmem : MemLp (fun X => T X+1) 2 μ :=
    (hTm.add (memLp_const (1 : ℝ))).mono_exponent (by norm_num)
  rw [hZeq]
  refine ⟨hS.indicator hE, hmem.indicator hE.nullMeasurableSet,?_⟩
  have hb := hbound (N : ℝ) (by exact_mod_cast N.pos) μ (fun X => T X+1) E hS
    (by norm_num only [Real.rpow_ofNat]; exact hnorm)
    (hprob p rfl le_rfl le_rfl N hN b)
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict hE.nullMeasurableSet] at hb
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity)] at ht
  exact ht

/-- Internal point-source norm identity for Proposition 4.10.
The vector essential supremum uses Euclidean length. -/
theorem internal_point_source_essSup {α : Type*} [MeasurableSpace α]
    (ν : Measure α) {n : ℕ} (i₀ : Fin n) (χ : Lp ℝ 2 ν) :
    eLpNorm (fun x => WithLp.toLp 2
      (fun i => ((if i=i₀ then χ else 0 : Lp ℝ 2 ν)) x)) ∞ ν = eLpNorm χ ∞ ν := by
  classical
  rw [← eLpNorm_norm _ (VectorRadial.memLp_values
    (fun i => if i=i₀ then χ else 0)).aestronglyMeasurable]
  rw [← eLpNorm_norm χ (Lp.aestronglyMeasurable χ)]
  apply eLpNorm_congr_ae
  filter_upwards [Lp.coeFn_zero ℝ 2 ν] with x hx
  change (0 : Lp ℝ 2 ν) x = 0 at hx
  have hz : (WithLp.toLp 2 (fun i => (if i=i₀ then χ else 0 : Lp ℝ 2 ν) x) :
      EuclideanSpace ℝ (Fin n)) = EuclideanSpace.single i₀ (χ x) := by
    ext i
    by_cases hi : i=i₀
    · simp [hi,EuclideanSpace.single]
    · simpa only [ite_eq_right hi, EuclideanSpace.single, PiLp.single_apply, ite_eq_right hi] using hx
  rw [hz]
  simp [EuclideanSpace.single,PiLp.norm_single]

set_option backward.isDefEq.respectTransparency false in
/-- Internal actual residual on the intrinsic law for Proposition 4.10.
The exceptional envelope is an internal input. The preceding theorem proves it
for the physical law. The auxiliary maximum principle supplies boundedness. -/
theorem internal_full_residual (p : Parameters) (hs : 1 < p.val.2)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (θ : PhysicalCutoff)
    (h : ℝ) (hh : 0 < h) (b : Bool) (D : ℝ)
    (W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ)
    (hW : ContDiffOn ℝ ∞ W (gapAmbientDomain N))
    (hval : ∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
      W y.val = fullPhysicalPotentialValue p N hN θ h b y)
    (τ : gapTangentSpace N → Riesz1.Configuration N) (hτ : Measurable τ)
    (hgap : ∀ᵐ z ∂fullIntrinsicTiltedGapLaw p N θ h b,
      WithLp.toLp 2 (gapVector (τ z)) = WithLp.toLp 2 (fun i => 1+z.val i))
    (Q : ScalarFormData (fullIntrinsicTiltedGapLaw p N θ h b))
    (hQ : IsClosedScalarDirichletForm Q)
    (i₀ : Fin (N : ℕ)) (χ : Lp ℝ 2 (fullIntrinsicTiltedGapLaw p N θ h b))
    (hχ : eLpNorm χ ∞ (fullIntrinsicTiltedGapLaw p N θ h b) < ⊤)
    (u : Fin (N : ℕ) → Q.1)
    (hu : WeightedWeakSolution Q (fun z => p.val.1 • fullFrozenMatrix p N θ h b D (τ z))
      (zeroSumComponents _) (fun i => if i=i₀ then χ else 0) u) :
    let ν := fullIntrinsicTiltedGapLaw p N θ h b
    let μ := tiltedParticleMeasure p N N le_rfl θ h b
    let E := (ExceptionalEvent.fullGoodEvent p N h D)ᶜ
    let Z := E.indicator (fun X =>
      ‖fderiv ℝ (fderiv ℝ W) (WithLp.toLp 2 (gapVector X))‖/p.val.1+1)
    Measurable Z → MemLp Z 2 μ →
    ∃ g : Fin (N : ℕ) → Lp ℝ 2 ν,
      (∀ᵐ z ∂ν, ∀ i, g i z = ∑ j,
        (hessianMatrix W (WithLp.toLp 2 (fun k => 1+z.val k)) i j-
          (p.val.1 • fullFrozenMatrix p N θ h b D (τ z)) i j)*(u j).val z) ∧
      ‖WithLp.toLp 2 g‖ ≤ (N : ℝ)^2 *
        ((p.val.1*(N : ℝ)^(-(p.val.2+2)*h))⁻¹ * (eLpNorm χ ∞ ν).toReal) *
        (p.val.1*(eLpNorm Z 2 μ).toReal) := by
  classical
  intro ν μ E Z hZm hZ
  let H := fun z : gapTangentSpace N => hessianMatrix W (WithLp.toLp 2 (fun i => 1+z.val i))
  let M := fun z => p.val.1 • fullFrozenMatrix p N θ h b D (τ z)
  let a := p.val.1*(N : ℝ)^(-(p.val.2+2)*h)
  let R := a⁻¹*(eLpNorm χ ∞ ν).toReal
  let T := fun z => p.val.1*Z (τ z)
  have ha : 0 < a := mul_pos p.property.1 (Real.rpow_pos_of_pos (by positivity) _)
  have hnorm : eLpNorm (Z ∘ τ) 2 ν = eLpNorm Z 2 μ :=
    internal_full_gap_norm_transport p N θ h b τ hτ hgap Z hZm (by
      intro X Y hxy
      simp only [Z, E, indicator, mem_compl_iff,
        fullGoodEvent_iff_of_gapVector_eq p N h D X Y hxy, hxy]) 2
  have hZτ : MemLp (Z ∘ τ) 2 ν :=
    by rw [memLp_iff,hnorm]; exact hZ.eLpNorm_lt_top
  have hT : MemLp T 2 ν := hZτ.const_mul p.val.1
  have hT0 : ∀ᵐ z ∂ν, 0 ≤ T z := ae_of_all ν fun z => by
    dsimp only [T,Z]
    exact mul_nonneg p.property.1.le
      (indicator_nonneg (fun X _ => add_nonneg
        (div_nonneg (norm_nonneg (fderiv ℝ (fderiv ℝ W)
          (WithLp.toLp 2 (gapVector X)))) p.property.1.le) zero_lt_one.le) (τ z))
  have hHm : ∀ i j, Measurable (fun z => H z i j) := fun i j =>
    (DifferentiatedPoisson.measurable_hessian_entries (V := W) i j).comp
      (PhysicalCollision.intrinsic_chart_contDiff N).continuous.measurable
  have hMm : ∀ i j, Measurable (fun z => M z i j) :=
    AbstractEnergy.scaled_measurable _ _ (fun i j =>
      ((fullFrozenMatrix_measurable_symmetric p N θ h b D).1 i j).comp hτ)
  have hentry : ∀ᵐ z ∂ν, ∀ i j, |(H z-M z) i j| ≤ T z := by
    filter_upwards [hgap] with z hz i j
    by_cases hx : τ z ∈ ExceptionalEvent.fullGoodEvent p N h D
    · have he := internal_fullFrozenMatrix_eq_physical p N hN θ h b D W hW hval (τ z) hx
      rw [hz] at he
      change |H z i j-M z i j| ≤ T z
      rw [show H z=M z from he,sub_self,abs_zero]
      exact mul_nonneg p.property.1.le (indicator_nonneg (fun X _ => add_nonneg
        (div_nonneg (norm_nonneg (fderiv ℝ (fderiv ℝ W)
          (WithLp.toLp 2 (gapVector X)))) p.property.1.le) zero_lt_one.le) (τ z))
    · have hm : fullFrozenMatrix p N θ h b D (τ z) = 1 := by
        simp only [fullFrozenMatrix, ite_eq_right hx]
      have he : Z (τ z) = ‖fderiv ℝ (fderiv ℝ W) (WithLp.toLp 2 (gapVector (τ z)))‖/p.val.1+1 :=
        indicator_of_mem hx _
      have hsW : ContDiffAt ℝ 2 W (WithLp.toLp 2 (gapVector (τ z))) :=
        (hW.of_le (by simp)).contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds
          (GapChart.gapVector_mem_gapAmbientDomain (τ z)))
      have hb : |hessianMatrix W (WithLp.toLp 2 (gapVector (τ z))) i j| ≤
          ‖fderiv ℝ (fderiv ℝ W) (WithLp.toLp 2 (gapVector (τ z)))‖ := by
        rw [PhysicalComparison.hessianMatrix_entry hsW]
        have ht := ContinuousLinearMap.le_opNorm₂ (fderiv ℝ (fderiv ℝ W)
          (WithLp.toLp 2 (gapVector (τ z)))) (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)
        simpa [EuclideanSpace.single,PiLp.norm_single] using ht
      have hi : |(1 : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ) i j| ≤ 1 := by
        simp only [Matrix.one_apply]; split_ifs <;> norm_num
      dsimp only [H,M,T]
      rw [hm, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, he, ← hz]
      apply (abs_sub _ _).trans
      rw [abs_mul,abs_of_pos p.property.1]
      have ht := add_le_add hb (mul_le_mul_of_nonneg_left hi p.property.1.le)
      convert ht using 1
      field_simp [p.property.1.ne']
  have hmax := internal_full_auxiliary_maximum p hs N hN θ h hh b D τ hτ ν Q hQ
    (zeroSumComponents _) (fun i => if i=i₀ then χ else 0) u hu
  rw [internal_point_source_essSup] at hmax
  have hU : ∀ᵐ z ∂ν, ‖(WithLp.toLp 2 (fun i => (u i).val z) : EuclideanSpace ℝ (Fin (N : ℕ)))‖ ≤ R := by
    have hle := ae_le_eLpNormEssSup (f := fun z => WithLp.toLp 2 (fun i => (u i).val z)) (μ := ν)
    rw [← eLpNorm_exponent_top (VectorRadial.memLp_values (fun i => (u i).val)).aestronglyMeasurable] at hle
    filter_upwards [hle] with z hz
    have ht := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hχ.ne) (hz.trans hmax)
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr ha.le),
      enorm_eq_nnnorm, ENNReal.coe_toReal, coe_nnnorm, R, a] using ht
  obtain ⟨g,hg,hgn⟩ := internal_action_of_envelope (fun z => H z-M z)
    (fun i j => (hHm i j).sub (hMm i j)) T hT hT0 (fun i => (u i).val) R
    (by dsimp only [R]; positivity) hentry hU
  refine ⟨g,hg,hgn.trans_eq ?_⟩
  have hn : eLpNorm T 2 ν = ENNReal.ofReal p.val.1*eLpNorm Z 2 μ := by
    change eLpNorm (p.val.1 • (Z ∘ τ)) 2 ν = _
    rw [eLpNorm_const_smul,Real.enorm_eq_ofReal_abs,abs_of_pos p.property.1,hnorm]
  rw [hn,ENNReal.toReal_mul,ENNReal.toReal_ofReal p.property.1.le]

/-- Full intrinsic realization with the physical ambient coercivity bound,
supporting Proposition 4.10. -/
theorem internal_full_realization (p : Parameters) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (θ : PhysicalCutoff) (h : ℝ) (b : Bool) :
    let ν := fullIntrinsicTiltedGapLaw p N θ h b
    let a := p.val.1*(p.val.2*(p.val.2+1))*(N : ℝ)^(-p.val.2-2)
    ∃ (W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ) (Q : ScalarFormData ν),
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = fullPhysicalPotentialValue p N hN θ h b y) ∧
      IsEuclideanGibbsPotential volume ν (intrinsicGapDomain N)
        (fun z => W (WithLp.toLp 2 (fun i => 1+z.val i))) ∧
      IsNeumannRealization (intrinsicGapDomain N) Q ∧
      IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
      let H := fun z : gapTangentSpace N => hessianMatrix W (WithLp.toLp 2 (fun i => 1+z.val i))
      (∀ᵐ z ∂ν, (H z).PosSemidef) ∧
      (∀ᵐ z ∂ν, ∀ t ∈ zeroSumComponents (Fin (N : ℕ)),
        a*(∑ i,t i^2) ≤ ∑ i,∑ j,t i*H z i j*t j) ∧
      ∀ f : Fin (N : ℕ) → Lp ℝ 2 ν,
        ∃! u : Fin (N : ℕ) → Q.1, WeightedWeakSolution Q H (zeroSumComponents _) f u := by
  intro ν a
  obtain ⟨_,_,_,W,Q,hW,hval,hG,hNeum,hQ,hcons,hsol⟩ := full_physical_wellposed p N hN θ h b
  obtain ⟨V,hV,hv,_,hl⟩ := full_physical_matrix_lower p N hN θ h b
  have hU := AffineMetric.intrinsicGapDomain_isOpen N
  have hsupport := IntrinsicScalarCore.supported hU hG
  have ha : 0 < a := mul_pos (mul_pos p.property.1
    (mul_pos p.property.2.1 (by linarith [p.property.2.1])))
      (Real.rpow_pos_of_pos (by positivity) _)
  let H := fun z : gapTangentSpace N => hessianMatrix W (WithLp.toLp 2 (fun i => 1+z.val i))
  have he (z : gapTangentSpace N) (hz : z ∈ intrinsicGapDomain N) :
      hessianMatrix W (WithLp.toLp 2 (fun i => 1+z.val i)) =
        hessianMatrix V (WithLp.toLp 2 (fun i => 1+z.val i)) := by
    have hx := PhysicalEnergy.simplex_subset_ambient N _
      (PhysicalCollision.intrinsic_chart_mem_simplex N hz)
    have heq : W =ᶠ[𝓝 (WithLp.toLp 2 (fun i => 1+z.val i))] V := by
      filter_upwards [(PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hx] with y hy
      exact (hval ⟨y,hy⟩).trans (hv ⟨y,hy⟩).symm
    have hWs : ContDiffAt ℝ 2 W (WithLp.toLp 2 (fun i => 1+z.val i)) :=
      (hW.of_le (by simp)).contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hx)
    have hVs : ContDiffAt ℝ 2 V (WithLp.toLp 2 (fun i => 1+z.val i)) :=
      (hV.of_le (by simp)).contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hx)
    ext i j
    rw [PhysicalComparison.hessianMatrix_entry hWs, PhysicalComparison.hessianMatrix_entry hVs,
      heq.fderiv.fderiv_eq]
  have hlow (z : gapTangentSpace N) (hz : z ∈ intrinsicGapDomain N) (t : Fin (N : ℕ) → ℝ) :
      a*(∑ i,t i^2) ≤ ∑ i,∑ j,t i*H z i j*t j := by
    dsimp only [H]
    rw [he z hz]
    exact hl z hz t
  refine ⟨W,Q,hW,hval,hG,hNeum,hQ,hcons,?_,hsupport.mono (fun z hz t _ => hlow z hz t),
    fun f => (hsol f).1⟩
  filter_upwards [hsupport] with z hz
  have hx := PhysicalEnergy.simplex_subset_ambient N _
    (PhysicalCollision.intrinsic_chart_mem_simplex N hz)
  have hWs := hW.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hx)
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    simp only [Matrix.conjTranspose_apply,star_trivial,Intrinsic.hessianMatrix_eq_second hWs]
    exact hWs.isSymmSndFDerivAt (by simp) _ _
  · intro t
    have ht := (mul_nonneg ha.le (Finset.sum_nonneg fun i _ => sq_nonneg (t i))).trans (hlow z hz t)
    simpa only [dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,Finset.mul_sum,mul_assoc] using ht

set_option backward.isDefEq.respectTransparency false in
/-- The full-cycle `N≥4` clause of Proposition 4.10, at
fixed temperature. This includes the law, normalizers, exact ambient
potential, intrinsic Neumann form, unique tangent solution, and component decay.
The loss exponent precedes the penalty scale and cutoff. -/
theorem full_physical_decay_fixed_beta (p : Parameters) (hs : 1 < p.val.2) :
    ∃ q : ℝ, 0 < q ∧ ∀ h : ℝ, 0 < h → ∃ δ : ℝ, 0 < δ ∧
      ∀ θ : PhysicalCutoff, ∃ A c : ℝ, 1 ≤ A ∧ 0 < c ∧
      ∀ (N : ℕ+) (hN : 4 ≤ (N : ℕ)) (b : Bool),
        let ν := fullIntrinsicTiltedGapLaw p N θ h b
        0 < tiltNormalizer p N N (le_refl _) θ h b ∧
        tiltNormalizer p N N (le_refl _) θ h b < ⊤ ∧ IsProbabilityMeasure ν ∧
        ∃ (W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ) (Q : ScalarFormData ν),
          ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
          (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
            W y.val = fullPhysicalPotentialValue p N (by omega) θ h b y) ∧
          IsEuclideanGibbsPotential volume ν (intrinsicGapDomain N)
            (fun z => W (WithLp.toLp 2 (fun i => 1+z.val i))) ∧
          IsNeumannRealization (intrinsicGapDomain N) Q ∧
          IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
          ∀ (i₀ : Fin (N : ℕ)) (χ : Lp ℝ 2 ν), eLpNorm χ ∞ ν < ⊤ →
          let H := fun z : gapTangentSpace N =>
            hessianMatrix W (WithLp.toLp 2 (fun i => 1+z.val i))
          (∃! u : Fin (N : ℕ) → Q.1, WeightedWeakSolution Q H
            (zeroSumComponents _) (fun i => if i=i₀ then χ else 0) u) ∧
          (∀ u : Fin (N : ℕ) → Q.1, WeightedWeakSolution Q H
            (zeroSumComponents _) (fun i => if i=i₀ then χ else 0) u →
            ∀ j : Fin (N : ℕ), ENNReal.ofReal ‖(u j).val‖ ≤
              ENNReal.ofReal (A*(N : ℝ)^(q*h)*
                ((1+(Riesz1.cyclicIndexDistance N j i₀ : ℝ))^(-p.val.2)+(N : ℝ)⁻¹)) *
                (ENNReal.ofReal ‖χ‖+ENNReal.ofReal (Real.exp (-c*(N : ℝ)^δ))*eLpNorm χ ∞ ν)) := by
  classical
  have hβ : 0 < p.val.1 := p.property.1
  have hk : 0 < p.val.1*(p.val.2*(p.val.2+1)) :=
    mul_pos hβ (mul_pos p.property.2.1 (by linarith [p.property.2.1]))
  obtain ⟨κ,hκ,henv⟩ := internal_full_exceptional_envelope p hs
  obtain ⟨r,hr,hdec⟩ := internal_full_auxiliary_decay p hs κ hκ.le
  refine ⟨r+1,by linarith,fun h hh => ?_⟩
  obtain ⟨δ,hδ,henv⟩ := henv h hh
  refine ⟨δ,hδ,fun θ => ?_⟩
  obtain ⟨A₀,hA₀,henv⟩ := henv θ
  obtain ⟨C₀,hC₀,hdec⟩ := hdec θ A₀ hA₀
  obtain ⟨C₁,c,hC₁,hc,henv⟩ := henv (p.val.2+4+(p.val.2+2)*h)
  obtain ⟨B,hB,hinsert⟩ := internal_insert_exponential_error (t := 1) hδ hc
  let k := p.val.1*(p.val.2*(p.val.2+1))
  let D₀ := C₀+k⁻¹*C₁
  let A := max 1 (B*D₀)
  refine ⟨A,c/2,le_max_left _ _,by positivity,?_⟩
  intro N hN b ν
  have hn0 : (0 : ℝ) < N := by positivity
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hN2 : 2 ≤ (N : ℕ) := by omega
  obtain ⟨hZ0,hZ1⟩ := DefinitionSanity.tilt_normalizer_valid p N N le_rfl θ h b
  let _ : IsProbabilityMeasure ν := DefinitionSanity.full_intrinsic_tilted_probability p N θ h b
  refine ⟨hZ0,hZ1.trans_lt ENNReal.one_lt_top,inferInstance,?_⟩
  obtain ⟨W,Q,hW,hval,hG,hNeum,hQ,hcons,hHb,hlow,hsol⟩ :=
    internal_full_realization p N hN2 θ h b
  refine ⟨W,Q,hW,hval,hG,hNeum,hQ,hcons,?_⟩
  obtain ⟨τ,hτ,hgap⟩ := internal_full_intrinsic_projection p N θ h b
  let H := fun z : gapTangentSpace N => hessianMatrix W (WithLp.toLp 2 (fun i => 1+z.val i))
  let a := k*(N : ℝ)^(-p.val.2-2)
  have ha : 0 < a := mul_pos hk (Real.rpow_pos_of_pos hn0 _)
  let D := A₀*(N : ℝ)^(κ*h)
  let M := fun z => p.val.1 • fullFrozenMatrix p N θ h b D (τ z)
  have hm := fullFrozenMatrix_measurable_symmetric p N θ h b D
  have hMm : ∀ i j, Measurable (fun z => M z i j) :=
    AbstractEnergy.scaled_measurable _ _ (fun i j => (hm.1 i j).comp hτ)
  have hMs : ∀ᵐ z ∂ν, ∀ i j, M z i j=M z j i := ae_of_all ν fun z i j =>
    congrArg (fun t : ℝ => p.val.1*t) (hm.2 (τ z) i j)
  have hHm : ∀ i j, Measurable (fun z => H z i j) := fun i j =>
    (DifferentiatedPoisson.measurable_hessian_entries (V := W) i j).comp
      (PhysicalCollision.intrinsic_chart_contDiff N).continuous.measurable
  have hD : 1 ≤ D := by
    have hp := Real.one_le_rpow hn1 (mul_nonneg hκ.le hh.le)
    dsimp only [D]
    nlinarith only [hA₀,hp,mul_nonneg (by linarith : 0 ≤ A₀-1)
      (by linarith : 0 ≤ (N : ℝ)^(κ*h)-1)]
  obtain ⟨Cθ,hCθ,hentry⟩ := fullFrozenMatrix_entry_bound θ
  have hMb : ∃ Bm : ℝ, ∀ᵐ z ∂ν, ∀ i j, |M z i j| ≤ Bm := by
    refine ⟨p.val.1*(D+Cθ*(N : ℝ)^(4*h)),ae_of_all ν fun z i j => ?_⟩
    simp only [M,Matrix.smul_apply,smul_eq_mul,abs_mul,abs_of_pos hβ]
    apply mul_le_mul_of_nonneg_left _ hβ.le
    apply (hentry p N h hh b D hD (τ z) i j).trans
    exact mul_le_of_le_one_right (by positivity)
      (Real.rpow_le_one_of_one_le_of_nonpos
        (le_add_of_nonneg_right (Nat.cast_nonneg _)) (by linarith [p.property.2.1]))
  let μ := tiltedParticleMeasure p N N le_rfl θ h b
  let E := (ExceptionalEvent.fullGoodEvent p N h D)ᶜ
  let Z := E.indicator (fun X =>
    ‖fderiv ℝ (fderiv ℝ W) (WithLp.toLp 2 (gapVector X))‖/p.val.1+1)
  obtain ⟨hZm,hZ,hZbound⟩ := henv N hN b W hval
  change Measurable Z at hZm
  change MemLp Z 2 μ at hZ
  change (N : ℝ)^(p.val.2+4+(p.val.2+2)*h)*(eLpNorm Z 2 μ).toReal ≤
    C₁*Real.exp (-c*(N : ℝ)^δ) at hZbound
  intro i₀ χ hχ
  refine ⟨hsol _,?_⟩
  intro u hu j
  obtain ⟨v,hv,_⟩ := (hdec h hh N hN2 b _ τ hτ ν Q hQ hcons i₀ χ).1
  obtain ⟨_,_,_,hvdec⟩ := (hdec h hh N hN2 b _ τ hτ ν Q hQ hcons i₀ χ).2 v hv
  obtain ⟨g,hg,hgn⟩ := internal_full_residual p hs N hN2 θ h hh b D W hW hval
    τ hτ hgap Q hQ i₀ χ hχ v hv hZm hZ
  change ‖WithLp.toLp 2 g‖ ≤ (N : ℝ)^2 *
    ((p.val.1*(N : ℝ)^(-(p.val.2+2)*h))⁻¹ * (eLpNorm χ ∞ ν).toReal) *
    (p.val.1*(eLpNorm Z 2 μ).toReal) at hgn
  have hcomp := (NaturalMatrixPerturbation.internal_comparison Q hQ H M hHm hMm
    hHb hMb hMs (zeroSumComponents _) a ha hlow (fun i => if i=i₀ then χ else 0)
      g u v hu hv hg).1
  have hainv : a⁻¹ = k⁻¹*(N : ℝ)^(p.val.2+2) := by
    dsimp only [a]
    rw [mul_inv_rev, ← Real.rpow_neg hn0.le]
    rw [show -(-p.val.2-2) = p.val.2+2 by ring,mul_comm]
  have hauxinv : (p.val.1*(N : ℝ)^(-(p.val.2+2)*h))⁻¹ =
      p.val.1⁻¹*(N : ℝ)^((p.val.2+2)*h) := by
    rw [mul_inv_rev, ← Real.rpow_neg hn0.le]
    rw [show -(-(p.val.2+2)*h) = (p.val.2+2)*h by ring,mul_comm]
  have herror : ‖WithLp.toLp 2 (fun i => (u i-v i).val)‖ ≤
      k⁻¹*C₁*Real.exp (-c*(N : ℝ)^δ)*(eLpNorm χ ∞ ν).toReal := by
    apply hcomp.trans
    apply (mul_le_mul_of_nonneg_left hgn (inv_nonneg.mpr ha.le)).trans
    calc
      _ = k⁻¹*((N : ℝ)^(p.val.2+4+(p.val.2+2)*h)*(eLpNorm Z 2 μ).toReal)*
          (eLpNorm χ ∞ ν).toReal := by
        have hpowers : (N : ℝ)^(p.val.2+4+(p.val.2+2)*h) =
            (N : ℝ)^(p.val.2+2)*(N : ℝ)^2*(N : ℝ)^((p.val.2+2)*h) := by
          rw [show p.val.2+4+(p.val.2+2)*h = (p.val.2+2)+2+(p.val.2+2)*h by ring,
            Real.rpow_add hn0,Real.rpow_add hn0,Real.rpow_two]
        rw [hainv,hauxinv,hpowers]
        field_simp [hβ.ne']
      _ ≤ _ := by
        calc
          _ ≤ k⁻¹*(C₁*Real.exp (-c*(N : ℝ)^δ))*(eLpNorm χ ∞ ν).toReal :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hZbound (show 0 ≤ k⁻¹ from inv_nonneg.mpr hk.le))
              ENNReal.toReal_nonneg
          _ = _ := by ring
  let P := (N : ℝ)^(r*h)
  let e := (1+(Riesz1.cyclicIndexDistance N j i₀ : ℝ))^(-p.val.2)+(N : ℝ)⁻¹
  have hP : 1 ≤ P := Real.one_le_rpow hn1 (mul_nonneg hr hh.le)
  have he0 : 0 ≤ e := by dsimp only [e]; positivity
  have hD0 : 0 ≤ D₀ := by dsimp only [D₀]; exact add_nonneg (by linarith) (mul_nonneg (inv_nonneg.mpr hk.le) hC₁.le)
  have hv' : ‖(v j).val‖ ≤ D₀*P*e*‖χ‖ := by
    apply (hvdec j).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg χ)
    apply mul_le_mul_of_nonneg_right _ he0
    apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans hP)
    exact le_add_of_nonneg_right (mul_nonneg (inv_nonneg.mpr hk.le) hC₁.le)
  have herr' : ‖(u j-v j).val‖ ≤ D₀*P*Real.exp (-c*(N : ℝ)^δ)*(eLpNorm χ ∞ ν).toReal := by
    apply (PiLp.norm_apply_le (WithLp.toLp 2 (fun i => (u i-v i).val)) j).trans
    apply herror.trans
    apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have hC : k⁻¹*C₁ ≤ D₀ := le_add_of_nonneg_left (by linarith)
    exact hC.trans (le_mul_of_one_le_right hD0 hP)
  have huj : (u j).val = (u j-v j).val+(v j).val := by
    change (u j).val = ((u j).val-(v j).val)+(v j).val
    abel
  have hnorm : ‖(u j).val‖ ≤ A*(N : ℝ)^((r+1)*h)*e*
      (‖χ‖+Real.exp (-(c/2)*(N : ℝ)^δ)*(eLpNorm χ ∞ ν).toReal) := by
    rw [huj]
    apply (norm_add_le _ _).trans ((add_le_add herr' hv').trans ?_)
    have ht := hinsert N (D₀*P) ‖χ‖ (eLpNorm χ ∞ ν).toReal e hn1
      (mul_nonneg hD0 (zero_le_one.trans hP)) (norm_nonneg _) ENNReal.toReal_nonneg
      (by dsimp only [e]; rw [Real.rpow_neg_one]; exact le_add_of_nonneg_left (by positivity))
    apply (show D₀*P*Real.exp (-c*(N : ℝ)^δ)*(eLpNorm χ ∞ ν).toReal+D₀*P*e*‖χ‖ =
      (D₀*P)*e*‖χ‖+(D₀*P)*Real.exp (-c*(N : ℝ)^δ)*(eLpNorm χ ∞ ν).toReal by ring).le.trans
    apply ht.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ he0
    calc
      _ = (B*D₀)*P := by ring
      _ ≤ A*(N : ℝ)^((r+1)*h) := mul_le_mul (le_max_right 1 (B*D₀))
        (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)) (by dsimp [P]; positivity)
        (by dsimp [A]; positivity)
  have ht := ENNReal.ofReal_le_ofReal hnorm
  rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_add (norm_nonneg _) (by positivity),
    ENNReal.ofReal_mul (Real.exp_pos _).le,ENNReal.ofReal_toReal hχ.ne] at ht
  exact ht

end Riesz2.DecayShort.PhysicalDecay
