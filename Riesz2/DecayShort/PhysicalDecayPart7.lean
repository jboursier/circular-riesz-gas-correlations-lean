/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.PhysicalDecayPart5
public import Riesz2.DecayShort.PhysicalDecayPart6
public import Riesz2.DecayShort.PaperPhysicalDecay

/-!
# Compact-temperature physical short-range decay

The full-cycle clause and joint statement of Proposition 4.10,
with common constants on compact positive temperature intervals.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology ContDiff

namespace Riesz2.DecayShort.PhysicalDecay

set_option backward.isDefEq.respectTransparency false in
/-- Uniform full-cycle exceptional envelope for Proposition 4.10.
The loss exponent precedes h and temperature. The prefactors are common on each
compact positive temperature interval. -/
theorem internal_full_exceptional_envelope_compact (s : ℝ) (hs : 1 < s) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ h : ℝ, 0 < h → ∃ δ : ℝ, 0 < δ ∧
      ∀ (θ : PhysicalCutoff) (βlo βhi : ℝ), 0 < βlo → βlo ≤ βhi →
      ∃ A : ℝ, 1 ≤ A ∧ ∀ a : ℝ,
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
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
  obtain ⟨κ,hκ,hprob⟩ := ExceptionalEvent.full_good_event_probability s hs
  refine ⟨κ,hκ,fun h hh => ?_⟩
  obtain ⟨δ,hδ,hprob⟩ := hprob h hh
  refine ⟨δ,hδ,fun θ βlo βhi hlo hle => ?_⟩
  obtain ⟨A,B,c,hA,hB,hc,hprob⟩ := hprob θ βlo βhi hlo hle
  obtain ⟨M,hM,hmom⟩ := ExceptionalEvent.full_hessian_fourth_moments
    s hs θ βlo βhi h hlo hle hh
  refine ⟨A,hA,fun a => ?_⟩
  obtain ⟨C,hC,hbound⟩ := ExceptionalEvent.internal_weighted_exceptional
    (d := 3) (a := a) hδ hc hB (show 0 < M+1 by linarith)
  refine ⟨C,c/8,hC,by positivity,?_⟩
  intro p hp hpl hph N hN b W hval μ E Z
  let _ : IsProbabilityMeasure μ := DefinitionSanity.tilted_probability p N N le_rfl θ h b
  obtain ⟨V,hV,hv,hmom⟩ := hmom p hp hpl hph N hN
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
    (hprob p hp hpl hph N hN b)
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict hE.nullMeasurableSet] at hb
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity)] at ht
  exact ht

set_option backward.isDefEq.respectTransparency false in
/-- Uniform full-cycle auxiliary decay and multiplier control for Proposition 4.10.
The loss exponent precedes h and temperature. The prefactors are common on each
compact positive temperature interval. -/
theorem internal_full_auxiliary_decay_compact (s : ℝ) (hs : 1 < s)
    (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ (θ : PhysicalCutoff) (A : ℝ), 1 ≤ A →
      ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (h : ℝ), 0 < h → ∀ (N : ℕ+), 2 ≤ (N : ℕ) →
      ∀ (b : Bool) (α : Type*) [MeasurableSpace α]
        (τ : α → Riesz1.Configuration N), Measurable τ →
      ∀ (ν : Measure α) [IsProbabilityMeasure ν] (Q : ScalarFormData ν),
        IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
      ∀ (i₀ : Fin (N : ℕ)) (χ : Lp ℝ 2 ν),
      let M := fun x => p.val.1 • fullFrozenMatrix p N θ h b (A*(N : ℝ)^(κ*h)) (τ x)
      let f := fun i => if i=i₀ then χ else 0
      (∃! u : Fin (N : ℕ) → Q.1,
        WeightedWeakSolution Q M (zeroSumComponents _) f u) ∧
      ∀ u : Fin (N : ℕ) → Q.1,
        WeightedWeakSolution Q M (zeroSumComponents _) f u →
        ∃ l : Lp ℝ 2 ν,
          (∀ᵐ x ∂ν, l x = gapMultiplierField N Q M f u x) ∧
          ‖l‖ ≤ C*(N : ℝ)^(r*h)*(N : ℝ)⁻¹*‖χ‖ ∧
          ∀ j : Fin (N : ℕ), ‖(u j).val‖ ≤ C*(N : ℝ)^(r*h)*
            ((1+(Riesz1.cyclicIndexDistance N j i₀ : ℝ))^(-p.val.2)+(N : ℝ)⁻¹)*‖χ‖ := by
  classical
  obtain ⟨r,hr,hdec⟩ := control_lambda_compact s hs
  let k := κ+s+6
  have hk : 0 ≤ k := by dsimp [k]; linarith
  refine ⟨r*k,mul_nonneg hr hk,fun θ A hA βlo βhi hlo hle => ?_⟩
  obtain ⟨C₀,hC₀,hdec⟩ := hdec βlo βhi hlo hle
  obtain ⟨Cθ,hCθ,hentry⟩ := fullFrozenMatrix_entry_bound θ
  let E := A+Cθ+1
  have hE : 1 ≤ E := by dsimp [E]; linarith
  have hE0 : 0 < E := lt_of_lt_of_le zero_lt_one hE
  have hEr : 1 ≤ E^r := Real.one_le_rpow hE hr
  refine ⟨C₀*E^r,(by nlinarith only [hC₀,hEr,mul_nonneg (by linarith : 0 ≤ C₀-1) (by linarith : 0 ≤ E^r-1)]),fun p hp hpl hph h hh N hN b α _ τ hτ ν _ Q hQ hcons i₀ χ => ?_⟩
  subst s
  have hs : 1 < p.val.2 := hs
  let B := E*(N : ℝ)^(k*h)
  let H := fun x => fullFrozenMatrix p N θ h b (A*(N : ℝ)^(κ*h)) (τ x)
  have hN0 : (0 : ℝ) < N := by positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hpow : 1 ≤ (N : ℝ)^(k*h) := Real.one_le_rpow hN1 (mul_nonneg hk hh.le)
  have hB : 1 ≤ B := by
    dsimp only [B]
    nlinarith only [hE,hpow,mul_nonneg (by linarith : 0 ≤ E-1) (by linarith : 0 ≤ (N : ℝ)^(k*h)-1)]
  have hD : 1 ≤ A*(N : ℝ)^(κ*h) := by
    have hp := Real.one_le_rpow hN1 (mul_nonneg hκ hh.le)
    nlinarith only [hA,hp,mul_nonneg (by linarith : 0 ≤ A-1) (by linarith : 0 ≤ (N : ℝ)^(κ*h)-1)]
  have hpm (t : ℝ) (ht : t ≤ k) : (N : ℝ)^(t*h) ≤ (N : ℝ)^(k*h) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (mul_le_mul_of_nonneg_right ht hh.le)
  have hκk : κ ≤ k := by dsimp [k]; linarith
  have h4k : 4 ≤ k := by dsimp [k]; linarith
  have hsk : p.val.2+2 ≤ k := by dsimp [k]; linarith
  have hBb : (N : ℝ)^((p.val.2+2)*h) ≤ B := (hpm _ hsk).trans
    (le_mul_of_one_le_left (by positivity) hE)
  have hBi : B⁻¹ ≤ (N : ℝ)^(-(p.val.2+2)*h) := by
    have hi := inv_anti₀ (Real.rpow_pos_of_pos hN0 ((p.val.2+2)*h)) hBb
    simpa only [← Real.rpow_neg hN0.le,neg_mul] using hi
  have hm := fullFrozenMatrix_measurable_symmetric p N θ h b (A*(N : ℝ)^(κ*h))
  have hHm : ∀ i j, Measurable (fun x => H x i j) := fun i j => (hm.1 i j).comp hτ
  have hbounds : ∀ᵐ x ∂ν, (∀ i j,H x i j=H x j i) ∧
      (∀ t : Fin (N : ℕ) → ℝ, B⁻¹*(∑ i,t i^2) ≤ ∑ i,∑ j,t i*H x i j*t j) ∧
      ∀ i j,|H x i j| ≤ B*(1+(Riesz1.cyclicIndexDistance N i j : ℝ))^(-p.val.2) := by
    apply ae_of_all
    intro x
    refine ⟨hm.2 (τ x),fun t => ?_,fun i j => ?_⟩
    · exact (mul_le_mul_of_nonneg_right hBi (Finset.sum_nonneg fun i _ => sq_nonneg (t i))).trans
        (fullFrozenMatrix_lower p hs N hN θ h hh b _ (τ x) t)
    · apply (hentry p N h hh b _ hD (τ x) i j).trans
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
      have h₁ := mul_le_mul_of_nonneg_left (hpm κ hκk) (show 0 ≤ A by linarith)
      have h₂ := mul_le_mul_of_nonneg_left (hpm 4 h4k) hCθ.le
      change A*(N : ℝ)^(κ*h)+Cθ*(N : ℝ)^(4*h) ≤ E*(N : ℝ)^(k*h)
      dsimp only [E]
      nlinarith only [h₁,h₂,Real.rpow_nonneg hN0.le (k*h)]
  let g : ComponentGeometry (Fin (N : ℕ)) := Sum.inr ⟨N,Function.Embedding.refl _⟩
  have hex := hdec p.val.1 ⟨hpl,hph⟩ α ν N Q hQ hcons g B hB H hHm hbounds i₀ χ
  have he : C₀*B^r = C₀*E^r*(N : ℝ)^((r*k)*h) := by
    dsimp only [B]
    rw [Real.mul_rpow hE0.le (Real.rpow_nonneg hN0.le _),← Real.rpow_mul hN0.le]
    rw [show k*h*r = (r*k)*h by ring]
    ring
  refine ⟨hex.1,fun u hu => ?_⟩
  obtain ⟨l,hl,hln,hcomp⟩ := hex.2 u hu
  rw [he] at hln hcomp
  exact ⟨l,hl,hln,hcomp⟩



set_option backward.isDefEq.respectTransparency false in
/-- Uniform physical full-cycle decay for N at least four for Proposition 4.10.
The loss exponent precedes h and temperature. The prefactors are common on each
compact positive temperature interval. -/
theorem full_physical_decay_compact_large (s : ℝ) (hs : 1 < s) :
    ∃ q : ℝ, 0 < q ∧ ∀ h : ℝ, 0 < h → ∃ δ : ℝ, 0 < δ ∧
      ∀ (θ : PhysicalCutoff) (βlo βhi : ℝ), 0 < βlo → βlo ≤ βhi →
      ∃ A c : ℝ, 1 ≤ A ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
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
  obtain ⟨κ,hκ,henv⟩ := internal_full_exceptional_envelope_compact s hs
  obtain ⟨r,hr,hdec⟩ := internal_full_auxiliary_decay_compact s hs κ hκ.le
  refine ⟨r+1,by linarith,fun h hh => ?_⟩
  obtain ⟨δ,hδ,henv⟩ := henv h hh
  refine ⟨δ,hδ,fun θ βlo βhi hlo hle => ?_⟩
  obtain ⟨A₀,hA₀,henv⟩ := henv θ βlo βhi hlo hle
  obtain ⟨C₀,hC₀,hdec⟩ := hdec θ A₀ hA₀ βlo βhi hlo hle
  obtain ⟨C₁,c,hC₁,hc,henv⟩ := henv (2+2*(s+2)*h)
  obtain ⟨B,hB,hinsert⟩ := internal_insert_exponential_error (t := 1) hδ hc
  let k₀ := βlo
  let D₀ := C₀+k₀⁻¹*C₁
  let A := max 1 (B*D₀)
  refine ⟨A,c/2,le_max_left _ _,by positivity,?_⟩
  intro p hp hpl hph
  subst s
  have hs : 1 < p.val.2 := hs
  have hβ : 0 < p.val.1 := p.property.1
  let k := p.val.1
  have hk : 0 < k := hβ
  have hk₀ : 0 < k₀ := hlo
  have hkinv : k⁻¹ ≤ k₀⁻¹ := inv_anti₀ hk₀ hpl
  have hdec := hdec p rfl hpl hph
  have henv := henv p rfl hpl hph
  intro N hN b ν
  have hn0 : (0 : ℝ) < N := by positivity
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hN2 : 2 ≤ (N : ℕ) := by omega
  obtain ⟨hZ0,hZ1⟩ := DefinitionSanity.tilt_normalizer_valid p N N le_rfl θ h b
  let _ : IsProbabilityMeasure ν := DefinitionSanity.full_intrinsic_tilted_probability p N θ h b
  refine ⟨hZ0,hZ1.trans_lt ENNReal.one_lt_top,inferInstance,?_⟩
  obtain ⟨W,Q,hW,hval,hG,hNeum,hQ,hcons,hHb,_,hsol⟩ :=
    internal_full_realization p N hN2 θ h b
  refine ⟨W,Q,hW,hval,hG,hNeum,hQ,hcons,?_⟩
  obtain ⟨τ,hτ,hgap⟩ := internal_full_intrinsic_projection p N θ h b
  let H := fun z : gapTangentSpace N => hessianMatrix W (WithLp.toLp 2 (fun i => 1+z.val i))
  let a := k*(N : ℝ)^(-(p.val.2+2)*h)
  have ha : 0 < a := mul_pos hk (Real.rpow_pos_of_pos hn0 _)
  have hlow : ∀ᵐ z ∂ν, ∀ t ∈ zeroSumComponents (Fin (N : ℕ)),
      a*(∑ i, t i^2) ≤ ∑ i, ∑ j, t i*H z i j*t j := by
    filter_upwards [IntrinsicScalarCore.supported (AffineMetric.intrinsicGapDomain_isOpen N) hG]
      with z hz t _
    exact full_physical_matrix_lower_scaled p hs N hN2 θ h hh b W hval z hz t
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
  change (N : ℝ)^(2+2*(p.val.2+2)*h)*(eLpNorm Z 2 μ).toReal ≤
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
  have hainv : a⁻¹ = k⁻¹*(N : ℝ)^((p.val.2+2)*h) := by
    dsimp only [a]
    rw [mul_inv_rev, ← Real.rpow_neg hn0.le]
    rw [show -(-(p.val.2+2)*h) = (p.val.2+2)*h by ring,mul_comm]
  have herror : ‖WithLp.toLp 2 (fun i => (u i-v i).val)‖ ≤
      k⁻¹*C₁*Real.exp (-c*(N : ℝ)^δ)*(eLpNorm χ ∞ ν).toReal := by
    apply hcomp.trans
    apply (mul_le_mul_of_nonneg_left hgn (inv_nonneg.mpr ha.le)).trans
    calc
      _ = k⁻¹*((N : ℝ)^(2+2*(p.val.2+2)*h)*(eLpNorm Z 2 μ).toReal)*
          (eLpNorm χ ∞ ν).toReal := by
        have hpowers : (N : ℝ)^(2+2*(p.val.2+2)*h) =
            (N : ℝ)^((p.val.2+2)*h)*(N : ℝ)^2*(N : ℝ)^((p.val.2+2)*h) := by
          rw [show 2+2*(p.val.2+2)*h = ((p.val.2+2)*h)+2+(p.val.2+2)*h by ring,
            Real.rpow_add hn0,Real.rpow_add hn0,Real.rpow_two]
        rw [hainv,hpowers]
        dsimp only [k]
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
  have hD0 : 0 ≤ D₀ := by dsimp only [D₀]; exact add_nonneg (by linarith) (mul_nonneg (inv_nonneg.mpr hk₀.le) hC₁.le)
  have hv' : ‖(v j).val‖ ≤ D₀*P*e*‖χ‖ := by
    apply (hvdec j).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg χ)
    apply mul_le_mul_of_nonneg_right _ he0
    apply mul_le_mul_of_nonneg_right _ (zero_le_one.trans hP)
    exact le_add_of_nonneg_right (mul_nonneg (inv_nonneg.mpr hk₀.le) hC₁.le)
  have herr' : ‖(u j-v j).val‖ ≤ D₀*P*Real.exp (-c*(N : ℝ)^δ)*(eLpNorm χ ∞ ν).toReal := by
    apply (PiLp.norm_apply_le (WithLp.toLp 2 (fun i => (u i-v i).val)) j).trans
    apply herror.trans
    apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have hC : k⁻¹*C₁ ≤ D₀ := (mul_le_mul_of_nonneg_right hkinv hC₁.le).trans
      (le_add_of_nonneg_left (by linarith))
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


set_option backward.isDefEq.respectTransparency false in
/-- Uniform small-volume physical decay for Proposition 4.10.
The constant precedes every positive temperature above βlo and both penalties. -/
theorem full_physical_decay_two_three_compact (s βlo : ℝ) (hs : 1 < s) (hlo : 0 < βlo) :
    ∃ A : ℝ, 0 < A ∧ ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → ∀ (θ : PhysicalCutoff) (h : ℝ)
      (N : ℕ+) (hN : 2 ≤ (N : ℕ)), (N : ℕ) ≤ 3 → ∀ b : Bool,
    let ν := fullIntrinsicTiltedGapLaw p N θ h b
    0 < tiltNormalizer p N N (le_refl _) θ h b ∧
      tiltNormalizer p N N (le_refl _) θ h b < ⊤ ∧ IsProbabilityMeasure ν ∧
    ∃ (W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ) (Q : ScalarFormData ν),
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = fullPhysicalPotentialValue p N hN θ h b y) ∧
      IsEuclideanGibbsPotential volume ν (intrinsicGapDomain N)
        (fun z => W (WithLp.toLp 2 (fun i => 1 + z.val i))) ∧
      IsNeumannRealization (intrinsicGapDomain N) Q ∧
      IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
      ∀ (i₀ : Fin (N : ℕ)) (χ : Lp ℝ 2 ν),
      let M := fun z : gapTangentSpace N => hessianMatrix W
        (WithLp.toLp 2 (fun i => 1 + z.val i))
      (∃! u : Fin (N : ℕ) → Q.1,
        WeightedWeakSolution Q M (zeroSumComponents _)
          (fun i => if i=i₀ then χ else 0) u) ∧
      ∀ u : Fin (N : ℕ) → Q.1,
        WeightedWeakSolution Q M (zeroSumComponents _)
          (fun i => if i=i₀ then χ else 0) u →
        ∀ j : Fin (N : ℕ), ‖(u j).val‖ ≤
          A*((1+(Riesz1.cyclicIndexDistance N j i₀ : ℝ))^(-p.val.2)+(N : ℝ)⁻¹)*‖χ‖ := by
  classical
  let a₃ := βlo*(s*(s+1))*(3 : ℝ)^(-s-2)
  have ha₃ : 0 < a₃ := mul_pos (mul_pos hlo
    (mul_pos (by linarith : 0 < s) (by linarith : 0 < s+1)))
    (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨3*a₃⁻¹,by positivity,?_⟩
  intro p hp hpl θ h N hN hN3 b ν
  subst s
  have hs0 : 0 < p.val.2 := by linarith
  obtain ⟨hZ,hZt,hprob,W,Q,hW,hval,hG,hreal,hQ,hcons,hsol⟩ :=
    full_physical_wellposed p N hN θ h b
  refine ⟨hZ,hZt,hprob,W,Q,hW,hval,hG,hreal,hQ,hcons,?_⟩
  intro i₀ χ M
  refine ⟨(hsol (fun i => if i=i₀ then χ else 0)).1,?_⟩
  intro u hu j
  have hn := (hsol (fun i => if i=i₀ then χ else 0)).2 u hu
  have hf : ‖WithLp.toLp 2 (fun i : Fin (N : ℕ) => if i=i₀ then χ else 0)‖ = ‖χ‖ := by
    convert PiLp.norm_single 2 (fun _ : Fin (N : ℕ) => Lp ℝ 2 ν) i₀ χ using 1
    congr 1
    apply PiLp.ext
    intro i
    simp only [PiLp.single_apply]
  rw [hf] at hn
  have hpow := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < N)
    (show (N : ℝ) ≤ 3 by exact_mod_cast hN3) (by linarith [p.property.2.1] : -p.val.2-2 ≤ 0)
  have ha : a₃ ≤ p.val.1*(p.val.2*(p.val.2+1))*(N : ℝ)^(-p.val.2-2) :=
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpl (by positivity)) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hpow (mul_nonneg p.property.1.le (by positivity)))
  have hnorm : ‖(u j).val‖ ≤ a₃⁻¹*‖χ‖ := (PiLp.norm_apply_le
    (WithLp.toLp 2 (fun i => (u i).val)) j).trans (hn.trans
      (mul_le_mul_of_nonneg_right (inv_anti₀ ha₃ ha) (norm_nonneg _)))
  have hN0 : (0 : ℝ) < N := by positivity
  have hinv : (1/3 : ℝ) ≤ (N : ℝ)⁻¹ := by
    simpa only [one_div] using inv_anti₀ hN0 (show (N : ℝ) ≤ 3 by exact_mod_cast hN3)
  have hprofile : (1/3 : ℝ) ≤
      (1+(Riesz1.cyclicIndexDistance N j i₀ : ℝ))^(-p.val.2)+(N : ℝ)⁻¹ :=
    hinv.trans (le_add_of_nonneg_left (Real.rpow_nonneg (by positivity) _))
  apply hnorm.trans
  have hp := mul_le_mul_of_nonneg_left hprofile (show 0 ≤ 3*a₃⁻¹ by positivity)
  have he : a₃⁻¹ ≤ 3*a₃⁻¹*
      ((1+(Riesz1.cyclicIndexDistance N j i₀ : ℝ))^(-p.val.2)+(N : ℝ)⁻¹) := by
    nlinarith only [hp]
  exact mul_le_mul_of_nonneg_right he (norm_nonneg _)

/-- Internal monotonicity of the extended decay expression in Proposition 4.10, used to give both clauses common constants. -/
theorem internal_decay_rhs_mono {n h q q' δ δ' A A' c c' e : ℝ}
    (hn : 1 ≤ n) (hh : 0 ≤ h) (hA : 0 ≤ A) (hAA : A ≤ A')
    (hqq : q ≤ q') (hδδ : δ' ≤ δ) (hc : 0 ≤ c') (hcc : c' ≤ c)
    (he : 0 ≤ e) (X Y : ℝ≥0∞) :
    ENNReal.ofReal (A*n^(q*h)*e) *
        (X+ENNReal.ofReal (Real.exp (-c*n^δ))*Y) ≤
      ENNReal.ofReal (A'*n^(q'*h)*e) *
        (X+ENNReal.ofReal (Real.exp (-c'*n^δ'))*Y) := by
  have hpow := Real.rpow_le_rpow_of_exponent_le hn
    (mul_le_mul_of_nonneg_right hqq hh)
  have htail := Real.rpow_le_rpow_of_exponent_le hn hδδ
  apply mul_le_mul'
  · apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hAA hpow (Real.rpow_nonneg (by linarith) _) (hA.trans hAA)) he
  · apply add_le_add le_rfl
    refine mul_le_mul' ?_ le_rfl
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have ht := mul_le_mul hcc htail (Real.rpow_nonneg (by linarith) _) (hc.trans hcc)
    linarith

/-- Complete full-cycle clause of Proposition 4.10, including
N=2,3, with the stated quantifier order and compact-temperature uniformity. -/
theorem full_physical_decay_compact :
  ∀ s : ShortExponent, ∃ q : ℝ, 0 < q ∧
  ∀ h : ℝ, 0 < h → ∃ δ : ℝ, 0 < δ ∧
  ∀ θ : PhysicalCutoff, ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
  ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
  let p := ofShort β s
  ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (b : Bool),
    let ν := fullIntrinsicTiltedGapLaw p N θ h b
    0 < tiltNormalizer p N N (le_refl _) θ h b ∧
    tiltNormalizer p N N (le_refl _) θ h b < ⊤ ∧ IsProbabilityMeasure ν ∧
    ∃ (W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ) (Q : ScalarFormData ν),
      ContDiffOn ℝ (⊤ : ℕ∞) W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = fullPhysicalPotentialValue p N hN θ h b y) ∧
      IsEuclideanGibbsPotential volume ν (intrinsicGapDomain N)
        (fun z => W (WithLp.toLp 2 (fun i => 1 + z.val i))) ∧
      IsNeumannRealization (intrinsicGapDomain N) Q ∧
      IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
      ∀ (i₀ : Fin (N : ℕ)) (χ : Lp ℝ 2 ν), eLpNorm χ ∞ ν < ⊤ →
      let M := fun z : gapTangentSpace N =>
        hessianMatrix W (WithLp.toLp 2 (fun i => 1 + z.val i))
      (∃! u : Fin (N : ℕ) → Q.1, WeightedWeakSolution Q M
        (zeroSumComponents _) (fun i => if i = i₀ then χ else 0) u) ∧
      (∀ u : Fin (N : ℕ) → Q.1, WeightedWeakSolution Q M
          (zeroSumComponents _) (fun i => if i = i₀ then χ else 0) u →
        ∀ j : Fin (N : ℕ), ENNReal.ofReal ‖(u j).val‖ ≤
          ENNReal.ofReal (A * (N : ℝ) ^ (q * h) *
            ((1 + (Riesz1.cyclicIndexDistance N j i₀ : ℝ)) ^ (-s.val) + (N : ℝ)⁻¹)) *
            (ENNReal.ofReal ‖χ‖ + ENNReal.ofReal (Real.exp (-c * (N : ℝ) ^ δ)) *
              eLpNorm χ ∞ ν)) := by
  intro s
  obtain ⟨q,hq,hlarge⟩ := full_physical_decay_compact_large s.val s.property
  refine ⟨q,hq,fun h hh => ?_⟩
  obtain ⟨δ,hδ,hlarge⟩ := hlarge h hh
  refine ⟨δ,hδ,fun θ βlo βhi hlo hle => ?_⟩
  obtain ⟨Aₗ,c,hAₗ,hc,hlarge⟩ := hlarge θ βlo βhi hlo hle
  obtain ⟨Aₛ,hAₛ,hsmall⟩ := full_physical_decay_two_three_compact s.val βlo s.property hlo
  let A := max Aₗ Aₛ
  have hA : 0 < A := hAₛ.trans_le (le_max_right _ _)
  refine ⟨A,c,hA,hc,fun β hβ => ?_⟩
  intro p N hN b ν
  by_cases hN4 : 4 ≤ (N : ℕ)
  · obtain ⟨hZ0,hZt,hprob,W,Q,hW,hval,hG,hNeum,hQ,hcons,hsol⟩ :=
      hlarge p rfl hβ.1 hβ.2 N hN4 b
    refine ⟨hZ0,hZt,hprob,W,Q,hW,hval,hG,hNeum,hQ,hcons,?_⟩
    intro i₀ χ hχ M
    refine ⟨(hsol i₀ χ hχ).1,?_⟩
    intro u hu j
    apply ((hsol i₀ χ hχ).2 u hu j).trans
    apply internal_decay_rhs_mono (by exact_mod_cast N.pos) hh.le
      (by linarith) (le_max_left _ _) le_rfl le_rfl hc.le le_rfl (by positivity)
  · obtain ⟨hZ0,hZt,hprob,W,Q,hW,hval,hG,hNeum,hQ,hcons,hsol⟩ :=
      hsmall p rfl hβ.1 θ h N hN (by omega) b
    refine ⟨hZ0,hZt,hprob,W,Q,hW,hval,hG,hNeum,hQ,hcons,?_⟩
    intro i₀ χ _hχ M
    refine ⟨(hsol i₀ χ).1,?_⟩
    intro u hu j
    have hb := ENNReal.ofReal_le_ofReal ((hsol i₀ χ).2 u hu j)
    rw [ENNReal.ofReal_mul (by positivity)] at hb
    apply hb.trans
    have hpow : 1 ≤ (N : ℝ)^(q*h) := Real.one_le_rpow
      (by exact_mod_cast N.pos) (mul_nonneg hq.le hh.le)
    have hfactor : Aₛ ≤ A*(N : ℝ)^(q*h) := (le_max_right _ _).trans
      (le_mul_of_one_le_right hA.le hpow)
    apply mul_le_mul'
    · apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right hfactor (by positivity)
    · exact le_add_of_nonneg_right zero_le

/-- See Proposition 4.10 of the paper: the joint physical short-range decay
statement with common constants. -/
theorem physical_decay :
  ∀ s : ShortExponent, ∃ q : ℝ, 0 < q ∧
  ∀ h : ℝ, 0 < h → ∃ δ : ℝ, 0 < δ ∧
  ∀ θ : PhysicalCutoff, ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
  ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
  let p := ofShort β s
  (∀ (N n : ℕ+) (_ : 4 ≤ (N : ℕ)) (_ : 2 ≤ (n : ℕ)),
    2 * (n : ℕ) ≤ (N : ℕ) → ∀ hn : (n : ℕ) ≤ (N : ℕ), ∀ b : Bool,
    let ν := activeTiltedGapLaw p N n hn θ h b
    0 < tiltNormalizer p N n hn θ h b ∧ tiltNormalizer p N n hn θ h b < ⊤ ∧
    IsProbabilityMeasure ν ∧
    ∃ (V : EuclideanSpace ℝ (Fin (n : ℕ)) → ℝ) (Q : ScalarFormData ν),
      IsEuclideanGibbsPotential volume ν (properMarginalDomain n N) V ∧
      IsNeumannRealization (properMarginalDomain n N) Q ∧
      IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
      ∀ i₀ : Fin (n : ℕ), (n : ℕ) ≤ 4 * (i₀.val + 1) →
        4 * (i₀.val + 1) ≤ 3 * (n : ℕ) →
        ∀ χ : Lp ℝ 2 ν, eLpNorm χ ∞ ν < ⊤ →
        (∃! u : Fin (n : ℕ) → Q.1,
          WeightedWeakSolution Q (hessianMatrix V) ⊤ (fun i => if i = i₀ then χ else 0) u) ∧
        (∀ u : Fin (n : ℕ) → Q.1,
          WeightedWeakSolution Q (hessianMatrix V) ⊤ (fun i => if i = i₀ then χ else 0) u →
          ∀ j : Fin (n : ℕ), ENNReal.ofReal ‖(u j).val‖ ≤
            ENNReal.ofReal (A * (n : ℝ) ^ (q * h) *
              ((1 + |(j.val : ℝ) - (i₀.val : ℝ)|) ^ (-s.val) +
                (n : ℝ) ^ (-(s.val - 1 / 2)) + (N : ℝ) ^ (-(1 / 2 : ℝ)))) *
              (ENNReal.ofReal ‖χ‖ + ENNReal.ofReal (Real.exp (-c * (n : ℝ) ^ δ)) *
                eLpNorm χ ∞ ν))) ∧
  (∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (b : Bool),
    let ν := fullIntrinsicTiltedGapLaw p N θ h b
    0 < tiltNormalizer p N N (le_refl _) θ h b ∧
    tiltNormalizer p N N (le_refl _) θ h b < ⊤ ∧ IsProbabilityMeasure ν ∧
    ∃ (W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ) (Q : ScalarFormData ν),
      ContDiffOn ℝ (⊤ : ℕ∞) W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = fullPhysicalPotentialValue p N hN θ h b y) ∧
      IsEuclideanGibbsPotential volume ν (intrinsicGapDomain N)
        (fun z => W (WithLp.toLp 2 (fun i => 1 + z.val i))) ∧
      IsNeumannRealization (intrinsicGapDomain N) Q ∧
      IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
      ∀ (i₀ : Fin (N : ℕ)) (χ : Lp ℝ 2 ν), eLpNorm χ ∞ ν < ⊤ →
      let M := fun z : gapTangentSpace N =>
        hessianMatrix W (WithLp.toLp 2 (fun i => 1 + z.val i))
      (∃! u : Fin (N : ℕ) → Q.1, WeightedWeakSolution Q M
        (zeroSumComponents _) (fun i => if i = i₀ then χ else 0) u) ∧
      (∀ u : Fin (N : ℕ) → Q.1, WeightedWeakSolution Q M
          (zeroSumComponents _) (fun i => if i = i₀ then χ else 0) u →
        ∀ j : Fin (N : ℕ), ENNReal.ofReal ‖(u j).val‖ ≤
          ENNReal.ofReal (A * (N : ℝ) ^ (q * h) *
            ((1 + (Riesz1.cyclicIndexDistance N j i₀ : ℝ)) ^ (-s.val) + (N : ℝ)⁻¹)) *
            (ENNReal.ofReal ‖χ‖ + ENNReal.ofReal (Real.exp (-c * (N : ℝ) ^ δ)) *
              eLpNorm χ ∞ ν))) := by
  intro s
  obtain ⟨qₚ,hqₚ,hproper⟩ := proper_physical_decay_compact s
  obtain ⟨q𝒻,hq𝒻,hfull⟩ := full_physical_decay_compact s
  let q := max qₚ q𝒻
  refine ⟨q,hqₚ.trans_le (le_max_left _ _),fun h hh => ?_⟩
  obtain ⟨δₚ,hδₚ,hproper⟩ := hproper h hh
  obtain ⟨δ𝒻,hδ𝒻,hfull⟩ := hfull h hh
  let δ := min δₚ δ𝒻
  refine ⟨δ,lt_min hδₚ hδ𝒻,fun θ βlo βhi hlo hle => ?_⟩
  obtain ⟨Aₚ,cₚ,hAₚ,hcₚ,hproper⟩ := hproper θ βlo βhi hlo hle
  obtain ⟨A𝒻,c𝒻,hA𝒻,hc𝒻,hfull⟩ := hfull θ βlo βhi hlo hle
  let A := max Aₚ A𝒻
  let c := min cₚ c𝒻
  have hA : 0 < A := hAₚ.trans_le (le_max_left _ _)
  have hc : 0 < c := lt_min hcₚ hc𝒻
  refine ⟨A,c,hA,hc,fun β hβ => ?_⟩
  intro p
  constructor
  · intro N n hN hn2 hhalf hn b ν
    obtain ⟨hZ0,hZt,hprob,V,Q,hV,hNeum,hQ,hcons,hsol⟩ :=
      hproper β hβ N n hN hn2 hhalf hn b
    refine ⟨hZ0,hZt,hprob,V,Q,hV,hNeum,hQ,hcons,?_⟩
    intro i₀ hlo hhi χ hχ
    refine ⟨(hsol i₀ hlo hhi χ hχ).1,?_⟩
    intro u hu j
    apply ((hsol i₀ hlo hhi χ hχ).2 u hu j).trans
    apply internal_decay_rhs_mono (by exact_mod_cast n.pos) hh.le
      hAₚ.le (le_max_left _ _) (le_max_left _ _) (min_le_left _ _) hc.le
      (min_le_left _ _) (by positivity)
  · intro N hN b ν
    obtain ⟨hZ0,hZt,hprob,W,Q,hW,hval,hG,hNeum,hQ,hcons,hsol⟩ :=
      hfull β hβ N hN b
    refine ⟨hZ0,hZt,hprob,W,Q,hW,hval,hG,hNeum,hQ,hcons,?_⟩
    intro i₀ χ hχ M
    refine ⟨(hsol i₀ χ hχ).1,?_⟩
    intro u hu j
    apply ((hsol i₀ χ hχ).2 u hu j).trans
    apply internal_decay_rhs_mono (by exact_mod_cast N.pos) hh.le
      hA𝒻.le (le_max_right _ _) (le_max_right _ _) (min_le_right _ _) hc.le
      (min_le_right _ _) (by positivity)

end Riesz2.DecayShort.PhysicalDecay
