/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.ConvexLocalization
public import Riesz2.ToMathlib.DominatedFibreRegularity
public import Riesz2.ToMathlib.DominatedDensityForce
public import Riesz2.ToMathlib.ConvexSecondDerivativeAt
public import Riesz1.ToMathlib.LogConcave.PrekopaFrontier
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Smooth convex localization

The C² regularity and separated Hessian formula of Lemma 3.5.
First and second density derivatives are integrated under the local
domination hypotheses.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Riesz2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {m : ℕ} {Ω : Set (E × EuclideanSpace ℝ (Fin m))}
  {H₂ : E × EuclideanSpace ℝ (Fin m) → ℝ}

namespace ConvexLocalizationInternal

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Off the joint frontier, the zero-extended second density derivative is
continuous in the base variable. Used to prove the regularity conclusion of
Lemma 3.5. -/
theorem continuousAt_second_density (hΩo : IsOpen Ω)
    (hH₂ : ContDiffOn ℝ 2 H₂ Ω) {x : E} {y : EuclideanSpace ℝ (Fin m)}
    (hy : (x, y) ∉ frontier Ω) :
    ContinuousAt (fun z =>
      Ω.indicator (fun p => Real.exp (-H₂ p)) (z, y) •
        ((fderiv ℝ (fun t => H₂ (t, y)) z).smulRight
          (fderiv ℝ (fun t => H₂ (t, y)) z) -
          fderiv ℝ (fderiv ℝ (fun t => H₂ (t, y))) z)) x := by
  have hline : Continuous (fun z : E => (z, y)) := by fun_prop
  by_cases hin : (x, y) ∈ Ω
  · let U : Set E := {z | (z, y) ∈ Ω}
    have ho : IsOpen U := hΩo.preimage hline
    have hc : ContDiffOn ℝ 2 (fun z => H₂ (z, y)) U :=
      hH₂.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ hz => hz)
    have hv : ContinuousAt (fun z => H₂ (z, y)) x :=
      hc.continuousOn.continuousAt (ho.mem_nhds hin)
    have hs : ContinuousAt (fun z => fderiv ℝ (fun t => H₂ (t, y)) z) x :=
      (hc.fderiv_of_isOpen ho (by norm_num : 1 + 1 ≤ (2 : WithTop ℕ∞))).continuousOn.continuousAt
        (ho.mem_nhds hin)
    have ht : ContinuousAt
        (fun z => fderiv ℝ (fderiv ℝ (fun t => H₂ (t, y))) z) x :=
      ((hc.fderiv_of_isOpen ho (by norm_num : 1 + 1 ≤ (2 : WithTop ℕ∞))).fderiv_of_isOpen
        ho (by norm_num : 0 + 1 ≤ (1 : WithTop ℕ∞))).continuousOn.continuousAt
          (ho.mem_nhds hin)
    have he : (fun z => Ω.indicator (fun p => Real.exp (-H₂ p)) (z, y)) =ᶠ[𝓝 x]
        fun z => Real.exp (-H₂ (z, y)) := by
      filter_upwards [ho.mem_nhds hin] with z hz
      exact indicator_of_mem (show (z, y) ∈ Ω from hz) (fun p => Real.exp (-H₂ p))
    have hw : ContinuousAt
        (fun z => Ω.indicator (fun p => Real.exp (-H₂ p)) (z, y)) x :=
      ContinuousAt.congr (Real.continuous_exp.continuousAt.comp hv.neg) he.symm
    have hss : ContinuousAt (fun z =>
        (fderiv ℝ (fun t => H₂ (t, y)) z).smulRight
          (fderiv ℝ (fun t => H₂ (t, y)) z)) x :=
      (isBoundedBilinearMap_smulRight
        (𝕜 := ℝ) (E := E) (F := E →L[ℝ] ℝ)).continuous.continuousAt.comp (hs.prodMk hs)
    exact hw.smul (hss.sub ht)
  · have hout : (x, y) ∈ (closure Ω)ᶜ := by
      intro hcl
      exact hy ⟨hcl, by simpa only [hΩo.interior_eq] using hin⟩
    have he : (fun z =>
        Ω.indicator (fun p => Real.exp (-H₂ p)) (z, y) •
          ((fderiv ℝ (fun t => H₂ (t, y)) z).smulRight
            (fderiv ℝ (fun t => H₂ (t, y)) z) -
            fderiv ℝ (fderiv ℝ (fun t => H₂ (t, y))) z)) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [((isClosed_closure.isOpen_compl).preimage hline).mem_nhds hout]
        with z hz
      rw [indicator_of_notMem (fun hz' => hz (subset_closure hz'))
        (fun p => Real.exp (-H₂ p))]
      ext u v
      simp
    exact ContinuousAt.congr continuousAt_const he.symm

end ConvexLocalizationInternal

/-- See Lemma 3.5 of the paper, C² conclusion under its local
domination assumptions. Continuity of the integrated second derivative is
proved using the null frontier section of each interior fibre. -/
theorem convexLocalization_contDiff (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hΩb : Bornology.IsBounded Ω) (hH₂c : ConvexOn ℝ Ω H₂)
    (hH₂ : ContDiffOn ℝ 2 H₂ Ω) (H₁ : E → ℝ)
    (hH₁ : ContDiffOn ℝ 2 H₁ (Prod.fst '' Ω)) :
    let w := fun x y => Ω.indicator (fun p => Real.exp (-H₂ p)) (x, y)
    let S := fun x y => fderiv ℝ (fun z => H₂ (z, y)) x
    let T := fun x y => fderiv ℝ (fderiv ℝ (fun z => H₂ (z, y))) x
    DominatedFibre.DominatedFDerivOn volume (Prod.fst '' Ω) w (fun x y => -w x y • S x y) →
    DominatedFibre.DominatedFDerivOn volume (Prod.fst '' Ω)
      (fun x y => -w x y • S x y)
      (fun x y => w x y • ((S x y).smulRight (S x y) - T x y)) →
    ContDiffOn ℝ 2 (fun x => H₁ x - Real.log (∫ y, w x y)) (Prod.fst '' Ω) := by
  intro w S T hdom hdom'
  have hp (x) (hx : x ∈ Prod.fst '' Ω) : 0 < ∫ y, w x y :=
    Riesz1.marginal_exp_indicator_pos hΩo hΩb hH₂c
      (Riesz1.exists_fiber_of_mem_fst_image hx)
  apply hH₁.sub
  apply ContDiffOn.log _ (fun x hx => (hp x hx).ne')
  apply DominatedFibre.contDiffOn_integral_two (isOpenMap_fst _ hΩo) hdom hdom'
  intro x hx
  have hnull := Riesz1.volume_section_frontier_eq_zero hΩo hΩc
    (Riesz1.exists_fiber_of_mem_fst_image hx)
  have hae : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      (x, y) ∉ frontier Ω := by
    rw [ae_iff]
    simpa only [not_not] using hnull
  exact hae.mono fun y hy => ConvexLocalizationInternal.continuousAt_second_density hΩo hH₂ hy

/-- See Lemma 3.5 of the paper, separated Hessian/covariance
identity. Both conditional forces are L² and the conditional energy Hessian
is integrable under the two density domination assumptions themselves. -/
theorem convexLocalization_hessian (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hΩb : Bornology.IsBounded Ω) (hH₂c : ConvexOn ℝ Ω H₂)
    (hH₂ : ContDiffOn ℝ 2 H₂ Ω) (H₁ : E → ℝ)
    (hH₁ : ContDiffOn ℝ 2 H₁ (Prod.fst '' Ω)) :
    let w := fun x y => Ω.indicator (fun p => Real.exp (-H₂ p)) (x, y)
    let S := fun x y => fderiv ℝ (fun z => H₂ (z, y)) x
    let T := fun x y => fderiv ℝ (fderiv ℝ (fun z => H₂ (z, y))) x
    DominatedFibre.DominatedFDerivOn volume (Prod.fst '' Ω) w (fun x y => -w x y • S x y) →
    DominatedFibre.DominatedFDerivOn volume (Prod.fst '' Ω)
      (fun x y => -w x y • S x y)
      (fun x y => w x y • ((S x y).smulRight (S x y) - T x y)) →
    ∀ x (hx : x ∈ Prod.fst '' Ω) (u v : E),
      let ρ := AffineFibre.convexConditionalMeasure hΩo hΩb hH₂c ⟨x, hx⟩
      MemLp (fun y => S x y u) 2 ρ ∧ MemLp (fun y => S x y v) 2 ρ ∧
      Integrable (fun y => T x y u v) ρ ∧
      fderiv ℝ (fderiv ℝ (fun z => H₁ z - Real.log (∫ y, w z y))) x u v =
        fderiv ℝ (fderiv ℝ H₁) x u v + (∫ y, T x y u v ∂ρ) -
          ProbabilityTheory.covariance (fun y => S x y u) (fun y => S x y v) ρ := by
  intro w S T hdom hdom' x hx u v ρ
  have ho : IsOpen (Prod.fst '' Ω) := isOpenMap_fst _ hΩo
  have hn (z) (_ : z ∈ Prod.fst '' Ω) (y) : 0 ≤ w z y :=
    indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
  have hp (z) (hz : z ∈ Prod.fst '' Ω) : 0 < ∫ y, w z y :=
    Riesz1.marginal_exp_indicator_pos hΩo hΩb hH₂c
      (Riesz1.exists_fiber_of_mem_fst_image hz)
  have hf : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      -w x y • S x y = -w x y • S x y := Eventually.of_forall fun _ => rfl
  have hsecond : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin m))),
      w x y • ((S x y).smulRight (S x y) - T x y) =
        w x y • ((S x y).smulRight (S x y) - T x y) := Eventually.of_forall fun _ => rfl
  have hiT := DominatedFibre.integrable_weighted_gibbs_hessian
    hdom hdom' hn hx (hp x hx) (S x) (T x) hf hsecond u v
  refine ⟨DominatedFibre.memLp_gibbs_force hdom hdom' hn hx (hp x hx) (S x) hf u,
    DominatedFibre.memLp_gibbs_force hdom hdom' hn hx (hp x hx) (S x) hf v,
    (DominatedFibre.integrable_normalizedMeasure_iff (hdom.integrable x hx) (hn x hx)
      (hp x hx) _).mpr hiT, ?_⟩
  have hm : ContDiffOn ℝ 2 (fun z => -Real.log (∫ y, w z y)) (Prod.fst '' Ω) := by
    simpa only [zero_sub] using
      convexLocalization_contDiff hΩo hΩc hΩb hH₂c hH₂ (fun _ => 0) contDiffOn_const hdom hdom'
  have heq : fderiv ℝ (fun z => H₁ z - Real.log (∫ y, w z y)) =ᶠ[𝓝 x]
      fun z => fderiv ℝ H₁ z + fderiv ℝ (fun z => -Real.log (∫ y, w z y)) z := by
    filter_upwards [ho.mem_nhds hx] with z hz
    change fderiv ℝ (fun z => H₁ z + -Real.log (∫ y, w z y)) z = _
    exact fderiv_fun_add
      ((hH₁.differentiableOn (by norm_num)).differentiableAt (ho.mem_nhds hz))
      ((hm.differentiableOn (by norm_num)).differentiableAt (ho.mem_nhds hz))
  rw [heq.fderiv_eq, fderiv_fun_add
    (((hH₁.fderiv_of_isOpen ho (by norm_num : 1 + 1 ≤ (2 : WithTop ℕ∞))).differentiableOn
      (by norm_num)).differentiableAt (ho.mem_nhds hx))
    (((hm.fderiv_of_isOpen ho (by norm_num : 1 + 1 ≤ (2 : WithTop ℕ∞))).differentiableOn
      (by norm_num)).differentiableAt (ho.mem_nhds hx))]
  have hess := DominatedFibre.gibbs_marginal_hessian_apply_of_domination ho hdom hdom'
    hn hp hx (S x) (T x) hf hsecond u v
  change _ + fderiv ℝ (fderiv ℝ (fun z => -Real.log (∫ y, w z y))) x u v = _
  rw [hess]
  dsimp only [ρ, AffineFibre.convexConditionalMeasure, w]
  exact (add_sub_assoc _ _ _).symm

/-- See Lemma 3.5 of the paper, the pointwise lower Hessian at
any twice differentiable point. The first derivative exists locally and is
differentiable at the given point. No C² neighbourhood or density domination
is assumed for this clause. -/
theorem convexLocalization_hessian_at (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hΩb : Bornology.IsBounded Ω) (hH₂c : ConvexOn ℝ Ω H₂)
    (H₁ : E → ℝ) (hH₁ : ContDiffOn ℝ 2 H₁ (Prod.fst '' Ω))
    {x : E} (hx : x ∈ Prod.fst '' Ω)
    (hd : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ (fun z => H₁ z - Real.log (∫ y,
      Ω.indicator (fun p => Real.exp (-H₂ p)) (z, y))) z)
    (hdd : DifferentiableAt ℝ (fderiv ℝ (fun z => H₁ z - Real.log (∫ y,
      Ω.indicator (fun p => Real.exp (-H₂ p)) (z, y)))) x) (v : E) :
    fderiv ℝ (fderiv ℝ H₁) x v v ≤
      fderiv ℝ (fderiv ℝ (fun z => H₁ z - Real.log (∫ y,
        Ω.indicator (fun p => Real.exp (-H₂ p)) (z, y)))) x v v := by
  let M := fun z => H₁ z - Real.log (∫ y, Ω.indicator (fun p => Real.exp (-H₂ p)) (z, y))
  have ho : IsOpen (Prod.fst '' Ω) := isOpenMap_fst _ hΩo
  have h1d (z) (hz : z ∈ Prod.fst '' Ω) : DifferentiableAt ℝ H₁ z :=
    (hH₁.differentiableOn (by norm_num)).differentiableAt (ho.mem_nhds hz)
  have h1dd : DifferentiableAt ℝ (fderiv ℝ H₁) x :=
    ((hH₁.fderiv_of_isOpen ho (by norm_num : 1 + 1 ≤ (2 : WithTop ℕ∞))).differentiableOn
      (by norm_num)).differentiableAt (ho.mem_nhds hx)
  have he : fderiv ℝ (fun z => M z - H₁ z) =ᶠ[𝓝 x]
      fun z => fderiv ℝ M z - fderiv ℝ H₁ z := by
    filter_upwards [hd, ho.mem_nhds hx] with z hz hzU
    exact fderiv_fun_sub hz (h1d z hzU)
  have hD : DifferentiableAt ℝ (fderiv ℝ (fun z => M z - H₁ z)) x :=
    (hdd.sub h1dd).congr_of_eventuallyEq he
  have hn := convexOn_second_fderiv_nonneg_at ho
    (convexLocalization hΩo hΩc hΩb hH₂c H₁).2 hx
    (by filter_upwards [hd, ho.mem_nhds hx] with z hz hzU; exact hz.sub (h1d z hzU)) hD v
  rw [he.fderiv_eq, fderiv_fun_sub hdd h1dd] at hn
  simpa only [sub_apply, sub_nonneg] using hn

/-- See Lemma 3.5 of the paper, all conclusions in one interface.
The first two derivative assumptions refer to the actual zero extension.
The pointwise clause uses the locally defined first derivative at a twice
differentiable point, without assuming continuity of the second derivative.
All force and energy-Hessian integrability is concluded. -/
theorem convexLocalization_complete {n m : ℕ} (_hn : 1 ≤ n)
    {Ω : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m))}
    (H₁ : EuclideanSpace ℝ (Fin n) → ℝ)
    {H₂ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) → ℝ}
    (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω) (hΩb : Bornology.IsBounded Ω)
    (hH₁smooth : ContDiffOn ℝ (⊤ : ℕ∞) H₁ (Prod.fst '' Ω))
    (hH₂smooth : ContDiffOn ℝ (⊤ : ℕ∞) H₂ Ω) (hH₂c : ConvexOn ℝ Ω H₂)
    (_hH : Integrable (Ω.indicator (fun p => Real.exp (-(H₁ p.1 + H₂ p)))))
    (_hHpos : 0 < ∫ p, Ω.indicator (fun p => Real.exp (-(H₁ p.1 + H₂ p))) p) :
    let w := fun x y => Ω.indicator (fun p => Real.exp (-H₂ p)) (x, y)
    let M := fun x => H₁ x - Real.log (∫ y, w x y)
    let S := fun x y => fderiv ℝ (fun z => H₂ (z, y)) x
    let T := fun x y => fderiv ℝ (fderiv ℝ (fun z => H₂ (z, y))) x
    (∀ x ∈ Prod.fst '' Ω, Integrable (w x) ∧ 0 < ∫ y, w x y) ∧
    ConvexOn ℝ (Prod.fst '' Ω) (fun x => M x - H₁ x) ∧
    (∀ (φ : EuclideanSpace ℝ (Fin n) → ℝ), ContDiff ℝ 2 φ → HasCompactSupport φ →
      tsupport φ ⊆ Prod.fst '' Ω → (∀ x, 0 ≤ φ x) → ∀ v,
        0 ≤ ∫ x, (M x - H₁ x) * fderiv ℝ (fderiv ℝ φ) x v v) ∧
    (∀ x ∈ Prod.fst '' Ω, (∀ᶠ z in 𝓝 x, DifferentiableAt ℝ M z) →
      DifferentiableAt ℝ (fderiv ℝ M) x → ∀ v,
        fderiv ℝ (fderiv ℝ H₁) x v v ≤ fderiv ℝ (fderiv ℝ M) x v v) ∧
    (DominatedFibre.DominatedFDerivOn volume (Prod.fst '' Ω) w
        (fun x y => -w x y • S x y) →
      DominatedFibre.DominatedFDerivOn volume (Prod.fst '' Ω)
        (fun x y => -w x y • S x y)
        (fun x y => w x y • ((S x y).smulRight (S x y) - T x y)) →
      ContDiffOn ℝ 2 M (Prod.fst '' Ω) ∧
      ∀ x (hx : x ∈ Prod.fst '' Ω) (u v : EuclideanSpace ℝ (Fin n)),
        let ρ := AffineFibre.convexConditionalMeasure hΩo hΩb hH₂c ⟨x, hx⟩
        MemLp (fun y => S x y u) 2 ρ ∧ MemLp (fun y => S x y v) 2 ρ ∧
        Integrable (fun y => T x y u v) ρ ∧
        fderiv ℝ M x u = fderiv ℝ H₁ x u + ∫ y, S x y u ∂ρ ∧
        fderiv ℝ (fderiv ℝ M) x u v = fderiv ℝ (fderiv ℝ H₁) x u v +
          (∫ y, T x y u v ∂ρ) -
            ProbabilityTheory.covariance (fun y => S x y u) (fun y => S x y v) ρ) := by
  intro w M S T
  have hH₁ : ContDiffOn ℝ 2 H₁ (Prod.fst '' Ω) := hH₁smooth.of_le (by norm_num)
  have hH₂ : ContDiffOn ℝ 2 H₂ Ω := hH₂smooth.of_le (by norm_num)
  obtain ⟨hmass, hconv⟩ := convexLocalization hΩo hΩc hΩb hH₂c H₁
  refine ⟨hmass, hconv, ?_, ?_, ?_⟩
  · intro φ hφ hφc hφΩ hφ0 v
    exact convexLocalization_distributional hΩo hΩc hΩb hH₂c H₁ hφ hφc hφΩ hφ0 v
  · intro x hx hd hdd v
    exact convexLocalization_hessian_at hΩo hΩc hΩb hH₂c H₁ hH₁ hx hd hdd v
  · intro hdom hdom'
    refine ⟨convexLocalization_contDiff hΩo hΩc hΩb hH₂c hH₂ H₁ hH₁ hdom hdom', ?_⟩
    intro x hx u v ρ
    obtain ⟨hu, hv, hiT, hh⟩ :=
      convexLocalization_hessian hΩo hΩc hΩb hH₂c hH₂ H₁ hH₁ hdom hdom' x hx u v
    refine ⟨hu, hv, hiT, ?_, hh⟩
    exact (convexLocalization_gradient hΩo hΩb hH₂c H₁
      (hH₁.differentiableOn (by norm_num)) hdom hx u).2

end Riesz2

end
