/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.OptimalLocalizationPart2
public import Riesz2.DecayLong.OptimalLocalizationPart3
public import Riesz2.DecayLong.OptimalLocalizationPart4

/-!
# Completion of the optimal localization bootstrap

The uniform induction convention of Subsection 5.5 uses one
prefactor for every ε ≥ εmin > 0. Uniform boundary and reference estimates
preserve this convention through the constrained step. The unrestricted
composition and finite saturation then give Proposition 5.15, with
only the explicit periodic-zeta connection formula and the stated quantifier order.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped BigOperators Classical Fin.NatCast

namespace Riesz2.OptimalLocalizationPart5

open OptimalLocalizationPart2

/-- See the proof of Proposition 5.15 in the paper: discharge the uniform field interface
of the reference and comparison estimates using the field theorem. -/
theorem uniform_field_estimate (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ)
    (hκstar : 0 < κstar) (hγstar : 0 < γstar) (M₀ : ℕ+) :
    OptimalLocalizationPart4.UniformFieldEstimate s κstar γstar M₀ := by
  exact OptimalLocalizationPart3.loc_field hzeta s κstar γstar hκstar hγstar M₀

/-- See Subsection 5.4 of the paper: absorb the logarithm with a common prefactor
for all ε ≥ εmin, including ε = εmin. -/
theorem logarithmic_loss_uniform_internal (s : Riesz1.RieszExponent)
    (εmin : ℝ) (hεmin : 0 < εmin) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, εmin ≤ ε →
      ∀ (n m : ℕ+), 2 ≤ (n : ℕ) → 2 ≤ (m : ℕ) →
      (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
      ∀ R : ℝ, 1 ≤ R → R ≤ (m : ℝ) →
      1 + Real.log (2 * R) ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨C, hC, hp⟩ := OptimalLocalization.logarithmic_loss_internal s εmin hεmin
  refine ⟨C, hC, fun ε hε n m hn hm hmn R hR hRm => ?_⟩
  apply (hp n m hn hm hmn R hR hRm).trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast n.pos) hε) hC.le

/-- See the proof of Proposition 5.15 in the paper: construct common boundary,
reference and comparison-error witnesses, with every quantitative prefactor
chosen before ε ≥ εmin. All estimates are conclusions. -/
theorem localized_decomposition_uniform_internal (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ)
    (hκstar : 0 < κstar) (hγstar : 0 < γstar) (M₀ : ℕ+) :
    ∃ κz κφ κg D : ℝ, 0 < κz ∧ 0 < κφ ∧ 0 < κg ∧ 0 < D ∧ ∀ εmin : ℝ, 0 < εmin →
    ∀ Cstar : ℝ, 1 ≤ Cstar →
    ∀ (βlo : ℝ) (_hβlo : 0 < βlo), ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ Cz Cφ Cg : ℝ, 0 < Cz ∧ 0 < Cφ ∧ 0 < Cg ∧
    ∀ ε : ℝ, εmin ≤ ε →
    ∀ {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
      (Q : ScalarFormData ν) (_hQ : IsClosedScalarDirichletForm Q), IsConservativeScalarForm Q →
    ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ)),
    2 ≤ (n : ℕ) → (n : ℕ) ≤ (m : ℕ) →
    (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
    let K := ⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ)
    1 ≤ K → 4 * K ≤ (m : ℕ) →
    ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M →
    ∃ A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → Ω → ℝ,
      (∀ t, Measurable (A t)) ∧
      (∀ᵐ x ∂ν, (∀ t, 0 ≤ A t x) ∧
        IntervalBoundary.intervalMatrix m m le_rfl (fun t => A t x) = M x) ∧
    ∀ (j i₀ : Fin (m : ℕ)) (hR : 16 ≤ Riesz1.cyclicIndexDistance m j i₀),
    (n : ℝ) ^ (D * ε) ≤ (Riesz1.cyclicIndexDistance m j i₀ : ℝ) →
    let n₀ := LocalizedMatrix.windowSize m j i₀
    let m₀ := LocalizedMatrix.windowPeriod s m j i₀
    let hn : (n₀ : ℕ) ≤ (m : ℕ) := by
      have := (LocalizedMatrix.window_size_bounds m j i₀ hR).2.2.2
      dsimp only [n₀]; omega
    let hn₀ : (n₀ : ℕ) ≤ (m₀ : ℕ) := by
      have := LocalizedMatrix.two_windowSize_lt_period s m j i₀ hR
      dsimp only [n₀, m₀]; omega
    let hm₀ : 2 ≤ (m₀ : ℕ) := by
      have := LocalizedMatrix.two_windowSize_lt_period s m j i₀ hR
      have := n₀.pos
      dsimp only [n₀, m₀] at *; omega
    let b := j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ))
    let P := fun x (l i : Fin (n₀ : ℕ)) => M x (l.castLE hn + b) (i.castLE hn + b)
    let Ml := LocalizedMatrix.matrix s m m₀ n₀ hm₀ hn hn₀ K (fun t => A (t.1 + b, t.2))
    let _Rem := LocalizedMatrix.remainder s m m₀ n₀ hm₀ hn hn₀ K
      (fun t => A (t.1 + b, t.2)) P
    let c : Fin (m₀ : ℕ) := ⟨Riesz1.cyclicIndexDistance m j i₀ / 8, by
      have hc := LocalizedMatrix.window_card m j i₀
      have ht := LocalizedMatrix.two_windowSize_lt_period s m j i₀ hR
      change _ < (LocalizedMatrix.windowPeriod s m j i₀ : ℕ)
      change (LocalizedMatrix.windowSize m j i₀ : ℕ) = _ at hc
      omega⟩
    ∀ (β : ℝ) (_hβl : βlo ≤ β), β ≤ βhi →
    ∀ (χ : Lp ℝ 2 ν) (u : Fin (m : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _)
      (fun i => if i = i₀ then χ else 0) u →
    ∃ ψ₀ z φ : Fin (m₀ : ℕ) → Q.1,
      (∀ i : Fin (n₀ : ℕ), ψ₀ (i.castLE hn₀) = u (LocalizedMatrix.windowEmbedding m j i₀ i)) ∧
      (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (2 - s.val) * ‖(z c).val‖ +
        (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ ((3 - s.val) / 2) *
          Real.sqrt (Q.2 (z c) (z c)) ≤ Cz * (n : ℝ) ^ (κz * ε) * ‖χ‖ ∧
      ‖(φ c).val‖ ≤ Cφ * (n : ℝ) ^ (κφ * ε) * ‖χ‖ *
        (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (-(2 - s.val)) ∧
      Real.sqrt (Q.2 (φ c) (φ c)) ≤ Cφ * (n : ℝ) ^ (κφ * ε) * ‖χ‖ *
        (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (-(3 - s.val) / 2) ∧
    ∃ g : Fin (m₀ : ℕ) → Lp ℝ 2 ν,
      WeightedWeakSolution Q (fun x => β • Ml x) ⊤ g (fun i => ψ₀ i - z i - φ i) ∧
      (∑ i, ‖g i‖) ≤ Cg * (n : ℝ) ^ (κg * ε) * ‖χ‖ *
        (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (-(1 - s.val)) ∧
      ∀ i, (Riesz1.cyclicIndexDistance m₀ i c : ℝ) ≤
        (Riesz1.cyclicIndexDistance m j i₀ : ℝ) / 64 →
        ‖g i‖ ≤ Cg * (n : ℝ) ^ (κg * ε) * ‖χ‖ *
          (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (-(2 - s.val)) := by
  obtain ⟨κφ, Dφ, hκφ, hDφ, href⟩ :=
    OptimalLocalizationPart4.loc_reference_solution_uniform_internal hzeta s κstar γstar
      hκstar hγstar M₀ (uniform_field_estimate hzeta s κstar γstar hκstar hγstar M₀)
  obtain ⟨κb, Db, hκb, hDb, hboundary⟩ :=
    OptimalLocalizationPart3.loc_boundary hzeta s κstar γstar hκstar hγstar M₀
  obtain ⟨κl, γl, Dl, hκl, hγl, hDl, hlocal⟩ :=
    ReferenceComparisonError.localization_for_representation_internal s κstar γstar M₀ hκstar hγstar
  obtain ⟨κ, hκ, hcomp⟩ :=
    ReferenceComparisonError.comparison_error_of_reference_estimates_internal s κl γl κφ hκl.le hκφ.le M₀
  let D := max (max Dφ Db) (max Dl (8 * (M₀ : ℕ)))
  refine ⟨κb, κφ, κ, D, hκb, hκφ, hκ, hDφ.trans_le ((le_max_left Dφ Db).trans (le_max_left _ _)), ?_⟩
  intro εmin hεmin Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Cφ, hCφ, href⟩ := href εmin hεmin Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Cb, hCb, hboundary⟩ := hboundary εmin hεmin Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Cl, hCl, hlocal⟩ := hlocal Cstar hCstar
  obtain ⟨C, hC, hcomp⟩ := hcomp Cl hCl Cφ hCφ βhi (hβlo.trans_le hβhi)
  refine ⟨Cb, Cφ, C, hCb, hCφ, hC, ?_⟩
  intro ε hεlower Ω _ ν _ Q hQ hQc n m hm hn hnm hmn K hK hKm M hM
  have hε : 0 < ε := hεmin.trans_le hεlower
  obtain ⟨A, hAm, hArep, hb⟩ := hboundary ε hεlower ν Q hQ hQc n m hm hn hnm hmn hK hKm M hM
  refine ⟨A, hAm, hArep, ?_⟩
  intro j i₀ hR hsep n₀ m₀ hnp hn₀ hm₀ b P Ml Rem c β hβl hβu χ u hu
  let pv := (MatrixEnergy.vectorEquiv Q hQ).symm
    (fun i => u (LocalizedMatrix.windowEmbedding m j i₀ i))
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ (n : ℕ) by omega)
  have sep (d : ℝ) (hd : d ≤ D) :
      (n : ℝ) ^ (d * ε) ≤ (Riesz1.cyclicIndexDistance m j i₀ : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hn1 (mul_le_mul_of_nonneg_right hd hε.le)).trans hsep
  have hsepφ := sep Dφ ((le_max_left Dφ Db).trans (le_max_left _ _))
  have hsepb := sep Db ((le_max_right Dφ Db).trans (le_max_left _ _))
  have hsepl := sep Dl ((le_max_left Dl _).trans (le_max_right _ _))
  have hsepc := sep (8 * (M₀ : ℕ)) ((le_max_right Dl _).trans (le_max_right _ _))
  have hMl := hlocal ν ε hε n m hn hm M hM A hAm (hArep.mono fun _ hx => hx.2) j i₀ hR hsepl
  obtain ⟨r, hr, hbdata, hzexists, hzest⟩ := hb j i₀ hR hsepb β hβl hβu χ u hu
  obtain ⟨lam, hlam, _, wb, hwb, Vb, hVb, hψexists, hψactive⟩ := hbdata
  obtain ⟨lamf, hlamf, U, hU, w, hw, V, hV, hφ⟩ :=
    href ε hεlower ν Q hQ hQc n m hm hn hnm hmn hK hKm M hM β hβl hβu χ i₀ u hu j hR hsepφ
  have helam : lamf = lam := by
    apply Lp.ext
    filter_upwards [hlamf, hlam] with x hx hy
    exact hx.trans hy.symm
  subst lamf
  have hKml := (LocalizedMatrix.window_reference_cutoff_admissible s n m ε hε M₀ j i₀ hR hsepc).2
  have hew : wb = w := by
    have he := LocalizedFieldPart4.normalized_schur_exists_internal hzeta s β (hβlo.trans_le hβl)
      n₀ m₀ hn₀ hm₀ K hK (by change 4 * K ≤ (m₀ : ℕ) at hKml; omega) ν Q hQ pv
    exact he.unique hwb hw
  subst wb
  have heV : Vb = V := by
    funext l
    apply Lp.ext
    have hrow := LocalizedFieldPart3.schur_row_ae_internal Q hQ s n₀ m₀ hn₀ hm₀ K
      Cl κl γl (ε * Real.log (n : ℝ) / Real.log (n₀ : ℝ)) β Ml hMl w l
    rw [hV l]
    filter_upwards [hVb l, hU l, hrow,
      Lp.coeFn_add ((-β) • U l - β • LocalizedFieldPart3.referenceRow Q hQ s n₀ m₀ hm₀ K
        (LocalizedFieldPart3.exteriorReindex Q hQ n₀ m₀ hn₀ w) (l.castLE hn₀)) lam,
      Lp.coeFn_sub ((-β) • U l) (β • LocalizedFieldPart3.referenceRow Q hQ s n₀ m₀ hm₀ K
        (LocalizedFieldPart3.exteriorReindex Q hQ n₀ m₀ hn₀ w) (l.castLE hn₀)),
      Lp.coeFn_smul (-β) (U l)] with x hv hu hr ha hs hm
    rw [ha, Pi.add_apply, hs, Pi.sub_apply, hm, Pi.smul_apply, smul_eq_mul, hu, hr]
    exact hv
  subst Vb
  obtain ⟨ψ₀, hψ, _⟩ := hψexists
  obtain ⟨z, hz, _⟩ := hzexists
  let f := (SchurRestriction.extendSource n₀ m₀ hn₀ (WithLp.toLp 2 V)).ofLp
  let rb := (SchurRestriction.extendSource n₀ m₀ hn₀ (WithLp.toLp 2 r)).ofLp
  have hsum : (SchurRestriction.extendSource n₀ m₀ hn₀ (WithLp.toLp 2 (fun i => V i + r i))).ofLp =
      fun i => f i + rb i := by
    have hh : WithLp.toLp 2 (fun i => V i + r i) = WithLp.toLp 2 V + WithLp.toLp 2 r := rfl
    rw [hh, map_add]
    rfl
  have hψ' : WeightedWeakSolution Q (fun x => β • Ml x) ⊤ (fun i => f i + rb i) ψ₀ := by
    rwa [hsum] at hψ
  have hz' : WeightedWeakSolution Q (fun x => β • Ml x) ⊤ rb z := by
    simpa only [rb, funext (ReferenceComparisonPart2.extendSource_sum_internal n₀ m₀ hn₀ r)] using hz
  have hn₀real : 1 < (n₀ : ℝ) := by
    have ht := (LocalizedMatrix.window_size_bounds m j i₀ hR).1
    change 5 ≤ (n₀ : ℕ) at ht
    exact_mod_cast (show 1 < (n₀ : ℕ) by omega)
  have hRreal : (16 : ℝ) ≤ (Riesz1.cyclicIndexDistance m j i₀ : ℝ) := by exact_mod_cast hR
  have hφ' :
      let φ := fun i => ∑ k, ScalarFormHilbert.equiv Q hQ
        (FiniteFormReferenceKernel.solutionKernel Q hQ _
          (ReferenceOperatorKernelPart3.reference_posDef s ⟨β, hβlo.trans_le hβl⟩ m₀ hm₀) i k (f k))
      (∑ i, ‖(φ i).val‖) ≤ Cφ * (n : ℝ) ^ (κφ * ε) * ‖χ‖ *
        (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (-(1 - s.val)) ∧
      ∀ i, (Riesz1.cyclicIndexDistance m₀ i c : ℝ) ≤
        (Riesz1.cyclicIndexDistance m j i₀ : ℝ) / 32 →
        ‖(φ i).val‖ ≤ Cφ * (n : ℝ) ^ (κφ * ε) * ‖χ‖ *
          (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (-(2 - s.val)) ∧
        Real.sqrt (Q.2 (φ i) (φ i)) ≤ Cφ * (n : ℝ) ^ (κφ * ε) * ‖χ‖ *
          (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (-(3 - s.val) / 2) := by
    simpa only [ReferenceComparison.referenceSolution, map_sum] using hφ
  have he := hcomp ε hε ν Q hQ n n₀ m₀ hn₀real hm₀ hK Ml hMl
    ⟨β, hβlo.trans_le hβl⟩ hβu χ c _ hRreal f rb ψ₀ z hψ' hz' hφ'
  let φ := ReferenceComparison.referenceSolution Q hQ s ⟨β, hβlo.trans_le hβl⟩ m₀ hm₀ f
  obtain ⟨g, hg, hgeq, hmass, hcentral⟩ := he
  have hcenter : (Riesz1.cyclicIndexDistance m₀ c c : ℝ) ≤
      (Riesz1.cyclicIndexDistance m j i₀ : ℝ) / 32 := by
    simp only [Riesz2.cyclicIndexDistance_self, Nat.cast_zero]
    positivity
  have hp := hφ.2 c hcenter
  refine ⟨ψ₀, z, φ, hψactive ψ₀ hψ, hzest z hz, hp.1, hp.2, g, ?_, hmass, hcentral⟩
  simpa only [φ, ReferenceComparison.referenceSolution, map_sum] using hgeq

/-- See the proof of Proposition 5.15 in the paper: the constrained improvement
preserves the uniform quantifier order of Subsection 5.5. Only the unrestricted
part of the current profile is needed by this internal construction. -/
theorem constrained_step_uniform_internal (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (A G : ℝ)
    (hAlo : 3 / 2 - s.val ≤ A) (_hAhi : A ≤ 2 - s.val)
    (hGlo : 1 - s.val / 2 ≤ G) (_hGhi : G ≤ (3 - s.val) / 2) (_hGA : G ≤ A)
    (hcurrent : UniformProfile s A G false) :
    UniformProfile s (min (2 - s.val) (A + 1 - s.val))
      (min ((3 - s.val) / 2) (G + 1 - s.val)) true := by
  intro κstar γstar M₀ hκstar hγstar
  obtain ⟨κz, κφ, κg, Dd, hκz, hκφ, hκg, hDd, hdec⟩ :=
    localized_decomposition_uniform_internal hzeta s κstar γstar hκstar hγstar M₀
  obtain ⟨κp, Dp, hκp, hDp, hpoint⟩ :=
    window_point_source_internal s A G hcurrent κstar γstar M₀ hκstar hγstar
  obtain ⟨κl, γl, Dl, hκl, hγl, hDl, hlocal⟩ :=
    ReferenceComparisonError.localization_for_representation_internal s κstar γstar M₀ hκstar hγstar
  have hA : 0 < A := by linarith only [hAlo, s.property.2]
  have hG : 0 < G := by linarith only [hGlo, s.property.2]
  have hp : 0 < 2 - s.val := by linarith [s.property.2]
  have hpg : 0 < (3 - s.val) / 2 := by linarith [s.property.2]
  have hpgp : (3 - s.val) / 2 ≤ 2 - s.val := by linarith [s.property.2]
  obtain ⟨Ce, hCe, herr⟩ := OptimalLocalization.comparison_error_internal s A G hA hG
  let D := max (max Dd Dp) Dl
  let κ := κstar + D * (2 - s.val) + κz + κφ + κg + κp + 1
  have hD : 0 < D := hDd.trans_le ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨κ, by dsimp only [κ]; positivity, ?_⟩
  intro εmin hεmin Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Cz, Cφ, Cg, hCz, hCφ, hCg, hdec⟩ := hdec εmin hεmin Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Cp, hCp, hpoint⟩ := hpoint εmin hεmin Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Cl, hCl, hlocal⟩ := hlocal Cstar hCstar
  obtain ⟨L, hL, hlog⟩ := logarithmic_loss_uniform_internal s εmin hεmin
  let Bs := 1 + 2 * βlo⁻¹ * Cstar
  let B := Bs + Cz + Cφ + 2 * Ce * Cp * Cg * L
  let C := (17 ^ (2 - s.val) + 2 ^ (2 - s.val)) * B
  have hBs : 0 < Bs := by dsimp only [Bs]; positivity
  have hB : 0 < B := by dsimp only [B]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro ε hεlower Ω _ ν _ Q hQ hQc n m hm hn hnm hmn K hK hKm M hM β hβl hβu i₀ χ
  have hε : 0 < ε := hεmin.trans_le hεlower
  have hβ : 0 < β := hβlo.trans_le hβl
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by positivity
  have hκsmall (t : ℝ) (ht : t ≤ 2 - s.val) : κstar + D * t ≤ κ := by
    have hh := mul_le_mul_of_nonneg_left ht hD.le
    dsimp only [κ]
    linarith only [hh, hκz, hκφ, hκg, hκp]
  have hκz' : κz ≤ κ := by dsimp only [κ]; linarith only [hκstar, hκz, hκφ, hκg, hκp, mul_nonneg hD.le hp.le]
  have hκφ' : κφ ≤ κ := by dsimp only [κ]; linarith only [hκstar, hκz, hκφ, hκg, hκp, mul_nonneg hD.le hp.le]
  have hκe' : κp + κg + 1 ≤ κ := by dsimp only [κ]; linarith only [hκstar, hκz, hκφ, hκg, hκp, mul_nonneg hD.le hp.le]
  let a := Cstar⁻¹ * (n : ℝ) ^ (-κstar * ε)
  have hl : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
      ∀ z : Fin (m : ℕ) → ℝ, a * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j :=
    hM.2.1.mono (fun _ hx => ⟨hx.1, hx.2.2.1⟩)
  obtain ⟨u, hu, huniq⟩ := (AbstractEquation.existence_energy Q hQ β hβ M hM.1 a
    (SchurRestriction.periodized_mass_pos hCstar) hl (zeroSumComponents _)
    (fun i => if i = i₀ then χ else 0)).1
  refine ⟨u, ⟨hu, ?_⟩, fun v hv => huniq v hv.1⟩
  intro j
  let R : ℝ := Riesz1.cyclicIndexDistance m j i₀
  let av := min (2 - s.val) (A + 1 - s.val)
  let gv := min ((3 - s.val) / 2) (G + 1 - s.val)
  have hav0 : 0 ≤ av := le_min hp.le (by linarith [s.property.2])
  have hgv0 : 0 ≤ gv := le_min hpg.le (by linarith [s.property.2])
  have havp : av ≤ 2 - s.val := min_le_left _ _
  have hgvp : gv ≤ 2 - s.val := (min_le_left _ _).trans hpgp
  by_cases hsmall : R < max 16 ((n : ℝ) ^ (D * ε))
  · have henergy := GlobalDecay.global_energy_unweighted s n m hm K Cstar κstar γstar ε
      hCstar hκstar.le hε.le Q hQ M hM βlo β hβlo hβl χ i₀ u hu
    have hplain : ∀ j, ‖(u j).val‖ ≤ Bs * (n : ℝ) ^ (κstar * ε) * ‖χ‖ ∧
        Real.sqrt (Q.2 (u j) (u j)) ≤ Bs * (n : ℝ) ^ (κstar * ε) * ‖χ‖ := by
      simpa only [neg_zero, Real.rpow_zero, one_mul, mul_one] using
        OptimalLocalizationBootstrap.component_bounds_internal Q hQ m i₀ 0 0 _ u
          (by simpa only [mul_zero, Real.rpow_zero, one_mul] using henergy)
    have lift (t x : ℝ) (ht : 0 ≤ t) (htp : t ≤ 2 - s.val)
        (hx : x ≤ Bs * (n : ℝ) ^ (κstar * ε) * ‖χ‖) :
        x ≤ C * (n : ℝ) ^ (κ * ε) * (1 + R) ^ (-t) * ‖χ‖ := by
      have hh := OptimalLocalization.small_distance_internal (n : ℝ) ε D κstar t R Bs ‖χ‖ x
        hn1 hε.le hD.le ht (by dsimp only [R]; positivity) hsmall hBs.le (norm_nonneg χ) hx
      apply hh.trans
      have hcb : 17 ^ t * Bs ≤ C := by
        have ht17 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 17) htp
        have hBsB : Bs ≤ B := by dsimp only [B]; linarith only [hCz, hCφ, show 0 ≤ Ce * Cp * Cg * L by positivity]
        dsimp only [C]
        exact mul_le_mul (ht17.trans (le_add_of_nonneg_right (by positivity))) hBsB hBs.le (by positivity)
      have hco := LocalizedMatrix.loss_mono_internal hn1 hε.le (by positivity) hcb (hκsmall t htp)
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hco
        (by positivity : 0 ≤ (1 + R) ^ (-t))) (norm_nonneg χ)
      exact hh
    exact ⟨lift av _ hav0 havp (hplain j).1, lift gv _ hgv0 hgvp (hplain j).2⟩
  · have hlarge : max 16 ((n : ℝ) ^ (D * ε)) ≤ R := le_of_not_gt hsmall
    have hR : 16 ≤ Riesz1.cyclicIndexDistance m j i₀ := by
      have hh : (16 : ℝ) ≤ (Riesz1.cyclicIndexDistance m j i₀ : ℝ) := (le_max_left _ _).trans hlarge
      exact_mod_cast hh
    have hR16 : 16 ≤ R := (le_max_left _ _).trans hlarge
    have hR1 : 1 ≤ R := by linarith
    have hRm : R ≤ (m : ℝ) := by
      have hh := Riesz1.APG.cyclicIndexDistance_le_half j i₀
      dsimp only [R]
      exact_mod_cast (show Riesz1.cyclicIndexDistance m j i₀ ≤ (m : ℕ) by omega)
    have sep (d : ℝ) (hd : d ≤ D) : (n : ℝ) ^ (d * ε) ≤ R :=
      (Real.rpow_le_rpow_of_exponent_le hn1 (mul_le_mul_of_nonneg_right hd hε.le)).trans
        ((le_max_right _ _).trans hlarge)
    obtain ⟨Ac, hAm, hArep, hdec⟩ := hdec ε hεlower ν Q hQ hQc n m hm hn hnm hmn hK hKm M hM
    obtain ⟨ψ, z, φ, hψ, hz, hφv, hφg, g, hgeq, hmass, hcentral⟩ :=
      hdec j i₀ hR (sep Dd ((le_max_left _ _).trans (le_max_left _ _))) β hβl hβu χ u hu
    let n₀ := LocalizedMatrix.windowSize m j i₀
    let m₀ := LocalizedMatrix.windowPeriod s m j i₀
    have hsize := LocalizedMatrix.window_size_bounds m j i₀ hR
    have htwo := LocalizedMatrix.two_windowSize_lt_period s m j i₀ hR
    have hnp : (n₀ : ℕ) ≤ (m : ℕ) := by dsimp only [n₀]; omega
    have hn₀ : (n₀ : ℕ) ≤ (m₀ : ℕ) := by dsimp only [n₀, m₀]; omega
    have hm₀ : 2 ≤ (m₀ : ℕ) := by have := n₀.pos; dsimp only [n₀, m₀] at *; omega
    let b : Fin (m : ℕ) := j - ↑(Riesz1.cyclicIndexDistance m j i₀ / 8)
    let Ml := LocalizedMatrix.matrix s m m₀ n₀ hm₀ hnp hn₀ K (fun t => Ac (t.1 + b, t.2))
    let c : Fin (m₀ : ℕ) := ⟨Riesz1.cyclicIndexDistance m j i₀ / 8, by
      have hc := LocalizedMatrix.window_card m j i₀
      change (n₀ : ℕ) = _ at hc
      omega⟩
    have hMl := hlocal ν ε hε n m hn hm M hM Ac hAm (hArep.mono fun _ hx => hx.2)
      j i₀ hR (sep Dl (le_max_right _ _))
    have hpoint' : ∀ (ζ : Lp ℝ 2 ν) (i : Fin (m₀ : ℕ)),
        ∃ v : Fin (m₀ : ℕ) → Q.1,
          WeightedWeakSolution Q (fun x => β • Ml x) ⊤ (fun k => if k = i then ζ else 0) v ∧
          ∀ l, ‖(v l).val‖ ≤ Cp * (n : ℝ) ^ (κp * ε) * weightRadius m₀ l i ^ (-A) * ‖ζ‖ ∧
            Real.sqrt (Q.2 (v l) (v l)) ≤ Cp * (n : ℝ) ^ (κp * ε) * weightRadius m₀ l i ^ (-G) * ‖ζ‖ := by
      intro ζ i
      obtain ⟨v, hv, _⟩ := hpoint ε hεlower ν Q hQ hQc n m hn hm hnm hmn hK M hM Ac hAm
        (hArep.mono fun _ hx => hx.2) j i₀ hR
        (sep Dp ((le_max_right _ _).trans (le_max_left _ _))) β hβl hβu i ζ
      exact ⟨v, hv⟩
    have herr' := herr ν Q hQ n₀ m₀ hm₀ K Cl κl γl
      (ε * Real.log (n : ℝ) / Real.log (n₀ : ℝ)) β hCl hβ Ml hMl
      (Cp * (n : ℝ) ^ (κp * ε)) (by positivity) hpoint' g
      (fun i => ψ i - z i - φ i) hgeq c R
      (Cg * (n : ℝ) ^ (κg * ε) * ‖χ‖) hR16 (by positivity) hmass hcentral
    let Z := Cz * (n : ℝ) ^ (κz * ε) * ‖χ‖
    let P := Cφ * (n : ℝ) ^ (κφ * ε) * ‖χ‖
    let E := (Ce * Cp * Cg * L) * (n : ℝ) ^ ((κp + κg + 1) * ε) * ‖χ‖
    have herrBound (x q : ℝ) (hx : x ≤ Ce * (Cp * (n : ℝ) ^ (κp * ε)) *
        (Cg * (n : ℝ) ^ (κg * ε) * ‖χ‖) * (1 + Real.log (2 * R)) *
        (R ^ (-(2 - s.val)) + R ^ (-q))) :
        x ≤ E * (R ^ (-(2 - s.val)) + R ^ (-q)) := by
      apply hx.trans
      have hh := mul_le_mul_of_nonneg_left (hlog ε hεlower n m hn hm hmn R hR1 hRm)
        (show 0 ≤ Ce * (Cp * (n : ℝ) ^ (κp * ε)) * (Cg * (n : ℝ) ^ (κg * ε) * ‖χ‖) by positivity)
      apply (mul_le_mul_of_nonneg_right hh (by positivity)).trans_eq
      dsimp only [E]
      rw [show (κp + κg + 1) * ε = κp * ε + κg * ε + ε by ring,
        Real.rpow_add hn0, Real.rpow_add hn0]
      ring
    have hev := herrBound _ (A + 1 - s.val) herr'.1
    have heg := herrBound _ (G + 1 - s.val) herr'.2
    have hz' := unweight_boundary_internal R _ _ _ _ Z (by linarith) (norm_nonneg _)
      (Real.sqrt_nonneg _) hz
    have htri := decomposition_triangles_internal Q hQ m j i₀ hR m₀ hn₀ u ψ z φ hψ
    have hv := OptimalLocalization.assemble_profile_internal R (2 - s.val) (A + 1 - s.val) av
      Z P E _ _ _ _ hR1 hav0 (min_le_left _ _) (min_le_right _ _)
      (by positivity) (by positivity) (by positivity) htri.1 hz'.1 hφv hev
    have heg' : Real.sqrt (Q.2 (ψ c - z c - φ c) (ψ c - z c - φ c)) ≤
        E * (R ^ (-((3 - s.val) / 2)) + R ^ (-(G + 1 - s.val))) := by
      apply heg.trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hrpow : R ^ (-(2 - s.val)) ≤ R ^ (-((3 - s.val) / 2)) :=
        Real.rpow_le_rpow_of_exponent_le hR1 (by linarith only [hpgp])
      exact add_le_add hrpow le_rfl
    have hφg' : Real.sqrt (Q.2 (φ c) (φ c)) ≤ P * R ^ (-((3 - s.val) / 2)) := by
      simpa only [neg_div] using hφg
    have hg := OptimalLocalization.assemble_profile_internal R ((3 - s.val) / 2) (G + 1 - s.val) gv
      Z P E _ _ _ _ hR1 hgv0 (min_le_left _ _) (min_le_right _ _)
      (by positivity) (by positivity) (by positivity) htri.2 hz'.2 hφg' heg'
    have hsum : Z + P + 2 * E ≤ B * (n : ℝ) ^ (κ * ε) * ‖χ‖ := by
      have hzcoef := LocalizedMatrix.loss_mono_internal hn1 hε.le hCz.le le_rfl hκz'
      have hpcoef := LocalizedMatrix.loss_mono_internal hn1 hε.le hCφ.le le_rfl hκφ'
      have hecoef := LocalizedMatrix.loss_mono_internal hn1 hε.le
        (show 0 ≤ Ce * Cp * Cg * L by positivity) le_rfl hκe'
      have hh := add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right hzcoef (norm_nonneg χ))
        (mul_le_mul_of_nonneg_right hpcoef (norm_nonneg χ)))
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hecoef (norm_nonneg χ))
          (by norm_num : (0 : ℝ) ≤ 2))
      apply hh.trans
      dsimp only [B]
      nlinarith only [show 0 ≤ Bs * (n : ℝ) ^ (κ * ε) * ‖χ‖ by positivity]
    have lift (t x : ℝ) (htp : t ≤ 2 - s.val)
        (hx : x ≤ (2 ^ t * (Z + P + 2 * E)) * (1 + R) ^ (-t)) :
        x ≤ C * (n : ℝ) ^ (κ * ε) * (1 + R) ^ (-t) * ‖χ‖ := by
      have ht2 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) htp
      have hc : 2 ^ t * (Z + P + 2 * E) ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ := by
        have ht2' : (2 : ℝ) ^ t ≤ 17 ^ (2 - s.val) + 2 ^ (2 - s.val) :=
          ht2.trans (le_add_of_nonneg_left (by positivity))
        have hh := mul_le_mul ht2' hsum
          (by positivity : 0 ≤ Z + P + 2 * E) (by positivity)
        convert hh using 1; dsimp only [C]; ring
      exact hx.trans ((mul_le_mul_of_nonneg_right hc (by positivity)).trans_eq (by ring))
    exact ⟨lift av _ havp hv, lift gv _ hgvp hg⟩

/-- See the proof of Proposition 5.15 in the paper with the uniform induction
property of Subsection 5.5: the two-mode current property implies the
constrained property at both improved exponents. -/
theorem loc_constrained_step (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (A G : ℝ)
    (hAlo : 3 / 2 - s.val ≤ A) (hAhi : A ≤ 2 - s.val)
    (hGlo : 1 - s.val / 2 ≤ G) (hGhi : G ≤ (3 - s.val) / 2) (hGA : G ≤ A)
    (hcurrent : ∀ b, UniformProfile s A G b) :
    UniformProfile s (min (2 - s.val) (A + 1 - s.val))
      (min ((3 - s.val) / 2) (G + 1 - s.val)) true := by
  exact constrained_step_uniform_internal hzeta s A G hAlo hAhi hGlo hGhi hGA (hcurrent false)

/-- See the proof of Proposition 5.15 in the paper with the uniform induction
property of Subsection 5.5: supply the constrained improvement, then compose
the mean correction and the current unrestricted point-source estimates. -/
theorem loc_unconstrained_step (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (A G : ℝ)
    (hAlo : 3 / 2 - s.val ≤ A) (hAhi : A ≤ 2 - s.val)
    (hGlo : 1 - s.val / 2 ≤ G) (hGhi : G ≤ (3 - s.val) / 2) (hGA : G ≤ A)
    (hcurrent : ∀ b, UniformProfile s A G b) :
    UniformProfile s (min (2 - s.val) (A + 1 - s.val))
      (min ((3 - s.val) / 2) (G + 1 - s.val)) false := by
  exact unconstrained_step_uniform_internal hzeta s A G hAlo hGlo (hcurrent false)
    (loc_constrained_step hzeta s A G hAlo hAhi hGlo hGhi hGA hcurrent)

/-- See Proposition 5.15 of the paper: unique constrained and unrestricted solutions
on the full component cycle, with optimal value and intrinsic gradient decay.
The only additional argument is the periodic-zeta connection formula. -/
theorem optimal_pointwise_decay (hzeta : External.PeriodicZeta) :
  ∀ (s : Riesz1.RieszExponent) (κₛ γₛ : ℝ) (M₀ : ℕ+),
    0 < κₛ → 0 < γₛ → ∃ κ : ℝ, 0 < κ ∧
    ∀ ε : ℝ, 0 < ε → ∀ Cₛ : ℝ, 1 ≤ Cₛ →
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
      ∃ C : ℝ, 0 < C ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n m : ℕ+) (_ : 2 ≤ (n : ℕ)) (hm : 2 ≤ (m : ℕ)),
        (n : ℕ) ≤ (m : ℕ) → (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
        let K := (Nat.floor ((n : ℝ) ^ ε)) ^ (M₀ : ℕ)
        1 ≤ K → 4 * K ≤ (m : ℕ) →
        ∀ (d : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin d)))
          (ν : Measure (EuclideanSpace ℝ (Fin d))),
          IsOpen Ω → Convex ℝ Ω → Bornology.IsBounded Ω → Ω.Nonempty →
          IsProbabilityMeasure ν →
          (∃ V : EuclideanSpace ℝ (Fin d) → ℝ,
            IsEuclideanGibbsPotential volume ν Ω V 2) →
          ∀ Q : ScalarFormData ν, IsNeumannRealization Ω Q →
            IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
          ∀ M : EuclideanSpace ℝ (Fin d) → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
            PeriodizedMatrixBounds (ν := ν) s n m hm K Cₛ κₛ γₛ ε M →
            ∀ (i₀ : Fin (m : ℕ)) (χ : Lp ℝ 2 ν) (b : Bool),
              let S := if b then zeroSumComponents (Fin (m : ℕ)) else ⊤
              (∃! u : Fin (m : ℕ) → Q.1, WeightedWeakSolution Q
                (fun x => β.val • M x) S (fun i => if i = i₀ then χ else 0) u) ∧
              (∀ u : Fin (m : ℕ) → Q.1, WeightedWeakSolution Q
                  (fun x => β.val • M x) S (fun i => if i = i₀ then χ else 0) u →
                ∀ j : Fin (m : ℕ),
                  ‖(u j).val‖ ≤ C * (n : ℝ) ^ (κ * ε) *
                    (1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ)) ^ (-(2 - s.val)) * ‖χ‖ ∧
                  Real.sqrt (Q.2 (u j) (u j)) ≤ C * (n : ℝ) ^ (κ * ε) *
                    (1 + (Riesz1.cyclicIndexDistance m j i₀ : ℝ)) ^ (-(3 - s.val) / 2) * ‖χ‖) := by
  exact optimal_decay_of_uniform_step_internal hzeta (loc_constrained_step hzeta)

end Riesz2.OptimalLocalizationPart5
