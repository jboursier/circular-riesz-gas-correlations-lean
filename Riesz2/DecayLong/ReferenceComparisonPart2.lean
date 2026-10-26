/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.ReferenceComparison
public import Riesz2.DecayLong.ReferenceComparisonError
public import Riesz2.DecayLong.LocalizedBoundaryPart8

/-!
# The comparison error for the actual exterior field

See the proof of Proposition 5.15 in the paper. The boundary decomposition and the
reference estimates are composed over the original scalar form. Uniqueness of
the normalized exterior equation identifies their field witnesses.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Finset
open scoped BigOperators Classical Fin.NatCast

namespace Riesz2.ReferenceComparisonPart2

/-- Zero extension agrees with the finite sum used for the boundary source
in Subsection 5.5. -/
theorem extendSource_sum_internal {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
    (f : Fin (n : ℕ) → Lp ℝ 2 ν) (i : Fin (m : ℕ)) :
    (SchurRestriction.extendSource n m hnm (WithLp.toLp 2 f)).ofLp i =
      ∑ l : Fin (n : ℕ), if i = l.castLE hnm then f l else 0 := by
  rw [show (SchurRestriction.extendSource n m hnm (WithLp.toLp 2 f)).ofLp i =
    (SchurRestriction.extendSource n m hnm (WithLp.toLp 2 f)) i from rfl,
    LocalizedFieldPart4.extendSource_apply_internal]
  split_ifs with hi
  · let l : Fin (n : ℕ) := ⟨i.val, hi⟩
    rw [sum_eq_single l]
    · rw [ite_eq_left (show i = l.castLE hnm from Fin.ext rfl)]
    · intro k _ hkl
      rw [ite_eq_right]
      intro he
      apply hkl
      exact Fin.ext (congrArg Fin.val he).symm
    · exact fun h => (h (mem_univ l)).elim
  · symm
    apply sum_eq_zero
    intro l _
    rw [ite_eq_right]
    intro he
    have hei : i.val = l.val := congrArg Fin.val he
    have := l.isLt
    omega

/-- See the proof of Proposition 5.15 in the paper: the exact equation and both
bounds for the comparison error of Subsection 5.5, with all fields and weak
solutions constructed from the constrained point source. Loss exponents
precede ε and prefactors. Prefactors are uniform on compact positive
temperature intervals. The full reference inverse retains the constant mode. -/
theorem loc_error_source (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ)
    (hκstar : 0 < κstar) (hγstar : 0 < γstar) (M₀ : ℕ+) :
    ∃ κ D : ℝ, 0 < κ ∧ 0 < D ∧ ∀ ε : ℝ, 0 < ε →
    ∀ Cstar : ℝ, 1 ≤ Cstar →
    ∀ (βlo : ℝ) (hβlo : 0 < βlo), ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
      (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q), IsConservativeScalarForm Q →
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
    let Rem := LocalizedMatrix.remainder s m m₀ n₀ hm₀ hn hn₀ K
      (fun t => A (t.1 + b, t.2)) P
    let c : Fin (m₀ : ℕ) := ⟨Riesz1.cyclicIndexDistance m j i₀ / 8, by
      have hc := LocalizedMatrix.window_card m j i₀
      have ht := LocalizedMatrix.two_windowSize_lt_period s m j i₀ hR
      change _ < (LocalizedMatrix.windowPeriod s m j i₀ : ℕ)
      change (LocalizedMatrix.windowSize m j i₀ : ℕ) = _ at hc
      omega⟩
    ∀ (β : ℝ) (hβl : βlo ≤ β) (_hβu : β ≤ βhi),
    ∀ (χ : Lp ℝ 2 ν) (u : Fin (m : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _)
      (fun i => if i = i₀ then χ else 0) u →
    let pv := (MatrixEnergy.vectorEquiv Q hQ).symm
      (fun i => u (LocalizedMatrix.windowEmbedding m j i₀ i))
    let J := SchurRestriction.assemble Q hQ n₀ m₀ hn₀
    let H := fun _ : Ω => (2 : ℝ) • referenceIntervalMatrix s m₀ hm₀ K
    ∃ r : Fin (n₀ : ℕ) → Lp ℝ 2 ν,
      (∀ l, ∀ᵐ x ∂ν, r l x = -β * ∑ i, Rem x l i *
        (u (LocalizedMatrix.windowEmbedding m j i₀ i)).val x) ∧
    ∃ lam : Lp ℝ 2 ν,
      (∀ᵐ x ∂ν, lam x = gapMultiplierField m Q (fun x => β • M x)
        (fun i => if i = i₀ then χ else 0) u x) ∧
    ∃ U : Fin (n₀ : ℕ) → Lp ℝ 2 ν,
      (∀ l, ∀ᵐ x ∂ν, U l x = ∑ i ∈ (LocalizedMatrix.window m j i₀)ᶜ,
        M x (LocalizedMatrix.windowEmbedding m j i₀ l) i * (u i).val x) ∧
    ∃ w : MatrixEnergy.Vector (ι := Fin ((m₀ : ℕ) - (n₀ : ℕ))) Q hQ,
      (∀ v : MatrixEnergy.Vector (ι := Fin ((m₀ : ℕ) - (n₀ : ℕ))) Q hQ,
        β⁻¹ * (∑ i, Q.2 (MatrixEnergy.vectorEquiv Q hQ w i) (MatrixEnergy.vectorEquiv Q hQ v i)) +
          (∫ x, matrixFieldPair H (fun i => (MatrixEnergy.vectorEquiv Q hQ (J (0,w)) i).val)
            (fun i => (MatrixEnergy.vectorEquiv Q hQ (J (0,v)) i).val) x ∂ν) =
          ∫ x, matrixFieldPair H (fun i => (MatrixEnergy.vectorEquiv Q hQ (J (pv,0)) i).val)
            (fun i => (MatrixEnergy.vectorEquiv Q hQ (J (0,v)) i).val) x ∂ν) ∧
    ∃ V : Fin (n₀ : ℕ) → Lp ℝ 2 ν,
      (∀ l, V l = (-β) • U l - β • LocalizedFieldPart3.referenceRow Q hQ s n₀ m₀ hm₀ K
        (LocalizedFieldPart3.exteriorReindex Q hQ n₀ m₀ hn₀ w) (l.castLE hn₀) + lam) ∧
    let f := (SchurRestriction.extendSource n₀ m₀ hn₀ (WithLp.toLp 2 V)).ofLp
    let rb := (SchurRestriction.extendSource n₀ m₀ hn₀ (WithLp.toLp 2 r)).ofLp
    ∃ ψ₀ z : Fin (m₀ : ℕ) → Q.1,
      WeightedWeakSolution Q (fun x => β • Ml x) ⊤ (fun i => f i + rb i) ψ₀ ∧
      (∀ i : Fin (n₀ : ℕ), ψ₀ (i.castLE hn₀) = u (LocalizedMatrix.windowEmbedding m j i₀ i)) ∧
      WeightedWeakSolution Q (fun x => β • Ml x) ⊤ rb z ∧
    let φ := ReferenceComparison.referenceSolution Q hQ s ⟨β, hβlo.trans_le hβl⟩ m₀ hm₀ f
    ∃ g : Fin (m₀ : ℕ) → Lp ℝ 2 ν,
      (∀ i, ∀ᵐ x ∂ν, g i x = -β * ∑ l,
        (Ml x i l - ((2 : ℝ) • referenceIntervalMatrix s m₀ hm₀ 1) i l) * (φ l).val x) ∧
      WeightedWeakSolution Q (fun x => β • Ml x) ⊤ g (fun i => ψ₀ i - z i - φ i) ∧
      (∑ i, ‖g i‖) ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ *
        (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (-(1-s.val)) ∧
      ∀ i, (Riesz1.cyclicIndexDistance m₀ i c : ℝ) ≤
        (Riesz1.cyclicIndexDistance m j i₀ : ℝ) / 64 →
        ‖g i‖ ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ *
          (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (-(2-s.val)) := by
  obtain ⟨κφ, Dφ, hκφ, hDφ, href⟩ :=
    ReferenceComparison.loc_reference_solution hzeta s κstar γstar hκstar hγstar M₀
  obtain ⟨κb, Db, hκb, hDb, hboundary⟩ :=
    LocalizedBoundary.loc_boundary hzeta s κstar γstar hκstar hγstar M₀
  obtain ⟨κl, γl, Dl, hκl, hγl, hDl, hlocal⟩ :=
    ReferenceComparisonError.localization_for_representation_internal s κstar γstar M₀ hκstar hγstar
  obtain ⟨κ, hκ, hcomp⟩ :=
    ReferenceComparisonError.comparison_error_of_reference_estimates_internal s κl γl κφ hκl.le hκφ.le M₀
  let D := max (max Dφ Db) (max Dl (8 * (M₀ : ℕ)))
  refine ⟨κ, D, hκ, hDφ.trans_le ((le_max_left Dφ Db).trans (le_max_left _ _)), ?_⟩
  intro ε hε Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Cφ, hCφ, href⟩ := href ε hε Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Cb, hCb, hboundary⟩ := hboundary ε hε Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Cl, hCl, hlocal⟩ := hlocal Cstar hCstar
  obtain ⟨C, hC, hcomp⟩ := hcomp Cl hCl Cφ hCφ βhi (hβlo.trans_le hβhi)
  refine ⟨C, hC, ?_⟩
  intro Ω _ ν _ Q hQ hQc n m hm hn hnm hmn K hK hKm M hM
  obtain ⟨A, hAm, hArep, hb⟩ := hboundary ν Q hQ hQc n m hm hn hnm hmn hK hKm M hM
  refine ⟨A, hAm, hArep, ?_⟩
  intro j i₀ hR hsep n₀ m₀ hnp hn₀ hm₀ b P Ml Rem c β hβl hβu χ u hu pv J H
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ (n : ℕ) by omega)
  have sep (d : ℝ) (hd : d ≤ D) :
      (n : ℝ) ^ (d * ε) ≤ (Riesz1.cyclicIndexDistance m j i₀ : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hn1 (mul_le_mul_of_nonneg_right hd hε.le)).trans hsep
  have hsepφ := sep Dφ ((le_max_left Dφ Db).trans (le_max_left _ _))
  have hsepb := sep Db ((le_max_right Dφ Db).trans (le_max_left _ _))
  have hsepl := sep Dl ((le_max_left Dl _).trans (le_max_right _ _))
  have hsepc := sep (8 * (M₀ : ℕ)) ((le_max_right Dl _).trans (le_max_right _ _))
  have hMl := hlocal ν ε hε n m hn hm M hM A hAm (hArep.mono fun _ hx => hx.2) j i₀ hR hsepl
  obtain ⟨r, hr, hbdata, hzexists, _⟩ := hb j i₀ hR hsepb β hβl hβu χ u hu
  obtain ⟨lam, hlam, _, wb, hwb, Vb, hVb, hψexists, hψactive⟩ := hbdata
  obtain ⟨lamf, hlamf, U, hU, w, hw, V, hV, hφ⟩ :=
    href ν Q hQ hQc n m hm hn hnm hmn hK hKm M hM β hβl hβu χ i₀ u hu j hR hsepφ
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
    simpa only [rb, funext (extendSource_sum_internal n₀ m₀ hn₀ r)] using hz
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
  refine ⟨r, hr, lam, hlam, U, hU, w, hw, V, hV, ψ₀, z, hψ', hψactive ψ₀ hψ, hz', ?_⟩
  simpa only [ReferenceComparison.referenceSolution, map_sum] using he

end Riesz2.ReferenceComparisonPart2
