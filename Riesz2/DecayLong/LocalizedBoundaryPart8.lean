/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.LocalizedBoundaryPart7

/-!
# Projection and the embedded boundary solution

The boundary decomposition in the proof of Proposition 5.15, using the
window, localized matrix, scalar form and exterior resolvent of Subsection 5.5.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter
open scoped BigOperators Classical Fin.NatCast

namespace Riesz2.LocalizedBoundary

open LocalizedMatrix IntervalBoundary

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}

/-- See Subsection 5.5 of the paper: measurable parent coefficients give measurable
entries of the existing localized matrix. -/
theorem localized_matrix_measurable_internal
    (s : Riesz1.RieszExponent) (m m₀ n₀ : ℕ+)
    (hm₀ : 2 ≤ (m₀ : ℕ)) (hn : (n₀ : ℕ) ≤ (m : ℕ))
    (hn₀ : (n₀ : ℕ) ≤ (m₀ : ℕ)) (K : ℕ)
    (A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → Ω → ℝ)
    (hA : ∀ t, Measurable (A t)) (i l : Fin (m₀ : ℕ)) :
    Measurable (fun x => matrix s m m₀ n₀ hm₀ hn hn₀ K A x i l) := by
  unfold matrix
  split_ifs
  · apply Measurable.add _ measurable_const
    unfold internalMatrix
    apply Finset.measurable_sum
    intro t _
    split_ifs
    · exact (hA t).mul_const _
    · exact measurable_const
  · exact measurable_const
  · exact measurable_const

/-- See the proof of Proposition 5.15 in the paper: the matrix bounds
transfer across almost everywhere equality, retaining literal measurability. -/
theorem periodized_bounds_congr_internal
    (s : Riesz1.RieszExponent) (n m : ℕ+) (hm : 2 ≤ (m : ℕ))
    (K : ℕ) (C κ γ ε : ℝ)
    (M N : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M)
    (hNm : ∀ i l, Measurable (fun x => N x i l)) (he : M =ᵐ[ν] N) :
    PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε N := by
  refine ⟨hNm, ?_, ?_⟩
  · filter_upwards [hM.2.1, he] with x hx h
    rwa [← h]
  · obtain ⟨a, ha, hb⟩ := hM.2.2
    refine ⟨a, ha, ?_⟩
    filter_upwards [hb, he] with x hx h
    rwa [← h]

/-- See the proof of Proposition 5.15 in the paper: coercive uniqueness promotes a
constructed solution's property to every unrestricted weak solution. -/
theorem unrestricted_properties_internal
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (s : Riesz1.RieszExponent) (n m : ℕ+) (hm : 2 ≤ (m : ℕ))
    (K : ℕ) (C κ γ ε β : ℝ) (hC : 1 ≤ C) (hβ : 0 < β)
    (M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M)
    (f : Fin (m : ℕ) → Lp ℝ 2 ν) (P : (Fin (m : ℕ) → Q.1) → Prop)
    (h : ∃ u, WeightedWeakSolution Q (fun x => β • M x) ⊤ f u ∧ P u) :
    (∃! u, WeightedWeakSolution Q (fun x => β • M x) ⊤ f u) ∧
      ∀ u, WeightedWeakSolution Q (fun x => β • M x) ⊤ f u → P u := by
  have he := (AbstractEquation.existence_energy Q hQ β hβ M hM.1 _
    (SchurRestriction.periodized_mass_pos hC)
    (hM.2.1.mono (fun _ hx => ⟨hx.1, hx.2.2.1⟩)) ⊤ f).1
  obtain ⟨u, hu, hp⟩ := h
  refine ⟨he, fun v hv => ?_⟩
  rw [he.unique hv hu]
  exact hp

/-- See the proof of Proposition 5.15: assemble the
actual projected source, the exterior resolvent correction and the unique
embedded solution. The exact block identity is an internal input. -/
theorem boundary_embedding_internal
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (s : Riesz1.RieszExponent) (n m : ℕ+) (hm : 2 ≤ (m : ℕ))
    (K : ℕ) (C κ γ ε β : ℝ) (hβ : 0 < β)
    (M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M)
    (χ : Lp ℝ 2 ν) (i₀ j : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1)
    (hu : WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _)
      (fun i => if i = i₀ then χ else 0) u)
    (hR : 0 < Riesz1.cyclicIndexDistance m j i₀)
    (m₀ : ℕ+) (hn₀ : (windowSize m j i₀ : ℕ) ≤ (m₀ : ℕ))
    (hm₀ : 2 ≤ (m₀ : ℕ)) (Cl κl γl εl : ℝ) (hCl : 1 ≤ Cl)
    (Ml : Ω → Matrix (Fin (m₀ : ℕ)) (Fin (m₀ : ℕ)) ℝ)
    (hMl : PeriodizedMatrixBounds (ν := ν) s (windowSize m j i₀) m₀ hm₀ K Cl κl γl εl Ml)
    (Rem : Ω → Matrix (Fin (windowSize m j i₀ : ℕ)) (Fin (windowSize m j i₀ : ℕ)) ℝ)
    (hblock : ∀ x l i, Ml x (l.castLE hn₀) (i.castLE hn₀) + Rem x l i =
      M x (windowEmbedding m j i₀ l) (windowEmbedding m j i₀ i))
    (g : Fin (windowSize m j i₀ : ℕ) → Lp ℝ 2 ν)
    (hg : ∀ l, ∀ᵐ x ∂ν, g l x = -β * ∑ i, Rem x l i *
      (u (windowEmbedding m j i₀ i)).val x) :
    let n₀ := windowSize m j i₀
    let pv := (MatrixEnergy.vectorEquiv Q hQ).symm (fun i => u (windowEmbedding m j i₀ i))
    let J := SchurRestriction.assemble Q hQ n₀ m₀ hn₀
    let H := fun _ : Ω => (2 : ℝ) • referenceIntervalMatrix s m₀ hm₀ K
    ∃ lam : Lp ℝ 2 ν,
      (∀ᵐ x ∂ν, lam x = gapMultiplierField m Q (fun x => β • M x)
        (fun i => if i = i₀ then χ else 0) u x) ∧
      (∀ l ∈ window m j i₀, ∀ v : Q.1,
        Integrable (fun x => ∑ i ∈ window m j i₀, β * M x l i * (u i).val x * v.val x) ν ∧
        Integrable (fun x => ∑ i ∈ (window m j i₀)ᶜ, β * M x l i * (u i).val x * v.val x) ν ∧
        Q.2 (u l) v + (∫ x, ∑ i ∈ window m j i₀, β * M x l i * (u i).val x * v.val x ∂ν) =
          -(∫ x, ∑ i ∈ (window m j i₀)ᶜ, β * M x l i * (u i).val x * v.val x ∂ν) +
            inner ℝ lam v.val) ∧
      ∃ w : MatrixEnergy.Vector (ι := Fin ((m₀ : ℕ) - (n₀ : ℕ))) Q hQ,
        (∀ v : MatrixEnergy.Vector (ι := Fin ((m₀ : ℕ) - (n₀ : ℕ))) Q hQ,
          β⁻¹ * (∑ i, Q.2 (MatrixEnergy.vectorEquiv Q hQ w i) (MatrixEnergy.vectorEquiv Q hQ v i)) +
            (∫ x, matrixFieldPair H
              (fun i => (MatrixEnergy.vectorEquiv Q hQ (J (0, w)) i).val)
              (fun i => (MatrixEnergy.vectorEquiv Q hQ (J (0, v)) i).val) x ∂ν) =
            ∫ x, matrixFieldPair H
              (fun i => (MatrixEnergy.vectorEquiv Q hQ (J (pv, 0)) i).val)
              (fun i => (MatrixEnergy.vectorEquiv Q hQ (J (0, v)) i).val) x ∂ν) ∧
        ∃ δV : Fin (n₀ : ℕ) → Lp ℝ 2 ν,
          (∀ l, ∀ᵐ x ∂ν, δV l x =
            -β * (∑ i ∈ (window m j i₀)ᶜ, M x (windowEmbedding m j i₀ l) i * (u i).val x) -
              (∑ i, (MatrixEnergy.vectorEquiv Q hQ (J (0, w)) i).val x *
                (β * Ml x i (l.castLE hn₀))) + lam x) ∧
          (∃! ψ₀ : Fin (m₀ : ℕ) → Q.1,
            WeightedWeakSolution Q (fun x => β • Ml x) ⊤
              (SchurRestriction.extendSource n₀ m₀ hn₀
                (WithLp.toLp 2 (fun i => δV i + g i))).ofLp ψ₀) ∧
          ∀ ψ₀ : Fin (m₀ : ℕ) → Q.1,
            WeightedWeakSolution Q (fun x => β • Ml x) ⊤
              (SchurRestriction.extendSource n₀ m₀ hn₀
                (WithLp.toLp 2 (fun i => δV i + g i))).ofLp ψ₀ →
            ∀ i : Fin (n₀ : ℕ), ψ₀ (i.castLE hn₀) = u (windowEmbedding m j i₀ i) := by
  dsimp only
  obtain ⟨lam, hlam, q, hq, hrows⟩ := projected_rows_internal Q s n m hm K C κ γ ε β M hM
    χ i₀ j u hu hR m₀ hn₀ Ml hMl.1 (SchurRestriction.periodized_scaled_bounded 1 hMl |>.imp
      (fun B hB => by simpa only [one_smul] using hB)) Rem hblock g hg
  let p := fun i => u (windowEmbedding m j i₀ i)
  have ha := active_form_from_rows_internal Q hQ s (windowSize m j i₀) m₀ hn₀ hm₀ K
    Cl κl γl εl β hCl hβ Ml hMl p (fun i => q i + g i) hrows
  obtain ⟨c, hc, ψ₀, hψ₀, _⟩ := harmonic_embedding_internal Q hQ s (windowSize m j i₀)
    m₀ hn₀ hm₀ K Cl κl γl εl β hCl hβ Ml hMl p (fun i => q i + g i) ha
  obtain ⟨lam', hlam', hproj⟩ := projected_equation s n m hm K C κ γ ε Q M hM β χ i₀ u hu
  have helam : lam' = lam := by
    apply Lp.ext
    filter_upwards [hlam', hlam] with x hx hy
    exact hx.trans hy.symm
  subst lam'
  let pv := (MatrixEnergy.vectorEquiv Q hQ).symm p
  let w := SchurRestriction.exteriorResponse Q hQ (windowSize m j i₀) m₀ hn₀ s hm₀ K
    Cl κl γl εl β hCl hβ Ml hMl pv
  let δV := fun i => q i - c i
  have he (i) : q i + g i - c i = δV i + g i := by dsimp [δV]; abel
  refine ⟨lam, hlam, hproj _ (source_not_mem_window m j i₀ hR), w, ?_, δV, ?_, ?_⟩
  · exact SchurRestriction.exterior_resolvent_equation Q hQ (windowSize m j i₀) m₀ hn₀
      s hm₀ K Cl κl γl εl β hCl hβ Ml hMl pv
  · intro l
    filter_upwards [Lp.coeFn_sub (q l) (c l), hq l, hc l] with x hx hy hz
    change (q l - c l) x = _
    rw [hx, Pi.sub_apply, hy, hz]
    ring
  · apply unrestricted_properties_internal Q hQ s (windowSize m j i₀) m₀ hm₀ K
      Cl κl γl εl β hCl hβ Ml hMl
    exact ⟨ψ₀, by simpa only [he] using hψ₀.1, hψ₀.2⟩

/-- The boundary decomposition and estimate (5.64) in the proof of
Proposition 5.15. The exterior field and the
unique unrestricted solutions are those of Subsection 5.5: the negative
remainder source, the full exterior resolvent, its negative Schur correction,
and exact agreement with the original solution on the ordered window.
All sources are L² classes. The projected integrals are explicitly integrable.
The constants precede every scalar probability space, size, matrix and source,
and are uniform on each closed positive temperature interval. -/
theorem loc_boundary (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ)
    (hκstar : 0 < κstar) (hγstar : 0 < γstar) (M₀ : ℕ+) :
    ∃ κ D : ℝ, 0 < κ ∧ 0 < D ∧
    ∀ ε : ℝ, 0 < ε → ∀ Cstar : ℝ, 1 ≤ Cstar →
    ∀ βlo : ℝ, 0 < βlo → ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
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
        dsimp only [n₀]
        have := (LocalizedMatrix.window_size_bounds m j i₀ hR).2.2.2; omega
      let hn₀ : (n₀ : ℕ) ≤ (m₀ : ℕ) := by
        dsimp only [n₀, m₀]
        have := LocalizedMatrix.two_windowSize_lt_period s m j i₀ hR; omega
      let hm₀ : 2 ≤ (m₀ : ℕ) := by
        dsimp only [m₀]
        have := LocalizedMatrix.two_windowSize_lt_period s m j i₀ hR
        have := (LocalizedMatrix.windowSize m j i₀).pos; omega
      let b := j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ))
      let P := fun x (l i : Fin (n₀ : ℕ)) => M x (l.castLE hn + b) (i.castLE hn + b)
      let Ml := LocalizedMatrix.matrix s m m₀ n₀ hm₀ hn hn₀ K
        (fun t => A (t.1 + b, t.2))
      let Rem := LocalizedMatrix.remainder s m m₀ n₀ hm₀ hn hn₀ K
        (fun t => A (t.1 + b, t.2)) P
      let c : Fin (m₀ : ℕ) := ⟨Riesz1.cyclicIndexDistance m j i₀ / 8, by
        have hc := LocalizedMatrix.window_card m j i₀
        have := LocalizedMatrix.two_windowSize_lt_period s m j i₀ hR
        change _ < (LocalizedMatrix.windowPeriod s m j i₀ : ℕ)
        change (LocalizedMatrix.window m j i₀).card = _ at hc
        change 2 * (LocalizedMatrix.window m j i₀).card < _ at this
        omega⟩
      ∀ β : ℝ, βlo ≤ β → β ≤ βhi →
      ∀ (χ : Lp ℝ 2 ν) (u : Fin (m : ℕ) → Q.1),
      WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _)
        (fun i => if i = i₀ then χ else 0) u →
      ∃ g : Fin (n₀ : ℕ) → Lp ℝ 2 ν,
        (∀ l, ∀ᵐ x ∂ν, g l x = -β * ∑ i, Rem x l i *
          (u (LocalizedMatrix.windowEmbedding m j i₀ i)).val x) ∧
        (let pv := (MatrixEnergy.vectorEquiv Q hQ).symm (fun i => u (windowEmbedding m j i₀ i))
         let J := SchurRestriction.assemble Q hQ n₀ m₀ hn₀
         let H := fun _ : Ω => (2 : ℝ) • referenceIntervalMatrix s m₀ hm₀ K
         ∃ lam : Lp ℝ 2 ν,
           (∀ᵐ x ∂ν, lam x = gapMultiplierField m Q (fun x => β • M x)
             (fun i => if i = i₀ then χ else 0) u x) ∧
           (∀ l ∈ window m j i₀, ∀ v : Q.1,
             Integrable (fun x => ∑ i ∈ window m j i₀, β * M x l i * (u i).val x * v.val x) ν ∧
             Integrable (fun x => ∑ i ∈ (window m j i₀)ᶜ, β * M x l i * (u i).val x * v.val x) ν ∧
             Q.2 (u l) v + (∫ x, ∑ i ∈ window m j i₀, β * M x l i * (u i).val x * v.val x ∂ν) =
               -(∫ x, ∑ i ∈ (window m j i₀)ᶜ, β * M x l i * (u i).val x * v.val x ∂ν) +
                 inner ℝ lam v.val) ∧
           ∃ w : MatrixEnergy.Vector (ι := Fin ((m₀ : ℕ) - (n₀ : ℕ))) Q hQ,
             (∀ v : MatrixEnergy.Vector (ι := Fin ((m₀ : ℕ) - (n₀ : ℕ))) Q hQ,
               β⁻¹ * (∑ i, Q.2 (MatrixEnergy.vectorEquiv Q hQ w i) (MatrixEnergy.vectorEquiv Q hQ v i)) +
                 (∫ x, matrixFieldPair H
                   (fun i => (MatrixEnergy.vectorEquiv Q hQ (J (0, w)) i).val)
                   (fun i => (MatrixEnergy.vectorEquiv Q hQ (J (0, v)) i).val) x ∂ν) =
                 ∫ x, matrixFieldPair H
                   (fun i => (MatrixEnergy.vectorEquiv Q hQ (J (pv, 0)) i).val)
                   (fun i => (MatrixEnergy.vectorEquiv Q hQ (J (0, v)) i).val) x ∂ν) ∧
             ∃ δV : Fin (n₀ : ℕ) → Lp ℝ 2 ν,
               (∀ l, ∀ᵐ x ∂ν, δV l x =
                 -β * (∑ i ∈ (window m j i₀)ᶜ, M x (windowEmbedding m j i₀ l) i * (u i).val x) -
                   (∑ i, (MatrixEnergy.vectorEquiv Q hQ (J (0, w)) i).val x *
                     (β * Ml x i (l.castLE hn₀))) + lam x) ∧
               (∃! ψ₀ : Fin (m₀ : ℕ) → Q.1,
                 WeightedWeakSolution Q (fun x => β • Ml x) ⊤
                   (SchurRestriction.extendSource n₀ m₀ hn₀
                     (WithLp.toLp 2 (fun i => δV i + g i))).ofLp ψ₀) ∧
               ∀ ψ₀ : Fin (m₀ : ℕ) → Q.1,
                 WeightedWeakSolution Q (fun x => β • Ml x) ⊤
                   (SchurRestriction.extendSource n₀ m₀ hn₀
                     (WithLp.toLp 2 (fun i => δV i + g i))).ofLp ψ₀ →
                 ∀ i : Fin (n₀ : ℕ), ψ₀ (i.castLE hn₀) = u (windowEmbedding m j i₀ i)) ∧
        (∃! z : Fin (m₀ : ℕ) → Q.1,
          WeightedWeakSolution Q (fun x => β • Ml x) ⊤
            (fun i => ∑ l : Fin (n₀ : ℕ), if i = l.castLE hn₀ then g l else 0) z) ∧
        ∀ z : Fin (m₀ : ℕ) → Q.1,
          WeightedWeakSolution Q (fun x => β • Ml x) ⊤
            (fun i => ∑ l : Fin (n₀ : ℕ), if i = l.castLE hn₀ then g l else 0) z →
          (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (2 - s.val) * ‖(z c).val‖ +
            (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ ((3 - s.val) / 2) *
              Real.sqrt (Q.2 (z c) (z c)) ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ := by
  obtain ⟨κl, γl, Dl, hκl, hγl, hDl, hlocal⟩ :=
    localized_periodizedMatrixBounds s κstar γstar M₀ hκstar hγstar
  obtain ⟨κ, Dz, hκ, hDz, hdecay⟩ :=
    boundary_remainder_decay hzeta s κstar γstar hκstar hγstar M₀
  refine ⟨κ, max Dl Dz, hκ, hDl.trans_le (le_max_left _ _), ?_⟩
  intro ε hε Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Cl, hCl, hlocal⟩ := hlocal Cstar hCstar
  obtain ⟨C, hC, hdecay⟩ := hdecay ε hε Cstar hCstar βlo hβlo βhi hβhi
  refine ⟨C, hC, ?_⟩
  intro X _ ρ _ Q hQ hQc n m hm hn hnm hmn K hK hKm M hM
  obtain ⟨A, hAm, hArep, hdecay⟩ := hdecay ρ Q hQ hQc n m hm hn hnm hmn hK hKm M hM
  obtain ⟨B, hBm, hBrep, hlocal⟩ := hlocal ρ ε hε n m hn hm M hM
  refine ⟨A, hAm, hArep, fun j i₀ hR hsep => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ (n : ℕ) by omega)
  have hDlsep : (n : ℝ) ^ (Dl * ε) ≤ (Riesz1.cyclicIndexDistance m j i₀ : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hn1
      (mul_le_mul_of_nonneg_right (le_max_left Dl Dz) hε.le)).trans hsep
  have hDzsep : (n : ℝ) ^ (Dz * ε) ≤ (Riesz1.cyclicIndexDistance m j i₀ : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hn1
      (mul_le_mul_of_nonneg_right (le_max_right Dl Dz) hε.le)).trans hsep
  dsimp only
  intro β hβl hβu χ u hu
  obtain ⟨g, hg, hz⟩ := hdecay j i₀ hR hDzsep β hβl hβu χ u hu
  let n₀ := windowSize m j i₀
  let m₀ := windowPeriod s m j i₀
  have hsize := window_size_bounds m j i₀ hR
  have htw := two_windowSize_lt_period s m j i₀ hR
  have hn₀ : (n₀ : ℕ) ≤ (m₀ : ℕ) := by dsimp [n₀, m₀]; omega
  have hnp : (n₀ : ℕ) ≤ (m : ℕ) := by dsimp [n₀]; omega
  have hm₀ : 2 ≤ (m₀ : ℕ) := by have := n₀.pos; dsimp [n₀, m₀] at *; omega
  let b : Fin (m : ℕ) := j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ))
  let Ml := matrix s m m₀ n₀ hm₀ hnp hn₀ K (fun t => A (t.1 + b, t.2))
  let Mb := matrix s m m₀ n₀ hm₀ hnp hn₀ K (fun t => B (t.1 + b, t.2))
  let P := fun x (l i : Fin (n₀ : ℕ)) => M x (l.castLE hnp + b) (i.castLE hnp + b)
  let Rem := remainder s m m₀ n₀ hm₀ hnp hn₀ K (fun t => A (t.1 + b, t.2)) P
  let ε₀ := ε * Real.log n / Real.log n₀
  have hMb : PeriodizedMatrixBounds (ν := ρ) s n₀ m₀ hm₀ K Cl κl γl ε₀ Mb :=
    hlocal j i₀ hR hDlsep
  have heq : Mb =ᵐ[ρ] Ml := by
    filter_upwards [hArep, hBrep] with x ha hb
    exact matrix_eq_of_intervalMatrix_eq_internal s m m₀ n₀ hm₀ hnp hn₀
      (by dsimp [n₀]; omega) K B A x (hb.2.trans ha.2.symm) b
  have hMl : PeriodizedMatrixBounds (ν := ρ) s n₀ m₀ hm₀ K Cl κl γl ε₀ Ml :=
    periodized_bounds_congr_internal s n₀ m₀ hm₀ K Cl κl γl ε₀ Mb Ml hMb
      (localized_matrix_measurable_internal s m m₀ n₀ hm₀ hnp hn₀ K _ (fun t => hAm _)) heq
  have hblock (x) (l i : Fin (n₀ : ℕ)) :
      Ml x (l.castLE hn₀) (i.castLE hn₀) + Rem x l i =
        M x (windowEmbedding m j i₀ l) (windowEmbedding m j i₀ i) := by
    have hl : windowEmbedding m j i₀ l = l.castLE hnp + b :=
      (windowEmbedding_apply m j i₀ l hnp).trans (add_comm _ _)
    have hi : windowEmbedding m j i₀ i = i.castLE hnp + b :=
      (windowEmbedding_apply m j i₀ i hnp).trans (add_comm _ _)
    rw [hl, hi]
    exact matrix_add_remainder s m m₀ n₀ hm₀ hnp hn₀ K
      (fun t => A (t.1 + b, t.2)) P x l i
  refine ⟨g, hg, ?_, ?_⟩
  · exact boundary_embedding_internal Q hQ s n m hm K Cstar κstar γstar ε β
      (hβlo.trans_le hβl) M hM χ i₀ j u hu (by omega) m₀ hn₀ hm₀ Cl κl γl ε₀ hCl Ml hMl
      Rem hblock g hg
  · apply unrestricted_properties_internal Q hQ s n₀ m₀ hm₀ K Cl κl γl ε₀ β hCl
      (hβlo.trans_le hβl) Ml hMl
    obtain ⟨z, hz, _⟩ := hz
    exact ⟨z, hz⟩

end Riesz2.LocalizedBoundary
