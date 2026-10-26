/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.LocalizedFieldPart4

/-!
# Uniform boundary and exterior field estimates

Boundary and exterior field estimates in the proof of Proposition 5.15.
The loss exponents precede εmin. A single prefactor controls every
ε ≥ εmin > 0, with the original cutoffs, scalar forms and solution domains.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Finset
open scoped BigOperators Classical Fin.NatCast

namespace Riesz2.OptimalLocalizationPart3

open LocalizedBoundary LocalizedMatrix LocalizedField LocalizedFieldPart4

/-- See the proof of Proposition 5.15 in the paper: the original window norm, with one
prefactor for every ε ≥ εmin > 0. -/
theorem original_solution_window_decay (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ)
    (hκstar : 0 < κstar) (hγstar : 0 < γstar) (M₀ : ℕ+) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ εmin : ℝ, 0 < εmin →
    ∀ Cstar : ℝ, 1 ≤ Cstar →
    ∀ βlo : ℝ, 0 < βlo → ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, εmin ≤ ε →
    ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
      (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
    ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ)),
    2 ≤ (n : ℕ) → (n : ℕ) ≤ (m : ℕ) →
    (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
    let K := ⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ)
    1 ≤ K → 4 * K ≤ (m : ℕ) →
    ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M →
    ∀ β : ℝ, βlo ≤ β → β ≤ βhi →
    ∀ (χ : Lp ℝ 2 ν) (i₀ j : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _)
      (fun i => if i = i₀ then χ else 0) u →
    0 < Riesz1.cyclicIndexDistance m j i₀ →
    (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (3 / 2 - s.val) *
      Real.sqrt (∑ i ∈ LocalizedMatrix.window m j i₀, ‖(u i).val‖ ^ 2) ≤
        C * (n : ℝ) ^ (κ * ε) * ‖χ‖ := by
  obtain ⟨κ, hκ, hb⟩ := LocalizedMatrix.Analytic.global_decay_bounds hzeta s κstar γstar
    hκstar hγstar M₀
  refine ⟨κ, hκ, fun εmin hεmin Cstar hCstar βlo hβlo βhi hβhi => ?_⟩
  obtain ⟨C, hC, hb⟩ := hb εmin hεmin Cstar hCstar βlo hβlo βhi hβhi
  refine ⟨2 ^ (3 / 2 - s.val) * C, by positivity, ?_⟩
  intro ε hεge Ω _ ν _ Q hQ hQc n m hm hn hnm hmn K hK hKm M hM β hβloβ hββhi χ i₀ j u hu hR
  obtain ⟨lam, _, _, hweighted, _, _⟩ :=
    hb ε hεge ν Q hQ hQc n m hm hn hnm hmn hK hKm M hM β hβloβ hββhi χ i₀ u hu
  have hv : Real.sqrt (∑ i, (weightRadius m i i₀ ^ (3 / 2 - s.val) * ‖(u i).val‖) ^ 2) ≤
      C * (n : ℝ) ^ (κ * ε) * ‖χ‖ := by
    linarith only [hweighted, Real.sqrt_nonneg
      (∑ i, weightRadius m i i₀ ^ (2 * (1 - s.val / 2)) * Q.2 (u i) (u i))]
  exact (window_norm_internal m j i₀ hR (3 / 2 - s.val)
    (by linarith [s.property.2]) (fun i => (u i).val)).trans
      ((mul_le_mul_of_nonneg_left hv (by positivity)).trans_eq (by ring))

/-- See the proof of Proposition 5.15 and equation (5.64) of the paper: the
remainder source and its unique solution, uniformly for ε ≥ εmin > 0.
The local loss ε₀ is bounded below by εmin/(3/2+1/s). -/
theorem boundary_remainder_decay (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ)
    (hκstar : 0 < κstar) (hγstar : 0 < γstar) (M₀ : ℕ+) :
    ∃ κ D : ℝ, 0 < κ ∧ 0 < D ∧
    ∀ εmin : ℝ, 0 < εmin → ∀ Cstar : ℝ, 1 ≤ Cstar →
    ∀ βlo : ℝ, 0 < βlo → ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, εmin ≤ ε →
    ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
      (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
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
        ∃! z : Fin (m₀ : ℕ) → Q.1,
          WeightedWeakSolution Q (fun x => β • Ml x) ⊤
            (fun i => ∑ l : Fin (n₀ : ℕ), if i = l.castLE hn₀ then g l else 0) z ∧
          (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (2 - s.val) * ‖(z c).val‖ +
            (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ ((3 - s.val) / 2) *
              Real.sqrt (Q.2 (z c) (z c)) ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ := by
  obtain ⟨κl, γl, Dl, hκl, hγl, hDl, hlocal⟩ :=
    LocalizedMatrix.localized_periodizedMatrixBounds s κstar γstar M₀ hκstar hγstar
  obtain ⟨κu, hκu, hsolve⟩ := unrestricted_superposition_separate hzeta s κl γl hκl hγl M₀
  obtain ⟨κg, hκg, hglobal⟩ := original_solution_window_decay hzeta s κstar γstar hκstar hγstar M₀
  obtain ⟨Cs, hCs, hconv⟩ := boundary_convolution_sharp s
  obtain ⟨Ct, hCt, hscale⟩ := boundary_decay_scaling_sharp_internal s
  have hs0 := s.property.1
  have hs1 : 0 < 1 - s.val := sub_pos.mpr s.property.2
  let D := max Dl (8 * (M₀ : ℕ))
  refine ⟨κu + κstar + κg, D, by positivity, hDl.trans_le (le_max_left _ _), ?_⟩
  intro εmin hεmin_pos Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Cl, hCl, hlocal⟩ := hlocal Cstar hCstar
  obtain ⟨Cu, hCu, hsolve⟩ := hsolve (εmin / (3 / 2 + 1 / s.val)) (by positivity)
    Cl hCl βlo hβlo βhi hβhi
  obtain ⟨Cg, hCg, hglobal⟩ := hglobal εmin hεmin_pos Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Cp, hCp, hrow⟩ := window_row_for_representation_internal s
  let B := 4 * Real.sqrt (2 + 1 / (1 + s.val)) * Cstar + Cp
  let H := 4 ^ ((1 + s.val) / 2) * (2 / (s.val / 2)) +
    4 ^ (1 - s.val / 2) * (2 / ((1 - s.val) / 2))
  let Hs := Cs * (8 ^ ((1 + s.val) / 2) + 8 ^ (1 - s.val / 2)) + H * 8 ^ (1 / 2 : ℝ)
  have hHs : 0 < Hs := by dsimp [Hs]; positivity
  have hβhi0 : 0 < βhi := hβlo.trans_le hβhi
  have hB : 0 < B := by dsimp [B]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨Ct * Hs * (Cu * βhi * B) * Cg, by positivity, ?_⟩
  intro ε hεge X _ ρ _ Q hQ hQc n m hm hn hnm hmn K hK hKm M hM
  have hε : 0 < ε := hεmin_pos.trans_le hεge
  obtain ⟨A, hAm, hArep, hlocal⟩ := hlocal ρ ε hε n m hn hm M hM
  refine ⟨A, hAm, hArep, fun j i₀ hR hsep => ?_⟩
  dsimp only
  intro β hβl hβu χ u hu
  let n₀ := LocalizedMatrix.windowSize m j i₀
  let m₀ := LocalizedMatrix.windowPeriod s m j i₀
  have hsize := LocalizedMatrix.window_size_bounds m j i₀ hR
  have htw := LocalizedMatrix.two_windowSize_lt_period s m j i₀ hR
  have hn₀ : (n₀ : ℕ) ≤ (m₀ : ℕ) := by dsimp [n₀, m₀]; omega
  have hnp : (n₀ : ℕ) ≤ (m : ℕ) := by dsimp [n₀]; omega
  have hm₀ : 2 ≤ (m₀ : ℕ) := by have := n₀.pos; dsimp [n₀, m₀] at *; omega
  let b : Fin (m : ℕ) := j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ))
  let Ml := LocalizedMatrix.matrix s m m₀ n₀ hm₀ hnp hn₀ K (fun t => A (t.1 + b, t.2))
  let P := fun x (l i : Fin (n₀ : ℕ)) => M x (l.castLE hnp + b) (i.castLE hnp + b)
  let Rem := LocalizedMatrix.remainder s m m₀ n₀ hm₀ hnp hn₀ K
    (fun t => A (t.1 + b, t.2)) P
  let ε₀ := ε * Real.log n / Real.log n₀
  let Rr : ℝ := Riesz1.cyclicIndexDistance m j i₀
  have hDlsep : (n : ℝ) ^ (Dl * ε) ≤ Rr :=
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ (n : ℕ) by omega))
      (mul_le_mul_of_nonneg_right (le_max_left Dl _) hε.le)).trans hsep
  have hMl : PeriodizedMatrixBounds (ν := ρ) s n₀ m₀ hm₀ K Cl κl γl ε₀ Ml :=
    hlocal j i₀ hR hDlsep
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ (n : ℕ) by omega)
  have hn0 : (0 : ℝ) < n := by positivity
  have ht : 1 ≤ (n : ℝ) ^ ((M₀ : ℕ) * ε) := Real.one_le_rpow hn1 (by positivity)
  have hcutsep : ((n : ℝ) ^ ((M₀ : ℕ) * ε)) ^ (8 : ℕ) ≤ Rr := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    exact (Real.rpow_le_rpow_of_exponent_le hn1 (by
      change ((M₀ : ℕ) : ℝ) * ε * 8 ≤ max Dl (8 * (M₀ : ℕ)) * ε
      have hh := mul_le_mul_of_nonneg_right (le_max_right Dl (8 * (M₀ : ℕ))) hε.le
      nlinarith only [hh])).trans hsep
  have hceil := (LocalizedMatrix.window_cutoff_admissible s m j i₀ hR ht hcutsep).2
  have hKceil : K ≤ ⌈(n : ℝ) ^ ((M₀ : ℕ) * ε)⌉₊ := by
    have hh : (K : ℝ) ≤ (n : ℝ) ^ ((M₀ : ℕ) * ε) := by
      calc
        _ = (⌊(n : ℝ) ^ ε⌋₊ : ℝ) ^ (M₀ : ℕ) := by simp only [K, Nat.cast_pow]
        _ ≤ ((n : ℝ) ^ ε) ^ (M₀ : ℕ) :=
          pow_le_pow_left₀ (by positivity) (Nat.floor_le (by positivity)) _
        _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; congr 1; ring
    exact_mod_cast hh.trans (Nat.le_ceil _)
  have hKml : 4 * K ≤ (m₀ : ℕ) := by dsimp only [m₀]; omega
  obtain ⟨_, hεmin, hpow, hcut⟩ := LocalizedMatrix.Analytic.window_loss_parameters s n m hn hmn j i₀ hR ε hε
  have hs : ∀ f : Fin (m₀ : ℕ) → Lp ℝ 2 ρ, ∃! z : Fin (m₀ : ℕ) → Q.1,
      WeightedWeakSolution Q (fun x => β • Ml x) ⊤ f z ∧
      ∀ k, (‖(z k).val‖ ≤ (Cu * (n : ℝ) ^ (κu * ε)) *
          ∑ l, weightRadius m₀ k l ^ (-(3 / 2 - s.val)) * ‖f l‖) ∧
        (Real.sqrt (Q.2 (z k) (z k)) ≤ (Cu * (n : ℝ) ^ (κu * ε)) *
          ∑ l, weightRadius m₀ k l ^ (-(1 - s.val / 2)) * ‖f l‖) := by
    intro f
    have hh := hsolve ε₀ ((div_le_div_of_nonneg_right hεge (by positivity)).trans hεmin) ρ Q hQ hQc n₀ m₀ hm₀ (by dsimp [n₀]; omega) hn₀
      (LocalizedMatrix.Analytic.windowPeriod_analytic_upper s m j i₀)
    rw [hcut (M₀ : ℕ)] at hh
    have hePow : (n₀ : ℝ) ^ (κu * ε₀) = (n : ℝ) ^ (κu * ε) := hpow κu
    simpa only [hePow] using hh hK hKml Ml hMl β hβl hβu f
  have hunique (f : Fin (m₀ : ℕ) → Lp ℝ 2 ρ) (z y : Fin (m₀ : ℕ) → Q.1)
      (hz : WeightedWeakSolution Q (fun x => β • Ml x) ⊤ f z)
      (hy : WeightedWeakSolution Q (fun x => β • Ml x) ⊤ f y) : z = y :=
    (AbstractEquation.existence_energy Q hQ β (hβlo.trans_le hβl) Ml hMl.1 _
      (SchurRestriction.periodized_mass_pos hCl)
      (hMl.2.1.mono (fun _ hx => ⟨hx.1, hx.2.2.1⟩)) ⊤ f).1.unique hz hy
  have hRm (l i : Fin (n₀ : ℕ)) : Measurable (fun x => Rem x l i) := by
    have he : (fun x => Rem x l i) =
        fun x => P x l i - Ml x (l.castLE hn₀) (i.castLE hn₀) := by
      funext x
      have hh := LocalizedMatrix.matrix_add_remainder s m m₀ n₀ hm₀ hnp hn₀ K
        (fun t => A (t.1 + b, t.2)) P x l i
      linarith only [hh]
    rw [he]
    exact (hM.1 _ _).sub (hMl.1 _ _)
  let E := 4 * Real.sqrt (2 + 1 / (1 + s.val)) * (Cstar * (n : ℝ) ^ (κstar * ε)) + Cp
  have hE : 0 < E := by dsimp [E]; positivity
  have hrows : ∀ᵐ x ∂ρ, ∀ l : Fin (n₀ : ℕ), Real.sqrt (∑ i, Rem x l i ^ 2) ≤
      E * ((min (l.val + 1) ((n₀ : ℕ) - l.val) : ℕ) : ℝ) ^ (-(1 + s.val) / 2) := by
    exact hrow ρ n m hm K Cstar κstar γstar ε hCstar M hM A
      (hArep.mono (fun _ hx => hx.2)) j i₀ hR
  let q := Riesz1.cyclicIndexDistance m j i₀ / 8
  have hcard : (n₀ : ℕ) = 2 * q + 1 := LocalizedMatrix.window_card m j i₀
  let c : Fin (n₀ : ℕ) := ⟨q, by omega⟩
  let v := fun i : Fin (n₀ : ℕ) => (u (LocalizedMatrix.windowEmbedding m j i₀ i)).val
  obtain ⟨g, hg, _, z, ⟨hz, hzb⟩, _⟩ := boundary_source_solution_sharp_internal s n₀ m₀
    (by dsimp [n₀, m₀]; omega) q hcard c rfl Q Ml
    (Cu * (n : ℝ) ^ (κu * ε)) β E Cs (by positivity) (hβlo.trans_le hβl).le hE.le
    hs hunique Rem hRm hrows (hconv n₀ m₀ (by dsimp [n₀, m₀]; omega) q hcard c rfl) v
  have hV : Rr ^ (3 / 2 - s.val) * Real.sqrt (∑ i, ‖v i‖ ^ 2) ≤
      Cg * (n : ℝ) ^ (κg * ε) * ‖χ‖ := by
    simpa only [← window_tuple_norm m j i₀ (fun i => (u i).val)] using
      hglobal ε hεge ρ Q hQ hQc n m hm hn hnm hmn hK hKm M hM β hβl hβu χ i₀ j u hu (by omega)
  have hloss : 1 ≤ (n : ℝ) ^ (κstar * ε) := Real.one_le_rpow hn1 (by positivity)
  have hEB : E ≤ B * (n : ℝ) ^ (κstar * ε) := by
    dsimp only [E, B]
    nlinarith only [mul_le_mul_of_nonneg_left hloss hCp.le]
  have hβ0 : 0 ≤ β := (hβlo.trans_le hβl).le
  let A₀ := Cu * βhi * B * (n : ℝ) ^ ((κu + κstar) * ε)
  have hfac : Cu * (n : ℝ) ^ (κu * ε) * β * E ≤ A₀ := by
    have hh := mul_le_mul hβu hEB hE.le hβhi0.le
    have hh' := mul_le_mul_of_nonneg_left hh
      (show 0 ≤ Cu * (n : ℝ) ^ (κu * ε) by positivity)
    have hl : (n : ℝ) ^ ((κu + κstar) * ε) =
        (n : ℝ) ^ (κu * ε) * (n : ℝ) ^ (κstar * ε) := by
      rw [add_mul, Real.rpow_add hn0]
    dsimp only [A₀]
    rw [hl]
    convert hh' using 1 <;> ring
  have hlog : 0 ≤ Real.log (2 * (n₀ : ℝ)) := Real.log_nonneg (by
    have hn01 : (1 : ℝ) ≤ n₀ := by exact_mod_cast n₀.pos
    linarith)
  have hzv : ‖(z (c.castLE hn₀)).val‖ ≤
      A₀ * Real.sqrt (∑ i, ‖v i‖ ^ 2) * Cs * Real.log (2 * (n₀ : ℝ)) *
        ((n₀ : ℝ) ^ (-(1 + s.val) / 2) + (n₀ : ℝ) ^ (s.val / 2 - 1)) := by
    apply hzb.1.trans
    convert mul_le_mul_of_nonneg_right hfac
      (show 0 ≤ Real.sqrt (∑ i, ‖v i‖ ^ 2) * Cs * Real.log (2 * (n₀ : ℝ)) *
        ((n₀ : ℝ) ^ (-(1 + s.val) / 2) + (n₀ : ℝ) ^ (s.val / 2 - 1)) by positivity) using 1 <;> ring
  have hzg : Real.sqrt (Q.2 (z (c.castLE hn₀)) (z (c.castLE hn₀))) ≤
      A₀ * Real.sqrt (∑ i, ‖v i‖ ^ 2) * H * (n₀ : ℝ) ^ (-(1 / 2 : ℝ)) := by
    apply hzb.2.trans
    convert mul_le_mul_of_nonneg_right hfac
      (show 0 ≤ Real.sqrt (∑ i, ‖v i‖ ^ 2) * H * (n₀ : ℝ) ^ (-(1 / 2 : ℝ)) by positivity) using 1 <;> ring
  have hfinal := hscale Rr n₀ A₀ (Cg * (n : ℝ) ^ (κg * ε)) ‖χ‖
    (Real.sqrt (∑ i, ‖v i‖ ^ 2)) ‖(z (c.castLE hn₀)).val‖
    (Real.sqrt (Q.2 (z (c.castLE hn₀)) (z (c.castLE hn₀)))) Cs H
    (by dsimp [Rr]; exact_mod_cast (show 1 ≤ Riesz1.cyclicIndexDistance m j i₀ by omega))
    (by exact_mod_cast n₀.pos) hsize.2.1 (by dsimp [Rr]; linarith only [hsize.2.2.1])
    (by dsimp [A₀]; positivity) (by positivity) (norm_nonneg _) (Real.sqrt_nonneg _) hCs.le hH.le
    hV hzv hzg
  refine ⟨g, hg, z, ⟨hz, ?_⟩, fun y hy => hunique _ y z hy.1 hz⟩
  have heq : (c.castLE hn₀).val = Riesz1.cyclicIndexDistance m j i₀ / 8 := rfl
  have heq' : c.castLE hn₀ = (⟨Riesz1.cyclicIndexDistance m j i₀ / 8, by
      have := (c.castLE hn₀).isLt
      simpa only [heq] using this⟩ : Fin (m₀ : ℕ)) := Fin.ext heq
  rw [heq'] at hfinal
  convert hfinal using 1
  dsimp only [A₀, Hs] at *
  rw [show (κu + κstar + κg) * ε = (κu + κstar) * ε + κg * ε by ring,
    Real.rpow_add hn0]
  ring

/-- See the proof of Proposition 5.15 in the paper (complete): projection, Schur
cancellation, exact restriction, unique embedded solutions and the weighted
boundary estimate, with a common prefactor for every ε ≥ εmin > 0.
-/
theorem loc_boundary (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ)
    (hκstar : 0 < κstar) (hγstar : 0 < γstar) (M₀ : ℕ+) :
    ∃ κ D : ℝ, 0 < κ ∧ 0 < D ∧
    ∀ εmin : ℝ, 0 < εmin → ∀ Cstar : ℝ, 1 ≤ Cstar →
    ∀ βlo : ℝ, 0 < βlo → ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, εmin ≤ ε →
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
  intro εmin hεmin Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Cl, hCl, hlocal⟩ := hlocal Cstar hCstar
  obtain ⟨C, hC, hdecay⟩ := hdecay εmin hεmin Cstar hCstar βlo hβlo βhi hβhi
  refine ⟨C, hC, ?_⟩
  intro ε hεge X _ ρ _ Q hQ hQc n m hm hn hnm hmn K hK hKm M hM
  have hε : 0 < ε := hεmin.trans_le hεge
  obtain ⟨A, hAm, hArep, hdecay⟩ := hdecay ε hεge ρ Q hQ hQc n m hm hn hnm hmn hK hKm M hM
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

/-- See the proof of Proposition 5.15 in the paper: the centered exterior rows and
neighbouring increments, uniformly for every ε ≥ εmin > 0. -/
theorem constrained_exterior_bounds (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ)
    (hκstar : 0 < κstar) (hγstar : 0 < γstar) (M₀ : ℕ+) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ εmin : ℝ, 0 < εmin →
    ∀ Cstar : ℝ, 1 ≤ Cstar →
    ∀ βlo : ℝ, 0 < βlo → ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, εmin ≤ ε →
    ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
      (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
    ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ)),
    2 ≤ (n : ℕ) → (n : ℕ) ≤ (m : ℕ) →
    (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
    let K := ⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ)
    1 ≤ K → 4 * K ≤ (m : ℕ) →
    ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M →
    ∀ β : ℝ, βlo ≤ β → β ≤ βhi →
    ∀ (χ : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _)
      (fun i => if i = i₀ then χ else 0) u →
    ∀ j : Fin (m : ℕ), 16 ≤ Riesz1.cyclicIndexDistance m j i₀ →
    ∃ U : Fin (LocalizedMatrix.windowSize m j i₀ : ℕ) → Lp ℝ 2 ν,
      (∀ l, ∀ᵐ x ∂ν, U l x = ∑ i ∈ (LocalizedMatrix.window m j i₀)ᶜ,
        M x (LocalizedMatrix.windowEmbedding m j i₀ l) i * (u i).val x) ∧
      ∀ l : Fin (LocalizedMatrix.windowSize m j i₀ : ℕ),
        let R := (Riesz1.cyclicIndexDistance m j i₀ : ℝ)
        let δ := min (l.val + 1) ((LocalizedMatrix.windowSize m j i₀ : ℕ) - l.val)
        ‖U l‖ ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ *
          (R ^ (-1 : ℝ) + R ^ (-(3 / 2 - s.val)) *
            Real.sqrt (∑ k ∈ Icc δ (4 * Riesz1.cyclicIndexDistance m j i₀), (k : ℝ) ^ (-2 * s.val))) ∧
        ∀ hl : 0 < l.val,
          let prev : Fin (LocalizedMatrix.windowSize m j i₀ : ℕ) := ⟨l.val - 1, by have := l.isLt; omega⟩
          let δpair := min δ (min (prev.val + 1) ((LocalizedMatrix.windowSize m j i₀ : ℕ) - prev.val))
          ‖U l - U prev‖ ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ *
            (R ^ (-2 : ℝ) + R ^ (-(3 / 2 - s.val)) * (δpair : ℝ) ^ (-(1 / 2 + s.val))) := by
  obtain ⟨κg, hκg, hg⟩ := LocalizedMatrix.Analytic.global_decay_bounds hzeta s κstar γstar hκstar hγstar M₀
  obtain ⟨P₀, P₁, hP₀, hP₁, hp⟩ := exterior_window_rows s
  refine ⟨κg + κstar, by positivity, fun εmin hεmin Cstar hCstar βlo hβlo βhi hβhi => ?_⟩
  obtain ⟨Cg, hCg, hg⟩ := hg εmin hεmin Cstar hCstar βlo hβlo βhi hβhi
  refine ⟨(P₀ + P₁) * Cstar * Cg, by positivity, ?_⟩
  intro ε hεge Ω _ ν _ Q hQ hQc n m hm hn hnm hmn K hK hKm M hM β hβloβ hββhi χ i₀ u hu j hR
  obtain ⟨lam, _, _, henergy, _, _⟩ := hg ε hεge ν Q hQ hQc n m hm hn hnm hmn hK hKm M hM β hβloβ hββhi χ i₀ u hu
  let E := Real.sqrt (∑ i, (weightRadius m i i₀ ^ (3 / 2 - s.val) * ‖(u i).val‖) ^ 2)
  have hE : E ≤ Cg * (n : ℝ) ^ (κg * ε) * ‖χ‖ :=
    (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans henergy
  obtain ⟨U, hU, hbound⟩ := hp ν n m hm K Cstar κstar γstar ε β (by linarith) Q M hM
    (fun i => if i = i₀ then χ else 0) u hu j i₀ hR
  refine ⟨fun l => U (LocalizedMatrix.windowEmbedding m j i₀ l), fun l => hU _, ?_⟩
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast n.pos
  have hmult (P profile : ℝ) (hP : 0 ≤ P) (hPsum : P ≤ P₀ + P₁) (hprofile : 0 ≤ profile) :
      P * (Cstar * (n : ℝ) ^ (κstar * ε)) * E * profile ≤
        ((P₀ + P₁) * Cstar * Cg) * (n : ℝ) ^ ((κg + κstar) * ε) * ‖χ‖ * profile := by
    calc
      _ ≤ P * (Cstar * (n : ℝ) ^ (κstar * ε)) *
          (Cg * (n : ℝ) ^ (κg * ε) * ‖χ‖) * profile := by gcongr
      _ = P * Cstar * Cg * (n : ℝ) ^ ((κg + κstar) * ε) * ‖χ‖ * profile := by
        rw [show (κg + κstar) * ε = κstar * ε + κg * ε by ring, Real.rpow_add hnreal]
        ring
      _ ≤ _ := by gcongr
  intro l R δ
  have hb := hbound l
  have hRp : 0 < R := by dsimp only [R]; exact_mod_cast (show 0 < Riesz1.cyclicIndexDistance m j i₀ by omega)
  constructor
  · apply hb.1.trans
    exact hmult P₀ _ hP₀.le (by linarith) (by positivity)
  · intro hl prev δpair
    have hprev := windowEmbedding_predecessor m j i₀ l hl
    change LocalizedMatrix.windowEmbedding m j i₀ prev = LocalizedMatrix.windowEmbedding m j i₀ l - 1 at hprev
    change ‖U (LocalizedMatrix.windowEmbedding m j i₀ l) - U (LocalizedMatrix.windowEmbedding m j i₀ prev)‖ ≤ _
    rw [hprev]
    apply hb.2.trans
    have hδpair : 1 ≤ δpair := by dsimp only [δpair, δ, prev]; have := l.isLt; omega
    have hδ : 1 ≤ δ := by dsimp only [δ]; have := l.isLt; omega
    have hδle : (δpair : ℝ) ≤ δ := by exact_mod_cast (min_le_left δ _)
    have hδp : (0 : ℝ) < δpair := by exact_mod_cast (show 0 < δpair by omega)
    have hpower := Real.rpow_le_rpow_of_nonpos hδp hδle
      (show -(1 / 2 + s.val) ≤ 0 by linarith [s.property.1])
    have hh := hmult P₁
      (R ^ (-2 : ℝ) + R ^ (-(3 / 2 - s.val)) * (δ : ℝ) ^ (-(1 / 2 + s.val)))
      hP₁.le (by linarith) (by positivity)
    apply hh.trans
    have hprofile : R ^ (-2 : ℝ) + R ^ (-(3 / 2 - s.val)) * (δ : ℝ) ^ (-(1 / 2 + s.val)) ≤
        R ^ (-2 : ℝ) + R ^ (-(3 / 2 - s.val)) * (δpair : ℝ) ^ (-(1 / 2 + s.val)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hpower
        (show 0 ≤ R ^ (-(3 / 2 - s.val)) by positivity))
    exact mul_le_mul_of_nonneg_left hprofile (by positivity)

/-- See the proof of Proposition 5.15 and equation (5.65) of the paper and
equation (5.66): sharp exterior profiles with uniform prefactors,
including the borderline exponent s = 1/2. -/
theorem constrained_exterior_sharp_bounds (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ)
    (hκstar : 0 < κstar) (hγstar : 0 < γstar) (M₀ : ℕ+) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ εmin : ℝ, 0 < εmin →
    ∀ Cstar : ℝ, 1 ≤ Cstar →
    ∀ βlo : ℝ, 0 < βlo → ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, εmin ≤ ε →
    ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
      (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
    ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ)),
    2 ≤ (n : ℕ) → (n : ℕ) ≤ (m : ℕ) →
    (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
    let K := ⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ)
    1 ≤ K → 4 * K ≤ (m : ℕ) →
    ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M →
    ∀ β : ℝ, βlo ≤ β → β ≤ βhi →
    ∀ (χ : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _)
      (fun i => if i = i₀ then χ else 0) u →
    ∀ j : Fin (m : ℕ), 16 ≤ Riesz1.cyclicIndexDistance m j i₀ →
    ∃ U : Fin (LocalizedMatrix.windowSize m j i₀ : ℕ) → Lp ℝ 2 ν,
      (∀ l, ∀ᵐ x ∂ν, U l x = ∑ i ∈ (LocalizedMatrix.window m j i₀)ᶜ,
        M x (LocalizedMatrix.windowEmbedding m j i₀ l) i * (u i).val x) ∧
      ∀ l : Fin (LocalizedMatrix.windowSize m j i₀ : ℕ),
        let R := (Riesz1.cyclicIndexDistance m j i₀ : ℝ)
        let δ := min (l.val + 1) ((LocalizedMatrix.windowSize m j i₀ : ℕ) - l.val)
        ‖U l‖ ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ * R ^ (-1 + s.val / 2) * (δ : ℝ) ^ (-s.val / 2) ∧
        ∀ hl : 0 < l.val,
          let prev : Fin (LocalizedMatrix.windowSize m j i₀ : ℕ) := ⟨l.val - 1, by have := l.isLt; omega⟩
          let δpair := min δ (min (prev.val + 1) ((LocalizedMatrix.windowSize m j i₀ : ℕ) - prev.val))
          ‖U l - U prev‖ ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ *
            R ^ (-1 + s.val / 2) * (δpair : ℝ) ^ (-1 - s.val / 2) := by
  obtain ⟨κ, hκ, hbound⟩ := constrained_exterior_bounds hzeta s κstar γstar hκstar hγstar M₀
  obtain ⟨P, hP, hprofile⟩ := exterior_profiles_internal s
  refine ⟨κ, hκ, fun εmin hεmin Cstar hCstar βlo hβlo βhi hβhi => ?_⟩
  obtain ⟨C, hC, hbound⟩ := hbound εmin hεmin Cstar hCstar βlo hβlo βhi hβhi
  refine ⟨C * P, by positivity, ?_⟩
  intro ε hεge Ω _ ν _ Q hQ hQc n m hm hn hnm hmn K hK hKm M hM β hβloβ hββhi χ i₀ u hu j hR
  obtain ⟨U, hU, hb⟩ := hbound ε hεge ν Q hQ hQc n m hm hn hnm hmn hK hKm M hM β hβloβ hββhi χ i₀ u hu j hR
  have hn₀ : (LocalizedMatrix.windowSize m j i₀ : ℕ) ≤ Riesz1.cyclicIndexDistance m j i₀ := by
    have hc := LocalizedMatrix.window_card m j i₀
    change (LocalizedMatrix.windowSize m j i₀ : ℕ) = _ at hc
    omega
  refine ⟨U, hU, ?_⟩
  intro l R δ
  have hδ : 1 ≤ δ := by dsimp only [δ]; have := l.isLt; omega
  have hδR : δ ≤ Riesz1.cyclicIndexDistance m j i₀ := by dsimp only [δ]; omega
  constructor
  · have hh := (hprofile _ δ hδ hδR).1
    have he := mul_le_mul_of_nonneg_left hh
      (show 0 ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ by positivity)
    exact (hb l).1.trans (by convert he using 1; ring)
  · intro hl prev δpair
    have hdp : 1 ≤ δpair := by dsimp only [δpair, δ, prev]; have := l.isLt; omega
    have hdR : δpair ≤ Riesz1.cyclicIndexDistance m j i₀ := by dsimp only [δpair]; omega
    have hh := (hprofile _ δpair hdp hdR).2
    have he := mul_le_mul_of_nonneg_left hh
      (show 0 ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ by positivity)
    exact ((hb l).2 hl).trans (by convert he using 1; ring)

/-- See the proof of Proposition 5.15 in the paper (complete): the canonical multiplier,
actual exterior resolvent field, entry and increment estimates, extended
L¹ mass and every cyclic translation modulus. The prefactor is common to
all ε ≥ εmin > 0. -/
theorem loc_field (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ)
    (hκstar : 0 < κstar) (hγstar : 0 < γstar) (M₀ : ℕ+) :
    ∃ κ D : ℝ, 0 < κ ∧ 0 < D ∧ ∀ εmin : ℝ, 0 < εmin →
    ∀ Cstar : ℝ, 1 ≤ Cstar →
    ∀ βlo : ℝ, 0 < βlo → ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, εmin ≤ ε →
    ∀ {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
      (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q), IsConservativeScalarForm Q →
    ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ)),
    2 ≤ (n : ℕ) → (n : ℕ) ≤ (m : ℕ) →
    (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
    let K := ⌊(n : ℝ) ^ ε⌋₊ ^ (M₀ : ℕ)
    1 ≤ K → 4 * K ≤ (m : ℕ) →
    ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M →
    ∀ β : ℝ, βlo ≤ β → β ≤ βhi →
    ∀ (χ : Lp ℝ 2 ν) (i₀ : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _)
      (fun i => if i = i₀ then χ else 0) u →
    ∀ (j : Fin (m : ℕ)) (hR : 16 ≤ Riesz1.cyclicIndexDistance m j i₀),
    (n : ℝ) ^ (D * ε) ≤ (Riesz1.cyclicIndexDistance m j i₀ : ℝ) →
    let n₀ := LocalizedMatrix.windowSize m j i₀
    let m₀ := LocalizedMatrix.windowPeriod s m j i₀
    let hn₀ : (n₀ : ℕ) ≤ (m₀ : ℕ) := by
      have := LocalizedMatrix.two_windowSize_lt_period s m j i₀ hR
      dsimp only [n₀, m₀]
      omega
    let hm₀ : 2 ≤ (m₀ : ℕ) := by
      have := n₀.pos
      have := LocalizedMatrix.two_windowSize_lt_period s m j i₀ hR
      dsimp only [n₀, m₀] at *
      omega
    let pv := (MatrixEnergy.vectorEquiv Q hQ).symm (fun i => u (LocalizedMatrix.windowEmbedding m j i₀ i))
    let J := SchurRestriction.assemble Q hQ n₀ m₀ hn₀
    let H := fun _ : Ω => (2 : ℝ) • referenceIntervalMatrix s m₀ hm₀ K
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
      (∀ l, ‖V l‖ ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ *
        (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (-1 + s.val / 2) *
        ((min (l.val + 1) ((n₀ : ℕ) - l.val) : ℕ) : ℝ) ^ (-s.val / 2)) ∧
      (∀ l : Fin (n₀ : ℕ), ∀ hl : 0 < l.val,
        let prev : Fin (n₀ : ℕ) := ⟨l.val - 1, by have := l.isLt; omega⟩
        ‖V l - V prev‖ ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ *
          (Riesz1.cyclicIndexDistance m j i₀ : ℝ) ^ (-1 + s.val / 2) *
          ((min (min (l.val + 1) ((n₀ : ℕ) - l.val))
            (min (prev.val + 1) ((n₀ : ℕ) - prev.val)) : ℕ) : ℝ) ^ (-1 - s.val / 2)) ∧
      (let f := (SchurRestriction.extendSource n₀ m₀ hn₀ (WithLp.toLp 2 V)).ofLp
       (∑ i, ‖f i‖) ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ ∧
       ∀ h, (∑ i, ‖f (i - h) - f i‖) ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ *
         min 1 (((Riesz1.cyclicIndexDistance m₀ h 0 : ℝ) /
           (Riesz1.cyclicIndexDistance m j i₀ : ℝ)) ^ (1 - s.val / 2))) := by
  obtain ⟨κu, hκu, hu⟩ := constrained_exterior_sharp_bounds hzeta s κstar γstar hκstar hγstar M₀
  obtain ⟨κg, hκg, hg⟩ := LocalizedMatrix.Analytic.global_decay_bounds hzeta s κstar γstar hκstar hγstar M₀
  obtain ⟨B, hB, hschur⟩ := normalized_schur_temperature_internal hzeta s
  let κ : ℝ := κu + κg + 2 * (M₀ : ℕ)
  let D : ℝ := 8 * ((M₀ : ℕ) + γstar + 1) + 8 * (M₀ : ℕ)
  let Cs : ℝ := Real.sqrt (2 / (1 - s.val)) * 2 ^ (3 / 2 - s.val)
  let Ct : ℝ := 8 / (1 - s.val / 2) + 4 + 2 / (s.val / 2)
  have hCs : 0 ≤ Cs := by dsimp only [Cs]; positivity
  have hhalf : 0 < 1 - s.val / 2 := by linarith [s.property.2]
  have hsmall : 0 < s.val / 2 := by linarith [s.property.1]
  have hCt : 1 ≤ Ct := by
    dsimp only [Ct]
    have h1 : 0 ≤ 8 / (1 - s.val / 2) := by positivity [s.property.2]
    have h2 : 0 ≤ 2 / (s.val / 2) := by positivity [s.property.1]
    linarith
  refine ⟨κ, D, by dsimp only [κ]; positivity, by dsimp only [D]; positivity, ?_⟩
  intro εmin hεmin Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Cu, hCu, hu⟩ := hu εmin hεmin Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Cg, hCg, hg⟩ := hg εmin hεmin Cstar hCstar βlo hβlo βhi hβhi
  have hβhi0 : 0 < βhi := hβlo.trans_le hβhi
  let C₀ := 1 + βhi * Cu + βhi * B * Cs * Cg + Cg
  have hC₀ : 0 < C₀ := by dsimp only [C₀]; positivity
  refine ⟨3 * Ct * C₀, by positivity, ?_⟩
  intro ε hεge Ω _ ν _ Q hQ hQc n m hm hn hnm hmn K hK hKm M hM β hβl hβu χ i₀ u husol j hR hsep
    n₀ m₀ hn₀ hm₀ pv J H
  have hε : 0 < ε := hεmin.trans_le hεge
  have hβ : 0 < β := hβlo.trans_le hβl
  let R : ℝ := Riesz1.cyclicIndexDistance m j i₀
  have hRp : 0 < R := by dsimp only [R]; exact_mod_cast (show 0 < Riesz1.cyclicIndexDistance m j i₀ by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ (n : ℕ) by omega)
  have hnp : (0 : ℝ) < n := by positivity
  have hcutsep : (n : ℝ) ^ ((8 * (M₀ : ℕ)) * ε) ≤ R :=
    (Real.rpow_le_rpow_of_exponent_le hn1
      (mul_le_mul_of_nonneg_right (by dsimp only [D]; linarith [show (0 : ℝ) ≤ (M₀ : ℕ) by positivity]) hε.le)).trans hsep
  obtain ⟨_, hKlocal⟩ := LocalizedMatrix.window_reference_cutoff_admissible s n m ε hε M₀ j i₀ hR hcutsep
  have hKml : K ≤ (m₀ : ℕ) / 4 := by change 4 * K ≤ (m₀ : ℕ) at hKlocal; omega
  obtain ⟨lam, hlam, _, henergy, hlamBound, _⟩ := hg ε hεge ν Q hQ hQc n m hm hn hnm hmn hK hKm M hM β hβl hβu χ i₀ u husol
  obtain ⟨U, hU, hUb⟩ := hu ε hεge ν Q hQ hQc n m hm hn hnm hmn hK hKm M hM β hβl hβu χ i₀ u husol j hR
  obtain ⟨w, hw, _⟩ := normalized_schur_exists_internal hzeta s β hβ n₀ m₀ hn₀ hm₀ K hK hKml ν Q hQ pv
  obtain ⟨hSp, hSi⟩ := hschur β hβ n₀ m₀ hn₀ hm₀ K hK hKml ν Q hQ pv w hw
  let S := ∑ i : Fin (n₀ : ℕ), ((min (i.val + 1) ((n₀ : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val / 2) *
    ‖(u (LocalizedMatrix.windowEmbedding m j i₀ i)).val‖
  let E := Real.sqrt (∑ i, (weightRadius m i i₀ ^ (3 / 2 - s.val) * ‖(u i).val‖) ^ 2)
  have hE : E ≤ Cg * (n : ℝ) ^ (κg * ε) * ‖χ‖ :=
    (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans henergy
  have hS : S ≤ Cs * R ^ (-1 + s.val / 2) * E :=
    window_schur_source_internal s m j i₀ hR (fun i => (u i).val)
  have hpv (i : Fin (n₀ : ℕ)) : (MatrixEnergy.vectorEquiv Q hQ pv i).val =
      (u (LocalizedMatrix.windowEmbedding m j i₀ i)).val := by
    exact congrArg (fun f : Fin (n₀ : ℕ) → Q.1 => (f i).val)
      ((MatrixEnergy.vectorEquiv Q hQ).apply_symm_apply _)
  simp_rw [hpv] at hSp hSi
  have hS0 : 0 ≤ S := by dsimp only [S]; positivity
  let A := C₀ * (n : ℝ) ^ (κ * ε) * ‖χ‖
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hcoeff (c k : ℝ) (hc : 0 ≤ c) (hcC : c ≤ C₀) (hk : k ≤ κ) :
      c * (n : ℝ) ^ (k * ε) * ‖χ‖ ≤ A :=
    mul_le_mul_of_nonneg_right
      (LocalizedMatrix.loss_mono_internal hn1 hε.le hc hcC hk) (norm_nonneg _)
  have hpu : β * (Cu * (n : ℝ) ^ (κu * ε) * ‖χ‖) ≤ A := by
    calc
      _ ≤ (βhi * Cu) * (n : ℝ) ^ (κu * ε) * ‖χ‖  := by
        calc
          _ ≤ βhi * (Cu * (n : ℝ) ^ (κu * ε) * ‖χ‖) :=
            mul_le_mul_of_nonneg_right hβu (by positivity)
          _ = _ := by ring
      _ ≤ _ := hcoeff _ _ (by positivity) (by dsimp only [C₀]; linarith [mul_nonneg (mul_nonneg (mul_nonneg hβhi0.le hB.le) hCs) hCg.le])
        (by dsimp only [κ]; linarith [show (0 : ℝ) ≤ 2 * (M₀ : ℕ) by positivity])
  have hpl : Cg * (n : ℝ) ^ (κg * ε) * ‖χ‖ ≤ A :=
    hcoeff _ _ hCg.le (by dsimp only [C₀]; linarith [mul_nonneg hβhi0.le hCu.le, mul_nonneg (mul_nonneg (mul_nonneg hβhi0.le hB.le) hCs) hCg.le])
      (by dsimp only [κ]; linarith [show (0 : ℝ) ≤ 2 * (M₀ : ℕ) by positivity])
  have hps : β * B * (K : ℝ) ^ 2 * S ≤ A * R ^ (-1 + s.val / 2) := by
    have hS' := hS.trans (mul_le_mul_of_nonneg_left hE (show 0 ≤ Cs * R ^ (-1 + s.val / 2) by positivity))
    have hks := BoundarySchurBounds.cutoff_sq_le (n : ℕ) (M₀ : ℕ) (by omega) ε
    calc
      _ ≤ βhi * B * (n : ℝ) ^ ((2 * (M₀ : ℕ) : ℝ) * ε) *
          (Cs * R ^ (-1 + s.val / 2) * (Cg * (n : ℝ) ^ (κg * ε) * ‖χ‖)) := by
            gcongr
      _ = (βhi * B * Cs * Cg) * (n : ℝ) ^ ((κg + 2 * (M₀ : ℕ)) * ε) * ‖χ‖ * R ^ (-1 + s.val / 2) := by
        rw [show (κg + 2 * (M₀ : ℕ)) * ε = (2 * (M₀ : ℕ)) * ε + κg * ε by ring, Real.rpow_add hnp]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (hcoeff _ _ (by positivity) (by dsimp only [C₀]; linarith [mul_nonneg hβhi0.le hCu.le])
          (by dsimp only [κ]; linarith)) (by positivity)
  let W := fun l : Fin (n₀ : ℕ) => β • LocalizedFieldPart3.referenceRow Q hQ s n₀ m₀ hm₀ K
    (LocalizedFieldPart3.exteriorReindex Q hQ n₀ m₀ hn₀ w) (l.castLE hn₀)
  let V := fun l => (-β) • U l - W l + lam
  have hwsize := LocalizedMatrix.window_size_bounds m j i₀ hR
  have hnR : (n₀ : ℝ) ≤ R := by
    have hnr := hwsize.2.2.1
    change (n₀ : ℝ) ≤ R / 2 at hnr
    linarith
  have hRml : R ≤ (m : ℝ) := by
    have hd : Riesz1.cyclicIndexDistance m j i₀ ≤ (m : ℕ) := by
      simp only [Riesz1.cyclicIndexDistance]
      omega
    dsimp only [R]
    exact_mod_cast hd
  have hlambda (δ : ℕ) (hd : 1 ≤ δ) (hdR : (δ : ℝ) ≤ R) :
      ‖lam‖ ≤ A * R ^ (-1 + s.val / 2) * (δ : ℝ) ^ (-s.val / 2) := by
    have hdp : (0 : ℝ) < δ := by exact_mod_cast (show 0 < δ by omega)
    have hbase := transfer_radius_power_internal hdp hdR (-1) 0 (s.val / 2) (by positivity [s.property.1])
    simp only [Real.rpow_zero, mul_one, zero_sub] at hbase
    rw [show -(s.val / 2) = -s.val / 2 by ring] at hbase
    have hinv : (m : ℝ)⁻¹ ≤ R ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]; exact inv_anti₀ hRp hRml
    calc
      _ ≤ (Cg * (n : ℝ) ^ (κg * ε) * ‖χ‖) * (m : ℝ)⁻¹ := by convert hlamBound using 1; ring
      _ ≤ A * (R ^ (-1 + s.val / 2) * (δ : ℝ) ^ (-s.val / 2)) :=
        mul_le_mul hpl (hinv.trans hbase) (by positivity) hA
      _ = _ := by ring
  have hW (l : Fin (n₀ : ℕ)) : ‖W l‖ ≤ (β * B * (K : ℝ) ^ 2 * S) *
      ((min (l.val + 1) ((n₀ : ℕ) - l.val) : ℕ) : ℝ) ^ (-s.val / 2) := by
    convert hSp l using 1
    ring
  have hWi (l k : Fin (n₀ : ℕ)) : ‖W l - W k‖ ≤ (β * B * (K : ℝ) ^ 2 * S) *
      (Nat.dist l.val k.val : ℝ) *
      ((min (min (l.val + 1) ((n₀ : ℕ) - l.val))
        (min (k.val + 1) ((n₀ : ℕ) - k.val)) : ℕ) : ℝ) ^ (-1 - s.val / 2) := by
    convert hSi l k using 1
    ring
  obtain ⟨hentry, hincrement, hmod⟩ := field_profile_assembly_internal s n₀ m₀ hn₀ R A
    (Cu * (n : ℝ) ^ (κu * ε) * ‖χ‖) (β * B * (K : ℝ) ^ 2 * S) β
    hRp hnR hA hβ hpu hps U W lam hUb hW hWi hlambda
  have hbig : 3 * A ≤ (3 * Ct * C₀) * (n : ℝ) ^ (κ * ε) * ‖χ‖ := by
    have hh := mul_le_mul_of_nonneg_right hCt (show 0 ≤ 3 * A by positivity)
    convert hh using 1 <;> dsimp only [A] <;> ring
  refine ⟨lam, hlam, U, hU, w, hw, V, fun _ => rfl, ?_, ?_, ?_⟩
  · intro l
    exact (hentry l).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbig (by positivity)) (by positivity))
  · intro l hl
    exact (hincrement l hl).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbig (by positivity)) (by positivity))
  · constructor
    · convert hmod.1 using 1; dsimp only [Ct, A, R]; ring
    · intro h
      convert hmod.2 h using 1; dsimp only [Ct, A, R]; ring

end Riesz2.OptimalLocalizationPart3
