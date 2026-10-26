/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.LocalizedBoundarySharpValues

/-!
# Sharp boundary remainder decay

The boundary part of Proposition 5.15, Step 1, uses separate
value and gradient convolutions before equation (5.64).
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Classical Fin.NatCast
namespace Riesz2.LocalizedBoundary
open LocalizedMatrix IntervalBoundary

/-- See the proof of Proposition 5.15 in the paper, equation (5.64):
the actual localized remainder source has a unique unrestricted solution
with both displayed decay powers. The matrix, reference cutoff and scalar
form are those of Subsection 5.5. -/
theorem boundary_remainder_decay (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κstar γstar : ℝ)
    (hκstar : 0 < κstar) (hγstar : 0 < γstar) (M₀ : ℕ+) :
    ∃ κ D : ℝ, 0 < κ ∧ 0 < D ∧
    ∀ ε : ℝ, 0 < ε → ∀ Cstar : ℝ, 1 ≤ Cstar →
    ∀ βlo : ℝ, 0 < βlo → ∀ βhi : ℝ, βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧
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
  intro ε hε Cstar hCstar βlo hβlo βhi hβhi
  obtain ⟨Cl, hCl, hlocal⟩ := hlocal Cstar hCstar
  obtain ⟨Cu, hCu, hsolve⟩ := hsolve (ε / (3 / 2 + 1 / s.val)) (by positivity)
    Cl hCl βlo hβlo βhi hβhi
  obtain ⟨Cg, hCg, hglobal⟩ := hglobal ε hε Cstar hCstar βlo hβlo βhi hβhi
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
  intro X _ ρ _ Q hQ hQc n m hm hn hnm hmn K hK hKm M hM
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
    have hh := hsolve ε₀ hεmin ρ Q hQ hQc n₀ m₀ hm₀ (by dsimp [n₀]; omega) hn₀
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
      hglobal ρ Q hQ hQc n m hm hn hnm hmn hK hKm M hM β hβl hβu χ i₀ j u hu (by omega)
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


end Riesz2.LocalizedBoundary
