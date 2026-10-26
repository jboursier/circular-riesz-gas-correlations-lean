/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.PaperGoodEventPart2

/-!
# Boundary-entry moments for the short-range good event

Step 2 of Lemma 4.8 sums the prefix, suffix and full-block
coefficient moments, retaining the two endpoint tails.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal ContDiff Topology

namespace Riesz2.DecayShort

/-- Internal finite-sum norm estimate in Step 2 of Lemma 4.8. -/
theorem internal_paper_weighted_sum_norm {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (f : ℕ → Ω → ℝ)
    (w B : ℕ → ℝ) (hB : ∀ k ∈ Finset.Ico 1 n, 0 ≤ B k)
    (hw : ∀ k, 0 ≤ w k)
    (hb : ∀ k ∈ Finset.Ico 1 n, eLpNorm (f k) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (B k)) :
    eLpNorm (fun x => ∑ k ∈ Finset.Ico 1 n, f k x*w k) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (∑ k ∈ Finset.Ico 1 n, B k*w k) := by
  have hqE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by simpa using ENNReal.ofReal_le_ofReal hq
  calc
    _ ≤ ∑ k ∈ Finset.Ico 1 n, eLpNorm (fun x => f k x*w k) (ENNReal.ofReal q) μ := by
      simpa only [Finset.sum_fn] using eLpNorm_sum_le (μ := μ) (s := Finset.Ico 1 n) hqE
        (f := fun k x => f k x*w k)
    _ ≤ ∑ k ∈ Finset.Ico 1 n, ENNReal.ofReal (B k*w k) := by
      apply Finset.sum_le_sum
      intro k hk
      have he : (fun x => f k x*w k) = w k • f k := by funext x; simp only [Pi.smul_apply,smul_eq_mul]; ring
      rw [he,eLpNorm_const_smul,Real.enorm_eq_ofReal_abs,abs_of_nonneg (hw k)]
      apply (mul_le_mul' le_rfl (hb k hk)).trans_eq
      rw [← ENNReal.ofReal_mul (hw k)]
      congr 1
      ring
    _ = _ := (ENNReal.ofReal_sum_of_nonneg (fun k hk => mul_nonneg (hB k hk) (hw k))).symm

set_option backward.isDefEq.respectTransparency false in
/-- The boundary-entry moment display in Step 2 of Lemma 4.8.
It is the profile used in equation (4.10), with constants
common on each compact positive temperature interval and for either tilt. -/
theorem paper_boundary_entry_moments (s : ℝ) (hs : 1 < s) :
    ∃ d : ℝ, 0 < d ∧ ∀ (θ : PhysicalCutoff) (βlo βhi h : ℝ),
      0 < βlo → βlo ≤ βhi → 0 < h →
      ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (n : ℕ+) (m : ℕ)
      (hn : (n : ℕ) ≤ (((n : ℕ)+m).succPNat : ℕ)),
      2*(n : ℕ) ≤ (n : ℕ)+m+1 → ∀ (b : Bool) (q : ℝ), 1 ≤ q →
      ∀ i j : Fin (n : ℕ),
      let μ := (activeTiltedGapLaw p ((n : ℕ)+m).succPNat n hn θ h b).comap
        ((↑) : AffineSimplex.chartDomain n ((n+m : ℕ)+1) → EuclideanSpace ℝ (Fin (n : ℕ)))
      let B := fun x => IntervalBoundary.boundaryMatrix ((n : ℕ)+m).succPNat n hn
        (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x) i j
      MemLp B (ENNReal.ofReal q) μ ∧ eLpNorm B (ENNReal.ofReal q) μ ≤
        ENNReal.ofReal (C*q^d*paperBoundaryProfile s i j) := by
  obtain ⟨d,hd,hm⟩ := interval_counting_coefficient_moments s hs
  refine ⟨d,hd,fun θ βlo βhi h hlo hle hh => ?_⟩
  obtain ⟨C₀,hC₀,hm⟩ := hm θ βlo βhi h hlo hle hh
  refine ⟨(2+1/s)*C₀,mul_pos (by positivity) hC₀,?_⟩
  intro p hp hpl hph n m hn hhalf b q hq i j μ B
  subst s
  let N := ((n : ℕ)+m).succPNat
  let A := fun x => conditionalIntervalWeight p n m n.pos (Equiv.refl _) x
  let P := fun k x => IntervalBoundary.prefixCoefficient N n hn (A x) k
  let Q := fun k x => IntervalBoundary.suffixCoefficient N n hn (A x) k
  let a := fun x => IntervalBoundary.fullCoefficient N n hn (A x)
  let u : ℕ → ℝ := fun k => IntervalBoundary.rankOne (IntervalBoundary.initialSegment n k) i j
  let v : ℕ → ℝ := fun k => IntervalBoundary.rankOne (IntervalBoundary.terminalSegment n k) i j
  let D := C₀*q^d
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hqE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by simpa using ENNReal.ofReal_le_ofReal hq
  obtain ⟨_,hPQ,ha,_⟩ := ((hm p rfl hpl hph).1 n m hn hhalf b).2.2 q hq
  have hP := internal_paper_weighted_sum_norm μ q hq n P u
    (fun k => D*(k : ℝ)^(-p.val.2-1)) (fun _ _ => by positivity)
    (fun _ => IntervalBoundary.rankOne_nonneg _ _ _)
    (fun k hk => (hPQ k (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2).2.1)
  have hQ := internal_paper_weighted_sum_norm μ q hq n Q v
    (fun k => D*(((n : ℕ)-k : ℕ) : ℝ)^(-p.val.2-1)) (fun _ _ => by positivity)
    (fun _ => IntervalBoundary.rankOne_nonneg _ _ _)
    (fun k hk => (hPQ k (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2).2.2.2)
  have he : B = fun x => (∑ k ∈ Finset.Ico 1 (n : ℕ), P k x*u k)+
      (∑ k ∈ Finset.Ico 1 (n : ℕ), Q k x*v k)+a x := by
    funext x
    exact IntervalBoundary.boundary_representation N n.pos
      (by simpa only [N,Nat.succPNat_coe] using hhalf) (A x) i j
  have hnorm : eLpNorm B (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (((2+1/p.val.2)*C₀)*q^d*paperBoundaryProfile p.val.2 i j) := by
    rw [he]
    apply (eLpNorm_add_le hqE).trans
    apply (add_le_add ((eLpNorm_add_le hqE).trans (add_le_add hP hQ)) ha.2).trans
    have hUsum : 0 ≤ ∑ k ∈ Finset.Ico 1 (n : ℕ), D*(k : ℝ)^(-p.val.2-1)*u k :=
      Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (IntervalBoundary.rankOne_nonneg _ _ _)
    have hVsum : 0 ≤ ∑ k ∈ Finset.Ico 1 (n : ℕ), D*(((n : ℕ)-k : ℕ) : ℝ)^(-p.val.2-1)*v k :=
      Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (IntervalBoundary.rankOne_nonneg _ _ _)
    rw [← ENNReal.ofReal_add hUsum hVsum,
      ← ENNReal.ofReal_add (add_nonneg hUsum hVsum) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have ht := internal_paper_boundary_sums p.val.2 (by linarith) n D hD
      (fun k => D*(k : ℝ)^(-p.val.2-1))
      (fun k => D*(((n : ℕ)-k : ℕ) : ℝ)^(-p.val.2-1)) (D*(n : ℝ)^(-p.val.2))
      (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl) le_rfl i j
    exact ht.trans_eq (by dsimp only [D]; ring)
  have hmB : Measurable B := by
    unfold B IntervalBoundary.boundaryMatrix
    apply Finset.measurable_sum
    intro t _
    split_ifs
    · exact measurable_const
    · exact (measurable_conditionalIntervalWeight p n m n.pos (Equiv.refl _) t).mul_const _
  exact ⟨internal_memLp_of_bound μ hmB hnorm,hnorm⟩

end Riesz2.DecayShort
