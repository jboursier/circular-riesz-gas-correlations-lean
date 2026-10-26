/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.IntrinsicScalarCore
public import Riesz2.ToMathlib.VectorRadialCompositionPart4
public import Riesz1.ToMathlib.WeightedSobolev.LipschitzH1Convolution

/-!
# Normal contractions for the concrete Neumann form

The complete closed Dirichlet-form certificate required by Proposition 3.3. All Sobolev carriers are the completions.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff BigOperators RealInnerProductSpace

namespace Riesz2.ClosedFormResolvent.Internal

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

set_option backward.isDefEq.respectTransparency false in
/-- Closed energy sublevels under strong convergence of values, used for normal
contractions in Proposition 3.3. This internal Hilbert-space
criterion uses the existing coercive inverse, without a Markov premise. -/
theorem exists_of_energy_bounded_approximation
    (B : V →L[ℝ] V →L[ℝ] ℝ) (J : V →L[ℝ] H)
    (hB : ∀ z, 0 ≤ B z z) (hs : ∀ z w, B z w = B w z)
    (hnorm : ∀ z, ‖z‖ ^ 2 = ‖J z‖ ^ 2 + B z z)
    (w : H) (z : ℕ → V) (C : ℝ)
    (hz : Tendsto (fun n => J (z n)) atTop (𝓝 w))
    (he : ∀ n, B (z n) (z n) ≤ C) :
    ∃ u : V, J u = w ∧ B u u ≤ C := by
  let b : H →L[ℝ] H →L[ℝ] ℝ := innerSL ℝ
  let A (n : ℕ) : V →L[ℝ] V →L[ℝ] ℝ :=
    B + ((n : ℝ) + 1) • b.bilinearComp J J
  have hA (n : ℕ) (v : V) : 1 * ‖v‖ ^ 2 ≤ A n v v := by
    change 1 * ‖v‖ ^ 2 ≤ B v v + ((n : ℝ) + 1) * inner ℝ (J v) (J v)
    rw [real_inner_self_eq_norm_sq, hnorm]
    nlinarith [sq_nonneg ‖J v‖, Nat.cast_nonneg (α := ℝ) n]
  let y (n : ℕ) : V :=
    CoerciveSolution.solution (A n) 1 zero_lt_one (hA n) J (((n : ℝ) + 1) • w)
  have hy (n : ℕ) (v : V) :
      B (y n) v + ((n : ℝ) + 1) * inner ℝ (J (y n) - w) (J v) = 0 := by
    have hh := CoerciveSolution.solution_solves (A n) 1 zero_lt_one (hA n) J
      (((n : ℝ) + 1) • w) v
    change B (y n) v + ((n : ℝ) + 1) * inner ℝ (J (y n)) (J v) =
      inner ℝ (((n : ℝ) + 1) • w) (J v) at hh
    rw [real_inner_smul_left] at hh
    rw [inner_sub_left]
    linarith
  have hm (n : ℕ) (v : V) :
      B (y n) (y n) + ((n : ℝ) + 1) * ‖J (y n) - w‖ ^ 2 ≤
        B v v + ((n : ℝ) + 1) * ‖J v - w‖ ^ 2 := by
    have hp := hB (v - y n)
    have heq := hy n (v - y n)
    have hn := sq_nonneg ‖J v - J (y n)‖
    have hdiff : J (v - y n) = (J v - w) - (J (y n) - w) := by
      rw [map_sub]; abel
    rw [hdiff, inner_sub_right] at heq
    simp only [map_sub] at heq
    simp only [map_sub, sub_apply, hs v (y n)] at hp
    have hident : ‖J v - J (y n)‖ ^ 2 =
        ‖J v - w‖ ^ 2 - 2 * inner ℝ (J (y n) - w) (J v - w) +
          ‖J (y n) - w‖ ^ 2 := by
      rw [show J v - J (y n) = (J v - w) - (J (y n) - w) by abel,
        norm_sub_sq_real, real_inner_comm]
    rw [hident] at hn
    rw [real_inner_self_eq_norm_sq] at heq
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hb (n : ℕ) : B (y n) (y n) + ((n : ℝ) + 1) * ‖J (y n) - w‖ ^ 2 ≤ C := by
    have ht : Tendsto (fun k => C + ((n : ℝ) + 1) * ‖J (z k) - w‖ ^ 2)
        atTop (𝓝 C) := by
      convert tendsto_const_nhds.add
        ((tendsto_const_nhds.mul ((hz.sub tendsto_const_nhds).norm.pow 2))) using 1
      simp
    exact ge_of_tendsto ht (Eventually.of_forall fun k =>
      (hm n (z k)).trans (add_le_add (he k) le_rfl))
  have henergy (n : ℕ) : B (y n) (y n) ≤ C :=
    (le_add_of_nonneg_right (mul_nonneg (by positivity) (sq_nonneg _))).trans (hb n)
  have herror (n : ℕ) : ((n : ℝ) + 1) * ‖J (y n) - w‖ ^ 2 ≤ C :=
    (le_add_of_nonneg_left (hB _)).trans (hb n)
  obtain ⟨u, hu, ht⟩ := exists_limit B J hB hs hnorm w y C hy henergy herror
  have htB : Tendsto (fun n => B (y n) (y n)) atTop (𝓝 (B u u)) :=
    ((B.continuous.clm_apply continuous_id).tendsto u).comp ht
  exact ⟨u, hu, le_of_tendsto htB (Eventually.of_forall henergy)⟩

end Riesz2.ClosedFormResolvent.Internal

namespace Riesz2.EuclideanScalarForm

open Riesz1.WeightedSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ρ : Measure E} [IsFiniteMeasure ρ] {U : Set E}

/-- Normal contractions on the original completed Neumann jets, for Proposition 3.3. No differentiability of the contraction is needed. -/
theorem normal_contraction (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hρ : ∀ᵐ x ∂ρ, x ∈ U)
    (T : ℝ → ℝ) (hT : LipschitzWith 1 T) (h0 : T 0 = 0)
    (f : ScalarForm.Domain (smoothJet hU hB hρ)) :
    ∃ g : ScalarForm.Domain (smoothJet hU hB hρ),
      (∀ᵐ x ∂ρ, ScalarForm.value _ g x = T (ScalarForm.value _ f x)) ∧
      ScalarForm.energy _ g g ≤ ScalarForm.energy _ f f := by
  let J := smoothJet hU hB hρ
  let F := ScalarForm.value J f
  let D := ScalarForm.deriv J f
  have hf : IsWeightedH1 ρ U F D := by
    apply (mem_completion_iff hU hB hρ F D (Lp.memLp F) (Lp.memLp D)).mp
    simp only [Lp.toLp_coeFn]
    exact f.property
  obtain ⟨φ, hφ, _, hdφ, hlφ, _⟩ := exists_smooth_approximation_lipschitz hT
  let S (n : ℕ) (r : ℝ) := φ n r - φ n 0
  have hS n : ContDiff ℝ ∞ (S n) := (hφ n).sub contDiff_const
  have hS0 n : S n 0 = 0 := sub_self _
  have hdS (n : ℕ) (r : ℝ) : ‖deriv (S n) r‖₊ ≤ 1 := by
    have he : deriv (S n) r = deriv (φ n) r := by
      exact ((hφ n).differentiable (by simp) r).hasDerivAt.sub_const _ |>.deriv
    rw [he]
    exact_mod_cast (by simpa only [gradient_eq_deriv', NNReal.coe_one] using hdφ n r : ‖deriv (φ n) r‖ ≤ (1 : ℝ))
  have hLip n : LipschitzWith 1 (S n) :=
    lipschitzWith_of_nnnorm_deriv_le ((hS n).differentiable (by simp)) (hdS n)
  have hcomp n := hf.comp_smooth hB hρ (hS n) (hS0 n) (hdS n)
  let z (n : ℕ) : ScalarForm.Domain J :=
    ⟨WithLp.toLp 2 ((hcomp n).1.toLp _, (hcomp n).2.1.toLp _),
      (mem_completion_iff hU hB hρ _ _ (hcomp n).1 (hcomp n).2.1).mpr (hcomp n)⟩
  have hz (n : ℕ) : ScalarForm.energy J (z n) (z n) ≤ ScalarForm.energy J f f := by
    simp only [ScalarForm.energy, real_inner_self_eq_norm_sq]
    change ‖ScalarForm.deriv J (z n)‖ ^ 2 ≤ ‖D‖ ^ 2
    have hn : ‖ScalarForm.deriv J (z n)‖ ≤ ‖D‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [(hcomp n).2.1.coeFn_toLp] with x hx
      change ‖((hcomp n).2.1.toLp _) x‖ ≤ ‖D x‖
      rw [hx, norm_smul]
      have hd : ‖deriv (S n) (F x)‖ ≤ (1 : ℝ) := by exact_mod_cast hdS n (F x)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hd (norm_nonneg (D x))
    nlinarith [norm_nonneg (ScalarForm.deriv J (z n)), norm_nonneg D]
  have hTF : MemLp (fun x => T (F x)) 2 ρ := hT.comp_memLp h0 (Lp.memLp F)
  have hl : Tendsto (fun n => ScalarForm.value J (z n)) atTop (𝓝 (hTF.toLp _)) := by
    apply tendsto_toLp_of_dominated (fun n => (hcomp n).1) hTF (Lp.memLp F).norm
    · intro n
      exact Eventually.of_forall fun x => by
        simpa only [hS0 n, sub_zero, dist_zero_right, NNReal.coe_one, one_mul] using
          (hLip n).dist_le_mul (F x) 0
    · exact Eventually.of_forall fun x => by
        simpa only [h0, sub_zero, dist_zero_right, NNReal.coe_one, one_mul] using
          hT.dist_le_mul (F x) 0
    · exact Eventually.of_forall fun x => by
        simpa only [h0, sub_zero] using (hlφ (F x)).sub (hlφ 0)
  let B : ScalarForm.Domain J →L[ℝ] ScalarForm.Domain J →L[ℝ] ℝ :=
    let b : Lp E 2 ρ →L[ℝ] Lp E 2 ρ →L[ℝ] ℝ := innerSL ℝ
    b.bilinearComp (ScalarForm.deriv J) (ScalarForm.deriv J)
  obtain ⟨g, hg, he⟩ := ClosedFormResolvent.Internal.exists_of_energy_bounded_approximation
    B (ScalarForm.value J) (ScalarForm.energy_nonneg J) (ScalarForm.energy_symm J)
    (ScalarForm.norm_sq J) (hTF.toLp _) z (ScalarForm.energy J f f) hl hz
  refine ⟨g, ?_, he⟩
  rw [hg]
  exact hTF.coeFn_toLp

end Riesz2.EuclideanScalarForm

namespace Riesz2.EuclideanScalarForm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ρ : Measure E} [IsFiniteMeasure ρ] {U : Set E}

set_option backward.isDefEq.respectTransparency false in
/-- The concrete Neumann completion is a closed scalar Dirichlet form in the
literal sense, including every normal contraction (Proposition 3.3 and Subsection 3.1). -/
theorem isClosedScalarDirichletForm (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hρ : ∀ᵐ x ∂ρ, x ∈ U)
    (hinj : Function.Injective (ScalarForm.value (smoothJet hU hB hρ))) :
    IsClosedScalarDirichletForm
      (ScalarForm.realization (smoothJet hU hB hρ) hinj) := by
  let J := smoothJet hU hB hρ
  let Q := ScalarForm.realization J hinj
  let e : ScalarForm.Domain J ≃ₗ[ℝ] Q.1 := ScalarForm.valueEquiv J hinj
  have he (f g : Q.1) : Q.2 f g = ScalarForm.energy J (e.symm f) (e.symm g) := rfl
  have hv (f : Q.1) : ScalarForm.value J (e.symm f) = f.val := by
    exact congrArg Subtype.val (e.apply_symm_apply f)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hr : range (fun f : Q.1 => f.val) = range (ScalarForm.value J) := by
      ext u
      constructor
      · rintro ⟨f, rfl⟩
        exact ⟨e.symm f, hv f⟩
      · rintro ⟨f, rfl⟩
        exact ⟨e f, rfl⟩
    rw [denseRange_iff_closure_range, hr]
    exact (denseRange_value hU hB hρ).closure_range
  · intro f g
    rw [he, he, ScalarForm.energy_symm]
  · intro f
    rw [he]
    exact ScalarForm.energy_nonneg J _
  · intro f u hval hC
    have hc : CauchySeq (fun n => e.symm (f n)) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨k, hk⟩ := hC (ε ^ 2) (sq_pos_of_pos hε)
      refine ⟨k, fun i hi j hj => ?_⟩
      have h := hk i j hi hj
      have hn := ScalarForm.norm_sq J (e.symm (f i) - e.symm (f j))
      rw [map_sub, hv, hv] at hn
      have hen : ScalarForm.energy J (e.symm (f i) - e.symm (f j))
          (e.symm (f i) - e.symm (f j)) = Q.2 (f i - f j) (f i - f j) := by
        rw [he, map_sub]
      rw [hen] at hn
      rw [dist_eq_norm]
      nlinarith [norm_nonneg (e.symm (f i) - e.symm (f j))]
    obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hc
    have hgv : ScalarForm.value J g = u := by
      apply tendsto_nhds_unique _ hval
      simpa only [Function.comp_def, hv] using (ScalarForm.value J).continuous.tendsto g |>.comp hg
    refine ⟨e g, hgv, ?_⟩
    have ht : Tendsto (fun n => ScalarForm.deriv J (e.symm (f n) - g)) atTop (𝓝 0) := by
      simpa only [sub_self, map_zero, Function.comp_def] using
        (ScalarForm.deriv J).continuous.tendsto (0 : ScalarForm.Domain J) |>.comp
          (by simpa only [sub_self] using hg.sub (tendsto_const_nhds (x := g)))
    change Tendsto (fun k => Q.2 (f k - e g) (f k - e g)) atTop (𝓝 0)
    have heq (n : ℕ) : Q.2 (f n - e g) (f n - e g) =
        ‖ScalarForm.deriv J (e.symm (f n) - g)‖ ^ 2 := by
      have hes : e.symm (f n - e g) = e.symm (f n) - g := by
        exact (e.symm.map_sub (f n) (e g)).trans
          (congrArg (fun v => e.symm (f n) - v) (e.symm_apply_apply g))
      rw [he, hes, ScalarForm.energy, real_inner_self_eq_norm_sq]
    simp_rw [heq]
    simpa only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using ht.norm.pow 2
  · intro T hT h0 f
    obtain ⟨g, hg, he'⟩ := normal_contraction hU hB hρ T hT h0 (e.symm f)
    refine ⟨e g, ?_, ?_⟩
    · change ∀ᵐ x ∂ρ, ScalarForm.value J g x = T (f.val x)
      rw [← hv f]
      exact hg
    · change Q.2 (e g) (e g) ≤ Q.2 f f
      simpa only [he, LinearEquiv.symm_apply_apply] using he'

end Riesz2.EuclideanScalarForm

namespace Riesz2.IntrinsicScalarCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ρ : Measure E} {U : Set E} {V : E → ℝ}

/-- The actual intrinsic Gibbs form satisfies the full Dirichlet-form
certificate required in Proposition 3.3. -/
theorem closed_dirichlet (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) :
    IsClosedScalarDirichletForm (form hU hB hV) := by
  have := probability hV
  exact EuclideanScalarForm.isClosedScalarDirichletForm hU hB (supported hU hV)
    (value_injective hU hB hV)

end Riesz2.IntrinsicScalarCore
