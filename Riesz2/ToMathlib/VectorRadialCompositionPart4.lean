/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.VectorRadialCompositionPart3
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Radial tests for arbitrary closed scalar Dirichlet forms

This completes the abstract finite-vector interface of
the proof of Proposition 3.6. Scalar resolvents preserve Euclidean balls.
Their energy increments control difference energies, giving strong convergence
in the complete form norm. The limiting projection supplies the radial test.
The test preserves the full matrix-energy domain and fixed component
subspaces, with no restriction on how its direction varies over the base.
-/

@[expose] public section
noncomputable section

open Filter Set Topology

namespace Riesz2.ClosedFormResolvent.Internal

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (B : V →L[ℝ] V →L[ℝ] ℝ) (J : V →L[ℝ] H)

/-- Resolvent energy increments dominate difference energies. This supplies the
strong convergence step of the proof of Proposition 3.6. -/
theorem energy_increment (hB : ∀ v, 0 ≤ B v v)
    (hs : ∀ v w, B v w = B w v) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (w : H) (x y : V)
    (hx : ∀ v, B x v + a * inner ℝ (J x - w) (J v) = 0)
    (hy : ∀ v, B y v + b * inner ℝ (J y - w) (J v) = 0) :
    B (y - x) (y - x) ≤ B y y - B x x := by
  have he : B y (y - x) = B x (y - x) + B (y - x) (y - x) := by
    simp only [map_sub, sub_apply]
    ring
  have hi : inner ℝ (J y - w) (J (y - x)) =
      inner ℝ (J x - w) (J (y - x)) + ‖J (y - x)‖ ^ 2 := by
    rw [show J y - w = (J x - w) + J (y - x) by rw [map_sub]; abel,
      inner_add_left, real_inner_self_eq_norm_sq]
  have hid : (b - a) * B x (y - x) =
      a * B (y - x) (y - x) + a * b * ‖J (y - x)‖ ^ 2 := by
    have h₁ := hx (y - x)
    have h₂ := hy (y - x)
    rw [he, hi] at h₂
    linear_combination b * h₁ - a * h₂
  have hp : 0 ≤ B x (y - x) := by
    have hn := add_nonneg (mul_nonneg ha.le (hB (y - x)))
      (mul_nonneg (mul_nonneg ha.le (ha.trans hab).le) (sq_nonneg ‖J (y - x)‖))
    rw [← hid] at hn
    exact nonneg_of_mul_nonneg_right hn (sub_pos.mpr hab)
  have hex : B y y - B x x =
      2 * B x (y - x) + B (y - x) (y - x) := by
    simp only [map_sub, sub_apply, hs y x]
    ring
  rw [hex]
  linarith

/-- An energy-bounded sequence of resolvents of a fixed value converges strongly
in the complete form domain (the proof of Proposition 3.6, internal
limit argument). No membership of the limiting value is assumed. -/
theorem exists_limit [CompleteSpace V]
    (hB : ∀ v, 0 ≤ B v v) (hs : ∀ v w, B v w = B w v)
    (hnorm : ∀ v, ‖v‖ ^ 2 = ‖J v‖ ^ 2 + B v v)
    (w : H) (y : ℕ → V) (C : ℝ)
    (heq : ∀ n v, B (y n) v + ((n : ℝ) + 1) * inner ℝ (J (y n) - w) (J v) = 0)
    (henergy : ∀ n, B (y n) (y n) ≤ C)
    (herror : ∀ n : ℕ, ((n : ℝ) + 1) * ‖J (y n) - w‖ ^ 2 ≤ C) :
    ∃ z : V, J z = w ∧ Tendsto y atTop (𝓝 z) := by
  have hval : Tendsto (fun n => J (y n)) atTop (𝓝 w) := by
    have ht : Tendsto (fun n : ℕ => C / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      simpa only [mul_one_div, mul_zero] using
        (tendsto_const_nhds (x := C)).mul tendsto_one_div_add_atTop_nhds_zero_nat
    have hz : Tendsto (fun n => ‖J (y n) - w‖ ^ 2) atTop (𝓝 0) :=
      squeeze_zero (fun n => sq_nonneg _) (fun n =>
        (le_div_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr (by
          simpa only [mul_comm] using herror n)) ht
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hz.sqrt
  have hinc (n m : ℕ) (h : n ≤ m) :
      B (y m - y n) (y m - y n) ≤ B (y m) (y m) - B (y n) (y n) := by
    rcases h.eq_or_lt with rfl | h
    · simp
    · exact energy_increment B J hB hs _ _ (by positivity)
        (by exact_mod_cast Nat.add_lt_add_right h 1) w _ _ (heq n) (heq m)
  have hmono : Monotone (fun n => B (y n) (y n)) := by
    intro n m h
    have := (hB (y m - y n)).trans (hinc n m h)
    linarith
  have hbdd : BddAbove (range (fun n => B (y n) (y n))) :=
    ⟨C, by rintro _ ⟨n, rfl⟩; exact henergy n⟩
  have hec := (tendsto_atTop_ciSup hmono hbdd).cauchySeq
  have hvc := hval.cauchySeq
  have hc : CauchySeq y := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨k₁, hk₁⟩ := Metric.cauchySeq_iff.mp hvc (ε / 2) (by positivity)
    obtain ⟨k₂, hk₂⟩ := Metric.cauchySeq_iff.mp hec (ε ^ 2 / 2) (by positivity)
    refine ⟨max k₁ k₂, fun n hn m hm => ?_⟩
    have hv := hk₁ n ((le_max_left _ _).trans hn) m ((le_max_left _ _).trans hm)
    have he := hk₂ n ((le_max_right _ _).trans hn) m ((le_max_right _ _).trans hm)
    rw [dist_eq_norm] at hv
    rw [Real.dist_eq] at he
    have hed : B (y n - y m) (y n - y m) < ε ^ 2 / 2 := by
      rcases le_total m n with h | h
      · exact (hinc m n h).trans_lt ((le_abs_self _).trans_lt he)
      · have hd : B (y m - y n) (y m - y n) =
            B (y n - y m) (y n - y m) := by
          simp only [map_sub, sub_apply]
          ring
        rw [← hd]
        rw [abs_sub_comm] at he
        exact (hinc n m h).trans_lt ((le_abs_self _).trans_lt he)
    have hv' : ‖J (y n - y m)‖ < ε / 2 := by simpa only [map_sub] using hv
    have hn' := hnorm (y n - y m)
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (y n - y m), norm_nonneg (J (y n - y m))]
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨z, tendsto_nhds_unique (J.continuous.tendsto z |>.comp hz) hval, hz⟩

end Riesz2.ClosedFormResolvent.Internal

open MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace Riesz2.VectorRadial

section Values

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι] {ρ : Measure α}

/-- The complement of the radial excess has values in the closed ball
(Subsection 3.5), for any finite tuple of scalar L² classes. -/
theorem sub_truncateValues_bound (R : ℝ≥0) (u : ι → Lp ℝ 2 ρ) :
    ∀ᵐ x ∂ρ, ‖(WithLp.toLp 2 (fun i => (u i - truncateValues R u i) x) :
      EuclideanSpace ℝ ι)‖ ≤ R := by
  have hsub := ae_all_iff.mpr (fun i => Lp.coeFn_sub (u i) (truncateValues R u i))
  filter_upwards [hsub, truncateValues_ae R u] with x hs ht
  have he : (WithLp.toLp 2 (fun i => (u i - truncateValues R u i) x) :
      EuclideanSpace ℝ ι) =
      (WithLp.toLp 2 (fun i => u i x) : EuclideanSpace ℝ ι) -
        truncate R (WithLp.toLp 2 (fun i => u i x) : EuclideanSpace ℝ ι) := by
    ext i
    exact (hs i).trans (by simp only [Pi.sub_apply, ht i]; rfl)
  rw [he]
  exact norm_sub_truncate_le R _

/-- The pointwise projection variational inequality integrated in vector L²
(the proof of Proposition 3.6, abstract form proof). -/
theorem inner_truncateValues_projection_nonpos (R : ℝ≥0)
    (u y : ι → Lp ℝ 2 ρ)
    (hy : ∀ᵐ x ∂ρ,
      ‖(WithLp.toLp 2 (fun i => y i x) : EuclideanSpace ℝ ι)‖ ≤ R) :
    inner ℝ (WithLp.toLp 2 (truncateValues R u) : PiLp 2 (fun _ : ι => Lp ℝ 2 ρ))
      (WithLp.toLp 2 y - (WithLp.toLp 2 u - WithLp.toLp 2 (truncateValues R u))) ≤ 0 := by
  let d : ι → Lp ℝ 2 ρ := fun i => y i - (u i - truncateValues R u i)
  have hint : ∀ i, Integrable (fun x => truncateValues R u i x * d i x) ρ :=
    fun i => (Lp.memLp _).integrable_mul (Lp.memLp _)
  have hsub := ae_all_iff.mpr (fun i => Lp.coeFn_sub (u i) (truncateValues R u i))
  have hd := ae_all_iff.mpr (fun i => Lp.coeFn_sub (y i) (u i - truncateValues R u i))
  have hp : ∀ᵐ x ∂ρ, (∑ i, truncateValues R u i x * d i x) ≤ 0 := by
    filter_upwards [hy, hsub, hd, truncateValues_ae R u] with x hx hs hd ht
    have h := inner_projection_error_nonpos R
      (WithLp.toLp 2 (fun i => u i x) : EuclideanSpace ℝ ι)
      (WithLp.toLp 2 (fun i => y i x) : EuclideanSpace ℝ ι) hx
    convert h using 1
    simp only [PiLp.inner_apply, Real.inner_apply, PiLp.sub_apply]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [d]
    simp only [hd i, Pi.sub_apply, hs i, ht i]
    rfl
  have hi := integral_nonpos_of_ae hp
  rw [integral_finsetSum Finset.univ (fun i _ => hint i)] at hi
  rw [PiLp.inner_apply]
  convert hi using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [L2.inner_def]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    change inner ℝ (truncateValues R u i x) (d i x) = truncateValues R u i x * d i x
    rw [Real.inner_apply, mul_comm])

end Values

section AbstractForm

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι] {ρ : Measure α}
  (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q)

include hQ

/-- Radial truncation of an arbitrary finite vector belongs to the scalar form
domain and has nonnegative summed diffusion pairing
(the proof of Proposition 3.6). The pairing dominates the test's energy,
and truncation decreases total diffusion energy. Only the scalar
Dirichlet-form assumptions are used. -/
theorem exists_truncation (R : ℝ≥0) (u : ι → Q.1) :
    ∃ h : ι → Q.1,
      (∀ i, (h i).val = truncateValues R (fun j => (u j).val) i) ∧
      0 ≤ ∑ i, Q.2 (u i) (h i) ∧
      (∑ i, Q.2 (h i) (h i)) ≤ ∑ i, Q.2 (u i) (h i) ∧
      (∑ i, Q.2 (h i) (h i)) ≤ ∑ i, Q.2 (u i) (u i) := by
  classical
  let V := PiLp 2 (fun _ : ι => ScalarFormHilbert.Space Q hQ)
  let H := PiLp 2 (fun _ : ι => Lp ℝ 2 ρ)
  let J : V →L[ℝ] H :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => Lp ℝ 2 ρ)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (fun i =>
        (ScalarFormHilbert.value Q hQ).comp (PiLp.proj 2 _ i)))
  let B : V →L[ℝ] V →L[ℝ] ℝ :=
    innerSL ℝ - (innerSL ℝ).bilinearComp J J
  have hJ (v : V) (i : ι) : J v i = ScalarFormHilbert.value Q hQ (v i) := rfl
  have hB (v t : V) : B v t = ∑ i,
      Q.2 (ScalarFormHilbert.equiv Q hQ (v i))
        (ScalarFormHilbert.equiv Q hQ (t i)) := by
    change inner ℝ v t - inner ℝ (J v) (J t) = _
    rw [PiLp.inner_apply v t, PiLp.inner_apply (J v) (J t)]
    simp only [ScalarFormHilbert.inner_eq, hJ, Finset.sum_add_distrib]
    ring
  have hpos (v : V) : 0 ≤ B v v := by
    rw [hB]
    exact Finset.sum_nonneg (fun i _ => hQ.2.2.1 _)
  have hsym (v t : V) : B v t = B t v := by
    simp only [hB, hQ.2.1]
  have hnorm (v : V) : ‖v‖ ^ 2 = ‖J v‖ ^ 2 + B v v := by
    change ‖v‖ ^ 2 = ‖J v‖ ^ 2 + (inner ℝ v v - inner ℝ (J v) (J v))
    simp only [real_inner_self_eq_norm_sq]
    ring
  let U : V := WithLp.toLp 2 (fun i => (ScalarFormHilbert.equiv Q hQ).symm (u i))
  let W : H := WithLp.toLp 2 (fun i => (u i).val - truncateValues R (fun j => (u j).val) i)
  have hUW : J U - W = (WithLp.toLp 2 (truncateValues R (fun j => (u j).val)) : H) := by
    apply (WithLp.equiv 2 _).injective
    funext i
    change (u i).val - ((u i).val - truncateValues R (fun j => (u j).val) i) = _
    abel
  have hW : ∀ᵐ x ∂ρ,
      ‖(WithLp.toLp 2 (fun i => W i x) : EuclideanSpace ℝ ι)‖ ≤ R :=
    sub_truncateValues_bound R (fun i => (u i).val)
  let y : ℕ → V := fun n => WithLp.toLp 2 (fun i =>
    ScalarFormHilbert.shiftedSolution Q hQ ((n : ℝ) + 1) (by positivity)
      (((n : ℝ) + 1) • W i))
  have heq (n : ℕ) (v : V) :
      B (y n) v + ((n : ℝ) + 1) * inner ℝ (J (y n) - W) (J v) = 0 := by
    rw [hB, inner_sub_left, PiLp.inner_apply (J (y n)) (J v),
      PiLp.inner_apply W (J v), mul_sub]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, hJ]
    apply Finset.sum_eq_zero
    intro i _
    have he := ScalarFormHilbert.shiftedSolution_solves Q hQ
      ((n : ℝ) + 1) (by positivity) (((n : ℝ) + 1) • W i) (v i)
    rw [real_inner_smul_left] at he
    change Q.2 (ScalarFormHilbert.equiv Q hQ (y n i))
      (ScalarFormHilbert.equiv Q hQ (v i)) +
      ((n : ℝ) + 1) * inner ℝ (ScalarFormHilbert.value Q hQ (y n i))
        (ScalarFormHilbert.value Q hQ (v i)) =
      ((n : ℝ) + 1) * inner ℝ (W i) (ScalarFormHilbert.value Q hQ (v i)) at he
    linarith
  have hyball (n : ℕ) : ∀ᵐ x ∂ρ,
      ‖(WithLp.toLp 2 (fun i => J (y n) i x) : EuclideanSpace ℝ ι)‖ ≤ R := by
    apply vector_shiftedSolution_bound Q hQ ((n : ℝ) + 1) (by positivity)
      (fun i => ((n : ℝ) + 1) • W i) R
    have hsm := ae_all_iff.mpr (fun i => Lp.coeFn_smul ((n : ℝ) + 1) (W i))
    filter_upwards [hW, hsm] with x hx hs
    have he : (WithLp.toLp 2 (fun i => (((n : ℝ) + 1) • W i) x) :
        EuclideanSpace ℝ ι) =
        ((n : ℝ) + 1) • (WithLp.toLp 2 (fun i => W i x) : EuclideanSpace ℝ ι) := by
      ext i
      exact hs i
    rw [he, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)]
    exact mul_le_mul_of_nonneg_left hx (by positivity)
  have hproj (n : ℕ) : inner ℝ (J U - W) (J (y n) - W) ≤ 0 := by
    have hp := inner_truncateValues_projection_nonpos R (fun i => (u i).val)
      (fun i => J (y n) i) (hyball n)
    convert hp using 1
    rw [hUW]
    congr 1
  have hest (n : ℕ) := Internal.energy_le_of_resolvent_projection B.toBilinForm
    J.toLinearMap hpos hsym ((n : ℝ) + 1) (by positivity) U (y n) W (heq n) (hproj n)
  obtain ⟨z, hz, ht⟩ := ClosedFormResolvent.Internal.exists_limit B J hpos hsym hnorm W y
    (B U U) heq (fun n => (hest n).1) (fun n => (hest n).2.2)
  have hp : 0 ≤ B z (U - z) := by
    have hc : Continuous (fun v : V => B v (U - v)) :=
      B.continuous.clm_apply (continuous_const.sub continuous_id)
    exact ge_of_tendsto ((hc.tendsto z).comp ht)
      (Eventually.of_forall (fun n => (hest n).2.1))
  let h : ι → Q.1 := fun i => ScalarFormHilbert.equiv Q hQ ((U - z) i)
  have hval (i : ι) : (h i).val = truncateValues R (fun j => (u j).val) i := by
    have hi := congrArg (fun v : H => v i) hz
    change ScalarFormHilbert.value Q hQ (z i) =
      (u i).val - truncateValues R (fun j => (u j).val) i at hi
    change (u i).val - ScalarFormHilbert.value Q hQ (z i) = _
    rw [hi]
    abel
  have hpair : B (U - z) (U - z) ≤ B U (U - z) := by
    have he : B U (U - z) = B (U - z) (U - z) + B z (U - z) := by
      simp only [map_sub, sub_apply]
      ring
    rw [he]
    linarith
  have henergy : B (U - z) (U - z) ≤ B U U := by
    have he : B U U = B (U - z) (U - z) + 2 * B z (U - z) + B z z := by
      simp only [map_sub, sub_apply, hsym U z]
      ring
    rw [he]
    linarith [hpos z]
  refine ⟨h, hval, ?_, ?_, ?_⟩
  · simpa only [hB, h, U, LinearEquiv.apply_symm_apply] using (hpos (U - z)).trans hpair
  · simpa only [hB, h, U, LinearEquiv.apply_symm_apply] using hpair
  · simpa only [hB, h, U, LinearEquiv.apply_symm_apply] using henergy

/-- Arbitrary finite-vector radial tests in the literal full matrix-energy
domain (Subsection 3.5, the proof of Proposition 3.6). This preserves
any fixed component subspace, and allows unbounded nonnegative matrix fields. -/
theorem admissible_truncation (R : ℝ≥0) (u : ι → Q.1)
    (M : α → Matrix ι ι ℝ) (S : Submodule ℝ (ι → ℝ))
    (hMmeas : ∀ i j, Measurable (fun x => M x i j))
    (hM : ∀ᵐ x ∂ρ, (M x).PosSemidef) (hu : WeightedFormDomain Q M S u) :
    ∃ h : ι → Q.1,
      (∀ i, (h i).val = truncateValues R (fun j => (u j).val) i) ∧
      WeightedFormDomain Q M S h ∧ 0 ≤ ∑ i, Q.2 (u i) (h i) ∧
      (∫ x, matrixFieldPair M (fun i => (h i).val) (fun i => (h i).val) x ∂ρ) ≤
        ∫ x, matrixFieldPair M (fun i => (u i).val) (fun i => (u i).val) x ∂ρ := by
  obtain ⟨h, hh, hp, _, _⟩ := exists_truncation Q hQ R u
  refine ⟨h, hh, Internal.weightedFormDomain_of_truncateValues R Q M S hMmeas hM
    u h hu hh, hp, ?_⟩
  simpa only [hh] using integral_matrixFieldPair_truncateValues_le R M hMmeas hM
    (fun i => (u i).val) hu.2

end AbstractForm

end Riesz2.VectorRadial
