/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.VectorRadialCompositionPart2
public import Riesz2.ToMathlib.CoerciveSolutionMaps

/-!
# Abstract scalar-form radial tests on a fixed line

Infrastructure for Subsection 3.5 and the proof of Proposition 3.6.
The scalar normal-contraction property of the closed Dirichlet form gives
radial tests without a gradient realization when the component field lies in
one fixed line. The pairing dominates the energy of the test. The radius-zero
case works for every finite vector field.

Scalar and finite-vector shifted resolvents preserve the corresponding balls.
An internal estimate bounds the energy and L² error of a resolvent of the
metric projection, for use in a subsequent form-domain limit argument.

This does not assert the general finite-vector normal-contraction property.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set Topology
open scoped BigOperators NNReal ENNReal

namespace Riesz2.VectorRadial

section Pointwise

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The reflection in the ball projection is contractive (Subsection 3.5). -/
theorem lipschitzWith_reflected_truncate (R : ℝ≥0) :
    LipschitzWith 1 (fun z : V => z - (2 : ℝ) • truncate R z) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have he : (z - (2 : ℝ) • truncate R z) - (w - (2 : ℝ) • truncate R w) =
      (z - w) - (2 : ℝ) • (truncate R z - truncate R w) := by module
  rw [he]
  have hf := firm R z w
  have hn : ‖(z - w) - (2 : ℝ) • (truncate R z - truncate R w)‖ ^ 2 =
      ‖z - w‖ ^ 2 - 4 * inner ℝ (truncate R z - truncate R w) (z - w) +
        4 * ‖truncate R z - truncate R w‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm (z - w), norm_smul]
    norm_num
    ring
  nlinarith [norm_nonneg ((z - w) - (2 : ℝ) • (truncate R z - truncate R w)),
    norm_nonneg (z - w)]

/-- On any fixed line the vector radial map is the scalar radial map with the
radius divided by the length of its direction (Subsection 3.5). -/
theorem truncate_smul_line (R : ℝ≥0) (a : V) (t : ℝ) :
    truncate R (t • a) = truncate (R / ‖a‖₊) t • a := by
  by_cases ha : a = 0
  · simp [ha, truncate_zero]
  by_cases ht : t = 0
  · simp [ht, truncate_zero]
  have hn : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have ht' : ‖t‖ ≠ 0 := norm_ne_zero_iff.mpr ht
  have hc : coefficient R (t • a) = coefficient (R / ‖a‖₊) t := by
    unfold coefficient
    rw [norm_smul]
    congr 2
    simp only [NNReal.coe_div, coe_nnnorm]
    field_simp
  simp only [truncate, hc, smul_smul, smul_eq_mul]

/-- The coercive pointwise inequality for radial tests
(Proposition 3.6, proof). -/
theorem inner_source_truncate_lower (R : ℝ≥0) (b : ℝ) (z v : V)
    (hv : ‖v‖ ≤ b * R) :
    b * ‖truncate R z‖ ^ 2 ≤ inner ℝ (b • z - v) (truncate R z) := by
  have hi := inner_truncate_sub R z
  have hs := real_inner_le_norm v (truncate R z)
  have hb := mul_le_mul_of_nonneg_right hv (norm_nonneg (truncate R z))
  rw [inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm] at hi
  rw [inner_sub_left, real_inner_smul_left]
  rw [show inner ℝ z (truncate R z) = ‖truncate R z‖ ^ 2 + R * ‖truncate R z‖ by
    linarith]
  nlinarith

/-- Variational inequality for the ball projection (Subsection 3.5), in the sign
needed to estimate the resolvents of that projection. -/
theorem inner_projection_error_nonpos (R : ℝ≥0) (z y : V) (hy : ‖y‖ ≤ R) :
    inner ℝ (truncate R z) (y - (z - truncate R z)) ≤ 0 := by
  have hi := inner_truncate_sub R z
  have hb := (real_inner_le_norm (truncate R z) y).trans
    (mul_le_mul_of_nonneg_left hy (norm_nonneg _))
  rw [inner_sub_right, hi]
  nlinarith

end Pointwise

section ResolventEstimates

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Internal algebraic estimate for the abstract resolvent proof of Proposition 3.6. A resolvent of the metric projection has
energy bounded by the original field, and its squared L² error is bounded by
that energy divided by the shift. This is an internal criterion, not a claim
that the projection is already in the form domain. -/
theorem Internal.energy_le_of_resolvent_projection
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] H)
    (hB : ∀ v, 0 ≤ B v v) (hBs : ∀ v w, B v w = B w v)
    (b : ℝ) (hb : 0 < b) (u y : V) (w : H)
    (heq : ∀ v, B y v + b * inner ℝ (J y - w) (J v) = 0)
    (hproj : inner ℝ (J u - w) (J y - w) ≤ 0) :
    B y y ≤ B u u ∧ 0 ≤ B y (u - y) ∧ b * ‖J y - w‖ ^ 2 ≤ B u u := by
  have hi : inner ℝ (J y - w) (J (u - y)) =
      inner ℝ (J u - w) (J y - w) - ‖J y - w‖ ^ 2 := by
    rw [map_sub]
    have hj : J u - J y = (J u - w) - (J y - w) := by abel
    rw [hj, inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm]
  have he := heq (u - y)
  rw [hi] at he
  have hn := mul_nonneg hb.le (sq_nonneg ‖J y - w‖)
  have hp : b * ‖J y - w‖ ^ 2 ≤ B y (u - y) := by
    have := mul_nonpos_of_nonneg_of_nonpos hb.le hproj
    nlinarith
  have hpos : 0 ≤ B y (u - y) := hn.trans hp
  have hex := hB (u - y)
  simp only [map_sub, LinearMap.sub_apply, hBs u y] at hex
  have hyu : B y (u - y) = B y u - B y y := map_sub (B y) u y
  rw [hyu] at hp hpos
  refine ⟨by linarith, ?_, ?_⟩
  · rw [hyu]
    exact hpos
  · linarith [hB y]

end ResolventEstimates

section AbstractScalar

variable {α : Type*} [MeasurableSpace α] {ρ : Measure α}
  (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q)

include hQ

/-- Scalar specialization of the proof of Proposition 3.6, using only
the normal-contraction property. The stronger pairing inequality follows
by applying that property to the reflected radial map. -/
theorem exists_scalar_truncation (R : ℝ≥0) (f : Q.1) :
    ∃ g : Q.1, (∀ᵐ x ∂ρ, g.val x = truncate R (f.val x)) ∧
      Q.2 g g ≤ Q.2 f f ∧ Q.2 g g ≤ Q.2 f g := by
  obtain ⟨g, hg, heg⟩ := hQ.2.2.2.2 (truncate R)
    (lipschitzWith_truncate R) (truncate_zero R) f
  obtain ⟨k, hk, hek⟩ := hQ.2.2.2.2 (fun t : ℝ => t - (2 : ℝ) • truncate R t)
    (lipschitzWith_reflected_truncate R) (by simp [truncate_zero]) f
  have hkg : k = f - (2 : ℝ) • g := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [hk, hg, Lp.coeFn_sub f.val ((2 : ℝ) • g.val),
      Lp.coeFn_smul (2 : ℝ) g.val] with x hx hy hs hm
    simpa only [Submodule.coe_sub, Submodule.coe_smul, hs, hm, hy,
      Pi.sub_apply, Pi.smul_apply] using hx
  rw [hkg] at hek
  have hexpand : Q.2 (f - (2 : ℝ) • g) (f - (2 : ℝ) • g) =
      Q.2 f f - 4 * Q.2 f g + 4 * Q.2 g g := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, hQ.2.1 g f]
    ring
  exact ⟨g, hg, heg, by rw [hexpand] at hek; linarith⟩

/-- Nonnegative diffusion pairing for the scalar radial test, without a gradient
realization (the proof of Proposition 3.6). -/
theorem exists_scalar_truncation_nonneg (R : ℝ≥0) (f : Q.1) :
    ∃ g : Q.1, (∀ᵐ x ∂ρ, g.val x = truncate R (f.val x)) ∧ 0 ≤ Q.2 f g := by
  obtain ⟨g, hg, _, hfg⟩ := exists_scalar_truncation Q hQ R f
  exact ⟨g, hg, (hQ.2.2.1 g).trans hfg⟩

/-- The scalar shifted resolvent preserves a uniform bound after scaling its
source by the shift. This is the scalar resolvent ingredient in the abstract
proof of Proposition 3.6. It uses no gradient realization. -/
theorem scalar_shiftedSolution_bound (b : ℝ) (hb : 0 < b) (f : Lp ℝ 2 ρ)
    (R : ℝ≥0) (hf : ∀ᵐ x ∂ρ, ‖f x‖ ≤ b * R) :
    ∀ᵐ x ∂ρ,
      ‖ScalarFormHilbert.value Q hQ (ScalarFormHilbert.shiftedSolution Q hQ b hb f) x‖ ≤ R := by
  let y := ScalarFormHilbert.shiftedSolution Q hQ b hb f
  let u : Q.1 := ScalarFormHilbert.equiv Q hQ y
  obtain ⟨g, hg, hpos⟩ := exists_scalar_truncation_nonneg Q hQ R u
  have he := ScalarFormHilbert.shiftedSolution_solves Q hQ b hb f
    ((ScalarFormHilbert.equiv Q hQ).symm g)
  change Q.2 u g + b * inner ℝ u.val g.val = inner ℝ f g.val at he
  have hbound : b * ‖g.val‖ ^ 2 ≤ b * inner ℝ u.val g.val - inner ℝ f g.val := by
    have hgg := (Lp.memLp g.val).integrable_mul (Lp.memLp g.val)
    have hug := (Lp.memLp u.val).integrable_mul (Lp.memLp g.val)
    have hfg := (Lp.memLp f).integrable_mul (Lp.memLp g.val)
    have hi : (∫ x, b * (g.val x * g.val x) ∂ρ) ≤
        ∫ x, b * (u.val x * g.val x) - f x * g.val x ∂ρ := by
      apply integral_mono_ae (hgg.const_mul b) ((hug.const_mul b).sub hfg)
      filter_upwards [hf, hg] with x hfx hgx
      have hp := inner_source_truncate_lower R b (u.val x) (f x) hfx
      simp only [← hgx, Real.norm_eq_abs, sq_abs] at hp
      simpa only [Real.inner_apply, smul_eq_mul, pow_two, sub_mul, mul_assoc,
        Pi.mul_apply, Pi.sub_apply] using hp
    have hgg' : ‖g.val‖ ^ 2 = ∫ x, g.val x * g.val x ∂ρ := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      rfl
    rw [hgg', L2.inner_def, L2.inner_def]
    simp only [Real.inner_apply]
    rw [← integral_const_mul, ← integral_const_mul]
    calc
      _ ≤ ∫ x, b * (u.val x * g.val x) - f x * g.val x ∂ρ := hi
      _ = _ := integral_sub (hug.const_mul b) hfg
  have hz : g.val = 0 := by
    have hbnd : b * ‖g.val‖ ^ 2 ≤ 0 := by linarith
    have hs : ‖g.val‖ ^ 2 ≤ 0 := by
      by_contra hn
      have := mul_pos hb (lt_of_not_ge hn)
      linarith
    have hn : ‖g.val‖ = 0 := by nlinarith [norm_nonneg g.val]
    exact norm_eq_zero.mp hn
  filter_upwards [hg, Lp.coeFn_zero ℝ 2 ρ] with x hgx hzero
  have ht : truncate R (u.val x) = 0 := by
    rw [← hgx, hz]
    exact hzero
  have hn := norm_truncate R (u.val x)
  rw [ht, norm_zero] at hn
  change ‖u.val x‖ ≤ R
  have := le_max_right 0 (‖u.val x‖ - R)
  linarith

end AbstractScalar

section AbstractVector

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι] {ρ : Measure α}
  (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q)

include hQ

omit hQ Q in
/-- Finite scalar L² linear combinations are the Euclidean inner products of
their values (Subsection 3.5). -/
theorem linearCombination_values_ae (a : EuclideanSpace ℝ ι) (f : ι → Lp ℝ 2 ρ) :
    ∀ᵐ x ∂ρ, (∑ i, a i • f i) x =
      inner ℝ a (WithLp.toLp 2 (fun i => f i x) : EuclideanSpace ℝ ι) := by
  have hsm : ∀ᵐ x ∂ρ, ∀ i, (a i • f i) x = a i * f i x :=
    ae_all_iff.mpr (fun i => Lp.coeFn_smul (a i) (f i))
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => a i • f i), hsm]
    with x hx hy
  simpa only [Finset.sum_apply, hy, PiLp.inner_apply, Real.inner_apply] using hx

/-- Componentwise scalar resolvents preserve Euclidean balls after scaling the
source by their shift. This couples arbitrary component directions without
assuming a gradient realization (the proof of Proposition 3.6, abstract
resolvent infrastructure). -/
theorem vector_shiftedSolution_bound (b : ℝ) (hb : 0 < b) (f : ι → Lp ℝ 2 ρ)
    (R : ℝ≥0)
    (hf : ∀ᵐ x ∂ρ,
      ‖(WithLp.toLp 2 (fun i => f i x) : EuclideanSpace ℝ ι)‖ ≤ b * R) :
    ∀ᵐ x ∂ρ, ‖(WithLp.toLp 2 (fun i => ScalarFormHilbert.value Q hQ
      (ScalarFormHilbert.shiftedSolution Q hQ b hb (f i)) x) : EuclideanSpace ℝ ι)‖ ≤ R := by
  let J : Lp ℝ 2 ρ →L[ℝ] Lp ℝ 2 ρ :=
    (ScalarFormHilbert.value Q hQ).comp (ScalarFormHilbert.shiftedSolution Q hQ b hb)
  have hdir (a : EuclideanSpace ℝ ι) : ∀ᵐ x ∂ρ,
      ‖inner ℝ a (WithLp.toLp 2 (fun i => J (f i) x) : EuclideanSpace ℝ ι)‖ ≤ ‖a‖ * R := by
    have hsource : ∀ᵐ x ∂ρ, ‖(∑ i, a i • f i) x‖ ≤ b * (‖a‖₊ * R : ℝ≥0) := by
      filter_upwards [hf, linearCombination_values_ae a f] with x hx hy
      rw [hy]
      calc
        _ ≤ ‖a‖ * ‖(WithLp.toLp 2 (fun i => f i x) : EuclideanSpace ℝ ι)‖ :=
          norm_inner_le_norm _ _
        _ ≤ ‖a‖ * (b * R) := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
        _ = _ := by simp only [NNReal.coe_mul, coe_nnnorm]; ring
    have h := scalar_shiftedSolution_bound Q hQ b hb (∑ i, a i • f i)
      (‖a‖₊ * R) hsource
    have heq : J (∑ i, a i • f i) = ∑ i, a i • J (f i) := by simp
    change ∀ᵐ x ∂ρ, ‖J (∑ i, a i • f i) x‖ ≤ (‖a‖₊ * R : ℝ≥0) at h
    rw [heq] at h
    filter_upwards [h, linearCombination_values_ae a (fun i => J (f i))] with x hx hy
    simpa only [hy, NNReal.coe_mul, coe_nnnorm] using hx
  let D := TopologicalSpace.denseSeq (EuclideanSpace ℝ ι)
  have hd : DenseRange D := TopologicalSpace.denseRange_denseSeq _
  filter_upwards [ae_all_iff.mpr (fun n : ℕ => hdir (D n))] with x hx
  let z : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => J (f i) x)
  have hall (a : EuclideanSpace ℝ ι) : ‖inner ℝ a z‖ ≤ ‖a‖ * R := by
    exact hd.induction_on a
      (isClosed_le (continuous_id.inner continuous_const).norm
        (continuous_norm.mul continuous_const)) hx
  have hz := hall z
  rw [real_inner_self_eq_norm_sq, Real.norm_of_nonneg (sq_nonneg _)] at hz
  change ‖z‖ ≤ R
  by_cases hzero : ‖z‖ = 0
  · simpa only [hzero] using R.coe_nonneg
  · have hpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    nlinarith

/-- Fixed-line specialization of the proof of Proposition 3.6 for an
abstract closed scalar Dirichlet form. The field is parametrized as `aᵢ f`.
The direction may vanish and the component type may be empty. -/
theorem exists_truncation_line (R : ℝ≥0) (a : ι → ℝ) (f : Q.1) :
    ∃ h : ι → Q.1,
      (∀ i, (h i).val = truncateValues R (fun j => (a j • f).val) i) ∧
      0 ≤ ∑ i, Q.2 (a i • f) (h i) ∧
      (∑ i, Q.2 (h i) (h i)) ≤ ∑ i, Q.2 (a i • f) (h i) ∧
      (∑ i, Q.2 (h i) (h i)) ≤ ∑ i, Q.2 (a i • f) (a i • f) := by
  let A : EuclideanSpace ℝ ι := WithLp.toLp 2 a
  obtain ⟨g, hg, heg, hfg⟩ := exists_scalar_truncation Q hQ (R / ‖A‖₊) f
  have hv : ∀ i, (a i • g).val = truncateValues R (fun j => (a j • f).val) i := by
    intro i
    apply Lp.ext
    have hf : ∀ᵐ x ∂ρ, ∀ j, (a j • f).val x = a j * f.val x :=
      ae_all_iff.mpr (fun j => Lp.coeFn_smul (a j) f.val)
    have hg' : ∀ᵐ x ∂ρ, ∀ j, (a j • g).val x = a j * g.val x :=
      ae_all_iff.mpr (fun j => Lp.coeFn_smul (a j) g.val)
    filter_upwards [hf, hg', hg, truncateValues_ae R (fun j => (a j • f).val)]
      with x hfx hgx hx htx
    have hvec : (WithLp.toLp 2 (fun j => (a j • f).val x) : EuclideanSpace ℝ ι) =
        f.val x • A := by
      ext j
      simp only [PiLp.smul_apply, A, hfx, smul_eq_mul]
      ring
    have hline := congrArg (fun z : EuclideanSpace ℝ ι => z i)
      (truncate_smul_line R A (f.val x))
    rw [← hvec] at hline
    change coefficient R (WithLp.toLp 2 (fun j => (a j • f).val x) :
      EuclideanSpace ℝ ι) * (a i • f).val x =
        truncate (R / ‖A‖₊) (f.val x) * a i at hline
    rw [hgx, hx, htx, hline, mul_comm]
  have hpair : (∑ i, Q.2 (a i • g) (a i • g)) ≤
      ∑ i, Q.2 (a i • f) (a i • g) := by
    apply Finset.sum_le_sum
    intro i _
    simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_assoc, pow_two]
      using mul_le_mul_of_nonneg_left hfg (sq_nonneg (a i))
  have henergy : (∑ i, Q.2 (a i • g) (a i • g)) ≤
      ∑ i, Q.2 (a i • f) (a i • f) := by
    apply Finset.sum_le_sum
    intro i _
    simpa only [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_assoc, pow_two]
      using mul_le_mul_of_nonneg_left heg (sq_nonneg (a i))
  exact ⟨fun i => a i • g, hv,
    (Finset.sum_nonneg (fun i _ => hQ.2.2.1 (a i • g))).trans hpair,
    hpair, henergy⟩

/-- At radius zero the abstract vector test is the original field, with no
restriction on its component directions (the proof of Proposition 3.6). -/
theorem exists_truncation_radius_zero (u : ι → Q.1) :
    ∃ h : ι → Q.1,
      (∀ i, (h i).val = truncateValues 0 (fun j => (u j).val) i) ∧
      0 ≤ ∑ i, Q.2 (u i) (h i) := by
  refine ⟨u, ?_, Finset.sum_nonneg (fun i _ => hQ.2.2.1 (u i))⟩
  intro i
  apply Lp.ext
  filter_upwards [truncateValues_ae 0 (fun j => (u j).val)] with x hx
  simpa [coefficient] using (hx i).symm

/-- Fixed-line radial tests belong to the full matrix-energy domain,
including unbounded nonnegative matrix fields (Subsection 3.5 and
the proof of Proposition 3.6). -/
theorem admissible_truncation_line (R : ℝ≥0) (a : ι → ℝ) (f : Q.1)
    (M : α → Matrix ι ι ℝ) (S : Submodule ℝ (ι → ℝ))
    (hMmeas : ∀ i j, Measurable (fun x => M x i j))
    (hM : ∀ᵐ x ∂ρ, (M x).PosSemidef)
    (hu : WeightedFormDomain Q M S (fun i => a i • f)) :
    ∃ h : ι → Q.1,
      (∀ i, (h i).val = truncateValues R (fun j => (a j • f).val) i) ∧
      WeightedFormDomain Q M S h ∧
      0 ≤ ∑ i, Q.2 (a i • f) (h i) ∧
      (∫ x, matrixFieldPair M (fun i => (h i).val) (fun i => (h i).val) x ∂ρ) ≤
        ∫ x, matrixFieldPair M (fun i => (a i • f).val) (fun i => (a i • f).val) x ∂ρ := by
  obtain ⟨h, hh, hp, _, _⟩ := exists_truncation_line Q hQ R a f
  refine ⟨h, hh, Internal.weightedFormDomain_of_truncateValues R Q M S hMmeas hM
    (fun i => a i • f) h hu hh, hp, ?_⟩
  simpa only [hh] using integral_matrixFieldPair_truncateValues_le R M hMmeas hM
    (fun i => (a i • f).val) hu.2

end AbstractVector

end Riesz2.VectorRadial
