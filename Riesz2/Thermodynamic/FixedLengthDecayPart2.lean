/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.FixedLengthDecay
public import Riesz2.DecayShort.PhysicalDecayPart3

/-!
# Temperature uniform auxiliary estimates on a fixed-length simplex

Supporting results for Lemma 6.4. Applying the short-range estimates at temperature one
to the matrix `β M` fixes their polynomial degree before choosing a compact positive
temperature interval. The scalar form and the weak solution are unchanged by this
application.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical NNReal MatrixOrder Matrix.Norms.L2Operator

namespace Riesz2.FixedLengthDecay

/-- See Lemma 6.4 of the paper: both short-range estimates have a common
polynomial degree chosen using `s` and the weighted exponent only, before β.
The constant is uniform on every compact positive temperature interval.
Both estimates apply to the same unique solution on the same scalar form. -/
theorem short_auxiliary_temperature_uniform_internal (s a : ℝ) (hs : 1 < s)
    (ha : 1 / 2 < a) (has : a < s - 1 / 2) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ β ∈ Icc βlo βhi,
      ∀ (X ι : Type*) [MeasurableSpace X] [Fintype ι] [DecidableEq ι]
        (ν : Measure X) [IsProbabilityMeasure ν]
        (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q →
        IsConservativeScalarForm Q → ∀ (g : ComponentGeometry ι) (B : ℝ), 1 ≤ B →
        ∀ M : X → Matrix ι ι ℝ, (∀ i j, Measurable (fun x => M x i j)) →
        (∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
          (∀ z : ι → ℝ, B⁻¹ * ∑ i, z i ^ 2 ≤ ∑ i, ∑ j, z i * M x i j * z j) ∧
          (∀ i j, |M x i j| ≤ B * (1 + componentDistance g i j) ^ (-s))) →
        ∀ (i₀ : ι) (χ : Lp ℝ 2 ν),
          (∃! v : ι → Q.1, WeightedWeakSolution Q (fun x => β • M x) ⊤
            (fun i => if i = i₀ then χ else 0) v) ∧
          (∀ v : ι → Q.1, WeightedWeakSolution Q (fun x => β • M x) ⊤
              (fun i => if i = i₀ then χ else 0) v →
            (‖WithLp.toLp 2 (fun i => InitialDecay.distortionWeight g i₀ a i • (v i).val)‖ +
              Real.sqrt (∑ i, Q.2 (InitialDecay.distortionWeight g i₀ a i • v i)
                (InitialDecay.distortionWeight g i₀ a i • v i)) ≤ C * B ^ r * ‖χ‖) ∧
            (∀ j, ‖(v j).val‖ ≤ C * B ^ r *
              (1 + componentDistance g j i₀) ^ (-s) * ‖χ‖)) := by
  obtain ⟨r₁, hr₁, hinit⟩ :=
    DecayShort.PhysicalDecay.initial_decay_compact s a hs ha has
  obtain ⟨r₂, hr₂, hopt⟩ := DecayShort.PhysicalDecay.optimal_decay_compact s hs
  let r := max r₁ r₂
  have hr : 0 ≤ r := hr₁.trans (le_max_left _ _)
  refine ⟨r, hr, ?_⟩
  intro βlo βhi hlo hhi
  obtain ⟨C₁, hC₁, hinit⟩ := hinit βlo βhi hlo hhi
  obtain ⟨C₂, hC₂, hopt⟩ := hopt βlo βhi hlo hhi
  let C := C₁ + C₂
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro β hβ X ι _ _ _ ν _ Q hQ hcons g B hB M hm hM i₀ χ
  have h₁ := hinit β hβ X ι ν Q hQ hcons g B hB M hm hM i₀ χ
  have h₂ := hopt β hβ X ι ν Q hQ hcons g B hB M hm hM i₀ χ
  have hp (t K : ℝ) (ht : t ≤ r) (hK : 0 ≤ K) (hKC : K ≤ C) :
      K * B ^ t ≤ C * B ^ r := by
    exact (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hB ht) hK).trans
      (mul_le_mul_of_nonneg_right hKC (Real.rpow_nonneg (by linarith) _))
  have hp₁ := hp r₁ C₁ (le_max_left _ _) (by linarith) (by dsimp [C]; linarith)
  have hp₂ := hp r₂ C₂ (le_max_right _ _) (by linarith) (by dsimp [C]; linarith)
  refine ⟨h₁.1, fun v hv => ⟨(h₁.2 v hv).trans ?_, fun j => (h₂.2 v hv j).trans ?_⟩⟩
  · exact mul_le_mul_of_nonneg_right hp₁ (norm_nonneg _)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp₂
      (Real.rpow_nonneg (by linarith [ComponentGeometryBounds.nonneg g j i₀]) _))
      (norm_nonneg _)

/-- See Lemma 6.4 of the paper, the short-range auxiliary step on its existing
scalar form. A single unique unrestricted solution has the optimal value
profile, a summable value norm, and the full intrinsic energy bound for its
mean. The degree precedes the tolerance, prefactor and temperature interval.
The scalar gradient of the source is never required. -/
theorem short_auxiliary_estimates_internal (s : ShortExponent)
    (q : ℝ) (hq : 0 ≤ q) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ ε : ℝ, 0 < ε → ∀ A : ℝ, 1 ≤ A →
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ β ∈ Icc βlo βhi,
      ∀ (n : ℕ+) (X ι : Type*) [MeasurableSpace X] [Fintype ι] [DecidableEq ι]
        (ν : Measure X) [IsProbabilityMeasure ν]
        (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q →
        IsConservativeScalarForm Q → ∀ (g : ComponentGeometry ι)
        (M : X → Matrix ι ι ℝ), SummableCoerciveMatrix (ρ := ν) s n ε A q g M →
        ∀ (i₀ : ι) (χ : Lp ℝ 2 ν),
          (∃! v : ι → Q.1, WeightedWeakSolution Q (fun x => β • M x) ⊤
            (fun i => if i = i₀ then χ else 0) v) ∧
          (∀ v : ι → Q.1, WeightedWeakSolution Q (fun x => β • M x) ⊤
              (fun i => if i = i₀ then χ else 0) v →
            (∀ j, ‖(v j).val‖ ≤ C * (n : ℝ) ^ (κ * ε) *
              (1 + componentDistance g j i₀) ^ (-s.val) * ‖χ‖) ∧
            ((∑ j, ‖(v j).val‖) + Real.sqrt (Q.2 (∑ j, v j) (∑ j, v j)) ≤
              C * (n : ℝ) ^ (κ * ε) * ‖χ‖) ∧
            (‖(∑ j, v j).val‖ + Real.sqrt (Q.2 (∑ j, v j) (∑ j, v j)) ≤
              C * (n : ℝ) ^ (κ * ε) * ‖χ‖)) := by
  let a := s.val / 2
  have ha : 1 / 2 < a := by dsimp [a]; linarith [s.property]
  have has : a < s.val - 1 / 2 := by dsimp [a]; linarith [s.property]
  obtain ⟨r, hr, hdec⟩ := short_auxiliary_temperature_uniform_internal s.val a s.property ha has
  refine ⟨q * r, mul_nonneg hq hr, ?_⟩
  intro ε hε A hA βlo βhi hlo hhi
  obtain ⟨D, hD, hdec⟩ := hdec βlo βhi hlo hhi
  let K := Real.sqrt (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(2 * a)))
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  let C := (1 + K) * D * A ^ r
  have hC : 1 ≤ C := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (by linarith) hD) (Real.one_le_rpow hA hr)
  refine ⟨C, hC, ?_⟩
  intro β hβ n X ι _ _ _ ν _ Q hQ hcons g M hM i₀ χ
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by positivity
  have hB : 1 ≤ A * (n : ℝ) ^ (q * ε) :=
    one_le_mul_of_one_le_of_one_le hA (Real.one_le_rpow hn (mul_nonneg hq hε.le))
  have he := hdec β hβ X ι ν Q hQ hcons g
    (A * (n : ℝ) ^ (q * ε)) hB M hM.1 hM.2 i₀ χ
  have hfactor : D * (A * (n : ℝ) ^ (q * ε)) ^ r =
      (D * A ^ r) * (n : ℝ) ^ ((q * r) * ε) := by
    rw [Real.mul_rpow (by linarith : 0 ≤ A) (by positivity), ← Real.rpow_mul hn0.le]
    rw [show q * ε * r = q * r * ε by ring]
    ring
  have hlarge : D * A ^ r ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg hK (by positivity : 0 ≤ D * A ^ r)]
  refine ⟨he.1, ?_⟩
  intro v hv
  obtain ⟨hw, hp⟩ := he.2 v hv
  obtain ⟨hm, hS⟩ := short_mean_from_weighted_estimate_internal Q hQ g i₀ a
    (D * (A * (n : ℝ) ^ (q * ε)) ^ r * ‖χ‖) ha v hw
  rw [hfactor] at hp hm hS
  have hmean : K * ((D * A ^ r) * (n : ℝ) ^ ((q * r) * ε) * ‖χ‖) ≤
      C * (n : ℝ) ^ ((q * r) * ε) * ‖χ‖ := by
    have hcoef : K * (D * A ^ r) ≤ C := by
      dsimp [C]
      nlinarith [show 0 ≤ D * A ^ r by positivity]
    nlinarith [mul_le_mul_of_nonneg_right hcoef
      (by positivity : 0 ≤ (n : ℝ) ^ ((q * r) * ε) * ‖χ‖)]
  refine ⟨fun j => (hp j).trans ?_, hm.trans hmean, hS.trans hmean⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlarge (by positivity))
      (Real.rpow_nonneg (by linarith [ComponentGeometryBounds.nonneg g j i₀]) _))
    (norm_nonneg _)

/-- See Lemma 6.4 of the paper: the same maximum principle supplies the
physical tangent and unrestricted auxiliary supremum bounds. The component
subspace is arbitrary. In particular no coordinatewise maximum principle in
a nonorthogonal basis is assumed. -/
theorem point_source_ae_bound_internal {X ι : Type*} [MeasurableSpace X]
    [Fintype ι] [DecidableEq ι] {ν : Measure X}
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (M : X → Matrix ι ι ℝ) (hm : ∀ i j, Measurable (fun x => M x i j))
    (c : ℝ) (hc : 0 < c)
    (hM : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
      ∀ z : ι → ℝ, c * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j)
    (S : Submodule ℝ (ι → ℝ)) (i₀ : ι) (χ : Lp ℝ 2 ν) (B : ℝ) (hB : 0 ≤ B)
    (hχ : ∀ᵐ x ∂ν, |χ x| ≤ B) (v : ι → Q.1)
    (hv : WeightedWeakSolution Q M S (fun i => if i = i₀ then χ else 0) v) :
    (∀ᵐ x ∂ν, ‖(WithLp.toLp 2 (fun i => (v i).val x) : EuclideanSpace ℝ ι)‖ ≤ c⁻¹ * B) ∧
      (∀ i, ∀ᵐ x ∂ν, |(v i).val x| ≤ c⁻¹ * B) := by
  let R : ℝ≥0 := ⟨c⁻¹ * B, by positivity⟩
  have hsrc : ∀ᵐ x ∂ν, ‖(WithLp.toLp 2
      (fun i => (if i = i₀ then χ else 0 : Lp ℝ 2 ν) x) : EuclideanSpace ℝ ι)‖ ≤ c * R := by
    filter_upwards [hχ, Lp.coeFn_zero ℝ 2 ν] with x hx hz
    rw [PiLp.norm_eq_of_L2]
    simp only [apply_ite (fun f : Lp ℝ 2 ν => f x), hz, Pi.zero_apply, norm_zero,
      apply_ite norm, ite_pow, zero_pow (by omega : 2 ≠ 0), Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, Real.sqrt_sq (norm_nonneg _)]
    change |χ x| ≤ c * (c⁻¹ * B)
    simpa only [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] using hx
  have hb := MaximumPrinciple.Internal.bound_of_source_bound Q hQ M hm c hc hM
    S _ v hv R hsrc
  refine ⟨hb, fun i => hb.mono fun x hx => ?_⟩
  exact (show |(v i).val x| ≤ ‖(WithLp.toLp 2 (fun j => (v j).val x) :
    EuclideanSpace ℝ ι)‖ by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le
        (WithLp.toLp 2 (fun j => (v j).val x) : EuclideanSpace ℝ ι) i).trans hx

/-- See Lemma 6.4 of the paper, short-range comparison on the physical natural
carrier. The bounded auxiliary equation is transported along the existing
forgetful map to the scalar Sobolev product. Its form is constructed here.
The perturbation is the literal integral of the matrix difference. -/
theorem bounded_auxiliary_natural_comparison_internal {X : Type*}
    [MeasurableSpace X] {ν : Measure X}
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q) (n : ℕ+)
    (H : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (hH : ∀ᵐ x ∂ν, (H x).PosSemidef)
    (a : ℝ) (ha : 0 < a)
    (hlower : ∀ᵐ x ∂ν, ∀ z : Fin (n : ℕ) → ℝ,
      a * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * H x i j * z j)
    (M : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (hm : ∀ i j, Measurable (fun x => M x i j))
    (hb : ∃ B : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ B)
    (hM : ∀ᵐ x ∂ν, (M x).PosSemidef)
    (f : Fin (n : ℕ) → Lp ℝ 2 ν)
    (ψ v r : MatrixEnergy.Natural Q hQ H ⊤ hH)
    (hψ : WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ))) f
      (MatrixEnergy.tuple Q hQ H ⊤ hH ψ))
    (hv : WeightedWeakSolution Q M ⊤ f (MatrixEnergy.tuple Q hQ H ⊤ hH v))
    (hz : ∑ i, MatrixEnergy.tuple Q hQ H ⊤ hH (v - r) i = 0)
    (L τ R : ℝ) (hL : 0 ≤ L) (hτ : 0 ≤ τ) (hR : 0 ≤ R)
    (hpert : |∫ x, matrixFieldPair (fun x => H x - M x)
      (fun i => (MatrixEnergy.tuple Q hQ H ⊤ hH v i).val)
      (fun i => (MatrixEnergy.tuple Q hQ H ⊤ hH (v - r - ψ) i).val) x ∂ν| ≤
      L * ‖MatrixEnergy.values Q hQ H ⊤ hH (v - r - ψ)‖ + τ)
    (hr : MatrixEnergy.weakForm Q hQ H ⊤ hH r r ≤ R) :
    ‖MatrixEnergy.values Q hQ H ⊤ hH (ψ - v)‖ ≤
      2 * L / a + Real.sqrt ((2 * τ + R) / a) +
        ‖MatrixEnergy.values Q hQ H ⊤ hH r‖ := by
  let b : MatrixEnergy.Natural Q hQ H ⊤ hH →L[ℝ]
      MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ :=
    MatrixEnergy.base (ι := Fin (n : ℕ)) (κ := Fin (n : ℕ))
      (MatrixEnergy.vectorValue Q hQ) (fun x => CFC.sqrt (H x)) ⊤
  let A := (BoundedMatrixForms.form Q hQ M hm hb hM).bilinearComp b b
  have ht (w : MatrixEnergy.Natural Q hQ H ⊤ hH) :
      MatrixEnergy.vectorEquiv Q hQ (b w) = MatrixEnergy.tuple Q hQ H ⊤ hH w := rfl
  have haux (w : MatrixEnergy.Natural Q hQ H ⊤ hH) :
      A v w = ∑ i, inner ℝ (f i) (MatrixEnergy.tuple Q hQ H ⊤ hH w i).val := by
    change BoundedMatrixForms.form Q hQ M hm hb hM (b v) (b w) = _
    rw [BoundedMatrixForms.form_apply, ht, ht]
    exact (hv.2 (MatrixEnergy.tuple Q hQ H ⊤ hH w)
      ((BoundedMatrixForms.domain_iff Q M hm hb ⊤ _).mpr
        (ae_of_all _ fun _ => Submodule.mem_top))).2
  apply natural_tangent_comparison_internal Q hQ n H hH a ha hlower f ψ v r hψ hz
    A haux L τ R hL hτ hR _ hr
  have hdiff (w : MatrixEnergy.Natural Q hQ H ⊤ hH) :
      MatrixEnergy.weakForm Q hQ H ⊤ hH v w - A v w =
        ∫ x, matrixFieldPair (fun x => H x - M x)
          (fun i => (MatrixEnergy.tuple Q hQ H ⊤ hH v i).val)
          (fun i => (MatrixEnergy.tuple Q hQ H ⊤ hH w i).val) x ∂ν := by
    change MatrixEnergy.weakForm Q hQ H ⊤ hH v w -
      BoundedMatrixForms.form Q hQ M hm hb hM (b v) (b w) = _
    rw [MatrixEnergy.weakForm_apply, BoundedMatrixForms.form_apply, ht, ht]
    rw [add_sub_add_left_eq_sub, ← integral_sub
      (MatrixEnergy.integrable_pair Q hQ H ⊤ hH v w)
      (BoundedMatrixForms.integrable_pair M hm hb _ _)]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    simp only [matrixFieldPair, Matrix.sub_apply, mul_sub, sub_mul,
      Finset.sum_sub_distrib]
  rwa [hdiff]

/-- See Lemma 6.4 of the paper: a good-set coefficient bound and the squared
exceptional envelope of Subsection 6.1 prove actual integrability
and a first-moment exceptional bound. Only the exceptional weighted mass
is used. -/
theorem coefficient_first_moment_internal {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν]
    (Y : X → ℝ) (hY : Measurable Y) (G : Set X)
    (A K T : ℝ) (hK : 0 ≤ K)
    (hgood : ∀ᵐ x ∂ν.restrict G, |Y x| ≤ A)
    (W : X → ℝ) (hW : IntegrableOn W Gᶜ ν)
    (hsq : ∀ᵐ x ∂ν.restrict Gᶜ, Y x ^ 2 ≤ K * W x)
    (htail : (∫ x in Gᶜ, W x ∂ν) ≤ T) :
    Integrable Y ν ∧ IntegrableOn (fun x => |Y x|) Gᶜ ν ∧
      (∫ x in Gᶜ, |Y x| ∂ν) ≤ Real.sqrt (K * T) := by
  have hi : IntegrableOn (fun x => Y x ^ 2) Gᶜ ν :=
    (hW.const_mul K).mono' (hY.pow_const 2).aestronglyMeasurable
      (hsq.mono fun x hx => by simpa only [Real.norm_eq_abs, abs_sq] using hx)
  have hb : IntegrableOn Y Gᶜ ν := MomentEvent.integrable_of_integrable_sq hY hi
  have hg : IntegrableOn Y G ν :=
    (integrable_const A).mono' hY.aestronglyMeasurable
      (hgood.mono fun x hx => by simpa only [Real.norm_eq_abs] using hx)
  have hall : Integrable Y ν := by
    have hh := integrableOn_union.mpr ⟨hg, hb⟩
    simpa only [union_compl_self, integrableOn_univ] using hh
  have hmass : (∫ x in Gᶜ, Y x ^ 2 ∂ν) ≤ K * T := by
    calc
      _ ≤ ∫ x in Gᶜ, K * W x ∂ν := integral_mono_ae hi (hW.const_mul K) hsq
      _ = K * ∫ x in Gᶜ, W x ∂ν := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left htail hK
  have hi' : Integrable (fun x => Y x ^ 2) (ν.restrict Gᶜ) := hi
  have hcs := Riesz1.integral_on_event_le_second_moment
    (μ := ν.restrict Gᶜ) hY.abs.aestronglyMeasurable
    (fun x => abs_nonneg (Y x)) (by simpa only [sq_abs] using hi') MeasurableSet.univ
  simp only [setIntegral_univ, sq_abs, ← Real.sqrt_eq_rpow,
    measureReal_restrict_apply_univ] at hcs
  refine ⟨hall, hb.abs, ?_⟩
  apply hcs.trans
  have hp : Real.sqrt (ν.real Gᶜ) ≤ 1 := by
    exact (Real.sqrt_le_sqrt measureReal_le_one).trans_eq Real.sqrt_one
  exact (mul_le_of_le_one_right (Real.sqrt_nonneg _) hp).trans (Real.sqrt_le_sqrt hmass)

/-- See Lemma 6.4 of the paper: entrywise first moments of a matrix defect
bound its pairing with bounded fields. All matrix integrals are proved
integrable before the estimate is taken. The finite loss is exactly the
square of the number of components. -/
theorem matrix_defect_pairing_internal {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    {ν : Measure X} (D : X → Matrix ι ι ℝ)
    (hD : ∀ i j, Integrable (fun x => D x i j) ν)
    (u v : ι → Lp ℝ 2 ν) (U V T : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hu : ∀ i, ∀ᵐ x ∂ν, |u i x| ≤ U)
    (hv : ∀ j, ∀ᵐ x ∂ν, |v j x| ≤ V)
    (hT : ∀ i j, (∫ x, |D x i j| ∂ν) ≤ T) :
    |∫ x, matrixFieldPair D u v x ∂ν| ≤ (Fintype.card ι : ℝ) ^ 2 * U * V * T := by
  have hi := bounded_matrix_pair_integrable D hD u v U V hu hv
  have hsum : Integrable (fun x => ∑ i, ∑ j, |D x i j|) ν :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hD i j).abs
  have hpoint : ∀ᵐ x ∂ν, |matrixFieldPair D u v x| ≤
      (U * V) * ∑ i, ∑ j, |D x i j| := by
    filter_upwards [ae_all_iff.mpr hu, ae_all_iff.mpr hv] with x hx hy
    calc
      _ ≤ ∑ i, |∑ j, u i x * D x i j * v j x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |u i x * D x i j * v j x| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, (U * V) * |D x i j| := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_mul]
        have hh := mul_le_mul
          (mul_le_mul_of_nonneg_right (hx i) (abs_nonneg (D x i j))) (hy j)
          (abs_nonneg (v j x)) (mul_nonneg hU (abs_nonneg (D x i j)))
        nlinarith only [hh]
      _ = _ := by simp only [Finset.mul_sum]
  calc
    _ ≤ ∫ x, |matrixFieldPair D u v x| ∂ν := abs_integral_le_integral_abs
    _ ≤ ∫ x, (U * V) * ∑ i, ∑ j, |D x i j| ∂ν :=
      integral_mono_ae hi.abs (hsum.const_mul _) hpoint
    _ = (U * V) * ∑ i, ∑ j, ∫ x, |D x i j| ∂ν := by
      rw [integral_const_mul, integral_finsetSum]
      · congr 1
        apply Finset.sum_congr rfl
        intro i _
        exact integral_finsetSum _ fun j _ => (hD i j).abs
      · intro i _
        exact integrable_finsetSum _ fun j _ => (hD i j).abs
    _ ≤ (U * V) * ∑ _i : ι, ∑ _j : ι, T :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hT i j) (mul_nonneg hU hV)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- See Lemma 6.4 of the paper, the short-range physical normal row estimates.
The good-set summable entry profile and the exceptional square envelope
imply all coefficient integrability, the `O(n)` normal row sum on the good
set, and its weighted exceptional first moment. These are conclusions,
rather than separate analytic assumptions in the normal-energy step. -/
theorem short_physical_rows_internal {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    {ν : Measure X} [IsProbabilityMeasure ν]
    (s : ℝ) (hs : 1 < s) (g : ComponentGeometry ι)
    (H : X → Matrix ι ι ℝ) (hm : ∀ i j, Measurable (fun x => H x i j))
    (G : Set X) (B K T : ℝ) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hgood : ∀ᵐ x ∂ν.restrict G, ∀ i j,
      |H x i j| ≤ B * (1 + componentDistance g i j) ^ (-s))
    (W : X → ℝ) (hW : IntegrableOn W Gᶜ ν)
    (hsq : ∀ᵐ x ∂ν.restrict Gᶜ, ∀ i j, H x i j ^ 2 ≤ K * W x)
    (htail : (∫ x in Gᶜ, W x ∂ν) ≤ T) :
    (∀ i j, Integrable (fun x => H x i j) ν) ∧
      (∀ᵐ x ∂ν.restrict G, (∑ i, ∑ j, H x i j) ≤
        (B * (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s))) * (Fintype.card ι : ℝ)) ∧
      IntegrableOn (fun x => |∑ i, ∑ j, H x i j|) Gᶜ ν ∧
      (∫ x in Gᶜ, |∑ i, ∑ j, H x i j| ∂ν) ≤
        (Fintype.card ι : ℝ) ^ 2 * Real.sqrt (K * T) := by
  have hcoeff (i j : ι) := coefficient_first_moment_internal
    (fun x => H x i j) (hm i j) G B K T hK
    (hgood.mono fun x hx => (hx i j).trans
      (mul_le_of_le_one_right hB (Real.rpow_le_one_of_one_le_of_nonpos
        (by linarith [ComponentGeometryBounds.nonneg g i j]) (by linarith))))
    W hW (hsq.mono fun x hx => hx i j) htail
  have hsum : IntegrableOn (fun x => ∑ i, ∑ j, H x i j) Gᶜ ν :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hcoeff i j).1.restrict
  refine ⟨fun i j => (hcoeff i j).1, ?_, hsum.abs, ?_⟩
  · filter_upwards [hgood] with x hx
    have hh := InitialDecay.Internal.summable_quadratic_upper s hs g B hB
      (H x) hx (fun _ => 1)
    simpa only [one_mul, mul_one, one_pow, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] using hh
  · calc
      _ ≤ ∫ x in Gᶜ, ∑ i, ∑ j, |H x i j| ∂ν := by
        apply integral_mono_ae hsum.abs
          (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
            (hcoeff i j).2.1)
        exact ae_of_all _ fun x => (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ = ∑ i, ∑ j, ∫ x in Gᶜ, |H x i j| ∂ν := by
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro i _
          exact integral_finsetSum _ fun j _ => (hcoeff i j).2.1
        · intro i _
          exact integrable_finsetSum _ fun j _ => (hcoeff i j).2.1
      _ ≤ ∑ _i : ι, ∑ _j : ι, Real.sqrt (K * T) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => (hcoeff i j).2.2
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- See Lemma 6.4 of the paper, complete short-range energy comparison on one
scalar form. Both supremum bounds, physical energy-domain membership of
the auxiliary and its mean correction, and the exceptional perturbation
bound for the actual comparison field are proved here. The normal row
data can be supplied by `short_physical_rows_internal`. This internal
lemma retains explicit first moments, before exponential absorption. -/
theorem short_comparison_from_moments_internal {X : Type*} [MeasurableSpace X]
    {ν : Measure X} (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (n : ℕ+) (H M : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (hHm : ∀ i j, Measurable (fun x => H x i j))
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hMb : ∃ C : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ C)
    (hH : ∀ᵐ x ∂ν, (H x).PosSemidef) (hM : ∀ᵐ x ∂ν, (M x).PosSemidef)
    (a d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hHa : ∀ᵐ x ∂ν, (∀ i j, H x i j = H x j i) ∧
      ∀ z : Fin (n : ℕ) → ℝ, a * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * H x i j * z j)
    (hMd : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
      ∀ z : Fin (n : ℕ) → ℝ, d * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j)
    (hHi : ∀ i j, Integrable (fun x => H x i j) ν)
    (hDi : ∀ i j, Integrable (fun x => H x i j - M x i j) ν)
    (T : ℝ) (hT : 0 ≤ T)
    (hdefect : ∀ i j, (∫ x, |H x i j - M x i j| ∂ν) ≤ T)
    (G : Set X) (hG : MeasurableSet G) (K Tail : ℝ) (hK : 0 ≤ K) (hTail : 0 ≤ Tail)
    (hgood : ∀ᵐ x ∂ν.restrict G, (∑ i, ∑ j, H x i j) ≤ K)
    (hbad : IntegrableOn (fun x => |∑ i, ∑ j, H x i j|) Gᶜ ν)
    (hbadmass : (∫ x in Gᶜ, |∑ i, ∑ j, H x i j| ∂ν) ≤ Tail)
    (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν) (B : ℝ) (hB : 0 ≤ B)
    (hχ : ∀ᵐ x ∂ν, |χ x| ≤ B) (ψ v : Fin (n : ℕ) → Q.1)
    (hψ : WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ)))
      (fun i => if i = i₀ then χ else 0) ψ)
    (hv : WeightedWeakSolution Q M ⊤ (fun i => if i = i₀ then χ else 0) v) :
    let S : Q.1 := ∑ i, v i
    let V := d⁻¹ * B
    let U := 2 * V + a⁻¹ * B
    let R := (n : ℝ)⁻¹ * Q.2 S S + (n : ℝ)⁻¹ ^ 2 *
      (K * ‖S.val‖ ^ 2 + ((n : ℝ) * V) ^ 2 * Tail)
    ‖WithLp.toLp 2 (fun i => (ψ i).val - (v i).val)‖ ≤
      Real.sqrt ((2 * (n : ℝ) ^ 2 * V * U * T + R) / a) +
        (n : ℝ) ^ (-(1 : ℝ) / 2) * ‖S.val‖ := by
  intro S V U R
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hvB := (point_source_ae_bound_internal Q hQ M hMm d hd hMd ⊤ i₀ χ B hB hχ v hv).2
  have hψB := (point_source_ae_bound_internal Q hQ H hHm a ha hHa _ i₀ χ B hB hχ ψ hψ).2
  let r₀ : Q.1 := (n : ℝ)⁻¹ • S
  have hrB : ∀ᵐ x ∂ν, |r₀.val x| ≤ V := normal_component_bound_internal Q n v V hvB
  have hSB : ∀ᵐ x ∂ν, |S.val x| ≤ (n : ℝ) * V := by
    simpa only [S, Submodule.coe_sum, Fintype.card_fin] using
      PhysicalPerturbation.sum_ae_bound_internal (fun i => (v i).val) V hvB
  obtain ⟨ψN, hψN⟩ := MatrixEnergy.exists_tuple Q hQ H ⊤ hH hHm ψ
    ⟨ae_of_all _ fun _ => Submodule.mem_top, hψ.1.2⟩
  obtain ⟨vN, hvN⟩ := MatrixEnergy.exists_tuple Q hQ H ⊤ hH hHm v
    (bounded_tuple_physical_domain_internal Q H hHi v V hvB)
  obtain ⟨rN, hrN⟩ := MatrixEnergy.exists_tuple Q hQ H ⊤ hH hHm (fun _ => r₀)
    (bounded_tuple_physical_domain_internal Q H hHi _ V (fun _ => hrB))
  have hz : ∑ i, MatrixEnergy.tuple Q hQ H ⊤ hH (vN - rN) i = 0 := by
    simpa only [map_sub, Pi.sub_apply, hvN, hrN] using subtract_mean_sum_zero Q n v
  have hR : 0 ≤ R := by dsimp [R]; positivity [hQ.2.2.1 S]
  have hr := normal_energy_estimate_internal Q hQ n H hH S rN
    (fun i => congrFun hrN i) G hG K ((n : ℝ) * V) Tail hK hSB hgood hbad hbadmass
  have hu (i : Fin (n : ℕ)) : ∀ᵐ x ∂ν,
      |(MatrixEnergy.tuple Q hQ H ⊤ hH (vN - rN - ψN) i).val x| ≤ U := by
    have ht : MatrixEnergy.tuple Q hQ H ⊤ hH (vN - rN - ψN) i = v i - r₀ - ψ i := by
      simp only [map_sub, Pi.sub_apply, hvN, hrN, hψN]
    rw [ht]
    filter_upwards [hvB i, hrB, hψB i, Lp.coeFn_sub (v i).val r₀.val,
      Lp.coeFn_sub ((v i).val - r₀.val) (ψ i).val] with x hx hy hz hs ht
    change |((v i).val - r₀.val - (ψ i).val) x| ≤ U
    rw [ht]
    simp only [Pi.sub_apply]
    rw [hs]
    simp only [Pi.sub_apply]
    have hh := (abs_sub ((v i).val x - r₀.val x) ((ψ i).val x)).trans
      (add_le_add (abs_sub ((v i).val x) (r₀.val x)) le_rfl)
    dsimp only [U, V] at *
    linarith
  have hpert := matrix_defect_pairing_internal (fun x => H x - M x) hDi
    (fun i => (MatrixEnergy.tuple Q hQ H ⊤ hH vN i).val)
    (fun i => (MatrixEnergy.tuple Q hQ H ⊤ hH (vN - rN - ψN) i).val)
    V U T hV hU (fun i => by simpa only [hvN] using hvB i) hu hdefect
  have hh := bounded_auxiliary_natural_comparison_internal Q hQ n H hH a ha
    (hHa.mono fun x hx => hx.2) M hMm hMb hM _ ψN vN rN
    (by simpa only [hψN] using hψ) (by simpa only [hvN] using hv) hz
    0 ((n : ℝ) ^ 2 * V * U * T) R le_rfl (by positivity) hR
    (by simpa only [Fintype.card_fin, zero_mul, zero_add] using hpert) hr
  have he : MatrixEnergy.values Q hQ H ⊤ hH (ψN - vN) =
      WithLp.toLp 2 (fun i => (ψ i).val - (v i).val) := by
    apply PiLp.ext
    intro i
    simp only [map_sub, PiLp.sub_apply, MatrixEnergy.values_apply,
      hψN, hvN]
  have her : MatrixEnergy.values Q hQ H ⊤ hH rN =
      WithLp.toLp 2 (fun _i : Fin (n : ℕ) => r₀.val) := by
    apply PiLp.ext
    intro i
    simp only [MatrixEnergy.values_apply, hrN]
  rw [he, her, normal_value_norm Q n S] at hh
  simpa only [mul_zero, zero_div, zero_add, mul_assoc] using hh

/-- See Lemma 6.4 of the paper, the short-range cutoff defect. A bounded
matrix agreeing with the physical matrix on the good set differs from it
by an integrable field whose entire first moment is controlled by the
weighted exceptional mass. This includes the prescribed identity cutoff
of Subsection 6.1, without introducing a new matrix definition. -/
theorem cutoff_defect_first_moment_internal {X ι : Type*} [MeasurableSpace X]
    [Fintype ι] {ν : Measure X} [IsProbabilityMeasure ν]
    (H M : X → Matrix ι ι ℝ)
    (hHm : ∀ i j, Measurable (fun x => H x i j))
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (G : Set X) (hG : MeasurableSet G) (D K T : ℝ) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hMb : ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ D)
    (heq : ∀ᵐ x ∂ν, x ∈ G → H x = M x)
    (W : X → ℝ) (hW : IntegrableOn W Gᶜ ν)
    (hW1 : ∀ᵐ x ∂ν.restrict Gᶜ, 1 ≤ W x)
    (hsq : ∀ᵐ x ∂ν.restrict Gᶜ, ∀ i j, H x i j ^ 2 ≤ K * W x)
    (htail : (∫ x in Gᶜ, W x ∂ν) ≤ T) :
    (∀ i j, Integrable (fun x => H x i j) ν) ∧
      (∀ i j, Integrable (fun x => H x i j - M x i j) ν) ∧
      (∀ i j, (∫ x, |H x i j - M x i j| ∂ν) ≤ Real.sqrt (K * T) + D * T) := by
  have hmass : ν.real Gᶜ ≤ T := by
    calc
      _ = ∫ _x in Gᶜ, (1 : ℝ) ∂ν := by simp only [setIntegral_const, smul_eq_mul, mul_one]
      _ ≤ ∫ x in Gᶜ, W x ∂ν := integral_mono_ae (integrable_const 1) hW hW1
      _ ≤ T := htail
  have hcoeff (i j : ι) := coefficient_first_moment_internal (fun x => H x i j)
    (hHm i j) G D K T hK
    (by
      filter_upwards [ae_restrict_of_ae hMb, ae_restrict_of_ae heq, ae_restrict_mem hG]
        with x hb he hx
      rw [he hx]
      exact hb i j)
    W hW (hsq.mono fun x hx => hx i j) htail
  have hMi (i j : ι) : Integrable (fun x => M x i j) ν :=
    (integrable_const D).mono' (hMm i j).aestronglyMeasurable
      (hMb.mono fun x hx => by simpa only [Real.norm_eq_abs] using hx i j)
  have hDi (i j : ι) : Integrable (fun x => H x i j - M x i j) ν :=
    (hcoeff i j).1.sub (hMi i j)
  refine ⟨fun i j => (hcoeff i j).1, hDi, ?_⟩
  intro i j
  have hs : (∫ x in Gᶜ, |H x i j - M x i j| ∂ν) =
      ∫ x, |H x i j - M x i j| ∂ν :=
    setIntegral_eq_integral_of_ae_compl_eq_zero (heq.mono fun x hx hn => by
      have hxG : x ∈ G := by simpa only [mem_compl_iff, not_not] using hn
      rw [hx hxG, sub_self, abs_zero])
  rw [← hs]
  calc
    _ ≤ ∫ x in Gᶜ, |H x i j| + D ∂ν := by
      apply integral_mono_ae (hDi i j).abs.restrict
        ((hcoeff i j).2.1.add (integrable_const D))
      filter_upwards [ae_restrict_of_ae hMb] with x hx
      change |H x i j - M x i j| ≤ |H x i j| + D
      exact (abs_sub (H x i j) (M x i j)).trans (add_le_add le_rfl (hx i j))
    _ = (∫ x in Gᶜ, |H x i j| ∂ν) + ν.real Gᶜ * D := by
      rw [integral_add (hcoeff i j).2.1 (integrable_const D), setIntegral_const, smul_eq_mul]
    _ ≤ Real.sqrt (K * T) + D * T := by
      have hh := mul_le_mul_of_nonneg_right hmass hD
      nlinarith only [(hcoeff i j).2.2, hh]

/-- See Lemma 6.4 of the paper, short-range local comparison from coefficients.
The only upper estimates are the good-set entry profile and the exceptional
square envelope. All integrability, normal row moments, supremum factors and
the test-field perturbation estimate are discharged by the preceding lemmas.
The remaining mean norms are the actual scalar-form sum of the auxiliary
solution, to which `short_auxiliary_estimates_internal` applies. -/
theorem short_comparison_from_coefficients_internal {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν]
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (s : ℝ) (hs : 1 < s) (n : ℕ+) (g : ComponentGeometry (Fin (n : ℕ)))
    (H M : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (hHm : ∀ i j, Measurable (fun x => H x i j))
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hH : ∀ᵐ x ∂ν, (H x).PosSemidef) (hM : ∀ᵐ x ∂ν, (M x).PosSemidef)
    (a d : ℝ) (ha : 0 < a) (hd : 0 < d)
    (hHa : ∀ᵐ x ∂ν, (∀ i j, H x i j = H x j i) ∧
      ∀ z : Fin (n : ℕ) → ℝ, a * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * H x i j * z j)
    (hMd : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
      ∀ z : Fin (n : ℕ) → ℝ, d * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j)
    (G : Set X) (hG : MeasurableSet G) (D P K T : ℝ)
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hK : 0 ≤ K) (hT : 0 ≤ T)
    (hMb : ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ D)
    (heq : ∀ᵐ x ∂ν, x ∈ G → H x = M x)
    (hgood : ∀ᵐ x ∂ν.restrict G, ∀ i j,
      |H x i j| ≤ P * (1 + componentDistance g i j) ^ (-s))
    (W : X → ℝ) (hW : IntegrableOn W Gᶜ ν)
    (hW1 : ∀ᵐ x ∂ν.restrict Gᶜ, 1 ≤ W x)
    (hsq : ∀ᵐ x ∂ν.restrict Gᶜ, ∀ i j, H x i j ^ 2 ≤ K * W x)
    (htail : (∫ x in Gᶜ, W x ∂ν) ≤ T)
    (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν) (B : ℝ) (hB : 0 ≤ B)
    (hχ : ∀ᵐ x ∂ν, |χ x| ≤ B) (ψ v : Fin (n : ℕ) → Q.1)
    (hψ : WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ)))
      (fun i => if i = i₀ then χ else 0) ψ)
    (hv : WeightedWeakSolution Q M ⊤ (fun i => if i = i₀ then χ else 0) v) :
    let S : Q.1 := ∑ i, v i
    let V := d⁻¹ * B
    let U := 2 * V + a⁻¹ * B
    let R := (n : ℝ)⁻¹ * Q.2 S S + (n : ℝ)⁻¹ ^ 2 *
      ((P * (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s)) * (n : ℝ)) * ‖S.val‖ ^ 2 +
        ((n : ℝ) * V) ^ 2 * ((n : ℝ) ^ 2 * Real.sqrt (K * T)))
    ‖WithLp.toLp 2 (fun i => (ψ i).val - (v i).val)‖ ≤
      Real.sqrt ((2 * (n : ℝ) ^ 2 * V * U * (Real.sqrt (K * T) + D * T) + R) / a) +
        (n : ℝ) ^ (-(1 : ℝ) / 2) * ‖S.val‖ := by
  have hr := short_physical_rows_internal s hs g H hHm G P K T hP hK hgood W hW hsq htail
  have hc := cutoff_defect_first_moment_internal H M hHm hMm G hG D K T
    hD hK hMb heq W hW hW1 hsq htail
  have hh := short_comparison_from_moments_internal Q hQ n H M hHm hMm ⟨D, hMb⟩
    hH hM a d ha hd hHa hMd hr.1 hc.2.1 (Real.sqrt (K * T) + D * T) (by positivity)
    hc.2.2 G hG (P * (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s)) * (n : ℝ))
    ((n : ℝ) ^ 2 * Real.sqrt (K * T)) (by positivity) (by positivity)
    (by simpa only [Fintype.card_fin] using hr.2.1) hr.2.2.1
    (by simpa only [Fintype.card_fin] using hr.2.2.2) i₀ χ B hB hχ ψ v hψ hv
  exact hh

end Riesz2.FixedLengthDecay
