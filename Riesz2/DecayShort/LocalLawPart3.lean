/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.LocalLawPart2
public import Riesz2.ToMathlib.StretchedCutoffRates
public import Riesz2.ToMathlib.CyclicIntervals

/-!
# Uniform short-range local law and point-fibre curvature

The finite-scale concentration estimate is applied with a power cutoff.
The constants precede the volume, retained set and temperature throughout.
When only one exterior gap remains, the upper marginal is twice
continuously differentiable and has the classical curvature bound.
-/

public section
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace Riesz2.DecayShort
namespace LocalLawInternal

/-- Power-cutoff assembly for Lemma B.1, in arbitrary
retained-label charts, uniformly for all temperatures above a positive bound. -/
theorem shortRange_uniform_chart (s βlo η : ℝ) (hs : 1 < s)
    (hβlo : 0 < βlo) (hη : 0 < η) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (p : Parameters), p.val.2 = s → βlo ≤ p.val.1 →
      ∀ (n m : ℕ), 1 ≤ n → ∀ (σ : Equiv.Perm (Fin (n + m + 1))),
        let J := Finset.univ.image (fun j : Fin n => σ (j.castAdd m).castSucc)
        (gibbsMeasure p (n + m).succPNat)
          {X | (n : ℝ) ^ (1 / 2 + η) ≤ |(∑ i ∈ J, gap X i.val) - (n : ℝ)|} ≤
            ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ (η / (4 * (s + 2))))) := by
  obtain ⟨B, hB, hfinite⟩ := shortRange_finite_scale
  let δ := η / (2 * (s + 2))
  let q := η / (4 * (s + 2))
  let a := Real.log 2 / 8
  have hδ : 0 < δ := div_pos hη (by linarith)
  have hq : 0 < q := div_pos hη (by linarith)
  have ha : 0 < a := div_pos (Real.log_pos one_lt_two) (by norm_num)
  obtain ⟨K, hK, hsmall⟩ := StretchedCutoff.eventual_small hδ ha hB.le (1 / 2 + η)
  have hqδ : q ≤ δ := by dsimp [q, δ]; apply div_le_div_of_nonneg_left hη.le <;> linarith
  have hqr : q ≤ 3 * η / 2 := by
    dsimp [q]
    apply (div_le_iff₀ (by linarith : 0 < 4 * (s + 2))).mpr
    nlinarith
  obtain ⟨D, c, hD, hc, hsum⟩ := StretchedCutoff.sum_bound hq hqδ hqr ha
    (div_pos hβlo (by norm_num : (0 : ℝ) < 8))
  refine ⟨max D (Real.exp (c * K ^ q)), c,
    lt_of_lt_of_le hD (le_max_left _ _), hc, ?_⟩
  intro p hps hpl n m hn σ J
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hp : 1 < p.val.2 := by rwa [hps]
  by_cases hlarge : K ≤ (n : ℝ)
  · let R : {R : ℝ // 0 < R} := ⟨(n : ℝ) ^ δ, Real.rpow_pos_of_pos hn0 _⟩
    have hR : 1 ≤ (R : ℝ) := Real.one_le_rpow hn1 hδ.le
    obtain ⟨he, hm⟩ := hsmall n hlarge
    have h := hfinite p hp n m hn σ R hR ((n : ℝ) ^ (1 / 2 + η))
      (Real.rpow_pos_of_pos hn0 _) he hm
    have hpower : (R : ℝ) ^ (-p.val.2 - 2) * ((n : ℝ) ^ (1 / 2 + η)) ^ 2 /
        (n : ℝ) = (n : ℝ) ^ (3 * η / 2) := by
      dsimp only [R]
      rw [hps, ← Real.rpow_mul hn0.le, ← Real.rpow_natCast,
        ← Real.rpow_mul hn0.le, ← Real.rpow_add hn0, div_eq_mul_inv,
        ← Real.rpow_neg_one, ← Real.rpow_add hn0]
      congr 1
      dsimp [δ]
      field_simp
      ring
    have hexponent : -(p.val.1 * (R : ℝ) ^ (-p.val.2 - 2)) *
        ((n : ℝ) ^ (1 / 2 + η)) ^ 2 / (8 * n) =
          -(p.val.1 / 8) * (n : ℝ) ^ (3 * η / 2) := by
      rw [show -(p.val.1 * (R : ℝ) ^ (-p.val.2 - 2)) *
        ((n : ℝ) ^ (1 / 2 + η)) ^ 2 / (8 * n) =
        -(p.val.1 / 8) * ((R : ℝ) ^ (-p.val.2 - 2) *
          ((n : ℝ) ^ (1 / 2 + η)) ^ 2 / n) by ring, hpower]
    change (gibbsMeasure p (n + m).succPNat) _ ≤
      ENNReal.ofReal (2 * Real.exp _ + 3 * n * Real.exp (-a * (n : ℝ) ^ δ)) at h
    rw [hexponent] at h
    apply h.trans
    apply ENNReal.ofReal_le_ofReal
    have htemp : Real.exp (-(p.val.1 / 8) * (n : ℝ) ^ (3 * η / 2)) ≤
        Real.exp (-(βlo / 8) * (n : ℝ) ^ (3 * η / 2)) := by
      apply Real.exp_le_exp.mpr
      have hn' := Real.rpow_nonneg hn0.le (3 * η / 2)
      nlinarith
    have hbound := hsum n hn1
    have hC := mul_le_mul_of_nonneg_right
      (le_max_left D (Real.exp (c * K ^ q))) (Real.exp_pos (-c * (n : ℝ) ^ q)).le
    change _ ≤ max D (Real.exp (c * K ^ q)) * Real.exp (-c * (n : ℝ) ^ q)
    calc
      _ ≤ 2 * Real.exp (-(βlo / 8) * (n : ℝ) ^ (3 * η / 2)) +
          3 * n * Real.exp (-a * (n : ℝ) ^ δ) := by gcongr
      _ ≤ _ := hbound.trans hC
  · have := gibbsMeasure_probability p (n + m).succPNat
    apply (prob_le_one (μ := gibbsMeasure p (n + m).succPNat)).trans
    apply (ENNReal.ofReal_one.symm.le).trans
    apply ENNReal.ofReal_le_ofReal
    have hpow := Real.rpow_le_rpow hn0.le (le_of_not_ge hlarge) hq.le
    have hmul : (1 : ℝ) ≤ Real.exp (c * K ^ q) * Real.exp (-c * (n : ℝ) ^ q) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      nlinarith
    exact hmul.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)

end LocalLawInternal

set_option backward.isDefEq.respectTransparency false in
/-- See Lemma B.1 of the paper: uniform local law for every nonempty
proper set of gaps. In particular this includes every cyclic block of length
at most half the volume. The constants are uniform on each positive compact
temperature interval (and the upper endpoint is not needed for this bound). -/
theorem shortRange_localLaw_sets (s βlo βhi η : ℝ) (hs : 1 < s)
    (hβlo : 0 < βlo) (_hβhi : βlo ≤ βhi) (hη : 0 < η) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (p : Parameters), p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ J : Finset (Fin (N : ℕ)),
        1 ≤ J.card → J.card < (N : ℕ) →
        (gapLaw p N) {x | (J.card : ℝ) ^ (1 / 2 + η) ≤
          |(∑ i ∈ J, x i) - (J.card : ℝ)|} ≤
            ENNReal.ofReal (C * Real.exp (-c * (J.card : ℝ) ^ (η / (4 * (s + 2))))) := by
  classical
  obtain ⟨C, c, hC, hc, hchart⟩ :=
    LocalLawInternal.shortRange_uniform_chart s βlo η hs hβlo hη
  refine ⟨C, c, hC, hc, ?_⟩
  intro p hps hpl _ N _ J hn hlt
  obtain ⟨m, hNm⟩ : ∃ m : ℕ, (N : ℕ) = J.card + m + 1 :=
    ⟨(N : ℕ) - J.card - 1, by omega⟩
  generalize hcard : J.card = n at *
  have hN : N = (n + m).succPNat := PNat.coe_injective hNm
  subst N
  let e : Fin n ↪ Fin (n + m + 1) :=
    ⟨fun i => ((J.orderIsoOfFin hcard) i).val, fun i j hij =>
      (J.orderIsoOfFin hcard).injective (Subtype.ext hij)⟩
  obtain ⟨σ, hσ⟩ := RetainedSimplex.exists_chart_labels n m e
  have hJ : Finset.univ.image (fun j : Fin n => σ (j.castAdd m).castSucc) = J := by
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, rfl⟩
      rw [hσ]
      exact ((J.orderIsoOfFin hcard) j).property
    · intro hi
      refine ⟨(J.orderIsoOfFin hcard).symm ⟨i, hi⟩, ?_⟩
      rw [hσ]
      exact congrArg Subtype.val ((J.orderIsoOfFin hcard).apply_symm_apply ⟨i, hi⟩)
  have h := hchart p hps hpl n m hn σ
  dsimp only at h
  rw [hJ] at h
  have hA : MeasurableSet {x : Fin (n + m + 1) → ℝ |
      (n : ℝ) ^ (1 / 2 + η) ≤ |(∑ i ∈ J, x i) - (n : ℝ)|} :=
    measurableSet_le measurable_const
      (((Finset.measurable_sum J (fun i _ => measurable_pi_apply i)).sub measurable_const).abs)
  have hgap : Measurable (@gapVector (n + m).succPNat) :=
    measurable_pi_iff.mpr (fun i => Riesz1.measurable_gap i.val)
  have he := Measure.map_apply (μ := gibbsMeasure p (n + m).succPNat) hgap hA
  change (gapLaw p (n + m).succPNat) _ = _ at he
  exact he.le.trans h

/-- See Lemma B.1 of the paper, the complete cyclic block range, with
constants chosen before the volume, block length, starting label and temperature. -/
theorem shortRange_localLaw (s βlo βhi η : ℝ) (hs : 1 < s)
    (hβlo : 0 < βlo) (hβhi : βlo ≤ βhi) (hη : 0 < η) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (p : Parameters), p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ k : ℕ, 1 ≤ k → k ≤ (N : ℕ) / 2 →
      ∀ a : ℤ,
        (gapLaw p N) {x | (k : ℝ) ^ (1 / 2 + η) ≤
          |(∑ i ∈ cyclicInterval N a k, x i) - (k : ℝ)|} ≤
            ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ (η / (4 * (s + 2))))) := by
  obtain ⟨C, c, hC, hc, hsets⟩ := shortRange_localLaw_sets s βlo βhi η hs hβlo hβhi hη
  refine ⟨C, c, hC, hc, ?_⟩
  intro p hps hpl hph N hN k hk hkN a
  have hcard := card_cyclicInterval (N := N) a (show k ≤ (N : ℕ) by omega)
  simpa only [hcard] using hsets p hps hpl hph N hN (cyclicInterval N a k)
    (by rwa [hcard]) (by rw [hcard]; omega)


set_option backward.isDefEq.respectTransparency false in
/-- See the proof of Lemma B.1 in the paper, classical regularity when the
exterior contains a single gap. The fibre has dimension zero, including
`N = 2`, and its density is the actual physical fibre mass. -/
theorem upperTilt_singleExterior_contDiff (p : Parameters) (hs : 1 < p.val.2)
    (n : ℕ) (hn : 1 ≤ n) (σ : Equiv.Perm (Fin (n + 0 + 1)))
    (θ : PhysicalCutoff) (R : {R : ℝ // 0 < R}) (hR : 1 ≤ (R : ℝ)) :
    let J := Finset.univ.image (fun j : Fin n => σ (j.castAdd 0).castSucc)
    let D := ProperMarginalChart.penalizedChartDensity p n 0 σ θ R.val⁻¹ J false
    ContDiffOn ℝ 2 (fun x => -Real.log (AffineFibre.fibreMass volume D x).toReal)
      (AffineSimplex.chartDomain n ((n + 0 : ℕ) + 1)) := by
  classical
  intro J D
  let N := (n + 0).succPNat
  let U := AffineSimplex.chartDomain n ((n + 0 : ℕ) + 1)
  let T := fun x : EuclideanSpace ℝ (Fin n) =>
    RetainedSimplex.chart n 0 ((n + 0 : ℕ) + 1) σ (x, 0)
  obtain ⟨W, hW, hval, _⟩ := upperGapPenalty_sub_quadratic_convex p hs N
    (by change 2 ≤ n + 0 + 1; omega) θ R hR J
  let A := fun x : EuclideanSpace ℝ (Fin n) =>
    p.val.1 * (W (T x) + ∑ i : Fin n, θ.val (x i / R))
  have hT : ContDiff ℝ 2 T := by
    have hchart : ContDiff ℝ 2 (AffineSimplex.chart (n + 0) ((n + 0 : ℕ) + 1)) := by
      have he : AffineSimplex.chart (n + 0) ((n + 0 : ℕ) + 1) = fun x =>
          (AffineSimplex.tangentMap (n + 0)).toContinuousLinearMap x +
            AffineSimplex.chart (n + 0) ((n + 0 : ℕ) + 1) 0 := by
        funext x
        exact AffineSimplex.chart_eq_tangentMap_add _ _ _
      rw [he]
      exact (AffineSimplex.tangentMap (n + 0)).toContinuousLinearMap.contDiff.add contDiff_const
    exact (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ).contDiff.comp
      (hchart.comp ((RetainedSimplex.join n 0).toContinuousLinearEquiv.contDiff.comp
        (contDiff_id.prodMk contDiff_const)))
  have hmem (x) (hx : x ∈ U) : T x ∈ AffineSimplex.massSimplex (n + 0) ((n + 0 : ℕ) + 1) := by
    apply (RetainedSimplex.chart_mem_simplex n 0 _ σ (x, 0)).mpr
    rw [RetainedSimplex.mem_domain]
    exact ⟨hx.1, by simp, by simpa using hx.2⟩
  have hamb (x) (hx : x ∈ U) : T x ∈ gapAmbientDomain N := by
    apply PhysicalEnergy.simplex_subset_ambient N (WithLp.ofLp (T x))
    exact ⟨(hmem x hx).1, by
      change ∑ i, T x i = ((n + 0 + 1 : ℕ) : ℝ)
      simpa only [Nat.cast_add, Nat.cast_one] using (hmem x hx).2⟩
  have hA : ContDiffOn ℝ 2 A U := by
    apply contDiffOn_const.mul
    apply ContDiffOn.add
    · exact (hW.of_le (by norm_num)).comp hT.contDiffOn hamb
    · apply ContDiffOn.sum
      intro i _
      exact (θ.property.1.of_le (by norm_num)).comp
        ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.div_const R.val).contDiffOn
        (fun x hx => div_nonneg (hx.1 i).le R.property.le)
  have he (x) (hx : x ∈ U) : -Real.log (AffineFibre.fibreMass volume D x).toReal = A x := by
    have hdom : (x, (0 : EuclideanSpace ℝ (Fin 0))) ∈
        RetainedSimplex.domain n 0 ((n + 0 : ℕ) + 1) := by
      rw [RetainedSimplex.mem_domain]
      exact ⟨hx.1, by simp, by simpa using hx.2⟩
    have hpen : (∑ i ∈ J, θ.val (R.val⁻¹ * T x i)) = ∑ i : Fin n, θ.val (x i / R) := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro i _
        rw [RetainedSimplex.chart_retained]
        simp only [div_eq_mul_inv, mul_comm]
      · intro i _ j _ hij
        exact Fin.ext (congrArg (fun k : Fin (n + 0 + 1) => k.val) (σ.injective hij))
    change -Real.log (∫⁻ z, D (x, z)).toReal = _
    rw [volume_euclideanSpace_eq_dirac, lintegral_dirac]
    change -Real.log ((RetainedSimplex.domain n 0 ((n + 0 : ℕ) + 1)).indicator
      (fun q => ProperMarginalChart.penalizedDensity p (n + 0) θ R.val⁻¹ J false
        (RetainedSimplex.chart n 0 ((n + 0 : ℕ) + 1) σ q)) (x, 0)).toReal = _
    rw [indicator_of_mem hdom]
    simp only [ProperMarginalChart.penalizedDensity, ProperMarginalChart.density,
      Bool.false_eq_true, ↓reduceIte, add_zero]
    erw [dite_eq_left (hmem x hx)]
    erw [← hval ⟨T x, hamb x hx⟩]
    erw [hpen, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
      ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.log_exp]
    dsimp only [A]
    ring
  exact hA.congr (fun x hx => he x hx)

set_option backward.isDefEq.respectTransparency false in
/-- See the proof of Lemma B.1 in the paper, the classical marginal Hessian
bound for every retained set with exactly one exterior gap. -/
theorem upperTilt_singleExterior_hessian (p : Parameters) (hs : 1 < p.val.2)
    (n : ℕ) (hn : 1 ≤ n) (σ : Equiv.Perm (Fin (n + 0 + 1)))
    (θ : PhysicalCutoff) (R : {R : ℝ // 0 < R}) (hR : 1 ≤ (R : ℝ)) :
    let J := Finset.univ.image (fun j : Fin n => σ (j.castAdd 0).castSucc)
    let D := ProperMarginalChart.penalizedChartDensity p n 0 σ θ R.val⁻¹ J false
    let V := fun x => -Real.log (AffineFibre.fibreMass volume D x).toReal
    ContDiffOn ℝ 2 V (AffineSimplex.chartDomain n ((n + 0 : ℕ) + 1)) ∧
      ∀ x ∈ AffineSimplex.chartDomain n ((n + 0 : ℕ) + 1),
        ∀ v : EuclideanSpace ℝ (Fin n),
          p.val.1 * (R : ℝ) ^ (-p.val.2 - 2) * ‖v‖ ^ 2 ≤
            fderiv ℝ (fderiv ℝ V) x v v := by
  intro J D V
  let U := AffineSimplex.chartDomain n ((n + 0 : ℕ) + 1)
  let a := p.val.1 * (R : ℝ) ^ (-p.val.2 - 2)
  let Q := fun x : EuclideanSpace ℝ (Fin n) => a / 2 * ‖x‖ ^ 2
  have hV : ContDiffOn ℝ 2 V U := upperTilt_singleExterior_contDiff p hs n hn σ θ R hR
  have hQ : ContDiff ℝ 2 Q := contDiff_const.mul (contDiff_norm_sq ℝ)
  have ho : IsOpen U := AffineSimplex.isOpen_chartDomain _ _
  refine ⟨hV, ?_⟩
  intro x hx v
  have hc : ConvexOn ℝ U (fun x => V x - Q x) :=
    upperTilt_marginal_residual_convex p hs n 0 hn σ θ R hR
  have hnonneg := Riesz1.fderiv_fderiv_nonneg_of_convexOn ho hc.1 hc
    (hV.sub hQ.contDiffOn) hx v
  have heq : fderiv ℝ (fun x => V x - Q x) =ᶠ[𝓝 x]
      fun z => fderiv ℝ V z - fderiv ℝ Q z := by
    filter_upwards [ho.mem_nhds hx] with z hz
    exact fderiv_fun_sub
      ((hV.differentiableOn (by norm_num)).differentiableAt (ho.mem_nhds hz))
      (hQ.differentiable (by norm_num)).differentiableAt
  have hVD : DifferentiableAt ℝ (fderiv ℝ V) x :=
    ((hV.fderiv_of_isOpen ho (by norm_num : 1 + 1 ≤ (2 : WithTop ℕ∞))).differentiableOn
      (by norm_num)).differentiableAt (ho.mem_nhds hx)
  have hQD : DifferentiableAt ℝ (fderiv ℝ Q) x :=
    (((hQ.contDiffOn (s := Set.univ)).fderiv_of_isOpen isOpen_univ
      (by norm_num : 1 + 1 ≤ (2 : WithTop ℕ∞))).differentiableOn
        (by norm_num)).differentiableAt (isOpen_univ.mem_nhds (Set.mem_univ x))
  rw [heq.fderiv_eq, fderiv_fun_sub hVD hQD] at hnonneg
  have hfirst : fderiv ℝ Q = fun z => a • innerSL ℝ z := by
    funext z
    rw [((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_mul (a / 2)).fderiv]
    ext u
    simp only [smul_apply, smul_eq_mul, two_smul, add_apply]
    ring
  have hsecond : fderiv ℝ (fderiv ℝ Q) x v v = a * ‖v‖ ^ 2 := by
    rw [hfirst]
    erw [((innerSL ℝ).hasFDerivAt (x := x) |>.const_smul a).fderiv]
    change a * innerSL ℝ v v = a * ‖v‖ ^ 2
    congr 1
    exact real_inner_self_eq_norm_sq v
  simp only [sub_apply, sub_nonneg] at hnonneg
  rw [hsecond] at hnonneg
  exact hnonneg

/-- See Lemma B.1 of the paper, all clauses: the local law over the
entire cyclic block range, uniform one-gap tails, and every positive and
inverse moment with both inequalities of the moment estimate. -/
theorem shortRange_localLaw_complete (s βlo βhi η : ℝ) (hs : 1 < s)
    (hβlo : 0 < βlo) (hβhi : βlo ≤ βhi) (hη : 0 < η) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      (∀ (p : Parameters), p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
        ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ k : ℕ, 1 ≤ k → k ≤ (N : ℕ) / 2 →
        ∀ a : ℤ,
          (gapLaw p N) {x | (k : ℝ) ^ (1 / 2 + η) ≤
            |(∑ i ∈ cyclicInterval N a k, x i) - (k : ℝ)|} ≤
              ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ (η / (4 * (s + 2)))))) ∧
      (∃ Ct ct : ℝ, 0 < Ct ∧ 0 < ct ∧
        ∀ (p : Parameters), p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
          ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ j : ℤ,
          (∀ u : ℝ, 0 < u → u ≤ 1 →
            (gibbsMeasure p N) {X | gap X j ≤ u} ≤
              ENNReal.ofReal (Ct * Real.exp (-ct * u ^ (-s)))) ∧
          (∀ u : ℝ, 1 ≤ u →
            (gibbsMeasure p N) {X | u ≤ gap X j} ≤
              ENNReal.ofReal (Ct * Real.exp (-ct * u)))) ∧
      ∀ r : ℝ, 0 < r → ∃ Cr : ℝ, 0 < Cr ∧
        ∀ (p : Parameters), p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
          ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ j : ℤ, ∀ q : ℝ, 1 ≤ q →
          eLpNorm (fun X : Riesz1.Configuration N => gap X j ^ r)
              (ENNReal.ofReal q) (gibbsMeasure p N) +
            eLpNorm (fun X : Riesz1.Configuration N => gap X j ^ (-r))
              (ENNReal.ofReal q) (gibbsMeasure p N) ≤
                ENNReal.ofReal (Cr * (q ^ r + q ^ (r / s))) ∧
          Cr * (q ^ r + q ^ (r / s)) ≤ 2 * Cr * q ^ (max r (r / s)) := by
  obtain ⟨C, c, hC, hc, hlocal⟩ := shortRange_localLaw s βlo βhi η hs hβlo hβhi hη
  obtain ⟨Ct, ct, hCt, hct, ht, hm⟩ := SingleGapTails.single_gap_tails s βlo βhi
    (zero_lt_one.trans hs) (ne_of_gt hs) hβlo hβhi
  exact ⟨C, c, hC, hc, hlocal, ⟨Ct, ct, hCt, hct, ht⟩, hm⟩

end Riesz2.DecayShort
