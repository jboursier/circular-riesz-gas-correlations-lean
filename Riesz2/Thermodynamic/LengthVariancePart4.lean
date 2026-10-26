/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.LengthVariancePart3

/-!
# Active length: physical score identities and variance bounds

See the proof of Lemma 6.5 in the paper, under the literal two-sided tilt. The physical
score has a finite second moment independently of the score identities. The collision
flux is differentiable across the boundary, and the normalized simplex chart transports
both identities to the particle law. The expected curvature then gives the lower
variance bound and the complete mean, variance, and canonical length-density conclusion.
-/

public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter
open scoped ContDiff ENNReal Topology

namespace Riesz2.LengthVariance

/-- See the proof of Lemma 6.5 in the paper: positive and inverse gap
powers have finite second moments under the actual two-sided tilt. -/
theorem tilted_gap_power_memLp (p : Parameters) (N n : ℕ+) (hN : 2 ≤ (N : ℕ))
    (hn : (n : ℕ) ≤ (N : ℕ)) (θ : PhysicalCutoff) {ε : ℝ} (hε : 0 < ε)
    {r : ℝ} (hr : 0 < r) (j : ℤ) :
    MemLp (fun X : Riesz1.Configuration N => gap X j ^ r) 2
      (tiltedParticleMeasure p N n hn θ ε true) ∧
    MemLp (fun X : Riesz1.Configuration N => gap X j ^ (-r)) 2
      (tiltedParticleMeasure p N n hn θ ε true) := by
  let μ := tiltedParticleMeasure p N n hn θ ε true
  obtain ⟨M, _, hb⟩ := InterpolantLocalLaws.compact_tilted_gap_moments
    p.val.2 ε p.val.1 p.val.1 p.property.2.1 p.property.2.2 hε
    p.property.1 le_rfl θ (2 * r) (by positivity)
  have h := hb p rfl le_rfl le_rfl N n hN hn j
  have hpos (X : Riesz1.Configuration N) : 0 < gap X j := Riesz1.gap_pos X j
  have hi (a : ℝ) (ha :
      (∫⁻ X, ENNReal.ofReal (gap X j ^ (2 * a)) ∂μ) < ⊤) :
      MemLp (fun X : Riesz1.Configuration N => gap X j ^ a) 2 μ := by
    apply (memLp_two_iff_integrable_sq ((Riesz1.measurable_gap j).pow_const a).aestronglyMeasurable).mpr
    have he (X : Riesz1.Configuration N) : (gap X j ^ a) ^ 2 = gap X j ^ (2 * a) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hpos X).le]
      congr 1
      ring
    change Integrable (fun X => (gap X j ^ a) ^ 2) μ
    simp_rw [he]
    exact ⟨((Riesz1.measurable_gap j).pow_const _).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun X =>
        Real.rpow_nonneg (hpos X).le _)).mpr ha⟩
  constructor
  · exact hi r (((le_add_of_nonneg_right zero_le).trans h).trans_lt ENNReal.ofReal_lt_top)
  · apply hi (-r)
    simpa only [mul_neg] using
      (((le_add_of_nonneg_left zero_le).trans h).trans_lt ENNReal.ofReal_lt_top)

/-- See the proof of Lemma 6.5 in the paper: every ambient energy
score has a finite second moment under the two-sided tilt. The realization
agrees with the energy on its entire ambient domain. -/
theorem energy_direction_memLp (p : Parameters) (N n : ℕ+) (hN : 2 ≤ (N : ℕ))
    (hn : (n : ℕ) ≤ (N : ℕ)) (θ : PhysicalCutoff) {ε : ℝ} (hε : 0 < ε) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ∀ w : EuclideanSpace ℝ (Fin (N : ℕ)),
        MemLp (fun X => fderiv ℝ W (WithLp.toLp 2 (gapVector X)) w) 2
          (tiltedParticleMeasure p N n hn θ ε true) := by
  classical
  let μ := tiltedParticleMeasure p N n hn θ ε true
  obtain ⟨U, hU, hv, ht⟩ := MarginalHessian.physical_energy_tensors p N
  obtain ⟨C, hC, hb⟩ := ht 1
  let W := fun y => p.val.1⁻¹ * U y
  have hW : ContDiffOn ℝ ∞ W (gapAmbientDomain N) := contDiffOn_const.mul hU
  have hder (y : EuclideanSpace ℝ (Fin (N : ℕ))) (hy : y ∈ gapAmbientDomain N) :
      fderiv ℝ W y = p.val.1⁻¹ • fderiv ℝ U y :=
    (((hU.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hy)).differentiableAt
      (by simp)).hasFDerivAt.const_mul _).fderiv
  refine ⟨W, hW, fun y => ?_, fun w => ?_⟩
  · dsimp only [W]
    rw [hv y, ← mul_assoc, inv_mul_cancel₀ p.property.1.ne', one_mul]
  · let F := fun X : Riesz1.Configuration N =>
      ∑ i : Fin (N : ℕ), gap X i.val ^ (-(p.val.2 + 1))
    have hF : MemLp F 2 μ := memLp_finsetSum _ fun i _ =>
      (tilted_gap_power_memLp p N n hN hn θ hε
        (show 0 < p.val.2 + 1 by linarith [p.property.2.1]) i.val).2
    have hm : Measurable (fun X : Riesz1.Configuration N =>
        fderiv ℝ W (WithLp.toLp 2 (gapVector X)) w) :=
      (measurable_fderiv_apply_const ℝ W w).comp
        ((WithLp.measurable_toLp 2 _).comp (Riesz1.measurable_gapVector N))
    apply (hF.const_mul (p.val.1⁻¹ * C * ‖w‖)).of_le hm.aestronglyMeasurable
    apply Eventually.of_forall
    intro X
    let y := WithLp.toLp 2 (gapVector X)
    have hy : gapVector X ∈ Riesz1.gapSimplex N := by
      rw [← Riesz1.range_gapVector_eq_gapSimplex]
      exact Set.mem_range_self X
    obtain ⟨i, hi⟩ := ElementaryBarriers.exists_iInf_eq_apply (fun i : Fin (N : ℕ) => y i)
    let δ := y i
    have hδ : 0 < δ := hy.1 i
    have hgap (j : Fin (N : ℕ)) : δ ≤ y j := by
      change y i ≤ y j
      rw [← hi]
      exact ciInf_le (Finite.bddBelow_range _) j
    have hnorm : ‖fderiv ℝ U y‖ ≤ C * δ ^ (-p.val.2 - 1) := by
      simpa only [PNat.val_ofNat, Nat.cast_one, norm_iteratedFDeriv_one] using hb y hy δ hδ hgap
    have hsum : δ ^ (-p.val.2 - 1) ≤ F X := by
      have hh := Finset.single_le_sum (s := Finset.univ)
        (fun j _ => Real.rpow_nonneg (hy.1 j).le (-(p.val.2 + 1))) (Finset.mem_univ i)
      convert hh using 1 <;> congr 1; ring
    have hF0 : 0 ≤ F X := Finset.sum_nonneg fun j _ =>
      Real.rpow_nonneg (Riesz1.gap_pos X j.val).le _
    have hβinv : 0 ≤ p.val.1⁻¹ := inv_nonneg.mpr p.property.1.le
    rw [Real.norm_of_nonneg (show 0 ≤ p.val.1⁻¹ * C * ‖w‖ * F X by
      dsimp [F]; positivity), hder y (GapChart.gapVector_mem_gapAmbientDomain X),
      smul_apply, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr p.property.1.le)]
    calc
      _ ≤ p.val.1⁻¹ * (‖fderiv ℝ U y‖ * ‖w‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (by positivity)
      _ ≤ p.val.1⁻¹ * (C * F X * ‖w‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (hnorm.trans (mul_le_mul_of_nonneg_left hsum hC.le)) (norm_nonneg _)) hβinv
      _ = _ := by ring

namespace Internal

/-- The literal two-sided scalar penalty has polynomially bounded slope.
This bound uses only the cutoff's second derivative bound. -/
theorem scalar_penalty_slope (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ a x : ℝ, 0 < a → 0 < x →
      |deriv (fun t => θ.val (a * t) + θ.val (a / t)) x| ≤
        C * a ^ 2 * (x + x ^ (- (3 : ℝ))) := by
  obtain ⟨C, hC, hb, _⟩ := PhysicalCollision.cutoff_deriv_bounds θ
  refine ⟨C, by linarith, fun a x ha hx => ?_⟩
  have hu := ((PhysicalCollision.cutoff_contDiffAt θ (mul_pos ha hx)).differentiableAt
    (by simp)).hasDerivAt.comp x ((hasDerivAt_id x).const_mul a)
  have hi := PhysicalCollision.inverse_penalty_hasDerivAt θ ha hx
  have hsum : HasDerivAt (fun t => θ.val (a * t) + θ.val (a / t))
      (deriv θ.val (a * x) * (a * 1) + -(a * x⁻¹ ^ 2) * deriv θ.val (a / x)) x := hu.add hi
  rw [hsum.deriv]
  have hp := hb (a * x) (mul_pos ha hx)
  have hn := hb (a / x) (div_pos ha hx)
  have hpow : x ^ (-(3 : ℝ)) = x⁻¹ ^ 3 := by
    rw [Real.rpow_neg hx.le, Real.rpow_ofNat, inv_pow]
  rw [hpow]
  calc
    _ ≤ |deriv θ.val (a * x) * (a * 1)| +
        |-(a * x⁻¹ ^ 2) * deriv θ.val (a / x)| := abs_add_le _ _
    _ = a * deriv θ.val (a * x) + (a * x⁻¹ ^ 2) * deriv θ.val (a / x) := by
      simp only [abs_mul, abs_neg, abs_of_nonneg hp.1, abs_of_nonneg ha.le,
        abs_of_nonneg (sq_nonneg x⁻¹), abs_of_nonneg hn.1, mul_one]
      ring
    _ ≤ a * (C * (a * x)) + (a * x⁻¹ ^ 2) * (C * (a / x)) :=
      add_le_add (mul_le_mul_of_nonneg_left hp.2 ha.le)
        (mul_le_mul_of_nonneg_left hn.2 (by positivity))
    _ = _ := by ring

end Internal

/-- See the proof of Lemma 6.5 in the paper: the actual active penalty
score is square integrable in every ambient direction. -/
theorem penalty_direction_memLp (p : Parameters) (N n : ℕ+) (hN : 2 ≤ (N : ℕ))
    (hn : (n : ℕ) ≤ (N : ℕ)) (θ : PhysicalCutoff) {ε : ℝ} (hε : 0 < ε)
    (J : Finset (Fin (N : ℕ))) (w : EuclideanSpace ℝ (Fin (N : ℕ))) :
    let a := (n : ℝ) ^ (-ε)
    let P := fun y : EuclideanSpace ℝ (Fin (N : ℕ)) =>
      ∑ i ∈ J, (θ.val (a * y i) + θ.val (a / y i))
    MemLp (fun X => fderiv ℝ P (WithLp.toLp 2 (gapVector X)) w) 2
      (tiltedParticleMeasure p N n hn θ ε true) := by
  classical
  intro a P
  let μ := tiltedParticleMeasure p N n hn θ ε true
  let ψ := fun t => θ.val (a * t) + θ.val (a / t)
  have ha : 0 < a := Real.rpow_pos_of_pos (by exact_mod_cast n.pos) _
  have hd (x : ℝ) (hx : 0 < x) : DifferentiableAt ℝ ψ x :=
    (((PhysicalCollision.cutoff_contDiffAt θ (mul_pos ha hx)).differentiableAt
      (by simp)).hasDerivAt.comp x ((hasDerivAt_id x).const_mul a)).differentiableAt.add
      (PhysicalCollision.inverse_penalty_hasDerivAt θ ha hx).differentiableAt
  have he (X : Riesz1.Configuration N) :
      fderiv ℝ P (WithLp.toLp 2 (gapVector X)) w =
        ∑ i ∈ J, deriv ψ (gap X i.val) * w i := by
    let y := WithLp.toLp 2 (gapVector X)
    have hterm (i : Fin (N : ℕ)) : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin (N : ℕ)) => ψ (y i))
        (deriv ψ (y i) • EuclideanSpace.proj (𝕜 := ℝ) i) y :=
      by
        convert
          (hd (y i) (Riesz1.gap_pos X i.val)).hasDerivAt.comp_hasFDerivAt y
            (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt using 1
        rw [EuclideanSpace.coe_proj]
        rfl
    have hh := HasFDerivAt.sum (u := J) (fun i _ => hterm i)
    have hP : HasFDerivAt P (∑ i ∈ J, deriv ψ (y i) • EuclideanSpace.proj (𝕜 := ℝ) i) y := by
      convert hh using 1
      ext z
      simp only [P, ψ, Finset.sum_apply]
    rw [hP.fderiv]
    simp only [sum_apply, smul_apply, smul_eq_mul]
    rfl
  obtain ⟨C, hC, hb⟩ := Internal.scalar_penalty_slope θ
  have hterm (i : Fin (N : ℕ)) : MemLp (fun X : Riesz1.Configuration N =>
      deriv ψ (gap X i.val) * w i) 2 μ := by
    have hp := (tilted_gap_power_memLp p N n hN hn θ hε (r := 1) zero_lt_one i.val).1
    have hi := (tilted_gap_power_memLp p N n hN hn θ hε (r := 3) (by norm_num) i.val).2
    simp only [Real.rpow_one] at hp
    have hm : Measurable (fun X : Riesz1.Configuration N => deriv ψ (gap X i.val) * w i) :=
      ((measurable_deriv ψ).comp (Riesz1.measurable_gap i.val)).mul_const _
    apply ((hp.add hi).const_mul (C * a ^ 2 * |w i|)).of_le hm.aestronglyMeasurable
    apply Eventually.of_forall
    intro X
    change ‖deriv ψ (gap X i.val) * w i‖ ≤
      ‖C * a ^ 2 * |w i| * (gap X i.val + gap X i.val ^ (-(3 : ℝ)))‖
    have hg := (Riesz1.gap_pos X i.val).le
    have hgp := Real.rpow_nonneg hg (-(3 : ℝ))
    have hw0 := abs_nonneg (w i)
    have hbound0 : 0 ≤ C * a ^ 2 * |w i| * (gap X i.val + gap X i.val ^ (-(3 : ℝ))) :=
      mul_nonneg (mul_nonneg (mul_nonneg hC.le (sq_nonneg _)) hw0) (add_nonneg hg hgp)
    rw [Real.norm_eq_abs, abs_mul, Real.norm_of_nonneg hbound0]
    calc
      _ ≤ (C * a ^ 2 * (gap X i.val + gap X i.val ^ (-(3 : ℝ)))) * |w i| :=
        mul_le_mul_of_nonneg_right (hb a _ ha (Riesz1.gap_pos X i.val)) (abs_nonneg _)
      _ = _ := by ring
  apply (memLp_congr_ae (Eventually.of_forall he)).mpr
  exact memLp_finsetSum J fun i _ => hterm i

/-- See the proof of Lemma 6.5 in the paper: the physical total score
belongs to L² under the actual two-sided tilt, independently of any score
identity. The assertion holds for every ambient direction. -/
theorem physical_score_memLp (p : Parameters) (N n : ℕ+) (hN : 2 ≤ (N : ℕ))
    (hn : (n : ℕ) ≤ (N : ℕ)) (θ : PhysicalCutoff) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        U y.val = physicalAmbientGapEnergy p N y +
          ∑ i ∈ Finset.univ.map (Fin.castLEEmb hn),
            (θ.val ((n : ℝ) ^ (-ε) * y.val i) + θ.val ((n : ℝ) ^ (-ε) / y.val i))) ∧
      ∀ w : EuclideanSpace ℝ (Fin (N : ℕ)),
        MemLp (fun X => fderiv ℝ U (WithLp.toLp 2 (gapVector X)) w) 2
          (tiltedParticleMeasure p N n hn θ ε true) := by
  classical
  obtain ⟨W, hW, hv, hmem⟩ := energy_direction_memLp p N n hN hn θ hε
  let a := (n : ℝ) ^ (-ε)
  let J := Finset.univ.map (Fin.castLEEmb hn)
  let P := fun y : EuclideanSpace ℝ (Fin (N : ℕ)) =>
    ∑ i ∈ J, (θ.val (a * y i) + θ.val (a / y i))
  have ha : 0 < a := Real.rpow_pos_of_pos (by exact_mod_cast n.pos) _
  have hP : ContDiffOn ℝ ∞ P (gapAmbientDomain N) := by
    intro y hy
    apply ContDiffAt.contDiffWithinAt
    apply ContDiffAt.sum
    intro i _
    have hi : 0 < y i := by
      simpa only [PhysicalEnergy.gapSum_one] using (hy i 1 (by omega) (by omega)).1
    have hproj : ContDiffAt ℝ ∞ (fun y : EuclideanSpace ℝ (Fin (N : ℕ)) => y i) y :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt
    exact ((PhysicalCollision.cutoff_contDiffAt θ (mul_pos ha hi)).comp y
      (contDiffAt_const.mul hproj)).add
        ((PhysicalCollision.cutoff_contDiffAt θ (div_pos ha hi)).comp y
          (contDiffAt_const.div hproj hi.ne'))
  refine ⟨fun y => W y + P y, hW.add hP, fun y => by dsimp only; rw [hv y], fun w => ?_⟩
  apply (memLp_congr_ae (Eventually.of_forall fun X => ?_)).mpr
  · exact (hmem w).add (penalty_direction_memLp p N n hN hn θ hε J w)
  · have hy := GapChart.gapVector_mem_gapAmbientDomain X
    have hdW := (hW.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hy)).differentiableAt
      (by simp)
    have hdP := (hP.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hy)).differentiableAt
      (by simp)
    exact congrArg (fun L => L w) (hdW.hasFDerivAt.add hdP.hasFDerivAt).fderiv

namespace Internal

/-- In a fixed affine mass chart, the actual penalty derivative has at
most an inverse-cube singularity in the smallest gap. -/
theorem affine_penalty_derivative_bound (k d : ℕ)
    (A : EuclideanSpace ℝ (Fin d) →ᴬ[ℝ] EuclideanSpace ℝ (Fin (k + 1)))
    (hmass : ∀ x, ∑ i, A x i = (k + 1 : ℝ))
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a) (J : Finset (Fin (k + 1)))
    (v : EuclideanSpace ℝ (Fin d)) :
    let P := fun x => ∑ i ∈ J, (θ.val (a * A x i) + θ.val (a / A x i))
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : EuclideanSpace ℝ (Fin d),
      (∀ i, 0 < A x i) →
      ContDiffAt ℝ ∞ P x ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → (∀ i, δ ≤ A x i) →
        |fderiv ℝ P x v| ≤ C * δ ^ (-(3 : ℝ)) := by
  classical
  intro P
  let ψ := fun t => θ.val (a * t) + θ.val (a / t)
  obtain ⟨B, hB, hb⟩ := scalar_penalty_slope θ
  let C := (J.card : ℝ) * (B * a ^ 2 * (k + 2 : ℝ)) * (‖A.contLinear‖ * ‖v‖)
  refine ⟨C, by dsimp [C]; positivity, fun x hx => ?_⟩
  have hs (i : Fin (k + 1)) : ContDiffAt ℝ ∞ (fun x => ψ (A x i)) x := by
    have hi : ContDiffAt ℝ ∞ (fun x => A x i) x :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt.comp x A.contDiff.contDiffAt
    exact ((PhysicalCollision.cutoff_contDiffAt θ (mul_pos ha (hx i))).comp x
      (contDiffAt_const.mul hi)).add
        ((PhysicalCollision.cutoff_contDiffAt θ (div_pos ha (hx i))).comp x
          (contDiffAt_const.div hi (hx i).ne'))
  have hPs : ContDiffAt ℝ ∞ P x := ContDiffAt.sum (fun i _ => hs i)
  refine ⟨hPs, fun δ hδ hδ1 hgap => ?_⟩
  have hscalar (i : Fin (k + 1)) : DifferentiableAt ℝ ψ (A x i) := by
    exact (((PhysicalCollision.cutoff_contDiffAt θ (mul_pos ha (hx i))).differentiableAt
      (by simp)).hasDerivAt.comp (A x i) ((hasDerivAt_id _).const_mul a)).differentiableAt.add
        (PhysicalCollision.inverse_penalty_hasDerivAt θ ha (hx i)).differentiableAt
  have he : fderiv ℝ P x v = ∑ i ∈ J, deriv ψ (A x i) * A.contLinear v i := by
    have hterm (i : Fin (k + 1)) : HasFDerivAt (fun z => ψ (A z i))
        (deriv ψ (A x i) • ((EuclideanSpace.proj (𝕜 := ℝ) i).comp A.contLinear)) x := by
      have hi := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x A.hasFDerivAt
      convert (hscalar i).hasDerivAt.comp_hasFDerivAt x hi using 1
      rw [EuclideanSpace.coe_proj]
      rfl
    have hsum : HasFDerivAt P (∑ i ∈ J, deriv ψ (A x i) •
        ((EuclideanSpace.proj (𝕜 := ℝ) i).comp A.contLinear)) x := by
      convert HasFDerivAt.sum (u := J) (fun i _ => hterm i) using 1
      ext z
      simp only [P, ψ, Finset.sum_apply]
    rw [hsum.fderiv]
    simp only [sum_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply]
    rfl
  have hpow : 1 ≤ δ ^ (-(3 : ℝ)) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by norm_num)
  have hcoef (i : Fin (k + 1)) : |deriv ψ (A x i)| ≤ B * a ^ 2 * (k + 2 : ℝ) * δ ^ (-(3 : ℝ)) := by
    have hiN : A x i ≤ (k + 1 : ℝ) := by
      rw [← hmass x]
      exact Finset.single_le_sum (fun j _ => (hx j).le) (Finset.mem_univ i)
    have hiδ : (A x i) ^ (-(3 : ℝ)) ≤ δ ^ (-(3 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hδ (hgap i) (by norm_num)
    have hiN' : A x i ≤ (k + 1 : ℝ) * δ ^ (-(3 : ℝ)) :=
      hiN.trans (le_mul_of_one_le_right (by positivity) hpow)
    have hh := mul_le_mul_of_nonneg_left (add_le_add hiN' hiδ) (show 0 ≤ B * a ^ 2 by positivity)
    exact (hb a _ ha (hx i)).trans (hh.trans_eq (by ring))
  rw [he]
  calc
    _ ≤ ∑ i ∈ J, |deriv ψ (A x i) * A.contLinear v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ J, (B * a ^ 2 * (k + 2 : ℝ) * δ ^ (-(3 : ℝ))) * (‖A.contLinear‖ * ‖v‖) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul (hcoef i)
        ((PiLp.norm_apply_le (A.contLinear v) i).trans (A.contLinear.le_opNorm v))
        (abs_nonneg _) (by positivity)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; dsimp only [C]; ring

end Internal

/-- See the proof of Lemma 6.5 in the paper, score-flux boundary step:
the directional derivative of the actual penalized density is differentiable
across every collision face in every affine mass chart. -/
theorem penalized_affine_density_flux_regular (p : Parameters) (k : ℕ) (hk : 1 ≤ k)
    (d : ℕ) (A : EuclideanSpace ℝ (Fin d) →ᴬ[ℝ] EuclideanSpace ℝ (Fin (k + 1)))
    (hmass : ∀ x, ∑ i, A x i = (k + 1 : ℝ)) (θ : PhysicalCutoff)
    {a : ℝ} (ha : 0 < a) (J : Finset (Fin (k + 1))) (v : EuclideanSpace ℝ (Fin d)) :
    let q := fun x => fderiv ℝ
      (fun z => (ProperMarginalChart.penalizedDensity p k θ a J true (A z)).toReal) x v
    Differentiable ℝ q ∧ ∀ x, (∃ i, A x i ≤ 0) →
      HasFDerivAt q (0 : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) x := by
  dsimp only
  classical
  let Q : Set (EuclideanSpace ℝ (Fin d)) := {x | ∀ i, 0 < A x i}
  let g := fun x => (ProperMarginalChart.penalizedDensity p k θ a J true (A x)).toReal
  let P := fun x => ∑ i ∈ J, (θ.val (a * A x i) + θ.val (a / A x i))
  have hQ : IsOpen Q := by
    have he : Q = ⋂ i, {x | 0 < A x i} := by ext x; simp [Q]
    rw [he]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
      ((PiLp.continuous_apply 2 (fun _ : Fin (k + 1) => ℝ) i).comp A.continuous)
  have hsimplex (x) (hx : x ∈ Q) : WithLp.ofLp (A x) ∈ Riesz1.gapSimplex k.succPNat :=
    ⟨hx, by simpa only [Nat.succPNat_coe, Nat.cast_succ] using hmass x⟩
  obtain ⟨U, hU, hval, ht⟩ := MarginalHessian.physical_affine_density_tensors p k.succPNat
    (by simp only [Nat.succPNat_coe]; omega)
  let f := fun x => Real.exp (-U (A x))
  obtain ⟨D, hD, hP⟩ := Internal.affine_penalty_derivative_bound k d A hmass θ ha J v
  have hf (x) (hx : x ∈ Q) : ContDiffAt ℝ ∞ f x :=
    ((hU.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain _).mem_nhds
      (PhysicalEnergy.simplex_subset_ambient _ _ (hsimplex x hx)))).comp x
        A.contDiff.contDiffAt).neg.exp
  have he (x) (hx : x ∈ Q) : g x = f x * Real.exp (-p.val.1 * P x) := by
    have hxS : A x ∈ AffineSimplex.massSimplex k (k + 1) := ⟨hx, hmass x⟩
    have hfval : f x = Real.exp (-p.val.1 * physicalAmbientGapEnergy p k.succPNat
        ⟨A x, ProperMarginalChart.simplex_ambient k hxS⟩) := by
      dsimp only [f]
      have hv := hval ⟨A x, PhysicalEnergy.simplex_subset_ambient _ _ (hsimplex x hx)⟩
      rw [hv]
      congr 1
      ring
    rw [hfval]
    simp only [g, ProperMarginalChart.penalizedDensity, ENNReal.toReal_mul,
      ProperMarginalChart.density, dite_eq_left hxS, ENNReal.toReal_ofReal (Real.exp_nonneg _),
      ↓reduceIte, P, div_eq_mul_inv]
  have hg (x) (hx : x ∈ Q) : ContDiffAt ℝ ∞ g x := by
    have hs : ContDiffAt ℝ ∞ (fun z => f z * Real.exp (-p.val.1 * P z)) x :=
      (hf x hx).mul (((contDiffAt_const (c := -p.val.1)).mul (hP x hx).1).exp)
    exact hs.congr_of_eventuallyEq (eventuallyEq_of_mem (hQ.mem_nhds hx) fun y hy => he y hy)
  have hz (x) (hx : x ∉ Q) : g x = 0 := by
    have hn : A x ∉ AffineSimplex.massSimplex k (k + 1) := fun h => hx h.1
    simp only [g, ProperMarginalChart.penalizedDensity, ProperMarginalChart.density,
      dite_eq_right hn, zero_mul, ENNReal.toReal_zero]
  have hdiff : Differentiable ℝ g := penalized_affine_density_differentiable p k hk d A hmass θ ha J
  have hdz (x) (hx : x ∉ Q) : fderiv ℝ g x = 0 := by
    have hmin : IsLocalMin g x := Eventually.of_forall fun y => by
      rw [hz x hx]
      exact ENNReal.toReal_nonneg
    exact hmin.fderiv_eq_zero
  obtain ⟨C₀, hC₀, hb₀⟩ := ht d A 0 5
  obtain ⟨C₁, hC₁, hb₁⟩ := ht d A 1 2
  let B := C₁ * ‖v‖ + p.val.1 * C₀ * D
  have hβ : 0 ≤ p.val.1 := p.property.1.le
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hflux (y) (hy : y ∈ Q) :
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → (∀ i, δ ≤ A y i) → (∃ i, A y i = δ) →
      |fderiv ℝ g y v| ≤ B * δ ^ 2 := by
    intro δ hδ hδ1 hgap hmin
    have ht₀ := hb₀ y (hsimplex y hy) δ hδ hδ1 hgap hmin
    have ht₁ := hb₁ y (hsimplex y hy) δ hδ hδ1 hgap hmin
    have hexp : Real.exp (-(p.val.1 / 2) * δ ^ (-p.val.2)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_nonneg hβ (by norm_num)))
        (Real.rpow_nonneg hδ.le _)
    have hf₀ : δ ^ (-(5 : ℝ)) * |f y| ≤ C₀ := by
      have hh := ht₀.trans (mul_le_of_le_one_right hC₀ hexp)
      simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hh
      convert hh using 1
    have hf₁ : δ ^ (-(2 : ℝ)) * ‖fderiv ℝ f y‖ ≤ C₁ := by
      have hh := ht₁.trans (mul_le_of_le_one_right hC₁ hexp)
      simp only [norm_iteratedFDeriv_one] at hh
      convert hh using 1
    have hfirst : |fderiv ℝ f y v| ≤ C₁ * δ ^ 2 * ‖v‖ := by
      have hh : ‖fderiv ℝ f y‖ ≤ C₁ * δ ^ 2 := by
        rw [Real.rpow_neg hδ.le, Real.rpow_two] at hf₁
        exact (div_le_iff₀ (sq_pos_of_pos hδ)).mp (by simpa only [div_eq_mul_inv, mul_comm] using hf₁)
      exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hh (norm_nonneg _))
    have hsecond : |f y| * |fderiv ℝ P y v| ≤ C₀ * D * δ ^ 2 := by
      have hp := (hP y hy).2 δ hδ hδ1 hgap
      have hh : |f y| * δ ^ (-(3 : ℝ)) ≤ C₀ * δ ^ 2 := by
        have h := mul_le_mul_of_nonneg_right hf₀ (sq_nonneg δ)
        have heq : δ ^ (-(5 : ℝ)) * δ ^ 2 = δ ^ (-(3 : ℝ)) := by
          rw [← Real.rpow_two, ← Real.rpow_add hδ]
          norm_num
        calc
          _ = (δ ^ (-(5 : ℝ)) * |f y|) * δ ^ 2 := by rw [mul_right_comm, heq]; ring
          _ ≤ _ := h
      calc
        _ ≤ |f y| * (D * δ ^ (-(3 : ℝ))) := mul_le_mul_of_nonneg_left hp (abs_nonneg _)
        _ = D * (|f y| * δ ^ (-(3 : ℝ))) := by ring
        _ ≤ D * (C₀ * δ ^ 2) := mul_le_mul_of_nonneg_left hh hD
        _ = _ := by ring
    have hP0 : 0 ≤ P y := Finset.sum_nonneg fun i _ =>
      add_nonneg (θ.property.2.2.1 _ (mul_nonneg ha.le (hy i).le))
        (θ.property.2.2.1 _ (div_nonneg ha.le (hy i).le))
    have hweight : Real.exp (-p.val.1 * P y) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [p.property.1])
    have hegrad : fderiv ℝ g y v = Real.exp (-p.val.1 * P y) *
        (fderiv ℝ f y v - p.val.1 * f y * fderiv ℝ P y v) := by
      have hevent : g =ᶠ[𝓝 y] fun z => f z * Real.exp (-p.val.1 * P z) :=
        eventuallyEq_of_mem (hQ.mem_nhds hy) fun z hz => he z hz
      rw [hevent.fderiv_eq]
      have hh := ((hf y hy).differentiableAt (by simp)).hasFDerivAt.mul
        (((hP y hy).1.differentiableAt (by simp)).hasFDerivAt.const_mul (-p.val.1)).exp
      have hhe := hh.fderiv
      change fderiv ℝ (fun z => f z * Real.exp (-p.val.1 * P z)) y = _ at hhe
      rw [hhe]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
    rw [hegrad, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    calc
      _ ≤ |fderiv ℝ f y v - p.val.1 * f y * fderiv ℝ P y v| :=
        mul_le_of_le_one_left (abs_nonneg _) hweight
      _ ≤ |fderiv ℝ f y v| + p.val.1 * (|f y| * |fderiv ℝ P y v|) := by
        simpa only [abs_mul, abs_of_nonneg p.property.1.le, mul_assoc] using
          abs_sub (fderiv ℝ f y v) (p.val.1 * f y * fderiv ℝ P y v)
      _ ≤ C₁ * δ ^ 2 * ‖v‖ + p.val.1 * (C₀ * D * δ ^ 2) :=
        add_le_add hfirst (mul_le_mul_of_nonneg_left hsecond p.property.1.le)
      _ = _ := by dsimp only [B]; ring
  have hboundary (x : EuclideanSpace ℝ (Fin d)) (hx : x ∉ Q) :
      HasFDerivAt (fun y => fderiv ℝ g y v) (0 : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) x := by
    have hqx : fderiv ℝ g x v = 0 := by rw [hdz x hx, zero_apply]
    have hb (y) : |fderiv ℝ g y v| ≤ (B * ‖A.contLinear‖ ^ 2) * ‖y - x‖ ^ 2 := by
      by_cases hy : y ∈ Q
      · let δ := ⨅ i, A y i
        obtain ⟨j, hj⟩ := ElementaryBarriers.exists_iInf_eq_apply (fun i => A y i)
        have hδ : 0 < δ := by rw [show δ = A y j from hj]; exact hy j
        have hgap (i) : δ ≤ A y i := ciInf_le (Finite.bddBelow_range _) i
        have hδ1 : δ ≤ 1 := by
          have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hgap i)
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hmass y] at hh
          push_cast at hh
          nlinarith [show (0 : ℝ) < k + 1 by positivity]
        obtain ⟨i, hi⟩ : ∃ i, A x i ≤ 0 := by
          simpa only [Q, mem_ofPred_eq, not_forall, not_lt] using hx
        have hdist : δ ≤ ‖A.contLinear‖ * ‖y - x‖ := by
          calc
            δ ≤ A y i - A x i := by linarith [hgap i]
            _ ≤ |A y i - A x i| := le_abs_self _
            _ = ‖(A y - A x) i‖ := by rfl
            _ ≤ ‖A y - A x‖ := PiLp.norm_apply_le _ _
            _ = ‖A.contLinear (y - x)‖ := by
              have heq : A.contLinear (y - x) = A y - A x := A.contLinear_apply_vsub y x
              rw [heq]
            _ ≤ _ := A.contLinear.le_opNorm _
        calc
          _ ≤ B * δ ^ 2 := hflux y hy δ hδ hδ1 hgap ⟨j, hj.symm⟩
          _ ≤ B * (‖A.contLinear‖ * ‖y - x‖) ^ 2 := by gcongr
          _ = _ := by ring
      · rw [hdz y hy, zero_apply, abs_zero]
        positivity
    apply HasFDerivAt.of_isLittleO (f' := (0 : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
    change (fun y => fderiv ℝ g y v - fderiv ℝ g x v -
      (0 : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (y - x)) =o[𝓝 x] fun y => y - x
    simp only [hqx, sub_zero, zero_apply]
    apply Asymptotics.IsLittleO.of_bound
    intro c hc
    have hK : 0 ≤ B * ‖A.contLinear‖ ^ 2 := by positivity
    have hnear : ∀ᶠ y in 𝓝 x, ‖y - x‖ < c / (B * ‖A.contLinear‖ ^ 2 + 1) := by
      have hh : ContinuousAt (fun y => ‖y - x‖) x := by fun_prop
      exact hh.eventually (gt_mem_nhds (by simpa using div_pos hc (by positivity)))
    filter_upwards [hnear] with y hy
    have hh := (lt_div_iff₀ (by positivity : 0 < B * ‖A.contLinear‖ ^ 2 + 1)).mp hy
    have hcoef : B * ‖A.contLinear‖ ^ 2 * ‖y - x‖ ≤ c := by nlinarith [norm_nonneg (y - x)]
    rw [Real.norm_eq_abs]
    exact (hb y).trans (by nlinarith [norm_nonneg (y - x)])
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · by_cases hx : x ∈ Q
    · exact (((hg x hx).fderiv_right (m := 1) (by simp)).differentiableAt (by simp)).clm_apply
        (differentiableAt_const v)
    · exact (hboundary x hx).differentiableAt
  · exact hboundary x (by rintro h; obtain ⟨i, hi⟩ := hx; exact (not_lt.mpr hi) (h i))

/-- See the proof of Lemma 6.5 in the paper: the full tilted law in
the ordinary simplex coordinates, with its exact normalizing factors.
The square-root Jacobian of intrinsic volume cancels explicitly. -/
theorem chart_penalized_density_law (p : Parameters) (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ+) (hn : (n : ℕ) ≤ (k.succPNat : ℕ)) (θ : PhysicalCutoff) (ε : ℝ) :
    (tiltedParticleMeasure p k.succPNat n hn θ ε true).map
      (fun X : Riesz1.Configuration k.succPNat =>
        AffineSimplex.coordinates k (WithLp.toLp 2 (gapVector X))) =
      (tiltNormalizer p k.succPNat n hn θ ε true)⁻¹ •
        (partitionFunction p k.succPNat)⁻¹ •
          ENNReal.ofReal ((k + 1 : ℝ) ^ k)⁻¹ •
            volume.withDensity (fun x => ProperMarginalChart.penalizedDensity p k θ
              ((n : ℝ) ^ (-ε)) (Finset.univ.map (Fin.castLEEmb hn)) true
                (AffineSimplex.chart k (k + 1) x)) := by
  classical
  let ρ := ProperMarginalChart.penalizedDensity p k θ ((n : ℝ) ^ (-ε))
    (Finset.univ.map (Fin.castLEEmb hn)) true
  have hρ : Measurable ρ := ProperMarginalChart.measurable_penalizedDensity p k θ
    (Real.rpow_pos_of_pos (by exact_mod_cast n.pos) _) _ true
  have hcoord := (AffineSimplex.continuous_coordinates k).measurable
  have hchart := (AffineSimplex.continuous_chart k (k + 1)).measurable
  have hpush : ((AffineSimplex.simplexVolume k (k + 1)).withDensity ρ).map
      (AffineSimplex.coordinates k) = ENNReal.ofReal (Real.sqrt (k + 1)) •
        volume.withDensity (fun x => ρ (AffineSimplex.chart k (k + 1) x)) := by
    rw [AffineSimplex.simplexVolume_eq, withDensity_smul_measure,
      Measure.map_smul _ hcoord.aemeasurable,
      ← Riesz1.map_withDensity_comp _ hchart hρ, Measure.map_map hcoord hchart]
    have hid : AffineSimplex.coordinates k ∘ AffineSimplex.chart k (k + 1) = id :=
      funext (AffineSimplex.coordinates_chart k (k + 1))
    rw [hid, Measure.map_id]
    congr 1
    rw [← withDensity_indicator (AffineSimplex.isOpen_chartDomain k (k + 1)).measurableSet]
    congr 1
    funext x
    by_cases hx : x ∈ AffineSimplex.chartDomain k (k + 1)
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx]
      have hnot : AffineSimplex.chart k (k + 1) x ∉ AffineSimplex.massSimplex k (k + 1) :=
        fun h => hx ((AffineSimplex.chart_mem_simplex_iff k (k + 1) x).mp h)
      simp only [ρ, ProperMarginalChart.penalizedDensity, ProperMarginalChart.density,
        dite_eq_right hnot, zero_mul]
  have he := congrArg (Measure.map (AffineSimplex.coordinates k))
    (ProperMarginalChart.map_tiltedParticleMeasure_full p k hk n hn θ ε true)
  have hm : Measurable (fun X : Riesz1.Configuration k.succPNat =>
      WithLp.toLp 2 (gapVector X)) := (WithLp.measurable_toLp 2 _).comp
        (Riesz1.measurable_gapVector k.succPNat)
  rw [Measure.map_map hcoord hm, Measure.map_smul _ hcoord.aemeasurable,
    Measure.map_smul _ hcoord.aemeasurable, Measure.map_smul _ hcoord.aemeasurable,
    Measure.map_smul _ hcoord.aemeasurable, hpush] at he
  simp only [smul_smul, ENNReal.inv_mul_cancel
    (ENNReal.ofReal_ne_zero_iff.mpr (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < k + 1)))
      ENNReal.ofReal_ne_top, mul_one] at he ⊢
  convert he using 1
  rfl

namespace Internal

/-- Global normalized score identities. This internal analytic lemma uses
ordinary differentiability of the density and its directional derivative,
with their integrability proved from the normalized moments. -/
theorem normalized_density_score_identities
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    {g S T H : E → ℝ} (hgm : Measurable g) (hg0 : ∀ x, 0 ≤ g x)
    (hg : Differentiable ℝ g) (v : E)
    (hq : Differentiable ℝ (fun x => fderiv ℝ g x v))
    (hSd : Differentiable ℝ S) (hSv : ∀ x, fderiv ℝ S x v = 1)
    {β : ℝ} (hβ : 0 < β)
    (hd : ∀ x, fderiv ℝ g x v = -β * g x * T x)
    (hdd : ∀ x, fderiv ℝ (fun y => fderiv ℝ g y v) x v =
      β * g x * (β * T x ^ 2 - H x))
    (hprob : IsProbabilityMeasure (c • volume.withDensity (fun x => ENNReal.ofReal (g x))))
    (hS : MemLp S 2 (c • volume.withDensity (fun x => ENNReal.ofReal (g x))))
    (hT : MemLp T 2 (c • volume.withDensity (fun x => ENNReal.ofReal (g x))))
    (hH : Integrable H (c • volume.withDensity (fun x => ENNReal.ofReal (g x)))) :
    let μ := c • volume.withDensity (fun x => ENNReal.ofReal (g x))
    β * ProbabilityTheory.covariance S T μ = 1 ∧
      (∫ x, T x ^ 2 ∂μ) = β⁻¹ * ∫ x, H x ∂μ := by
  let μ := c • volume.withDensity (fun x => ENNReal.ofReal (g x))
  have : IsProbabilityMeasure μ := hprob
  have hweight (f : E → ℝ) (hf : Integrable f μ) : Integrable (fun x => g x * f x) := by
    have hi := (integrable_smul_measure hc0 hct).mp hf
    have hh := (integrable_withDensity_iff_integrable_smul' hgm.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hi
    simpa only [ENNReal.toReal_ofReal (hg0 _), smul_eq_mul] using hh
  have heval (f : E → ℝ) : (∫ x, f x ∂μ) = c.toReal * ∫ x, g x * f x := by
    rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul hgm.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hg0 _), smul_eq_mul]
  have hgi : Integrable g := by simpa only [mul_one] using hweight (fun _ => 1) (integrable_const 1)
  have hTi := hT.integrable one_le_two
  have hTT : Integrable (fun x => T x ^ 2) μ := (memLp_two_iff_integrable_sq hT.aestronglyMeasurable).mp hT
  have hqi : Integrable (fun x => fderiv ℝ g x v) := by
    have he : (fun x => fderiv ℝ g x v) = fun x => -β * (g x * T x) := by ext x; rw [hd]; ring
    rw [he]
    exact (hweight T hTi).const_mul _
  have hqqi : Integrable (fun x => fderiv ℝ (fun y => fderiv ℝ g y v) x v) := by
    have he : (fun x => fderiv ℝ (fun y => fderiv ℝ g y v) x v) =
        fun x => β ^ 2 * (g x * T x ^ 2) - β * (g x * H x) := by ext x; rw [hdd]; ring
    rw [he]
    exact ((hweight _ hTT).const_mul _).sub ((hweight H hH).const_mul _)
  have hzero (f : E → ℝ) (hf : Differentiable ℝ f) (hi : Integrable f)
      (hdi : Integrable (fun x => fderiv ℝ f x v)) : (∫ x, fderiv ℝ f x v) = 0 := by
    have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (f := fun _ : E => (1 : ℝ)) (g := f) (v := v)
      (by
        have he : (fun x : E => fderiv ℝ (fun _ : E => (1 : ℝ)) x v * f x) = 0 := by
          funext x; rw [(hasFDerivAt_const (1 : ℝ) x).fderiv, zero_apply, zero_mul]; rfl
        rw [he]
        exact integrable_zero E ℝ volume)
      (by simpa only [one_mul] using hdi) (by simpa only [one_mul] using hi)
      (fun x _ => differentiableAt_const 1) (fun x _ => hf x)
    have hd1 (x : E) : fderiv ℝ (fun _ : E => (1 : ℝ)) x v = 0 := by
      rw [(hasFDerivAt_const (c := (1 : ℝ)) x).fderiv, zero_apply]
    simpa only [one_mul, hd1, zero_mul, integral_zero, neg_zero] using hh
  have hqzero := hzero _ hq hqi hqqi
  have hscore : (∫ x, T x ^ 2 ∂μ) = β⁻¹ * ∫ x, H x ∂μ := by
    have he : (∫ x, fderiv ℝ (fun y => fderiv ℝ g y v) x v) =
        β ^ 2 * (∫ x, g x * T x ^ 2) - β * ∫ x, g x * H x := by
      simp_rw [hdd]
      rw [integral_congr_ae (Eventually.of_forall fun x => show
        β * g x * (β * T x ^ 2 - H x) = β ^ 2 * (g x * T x ^ 2) - β * (g x * H x) by ring),
        integral_sub ((hweight _ hTT).const_mul _) ((hweight H hH).const_mul _), integral_const_mul, integral_const_mul]
    rw [he] at hqzero
    have hh : β * (∫ x, g x * T x ^ 2) = ∫ x, g x * H x := by nlinarith
    rw [heval, heval]
    calc
      _ = c.toReal * (β⁻¹ * (β * ∫ x, g x * T x ^ 2)) := by field_simp
      _ = _ := by rw [hh]; ring
  let F := fun x => S x - ∫ y, S y ∂μ
  have hF : MemLp F 2 μ := hS.sub (memLp_const _)
  have hFT : Integrable (fun x => F x * T x) μ := hF.integrable_mul hT
  have hFd : Differentiable ℝ F := hSd.sub_const _
  have hFv (x) : fderiv ℝ F x v = 1 := by rw [fderiv_sub_const, hSv]
  have hip := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := F) (g := g) (v := v)
    (by simpa only [hFv, one_mul] using hgi)
    (by
      have he : (fun x => F x * fderiv ℝ g x v) = fun x => -β * (g x * (F x * T x)) := by
        ext x; rw [hd]; ring
      rw [he]
      exact (hweight _ hFT).const_mul _)
    (by simpa only [mul_comm] using hweight F (hF.integrable one_le_two))
    (fun x _ => hFd x) (fun x _ => hg x)
  have hpair : β * (∫ x, F x * T x ∂μ) = 1 := by
    have he : (∫ x, F x * fderiv ℝ g x v) = -β * ∫ x, g x * (F x * T x) := by
      rw [← integral_const_mul]
      apply integral_congr_ae (Eventually.of_forall fun x => ?_)
      rw [hd]
      ring
    rw [he] at hip
    simp only [hFv, one_mul] at hip
    have hmass : c.toReal * (∫ x, g x) = 1 := by
      simpa only [integral_const, probReal_univ, one_smul, mul_one] using (heval (fun _ => 1)).symm
    rw [heval]
    have hh := congrArg (fun z => c.toReal * z) hip
    nlinarith only [hh, hmass]
  refine ⟨?_, hscore⟩
  have hecov : ProbabilityTheory.covariance S T μ = ∫ x, F x * T x ∂μ := by
    rw [ProbabilityTheory.covariance_eq_sub hS hT]
    change (∫ x, S x * T x ∂μ) - (∫ x, S x ∂μ) * (∫ x, T x ∂μ) = _
    rw [show (fun x => F x * T x) = fun x => S x * T x - (∫ y, S y ∂μ) * T x by ext x; dsimp only [F]; ring]
    have hiST : Integrable (fun x => S x * T x) μ := hS.integrable_mul hT
    rw [integral_sub hiST (hTi.const_mul _), integral_const_mul]
  rw [hecov]
  exact hpair

/-- Actual first and second density derivatives in an arbitrary affine
mass chart. The exterior formulas use the proved collision flux derivative. -/
theorem affine_density_score_derivatives (p : Parameters) (k : ℕ) (hk : 1 ≤ k)
    (d : ℕ) (A : EuclideanSpace ℝ (Fin d) →ᴬ[ℝ] EuclideanSpace ℝ (Fin (k + 1)))
    (hmass : ∀ x, ∑ i, A x i = (k + 1 : ℝ)) (θ : PhysicalCutoff)
    {a : ℝ} (ha : 0 < a) (J : Finset (Fin (k + 1)))
    (U : EuclideanSpace ℝ (Fin (k + 1)) → ℝ)
    (hU : ContDiffOn ℝ ∞ U (gapAmbientDomain k.succPNat))
    (hval : ∀ y : {y : EuclideanSpace ℝ (Fin (k + 1)) // y ∈ gapAmbientDomain k.succPNat},
      U y.val = physicalAmbientGapEnergy p k.succPNat y +
        ∑ i ∈ J, (θ.val (a * y.val i) + θ.val (a / y.val i)))
    (v : EuclideanSpace ℝ (Fin d)) :
    let g := fun x => (ProperMarginalChart.penalizedDensity p k θ a J true (A x)).toReal
    let w := A.contLinear v
    let T := fun x => fderiv ℝ U (A x) w
    let H := fun x => fderiv ℝ (fderiv ℝ U) (A x) w w
    Differentiable ℝ g ∧ Differentiable ℝ (fun x => fderiv ℝ g x v) ∧
      (∀ x, fderiv ℝ g x v = -p.val.1 * g x * T x) ∧
      (∀ x, fderiv ℝ (fun y => fderiv ℝ g y v) x v =
        p.val.1 * g x * (p.val.1 * T x ^ 2 - H x)) := by
  classical
  intro g w Tc Hc
  have hg := penalized_affine_density_differentiable p k hk d A hmass θ ha J
  have hflux := penalized_affine_density_flux_regular p k hk d A hmass θ ha J v
  let Q : Set (EuclideanSpace ℝ (Fin d)) := {x | ∀ i, 0 < A x i}
  have hQ : IsOpen Q := by
    have he : Q = ⋂ i, {x | 0 < A x i} := by ext x; simp [Q]
    rw [he]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
      ((PiLp.continuous_apply 2 (fun _ : Fin (k + 1) => ℝ) i).comp A.continuous)
  have hinside (x) (hx : x ∈ Q) : A x ∈ gapAmbientDomain k.succPNat :=
    ProperMarginalChart.simplex_ambient k ⟨hx, hmass x⟩
  have hzero (x) (hx : x ∉ Q) : g x = 0 := by
    have hnQ : A x ∉ AffineSimplex.massSimplex k (k + 1) := fun h => hx h.1
    simp only [g, ProperMarginalChart.penalizedDensity, ProperMarginalChart.density,
      dite_eq_right hnQ, zero_mul, ENNReal.toReal_zero]
  have hevent (x) (hx : x ∈ Q) : g =ᶠ[𝓝 x] fun z => Real.exp (-p.val.1 * U (A z)) := by
    apply eventuallyEq_of_mem (hQ.mem_nhds hx)
    intro z hz
    have hS : A z ∈ AffineSimplex.massSimplex k (k + 1) := ⟨hz, hmass z⟩
    have hv := hval ⟨A z, hinside z hz⟩
    dsimp only [g, ProperMarginalChart.penalizedDensity, ProperMarginalChart.density]
    rw [dite_eq_left hS, ENNReal.toReal_mul]
    simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _), ↓reduceIte]
    rw [← Real.exp_add]
    congr 1
    rw [hv]
    simp only [div_eq_mul_inv]
    ring
  have hd (x) : fderiv ℝ g x v = -p.val.1 * g x * Tc x := by
    by_cases hx : x ∈ Q
    · have hu := (hU.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain _).mem_nhds
        (hinside x hx))).differentiableAt (by simp)
      have hdensity := ((hu.hasFDerivAt.comp x A.hasFDerivAt).const_mul (-p.val.1)).exp
      have heD := hdensity.fderiv
      change fderiv ℝ (fun z => Real.exp (-p.val.1 * U (A z))) x = _ at heD
      rw [(hevent x hx).fderiv_eq, heD, (hevent x hx).eq_of_nhds]
      simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply, Function.comp_apply]
      change _ = -p.val.1 * _ * fderiv ℝ U (A x) w
      rw [show A.contLinear v = w from rfl]
      ring
    · have hmin : IsLocalMin g x := Eventually.of_forall fun y => by
        rw [hzero x hx]; exact ENNReal.toReal_nonneg
      rw [hmin.fderiv_eq_zero, zero_apply, hzero x hx, mul_zero, zero_mul]
  have hdd (x) : fderiv ℝ (fun y => fderiv ℝ g y v) x v =
      p.val.1 * g x * (p.val.1 * Tc x ^ 2 - Hc x) := by
    by_cases hx : x ∈ Q
    · have hu := hU.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain _).mem_nhds (hinside x hx))
      have hDU := ((hu.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)).hasFDerivAt
      have hDT := (hDU.comp x A.hasFDerivAt).clm_apply (hasFDerivAt_const (x := x) (c := w))
      have hDTv : fderiv ℝ Tc x v = Hc x := by
        have hdT := hDT.fderiv
        change fderiv ℝ Tc x = _ at hdT
        rw [hdT]
        simp only [add_apply, ContinuousLinearMap.comp_apply, zero_apply, map_zero, zero_add,
          ContinuousLinearMap.flip_apply]
        rw [show A.contLinear v = w from rfl]
      have heq : (fun y => fderiv ℝ g y v) = fun y => -p.val.1 * g y * Tc y := funext hd
      rw [heq]
      have hdTc : HasFDerivAt Tc (fderiv ℝ Tc x) x := hDT.differentiableAt.hasFDerivAt
      have hdg : HasFDerivAt g (fderiv ℝ g x) x := (hg x).hasFDerivAt
      have hh := (hdg.const_mul (-p.val.1)).mul hdTc
      have heh := hh.fderiv
      change fderiv ℝ (fun y => -p.val.1 * g y * Tc y) x = _ at heh
      rw [heh]
      simp only [add_apply, smul_apply, smul_eq_mul, hd, hDTv]
      ring
    · obtain ⟨i, hi⟩ : ∃ i, A x i ≤ 0 := by
        simpa only [Q, mem_ofPred_eq, not_forall, not_lt] using hx
      rw [(hflux.2 x ⟨i, hi⟩).fderiv, zero_apply, hzero x hx, mul_zero, zero_mul]
  exact ⟨hg, hflux.1, hd, hdd⟩

/-- Physical instantiation of the global score identities. The realization
and Hessian integrability premises are internal inputs supplied by the
physical expected-curvature theorem. -/
theorem physical_score_identities (p : Parameters) (k : ℕ) (hk : 1 ≤ k)
    (a : ℕ+) (haK : (a : ℕ) ≤ k) (θ : PhysicalCutoff) {ε : ℝ} (hε : 0 < ε)
    (U : EuclideanSpace ℝ (Fin (k + 1)) → ℝ)
    (hU : ContDiffOn ℝ ∞ U (gapAmbientDomain k.succPNat))
    (hval : ∀ y : {y : EuclideanSpace ℝ (Fin (k + 1)) // y ∈ gapAmbientDomain k.succPNat},
      U y.val = physicalAmbientGapEnergy p k.succPNat y +
        ∑ i ∈ Finset.univ.map (Fin.castLEEmb (haK.trans (Nat.le_succ k))),
          (θ.val ((a : ℝ) ^ (-ε) * y.val i) + θ.val ((a : ℝ) ^ (-ε) / y.val i)))
    (w : EuclideanSpace ℝ (Fin (k + 1))) (hw : (∑ i, w i) = 0)
    (hwa : (∑ i : Fin (a : ℕ), w (i.castLE (haK.trans (Nat.le_succ k)))) = 1)
    (hH : Integrable (fun X : Riesz1.Configuration k.succPNat => fderiv ℝ (fderiv ℝ U) (WithLp.toLp 2 (gapVector X)) w w)
      (tiltedParticleMeasure p k.succPNat a (haK.trans (Nat.le_succ k)) θ ε true)) :
    let μ := tiltedParticleMeasure p k.succPNat a (haK.trans (Nat.le_succ k)) θ ε true
    let S := fun X : Riesz1.Configuration k.succPNat => ∑ i : Fin (a : ℕ), gap X i.val
    let T := fun X : Riesz1.Configuration k.succPNat => fderiv ℝ U (WithLp.toLp 2 (gapVector X)) w
    MemLp T 2 μ ∧ p.val.1 * ProbabilityTheory.covariance S T μ = 1 ∧
      (∫ X, T X ^ 2 ∂μ) = p.val.1⁻¹ *
        ∫ X, fderiv ℝ (fderiv ℝ U) (WithLp.toLp 2 (gapVector X)) w w ∂μ := by
  classical
  intro μ S T
  let hn := haK.trans (Nat.le_succ k)
  have hN : 2 ≤ (k.succPNat : ℕ) := by simp only [Nat.succPNat_coe]; omega
  have : IsProbabilityMeasure μ := (InterpolatingDensities.tilt_valid p k.succPNat a hn θ ε true).2.2
  obtain ⟨U₀, hU₀, hv₀, hmem₀⟩ := physical_score_memLp p k.succPNat a hN hn θ hε
  have hT : MemLp T 2 μ := by
    apply (memLp_congr_ae (Eventually.of_forall fun X => ?_)).mpr (hmem₀ w)
    let y := WithLp.toLp 2 (gapVector X)
    have hy := GapChart.gapVector_mem_gapAmbientDomain X
    have heq : U =ᶠ[𝓝 y] U₀ := eventuallyEq_of_mem
      ((PhysicalEnergy.isOpen_gapAmbientDomain _).mem_nhds hy) fun z hz =>
        (hval ⟨z, hz⟩).trans (hv₀ ⟨z, hz⟩).symm
    exact congrArg (fun D : EuclideanSpace ℝ (Fin (k + 1)) →L[ℝ] ℝ => D w) (heq.fderiv_eq (𝕜 := ℝ))
  let L := (AffineSimplex.tangentMap k).toContinuousLinearMap
  let A : EuclideanSpace ℝ (Fin k) →ᴬ[ℝ] EuclideanSpace ℝ (Fin (k + 1)) :=
    L.toContinuousAffineMap + ContinuousAffineMap.const ℝ _ (AffineSimplex.chart k (k + 1) 0)
  have hAL : A.contLinear = L := by
    ext z i
    simp [A]
  have hA (x) : A x = AffineSimplex.chart k (k + 1) x :=
    (AffineSimplex.chart_eq_tangentMap_add k (k + 1) x).symm
  have hmass (x) : ∑ i, A x i = (k + 1 : ℝ) := by rw [hA]; exact AffineSimplex.sum_chart _ _ _
  let v := AffineSimplex.coordinates k w
  have hLv : L v = w := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have hh := hw
      rw [Fin.sum_univ_castSucc] at hh
      change AffineSimplex.chart k 0 v (Fin.last k) = w (Fin.last k)
      rw [AffineSimplex.chart_last]
      change 0 - ∑ j : Fin k, w j.castSucc = w (Fin.last k)
      linarith
    · change AffineSimplex.chart k 0 v j.castSucc = w j.castSucc
      rw [AffineSimplex.chart_castSucc]
      rfl
  let π := fun X : Riesz1.Configuration k.succPNat =>
    AffineSimplex.coordinates k (WithLp.toLp 2 (gapVector X))
  have hπ : Measurable π := (AffineSimplex.continuous_coordinates k).measurable.comp
    ((WithLp.measurable_toLp 2 _).comp (Riesz1.measurable_gapVector k.succPNat))
  have hAπ (X : Riesz1.Configuration k.succPNat) : A (π X) = WithLp.toLp 2 (gapVector X) := by
    rw [hA]
    apply AffineSimplex.chart_coordinates
    have hy : gapVector X ∈ Riesz1.gapSimplex k.succPNat := by
      rw [← Riesz1.range_gapVector_eq_gapSimplex]
      exact Set.mem_range_self X
    change (∑ i : Fin (k + 1), gapVector X i) = k + 1
    simpa only [Nat.succPNat_coe, Nat.cast_succ] using hy.2
  let J := Finset.univ.map (Fin.castLEEmb hn)
  let ρ := ProperMarginalChart.penalizedDensity p k θ ((a : ℝ) ^ (-ε)) J true
  let g := fun x => (ρ (A x)).toReal
  let Tc := fun x => fderiv ℝ U (A x) w
  let Hc := fun x => fderiv ℝ (fderiv ℝ U) (A x) w w
  let Sc := fun x : EuclideanSpace ℝ (Fin k) => ∑ i : Fin (a : ℕ), A x (i.castLE hn)
  let c := (tiltNormalizer p k.succPNat a hn θ ε true)⁻¹ *
    ((partitionFunction p k.succPNat)⁻¹ * ENNReal.ofReal ((k + 1 : ℝ) ^ k)⁻¹)
  let ν := μ.map π
  have hρ : Measurable ρ := ProperMarginalChart.measurable_penalizedDensity p k θ
    (Real.rpow_pos_of_pos (by exact_mod_cast a.pos) _) _ true
  have hρt (y) : ρ y ≠ ⊤ := by
    dsimp only [ρ, ProperMarginalChart.penalizedDensity, ProperMarginalChart.density]
    split_ifs <;> finiteness
  have hν : ν = c • volume.withDensity (fun x => ENNReal.ofReal (g x)) := by
    have hh := chart_penalized_density_law p k hk a hn θ ε
    change ν = _ at hh
    rw [hh]
    simp only [smul_smul]
    congr 2
    funext x
    rw [ENNReal.ofReal_toReal (hρt _), hA]
  have hc0 : c ≠ 0 := by
    dsimp only [c]
    refine mul_ne_zero ?_ (mul_ne_zero ?_ ?_)
    · exact ENNReal.inv_ne_zero.mpr (ne_of_lt ((InterpolatingDensities.tilt_valid p k.succPNat a hn θ ε true).2.1.trans_lt ENNReal.one_lt_top))
    · exact ENNReal.inv_ne_zero.mpr (ne_of_lt (finiteModel_valid p k.succPNat).2.2.2)
    · exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hct : c ≠ ⊤ := by
    dsimp only [c]
    refine ENNReal.mul_ne_top ?_ (ENNReal.mul_ne_top ?_ ?_)
    · exact ENNReal.inv_ne_top.mpr (ne_of_gt (InterpolatingDensities.tilt_valid p k.succPNat a hn θ ε true).1)
    · exact ENNReal.inv_ne_top.mpr (ne_of_gt (finiteModel_valid p k.succPNat).2.2.1)
    · exact ENNReal.ofReal_ne_top
  have hgm : Measurable g := ENNReal.measurable_toReal.comp (hρ.comp A.continuous.measurable)
  have hTcm : Measurable Tc := (measurable_fderiv_apply_const ℝ U w).comp A.continuous.measurable
  have hHcm : Measurable Hc := ((ContinuousLinearMap.measurable_apply w).comp
    (measurable_fderiv_apply_const ℝ (fderiv ℝ U) w)).comp A.continuous.measurable
  have hScd : Differentiable ℝ Sc := by
    have hh : Differentiable ℝ (∑ i : Fin (a : ℕ), fun x => A x (i.castLE hn)) :=
      Differentiable.sum (fun i _ =>
        (EuclideanSpace.proj (𝕜 := ℝ) (i.castLE hn)).differentiable.comp A.differentiable)
    convert hh using 1
    ext x
    simp only [Sc, Finset.sum_apply]
  have hScv (x) : fderiv ℝ Sc x v = 1 := by
    have hd : HasFDerivAt Sc (∑ i : Fin (a : ℕ),
      (EuclideanSpace.proj (𝕜 := ℝ) (i.castLE hn)).comp L) x := by
      convert HasFDerivAt.sum (u := (Finset.univ : Finset (Fin (a : ℕ)))) (fun i _ =>
        (EuclideanSpace.proj (𝕜 := ℝ) (i.castLE hn)).hasFDerivAt.comp x A.hasFDerivAt) using 1
      · ext z; simp only [Sc, Finset.sum_apply]; rfl
      · rw [hAL]
    rw [hd.fderiv]
    simpa only [sum_apply, ContinuousLinearMap.comp_apply, hLv, EuclideanSpace.coe_proj] using hwa
  have hScπ (X) : Sc (π X) = S X := by simp only [Sc, hAπ]; rfl
  have hTcπ (X) : Tc (π X) = T X := by dsimp only [Tc]; rw [hAπ]
  have hHcπ (X) : Hc (π X) = fderiv ℝ (fderiv ℝ U) (WithLp.toLp 2 (gapVector X)) w w := by dsimp only [Hc]; rw [hAπ]
  have hS : MemLp S 2 μ := memLp_finsetSum _ fun i _ => by
    simpa only [Real.rpow_one] using
      (tilted_gap_power_memLp p _ a hN hn θ hε (r := 1) zero_lt_one i.val).1
  have hTc : MemLp Tc 2 ν := (memLp_map_measure_iff hTcm.aestronglyMeasurable hπ.aemeasurable).mpr
    ((memLp_congr_ae (Eventually.of_forall hTcπ)).mpr hT)
  have hSc : MemLp Sc 2 ν := (memLp_map_measure_iff hScd.continuous.measurable.aestronglyMeasurable hπ.aemeasurable).mpr
    ((memLp_congr_ae (Eventually.of_forall hScπ)).mpr hS)
  have hHc : Integrable Hc ν := (integrable_map_measure hHcm.aestronglyMeasurable hπ.aemeasurable).mpr
    (hH.congr (Eventually.of_forall fun X => (hHcπ X).symm))
  obtain ⟨hg, hflux, hd, hdd⟩ := affine_density_score_derivatives p k hk k A hmass θ
    (a := (a : ℝ) ^ (-ε)) (Real.rpow_pos_of_pos (by exact_mod_cast a.pos) _) J U hU hval v
  rw [hAL, hLv] at hd hdd
  have : IsProbabilityMeasure ν := inferInstance
  have hident := normalized_density_score_identities hc0 hct hgm
    (fun x => ENNReal.toReal_nonneg) hg v hflux hScd hScv p.property.1 hd hdd
    (hν ▸ (inferInstance : IsProbabilityMeasure ν))
    (hν ▸ hSc) (hν ▸ hTc) (hν ▸ hHc)
  dsimp only at hident
  rw [← hν] at hident
  refine ⟨hT, ?_, ?_⟩
  · have hc := ProbabilityTheory.covariance_map_fun hSc.aestronglyMeasurable
      hTc.aestronglyMeasurable hπ.aemeasurable
    change ProbabilityTheory.covariance Sc Tc ν = _ at hc
    simp only [hScπ, hTcπ] at hc
    rw [hc] at hident
    exact hident.1
  · have hleft : (∫ x, Tc x ^ 2 ∂ν) = ∫ X, T X ^ 2 ∂μ := by
      rw [integral_map hπ.aemeasurable (hTcm.pow_const 2).aestronglyMeasurable]
      simp only [hTcπ]
    have hright : (∫ x, Hc x ∂ν) = ∫ X,
        fderiv ℝ (fderiv ℝ U) (WithLp.toLp 2 (gapVector X)) w w ∂μ := by
      rw [integral_map hπ.aemeasurable hHcm.aestronglyMeasurable]
      simp only [hHcπ]
    calc
      _ = ∫ x, Tc x ^ 2 ∂ν := hleft.symm
      _ = p.val.1⁻¹ * ∫ x, Hc x ∂ν := hident.2
      _ = _ := by rw [hright]

end Internal

/-- See the proof of Lemma 6.5 in the paper: the lower length variance
bound, uniformly on each compact positive temperature interval. -/
theorem lower_variance (s ε βlo βhi : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (hε : 0 < ε) (hlo : 0 < βlo) (hle : βlo ≤ βhi) (θ : PhysicalCutoff) :
    ∃ c : ℝ, 0 < c ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ n m : ℕ,
      2 * (n + 1) ≤ n + 1 + (m + 1) →
      ENNReal.ofReal (c * (n + 1 : ℝ) ^ (min s 1)) ≤
        Riesz1.variance (LengthAveragingFibres.activeMeasure p n m θ ε)
          (fun x => ∑ i, x i) (memLp_one_iff_integrable.mp (length_memLp p n m θ ε 1)) := by
  classical
  obtain ⟨C, hC, hcurv⟩ := expected_total_curvature s ε βlo βhi hs hs1 hε hlo hle θ
  have hhi : 0 < βhi := hlo.trans_le hle
  refine ⟨1 / (βhi * C), by positivity, fun p hps hpl hph n m hsize => ?_⟩
  let N := (n + 1 + m).succPNat
  let a : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩
  let hn : (a : ℕ) ≤ (N : ℕ) := by change n + 1 ≤ n + 1 + m + 1; omega
  let μ := tiltedParticleMeasure p N a hn θ ε true
  let u : EuclideanSpace ℝ (Fin (n + 1)) := WithLp.toLp 2 (fun _ => (n + 1 : ℝ)⁻¹)
  let w := MarginalHessian.compensatedDirection (n + 1) m (Equiv.refl _) u
  have := (InterpolatingDensities.tilt_valid p N a hn θ ε true).2.2
  obtain ⟨U, hU, hv, hHi, hHb⟩ := hcurv p hps hpl hph n m hsize
  have hw := compensated_length_direction n m
  dsimp only at hw
  have hv' (y : {y : EuclideanSpace ℝ (Fin (n + 1 + m + 1)) // y ∈ gapAmbientDomain N}) :
      U y.val = physicalAmbientGapEnergy p N y +
        ∑ i ∈ Finset.univ.map (Fin.castLEEmb hn),
          (θ.val ((a : ℝ) ^ (-ε) * y.val i) + θ.val ((a : ℝ) ^ (-ε) / y.val i)) := by
    rw [hv y]
    congr 1
    rw [Finset.sum_map]
    have hac : (a : ℝ) = n + 1 := by simp [a]
    rw [hac]
    apply Finset.sum_congr rfl
    intro i _
    have hi : i.castAdd (m + 1) = (Fin.castLEEmb hn) i := Fin.ext rfl
    rw [hi]
  have hwa : (∑ i : Fin (a : ℕ), w (i.castLE hn)) = 1 := by
    convert hw.2.1 using 1
    apply Finset.sum_congr rfl
    intro i _
    change w (i.castLE hn) = w (i.castAdd (m + 1))
    exact congrArg (fun j : Fin (N : ℕ) => w j) (Fin.ext rfl)
  obtain ⟨hT, hpair, hscore⟩ := Internal.physical_score_identities p (n + 1 + m)
    (by omega) a (by change n + 1 ≤ n + 1 + m; omega) θ hε U hU hv' w hw.1 hwa hHi
  obtain ⟨hS, hS2, hvar⟩ := active_variance_eq_particle p n m θ ε
  let A := C * (n + 1 : ℝ) ^ (-min s 1)
  have hA : 0 < A := mul_pos hC (Real.rpow_pos_of_pos (by positivity) _)
  have hTbound : (∫ X, (fderiv ℝ U (WithLp.toLp 2 (gapVector X)) w) ^ 2 ∂μ) ≤ A / p.val.1 := by
    calc
      _ = p.val.1⁻¹ * ∫ X, fderiv ℝ (fderiv ℝ U) (WithLp.toLp 2 (gapVector X)) w w ∂μ := hscore
      _ ≤ p.val.1⁻¹ * (C * (n + 1 : ℝ) ^ (-min s 1)) :=
        mul_le_mul_of_nonneg_left hHb (inv_nonneg.mpr p.property.1.le)
      _ = _ := by dsimp only [A]; ring
  have hlower := Internal.score_square_lower μ hS2 hT p.property.1 hA hpair hTbound
  rw [hvar]
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hlower
  have hx : 0 < (n + 1 : ℝ) := by positivity
  have he : 1 / (p.val.1 * A) = (1 / (p.val.1 * C)) * (n + 1 : ℝ) ^ (min s 1) := by
    dsimp only [A]
    rw [Real.rpow_neg hx.le]
    field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_right
    (one_div_le_one_div_of_le (mul_pos p.property.1 hC)
      (mul_le_mul_of_nonneg_right hph hC.le)) (Real.rpow_nonneg hx.le _)

/-- See the proof of Lemma 6.5 in the paper, complete statement. The
loss is selected using only the exponent, and the tail power before the
compact temperature interval. A single pair of constants works for the
mean estimate, both variance estimates, and the canonical length density.
Lean `n,m` denote `n+1` active and `m+1` exterior gaps. -/
theorem length_averaging_variance (hRig : External.LongRangeRigidityLocallyUniform)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ κ εstar : ℝ, 0 < κ ∧ 0 < εstar ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ εstar → ∃ δ : ℝ, 0 < δ ∧
        ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
          ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
            ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
              ∀ n m : ℕ, 1 ≤ n → 4 * (n + 1) ≤ n + 1 + m + 1 →
                (n + 1 : ℝ) ^ (2 / s) ≤ ((n + 1 + m : ℕ) + 1 : ℝ) →
                let ν := LengthAveragingFibres.activeMeasure p n m θ ε
                let V := Riesz1.variance ν (fun x => ∑ i, x i)
                  (memLp_one_iff_integrable.mp (length_memLp p n m θ ε 1))
                |(∫ x, ∑ i, x i ∂ν) - (n + 1 : ℝ)| ≤
                    C * Real.exp (-c * (n + 1 : ℝ) ^ δ) ∧
                  ENNReal.ofReal (c * (n + 1 : ℝ) ^ (min s 1)) ≤ V ∧
                  V ≤ ENNReal.ofReal (C * (n + 1 : ℝ) ^ (min s 1 + κ * ε)) ∧
                  ∀ L M : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ),
                    ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
                      ∃ h : a * L.val + b * M.val ∈ Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ),
                        a * Real.log (LengthAveragingFibres.lengthDensity p n m θ ε L).toReal +
                          b * Real.log (LengthAveragingFibres.lengthDensity p n m θ ε M).toReal ≤
                            Real.log (LengthAveragingFibres.lengthDensity p n m θ ε
                              ⟨a * L.val + b * M.val, h⟩).toReal := by
  obtain ⟨εstar, hεstar, hu⟩ := upper_variance hRig s hs hs1
  refine ⟨2, εstar, by norm_num, hεstar, fun ε hε hεsmall => ?_⟩
  obtain ⟨δ, hδ, hm⟩ := mean_exponential_locally_uniform s ε hs hs1 hε
  refine ⟨δ, hδ, fun βlo βhi hlo hle θ => ?_⟩
  obtain ⟨A, b, hA, hb, hmean⟩ := hm βlo βhi hlo hle θ
  obtain ⟨B, hB, hupper⟩ := hu ε hε hεsmall βlo βhi hlo hle θ
  obtain ⟨d, hd, hlower⟩ := lower_variance s ε βlo βhi hs hs1 hε hlo hle θ
  refine ⟨A + B, min b d, add_pos hA hB, lt_min hb hd, fun p hps hpl hph n m hn hsize hscale => ?_⟩
  intro ν V
  refine ⟨?_, ?_, ?_, fun L M a b ha hb hab => lengthDensity_logConcave_values p n m θ ε L M a b ha hb hab⟩
  · apply (hmean p hps hpl hph n m).trans
    apply mul_le_mul
    · exact le_add_of_nonneg_right hB.le
    · apply Real.exp_le_exp.mpr
      have hpow : 0 ≤ (n + 1 : ℝ) ^ δ := by positivity
      exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left b d)) hpow
    · exact (Real.exp_pos _).le
    · exact (add_pos hA hB).le
  · apply le_trans (ENNReal.ofReal_le_ofReal ?_) (hlower p hps hpl hph n m (by omega))
    exact mul_le_mul_of_nonneg_right (min_le_right b d) (by positivity)
  · apply (hupper p hps hpl hph n m hn hsize hscale).trans
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA.le) (by positivity)

end Riesz2.LengthVariance
