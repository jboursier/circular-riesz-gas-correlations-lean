/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.PhysicalCorePart7
public import Riesz2.DecayLong.PhysicalIdentityPart8
public import Riesz2.DecayShort.PhysicalDecayPart5

/-!
# Full-cycle physical comparison

Supporting estimates for the proof of Theorem 1.
The physical and auxiliary equations use the same intrinsic scalar form and
zero-sum component constraint. The full tilted gap law and the physical
Hessian are the existing objects.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology ContDiff Classical

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.FullCycleComparison

/-- Supporting the proof of Theorem 1: an
ambient gap observable has its literal particle-law norm after pulling back
to the intrinsic full-cycle chart. This applies at every exponent, including
infinity, without choosing a section of the gap map. -/
theorem intrinsic_gap_norm (p : Parameters) (N : ℕ+) (θ : PhysicalCutoff)
    (η : ℝ) (b : Bool) (f : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ)
    (hf : Measurable f) (q : ℝ≥0∞) :
    eLpNorm (fun z : gapTangentSpace N => f (WithLp.toLp 2 (fun i => 1+z.val i))) q
      (fullIntrinsicTiltedGapLaw p N θ η b) =
    eLpNorm (fun X : Riesz1.Configuration N => f (WithLp.toLp 2 (gapVector X))) q
      (tiltedParticleMeasure p N N le_rfl θ η b) := by
  rw [DecayShort.PhysicalDecay.full_intrinsic_tilted_eq_map]
  have hY : Measurable (fun z : gapTangentSpace N =>
      WithLp.toLp 2 (fun i => 1+z.val i)) :=
    (PhysicalCollision.intrinsic_chart_contDiff N).continuous.measurable
  rw [eLpNorm_map_measure (g := fun z : gapTangentSpace N =>
    f (WithLp.toLp 2 (fun i => 1+z.val i)))
    (hf.comp hY).aestronglyMeasurable (DefinitionSanity.intrinsic_projection_measurable N).aemeasurable]
  congr 1
  funext X
  dsimp only [Function.comp_apply]
  rw [DecayShort.PhysicalDecay.internal_full_chart_gap]

/-- Supporting the proof of Theorem 1: the
reference Hessian has a polynomial entry envelope, uniformly over every
truncation, including the empty truncation. -/
theorem reference_entry_envelope (s : Riesz1.RieszExponent) :
    ∃ R : ℝ, 0 < R ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K : ℕ)
      (a b : Fin (N : ℕ)),
      |2*referenceIntervalMatrix s N hN K a b| ≤ R*(N : ℝ)^2 := by
  obtain ⟨R,hR,hw⟩ := BoundaryEntries.referenceWeight_bound s
  refine ⟨R,hR,fun N hN K a b => ?_⟩
  rw [PhysicalCore.Internal.referenceMatrix_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _i : Fin (N : ℕ), ∑ _r : Fin ((N : ℕ)/2), R := by
      apply Finset.sum_le_sum
      intro i _
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro r _
      have hn := BoundaryEntries.referenceWeight_nonneg s N hN K (i,r)
      have hb := hw N hN K (i,r)
      have hp : (r.val+1 : ℝ)^(-s.val-2) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos
          (le_add_of_nonneg_left (Nat.cast_nonneg _)) (by linarith [s.property.1])
      have hr : BoundaryEntries.referenceWeight s N hN K (i,r) ≤ R :=
        hb.trans (mul_le_of_le_one_right hR.le hp)
      split_ifs <;> simp_all only [mul_one,mul_zero,abs_zero,abs_of_nonneg hn]
      all_goals positivity
    _ = (N : ℝ)*((N : ℕ)/2 : ℕ)*R := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring
    _ ≤ R*(N : ℝ)^2 := by
      have hn : (((N : ℕ)/2 : ℕ) : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast Nat.div_le_self (N : ℕ) 2
      nlinarith [mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ N) hR.le)
        (sub_nonneg.mpr hn)]

/-- Supporting the proof of Theorem 1: the
maximum principle acts directly on the zero-sum solution of the actual
auxiliary field. The polynomial mass exponent precedes temperature and
forcing data. No normal multiplier is estimated. -/
theorem auxiliary_maximum (s : Riesz1.RieszExponent) (M₀ : ℕ) :
    ∃ c κ : ℝ, 0 < c ∧ 0 < κ ∧ ∀ (β : InverseTemperature) (N : ℕ+)
      (hN : 2 ≤ (N : ℕ)) (θ : PhysicalCutoff) (η κ₀ : ℝ), 0 ≤ η →
      let K := ⌊(N : ℝ)^η⌋₊^M₀
      K ≤ (N : ℕ)/4 →
      ∀ (Q : ScalarFormData (fullIntrinsicTiltedGapLaw (ofLong β s) N θ η false)),
      IsClosedScalarDirichletForm Q → ∀ (i₀ : Fin (N : ℕ))
        (χ : Lp ℝ 2 (fullIntrinsicTiltedGapLaw (ofLong β s) N θ η false))
        (u : Fin (N : ℕ) → Q.1),
        WeightedWeakSolution Q (fun z => β.val • PhysicalCore.fullMatrix s N hN K θ η κ₀
          (WithLp.toLp 2 (fun i => 1+z.val i))) (zeroSumComponents _)
          (fun i => if i=i₀ then χ else 0) u →
        eLpNorm (fun z => WithLp.toLp 2 (fun i => (u i).val z)) ∞
          (fullIntrinsicTiltedGapLaw (ofLong β s) N θ η false) ≤
        ENNReal.ofReal ((β.val*c*(N : ℝ)^(-κ*η))⁻¹) *
          eLpNorm χ ∞ (fullIntrinsicTiltedGapLaw (ofLong β s) N θ η false) := by
  obtain ⟨c,hc,hl⟩ := PhysicalCore.fullMatrix_cutoff_coercivity s
  let κ := s.val+2+(M₀ : ℝ)*(1+s.val)
  have hκ : 0 < κ := by dsimp only [κ]; have := s.property.1; positivity
  refine ⟨c,κ,hc,hκ,?_⟩
  intro β N hN θ η κ₀ hη K hKN Q hQ i₀ χ u hu
  let ν := fullIntrinsicTiltedGapLaw (ofLong β s) N θ η false
  let M := fun z : gapTangentSpace N => β.val • PhysicalCore.fullMatrix s N hN K θ η κ₀
    (WithLp.toLp 2 (fun i => 1+z.val i))
  let a := β.val*c*(N : ℝ)^(-κ*η)
  have ha : 0 < a := mul_pos (mul_pos β.property hc) (Real.rpow_pos_of_pos (by positivity) _)
  have hY : Measurable (fun z : gapTangentSpace N => WithLp.toLp 2 (fun i => 1+z.val i)) :=
    (PhysicalCollision.intrinsic_chart_contDiff N).continuous.measurable
  have hm : ∀ i j, Measurable (fun z => M z i j) :=
    AbstractEnergy.scaled_measurable _ _ (fun i j =>
      (PhysicalCore.measurable_fullMatrix s N hN K θ η κ₀ i j).comp hY)
  have hlow : ∀ᵐ z ∂ν, (∀ i j, M z i j = M z j i) ∧
      ∀ t : Fin (N : ℕ) → ℝ, a*(∑ i,t i^2) ≤ ∑ i,∑ j,t i*M z i j*t j := by
    apply ae_of_all
    intro z
    have he := hl M₀ β N hN θ η κ₀ hη hKN (WithLp.toLp 2 (fun i => 1+z.val i))
    have hsym := PhysicalCore.fullMatrix_symmetric β s N hN K θ η κ₀
      (WithLp.toLp 2 (fun i => 1+z.val i))
    have hHerm : (PhysicalCore.fullMatrix s N hN K θ η κ₀
        (WithLp.toLp 2 (fun i => 1+z.val i))).IsHermitian := by
      ext i j
      simp only [Matrix.conjTranspose_apply,star_trivial]
      exact hsym j i
    have hb := (FiniteMatrixOrder.smul_one_le_iff hHerm _).mp he
    refine ⟨fun i j => congrArg (fun r : ℝ => β.val*r) (hsym i j),fun t => ?_⟩
    have hh := mul_le_mul_of_nonneg_left (hb t) β.property.le
    simpa only [M,a,κ,Matrix.smul_apply,smul_eq_mul,Matrix.mulVec,dotProduct,
      Finset.mul_sum,mul_assoc,mul_left_comm,mul_comm,pow_two] using hh
  have hh := AbstractEnergy.weakSolution_eLpNorm_top_le Q hQ M hm a ha hlow
    (zeroSumComponents _) (fun i => if i=i₀ then χ else 0) u hu
  rwa [DecayShort.PhysicalDecay.internal_point_source_essSup] at hh

namespace Internal

/-- The fourth moment of a full-cycle signed coefficient defect is polynomial
in the size. This uses the literal forcing and reference matrix. -/
theorem particle_defect_four_norm (s : Riesz1.RieszExponent) {η Cθ : ℝ}
    (hη : 0 < η) (hCθ : 1 ≤ Cθ) (βlo βhi : ℝ)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ D : ℝ, 0 < D ∧ ∀ (β : InverseTemperature), β.val ∈ Icc βlo βhi →
      ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K : ℕ) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ a b : Fin (N : ℕ),
        eLpNorm (fun X : Riesz1.Configuration N =>
          PhysicalCore.forcingHessian N θ η (WithLp.toLp 2 (gapVector X)) a b +
            GoodBlocks.particleHessian (ofLong β s) N a b X -
              2*referenceIntervalMatrix s N hN K a b) 4
          (tiltedParticleMeasure (ofLong β s) N N le_rfl θ η false) ≤
            ENNReal.ofReal (D*(N : ℝ)^2) := by
  obtain ⟨M,hM,hm⟩ := GoodBlocks.tilted_hessian_moments s.val βlo βhi η Cθ
    s.property.1 hlo hle hη hCθ
  obtain ⟨R,hR,hr⟩ := reference_entry_envelope s
  let B := M*(4 : ℝ)^((s.val+2)/s.val)
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B+Cθ+R,by linarith,?_⟩
  intro β hβ N hN K θ hcurv a b
  let μ := tiltedParticleMeasure (ofLong β s) N N le_rfl θ η false
  have : IsProbabilityMeasure μ := DefinitionSanity.tilted_probability _ _ _ _ _ _ _
  let H := GoodBlocks.particleHessian (ofLong β s) N a b
  let F := fun X : Riesz1.Configuration N =>
    PhysicalCore.forcingHessian N θ η (WithLp.toLp 2 (gapVector X)) a b + H X -
      2*referenceIntervalMatrix s N hN K a b
  have hFm : Measurable F := by
    apply Measurable.sub_const
    exact ((PhysicalCore.measurable_forcingHessian N θ η a b).comp
      ((WithLp.measurable_toLp 2 _).comp (Riesz1.measurable_gapVector N))).add (GoodBlocks.measurable_particleHessian _ _ _ _)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hn2 : (1 : ℝ) ≤ (N : ℝ)^2 := one_le_pow₀ hn1
  have hCn : 0 ≤ Cθ+R*(N : ℝ)^2 := by positivity
  have hnorm : eLpNorm H 4 μ ≤ ENNReal.ofReal B := by
    have ht := hm (ofLong β s) rfl hβ.1 hβ.2 N N hN le_rfl θ hcurv a b 4 (by norm_num)
    norm_num only [ENNReal.ofReal_ofNat] at ht
    exact ht.trans (ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right hB.le
      (Real.rpow_le_one_of_one_le_of_nonpos
        (le_add_of_nonneg_right (Nat.cast_nonneg _)) (by linarith [s.property.1]))))
  have hbound : ∀ X, ‖F X‖ ≤ H X+(Cθ+R*(N : ℝ)^2) := by
    intro X
    have hx := PhysicalCore.Internal.simplex_mem_forcing_chart N
      (WithLp.toLp 2 (gapVector X)) (Riesz1.boundary_gapVector_mem_simplex X)
    have hf0 := ((PhysicalCore.forcingHessian_bound N 0 θ η).choose_spec.2
      ⟨_,hx⟩ a b).1
    have hf : PhysicalCore.forcingHessian N θ η (WithLp.toLp 2 (gapVector X)) a b ≤ Cθ := by
      rw [PhysicalCore.forcingHessian_apply N 0 θ η ⟨_,hx⟩ a b]
      split_ifs
      · have hh := hcurv ((N : ℝ)^(-η)*gapVector X a)
          (mul_pos (Real.rpow_pos_of_pos (by positivity) _) (DefinitionSanity.gap_positive X a.val))
        exact (div_le_self hh.1 (one_le_pow₀ (Real.one_le_rpow hn1 hη.le))).trans hh.2
      · linarith
    have hH := GoodBlocks.particleHessian_nonneg (ofLong β s) N a b X
    have ht := (abs_sub (PhysicalCore.forcingHessian N θ η (WithLp.toLp 2 (gapVector X)) a b+H X)
      (2*referenceIntervalMatrix s N hN K a b)).trans
        (add_le_add (abs_add_le _ _) (hr N hN K a b))
    rw [abs_of_nonneg hf0,abs_of_nonneg hH] at ht
    rw [Real.norm_eq_abs]
    exact ht.trans (by dsimp only [F,H] at *; linarith)
  have hconst : eLpNorm (fun _ : Riesz1.Configuration N => Cθ+R*(N : ℝ)^2) 4 μ =
      ENNReal.ofReal (Cθ+R*(N : ℝ)^2) := by
    simp [eLpNorm_const',Real.enorm_eq_ofReal hCn]
  have hadd := eLpNorm_add_le (f := H)
    (g := fun _ : Riesz1.Configuration N => Cθ+R*(N : ℝ)^2) (μ := μ) (by norm_num : (1 : ℝ≥0∞) ≤ 4)
  have hh := (eLpNorm_mono_ae_real hFm.aestronglyMeasurable (ae_of_all μ hbound)).trans hadd
  refine hh.trans ((add_le_add hnorm hconst.le).trans ?_)
  rw [← ENNReal.ofReal_add hB.le hCn]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [mul_nonneg (by linarith : 0 ≤ B+Cθ) (sub_nonneg.mpr hn2)]

end Internal

/-- Supporting the proof of Theorem 1: each
entry of the unscaled signed physical-minus-core defect is exponentially
small in L² of the actual intrinsic tilted law. The forcing and reference
contributions are included. The exponent is exactly the beta-independent
power of Subsection 5.1, and constants are uniform on compact beta intervals. -/
theorem exceptional_defect_entries (hRig : External.LongRangeRigidityLocallyUniform)
    (s : Riesz1.RieszExponent) {η Cθ : ℝ} (hη : 0 < η) (hCθ : 1 ≤ Cθ)
    (βlo βhi : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (β : InverseTemperature), β.val ∈ Icc βlo βhi →
      ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K : ℕ) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ κ₀ : ℝ, 1 ≤ κ₀ → ∀ a b : Fin (N : ℕ),
        eLpNorm (fun z : gapTangentSpace N =>
          (PhysicalCore.fullGapGoodSet s N η κ₀)ᶜ.indicator (fun y =>
            PhysicalCore.forcingHessian N θ η y a b + GoodBlocks.gapHessian s N a b y -
              2*referenceIntervalMatrix s N hN K a b)
                (WithLp.toLp 2 (fun i => 1+z.val i))) 2
          (fullIntrinsicTiltedGapLaw (ofLong β s) N θ η false) ≤
            ENNReal.ofReal (C*Real.exp (-c*(N : ℝ)^GoodBlocks.coefficientTailPower s.val η)) := by
  obtain ⟨D,hD,hfour⟩ := Internal.particle_defect_four_norm s hη hCθ βlo βhi hlo hle
  obtain ⟨B,c,hB,hc,hprob⟩ := GoodBlocks.full_good_event hRig s hη hCθ βlo βhi hlo hle
  have hδ := GoodBlocks.coefficientTailPower_pos s.property.1 s.property.2 hη
  obtain ⟨A,hA,habsorb⟩ := MomentEvent.exists_rpow_mul_exp_neg_le (a := 2)
    hδ (show c/8 < c/4 by linarith)
  refine ⟨D*B^(1/4 : ℝ)*(A+1),c/8,by positivity,by positivity,?_⟩
  intro β hβ N hN K θ hcurv κ₀ hκ₀ a b
  let μ := tiltedParticleMeasure (ofLong β s) N N le_rfl θ η false
  let E := (GoodBlocks.fullGoodEvent (ofLong β s) N η κ₀)ᶜ
  let F := fun X : Riesz1.Configuration N =>
    PhysicalCore.forcingHessian N θ η (WithLp.toLp 2 (gapVector X)) a b +
      GoodBlocks.particleHessian (ofLong β s) N a b X - 2*referenceIntervalMatrix s N hN K a b
  let f := (PhysicalCore.fullGapGoodSet s N η κ₀)ᶜ.indicator (fun y =>
    PhysicalCore.forcingHessian N θ η y a b + GoodBlocks.gapHessian s N a b y -
      2*referenceIntervalMatrix s N hN K a b)
  have hf : Measurable f :=
    (((PhysicalCore.measurable_forcingHessian N θ η a b).add
      (GoodBlocks.measurable_gapHessian s N a b)).sub_const _).indicator
        (PhysicalCore.measurableSet_fullGapGoodSet s N η κ₀).compl
  have hF : Measurable F :=
    (((PhysicalCore.measurable_forcingHessian N θ η a b).comp
      ((WithLp.measurable_toLp 2 _).comp (Riesz1.measurable_gapVector N))).add
        (GoodBlocks.measurable_particleHessian _ _ _ _)).sub_const _
  have he : (fun X : Riesz1.Configuration N => f (WithLp.toLp 2 (gapVector X))) = E.indicator F := by
    funext X
    simp only [f,E,F,indicator,mem_compl_iff,PhysicalCore.fullGapGoodSet_gapVector β s N,
      GoodBlocks.gapHessian_particle β s N]
  change eLpNorm (fun z : gapTangentSpace N => f (WithLp.toLp 2 (fun i => 1+z.val i))) 2 _ ≤ _
  rw [intrinsic_gap_norm _ _ _ _ _ f hf 2,he,
    eLpNorm_indicator_eq_eLpNorm_restrict (GoodBlocks.measurableSet_fullGoodEvent _ _ _ _).compl.nullMeasurableSet]
  have hh := MomentEvent.restricted_two_norm_le hF E
    (t := c*(N : ℝ)^GoodBlocks.coefficientTailPower s.val η)
    (by positivity : 0 ≤ D*(N : ℝ)^2) hB.le
    (hfour β hβ N hN K θ hcurv a b)
    (by simpa only [neg_mul] using hprob β hβ N hN θ hcurv κ₀ hκ₀)
  refine hh.trans (ENNReal.ofReal_le_ofReal ?_)
  have ha := habsorb (N : ℝ) (by exact_mod_cast N.pos)
  have hapos := mul_le_mul_of_nonneg_left ha (show 0 ≤ D*B^(1/4 : ℝ) by positivity)
  have hpos := Real.exp_pos (-(c/8)*(N : ℝ)^GoodBlocks.coefficientTailPower s.val η)
  have hexp : -(c*(N : ℝ)^GoodBlocks.coefficientTailPower s.val η)/4 =
      -(c/4)*(N : ℝ)^GoodBlocks.coefficientTailPower s.val η := by ring
  rw [hexp]
  norm_num only [Real.rpow_ofNat] at hapos
  calc
    _ = (D*B^(1/4 : ℝ))*((N : ℝ)^2*
        Real.exp (-(c/4)*(N : ℝ)^GoodBlocks.coefficientTailPower s.val η)) := by ring
    _ ≤ (D*B^(1/4 : ℝ))*(A*
        Real.exp (-(c/8)*(N : ℝ)^GoodBlocks.coefficientTailPower s.val η)) := hapos
    _ ≤ _ := by
      have hp := mul_le_mul_of_nonneg_left (show A ≤ A+1 by linarith)
        (show 0 ≤ D*B^(1/4 : ℝ)*Real.exp (-(c/8)*(N : ℝ)^GoodBlocks.coefficientTailPower s.val η)
          by positivity)
      convert hp using 1 <;> ring

/-- Supporting the proof of Theorem 1: the
entry estimate applies to the literal ambient physical Hessian and actual
auxiliary matrix on the intrinsic law. It applies to every smooth physical
representative, not just a chosen extension. -/
theorem physical_exceptional_entries (hRig : External.LongRangeRigidityLocallyUniform)
    (s : Riesz1.RieszExponent) {η Cθ : ℝ} (hη : 0 < η) (hCθ : 1 ≤ Cθ)
    (βlo βhi : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (β : InverseTemperature), β.val ∈ Icc βlo βhi →
      ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K : ℕ) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ κ₀ : ℝ, 1 ≤ κ₀ →
      ∀ U : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain N) →
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        U y.val = fullPhysicalPotentialValue (ofLong β s) N hN θ η false y) →
      ∀ a b : Fin (N : ℕ),
        let ν := fullIntrinsicTiltedGapLaw (ofLong β s) N θ η false
        let f := fun z : gapTangentSpace N =>
          hessianMatrix U (WithLp.toLp 2 (fun i => 1+z.val i)) a b -
            β.val*PhysicalCore.fullMatrix s N hN K θ η κ₀ (WithLp.toLp 2 (fun i => 1+z.val i)) a b
        MemLp f 2 ν ∧ eLpNorm f 2 ν ≤
          ENNReal.ofReal (C*Real.exp (-c*(N : ℝ)^GoodBlocks.coefficientTailPower s.val η)) := by
  obtain ⟨C,c,hC,hc,hentry⟩ := exceptional_defect_entries hRig s hη hCθ βlo βhi hlo hle
  have hhi : 0 < βhi := lt_of_lt_of_le hlo hle
  refine ⟨βhi*C,c,by positivity,hc,?_⟩
  intro β hβ N hN K θ hcurv κ₀ hκ₀ U hU hv a b ν f
  let Y := fun z : gapTangentSpace N => WithLp.toLp 2 (fun i => 1+z.val i)
  let g := fun z : gapTangentSpace N =>
    (PhysicalCore.fullGapGoodSet s N η κ₀)ᶜ.indicator (fun y =>
      PhysicalCore.forcingHessian N θ η y a b+GoodBlocks.gapHessian s N a b y-
        2*referenceIntervalMatrix s N hN K a b) (Y z)
  have hY : Measurable Y := (PhysicalCollision.intrinsic_chart_contDiff N).continuous.measurable
  have hfm : Measurable f :=
    ((DifferentiatedPoisson.measurable_hessian_entries (V := U) a b).comp hY).sub
      (((PhysicalCore.measurable_fullMatrix s N hN K θ η κ₀ a b).comp hY).const_mul β.val)
  have hsupp : ∀ᵐ z ∂ν, WithLp.ofLp (Y z) ∈ Riesz1.gapSimplex N := by
    obtain ⟨V,_,_,hG,_⟩ := PhysicalFormDomain.full_trace_inputs β s N hN θ η
    exact (IntrinsicScalarCore.supported (AffineMetric.intrinsicGapDomain_isOpen N) hG).mono
      (fun z hz => PhysicalCollision.intrinsic_chart_mem_simplex N hz)
  have heq : f =ᵐ[ν] β.val • g := by
    filter_upwards [hsupp] with z hz
    rw [show f z = hessianMatrix U (Y z) a b -
      β.val*PhysicalCore.fullMatrix s N hN K θ η κ₀ (Y z) a b from rfl,
      PhysicalIdentity.Internal.full_multiplication_defect β s N hN K θ η κ₀ U hU hv (Y z) hz a b]
    dsimp only [g,Pi.smul_apply,smul_eq_mul,indicator,mem_compl_iff]
    by_cases hzgood : Y z ∈ PhysicalCore.fullGapGoodSet s N η κ₀
    · simp only [mem_compl_iff,hzgood,not_true_eq_false,ite_true,ite_false,mul_zero]
    · simp only [mem_compl_iff,hzgood,not_false_eq_true,ite_true,ite_false]
  have hn : eLpNorm f 2 ν ≤ ENNReal.ofReal
      (βhi*C*Real.exp (-c*(N : ℝ)^GoodBlocks.coefficientTailPower s.val η)) := by
    rw [eLpNorm_congr_ae heq,eLpNorm_const_smul,Real.enorm_eq_ofReal_abs,abs_of_pos β.property]
    have hh := mul_le_mul_right (hentry β hβ N hN K θ hcurv κ₀ hκ₀ a b) (ENNReal.ofReal β.val)
    refine hh.trans ?_
    rw [← ENNReal.ofReal_mul β.property.le]
    apply ENNReal.ofReal_le_ofReal
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hβ.2
      (show 0 ≤ C*Real.exp (-c*(N : ℝ)^GoodBlocks.coefficientTailPower s.val η) by positivity)
  exact ⟨by rw [memLp_iff]; exact hn.trans_lt ENNReal.ofReal_lt_top,hn⟩

/-- Supporting the proof of Theorem 1: the
actual signed matrix action on the constrained auxiliary solution is in L².
The estimate retains all polynomial factors explicitly. The entry estimate
has already absorbed its own polynomial loss. The constants controlling
the auxiliary mass precede the temperature interval and the cutoff scale. -/
theorem auxiliary_residual (hRig : External.LongRangeRigidityLocallyUniform)
    (s : Riesz1.RieszExponent) (M₀ : ℕ) :
    ∃ c₀ κ : ℝ, 0 < c₀ ∧ 0 < κ ∧
      ∀ {η Cθ : ℝ}, 0 < η → 1 ≤ Cθ →
      ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (β : InverseTemperature), β.val ∈ Icc βlo βhi →
      ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ κ₀ : ℝ, 1 ≤ κ₀ →
      let K := ⌊(N : ℝ)^η⌋₊^M₀
      K ≤ (N : ℕ)/4 →
      ∀ U : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain N) →
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        U y.val = fullPhysicalPotentialValue (ofLong β s) N hN θ η false y) →
      let ν := fullIntrinsicTiltedGapLaw (ofLong β s) N θ η false
      ∀ Q : ScalarFormData ν, IsClosedScalarDirichletForm Q →
      ∀ (i₀ : Fin (N : ℕ)) (χ : Lp ℝ 2 ν), eLpNorm χ ∞ ν < ⊤ →
      ∀ u : Fin (N : ℕ) → Q.1,
      WeightedWeakSolution Q (fun z => β.val • PhysicalCore.fullMatrix s N hN K θ η κ₀
        (WithLp.toLp 2 (fun i => 1+z.val i))) (zeroSumComponents _)
        (fun i => if i=i₀ then χ else 0) u →
      ∃ g : Fin (N : ℕ) → Lp ℝ 2 ν,
        (∀ᵐ z ∂ν, ∀ i, g i z = ∑ j,
          (hessianMatrix U (WithLp.toLp 2 (fun k => 1+z.val k)) i j -
            β.val*PhysicalCore.fullMatrix s N hN K θ η κ₀
              (WithLp.toLp 2 (fun k => 1+z.val k)) i j)*(u j).val z) ∧
        ‖WithLp.toLp 2 g‖ ≤ (N : ℝ)^4 *
          ((β.val*c₀*(N : ℝ)^(-κ*η))⁻¹*(eLpNorm χ ∞ ν).toReal) *
          (C*Real.exp (-c*(N : ℝ)^GoodBlocks.coefficientTailPower s.val η)) := by
  obtain ⟨c₀,κ,hc₀,hκ,hmax⟩ := auxiliary_maximum s M₀
  refine ⟨c₀,κ,hc₀,hκ,?_⟩
  intro η Cθ hη hCθ βlo βhi hlo hle
  obtain ⟨C,c,hC,hc,he⟩ := physical_exceptional_entries hRig s hη hCθ βlo βhi hlo hle
  refine ⟨C,c,hC,hc,?_⟩
  intro β hβ N hN θ hcurv κ₀ hκ₀ K hKN U hU hv ν Q hQ i₀ χ hχ u hu
  let Y := fun z : gapTangentSpace N => WithLp.toLp 2 (fun i => 1+z.val i)
  let D := fun z : gapTangentSpace N => hessianMatrix U (Y z) -
    β.val • PhysicalCore.fullMatrix s N hN K θ η κ₀ (Y z)
  let T := fun z : gapTangentSpace N => ∑ i, ∑ j, |D z i j|
  let E := C*Real.exp (-c*(N : ℝ)^GoodBlocks.coefficientTailPower s.val η)
  let R := (β.val*c₀*(N : ℝ)^(-κ*η))⁻¹*(eLpNorm χ ∞ ν).toReal
  have hY : Measurable Y := (PhysicalCollision.intrinsic_chart_contDiff N).continuous.measurable
  have hDm : ∀ i j, Measurable (fun z => D z i j) := fun i j =>
    ((DifferentiatedPoisson.measurable_hessian_entries (V := U) i j).comp hY).sub
      (((PhysicalCore.measurable_fullMatrix s N hN K θ η κ₀ i j).comp hY).const_mul β.val)
  have hDn : ∀ i j, eLpNorm (fun z => D z i j) 2 ν ≤ ENNReal.ofReal E := fun i j =>
    (he β hβ N hN K θ hcurv κ₀ hκ₀ U hU hv i j).2
  have hTn : eLpNorm T 2 ν ≤ ENNReal.ofReal ((N : ℝ)^2*E) := by
    calc
      _ ≤ ∑ i, eLpNorm (fun z => ∑ j, |D z i j|) 2 ν := by
        have hh := eLpNorm_sum_le (s := Finset.univ) (f := fun i => fun z => ∑ j, |D z i j|)
          (μ := ν) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
        have heq : (∑ i, fun z => ∑ j, |D z i j|) = T := by
          funext z
          simp only [T,Finset.sum_apply]
        rwa [heq] at hh
      _ ≤ ∑ _i : Fin (N : ℕ), ∑ _j : Fin (N : ℕ), ENNReal.ofReal E := by
        apply Finset.sum_le_sum
        intro i _
        have hh : eLpNorm (fun z => ∑ j, |D z i j|) 2 ν ≤
            ∑ j, eLpNorm (fun z => |D z i j|) 2 ν := by
          have hsum := eLpNorm_sum_le (s := Finset.univ) (f := fun j => fun z => |D z i j|)
            (μ := ν) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
          have heq : (∑ j, fun z => |D z i j|) = (fun z => ∑ j, |D z i j|) := by
            funext z
            simp only [Finset.sum_apply]
          rwa [heq] at hsum
        refine hh.trans (Finset.sum_le_sum (fun j _ => ?_))
        rw [show (fun z => |D z i j|) = (fun z => ‖D z i j‖) from rfl,
          eLpNorm_norm _ (hDm i j).aestronglyMeasurable]
        exact hDn i j
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
  have hT : MemLp T 2 ν := hTn.trans_lt ENNReal.ofReal_lt_top
  have hT0 : ∀ᵐ z ∂ν, 0 ≤ T z := ae_of_all ν (fun z =>
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)))
  have hentry : ∀ᵐ z ∂ν, ∀ i j, |D z i j| ≤ T z := by
    apply ae_of_all
    intro z i j
    exact (Finset.single_le_sum (fun k _ => abs_nonneg (D z i k)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => abs_nonneg (D z k l)))
        (Finset.mem_univ i))
  have ha : 0 < β.val*c₀*(N : ℝ)^(-κ*η) :=
    mul_pos (mul_pos β.property hc₀) (Real.rpow_pos_of_pos (by positivity) _)
  have hUbound : ∀ᵐ z ∂ν,
      ‖(WithLp.toLp 2 (fun i => (u i).val z) : EuclideanSpace ℝ (Fin (N : ℕ)))‖ ≤ R := by
    have hh := hmax β N hN θ η κ₀ hη.le hKN Q hQ i₀ χ u hu
    have hn := ae_le_eLpNormEssSup (f := fun z => WithLp.toLp 2 (fun i => (u i).val z)) (μ := ν)
    rw [← eLpNorm_exponent_top (VectorRadial.memLp_values (fun i => (u i).val)).aestronglyMeasurable] at hn
    filter_upwards [hn] with z hz
    have ht := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hχ.ne) (hz.trans hh)
    simpa only [R,ENNReal.toReal_mul,ENNReal.toReal_ofReal (inv_nonneg.mpr ha.le),
      enorm_eq_nnnorm,ENNReal.coe_toReal,coe_nnnorm] using ht
  obtain ⟨g,hg,hgn⟩ := DecayShort.PhysicalDecay.internal_action_of_envelope D hDm T hT hT0
    (fun i => (u i).val) R (by dsimp only [R]; positivity) hentry hUbound
  refine ⟨g,hg,?_⟩
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hTn
  rw [ENNReal.toReal_ofReal (by dsimp only [E]; positivity)] at ht
  have hn := hgn.trans (mul_le_mul_of_nonneg_left ht (by dsimp only [R]; positivity))
  convert hn using 1
  dsimp only [R,E]
  ring

namespace Internal

/-- Same-form comparison for the literal full-cycle matrices. Only this
internal helper takes an L² residual as an explicit input. -/
theorem physical_perturbation_error (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (η κ₀ : ℝ)
    (hη : 0 ≤ η) (U : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ)
    (hU : ContDiffOn ℝ ∞ U (gapAmbientDomain N))
    (hv : ∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
      U y.val = fullPhysicalPotentialValue (ofLong β s) N hN θ η false y)
    (Q : ScalarFormData (fullIntrinsicTiltedGapLaw (ofLong β s) N θ η false))
    (hQ : IsClosedScalarDirichletForm Q)
    (f g : Fin (N : ℕ) → Lp ℝ 2 (fullIntrinsicTiltedGapLaw (ofLong β s) N θ η false))
    (ψ v : Fin (N : ℕ) → Q.1)
    (hψ : WeightedWeakSolution Q (fun z => hessianMatrix U (WithLp.toLp 2 (fun i => 1+z.val i)))
      (zeroSumComponents _) f ψ)
    (hvs : WeightedWeakSolution Q (fun z => β.val • PhysicalCore.fullMatrix s N hN K θ η κ₀
      (WithLp.toLp 2 (fun i => 1+z.val i))) (zeroSumComponents _) f v)
    (hg : ∀ᵐ z ∂fullIntrinsicTiltedGapLaw (ofLong β s) N θ η false, ∀ i, g i z = ∑ j,
      (hessianMatrix U (WithLp.toLp 2 (fun k => 1+z.val k)) i j -
        β.val*PhysicalCore.fullMatrix s N hN K θ η κ₀ (WithLp.toLp 2 (fun k => 1+z.val k)) i j)*
          (v j).val z) :
    ‖WithLp.toLp 2 (fun i => (ψ i-v i).val)‖ ≤
      (β.val*min 1 (s.val*(s.val+1))*(N : ℝ)^(-(s.val+2)*η))⁻¹ * ‖WithLp.toLp 2 g‖ := by
  let ν := fullIntrinsicTiltedGapLaw (ofLong β s) N θ η false
  let Y := fun z : gapTangentSpace N => WithLp.toLp 2 (fun i => 1+z.val i)
  let H := fun z => hessianMatrix U (Y z)
  let M := fun z => β.val • PhysicalCore.fullMatrix s N hN K θ η κ₀ (Y z)
  let a := β.val*min 1 (s.val*(s.val+1))*(N : ℝ)^(-(s.val+2)*η)
  have ha : 0 < a := mul_pos (mul_pos β.property (lt_min zero_lt_one
    (mul_pos s.property.1 (by linarith [s.property.1]))))
      (Real.rpow_pos_of_pos (by positivity) _)
  have hY : Measurable Y := (PhysicalCollision.intrinsic_chart_contDiff N).continuous.measurable
  have hHm : ∀ i j, Measurable (fun z => H z i j) := fun i j =>
    (DifferentiatedPoisson.measurable_hessian_entries (V := U) i j).comp hY
  have hMm : ∀ i j, Measurable (fun z => M z i j) :=
    AbstractEnergy.scaled_measurable β.val _ (fun i j =>
      (PhysicalCore.measurable_fullMatrix s N hN K θ η κ₀ i j).comp hY)
  have hMs : ∀ᵐ z ∂ν, ∀ i j, M z i j = M z j i := ae_of_all ν (fun z i j =>
    congrArg (fun r : ℝ => β.val*r) (PhysicalCore.fullMatrix_symmetric β s N hN K θ η κ₀ (Y z) i j))
  obtain ⟨B,hB,hbound⟩ := PhysicalCore.fullMatrix_bounded β s N hN K θ η κ₀
  have hMb : ∃ Bm : ℝ, ∀ᵐ z ∂ν, ∀ i j, |M z i j| ≤ Bm := by
    refine ⟨β.val*B,ae_of_all ν (fun z i j => ?_)⟩
    simp only [M,Matrix.smul_apply,smul_eq_mul,abs_mul,abs_of_pos β.property]
    exact mul_le_mul_of_nonneg_left (hbound (Y z) i j) β.property.le
  have hlow := PhysicalIdentity.Internal.full_physical_lower_ae β s N hN θ η hη U hU hv
  have hlow' : ∀ᵐ z ∂ν, ∀ t ∈ zeroSumComponents (Fin (N : ℕ)),
      a*(∑ i,t i^2) ≤ ∑ i,∑ j,t i*H z i j*t j := by
    filter_upwards [hlow] with z hz t _
    simpa only [a,mul_assoc] using hz t
  have hHb : ∀ᵐ z ∂ν, (H z).PosSemidef := by
    obtain ⟨V,_,_,hG,_⟩ := PhysicalFormDomain.full_trace_inputs β s N hN θ η
    filter_upwards [hlow,IntrinsicScalarCore.supported (AffineMetric.intrinsicGapDomain_isOpen N) hG]
      with z hz hsupp
    have hx := PhysicalEnergy.simplex_subset_ambient N (Y z)
      (PhysicalCollision.intrinsic_chart_mem_simplex N hsupp)
    have hs := hU.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hx)
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    constructor
    · ext i j
      simp only [H,Matrix.conjTranspose_apply,star_trivial,Intrinsic.hessianMatrix_eq_second hs]
      exact hs.isSymmSndFDerivAt (by simp) _ _
    · intro t
      have hh := (mul_nonneg ha.le (Finset.sum_nonneg (fun i _ => sq_nonneg (t i)))).trans
        (show a*(∑ i,t i^2) ≤ ∑ i,∑ j,t i*H z i j*t j by simpa only [a,mul_assoc] using hz t)
      simpa only [dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,Finset.mul_sum,mul_assoc] using hh
  have hh := (NaturalMatrixPerturbation.internal_comparison Q hQ H M hHm hMm hHb hMb hMs
    (zeroSumComponents _) a ha hlow' f g ψ v hψ hvs hg).1
  exact hh

end Internal

/-- Supporting the proof of Theorem 1: the
physical and auxiliary constrained solutions differ by the actual L²
residual divided by the physical coercivity mass. This estimate is uniform
on compact temperature intervals and keeps every polynomial factor visible.
Both solutions use the same scalar form and natural finite-energy domain. -/
theorem physical_auxiliary_error (hRig : External.LongRangeRigidityLocallyUniform)
    (s : Riesz1.RieszExponent) (M₀ : ℕ) :
    ∃ c₀ κ : ℝ, 0 < c₀ ∧ 0 < κ ∧
      ∀ {η Cθ : ℝ}, 0 < η → 1 ≤ Cθ →
      ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (β : InverseTemperature), β.val ∈ Icc βlo βhi →
      ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ κ₀ : ℝ, 1 ≤ κ₀ →
      let K := ⌊(N : ℝ)^η⌋₊^M₀
      K ≤ (N : ℕ)/4 →
      ∀ U : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain N) →
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        U y.val = fullPhysicalPotentialValue (ofLong β s) N hN θ η false y) →
      let ν := fullIntrinsicTiltedGapLaw (ofLong β s) N θ η false
      let Y := fun z : gapTangentSpace N => WithLp.toLp 2 (fun i => 1+z.val i)
      let H := fun z => hessianMatrix U (Y z)
      let M := fun z => β.val • PhysicalCore.fullMatrix s N hN K θ η κ₀ (Y z)
      ∀ Q : ScalarFormData ν, IsClosedScalarDirichletForm Q →
      ∀ (i₀ : Fin (N : ℕ)) (χ : Lp ℝ 2 ν), eLpNorm χ ∞ ν < ⊤ →
      ∀ ψ v : Fin (N : ℕ) → Q.1,
      WeightedWeakSolution Q H (zeroSumComponents _) (fun i => if i=i₀ then χ else 0) ψ →
      WeightedWeakSolution Q M (zeroSumComponents _) (fun i => if i=i₀ then χ else 0) v →
      ‖WithLp.toLp 2 (fun i => (ψ i-v i).val)‖ ≤
        (β.val*min 1 (s.val*(s.val+1))*(N : ℝ)^(-(s.val+2)*η))⁻¹ *
          ((N : ℝ)^4*((β.val*c₀*(N : ℝ)^(-κ*η))⁻¹*(eLpNorm χ ∞ ν).toReal) *
            (C*Real.exp (-c*(N : ℝ)^GoodBlocks.coefficientTailPower s.val η))) := by
  obtain ⟨c₀,κ,hc₀,hκ,hr⟩ := auxiliary_residual hRig s M₀
  refine ⟨c₀,κ,hc₀,hκ,?_⟩
  intro η Cθ hη hCθ βlo βhi hlo hle
  obtain ⟨C,c,hC,hc,hr⟩ := hr hη hCθ βlo βhi hlo hle
  refine ⟨C,c,hC,hc,?_⟩
  intro β hβ N hN θ hcurv κ₀ hκ₀ K hKN U hU hv ν Y H M Q hQ i₀ χ hχ ψ v hψ hvs
  obtain ⟨g,hg,hgn⟩ := hr β hβ N hN θ hcurv κ₀ hκ₀ hKN U hU hv Q hQ i₀ χ hχ v hvs
  have hh := Internal.physical_perturbation_error β s N hN K θ η κ₀ hη.le U hU hv Q hQ
    (fun i => if i=i₀ then χ else 0) g ψ v hψ hvs hg
  have ha : 0 < β.val*min 1 (s.val*(s.val+1))*(N : ℝ)^(-(s.val+2)*η) :=
    mul_pos (mul_pos β.property (lt_min zero_lt_one
      (mul_pos s.property.1 (by linarith [s.property.1]))))
        (Real.rpow_pos_of_pos (by positivity) _)
  exact hh.trans (mul_le_mul_of_nonneg_left hgn (inv_nonneg.mpr ha.le))

end Riesz2.FullCycleComparison
