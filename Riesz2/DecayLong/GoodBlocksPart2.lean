/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.GoodBlocks
public import Riesz2.ToMathlib.CyclicIntervalHessianBounds
public import Riesz2.ToMathlib.MomentCutoffTail
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Physical Hessian moments

Continuation of Subsection 5.1. The finite interval matrix below
is identified with the Hessian of the short-interval ambient energy.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology ContDiff

namespace Riesz2.GoodBlocks

/-- See Subsection 5.1 of the paper, full-cycle case: the actual ambient Hessian
evaluated on particle gaps, in its interval representation. The derivative
identification is `particleHessian_eq_second`. -/
def particleHessian (p : Parameters) (N : ℕ+) (a b : Fin (N : ℕ))
    (X : Riesz1.Configuration N) : ℝ :=
  ∑ r : Fin ((N : ℕ) / 2), ∑ i : Fin (N : ℕ),
    if a ∈ cyclicIndexInterval N i (r.val + 1) ∧
      b ∈ cyclicIndexInterval N i (r.val + 1) then
        particleCoefficient p N i.val (r.val + 1) (by omega) (by have := r.isLt; omega) X
      else 0

theorem measurable_particleHessian (p : Parameters) (N : ℕ+) (a b : Fin (N : ℕ)) :
    Measurable (particleHessian p N a b) := by
  classical
  apply Finset.measurable_sum
  intro r _
  apply Finset.measurable_sum
  intro i _
  by_cases h : a ∈ cyclicIndexInterval N i (r.val + 1) ∧
      b ∈ cyclicIndexInterval N i (r.val + 1)
  · simpa only [h, and_self, ↓reduceIte] using measurable_particleCoefficient p N i.val
      (r.val + 1) (by omega) (by have := r.isLt; omega)
  · simp only [h, ↓reduceIte]
    exact measurable_const

theorem particleHessian_nonneg (p : Parameters) (N : ℕ+) (a b : Fin (N : ℕ))
    (X : Riesz1.Configuration N) : 0 ≤ particleHessian p N a b X := by
  apply Finset.sum_nonneg
  intro r _
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact (particleCoefficient_pos p N _ _ _ _ X).le
  · exact le_rfl

theorem particleHessian_symmetric (p : Parameters) (N : ℕ+) (a b : Fin (N : ℕ))
    (X : Riesz1.Configuration N) :
    particleHessian p N a b X = particleHessian p N b a X := by
  simp only [particleHessian, and_comm]

/-- See Subsection 5.1 of the paper: the interval matrix is exactly the bilinear
second derivative of a smooth representative of the ambient energy.
The equality holds at every configuration, including antipodal intervals. -/
theorem particleHessian_eq_second (p : Parameters) (N : ℕ+) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ∀ (X : Riesz1.Configuration N) (a b : Fin (N : ℕ)),
        fderiv ℝ (fderiv ℝ W) (WithLp.toLp 2 (gapVector X))
          (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) =
            particleHessian p N a b X := by
  classical
  obtain ⟨W, hW, hval, hjet⟩ := PhysicalEnergy.ambient_derivatives p N
  refine ⟨W, hW, hval, fun X a b => ?_⟩
  rw [(hjet ⟨WithLp.toLp 2 (gapVector X),
    GapChart.gapVector_mem_gapAmbientDomain X⟩ _ _).2, particleHessian,
    Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro i _
  rw [particleCoefficient_gapVector]
  have ha : cyclicGapSum N i (r.val + 1)
      (WithLp.ofLp (EuclideanSpace.single a (1 : ℝ))) =
        if a ∈ cyclicIndexInterval N i (r.val + 1) then 1 else 0 := by
    convert cyclicGapSum_single N i a (show r.val + 1 ≤ (N : ℕ) by have := r.isLt; omega)
      using 1
    congr 1
    ext j
    simp [EuclideanSpace.single, eq_comm]
  have hb : cyclicGapSum N i (r.val + 1)
      (WithLp.ofLp (EuclideanSpace.single b (1 : ℝ))) =
        if b ∈ cyclicIndexInterval N i (r.val + 1) then 1 else 0 := by
    convert cyclicGapSum_single N i b (show r.val + 1 ≤ (N : ℕ) by have := r.isLt; omega)
      using 1
    congr 1
    ext j
    simp [EuclideanSpace.single, eq_comm]
  rw [ha, hb]
  by_cases hia : a ∈ cyclicIndexInterval N i (r.val + 1) <;>
    by_cases hib : b ∈ cyclicIndexInterval N i (r.val + 1) <;>
    simp only [hia, hib, and_self, and_false, false_and, ↓reduceIte, mul_one, mul_zero]

/-- See Subsection 5.1 of the paper, bridge to the `hessianMatrix`
convention. This controls ambient entries, not only tangent compressions. -/
theorem particleHessian_eq_matrix (p : Parameters) (N : ℕ+) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ∀ (X : Riesz1.Configuration N) (a b : Fin (N : ℕ)),
        hessianMatrix W (WithLp.toLp 2 (gapVector X)) a b = particleHessian p N a b X := by
  obtain ⟨W, hW, hval, hjet⟩ := particleHessian_eq_second p N
  refine ⟨W, hW, hval, fun X a b => ?_⟩
  have hx := GapChart.gapVector_mem_gapAmbientDomain X
  have hs := hW.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hx)
  have hd : DifferentiableAt ℝ (fderiv ℝ W) (WithLp.toLp 2 (gapVector X)) :=
    (hs.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he := Riesz1.inner_fderiv_gradient hd
    (EuclideanSpace.single b 1) (EuclideanSpace.single a 1)
  rw [EuclideanSpace.inner_single_right] at he
  simp only [one_mul] at he
  exact he.trans ((hjet X b a).trans (particleHessian_symmetric p N b a X))

/-- See Subsection 5.1 of the paper, full-cycle Hessian moment clause, also valid
before taking any active marginal. The sharp moment degree and spatial
exponent retain no temperature dependence. Prefactors are uniform on compact
temperature intervals and for cutoffs of bounded curvature. -/
theorem tilted_hessian_moments (s βlo βhi ε Cθ : ℝ) (hs : 0 < s)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (hε : 0 < ε) (hCθ : 1 ≤ Cθ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Parameters), p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (N n : ℕ+), 2 ≤ (N : ℕ) →
      ∀ (hn : (n : ℕ) ≤ (N : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ (a b : Fin (N : ℕ)) (q : ℝ), 1 ≤ q →
        eLpNorm (particleHessian p N a b) (ENNReal.ofReal q)
          (tiltedParticleMeasure p N n hn θ ε false) ≤ ENNReal.ofReal
            (C * q ^ ((s + 2) / s) *
              (1 + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-s)) := by
  obtain ⟨D, hD, hcoeff⟩ := tilted_coefficient_moments s βlo βhi ε Cθ hs hlo hle hε hCθ
  refine ⟨D * (1 + 1 / s), by positivity, ?_⟩
  intro p hps hpl hph N n hN hn θ hcurv a b q hq
  have hh := interval_matrix_eLpNorm_le
    (tiltedParticleMeasure p N n hn θ ε false) N hs hq
    (show 0 ≤ D * q ^ ((s + 2) / s) by positivity)
    (fun i r => particleCoefficient p N i.val (r.val + 1) (by omega)
      (by have := r.isLt; omega))
    (fun i r => by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (hcoeff p hps hpl hph N n hN hn θ hcurv i.val
          (r.val + 1) (by omega) (by have := r.isLt; omega) q hq)) a b
  calc
    _ ≤ ENNReal.ofReal ((D * q ^ ((s + 2) / s)) * (1 + 1 / s) *
        (1 + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-s)) := hh
    _ = _ := by congr 1; ring

/-- See Subsection 5.1 of the paper, pulled back to configurations in the full-cycle
case `n=N`. All coordinates are already on the actual open mass simplex.
The Hessian is the density-free direct Hessian required by Subsection 5.1. -/
def fullGoodEvent (p : Parameters) (N : ℕ+) (ε κ : ℝ) : Set (Riesz1.Configuration N) :=
  {X | ((∀ i : Fin (N : ℕ),
      (N : ℝ) ^ (-ε) ≤ gap X i.val ∧ gap X i.val ≤ (N : ℝ) ^ ε) ∧
    ∀ (j : Fin (N : ℕ)) (k : Fin ((N : ℕ) + 1)),
      1 ≤ k.val → k.val ≤ (N : ℕ) / 2 →
        |Riesz1.blockLength X j.val k.val - (k.val : ℝ)| ≤
          (N : ℝ) ^ ε * (k.val : ℝ) ^ (p.val.2 / 2)) ∧
    ∀ a b : Fin (N : ℕ), particleHessian p N a b X ≤
      (N : ℝ) ^ (κ * ε) *
        (1 + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-p.val.2)}

theorem measurableSet_fullGoodEvent (p : Parameters) (N : ℕ+) (ε κ : ℝ) :
    MeasurableSet (fullGoodEvent p N ε κ) := by
  have hall {ι : Type} [Countable ι] {P : ι → Riesz1.Configuration N → Prop}
      (h : ∀ i, MeasurableSet {x | P i x}) : MeasurableSet {x | ∀ i, P i x} := by
    simpa only [ofPred_forall] using MeasurableSet.iInter h
  unfold fullGoodEvent
  apply MeasurableSet.inter
  · apply MeasurableSet.inter
    · exact hall fun i : Fin (N : ℕ) =>
        (measurableSet_le measurable_const (Riesz1.measurable_gap i.val)).inter
          (measurableSet_le (Riesz1.measurable_gap i.val) measurable_const)
    · exact hall fun j : Fin (N : ℕ) => hall fun k : Fin ((N : ℕ) + 1) =>
        MeasurableSet.imp (measurable_const (a := 1 ≤ k.val)).setOf
          (MeasurableSet.imp (measurable_const (a := k.val ≤ (N : ℕ) / 2)).setOf
            (measurableSet_le ((Riesz1.measurable_blockLength j.val k.val).sub_const _).abs
              measurable_const))
  · exact hall fun a : Fin (N : ℕ) => hall fun b : Fin (N : ℕ) =>
      measurableSet_le (measurable_particleHessian p N a b) measurable_const

/-- See Subsection 5.1 of the paper, exceptional probability for the full cycle.
The specified exponent is exactly `coefficientTailPower`, fixed before
temperature. All prefactors are uniform on compact temperature intervals. -/
theorem full_good_event (hRig : External.LongRangeRigidityLocallyUniform)
    (s : Riesz1.RieszExponent) {ε Cθ : ℝ} (hε : 0 < ε) (hCθ : 1 ≤ Cθ)
    (βlo βhi : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (β : InverseTemperature), β.val ∈ Icc βlo βhi →
      ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ θ : PhysicalCutoff,
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ κ : ℝ, 1 ≤ κ →
        (tiltedParticleMeasure (ofLong β s) N N le_rfl θ ε false)
          (fullGoodEvent (ofLong β s) N ε κ)ᶜ ≤
            ENNReal.ofReal (C * Real.exp (-c * (N : ℝ) ^ coefficientTailPower s.val ε)) := by
  classical
  obtain ⟨B, b, hB, hb, _, hblocks⟩ :=
    uniform_good_blocks hRig s hε hCθ βlo βhi hlo hle
  obtain ⟨M, hM, hmom⟩ := tilted_hessian_moments s.val βlo βhi ε Cθ
    s.property.1 hlo hle hε hCθ
  have hA : 0 < (s.val + 2) / s.val := by have := s.property.1; positivity
  obtain ⟨D, d, hD, hd, hcut⟩ := MomentEvent.finite_moment_cutoffs hA hε hM
  refine ⟨B + D, min b d, by positivity, lt_min hb hd, ?_⟩
  intro β hβ N hN θ hcurv κ hκ
  let μ := tiltedParticleMeasure (ofLong β s) N N le_rfl θ ε false
  have hμ : IsProbabilityMeasure μ := DefinitionSanity.tilted_probability _ _ _ _ _ _ _
  let := hμ
  let Y : (Fin (N : ℕ) × Fin (N : ℕ)) → Riesz1.Configuration N → ℝ :=
    fun ab => particleHessian (ofLong β s) N ab.1 ab.2
  let w : (Fin (N : ℕ) × Fin (N : ℕ)) → ℝ :=
    fun ab => (1 + (Riesz1.cyclicIndexDistance N ab.1 ab.2 : ℝ)) ^ (-s.val)
  let E : Set (Riesz1.Configuration N) := {X | ∃ ab, (N : ℝ) ^ (κ * ε) * w ab < |Y ab X|}
  have hcoeff := hcut N (by omega) μ Y w κ (by simp [sq])
    (fun ab => measurable_particleHessian _ _ _ _)
    (fun ab => by dsimp [w]; positivity) hκ
    (fun ab q hq => hmom (ofLong β s) rfl hβ.1 hβ.2 N N hN le_rfl θ hcurv ab.1 ab.2 q hq)
  let G : Set (Riesz1.Configuration N) := {X | ¬ ((∀ i : Fin (N : ℕ),
      (N : ℝ) ^ (-ε) ≤ gap X i.val ∧ gap X i.val ≤ (N : ℝ) ^ ε) ∧
    ∀ (j : Fin (N : ℕ)) (k : Fin ((N : ℕ) + 1)),
      1 ≤ k.val → k.val ≤ (N : ℕ) / 2 →
        |Riesz1.blockLength X j.val k.val - (k.val : ℝ)| ≤
          (N : ℝ) ^ ε * (k.val : ℝ) ^ (s.val / 2))}
  have hgap : μ G ≤ ENNReal.ofReal (B * Real.exp (-b * (N : ℝ) ^ blockTailPower s.val ε)) := by
    simpa only [μ, G, ofLong, longParameters, true_or, implies_true, forall_const,
      or_true, true_implies] using (hblocks β hβ N N hN le_rfl (Or.inl rfl) θ hcurv).1
  have hsub : (fullGoodEvent (ofLong β s) N ε κ)ᶜ ⊆ G ∪ E := by
    intro X hX
    by_cases hg : X ∈ G
    · exact Or.inl hg
    · right
      have hgood : ¬ X ∈ fullGoodEvent (ofLong β s) N ε κ := hX
      have hfirst : ¬¬ ((∀ i : Fin (N : ℕ),
          (N : ℝ) ^ (-ε) ≤ gap X i.val ∧ gap X i.val ≤ (N : ℝ) ^ ε) ∧
        ∀ (j : Fin (N : ℕ)) (k : Fin ((N : ℕ) + 1)),
          1 ≤ k.val → k.val ≤ (N : ℕ) / 2 →
            |Riesz1.blockLength X j.val k.val - (k.val : ℝ)| ≤
              (N : ℝ) ^ ε * (k.val : ℝ) ^ (s.val / 2)) := hg
      have hex : ∃ a b : Fin (N : ℕ), (N : ℝ) ^ (κ * ε) *
          (1 + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-s.val) <
            particleHessian (ofLong β s) N a b X := by
        have hnot : ¬ ∀ a b : Fin (N : ℕ), particleHessian (ofLong β s) N a b X ≤
            (N : ℝ) ^ (κ * ε) * (1 + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-s.val) :=
          fun hp => hgood ⟨Classical.not_not.mp hfirst, hp⟩
        simpa only [not_forall, not_le] using hnot
      obtain ⟨a, b, hab⟩ := hex
      refine ⟨(a, b), ?_⟩
      simpa only [Y, w, abs_of_nonneg (particleHessian_nonneg _ _ _ _ _)] using hab
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hcompare (a t C₀ : ℝ) (ha : min b d ≤ a)
      (ht : coefficientTailPower s.val ε ≤ t) (hC₀ : 0 ≤ C₀) :
      ENNReal.ofReal (C₀ * Real.exp (-a * (N : ℝ) ^ t)) ≤
        ENNReal.ofReal (C₀ * Real.exp (-(min b d) * (N : ℝ) ^ coefficientTailPower s.val ε)) := by
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hC₀
    apply Real.exp_le_exp.mpr
    have ha0 : 0 ≤ a := (lt_min hb hd).le.trans ha
    have hh := mul_le_mul ha (Real.rpow_le_rpow_of_exponent_le hn1 ht)
      (by positivity : 0 ≤ (N : ℝ) ^ coefficientTailPower s.val ε) ha0
    linarith
  calc
    μ (fullGoodEvent (ofLong β s) N ε κ)ᶜ ≤ μ (G ∪ E) := measure_mono hsub
    _ ≤ μ G + μ E := measure_union_le _ _
    _ ≤ ENNReal.ofReal (B * Real.exp (-b * (N : ℝ) ^ blockTailPower s.val ε)) +
        ENNReal.ofReal (D * Real.exp (-d * (N : ℝ) ^ (ε / (2 * ((s.val + 2) / s.val))))) :=
      add_le_add hgap hcoeff
    _ ≤ _ := by
      have hh := add_le_add
        (hcompare b (blockTailPower s.val ε) B (min_le_left _ _)
          (min_le_left _ _) hB.le)
        (hcompare d (ε / (2 * ((s.val + 2) / s.val))) D (min_le_right _ _)
          (min_le_right _ _) hD.le)
      refine hh.trans_eq ?_
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- See Subsection 5.1 of the paper, exceptional restricted `L²` norm for the full
cycle. This uses the actual coefficient-augmented good event, and its tail
power is unchanged by Hölder. -/
theorem full_exceptional_hessian (hRig : External.LongRangeRigidityLocallyUniform)
    (s : Riesz1.RieszExponent) {ε Cθ : ℝ} (hε : 0 < ε) (hCθ : 1 ≤ Cθ)
    (βlo βhi : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (β : InverseTemperature), β.val ∈ Icc βlo βhi →
      ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ θ : PhysicalCutoff,
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ κ : ℝ, 1 ≤ κ → ∀ a b : Fin (N : ℕ),
        eLpNorm (particleHessian (ofLong β s) N a b) 2
          ((tiltedParticleMeasure (ofLong β s) N N le_rfl θ ε false).restrict
            (fullGoodEvent (ofLong β s) N ε κ)ᶜ) ≤
          ENNReal.ofReal (C * Real.exp (-c * (N : ℝ) ^ coefficientTailPower s.val ε)) := by
  obtain ⟨B, c, hB, hc, hprob⟩ := full_good_event hRig s hε hCθ βlo βhi hlo hle
  obtain ⟨M, hM, hmom⟩ := tilted_hessian_moments s.val βlo βhi ε Cθ
    s.property.1 hlo hle hε hCθ
  refine ⟨M * (4 : ℝ) ^ ((s.val + 2) / s.val) * B ^ (1 / 4 : ℝ), c / 4,
    by positivity, by positivity, ?_⟩
  intro β hβ N hN θ hcurv κ hκ a b
  have hsp : (1 + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-s.val) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact le_add_of_nonneg_right (Nat.cast_nonneg _))
      (by have := s.property.1; linarith)
  have h4 : eLpNorm (particleHessian (ofLong β s) N a b) 4
      (tiltedParticleMeasure (ofLong β s) N N le_rfl θ ε false) ≤
        ENNReal.ofReal (M * (4 : ℝ) ^ ((s.val + 2) / s.val)) := by
    have hh := hmom (ofLong β s) rfl hβ.1 hβ.2 N N hN le_rfl θ hcurv a b 4 (by norm_num)
    norm_num only [ENNReal.ofReal_ofNat] at hh
    refine hh.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_of_le_one_right (by positivity) hsp
  have hh := MomentEvent.restricted_two_norm_le (measurable_particleHessian _ _ _ _)
    (fullGoodEvent (ofLong β s) N ε κ)ᶜ
    (t := c * (N : ℝ) ^ coefficientTailPower s.val ε) (by positivity) hB.le h4
    (by simpa only [neg_mul] using hprob β hβ N hN θ hcurv κ hκ)
  convert hh using 1
  congr 3
  ring

end Riesz2.GoodBlocks
