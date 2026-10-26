/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.PhysicalDecayPart7
public import Riesz2.DecayShort.ObservableTransfer
public import Riesz2.DecayLong.LowerCorrelations
public import Riesz2.Bridges.CyclicLabels
public import Riesz2.ToMathlib.CyclicIntervals
public import Riesz2.ToMathlib.CyclicDistance
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Cyclic transport of the short-range physical law

The cyclic-interval step in the proof of Theorem 2: the ordered
active coordinates of an arbitrary cyclic interval have exactly the first-block tilted law. Thus its potential, scalar form and physical equation
can be used without changing coordinates on the active Euclidean space.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Riesz2.DecayShort.ShortRangeResult

/-- The iterated particle relabelling shifts every integer gap label.
See the proof of Theorem 2 in the paper, using Subsection 2.2. -/
theorem gap_cycleConfig_iterate {N : ℕ+} (k : ℕ)
    (X : Riesz1.Configuration N) (j : ℤ) :
    gap ((GapSymmetries.cycleConfig (N := N))^[k] X) j = gap X (j + k) := by
  induction k generalizing j with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', GapSymmetries.gap_cycleConfig, ih]
    congr 1
    push_cast
    ring

/-- Reduce the cyclic starting point before iterating the particle symmetry.
See the proof of Theorem 2 in the paper. Negative and wrapping starting points are included. -/
theorem gap_cycleConfig_label {N : ℕ+} (a j : ℤ) (X : Riesz1.Configuration N) :
    gap ((GapSymmetries.cycleConfig (N := N))^[(Riesz1.labelOf N a).val] X) j =
      gap X (a + j) := by
  rw [gap_cycleConfig_iterate, gap_eq_gapVector_labelOf, gap_eq_gapVector_labelOf]
  congr 1
  apply (Riesz1.labelOf_eq_iff_emod N _ _).2
  rw [Riesz1.labelOf_val_int]
  simp only [Int.add_emod, Int.emod_emod, add_comm]

/-- Sum a function over a cyclic interval in its ordered local coordinates.
See the proof of Theorem 2 in the paper, active interval bookkeeping. -/
theorem sum_cyclicInterval {N n : ℕ+} (hn : (n : ℕ) ≤ (N : ℕ))
    (a : ℤ) (f : Fin (N : ℕ) → ℝ) :
    ∑ i ∈ cyclicInterval N a n, f i =
      ∑ i : Fin (n : ℕ), f (Riesz1.labelOf N (a + i.val)) := by
  have hinj : Set.InjOn (fun k : ℕ => Riesz1.labelOf N (a + k)) (Finset.range n) := by
    apply Finset.card_image_iff.mp
    change (cyclicInterval N a n).card = (Finset.range (n : ℕ)).card
    rw [card_cyclicInterval a hn, Finset.card_range]
  rw [cyclicInterval, Finset.sum_image hinj]
  exact (Fin.sum_univ_eq_sum_range (fun k : ℕ => f (Riesz1.labelOf N (a + k))) n).symm

/-- The arbitrary-interval penalty is the pullback of the first-block penalty. See Subsection 4.4 and the proof of Theorem 2 of the paper. -/
theorem activeGapPenalty_cyclicInterval {N n : ℕ+} (hn : (n : ℕ) ≤ (N : ℕ))
    (θ : PhysicalCutoff) (h : ℝ) (b : Bool) (a : ℤ) (X : Riesz1.Configuration N) :
    activeGapPenalty θ ((n : ℝ)^h) b (cyclicInterval N a n) X =
      physicalGapPenalty N n hn θ h b
        ((GapSymmetries.cycleConfig (N := N))^[(Riesz1.labelOf N a).val] X) := by
  rw [activeGapPenalty, sum_cyclicInterval hn]
  unfold physicalGapPenalty
  apply Finset.sum_congr rfl
  intro i _
  rw [gap_cycleConfig_label, Real.rpow_neg (Nat.cast_nonneg _) h]
  have he := gap_eq_gapVector_labelOf X (a + i.val)
  change gap X (a + i.val) = gap X ((Riesz1.labelOf N (a + i.val)).val : ℕ) at he
  rw [← he]
  simp only [div_eq_inv_mul, mul_inv, mul_one]

/-- Internal transport of a normalized exponential tilt by a measure-preserving
map. No injectivity or integrability assumption is needed for this measure identity. -/
theorem internal_map_expTilt {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {T : α → β} (hT : MeasurePreserving T μ ν)
    (b : ℝ) {F : β → ℝ} (hF : Measurable F) :
    (NonnegativeTilt.expTilt μ b (F ∘ T)).map T =
      NonnegativeTilt.expTilt ν b F := by
  let g := fun x => ENNReal.ofReal (Real.exp (-b * F x))
  have hg : Measurable g := ((hF.const_mul (-b)).exp).ennreal_ofReal
  have hZ : ∫⁻ x, g (T x) ∂μ = ∫⁻ y, g y ∂ν :=
    hT.lintegral_comp hg
  have hmap : (μ.withDensity (g ∘ T)).map T = ν.withDensity g := by
    ext s hs
    rw [Measure.map_apply hT.measurable hs,
      withDensity_apply _ (hT.measurable hs), withDensity_apply _ hs]
    exact hT.setLIntegral_comp_preimage hs hg
  unfold NonnegativeTilt.expTilt
  change ((∫⁻ x, g (T x) ∂μ)⁻¹ • μ.withDensity (g ∘ T)).map T =
    (∫⁻ y, g y ∂ν)⁻¹ • ν.withDensity g
  rw [Measure.map_smul _ hT.measurable.aemeasurable, hZ, hmap]

/-- Relabelling an arbitrary cyclic active tilt gives the first-block
particle tilt. See Subsection 4.4 and the proof of Theorem 2 of the paper. -/
theorem activeTilt_cyclicInterval_map (p : Parameters) {N n : ℕ+}
    (hN : 2 ≤ (N : ℕ)) (hn : (n : ℕ) ≤ (N : ℕ))
    (θ : PhysicalCutoff) (h : ℝ) (b : Bool) (a : ℤ) :
    (activeTilt p N θ ((n : ℝ)^h) b (cyclicInterval N a n)).map
      ((GapSymmetries.cycleConfig (N := N))^[(Riesz1.labelOf N a).val]) =
        tiltedParticleMeasure p N n hn θ h b := by
  have hT : MeasurePreserving (GapSymmetries.cycleConfig (N := N))
      (gibbsMeasure p N) (gibbsMeasure p N) :=
    ⟨GapSymmetries.measurable_cycleConfig, LowerCorrelations.gibbsMeasure_map_cycle p N hN⟩
  have hF : Measurable (physicalGapPenalty N n hn θ h b) := by
    rw [← activeGapPenalty_firstGapSet hn θ h b]
    exact activeGapPenalty_measurable θ (Real.rpow_nonneg (Nat.cast_nonneg _) h) b _
  have he : activeGapPenalty θ ((n : ℝ)^h) b (cyclicInterval N a n) =
      physicalGapPenalty N n hn θ h b ∘
        ((GapSymmetries.cycleConfig (N := N))^[(Riesz1.labelOf N a).val]) :=
    funext (activeGapPenalty_cyclicInterval hn θ h b a)
  rw [activeTilt, he, internal_map_expTilt (hT.iterate _) p.val.1 hF]
  rfl

/-- The arbitrary-interval extended normalizer equals the first-block normalizer.
See Subsection 4.4 and the proof of Theorem 2 of the paper. -/
theorem activeTilt_cyclicInterval_normalizer (p : Parameters) {N n : ℕ+}
    (hN : 2 ≤ (N : ℕ)) (hn : (n : ℕ) ≤ (N : ℕ))
    (θ : PhysicalCutoff) (h : ℝ) (b : Bool) (a : ℤ) :
    (∫⁻ X, ENNReal.ofReal (Real.exp (-p.val.1 *
      activeGapPenalty θ ((n : ℝ)^h) b (cyclicInterval N a n) X)) ∂gibbsMeasure p N) =
        tiltNormalizer p N n hn θ h b := by
  have hT : MeasurePreserving (GapSymmetries.cycleConfig (N := N))
      (gibbsMeasure p N) (gibbsMeasure p N) :=
    ⟨GapSymmetries.measurable_cycleConfig, LowerCorrelations.gibbsMeasure_map_cycle p N hN⟩
  have hF : Measurable (physicalGapPenalty N n hn θ h b) := by
    rw [← activeGapPenalty_firstGapSet hn θ h b]
    exact activeGapPenalty_measurable θ (Real.rpow_nonneg (Nat.cast_nonneg _) h) b _
  simp_rw [activeGapPenalty_cyclicInterval hn θ h b a]
  exact (hT.iterate _).lintegral_comp ((hF.const_mul (-p.val.1)).exp.ennreal_ofReal)

/-- The ordered coordinates of any cyclic interval have the exact first-block tilted gap law. See the proof of Theorem 2 in the paper. -/
theorem activeTilt_cyclicInterval_gapLaw (p : Parameters) {N n : ℕ+}
    (hN : 2 ≤ (N : ℕ)) (hn : (n : ℕ) ≤ (N : ℕ))
    (θ : PhysicalCutoff) (h : ℝ) (b : Bool) (a : ℤ) :
    (activeTilt p N θ ((n : ℝ)^h) b (cyclicInterval N a n)).map
      (fun X => WithLp.toLp 2 (fun i : Fin (n : ℕ) => gap X (a + i.val))) =
        activeTiltedGapLaw p N n hn θ h b := by
  have hB : Measurable (fun X : Riesz1.Configuration N =>
      WithLp.toLp 2 (finiteGapBlock (K := n) X)) :=
    (WithLp.measurable_toLp 2 _).comp
      (measurable_pi_iff.mpr fun i : Fin (n : ℕ) => Riesz1.measurable_gap i.val)
  rw [activeTiltedGapLaw, ← activeTilt_cyclicInterval_map p hN hn θ h b a,
    Measure.map_map hB (GapSymmetries.measurable_cycleConfig.iterate _)]
  congr 1
  funext X
  ext i
  exact (gap_cycleConfig_label a i.val X).symm

/-- Covariances of active coordinate observables are exactly the covariances
under the marginal. See the proof of Theorem 2 and Theorem 1 of the paper.
The observables are Lipschitz. -/
theorem covariance_cyclicInterval (p : Parameters) {N n : ℕ+}
    (hN : 2 ≤ (N : ℕ)) (hn : (n : ℕ) ≤ (N : ℕ))
    (θ : PhysicalCutoff) (h : ℝ) (b : Bool) (a : ℤ)
    (ξ χ : GapObservable) (i j : Fin (n : ℕ)) :
    ProbabilityTheory.covariance
      (fun X => ξ.val.1 (gap X (a + i.val)))
      (fun X => χ.val.1 (gap X (a + j.val)))
      (activeTilt p N θ ((n : ℝ)^h) b (cyclicInterval N a n)) =
    ProbabilityTheory.covariance (fun y : EuclideanSpace ℝ (Fin (n : ℕ)) => ξ.val.1 (y i))
      (fun y => χ.val.1 (y j)) (activeTiltedGapLaw p N n hn θ h b) := by
  obtain ⟨Lξ,hξ⟩ := ξ.property.1
  obtain ⟨Lχ,hχ⟩ := χ.property.1
  rw [← activeTilt_cyclicInterval_gapLaw p hN hn θ h b a]
  symm
  exact ProbabilityTheory.covariance_map_fun
    (hξ.continuous.measurable.comp (by fun_prop)).aestronglyMeasurable
    (hχ.continuous.measurable.comp (by fun_prop)).aestronglyMeasurable
    ((WithLp.measurable_toLp 2 _).comp
      (measurable_pi_iff.mpr fun i : Fin (n : ℕ) => Riesz1.measurable_gap (a + i.val))).aemeasurable

/-- Internal seminorm transport for any measurable class on the active marginal.
This includes derivative representatives once their marginal measurability has
been established. See the proof of Theorem 2 in the paper. -/
theorem internal_eLpNorm_cyclicInterval (p : Parameters) {N n : ℕ+}
    (hN : 2 ≤ (N : ℕ)) (hn : (n : ℕ) ≤ (N : ℕ))
    (θ : PhysicalCutoff) (h : ℝ) (b : Bool) (a : ℤ)
    {f : EuclideanSpace ℝ (Fin (n : ℕ)) → ℝ}
    (hf : AEStronglyMeasurable f (activeTiltedGapLaw p N n hn θ h b)) (r : ℝ≥0∞) :
    eLpNorm (fun X => f (WithLp.toLp 2 (fun i : Fin (n : ℕ) => gap X (a + i.val)))) r
      (activeTilt p N θ ((n : ℝ)^h) b (cyclicInterval N a n)) =
        eLpNorm f r (activeTiltedGapLaw p N n hn θ h b) := by
  rw [← activeTilt_cyclicInterval_gapLaw p hN hn θ h b a] at hf ⊢
  exact (eLpNorm_map_measure hf
    ((WithLp.measurable_toLp 2 _).comp
      (measurable_pi_iff.mpr fun i : Fin (n : ℕ) => Riesz1.measurable_gap (a + i.val))).aemeasurable).symm

/-- The line distance of local coordinates is the ambient cyclic distance on
an active interval of length at most half the cycle. See the proof of Theorem 2 in the paper.
This also covers equal indices and an interval crossing label zero. -/
theorem cyclicInterval_coordinate_distance {N n : ℕ+} (hhalf : 2 * (n : ℕ) ≤ (N : ℕ))
    (a : ℤ) (i j : Fin (n : ℕ)) :
    (Riesz1.cyclicIndexDistance N (Riesz1.labelOf N (a + i.val))
      (Riesz1.labelOf N (a + j.val)) : ℝ) = |(j.val : ℝ) - (i.val : ℝ)| := by
  have hd : 2 * |(a + (j.val : ℤ)) - (a + (i.val : ℤ))| ≤ (N : ℤ) := by
    rw [add_sub_add_left_eq_sub]
    have hb : |(j.val : ℤ) - i.val| ≤ (n : ℤ) := by
      rw [abs_le]
      constructor <;> omega
    omega
  have he := cyclicIndexDistance_labelOf_eq_abs (N := N) hd
  rw [add_sub_add_left_eq_sub] at he
  exact_mod_cast he

/-- The proper physical equation and its decay estimate hold for the actual
ordered coordinates of every cyclic active interval. See the proof of Theorem 2 in the paper
and Proposition 4.10. The witnesses are transported by equality of measures,
so the potential, Hessian and Neumann form are the existing physical ones.
All constants keep the physical theorem's quantifier order. -/
theorem proper_physical_decay_cyclicInterval :
    ∀ s : ShortExponent, ∃ q : ℝ, 0 < q ∧
    ∀ h : ℝ, 0 < h → ∃ δ : ℝ, 0 < δ ∧
    ∀ θ : PhysicalCutoff, ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
    ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    let p := ofShort β s
    ∀ (N n : ℕ+) (_ : 4 ≤ (N : ℕ)) (_ : 2 ≤ (n : ℕ)),
    2 * (n : ℕ) ≤ (N : ℕ) → ∀ _hn : (n : ℕ) ≤ (N : ℕ), ∀ (b : Bool) (a : ℤ),
    let ν := (activeTilt p N θ ((n : ℝ)^h) b (cyclicInterval N a n)).map
      (fun X => WithLp.toLp 2 (fun i : Fin (n : ℕ) => gap X (a + i.val)))
    let Z := ∫⁻ X, ENNReal.ofReal (Real.exp (-p.val.1 *
      activeGapPenalty θ ((n : ℝ)^h) b (cyclicInterval N a n) X)) ∂gibbsMeasure p N
    0 < Z ∧ Z < ⊤ ∧ IsProbabilityMeasure ν ∧
    ∃ (V : EuclideanSpace ℝ (Fin (n : ℕ)) → ℝ) (Q : ScalarFormData ν),
      IsEuclideanGibbsPotential volume ν (properMarginalDomain n N) V ∧
      IsNeumannRealization (properMarginalDomain n N) Q ∧
      IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
      ∀ i₀ : Fin (n : ℕ), (n : ℕ) ≤ 4 * (i₀.val + 1) →
        4 * (i₀.val + 1) ≤ 3 * (n : ℕ) →
        ∀ χ : Lp ℝ 2 ν, eLpNorm χ ∞ ν < ⊤ →
        (∃! u : Fin (n : ℕ) → Q.1,
          WeightedWeakSolution Q (hessianMatrix V) ⊤ (fun i => if i = i₀ then χ else 0) u) ∧
        (∀ u : Fin (n : ℕ) → Q.1,
          WeightedWeakSolution Q (hessianMatrix V) ⊤ (fun i => if i = i₀ then χ else 0) u →
          ∀ j : Fin (n : ℕ), ENNReal.ofReal ‖(u j).val‖ ≤
            ENNReal.ofReal (A * (n : ℝ) ^ (q * h) *
              ((1 + |(j.val : ℝ) - (i₀.val : ℝ)|) ^ (-s.val) +
                (n : ℝ) ^ (-(s.val - 1 / 2)) + (N : ℝ) ^ (-(1 / 2 : ℝ)))) *
              (ENNReal.ofReal ‖χ‖ + ENNReal.ofReal (Real.exp (-c * (n : ℝ) ^ δ)) *
                eLpNorm χ ∞ ν)) := by
  intro s
  obtain ⟨q,hq,hdec⟩ := PhysicalDecay.physical_decay s
  refine ⟨q,hq,fun h hh => ?_⟩
  obtain ⟨δ,hδ,hdec⟩ := hdec h hh
  refine ⟨δ,hδ,fun θ βlo βhi hlo hle => ?_⟩
  obtain ⟨A,c,hA,hc,hdec⟩ := hdec θ βlo βhi hlo hle
  refine ⟨A,c,hA,hc,fun β hβ N n hN hn2 hhalf hn b a => ?_⟩
  dsimp only
  rw [activeTilt_cyclicInterval_gapLaw (ofShort β s) (by omega) hn θ h b a,
    activeTilt_cyclicInterval_normalizer (ofShort β s) (by omega) hn θ h b a]
  obtain ⟨hZ0,hZt,hprob,V,Q,hV,hNeum,hQ,hcons,hsol⟩ :=
    (hdec β hβ).1 N n hN hn2 hhalf hn b
  exact ⟨hZ0,hZt,hprob,V,Q,hV,hNeum,hQ,hcons,hsol⟩

end Riesz2.DecayShort.ShortRangeResult
