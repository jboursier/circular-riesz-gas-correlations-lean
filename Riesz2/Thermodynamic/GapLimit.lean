/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.GapWeakTests
public import Riesz2.HelfferSjostrand.SingleGapTails
public import Riesz2.ToMathlib.CountableProductTightness
public import Riesz2.ToMathlib.WeakMomentTruncation
public import Riesz2.DecayShort.ShortRangeResultPart4
public import Riesz2.Frozen.MiddleConsecutiveBlock
public import Riesz2.Frozen.DependsOnBlockCoordinates
public import Riesz2.Frozen.BlockDerivativeNorm
public import Riesz2.Frozen.NearOptimalRigidity
public import Riesz2.DecayShort.LocalLawPart3
public import Riesz2.ToMathlib.StretchedCutoffRates
public import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
public import Riesz2.ToMathlib.SummableStretchedExponential

/-!
# The two-sided gap limit

See the proof of Theorem 3 and the periodic laws of Subsection 6.3. The microscopic gap
defines periodic laws on the positive product carrier of `GapWeakTests`. Coordinate
moments give tightness. The ordinary-gap Cauchy estimate gives uniqueness and full weak
convergence. Portmanteau, uniform integrability and Borel–Cantelli give symmetries,
moments, span estimates and almost-sure averages.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz2

/-- See Subsection 6.3 of the paper: the positive, two-sided periodic gap sequence.
Coordinate zero is paper label one. -/
def periodicGapSequence {N : ℕ+} (X : Riesz1.Configuration N) : ℤ → Ioi (0 : ℝ) :=
  fun i => ⟨gap X i, Riesz1.gap_pos X i⟩

/-- The periodic extension is measurable for the product sigma-algebra. -/
lemma measurable_periodicGapSequence (N : ℕ+) :
    Measurable (@periodicGapSequence N) :=
  measurable_pi_iff.mpr fun i => (Riesz1.measurable_gap i).subtype_mk

/-- Boundary check for Subsection 6.3: one particle gives unit gaps at every label. -/
lemma periodicGapSequence_one (X : Riesz1.Configuration 1) (i : ℤ) :
    (periodicGapSequence X i : ℝ) = 1 := by
  change Riesz1.gap X i = 1
  have h := Riesz1.blockLength_N X i
  rw [Riesz1.blockLength_eq_sum] at h
  simpa only [PNat.val_ofNat, Finset.sum_range_one, Nat.cast_one, Int.natCast_zero,
    add_zero] using h

/-- See Subsection 6.3 of the paper: the finite-volume law on two-sided positive gaps.
This is the pushforward of the actual Gibbs probability in either exponent regime. -/
def periodicGapLaw (p : Parameters) (N : ℕ+) : ProbabilityMeasure (ℤ → Ioi (0 : ℝ)) :=
  ProbabilityMeasure.map
    (⟨gibbsMeasure p N, gibbsMeasure_probability p N⟩ :
      ProbabilityMeasure (Riesz1.Configuration N))
    (periodicGapSequence (N := N))

/-- The underlying measure is the measurable pushforward of the Gibbs law. -/
lemma periodicGapLaw_toMeasure (p : Parameters) (N : ℕ+) :
    (periodicGapLaw p N).toMeasure = (gibbsMeasure p N).map periodicGapSequence := rfl

/-- Integrals of measurable functions against the periodic law are finite-volume integrals.
The equality is valid even before integrability is established. -/
lemma integral_periodicGapLaw (p : Parameters) (N : ℕ+)
    {f : (ℤ → Ioi (0 : ℝ)) → ℝ} (hf : Measurable f) :
    (∫ y, f y ∂periodicGapLaw p N) =
      ∫ X, f (periodicGapSequence X) ∂gibbsMeasure p N := by
  rw [periodicGapLaw_toMeasure]
  exact integral_map (measurable_periodicGapSequence N).aemeasurable hf.aestronglyMeasurable

/-- The same transport for nonnegative integrals, with no finiteness assumption. -/
lemma lintegral_periodicGapLaw (p : Parameters) (N : ℕ+)
    {f : (ℤ → Ioi (0 : ℝ)) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y, f y ∂periodicGapLaw p N) =
      ∫⁻ X, f (periodicGapSequence X) ∂gibbsMeasure p N := by
  rw [periodicGapLaw_toMeasure]
  exact lintegral_map hf (measurable_periodicGapSequence N)

/-- The periodic law projects to the finite-block pushforward, including
blocks longer than a period. Thus the construction uses the existing gap encoding. -/
lemma periodicGapLaw_map_finiteGapBlock (p : Parameters) (N K : ℕ+) :
    (periodicGapLaw p N).toMeasure.map
      (fun y : ℤ → Ioi (0 : ℝ) => fun j : Fin (K : ℕ) => (y (j.val : ℤ) : ℝ)) =
        (gibbsMeasure p N).map (finiteGapBlock (K := K)) := by
  have hm : Measurable (fun y : ℤ → Ioi (0 : ℝ) =>
      fun j : Fin (K : ℕ) => (y (j.val : ℤ) : ℝ)) :=
    Measurable.of_eval fun j => measurable_subtype_coe.comp (measurable_pi_apply _)
  rw [periodicGapLaw_toMeasure, Measure.map_map hm (measurable_periodicGapSequence N)]
  rfl

/-- In particular, the first period has exactly the finite gap law. -/
lemma periodicGapLaw_map_gapLaw (p : Parameters) (N : ℕ+) :
    (periodicGapLaw p N).toMeasure.map
      (fun y : ℤ → Ioi (0 : ℝ) => fun j : Fin (N : ℕ) => (y (j.val : ℤ) : ℝ)) =
        gapLaw p N :=
  periodicGapLaw_map_finiteGapBlock p N N

/-- Periodicity is inherited from the companion library's integer microscopic gaps. -/
lemma periodicGapSequence_add_period {N : ℕ+} (X : Riesz1.Configuration N) (i : ℤ) :
    periodicGapSequence X (i + (N : ℕ)) = periodicGapSequence X i := by
  apply Subtype.ext
  exact Riesz1.gap_add_N X i

/-- All positive and inverse coordinate moments of the periodic laws are uniformly finite.
The constants are inherited from Lemma 2.1. -/
theorem periodicGapLaw_moment_bound (p : Parameters) (r : ℝ) (hr : 0 < r) :
    ∃ D : ℝ, 0 < D ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ i : ℤ,
      (∫⁻ y : ℤ → Ioi (0 : ℝ), ENNReal.ofReal ((y i : ℝ) ^ r) ∂periodicGapLaw p N) +
        (∫⁻ y : ℤ → Ioi (0 : ℝ), ENNReal.ofReal ((y i : ℝ) ^ (-r))
          ∂periodicGapLaw p N) ≤ ENNReal.ofReal D := by
  obtain ⟨D, hD, hb⟩ := SingleGapTails.single_gap_moment_integrals
    p.val.2 p.val.1 p.val.1 p.property.2.1 p.property.2.2 p.property.1 le_rfl r hr
  refine ⟨D, hD, fun N hN i => ?_⟩
  have hm : Measurable (fun y : ℤ → Ioi (0 : ℝ) => (y i : ℝ)) :=
    measurable_subtype_coe.comp (measurable_pi_apply i)
  rw [lintegral_periodicGapLaw p N (hm.pow_const r).ennreal_ofReal,
    lintegral_periodicGapLaw p N (hm.pow_const (-r)).ennreal_ofReal]
  exact (hb p rfl le_rfl le_rfl N hN i).2.2

/-- Coordinate compact containment, simultaneously for every volume at least two.
The reciprocal moment prevents escape to the boundary zero. -/
theorem periodicGapLaw_coordinate_compact (p : Parameters) (i : ℤ)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ K : Set (Ioi (0 : ℝ)), IsCompact K ∧
      ∀ (N : ℕ+), 2 ≤ (N : ℕ) →
        (periodicGapLaw p N).toMeasure {y | y i ∉ K} ≤ ε := by
  obtain ⟨D, hD, hb⟩ := periodicGapLaw_moment_bound p 1 zero_lt_one
  obtain ⟨δ, hδ, hs⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' Unit
  have hd : 0 < (δ () : ℝ) := hδ ()
  have hδε : (δ () : ℝ≥0∞) ≤ ε :=
    (ENNReal.le_tsum ()).trans hs.le
  let R : ℝ := max 1 (D / (δ () : ℝ))
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR : 0 < R := zero_lt_one.trans_le hR1
  let K : Set (Ioi (0 : ℝ)) := Icc ⟨R⁻¹, inv_pos.mpr hR⟩ ⟨R, hR⟩
  have hK : IsCompact K := by
    change IsCompact (Subtype.val ⁻¹' Icc R⁻¹ R)
    apply Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' isCompact_Icc
    intro x hx
    exact ⟨⟨x, (inv_pos.mpr hR).trans_le hx.1⟩, rfl⟩
  refine ⟨K, hK, fun N hN => ?_⟩
  let f : (ℤ → Ioi (0 : ℝ)) → ℝ≥0∞ :=
    fun y => ENNReal.ofReal ((y i : ℝ) + (y i : ℝ)⁻¹)
  have hm : Measurable (fun y : ℤ → Ioi (0 : ℝ) => (y i : ℝ)) :=
    measurable_subtype_coe.comp (measurable_pi_apply i)
  have hf : Measurable f := (hm.add hm.inv).ennreal_ofReal
  have hmass : (∫⁻ y, f y ∂periodicGapLaw p N) ≤ ENNReal.ofReal D := by
    have he (y : ℤ → Ioi (0 : ℝ)) : f y =
        ENNReal.ofReal ((y i : ℝ) ^ (1 : ℝ)) +
          ENNReal.ofReal ((y i : ℝ) ^ (-(1 : ℝ))) := by
      simp only [f, Real.rpow_one, Real.rpow_neg_one]
      exact ENNReal.ofReal_add (y i).property.le (inv_nonneg.mpr (y i).property.le)
    simp_rw [he]
    rw [lintegral_add_left (hm.pow_const 1).ennreal_ofReal]
    exact hb N hN i
  have hsub : {y : ℤ → Ioi (0 : ℝ) | y i ∉ K} ⊆
      {y | ENNReal.ofReal R ≤ f y} := by
    intro y hy
    apply ENNReal.ofReal_le_ofReal
    have hyn : 0 < (y i : ℝ) := (y i).property
    by_cases hlo : R⁻¹ ≤ (y i : ℝ)
    · have hhi : R < (y i : ℝ) := by
        by_contra hh
        exact hy ⟨hlo, le_of_not_gt hh⟩
      exact hhi.le.trans (le_add_of_nonneg_right (inv_nonneg.mpr hyn.le))
    · have hinv : R ≤ (y i : ℝ)⁻¹ := by
        have hi := (inv_le_inv₀ (inv_pos.mpr hR) hyn).mpr (le_of_not_ge hlo)
        simpa using hi
      exact hinv.trans (le_add_of_nonneg_left hyn.le)
  calc
    _ ≤ (periodicGapLaw p N).toMeasure {y | ENNReal.ofReal R ≤ f y} := measure_mono hsub
    _ ≤ (∫⁻ y, f y ∂periodicGapLaw p N) / ENNReal.ofReal R :=
      meas_ge_le_lintegral_div hf.aemeasurable (ENNReal.ofReal_pos.mpr hR).ne'
        ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal D / ENNReal.ofReal R := by gcongr
    _ = ENNReal.ofReal (D / R) := (ENNReal.ofReal_div_of_pos hR).symm
    _ ≤ (δ () : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      apply ENNReal.ofReal_le_ofReal
      rw [div_le_iff₀ hR]
      have hr := (div_le_iff₀ hd).mp (le_max_right 1 (D / (δ () : ℝ)))
      nlinarith
    _ ≤ ε := hδε

/-- Tightness for the explicit positive gap product in the proof of Theorem 3. No configuration-space topology is used. -/
theorem periodicGapLaw_tight (p : Parameters) :
    IsTightMeasureSet {μ | ∃ N : ℕ+, 2 ≤ (N : ℕ) ∧
      μ = (periodicGapLaw p N).toMeasure} := by
  apply isTightMeasureSet_pi_of_coordinate_compacts
  intro i ε hε
  obtain ⟨K, hK, hb⟩ := periodicGapLaw_coordinate_compact p i ε hε
  exact ⟨K, hK, fun μ ⟨N, hN, hμ⟩ => hμ ▸ hb N hN⟩

/-- See Subsection 6.3 of the paper: translation of the integer gap labels. -/
def gapIndexShift (a : ℤ) : (ℤ → Ioi (0 : ℝ)) ≃ₜ (ℤ → Ioi (0 : ℝ)) where
  toFun y i := y (a + i)
  invFun y i := y (-a + i)
  left_inv y := by funext i; simp
  right_inv y := by funext i; simp
  continuous_toFun := continuous_pi fun _ => continuous_apply _
  continuous_invFun := continuous_pi fun _ => continuous_apply _

/-- Every finite periodic law is invariant under every integer shift. -/
theorem periodicGapLaw_shift (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (a : ℤ) :
    (periodicGapLaw p N).map (gapIndexShift a) = periodicGapLaw p N := by
  let T := (GapSymmetries.cycleConfig (N := N))^[(Riesz1.labelOf N a).val]
  have hT : MeasurePreserving T (gibbsMeasure p N) (gibbsMeasure p N) :=
    (show MeasurePreserving (GapSymmetries.cycleConfig (N := N))
      (gibbsMeasure p N) (gibbsMeasure p N) from
      ⟨GapSymmetries.measurable_cycleConfig,
        LowerCorrelations.gibbsMeasure_map_cycle p N hN⟩).iterate _
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map, periodicGapLaw_toMeasure,
    Measure.map_map (gapIndexShift a).continuous.measurable (measurable_periodicGapSequence N)]
  have he : gapIndexShift a ∘ periodicGapSequence = periodicGapSequence ∘ T := by
    funext X i
    apply Subtype.ext
    exact (DecayShort.ShortRangeResult.gap_cycleConfig_label a i X).symm
  rw [he, ← Measure.map_map (measurable_periodicGapSequence N) hT.measurable,
    hT.map_eq]

/-- The finite-volume laws have compact closure in the topology of weak convergence. -/
theorem periodicGapLaw_isCompact_closure (p : Parameters) :
    IsCompact (closure {q : ProbabilityMeasure (ℤ → Ioi (0 : ℝ)) |
      ∃ N : ℕ+, 2 ≤ (N : ℕ) ∧ q = periodicGapLaw p N}) := by
  let S : Set (ProbabilityMeasure (ℤ → Ioi (0 : ℝ))) :=
    {q | ∃ N : ℕ+, 2 ≤ (N : ℕ) ∧ q = periodicGapLaw p N}
  have ht : IsTightMeasureSet {(μ : Measure (ℤ → Ioi (0 : ℝ))) | μ ∈ S} := by
    convert periodicGapLaw_tight p using 1
    ext μ
    constructor
    · rintro ⟨q, ⟨N, hN, rfl⟩, rfl⟩
      exact ⟨N, hN, rfl⟩
    · rintro ⟨N, hN, rfl⟩
      exact ⟨periodicGapLaw p N, ⟨N, hN, rfl⟩, rfl⟩
  exact isCompact_closure_of_isTightMeasureSet ht

/-- Tightness supplies a subsequential limit of the actual finite-volume laws. -/
theorem periodicGapLaw_exists_subsequence (p : Parameters) :
    ∃ q : ProbabilityMeasure (ℤ → Ioi (0 : ℝ)), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (fun n => periodicGapLaw p (φ n + 1).succPNat) atTop (𝓝 q) := by
  obtain ⟨q, _, φ, hφ, hq⟩ :=
    (periodicGapLaw_isCompact_closure p).tendsto_subseq
      (fun n => subset_closure ⟨(n + 1).succPNat, by simp, rfl⟩)
  exact ⟨q, φ, hφ, hq⟩

/-- Every weak subsequential limit inherits the finite cyclic symmetries. -/
theorem periodicGapLaw_limit_shift (p : Parameters) (V : ℕ → ℕ+)
    (hV : ∀ n, 2 ≤ (V n : ℕ)) (q : ProbabilityMeasure (ℤ → Ioi (0 : ℝ)))
    (hq : Tendsto (fun n => periodicGapLaw p (V n)) atTop (𝓝 q)) (a : ℤ) :
    q.map (gapIndexShift a) = q := by
  have ht := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hq
    (gapIndexShift a).continuous
  simp_rw [periodicGapLaw_shift p _ (hV _) a] at ht
  exact tendsto_nhds_unique ht hq

/-- Positive and inverse moments pass to every subsequential limit with precisely
the same uniform bound, by the nonnegative form of Portmanteau. -/
theorem periodicGapLaw_limit_moment_bound (p : Parameters) (V : ℕ → ℕ+)
    (hV : ∀ n, 2 ≤ (V n : ℕ)) (q : ProbabilityMeasure (ℤ → Ioi (0 : ℝ)))
    (hq : Tendsto (fun n => periodicGapLaw p (V n)) atTop (𝓝 q))
    (r : ℝ) (hr : 0 < r) :
    ∃ D : ℝ, 0 < D ∧
      (∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ i : ℤ,
        (∫⁻ y : ℤ → Ioi (0 : ℝ), ENNReal.ofReal ((y i : ℝ) ^ r) ∂periodicGapLaw p N) +
          (∫⁻ y : ℤ → Ioi (0 : ℝ), ENNReal.ofReal ((y i : ℝ) ^ (-r))
            ∂periodicGapLaw p N) ≤ ENNReal.ofReal D) ∧
      ∀ i : ℤ,
        (∫⁻ y : ℤ → Ioi (0 : ℝ), ENNReal.ofReal ((y i : ℝ) ^ r) ∂q) +
          (∫⁻ y : ℤ → Ioi (0 : ℝ), ENNReal.ofReal ((y i : ℝ) ^ (-r)) ∂q) ≤
            ENNReal.ofReal D := by
  obtain ⟨D, hD, hb⟩ := periodicGapLaw_moment_bound p r hr
  refine ⟨D, hD, hb, fun i => ?_⟩
  have hy : Continuous (fun y : ℤ → Ioi (0 : ℝ) => (y i : ℝ)) :=
    continuous_subtype_val.comp (continuous_apply i)
  have hp := hy.rpow_const (p := r) fun y => Or.inl (y i).property.ne'
  have hn := hy.rpow_const (p := -r) fun y => Or.inl (y i).property.ne'
  have he (y : ℤ → Ioi (0 : ℝ)) :
      ENNReal.ofReal ((y i : ℝ) ^ r + (y i : ℝ) ^ (-r)) =
        ENNReal.ofReal ((y i : ℝ) ^ r) + ENNReal.ofReal ((y i : ℝ) ^ (-r)) :=
    ENNReal.ofReal_add (Real.rpow_nonneg (y i).property.le _)
      (Real.rpow_nonneg (y i).property.le _)
  have hlow := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    (hp.add hn) (fun y => add_nonneg (Real.rpow_nonneg (y i).property.le _)
      (Real.rpow_nonneg (y i).property.le _))
    (fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hq hG)
  simp only [Pi.add_apply, he] at hlow
  simp_rw [lintegral_add_left hp.measurable.ennreal_ofReal] at hlow
  exact hlow.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun n => hb (V n) (hV n) i))

/-- A bounded continuous cylinder test on the positive gap product. -/
def gapCylinder {k : ℕ} (labels : Fin k → ℤ)
    (f : EuclideanSpace ℝ (Fin k) →ᵇ ℝ) : (ℤ → Ioi (0 : ℝ)) →ᵇ ℝ :=
  f.compContinuous ⟨fun y => WithLp.toLp 2 (fun i => (y (labels i) : ℝ)),
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i =>
      continuous_subtype_val.comp (continuous_apply (labels i)))⟩

/-- Any Lipschitz cylinder can be moved into arbitrarily large middle blocks.
The constant in the derivative norm depends only on the fixed cylinder. -/
theorem gapCylinder_middle_embedding (k : ℕ) (labels : Fin k → ℤ)
    (f : EuclideanSpace ℝ (Fin k) →ᵇ ℝ) (hf : ∃ L, LipschitzWith L f) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m : ℕ, ∃ (n : ℕ+) (G : BlockObservable n)
      (J : Finset (Fin (n : ℕ))),
      2 ≤ (n : ℕ) ∧ m ≤ (n : ℕ) ∧ MiddleConsecutiveBlock n J ∧
      DependsOnBlockCoordinates G J ∧ blockDerivativeNorm G ≤ A ∧
      ∀ (p : Parameters) (N : ℕ+), 2 ≤ (N : ℕ) →
        (∫ y, gapCylinder labels f y ∂periodicGapLaw p N) =
          ∫ X : Riesz1.Configuration N, G.val (finiteGapBlock X) ∂gibbsMeasure p N := by
  classical
  obtain ⟨L, hL⟩ := hf
  let B := Finset.univ.sup (fun i => (labels i).natAbs)
  have hB (i : Fin k) : -(B : ℤ) ≤ labels i ∧ labels i ≤ B := by
    have hi : (labels i).natAbs ≤ B :=
      Finset.le_sup (f := fun i => (labels i).natAbs) (Finset.mem_univ i)
    have hci : ((labels i).natAbs : ℤ) ≤ B := by exact_mod_cast hi
    constructor
    · have hn : -(labels i) ≤ ((labels i).natAbs : ℤ) := by
        simpa using (Int.le_natAbs (a := -(labels i)))
      omega
    · exact Int.le_natAbs.trans hci
  let d : Fin k → ℕ := fun i => (labels i + B).toNat
  have hd (i : Fin k) : (d i : ℤ) = labels i + B :=
    Int.toNat_of_nonneg (by have := (hB i).1; omega)
  have hdle (i : Fin k) : d i ≤ 2 * B := by have := hd i; have := (hB i).2; omega
  let H : ℝ≥0 := L * ((k : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal)
  refine ⟨(2 * B + 1 : ℕ) * (H : ℝ), by positivity, fun m => ?_⟩
  let t := m + 2 * B + 1
  let n : ℕ+ := ⟨8 * t, by dsimp [t]; omega⟩
  let ej : Fin (2 * B + 1) → Fin (n : ℕ) :=
    fun j => ⟨4 * t + j.val, by have := j.isLt; dsimp [n, t]; omega⟩
  let e : Fin k → Fin (n : ℕ) := fun i => ej ⟨d i, Nat.lt_succ_of_le (hdle i)⟩
  let J := Finset.univ.image ej
  have hmem (i : Fin k) : e i ∈ J := Finset.mem_image.mpr
    ⟨⟨d i, Nat.lt_succ_of_le (hdle i)⟩, Finset.mem_univ _, rfl⟩
  have hJ : J = Finset.univ.filter
      (fun i : Fin (n : ℕ) => 4 * t ≤ i.val ∧ i.val < 4 * t + (2 * B + 1)) := by
    ext i
    simp only [J, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨j, rfl⟩
      dsimp [ej]
      have := j.isLt
      omega
    · intro hi
      refine ⟨⟨i.val - 4 * t, by omega⟩, ?_⟩
      apply Fin.ext
      dsimp [ej]
      omega
  have hmiddle : MiddleConsecutiveBlock n J := by
    refine ⟨4 * t, 2 * B + 1, ?_, ?_, hJ, ?_⟩
    · dsimp [n, t]; omega
    · dsimp [n, t]; omega
    · intro i hi
      rw [hJ] at hi
      have hi := (Finset.mem_filter.mp hi).2
      dsimp [n, t] at *
      omega
  have hsel : LipschitzWith 1 (fun x : Fin (n : ℕ) → ℝ => fun i : Fin k => x (e i)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul]
    exact (dist_pi_le_iff dist_nonneg).mpr fun i => dist_le_pi_dist x y (e i)
  have hG : LipschitzWith H (fun x : Fin (n : ℕ) → ℝ =>
      f (WithLp.toLp 2 (fun i => x (e i)))) := by
    simpa only [mul_one, Fintype.card_fin, H, Function.comp_def] using
      hL.comp ((PiLp.lipschitzWith_toLp 2 (fun _ : Fin k => ℝ)).comp hsel)
  let G : BlockObservable n := ⟨_, H, hG⟩
  have hdep : DependsOnBlockCoordinates G J := by
    intro x y hxy
    apply congrArg f
    apply WithLp.ofLp_injective
    funext i
    exact hxy (e i) (hmem i)
  have hcoord (j : Fin (n : ℕ)) : coordinateDerivativeNorm G j ≤ if j ∈ J then H else 0 := by
    apply csInf_le (OrderBot.bddBelow _)
    intro x u
    by_cases hj : j ∈ J
    · simp only [hj, ↓reduceIte]
      have hdxy : dist (Function.update x j u) x ≤ |u - x j| := by
        apply (dist_pi_le_iff (abs_nonneg _)).mpr
        intro i
        by_cases hi : i = j
        · subst i; simp [Real.dist_eq]
        · simp [Function.update_of_ne hi, abs_nonneg]
      exact (hG.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left hdxy H.property)
    · have heq : G.val (Function.update x j u) = G.val x := by
        apply hdep
        intro i hi
        exact Function.update_of_ne (by intro he; subst i; exact hj hi) _ _
      simp only [hj, ↓reduceIte, NNReal.coe_zero, zero_mul, heq, sub_self, abs_zero, le_refl]
  have hnorm : blockDerivativeNorm G ≤ (2 * B + 1 : ℕ) * (H : ℝ) := by
    calc
      _ ≤ ∑ j : Fin (n : ℕ), (if j ∈ J then (H : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro j _
        have h := NNReal.coe_le_coe.mpr (hcoord j)
        simpa only [apply_ite (fun x : ℝ≥0 => (x : ℝ)), NNReal.coe_zero] using h
      _ = (J.card : ℝ) * (H : ℝ) := by simp [Finset.sum_ite_mem]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ H.property
        have hc : J.card ≤ 2 * B + 1 := by
          simpa only [J, Finset.card_univ, Fintype.card_fin] using
            (Finset.card_image_le (s := Finset.univ) (f := ej))
        exact_mod_cast hc
  refine ⟨n, G, J, by dsimp [n, t]; omega, by dsimp [n, t]; omega,
    hmiddle, hdep, hnorm, fun p N hN => ?_⟩
  let a : ℤ := 4 * t + B
  have heq : (fun X : Riesz1.Configuration N => G.val (finiteGapBlock X)) =
      fun X => gapCylinder labels f (gapIndexShift a (periodicGapSequence X)) := by
    funext X
    apply congrArg f
    apply WithLp.ofLp_injective
    funext i
    change gap X ((e i).val : ℤ) = gap X (a + labels i)
    congr 1
    change ((4 * t + d i : ℕ) : ℤ) = 4 * t + B + labels i
    push_cast
    rw [hd i]
    ring
  rw [heq]
  have ht := integral_periodicGapLaw p N
    (f := fun y => gapCylinder labels f (gapIndexShift a y))
    ((gapCylinder labels f).continuous.measurable.comp (gapIndexShift a).continuous.measurable)
  rw [← ht]
  rw [← integral_map (gapIndexShift a).continuous.measurable.aemeasurable
    (gapCylinder labels f).continuous.aestronglyMeasurable, ← ProbabilityMeasure.toMeasure_map,
    periodicGapLaw_shift p N hN a]

section InternalCauchy

variable (hcomparison :
  ∀ (p : Parameters) (ζ : ℝ), 0 < ζ → ∃ C : ℝ, 0 < C ∧
    ∀ (n N N' : ℕ+) (_ : 2 ≤ (n : ℕ)),
      (N : ℕ) ≤ (N' : ℕ) → 4 * (n : ℕ) ≤ (N : ℕ) →
      (n : ℝ) ^ (2 / p.val.2) ≤ (N : ℝ) →
      ∀ (G : BlockObservable n) (J : Finset (Fin (n : ℕ))),
        MiddleConsecutiveBlock n J → DependsOnBlockCoordinates G J →
        Integrable (fun X : Riesz1.Configuration N => G.val (finiteGapBlock X))
          (gibbsMeasure p N) ∧
        Integrable (fun X : Riesz1.Configuration N' => G.val (finiteGapBlock X))
          (gibbsMeasure p N') ∧
        |(∫ X : Riesz1.Configuration N, G.val (finiteGapBlock X) ∂gibbsMeasure p N) -
          (∫ X : Riesz1.Configuration N', G.val (finiteGapBlock X) ∂gibbsMeasure p N')| ≤
          C * (n : ℝ) ^ (-min p.val.2 1 / 2 + ζ) * blockDerivativeNorm G)

include hcomparison

/-- The cylinder convergence step in the proof of Theorem 3 assumes the
ordinary-gap Cauchy estimate. -/
theorem gapCylinder_cauchy_internal (p : Parameters) (k : ℕ) (labels : Fin k → ℤ)
    (f : EuclideanSpace ℝ (Fin k) →ᵇ ℝ) (hf : ∃ L, LipschitzWith L f) :
    CauchySeq (fun v : ℕ =>
      ∫ y, gapCylinder labels f y ∂periodicGapLaw p (v + 1).succPNat) := by
  let σ := min p.val.2 1 / 2
  have hσ : 0 < σ := div_pos (lt_min p.property.2.1 zero_lt_one) (by norm_num)
  obtain ⟨C, hC, hc⟩ := hcomparison p (σ / 2) (half_pos hσ)
  obtain ⟨A, hA, hemb⟩ := gapCylinder_middle_embedding k labels f hf
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have ht : Tendsto (fun m : ℕ => C * (m : ℝ) ^ (-(σ / 2)) * A) atTop (𝓝 0) := by
    simpa using (((tendsto_rpow_neg_atTop (half_pos hσ)).comp
      tendsto_natCast_atTop_atTop).const_mul C).mul_const A
  obtain ⟨m, hm1, hmε⟩ :=
    ((eventually_ge_atTop 1).and (ht.eventually_lt_const hε)).exists
  obtain ⟨n, G, J, hn, hmn, hmiddle, hdep, hnorm, htransport⟩ := hemb m
  have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm1)
  have hp : (n : ℝ) ^ (-(σ / 2)) ≤ (m : ℝ) ^ (-(σ / 2)) :=
    Real.rpow_le_rpow_of_nonpos hmR hmnR (neg_nonpos.mpr (half_pos hσ).le)
  have hsmall : C * (n : ℝ) ^ (-min p.val.2 1 / 2 + σ / 2) * blockDerivativeNorm G < ε := by
    have hexp : -min p.val.2 1 / 2 + σ / 2 = -(σ / 2) := by dsimp [σ]; ring
    rw [hexp]
    calc
      _ ≤ C * (n : ℝ) ^ (-(σ / 2)) * A :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ ≤ C * (m : ℝ) ^ (-(σ / 2)) * A := by gcongr
      _ < ε := hmε
  obtain ⟨b₀, hb₀⟩ := exists_nat_ge ((n : ℝ) ^ (2 / p.val.2))
  let b := max (4 * (n : ℕ)) b₀
  have hb (v : ℕ) (hv : b ≤ v) :
      4 * (n : ℕ) ≤ ((v + 1).succPNat : ℕ) ∧
        (n : ℝ) ^ (2 / p.val.2) ≤ ((v + 1).succPNat : ℝ) := by
    constructor
    · have := le_max_left (4 * (n : ℕ)) b₀
      dsimp [b] at hv
      simp only [Nat.succPNat_coe]
      omega
    · apply hb₀.trans
      have hi : b₀ ≤ v + 2 := (le_max_right _ _).trans (hv.trans (by omega))
      exact_mod_cast hi
  refine ⟨b, fun v hv w hw => ?_⟩
  have hv2 : 2 ≤ ((v + 1).succPNat : ℕ) := by simp
  have hw2 : 2 ≤ ((w + 1).succPNat : ℕ) := by simp
  rw [Real.dist_eq, htransport p _ hv2, htransport p _ hw2]
  rcases le_total v w with hvw | hwv
  · exact (hc n (v + 1).succPNat (w + 1).succPNat hn (by simpa using hvw)
      (hb v hv).1 (hb v hv).2 G J hmiddle hdep).2.2.trans_lt hsmall
  · rw [abs_sub_comm]
    exact (hc n (w + 1).succPNat (v + 1).succPNat hn (by simpa using hwv)
      (hb w hw).1 (hb w hw).2 G J hmiddle hdep).2.2.trans_lt hsmall

/-- Internal uniqueness step of the proof of Theorem 3:
all subsequential limits at diverging volumes agree, including subsequences
which are not monotone. -/
theorem periodicGapLaw_cluster_unique_internal (p : Parameters)
    (u v : ℕ → ℕ) (hu : Tendsto u atTop atTop) (hv : Tendsto v atTop atTop)
    (q q' : ProbabilityMeasure (ℤ → Ioi (0 : ℝ)))
    (hq : Tendsto (fun n => periodicGapLaw p (u n + 1).succPNat) atTop (𝓝 q))
    (hq' : Tendsto (fun n => periodicGapLaw p (v n + 1).succPNat) atTop (𝓝 q')) : q = q' := by
  apply gapSequence_eq_of_bounded_lipschitz_cylinders
  intro k labels f hf
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete
    (gapCylinder_cauchy_internal hcomparison p k labels f hf)
  have h₁ := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hq)
    (gapCylinder labels f)
  have h₂ := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hq')
    (gapCylinder labels f)
  exact (tendsto_nhds_unique (ha.comp hu) h₁).symm.trans
    (tendsto_nhds_unique (ha.comp hv) h₂)

/-- Internal existence and full weak convergence in the proof of Theorem 3, assuming the ordinary-gap Cauchy estimate.
The indexing includes the one-particle law. Dropping this first term is justified
by the shift equivalence for convergence of a sequence. -/
theorem periodicGapLaw_exists_unique_limit_internal (p : Parameters) :
    ∃! q : ProbabilityMeasure (ℤ → Ioi (0 : ℝ)),
      Tendsto (fun n : ℕ => periodicGapLaw p n.succPNat) atTop (𝓝 q) := by
  obtain ⟨q, φ, hφ, hq⟩ := periodicGapLaw_exists_subsequence p
  have hfull : Tendsto (fun n : ℕ => periodicGapLaw p (n + 1).succPNat) atTop (𝓝 q) := by
    apply Filter.tendsto_of_subseq_tendsto
    intro ns hns
    obtain ⟨q', _, ms, hms, hq'⟩ := (periodicGapLaw_isCompact_closure p).tendsto_subseq
      (fun n => subset_closure ⟨(ns n + 1).succPNat, by simp, rfl⟩)
    have heq : q = q' := periodicGapLaw_cluster_unique_internal hcomparison p φ (ns ∘ ms)
      hφ.tendsto_atTop (hns.comp hms.tendsto_atTop) q q' hq hq'
    exact ⟨ms, heq ▸ hq'⟩
  have hfull' : Tendsto (fun n : ℕ => periodicGapLaw p n.succPNat) atTop (𝓝 q) :=
    (tendsto_add_atTop_iff_nat 1).mp hfull
  exact ⟨q, hfull', fun q' hq' => tendsto_nhds_unique hq' hfull'⟩

end InternalCauchy

/-- A finite second coordinate moment gives square integrability. -/
lemma gapCoordinate_memLp_two_internal
    (q : ProbabilityMeasure (ℤ → Ioi (0 : ℝ))) (i : ℤ)
    (h : (∫⁻ y : ℤ → Ioi (0 : ℝ), ENNReal.ofReal ((y i : ℝ) ^ (2 : ℝ)) ∂q) < ∞) :
    MemLp (fun y : ℤ → Ioi (0 : ℝ) => (y i : ℝ)) 2 q := by
  have hm : Measurable (fun y : ℤ → Ioi (0 : ℝ) => (y i : ℝ)) :=
    measurable_subtype_coe.comp (measurable_pi_apply i)
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  apply (lintegral_ofReal_ne_top_iff_integrable (hm.pow_const (2 : ℕ)).aestronglyMeasurable
    (ae_of_all _ fun y => sq_nonneg (y i : ℝ))).mp
  simpa only [Real.rpow_two] using h.ne

/-- The mean-one assertion of the proof of Theorem 3.
The uniform second moment justifies passage of the unbounded coordinate test. -/
theorem periodicGapLaw_limit_mean (p : Parameters) (V : ℕ → ℕ+)
    (hV : ∀ n, 2 ≤ (V n : ℕ)) (q : ProbabilityMeasure (ℤ → Ioi (0 : ℝ)))
    (hq : Tendsto (fun n => periodicGapLaw p (V n)) atTop (𝓝 q)) (i : ℤ) :
    Integrable (fun y : ℤ → Ioi (0 : ℝ) => (y i : ℝ)) q ∧
      (∫ y : ℤ → Ioi (0 : ℝ), (y i : ℝ) ∂q) = 1 := by
  obtain ⟨D, hD, hf, hqD⟩ := periodicGapLaw_limit_moment_bound p V hV q hq 2 (by norm_num)
  have hμD (n : ℕ) :
      (∫⁻ y : ℤ → Ioi (0 : ℝ), ENNReal.ofReal ((y i : ℝ) ^ (2 : ℝ))
        ∂periodicGapLaw p (V n)) ≤ ENNReal.ofReal D :=
    le_trans (le_add_of_nonneg_right (by positivity)) (hf (V n) (hV n) i)
  have hνD : (∫⁻ y : ℤ → Ioi (0 : ℝ), ENNReal.ofReal ((y i : ℝ) ^ (2 : ℝ)) ∂q) ≤
      ENNReal.ofReal D := le_trans (le_add_of_nonneg_right (by positivity)) (hqD i)
  have hμ (n) := gapCoordinate_memLp_two_internal (periodicGapLaw p (V n)) i
    ((hμD n).trans_lt ENNReal.ofReal_lt_top)
  have hν := gapCoordinate_memLp_two_internal q i (hνD.trans_lt ENNReal.ofReal_lt_top)
  have hy : Continuous (fun y : ℤ → Ioi (0 : ℝ) => (y i : ℝ)) :=
    continuous_subtype_val.comp (continuous_apply i)
  have ht := WeakMomentTruncation.integral_tendsto_of_uniform_second_moment_internal
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hq) hy hμ hν
    (C := D) (Eventually.of_forall fun n => by
      rw [integral_eq_lintegral_of_nonneg_ae
        (f := fun y : ℤ → Ioi (0 : ℝ) => (y i : ℝ) ^ (2 : ℕ))
        (ae_of_all _ fun y => sq_nonneg (y i : ℝ))
        (hy.measurable.pow_const (2 : ℕ)).aestronglyMeasurable]
      exact ENNReal.toReal_le_of_le_ofReal hD.le (by simpa only [Real.rpow_two] using hμD n))
  have hm : ∀ n : ℕ, (∫ y : ℤ → Ioi (0 : ℝ), (y i : ℝ) ∂periodicGapLaw p (V n)) = 1 := by
    intro n
    rw [integral_periodicGapLaw p (V n) hy.measurable]
    have hmean := (RemovableGapBarrier.gap_mean_one p (V n) (hV n) (Riesz1.labelOf (V n) i)).2
    have hmap : Measurable (@gapVector (V n)) := Riesz1.measurable_gapVector _
    rw [gapLaw, integral_map hmap.aemeasurable
      (measurable_pi_apply _).aestronglyMeasurable] at hmean
    simpa only [periodicGapSequence, ← gap_eq_gapVector_labelOf] using hmean
  simp_rw [hm] at ht
  exact ⟨hν.integrable (by norm_num), tendsto_nhds_unique ht tendsto_const_nhds⟩

/-- The sum of `k` consecutive gaps starting at the integer label `i`. -/
def gapSequenceSpan (y : ℤ → Ioi (0 : ℝ)) (i : ℤ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, (y (i + j) : ℝ)

/-- Each finite span is continuous in the positive product topology. -/
lemma continuous_gapSequenceSpan (i : ℤ) (k : ℕ) :
    Continuous (fun y : ℤ → Ioi (0 : ℝ) => gapSequenceSpan y i k) := by
  exact continuous_finsetSum _ fun j _ => continuous_subtype_val.comp (continuous_apply _)

/-- Strict span deviations are open events, as required by Portmanteau. -/
lemma isOpen_gapSequenceSpan_deviation (i : ℤ) (k : ℕ) (a : ℝ) :
    IsOpen {y : ℤ → Ioi (0 : ℝ) | a < |gapSequenceSpan y i k - k|} :=
  isOpen_lt continuous_const (show Continuous (fun y : ℤ → Ioi (0 : ℝ) =>
    |gapSequenceSpan y i k - k|) from ((continuous_gapSequenceSpan i k).sub continuous_const).abs)

/-- The index shift evaluates at the translated label. -/
lemma gapIndexShift_apply (a : ℤ) (y : ℤ → Ioi (0 : ℝ)) (i : ℤ) :
    gapIndexShift a y i = y (a + i) := rfl

/-- Periodic spans are the companion library's block lengths, with the same labels. -/
lemma gapSequenceSpan_periodic {N : ℕ+} (X : Riesz1.Configuration N) (i : ℤ) (k : ℕ) :
    gapSequenceSpan (periodicGapSequence X) i k = Riesz1.blockLength X i k :=
  (Riesz1.blockLength_eq_sum X i k).symm

/-- Finite cyclic invariance moves an arbitrary span to label zero. -/
lemma periodicGapLaw_span_deviation_shift (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (i : ℤ) (k : ℕ) (a : ℝ) :
    (periodicGapLaw p N).toMeasure {y | a < |gapSequenceSpan y i k - k|} =
      (periodicGapLaw p N).toMeasure {y | a < |gapSequenceSpan y 0 k - k|} := by
  have hm : MeasurableSet {y : ℤ → Ioi (0 : ℝ) | a < |gapSequenceSpan y 0 k - k|} :=
    (isOpen_gapSequenceSpan_deviation 0 k a).measurableSet
  have he := congrArg (fun q : ProbabilityMeasure (ℤ → Ioi (0 : ℝ)) =>
    q.toMeasure {y | a < |gapSequenceSpan y 0 k - k|}) (periodicGapLaw_shift p N hN i)
  rw [ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (gapIndexShift i).continuous.measurable hm] at he
  simpa only [Set.preimage_ofPred_eq, gapSequenceSpan, gapIndexShift_apply,
    zero_add] using he

/-- A finite interval of distinct cyclic labels has its usual consecutive-gap sum. -/
lemma gapVector_sum_cyclicInterval_zero {N : ℕ+} (k : ℕ) (hk : 1 ≤ k)
    (hkN : k ≤ (N : ℕ)) (X : Riesz1.Configuration N) :
    (∑ i ∈ cyclicInterval N 0 k, gapVector X i) =
      gapSequenceSpan (periodicGapSequence X) 0 k := by
  let K : ℕ+ := ⟨k, hk⟩
  have h := DecayShort.ShortRangeResult.sum_cyclicInterval (n := K) hkN 0 (gapVector X)
  change (∑ i ∈ cyclicInterval N 0 k, gapVector X i) =
    ∑ i : Fin k, gapVector X (Riesz1.labelOf N (0 + (i.val : ℤ))) at h
  rw [h]
  simp only [zero_add, ← gap_eq_gapVector_labelOf]
  simpa only [gapSequenceSpan, periodicGapSequence, zero_add] using
    Fin.sum_univ_eq_sum_range (fun j : ℕ => gap X (j : ℤ)) k

/-- Uniform finite-volume span deviations in both exponent regimes. The additional
upper bound on the small exponent is what the later average argument uses. -/
theorem periodicGapLaw_finite_rigidity (p : Parameters) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ min p.val.2 1 / 2 + η₀ < 1 ∧
      ∀ η : ℝ, 0 < η → η < η₀ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ k : ℕ, 1 ≤ k → k ≤ (N : ℕ) / 2 → ∀ i : ℤ,
          (periodicGapLaw p N).toMeasure
            {y | (k : ℝ) ^ (min p.val.2 1 / 2 + η) < |gapSequenceSpan y i k - k|} ≤
              ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ (η / (4 * (p.val.2 + 2))))) := by
  by_cases hs : p.val.2 < 1
  · let s : Riesz1.RieszExponent := ⟨p.val.2, p.property.2.1, hs⟩
    let β : InverseTemperature := ⟨p.val.1, p.property.1⟩
    have hp : ofLong β s = p := Subtype.ext rfl
    obtain ⟨ε₀, hε₀, hb⟩ := nearOptimalRigidity s β
    let η₀ := min (ε₀ / 2) ((1 - p.val.2 / 2) / 2)
    have hη₀ : 0 < η₀ := lt_min (half_pos hε₀) (by linarith)
    refine ⟨η₀, hη₀, ?_, fun η hη hηsmall => ?_⟩
    · rw [min_eq_left hs.le]
      have := min_le_right (ε₀ / 2) ((1 - p.val.2 / 2) / 2)
      dsimp [η₀] at *
      linarith
    have hε : η < ε₀ :=
      (hηsmall.trans_le (min_le_left _ _)).trans (half_lt_self hε₀)
    obtain ⟨C, c, hC, hc, hb⟩ := hb η hη hε
    refine ⟨C, c, hC, hc, fun N hN k hk hkN i => ?_⟩
    rw [periodicGapLaw_span_deviation_shift p N hN i, periodicGapLaw_toMeasure,
      Measure.map_apply (measurable_periodicGapSequence N)
        (isOpen_gapSequenceSpan_deviation 0 k _).measurableSet]
    have ht := hb N hN ⟨0, N.pos⟩ k hk hkN
    rw [hp] at ht
    apply (measure_mono (fun X hX => ?_)).trans ht
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, gapSequenceSpan_periodic,
      min_eq_left hs.le] at hX
    exact hX.le
  · have hs' : 1 < p.val.2 := lt_of_le_of_ne (le_of_not_gt hs) p.property.2.2.symm
    refine ⟨1 / 4, by norm_num, ?_, fun η hη _ => ?_⟩
    · rw [min_eq_right hs'.le]; norm_num
    obtain ⟨C, c, hC, hc, hb, _⟩ := DecayShort.shortRange_localLaw_complete
      p.val.2 p.val.1 p.val.1 η hs' p.property.1 le_rfl hη
    refine ⟨C, c, hC, hc, fun N hN k hk hkN i => ?_⟩
    rw [periodicGapLaw_span_deviation_shift p N hN i, periodicGapLaw_toMeasure,
      Measure.map_apply (measurable_periodicGapSequence N)
        (isOpen_gapSequenceSpan_deviation 0 k _).measurableSet]
    have ht := hb p rfl le_rfl le_rfl N hN k hk hkN 0
    have hmap : Measurable (@gapVector N) := Riesz1.measurable_gapVector _
    rw [gapLaw, Measure.map_apply hmap (by
      apply measurableSet_le
      · exact measurable_const
      · exact ((Finset.measurable_sum _ fun j _ => measurable_pi_apply j).sub_const
          (k : ℝ)).abs)] at ht
    apply (measure_mono (fun X hX => ?_)).trans ht
    change (k : ℝ) ^ (1 / 2 + η) ≤ |(∑ i ∈ cyclicInterval N 0 k, gapVector X i) - k|
    rw [gapVector_sum_cyclicInterval_zero k hk (by omega) X]
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, min_eq_right hs'.le] at hX
    exact hX.le

/-- The strict block-deviation bound of the proof of Theorem 3
passes to every weak limit at diverging volumes. The constants precede the block
length and starting label. -/
theorem periodicGapLaw_limit_rigidity (p : Parameters) (V : ℕ → ℕ+)
    (hV : ∀ n, 2 ≤ (V n : ℕ)) (hVtop : Tendsto (fun n => (V n : ℕ)) atTop atTop)
    (q : ProbabilityMeasure (ℤ → Ioi (0 : ℝ)))
    (hq : Tendsto (fun n => periodicGapLaw p (V n)) atTop (𝓝 q)) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ min p.val.2 1 / 2 + η₀ < 1 ∧
      ∀ η : ℝ, 0 < η → η < η₀ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ k : ℕ, 1 ≤ k → ∀ i : ℤ,
          q.toMeasure {y | (k : ℝ) ^ (min p.val.2 1 / 2 + η) < |gapSequenceSpan y i k - k|} ≤
            ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ (η / (4 * (p.val.2 + 2))))) := by
  obtain ⟨η₀, hη₀, hη₀small, hb⟩ := periodicGapLaw_finite_rigidity p
  refine ⟨η₀, hη₀, hη₀small, fun η hη hsmall => ?_⟩
  obtain ⟨C, c, hC, hc, hb⟩ := hb η hη hsmall
  refine ⟨C, c, hC, hc, fun k hk i => ?_⟩
  have hl := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hq
    (isOpen_gapSequenceSpan_deviation i k ((k : ℝ) ^ (min p.val.2 1 / 2 + η)))
  apply hl.trans
  apply liminf_le_of_frequently_le'
  apply Eventually.frequently
  filter_upwards [hVtop.eventually (eventually_ge_atTop (2 * k))] with n hn
  exact hb (V n) (hV n) k hk (by omega) i

/-- The moment passage includes the deterministic one-particle law. Both the
finite laws and the limit share one bound for each positive moment order. -/
theorem periodicGapLaw_limit_all_moments (p : Parameters) (V : ℕ → ℕ+)
    (hV : ∀ n, 2 ≤ (V n : ℕ)) (q : ProbabilityMeasure (ℤ → Ioi (0 : ℝ)))
    (hq : Tendsto (fun n => periodicGapLaw p (V n)) atTop (𝓝 q)) (r : ℝ) (hr : 0 < r) :
    ∃ D : ℝ, 0 < D ∧
      (∀ (N : ℕ+) (i : ℤ),
        (∫⁻ y : ℤ → Ioi (0 : ℝ), ENNReal.ofReal ((y i : ℝ) ^ r) ∂periodicGapLaw p N) +
          (∫⁻ y : ℤ → Ioi (0 : ℝ), ENNReal.ofReal ((y i : ℝ) ^ (-r))
            ∂periodicGapLaw p N) ≤ ENNReal.ofReal D) ∧
      ∀ i : ℤ,
        (∫⁻ y : ℤ → Ioi (0 : ℝ), ENNReal.ofReal ((y i : ℝ) ^ r) ∂q) +
          (∫⁻ y : ℤ → Ioi (0 : ℝ), ENNReal.ofReal ((y i : ℝ) ^ (-r)) ∂q) ≤
            ENNReal.ofReal D := by
  obtain ⟨D, hD, hf, hqD⟩ := periodicGapLaw_limit_moment_bound p V hV q hq r hr
  refine ⟨max D 2, lt_of_lt_of_le hD (le_max_left _ _), ?_, fun i =>
    (hqD i).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))⟩
  intro N i
  by_cases hN : 2 ≤ (N : ℕ)
  · exact (hf N hN i).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hN1 : N = 1 := PNat.eq (by have := N.pos; simp only [PNat.val_ofNat]; omega)
  subst N
  have := gibbsMeasure_probability p 1
  have hm : Measurable (fun y : ℤ → Ioi (0 : ℝ) => (y i : ℝ)) :=
    measurable_subtype_coe.comp (measurable_pi_apply i)
  rw [lintegral_periodicGapLaw p 1 (hm.pow_const r).ennreal_ofReal,
    lintegral_periodicGapLaw p 1 (hm.pow_const (-r)).ennreal_ofReal]
  simp only [periodicGapSequence_one, Real.one_rpow, ENNReal.ofReal_one,
    lintegral_const, measure_univ, mul_one]
  have he := ENNReal.ofReal_le_ofReal (le_max_right D 2)
  norm_num at he ⊢

/-- Internal Borel--Cantelli step: starting labels may vary with the span length,
which includes the backward blocks ending at label minus one. -/
theorem gapSequenceSpan_average_internal
    (q : ProbabilityMeasure (ℤ → Ioi (0 : ℝ)))
    {α δ C c : ℝ} (hα : α < 1) (hδ : 0 < δ) (_hC : 0 < C) (hc : 0 < c)
    (hb : ∀ k : ℕ, 1 ≤ k → ∀ i : ℤ,
      q.toMeasure {y | (k : ℝ) ^ α < |gapSequenceSpan y i k - k|} ≤
        ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ δ)))
    (a : ℕ → ℤ) :
    ∀ᵐ y ∂q.toMeasure, Tendsto (fun k : ℕ => gapSequenceSpan y (a k) k / k) atTop (𝓝 1) := by
  let E := fun k : ℕ => {y : ℤ → Ioi (0 : ℝ) |
    (k : ℝ) ^ α < |gapSequenceSpan y (a k) k - k|}
  have hsum : (∑' k : ℕ, q.toMeasure (E k)) ≠ ∞ := by
    apply ne_of_lt
    apply (ENNReal.tsum_le_tsum (fun k => ?_)).trans_lt
      (summable_nat_stretched_exponential C hc hδ).tsum_ofReal_lt_top
    by_cases hk : k = 0
    · subst k
      simp [E, gapSequenceSpan, not_lt_of_ge (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 0) α)]
    · exact hb k (by omega) (a k)
  have hae := ae_eventually_notMem hsum
  filter_upwards [hae] with y hy
  have ht : Tendsto (fun k : ℕ => (k : ℝ) ^ (α - 1)) atTop (𝓝 0) := by
    simpa only [neg_sub, Function.comp_def] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hα)).comp tendsto_natCast_atTop_atTop
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hy, eventually_ge_atTop 1, ht.eventually_lt_const hε] with k hk hk1 hkε
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk1)
  have hdev : |gapSequenceSpan y (a k) k - k| ≤ (k : ℝ) ^ α := le_of_not_gt hk
  rw [Real.dist_eq, show gapSequenceSpan y (a k) k / k - 1 =
    (gapSequenceSpan y (a k) k - k) / k by field_simp,
    abs_div, abs_of_pos hkR]
  calc
    _ ≤ (k : ℝ) ^ α / k := div_le_div_of_nonneg_right hdev hkR.le
    _ = (k : ℝ) ^ (α - 1) := by rw [Real.rpow_sub hkR, Real.rpow_one]
    _ < ε := hkε

/-- The almost-sure average conclusion of the proof of Theorem 3,
for every subsequential gap limit at diverging volumes. -/
theorem periodicGapLaw_limit_averages (p : Parameters) (V : ℕ → ℕ+)
    (hV : ∀ n, 2 ≤ (V n : ℕ)) (hVtop : Tendsto (fun n => (V n : ℕ)) atTop atTop)
    (q : ProbabilityMeasure (ℤ → Ioi (0 : ℝ)))
    (hq : Tendsto (fun n => periodicGapLaw p (V n)) atTop (𝓝 q)) :
    ∀ᵐ y ∂q.toMeasure,
      Tendsto (fun k : ℕ => gapSequenceSpan y 0 k / k) atTop (𝓝 1) ∧
        Tendsto (fun k : ℕ => gapSequenceSpan y (-(k : ℤ)) k / k) atTop (𝓝 1) := by
  obtain ⟨η₀, hη₀, hsmall, hb⟩ := periodicGapLaw_limit_rigidity p V hV hVtop q hq
  obtain ⟨C, c, hC, hc, hb⟩ := hb (η₀ / 2) (half_pos hη₀) (half_lt_self hη₀)
  have hα : min p.val.2 1 / 2 + η₀ / 2 < 1 := by linarith
  have hδ : 0 < (η₀ / 2) / (4 * (p.val.2 + 2)) := by
    apply div_pos (half_pos hη₀)
    have := p.property.2.1
    positivity
  exact (gapSequenceSpan_average_internal q hα hδ hC hc hb (fun _ => 0)).and
    (gapSequenceSpan_average_internal q hα hδ hC hc hb (fun k => -(k : ℤ)))

/-- Positive limiting averages force the unnormalized sums to diverge. -/
lemma gapSequenceSpan_diverges_of_average_internal
    (y : ℤ → Ioi (0 : ℝ)) (a : ℕ → ℤ)
    (h : Tendsto (fun k : ℕ => gapSequenceSpan y (a k) k / k) atTop (𝓝 1)) :
    Tendsto (fun k : ℕ => gapSequenceSpan y (a k) k) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  have hb := (tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop)
    |>.eventually (eventually_ge_atTop (2 * b))
  filter_upwards [h.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    hb, eventually_ge_atTop 1] with k hk hkb hk1
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk1)
  have hlow := (lt_div_iff₀ hkR).mp hk
  linarith

/-- The ordinary-gap Cauchy estimate gives the gap-limit conclusions in the
proof of Theorem 3: a unique weak limit, integer shift invariance, mean one,
uniform positive and inverse moments, uniform span deviations and
almost-sure forward and backward averages. The divergent-sum conclusion
allows reconstruction. -/
theorem convergence_gap_limit_from_cauchy_internal
    (hcomparison :
      ∀ (p : Parameters) (ζ : ℝ), 0 < ζ → ∃ C : ℝ, 0 < C ∧
        ∀ (n N N' : ℕ+) (_ : 2 ≤ (n : ℕ)),
          (N : ℕ) ≤ (N' : ℕ) → 4 * (n : ℕ) ≤ (N : ℕ) →
          (n : ℝ) ^ (2 / p.val.2) ≤ (N : ℝ) →
          ∀ (G : BlockObservable n) (J : Finset (Fin (n : ℕ))),
            MiddleConsecutiveBlock n J → DependsOnBlockCoordinates G J →
            Integrable (fun X : Riesz1.Configuration N => G.val (finiteGapBlock X))
              (gibbsMeasure p N) ∧
            Integrable (fun X : Riesz1.Configuration N' => G.val (finiteGapBlock X))
              (gibbsMeasure p N') ∧
            |(∫ X : Riesz1.Configuration N, G.val (finiteGapBlock X) ∂gibbsMeasure p N) -
              (∫ X : Riesz1.Configuration N', G.val (finiteGapBlock X) ∂gibbsMeasure p N')| ≤
              C * (n : ℝ) ^ (-min p.val.2 1 / 2 + ζ) * blockDerivativeNorm G)
    (p : Parameters) :
    ∃! q : ProbabilityMeasure (ℤ → Ioi (0 : ℝ)),
      Tendsto (fun n : ℕ => periodicGapLaw p n.succPNat) atTop (𝓝 q) ∧
      (∀ a : ℤ, q.map (gapIndexShift a) = q) ∧
      (∀ i : ℤ, Integrable (fun y : ℤ → Ioi (0 : ℝ) => (y i : ℝ)) q ∧
        (∫ y : ℤ → Ioi (0 : ℝ), (y i : ℝ) ∂q) = 1) ∧
      (∀ r : ℝ, 0 < r → ∃ D : ℝ, 0 < D ∧
        (∀ (N : ℕ+) (i : ℤ),
          (∫⁻ y : ℤ → Ioi (0 : ℝ), ENNReal.ofReal ((y i : ℝ) ^ r) ∂periodicGapLaw p N) +
            (∫⁻ y : ℤ → Ioi (0 : ℝ), ENNReal.ofReal ((y i : ℝ) ^ (-r))
              ∂periodicGapLaw p N) ≤ ENNReal.ofReal D) ∧
        ∀ i : ℤ,
          (∫⁻ y : ℤ → Ioi (0 : ℝ), ENNReal.ofReal ((y i : ℝ) ^ r) ∂q) +
            (∫⁻ y : ℤ → Ioi (0 : ℝ), ENNReal.ofReal ((y i : ℝ) ^ (-r)) ∂q) ≤
              ENNReal.ofReal D) ∧
      (∃ η₀ : ℝ, 0 < η₀ ∧ min p.val.2 1 / 2 + η₀ < 1 ∧
        ∀ η : ℝ, 0 < η → η < η₀ → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
          ∀ k : ℕ, 1 ≤ k → ∀ i : ℤ,
            q.toMeasure {y | (k : ℝ) ^ (min p.val.2 1 / 2 + η) < |gapSequenceSpan y i k - k|} ≤
              ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ (η / (4 * (p.val.2 + 2)))))) ∧
      (∀ᵐ y ∂q.toMeasure,
        Tendsto (fun k : ℕ => gapSequenceSpan y 0 k / k) atTop (𝓝 1) ∧
          Tendsto (fun k : ℕ => gapSequenceSpan y (-(k : ℤ)) k / k) atTop (𝓝 1)) ∧
      (∀ᵐ y ∂q.toMeasure,
        Tendsto (fun k : ℕ => gapSequenceSpan y 0 k) atTop atTop ∧
          Tendsto (fun k : ℕ => gapSequenceSpan y (-(k : ℤ)) k) atTop atTop) := by
  obtain ⟨q, hq, huniq⟩ := periodicGapLaw_exists_unique_limit_internal hcomparison p
  let V : ℕ → ℕ+ := fun n => (n + 1).succPNat
  have hV : ∀ n, 2 ≤ (V n : ℕ) := by intro n; simp [V]
  have hVtop : Tendsto (fun n => (V n : ℕ)) atTop atTop := by
    simpa only [V, Nat.succPNat_coe, Nat.add_assoc, one_add_one_eq_two] using
      (tendsto_add_atTop_nat 2)
  have hqV : Tendsto (fun n => periodicGapLaw p (V n)) atTop (𝓝 q) :=
    (tendsto_add_atTop_iff_nat 1).mpr hq
  have havg := periodicGapLaw_limit_averages p V hV hVtop q hqV
  refine ⟨q, ⟨hq, periodicGapLaw_limit_shift p V hV q hqV,
    periodicGapLaw_limit_mean p V hV q hqV,
    periodicGapLaw_limit_all_moments p V hV q hqV,
    periodicGapLaw_limit_rigidity p V hV hVtop q hqV, havg, ?_⟩,
    fun q' hq' => huniq q' hq'.1⟩
  filter_upwards [havg] with y hy
  exact ⟨gapSequenceSpan_diverges_of_average_internal y (fun _ => 0) hy.1,
    gapSequenceSpan_diverges_of_average_internal y (fun k => -(k : ℤ)) hy.2⟩

end Riesz2
