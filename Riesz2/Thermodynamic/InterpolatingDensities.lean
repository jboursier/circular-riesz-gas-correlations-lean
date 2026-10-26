/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.ObservableTransfer
public import Riesz2.Frozen.BlockDerivativeNorm
public import Riesz2.Frozen.ActiveTiltedGapLaw
public import Riesz2.HelfferSjostrand.ConditionalWellPosednessPart2
public import Riesz1.ToMathlib.LipschitzExpectationL2
public import Riesz2.Thermodynamic.LocalLimitUniqueness

/-!
# Two-sided tilts and common length fibres

Bridges from the existing finite-set tilt calculus to the first-block law, and estimates
used by the proof of Proposition 6.6. The ambient law, microscopic gaps and penalties
retain their meanings.
-/

public section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace Riesz2.InterpolatingDensities

/-- The first block as a finite subset of the existing particle labels. -/
def activeLabels (N n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ)) : Finset (Fin (N : ℕ)) :=
  Finset.univ.map (Fin.castLEEmb hn)

/-- The selected block has its stated size, including a full cycle. -/
theorem card_activeLabels (N n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ)) :
    (activeLabels N n hn).card = (n : ℕ) := by
  simp [activeLabels]

/-- See Subsection 6.1 of the paper: the finite-set penalty is the first-block penalty. This bridge holds for both source penalties. -/
theorem activeGapPenalty_eq (N n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ) (b : Bool) :
    DecayShort.activeGapPenalty θ ((n : ℝ) ^ ε) b (activeLabels N n hn) =
      physicalGapPenalty N n hn θ ε b := by
  funext X
  simp only [DecayShort.activeGapPenalty, activeLabels, Finset.sum_map,
    physicalGapPenalty]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.castLEEmb_apply, Fin.val_castLE]
  rw [Real.rpow_neg (show (0 : ℝ) ≤ n by positivity)]
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  have hu : gap X (↑i) * ((n : ℝ) ^ ε)⁻¹ = ((n : ℝ) ^ ε)⁻¹ * gap X (↑i) := mul_comm _ _
  have hl : (gap X (↑i))⁻¹ * ((n : ℝ) ^ ε)⁻¹ =
      ((n : ℝ) ^ ε)⁻¹ * (gap X (↑i))⁻¹ := mul_comm _ _
  rw [hu, hl]

/-- The existing finite-set tilt is exactly the probability law. -/
theorem activeTilt_eq (p : Parameters) (N n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ) (b : Bool) :
    DecayShort.activeTilt p N θ ((n : ℝ) ^ ε) b (activeLabels N n hn) =
      tiltedParticleMeasure p N n hn θ ε b := by
  simp only [DecayShort.activeTilt, activeGapPenalty_eq, NonnegativeTilt.expTilt,
    tiltedParticleMeasure, tiltNormalizer]

/-- The real and extended normalizers agree. In particular no totalized
Bochner integral is used in place of a divergent normalization. -/
theorem normalizer_eq (p : Parameters) (N n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ) (b : Bool) :
    tiltNormalizer p N n hn θ ε b = ENNReal.ofReal
      (NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
        (physicalGapPenalty N n hn θ ε b)) := by
  have := gibbsMeasure_probability p N
  have hR : 0 ≤ (n : ℝ) ^ ε := Real.rpow_nonneg (by positivity) _
  change (∫⁻ X, ENNReal.ofReal (Real.exp (-p.val.1 * physicalGapPenalty N n hn θ ε b X))
    ∂gibbsMeasure p N) = _
  rw [← activeGapPenalty_eq N n hn θ ε b]
  exact NonnegativeTilt.lintegral_normalizer_eq
    (DecayShort.activeGapPenalty_measurable θ hR b _)
    p.property.1.le (DecayShort.activeGapPenalty_nonneg θ hR b _)

/-- Positive finite normalization and probability for every first-block
penalty. See Subsection 6.1. -/
theorem tilt_valid (p : Parameters) (N n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ) (b : Bool) :
    0 < tiltNormalizer p N n hn θ ε b ∧ tiltNormalizer p N n hn θ ε b ≤ 1 ∧
      IsProbabilityMeasure (tiltedParticleMeasure p N n hn θ ε b) := by
  have := gibbsMeasure_probability p N
  have hG := DecayShort.activeGapPenalty_measurable (N := N) θ
    (show 0 ≤ (n : ℝ) ^ ε by positivity) b (activeLabels N n hn)
  have hG0 := DecayShort.activeGapPenalty_nonneg (N := N) θ
    (show 0 ≤ (n : ℝ) ^ ε by positivity) b (activeLabels N n hn)
  rw [activeGapPenalty_eq] at hG hG0
  refine ⟨?_, ?_, ?_⟩
  · rw [normalizer_eq]
    exact ENNReal.ofReal_pos.mpr (NonnegativeTilt.expTiltNormalizer_pos hG p.property.1.le hG0)
  · rw [normalizer_eq]
    exact ENNReal.ofReal_le_one.mpr
      (NonnegativeTilt.expTiltNormalizer_le_one hG p.property.1.le hG0)
  · rw [← activeTilt_eq]
    exact DecayShort.activeTilt_isProbabilityMeasure p θ (by positivity) b _

/-- Both exponential tails have the common stretched exponent
`ε min(s,1)`. No lower bound on `n^ε/2` is needed. -/
theorem internal_two_tail_bound {s β ε A : ℝ} (hs : 0 < s) (hβ : 0 < β)
    (hε : 0 < ε) (hA : 0 ≤ A) {x : ℝ} (hx : 1 ≤ x) :
    3 * Real.exp (-(Real.log 2 / 4) * (x ^ ε / 2)) +
        A * Real.exp (-β * (x ^ ε / 2) ^ s) ≤
      (3 + A) * Real.exp (-(min (Real.log 2 / 8) (β / 2 ^ s)) *
        x ^ (ε * min s 1)) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hm : 0 < min s 1 := lt_min hs zero_lt_one
  have hp : x ^ (ε * min s 1) ≤ x ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hx (by nlinarith [min_le_right s 1])
  have hq : x ^ (ε * min s 1) ≤ x ^ (ε * s) :=
    Real.rpow_le_rpow_of_exponent_le hx (mul_le_mul_of_nonneg_left (min_le_left s 1) hε.le)
  have he : (x ^ ε / 2) ^ s = x ^ (ε * s) / 2 ^ s := by
    rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hx0.le]
  have hc0 : 0 < Real.log 2 / 8 := div_pos (Real.log_pos one_lt_two) (by norm_num)
  have hβs : 0 < β / 2 ^ s := div_pos hβ (by positivity)
  have hu : min (Real.log 2 / 8) (β / 2 ^ s) * x ^ (ε * min s 1) ≤
      (Real.log 2 / 4) * (x ^ ε / 2) := by
    calc
      _ ≤ (Real.log 2 / 8) * x ^ ε :=
        mul_le_mul (min_le_left _ _) hp (by positivity) hc0.le
      _ = _ := by ring
  have hl : min (Real.log 2 / 8) (β / 2 ^ s) * x ^ (ε * min s 1) ≤
      β * (x ^ ε / 2) ^ s := by
    rw [he]
    calc
      _ ≤ (β / 2 ^ s) * x ^ (ε * s) :=
        mul_le_mul (min_le_right _ _) hq (by positivity) hβs.le
      _ = _ := by ring
  calc
    _ ≤ 3 * Real.exp (-(min (Real.log 2 / 8) (β / 2 ^ s)) * x ^ (ε * min s 1)) +
        A * Real.exp (-(min (Real.log 2 / 8) (β / 2 ^ s)) * x ^ (ε * min s 1)) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.exp_le_exp.mpr (by linarith)
      · apply mul_le_mul_of_nonneg_left _ hA
        exact Real.exp_le_exp.mpr (by linarith)
    _ = _ := by ring

/-- Uniform positive normalization and a stretched exponential bound on the
support of the penalty, the quantitative core of
the proof of Proposition 6.6. Constants precede both sizes. -/
theorem penalty_support_and_normalizer (s β ε : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (hβ : 0 < β) (hε : 0 < ε) (θ : PhysicalCutoff) :
    ∃ z C c δ : ℝ, 0 < z ∧ 0 < C ∧ 0 < c ∧ 0 < δ ∧
      ∀ p : Parameters, p.val.2 = s → p.val.1 = β →
      ∀ N n : ℕ+, 2 ≤ (N : ℕ) → ∀ hn : (n : ℕ) ≤ (N : ℕ),
      (gibbsMeasure p N).real {X | physicalGapPenalty N n hn θ ε true X ≠ 0} ≤
        C * Real.exp (-c * (n : ℝ) ^ δ) ∧
      z ≤ NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
        (physicalGapPenalty N n hn θ ε true) := by
  obtain ⟨A, hA, hi⟩ := DecayShort.gap_inverse_tail hs hβ
  obtain ⟨K, hK, hθ⟩ := θ.exists_sq_bound
  obtain ⟨D, hD, hmoment⟩ := DecayShort.gap_moment_bound hs hs1 hβ 2 (by norm_num)
  let δ := ε * min s 1
  let c := min (Real.log 2 / 8) (β / 2 ^ s)
  have hδ : 0 < δ := mul_pos hε (lt_min hs zero_lt_one)
  have hc : 0 < c := lt_min
    (div_pos (Real.log_pos one_lt_two) (by norm_num)) (div_pos hβ (by positivity))
  obtain ⟨B, hB, hb⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := 1) (c := c) (c' := c / 2) hδ (by linarith)
  let C := (3 + A) * B + 1
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨n0, hn0⟩ := DecayShort.exists_threshold_exp
    (Kq := C) (c := c / 2) hδ (by linarith)
  let z := min (1 / 2) (Real.exp (-β * ((n0 : ℝ) * (K * D))))
  have hz : 0 < z := lt_min (by norm_num) (Real.exp_pos _)
  refine ⟨z, C, c / 2, δ, hz, hC, by positivity, hδ, ?_⟩
  intro p hps hpβ N n hN hn
  have := gibbsMeasure_probability p N
  let I := activeLabels N n hn
  have hcard : I.card = (n : ℕ) := card_activeLabels N n hn
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast n.pos
  have hR1 : 1 ≤ (n : ℝ) ^ ε := Real.one_le_rpow hn1 hε.le
  have hR : 0 < (n : ℝ) ^ ε := by positivity
  have hrare : (gibbsMeasure p N).real {X | physicalGapPenalty N n hn θ ε true X ≠ 0} ≤
      C * Real.exp (-(c / 2) * (n : ℝ) ^ δ) := by
    rw [← activeGapPenalty_eq]
    have ht := DecayShort.activeGapPenalty_measureReal_le p hN θ hs.le hR hA.le
      (hi p hps hpβ N hN) true I
    rw [hcard] at ht
    apply ht.trans
    calc
      _ ≤ (n : ℝ) * ((3 + A) * Real.exp (-c * (n : ℝ) ^ δ)) :=
        mul_le_mul_of_nonneg_left (internal_two_tail_bound hs hβ hε hA.le hn1) (by positivity)
      _ = (3 + A) * ((n : ℝ) * Real.exp (-c * (n : ℝ) ^ δ)) := by ring
      _ ≤ (3 + A) * (B * Real.exp (-(c / 2) * (n : ℝ) ^ δ)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        simpa only [Real.rpow_one] using hb (n : ℝ) hn1
      _ ≤ C * Real.exp (-(c / 2) * (n : ℝ) ^ δ) := by
        dsimp only [C]
        nlinarith [Real.exp_pos (-(c / 2) * (n : ℝ) ^ δ)]
  refine ⟨hrare, ?_⟩
  rw [← activeGapPenalty_eq]
  rcases le_total (n : ℕ) n0 with hsmall | hlarge
  · have hj := DecayShort.expTiltNormalizer_ge_of_card p θ hK hθ hR1
      (fun j => hmoment p hps hpβ N hN j) true I
    rw [hcard] at hj
    rw [hpβ]
    rw [hpβ] at hj
    apply (min_le_right _ _).trans
    apply le_trans _ hj
    apply Real.exp_le_exp.mpr
    have hnn : (n : ℝ) ≤ (n0 : ℝ) := by exact_mod_cast hsmall
    have hmul := mul_le_mul_of_nonneg_right hnn (show 0 ≤ β * (K * D) by positivity)
    nlinarith
  · have hhalf := hn0 (n : ℕ) hlarge
    have hG := DecayShort.activeGapPenalty_measurable θ hR.le true I
    have hG0 := DecayShort.activeGapPenalty_nonneg θ hR.le true I
    have hone := NonnegativeTilt.one_sub_expTiltNormalizer_le
      (μ := gibbsMeasure p N) hG p.property.1.le hG0
    rw [activeGapPenalty_eq] at hone ⊢
    exact (min_le_left _ _).trans (by linarith)

/-- The least coordinate Lipschitz constant satisfies its defining
inequality. The infimum is attained in its closed nonempty set. -/
theorem coordinate_bound {n : ℕ+} (G : BlockObservable n) (j : Fin (n : ℕ))
    (x : Fin (n : ℕ) → ℝ) (t : ℝ) :
    |G.val (Function.update x j t) - G.val x| ≤
      (coordinateDerivativeNorm G j : ℝ) * |t - x j| := by
  let S := {L : ℝ≥0 | ∀ (x : Fin (n : ℕ) → ℝ) (t : ℝ),
    |G.val (Function.update x j t) - G.val x| ≤ (L : ℝ) * |t - x j|}
  have hne : S.Nonempty := by
    obtain ⟨L, hL⟩ := G.property
    refine ⟨L, fun x t => ?_⟩
    have hd : dist (Function.update x j t) x ≤ |t - x j| := by
      apply (dist_pi_le_iff (abs_nonneg _)).mpr
      intro k
      by_cases hk : k = j
      · subst k; simp [Real.dist_eq]
      · simp [Function.update_of_ne hk, abs_nonneg]
    exact (hL.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left hd L.property)
  have hclosed : IsClosed S := by
    simp only [S, ofPred_forall]
    apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro t
    exact isClosed_le continuous_const (continuous_subtype_val.mul_const _)
  exact (hclosed.csInf_mem hne (OrderBot.bddBelow S)) x t

/-- See Theorem 4 of the paper: coordinate telescoping gives the exact sum of
the coordinate derivative norms, including nonsmooth observables. -/
theorem block_bound {n : ℕ+} (G : BlockObservable n) (x y : Fin (n : ℕ) → ℝ) :
    |G.val y - G.val x| ≤ ∑ j, (coordinateDerivativeNorm G j : ℝ) * |y j - x j| := by
  classical
  have haux (S : Finset (Fin (n : ℕ))) :
      |G.val (S.piecewise y x) - G.val x| ≤
        ∑ j ∈ S, (coordinateDerivativeNorm G j : ℝ) * |y j - x j| := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert j S hj ih =>
      rw [Finset.piecewise_insert, Finset.sum_insert hj]
      have hb := coordinate_bound G j (S.piecewise y x) (y j)
      rw [Finset.piecewise_eq_of_notMem S y x hj] at hb
      calc
        _ ≤ |G.val (Function.update (S.piecewise y x) j (y j)) - G.val (S.piecewise y x)| +
            |G.val (S.piecewise y x) - G.val x| := abs_sub_le _ _ _
        _ ≤ _ := add_le_add hb ih
  simpa using haux Finset.univ

/-- Internal block version of the `L²` domination used in penalty removal.
The observable and its coordinate constants are the objects. -/
theorem internal_centered_block_norm {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ+} (G : BlockObservable n)
    (X : Ω → Fin (n : ℕ) → ℝ) (hX : ∀ j, Measurable (fun ω => X ω j))
    {K : ℝ} (hK : 0 ≤ K) (hXnorm : ∀ j, eLpNorm (fun ω => X ω j) 2 μ ≤ ENNReal.ofReal K) :
    MemLp (fun ω => G.val (X ω) - G.val (fun _ => 1)) 2 μ ∧
      Real.sqrt (∫ ω, (G.val (X ω) - G.val (fun _ => 1)) ^ 2 ∂μ) ≤
        (K + 1) * blockDerivativeNorm G := by
  classical
  let a := fun j => (coordinateDerivativeNorm G j : ℝ)
  let F := fun ω => G.val (X ω) - G.val (fun _ => 1)
  let H := fun ω => ∑ j, a j * |X ω j - 1|
  have ha (j) : 0 ≤ a j := (coordinateDerivativeNorm G j).property
  have hmF : Measurable F :=
    (G.property.choose_spec.continuous.measurable.comp (Measurable.of_eval hX)).sub_const _
  have hnorm (j) : eLpNorm (fun ω => X ω j - 1) 2 μ ≤ ENNReal.ofReal (K + 1) := by
    have ht := (eLpNorm_sub_le (μ := μ) (f := fun ω => X ω j)
      (g := fun _ => (1 : ℝ)) (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
      (add_le_add (hXnorm j) le_rfl)
    have hone : eLpNorm (fun _ : Ω => (1 : ℝ)) 2 μ = 1 := by
      rw [eLpNorm_const 1 (by norm_num) (NeZero.ne μ)]
      simp
    rw [ENNReal.ofReal_add hK (by norm_num), ENNReal.ofReal_one]
    simpa only [Pi.sub_def, hone] using ht
  have hterm (j) : eLpNorm (fun ω => a j * |X ω j - 1|) 2 μ ≤
      ENNReal.ofReal (a j * (K + 1)) := by
    have he : eLpNorm (fun ω => |X ω j - 1|) 2 μ =
        eLpNorm (fun ω => X ω j - 1) 2 μ := by
      simpa only [Real.norm_eq_abs] using eLpNorm_norm (fun ω => X ω j - 1)
        ((hX j).sub_const 1).aestronglyMeasurable
    change eLpNorm ((a j) • (fun ω => |X ω j - 1|)) 2 μ ≤ _
    rw [eLpNorm_const_smul, he, Real.enorm_eq_ofReal_abs, abs_of_nonneg (ha j),
      ENNReal.ofReal_mul (ha j)]
    exact mul_le_mul_of_nonneg_left (hnorm j) zero_le
  have hsum : eLpNorm H 2 μ ≤ ENNReal.ofReal ((K + 1) * blockDerivativeNorm G) := by
    have he : H = ∑ j, (fun ω => a j * |X ω j - 1|) := by
      funext ω
      simp only [H, Finset.sum_apply]
    rw [he]
    apply (eLpNorm_sum_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
    apply (Finset.sum_le_sum fun j _ => hterm j).trans_eq
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (ha j) (by linarith)),
      ← Finset.sum_mul]
    congr 1
    dsimp only [blockDerivativeNorm, a]
    ring
  have hb : ∀ ω, ‖F ω‖ ≤ ‖H ω‖ := by
    intro ω
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ H ω by
      exact Finset.sum_nonneg fun j _ => mul_nonneg (ha j) (abs_nonneg _))]
    exact block_bound G (fun _ => 1) (X ω)
  have hbound := (eLpNorm_mono_ae hmF.aestronglyMeasurable (ae_of_all _ hb)).trans hsum
  have hF : MemLp F 2 μ := hbound.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hF, ?_⟩
  rw [← Riesz1.eLpNorm_two_toReal_eq_sqrt_integral_sq hF]
  exact ENNReal.toReal_le_of_le_ofReal
    (mul_nonneg (by linarith) (Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _)) hbound

/-- A block observable is integrable under every finite law on a fixed
configuration space. The volume-dependent bound is used only here to
establish integrability, never in the uniform comparison estimate. -/
theorem block_integrable (N n : ℕ+) (G : BlockObservable n)
    (μ : Measure (Riesz1.Configuration N)) [IsFiniteMeasure μ] :
    Integrable (fun X => G.val (finiteGapBlock (K := n) X)) μ := by
  have hmeas : Measurable (fun X : Riesz1.Configuration N => G.val (finiteGapBlock (K := n) X)) :=
    G.property.choose_spec.continuous.measurable.comp
      (Measurable.of_eval fun j => Riesz1.measurable_gap j.val)
  apply (integrable_const (blockDerivativeNorm G * ((N : ℝ) + 1) + |G.val (fun _ => 1)|)).mono'
    hmeas.aestronglyMeasurable
  apply ae_of_all
  intro X
  rw [Real.norm_eq_abs]
  calc
    |G.val (finiteGapBlock X)| ≤ |G.val (finiteGapBlock X) - G.val (fun _ => 1)| +
        |G.val (fun _ => 1)| := by
      have ht := abs_add_le (G.val (finiteGapBlock X) - G.val (fun _ => 1)) (G.val (fun _ => 1))
      simpa only [sub_add_cancel] using ht
    _ ≤ (∑ j, (coordinateDerivativeNorm G j : ℝ) * |gap X j.val - 1|) +
        |G.val (fun _ => 1)| := add_le_add (block_bound G (fun _ => 1) (finiteGapBlock X)) le_rfl
    _ ≤ (∑ j, (coordinateDerivativeNorm G j : ℝ) * ((N : ℝ) + 1)) +
        |G.val (fun _ => 1)| := by
      apply add_le_add _ le_rfl
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg _)
      have hgap := Riesz1.gap_le_N X j.val
      have hg := Riesz1.gap_pos X j.val
      change gap X j.val ≤ (N : ℝ) at hgap
      change 0 < gap X j.val at hg
      have hN0 : 0 ≤ (N : ℝ) := by positivity
      rw [abs_le]
      constructor <;> linarith
    _ = _ := by rw [← Finset.sum_mul]; rfl

/-- All positive and inverse moments under the two-sided tilt are uniformly
bounded in both sizes. The moment clause of the proof of Proposition 6.6.
Extended integrals explicitly assert finiteness. -/
theorem tilted_gap_moments (s β ε : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (hβ : 0 < β) (hε : 0 < ε) (θ : PhysicalCutoff) (r : ℝ) (hr : 0 < r) :
    ∃ M : ℝ, 0 < M ∧ ∀ p : Parameters, p.val.2 = s → p.val.1 = β →
      ∀ N n : ℕ+, 2 ≤ (N : ℕ) → ∀ hn : (n : ℕ) ≤ (N : ℕ), ∀ j : ℤ,
        (∫⁻ X, ENNReal.ofReal (gap X j ^ r) ∂tiltedParticleMeasure p N n hn θ ε true) +
          (∫⁻ X, ENNReal.ofReal (gap X j ^ (-r)) ∂tiltedParticleMeasure p N n hn θ ε true) ≤
            ENNReal.ofReal M := by
  obtain ⟨z, C, c, δ, hz, _, _, _, hrate⟩ := penalty_support_and_normalizer s β ε hs hs1 hβ hε θ
  obtain ⟨D, hD, hm⟩ := SingleGapTails.single_gap_moment_integrals s β β hs hs1 hβ le_rfl r hr
  refine ⟨z⁻¹ * D, mul_pos (inv_pos.mpr hz) hD, fun p hps hpβ N n hN hn j => ?_⟩
  have := gibbsMeasure_probability p N
  have hR : 0 ≤ (n : ℝ) ^ ε := by positivity
  have hG := DecayShort.activeGapPenalty_measurable (N := N) θ hR true (activeLabels N n hn)
  have hG0 := DecayShort.activeGapPenalty_nonneg (N := N) θ hR true (activeLabels N n hn)
  have hZ := (hrate p hps hpβ N n hN hn).2
  rw [← activeGapPenalty_eq] at hZ
  have hp := NonnegativeTilt.lintegral_expTilt_le (μ := gibbsMeasure p N) hG p.property.1.le hG0
    (((Riesz1.measurable_gap j).pow_const r).ennreal_ofReal)
  have hi := NonnegativeTilt.lintegral_expTilt_le (μ := gibbsMeasure p N) hG p.property.1.le hG0
    (((Riesz1.measurable_gap j).pow_const (-r)).ennreal_ofReal)
  rw [← activeTilt_eq, DecayShort.activeTilt]
  apply (add_le_add hp hi).trans
  rw [← mul_add, NonnegativeTilt.lintegral_normalizer_eq hG p.property.1.le hG0,
    ENNReal.ofReal_mul (inv_nonneg.mpr hz.le)]
  apply mul_le_mul
  · rw [ENNReal.ofReal_inv_of_pos hz]
    exact ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal hZ)
  · exact (hm p hps hpβ.ge hpβ.le N hN j).2.2
  · exact zero_le
  · exact zero_le

/-- Total variation removal of the two-sided penalty on the full gap law. The total variation clause of the proof of Proposition 6.6. -/
theorem tilt_totalVariation (s β ε : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (hβ : 0 < β) (hε : 0 < ε) (θ : PhysicalCutoff) :
    ∃ C c δ : ℝ, 0 < C ∧ 0 < c ∧ 0 < δ ∧
      ∀ p : Parameters, p.val.2 = s → p.val.1 = β →
      ∀ N n : ℕ+, 2 ≤ (N : ℕ) → ∀ hn : (n : ℕ) ≤ (N : ℕ),
      letI := gibbsMeasure_probability p N
      letI := (tilt_valid p N n hn θ ε true).2.2
      letI : IsProbabilityMeasure (gapLaw p N) := by unfold gapLaw; infer_instance
      totalVariation ((tiltedParticleMeasure p N n hn θ ε true).map (gapVector (N := N)))
        (gapLaw p N) ≤ ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ δ)) := by
  obtain ⟨z, C, c, δ, _, hC, hc, hδ, hrate⟩ := penalty_support_and_normalizer s β ε hs hs1 hβ hε θ
  refine ⟨C, c, δ, hC, hc, hδ, fun p hps hpβ N n hN hn => ?_⟩
  have := gibbsMeasure_probability p N
  have : IsProbabilityMeasure (tiltedParticleMeasure p N n hn θ ε true) :=
    (tilt_valid p N n hn θ ε true).2.2
  have : IsProbabilityMeasure (gapLaw p N) := by unfold gapLaw; infer_instance
  have : IsProbabilityMeasure ((tiltedParticleMeasure p N n hn θ ε true).map (gapVector (N := N))) :=
    by infer_instance
  rw [totalVariation_symm]
  apply (NonnegativeTilt.totalVariation_map_le (gibbsMeasure p N)
    (tiltedParticleMeasure p N n hn θ ε true) (gapVector (N := N))
    (Riesz1.measurable_gapVector N)).trans
  have ht := DecayShort.totalVariation_activeTilt_le p θ
    (show 0 ≤ (n : ℝ) ^ ε by positivity) true (activeLabels N n hn)
  have ht' : totalVariation (gibbsMeasure p N) (tiltedParticleMeasure p N n hn θ ε true) ≤
      ENNReal.ofReal ((gibbsMeasure p N).real
        {X | physicalGapPenalty N n hn θ ε true X ≠ 0}) := by
    simpa only [activeTilt_eq, activeGapPenalty_eq] using ht
  exact ht'.trans (ENNReal.ofReal_le_ofReal (hrate p hps hpβ N n hN hn).1)

/-- Lipschitz expectation comparison in the proof of Proposition 6.6, with
constants before both sizes and the observable. Integrability under both
laws is part of the conclusion. -/
theorem tilt_expectation (s β ε : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (hβ : 0 < β) (hε : 0 < ε) (θ : PhysicalCutoff) :
    ∃ C c δ : ℝ, 0 < C ∧ 0 < c ∧ 0 < δ ∧
      ∀ p : Parameters, p.val.2 = s → p.val.1 = β →
      ∀ N n : ℕ+, 2 ≤ (N : ℕ) → ∀ hn : (n : ℕ) ≤ (N : ℕ), ∀ G : BlockObservable n,
        Integrable (fun X => G.val (finiteGapBlock X)) (gibbsMeasure p N) ∧
        Integrable (fun X => G.val (finiteGapBlock X)) (tiltedParticleMeasure p N n hn θ ε true) ∧
        |(∫ X, G.val (finiteGapBlock X) ∂tiltedParticleMeasure p N n hn θ ε true) -
          (∫ X, G.val (finiteGapBlock X) ∂gibbsMeasure p N)| ≤
            C * Real.exp (-c * (n : ℝ) ^ δ) * blockDerivativeNorm G := by
  obtain ⟨z, A, c, δ, hz, hA, hc, hδ, hrate⟩ := penalty_support_and_normalizer s β ε hs hs1 hβ hε θ
  obtain ⟨L, hL, hm⟩ := SingleGapTails.single_gap_moments s β β hs hs1 hβ le_rfl 1 (by norm_num)
  let K := L * (2 + (2 : ℝ) ^ (1 / s))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let C := z⁻¹ * (Real.sqrt A + A) * (K + 1)
  have hC : 0 < C := mul_pos (mul_pos (inv_pos.mpr hz) (by positivity)) (by linarith)
  refine ⟨C, c / 2, δ, hC, by positivity, hδ, fun p hps hpβ N n hN hn G => ?_⟩
  have : IsProbabilityMeasure (gibbsMeasure p N) := gibbsMeasure_probability p N
  have : IsProbabilityMeasure (tiltedParticleMeasure p N n hn θ ε true) :=
    (tilt_valid p N n hn θ ε true).2.2
  have hiμ := block_integrable N n G (gibbsMeasure p N)
  have hiQ := block_integrable N n G (tiltedParticleMeasure p N n hn θ ε true)
  refine ⟨hiμ, hiQ, ?_⟩
  have hgapnorm (j : Fin (n : ℕ)) : eLpNorm (fun X : Riesz1.Configuration N => gap X j.val) 2
      (gibbsMeasure p N) ≤ ENNReal.ofReal K := by
    have ht := (hm p hps hpβ.ge hpβ.le N hN j.val 2 (by norm_num)).1
    simp only [Real.rpow_one, ENNReal.ofReal_ofNat] at ht
    exact (le_add_of_nonneg_right zero_le).trans ht
  obtain ⟨hf, hfnorm⟩ := internal_centered_block_norm (gibbsMeasure p N) G
    (finiteGapBlock (K := n)) (fun j => Riesz1.measurable_gap j.val) hK hgapnorm
  have hR : 0 ≤ (n : ℝ) ^ ε := by positivity
  have hG := DecayShort.activeGapPenalty_measurable (N := N) θ hR true (activeLabels N n hn)
  have hG0 := DecayShort.activeGapPenalty_nonneg (N := N) θ hR true (activeLabels N n hn)
  rw [activeGapPenalty_eq] at hG hG0
  obtain ⟨hrare, hZ⟩ := hrate p hps hpβ N n hN hn
  let q := A * Real.exp (-c * (n : ℝ) ^ δ)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have he := NonnegativeTilt.abs_integral_expTilt_sub_le hG p.property.1.le hG0 hf hrare
  have heq : NonnegativeTilt.expTilt (gibbsMeasure p N) p.val.1
      (physicalGapPenalty N n hn θ ε true) = tiltedParticleMeasure p N n hn θ ε true := rfl
  rw [heq, integral_sub hiQ (integrable_const _), integral_sub hiμ (integrable_const _)] at he
  simp only [integral_const, probReal_univ, one_smul, sub_sub_sub_cancel_right] at he
  apply he.trans
  have hZi : (NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N) p.val.1
      (physicalGapPenalty N n hn θ ε true))⁻¹ ≤ z⁻¹ := inv_anti₀ hz hZ
  have hroot : Real.sqrt q = Real.sqrt A * Real.exp (-(c / 2) * (n : ℝ) ^ δ) := by
    apply (Real.sqrt_eq_iff_eq_sq hq (by positivity)).mpr
    rw [mul_pow, Real.sq_sqrt hA.le, ← Real.exp_nat_mul]
    dsimp only [q]
    congr 2
    ring
  have hq' : q ≤ A * Real.exp (-(c / 2) * (n : ℝ) ^ δ) := by
    apply mul_le_mul_of_nonneg_left _ hA.le
    apply Real.exp_le_exp.mpr
    have hp : 0 ≤ (n : ℝ) ^ δ := by positivity
    nlinarith
  have hs : Real.sqrt q + q ≤ (Real.sqrt A + A) * Real.exp (-(c / 2) * (n : ℝ) ^ δ) := by
    rw [hroot]
    nlinarith
  calc
    _ ≤ (z⁻¹ * ((Real.sqrt A + A) * Real.exp (-(c / 2) * (n : ℝ) ^ δ))) *
        ((K + 1) * blockDerivativeNorm G) := by
      apply mul_le_mul _ hfnorm (Real.sqrt_nonneg _) (by positivity)
      exact mul_le_mul hZi hs (by positivity) (by positivity)
    _ = _ := by dsimp [C]; ring

/-- See the proof of Proposition 6.6 in the paper, complete penalty-removal theorem:
total variation, every fixed positive and inverse moment, and Lipschitz
expectations with the coordinate derivative sum. All three rate
constants precede the sizes and observable. -/
theorem distinct_tilt (s β ε : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (hβ : 0 < β) (hε : 0 < ε) (θ : PhysicalCutoff) :
    ∃ C c δ : ℝ, 0 < C ∧ 0 < c ∧ 0 < δ ∧
      (∀ r : ℝ, 0 < r → ∃ M : ℝ, 0 < M ∧
        ∀ p : Parameters, p.val.2 = s → p.val.1 = β →
        ∀ N n : ℕ+, 2 ≤ (n : ℕ) → ∀ hn : (n : ℕ) < (N : ℕ), ∀ j : Fin (n : ℕ),
          (∫⁻ X, ENNReal.ofReal (gap X j.val ^ r)
            ∂tiltedParticleMeasure p N n hn.le θ ε true) +
          (∫⁻ X, ENNReal.ofReal (gap X j.val ^ (-r))
            ∂tiltedParticleMeasure p N n hn.le θ ε true) ≤ ENNReal.ofReal M) ∧
      ∀ p : Parameters, p.val.2 = s → p.val.1 = β →
      ∀ N n : ℕ+, 2 ≤ (n : ℕ) → ∀ hn : (n : ℕ) < (N : ℕ),
        letI := gibbsMeasure_probability p N
        letI := (tilt_valid p N n hn.le θ ε true).2.2
        letI : IsProbabilityMeasure (gapLaw p N) := by unfold gapLaw; infer_instance
        0 < tiltNormalizer p N n hn.le θ ε true ∧
        tiltNormalizer p N n hn.le θ ε true < ⊤ ∧
        totalVariation ((tiltedParticleMeasure p N n hn.le θ ε true).map (gapVector (N := N)))
          (gapLaw p N) ≤ ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ δ)) ∧
        ∀ G : BlockObservable n,
          Integrable (fun X => G.val (finiteGapBlock X)) (gibbsMeasure p N) ∧
          Integrable (fun X => G.val (finiteGapBlock X)) (tiltedParticleMeasure p N n hn.le θ ε true) ∧
          |(∫ X, G.val (finiteGapBlock X) ∂tiltedParticleMeasure p N n hn.le θ ε true) -
            (∫ X, G.val (finiteGapBlock X) ∂gibbsMeasure p N)| ≤
              C * Real.exp (-c * (n : ℝ) ^ δ) * blockDerivativeNorm G := by
  obtain ⟨C₁, c₁, δ₁, hC₁, hc₁, hδ₁, htv⟩ := tilt_totalVariation s β ε hs hs1 hβ hε θ
  obtain ⟨C₂, c₂, δ₂, hC₂, hc₂, hδ₂, hmean⟩ := tilt_expectation s β ε hs hs1 hβ hε θ
  let C := C₁ + C₂
  let c := min c₁ c₂
  let δ := min δ₁ δ₂
  have hC : 0 < C := add_pos hC₁ hC₂
  have hc : 0 < c := lt_min hc₁ hc₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have hrate {x d k A : ℝ} (hx : 1 ≤ x) (hd : δ ≤ d) (hk : c ≤ k)
      (hA : A ≤ C) (hA0 : 0 ≤ A) (hk0 : 0 ≤ k) :
      A * Real.exp (-k * x ^ d) ≤ C * Real.exp (-c * x ^ δ) := by
    have hp := Real.rpow_le_rpow_of_exponent_le hx hd
    have hmul := mul_le_mul hk hp (Real.rpow_nonneg (by linarith) _) hk0
    exact mul_le_mul hA (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le hC.le
  refine ⟨C, c, δ, hC, hc, hδ, ?_, ?_⟩
  · intro r hr
    obtain ⟨M, hM, hm⟩ := tilted_gap_moments s β ε hs hs1 hβ hε θ r hr
    refine ⟨M, hM, fun p hps hpβ N n hn hnN j => ?_⟩
    exact hm p hps hpβ N n (by omega) hnN.le j.val
  · intro p hps hpβ N n hn hnN
    have hN : 2 ≤ (N : ℕ) := by omega
    have hx : 1 ≤ (n : ℝ) := by exact_mod_cast n.pos
    have hv := tilt_valid p N n hnN.le θ ε true
    refine ⟨hv.1, hv.2.1.trans_lt (by norm_num), ?_, ?_⟩
    · exact (htv p hps hpβ N n hN hnN.le).trans (ENNReal.ofReal_le_ofReal
        (hrate hx (min_le_left _ _) (min_le_left _ _) (by dsimp [C]; linarith) hC₁.le hc₁.le))
    · intro G
      obtain ⟨hiμ, hiQ, hm⟩ := hmean p hps hpβ N n hN hnN.le G
      refine ⟨hiμ, hiQ, hm.trans ?_⟩
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun j _ => NNReal.coe_nonneg _)
      exact hrate hx (min_le_right _ _) (min_le_right _ _) (by dsimp [C]; linarith) hC₂.le hc₂.le

end Riesz2.InterpolatingDensities
