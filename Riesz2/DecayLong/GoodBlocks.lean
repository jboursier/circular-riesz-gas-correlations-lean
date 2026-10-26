/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.SingleGapTails
public import Riesz2.HelfferSjostrand.PhysicalEnergy
public import Riesz2.Sanity.TiltedLaws
public import Riesz1.Rigidity.NoExplosionBlocks
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Riesz2.Frozen.External.LongRangeRigidityLocallyUniform
public import Riesz2.ToMathlib.MomentEventBounds

/-!
# Good blocks and physical interval moments

Estimates toward Subsection 5.1, using the
upper-gap tilt. Interval comparisons reuse the companion
library's deterministic inverse-block inequality.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace Riesz2.GoodBlocks

/-- See Subsection 5.1 of the paper: the specified temperature-independent tail power. -/
def blockTailPower (s ε : ℝ) : ℝ :=
  let η := min ε (1 / 4)
  let b := min (η / 8) ((1 - s / 2) / 4)
  min (s * η / 2) (η * b / (16 * (s + 2)))

theorem blockTailPower_pos {s ε : ℝ} (hs : 0 < s) (hs1 : s < 1) (hε : 0 < ε) :
    0 < blockTailPower s ε := by
  have hη : 0 < min ε (1 / 4) := lt_min hε (by norm_num)
  have hb : 0 < min (min ε (1 / 4) / 8) ((1 - s / 2) / 4) :=
    lt_min (by positivity) (by linarith)
  unfold blockTailPower
  exact lt_min (by positivity) (by positivity)

/-- See Subsection 5.1 of the paper: its specified exceptional-set power. -/
def coefficientTailPower (s ε : ℝ) : ℝ :=
  min (blockTailPower s ε) (ε / (2 * ((s + 2) / s)))

theorem coefficientTailPower_pos {s ε : ℝ} (hs : 0 < s) (hs1 : s < 1) (hε : 0 < ε) :
    0 < coefficientTailPower s ε :=
  lt_min (blockTailPower_pos hs hs1 hε) (by positivity)

/-- The complement of an actual particle interval is the next cyclic block. -/
theorem blockLength_complement {N : ℕ+} (X : Riesz1.Configuration N) (i : ℤ)
    {r : ℕ} (hr : r ≤ (N : ℕ)) :
    (N : ℝ) - Riesz1.blockLength X i r =
      Riesz1.blockLength X (i + r) ((N : ℕ) - r) := by
  unfold Riesz1.blockLength
  have he : i + (r : ℤ) + ((N : ℕ) - r : ℕ) = i + (N : ℕ) := by
    rw [Nat.cast_sub hr]
    ring
  rw [he, Riesz1.cyclicLift_add_N]
  ring

/-- The deterministic inverse-block comparison preserves any given `L^q`
bound for the inverse gaps, including its dependence on `q`. -/
theorem inverse_block_norm_le {N : ℕ+} {μ : Measure (Riesz1.Configuration N)}
    {v q M : ℝ} (hv : 0 < v) (hq : 1 ≤ q) (_hM : 0 ≤ M)
    (hgap : ∀ j : ℤ, eLpNorm (fun X : Riesz1.Configuration N => gap X j ^ (-v))
      (ENNReal.ofReal q) μ ≤ ENNReal.ofReal M) (j : ℤ) {r : ℕ} (hr : 0 < r) :
    eLpNorm (fun X : Riesz1.Configuration N => Riesz1.blockLength X j r ^ (-v))
      (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (M * (r : ℝ) ^ (-v)) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hqE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hq
  have hdom := eLpNorm_mono_real
    ((Riesz1.measurable_blockLength j r).pow_const (-v)).aestronglyMeasurable
    (μ := μ) (p := ENNReal.ofReal q)
    (g := fun X => (r : ℝ) ^ (-v) * ((r : ℝ)⁻¹ *
      ∑ a ∈ Finset.range r, gap X (j + a) ^ (-v))) (fun X => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (Riesz1.blockLength_pos X j hr).le _)]
      exact Riesz1.blockLength_inverse_rpow_le X j hr hv)
  have hsum : eLpNorm (fun X : Riesz1.Configuration N =>
      ∑ a ∈ Finset.range r, gap X (j + a) ^ (-v)) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal ((r : ℝ) * M) := by
    refine (show eLpNorm (fun X : Riesz1.Configuration N =>
      ∑ a ∈ Finset.range r, gap X (j + a) ^ (-v)) (ENNReal.ofReal q) μ ≤
        ∑ a ∈ Finset.range r, eLpNorm (fun X : Riesz1.Configuration N =>
          gap X (j + a) ^ (-v)) (ENNReal.ofReal q) μ from by
        simpa only [Finset.sum_fn] using eLpNorm_sum_le (μ := μ)
          (f := fun (a : ℕ) X => gap X (j + a) ^ (-v)) (s := Finset.range r) hqE).trans ?_
    calc
      ∑ a ∈ Finset.range r, eLpNorm (fun X : Riesz1.Configuration N =>
          gap X (j + a) ^ (-v)) (ENNReal.ofReal q) μ ≤
          ∑ _a ∈ Finset.range r, ENNReal.ofReal M := Finset.sum_le_sum (fun a _ => hgap _)
      _ = ENNReal.ofReal ((r : ℝ) * M) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg r), ENNReal.ofReal_natCast]
  have hscale (a : ℝ) (f : Riesz1.Configuration N → ℝ) :
      eLpNorm (fun X => a * f X) (ENNReal.ofReal q) μ =
        ENNReal.ofReal |a| * eLpNorm f (ENNReal.ofReal q) μ := by
    change eLpNorm (a • f) (ENNReal.ofReal q) μ = _
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs]
  rw [hscale, hscale, abs_of_nonneg (Real.rpow_nonneg hr0.le _),
    abs_of_pos (inv_pos.mpr hr0)] at hdom
  refine hdom.trans ((mul_le_mul_right (mul_le_mul_right hsum _) _).trans_eq ?_)
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hr0.le),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hr0.le _)]
  congr 1
  field_simp

/-- See Subsection 5.1 of the paper, inverse-interval input: the sharp moment degree
`v/s` with constants uniform on a compact temperature interval. This holds
for all positive block lengths, without independence of the gaps. -/
theorem inverse_block_moments (s βlo βhi v : ℝ) (hs : 0 < s)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (hv : 0 < v) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Parameters), p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (N : ℕ+), 2 ≤ (N : ℕ) →
      ∀ (j : ℤ) (r : ℕ), 0 < r → ∀ q : ℝ, 1 ≤ q →
        eLpNorm (fun X : Riesz1.Configuration N => Riesz1.blockLength X j r ^ (-v))
          (ENNReal.ofReal q) (gibbsMeasure p N) ≤
            ENNReal.ofReal (C * q ^ (v / s) * (r : ℝ) ^ (-v)) := by
  obtain ⟨A, hA, hInv⟩ := SingleGapTails.inverse_exponential_moment s βlo βhi hs hlo hle
  let C := max A 1 * ((v / s) / (Real.exp 1 * βlo)) ^ (v / s)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro p hps hpl hph N hN j r hr q hq
  apply inverse_block_norm_le hv hq (by positivity) _ j hr
  intro a
  have hi := hInv p hps hpl hph N hN a
  have hh := ExponentialPower.power_eLpNorm_le hlo hA.le (div_pos hv hs)
    ((Riesz1.measurable_gap a).pow_const (-s))
    (fun X : Riesz1.Configuration N => Real.rpow_nonneg (Riesz1.gap_pos X a).le (-s))
    hi.1 hi.2 hq
  have he (X : Riesz1.Configuration N) :
      (gap X a ^ (-s)) ^ (v / s) = gap X a ^ (-v) := by
    rw [← Real.rpow_mul (show 0 ≤ gap X a from (Riesz1.gap_pos X a).le)]
    congr 1
    field_simp
  change eLpNorm (fun X : Riesz1.Configuration N => (gap X a ^ (-s)) ^ (v / s))
    (ENNReal.ofReal q) (gibbsMeasure p N) ≤ _ at hh
  simpa only [he] using hh

/-- See Subsection 5.1 of the paper: the upper penalty vanishes whenever
every active gap is at most half the upper cutoff. -/
theorem penalty_eq_zero (N n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ) (X : Riesz1.Configuration N)
    (hX : ∀ i : Fin (n : ℕ), gap X i.val ≤ (n : ℝ) ^ ε / 2) :
    physicalGapPenalty N n hn θ ε false X = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
  apply θ.property.2.2.2.1
  refine ⟨mul_nonneg (Real.rpow_nonneg (by positivity) _) (Riesz1.gap_pos X _).le, ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  calc
    (n : ℝ) ^ (-ε) * gap X i.val ≤ (n : ℝ) ^ (-ε) * ((n : ℝ) ^ ε / 2) :=
      mul_le_mul_of_nonneg_left (hX i) (Real.rpow_nonneg hn0.le _)
    _ = 1 / 2 := by rw [← mul_div_assoc, ← Real.rpow_add hn0]; simp

/-- The mass on which the upper forcing can be nonzero is small. This
quantitative estimate holds before choosing a large-size threshold. -/
theorem nonzero_penalty_mass_le (p : Parameters) (N n : ℕ+) (hN : 2 ≤ (N : ℕ))
    (hn : (n : ℕ) ≤ (N : ℕ)) (θ : PhysicalCutoff) (ε : ℝ) :
    (gibbsMeasure p N) {X | physicalGapPenalty N n hn θ ε false X ≠ 0} ≤
      ENNReal.ofReal (3 * (n : ℝ) * Real.exp (-(Real.log 2 / 8) * (n : ℝ) ^ ε)) := by
  have : IsProbabilityMeasure (gibbsMeasure p N) := DefinitionSanity.particle_law_probability p N
  have hsub : {X | physicalGapPenalty N n hn θ ε false X ≠ 0} ⊆
      ⋃ i : Fin (n : ℕ), {X | (n : ℝ) ^ ε / 2 ≤ gap X i.val} := by
    intro X hX
    by_contra h
    have hsmall : ∀ i : Fin (n : ℕ), gap X i.val ≤ (n : ℝ) ^ ε / 2 := by
      intro i
      have hi : X ∉ {X : Riesz1.Configuration N | (n : ℝ) ^ ε / 2 ≤ gap X i.val} :=
        fun hi => h (mem_iUnion.mpr ⟨i, hi⟩)
      exact (lt_of_not_ge hi).le
    exact hX (penalty_eq_zero N n hn θ ε X hsmall)
  have hb (i : Fin (n : ℕ)) := ExponentialPower.closed_tail
    (by positivity : 0 < Real.log 2 / 4)
    (SingleGapTails.exponential_moment p N hN i.val).1
    (SingleGapTails.exponential_moment p N hN i.val).2 ((n : ℝ) ^ ε / 2)
  calc
    _ ≤ (gibbsMeasure p N) (⋃ i : Fin (n : ℕ), {X | (n : ℝ) ^ ε / 2 ≤ gap X i.val}) := measure_mono hsub
    _ ≤ ∑ i : Fin (n : ℕ), (gibbsMeasure p N) {X | (n : ℝ) ^ ε / 2 ≤ gap X i.val} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin (n : ℕ), ENNReal.ofReal (3 * Real.exp (-(Real.log 2 / 4) * ((n : ℝ) ^ ε / 2))) :=
      Finset.sum_le_sum (fun i _ => hb i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      rw [show -(Real.log 2 / 4) * ((n : ℝ) ^ ε / 2) =
        -(Real.log 2 / 8) * (n : ℝ) ^ ε by ring]
      ring

/-- See Subsection 5.1 of the paper, normalizer clause. The threshold is
independent of the temperature, volume and cutoff function. -/
theorem normalizer_eventually_half {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ (p : Parameters) (N n : ℕ+) (_hN : 2 ≤ (N : ℕ))
      (hn : (n : ℕ) ≤ (N : ℕ)) (θ : PhysicalCutoff), n₀ ≤ (n : ℕ) →
        (1 / 2 : ℝ≥0∞) ≤ tiltNormalizer p N n hn θ ε false := by
  have hlim : Tendsto (fun x : ℝ => 3 * (x ^ ε) ^ (1 / ε) *
      Real.exp (-(Real.log 2 / 8) * x ^ ε)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, mul_assoc] using ((tendsto_const_nhds (x := (3 : ℝ))).mul
      ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / ε)
        (Real.log 2 / 8) (by positivity)).comp (tendsto_rpow_atTop hε)))
  have hevent : ∀ᶠ k : ℕ in atTop,
      3 * (k : ℝ) * Real.exp (-(Real.log 2 / 8) * (k : ℝ) ^ ε) < 1 / 2 := by
    have hh := ((hlim.comp tendsto_natCast_atTop_atTop).eventually_lt_const
      (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [hh, eventually_ge_atTop (1 : ℕ)] with k hk hk1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    simpa only [Function.comp_def, ← Real.rpow_mul hk0.le, mul_one_div_cancel hε.ne', Real.rpow_one] using hk
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hevent
  refine ⟨n₀, ?_⟩
  intro p N n hN hn θ hn0
  let μ := gibbsMeasure p N
  have : IsProbabilityMeasure μ := DefinitionSanity.particle_law_probability p N
  let S := {X : Riesz1.Configuration N | physicalGapPenalty N n hn θ ε false X = 0}
  have hS : MeasurableSet S := (DefinitionSanity.penalty_measurable N n hn θ ε false) (measurableSet_singleton 0)
  have hbad : μ Sᶜ ≤ (1 / 2 : ℝ≥0∞) := by
    refine (nonzero_penalty_mass_le p N n hN hn θ ε).trans ?_
    exact (ENNReal.ofReal_le_ofReal (hn₀ n hn0).le).trans_eq (by rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]; norm_num)
  have hgood : (1 / 2 : ℝ≥0∞) ≤ μ S := by
    have hh := measure_add_measure_compl hS (μ := μ)
    rw [measure_univ] at hh
    have hh' := ENNReal.toReal_add (measure_ne_top μ S) (measure_ne_top μ Sᶜ)
    rw [hh] at hh'
    have hb := ENNReal.toReal_mono (by norm_num : (1 / 2 : ℝ≥0∞) ≠ ⊤) hbad
    have hg : (1 / 2 : ℝ) ≤ (μ S).toReal := by norm_num at hh' hb ⊢; linarith
    have hhg := ENNReal.ofReal_le_ofReal hg
    rw [ENNReal.ofReal_toReal (measure_ne_top μ S),
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)] at hhg
    simpa using hhg
  refine hgood.trans ?_
  calc
    μ S = ∫⁻ _X in S, (1 : ℝ≥0∞) ∂μ := by simp
    _ = ∫⁻ X in S, ENNReal.ofReal (Real.exp (-p.val.1 * physicalGapPenalty N n hn θ ε false X)) ∂μ := by
      apply setLIntegral_congr_fun hS
      intro X hX
      simp only [S, mem_ofPred_eq] at hX
      simp only [hX, mul_zero, Real.exp_zero, ENNReal.ofReal_one]
    _ ≤ tiltNormalizer p N n hn θ ε false := lintegral_mono' Measure.restrict_le_self le_rfl

/-- Nonempty strict subperiod blocks have their actual length in `(0,N)`. -/
theorem blockLength_mem {N : ℕ+} (X : Riesz1.Configuration N) (j : ℤ)
    {r : ℕ} (hr : 0 < r) (hrN : r < (N : ℕ)) :
    0 < Riesz1.blockLength X j r ∧ Riesz1.blockLength X j r < (N : ℝ) := by
  refine ⟨Riesz1.blockLength_pos X j hr, ?_⟩
  have hh := Riesz1.blockLength_pos X (j + r) (Nat.sub_pos_of_lt hrN)
  rw [← blockLength_complement X j hrN.le] at hh
  linarith

/-- See Subsection 5.1 of the paper: evaluate the physical interval coefficient
on the actual cyclic particle gaps, including the antipodal multiplicity.
The proof arguments describe the interval carrier and exclude collisions. -/
def particleCoefficient (p : Parameters) (N : ℕ+) (j : ℤ) (r : ℕ)
    (hr : 0 < r) (hrN : r ≤ (N : ℕ) / 2) (X : Riesz1.Configuration N) : ℝ :=
  (2 - if 2 * r = (N : ℕ) then (1 : ℝ) else 0) *
    PhysicalEnergy.intervalCoefficient p N
      ⟨Riesz1.blockLength X j r, blockLength_mem X j hr (by omega)⟩

theorem particleCoefficient_pos (p : Parameters) (N : ℕ+) (j : ℤ) (r : ℕ)
    (hr : 0 < r) (hrN : r ≤ (N : ℕ) / 2) (X : Riesz1.Configuration N) :
    0 < particleCoefficient p N j r hr hrN X := by
  unfold particleCoefficient
  apply mul_pos _ (PhysicalEnergy.intervalCoefficient_pos _ _ _)
  split_ifs <;> norm_num

/-- The exact image sum identifies the new evaluation with the existing
physical coefficient, rather than introducing a new kernel. -/
theorem particleCoefficient_images (p : Parameters) (N : ℕ+) (j : ℤ) (r : ℕ)
    (hr : 0 < r) (hrN : r ≤ (N : ℕ) / 2) (X : Riesz1.Configuration N) :
    particleCoefficient p N j r hr hrN X =
      (2 - if 2 * r = (N : ℕ) then (1 : ℝ) else 0) * (p.val.2 * (p.val.2 + 1) *
        ∑' k : ℤ, |Riesz1.blockLength X j r + k * (N : ℝ)| ^ (-p.val.2 - 2)) := by
  unfold particleCoefficient
  rw [PhysicalEnergy.intervalCoefficient_images]

/-- Bridge from the particle evaluation to the cyclic-gap expression in
the ambient Hessian formula. -/
theorem particleCoefficient_gapVector (p : Parameters) (N : ℕ+)
    (i : Fin (N : ℕ)) (r : ℕ) (hr : 0 < r) (hrN : r ≤ (N : ℕ) / 2)
    (X : Riesz1.Configuration N) :
    particleCoefficient p N i.val r hr hrN X =
      (2 - if 2 * r = (N : ℕ) then (1 : ℝ) else 0) *
        PhysicalEnergy.intervalCoefficient p N
          ⟨cyclicGapSum N i r (gapVector X),
            PhysicalEnergy.gapSum_mem N i (by omega) (by omega) (gapVector X)
              ⟨fun a => Riesz1.gap_pos X a.val, DefinitionSanity.actual_gap_sum X⟩⟩ := by
  unfold particleCoefficient
  apply congrArg (fun L => (2 - if 2 * r = (N : ℕ) then (1 : ℝ) else 0) *
    PhysicalEnergy.intervalCoefficient p N L)
  apply Subtype.ext
  exact (GapChart.cyclicGapSum_gapVector X i r).symm

/-- At an antipodal interval the multiplicity is one, also at `N = 2`. -/
theorem particleCoefficient_antipodal (p : Parameters) (N : ℕ+) (j : ℤ) (r : ℕ)
    (hr : 0 < r) (hrN : r ≤ (N : ℕ) / 2) (hanti : 2 * r = (N : ℕ))
    (X : Riesz1.Configuration N) :
    particleCoefficient p N j r hr hrN X = PhysicalEnergy.intervalCoefficient p N
      ⟨Riesz1.blockLength X j r, blockLength_mem X j hr (by omega)⟩ := by
  simp only [particleCoefficient, hanti, ↓reduceIte]
  norm_num

theorem measurable_particleCoefficient (p : Parameters) (N : ℕ+) (j : ℤ) (r : ℕ)
    (hr : 0 < r) (hrN : r ≤ (N : ℕ) / 2) :
    Measurable (particleCoefficient p N j r hr hrN) := by
  simp_rw [funext (particleCoefficient_images p N j r hr hrN)]
  apply Measurable.const_mul
  apply Measurable.const_mul
  apply Measurable.tsum
  intro k
  exact ((Riesz1.measurable_blockLength j r).add_const _).abs.pow_const _

/-- See Subsection 5.1 of the paper, pointwise image bound, retaining both endpoints
of the circle. The complementary block cannot be dropped near a collision. -/
theorem particleCoefficient_upper (p : Parameters) (N : ℕ+) (j : ℤ) (r : ℕ)
    (hr : 0 < r) (hrN : r ≤ (N : ℕ) / 2) (X : Riesz1.Configuration N) :
    particleCoefficient p N j r hr hrN X ≤
      (2 * p.val.2 * (p.val.2 + 1) *
        PeriodicPower.bound (p.val.2 + 2) (by linarith [p.property.2.1])) *
      (Riesz1.blockLength X j r ^ (-p.val.2 - 2) +
        Riesz1.blockLength X (j + r) ((N : ℕ) - r) ^ (-p.val.2 - 2)) := by
  let L := Riesz1.blockLength X j r
  have hL := blockLength_mem X j hr (show r < (N : ℕ) by omega)
  have hδ : 0 < min L ((N : ℝ) - L) := lt_min hL.1 (sub_pos.mpr hL.2)
  have hu := PhysicalEnergy.intervalCoefficient_upper p N ⟨L, hL⟩ hδ
    (min_le_left _ _) (min_le_right _ _)
  have hmin : (min L ((N : ℝ) - L)) ^ (-p.val.2 - 2) ≤
      L ^ (-p.val.2 - 2) + ((N : ℝ) - L) ^ (-p.val.2 - 2) := by
    rcases le_total L ((N : ℝ) - L) with h | h
    · rw [min_eq_left h]
      exact le_add_of_nonneg_right (Real.rpow_nonneg (by linarith [hL.2]) _)
    · rw [min_eq_right h]
      exact le_add_of_nonneg_left (Real.rpow_nonneg hL.1.le _)
  have hmult : (2 - if 2 * r = (N : ℕ) then (1 : ℝ) else 0) ≤ 2 := by
    split_ifs <;> norm_num
  have hcoef : 0 ≤ PhysicalEnergy.intervalCoefficient p N ⟨L, hL⟩ :=
    (PhysicalEnergy.intervalCoefficient_pos _ _ _).le
  have hfactor : 0 ≤ p.val.2 * (p.val.2 + 1) *
      PeriodicPower.bound (p.val.2 + 2) (by linarith [p.property.2.1]) :=
    mul_nonneg (by positivity [p.property.2.1]) (PeriodicPower.bound_pos _ _).le
  have hh := mul_le_mul_of_nonneg_left
    (hu.trans (mul_le_mul_of_nonneg_left hmin hfactor)) (by norm_num : (0 : ℝ) ≤ 2)
  have hh' := (mul_le_mul_of_nonneg_right hmult hcoef).trans hh
  rw [blockLength_complement X j (by omega : r ≤ (N : ℕ))] at hh'
  convert hh' using 1 <;> dsimp [particleCoefficient, L]
  ring

/-- See Subsection 5.1 of the paper, the interval-coefficient moment estimate under
the original particle Gibbs law. The same constant covers every real
`q ≥ 1`, volume, interval, and temperature in the prescribed compact set. -/
theorem particleCoefficient_moments (s βlo βhi : ℝ) (hs : 0 < s)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Parameters), p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (N : ℕ+), 2 ≤ (N : ℕ) →
      ∀ (j : ℤ) (r : ℕ) (hr : 0 < r) (hrN : r ≤ (N : ℕ) / 2),
      ∀ q : ℝ, 1 ≤ q →
        eLpNorm (particleCoefficient p N j r hr hrN) (ENNReal.ofReal q)
          (gibbsMeasure p N) ≤ ENNReal.ofReal
            (C * q ^ ((s + 2) / s) * (r : ℝ) ^ (-s - 2)) := by
  obtain ⟨D, hD, hblock⟩ := inverse_block_moments s βlo βhi (s + 2) hs hlo hle (by linarith)
  let B := 2 * s * (s + 1) * PeriodicPower.bound (s + 2) (by linarith)
  have hB : 0 < B := by
    dsimp [B]
    exact mul_pos (by positivity) (PeriodicPower.bound_pos _ _)
  refine ⟨2 * B * D, by positivity, ?_⟩
  intro p hps hpl hph N hN j r hr hrN q hq
  let μ := gibbsMeasure p N
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hqE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hq
  have hdom := eLpNorm_mono_real (measurable_particleCoefficient p N j r hr hrN).aestronglyMeasurable
    (μ := μ) (p := ENNReal.ofReal q)
    (g := fun X => B * (Riesz1.blockLength X j r ^ (-s - 2) +
      Riesz1.blockLength X (j + r) ((N : ℕ) - r) ^ (-s - 2))) (fun X => by
      rw [Real.norm_of_nonneg (particleCoefficient_pos p N j r hr hrN X).le]
      simpa only [hps] using particleCoefficient_upper p N j r hr hrN X)
  have he : -(s + 2) = -s - 2 := by ring
  have hfirst := hblock p hps hpl hph N hN j r hr q hq
  have hsecond := hblock p hps hpl hph N hN (j + r) ((N : ℕ) - r)
    (by omega) q hq
  rw [he] at hfirst hsecond
  have hcomp : (((N : ℕ) - r : ℕ) : ℝ) ^ (-s - 2) ≤ (r : ℝ) ^ (-s - 2) := by
    apply Real.rpow_le_rpow_of_nonpos hr0 _ (by linarith)
    exact_mod_cast (show r ≤ (N : ℕ) - r by omega)
  have hsecond' := hsecond.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left hcomp (by positivity : 0 ≤ D * q ^ ((s + 2) / s))))
  have hadd := (eLpNorm_add_le hqE).trans (add_le_add hfirst hsecond')
  have hscale : eLpNorm (fun X : Riesz1.Configuration N => B *
      (Riesz1.blockLength X j r ^ (-s - 2) +
        Riesz1.blockLength X (j + r) ((N : ℕ) - r) ^ (-s - 2))) (ENNReal.ofReal q) μ =
      ENNReal.ofReal B * eLpNorm
        (fun X => Riesz1.blockLength X j r ^ (-s - 2) +
          Riesz1.blockLength X (j + r) ((N : ℕ) - r) ^ (-s - 2)) (ENNReal.ofReal q) μ := by
    change eLpNorm (B • _) _ μ = _
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_pos hB]
  rw [hscale] at hdom
  refine hdom.trans ((mul_le_mul_right hadd _).trans_eq ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_mul hB.le]
  congr 1
  ring

/-- The curvature bound controls the cutoff on its whole used carrier. -/
theorem cutoff_quadratic (θ : PhysicalCutoff) {C : ℝ} (hC : 1 ≤ C)
    (hcurv : ∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧
      deriv (deriv θ.val) x ≤ C) :
    ∀ x : ℝ, 0 ≤ x → θ.val x ≤ C * x ^ 2 := by
  have hsm (x : ℝ) (hx : 0 < x) : ContDiffAt ℝ (⊤ : ℕ∞) θ.val x :=
    θ.property.1.contDiffAt (Ici_mem_nhds hx)
  have hd (x : ℝ) (hx : 0 < x) : DifferentiableAt ℝ θ.val x :=
    (hsm x hx).differentiableAt (by simp)
  have hdd (x : ℝ) (hx : 0 < x) : DifferentiableAt ℝ (deriv θ.val) x :=
    ((hsm x hx).derivWithin (m := 1) (by simp)).differentiableAt (by norm_num)
  have ha : θ.val (1 / 4) = 0 := θ.property.2.2.2.1 _ ⟨by norm_num, by norm_num⟩
  have hda : deriv θ.val (1 / 4) = 0 := by
    have he : θ.val =ᶠ[𝓝 (1 / 4 : ℝ)] fun _ => 0 := by
      filter_upwards [Ioo_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)
        (by norm_num : (1 / 4 : ℝ) < 1 / 2)] with x hx
      exact θ.property.2.2.2.1 _ ⟨hx.1.le, hx.2.le⟩
    rw [he.deriv_eq]
    exact deriv_const _ _
  intro x hx
  by_cases hxa : x ≤ 1 / 4
  · rw [θ.property.2.2.2.1 _ ⟨hx, by linarith⟩]
    positivity
  have hax : (1 / 4 : ℝ) ≤ x := (lt_of_not_ge hxa).le
  have hderiv (t : ℝ) (ht : t ∈ Icc (1 / 4 : ℝ) x) : |deriv θ.val t| ≤ C * x := by
    have hh := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := deriv θ.val) (a := 1 / 4) (b := x)
      (fun z hz => (hdd z (by linarith [hz.1])).hasDerivAt.hasDerivWithinAt)
      (fun z hz => by
        rw [Real.norm_of_nonneg (hcurv z (by linarith [hz.1])).1]
        exact (hcurv z (by linarith [hz.1])).2) t ht
    rw [hda, sub_zero, Real.norm_eq_abs] at hh
    exact hh.trans (by nlinarith [mul_nonneg (show 0 ≤ C by linarith) (sub_nonneg.mpr ht.2)])
  have hh := norm_image_sub_le_of_norm_deriv_le_segment' (f := θ.val)
    (a := 1 / 4) (b := x)
    (fun z hz => (hd z (by linarith [hz.1])).hasDerivAt.hasDerivWithinAt)
    (fun z hz => hderiv z ⟨hz.1, hz.2.le⟩) x ⟨hax, le_rfl⟩
  rw [ha, sub_zero, Real.norm_eq_abs] at hh
  have hn := θ.property.2.2.1 x hx
  rw [abs_of_nonneg hn] at hh
  nlinarith

private theorem square_gap_integral_le (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (j : ℤ) :
    Integrable (fun X : Riesz1.Configuration N => gap X j ^ 2) (gibbsMeasure p N) ∧
      (∫ X, gap X j ^ 2 ∂gibbsMeasure p N) ≤
        3 * (2 / Real.exp 1) ^ (2 : ℝ) / (Real.log 2 / 4) ^ (2 : ℝ) := by
  have hm := SingleGapTails.exponential_moment p N hN j
  have hh := Riesz1.moment_le_of_exp_moment_le (by positivity : 0 < Real.log 2 / 4)
    (fun X : Riesz1.Configuration N => gap X j) (Riesz1.measurable_gap j)
    (fun X => (Riesz1.gap_pos X j).le) hm.1 hm.2 2 (by norm_num)
  simpa only [Real.rpow_two] using hh

/-- The forcing has a volume-uniform first-moment bound linear in the
active size. This supplies penalty integrability. -/
theorem penalty_integral_le (p : Parameters) (N n : ℕ+) (hN : 2 ≤ (N : ℕ))
    (hn : (n : ℕ) ≤ (N : ℕ)) (θ : PhysicalCutoff) {ε C : ℝ} (hε : 0 ≤ ε)
    (hC : 1 ≤ C) (hcurv : ∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧
      deriv (deriv θ.val) x ≤ C) :
    Integrable (physicalGapPenalty N n hn θ ε false) (gibbsMeasure p N) ∧
      (∫ X, physicalGapPenalty N n hn θ ε false X ∂gibbsMeasure p N) ≤
        C * (n : ℝ) * (3 * (2 / Real.exp 1) ^ (2 : ℝ) /
          (Real.log 2 / 4) ^ (2 : ℝ)) := by
  let μ := gibbsMeasure p N
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hscale : (n : ℝ) ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  have hsum : Integrable (fun X : Riesz1.Configuration N =>
      C * ∑ i : Fin (n : ℕ), gap X i.val ^ 2) μ :=
    (integrable_finsetSum _ (fun i _ => (square_gap_integral_le p N hN i.val).1)).const_mul C
  have hdom (X : Riesz1.Configuration N) : physicalGapPenalty N n hn θ ε false X ≤
      C * ∑ i : Fin (n : ℕ), gap X i.val ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    change θ.val ((n : ℝ) ^ (-ε) * gap X i.val) + 0 ≤ _
    rw [add_zero]
    have hy : 0 ≤ (n : ℝ) ^ (-ε) * gap X i.val :=
      mul_nonneg (Real.rpow_nonneg (by positivity) _) (Riesz1.gap_pos X i.val).le
    refine (cutoff_quadratic θ hC hcurv _ hy).trans ?_
    gcongr
    exact (mul_le_mul_of_nonneg_right hscale (Riesz1.gap_pos X i.val).le).trans_eq (one_mul _)
  have hi : Integrable (physicalGapPenalty N n hn θ ε false) μ :=
    hsum.mono' (DefinitionSanity.penalty_measurable N n hn θ ε false).aestronglyMeasurable
      (ae_of_all μ (fun X => by
        rw [Real.norm_of_nonneg (DefinitionSanity.penalty_nonneg N n hn θ ε false X)]
        exact hdom X))
  refine ⟨hi, (integral_mono hi hsum hdom).trans ?_⟩
  rw [integral_const_mul, integral_finsetSum _
    (fun i _ => (square_gap_integral_le p N hN i.val).1)]
  have hh := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin (n : ℕ)) _ =>
      (square_gap_integral_le p N hN i.val).2)) (by linarith : 0 ≤ C)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_assoc] using hh

private theorem normalizer_ge_jensen (p : Parameters) (N n : ℕ+)
    (hn : (n : ℕ) ≤ (N : ℕ)) (θ : PhysicalCutoff) (ε : ℝ)
    (hi : Integrable (physicalGapPenalty N n hn θ ε false) (gibbsMeasure p N)) :
    ENNReal.ofReal (Real.exp (-p.val.1 *
      ∫ X, physicalGapPenalty N n hn θ ε false X ∂gibbsMeasure p N)) ≤
        tiltNormalizer p N n hn θ ε false := by
  let μ := gibbsMeasure p N
  have : IsProbabilityMeasure μ := DefinitionSanity.particle_law_probability p N
  have hm := (DefinitionSanity.penalty_measurable N n hn θ ε false).const_mul (-p.val.1)
  have hnexp (X : Riesz1.Configuration N) :
      Real.exp (-p.val.1 * physicalGapPenalty N n hn θ ε false X) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith [p.property.1])
      (DefinitionSanity.penalty_nonneg N n hn θ ε false X))
  have hexp : Integrable (fun X => Real.exp
      (-p.val.1 * physicalGapPenalty N n hn θ ε false X)) μ :=
    (integrable_const (1 : ℝ)).mono' (Real.measurable_exp.comp hm).aestronglyMeasurable
      (ae_of_all μ fun X => by rw [Real.norm_of_nonneg (Real.exp_pos _).le]; exact hnexp X)
  have hh := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn
    isClosed_univ (ae_of_all μ (fun _ => mem_univ _)) (hi.const_mul (-p.val.1)) hexp
  rw [integral_const_mul] at hh
  exact (ENNReal.ofReal_le_ofReal hh).trans_eq
    (ofReal_integral_eq_lintegral_ofReal hexp (ae_of_all μ fun _ => (Real.exp_pos _).le))

/-- The proof of Lemma 5.1 of the paper: the zero region
and quadratic growth of the cutoff, together with the one-gap exponential
moment, bound the expectation of the entire penalty uniformly in both sizes. -/
theorem penalty_integral_uniform {ε C : ℝ} (hε : 0 < ε) (hC : 1 ≤ C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (p : Parameters) (N n : ℕ+), 2 ≤ (N : ℕ) →
      ∀ (hn : (n : ℕ) ≤ (N : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ C) →
      Integrable (physicalGapPenalty N n hn θ ε false) (gibbsMeasure p N) ∧
        (∫ X, physicalGapPenalty N n hn θ ε false X ∂gibbsMeasure p N) ≤ B := by
  let c := Real.log 2 / 4
  let A := (2 / Real.exp 1) ^ (2 : ℝ) / (c / 2) ^ (2 : ℝ)
  have hc : 0 < c := by dsimp [c]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨D, hD, hpoly⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := 1) (c := c / 4) (c' := 0) hε (by positivity)
  refine ⟨3 * C * A * D, by positivity, ?_⟩
  intro p N n hN hn θ hcurv
  let μ := gibbsMeasure p N
  let R := (n : ℝ) ^ ε
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by positivity
  have hscale : (n : ℝ) ^ (-ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  have hcancel : (n : ℝ) ^ (-ε) * R = 1 := by
    dsimp [R]; rw [← Real.rpow_add hn0]; simp
  have hpoint (X : Riesz1.Configuration N) (i : Fin (n : ℕ)) :
      θ.val ((n : ℝ) ^ (-ε) * gap X i.val) ≤
        C * A * Real.exp (-c * R / 4) * Real.exp (c * gap X i.val) := by
    have hg := (Riesz1.gap_pos X i.val).le
    have hy : 0 ≤ (n : ℝ) ^ (-ε) * gap X i.val :=
      mul_nonneg (Real.rpow_nonneg hn0.le _) hg
    by_cases hsmall : gap X i.val ≤ R / 2
    · rw [θ.property.2.2.2.1 _ ⟨hy, by
        have h := mul_le_mul_of_nonneg_left hsmall
          (Real.rpow_nonneg hn0.le (-ε))
        rw [← mul_div_assoc, hcancel] at h
        exact h⟩]
      positivity
    have hq := cutoff_quadratic θ hC hcurv _ hy
    have hsquare : gap X i.val ^ 2 ≤ A * Real.exp (c * gap X i.val / 2) := by
      have hh := Riesz1.rpow_le_div_exp_mul_exp (p := 2) (by norm_num)
        (mul_nonneg (show 0 ≤ c / 2 by positivity) hg)
      rw [Real.mul_rpow (by positivity) hg] at hh
      simp only [Real.rpow_two] at hh
      change Riesz1.gap X i.val ^ 2 ≤ A * Real.exp (c * Riesz1.gap X i.val / 2)
      dsimp [A]
      simp only [Real.rpow_two]
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : 0 < (c / 2) ^ 2)]
      rw [show c / 2 * Riesz1.gap X i.val = c * Riesz1.gap X i.val / 2 by ring] at hh
      nlinarith only [hh]
    have hexp : Real.exp (c * gap X i.val / 2) ≤
        Real.exp (-c * R / 4) * Real.exp (c * gap X i.val) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [lt_of_not_ge hsmall]
    calc
      _ ≤ C * gap X i.val ^ 2 := hq.trans (by
        gcongr
        exact (mul_le_mul_of_nonneg_right hscale hg).trans_eq (one_mul _))
      _ ≤ C * (A * Real.exp (c * gap X i.val / 2)) :=
        mul_le_mul_of_nonneg_left hsquare (by linarith)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hexp (mul_nonneg (by linarith : 0 ≤ C) hA)]
  have hi := (penalty_integral_le p N n hN hn θ hε.le hC hcurv).1
  refine ⟨hi, ?_⟩
  have hdom : (∫ X, physicalGapPenalty N n hn θ ε false X ∂μ) ≤
      ∫ X, ∑ i : Fin (n : ℕ),
        C * A * Real.exp (-c * R / 4) * Real.exp (c * gap X i.val) ∂μ := by
    apply integral_mono hi
      (integrable_finsetSum _ fun i _ =>
        (SingleGapTails.exponential_moment p N hN i.val).1.const_mul _)
    intro X
    apply Finset.sum_le_sum
    intro i _
    simpa only [Bool.false_eq_true, ↓reduceIte, add_zero] using hpoint X i
  apply hdom.trans
  rw [integral_finsetSum _ (fun i _ =>
    (SingleGapTails.exponential_moment p N hN i.val).1.const_mul _)]
  simp_rw [integral_const_mul]
  calc
    _ ≤ ∑ _i : Fin (n : ℕ), C * A * Real.exp (-c * R / 4) * 3 :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
        (SingleGapTails.exponential_moment p N hN i.val).2 (by positivity)
    _ = (3 * C * A) * ((n : ℝ) ^ (1 : ℝ) * Real.exp (-(c / 4) * (n : ℝ) ^ ε)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Real.rpow_one]
      rw [show -c * R / 4 = -(c / 4) * (n : ℝ) ^ ε by dsimp [R]; ring]
      ring
    _ ≤ (3 * C * A) * D := by
      have h := hpoly (n : ℝ) hn1
      simp only [neg_zero, zero_mul, Real.exp_zero, mul_one] at h
      exact mul_le_mul_of_nonneg_left h (by positivity)

/-- See Subsection 5.1 of the paper, the normalizer has a positive lower
bound at every size, uniformly over compact temperature intervals and
all cutoffs with the prescribed curvature bound. This is the direct Jensen
normalization step of Lemma 5.1 of the paper. -/
theorem normalizer_uniform_lower {ε C βhi : ℝ} (hε : 0 < ε) (hC : 1 ≤ C)
    (hβhi : 0 < βhi) :
    ∃ z : ℝ, 0 < z ∧ z ≤ 1 / 2 ∧
      ∀ (p : Parameters), p.val.1 ≤ βhi → ∀ (N n : ℕ+), 2 ≤ (N : ℕ) →
      ∀ (hn : (n : ℕ) ≤ (N : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ C) →
        ENNReal.ofReal z ≤ tiltNormalizer p N n hn θ ε false := by
  obtain ⟨B, hB, hbound⟩ := penalty_integral_uniform hε hC
  let z := min (1 / 2) (Real.exp (-βhi * B))
  refine ⟨z, lt_min (by norm_num) (Real.exp_pos _), min_le_left _ _, ?_⟩
  intro p hp N n hN hn θ hcurv
  obtain ⟨hi, hb⟩ := hbound p N n hN hn θ hcurv
  have hnn : 0 ≤ ∫ X, physicalGapPenalty N n hn θ ε false X ∂gibbsMeasure p N :=
    integral_nonneg (DefinitionSanity.penalty_nonneg N n hn θ ε false)
  refine (ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans
    ((ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)).trans
      (normalizer_ge_jensen p N n hn θ ε hi))
  have hh := mul_le_mul hp hb hnn hβhi.le
  linarith

/-- The actual tilted law is dominated by the inverse normalizer
times the actual Gibbs law. -/
theorem tilted_measure_le (p : Parameters) (N n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ))
    (θ : PhysicalCutoff) (ε : ℝ) :
    tiltedParticleMeasure p N n hn θ ε false ≤
      (tiltNormalizer p N n hn θ ε false)⁻¹ • gibbsMeasure p N := by
  unfold tiltedParticleMeasure
  have hh : (gibbsMeasure p N).withDensity (fun X =>
      ENNReal.ofReal (Real.exp (-p.val.1 * physicalGapPenalty N n hn θ ε false X))) ≤
      gibbsMeasure p N := by
    refine (withDensity_mono (ae_of_all _ (fun X => ?_))).trans_eq withDensity_one
    exact ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (by linarith [p.property.1])
        (DefinitionSanity.penalty_nonneg N n hn θ ε false X)))
  gcongr

private theorem tilted_norm_le {p : Parameters} {N n : ℕ+} {hn : (n : ℕ) ≤ (N : ℕ)}
    {θ : PhysicalCutoff} {ε z : ℝ} (hz : 0 < z) (hz1 : z ≤ 1)
    (hZ : ENNReal.ofReal z ≤ tiltNormalizer p N n hn θ ε false)
    (f : Riesz1.Configuration N → ℝ) {q : ℝ} (hq : 1 ≤ q) :
    eLpNorm f (ENNReal.ofReal q) (tiltedParticleMeasure p N n hn θ ε false) ≤
      ENNReal.ofReal z⁻¹ * eLpNorm f (ENNReal.ofReal q) (gibbsMeasure p N) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hmeasure : tiltedParticleMeasure p N n hn θ ε false ≤
      ENNReal.ofReal z⁻¹ • gibbsMeasure p N := by
    refine (tilted_measure_le p N n hn θ ε).trans ?_
    have hinv := ENNReal.inv_le_inv.mpr hZ
    rw [← ENNReal.ofReal_inv_of_pos hz] at hinv
    gcongr
  have hnorm := (eLpNorm_mono_measure f hmeasure).trans
    (eLpNorm_smul_measure_le (ENNReal.ofReal z⁻¹) f (ENNReal.ofReal q) (gibbsMeasure p N))
  simp only [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal hq0.le, smul_eq_mul] at hnorm
  refine hnorm.trans (mul_le_mul_left ?_ _)
  rw [ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr hz.le) (inv_nonneg.mpr hq0.le)]
  apply ENNReal.ofReal_le_ofReal
  calc
    z⁻¹ ^ q⁻¹ ≤ z⁻¹ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le
      ((one_le_inv₀ hz).mpr hz1) ((inv_le_one₀ hq0).mpr hq)
    _ = z⁻¹ := Real.rpow_one _

/-- See Subsection 5.1 of the paper, complete `a_J` moment clause under the upper-gap tilted law, uniformly in all sizes and real norm exponents.
The moment degree is independent of temperature. Constants are uniform
over compact temperature intervals and cutoffs of bounded curvature. -/
theorem tilted_coefficient_moments (s βlo βhi ε Cθ : ℝ) (hs : 0 < s)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (hε : 0 < ε) (hCθ : 1 ≤ Cθ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Parameters), p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (N n : ℕ+), 2 ≤ (N : ℕ) →
      ∀ (hn : (n : ℕ) ≤ (N : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ (j : ℤ) (r : ℕ) (hr : 0 < r) (hrN : r ≤ (N : ℕ) / 2),
      ∀ q : ℝ, 1 ≤ q →
        eLpNorm (particleCoefficient p N j r hr hrN) (ENNReal.ofReal q)
          (tiltedParticleMeasure p N n hn θ ε false) ≤ ENNReal.ofReal
            (C * q ^ ((s + 2) / s) * (r : ℝ) ^ (-s - 2)) := by
  obtain ⟨D, hD, hcoeff⟩ := particleCoefficient_moments s βlo βhi hs hlo hle
  obtain ⟨z, hz, hzhalf, hnorm⟩ := normalizer_uniform_lower hε hCθ (by linarith : 0 < βhi)
  refine ⟨z⁻¹ * D, by positivity, ?_⟩
  intro p hps hpl hph N n hN hn θ hcurv j r hr hrN q hq
  have hZ := hnorm p hph N n hN hn θ hcurv
  have hdom := tilted_norm_le hz (by linarith) hZ
    (particleCoefficient p N j r hr hrN) hq
  refine hdom.trans ((mul_le_mul_right (hcoeff p hps hpl hph N hN j r hr hrN q hq) _).trans_eq ?_)
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hz.le)]
  congr 1
  ring

private theorem blockLength_mono {N : ℕ+} (X : Riesz1.Configuration N) (j : ℤ)
    {k h : ℕ} (hkh : k ≤ h) : Riesz1.blockLength X j k ≤ Riesz1.blockLength X j h := by
  unfold Riesz1.blockLength
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ N)
  apply sub_le_sub_right
  exact (Riesz1.cyclicLift_strictMono X).monotone
    (by omega)

private theorem internal_block_tail {N n : ℕ+} {μ : Measure (Riesz1.Configuration N)}
    {s η b C c : ℝ} (hs : 0 < s) (hb : 0 < b) (hbη : b ≤ η)
    (hsmall : s / 2 + b ≤ 1) (hC : 0 ≤ C) (hc : 0 < c)
    (hRig : ∀ (j : ℤ) (r : ℕ), 1 ≤ r → r ≤ (N : ℕ) / 2 →
      μ {X | (r : ℝ) ^ (s / 2 + b) ≤ |Riesz1.blockLength X j r - r|} ≤
        ENNReal.ofReal (C * Real.exp (-c * (r : ℝ) ^ (b / (4 * (s + 2))))))
    {h k : ℕ} (hh : 1 ≤ h) (hhN : h ≤ (N : ℕ) / 2)
    (hpower : (n : ℝ) ^ (η / 2) ≤ h) (hupper : 2 * (h : ℝ) ≤ (n : ℝ) ^ η)
    (hk : 1 ≤ k) (hkn : k ≤ (n : ℕ)) (hkN : k ≤ (N : ℕ) / 2) (j : ℤ) :
    μ {X | (n : ℝ) ^ η * (k : ℝ) ^ (s / 2) < |Riesz1.blockLength X j k - k|} ≤
      ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ (η * b / (8 * (s + 2))))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hcompare (r : ℕ) (hr : (n : ℝ) ^ (η / 2) ≤ r) :
      ENNReal.ofReal (C * Real.exp (-c * (r : ℝ) ^ (b / (4 * (s + 2))))) ≤
        ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ (η * b / (8 * (s + 2))))) := by
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hC
    apply Real.exp_le_exp.mpr
    have hp := Real.rpow_le_rpow (Real.rpow_nonneg hn0.le _) hr
      (by positivity : 0 ≤ b / (4 * (s + 2)))
    rw [← Real.rpow_mul hn0.le] at hp
    have he : η / 2 * (b / (4 * (s + 2))) = η * b / (8 * (s + 2)) := by field_simp; ring
    rw [he] at hp
    nlinarith
  by_cases hkh : h ≤ k
  · refine (measure_mono (fun X hX => ?_)).trans
      ((hRig j k hk hkN).trans (hcompare k (hpower.trans (by exact_mod_cast hkh))))
    have hkb : (k : ℝ) ^ b ≤ (n : ℝ) ^ η :=
      (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hkn) hb.le).trans
        (Real.rpow_le_rpow_of_exponent_le hn1 hbη)
    have hth : (k : ℝ) ^ (s / 2 + b) ≤ (n : ℝ) ^ η * (k : ℝ) ^ (s / 2) := by
      rw [Real.rpow_add (by positivity : (0 : ℝ) < k)]
      nlinarith [mul_le_mul_of_nonneg_right hkb (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ k) (s / 2))]
    exact hth.trans hX.le
  · refine (measure_mono (fun X hX => ?_)).trans
      ((hRig j h hh hhN).trans (hcompare h hpower))
    have hkh' : k ≤ h := by omega
    have hkT : (k : ℝ) ≤ (n : ℝ) ^ η * (k : ℝ) ^ (s / 2) := by
      have hpow1 : 1 ≤ (k : ℝ) ^ (s / 2) := Real.one_le_rpow hk1 (by positivity)
      have hkr : (k : ℝ) ≤ h := by exact_mod_cast hkh'
      nlinarith [mul_le_mul_of_nonneg_left hpow1 (Real.rpow_nonneg hn0.le η)]
    have hdev : (n : ℝ) ^ η * (k : ℝ) ^ (s / 2) < Riesz1.blockLength X j k - k := by
      by_contra h
      have hle : |Riesz1.blockLength X j k - k| ≤ (n : ℝ) ^ η * (k : ℝ) ^ (s / 2) :=
        abs_le.mpr ⟨by linarith [Riesz1.blockLength_pos X j (by omega : 0 < k)], le_of_not_gt h⟩
      exact (not_lt_of_ge hle) hX
    have hmono := blockLength_mono X j hkh'
    have hp : (h : ℝ) ^ (s / 2 + b) ≤ h :=
      (Real.rpow_le_rpow_of_exponent_le hh1 hsmall).trans_eq (Real.rpow_one _)
    have hkpow : 1 ≤ (k : ℝ) ^ (s / 2) := Real.one_le_rpow hk1 (by positivity)
    have hmul := mul_le_mul_of_nonneg_left hkpow (Real.rpow_nonneg hn0.le η)
    have hfinal : (h : ℝ) ^ (s / 2 + b) ≤ Riesz1.blockLength X j h - h := by nlinarith
    exact hfinal.trans (le_abs_self _)

private theorem internal_interval_scale {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 4) :
    ∃ n₀ : ℕ, ∀ n : ℕ+, n₀ ≤ (n : ℕ) →
      ∃ h : ℕ, 1 ≤ h ∧ 2 * h ≤ (n : ℕ) ∧
        (n : ℝ) ^ (η / 2) ≤ h ∧ 2 * (h : ℝ) ≤ (n : ℝ) ^ η := by
  have ha : 0 < η / 2 := by positivity
  have hb : 0 < 1 - η / 2 := by linarith
  have he : ∀ᶠ k : ℕ in atTop,
      4 ≤ (k : ℝ) ^ (η / 2) ∧ 4 ≤ (k : ℝ) ^ (1 - η / 2) :=
    (((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (4 : ℝ))).and
      (((tendsto_rpow_atTop hb).comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop (4 : ℝ)))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp he
  refine ⟨n₀, ?_⟩
  intro n hn
  have hh := hn₀ n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  let h := ⌈(n : ℝ) ^ (η / 2)⌉₊
  have hceil : (n : ℝ) ^ (η / 2) ≤ h := Nat.le_ceil _
  have hceil' : (h : ℝ) ≤ 2 * (n : ℝ) ^ (η / 2) := by
    have hc := Nat.ceil_lt_add_one (Real.rpow_nonneg hn0.le (η / 2))
    dsimp [h]
    linarith [hh.1]
  have hnident : (n : ℝ) ^ (η / 2) * (n : ℝ) ^ (1 - η / 2) = n := by
    rw [← Real.rpow_add hn0]
    norm_num
  have hηident : (n : ℝ) ^ (η / 2) * (n : ℝ) ^ (η / 2) = (n : ℝ) ^ η := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  have h2h : 2 * (h : ℝ) ≤ (n : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hh.2 (Real.rpow_nonneg hn0.le (η / 2))]
  refine ⟨h, ?_, by exact_mod_cast h2h, hceil, ?_⟩
  · have hp : (0 : ℝ) < h := lt_of_lt_of_le (Real.rpow_pos_of_pos hn0 _) hceil
    exact_mod_cast (show (1 : ℝ) ≤ h by
      exact_mod_cast (show 1 ≤ h from Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hp.ne')))
  · nlinarith [mul_le_mul_of_nonneg_left hh.1 (Real.rpow_nonneg hn0.le (η / 2))]

/-- See Subsection 5.1 of the paper, individual block estimate under the
unmodified law. It holds for every starting label, including blocks that
cross the active window. The threshold is uniform in temperature. -/
theorem block_tails (hRig : External.LongRangeRigidityLocallyUniform)
    (s : Riesz1.RieszExponent) {ε : ℝ} (hε : 0 < ε)
    (βlo βhi : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ n₀ : ℕ,
      ∀ (β : InverseTemperature), β.val ∈ Icc βlo βhi →
      ∀ (N n : ℕ+), 2 ≤ (N : ℕ) → (n : ℕ) ≤ (N : ℕ) → n₀ ≤ (n : ℕ) →
      ∀ (j : ℤ) (k : ℕ), 1 ≤ k → k ≤ (n : ℕ) → k ≤ (N : ℕ) / 2 →
        (gibbsMeasure (ofLong β s) N)
          {X | (n : ℝ) ^ ε * (k : ℝ) ^ (s.val / 2) < |Riesz1.blockLength X j k - k|} ≤
          ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ (blockTailPower s.val ε))) := by
  let η := min ε (1 / 4)
  let b := min (η / 8) ((1 - s.val / 2) / 4)
  have hη : 0 < η := lt_min hε (by norm_num)
  have hη1 : η ≤ 1 / 4 := min_le_right _ _
  have hb : 0 < b := lt_min (by dsimp [η]; positivity) (by linarith [s.property.2])
  have hbη : b ≤ η := (min_le_left _ _).trans (by linarith)
  have hbs : b < (1 - s.val / 2) / 2 := by
    have hh := min_le_right (η / 8) ((1 - s.val / 2) / 4)
    dsimp [b]
    linarith [s.property.2]
  obtain ⟨C, c, hC, hc, htail⟩ := hRig s b hb hbs βlo βhi hlo hle
  obtain ⟨n₀, hscale⟩ := internal_interval_scale hη hη1
  refine ⟨C, c, hC, hc, n₀, ?_⟩
  intro β hβ N n hN hn hn0 j k hk hkn hkN
  obtain ⟨h, hh, hhsize, hpow, hupper⟩ := hscale n hn0
  have hhN : h ≤ (N : ℕ) / 2 := by omega
  have hR : ∀ (j : ℤ) (r : ℕ), 1 ≤ r → r ≤ (N : ℕ) / 2 →
      (gibbsMeasure (ofLong β s) N)
        {X | (r : ℝ) ^ (s.val / 2 + b) ≤ |Riesz1.blockLength X j r - r|} ≤
        ENNReal.ofReal (C * Real.exp (-c * (r : ℝ) ^ (b / (4 * (s.val + 2))))) := by
    intro a r hr hrN
    exact htail β hβ N hN a r hr hrN
  have hsmall : s.val / 2 + b ≤ 1 := by
    have hh := min_le_right (η / 8) ((1 - s.val / 2) / 4)
    dsimp [b]
    linarith [s.property.2]
  have hbnd := internal_block_tail s.property.1 hb hbη hsmall hC.le hc hR
    hh hhN hpow hupper hk hkn hkN j
  refine (measure_mono (fun X hX => ?_)).trans (hbnd.trans ?_)
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hn1 (min_le_left ε (1 / 4)))
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ k) _)) hX
  · apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.exp_le_exp.mpr
    have hδ : blockTailPower s.val ε ≤ η * b / (8 * (s.val + 2)) := by
      have hh := min_le_right (s.val * η / 2) (η * b / (16 * (s.val + 2)))
      change min (s.val * η / 2) (η * b / (16 * (s.val + 2))) ≤ _
      exact hh.trans (div_le_div_of_nonneg_left (by positivity) (by linarith [s.property.1])
        (by linarith [s.property.1]))
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
    have hp := Real.rpow_le_rpow_of_exponent_le hn1 hδ
    nlinarith

private theorem internal_small_size_bound {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (n : ℕ+) (n₀ : ℕ) (hn : (n : ℕ) ≤ n₀) :
    1 ≤ Real.exp (c * (n₀ : ℝ) ^ δ) * Real.exp (-c * (n : ℝ) ^ δ) := by
  rw [← Real.exp_add, ← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  have hh := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ n)
    (by exact_mod_cast hn : (n : ℝ) ≤ n₀) hδ.le
  nlinarith

/-- See Subsection 5.1 of the paper, block deviations at every active size,
including the finitely many sizes preceding the rigidity threshold. -/
theorem block_tails_all_sizes (hRig : External.LongRangeRigidityLocallyUniform)
    (s : Riesz1.RieszExponent) {ε : ℝ} (hε : 0 < ε)
    (βlo βhi : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (β : InverseTemperature), β.val ∈ Icc βlo βhi →
      ∀ (N n : ℕ+), 2 ≤ (N : ℕ) → (n : ℕ) ≤ (N : ℕ) →
      ∀ (j : ℤ) (k : ℕ), 1 ≤ k → k ≤ (n : ℕ) → k ≤ (N : ℕ) / 2 →
        (gibbsMeasure (ofLong β s) N)
          {X | (n : ℝ) ^ ε * (k : ℝ) ^ (s.val / 2) < |Riesz1.blockLength X j k - k|} ≤
          ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ (blockTailPower s.val ε))) := by
  obtain ⟨C, c, hC, hc, n₀, htail⟩ := block_tails hRig s hε βlo βhi hlo hle
  let D := C + Real.exp (c * (n₀ : ℝ) ^ (blockTailPower s.val ε))
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, c, hD, hc, ?_⟩
  intro β hβ N n hN hn j k hk hkn hkN
  have : IsProbabilityMeasure (gibbsMeasure (ofLong β s) N) :=
    DefinitionSanity.particle_law_probability _ _
  by_cases hsize : n₀ ≤ (n : ℕ)
  · exact (htail β hβ N n hN hn hsize j k hk hkn hkN).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (by dsimp [D]; linarith [Real.exp_pos (c * (n₀ : ℝ) ^ blockTailPower s.val ε)]) (Real.exp_pos _).le))
  · refine prob_le_one.trans ?_
    have hh := internal_small_size_bound hc (blockTailPower_pos s.property.1 s.property.2 hε)
      n n₀ (by omega)
    have hd : Real.exp (c * (n₀ : ℝ) ^ blockTailPower s.val ε) ≤ D := by
      dsimp [D]
      linarith
    exact (show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp).trans_le
      (ENNReal.ofReal_le_ofReal (hh.trans (mul_le_mul_of_nonneg_right hd (Real.exp_pos _).le)))

/-- See Subsection 5.1 of the paper, the single-gap cutoffs on the specified
block-tail scale, with constants uniform over compact temperatures. -/
theorem cutoff_tails (s : Riesz1.RieszExponent) {ε : ℝ} (hε : 0 < ε)
    (βlo βhi : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (β : InverseTemperature), β.val ∈ Icc βlo βhi →
      ∀ (N n : ℕ+), 2 ≤ (N : ℕ) → ∀ j : ℤ,
        (gibbsMeasure (ofLong β s) N)
          {X | ¬ ((n : ℝ) ^ (-ε) ≤ gap X j ∧ gap X j ≤ (n : ℝ) ^ ε)} ≤
          ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ (blockTailPower s.val ε))) := by
  obtain ⟨C, c, hC, hc, htail⟩ := SingleGapTails.single_gap_tails_density s.val βlo βhi
    s.property.1 (ne_of_lt s.property.2) hlo hle
  refine ⟨2 * C, c, by positivity, hc, ?_⟩
  intro β hβ N n hN j
  have ht := htail (ofLong β s) rfl hβ.1 hβ.2 N hN j
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hlow := ht.1 ((n : ℝ) ^ (-ε)) (Real.rpow_pos_of_pos hn0 _)
    (Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith))
  have hup := ht.2 ((n : ℝ) ^ ε) (Real.one_le_rpow hn1 hε.le)
  rw [← Real.rpow_mul hn0.le, neg_mul_neg] at hlow
  have hη : min ε (1 / 4) ≤ ε := min_le_left _ _
  have hδ : blockTailPower s.val ε ≤ s.val * ε := by
    have hh : blockTailPower s.val ε ≤ s.val * min ε (1 / 4) / 2 := min_le_left _ _
    have hm := mul_le_mul_of_nonneg_left hη s.property.1.le
    have hp : 0 ≤ s.val * min ε (1 / 4) := by positivity [s.property.1]
    linarith
  have hδε : blockTailPower s.val ε ≤ ε := hδ.trans (by nlinarith [s.property.2])
  have hcomp (t : ℝ) (ht : blockTailPower s.val ε ≤ t) :
      ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ t)) ≤
      ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ (blockTailPower s.val ε))) := by
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.exp_le_exp.mpr
    nlinarith [Real.rpow_le_rpow_of_exponent_le hn1 ht]
  have hsub : {X : Riesz1.Configuration N |
      ¬ ((n : ℝ) ^ (-ε) ≤ gap X j ∧ gap X j ≤ (n : ℝ) ^ ε)} ⊆
      {X | gap X j ≤ (n : ℝ) ^ (-ε)} ∪ {X | (n : ℝ) ^ ε ≤ gap X j} := by
    intro X hX
    by_cases h : (n : ℝ) ^ (-ε) ≤ gap X j
    · exact Or.inr (le_of_lt (lt_of_not_ge (fun hh => hX ⟨h, hh⟩)))
    · exact Or.inl (le_of_lt (lt_of_not_ge h))
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  have hh := add_le_add (hlow.trans (hcomp (ε * s.val) (by nlinarith [hδ])))
    (hup.trans (hcomp ε hδε))
  refine hh.trans_eq ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  ring

private theorem finite_failure_mass_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (P : ι → Ω → Prop) (a : ℝ≥0∞)
    (hb : ∀ i, μ {x | ¬ P i x} ≤ a) :
    μ {x | ¬ ∀ i, P i x} ≤ Fintype.card ι * a := by
  have hset : {x | ¬ ∀ i, P i x} = ⋃ i, {x | ¬ P i x} := by ext x; simp
  rw [hset]
  exact (measure_iUnion_fintype_le _ _).trans
    ((Finset.sum_le_sum (fun i _ => hb i)).trans_eq (by simp [nsmul_eq_mul]))

/-- See Subsection 5.1 of the paper, simultaneous gap and interval bounds and
the normalizer clause. Proper active intervals do not wrap. Full-cycle
intervals may wrap. All constants and the size threshold precede the
temperature in a compact positive interval. The displayed tail power
depends only on `s, ε`. The upper-gap law is used literally. -/
theorem uniform_good_blocks (hRig : External.LongRangeRigidityLocallyUniform)
    (s : Riesz1.RieszExponent) {ε Cθ : ℝ} (hε : 0 < ε) (hCθ : 1 ≤ Cθ)
    (βlo βhi : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ n₀ : ℕ,
      ∀ (β : InverseTemperature), β.val ∈ Icc βlo βhi →
      ∀ (N n : ℕ+) (_hN : 2 ≤ (N : ℕ)) (hn : (n : ℕ) ≤ (N : ℕ)),
      (n = N ∨ 2 * (n : ℕ) ≤ (N : ℕ)) → ∀ θ : PhysicalCutoff,
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      (tiltedParticleMeasure (ofLong β s) N n hn θ ε false)
        {X | ¬ ((∀ i : Fin (n : ℕ),
          (n : ℝ) ^ (-ε) ≤ gap X i.val ∧ gap X i.val ≤ (n : ℝ) ^ ε) ∧
          ∀ (j : Fin (n : ℕ)) (k : Fin ((n : ℕ) + 1)),
            1 ≤ k.val → k.val ≤ (N : ℕ) / 2 →
            (j.val + k.val ≤ (n : ℕ) ∨ n = N) →
            |Riesz1.blockLength X j.val k.val - (k.val : ℝ)| ≤
              (n : ℝ) ^ ε * (k.val : ℝ) ^ (s.val / 2))} ≤
          ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ (blockTailPower s.val ε))) ∧
      (n₀ ≤ (n : ℕ) → (1 / 2 : ℝ≥0∞) ≤ tiltNormalizer (ofLong β s) N n hn θ ε false) := by
  obtain ⟨G, g, hG, hg, hgap⟩ := cutoff_tails s hε βlo βhi hlo hle
  obtain ⟨B, b, hB, hb, hblock⟩ := block_tails_all_sizes hRig s hε βlo βhi hlo hle
  obtain ⟨z, hz, hzhalf, hZ⟩ := normalizer_uniform_lower hε hCθ (by linarith : 0 < βhi)
  obtain ⟨n₀, hhalf⟩ := normalizer_eventually_half hε
  let d := min g b
  let D := max G B
  have hd : 0 < d := lt_min hg hb
  have hD : 0 < D := lt_of_lt_of_le hG (le_max_left _ _)
  have hδ := blockTailPower_pos s.property.1 s.property.2 hε
  obtain ⟨K, hK, hAbsorb⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := 2) hδ (show d / 2 < d by linarith)
  refine ⟨z⁻¹ * (3 * D * (K + 1)), d / 2, by positivity, by positivity, n₀, ?_⟩
  intro β hβ N n hN hn _hpermitted θ hcurv
  refine ⟨?_, hhalf (ofLong β s) N n hN hn θ⟩
  let μ := gibbsMeasure (ofLong β s) N
  let e := Real.exp (-d * (n : ℝ) ^ (blockTailPower s.val ε))
  have he : 0 < e := Real.exp_pos _
  have hcommon (A a : ℝ) (hAD : A ≤ D) (ha : d ≤ a) :
      ENNReal.ofReal (A * Real.exp (-a * (n : ℝ) ^ (blockTailPower s.val ε))) ≤
        ENNReal.ofReal (D * e) := by
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul hAD _ (Real.exp_pos _).le hD.le
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n) (blockTailPower s.val ε))
    linarith
  let P := fun (i : Fin (n : ℕ)) (X : Riesz1.Configuration N) =>
    (n : ℝ) ^ (-ε) ≤ gap X i.val ∧ gap X i.val ≤ (n : ℝ) ^ ε
  let Q := fun (a : Fin (n : ℕ) × Fin ((n : ℕ) + 1)) (X : Riesz1.Configuration N) =>
    1 ≤ a.2.val → a.2.val ≤ (N : ℕ) / 2 →
      (a.1.val + a.2.val ≤ (n : ℕ) ∨ n = N) →
      |Riesz1.blockLength X a.1.val a.2.val - (a.2.val : ℝ)| ≤
        (n : ℝ) ^ ε * (a.2.val : ℝ) ^ (s.val / 2)
  have hP := finite_failure_mass_le μ P (ENNReal.ofReal (D * e)) (fun i =>
    (hgap β hβ N n hN i.val).trans (hcommon G g (le_max_left _ _) (min_le_left _ _)))
  have hQ := finite_failure_mass_le μ Q (ENNReal.ofReal (D * e)) (fun a => by
    by_cases hk : 1 ≤ a.2.val
    · by_cases hkN : a.2.val ≤ (N : ℕ) / 2
      · by_cases hint : a.1.val + a.2.val ≤ (n : ℕ) ∨ n = N
        · have hs : {X | ¬ Q a X} = {X : Riesz1.Configuration N |
              (n : ℝ) ^ ε * (a.2.val : ℝ) ^ (s.val / 2) <
                |Riesz1.blockLength X a.1.val a.2.val - (a.2.val : ℝ)|} := by
            ext X
            simp only [Q, hk, hkN, hint, true_implies, not_le, mem_ofPred_eq]
          rw [hs]
          exact (hblock β hβ N n hN hn a.1.val a.2.val hk (by omega) hkN).trans
            (hcommon B b (le_max_right _ _) (min_le_right _ _))
        · simp [Q, hint]
      · simp [Q, hkN]
    · simp [Q, hk])
  have hun : μ {X | ¬ ((∀ i, P i X) ∧ ∀ a, Q a X)} ≤
      (Fintype.card (Fin (n : ℕ)) : ℝ≥0∞) * ENNReal.ofReal (D * e) +
        (Fintype.card (Fin (n : ℕ) × Fin ((n : ℕ) + 1)) : ℝ≥0∞) * ENNReal.ofReal (D * e) := by
    have hs : {X | ¬ ((∀ i, P i X) ∧ ∀ a, Q a X)} =
        {X | ¬ ∀ i, P i X} ∪ {X | ¬ ∀ a, Q a X} := by
      ext X
      simp only [mem_ofPred_eq, mem_union]
      tauto
    rw [hs]
    exact (measure_union_le _ _).trans (add_le_add hP hQ)
  have hprob : μ {X | ¬ ((∀ i, P i X) ∧ ∀ a, Q a X)} ≤
      ENNReal.ofReal (3 * D * (K + 1) *
        Real.exp (-(d / 2) * (n : ℝ) ^ (blockTailPower s.val ε))) := by
    refine hun.trans ?_
    simp only [Fintype.card_fin, Fintype.card_prod]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
    have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
    have hpol : (n : ℝ) + (n : ℝ) * ((n : ℝ) + 1) ≤ 3 * (n : ℝ) ^ (2 : ℝ) := by
      rw [Real.rpow_two]
      nlinarith
    have hab := hAbsorb (n : ℝ) hn1
    have hh := mul_le_mul_of_nonneg_left hab (show 0 ≤ 3 * D by positivity)
    have hstart := mul_le_mul_of_nonneg_right hpol (show 0 ≤ D * e by positivity)
    push_cast
    dsimp [e] at hstart ⊢
    nlinarith [mul_le_mul_of_nonneg_left (show K ≤ K + 1 by linarith)
      (show 0 ≤ 3 * D * Real.exp (-(d / 2) * (n : ℝ) ^ blockTailPower s.val ε) by positivity)]
  have hzlow := hZ (ofLong β s) hβ.2 N n hN hn θ hcurv
  have hmeasure : tiltedParticleMeasure (ofLong β s) N n hn θ ε false ≤
      ENNReal.ofReal z⁻¹ • μ := by
    refine (tilted_measure_le (ofLong β s) N n hn θ ε).trans ?_
    have hi := ENNReal.inv_le_inv.mpr hzlow
    rw [← ENNReal.ofReal_inv_of_pos hz] at hi
    gcongr
  have hfinal := (hmeasure {X | ¬ ((∀ i, P i X) ∧ ∀ a, Q a X)}).trans
    (mul_le_mul_right hprob (ENNReal.ofReal z⁻¹))
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hz.le)] at hfinal
  have hset : {X | ¬ ((∀ i, P i X) ∧ ∀ a, Q a X)} =
      {X : Riesz1.Configuration N | ¬ ((∀ i : Fin (n : ℕ),
        (n : ℝ) ^ (-ε) ≤ gap X i.val ∧ gap X i.val ≤ (n : ℝ) ^ ε) ∧
        ∀ (j : Fin (n : ℕ)) (k : Fin ((n : ℕ) + 1)),
          1 ≤ k.val → k.val ≤ (N : ℕ) / 2 →
          (j.val + k.val ≤ (n : ℕ) ∨ n = N) →
          |Riesz1.blockLength X j.val k.val - (k.val : ℝ)| ≤
            (n : ℝ) ^ ε * (k.val : ℝ) ^ (s.val / 2))} := by
    ext X
    simp only [P, Q, Prod.forall]
  rw [hset] at hfinal
  convert hfinal using 1
  congr 1
  ring

end Riesz2.GoodBlocks
