/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.LengthVariance
public import Riesz2.HelfferSjostrand.MarginalHessianPart5
public import Riesz2.ToMathlib.ConvexIntervalMarginal
public import Riesz2.DecayLong.GoodBlocks

/-!
# Active length: uniform mean and compensated direction

Supporting results for the proof of Lemma 6.5. The tail power is selected before the
compact temperature interval. The compensated direction reuses the physical marginal
chart.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ContDiff

namespace Riesz2.LengthVariance

open LengthAveragingFibres

/-- See the proof of Lemma 6.5 in the paper: support of the actual two-sided
penalty, uniformly on a compact temperature interval. The power is explicitly
`ε * min s 1` and is independent of the temperature interval and cutoff. -/
theorem compact_penalty_support (s ε βlo βhi : ℝ) (hs : 0 < s)
    (hε : 0 < ε) (hlo : 0 < βlo) (hle : βlo ≤ βhi) (θ : PhysicalCutoff) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ N n : ℕ+, 2 ≤ (N : ℕ) → ∀ hn : (n : ℕ) ≤ (N : ℕ),
      (gibbsMeasure p N).real {X | physicalGapPenalty N n hn θ ε true X ≠ 0} ≤
        C * Real.exp (-c * (n : ℝ) ^ (ε * min s 1)) := by
  obtain ⟨A, hA, hi⟩ := SingleGapTails.inverse_exponential_moment s βlo βhi hs hlo hle
  let c := min (Real.log 2 / 8) (βlo / 2 ^ s)
  have hc : 0 < c := lt_min
    (div_pos (Real.log_pos one_lt_two) (by norm_num)) (div_pos hlo (by positivity))
  obtain ⟨B, hB, hb⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := 1) (c := c) (c' := c / 2) (mul_pos hε (lt_min hs zero_lt_one)) (by linarith)
  refine ⟨(3 + A) * B + 1, c / 2, by positivity, by positivity, ?_⟩
  intro p hps hpl hph N n hN hn
  have := gibbsMeasure_probability p N
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast n.pos
  have htail (j : ℤ) (u : ℝ) :
      gibbsMeasure p N {X | u ≤ gap X j ^ (-s)} ≤
        ENNReal.ofReal (A * Real.exp (-βlo * u)) :=
    ExponentialPower.closed_tail hlo (hi p hps hpl hph N hN j).1
      (hi p hps hpl hph N hN j).2 u
  rw [← InterpolatingDensities.activeGapPenalty_eq]
  have ht := DecayShort.activeGapPenalty_measureReal_le p hN θ hs.le
    (show 0 < (n : ℝ) ^ ε by positivity) hA.le htail true
    (InterpolatingDensities.activeLabels N n hn)
  rw [InterpolatingDensities.card_activeLabels] at ht
  apply ht.trans
  have he := InterpolatingDensities.internal_two_tail_bound hs hlo hε hA.le hn1
  have hp := hb (n : ℝ) hn1
  rw [Real.rpow_one] at hp
  calc
    _ ≤ (n : ℝ) * ((3 + A) * Real.exp (-c * (n : ℝ) ^ (ε * min s 1))) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = (3 + A) * ((n : ℝ) * Real.exp (-c * (n : ℝ) ^ (ε * min s 1))) := by ring
    _ ≤ (3 + A) * (B * Real.exp (-(c / 2) * (n : ℝ) ^ (ε * min s 1))) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ _ := by nlinarith [Real.exp_pos (-(c / 2) * (n : ℝ) ^ (ε * min s 1))]

/-- See the proof of Lemma 6.5 in the paper: the complete mean clause,
uniform on each compact positive temperature interval. The tail power is
chosen using only `s, ε`, before that interval, both volumes, and the cutoff. -/
theorem mean_exponential_locally_uniform (s ε : ℝ) (hs : 0 < s)
    (hs1 : s ≠ 1) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
      ∀ θ : PhysicalCutoff, ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ n m : ℕ,
        |(∫ x, ∑ i, x i ∂activeMeasure p n m θ ε) - (n + 1 : ℝ)| ≤
          C * Real.exp (-c * (n + 1 : ℝ) ^ δ) := by
  let δ := ε * min s 1
  have hδ : 0 < δ := mul_pos hε (lt_min hs zero_lt_one)
  refine ⟨δ, hδ, fun βlo βhi hlo hle θ => ?_⟩
  obtain ⟨A, c, hA, hc, hrare⟩ := compact_penalty_support s ε βlo βhi hs hε hlo hle θ
  obtain ⟨z, hz, hnorm⟩ := InterpolantLocalLaws.compact_tilt_normalizer
    s ε βlo βhi hs hs1 hε hlo hle θ
  obtain ⟨L, hL, hm⟩ := SingleGapTails.single_gap_moments
    s βlo βhi hs hs1 hlo hle 1 (by norm_num)
  let K := L * (2 + (2 : ℝ) ^ (1 / s))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let D := z⁻¹ * (Real.sqrt A + A) * (K + 1)
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨B, hB, hb⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := 1) (c := c / 2) (c' := c / 4) hδ (by linarith)
  refine ⟨D * (B + 1), c / 4, by positivity, by positivity, ?_⟩
  intro p hps hpl hph n m
  let N := ((n + 1) + m).succPNat
  let a : ℕ+ := ⟨n + 1, Nat.succ_pos n⟩
  have hN : 2 ≤ (N : ℕ) := by dsimp [N]; omega
  have hn : (a : ℕ) ≤ (N : ℕ) := by dsimp [N, a]; omega
  have := gibbsMeasure_probability p N
  have := (InterpolatingDensities.tilt_valid p N a hn θ ε true).2.2
  let G := lengthObservable a
  have hiμ := InterpolatingDensities.block_integrable N a G (gibbsMeasure p N)
  have hiQ := InterpolatingDensities.block_integrable N a G
    (tiltedParticleMeasure p N a hn θ ε true)
  have hgapnorm (j : Fin (a : ℕ)) : eLpNorm (fun X : Riesz1.Configuration N => gap X j.val) 2
      (gibbsMeasure p N) ≤ ENNReal.ofReal K := by
    have ht := (hm p hps hpl hph N hN j.val 2 (by norm_num)).1
    simp only [Real.rpow_one, ENNReal.ofReal_ofNat] at ht
    exact (le_add_of_nonneg_right zero_le).trans ht
  obtain ⟨hf, hfnorm⟩ := InterpolatingDensities.internal_centered_block_norm
    (gibbsMeasure p N) G (finiteGapBlock (K := a))
    (fun j => Riesz1.measurable_gap j.val) hK hgapnorm
  have hR : 0 ≤ (a : ℝ) ^ ε := by positivity
  have hF := DecayShort.activeGapPenalty_measurable (N := N) θ hR true
    (InterpolatingDensities.activeLabels N a hn)
  have hF0 := DecayShort.activeGapPenalty_nonneg (N := N) θ hR true
    (InterpolatingDensities.activeLabels N a hn)
  rw [InterpolatingDensities.activeGapPenalty_eq] at hF hF0
  have hrare' := hrare p hps hpl hph N a hN hn
  have hZ := hnorm p hps hpl hph N a hN hn
  let q := A * Real.exp (-c * (a : ℝ) ^ δ)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have he := NonnegativeTilt.abs_integral_expTilt_sub_le hF p.property.1.le hF0 hf hrare'
  change |(∫ X, (G.val (finiteGapBlock X) - G.val (fun _ => 1))
      ∂tiltedParticleMeasure p N a hn θ ε true) -
      (∫ X, (G.val (finiteGapBlock X) - G.val (fun _ => 1)) ∂gibbsMeasure p N)| ≤ _ at he
  rw [integral_sub hiQ (integrable_const _), integral_sub hiμ (integrable_const _)] at he
  simp only [integral_const, probReal_univ, one_smul, sub_sub_sub_cancel_right] at he
  have hZi := inv_anti₀ hz hZ
  have hroot : Real.sqrt q = Real.sqrt A * Real.exp (-(c / 2) * (a : ℝ) ^ δ) := by
    apply (Real.sqrt_eq_iff_eq_sq hq (by positivity)).mpr
    rw [mul_pow, Real.sq_sqrt hA.le, ← Real.exp_nat_mul]
    dsimp only [q]
    congr 2
    ring
  have hq' : q ≤ A * Real.exp (-(c / 2) * (a : ℝ) ^ δ) := by
    apply mul_le_mul_of_nonneg_left _ hA.le
    apply Real.exp_le_exp.mpr
    have hp : 0 ≤ (a : ℝ) ^ δ := by positivity
    nlinarith
  have hsqrt : Real.sqrt q + q ≤
      (Real.sqrt A + A) * Real.exp (-(c / 2) * (a : ℝ) ^ δ) := by
    rw [hroot]
    nlinarith
  have hmean : |(∫ X, G.val (finiteGapBlock X) ∂tiltedParticleMeasure p N a hn θ ε true) -
      (∫ X, G.val (finiteGapBlock X) ∂gibbsMeasure p N)| ≤
        D * Real.exp (-(c / 2) * (a : ℝ) ^ δ) * (a : ℝ) := by
    apply he.trans
    apply le_trans (mul_le_mul
      (mul_le_mul hZi hsqrt (by positivity) (by positivity)) hfnorm
      (Real.sqrt_nonneg _) (by positivity))
    dsimp only [D, G]
    rw [blockDerivativeNorm_length]
    ring_nf
    exact le_rfl
  change |(∫ X, ∑ i : Fin (n + 1), gap X i.val
      ∂tiltedParticleMeasure p N a hn θ ε true) -
      (∫ X, ∑ i : Fin (n + 1), gap X i.val ∂gibbsMeasure p N)| ≤ _ at hmean
  rw [untilted_mean p n m] at hmean
  rw [active_mean_eq]
  apply hmean.trans
  have hp := hb (n + 1 : ℝ) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  rw [Real.rpow_one] at hp
  have hac : (a : ℝ) = n + 1 := by simp [a]
  rw [hac]
  nlinarith [Real.exp_pos (-(c / 4) * (n + 1 : ℝ) ^ δ)]

/-- See the proof of Lemma 6.5 in the paper: the active marginal weight is
exactly a convex exponential density on its entire interior. -/
theorem marginalWeight_convex_exponential (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) :
    ∃ V : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
      ConvexOn ℝ (AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1)) V ∧
      ∀ x ∈ AffineSimplex.chartDomain (n + 1) ((n + 1 + m : ℕ) + 1),
        marginalWeight p n m θ ε x = ENNReal.ofReal (Real.exp (-V x)) := by
  let N := (n + 1 + m).succPNat
  let L : ℝ := ((n + 1 + m : ℕ) + 1)
  let σ := Equiv.refl (Fin ((n + 1) + m + 1))
  obtain ⟨W, _, hval, _, _, hW⟩ := RemovableGapBarrier.selected_gap_barrier_convex
    p N (by dsimp [N]; omega)
  let H := fun q => p.val.1 * W (RetainedSimplex.chart (n + 1) m L σ q)
  have hc : ConvexOn ℝ (RetainedSimplex.domain (n + 1) m L) H := by
    refine ⟨RetainedSimplex.convex_domain _ _ _, ?_⟩
    intro q hq r hr a b ha hb hab
    have hs (q) (hq : q ∈ RetainedSimplex.domain (n + 1) m L) :
        WithLp.ofLp (RetainedSimplex.chart (n + 1) m L σ q) ∈ Riesz1.gapSimplex N := by
      have h := (RetainedSimplex.chart_mem_simplex _ _ _ σ q).mpr hq
      refine ⟨h.1, ?_⟩
      simpa only [N, L, Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using h.2
    change p.val.1 * W (RetainedSimplex.chart (n + 1) m L σ (a • q + b • r)) ≤ _
    rw [RetainedSimplex.chart_convex_combination _ _ _ _ _ _ hab]
    exact (hW.smul p.property.1.le).2 (hs q hq) (hs r hr) ha hb hab
  have hbase := (convexLocalization (RetainedSimplex.isOpen_domain (n + 1) m L)
    hc.1 (RetainedSimplex.isBounded_domain (n + 1) m L) hc (fun _ => 0)).2
  rw [RetainedSimplex.fst_image_domain] at hbase
  let V₀ := fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
    -Real.log (∫ z : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p (n + 1) m σ (x,z)).toReal)
  have hV₀ : ConvexOn ℝ (AffineSimplex.chartDomain (n + 1) L) V₀ := by
    apply hbase.congr
    intro x _
    dsimp only [V₀]
    simp_rw [MarginalCollision.internal_chart_density_real p (n + 1) m σ hval]
    simp only [zero_sub, sub_zero, H, neg_mul, L]
  let a := (n + 1 : ℝ) ^ (-ε)
  let P := fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
    ∑ i : Fin (n + 1), (θ.val (a * x i) + θ.val (a * (x i)⁻¹))
  have hP : ConvexOn ℝ (AffineSimplex.chartDomain (n + 1) L) P := by
    simpa only [P, ↓reduceIte] using
      (MarginalCollision.active_penalty_smooth_convex (n + 1) L θ
        (show 0 < a by dsimp [a]; positivity) Finset.univ true).2
  refine ⟨fun x => p.val.1 * P x + V₀ x, (hP.smul p.property.1.le).add hV₀, ?_⟩
  intro x hx
  let S : ℝ := ∑ i, x i
  have hsum : ∑ i, x i = S := rfl
  obtain ⟨z, hz⟩ := show x ∈ Set.range (AffineSimplex.centredChart n S) from by
    rw [AffineSimplex.range_centredChart]; exact hsum
  have hzmem : z ∈ AffineSimplex.centredChart n S ⁻¹' AffineSimplex.massSimplex n S := by
    change AffineSimplex.centredChart n S z ∈ AffineSimplex.massSimplex n S
    rw [hz]
    exact ⟨hx.1, rfl⟩
  have ht := ConditionalWellPosedness.penalized_marginal_fibre_density
    p n m σ (show S < L from hx.2) θ a Finset.univ true hzmem
  rw [hz] at ht
  exact ht.symm

/-- See the proof of Lemma 6.5 in the paper: log-concavity of the
canonical, every-point coarea length density, including its exact Jacobian.
The logarithm uses the real value only after positive finiteness is proved. -/
theorem lengthDensity_logConcave (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) :
    ConcaveOn ℝ (Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ))
      (fun L => Real.log ((marginalScale p n m θ ε *
        (ENNReal.ofReal (Real.sqrt (n + 1)))⁻¹ *
        ∫⁻ x, marginalWeight p n m θ ε x ∂AffineSimplex.simplexVolume n L).toReal)) := by
  let L : ℝ := ((n + 1 + m : ℕ) + 1)
  let Ω := AffineSimplex.chartDomain (n + 1) L
  obtain ⟨V, hV, hv⟩ := marginalWeight_convex_exponential p n m θ ε
  let T : (ℝ × EuclideanSpace ℝ (Fin n)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    (AffineSimplex.tangentMap n).comp (LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin n))) +
      (LinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin n))).smulRight (AffineSimplex.chart n 1 0)
  have hT (q : ℝ × EuclideanSpace ℝ (Fin n)) : T q = AffineFibre.SumChart.totalChart n q := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [T, AffineFibre.SumChart.totalChart, AffineSimplex.tangentMap,
        AffineSimplex.chart_last]
      ring
    · simp [T, AffineFibre.SumChart.totalChart, AffineSimplex.tangentMap,
        AffineSimplex.chart_castSucc]
  let Q := T ⁻¹' Ω
  have hQo : IsOpen Q := (AffineSimplex.isOpen_chartDomain _ _).preimage
    T.continuous_of_finiteDimensional
  have hQb : Bornology.IsBounded Q := by
    apply (((AffineSimplex.isBounded_chartDomain (n + 1) L).isCompact_closure.image
      (AffineFibre.SumChart.totalChart n).symm.continuous).isBounded).subset
    intro q hq
    refine ⟨T q, subset_closure hq, ?_⟩
    rw [hT, (AffineFibre.SumChart.totalChart n).symm_apply_apply]
  have hproj : Prod.fst '' Q = Ioo (0 : ℝ) L := by
    ext t
    constructor
    · rintro ⟨⟨u,z⟩, hq, rfl⟩
      have hq' : AffineSimplex.chart n u z ∈ Ω := by
        simpa only [hT, AffineFibre.SumChart.totalChart_apply] using (show T (u,z) ∈ Ω from hq)
      refine ⟨?_, ?_⟩
      · rw [← AffineSimplex.sum_chart n u z]
        exact Finset.sum_pos (fun i _ => hq'.1 i) Finset.univ_nonempty
      · simpa only [AffineSimplex.sum_chart] using hq'.2
    · intro ht
      let x := AffineSimplex.centre n t
      let q := (AffineFibre.SumChart.totalChart n).symm x
      have hq : T q = x := by rw [hT]; exact (AffineFibre.SumChart.totalChart n).apply_symm_apply x
      refine ⟨q, ?_, ?_⟩
      · change T q ∈ Ω
        rw [hq]
        exact ⟨(AffineSimplex.centre_mem_simplex n ht.1).1,
          by simpa only [x, AffineSimplex.sum_centre] using ht.2⟩
      · exact AffineSimplex.sum_centre n t
  let c := (marginalScale p n m θ ε).toReal
  have hc : 0 < c := ENNReal.toReal_pos (marginalScale_valid p n m θ ε).1
    (marginalScale_valid p n m θ ε).2
  let J := Q.indicator (fun q => Real.exp (-V (T q)))
  have hconv := hV.comp_linearMap T
  have han := convex_interval_marginal hQo hQb hconv hconv (fun _ => 0)
    (fun _ _ => by simp) hc
  have hi (t : ℝ) : Integrable (fun z => J (t,z)) :=
    Riesz1.integrable_fiber_exp_indicator hQo hQb hconv t
  have hJ0 (q) : 0 ≤ J q := indicator_nonneg (fun _ _ => (Real.exp_pos _).le) q
  have he (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) L) :
      (marginalScale p n m θ ε * (ENNReal.ofReal (Real.sqrt (n + 1)))⁻¹ *
        ∫⁻ x, marginalWeight p n m θ ε x ∂AffineSimplex.simplexVolume n t).toReal =
          c * ∫ z, J (t,z) := by
    have hf (z : EuclideanSpace ℝ (Fin n)) :
        (AffineSimplex.chartDomain n t).indicator
          (fun z => marginalWeight p n m θ ε (AffineSimplex.chart n t z)) z =
        ENNReal.ofReal (J (t,z)) := by
      have hiff : z ∈ AffineSimplex.chartDomain n t ↔ (t,z) ∈ Q := by
        change _ ↔ T (t,z) ∈ AffineSimplex.chartDomain (n + 1) L
        rw [hT, AffineFibre.SumChart.totalChart_apply]
        rw [← AffineSimplex.chart_mem_simplex_iff]
        constructor
        · intro hz
          exact ⟨hz.1, by simpa only [AffineSimplex.sum_chart] using ht.2⟩
        · intro hz
          exact ⟨hz.1, AffineSimplex.sum_chart n t z⟩
      by_cases hz : z ∈ AffineSimplex.chartDomain n t
      · rw [indicator_of_mem hz]
        change _ = ENNReal.ofReal (Q.indicator _ (t,z))
        rw [indicator_of_mem (hiff.mp hz), hT, AffineFibre.SumChart.totalChart_apply]
        apply hv
        have hh : T (t,z) ∈ Ω := hiff.mp hz
        simpa only [hT, AffineFibre.SumChart.totalChart_apply] using hh
      · rw [indicator_of_notMem hz]
        change _ = ENNReal.ofReal (Q.indicator _ (t,z))
        rw [indicator_of_notMem (fun h => hz (hiff.mpr h)), ENNReal.ofReal_zero]
    rw [AffineSimplex.lintegral_simplexVolume, ← lintegral_indicator
      (AffineSimplex.isOpen_chartDomain n t).measurableSet]
    simp_rw [hf]
    rw [mul_assoc, ← mul_assoc ((ENNReal.ofReal (Real.sqrt (n + 1)))⁻¹) _,
      ENNReal.inv_mul_cancel
      (ENNReal.ofReal_ne_zero_iff.mpr (Real.sqrt_pos.mpr (by positivity)))
      ENNReal.ofReal_ne_top, one_mul,
      ← ofReal_integral_eq_lintegral_ofReal (hi t)
        (Filter.Eventually.of_forall fun z => hJ0 (t,z)), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (integral_nonneg fun z => hJ0 (t,z))]
  have hlog := han.2.2.2.1
  rw [hproj] at hlog
  exact hlog.congr (fun t ht => congrArg Real.log (he t ht).symm)

/-- See the proof of Lemma 6.5 in the paper: the log-concavity inequality
written directly with the canonical `lengthDensity`, at every pair of interior
lengths and every convex combination, including its endpoints. -/
theorem lengthDensity_logConcave_values (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ)
    (L M : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ∃ h : a * L.val + b * M.val ∈ Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ),
      a * Real.log (lengthDensity p n m θ ε L).toReal +
        b * Real.log (lengthDensity p n m θ ε M).toReal ≤
          Real.log (lengthDensity p n m θ ε ⟨a * L.val + b * M.val, h⟩).toReal := by
  have h := (convex_Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ))
    L.property M.property ha hb hab
  refine ⟨h, ?_⟩
  simpa only [lengthDensity, smul_eq_mul] using
    (lengthDensity_logConcave p n m θ ε).2 L.property M.property ha hb hab

/-- See the proof of Lemma 6.5 in the paper: the existing compensated
chart applied to the unit length displacement has total mass zero and active
mass one. Its exterior entries distribute the compensation uniformly. -/
theorem compensated_length_direction (n m : ℕ) :
    let u : EuclideanSpace ℝ (Fin (n + 1)) := WithLp.toLp 2 (fun _ => (n + 1 : ℝ)⁻¹)
    let w := MarginalHessian.compensatedDirection (n + 1) m (Equiv.refl _) u
    (∑ j, w j) = 0 ∧
      (∑ j : Fin (n + 1), w (j.castAdd (m + 1))) = 1 ∧
      ∀ j, w j = if j.val < n + 1 then (n + 1 : ℝ)⁻¹ else -(m + 1 : ℝ)⁻¹ := by
  classical
  intro u w
  have hu : (∑ i, u i) = 1 := by
    simp only [u, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    push_cast
    exact mul_inv_cancel₀ (by positivity)
  have hactive (j : Fin (n + 1)) : w (j.castAdd (m + 1)) = (n + 1 : ℝ)⁻¹ := by
    exact MarginalHessian.compensatedDirection_retained (n + 1) m (Equiv.refl _) u j
  have hext (j : Fin (m + 1)) : w (j.natAdd (n + 1)) = -(m + 1 : ℝ)⁻¹ := by
    have hh := MarginalHessian.compensatedDirection_exterior (n + 1) m (Equiv.refl _) u j
    rw [hu] at hh
    simpa only [Equiv.refl_apply, neg_div, one_div] using hh
  have ha : (∑ j : Fin (n + 1), w (j.castAdd (m + 1))) = 1 := by
    simp_rw [hactive]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    exact mul_inv_cancel₀ (by positivity)
  refine ⟨?_, ha, ?_⟩
  · calc
      (∑ j, w j) = (∑ j : Fin (n + 1), w (j.castAdd (m + 1))) +
          ∑ j : Fin (m + 1), w (j.natAdd (n + 1)) :=
            Fin.sum_univ_add (a := n + 1) (b := m + 1) (M := ℝ)
              (fun j : Fin ((n + 1) + (m + 1)) => w j)
      _ = 0 := by
        rw [ha]
        simp_rw [hext]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        rw [mul_neg, mul_inv_cancel₀ (by positivity : (m + 1 : ℝ) ≠ 0)]
        ring
  · intro j
    refine Fin.addCases (m := n + 1) (n := m + 1) (fun i => ?_) (fun i => ?_) j
    · rw [hactive, ite_eq_left (by simpa only [Fin.val_castAdd] using i.isLt)]
    · rw [hext, ite_eq_right (by simp only [Fin.val_natAdd]; omega)]

/-- See the proof of Lemma 6.5 in the paper: every physical interval
Hessian coefficient has expectation at most `C r^(-s-2)` under the actual
two-sided tilted law, uniformly over compact temperature intervals. The
complementary periodic images are already included in `particleCoefficient`.
Integrability is concluded before its real expectation is used. -/
theorem compact_interval_curvature (s ε βlo βhi : ℝ) (hs : 0 < s)
    (hs1 : s ≠ 1) (hε : 0 < ε) (hlo : 0 < βlo) (hle : βlo ≤ βhi)
    (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ N n : ℕ+, 2 ≤ (N : ℕ) →
      ∀ hn : (n : ℕ) ≤ (N : ℕ), ∀ (j : ℤ) (r : ℕ) (hr : 0 < r)
        (hrN : r ≤ (N : ℕ) / 2),
      Integrable (GoodBlocks.particleCoefficient p N j r hr hrN)
        (tiltedParticleMeasure p N n hn θ ε true) ∧
      (∫ X, GoodBlocks.particleCoefficient p N j r hr hrN X
        ∂tiltedParticleMeasure p N n hn θ ε true) ≤ C * (r : ℝ) ^ (-s - 2) := by
  obtain ⟨D, hD, hcoeff⟩ := GoodBlocks.particleCoefficient_moments s βlo βhi hs hlo hle
  obtain ⟨z, hz, hnorm⟩ := InterpolantLocalLaws.compact_tilt_normalizer
    s ε βlo βhi hs hs1 hε hlo hle θ
  refine ⟨z⁻¹ * D, by positivity, ?_⟩
  intro p hps hpl hph N n hN hn j r hr hrN
  have := gibbsMeasure_probability p N
  let f := GoodBlocks.particleCoefficient p N j r hr hrN
  have hf : Measurable f := GoodBlocks.measurable_particleCoefficient p N j r hr hrN
  have hf0 (X) : 0 ≤ f X := (GoodBlocks.particleCoefficient_pos p N j r hr hrN X).le
  have hb := hcoeff p hps hpl hph N hN j r hr hrN 1 le_rfl
  simp only [ENNReal.ofReal_one, Real.one_rpow, mul_one] at hb
  rw [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable] at hb
  have hnormeq (X : Riesz1.Configuration N) : ‖f X‖ₑ = ENNReal.ofReal (f X) := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hf0 X)]
  change (∫⁻ X, ‖f X‖ₑ ∂gibbsMeasure p N) ≤ _ at hb
  simp_rw [hnormeq] at hb
  have hR : 0 ≤ (n : ℝ) ^ ε := by positivity
  have hG := DecayShort.activeGapPenalty_measurable (N := N) θ hR true
    (InterpolatingDensities.activeLabels N n hn)
  have hG0 := DecayShort.activeGapPenalty_nonneg (N := N) θ hR true
    (InterpolatingDensities.activeLabels N n hn)
  rw [InterpolatingDensities.activeGapPenalty_eq] at hG hG0
  have ht := NonnegativeTilt.lintegral_expTilt_le (μ := gibbsMeasure p N)
    hG p.property.1.le hG0 hf.ennreal_ofReal
  rw [NonnegativeTilt.lintegral_normalizer_eq hG p.property.1.le hG0] at ht
  have hZ := hnorm p hps hpl hph N n hN hn
  have hZi : (ENNReal.ofReal (NonnegativeTilt.expTiltNormalizer (gibbsMeasure p N)
      p.val.1 (physicalGapPenalty N n hn θ ε true)))⁻¹ ≤ ENNReal.ofReal z⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hz]
    exact ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal hZ)
  have hbound : (∫⁻ X, ENNReal.ofReal (f X) ∂tiltedParticleMeasure p N n hn θ ε true) ≤
      ENNReal.ofReal (z⁻¹ * D * (r : ℝ) ^ (-s - 2)) := by
    apply ht.trans
    apply (mul_le_mul hZi hb zero_le zero_le).trans_eq
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  have hfi : Integrable f (tiltedParticleMeasure p N n hn θ ε true) :=
    ⟨hf.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hf0)).mpr
        (hbound.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hfi, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
  rw [ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf0)]
  exact hbound

namespace Internal

/-- See the proof of Lemma 6.5 in the paper: diagonal curvature of the
actual two-sided penalty. This bound retains the individual direction entries,
which is essential for the length direction of size `1/n` on active labels. -/
theorem penalty_direction_curvature (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 < a → ∀ n : ℕ,
      ∀ x u : EuclideanSpace ℝ (Fin n), (∀ i, 0 < x i) →
      0 ≤ fderiv ℝ (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) =>
        ∑ i, (θ.val (a * y i) + θ.val (a / y i)))) x u u ∧
      fderiv ℝ (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) =>
        ∑ i, (θ.val (a * y i) + θ.val (a / y i)))) x u u ≤
          C * a ^ 2 * ∑ i, (1 + (x i)⁻¹ ^ 4) * (u i) ^ 2 := by
  obtain ⟨C₀, hC₀, hup⟩ := PhysicalCollision.upper_penalty_curvature θ
  obtain ⟨C₁, hC₁, hinv⟩ := PhysicalCollision.inverse_penalty_curvature θ
  refine ⟨C₀ + C₁, by positivity, fun a ha n x u hx => ?_⟩
  let φ := fun t : ℝ => θ.val (a * t) + θ.val (a / t)
  have hφ (t : ℝ) (ht : 0 < t) : ContDiffAt ℝ ∞ φ t :=
    ((PhysicalCollision.cutoff_contDiffAt θ (mul_pos ha ht)).comp t
      (contDiffAt_const.mul contDiffAt_id)).add
      ((PhysicalCollision.cutoff_contDiffAt θ (div_pos ha ht)).comp t
        (contDiffAt_const.div contDiffAt_id ht.ne'))
  have hφ'' (t : ℝ) (ht : 0 < t) :
      0 ≤ deriv (deriv φ) t ∧
      deriv (deriv φ) t ≤ (C₀ + C₁) * a ^ 2 * (1 + t⁻¹ ^ 4) := by
    have hu := (PhysicalCollision.cutoff_contDiffAt θ (mul_pos ha ht)).comp t
      (contDiffAt_const.mul contDiffAt_id)
    have hi := (PhysicalCollision.cutoff_contDiffAt θ (div_pos ha ht)).comp t
      (contDiffAt_const.div contDiffAt_id ht.ne')
    have hh := PhysicalCollision.internal_hessian_add
      (hu.of_le (by simp)) (hi.of_le (by simp)) 1 1
    simp only [PhysicalCollision.internal_scalar_hessian, mul_one, Function.comp_def] at hh
    change deriv (deriv φ) t = _ at hh
    rw [hh]
    refine ⟨add_nonneg (hup a t ha ht).1 (hinv a t ha ht).1, ?_⟩
    have h := add_le_add (hup a t ha ht).2 (hinv a t ha ht).2
    nlinarith [mul_nonneg (mul_nonneg hC₀.le (sq_nonneg a))
      (pow_nonneg (inv_nonneg.mpr ht.le) 4), mul_nonneg hC₁.le (sq_nonneg a)]
  have hs (i : Fin n) : ContDiffAt ℝ 2
      (fun y : EuclideanSpace ℝ (Fin n) => φ (y i)) x :=
    ((hφ _ (hx i)).comp x (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt).of_le (by simp)
  have he (i : Fin n) :
      fderiv ℝ (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => φ (y i))) x u u =
        deriv (deriv φ) (x i) * (u i) ^ 2 := by
    simpa only [EuclideanSpace.coe_proj, add_zero] using
      PhysicalCollision.internal_scalar_affine_hessian φ (EuclideanSpace.proj (𝕜 := ℝ) i) 0
        (z := x) (by simpa only [EuclideanSpace.coe_proj, add_zero] using
          (hφ _ (hx i)).of_le (by simp)) u
  change 0 ≤ fderiv ℝ (fderiv ℝ (fun y => ∑ i, φ (y i))) x u u ∧ _
  rw [PhysicalCollision.internal_hessian_sum Finset.univ _ (fun i _ => hs i) u]
  simp_rw [he]
  constructor
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hφ'' _ (hx i)).1 (sq_nonneg _))
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_right (hφ'' _ (hx i)).2 (sq_nonneg (u i))

end Internal

/-- See the proof of Lemma 6.5 in the paper: the expected penalty
curvature in the compensated length direction is `O(n^(-1-2ε))`, uniformly
on compact temperature intervals. This already is smaller than `n^(-min(s,1))`. The exponentially rare support is unnecessary for the lower variance bound.
The Hessian is that of the actual penalty on active coordinates. -/
theorem expected_penalty_curvature (s ε βlo βhi : ℝ) (hs : 0 < s)
    (hs1 : s ≠ 1) (hε : 0 < ε) (hlo : 0 < βlo) (hle : βlo ≤ βhi)
    (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ N n : ℕ+, 2 ≤ (N : ℕ) →
      ∀ hn : (n : ℕ) ≤ (N : ℕ),
      let P := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
        ∑ i, (θ.val ((n : ℝ) ^ (-ε) * y i) + θ.val ((n : ℝ) ^ (-ε) / y i))
      let u : EuclideanSpace ℝ (Fin (n : ℕ)) := WithLp.toLp 2 (fun _ => (n : ℝ)⁻¹)
      (∫⁻ X, ENNReal.ofReal (fderiv ℝ (fderiv ℝ P)
        (WithLp.toLp 2 (finiteGapBlock (K := n) X)) u u)
        ∂tiltedParticleMeasure p N n hn θ ε true) ≤
          ENNReal.ofReal (C * (n : ℝ) ^ (-1 - 2 * ε)) := by
  obtain ⟨M, hM, hm⟩ := InterpolantLocalLaws.compact_tilted_gap_moments
    s ε βlo βhi hs hs1 hε hlo hle θ 4 (by norm_num)
  obtain ⟨D, hD, hd⟩ := Internal.penalty_direction_curvature θ
  refine ⟨D * (1 + M), by positivity, fun p hps hpl hph N n hN hn => ?_⟩
  intro P u
  let μ := tiltedParticleMeasure p N n hn θ ε true
  have := (InterpolatingDensities.tilt_valid p N n hn θ ε true).2.2
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hi (i : Fin (n : ℕ)) :
      (∫⁻ X, ENNReal.ofReal (1 + (gap X i.val)⁻¹ ^ 4) ∂μ) ≤ ENNReal.ofReal (1 + M) := by
    have h := (le_add_of_nonneg_left zero_le).trans (hm p hps hpl hph N n hN hn i.val)
    have he (X : Riesz1.Configuration N) : (gap X i.val) ^ (-(4 : ℝ)) =
        (gap X i.val)⁻¹ ^ 4 := by
      calc
        _ = ((gap X i.val) ^ (4 : ℝ))⁻¹ :=
          Real.rpow_neg (show 0 ≤ gap X i.val from (Riesz1.gap_pos X i.val).le) 4
        _ = _ := by
          change ((gap X i.val) ^ ((4 : ℕ) : ℝ))⁻¹ = _
          rw [Real.rpow_natCast, inv_pow]
    have h' : (∫⁻ X, ENNReal.ofReal ((gap X i.val)⁻¹ ^ 4) ∂μ) ≤ ENNReal.ofReal M := by
      convert h using 1
      congr 1
      ext X
      exact congrArg ENNReal.ofReal (he X).symm
    have heA (X : Riesz1.Configuration N) : ENNReal.ofReal (1 + (gap X i.val)⁻¹ ^ 4) =
        1 + ENNReal.ofReal ((gap X i.val)⁻¹ ^ 4) := by
      rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one]
    simp_rw [heA]
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      ENNReal.ofReal_add (by norm_num) hM.le, ENNReal.ofReal_one]
    exact add_le_add le_rfl h'
  have hg (i : Fin (n : ℕ)) : Measurable (fun X : Riesz1.Configuration N =>
      ENNReal.ofReal (1 + (gap X i.val)⁻¹ ^ (4 : ℕ))) := by
    exact (measurable_const.add ((Riesz1.measurable_gap i.val).inv.pow_const 4)).ennreal_ofReal
  calc
    _ ≤ ∫⁻ X, ENNReal.ofReal (D * ((n : ℝ) ^ (-ε)) ^ 2 * (n : ℝ)⁻¹ ^ 2 *
        ∑ i : Fin (n : ℕ), (1 + (gap X i.val)⁻¹ ^ 4)) ∂μ := by
      apply lintegral_mono
      intro X
      apply ENNReal.ofReal_le_ofReal
      have h := (hd ((n : ℝ) ^ (-ε)) (by positivity) n
        (WithLp.toLp 2 (finiteGapBlock (K := n) X)) u
        (fun i => Riesz1.gap_pos X i.val)).2
      apply h.trans_eq
      change D * ((n : ℝ) ^ (-ε)) ^ 2 *
        (∑ i : Fin (n : ℕ), (1 + (gap X i.val)⁻¹ ^ 4) * (n : ℝ)⁻¹ ^ 2) = _
      rw [← Finset.sum_mul]
      ring
    _ = ENNReal.ofReal (D * ((n : ℝ) ^ (-ε)) ^ 2 * (n : ℝ)⁻¹ ^ 2) *
        ∑ i : Fin (n : ℕ), ∫⁻ X, ENNReal.ofReal (1 + (gap X i.val)⁻¹ ^ 4) ∂μ := by
      have he (X : Riesz1.Configuration N) :
          ENNReal.ofReal (D * ((n : ℝ) ^ (-ε)) ^ 2 * (n : ℝ)⁻¹ ^ 2 *
            ∑ i : Fin (n : ℕ), (1 + (gap X i.val)⁻¹ ^ 4)) =
          ENNReal.ofReal (D * ((n : ℝ) ^ (-ε)) ^ 2 * (n : ℝ)⁻¹ ^ 2) *
            ∑ i : Fin (n : ℕ), ENNReal.ofReal (1 + (gap X i.val)⁻¹ ^ 4) := by
        rw [ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
      simp_rw [he]
      rw [lintegral_const_mul _ (Finset.measurable_sum _ fun i _ => hg i),
        lintegral_finsetSum _ (fun i _ => hg i)]
    _ ≤ ENNReal.ofReal (D * ((n : ℝ) ^ (-ε)) ^ 2 * (n : ℝ)⁻¹ ^ 2) *
        ∑ _i : Fin (n : ℕ), ENNReal.ofReal (1 + M) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hi i) zero_le
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have hp : ((n : ℝ) ^ (-ε)) ^ 2 = (n : ℝ) ^ (-2 * ε) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
        congr 1
        ring
      rw [hp]
      have hn : (n : ℝ)⁻¹ ^ 2 * (n : ℝ) = (n : ℝ)⁻¹ := by field_simp
      calc
        _ = D * (1 + M) * ((n : ℝ) ^ (-2 * ε) * (n : ℝ)⁻¹) := by
          rw [show D * (n : ℝ) ^ (-2 * ε) * (n : ℝ)⁻¹ ^ 2 *
              ((n : ℝ) * (1 + M)) = D * (1 + M) * (n : ℝ) ^ (-2 * ε) *
                ((n : ℝ)⁻¹ ^ 2 * (n : ℝ)) by ring, hn]
          ring
        _ = _ := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add hn0]
          congr 2
          ring

end Riesz2.LengthVariance
