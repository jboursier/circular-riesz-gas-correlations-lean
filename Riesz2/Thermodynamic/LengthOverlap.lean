/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.LengthVariancePart4
public import Riesz2.Thermodynamic.LengthDerivative
public import Riesz2.Frozen.External.ThermodynamicLogConcavity
public import Riesz2.Frozen.DependsOnBlockCoordinates
public import Riesz2.Frozen.RestrictedBlockDerivativeNorm
public import Riesz2.ToMathlib.DensityOverlap
public import Riesz2.ToMathlib.MomentEventBounds

/-!
# Common length distributions

Supporting interfaces for the proof of Proposition 6.6. The density on ℝ is the
canonical coarea density on its open carrier and zero off that carrier, as required for
comparing different volumes.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Riesz2.LengthOverlap

open LengthAveragingFibres LengthDerivative

/-- See Lemma 6.5 of the paper: the actual coarea density on ℝ. Its zero value
outside `(0,N)` expresses the support of the length law. -/
def realLengthDensity (p : Parameters) (n m : ℕ) (θ : PhysicalCutoff) (ε : ℝ)
    (L : ℝ) : ℝ :=
  if h : L ∈ Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ) then
    (lengthDensity p n m θ ε ⟨L, h⟩).toReal else 0

/-- The density extension is measurable and nonnegative everywhere. -/
theorem realLengthDensity_measurable (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) :
    Measurable (realLengthDensity p n m θ ε) ∧
      ∀ L, 0 ≤ realLengthDensity p n m θ ε L := by
  refine ⟨?_, fun L => ?_⟩
  · exact Measurable.dite (ENNReal.measurable_toReal.comp
      (measurable_lengthDensity p n m θ ε)) measurable_const measurableSet_Ioo
  · dsimp only [realLengthDensity]
    split_ifs <;> positivity

/-- The strictly positive support of the real density is exactly the
full physical open interval, not a smaller almost-everywhere support. -/
theorem realLengthDensity_pos (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) :
    {L | 0 < realLengthDensity p n m θ ε L} =
      Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ) := by
  ext L
  by_cases h : L ∈ Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)
  · simp only [mem_ofPred_eq, realLengthDensity, h, iff_true]
    exact ENNReal.toReal_pos (lengthDensity_valid p n m θ ε ⟨L,h⟩).1
      (lengthDensity_valid p n m θ ε ⟨L,h⟩).2
  · change (0 < realLengthDensity p n m θ ε L) ↔ _
    rw [realLengthDensity, dite_eq_right h]
    simp only [lt_self_iff_false, false_iff]
    exact h

/-- The logarithm of the canonical coarea density is concave on its positive support. -/
theorem realLengthDensity_logConcave (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) :
    ConcaveOn ℝ {L | 0 < realLengthDensity p n m θ ε L}
      (fun L => Real.log (realLengthDensity p n m θ ε L)) := by
  rw [realLengthDensity_pos]
  refine ⟨convex_Ioo _ _, fun L hL M hM a b ha hb hab => ?_⟩
  have h : a * L + b * M ∈ Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ) := by
    simpa only [smul_eq_mul] using
      (convex_Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) hL hM ha hb hab
  have he := (LengthVariance.lengthDensity_logConcave p n m θ ε).2 hL hM ha hb hab
  simpa only [realLengthDensity, smul_eq_mul, dite_eq_left hL, dite_eq_left hM, dite_eq_left h,
    lengthDensity] using he

/-- The extension has exactly the existing sum-image law. This bridge
retains the physical coarea Jacobian and the active marginal. -/
theorem realLengthDensity_law (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) :
    volume.withDensity (fun L => ENNReal.ofReal (realLengthDensity p n m θ ε L)) =
      (activeMeasure p n m θ ε).map (fun x => ∑ i, x i) := by
  rw [← lengthMeasure_map p n m θ ε]
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_withDensity_eq_lintegral_mul _
    (realLengthDensity_measurable p n m θ ε).1.ennreal_ofReal hf,
    lintegral_map hf measurable_subtype_coe, lengthMeasure]
  change (∫⁻ L, ENNReal.ofReal (realLengthDensity p n m θ ε L) * f L) =
    ∫⁻ L, (f ∘ Subtype.val) L ∂(volume.comap Subtype.val).withDensity (lengthDensity p n m θ ε)
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_lengthDensity p n m θ ε)
    (hf.comp measurable_subtype_coe)]
  let Ω := Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)
  have he (L : ℝ) : ENNReal.ofReal (realLengthDensity p n m θ ε L) * f L =
      Ω.indicator (fun L => ENNReal.ofReal (realLengthDensity p n m θ ε L) * f L) L := by
    by_cases hL : L ∈ Ω
    · rw [indicator_of_mem hL]
    · rw [indicator_of_notMem hL]
      change ENNReal.ofReal (if h : L ∈ Ω then _ else 0) * f L = 0
      rw [dite_eq_right hL, ENNReal.ofReal_zero, zero_mul]
  rw [lintegral_congr he]
  rw [lintegral_indicator measurableSet_Ioo]
  rw [← lintegral_subtype_comap measurableSet_Ioo
    (fun L => ENNReal.ofReal (realLengthDensity p n m θ ε L) * f L)]
  apply lintegral_congr
  intro L
  rw [realLengthDensity, dite_eq_left L.property,
    ENNReal.ofReal_toReal (lengthDensity_valid p n m θ ε L).2]
  rfl

/-- Normalization and integrability of the real density. -/
theorem realLengthDensity_integral (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) :
    Integrable (realLengthDensity p n m θ ε) volume ∧
      (∫ L, realLengthDensity p n m θ ε L) = 1 := by
  have hp : IsProbabilityMeasure
      (volume.withDensity (fun L => ENNReal.ofReal (realLengthDensity p n m θ ε L))) := by
    rw [realLengthDensity_law, ← lengthMeasure_map p n m θ ε]
    have := lengthMeasure_probability p n m θ ε
    infer_instance
  have hn : (∫⁻ L, ENNReal.ofReal (realLengthDensity p n m θ ε L)) = 1 := by
    simpa only [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] using hp.measure_univ
  have hi : Integrable (realLengthDensity p n m θ ε) volume :=
    ⟨(realLengthDensity_measurable p n m θ ε).1.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _
        (realLengthDensity_measurable p n m θ ε).2)).mpr (hn ▸ ENNReal.one_lt_top)⟩
  refine ⟨hi, ?_⟩
  have h := ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ (realLengthDensity_measurable p n m θ ε).2)
  rw [hn] at h
  exact (ENNReal.ofReal_eq_one.mp h)

/-- The real length density has all the finite moments of the actual
sum-image law, with exactly the original active mean and variance. -/
theorem realLengthDensity_moments (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) :
    let μ := volume.withDensity (fun L => ENNReal.ofReal (realLengthDensity p n m θ ε L))
    MemLp (fun L : ℝ => L) 2 μ ∧
      (∫ L, L ∂μ) = ∫ x, ∑ i, x i ∂activeMeasure p n m θ ε ∧
      (∫⁻ L, ENNReal.ofReal ((L - ∫ t, t ∂μ)^2) ∂μ) =
        Riesz1.variance (activeMeasure p n m θ ε) (fun x => ∑ i, x i)
          (memLp_one_iff_integrable.mp (LengthVariance.length_memLp p n m θ ε 1)) := by
  intro μ
  have hsum : Measurable (fun x : EuclideanSpace ℝ (Fin (n+1)) => ∑ i, x i) :=
    (continuous_finsetSum _ fun i _ => PiLp.continuous_apply 2 _ i).measurable
  have hlaw : μ = (activeMeasure p n m θ ε).map (fun x => ∑ i, x i) :=
    realLengthDensity_law p n m θ ε
  have hm : (∫ L, L ∂μ) = ∫ x, ∑ i, x i ∂activeMeasure p n m θ ε := by
    rw [hlaw]
    exact integral_map hsum.aemeasurable (show AEStronglyMeasurable (fun L : ℝ => L) _ from
      measurable_id.aestronglyMeasurable)
  refine ⟨?_, hm, ?_⟩
  · rw [hlaw]
    exact (memLp_map_measure_iff measurable_id.aestronglyMeasurable hsum.aemeasurable).mpr
      (LengthVariance.length_memLp p n m θ ε 2)
  · rw [hm, hlaw]
    exact lintegral_map (show Measurable (fun L : ℝ => ENNReal.ofReal
      ((L - ∫ x, ∑ i, x i ∂activeMeasure p n m θ ε)^2)) from by fun_prop) hsum

/-- A finite real centered moment represents exactly the active
variance. This equality is used before converting extended inequalities. -/
theorem realLengthDensity_variance (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) :
    let μ := volume.withDensity (fun L => ENNReal.ofReal (realLengthDensity p n m θ ε L))
    Riesz1.variance (activeMeasure p n m θ ε) (fun x => ∑ i, x i)
      (memLp_one_iff_integrable.mp (LengthVariance.length_memLp p n m θ ε 1)) =
      ENNReal.ofReal (∫ L, (L - ∫ t, t ∂μ)^2 ∂μ) := by
  intro μ
  obtain ⟨hmem, _, hv⟩ := realLengthDensity_moments p n m θ ε
  have : IsProbabilityMeasure μ := by
    dsimp only [μ]
    rw [realLengthDensity_law, ← lengthMeasure_map p n m θ ε]
    have := lengthMeasure_probability p n m θ ε
    infer_instance
  rw [← hv]
  exact (ofReal_integral_eq_lintegral_ofReal
    (hmem.sub (memLp_const _)).integrable_sq (ae_of_all _ fun _ => sq_nonneg _)).symm

/-- See the proof of Proposition 6.6 in the paper, overlap-mass clause. The loss
is fixed before the tolerance and temperature interval. Both laws are the
canonical physical length laws. Constants are uniform on that interval. -/
theorem overlap_mass_lower (hRig : External.LongRangeRigidityLocallyUniform)
    (hLog : External.ThermodynamicLogConcavity)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ κ εstar : ℝ, 0 < κ ∧ 0 < εstar ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ εstar →
      ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
      ∃ n0 : ℕ, 1 ≤ n0 ∧ ∃ C : ℝ, 0 < C ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ n m m' : ℕ, n0 ≤ n →
        4*(n+1) ≤ n+1+m+1 → 4*(n+1) ≤ n+1+m'+1 →
        (n+1 : ℝ)^(2/s) ≤ ((n+1+m : ℕ)+1 : ℝ) →
        (n+1 : ℝ)^(2/s) ≤ ((n+1+m' : ℕ)+1 : ℝ) →
        C⁻¹*(n+1 : ℝ)^(-κ*ε) ≤ DensityOverlap.mass volume
          (realLengthDensity p n m θ ε) (realLengthDensity p n m' θ ε) := by
  obtain ⟨κv, εstar, hκv, hεstar, hvar⟩ :=
    LengthVariance.length_averaging_variance hRig s hs hs1
  obtain ⟨c0, hc0, hcentral⟩ := hLog
  refine ⟨κv/2, εstar, by positivity, hεstar, fun ε hε hεsmall βlo βhi hlo hle θ => ?_⟩
  obtain ⟨δ, hδ, hb⟩ := hvar ε hε hεsmall
  obtain ⟨A, b, hA, hb0, hb⟩ := hb βlo βhi hlo hle θ
  let τ := min s 1
  have hτ : 0 < τ := lt_min hs zero_lt_one
  let d := c0^2 * Real.sqrt b / Real.sqrt A
  have hd : 0 < d := by dsimp only [d]; positivity
  have hevent : ∀ᶠ n : ℕ in atTop,
      2*A/(c0*Real.sqrt b) ≤ (n+1 : ℝ)^(τ/2) :=
    ((tendsto_rpow_atTop (by positivity : 0 < τ/2)).comp
      ((tendsto_atTop_add_const_right atTop 1
        (tendsto_natCast_atTop_atTop (R := ℝ))))).eventually_ge_atTop _
  obtain ⟨n0, hn0⟩ := eventually_atTop.mp hevent
  refine ⟨max n0 1, le_max_right _ _, d⁻¹, inv_pos.mpr hd,
    fun p hps hpl hph n m m' hn hm hm' hscale hscale' => ?_⟩
  have hn1 : 1 ≤ n := (le_max_right n0 1).trans hn
  have hx : 0 < (n+1 : ℝ) := by positivity
  let lo := Real.sqrt b * (n+1 : ℝ)^(τ/2)
  let hi := Real.sqrt A * (n+1 : ℝ)^((τ+κv*ε)/2)
  have hlo0 : 0 < lo := by dsimp only [lo]; positivity
  have hhi0 : 0 < hi := by dsimp only [hi]; positivity
  have hmean : A ≤ c0*lo/2 := by
    have h := hn0 n ((le_max_left n0 1).trans hn)
    have hden : 0 < c0 * Real.sqrt b := by positivity
    have hh := (div_le_iff₀ hden).mp h
    dsimp only [lo]
    nlinarith
  have one (k : ℕ) (hk : 4*(n+1) ≤ n+1+k+1)
      (hsc : (n+1 : ℝ)^(2/s) ≤ ((n+1+k : ℕ)+1 : ℝ)) :
      ∀ L : ℝ, |L-(n+1 : ℝ)| ≤ c0*lo/2 →
        c0/hi ≤ realLengthDensity p n k θ ε L := by
    let f := realLengthDensity p n k θ ε
    let μ := volume.withDensity (fun L => ENNReal.ofReal (f L))
    let a := ∫ L, L ∂μ
    let v := ∫ L, (L-a)^2 ∂μ
    have hf := realLengthDensity_measurable p n k θ ε
    have hfi := realLengthDensity_integral p n k θ ε
    obtain ⟨hmem, hamean, hvvar⟩ := realLengthDensity_moments p n k θ ε
    have : IsProbabilityMeasure μ := by
      dsimp only [μ, f]
      rw [realLengthDensity_law, ← lengthMeasure_map p n k θ ε]
      have := lengthMeasure_probability p n k θ ε
      infer_instance
    have hv0 : 0 ≤ v := integral_nonneg fun _ => sq_nonneg _
    have hvreal := realLengthDensity_variance p n k θ ε
    have hvint : (∫⁻ L, ENNReal.ofReal ((L-a)^2) ∂μ) = ENNReal.ofReal v :=
      ofReal_integral_eq_lintegral_ofReal
        (hmem.sub (memLp_const _)).integrable_sq (ae_of_all _ fun _ => sq_nonneg _) |>.symm
    obtain ⟨ham, hvl, hvu, _⟩ := hb p hps hpl hph n k hn1 hk hsc
    rw [hvreal] at hvl hvu
    change ENNReal.ofReal (b*(n+1 : ℝ)^τ) ≤ ENNReal.ofReal v at hvl
    change ENNReal.ofReal v ≤ ENNReal.ofReal (A*(n+1 : ℝ)^(τ+κv*ε)) at hvu
    have hvl' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvl
    have hvu' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hvu
    simp only [ENNReal.toReal_ofReal hv0,
      ENNReal.toReal_ofReal (show 0 ≤ b*(n+1 : ℝ)^τ by positivity),
      ENNReal.toReal_ofReal (show 0 ≤ A*(n+1 : ℝ)^(τ+κv*ε) by positivity)] at hvl' hvu'
    have hvpos : 0 < v := (mul_pos hb0 (Real.rpow_pos_of_pos hx τ)).trans_le hvl'
    have hsqrt (B : ℝ) (hB : 0 ≤ B) (r : ℝ) :
        Real.sqrt (B*(n+1 : ℝ)^r) = Real.sqrt B * (n+1 : ℝ)^(r/2) := by
      rw [Real.sqrt_mul hB, Real.sqrt_eq_rpow ((n+1 : ℝ)^r), ← Real.rpow_mul hx.le]
      congr 2
      ring
    have hvlower : lo ≤ Real.sqrt v := by
      simpa only [hsqrt b hb0.le τ] using Real.sqrt_le_sqrt hvl'
    have hvupper : Real.sqrt v ≤ hi := by
      simpa only [hsqrt A hA.le (τ+κv*ε)] using Real.sqrt_le_sqrt hvu'
    have hfn : (∫⁻ L, ENNReal.ofReal (f L)) = 1 := by
      rw [← ofReal_integral_eq_lintegral_ofReal hfi.1 (ae_of_all _ hf.2), hfi.2,
        ENNReal.ofReal_one]
    have hcen := (hcentral f hf.1 hf.2 (realLengthDensity_logConcave p n k θ ε)
      hfn a v (hmem.integrable (by norm_num)) rfl hvpos hvint).1
    have hamean' : |a-(n+1 : ℝ)| ≤ c0*lo/2 := by
      change |(∫ L, L ∂μ)-(n+1 : ℝ)| ≤ _
      rw [hamean]
      apply ham.trans
      apply le_trans _ hmean
      exact mul_le_of_le_one_right hA.le (Real.exp_le_one_iff.mpr (by
        have hp := Real.rpow_nonneg hx.le δ
        nlinarith))
    intro L hL
    have hdist : |L-a| ≤ c0*Real.sqrt v := by
      calc
        |L-a| ≤ |L-(n+1 : ℝ)| + |a-(n+1 : ℝ)| := by
          simpa only [abs_sub_comm] using abs_sub_le L (n+1 : ℝ) a
        _ ≤ c0*lo := by linarith
        _ ≤ _ := mul_le_mul_of_nonneg_left hvlower hc0.le
    exact (div_le_div_of_nonneg_left hc0.le (Real.sqrt_pos.mpr hvpos) hvupper).trans
      (hcen L hdist)
  have hlower := DensityOverlap.mass_lower_of_interval
    (realLengthDensity_integral p n m θ ε).1
    (realLengthDensity_integral p n m' θ ε).1
    (realLengthDensity_measurable p n m θ ε).2
    (realLengthDensity_measurable p n m' θ ε).2
    (show 0 ≤ c0*lo/2 by positivity)
    (fun L hL => ⟨one m hm hscale L hL, one m' hm' hscale' L hL⟩)
  have he : 2*(c0*lo/2)*(c0/hi) = d*(n+1 : ℝ)^(-(κv/2)*ε) := by
    dsimp only [lo, hi, d]
    rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_assoc]
    field_simp
    rw [← Real.rpow_add hx]
    congr 1; ring
  rw [he] at hlower
  simpa only [inv_inv] using hlower

/-- The real coarea law is a probability. -/
theorem realLengthDensity_probability (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) :
    IsProbabilityMeasure (volume.withDensity
      (fun L => ENNReal.ofReal (realLengthDensity p n m θ ε L))) := by
  rw [realLengthDensity_law, ← lengthMeasure_map p n m θ ε]
  have := lengthMeasure_probability p n m θ ε
  infer_instance

/-- See Lemma 6.5 of the paper: the canonical fibre expectation extended by
zero off its carrier, for integration against common length densities. -/
def realAveragedObservable (p : Parameters) (n m : ℕ) (θ : PhysicalCutoff) (ε : ℝ)
    (G : BlockObservable n.succPNat) : ℝ → ℝ :=
  Function.extend (Subtype.val : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ) → ℝ)
    (averagedObservable p n m θ ε G) (fun _ => 0)

/-- The real extension agrees with the every-point fibre integral. -/
theorem realAveragedObservable_apply (p : Parameters) (n m : ℕ) (θ : PhysicalCutoff) (ε : ℝ)
    (G : BlockObservable n.succPNat) (L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ)) :
    realAveragedObservable p n m θ ε G L.val = averagedObservable p n m θ ε G L :=
  Subtype.val_injective.extend_apply _ _ L

/-- Measurability of the zero extension. -/
theorem realAveragedObservable_measurable (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) (G : BlockObservable n.succPNat) :
    Measurable (realAveragedObservable p n m θ ε G) :=
  (MeasurableEmbedding.subtype_coe measurableSet_Ioo).measurable_extend
    (measurable_averagedObservable p n m θ ε G) measurable_const

/-- The finite second moment asserted by length averaging is unchanged
by passing from the coarea carrier to the real length law. -/
theorem realAveragedObservable_memLp (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) (G : BlockObservable n.succPNat)
    (hG : MemLp (averagedObservable p n m θ ε G) 2 (lengthMeasure p n m θ ε)) :
    MemLp (realAveragedObservable p n m θ ε G) 2
      (volume.withDensity (fun L => ENNReal.ofReal (realLengthDensity p n m θ ε L))) := by
  rw [realLengthDensity_law, ← lengthMeasure_map p n m θ ε]
  apply (memLp_map_measure_iff
    (realAveragedObservable_measurable p n m θ ε G).aestronglyMeasurable
    measurable_subtype_coe.aemeasurable).mpr
  simpa only [Function.comp_def, realAveragedObservable_apply] using hG

/-- A block observable has a first moment under the active law. -/
theorem active_observable_integrable (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) (G : BlockObservable n.succPNat) :
    Integrable (fun x => G.val (WithLp.ofLp x)) (activeMeasure p n m θ ε) := by
  let N := (n+1+m).succPNat
  let hn : (n.succPNat : ℕ) ≤ (N : ℕ) := by dsimp [N]; simp; omega
  let μ := tiltedParticleMeasure p N n.succPNat hn θ ε true
  have : IsProbabilityMeasure μ := (InterpolatingDensities.tilt_valid p N n.succPNat hn θ ε true).2.2
  have hg : Measurable (fun x : EuclideanSpace ℝ (Fin (n+1)) => G.val (WithLp.ofLp x)) :=
    G.property.choose_spec.continuous.measurable.comp (WithLp.measurable_ofLp 2 _)
  have hm : Measurable (fun X : Riesz1.Configuration N => WithLp.toLp 2 (finiteGapBlock (K := n.succPNat) X)) :=
    (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.mpr fun i => Riesz1.measurable_gap i.val)
  exact (integrable_map_measure hg.aestronglyMeasurable hm.aemeasurable).mpr
    (InterpolatingDensities.block_integrable N n.succPNat G μ)

/-- See Lemma 6.5 of the paper: the real fibre mean equals the actual active
expectation, with integrability supplied by the finite physical law. -/
theorem realAveragedObservable_mean (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) (G : BlockObservable n.succPNat) :
    (∫ L, realAveragedObservable p n m θ ε G L
      ∂volume.withDensity (fun L => ENNReal.ofReal (realLengthDensity p n m θ ε L))) =
      ∫ x, G.val (WithLp.ofLp x) ∂activeMeasure p n m θ ε := by
  rw [realLengthDensity_law, ← lengthMeasure_map p n m θ ε,
    integral_map measurable_subtype_coe.aemeasurable
      (realAveragedObservable_measurable p n m θ ε G).aestronglyMeasurable]
  simp only [realAveragedObservable_apply]
  exact (integral_disintegration_internal p n m θ ε
    (active_observable_integrable p n m θ ε G)).symm

/-- The real centered second moment is exactly the finite variance in
the length-averaging conclusion, with its canonical fibre representative. -/
theorem realAveragedObservable_variance (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) (G : BlockObservable n.succPNat)
    (hG : MemLp (averagedObservable p n m θ ε G) 2 (lengthMeasure p n m θ ε)) :
    let μ := volume.withDensity (fun L => ENNReal.ofReal (realLengthDensity p n m θ ε L))
    let H := realAveragedObservable p n m θ ε G
    (∫ L, (H L - ∫ t, H t ∂μ)^2 ∂μ) =
      (Riesz1.variance (lengthMeasure p n m θ ε) (averagedObservable p n m θ ε G)
        (by have := lengthMeasure_probability p n m θ ε; exact hG.integrable one_le_two)).toReal := by
  intro μ H
  have := lengthMeasure_probability p n m θ ε
  rw [Riesz1.variance_eq_ofReal_integral_sq _ _ hG,
    ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  have hm : μ = (lengthMeasure p n m θ ε).map Subtype.val := by
    dsimp only [μ]
    rw [realLengthDensity_law, lengthMeasure_map]
  have hmean : (∫ t, H t ∂μ) = ∫ t, averagedObservable p n m θ ε G t ∂lengthMeasure p n m θ ε := by
    rw [hm, integral_map measurable_subtype_coe.aemeasurable
      (realAveragedObservable_measurable p n m θ ε G).aestronglyMeasurable]
    simp only [realAveragedObservable_apply]
  rw [hmean, hm]
  rw [integral_map measurable_subtype_coe.aemeasurable
    (show AEStronglyMeasurable (fun L : ℝ => (H L - ∫ t, averagedObservable p n m θ ε G t
      ∂lengthMeasure p n m θ ε)^2) _ from
      (((realAveragedObservable_measurable p n m θ ε G).sub measurable_const).pow_const 2).aestronglyMeasurable)]
  simp only [H, realAveragedObservable_apply]

/-- At admissible volumes the fine active event is independent of the
volume cutoff. This permits the same good-set derivative norm in
both length-averaging estimates. -/
theorem goodBlockEvent_volume_independent (s η : ℝ) (n N M : ℕ+)
    (hη : η + min s 1 / 2 ≤ 1)
    (hN : 4*(n : ℕ) ≤ (N : ℕ)) (hM : 4*(n : ℕ) ≤ (M : ℕ)) :
    goodBlockEvent s n N η = goodBlockEvent s n M η := by
  have hsum (x : Fin (n : ℕ) → ℝ)
      (hx : ∀ a b : ℕ, a < b → b ≤ (n : ℕ) →
        |(∑ i ∈ Finset.univ.filter (fun i : Fin (n : ℕ) => a ≤ i.val ∧ i.val < b), x i) -
          (b-a : ℕ)| ≤ (n : ℝ)^η*(b-a : ℕ)^(min s 1/2)) :
      (∑ i, x i) ≤ 2*(n : ℝ) := by
    have h := hx 0 n n.pos le_rfl
    simp only [Nat.zero_le, true_and, Fin.is_lt, Finset.filter_true,
      Nat.sub_zero] at h
    have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ (n : ℕ) from n.property)
    have hpow : (n : ℝ)^η*(n : ℝ)^(min s 1/2) ≤ (n : ℝ) := by
      rw [← Real.rpow_add (by exact_mod_cast n.pos)]
      exact (Real.rpow_le_rpow_of_exponent_le hn1 hη).trans_eq (Real.rpow_one _)
    have hh := (le_abs_self ((∑ i, x i)-(n : ℝ))).trans (h.trans hpow)
    linarith
  have hcut (L : ℕ+) (hL : 4*(n : ℕ) ≤ (L : ℕ)) (x : Fin (n : ℕ) → ℝ)
      (hx : x ∈ goodBlockEvent s n L η) : (∑ i, x i) ≤ 2*(n : ℝ) :=
    hsum x hx.2.2
  ext x
  constructor
  · intro hx
    refine ⟨?_, hx.2⟩
    have h := hcut N hN x hx
    have hc : 4*(n : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast n.pos
    linarith
  · intro hx
    refine ⟨?_, hx.2⟩
    have h := hcut M hM x hx
    have hc : 4*(n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast n.pos
    linarith

/-- See the proof of Proposition 6.6 in the paper, internal Cauchy--Schwarz
step. The variance inputs here are precisely those supplied by length
averaging, on the literal coarea carrier. -/
theorem averaging_overlap_transfer_internal (p : Parameters) (n m m' : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) (G : BlockObservable n.succPNat)
    (hG : MemLp (averagedObservable p n m θ ε G) 2 (lengthMeasure p n m θ ε))
    (hG' : MemLp (averagedObservable p n m' θ ε G) 2 (lengthMeasure p n m' θ ε))
    (ha : 0 < DensityOverlap.mass volume (realLengthDensity p n m θ ε)
      (realLengthDensity p n m' θ ε)) :
    let ρ := volume.withDensity (fun L => ENNReal.ofReal
      (DensityOverlap.density volume (realLengthDensity p n m θ ε) (realLengthDensity p n m' θ ε) ha L))
    |(∫ L, realAveragedObservable p n m θ ε G L ∂ρ) -
      ∫ x, G.val (WithLp.ofLp x) ∂activeMeasure p n m θ ε| +
    |(∫ L, realAveragedObservable p n m' θ ε G L ∂ρ) -
      ∫ x, G.val (WithLp.ofLp x) ∂activeMeasure p n m' θ ε| ≤
      Real.sqrt (DensityOverlap.mass volume (realLengthDensity p n m θ ε)
        (realLengthDensity p n m' θ ε))⁻¹ *
      (Real.sqrt ((Riesz1.variance (lengthMeasure p n m θ ε)
        (averagedObservable p n m θ ε G)
        (by have := lengthMeasure_probability p n m θ ε; exact hG.integrable one_le_two)).toReal) +
      Real.sqrt ((Riesz1.variance (lengthMeasure p n m' θ ε)
        (averagedObservable p n m' θ ε G)
        (by have := lengthMeasure_probability p n m' θ ε; exact hG'.integrable one_le_two)).toReal)) := by
  intro ρ
  have := realLengthDensity_probability p n m θ ε
  have := realLengthDensity_probability p n m' θ ε
  have h := DensityOverlap.pair_mean_sub_le volume
    (realLengthDensity_measurable p n m θ ε).1
    (realLengthDensity_measurable p n m' θ ε).1
    (realLengthDensity_integral p n m θ ε).1
    (realLengthDensity_integral p n m' θ ε).1
    (realLengthDensity_measurable p n m θ ε).2
    (realLengthDensity_measurable p n m' θ ε).2 ha
    (realAveragedObservable_memLp p n m θ ε G hG)
    (realAveragedObservable_memLp p n m' θ ε G hG')
  dsimp only at h
  rw [realAveragedObservable_variance p n m θ ε G hG,
    realAveragedObservable_variance p n m' θ ε G hG',
    realAveragedObservable_mean p n m θ ε G,
    realAveragedObservable_mean p n m' θ ε G] at h
  exact h

/-- The common length law in the proof of Proposition 6.6 follows from
Lemma 6.5. The conclusion includes the minimum density, its normalization,
both domination bounds and the sum of averaging errors.
Lean `n,m,m'` mean `n+1` active gaps and `m+1,m'+1` exterior gaps. -/
theorem distinct_overlap_from_averaging_internal
    (hRig : External.LongRangeRigidityLocallyUniform)
    (hLog : External.ThermodynamicLogConcavity)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) (K : ℝ) (hK : 1 < K)
    (hAveraging : ∃ κ εstar : ℝ, 0 < κ ∧ 0 < εstar ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ εstar → ∃ δ : ℝ, 0 < δ ∧
      ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
        ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
          ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
          ∀ n m : ℕ, 1 ≤ n → 4*(n+1) ≤ n+1+m+1 →
            (n+1 : ℝ)^(2/s) ≤ ((n+1+m : ℕ)+1 : ℝ) →
          let ν := activeMeasure p n m θ ε
          let V := Riesz1.variance ν (fun x => ∑ i, x i)
            (memLp_one_iff_integrable.mp (LengthVariance.length_memLp p n m θ ε 1))
          |(∫ x, ∑ i, x i ∂ν)-(n+1 : ℝ)| ≤ C*Real.exp (-c*(n+1 : ℝ)^δ) ∧
            ENNReal.ofReal (c*(n+1 : ℝ)^(min s 1)) ≤ V ∧
            V ≤ ENNReal.ofReal (C*(n+1 : ℝ)^(min s 1+κ*ε)) ∧
          ∀ G : BlockObservable n.succPNat, ∀ J : Finset (Fin (n+1)),
            DependsOnBlockCoordinates G J →
            (∀ i ∈ J, |(i.val : ℝ)+1-(n+1 : ℝ)/2| ≤ (n+1 : ℝ)/4) →
          ∃ hG : MemLp (averagedObservable p n m θ ε G) 2 (lengthMeasure p n m θ ε),
            Real.sqrt ((Riesz1.variance (lengthMeasure p n m θ ε)
              (averagedObservable p n m θ ε G)
              (by have := lengthMeasure_probability p n m θ ε; exact hG.integrable one_le_two)).toReal) ≤
              C*(n+1 : ℝ)^(κ*ε-min s 1/2)*restrictedBlockDerivativeNorm G J
                (goodBlockEvent s n.succPNat (n+1+m).succPNat (K*ε)) +
              C*Real.exp (-c*(n+1 : ℝ)^δ)*blockDerivativeNorm G) :
    ∃ κ εstar : ℝ, 0 < κ ∧ 0 < εstar ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ εstar → ∃ δ : ℝ, 0 < δ ∧
      ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
      ∃ n0 : ℕ, 1 ≤ n0 ∧ ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ n m m' : ℕ, n0 ≤ n → m ≤ m' → 4*(n+1) ≤ n+1+m+1 →
        (n+1 : ℝ)^(2/s) ≤ ((n+1+m : ℕ)+1 : ℝ) →
      let f := realLengthDensity p n m θ ε
      let f' := realLengthDensity p n m' θ ε
      let a0 := DensityOverlap.mass volume f f'
      let ρ := fun L => min (f L) (f' L) / a0
      let μρ := volume.withDensity (fun L => ENNReal.ofReal (ρ L))
      C⁻¹*(n+1 : ℝ)^(-κ*ε) ≤ a0 ∧ 0 < a0 ∧
        Measurable ρ ∧ (∀ L, 0 ≤ ρ L) ∧ (∫ L, ρ L) = 1 ∧
        (∀ L, ρ L ≤ a0⁻¹*f L) ∧ (∀ L, ρ L ≤ a0⁻¹*f' L) ∧
      ∀ G : BlockObservable n.succPNat, ∀ J : Finset (Fin (n+1)),
        DependsOnBlockCoordinates G J →
        (∀ i ∈ J, |(i.val : ℝ)+1-(n+1 : ℝ)/2| ≤ (n+1 : ℝ)/4) →
        Integrable (realAveragedObservable p n m θ ε G) μρ ∧
        Integrable (realAveragedObservable p n m' θ ε G) μρ ∧
        |(∫ L, realAveragedObservable p n m θ ε G L ∂μρ) -
          ∫ x, G.val (WithLp.ofLp x) ∂activeMeasure p n m θ ε| +
        |(∫ L, realAveragedObservable p n m' θ ε G L ∂μρ) -
          ∫ x, G.val (WithLp.ofLp x) ∂activeMeasure p n m' θ ε| ≤
          C*(n+1 : ℝ)^(κ*ε-min s 1/2)*restrictedBlockDerivativeNorm G J
            (goodBlockEvent s n.succPNat (n+1+m).succPNat (K*ε)) +
          C*Real.exp (-c*(n+1 : ℝ)^δ)*blockDerivativeNorm G := by
  obtain ⟨κo, εo, hκo, hεo, hO⟩ := overlap_mass_lower hRig hLog s hs hs1
  obtain ⟨κa, εa, hκa, hεa, hA⟩ := hAveraging
  have hK0 : 0 < K := zero_lt_one.trans hK
  let εstar := min εa (min εo (1/(2*K)))
  have hεstar : 0 < εstar := lt_min hεa (lt_min hεo (by positivity))
  refine ⟨κa+κo, εstar, add_pos hκa hκo, hεstar, fun ε hε hεsmall => ?_⟩
  have hεa' : ε ≤ εa := hεsmall.trans (min_le_left _ _)
  have hεo' : ε ≤ εo := hεsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεK : K*ε + min s 1/2 ≤ 1 := by
    have he := hεsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hh := (le_div_iff₀ (show 0 < 2*K by positivity)).mp he
    have hsmin := min_le_right s (1 : ℝ)
    nlinarith
  obtain ⟨δ, hδ, hAb⟩ := hA ε hε hεa'
  refine ⟨δ, hδ, fun βlo βhi hlo hle θ => ?_⟩
  obtain ⟨n0, hn0, B, hB, hOb⟩ := hO ε hε hεo' βlo βhi hlo hle θ
  obtain ⟨A, a, hA0, ha0, hAb⟩ := hAb βlo βhi hlo hle θ
  obtain ⟨Q, hQ, hQb⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := κo*ε/2) hδ (show a/2 < a by linarith)
  let D := 2*Real.sqrt B*A*(1+Q)
  have hD : 0 < D := by dsimp only [D]; positivity
  let C := B+D
  have hC : 0 < C := add_pos hB hD
  have hBC : B ≤ C := le_add_of_nonneg_right hD.le
  have hDC : D ≤ C := le_add_of_nonneg_left hB.le
  refine ⟨n0, hn0, C, a/2, hC, by positivity,
    fun p hps hpl hph n m m' hn hmm' hsize hscale => ?_⟩
  intro f f' a0 ρ μρ
  have hn1 : 1 ≤ n := hn0.trans hn
  have hx : 1 ≤ (n+1 : ℝ) := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hsize' : 4*(n+1) ≤ n+1+m'+1 := by omega
  have hscale' : (n+1 : ℝ)^(2/s) ≤ ((n+1+m' : ℕ)+1 : ℝ) :=
    hscale.trans (by exact_mod_cast (show n+1+m+1 ≤ n+1+m'+1 by omega))
  have hlower := hOb p hps hpl hph n m m' hn hsize hsize' hscale hscale'
  have ha0' : 0 < a0 :=
    (mul_pos (inv_pos.mpr hB) (Real.rpow_pos_of_pos (by positivity) _)).trans_le hlower
  obtain ⟨_hiρ, hρ0, hρn, hρf, hρf'⟩ := DensityOverlap.density_properties volume
    (realLengthDensity_integral p n m θ ε).1 (realLengthDensity_integral p n m' θ ε).1
    (realLengthDensity_measurable p n m θ ε).2
    (realLengthDensity_measurable p n m' θ ε).2 ha0'
  have hρm : Measurable ρ :=
    ((realLengthDensity_measurable p n m θ ε).1.min
      (realLengthDensity_measurable p n m' θ ε).1).div_const _
  refine ⟨?_, ha0', hρm, hρ0, hρn, hρf, hρf', fun G J hJ hmiddle => ?_⟩
  · apply le_trans _ hlower
    apply mul_le_mul
    · simpa only [one_div] using one_div_le_one_div_of_le hB hBC
    · exact Real.rpow_le_rpow_of_exponent_le hx (by nlinarith)
    · positivity
    · exact (inv_pos.mpr hB).le
  · have hevent := goodBlockEvent_volume_independent s (K*ε) n.succPNat
      (n+1+m).succPNat (n+1+m').succPNat hεK hsize hsize'
    obtain ⟨_, _, _, hAbG⟩ := hAb p hps hpl hph n m hn1 hsize hscale
    obtain ⟨_, _, _, hAbG'⟩ := hAb p hps hpl hph n m' hn1 hsize' hscale'
    obtain ⟨hG, hGb⟩ := hAbG G J hJ hmiddle
    obtain ⟨hG', hGb'⟩ := hAbG' G J hJ hmiddle
    rw [← hevent] at hGb'
    have : IsProbabilityMeasure μρ := DensityOverlap.probability volume
      (realLengthDensity_integral p n m θ ε).1 (realLengthDensity_integral p n m' θ ε).1
      (realLengthDensity_measurable p n m θ ε).2
      (realLengthDensity_measurable p n m' θ ε).2 ha0'
    have hdom := DensityOverlap.measure_le_left volume
      (realLengthDensity_measurable p n m θ ε).1
      (realLengthDensity_measurable p n m' θ ε).1 ha0'
    have hdom' : μρ ≤ ENNReal.ofReal a0⁻¹ •
        volume.withDensity (fun L => ENNReal.ofReal (f' L)) := by
      rw [← withDensity_smul _ (realLengthDensity_measurable p n m' θ ε).1.ennreal_ofReal]
      apply withDensity_mono
      apply ae_of_all
      intro L
      change ENNReal.ofReal (ρ L) ≤ ENNReal.ofReal a0⁻¹ * ENNReal.ofReal (f' L)
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr ha0'.le)]
      exact ENNReal.ofReal_le_ofReal (hρf' L)
    have hi := (realAveragedObservable_memLp p n m θ ε G hG).of_measure_le_smul
      ENNReal.ofReal_ne_top hdom
    have hi' := (realAveragedObservable_memLp p n m' θ ε G hG').of_measure_le_smul
      ENNReal.ofReal_ne_top hdom'
    change MemLp (realAveragedObservable p n m θ ε G) 2 μρ at hi
    change MemLp (realAveragedObservable p n m' θ ε G) 2 μρ at hi'
    refine ⟨hi.integrable one_le_two, hi'.integrable one_le_two, ?_⟩
    have htransfer := averaging_overlap_transfer_internal p n m m' θ ε G hG hG' ha0'
    have hDA : 0 ≤ restrictedBlockDerivativeNorm G J
        (goodBlockEvent s n.succPNat (n+1+m).succPNat (K*ε)) := by
      unfold restrictedBlockDerivativeNorm; positivity
    have hDB : 0 ≤ blockDerivativeNorm G := by unfold blockDerivativeNorm; positivity
    have hr := DensityOverlap.averaging_rate_internal hx hε hκo hA0 hB hQ hDA hDB
      ha0' hlower htransfer hGb hGb' (hQb (n+1 : ℝ) hx)
    apply hr.trans
    exact add_le_add
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDC (by positivity)) hDA)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hDC (Real.exp_pos _).le) hDB)

end Riesz2.LengthOverlap
