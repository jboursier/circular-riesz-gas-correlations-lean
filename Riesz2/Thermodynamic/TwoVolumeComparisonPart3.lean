/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.TwoVolumeComparison
public import Riesz2.Thermodynamic.LengthAveragingFinal
public import Riesz2.Thermodynamic.InterpolantLocalLawsPart10
public import Riesz2.ToMathlib.CommonBaseKernelMoments
public import Riesz2.ToMathlib.ComparisonRates

/-!
# Moments, rounding, and remainder estimates for two-volume comparison

Supporting steps for Proposition 6.6. These estimates use the block observable and its
coordinate constants literally. The rounding lemmas distinguish exact middle-half
support from the larger support required by the final comparison.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Riesz2.TwoVolumeComparison

/-- See Proposition 6.6 of the paper: outside the exceptional rounding case,
the support satisfies the exact middle-half hypothesis of the length-averaging and compatible-comparison interfaces. -/
theorem symmetricMiddleBlock_middle_half (n : ℕ+) (K : ℕ) (hK : K ≤ (n : ℕ) / 4)
    (hround : (n : ℕ) % 4 ≠ 1 ∨ K < (n : ℕ) / 4)
    (i : Fin (n : ℕ)) (hi : i ∈ symmetricMiddleBlock n K) :
    |(i.val : ℝ) + 1 - (n : ℝ) / 2| ≤ (n : ℝ) / 4 := by
  simp only [symmetricMiddleBlock, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  have hlo : (n : ℕ) ≤ 4 * (i.val + 1) := by omega
  have hhi : 4 * (i.val + 1) ≤ 3 * (n : ℕ) := by omega
  have hlo' : (n : ℝ) ≤ 4 * ((i.val : ℝ) + 1) := by exact_mod_cast hlo
  have hhi' : 4 * ((i.val : ℝ) + 1) ≤ 3 * (n : ℝ) := by exact_mod_cast hhi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- See Proposition 6.6 of the paper: the problematic rounding case occurs
at arbitrarily large sizes. Its left endpoint is outside the exact middle
half, while it remains in the support. -/
theorem symmetricMiddleBlock_rounding_obstruction (m : ℕ) (hm : 1 ≤ m) :
    let n : ℕ+ := ⟨4 * m + 1, by omega⟩
    let i : Fin (n : ℕ) := ⟨m - 1, by dsimp [n]; omega⟩
    m ≤ (n : ℕ) / 4 ∧ i ∈ symmetricMiddleBlock n m ∧
      ¬ |(i.val : ℝ) + 1 - (n : ℝ) / 2| ≤ (n : ℝ) / 4 := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · change m ≤ (4 * m + 1) / 4
    omega
  · simp only [symmetricMiddleBlock, Finset.mem_filter, Finset.mem_univ, true_and]
    change (4*m+1)/2 ≤ (m-1)+1+m ∧ (m-1)+1 ≤ (4*m+1)/2+m
    omega
  · change ¬ |((m - 1 : ℕ) : ℝ) + 1 - ((4*m+1 : ℕ) : ℝ)/2| ≤
      ((4*m+1 : ℕ) : ℝ)/4
    have he : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
      exact_mod_cast (show m - 1 + 1 = m by omega)
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rw [he]
    intro hh
    have hl := (abs_le.mp hh).1
    linarith

/-- See Proposition 6.6 of the paper: the second moment of a centered block
observable is controlled by coordinate second moments with no factor of
the number of active or support coordinates. -/
theorem centered_block_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ+) (G : BlockObservable n)
    (x : Ω → Fin (n : ℕ) → ℝ) (hx : Measurable x) (M : ℝ) (_hM : 0 ≤ M)
    (hm : ∀ i, Integrable (fun ω => (x ω i - 1) ^ 2) μ ∧
      (∫ ω, (x ω i - 1) ^ 2 ∂μ) ≤ M) :
    Integrable (fun ω => (G.val (x ω) - G.val (fun _ => 1)) ^ 2) μ ∧
      (∫ ω, (G.val (x ω) - G.val (fun _ => 1)) ^ 2 ∂μ) ≤
        M * blockDerivativeNorm G ^ 2 := by
  classical
  let a := fun i => (coordinateDerivativeNorm G i : ℝ)
  have ha (i) : 0 ≤ a i := NNReal.coe_nonneg _
  have hD : (∑ i, a i) = blockDerivativeNorm G := rfl
  have hD0 : 0 ≤ blockDerivativeNorm G := hD ▸ Finset.sum_nonneg (fun i _ => ha i)
  let H := fun ω => blockDerivativeNorm G * ∑ i, a i * (x ω i - 1) ^ 2
  have hHi : Integrable H μ :=
    (integrable_finsetSum _ (fun i _ => (hm i).1.const_mul (a i))).const_mul _
  have hpoint (ω : Ω) : (G.val (x ω) - G.val (fun _ => 1)) ^ 2 ≤ H ω := by
    have hb := InterpolatingDensities.block_bound G (fun _ => 1) (x ω)
    have hs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s := Finset.univ)
      (f := a) (g := fun i => a i * (x ω i - 1) ^ 2)
      (r := fun i => a i * |x ω i - 1|)
      (fun i _ => ha i) (fun i _ => mul_nonneg (ha i) (sq_nonneg _))
      (fun i _ => by rw [mul_pow, sq_abs]; ring_nf; exact le_rfl)
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hb 2
    rw [sq_abs] at hsq
    exact hsq.trans (by simpa only [H, hD] using hs)
  have hGm : Measurable (fun ω => (G.val (x ω) - G.val (fun _ => 1)) ^ 2) :=
    (((G.property.choose_spec.continuous.measurable.comp hx).sub_const _).pow_const 2)
  have hi : Integrable (fun ω => (G.val (x ω) - G.val (fun _ => 1)) ^ 2) μ :=
    hHi.mono' hGm.aestronglyMeasurable (ae_of_all μ fun ω => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hpoint ω)
  refine ⟨hi, (integral_mono hi hHi hpoint).trans ?_⟩
  calc
    (∫ ω, H ω ∂μ) = blockDerivativeNorm G * ∑ i, a i * ∫ ω, (x ω i - 1) ^ 2 ∂μ := by
      rw [integral_const_mul, integral_finsetSum]
      · simp only [integral_const_mul]
      · exact fun i _ => (hm i).1.const_mul (a i)
    _ ≤ blockDerivativeNorm G * ∑ i, a i * M := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hm i).2 (ha i)) hD0
    _ = M * blockDerivativeNorm G ^ 2 := by rw [← Finset.sum_mul, hD]; ring

/-- See Proposition 6.6 of the paper: centered block second moments under
both original tilted laws are uniform in the ambient volume and the block
size. The coefficient is the square of the global derivative sum. -/
theorem compact_centered_block_second_moment (s ε βlo βhi : ℝ)
    (hs : 0 < s) (hs1 : s ≠ 1) (hε : 0 < ε)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (θ : PhysicalCutoff) :
    ∃ H : ℝ, 0 < H ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ N n : ℕ+, 2 ≤ (N : ℕ) →
      ∀ hn : (n : ℕ) ≤ (N : ℕ), ∀ G : BlockObservable n,
      let μ := tiltedParticleMeasure p N n hn θ ε true
      Integrable (fun X => (G.val (finiteGapBlock X) - G.val (fun _ => 1)) ^ 2) μ ∧
        (∫⁻ X, ENNReal.ofReal ((G.val (finiteGapBlock X) - G.val (fun _ => 1)) ^ 2) ∂μ) ≤
          ENNReal.ofReal (H * blockDerivativeNorm G ^ 2) := by
  obtain ⟨M, hM, hm⟩ := InterpolantLocalLaws.compact_tilted_gap_moments
    s ε βlo βhi hs hs1 hε hlo hle θ 2 (by norm_num)
  refine ⟨2*M+2, by positivity, fun p hps hpl hph N n hN hn G => ?_⟩
  let μ := tiltedParticleMeasure p N n hn θ ε true
  have : IsProbabilityMeasure μ := (InterpolatingDensities.tilt_valid p N n hn θ ε true).2.2
  have hcoord (i : Fin (n : ℕ)) : Integrable (fun X => (gap X i.val - 1) ^ 2) μ ∧
      (∫ X, (gap X i.val - 1) ^ 2 ∂μ) ≤ 2*M+2 := by
    have hb := (le_add_right (le_refl _)).trans (hm p hps hpl hph N n hN hn i.val)
    obtain ⟨hi, hb'⟩ := MomentEvent.integrable_rpow_abs_and_integral_le_of_lintegral_le
      (μ := μ) (p := 2) (f := fun X : Riesz1.Configuration N => gap X i.val)
      (Riesz1.measurable_gap i.val) hM.le (by
        simpa only [Real.rpow_two, sq_abs] using hb)
    simp only [Real.rpow_two, sq_abs] at hi hb'
    have hdom : Integrable (fun X => 2 * gap X i.val ^ 2 + 2) μ :=
      (hi.const_mul 2).add (integrable_const 2)
    have hsub : Integrable (fun X => (gap X i.val - 1) ^ 2) μ :=
      hdom.mono' (((Riesz1.measurable_gap i.val).sub_const 1).pow_const 2).aestronglyMeasurable
        (ae_of_all μ fun X => by
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          nlinarith [sq_nonneg (gap X i.val + 1)])
    refine ⟨hsub, (integral_mono hsub hdom (fun X => by
      nlinarith [sq_nonneg (gap X i.val + 1)])).trans ?_⟩
    rw [integral_add (hi.const_mul 2) (integrable_const 2), integral_const_mul,
      integral_const, probReal_univ, smul_eq_mul, one_mul]
    linarith
  obtain ⟨hi, hb⟩ := centered_block_second_moment μ n G
    (fun X => finiteGapBlock X) (Measurable.of_eval fun i => Riesz1.measurable_gap i.val)
    (2*M+2) (by positivity) hcoord
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all μ fun _ => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hb

/-- See Proposition 6.6 of the paper: all bounded active sizes satisfy the
final form of the comparison estimate directly. The prefactor is uniform
in the ambient volumes and in a compact positive temperature interval.
Neither an overlap assertion at small sizes nor a sign for `q` is needed. -/
theorem bounded_sizes_comparison_internal (s ε βlo βhi q c δ η : ℝ)
    (hs : 0 < s) (hs1 : s ≠ 1) (hε : 0 < ε)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (θ : PhysicalCutoff) (n₀ : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ N N' n : ℕ+,
      2 ≤ (N : ℕ) → 2 ≤ (N' : ℕ) → (n : ℕ) ≤ n₀ →
      ∀ (hn : (n : ℕ) ≤ (N : ℕ)) (hn' : (n : ℕ) ≤ (N' : ℕ)),
      ∀ (G : BlockObservable n) (J : Finset (Fin (n : ℕ))),
      |(∫ X, G.val (finiteGapBlock X) ∂tiltedParticleMeasure p N n hn θ ε true) -
        (∫ X, G.val (finiteGapBlock X) ∂tiltedParticleMeasure p N' n hn' θ ε true)| ≤
          C * (n : ℝ)^q * (restrictedBlockDerivativeNorm G J (goodBlockEvent s n N η) +
            Real.exp (-c*(n : ℝ)^δ)*blockDerivativeNorm G) := by
  obtain ⟨B, _hB, hb⟩ := compact_global_comparison s ε βlo βhi hs hs1 hε hlo hle θ
  obtain ⟨C, hC, hc⟩ := ComparisonRates.bounded_sizes_remainder n₀ B q c δ
  refine ⟨C, hC, fun p hps hpl hph N N' n hN hN' hn₀ hn hn' G J => ?_⟩
  have hD : 0 ≤ blockDerivativeNorm G := Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _
  have hA : 0 ≤ restrictedBlockDerivativeNorm G J (goodBlockEvent s n N η) :=
    Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _
  calc
    _ ≤ B * blockDerivativeNorm G := hb p hps hpl hph N N' n hN hN' hn hn' G
    _ ≤ (C*(n : ℝ)^q*Real.exp (-c*(n : ℝ)^δ))*blockDerivativeNorm G :=
      mul_le_mul_of_nonneg_right (hc n n.pos hn₀) hD
    _ ≤ _ := by
      have hh : 0 ≤ C*(n : ℝ)^q*restrictedBlockDerivativeNorm G J (goodBlockEvent s n N η) :=
        mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _)) hA
      nlinarith only [hh]

/-- See Proposition 6.6 of the paper: the actual fixed-exterior centered
active expectations have uniformly bounded second moment under the original
exterior law. Jensen is applied to the literal simplex conditional kernel. -/
theorem compact_conditional_centered_second_moment (s ε βlo βhi : ℝ)
    (hs : 0 < s) (hs1 : s ≠ 1) (hε : 0 < ε)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (θ : PhysicalCutoff) :
    ∃ H : ℝ, 0 < H ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ d a : ℕ, ∀ hd : 1 ≤ d,
      ∀ G : BlockObservable a.succPNat,
      let h : a+1 ≤ d+a+1 := by omega
      let σ := InterpolatingDensities.exteriorPermutation d a
      let ha := Real.rpow_pos_of_pos (show (0 : ℝ) < (a+1 : ℕ) by positivity) (-ε)
      let J := Finset.univ.map (Fin.castLEEmb h)
      let κ := InterpolatingDensities.simplexFibreKernel p d a hd σ θ ha J true
      let F := fun y => ∫ u, (G.val (WithLp.ofLp u) - G.val (fun _ => 1)) ∂κ y
      Measurable F ∧
        (∫⁻ y, ENNReal.ofReal (F y ^ 2) ∂InterpolantLocalLaws.physicalExteriorLaw p d a θ ε) ≤
          ENNReal.ofReal (H * blockDerivativeNorm G ^ 2) := by
  obtain ⟨H, hH, hbound⟩ := compact_centered_block_second_moment
    s ε βlo βhi hs hs1 hε hlo hle θ
  refine ⟨H, hH, fun p hps hpl hph d a hd G => ?_⟩
  intro h σ ha J κ F
  let f := fun u : EuclideanSpace ℝ (Fin (a+1)) =>
    G.val (WithLp.ofLp u) - G.val (fun _ => 1)
  have hf : Measurable f :=
    ((G.property.choose_spec.continuous.measurable.comp (WithLp.measurable_ofLp 2 _)).sub_const _)
  refine ⟨hf.stronglyMeasurable.integral_kernel.measurable, ?_⟩
  have hJensen := CommonBaseKernel.conditional_average_second_moment κ
    (InterpolantLocalLaws.physicalExteriorLaw p d a θ ε) f hf
  have hdis := (InterpolantLocalLaws.physical_exterior_disintegration p d a hd θ ε).2
    (fun q => ENNReal.ofReal (f q.2 ^ 2)) (((hf.comp measurable_snd).pow_const 2).ennreal_ofReal)
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) ((hf.pow_const 2).ennreal_ofReal).aemeasurable]
    at hJensen
  apply hJensen.trans
  rw [← hdis]
  have hb := (hbound p hps hpl hph (d+a).succPNat a.succPNat
    (by change 2 ≤ d+a+1; omega) h G).2
  simpa only [f, WithLp.ofLp_toLp] using hb

/-- See Proposition 6.6 of the paper: application of the overlap
theorem to the rounded support whenever it is contained in the
exact middle half. The excluded case is identified by
`symmetricMiddleBlock_rounding_obstruction`. -/
theorem rounded_overlap_internal
    (hz : External.PeriodicZeta) (hRig : External.LongRangeRigidityLocallyUniform)
    (hLog : External.ThermodynamicLogConcavity)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ κ εstar : ℝ, 0 < κ ∧ 0 < εstar ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ εstar → ∃ δ : ℝ, 0 < δ ∧
      ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
      ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ n m m' : ℕ, n₀ ≤ n → m ≤ m' → 4*(n+1) ≤ n+1+m+1 →
        (n+1 : ℝ)^(2/s) ≤ ((n+1+m : ℕ)+1 : ℝ) →
      let f := LengthOverlap.realLengthDensity p n m θ ε
      let f' := LengthOverlap.realLengthDensity p n m' θ ε
      let a₀ := DensityOverlap.mass volume f f'
      let ρ := fun L => min (f L) (f' L) / a₀
      let μρ := volume.withDensity (fun L => ENNReal.ofReal (ρ L))
      C⁻¹*(n+1 : ℝ)^(-κ*ε) ≤ a₀ ∧ 0 < a₀ ∧
        Measurable ρ ∧ (∀ L, 0 ≤ ρ L) ∧ (∫ L, ρ L) = 1 ∧
        (∀ L, ρ L ≤ a₀⁻¹*f L) ∧ (∀ L, ρ L ≤ a₀⁻¹*f' L) ∧
      ∀ K : ℕ, K ≤ (n+1)/4 → ((n+1)%4 ≠ 1 ∨ K < (n+1)/4) →
      ∀ G : BlockObservable n.succPNat,
        DependsOnBlockCoordinates G (symmetricMiddleBlock n.succPNat K) →
        Integrable (LengthOverlap.realAveragedObservable p n m θ ε G) μρ ∧
        Integrable (LengthOverlap.realAveragedObservable p n m' θ ε G) μρ ∧
        |(∫ L, LengthOverlap.realAveragedObservable p n m θ ε G L ∂μρ) -
          ∫ x, G.val (WithLp.ofLp x) ∂LengthAveragingFibres.activeMeasure p n m θ ε| +
        |(∫ L, LengthOverlap.realAveragedObservable p n m' θ ε G L ∂μρ) -
          ∫ x, G.val (WithLp.ofLp x) ∂LengthAveragingFibres.activeMeasure p n m' θ ε| ≤
          C*(n+1 : ℝ)^(κ*ε-min s 1/2)*
            restrictedBlockDerivativeNorm G (symmetricMiddleBlock n.succPNat K)
              (goodBlockEvent s n.succPNat (n+1+m).succPNat (2*ε)) +
          C*Real.exp (-c*(n+1 : ℝ)^δ)*blockDerivativeNorm G := by
  obtain ⟨κ, εstar, hκ, hεstar, hε⟩ := LengthOverlap.distinct_overlap hz hRig hLog s hs hs1
  refine ⟨κ, εstar, hκ, hεstar, fun ε hεpos hεle => ?_⟩
  obtain ⟨δ, hδ, h⟩ := hε ε hεpos hεle
  refine ⟨δ, hδ, fun βlo βhi hlo hle θ => ?_⟩
  obtain ⟨n₀, hn₀, C, c, hC, hc, hb⟩ := h βlo βhi hlo hle θ
  refine ⟨n₀, hn₀, C, c, hC, hc, fun p hps hpl hph n m m' hn hmm' h4 hpow => ?_⟩
  obtain ⟨hlower, hpos, hmeas, hnonneg, hone, hdom, hdom', hobs⟩ :=
    hb p hps hpl hph n m m' hn hmm' h4 hpow
  refine ⟨hlower, hpos, hmeas, hnonneg, hone, hdom, hdom', fun K hK hround G hG => ?_⟩
  exact hobs G (symmetricMiddleBlock n.succPNat K) hG
    (fun i hi => by
      simpa only [Nat.succPNat_coe, Nat.cast_succ] using
        symmetricMiddleBlock_middle_half n.succPNat K hK hround i hi)

/-- See Proposition 6.6 of the paper: specialize the common-base union
bound to the literal admissibility events and the physical exterior
tail theorem. The only kernel identities required are the two original-law
mixture identities. The density-domination factor is explicit. -/
theorem common_base_admissibility_tail_internal
    (hRig : External.LongRangeRigidityLocallyUniform)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) (A : ℝ) (hA : 1 < A) :
    ∃ K ε₀ : ℝ, 1 < K ∧ 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
      ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ d e a : ℕ, ∀ (hd : 1 ≤ d) (he : 1 ≤ e), 1 ≤ a →
        4*(a+1) ≤ d+a+1 → 4*(a+1) ≤ e+a+1 →
        (a+1 : ℝ)^(2/s) ≤ ((d+a : ℕ)+1 : ℝ) →
        (a+1 : ℝ)^(2/s) ≤ ((e+a : ℕ)+1 : ℝ) →
      ∀ {L : Type} [MeasurableSpace L]
        (κ : Kernel L (AffineSimplex.chartDomain d ((d+a : ℕ)+1)))
        (η : Kernel L (AffineSimplex.chartDomain e ((e+a : ℕ)+1)))
        [IsMarkovKernel κ] [IsMarkovKernel η] (ρ μ ν : Measure L) (b : ℝ≥0∞),
        κ ∘ₘ μ = InterpolantLocalLaws.physicalExteriorLaw p d a θ ε →
        η ∘ₘ ν = InterpolantLocalLaws.physicalExteriorLaw p e a θ ε →
        ρ ≤ b • μ → ρ ≤ b • ν →
      CommonBaseKernel.law κ η ρ
        ((Prod.fst ⁻¹' {y | ¬ InterpolantLocalLaws.admissibleExterior p d a hd θ ε A K y}) ∪
          (Prod.snd ⁻¹' {z | ¬ InterpolantLocalLaws.admissibleExterior p e a he θ ε A K z})) ≤
        2*b*ENNReal.ofReal (C*Real.exp (-c*(a+1 : ℝ)^δ)) := by
  obtain ⟨K, ε₀, hK, hε₀, _, htail⟩ :=
    InterpolantLocalLaws.admissible_exteriors_typical hRig s hs hs1 A hA
  refine ⟨K, ε₀, hK, hε₀, fun ε hε hεle => ?_⟩
  obtain ⟨δ, hδ, h⟩ := htail ε hε hεle
  refine ⟨δ, hδ, fun βlo βhi hlo hle θ => ?_⟩
  obtain ⟨C, c, hC, hc, hb⟩ := h βlo βhi hlo hle θ
  refine ⟨C, c, hC, hc, fun p hps hpl hph d e a hd he ha h4d h4e hpowd hpowe
    L _ κ η _ _ ρ μ ν b hκ hη hρμ hρν => ?_⟩
  have hE := (InterpolantLocalLaws.measurableSet_admissibleExterior p d a hd θ ε A K).compl
  have hF := (InterpolantLocalLaws.measurableSet_admissibleExterior p e a he θ ε A K).compl
  have ht := CommonBaseKernel.bad_event_le κ η ρ μ ν b hρμ hρν
    {y | ¬ InterpolantLocalLaws.admissibleExterior p d a hd θ ε A K y}
    {z | ¬ InterpolantLocalLaws.admissibleExterior p e a he θ ε A K z} hE hF
  rw [hκ, hη] at ht
  have hd' := hb p hps hpl hph d a hd ha h4d
    (by simpa only [Nat.cast_add, Nat.cast_one] using hpowd)
  have he' := hb p hps hpl hph e a he ha h4e
    (by simpa only [Nat.cast_add, Nat.cast_one] using hpowe)
  simp only [Nat.cast_add, Nat.cast_one] at hd' he'
  apply ht.trans
  exact (add_le_add (mul_le_mul' le_rfl hd') (mul_le_mul' le_rfl he')).trans_eq (by ring)

end Riesz2.TwoVolumeComparison
