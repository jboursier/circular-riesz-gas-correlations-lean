/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.LengthDerivativePart2
public import Riesz2.Thermodynamic.LengthVariancePart4
public import Riesz2.ToMathlib.CompactFibreC1
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Moving-length differentiation of the physical penalized marginal

See the proof of Lemma 6.5 in the paper: collision flatness of the actual two-sided
penalized density supplies uniform domination, including its inverse-gap derivatives.
All integrals use the existing physical weight and the fixed zero-sum tangent chart.
-/

public section
noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal ContDiff

namespace Riesz2.LengthDerivative

open AffineSimplex LengthAveragingFibres

/-- See the proof of Lemma 6.5 in the paper, collision regularity:
the actual two-sided penalized density is C¹ in every affine mass chart.
The collision-face flux theorem supplies continuity of every directional
derivative, including directions transverse to a collision face. -/
theorem penalized_affine_density_C1 (p : Parameters) (k : ℕ) (hk : 1 ≤ k)
    (d : ℕ) (A : EuclideanSpace ℝ (Fin d) →ᴬ[ℝ] EuclideanSpace ℝ (Fin (k + 1)))
    (hmass : ∀ x, ∑ i, A x i = (k + 1 : ℝ)) (θ : PhysicalCutoff)
    {a : ℝ} (ha : 0 < a) (J : Finset (Fin (k + 1))) :
    ContDiff ℝ 1 (fun x =>
      (ProperMarginalChart.penalizedDensity p k θ a J true (A x)).toReal) := by
  refine contDiff_one_iff_fderiv.mpr ⟨
    LengthVariance.penalized_affine_density_differentiable p k hk d A hmass θ ha J, ?_⟩
  apply continuous_clm_apply.mpr
  intro v
  exact (LengthVariance.penalized_affine_density_flux_regular p k hk d A hmass θ ha J v).1.continuous

/-- See the proof of Lemma 6.5 in the paper: the actual penalized
joint chart density, extended by zero, is C¹ and compactly supported. The
penalty coefficient is any positive number and includes its inverse-gap part. -/
theorem penalized_chart_density_C1_compact (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (J : Finset (Fin (n + m + 1))) :
    ContDiff ℝ 1 (fun q =>
      (ProperMarginalChart.penalizedChartDensity p n m (Equiv.refl _) θ a J true q).toReal) ∧
    HasCompactSupport (fun q =>
      (ProperMarginalChart.penalizedChartDensity p n m (Equiv.refl _) θ a J true q).toReal) := by
  classical
  let L : ℝ := ((n + m : ℕ) + 1)
  let A : EuclideanSpace ℝ (Fin (n + m)) →ᴬ[ℝ]
      EuclideanSpace ℝ (Fin (n + m + 1)) :=
    (tangentMap (n + m)).toContinuousLinearMap.toContinuousAffineMap +
      ContinuousAffineMap.const ℝ _ (chart (n + m) L 0)
  have hA (x : EuclideanSpace ℝ (Fin (n + m))) :
      A x = chart (n + m) L x :=
    (chart_eq_tangentMap_add (n + m) L x).symm
  have hmass (x) : ∑ i, A x i = (n + m : ℕ) + (1 : ℝ) := by rw [hA, sum_chart]
  have hs := penalized_affine_density_C1 p (n + m) (by omega) (n + m) A hmass θ ha J
  have he (q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :
      (ProperMarginalChart.penalizedChartDensity p n m (Equiv.refl _) θ a J true q).toReal =
        (ProperMarginalChart.penalizedDensity p (n + m) θ a J true
          (A (RetainedSimplex.join n m q))).toReal := by
    have hc : A (RetainedSimplex.join n m q) =
        RetainedSimplex.chart n m L (Equiv.refl _) q := by rw [hA]; rfl
    rw [hc]
    by_cases hq : q ∈ RetainedSimplex.domain n m L
    · simp only [ProperMarginalChart.penalizedChartDensity, L, indicator_of_mem hq]
    · have hqS : RetainedSimplex.chart n m L (Equiv.refl _) q ∉ massSimplex (n + m) L :=
        fun h => hq ((RetainedSimplex.chart_mem_simplex n m L (Equiv.refl _) q).mp h)
      simp only [ProperMarginalChart.penalizedChartDensity, L, indicator_of_notMem hq,
        ProperMarginalChart.penalizedDensity, ProperMarginalChart.density, dite_eq_right hqS,
        zero_mul, ENNReal.toReal_zero]
  refine ⟨?_, ?_⟩
  · have : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :=
      Prod.continuousSMul
    have hj : ContDiff ℝ 1 (RetainedSimplex.join n m) :=
      (RetainedSimplex.join n m).toContinuousLinearEquiv.contDiff
    rw [funext he]
    exact hs.comp hj
  · apply HasCompactSupport.intro (RetainedSimplex.isBounded_domain n m L).isCompact_closure
    intro q hq
    have hq' : q ∉ RetainedSimplex.domain n m L := fun h => hq (subset_closure h)
    simp only [ProperMarginalChart.penalizedChartDensity, L, indicator_of_notMem hq',
      ENNReal.toReal_zero]

/-- See Lemma 6.5 of the paper: at every active point the real physical
marginal weight is the integrable exterior integral. Its extended
mass is finite before taking real values. -/
theorem marginalWeight_real_integral (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    let w := ProperMarginalChart.penalizedChartDensity p (n + 1) m (Equiv.refl _) θ
      ((n + 1 : ℝ) ^ (-ε))
      (Finset.univ.image (fun i : Fin (n + 1) => (i.castAdd m).castSucc)) true
    Integrable (fun z => (w (x,z)).toReal) volume ∧
      marginalWeight p n m θ ε x ≠ ⊤ ∧
      (marginalWeight p n m θ ε x).toReal = ∫ z, (w (x,z)).toReal := by
  classical
  intro w
  obtain ⟨hf, hs⟩ := penalized_chart_density_C1_compact p (n + 1) m (by omega) θ
    (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < n + 1) (-ε))
    (Finset.univ.image (fun i : Fin (n + 1) => (i.castAdd m).castSucc))
  have hi := CompactFibreC1.integrable volume hf.continuous hs x
  have hw (z) : w (x,z) ≠ ⊤ := by
    dsimp only [w, ProperMarginalChart.penalizedChartDensity]
    by_cases hq : (x,z) ∈ RetainedSimplex.domain (n + 1) m ((n + 1 + m : ℕ) + 1)
    · rw [indicator_of_mem hq]
      dsimp only [ProperMarginalChart.penalizedDensity]
      apply ENNReal.mul_ne_top _ ENNReal.ofReal_ne_top
      dsimp only [ProperMarginalChart.density]
      split_ifs
      · exact ENNReal.ofReal_ne_top
      · exact ENNReal.zero_ne_top
    · rw [indicator_of_notMem hq]
      exact ENNReal.zero_ne_top
  have he : ENNReal.ofReal (∫ z, (w (x,z)).toReal) = marginalWeight p n m θ ε x := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))]
    exact lintegral_congr fun z => ENNReal.ofReal_toReal (hw z)
  refine ⟨hi, he ▸ ENNReal.ofReal_ne_top, ?_⟩
  rw [← he, ENNReal.toReal_ofReal (integral_nonneg (fun _ => ENNReal.toReal_nonneg))]

/-- See the proof of Lemma 6.5 in the paper: the actual real
marginal density is globally C¹ and compactly supported, including across
active collisions. This controls derivatives as well as the density. -/
theorem marginalWeight_C1_compact (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) :
    ContDiff ℝ 1 (fun x => (marginalWeight p n m θ ε x).toReal) ∧
      HasCompactSupport (fun x => (marginalWeight p n m θ ε x).toReal) := by
  classical
  obtain ⟨hf, hs⟩ := penalized_chart_density_C1_compact p (n + 1) m (by omega) θ
    (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < n + 1) (-ε))
    (Finset.univ.image (fun i : Fin (n + 1) => (i.castAdd m).castSucc))
  have he := funext fun x => (marginalWeight_real_integral p n m θ ε x).2.2
  rw [he]
  exact CompactFibreC1.integral volume hf hs

/-- See the proof of Lemma 6.5 in the paper: the fixed tangent-chart
weight is jointly C¹ with compact support in length and tangent coordinate.
In particular its derivative has a common integrable envelope on every
compact length interval. -/
theorem centred_weight_C1_compact (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) :
    ContDiff ℝ 1 (fun q : ℝ × Tangent n =>
      (marginalWeight p n m θ ε (centredChart n q.1 q.2)).toReal) ∧
    HasCompactSupport (fun q : ℝ × Tangent n =>
      (marginalWeight p n m θ ε (centredChart n q.1 q.2)).toReal) := by
  have : ContinuousSMul ℝ (ℝ × Tangent n) := Prod.continuousSMul
  let C : (ℝ × Tangent n) →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
    { toFun := fun q => centredChart n q.1 q.2
      map_add' := by
        intro q r
        ext i
        simp only [centredChart, centre, Prod.fst_add, Prod.snd_add,
          Submodule.coe_add, PiLp.add_apply]
        change (q.2.val i + r.2.val i) + (q.1 + r.1) / (n + 1) = _
        rw [add_div]
        ring
      map_smul' := by
        intro c q
        ext i
        change c * q.2.val i + (c * q.1) / (n + 1) =
          c * (q.2.val i + q.1 / (n + 1))
        ring }
  have hinj : Function.Injective C := by
    intro q r h
    have hL : q.1 = r.1 := by
      have := congrArg (fun x : EuclideanSpace ℝ (Fin (n + 1)) => ∑ i, x i) h
      simpa only [C, LinearMap.coe_mk, AddHom.coe_mk, sum_centredChart] using this
    apply Prod.ext hL
    apply Subtype.ext
    change q.2.val + centre n q.1 = r.2.val + centre n r.1 at h
    rw [hL] at h
    exact add_right_cancel h
  obtain ⟨hf, hs⟩ := marginalWeight_C1_compact p n m θ ε
  exact ⟨hf.comp C.toContinuousLinearMap.contDiff,
    hs.comp_isClosedEmbedding (C.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hinj))⟩

/-- See the proof of Lemma 6.5 in the paper: the moving-chart weight
satisfies the fixed-fibre domination contract on the entire real parameter
line. The physical quotient is used only at interior lengths. -/
theorem centred_weight_domination (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) :
    DominatedFibre.DominatedFDerivOn (volume : Measure (Tangent n)) univ
      (fun L z => (marginalWeight p n m θ ε (centredChart n L z)).toReal)
      (fun L z => (fderiv ℝ (fun q : ℝ × Tangent n =>
        (marginalWeight p n m θ ε (centredChart n q.1 q.2)).toReal) (L,z)).comp
          (ContinuousLinearMap.inl ℝ ℝ (Tangent n))) := by
  obtain ⟨hf, hs⟩ := centred_weight_C1_compact p n m θ ε
  exact CompactFibreC1.domination volume hf hs univ isOpen_univ

/-- The existing centered chart is jointly smooth in length and tangent
coordinate. The proof of Lemma 6.5. -/
theorem centredChart_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (fun q : ℝ × Tangent n => centredChart n q.1 q.2) := by
  have : ContinuousSMul ℝ (ℝ × Tangent n) := Prod.continuousSMul
  have hcentre : (fun q : ℝ × Tangent n => centre n q.1) =
      fun q => q.1 • centre n 1 := by
    funext q
    ext i
    change q.1 / (n + 1) = q.1 * (1 / (n + 1))
    ring
  exact ((Tangent n).subtypeL.contDiff.comp contDiff_snd).add
    (by rw [hcentre]; exact contDiff_fst.smul contDiff_const)

/-- See the proof of Lemma 6.5 in the paper: uniform domination of
the actual observable-weighted numerator, for a C¹ block observable. -/
theorem centred_numerator_domination (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ)
    (G : BlockObservable (⟨n + 1, Nat.succ_pos n⟩ : ℕ+))
    (hG : ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin (n + 1)) => G.val (WithLp.ofLp x))) :
    let f := fun q : ℝ × Tangent n =>
      (marginalWeight p n m θ ε (centredChart n q.1 q.2)).toReal *
        G.val (WithLp.ofLp (centredChart n q.1 q.2))
    DominatedFibre.DominatedFDerivOn (volume : Measure (Tangent n)) univ
      (fun L z => f (L,z))
      (fun L z => (fderiv ℝ f (L,z)).comp (ContinuousLinearMap.inl ℝ ℝ (Tangent n))) := by
  intro f
  obtain ⟨hf, hs⟩ := centred_weight_C1_compact p n m θ ε
  exact CompactFibreC1.domination volume (hf.mul (hG.comp ((centredChart_contDiff n).of_le (by simp)))) hs.mul_right univ isOpen_univ

/-- See the proof of Lemma 6.5 in the paper: moving the total length
with a fixed zero-sum coordinate differentiates in the normal direction
`(1/(n+1)) • 1`, with no additional Jacobian. -/
theorem centredChart_hasDerivAt (n : ℕ) (L : ℝ) (z : Tangent n) :
    HasDerivAt (fun t => centredChart n t z) (centre n 1) L := by
  have he : (fun t => centredChart n t z) = fun t => z.val + t • centre n 1 := by
    funext t
    ext i
    change z.val i + t / (n + 1) = z.val i + t * (1 / (n + 1))
    ring
  rw [he]
  simpa only [id_eq, one_smul] using ((hasDerivAt_id L).smul_const (centre n 1)).const_add z.val

/-- See Lemma 6.5 of the paper: the literal marginal Hamiltonian has exactly
the physical density on its positive interior. -/
theorem marginalWeight_eq_exp_potential (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) :
    let P := fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
      ∑ i, (θ.val (((n + 1 : ℝ) ^ (-ε)) * y i) +
        θ.val (((n + 1 : ℝ) ^ (-ε)) * (y i)⁻¹))
    let K := fun y => p.val.1⁻¹ * (p.val.1 * P y -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n + 1) m (Equiv.refl _) (y,z)).toReal))
    ContDiffOn ℝ ∞ K (chartDomain (n + 1) ((n + 1 + m : ℕ) + 1)) ∧
    ∀ x ∈ chartDomain (n + 1) ((n + 1 + m : ℕ) + 1),
      (marginalWeight p n m θ ε x).toReal = Real.exp (-p.val.1 * K x) := by
  classical
  intro P K
  have hβ := p.property.1.ne'
  have hK := MarginalHessian.physical_penalized_marginal_potential_smooth p (n + 1) m
    (by omega) (Equiv.refl _) θ
    (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < n + 1) (-ε)) Finset.univ true
  refine ⟨?_, fun x hx => ?_⟩
  · exact contDiffOn_const.mul (by simpa only [↓reduceIte] using hK)
  · let S := ∑ i, x i
    obtain ⟨z, hz⟩ := show x ∈ range (centredChart n S) from by
      rw [range_centredChart]
      rfl
    have hzmem : z ∈ centredChart n S ⁻¹' massSimplex n S := by
      change centredChart n S z ∈ massSimplex n S
      rw [hz]
      exact ⟨hx.1, rfl⟩
    have ht := ConditionalWellPosedness.penalized_marginal_fibre_density p n m
      (Equiv.refl _) hx.2 θ ((n + 1 : ℝ) ^ (-ε)) Finset.univ true hzmem
    rw [hz] at ht
    have he : marginalWeight p n m θ ε x =
        ENNReal.ofReal (Real.exp (-(p.val.1 * P x -
          Real.log (∫ z : EuclideanSpace ℝ (Fin m),
            (ProperMarginalChart.chartDensity p (n + 1) m (Equiv.refl _) (x,z)).toReal)))) := by
      simpa only [marginalWeight, P, ↓reduceIte, Equiv.refl_apply] using ht.symm
    rw [he, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
    congr 1
    dsimp only [K]
    field_simp

/-- See the proof of Lemma 6.5 in the paper: the derivative of the
actual zero-extended marginal weight is minus density times the normal
marginal score. This identity holds also at and outside collisions, where
the weight and its derivative vanish. -/
theorem centred_weight_hasDerivAt_score (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) :
    let P := fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
      ∑ i, (θ.val (((n + 1 : ℝ) ^ (-ε)) * y i) +
        θ.val (((n + 1 : ℝ) ^ (-ε)) * (y i)⁻¹))
    let K := fun y => p.val.1⁻¹ * (p.val.1 * P y -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n + 1) m (Equiv.refl _) (y,z)).toReal))
    ∀ L : ℝ, ∀ z : Tangent n,
      HasDerivAt (fun t => (marginalWeight p n m θ ε (centredChart n t z)).toReal)
        (-p.val.1 * (marginalWeight p n m θ ε (centredChart n L z)).toReal *
          fderiv ℝ K (centredChart n L z) (centre n 1)) L := by
  intro P K L z
  let w := fun x => (marginalWeight p n m θ ε x).toReal
  let x := centredChart n L z
  have hw := (marginalWeight_C1_compact p n m θ ε).1.differentiable (by norm_num) x
  have hd : HasDerivAt (fun t => w (centredChart n t z)) (fderiv ℝ w x (centre n 1)) L :=
    by simpa only [Function.comp_def, w, x] using
      hw.hasFDerivAt.comp_hasDerivAt L (centredChart_hasDerivAt n L z)
  change HasDerivAt (fun t => w (centredChart n t z))
    (-p.val.1 * w x * fderiv ℝ K x (centre n 1)) L
  by_cases hx : x ∈ chartDomain (n + 1) ((n + 1 + m : ℕ) + 1)
  · obtain ⟨hK, he⟩ := marginalWeight_eq_exp_potential p n m θ ε
    have hKs := (hK.contDiffAt ((isOpen_chartDomain _ _).mem_nhds hx)).differentiableAt (by simp)
    have hev : w =ᶠ[𝓝 x] fun y => Real.exp (-p.val.1 * K y) :=
      eventuallyEq_of_mem ((isOpen_chartDomain _ _).mem_nhds hx) fun y hy => he y hy
    have hder := ((hKs.hasFDerivAt.const_mul (-p.val.1)).exp).congr_of_eventuallyEq hev
    have hdf := hder.fderiv
    change fderiv ℝ w x = _ at hdf
    have hv : fderiv ℝ w x (centre n 1) =
        -p.val.1 * w x * fderiv ℝ K x (centre n 1) := by
      rw [hdf]
      simp only [smul_apply, smul_eq_mul]
      change Real.exp (-p.val.1 * K x) * (-p.val.1 * fderiv ℝ K x (centre n 1)) = _
      rw [show w x = Real.exp (-p.val.1 * K x) from he x hx]
      ring
    rw [hv] at hd
    exact hd
  · have hz : w x = 0 := by
      change (marginalWeight p n m θ ε x).toReal = 0
      rw [marginalWeight_eq_zero p n m θ ε hx, ENNReal.toReal_zero]
    have hmin : IsLocalMin w x := Eventually.of_forall fun y => by
      rw [hz]
      exact ENNReal.toReal_nonneg
    rw [hmin.fderiv_eq_zero] at hd
    simpa only [hz, mul_zero, zero_mul, zero_apply] using hd

/-- See the proof of Lemma 6.5 in the paper, smooth differentiation
step: the physical every-length average agrees on its whole open carrier
with a C¹ function, whose derivative is the mean normal derivative minus
the normal-score covariance. Score and score-product integrability are
conclusions. -/
theorem smooth_averagedObservable_differentiation (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ)
    (G : BlockObservable (⟨n + 1, Nat.succ_pos n⟩ : ℕ+))
    (hG : ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin (n + 1)) => G.val (WithLp.ofLp x))) :
    let P := fun y : EuclideanSpace ℝ (Fin (n + 1)) =>
      ∑ i, (θ.val (((n + 1 : ℝ) ^ (-ε)) * y i) +
        θ.val (((n + 1 : ℝ) ^ (-ε)) * (y i)⁻¹))
    let K := fun y => p.val.1⁻¹ * (p.val.1 * P y -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p (n + 1) m (Equiv.refl _) (y,z)).toReal))
    let g := fun x : EuclideanSpace ℝ (Fin (n + 1)) => G.val (WithLp.ofLp x)
    ∃ M : ℝ → ℝ,
      (∀ L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ),
        M L.val = averagedObservable p n m θ ε G L) ∧
      ContDiffOn ℝ 1 M (Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) ∧
      ∀ L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ),
        Integrable (fun x => fderiv ℝ K x (centre n 1)) (fibreKernel p n m θ ε L) ∧
        Integrable (fun x => g x * fderiv ℝ K x (centre n 1)) (fibreKernel p n m θ ε L) ∧
        HasDerivAt M
          ((∫ x, fderiv ℝ g x (centre n 1) ∂fibreKernel p n m θ ε L) -
            p.val.1 * covariance g (fun x => fderiv ℝ K x (centre n 1))
              (fibreKernel p n m θ ε L)) L.val := by
  classical
  intro P K g
  let w := fun (L : ℝ) (z : Tangent n) =>
    (marginalWeight p n m θ ε (centredChart n L z)).toReal
  let g₀ := fun (L : ℝ) (z : Tangent n) => g (centredChart n L z)
  let f := fun q : ℝ × Tangent n => w q.1 q.2
  let num := fun q : ℝ × Tangent n => w q.1 q.2 * g₀ q.1 q.2
  let dw := fun L z => (fderiv ℝ f (L,z)).comp (ContinuousLinearMap.inl ℝ ℝ (Tangent n))
  let dn := fun L z => (fderiv ℝ num (L,z)).comp (ContinuousLinearMap.inl ℝ ℝ (Tangent n))
  let M := fun L => (∫ z, w L z * g₀ L z) / ∫ z, w L z
  have hw := centred_weight_domination p n m θ ε
  have hn := centred_numerator_domination p n m θ ε G hG
  have hC : ContDiff ℝ 1 (fun q : ℝ × Tangent n => centredChart n q.1 q.2) :=
    (centredChart_contDiff n).of_le (by simp)
  obtain ⟨hf, hs⟩ := centred_weight_C1_compact p n m θ ε
  have hnum : ContDiff ℝ 1 num := hf.mul (hG.comp hC)
  have hsnum : HasCompactSupport num := hs.mul_right
  have hmean (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) :
      M L.val = averagedObservable p n m θ ε G L :=
    (averagedObservable_centred_ratio p n m θ ε G L).2.symm
  refine ⟨M, hmean, ?_, fun L => ?_⟩
  · exact (CompactFibreC1.integral volume hnum hsnum).1.contDiffOn.div
      (CompactFibreC1.integral volume hf hs).1.contDiffOn
      (fun L hL => (centred_real_mass p n m θ ε ⟨L,hL⟩).2.ne')
  · let S := fun z : Tangent n => p.val.1 * fderiv ℝ K (centredChart n L.val z) (centre n 1)
    let D := fun z : Tangent n => fderiv ℝ g (centredChart n L.val z) (centre n 1)
    have hscore := centred_weight_hasDerivAt_score p n m θ ε
    have hforce : ∀ᵐ z : Tangent n, dw L.val z 1 = -w L.val z * S z := by
      obtain ⟨s, hss, _, b, hb, hbound, hdiff⟩ := hw.locally_dominated L.val (mem_univ _)
      filter_upwards [hdiff] with z hz
      have he := ((hz L.val (mem_of_mem_nhds hss)).hasDerivAt).unique (hscore L.val z)
      change dw L.val z 1 = _ at he
      rw [he]
      dsimp only [S, w]
      ring
    have hnumder : ∀ᵐ z : Tangent n,
        dn L.val z 1 = w L.val z * (D z - g₀ L.val z * S z) := by
      obtain ⟨s, hss, _, b, hb, hbound, hdiff⟩ := hn.locally_dominated L.val (mem_univ _)
      filter_upwards [hdiff] with z hz
      have hdg := (hG.differentiable (by norm_num) (centredChart n L.val z)).hasFDerivAt.comp_hasDerivAt
        L.val (centredChart_hasDerivAt n L.val z)
      have he := ((hz L.val (mem_of_mem_nhds hss)).hasDerivAt).unique
        ((hscore L.val z).mul hdg)
      change dn L.val z 1 = _ at he
      rw [he]
      dsimp only [S, D, g₀, w, g] at *
      ring
    have hDcont : Continuous (fun q : ℝ × Tangent n =>
        w q.1 q.2 * fderiv ℝ g (centredChart n q.1 q.2) (centre n 1)) :=
      hf.continuous.mul (((hG.continuous_fderiv (by norm_num)).clm_apply continuous_const).comp
        hC.continuous)
    have hDi : Integrable (fun z => w L.val z * D z) volume :=
      CompactFibreC1.integrable volume hDcont hs.mul_right L.val
    have hpos := (centred_real_mass p n m θ ε L).2
    let ρ₀ := AffineFibre.normalizedMeasure (volume : Measure (Tangent n))
      (fun z => ENNReal.ofReal (w L.val z))
      (by rw [← ofReal_integral_eq_lintegral_ofReal (hw.integrable L.val (mem_univ _))
            (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))]
          exact ENNReal.ofReal_ne_zero_iff.mpr hpos)
      (by rw [← ofReal_integral_eq_lintegral_ofReal (hw.integrable L.val (mem_univ _))
            (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))]
          exact ENNReal.ofReal_ne_top)
    let ρ := AffineFibre.normalizedMeasure (volume : Measure (Tangent n))
      (fun z => marginalWeight p n m θ ε (centredChart n L.val z))
      (centred_mass_valid p n m θ ε L).1 (centred_mass_valid p n m θ ε L).2
    have hρ : ρ₀ = ρ := by
      have hew : (fun z => ENNReal.ofReal (w L.val z)) =
          fun z => marginalWeight p n m θ ε (centredChart n L.val z) := by
        funext z
        exact ENNReal.ofReal_toReal
          (marginalWeight_real_integral p n m θ ε (centredChart n L.val z)).2.1
      dsimp only [ρ₀, ρ]
      congr 1
    have hr : Integrable S ρ₀ ∧ Integrable (fun z => g₀ L.val z * S z) ρ₀ ∧
        HasDerivAt M ((∫ z, D z ∂ρ₀) - covariance (g₀ L.val) S ρ₀) L.val :=
      CompactFibreC1.normalized_hasDerivAt_score hw hn
        (fun _ => ENNReal.toReal_nonneg) hpos S D hforce hnumder hDi
    rw [hρ] at hr
    have hmap : fibreKernel p n m θ ε L = ρ.map (centredChart n L.val) :=
      fibreKernel_eq_centred_map p n m θ ε L
    have hm : AEMeasurable (centredChart n L.val) ρ :=
      (isometry_centredChart n L.val).continuous.measurable.aemeasurable
    have hKmeas : Measurable (fun x => fderiv ℝ K x (centre n 1)) :=
      measurable_fderiv_apply_const ℝ K (centre n 1)
    have hgmeas : Measurable g := hG.continuous.measurable
    have hSmeas : Measurable (fun x => p.val.1 * fderiv ℝ K x (centre n 1)) :=
      measurable_const.mul hKmeas
    have hSi : Integrable (fun x => p.val.1 * fderiv ℝ K x (centre n 1))
        (fibreKernel p n m θ ε L) := by
      rw [hmap]
      exact (integrable_map_measure hSmeas.aestronglyMeasurable hm).mpr hr.1
    have hGSi : Integrable (fun x => g x * (p.val.1 * fderiv ℝ K x (centre n 1)))
        (fibreKernel p n m θ ε L) := by
      rw [hmap]
      exact (integrable_map_measure (hgmeas.mul hSmeas).aestronglyMeasurable hm).mpr hr.2.1
    have hβ := p.property.1.ne'
    refine ⟨?_, ?_, ?_⟩
    · convert hSi.const_mul p.val.1⁻¹ using 1
      ext x
      field_simp
    · convert hGSi.const_mul p.val.1⁻¹ using 1
      ext x
      field_simp
    · have hiD : (∫ x, fderiv ℝ g x (centre n 1) ∂fibreKernel p n m θ ε L) = ∫ z, D z ∂ρ := by
        rw [hmap, integral_map hm (measurable_fderiv_apply_const ℝ g (centre n 1)).aestronglyMeasurable]
      have hcov : p.val.1 * covariance g (fun x => fderiv ℝ K x (centre n 1))
          (fibreKernel p n m θ ε L) = covariance (g₀ L.val) S ρ := by
        rw [← covariance_const_mul_right, hmap,
          covariance_map hgmeas.aestronglyMeasurable hSmeas.aestronglyMeasurable hm]
        rfl
      rw [hiD, hcov]
      exact hr.2.2

end Riesz2.LengthDerivative
