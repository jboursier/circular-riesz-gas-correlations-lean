/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.RigidityGaps
public import Riesz1.Rigidity.ForcingComparison
public import Riesz1.Frozen.External.BakryEmeryProof
public import Riesz1.Frozen.External.PrekopaLeindlerProof
public import Riesz2.Bridges.GapRigidity
public import Riesz2.Bridges.ConvexMeasureInputs
public import Riesz2.ToMathlib.AffineFibreDisintegration
public import Mathlib.Tactic

/-!
# Long-range rigidity and conditional Brascamp–Lieb inputs

The companion gap rigidity estimate follows from
`Riesz1.almost_optimal_rigidity_gaps` for `0 < b < (1 - s/2)/2`.
Its inequality inputs are `Riesz1.External.bakry_emery` and
`Riesz1.External.prekopa_leindler`.

The conditional Brascamp–Lieb inequality follows from
`Riesz2.euclidean_brascamp_lieb` on a bounded open convex domain in `ℝ^d`.
The dimension-zero case is the identity `0 = 0`.

The fibre form `longConditionalBL_fibre` uses the standard coordinates
`y ∈ ℝ^n` on the section `{y | (x, y) ∈ Q}` of `Q ⊂ B × ℝ^n`.
The corollary `longConditionalBL_convexConditional` gives the same bound for
`Riesz2.AffineFibre.convexConditionalMeasure`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace

namespace Riesz2

/-! ### Companion rigidity -/

/-- The companion rigidity estimate. Let `0 < s < 1`, and let
`β > 0`. For every `0 < b < (1 - s/2)/2`, there exist `C, c > 0`, depending only on `β, s, b`, such
that for every integer `N ≥ 2`, every cyclic label `i ∈ ℤ`, and every integer
`1 ≤ k ≤ ⌊N/2⌋`, the Gibbs probability of `|N(t_{i+k} - t_i) - k| ≥ k^{s/2 + b}` is at most
`C exp(-c k^{b/(4(s+2))})`. The labels are cyclic lifts: `t_{i+N} = t_i + 1`. -/
theorem longRangeRigidity (β : InverseTemperature) (s : Riesz1.RieszExponent) {b : ℝ}
    (hb : 0 < b) (hbs : b < (1 - s.val / 2) / 2) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (N : ℕ+) (_ : 2 ≤ (N : ℕ)) (i : ℤ) (k : ℕ), 1 ≤ k → k ≤ (N : ℕ) / 2 →
        gibbsMeasure (ofLong β s) N {X |
          |(N : ℝ) * (Riesz1.cyclicLift X (i + k) - Riesz1.cyclicLift X i) - k| ≥
            (k : ℝ) ^ (s.val / 2 + b)} ≤
          ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ (b / (4 * (s.val + 2))))) := by
  have hs := s.property
  set P : Riesz1.Parameters := ⟨(β.val, s.val), β.property, hs.1, hs.2⟩ with hP
  have hεs : b < min 1 (1 - (Riesz1.parametersExponent P).val / 2) := by
    show b < min 1 (1 - s.val / 2)
    exact lt_min (by linarith) (by linarith)
  obtain ⟨c₁, C₁, hc₁, hC₁, hN⟩ := Riesz1.almost_optimal_rigidity_gaps
    Riesz1.External.bakry_emery Riesz1.External.prekopa_leindler P hb hεs
  refine ⟨C₁, c₁, hC₁, hc₁, fun N hN2 i k hk1 hk2 => ?_⟩
  have h2k : 2 * k ≤ (N : ℕ) := by
    have := (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mp hk2
    omega
  have hmain := (hN N hN2 i).1 k hk1 h2k
  have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hpow : (k : ℝ) ^ (b / (4 * (s.val + 2))) ≤ (k : ℝ) ^ (b / (2 * (s.val + 2))) :=
    Real.rpow_le_rpow_of_exponent_le hk1'
      (div_le_div_of_nonneg_left hb.le (by linarith [hs.1]) (by linarith [hs.1]))
  rw [gibbsMeasure_ofLong]
  have := Riesz1.isProbabilityMeasure_gibbsMeasure P N
  refine (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
    (mul_nonneg hC₁.le (Real.exp_pos _).le)).mpr ?_
  have hset : ∀ X : Riesz1.Configuration N,
      (|(N : ℝ) * (Riesz1.cyclicLift X (i + k) - Riesz1.cyclicLift X i) - k| ≥
        (k : ℝ) ^ (s.val / 2 + b)) ↔
      ((k : ℝ) ^ (s.val / 2 + b) ≤ |Riesz1.blockLength X i k - k|) := fun X => by
    unfold Riesz1.blockLength
    exact ge_iff_le
  have hS : {X : Riesz1.Configuration N |
      |(N : ℝ) * (Riesz1.cyclicLift X (i + k) - Riesz1.cyclicLift X i) - k| ≥
        (k : ℝ) ^ (s.val / 2 + b)} =
      {X : Riesz1.Configuration N | (k : ℝ) ^ (s.val / 2 + b) ≤
        |Riesz1.blockLength X i k - k|} :=
    Set.ext fun X => hset X
  rw [hS]
  refine (hmain.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC₁.le))
  show -c₁ * (k : ℝ) ^ (b / (2 * (s.val + 2))) ≤ -c₁ * (k : ℝ) ^ (b / (4 * (s.val + 2)))
  linarith [mul_le_mul_of_nonneg_left hpow hc₁.le]

/-! ### Euclidean conditional Brascamp–Lieb inequality -/

/-- The Euclidean Brascamp–Lieb inequality. Let `1 ≤ d`, and
let `Ω ⊂ ℝ^d` be bounded, nonempty, open and convex. Let `V ∈ C²(Ω)` with `∇²V ≥ a I_d` for some
`a > 0`. Let `μ` be the probability with density proportional to `e^{-V}` on `Ω`, with finite positive
normalization `∫_Ω e^{-V}`. Then for every `F ∈ H¹(μ)` with weak gradient `G`,
`Var_μ(F) ≤ E_μ[∇F · (∇²V)^{-1} ∇F]`. The energy `⟨G, (∇²V)^{-1} G⟩` is written as the variational
supremum `sup_h (2⟨G, h⟩ - ∇²V(h, h))`, and the identity of the two forms at each point of `Ω` is part
of the conclusion. -/
theorem longConditionalBL {d : ℕ} (hd : 1 ≤ d)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩb : Bornology.IsBounded Ω) (hΩo : IsOpen Ω)
    (hΩne : Ω.Nonempty) (hΩc : Convex ℝ Ω)
    {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiffOn ℝ 2 V Ω) {a : ℝ} (ha : 0 < a)
    (hH : ∀ x ∈ Ω, ∀ h : EuclideanSpace ℝ (Fin d), a * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h)
    (μ : Measure (EuclideanSpace ℝ (Fin d)))
    (hμ : μ = (volume.restrict Ω).withDensity
      (fun x => ENNReal.ofReal (Real.exp (-V x) / ∫ y in Ω, Real.exp (-V y)))) :
    (0 < ∫⁻ x in Ω, ENNReal.ofReal (Real.exp (-V x))) ∧
    (∫⁻ x in Ω, ENNReal.ofReal (Real.exp (-V x))) < ⊤ ∧
    IsProbabilityMeasure μ ∧
    (∀ (F : EuclideanSpace ℝ (Fin d) → ℝ) (G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
      Riesz1.WeightedSobolev.IsWeightedH1 μ Ω F G →
        (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) ≤
          ∫ x, sSup (Set.range fun h : EuclideanSpace ℝ (Fin d) =>
            2 * ⟪G x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h) ∂μ) ∧
    (∀ (g x : EuclideanSpace ℝ (Fin d)), x ∈ Ω →
      ∃ hB : IsCoercive (fderiv ℝ (fderiv ℝ V) x),
        sSup (Set.range fun h : EuclideanSpace ℝ (Fin d) =>
          2 * ⟪g, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h) =
          ⟪g, hB.continuousLinearEquivOfBilin.symm g⟫_ℝ) := by
  obtain ⟨hZ, hZf, hprob, hvar, hid⟩ :=
    Riesz2.euclidean_brascamp_lieb hd hΩb hΩo hΩne hΩc hV ha hH μ hμ
  refine ⟨hZ, hZf, hprob, fun F G hFG => (hvar F G hFG).1, fun g x hx => ?_⟩
  exact hid (fun _ => g) x hx

/-! ### Dimension zero -/

/-- On a one-point space, the variance of every function under a probability measure vanishes. -/
theorem variance_eq_zero_of_subsingleton {E : Type*} [MeasurableSpace E] [Subsingleton E]
    (μ : Measure E) [IsProbabilityMeasure μ] (F : E → ℝ) :
    ∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ = 0 := by
  have h : ∀ x, F x - ∫ y, F y ∂μ = 0 := by
    intro x
    have hc : ∀ y, F y = F x := fun y => congrArg F (Subsingleton.elim y x)
    simp [hc]
  simp [h]

/-- The dimension-zero Brascamp–Lieb inequality. On the zero-dimensional space, the
Brascamp–Lieb variance conclusion is the identity `0 = 0`: the variance vanishes and the variational
energy is zero at every point, so both sides are zero. -/
theorem longConditionalBL_zero_dim (V : EuclideanSpace ℝ (Fin 0) → ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin 0))) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ (Fin 0) → ℝ) (G : EuclideanSpace ℝ (Fin 0) → EuclideanSpace ℝ (Fin 0)) :
    (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) ≤
      ∫ x, sSup (Set.range fun h : EuclideanSpace ℝ (Fin 0) =>
        2 * ⟪G x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h) ∂μ := by
  rw [variance_eq_zero_of_subsingleton μ F]
  have hzero : ∀ x : EuclideanSpace ℝ (Fin 0),
      sSup (Set.range fun h : EuclideanSpace ℝ (Fin 0) =>
        2 * ⟪G x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h) = 0 := by
    intro x
    have hz : ∀ h : EuclideanSpace ℝ (Fin 0),
        2 * ⟪G x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h = 0 := by
      intro h
      rw [Subsingleton.elim h 0]
      simp
    have hr : Set.range (fun h : EuclideanSpace ℝ (Fin 0) =>
        2 * ⟪G x, h⟫_ℝ - fderiv ℝ (fderiv ℝ V) x h h) = {0} := by
      ext t
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h, rfl⟩
        exact hz h
      · rintro rfl
        exact ⟨0, hz 0⟩
    rw [hr, csSup_singleton]
  simp [hzero]

/-- In dimension zero, the normalized density `e^{-V}` on a nonempty set is a probability measure:
the one-point space carries a single finite positive mass. -/
theorem isProbabilityMeasure_normalized_zero_dim {Ω : Set (EuclideanSpace ℝ (Fin 0))}
    (hΩne : Ω.Nonempty) (V : EuclideanSpace ℝ (Fin 0) → ℝ) :
    IsProbabilityMeasure ((volume.restrict Ω).withDensity (fun y =>
      ENNReal.ofReal (Real.exp (-V y) / ∫ z in Ω, Real.exp (-V z)))) := by
  obtain ⟨z, hz⟩ := hΩne
  have hΩu : Ω = Set.univ := Set.eq_univ_of_forall fun y => by rwa [Subsingleton.elim y z]
  subst hΩu
  have hpt : (fun y : EuclideanSpace ℝ (Fin 0) => Real.exp (-V y)) =
      fun _ => Real.exp (-V z) := funext fun y => by rw [Subsingleton.elim y z]
  have hfin : volume (Set.univ : Set (EuclideanSpace ℝ (Fin 0))) ≠ ⊤ :=
    (Set.toFinite (Set.univ : Set (EuclideanSpace ℝ (Fin 0)))).isCompact.measure_lt_top.ne
  have hpos : volume (Set.univ : Set (EuclideanSpace ℝ (Fin 0))) ≠ 0 :=
    (isOpen_univ.measure_pos volume ⟨z, Set.mem_univ z⟩).ne'
  set m : ℝ := (volume (Set.univ : Set (EuclideanSpace ℝ (Fin 0)))).toReal with hm
  have hmpos : 0 < m := ENNReal.toReal_pos hpos hfin
  have hexp : Real.exp (-V z) ≠ 0 := (Real.exp_pos _).ne'
  have hZ : ∫ y in (Set.univ : Set (EuclideanSpace ℝ (Fin 0))), Real.exp (-V y) =
      Real.exp (-V z) * m := by
    rw [setIntegral_univ, hpt, integral_const, smul_eq_mul, measureReal_def, mul_comm]
  have hconst : (fun y : EuclideanSpace ℝ (Fin 0) => ENNReal.ofReal (Real.exp (-V y) /
      ∫ w in (Set.univ : Set (EuclideanSpace ℝ (Fin 0))), Real.exp (-V w))) =
      fun _ => ENNReal.ofReal (1 / m) := by
    funext y
    rw [hZ, Subsingleton.elim y z]
    congr 1
    field_simp
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, setLIntegral_univ, hconst,
    lintegral_const, ← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul (by positivity),
    one_div_mul_cancel hmpos.ne', ENNReal.ofReal_one]

/-! ### Fibre form, with the conditional law of `Riesz2.AffineFibre` -/

/-- The conditional law of `Riesz2.AffineFibre.convexConditionalMeasure` over `x` is the normalized
density `e^{-V(x, ·)}` on the section `{y | (x, y) ∈ Q}`, with respect to Lebesgue measure. -/
theorem convexConditionalMeasure_eq_section {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [FiniteDimensional ℝ B] [MeasurableSpace B] [BorelSpace B] {n : ℕ}
    {Q : Set (B × EuclideanSpace ℝ (Fin n))} {V : B × EuclideanSpace ℝ (Fin n) → ℝ}
    (hQo : IsOpen Q) (hQb : Bornology.IsBounded Q) (hV : ConvexOn ℝ Q V)
    (x : Prod.fst '' Q) :
    AffineFibre.convexConditionalMeasure hQo hQb hV x =
      (volume.restrict {y | (x.val, y) ∈ Q}).withDensity (fun y =>
        ENNReal.ofReal (Real.exp (-V (x.val, y)) /
          ∫ z in {y | (x.val, y) ∈ Q}, Real.exp (-V (x.val, z)))) := by
  obtain ⟨p, hp, hpx⟩ := x.property
  have hxp : (x.val, p.2) = p := Prod.ext hpx.symm rfl
  have hcont : Continuous fun y : EuclideanSpace ℝ (Fin n) => (x.val, y) := by fun_prop
  have hSo : IsOpen {y : EuclideanSpace ℝ (Fin n) | (x.val, y) ∈ Q} := hQo.preimage hcont
  have hS : MeasurableSet {y : EuclideanSpace ℝ (Fin n) | (x.val, y) ∈ Q} := hSo.measurableSet
  have hind : ∀ y : EuclideanSpace ℝ (Fin n),
      Q.indicator (fun q => Real.exp (-V q)) (x.val, y) =
        {y : EuclideanSpace ℝ (Fin n) | (x.val, y) ∈ Q}.indicator
          (fun z => Real.exp (-V (x.val, z))) y := by
    intro y
    by_cases hy : (x.val, y) ∈ Q <;> simp [hy]
  have hZpos : 0 < ∫ z in {y : EuclideanSpace ℝ (Fin n) | (x.val, y) ∈ Q},
      Real.exp (-V (x.val, z)) := by
    have h1 := Riesz1.marginal_exp_indicator_pos hQo hQb hV (z := x.val) ⟨p.2, hxp ▸ hp⟩
    simpa only [hind, integral_indicator hS] using h1
  have hZeq : ∫ y, Q.indicator (fun q => Real.exp (-V q)) (x.val, y) =
      ∫ z in {y : EuclideanSpace ℝ (Fin n) | (x.val, y) ∈ Q}, Real.exp (-V (x.val, z)) := by
    simp only [hind, integral_indicator hS]
  have hw : ∫⁻ y, ENNReal.ofReal (Q.indicator (fun q => Real.exp (-V q)) (x.val, y)) =
      ENNReal.ofReal (∫ z in {y : EuclideanSpace ℝ (Fin n) | (x.val, y) ∈ Q},
        Real.exp (-V (x.val, z))) := by
    rw [← ofReal_integral_eq_lintegral_ofReal
      (Riesz1.integrable_fiber_exp_indicator hQo hQb hV x.val)
      (ae_of_all _ fun y => indicator_nonneg (fun q _ => (Real.exp_pos (-V q)).le) (x.val, y)),
      hZeq]
  unfold AffineFibre.convexConditionalMeasure AffineFibre.normalizedMeasure
    AffineFibre.normalizedDensity
  rw [hw, ← withDensity_indicator hS]
  congr 1
  funext y
  dsimp only
  by_cases hy : (x.val, y) ∈ Q
  · have hyS : y ∈ {y : EuclideanSpace ℝ (Fin n) | (x.val, y) ∈ Q} := hy
    rw [Set.indicator_of_mem hyS, Set.indicator_of_mem hy]
    rw [← ENNReal.ofReal_inv_of_pos hZpos, ← ENNReal.ofReal_mul (inv_nonneg.2 hZpos.le),
      div_eq_inv_mul]
  · have hyS : y ∉ {y : EuclideanSpace ℝ (Fin n) | (x.val, y) ∈ Q} := hy
    simp [Set.indicator_of_notMem hyS, Set.indicator_of_notMem hy]

/-- Each fibre `{y | (x, y) ∈ Q}` of a convex set `Q ⊂ B × ℝ^n` is convex. -/
theorem convex_fibre_of_convex {B : Type*} [AddCommGroup B] [Module ℝ B] {n : ℕ}
    {Q : Set (B × EuclideanSpace ℝ (Fin n))} (hQc : Convex ℝ Q) (x : B) :
    Convex ℝ {y : EuclideanSpace ℝ (Fin n) | (x, y) ∈ Q} := by
  intro y₁ hy₁ y₂ hy₂ s t hs ht hst
  have e : (x, s • y₁ + t • y₂) = s • (x, y₁) + t • (x, y₂) :=
    Prod.ext (by simp [← add_smul, hst]) rfl
  show (x, s • y₁ + t • y₂) ∈ Q
  rw [e]
  exact hQc hy₁ hy₂ hs ht hst

/-- The Brascamp–Lieb inequality on a fibre. Let `B × ℝ^n` be a product, and let
`Q ⊂ B × ℝ^n`. Let `x` lie in the projection of `Q` to `B`, and let `ν` be the normalized density
`e^{-V(x, ·)}` on the fibre `{y | (x, y) ∈ Q}`, using the standard coordinates `y ∈ ℝ^n`. Assume that this fibre is open, bounded and convex, that `V(x, ·)` is `C²` on
it, and that `∇²_y V(x, y) ≥ a I` there for some `a > 0`. Then for every `F ∈ H¹(ν)` with weak
gradient `G`,
`Var_ν(F) ≤ E_ν[∇F · (∇²_y V)^{-1} ∇F]`, in the variational form of `longConditionalBL`. In
dimension zero the conclusion is `0 = 0`. -/
theorem longConditionalBL_fibre {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [FiniteDimensional ℝ B] [MeasurableSpace B] [BorelSpace B] {n : ℕ}
    {Q : Set (B × EuclideanSpace ℝ (Fin n))} {V : B × EuclideanSpace ℝ (Fin n) → ℝ}
    (x : Prod.fst '' Q)
    (hΩo : IsOpen {y : EuclideanSpace ℝ (Fin n) | (x.val, y) ∈ Q})
    (hΩb : Bornology.IsBounded {y : EuclideanSpace ℝ (Fin n) | (x.val, y) ∈ Q})
    (hQc : Convex ℝ {y : EuclideanSpace ℝ (Fin n) | (x.val, y) ∈ Q})
    (hVc : ContDiffOn ℝ 2 (fun y => V (x.val, y)) {y | (x.val, y) ∈ Q}) {a : ℝ} (ha : 0 < a)
    (hH : ∀ y : EuclideanSpace ℝ (Fin n), (x.val, y) ∈ Q →
      ∀ h : EuclideanSpace ℝ (Fin n), a * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (fun z => V (x.val, z))) y h h)
    (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hν : ν = (volume.restrict {y | (x.val, y) ∈ Q}).withDensity (fun y =>
      ENNReal.ofReal (Real.exp (-V (x.val, y)) /
        ∫ z in {y | (x.val, y) ∈ Q}, Real.exp (-V (x.val, z))))) :
    ∀ (F : EuclideanSpace ℝ (Fin n) → ℝ) (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      Riesz1.WeightedSobolev.IsWeightedH1 ν {y | (x.val, y) ∈ Q} F G →
        (∫ y, (F y - ∫ z, F z ∂ν) ^ 2 ∂ν) ≤
          ∫ y, sSup (Set.range fun h : EuclideanSpace ℝ (Fin n) =>
            2 * ⟪G y, h⟫_ℝ - fderiv ℝ (fderiv ℝ (fun z => V (x.val, z))) y h h) ∂ν := by
  obtain ⟨p, hp, hpx⟩ := x.property
  have hxp : (x.val, p.2) = p := Prod.ext hpx.symm rfl
  have hΩne : {y : EuclideanSpace ℝ (Fin n) | (x.val, y) ∈ Q}.Nonempty :=
    ⟨p.2, by show (x.val, p.2) ∈ Q; rw [hxp]; exact hp⟩
  intro F G hFG
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hprob : IsProbabilityMeasure ν := by
      rw [hν]
      exact isProbabilityMeasure_normalized_zero_dim hΩne (fun z => V (x.val, z))
    exact longConditionalBL_zero_dim (fun z => V (x.val, z)) ν F G
  · have hcl := longConditionalBL hn hΩb hΩo hΩne hQc hVc ha hH ν hν
    exact hcl.2.2.2.1 F G hFG

/-- The Brascamp–Lieb inequality for the conditional law of `Riesz2.AffineFibre`. This is
`longConditionalBL_fibre` with `ν` equal to `Riesz2.AffineFibre.convexConditionalMeasure`. The
convexity of `V` on `Q` is the standing hypothesis that defines that conditional law, and the
bound itself uses only the convexity of the fibre and the normalized density. -/
theorem longConditionalBL_convexConditional {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [FiniteDimensional ℝ B] [MeasurableSpace B] [BorelSpace B] {n : ℕ}
    {Q : Set (B × EuclideanSpace ℝ (Fin n))} {V : B × EuclideanSpace ℝ (Fin n) → ℝ}
    (hQo : IsOpen Q) (hQb : Bornology.IsBounded Q) (hV : ConvexOn ℝ Q V)
    (x : Prod.fst '' Q)
    (hVc : ContDiffOn ℝ 2 (fun y => V (x.val, y)) {y | (x.val, y) ∈ Q}) {a : ℝ} (ha : 0 < a)
    (hH : ∀ y : EuclideanSpace ℝ (Fin n), (x.val, y) ∈ Q →
      ∀ h : EuclideanSpace ℝ (Fin n), a * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (fun z => V (x.val, z))) y h h)
    (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hν : ν = AffineFibre.convexConditionalMeasure hQo hQb hV x) :
    ∀ (F : EuclideanSpace ℝ (Fin n) → ℝ) (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      Riesz1.WeightedSobolev.IsWeightedH1 ν {y | (x.val, y) ∈ Q} F G →
        (∫ y, (F y - ∫ z, F z ∂ν) ^ 2 ∂ν) ≤
          ∫ y, sSup (Set.range fun h : EuclideanSpace ℝ (Fin n) =>
            2 * ⟪G y, h⟫_ℝ - fderiv ℝ (fderiv ℝ (fun z => V (x.val, z))) y h h) ∂ν :=
  by
    have hcont : Continuous fun y : EuclideanSpace ℝ (Fin n) => (x.val, y) := by fun_prop
    have hΩo : IsOpen {y : EuclideanSpace ℝ (Fin n) | (x.val, y) ∈ Q} := hQo.preimage hcont
    have hΩb : Bornology.IsBounded {y : EuclideanSpace ℝ (Fin n) | (x.val, y) ∈ Q} :=
      ((LipschitzWith.prod_snd).isBounded_image hQb).subset fun y hy => ⟨(x.val, y), hy, rfl⟩
    exact longConditionalBL_fibre x hΩo hΩb (convex_fibre_of_convex hV.1 x.val) hVc ha hH ν
      (hν.trans (convexConditionalMeasure_eq_section hQo hQb hV x))

end Riesz2

end
end
