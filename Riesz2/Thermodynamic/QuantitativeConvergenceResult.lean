/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.OrdinaryGapCauchyCompact
public import Riesz2.Frozen.OrdinaryGapCauchy
public import Riesz2.Thermodynamic.GapLimit
public import Riesz2.Thermodynamic.ConvergenceResult
public import Riesz2.Frozen.ConvergenceRate
public import Riesz2.Thermodynamic.LocalTotalVariationFinal
public import Riesz2.Thermodynamic.LocalLimitUniqueness
public import Riesz2.Frozen.LimitingRieszProcess
public import Riesz2.Frozen.PalmRegular
public import Riesz2.Frozen.RootedGapBlock
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Riesz1.ToMathlib.Moments.RpowLpBound

/-!
# Quantitative convergence of labelled gaps

See Theorem 4. Block embeddings and a mesoscopic scale allow passage of the ordinary
Cauchy estimate to the infinite gap law.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2.QuantitativeConvergenceResult

/-- See Theorem 4 of the paper: extend an observable by ignoring
the additional coordinates. The original observable is used literally. -/
def extendBlock {K n : ℕ+} (h : (K : ℕ) ≤ (n : ℕ)) (G : BlockObservable K) :
    BlockObservable n :=
  ⟨fun x => G.val (fun i => x (Fin.castLE h i)), by
    obtain ⟨L, hL⟩ := G.property
    refine ⟨L * 1, hL.comp (LipschitzWith.of_dist_le_mul fun x y => ?_)⟩
    simp only [NNReal.coe_one, one_mul]
    exact (dist_pi_le_iff dist_nonneg).mpr fun i => dist_le_pi_dist x y _⟩

/-- Ignoring coordinates preserves each finite-volume integrand exactly. -/
theorem extendBlock_finite {K n N : ℕ+} (h : (K : ℕ) ≤ (n : ℕ))
    (G : BlockObservable K) (X : Riesz1.Configuration N) :
    (extendBlock h G).val (finiteGapBlock X) = G.val (finiteGapBlock X) := rfl

/-- The extension depends on the first `K` consecutive coordinates. -/
theorem extendBlock_depends {K n : ℕ+} (h : (K : ℕ) ≤ (n : ℕ))
    (G : BlockObservable K) :
    DependsOnBlockCoordinates (extendBlock h G)
      (Finset.univ.filter (fun i => 0 ≤ i.val ∧ i.val < (K : ℕ))) := by
  intro x y hxy
  apply congrArg G.val
  funext i
  exact hxy _ (by simp [i.isLt])

/-- Adding unused coordinates does not increase the derivative sum. -/
theorem extendBlock_norm_le {K n : ℕ+} (h : (K : ℕ) ≤ (n : ℕ))
    (G : BlockObservable K) :
    blockDerivativeNorm (extendBlock h G) ≤ blockDerivativeNorm G := by
  classical
  have hcoord (i : Fin (K : ℕ)) :
      coordinateDerivativeNorm (extendBlock h G) (Fin.castLE h i) ≤
        coordinateDerivativeNorm G i := by
    apply csInf_le (OrderBot.bddBelow _)
    intro x t
    have he : (fun j => (Function.update x (Fin.castLE h i) t) (Fin.castLE h j)) =
        Function.update (fun j => x (Fin.castLE h j)) i t := by
      funext j
      by_cases hj : j = i
      · subst j; simp
      · have hji : Fin.castLE h j ≠ Fin.castLE h i := fun he => hj (Fin.castLE_injective h he)
        simp [Function.update_of_ne hj, Function.update_of_ne hji]
    change |G.val _ - G.val _| ≤ _
    rw [he]
    exact InterpolatingDensities.coordinate_bound G i _ t
  have hzero (j : Fin (n : ℕ)) (hj : j ∉ Finset.univ.image (Fin.castLE h)) :
      coordinateDerivativeNorm (extendBlock h G) j = 0 := by
    apply le_antisymm _ (zero_le)
    apply csInf_le (OrderBot.bddBelow _)
    intro x t
    have he : (fun i : Fin (K : ℕ) => (Function.update x j t) (Fin.castLE h i)) =
        (fun i => x (Fin.castLE h i)) := by
      funext i
      apply Function.update_of_ne
      intro hij
      exact hj (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hij⟩)
    change |G.val _ - G.val _| ≤ (0 : ℝ≥0) * _
    rw [he]
    simp
  unfold blockDerivativeNorm
  calc
    _ = ∑ j ∈ Finset.univ.image (Fin.castLE h),
        (coordinateDerivativeNorm (extendBlock h G) j : ℝ) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      rw [hzero j hj, NNReal.coe_zero]
    _ = ∑ i : Fin (K : ℕ),
        (coordinateDerivativeNorm (extendBlock h G) (Fin.castLE h i) : ℝ) :=
      Finset.sum_image (fun _ _ _ _ he => Fin.castLE_injective h he)
    _ ≤ _ := Finset.sum_le_sum fun i _ => NNReal.coe_le_coe.mpr (hcoord i)

/-- See Theorem 4 of the paper: place the first `K` gaps into
the closed middle half, preserving both expectations and the derivative sum.
This uses the ordinary comparison interface. -/
theorem middle_block {K n : ℕ+} (hK : (K : ℕ) ≤ (n : ℕ) / 4)
    (G : BlockObservable K) :
    ∃ (H : BlockObservable n) (J : Finset (Fin (n : ℕ))),
      MiddleConsecutiveBlock n J ∧ DependsOnBlockCoordinates H J ∧
      blockDerivativeNorm H ≤ blockDerivativeNorm G ∧
      ∀ (p : Parameters) (N : ℕ+), 2 ≤ (N : ℕ) →
        (∫ X : Riesz1.Configuration N, H.val (finiteGapBlock X) ∂gibbsMeasure p N) =
          ∫ X : Riesz1.Configuration N, G.val (finiteGapBlock X) ∂gibbsMeasure p N := by
  classical
  have hKn : (K : ℕ) ≤ (n : ℕ) := hK.trans (Nat.div_le_self _ _)
  obtain ⟨H, hH, hnorm, he⟩ := OrdinaryGapCauchyV2.interval_transport
    0 ((n : ℕ) / 2) (K : ℕ) (by omega) (by omega)
    (extendBlock hKn G) (by simpa only [zero_add] using extendBlock_depends hKn G)
  refine ⟨H, _, ?_, hH, hnorm.trans (extendBlock_norm_le hKn G), ?_⟩
  · refine ⟨(n : ℕ) / 2, (K : ℕ), hK, by omega, rfl, ?_⟩
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    omega
  · intro p N hN
    exact he p N hN

/-- See Theorem 4 of the paper: the floor scale satisfies every
size condition of the ordinary comparison, including the maximal allowed `K`. -/
theorem scale (s : ℝ) (hs : 0 < s) (N K : ℕ+)
    (hK : (K : ℝ) ≤ (N : ℝ) ^ exponentA s / 32) :
    ∃ n : ℕ+, 4 ≤ (n : ℕ) ∧ (K : ℕ) ≤ (n : ℕ) / 4 ∧
      4 * (n : ℕ) ≤ (N : ℕ) ∧ (n : ℝ) ^ (2 / s) ≤ (N : ℝ) ∧
      (N : ℝ) ^ exponentA s / 16 ≤ (n : ℝ) ∧
      (n : ℝ) ≤ (N : ℝ) ^ exponentA s / 8 := by
  let X : ℝ := (N : ℝ) ^ exponentA s
  have hN : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ (N : ℕ) from N.pos)
  have hN0 : (0 : ℝ) < (N : ℝ) := by positivity
  have hX : 32 ≤ X := by
    have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (show 1 ≤ (K : ℕ) from K.pos)
    change (K : ℝ) ≤ X / 32 at hK
    linarith
  let m : ℕ := ⌊X / 8⌋₊
  have hm4 : 4 ≤ m := (Nat.le_floor_iff (by positivity : 0 ≤ X / 8)).mpr (by
    norm_num; linarith)
  let n : ℕ+ := ⟨m, by omega⟩
  have hupper : (n : ℝ) ≤ X / 8 := Nat.floor_le (by positivity)
  have hlower : X / 8 < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmreal : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hm4
  have hKn : (K : ℕ) ≤ (n : ℕ) / 4 := by
    have h4K : 4 * (K : ℕ) ≤ m :=
      (Nat.le_floor_iff (by positivity : 0 ≤ X / 8)).mpr (by
        push_cast
        change (K : ℝ) ≤ X / 32 at hK
        linarith)
    change (K : ℕ) ≤ m / 4
    omega
  have hXN : X ≤ (N : ℝ) := by
    exact (Real.rpow_le_rpow_of_exponent_le hN (min_le_right _ _)).trans_eq (Real.rpow_one _)
  have h4n : 4 * (n : ℕ) ≤ (N : ℕ) := by
    have hh : 4 * (n : ℝ) ≤ (N : ℝ) := by linarith
    exact_mod_cast hh
  refine ⟨n, hm4, hKn, h4n, ?_, by dsimp [X] at *; linarith, hupper⟩
  have hpower : (n : ℝ) ≤ X := by linarith
  calc
    (n : ℝ) ^ (2 / s) ≤ X ^ (2 / s) :=
      Real.rpow_le_rpow (by positivity) hpower (by positivity)
    _ = (N : ℝ) ^ (exponentA s * (2 / s)) := (Real.rpow_mul hN0.le _ _).symm
    _ ≤ (N : ℝ) ^ (1 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hN
      have ha : exponentA s ≤ s / 2 := min_le_left _ _
      have hh := mul_le_mul_of_nonneg_right ha (show 0 ≤ 2 / s by positivity)
      have he : s / 2 * (2 / s) = 1 := by field_simp
      linarith
    _ = (N : ℝ) := Real.rpow_one _

/-- See Theorem 4 of the paper: choose the loss before all volumes,
and convert the comparison scale to the exact convergence rate. -/
theorem rate (s ε : ℝ) (hs : 0 < s) (hε : 0 < ε) :
    ∃ ζ A : ℝ, 0 < ζ ∧ ζ < exponentB s ∧ 0 < A ∧
      ∀ (N n : ℕ+), (N : ℝ) ^ exponentA s / 16 ≤ (n : ℝ) →
        (n : ℝ) ^ (-min s 1 / 2 + ζ) ≤ A * (N : ℝ) ^ (-convergenceRate s + ε) := by
  have ha : 0 < exponentA s := lt_min (by linarith) zero_lt_one
  have hb : 0 < exponentB s := by unfold exponentB; positivity
  let ζ : ℝ := min (exponentB s / 2) (ε / (2 * exponentA s))
  have hζ : 0 < ζ := lt_min (by positivity) (by positivity)
  have hζb : ζ < exponentB s := (min_le_left _ _).trans_lt (by linarith)
  have hζε : exponentA s * ζ ≤ ε := by
    have hh := mul_le_mul_of_nonneg_left (min_le_right
      (exponentB s / 2) (ε / (2 * exponentA s))) ha.le
    have he : exponentA s * (ε / (2 * exponentA s)) = ε / 2 := by field_simp
    change exponentA s * ζ ≤ ε
    rw [he] at hh
    linarith
  let e : ℝ := -exponentB s + ζ
  refine ⟨ζ, 16 ^ (-e), hζ, hζb, by positivity, ?_⟩
  intro N n hn
  have hN : (0 : ℝ) < (N : ℝ) := by positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ (N : ℕ) from N.pos)
  have he : e ≤ 0 := by dsimp [e]; linarith
  rw [show -min s 1 / 2 + ζ = e by dsimp [e, exponentB]; ring]
  calc
    (n : ℝ) ^ e ≤ ((N : ℝ) ^ exponentA s / 16) ^ e :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hn he
    _ = 16 ^ (-e) * (N : ℝ) ^ (exponentA s * e) := by
      rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hN.le,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 16)]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le hN1
      dsimp [convergenceRate, e]
      nlinarith

/-- See Theorem 4 of the paper: second coordinate moments give
a uniform second moment of every unbounded Lipschitz block observable. -/
theorem block_second_moment (q : ProbabilityMeasure (ℤ → Ioi (0 : ℝ)))
    {D : ℝ} (hD : 0 ≤ D)
    (hmoment : ∀ i : ℤ,
      (∫⁻ y : ℤ → Ioi (0 : ℝ), ENNReal.ofReal ((y i : ℝ) ^ (2 : ℝ)) ∂q) ≤
        ENNReal.ofReal D)
    {K : ℕ+} (G : BlockObservable K) :
    let F := fun y : ℤ → Ioi (0 : ℝ) => G.val (fun j => (y (j.val : ℤ) : ℝ))
    MemLp F 2 q ∧ (∫ y, F y ^ 2 ∂q) ≤
      2 * ((D + 2) * blockDerivativeNorm G) ^ 2 + 2 * G.val (fun _ => 1) ^ 2 := by
  intro F
  have hcoord (j : Fin (K : ℕ)) :
      eLpNorm (fun y : ℤ → Ioi (0 : ℝ) => (y (j.val : ℤ) : ℝ)) 2 q ≤
        ENNReal.ofReal (D + 1) := by
    have hh : D ≤ (D + 1) ^ (2 : ℝ) := by rw [Real.rpow_two]; nlinarith
    simpa only [ENNReal.ofReal_ofNat] using Riesz1.eLpNorm_le_of_lintegral_rpow_le
      q.toMeasure (by fun_prop) (fun y => (y _).property.le)
      (by norm_num : (0 : ℝ) < 2) (by linarith : 0 ≤ D + 1)
      ((hmoment j.val).trans (ENNReal.ofReal_le_ofReal hh))
  obtain ⟨hcenter, hbound⟩ := InterpolatingDensities.internal_centered_block_norm
    q.toMeasure G (fun y j => (y (j.val : ℤ) : ℝ)) (by intro j; fun_prop)
      (by linarith : 0 ≤ D + 1) hcoord
  have hF : MemLp F 2 q := by
    convert hcenter.add (memLp_const (G.val (fun _ => 1))) using 1
    funext y
    simp [F]
  refine ⟨hF, ?_⟩
  have hcenter2 : (∫ y, (F y - G.val (fun _ => 1)) ^ 2 ∂q) ≤
      ((D + 2) * blockDerivativeNorm G) ^ 2 := by
    have hn : 0 ≤ (D + 2) * blockDerivativeNorm G :=
      mul_nonneg (by linarith) (Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _)
    have hsq := mul_self_le_mul_self (Real.sqrt_nonneg _) hbound
    rw [← sq, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _), ← sq] at hsq
    simpa only [add_assoc, one_add_one_eq_two] using hsq
  have hpoint (y) : F y ^ 2 ≤
      2 * (F y - G.val (fun _ => 1)) ^ 2 + 2 * G.val (fun _ => 1) ^ 2 := by
    nlinarith [sq_nonneg (F y - 2 * G.val (fun _ => 1))]
  have hi := integral_mono hF.integrable_sq
    ((hcenter.integrable_sq.const_mul 2).add (integrable_const _)) hpoint
  simp only [Pi.add_apply] at hi
  rw [integral_add (hcenter.integrable_sq.const_mul 2) (integrable_const _),
    integral_const_mul, integral_const] at hi
  simp only [probReal_univ, smul_eq_mul, one_mul] at hi
  linarith

/-- See Theorem 4 of the paper: weak convergence of the gap law
passes every fixed unbounded Lipschitz test, by uniform second moments. -/
theorem block_integral_tendsto (p : Parameters)
    (q : ProbabilityMeasure (ℤ → Ioi (0 : ℝ)))
    (hq : Tendsto (fun m : ℕ => periodicGapLaw p m.succPNat) atTop (𝓝 q))
    {K : ℕ+} (G : BlockObservable K) :
    Integrable (fun y : ℤ → Ioi (0 : ℝ) => G.val (fun j => (y (j.val : ℤ) : ℝ))) q ∧
      Tendsto (fun m : ℕ => ∫ X : Riesz1.Configuration m.succPNat,
        G.val (finiteGapBlock X) ∂gibbsMeasure p m.succPNat) atTop
        (𝓝 (∫ y : ℤ → Ioi (0 : ℝ), G.val (fun j => (y (j.val : ℤ) : ℝ)) ∂q)) := by
  let V : ℕ → ℕ+ := fun m => (m + 1).succPNat
  have hV : ∀ m, 2 ≤ (V m : ℕ) := by intro m; simp [V]
  have hqV : Tendsto (fun m => periodicGapLaw p (V m)) atTop (𝓝 q) :=
    (tendsto_add_atTop_iff_nat 1).mpr hq
  obtain ⟨D, hD, hf, hl⟩ := periodicGapLaw_limit_moment_bound p V hV q hqV 2 (by norm_num)
  have hfinite (m : ℕ) := block_second_moment (periodicGapLaw p (V m)) hD.le
    (fun i => (le_add_right le_rfl).trans (hf (V m) (hV m) i)) G
  have hlimit := block_second_moment q hD.le
    (fun i => (le_add_right le_rfl).trans (hl i)) G
  refine ⟨hlimit.1.integrable (by norm_num), ?_⟩
  apply (tendsto_add_atTop_iff_nat 1).mp
  have hcont : Continuous (fun y : ℤ → Ioi (0 : ℝ) =>
      G.val (fun j => (y (j.val : ℤ) : ℝ))) :=
    G.property.choose_spec.continuous.comp (by fun_prop)
  have ht := WeakMomentTruncation.integral_tendsto_of_uniform_second_moment_internal
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hqV)
    hcont (fun m => (hfinite m).1) hlimit.1
    (Eventually.of_forall fun m => (hfinite m).2)
  simp_rw [integral_periodicGapLaw p _ hcont.measurable] at ht
  exact ht


local instance quantitativeConfigurationMeasurableSpace :
    MeasurableSpace LineConfiguration := configurationMeasurableSpace

/-- See Theorem 4 of the paper: identify the weak gap limit with
the actual Palm gaps of the uniquely specified limiting process. -/
theorem palm_gap_limit_internal
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
    (hlog : External.LogConcaveConvergence)
    (p : Parameters) (h : UniqueRieszLimit p) :
    ∃ q : ProbabilityMeasure (ℤ → Ioi (0 : ℝ)),
      Tendsto (fun m : ℕ => periodicGapLaw p m.succPNat) atTop (𝓝 q) ∧
      (rootedPalmMeasure (limitingRieszProcess p h)).map rootedGap =
        q.toMeasure.map (fun y : ℤ → Ioi (0 : ℝ) => fun i => (y i : ℝ)) := by
  obtain ⟨q, hq, _⟩ := convergence_local_total_variation_from_cauchy_internal hcomparison hlog p
  obtain ⟨qP, hqP, _⟩ := convergence_palm_inversion_from_cauchy_internal hcomparison p
  have heq : qP = q := tendsto_nhds_unique hqP.1 hq.1
  subst qP
  obtain ⟨P, hP, hlocal⟩ := hq.2
  obtain ⟨Q, hQ, _, _, _, _, hgap, _⟩ := hqP.2
  have hPQ : P = Q := ProbabilityMeasure.toMeasure_injective (hP.trans hQ.symm)
  have hchosen : limitingRieszProcess p h = P :=
    localConverges_unique _ _ P (Classical.choose_spec h.exists) hlocal
  refine ⟨q, hq.1, ?_⟩
  rw [hchosen, hPQ]
  exact hgap

/-- Transport a Lipschitz test and its integrability through the Palm
gap map, with no boundedness assumption on the test. -/
theorem palm_block_integral_internal (P : PointProcess)
    (q : ProbabilityMeasure (ℤ → Ioi (0 : ℝ)))
    (hgap : (rootedPalmMeasure P).map rootedGap =
      q.toMeasure.map (fun y : ℤ → Ioi (0 : ℝ) => fun i => (y i : ℝ)))
    {K : ℕ+} (G : BlockObservable K)
    (hi : Integrable (fun y : ℤ → Ioi (0 : ℝ) =>
      G.val (fun j => (y (j.val : ℤ) : ℝ))) q) :
    Integrable (fun C => G.val (rootedGapBlock K C)) (rootedPalmMeasure P) ∧
      (∫ C, G.val (rootedGapBlock K C) ∂rootedPalmMeasure P) =
        ∫ y : ℤ → Ioi (0 : ℝ), G.val (fun j => (y (j.val : ℤ) : ℝ)) ∂q := by
  let F : (ℤ → ℝ) → ℝ := fun y => G.val (fun j => y (j.val : ℤ))
  have hF : Measurable F := G.property.choose_spec.continuous.measurable.comp
    (measurable_pi_iff.mpr fun j => measurable_pi_apply _)
  have hcoe : Measurable (fun y : ℤ → Ioi (0 : ℝ) => fun i => (y i : ℝ)) :=
    measurable_pi_iff.mpr fun i => measurable_subtype_coe.comp (measurable_pi_apply i)
  have hroot : Measurable (rootedGap : RootedConfiguration → ℤ → ℝ) :=
    measurable_pi_iff.mpr measurable_rootedGap
  have hmap : Integrable F ((rootedPalmMeasure P).map rootedGap) := by
    rw [hgap]
    exact (integrable_map_measure hF.aestronglyMeasurable hcoe.aemeasurable).mpr hi
  refine ⟨(integrable_map_measure hF.aestronglyMeasurable hroot.aemeasurable).mp hmap, ?_⟩
  change (∫ C, F (rootedGap C) ∂rootedPalmMeasure P) = _
  rw [← integral_map hroot.aemeasurable hF.aestronglyMeasurable, hgap,
    integral_map hcoe.aemeasurable hF.aestronglyMeasurable]

/-- Theorem 4 of the paper, with constants locally
uniform in β. Choose the comparison constant before β and pass its bound
to each Palm gap limit separately, using the paper's mesoscopic scale. -/
theorem quantitativeConvergence_locallyUniform
    (hlog : External.LogConcaveConvergence)
    (s : {s : ℝ // 0 < s ∧ s ≠ 1}) (ε : ℝ) (hε : 0 < ε)
    (βlo βhi : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C : ℝ, 0 < C ∧
      ∀ p : Parameters, p.val.2 = s.val → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∃ h : UniqueRieszLimit p,
        let P := limitingRieszProcess p h
        PalmRegular P ∧ ∀ N K : ℕ+,
          (K : ℝ) ≤ (N : ℝ) ^ exponentA s.val / 32 → ∀ G : BlockObservable K,
          Integrable (fun X : Riesz1.Configuration N => G.val (finiteGapBlock X))
            (gibbsMeasure p N) ∧
          Integrable (fun C => G.val (rootedGapBlock K C)) (rootedPalmMeasure P) ∧
          |(∫ X, G.val (finiteGapBlock X) ∂gibbsMeasure p N) -
            (∫ C, G.val (rootedGapBlock K C) ∂rootedPalmMeasure P)| ≤
              C * (N : ℝ) ^ (-convergenceRate s.val + ε) * blockDerivativeNorm G := by
  obtain ⟨ζ, A, hζ, _, hA, hrate⟩ := rate s.val ε s.property.1 hε
  obtain ⟨C, hC, hcomp⟩ := OrdinaryGapCauchyV2.ordinary_gap_cauchy_locallyUniform
    s ζ hζ βlo βhi hlo hle
  refine ⟨C * A, mul_pos hC hA, ?_⟩
  intro p hps hpl hph
  obtain ⟨h, _, _, hreg⟩ := convergence_from_cauchy_internal Riesz2.ordinaryGapCauchy hlog p
  obtain ⟨q, hq, hgap⟩ := palm_gap_limit_internal Riesz2.ordinaryGapCauchy hlog p h
  have hcomp := hcomp p hps hpl hph
  rw [← hps] at hcomp hrate ⊢
  refine ⟨h, hreg, ?_⟩
  intro N K hK G
  obtain ⟨n, hn4, hKn, hnN, hpower, hlower, _⟩ := scale p.val.2 p.property.2.1 N K hK
  obtain ⟨H, J, hJ, hH, hnorm, he⟩ := middle_block hKn G
  have hN2 : 2 ≤ (N : ℕ) := by omega
  have hprob := gibbsMeasure_probability p N
  obtain ⟨hi, ht⟩ := block_integral_tendsto p q hq G
  obtain ⟨hiP, heP⟩ := palm_block_integral_internal _ q hgap G hi
  refine ⟨InterpolatingDensities.block_integrable N K G _, hiP, ?_⟩
  rw [heP]
  have hb : |(∫ X : Riesz1.Configuration N, G.val (finiteGapBlock X) ∂gibbsMeasure p N) -
        (∫ y : ℤ → Ioi (0 : ℝ), G.val (fun j => (y (j.val : ℤ) : ℝ)) ∂q)| ≤
      C * (n : ℝ) ^ (-min p.val.2 1 / 2 + ζ) * blockDerivativeNorm G := by
    apply le_of_tendsto ((tendsto_const_nhds.sub ht).abs)
    filter_upwards [eventually_ge_atTop (N : ℕ)] with m hm
    have hN' : (N : ℕ) ≤ (m.succPNat : ℕ) := by simp only [Nat.succPNat_coe]; omega
    have hh := (hcomp n N m.succPNat (by omega) hN' hnN hpower H J hJ hH).2.2
    rw [he p N hN2, he p m.succPNat (by simp only [Nat.succPNat_coe]; omega)] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hnorm (by positivity))
  calc
    _ ≤ _ := hb
    _ ≤ C * (A * (N : ℝ) ^ (-convergenceRate p.val.2 + ε)) * blockDerivativeNorm G := by
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _)
      exact mul_le_mul_of_nonneg_left (hrate N n hlower) hC.le
    _ = _ := by ring


end Riesz2.QuantitativeConvergenceResult
