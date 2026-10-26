/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.FixedLengthDecayPart5
public import Riesz2.Thermodynamic.IntegratedCovariancePart2
public import Riesz2.Thermodynamic.InterpolantLocalLawsPart11
public import Riesz2.Frozen.RestrictedBlockDerivativeNorm
public import Riesz2.ToMathlib.GoodSetL2Comparison
public import Riesz2.ToMathlib.WeightedWeakSuperposition

/-!
# Compatible conditional comparison

Steps of the proof of Proposition 6.6. The pairing estimate uses the two conclusions of
Lemma 6.4 with the boundary weights defined in the code.
-/

public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter ProbabilityTheory
open scoped BigOperators ENNReal NNReal ContDiff

namespace Riesz2.CompatibleComparison

/-- See the proof of Proposition 6.6 in the paper: the finite-period error has
at least the required decay, including the smallest active block. -/
theorem period_error_le_rate (s : ℝ) (hs : 0 < s) (n N : ℕ+)
    (hsize : (n : ℝ) ^ (2 / s) ≤ (N : ℝ)) :
    (n : ℝ) * (N : ℝ) ^ (-s) ≤ (n : ℝ) ^ (-min s 1 / 2) := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  calc
    _ ≤ (n : ℝ)⁻¹ := InteractionDifferential.period_error_le hs
      (by exact_mod_cast n.pos) (by exact_mod_cast N.pos) hsize
    _ = (n : ℝ) ^ (-1 : ℝ) := (Real.rpow_neg_one _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn (by linarith [min_le_right s 1])

/-- See the proof of Proposition 6.6 and Lemma 6.5 of the paper: on a common
length fibre the fine event is independent of the volume cutoff. This
uses the event rather than introducing another rigidity set. -/
theorem fine_event_on_common_fibre (s η : ℝ) (n N M : ℕ+) {L : ℝ}
    (hLN : L < (N : ℝ)) (hLM : L < (M : ℝ))
    {x : Fin (n : ℕ) → ℝ} (hx : ∑ i, x i = L) :
    x ∈ goodBlockEvent s n N η ↔ x ∈ goodBlockEvent s n M η := by
  rw [InterpolantLocalLaws.goodBlockEvent_on_length s n N η L hLN x hx,
    InterpolantLocalLaws.goodBlockEvent_on_length s n M η L hLM x hx]

/-- See the proof of Proposition 6.6 in the paper: in the small-tolerance range,
the total-interval rigidity bound makes the volume cutoff redundant on
the entire active carrier, not just on a fixed hyperplane. Thus the
restricted derivative norm can be used without a volume cutoff. -/
theorem fine_event_without_volume_cutoff (s η : ℝ) (n N : ℕ+)
    (hη : η + min s 1 / 2 ≤ 1) (hN : 2 * (n : ℝ) < (N : ℝ))
    (x : Fin (n : ℕ) → ℝ) :
    x ∈ goodBlockEvent s n N η ↔
      (∀ i, (n : ℝ) ^ (-η) ≤ x i ∧ x i ≤ (n : ℝ) ^ η) ∧
      ∀ a b : ℕ, a < b → b ≤ (n : ℕ) →
        |(∑ i ∈ Finset.univ.filter (fun i : Fin (n : ℕ) => a ≤ i.val ∧ i.val < b), x i) -
          (b - a : ℕ)| ≤ (n : ℝ) ^ η * (b - a : ℕ) ^ (min s 1 / 2) := by
  constructor
  · exact fun hx => hx.2
  · intro hx
    refine ⟨?_, hx⟩
    have hh := hx.2 0 (n : ℕ) n.pos (le_refl _)
    have hfilter : Finset.univ.filter (fun i : Fin (n : ℕ) =>
        0 ≤ i.val ∧ i.val < (n : ℕ)) = Finset.univ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact iff_true_intro ⟨Nat.zero_le _, i.isLt⟩
    rw [hfilter, Nat.sub_zero] at hh
    have hn : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
    have hp : (n : ℝ) ^ η * (n : ℝ) ^ (min s 1 / 2) ≤ (n : ℝ) := by
      rw [← Real.rpow_add (zero_lt_one.trans_le hn)]
      exact (Real.rpow_le_rpow_of_exponent_le hn hη).trans_eq (Real.rpow_one _)
    have hsum : (∑ i, x i) ≤ 2 * (n : ℝ) := by
      have hh' := (le_abs_self ((∑ i, x i) - (n : ℝ))).trans hh
      linarith
    exact hsum.trans_lt hN

/-- See Lemma 6.5 of the paper: in the range of compatible comparison, the
good event and hence its restricted coordinate norm are literally
independent of the chosen large enclosing volume. -/
theorem fine_event_large_volume_eq (s η : ℝ) (n N M : ℕ+)
    (hη : η + min s 1 / 2 ≤ 1)
    (hN : 2 * (n : ℝ) < (N : ℝ)) (hM : 2 * (n : ℝ) < (M : ℝ)) :
    goodBlockEvent s n N η = goodBlockEvent s n M η := by
  ext x
  rw [fine_event_without_volume_cutoff s η n N hη hN,
    fine_event_without_volume_cutoff s η n M hη hM]

section Pairing

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} [IsProbabilityMeasure ν]

/-- Internal analytic assembly for the proof of Proposition 6.6.
The hypothesis `hDecay` is precisely the weighted and unweighted
conclusions of Lemma 6.4, for this bounded L² source. The coefficient
and exceptional envelope are those supplied by the interaction differential. The supremum estimate is supplied separately by the maximum principle.
The source L² norm is then localized to the same fine good set. -/
theorem pairing_from_decay_internal
    (s : ℝ) (hs : 0 < s) (n N : ℕ+)
    (hsize : (n : ℝ) ^ (2 / s) ≤ (N : ℝ))
    (χ : BoundedL2Pairings.boundedSubmodule ν)
    (ψ : Fin (n : ℕ) → Lp ℝ 2 ν)
    (b : Fin (n : ℕ) → X → ℝ) (W : X → ℝ)
    (hb : ∀ j, AEStronglyMeasurable (b j) ν)
    {G : Set X} (hG : MeasurableSet G)
    (A B Ab Kb T C κ ε c δ U : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAb : 0 ≤ Ab)
    (hKb : 0 ≤ Kb) (_hT : 0 ≤ T) (hC : 0 ≤ C) (hU : 0 ≤ U)
    (hχgood : ∀ᵐ x ∂ν.restrict G, |χ.val x| ≤ A)
    (hχglobal : ∀ᵐ x ∂ν, |χ.val x| ≤ B)
    (hgood : ∀ j, ∀ᵐ x ∂ν.restrict G, |b j x| ≤
      Ab * (InteractionDifferential.boundaryWeight s n j +
        (n : ℝ) * (N : ℝ) ^ (-s)))
    (hW : IntegrableOn W Gᶜ ν)
    (hsq : ∀ j, ∀ᵐ x ∂ν.restrict Gᶜ, b j x ^ 2 ≤ Kb * W x)
    (htail : (∫ x in Gᶜ, W x ∂ν) ≤ T) (hprob : ν.real Gᶜ ≤ T)
    (hψsup : ∀ j, ∀ᵐ x ∂ν, |ψ j x| ≤
      U * (eLpNorm (χ.val : X → ℝ) ∞ ν).toReal)
    (hDecay :
      (∑ j, InteractionDifferential.boundaryWeight s n j * ‖ψ j‖) ≤
        C * (n : ℝ) ^ (κ * ε - min s 1 / 2) *
          (‖χ.val‖ + Real.exp (-c * (n : ℝ) ^ δ) *
            (eLpNorm (χ.val : X → ℝ) ∞ ν).toReal) ∧
      (∑ j, ‖ψ j‖) ≤ C * (n : ℝ) ^ (κ * ε) *
          (‖χ.val‖ + Real.exp (-c * (n : ℝ) ^ δ) *
            (eLpNorm (χ.val : X → ℝ) ∞ ν).toReal)) :
    Integrable (fun x => ∑ j, b j x * ψ j x) ν ∧
      |∫ x, ∑ j, b j x * ψ j x ∂ν| ≤
        2 * Ab * C * (n : ℝ) ^ (κ * ε - min s 1 / 2) *
          (A + (Real.sqrt T + Real.exp (-c * (n : ℝ) ^ δ)) * B) +
        (n : ℝ) * U * B * Real.sqrt (Kb * T) := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast n.pos
  have hρ : 0 ≤ (n : ℝ) * (N : ℝ) ^ (-s) := by positivity
  have hBχ := BoundedL2Pairings.essentialNorm_le χ B hB hχglobal
  have hsource := GoodSetL2Comparison.source_norm_le χ.val hG hA hB hχgood hχglobal
  have hsource' : ‖χ.val‖ ≤ A + B * Real.sqrt T :=
    hsource.trans (add_le_add (le_refl A) (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt hprob) hB))
  have hF : ‖χ.val‖ + Real.exp (-c * (n : ℝ) ^ δ) *
      (eLpNorm (χ.val : X → ℝ) ∞ ν).toReal ≤
        A + (Real.sqrt T + Real.exp (-c * (n : ℝ) ^ δ)) * B := by
    have hh := add_le_add hsource'
      (mul_le_mul_of_nonneg_left hBχ (Real.exp_pos (-c * (n : ℝ) ^ δ)).le)
    nlinarith only [hh]
  have hweight := hDecay.1.trans (mul_le_mul_of_nonneg_left hF (by positivity))
  have hunweight := hDecay.2.trans (mul_le_mul_of_nonneg_left hF (by positivity))
  have hperiod := period_error_le_rate s hs n N hsize
  have hprofile : (∑ j, InteractionDifferential.boundaryWeight s n j * ‖ψ j‖) +
      (n : ℝ) * (N : ℝ) ^ (-s) * ∑ j, ‖ψ j‖ ≤
        2 * C * (n : ℝ) ^ (κ * ε - min s 1 / 2) *
          (A + (Real.sqrt T + Real.exp (-c * (n : ℝ) ^ δ)) * B) := by
    have htail' := mul_le_mul_of_nonneg_left hunweight hρ
    have hperiod' := mul_le_mul_of_nonneg_right hperiod
      (show 0 ≤ C * (n : ℝ) ^ (κ * ε) *
        (A + (Real.sqrt T + Real.exp (-c * (n : ℝ) ^ δ)) * B) by positivity)
    have he : (n : ℝ) ^ (-min s 1 / 2) *
        (C * (n : ℝ) ^ (κ * ε) *
          (A + (Real.sqrt T + Real.exp (-c * (n : ℝ) ^ δ)) * B)) =
        C * (n : ℝ) ^ (κ * ε - min s 1 / 2) *
          (A + (Real.sqrt T + Real.exp (-c * (n : ℝ) ^ δ)) * B) := by
      rw [show κ * ε - min s 1 / 2 = (-min s 1 / 2) + κ * ε by ring,
        Real.rpow_add hn]
      ring
    rw [he] at hperiod'
    nlinarith only [hweight, htail', hperiod']
  obtain ⟨hi, hp⟩ := GoodSetL2Comparison.vector_pairing_le b W hb ψ hG
    (InteractionDifferential.boundaryWeight s n)
    (fun j => (InteractionDifferential.boundaryWeight_pos s n j).le)
    hAb hρ (mul_nonneg hU hB) hKb hgood
    (fun j => (hψsup j).mono fun x hx => hx.trans (mul_le_mul_of_nonneg_left hBχ hU))
    hW hsq htail
  refine ⟨hi, hp.trans ?_⟩
  simp only [Fintype.card_fin]
  have hh := mul_le_mul_of_nonneg_left hprofile hAb
  nlinarith only [hh]

end Pairing

/-- Internal time integration in the proof of Proposition 6.6.
Uniform bounds on a finite sum of coordinate pairings integrate without
a factor depending on the number of source coordinates. -/
theorem integrate_coordinate_pairings_internal {ι : Type*} [Fintype ι]
    (J : Finset ι) (h : ℝ → ℝ) (a : ι → ℝ → ℝ)
    (β P E : ℝ) (hβ : 0 ≤ β)
    (D B : ι → ℝ)
    (hid : h 1 - h 0 = β * ∫ t in (0 : ℝ)..1, ∑ i ∈ J, a i t)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i ∈ J,
      |a i t| ≤ P * (D i + E * B i)) :
    |h 1 - h 0| ≤ β * P * ((∑ i ∈ J, D i) + E * ∑ i ∈ J, B i) := by
  have hh : |∫ t in (0 : ℝ)..1, ∑ i ∈ J, a i t| ≤
      P * ((∑ i ∈ J, D i) + E * ∑ i ∈ J, B i) := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1)
      (f := fun t => ∑ i ∈ J, a i t) (C := P * ((∑ i ∈ J, D i) + E * ∑ i ∈ J, B i))
      (fun t ht => ?_)
    · simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using hi
    · have ht' : t ∈ Icc (0 : ℝ) 1 := by
        have ht'' : t ∈ Ioc (0 : ℝ) 1 := by
          simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
        exact ⟨ht''.1.le, ht''.2⟩
      rw [Real.norm_eq_abs]
      calc
        _ ≤ ∑ i ∈ J, |a i t| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ J, P * (D i + E * B i) := Finset.sum_le_sum fun i hi => hbound t ht' i hi
        _ = _ := by simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
  rw [hid, abs_mul, abs_of_nonneg hβ]
  exact (mul_le_mul_of_nonneg_left hh hβ).trans_eq (by ring)

/-- See the proof of Proposition 6.6 in the paper: a block observable is
bounded on every positive length simplex by its literal coordinate norm.
The bound is valid on the whole fibre, including arbitrarily small gaps. -/
theorem block_bound_on_simplex (n : ℕ) {L : ℝ} (_hL : 0 < L)
    (G : BlockObservable n.succPNat)
    (x : EuclideanSpace ℝ (Fin (n + 1))) (hx : x ∈ AffineSimplex.massSimplex n L) :
    |G.val (WithLp.ofLp x)| ≤ |G.val 0| + blockDerivativeNorm G * L := by
  have hb := InterpolatingDensities.block_bound G 0 (WithLp.ofLp x)
  have hcoord (j : Fin (n + 1)) : |x j| ≤ L := by
    rw [abs_of_pos (hx.1 j)]
    have hh := Finset.single_le_sum (s := Finset.univ) (f := fun i => x i)
      (fun i _ => (hx.1 i).le) (Finset.mem_univ j)
    exact hh.trans_eq hx.2
  have hs : (∑ j, (coordinateDerivativeNorm G j : ℝ) *
      |(WithLp.ofLp x) j - (0 : Fin (n.succPNat : ℕ) → ℝ) j|) ≤
        blockDerivativeNorm G * L := by
    unfold blockDerivativeNorm
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    simpa using mul_le_mul_of_nonneg_left (hcoord j) (coordinateDerivativeNorm G j).property
  have hh : |G.val (WithLp.ofLp x)| ≤ |G.val (WithLp.ofLp x) - G.val 0| + |G.val 0| := by
    simpa only [sub_add_cancel] using abs_add_le (G.val (WithLp.ofLp x) - G.val 0) (G.val 0)
  linarith only [hb, hs, hh]

/-- See Lemma 6.1 of the paper, used in
the proof of Proposition 6.6, for the Lipschitz observable.
All endpoint moments and the time integral are finite. A bounded clamp
equal to the observable on the whole simplex permits direct reuse of the
common-barrier differentiation theorem. -/
theorem integrated_block_identity (p : Parameters) (n m r : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin ((n + 1) + m + 1)))
    (τ : Equiv.Perm (Fin ((n + 1) + r + 1))) {L : ℝ} (hL : 0 < L)
    (y : EuclideanSpace ℝ (Fin (m + 1))) (hy : ∀ j, 0 < y j)
    (z : EuclideanSpace ℝ (Fin (r + 1))) (hz : ∀ j, 0 < z j)
    (hcompatY : L + ∑ j, y j = ((n + 1 + m : ℕ) + 1 : ℝ))
    (hcompatZ : L + ∑ j, z j = ((n + 1 + r : ℕ) + 1 : ℝ))
    (θ : PhysicalCutoff) (ε : ℝ) (hε : 0 < ε)
    (G : BlockObservable n.succPNat) :
    let Ω := AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L
    ∃ Ky Kz : AffineSimplex.Tangent n → ℝ,
      (∀ w (hw : w ∈ Ω), Ky w = physicalAmbientGapEnergy p (n + 1 + m).succPNat
        ⟨RetainedSimplex.assemble (n + 1) m σ (AffineSimplex.centredChart n L w) y,
          PhysicalEnergy.simplex_subset_ambient _ _ (by
            have hh := ConditionalWellPosedness.assemble_fixed_exterior_mem n m σ y hy hcompatY hw
            rw [AffineSimplex.massSimplex_physical] at hh
            exact hh)⟩) ∧
      (∀ w (hw : w ∈ Ω), Kz w = physicalAmbientGapEnergy p (n + 1 + r).succPNat
        ⟨RetainedSimplex.assemble (n + 1) r τ (AffineSimplex.centredChart n L w) z,
          PhysicalEnergy.simplex_subset_ambient _ _ (by
            have hh := ConditionalWellPosedness.assemble_fixed_exterior_mem n r τ z hz hcompatZ hw
            rw [AffineSimplex.massSimplex_physical] at hh
            exact hh)⟩) ∧
      let μ : Measure Ω := volume.comap Subtype.val
      let P := fun w : AffineSimplex.Tangent n => ∑ i,
        (θ.val (((n + 1 : ℕ) : ℝ) ^ (-ε) * AffineSimplex.centredChart n L w i) +
          θ.val (((n + 1 : ℕ) : ℝ) ^ (-ε) * (AffineSimplex.centredChart n L w i)⁻¹))
      let V := fun t w => p.val.1 * (P w + (1 - t) * Ky w + t * Kz w)
      let ν := fun t => μ.tilted (fun w : Ω => -V t w.val)
      let g := fun w : Ω => G.val (WithLp.ofLp (AffineSimplex.centredChart n L w.val))
      let D := fun w : Ω => Ky w.val - Kz w.val
      ∃ δ : ℝ, 0 < δ ∧
        ContDiffOn ℝ ∞ (fun t => ∫ w, g w ∂ν t) (Ioo (-δ) (1 + δ)) ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          Integrable (fun w : Ω => Real.exp (-V t w.val)) μ ∧
          (0 < ∫ w, Real.exp (-V t w.val) ∂μ) ∧
          (∃ h0 ht, ν t = AffineFibre.normalizedMeasure μ
            (fun w : Ω => ENNReal.ofReal (Real.exp (-V t w.val))) h0 ht) ∧
          IsProbabilityMeasure (ν t) ∧
          MemLp g 2 (ν t) ∧ MemLp D 2 (ν t) ∧
          HasDerivAt (fun u => ∫ w, g w ∂ν u) (p.val.1 * covariance g D (ν t)) t) ∧
        IntervalIntegrable (fun t => covariance g D (ν t)) volume 0 1 ∧
        (∫ w, g w ∂ν 1) - (∫ w, g w ∂ν 0) =
          p.val.1 * ∫ t in (0 : ℝ)..1, covariance g D (ν t) := by
  intro Ω
  let M := |G.val 0| + blockDerivativeNorm G * L
  have hM : 0 ≤ M := by
    dsimp only [M, blockDerivativeNorm]
    positivity
  let F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ :=
    fun x => max (-M) (min M (G.val (WithLp.ofLp x)))
  obtain ⟨LG, hLG⟩ := G.property
  have hFG : Measurable (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
      G.val (WithLp.ofLp x)) := hLG.continuous.measurable.comp
        (PiLp.continuous_ofLp 2 (fun _ : Fin (n + 1) => ℝ)).measurable
  have hF : Measurable F := measurable_const.max (measurable_const.min hFG)
  have hFb : ∀ x, |F x| ≤ M := fun x => abs_le.mpr
    ⟨le_max_left _ _, max_le (by linarith only [hM]) (min_le_left _ _)⟩
  have he : ∀ x ∈ AffineSimplex.massSimplex n L,
      F x = G.val (WithLp.ofLp x) := by
    intro x hx
    have hh := abs_le.mp (block_bound_on_simplex n hL G x hx)
    dsimp only [F]
    rw [min_eq_right hh.2, max_eq_right hh.1]
  obtain ⟨Ky, Kz, hKy, hKz, hrest⟩ := IntegratedCovariance.integrated_representation p n m r hn
    σ τ hL y hy z hz hcompatY hcompatZ θ ε hε F hF ⟨M, hFb⟩
  refine ⟨Ky, Kz, hKy, hKz, ?_⟩
  have hg (w : Ω) : F (AffineSimplex.centredChart n L w.val) =
      G.val (WithLp.ofLp (AffineSimplex.centredChart n L w.val)) := he _ w.property
  simpa only [hg] using hrest

/-- See Lemma 6.5 of the paper: each infimum in the restricted
derivative sum is attained. The global coordinate constant proves
nonemptiness, even when the restricted set has no coordinate segments. -/
theorem restricted_coordinate_bound_internal {n : ℕ+} (G : BlockObservable n)
    (A : Set (Fin (n : ℕ) → ℝ)) (j : Fin (n : ℕ))
    (x : Fin (n : ℕ) → ℝ) (t : ℝ) (hx : x ∈ A) (ht : Function.update x j t ∈ A) :
    |G.val (Function.update x j t) - G.val x| ≤
      ((sInf {L : ℝ≥0 | ∀ (y : Fin (n : ℕ) → ℝ) (u : ℝ),
        y ∈ A → Function.update y j u ∈ A →
        |G.val (Function.update y j u) - G.val y| ≤ (L : ℝ) * |u - y j|} : ℝ≥0) : ℝ) *
        |t - x j| := by
  let S := {L : ℝ≥0 | ∀ (y : Fin (n : ℕ) → ℝ) (u : ℝ),
    y ∈ A → Function.update y j u ∈ A →
    |G.val (Function.update y j u) - G.val y| ≤ (L : ℝ) * |u - y j|}
  have hne : S.Nonempty := ⟨coordinateDerivativeNorm G j,
    fun y u _ _ => InterpolatingDensities.coordinate_bound G j y u⟩
  have hclosed : IsClosed S := by
    simp only [S, ofPred_forall]
    apply isClosed_iInter
    intro y
    apply isClosed_iInter
    intro u
    apply isClosed_iInter
    intro hy
    apply isClosed_iInter
    intro hu
    exact isClosed_le continuous_const (continuous_subtype_val.mul_const _)
  exact (hclosed.csInf_mem hne (OrderBot.bddBelow S)) x t hx ht

/-- See Lemma 6.5 of the paper: the classical partial derivative at an
interior point is bounded by the literal restricted coordinate infimum.
This is a local one-dimensional difference-quotient argument. -/
theorem restricted_partial_interior_internal {n : ℕ+} (G : BlockObservable n)
    (A : Set (Fin (n : ℕ) → ℝ)) (j : Fin (n : ℕ))
    {x : Fin (n : ℕ) → ℝ} (hx : x ∈ interior A)
    (hd : DifferentiableAt ℝ G.val x) :
    |fderiv ℝ G.val x (Pi.single j 1)| ≤
      ((sInf {L : ℝ≥0 | ∀ (y : Fin (n : ℕ) → ℝ) (u : ℝ),
        y ∈ A → Function.update y j u ∈ A →
        |G.val (Function.update y j u) - G.val y| ≤ (L : ℝ) * |u - y j|} : ℝ≥0) : ℝ) := by
  let C : ℝ≥0 := sInf {L : ℝ≥0 | ∀ (y : Fin (n : ℕ) → ℝ) (u : ℝ),
    y ∈ A → Function.update y j u ∈ A →
    |G.val (Function.update y j u) - G.val y| ≤ (L : ℝ) * |u - y j|}
  have hder := hd.hasFDerivAt.comp_hasDerivAt_of_eq (x j)
    (hasDerivAt_update x j (x j)) (Function.update_eq_self j x).symm
  change HasDerivAt (fun t => G.val (Function.update x j t))
    (fderiv ℝ G.val x (Pi.single j 1)) (x j) at hder
  have hn : ∀ᶠ t in nhds (x j), Function.update x j t ∈ A := by
    have hc : Continuous (Function.update x j) := by fun_prop
    have htend : Tendsto (Function.update x j) (nhds (x j)) (nhds x) := by
      simpa only [ContinuousAt, Function.update_eq_self] using hc.continuousAt (x := x j)
    exact htend.eventually (mem_interior_iff_mem_nhds.mp hx)
  have hh := norm_deriv_le_of_lip' (f := fun t => G.val (Function.update x j t)) C.property
    (hn.mono fun t ht => by
      simpa [Real.norm_eq_abs, C] using
        restricted_coordinate_bound_internal G A j x t (interior_subset hx) ht)
  rw [hder.deriv, Real.norm_eq_abs] at hh
  exact hh

/-- See Lemma 6.5 of the paper, the smooth boundary step used in
the proof of Proposition 6.6: continuity extends the restricted partial
bound from the interior of a convex set to every point of that set. -/
theorem smooth_derivative_sum_le_restricted {n : ℕ+} (G : BlockObservable n)
    (hG : ContDiff ℝ 1 G.val) (J : Finset (Fin (n : ℕ)))
    (A : Set (Fin (n : ℕ) → ℝ)) (hA : Convex ℝ A)
    (hne : (interior A).Nonempty) {x : Fin (n : ℕ) → ℝ} (hx : x ∈ A) :
    (∑ j ∈ J, |fderiv ℝ G.val x (Pi.single j 1)|) ≤ restrictedBlockDerivativeNorm G J A := by
  unfold restrictedBlockDerivativeNorm
  apply Finset.sum_le_sum
  intro j _
  let C : ℝ≥0 := sInf {L : ℝ≥0 | ∀ (y : Fin (n : ℕ) → ℝ) (u : ℝ),
    y ∈ A → Function.update y j u ∈ A →
    |G.val (Function.update y j u) - G.val y| ≤ (L : ℝ) * |u - y j|}
  have hc : Continuous (fun y => |fderiv ℝ G.val y (Pi.single j 1)|) :=
    ((hG.continuous_fderiv (by norm_num)).clm_apply continuous_const).abs
  have hsub : interior A ⊆ {y | |fderiv ℝ G.val y (Pi.single j 1)| ≤ (C : ℝ)} :=
    fun y hy => restricted_partial_interior_internal G A j hy (hG.differentiable (by norm_num) y)
  have hcl := closure_minimal hsub (isClosed_le hc continuous_const)
  apply hcl
  rw [hA.closure_interior_eq_closure_of_nonempty_interior hne]
  exact subset_closure hx

/-- Internal exponential bookkeeping for the proof of Proposition 6.6. The exceptional first moment and the
localized source norm retain the same tail power after polynomial
absorption. Both constants precede the size and the observable bounds. -/
theorem pairing_rate_absorption_internal (Cg U Q T c ct δ q r : ℝ)
    (hCg : 0 < Cg) (hU : 0 ≤ U) (hQ : 0 ≤ Q) (hT : 0 ≤ T)
    (hc : 0 < c) (hct : 0 < ct) (hδ : 0 < δ) :
    ∃ C cf : ℝ, 0 < C ∧ 0 < cf ∧ ∀ n : ℝ, 1 ≤ n →
      ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      Cg * n ^ q * (A + (Real.sqrt (T * Real.exp (-ct * n ^ δ)) +
        Real.exp (-c * n ^ δ)) * B) +
        U * n ^ r * Real.sqrt (Q * T * Real.exp (-ct * n ^ δ)) * B ≤
      C * n ^ q * (A + Real.exp (-cf * n ^ δ) * B) := by
  obtain ⟨M, hM, hm⟩ := GoodSetL2Comparison.sqrt_tail_absorption
    (A := T) (a := 0) hT hct hδ
  obtain ⟨R, hR, hr⟩ := GoodSetL2Comparison.sqrt_tail_absorption
    (A := Q * T) (a := r - q) (mul_nonneg hQ hT) hct hδ
  let cf := min c (ct / 4)
  let C := Cg + Cg * (M + 1) + U * R + 1
  have hcf : 0 < cf := lt_min hc (by positivity)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, cf, hC, hcf, fun n hn A B hA hB => ?_⟩
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hexp : Real.exp (-c * n ^ δ) ≤ Real.exp (-cf * n ^ δ) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left c (ct / 4))) (by positivity)
  have hctexp : Real.exp (-(ct / 4) * n ^ δ) ≤ Real.exp (-cf * n ^ δ) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right c (ct / 4))) (by positivity)
  have hsource : Real.sqrt (T * Real.exp (-ct * n ^ δ)) + Real.exp (-c * n ^ δ) ≤
      (M + 1) * Real.exp (-cf * n ^ δ) := by
    have hh := hm n hn
    rw [Real.rpow_zero, one_mul] at hh
    have hh' := mul_le_mul_of_nonneg_left hctexp hM.le
    nlinarith only [hh, hh', hexp]
  have hbad : n ^ r * Real.sqrt (Q * T * Real.exp (-ct * n ^ δ)) ≤
      n ^ q * R * Real.exp (-cf * n ^ δ) := by
    have hh := mul_le_mul_of_nonneg_left (hr n hn) (Real.rpow_nonneg hn0.le q)
    have he : n ^ q * n ^ (r - q) = n ^ r := by
      rw [← Real.rpow_add hn0]
      congr 1
      ring
    rw [← mul_assoc, he] at hh
    exact hh.trans (by
      have hh' := mul_le_mul_of_nonneg_left hctexp
        (show 0 ≤ n ^ q * R by positivity)
      nlinarith only [hh'])
  have hmain := mul_le_mul_of_nonneg_left
    (add_le_add (le_refl A) (mul_le_mul_of_nonneg_right hsource hB))
    (show 0 ≤ Cg * n ^ q by positivity)
  have hbad' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbad hB) hU
  have hCA : Cg ≤ C := by
    have hh : 0 ≤ Cg * (M + 1) + U * R + 1 := by positivity
    dsimp only [C]
    linarith only [hh]
  have hCB : Cg * (M + 1) + U * R ≤ C := by dsimp only [C]; linarith
  have hfirst := mul_le_mul_of_nonneg_right hCA (show 0 ≤ n ^ q * A by positivity)
  have hsecond := mul_le_mul_of_nonneg_right hCB
    (show 0 ≤ n ^ q * Real.exp (-cf * n ^ δ) * B by positivity)
  nlinarith only [hmain, hbad', hfirst, hsecond]

/-- Internal source decomposition in the proof of Proposition 6.6: solve each supported coordinate source on
the same full tangent domain. Their sum is exactly the solution with the
whole supported source, by the existing coercive uniqueness theorem. -/
theorem point_sources_superpose_internal
    {X : Type*} [MeasurableSpace X] {ν : Measure X}
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q) (n : ℕ+)
    (H : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (hH : ∀ᵐ x ∂ν, (H x).PosSemidef)
    (hHm : ∀ i j, Measurable (fun x => H x i j))
    (a : ℝ) (ha : 0 < a)
    (hcoerc : ∀ᵐ x ∂ν, ∀ v ∈ zeroSumComponents (Fin (n : ℕ)),
      a * (∑ i, v i ^ 2) ≤ ∑ i, ∑ j, v i * H x i j * v j)
    (J : Finset (Fin (n : ℕ))) (χ : Fin (n : ℕ) → Lp ℝ 2 ν)
    (ψ : Fin (n : ℕ) → Fin (n : ℕ) → Q.1)
    (hψ : ∀ i ∈ J, WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ)))
      (fun j => if j = i then χ i else 0) (ψ i))
    (Ψ : Fin (n : ℕ) → Q.1)
    (hΨ : WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ)))
      (fun i => if i ∈ J then χ i else 0) Ψ) :
    Ψ = ∑ i ∈ J, ψ i := by
  have hs := WeightedWeakSuperposition.finset_sum Q hQ H
    (zeroSumComponents (Fin (n : ℕ))) hH a ha hcoerc hHm J
    (fun i j => if j = i then χ i else 0) ψ hψ
  have he : (∑ i ∈ J, fun j => if j = i then χ i else 0) =
      (fun i => if i ∈ J then χ i else 0) := by
    funext j
    simp [Finset.sum_apply, eq_comm]
  rw [he] at hs
  exact (MatrixEnergy.weightedWeakSolution_unique Q hQ H _ hH a ha hcoerc hHm _ Ψ hΨ).trans
    (MatrixEnergy.weightedWeakSolution_unique Q hQ H _ hH a ha hcoerc hHm _ _ hs).symm

/-- See Subsection 6.1 of the paper: the ordinary-interval cardinality appearing
in the fine event, including the whole active interval. -/
theorem ordinary_interval_card_internal (n a b : ℕ) (hab : a ≤ b) (hb : b ≤ n) :
    (Finset.univ.filter (fun i : Fin n => a ≤ i.val ∧ i.val < b)).card = b - a := by
  classical
  have hsub : Finset.univ.filter (fun i : Fin n => i.val < a) ⊆
      Finset.univ.filter (fun i : Fin n => i.val < b) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    omega
  have he : Finset.univ.filter (fun i : Fin n => a ≤ i.val ∧ i.val < b) =
      Finset.univ.filter (fun i : Fin n => i.val < b) \
        Finset.univ.filter (fun i : Fin n => i.val < a) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    omega
  rw [he, Finset.card_sdiff_of_subset hsub, Fin.card_filter_val_lt,
    Fin.card_filter_val_lt, min_eq_right hb, min_eq_right (hab.trans hb)]

/-- See Subsection 6.1 and Lemma 6.5 of the paper: the all-one active vector is an
interior point of the good set when the block has at least two
gaps. This provides the full-dimensional interior needed for the
restricted derivative norm, independently of a length hyperplane. -/
theorem one_mem_interior_fine_event (s η : ℝ) (hη : 0 < η) (n N : ℕ+)
    (hn : 2 ≤ (n : ℕ)) (hN : (n : ℕ) < (N : ℕ)) :
    (fun _ : Fin (n : ℕ) => (1 : ℝ)) ∈ interior (goodBlockEvent s n N η) := by
  let U : Set (Fin (n : ℕ) → ℝ) := {x |
    (∑ i, x i) < (N : ℝ) ∧
    (∀ i, (n : ℝ) ^ (-η) < x i ∧ x i < (n : ℝ) ^ η) ∧
    ∀ a b : Fin ((n : ℕ) + 1), a.val < b.val →
      |(∑ i ∈ Finset.univ.filter (fun i : Fin (n : ℕ) => a.val ≤ i.val ∧ i.val < b.val), x i) -
        (b.val - a.val : ℕ)| < (n : ℝ) ^ η * (b.val - a.val : ℕ) ^ (min s 1 / 2)}
  have ho : IsOpen U := by
    simp only [U, ofPred_and, ofPred_forall]
    refine (isOpen_lt (by fun_prop) continuous_const).inter (?_)
    refine (isOpen_iInter_of_finite fun i =>
      (isOpen_lt continuous_const (continuous_apply i)).inter
        (isOpen_lt (continuous_apply i) continuous_const)).inter ?_
    apply isOpen_iInter_of_finite
    intro a
    apply isOpen_iInter_of_finite
    intro b
    apply isOpen_iInter_of_finite
    intro hab
    exact isOpen_lt (by fun_prop) continuous_const
  have hU : (fun _ : Fin (n : ℕ) => (1 : ℝ)) ∈ U := by
    have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < (n : ℕ) by omega)
    refine ⟨?_, fun i => ⟨Real.rpow_lt_one_of_one_lt_of_neg hn' (by linarith),
      Real.one_lt_rpow hn' hη⟩, ?_⟩
    · simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        using (show (n : ℝ) < (N : ℝ) by exact_mod_cast hN)
    · intro a b hab
      rw [Finset.sum_const, ordinary_interval_card_internal (n : ℕ) a.val b.val hab.le
        (by have := b.isLt; omega), nsmul_eq_mul, mul_one, sub_self, abs_zero]
      apply mul_pos (Real.rpow_pos_of_pos (by exact_mod_cast n.pos) η)
      apply Real.rpow_pos_of_pos
      exact_mod_cast (show 0 < b.val - a.val by omega)
  have hUG : U ⊆ goodBlockEvent s n N η := by
    intro x hx
    refine ⟨hx.1, fun i => ⟨(hx.2.1 i).1.le, (hx.2.1 i).2.le⟩, ?_⟩
    intro a b hab hbn
    exact (hx.2.2 ⟨a, by omega⟩ ⟨b, by omega⟩ hab).le
  apply interior_mono hUG
  rwa [ho.interior_eq]

/-- See the proof of Proposition 6.6 in the paper, smooth good-set derivative
bound using the restricted norm. No extra geometric
interior hypothesis is needed for the fine rigidity event. -/
theorem smooth_fine_derivative_sum (s η : ℝ) (hη : 0 < η) (n N : ℕ+)
    (hn : 2 ≤ (n : ℕ)) (hN : (n : ℕ) < (N : ℕ))
    (G : BlockObservable n) (hG : ContDiff ℝ 1 G.val)
    (J : Finset (Fin (n : ℕ))) {x : Fin (n : ℕ) → ℝ}
    (hx : x ∈ goodBlockEvent s n N η) :
    (∑ j ∈ J, |fderiv ℝ G.val x (Pi.single j 1)|) ≤
      restrictedBlockDerivativeNorm G J (goodBlockEvent s n N η) :=
  smooth_derivative_sum_le_restricted G hG J _
    (InterpolantLocalLaws.convex_goodBlockEvent s n N η)
    ⟨_, one_mem_interior_fine_event s η hη n N hn hN⟩ hx

/-- See Theorem 4 of the paper: at every differentiability point the classical
coordinate derivative is bounded by the global coordinate norm. -/
theorem coordinate_partial_bound {n : ℕ+} (G : BlockObservable n)
    (j : Fin (n : ℕ)) {x : Fin (n : ℕ) → ℝ} (hd : DifferentiableAt ℝ G.val x) :
    |fderiv ℝ G.val x (Pi.single j 1)| ≤ (coordinateDerivativeNorm G j : ℝ) := by
  have hh := restricted_partial_interior_internal G univ j
    (x := x) (by simp only [interior_univ, mem_univ]) hd
  simpa [coordinateDerivativeNorm] using hh

end Riesz2.CompatibleComparison
