/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.InterpolatingDensities
public import Riesz2.Preliminaries.GapSymmetries
public import Riesz2.Sanity.SmoothCutoff
public import Riesz2.Frozen.MiddleConsecutiveBlock
public import Riesz2.Frozen.DependsOnBlockCoordinates
public import Riesz2.Frozen.SymmetricMiddleBlock
public import Riesz2.Frozen.RestrictedBlockDerivativeNorm
public import Riesz2.Frozen.GoodBlockEvent

/-!
# Ordinary gap expectations from the tilted comparison

See the proof of Proposition 6.6. The composition assumes the full tilted comparison.
The rounded middle block needs at most one cyclic relabelling.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace Riesz2.OrdinaryGapCauchy

/-- See the proof of Proposition 6.6 in the paper: restricted derivative sums
are bounded by the global sum, on any set. -/
theorem restricted_le_global {n : ℕ+} (G : BlockObservable n)
    (J : Finset (Fin (n : ℕ))) (A : Set (Fin (n : ℕ) → ℝ)) :
    restrictedBlockDerivativeNorm G J A ≤ blockDerivativeNorm G := by
  unfold restrictedBlockDerivativeNorm blockDerivativeNorm
  apply (Finset.sum_le_sum fun j _ => ?_).trans
    (Finset.sum_le_univ_sum_of_nonneg fun j => NNReal.coe_nonneg _)
  exact NNReal.coe_le_coe.mpr (csInf_le (OrderBot.bddBelow _)
    (fun x t _ _ => InterpolatingDensities.coordinate_bound G j x t))

/-- Relabel every coordinate of an observable by a permutation. -/
def relabel {n : ℕ+} (G : BlockObservable n) (e : Equiv.Perm (Fin (n : ℕ))) :
    BlockObservable n :=
  ⟨fun x => G.val (x ∘ e.symm), by
    obtain ⟨L, hL⟩ := G.property
    refine ⟨L * 1, hL.comp ?_⟩
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul]
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro i
    exact dist_le_pi_dist x y (e.symm i)⟩

/-- See the proof of Proposition 6.6 in the paper: coordinate updates commute
with the permutation used to embed the support. -/
theorem update_relabel {n : ℕ+} (e : Equiv.Perm (Fin (n : ℕ)))
    (x : Fin (n : ℕ) → ℝ) (j : Fin (n : ℕ)) (t : ℝ) :
    (Function.update x j t) ∘ e.symm = Function.update (x ∘ e.symm) (e j) t := by
  funext i
  by_cases hi : i = e j
  · subst i; simp
  · have hij : e.symm i ≠ j := fun h => hi (by simpa using congrArg e h)
    simp [Function.comp_apply, Function.update_of_ne hi, Function.update_of_ne hij]

/-- See the proof of Proposition 6.6 in the paper: coordinate relabelling does
not increase the global derivative sum. -/
theorem relabel_norm_le {n : ℕ+} (G : BlockObservable n)
    (e : Equiv.Perm (Fin (n : ℕ))) :
    blockDerivativeNorm (relabel G e) ≤ blockDerivativeNorm G := by
  have hc (j : Fin (n : ℕ)) :
      coordinateDerivativeNorm (relabel G e) j ≤ coordinateDerivativeNorm G (e j) := by
    apply csInf_le (OrderBot.bddBelow _)
    intro x t
    change |G.val ((Function.update x j t) ∘ e.symm) - G.val (x ∘ e.symm)| ≤ _
    rw [update_relabel]
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
      InterpolatingDensities.coordinate_bound G (e j) (x ∘ e.symm) t
  unfold blockDerivativeNorm
  calc
    _ ≤ ∑ j, (coordinateDerivativeNorm G (e j) : ℝ) :=
      Finset.sum_le_sum fun j _ => NNReal.coe_le_coe.mpr (hc j)
    _ = _ := Equiv.sum_comp e (fun j => (coordinateDerivativeNorm G j : ℝ))

/-- See the proof of Proposition 6.6 in the paper: either the support already
lies in the rounded symmetric block, or shifting it back one index does.
The latter case has no zero index, hence no wraparound in the active block. -/
theorem middle_embedding (n : ℕ+) (J : Finset (Fin (n : ℕ)))
    (hJ : MiddleConsecutiveBlock n J) :
    J ⊆ symmetricMiddleBlock n ((n : ℕ) / 4) ∨
      ∀ i ∈ J, 1 ≤ i.val ∧
        (finRotate (n : ℕ)).symm i ∈ symmetricMiddleBlock n ((n : ℕ) / 4) := by
  classical
  by_cases h : J ⊆ symmetricMiddleBlock n ((n : ℕ) / 4)
  · exact Or.inl h
  right
  obtain ⟨a, k, hk, hak, hJeq, hmiddle⟩ := hJ
  obtain ⟨j, hj, hjs⟩ := Finset.not_subset.mp h
  have hjm := hmiddle j hj
  have hjr : a ≤ j.val ∧ j.val < a + k := by simpa [hJeq] using hj
  simp only [symmetricMiddleBlock, Finset.mem_filter, Finset.mem_univ, true_and,
    not_and_or, not_le] at hjs
  intro i hi
  have him := hmiddle i hi
  have hir : a ≤ i.val ∧ i.val < a + k := by simpa [hJeq] using hi
  have hi0 : 1 ≤ i.val := by omega
  refine ⟨hi0, ?_⟩
  have hne : i ≠ 0 := by intro he; have hz : i.val = 0 := congrArg Fin.val he; omega
  simp only [symmetricMiddleBlock, Finset.mem_filter, Finset.mem_univ, true_and,
    coe_finRotate_symm_of_ne_zero hne]
  omega

/-- See the proof of Proposition 6.6 in the paper: moving a support back one
coordinate preserves its ordinary Gibbs expectation in every volume. -/
theorem integral_relabel_cycle (p : Parameters) (n N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (G : BlockObservable n) (J : Finset (Fin (n : ℕ)))
    (hG : DependsOnBlockCoordinates G J) (hJ : ∀ i ∈ J, 1 ≤ i.val) :
    (∫ X : Riesz1.Configuration N,
      (relabel G (finRotate (n : ℕ))).val (finiteGapBlock X) ∂gibbsMeasure p N) =
    ∫ X : Riesz1.Configuration N, G.val (finiteGapBlock X) ∂gibbsMeasure p N := by
  have heq (X : Riesz1.Configuration N) :
      (relabel G (finRotate (n : ℕ))).val
        (finiteGapBlock (GapSymmetries.cycleConfig X)) = G.val (finiteGapBlock X) := by
    apply hG
    intro i hi
    have hi0 := hJ i hi
    have hne : i ≠ 0 := by intro he; have hz : i.val = 0 := congrArg Fin.val he; omega
    simp only [Function.comp_apply, finiteGapBlock, GapSymmetries.gap_cycleConfig,
      coe_finRotate_symm_of_ne_zero hne]
    congr 1
    omega
  have hm : Measurable (fun X : Riesz1.Configuration N =>
      (relabel G (finRotate (n : ℕ))).val (finiteGapBlock X)) :=
    ((relabel G (finRotate (n : ℕ))).property.choose_spec.continuous.measurable).comp
      (measurable_pi_iff.mpr fun i => Riesz1.measurable_gap _)
  obtain ⟨m, hmN⟩ : ∃ m : ℕ, N = (m + 1).succPNat :=
    ⟨(N : ℕ) - 2, by apply PNat.eq; simp; omega⟩
  subst N
  calc
    _ = ∫ X, (relabel G (finRotate (n : ℕ))).val
        (finiteGapBlock (GapSymmetries.cycleConfig X)) ∂gibbsMeasure p (m + 1).succPNat := by
      rw [← integral_map GapSymmetries.measurable_cycleConfig.aemeasurable
        hm.aestronglyMeasurable, GapSymmetries.gibbsMeasure_map_cycleConfig]
    _ = _ := integral_congr_ae (ae_of_all _ heq)

/-- See the proof of Proposition 6.6 in the paper: a stretched exponential is
bounded by any prescribed power on every positive integer scale. -/
theorem exponential_le_power {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) (q : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, 1 ≤ x → Real.exp (-c * x ^ δ) ≤ B * x ^ q := by
  obtain ⟨B, hB, hb⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := -q) (c := c) (c' := 0) hδ hc
  refine ⟨B, hB, fun x hx => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hh := mul_le_mul_of_nonneg_right (hb x hx) (Real.rpow_nonneg hx0.le q)
  have he : x ^ (-q) * x ^ q = 1 := by rw [← Real.rpow_add hx0]; simp
  simpa only [neg_zero, zero_mul, Real.exp_zero, mul_one,
    mul_right_comm (x ^ (-q)), he, one_mul] using hh

/-- See the proof of Proposition 6.6 in the paper: internal assembly from the
complete tilted comparison proposition. Its conclusion has exactly the
ordinary-gap proposition's type. -/
theorem ordinary_gap_cauchy_internal
    (hcomparison :
  ∀ s : {s : ℝ // 0 < s ∧ s ≠ 1},
    ∃ Kₛ κ ε₀ : ℝ, 1 < Kₛ ∧ 0 < κ ∧ 0 < ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    ∀ θ : PhysicalCutoff, ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    let p : Parameters := ⟨(β.val, s.val), β.property, s.property⟩
    ∀ (n N N' : ℕ+) (_ : 2 ≤ (n : ℕ)),
      (N : ℕ) ≤ (N' : ℕ) → 4 * (n : ℕ) ≤ (N : ℕ) →
      (n : ℝ) ^ (2 / s.val) ≤ (N : ℝ) →
      ∀ (hn : (n : ℕ) ≤ (N : ℕ)) (hn' : (n : ℕ) ≤ (N' : ℕ)),
      let μ := tiltedParticleMeasure p N n hn θ ε true
      let μ' := tiltedParticleMeasure p N' n hn' θ ε true
      0 < tiltNormalizer p N n hn θ ε true ∧ tiltNormalizer p N n hn θ ε true < ⊤ ∧
      0 < tiltNormalizer p N' n hn' θ ε true ∧ tiltNormalizer p N' n hn' θ ε true < ⊤ ∧
      IsProbabilityMeasure μ ∧ IsProbabilityMeasure μ' ∧
      ∀ (K : ℕ), K ≤ (n : ℕ) / 4 → ∀ G : BlockObservable n,
        DependsOnBlockCoordinates G (symmetricMiddleBlock n K) →
        Integrable (fun X => G.val (finiteGapBlock X)) μ ∧
        Integrable (fun X => G.val (finiteGapBlock X)) μ' ∧
        |(∫ X, G.val (finiteGapBlock X) ∂μ) - (∫ X, G.val (finiteGapBlock X) ∂μ')| ≤
          C * (n : ℝ) ^ (κ * ε - min s.val 1 / 2) *
            (restrictedBlockDerivativeNorm G (symmetricMiddleBlock n K)
                (goodBlockEvent s.val n N (Kₛ * ε)) +
              Real.exp (-c * (n : ℝ) ^ δ) * blockDerivativeNorm G)) :
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
          C * (n : ℝ) ^ (-min p.val.2 1 / 2 + ζ) * blockDerivativeNorm G := by
  classical
  intro p ζ hζ
  obtain ⟨Ks, κ, ε₀, hKs, hκ, hε₀, hcompare⟩ :=
    hcomparison ⟨p.val.2, p.property.2⟩
  let ε := min (ε₀ / 2) (ζ / (2 * κ))
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hε₀' : ε < ε₀ := (min_le_left _ _).trans_lt (by linarith)
  have hκε : κ * ε ≤ ζ := by
    have hh := min_le_right (ε₀ / 2) (ζ / (2 * κ))
    have hh' := (le_div_iff₀ (by positivity : 0 < 2 * κ)).mp hh
    dsimp only [ε]
    nlinarith
  obtain ⟨δ, hδ, hcompare⟩ := hcompare ε hε hε₀'
  obtain ⟨θ⟩ := DefinitionSanity.physicalCutoff_nonempty
  obtain ⟨C, c, hC, hc, hcompare⟩ :=
    hcompare θ p.val.1 p.val.1 p.property.1 le_rfl
  have hcompare := hcompare ⟨p.val.1, p.property.1⟩ ⟨le_rfl, le_rfl⟩
  change ∀ (n N N' : ℕ+) (_ : 2 ≤ (n : ℕ)), _ at hcompare
  obtain ⟨A, b, d, hA, hb, hd, htilt⟩ := InterpolatingDensities.tilt_expectation
    p.val.2 p.val.1 ε p.property.2.1 p.property.2.2 p.property.1 hε θ
  have htilt := htilt p rfl rfl
  let q := -min p.val.2 1 / 2 + ζ
  obtain ⟨B, hB, htail⟩ := exponential_le_power hb hd q
  refine ⟨2 * C + 2 * A * B, by positivity, ?_⟩
  intro n N N' hn hNN' hnN hscale G J hJ hG
  have hN : 2 ≤ (N : ℕ) := by omega
  have hN' : 2 ≤ (N' : ℕ) := by omega
  have hnle : (n : ℕ) ≤ (N : ℕ) := by omega
  have hnle' : (n : ℕ) ≤ (N' : ℕ) := by omega
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ (n : ℕ) by omega)
  have hn0 : 0 < (n : ℝ) := by positivity
  have hD (H : BlockObservable n) : 0 ≤ blockDerivativeNorm H := by
    unfold blockDerivativeNorm; positivity
  have hsymmetric (H : BlockObservable n)
      (hH : DependsOnBlockCoordinates H (symmetricMiddleBlock n ((n : ℕ) / 4))) :
      |(∫ X : Riesz1.Configuration N, H.val (finiteGapBlock X) ∂gibbsMeasure p N) -
        (∫ X : Riesz1.Configuration N', H.val (finiteGapBlock X) ∂gibbsMeasure p N')| ≤
        (2 * C + 2 * A * B) * (n : ℝ) ^ q * blockDerivativeNorm H := by
    have ht := hcompare n N N' hn hNN' hnN hscale hnle hnle'
    have ht := ht.2.2.2.2.2.2 ((n : ℕ) / 4) le_rfl H hH
    have htN := htilt N n hN hnle H
    have htN' := htilt N' n hN' hnle' H
    have hrestricted := restricted_le_global H (symmetricMiddleBlock n ((n : ℕ) / 4))
      (goodBlockEvent p.val.2 n N (Ks * ε))
    have hexp : Real.exp (-c * (n : ℝ) ^ δ) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have : 0 ≤ (n : ℝ) ^ δ := by positivity
      nlinarith
    have hpower : (n : ℝ) ^ (κ * ε - min p.val.2 1 / 2) ≤ (n : ℝ) ^ q :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [q]; linarith)
    have hmain :
        |(∫ X, H.val (finiteGapBlock X) ∂tiltedParticleMeasure p N n hnle θ ε true) -
          (∫ X, H.val (finiteGapBlock X) ∂tiltedParticleMeasure p N' n hnle' θ ε true)| ≤
          2 * C * (n : ℝ) ^ q * blockDerivativeNorm H := by
      calc
        _ ≤ C * (n : ℝ) ^ (κ * ε - min p.val.2 1 / 2) *
            (blockDerivativeNorm H + 1 * blockDerivativeNorm H) := by
          apply ht.2.2.trans
          gcongr
          exact hD H
        _ ≤ 2 * C * (n : ℝ) ^ q * blockDerivativeNorm H := by
          nlinarith [mul_le_mul_of_nonneg_right hpower
            (mul_nonneg hC.le (hD H))]
    have htbound := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (htail (n : ℝ) hn1) hA.le) (hD H)
    have heN := htN.2.2.trans htbound
    have heN' := htN'.2.2.trans htbound
    rw [abs_sub_comm] at heN
    have htriangle := abs_sub_le
      (∫ X : Riesz1.Configuration N, H.val (finiteGapBlock X) ∂gibbsMeasure p N)
      (∫ X, H.val (finiteGapBlock X) ∂tiltedParticleMeasure p N n hnle θ ε true)
      (∫ X : Riesz1.Configuration N', H.val (finiteGapBlock X) ∂gibbsMeasure p N')
    have htriangle' := abs_sub_le
      (∫ X, H.val (finiteGapBlock X) ∂tiltedParticleMeasure p N n hnle θ ε true)
      (∫ X, H.val (finiteGapBlock X) ∂tiltedParticleMeasure p N' n hnle' θ ε true)
      (∫ X : Riesz1.Configuration N', H.val (finiteGapBlock X) ∂gibbsMeasure p N')
    nlinarith
  have := gibbsMeasure_probability p N
  have := gibbsMeasure_probability p N'
  refine ⟨InterpolatingDensities.block_integrable N n G _,
    InterpolatingDensities.block_integrable N' n G _, ?_⟩
  rcases middle_embedding n J hJ with hsub | hshift
  · exact hsymmetric G (fun x y hxy => hG x y (fun i hi => hxy i (hsub hi)))
  · let H := relabel G (finRotate (n : ℕ))
    have hH : DependsOnBlockCoordinates H (symmetricMiddleBlock n ((n : ℕ) / 4)) := by
      intro x y hxy
      apply hG
      intro i hi
      exact hxy _ (hshift i hi).2
    have hh := hsymmetric H hH
    rw [integral_relabel_cycle p n N hN G J hG (fun i hi => (hshift i hi).1),
      integral_relabel_cycle p n N' hN' G J hG (fun i hi => (hshift i hi).1)] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (relabel_norm_le G _)
      (by positivity))

end Riesz2.OrdinaryGapCauchy
