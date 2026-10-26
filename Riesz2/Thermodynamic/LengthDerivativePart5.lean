/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.LengthDerivativePart3
public import Riesz2.Thermodynamic.CompatibleComparisonPart4
public import Riesz2.ToMathlib.CompactFibreContinuousFactor
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# Length differentiation for supported Lipschitz observables

For the proof of Lemma 6.5, change length through an unused active coordinate. The
observable is then fixed in the parameter. Only the compactly supported density is
differentiated. Inward mollification preserves both coordinate derivative norms.
-/

public section
noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter
open scoped Topology ContDiff ENNReal

namespace Riesz2.LengthDerivative

open AffineSimplex LengthAveragingFibres

/-- See the proof of Lemma 6.5 in the paper: a zero-sum shear makes
the change in length occur in any specified active coordinate. -/
theorem exists_coordinate_shear (n : ℕ) (j : Fin (n+1)) :
    ∃ a : Tangent n, ∀ (L : ℝ) (z : Tangent n),
      centredChart n L (z + L • a) = z.val + L • EuclideanSpace.single j 1 := by
  let a : Tangent n := ⟨EuclideanSpace.single j 1 - centre n 1,
    (mem_hsOrthSubspace_iff n _).mpr (by
      simp only [PiLp.sub_apply, Finset.sum_sub_distrib, sum_centre]
      simp)⟩
  refine ⟨a, fun L z => ?_⟩
  ext i
  change z.val i + L * ((EuclideanSpace.single j (1 : ℝ)) i - 1/((n : ℝ)+1)) + L/((n : ℝ)+1) =
    z.val i + L * (EuclideanSpace.single j (1 : ℝ)) i
  ring

/-- See the proof of Lemma 6.5 in the paper: the existing physical
weight remains C¹ and compactly supported after a zero-sum shear. -/
theorem sheared_weight_C1_compact (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) (a : Tangent n) :
    ContDiff ℝ 1 (fun q : ℝ × Tangent n =>
      (marginalWeight p n m θ ε (centredChart n q.1 (q.2 + q.1 • a))).toReal) ∧
    HasCompactSupport (fun q : ℝ × Tangent n =>
      (marginalWeight p n m θ ε (centredChart n q.1 (q.2 + q.1 • a))).toReal) := by
  obtain ⟨hw, hs⟩ := centred_weight_C1_compact p n m θ ε
  exact CompactFibreContinuousFactor.shear hw hs a

/-- See Lemma 6.5 of the paper: translating the fixed zero-sum coordinate
leaves the physical every-length quotient unchanged. -/
theorem averagedObservable_sheared_ratio (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) (a : Tangent n)
    (G : BlockObservable n.succPNat)
    (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) :
    averagedObservable p n m θ ε G L =
      (∫ z : Tangent n,
        (marginalWeight p n m θ ε (centredChart n L.val (z + L.val • a))).toReal *
          G.val (WithLp.ofLp (centredChart n L.val (z + L.val • a)))) /
      (∫ z : Tangent n,
        (marginalWeight p n m θ ε (centredChart n L.val (z + L.val • a))).toReal) := by
  rw [(averagedObservable_centred_ratio p n m θ ε G L).2]
  rw [integral_add_right_eq_self (fun z : Tangent n =>
    (marginalWeight p n m θ ε (centredChart n L.val z)).toReal *
      G.val (WithLp.ofLp (centredChart n L.val z))) (L.val • a),
    integral_add_right_eq_self (fun z : Tangent n =>
      (marginalWeight p n m θ ε (centredChart n L.val z)).toReal) (L.val • a)]

/-- See the proof of Lemma 6.5 in the paper: every proper supported
Lipschitz observable has a C¹ every-length average. In particular the
specified fibre representative is locally absolutely continuous. -/
theorem proper_averagedObservable_C1 (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) (J : Finset (Fin (n+1)))
    (j : Fin (n+1)) (hj : j ∉ J)
    (G : BlockObservable n.succPNat) (hJ : DependsOnBlockCoordinates G J) :
    ∃ M : ℝ → ℝ,
      (∀ L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ),
        M L.val = averagedObservable p n m θ ε G L) ∧
      ContDiffOn ℝ 1 M (Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) ∧
      (∀ u v : ℝ, u ∈ Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ) →
        v ∈ Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ) →
        AbsolutelyContinuousOnInterval M u v) := by
  obtain ⟨a, ha⟩ := exists_coordinate_shear n j
  let w := fun q : ℝ × Tangent n =>
    (marginalWeight p n m θ ε (centredChart n q.1 (q.2 + q.1 • a))).toReal
  let g := fun z : Tangent n => G.val (WithLp.ofLp z.val)
  have hg : Continuous g := G.property.choose_spec.continuous.comp
    ((PiLp.continuous_ofLp 2 _).comp continuous_subtype_val)
  have he (L : ℝ) (z : Tangent n) :
      G.val (WithLp.ofLp (centredChart n L (z + L • a))) = g z := by
    apply hJ
    intro i hi
    rw [ha]
    change z.val i + L * (EuclideanSpace.single j 1) i = z.val i
    have hne : i ≠ j := fun h => hj (h ▸ hi)
    simp [EuclideanSpace.single, Ne.symm hne]
  obtain ⟨hw, hs⟩ := sheared_weight_C1_compact p n m θ ε a
  let Z := fun L => ∫ z, w (L,z)
  have hZ (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) : 0 < Z L.val := by
    dsimp only [Z, w]
    rw [integral_add_right_eq_self (fun z : Tangent n =>
      (marginalWeight p n m θ ε (centredChart n L.val z)).toReal) (L.val • a)]
    exact (centred_real_mass p n m θ ε L).2
  let M := fun L => (∫ z, w (L,z) * g z) / Z L
  have hM : ContDiffOn ℝ 1 M (Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) :=
    (CompactFibreContinuousFactor.integral volume hw hs hg).1.contDiffOn.div
      (CompactFibreC1.integral volume hw hs).1.contDiffOn (fun L hL => (hZ ⟨L,hL⟩).ne')
  refine ⟨M, fun L => ?_, hM, fun u v hu hv => ?_⟩
  · rw [averagedObservable_sheared_ratio p n m θ ε a G L]
    simp_rw [he]
    rfl
  · exact (hM.mono (OrdConnected.uIcc_subset (ordConnected_Ioo) hu hv)).absolutelyContinuousOnInterval

/-- See the proof of Lemma 6.5 in the paper: two extensions of the
same every-length average have the same ordinary derivative in the open
carrier, independently of their values outside it. -/
theorem averagedObservable_deriv_eq_internal (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) (G : BlockObservable n.succPNat)
    {M F : ℝ → ℝ}
    (hM : ∀ L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ),
      M L.val = averagedObservable p n m θ ε G L)
    (hF : ∀ L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ),
      F L.val = averagedObservable p n m θ ε G L)
    (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) :
    deriv M L.val = deriv F L.val := by
  apply Filter.EventuallyEq.deriv_eq
  exact eventuallyEq_of_mem (isOpen_Ioo.mem_nhds L.property)
    (fun t ht => (hM ⟨t,ht⟩).trans (hF ⟨t,ht⟩).symm)

/-- See the proof of Lemma 6.5 in the paper: value approximation of
proper supported observables with bounded global norms gives
pointwise convergence of the derivatives of their every-length averages.
The unused coordinate carries the parameter derivative, so no derivatives
of the original Lipschitz observable are taken on a null hyperplane. -/
theorem proper_average_deriv_tendsto_internal (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) (J : Finset (Fin (n+1)))
    (j : Fin (n+1)) (hj : j ∉ J)
    (G : BlockObservable n.succPNat) (hJ : DependsOnBlockCoordinates G J)
    (φ : ℕ → BlockObservable n.succPNat)
    (hφ : ∀ k, DependsOnBlockCoordinates (φ k) J)
    (hD : ∀ k, blockDerivativeNorm (φ k) ≤ blockDerivativeNorm G)
    (hp : ∀ x, Tendsto (fun k => (φ k).val x) atTop (𝓝 (G.val x)))
    (M : ℝ → ℝ) (F : ℕ → ℝ → ℝ)
    (hM : ∀ L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ),
      M L.val = averagedObservable p n m θ ε G L)
    (hF : ∀ k, ∀ L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ),
      F k L.val = averagedObservable p n m θ ε (φ k) L) :
    ∀ L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ),
      Tendsto (fun k => deriv (F k) L.val) atTop (𝓝 (deriv M L.val)) := by
  obtain ⟨a, ha⟩ := exists_coordinate_shear n j
  let w := fun q : ℝ × Tangent n =>
    (marginalWeight p n m θ ε (centredChart n q.1 (q.2 + q.1 • a))).toReal
  let g := fun (H : BlockObservable n.succPNat) (z : Tangent n) =>
    H.val (WithLp.ofLp z.val)
  let Q := fun (H : BlockObservable n.succPNat) (L : ℝ) =>
    (∫ z, w (L,z) * g H z) / ∫ z, w (L,z)
  have hg (H : BlockObservable n.succPNat) : Continuous (g H) :=
    H.property.choose_spec.continuous.comp
      ((PiLp.continuous_ofLp 2 _).comp continuous_subtype_val)
  have hQ (H : BlockObservable n.succPNat) (hH : DependsOnBlockCoordinates H J)
      (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) :
      Q H L.val = averagedObservable p n m θ ε H L := by
    rw [averagedObservable_sheared_ratio p n m θ ε a H L]
    have he (z : Tangent n) :
        H.val (WithLp.ofLp (centredChart n L.val (z + L.val • a))) = g H z := by
      apply hH
      intro i hi
      rw [ha]
      change z.val i + L.val * (EuclideanSpace.single j 1) i = z.val i
      have hne : i ≠ j := fun h => hj (h ▸ hi)
      simp [EuclideanSpace.single, Ne.symm hne]
    simp_rw [he]
    rfl
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto (fun k => (φ k).val 0) (hp 0)).exists_norm_le
  let H := fun z : Tangent n => B + blockDerivativeNorm G * ‖z‖
  have hbound k z : ‖g (φ k) z‖ ≤ H z := by
    have hb := InterpolatingDensities.block_bound (φ k) 0 (WithLp.ofLp z.val)
    have hzi (i : Fin (n+1)) : |z.val i| ≤ ‖z‖ := by
      exact PiLp.norm_apply_le z.val i
    have hsum : (∑ i, (coordinateDerivativeNorm (φ k) i : ℝ) * |z.val i|) ≤
        blockDerivativeNorm G * ‖z‖ := by
      calc
        _ ≤ ∑ i, (coordinateDerivativeNorm (φ k) i : ℝ) * ‖z‖ :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hzi i) (NNReal.coe_nonneg _)
        _ = blockDerivativeNorm (φ k) * ‖z‖ := by rw [← Finset.sum_mul]; rfl
        _ ≤ _ := mul_le_mul_of_nonneg_right (hD k) (norm_nonneg _)
    have hb0 : |(φ k).val 0| ≤ B := hB _ (mem_range_self k)
    have htri : |g (φ k) z| ≤ |g (φ k) z - (φ k).val 0| + |(φ k).val 0| := by
      simpa only [sub_add_cancel] using abs_add_le (g (φ k) z - (φ k).val 0) ((φ k).val 0)
    simp only [Pi.zero_apply, sub_zero] at hb
    change |g (φ k) z| ≤ B + blockDerivativeNorm G * ‖z‖
    linarith
  obtain ⟨hw, hs⟩ := sheared_weight_C1_compact p n m θ ε a
  intro L
  have hZ : 0 < ∫ z, w (L.val,z) := by
    dsimp only [w]
    rw [integral_add_right_eq_self (fun z : Tangent n =>
      (marginalWeight p n m θ ε (centredChart n L.val z)).toReal) (L.val • a)]
    exact (centred_real_mass p n m θ ε L).2
  have ht := CompactFibreContinuousFactor.normalized_deriv_tendsto volume hw hs
    (fun k => hg (φ k)) (hg G) (by dsimp only [H]; fun_prop) hbound
    (fun z => hp (WithLp.ofLp z.val)) L.val hZ
  have he k : deriv (F k) L.val = deriv (Q (φ k)) L.val :=
    averagedObservable_deriv_eq_internal p n m θ ε (φ k) (hF k) (hQ (φ k) (hφ k)) L
  have heM : deriv M L.val = deriv (Q G) L.val :=
    averagedObservable_deriv_eq_internal p n m θ ε G hM (hQ G hJ) L
  simp_rw [he, heM]
  exact ht

/-- See the proof of Lemma 6.5 in the paper, internal passage from
the displayed bound for C¹ observables to the complete supported Lipschitz
class. The same good event, norms, constants and exponents occur on
both sides of the implication. The conclusion includes every-length
identification, local absolute continuity, and finite weighted L² derivative.
The smooth estimate is deliberately an internal hypothesis. -/
theorem lipschitz_derivative_of_smooth_internal (p : Parameters) (n m : ℕ)
    (hn : 1 ≤ n) (θ : PhysicalCutoff) (ε η : ℝ) (hη : 0 < η)
    (J : Finset (Fin (n+1))) (j : Fin (n+1)) (hj : j ∉ J)
    (C c κ δ : ℝ) (hC : 0 ≤ C)
    (hSmooth : ∀ G : BlockObservable n.succPNat,
      ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin (n+1)) => G.val (WithLp.ofLp x)) →
      DependsOnBlockCoordinates G J →
      ∃ M : ℝ → ℝ,
        (∀ L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ),
          M L.val = averagedObservable p n m θ ε G L) ∧
        MemLp (fun L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ) => deriv M L.val)
          2 (lengthMeasure p n m θ ε) ∧
        (eLpNorm (fun L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ) => deriv M L.val)
          2 (lengthMeasure p n m θ ε)).toReal ≤
          C * (n+1 : ℝ)^(κ*ε-min p.val.2 1) *
            restrictedBlockDerivativeNorm G J
              (goodBlockEvent p.val.2 n.succPNat (n+1+m).succPNat η) +
          C * Real.exp (-c*(n+1 : ℝ)^δ) * blockDerivativeNorm G) :
    ∀ G : BlockObservable n.succPNat, DependsOnBlockCoordinates G J →
      ∃ M : ℝ → ℝ,
        (∀ L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ),
          M L.val = averagedObservable p n m θ ε G L) ∧
        ContDiffOn ℝ 1 M (Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) ∧
        (∀ u v : ℝ, u ∈ Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ) →
          v ∈ Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ) →
          AbsolutelyContinuousOnInterval M u v) ∧
        MemLp (fun L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ) => deriv M L.val)
          2 (lengthMeasure p n m θ ε) ∧
        (eLpNorm (fun L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ) => deriv M L.val)
          2 (lengthMeasure p n m θ ε)).toReal ≤
          C * (n+1 : ℝ)^(κ*ε-min p.val.2 1) *
            restrictedBlockDerivativeNorm G J
              (goodBlockEvent p.val.2 n.succPNat (n+1+m).succPNat η) +
          C * Real.exp (-c*(n+1 : ℝ)^δ) * blockDerivativeNorm G := by
  classical
  intro G hJ
  obtain ⟨φ, hs, hφ, hA, hD, hp, _⟩ :=
    CompatibleComparison.normalized_restricted_smooth_approximation p.val.2 η hη n
      (n+1+m).succPNat (by omega) (by simp only [Nat.succPNat_coe]; omega) G J hJ
  have hs' k : ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin (n+1)) =>
      (φ k).val (WithLp.ofLp x)) := (hs k).of_le (by simp) |>.comp PiLp.contDiff_ofLp
  choose F hF hiF hbF using fun k => hSmooth (φ k) (hs' k) (hφ k)
  obtain ⟨M, hM, hMC, hAC⟩ := proper_averagedObservable_C1 p n m θ ε J j hj G hJ
  let B := C * (n+1 : ℝ)^(κ*ε-min p.val.2 1) *
      restrictedBlockDerivativeNorm G J
        (goodBlockEvent p.val.2 n.succPNat (n+1+m).succPNat η) +
    C * Real.exp (-c*(n+1 : ℝ)^δ) * blockDerivativeNorm G
  have hB : 0 ≤ B := by
    have hA0 : 0 ≤ restrictedBlockDerivativeNorm G J
        (goodBlockEvent p.val.2 n.succPNat (n+1+m).succPNat η) := by
      unfold restrictedBlockDerivativeNorm
      positivity
    have hD0 : 0 ≤ blockDerivativeNorm G := by unfold blockDerivativeNorm; positivity
    exact add_nonneg (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (by positivity) _)) hA0)
      (mul_nonneg (mul_nonneg hC (Real.exp_pos _).le) hD0)
  have hb k : (eLpNorm (fun L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ) =>
      deriv (F k) L.val) 2 (lengthMeasure p n m θ ε)).toReal ≤ B := by
    refine (hbF k).trans (add_le_add ?_ ?_)
    · exact mul_le_mul_of_nonneg_left (hA k J)
        (mul_nonneg hC (Real.rpow_nonneg (by positivity) _))
    · exact mul_le_mul_of_nonneg_left (hD k) (mul_nonneg hC (Real.exp_pos _).le)
  have hmeas : AEStronglyMeasurable
      (fun L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ) => deriv M L.val)
      (lengthMeasure p n m θ ε) :=
    ((measurable_deriv M).comp measurable_subtype_coe).aestronglyMeasurable
  have hlim := proper_average_deriv_tendsto_internal p n m θ ε J j hj G hJ
    φ hφ hD hp M F hM hF
  have hnorm : eLpNorm
      (fun L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ) => deriv M L.val)
      2 (lengthMeasure p n m θ ε) ≤ ENNReal.ofReal B := by
    apply Lp.eLpNorm_le_of_ae_tendsto _ (fun k => (hiF k).aestronglyMeasurable) hmeas
      (Eventually.of_forall hlim)
    apply Eventually.of_forall
    intro k
    rw [← ENNReal.ofReal_toReal (hiF k).ne]
    exact ENNReal.ofReal_le_ofReal (hb k)
  refine ⟨M, hM, hMC, hAC, hnorm.trans_lt ENNReal.ofReal_lt_top, ?_⟩
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm
  simpa only [ENNReal.toReal_ofReal hB] using ht

/-- See the proof of Lemma 6.5 in the paper: the complete smooth-to-
Lipschitz implication for the middle-half support class of the paper
(paper labels are Lean indices plus one).  Constants retain their original quantifier scope. -/
theorem middle_half_lipschitz_derivative_of_smooth_internal (p : Parameters) (n m : ℕ)
    (hn : 1 ≤ n) (θ : PhysicalCutoff) (ε η : ℝ) (hη : 0 < η)
    (J : Finset (Fin (n+1)))
    (hmiddle : ∀ i ∈ J,
      |((i.val : ℝ)+1) - (n+1 : ℝ)/2| ≤ (n+1 : ℝ)/4)
    (C c κ δ : ℝ) (hC : 0 ≤ C)
    (hSmooth : ∀ G : BlockObservable n.succPNat,
      ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin (n+1)) => G.val (WithLp.ofLp x)) →
      DependsOnBlockCoordinates G J →
      ∃ M : ℝ → ℝ,
        (∀ L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ),
          M L.val = averagedObservable p n m θ ε G L) ∧
        MemLp (fun L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ) => deriv M L.val)
          2 (lengthMeasure p n m θ ε) ∧
        (eLpNorm (fun L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ) => deriv M L.val)
          2 (lengthMeasure p n m θ ε)).toReal ≤
          C * (n+1 : ℝ)^(κ*ε-min p.val.2 1) *
            restrictedBlockDerivativeNorm G J
              (goodBlockEvent p.val.2 n.succPNat (n+1+m).succPNat η) +
          C * Real.exp (-c*(n+1 : ℝ)^δ) * blockDerivativeNorm G) :
    ∀ G : BlockObservable n.succPNat, DependsOnBlockCoordinates G J →
      ∃ M : ℝ → ℝ,
        (∀ L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ),
          M L.val = averagedObservable p n m θ ε G L) ∧
        ContDiffOn ℝ 1 M (Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) ∧
        (∀ u v : ℝ, u ∈ Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ) →
          v ∈ Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ) →
          AbsolutelyContinuousOnInterval M u v) ∧
        MemLp (fun L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ) => deriv M L.val)
          2 (lengthMeasure p n m θ ε) ∧
        (eLpNorm (fun L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ) => deriv M L.val)
          2 (lengthMeasure p n m θ ε)).toReal ≤
          C * (n+1 : ℝ)^(κ*ε-min p.val.2 1) *
            restrictedBlockDerivativeNorm G J
              (goodBlockEvent p.val.2 n.succPNat (n+1+m).succPNat η) +
          C * Real.exp (-c*(n+1 : ℝ)^δ) * blockDerivativeNorm G := by
  have hj : Fin.last n ∉ J := by
    intro h
    have hh := hmiddle (Fin.last n) h
    simp only [Fin.val_last] at hh
    have hab := le_abs_self (((n : ℝ)+1) - (n+1 : ℝ)/2)
    have hpos : 0 < (n+1 : ℝ) := by positivity
    linarith
  exact lipschitz_derivative_of_smooth_internal p n m hn θ ε η hη J (Fin.last n) hj
    C c κ δ hC hSmooth

end Riesz2.LengthDerivative
