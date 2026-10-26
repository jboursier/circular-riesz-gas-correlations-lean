/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.LengthAveragingFibres
public import Riesz2.ToMathlib.DominatedFibreCalculus
public import Riesz2.Thermodynamic.InterpolatingDensities
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# The every-length averaged observable

The observable in Lemma 6.5 uses the physical fibre kernel. Its integral is finite at
every interior length, including fibres of zero length-law measure. The identities are
steps in the proof of Lemma 6.5.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Riesz2.LengthDerivative

open LengthAveragingFibres AffineSimplex

variable (p : Parameters) (n m : ℕ) (θ : PhysicalCutoff) (ε : ℝ)

/-- The physical fibre is supported on the positive mass simplex at every
interior length. See Lemma 6.5. -/
theorem mem_simplex_ae_fibre
    (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) :
    ∀ᵐ x ∂fibreKernel p n m θ ε L, x ∈ massSimplex n L.val := by
  apply (withDensity_absolutelyContinuous _ _)
  apply ae_restrict_mem
  change MeasurableSet ({x | ∀ i : Fin (n + 1), 0 < x i} ∩ massHyperplane n L.val)
  apply MeasurableSet.inter _ (isClosed_massHyperplane n L.val).measurableSet
  simpa only [ofPred_forall] using MeasurableSet.iInter
    (fun i : Fin (n + 1) => measurableSet_lt (measurable_const (a := (0 : ℝ)))
      (PiLp.continuous_apply 2 _ i).measurable)

/-- Every Lipschitz block observable is integrable on every physical
length fibre. This rules out a junk Bochner value in Lemma 6.5. -/
theorem observable_integrable_fibre
    (G : BlockObservable (⟨n + 1, Nat.succ_pos n⟩ : ℕ+))
    (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) :
    Integrable (fun x => G.val (WithLp.ofLp x)) (fibreKernel p n m θ ε L) := by
  have hG : Measurable G.val := G.property.choose_spec.continuous.measurable
  have hmeas : Measurable (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
      G.val (WithLp.ofLp x)) :=
    hG.comp
      (WithLp.measurable_ofLp 2 _)
  apply (integrable_const (blockDerivativeNorm G * L.val + |G.val 0|)).mono'
    hmeas.aestronglyMeasurable
  filter_upwards [mem_simplex_ae_fibre p n m θ ε L] with x hx
  have hxi (i : Fin (n + 1)) : |x i| ≤ L.val := by
    rw [abs_of_pos (hx.1 i)]
    calc
      x i ≤ ∑ j, x j := Finset.single_le_sum (fun j _ => (hx.1 j).le) (Finset.mem_univ i)
      _ = L.val := hx.2
  rw [Real.norm_eq_abs]
  calc
    |G.val (WithLp.ofLp x)| ≤ |G.val (WithLp.ofLp x) - G.val 0| + |G.val 0| := by
      simpa only [sub_add_cancel] using
        abs_add_le (G.val (WithLp.ofLp x) - G.val 0) (G.val 0)
    _ ≤ (∑ i, (coordinateDerivativeNorm G i : ℝ) * |x i|) + |G.val 0| := by
      simpa only [Pi.zero_apply, sub_zero] using
        add_le_add (InterpolatingDensities.block_bound G 0 (WithLp.ofLp x)) le_rfl
    _ ≤ (∑ i, (coordinateDerivativeNorm G i : ℝ) * L.val) + |G.val 0| :=
      add_le_add (Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hxi i) (NNReal.coe_nonneg _)) le_rfl
    _ = _ := by rw [← Finset.sum_mul]; rfl

/-- See Lemma 6.5 of the paper: the explicit averaged observable on the whole
open length carrier. Integrability at each length is proved above. -/
def averagedObservable
    (G : BlockObservable (⟨n + 1, Nat.succ_pos n⟩ : ℕ+))
    (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) : ℝ :=
  ∫ x, G.val (WithLp.ofLp x) ∂fibreKernel p n m θ ε L

/-- The actual fibre average is measurable. See Lemma 6.5. -/
theorem measurable_averagedObservable
    (G : BlockObservable (⟨n + 1, Nat.succ_pos n⟩ : ℕ+)) :
    Measurable (averagedObservable p n m θ ε G) := by
  have hg : Measurable G.val := G.property.choose_spec.continuous.measurable
  have hG : Measurable (fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
      G.val (WithLp.ofLp x)) :=
    hg.comp
      (WithLp.measurable_ofLp 2 _)
  exact (hG.stronglyMeasurable.comp_measurable measurable_snd).integral_kernel_prod_right'.measurable

/-- Boundary check for Lemma 6.5: averaging a constant preserves it on
every fibre, independently of the ambient law. -/
theorem integral_const_fibre (c : ℝ)
    (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) :
    (∫ _x, c ∂fibreKernel p n m θ ε L) = c := by simp

/-- Boundary check for the proof of Lemma 6.5: the average
of the total active length is the length itself. This test has derivative
one and fixes the normal-direction convention. -/
theorem integral_sum_fibre
    (L : Ioo (0 : ℝ) ((n + 1 + m : ℕ) + 1 : ℝ)) :
    (∫ x, ∑ i, x i ∂fibreKernel p n m θ ε L) = L.val := by
  calc
    _ = ∫ _x, L.val ∂fibreKernel p n m θ ε L :=
      integral_congr_ae (sum_eq_ae_fibre p n m θ ε L)
    _ = _ := by simp

/-- See Lemma 6.5 of the paper: the active marginal is exactly the
composition of the explicit physical fibre kernel and length measure. -/
theorem activeMeasure_eq_comp :
    activeMeasure p n m θ ε = fibreKernel p n m θ ε ∘ₘ lengthMeasure p n m θ ε := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable]
  exact lintegral_disintegration p n m θ ε hf

/-- Signed disintegration for an integrable observable, as used in Lemma 6.5. -/
theorem integral_disintegration_internal
    {g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hg : Integrable g (activeMeasure p n m θ ε)) :
    (∫ x, g x ∂activeMeasure p n m θ ε) =
      ∫ L, ∫ x, g x ∂fibreKernel p n m θ ε L ∂lengthMeasure p n m θ ε := by
  rw [activeMeasure_eq_comp p n m θ ε] at hg ⊢
  rw [Measure.comp_eq_comp_const_apply] at hg ⊢
  exact Kernel.integral_comp hg

section MultiplierSign

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} [IsProbabilityMeasure ν]

/-- See the proof of Lemma 6.5 in the paper, multiplier sign identity.
The covariance representation is an internal premise. The multiplier is
the field, with the inverse temperature already in `M`.
The normal Hessian contraction is summed in the same order as the multiplier, so symmetry need not be an extra algebraic premise. -/
theorem derivative_eq_neg_multiplier_internal (N : ℕ+) (Q : ScalarFormData ν)
    (M : X → Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (v : Fin (N : ℕ) → Lp ℝ 2 ν) (u : Fin (N : ℕ) → Q.1)
    (hpair : ∀ i j, Integrable (fun x => M x i j * (u j).val x) ν)
    (d covarianceTerm : ℝ)
    (hd : d = (N : ℝ)⁻¹ * (∑ i, ∫ x, v i x ∂ν) - covarianceTerm)
    (hc : covarianceTerm =
      (N : ℝ)⁻¹ * (∑ i, ∑ j, ∫ x, M x i j * (u j).val x ∂ν)) :
    d = -(∫ x, gapMultiplierField N Q M v u x ∂ν) := by
  rw [(LengthAveragingFibres.multiplier_mean_internal N Q M v u hpair).2, hd, hc]
  ring

end MultiplierSign

end Riesz2.LengthDerivative
