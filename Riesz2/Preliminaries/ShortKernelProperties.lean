/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Bridges.KernelIdentification
public import Riesz2.Frozen.ShortKernelLift
public import Riesz2.Frozen.ShortKernel
public import Riesz2.Sanity.FiniteLaws

/-!
# Short-range periodic kernel

See Subsection 1.1 of the paper. All analytic assertions exclude the collision lattice.
The real series used in derivative formulas agrees with the lift on its whole carrier.
-/

@[expose] public section

noncomputable section

open Filter Set Topology
open scoped ContDiff

namespace Riesz2

/-- A derivative tower on an open set consists of smooth functions. -/
private theorem contDiffOn_of_hasDerivAt_tower {U : Set ℝ} (hU : IsOpen U)
    (F : ℕ → ℝ → ℝ)
    (hF : ∀ n x, x ∈ U → HasDerivAt (F n) (F (n + 1) x) x) (j : ℕ) :
    ContDiffOn ℝ ∞ (F j) U := by
  have hfinite : ∀ n : ℕ, ∀ j, ContDiffOn ℝ n (F j) U := by
    intro n
    induction n with
    | zero =>
      intro j
      exact contDiffOn_zero.mpr (fun x hx => (hF j x hx).continuousAt.continuousWithinAt)
    | succ n ih =>
      intro j
      rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by rfl,
        contDiffOn_succ_iff_deriv_of_isOpen hU]
      refine ⟨fun x hx => (hF j x hx).differentiableAt.differentiableWithinAt,
        by simp, ?_⟩
      exact (ih (j + 1)).congr (fun x hx => (hF j x hx).deriv)
  exact contDiffOn_infty.mpr (fun n => hfinite n j)


/-- Absolute convergence of the short-range image sum (Subsection 1.1). -/
theorem summable_shortKernelLift (s : ShortExponent) (x : OffLattice) :
    Summable (fun k : ℤ => 1 / |(k : ℝ) + x.val| ^ s.val) := by
  exact FrozenSanity.shortKernelLift_summable s x

/-- The negative-power series is exactly the lift, not a new kernel. -/
theorem shortKernelLift_eq_tsum_rpow (s : ShortExponent) (x : OffLattice) :
    shortKernelLift s x = ∑' k : ℤ, |(k : ℝ) + x.val| ^ (-s.val) := by
  simp only [shortKernelLift, Real.rpow_neg (abs_nonneg _), one_div]

/-- Locally uniform convergence, including order zero (Subsection 1.1). -/
theorem hasSumLocallyUniformlyOn_short_images (s : ShortExponent) (p : ℕ) :
    HasSumLocallyUniformlyOn
      (fun (k : ℤ) (x : ℝ) => iteratedDeriv p (fun y : ℝ => |(k : ℝ) + y| ^ (-s.val)) x)
      (fun x : ℝ => ∑' k : ℤ, iteratedDeriv p (fun y : ℝ => |(k : ℝ) + y| ^ (-s.val)) x)
      {x : ℝ | (x : UnitAddCircle) ≠ 0} := by
  refine hasSumLocallyUniformlyOn_of_of_forall_exists_nhds fun x hx => ?_
  have hδ : 0 < |x - round x| / 2 := by linarith [Riesz1.abs_sub_round_pos hx]
  have he : -s.val - (p : ℝ) < -1 := by linarith [s.property, Nat.cast_nonneg (α := ℝ) p]
  refine ⟨Metric.ball x (|x - round x| / 2),
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hδ),
    HasSumUniformlyOn.of_norm_le_summable
      ((Riesz1.summable_half_abs_add_int_rpow hx he).mul_left
        |∏ i ∈ Finset.range p, (-s.val - i)|) ?_⟩
  intro k z hz
  exact Riesz1.norm_iteratedDeriv_le_ball s.val (by linarith [s.property]) p k hx
    (by simpa only [Metric.mem_ball, Real.dist_eq] using hz)

/-- Termwise differentiation of the short-range series (Subsection 1.1). -/
theorem hasDerivAt_short_image_tower (s : ShortExponent) (p : ℕ) {x : ℝ}
    (hx : (x : UnitAddCircle) ≠ 0) :
    HasDerivAt
      (fun z : ℝ => ∑' k : ℤ, iteratedDeriv p (fun y : ℝ => |(k : ℝ) + y| ^ (-s.val)) z)
      (∑' k : ℤ, iteratedDeriv (p + 1) (fun y : ℝ => |(k : ℝ) + y| ^ (-s.val)) x) x := by
  rcases p with _ | p
  · simp only [iteratedDeriv_zero]
    apply hasDerivAt_of_tendstoLocallyUniformlyOn (l := (atTop : Filter (Finset ℤ)))
      (f := fun (I : Finset ℤ) (y : ℝ) => ∑ k ∈ I, |(k : ℝ) + y| ^ (-s.val))
      Riesz1.isOpen_nonInt
      (hasSumLocallyUniformlyOn_short_images s 1) ?_ ?_ hx
    · refine Eventually.of_forall fun I z hz => HasDerivAt.fun_sum fun k _ => ?_
      simp only [iteratedDeriv_one]
      exact (((Riesz1.contDiffOn_abs_rpow_add_int s.val k
        (fun w hw => Riesz1.add_int_ne_zero_of_nonInt hw k)) z hz).contDiffAt
        (Riesz1.isOpen_nonInt.mem_nhds hz)).differentiableAt (by simp) |>.hasDerivAt
    · intro z hz
      exact ((Riesz1.summable_abs_add_int_rpow hz
        (by linarith [s.property] : -s.val < -1)).hasSum)
  · exact Riesz1.hasDerivAt_tsum_iteratedDeriv s.val (by linarith [s.property])
      (Nat.succ_le_succ (Nat.zero_le p)) hx

/-- Smoothness of the image series off collisions (Subsection 1.1). -/
theorem contDiffOn_short_images (s : ShortExponent) :
    ContDiffOn ℝ ∞ (fun x : ℝ => ∑' k : ℤ, |(k : ℝ) + x| ^ (-s.val))
      {x : ℝ | (x : UnitAddCircle) ≠ 0} := by
  exact contDiffOn_of_hasDerivAt_tower Riesz1.isOpen_nonInt
    (fun p x => ∑' k : ℤ, iteratedDeriv p (fun y : ℝ => |(k : ℝ) + y| ^ (-s.val)) x)
    (fun p _ hx => hasDerivAt_short_image_tower s p hx) 0

/-- Derivatives commute with the image sum at every noncollision (Subsection 1.1). -/
theorem iteratedDeriv_short_images (s : ShortExponent) (p : ℕ) {x : ℝ}
    (hx : (x : UnitAddCircle) ≠ 0) :
    iteratedDeriv p (fun y : ℝ => ∑' k : ℤ, |(k : ℝ) + y| ^ (-s.val)) x =
      ∑' k : ℤ, iteratedDeriv p (fun y : ℝ => |(k : ℝ) + y| ^ (-s.val)) x := by
  induction p generalizing x with
  | zero => simp only [iteratedDeriv_zero]
  | succ p ih =>
    have heq : iteratedDeriv p (fun y : ℝ => ∑' k : ℤ, |(k : ℝ) + y| ^ (-s.val))
        =ᶠ[𝓝 x] fun z : ℝ => ∑' k : ℤ,
          iteratedDeriv p (fun y : ℝ => |(k : ℝ) + y| ^ (-s.val)) z :=
      eventually_of_mem (Riesz1.isOpen_nonInt.mem_nhds hx) fun _ hz => ih hz
    rw [iteratedDeriv_succ, heq.deriv_eq, (hasDerivAt_short_image_tower s p hx).deriv]

/-- The closed signed derivative formula (Subsection 1.1), also valid at order zero. -/
theorem iteratedDeriv_short_images_signed (s : ShortExponent) (p : ℕ) {x : ℝ}
    (hx : (x : UnitAddCircle) ≠ 0) :
    iteratedDeriv p (fun y : ℝ => ∑' k : ℤ, |(k : ℝ) + y| ^ (-s.val)) x =
      ((-1 : ℝ) ^ p * ∏ j ∈ Finset.range p, (s.val + (j : ℝ))) *
        ∑' k : ℤ, Real.sign (x + k) ^ p / |x + k| ^ (s.val + (p : ℝ)) := by
  rw [iteratedDeriv_short_images s p hx, ← tsum_mul_left]
  exact tsum_congr fun k => iteratedDeriv_abs_rpow_add_int s.val p k hx

/-- Absolute convergence at every derivative order (Subsection 1.1). -/
theorem summable_norm_short_image_derivatives (s : ShortExponent) (p : ℕ)
    {x : ℝ} (hx : (x : UnitAddCircle) ≠ 0) :
    Summable (fun k : ℤ => ‖iteratedDeriv p (fun y : ℝ => |(k : ℝ) + y| ^ (-s.val)) x‖) := by
  have he : -s.val - (p : ℝ) < -1 := by linarith [s.property, Nat.cast_nonneg (α := ℝ) p]
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => Riesz1.norm_iteratedDeriv_le_ball s.val (by linarith [s.property]) p k hx
      (by simpa using half_pos (Riesz1.abs_sub_round_pos hx)))
    ((Riesz1.summable_half_abs_add_int_rpow hx he).mul_left _)

/-- A summable majorant valid on a whole neighborhood, at every order.
This is the image-tail bound used in the proof of Subsection 1.1. -/
theorem short_image_derivative_majorant (s : ShortExponent) (p : ℕ) (x : OffLattice) :
    Summable (fun k : ℤ => |∏ i ∈ Finset.range p, (-s.val - i)| *
      (|(k : ℝ) + x.val| / 2) ^ (-s.val - (p : ℝ))) ∧
    ∀ (k : ℤ) (z : ℝ), |z - x.val| < |x.val - round x.val| / 2 →
      ‖iteratedDeriv p (fun y : ℝ => |(k : ℝ) + y| ^ (-s.val)) z‖ ≤
        |∏ i ∈ Finset.range p, (-s.val - i)| *
          (|(k : ℝ) + x.val| / 2) ^ (-s.val - (p : ℝ)) := by
  refine ⟨(Riesz1.summable_half_abs_add_int_rpow x.property
    (by linarith [s.property, Nat.cast_nonneg (α := ℝ) p] : -s.val - (p : ℝ) < -1)).mul_left _,
    fun k z hz => ?_⟩
  exact Riesz1.norm_iteratedDeriv_le_ball s.val (by linarith [s.property]) p k x.property hz

/-- Uniform convergence on every compact set off collisions (Subsection 1.1).
The limit is the actual derivative of the series, including at order zero. -/
theorem tendstoUniformlyOn_short_image_derivatives (s : ShortExponent) (p : ℕ)
    {K : Set ℝ} (hK : IsCompact K) (hKU : K ⊆ {x : ℝ | (x : UnitAddCircle) ≠ 0}) :
    TendstoUniformlyOn
      (fun (I : Finset ℤ) (x : ℝ) =>
        ∑ k ∈ I, iteratedDeriv p (fun y : ℝ => |(k : ℝ) + y| ^ (-s.val)) x)
      (iteratedDeriv p (fun x : ℝ => ∑' k : ℤ, |(k : ℝ) + x| ^ (-s.val))) atTop K := by
  apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
  exact ((hasSumLocallyUniformlyOn_short_images s p).mono hKU).congr_right
    (fun x hx => (iteratedDeriv_short_images s p (hKU hx)).symm)

/-- Continuity on the entire off-lattice carrier (Subsection 1.1). -/
theorem continuous_shortKernelLift (s : ShortExponent) : Continuous (shortKernelLift s) := by
  have h := (contDiffOn_short_images s).continuousOn.domRestrict
  exact h.congr (fun x => (shortKernelLift_eq_tsum_rpow s x).symm)

/-- Strict positivity of the lift (Subsection 1.1). -/
theorem shortKernelLift_pos (s : ShortExponent) (x : OffLattice) : 0 < shortKernelLift s x :=
  FrozenSanity.shortKernelLift_pos s x

/-- Evenness of the lift (Subsection 1.1). -/
theorem shortKernelLift_even (s : ShortExponent) (x : OffLattice) :
    shortKernelLift s ⟨-x.val, by simpa using x.property⟩ = shortKernelLift s x :=
  FrozenSanity.shortKernelLift_even s x

/-- Integer-periodicity of the lift (Subsection 1.1). -/
theorem shortKernelLift_add_int (s : ShortExponent) (x : OffLattice) (n : ℤ) :
    shortKernelLift s ⟨x.val + n, by simpa using x.property⟩ = shortKernelLift s x :=
  FrozenSanity.imageSum_add_int s.val x.val n

/-- The circle kernel agrees with every real lift, not just its chosen representative
(Subsection 1.1). -/
theorem shortKernel_coe (s : ShortExponent) (x : OffLattice) :
    shortKernel s ⟨(x.val : UnitAddCircle), x.property⟩ = shortKernelLift s x := by
  have hc := FrozenSanity.centralRep_cast (x.val : UnitAddCircle)
  have hz : ((Riesz1.centralRep Riesz1.unitLength (x.val : UnitAddCircle) - x.val : ℝ) :
      UnitAddCircle) = 0 := by rw [AddCircle.coe_sub, hc, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
  rw [zsmul_eq_mul, mul_one] at hn
  have hr : Riesz1.centralRep Riesz1.unitLength (x.val : UnitAddCircle) = x.val + n := by
    linarith
  unfold shortKernel shortKernelLift
  rw [hr, FrozenSanity.imageSum_add_int]

/-- Evenness of the actual circle kernel (Subsection 1.1). -/
theorem shortKernel_even (s : ShortExponent) (x : {x : UnitAddCircle // x ≠ 0}) :
    shortKernel s ⟨-x.val, neg_ne_zero.mpr x.property⟩ = shortKernel s x :=
  FrozenSanity.shortKernel_even s x

/-- Positivity of the actual circle kernel (Subsection 1.1). -/
theorem shortKernel_pos (s : ShortExponent) (x : {x : UnitAddCircle // x ≠ 0}) :
    0 < shortKernel s x := FrozenSanity.shortKernel_pos s x

/-- The singular image gives a lower bound on the whole kernel (Subsection 1.1). -/
theorem singularTerm_le_shortKernelLift (s : ShortExponent) (x : OffLattice) :
    1 / |x.val| ^ s.val ≤ shortKernelLift s x :=
  FrozenSanity.singularTerm_le_shortKernelLift s x

/-- Distant images decay with exponent `s`, as used in Subsection 1.1. -/
theorem shortImage_decay (s : ShortExponent) (x : ℝ) (k : ℤ)
    (hk : k ≠ 0) (hfar : 2 * |x| ≤ |(k : ℝ)|) :
    1 / |(k : ℝ) + x| ^ s.val ≤ 2 ^ s.val / |(k : ℝ)| ^ s.val :=
  FrozenSanity.shortImage_decay s x k hk hfar

/-- Collision blow-up (Subsection 1.1), along exactly the off-collision carrier. -/
theorem tendsto_short_images_collision (s : ShortExponent) :
    Tendsto (fun x : ℝ => ∑' k : ℤ, |(k : ℝ) + x| ^ (-s.val))
      (𝓝[{x : ℝ | (x : UnitAddCircle) ≠ 0}] 0) atTop := by
  have hfilter : 𝓝[{x : ℝ | (x : UnitAddCircle) ≠ 0}] (0 : ℝ) ≤ 𝓝[≠] 0 :=
    nhdsWithin_mono _ (fun x hx h => hx (by simp [Set.mem_singleton_iff.mp h]))
  have hsing := (tendsto_rpow_neg_nhdsGT_zero
    (by linarith [s.property] : -s.val < 0)).comp
    (tendsto_abs_nhdsNE_zero.mono_left hfilter)
  apply tendsto_atTop_mono' _ _ hsing
  filter_upwards [self_mem_nhdsWithin] with x hx
  have h := singularTerm_le_shortKernelLift s ⟨x, hx⟩
  simpa only [Function.comp_apply, shortKernelLift_eq_tsum_rpow, one_div, Real.rpow_neg (abs_nonneg _)] using h

/-- Evenness of the real series representing the kernel (Subsection 1.1). -/
theorem short_images_even (s : ShortExponent) :
    Function.Even (fun x : ℝ => ∑' k : ℤ, |(k : ℝ) + x| ^ (-s.val)) := by
  intro x
  simpa only [one_div, Real.rpow_neg (abs_nonneg _)] using
    FrozenSanity.imageSum_neg s.val x

/-- Unit periodicity of the real series representing the kernel (Subsection 1.1). -/
theorem short_images_periodic (s : ShortExponent) :
    Function.Periodic (fun x : ℝ => ∑' k : ℤ, |(k : ℝ) + x| ^ (-s.val)) 1 := by
  intro x
  simpa only [Int.cast_one, one_div, Real.rpow_neg (abs_nonneg _)] using
    FrozenSanity.imageSum_add_int s.val x 1

/-- See Subsection 1.1 of the paper, all parts: the lift and circle kernel agree.
The defining image series and every termwise derivative converge absolutely and locally
uniformly off collisions. The kernel is smooth, even, periodic and positive, blows up
at a collision, and has the displayed signed derivative formula for every `p ≥ 1`.
The exponent subtype means exactly `s > 1`. The local series expression is identified
pointwise with the kernel, so no value at a collision enters the statement. -/
theorem shortKernel_properties (s : ShortExponent) :
    (∀ x : OffLattice, shortKernelLift s x = ∑' k : ℤ, |(k : ℝ) + x.val| ^ (-s.val)) ∧
    (∀ x : OffLattice, shortKernel s ⟨(x.val : UnitAddCircle), x.property⟩ = shortKernelLift s x) ∧
    (∀ p : ℕ,
      HasSumLocallyUniformlyOn
        (fun (k : ℤ) (x : ℝ) => iteratedDeriv p (fun y : ℝ => |(k : ℝ) + y| ^ (-s.val)) x)
        (fun x : ℝ => ∑' k : ℤ, iteratedDeriv p (fun y : ℝ => |(k : ℝ) + y| ^ (-s.val)) x)
        {x : ℝ | (x : UnitAddCircle) ≠ 0} ∧
      ∀ x : OffLattice, Summable (fun k : ℤ =>
        ‖iteratedDeriv p (fun y : ℝ => |(k : ℝ) + y| ^ (-s.val)) x.val‖)) ∧
    ContDiffOn ℝ ∞ (fun x : ℝ => ∑' k : ℤ, |(k : ℝ) + x| ^ (-s.val))
      {x : ℝ | (x : UnitAddCircle) ≠ 0} ∧
    Function.Even (fun x : ℝ => ∑' k : ℤ, |(k : ℝ) + x| ^ (-s.val)) ∧
    Function.Periodic (fun x : ℝ => ∑' k : ℤ, |(k : ℝ) + x| ^ (-s.val)) 1 ∧
    (∀ x : OffLattice, 0 < shortKernelLift s x) ∧
    Tendsto (fun x : ℝ => ∑' k : ℤ, |(k : ℝ) + x| ^ (-s.val))
      (𝓝[{x : ℝ | (x : UnitAddCircle) ≠ 0}] 0) atTop ∧
    (∀ p : ℕ, 1 ≤ p → ∀ x : OffLattice,
      iteratedDeriv p (fun y : ℝ => ∑' k : ℤ, |(k : ℝ) + y| ^ (-s.val)) x.val =
        ((-1 : ℝ) ^ p * ∏ j ∈ Finset.range p, (s.val + (j : ℝ))) *
          ∑' k : ℤ, Real.sign (x.val + k) ^ p / |x.val + k| ^ (s.val + (p : ℝ))) := by
  exact ⟨shortKernelLift_eq_tsum_rpow s, shortKernel_coe s,
    fun p => ⟨hasSumLocallyUniformlyOn_short_images s p,
      fun x => summable_norm_short_image_derivatives s p x.property⟩,
    contDiffOn_short_images s, short_images_even s, short_images_periodic s,
    shortKernelLift_pos s, tendsto_short_images_collision s,
    fun p _ x => iteratedDeriv_short_images_signed s p x.property⟩

end Riesz2
