/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.ConditionalEnergyMoments
public import Riesz2.HelfferSjostrand.MarginalHessian
public import Riesz2.HelfferSjostrand.RemovableGapBarrier
public import Riesz2.ToMathlib.ConvexGradientBound
public import Riesz2.ToMathlib.ConvexEnergyMoments
public import Riesz2.ToMathlib.CollisionDensityBounds
public import Riesz1.Kernel.MeanFieldEnergyKernel
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Topology.Order.Compact

/-!
# Physical lower bounds and conditional minimizers

Deterministic ingredients of Appendix A, for the physical energy, both exponent regimes, and arbitrary retained coordinates.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace Riesz2.ConditionalEnergyMoments

/-- Internal minimization principle for Appendix A. Compact
ambient constraints may include any closed affine fibre, and the index type
may be empty. The function is only required to be continuous in the interior. -/
private theorem exists_isMinOn_inverse_barrier {E ι : Type*} [TopologicalSpace E] [Finite ι]
    {K : Set E} (hK : IsCompact K) (ℓ : ι → E → ℝ)
    (hℓ : ∀ i, Continuous (ℓ i))
    {V : E → ℝ} (hV : ContinuousOn V {x ∈ K | ∀ i, 0 < ℓ i x})
    {c s C : ℝ} (hc : 0 < c) (hs : 0 < s)
    (hbarrier : ∀ x ∈ K, (∀ i, 0 < ℓ i x) →
      ∀ i, c * (ℓ i x) ^ (-s) - C ≤ V x)
    (hne : {x ∈ K | ∀ i, 0 < ℓ i x}.Nonempty) :
    ∃ x ∈ K, (∀ i, 0 < ℓ i x) ∧
      IsMinOn V {x ∈ K | ∀ i, 0 < ℓ i x} x := by
  classical
  obtain ⟨x₀, hx₀, hpos₀⟩ := hne
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, (V x₀ + C) / c < t ^ (-s) :=
    (tendsto_rpow_neg_nhdsGT_zero (neg_neg_of_pos hs)).eventually
      (eventually_gt_atTop _)
  obtain ⟨ε, hε, hsmall⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp hev
  let T : Set E := {x ∈ K | ∀ i, ε ≤ ℓ i x}
  have hclosed : IsClosed {x : E | ∀ i, ε ≤ ℓ i x} := by
    have he : {x : E | ∀ i, ε ≤ ℓ i x} = ⋂ i, {x : E | ε ≤ ℓ i x} := by
      ext x; simp
    rw [he]
    exact isClosed_iInter fun i =>
      isClosed_le (f := fun _ : E => ε) continuous_const (hℓ i)
  have hT : IsCompact T := hK.inter_right hclosed
  have hTΩ : T ⊆ {x ∈ K | ∀ i, 0 < ℓ i x} :=
    fun x hx => ⟨hx.1, fun i => hε.trans_le (hx.2 i)⟩
  have hsub (x : E) (hx : x ∈ K) (hpos : ∀ i, 0 < ℓ i x)
      (hle : V x ≤ V x₀) : x ∈ T := by
    refine ⟨hx, fun i => ?_⟩
    by_contra hi
    have hh := hsmall ⟨hpos i, lt_of_not_ge hi⟩
    have hh' : V x₀ + C < c * (ℓ i x) ^ (-s) := by
      exact (div_lt_iff₀ hc).mp hh |>.trans_eq (mul_comm _ _)
    have hb := hbarrier x hx hpos i
    linarith
  have hx₀T : x₀ ∈ T := hsub x₀ hx₀ hpos₀ le_rfl
  obtain ⟨x, hx, hmin⟩ := hT.exists_isMinOn ⟨x₀, hx₀T⟩ (hV.mono hTΩ)
  refine ⟨x, hx.1, (hTΩ hx).2, fun y hy => ?_⟩
  by_cases hle : V y ≤ V x₀
  · exact hmin (hsub y hy.1 hy.2 hle)
  · exact (hmin hx₀T).trans (le_of_not_ge hle)


private theorem simplex_norm_le (N : ℕ+)
    {y : EuclideanSpace ℝ (Fin (N : ℕ))}
    (hy : (∀ i, 0 ≤ y i) ∧ ∑ i, y i = (N : ℝ)) :
    ‖y‖ ≤ (N : ℝ) ^ 2 := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hbound (i : Fin (N : ℕ)) : y i ≤ (N : ℝ) := by
    rw [← hy.2]
    exact Finset.single_le_sum (fun j _ => hy.1 j) (Finset.mem_univ i)
  have hsq : ‖y‖ ^ 2 ≤ (N : ℝ) * (N : ℝ) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      ∑ i, y i ^ 2 ≤ ∑ _i : Fin (N : ℕ), (N : ℝ) ^ 2 :=
        Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (hy.1 i) (hbound i) 2
      _ = _ := by simp
  nlinarith [norm_nonneg y, sq_nonneg ((N : ℝ) - 1)]

/-- Deterministic ingredient of Appendix A: the nearest-gap
convex remainder has a uniform lower bound on the fixed-volume simplex.
The constant precedes the configuration and all gap labels. -/
theorem physical_energy_lower (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (y : EuclideanSpace ℝ (Fin (N : ℕ)))
        (hy : WithLp.ofLp y ∈ Riesz1.gapSimplex N),
        2 * p.val.1 * ∑ i, (y i) ^ (-p.val.2) - C ≤
          p.val.1 * physicalAmbientGapEnergy p N
            ⟨y, PhysicalEnergy.simplex_subset_ambient N _ hy⟩ := by
  have hp := p.property.1
  obtain ⟨W, hW, hval, hc⟩ :=
    RemovableGapBarrier.nearest_gap_barrier_convex p N hN
  let y₀ : EuclideanSpace ℝ (Fin (N : ℕ)) := WithLp.toLp 2 (fun _ => 1)
  let R : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ :=
    fun y => W y - 2 * ∑ i, (y i) ^ (-p.val.2)
  have hy₀ : WithLp.ofLp y₀ ∈ Riesz1.gapSimplex N := by
    constructor
    · intro i; norm_num [y₀]
    · simp [y₀]
  have hR : DifferentiableAt ℝ R y₀ := by
    apply DifferentiableAt.sub
    · exact ((hW y₀ (PhysicalEnergy.simplex_subset_ambient N _ hy₀)).contDiffAt
        ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds
          (PhysicalEnergy.simplex_subset_ambient N _ hy₀))).differentiableAt (by simp)
    · apply DifferentiableAt.const_mul
      apply DifferentiableAt.fun_sum
      intro i _
      exact ((EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt).rpow_const
        (Or.inl (by norm_num [y₀]))
  let B := |R y₀| + ‖fderiv ℝ R y₀‖ * (2 * (N : ℝ) ^ 2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hlower (y : EuclideanSpace ℝ (Fin (N : ℕ)))
      (hy : WithLp.ofLp y ∈ Riesz1.gapSimplex N) : -B ≤ R y := by
    have hg := ConvexGradient.fderiv_apply_sub_le_sub hc hy₀ hy hR
    have hn : ‖y - y₀‖ ≤ 2 * (N : ℝ) ^ 2 := by
      calc
        ‖y - y₀‖ ≤ ‖y‖ + ‖y₀‖ := norm_sub_le _ _
        _ ≤ (N : ℝ) ^ 2 + (N : ℝ) ^ 2 :=
          add_le_add (simplex_norm_le N ⟨fun i => (hy.1 i).le, hy.2⟩)
            (simplex_norm_le N ⟨fun i => (hy₀.1 i).le, hy₀.2⟩)
        _ = _ := by ring
    have hop := (fderiv ℝ R y₀).le_opNorm (y - y₀)
    have habs := neg_abs_le (fderiv ℝ R y₀ (y - y₀))
    have hmul := mul_le_mul_of_nonneg_left hn (norm_nonneg (fderiv ℝ R y₀))
    rw [Real.norm_eq_abs] at hop
    dsimp [B]
    linarith [neg_abs_le (R y₀)]
  refine ⟨p.val.1 * B + 1, by positivity, fun y hy => ?_⟩
  have hl := mul_le_mul_of_nonneg_left (hlower y hy) p.property.1.le
  have hv := hval ⟨y, PhysicalEnergy.simplex_subset_ambient N _ hy⟩
  dsimp [R] at hl
  rw [hv] at hl
  nlinarith

/-- Deterministic ingredient of Appendix A: each inverse gap
power is bounded by a fixed positive multiple of the shifted physical
energy. The shifted energy is nonnegative throughout the simplex. -/
theorem physical_inverse_gap_bound (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (y : EuclideanSpace ℝ (Fin (N : ℕ)))
        (hy : WithLp.ofLp y ∈ Riesz1.gapSimplex N),
        let U := p.val.1 * physicalAmbientGapEnergy p N
          ⟨y, PhysicalEnergy.simplex_subset_ambient N _ hy⟩
        0 ≤ U + C ∧ ∀ i, (y i) ^ (-p.val.2) ≤ (U + C) / (2 * p.val.1) := by
  obtain ⟨C, hC, hb⟩ := physical_energy_lower p N hN
  refine ⟨C, hC, fun y hy => ?_⟩
  dsimp only
  have hs : 0 ≤ ∑ i, (y i) ^ (-p.val.2) :=
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hy.1 i).le _
  have hbound := hb y hy
  have hp : 0 < 2 * p.val.1 := by linarith [p.property.1]
  constructor
  · nlinarith
  · intro i
    apply (le_div_iff₀ hp).mpr
    have hi := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin (N : ℕ)))) =>
        Real.rpow_nonneg (hy.1 j).le (-p.val.2)) (Finset.mem_univ i)
    nlinarith

/-- Existence clause of Appendix A: on every nonempty fibre
obtained by retaining any set of gap coordinates, the physical energy has
an interior minimizer. The seed specifies a point of the fibre and does
not constrain its exterior coordinates. Point fibres are included. -/
theorem physical_fibre_minimum (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ∀ (I : Set (Fin (N : ℕ))) (x : EuclideanSpace ℝ (Fin (N : ℕ))),
        WithLp.ofLp x ∈ Riesz1.gapSimplex N →
        ∃ y : EuclideanSpace ℝ (Fin (N : ℕ)),
          WithLp.ofLp y ∈ Riesz1.gapSimplex N ∧
          (∀ i ∈ I, y i = x i) ∧
          IsMinOn (fun z => p.val.1 * W z)
            {z | WithLp.ofLp z ∈ Riesz1.gapSimplex N ∧ ∀ i ∈ I, z i = x i} y := by
  classical
  obtain ⟨W, hW, hval, _⟩ := PhysicalEnergy.ambient_derivatives p N
  obtain ⟨C, _, hC⟩ := physical_energy_lower p N hN
  refine ⟨W, hW, hval, fun I x hx => ?_⟩
  let K : Set (EuclideanSpace ℝ (Fin (N : ℕ))) :=
    {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = (N : ℝ) ∧ ∀ i ∈ I, y i = x i}
  have hKc : IsClosed K := by
    have hpos : IsClosed {y : EuclideanSpace ℝ (Fin (N : ℕ)) | ∀ i, 0 ≤ y i} := by
      have he : {y : EuclideanSpace ℝ (Fin (N : ℕ)) | ∀ i, 0 ≤ y i} =
          ⋂ i, {y | 0 ≤ y i} := by ext y; simp
      rw [he]
      exact isClosed_iInter fun i => isClosed_le continuous_const
        (EuclideanSpace.proj (𝕜 := ℝ) i).continuous
    have hsum : IsClosed {y : EuclideanSpace ℝ (Fin (N : ℕ)) |
        ∑ i, y i = (N : ℝ)} :=
      isClosed_eq (by fun_prop) continuous_const
    have heq : IsClosed {y : EuclideanSpace ℝ (Fin (N : ℕ)) |
        ∀ i ∈ I, y i = x i} := by
      have he : {y : EuclideanSpace ℝ (Fin (N : ℕ)) | ∀ i ∈ I, y i = x i} =
          ⋂ i ∈ I, {y | y i = x i} := by ext y; simp
      rw [he]
      exact isClosed_iInter fun i => isClosed_iInter fun _ =>
        isClosed_eq (EuclideanSpace.proj (𝕜 := ℝ) i).continuous continuous_const
    exact hpos.inter (hsum.inter heq)
  have hKb : Bornology.IsBounded K := isBounded_iff_forall_norm_le.mpr
    ⟨(N : ℝ) ^ 2, fun y hy => simplex_norm_le N ⟨hy.1, hy.2.1⟩⟩
  have hK : IsCompact K := Metric.isCompact_iff_isClosed_bounded.mpr ⟨hKc, hKb⟩
  have hsimplex (y : EuclideanSpace ℝ (Fin (N : ℕ)))
      (hy : y ∈ K) (hpos : ∀ i, 0 < y i) :
      WithLp.ofLp y ∈ Riesz1.gapSimplex N := ⟨hpos, hy.2.1⟩
  have hV : ContinuousOn (fun y => p.val.1 * W y)
      {y ∈ K | ∀ i, 0 < y i} := by
    apply continuousOn_const.mul
    exact hW.continuousOn.mono fun y hy =>
      PhysicalEnergy.simplex_subset_ambient N _ (hsimplex y hy.1 hy.2)
  have hbarrier (y : EuclideanSpace ℝ (Fin (N : ℕ)))
      (hy : y ∈ K) (hpos : ∀ i, 0 < y i) (i : Fin (N : ℕ)) :
      (2 * p.val.1) * (y i) ^ (-p.val.2) - C ≤ p.val.1 * W y := by
    have hphys := hC y (hsimplex y hy hpos)
    rw [← hval ⟨y, PhysicalEnergy.simplex_subset_ambient N _ (hsimplex y hy hpos)⟩]
      at hphys
    have hterm := Finset.single_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin (N : ℕ)))) =>
        Real.rpow_nonneg (hpos j).le (-p.val.2)) (Finset.mem_univ i)
    have hmul := mul_le_mul_of_nonneg_left hterm
      (show 0 ≤ 2 * p.val.1 by linarith [p.property.1])
    linarith
  obtain ⟨y, hyK, hypos, hmin⟩ := exists_isMinOn_inverse_barrier hK
    (fun i y => y i) (fun i => (EuclideanSpace.proj (𝕜 := ℝ) i).continuous)
    hV (by linarith [p.property.1] : 0 < 2 * p.val.1) p.property.2.1
    hbarrier ⟨x, ⟨fun i => (hx.1 i).le, hx.2, fun _ _ => rfl⟩, hx.1⟩
  refine ⟨y, hsimplex y hyK hypos, hyK.2.2, fun z hz => ?_⟩
  exact hmin ⟨⟨fun i => (hz.1.1 i).le, hz.1.2, hz.2⟩, hz.1.1⟩

/-- Kernel-value ingredient of Appendix A. The bound uses the
zeroth-order companion-library estimate in the long-range regime and the
convergent positive image sum in the short-range regime. -/
theorem kernel_value_bound (p : Parameters) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : {u : ℝ // 0 < u ∧ u < 1})
      (δ : ℝ), 0 < δ → δ ≤ u.val → δ ≤ 1 - u.val →
      |kernelAtParameters p (interiorCirclePoint u)| ≤ C * δ ^ (-p.val.2) := by
  by_cases hs : p.val.2 < 1
  · let s : Riesz1.RieszExponent := ⟨p.val.2, p.property.2.1, hs⟩
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hb, _, _⟩ := Riesz1.fundamental_series s
    obtain ⟨C, hC, hb⟩ := hb 0
    refine ⟨C, hC, fun u δ hδ hu huc => ?_⟩
    have hd : δ ≤ dist (u.val : UnitAddCircle) 0 :=
      (le_min hu huc).trans (Riesz1.min_le_dist_coe _)
    have hn := (interiorCirclePoint u).property
    have hbound := hb u.val hn
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at hbound
    calc
      |kernelAtParameters p (interiorCirclePoint u)| =
          |Riesz1.rieszRepresentative s u.val| := by
        simp only [kernelAtParameters, hs, ↓reduceDIte, Riesz1.rieszKernel,
          interiorCirclePoint, s]
      _ ≤ C * dist (u.val : UnitAddCircle) 0 ^ (-p.val.2) := hbound
      _ ≤ C * δ ^ (-p.val.2) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hδ hd (neg_nonpos.mpr p.property.2.1.le)) hC.le
  · have hs' : 1 < p.val.2 :=
      lt_of_le_of_ne (le_of_not_gt hs) (Ne.symm p.property.2.2)
    let s : ShortExponent := ⟨p.val.2, hs'⟩
    refine ⟨PeriodicPower.bound p.val.2 hs', PeriodicPower.bound_pos _ _,
      fun u δ hδ hu huc => ?_⟩
    have hrep : kernelAtParameters p (interiorCirclePoint u) =
        ∑' k : ℤ, |u.val + (k : ℝ) * 1| ^ (-p.val.2) := by
      simp only [kernelAtParameters, hs, ↓reduceDIte]
      rw [show interiorCirclePoint u =
        ⟨(u.val : UnitAddCircle), (interiorCirclePoint u).property⟩ from rfl,
        shortKernel_coe s ⟨u.val, (interiorCirclePoint u).property⟩,
        shortKernelLift_eq_tsum_rpow]
      congr 1
      funext k
      simp only [mul_one, add_comm, s]
    rw [hrep, abs_of_nonneg (tsum_nonneg fun k => Real.rpow_nonneg (abs_nonneg _) _)]
    exact (PeriodicPower.summable_and_le hs' hδ hu huc).2

/-- Deterministic energy estimate used in Appendix A: a lower
bound on every full gap controls the actual temperature-weighted energy.
The constant is independent of the point and its gap lower bound. -/
theorem physical_energy_upper (p : Parameters) (N : ℕ+) (_hN : 2 ≤ (N : ℕ)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (y : EuclideanSpace ℝ (Fin (N : ℕ)))
        (hy : WithLp.ofLp y ∈ Riesz1.gapSimplex N)
        (δ : ℝ), 0 < δ → (∀ i, δ ≤ y i) →
        p.val.1 * physicalAmbientGapEnergy p N
          ⟨y, PhysicalEnergy.simplex_subset_ambient N _ hy⟩ ≤ C * δ ^ (-p.val.2) := by
  obtain ⟨C, hC, hb⟩ := kernel_value_bound p
  have hp := p.property.1
  have hNr : (0 : ℝ) < N := by exact_mod_cast N.pos
  refine ⟨2 * p.val.1 * C * (N : ℝ) ^ 2, by positivity, fun y hy δ hδ hgap => ?_⟩
  have hδN : 0 < δ / (N : ℝ) := div_pos hδ hNr
  have hterm (i : Fin (N : ℕ)) (r : Fin ((N : ℕ) / 2)) :
      (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
        kernelAtParameters p (interiorCirclePoint
          ⟨cyclicGapSum N i (r.val + 1) (WithLp.ofLp y) / (N : ℝ), by
            have h := PhysicalEnergy.gapSum_mem N i (Nat.succ_pos r.val)
              ((Nat.succ_le_of_lt r.isLt).trans_lt (Nat.div_lt_self N.pos (by norm_num))) _ hy
            exact ⟨div_pos h.1 hNr, (div_lt_one hNr).mpr h.2⟩⟩) ≤
        2 * C * (δ / (N : ℝ)) ^ (-p.val.2) := by
    have hr1 : (1 : ℝ) ≤ r.val + 1 := by
      linarith [Nat.cast_nonneg (α := ℝ) r.val]
    have hrNat : r.val + 1 + 1 ≤ (N : ℕ) := Nat.succ_le_of_lt
      ((Nat.succ_le_of_lt r.isLt).trans_lt (Nat.div_lt_self N.pos (by norm_num)))
    have hrN : (r.val : ℝ) + 1 ≤ (N : ℝ) - 1 := by
      have hh : (r.val : ℝ) + 1 + 1 ≤ (N : ℝ) := by exact_mod_cast hrNat
      linarith
    have hleft := (PhysicalEnergy.gapSum_bounds N i (r.val + 1) (WithLp.ofLp y)
      (fun j => ⟨hgap j, show y j ≤ (N : ℝ) by
        rw [← hy.2]; exact Finset.single_le_sum (fun k _ => (hy.1 k).le)
          (Finset.mem_univ j)⟩)).1
    have hright := PhysicalEnergy.gapSum_complement_lower N i
      ((Nat.succ_le_of_lt r.isLt).trans (Nat.div_le_self (N : ℕ) 2)) _ hgap hy.2
    have hl : δ / (N : ℝ) ≤ cyclicGapSum N i (r.val + 1) (WithLp.ofLp y) / N := by
      apply (div_le_div_iff_of_pos_right hNr).mpr
      push_cast at hleft
      nlinarith
    have hr : δ / (N : ℝ) ≤ 1 - cyclicGapSum N i (r.val + 1) (WithLp.ofLp y) / N := by
      rw [← div_self hNr.ne', ← sub_div]
      apply (div_le_div_iff_of_pos_right hNr).mpr
      push_cast at hright
      nlinarith
    have hmem := PhysicalEnergy.gapSum_mem N i (Nat.succ_pos r.val)
      ((Nat.succ_le_of_lt r.isLt).trans_lt (Nat.div_lt_self N.pos (by norm_num))) _ hy
    have hk := hb ⟨cyclicGapSum N i (r.val + 1) (WithLp.ofLp y) / N,
      div_pos hmem.1 hNr, (div_lt_one hNr).mpr hmem.2⟩ (δ / N) hδN hl hr
    have hw : 0 ≤ (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) ∧
        (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) ≤ 2 := by
      split_ifs <;> norm_num
    calc
      _ ≤ (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
          |kernelAtParameters p (interiorCirclePoint _)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hw.1
      _ ≤ 2 * (C * (δ / (N : ℝ)) ^ (-p.val.2)) :=
        mul_le_mul hw.2 hk (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun r _ => hterm i r
  have hscaled := mul_le_mul_of_nonneg_left hsum
    (mul_nonneg hp.le (Real.rpow_nonneg hNr.le (-p.val.2)))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hscaled
  have hcancel : (N : ℝ) ^ (-p.val.2) * (δ / (N : ℝ)) ^ (-p.val.2) =
      δ ^ (-p.val.2) := by
    rw [Real.div_rpow hδ.le hNr.le]
    exact mul_div_cancel₀ _ (Real.rpow_pos_of_pos hNr _).ne'
  have he : p.val.1 * (N : ℝ) ^ (-p.val.2) *
      ((N : ℝ) * (((N : ℕ) / 2 : ℕ) : ℝ) *
        (2 * C * (δ / (N : ℝ)) ^ (-p.val.2))) =
      2 * p.val.1 * C * (N : ℝ) * (((N : ℕ) / 2 : ℕ) : ℝ) * δ ^ (-p.val.2) := by
    calc
      _ = (2 * p.val.1 * C * (N : ℝ) * (((N : ℕ) / 2 : ℕ) : ℝ)) *
          ((N : ℝ) ^ (-p.val.2) * (δ / (N : ℝ)) ^ (-p.val.2)) := by ring
      _ = _ := by rw [hcancel]
  have hcount : ((((N : ℕ) / 2 : ℕ)) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.div_le_self (N : ℕ) 2
  change p.val.1 * ((N : ℝ) ^ (-p.val.2) * _) ≤ _
  rw [← mul_assoc]
  refine hscaled.trans ?_
  calc
    p.val.1 * (N : ℝ) ^ (-p.val.2) *
        ((N : ℝ) * ((((N : ℕ) / 2 : ℕ) : ℝ) *
          (2 * C * (δ / (N : ℝ)) ^ (-p.val.2)))) =
        2 * p.val.1 * C * (N : ℝ) * (((N : ℕ) / 2 : ℕ) : ℝ) *
          δ ^ (-p.val.2) := by simpa only [mul_assoc] using he
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hcount
        (show 0 ≤ 2 * p.val.1 * C * (N : ℝ) * δ ^ (-p.val.2) by positivity)
      nlinarith

/-- The minimum and its upper bound in Appendix A, for every
retained set. Taking `δ` to be the minimum of the active gaps and exterior
mass gives the stated `C_N (1 + δ ^ (-s))` bound. Only values at retained
coordinates are used. Constants are independent of those values and labels. -/
theorem physical_fibre_minimum_bound (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ (I : Finset (Fin (N : ℕ))), I.card < (N : ℕ) →
          ∀ (x : EuclideanSpace ℝ (Fin (N : ℕ))),
            ∀ δ : ℝ, 0 < δ → (∀ i ∈ I, δ ≤ x i) →
              δ ≤ (N : ℝ) - ∑ i ∈ I, x i →
              ∃ y : EuclideanSpace ℝ (Fin (N : ℕ)),
                WithLp.ofLp y ∈ Riesz1.gapSimplex N ∧
                (∀ i ∈ I, y i = x i) ∧
                IsMinOn (fun z => p.val.1 * W z)
                  {z | WithLp.ofLp z ∈ Riesz1.gapSimplex N ∧ ∀ i ∈ I, z i = x i} y ∧
                p.val.1 * W y ≤ C * (1 + δ ^ (-p.val.2)) := by
  classical
  obtain ⟨W, hW, hval, hmin⟩ := physical_fibre_minimum p N hN
  obtain ⟨C, hC, hb⟩ := physical_energy_upper p N hN
  have hp := p.property.1
  have hNr : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  refine ⟨W, hW, hval, C * (N : ℝ) ^ p.val.2, by positivity,
    fun I hI x δ hδ hδI hδL => ?_⟩
  let m : ℝ := (N : ℝ) - I.card
  let L : ℝ := (N : ℝ) - ∑ i ∈ I, x i
  have hm : 0 < m := by
    dsimp [m]
    exact sub_pos.mpr (by exact_mod_cast hI)
  have hmN : m ≤ (N : ℝ) := by dsimp [m]; linarith [Nat.cast_nonneg (α := ℝ) I.card]
  have hL : 0 < L := hδ.trans_le hδL
  let t : EuclideanSpace ℝ (Fin (N : ℕ)) :=
    WithLp.toLp 2 (fun i => if i ∈ I then x i else L / m)
  have htI (i : Fin (N : ℕ)) (hi : i ∈ I) : t i = x i := by simp [t, hi]
  have htpos (i : Fin (N : ℕ)) : 0 < t i := by
    by_cases hi : i ∈ I
    · rw [htI i hi]
      exact hδ.trans_le (hδI i hi)
    · simpa [t, hi] using div_pos hL hm
  have htsum : ∑ i, t i = (N : ℝ) := by
    have he : (∑ i, t i) = ∑ i ∈ I, x i + ((N : ℕ) - I.card : ℕ) * (L / m) := by
      have hcompl : Finset.univ.filter (fun i => i ∉ I) = Iᶜ := by ext i; simp
      simp [t, Finset.sum_ite, hcompl, Finset.card_compl]
    rw [he]
    have hmcast : (((N : ℕ) - I.card : ℕ) : ℝ) = m := by
      dsimp [m]
      exact Nat.cast_sub (Nat.le_of_lt hI)
    rw [hmcast, mul_div_cancel₀ L hm.ne']
    dsimp [L]
    ring
  have ht : WithLp.ofLp t ∈ Riesz1.gapSimplex N := ⟨htpos, htsum⟩
  have hgap (i : Fin (N : ℕ)) : δ / (N : ℝ) ≤ t i := by
    by_cases hi : i ∈ I
    · rw [htI i hi]
      exact (div_le_self hδ.le hN1).trans (hδI i hi)
    · simp only [t, ite_eq_right_iff.mpr (fun h => (hi h).elim)]
      apply (div_le_div_iff₀ hNr hm).mpr
      have hh := mul_le_mul_of_nonneg_left hmN hδ.le
      have hh' := mul_le_mul_of_nonneg_right hδL hNr.le
      exact hh.trans hh'
  obtain ⟨y, hy, hyI, hymin⟩ := hmin (I : Set (Fin (N : ℕ))) t ht
  have hyIx : ∀ i ∈ I, y i = x i := fun i hi => (hyI i hi).trans (htI i hi)
  have hyminx : IsMinOn (fun z => p.val.1 * W z)
      {z | WithLp.ofLp z ∈ Riesz1.gapSimplex N ∧ ∀ i ∈ I, z i = x i} y := by
    intro z hz
    exact hymin ⟨hz.1, fun i hi => (hz.2 i hi).trans (htI i hi).symm⟩
  refine ⟨y, hy, hyIx, hyminx, ?_⟩
  have htrial := hb t ht (δ / N) (div_pos hδ hNr) hgap
  rw [← hval ⟨t, PhysicalEnergy.simplex_subset_ambient N _ ht⟩] at htrial
  have hybound := (hyminx ⟨ht, htI⟩).trans htrial
  have heq : (δ / (N : ℝ)) ^ (-p.val.2) =
      (N : ℝ) ^ p.val.2 * δ ^ (-p.val.2) := by
    rw [Real.div_rpow hδ.le hNr.le, Real.rpow_neg hNr.le,
      div_inv_eq_mul, mul_comm]
  rw [heq] at hybound
  have hadd : 0 ≤ C * (N : ℝ) ^ p.val.2 := by positivity
  nlinarith

/-- Collision domination used in Appendix A: the
physical Gibbs density is bounded by the exponential nearest-gap barrier
for any selected collection of coordinates. The constant is uniform on
the whole fixed-volume simplex. -/
theorem physical_density_barrier (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (y : EuclideanSpace ℝ (Fin (N : ℕ)))
        (hy : WithLp.ofLp y ∈ Riesz1.gapSimplex N)
        (I : Finset (Fin (N : ℕ))),
        Real.exp (-p.val.1 * physicalAmbientGapEnergy p N
          ⟨y, PhysicalEnergy.simplex_subset_ambient N _ hy⟩) ≤
          C * Real.exp (-(2 * p.val.1) * ∑ i ∈ I, (y i) ^ (-p.val.2)) := by
  obtain ⟨B, _, hB⟩ := physical_energy_lower p N hN
  refine ⟨Real.exp B, Real.exp_pos _, fun y hy I => ?_⟩
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hsum : (∑ i ∈ I, (y i) ^ (-p.val.2)) ≤ ∑ i, (y i) ^ (-p.val.2) :=
    Finset.sum_le_univ_sum_of_nonneg fun i => Real.rpow_nonneg (hy.1 i).le _
  have hmul := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ 2 * p.val.1 by linarith [p.property.1])
  have hh := hB y hy
  linarith

/-- Physical scalar flatness needed in Appendix A:
along any collision within the simplex, every inverse power times the
actual Gibbs density tends to zero. -/
theorem tendsto_physical_density_inverse_power (p : Parameters) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) {A : Type*} {l : Filter A}
    (y : A → {y : EuclideanSpace ℝ (Fin (N : ℕ)) |
      WithLp.ofLp y ∈ Riesz1.gapSimplex N})
    (i : Fin (N : ℕ)) (hgap : Tendsto (fun a => y a |>.val i) l (𝓝[>] 0))
    (r : ℝ) :
    Tendsto (fun a => ((y a).val i) ^ (-r) *
      Real.exp (-p.val.1 * physicalAmbientGapEnergy p N
        ⟨(y a).val, PhysicalEnergy.simplex_subset_ambient N _ (y a).property⟩))
      l (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := physical_density_barrier p N hN
  have ht := (CollisionDensity.tendsto_inverse_power_mul_exp p.property.2.1
    (by linarith [p.property.1] : 0 < 2 * p.val.1) r).comp hgap
  have ht' := ht.const_mul C
  rw [mul_zero] at ht'
  apply squeeze_zero (fun a => mul_nonneg
    (Real.rpow_nonneg ((y a).property.1 i).le _) (Real.exp_nonneg _)) _ ht'
  intro a
  have hh := hbound (y a).val (y a).property {i}
  simp only [Finset.sum_singleton] at hh
  have hm := mul_le_mul_of_nonneg_left hh
    (Real.rpow_nonneg ((y a).property.1 i).le (-r))
  simpa only [mul_left_comm, mul_assoc, Function.comp_apply] using hm

end Riesz2.ConditionalEnergyMoments
