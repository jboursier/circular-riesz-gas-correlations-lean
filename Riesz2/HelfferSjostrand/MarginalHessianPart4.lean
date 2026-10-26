/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.MarginalHessianPart2
public import Riesz2.HelfferSjostrand.ConditionalEnergyMomentsPart3
public import Riesz2.ToMathlib.ExponentialDerivativeBounds

/-!
# Physical energy tensors for proper marginal calculus

The all-order inverse-gap estimates in Appendix A.
The energy realizations agree with the physical energy on its whole
ambient domain. Estimates on the simplex include all ambient tensor directions.
The actual supported density is smooth across collision faces in affine
mass-hyperplane charts, with common integrable exterior derivative majorants.
-/

public section
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace Riesz2.MarginalHessian

private theorem scalar_realization (p : Parameters) :
    ∃ K : ℝ → ℝ, ContDiffOn ℝ ∞ K (Ioo 0 1) ∧
      (∀ x : Ioo (0 : ℝ) 1,
        K x.val = kernelAtParameters p (interiorCirclePoint x)) ∧
      ∀ (j : ℕ+) (x : Ioo (0 : ℝ) 1),
        iteratedDeriv j K x.val = PhysicalEnergy.kernelDerivative p j
          ⟨x.val, (interiorCirclePoint x).property⟩ := by
  have hsub : Ioo (0 : ℝ) 1 ⊆ {x : ℝ | (x : UnitAddCircle) ≠ 0} :=
    fun x hx => (interiorCirclePoint ⟨x, hx⟩).property
  by_cases h : p.val.2 < 1
  · refine ⟨fun x => Riesz1.rieszRepresentative ⟨p.val.2, p.property.2.1, h⟩ x,
      (companionKernelIdentification _).1.mono hsub, ?_, ?_⟩
    · intro x
      simp only [kernelAtParameters, h, ↓reduceDIte, Riesz1.rieszKernel]
      rfl
    · intro j x
      simp only [PhysicalEnergy.kernelDerivative, h, ↓reduceDIte]
  · let s : ShortExponent :=
      ⟨p.val.2, lt_of_le_of_ne (le_of_not_gt h) (Ne.symm p.property.2.2)⟩
    refine ⟨fun x => ∑' k : ℤ, |(k : ℝ) + x| ^ (-p.val.2),
      (contDiffOn_short_images s).mono hsub, ?_, ?_⟩
    · intro x
      simp only [kernelAtParameters, h, ↓reduceDIte]
      exact (shortKernelLift_eq_tsum_rpow s
        ⟨x.val, (interiorCirclePoint x).property⟩).symm.trans (shortKernel_coe s _).symm
    · intro j x
      simp only [PhysicalEnergy.kernelDerivative, h, ↓reduceDIte]

/-- The physical tensor estimate in Appendix A.
The representative is the temperature-weighted energy on
the whole ambient domain. Every positive-order tensor is bounded on the
mass simplex by the indicated inverse power of a lower gap bound. -/
theorem physical_energy_tensors (p : Parameters) (N : ℕ+) :
    ∃ U : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        U y.val = p.val.1 * physicalAmbientGapEnergy p N y) ∧
      ∀ j : ℕ+, ∃ C : ℝ, 0 < C ∧
        ∀ (y : EuclideanSpace ℝ (Fin (N : ℕ))),
          WithLp.ofLp y ∈ Riesz1.gapSimplex N →
          ∀ δ : ℝ, 0 < δ → (∀ i, δ ≤ y i) →
            ‖iteratedFDeriv ℝ j U y‖ ≤ C * δ ^ (-p.val.2 - (j : ℝ)) := by
  classical
  obtain ⟨K, hK, hval, hjet⟩ := scalar_realization p
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  let I := Fin (N : ℕ) × Fin ((N : ℕ) / 2)
  let l : I → EuclideanSpace ℝ (Fin (N : ℕ)) →L[ℝ] ℝ :=
    fun q => (N : ℝ)⁻¹ • PhysicalEnergy.intervalLinear N q.1 (q.2.val + 1)
  let c : I → ℝ := fun q => p.val.1 * (N : ℝ) ^ (-p.val.2) *
    (2 - if 2 * (q.2.val + 1) = (N : ℕ) then 1 else 0)
  let U := fun y => ∑ q : I, c q * K (l q y)
  have hl (q : I) (y : EuclideanSpace ℝ (Fin (N : ℕ))) :
      l q y = cyclicGapSum N q.1 (q.2.val + 1) (WithLp.ofLp y) / N := by
    simp only [l, smul_apply, smul_eq_mul, PhysicalEnergy.intervalLinear_apply,
      div_eq_mul_inv]
    ring
  have harg (y : EuclideanSpace ℝ (Fin (N : ℕ)))
      (hy : y ∈ gapAmbientDomain N) (q : I) : l q y ∈ Ioo (0 : ℝ) 1 := by
    have hi := hy q.1 (q.2.val + 1) (by omega) (by have := q.2.isLt; omega)
    rw [hl]
    exact ⟨div_pos hi.1 hN, (div_lt_one hN).mpr hi.2⟩
  refine ⟨U, ?_, ?_, fun j => ?_⟩
  · exact ContDiffOn.sum fun q _ =>
      contDiffOn_const.mul (hK.comp (l q).contDiff.contDiffOn (fun y hy => harg y hy q))
  · intro y
    unfold physicalAmbientGapEnergy
    simp only [U, I, c, Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro r _
    have hv := hval ⟨l (i, r) y.val, harg y.val y.property (i, r)⟩
    simp only [hl] at hv
    rw [hl, hv]
    simp only [mul_assoc]
    rfl
  · obtain ⟨B, hB, hb⟩ := kernel_derivative_bound p j
    let C := ∑ q : I, |c q| * (B * (N : ℝ) ^ (p.val.2 + (j : ℝ))) * ‖l q‖ ^ (j : ℕ)
    have hC : 0 ≤ C := Finset.sum_nonneg fun q _ => by positivity
    refine ⟨C + 1, by positivity, fun y hy δ hδ hgap => ?_⟩
    have ha : y ∈ gapAmbientDomain N := PhysicalEnergy.simplex_subset_ambient N _ hy
    have hc (q : I) : ContDiffAt ℝ (j : ℕ) (fun z => K (l q z)) y :=
      ((hK.of_le (by simp)).contDiffAt (isOpen_Ioo.mem_nhds (harg y ha q))).comp y
        (l q).contDiff.contDiffAt
    have ht : ‖iteratedFDeriv ℝ j U y‖ ≤
        ∑ q : I, |c q| * |iteratedDeriv j K (l q y)| * ‖l q‖ ^ (j : ℕ) := by
      dsimp only [U]
      rw [iteratedFDeriv_fun_sum_apply (fun q _ => contDiffAt_const.mul (hc q))]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro q _
      change ‖iteratedFDeriv ℝ j (c q • (fun z => K (l q z))) y‖ ≤ _
      rw [iteratedFDeriv_const_smul_apply (hc q), norm_smul, Real.norm_eq_abs]
      have he := (l q).iteratedFDerivWithin_comp_right hK isOpen_Ioo.uniqueDiffOn
        (isOpen_Ioo.preimage (l q).continuous).uniqueDiffOn (harg y ha q)
        (i := (j : ℕ)) (by simp)
      rw [iteratedFDerivWithin_of_isOpen (j : ℕ)
        (isOpen_Ioo.preimage (l q).continuous) (harg y ha q),
        iteratedFDerivWithin_of_isOpen (j : ℕ) isOpen_Ioo (harg y ha q)] at he
      change iteratedFDeriv ℝ j (fun z => K (l q z)) y = _ at he
      rw [he]
      have hb := (iteratedFDeriv ℝ j K (l q y)).norm_compContinuousLinearMap_le
        (fun _ : Fin (j : ℕ) => l q)
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at hb
      exact (mul_le_mul_of_nonneg_left hb (abs_nonneg _)).trans_eq (mul_assoc _ _ _).symm
    have hscalar (q : I) :
        |iteratedDeriv j K (l q y)| ≤
          (B * (N : ℝ) ^ (p.val.2 + (j : ℝ))) * δ ^ (-p.val.2 - (j : ℝ)) := by
      rw [hjet j ⟨l q y, harg y ha q⟩]
      have hupper (i : Fin (N : ℕ)) : y i ≤ (N : ℝ) := by
        rw [← hy.2]
        exact Finset.single_le_sum (fun k _ => (hy.1 k).le) (Finset.mem_univ i)
      have hg := (PhysicalEnergy.gapSum_bounds N q.1 (q.2.val + 1)
        (WithLp.ofLp y) (fun i => ⟨hgap i, hupper i⟩)).1
      have hrNat : q.2.val + 1 + 1 ≤ (N : ℕ) := Nat.succ_le_of_lt
        ((Nat.succ_le_of_lt q.2.isLt).trans_lt (Nat.div_lt_self N.pos (by norm_num)))
      have hrN : (q.2.val : ℝ) + 1 + 1 ≤ (N : ℝ) := by exact_mod_cast hrNat
      have hgc := PhysicalEnergy.gapSum_complement_lower N q.1
        ((Nat.succ_le_of_lt q.2.isLt).trans (Nat.div_le_self (N : ℕ) 2))
        (WithLp.ofLp y) hgap hy.2
      have hleft : δ / (N : ℝ) ≤ l q y := by
        rw [hl]
        apply (div_le_div_iff_of_pos_right hN).mpr
        push_cast at hg
        nlinarith [Nat.cast_nonneg (α := ℝ) q.2.val]
      have hright : δ / (N : ℝ) ≤ 1 - l q y := by
        rw [hl, ← div_self hN.ne', ← sub_div]
        apply (div_le_div_iff_of_pos_right hN).mpr
        push_cast at hgc
        nlinarith
      have hb' := hb ⟨l q y, (interiorCirclePoint ⟨l q y, harg y ha q⟩).property⟩
        (δ / N) (div_pos hδ hN) hleft hright
      have he : (δ / (N : ℝ)) ^ (-p.val.2 - (j : ℝ)) =
          (N : ℝ) ^ (p.val.2 + (j : ℝ)) * δ ^ (-p.val.2 - (j : ℝ)) := by
        rw [Real.div_rpow hδ.le hN.le,
          show -p.val.2 - (j : ℝ) = -(p.val.2 + (j : ℝ)) by ring,
          Real.rpow_neg hN.le, div_eq_mul_inv, inv_inv]
        ring
      rw [he] at hb'
      simpa only [mul_assoc] using hb'
    have hs : ‖iteratedFDeriv ℝ j U y‖ ≤ C * δ ^ (-p.val.2 - (j : ℝ)) := by
      apply ht.trans
      dsimp only [C]
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro q _
      calc
        _ ≤ |c q| * ((B * (N : ℝ) ^ (p.val.2 + (j : ℝ))) *
            δ ^ (-p.val.2 - (j : ℝ))) * ‖l q‖ ^ (j : ℕ) := by
          gcongr
          exact hscalar q
        _ = _ := by ring
    exact hs.trans (mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg hδ.le _))

/-- The physical density tensor estimate in Appendix A.
Every derivative order retains exponential suppression at the smallest
gap. -/
theorem physical_density_tensors (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    ∃ U : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        U y.val = p.val.1 * physicalAmbientGapEnergy p N y) ∧
      ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ (y : EuclideanSpace ℝ (Fin (N : ℕ))),
          WithLp.ofLp y ∈ Riesz1.gapSimplex N →
          ∀ δ : ℝ, 0 < δ → δ ≤ 1 → (∀ i, δ ≤ y i) → (∃ i, y i = δ) →
            ‖iteratedFDeriv ℝ n (fun z => Real.exp (-U z)) y‖ ≤
              C * Real.exp (-p.val.1 * δ ^ (-p.val.2)) := by
  classical
  obtain ⟨U, hU, hv, hT⟩ := physical_energy_tensors p N
  choose B hB hjet using hT
  obtain ⟨K, _, hK⟩ := ConditionalEnergyMoments.physical_energy_lower p N hN
  refine ⟨U, hU, hv, fun n => ?_⟩
  let A : ℝ := 1 + ∑ i ∈ Finset.range n, B ⟨i + 1, Nat.succ_pos i⟩
  have hA : 1 ≤ A := by
    dsimp only [A]
    linarith [Finset.sum_nonneg (s := Finset.range n)
      (fun i _ => (hB ⟨i + 1, Nat.succ_pos i⟩).le)]
  obtain ⟨C, hC, hb⟩ := ExponentialDerivative.inverse_barrier_bound
    (E := EuclideanSpace ℝ (Fin (N : ℕ))) p.property.2.1
    (by linarith [p.property.1] : 0 < 2 * p.val.1)
    n A K (p.val.2 + n) (by linarith)
  refine ⟨C, hC, fun y hy δ hδ hδ1 hgap hmin => ?_⟩
  have ha := PhysicalEnergy.simplex_subset_ambient N _ hy
  have hlower : -U y ≤ K - (2 * p.val.1) * δ ^ (-p.val.2) := by
    obtain ⟨i, hi⟩ := hmin
    have hh := hK y hy
    have hs := Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin (N : ℕ))))
      (fun j _ => Real.rpow_nonneg (hy.1 j).le (-p.val.2)) (Finset.mem_univ i)
    rw [hi] at hs
    rw [← hv ⟨y, ha⟩] at hh
    have hp := p.property.1
    nlinarith
  have ht (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDeriv ℝ i (fun z => -U z) y‖ ≤ (A * δ ^ (-(p.val.2 + n))) ^ i := by
    let j : ℕ+ := ⟨i, by omega⟩
    have hUi : ContDiffAt ℝ i U y :=
      (hU.of_le (by simp)).contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds ha)
    have he : (fun z => -U z) = (-1 : ℝ) • U := by ext z; simp
    rw [he, iteratedFDeriv_const_smul_apply hUi, norm_smul]
    norm_num only [Real.norm_eq_abs, abs_neg, abs_one, one_mul]
    have hBj : B j ≤ A := by
      have hh := Finset.single_le_sum
        (s := Finset.range n) (fun k _ => (hB ⟨k + 1, Nat.succ_pos k⟩).le)
        (Finset.mem_range.mpr (show i - 1 < n by omega))
      have hj : (⟨i - 1 + 1, Nat.succ_pos (i - 1)⟩ : ℕ+) = j := by
        apply Subtype.ext
        dsimp only [j]
        omega
      rw [hj] at hh
      dsimp only [A]
      linarith
    have hBi : B j ≤ A ^ i := hBj.trans (le_self_pow₀ hA (by omega))
    have hpow : δ ^ (-p.val.2 - (i : ℝ)) ≤ (δ ^ (-(p.val.2 + n))) ^ i := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
      apply Real.rpow_le_rpow_of_exponent_ge hδ hδ1
      have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi
      have hinR : (i : ℝ) ≤ n := by exact_mod_cast hin
      have hs := p.property.2.1
      nlinarith
    calc
      _ ≤ B j * δ ^ (-p.val.2 - (i : ℝ)) := hjet j y hy δ hδ hgap
      _ ≤ A ^ i * (δ ^ (-(p.val.2 + n))) ^ i :=
        mul_le_mul hBi hpow (Real.rpow_nonneg hδ.le _) (by positivity)
      _ = _ := (mul_pow _ _ _).symm
  have h := hb (gapAmbientDomain N) (PhysicalEnergy.isOpen_gapAmbientDomain N)
    (fun z => -U z) (hU.neg.of_le (by simp)) y ha δ hδ hδ1 hlower ht
  convert h using 1
  congr 3
  ring

/-- Polynomially weighted physical density tensors still vanish
exponentially, as required in Appendix A. The constants
precede the simplex point and its smallest gap. -/
theorem physical_density_weighted_tensors (p : Parameters) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) :
    ∃ U : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        U y.val = p.val.1 * physicalAmbientGapEnergy p N y) ∧
      ∀ (n : ℕ) (r : ℝ), ∃ C : ℝ, 0 ≤ C ∧
        ∀ (y : EuclideanSpace ℝ (Fin (N : ℕ))),
          WithLp.ofLp y ∈ Riesz1.gapSimplex N →
          ∀ δ : ℝ, 0 < δ → δ ≤ 1 → (∀ i, δ ≤ y i) → (∃ i, y i = δ) →
            δ ^ (-r) * ‖iteratedFDeriv ℝ n (fun z => Real.exp (-U z)) y‖ ≤
              C * Real.exp (-(p.val.1 / 2) * δ ^ (-p.val.2)) := by
  obtain ⟨U, hU, hv, ht⟩ := physical_density_tensors p N hN
  refine ⟨U, hU, hv, fun n r => ?_⟩
  obtain ⟨A, hA, ha⟩ := ht n
  obtain ⟨B, hB, hb⟩ := CollisionDensity.inverse_power_absorption
    p.property.2.1 p.property.1 r
  refine ⟨A * B, mul_nonneg hA hB, fun y hy δ hδ hδ1 hgap hmin => ?_⟩
  calc
    _ ≤ δ ^ (-r) * (A * Real.exp (-p.val.1 * δ ^ (-p.val.2))) :=
      mul_le_mul_of_nonneg_left (ha y hy δ hδ hδ1 hgap hmin)
        (Real.rpow_nonneg hδ.le _)
    _ = A * (δ ^ (-r) * Real.exp (-p.val.1 * δ ^ (-p.val.2))) := by ring
    _ ≤ A * (B * Real.exp (-(p.val.1 / 2) * δ ^ (-p.val.2))) :=
      mul_le_mul_of_nonneg_left (hb δ hδ hδ1) hA
    _ = _ := by ring

/-- Affine-chart version of the physical estimate in Appendix A. It applies in particular to fixed compensated exterior
charts, with no restriction on their ambient tensor directions. -/
theorem physical_affine_density_tensors (p : Parameters) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) :
    ∃ U : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        U y.val = p.val.1 * physicalAmbientGapEnergy p N y) ∧
      ∀ (k : ℕ) (a : EuclideanSpace ℝ (Fin k) →ᴬ[ℝ]
          EuclideanSpace ℝ (Fin (N : ℕ))) (n : ℕ) (r : ℝ),
        ∃ C : ℝ, 0 ≤ C ∧ ∀ x : EuclideanSpace ℝ (Fin k),
          WithLp.ofLp (a x) ∈ Riesz1.gapSimplex N →
          ∀ δ : ℝ, 0 < δ → δ ≤ 1 → (∀ i, δ ≤ a x i) → (∃ i, a x i = δ) →
            δ ^ (-r) * ‖iteratedFDeriv ℝ n (fun z => Real.exp (-U (a z))) x‖ ≤
              C * Real.exp (-(p.val.1 / 2) * δ ^ (-p.val.2)) := by
  obtain ⟨U, hU, hv, ht⟩ := physical_density_weighted_tensors p N hN
  refine ⟨U, hU, hv, fun k a n r => ?_⟩
  obtain ⟨C, hC, hb⟩ := ht n r
  refine ⟨C * ‖a.contLinear‖ ^ n, by positivity,
    fun x hx δ hδ hδ1 hgap hmin => ?_⟩
  let f := fun y => Real.exp (-U y)
  have hf : ContDiffOn ℝ n f (gapAmbientDomain N) :=
    (hU.neg.exp).of_le (by simp)
  have ha := PhysicalEnergy.simplex_subset_ambient N _ hx
  have hQ := PhysicalEnergy.isOpen_gapAmbientDomain N
  have hp := (hf.ftaylorSeriesWithin hQ.uniqueDiffOn).comp_continuousAffineMap a
  have he := hp.eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl
    (hQ.preimage a.continuous).uniqueDiffOn ha
  change (iteratedFDerivWithin ℝ n f (gapAmbientDomain N) (a x)).compContinuousLinearMap
    (fun _ => a.contLinear) = _ at he
  rw [iteratedFDerivWithin_of_isOpen n (hQ.preimage a.continuous) ha,
    iteratedFDerivWithin_of_isOpen n hQ ha] at he
  have hn : ‖iteratedFDeriv ℝ n (fun z => Real.exp (-U (a z))) x‖ ≤
      ‖iteratedFDeriv ℝ n f (a x)‖ * ‖a.contLinear‖ ^ n := by
    change ‖iteratedFDeriv ℝ n (f ∘ a) x‖ ≤ _
    rw [← he]
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (iteratedFDeriv ℝ n f (a x)).norm_compContinuousLinearMap_le
        (fun _ : Fin n => a.contLinear)
  calc
    _ ≤ δ ^ (-r) * (‖iteratedFDeriv ℝ n f (a x)‖ * ‖a.contLinear‖ ^ n) :=
      mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg hδ.le _)
    _ = (δ ^ (-r) * ‖iteratedFDeriv ℝ n f (a x)‖) * ‖a.contLinear‖ ^ n := by ring
    _ ≤ (C * Real.exp (-(p.val.1 / 2) * δ ^ (-p.val.2))) * ‖a.contLinear‖ ^ n :=
      mul_le_mul_of_nonneg_right (hb (a x) hx δ hδ hδ1 hgap hmin) (by positivity)
    _ = _ := by ring

private theorem zero_extension_hasFDerivAt {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Q : Set E} {f : E → F} {x : E} (hx : x ∉ Q)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ y ∈ Q, ‖f y‖ ≤ C * ‖y - x‖ ^ 2) :
    HasFDerivAt (Q.indicator f) (0 : E →L[ℝ] F) x := by
  classical
  rw [hasFDerivAt_iff_isLittleO]
  simp only [indicator_of_notMem hx, sub_zero, zero_apply]
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  have hn : ∀ᶠ y in 𝓝 x, ‖y - x‖ < c / (C + 1) := by
    have hh : ContinuousAt (fun y : E => ‖y - x‖) x := by fun_prop
    have ht : (0 : ℝ) < c / (C + 1) := div_pos hc (by linarith)
    exact hh.eventually (p := fun t : ℝ => t < c / (C + 1))
      (gt_mem_nhds (by simpa only [sub_self, norm_zero] using ht))
  filter_upwards [hn] with y hy
  by_cases hyQ : y ∈ Q
  · rw [indicator_of_mem hyQ]
    have hh : C * ‖y - x‖ ≤ c := by
      have hh := (lt_div_iff₀ (show 0 < C + 1 by linarith)).mp hy
      nlinarith [norm_nonneg (y - x)]
    calc
      ‖f y‖ ≤ C * ‖y - x‖ ^ 2 := hb y hyQ
      _ = (C * ‖y - x‖) * ‖y - x‖ := by ring
      _ ≤ c * ‖y - x‖ := mul_le_mul_of_nonneg_right hh (norm_nonneg _)
  · rw [indicator_of_notMem hyQ, norm_zero]
    positivity

private theorem zero_extension_smooth {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Q : Set E} (hQ : IsOpen Q) {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f Q)
    (hb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∉ Q, ∀ y ∈ Q, ‖iteratedFDeriv ℝ n f y‖ ≤ C * ‖y - x‖ ^ 2) :
    ContDiff ℝ ∞ (Q.indicator f) := by
  classical
  have he : ∀ n : ℕ, iteratedFDeriv ℝ n (Q.indicator f) =
      Q.indicator (iteratedFDeriv ℝ n f) := by
    intro n
    induction n with
    | zero =>
      funext x
      ext m
      by_cases hx : x ∈ Q <;> simp [hx, iteratedFDeriv_zero_apply]
    | succ n ih =>
      funext x
      by_cases hx : x ∈ Q
      · have hh : Q.indicator f =ᶠ[𝓝 x] f :=
          Filter.eventuallyEq_of_mem (hQ.mem_nhds hx) fun y hy => indicator_of_mem hy f
        rw [(hh.iteratedFDeriv ℝ (n + 1)).eq_of_nhds, indicator_of_mem hx]
      · obtain ⟨C, hC, hbC⟩ := hb n
        have hd := zero_extension_hasFDerivAt hx hC (hbC x hx)
        rw [iteratedFDeriv_succ_eq_comp_left]
        simp only [Function.comp_apply, ih, hd.fderiv, indicator_of_notMem hx]
        ext m
        rfl
  apply contDiff_of_differentiable_iteratedFDeriv
  intro n _
  rw [he n]
  intro x
  by_cases hx : x ∈ Q
  · have hh : Q.indicator (iteratedFDeriv ℝ n f) =ᶠ[𝓝 x] iteratedFDeriv ℝ n f :=
      Filter.eventuallyEq_of_mem (hQ.mem_nhds hx) fun y hy => indicator_of_mem hy _
    apply DifferentiableAt.congr_of_eventuallyEq _ hh
    exact (hf.contDiffAt (hQ.mem_nhds hx)).differentiableAt_iteratedFDeriv
      (m := n) (by exact_mod_cast (WithTop.coe_lt_top n : (n : ℕ∞) < ⊤))
  · obtain ⟨C, hC, hbC⟩ := hb n
    exact (zero_extension_hasFDerivAt hx hC (hbC x hx)).differentiableAt

set_option backward.isDefEq.respectTransparency false in
/-- The zero extension of the actual physical density is smooth in every
affine mass-hyperplane chart. This proves the collision-face gluing step
of Appendix A, including charts with zero-dimensional
fibres. The only chart hypothesis is its prescribed total mass. -/
theorem physical_affine_density_smooth (p : Parameters) (k : ℕ) (hk : 1 ≤ k)
    (d : ℕ) (a : EuclideanSpace ℝ (Fin d) →ᴬ[ℝ] EuclideanSpace ℝ (Fin (k + 1)))
    (hmass : ∀ x, ∑ i, a x i = (k + 1 : ℝ)) :
    ContDiff ℝ ∞ (fun x => (ProperMarginalChart.density p k (a x)).toReal) := by
  classical
  obtain ⟨U, hU, hv, hbound⟩ := physical_affine_density_tensors p k.succPNat
    (by simp only [Nat.succPNat_coe]; omega)
  let Q : Set (EuclideanSpace ℝ (Fin d)) := {x | ∀ i, 0 < a x i}
  let f := fun x => Real.exp (-U (a x))
  have hQ : IsOpen Q := by
    have heq : Q = ⋂ i, {x | 0 < a x i} := by ext x; simp [Q]
    rw [heq]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
      ((PiLp.continuous_apply 2 (fun _ : Fin (k + 1) => ℝ) i).comp a.continuous)
  have hs (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Q) :
      WithLp.ofLp (a x) ∈ Riesz1.gapSimplex k.succPNat := by
    refine ⟨hx, ?_⟩
    simpa only [Nat.succPNat_coe, Nat.cast_succ] using hmass x
  have hf : ContDiffOn ℝ ∞ f Q :=
    (hU.neg.exp).comp a.contDiff.contDiffOn
      (fun x hx => PhysicalEnergy.simplex_subset_ambient _ _ (hs x hx))
  have he : (fun x => (ProperMarginalChart.density p k (a x)).toReal) = Q.indicator f := by
    funext x
    by_cases hx : x ∈ Q
    · have hxS : a x ∈ AffineSimplex.massSimplex k (k + 1) := ⟨hx, hmass x⟩
      simp only [ProperMarginalChart.density, dite_eq_left hxS, indicator_of_mem hx]
      rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)]
      dsimp only [f]
      rw [hv ⟨a x, ProperMarginalChart.simplex_ambient k hxS⟩]
      congr 1
      ring
    · have hxS : a x ∉ AffineSimplex.massSimplex k (k + 1) := fun h => hx h.1
      simp only [ProperMarginalChart.density, dite_eq_right hxS, ENNReal.toReal_zero,
        indicator_of_notMem hx]
  rw [he]
  apply zero_extension_smooth hQ hf
  intro n
  obtain ⟨C, hC, hb⟩ := hbound d a n 2
  refine ⟨C * ‖a.contLinear‖ ^ 2, by positivity, fun x hx y hy => ?_⟩
  let δ : ℝ := ⨅ i, a y i
  obtain ⟨j, hj⟩ := ElementaryBarriers.exists_iInf_eq_apply (fun i => a y i)
  have hδ : 0 < δ := by rw [show δ = a y j from hj]; exact hy j
  have hδgap (i : Fin (k + 1)) : δ ≤ a y i := ciInf_le (Finite.bddBelow_range _) i
  have hδ1 : δ ≤ 1 := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hδgap i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      hmass y] at hh
    push_cast at hh
    nlinarith [show (0 : ℝ) < k + 1 by positivity]
  have ht := hb y (hs y hy) δ hδ hδ1 hδgap ⟨j, hj.symm⟩
  have hexp : Real.exp (-(p.val.1 / 2) * δ ^ (-p.val.2)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hp := p.property.1
    have hr := Real.rpow_nonneg hδ.le (-p.val.2)
    nlinarith
  have ht' : ‖iteratedFDeriv ℝ n f y‖ ≤ C * δ ^ 2 := by
    have hh := ht.trans (mul_le_of_le_one_right hC hexp)
    rw [Real.rpow_neg hδ.le, Real.rpow_two] at hh
    have hh' : ‖iteratedFDeriv ℝ n f y‖ / δ ^ 2 ≤ C := by
      rw [div_eq_mul_inv, mul_comm]
      exact hh
    exact (div_le_iff₀ (sq_pos_of_pos hδ)).mp hh'
  have hx' : ∃ i, a x i ≤ 0 := by
    change ¬ ∀ i, 0 < a x i at hx
    simpa only [not_forall, not_lt] using hx
  obtain ⟨i, hi⟩ := hx'
  have hdist : δ ≤ ‖a.contLinear‖ * ‖y - x‖ := by
    calc
      δ ≤ a y i - a x i := by linarith [hδgap i]
      _ ≤ |a y i - a x i| := le_abs_self _
      _ = ‖(a y - a x) i‖ := by rfl
      _ ≤ ‖a y - a x‖ := PiLp.norm_apply_le _ _
      _ = ‖a.contLinear (y - x)‖ := by
        have hh : a.contLinear (y - x) = a y - a x := a.contLinear_apply_vsub y x
        rw [hh]
      _ ≤ ‖a.contLinear‖ * ‖y - x‖ := a.contLinear.le_opNorm _
  calc
    _ ≤ C * δ ^ 2 := ht'
    _ ≤ C * (‖a.contLinear‖ * ‖y - x‖) ^ 2 := by gcongr
    _ = _ := by ring

set_option backward.isDefEq.respectTransparency false in
/-- The actual density in every retained-coordinate chart is globally
smooth and compactly supported. This supplies the common bounded support
in Appendix A, for every retained set. -/
theorem physical_chart_density_smooth_compact (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) :
    ContDiff ℝ ∞ (fun q => (ProperMarginalChart.chartDensity p n m σ q).toReal) ∧
      HasCompactSupport (fun q => (ProperMarginalChart.chartDensity p n m σ q).toReal) := by
  classical
  let L : ℝ := ((n + m : ℕ) + 1)
  let a₀ : EuclideanSpace ℝ (Fin (n + m)) →ᴬ[ℝ]
      EuclideanSpace ℝ (Fin (n + m + 1)) :=
    (AffineSimplex.tangentMap (n + m)).toContinuousLinearMap.toContinuousAffineMap +
      ContinuousAffineMap.const ℝ _ (AffineSimplex.chart (n + m) L 0)
  have ha₀ (x : EuclideanSpace ℝ (Fin (n + m))) :
      a₀ x = AffineSimplex.chart (n + m) L x :=
    (AffineSimplex.chart_eq_tangentMap_add (n + m) L x).symm
  let e := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ
  let a := e.toContinuousLinearEquiv.toContinuousLinearMap.toContinuousAffineMap.comp a₀
  have ha (x : EuclideanSpace ℝ (Fin (n + m))) :
      a x = e (AffineSimplex.chart (n + m) L x) := by
    change e (a₀ x) = _
    rw [ha₀]
  have hmass (x : EuclideanSpace ℝ (Fin (n + m))) :
      ∑ i, a x i = (n + m : ℝ) + 1 := by
    rw [ha]
    change (∑ i, AffineSimplex.chart (n + m) L x (σ.symm i)) = _
    rw [σ.symm.sum_comp, AffineSimplex.sum_chart]
    simp only [L, Nat.cast_add]
  have hs := physical_affine_density_smooth p (n + m) (by omega) (n + m) a (by
    intro x
    simpa only [Nat.cast_add] using hmass x)
  have hchart (q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :
      a (RetainedSimplex.join n m q) = RetainedSimplex.chart n m L σ q := by
    rw [ha]
    rfl
  have he : (fun q => (ProperMarginalChart.chartDensity p n m σ q).toReal) =
      fun q => (ProperMarginalChart.density p (n + m)
        (a (RetainedSimplex.join n m q))).toReal := by
    funext q
    rw [hchart]
    by_cases hq : q ∈ RetainedSimplex.domain n m L
    · dsimp only [L] at hq ⊢
      simp only [ProperMarginalChart.chartDensity, indicator_of_mem hq]
    · have hqS : RetainedSimplex.chart n m L σ q ∉
          AffineSimplex.massSimplex (n + m) L :=
        fun h => hq ((RetainedSimplex.chart_mem_simplex n m L σ q).mp h)
      dsimp only [L] at hq hqS ⊢
      simp only [ProperMarginalChart.chartDensity, indicator_of_notMem hq,
        ProperMarginalChart.density, dite_eq_right hqS, ENNReal.toReal_zero]
  refine ⟨?_, ?_⟩
  · rw [he]
    have : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) :=
      Prod.continuousSMul
    have hj : ContDiff ℝ ∞ (RetainedSimplex.join n m) :=
      (RetainedSimplex.join n m).toContinuousLinearEquiv.contDiff
    exact hs.comp hj
  · apply HasCompactSupport.intro
      (RetainedSimplex.isBounded_domain n m L).isCompact_closure
    intro q hq
    have hq' : q ∉ RetainedSimplex.domain n m L := fun h => hq (subset_closure h)
    dsimp only [L] at hq'
    simp only [ProperMarginalChart.chartDensity, indicator_of_notMem hq', ENNReal.toReal_zero]

/-- Common integrable exterior majorants for every order of the actual
physical chart-density tensors, as used in Appendix A.
One compact exterior set works for every retained point and every order. -/
theorem physical_chart_density_derivative_bounds (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin (n + m + 1))) :
    ∃ K : Set (EuclideanSpace ℝ (Fin m)), IsCompact K ∧
      ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        Integrable (K.indicator (fun _ => C)) volume ∧
        ∀ (x : EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin m)),
          ‖iteratedFDeriv ℝ j
            (fun q => (ProperMarginalChart.chartDensity p n m σ q).toReal) (x, z)‖ ≤
              K.indicator (fun _ => C) z := by
  classical
  obtain ⟨hf, hc⟩ := physical_chart_density_smooth_compact p n m hn σ
  let f := fun q => (ProperMarginalChart.chartDensity p n m σ q).toReal
  let K := Prod.snd '' tsupport f
  have hK : IsCompact K := hc.isCompact.image continuous_snd
  refine ⟨K, hK, fun j => ?_⟩
  have hd : Continuous (iteratedFDeriv ℝ j f) := hf.continuous_iteratedFDeriv (by simp)
  obtain ⟨B, hB⟩ := ((hc.iteratedFDeriv j).isCompact_range hd).bddAbove_image
    continuous_norm.continuousOn
  let C := max B 0
  have hC : 0 ≤ C := le_max_right _ _
  refine ⟨C, hC, ?_, fun x z => ?_⟩
  · apply (integrable_indicator_iff hK.measurableSet).mpr
    exact integrableOn_const (μ := volume) (C := C) (hK.measure_lt_top (μ := volume)).ne
  · by_cases hz : z ∈ K
    · rw [indicator_of_mem hz]
      exact (hB ⟨iteratedFDeriv ℝ j f (x, z), ⟨(x, z), rfl⟩, rfl⟩).trans
        (le_max_left _ _)
    · rw [indicator_of_notMem hz]
      have hq : (x, z) ∉ tsupport f := fun h => hz ⟨(x, z), h, rfl⟩
      have ht : iteratedFDeriv ℝ j f (x, z) = 0 :=
        Function.notMem_support.mp (fun h => hq (support_iteratedFDeriv_subset (𝕜 := ℝ) j h))
      change ‖iteratedFDeriv ℝ j f (x, z)‖ ≤ 0
      rw [ht, norm_zero]

end Riesz2.MarginalHessian
