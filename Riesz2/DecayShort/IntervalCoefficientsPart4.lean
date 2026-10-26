/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.IntervalCoefficientsPart3
public import Riesz2.DecayShort.PhysicalFibresPart3

/-!
# Conditional exterior energy and the complete coefficient moment bounds

See Subsection 4.5 of the paper, using the physical supported fibre and the retained marginal for both active tilts.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology ProbabilityTheory
namespace Riesz2.DecayShort.PhysicalFibres

set_option backward.isDefEq.respectTransparency false in
/-- Internal realization independence for Subsection 4.5: the
second derivative of any representative of the energy is its interval matrix on the open ambient domain. -/
theorem internal_second_eq_intervalMatrix (p : Parameters) (N : ℕ+)
    (W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ)
    (hv : ∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
      W y.val = physicalAmbientGapEnergy p N y)
    (y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N})
    (i j : Fin (N : ℕ)) :
    fderiv ℝ (fderiv ℝ W) y.val (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      IntervalBoundary.intervalMatrix N (N : ℕ) le_rfl (fun t => intervalWeight p N t y) i j := by
  classical
  obtain ⟨U, _, hu, hj⟩ := PhysicalEnergy.ambient_derivatives p N
  have he : W =ᶠ[𝓝 y.val] U := by
    filter_upwards [(PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds y.property] with z hz
    exact (hv ⟨z,hz⟩).trans (hu ⟨z,hz⟩).symm
  rw [he.fderiv.fderiv_eq, (hj y _ _).2]
  have hg (a b : Fin (N : ℕ)) (r : ℕ) (hr : r ≤ (N : ℕ)) :
      cyclicGapSum N a r (WithLp.ofLp (EuclideanSpace.single b (1 : ℝ))) =
        if b ∈ cyclicIndexInterval N a r then 1 else 0 := by
    convert cyclicGapSum_single N a b hr using 1
    congr 1
    ext k
    simp [EuclideanSpace.single, PiLp.single_apply, eq_comm]
  unfold IntervalBoundary.intervalMatrix
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro r _
  rw [hg a i _ (Nat.le_trans (Nat.succ_le_of_lt r.isLt) (Nat.div_le_self _ _)),
    hg a j _ (Nat.le_trans (Nat.succ_le_of_lt r.isLt) (Nat.div_le_self _ _))]
  dsimp only [intervalWeight, IntervalBoundary.rankOne, IntervalBoundary.trace]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.castLE_refl]
  by_cases hi : i ∈ cyclicIndexInterval N a (r.val + 1) <;>
    by_cases hj : j ∈ cyclicIndexInterval N a (r.val + 1) <;> simp [hi, hj]

/-- Internal image-series formula for the existing physical interval matrix.
Used only at points of the ambient domain. -/
theorem internal_intervalMatrix_images (p : Parameters) (N : ℕ+)
    (y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N})
    (i j : Fin (N : ℕ)) :
    IntervalBoundary.intervalMatrix N (N : ℕ) le_rfl (fun t => intervalWeight p N t y) i j =
      ∑ r : Fin ((N : ℕ) / 2), ∑ a : Fin (N : ℕ),
        if i ∈ cyclicIndexInterval N a (r.val + 1) ∧
          j ∈ cyclicIndexInterval N a (r.val + 1) then
          (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
            (p.val.2 * (p.val.2 + 1) * ∑' k : ℤ,
              |PhysicalEnergy.intervalLinear N a (r.val + 1) y.val + k * (N : ℝ)| ^ (-p.val.2 - 2))
        else 0 := by
  classical
  rw [IntervalBoundary.intervalMatrix, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro a _
  rw [intervalWeight_images]
  dsimp only [IntervalBoundary.rankOne, IntervalBoundary.trace]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.castLE_refl]
  split_ifs <;> simp_all

/-- See Subsection 4.5 of the paper: the nonnegative exterior gradient energy on
its entire physical retained carrier. The interval matrix is identified
with the actual second derivative by `internal_second_eq_intervalMatrix`. -/
def exteriorGradientEnergy (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (i : Fin n) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (∑ a : Fin (n + m + 1), if n ≤ a.val then
    ((configuration n m (Equiv.refl _) x z).val a) ^ (p.val.2 + 2) *
      (IntervalBoundary.intervalMatrix (n + m).succPNat (n + m + 1) le_rfl
        (fun t => intervalWeight p (n + m).succPNat t
          (configuration n m (Equiv.refl _) x z)) (Fin.castLE (by omega) i) a) ^ 2 else 0)
    ∂measure p n m hn (Equiv.refl _) x

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 4.5 of the paper: every-point finiteness and the ordinary integral
realization of Subsection 4.5. This also identifies its integrand with the actual
weighted square Hessian, before taking any conditional mean. -/
theorem exteriorGradientEnergy_finite (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (W : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ)
    (hv : ∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
        y ∈ gapAmbientDomain (n + m).succPNat},
      W y.val = physicalAmbientGapEnergy p (n + m).succPNat y)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (i : Fin n) :
    let V := fun z => ∑ a : Fin (n + m + 1), if n ≤ a.val then
      ((configuration n m (Equiv.refl _) x z).val a) ^ (p.val.2 + 2) *
        (fderiv ℝ (fderiv ℝ W) (configuration n m (Equiv.refl _) x z).val
          (EuclideanSpace.single (Fin.castLE (by omega) i) 1) (EuclideanSpace.single a 1)) ^ 2 else 0
    Integrable V (measure p n m hn (Equiv.refl _) x) ∧
      exteriorGradientEnergy p n m hn x i < ⊤ ∧
      ENNReal.ofReal (∫ z, V z ∂measure p n m hn (Equiv.refl _) x) =
        exteriorGradientEnergy p n m hn x i ∧
      (exteriorGradientEnergy p n m hn x i).toReal =
        ∫ z, V z ∂measure p n m hn (Equiv.refl _) x := by
  intro V
  obtain ⟨U, _, hu, hf⟩ := exterior_gradient_energy_finite p n m hn
  have he : V = fun z => ∑ a : Fin (n + m + 1), if n ≤ a.val then
      ((configuration n m (Equiv.refl _) x z).val a) ^ (p.val.2 + 2) *
        (fderiv ℝ (fderiv ℝ U) (configuration n m (Equiv.refl _) x z).val
          (EuclideanSpace.single (Fin.castLE (by omega) i) 1) (EuclideanSpace.single a 1)) ^ 2 else 0 := by
    funext z
    apply Finset.sum_congr rfl
    intro a _
    dsimp only [V]
    split_ifs
    · have heq : W =ᶠ[𝓝 (configuration n m (Equiv.refl _) x z).val] U := by
        filter_upwards [(PhysicalEnergy.isOpen_gapAmbientDomain _).mem_nhds
          (configuration n m (Equiv.refl _) x z).property] with y hy
        exact (hv ⟨y,hy⟩).trans (hu ⟨y,hy⟩).symm
      rw [heq.fderiv.fderiv_eq]
    · rfl
  have hI : Integrable V (measure p n m hn (Equiv.refl _) x) := he ▸ (hf x i).1
  have hnn : ∀ z, 0 ≤ V z := by
    intro z
    apply Finset.sum_nonneg
    intro a _
    split_ifs
    · exact mul_nonneg (Real.rpow_nonneg
        ((configuration_mem_simplex n m (Equiv.refl _) x z).1 a).le _) (sq_nonneg _)
    · exact le_rfl
  have heV : (∫⁻ z, ENNReal.ofReal (V z) ∂measure p n m hn (Equiv.refl _) x) =
      exteriorGradientEnergy p n m hn x i := by
    unfold exteriorGradientEnergy
    apply lintegral_congr
    intro z
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    dsimp only [V]
    split_ifs
    · have hj := internal_second_eq_intervalMatrix p (n + m).succPNat W hv
        (configuration n m (Equiv.refl _) x z)
        (Fin.castLE (by simp only [Nat.succPNat_coe]; omega) i) a
      simp only [Nat.succPNat_coe] at hj
      rw [hj]
      rfl
    · rfl
  have hreal := (ofReal_integral_eq_lintegral_ofReal hI (ae_of_all _ hnn)).trans heV
  refine ⟨hI, ?_, hreal, ?_⟩
  · rw [← hreal]
    exact ENNReal.ofReal_lt_top
  · rw [← hreal, ENNReal.toReal_ofReal (integral_nonneg hnn)]

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 4.4 and Subsection 4.5 of the paper: the two finite contractions of
the actual conditional interval matrix are exactly the paper's bilinear
uniform-exterior-direction integrals. Integrability holds at every point. -/
theorem physical_exterior_contractions (p : Parameters) (n m : ℕ) (hn : 1 ≤ n) :
    ∃ W : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain (n + m).succPNat) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
          y ∈ gapAmbientDomain (n + m).succPNat},
        W y.val = physicalAmbientGapEnergy p (n + m).succPNat y) ∧
      ∀ x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
        let S := Finset.univ.filter (fun a : Fin (n + m + 1) => n ≤ a.val)
        let M : ℝ := m + 1
        let q := WithLp.toLp 2 (Fin.append (fun _ : Fin n => (0 : ℝ))
          (fun _ : Fin (m + 1) => M⁻¹))
        let H := IntervalBoundary.intervalMatrix (n + m).succPNat (n + m + 1) le_rfl
          (conditionalIntervalWeight p n m hn (Equiv.refl _) x)
        let B := fun z => fderiv ℝ (fderiv ℝ W) (configuration n m (Equiv.refl _) x z).val
        (∀ i : Fin n,
          Integrable (fun z => B z (EuclideanSpace.single (Fin.castLE (by omega) i) 1) q)
            (measure p n m hn (Equiv.refl _) x) ∧
          (∫ z, B z (EuclideanSpace.single (Fin.castLE (by omega) i) 1) q
            ∂measure p n m hn (Equiv.refl _) x) = M⁻¹ * ∑ a ∈ S, H (Fin.castLE (by omega) i) a) ∧
        Integrable (fun z => B z q q) (measure p n m hn (Equiv.refl _) x) ∧
        (∫ z, B z q q ∂measure p n m hn (Equiv.refl _) x) =
          M⁻¹ ^ 2 * ∑ a ∈ S, ∑ b ∈ S, H a b := by
  classical
  obtain ⟨W, hW, hv, hentries⟩ := ambient_hessian_conditional_entries p n m hn
  refine ⟨W, hW, hv, ?_⟩
  intro x S M q H B
  have hq : q = M⁻¹ • ∑ a ∈ S, EuclideanSpace.single a 1 := by
    ext k
    simp only [PiLp.smul_apply, WithLp.ofLp_sum, Finset.sum_apply,
      EuclideanSpace.single, PiLp.single_apply, smul_eq_mul]
    refine Fin.addCases (m := n) (n := m + 1) (fun j => ?_) (fun j => ?_) k
    · simp [q, S, Fin.append, Fin.addCases_left, j.isLt]
    · simp [q, S, Fin.append, Fin.addCases_right, Fin.val_natAdd]
  have hb (z) (i : Fin n) :
      B z (EuclideanSpace.single (Fin.castLE (by omega) i) 1) q =
        M⁻¹ * ∑ a ∈ S, B z (EuclideanSpace.single (Fin.castLE (by omega) i) 1)
          (EuclideanSpace.single a 1) := by
    rw [hq]
    simp only [map_smul, map_sum, smul_eq_mul]
  have hc (z) : B z q q = M⁻¹ ^ 2 * ∑ a ∈ S, ∑ b ∈ S,
      B z (EuclideanSpace.single a 1) (EuclideanSpace.single b 1) := by
    rw [hq]
    simp only [map_smul, map_sum, sum_apply,
      smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hi (a b) : Integrable (fun z => B z (EuclideanSpace.single a 1)
      (EuclideanSpace.single b 1)) (measure p n m hn (Equiv.refl _) x) :=
    (hentries x a b).1
  have he (a b) : (∫ z, B z (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)
      ∂measure p n m hn (Equiv.refl _) x) = H a b := (hentries x a b).2
  constructor
  · intro i
    simp_rw [hb]
    refine ⟨(integrable_finsetSum S (fun a _ => hi _ a)).const_mul _, ?_⟩
    rw [integral_const_mul, integral_finsetSum S (fun a _ => hi _ a)]
    simp only [he]
  · simp_rw [hc]
    have hrow (a) := integrable_finsetSum S (fun b _ => hi a b)
    refine ⟨(integrable_finsetSum S (fun a _ => hrow a)).const_mul _, ?_⟩
    rw [integral_const_mul, integral_finsetSum S (fun a _ => hrow a)]
    simp_rw [integral_finsetSum S (fun b _ => hi _ b), he]

end Riesz2.DecayShort.PhysicalFibres

namespace Riesz2.DecayShort

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 4.5 of the paper: conditional exterior energy moments, with the
sharp boundary profile, compact-temperature uniformity, and degree depending
only on the Riesz exponent. The energy is finite at every retained point. -/
theorem activeTilt_conditional_exterior_energy_moments (s βlo βhi h Cθ : ℝ) (hs : 1 < s)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (hh : 0 < h) (hCθ : 1 ≤ Cθ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (n : ℕ+) (m : ℕ)
      (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ (ι : Bool) (i : Fin (n : ℕ)) (q : ℝ), 1 ≤ q →
        Measurable (fun x => (PhysicalFibres.exteriorGradientEnergy p n m n.pos x i).toReal) ∧
        eLpNorm (fun x => (PhysicalFibres.exteriorGradientEnergy p n m n.pos x i).toReal)
          (ENNReal.ofReal q)
          ((activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ h ι).comap
            ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
              EuclideanSpace ℝ (Fin (n : ℕ)))) ≤
            ENNReal.ofReal (C * q ^ ((s + 2) + 2 * ((s + 2) / s)) *
              (min (i.val + 1) ((n : ℕ) - i.val) : ℕ) ^ (1 - 2 * s)) := by
  classical
  obtain ⟨C, hC, hb⟩ := activeTilt_particle_exterior_energy_moments s βlo βhi h Cθ
    hs hlo hle hh hCθ
  refine ⟨C, hC, ?_⟩
  intro p hp hpl hph n m hn θ hcurv ι i q hq
  let N := ((n : ℕ) + m).succPNat
  let μ := (activeTiltedGapLaw p N n hn θ h ι).comap
    ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
  let K := ProperMarginalChart.conditionalKernel p n m n.pos (Equiv.refl _)
  let T := RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _)
  let A := fun (a : Fin (N : ℕ)) (r : Fin ((N : ℕ) / 2))
      (w : EuclideanSpace ℝ (Fin (n : ℕ)) × EuclideanSpace ℝ (Fin m)) =>
    (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
      (p.val.2 * (p.val.2 + 1) * ∑' k : ℤ,
        |PhysicalEnergy.intervalLinear N a (r.val + 1) (T w) + k * (N : ℝ)| ^ (-p.val.2 - 2))
  let H := fun (a b : Fin (N : ℕ)) w => ∑ r : Fin ((N : ℕ) / 2), ∑ c : Fin (N : ℕ),
    if a ∈ cyclicIndexInterval N c (r.val + 1) ∧ b ∈ cyclicIndexInterval N c (r.val + 1)
    then A c r w else 0
  let f := fun w => ∑ a : Fin (N : ℕ), if (n : ℕ) ≤ a.val then
    (T w a) ^ (p.val.2 + 2) * (H (Fin.castLE hn i) a w) ^ 2 else 0
  have hA (a r) : Measurable (A a r) := by
    apply Measurable.const_mul
    apply Measurable.const_mul
    apply Measurable.tsum
    intro k
    exact (((PhysicalEnergy.intervalLinear N a (r.val + 1)).continuous.measurable.comp
      (RetainedSimplex.continuous_chart n m _ (Equiv.refl _)).measurable).add_const _).abs.pow_const _
  have hH (a b) : Measurable (H a b) := by
    apply Finset.measurable_sum
    intro r _
    apply Finset.measurable_sum
    intro c _
    split_ifs
    · exact hA c r
    · exact measurable_const
  have hf : Measurable f := by
    apply Finset.measurable_sum
    intro a _
    split_ifs
    · have ht : Measurable (fun w => T w a) :=
        ((EuclideanSpace.proj (𝕜 := ℝ) a).continuous.comp
          (RetainedSimplex.continuous_chart n m _ (Equiv.refl _))).measurable
      exact (ht.pow_const _).mul ((hH _ _).pow_const 2)
    · exact measurable_const
  let inc := fun w : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) ×
    EuclideanSpace ℝ (Fin m) => (w.1.val, w.2)
  have hi : Measurable inc :=
    (measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd
  let : IsProbabilityMeasure μ := activeTilt_proper_probability p n m hn θ h ι
  have hJ := activeTilt_proper_disintegration p n m hn θ h ι
  change _ = (μ ⊗ₘ K).map inc at hJ
  have hc : Measurable (fun X : Riesz1.Configuration N =>
      RetainedSimplex.coordinates n m (Equiv.refl _) (WithLp.toLp 2 (gapVector X))) :=
    (RetainedSimplex.continuous_coordinates n m (Equiv.refl _)).measurable.comp
      ((PiLp.volume_preserving_toLp _).measurable.comp (Riesz1.measurable_gapVector _))
  have hparticle (a b : Fin (N : ℕ)) (X : Riesz1.Configuration N) :
      H a b (RetainedSimplex.coordinates n m (Equiv.refl _) (WithLp.toLp 2 (gapVector X))) =
        GoodBlocks.particleHessian p N a b X := by
    unfold H GoodBlocks.particleHessian
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro c _
    split_ifs
    · dsimp only [A, T]
      rw [GoodBlocks.retained_chart_gapVector, PhysicalEnergy.intervalLinear_apply,
        GapChart.cyclicGapSum_gapVector, GoodBlocks.particleCoefficient_images]
    · rfl
  have hnorm : eLpNorm (f ∘ inc) (ENNReal.ofReal q) (μ ⊗ₘ K) =
      eLpNorm (fun X => ∑ a : Fin (N : ℕ), if (n : ℕ) ≤ a.val then
        gap X a.val ^ (s + 2) * (GoodBlocks.particleHessian p N (Fin.castLE hn i) a X) ^ 2 else 0)
        (ENNReal.ofReal q) (tiltedParticleMeasure p N n hn θ h ι) := by
    rw [← eLpNorm_map_measure hf.aestronglyMeasurable hi.aemeasurable, ← hJ,
      eLpNorm_map_measure hf.aestronglyMeasurable hc.aemeasurable]
    apply eLpNorm_congr_ae
    apply ae_of_all
    intro X
    dsimp only [Function.comp_def, f, T]
    rw [GoodBlocks.retained_chart_gapVector]
    simp only [hparticle, hp]
    rfl
  have hj := eLpNorm_integral_kernel_le μ K (hf.comp hi) hq
  have he : (fun x => ∫ z, (f ∘ inc) (x,z) ∂K x) =
      fun x => (PhysicalFibres.exteriorGradientEnergy p n m n.pos x i).toReal := by
    funext x
    rw [show K x = _ from ProperMarginalChart.conditionalKernel_apply p n m n.pos (Equiv.refl _) x,
      ← PhysicalFibres.map_measure p n m n.pos (Equiv.refl _) x,
      (MeasurableEmbedding.subtype_coe (AffineSimplex.isOpen_chartDomain _ _).measurableSet).integral_map]
    obtain ⟨W, _, hv, _⟩ := PhysicalEnergy.ambient_derivatives p N
    have hvf := PhysicalFibres.exteriorGradientEnergy_finite p n m n.pos W hv x i
    apply Eq.trans _ hvf.2.2.2.symm
    apply integral_congr_ae
    apply ae_of_all
    intro z
    apply Finset.sum_congr rfl
    intro a _
    dsimp only [Function.comp_def, f, inc, T]
    split_ifs
    · have hjj := PhysicalFibres.internal_second_eq_intervalMatrix p N W hv
        (PhysicalFibres.configuration n m (Equiv.refl _) x z) (Fin.castLE hn i) a
      have himg := PhysicalFibres.internal_intervalMatrix_images p N
        (PhysicalFibres.configuration n m (Equiv.refl _) x z) (Fin.castLE hn i) a
      exact congrArg (fun v : ℝ =>
        ((PhysicalFibres.configuration n m (Equiv.refl _) x z).val a) ^ (p.val.2 + 2) * v ^ 2)
        (hjj.trans himg).symm
    · rfl
  rw [he, hnorm] at hj
  refine ⟨?_, hj.trans (hb p hp hpl hph N n (by change 2 ≤ (n : ℕ) + m + 1; have := n.pos; omega)
    hn θ hcurv ι i q hq)⟩
  rw [← he]
  exact ((hf.comp hi).stronglyMeasurable.integral_kernel_prod_right' (κ := K)).measurable

/-- See Subsection 4.4 of the paper: every entry of the physical conditional interval
matrix is measurable, including entries indexed by exterior labels. -/
theorem measurable_conditional_intervalMatrix (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (k : ℕ) (hk : k ≤ n + m + 1) (i j : Fin k) :
    Measurable (fun x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) =>
      IntervalBoundary.intervalMatrix (n + m).succPNat k hk
        (conditionalIntervalWeight p n m hn (Equiv.refl _) x) i j) := by
  classical
  apply Finset.measurable_sum
  intro t _
  exact (measurable_conditionalIntervalWeight p n m hn (Equiv.refl _) t).mul_const _

/-- Internal bookkeeping for Subsection 4.5: enlarge a positive
prefactor and polynomial degree without changing the spatial profile. -/
theorem internal_moment_bound_enlarge {A C d D q w : ℝ} (hA : 0 ≤ A) (hAC : A ≤ C)
    (hq : 1 ≤ q) (hd : d ≤ D) (hw : 0 ≤ w) :
    ENNReal.ofReal (A * q ^ d * w) ≤ ENNReal.ofReal (C * q ^ D * w) := by
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ hw
  exact mul_le_mul hAC (Real.rpow_le_rpow_of_exponent_le hq hd)
    (Real.rpow_nonneg (by linarith) _) (hA.trans hAC)

/-- Internal finiteness bookkeeping: a measurable function satisfying one of
the finite bounds in Subsection 4.5 belongs to the asserted Lp space. -/
theorem internal_memLp_of_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f : Ω → ℝ} (_hf : Measurable f) {q B : ℝ}
    (hb : eLpNorm f (ENNReal.ofReal q) μ ≤ ENNReal.ofReal B) :
    MemLp f (ENNReal.ofReal q) μ :=
  hb.trans_lt ENNReal.ofReal_lt_top

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 4.5 of the paper, complete interval counting and coefficient moments.
The degree is chosen before every other parameter. The prefactor is uniform
on each compact positive temperature interval, for both active tilts and every
volume. All coefficients use the actual physical conditional law. The Hessian
and bilinear identifications are `conditional_hessian_entries`,
`PhysicalFibres.physical_exterior_contractions` and
`PhysicalFibres.exteriorGradientEnergy_finite`. Every asserted moment is finite,
and the exterior energy is finite at every retained point. -/
theorem interval_counting_coefficient_moments (s : ℝ) (hs : 1 < s) :
    ∃ D : ℝ, 0 < D ∧ ∀ (θ : PhysicalCutoff) (βlo βhi h : ℝ),
      0 < βlo → βlo ≤ βhi → 0 < h →
      ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s →
        βlo ≤ p.val.1 → p.val.1 ≤ βhi →
        (∀ (n : ℕ+) (m : ℕ) (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)),
          2 * (n : ℕ) ≤ (n : ℕ) + m + 1 → ∀ ι : Bool,
          let μ := (activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ h ι).comap
            ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
              EuclideanSpace ℝ (Fin (n : ℕ)))
          let A := fun x => conditionalIntervalWeight p n m n.pos (Equiv.refl _) x
          let P := fun i j x => IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat n hn (A x) i j
          let H := fun x => IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat
            ((n : ℕ) + m + 1) le_rfl (A x)
          let S := Finset.univ.filter (fun a : Fin ((n : ℕ) + m + 1) => (n : ℕ) ≤ a.val)
          let b := fun i x => (m + 1 : ℝ)⁻¹ * ∑ a ∈ S, H x (Fin.castLE hn i) a
          let c := fun x => (m + 1 : ℝ)⁻¹ ^ 2 * ∑ a ∈ S, ∑ b ∈ S, H x a b
          let V := fun i x => (PhysicalFibres.exteriorGradientEnergy p n m n.pos x i).toReal
          (∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) t,
            Integrable (fun z => intervalWeight p ((n : ℕ) + m).succPNat t
              (PhysicalFibres.configuration n m (Equiv.refl _) x z))
              (PhysicalFibres.measure p n m n.pos (Equiv.refl _) x)) ∧
          (∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) i,
            PhysicalFibres.exteriorGradientEnergy p n m n.pos x i < ⊤) ∧
          ∀ q : ℝ, 1 ≤ q →
          (∀ i j : Fin (n : ℕ), MemLp (P i j) (ENNReal.ofReal q) μ ∧
            eLpNorm (P i j) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal
              (C * q ^ D * (1 + (Riesz1.cyclicIndexDistance ((n : ℕ) + m).succPNat
                (Fin.castLE hn i) (Fin.castLE hn j) : ℝ)) ^ (-s))) ∧
          (∀ k : ℕ, 1 ≤ k → k < (n : ℕ) →
            let f := fun x => IntervalBoundary.prefixCoefficient ((n : ℕ) + m).succPNat n hn (A x) k
            let g := fun x => IntervalBoundary.suffixCoefficient ((n : ℕ) + m).succPNat n hn (A x) k
            MemLp f (ENNReal.ofReal q) μ ∧
              eLpNorm f (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (C * q ^ D * (k : ℝ) ^ (-s - 1)) ∧
            MemLp g (ENNReal.ofReal q) μ ∧
              eLpNorm g (ENNReal.ofReal q) μ ≤
                ENNReal.ofReal (C * q ^ D * ((n : ℕ) - k : ℕ) ^ (-s - 1))) ∧
          (let f := fun x => IntervalBoundary.fullCoefficient ((n : ℕ) + m).succPNat n hn (A x);
            MemLp f (ENNReal.ofReal q) μ ∧
              eLpNorm f (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (C * q ^ D * (n : ℝ) ^ (-s))) ∧
          (∀ i : Fin (n : ℕ), MemLp (b i) (ENNReal.ofReal q) μ ∧ MemLp c (ENNReal.ofReal q) μ ∧
            eLpNorm (b i) (ENNReal.ofReal q) μ + eLpNorm c (ENNReal.ofReal q) μ ≤
              ENNReal.ofReal (C * q ^ D / ((n : ℕ) + m + 1 : ℕ)) ∧
            MemLp (V i) (ENNReal.ofReal q) μ ∧
            eLpNorm (V i) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal
              (C * q ^ D * (min (i.val + 1) ((n : ℕ) - i.val) : ℕ) ^ (1 - 2 * s)))) ∧
        (∀ (N : ℕ+), 4 ≤ (N : ℕ) → ∀ (ι : Bool) (q : ℝ), 1 ≤ q →
          ∀ a b : Fin (N : ℕ),
            MemLp (GoodBlocks.particleHessian p N a b) (ENNReal.ofReal q)
              (tiltedParticleMeasure p N N le_rfl θ h ι) ∧
            eLpNorm (GoodBlocks.particleHessian p N a b) (ENNReal.ofReal q)
              (tiltedParticleMeasure p N N le_rfl θ h ι) ≤ ENNReal.ofReal
                (C * q ^ D * (1 + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-s))) := by
  classical
  let d := (s + 2) / s
  let D := (s + 2) + 2 * d
  have hd : 0 < d := div_pos (by linarith) (by linarith)
  have hD : 0 < D := by dsimp [D]; linarith
  have hdd : d ≤ D := by dsimp [D]; linarith
  refine ⟨D, hD, ?_⟩
  intro θ βlo βhi h hlo hle hh
  obtain ⟨Cθ, hCθ, hcurv, _⟩ := θ.property.2.2.2.2
  obtain ⟨C₁, hC₁, hP⟩ := activeTilt_conditional_P_moments s βlo βhi h Cθ hs hlo hle hh hCθ
  obtain ⟨C₂, hC₂, hpq⟩ := activeTilt_boundary_moments s βlo βhi h Cθ hs hlo hle hh hCθ
  obtain ⟨C₃, hC₃, hd₀⟩ := activeTilt_full_boundary_moments s βlo βhi h Cθ hs hlo hle hh hCθ
  obtain ⟨C₄, hC₄, hbc⟩ := activeTilt_exterior_contraction_moments s βlo βhi h Cθ hs hlo hle hh hCθ
  obtain ⟨C₅, hC₅, hV⟩ := activeTilt_conditional_exterior_energy_moments s βlo βhi h Cθ hs hlo hle hh hCθ
  obtain ⟨C₆, hC₆, hfull⟩ := activeTilt_hessian_moments s βlo βhi h Cθ hs hlo hle hh hCθ
  let C := C₁ + C₂ + C₃ + C₄ + C₅ + C₆
  have hC : 0 < C := by dsimp [C]; linarith
  have hc₁ : C₁ ≤ C := by dsimp [C]; linarith
  have hc₂ : C₂ ≤ C := by dsimp [C]; linarith
  have hc₃ : C₃ ≤ C := by dsimp [C]; linarith
  have hc₄ : C₄ ≤ C := by dsimp [C]; linarith
  have hc₅ : C₅ ≤ C := by dsimp [C]; linarith
  have hc₆ : C₆ ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro p hp hpl hph
  constructor
  · intro n m hn hhalf ι μ A P H S b c V
    refine ⟨fun x t => integrable_intervalWeight p n m n.pos (Equiv.refl _) x t, ?_, ?_⟩
    · obtain ⟨W, _, hv, _⟩ := PhysicalEnergy.ambient_derivatives p ((n : ℕ) + m).succPNat
      exact fun x i => (PhysicalFibres.exteriorGradientEnergy_finite p n m n.pos W hv x i).2.1
    · intro q hq
      have hlarge {a e w : ℝ} (ha : 0 ≤ a) (hac : a ≤ C) (he : e ≤ D) (hw : 0 ≤ w) :=
        internal_moment_bound_enlarge ha hac hq he hw
      have hmH (a b : Fin ((n : ℕ) + m + 1)) : Measurable (fun x => H x a b) :=
        measurable_conditional_intervalMatrix p n m n.pos _ le_rfl a b
      have hmb (i : Fin (n : ℕ)) : Measurable (b i) := by
        apply Measurable.const_mul
        exact Finset.measurable_sum _ (fun a _ => hmH _ a)
      have hmc : Measurable c := by
        apply Measurable.const_mul
        exact Finset.measurable_sum _ (fun a _ => Finset.measurable_sum _ (fun b _ => hmH a b))
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i j
        have hb := (hP p hp hpl hph n m hn θ hcurv ι i j q hq).trans
          (hlarge hC₁.le hc₁ hdd (by positivity))
        exact ⟨internal_memLp_of_bound μ
          (measurable_conditional_intervalMatrix p n m n.pos _ hn i j) hb, hb⟩
      · intro k hk hkn f g
        have hb := hpq p hp hpl hph n m hn hhalf θ hcurv ι q hq k hk hkn
        have hf := hb.1.trans (hlarge hC₂.le hc₂ hdd (by positivity))
        have hg := hb.2.trans (hlarge hC₂.le hc₂ hdd (by positivity))
        have hm := measurable_physical_boundary_coefficients p n m n.pos hn
        exact ⟨internal_memLp_of_bound μ (hm.1 k) hf, hf,
          internal_memLp_of_bound μ (hm.2.1 k) hg, hg⟩
      · intro f
        have hb := (hd₀ p hp hpl hph n m hn hhalf θ hcurv ι q hq).trans
          (hlarge hC₃.le hc₃ hdd (by positivity))
        exact ⟨internal_memLp_of_bound μ
          (measurable_physical_boundary_coefficients p n m n.pos hn).2.2 hb, hb⟩
      · intro i
        have hsum := hbc p hp hpl hph n m hn hhalf θ hcurv ι q hq i
        have hsum' : eLpNorm (b i) (ENNReal.ofReal q) μ + eLpNorm c (ENNReal.ofReal q) μ ≤
            ENNReal.ofReal (C * q ^ D / ((n : ℕ) + m + 1 : ℕ)) := by
          apply hsum.trans
          simp only [div_eq_mul_inv]
          exact hlarge hC₄.le hc₄ hdd (by positivity)
        have hvi := hV p hp hpl hph n m hn θ hcurv ι i q hq
        have hvb := hvi.2.trans (hlarge hC₅.le hc₅ le_rfl (by positivity))
        exact ⟨internal_memLp_of_bound μ (hmb i) ((le_self_add).trans hsum'),
          internal_memLp_of_bound μ hmc ((le_add_self).trans hsum'), hsum',
          internal_memLp_of_bound μ hvi.1 hvb, hvb⟩
  · intro N hN ι q hq a b
    have hb := (hfull p hp hpl hph N N (by omega) le_rfl θ hcurv ι a b q hq).trans
      (internal_moment_bound_enlarge hC₆.le hc₆ hq hdd (by positivity))
    exact ⟨internal_memLp_of_bound _ (GoodBlocks.measurable_particleHessian p N a b) hb, hb⟩

end Riesz2.DecayShort
