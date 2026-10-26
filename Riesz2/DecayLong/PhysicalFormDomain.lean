/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.MarginalCollision
public import Riesz2.DecayShort.PhysicalFibresPart2
public import Riesz2.HelfferSjostrand.PhysicalCollisionPart2
public import Riesz2.Frozen.OfLong

/-!
# Physical trace and collision inputs

Analytic inputs to Subsection 5.1. The proper marginal potential uses the
fibre density. The full-cycle potential realizes the ambient extension,
and its Gibbs certificate identifies the full intrinsic tilted law.
Constants here may depend on the fixed volume and parameters.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open InnerProductSpace
open scoped ENNReal ContDiff Topology Laplacian

namespace Riesz2.PhysicalFormDomain

namespace Internal

/-- Internal trace fact used for the physical potentials: a nonnegative
bilinear Hessian has nonnegative Euclidean Laplacian. -/
theorem laplacian_nonneg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (V : E → ℝ) (x : E)
    (h : ∀ u : E, 0 ≤ fderiv ℝ (fderiv ℝ V) x u u) : 0 ≤ Δ V x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis V
    (stdOrthonormalBasis ℝ E)]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact Finset.sum_nonneg fun i _ => h _

end Internal

set_option backward.isDefEq.respectTransparency false in
/-- Analytic inputs for Subsection 5.1, proper case.
The trace is nonnegative and is dominated by any positive multiple of the
squared score, with a fixed finite remainder. The precise ground-state
barrier required by the compact scalar core is also concluded.
The potential is beta times the physical marginal potential, up to its
additive normalizing constant. -/
theorem proper_trace_inputs (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n m : ℕ) (hn : 1 ≤ n) (θ : PhysicalCutoff) (ε : ℝ) :
    let p := ofLong β s
    let Ω := AffineSimplex.chartDomain n ((n + m : ℕ) + 1)
    let V := fun x : EuclideanSpace ℝ (Fin n) =>
      p.val.1 * ∑ i, θ.val ((n : ℝ) ^ (-ε) * x i) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal)
    ContDiffOn ℝ ∞ V Ω ∧
      (∀ x ∈ Ω, 0 ≤ Δ V x) ∧
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧
        ∀ x ∈ Ω, Δ V x ≤ A * ‖gradient V x‖ ^ 2 + C) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ Ω,
        (Metric.infDist x (frontier Ω))⁻¹ ^ 2 - B ≤
          ‖gradient V x‖ ^ 2 / 4 - Δ V x / 2 := by
  intro p Ω V
  have ha : 0 < (n : ℝ) ^ (-ε) := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  obtain ⟨_, _, hsm, ⟨κ, hκ, hcurv⟩, hcoll, B, hB, hbar⟩ :=
    MarginalCollision.proper_marginal_collision_criterion p n m hn
      (Equiv.refl _) θ ha Finset.univ false
  have hΩ : properMarginalDomain ⟨n, by omega⟩ (n + m).succPNat = Ω := by
    ext x
    simp only [properMarginalDomain, Ω, AffineSimplex.chartDomain,
      Nat.succPNat_coe, Nat.cast_succ, PNat.mk_coe]
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero,
    ← sub_eq_add_neg, hΩ] at hsm hcurv hcoll hbar
  refine ⟨hsm, fun x hx => Internal.laplacian_nonneg V x (fun u => ?_), ?_, B, hB, ?_⟩
  · exact (mul_nonneg hκ.le (sq_nonneg ‖u‖)).trans (hcurv x hx u)
  · intro A hA
    obtain ⟨C, hC, hb⟩ := hcoll A 1 hA (by norm_num)
    refine ⟨C, hC, fun x hx => ?_⟩
    have hh := hb x hx
    nlinarith only [hh, sq_nonneg (Metric.infDist x (frontier Ω))⁻¹]
  · intro x hx
    have h := hbar x hx
    change (Metric.infDist x (frontier Ω))⁻¹ ^ 2 - B ≤ _ at h
    linarith only [h]

set_option backward.isDefEq.respectTransparency false in
/-- Analytic inputs for Subsection 5.1, full-cycle case.
The ambient potential realizes `fullPhysicalPotentialValue` on its entire
open carrier. Intrinsic derivatives have nonnegative trace, arbitrarily
small score domination, and the exact scalar-core collision barrier. The
Gibbs law is the full intrinsic tilted law. -/
theorem full_trace_inputs (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (θ : PhysicalCutoff) (ε : ℝ) :
    let p := ofLong β s
    ∃ U : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        U y.val = fullPhysicalPotentialValue p N hN θ ε false y) ∧
      let V := fun z : gapTangentSpace N => U (WithLp.toLp 2 (fun i => 1 + z.val i))
      IsEuclideanGibbsPotential volume (fullIntrinsicTiltedGapLaw p N θ ε false)
        (intrinsicGapDomain N) V ∧
      (∀ z ∈ intrinsicGapDomain N, 0 ≤ Δ V z) ∧
      (∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧
        ∀ z ∈ intrinsicGapDomain N, Δ V z ≤ A * ‖gradient V z‖ ^ 2 + C) ∧
      ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ intrinsicGapDomain N,
        (Metric.infDist z (frontier (intrinsicGapDomain N)))⁻¹ ^ 2 - B ≤
          ‖gradient V z‖ ^ 2 / 4 - Δ V z / 2 := by
  intro p
  obtain ⟨U, hU, hv, hg, κ, hκ, hcurv, hcoll⟩ :=
    PhysicalCollision.fullPhysicalPotential_wellposed N p hN θ ε false
  refine ⟨U, hU, hv, hg, fun z hz => Internal.laplacian_nonneg _ z (fun u => ?_), ?_, ?_⟩
  · exact (mul_nonneg hκ.le (sq_nonneg ‖u‖)).trans (hcurv z hz u)
  · intro A hA
    obtain ⟨C, hC, hb⟩ := hcoll A 1 hA (by norm_num)
    refine ⟨C, hC, fun z hz => ?_⟩
    have hh := hb z hz
    nlinarith only [hh,
      sq_nonneg (Metric.infDist z (frontier (intrinsicGapDomain N)))⁻¹]
  · obtain ⟨B, hB, hb⟩ := hcoll (1 / 2) 2 (by norm_num) (by norm_num)
    refine ⟨B / 2, div_nonneg hB (by norm_num), fun z hz => ?_⟩
    have hh := hb z hz
    linarith only [hh]

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 5.1 of the paper: the
smooth negative-log fibre potential is a Gibbs potential for the literal
active tilted gap law. Its positive finite normalization is concluded,
rather than supplied as a physical hypothesis. -/
theorem proper_gibbs_potential (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε : ℝ) :
    let p := ofLong β s
    let hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ) := by simp; omega
    let Ω := AffineSimplex.chartDomain n ((n + m : ℕ) + 1)
    let V := fun x : EuclideanSpace ℝ (Fin n) =>
      p.val.1 * ∑ i, θ.val ((n : ℝ) ^ (-ε) * x i) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal)
    IsEuclideanGibbsPotential volume (activeTiltedGapLaw p ((n : ℕ) + m).succPNat
      n hn θ ε false) Ω V := by
  classical
  intro p hn Ω V
  let D := ProperMarginalChart.penalizedChartDensity p n m (Equiv.refl _) θ
    ((n : ℝ) ^ (-ε)) (Finset.univ.map (Fin.castLEEmb hn)) false
  let w := AffineFibre.fibreMass volume D
  have ha : 0 < (n : ℝ) ^ (-ε) := Real.rpow_pos_of_pos (by exact_mod_cast n.pos) _
  have hsm : ContDiffOn ℝ ∞ V Ω := by
    simpa only [Bool.false_eq_true, ↓reduceIte, add_zero] using
      MarginalHessian.physical_penalized_marginal_potential_smooth p n m n.pos
        (Equiv.refl _) θ ha Finset.univ false
  obtain ⟨_, _, hprob, hρ⟩ :=
    ProperMarginalChart.activeTiltedGapLaw_density_valid p n m hn θ ε false
  have hd : w = Ω.indicator (fun x => ENNReal.ofReal (Real.exp (-V x))) := by
    funext x
    by_cases hx : x ∈ Ω
    · obtain ⟨h0, ht, he⟩ := DecayShort.PhysicalFibres.active_marginal_potential_density
        p n m hn θ ε false hx
      have hscale : ((n : ℝ) ^ ε)⁻¹ = (n : ℝ) ^ (-ε) :=
        (Real.rpow_neg (by exact_mod_cast n.pos.le) ε).symm
      have hv : V x = -Real.log (w x).toReal := by
        apply mul_left_cancel₀ (inv_ne_zero p.property.1.ne')
        simpa only [V, D, w, Bool.false_eq_true, ↓reduceIte, add_zero, hscale, neg_mul, mul_neg] using he
      rw [indicator_of_mem hx, hv, neg_neg,
        Real.exp_log (ENNReal.toReal_pos h0 ht), ENNReal.ofReal_toReal ht]
    · have hzero (z : EuclideanSpace ℝ (Fin m)) : D (x,z) = 0 := by
        have hq : (x,z) ∉ RetainedSimplex.domain n m ((n + m : ℕ) + 1) := by
          intro hh
          apply hx
          change x ∈ AffineSimplex.chartDomain n ((n + m : ℕ) + 1)
          rw [← RetainedSimplex.fst_image_domain n m ((n + m : ℕ) + 1)]
          exact ⟨(x,z), hh, rfl⟩
        exact indicator_of_notMem hq _
      rw [indicator_of_notMem hx]
      change (∫⁻ z : EuclideanSpace ℝ (Fin m), D (x,z)) = 0
      simp only [hzero, lintegral_zero]
  let q := (tiltNormalizer p ((n : ℕ) + m).succPNat n hn θ ε false)⁻¹ *
    (partitionFunction p ((n : ℕ) + m).succPNat)⁻¹ *
      ENNReal.ofReal ((n + m + 1 : ℝ) ^ ((n : ℕ) + m))⁻¹
  let Z := ∫⁻ x in Ω, ENNReal.ofReal (Real.exp (-V x))
  have hden : activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ ε false =
      q • (volume.restrict Ω).withDensity (fun x => ENNReal.ofReal (Real.exp (-V x))) := by
    rw [hρ]
    change _ = q • _
    rw [← withDensity_indicator (μ := volume) (AffineSimplex.isOpen_chartDomain _ _).measurableSet]
    rw [← hd]
    simp only [q, D, w, smul_smul, mul_assoc]
  have hnorm : q * Z = 1 := by
    have hmass := hprob.measure_univ
    rw [hden, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ] at hmass
    exact hmass
  have hZ0 : Z ≠ 0 := right_ne_zero_of_mul_eq_one hnorm
  have hq0 : q ≠ 0 := left_ne_zero_of_mul_eq_one hnorm
  have hZt : Z ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top hq0] at hnorm
    exact ENNReal.top_ne_one hnorm
  refine ⟨hsm, pos_iff_ne_zero.mpr hZ0, lt_top_iff_ne_top.mpr hZt, ?_⟩
  rw [hden, ENNReal.eq_inv_of_mul_eq_one_left hnorm]

end Riesz2.PhysicalFormDomain
