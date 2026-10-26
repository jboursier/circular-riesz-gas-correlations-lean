/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.AdmissibleParticlePairs
public import Riesz2.Frozen.PairGibbsMeasure
public import Riesz2.Frozen.PairAmbientGapPotential
public import Riesz2.Frozen.IntrinsicGapDomain
public import Riesz2.Frozen.CenteredGapChart
public import Riesz2.ToMathlib.AffineSimplexCharts
public import Riesz2.ToMathlib.FiniteMatrixOrder
public import Riesz1.HelfferSjostrand.GeometryRelabelAdmissible
public import Riesz1.HelfferSjostrand.GeometryLawBijection
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Hessian normalization and the affine gap metric

The normalization and Hessian identity of Subsection 3.1, the geometry
and rotation identities of Subsection 3.2, and the particle metric used in
Lemma A.1. Pair data are indexed by upper-triangular pairs. Their symmetric
incidence sum adapts them to the companion library.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Finset
open scoped ENNReal Topology RealInnerProductSpace

namespace Riesz2

namespace AffineMetric

variable {N : ℕ+}

/-- The symmetric incidence sum of the unordered pair family. This supplies the
redundant label slots in the library API. Its diagonal is the empty incidence sum. -/
def symmetricPairFamily (χ : ParticlePairData N) (i j : Fin (N : ℕ)) (r : ℝ) : ℝ :=
  ∑ p : {p : Fin (N : ℕ) × Fin (N : ℕ) // p.1 < p.2}
    with p.val = (i, j) ∨ p.val = (j, i), χ p r

theorem symmetricPairFamily_apply (χ : ParticlePairData N)
    {i j : Fin (N : ℕ)} (hij : i < j) :
    symmetricPairFamily χ i j = χ ⟨(i, j), hij⟩ := by
  funext r
  unfold symmetricPairFamily
  classical
  refine Finset.sum_eq_single (f := fun p => χ p r) ⟨(i, j), hij⟩ ?_ ?_
  · intro p hp hne
    rcases (Finset.mem_filter.mp hp).2 with hp | hp
    · exact False.elim (hne (Subtype.ext hp))
    · have hlt := p.property
      rw [hp] at hlt
      exact False.elim (not_lt_of_ge hij.le hlt)
  · intro h
    exact False.elim (h (by simp))

/-- Repackage the same pair functions in the Riesz 1 interface. -/
def libraryPairs {hN : 2 ≤ (N : ℕ)} {χ : ParticlePairData N} {c : ℝ}
    (h : AdmissibleParticlePairs hN χ c) : Riesz1.HsPairPotentials N c where
  potential := symmetricPairFamily χ
  symmetric i j := by
    funext r
    unfold symmetricPairFamily
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, or_comm]
  smooth i j hij := by rw [symmetricPairFamily_apply χ hij]; exact (h.1 _).1
  curvature i j hij := by rw [symmetricPairFamily_apply χ hij]; exact (h.1 _).2.1
  leftBoundary i j hij := by rw [symmetricPairFamily_apply χ hij]; exact (h.1 _).2.2.1
  rightBoundary i j hij := by rw [symmetricPairFamily_apply χ hij]; exact (h.1 _).2.2.2

/-- Reindex a sum over unordered pairs as the library's triangular double sum. -/
theorem sum_pairs {M : Type*} [AddCommMonoid M]
    (f : {p : Fin (N : ℕ) × Fin (N : ℕ) // p.1 < p.2} → M) :
    ∑ p, f p = ∑ i, ∑ j : {j : Fin (N : ℕ) // i < j}, f ⟨(i, j.val), j.property⟩ := by
  calc
    ∑ p, f p = ∑ q : (i : Fin (N : ℕ)) × {j : Fin (N : ℕ) // i < j},
        f ⟨(q.1, q.2.val), q.2.property⟩ :=
      Fintype.sum_equiv (Equiv.subtypeProdEquivSigmaSubtype
        (fun i j : Fin (N : ℕ) => i < j)) _ _ (fun _ => rfl)
    _ = _ := Fintype.sum_sigma _

theorem libraryPairs_energy {hN : 2 ≤ (N : ℕ)} {χ : ParticlePairData N} {c : ℝ}
    (h : AdmissibleParticlePairs hN χ c) :
    Riesz1.hsPairExpression (libraryPairs h) = particlePairEnergy χ := by
  funext x
  unfold Riesz1.hsPairExpression particlePairEnergy
  congr 1
  rw [sum_pairs]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_subtype (univ.filter (i < ·)) (p := fun j => i < j) (by simp)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [libraryPairs, symmetricPairFamily_apply χ j.property]

theorem pair_normalizer_eq_library {hN : 2 ≤ (N : ℕ)} {χ : ParticlePairData N} {c : ℝ}
    (h : AdmissibleParticlePairs hN χ c) :
    pairGibbsNormalizer χ = Riesz1.hsPartitionFunction (libraryPairs h) := by
  rw [Riesz1.hsPartitionFunction_eq_lintegral]
  simp only [pairGibbsNormalizer, Riesz1.hsFundamentalHamiltonian, libraryPairs_energy]

theorem sum_pairs_eval {M : Type*} [AddCommMonoid M]
    (f : Fin (N : ℕ) → Fin (N : ℕ) → M) :
    (∑ p : {p : Fin (N : ℕ) × Fin (N : ℕ) // p.1 < p.2}, f p.val.1 p.val.2) =
      ∑ i, ∑ j ∈ univ.filter (i < ·), f i j := by
  rw [sum_pairs]
  apply Finset.sum_congr rfl
  intro i _
  exact (Finset.sum_subtype (univ.filter (i < ·))
    (p := fun j => i < j) (by simp) (f i)).symm

/-- The tangent space is exactly the library's orthogonal complement. -/
theorem gapTangentSpace_eq_orth (N : ℕ+) :
    gapTangentSpace N = Riesz1.hsOrthSubspace N := by
  ext z
  constructor
  · intro hz
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    change inner ℝ ((Real.sqrt (N : ℕ))⁻¹ • Riesz1.hsRotationVector N) z = 0
    rw [inner_smul_left]
    simp [Riesz1.hsRotationVector, PiLp.inner_apply, show ∑ i, z i = 0 from hz]
  · exact Riesz1.sum_coord_eq_zero_of_mem_orth z

end AffineMetric

open AffineMetric

variable {N : ℕ+}

/-- See Subsection 3.1 of the paper: the bilinear Hessian identity, in the pair convention. -/
theorem particlePairEnergy_hessian {hN : 2 ≤ (N : ℕ)} {χ : ParticlePairData N} {c : ℝ}
    (h : AdmissibleParticlePairs hN χ c) {x : EuclideanSpace ℝ (Fin (N : ℕ))}
    (hx : x ∈ particleChamber N) (u v : EuclideanSpace ℝ (Fin (N : ℕ))) :
    fderiv ℝ (fderiv ℝ (particlePairEnergy χ)) x u v =
      2 * ∑ p : {p : Fin (N : ℕ) × Fin (N : ℕ) // p.1 < p.2},
        deriv (deriv (χ p)) (x p.val.2 - x p.val.1) *
          ((u p.val.2 - u p.val.1) * (v p.val.2 - v p.val.1)) := by
  rw [← libraryPairs_energy h, Riesz1.hessian_hsPairExpression_apply (libraryPairs h) hx]
  congr 1
  rw [sum_pairs]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_subtype (univ.filter (i < ·)) (p := fun j => i < j) (by simp)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [libraryPairs, symmetricPairFamily_apply χ j.property]

/-- See Subsection 3.1 of the paper: positivity of the particle Hessian on the entire lift space. -/
theorem particlePairEnergy_hessian_nonneg {hN : 2 ≤ (N : ℕ)} {χ : ParticlePairData N}
    {c : ℝ} (hc : 0 < c) (h : AdmissibleParticlePairs hN χ c)
    {x : EuclideanSpace ℝ (Fin (N : ℕ))} (hx : x ∈ particleChamber N)
    (u : EuclideanSpace ℝ (Fin (N : ℕ))) :
    0 ≤ fderiv ℝ (fderiv ℝ (particlePairEnergy χ)) x u u := by
  rw [particlePairEnergy_hessian h hx]
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro p _
  exact mul_nonneg (hc.le.trans ((h.1 p).2.1 _
    (Riesz1.hsChamber_separation_mem hx p.property))) (mul_self_nonneg _)

/-- See Subsection 3.1 of the paper: the trace of the particle Hessian is nonnegative. -/
theorem particlePairEnergy_laplacian_nonneg {hN : 2 ≤ (N : ℕ)} {χ : ParticlePairData N}
    {c : ℝ} (hc : 0 < c) (h : AdmissibleParticlePairs hN χ c)
    {x : EuclideanSpace ℝ (Fin (N : ℕ))} (hx : x ∈ particleChamber N) :
    0 ≤ Laplacian.laplacian (particlePairEnergy χ) x := by
  rw [Riesz1.laplacian_eq_sum_fderiv_fderiv _ (EuclideanSpace.basisFun _ ℝ)]
  exact Finset.sum_nonneg fun _ _ => particlePairEnergy_hessian_nonneg hc h hx _

/-- See Subsection 3.1 of the paper (amplification) and the particle-metric assertion of
Lemma A.1: arbitrary positive coefficients and inverse-square mass. -/
theorem particle_collision_bound {hN : 2 ≤ (N : ℕ)} {χ : ParticlePairData N} {c : ℝ}
    (hc : 0 < c) (h : AdmissibleParticlePairs hN χ c)
    (a b k : ℝ) (ha : 0 < a) (hb : 0 < b) (_hk : 0 < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ particleChamber N,
      k * (Metric.infDist x (particleChamber N)ᶜ)⁻¹ ^ 2 - C ≤
        a * ‖gradient (particlePairEnergy χ) x‖ ^ 2 -
          b * Laplacian.laplacian (particlePairEnergy χ) x := by
  let t := max b k
  have ht : 0 < t := lt_of_lt_of_le hb (le_max_left _ _)
  obtain ⟨C, hC, hbound⟩ := h.2 (a / t) (div_pos ha ht)
  refine ⟨t * C, mul_nonneg ht.le hC, fun x hx => ?_⟩
  have hmul := mul_le_mul_of_nonneg_left (hbound x hx) ht.le
  have hlap := particlePairEnergy_laplacian_nonneg hc h hx
  have htb : b ≤ t := le_max_left _ _
  have htk : k ≤ t := le_max_right _ _
  have hgrad : t * (a / t) = a := by field_simp
  rw [mul_sub, mul_sub, ← mul_assoc, hgrad] at hmul
  nlinarith [mul_nonneg (sub_nonneg.mpr htb) hlap,
    mul_nonneg (sub_nonneg.mpr htk) (sq_nonneg (Metric.infDist x (particleChamber N)ᶜ)⁻¹)]

/-- See Subsection 3.1 of the paper, including every normalization, Hessian, curvature and
Riesz 1 collision-bound assertion. Derivatives are evaluated only inside the open chamber. -/
theorem particle_hessian_normalization (hN : 2 ≤ (N : ℕ)) (c : ℝ) (hc : 0 < c)
    (χ : ParticlePairData N) (h : AdmissibleParticlePairs hN χ c) :
    (0 < pairGibbsNormalizer χ ∧ pairGibbsNormalizer χ < ⊤) ∧
    (∀ x ∈ particleChamber N,
      fderiv ℝ (fderiv ℝ (particlePairEnergy χ)) x (Riesz1.hsRotationVector N) = 0 ∧
      ∀ u : gapTangentSpace N,
        (fderiv ℝ (fderiv ℝ (particlePairEnergy χ)) x u.val u.val =
          2 * ∑ p : {p : Fin (N : ℕ) × Fin (N : ℕ) // p.1 < p.2},
            deriv (deriv (χ p)) (x p.val.2 - x p.val.1) *
              (u.val p.val.2 - u.val p.val.1) ^ 2) ∧
        2 * (N : ℝ) * c * ‖u‖ ^ 2 ≤
          fderiv ℝ (fderiv ℝ (particlePairEnergy χ)) x u.val u.val) ∧
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ particleChamber N,
      (Metric.infDist x (particleChamber N)ᶜ)⁻¹ ^ 2 - C ≤
        ‖gradient (particlePairEnergy χ) x‖ ^ 2 / (4 * (N : ℝ)) -
          Laplacian.laplacian (particlePairEnergy χ) x / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [pair_normalizer_eq_library h]
    exact ⟨Riesz1.hsPartitionFunction_pos _, Riesz1.hsPartitionFunction_lt_top _ hc⟩
  · intro x hx
    constructor
    · ext v
      rw [particlePairEnergy_hessian h hx]
      simp [Riesz1.hsRotationVector]
    · intro u
      constructor
      · simpa only [pow_two] using particlePairEnergy_hessian h hx u.val u.val
      · rw [← libraryPairs_energy h]
        have hu' : u.val ∈ Riesz1.hsOrthSubspace N := by
          rw [← gapTangentSpace_eq_orth]
          exact u.property
        have hu : inner ℝ u.val (Riesz1.hsUnitVector N) = 0 :=
          Submodule.mem_orthogonal_singleton_iff_inner_left.mp hu'
        have hlower := Riesz1.hessian_hsPairExpression_lower_bound (libraryPairs h) hx u.val hu
        simpa only [Submodule.norm_coe, mul_comm, mul_left_comm, mul_assoc] using hlower
  · obtain ⟨C, hC, hbound⟩ := particle_collision_bound hc h (1 / (4 * (N : ℝ)))
      (1 / 2) 1 (by positivity) (by norm_num) (by norm_num)
    refine ⟨C, hC, fun x hx => ?_⟩
    simpa only [one_mul, one_div_mul_eq_div, div_eq_mul_inv, mul_comm] using hbound x hx

/-- The particle Gibbs weight is measurable on its actual configuration carrier. -/
theorem pairGibbsWeight_measurable {hN : 2 ≤ (N : ℕ)} {χ : ParticlePairData N} {c : ℝ}
    (h : AdmissibleParticlePairs hN χ c) :
    Measurable (fun X : Riesz1.Configuration N =>
      ENNReal.ofReal (Real.exp (-particlePairEnergy χ (WithLp.toLp 2 X.val)))) := by
  rw [← libraryPairs_energy h]
  exact (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
    (Riesz1.continuous_hsFundamentalHamiltonian (libraryPairs h)).neg)).measurable

/-- The Gibbs measure and the existing library probability are the same measure. -/
theorem pairGibbsMeasure_eq_library {hN : 2 ≤ (N : ℕ)} {χ : ParticlePairData N} {c : ℝ}
    (hc : 0 < c) (h : AdmissibleParticlePairs hN χ c) :
    pairGibbsMeasure χ (pairGibbsWeight_measurable h)
        (particle_hessian_normalization hN c hc χ h).1 =
      (Riesz1.hsGibbsProbability (libraryPairs h) hc : Measure (Riesz1.Configuration N)) := by
  simp only [pairGibbsMeasure, Riesz1.hsGibbsProbability, Riesz1.hsFundamentalWeight,
    Riesz1.hsFundamentalHamiltonian, libraryPairs_energy, ← pair_normalizer_eq_library h,
    ProbabilityMeasure.coe_mk]

/-- See Subsection 3.2 of the paper, rotation assertion: the orthogonal coordinate and common
rotation have product law, with the latter uniform on the circle of length `√N`.
This is the companion paper's normalized angle `ω = √N t mod √N`. -/
theorem particle_rotation_product_law (hN : 2 ≤ (N : ℕ)) (c : ℝ) (hc : 0 < c)
    (χ : ParticlePairData N) (h : AdmissibleParticlePairs hN χ c) :
    (pairGibbsMeasure χ (pairGibbsWeight_measurable h)
        (particle_hessian_normalization hN c hc χ h).1).map (Riesz1.hsConfigCoord N) =
      (Riesz1.hsRadialProbability (libraryPairs h) hc : Measure (Riesz1.hsOrthSubspace N)).prod
        (Riesz1.hsUniformCircle N : Measure (AddCircle (Real.sqrt (N : ℕ)))) := by
  rw [pairGibbsMeasure_eq_library hc h]
  exact Riesz1.hsGibbs_map_hsConfigCoord (libraryPairs h) hc

namespace AffineMetric

/-- The linear part of the existing cyclic gap map, with Euclidean norms. -/
def cyclicGapLinear (N : ℕ+) :
    EuclideanSpace ℝ (Fin (N : ℕ)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (N : ℕ)) where
  toFun x := WithLp.toLp 2 (fun i => (N : ℝ) * (x (finRotate (N : ℕ) i) - x i))
  map_add' x y := by ext i; simp; ring
  map_smul' a x := by ext i; simp; ring

theorem cyclicGapLinear_apply (N : ℕ+) (x : EuclideanSpace ℝ (Fin (N : ℕ)))
    (i : Fin (N : ℕ)) :
    cyclicGapLinear N x i = (N : ℝ) * (x (finRotate (N : ℕ) i) - x i) := rfl

/-- The existing gap map is affine on its entire ambient carrier. -/
theorem hsGap_eq_linear_add (x : EuclideanSpace ℝ (Fin (N : ℕ))) :
    WithLp.toLp 2 (Riesz1.hsGap x) =
      cyclicGapLinear N x + WithLp.toLp 2 (Riesz1.hsGap (0 : EuclideanSpace ℝ (Fin (N : ℕ)))) := by
  ext i
  have hrot : (finRotate (N : ℕ) i).val = (i.val + 1) % (N : ℕ) := by
    rw [finRotate_apply]
    simp [Fin.val_add, Nat.add_mod]
  by_cases hi : i.val + 1 < (N : ℕ)
  · have he : finRotate (N : ℕ) i = ⟨i.val + 1, hi⟩ := by
      apply Fin.ext
      rw [hrot, Nat.mod_eq_of_lt hi]
    simp only [PiLp.add_apply, cyclicGapLinear_apply,
      Riesz1.hsGap, Riesz1.hsCyclicLift_nat x hi, Riesz1.hsCyclicLift_nat x i.isLt,
      Riesz1.hsCyclicLift_nat (0 : EuclideanSpace ℝ (Fin (N : ℕ))) hi,
      Riesz1.hsCyclicLift_nat (0 : EuclideanSpace ℝ (Fin (N : ℕ))) i.isLt, he]
    simp
  · have heq : i.val + 1 = (N : ℕ) := by omega
    have he : finRotate (N : ℕ) i = ⟨0, N.pos⟩ := by
      apply Fin.ext
      rw [hrot, heq, Nat.mod_self]
    simp only [PiLp.add_apply, cyclicGapLinear_apply, Riesz1.hsGap, heq,
      Riesz1.hsCyclicLift_card, Riesz1.hsCyclicLift_nat x i.isLt,
      Riesz1.hsCyclicLift_nat (0 : EuclideanSpace ℝ (Fin (N : ℕ))) i.isLt, he]
    simp
    ring

theorem sum_cyclicGapLinear (N : ℕ+) (x : EuclideanSpace ℝ (Fin (N : ℕ))) :
    ∑ i, cyclicGapLinear N x i = 0 := by
  simp only [cyclicGapLinear_apply, ← Finset.mul_sum, Finset.sum_sub_distrib]
  rw [Equiv.sum_comp (finRotate (N : ℕ)) (fun i => x i), sub_self, mul_zero]

/-- The cyclic difference operator restricted to the zero-sum space. -/
def gapLinear (N : ℕ+) : gapTangentSpace N →ₗ[ℝ] gapTangentSpace N where
  toFun z := ⟨cyclicGapLinear N z.val, sum_cyclicGapLinear N z.val⟩
  map_add' z w := Subtype.ext ((cyclicGapLinear N).map_add z.val w.val)
  map_smul' a z := Subtype.ext ((cyclicGapLinear N).map_smul a z.val)

theorem gapLinear_injective (N : ℕ+) : Function.Injective (gapLinear N) := by
  intro z w h
  apply Subtype.ext
  apply Riesz1.eq_of_hsGap_eq_of_mem_orth
  · rw [← gapTangentSpace_eq_orth]; exact z.property
  · rw [← gapTangentSpace_eq_orth]; exact w.property
  · have hv : cyclicGapLinear N z.val = cyclicGapLinear N w.val := congrArg Subtype.val h
    have he : WithLp.toLp 2 (Riesz1.hsGap z.val) = WithLp.toLp 2 (Riesz1.hsGap w.val) := by
      calc
        _ = cyclicGapLinear N z.val + WithLp.toLp 2 (Riesz1.hsGap 0) := hsGap_eq_linear_add _
        _ = cyclicGapLinear N w.val + WithLp.toLp 2 (Riesz1.hsGap 0) := by rw [hv]
        _ = _ := (hsGap_eq_linear_add _).symm
    exact congrArg WithLp.ofLp he

/-- Invertibility of the derivative of the affine gap chart. -/
def gapLinearEquiv (N : ℕ+) : gapTangentSpace N ≃L[ℝ] gapTangentSpace N :=
  (LinearEquiv.ofBijective (gapLinear N)
    ((LinearMap.injective_iff_surjective (f := gapLinear N)).mp (gapLinear_injective N)
      |> fun hs => ⟨gapLinear_injective N, hs⟩)).toContinuousLinearEquiv

/-- The affine offset, expressed in the isometric chart `y = 1 + z`. -/
def gapOffset (N : ℕ+) : gapTangentSpace N :=
  centeredGapChart N (WithLp.toLp 2 (Riesz1.hsGap (0 : EuclideanSpace ℝ (Fin (N : ℕ)))))

/-- The existing gap map followed by its isometric centering chart. -/
def intrinsicParticleGapMap (N : ℕ+) (z : gapTangentSpace N) : gapTangentSpace N :=
  centeredGapChart N (WithLp.toLp 2 (Riesz1.hsGap z.val))

theorem intrinsicParticleGapMap_eq (N : ℕ+) (z : gapTangentSpace N) :
    intrinsicParticleGapMap N z = gapLinearEquiv N z + gapOffset N := by
  apply Subtype.ext
  ext i
  have he := congrArg (fun x : EuclideanSpace ℝ (Fin (N : ℕ)) => x i)
    (hsGap_eq_linear_add z.val)
  change Riesz1.hsGap z.val i - (∑ j, Riesz1.hsGap z.val j) / (N : ℝ) =
    cyclicGapLinear N z.val i +
      ((Riesz1.hsGap (0 : EuclideanSpace ℝ (Fin (N : ℕ)))) i -
        (∑ j, Riesz1.hsGap (0 : EuclideanSpace ℝ (Fin (N : ℕ))) j) / (N : ℝ))
  rw [Riesz1.sum_hsGap, Riesz1.sum_hsGap]
  change Riesz1.hsGap z.val i = cyclicGapLinear N z.val i + Riesz1.hsGap 0 i at he
  linarith

/-- See Subsection 3.2 of the paper: the derivative of `T` is the invertible cyclic difference map. -/
theorem hasFDerivAt_intrinsicParticleGapMap (N : ℕ+) (z : gapTangentSpace N) :
    HasFDerivAt (intrinsicParticleGapMap N) (gapLinearEquiv N).toContinuousLinearMap z := by
  simpa only [← intrinsicParticleGapMap_eq] using
    (gapLinearEquiv N).hasFDerivAt.add_const (gapOffset N)

theorem intrinsicParticleGapMap_apply (N : ℕ+) (z : gapTangentSpace N)
    (i : Fin (N : ℕ)) :
    (intrinsicParticleGapMap N z).val i = Riesz1.hsGap z.val i - 1 := by
  change Riesz1.hsGap z.val i - (∑ j, Riesz1.hsGap z.val j) / (N : ℝ) = _
  rw [Riesz1.sum_hsGap, div_self (by positivity : (N : ℝ) ≠ 0)]

theorem centeredGapChart_val_eq_translate (N : ℕ+)
    (x : EuclideanSpace ℝ (Fin (N : ℕ))) :
    (centeredGapChart N x).val = Riesz1.hsTranslate (-(∑ i, x i) / (N : ℝ)) x := by
  ext i
  change x i - (∑ j, x j) / (N : ℝ) = x i + -(∑ j, x j) / (N : ℝ)
  ring

/-- See Subsection 3.2 of the paper: the gap map is a bijection from the orthogonal
quotient chamber onto the full intrinsic gap simplex. -/
theorem intrinsicParticleGapMap_bijOn (N : ℕ+) :
    Set.BijOn (intrinsicParticleGapMap N)
      {z : gapTangentSpace N | z.val ∈ particleChamber N} (intrinsicGapDomain N) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz i
    have hp := (Riesz1.hsGap_mem_gapSimplex hz).1 i
    change 0 < 1 + (intrinsicParticleGapMap N z).val i
    rw [intrinsicParticleGapMap_apply]
    linarith
  · intro z _ w _ h
    simp only [intrinsicParticleGapMap_eq, add_left_inj] at h
    exact (gapLinearEquiv N).injective h
  · intro w hw
    let a : Fin (N : ℕ) → ℝ := fun i => 1 + w.val i
    have ha : a ∈ Riesz1.gapSimplex N := by
      refine ⟨hw, ?_⟩
      simp only [a, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
      rw [show ∑ i, w.val i = 0 from w.property, add_zero]
    obtain ⟨x, hx, hgap⟩ := Riesz1.exists_hsGap_eq a ha
    refine ⟨centeredGapChart N x, ?_, ?_⟩
    · change (centeredGapChart N x).val ∈ Riesz1.hsChamber N
      rw [centeredGapChart_val_eq_translate]
      exact (Riesz1.hsTranslate_mem_chamber_iff _ x).mpr hx
    · apply Subtype.ext
      ext i
      rw [intrinsicParticleGapMap_apply, centeredGapChart_val_eq_translate,
        Riesz1.hsGap_translate, hgap]
      change 1 + w.val i - 1 = w.val i
      ring

/-- See Subsection 3.2 of the paper: the largest singular value is at most `2N`. -/
theorem norm_cyclicGapLinear_le (N : ℕ+) (x : EuclideanSpace ℝ (Fin (N : ℕ))) :
    ‖cyclicGapLinear N x‖ ≤ 2 * (N : ℝ) * ‖x‖ := by
  let r : EuclideanSpace ℝ (Fin (N : ℕ)) :=
    WithLp.toLp 2 (fun i => x (finRotate (N : ℕ) i))
  have hr : ‖r‖ = ‖x‖ := by
    simp only [EuclideanSpace.norm_eq]
    congr 1
    exact Equiv.sum_comp (finRotate (N : ℕ)) (fun i => ‖x i‖ ^ 2)
  have he : cyclicGapLinear N x = (N : ℝ) • (r - x) := by
    ext i
    rfl
  rw [he, norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ))]
  calc
    (N : ℝ) * ‖r - x‖ ≤ (N : ℝ) * (‖r‖ + ‖x‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
    _ = _ := by rw [hr]; ring

theorem norm_gapLinearEquiv_le (N : ℕ+) (z : gapTangentSpace N) :
    ‖gapLinearEquiv N z‖ ≤ 2 * (N : ℝ) * ‖z‖ :=
  norm_cyclicGapLinear_le N z.val

theorem opNorm_gapLinearEquiv_le (N : ℕ+) :
    ‖(gapLinearEquiv N).toContinuousLinearMap‖ ≤ 2 * (N : ℝ) :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) (norm_gapLinearEquiv_le N)

/-- Consecutive sums of the existing gaps recover each pair separation. -/
theorem sum_hsGap_interval (x : EuclideanSpace ℝ (Fin (N : ℕ)))
    (i j : Fin (N : ℕ)) (hij : i ≤ j) :
    (∑ a ∈ univ.filter (fun a : Fin (N : ℕ) => i.val ≤ a.val ∧ a.val < j.val),
      Riesz1.hsGap x a) = (N : ℝ) * (x j - x i) := by
  let f : ℕ → ℝ := fun k => Riesz1.hsCyclicLift x (k : ℤ)
  have he : (∑ a ∈ univ.filter (fun a : Fin (N : ℕ) => i.val ≤ a.val ∧ a.val < j.val),
      Riesz1.hsGap x a) =
      (N : ℝ) * ∑ k ∈ Finset.Ico i.val j.val, (f (k + 1) - f k) := by
    simp only [Riesz1.hsGap, ← Finset.mul_sum]
    congr 1
    apply Finset.sum_bij (fun a _ => a.val)
    · intro a ha
      simpa using (Finset.mem_filter.mp ha).2
    · intro a _ b _ hab
      exact Fin.ext hab
    · intro k hk
      have hk' := Finset.mem_Ico.mp hk
      refine ⟨⟨k, hk'.2.trans j.isLt⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'⟩
    · intro a _
      rfl
  rw [he, Finset.sum_Ico_eq_sub _ (show i.val ≤ j.val from hij),
    Finset.sum_range_sub, Finset.sum_range_sub]
  dsimp only [f]
  rw [Riesz1.hsCyclicLift_nat x j.isLt, Riesz1.hsCyclicLift_nat x i.isLt]
  ring

/-- See Subsection 3.2 of the paper: the inverse-chart potential recovers `H`.
This identity holds on the entire lift space, before imposing chamber hypotheses. -/
theorem pairAmbientGapPotential_hsGap (χ : ParticlePairData N)
    (x : EuclideanSpace ℝ (Fin (N : ℕ))) :
    pairAmbientGapPotential χ (WithLp.toLp 2 (Riesz1.hsGap x)) = particlePairEnergy χ x := by
  unfold pairAmbientGapPotential particlePairEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [sum_hsGap_interval x p.val.1 p.val.2 p.property.le,
    mul_div_cancel_left₀ _ (by positivity : (N : ℝ) ≠ 0)]

/-- See Subsection 3.2 of the paper: `H = W ∘ T` in the intrinsic chart. -/
theorem pairPotential_intrinsicParticleGapMap (χ : ParticlePairData N)
    (z : gapTangentSpace N) :
    pairAmbientGapPotential χ
      (WithLp.toLp 2 (fun i => 1 + (intrinsicParticleGapMap N z).val i)) =
        particlePairEnergy χ z.val := by
  have he : WithLp.toLp 2 (fun i => 1 + (intrinsicParticleGapMap N z).val i) =
      WithLp.toLp 2 (Riesz1.hsGap z.val) := by
    ext i
    change 1 + (intrinsicParticleGapMap N z).val i = Riesz1.hsGap z.val i
    rw [intrinsicParticleGapMap_apply]
    ring
  rw [he, pairAmbientGapPotential_hsGap]

theorem intrinsicParticleGapMap_mem_iff (N : ℕ+) (z : gapTangentSpace N) :
    intrinsicParticleGapMap N z ∈ intrinsicGapDomain N ↔ z.val ∈ particleChamber N := by
  constructor
  · intro hz
    obtain ⟨w, hw, he⟩ := (intrinsicParticleGapMap_bijOn N).surjOn hz
    have heq : w = z := by
      simp only [intrinsicParticleGapMap_eq, add_left_inj] at he
      exact (gapLinearEquiv N).injective he
    exact heq ▸ hw
  · intro hz
    exact (intrinsicParticleGapMap_bijOn N).mapsTo hz

/-- The global homeomorphism underlying the affine gap chart. -/
def particleGapHomeomorph (N : ℕ+) : gapTangentSpace N ≃ₜ gapTangentSpace N :=
  (gapLinearEquiv N).toHomeomorph.trans (Homeomorph.addRight (gapOffset N))

theorem particleGapHomeomorph_apply (N : ℕ+) (z : gapTangentSpace N) :
    particleGapHomeomorph N z = intrinsicParticleGapMap N z :=
  (intrinsicParticleGapMap_eq N z).symm

end AffineMetric

end Riesz2
