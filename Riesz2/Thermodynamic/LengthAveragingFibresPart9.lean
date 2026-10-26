/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.LengthAveragingFibresPart5
public import Riesz2.Thermodynamic.LengthAveragingFibresPart3
public import Riesz2.DecayShort.PhysicalDecayPart3
public import Riesz2.Thermodynamic.FixedLengthDecayPart6
import all Riesz2.DecayShort.ExceptionalEventPart4
import all Riesz2.DecayShort.PhysicalComparisonPart4

/-!
# Short marginal matrices with independent penalty and fine-event exponents

See the proof of Lemma 6.5. The identity cutoffs are those of Subsection 4.5, with the
physical penalty evaluated at epsilon and the event evaluated at eta. Local notation
abbreviates these formulas.
-/

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Classical ContDiff

attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false

namespace Riesz2.LengthAveragingFibres

open DecayShort DecayShort.PhysicalComparison

section IndependentExponents

variable (p : Parameters) (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε η κ : ℝ)

local notation "F" => (fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
  ∑ i, (θ.val (((n : ℝ)^ε)⁻¹*y i) + θ.val (((n : ℝ)^ε)⁻¹*(y i)⁻¹)))
local notation "K" => (fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
  p.val.1⁻¹*(p.val.1*F y - Real.log (∫ z : EuclideanSpace ℝ (Fin m),
    (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,z)).toReal)))
local notation "G" => shortFineEvent p n m η κ
local notation "I" => (fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) =>
  IntervalBoundary.internalMatrix ((n : ℕ)+m).succPNat n (by simp; omega)
    (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x))
local notation "Hf" => (fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) =>
  if x ∈ G then hessianMatrix K x.val else (1 : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ))
local notation "Mf" => (fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) =>
  if x ∈ G then hessianMatrix F x.val + I x else (1 : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ))

/-- See the proof of Lemma 6.5 in the paper, short step of Subsection 4.5:
the actual full-minus-internal defect is independent of the physical penalty
exponent. The fine event remains exactly the event at eta. -/
theorem short_independent_defect_internal :
    ∀ x : AffineSimplex.chartDomain n ((n+m : ℕ)+1),
    Hf x - Mf x = frozenPhysicalMatrix p n m θ η true ((n : ℝ)^(κ*η)) x -
      frozenInternalMatrix p n m θ η true ((n : ℝ)^(κ*η)) x := by
  intro x
  ext i j
  by_cases hx : x ∈ G
  · have hh := marginal_penalty_difference_internal p n m θ ε η x i j
    simp only [shortFineEvent] at hx
    simp only [Matrix.sub_apply, frozenPhysicalMatrix, frozenInternalMatrix,
      shortFineEvent, hx, ↓reduceIte, Matrix.add_apply]
    dsimp only at hh
    linarith only [hh]
  · have hx' := hx
    simp only [shortFineEvent] at hx'
    simp only [Matrix.sub_apply, frozenPhysicalMatrix, frozenInternalMatrix,
      shortFineEvent, hx', ↓reduceIte, sub_self]

/-- See the proof of Lemma 6.5 in the paper, short matrix step:
measurability and symmetry of both literal matrices at independent exponents. -/
theorem short_independent_measurable_symmetric_internal (hs : 1 < p.val.2)
    (hε : 0 < ε) :
    (∀ i j, Measurable (fun x => Hf x i j)) ∧
    (∀ i j, Measurable (fun x => Mf x i j)) ∧
    (∀ x i j, Hf x i j = Hf x j i) ∧
    (∀ x i j, Mf x i j = Mf x j i) := by
  have hF := (ExceptionalEvent.penalty_smooth_convex n ((n+m : ℕ)+1) θ
    (by positivity : 0 < ((n : ℝ)^ε)⁻¹) true).1
  change ContDiffOn ℝ ∞ F (AffineSimplex.chartDomain n ((n+m : ℕ)+1)) at hF
  have hK := (PhysicalFibres.active_marginal_curvature p hs n m n.pos
    (Equiv.refl _) θ ε hε true).1
  change ContDiffOn ℝ ∞ K (AffineSimplex.chartDomain n ((n+m : ℕ)+1)) at hK
  have hG := measurableSet_shortFineEvent p hs n m θ η κ
  have hmI (i j : Fin (n : ℕ)) : Measurable (fun x => I x i j) := by
    apply Finset.measurable_sum
    intro t _
    split_ifs
    · exact (measurable_conditionalIntervalWeight p n m n.pos (Equiv.refl _) t).mul_const _
    · exact measurable_const
  refine ⟨fun i j => ?_, fun i j => ?_, fun x i j => ?_, fun x i j => ?_⟩
  · have hm : Measurable (fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) =>
        if x ∈ G then hessianMatrix K x.val i j else
          (1 : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ) i j) := Measurable.ite hG
      (measurable_hessianMatrix (AffineSimplex.isOpen_chartDomain _ _) hK i j)
      (measurable_const (a := (1 : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ) i j))
    convert hm using 1
    funext x
    dsimp only
    split_ifs <;> rfl
  · have hm : Measurable (fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) =>
        if x ∈ G then hessianMatrix F x.val i j + I x i j else
          (1 : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ) i j) := Measurable.ite hG
      ((measurable_hessianMatrix (AffineSimplex.isOpen_chartDomain _ _) hF i j).add (hmI i j))
      (measurable_const (a := (1 : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ) i j))
    convert hm using 1
    funext x
    dsimp only
    split_ifs <;> rfl
  · dsimp only
    split_ifs
    · exact hessianMatrix_symm
        ((hK.contDiffAt ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds x.property)).of_le
          (by norm_num)) i j
    · exact Matrix.isSymm_one.apply j i
  · dsimp only
    split_ifs
    · simp only [Matrix.add_apply]
      rw [hessianMatrix_symm
        ((hF.contDiffAt ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds x.property)).of_le
          (by norm_num)) i j,
        IntervalBoundary.internalMatrix_symm]
    · exact Matrix.isSymm_one.apply j i

/-- See the proof of Lemma 6.5 in the paper: coercivity of the full
cutoff uses the physical exponent epsilon, including outside the fine event. -/
theorem short_independent_physical_lower_internal (hs : 1 < p.val.2)
    (hε : 0 < ε) (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1))
    (z : Fin (n : ℕ) → ℝ) :
    (n : ℝ)^(-(p.val.2+2)*ε)*(∑ i, z i^2) ≤
      ∑ i, ∑ j, z i*Hf x i j*z j := by
  by_cases hx : x ∈ G
  · simp only [hx, ↓reduceIte]
    have hK := PhysicalFibres.active_marginal_curvature p hs n m n.pos
      (Equiv.refl _) θ ε hε true
    have hKx : ContDiffAt ℝ 2 K x.val :=
      (hK.1.contDiffAt ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds x.property)).of_le
        (by norm_num)
    have hb := hK.2 x.val x.property (WithLp.toLp 2 z)
    change (n : ℝ)^(-(p.val.2+2)*ε)*‖WithLp.toLp 2 z‖^2 ≤
      fderiv ℝ (fderiv ℝ K) x.val (WithLp.toLp 2 z) (WithLp.toLp 2 z) at hb
    rw [← PhysicalEnergy.hessianMatrix_quadratic hKx, EuclideanSpace.real_norm_sq_eq] at hb
    exact hb
  · simp only [hx, ↓reduceIte, Matrix.one_apply, mul_ite, mul_one, mul_zero,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ← sq]
    exact mul_le_of_le_one_left (Finset.sum_nonneg fun i _ => sq_nonneg (z i))
      (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast n.pos)
        (by nlinarith [p.property.2.1]))

/-- See the proof of Lemma 6.5 in the paper: the internal cutoff is
coercive at the fine exponent eta while its nonnegative penalty is still
the physical penalty at epsilon. -/
theorem short_independent_internal_lower_internal (hs : 1 < p.val.2)
    (hN : 2 ≤ (n : ℕ)+m+1) (hη : 0 ≤ η)
    (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1)) (z : Fin (n : ℕ) → ℝ) :
    (n : ℝ)^(-(p.val.2+2)*η)*(∑ i, z i^2) ≤
      ∑ i, ∑ j, z i*Mf x i j*z j := by
  have hn : (0 : ℝ) < n := by positivity
  by_cases hx : x ∈ G
  · have hl := IntervalBoundary.internalMatrix_singleton_lower ((n : ℕ)+m).succPNat n
      (by simp; omega) (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
      (conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x)
      (by simpa only [Nat.succPNat_coe] using hN)
      ((n : ℝ)^(-(p.val.2+2)*η)) (fun i => ?_) z
    · have hconv := ExceptionalEvent.penalty_smooth_convex n ((n+m : ℕ)+1) θ
        (by positivity : 0 < ((n : ℝ)^ε)⁻¹) true
      have hFx : ContDiffAt ℝ 2 F x.val := (hconv.1.contDiffAt
        ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds x.property)).of_le (by norm_num)
      have hp : 0 ≤ ∑ i, ∑ j, z i*hessianMatrix F x.val i j*z j := by
        rw [PhysicalEnergy.hessianMatrix_quadratic hFx (WithLp.toLp 2 z)]
        exact Riesz1.fderiv_fderiv_nonneg_of_convexOn (AffineSimplex.isOpen_chartDomain _ _)
          hconv.2.1 hconv.2 (hconv.1.of_le (by norm_num)) x.property _
      change _ ≤ ∑ i, ∑ j, z i*(if x ∈ G then hessianMatrix F x.val + I x else 1) i j*z j
      rw [ite_eq_left hx]
      have he : (∑ i, ∑ j, z i*(hessianMatrix F x.val + I x) i j*z j) =
          (∑ i, ∑ j, z i*hessianMatrix F x.val i j*z j) +
            ∑ i, ∑ j, z i*I x i j*z j := by
        simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
      rw [he]
      exact hl.trans (le_add_of_nonneg_left hp)
    · have hu : x.val i ≤ (n : ℝ)^η := (hx.1.2.1 i).2
      have hp : (n : ℝ)^(-(p.val.2+2)*η) ≤ (x.val i)^(-p.val.2-2) := by
        calc
          _ = ((n : ℝ)^η)^(-p.val.2-2) := by rw [← Real.rpow_mul hn.le]; congr 1; ring
          _ ≤ _ := Real.rpow_le_rpow_of_nonpos (x.property.1 i) hu (by linarith)
      apply hp.trans
      apply le_trans _ (internal_singleton_coefficient_lower p n m hN x i)
      have hs1 : 1 ≤ p.val.2*(p.val.2+1) := by nlinarith
      exact le_mul_of_one_le_left (Real.rpow_nonneg (x.property.1 i).le _) hs1
  · simp only [hx, ↓reduceIte, Matrix.one_apply, mul_ite, mul_one, mul_zero,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ← sq]
    exact mul_le_of_le_one_left (Finset.sum_nonneg fun i _ => sq_nonneg (z i))
      (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast n.pos)
        (by nlinarith [p.property.2.1]))

/-- See the proof of Lemma 6.5 in the paper: physical penalty entries
at epsilon are diagonal and bounded using the gap cutoff at eta. -/
theorem short_independent_penalty_internal
    (C : ℝ) (hC : ∀ x : AffineSimplex.chartDomain n ((n+m : ℕ)+1),
      x ∈ G → ∀ i j, |InterpolationMatrix.penaltyHessian n θ ε x.val i j| ≤
        if i = j then C*(n : ℝ)^(4*η) else 0)
    (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1)) (hx : x ∈ G) (i j : Fin (n : ℕ)) :
    |hessianMatrix F x.val i j| ≤ if i = j then C*(n : ℝ)^(4*η) else 0 := by
  simpa only [InterpolationMatrix.penaltyHessian, Real.rpow_neg (by positivity : (0 : ℝ) ≤ n)]
    using hC x hx i j

/-- See the proof of Lemma 6.5 in the paper, matrix step: a diagonal
penalty bound at eta and the literal coefficient event control every
internal entry, with ordinary interval distance. -/
theorem short_independent_internal_entries_internal
    (hhalf : 2*(n : ℕ) ≤ (n : ℕ)+m+1)
    (C : ℝ) (hC : 0 ≤ C)
    (hpen : ∀ x : AffineSimplex.chartDomain n ((n+m : ℕ)+1), x ∈ G → ∀ i j,
      |hessianMatrix F x.val i j| ≤ if i = j then C*(n : ℝ)^(4*η) else 0)
    (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1)) (i j : Fin (n : ℕ)) :
    |Mf x i j| ≤ (1+(n : ℝ)^(κ*η)+C*(n : ℝ)^(4*η))*
      (1+|(i.val : ℝ)-(j.val : ℝ)|)^(-p.val.2) := by
  let r := (1+|(i.val : ℝ)-(j.val : ℝ)|)^(-p.val.2)
  have hr : 0 ≤ r := Real.rpow_nonneg (by positivity) _
  by_cases hx : x ∈ G
  · have hIb : |I x i j| ≤ (n : ℝ)^(κ*η)*r := by
      rw [abs_of_nonneg (IntervalBoundary.internalMatrix_nonneg ((n : ℕ)+m).succPNat n (by simp; omega) _
        (conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x) i j)]
      apply (IntervalBoundary.internalMatrix_le_intervalMatrix ((n : ℕ)+m).succPNat n (by simp; omega) _
        (conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x) i j).trans
      have hb := hx.2.1 i j
      rw [properBlock_distance _ _ _ (by simpa only [Nat.succPNat_coe] using hhalf)] at hb
      exact hb
    have hFb : |hessianMatrix F x.val i j| ≤ C*(n : ℝ)^(4*η)*r := by
      by_cases hij : i = j
      · subst j
        simpa only [r, sub_self, abs_zero, add_zero, Real.one_rpow, mul_one, ↓reduceIte] using
          hpen x hx i i
      · have he : hessianMatrix F x.val i j = 0 := by
          exact abs_eq_zero.mp (le_antisymm (by simpa only [hij, ↓reduceIte] using hpen x hx i j)
            (abs_nonneg _))
        rw [he, abs_zero]
        positivity
    simp only [hx, ↓reduceIte, Matrix.add_apply]
    exact (abs_add_le _ _).trans ((add_le_add hFb hIb).trans (by dsimp only [r] at *; nlinarith))
  · simp only [hx, ↓reduceIte]
    by_cases hij : i = j
    · subst j
      simp only [Matrix.one_apply_eq, abs_one, sub_self, abs_zero, add_zero, Real.one_rpow, mul_one]
      nlinarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n) (κ*η),
        mul_nonneg hC (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n) (4*η))]
    · simp only [Matrix.one_apply_ne hij, abs_zero]
      positivity

/-- See the proof of Lemma 6.5 in the paper: the full cutoff has a
cardinality-independent upper quadratic bound on the fine event at eta,
with the penalty still evaluated at epsilon. -/
theorem short_independent_physical_upper_internal (hs : 1 < p.val.2)
    (hε : 0 < ε) (C : ℝ) (hC : 0 ≤ C)
    (hpen : ∀ x : AffineSimplex.chartDomain n ((n+m : ℕ)+1), x ∈ G → ∀ i j,
      |hessianMatrix F x.val i j| ≤ if i = j then C*(n : ℝ)^(4*η) else 0)
    (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1)) (z : Fin (n : ℕ) → ℝ) :
    (∑ i, ∑ j, z i*Hf x i j*z j) ≤
      (1+C*(n : ℝ)^(4*η)+2*(n : ℝ)^(κ*η)*
        ((2*∑' k : ℕ, (1+(k : ℝ))^(-p.val.2))+1))*(∑ i, z i^2) := by
  let D := (n : ℝ)^(κ*η)
  let S := 2*∑' k : ℕ, (1+(k : ℝ))^(-p.val.2)
  let N := ((n : ℕ)+m).succPNat
  have hn : (n : ℕ) ≤ (N : ℕ) := by simp only [N, Nat.succPNat_coe]; omega
  let A := conditionalIntervalWeight p n m n.pos (Equiv.refl _) x
  let P := IntervalBoundary.intervalMatrix N n hn A
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hz : 0 ≤ ∑ i, z i^2 := Finset.sum_nonneg fun i _ => sq_nonneg (z i)
  by_cases hx : x ∈ G
  · have hp : (∑ i, ∑ j, z i*hessianMatrix F x.val i j*z j) ≤
        C*(n : ℝ)^(4*η)*(∑ i, z i^2) := by
      have he (i) : (∑ j, z i*hessianMatrix F x.val i j*z j) =
          z i*hessianMatrix F x.val i i*z i := by
        apply Finset.sum_eq_single i
        · intro j _ hij
          have he := hpen x hx i j
          rw [ite_eq_right (Ne.symm hij)] at he
          have he0 := abs_eq_zero.mp (le_antisymm he (abs_nonneg _))
          rw [he0, mul_zero, zero_mul]
        · simp
      simp_rw [he]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      have hb := hpen x hx i i
      rw [ite_eq_left rfl] at hb
      have hb' := (le_abs_self _).trans hb
      nlinarith [mul_le_mul_of_nonneg_right hb' (sq_nonneg (z i))]
    obtain ⟨hr,hc⟩ := complete_schur_bounds p hs n m D hD x hx.2
    have hPnn (i j) : 0 ≤ P i j := IntervalBoundary.intervalMatrix_nonneg N n hn A
      (conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x) i j
    have hP : (∑ i, ∑ j, z i*P i j*z j) ≤ D*S*(∑ i, z i^2) := by
      calc
        _ ≤ ∑ i, ∑ j, |z i| * P i j * |z j| := Finset.sum_le_sum fun i _ =>
          Finset.sum_le_sum fun j _ => (le_abs_self _).trans_eq (by
            rw [abs_mul, abs_mul, abs_of_nonneg (hPnn i j)])
        _ ≤ _ := by
          simpa only [add_self_div_two] using
            InitialDecay.Internal.schur_quadratic_le P hPnn (D*S) (D*S) hr hc z
    have hmode := exterior_mode_bound p n m D x hx.2
    have hsum : (∑ i, z i)^2 ≤ (n : ℝ)*∑ i, z i^2 := by
      have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin (n : ℕ) => (1 : ℝ)) z
      simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one] using hh
    have hmode' := mul_le_mul_of_nonneg_left hsum hmode.1
    have hmode'' := mul_le_mul_of_nonneg_right hmode.2 hz
    have hupper := physical_hessian_quadratic_upper p n m θ ε hε true x z
    change (∑ i, ∑ j, z i*hessianMatrix K x.val i j*z j) ≤
      (∑ i, ∑ j, z i*hessianMatrix F x.val i j*z j)+
        2*(∑ i, ∑ j, z i*P i j*z j)+_ at hupper
    change (∑ i, ∑ j, z i*(if x ∈ G then hessianMatrix K x.val else 1) i j*z j) ≤ _
    rw [ite_eq_left hx]
    apply hupper.trans
    dsimp only [N, Nat.succPNat_coe] at hmode' hmode'' ⊢
    nlinarith only [hp, hP, hmode', hmode'', hz]
  · simp only [hx, ↓reduceIte, Matrix.one_apply, mul_ite, mul_one, mul_zero,
      ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ← sq]
    have hc0 : 0 ≤ C*(n : ℝ)^(4*η) := by positivity
    have hd0 : 0 ≤ 2*D*(S+1) := by positivity
    change (∑ i, z i^2) ≤ (1+C*(n : ℝ)^(4*η)+2*D*(S+1))*(∑ i, z i^2)
    nlinarith only [mul_nonneg hc0 hz, mul_nonneg hd0 hz]

/-- See the proof of Lemma 6.5 in the paper, short step of Subsection 4.5:
the independent-exponent defect applied to a summably decaying source
has the actual boundary and ambient-volume rates, on any retained law. -/
theorem short_independent_source_internal (hs : 1 < p.val.2)
    (βlo βhi : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi)
    (hpl : βlo ≤ p.val.1) (hph : p.val.1 ≤ βhi) :
    ∃ C : ℝ, 1 ≤ C ∧
    (4 ≤ (n : ℕ)+m+1 → 2*(n : ℕ) ≤ (n : ℕ)+m+1 → 0 < η →
    ∀ (ν : Measure (AffineSimplex.chartDomain n ((n+m : ℕ)+1)))
      (i₀ : Fin (n : ℕ)), (n : ℝ)/4 ≤ (i₀.val : ℝ)+1 →
      (i₀.val : ℝ)+1 ≤ 3*(n : ℝ)/4 →
    ∀ V : ℝ, 0 ≤ V → ∀ v : Fin (n : ℕ) → Lp ℝ 2 ν,
      (∀ i, ‖v i‖ ≤ V*(1+|(i.val : ℝ)-(i₀.val : ℝ)|)^(-p.val.2)) →
    ∃ g : Fin (n : ℕ) → Lp ℝ 2 ν,
      (∀ᵐ x ∂ν, ∀ i, g i x = ∑ j, (Hf x-Mf x) i j*v j x) ∧
      ‖WithLp.toLp 2 g‖ ≤ C*(n : ℝ)^(κ*η)*V*
        ((n : ℝ)^(-(p.val.2-1/2))+(((n : ℕ)+m+1 : ℕ) : ℝ)^(-(1/2 : ℝ)))) := by
  obtain ⟨C,hC,hres⟩ := DecayShort.PhysicalDecay.internal_residual_profile_compact
    p.val.2 βlo βhi hs hlo hle
  refine ⟨C, hC, ?_⟩
  intro hN hhalf hη ν i₀ hi₀ hj₀ V hV v hv
  obtain ⟨g,hg,hgn⟩ := hres p rfl hpl hph n m hN hhalf θ η hη true
    ((n : ℝ)^(κ*η)) (by positivity) _ id measurable_id ν i₀ hi₀ hj₀ V hV v hv
  refine ⟨g, ?_, hgn⟩
  filter_upwards [hg] with x hx i
  rw [short_independent_defect_internal p n m θ ε η κ x]
  exact hx i

end IndependentExponents

/-- See the proof of Lemma 6.5 in the paper, independent-exponent
version of Subsection 4.5: both actual cutoffs have uniform matrix bounds.
The loss precedes both exponents, and the prefactor precedes beta, the
volumes, the fibre law and its length. The event is the exact short fine set. -/
theorem short_independent_matrix_bounds_internal (s : ℝ) (hs : 1 < s) (κ : ℝ) :
    ∃ q : ℝ, 0 ≤ q ∧ ∀ θ : PhysicalCutoff, ∃ C : ℝ, 1 ≤ C ∧
    ∀ (p : Parameters), p.val.2 = s → ∀ (n : ℕ+) (m : ℕ),
      2*(n : ℕ) ≤ (n : ℕ)+m+1 → ∀ ε η : ℝ, 0 < ε → ε ≤ η →
    let F := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      ∑ i, (θ.val (((n : ℝ)^ε)⁻¹*y i)+θ.val (((n : ℝ)^ε)⁻¹*(y i)⁻¹))
    let K := fun y => p.val.1⁻¹*(p.val.1*F y-Real.log (∫ z : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,z)).toReal))
    let M := fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) =>
      if x ∈ shortFineEvent p n m η κ then hessianMatrix F x.val+
        IntervalBoundary.internalMatrix ((n : ℕ)+m).succPNat n (by simp; omega)
          (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x) else 1
    let H := fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) =>
      if x ∈ shortFineEvent p n m η κ then hessianMatrix K x.val else 1
    let g : ComponentGeometry (Fin (n : ℕ)) := Sum.inl
      ⟨fun i => (i.val : ℤ), fun _ _ hij => Fin.ext (Int.ofNat_inj.mp hij)⟩
    (∀ ν : Measure (AffineSimplex.chartDomain n ((n+m : ℕ)+1)),
      SummableCoerciveMatrix (ρ := ν) ⟨s,hs⟩ n η C q g M) ∧
    (∀ i j, Measurable (fun x => H x i j)) ∧ (∀ x i j, H x i j = H x j i) ∧
    ∀ x (z : Fin (n : ℕ) → ℝ),
      (C*(n : ℝ)^(q*η))⁻¹*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*H x i j*z j ∧
      (∑ i, ∑ j, z i*H x i j*z j) ≤ C*(n : ℝ)^(q*η)*(∑ i, z i^2) := by
  let q := max (s+2) (max 4 κ)
  have hqs : s+2 ≤ q := le_max_left _ _
  have hq4 : 4 ≤ q := (le_max_left _ _).trans (le_max_right _ _)
  have hqκ : κ ≤ q := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨q, by linarith, ?_⟩
  intro θ
  obtain ⟨Cp,hCp,hpen⟩ := short_fine_penalty_internal θ
  let S := 2*∑' k : ℕ, (1+(k : ℝ))^(-s)
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  let C := 2+Cp+2*(S+1)
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro p hp n m hhalf ε η hε hεη F K M H g
  have hps : 1 < p.val.2 := hp ▸ hs
  have hn : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hη : 0 < η := hε.trans_le hεη
  have hpen' (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1))
      (hx : x ∈ shortFineEvent p n m η κ) (i j) :
      |hessianMatrix F x.val i j| ≤ if i = j then Cp*(n : ℝ)^(4*η) else 0 :=
    short_independent_penalty_internal p n m θ ε η κ Cp
      (fun y hy k l => hpen p n m ε η κ hε.le hη.le y hy k l) x hx i j
  obtain ⟨hmH,hmM,hsH,hsM⟩ :=
    short_independent_measurable_symmetric_internal p n m θ ε η κ hps hε
  have hpower (a : ℝ) (ha : a ≤ q) : (n : ℝ)^(a*η) ≤ (n : ℝ)^(q*η) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (mul_le_mul_of_nonneg_right ha hη.le)
  have hpow1 : 1 ≤ (n : ℝ)^(q*η) := Real.one_le_rpow hn1 (by nlinarith)
  have hlower : (C*(n : ℝ)^(q*η))⁻¹ ≤ (n : ℝ)^(-(p.val.2+2)*η) := by
    rw [mul_inv, ← Real.rpow_neg hn.le, hp]
    calc
      _ ≤ 1*(n : ℝ)^(-(s+2)*η) := mul_le_mul (inv_le_one_of_one_le₀ hC)
        (Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith only [hqs, hη.le]))
        (by positivity) zero_le_one
      _ = _ := one_mul _
  have hentry (x) (i j) : |M x i j| ≤ C*(n : ℝ)^(q*η)*
      (1+|(i.val : ℝ)-(j.val : ℝ)|)^(-s) := by
    have hb := short_independent_internal_entries_internal p n m θ ε η κ hhalf
      Cp hCp.le hpen' x i j
    rw [hp] at hb
    apply hb.trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
    have hp4 := mul_le_mul_of_nonneg_left (hpower 4 hq4) hCp.le
    have hpk := hpower κ hqκ
    have hC' : 2+Cp ≤ C := by dsimp only [C]; linarith
    nlinarith only [hp4, hpk, hpow1,
      mul_le_mul_of_nonneg_right hC' (by positivity : 0 ≤ (n : ℝ)^(q*η))]
  refine ⟨fun ν => ⟨hmM, ae_of_all _ fun x => ⟨hsM x, fun z => ?_, fun i j => ?_⟩⟩,
    hmH, hsH, fun x z => ⟨?_, ?_⟩⟩
  · exact (mul_le_mul_of_nonneg_right hlower (Finset.sum_nonneg fun i _ => sq_nonneg _)).trans
      (short_independent_internal_lower_internal p n m θ ε η κ hps
        (by have := n.pos; omega) hη.le x z)
  · simpa only [componentDistance, g, Function.Embedding.coeFn_mk, Int.cast_natCast] using hentry x i j
  · have hphysical : (n : ℝ)^(-(p.val.2+2)*η) ≤ (n : ℝ)^(-(p.val.2+2)*ε) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith [p.property.2.1])
    exact (mul_le_mul_of_nonneg_right (hlower.trans hphysical)
      (Finset.sum_nonneg fun i _ => sq_nonneg _)).trans
        (short_independent_physical_lower_internal p n m θ ε η κ hps hε x z)
  · have hb := short_independent_physical_upper_internal p n m θ ε η κ hps hε Cp hCp.le hpen' x z
    rw [hp] at hb
    apply hb.trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun i _ => sq_nonneg _)
    have hp4 := mul_le_mul_of_nonneg_left (hpower 4 hq4) hCp.le
    have hpk := mul_le_mul_of_nonneg_right (hpower κ hqκ) (by positivity : 0 ≤ 2*(S+1))
    change 1+Cp*(n : ℝ)^(4*η)+2*(n : ℝ)^(κ*η)*(S+1) ≤ C*(n : ℝ)^(q*η)
    dsimp only [C]
    nlinarith only [hp4, hpk, hpow1]

/-- See the proof of Lemma 6.5 in the paper: global absolute entry
envelope for the short physical marginal, with the actual two-sided
penalty at epsilon and the arbitrary envelope exponent C0. -/
theorem short_physical_entry_envelope_internal (p : Parameters) (hs : 1 < p.val.2)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε C₀ : ℝ) (hε : 0 < ε) :
    let F := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      ∑ i, (θ.val (((n : ℝ)^ε)⁻¹*y i)+θ.val (((n : ℝ)^ε)⁻¹*(y i)⁻¹))
    let K := fun y => p.val.1⁻¹*(p.val.1*F y-Real.log (∫ z : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,z)).toReal))
    ∀ x : AffineSimplex.chartDomain n ((n+m : ℕ)+1), ∀ i j,
      |(p.val.1 • hessianMatrix K x.val) i j| ≤
        p.val.1*(n : ℝ)^(2-C₀)*shortEnvelope p n m θ ε C₀ x := by
  intro F K x i j
  have hK := (PhysicalFibres.active_marginal_curvature p hs n m n.pos
    (Equiv.refl _) θ ε hε true).1
  change ContDiffOn ℝ ∞ K (AffineSimplex.chartDomain n ((n+m : ℕ)+1)) at hK
  have hKx : ContDiffAt ℝ 2 K x.val :=
    (hK.contDiffAt ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds x.property)).of_le
      (by norm_num)
  have hb : |hessianMatrix K x.val i j| ≤ (n : ℝ)^(2-C₀)*shortEnvelope p n m θ ε C₀ x := by
    rw [hessianMatrix_entry hKx]
    have h₁ := (fderiv ℝ (fderiv ℝ K) x.val (EuclideanSpace.single j 1)).unit_le_opNorm
      (EuclideanSpace.single i 1) (show ‖EuclideanSpace.single i (1 : ℝ)‖ ≤ 1 by simp)
    have h₂ := (fderiv ℝ (fderiv ℝ K) x.val).unit_le_opNorm
      (EuclideanSpace.single j 1) (show ‖EuclideanSpace.single j (1 : ℝ)‖ ≤ 1 by simp)
    exact (h₁.trans h₂).trans (marginal_hessian_envelope p n m θ ε C₀ hε x)
  simpa only [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos p.property.1, mul_assoc] using
    mul_le_mul_of_nonneg_left hb p.property.1.le

/-- See the proof of Lemma 6.5 in the paper: normal energy for the
actual short retained law, preserving its finite conditional remainder.
The good-event contraction is a hypothesis for the column estimates. The exceptional contraction is proved here. -/
theorem short_retained_normal_energy_internal
    (p : Parameters) (hs : 1 < p.val.2) (n m : ℕ)
    (θ : PhysicalCutoff) (ε C₀ η κ : ℝ) (hε : 0 < ε)
    (L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ))
    (he : shortRemainder p n m θ ε C₀ η κ L ≠ (∞ : ℝ≥0∞)) :
    let ν := retainedKernel p n m θ ε L
    let F := fun y : EuclideanSpace ℝ (Fin (n+1)) =>
      ∑ i, (θ.val (((n+1 : ℝ)^ε)⁻¹*y i)+θ.val (((n+1 : ℝ)^ε)⁻¹*(y i)⁻¹))
    let K := fun y => p.val.1⁻¹*(p.val.1*F y-Real.log (∫ z : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p (n+1) m (Equiv.refl _) (y,z)).toReal))
    let H := fun x : AffineSimplex.chartDomain (n+1) ((n+1+m : ℕ)+1) =>
      p.val.1 • hessianMatrix K x.val
    ∀ (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
      (hH : ∀ᵐ x ∂ν, (H x).PosSemidef) (S : Q.1)
      (r : MatrixEnergy.Natural Q hQ H ⊤ hH),
      (∀ i, MatrixEnergy.tuple Q hQ H ⊤ hH r i = (n+1 : ℝ)⁻¹ • S) →
    ∀ (T B : ℝ), 0 ≤ T → (∀ᵐ x ∂ν, |S.val x| ≤ B) →
      (∀ᵐ x ∂ν.restrict (shortFineEvent p n.succPNat m η κ),
        (∑ i, ∑ j, H x i j) ≤ T) →
    MatrixEnergy.weakForm Q hQ H ⊤ hH r r ≤
      (n+1 : ℝ)⁻¹*Q.2 S S+(n+1 : ℝ)⁻¹^2*
        (T*‖S.val‖^2+B^2*(p.val.1*(n+1 : ℝ)^4*(n+1 : ℝ)^(-C₀)*
          (shortRemainder p n m θ ε C₀ η κ L).toReal)) := by
  intro ν F K H Q hQ hH S r hr T B hT hSB hgood
  have hK := (PhysicalFibres.active_marginal_curvature p hs (n+1) m (by omega)
    (Equiv.refl _) θ ε hε true).1
  have hK' : ContDiffOn ℝ ∞ K (AffineSimplex.chartDomain (n+1) ((n+1+m : ℕ)+1)) := by
    simpa only [K, F, Nat.cast_add, Nat.cast_one, ite_true] using hK
  have hm (i j : Fin (n+1)) : Measurable (fun x => H x i j) :=
    (measurable_hessianMatrix (AffineSimplex.isOpen_chartDomain _ _) hK' i j).const_mul p.val.1
  have hW := measurable_shortEnvelope p n.succPNat m θ ε C₀
  have hW0 (x) : 0 ≤ shortEnvelope p n.succPNat m θ ε C₀ x :=
    (Real.rpow_nonneg (by positivity) C₀).trans (shortEnvelope_lower p n.succPNat m θ ε C₀ x)
  have hbad : ∀ᵐ x ∂ν.restrict (shortFineEvent p n.succPNat m η κ)ᶜ,
      |∑ i, ∑ j, H x i j| ≤ p.val.1*(n+1 : ℝ)^4*(n.succPNat : ℝ)^(-C₀)*
        shortEnvelope p n.succPNat m θ ε C₀ x := by
    apply ae_of_all
    intro x
    calc
      _ ≤ ∑ i, ∑ j, |H x i j| := (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i : Fin (n+1), ∑ _j : Fin (n+1),
          p.val.1*(n+1 : ℝ)^(2-C₀)*shortEnvelope p n.succPNat m θ ε C₀ x :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          simpa only [H, K, F, Nat.succPNat_coe, Nat.cast_succ] using
            short_physical_entry_envelope_internal p hs n.succPNat m θ ε C₀ hε x i j
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.succPNat_coe, Nat.cast_succ]
        rw [show (n+1 : ℝ)^(2-C₀) = (n+1 : ℝ)^2*(n+1 : ℝ)^(-C₀) by
          rw [show 2-C₀ = 2+(-C₀) by ring, Real.rpow_add (by positivity), Real.rpow_two]]
        ring
  simpa only [ν, shortRemainder, retainedExceptionalMass,
    Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using
    conditional_normal_energy_internal Q hQ n.succPNat H hm hH S r
      (by simpa only [Nat.succPNat_coe, Nat.cast_succ] using hr) _ hW hW0 _
      (measurableSet_shortFineEvent p hs n.succPNat m θ η κ) he T B
      (p.val.1*(n+1 : ℝ)^4) C₀ hT hSB hgood hbad

/-- See Subsection 4.5 of the paper, general same-form comparison: symmetric
quadratic bounds and a summable coercive matrix suffice. Positivity and
bounded coefficient operators are conclusions of these bounds. -/
theorem short_scaled_source_comparison_internal {X : Type*} [MeasurableSpace X] {ν : Measure X}
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (s : ShortExponent) (n : ℕ+) (η A q β : ℝ) (hβ : 0 < β)
    (g : ComponentGeometry (Fin (n : ℕ)))
    (H M : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (hM : SummableCoerciveMatrix (ρ := ν) s n η A q g M)
    (hHm : ∀ i j, Measurable (fun x => H x i j))
    (hHs : ∀ᵐ x ∂ν, ∀ i j, H x i j = H x j i)
    (hB : 1 ≤ A*(n : ℝ)^(q*η))
    (hHb : ∀ᵐ x ∂ν, ∀ z : Fin (n : ℕ) → ℝ,
      (A*(n : ℝ)^(q*η))⁻¹*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*H x i j*z j ∧
      (∑ i, ∑ j, z i*H x i j*z j) ≤ (A*(n : ℝ)^(q*η))*(∑ i, z i^2))
    (f : Fin (n : ℕ) → Lp ℝ 2 ν) (u v : Fin (n : ℕ) → Q.1)
    (hu : WeightedWeakSolution Q (fun x => β • H x) ⊤ f u)
    (hv : WeightedWeakSolution Q (fun x => β • M x) ⊤ f v)
    (gg : Fin (n : ℕ) → Lp ℝ 2 ν)
    (hgg : ∀ᵐ x ∂ν, ∀ i, gg i x = ∑ j, (H x-M x) i j*(v j).val x) :
    ‖WithLp.toLp 2 (fun i => (u i-v i).val)‖+
      Real.sqrt (∑ i, Q.2 (u i-v i) (u i-v i)) ≤
      2*(1+β⁻¹)*(A*(n : ℝ)^(q*η))*β*‖WithLp.toLp 2 gg‖ := by
  let B := A*(n : ℝ)^(q*η)
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hHlow : ∀ᵐ x ∂ν, (∀ i j, H x i j = H x j i) ∧
      ∀ z : Fin (n : ℕ) → ℝ, B⁻¹*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*H x i j*z j := by
    filter_upwards [hHb,hHs] with x hx hy
    exact ⟨hy,fun z => (hx z).1⟩
  have hMlow : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
      ∀ z : Fin (n : ℕ) → ℝ, B⁻¹*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*M x i j*z j :=
    hM.2.mono fun x hx => ⟨hx.1,hx.2.1⟩
  have hHp := AbstractEnergy.scaled_posSemidef (ρ := ν) β B⁻¹ hβ.le
    (by positivity) H hHlow
  have hMp := AbstractEnergy.scaled_posSemidef (ρ := ν) β B⁻¹ hβ.le
    (by positivity) M hMlow
  have hHb' : ∃ b : ℝ, ∀ᵐ x ∂ν, ∀ i j, |H x i j| ≤ b := by
    refine ⟨B, ?_⟩
    filter_upwards [hHs,hHb] with x hx hy i j
    exact DecayShort.PhysicalComparison.internal_entry_bound (H x) B hx
      (fun z => (mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg _)).trans
        (hy z).1) (fun z => (hy z).2) i j
  have hMb : ∃ b : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ b := by
    refine ⟨B, hM.2.mono fun x hx i j => (hx.2.2 i j).trans ?_⟩
    apply mul_le_of_le_one_right hB0.le
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by linarith [ComponentGeometryBounds.nonneg g i j]) (by linarith [s.property])
  have hscaled (T : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
      (ht : ∃ b : ℝ, ∀ᵐ x ∂ν, ∀ i j, |T x i j| ≤ b) :
      ∃ b : ℝ, ∀ᵐ x ∂ν, ∀ i j, |(β • T x) i j| ≤ b := by
    obtain ⟨b,hb⟩ := ht
    refine ⟨β*b,hb.mono fun x hx i j => ?_⟩
    simpa only [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hβ] using
      mul_le_mul_of_nonneg_left (hx i j) hβ.le
  have hHa : ∀ᵐ x ∂ν, ∀ z : Fin (n : ℕ) → ℝ,
      (β*B⁻¹)*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*(β • H x) i j*z j := by
    filter_upwards [hHb] with x hx z
    simpa only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc, mul_left_comm] using
      mul_le_mul_of_nonneg_left (hx z).1 hβ.le
  let ggβ := fun i => β • gg i
  have hggβ : ∀ᵐ x ∂ν, ∀ i, ggβ i x = ∑ j,
      ((β • H x) i j-(β • M x) i j)*(v j).val x := by
    filter_upwards [hgg,ae_all_iff.mpr fun i => Lp.coeFn_smul β (gg i)] with x hx hsc i
    rw [hsc i]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hx i]
    simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Finset.mul_sum, sub_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hgn : ‖WithLp.toLp 2 ggβ‖ = β*‖WithLp.toLp 2 gg‖ := by
    change ‖β • WithLp.toLp 2 gg‖ = _
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hβ]
  have he := DecayShort.PhysicalComparison.internal_common_form_comparison Q hQ
    (fun x => β • H x) (fun x => β • M x)
    (AbstractEnergy.scaled_measurable _ H hHm)
    (AbstractEnergy.scaled_measurable _ M hM.1)
    (hscaled H hHb') (hscaled M hMb) hHp hMp (β*B⁻¹) (by positivity) hHa
    f u v hu hv ggβ hggβ
  have hmin : (min 1 (β*B⁻¹))⁻¹ ≤ (1+β⁻¹)*B := by
    by_cases h : 1 ≤ β*B⁻¹
    · rw [min_eq_left h,inv_one]
      nlinarith [mul_nonneg (inv_nonneg.mpr hβ.le) hB0.le]
    · rw [min_eq_right (le_of_not_ge h),mul_inv_rev,inv_inv]
      nlinarith [inv_nonneg.mpr hβ.le]
  rw [hgn] at he
  exact he.trans (by
    dsimp only [B] at hmin
    nlinarith only [mul_le_mul_of_nonneg_right hmin
      (by positivity : 0 ≤ 2*(β*‖WithLp.toLp 2 gg‖))])


/-- See the proof of Lemma 6.5 in the paper, short use of Subsection 4.5:
construct the internal solution with its value, sum and mean-gradient bounds.
All polynomial degrees precede both exponents and temperature. Compact-temperature
prefactors precede the volumes and fibre law. -/
theorem short_independent_auxiliary_internal (s : ℝ) (hs : 1 < s)
    (κ : ℝ) (_hκ : 0 ≤ κ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ (θ : PhysicalCutoff) (ε η : ℝ), 0 < ε → ε ≤ η →
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∃ C : ℝ, 1 ≤ C ∧
    ∀ (p : Parameters), p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
    ∀ (n : ℕ+) (m : ℕ), 4 ≤ (n : ℕ)+m+1 → 2*(n : ℕ) ≤ (n : ℕ)+m+1 →
    let F := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      ∑ i, (θ.val (((n : ℝ)^ε)⁻¹*y i)+θ.val (((n : ℝ)^ε)⁻¹*(y i)⁻¹))
    let K := fun y => p.val.1⁻¹*(p.val.1*F y-Real.log (∫ z : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,z)).toReal))
    let M := fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) =>
      if x ∈ shortFineEvent p n m η κ then hessianMatrix F x.val+
        IntervalBoundary.internalMatrix ((n : ℕ)+m).succPNat n (by simp; omega)
          (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x) else 1
    let _H := fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) =>
      if x ∈ shortFineEvent p n m η κ then hessianMatrix K x.val else 1
    ∀ (ν : Measure (AffineSimplex.chartDomain n ((n+m : ℕ)+1))) [IsProbabilityMeasure ν]
      (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
    ∀ i₀ : Fin (n : ℕ), (n : ℝ)/4 ≤ (i₀.val : ℝ)+1 →
      (i₀.val : ℝ)+1 ≤ 3*(n : ℝ)/4 → ∀ χ : Lp ℝ 2 ν,
    (∃! v : Fin (n : ℕ) → Q.1, WeightedWeakSolution Q (fun x => p.val.1 • M x) ⊤
      (fun i => if i=i₀ then χ else 0) v) ∧
    (∀ v : Fin (n : ℕ) → Q.1, WeightedWeakSolution Q (fun x => p.val.1 • M x) ⊤
      (fun i => if i=i₀ then χ else 0) v →
      (∀ j, ‖(v j).val‖ ≤ C*(n : ℝ)^(r*η)*
        (1+|(j.val : ℝ)-(i₀.val : ℝ)|)^(-s)*‖χ‖) ∧
      ((∑ j, ‖(v j).val‖)+Real.sqrt (Q.2 (∑ j, v j) (∑ j, v j)) ≤ C*(n : ℝ)^(r*η)*‖χ‖) ∧
      (‖(∑ j, v j : Q.1).val‖+Real.sqrt (Q.2 (∑ j, v j) (∑ j, v j)) ≤ C*(n : ℝ)^(r*η)*‖χ‖)) := by
  obtain ⟨q,hq,hmat⟩ := short_independent_matrix_bounds_internal s hs κ
  obtain ⟨r,hr,haux⟩ := FixedLengthDecay.short_auxiliary_estimates_internal ⟨s,hs⟩ q hq
  refine ⟨r, hr, ?_⟩
  intro θ ε η hε hεη βlo βhi hlo hle
  obtain ⟨Cm,hCm,hmat⟩ := hmat θ
  obtain ⟨C,hC,haux⟩ := haux η (hε.trans_le hεη) Cm hCm βlo βhi hlo hle
  refine ⟨C,hC,?_⟩
  intro p hp hpl hph n m _hN hhalf F K M _H ν _ Q hQ hcons i₀ _hi₀ _hj₀ χ
  let g : ComponentGeometry (Fin (n : ℕ)) := Sum.inl
    ⟨fun i => (i.val : ℤ),fun _ _ hij => Fin.ext (Int.ofNat_inj.mp hij)⟩
  have hM := (hmat p hp n m hhalf ε η hε hεη).1 ν
  have hh := haux p.val.1 ⟨hpl,hph⟩ n _ _ ν Q hQ hcons g M hM i₀ χ
  refine ⟨hh.1,fun v hv => ?_⟩
  obtain ⟨hvp,hvs,hvm⟩ := hh.2 v hv
  refine ⟨fun j => ?_,hvs,hvm⟩
  simpa only [componentDistance, g, Function.Embedding.coeFn_mk, Int.cast_natCast] using hvp j

/-- See the proof of Lemma 6.5 in the paper, short use of Subsection 4.5:
compare the two physical-at-epsilon equations using the internal
source profile. This internal helper derives the residual estimate and the
comparison. The preceding theorem constructs the required internal profile. -/
theorem short_independent_comparison_internal (s : ℝ) (hs : 1 < s)
    (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ (θ : PhysicalCutoff) (ε η : ℝ), 0 < ε → ε ≤ η →
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∃ C : ℝ, 1 ≤ C ∧
    ∀ (p : Parameters), p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
    ∀ (n : ℕ+) (m : ℕ), 4 ≤ (n : ℕ)+m+1 → 2*(n : ℕ) ≤ (n : ℕ)+m+1 →
    let F := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      ∑ i, (θ.val (((n : ℝ)^ε)⁻¹*y i)+θ.val (((n : ℝ)^ε)⁻¹*(y i)⁻¹))
    let K := fun y => p.val.1⁻¹*(p.val.1*F y-Real.log (∫ z : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,z)).toReal))
    let M := fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) =>
      if x ∈ shortFineEvent p n m η κ then hessianMatrix F x.val+
        IntervalBoundary.internalMatrix ((n : ℕ)+m).succPNat n (by simp; omega)
          (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x) else 1
    let H := fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) =>
      if x ∈ shortFineEvent p n m η κ then hessianMatrix K x.val else 1
    ∀ (ν : Measure (AffineSimplex.chartDomain n ((n+m : ℕ)+1)))
      (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q →
    ∀ (i₀ : Fin (n : ℕ)), (n : ℝ)/4 ≤ (i₀.val : ℝ)+1 →
      (i₀.val : ℝ)+1 ≤ 3*(n : ℝ)/4 →
    ∀ (χ : Lp ℝ 2 ν) (V : ℝ), 0 ≤ V → ∀ u v : Fin (n : ℕ) → Q.1,
      WeightedWeakSolution Q (fun x => p.val.1 • H x) ⊤
        (fun i => if i=i₀ then χ else 0) u →
      WeightedWeakSolution Q (fun x => p.val.1 • M x) ⊤
        (fun i => if i=i₀ then χ else 0) v →
      (∀ j, ‖(v j).val‖ ≤ V*(1+|(j.val : ℝ)-(i₀.val : ℝ)|)^(-s)) →
      ‖WithLp.toLp 2 (fun i => (u i-v i).val)‖+
        Real.sqrt (∑ i, Q.2 (u i-v i) (u i-v i)) ≤
        C*(n : ℝ)^(r*η)*V*((n : ℝ)^(-(s-1/2))+
          (((n : ℕ)+m+1 : ℕ) : ℝ)^(-(1/2 : ℝ))) := by
  obtain ⟨q,hq,hmat⟩ := short_independent_matrix_bounds_internal s hs κ
  refine ⟨q+κ,add_nonneg hq hκ,?_⟩
  intro θ ε η hε hεη βlo βhi hlo hle
  obtain ⟨Cm,hCm,hmat⟩ := hmat θ
  obtain ⟨Cg,hCg,hres⟩ := DecayShort.PhysicalDecay.internal_residual_profile_compact
    s βlo βhi hs hlo hle
  have hβhi : 0 < βhi := hlo.trans_le hle
  let C := 1+2*(1+βlo⁻¹)*Cm*βhi*Cg
  have hC : 1 ≤ C := by
    dsimp only [C]
    have : 0 ≤ 2*(1+βlo⁻¹)*Cm*βhi*Cg := by positivity
    linarith
  refine ⟨C,hC,?_⟩
  intro p hp hpl hph n m hN hhalf F K M H ν Q hQ i₀ hi₀ hj₀ χ V hV u v hu hv hprof
  have hβ : 0 < p.val.1 := p.property.1
  let g : ComponentGeometry (Fin (n : ℕ)) := Sum.inl
    ⟨fun i => (i.val : ℤ),fun _ _ hij => Fin.ext (Int.ofNat_inj.mp hij)⟩
  obtain ⟨hM,hmH,hsH,hHb⟩ := hmat p hp n m hhalf ε η hε hεη
  have hη : 0 < η := hε.trans_le hεη
  have hn : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hB : 1 ≤ Cm*(n : ℝ)^(q*η) := one_le_mul_of_one_le_of_one_le hCm
    (Real.one_le_rpow hn1 (mul_nonneg hq hη.le))
  obtain ⟨gg,hgg,hggn⟩ := hres p hp hpl hph n m hN hhalf θ η hη true
    ((n : ℝ)^(κ*η)) (by positivity) _ id measurable_id ν i₀ hi₀ hj₀ V hV
    (fun i => (v i).val) (by simpa only [hp] using hprof)
  have hdefect : ∀ᵐ x ∂ν, ∀ i, gg i x = ∑ j, (H x-M x) i j*(v j).val x := by
    filter_upwards [hgg] with x hx i
    rw [short_independent_defect_internal p n m θ ε η κ x]
    exact hx i
  have he := short_scaled_source_comparison_internal Q hQ ⟨s,hs⟩ n η Cm q p.val.1
    p.property.1 g H M (hM ν) hmH (ae_of_all _ hsH) hB (ae_of_all _ hHb)
    _ u v hu hv gg hdefect
  have hβinv : p.val.1⁻¹ ≤ βlo⁻¹ := (inv_le_inv₀ p.property.1 hlo).mpr hpl
  apply he.trans
  calc
    _ ≤ 2*(1+βlo⁻¹)*(Cm*(n : ℝ)^(q*η))*βhi*
        (Cg*(n : ℝ)^(κ*η)*V*((n : ℝ)^(-(p.val.2-1/2))+
          (((n : ℕ)+m+1 : ℕ) : ℝ)^(-(1/2 : ℝ)))) := by
      apply mul_le_mul
      · gcongr
      · exact hggn
      · exact norm_nonneg _
      · positivity
    _ = (2*(1+βlo⁻¹)*Cm*βhi*Cg)*(n : ℝ)^((q+κ)*η)*V*
        ((n : ℝ)^(-(s-1/2))+(((n : ℕ)+m+1 : ℕ) : ℝ)^(-(1/2 : ℝ))) := by
      rw [show (n : ℝ)^((q+κ)*η) = (n : ℝ)^(q*η)*(n : ℝ)^(κ*η) by
        rw [← Real.rpow_add hn]; congr 1; ring, hp]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hV
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      dsimp only [C]
      linarith

/-- See the proof of Lemma 6.5 in the paper: transfer the component
sum and its scalar-form gradient through the two-matrix comparison. -/
theorem short_auxiliary_mean_transfer_internal {X : Type*} [MeasurableSpace X]
    {ν : Measure X} (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (n : ℕ+) (u v : Fin (n : ℕ) → Q.1) :
    (∑ i, ‖(u i).val‖)+Real.sqrt (Q.2 (∑ i, u i) (∑ i, u i)) ≤
      (∑ i, ‖(v i).val‖)+Real.sqrt (Q.2 (∑ i, v i) (∑ i, v i))+
        2*Real.sqrt (n : ℝ)*(‖WithLp.toLp 2 (fun i => (u i-v i).val)‖+
          Real.sqrt (∑ i, Q.2 (u i-v i) (u i-v i))) := by
  let d := fun i => u i-v i
  have hs : (∑ i, u i : Q.1) = (∑ i, v i)+(∑ i, d i) := by
    simp only [d, Finset.sum_sub_distrib]
    abel
  have he (i) : (u i).val = (v i).val+(d i).val := by
    change (u i).val = (v i).val+((u i).val-(v i).val)
    abel
  have hvalue : (∑ i, ‖(u i).val‖) ≤ (∑ i, ‖(v i).val‖)+
      Real.sqrt (n : ℝ)*‖WithLp.toLp 2 (fun i => (d i).val)‖ := by
    have hc := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : Fin (n : ℕ) => (1 : ℝ))
      (fun i => ‖(d i).val‖)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at hc
    have hnval : ‖WithLp.toLp 2 (fun i => (d i).val)‖^2 = ∑ i, ‖(d i).val‖^2 :=
      by rw [PiLp.norm_sq_eq_of_L2]
    rw [← hnval,Real.sqrt_sq (norm_nonneg _)] at hc
    calc
      _ ≤ ∑ i, (‖(v i).val‖+‖(d i).val‖) := Finset.sum_le_sum fun i _ => by
        rw [he i]
        exact norm_add_le _ _
      _ ≤ _ := by rw [Finset.sum_add_distrib]; linarith only [hc]
  let D := (ScalarFormHalfGenerator.halfGenerator Q hQ).toLinearMap.comp
    (ScalarFormHilbert.equiv Q hQ).symm.toLinearMap
  have hnorm (w : Q.1) : ‖D w‖ = Real.sqrt (Q.2 w w) :=
    ScalarFormHalfGenerator.halfGenerator_norm Q hQ w
  have hgrad : Real.sqrt (Q.2 (∑ i, u i) (∑ i, u i)) ≤
      Real.sqrt (Q.2 (∑ i, v i) (∑ i, v i))+
        Real.sqrt (n : ℝ)*Real.sqrt (∑ i, Q.2 (d i) (d i)) := by
    have hc := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : Fin (n : ℕ) => (1 : ℝ))
      (fun i => Real.sqrt (Q.2 (d i) (d i)))
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, Real.sq_sqrt (hQ.2.2.1 _)] at hc
    rw [← hnorm,hs,map_add]
    apply (norm_add_le _ _).trans
    rw [hnorm]
    apply add_le_add le_rfl
    rw [map_sum]
    exact (norm_sum_le _ _).trans ((Finset.sum_congr rfl fun i _ => hnorm (d i)).le.trans hc)
  have hn : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hv : 0 ≤ ‖WithLp.toLp 2 (fun i => (d i).val)‖ := norm_nonneg _
  have hg : 0 ≤ Real.sqrt (∑ i, Q.2 (d i) (d i)) := Real.sqrt_nonneg _
  dsimp only [d] at hvalue hgrad hv hg
  nlinarith only [hvalue,hgrad,mul_nonneg hn hv,mul_nonneg hn hg]

/-- See the proof of Lemma 6.5 in the paper: square the conditional
physical/cutoff comparison before fixing C0. Exceptional coefficients
remain `n^(b-C0)` times the conditional remainder, with no unconditional
tail substituted and no square of the envelope required. -/
theorem short_conditional_square_internal {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsProbabilityMeasure ν]
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q) (n : ℕ+)
    (H M : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (hHm : ∀ i j, Measurable (fun x => H x i j))
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hMb : ∃ K : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ K)
    (hH : ∀ᵐ x ∂ν, (H x).PosSemidef) (hM : ∀ᵐ x ∂ν, (M x).PosSemidef)
    (a0 loss K0 D0 D b C₀ : ℝ) (ha0 : 0 < a0) (hloss : 0 ≤ loss)
    (hK0 : 0 ≤ K0) (hD0 : 0 ≤ D0) (hD : 0 ≤ D)
    (hHa : ∀ᵐ x ∂ν, (∀ i j, H x i j = H x j i) ∧ ∀ z : Fin (n : ℕ) → ℝ,
      (a0*(n : ℝ)^(-loss))*(∑ i,z i^2) ≤ ∑ i,∑ j,z i*H x i j*z j)
    (hMa : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧ ∀ z : Fin (n : ℕ) → ℝ,
      (a0*(n : ℝ)^(-loss))*(∑ i,z i^2) ≤ ∑ i,∑ j,z i*M x i j*z j)
    (W : X → ℝ) (hW : Measurable W) (hW0 : ∀ x, 0 ≤ W x)
    (G : Set X) (hG : MeasurableSet G)
    (he : (∫⁻ x in Gᶜ, ENNReal.ofReal (W x) ∂ν) ≠ (∞ : ℝ≥0∞))
    (heq : ∀ᵐ x ∂ν, x ∈ G → H x = M x)
    (hdefect : ∀ᵐ x ∂ν.restrict Gᶜ, ∀ i j,
      |H x i j-M x i j| ≤ D*(n : ℝ)^(b-C₀)*W x)
    (hgood : ∀ᵐ x ∂ν.restrict G, (∑ i,∑ j,H x i j) ≤ K0*(n : ℝ)^(loss+1))
    (hbad : ∀ᵐ x ∂ν.restrict Gᶜ,
      |∑ i,∑ j,H x i j| ≤ D*(n : ℝ)^(b-C₀)*W x)
    (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν) (B : ℝ) (hB : 0 ≤ B)
    (hχ : ∀ᵐ x ∂ν, |χ x| ≤ B) (ψ u : Fin (n : ℕ) → Q.1)
    (hψ : WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ)))
      (fun i => if i=i₀ then χ else 0) ψ)
    (hu : WeightedWeakSolution Q M ⊤ (fun i => if i=i₀ then χ else 0) u)
    (hmean : ‖(∑ i,u i : Q.1).val‖ ≤ D0*(n : ℝ)^loss*‖χ‖)
    (hgrad : Real.sqrt (Q.2 (∑ i,u i) (∑ i,u i)) ≤ D0*(n : ℝ)^loss*‖χ‖) :
    let e := (∫⁻ x in Gᶜ, ENNReal.ofReal (W x) ∂ν).toReal
    ‖WithLp.toLp 2 (fun i => (ψ i).val-(u i).val)‖^2 ≤
      (3*((1+K0)*D0^2/a0+D0^2))*(n : ℝ)^(8*loss-1)*‖χ‖^2+
      (36*D*a0⁻¹^2/a0)*(n : ℝ)^(4+4*loss+b-C₀)*B^2*e := by
  intro e
  have hn : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  let a := a0*(n : ℝ)^(-loss)
  let S : Q.1 := ∑ i,u i
  let V := a⁻¹*B
  let U := 2*V+a⁻¹*B
  let E0 := D*(n : ℝ)^(b-C₀)*e
  let τ := (n : ℝ)^2*V*U*E0
  let R := (n : ℝ)⁻¹*Q.2 S S+(n : ℝ)⁻¹^2*
    ((K0*(n : ℝ)^(loss+1))*‖S.val‖^2+((n : ℝ)*V)^2*E0)
  have ha : 0 < a := by dsimp only [a]; positivity
  have hV : V = a0⁻¹*(n : ℝ)^loss*B := by
    dsimp only [V,a]
    rw [mul_inv,← Real.rpow_neg hn.le,neg_neg]
  have hU : U = (2*a0⁻¹+a0⁻¹)*(n : ℝ)^loss*B := by
    dsimp only [U]
    change 2*V+V = _
    rw [hV]
    ring
  have hE0 : 0 ≤ E0 := by dsimp only [E0,e]; positivity
  have hcomp := conditional_vector_comparison_internal Q hQ n H M hHm hMm hMb hH hM
    a a ha ha hHa hMa W hW hW0 G hG he heq D (C₀-b) (K0*(n : ℝ)^(loss+1))
    hD (by positivity)
    (by simpa only [neg_sub] using hdefect) hgood (by simpa only [neg_sub] using hbad)
    i₀ χ B hB hχ ψ u hψ hu
  have hτ : τ ≤ (n : ℝ)^2*(E0*((2*a0⁻¹+a0⁻¹)*(n : ℝ)^loss*B)*
      (a0⁻¹*(n : ℝ)^loss*B)) := by
    apply le_of_eq
    dsimp only [τ]
    rw [hV,hU]
    ring
  have hR : R ≤ (n : ℝ)⁻¹*Q.2 S S+K0*(n : ℝ)^(loss-1)*‖S.val‖^2+
      (n : ℝ)^4*E0*(a0⁻¹*(n : ℝ)^loss*B)^2 := by
    have heqR : R = (n : ℝ)⁻¹*Q.2 S S+K0*(n : ℝ)^(loss-1)*‖S.val‖^2+V^2*E0 := by
      dsimp only [R]
      rw [show loss+1 = loss+1 by rfl,Real.rpow_add hn,
        Real.rpow_one,show loss-1 = loss+(-1) by ring,Real.rpow_add hn,Real.rpow_neg_one]
      field_simp
      ring
    rw [heqR,hV]
    have hpow : 1 ≤ (n : ℝ)^4 := one_le_pow₀ hn1
    nlinarith only [mul_le_mul_of_nonneg_right hpow
      (mul_nonneg (sq_nonneg (a0⁻¹*(n : ℝ)^loss*B)) hE0)]
  have hh := FixedLengthDecay.short_comparison_square_uniform_internal loss a0 K0 D0 a0⁻¹ E0 0 1
    hloss ha0 hK0 hD0 (by positivity) hE0 X ν Q hQ n S ‖χ‖ B
    ‖WithLp.toLp 2 (fun i => (ψ i).val-(u i).val)‖ τ R (norm_nonneg _) hB
    (norm_nonneg _) (by dsimp only [τ]; rw [hV,hU]; positivity)
    (by dsimp only [R]; positivity [hQ.2.2.1 S]) hmean hgrad
    (by simpa only [neg_zero,zero_mul,Real.exp_zero,mul_one] using hτ)
    (by simpa only [neg_zero,zero_mul,Real.exp_zero,mul_one] using hR) ?_
  · apply hh.trans_eq
    simp only [neg_zero,zero_mul,Real.exp_zero,mul_one]
    dsimp only [E0]
    have hexp : (n : ℝ)^(4+4*loss+b-C₀) = (n : ℝ)^(b-C₀)*(n : ℝ)^(4+4*loss) := by
      rw [show 4+4*loss+b-C₀ = (b-C₀)+(4+4*loss) by ring,Real.rpow_add hn]
    rw [hexp]
    ring
  · simpa only [τ,R,E0,S,V,U,a,e,neg_sub,mul_assoc] using hcomp

/-- See the proof of Lemma 6.5 in the paper: the actual short physical
matrix and its independent fine-event cutoff have the exceptional
first-order envelope required by the squared comparison. The normal
contraction keeps its full cardinality cost until C0 is selected. -/
theorem short_physical_cutoff_defect_internal (p : Parameters) (hs : 1 < p.val.2)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε η κ C₀ : ℝ) (hε : 0 < ε) :
    let F := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      ∑ i, (θ.val (((n : ℝ)^ε)⁻¹*y i)+θ.val (((n : ℝ)^ε)⁻¹*(y i)⁻¹))
    let K := fun y => p.val.1⁻¹*(p.val.1*F y-Real.log (∫ z : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,z)).toReal))
    let H := fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) => p.val.1 • hessianMatrix K x.val
    let U := fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) =>
      p.val.1 • (if x ∈ shortFineEvent p n m η κ then hessianMatrix K x.val else 1)
    ∀ x : AffineSimplex.chartDomain n ((n+m : ℕ)+1),
      (∀ i j, |H x i j-U x i j| ≤ 2*p.val.1*(n : ℝ)^(4-C₀)*shortEnvelope p n m θ ε C₀ x) ∧
      |∑ i,∑ j,H x i j| ≤ 2*p.val.1*(n : ℝ)^(4-C₀)*shortEnvelope p n m θ ε C₀ x := by
  intro F K H U x
  have hn : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  let E := (n : ℝ)^(-C₀)*shortEnvelope p n m θ ε C₀ x
  have hE : 1 ≤ E := by
    have hh := mul_le_mul_of_nonneg_left (shortEnvelope_lower p n m θ ε C₀ x)
      (Real.rpow_nonneg hn.le (-C₀))
    rw [← Real.rpow_add hn,neg_add_cancel,Real.rpow_zero] at hh
    exact hh
  have hpow (a : ℝ) : (n : ℝ)^(a-C₀)*shortEnvelope p n m θ ε C₀ x = (n : ℝ)^a*E := by
    dsimp only [E]
    rw [show a-C₀ = a+(-C₀) by ring,Real.rpow_add hn,mul_assoc]
  have hb (i j) : |H x i j| ≤ p.val.1*(n : ℝ)^2*E := by
    have hh := short_physical_entry_envelope_internal p hs n m θ ε C₀ hε x i j
    change |H x i j| ≤ _ at hh
    rw [mul_assoc p.val.1, hpow 2, Real.rpow_two] at hh
    simpa only [mul_assoc] using hh
  have h24 : (n : ℝ)^2 ≤ (n : ℝ)^4 := by nlinarith [sq_nonneg ((n : ℝ)^2-1),one_le_pow₀ hn1 (n := 2)]
  have h2 : 1 ≤ (n : ℝ)^2 := one_le_pow₀ hn1
  have hβ : 0 < p.val.1 := p.property.1
  have h4 : (n : ℝ)^(4-C₀)*shortEnvelope p n m θ ε C₀ x = (n : ℝ)^4*E := by
    simpa only [Real.rpow_ofNat] using hpow 4
  constructor
  · intro i j
    by_cases hx : x ∈ shortFineEvent p n m η κ
    · simp only [H,U,hx,↓reduceIte,sub_self,abs_zero]
      have hW0 : 0 ≤ shortEnvelope p n m θ ε C₀ x :=
        (Real.rpow_nonneg hn.le C₀).trans (shortEnvelope_lower p n m θ ε C₀ x)
      positivity
    · have hU : |U x i j| ≤ p.val.1 := by
        dsimp only [U]
        rw [ite_eq_right hx]
        simp only [Matrix.smul_apply,smul_eq_mul,abs_mul,abs_of_pos hβ,Matrix.one_apply]
        split_ifs <;> simp only [abs_one,abs_zero,mul_one,mul_zero] <;> linarith
      calc
        _ ≤ |H x i j|+|U x i j| := abs_sub _ _
        _ ≤ p.val.1*(n : ℝ)^2*E+p.val.1 := add_le_add (hb i j) hU
        _ ≤ 2*p.val.1*(n : ℝ)^4*E := by
          nlinarith only [mul_le_mul_of_nonneg_left h2 hβ.le,
            mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ p.val.1*(n : ℝ)^2),
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h24 hβ.le) (by linarith : 0 ≤ E)]
        _ = _ := by nlinarith only [congrArg (fun t : ℝ => 2*p.val.1*t) h4]
  · calc
      _ ≤ ∑ i,∑ j,|H x i j| := (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i : Fin (n : ℕ), ∑ _j : Fin (n : ℕ), p.val.1*(n : ℝ)^2*E :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hb i j
      _ ≤ 2*p.val.1*(n : ℝ)^4*E := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        nlinarith only [show 0 ≤ p.val.1*(n : ℝ)^4*E by positivity]
      _ = _ := by nlinarith only [congrArg (fun t : ℝ => 2*p.val.1*t) h4]

/-- See the proof of Lemma 6.5 in the paper: transfer the squared
physical/full-cutoff error to the internal auxiliary field and absorb
the explicitly retained exceptional power into the final squared interface. -/
theorem short_square_transfer_internal {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (n : ℕ+) (loss b C₀ P A T D F B e : ℝ)
    (hloss : 0 ≤ loss) (hT : 0 ≤ T) (hD : 0 ≤ D) (hF : 0 ≤ F)
    (he : 0 ≤ e) (hC₀ : 4+4*loss+b+2*P ≤ C₀)
    (ψ u v : Fin (n : ℕ) → H)
    (hphysical : ‖WithLp.toLp 2 (fun i => ψ i-u i)‖^2 ≤
      A*(n : ℝ)^(8*loss-1)*F^2+T*(n : ℝ)^(4+4*loss+b-C₀)*B^2*e)
    (hcutoff : ‖WithLp.toLp 2 (fun i => u i-v i)‖ ≤ D*(n : ℝ)^(loss-1/2)*F) :
    ‖WithLp.toLp 2 (fun i => ψ i-v i)‖^2 ≤
      (2*A+2*D^2)*(n : ℝ)^(2*(4*loss)-1)*F^2+
        (2*T)*(n : ℝ)^(-2*P)*B^2*e := by
  have hn : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hcutoff
  have hpow : (D*(n : ℝ)^(loss-1/2)*F)^2 = D^2*(n : ℝ)^(2*loss-1)*F^2 := by
    rw [mul_pow,mul_pow,← Real.rpow_mul_natCast hn.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (loss-1/2)*(2 : ℝ) = 2*loss-1 by ring]
  rw [hpow] at hsq
  have hsq' : ‖WithLp.toLp 2 (fun i => u i-v i)‖^2 ≤
      D^2*(n : ℝ)^(8*loss-1)*F^2 := hsq.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)) (sq_nonneg D)) (sq_nonneg F))
  have ht : (n : ℝ)^(4+4*loss+b-C₀) ≤ (n : ℝ)^(-2*P) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have htail := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht hT) (sq_nonneg B)) he
  have hnorm : ‖WithLp.toLp 2 (fun i => ψ i-v i)‖ ≤
      ‖WithLp.toLp 2 (fun i => ψ i-u i)‖+‖WithLp.toLp 2 (fun i => u i-v i)‖ := by
    have hh : WithLp.toLp 2 (fun i => ψ i-v i) =
        WithLp.toLp 2 (fun i => ψ i-u i)+WithLp.toLp 2 (fun i => u i-v i) := by
      apply PiLp.ext
      intro i
      change ψ i-v i = (ψ i-u i)+(u i-v i)
      abel
    rw [hh]
    exact norm_add_le _ _
  have hnorm2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hnorm
  rw [show 2*(4*loss)-1 = 8*loss-1 by ring]
  nlinarith only [hphysical,hsq',htail,hnorm2,
    sq_nonneg (‖WithLp.toLp 2 (fun i => ψ i-u i)‖-‖WithLp.toLp 2 (fun i => u i-v i)‖)]

/-- See the proof of Lemma 6.5 and equation (6.23) of the paper:
both short fibre sums from the conditional physical comparison, the
independent two-matrix comparison and the internal value profile. -/
theorem short_fibre_sums_from_two_comparisons_internal {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (s : ℝ) (hs : 1 < s) (n : ℕ+) (i₀ : Fin (n : ℕ))
    (hi₀ : |(i₀.val : ℝ)+1-(n : ℝ)/2| ≤ (n : ℝ)/4)
    (loss b C₀ P A T D Dv F B e : ℝ)
    (hloss : 0 ≤ loss) (hA : 0 ≤ A) (hT : 0 ≤ T) (hD : 0 ≤ D) (hDv : 0 ≤ Dv)
    (hF : 0 ≤ F) (hB : 0 ≤ B) (he : 0 ≤ e)
    (hP : 1/2 ≤ P) (hC₀ : 4+4*loss+b+2*P ≤ C₀)
    (ψ u v : Fin (n : ℕ) → H)
    (hvalue : ∀ j, ‖v j‖ ≤ Dv*(n : ℝ)^(4*loss)*
      (1+(Nat.dist j.val i₀.val : ℝ))^(-s)*F)
    (hsum : (∑ j, ‖v j‖) ≤ Dv*(n : ℝ)^(4*loss)*F)
    (hphysical : ‖WithLp.toLp 2 (fun i => ψ i-u i)‖^2 ≤
      A*(n : ℝ)^(8*loss-1)*F^2+T*(n : ℝ)^(4+4*loss+b-C₀)*B^2*e)
    (hcutoff : ‖WithLp.toLp 2 (fun i => u i-v i)‖ ≤ D*(n : ℝ)^(loss-1/2)*F) :
    let K := 4*8^s+Real.sqrt 8
    let W := 2*∑' k : ℕ, (1+(k : ℝ))^(-(2*s-1))
    (∑ j, InteractionDifferential.boundaryWeight s n j*‖ψ j‖) ≤
      (K*Dv+Real.sqrt W*Real.sqrt (2*A+2*D^2))*(n : ℝ)^(4*loss-1/2)*F+
        Real.sqrt W*Real.sqrt (2*T)*B*Real.sqrt e ∧
    (∑ j, ‖ψ j‖) ≤ (Dv+Real.sqrt (2*A+2*D^2))*(n : ℝ)^(4*loss)*F+
      Real.sqrt (2*T)*B*Real.sqrt e := by
  exact conditional_short_fibre_sums_internal s hs n i₀ hi₀ Dv (2*A+2*D^2) (2*T)
    (4*loss) P F B e hDv (by positivity) (by positivity) hF hB he hP ψ v hvalue hsum
    (short_square_transfer_internal n loss b C₀ P A T D F B e hloss hT hD hF he hC₀
      ψ u v hphysical hcutoff)

/-- See the proof of Lemma 6.5 in the paper, short use of Subsection 4.5:
the full equation with the physical penalty at epsilon has a
unique unrestricted solution over the specified common scalar form. -/
theorem short_independent_full_solution_internal (p : Parameters) (hs : 1 < p.val.2)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε η κ : ℝ)
    (hε : 0 < ε) (hεη : ε ≤ η) (hhalf : 2*(n : ℕ) ≤ (n : ℕ)+m+1)
    (ν : Measure (AffineSimplex.chartDomain n ((n+m : ℕ)+1)))
    [IsProbabilityMeasure ν]
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q) (hcons : IsConservativeScalarForm Q)
    (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν) :
    let F := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      ∑ i, (θ.val (((n : ℝ)^ε)⁻¹*y i)+θ.val (((n : ℝ)^ε)⁻¹*(y i)⁻¹))
    let K := fun y => p.val.1⁻¹*(p.val.1*F y-Real.log (∫ z : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,z)).toReal))
    let H := fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) =>
      if x ∈ shortFineEvent p n m η κ then hessianMatrix K x.val else 1
    ∃! u : Fin (n : ℕ) → Q.1, WeightedWeakSolution Q (fun x => p.val.1 • H x) ⊤
      (fun i => if i=i₀ then χ else 0) u := by
  intro F K H
  obtain ⟨q,hq,hmat⟩ := short_independent_matrix_bounds_internal p.val.2 hs κ
  obtain ⟨C,hC,hmat⟩ := hmat θ
  obtain ⟨_,hmH,hsH,hHb⟩ := hmat p rfl n m hhalf ε η hε hεη
  let B := C*(n : ℝ)^(q*η)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le hC
    (Real.one_le_rpow hn1 (mul_nonneg hq (hε.trans_le hεη).le))
  have hB0 : 0 < B := zero_lt_one.trans_le hB
  have hbounds : ∀ᵐ x ∂ν, (∀ i j, H x i j = H x j i) ∧
      ∀ z : Fin (n : ℕ) → ℝ, B⁻¹*(∑ i,z i^2) ≤ ∑ i,∑ j,z i*H x i j*z j ∧
        (∑ i,∑ j,z i*H x i j*z j) ≤ B*(∑ i,z i^2) :=
    ae_of_all _ fun x => ⟨hsH x,hHb x⟩
  obtain ⟨_,_,_,hT⟩ := AbstractEnergy.illustrative_energy p.val.1 p.property.1 Q hQ hcons
    H hmH B⁻¹ B (inv_pos.mpr hB0) ((inv_le_one_of_one_le₀ hB).trans hB) hbounds ⊤
  obtain ⟨u,hu,huniq,_⟩ := hT (WithLp.toLp 2 (fun i => if i=i₀ then χ else 0))
  exact ⟨u,hu,huniq⟩

end Riesz2.LengthAveragingFibres
