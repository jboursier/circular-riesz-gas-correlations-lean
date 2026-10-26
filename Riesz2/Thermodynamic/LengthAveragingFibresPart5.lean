/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.LengthAveragingFibresPart4
public import Riesz2.DecayLong.PerturbationBoundsPart3

/-!
# Conditional marginal coefficient pairings

Pointwise and retained-law ingredients of the proof of Lemma 6.5. The physical penalty
exponent and the fine tolerance are independent. Exceptional terms use the conditional
envelope itself, retaining the factor `n^(-C₀)`.
-/

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Classical ContDiff Topology

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.LengthAveragingFibres

/-- See Subsection 6.3 and the proof of Lemma 6.5 of the paper: each literal
nonnegative coefficient is controlled by the unscaled long envelope on
the entire retained carrier. No conditional moment assumption is used. -/
theorem long_envelope_coefficients_internal
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (θ : PhysicalCutoff) (ε C₀ : ℝ)
    (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1)) :
    let E := (n : ℝ)^(-C₀)*longEnvelope β s n m θ ε C₀ x
    (∀ i j, GoodBlocks.conditionalHessian β s n m i j x ≤ E) ∧
      (∀ i, ConditionalForces.compensationB β s n m i x ≤ E) ∧
      ConditionalForces.compensationC β s n m x ≤ E ∧
      (∀ i j, |ConditionalForces.compensationQ β s n m i j x| ≤ 3*E) ∧
      (∀ i j l, |ConditionalForces.compensationQ β s n m i j x -
        ConditionalForces.compensationQ β s n m i l x| ≤ 2*E) := by
  intro E
  let P := ∑ i, ∑ j, GoodBlocks.conditionalHessian β s n m i j x
  let b := ∑ i, ConditionalForces.compensationB β s n m i x
  let c := ConditionalForces.compensationC β s n m x
  have hP : 0 ≤ P := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    GoodBlocks.conditionalHessian_nonneg β s n m i j x
  have hb : 0 ≤ b := Finset.sum_nonneg fun i _ =>
    ConditionalForces.compensationB_nonneg β s n m i x
  have hc : 0 ≤ c := ConditionalForces.compensationC_nonneg β s n m x
  have he : E = 1 + (∑ i, |InterpolationMatrix.penaltyHessian n θ ε x.val i i|) + P+b+c := by
    dsimp only [E, longEnvelope, P, b, c]
    rw [← mul_assoc, ← Real.rpow_add (by positivity : (0 : ℝ) < n),
      neg_add_cancel, Real.rpow_zero, one_mul]
  have hf := Finset.sum_nonneg (s := Finset.univ) fun i _ =>
    abs_nonneg (InterpolationMatrix.penaltyHessian n θ ε x.val i i)
  have hPi (i j) : GoodBlocks.conditionalHessian β s n m i j x ≤ P :=
    (Finset.single_le_sum (fun k _ => GoodBlocks.conditionalHessian_nonneg β s n m i k x)
      (Finset.mem_univ j)).trans (Finset.single_le_sum
        (fun k _ => Finset.sum_nonneg fun l _ =>
          GoodBlocks.conditionalHessian_nonneg β s n m k l x) (Finset.mem_univ i))
  have hbi (i) : ConditionalForces.compensationB β s n m i x ≤ b :=
    Finset.single_le_sum (fun j _ => ConditionalForces.compensationB_nonneg β s n m j x)
      (Finset.mem_univ i)
  have hpE : P ≤ E := by rw [he]; linarith
  have hbE : b ≤ E := by rw [he]; linarith
  have hcE : c ≤ E := by rw [he]; linarith
  refine ⟨fun i j => (hPi i j).trans hpE, fun i => (hbi i).trans hbE, hcE, ?_, ?_⟩
  · intro i j
    have hi := ConditionalForces.compensationB_nonneg β s n m i x
    have hj := ConditionalForces.compensationB_nonneg β s n m j x
    apply abs_le.mpr
    constructor <;> dsimp only [ConditionalForces.compensationQ] <;> linarith [hbi i, hbi j]
  · intro i j l
    rw [ConditionalForces.compensationQ_sub]
    apply (abs_sub _ _).trans
    rw [abs_of_nonneg (ConditionalForces.compensationB_nonneg β s n m l x),
      abs_of_nonneg (ConditionalForces.compensationB_nonneg β s n m j x)]
    linarith [hbi l, hbi j]

/-- See the proof of Lemma 6.5 in the paper: nonwrapping adjacent
compensation bounds telescope pointwise with the minimum endpoint depth.
This is the point-mass specialization of the moment telescope. -/
theorem depth_telescoping_internal (n : ℕ+) (f : Fin (n : ℕ) → ℝ)
    (M t : ℝ) (hM : 0 ≤ M) (ht : 0 ≤ t)
    (hf : ∀ k : Fin (n : ℕ), k.val+1 < (n : ℕ) →
      |f (k+1)-f k| ≤ M*(min (k.val+1) ((n : ℕ)-k.val) : ℕ)^(-t))
    (j l : Fin (n : ℕ)) :
    |f j-f l| ≤ M*(Nat.dist j.val l.val : ℝ)*
      (min (min (j.val+1) ((n : ℕ)-j.val))
        (min (l.val+1) ((n : ℕ)-l.val)) : ℕ)^(-t) := by
  have hh := ConditionalForces.block_moment_telescoping_internal (Measure.dirac ())
    n (fun i (_ : Unit) => f i) (p := 2) (by norm_num) hM ht
    (fun k hk => by
      simpa [Real.enorm_eq_ofReal_abs] using ENNReal.ofReal_le_ofReal (hf k hk)) j l
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
  simpa [Real.enorm_eq_ofReal_abs] using hh

/-- See Subsection 6.3 and the proof of Lemma 6.5 of the paper: the fine
event controls the actual compensation entries and their signed ordinary
column increments. These bounds retain their stronger volume profiles. -/
theorem long_fine_compensation_internal
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (η κ : ℝ) (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1))
    (hx : x ∈ longFineEvent β s n m η κ) :
    let N := (n : ℝ)+m+1
    let A := (n : ℝ)^(κ*η)
    (∀ i, ConditionalForces.compensationC β s n m x +
      ConditionalForces.compensationB β s n m i x ≤ A*N^(-s.val)) ∧
    (∀ i j, |ConditionalForces.compensationQ β s n m i j x| ≤ 3*A*N^(-s.val)) ∧
    (∀ i j l, |ConditionalForces.compensationQ β s n m i j x -
      ConditionalForces.compensationQ β s n m i l x| ≤
      A*N⁻¹*(Nat.dist j.val l.val : ℝ)*
        (min (min (j.val+1) ((n : ℕ)-j.val))
          (min (l.val+1) ((n : ℕ)-l.val)) : ℕ)^(-s.val)) := by
  intro N A
  have hN : 0 < N := by dsimp [N]; positivity
  have hsize (i) : ConditionalForces.compensationC β s n m x +
      ConditionalForces.compensationB β s n m i x ≤ A*N^(-s.val) := by
    have hh := hx.2.1 i
    have hh' : ConditionalForces.compensationC β s n m x +
        ConditionalForces.compensationB β s n m i x ≤ A/N^s.val :=
      (le_div_iff₀ (Real.rpow_pos_of_pos hN s.val)).mpr (by
        change (_+_)*((n : ℝ)+m+1)^s.val ≤ (n : ℝ)^(κ*η)
        nlinarith only [hh])
    simpa only [div_eq_mul_inv, ← Real.rpow_neg hN.le] using hh'
  refine ⟨hsize, fun i j => ?_, fun i j l => ?_⟩
  · have hi := ConditionalForces.compensationB_nonneg β s n m i x
    have hj := ConditionalForces.compensationB_nonneg β s n m j x
    have hc := ConditionalForces.compensationC_nonneg β s n m x
    apply abs_le.mpr
    constructor <;> dsimp only [ConditionalForces.compensationQ] <;>
      nlinarith [hsize i, hsize j,
        mul_nonneg (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n) (κ*η))
          (Real.rpow_nonneg hN.le (-s.val))]
  · have hstep (k : Fin (n : ℕ)) (hk : k.val+1 < (n : ℕ)) :
        |ConditionalForces.compensationB β s n m (k+1) x -
          ConditionalForces.compensationB β s n m k x| ≤
          (A*N⁻¹)*(min (k.val+1) ((n : ℕ)-k.val) : ℕ)^(-s.val) := by
      let q : Fin ((n : ℕ)-1) := ⟨k.val, by omega⟩
      have hh := hx.2.2 q
      have hδ : 0 < (min (k.val+1) ((n : ℕ)-k.val) : ℕ) := by
        have := k.isLt
        omega
      have hb : 0 < N*(min (k.val+1) ((n : ℕ)-k.val) : ℕ)^s.val := by
        exact mul_pos hN (Real.rpow_pos_of_pos (by exact_mod_cast hδ) _)
      have he : (⟨q.val+1, by omega⟩ : Fin (n : ℕ)) = k+1 := by
        apply Fin.ext
        exact (Fin.val_add_one_of_lt' hk).symm
      have he' : (⟨q.val, by omega⟩ : Fin (n : ℕ)) = k := Fin.ext rfl
      rw [he, he'] at hh
      have hh' : |ConditionalForces.compensationB β s n m (k+1) x -
          ConditionalForces.compensationB β s n m k x| ≤
          A/(N*(min (k.val+1) ((n : ℕ)-k.val) : ℕ)^s.val) :=
        (le_div_iff₀ hb).mpr (by
          dsimp only [q, A, N] at hh ⊢
          nlinarith only [hh])
      simpa only [q, div_eq_mul_inv, mul_inv_rev, ← Real.rpow_neg (by positivity :
        (0 : ℝ) ≤ (min (k.val+1) ((n : ℕ)-k.val) : ℕ)), mul_assoc, mul_comm,
        mul_left_comm] using hh'
    rw [ConditionalForces.compensationQ_sub, abs_sub_comm]
    exact depth_telescoping_internal n (fun k => ConditionalForces.compensationB β s n m k x)
      (A*N⁻¹) s.val (by dsimp [A]; positivity) s.property.1.le hstep j l

/-- See the proof of Lemma 6.5 in the paper: volume compensation
profiles are bounded by the boundary profiles required for column
subtraction. Both exponents `s/2` and `1-s/2` are positive. -/
theorem compensation_profiles_internal (s : Riesz1.RieszExponent)
    (N a b : ℝ) (ha : 0 < a) (hb : 0 < b) (haN : a ≤ N) (hbN : b ≤ N) :
    N^(-s.val) ≤ a^(-s.val/2)*b^(-s.val/2) ∧
      N⁻¹*b^(-s.val) ≤ a^(-s.val/2)*b^(-1-s.val/2) := by
  have hN : 0 < N := ha.trans_le haN
  have hs : 0 ≤ s.val/2 := by linarith [s.property.1]
  have ht : 0 ≤ 1-s.val/2 := by linarith [s.property.2]
  constructor
  · have hi := Real.rpow_le_rpow_of_nonpos ha haN (show -s.val/2 ≤ 0 by linarith)
    have hj := Real.rpow_le_rpow_of_nonpos hb hbN (show -s.val/2 ≤ 0 by linarith)
    calc
      N^(-s.val) = N^(-s.val/2)*N^(-s.val/2) := by
        rw [← Real.rpow_add hN]; congr 1; ring
      _ ≤ _ := mul_le_mul hi hj (by positivity) (by positivity)
  · have hh : a^(s.val/2)*b^(1-s.val/2) ≤ N := by
      calc
        _ ≤ N^(s.val/2)*N^(1-s.val/2) :=
          mul_le_mul (Real.rpow_le_rpow ha.le haN hs)
            (Real.rpow_le_rpow hb.le hbN ht) (by positivity) (by positivity)
        _ = N := by rw [← Real.rpow_add hN]; ring_nf; rw [Real.rpow_one]
    have hh' := (inv_le_inv₀ hN (by positivity : 0 < a^(s.val/2)*b^(1-s.val/2))).mpr hh
    have hh'' := mul_le_mul_of_nonneg_right hh' (Real.rpow_nonneg hb.le (-s.val))
    apply hh''.trans_eq
    rw [mul_inv_rev, ← Real.rpow_neg ha.le, ← Real.rpow_neg hb.le]
    calc
      _ = a^(-(s.val/2))*(b^(-(1-s.val/2))*b^(-s.val)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hb, show -(s.val/2) = -s.val/2 by ring,
          show -(1-s.val/2)+ -s.val = -1-s.val/2 by ring]

/-- See the proof of Lemma 6.5 in the paper: the fine compensation
matrix has the literal entry and signed column-increment boundary bounds,
pointwise on every retained length fibre. -/
theorem long_fine_compensation_profiles_internal
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (η κ : ℝ) (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1))
    (hx : x ∈ longFineEvent β s n m η κ) (i j l : Fin (n : ℕ)) :
    let d := fun a : Fin (n : ℕ) => ((min (a.val+1) ((n : ℕ)-a.val) : ℕ) : ℝ)
    let A := (n : ℝ)^(κ*η)
    |ConditionalForces.compensationQ β s n m i j x| ≤
      3*A*(d i)^(-s.val/2)*(d j)^(-s.val/2) ∧
    |ConditionalForces.compensationQ β s n m i j x -
      ConditionalForces.compensationQ β s n m i l x| ≤
      A*(Nat.dist j.val l.val : ℝ)*(d i)^(-s.val/2)*
        (min (d j) (d l))^(-1-s.val/2) := by
  intro d A
  have hd (a : Fin (n : ℕ)) : 0 < d a := by
    dsimp [d]
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (PerturbationBounds.depth_bounds n a).1)
  have hdN (a : Fin (n : ℕ)) : d a ≤ (n : ℝ)+m+1 := by
    have hh : d a ≤ n := by
      dsimp only [d]
      exact_mod_cast (PerturbationBounds.depth_bounds n a).2
    exact hh.trans (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have hmin : 0 < min (d j) (d l) := lt_min (hd j) (hd l)
  obtain ⟨_, hp, hi⟩ := long_fine_compensation_internal β s n m η κ x hx
  constructor
  · apply (hp i j).trans
    have h := (compensation_profiles_internal s _ _ _ (hd i) (hd j) (hdN i) (hdN j)).1
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h (by dsimp [A]; positivity : 0 ≤ 3*A)
  · have hh := hi i j l
    simp only [Nat.cast_min] at hh
    apply hh.trans
    have h := (compensation_profiles_internal s _ _ _ (hd i) hmin (hdN i)
      ((min_le_left _ _).trans (hdN j))).2
    have hmul := mul_le_mul_of_nonneg_left h (by dsimp [A]; positivity :
      0 ≤ A*(Nat.dist j.val l.val : ℝ))
    simpa only [d, A, Nat.cast_min, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- See the proof of Lemma 6.5 in the paper: both compensation pairings
on any retained-coordinate law, in particular the actual length kernel.
Their exceptional coefficients are independent of the volume and length. The physical exponent `ε` does not enter the fine bounds at `η`. -/
theorem conditional_compensation_pairings_internal
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (θ : PhysicalCutoff) (ε C₀ η κ : ℝ)
    (ν : Measure (AffineSimplex.chartDomain n ((n+m : ℕ)+1)))
    (he : (∫⁻ x in (longFineEvent β s n m η κ)ᶜ,
      ENNReal.ofReal (longEnvelope β s n m θ ε C₀ x) ∂ν) ≠ (∞ : ℝ≥0∞))
    (φ ζ : Lp ℝ 2 ν) (Mφ Mζ : ℝ) (hMφ : 0 ≤ Mφ) (hMζ : 0 ≤ Mζ)
    (hφ : ∀ᵐ x ∂ν, |φ x| ≤ Mφ) (hζ : ∀ᵐ x ∂ν, |ζ x| ≤ Mζ)
    (i j l : Fin (n : ℕ)) :
    let d := fun a : Fin (n : ℕ) => ((min (a.val+1) ((n : ℕ)-a.val) : ℕ) : ℝ)
    let A := (n : ℝ)^(κ*η)
    let e := (∫⁻ x in (longFineEvent β s n m η κ)ᶜ,
      ENNReal.ofReal (longEnvelope β s n m θ ε C₀ x) ∂ν).toReal
    Integrable (fun x => φ x*ζ x*ConditionalForces.compensationQ β s n m i j x) ν ∧
    |∫ x, φ x*ζ x*ConditionalForces.compensationQ β s n m i j x ∂ν| ≤
      3*A*(d i)^(-s.val/2)*(d j)^(-s.val/2)*‖φ‖*‖ζ‖ +
        3*(n : ℝ)^(-C₀)*e*Mφ*Mζ ∧
    Integrable (fun x => φ x*ζ x*(ConditionalForces.compensationQ β s n m i j x -
      ConditionalForces.compensationQ β s n m i l x)) ν ∧
    |∫ x, φ x*ζ x*(ConditionalForces.compensationQ β s n m i j x -
      ConditionalForces.compensationQ β s n m i l x) ∂ν| ≤
      A*(Nat.dist j.val l.val : ℝ)*(d i)^(-s.val/2)*
        (min (d j) (d l))^(-1-s.val/2)*‖φ‖*‖ζ‖ +
        2*(n : ℝ)^(-C₀)*e*Mφ*Mζ := by
  intro d A e
  have hW := measurable_longEnvelope β s n m θ ε C₀
  have hW0 (x) : 0 ≤ longEnvelope β s n m θ ε C₀ x :=
    (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n) C₀).trans
      (longEnvelope_lower β s n m θ ε C₀ x)
  have hG := measurableSet_longFineEvent β s n m η κ
  have hQ (a b) : Measurable (ConditionalForces.compensationQ β s n m a b) :=
    ((ConditionalForces.measurable_compensationB β s n m a).neg.sub
      (ConditionalForces.measurable_compensationB β s n m b)).add
      (ConditionalForces.measurable_compensationC β s n m)
  have hp := conditional_coefficient_pair_internal n _ hW hW0 _ hG he _ (hQ i j)
    (3*A*(d i)^(-s.val/2)*(d j)^(-s.val/2)) 3 C₀ (by dsimp [A]; positivity)
    (fun x hx => (long_fine_compensation_profiles_internal β s n m η κ x hx i j l).1)
    (ae_of_all _ fun x => by
      simpa only [Pi.sub_apply, mul_assoc] using (long_envelope_coefficients_internal β s n m θ ε C₀ x).2.2.2.1 i j)
    φ ζ Mφ Mζ hMφ hMζ hφ hζ
  have hi := conditional_coefficient_pair_internal n _ hW hW0 _ hG he _ ((hQ i j).sub (hQ i l))
    (A*(Nat.dist j.val l.val : ℝ)*(d i)^(-s.val/2)*(min (d j) (d l))^(-1-s.val/2))
    2 C₀ (by dsimp [A]; positivity)
    (fun x hx => (long_fine_compensation_profiles_internal β s n m η κ x hx i j l).2)
    (ae_of_all _ fun x => by
      simpa only [Pi.sub_apply, mul_assoc] using (long_envelope_coefficients_internal β s n m θ ε C₀ x).2.2.2.2 i j l)
    φ ζ Mφ Mζ hMφ hMζ hφ hζ
  exact ⟨hp.1, hp.2, hi.1, hi.2⟩

/-- See the proof of Lemma 6.5 in the paper: a compensated-score
covariance bounded by the BL diagonal envelopes is controlled globally
by the literal long envelope. This pointwise estimate applies to every
retained law and needs no unconditional exceptional probability. -/
theorem long_covariance_envelope_internal
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (θ : PhysicalCutoff) (ε C₀ : ℝ)
    (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1)) (i j : Fin (n : ℕ))
    (y : ℝ)
    (hy : |y| ≤ Real.sqrt (β.val⁻¹*(BoundaryEntries.physicalCrossing β s n m x i i +
      ConditionalForces.compensationC β s n m x))*
      Real.sqrt (β.val⁻¹*(BoundaryEntries.physicalCrossing β s n m x j j +
        ConditionalForces.compensationC β s n m x))) :
    |y| ≤ (4*β.val⁻¹)*(n : ℝ)^(-C₀)*longEnvelope β s n m θ ε C₀ x := by
  let E := (n : ℝ)^(-C₀)*longEnvelope β s n m θ ε C₀ x
  have henv := long_envelope_coefficients_internal β s n m θ ε C₀ x
  have hdiag (k : Fin (n : ℕ)) : BoundaryEntries.physicalCrossing β s n m x k k +
      ConditionalForces.compensationC β s n m x ≤ 2*E := by
    have hk := BoundaryEntries.physicalCrossing_le_hessian β s n m x k k
    linarith [henv.1 k k, henv.2.2.1]
  have hpos (k : Fin (n : ℕ)) : 0 ≤ β.val⁻¹*(BoundaryEntries.physicalCrossing β s n m x k k +
      ConditionalForces.compensationC β s n m x) := by
    exact mul_nonneg (inv_nonneg.mpr β.property.le)
      (add_nonneg (BoundaryEntries.physicalCrossing_nonneg β s n m x k k)
        (ConditionalForces.compensationC_nonneg β s n m x))
  calc
    _ ≤ β.val⁻¹*(BoundaryEntries.physicalCrossing β s n m x i i +
          ConditionalForces.compensationC β s n m x) +
        β.val⁻¹*(BoundaryEntries.physicalCrossing β s n m x j j +
          ConditionalForces.compensationC β s n m x) :=
      hy.trans (KernelCovarianceBounds.sqrt_product_le_add (hpos i) (hpos j))
    _ ≤ β.val⁻¹*(2*E)+β.val⁻¹*(2*E) := add_le_add
      (mul_le_mul_of_nonneg_left (hdiag i) (inv_nonneg.mpr β.property.le))
      (mul_le_mul_of_nonneg_left (hdiag j) (inv_nonneg.mpr β.property.le))
    _ = _ := by dsimp only [E]; ring

/-- See the proof of Lemma 6.5 in the paper: covariance entry and
signed column-increment pairings with the conditional weighted remainder.
The loss is chosen before the fine tolerance and temperature interval.
The law may be an individual retained fibre. No domination of that law
by an unconditional marginal is assumed. -/
theorem conditional_covariance_pairings_internal
    (s : Riesz1.RieszExponent) (κ₀ : ℝ) (hκ₀ : 1 ≤ κ₀) :
    ∃ κ > 0, ∀ η βlo βhi : ℝ, 0 < η → 0 < βlo → βlo ≤ βhi →
    ∃ C > 0, ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    ∀ (n : ℕ+) (m : ℕ), 2*(n : ℕ) ≤ (n : ℕ)+m+1 →
    ∃ U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ,
      ContDiffOn ℝ ∞ U (gapAmbientDomain ((n : ℕ)+m).succPNat) ∧
      (∀ y : gapAmbientDomain ((n : ℕ)+m).succPNat,
        U y.val = β.val*physicalAmbientGapEnergy (ofLong β s) ((n : ℕ)+m).succPNat y) ∧
    let Xi := fun (i : Fin (n : ℕ))
      (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1)) z => β.val⁻¹ *
        (fderiv ℝ U (RetainedSimplex.chart n m ((n+m : ℕ)+1) (Equiv.refl _) (x.val,z))
          (EuclideanSpace.single (i.castAdd m).castSucc 1) -
        fderiv ℝ U (RetainedSimplex.chart n m ((n+m : ℕ)+1) (Equiv.refl _) (x.val,z))
          (WithLp.toLp 2 (ConditionalForces.compensationVector n m)))
    let Y := fun i j x => ProbabilityTheory.covariance (Xi i x) (Xi j x)
      (ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x)
    (∀ x i, MemLp (Xi i x) 2
      (ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x)) ∧
    ∀ (θ : PhysicalCutoff) (ε C₀ : ℝ)
      (ν : Measure (AffineSimplex.chartDomain n ((n+m : ℕ)+1))),
      (∫⁻ x in (longFineEvent β s n m η κ₀)ᶜ,
        ENNReal.ofReal (longEnvelope β s n m θ ε C₀ x) ∂ν) ≠ (∞ : ℝ≥0∞) →
    ∀ (φ ζ : Lp ℝ 2 ν) (Mφ Mζ : ℝ), 0 ≤ Mφ → 0 ≤ Mζ →
      (∀ᵐ x ∂ν, |φ x| ≤ Mφ) → (∀ᵐ x ∂ν, |ζ x| ≤ Mζ) →
    ∀ i j l : Fin (n : ℕ),
    let d := fun a : Fin (n : ℕ) => ((min (a.val+1) ((n : ℕ)-a.val) : ℕ) : ℝ)
    let e := (∫⁻ x in (longFineEvent β s n m η κ₀)ᶜ,
      ENNReal.ofReal (longEnvelope β s n m θ ε C₀ x) ∂ν).toReal
    Integrable (fun x => φ x*ζ x*Y i j x) ν ∧
    |∫ x, φ x*ζ x*Y i j x ∂ν| ≤
      C*(n : ℝ)^(κ*η)*(d i)^(-s.val/2)*(d j)^(-s.val/2)*‖φ‖*‖ζ‖ +
        (4*βlo⁻¹)*(n : ℝ)^(-C₀)*e*Mφ*Mζ ∧
    Integrable (fun x => φ x*ζ x*(Y i j x-Y i l x)) ν ∧
    |∫ x, φ x*ζ x*(Y i j x-Y i l x) ∂ν| ≤
      C*(n : ℝ)^(κ*η)*(Nat.dist j.val l.val : ℝ)*(d i)^(-s.val/2)*
        (min (d j) (d l))^(-1-s.val/2)*‖φ‖*‖ζ‖ +
        (8*βlo⁻¹)*(n : ℝ)^(-C₀)*e*Mφ*Mζ := by
  obtain ⟨k, hk, henv⟩ := PerturbationBounds.uniform_covariance_envelopes s κ₀ (by linarith)
  let κ := 2*(k+κ₀+7)
  refine ⟨κ, by dsimp [κ]; linarith, fun η βlo βhi hη hlo hle => ?_⟩
  obtain ⟨B, hB, hb⟩ := henv η βlo βhi hη hlo hle
  let V := βlo⁻¹*(128*(5/Real.log 2+4)*(Real.log 2+1/η)+1)
  have hV : 0 ≤ V := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    dsimp [V]
    positivity
  let J := V+1
  have hJ : 0 < J := by dsimp [J]; linarith
  let C := J^2+J*B+1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun β hβ n m hper => ?_⟩
  obtain ⟨U, hU, hUv, he⟩ := hb β hβ n m hper
  refine ⟨U, hU, hUv, ?_⟩
  intro Xi Y
  refine ⟨fun x i => (he x).1 i, ?_⟩
  intro θ ε C₀ ν hfinite φ ζ Mφ Mζ hMφ hMζ hφ hζ i j l d e
  have hm (a b) : Measurable (Y a b) := PerturbationBounds.measurable_physical_covariance β s n m U a b
  have hW := measurable_longEnvelope β s n m θ ε C₀
  have hW0 (x) : 0 ≤ longEnvelope β s n m θ ε C₀ x :=
    (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n) C₀).trans
      (longEnvelope_lower β s n m θ ε C₀ x)
  have hG := measurableSet_longFineEvent β s n m η κ₀
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hd (a : Fin (n : ℕ)) : 0 < d a := by
    dsimp only [d]
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (PerturbationBounds.depth_bounds n a).1)
  have hvb (x) (hx : x ∈ longFineEvent β s n m η κ₀) (a : Fin (n : ℕ)) :
      Real.sqrt (β.val⁻¹*(BoundaryEntries.physicalCrossing β s n m x a a +
        ConditionalForces.compensationC β s n m x)) ≤ J*(n : ℝ)^((κ₀+7)*η)*(d a)^(-s.val/2) := by
    have hc : ConditionalForces.compensationC β s n m x ≤
        (n : ℝ)^(κ₀*η)*((n : ℝ)+m+1)^(-s.val) := by
      have hh := (long_fine_compensation_internal β s n m η κ₀ x hx).1 a
      linarith [ConditionalForces.compensationB_nonneg β s n m a x]
    exact (Real.sqrt_le_sqrt (PerturbationBounds.variance_depth_bound β s βlo η κ₀ hlo
      hβ.1 hη hκ₀ n m hper x hx.1 hc a)).trans
        (PerturbationBounds.sqrt_depth_internal hV hn1 (by nlinarith) (hd a))
  have halg := PerturbationBounds.covariance_profile_algebra_internal hn1 hη
    (show 0 ≤ κ₀+7 by linarith) hk.le hJ.le hB.le
    (Real.rpow_nonneg (hd i).le (-s.val/2)) (Real.rpow_nonneg (hd j).le (-s.val/2))
    (Nat.cast_nonneg (α := ℝ) (Nat.dist j.val l.val))
    (Real.rpow_nonneg (le_of_lt (lt_min (hd j) (hd l))) (-1-s.val/2))
    (show J^2 ≤ C by dsimp [C]; nlinarith [mul_nonneg hJ.le hB.le])
    (show J*B ≤ C by dsimp [C]; nlinarith [sq_nonneg J])
  have hgood (x) (hx : x ∈ longFineEvent β s n m η κ₀) :
      |Y i j x| ≤ C*(n : ℝ)^(κ*η)*(d i)^(-s.val/2)*(d j)^(-s.val/2) := by
    exact ((he x).2.1 i j).trans ((mul_le_mul (hvb x hx i) (hvb x hx j)
      (Real.sqrt_nonneg _) (by positivity)).trans (by simpa only [κ, add_assoc] using halg.1))
  have hincr (x) (hx : x ∈ longFineEvent β s n m η κ₀) :
      |Y i j x-Y i l x| ≤ C*(n : ℝ)^(κ*η)*(Nat.dist j.val l.val : ℝ)*
        (d i)^(-s.val/2)*(min (d j) (d l))^(-1-s.val/2) := by
    have hh := (he x).2.2 hx.1 i j l
    simp only [Nat.cast_min] at hh
    apply hh.trans
    apply (mul_le_mul_of_nonneg_right (hvb x hx i) (by positivity)).trans
    simpa only [κ, add_assoc, d, Nat.cast_min] using halg.2
  have hbad (a b) (x) : |Y a b x| ≤
      (4*βlo⁻¹)*(n : ℝ)^(-C₀)*longEnvelope β s n m θ ε C₀ x := by
    apply (long_covariance_envelope_internal β s n m θ ε C₀ x a b _ ((he x).2.1 a b)).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        ((inv_le_inv₀ β.property hlo).mpr hβ.1) (by norm_num)) (by positivity)) (hW0 x)
  have hbadinc (x) : |Y i j x-Y i l x| ≤
      (8*βlo⁻¹)*(n : ℝ)^(-C₀)*longEnvelope β s n m θ ε C₀ x := by
    apply (abs_sub _ _).trans
    nlinarith only [hbad i j x, hbad i l x]
  have hp := conditional_coefficient_pair_internal n _ hW hW0 _ hG hfinite _ (hm i j)
    _ (4*βlo⁻¹) C₀ (by positivity) hgood (ae_of_all _ (hbad i j))
    φ ζ Mφ Mζ hMφ hMζ hφ hζ
  have hi := conditional_coefficient_pair_internal n _ hW hW0 _ hG hfinite _ ((hm i j).sub (hm i l))
    _ (8*βlo⁻¹) C₀ (by positivity) hincr (ae_of_all _ hbadinc)
    φ ζ Mφ Mζ hMφ hMζ hφ hζ
  exact ⟨hp.1, hp.2, hi.1, hi.2⟩

/-- See the proof of Lemma 6.5 in the paper: the compensated Hessian
identity holds for every realization of the same physical ambient
potential. Thus the score realization giving the pointwise BL bounds
can be used in the actual two-sided Hessian formula. -/
theorem long_twoSided_hessian_realization_internal
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ)
    (U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ)
    (hU : ∀ y : gapAmbientDomain ((n : ℕ)+m).succPNat,
      U y.val = β.val*physicalAmbientGapEnergy (ofLong β s) ((n : ℕ)+m).succPNat y) :
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      β.val*∑ i, (θ.val ((n : ℝ)^(-ε)*x i)+θ.val ((n : ℝ)^(-ε)*(x i)⁻¹)) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (x,z)).toReal)
    ∀ x : AffineSimplex.chartDomain n ((n+m : ℕ)+1),
    let μ := ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x
    let Xi := fun i z => β.val⁻¹ *
      (fderiv ℝ U (RetainedSimplex.chart n m ((n+m : ℕ)+1) (Equiv.refl _) (x.val,z))
        (EuclideanSpace.single (i.castAdd m).castSucc 1) -
       fderiv ℝ U (RetainedSimplex.chart n m ((n+m : ℕ)+1) (Equiv.refl _) (x.val,z))
        (WithLp.toLp 2 (ConditionalForces.compensationVector n m)))
    (∀ i : Fin (n : ℕ), MemLp (Xi i) 2 μ) ∧
    ∀ i j, hessianMatrix V x.val i j =
      β.val*(InterpolationMatrix.penaltyHessian n θ ε x.val i j +
        GoodBlocks.conditionalHessian β s n m i j x +
        ConditionalForces.compensationQ β s n m i j x) -
      β.val^2*ProbabilityTheory.covariance (Xi i) (Xi j) μ := by
  intro V
  obtain ⟨U', _hsm, hU', hh⟩ := long_twoSided_hessian_internal β s n m θ ε
  have hd (y : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)))
      (hy : y ∈ gapAmbientDomain ((n : ℕ)+m).succPNat) : fderiv ℝ U y = fderiv ℝ U' y := by
    have heq : U =ᶠ[𝓝 y] U' := by
      filter_upwards [(PhysicalEnergy.isOpen_gapAmbientDomain _).mem_nhds hy] with z hz
      exact (hU ⟨z,hz⟩).trans (hU' ⟨z,hz⟩).symm
    exact heq.fderiv_eq
  intro x μ Xi
  let Xi' := fun (i : Fin (n : ℕ)) (z : EuclideanSpace ℝ (Fin m)) => β.val⁻¹ *
    (fderiv ℝ U' (RetainedSimplex.chart n m ((n+m : ℕ)+1) (Equiv.refl _) (x.val,z))
      (EuclideanSpace.single (i.castAdd m).castSucc 1) -
     fderiv ℝ U' (RetainedSimplex.chart n m ((n+m : ℕ)+1) (Equiv.refl _) (x.val,z))
      (WithLp.toLp 2 (ConditionalForces.compensationVector n m)))
  have heq (i : Fin (n : ℕ)) : Xi i =ᵐ[μ] Xi' i := by
    filter_upwards [ConditionalEnergyMoments.physical_conditional_support
      (ofLong β s) n m n.pos (Equiv.refl _) x] with z hz
    have hdom := (Set.ext_iff.mp (RetainedSimplex.fibre_domain n m _ x.property) z).mpr hz
    have hsimp := (RetainedSimplex.chart_mem_simplex n m _ (Equiv.refl _) _).mpr hdom
    have hamb := ProperMarginalChart.simplex_ambient _ hsimp
    dsimp only [Xi, Xi']
    rw [hd _ hamb]
  obtain ⟨hLp, hH⟩ := hh x
  refine ⟨fun i => (memLp_congr_ae (heq i)).mpr (hLp i), fun i j => ?_⟩
  have hcov : ProbabilityTheory.covariance (Xi i) (Xi j) μ =
      ProbabilityTheory.covariance (Xi' i) (Xi' j) μ := by
    unfold ProbabilityTheory.covariance
    rw [integral_congr_ae (heq i), integral_congr_ae (heq j)]
    apply integral_congr_ae
    filter_upwards [heq i, heq j] with z hi hj
    rw [hi, hj]
  rw [hcov]
  exact hH i j

/-- See the proof of Lemma 6.5 in the paper: the marginal fine event
implies the common rigidity event used to freeze the interval matrix.
The half-volume assumption ensures that every retained interval is among
the nonwrapping intervals tested by the marginal event. -/
theorem long_fine_mem_goodSet_internal
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (hper : 2*(n : ℕ) ≤ (n : ℕ)+m+1) (η κ : ℝ)
    (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1))
    (hx : x ∈ longFineEvent β s n m η κ) : x ∈ InterpolationMatrix.goodSet s n m η := by
  refine ⟨?_, hx.1.1.1, ?_⟩
  · simpa only [Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add] using x.property.2
  · intro a b hab hbn
    let j : Fin (n : ℕ) := ⟨a, by omega⟩
    let k : Fin ((n : ℕ)+1) := ⟨b-a, by omega⟩
    have hk : k.val ≤ ((n : ℕ)+m+1)/2 := by dsimp [k]; omega
    have hh := hx.1.1.2 j k (by dsimp [k]; omega) hk (by dsimp [j,k]; omega)
    rw [InterpolationCoefficients.cyclicGapSum_filter n a (b-a) (by omega) (by omega)] at hh
    simpa only [j, k, Nat.add_sub_of_le hab.le, min_eq_left s.property.2.le] using hh

/-- See the proof of Lemma 6.5 in the paper: the penalty part of the
global long envelope controls every Hessian entry. Mixed entries vanish
on the entire positive carrier, independently of either tolerance. -/
theorem long_penalty_envelope_internal
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (θ : PhysicalCutoff) (ε C₀ : ℝ)
    (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1)) (i j : Fin (n : ℕ)) :
    |InterpolationMatrix.penaltyHessian n θ ε x.val i j| ≤
      (n : ℝ)^(-C₀)*longEnvelope β s n m θ ε C₀ x := by
  by_cases hij : i = j
  · subst j
    have hdiag := Finset.single_le_sum
      (fun k _ => abs_nonneg (InterpolationMatrix.penaltyHessian n θ ε x.val k k)) (Finset.mem_univ i)
    have hP := Finset.sum_nonneg (s := Finset.univ) fun k _ =>
      Finset.sum_nonneg (s := Finset.univ) fun l _ => GoodBlocks.conditionalHessian_nonneg β s n m k l x
    have hb := Finset.sum_nonneg (s := Finset.univ) fun k _ =>
      ConditionalForces.compensationB_nonneg β s n m k x
    have hc := ConditionalForces.compensationC_nonneg β s n m x
    unfold longEnvelope
    rw [← mul_assoc, ← Real.rpow_add (by positivity : (0 : ℝ) < n),
      neg_add_cancel, Real.rpow_zero, one_mul]
    linarith
  · rw [InterpolationMatrix.penaltyHessian_off_diagonal n θ ε x.val x.property.1 i j hij, abs_zero]
    exact mul_nonneg (by positivity)
      ((Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n) C₀).trans
        (longEnvelope_lower β s n m θ ε C₀ x))

/-- See the proof of Lemma 6.5 in the paper: both reference interval
pieces are entrywise nonnegative with the cutoff and antipodal
normalization. -/
theorem reference_split_nonneg_internal (s : Riesz1.RieszExponent) (M : ℕ+)
    (hM : 2 ≤ (M : ℕ)) (K : ℕ) (n : ℕ+) (hnM : (n : ℕ) ≤ (M : ℕ))
    (i j : Fin (n : ℕ)) :
    0 ≤ BoundaryEntries.referenceInternal s M hM K n hnM i j ∧
      0 ≤ BoundaryEntries.referenceCrossing s M hM K n hnM i j := by
  have hblock (family : Finset (Fin (M : ℕ)) → Prop) :
      0 ≤ BoundaryEntries.referenceIntervalBlock s M hM K n hnM family i j := by
    apply Finset.sum_nonneg
    intro a _
    apply Finset.sum_nonneg
    intro r hr
    have hrs := (Finset.mem_filter.mp hr).2
    have hrM : r < (M : ℕ) := by
      have hh := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
      omega
    have hne : (⟨r % (M : ℕ), Nat.mod_lt _ M.pos⟩ : Fin (M : ℕ)) ≠ 0 := by
      intro heq
      have hh := congrArg Fin.val heq
      simp only [Fin.val_zero, Nat.mod_eq_of_lt hrM] at hh
      omega
    have hp := (sampledSecondDifference_pos s M hM hne).le
    split_ifs <;> positivity
  exact ⟨hblock _, hblock _⟩

/-- See the proof of Lemma 6.5 in the paper: the interval-freezing
defect has a global envelope, retaining the reference-period factor.
This is the actual two-sided matrix at physical exponent `ε` and
independent fine tolerance `η`, specialized to identical endpoints. -/
theorem long_interval_freezing_envelope_internal (s : Riesz1.RieszExponent) :
    ∃ C > 0, ∀ (β : InverseTemperature) (n : ℕ+) (m : ℕ)
      (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ)
      (θ : PhysicalCutoff) (ε C₀ η : ℝ)
      (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1)) (i j : Fin (n : ℕ)),
    |InterpolationMatrix.penaltyHessian n θ ε x.val i j +
      GoodBlocks.conditionalHessian β s n m i j x -
      InterpolationMatrix.activeBlock β s n m m le_rfl M hM hnM K θ ε η 0 x i j| ≤
        (2+2*C*(M : ℝ)^2)*(n : ℝ)^(-C₀)*longEnvelope β s n m θ ε C₀ x := by
  obtain ⟨C, hC, href⟩ := PerturbationBounds.reference_freezing_bound s
  refine ⟨C, hC, ?_⟩
  intro β n m M hM hnM K θ ε C₀ η x i j
  let E := (n : ℝ)^(-C₀)*longEnvelope β s n m θ ε C₀ x
  have hE : 1 ≤ E := by
    have hh := mul_le_mul_of_nonneg_left (longEnvelope_lower β s n m θ ε C₀ x)
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n) (-C₀))
    simpa only [← Real.rpow_add (by positivity : (0 : ℝ) < n),
      neg_add_cancel, Real.rpow_zero] using hh
  have hP := (long_envelope_coefficients_internal β s n m θ ε C₀ x).1 i j
  have hF := long_penalty_envelope_internal β s n m θ ε C₀ x i j
  have hP0 := GoodBlocks.conditionalHessian_nonneg β s n m i j x
  have hreference := href M hM K (i.castLE hnM) (j.castLE hnM)
  have hsplit := reference_split_nonneg_internal s M hM K n hnM i j
  have hrc : BoundaryEntries.referenceCrossing s M hM K n hnM i j ≤ 2*C*(M : ℝ)^2 := by
    have he := BoundaryEntries.referenceInternal_add_crossing s M hM K n hnM i j
    have hri := hsplit.1
    linarith [le_abs_self (referenceIntervalMatrix s M hM K (i.castLE hnM) (j.castLE hnM))]
  have hcross0 := BoundaryEntries.physicalCrossing_nonneg β s n m x i j
  have hcross := (BoundaryEntries.physicalCrossing_le_hessian β s n m x i j).trans hP
  have he0 : InterpolationMatrix.internalBlock β s n m m le_rfl 0 x =
      BoundaryEntries.physicalInternal β s n m x := by
    simp only [InterpolationMatrix.internalBlock, sub_zero, one_smul, zero_smul, add_zero]
  by_cases hx : x ∈ InterpolationMatrix.goodSet s n m η
  · have he := BoundaryEntries.physicalInternal_add_crossing β s n m x i j
    simp only [InterpolationMatrix.activeBlock, ite_eq_left hx, he0, Matrix.add_apply]
    have hrc' := hsplit.2
    apply abs_le.mpr
    constructor <;> dsimp only [E] at * <;>
      nlinarith [mul_nonneg (by positivity : 0 ≤ 2*C*(M : ℝ)^2) (sub_nonneg.mpr hE)]
  · simp only [InterpolationMatrix.activeBlock, ite_eq_right hx, Matrix.add_apply,
      BoundaryEntries.referenceInternal_add_crossing]
    apply abs_le.mpr
    have hf := abs_le.mp hF
    have hr := abs_le.mp hreference
    constructor <;> dsimp only [E] at * <;>
      nlinarith [mul_nonneg (by positivity : 0 ≤ 2*C*(M : ℝ)^2) (sub_nonneg.mpr hE)]

/-- See the proof of Lemma 6.5 in the paper: on the fine event the
literal two-sided freezing defect is exactly the physical-minus-reference
crossing block. The active penalty at `ε` cancels before any estimate. -/
theorem long_interval_freezing_on_fine_internal
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (hper : 2*(n : ℕ) ≤ (n : ℕ)+m+1)
    (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ)
    (θ : PhysicalCutoff) (ε η κ : ℝ)
    (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1))
    (hx : x ∈ longFineEvent β s n m η κ) (i j : Fin (n : ℕ)) :
    InterpolationMatrix.penaltyHessian n θ ε x.val i j +
      GoodBlocks.conditionalHessian β s n m i j x -
      InterpolationMatrix.activeBlock β s n m m le_rfl M hM hnM K θ ε η 0 x i j =
        BoundaryEntries.boundaryRemainder β s n m M hM hnM K x i j := by
  have hg := long_fine_mem_goodSet_internal β s n m hper η κ x hx
  simp only [InterpolationMatrix.activeBlock, ite_eq_left hg,
    InterpolationMatrix.internalBlock, sub_zero, one_smul, zero_smul, add_zero,
    Matrix.add_apply, BoundaryEntries.boundaryRemainder, Matrix.sub_apply]
  linarith only [BoundaryEntries.physicalInternal_add_crossing β s n m x i j]

/-- See the proof of Lemma 6.5 in the paper: both interval-freezing
pairings on an individual retained-coordinate law. The exceptional
coefficient is `n^(1+2/s-C₀)`, uniform in the physical volume and fibre
length. The reference period has only its prescribed polynomial bound. -/
theorem conditional_interval_freezing_pairings_internal (s : Riesz1.RieszExponent) (κ₀ : ℝ) :
    ∃ κ > 0, ∀ η : ℝ, 0 < η → ∃ A D : ℝ, 0 < A ∧ 0 < D ∧
    ∀ (β : InverseTemperature) (n : ℕ+) (m : ℕ),
      2*(n : ℕ) ≤ (n : ℕ)+m+1 →
    ∀ (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ),
      2*(n : ℕ) ≤ (M : ℕ) → (M : ℝ) ≤ 3*(n : ℝ)^(1/2+1/s.val) →
    ∀ (θ : PhysicalCutoff) (ε C₀ : ℝ)
      (ν : Measure (AffineSimplex.chartDomain n ((n+m : ℕ)+1))),
      (∫⁻ x in (longFineEvent β s n m η κ₀)ᶜ,
        ENNReal.ofReal (longEnvelope β s n m θ ε C₀ x) ∂ν) ≠ (∞ : ℝ≥0∞) →
    ∀ (φ ζ : Lp ℝ 2 ν) (Mφ Mζ : ℝ), 0 ≤ Mφ → 0 ≤ Mζ →
      (∀ᵐ x ∂ν, |φ x| ≤ Mφ) → (∀ᵐ x ∂ν, |ζ x| ≤ Mζ) →
    ∀ i j l : Fin (n : ℕ),
    let d := fun a : Fin (n : ℕ) => ((min (a.val+1) ((n : ℕ)-a.val) : ℕ) : ℝ)
    let Y := fun a b x => InterpolationMatrix.penaltyHessian n θ ε x.val a b +
      GoodBlocks.conditionalHessian β s n m a b x -
      InterpolationMatrix.activeBlock β s n m m le_rfl M hM hnM K θ ε η 0 x a b
    let e := (∫⁻ x in (longFineEvent β s n m η κ₀)ᶜ,
      ENNReal.ofReal (longEnvelope β s n m θ ε C₀ x) ∂ν).toReal
    Integrable (fun x => φ x*ζ x*Y i j x) ν ∧
    |∫ x, φ x*ζ x*Y i j x ∂ν| ≤
      A*(n : ℝ)^(κ*η)*(d i)^(-s.val/2)*(d j)^(-s.val/2)*‖φ‖*‖ζ‖ +
        D*(n : ℝ)^(1+2/s.val-C₀)*e*Mφ*Mζ ∧
    Integrable (fun x => φ x*ζ x*(Y i j x-Y i l x)) ν ∧
    |∫ x, φ x*ζ x*(Y i j x-Y i l x) ∂ν| ≤
      A*(n : ℝ)^(κ*η)*(Nat.dist j.val l.val : ℝ)*(d i)^(-s.val/2)*
        (min (d j) (d l))^(-1-s.val/2)*‖φ‖*‖ζ‖ +
        2*D*(n : ℝ)^(1+2/s.val-C₀)*e*Mφ*Mζ := by
  obtain ⟨κ, hκ, hb⟩ := BoundaryEntries.boundary_intervals_uniform s κ₀
  obtain ⟨R, hR, hr⟩ := long_interval_freezing_envelope_internal s
  refine ⟨κ, hκ, fun η hη => ?_⟩
  obtain ⟨A, hA, ha⟩ := hb η hη
  refine ⟨A, 2+18*R, hA, by positivity, ?_⟩
  intro β n m hper M hM hnM K hhalf hscale θ ε C₀ ν hfinite φ ζ Mφ Mζ hMφ hMζ hφ hζ i j l d Y e
  let B := 1+2/s.val
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hpow : (M : ℝ)^2 ≤ 9*(n : ℝ)^B := by
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ M) hscale 2
    have hp : ((n : ℝ)^(1/2+1/s.val))^2 = (n : ℝ)^B := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
      congr 1
      dsimp only [B]
      push_cast
      ring
    simpa only [mul_pow, hp, show (3 : ℝ)^2 = 9 by norm_num] using hh
  have hfac : 2+2*R*(M : ℝ)^2 ≤ (2+18*R)*(n : ℝ)^B := by
    have hh : 1 ≤ (n : ℝ)^B := Real.one_le_rpow hn1 (by dsimp [B]; have := s.property.1; positivity)
    nlinarith [mul_le_mul_of_nonneg_left hpow hR.le]
  have hW := measurable_longEnvelope β s n m θ ε C₀
  have hW0 (x) : 0 ≤ longEnvelope β s n m θ ε C₀ x :=
    (Real.rpow_nonneg hn0.le C₀).trans (longEnvelope_lower β s n m θ ε C₀ x)
  have hG := measurableSet_longFineEvent β s n m η κ₀
  have hm (a b : Fin (n : ℕ)) : Measurable (Y a b) :=
    (((InterpolationMatrix.measurable_penaltyHessian n θ ε a b).comp measurable_subtype_coe).add
      (GoodBlocks.measurable_conditionalHessian β s n m a b)).sub
        (InterpolationMatrix.measurable_activeBlock β s n m m le_rfl M hM hnM K θ ε η 0 a b)
  have hg (x) (hx : x ∈ longFineEvent β s n m η κ₀) :=
    ha β n m hper M hM hnM K hhalf x hx.1 i j l
  have heq (x) (hx : x ∈ longFineEvent β s n m η κ₀) (a b) :
      Y a b x = BoundaryEntries.boundaryRemainder β s n m M hM hnM K x a b :=
    long_interval_freezing_on_fine_internal β s n m hper M hM hnM K θ ε η κ₀ x hx a b
  have hgood (x) (hx : x ∈ longFineEvent β s n m η κ₀) :
      |Y i j x| ≤ A*(n : ℝ)^(κ*η)*(d i)^(-s.val/2)*(d j)^(-s.val/2) := by
    rw [heq x hx]
    exact (hg x hx).1
  have hincr (x) (hx : x ∈ longFineEvent β s n m η κ₀) :
      |Y i j x-Y i l x| ≤ A*(n : ℝ)^(κ*η)*(Nat.dist j.val l.val : ℝ)*
        (d i)^(-s.val/2)*(min (d j) (d l))^(-1-s.val/2) := by
    rw [heq x hx, heq x hx]
    simpa only [d, Nat.cast_min] using (hg x hx).2
  have hbad (a b) (x) : |Y a b x| ≤
      ((2+18*R)*(n : ℝ)^B)*(n : ℝ)^(-C₀)*longEnvelope β s n m θ ε C₀ x :=
    (hr β n m M hM hnM K θ ε C₀ η x a b).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfac (by positivity)) (hW0 x))
  have hbadinc (x) : |Y i j x-Y i l x| ≤
      (2*((2+18*R)*(n : ℝ)^B))*(n : ℝ)^(-C₀)*longEnvelope β s n m θ ε C₀ x := by
    apply (abs_sub _ _).trans
    nlinarith only [hbad i j x, hbad i l x]
  have hp := conditional_coefficient_pair_internal n _ hW hW0 _ hG hfinite _ (hm i j)
    _ ((2+18*R)*(n : ℝ)^B) C₀ (by positivity) hgood (ae_of_all _ (hbad i j))
    φ ζ Mφ Mζ hMφ hMζ hφ hζ
  have hi := conditional_coefficient_pair_internal n _ hW hW0 _ hG hfinite _ ((hm i j).sub (hm i l))
    _ (2*((2+18*R)*(n : ℝ)^B)) C₀ (by positivity) hincr (ae_of_all _ hbadinc)
    φ ζ Mφ Mζ hMφ hMζ hφ hζ
  have hjoin : (n : ℝ)^B*(n : ℝ)^(-C₀) = (n : ℝ)^(1+2/s.val-C₀) := by
    rw [← Real.rpow_add hn0]
    rfl
  refine ⟨hp.1, ?_, hi.1, ?_⟩
  · simpa only [mul_assoc, hjoin] using hp.2
  · simpa only [Pi.sub_apply, mul_assoc, hjoin] using hi.2

/-- See the proof of Lemma 6.5 in the paper: signed assembly of the
interval, compensation and covariance pairings after absolute
integrability has been established on the conditional law. -/
theorem conditional_signed_assembly_internal {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (b q y d : X → ℝ) (β βhi P E Ab Aq Ay Db Dq Dy : ℝ)
    (hβ : 0 ≤ β) (hβhi : β ≤ βhi)
    (hb : Integrable b ν) (hq : Integrable q ν) (hy : Integrable y ν)
    (hd : ∀ x, d x = β*b x+β*q x-β^2*y x)
    (hbb : |∫ x, b x ∂ν| ≤ Ab*P+Db*E)
    (hqb : |∫ x, q x ∂ν| ≤ Aq*P+Dq*E)
    (hyb : |∫ x, y x ∂ν| ≤ Ay*P+Dy*E) :
    Integrable d ν ∧ |∫ x, d x ∂ν| ≤
      (βhi*(Ab+Aq)+βhi^2*Ay)*P+(βhi*(Db+Dq)+βhi^2*Dy)*E := by
  have he : d = fun x => β*b x+β*q x-β^2*y x := funext hd
  rw [he]
  refine ⟨((hb.const_mul β).add (hq.const_mul β)).sub (hy.const_mul (β^2)), ?_⟩
  have hs := integral_sub ((hb.const_mul β).add (hq.const_mul β)) (hy.const_mul (β^2))
  simp only [Pi.add_apply] at hs
  rw [hs, integral_add (hb.const_mul β) (hq.const_mul β), integral_const_mul,
    integral_const_mul, integral_const_mul]
  have hβhi0 : 0 ≤ βhi := hβ.trans hβhi
  have hβsq := pow_le_pow_left₀ hβ hβhi 2
  calc
    _ ≤ |β*∫ x, b x ∂ν|+|β*∫ x, q x ∂ν|+|β^2*∫ x, y x ∂ν| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = β*|∫ x, b x ∂ν|+β*|∫ x, q x ∂ν|+β^2*|∫ x, y x ∂ν| := by
      simp only [abs_mul, abs_of_nonneg hβ, abs_of_nonneg (sq_nonneg β)]
    _ ≤ βhi*(Ab*P+Db*E)+βhi*(Aq*P+Dq*E)+βhi^2*(Ay*P+Dy*E) := by
      exact add_le_add (add_le_add
        (mul_le_mul hβhi hbb (abs_nonneg _) hβhi0)
        (mul_le_mul hβhi hqb (abs_nonneg _) hβhi0))
        (mul_le_mul hβsq hyb (abs_nonneg _) (sq_nonneg βhi))
    _ = _ := by ring

/-- See the proof of Lemma 6.5 in the paper: the full physical marginal
multiplication defect, with both its point and signed column-increment
pairings on the retained law. All three physical contributions are proved
above. The exceptional term is the same conditional envelope, with its
explicit polynomial loss. No unconditional event bound is used. -/
theorem conditional_long_multiplication_pairings_internal
    (s : Riesz1.RieszExponent) (κ₀ : ℝ) (hκ₀ : 1 ≤ κ₀) :
    ∃ κ > 0, ∀ η βlo βhi : ℝ, 0 < η → 0 < βlo → βlo ≤ βhi →
    ∃ A D : ℝ, 0 < A ∧ 0 < D ∧
    ∀ (β : InverseTemperature), β.val ∈ Icc βlo βhi →
    ∀ (n : ℕ+) (m : ℕ), 2*(n : ℕ) ≤ (n : ℕ)+m+1 →
    ∀ (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ),
      2*(n : ℕ) ≤ (M : ℕ) → (M : ℝ) ≤ 3*(n : ℝ)^(1/2+1/s.val) →
    ∀ (θ : PhysicalCutoff) (ε C₀ : ℝ)
      (ν : Measure (AffineSimplex.chartDomain n ((n+m : ℕ)+1))),
      (∫⁻ x in (longFineEvent β s n m η κ₀)ᶜ,
        ENNReal.ofReal (longEnvelope β s n m θ ε C₀ x) ∂ν) ≠ (∞ : ℝ≥0∞) →
    ∀ (φ ζ : Lp ℝ 2 ν) (Mφ Mζ : ℝ), 0 ≤ Mφ → 0 ≤ Mζ →
      (∀ᵐ x ∂ν, |φ x| ≤ Mφ) → (∀ᵐ x ∂ν, |ζ x| ≤ Mζ) →
    ∀ i j l : Fin (n : ℕ),
    let d := fun a : Fin (n : ℕ) => ((min (a.val+1) ((n : ℕ)-a.val) : ℕ) : ℝ)
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      β.val*∑ i, (θ.val ((n : ℝ)^(-ε)*x i)+θ.val ((n : ℝ)^(-ε)*(x i)⁻¹)) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (x,z)).toReal)
    let Y := fun a b (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1)) =>
      hessianMatrix V x.val a b -
        β.val*InterpolationMatrix.activeBlock β s n m m le_rfl M hM hnM K θ ε η 0 x a b
    let e := (∫⁻ x in (longFineEvent β s n m η κ₀)ᶜ,
      ENNReal.ofReal (longEnvelope β s n m θ ε C₀ x) ∂ν).toReal
    Integrable (fun x => φ x*ζ x*Y i j x) ν ∧
    |∫ x, φ x*ζ x*Y i j x ∂ν| ≤
      A*(n : ℝ)^(κ*η)*(d i)^(-s.val/2)*(d j)^(-s.val/2)*‖φ‖*‖ζ‖ +
        D*(n : ℝ)^(1+2/s.val-C₀)*e*Mφ*Mζ ∧
    Integrable (fun x => φ x*ζ x*(Y i j x-Y i l x)) ν ∧
    |∫ x, φ x*ζ x*(Y i j x-Y i l x) ∂ν| ≤
      A*(n : ℝ)^(κ*η)*(Nat.dist j.val l.val : ℝ)*(d i)^(-s.val/2)*
        (min (d j) (d l))^(-1-s.val/2)*‖φ‖*‖ζ‖ +
        D*(n : ℝ)^(1+2/s.val-C₀)*e*Mφ*Mζ := by
  obtain ⟨kb, hkb, hb⟩ := conditional_interval_freezing_pairings_internal s κ₀
  obtain ⟨kc, hkc, hc⟩ := conditional_covariance_pairings_internal s κ₀ hκ₀
  let κ := max kb (max kc κ₀)
  have hκ : 0 < κ := hkb.trans_le (le_max_left _ _)
  refine ⟨κ, hκ, fun η βlo βhi hη hlo hle => ?_⟩
  obtain ⟨Ab, Db, hAb, hDb, hb⟩ := hb η hη
  obtain ⟨Ac, hAc, hc⟩ := hc η βlo βhi hη hlo hle
  let A := βhi*(Ab+3)+βhi^2*Ac
  let D := βhi*(2*Db+3)+βhi^2*(8*βlo⁻¹)
  have hhi : 0 < βhi := hlo.trans_le hle
  refine ⟨A, D, by dsimp [A]; positivity, by dsimp [D]; positivity, ?_⟩
  intro β hβ n m hper M hM hnM K hhalf hscale θ ε C₀ ν hfinite φ ζ Mφ Mζ hMφ hMζ hφ hζ i j l d V Y e
  obtain ⟨U, _hU, hUv, hXi, hc⟩ := hc β hβ n m hper
  let Xi := fun (a : Fin (n : ℕ))
      (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1)) z => β.val⁻¹ *
    (fderiv ℝ U (RetainedSimplex.chart n m ((n+m : ℕ)+1) (Equiv.refl _) (x.val,z))
      (EuclideanSpace.single (a.castAdd m).castSucc 1) -
     fderiv ℝ U (RetainedSimplex.chart n m ((n+m : ℕ)+1) (Equiv.refl _) (x.val,z))
      (WithLp.toLp 2 (ConditionalForces.compensationVector n m)))
  let C := fun a b x => ProbabilityTheory.covariance (Xi a x) (Xi b x)
    (ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x)
  let B := fun a b (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1)) =>
    InterpolationMatrix.penaltyHessian n θ ε x.val a b +
      GoodBlocks.conditionalHessian β s n m a b x -
      InterpolationMatrix.activeBlock β s n m m le_rfl M hM hnM K θ ε η 0 x a b
  let Q := ConditionalForces.compensationQ β s n m
  have hH (x) (a b) : Y a b x = β.val*B a b x+β.val*Q a b x-β.val^2*C a b x := by
    have hh := (long_twoSided_hessian_realization_internal β s n m θ ε U hUv x).2 a b
    dsimp only [Y, B, Q, C, Xi]
    rw [hh]
    ring
  obtain ⟨hbi, hbp, hbdi, hbdp⟩ := hb β n m hper M hM hnM K hhalf hscale θ ε C₀
    ν hfinite φ ζ Mφ Mζ hMφ hMζ hφ hζ i j l
  obtain ⟨hqi, hqp, hqdi, hqdp⟩ := conditional_compensation_pairings_internal β s n m θ ε C₀ η κ₀
    ν hfinite φ ζ Mφ Mζ hMφ hMζ hφ hζ i j l
  obtain ⟨hci, hcp, hcdi, hcdp⟩ := hc θ ε C₀ ν hfinite φ ζ Mφ Mζ hMφ hMζ hφ hζ i j l
  let P := fun w : ℝ => (n : ℝ)^(κ*η)*w*‖φ‖*‖ζ‖
  let E := (n : ℝ)^(1+2/s.val-C₀)*e*Mφ*Mζ
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have he0 : 0 ≤ e := ENNReal.toReal_nonneg
  have ht : -C₀ ≤ 1+2/s.val-C₀ := by
    have hh := div_nonneg (by norm_num : (0 : ℝ) ≤ 2) s.property.1.le
    linarith
  have lift (u a b b' k t w : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
      (hbb' : b ≤ b') (hk : k ≤ κ) (ht : t ≤ 1+2/s.val-C₀) (hw : 0 ≤ w)
      (hu : |u| ≤ a*(n : ℝ)^(k*η)*w*‖φ‖*‖ζ‖+b*(n : ℝ)^t*e*Mφ*Mζ) :
      |u| ≤ a*P w+b'*E := by
    apply hu.trans
    dsimp only [P, E]
    calc
      _ ≤ a*(n : ℝ)^(κ*η)*w*‖φ‖*‖ζ‖+b'*(n : ℝ)^(1+2/s.val-C₀)*e*Mφ*Mζ := by
        gcongr
        exact hb.trans hbb'
      _ = _ := by ring
  have hbκ : kb ≤ κ := le_max_left _ _
  have hcκ : kc ≤ κ := (le_max_left kc κ₀).trans (le_max_right kb _)
  have hqκ : κ₀ ≤ κ := (le_max_right kc κ₀).trans (le_max_right kb _)
  let wp := (d i)^(-s.val/2)*(d j)^(-s.val/2)
  let wi := (Nat.dist j.val l.val : ℝ)*(d i)^(-s.val/2)*(min (d j) (d l))^(-1-s.val/2)
  have hwp : 0 ≤ wp := by dsimp [wp]; positivity
  have hwi : 0 ≤ wi := by dsimp [wi]; positivity
  have hbp' := lift _ Ab Db (2*Db) kb (1+2/s.val-C₀) wp hAb.le hDb.le (by linarith) hbκ le_rfl hwp
    (by simpa only [wp, mul_assoc] using hbp)
  have hbdp' := lift _ Ab (2*Db) (2*Db) kb (1+2/s.val-C₀) wi hAb.le (by positivity) le_rfl hbκ le_rfl hwi
    (by simpa only [wi, mul_assoc] using hbdp)
  have hqp' := lift _ 3 3 3 κ₀ (-C₀) wp (by norm_num) (by norm_num) le_rfl hqκ ht hwp
    (by simpa only [wp, mul_assoc] using hqp)
  have hqdp' := lift _ 1 2 3 κ₀ (-C₀) wi (by norm_num) (by norm_num) (by norm_num) hqκ ht hwi
    (by simpa only [wi, one_mul, mul_assoc] using hqdp)
  have hcp' := lift _ Ac (4*βlo⁻¹) (8*βlo⁻¹) kc (-C₀) wp hAc.le (by positivity)
    (by have := inv_pos.mpr hlo; linarith) hcκ ht hwp
    (by simpa only [wp, mul_assoc] using hcp)
  have hcdp' := lift _ Ac (8*βlo⁻¹) (8*βlo⁻¹) kc (-C₀) wi hAc.le (by positivity) le_rfl hcκ ht hwi
    (by simpa only [wi, mul_assoc] using hcdp)
  have hqdp'' : |∫ x, φ x*ζ x*(Q i j x-Q i l x) ∂ν| ≤ 3*P wi+3*E := by
    have hp : 0 ≤ P wi := by dsimp [P]; positivity
    have hh : |∫ x, φ x*ζ x*(Q i j x-Q i l x) ∂ν| ≤ P wi+3*E := by
      simpa only [Q, Pi.sub_apply, mul_assoc, one_mul] using hqdp'
    linarith only [hh, hp]
  obtain ⟨hpi, hpp⟩ := conditional_signed_assembly_internal ν
    (fun x => φ x*ζ x*B i j x) (fun x => φ x*ζ x*Q i j x)
    (fun x => φ x*ζ x*C i j x) (fun x => φ x*ζ x*Y i j x)
    β.val βhi (P wp) E Ab 3 Ac (2*Db) 3 (8*βlo⁻¹) β.property.le hβ.2 hbi hqi hci
    (fun x => by rw [hH]; ring)
    (by simpa only [B, mul_assoc] using hbp')
    (by simpa only [Q, mul_assoc] using hqp')
    (by simpa only [C, Xi, mul_assoc] using hcp')
  obtain ⟨hii, hip⟩ := conditional_signed_assembly_internal ν
    (fun x => φ x*ζ x*(B i j x-B i l x)) (fun x => φ x*ζ x*(Q i j x-Q i l x))
    (fun x => φ x*ζ x*(C i j x-C i l x)) (fun x => φ x*ζ x*(Y i j x-Y i l x))
    β.val βhi (P wi) E Ab 3 Ac (2*Db) 3 (8*βlo⁻¹) β.property.le hβ.2 hbdi hqdi hcdi
    (fun x => by rw [hH, hH]; ring)
    (by simpa only [B, Pi.sub_apply, mul_assoc] using hbdp') hqdp''
    (by simpa only [C, Xi, Pi.sub_apply, mul_assoc] using hcdp')
  refine ⟨hpi, ?_, hii, ?_⟩
  · simpa only [A, D, P, E, wp, mul_assoc] using hpp
  · simpa only [A, D, P, E, wi, mul_assoc] using hip

/-- See the proof of Lemma 6.5 in the paper: the short physical
two-sided marginal has its actual curvature at `ε`. The fine tolerance
does not replace the physical penalty exponent in this bound. -/
theorem short_twoSided_matrix_internal (p : Parameters) (hs : 1 < p.val.2)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε : ℝ) (hε : 0 < ε) :
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      p.val.1*∑ i, (θ.val ((n : ℝ)^(-ε)*x i)+θ.val ((n : ℝ)^(-ε)*(x i)⁻¹)) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal)
    let a := p.val.1*(n : ℝ)^(-(p.val.2+2)*ε)
    ContDiffOn ℝ ∞ V (AffineSimplex.chartDomain n ((n+m : ℕ)+1)) ∧ 0 < a ∧
    ∀ x : AffineSimplex.chartDomain n ((n+m : ℕ)+1),
      (hessianMatrix V x.val).PosSemidef ∧ ∀ z : Fin (n : ℕ) → ℝ,
      a*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*hessianMatrix V x.val i j*z j := by
  intro V a
  let K := fun x => p.val.1⁻¹*V x
  have hp : ContDiffOn ℝ ∞ K (AffineSimplex.chartDomain n ((n+m : ℕ)+1)) ∧
      ∀ x ∈ AffineSimplex.chartDomain n ((n+m : ℕ)+1),
      ∀ v : EuclideanSpace ℝ (Fin (n : ℕ)),
        (n : ℝ)^(-(p.val.2+2)*ε)*‖v‖^2 ≤ fderiv ℝ (fderiv ℝ K) x v v := by
    simpa only [K, V, Real.rpow_neg (by positivity : (0 : ℝ) ≤ n), ite_true] using
      DecayShort.PhysicalFibres.active_marginal_curvature p hs n m n.pos (Equiv.refl _) θ ε hε true
  have he : V = fun x => p.val.1*K x := by
    funext x
    dsimp only [K]
    rw [mul_inv_cancel_left₀ p.property.1.ne']
  have hV : ContDiffOn ℝ ∞ V (AffineSimplex.chartDomain n ((n+m : ℕ)+1)) := by
    rw [he]
    exact contDiffOn_const.mul hp.1
  have ha : 0 < a := mul_pos p.property.1 (Real.rpow_pos_of_pos (by positivity) _)
  refine ⟨hV, ha, fun x => ?_⟩
  have hVx : ContDiffAt ℝ 2 V x.val :=
    (hV.contDiffAt ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds x.property)).of_le (by norm_num)
  have hKx : ContDiffAt ℝ 2 K x.val :=
    (hp.1.contDiffAt ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds x.property)).of_le (by norm_num)
  have hl (v : EuclideanSpace ℝ (Fin (n : ℕ))) : a*‖v‖^2 ≤ fderiv ℝ (fderiv ℝ V) x.val v v := by
    rw [he, PhysicalCollision.internal_hessian_const_mul hKx]
    simpa only [a, mul_assoc] using
      mul_le_mul_of_nonneg_left (hp.2 x.val x.property v) p.property.1.le
  have hquad (z : Fin (n : ℕ) → ℝ) :
      a*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*hessianMatrix V x.val i j*z j := by
    have hh := hl (WithLp.toLp 2 z)
    rw [← PhysicalEnergy.hessianMatrix_quadratic hVx, EuclideanSpace.real_norm_sq_eq] at hh
    exact hh
  refine ⟨Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, ?_⟩, hquad⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial]
    exact DecayShort.PhysicalComparison.hessianMatrix_symm hVx j i
  · intro z
    simpa only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum, mul_assoc] using
      (mul_nonneg ha.le (Finset.sum_nonneg fun i _ => sq_nonneg (z i))).trans (hquad z)

/-- See the proof of Lemma 6.5 in the paper: on the short fine event,
the physical two-sided penalty at `ε` has the bound at `η`, with the
two exponents independent. The off-diagonal assertion is retained. -/
theorem short_fine_penalty_internal (θ : PhysicalCutoff) :
    ∃ C > 0, ∀ (p : Parameters) (n : ℕ+) (m : ℕ) (ε η κ : ℝ),
      0 ≤ ε → 0 ≤ η →
    ∀ x : AffineSimplex.chartDomain n ((n+m : ℕ)+1),
      x ∈ shortFineEvent p n m η κ → ∀ i j,
      |InterpolationMatrix.penaltyHessian n θ ε x.val i j| ≤
        if i = j then C*(n : ℝ)^(4*η) else 0 := by
  obtain ⟨C, hC, hb⟩ := InterpolationCoercivity.forcing_entry_bound θ
  refine ⟨C, hC, ?_⟩
  intro p n m ε η κ hε hη x hx i j
  rcases n with ⟨n, hn⟩
  cases n with
  | zero => omega
  | succ a =>
      simpa only [InterpolationMatrix.penaltyHessian, PNat.mk_coe, Nat.cast_add, Nat.cast_one] using
        hb a ε η hε hη x.val (fun k => by
          simpa only [PNat.mk_coe, Nat.cast_add, Nat.cast_one] using (hx.1.2.1 k).1) i j

/-- See the proof of Lemma 6.5 in the paper: the actual retained law
comes from an orthonormal Gibbs chart with a closed conservative Neumann
realization. The intrinsic transport API applies to this same
chart and inclusion when transporting the auxiliary estimates. -/
theorem retained_neumann_realization_internal
    (p : Parameters) (n m : ℕ) (θ : PhysicalCutoff) (ε : ℝ)
    (L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ))
    (frame : AffineSimplex.Tangent n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    let V := fun z : EuclideanSpace ℝ (Fin n) =>
      let x := AffineSimplex.centredChart n L.val (frame.symm z)
      p.val.1*∑ i, (θ.val ((n+1 : ℝ)^(-ε)*x i)+θ.val ((n+1 : ℝ)^(-ε)*(x i)⁻¹)) -
        Real.log (∫ y : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity p (n+1) m (Equiv.refl _) (x,y)).toReal)
    let U := frame '' (AffineSimplex.centredChart n L.val ⁻¹' AffineSimplex.massSimplex n L.val)
    ∃ ν : Measure (EuclideanSpace ℝ (Fin n)), IsEuclideanGibbsPotential volume ν U V ∧
      (ν.comap (Subtype.val : U → _)).map
        (InterpolationTransport.orthonormalInclusion n L.val _ L.property.2 frame) =
          retainedKernel p n m θ ε L ∧
    ∃ Q : ScalarFormData ν, IsNeumannRealization U Q ∧
      IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q := by
  intro V U
  obtain ⟨ν, hV, hlaw, _⟩ := retained_intrinsic_scalar_internal p n m θ ε L frame
  have hU : IsOpen U := frame.toHomeomorph.isOpenMap _ (ConditionalWellPosedness.fibre_isOpen n L.val)
  have hB : Bornology.IsBounded U := frame.isometry.lipschitzWith.isBounded_image
    (ConditionalWellPosedness.fibre_isBounded n L.val)
  exact ⟨ν, hV, hlaw, IntrinsicScalarCore.form hU hB hV,
    IntrinsicScalarCore.realization hU hB hV, IntrinsicScalarCore.closed_dirichlet hU hB hV,
    IntrinsicScalarCore.conservative hU hB hV⟩

/-- See the proof of Lemma 6.5 in the paper: the interval matrix admits the unique auxiliary Schur solution over the
actual retained law and any specified intrinsic form on that law.
Coefficient bounds are proved
pointwise by the matrix theorem, with constants before volume,
length and the temperature. -/
theorem retained_long_frozen_auxiliary_internal
    (s : Riesz1.RieszExponent) (θ : PhysicalCutoff) (h : ℕ) :
    let κ := (s.val+7+(h : ℝ))+(s.val+2+(h : ℝ)*(1+s.val))
    let γ := (h : ℝ)+1
    ∃ (C : ℝ) (hC : 1 ≤ C), ∀ (β : InverseTemperature) (n m : ℕ),
      4*(n+1) ≤ n+1+m+1 →
    ∀ (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : (n.succPNat : ℕ) ≤ (M : ℕ))
      (_hhalf : 2*(n+1) ≤ (M : ℕ)),
      (M : ℕ) ≤ n+1+m+1 → (n+1 : ℝ)^(1/2+1/s.val) ≤ (M : ℝ) →
    ∀ ε η : ℝ, 0 ≤ ε → 0 ≤ η → η ≤ 1-s.val/2 →
    let k := ⌊(n+1 : ℝ)^η⌋₊^h
    k ≤ (M : ℕ)/4 →
    ∀ L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ),
    let ν := retainedKernel (ofLong β s) n m θ ε L
    let A := InterpolationMatrix.matrix β s n.succPNat m m le_rfl M hM hnM k θ ε η 0
    ∀ (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q),
    ∃ hA : PeriodizedMatrixBounds (ν := ν) s n.succPNat M hM k C κ γ η A,
    ∀ (i₀ : Fin (n+1)) (χ : Lp ℝ 2 ν),
    let f : PiLp 2 (fun _ : Fin (n+1) => Lp ℝ 2 ν) :=
      WithLp.toLp 2 (fun i => if i = i₀ then χ else 0)
    let B := SchurRestriction.schurForm Q hQ n.succPNat M hnM
      s hM k C κ γ η β.val hC β.property A hA
    ∃! v : MatrixEnergy.Vector (ι := Fin (n+1)) Q hQ,
      ∀ w, B v w = inner ℝ f (OperatorSchur.vectorValues Q hQ w) := by
  intro κ γ
  obtain ⟨C, hC, hb⟩ := InterpolationMatrix.matrix_bounds s θ h
  refine ⟨C, hC, ?_⟩
  intro β n m hvol M hM hnM hhalf hMN hscale ε η hε hη hηs k hk L ν A Q hQ
  have hs' : (n.succPNat : ℝ)^(1/2+1/s.val) ≤ (M : ℝ) := by
    simpa only [Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using hscale
  have hk' : ⌊(n.succPNat : ℝ)^η⌋₊^h ≤ (M : ℕ)/4 := by
    simpa only [k, Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using hk
  have hA : PeriodizedMatrixBounds (ν := ν) s n.succPNat M hM k C κ γ η A := by
    simpa only [A, k, Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using
      hb β n.succPNat m m le_rfl hvol M hM hhalf hMN hs' ε η 0 hε hη hηs
        le_rfl zero_le_one hk' ν
  refine ⟨hA, fun i₀ χ => ?_⟩
  exact (AuxiliaryMean.schur_lift_point_source_internal Q hQ s n.succPNat M hnM hM k
    C κ γ η β.val hC β.property A hA i₀ χ).1

end Riesz2.LengthAveragingFibres
