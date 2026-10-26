/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.InterpolationMatrix
public import Riesz2.Thermodynamic.InterpolationCoercivity
public import Riesz2.Thermodynamic.AuxiliaryMeanPart2
public import Riesz2.ToMathlib.PeriodizedMatrixPushforward

/-!
# All-size estimates for the common interpolation matrix

The matrix and coefficients are the literal objects of Subsection 6.1. These estimates
complete the internal coefficient comparisons used in Subsection 6.1, keeping the
physical periods separate from the component period.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical MatrixOrder ENNReal ContDiff

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.InterpolationMatrix

/-- See Subsection 6.1 of the paper: the full-interval part of the fine
rigidity event bounds the active mass at every size. -/
theorem goodSet_mass_le (s : Riesz1.RieszExponent) (n : ℕ+) (d : ℕ)
    (η : ℝ) (hη : η ≤ 1 - s.val / 2)
    (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1))
    (hx : x ∈ goodSet s n d η) : (∑ i, x.val i) ≤ 2 * (n : ℝ) := by
  have hh := hx.2.2 0 n n.pos le_rfl
  simp only [Nat.zero_le, Fin.isLt, and_self, Finset.filter_true,
    Nat.sub_zero, min_eq_left s.property.2.le] at hh
  have hu := (abs_le.mp hh).2
  have hp : (n : ℝ)^η * (n : ℝ)^(s.val/2) ≤ (n : ℝ) := by
    rw [← Real.rpow_add (by positivity : (0 : ℝ) < n)]
    exact (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast n.pos)
      (by linarith : η + s.val/2 ≤ 1)).trans_eq (Real.rpow_one _)
  linarith

/-- See Subsection 6.1 of the paper: enlarging the physical period preserves the
common fine rigidity event. -/
theorem largerChart_goodSet (s : Riesz1.RieszExponent) (n : ℕ+) (d e : ℕ)
    (hde : d ≤ e) (η : ℝ)
    (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1))
    (hx : x ∈ goodSet s n d η) : largerChart n d e hde x ∈ goodSet s n e η := by
  refine ⟨?_, hx.2⟩
  simpa only [Nat.succPNat_coe, Nat.cast_add, Nat.cast_one, Nat.cast_succ] using
    (largerChart n d e hde x).property.2

/-- See Subsection 6.1 of the paper: quantitative two-sided singleton bound on the
literal common fine event, with a prefactor before all sizes and scales. -/
theorem penaltyHessian_good_bound (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Riesz1.RieszExponent) (n : ℕ+) (d : ℕ)
      (ε η : ℝ), 0 ≤ ε → 0 ≤ η →
      ∀ (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1)),
      x ∈ goodSet s n d η → ∀ i j,
      |penaltyHessian n θ ε x.val i j| ≤
        if i = j then C * (n : ℝ)^(4*η) else 0 := by
  obtain ⟨C, hC, hb⟩ := InterpolationCoercivity.forcing_entry_bound θ
  refine ⟨C, hC, ?_⟩
  intro s n d ε η hε hη x hx i j
  rcases n with ⟨n, hn⟩
  cases n with
  | zero => omega
  | succ a =>
      simpa only [penaltyHessian, PNat.mk_coe, Nat.cast_add, Nat.cast_one] using
        hb a ε η hε hη x.val
          (fun k => by simpa only [PNat.mk_coe, Nat.cast_add, Nat.cast_one] using (hx.2.1 k).1) i j

/-- See Subsection 6.1 of the paper: a uniform absolute internal-entry bound on the
common event, obtained by counting only retained internal intervals. -/
theorem internal_entry_upper (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : InverseTemperature) (n : ℕ+) (d : ℕ),
      4*(n : ℕ) ≤ (n : ℕ)+d+1 → ∀ η : ℝ, η ≤ 1-s.val/2 →
      ∀ (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1)),
      x ∈ goodSet s n d η → ∀ a b : Fin (n : ℕ),
      |BoundaryEntries.physicalInternal β s n d x a b| ≤
        C*(n : ℝ)^((s.val+2)*η) := by
  let D := 2*(s.val*(s.val+1)*PeriodicPower.bound (s.val+2) (by linarith [s.property.1]))
  have hD : 0 < D := by
    dsimp only [D]
    have := PeriodicPower.bound_pos (s.val+2) (by linarith [s.property.1])
    have := s.property.1
    positivity
  refine ⟨D*(1+1/s.val), by have := s.property.1; positivity, ?_⟩
  intro β n d hn η hη x hx a b
  let N := ((n : ℕ)+d).succPNat
  have hn2 : 2*(n : ℕ) ≤ (N : ℕ) := by dsimp only [N, Nat.succPNat_coe]; omega
  have hmass : 2*(∑ i, x.val i) ≤ ((n+d : ℕ)+1 : ℝ) := by
    have hh := goodSet_mass_le s n d η hη x hx
    have hN : 4*(n : ℝ) ≤ ((n+d : ℕ)+1 : ℝ) := by exact_mod_cast hn
    linarith
  let F := fun (i : Fin (N : ℕ)) (r : Fin ((N : ℕ)/2)) =>
    if IntervalBoundary.IsInternal N n (i,r) then
      BoundaryEntries.conditionalIntervalWeight β s n d r i x else 0
  have hF (i) (r) : |F i r| ≤
      (D*(n : ℝ)^((s.val+2)*η))*(r.val+1 : ℝ)^(-s.val-2) := by
    dsimp only [F]
    split_ifs with hi
    · rw [abs_of_nonneg (BoundaryEntries.conditionalIntervalWeight_nonneg β s n d r i x)]
      exact internal_coefficient_upper_internal β s n d (by omega) η x hx hmass i r hi
    · rw [abs_zero]; positivity
  have hh := PhysicalCore.Internal.signed_interval_entry_bound N s.property.1
    (by positivity) F hF (a.castLE (by omega)) (b.castLE (by omega))
  have he : BoundaryEntries.physicalInternal β s n d x a b =
      ∑ i, ∑ r, F i r *
        (if a.castLE (by omega : (n : ℕ) ≤ (N : ℕ)) ∈ cyclicIndexInterval N i (r.val+1) then 1 else 0) *
        (if b.castLE (by omega : (n : ℕ) ≤ (N : ℕ)) ∈ cyclicIndexInterval N i (r.val+1) then 1 else 0) := by
    rw [PhysicalCore.physicalInternal_reference_intervals β s n d (by omega) N hn2 x a b]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro r _
    by_cases hi : IntervalBoundary.IsInternal N n (i,r)
    · by_cases ha : a.castLE (by omega : (n : ℕ) ≤ (N : ℕ)) ∈ cyclicIndexInterval N i (r.val+1) <;>
        by_cases hb : b.castLE (by omega : (n : ℕ) ≤ (N : ℕ)) ∈ cyclicIndexInterval N i (r.val+1) <;>
        simp only [hi, ha, hb, F, dite_true, ite_true, ite_false, and_self, and_false,
          false_and, mul_one, mul_zero]
      rfl
    · simp only [hi, F, dite_false, ite_false, zero_mul]
  rw [he]
  exact hh.trans (by
    have hw := Real.rpow_le_one_of_one_le_of_nonpos
      (show 1 ≤ 1+(Riesz1.cyclicIndexDistance N (a.castLE (by omega)) (b.castLE (by omega)) : ℝ) by exact le_add_of_nonneg_right (Nat.cast_nonneg _))
      (by linarith [s.property.1] : -s.val ≤ 0)
    calc
      _ ≤ (D*(n : ℝ)^((s.val+2)*η))*(1+1/s.val) :=
        mul_le_of_le_one_right (by have := s.property.1; positivity) hw
      _ = _ := by ring)

/-- See Subsection 6.1 of the paper: internal error in any smaller component period
at the prescribed polynomial scale. The bounded sizes include the differing
physical and reference antipodal conventions. -/
theorem internal_entry_error_component_period (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℕ) (β : InverseTemperature)
      (n : ℕ+) (d : ℕ) (_hn : 4*(n : ℕ) ≤ (n : ℕ)+d+1)
      (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : 2*(n : ℕ) ≤ (M : ℕ)),
      (M : ℕ) ≤ (n : ℕ)+d+1 → (n : ℝ)^(1/2+1/s.val) ≤ (M : ℝ) →
      ∀ η : ℝ, 0 ≤ η → η ≤ 1-s.val/2 →
      ∀ (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1)),
      x ∈ goodSet s n d η → ∀ a b : Fin (n : ℕ),
      |BoundaryEntries.physicalInternal β s n d x a b -
        BoundaryEntries.referenceInternal s M hM (⌊(n : ℝ)^η⌋₊^h) n (by omega) a b| ≤
        C*(n : ℝ)^((s.val+3+(h : ℝ))*η)*
          (1+(Nat.dist a.val b.val : ℝ))^(-1-s.val/2) := by
  obtain ⟨B,hB,hsame⟩ := internal_entry_error_same_period_internal s
  obtain ⟨D,hD,hperiod⟩ := LocalizedMatrix.referenceInternal_different_period s
  obtain ⟨E,hE,href⟩ := PhysicalCore.Internal.referenceInternal_entry_bound s
  obtain ⟨U,hU,hphys⟩ := internal_entry_upper s
  let T := (U+E)*(5 : ℝ)^(1+s.val/2)
  have hT : 0 < T := by dsimp only [T]; positivity
  refine ⟨B+D+T,by positivity,?_⟩
  intro h β n d hn M hM hnM hMN hscale η hη hηa x hx a b
  let N := ((n : ℕ)+d).succPNat
  have hN : 2 ≤ (N : ℕ) := by have := n.pos; dsimp only [N,Nat.succPNat_coe]; omega
  have hnN : (n : ℕ) ≤ (N : ℕ) := by dsimp only [N,Nat.succPNat_coe]; omega
  let K := ⌊(n : ℝ)^η⌋₊^h
  let v := (n : ℝ)^((s.val+3+(h : ℝ))*η)
  let w := (1+(Nat.dist a.val b.val : ℝ))^(-1-s.val/2)
  have hv : 1 ≤ v := Real.one_le_rpow (by exact_mod_cast n.pos)
    (by have := Nat.cast_nonneg h (α := ℝ); nlinarith [s.property.1])
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hd : Nat.dist a.val b.val < (n : ℕ) := by
    have := a.isLt; have := b.isLt; unfold Nat.dist; omega
  by_cases hlarge : 4 < (n : ℕ)
  · have hmass : 2*(∑ j, x.val j) ≤ ((n+d : ℕ)+1 : ℝ) := by
      have hh := goodSet_mass_le s n d η hηa x hx
      have hN : 4*(n : ℝ) ≤ ((n+d : ℕ)+1 : ℝ) := by exact_mod_cast hn
      linarith
    have hh := hsame h β n d hn η hη x hx hmass a b
    have hstrict := PhysicalCore.Internal.two_n_lt_polynomial_period s n M hlarge hscale
    have hp : |BoundaryEntries.referenceInternal s N hN K n hnN a b -
        BoundaryEntries.referenceInternal s M hM K n (by omega) a b| ≤ D*w :=
      (hperiod N M n hN hM hMN hstrict K a b).trans (by
        simpa only [w,mul_assoc] using mul_le_mul_of_nonneg_left
          (LocalizedMatrix.period_error_absorption s n M hscale hd) hD.le)
    have htri := abs_sub_le (BoundaryEntries.physicalInternal β s n d x a b)
      (BoundaryEntries.referenceInternal s N hN K n hnN a b)
      (BoundaryEntries.referenceInternal s M hM K n (by omega) a b)
    have hDv := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hD.le) hw
    change _ ≤ B*v*w at hh
    change _ ≤ (B+D+T)*v*w
    nlinarith only [htri,hh,hp,hDv,mul_nonneg hT.le (mul_nonneg (le_trans zero_le_one hv) hw)]
  · have hsmall : (n : ℕ) ≤ 4 := by omega
    have hP := hphys β n d hn η hηa x hx a b
    have hR := href M hM K n (by omega) a b
    have hR' : |BoundaryEntries.referenceInternal s M hM K n (by omega) a b| ≤ E :=
      hR.trans (mul_le_of_le_one_right hE.le (Real.rpow_le_one_of_one_le_of_nonpos
        (le_add_of_nonneg_right (Nat.cast_nonneg _)) (by linarith [s.property.1])))
    have hPv : (n : ℝ)^((s.val+2)*η) ≤ v := Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast n.pos) (by have := Nat.cast_nonneg h (α := ℝ); nlinarith)
    have hweight : 1 ≤ (5 : ℝ)^(1+s.val/2)*w := by
      have hp : (5 : ℝ)^(-1-s.val/2) ≤ w := Real.rpow_le_rpow_of_nonpos
        (by positivity) (by exact_mod_cast (by omega : 1+Nat.dist a.val b.val ≤ 5))
        (by linarith [s.property.1])
      have he : (5 : ℝ)^(1+s.val/2)*(5 : ℝ)^(-1-s.val/2) = 1 := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 5)]
        norm_num
      nlinarith only [mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 5) (1+s.val/2)),he]
    have htri := abs_sub_le (BoundaryEntries.physicalInternal β s n d x a b) 0
      (BoundaryEntries.referenceInternal s M hM K n (by omega) a b)
    simp only [sub_zero,zero_sub,abs_neg] at htri
    have hUv := mul_le_mul_of_nonneg_left hPv hU.le
    have hEv := mul_le_mul_of_nonneg_left hv hE.le
    have hTv := mul_le_mul_of_nonneg_left hweight
      (mul_nonneg (show 0 ≤ U+E by linarith) (le_trans zero_le_one hv))
    change _ ≤ (B+D+T)*v*w
    dsimp only [T] at *
    nlinarith only [hP,hUv,hR',htri,hEv,hTv,
      mul_nonneg (show 0 ≤ B+D by linarith) (mul_nonneg (le_trans zero_le_one hv) hw)]

/-- See Subsection 6.1 of the paper: upper bound for the complete measurable
interval family, including the two-sided penalty and both freezing branches. -/
theorem intervalWeight_upper (s : Riesz1.RieszExponent) (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : InverseTemperature)
      (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (_hn : 4*(n : ℕ) ≤ (n : ℕ)+d+1)
      (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : 2*(n : ℕ) ≤ (M : ℕ))
      (K : ℕ) (ε η t : ℝ), 0 ≤ ε → 0 ≤ η → η ≤ 1-s.val/2 →
      0 ≤ t → t ≤ 1 →
      ∀ (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1))
        (i : Fin (M : ℕ)) (r : Fin ((M : ℕ)/2)),
      intervalWeight β s n d e hde (by omega) M hM hnM K θ ε η t i r x ≤
        C*(n : ℝ)^((s.val+6)*η)*(r.val+1 : ℝ)^(-s.val-2) := by
  obtain ⟨B,hB,href⟩ := BoundaryEntries.referenceWeight_bound s
  obtain ⟨P,hP,hpen⟩ := penaltyHessian_good_bound θ
  let D := 2*(s.val*(s.val+1)*PeriodicPower.bound (s.val+2) (by linarith [s.property.1]))
  have hD : 0 < D := by
    dsimp only [D]
    have := PeriodicPower.bound_pos (s.val+2) (by linarith [s.property.1])
    have := s.property.1
    positivity
  refine ⟨D+P+B, by positivity, ?_⟩
  intro β n d e hde hn M hM hnM K ε η t hε hη hηa ht ht1 x i r
  let v := (n : ℝ)^((s.val+6)*η)
  let w := (r.val+1 : ℝ)^(-s.val-2)
  have hv : 1 ≤ v := Real.one_le_rpow (by exact_mod_cast n.pos) (by nlinarith [s.property.1])
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hDv : (n : ℝ)^((s.val+2)*η) ≤ v :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast n.pos) (by nlinarith)
  have hPv : (n : ℝ)^(4*η) ≤ v :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast n.pos) (by nlinarith [s.property.1])
  have hRef : BoundaryEntries.referenceWeight s M hM K (i,r) ≤ (D+P+B)*v*w := by
    have hh := href M hM K (i,r)
    have hBv := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hB.le) hw
    have hrest : 0 ≤ (D+P)*v*w := by positivity
    change _ ≤ (D+P+B)*v*w
    nlinarith only [hh,hBv,hrest]
  by_cases hx : x ∈ goodSet s n d η
  · by_cases hi : IntervalBoundary.IsInternal M n (i,r)
    · rw [intervalWeight, ite_eq_left hx, dite_eq_left hi]
      have hend := (PhysicalCore.Internal.internal_iff_end_le M n hnM i r).mp hi
      let i₀ : Fin ((n : ℕ)+d+1) := ⟨i.val, by omega⟩
      let r₀ : Fin (((n : ℕ)+d+1)/2) := ⟨r.val, by omega⟩
      let i₁ : Fin ((n : ℕ)+e+1) := ⟨i.val, by omega⟩
      let r₁ : Fin (((n : ℕ)+e+1)/2) := ⟨r.val, by omega⟩
      have hi₀ : IntervalBoundary.IsInternal ((n : ℕ)+d).succPNat n (i₀,r₀) :=
        (PhysicalCore.Internal.internal_iff_end_le _ _ (by simp only [Nat.succPNat_coe]; omega) _ _).mpr hend
      have hi₁ : IntervalBoundary.IsInternal ((n : ℕ)+e).succPNat n (i₁,r₁) :=
        (PhysicalCore.Internal.internal_iff_end_le _ _ (by simp only [Nat.succPNat_coe]; omega) _ _).mpr hend
      have hx₁ := largerChart_goodSet s n d e hde η x hx
      have hmass₀ : 2*(∑ j, x.val j) ≤ ((n+d : ℕ)+1 : ℝ) := by
        have hh := goodSet_mass_le s n d η hηa x hx
        have hN : 4*(n : ℝ) ≤ ((n+d : ℕ)+1 : ℝ) := by exact_mod_cast hn
        linarith
      have hmass₁ : 2*(∑ j, (largerChart n d e hde x).val j) ≤ ((n+e : ℕ)+1 : ℝ) := by
        have hh : ((n+d : ℕ)+1 : ℝ) ≤ ((n+e : ℕ)+1 : ℝ) := by exact_mod_cast (show (n : ℕ)+d+1 ≤ (n : ℕ)+e+1 by omega)
        exact hmass₀.trans hh
      have h₀ := internal_coefficient_upper_internal β s n d (by omega) η x hx hmass₀ i₀ r₀ hi₀
      have h₁ := internal_coefficient_upper_internal β s n e (by omega) η
        (largerChart n d e hde x) hx₁ hmass₁ i₁ r₁ hi₁
      have hp := hpen s n d ε η hε hη x hx
        ⟨i.val,by omega⟩ ⟨i.val,by omega⟩
      simp only [ite_true] at hp
      have hp' := (le_abs_self _).trans hp
      have hcomb :
          (1-t)*BoundaryEntries.conditionalIntervalWeight β s n d r₀ i₀ x +
          t*BoundaryEntries.conditionalIntervalWeight β s n e r₁ i₁ (largerChart n d e hde x) ≤
            D*(n : ℝ)^((s.val+2)*η)*w := by
        have hy := mul_le_mul_of_nonneg_left h₀ (sub_nonneg.mpr ht1)
        have hz := mul_le_mul_of_nonneg_left h₁ ht
        dsimp only [D,w,r₀,r₁] at *
        nlinarith only [hy,hz]
      have hupper := mul_le_mul_of_nonneg_left hDv hD.le
      have hpupper := mul_le_mul_of_nonneg_left hPv hP.le
      by_cases hr0 : r.val = 0
      · simp only [ite_eq_left hr0]
        have hw1 : w = 1 := by simp [w,hr0]
        change _ ≤ (D+P+B)*v*w
        rw [hw1] at hcomb ⊢
        have hBv : 0 ≤ B*v := by positivity
        simp only [mul_one]
        simpa only [mul_one] using (show
          (1-t)*BoundaryEntries.conditionalIntervalWeight β s n d r₀ i₀ x +
          t*BoundaryEntries.conditionalIntervalWeight β s n e r₁ i₁ (largerChart n d e hde x) +
          penaltyHessian n θ ε x.val ⟨i.val,by omega⟩ ⟨i.val,by omega⟩ ≤
          (D+P+B)*v by nlinarith only [hcomb,hupper,hp',hpupper,hBv])
      · simp only [ite_eq_right hr0, add_zero]
        have hrest : 0 ≤ (P+B)*v*w := by positivity
        have hDu := mul_le_mul_of_nonneg_right hupper hw
        change _ ≤ (D+P+B)*v*w
        nlinarith only [hcomb,hDu,hrest]
    · simp only [intervalWeight, ite_eq_left hx, dite_eq_right hi]; exact hRef
  · simp only [intervalWeight, ite_eq_right hx]; exact hRef


/-- See Subsection 6.1 of the paper: absolute long-interval lower bound on the
exact threshold region of the matrix predicate. -/
theorem intervalWeight_threshold_lower (s : Riesz1.RieszExponent) :
    ∃ c : ℝ, 0 < c ∧ ∀ (h : ℕ) (γ : ℝ), (h : ℝ) ≤ γ →
      ∀ (β : InverseTemperature) (n : ℕ+) (d e : ℕ) (hde : d ≤ e)
      (hn : 2*(n : ℕ) ≤ (n : ℕ)+d+1)
      (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : 2*(n : ℕ) ≤ (M : ℕ))
      (θ : PhysicalCutoff) (ε η t : ℝ), 0 ≤ η → 0 ≤ t → t ≤ 1 →
      ∀ (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1))
        (i : Fin (M : ℕ)) (r : Fin ((M : ℕ)/2)),
      (n : ℝ)^(γ*η) ≤ (r.val+1 : ℝ) →
      c*(n : ℝ)^(-(s.val+2)*η)*(r.val+1 : ℝ)^(-s.val-2) ≤
        intervalWeight β s n d e hde hn M hM hnM (⌊(n : ℝ)^η⌋₊^h) θ ε η t i r x := by
  obtain ⟨c,hc,_,hl⟩ := intervalWeight_reference_lower s
  obtain ⟨b,hb,href⟩ := PhysicalCore.referenceWeight_lower s
  refine ⟨c*b,mul_pos hc hb,?_⟩
  intro h γ hγ β n d e hde hn M hM hnM θ ε η t hη ht ht1 x i r hr
  let K := ⌊(n : ℝ)^η⌋₊^h
  have hK : K ≤ r.val+1 := by
    have hh : (K : ℝ) ≤ (n : ℝ)^(γ*η) := by
      calc
        _ = (⌊(n : ℝ)^η⌋₊ : ℝ)^h := by rw [Nat.cast_pow]
        _ ≤ ((n : ℝ)^η)^h := pow_le_pow_left₀ (Nat.cast_nonneg _)
          (Nat.floor_le (Real.rpow_nonneg (by positivity) _)) h
        _ = (n : ℝ)^((h : ℝ)*η) := by
          rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity : (0 : ℝ) ≤ n)]
          congr 1; ring
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast n.pos)
          (mul_le_mul_of_nonneg_right hγ hη)
    exact_mod_cast hh.trans hr
  have hh := mul_le_mul_of_nonneg_left (href M hM K i r hK)
    (show 0 ≤ c*(n : ℝ)^(-(s.val+2)*η) by positivity)
  have hh' := hl β n d e hde hn M hM hnM K θ ε η t hη ht ht1 x i r
  simp only [Nat.cast_add,Nat.cast_one] at hh
  apply le_trans _ hh'
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hh

/-- See Subsection 6.1 of the paper: improved active-entry reference error for the
actual convex interpolation and two-sided forcing, on both event branches. -/
theorem matrix_active_error (s : Riesz1.RieszExponent) (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℕ) (β : InverseTemperature)
      (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (_hn : 4*(n : ℕ) ≤ (n : ℕ)+d+1)
      (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : 2*(n : ℕ) ≤ (M : ℕ)),
      (M : ℕ) ≤ (n : ℕ)+d+1 → (n : ℝ)^(1/2+1/s.val) ≤ (M : ℝ) →
      ∀ ε η t : ℝ, 0 ≤ ε → 0 ≤ η → η ≤ 1-s.val/2 → 0 ≤ t → t ≤ 1 →
      ∀ (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1)) (a b : Fin (n : ℕ)),
      |matrix β s n d e hde M hM (by omega) (⌊(n : ℝ)^η⌋₊^h) θ ε η t x
          (a.castLE (by omega)) (b.castLE (by omega)) -
        ((2 : ℝ) • referenceIntervalMatrix s M hM (⌊(n : ℝ)^η⌋₊^h))
          (a.castLE (by omega)) (b.castLE (by omega))| ≤
        C*(n : ℝ)^((s.val+7+(h : ℝ))*η)*
          (1+(Nat.dist a.val b.val : ℝ))^(-1-s.val/2) := by
  obtain ⟨E,hE,he⟩ := internal_entry_error_component_period s
  obtain ⟨P,hP,hp⟩ := penaltyHessian_good_bound θ
  refine ⟨E+P,by positivity,?_⟩
  intro h β n d e hde hn M hM hnM hMN hscale ε η t hε hη hηa ht ht1 x a b
  let K := ⌊(n : ℝ)^η⌋₊^h
  let v := (n : ℝ)^((s.val+7+(h : ℝ))*η)
  let w := (1+(Nat.dist a.val b.val : ℝ))^(-1-s.val/2)
  have hw : 0 ≤ w := by dsimp only [w]; positivity
  have hmon : (n : ℝ)^((s.val+3+(h : ℝ))*η) ≤ v :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast n.pos) (by nlinarith)
  have hmonP : (n : ℝ)^(4*η) ≤ v := Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast n.pos) (by have := Nat.cast_nonneg h (α := ℝ); nlinarith [s.property.1])
  by_cases hx : x ∈ goodSet s n d η
  · have hy := he h β n d hn M hM hnM hMN hscale η hη hηa x hx a b
    have hz := he h β n e (by omega) M hM hnM (by omega) hscale η hη hηa
      (largerChart n d e hde x) (largerChart_goodSet s n d e hde η x hx) a b
    let A := BoundaryEntries.referenceInternal s M hM K n (by omega)
    have herror : |(1-t)*(BoundaryEntries.physicalInternal β s n d x a b-A a b) +
        t*(BoundaryEntries.physicalInternal β s n e (largerChart n d e hde x) a b-A a b)| ≤ E*v*w := by
      have htri := abs_add_le
        ((1-t)*(BoundaryEntries.physicalInternal β s n d x a b-A a b))
        (t*(BoundaryEntries.physicalInternal β s n e (largerChart n d e hde x) a b-A a b))
      rw [abs_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr ht1),abs_of_nonneg ht] at htri
      have hy' := mul_le_mul_of_nonneg_left hy (sub_nonneg.mpr ht1)
      have hz' := mul_le_mul_of_nonneg_left hz ht
      have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmon hE.le) hw
      dsimp only [A] at htri
      change _ ≤ E*v*w
      dsimp only [v,w,K] at *
      nlinarith only [htri,hy',hz',hm]
    have hpen : |penaltyHessian n θ ε x.val a b| ≤ P*v*w := by
      have hh := hp s n d ε η hε hη x hx a b
      by_cases hab : a = b
      · subst b
        simp only [ite_true] at hh
        have hw1 : w = 1 := by simp [w]
        rw [hw1,mul_one]
        exact hh.trans (mul_le_mul_of_nonneg_left hmonP hP.le)
      · simp only [hab,ite_false] at hh
        exact hh.trans (by positivity)
    have heq : matrix β s n d e hde M hM (by omega) K θ ε η t x
        (a.castLE (by omega)) (b.castLE (by omega)) -
        ((2 : ℝ) • referenceIntervalMatrix s M hM K)
          (a.castLE (by omega)) (b.castLE (by omega)) =
        penaltyHessian n θ ε x.val a b +
          ((1-t)*(BoundaryEntries.physicalInternal β s n d x a b-A a b) +
            t*(BoundaryEntries.physicalInternal β s n e (largerChart n d e hde x) a b-A a b)) := by
      rw [matrix_active]
      have href := BoundaryEntries.referenceInternal_add_crossing s M hM K n (by omega) a b
      simp only [activeBlock,ite_eq_left hx,internalBlock,Matrix.add_apply,
        Matrix.smul_apply,smul_eq_mul]
      dsimp only [A]
      linarith only [href]
    change _ ≤ (E+P)*v*w
    rw [heq]
    exact (abs_add_le _ _).trans ((add_le_add hpen herror).trans_eq (by ring))
  · rw [matrix_off_goodSet β s n d e hde M hM (by omega) K θ ε η t x hx,
      sub_self,abs_zero]
    positivity

/-- See Subsection 6.1 of the paper, all-size internal-matrix clause: the exact
matrix satisfies every clause of the predicate. The statement
is pointwise before choosing any measure.  The component period is allowed to differ from
both physical periods. -/
theorem matrix_bounds (s : Riesz1.RieszExponent) (θ : PhysicalCutoff) (h : ℕ) :
    let κ := (s.val+7+(h : ℝ))+(s.val+2+(h : ℝ)*(1+s.val))
    let γ := (h : ℝ)+1
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (β : InverseTemperature) (n : ℕ+) (d e : ℕ) (hde : d ≤ e)
      (_hn : 4*(n : ℕ) ≤ (n : ℕ)+d+1)
      (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : 2*(n : ℕ) ≤ (M : ℕ)),
      (M : ℕ) ≤ (n : ℕ)+d+1 → (n : ℝ)^(1/2+1/s.val) ≤ (M : ℝ) →
      ∀ ε η t : ℝ, 0 ≤ ε → 0 ≤ η → η ≤ 1-s.val/2 → 0 ≤ t → t ≤ 1 →
      let K := ⌊(n : ℝ)^η⌋₊^h
      K ≤ (M : ℕ)/4 →
      ∀ μ : Measure (AffineSimplex.chartDomain n ((n+d : ℕ)+1)),
      PeriodizedMatrixBounds (ν := μ) s n M hM K C κ γ η
        (matrix β s n d e hde M hM (by omega) K θ ε η t) := by
  intro κ γ
  obtain ⟨c₁,hc₁,hcoerc⟩ := matrix_cutoff_coercivity s
  obtain ⟨c₂,hc₂,hlower⟩ := intervalWeight_threshold_lower s
  obtain ⟨U,hU,hupper⟩ := intervalWeight_upper s θ
  obtain ⟨E,hE,hentry⟩ := matrix_active_error s θ
  let kE := s.val+7+(h : ℝ)
  let kC := s.val+2+(h : ℝ)*(1+s.val)
  have hkE : 0 < kE := by dsimp only [kE]; have := Nat.cast_nonneg h (α := ℝ); linarith [s.property.1]
  have hkC : 0 < kC := by dsimp only [kC]; have := s.property.1; positivity
  let C := 1+U+E+c₁⁻¹+c₂⁻¹
  have hC : 1 ≤ C := by dsimp only [C]; linarith [inv_pos.mpr hc₁,inv_pos.mpr hc₂]
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hCU : U ≤ C := by dsimp only [C]; linarith [inv_pos.mpr hc₁,inv_pos.mpr hc₂]
  have hCE : E ≤ C := by dsimp only [C]; linarith [inv_pos.mpr hc₁,inv_pos.mpr hc₂]
  have hcC₁ : C⁻¹ ≤ c₁ := (inv_le_comm₀ hC0 hc₁).mpr (by dsimp only [C]; linarith [inv_pos.mpr hc₁,inv_pos.mpr hc₂])
  have hcC₂ : C⁻¹ ≤ c₂ := (inv_le_comm₀ hC0 hc₂).mpr (by dsimp only [C]; linarith [inv_pos.mpr hc₁,inv_pos.mpr hc₂])
  refine ⟨C,hC,?_⟩
  intro β n d e hde hn M hM hnM hMN hscale ε η t hε hη hηa ht ht1 K hKM μ
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by positivity
  have lower (c l : ℝ) (hc : 0 < c) (hcl : C⁻¹ ≤ c) (hl : l ≤ κ) :
      C⁻¹*(n : ℝ)^(-κ*η) ≤ c*(n : ℝ)^(-l*η) :=
    mul_le_mul hcl (Real.rpow_le_rpow_of_exponent_le hn1
      (by nlinarith only [hl,hη])) (Real.rpow_nonneg hn0.le _) hc.le
  have upper (c l : ℝ) (_hc : 0 ≤ c) (hcl : c ≤ C) (hl : l ≤ κ) :
      c*(n : ℝ)^(l*η) ≤ C*(n : ℝ)^(κ*η) :=
    mul_le_mul hcl (Real.rpow_le_rpow_of_exponent_le hn1
      (mul_le_mul_of_nonneg_right hl hη)) (Real.rpow_nonneg hn0.le _) hC0.le
  have hkEκ : kE ≤ κ := by dsimp only [κ]; linarith
  have hkCκ : kC ≤ κ := by dsimp only [κ]; linarith
  have hkUκ : s.val+6 ≤ κ := by dsimp only [kE] at hkEκ; have := Nat.cast_nonneg h (α := ℝ); linarith
  have hksκ : s.val+2 ≤ κ := by
    have hh : 0 ≤ (h : ℝ)*(1+s.val) := by have := s.property.1; positivity
    dsimp only [kC] at hkCκ
    linarith
  refine ⟨measurable_matrix β s n d e hde M hM (by omega) K θ ε η t,?_,?_⟩
  · apply ae_of_all
    intro x
    have hsym := matrix_symmetric β s n d e hde M hM (by omega) K θ ε η t x
    have hHerm : (matrix β s n d e hde M hM (by omega) K θ ε η t x).IsHermitian := by
      ext a b
      simp only [Matrix.conjTranspose_apply,star_trivial,hsym]
    refine ⟨hsym,matrix_exterior β s n d e hde M hM (by omega) K θ ε η t x,?_,?_⟩
    · intro z
      have hh := (FiniteMatrixOrder.smul_one_le_iff hHerm _).mp
        (hcoerc h β n d e hde (by omega) M hM hnM θ ε η t hη ht ht1 hKM x) z
      have hh' : c₁*(n : ℝ)^(-kC*η)*(∑ i,z i^2) ≤
          ∑ i,∑ j,z i*matrix β s n d e hde M hM (by omega) K θ ε η t x i j*z j := by
        simpa only [kC,Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc,pow_two] using hh
      exact (mul_le_mul_of_nonneg_right (lower c₁ kC hc₁ hcC₁ hkCκ)
        (Finset.sum_nonneg (fun i _ => sq_nonneg (z i)))).trans hh'
    · intro a b ha hb
      let a' : Fin (n : ℕ) := ⟨a.val,ha⟩
      let b' : Fin (n : ℕ) := ⟨b.val,hb⟩
      have ha' : a'.castLE (by omega : (n : ℕ) ≤ (M : ℕ)) = a := Fin.ext rfl
      have hb' : b'.castLE (by omega : (n : ℕ) ≤ (M : ℕ)) = b := Fin.ext rfl
      have he := hentry h β n d e hde hn M hM hnM hMN hscale ε η t hε hη hηa ht ht1 x a' b'
      have hd := PhysicalCore.Internal.active_distance M n hnM a' b'
      rw [ha',hb'] at he hd
      rw [← hd] at he
      exact he.trans (mul_le_mul_of_nonneg_right (upper E kE hE.le hCE hkEκ) (by positivity))
  · refine ⟨intervalWeight β s n d e hde (by omega) M hM hnM K θ ε η t,
      measurable_intervalWeight β s n d e hde (by omega) M hM hnM K θ ε η t,
      ae_of_all _ (fun x => ?_)⟩
    refine ⟨fun i r => ⟨intervalWeight_nonneg β s n d e hde (by omega) M hM hnM K θ ε η t ht ht1 i r x,?_,?_⟩,
      matrix_interval_quadratic β s n d e hde (by omega) M hM hnM K θ ε η t x⟩
    · have hu := mul_le_mul_of_nonneg_right (upper U (s.val+6) hU.le hCU hkUκ)
        (Real.rpow_nonneg (by positivity : 0 ≤ (r.val+1 : ℝ)) (-s.val-2))
      exact (hupper β n d e hde hn M hM hnM K ε η t hε hη hηa ht ht1 x i r).trans
        (by simpa only [Nat.cast_add,Nat.cast_one] using hu)
    · intro hr
      simp only [Nat.cast_add,Nat.cast_one] at hr ⊢
      exact (mul_le_mul_of_nonneg_right (lower c₂ (s.val+2) hc₂ hcC₂ hksκ) (by positivity)).trans
        (hlower h γ (by dsimp only [γ]; linarith) β n d e hde (by omega) M hM hnM θ ε η t hη ht ht1 x i r hr)

/-- See Subsection 6.1 of the paper: the physical internal coefficients agree with
those of every fixed-exterior assembly. Only retained coordinates enter
these intervals. The identity holds on the whole positive active chart. -/
theorem internal_coefficient_assemble (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (d : ℕ) (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1))
    (y : EuclideanSpace ℝ (Fin (d+1)))
    (i : Fin ((n : ℕ)+d+1)) (r : Fin (((n : ℕ)+d+1)/2))
    (hi : IntervalBoundary.IsInternal ((n : ℕ)+d).succPNat n (i,r)) :
    BoundaryEntries.conditionalIntervalWeight β s n d r i x =
      BoundaryEntries.intervalWeight s ((n : ℕ)+d).succPNat r i
        (RetainedSimplex.assemble n d (Equiv.refl _) x.val y) := by
  rw [PhysicalCore.conditionalIntervalWeight_internal β s n d x r i hi]
  have he : cyclicGapSum ((n : ℕ)+d).succPNat i (r.val+1)
      (WithLp.ofLp (RetainedSimplex.chart n d ((n+d : ℕ)+1) (Equiv.refl _) (x.val,0))) =
      cyclicGapSum ((n : ℕ)+d).succPNat i (r.val+1)
      (WithLp.ofLp (RetainedSimplex.assemble n d (Equiv.refl _) x.val y)) := by
    rw [← sum_cyclicIndexInterval_eq_cyclicGapSum _ _ (by have := r.isLt; simp only [Nat.succPNat_coe]; omega),
      ← sum_cyclicIndexInterval_eq_cyclicGapSum _ _ (by have := r.isLt; simp only [Nat.succPNat_coe]; omega)]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn := hi j hj
    let j' : Fin (n : ℕ) := ⟨j.val,hjn⟩
    have hj₀ : (j'.castAdd d).castSucc = j := Fin.ext rfl
    have hj₁ : j'.castAdd (d+1) = j := Fin.ext rfl
    change RetainedSimplex.chart n d _ (Equiv.refl _) (x.val,0) j =
      RetainedSimplex.assemble n d (Equiv.refl _) x.val y j
    have hret := RetainedSimplex.chart_retained n d ((n+d : ℕ)+1) (Equiv.refl _) x.val 0 j'
    simp only [Equiv.coe_refl,Function.id_def] at hret
    rw [← hj₀,hret]
    rw [hj₀,← hj₁]
    simp [RetainedSimplex.assemble,RetainedSimplex.join]
  simp only [BoundaryEntries.intervalWeight,he]

/-- See Subsection 6.1 of the paper: the exact physical internal block is the
internal interval matrix used by the fixed-exterior auxiliary theorem. -/
theorem physicalInternal_eq_internalMatrix (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (d : ℕ) (hn : 2*(n : ℕ) ≤ (n : ℕ)+d+1)
    (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1))
    (y : EuclideanSpace ℝ (Fin (d+1))) :
    BoundaryEntries.physicalInternal β s n d x =
      IntervalBoundary.internalMatrix ((n : ℕ)+d).succPNat n (by simp only [Nat.succPNat_coe]; omega)
        (fun ir => BoundaryEntries.intervalWeight s ((n : ℕ)+d).succPNat ir.2 ir.1
          (RetainedSimplex.assemble n d (Equiv.refl _) x.val y)) := by
  ext a b
  rw [PhysicalCore.physicalInternal_reference_intervals β s n d hn ((n : ℕ)+d).succPNat hn x a b]
  simp only [IntervalBoundary.internalMatrix,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro r _
  by_cases hi : IntervalBoundary.IsInternal ((n : ℕ)+d).succPNat n (i,r)
  · rw [dite_eq_left hi,ite_eq_left hi]
    simp only [Fin.eta]
    rw [internal_coefficient_assemble β s n d x y i r hi]
    simp only [IntervalBoundary.rankOne,IntervalBoundary.trace,Finset.mem_filter,
      Finset.mem_univ,true_and]
    split_ifs <;> simp_all only [mul_one,mul_zero]
  · simp only [hi,dite_false,ite_false]

/-- See Subsection 6.1 of the paper: every fixed-exterior internal interval field
is Borel on the full ambient coordinate space. -/
theorem measurable_assembled_internal (s : Riesz1.RieszExponent) (n : ℕ+) (d : ℕ)
    (hn : (n : ℕ) ≤ (n : ℕ)+d+1) (y : EuclideanSpace ℝ (Fin (d+1)))
    (a b : Fin (n : ℕ)) :
    Measurable (fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      IntervalBoundary.internalMatrix ((n : ℕ)+d).succPNat n hn
        (fun ir => BoundaryEntries.intervalWeight s ((n : ℕ)+d).succPNat ir.2 ir.1
          (RetainedSimplex.assemble n d (Equiv.refl _) x y)) a b) := by
  have : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin (n : ℕ)) ×
      EuclideanSpace ℝ (Fin (d+1))) := Prod.continuousSMul
  have hf : Measurable (fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      RetainedSimplex.assemble n d (Equiv.refl _) x y) :=
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.refl _)).continuous.comp
      ((RetainedSimplex.join n (d+1)).toContinuousLinearEquiv.continuous.comp
        (continuous_id.prodMk continuous_const))).measurable
  simp only [IntervalBoundary.internalMatrix]
  apply Finset.measurable_sum
  intro ir _
  by_cases hi : IntervalBoundary.IsInternal ((n : ℕ)+d).succPNat n ir
  · simpa only [hi,ite_true,Function.comp_apply] using
      ((BoundaryEntries.measurable_intervalWeight s ((n : ℕ)+d).succPNat ir.2 ir.1).comp hf).mul_const
        (IntervalBoundary.rankOne (IntervalBoundary.trace ((n : ℕ)+d).succPNat n hn ir.1 (ir.2.val+1)) a b)
  · simp only [hi,ite_false]
    exact measurable_const

/-- Internal transport for Subsection 6.1: the all-size bounds
hold for the literal ambient matrix appearing in
`AuxiliaryMean.fixed_exterior_auxiliary_internal`, under any measure supported
on the positive active chart. The support premise is measure geometry, not
a coefficient estimate. No exterior expectation remains in the matrix. -/
theorem physical_matrix_bounds_internal (s : Riesz1.RieszExponent)
    (θ : PhysicalCutoff) (h : ℕ) :
    let κ := (s.val+7+(h : ℝ))+(s.val+2+(h : ℝ)*(1+s.val))
    let γ := (h : ℝ)+1
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (β : InverseTemperature) (n : ℕ+) (d e : ℕ) (hde : d ≤ e)
      (_hn : 4*(n : ℕ) ≤ (n : ℕ)+d+1)
      (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : 2*(n : ℕ) ≤ (M : ℕ)),
      (M : ℕ) ≤ (n : ℕ)+d+1 → (n : ℝ)^(1/2+1/s.val) ≤ (M : ℝ) →
      ∀ ε η t : ℝ, 0 ≤ ε → 0 ≤ η → η ≤ 1-s.val/2 → 0 ≤ t → t ≤ 1 →
      let K := ⌊(n : ℝ)^η⌋₊^h
      K ≤ (M : ℕ)/4 →
      ∀ (y : EuclideanSpace ℝ (Fin (d+1))) (z : EuclideanSpace ℝ (Fin (e+1))),
      let hn₀ : (n : ℕ) ≤ (M : ℕ) := by omega
      let H := (2 : ℝ) • referenceIntervalMatrix s M hM K
      let Py := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
        IntervalBoundary.internalMatrix ((n : ℕ)+d).succPNat n (by simp only [Nat.succPNat_coe]; omega)
          (fun ir => BoundaryEntries.intervalWeight s ((n : ℕ)+d).succPNat ir.2 ir.1
            (RetainedSimplex.assemble n d (Equiv.refl _) x y))
      let Pz := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
        IntervalBoundary.internalMatrix ((n : ℕ)+e).succPNat n (by simp only [Nat.succPNat_coe]; omega)
          (fun ir => BoundaryEntries.intervalWeight s ((n : ℕ)+e).succPNat ir.2 ir.1
            (RetainedSimplex.assemble n e (Equiv.refl _) x z))
      let A0 := fun x =>
        (if WithLp.ofLp x ∈ goodBlockEvent s.val n ((n : ℕ)+d).succPNat η then
          penaltyHessian n θ ε x + (1-t) • Py x + t • Pz x
        else BoundaryEntries.referenceInternal s M hM K n hn₀) +
          BoundaryEntries.referenceCrossing s M hM K n hn₀
      let Mphys := fun x => fun i j : Fin (M : ℕ) =>
        if hi : i.val < (n : ℕ) then
          if hj : j.val < (n : ℕ) then A0 x ⟨i.val,hi⟩ ⟨j.val,hj⟩ else H i j
        else H i j
      ∀ μ : Measure (EuclideanSpace ℝ (Fin (n : ℕ))),
      (∀ᵐ x ∂μ, x ∈ AffineSimplex.chartDomain n ((n+d : ℕ)+1)) →
      PeriodizedMatrixBounds (ν := μ) s n M hM K C κ γ η Mphys := by
  intro κ γ
  obtain ⟨C,hC,hbounds⟩ := matrix_bounds s θ h
  refine ⟨C,hC,?_⟩
  intro β n d e hde hn M hM hnM hMN hscale ε η t hε hη hηa ht ht1 K hKM y z hn₀ H Py Pz A0 Mphys μ hμ
  let S := AffineSimplex.chartDomain n ((n+d : ℕ)+1)
  let f : S → EuclideanSpace ℝ (Fin (n : ℕ)) := Subtype.val
  have hf : MeasurableEmbedding f := MeasurableEmbedding.subtype_coe (AffineSimplex.isOpen_chartDomain n _).measurableSet
  have heq : Mphys ∘ f = matrix β s n d e hde M hM hn₀ K θ ε η t := by
    funext x i j
    have hy : Py x.val = BoundaryEntries.physicalInternal β s n d x :=
      (physicalInternal_eq_internalMatrix β s n d (by omega) x y).symm
    have hz : Pz x.val = BoundaryEntries.physicalInternal β s n e (largerChart n d e hde x) :=
      (physicalInternal_eq_internalMatrix β s n e (by omega) (largerChart n d e hde x) z).symm
    simp only [Function.comp_apply,Mphys,matrix,f]
    split_ifs with hi hj
    · simp only [A0,activeBlock,internalBlock,hy,hz,goodSet,Set.mem_ofPred_eq,
        add_assoc]
    all_goals rfl
  have hgood : MeasurableSet {x : EuclideanSpace ℝ (Fin (n : ℕ)) |
      WithLp.ofLp x ∈ goodBlockEvent s.val n ((n : ℕ)+d).succPNat η} :=
    (InterpolantLocalLaws.measurableSet_goodBlockEvent s.val n _ η).preimage
      (Measurable.of_eval (fun i => (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable))
  have hmeas (i j : Fin (M : ℕ)) : Measurable (fun x => Mphys x i j) := by
    dsimp only [Mphys]
    split_ifs
    · have hPy := measurable_assembled_internal s n d (by omega) y
      have hPz := measurable_assembled_internal s n e (by omega) z
      have he : (fun x => A0 x ⟨i.val,by omega⟩ ⟨j.val,by omega⟩) = fun x =>
          (if WithLp.ofLp x ∈ goodBlockEvent s.val n ((n : ℕ)+d).succPNat η then
            penaltyHessian n θ ε x ⟨i.val,by omega⟩ ⟨j.val,by omega⟩ +
            (1-t)*Py x ⟨i.val,by omega⟩ ⟨j.val,by omega⟩ +
            t*Pz x ⟨i.val,by omega⟩ ⟨j.val,by omega⟩
          else BoundaryEntries.referenceInternal s M hM K n hn₀ ⟨i.val,by omega⟩ ⟨j.val,by omega⟩) +
            BoundaryEntries.referenceCrossing s M hM K n hn₀ ⟨i.val,by omega⟩ ⟨j.val,by omega⟩ := by
        funext x
        dsimp only [A0]
        split_ifs <;> rfl
      rw [he]
      exact ((((measurable_penaltyHessian n θ ε _ _).add
        ((hPy _ _).const_mul (1-t))).add ((hPz _ _).const_mul t)).ite hgood measurable_const).add_const _
    all_goals exact measurable_const
  have hb := hbounds β n d e hde hn M hM hnM hMN hscale ε η t hε hη hηa ht ht1 hKM
    (μ.comap f)
  have hpush := PeriodizedMatrixPushforward.of_embedding (μ.comap f) f hf s n M hM K C κ γ η
    _ Mphys hmeas heq hb
  have hmap : (μ.comap f).map f = μ := by
    rw [map_comap_subtype_coe (AffineSimplex.isOpen_chartDomain n _).measurableSet]
    exact Measure.restrict_eq_self_of_ae_mem hμ
  rwa [hmap] at hpush

/-- See Subsection 6.1 of the paper: the prescribed common component period is at
least the polynomial scale even when capped by the smaller physical period. -/
theorem properReferencePeriod_scale (s : Riesz1.RieszExponent) (n N : ℕ+)
    (hnN : 2*(n : ℕ) ≤ (N : ℕ)) (hN : (n : ℝ)^(2/s.val) ≤ (N : ℝ)) :
    (n : ℝ)^(1/2+1/s.val) ≤ (PhysicalCore.properReferencePeriod s n N : ℝ) := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hs : 1 ≤ 1/s.val := (one_le_div s.property.1).mpr s.property.2.le
  have hp := (Real.rpow_le_rpow_of_exponent_le hn
    (by have he : 2/s.val = 2*(1/s.val) := by ring
        rw [he]; linarith : 1/2+1/s.val ≤ 2/s.val)).trans hN
  rcases (PhysicalCore.properReferencePeriod_bounds s n N hnN).2.2 with he | he
  · rw [he]; exact hp
  · exact he

/-- See Subsection 6.1 of the paper: the actual normalized scalar-chart law pushes
forward to the common positive active chart. This uses support of the
normalized Gibbs density, as given by the Gibbs density. -/
theorem simplex_chart_support (a : ℕ) (L N : ℝ) (hLN : L < N)
    (e : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
    (ν : Measure (EuclideanSpace ℝ (Fin a))) (V : EuclideanSpace ℝ (Fin a) → ℝ)
    (hW : IsEuclideanGibbsPotential volume ν
      (e '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)) V) :
    ∀ᵐ x ∂ν.map (fun w => AffineSimplex.centredChart a L (e.symm w)),
      x ∈ AffineSimplex.chartDomain (a+1) N := by
  have hU := e.toHomeomorph.isOpenMap _ (ConditionalWellPosedness.fibre_isOpen a L)
  have hchart : MeasurableEmbedding (fun w => AffineSimplex.centredChart a L (e.symm w)) :=
    ((AffineSimplex.isometry_centredChart a L).comp e.symm.isometry).isClosedEmbedding.measurableEmbedding
  rw [hchart.ae_map_iff]
  apply (IntrinsicScalarCore.supported hU hW).mono
  rintro x ⟨w,hw,rfl⟩
  change AffineSimplex.centredChart a L (e.symm (e w)) ∈ AffineSimplex.chartDomain (a+1) N
  rw [e.symm_apply_apply]
  exact ⟨hw.1,hw.2.trans_lt hLN⟩

/-- See the proof of Lemma 6.4 in the paper: the physical common-simplex auxiliary
inverse exists uniquely and satisfies all five displayed estimates at every
size. The normalized physical Gibbs law and intrinsic scalar realization
are constructed in the conclusion. The concrete all-size matrix predicate
is proved here, so no matrix estimate is a hypothesis of this theorem.
Only the explicit periodic-zeta predicate is used externally. The
cutoff uses the least degree of Lemma 5.4 of the paper, as in the
proof of Lemma 6.4. -/
theorem fixed_exterior_auxiliary (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (θ : PhysicalCutoff) (Ks : ℝ) (hKs : 0 < Ks) :
    let h : ℕ+ := paperReferenceCutoffExponent s
    let κstar := (s.val+7+(h : ℝ))+(s.val+2+(h : ℝ)*(1+s.val))
    let γstar := (h : ℝ)+1
    ∃ Cstar : ℝ, ∃ hCstar : 1 ≤ Cstar,
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, ∀ _hε : 0 < ε,
    ∀ _hsmall : ε ≤ (4 * Ks * ((h : ℝ) + 1))⁻¹,
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧ ∀ β : InverseTemperature, ∀ _hβ : β.val ∈ Icc βlo βhi,
    ∀ a b c : ℕ, ∀ _ha : 1 ≤ a, ∀ _hbc : b ≤ c,
    let n := a.succPNat
    let N := (a + 1 + b).succPNat
    let N' := (a + 1 + c).succPNat
    ∀ hN : 4 * (n : ℕ) ≤ (N : ℕ),
      (n : ℝ) ^ (2 / s.val) ≤ (N : ℝ) →
    ∀ (L : ℝ), ∀ _hL : 0 < L,
    ∀ (y : EuclideanSpace ℝ (Fin (b + 1))) (z : EuclideanSpace ℝ (Fin (c + 1))),
    ∀ hy : (∀ j, 0 < y j), ∀ hz : (∀ j, 0 < z j),
    ∀ hmassY : L + ∑ j, y j = (N : ℝ), ∀ hmassZ : L + ∑ j, z j = (N' : ℝ),
    let Ω := AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L
    let P := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) => ∑ i,
      (θ.val ((n : ℝ) ^ (-ε) * x i) + θ.val ((n : ℝ) ^ (-ε) * (x i)⁻¹))
    ∃ Ky Kz : AffineSimplex.Tangent a → ℝ,
      (∀ w (hw : w ∈ Ω), Ky w = physicalAmbientGapEnergy (ofLong β s) N
        ⟨RetainedSimplex.assemble (a + 1) b (Equiv.refl _)
          (AffineSimplex.centredChart a L w) y,
          PhysicalEnergy.simplex_subset_ambient _ _ (by
            have hh := ConditionalWellPosedness.assemble_fixed_exterior_mem a b
              (Equiv.refl _) y hy (by
                simpa only [N, Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using hmassY) hw
            rw [AffineSimplex.massSimplex_physical] at hh
            exact hh)⟩) ∧
      (∀ w (hw : w ∈ Ω), Kz w = physicalAmbientGapEnergy (ofLong β s) N'
        ⟨RetainedSimplex.assemble (a + 1) c (Equiv.refl _)
          (AffineSimplex.centredChart a L w) z,
          PhysicalEnergy.simplex_subset_ambient _ _ (by
            have hh := ConditionalWellPosedness.assemble_fixed_exterior_mem a c
              (Equiv.refl _) z hz (by
                simpa only [N', Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using hmassZ) hw
            rw [AffineSimplex.massSimplex_physical] at hh
            exact hh)⟩) ∧
    ∀ t : ℝ, ∀ _ht : t ∈ Icc (0 : ℝ) 1,
    let V := fun w => β.val * (P (AffineSimplex.centredChart a L w) +
      (1 - t) * Ky w + t * Kz w)
    ∃ ρ : Measure (AffineSimplex.Tangent a),
      IsEuclideanGibbsPotential volume ρ Ω V ∧
    ∀ e : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a),
    let U := e '' Ω
    let ν := ρ.map e
    ∃ _hW : IsEuclideanGibbsPotential volume ν U (V ∘ e.symm),
    ∃ Q : ScalarFormData ν, IsNeumannRealization U Q ∧ IsConservativeScalarForm Q ∧
    ∃ hQ : IsClosedScalarDirichletForm Q,
    let m := PhysicalCore.properReferencePeriod s n N
    let hm : 2 ≤ (m : ℕ) := by
      change 2 ≤ (PhysicalCore.properReferencePeriod s n N : ℕ)
      have := (PhysicalCore.properReferencePeriod_bounds s n N (by omega)).1
      have := n.pos
      omega
    let hnm : (n : ℕ) ≤ (m : ℕ) := by
      change (n : ℕ) ≤ (PhysicalCore.properReferencePeriod s n N : ℕ)
      have := (PhysicalCore.properReferencePeriod_bounds s n N (by omega)).1
      omega
    let η := Ks * ε
    let K := ⌊(n : ℝ) ^ η⌋₊ ^ (h : ℕ)
    let H := (2 : ℝ) • referenceIntervalMatrix s m hm K
    let Py := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      IntervalBoundary.internalMatrix N n (by omega) (fun ir =>
        BoundaryEntries.intervalWeight s N ir.2 ir.1
          (RetainedSimplex.assemble (a + 1) b (Equiv.refl _) x y))
    let Pz := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      IntervalBoundary.internalMatrix N' n (by
        simp only [N', n, Nat.succPNat_coe]
        omega) (fun ir =>
        BoundaryEntries.intervalWeight s N' ir.2 ir.1
          (RetainedSimplex.assemble (a + 1) c (Equiv.refl _) x z))
    let A0 := fun x =>
      (if WithLp.ofLp x ∈ goodBlockEvent s.val n N η then
        hessianMatrix P x + (1 - t) • Py x + t • Pz x
      else BoundaryEntries.referenceInternal s m hm K n hnm) +
        BoundaryEntries.referenceCrossing s m hm K n hnm
    let Mphys := fun x : EuclideanSpace ℝ (Fin (a + 1)) =>
      fun i j : Fin (m : ℕ) => if hi : i.val < (n : ℕ) then
        if hj : j.val < (n : ℕ) then
          A0 x ⟨i.val, hi⟩ ⟨j.val, hj⟩
        else H i j
      else H i j
    let chart := fun w => AffineSimplex.centredChart a L (e.symm w)
    let M := Mphys ∘ chart
    ∃ hMphys : PeriodizedMatrixBounds (ν := ν.map chart)
      s n m hm K Cstar κstar γstar η Mphys,
    let hM := AuxiliaryMean.simplex_matrix_bounds_internal s n m hm K Cstar κstar γstar η
      a L e ν Mphys hMphys
    ∀ i₀ : Fin (n : ℕ), |(i₀.val : ℝ) + 1 - (n : ℝ) / 2| ≤ (n : ℝ) / 4 →
    ∀ χ : Lp ℝ 2 ν,
    let f : PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν) :=
      WithLp.toLp 2 (fun i => if i = i₀ then χ else 0)
    let Abar := SchurRestriction.schurForm Q hQ n m hnm s hm K
      Cstar κstar γstar η β.val hCstar β.property M hM
    (∃! v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ,
      ∀ w, Abar v w = inner ℝ f (OperatorSchur.vectorValues Q hQ w)) ∧
    ∀ v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ,
      (∀ w, Abar v w = inner ℝ f (OperatorSchur.vectorValues Q hQ w)) →
    let v' := MatrixEnergy.vectorEquiv Q hQ v
    let S : Q.1 := ∑ i : Fin (n : ℕ), v' i
    (∀ j : Fin (n : ℕ), ‖(v' j).val‖ ≤ C * (n : ℝ) ^ (κ * ε) *
      (1 + (Nat.dist j.val i₀.val : ℝ)) ^ (s.val - 2) * ‖χ‖) ∧
    (∑ j, ‖(v' j).val‖) ≤ C * (n : ℝ) ^ (κ * ε) * ‖χ‖ ∧
    ‖S.val‖ ≤ C * (n : ℝ) ^ (κ * ε - (1 - s.val)) * ‖χ‖ ∧
    Real.sqrt (Q.2 S S) ≤ C * (n : ℝ) ^ (κ * ε - (1 - s.val) / 2) * ‖χ‖ ∧
    eLpNorm (fun x => (WithLp.toLp 2 (fun i => (v' i).val x) :
      EuclideanSpace ℝ (Fin (n : ℕ)))) ∞ ν ≤
        ENNReal.ofReal (C * (n : ℝ) ^ (κ * ε)) * eLpNorm χ ∞ ν := by
  intro h κstar γstar
  have hκstar : 0 < κstar := by
    dsimp only [κstar]
    have := s.property.1
    have := Nat.cast_nonneg (h : ℕ) (α := ℝ)
    positivity
  have hγstar : 0 < γstar := by dsimp only [γstar]; positivity
  obtain ⟨Cstar,hCstar,hmatrix⟩ := physical_matrix_bounds_internal s θ (h : ℕ)
  obtain ⟨κ,hκ,hbounds⟩ := AuxiliaryMean.fixed_exterior_auxiliary_internal hzeta s
    κstar γstar Ks hκstar hγstar hKs
  refine ⟨Cstar,hCstar,κ,hκ,?_⟩
  intro ε hε hsmall βlo βhi hβlo hβhi
  obtain ⟨C,hC,hbounds⟩ := hbounds ε hε hsmall Cstar hCstar βlo βhi hβlo hβhi
  refine ⟨C,hC,?_⟩
  intro β hβ a b c ha hbc n N N' hN hNpow L hL y z hy hz hmassY hmassZ Ω P
  obtain ⟨Ky,Kz,hKy,hKz,hphysical⟩ := hbounds β hβ a b c ha hbc hN hNpow L hL
    y z hy hz hmassY hmassZ θ
  refine ⟨Ky,Kz,hKy,hKz,?_⟩
  intro t ht V
  obtain ⟨ρ,hV,hphysical⟩ := hphysical t ht
  refine ⟨ρ,hV,?_⟩
  intro e U ν
  obtain ⟨hW,Q,hr,hcon,hQ,hphysical⟩ := hphysical e
  refine ⟨hW,Q,hr,hcon,hQ,?_⟩
  intro m hm hnm η K H Py Pz A0 Mphys chart M
  have hn : 2 ≤ (n : ℕ) := by simp only [n,Nat.succPNat_coe]; omega
  have hnm2 : 2*(n : ℕ) ≤ (m : ℕ) :=
    (PhysicalCore.properReferencePeriod_bounds s n N (by omega)).1
  have hmn : (m : ℕ) ≤ (N : ℕ) :=
    (PhysicalCore.properReferencePeriod_bounds s n N (by omega)).2.1
  have hscale : (n : ℝ)^(1/2+1/s.val) ≤ (m : ℝ) :=
    properReferencePeriod_scale s n N (by omega) hNpow
  have hη : 0 ≤ η := (mul_pos hKs hε).le
  have hprod : (h : ℝ)*η ≤ 1/4 ∧ η ≤ 1/4 := by
    have hd : 0 < 4*Ks*((h : ℝ)+1) := by positivity
    have hh : ε*(4*Ks*((h : ℝ)+1)) ≤ 1 :=
      (mul_le_mul_of_nonneg_right hsmall hd.le).trans_eq (inv_mul_cancel₀ hd.ne')
    have hh0 : 0 ≤ (h : ℝ) := Nat.cast_nonneg _
    dsimp only [η]
    constructor <;> nlinarith [mul_nonneg hh0 (mul_pos hKs hε).le]
  have hηupper : η ≤ 1-s.val/2 := by linarith [s.property.2,hprod.2]
  have hcut := AuxiliaryMean.interpolation_cutoff_bounds_internal n m hn hnm2 η
    (h : ℕ) hη hprod.1
  have hLN : L < (N : ℝ) := by
    have hh : 0 < ∑ j, y j := Finset.sum_pos (fun j _ => hy j) Finset.univ_nonempty
    linarith only [hh,hmassY]
  have hsupp := simplex_chart_support a L (N : ℝ) hLN e ν (V ∘ e.symm) hW
  have hsupp' : ∀ᵐ x ∂ν.map chart, x ∈ AffineSimplex.chartDomain n ((n+b : ℕ)+1) := by
    simpa only [n,N,Nat.succPNat_coe,Nat.cast_add,Nat.cast_succ,Nat.cast_one] using hsupp
  have hMphys : PeriodizedMatrixBounds (ν := ν.map chart)
      s n m hm K Cstar κstar γstar η Mphys := by
    exact hmatrix β n b c hbc hN m hm hnm2 hmn hscale ε η t hε.le hη hηupper ht.1 ht.2
      (by have hh := hcut.2; omega) y z (ν.map chart) hsupp'
  refine ⟨hMphys, ?_⟩
  intro hM i₀ hi₀ χ f Abar
  obtain ⟨hex,hest⟩ := hphysical hMphys i₀ hi₀ χ
  dsimp only [Abar, f, hM]
  dsimp only [M, Mphys, chart]
  dsimp only [A0, Py, Pz, H]
  dsimp only [K, η, m, n, N, N', ν, P]
  exact ⟨hex,hest⟩

end Riesz2.InterpolationMatrix
