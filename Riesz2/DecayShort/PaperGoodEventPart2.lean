/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.PaperGoodEvent
public import Riesz1.ToMathlib.BoundedCovarianceVariance

/-!
# Boundary profile and compensated variance for the good event

Quantitative inclusion of the finer coefficient event in the good event
of equation (4.10).
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal ContDiff Topology

namespace Riesz2.DecayShort
open ConditionalScores

/-- Internal tail summation for the boundary profile in
equation (4.10) and Step 2 of Lemma 4.8. -/
theorem internal_paper_boundary_tail {s : ℝ} (hs : 0 < s) (n L : ℕ) (hL : 1 ≤ L) :
    (∑ k ∈ Finset.Ico 1 n, if L ≤ k then (k : ℝ) ^ (-s-1) else 0) ≤
      (1+1/s) * (L : ℝ) ^ (-s) := by
  let f : ℕ → ℝ := fun k => if L ≤ k then (k : ℝ) ^ (-s-1) else 0
  have hf : Summable f := Summable.of_nonneg_of_le
    (fun k => by dsimp only [f]; split_ifs <;> positivity)
    (fun k => by dsimp only [f]; split_ifs; exact le_rfl; positivity)
    (Real.summable_nat_rpow.mpr (by linarith : -s-1 < -1))
  have hshift : ∑' k, f k = ∑' k, f (k+1) := by
    rw [← hf.sum_add_tsum_nat_add 1]
    simp [f, show ¬ L ≤ 0 by omega]
  have ht := tsum_tail_indicator_le (t := s+1) (by linarith)
    (R := (L : ℝ)) (by exact_mod_cast hL)
  apply (hf.sum_le_tsum (Finset.Ico 1 n)
    (fun k _ => by dsimp only [f]; split_ifs <;> positivity)).trans
  rw [hshift]
  convert ht using 1
  · apply tsum_congr
    intro k
    simp only [f, Nat.cast_add, Nat.cast_one, show -s-1 = -(s+1) by ring]
    have hi : (L ≤ k+1) ↔ (L : ℝ) ≤ 1+(k : ℝ) := by
      rw [add_comm 1]; exact_mod_cast (Iff.rfl : L ≤ k+1 ↔ L ≤ k+1)
    simp only [hi, add_comm (k : ℝ) 1]
  · congr 2 <;> ring

set_option backward.isDefEq.respectTransparency false in
/-- Internal finite scalar summation for the boundary moment display in
Step 2 of Lemma 4.8. Both endpoint tails are retained. -/
theorem internal_paper_boundary_sums (s : ℝ) (hs : 0 < s)
    (n : ℕ+) (D : ℝ) (hD : 0 ≤ D) (P Q : ℕ → ℝ) (a : ℝ)
    (hP : ∀ k : ℕ, 1 ≤ k → k < (n : ℕ) → P k ≤ D*(k : ℝ)^(-s-1))
    (hQ : ∀ k : ℕ, 1 ≤ k → k < (n : ℕ) → Q k ≤ D*((n : ℕ)-k : ℕ)^(-s-1))
    (ha : a ≤ D*(n : ℝ)^(-s)) (i j : Fin (n : ℕ)) :
    (∑ k ∈ Finset.Ico 1 (n : ℕ), P k*IntervalBoundary.rankOne (IntervalBoundary.initialSegment n k) i j)+
      (∑ k ∈ Finset.Ico 1 (n : ℕ), Q k*IntervalBoundary.rankOne (IntervalBoundary.terminalSegment n k) i j)+a ≤
      (2+1/s)*D*paperBoundaryProfile s i j := by
  classical
  let L := max (i.val+1) (j.val+1)
  let R := (n : ℕ)-min i.val j.val
  let f := fun k : ℕ => if L ≤ k then (k : ℝ)^(-s-1) else 0
  let g := fun k : ℕ => if R ≤ k then (k : ℝ)^(-s-1) else 0
  have hL : 1 ≤ L := by dsimp only [L]; omega
  have hR : 1 ≤ R := by dsimp only [R]; have := i.isLt; have := j.isLt; omega
  have hLi : L ≤ (n : ℕ) := by dsimp only [L]; have := i.isLt; have := j.isLt; omega
  have hRi : R ≤ (n : ℕ) := Nat.sub_le _ _
  have hp (k : ℕ) (hk : k ∈ Finset.Ico 1 (n : ℕ)) :
      P k *
        IntervalBoundary.rankOne (IntervalBoundary.initialSegment n k) i j ≤ D*f k := by
    have hkn := Finset.mem_Ico.mp hk
    have hb := hP k hkn.1 hkn.2
    by_cases hmem : i ∈ IntervalBoundary.initialSegment n k ∧
        j ∈ IntervalBoundary.initialSegment n k
    · have hLk : L ≤ k := by
        have hi := (Finset.mem_filter.mp hmem.1).2
        have hj := (Finset.mem_filter.mp hmem.2).2
        dsimp only [L]
        omega
      simpa only [IntervalBoundary.rankOne, ite_eq_left hmem, mul_one, f, ite_eq_left hLk] using hb
    · simp only [IntervalBoundary.rankOne, ite_eq_right hmem, mul_zero]
      exact mul_nonneg hD (by dsimp only [f]; split_ifs <;> positivity)
  have hq (k : ℕ) (hk : k ∈ Finset.Ico 1 (n : ℕ)) :
      Q k *
        IntervalBoundary.rankOne (IntervalBoundary.terminalSegment n k) i j ≤ D*g ((n : ℕ)-k) := by
    have hkn := Finset.mem_Ico.mp hk
    have hb := hQ k hkn.1 hkn.2
    by_cases hmem : i ∈ IntervalBoundary.terminalSegment n k ∧
        j ∈ IntervalBoundary.terminalSegment n k
    · have hRk : R ≤ (n : ℕ)-k := by
        have hi := (Finset.mem_filter.mp hmem.1).2
        have hj := (Finset.mem_filter.mp hmem.2).2
        dsimp only [R]
        omega
      simpa only [IntervalBoundary.rankOne, ite_eq_left hmem, mul_one, g, ite_eq_left hRk] using hb
    · simp only [IntervalBoundary.rankOne, ite_eq_right hmem, mul_zero]
      exact mul_nonneg hD (by dsimp only [g]; split_ifs <;> positivity)
  have hreflect : (∑ k ∈ Finset.Ico 1 (n : ℕ), g ((n : ℕ)-k)) =
      ∑ k ∈ Finset.Ico 1 (n : ℕ), g k := by
    apply Finset.sum_bij (fun k _ => (n : ℕ)-k)
    · intro k hk
      have := Finset.mem_Ico.mp hk
      exact Finset.mem_Ico.mpr ⟨by omega,by omega⟩
    · intro a ha b hb he
      have := Finset.mem_Ico.mp ha
      have := Finset.mem_Ico.mp hb
      omega
    · intro k hk
      have := Finset.mem_Ico.mp hk
      exact ⟨(n : ℕ)-k, Finset.mem_Ico.mpr ⟨by omega,by omega⟩,by omega⟩
    · intro _ _
      rfl
  have hqSum : (∑ k ∈ Finset.Ico 1 (n : ℕ),
      Q k *
        IntervalBoundary.rankOne (IntervalBoundary.terminalSegment n k) i j) ≤
      D*((1+1/s)*(R : ℝ)^(-s)) := by
    calc
      _ ≤ ∑ k ∈ Finset.Ico 1 (n : ℕ), D*g ((n : ℕ)-k) := Finset.sum_le_sum hq
      _ = D * ∑ k ∈ Finset.Ico 1 (n : ℕ), g k := by rw [← Finset.mul_sum,hreflect]
      _ ≤ _ := mul_le_mul_of_nonneg_left (internal_paper_boundary_tail
        (by linarith : 0 < s) (n : ℕ) R hR) hD
  have hpSum' : (∑ k ∈ Finset.Ico 1 (n : ℕ),
      P k *
        IntervalBoundary.rankOne (IntervalBoundary.initialSegment n k) i j) ≤
      D*((1+1/s)*(L : ℝ)^(-s)) := by
    calc
      _ ≤ ∑ k ∈ Finset.Ico 1 (n : ℕ), D*f k := Finset.sum_le_sum hp
      _ = D * ∑ k ∈ Finset.Ico 1 (n : ℕ), f k := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (internal_paper_boundary_tail
        (by linarith : 0 < s) (n : ℕ) L hL) hD
  have hnL : (n : ℝ)^(-s) ≤ (L : ℝ)^(-s) :=
    Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (show 0 < L by omega)) (by exact_mod_cast hLi) (by linarith)
  have hd := ha
  have hd' := hd.trans (mul_le_mul_of_nonneg_left hnL hD)
  change _ ≤ (2+1/s)*D*((L : ℝ)^(-s)+(R : ℝ)^(-s))
  have hnonneg : 0 ≤ D*(R : ℝ)^(-s) := by positivity
  nlinarith only [hpSum',hqSum,hd',hnonneg]

set_option backward.isDefEq.respectTransparency false in
/-- Internal deterministic boundary summation for equation (4.10).
It sums the finer prefix and suffix bounds, retaining both endpoints. -/
theorem internal_paper_boundary_profile (p : Parameters) (hs : 1 < p.val.2)
    (n : ℕ+) (m : ℕ) (hhalf : 2*(n : ℕ) ≤ (n : ℕ)+m+1) (D : ℝ) (hD : 0 ≤ D)
    (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1))
    (hx : x ∈ ExceptionalEvent.coefficientEvent p n m (by simp; omega) D)
    (i j : Fin (n : ℕ)) :
    IntervalBoundary.boundaryMatrix ((n : ℕ)+m).succPNat n (by simp; omega)
      (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x) i j ≤
      (2+1/p.val.2)*D*paperBoundaryProfile p.val.2 i j := by
  classical
  let N := ((n : ℕ)+m).succPNat
  let hn : (n : ℕ) ≤ (N : ℕ) := by simp only [N,Nat.succPNat_coe]; omega
  let A := conditionalIntervalWeight p n m n.pos (Equiv.refl _) x
  rw [IntervalBoundary.boundary_representation N n.pos (by simpa only [N,Nat.succPNat_coe] using hhalf)]
  apply internal_paper_boundary_sums p.val.2 (by linarith) n D hD
  · intro k hk hkn
    have ht := hx.2.1 ⟨k-1,by omega⟩
    simpa only [show k-1+1 = k by omega] using ht
  · intro k hk hkn
    have ht := hx.2.2.1 ⟨k-1,by omega⟩
    simpa only [show k-1+1 = k by omega] using ht
  · exact hx.2.2.2.1

/-- Internal variance inequality for Step 3 of Lemma 4.8. -/
theorem internal_paper_variance_sub {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F G : Ω → ℝ)
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    (∫ z, (F z-G z-∫ y, F y-G y ∂μ)^2 ∂μ) ≤
      2*(∫ z, (F z-∫ y, F y ∂μ)^2 ∂μ) +
      2*(∫ z, (G z-∫ y, G y ∂μ)^2 ∂μ) := by
  have h := Riesz1.variance_const_mul_sub_le_two hF hG 1
  simp only [one_mul, one_pow, mul_one] at h
  have hFG : MemLp (fun z => F z - G z) 2 μ := hF.sub hG
  rw [Riesz1.variance_eq_ofReal_integral_sq μ _ hFG,
    Riesz1.variance_eq_ofReal_integral_sq μ F hF,
    Riesz1.variance_eq_ofReal_integral_sq μ G hG] at h
  rw [← ENNReal.ofReal_ofNat (n := 2), ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.ofReal_add (by positivity) (by positivity)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

set_option backward.isDefEq.respectTransparency false in
/-- Internal physical variance upper bound for Step 3 of Lemma 4.8.
Both Brascamp–Lieb inputs are proved for the actual conditional law. -/
theorem internal_paper_compensated_variance_upper (p : Parameters) (n : ℕ+) (m : ℕ)
    (hN : 2 ≤ (n : ℕ)+m+1) (hhalf : 2*(n : ℕ) ≤ (n : ℕ)+m+1)
    (U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ)
    (hv : ∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) //
      y ∈ gapAmbientDomain ((n : ℕ)+m).succPNat},
      U y.val = p.val.1 * physicalAmbientGapEnergy p ((n : ℕ)+m).succPNat y)
    (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1)) (i : Fin (n : ℕ)) :
    let H := IntervalBoundary.intervalMatrix ((n : ℕ)+m).succPNat ((n : ℕ)+m+1) le_rfl
      (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
    let S := Finset.univ.filter (fun a : Fin ((n : ℕ)+m+1) => (n : ℕ) ≤ a.val)
    paperCompensatedVariance p n m U x i ≤
      2*(p.val.1*(2*(p.val.2*(p.val.2+1))))⁻¹ *
        (PhysicalFibres.exteriorGradientEnergy p n m n.pos x i).toReal +
      2*p.val.1⁻¹*((m+1 : ℝ)⁻¹^2*∑ a ∈ S, ∑ b ∈ S, H a b) := by
  classical
  intro H S
  have hβ := p.property.1
  have hs₀ := p.property.2.1
  by_cases hm0 : m=0
  · subst m
    have hz : paperCompensatedVariance p n 0 U x i=0 := by
      dsimp only [paperCompensatedVariance]
      rw [ProperMarginalChart.conditionalMeasure_point]
      simp
    rw [hz]
    apply add_nonneg (by positivity)
    apply mul_nonneg (by positivity)
    apply mul_nonneg (sq_nonneg _)
    apply Finset.sum_nonneg
    intro a _
    apply Finset.sum_nonneg
    intro b _
    exact IntervalBoundary.intervalMatrix_nonneg ((n : ℕ)+0).succPNat ((n : ℕ)+0+1) le_rfl
      (conditionalIntervalWeight p n 0 n.pos (Equiv.refl _) x)
      (conditionalIntervalWeight_nonneg p n 0 n.pos (Equiv.refl _) x) a b
  have hm : 1 ≤ m := by omega
  obtain ⟨V,_,hV,hF⟩ := physical_individual_score_variance p n m n.pos (by have := n.pos; omega) hm
  obtain ⟨W,_,hW,hG⟩ := physical_compensation_score_variance p n m n.pos (by have := n.pos; omega) hm
  let μ := ProperMarginalChart.conditionalMeasure p n m n.pos (Equiv.refl _) x
  let _ := ProperMarginalChart.conditionalMeasure_probability p n m n.pos (Equiv.refl _) x
  let e : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) :=
    EuclideanSpace.single (Fin.castLE (by omega) i) 1
  let q := WithLp.toLp 2 (ConditionalForces.compensationVector n m)
  let F := fun z => p.val.1⁻¹*fderiv ℝ U
    (RetainedSimplex.chart n m ((n+m : ℕ)+1) (Equiv.refl _) (x.val,z)) e
  let G := fun z => p.val.1⁻¹*fderiv ℝ U
    (RetainedSimplex.chart n m ((n+m : ℕ)+1) (Equiv.refl _) (x.val,z)) q
  have heF := PhysicalComparison.internal_score_extension_ae p n m n.pos U V
    (fun y => (hv y).trans (hV y).symm) x e
  have heG := PhysicalComparison.internal_score_extension_ae p n m n.pos U W
    (fun y => (hv y).trans (hW y).symm) x q
  have hFi : MemLp F 2 μ := MemLp.ae_eq heF.symm (hF x i).1
  have hGi : MemLp G 2 μ := MemLp.ae_eq heG.symm (hG x).1
  have hvar {f g : EuclideanSpace ℝ (Fin m) → ℝ} (he : f =ᵐ[μ] g) :
      (∫ z, (f z-∫ y, f y ∂μ)^2 ∂μ) = ∫ z, (g z-∫ y, g y ∂μ)^2 ∂μ := by
    rw [integral_congr_ae he]
    apply integral_congr_ae
    filter_upwards [he] with z hz
    rw [hz]
  have hVF := (hvar heF).trans_le (hF x i).2
  have hVG := (hvar heG).trans_le (hG x).2
  have hXi : paperCompensatedScore p n m U x i = fun z => F z-G z := by
    funext z
    dsimp only [paperCompensatedScore,F,G,e,q]
    rw [map_sub,mul_sub]
  dsimp only [paperCompensatedVariance]
  rw [hXi]
  exact (internal_paper_variance_sub μ F G hFi hGi).trans
    (by nlinarith only [hVF,hVG])

set_option backward.isDefEq.respectTransparency false in
/-- Inclusion of the finer Lean event in the good event of equation (4.10),
with one enlargement factor uniform over all inverse temperatures above `βlo`.
This transfers the exceptional estimates to the event of Lemma 4.8. -/
theorem legacyGoodEvent_subset_paperGoodEvent (s βlo : ℝ) (hs : 1 < s) (hlo : 0 < βlo) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 →
      ∀ (n : ℕ+) (m : ℕ), 4 ≤ (n : ℕ)+m+1 → 2*(n : ℕ) ≤ (n : ℕ)+m+1 →
      ∀ (U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ),
      (∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) //
        y ∈ gapAmbientDomain ((n : ℕ)+m).succPNat},
        U y.val = p.val.1 * physicalAmbientGapEnergy p ((n : ℕ)+m).succPNat y) →
      ∀ h D : ℝ, 0 ≤ D →
      ExceptionalEvent.properGoodEvent p n m (by simp; omega) h D ⊆
        paperProperGoodEvent p n m U h (K*D) := by
  let α := βlo*(2*(s*(s+1)))
  let K := 4+1/s+2*α⁻¹+2*βlo⁻¹
  have hs0 : 0 < s := by linarith
  have hα : 0 < α := by dsimp only [α]; positivity
  have hK : 3 ≤ K := by dsimp only [K]; linarith [one_div_pos.mpr hs0,inv_pos.mpr hα,inv_pos.mpr hlo]
  have hKB : 2+1/s ≤ K := by dsimp only [K]; linarith [inv_pos.mpr hα,inv_pos.mpr hlo]
  have hKV : 2*α⁻¹+2*βlo⁻¹ ≤ K := by dsimp only [K]; linarith [one_div_pos.mpr hs0]
  refine ⟨K,by linarith,?_⟩
  intro p hp hpl n m hN hhalf U hv h D hD x hx
  subst s
  let N := ((n : ℕ)+m).succPNat
  let hn : (n : ℕ) ≤ (N : ℕ) := by dsimp only [N]; simp; omega
  let A := conditionalIntervalWeight p n m n.pos (Equiv.refl _) x
  let H := IntervalBoundary.intervalMatrix N (N : ℕ) le_rfl A
  let S := Finset.univ.filter (fun a : Fin (N : ℕ) => (n : ℕ) ≤ a.val)
  let b := fun i : Fin (n : ℕ) => (m+1 : ℝ)⁻¹*∑ a ∈ S, H (Fin.castLE hn i) a
  let c := (m+1 : ℝ)⁻¹^2*∑ a ∈ S, ∑ b ∈ S, H a b
  have hH (i j) : 0 ≤ H i j := IntervalBoundary.intervalMatrix_nonneg N (N : ℕ) le_rfl A
    (conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x) i j
  have hb (i) : 0 ≤ b i := mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => hH _ a)
  have hc : 0 ≤ c := mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun a _ =>
    Finset.sum_nonneg fun b _ => hH a b)
  have hbc (i) : b i+c ≤ D/(N : ℝ) := hx.2.2.2.2.2.1 i
  have hbi (i) : b i ≤ D/(N : ℝ) := (le_add_of_nonneg_right hc).trans (hbc i)
  have hcD : c ≤ D/(N : ℝ) := (le_add_of_nonneg_left (hb ⟨0,n.pos⟩)).trans (hbc ⟨0,n.pos⟩)
  have hDle : D ≤ K*D := by nlinarith
  refine ⟨hx.1,?_,?_,?_,?_⟩
  · intro i j
    exact (hx.2.1 i j).trans (mul_le_mul_of_nonneg_right hDle (by positivity))
  · intro i j
    have heQ : paperCompensationEntry p n m x i j = -b i-b j+c := by
      dsimp only [paperCompensationEntry,b,c,H,S,N,A,Nat.succPNat_coe]
      ring
    rw [heQ]
    have ht : |-b i-b j+c| ≤ b i+b j+c := by
      calc
        _ ≤ |-b i-b j|+|c| := abs_add_le _ _
        _ ≤ |-b i|+|b j|+|c| := add_le_add (abs_sub _ _) le_rfl
        _ = _ := by rw [abs_neg,abs_of_nonneg (hb i),abs_of_nonneg (hb j),abs_of_nonneg hc]
    have ht' := add_le_add (add_le_add (hbi i) (hbi j)) hcD
    apply (ht.trans ht').trans
    have hNK : 0 < (N : ℝ) := by positivity
    change D/(N : ℝ)+D/(N : ℝ)+D/(N : ℝ) ≤ K*D/(N : ℝ)
    rw [← add_div,← add_div]
    apply (div_le_div_iff_of_pos_right hNK).mpr
    nlinarith
  · intro i j
    apply (internal_paper_boundary_profile p hs n m hhalf D hD x hx.2 i j).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKB hD) (by unfold paperBoundaryProfile; positivity)
  · intro i
    have hαp : α ≤ p.val.1*(2*(p.val.2*(p.val.2+1))) :=
      mul_le_mul_of_nonneg_right hpl (by positivity)
    have hαinv := inv_anti₀ hα hαp
    have hβinv := inv_anti₀ hlo hpl
    have hV := hx.2.2.2.2.2.2 i
    have hu := internal_paper_compensated_variance_upper p n m (by omega) hhalf U hv x i
    have hV0 : 0 ≤ (PhysicalFibres.exteriorGradientEnergy p n m n.pos x i).toReal :=
      ENNReal.toReal_nonneg
    have hvar : paperCompensatedVariance p n m U x i ≤
        2*α⁻¹*(D*(boundaryDistance i : ℝ)^(1-2*p.val.2))+2*βlo⁻¹*(D/(N : ℝ)) := by
      apply hu.trans
      apply add_le_add
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hαinv (by norm_num)) hV hV0 (by positivity)
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hβinv (by norm_num)) hcD hc (by positivity)
    apply hvar.trans
    have hP : 0 ≤ (boundaryDistance i : ℝ)^(1-2*p.val.2) := by positivity
    have hNI : 0 ≤ (N : ℝ)⁻¹ := by positivity
    have hcoeff₁ : 2*α⁻¹ ≤ K := by linarith [inv_nonneg.mpr hlo.le]
    have hcoeff₂ : 2*βlo⁻¹ ≤ K := by linarith [inv_nonneg.mpr hα.le]
    change _ ≤ K*D*((boundaryDistance i : ℝ)^(1-2*p.val.2)+(N : ℝ)⁻¹)
    have h₁ := mul_le_mul_of_nonneg_right hcoeff₁ (mul_nonneg hD hP)
    have h₂ := mul_le_mul_of_nonneg_right hcoeff₂ (mul_nonneg hD hNI)
    simp only [div_eq_mul_inv] at *
    nlinarith only [h₁,h₂]

end Riesz2.DecayShort
