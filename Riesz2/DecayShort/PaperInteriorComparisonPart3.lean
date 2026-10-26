/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.PaperInteriorComparisonPart2
import all Riesz2.DecayShort.PhysicalComparisonPart4

/-!
# Both conclusions of the interior comparison

Weighted Cauchy–Schwarz for the core solution, the component correction,
and the two estimates of Lemma 4.9, including all scalar fibers.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators

namespace Riesz2.DecayShort
open PhysicalComparison

attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false in
/-- Weighted Cauchy–Schwarz for the core solution in Lemma 4.9,
including the scalar-form norm needed for the gradient of the component sum. -/
theorem paper_auxiliary_graph_sum_bound (s : ℝ) (hs : 1 < s)
    (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ (θ : PhysicalCutoff) (h : ℝ), 0 < h →
      ∀ A : ℝ, 1 ≤ A → ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : Parameters), p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (n : ℕ+) (m : ℕ)
      (U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ),
      (∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) //
        y ∈ gapAmbientDomain ((n : ℕ)+m).succPNat},
        U y.val = p.val.1*physicalAmbientGapEnergy p ((n : ℕ)+m).succPNat y) →
        2 ≤ (n : ℕ)+m+1 → 2*(n : ℕ) ≤ (n : ℕ)+m+1 → ∀ (b : Bool)
        (α : Type*) [MeasurableSpace α]
        (τ : α → AffineSimplex.chartDomain n ((n+m : ℕ)+1)), Measurable τ →
        ∀ (ν : Measure α) [IsProbabilityMeasure ν] (Q : ScalarFormData ν)
        (hQ : IsClosedScalarDirichletForm Q), IsConservativeScalarForm Q →
        ∀ (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν) (v : Fin (n : ℕ) → Q.1),
        WeightedWeakSolution Q (fun x => p.val.1 • paperFrozenInteriorMatrix p n m U θ h b
          (A*(n : ℝ)^(κ*h)) (τ x)) ⊤ (fun i => if i=i₀ then χ else 0) v →
        (∑ i, ‖(ScalarFormHilbert.equiv Q hQ).symm (v i)‖) ≤ C*(n : ℝ)^(r*h)*‖χ‖ := by
  classical
  obtain ⟨q,hq,hmat⟩ := paper_uniform_matrix_bounds s hs κ hκ
  let a := s/2
  have ha : 1/2<a := by dsimp only [a]; linarith
  have has : a<s-1/2 := by dsimp only [a]; linarith
  obtain ⟨r,hr,hdec⟩ := PhysicalDecay.initial_decay_compact s a hs ha has
  let S := 2*∑' k : ℕ, (1+(k : ℝ))^(-(2*a))
  have hS : 0 ≤ S := mul_nonneg (by norm_num) (tsum_nonneg fun _ => by positivity)
  refine ⟨q*r,mul_nonneg hq hr,?_⟩
  intro θ h hh A hA βlo βhi hlo hle
  obtain ⟨Cd,hCd,hdec⟩ := hdec βlo βhi hlo hle
  obtain ⟨Cm,hCm,hmat⟩ := hmat θ h hh A hA
  let C := 1+Real.sqrt S*Cd*Cm^r
  have hC : 1 ≤ C := by
    dsimp only [C]
    have ht : 0 ≤ Real.sqrt S*Cd*Cm^r := by positivity
    linarith
  refine ⟨C,hC,?_⟩
  intro p hp hpl hph
  subst s
  have hs : 1 < p.val.2 := hs
  have hdec := hdec p.val.1 ⟨hpl,hph⟩
  intro n m U hvU hN hhalf b α _ τ hτ ν _ Q hQ hcons i₀ χ v hv
  let B := Cm*(n : ℝ)^(q*h)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le hCm
    (Real.one_le_rpow hn1 (mul_nonneg hq hh.le))
  let g : ComponentGeometry (Fin (n : ℕ)) := Sum.inl
    ⟨fun i => (i.val : ℤ),fun i j hij => Fin.ext (Int.ofNat_inj.mp hij)⟩
  let M := fun x => paperFrozenInteriorMatrix p n m U θ h b (A*(n : ℝ)^(κ*h)) (τ x)
  have hm := (hmat p rfl n m U hvU hN hhalf b).1 (ν.map τ)
  have hMm (i j) : Measurable (fun x => M x i j) := (hm.1 i j).comp hτ
  have hb := ae_of_ae_map hτ.aemeasurable hm.2
  have hd := (hdec α (Fin (n : ℕ)) ν Q hQ hcons g B hB M hMm hb i₀ χ).2 v hv
  have hsum := internal_weighted_graph_sum Q hQ g i₀ a ha v
  apply hsum.trans
  apply (mul_le_mul_of_nonneg_left hd (Real.sqrt_nonneg S)).trans
  have hfactor : Real.sqrt S*(Cd*B^r*‖χ‖) =
      (Real.sqrt S*Cd*Cm^r)*(n : ℝ)^((q*r)*h)*‖χ‖ := by
    dsimp only [B]
    rw [Real.mul_rpow (by linarith : 0 ≤ Cm) (by positivity),← Real.rpow_mul hn0.le,
      show (q*h)*r=(q*r)*h by ring]
    ring
  rw [hfactor]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg χ)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  dsimp only [C]
  linarith

set_option backward.isDefEq.respectTransparency false in
/-- Well-posedness of the physical auxiliary equation in Lemma 4.9,
over the same scalar form as its interior equation. -/
theorem paper_physical_auxiliary_exists (p : Parameters) (hs : 1 < p.val.2)
    (κ : ℝ) (hκ : 0 ≤ κ) (θ : PhysicalCutoff) (h : ℝ) (hh : 0 < h)
    (A : ℝ) (hA : 1 ≤ A) (n : ℕ+) (m : ℕ)
    (U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ)
    (hvU : ∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) //
      y ∈ gapAmbientDomain ((n : ℕ)+m).succPNat},
      U y.val = p.val.1*physicalAmbientGapEnergy p ((n : ℕ)+m).succPNat y)
    (hN : 2 ≤ (n : ℕ)+m+1) (hhalf : 2*(n : ℕ) ≤ (n : ℕ)+m+1) (b : Bool)
    (α : Type*) [MeasurableSpace α]
    (τ : α → AffineSimplex.chartDomain n ((n+m : ℕ)+1)) (hτ : Measurable τ)
    (ν : Measure α) [IsProbabilityMeasure ν] (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (hcons : IsConservativeScalarForm Q)
    (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν) :
    ∃! u : Fin (n : ℕ) → Q.1,
      WeightedWeakSolution Q (fun x => p.val.1 • paperFrozenPhysicalMatrix p n m U θ h b
        (A*(n : ℝ)^(κ*h)) (τ x)) ⊤ (fun i => if i=i₀ then χ else 0) u := by
  classical
  obtain ⟨q,hq,hmat⟩ := paper_uniform_matrix_bounds p.val.2 hs κ hκ
  obtain ⟨C,hC,hmat⟩ := hmat θ h hh A hA
  let B := C*(n : ℝ)^(q*h)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le hC
    (Real.one_le_rpow hn1 (mul_nonneg hq hh.le))
  have hB0 : 0 < B := by linarith
  have hHb := (hmat p rfl n m U hvU hN hhalf b).2.1
  obtain ⟨hmH,_,hsH,_⟩ := paperFrozenMatrices_measurable_symmetric p hs n m U θ h hh b (A*(n : ℝ)^(κ*h))
  let H := fun x => paperFrozenPhysicalMatrix p n m U θ h b (A*(n : ℝ)^(κ*h)) (τ x)
  have hHm (i j) : Measurable (fun x => H x i j) := (hmH i j).comp hτ
  have hbounds : ∀ᵐ x ∂ν, (∀ i j, H x i j=H x j i) ∧
      ∀ z : Fin (n : ℕ) → ℝ, B⁻¹*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*H x i j*z j ∧
      (∑ i, ∑ j, z i*H x i j*z j) ≤ B*(∑ i, z i^2) :=
    ae_of_all _ fun x => ⟨hsH (τ x),hHb (τ x)⟩
  obtain ⟨_,T,_,hT⟩ := AbstractEnergy.illustrative_energy p.val.1 p.property.1 Q hQ hcons
    H hHm B⁻¹ B (inv_pos.mpr hB0) ((inv_le_one_of_one_le₀ hB).trans hB) hbounds ⊤
  obtain ⟨u,hu,huniq,_⟩ := hT (WithLp.toLp 2 (fun i => if i=i₀ then χ else 0))
  exact ⟨u,hu,huniq⟩

set_option backward.isDefEq.respectTransparency false in
/-- Both conclusions of Lemma 4.9 for the matrices
of equation (4.13) on the event in equation (4.10). The degree
precedes the tilt and temperature interval. The common scalar form and measurable
pullback include every fixed-length fiber. Existence and uniqueness are included. -/
theorem paper_fixed_scalar_form_comparison (s : ℝ) (hs : 1 < s)
    (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ (θ : PhysicalCutoff) (h : ℝ), 0 < h →
      ∀ A : ℝ, 1 ≤ A → ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : Parameters), p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (n : ℕ+) (m : ℕ)
      (U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ),
      (∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) //
        y ∈ gapAmbientDomain ((n : ℕ)+m).succPNat},
        U y.val = p.val.1*physicalAmbientGapEnergy p ((n : ℕ)+m).succPNat y) →
        2 ≤ (n : ℕ)+m+1 → 2*(n : ℕ) ≤ (n : ℕ)+m+1 → ∀ (b : Bool)
        (α : Type*) [MeasurableSpace α]
        (τ : α → AffineSimplex.chartDomain n ((n+m : ℕ)+1)), Measurable τ →
        ∀ (ν : Measure α) [IsProbabilityMeasure ν] (Q : ScalarFormData ν),
        IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
        ∀ (i₀ : Fin (n : ℕ)), (n : ℝ)/4 ≤ (i₀.val : ℝ)+1 →
          (i₀.val : ℝ)+1 ≤ 3*(n : ℝ)/4 → ∀ χ : Lp ℝ 2 ν,
        let H := fun x => p.val.1 • paperFrozenPhysicalMatrix p n m U θ h b (A*(n : ℝ)^(κ*h)) (τ x)
        let M := fun x => p.val.1 • paperFrozenInteriorMatrix p n m U θ h b (A*(n : ℝ)^(κ*h)) (τ x)
        let f := fun i => if i=i₀ then χ else 0
        (∃! u : Fin (n : ℕ) → Q.1, WeightedWeakSolution Q H ⊤ f u) ∧
        (∃! v : Fin (n : ℕ) → Q.1, WeightedWeakSolution Q M ⊤ f v) ∧
        ∀ (u v : Fin (n : ℕ) → Q.1), WeightedWeakSolution Q H ⊤ f u →
          WeightedWeakSolution Q M ⊤ f v →
          (‖WithLp.toLp 2 (fun i => (u i-v i).val)‖ +
            Real.sqrt (∑ i, Q.2 (u i-v i) (u i-v i)) ≤
            C*(n : ℝ)^(r*h)*((n : ℝ)^(-(p.val.2-1/2)) +
              (((n : ℕ)+m+1 : ℕ) : ℝ)^(-(1/2 : ℝ)))*‖χ‖) ∧
          ((∑ i, ‖(u i).val‖) + Real.sqrt (Q.2 (∑ i, u i) (∑ i, u i)) ≤
            C*(n : ℝ)^(r*h)*‖χ‖) := by
  classical
  obtain ⟨rc,hrc,hcomp⟩ := paper_physical_comparison_compact s hs κ hκ
  obtain ⟨rv,hrv,haux⟩ := paper_auxiliary_graph_sum_bound s hs κ hκ
  obtain ⟨_,_,hex⟩ := paper_auxiliary_decay_compact s hs κ hκ
  refine ⟨rc+rv,add_nonneg hrc hrv,?_⟩
  intro θ h hh A hA βlo βhi hlo hle
  obtain ⟨Cc,hCc,hcomp⟩ := hcomp θ h hh A hA βlo βhi hlo hle
  obtain ⟨Cv,hCv,haux⟩ := haux θ h hh A hA βlo βhi hlo hle
  obtain ⟨_,_,hex⟩ := hex θ h hh A hA βlo βhi hlo hle
  let C := 1+2*Cv+4*Cc
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  have hCcC : Cc ≤ C := by dsimp only [C]; linarith
  have hsumC : 2*Cv+4*Cc ≤ C := by dsimp only [C]; linarith
  refine ⟨C,hC,?_⟩
  intro p hp hpl hph
  subst s
  have hs : 1 < p.val.2 := hs
  have hcomp := hcomp p rfl hpl hph
  have haux := haux p rfl hpl hph
  have hex := hex p rfl hpl hph
  intro n m U hvU hN hhalf b α _ τ hτ ν _ Q hQ hcons i₀ hlo hhi χ H M f
  refine ⟨paper_physical_auxiliary_exists p hs κ hκ θ h hh A hA n m U hvU hN hhalf b α τ hτ ν Q hQ hcons i₀ χ,
    (hex n m U hvU hN hhalf b α τ hτ ν Q hQ hcons i₀ χ).1,?_⟩
  intro u v hu hv
  have hc := hcomp n m U hvU hN hhalf b α τ hτ ν Q hQ hcons i₀ hlo hhi χ u v hu hv
  have ha := haux n m U hvU hN hhalf b α τ hτ ν Q hQ hcons i₀ χ v hv
  let P := (n : ℝ)^((rc+rv)*h)
  let R := (n : ℝ)^(-(p.val.2-1/2))+(((n : ℕ)+m+1 : ℕ) : ℝ)^(-(1/2 : ℝ))
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hpC : (n : ℝ)^(rc*h) ≤ P := Real.rpow_le_rpow_of_exponent_le hn1
    (by nlinarith : rc*h ≤ (rc+rv)*h)
  have hpV : (n : ℝ)^(rv*h) ≤ P := Real.rpow_le_rpow_of_exponent_le hn1
    (by nlinarith : rv*h ≤ (rc+rv)*h)
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hc' : ‖WithLp.toLp 2 (fun i => (u i-v i).val)‖+
      Real.sqrt (∑ i, Q.2 (u i-v i) (u i-v i)) ≤ Cc*P*R*‖χ‖ := by
    apply hc.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpC (by linarith)) hR) (norm_nonneg χ)
  have ha' : (∑ i, ‖(ScalarFormHilbert.equiv Q hQ).symm (v i)‖) ≤ Cv*P*‖χ‖ :=
    ha.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpV (by linarith)) (norm_nonneg χ))
  constructor
  · exact hc'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCcC hP) hR) (norm_nonneg χ))
  have hd := internal_graph_sum_cauchy Q hQ (fun i => u i-v i)
  have hnN : (n : ℝ) ≤ (((n : ℕ)+m+1 : ℕ) : ℝ) := by norm_cast; omega
  have hsize := (comparison_size_bounds p.val.2 hs n _ hnN).2.2.2
  change Real.sqrt (n : ℝ)*R ≤ 2 at hsize
  have hd' : (∑ i, ‖(ScalarFormHilbert.equiv Q hQ).symm (u i-v i)‖) ≤ 2*Cc*P*‖χ‖ := by
    apply (hd.trans (mul_le_mul_of_nonneg_left hc' (Real.sqrt_nonneg _))).trans
    calc
      _ = (Real.sqrt (n : ℝ)*R)*(Cc*P*‖χ‖) := by ring
      _ ≤ 2*(Cc*P*‖χ‖) := mul_le_mul_of_nonneg_right hsize (by positivity)
      _ = _ := by ring
  have hs : (∑ i, ‖(ScalarFormHilbert.equiv Q hQ).symm (u i)‖) ≤
      (Cv+2*Cc)*P*‖χ‖ := by
    calc
      _ ≤ ∑ i, (‖(ScalarFormHilbert.equiv Q hQ).symm (v i)‖+
          ‖(ScalarFormHilbert.equiv Q hQ).symm (u i-v i)‖) := by
        apply Finset.sum_le_sum
        intro i _
        have he : (ScalarFormHilbert.equiv Q hQ).symm (u i) =
            (ScalarFormHilbert.equiv Q hQ).symm (v i)+
            (ScalarFormHilbert.equiv Q hQ).symm (u i-v i) := by
          rw [map_sub]
          abel
        rw [he]
        exact norm_add_le _ _
      _ = _ := Finset.sum_add_distrib
      _ ≤ Cv*P*‖χ‖+2*Cc*P*‖χ‖ := add_le_add ha' hd'
      _ = _ := by ring
  apply (internal_graph_sums Q hQ u).trans
  apply (mul_le_mul_of_nonneg_left hs (by norm_num)).trans
  calc
    _ = (2*Cv+4*Cc)*P*‖χ‖ := by ring
    _ ≤ C*P*‖χ‖ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsumC hP) (norm_nonneg χ)

end Riesz2.DecayShort
