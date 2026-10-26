/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.PhysicalIdentityPart5
public import Riesz2.DecayLong.PhysicalCorePart5
public import Riesz1.Rigidity.BoundarySelectionLawCyclic

/-!
# Full-cycle core and physical comparison

The intrinsic full-cycle construction in Subsection 5.1, with the literal ambient Hessian and the original scalar form.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators MatrixOrder ContDiff Classical Topology

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.PhysicalCore

/-- See Subsection 5.1 of the paper on gap coordinates. This is the gap-coordinate
version of `GoodBlocks.fullGoodEvent`, with its density-free physical
Hessian. Its equivalence on particle gaps is proved below. -/
def fullGapGoodSet (s : Riesz1.RieszExponent) (N : ℕ+) (ε κ₀ : ℝ) :
    Set (EuclideanSpace ℝ (Fin (N : ℕ))) :=
  {y | WithLp.ofLp y ∈ Riesz1.gapSimplex N ∧
    ((∀ i, (N : ℝ)^(-ε) ≤ y i ∧ y i ≤ (N : ℝ)^ε) ∧
      ∀ (i : Fin (N : ℕ)) (k : Fin ((N : ℕ)+1)), 1 ≤ k.val → k.val ≤ (N : ℕ)/2 →
        |cyclicGapSum N i k.val (WithLp.ofLp y) - (k.val : ℝ)| ≤
          (N : ℝ)^ε * (k.val : ℝ)^(s.val/2)) ∧
    ∀ a b, GoodBlocks.gapHessian s N a b y ≤
      (N : ℝ)^(κ₀*ε)*(1+(Riesz1.cyclicIndexDistance N a b : ℝ))^(-s.val)}

/-- The full-cycle good event is Borel on the complete gap carrier. -/
theorem measurableSet_fullGapGoodSet (s : Riesz1.RieszExponent) (N : ℕ+) (ε κ₀ : ℝ) :
    MeasurableSet (fullGapGoodSet s N ε κ₀) := by
  have hall {ι : Type} [Countable ι] {P : ι → EuclideanSpace ℝ (Fin (N : ℕ)) → Prop}
      (h : ∀ i, MeasurableSet {y | P i y}) : MeasurableSet {y | ∀ i, P i y} := by
    simpa only [ofPred_forall] using MeasurableSet.iInter h
  have hs : MeasurableSet {y : EuclideanSpace ℝ (Fin (N : ℕ)) |
      WithLp.ofLp y ∈ Riesz1.gapSimplex N} := by
    refine MeasurableSet.inter ?_ ?_
    · apply hall (ι := Fin (N : ℕ)) (P := fun i y => 0 < y i)
      intro i
      exact measurableSet_lt measurable_const (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable
    · exact measurableSet_eq_fun (by fun_prop) measurable_const
  unfold fullGapGoodSet
  refine hs.inter (MeasurableSet.inter (MeasurableSet.inter ?_ ?_) ?_)
  · apply hall (ι := Fin (N : ℕ))
      (P := fun i y => (N : ℝ)^(-ε) ≤ y i ∧ y i ≤ (N : ℝ)^ε)
    intro i
    exact (measurableSet_le measurable_const (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable).inter
      (measurableSet_le (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable measurable_const)
  · apply hall (ι := Fin (N : ℕ))
    intro i
    apply hall (ι := Fin ((N : ℕ)+1))
    intro k
    apply MeasurableSet.imp (measurable_const (a := 1 ≤ k.val)).setOf
    apply MeasurableSet.imp (measurable_const (a := k.val ≤ (N : ℕ)/2)).setOf
    apply measurableSet_le _ measurable_const
    have h := (PhysicalEnergy.intervalLinear N i k.val).continuous.measurable
    simpa only [PhysicalEnergy.intervalLinear_apply] using (h.sub_const (k.val : ℝ)).abs
  · apply hall (ι := Fin (N : ℕ))
    intro a
    apply hall (ι := Fin (N : ℕ))
    intro b
    exact measurableSet_le (GoodBlocks.measurable_gapHessian s N a b) measurable_const

/-- See Subsection 5.1 of the paper: the new carrier has exactly the particle
good event, with every rigidity and Hessian-cutoff clause unchanged. -/
theorem fullGapGoodSet_gapVector (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (ε κ₀ : ℝ) (X : Riesz1.Configuration N) :
    WithLp.toLp 2 (gapVector X) ∈ fullGapGoodSet s N ε κ₀ ↔
      X ∈ GoodBlocks.fullGoodEvent (ofLong β s) N ε κ₀ := by
  have hy : gapVector X ∈ Riesz1.gapSimplex N := Riesz1.boundary_gapVector_mem_simplex X
  simp only [fullGapGoodSet,Set.mem_ofPred_eq,hy,true_and,
    GapChart.cyclicGapSum_gapVector,GoodBlocks.gapHessian_particle β s N,
    GoodBlocks.fullGoodEvent,ofLong]
  rfl

/-- See Subsection 5.1 of the paper, full-cycle core. There are no boundary or
conditional terms. On the good event this is precisely the forcing plus
physical ambient Hessian. Off the good event it is the original reference.
The formula defines the field on its entire ambient carrier. -/
def fullMatrix (s : Riesz1.RieszExponent) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ)
    (y : EuclideanSpace ℝ (Fin (N : ℕ))) : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ :=
  if y ∈ fullGapGoodSet s N ε κ₀ then
    forcingHessian N θ ε y + Matrix.of (fun a b => GoodBlocks.gapHessian s N a b y)
  else (2 : ℝ) • referenceIntervalMatrix s N hN K

/-- Measurability of the actual full-cycle core, on its whole carrier. -/
theorem measurable_fullMatrix (s : Riesz1.RieszExponent) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ) (a b : Fin (N : ℕ)) :
    Measurable (fun y => fullMatrix s N hN K θ ε κ₀ y a b) := by
  have he : (fun y => fullMatrix s N hN K θ ε κ₀ y a b) = fun y =>
      if y ∈ fullGapGoodSet s N ε κ₀ then forcingHessian N θ ε y a b + GoodBlocks.gapHessian s N a b y
      else 2*referenceIntervalMatrix s N hN K a b := by funext y; unfold fullMatrix; split_ifs <;> rfl
  rw [he]
  exact ((measurable_forcingHessian N θ ε a b).add (GoodBlocks.measurable_gapHessian s N a b)).ite
    (measurableSet_fullGapGoodSet s N ε κ₀) measurable_const

namespace Internal

/-- A full simplex point is also in the auxiliary proper open chart of
mass `N+1`. This is only used to reuse the already proved forcing calculus. -/
theorem simplex_mem_forcing_chart (N : ℕ+) (y : EuclideanSpace ℝ (Fin (N : ℕ)))
    (hy : WithLp.ofLp y ∈ Riesz1.gapSimplex N) :
    y ∈ AffineSimplex.chartDomain N ((N+0 : ℕ)+1) := by
  refine ⟨hy.1,?_⟩
  have he : ∑ i,y i = (N : ℝ) := hy.2
  simpa only [Nat.add_zero,Nat.cast_add,Nat.cast_one,he] using (lt_add_one (N : ℝ))

end Internal

/-- The actual full-cycle core is symmetric on its entire carrier. -/
theorem fullMatrix_symmetric (_β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ)
    (y : EuclideanSpace ℝ (Fin (N : ℕ))) (a b : Fin (N : ℕ)) :
    fullMatrix s N hN K θ ε κ₀ y a b = fullMatrix s N hN K θ ε κ₀ y b a := by
  unfold fullMatrix
  split_ifs with hy
  · simp only [Matrix.add_apply]
    rw [forcingHessian_symmetric N 0 θ ε ⟨y,Internal.simplex_mem_forcing_chart N y hy.1⟩ a b]
    congr 1
    simp only [Matrix.of_apply,GoodBlocks.gapHessian,and_comm]
  · simpa only [Matrix.smul_apply,smul_eq_mul] using
      congrArg (fun t : ℝ => 2*t) (show referenceIntervalMatrix s N hN K a b =
        referenceIntervalMatrix s N hN K b a from by
          simpa only [Matrix.conjTranspose_apply,star_trivial] using
            congrFun (congrFun (referenceIntervalMatrix_isHermitian s N hN K) b) a)

/-- See Subsection 5.1 of the paper, fixed-parameter boundedness of the full core.
The diagonal cutoff controls physical entries everywhere on the good event,
and the exact reference controls the complement. -/
theorem fullMatrix_bounded (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y a b, |fullMatrix s N hN K θ ε κ₀ y a b| ≤ C := by
  obtain ⟨F,hF,hforce⟩ := forcingHessian_bound N 0 θ ε
  let H := (2 : ℝ) • referenceIntervalMatrix s N hN K
  let B := ∑ a,∑ b,|H a b|
  have hB : 0 ≤ B := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => abs_nonneg _
  refine ⟨F+(N : ℝ)^(κ₀*ε)+B,by positivity,fun y a b => ?_⟩
  by_cases hy : y ∈ fullGapGoodSet s N ε κ₀
  · have hp := GoodBlocks.gapHessian_nonneg β s N a b y hy.1
    have hd : (1+(Riesz1.cyclicIndexDistance N a b : ℝ))^(-s.val) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (le_add_of_nonneg_right (Nat.cast_nonneg _))
        (by linarith [s.property.1])
    have hcut' := mul_le_mul_of_nonneg_left hd
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ N) (κ₀*ε))
    rw [mul_one] at hcut'
    have hcut := (hy.2.2 a b).trans hcut'
    have hf := (hforce ⟨y,Internal.simplex_mem_forcing_chart N y hy.1⟩ a b).2
    simp only [fullMatrix,ite_eq_left hy,Matrix.add_apply,Matrix.of_apply]
    exact (abs_add_le _ _).trans (by rw [abs_of_nonneg hp]; linarith only [hf,hcut,hB])
  · simp only [fullMatrix,ite_eq_right hy]
    have he := (Finset.single_le_sum (fun j _ => abs_nonneg (H a j)) (Finset.mem_univ b)).trans
      (Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg (H i j)) (Finset.mem_univ a))
    exact he.trans (by dsimp only [B]; linarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ N) (κ₀*ε)])

end Riesz2.PhysicalCore

namespace Riesz2.PhysicalIdentity.Internal

/-- Identify the full physical Hessian with its literal forcing and
ambient gap matrix at each point of the positive mass simplex. -/
theorem full_hessian_eq (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (θ : PhysicalCutoff) (ε : ℝ)
    (U : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ)
    (hU : ContDiffOn ℝ ∞ U (gapAmbientDomain N))
    (hv : ∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
      U y.val = fullPhysicalPotentialValue (ofLong β s) N hN θ ε false y)
    (y : EuclideanSpace ℝ (Fin (N : ℕ))) (hy : WithLp.ofLp y ∈ Riesz1.gapSimplex N)
    (a b : Fin (N : ℕ)) :
    hessianMatrix U y a b = β.val*(PhysicalCore.forcingHessian N θ ε y a b +
      GoodBlocks.gapHessian s N a b y) := by
  obtain ⟨W,hW,hw,hjet⟩ := GoodBlocks.gapHessian_eq_second β s N
  have hyΩ := PhysicalEnergy.simplex_subset_ambient N (WithLp.ofLp y) hy
  let P := fun x : EuclideanSpace ℝ (Fin (N : ℕ)) => ∑ i,θ.val ((N : ℝ)^(-ε)*x i)
  have hP := (PhysicalCore.forcing_smooth N 0 θ ε).contDiffAt
    ((AffineSimplex.isOpen_chartDomain N _).mem_nhds (PhysicalCore.Internal.simplex_mem_forcing_chart N y hy))
  have hWy := hW.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hyΩ)
  have hUy := hU.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hyΩ)
  have he : U =ᶠ[𝓝 y] (fun x => β.val*(W x+P x)) := by
    filter_upwards [(PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hyΩ] with x hx
    rw [hv ⟨x,hx⟩,hw ⟨x,hx⟩]
    simp only [fullPhysicalPotentialValue,ofLong,Bool.false_eq_true,ite_false,add_zero]
    rfl
  rw [Intrinsic.hessianMatrix_eq_second hUy,he.fderiv.fderiv_eq,
    PhysicalCollision.internal_hessian_const_mul ((hWy.add hP).of_le (by simp)),
    PhysicalCollision.internal_hessian_add (hWy.of_le (by simp)) (hP.of_le (by simp)),hjet y hy a b]
  rw [← Intrinsic.hessianMatrix_eq_second hP]
  change β.val*(GoodBlocks.gapHessian s N a b y + PhysicalCore.forcingHessian N θ ε y a b) = _
  ring

/-- The paper's full physical lower bound, on unrestricted ambient
components and with the literal upper penalty. This is independent of the
good event and remains valid before zero-sum compression. -/
theorem full_physical_lower (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (θ : PhysicalCutoff) (ε : ℝ) (hε : 0 ≤ ε)
    (U : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ)
    (hU : ContDiffOn ℝ ∞ U (gapAmbientDomain N))
    (hv : ∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
      U y.val = fullPhysicalPotentialValue (ofLong β s) N hN θ ε false y) :
    let a := min 1 (s.val*(s.val+1))*(N : ℝ)^(-(s.val+2)*ε)
    0 < a ∧ ∀ (y : EuclideanSpace ℝ (Fin (N : ℕ))), WithLp.ofLp y ∈ Riesz1.gapSimplex N →
      ∀ t : Fin (N : ℕ) → ℝ,
        β.val*a*(∑ i,t i^2) ≤ ∑ i,∑ j,t i*hessianMatrix U y i j*t j := by
  intro a
  have ha : 0 < a := mul_pos (lt_min zero_lt_one (by nlinarith [s.property.1]))
    (Real.rpow_pos_of_pos (by positivity) _)
  refine ⟨ha,fun y hy t => ?_⟩
  let R : {R : ℝ // 0 < R} := ⟨(N : ℝ)^ε,Real.rpow_pos_of_pos (by positivity) _⟩
  have hR : 1 ≤ (R : ℝ) := Real.one_le_rpow (by exact_mod_cast N.pos) hε
  obtain ⟨W,hW,hw,hlow⟩ := full_curvature β s N hN θ R hR Finset.univ
  let P := fun x : EuclideanSpace ℝ (Fin (N : ℕ)) => ∑ i,θ.val (x i/R)
  have hWy := hW.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds
    (PhysicalEnergy.simplex_subset_ambient N (WithLp.ofLp y) hy))
  have hP := DecayShort.upperGapPenalty_contDiffAt θ R Finset.univ y hy.1
  have hyΩ := PhysicalEnergy.simplex_subset_ambient N (WithLp.ofLp y) hy
  have hUy := hU.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hyΩ)
  have hscale : (R : ℝ)⁻¹ = (N : ℝ)^(-ε) := (Real.rpow_neg (by positivity) ε).symm
  have he : U =ᶠ[𝓝 y] (fun x => β.val*(W x+P x)) := by
    filter_upwards [(PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hyΩ] with x hx
    rw [hv ⟨x,hx⟩,hw ⟨x,hx⟩]
    simp only [fullPhysicalPotentialValue,ofLong,Bool.false_eq_true,ite_false,add_zero]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg θ.val (by rw [div_eq_mul_inv,hscale]; ring)
  have hh := mul_le_mul_of_nonneg_left (hlow (WithLp.ofLp y) hy (WithLp.toLp 2 t)) β.property.le
  have hpow : (R : ℝ)^(-s.val-2) = (N : ℝ)^(-(s.val+2)*ε) := by
    dsimp only [R]
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ N)]
    congr 1
    ring
  rw [hpow] at hh
  have heder : fderiv ℝ (fderiv ℝ U) y (WithLp.toLp 2 t) (WithLp.toLp 2 t) =
      β.val*fderiv ℝ (fderiv ℝ (fun x => W x+P x)) y (WithLp.toLp 2 t) (WithLp.toLp 2 t) := by
    rw [he.fderiv.fderiv_eq,
      PhysicalCollision.internal_hessian_const_mul ((hWy.of_le (by simp)).add hP)]
  change β.val*(a*(∑ i,t i^2)) ≤
    β.val*fderiv ℝ (fderiv ℝ (fun x => W x+P x)) y (WithLp.toLp 2 t) (WithLp.toLp 2 t) at hh
  rw [← heder,Intrinsic.hessianMatrix_bilinear hUy] at hh
  simpa only [a,mul_assoc] using hh

end Riesz2.PhysicalIdentity.Internal

namespace Riesz2.PhysicalCore

/-- See the proof of Lemma 5.4 in the paper (full-cycle coercivity) and Subsection 5.1:
the actual full core has a strictly positive lower bound at every
point of its whole carrier, for every admissible reference cutoff. -/
theorem fullMatrix_lower (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K : ℕ) (hK : 1 ≤ K) (hKN : K ≤ (N : ℕ)/4)
    (θ : PhysicalCutoff) (ε κ₀ : ℝ) (hε : 0 ≤ ε) :
    ∃ b : ℝ, 0 < b ∧ ∀ (y : EuclideanSpace ℝ (Fin (N : ℕ))) (t : Fin (N : ℕ) → ℝ),
      b*(∑ i,t i^2) ≤ ∑ i,∑ j,t i*fullMatrix s N hN K θ ε κ₀ y i j*t j := by
  obtain ⟨U,hU,hv,_⟩ := PhysicalFormDomain.full_form_domain β s N hN θ ε
  obtain ⟨ha,hlow⟩ := PhysicalIdentity.Internal.full_physical_lower β s N hN θ ε hε U hU hv
  obtain ⟨c,hc,href⟩ := referenceIntervalMatrix_truncated_coercivity s
  let a := min 1 (s.val*(s.val+1))*(N : ℝ)^(-(s.val+2)*ε)
  let d := 2*c*(K : ℝ)^(-1-s.val)
  have hd : 0 < d := by
    dsimp only [d]
    exact mul_pos (by positivity) (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < K by omega)) _)
  refine ⟨min a d,lt_min ha hd,fun y t => ?_⟩
  by_cases hy : y ∈ fullGapGoodSet s N ε κ₀
  · have hh := hlow y hy.1 t
    have heq : hessianMatrix U y = β.val • fullMatrix s N hN K θ ε κ₀ y := by
      ext i j
      simp only [fullMatrix,ite_eq_left hy,Matrix.smul_apply,smul_eq_mul,Matrix.add_apply,Matrix.of_apply]
      exact PhysicalIdentity.Internal.full_hessian_eq β s N hN θ ε U hU hv y hy.1 i j
    rw [heq] at hh
    have hfactor : (∑ i,∑ j,t i*(β.val • fullMatrix s N hN K θ ε κ₀ y) i j*t j) =
        β.val*(∑ i,∑ j,t i*fullMatrix s N hN K θ ε κ₀ y i j*t j) := by
      simp only [Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hfactor] at hh
    have hh' : a*(∑ i,t i^2) ≤ ∑ i,∑ j,t i*fullMatrix s N hN K θ ε κ₀ y i j*t j :=
      (mul_le_mul_iff_right₀ β.property).mp (by simpa only [a,mul_assoc] using hh)
    exact (mul_le_mul_of_nonneg_right (min_le_left a d) (Finset.sum_nonneg fun i _ => sq_nonneg _)).trans hh'
  · have href' := (FiniteMatrixOrder.smul_one_le_iff
      (referenceIntervalMatrix_isHermitian s N hN K) _).mp (href N hN K hK hKN).2.2 t
    have hh := mul_le_mul_of_nonneg_left href' (by norm_num : (0 : ℝ) ≤ 2)
    have hh' : d*(∑ i,t i^2) ≤ ∑ i,∑ j,t i*fullMatrix s N hN K θ ε κ₀ y i j*t j := by
      simpa only [fullMatrix,ite_eq_right hy,Matrix.smul_apply,smul_eq_mul,d,Matrix.mulVec,
        dotProduct,Finset.mul_sum,mul_assoc,mul_left_comm,mul_comm,pow_two] using hh
    exact (mul_le_mul_of_nonneg_right (min_le_right a d) (Finset.sum_nonneg fun i _ => sq_nonneg _)).trans hh'

end Riesz2.PhysicalCore

namespace Riesz2.PhysicalIdentity

/-- The closed lift of the zero-sum component constraint to the
original scalar Sobolev product. It is the kernel of the continuous sum
map. -/
def fullZeroSumSpace {α : Type*} [MeasurableSpace α] {ρ : Measure α}
    (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q) (N : ℕ+) :
    Submodule ℝ (MatrixEnergy.Vector (ι := Fin (N : ℕ)) Q hQ) :=
  (∑ i : Fin (N : ℕ), PiLp.proj 2 (fun _ : Fin (N : ℕ) => ScalarFormHilbert.Space Q hQ) i).ker

/-- The lifted full-cycle constraint is a complete closed subspace. -/
theorem isClosed_fullZeroSumSpace {α : Type*} [MeasurableSpace α] {ρ : Measure α}
    (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q) (N : ℕ+) :
    IsClosed (fullZeroSumSpace Q hQ N : Set (MatrixEnergy.Vector (ι := Fin (N : ℕ)) Q hQ)) :=
  ContinuousLinearMap.isClosed_ker _

/-- Exact bridge to the zero-sum component predicate on the physical
Sobolev domain. -/
theorem mem_fullZeroSumSpace_iff {α : Type*} [MeasurableSpace α] {ρ : Measure α}
    (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q) (N : ℕ+)
    (u : MatrixEnergy.Vector (ι := Fin (N : ℕ)) Q hQ) :
    u ∈ fullZeroSumSpace Q hQ N ↔
      ∀ᵐ x ∂ρ, (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val x) ∈ zeroSumComponents (Fin (N : ℕ)) := by
  have he : u ∈ fullZeroSumSpace Q hQ N ↔ ∑ i, ScalarFormHilbert.value Q hQ (u i) = 0 := by
    change (∑ i : Fin (N : ℕ), PiLp.proj 2 (fun _ : Fin (N : ℕ) => ScalarFormHilbert.Space Q hQ) i) u = 0 ↔ _
    simp only [sum_apply,PiLp.proj_apply]
    rw [← map_sum]
    exact ⟨fun h => by rw [h,map_zero],fun h => ScalarFormHilbert.value_injective Q hQ (by simpa only [map_zero] using h)⟩
  rw [he,Lp.eq_zero_iff_ae_eq_zero]
  have hsum := Lp.coeFn_fun_finsetSum Finset.univ (fun i : Fin (N : ℕ) => ScalarFormHilbert.value Q hQ (u i))
  constructor
  · intro hz
    filter_upwards [hsum,hz] with x hx hx0
    change ∑ i,(MatrixEnergy.vectorEquiv Q hQ u i).val x = 0
    exact hx.symm.trans hx0
  · intro hz
    filter_upwards [hsum,hz] with x hx hx0
    exact hx.trans hx0

end Riesz2.PhysicalIdentity

namespace Riesz2.PhysicalIdentity.Internal

/-- Change only the finite product norm in a literal physical multiplication form. -/
theorem vectorize_form {α : Type*} [MeasurableSpace α] {ρ : Measure α}
    (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q) (N : ℕ+)
    (M : α → Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (H₀ : (Fin (N : ℕ) → ScalarFormHilbert.Space Q hQ) →L[ℝ]
      (Fin (N : ℕ) → ScalarFormHilbert.Space Q hQ) →L[ℝ] ℝ)
    (hH₀ : ∀ u v : Fin (N : ℕ) → Q.1,
      Integrable (matrixFieldPair M (fun i => (u i).val) (fun i => (v i).val)) ρ ∧
      H₀ (fun i => (ScalarFormHilbert.equiv Q hQ).symm (u i))
        (fun i => (ScalarFormHilbert.equiv Q hQ).symm (v i)) =
          ∫ z,matrixFieldPair M (fun i => (u i).val) (fun i => (v i).val) z ∂ρ) :
    ∃ H : MatrixEnergy.Vector (ι := Fin (N : ℕ)) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := Fin (N : ℕ)) Q hQ →L[ℝ] ℝ,
      ∀ u v, Integrable (matrixFieldPair M
        (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ v i).val)) ρ ∧
        H u v = ∫ z,matrixFieldPair M
          (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ v i).val) z ∂ρ := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (N : ℕ) => ScalarFormHilbert.Space Q hQ)
  refine ⟨H₀.bilinearComp e.toContinuousLinearMap e.toContinuousLinearMap,fun u v => ?_⟩
  have hh := hH₀ (MatrixEnergy.vectorEquiv Q hQ u) (MatrixEnergy.vectorEquiv Q hQ v)
  have hu : (fun i => (ScalarFormHilbert.equiv Q hQ).symm
      (MatrixEnergy.vectorEquiv Q hQ u i)) = e u := by
    funext i
    exact (ScalarFormHilbert.equiv Q hQ).symm_apply_apply (u i)
  have hv' : (fun i => (ScalarFormHilbert.equiv Q hQ).symm
      (MatrixEnergy.vectorEquiv Q hQ v i)) = e v := by
    funext i
    exact (ScalarFormHilbert.equiv Q hQ).symm_apply_apply (v i)
  refine ⟨hh.1,?_⟩
  change H₀ (e u) (e v) = _
  rw [← hu,← hv']
  exact hh.2

/-- The actual bounded full core defines a continuous multiplication form
on the original intrinsic Sobolev product. -/
theorem full_core_form (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ)
    {ρ : Measure (gapTangentSpace N)} (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q) :
    ∃ B : MatrixEnergy.Vector (ι := Fin (N : ℕ)) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := Fin (N : ℕ)) Q hQ →L[ℝ] ℝ,
      ∀ u v, Integrable (matrixFieldPair
        (fun z => PhysicalCore.fullMatrix s N hN K θ ε κ₀ (WithLp.toLp 2 (fun i => 1+z.val i)))
        (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ v i).val)) ρ ∧
      B u v = ∫ z,matrixFieldPair
        (fun z => PhysicalCore.fullMatrix s N hN K θ ε κ₀ (WithLp.toLp 2 (fun i => 1+z.val i)))
        (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ v i).val) z ∂ρ := by
  let Y := fun z : gapTangentSpace N => WithLp.toLp 2 (fun i => 1+z.val i)
  have hY : Measurable Y := (PhysicalCollision.intrinsic_chart_contDiff N).continuous.measurable
  obtain ⟨C,hC,hb⟩ := PhysicalCore.fullMatrix_bounded β s N hN K θ ε κ₀
  exact carrier_matrix_form (fun z : gapTangentSpace N => z) Q hQ (MeasurePreserving.id ρ)
    (fun z => PhysicalCore.fullMatrix s N hN K θ ε κ₀ (Y z))
    (fun a b => (PhysicalCore.measurable_fullMatrix s N hN K θ ε κ₀ a b).comp hY)
    ⟨C,hC,fun z a b => hb (Y z) a b⟩

/-- The actual intrinsic law is supported on the positive full simplex,
so the ambient physical curvature bound holds almost everywhere. -/
theorem full_physical_lower_ae (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (θ : PhysicalCutoff) (ε : ℝ) (hε : 0 ≤ ε)
    (U : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ)
    (hU : ContDiffOn ℝ ∞ U (gapAmbientDomain N))
    (hv : ∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
      U y.val = fullPhysicalPotentialValue (ofLong β s) N hN θ ε false y) :
    let ρ := fullIntrinsicTiltedGapLaw (ofLong β s) N θ ε false
    let a := min 1 (s.val*(s.val+1))*(N : ℝ)^(-(s.val+2)*ε)
    ∀ᵐ z ∂ρ, ∀ t : Fin (N : ℕ) → ℝ,
      β.val*a*(∑ i,t i^2) ≤ ∑ i,∑ j,t i*hessianMatrix U (WithLp.toLp 2 (fun i => 1+z.val i)) i j*t j := by
  intro ρ a
  obtain ⟨V,_,_,hg,_⟩ := PhysicalFormDomain.full_trace_inputs β s N hN θ ε
  have hs := IntrinsicScalarCore.supported (AffineMetric.intrinsicGapDomain_isOpen N) hg
  have hl := (full_physical_lower β s N hN θ ε hε U hU hv).2
  filter_upwards [hs] with z hz
  exact hl _ (PhysicalCollision.intrinsic_chart_mem_simplex N hz)

end Riesz2.PhysicalIdentity.Internal

