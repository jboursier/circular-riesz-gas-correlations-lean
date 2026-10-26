/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.PaperCutoffDegree
public import Riesz2.DecayLong.PhysicalPerturbationPart2
public import Riesz2.Frozen.ProperMarginalDomain
public import Riesz2.DecayShort.PhysicalComparisonPart2

/-!
# Proper physical marginal decay

Full-domain solvability and comparison estimates for Proposition 5.18.
All physical objects and scalar domains are the existing ones.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators ENNReal Classical

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.ProperMarginalDecay

/-- See Proposition 5.18 of the paper: the point-source L² norm has no size factor. -/
theorem point_source_norm_internal {X ι : Type*} [MeasurableSpace X]
    [Fintype ι] [DecidableEq ι] {ν : Measure X} (i₀ : ι) (χ : Lp ℝ 2 ν) :
    ‖(WithLp.toLp 2 (fun i => if i = i₀ then χ else 0) :
      PiLp 2 (fun _ : ι => Lp ℝ 2 ν))‖ = ‖χ‖ := by
  have he : (WithLp.toLp 2 (fun i => if i = i₀ then χ else 0) :
      PiLp 2 (fun _ : ι => Lp ℝ 2 ν)) = PiLp.single 2 i₀ χ := by
    apply PiLp.ext
    intro i
    simp only [PiLp.single_apply]
  rw [he, PiLp.norm_single]

/-- See Proposition 5.18 of the paper: the actual physical Hessian is symmetric and
has the uniform forcing mass, on the support of the actual proper law. -/
theorem physical_matrix_lower_internal
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) (hε : 0 ≤ ε) :
    let ν := activeTiltedGapLaw (ofLong β s) ((n : ℕ)+m).succPNat n (by simp; omega) θ ε false
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      β.val * ∑ i, θ.val ((n : ℝ)^(-ε)*x i) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (x,z)).toReal)
    let a := β.val * min 1 (s.val*(s.val+1)) * (n : ℝ)^(-(s.val+2)*ε)
    0 < a ∧ ∀ᵐ x ∂ν, (∀ i j, hessianMatrix V x i j = hessianMatrix V x j i) ∧
      ∀ t : Fin (n : ℕ) → ℝ,
        a * (∑ i, t i^2) ≤ ∑ i, ∑ j, t i*hessianMatrix V x i j*t j := by
  intro ν V a
  obtain ⟨ha, hl⟩ := PhysicalIdentity.proper_physical_lower β s n m θ ε hε
  have hpot := PhysicalFormDomain.proper_gibbs_potential β s n m θ ε
  refine ⟨by simpa only [a, mul_assoc] using mul_pos β.property ha, ?_⟩
  filter_upwards [hl, IntrinsicScalarCore.supported
    (AffineSimplex.isOpen_chartDomain (n : ℕ) ((n+m : ℕ)+1)) hpot] with x hx hΩ
  have hsm := hpot.1.contDiffAt ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds hΩ)
  have hsm' : ContDiffAt ℝ (↑(⊤ : ℕ∞)) V x := hsm
  refine ⟨fun i j => ?_, ?_⟩
  · rw [Intrinsic.hessianMatrix_eq_second hsm', Intrinsic.hessianMatrix_eq_second hsm']
    exact (hsm'.isSymmSndFDerivAt (by norm_num)).eq _ _
  simpa only [a, mul_assoc] using hx

/-- See Proposition 5.18 of the paper: unique finite-energy solutions and the coarse
L² bound for every L² source, on any realization of the physical scalar graph. -/
theorem physical_solvability_internal
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) (hε : 0 ≤ ε) :
    let ν := activeTiltedGapLaw (ofLong β s) ((n : ℕ)+m).succPNat n (by simp; omega) θ ε false
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      β.val * ∑ i, θ.val ((n : ℝ)^(-ε)*x i) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (x,z)).toReal)
    ∀ (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q →
    ∀ (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν),
      (∃! u : Fin (n : ℕ) → Q.1,
        WeightedWeakSolution Q (hessianMatrix V) ⊤ (fun i => if i=i₀ then χ else 0) u) ∧
      ∀ u : Fin (n : ℕ) → Q.1,
        WeightedWeakSolution Q (hessianMatrix V) ⊤ (fun i => if i=i₀ then χ else 0) u →
        ∀ j : Fin (n : ℕ), ‖(u j).val‖ ≤
          (β.val * min 1 (s.val*(s.val+1)))⁻¹ *
            (n : ℝ)^((s.val+2)*ε) * ‖χ‖ := by
  intro ν V Q hQ i₀ χ
  obtain ⟨ha, hM⟩ := physical_matrix_lower_internal β s n m θ ε hε
  obtain ⟨hex, hnorm⟩ := AbstractEquation.existence_energy Q hQ 1 zero_lt_one
    (hessianMatrix V) (fun i j => DifferentiatedPoisson.measurable_hessian_entries i j)
    _ ha hM ⊤ (fun i => if i=i₀ then χ else 0)
  simp only [one_smul, one_mul] at hex hnorm
  refine ⟨hex, fun u hu j => ?_⟩
  have hj : ‖(u j).val‖ ≤ ‖(WithLp.toLp 2 (fun i => (u i).val) :
      PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν))‖ :=
    PiLp.norm_apply_le (WithLp.toLp 2 (fun i => (u i).val)) j
  have hh := hj.trans (hnorm u hu).1
  rw [point_source_norm_internal] at hh
  apply hh.trans_eq
  rw [show -(s.val+2)*ε = -((s.val+2)*ε) by ring,
    mul_inv_rev, Real.rpow_neg (by positivity : (0 : ℝ) ≤ n), inv_inv]
  ring

open PhysicalCore

/-- See Proposition 5.18 of the paper: the structural exponents and admissible epsilon
range are independent of the physical cutoff. This refines the quantifier
order of `PhysicalMean.proper_matrix_bounds_uniform_internal`, assembling
its existing coefficient estimates before choosing the cutoff prefactor. -/
theorem structural_bounds_internal (s : Riesz1.RieszExponent)
    (M₀ : ℕ) (κ₀ : ℝ) (hκ₀ : 0 ≤ κ₀) :
    ∃ ε₀ κ γ : ℝ, 0 < ε₀ ∧ 0 < κ ∧ 0 < γ ∧
      ∀ θ : PhysicalCutoff, ∃ C : ℝ, 1 ≤ C ∧ ∀ β : InverseTemperature,
        ∀ ε : ℝ, 0 ≤ ε → ε ≤ ε₀ →
        ∀ (n : ℕ+) (m : ℕ) (hn : 2*(n : ℕ) ≤ (n : ℕ)+m+1),
        let N := ((n : ℕ)+m).succPNat
        let M := properReferencePeriod s n N
        let hM : 2 ≤ (M : ℕ) := by
          change 2 ≤ (properReferencePeriod s n N : ℕ)
          have := (properReferencePeriod_bounds s n N hn).1
          have := n.pos
          omega
        let hnM : (n : ℕ) ≤ (M : ℕ) := by
          change (n : ℕ) ≤ (properReferencePeriod s n N : ℕ)
          have := (properReferencePeriod_bounds s n N hn).1
          omega
        let K := ⌊(n : ℝ)^ε⌋₊^M₀
        K ≤ (M : ℕ)/4 →
        ∀ μ : Measure (AffineSimplex.chartDomain n ((n+m : ℕ)+1)),
          PeriodizedMatrixBounds (ν := μ) s n M hM K C κ γ ε
            (properMatrix β s n m M hM hnM K θ ε κ₀) := by
  obtain ⟨c₁,hc₁,hcoerc⟩ := properMatrix_cutoff_coercivity s
  obtain ⟨c₂,hc₂,hlower⟩ := properIntervalWeight_threshold_lower s
  let kE := κ₀+s.val+3+(M₀ : ℝ)
  let kC := s.val+2+(M₀ : ℝ)*(1+s.val)
  let κ := kE+kC
  let γ := (M₀ : ℝ)+1
  have hkE : 0 < kE := by dsimp only [kE]; have := Nat.cast_nonneg M₀ (α := ℝ); linarith [s.property.1]
  have hkC : 0 < kC := by dsimp only [kC]; have := s.property.1; positivity
  have hi₁ : 0 < c₁⁻¹ := inv_pos.mpr hc₁
  have hi₂ : 0 < c₂⁻¹ := inv_pos.mpr hc₂
  refine ⟨(1-s.val/2)/2,κ,γ,by linarith [s.property.2],by dsimp only [κ]; positivity,
    by dsimp only [γ]; positivity,?_⟩
  intro θ
  obtain ⟨U,hU,hupper⟩ := properIntervalWeight_upper s θ
  obtain ⟨E,hE,hentry⟩ := properActive_entry_error s θ
  let C := 1+U+E+c₁⁻¹+c₂⁻¹
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hCU : U ≤ C := by dsimp only [C]; linarith
  have hCE : E ≤ C := by dsimp only [C]; linarith
  have hcC₁ : C⁻¹ ≤ c₁ := (inv_le_comm₀ hC0 hc₁).mpr (by dsimp only [C]; linarith)
  have hcC₂ : C⁻¹ ≤ c₂ := (inv_le_comm₀ hC0 hc₂).mpr (by dsimp only [C]; linarith)
  refine ⟨C,hC,?_⟩
  intro β ε hε hεa n m hn N M hM hnM K hKM μ
  have hhalf : 2*(n : ℕ) ≤ (M : ℕ) := (properReferencePeriod_bounds s n N hn).1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by positivity
  have lower (c l : ℝ) (hc : 0 < c) (hcl : C⁻¹ ≤ c) (hl : l ≤ κ) :
      C⁻¹*(n : ℝ)^(-κ*ε) ≤ c*(n : ℝ)^(-l*ε) := by
    exact mul_le_mul hcl (Real.rpow_le_rpow_of_exponent_le hn1
      (by nlinarith only [hl,hε])) (Real.rpow_nonneg hn0.le _) hc.le
  have upper (c l : ℝ) (hc : 0 ≤ c) (hcl : c ≤ C) (hl : l ≤ κ) :
      c*(n : ℝ)^(l*ε) ≤ C*(n : ℝ)^(κ*ε) :=
    mul_le_mul hcl (Real.rpow_le_rpow_of_exponent_le hn1
      (mul_le_mul_of_nonneg_right hl hε)) (Real.rpow_nonneg hn0.le _) hC0.le
  have hkEκ : kE ≤ κ := by dsimp only [κ]; linarith
  have hkCκ : kC ≤ κ := by dsimp only [κ]; linarith
  have hkUκ : κ₀+s.val+2 ≤ κ := by dsimp only [kE] at hkEκ; have := Nat.cast_nonneg M₀ (α := ℝ); linarith
  have hksκ : s.val+2 ≤ κ := by linarith
  refine ⟨measurable_properMatrix β s n m M hM hnM K θ ε κ₀,?_,?_⟩
  · apply ae_of_all
    intro x
    have hsym := properMatrix_symmetric β s n m M hM hnM K θ ε κ₀ x
    have hHerm : (properMatrix β s n m M hM hnM K θ ε κ₀ x).IsHermitian := by
      ext a b
      simp only [Matrix.conjTranspose_apply,star_trivial,hsym]
    refine ⟨hsym,properMatrix_exterior β s n m M hM hnM K θ ε κ₀ x,?_,?_⟩
    · intro z
      have hh := (FiniteMatrixOrder.smul_one_le_iff hHerm _).mp
        (hcoerc M₀ β n m hn M hM hhalf θ ε κ₀ hε hKM x) z
      have hh' : c₁*(n : ℝ)^(-kC*ε)*(∑ i,z i^2) ≤
          ∑ i,∑ j,z i*properMatrix β s n m M hM hnM K θ ε κ₀ x i j*z j := by
        simpa only [kC,Matrix.mulVec,dotProduct,Finset.mul_sum,mul_assoc,pow_two] using hh
      exact (mul_le_mul_of_nonneg_right (lower c₁ kC hc₁ hcC₁ hkCκ)
        (Finset.sum_nonneg (fun i _ => sq_nonneg (z i)))).trans hh'
    · intro a b ha hb
      let a' : Fin (n : ℕ) := ⟨a.val,ha⟩
      let b' : Fin (n : ℕ) := ⟨b.val,hb⟩
      have ha' : a'.castLE hnM = a := Fin.ext rfl
      have hb' : b'.castLE hnM = b := Fin.ext rfl
      have he := hentry M₀ β n m hn ε κ₀ hε hεa hκ₀ x a' b'
      rw [← properMatrix_active β s n m M hM hnM K θ ε κ₀ x a' b',ha',hb'] at he
      exact he.trans (by
        simpa only [Matrix.smul_apply,smul_eq_mul] using mul_le_mul_of_nonneg_right
          (upper E kE hE.le hCE hkEκ)
          (Real.rpow_nonneg (by positivity : 0 ≤ 1+(Riesz1.cyclicIndexDistance M a b : ℝ)) (-1-s.val/2)))
  · refine ⟨properIntervalWeight β s n m hn M hM hhalf K θ ε κ₀,
      measurable_properIntervalWeight β s n m hn M hM hhalf K θ ε κ₀,ae_of_all _ (fun x => ?_)⟩
    refine ⟨fun i r => ⟨properIntervalWeight_nonneg β s n m hn M hM hhalf K θ ε κ₀ i r x,?_,?_⟩,
      properMatrix_interval_quadratic β s n m hn M hM hhalf K θ ε κ₀ x⟩
    · exact (hupper β n m hn M hM hhalf K ε κ₀ hε hεa hκ₀ x i r).trans
        (mul_le_mul_of_nonneg_right (upper U (κ₀+s.val+2) hU.le hCU hkUκ) (by positivity))
    · intro hr
      exact (mul_le_mul_of_nonneg_right (lower c₂ (s.val+2) hc₂ hcC₂ hksκ) (by positivity)).trans
        (hlower M₀ γ (by dsimp only [γ]; linarith) β n m hn M hM hhalf θ ε κ₀ hε x i r hr)


/-- See Proposition 5.18 of the paper: summing the single-component tests recovers
the full perturbation pairing on the same Hilbert product. -/
theorem pairing_sum_internal {X ι : Type*} [MeasurableSpace X]
    [Fintype ι] [DecidableEq ι] {ν : Measure X}
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (T : MatrixEnergy.Vector (ι := ι) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := ι) Q hQ →L[ℝ] ℝ)
    (v w : MatrixEnergy.Vector (ι := ι) Q hQ) :
    T v w = ∑ j, T v (PiLp.single 2 j
      ((ScalarFormHilbert.equiv Q hQ).symm (MatrixEnergy.vectorEquiv Q hQ w j))) := by
  have he : w = ∑ j, PiLp.single 2 j
      ((ScalarFormHilbert.equiv Q hQ).symm (MatrixEnergy.vectorEquiv Q hQ w j)) := by
    apply PiLp.ext
    intro i
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.single_apply]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true]
    exact ((ScalarFormHilbert.equiv Q hQ).symm_apply_apply (w i)).symm
  conv_lhs => rw [he]
  exact map_sum (T v) _ _

open PhysicalPerturbation

/-- Identify the entire form in Proposition 5.18 with the actual bounded-input
operator of Lemma 5.17. The native row identities are used
only as equalities. -/
theorem physical_pairing_identification_internal {X Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Z] {μ : Measure X} {ν : Measure Z}
    [IsFiniteMeasure ν] (f : X → Z) (hf : MeasurableEmbedding f)
    (hco : MeasurePreserving f μ ν) (n : ℕ+)
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (D : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (hD : ∀ x i j, D x i j = D x j i)
    (Y : Z → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (hY : ∀ i k, Integrable (fun x => Y x i k) ν)
    (he : ∀ x i k, Y (f x) i k = D x i k)
    (Sop : PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν) →L[ℝ]
      PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν))
    (T G : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ] ℝ)
    (hT : ∀ v z, T v z = (∫ x, ∑ i, ∑ k,
      (MatrixEnergy.vectorEquiv Q hQ v i).val (f x)*D x i k*
        (MatrixEnergy.vectorEquiv Q hQ z k).val (f x) ∂μ)+G v z)
    (v w : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ)
    (hG : ∀ j, G v (PiLp.single 2 j ((ScalarFormHilbert.equiv Q hQ).symm
      (MatrixEnergy.vectorEquiv Q hQ w j))) =
      ∑ k, inner ℝ (PiLp.single 2 j (MatrixEnergy.vectorEquiv Q hQ w j).val)
        (Sop (PiLp.single 2 k (MatrixEnergy.vectorEquiv Q hQ v k).val)))
    (Bv Bw : ℝ)
    (hv : ∀ k, ∀ᵐ x ∂ν, |(MatrixEnergy.vectorEquiv Q hQ v k).val x| ≤ Bv)
    (hw : ∀ k, ∀ᵐ x ∂ν, |(MatrixEnergy.vectorEquiv Q hQ w k).val x| ≤ Bw) :
    let vB : Fin (n : ℕ) → BoundedL2Pairings.boundedSubmodule ν :=
      fun k => ⟨(MatrixEnergy.vectorEquiv Q hQ v k).val,Bv,hv k⟩
    let uB : Fin (n : ℕ) → BoundedL2Pairings.boundedSubmodule ν :=
      fun k => ⟨(MatrixEnergy.vectorEquiv Q hQ w k).val,Bw,hw k⟩
    T v w = ColumnSubtraction.pairing (BoundedPerturbationOperator.field uB)
      (BoundedPerturbationOperator.operator Y hY Sop (BoundedPerturbationOperator.field vB)) := by
  intro vB uB
  rw [pairing_sum_internal,BoundedPerturbationOperator.pairing_operator_columns]
  apply Finset.sum_congr rfl
  intro j _
  have hi (k : Fin (n : ℕ)) : Integrable (fun x =>
      (uB j).val (f x)*(vB k).val (f x)*D x j k) μ := by
    have hh := BoundedL2Pairings.integrable_product (fun x => Y x j k) (hY j k) (uB j) (vB k)
    exact ((hco.integrable_comp_emb hf).mpr hh).congr
      (ae_of_all _ fun x => by dsimp only [Function.comp_apply]; rw [he]; ring)
  rw [hT,hG,multiplication_row_internal f hco Q hQ D hD v j
    (MatrixEnergy.vectorEquiv Q hQ w j) hi]
  simp only [BoundedPerturbationOperator.point,Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [← hco.integral_comp hf (fun x => (uB j).val x*Y x j k*(vB k).val x)]
  exact integral_congr_ae (ae_of_all _ fun x => by dsimp only; rw [he]; ring)

/-- Uniform coefficient absorption for the complete pairing in Proposition 5.18
and Lemma 5.17, before the temperature and volume are chosen. -/
theorem full_pairing_coefficients_internal (s : Riesz1.RieszExponent) (n : ℕ+)
    (p ε Cr Cm q kr km c δ Ka B F W : ℝ)
    (hCr : 0 ≤ Cr) (hCm : 0 ≤ Cm) (hq : 0 < q) (hKa : 0 ≤ Ka)
    (hF : 0 ≤ F) (hW : 0 ≤ W)
    (ha : (n : ℝ)^(kr*ε+7/2+2*p*ε)*Real.exp (-c*(n : ℝ)^δ) ≤
      Ka*Real.exp (-(c/2)*(n : ℝ)^δ)) :
    let P := q⁻¹*(n : ℝ)^(p*ε)*B
    let C := Cr*ColumnSubtraction.sourceConstant s*Cm+6*Cr*q⁻¹^2*Ka
    (Cr*(n : ℝ)^(kr*ε))*ColumnSubtraction.sourceConstant s*((Cm*(n : ℝ)^(km*ε))*F)*
        Real.sqrt (2/(1-s.val))*(n : ℝ)^(-(1/2 : ℝ))*W +
      3*(Cr*(n : ℝ)^(kr*ε))*(n : ℝ)^(5/2 : ℝ)*Real.exp (-c*(n : ℝ)^δ)*
        ((n : ℝ)*(2*P))*((n : ℝ)*P) ≤
      C*(n : ℝ)^((kr+km)*ε)*Real.sqrt (2/(1-s.val))*F*(n : ℝ)^(-(1/2 : ℝ))*W+
        (n : ℝ)*C*Real.exp (-(c/2)*(n : ℝ)^δ)*B^2 := by
  intro P C
  have hn0 : (0 : ℝ) < n := by positivity
  have hmainC : Cr*ColumnSubtraction.sourceConstant s*Cm ≤ C :=
    le_add_of_nonneg_right (by positivity)
  have herrC : 6*Cr*q⁻¹^2*Ka ≤ C := le_add_of_nonneg_left (by
    have := ColumnSubtraction.sourceConstant_pos s; positivity)
  apply add_le_add
  · have hpow : (n : ℝ)^((kr+km)*ε) = (n : ℝ)^(kr*ε)*(n : ℝ)^(km*ε) := by
      rw [add_mul,Real.rpow_add hn0]
    rw [hpow]
    have hh := mul_le_mul_of_nonneg_right hmainC
      (show 0 ≤ (n : ℝ)^(kr*ε)*(n : ℝ)^(km*ε)*Real.sqrt (2/(1-s.val))*F*
        (n : ℝ)^(-(1/2 : ℝ))*W by positivity)
    convert hh using 1 <;> ring
  · calc
      _ = (6*Cr*q⁻¹^2)*(n : ℝ)*((n : ℝ)^(kr*ε+7/2+2*p*ε)*
          Real.exp (-c*(n : ℝ)^δ))*B^2 := by
        dsimp only [P]
        rw [show kr*ε+7/2+2*p*ε = kr*ε+((5/2:ℝ)+1)+((p*ε)+(p*ε)) by ring]
        simp only [Real.rpow_add hn0,Real.rpow_one,pow_two]
        ring
      _ ≤ (6*Cr*q⁻¹^2)*(n : ℝ)*(Ka*Real.exp (-(c/2)*(n : ℝ)^δ))*B^2 := by
        gcongr
      _ ≤ (n : ℝ)*C*Real.exp (-(c/2)*(n : ℝ)^δ)*B^2 := by
        have hh := mul_le_mul_of_nonneg_right herrC
          (show 0 ≤ (n : ℝ)*Real.exp (-(c/2)*(n : ℝ)^δ)*B^2 by positivity)
        nlinarith only [hh]

set_option backward.isDefEq.respectTransparency false in
/-- See Proposition 5.18 of the paper: the full perturbation pairing from
Lemma 5.17, with its loss chosen before the cutoff and its
exceptional polynomial absorbed uniformly before temperature and volume. -/
theorem uniform_perturbation_operator_internal (hRig : External.LongRangeRigidityLocallyUniform)
    (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (M₀ : ℕ+)
    (κ₀ : ℝ) (hκ₀ : 1 ≤ κ₀) :
    ∃ ε₀ κ ks gs : ℝ,
      0 < ε₀ ∧ 0 < κ ∧ 0 < ks ∧ 0 < gs ∧
    ∀ θ : PhysicalCutoff, ∃ Cstar : ℝ, ∃ hCstar : 1 ≤ Cstar,
    ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    ∀ (n : ℕ+) (m : ℕ) (hn : 2 ≤ (n : ℕ))
      (hnN : 2*(n : ℕ) ≤ (n : ℕ)+m+1),
    let N := ((n : ℕ)+m).succPNat
    let M := properReferencePeriod s n N
    let hM : 2 ≤ (M : ℕ) := by
      change 2 ≤ (properReferencePeriod s n N : ℕ)
      have := (properReferencePeriod_bounds s n N hnN).1
      omega
    let hnM : (n : ℕ) ≤ (M : ℕ) := by
      change (n : ℕ) ≤ (properReferencePeriod s n N : ℕ)
      have := (properReferencePeriod_bounds s n N hnN).1
      omega
    let K := ⌊(n : ℝ)^ε⌋₊^(M₀ : ℕ)
    1 ≤ K → 4*K ≤ (M : ℕ) →
    let ν := activeTiltedGapLaw (ofLong β s) N n (by simp only [N,Nat.succPNat_coe]; omega) θ ε false
    let Ω := AffineSimplex.chartDomain n ((n+m : ℕ)+1)
    ∃ Q : ScalarFormData ν, IsNeumannRealization Ω Q ∧
    ∃ hQ : IsClosedScalarDirichletForm Q, IsConservativeScalarForm Q ∧
    ∃ A : EuclideanSpace ℝ (Fin (n : ℕ)) → Matrix (Fin (M : ℕ)) (Fin (M : ℕ)) ℝ,
      (∀ x : Ω, A x.val = properMatrix β s n m M hM hnM K θ ε κ₀ x) ∧
    ∃ hA : PeriodizedMatrixBounds (ν := ν) s n M hM K Cstar ks gs ε A,
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      β.val * ∑ i, θ.val ((n : ℝ)^(-ε)*x i) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (x,z)).toReal)
    ∃ S Aphys T : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ] ℝ,
    (∀ (W : Submodule ℝ (Fin (n : ℕ) → ℝ)) (u : Fin (n : ℕ) → Q.1),
      WeightedFormDomain Q (hessianMatrix V) W u ↔
        ∀ᵐ x ∂ν, (fun i => (u i).val x) ∈ W) ∧
    (∀ u z, Integrable (matrixFieldPair (hessianMatrix V)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ z i).val)) ν ∧
      Aphys u z = OperatorSchur.vectorEnergy Q hQ u z + ∫ x,
        matrixFieldPair (hessianMatrix V)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ z i).val) x ∂ν) ∧
    S = SchurRestriction.schurForm Q hQ n M hnM s hM K Cstar ks gs ε β.val
      hCstar β.property A hA ∧ Aphys = S + T ∧
    (∀ f : PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν),
      (∃! v, ∀ z, S v z = inner ℝ f (OperatorSchur.vectorValues Q hQ z)) ∧
      (∃! ψ, ∀ z, Aphys ψ z = inner ℝ f (OperatorSchur.vectorValues Q hQ z))) ∧
    ∀ (χ : Lp ℝ 2 ν) (B : ℝ), 0 ≤ B → (∀ᵐ x ∂ν, |χ x| ≤ B) →
    ∀ i₀ : Fin (n : ℕ), (n : ℝ)/4 ≤ (i₀.val : ℝ)+1 →
      (i₀.val : ℝ)+1 ≤ 3*(n : ℝ)/4 →
    let f := WithLp.toLp 2 (fun i : Fin (n : ℕ) => if i=i₀ then χ else 0)
    ∀ (v ψ : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ),
      (∀ z, S v z = inner ℝ f (OperatorSchur.vectorValues Q hQ z)) →
      (∀ z, Aphys ψ z = inner ℝ f (OperatorSchur.vectorValues Q hQ z)) →
    |T v (v-ψ)| ≤
      C*(n : ℝ)^(κ*ε)*Real.sqrt (2/(1-s.val))*‖χ‖*(n : ℝ)^(-(1/2 : ℝ))*
        ‖OperatorSchur.vectorValues Q hQ (v-ψ)‖ +
      (n : ℝ)*C*Real.exp (-c*(n : ℝ)^GoodBlocks.coefficientTailPower s.val ε)*B^2 := by
  choose ε₀ ks gs he₀ hks hgs hbounds using
    structural_bounds_internal s M₀ κ₀ (by linarith)
  choose km hkm hmean using PhysicalMean.periodized_mean_internal hzeta s ks gs hks hgs M₀
  choose kr hkr hrow using ambient_operator_internal hRig hzeta s κ₀ hκ₀ M₀ M₀.pos
  refine ⟨ε₀,kr+km,ks,gs,he₀,add_pos hkr hkm,hks,hgs,?_⟩
  intro θ
  obtain ⟨Cstar,hCstar,hbounds⟩ := hbounds θ
  choose Cθ hCθ hθ hθlower using θ.property.2.2.2.2
  let p := ks+s.val+2
  have hp : 0 < p := by dsimp [p]; linarith [s.property.1]
  refine ⟨Cstar,hCstar,?_⟩
  intro ε hε hεa βlo βhi hlo hle
  choose Cm hCm hm using hmean ε hε Cstar hCstar βlo βhi hlo hle
  choose Cr c hCr hc hr using hrow ε Cθ βlo βhi hε hCθ hlo hle
  let a₀ := min 1 (s.val*(s.val+1))
  have ha₀ : 0 < a₀ := lt_min zero_lt_one (by have := s.property.1; positivity)
  let q := min (βlo*Cstar⁻¹) (βlo*a₀)
  have hCs : 0 < Cstar := lt_of_lt_of_le zero_lt_one hCstar
  have hq : 0 < q := lt_min (by positivity) (mul_pos hlo ha₀)
  have hδ := GoodBlocks.coefficientTailPower_pos s.property.1 s.property.2 hε
  obtain ⟨Ka,hKa,ha⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := kr*ε+7/2+2*p*ε) (c := c) (c' := c/2) hδ (by linarith)
  let C := Cr*ColumnSubtraction.sourceConstant s*Cm + 6*Cr*q⁻¹^2*Ka
  have hC : 0 < C := by
    dsimp [C]
    have := ColumnSubtraction.sourceConstant_pos s
    positivity
  refine ⟨C,c/2,hC,by positivity,?_⟩
  intro β hβ n m hn hnN N M hM hnM K hK hKM ν Ω
  let μ := ν.comap ((↑) : Ω → EuclideanSpace ℝ (Fin (n : ℕ)))
  have hhalf : 2*(n : ℕ) ≤ (M : ℕ) := (PhysicalCore.properReferencePeriod_bounds s n N hnN).1
  have hKM' : K ≤ (M : ℕ)/4 := by omega
  choose hprob hne hpot2 Q hreal hQ hcons hco using
    PhysicalMean.proper_scalar_internal β s n m θ ε
  change ScalarFormData ν at Q
  change IsNeumannRealization Ω Q at hreal
  change IsClosedScalarDirichletForm Q at hQ
  change IsConservativeScalarForm Q at hcons
  change MeasurePreserving ((↑) : Ω → EuclideanSpace ℝ (Fin (n : ℕ))) μ ν at hco
  have hpot := PhysicalFormDomain.proper_gibbs_potential β s n m θ ε
  let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
    β.val * ∑ i, θ.val ((n : ℝ)^(-ε)*x i) -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (x,z)).toReal)
  have hΩ := AffineSimplex.isOpen_chartDomain (n : ℕ) ((n+m : ℕ)+1)
  have hf := MeasurableEmbedding.subtype_coe hΩ.measurableSet
  have hmat := hbounds β ε hε.le hεa n m hnN hKM' μ
  choose A heq hA using PhysicalMean.periodized_matrix_extension_internal _ hf hco s n M hM K
    Cstar ks gs ε _ hmat
  have hdata := comparison_interfaces_internal β s n m hnN M hM hhalf hnM K hK hKM' θ ε κ₀ hε.le
    Cstar ks gs hCstar Q hQ hreal hco A heq hA
  let S := hdata.choose
  have hdata := hdata.choose_spec
  let Aphys := hdata.choose
  have hdata := hdata.choose_spec
  let T := hdata.choose
  have hdata := hdata.choose_spec
  let G := hdata.choose
  have hdata := hdata.choose_spec
  let Re := hdata.choose
  have hdata := hdata.choose_spec
  have hdom := hdata.1
  have hphysical := hdata.2.1
  have hSeq := hdata.2.2.1
  have hAT := hdata.2.2.2.1
  have hRe := hdata.2.2.2.2.1
  have hG := hdata.2.2.2.2.2.1
  have hT := hdata.2.2.2.2.2.2.1
  have hsol := hdata.2.2.2.2.2.2.2
  refine ⟨Q,hreal,hQ,hcons,A,heq,hA,S,Aphys,T,hdom,?_,hSeq,hAT,hsol,?_⟩
  · intro u z
    exact hphysical u z
  intro χ B hB hχ i₀ hil hih f v ψ hv hψ
  obtain ⟨hfull,hmdec⟩ := hm β hβ n M hn hM hhalf (PhysicalMean.proper_period_upper_internal s n N)
    hK hKM n Ω ν hΩ (AffineSimplex.convex_chartDomain _ _)
    (AffineSimplex.isBounded_chartDomain _ _) hne hprob hpot2 Q hreal hQ hcons A hA i₀ hil hih χ
  let Ψ := hfull.choose
  have hΨ := hfull.choose_spec.1
  have hv' := equation_congr_internal S
    (SchurRestriction.schurForm Q hQ n M hnM s hM K Cstar ks gs ε β.val hCstar β.property A hA)
    hSeq v (fun z => inner ℝ f (OperatorSchur.vectorValues Q hQ z)) hv
  have hcomp := PhysicalMean.schur_components_internal Q hQ s n M hnM hM K Cstar ks gs ε β.val
    hCstar β.property A hA i₀ χ Ψ v hΨ hv'
  obtain ⟨hprofile,_,hsum,g,hg,hgeq,hmeanv⟩ := hmdec Ψ hΨ
  let v' := MatrixEnergy.vectorEquiv Q hQ v
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by positivity
  let P := q⁻¹*(n : ℝ)^(p*ε)*B
  have hP : 0 ≤ P := by dsimp [P]; positivity
  obtain ⟨hvB,hwB⟩ := solution_suprema_internal β s n m M hM hnM K θ ε hε Cstar ks gs p q hq
    (by dsimp [p]; linarith only [s.property.1]) (by dsimp [p]; linarith only [hks])
    ((min_le_left _ _).trans (mul_le_mul_of_nonneg_right hβ.1 (by positivity)))
    ((min_le_right _ _).trans (mul_le_mul_of_nonneg_right hβ.1 ha₀.le))
    Q hQ A hA Aphys hphysical χ B hB hχ i₀ Ψ v ψ hΨ hcomp hψ
  obtain ⟨R,hR,huniq,Y,hYe,hY,hOp,he⟩ := hr β hβ n m hn hnN
    (by simp only [Nat.succPNat_coe]; omega) θ hθ M hM hnM hhalf
    ((PhysicalMean.proper_period_upper_internal s n N).trans (by
      have : 0 ≤ (n : ℝ)^(1/2+1/s.val) := Real.rpow_nonneg hn0.le _
      linarith)) hK hKM' hco Q hQ
  have hvalue (k : Fin (n : ℕ)) : ‖(v' k).val‖ ≤
      (Cm*(n : ℝ)^(km*ε))*‖χ‖*(1+(Nat.dist k.val i₀.val : ℝ))^(-(2-s.val)) := by
    have hh := hprofile (k.castLE hnM)
    rw [hcomp] at hh
    have hd := LocalizedMatrix.active_distance M n hhalf k i₀
    simpa only [weightRadius, hd, mul_assoc,mul_comm,mul_left_comm] using hh
  let vB : Fin (n : ℕ) → BoundedL2Pairings.boundedSubmodule ν :=
    fun k => ⟨(v' k).val,P,hvB k⟩
  let w := v-ψ
  let uB : Fin (n : ℕ) → BoundedL2Pairings.boundedSubmodule ν :=
    fun j => ⟨(MatrixEnergy.vectorEquiv Q hQ w j).val,2*P,hwB j⟩
  let Sop := properSchurOperator (Q := Q) (hQ := hQ) (s := s) (n := n) (M := M)
    (hnM := hnM) (hM := hM) (K := K) (β := β.val) R
  have hdepth : (n : ℝ)/4 ≤ ((min (i₀.val+1) ((n : ℕ)-i₀.val) : ℕ) : ℝ) := by
    rw [Nat.cast_min,Nat.cast_add,Nat.cast_one,Nat.cast_sub (Nat.le_of_lt i₀.isLt)]
    exact le_min hil (by linarith)
  have hbound := ColumnSubtraction.column_subtraction_pairing_polynomial s n hn
    (Cr*(n : ℝ)^(kr*ε)) c _ (by positivity)
    (BoundedPerturbationOperator.operator Y hY Sop) hOp i₀ hdepth
    (BoundedPerturbationOperator.field vB) ((Cm*(n : ℝ)^(km*ε))*‖χ‖) (by positivity)
    (by simpa only [BoundedPerturbationOperator.coordinate_field,
      BoundedPerturbationOperator.toL2_ofBoundedScalar,vB] using hvalue)
    (by simpa only [BoundedPerturbationOperator.toL2_coordinateSum_field,vB,hcomp,v',mul_assoc,
      mul_comm,mul_left_comm] using hmeanv)
    (BoundedPerturbationOperator.field uB)
  let D := fun x : Ω => fun i k => hessianMatrix V x.val i k - β.val*
    PhysicalCore.properActive β s n m M hM hnM K θ ε κ₀ x i k
  have hD (x : Ω) (i k : Fin (n : ℕ)) : D x i k = D x k i := by
    dsimp only [D]
    have hsmooth : ContDiffAt ℝ 2 V x.val :=
      (hpot.1.of_le (by norm_num)).contDiffAt (hΩ.mem_nhds x.property)
    rw [DecayShort.PhysicalComparison.hessianMatrix_symm hsmooth i k,
      PhysicalCore.properActive_symmetric β s n m M hM hnM K θ ε κ₀ x i k]
  have hGrow (j : Fin (n : ℕ)) :
      G v (PiLp.single 2 j ((ScalarFormHilbert.equiv Q hQ).symm
        (MatrixEnergy.vectorEquiv Q hQ w j))) =
      ∑ k, inner ℝ (PiLp.single 2 j (MatrixEnergy.vectorEquiv Q hQ w j).val)
        (Sop (PiLp.single 2 k (MatrixEnergy.vectorEquiv Q hQ v k).val)) := by
    simp_rw [Sop,properSchurOperator_point]
    rw [← Finset.mul_sum]
    exact schur_correction_row_internal Q hQ s n M hnM hM K β.val β.property _ R hR huniq Re G
      hRe hG v j (MatrixEnergy.vectorEquiv Q hQ w j)
  have hpairFull := physical_pairing_identification_internal _ hf hco n Q hQ D hD Y hY
    hYe Sop T G hT v w hGrow P (2*P) hvB hwB
  rw [← hpairFull,← BoundedPerturbationOperator.source_norm,
    BoundedPerturbationOperator.source_field] at hbound
  change |T v w| ≤ _ at hbound
  apply hbound.trans
  have hu := BoundedPerturbationOperator.field_norm_le uB (2*P) (by positivity) hwB
  have hvf := BoundedPerturbationOperator.field_norm_le vB P hP hvB
  calc
    _ ≤ (Cr*(n : ℝ)^(kr*ε))*ColumnSubtraction.sourceConstant s*
        ((Cm*(n : ℝ)^(km*ε))*‖χ‖)*Real.sqrt (2/(1-s.val))*(n : ℝ)^(-(1/2 : ℝ))*
        ‖OperatorSchur.vectorValues Q hQ w‖+
      3*(Cr*(n : ℝ)^(kr*ε))*(n : ℝ)^(5/2 : ℝ)*
        Real.exp (-c*(n : ℝ)^GoodBlocks.coefficientTailPower s.val ε)*
        ((n : ℝ)*(2*P))*((n : ℝ)*P) := by
          exact add_le_add le_rfl (by gcongr)
    _ ≤ _ := full_pairing_coefficients_internal s n p ε Cr Cm q kr km c
      (GoodBlocks.coefficientTailPower s.val ε) Ka B ‖χ‖ ‖OperatorSchur.vectorValues Q hQ w‖
      hCr.le hCm.le hq hKa (norm_nonneg _) (norm_nonneg _) (ha n hn1)

/-- See Proposition 5.18 of the paper: solve the quadratic energy inequality with
the correct homogeneous dependence on both source norms. -/
theorem energy_root_internal {x a b e : ℝ} (_hx : 0 ≤ x) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (he : 0 < e) (h : e*x^2 ≤ a*x+b) :
    x ≤ e⁻¹*a + Real.sqrt (e⁻¹*b) := by
  have hs : 0 ≤ Real.sqrt (e⁻¹*b) := Real.sqrt_nonneg _
  have hsq := Real.sq_sqrt (show 0 ≤ e⁻¹*b by positivity)
  have hh := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr he.le)
  rw [← mul_assoc, inv_mul_cancel₀ he.ne', one_mul, mul_add] at hh
  by_contra hn
  have hgt : e⁻¹*a+Real.sqrt (e⁻¹*b) < x := lt_of_not_ge hn
  have hprod := mul_pos (sub_pos.mpr hgt) (show 0 < x+Real.sqrt (e⁻¹*b) by
    have : 0 ≤ e⁻¹*a := by positivity
    linarith)
  nlinarith only [hh, hsq, hprod, mul_nonneg (show 0 ≤ e⁻¹*a by positivity) hs]

/-- See Proposition 5.18 of the paper: physical coercivity and the full pairing of
Lemma 5.17 give a bound for the entire difference in vector L². -/
theorem difference_norm_from_pairing_internal {X : Type*} [MeasurableSpace X]
    {ν : Measure X} (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (s : Riesz1.RieszExponent) (n : ℕ+)
    (T : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ] ℝ)
    (v w : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ)
    (A F E B mass : ℝ) (hA : 0 ≤ A) (hF : 0 ≤ F) (hE : 0 ≤ E)
    (hB : 0 ≤ B) (hmass : 0 < mass)
    (henergy : mass*‖OperatorSchur.vectorValues Q hQ w‖^2 ≤ T v w)
    (hpair : |T v w| ≤ A*Real.sqrt (2/(1-s.val))*F*(n : ℝ)^(-(1/2 : ℝ))*
      ‖OperatorSchur.vectorValues Q hQ w‖+(n : ℝ)*E*B^2) :
    ‖OperatorSchur.vectorValues Q hQ w‖ ≤
      mass⁻¹*(A*Real.sqrt (2/(1-s.val))*F*(n : ℝ)^(-(1/2 : ℝ))) +
        Real.sqrt (mass⁻¹*(n : ℝ)*E)*B := by
  have hs := energy_root_internal (norm_nonneg (OperatorSchur.vectorValues Q hQ w))
    (show 0 ≤ A*Real.sqrt (2/(1-s.val))*F*(n : ℝ)^(-(1/2 : ℝ)) by positivity)
    (show 0 ≤ (n : ℝ)*E*B^2 by positivity) hmass
    (henergy.trans ((le_abs_self _).trans hpair))
  apply hs.trans_eq
  rw [show mass⁻¹*((n : ℝ)*E*B^2) = (mass⁻¹*(n : ℝ)*E)*B^2 by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq hB]

/-- See Proposition 5.18 of the paper: the square root of the exceptional energy
term retains a stretched exponential and the required factor `n^(-1/2)`. -/
theorem exceptional_root_internal (p ε q C c δ : ℝ)
    (hq : 0 < q) (hC : 0 < C) (hc : 0 < c) (hδ : 0 < δ) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ+, 2 ≤ (n : ℕ) →
      Real.sqrt ((q*(n : ℝ)^(-p*ε))⁻¹*(n : ℝ)*
        (C*Real.exp (-c*(n : ℝ)^δ))) ≤
      D*(n : ℝ)^(-(1/2 : ℝ))*Real.exp (-(c/4)*(n : ℝ)^δ) := by
  obtain ⟨K, hK⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := p*ε+2) (c := c) (c' := c/2) hδ (by linarith)
  let L := max K 1
  have hL : 0 < L := zero_lt_one.trans_le (le_max_right _ _)
  let D := Real.sqrt (q⁻¹*C*L)
  have hD : 0 < D := Real.sqrt_pos.mpr (by dsimp [L]; positivity)
  refine ⟨D,hD,fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by positivity
  have hh : (n : ℝ)^(p*ε+2)*Real.exp (-c*(n : ℝ)^δ) ≤
      L*Real.exp (-(c/2)*(n : ℝ)^δ) :=
    (hK.2 n hn1).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  have hninv : (n : ℝ)^(-1 : ℝ)*(n : ℝ)^(p*ε+2) = (n : ℝ)^(p*ε+1) := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  have hcoeff : (q*(n : ℝ)^(-p*ε))⁻¹*(n : ℝ)*
      (C*Real.exp (-c*(n : ℝ)^δ)) =
      (q⁻¹*C)*((n : ℝ)^(-1 : ℝ)*
        ((n : ℝ)^(p*ε+2)*Real.exp (-c*(n : ℝ)^δ))) := by
    rw [show -p*ε = -(p*ε) by ring, mul_inv_rev, Real.rpow_neg hn0.le, inv_inv,
      ← mul_assoc ((n : ℝ)^(-1 : ℝ)) ((n : ℝ)^(p*ε+2)), hninv,
      Real.rpow_add hn0, Real.rpow_one]
    ring
  have hpower : ((n : ℝ)^(-(1/2 : ℝ)))^2 = (n : ℝ)^(-1 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    congr 1
    push_cast
    ring
  have hexp : (Real.exp (-(c/4)*(n : ℝ)^δ))^2 =
      Real.exp (-(c/2)*(n : ℝ)^δ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, mul_pow, show D^2 = q⁻¹*C*L from Real.sq_sqrt (by positivity), hpower, hexp,
    hcoeff]
  have hh' := mul_le_mul_of_nonneg_left hh
    (show 0 ≤ (q⁻¹*C)*(n : ℝ)^(-1 : ℝ) by positivity)
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hh'

set_option backward.isDefEq.respectTransparency true in
/-- See Proposition 5.18 of the paper: a continuous physical matrix pairing permits
comparison testing on the full scalar form domain. -/
theorem matrix_comparison_energy_internal {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    {ν : Measure X} (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (M : X → Matrix ι ι ℝ) (mass : ℝ)
    (Aphys S T : MatrixEnergy.Vector (ι := ι) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := ι) Q hQ →L[ℝ] ℝ)
    (hphysical : ∀ u z, Integrable (matrixFieldPair M
        (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ z i).val)) ν ∧
      Aphys u z = OperatorSchur.vectorEnergy Q hQ u z + ∫ x, matrixFieldPair M
        (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ z i).val) x ∂ν)
    (hAT : Aphys = S+T)
    (hlow : ∀ᵐ x ∂ν, ∀ t : ι → ℝ,
      mass*(∑ i,t i^2) ≤ ∑ i,∑ k,t i*M x i k*t k)
    (f : PiLp 2 (fun _ : ι => Lp ℝ 2 ν))
    (v ψ : MatrixEnergy.Vector (ι := ι) Q hQ)
    (hv : ∀ z, S v z = inner ℝ f (OperatorSchur.vectorValues Q hQ z))
    (hψ : ∀ z, Aphys ψ z = inner ℝ f (OperatorSchur.vectorValues Q hQ z)) :
    mass*‖OperatorSchur.vectorValues Q hQ (v-ψ)‖^2 ≤ T v (v-ψ) := by
  have henergy (u : MatrixEnergy.Vector (ι := ι) Q hQ) :
      mass*‖OperatorSchur.vectorValues Q hQ u‖^2 ≤ Aphys u u := by
    have hm := PhysicalIdentity.Internal.matrix_pair_lower Q hQ M mass hlow u (hphysical u u).1
    rw [(hphysical u u).2]
    have hn := OperatorSchur.vectorEnergy_nonneg Q hQ u
    exact hm.trans (le_add_of_nonneg_left hn)
  have he : Aphys (v-ψ) (v-ψ) = T v (v-ψ) := by
    have he' : Aphys (v-ψ) = Aphys v - Aphys ψ := map_sub Aphys v ψ
    rw [he', sub_apply, hψ, hAT]
    simp only [add_apply, hv]
    ring
  exact (henergy (v-ψ)).trans_eq he

set_option backward.isDefEq.respectTransparency true in
/-- See Proposition 5.18 of the paper: testing the physical comparison on its full
Sobolev domain gives the uniform-temperature mass inequality. -/
theorem proper_comparison_energy_internal
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) (hε : 0 ≤ ε) (q : ℝ)
    (hqm : q ≤ β.val*min 1 (s.val*(s.val+1))) :
    let ν := activeTiltedGapLaw (ofLong β s) ((n : ℕ)+m).succPNat n (by simp; omega) θ ε false
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      β.val * ∑ i, θ.val ((n : ℝ)^(-ε)*x i) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (x,z)).toReal)
    ∀ (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
      (Aphys S T : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ]
        MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ] ℝ),
    (∀ u z, Integrable (matrixFieldPair (hessianMatrix V)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ z i).val)) ν ∧
      Aphys u z = OperatorSchur.vectorEnergy Q hQ u z + ∫ x, matrixFieldPair (hessianMatrix V)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ z i).val) x ∂ν) →
    Aphys = S+T → ∀ (f : PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν)) (v ψ),
      (∀ z, S v z = inner ℝ f (OperatorSchur.vectorValues Q hQ z)) →
      (∀ z, Aphys ψ z = inner ℝ f (OperatorSchur.vectorValues Q hQ z)) →
      (q*(n : ℝ)^(-(s.val+2)*ε))*‖OperatorSchur.vectorValues Q hQ (v-ψ)‖^2 ≤ T v (v-ψ) := by
  intro ν V Q hQ Aphys S T hphysical hAT f v ψ hv hψ
  obtain ⟨_,hl⟩ := physical_matrix_lower_internal β s n m θ ε hε
  have hlow : ∀ᵐ x ∂ν, ∀ t : Fin (n : ℕ) → ℝ,
      (q*(n : ℝ)^(-(s.val+2)*ε))*(∑ i,t i^2) ≤
        ∑ i,∑ k,t i*hessianMatrix V x i k*t k := by
    filter_upwards [hl] with x hx t
    apply le_trans _ (hx.2 t)
    have hh := mul_le_mul_of_nonneg_right hqm
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n) (-(s.val+2)*ε))
    exact mul_le_mul_of_nonneg_right hh (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  exact matrix_comparison_energy_internal Q hQ (hessianMatrix V) _ Aphys S T
    hphysical hAT hlow f v ψ hv hψ

/-- See Proposition 5.18 of the paper: component decay from the full pairing of
Lemma 5.17 and the comparison energy,
keeping the spatial profile and exceptional source homogeneous. -/
theorem component_from_pairing_internal {X : Type*} [MeasurableSpace X] {ν : Measure X}
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (s : Riesz1.RieszExponent) (n : ℕ+) (χ : Lp ℝ 2 ν) (B : ℝ)
    (T : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ] ℝ)
    (v ψ : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ)
    (Cp Cm q kp km p ε c δ D : ℝ)
    (hCp : 0 < Cp) (hCm : 0 < Cm) (hq : 0 < q) (hkp : 0 < kp)
    (hkm : 0 < km) (hp : 0 < p) (hε : 0 < ε) (hB : 0 ≤ B) (hD : 0 < D)
    (i₀ j : Fin (n : ℕ)) :
    let w := v-ψ
    let mass := q*(n : ℝ)^(-p*ε)
    let κ := kp+km+p
    let H := q⁻¹*Cp*Real.sqrt (2/(1-s.val))
    let C := Cm+H+D
    ‖(MatrixEnergy.vectorEquiv Q hQ v j).val‖ ≤
      Cm*(n : ℝ)^(km*ε)*(1+|(j.val : ℝ)-(i₀.val : ℝ)|)^(-(2-s.val))*‖χ‖ →
    mass*‖OperatorSchur.vectorValues Q hQ w‖^2 ≤ T v w →
    |T v w| ≤ Cp*(n : ℝ)^(kp*ε)*Real.sqrt (2/(1-s.val))*‖χ‖*(n : ℝ)^(-(1/2 : ℝ))*
      ‖OperatorSchur.vectorValues Q hQ w‖+(n : ℝ)*Cp*Real.exp (-c*(n : ℝ)^δ)*B^2 →
    Real.sqrt (mass⁻¹*(n : ℝ)*(Cp*Real.exp (-c*(n : ℝ)^δ))) ≤
      D*(n : ℝ)^(-(1/2 : ℝ))*Real.exp (-(c/4)*(n : ℝ)^δ) →
    ‖(MatrixEnergy.vectorEquiv Q hQ ψ j).val‖ ≤ C*(n : ℝ)^(κ*ε)*
      ((1+|(j.val : ℝ)-(i₀.val : ℝ)|)^(-(2-s.val))+(n : ℝ)^(-(1/2 : ℝ)))*
        (‖χ‖+Real.exp (-(c/4)*(n : ℝ)^δ)*B) := by
  intro w mass κ H C hvalue henergy hpair herr
  have hmass : 0 < mass := by dsimp [mass]; positivity
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hH : 0 < H := by dsimp [H]; have := s.property.2; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hw := difference_norm_from_pairing_internal Q hQ s n T v w (Cp*(n : ℝ)^(kp*ε)) ‖χ‖
    (Cp*Real.exp (-c*(n : ℝ)^δ)) B mass
    (by positivity) (norm_nonneg _) (by positivity) hB hmass henergy
    (by simpa only [mul_assoc] using hpair)
  have hn0 : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hmain : mass⁻¹*(Cp*(n : ℝ)^(kp*ε)*Real.sqrt (2/(1-s.val))*‖χ‖*
      (n : ℝ)^(-(1/2 : ℝ))) =
      H*(n : ℝ)^((kp+p)*ε)*(n : ℝ)^(-(1/2 : ℝ))*‖χ‖ := by
    dsimp only [mass,H]
    rw [show -p*ε = -(p*ε) by ring, mul_inv_rev, Real.rpow_neg hn0.le, inv_inv,
      add_mul, Real.rpow_add hn0]
    ring
  rw [hmain] at hw
  have hw' := hw.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_right herr hB))
  have hψj : ‖(MatrixEnergy.vectorEquiv Q hQ ψ j).val‖ ≤
      ‖(MatrixEnergy.vectorEquiv Q hQ v j).val‖+‖OperatorSchur.vectorValues Q hQ w‖ := by
    have he : (OperatorSchur.vectorValues Q hQ ψ) j =
        (OperatorSchur.vectorValues Q hQ v) j-(OperatorSchur.vectorValues Q hQ w) j := by
      simp only [w,map_sub,PiLp.sub_apply,sub_sub_cancel]
    change ‖(OperatorSchur.vectorValues Q hQ ψ) j‖ ≤ _
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add le_rfl (PiLp.norm_apply_le _ j))
  apply (hψj.trans (add_le_add hvalue hw')).trans
  have hkmPow : (n : ℝ)^(km*ε) ≤ (n : ℝ)^(κ*ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [κ]; nlinarith only [hkp,hp,hε])
  have hkpPow : (n : ℝ)^((kp+p)*ε) ≤ (n : ℝ)^(κ*ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [κ]; nlinarith only [hkm,hε])
  have hone : 1 ≤ (n : ℝ)^(κ*ε) := Real.one_le_rpow hn1 (mul_pos hκ hε).le
  have hCmC : Cm ≤ C := by dsimp [C]; linarith only [hH,hD]
  have hHC : H ≤ C := by dsimp [C]; linarith only [hCm,hD]
  have hDC : D ≤ C := by dsimp [C]; linarith only [hCm,hH]
  let r := (1+|(j.val : ℝ)-(i₀.val : ℝ)|)^(-(2-s.val))
  let t := (n : ℝ)^(-(1/2 : ℝ))
  let b := Real.exp (-(c/4)*(n : ℝ)^δ)*B
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have h1 : Cm*(n : ℝ)^(km*ε)*r*‖χ‖ ≤ C*(n : ℝ)^(κ*ε)*r*‖χ‖ := by gcongr
  have h2 : H*(n : ℝ)^((kp+p)*ε)*t*‖χ‖ ≤ C*(n : ℝ)^(κ*ε)*t*‖χ‖ := by gcongr
  have h3 : D*t*b ≤ C*(n : ℝ)^(κ*ε)*t*b := by
    have hh : D ≤ C*(n : ℝ)^(κ*ε) := hDC.trans (by nlinarith only [hone,hC])
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh ht) hb
  have hcross := mul_nonneg (show 0 ≤ C*(n : ℝ)^(κ*ε)*r by positivity) hb
  have hgoal : Cm*(n : ℝ)^(km*ε)*r*‖χ‖ + (H*(n : ℝ)^((kp+p)*ε)*t*‖χ‖+D*t*b) ≤
      C*(n : ℝ)^(κ*ε)*(r+t)*(‖χ‖+b) := by
    nlinarith only [h1,h2,h3,hcross]
  simpa only [r,t,b,mul_assoc] using hgoal

set_option backward.isDefEq.respectTransparency true in
/-- The proof of Proposition 5.18, with the cutoff of Lemma 5.4: decay at admissible reference cutoffs, for every
bounded L² source, with one loss before the physical cutoff. The same good
event exponent `κ₀ = 1` is used in the mean and perturbation constructions. -/
theorem admissible_decay_internal (hzeta : External.PeriodicZeta)
    (hRig : External.LongRangeRigidityLocallyUniform) (s : Riesz1.RieszExponent) :
    ∃ ε₀ κ : ℝ, 0 < ε₀ ∧ 0 < κ ∧
    ∀ θ : PhysicalCutoff, ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    ∀ (n : ℕ+) (m : ℕ) (_hn : 2 ≤ (n : ℕ)) (_hnN : 2*(n : ℕ) ≤ (n : ℕ)+m+1),
    let N := ((n : ℕ)+m).succPNat
    let M := properReferencePeriod s n N
    let K := ⌊(n : ℝ)^ε⌋₊^(paperReferenceCutoffExponent s : ℕ)
    1 ≤ K → 4*K ≤ (M : ℕ) →
    let ν := activeTiltedGapLaw (ofLong β s) N n (by simp only [N,Nat.succPNat_coe]; omega) θ ε false
    let Ω := AffineSimplex.chartDomain n ((n+m : ℕ)+1)
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      β.val * ∑ i, θ.val ((n : ℝ)^(-ε)*x i) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (x,z)).toReal)
    ∃ Q : ScalarFormData ν, IsNeumannRealization Ω Q ∧
      ∃ _hQ : IsClosedScalarDirichletForm Q, IsConservativeScalarForm Q ∧
      (∀ (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν), ∃! u : Fin (n : ℕ) → Q.1,
        WeightedWeakSolution Q (hessianMatrix V) ⊤ (fun i => if i=i₀ then χ else 0) u) ∧
      ∀ (i₀ : Fin (n : ℕ)), (n : ℝ)/4 ≤ (i₀.val : ℝ)+1 →
        (i₀.val : ℝ)+1 ≤ 3*(n : ℝ)/4 →
      ∀ (χ : Lp ℝ 2 ν) (B : ℝ), 0 ≤ B → (∀ᵐ x ∂ν, |χ x| ≤ B) →
      ∀ u : Fin (n : ℕ) → Q.1,
        WeightedWeakSolution Q (hessianMatrix V) ⊤ (fun i => if i=i₀ then χ else 0) u →
      ∀ j : Fin (n : ℕ), ‖(u j).val‖ ≤ C*(n : ℝ)^(κ*ε)*
        ((1+|(j.val : ℝ)-(i₀.val : ℝ)|)^(-(2-s.val))+(n : ℝ)^(-(1/2 : ℝ)))*
          (‖χ‖+Real.exp (-c*(n : ℝ)^GoodBlocks.coefficientTailPower s.val ε)*B) := by
  obtain ⟨ε₀,kp,ks,gs,he₀,hkp,hks,hgs,hpert⟩ :=
    uniform_perturbation_operator_internal hRig hzeta s (paperReferenceCutoffExponent s) 1 le_rfl
  obtain ⟨km,hkm,hmean⟩ := PhysicalMean.periodized_mean_internal hzeta s ks gs hks hgs (paperReferenceCutoffExponent s)
  let p := s.val+2
  have hp : 0 < p := by dsimp [p]; linarith [s.property.1]
  let κ := kp+km+p
  have hκ : 0 < κ := by dsimp [κ]; positivity
  refine ⟨ε₀,κ,he₀,hκ,?_⟩
  intro θ ε hε hεa βlo βhi hlo hle
  obtain ⟨Cstar,hCstar,hpert⟩ := hpert θ
  obtain ⟨Cp,c,hCp,hc,hpert⟩ := hpert ε hε hεa βlo βhi hlo hle
  obtain ⟨Cm,hCm,hmean⟩ := hmean ε hε Cstar hCstar βlo βhi hlo hle
  let q := βlo*min 1 (s.val*(s.val+1))
  have hq : 0 < q := mul_pos hlo (lt_min zero_lt_one (by have := s.property.1; positivity))
  have hδ := GoodBlocks.coefficientTailPower_pos s.property.1 s.property.2 hε
  obtain ⟨D,hD,herr⟩ := exceptional_root_internal p ε q Cp c
    (GoodBlocks.coefficientTailPower s.val ε) hq hCp hc hδ
  let H := q⁻¹*Cp*Real.sqrt (2/(1-s.val))
  have hH : 0 < H := by dsimp [H]; have := s.property.2; positivity
  let C := Cm+H+D
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,c/4,hC,by positivity,?_⟩
  intro β hβ n m hn hnN N M K hK hKM ν Ω V
  obtain ⟨Q,hreal,hQ,hcons,A,heq,hA,S,Aphys,T,hdom,hphysical,hSeq,hAT,hsol,hrow⟩ :=
    hpert β hβ n m hn hnN hK hKM
  change ScalarFormData ν at Q
  change IsClosedScalarDirichletForm Q at hQ
  change IsNeumannRealization Ω Q at hreal
  change IsConservativeScalarForm Q at hcons
  have hnorm := physical_solvability_internal β s n m θ ε hε.le Q hQ
  refine ⟨Q,hreal,hQ,hcons,fun i χ => (hnorm i χ).1,?_⟩
  intro i₀ hil hih χ B hB hχ u hu j
  let f := WithLp.toLp 2 (fun i : Fin (n : ℕ) => if i=i₀ then χ else 0)
  obtain ⟨v,hv,_⟩ := (hsol f).1
  obtain ⟨ψ,hψ,_⟩ := (hsol f).2
  have hψweak := weak_of_form_internal Q hQ (hessianMatrix V) Aphys hphysical
    (fun i => if i=i₀ then χ else 0) ψ hψ
  have hue : u = MatrixEnergy.vectorEquiv Q hQ ψ := (hnorm i₀ χ).1.unique hu hψweak
  rw [hue]
  have hM : 2 ≤ (M : ℕ) := by
    change 2 ≤ (properReferencePeriod s n N : ℕ)
    have := (properReferencePeriod_bounds s n N hnN).1
    omega
  have hnM : (n : ℕ) ≤ (M : ℕ) := by
    change (n : ℕ) ≤ (properReferencePeriod s n N : ℕ)
    have := (properReferencePeriod_bounds s n N hnN).1
    omega
  have hhalf : 2*(n : ℕ) ≤ (M : ℕ) := (properReferencePeriod_bounds s n N hnN).1
  have hA' : PeriodizedMatrixBounds (ν := ν) s n M hM K Cstar ks gs ε A := hA
  obtain ⟨hprob,hne,hpot2,_⟩ := PhysicalMean.proper_scalar_internal β s n m θ ε
  obtain ⟨hfull,hdec⟩ := hmean β hβ n M hn hM hhalf
    (PhysicalMean.proper_period_upper_internal s n N) hK hKM n Ω ν
    (AffineSimplex.isOpen_chartDomain _ _) (AffineSimplex.convex_chartDomain _ _)
    (AffineSimplex.isBounded_chartDomain _ _) hne hprob hpot2 Q hreal hQ hcons A hA i₀ hil hih χ
  obtain ⟨Ψ,hΨ,_⟩ := hfull
  have hv' := equation_congr_internal S _ hSeq v
    (fun z => inner ℝ f (OperatorSchur.vectorValues Q hQ z)) hv
  have hΨ' : WeightedWeakSolution Q (fun x => β.val • A x) ⊤
      (fun i => if i=i₀.castLE hnM then χ else 0) Ψ := hΨ
  have hv'' : ∀ z, (SchurRestriction.schurForm Q hQ n M hnM s hM K Cstar ks gs ε
      β.val hCstar β.property A hA') v z = inner ℝ f (OperatorSchur.vectorValues Q hQ z) := by
    rw [← hSeq]
    exact hv
  have hcomp : ∀ i, Ψ (i.castLE hnM) = MatrixEnergy.vectorEquiv Q hQ v i :=
    PhysicalMean.schur_components_internal Q hQ s n M hnM hM K
      Cstar ks gs ε β.val hCstar β.property A hA' i₀ χ Ψ v hΨ' hv''
  have hprofile := (hdec Ψ hΨ).1
  have hvalue : ‖(MatrixEnergy.vectorEquiv Q hQ v j).val‖ ≤
      Cm*(n : ℝ)^(km*ε)*(1+|(j.val : ℝ)-(i₀.val : ℝ)|)^(-(2-s.val))*‖χ‖ := by
    have hh := hprofile (j.castLE hnM)
    rw [hcomp] at hh
    rw [weightRadius, LocalizedMatrix.active_distance M n hhalf] at hh
    have hd : (Nat.dist j.val i₀.val : ℝ) = |(j.val : ℝ)-(i₀.val : ℝ)| := by
      rcases le_total j.val i₀.val with h | h
      · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h,
          abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h))]; ring
      · rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h,
          abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]
    simpa only [hd] using hh
  let w := v-ψ
  let mass := q*(n : ℝ)^(-p*ε)
  have hmass : 0 < mass := by dsimp [mass]; positivity
  have henergy := proper_comparison_energy_internal β s n m θ ε hε.le q
    (by
      dsimp only [q]
      exact mul_le_mul_of_nonneg_right hβ.1
        (le_of_lt (lt_min zero_lt_one (by have := s.property.1; positivity))))
    Q hQ Aphys S T hphysical hAT f v ψ hv hψ
  exact component_from_pairing_internal Q hQ s n χ B T v ψ Cp Cm q kp km p ε c
    (GoodBlocks.coefficientTailPower s.val ε) D hCp hCm hq hkp hkm hp hε hB hD i₀ j
    hvalue henergy (hrow χ B hB hχ i₀ hil hih v ψ hv hψ) (herr n hn)

/-- See Proposition 5.18 of the paper: real estimates for every finite essential bound
give the literal extended-valued estimate, including infinite suprema. -/
theorem extended_bound_internal {X : Type*} [MeasurableSpace X] {ν : Measure X}
    (χ : Lp ℝ 2 ν) (x a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : ∀ B : ℝ, 0 ≤ B → (∀ᵐ z ∂ν, |χ z| ≤ B) → x ≤ a*(‖χ‖+b*B)) :
    ENNReal.ofReal x ≤ ENNReal.ofReal a *
      (ENNReal.ofReal ‖χ‖+ENNReal.ofReal b*eLpNorm χ ∞ ν) := by
  by_cases hχ : eLpNorm χ ∞ ν < ⊤
  · have hbound := ae_le_eLpNormEssSup (f := χ) (μ := ν)
    rw [← eLpNorm_exponent_top (Lp.aestronglyMeasurable χ)] at hbound
    have he : ∀ᵐ z ∂ν, |χ z| ≤ (eLpNorm χ ∞ ν).toReal := by
      filter_upwards [hbound] with z hz
      have ht := ENNReal.toReal_mono hχ.ne hz
      simpa only [enorm_eq_nnnorm, ENNReal.coe_toReal, coe_nnnorm, Real.norm_eq_abs] using ht
    have hh := ENNReal.ofReal_le_ofReal (h _ ENNReal.toReal_nonneg he)
    rw [ENNReal.ofReal_mul ha.le, ENNReal.ofReal_add (norm_nonneg _) (by positivity),
      ENNReal.ofReal_mul hb.le, ENNReal.ofReal_toReal hχ.ne] at hh
    exact hh
  · have he : eLpNorm χ ∞ ν = ⊤ := top_unique (le_of_not_gt hχ)
    rw [he, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hb).ne', add_top,
      ENNReal.mul_top (ENNReal.ofReal_pos.mpr ha).ne']
    exact le_top

/-- The powered cutoff of Lemma 5.4 and Proposition 5.18 of the paper
is admissible from size sixteen when its total exponent is at most one half. -/
theorem cutoff_admissible_internal (n : ℕ+) (ε : ℝ) (M₀ : ℕ+)
    (hn : 16 ≤ (n : ℕ)) (hε : 0 < ε) (hεh : ε*(M₀ : ℝ) ≤ 1/2) :
    1 ≤ ⌊(n : ℝ)^ε⌋₊^(M₀ : ℕ) ∧
      4*⌊(n : ℝ)^ε⌋₊^(M₀ : ℕ) ≤ (n : ℕ) := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn16 : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hfloor : 1 ≤ ⌊(n : ℝ)^ε⌋₊ :=
    (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hn1 hε.le)
  refine ⟨one_le_pow₀ hfloor,?_⟩
  have hf : (⌊(n : ℝ)^ε⌋₊ : ℝ)^(M₀ : ℕ) ≤ (n : ℝ)^(1/2 : ℝ) := by
    calc
      _ ≤ ((n : ℝ)^ε)^(M₀ : ℕ) :=
        pow_le_pow_left₀ (by positivity) (Nat.floor_le (by positivity)) _
      _ = (n : ℝ)^(ε*(M₀ : ℝ)) := (Real.rpow_mul_natCast hn0.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 hεh
  have hs : ((n : ℝ)^(1/2 : ℝ))^2 = (n : ℝ) := by
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hn0.le]
  have hroot : (4 : ℝ) ≤ (n : ℝ)^(1/2 : ℝ) := by
    nlinarith [Real.rpow_nonneg hn0.le (1/2 : ℝ)]
  have hh : (4 : ℝ)*(⌊(n : ℝ)^ε⌋₊ : ℝ)^(M₀ : ℕ) ≤ (n : ℝ) := by nlinarith
  exact_mod_cast hh

/-- See Proposition 5.18 of the paper: coarse coercivity supplies the displayed
profile at small sizes or forcing exponents above the fixed threshold. -/
theorem coarse_profile_internal (s : Riesz1.RieszExponent)
    (n : ℕ+) (ε ε₀ κ : ℝ) (hε₀ : 0 < ε₀) (hε : 0 < ε)
    (hκ : s.val+2+1/(2*ε₀) ≤ κ)
    (hcase : (n : ℕ) ≤ 16 ∨ ε₀ ≤ ε) :
    (n : ℝ)^((s.val+2)*ε) ≤ 4*(n : ℝ)^(κ*ε)*(n : ℝ)^(-(1/2 : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by positivity
  have hk : s.val+2 ≤ κ := by
    have hi : 0 < 1/(2*ε₀) := by positivity
    linarith only [hκ,hi]
  rcases hcase with hn | he
  · have hn16 : (n : ℝ) ≤ 16 := by exact_mod_cast hn
    have hroot : (n : ℝ)^(1/2 : ℝ) ≤ 4 := by
      have hsq : ((n : ℝ)^(1/2 : ℝ))^2 = (n : ℝ) := by
        rw [← Real.sqrt_eq_rpow,Real.sq_sqrt hn0.le]
      nlinarith [Real.rpow_nonneg hn0.le (1/2 : ℝ)]
    have hmul := mul_le_mul_of_nonneg_right hroot (Real.rpow_nonneg hn0.le (-(1/2 : ℝ)))
    rw [← Real.rpow_add hn0, add_neg_cancel, Real.rpow_zero] at hmul
    have hpow := Real.rpow_le_rpow_of_exponent_le hn1 (mul_le_mul_of_nonneg_right hk hε.le)
    have hh := mul_le_mul_of_nonneg_left hmul (Real.rpow_nonneg hn0.le (κ*ε))
    nlinarith only [hpow,hh]
  · have heq : (s.val+2)*ε ≤ κ*ε-(1/2 : ℝ) := by
      have hh := mul_le_mul_of_nonneg_right hκ hε.le
      have hh' := mul_le_mul_of_nonneg_left he (show 0 < 1/(2*ε₀) by positivity).le
      have hid : (1/(2*ε₀))*ε₀ = (1/2 : ℝ) := by field_simp
      rw [hid] at hh'
      nlinarith only [hh,hh']
    have hh := Real.rpow_le_rpow_of_exponent_le hn1 heq
    rw [sub_eq_add_neg,Real.rpow_add hn0] at hh
    have hnonneg := mul_nonneg (Real.rpow_nonneg hn0.le (κ*ε))
      (Real.rpow_nonneg hn0.le (-(1/2 : ℝ)))
    exact hh.trans (by nlinarith only [hnonneg])

/-- See Proposition 5.18 of the paper: complete the physical certificates and
extended-valued source convention from a bounded-source estimate on its
existing Neumann realization. This is only an internal assembly lemma. -/
theorem complete_chart_internal (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε κ C c δ : ℝ)
    (hε : 0 ≤ ε) (hC : 0 < C) :
    let N := ((n : ℕ)+m).succPNat
    let hn : (n : ℕ) ≤ (N : ℕ) := by simp only [N,Nat.succPNat_coe]; omega
    let ν := activeTiltedGapLaw (ofLong β s) N n hn θ ε false
    let Ω := AffineSimplex.chartDomain n ((n+m : ℕ)+1)
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      β.val * ∑ i, θ.val ((n : ℝ)^(-ε)*x i) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (x,z)).toReal)
    ∀ (Q : ScalarFormData ν), IsNeumannRealization Ω Q →
      IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
    (∀ (i₀ : Fin (n : ℕ)), (n : ℝ)/4 ≤ (i₀.val : ℝ)+1 →
      (i₀.val : ℝ)+1 ≤ 3*(n : ℝ)/4 →
      ∀ (χ : Lp ℝ 2 ν) (B : ℝ), 0 ≤ B → (∀ᵐ x ∂ν, |χ x| ≤ B) →
      ∀ u : Fin (n : ℕ) → Q.1,
        WeightedWeakSolution Q (hessianMatrix V) ⊤ (fun i => if i=i₀ then χ else 0) u →
      ∀ j : Fin (n : ℕ), ‖(u j).val‖ ≤ C*(n : ℝ)^(κ*ε)*
        ((1+|(j.val : ℝ)-(i₀.val : ℝ)|)^(-(2-s.val))+(n : ℝ)^(-(1/2 : ℝ)))*
          (‖χ‖+Real.exp (-c*(n : ℝ)^δ)*B)) →
    0 < tiltNormalizer (ofLong β s) N n hn θ ε false ∧
      tiltNormalizer (ofLong β s) N n hn θ ε false < ⊤ ∧ IsProbabilityMeasure ν ∧
      ∃ (V : EuclideanSpace ℝ (Fin (n : ℕ)) → ℝ) (Q : ScalarFormData ν),
        IsEuclideanGibbsPotential volume ν (properMarginalDomain n N) V ∧
        IsNeumannRealization (properMarginalDomain n N) Q ∧
        IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
        ∀ i₀ : Fin (n : ℕ), (n : ℕ) ≤ 4*(i₀.val+1) →
          4*(i₀.val+1) ≤ 3*(n : ℕ) →
          ∀ χ : Lp ℝ 2 ν, (χ ∈ Q.1 ∨ eLpNorm χ ∞ ν < ⊤) →
          (∃! u : Fin (n : ℕ) → Q.1,
            WeightedWeakSolution Q (hessianMatrix V) ⊤ (fun i => if i=i₀ then χ else 0) u) ∧
          (∀ u : Fin (n : ℕ) → Q.1,
            WeightedWeakSolution Q (hessianMatrix V) ⊤ (fun i => if i=i₀ then χ else 0) u →
            ∀ j : Fin (n : ℕ), ENNReal.ofReal ‖(u j).val‖ ≤
              ENNReal.ofReal (C*(n : ℝ)^(κ*ε)*
                ((1+|(j.val : ℝ)-(i₀.val : ℝ)|)^(-(2-s.val))+(n : ℝ)^(-(1/2 : ℝ)))) *
                (ENNReal.ofReal ‖χ‖+ENNReal.ofReal (Real.exp (-c*(n : ℝ)^δ))*eLpNorm χ ∞ ν)) := by
  intro N hn ν Ω V Q hreal hQ hcons hbound
  have hpot := PhysicalFormDomain.proper_gibbs_potential β s n m θ ε
  change IsEuclideanGibbsPotential volume ν Ω V at hpot
  have hΩ : properMarginalDomain n N = Ω := by
    ext x
    change ((∀ i, 0 < x i) ∧ (∑ i, x i) < (N : ℝ)) ↔
      ((∀ i, 0 < x i) ∧ (∑ i, x i) < ((n+m : ℕ) : ℝ)+1)
    simp only [N,Nat.succPNat_coe,Nat.cast_succ,Nat.cast_add]
  have hZ := DefinitionSanity.tilt_normalizer_valid (ofLong β s) N n hn θ ε false
  refine ⟨hZ.1,hZ.2.trans_lt (by norm_num),IntrinsicScalarCore.probability hpot,V,Q,?_,?_,hQ,hcons,?_⟩
  · simpa only [hΩ] using hpot
  · simpa only [hΩ] using hreal
  intro i₀ hil hih χ _hχ
  have hil' : (n : ℝ)/4 ≤ (i₀.val : ℝ)+1 := by
    have hh : (n : ℝ) ≤ 4*((i₀.val : ℝ)+1) := by exact_mod_cast hil
    linarith
  have hih' : (i₀.val : ℝ)+1 ≤ 3*(n : ℝ)/4 := by
    have hh : 4*((i₀.val : ℝ)+1) ≤ 3*(n : ℝ) := by exact_mod_cast hih
    linarith
  refine ⟨(physical_solvability_internal β s n m θ ε hε Q hQ i₀ χ).1,?_⟩
  intro u hu j
  exact extended_bound_internal χ _ _ _ (by positivity) (Real.exp_pos _)
    (fun B hB hχ => hbound i₀ hil' hih' χ B hB hχ u hu j)

/-- See Proposition 5.18 of the paper: the coarse physical solution estimate covers
both the bounded-size and large-forcing regimes, for every L² source. -/
theorem coarse_bounded_internal (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε ε₀ κ C c δ βlo : ℝ)
    (hlo : 0 < βlo) (hβ : βlo ≤ β.val) (he₀ : 0 < ε₀) (hε : 0 < ε)
    (hκ : s.val+2+1/(2*ε₀) ≤ κ)
    (hC : 4*(βlo*min 1 (s.val*(s.val+1)))⁻¹ ≤ C)
    (hcase : (n : ℕ) ≤ 16 ∨ ε₀ ≤ ε) :
    let ν := activeTiltedGapLaw (ofLong β s) ((n : ℕ)+m).succPNat n (by simp; omega) θ ε false
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      β.val * ∑ i, θ.val ((n : ℝ)^(-ε)*x i) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (x,z)).toReal)
    ∀ (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q →
    ∀ (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν) (B : ℝ), 0 ≤ B →
    ∀ u : Fin (n : ℕ) → Q.1,
      WeightedWeakSolution Q (hessianMatrix V) ⊤ (fun i => if i=i₀ then χ else 0) u →
    ∀ j : Fin (n : ℕ), ‖(u j).val‖ ≤ C*(n : ℝ)^(κ*ε)*
      ((1+|(j.val : ℝ)-(i₀.val : ℝ)|)^(-(2-s.val))+(n : ℝ)^(-(1/2 : ℝ)))*
        (‖χ‖+Real.exp (-c*(n : ℝ)^δ)*B) := by
  intro ν V Q hQ i₀ χ B hB u hu j
  have hp := coarse_profile_internal s n ε ε₀ κ he₀ hε hκ hcase
  have hm : 0 < min 1 (s.val*(s.val+1)) := lt_min zero_lt_one (by have := s.property.1; positivity)
  have hi : (β.val*min 1 (s.val*(s.val+1)))⁻¹ ≤
      (βlo*min 1 (s.val*(s.val+1)))⁻¹ :=
    inv_anti₀ (mul_pos hlo hm) (mul_le_mul_of_nonneg_right hβ hm.le)
  have hnorm := (physical_solvability_internal β s n m θ ε hε.le Q hQ i₀ χ).2 u hu j
  have hc0 : 0 < C := (by positivity : 0 < 4*(βlo*min 1 (s.val*(s.val+1)))⁻¹).trans_le hC
  have hmain : (β.val*min 1 (s.val*(s.val+1)))⁻¹*(n : ℝ)^((s.val+2)*ε) ≤
      C*(n : ℝ)^(κ*ε)*(n : ℝ)^(-(1/2 : ℝ)) := by
    have hh := mul_le_mul hi hp (Real.rpow_nonneg (by positivity) _) (by positivity)
    have hh' := mul_le_mul_of_nonneg_right hC
      (show 0 ≤ (n : ℝ)^(κ*ε)*(n : ℝ)^(-(1/2 : ℝ)) by positivity)
    exact hh.trans (by simpa only [mul_assoc,mul_left_comm,mul_comm] using hh')
  apply hnorm.trans
  have hh := mul_le_mul_of_nonneg_right hmain (norm_nonneg χ)
  apply hh.trans
  have hr : 0 ≤ (1+|(j.val : ℝ)-(i₀.val : ℝ)|)^(-(2-s.val)) := by positivity
  have he : 0 ≤ Real.exp (-c*(n : ℝ)^δ)*B := by positivity
  nlinarith only [hr,he,mul_nonneg
    (show 0 ≤ C*(n : ℝ)^(κ*ε) by positivity) (mul_nonneg hr (norm_nonneg χ)),
    mul_nonneg (show 0 ≤ C*(n : ℝ)^(κ*ε)*
      ((1+|(j.val : ℝ)-(i₀.val : ℝ)|)^(-(2-s.val))+(n : ℝ)^(-(1/2 : ℝ))) by positivity) he]

/-- Proposition 5.18, combining the small-exponent and coarse branches: proper physical marginal decay, with exactly
the quantifier order and full finite-energy solution domain. -/
theorem proper_physical_marginal_decay (hzeta : External.PeriodicZeta)
    (hRig : External.LongRangeRigidityLocallyUniform) :
  ∀ s : Riesz1.RieszExponent, ∃ κ : ℝ, 0 < κ ∧
  ∀ θ : PhysicalCutoff, ∀ ε : ℝ, 0 < ε →
  ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
    ∃ C c δ : ℝ, 0 < C ∧ 0 < c ∧ 0 < δ ∧
    ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    ∀ (N n : ℕ+) (_ : 4 ≤ (N : ℕ)) (_ : 2 ≤ (n : ℕ)),
      2 * (n : ℕ) ≤ (N : ℕ) → ∀ hn : (n : ℕ) ≤ (N : ℕ),
      let p := ofLong β s
      let ν := activeTiltedGapLaw p N n hn θ ε false
      0 < tiltNormalizer p N n hn θ ε false ∧ tiltNormalizer p N n hn θ ε false < ⊤ ∧
      IsProbabilityMeasure ν ∧
      ∃ (V : EuclideanSpace ℝ (Fin (n : ℕ)) → ℝ) (Q : ScalarFormData ν),
        IsEuclideanGibbsPotential volume ν (properMarginalDomain n N) V ∧
        IsNeumannRealization (properMarginalDomain n N) Q ∧
        IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
        ∀ i₀ : Fin (n : ℕ), (n : ℕ) ≤ 4 * (i₀.val + 1) →
          4 * (i₀.val + 1) ≤ 3 * (n : ℕ) →
          ∀ χ : Lp ℝ 2 ν, (χ ∈ Q.1 ∨ eLpNorm χ ∞ ν < ⊤) →
          (∃! u : Fin (n : ℕ) → Q.1,
            WeightedWeakSolution Q (hessianMatrix V) ⊤ (fun i => if i = i₀ then χ else 0) u) ∧
          (∀ u : Fin (n : ℕ) → Q.1,
            WeightedWeakSolution Q (hessianMatrix V) ⊤ (fun i => if i = i₀ then χ else 0) u →
            ∀ j : Fin (n : ℕ), ENNReal.ofReal ‖(u j).val‖ ≤
              ENNReal.ofReal (C * (n : ℝ) ^ (κ * ε) *
                ((1 + |(j.val : ℝ) - (i₀.val : ℝ)|) ^ (-(2 - s.val)) +
                  (n : ℝ) ^ (-(1 / 2 : ℝ)))) *
                (ENNReal.ofReal ‖χ‖ + ENNReal.ofReal (Real.exp (-c * (n : ℝ) ^ δ)) *
                  eLpNorm χ ∞ ν)) := by
  intro s
  obtain ⟨ε₀,k,hε₀,hk,hdec⟩ := admissible_decay_internal hzeta hRig s
  let εstar := min ε₀ (paperCutoffThreshold s)
  have hstar : 0 < εstar := lt_min hε₀ (paperCutoffThreshold_pos s)
  let κ := k+s.val+2+1/(2*εstar)
  have hκ : 0 < κ := by dsimp [κ]; have := s.property.1; positivity
  have hκk : k ≤ κ := by
    have hi : 0 < 1/(2*εstar) := by positivity
    dsimp only [κ]
    linarith only [hi,s.property.1]
  have hκcoarse : s.val+2+1/(2*εstar) ≤ κ := by dsimp only [κ]; linarith only [hk]
  refine ⟨κ,hκ,?_⟩
  intro θ ε hε βlo βhi hlo hle
  let η := min ε εstar
  have hη : 0 < η := lt_min hε hstar
  have hηsmall : η ≤ ε₀ := (min_le_right _ _).trans (min_le_left _ _)
  obtain ⟨Cs,c,hCs,hc,hdec⟩ := hdec θ η hη hηsmall βlo βhi hlo hle
  let δ := GoodBlocks.coefficientTailPower s.val η
  have hδ : 0 < δ := GoodBlocks.coefficientTailPower_pos s.property.1 s.property.2 hη
  let q := βlo*min 1 (s.val*(s.val+1))
  have hq : 0 < q := mul_pos hlo (lt_min zero_lt_one (by have := s.property.1; positivity))
  let C := Cs+4*q⁻¹
  have hC : 0 < C := by dsimp only [C]; positivity
  have hCsC : Cs ≤ C := le_add_of_nonneg_right (by positivity)
  have hcoarseC : 4*(βlo*min 1 (s.val*(s.val+1)))⁻¹ ≤ C :=
    le_add_of_nonneg_left hCs.le
  refine ⟨C,c,δ,hC,hc,hδ,?_⟩
  intro β hβ N n hN hn2 hhalf hn p ν
  obtain ⟨m,he⟩ : ∃ m : ℕ, ((n : ℕ)+m).succPNat = N := by
    refine ⟨(N : ℕ)-(n : ℕ)-1,?_⟩
    apply PNat.coe_injective
    change (n : ℕ)+((N : ℕ)-(n : ℕ)-1)+1 = (N : ℕ)
    omega
  subst N
  have hnN : 2*(n : ℕ) ≤ (n : ℕ)+m+1 := by simpa only [Nat.succPNat_coe] using hhalf
  by_cases hgood : ε ≤ εstar ∧ 16 ≤ (n : ℕ)
  · have hηeq : η = ε := min_eq_left hgood.1
    have hεhalf : ε*(paperReferenceCutoffExponent s : ℝ) ≤ 1/2 :=
      paperCutoffThreshold_mul_degree_le_half s hε.le
        (hgood.1.trans (min_le_right ε₀ (paperCutoffThreshold s)))
    obtain ⟨hK,hKn⟩ := cutoff_admissible_internal n ε (paperReferenceCutoffExponent s)
      hgood.2 hε hεhalf
    have hKM : 4*⌊(n : ℝ)^ε⌋₊^(paperReferenceCutoffExponent s : ℕ) ≤ (properReferencePeriod s n ((n : ℕ)+m).succPNat : ℕ) :=
      hKn.trans (by have := (properReferencePeriod_bounds s n ((n : ℕ)+m).succPNat hnN).1; omega)
    rw [hηeq] at hdec
    obtain ⟨Q,hreal,hQ,hcons,_,hbound⟩ := hdec β hβ n m hn2 hnN hK hKM
    apply complete_chart_internal β s n m θ ε κ C c δ hε.le hC Q hreal hQ hcons
    intro i₀ hil hih χ B hB hχ u hu j
    have hh := hbound i₀ hil hih χ B hB hχ u hu j
    have hpow : (n : ℝ)^(k*ε) ≤ (n : ℝ)^(κ*ε) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast n.pos)
        (mul_le_mul_of_nonneg_right hκk hε.le)
    have hcoeff := mul_le_mul hCsC hpow (Real.rpow_nonneg (by positivity) _) hC.le
    have hb := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoeff
        (show 0 ≤ (1+|(j.val : ℝ)-(i₀.val : ℝ)|)^(-(2-s.val))+(n : ℝ)^(-(1/2 : ℝ)) by positivity))
      (show 0 ≤ ‖χ‖+Real.exp (-c*(n : ℝ)^GoodBlocks.coefficientTailPower s.val ε)*B by positivity)
    simpa only [δ,hηeq] using hh.trans hb
  · have hcase : (n : ℕ) ≤ 16 ∨ εstar ≤ ε := by
      by_cases heps : ε ≤ εstar
      · left
        have : ¬16 ≤ (n : ℕ) := fun hh => hgood ⟨heps,hh⟩
        omega
      · exact Or.inr (le_of_not_ge heps)
    obtain ⟨_,_,_,Q,hreal,hQ,hcons,_⟩ := PhysicalMean.proper_scalar_internal β s n m θ ε
    apply complete_chart_internal β s n m θ ε κ C c δ hε.le hC Q hreal hQ hcons
    intro i₀ _hil _hih χ B hB _hχ u hu j
    exact coarse_bounded_internal β s n m θ ε εstar κ C c δ βlo hlo hβ.1
      hstar hε hκcoarse hcoarseC hcase Q hQ i₀ χ B hB u hu j

end Riesz2.ProperMarginalDecay
