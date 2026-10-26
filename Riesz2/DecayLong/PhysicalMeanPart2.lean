/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.PhysicalMean
import all Riesz2.DecayLong.PhysicalCorePart6
public import Riesz2.DecayLong.PhysicalIdentityPart5

/-!
# Physical mean: carrier and temperature bridges

Continuation of the proof of Proposition 5.18. The physical matrix is used
on its actual retained chart. Ambient representatives are identified on
that entire chart and hence uniquely almost everywhere for supported laws.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical MatrixOrder

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.PhysicalMean

open PhysicalCore

/-- Temperature-uniform proper matrix bounds used in Proposition 5.18 and
Lemma 5.4. The coefficient constants are chosen before temperature. -/
theorem proper_matrix_bounds_uniform_internal (s : Riesz1.RieszExponent) (θ : PhysicalCutoff)
    (M₀ : ℕ) (κ₀ : ℝ) (hκ₀ : 0 ≤ κ₀) :
    ∃ ε₀ κ γ : ℝ, 0 < ε₀ ∧ 0 < κ ∧ 0 < γ ∧
      ∃ C : ℝ, 1 ≤ C ∧ ∀ β : InverseTemperature,
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
  obtain ⟨U,hU,hupper⟩ := properIntervalWeight_upper s θ
  obtain ⟨E,hE,hentry⟩ := properActive_entry_error s θ
  let kE := κ₀+s.val+3+(M₀ : ℝ)
  let kC := s.val+2+(M₀ : ℝ)*(1+s.val)
  let κ := kE+kC
  let γ := (M₀ : ℝ)+1
  have hkE : 0 < kE := by dsimp only [kE]; have := Nat.cast_nonneg M₀ (α := ℝ); linarith [s.property.1]
  have hkC : 0 < kC := by dsimp only [kC]; have := s.property.1; positivity
  have hi₁ : 0 < c₁⁻¹ := inv_pos.mpr hc₁
  have hi₂ : 0 < c₂⁻¹ := inv_pos.mpr hc₂
  let C := 1+U+E+c₁⁻¹+c₂⁻¹
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hCU : U ≤ C := by dsimp only [C]; linarith
  have hCE : E ≤ C := by dsimp only [C]; linarith
  have hcC₁ : C⁻¹ ≤ c₁ := (inv_le_comm₀ hC0 hc₁).mpr (by dsimp only [C]; linarith)
  have hcC₂ : C⁻¹ ≤ c₂ := (inv_le_comm₀ hC0 hc₂).mpr (by dsimp only [C]; linarith)
  refine ⟨(1-s.val/2)/2,κ,γ,by linarith [s.property.2],by dsimp only [κ]; positivity,
    by dsimp only [γ]; positivity,?_⟩
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



/-- Internal carrier bridge for the proof of Proposition 5.18. A matrix
on a measure-preserving embedded carrier has an ambient measurable
representative with precisely the same matrix bounds. Agreement
is on the whole carrier. No off-carrier value is prescribed or used. -/
theorem periodized_matrix_extension_internal
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (f : X → Y)
    (hf : MeasurableEmbedding f) (hco : MeasurePreserving f μ ν)
    (s : Riesz1.RieszExponent) (n m : ℕ+) (hm : 2 ≤ (m : ℕ))
    (K : ℕ) (C κ γ ε : ℝ)
    (M : X → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hM : PeriodizedMatrixBounds (ν := μ) s n m hm K C κ γ ε M) :
    ∃ A : Y → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
      (∀ x, A (f x) = M x) ∧
      PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε A := by
  have hMm : Measurable M := Measurable.of_eval fun i =>
    Measurable.of_eval fun j => hM.1 i j
  obtain ⟨A,hAm,hA⟩ := hf.exists_measurable_extend hMm (fun _ => inferInstance)
  have heq (x : X) : A (f x) = M x := congrFun hA x
  obtain ⟨a,ham,ha⟩ := hM.2.2
  have ham' : Measurable (fun x i r => a i r x) :=
    Measurable.of_eval fun i => Measurable.of_eval fun r => ham i r
  obtain ⟨b,hbm,hb⟩ := hf.exists_measurable_extend ham' (fun _ => inferInstance)
  have hbeq (x : X) (i : Fin (m : ℕ)) (r : Fin ((m : ℕ)/2)) :
      b (f x) i r = a i r x := congrFun (congrFun (congrFun hb x) i) r
  refine ⟨A,heq,fun i j => (measurable_pi_apply j).comp
    ((measurable_pi_apply i).comp hAm),?_,?_⟩
  · rw [← hco.map_eq, hf.ae_map_iff]
    exact hM.2.1.mono fun x hx => by simpa only [heq] using hx
  · refine ⟨fun i r x => b x i r,
      fun i r => (measurable_pi_apply r).comp ((measurable_pi_apply i).comp hbm),?_⟩
    rw [← hco.map_eq, hf.ae_map_iff]
    exact ha.mono fun x hx => by simpa only [heq,hbeq] using hx

/-- The ambient representatives above are uniquely determined almost
everywhere, despite the deliberately unspecified exterior values.
This supports the carrier interpretation of the proof of Proposition 5.18. -/
theorem matrix_extension_unique_internal
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (f : X → Y)
    (hf : MeasurableEmbedding f) (hco : MeasurePreserving f μ ν)
    {ι : Type*} (A B : Y → Matrix ι ι ℝ)
    (heq : ∀ x, A (f x) = B (f x)) : A =ᵐ[ν] B := by
  change ∀ᵐ y ∂ν, A y = B y
  rw [← hco.map_eq, hf.ae_map_iff]
  exact ae_of_all _ heq

/-- Internal form identification for the proof of Proposition 5.18.
Any existing physical lifted form with the actual carrier integral is
exactly the bounded periodized form of an agreeing ambient
representative. -/
theorem carrier_periodized_form_internal
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (f : X → Y)
    (hf : MeasurableEmbedding f) (hco : MeasurePreserving f μ ν)
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (s : Riesz1.RieszExponent) (n m : ℕ+) (hm : 2 ≤ (m : ℕ))
    (K : ℕ) (C κ γ ε β : ℝ) (hC : 1 ≤ C) (hβ : 0 < β)
    (M : X → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (A : Y → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (heq : ∀ x, A (f x) = M x)
    (hA : PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε A)
    (F : MatrixEnergy.Vector (ι := Fin (m : ℕ)) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := Fin (m : ℕ)) Q hQ →L[ℝ] ℝ)
    (hF : ∀ u v, F u v = OperatorSchur.vectorEnergy Q hQ u v + β *
      ∫ x, ∑ i, ∑ j,
        (MatrixEnergy.vectorEquiv Q hQ u i).val (f x) * M x i j *
        (MatrixEnergy.vectorEquiv Q hQ v j).val (f x) ∂μ) :
    F = SchurRestriction.periodizedForm Q hQ n m s hm K C κ γ ε β hC hβ A hA := by
  ext u v
  rw [hF,SchurRestriction.periodizedForm,BoundedMatrixForms.form_apply,
    SchurRestriction.integral_pair_smul,OperatorSchur.vectorEnergy_apply]
  congr 1
  congr 1
  have hi := hco.integral_comp hf (fun y => matrixFieldPair A
    (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val)
    (fun i => (MatrixEnergy.vectorEquiv Q hQ v i).val) y)
  simpa only [matrixFieldPair,Function.comp_def,heq] using hi


/-- Internal identification with the existing physical Schur construction
in Subsection 5.1, supporting the proof of Proposition 5.18. The hypotheses
are its defining carrier integrals and exterior variational equation.
Uniqueness of that exterior equation identifies the response and the
Schur form, even when their constructions use different coercivity bounds. -/
theorem carrier_schur_form_internal
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (f : X → Y)
    (hf : MeasurableEmbedding f) (hco : MeasurePreserving f μ ν)
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (s : Riesz1.RieszExponent) (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
    (hm : 2 ≤ (m : ℕ)) (K : ℕ) (C κ γ ε β : ℝ) (hC : 1 ≤ C) (hβ : 0 < β)
    (M : X → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (A : Y → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (heq : ∀ x, A (f x) = M x)
    (hA : PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε A)
    (F : MatrixEnergy.Vector (ι := Fin (m : ℕ)) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := Fin (m : ℕ)) Q hQ →L[ℝ] ℝ)
    (S G : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ] ℝ)
    (R : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := Fin ((m : ℕ)-(n : ℕ))) Q hQ)
    (hF : ∀ u v, F u v = OperatorSchur.vectorEnergy Q hQ u v + β *
      ∫ x, ∑ i, ∑ j,
        (MatrixEnergy.vectorEquiv Q hQ u i).val (f x) * M x i j *
        (MatrixEnergy.vectorEquiv Q hQ v j).val (f x) ∂μ)
    (hS : ∀ u v, S u v =
      F (SchurRestriction.assemble Q hQ n m hnm (u,0))
        (SchurRestriction.assemble Q hQ n m hnm (v,0)) - G u v)
    (hR : ∀ u w,
      let P := fun z z' => fun x : X => matrixFieldPair
        (fun _ : Y => (2 : ℝ) • referenceIntervalMatrix s m hm K)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ
          (SchurRestriction.assemble Q hQ n m hnm z) i).val)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ
          (SchurRestriction.assemble Q hQ n m hnm z') i).val) (f x)
      β⁻¹ * OperatorSchur.vectorEnergy Q hQ (R u) w +
        (∫ x, P (0,R u) (0,w) x ∂μ) = ∫ x, P (u,0) (0,w) x ∂μ)
    (hG : ∀ u v,
      G u v = β * ∫ x, matrixFieldPair
        (fun _ : Y => (2 : ℝ) • referenceIntervalMatrix s m hm K)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ
          (SchurRestriction.assemble Q hQ n m hnm (v,0)) i).val)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ
          (SchurRestriction.assemble Q hQ n m hnm (0,R u)) i).val) (f x) ∂μ) :
    F = SchurRestriction.periodizedForm Q hQ n m s hm K C κ γ ε β hC hβ A hA ∧
    R = SchurRestriction.exteriorResponse Q hQ n m hnm s hm K C κ γ ε β hC hβ A hA ∧
    S = SchurRestriction.schurForm Q hQ n m hnm s hm K C κ γ ε β hC hβ A hA := by
  have hF' := carrier_periodized_form_internal f hf hco Q hQ s n m hm K C κ γ ε β
    hC hβ M A heq hA F hF
  let P := SchurRestriction.splitForm Q hQ n m hnm s hm K C κ γ ε β hC hβ A hA
  let E := SchurRestriction.exteriorForm Q hQ n ((m : ℕ)-(n : ℕ)) P
  let B := SchurRestriction.cross Q hQ n ((m : ℕ)-(n : ℕ)) P
  let c := min 1 (β * (C⁻¹ * (n : ℝ)^(-κ*ε)))
  have hc := SchurRestriction.coercivity_pos n C κ ε β hC hβ
  have hE := SchurRestriction.exterior_coercive Q hQ n ((m : ℕ)-(n : ℕ)) P c
    (SchurRestriction.splitForm_coercive Q hQ n m hnm s hm K C κ γ ε β hC hβ A hA)
  have hint (z z') :
      (∫ x, matrixFieldPair (fun _ : Y => (2 : ℝ) • referenceIntervalMatrix s m hm K)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ
          (SchurRestriction.assemble Q hQ n m hnm z) i).val)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ
          (SchurRestriction.assemble Q hQ n m hnm z') i).val) (f x) ∂μ) =
      ∫ y, matrixFieldPair (fun _ : Y => (2 : ℝ) • referenceIntervalMatrix s m hm K)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ
          (SchurRestriction.assemble Q hQ n m hnm z) i).val)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ
          (SchurRestriction.assemble Q hQ n m hnm z') i).val) y ∂ν :=
    hco.integral_comp hf _
  have hRu (u) : R u = SchurRestriction.exteriorResponse Q hQ n m hnm s hm K C κ γ ε β hC hβ A hA u := by
    change R u = CoerciveSolution.inverse E c hc hE (B u)
    apply CoerciveSolution.inverse_unique
    intro w
    dsimp only [E,B,P]
    rw [SchurRestriction.exteriorForm_reference,SchurRestriction.cross_reference]
    simp only [SchurRestriction.integral_pair_smul]
    have he := hR u w
    dsimp only at he
    rw [hint,hint,OperatorSchur.vectorEnergy_apply] at he
    have he' := congrArg (fun t : ℝ => β*t) he
    simpa only [SchurRestriction.integral_pair_smul,mul_add,← mul_assoc,
      mul_inv_cancel₀ hβ.ne',one_mul] using he'
  have hR' : R = SchurRestriction.exteriorResponse Q hQ n m hnm s hm K C κ γ ε β hC hβ A hA := by
    apply ContinuousLinearMap.ext
    intro u
    exact hRu u
  refine ⟨hF',hR',?_⟩
  ext u v
  rw [hS,hF',SchurRestriction.schurForm,OperatorSchur.reduced_apply]
  congr 1
  change G u v = B v (SchurRestriction.exteriorResponse Q hQ n m hnm s hm K C κ γ ε β hC hβ A hA u)
  rw [← hRu]
  dsimp only [B,P]
  rw [SchurRestriction.cross_reference,SchurRestriction.integral_pair_smul,hG,hint]


/-- The prescribed proper period satisfies the size range used by optimal
localization, including the ceiling and the smallest active sizes.
This supports Subsection 5.1 and the proof of Proposition 5.18. -/
theorem proper_period_upper_internal (s : Riesz1.RieszExponent) (n N : ℕ+) :
    (properReferencePeriod s n N : ℝ) ≤ 2*(n : ℝ)^(1/2+1/s.val) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hp : 1 ≤ 1/2+1/s.val := by
    have := (one_le_div s.property.1).mpr s.property.2.le
    linarith
  have hpow := Real.self_le_rpow_of_one_le hn1 hp
  have hceil := Nat.ceil_lt_add_one
    (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n) (1/2+1/s.val))
  have hmax : ((max (2*(n : ℕ)) ⌈(n : ℝ)^(1/2+1/s.val)⌉₊ : ℕ) : ℝ) ≤
      2*(n : ℝ)^(1/2+1/s.val) := by
    rw [Nat.cast_max,Nat.cast_mul,Nat.cast_ofNat]
    exact max_le (by linarith) (by linarith)
  exact (Nat.cast_le.mpr (min_le_right (N : ℕ)
    (max (2*(n : ℕ)) ⌈(n : ℝ)^(1/2+1/s.val)⌉₊))).trans hmax

/-- The actual physical scalar realization and supported carrier needed
by the proof of Proposition 5.18. These facts are proved for the law itself. -/
theorem proper_scalar_internal (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε : ℝ) :
    let N := ((n : ℕ)+m).succPNat
    let ν := activeTiltedGapLaw (ofLong β s) N n (by simp only [N,Nat.succPNat_coe]; omega) θ ε false
    let Ω := AffineSimplex.chartDomain n ((n+m : ℕ)+1)
    IsProbabilityMeasure ν ∧ Ω.Nonempty ∧
    (∃ V, IsEuclideanGibbsPotential volume ν Ω V 2) ∧
    ∃ Q : ScalarFormData ν, IsNeumannRealization Ω Q ∧
    ∃ _hQ : IsClosedScalarDirichletForm Q, IsConservativeScalarForm Q ∧
    MeasurePreserving ((↑) : Ω → EuclideanSpace ℝ (Fin (n : ℕ)))
      (ν.comap ((↑) : Ω → EuclideanSpace ℝ (Fin (n : ℕ)))) ν := by
  intro N ν Ω
  have hpot := PhysicalFormDomain.proper_gibbs_potential β s n m θ ε
  have hΩ := AffineSimplex.isOpen_chartDomain (n : ℕ) ((n+m : ℕ)+1)
  have hB := AffineSimplex.isBounded_chartDomain (n : ℕ) ((n+m : ℕ)+1)
  have hprob : IsProbabilityMeasure ν := IntrinsicScalarCore.probability hpot
  have hne : Ω.Nonempty := by
    refine ⟨WithLp.toLp 2 (fun _ => (1 : ℝ)),(fun _ => zero_lt_one),?_⟩
    change (∑ _i : Fin (n : ℕ), (1 : ℝ)) < ((n+m : ℕ) : ℝ)+1
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
    push_cast
    linarith
  refine ⟨hprob,hne,⟨_,hpot.1.of_le (by norm_num),hpot.2⟩,
    IntrinsicScalarCore.form hΩ hB hpot,IntrinsicScalarCore.realization hΩ hB hpot,
    IntrinsicScalarCore.closed_dirichlet hΩ hB hpot,
    IntrinsicScalarCore.conservative hΩ hB hpot,measurable_subtype_coe,?_⟩
  rw [map_comap_subtype_coe hΩ.measurableSet]
  exact Measure.restrict_eq_self_of_ae_mem (IntrinsicScalarCore.supported hΩ hpot)

/-- The existing proper physical auxiliary forms agree with the
ambient periodized forms, including their Schur restriction. This
internal bridge supports the proof of Proposition 5.18. -/
theorem proper_auxiliary_identification_internal
    (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (hnN : 2*(n : ℕ) ≤ (n : ℕ)+m+1)
    (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hhalf : 2*(n : ℕ) ≤ (M : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (hK : 1 ≤ K) (hKM : K ≤ (M : ℕ)/4)
    (θ : PhysicalCutoff) (ε κ₀ : ℝ) (hε : 0 ≤ ε)
    {ν : Measure (EuclideanSpace ℝ (Fin (n : ℕ)))}
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (hco : MeasurePreserving
      ((↑) : AffineSimplex.chartDomain n ((n+m : ℕ)+1) → EuclideanSpace ℝ (Fin (n : ℕ)))
      (ν.comap ((↑) : AffineSimplex.chartDomain n ((n+m : ℕ)+1) → EuclideanSpace ℝ (Fin (n : ℕ)))) ν)
    (Cstar ks gs : ℝ) (hCstar : 1 ≤ Cstar)
    (A : EuclideanSpace ℝ (Fin (n : ℕ)) → Matrix (Fin (M : ℕ)) (Fin (M : ℕ)) ℝ)
    (heq : ∀ x, A x.val = properMatrix β s n m M hM hnM K θ ε κ₀ x)
    (hA : PeriodizedMatrixBounds (ν := ν) s n M hM K Cstar ks gs ε A) :
    let Ω := AffineSimplex.chartDomain n ((n+m : ℕ)+1)
    let μ := ν.comap ((↑) : Ω → EuclideanSpace ℝ (Fin (n : ℕ)))
    ∃ (F : MatrixEnergy.Vector (ι := Fin (M : ℕ)) Q hQ →L[ℝ]
        MatrixEnergy.Vector (ι := Fin (M : ℕ)) Q hQ →L[ℝ] ℝ)
      (S G : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ]
        MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ] ℝ)
      (R : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ]
        MatrixEnergy.Vector (ι := Fin ((M : ℕ)-(n : ℕ))) Q hQ),
    let J := SchurRestriction.assemble Q hQ n M hnM
    let P := fun z z' => fun x : Ω => matrixFieldPair
      (fun _ : EuclideanSpace ℝ (Fin (n : ℕ)) => (2 : ℝ) • referenceIntervalMatrix s M hM K)
      (fun i => (MatrixEnergy.vectorEquiv Q hQ (J z) i).val)
      (fun i => (MatrixEnergy.vectorEquiv Q hQ (J z') i).val) x.val
    (∀ u v,
      let B := fun x : Ω => ∑ i, ∑ j,
        (MatrixEnergy.vectorEquiv Q hQ u i).val x.val *
          properMatrix β s n m M hM hnM K θ ε κ₀ x i j *
          (MatrixEnergy.vectorEquiv Q hQ v j).val x.val
      Integrable B μ ∧ F u v = OperatorSchur.vectorEnergy Q hQ u v + β.val * ∫ x, B x ∂μ) ∧
    (∀ u v, S u v = F (J (u,0)) (J (v,0)) - G u v) ∧
    (∀ u w, β.val⁻¹ * OperatorSchur.vectorEnergy Q hQ (R u) w +
      (∫ x, P (0,R u) (0,w) x ∂μ) = ∫ x, P (u,0) (0,w) x ∂μ) ∧
    (∀ u v, G u v = β.val * ∫ x, P (v,0) (0,R u) x ∂μ) ∧
    F = SchurRestriction.periodizedForm Q hQ n M s hM K Cstar ks gs ε β.val
      hCstar β.property A hA ∧
    S = SchurRestriction.schurForm Q hQ n M hnM s hM K Cstar ks gs ε β.val
      hCstar β.property A hA := by
  intro Ω μ
  have hf := MeasurableEmbedding.subtype_coe
    (AffineSimplex.isOpen_chartDomain (n : ℕ) ((n+m : ℕ)+1)).measurableSet
  obtain ⟨F,S,G,R,hF,_,_,hS,hR,hG,_⟩ :=
    PhysicalIdentity.Internal.proper_auxiliary_forms β s n m hnN M hM hhalf K hK hKM
      θ ε κ₀ hε Q hQ hco
  obtain ⟨hFeq,_,hSeq⟩ := carrier_schur_form_internal _ hf hco Q hQ s n M hnM hM K
    Cstar ks gs ε β.val hCstar β.property _ A heq hA F S G R
    (fun u v => (hF u v).2) hS (fun u w => (hR u w).2.2) (fun u v => (hG u v).2)
  exact ⟨F,S,G,R,hF,hS,(fun u w => (hR u w).2.2),(fun u v => (hG u v).2),hFeq,hSeq⟩

/-- See the proof of Proposition 5.18 in the paper (all conclusions). The ambient matrix
agrees everywhere on the physical chart with the actual proper matrix.
Its Schur form agrees with the existing physical construction by
`proper_auxiliary_identification_internal`. The summed equation is
valid on the entire scalar form domain, with the actual physical
reference error. The prefactor is uniform on compact positive
temperature intervals, and the loss exponent precedes epsilon and
those intervals. The structural witnesses are independent of volume. -/
theorem physical_mean (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (θ : PhysicalCutoff) (M₀ : ℕ+)
    (κ₀ : ℝ) (hκ₀ : 0 ≤ κ₀) :
    ∃ ε₀ κ ks gs Cstar : ℝ,
      0 < ε₀ ∧ 0 < κ ∧ 0 < ks ∧ 0 < gs ∧ ∃ hCstar : 1 ≤ Cstar,
    ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
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
    let μ := ν.comap ((↑) : Ω → EuclideanSpace ℝ (Fin (n : ℕ)))
    ∃ Q : ScalarFormData ν, IsNeumannRealization Ω Q ∧
    ∃ hQ : IsClosedScalarDirichletForm Q, IsConservativeScalarForm Q ∧
    ∃ A : EuclideanSpace ℝ (Fin (n : ℕ)) → Matrix (Fin (M : ℕ)) (Fin (M : ℕ)) ℝ,
      (∀ x : Ω, A x.val = properMatrix β s n m M hM hnM K θ ε κ₀ x) ∧
    ∃ hA : PeriodizedMatrixBounds (ν := ν) s n M hM K Cstar ks gs ε A,
    let S := SchurRestriction.schurForm Q hQ n M hnM s hM K Cstar ks gs ε β.val
      hCstar β.property A hA
    ∀ i₀ : Fin (n : ℕ), (n : ℝ)/4 ≤ (i₀.val : ℝ)+1 →
      (i₀.val : ℝ)+1 ≤ 3*(n : ℝ)/4 → ∀ χ : Lp ℝ 2 ν,
    let f := WithLp.toLp 2 (fun i : Fin (n : ℕ) => if i=i₀ then χ else 0)
    (∃! Ψ : Fin (M : ℕ) → Q.1, WeightedWeakSolution Q (fun x => β.val • A x) ⊤
      (fun j => if j=i₀.castLE hnM then χ else 0) Ψ) ∧
    (∃! v, ∀ w, S v w = inner ℝ f (OperatorSchur.vectorValues Q hQ w)) ∧
    ∀ (Ψ : Fin (M : ℕ) → Q.1)
      (v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ),
      WeightedWeakSolution Q (fun x => β.val • A x) ⊤
        (fun j => if j=i₀.castLE hnM then χ else 0) Ψ →
      (∀ w, S v w = inner ℝ f (OperatorSchur.vectorValues Q hQ w)) →
    let v' := MatrixEnergy.vectorEquiv Q hQ v
    (∀ i, Ψ (i.castLE hnM) = v' i) ∧
    (∀ j, ‖(Ψ j).val‖ ≤ C*(n : ℝ)^(κ*ε)*
      weightRadius M j (i₀.castLE hnM)^(-(2-s.val))*‖χ‖) ∧
    (∑ j, ‖(Ψ j).val‖) ≤ C*(n : ℝ)^(κ*ε)*‖χ‖ ∧
    ∃ g : Lp ℝ 2 ν,
      (∀ᵐ x ∂μ, g x.val = β.val * ∑ a, ∑ b, (Ψ a).val x.val *
        (properMatrix β s n m M hM hnM K θ ε κ₀ x a b -
          ((2 : ℝ) • rieszMatrix s M hM) a b)) ∧
      (∀ w : Q.1, Q.2 (∑ j,Ψ j) w +
        (β.val*(2*∑ k, sampledRieszKernel s M hM k))*inner ℝ (∑ j,(Ψ j).val) w.val =
          inner ℝ (χ-g) w.val) ∧
      (∑ i,v' i) = (∑ j,Ψ j) -
        ∑ j ∈ Finset.univ.filter (fun j : Fin (M : ℕ) => (n : ℕ) ≤ j.val), Ψ j ∧
      ‖∑ i,(v' i).val‖ ≤ C*(n : ℝ)^(κ*ε)*(n : ℝ)^(-(1-s.val))*‖χ‖ := by
  obtain ⟨ε₀,ks,gs,he₀,hks,hgs,Cstar,hCstar,hbounds⟩ :=
    proper_matrix_bounds_uniform_internal s θ M₀ κ₀ hκ₀
  obtain ⟨κ,hκ,hmean⟩ := periodized_mean_internal hzeta s ks gs hks hgs M₀
  refine ⟨ε₀,κ,ks,gs,Cstar,he₀,hκ,hks,hgs,hCstar,?_⟩
  intro ε hε hεa βlo βhi hβlo hβhi
  obtain ⟨C,hC,hmean⟩ := hmean ε hε Cstar hCstar βlo βhi hβlo hβhi
  refine ⟨C,hC,?_⟩
  intro β hβ n m hn hnN N M hM hnM K hK hKM ν Ω μ
  have hhalf : 2*(n : ℕ) ≤ (M : ℕ) := (properReferencePeriod_bounds s n N hnN).1
  obtain ⟨hprob,hne,hpot2,Q,hreal,hQ,hcons,hco⟩ := proper_scalar_internal β s n m θ ε
  change ScalarFormData ν at Q
  change IsNeumannRealization Ω Q at hreal
  change IsClosedScalarDirichletForm Q at hQ
  change IsConservativeScalarForm Q at hcons
  change MeasurePreserving ((↑) : Ω → EuclideanSpace ℝ (Fin (n : ℕ))) μ ν at hco
  have : IsProbabilityMeasure ν := hprob
  have hΩ := AffineSimplex.isOpen_chartDomain (n : ℕ) ((n+m : ℕ)+1)
  have hB := AffineSimplex.isBounded_chartDomain (n : ℕ) ((n+m : ℕ)+1)
  have hf := MeasurableEmbedding.subtype_coe hΩ.measurableSet
  have hKM' : K ≤ (M : ℕ)/4 := by omega
  have hmat := hbounds β ε hε.le hεa n m hnN hKM' μ
  obtain ⟨A,heq,hA⟩ := periodized_matrix_extension_internal _ hf hco s n M hM K
    Cstar ks gs ε _ hmat
  refine ⟨Q,hreal,hQ,hcons,A,heq,hA,?_⟩
  intro S i₀ hlo hhi χ f
  have hd := hmean β hβ n M hn hM hhalf (proper_period_upper_internal s n N)
    hK hKM n Ω ν hΩ (AffineSimplex.convex_chartDomain _ _) hB hne inferInstance
    hpot2 Q hreal hQ hcons A hA i₀ hlo hhi χ
  have hs := SchurRestriction.schur_restriction_weak Q hQ n M hnM s hM K Cstar ks gs ε
    β.val hCstar β.property A hA f
  obtain ⟨hfull,hdec⟩ := hd
  obtain ⟨_,hschur,_⟩ := hs
  refine ⟨?_,?_,?_⟩
  · exact hfull
  · exact hschur
  intro Ψ v hu hv v'
  have hcomp := schur_components_internal Q hQ s n M hnM hM K Cstar ks gs ε β.val
    hCstar β.property A hA i₀ χ Ψ v hu hv
  obtain ⟨hp,hsum,hactive,g,hg,hgeq,hmn⟩ := hdec Ψ hu
  have hg' : ∀ᵐ x ∂μ, g x.val = β.val * ∑ a, ∑ b, (Ψ a).val x.val *
      (properMatrix β s n m M hM hnM K θ ε κ₀ x a b -
        ((2 : ℝ) • rieszMatrix s M hM) a b) := by
    have hh := hco.quasiMeasurePreserving.ae hg
    filter_upwards [hh] with x hx
    change g x.val = β.val * ∑ a, ∑ b, (Ψ a).val x.val *
      (A x.val a b - ((2 : ℝ) • rieszMatrix s M hM) a b) at hx
    simpa only [heq] using hx
  refine ⟨hcomp,hp,hsum,g,hg',hgeq,?_,?_⟩
  · simpa only [hcomp] using hactive
  · simpa only [hcomp] using hmn

end Riesz2.PhysicalMean
