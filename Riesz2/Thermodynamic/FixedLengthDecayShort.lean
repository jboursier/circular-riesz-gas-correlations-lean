/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.FixedLengthDecayPart6
public import Riesz2.Thermodynamic.InterpolationCoefficientBounds

/-!
# Short-range physical fixed-length comparison

Physical identity-cutoff and exceptional coefficient estimates for Lemma 6.4, using the
same scalar form as the tangent equation.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator ContDiff

attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.FixedLengthDecay

/-- See Lemma 6.4 of the paper: a square coefficient envelope and the weighted
exceptional tail give a uniform first-moment error. The polynomial envelope
degree may depend on the temperature interval. The tail power is preserved. -/
theorem short_exceptional_moment_uniform_internal
    (K T D q r c δ : ℝ) (hK : 0 ≤ K) (hT : 0 ≤ T) (hD : 0 ≤ D)
    (hc : 0 < c) (hδ : 0 < δ) :
    ∃ E : ℝ, 0 < E ∧ ∀ x : ℝ, 1 ≤ x →
      Real.sqrt ((K*x^q)*(T*Real.exp (-c*x^δ))) +
        (D*x^r)*(T*Real.exp (-c*x^δ)) ≤ E*Real.exp (-(c/4)*x^δ) := by
  obtain ⟨K₁,hK₁,h₁⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := q/2) (c := c/2) (c' := c/4) hδ (by linarith)
  obtain ⟨K₂,hK₂,h₂⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := r) (c := c) (c' := c/4) hδ (by linarith)
  refine ⟨Real.sqrt (K*T)*K₁+D*T*K₂+1,by positivity,?_⟩
  intro x hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hs : Real.sqrt ((K*x^q)*(T*Real.exp (-c*x^δ))) =
      Real.sqrt (K*T)*x^(q/2)*Real.exp (-(c/2)*x^δ) := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
    rw [mul_pow,mul_pow,Real.sq_sqrt (mul_nonneg hK hT),
        ← Real.rpow_mul_natCast hx0.le,Nat.cast_ofNat,show q/2*(2 : ℝ) = q by ring,
        pow_two (Real.exp _),← Real.exp_add]
    rw [show -(c/2)*x^δ+ -(c/2)*x^δ = -c*x^δ by ring]
    ring
  rw [hs]
  have hb₁ := mul_le_mul_of_nonneg_left (h₁ x hx) (Real.sqrt_nonneg (K*T))
  have hb₂ := mul_le_mul_of_nonneg_left (h₂ x hx) (mul_nonneg hD hT)
  have he := Real.exp_pos (-(c/4)*x^δ)
  nlinarith only [hb₁,hb₂,he]

/-- See Lemma 6.4 of the paper: the literal identity cutoff has the
summable coercive matrix interface on the physical fibre. This statement
allows any probability supported on that fibre, so it applies to the original
normalized Hausdorff law without changing its scalar form. -/
theorem short_identity_cutoff_matrix_internal
    (s : ShortExponent) (a : ℕ) (L N : ℝ)
    (ν : Measure (AffineSimplex.chartDomain (a+1) N))
    (hsupp : ∀ᵐ x ∂ν, x.val ∈ AffineSimplex.massSimplex a L)
    (H : EuclideanSpace ℝ (Fin (a+1)) → ℝ)
    (G : Set (EuclideanSpace ℝ (Fin (a+1)))) (hG : MeasurableSet G)
    (C κ ε : ℝ) (hC : 1 ≤ C) (hloss : 0 ≤ κ*ε)
    (hsym : ∀ x ∈ AffineSimplex.massSimplex a L,
      (hessianMatrix H x).IsSymm)
    (hlower : ∀ x ∈ AffineSimplex.massSimplex a L, ∀ z : Fin (a+1) → ℝ,
      C⁻¹*(a+1 : ℝ)^(-κ*ε)*(∑ i,z i^2) ≤
        ∑ i,∑ j,z i*hessianMatrix H x i j*z j)
    (hentry : ∀ x ∈ AffineSimplex.massSimplex a L, ∀ i j : Fin (a+1),
      |(if x ∈ G then hessianMatrix H x else (1 : Matrix (Fin (a+1)) (Fin (a+1)) ℝ)) i j| ≤
        C*(a+1 : ℝ)^(κ*ε)*(1+|(i.val : ℝ)-j.val|)^(-s.val)) :
    let g : ComponentGeometry (Fin (a+1)) := Sum.inl
      ⟨fun i => (i.val : ℤ),fun _ _ h => Fin.ext (Int.ofNat_inj.mp h)⟩
    let M := fun x : AffineSimplex.chartDomain (a+1) N =>
      if x.val ∈ G then hessianMatrix H x.val else (1 : Matrix (Fin (a+1)) (Fin (a+1)) ℝ)
    SummableCoerciveMatrix (ρ := ν) s a.succPNat ε C κ g M := by
  intro g M
  refine ⟨fun i j => ?_,?_⟩
  · have heq : (fun x => M x i j) =
        (fun x : AffineSimplex.chartDomain (a+1) N =>
          if x.val ∈ G then hessianMatrix H x.val i j else
            (1 : Matrix (Fin (a+1)) (Fin (a+1)) ℝ) i j) := by
        funext x
        dsimp only [M]
        split_ifs <;> rfl
    rw [heq]
    exact (Measurable.ite (hG.preimage measurable_subtype_coe)
        ((DifferentiatedPoisson.measurable_hessian_entries (V := H) i j).comp measurable_subtype_coe)
        (measurable_const : Measurable (fun _x : AffineSimplex.chartDomain (a+1) N =>
          (1 : Matrix (Fin (a+1)) (Fin (a+1)) ℝ) i j)))
  · filter_upwards [hsupp] with x hx
    refine ⟨?_,?_,?_⟩
    · intro i j
      dsimp only [M]
      split_ifs
      · exact congrFun (congrFun (hsym x.val hx).eq j) i
      · exact Matrix.isSymm_one.apply j i
    · intro z
      have hp : (C*(a+1 : ℝ)^(κ*ε))⁻¹ = C⁻¹*(a+1 : ℝ)^(-κ*ε) := by
        rw [mul_inv,← Real.rpow_neg (by positivity : (0 : ℝ) ≤ a+1)]
        congr 2
        ring
      simp only [Nat.succPNat_coe,Nat.cast_succ]
      change (C*(a+1 : ℝ)^(κ*ε))⁻¹*(∑ i,z i^2) ≤ _
      rw [hp]
      dsimp only [M]
      split_ifs with hg
      · exact hlower x.val hx z
      · have hc : C⁻¹*(a+1 : ℝ)^(-κ*ε) ≤ 1 := by
          rw [← hp]
          apply inv_le_one_of_one_le₀
          exact one_le_mul_of_one_le_of_one_le hC
            (Real.one_le_rpow (by have := Nat.cast_nonneg a (α := ℝ); linarith) hloss)
        have hsum : ∑ i,∑ j,z i*(1 : Matrix (Fin (a+1)) (Fin (a+1)) ℝ) i j*z j = ∑ i,z i^2 := by
          simp [Matrix.one_apply,pow_two]
        rw [hsum]
        exact mul_le_of_le_one_left (Finset.sum_nonneg fun i _ => sq_nonneg (z i)) hc
    · intro i j
      simp only [Nat.succPNat_coe,Nat.cast_succ,componentDistance,g,
        Function.Embedding.coeFn_mk,Int.cast_natCast]
      change |M x i j| ≤ C*(a+1 : ℝ)^(κ*ε)*(1+|(i.val : ℝ)-j.val|)^(-s.val)
      exact hentry x.val hx i j

/-- See Lemma 6.4 of the paper: compose the actual coefficient
comparison, scalar mean estimates and exceptional first moments into a
squared vector error. -/
theorem short_square_from_coefficients_internal
    {X : Type*} [MeasurableSpace X] {ν : Measure X} [IsProbabilityMeasure ν]
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (s : ℝ) (hs : 1 < s) (n : ℕ+) (g : ComponentGeometry (Fin (n : ℕ)))
    (H M : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (hHm : ∀ i j, Measurable (fun x => H x i j))
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hH : ∀ᵐ x ∂ν, (H x).PosSemidef) (hM : ∀ᵐ x ∂ν, (M x).PosSemidef)
    (a0 loss : ℝ) (ha0 : 0 < a0) (hloss : 0 ≤ loss)
    (hHa : ∀ᵐ x ∂ν, (∀ i j, H x i j = H x j i) ∧
      ∀ z : Fin (n : ℕ) → ℝ, (a0*(n : ℝ)^(-loss))*(∑ i,z i^2) ≤
        ∑ i,∑ j,z i*H x i j*z j)
    (hMa : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
      ∀ z : Fin (n : ℕ) → ℝ, (a0*(n : ℝ)^(-loss))*(∑ i,z i^2) ≤
        ∑ i,∑ j,z i*M x i j*z j)
    (G : Set X) (hG : MeasurableSet G) (P0 K T E0 c δ : ℝ)
    (hP0 : 0 ≤ P0) (hK : 0 ≤ K) (hT : 0 ≤ T) (hE0 : 0 ≤ E0)
    (hMb : ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ P0*(n : ℝ)^loss)
    (heq : ∀ᵐ x ∂ν, x ∈ G → H x = M x)
    (hgood : ∀ᵐ x ∂ν.restrict G, ∀ i j,
      |H x i j| ≤ (P0*(n : ℝ)^loss)*(1+componentDistance g i j)^(-s))
    (W : X → ℝ) (hW : IntegrableOn W Gᶜ ν)
    (hW1 : ∀ᵐ x ∂ν.restrict Gᶜ, 1 ≤ W x)
    (hsq : ∀ᵐ x ∂ν.restrict Gᶜ, ∀ i j, H x i j^2 ≤ K*W x)
    (htail : (∫ x in Gᶜ,W x ∂ν) ≤ T)
    (herr : Real.sqrt (K*T)+(P0*(n : ℝ)^loss)*T ≤ E0*Real.exp (-c*(n : ℝ)^δ))
    (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν) (B D0 : ℝ) (hB : 0 ≤ B) (hD0 : 0 ≤ D0)
    (hχ : ∀ᵐ x ∂ν, |χ x| ≤ B) (ψ v : Fin (n : ℕ) → Q.1)
    (hψ : WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ)))
      (fun i => if i = i₀ then χ else 0) ψ)
    (hv : WeightedWeakSolution Q M ⊤ (fun i => if i = i₀ then χ else 0) v)
    (hmean : ‖(∑ i,v i : Q.1).val‖ ≤ D0*(n : ℝ)^loss*‖χ‖)
    (hgrad : Real.sqrt (Q.2 (∑ i,v i) (∑ i,v i)) ≤ D0*(n : ℝ)^loss*‖χ‖) :
    let K0 := P0*(2*∑' k : ℕ,(1+(k : ℝ))^(-s))
    ‖WithLp.toLp 2 (fun i => (ψ i).val-(v i).val)‖^2 ≤
      (3*((1+K0)*D0^2/a0+D0^2))*(n : ℝ)^(8*loss-1)*‖χ‖^2 +
      (9*(E0*(2*a0⁻¹+a0⁻¹)*a0⁻¹+E0*(a0⁻¹)^2)/a0)*
        (n : ℝ)^(4+4*loss)*Real.exp (-c*(n : ℝ)^δ)*B^2 := by
  intro K0
  let S : Q.1 := ∑ i,v i
  let a := a0*(n : ℝ)^(-loss)
  let V := a⁻¹*B
  let U := 2*V+a⁻¹*B
  let Err := Real.sqrt (K*T)+(P0*(n : ℝ)^loss)*T
  let τ := (n : ℝ)^2*V*U*Err
  let R := (n : ℝ)⁻¹*Q.2 S S+(n : ℝ)⁻¹^2*
    (((P0*(n : ℝ)^loss)*(2*∑' k : ℕ,(1+(k : ℝ))^(-s))*(n : ℝ))*‖S.val‖^2+
      ((n : ℝ)*V)^2*((n : ℝ)^2*Real.sqrt (K*T)))
  have hn : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have ha : 0 < a := by dsimp only [a]; positivity
  have hV : V = a0⁻¹*(n : ℝ)^loss*B := by
    dsimp only [V,a]
    rw [mul_inv,← Real.rpow_neg hn.le,neg_neg]
  have hU : U = (2*a0⁻¹+a0⁻¹)*(n : ℝ)^loss*B := by
    dsimp only [U]
    rw [hV]
    change 2*(a0⁻¹*(n : ℝ)^loss*B)+(a0*(n : ℝ)^(-loss))⁻¹*B = _
    rw [mul_inv,← Real.rpow_neg hn.le,neg_neg]
    ring
  have hc := short_comparison_from_coefficients_internal Q hQ s hs n g H M hHm hMm hH hM
    a a ha ha hHa hMa G hG (P0*(n : ℝ)^loss) (P0*(n : ℝ)^loss) K T
    (by positivity) (by positivity) hK hT hMb heq hgood W hW hW1 hsq htail
    i₀ χ B hB hχ ψ v hψ hv
  have hroot : Real.sqrt (K*T) ≤ E0*Real.exp (-c*(n : ℝ)^δ) :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (P0*(n : ℝ)^loss)*T)).trans herr
  have hτ : τ ≤ (n : ℝ)^2*(E0*Real.exp (-c*(n : ℝ)^δ)*
      ((2*a0⁻¹+a0⁻¹)*(n : ℝ)^loss*B)*(a0⁻¹*(n : ℝ)^loss*B)) := by
    dsimp only [τ]
    rw [hV,hU]
    calc
      _ ≤ (n : ℝ)^2*(a0⁻¹*(n : ℝ)^loss*B)*
          ((2*a0⁻¹+a0⁻¹)*(n : ℝ)^loss*B)*(E0*Real.exp (-c*(n : ℝ)^δ)) := by
        exact mul_le_mul_of_nonneg_left herr (by positivity)
      _ = _ := by ring
  have hR : R ≤ (n : ℝ)⁻¹*Q.2 S S+K0*(n : ℝ)^(loss-1)*‖S.val‖^2+
      (n : ℝ)^4*(E0*Real.exp (-c*(n : ℝ)^δ))*(a0⁻¹*(n : ℝ)^loss*B)^2 := by
    have heqR : R = (n : ℝ)⁻¹*Q.2 S S+
        K0*(n : ℝ)^(loss-1)*‖S.val‖^2+(n : ℝ)^2*V^2*Real.sqrt (K*T) := by
      dsimp only [R,K0]
      rw [show loss-1 = loss+(-1) by ring,Real.rpow_add hn,Real.rpow_neg_one]
      field_simp
      ring
    rw [heqR,hV]
    apply add_le_add le_rfl
    calc
      _ ≤ (n : ℝ)^2*(a0⁻¹*(n : ℝ)^loss*B)^2*(E0*Real.exp (-c*(n : ℝ)^δ)) := by
        gcongr
      _ ≤ (n : ℝ)^4*(a0⁻¹*(n : ℝ)^loss*B)^2*(E0*Real.exp (-c*(n : ℝ)^δ)) := by
        gcongr
        norm_num
      _ = _ := by ring
  have hτ0 : 0 ≤ τ := by dsimp only [τ,Err]; rw [hV,hU]; positivity
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity [hQ.2.2.1 S]
  apply short_comparison_square_uniform_internal loss a0 K0 D0 a0⁻¹ E0 c δ hloss ha0
    (by dsimp only [K0]; positivity) hD0 (by positivity) hE0
    X ν Q hQ n S ‖χ‖ B ‖WithLp.toLp 2 (fun i => (ψ i).val-(v i).val)‖ τ R
    (norm_nonneg _) hB (norm_nonneg _) hτ0 hR0 hmean hgrad hτ hR
  convert hc using 1
  dsimp only [τ,Err,R,S,V,U,a]
  congr 2
  ring

/-- Composition for Lemma 6.4. This internal
theorem constructs the auxiliary field from the summable coefficient bound
and proves both physical coordinate sums. Its hypotheses are coefficient and
weighted-tail data, rather than any auxiliary or comparison conclusion.
The common loss degree precedes epsilon and every prefactor. -/
theorem short_fixed_length_from_coefficients_internal (s : ShortExponent)
    (q : ℝ) (hq : 0 ≤ q) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ ε : ℝ, 0 < ε →
    ∀ A K0 T0 qK c δ : ℝ, 1 ≤ A → 0 ≤ K0 → 0 ≤ T0 → 0 < c → 0 < δ →
    ∀ n0 : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ+) (X : Type) [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
      (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
    ∀ H : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ,
      (∀ i j, Measurable (fun x => H x i j)) →
      (∀ᵐ x ∂ν, (H x).PosSemidef) →
      (∀ᵐ x ∂ν, ∀ z : Fin (n : ℕ) → ℝ,
        (A⁻¹*(n : ℝ)^(-(q*ε)))*(∑ i,z i^2) ≤ ∑ i,∑ j,z i*H x i j*z j) →
    ∀ i₀ : Fin (n : ℕ), |(i₀.val : ℝ)+1-(n : ℝ)/2| ≤ (n : ℝ)/4 →
    ∀ χ : BoundedL2Pairings.boundedSubmodule ν,
    ∀ ψ : Fin (n : ℕ) → Q.1,
      WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ)))
        (fun i => if i = i₀ then χ.val else 0) ψ →
    let g : ComponentGeometry (Fin (n : ℕ)) := Sum.inl
      ⟨fun i => (i.val : ℤ),fun _ _ h => Fin.ext (Int.ofNat_inj.mp h)⟩
    ((n0 : ℝ) ≤ (n : ℝ) →
      ∃ (M : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ) (G : Set X) (W : X → ℝ),
        SummableCoerciveMatrix (ρ := ν) s n ε A q g M ∧ MeasurableSet G ∧
        (∀ᵐ x ∂ν, x ∈ G → H x = M x) ∧
        IntegrableOn W Gᶜ ν ∧ (∀ᵐ x ∂ν.restrict Gᶜ,1 ≤ W x) ∧
        (∀ᵐ x ∂ν.restrict Gᶜ,∀ i j,H x i j^2 ≤ K0*(n : ℝ)^qK*W x) ∧
        (∫ x in Gᶜ,W x ∂ν) ≤ T0*Real.exp (-c*(n : ℝ)^δ)) →
    let B := (eLpNorm (χ.val : X → ℝ) ∞ ν).toReal
    (∑ j,InteractionDifferential.boundaryWeight s.val n j*‖(ψ j).val‖) ≤
      C*(n : ℝ)^(κ*ε-1/2)*(‖χ.val‖+Real.exp (-(c/16)*(n : ℝ)^δ)*B) ∧
    (∑ j,‖(ψ j).val‖) ≤
      C*(n : ℝ)^(κ*ε)*(‖χ.val‖+Real.exp (-(c/16)*(n : ℝ)^δ)*B) := by
  obtain ⟨κa,hκa,haux⟩ := short_auxiliary_estimates_internal s q hq
  let κb := max q κa
  have hκb : 0 ≤ κb := hq.trans (le_max_left _ _)
  refine ⟨max q (4*κb),le_max_of_le_left hq,?_⟩
  intro ε hε A K0 T0 qK c δ hA hK0 hT0 hc hδ n0
  obtain ⟨D0,hD0,haux⟩ := haux ε hε A hA 1 1 (by norm_num) le_rfl
  obtain ⟨E0,hE0,herr⟩ := short_exceptional_moment_uniform_internal K0 T0 A qK (κb*ε) c δ
    hK0 hT0 (by linarith) hc hδ
  let a0 := A⁻¹
  let Krow := A*(2*∑' k : ℕ,(1+(k : ℝ))^(-s.val))
  let Derr := 3*((1+Krow)*D0^2/a0+D0^2)
  let Terr := 9*(E0*(2*a0⁻¹+a0⁻¹)*a0⁻¹+E0*(a0⁻¹)^2)/a0
  have ha0 : 0 < a0 := inv_pos.mpr (by linarith)
  obtain ⟨C,hC,hjoin⟩ := fixed_length_decay_from_comparison_internal
    s.val (by linarith [s.property]) (ne_of_gt s.property) q (4*κb) ε hε.le n0
    a0 D0 Derr Terr (4+4*(κb*ε)) (c/4) δ ha0 (by linarith)
    (by dsimp only [Derr,Krow]; positivity) (by dsimp only [Terr]; positivity)
    (by positivity) hδ
  refine ⟨C,hC,?_⟩
  intro n X _ ν _ Q hQ hcons H hHm hH hlower i₀ hi₀ χ ψ hψ g hcoeff B
  have hn : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hB : 0 ≤ B := ENNReal.toReal_nonneg
  have hχ := bounded_ae_essentialNorm_internal χ
  have hpow (p r : ℝ) (hpr : p ≤ r) : (n : ℝ)^(p*ε) ≤ (n : ℝ)^(r*ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (mul_le_mul_of_nonneg_right hpr hε.le)
  have hbig : (n0 : ℝ) ≤ (n : ℝ) → ∃ v : Fin (n : ℕ) → Lp ℝ 2 ν,
      (∀ j,‖v j‖ ≤ D0*(n : ℝ)^((4*κb)*ε)*
        (1+(Nat.dist j.val i₀.val : ℝ))^(-s.val)*‖χ.val‖) ∧
      (∑ j,‖v j‖) ≤ D0*(n : ℝ)^((4*κb)*ε)*‖χ.val‖ ∧
      ‖WithLp.toLp 2 (fun j => (ψ j).val-v j)‖^2 ≤
        Derr*(n : ℝ)^(2*((4*κb)*ε)-1)*‖χ.val‖^2+
          Terr*(n : ℝ)^(4+4*(κb*ε))*Real.exp (-(c/4)*(n : ℝ)^δ)*B^2 := by
    intro hlarge
    obtain ⟨M,G,W,hM,hG,heq,hW,hW1,hsq,htail⟩ := hcoeff hlarge
    obtain ⟨hvex,hvest⟩ := haux 1 (by simp) n X (Fin (n : ℕ)) ν Q hQ hcons g M hM i₀ χ.val
    obtain ⟨v,hv,_⟩ := hvex
    have hv' : WeightedWeakSolution Q M ⊤ (fun i => if i = i₀ then χ.val else 0) v := by
      simpa only [one_smul] using hv
    obtain ⟨hvprofile,hvsum,hvmean⟩ := hvest v hv
    let loss := κb*ε
    have hauxfac : D0*(n : ℝ)^(κa*ε) ≤ D0*(n : ℝ)^loss :=
      mul_le_mul_of_nonneg_left (hpow _ _ (le_max_right _ _)) (by linarith)
    have hmean : ‖(∑ i,v i : Q.1).val‖ ≤ D0*(n : ℝ)^loss*‖χ.val‖ :=
      (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans
        (hvmean.trans (mul_le_mul_of_nonneg_right hauxfac (norm_nonneg _)))
    have hgrad : Real.sqrt (Q.2 (∑ i,v i) (∑ i,v i)) ≤ D0*(n : ℝ)^loss*‖χ.val‖ :=
      (le_add_of_nonneg_left (norm_nonneg _)).trans
        (hvmean.trans (mul_le_mul_of_nonneg_right hauxfac (norm_nonneg _)))
    have hcoef : a0*(n : ℝ)^(-loss) ≤ A⁻¹*(n : ℝ)^(-(q*ε)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ a0)
      apply Real.rpow_le_rpow_of_exponent_le hn1
      dsimp only [loss]
      have h := mul_le_mul_of_nonneg_right (le_max_left q κa) hε.le
      linarith
    have hMa : ∀ᵐ x ∂ν,(∀ i j,M x i j = M x j i) ∧ ∀ z : Fin (n : ℕ) → ℝ,
        (a0*(n : ℝ)^(-loss))*(∑ i,z i^2) ≤ ∑ i,∑ j,z i*M x i j*z j := by
      filter_upwards [hM.2] with x hx
      refine ⟨hx.1,fun z => ?_⟩
      have he := hx.2.1 z
      rw [mul_inv,← Real.rpow_neg hn.le] at he
      exact (mul_le_mul_of_nonneg_right hcoef
        (Finset.sum_nonneg fun i _ => sq_nonneg (z i))).trans he
    have hHa : ∀ᵐ x ∂ν,(∀ i j,H x i j = H x j i) ∧ ∀ z : Fin (n : ℕ) → ℝ,
        (a0*(n : ℝ)^(-loss))*(∑ i,z i^2) ≤ ∑ i,∑ j,z i*H x i j*z j := by
      filter_upwards [hH,hlower] with x hx hl
      refine ⟨fun i j => ?_,fun z => ?_⟩
      · simpa only [Matrix.IsHermitian,Matrix.conjTranspose_apply,star_trivial] using
          congrFun (congrFun hx.1 j) i
      · exact (mul_le_mul_of_nonneg_right hcoef
          (Finset.sum_nonneg fun i _ => sq_nonneg (z i))).trans (hl z)
    have hMp : ∀ᵐ x ∂ν,(M x).PosSemidef := by
      filter_upwards [hMa] with x hx
      apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
      refine ⟨?_,fun z => ?_⟩
      · ext i j
        simpa only [Matrix.conjTranspose_apply,star_trivial] using hx.1 j i
      · have hh := (show 0 ≤ (a0*(n : ℝ)^(-loss))*(∑ i,z i^2) by positivity).trans (hx.2 z)
        simpa only [dotProduct,Matrix.mulVec,star_trivial,Finset.mul_sum,mul_assoc] using hh
    have hMb : ∀ᵐ x ∂ν,∀ i j,|M x i j| ≤ A*(n : ℝ)^(q*ε) := by
      filter_upwards [hM.2] with x hx i j
      exact (hx.2.2 i j).trans (mul_le_of_le_one_right (by positivity)
        (Real.rpow_le_one_of_one_le_of_nonpos
          (by linarith [ComponentGeometryBounds.nonneg g i j]) (by linarith [s.property])))
    have hMb' : ∀ᵐ x ∂ν,∀ i j,|M x i j| ≤ A*(n : ℝ)^loss :=
      hMb.mono fun x hx i j => (hx i j).trans
        (mul_le_mul_of_nonneg_left (hpow _ _ (le_max_left _ _)) (by linarith))
    have hgood : ∀ᵐ x ∂ν.restrict G,∀ i j,
        |H x i j| ≤ (A*(n : ℝ)^loss)*(1+componentDistance g i j)^(-s.val) := by
      filter_upwards [ae_restrict_of_ae hM.2,ae_restrict_of_ae heq,ae_restrict_mem hG] with x hx he hxG i j
      rw [he hxG]
      exact (hx.2.2 i j).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hpow _ _ (le_max_left _ _)) (by linarith)) (Real.rpow_nonneg (by linarith [ComponentGeometryBounds.nonneg g i j]) _))
    have hErr : Real.sqrt ((K0*(n : ℝ)^qK)*(T0*Real.exp (-c*(n : ℝ)^δ)))+
        (A*(n : ℝ)^loss)*(T0*Real.exp (-c*(n : ℝ)^δ)) ≤
        E0*Real.exp (-(c/4)*(n : ℝ)^δ) := by
      exact herr n hn1
    have hsqerr := short_square_from_coefficients_internal Q hQ s.val s.property n g H M hHm hM.1 hH hMp
      a0 loss ha0 (mul_nonneg hκb hε.le) hHa hMa G hG A (K0*(n : ℝ)^qK)
      (T0*Real.exp (-c*(n : ℝ)^δ)) E0 (c/4) δ (by linarith) (by positivity) (by positivity)
      hE0.le hMb' heq hgood W hW hW1 hsq htail hErr i₀ χ.val B D0 hB (by linarith)
      hχ ψ v hψ hv' hmean hgrad
    refine ⟨fun i => (v i).val,?_,?_,?_⟩
    · intro j
      have hd : componentDistance g j i₀ = (Nat.dist j.val i₀.val : ℝ) := by
        dsimp only [g,componentDistance]
        simpa only [Function.Embedding.coeFn_mk,Int.cast_natCast] using (show (Nat.dist j.val i₀.val : ℝ) = |(j.val : ℝ)-i₀.val| by exact_mod_cast natCast_dist_eq_abs j.val i₀.val).symm
      have hpj := hvprofile j
      rw [hd] at hpj
      exact hpj.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (hpow _ _ (by have := le_max_right q κa; have := hκb; dsimp only [κb] at *; linarith))
          (by linarith)) (by positivity)) (norm_nonneg _))
    · exact (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans
        (hvsum.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hpow _ _ (by have := le_max_right q κa; linarith))
            (by linarith)) (norm_nonneg _)))
    · simpa only [Derr,Terr,Krow,loss,show 8*(κb*ε)-1 = 2*((4*κb)*ε)-1 by ring] using hsqerr
  have hh := hjoin n X ν Q hQ H hHm hH (hlower.mono fun x hx z _ => hx z)
    i₀ hi₀ χ ψ hψ
    (by simpa only [ite_eq_right (not_lt.mpr s.property.le)] using hbig)
  simpa only [min_eq_right s.property.le,show c/4/4 = c/16 by ring] using hh

/-- See Lemma 6.4 of the paper: scalar temperature multiplication commutes
with the literal finite quadratic pairing. -/
theorem short_scaled_quadratic_internal {ι : Type*} [Fintype ι]
    (b : ℝ) (P : Matrix ι ι ℝ) (v : ι → ℝ) :
    (∑ i,∑ j,v i*(b*P i j)*v j) = b*(∑ i,∑ j,v i*P i j*v j) := by
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- See Lemma 6.4 of the paper: normalize the beta-scaled identity cutoff
on its original mass-fibre carrier. In particular the cutoff outside the
fine event is beta times the identity, as required by the physical equation. -/
theorem short_scaled_cutoff_matrix_internal
    (s : ShortExponent) (a : ℕ) (L N : ℝ)
    (ν : Measure (AffineSimplex.chartDomain (a+1) N))
    (hsupp : ∀ᵐ x ∂ν,x.val ∈ AffineSimplex.massSimplex a L)
    (V : EuclideanSpace ℝ (Fin (a+1)) → ℝ)
    (GA : Set (EuclideanSpace ℝ (Fin (a+1)))) (hGA : MeasurableSet GA)
    (β A q ε : ℝ) (hA : 1 ≤ A) (hloss : 0 ≤ q*ε) (hβlo : A⁻¹ ≤ β)
    (hsym : ∀ u ∈ AffineSimplex.massSimplex a L,∀ i j : Fin (a+1),
      hessianMatrix V u i j = hessianMatrix V u j i)
    (hlower : ∀ᵐ x ∂ν,∀ v : Fin (a+1) → ℝ,
      (A⁻¹*(a+1 : ℝ)^(-(q*ε)))*(∑ i,v i^2) ≤
        ∑ i,∑ j,v i*(β*hessianMatrix V x.val i j)*v j)
    (hentry : ∀ᵐ x ∂ν,∀ i j : Fin (a+1),
      |β*((if x.val ∈ GA then hessianMatrix V x.val else (1 : Matrix (Fin (a+1)) (Fin (a+1)) ℝ)) i j)| ≤
        A*(a+1 : ℝ)^(q*ε)*(1+|(i.val : ℝ)-j.val|)^(-s.val)) :
    let M := fun x : AffineSimplex.chartDomain (a+1) N =>
      β • (if x.val ∈ GA then hessianMatrix V x.val else (1 : Matrix (Fin (a+1)) (Fin (a+1)) ℝ))
    SummableCoerciveMatrix (ρ := ν) s a.succPNat ε A q
      (Sum.inl ⟨fun i => (i.val : ℤ),fun _ _ h => Fin.ext (Int.ofNat_inj.mp h)⟩) M := by
  intro M
  refine ⟨?_,?_⟩
  · intro i j
    have heq : (fun x => M x i j) = (fun x : AffineSimplex.chartDomain (a+1) N =>
        β*(if x.val ∈ GA then hessianMatrix V x.val i j else
          (1 : Matrix (Fin (a+1)) (Fin (a+1)) ℝ) i j)) := by
      funext x
      dsimp only [M]
      split_ifs <;> rfl
    rw [heq]
    exact (Measurable.ite (hGA.preimage measurable_subtype_coe)
      ((DifferentiatedPoisson.measurable_hessian_entries (V := V) i j).comp measurable_subtype_coe)
      measurable_const).const_mul β
  · filter_upwards [hsupp,hlower,hentry] with x hx hl he
    refine ⟨?_,?_,?_⟩
    · intro i j
      dsimp only [M]
      split_ifs
      · simp only [Matrix.smul_apply,smul_eq_mul,hsym x.val hx i j]
      · simp only [Matrix.smul_apply,smul_eq_mul,Matrix.isSymm_one.apply i j]
    · intro v
      simp only [Nat.succPNat_coe,Nat.cast_succ,mul_inv,← Real.rpow_neg (by positivity : (0 : ℝ) ≤ a+1)]
      dsimp only [M]
      split_ifs with hg
      · exact hl v
      · have hc : A⁻¹*(a+1 : ℝ)^(-(q*ε)) ≤ β :=
          (mul_le_of_le_one_right (by positivity)
            (Real.rpow_le_one_of_one_le_of_nonpos
              (by have := Nat.cast_nonneg a (α := ℝ); linarith) (by linarith))).trans hβlo
        have hsum : (∑ i,∑ j,v i*(β • (1 : Matrix (Fin (a+1)) (Fin (a+1)) ℝ)) i j*v j) =
            β*(∑ i,v i^2) := by
          change (∑ i,∑ j,v i*(β*(1 : Matrix (Fin (a+1)) (Fin (a+1)) ℝ) i j)*v j) = _
          rw [short_scaled_quadratic_internal]
          simp [Matrix.one_apply,pow_two]
        rw [hsum]
        exact mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg fun i _ => sq_nonneg (v i))
    · intro i j
      simpa only [M,Matrix.smul_apply,smul_eq_mul,Nat.succPNat_coe,Nat.cast_succ,
        componentDistance,Function.Embedding.coeFn_mk,Int.cast_natCast] using he i j

/-- See Lemma 6.4 of the paper: enlarge the good-set entry prefactor and
power before scaling by temperature. The cutoff on the mass fibre agrees
with the ambient cutoff there, including every boundary component. -/
theorem short_cutoff_entry_enlarge_internal (a : ℕ) (L : ℝ)
    (GA Gf : Set (EuclideanSpace ℝ (Fin (a+1))))
    (hGf : Gf = AffineSimplex.massSimplex a L ∩ GA)
    (V : EuclideanSpace ℝ (Fin (a+1)) → ℝ)
    (β A B p q s : ℝ) (hβ : 0 ≤ β) (hB : 0 ≤ B)
    (hpref : β*B ≤ A) (hp : p ≤ q)
    (hentry : ∀ u (i j : Fin (a+1)),
      |(if u ∈ Gf then hessianMatrix V u else
        (1 : Matrix (Fin (a+1)) (Fin (a+1)) ℝ)) i j| ≤
        B*(a+1 : ℝ)^p*(1+|(i.val : ℝ)-j.val|)^(-s)) :
    ∀ u ∈ AffineSimplex.massSimplex a L,∀ i j : Fin (a+1),
      |β*((if u ∈ GA then hessianMatrix V u else (1 : Matrix (Fin (a+1)) (Fin (a+1)) ℝ)) i j)| ≤
        A*(a+1 : ℝ)^q*(1+|(i.val : ℝ)-j.val|)^(-s) := by
  intro u hu i j
  have he := hentry u i j
  have hh : |(if u ∈ GA then hessianMatrix V u else (1 : Matrix (Fin (a+1)) (Fin (a+1)) ℝ)) i j| ≤
      B*(a+1 : ℝ)^p*(1+|(i.val : ℝ)-j.val|)^(-s) := by
    by_cases hg : u ∈ GA
    · simpa only [ite_eq_left (show u ∈ Gf from hGf.symm ▸ ⟨hu,hg⟩),ite_eq_left hg] using he
    · simpa only [ite_eq_right (show u ∉ Gf from fun h => hg ((hGf ▸ h).2)),ite_eq_right hg] using he
  have hn1 : (1 : ℝ) ≤ a+1 := by have := Nat.cast_nonneg a (α := ℝ); linarith
  have hA0 : 0 ≤ A := (mul_nonneg hβ hB).trans hpref
  rw [abs_mul,abs_of_nonneg hβ]
  calc
    _ ≤ β*(B*(a+1 : ℝ)^p*(1+|(i.val : ℝ)-j.val|)^(-s)) := mul_le_mul_of_nonneg_left hh hβ
    _ = (β*B)*(a+1 : ℝ)^p*(1+|(i.val : ℝ)-j.val|)^(-s) := by ring
    _ ≤ _ := by gcongr

/-- See Lemma 6.4 of the paper: the full scaled curvature and symmetry
give the literal physical PSD and lower-bound inputs on a fibre law. -/
theorem short_mass_curvature_internal
    (s : ShortExponent) (a : ℕ) (L N : ℝ)
    (ν : Measure (AffineSimplex.chartDomain (a+1) N))
    (hsupp : ∀ᵐ x ∂ν,x.val ∈ AffineSimplex.massSimplex a L)
    (V : EuclideanSpace ℝ (Fin (a+1)) → ℝ)
    (β A q ε : ℝ) (hβ : 0 < β) (hA : 1 ≤ A) (hβlo : A⁻¹ ≤ β)
    (hε : 0 ≤ ε) (hq : s.val+2 ≤ q)
    (hsym : ∀ u ∈ AffineSimplex.massSimplex a L,∀ i j : Fin (a+1),
      hessianMatrix V u i j = hessianMatrix V u j i)
    (hcurv : ∀ u ∈ AffineSimplex.massSimplex a L,∀ v : EuclideanSpace ℝ (Fin (a+1)),
      (a+1 : ℝ)^(-(s.val+2)*ε)*(∑ i,(v i)^2) ≤ ∑ i,∑ j,v i*hessianMatrix V u i j*v j) :
    let H := fun x : AffineSimplex.chartDomain (a+1) N => β • hessianMatrix V x.val
    (∀ᵐ x ∂ν,(H x).PosSemidef) ∧
    (∀ᵐ x ∂ν,∀ v : Fin (a+1) → ℝ,
      (A⁻¹*(a+1 : ℝ)^(-(q*ε)))*(∑ i,v i^2) ≤ ∑ i,∑ j,v i*H x i j*v j) := by
  intro H
  have hn1 : (1 : ℝ) ≤ a+1 := by have := Nat.cast_nonneg a (α := ℝ); linarith
  have hl : ∀ᵐ x ∂ν,∀ v : Fin (a+1) → ℝ,
      (A⁻¹*(a+1 : ℝ)^(-(q*ε)))*(∑ i,v i^2) ≤ ∑ i,∑ j,v i*H x i j*v j := by
    filter_upwards [hsupp] with x hx v
    have hp : A⁻¹*(a+1 : ℝ)^(-(q*ε)) ≤ β*(a+1 : ℝ)^(-(s.val+2)*ε) := by
      apply mul_le_mul hβlo _ (by positivity) hβ.le
      apply Real.rpow_le_rpow_of_exponent_le hn1
      nlinarith only [hq,hε]
    change _ ≤ ∑ i,∑ j,v i*(β*hessianMatrix V x.val i j)*v j
    rw [short_scaled_quadratic_internal]
    exact (mul_le_mul_of_nonneg_right hp (Finset.sum_nonneg fun i _ => sq_nonneg (v i))).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hcurv x.val hx (WithLp.toLp 2 v)) hβ.le)
  refine ⟨?_,hl⟩
  filter_upwards [hsupp,hl] with x hx hlow
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨?_,fun v => ?_⟩
  · ext i j
    simp only [H,Matrix.conjTranspose_apply,star_trivial,Matrix.smul_apply,smul_eq_mul]
    rw [hsym x.val hx j i]
  · have hh := (show 0 ≤ (A⁻¹*(a+1 : ℝ)^(-(q*ε)))*(∑ i,v i^2) by positivity).trans (hlow v)
    simpa only [dotProduct,Matrix.mulVec,star_trivial,Finset.mul_sum,mul_assoc] using hh

/-- See Lemma 6.4 of the paper: a two-term physical Hessian square envelope
retains one common polynomial degree on the whole simplex. -/
theorem short_add_square_envelope_internal (b bmax u v A B x w : ℝ)
    (hb : 0 ≤ b) (hbm : b ≤ bmax) (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hx : 1 ≤ x) (hw : 0 ≤ w) (hu : u^2 ≤ A*w) (hv : v^2 ≤ B*x*w) :
    (b*(u+v))^2 ≤ (2*bmax^2*(A+B))*x*w := by
  have ha := mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hA hx) hw
  have hsum : (u+v)^2 ≤ 2*(A+B)*x*w := by nlinarith only [ha,hu,hv,sq_nonneg (u-v)]
  calc
    _ = b^2*(u+v)^2 := mul_pow _ _ _
    _ ≤ bmax^2*(2*(A+B)*x*w) := by gcongr
    _ = _ := by ring

/-- See Lemma 6.4 of the paper, short-range physical conclusion. Constants
are chosen before sizes, compatible admissible exteriors, time and source.
The scalar form is the intrinsic Neumann form of the original normalized
Hausdorff law. The locally uniform rigidity bound is a hypothesis. -/
theorem short_fixed_length_decay (hRig : External.LongRangeRigidityLocallyUniform)
    (s : ShortExponent) :
    ∃ A K ε₀ κ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧ 0 < κ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    ∀ (a e f : ℕ) (_ha : 1 ≤ a) (he : 1 ≤ e) (hf : 1 ≤ f),
      e ≤ f → 4*(a+1) ≤ e+a+1 → (a+1 : ℝ)^(2/s.val) ≤ ((e+a : ℕ)+1 : ℝ) →
    ∀ (y : AffineSimplex.chartDomain e ((e+a : ℕ)+1))
      (z : AffineSimplex.chartDomain f ((f+a : ℕ)+1)) (L : ℝ),
    ∀ (hyL : ((e+a : ℕ)+1 : ℝ)-∑ k,y.val k = L)
      (_hzL : ((f+a : ℕ)+1 : ℝ)-∑ k,z.val k = L),
    InterpolantLocalLaws.admissibleExterior (ofShort β s) e a he θ ε A K y →
    InterpolantLocalLaws.admissibleExterior (ofShort β s) f a hf θ ε A K z →
    let Y := RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val
    let Z := RetainedSimplex.assemble f a (InterpolatingDensities.exteriorPermutation f a) z.val
    let Dy := Y ⁻¹' gapAmbientDomain (e+a).succPNat
    let Dz := Z ⁻¹' gapAmbientDomain (f+a).succPNat
    ∃ Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ,
      ContDiffOn ℝ ∞ Ky Dy ∧ ContDiffOn ℝ ∞ Kz Dz ∧
      (∀ u (hu : u ∈ Dy),Ky u = physicalAmbientGapEnergy (ofShort β s) (e+a).succPNat ⟨Y u,hu⟩) ∧
      (∀ u (hu : u ∈ Dz),Kz u = physicalAmbientGapEnergy (ofShort β s) (f+a).succPNat ⟨Z u,hu⟩) ∧
    ∀ t ∈ Icc (0 : ℝ) 1,
    let Ht := fun u : EuclideanSpace ℝ (Fin (a+1)) =>
      (∑ k,(θ.val ((a+1 : ℝ)^(-ε)*u k)+θ.val ((a+1 : ℝ)^(-ε)*(u k)⁻¹)))+(1-t)*Ky u+t*Kz u
    let μ : Measure (AffineSimplex.massSimplex a L) := (AffineSimplex.simplexVolume a L).comap Subtype.val
    let w := fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal (Real.exp (-β.val*Ht u.val))
    ∃ (h0 : (∫⁻ u,w u ∂μ) ≠ 0) (htop : (∫⁻ u,w u ∂μ) ≠ ⊤),
    let hLN := InterpolationTransport.compatible_mass_lt a e he L y (by linarith only [hyL])
    let ν := (AffineFibre.normalizedMeasure μ w h0 htop).map (InterpolationTransport.inclusion a L ((e+a : ℕ)+1) hLN)
    let H := fun x : AffineSimplex.chartDomain (a+1) ((e+a : ℕ)+1) => β.val • hessianMatrix Ht x.val
    IsProbabilityMeasure ν ∧
    ∀ frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a),
    ∃ Q : ScalarFormData ν, IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
      InterpolationCoefficientBounds.IsIntrinsicFibreForm a L _ hLN frame ν Q ∧
    ∀ i₀ : Fin (a+1), |(i₀.val : ℝ)+1-(a+1 : ℝ)/2| ≤ (a+1 : ℝ)/4 →
    ∀ χ : BoundedL2Pairings.boundedSubmodule ν,
      (∃! ψ : Fin (a+1) → Q.1,WeightedWeakSolution Q H (zeroSumComponents (Fin (a+1)))
        (fun i => if i = i₀ then χ.val else 0) ψ) ∧
      ∀ ψ : Fin (a+1) → Q.1,
        WeightedWeakSolution Q H (zeroSumComponents (Fin (a+1)))
          (fun i => if i = i₀ then χ.val else 0) ψ →
        let B := (eLpNorm (χ.val : AffineSimplex.chartDomain (a+1) ((e+a : ℕ)+1) → ℝ) ∞ ν).toReal
        (∑ j,InteractionDifferential.boundaryWeight s.val a.succPNat j*‖(ψ j).val‖) ≤
          C*(a+1 : ℝ)^(κ*ε-1/2)*(‖χ.val‖+Real.exp (-c*(a+1 : ℝ)^δ)*B) ∧
        (∑ j,‖(ψ j).val‖) ≤ C*(a+1 : ℝ)^(κ*ε)*(‖χ.val‖+Real.exp (-c*(a+1 : ℝ)^δ)*B) := by
  obtain ⟨A,K,εbase,hA,hK,hεbase,hlocal⟩ := InterpolantLocalLaws.local_laws hRig s.val
    (by linarith [s.property]) (ne_of_gt s.property)
  obtain ⟨Ce,κe,hCe,hκe,hentry⟩ := InterpolationCoefficientBounds.interaction_entry_internal s.val K
    (by linarith [s.property]) (by linarith)
  let q := max (s.val+2) (max (4*K) κe)
  have hq : 0 ≤ q := by dsimp only [q]; have := s.property; positivity
  obtain ⟨κ,hκ,hdec⟩ := short_fixed_length_from_coefficients_internal s q hq
  refine ⟨A,K,min εbase (1/16),κ+1,hA,hK,lt_min hεbase (by norm_num),by linarith,?_⟩
  intro ε hε hεsmall
  have hsmall := hεsmall.trans_le (min_le_left εbase (1/16))
  have hσε : min s.val 1/2+2*ε < 1 := by
    rw [min_eq_right s.property.le]
    have hh := hεsmall.trans_le (min_le_right εbase (1/16))
    linarith
  obtain ⟨δ,hδ,hlocal⟩ := hlocal ε hε hsmall
  obtain ⟨ne,hne,hentry⟩ := hentry ε hε.le hσε
  obtain ⟨ns,Cs,hns,hCs,hsquare⟩ := InterpolationCoefficientBounds.interaction_square_internal s.val ε
    (by linarith [s.property]) hε.le hσε
  let n0 := max ne ns
  refine ⟨δ,hδ,?_⟩
  intro βlo βhi hlo hle θ
  obtain ⟨T0,c,hT0,hc,hlocal⟩ := hlocal βlo βhi hlo hle θ
  obtain ⟨F,hF,hshort⟩ := InterpolationCoercivity.short_range_entry_internal θ
  obtain ⟨Fs,hFs,hforcing⟩ := InterpolationCoercivity.forcing_sq_le_weight θ s.val (by linarith [s.property])
  let P0 := 2+βlo⁻¹+βhi*(1+F+Ce)
  have hpos : 0 ≤ βhi*(1+F+Ce) := by have := hlo.trans_le hle; positivity
  have hP0 : 1 ≤ P0 := by dsimp only [P0]; linarith [inv_pos.mpr hlo]
  have hPlo : P0⁻¹ ≤ βlo := (inv_le_comm₀ (by linarith : 0 < P0) hlo).mpr (by
    dsimp only [P0]; linarith)
  have hPhi : βhi*(1+F+Ce) ≤ P0 := by dsimp only [P0]; linarith [inv_pos.mpr hlo]
  let E0 := 2*βhi^2*(Cs+Fs)
  have hE0 : 0 ≤ E0 := by dsimp only [E0]; positivity
  obtain ⟨C,hC,hdec⟩ := hdec ε hε P0 E0 T0 Cs c δ hP0 hE0 hT0.le hc hδ n0
  refine ⟨C,c/16,hC,by positivity,?_⟩
  intro β hβ a e f ha he hf hef hsize hpower y z L hyL hzL hy hz Y Z Dy Dz
  obtain ⟨Ky,hKy,hky,_⟩ := InterpolationCoercivity.assembled_energy_realization (ofShort β s) e a (by omega) y
  obtain ⟨Kz,hKz,hkz,_⟩ := InterpolationCoercivity.assembled_energy_realization (ofShort β s) f a (by omega) z
  refine ⟨Ky,Kz,hKy,hKz,hky,hkz,?_⟩
  intro t ht Ht μ w
  let hLN := InterpolationTransport.compatible_mass_lt a e he L y (by linarith only [hyL])
  obtain ⟨h0,htop,hprob,hforms⟩ := InterpolationCoefficientBounds.physical_form_internal (ofShort β s) θ ε
    e f a he hf y z L hyL hzL Ky Kz hky hkz ((e+a : ℕ)+1) rfl hLN t ht
  refine ⟨h0,htop,?_⟩
  intro _ ν H
  refine ⟨hprob,?_⟩
  let : IsProbabilityMeasure ν := hprob
  have hn : (0 : ℝ) < a+1 := by positivity
  have hn1 : (1 : ℝ) ≤ a+1 := by have := Nat.cast_nonneg a (α := ℝ); linarith
  have hsupp : ∀ᵐ x ∂ν,x.val ∈ AffineSimplex.massSimplex a L := by
    rw [(InterpolationTransport.measurableEmbedding_inclusion a L _ hLN).ae_map_iff]
    exact ae_of_all _ (fun u => u.property)
  have hsm (u) (hu : u ∈ AffineSimplex.massSimplex a L) :
      ContDiffAt ℝ ∞ Ky u ∧ ContDiffAt ℝ ∞ Kz u := by
    exact ⟨hKy.contDiffAt (((PhysicalEnergy.isOpen_gapAmbientDomain _).preimage
      (RetainedSimplex.continuous_assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val)).mem_nhds
        (InterpolationCoefficientBounds.fibre_mem_internal e a y L hyL hu)),
      hKz.contDiffAt (((PhysicalEnergy.isOpen_gapAmbientDomain _).preimage
      (RetainedSimplex.continuous_assemble f a (InterpolatingDensities.exteriorPermutation f a) z.val)).mem_nhds
        (InterpolationCoefficientBounds.fibre_mem_internal f a z L hzL hu))⟩
  have hHt (u) (hu : u ∈ AffineSimplex.massSimplex a L) : ContDiffAt ℝ ∞ Ht u :=
    ((InterpolationCoercivity.forcing_smooth θ (Real.rpow_pos_of_pos hn (-ε)) hu.1).add
      (contDiffAt_const.mul (hsm u hu).1)).add (contDiffAt_const.mul (hsm u hu).2)
  have hsym (u) (hu : u ∈ AffineSimplex.massSimplex a L) (i j : Fin (a+1)) :
      hessianMatrix Ht u i j = hessianMatrix Ht u j i := by
    simp only [Intrinsic.hessianMatrix_eq_second (hHt u hu)]
    exact (hHt u hu).isSymmSndFDerivAt (by simp) _ _
  have hcurv := InterpolationCoefficientBounds.coercivity_internal (ofShort β s) θ ε hε.le e f a ha y z L
    hyL hzL Ky Kz hky hkz t ht
  have hb : min 1 (s.val*(s.val+1)) = 1 := min_eq_left (by nlinarith only [s.property])
  change ∀ u ∈ AffineSimplex.massSimplex a L,∀ v : EuclideanSpace ℝ (Fin (a+1)),
    min 1 (s.val*(s.val+1))*(a+1 : ℝ)^(-(s.val+2)*ε)*(∑ i,(v i)^2) ≤
      ∑ i,∑ j,v i*hessianMatrix Ht u i j*v j at hcurv
  rw [hb,one_mul] at hcurv
  have hHm (i j : Fin (a+1)) : Measurable (fun x => H x i j) :=
    ((DifferentiatedPoisson.measurable_hessian_entries (V := Ht) i j).comp measurable_subtype_coe).const_mul β.val
  obtain ⟨hHp,hlow⟩ := short_mass_curvature_internal s a L _ ν hsupp Ht β.val P0 q ε
    β.property hP0 (hPlo.trans hβ.1) hε.le (le_max_left _ _) hsym hcurv
  have hcoeff : (n0 : ℝ) ≤ (a+1 : ℝ) →
      ∃ (M : AffineSimplex.chartDomain (a+1) ((e+a : ℕ)+1) → Matrix (Fin (a+1)) (Fin (a+1)) ℝ)
        (G : Set (AffineSimplex.chartDomain (a+1) ((e+a : ℕ)+1)))
        (W : AffineSimplex.chartDomain (a+1) ((e+a : ℕ)+1) → ℝ),
        SummableCoerciveMatrix (ρ := ν) s a.succPNat ε P0 q
          (Sum.inl ⟨fun i => (i.val : ℤ),fun _ _ h => Fin.ext (Int.ofNat_inj.mp h)⟩) M ∧
        MeasurableSet G ∧ (∀ᵐ x ∂ν,x ∈ G → H x = M x) ∧ IntegrableOn W Gᶜ ν ∧
        (∀ᵐ x ∂ν.restrict Gᶜ,1 ≤ W x) ∧
        (∀ᵐ x ∂ν.restrict Gᶜ,∀ i j,H x i j^2 ≤ E0*(a+1 : ℝ)^Cs*W x) ∧
        (∫ x in Gᶜ,W x ∂ν) ≤ T0*Real.exp (-c*(a+1 : ℝ)^δ) := by
    intro hlarge
    have hn0 : n0 ≤ a+1 := by exact_mod_cast hlarge
    have hne' : ne ≤ a+1 := (le_max_left _ _).trans hn0
    have hns' : ns ≤ a+1 := (le_max_right _ _).trans hn0
    let GA := {u : EuclideanSpace ℝ (Fin (a+1)) |
      WithLp.ofLp u ∈ goodBlockEvent s.val a.succPNat (e+a).succPNat (K*ε)}
    let G : Set (AffineSimplex.chartDomain (a+1) ((e+a : ℕ)+1)) := Subtype.val ⁻¹' GA
    let W := fun x : AffineSimplex.chartDomain (a+1) ((e+a : ℕ)+1) =>
      InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s.val (WithLp.ofLp x.val)
    let M := fun x : AffineSimplex.chartDomain (a+1) ((e+a : ℕ)+1) =>
      β.val • (if x.val ∈ GA then hessianMatrix Ht x.val else (1 : Matrix (Fin (a+1)) (Fin (a+1)) ℝ))
    have hGA : MeasurableSet GA := (InterpolantLocalLaws.measurableSet_goodBlockEvent _ _ _ _).preimage
      (WithLp.measurable_ofLp 2 _)
    have hG : MeasurableSet G := hGA.preimage measurable_subtype_coe
    let Gf := AffineSimplex.massSimplex a L ∩ GA
    have hpentry := hshort a ε (K*ε) (κe*ε) s.val Ce t hε.le (by have := hK; positivity)
      (by positivity) s.property hCe.le Gf Ky Kz
      (fun u hu i => by simpa only [Nat.succPNat_coe,Nat.cast_succ] using (hu.2.2.1 i).1)
      (fun u hu => hsm u hu.1)
      (fun u hu i j => hentry (ofShort β s) rfl e f a hef hne' hsize y z hy.1 hz.1 u
        (hyL ▸ hu.1) (hzL ▸ hu.1) hu.2 Ky Kz hky hkz t ht i j)
    have hq1 : max (4*(K*ε)) (κe*ε) ≤ q*ε := by
      apply max_le
      · have h := (le_max_left (4*K) κe).trans (le_max_right (s.val+2) (max (4*K) κe)); nlinarith only [h,hε]
      · have h := (le_max_right (4*K) κe).trans (le_max_right (s.val+2) (max (4*K) κe)); nlinarith only [h,hε]
    have hentries := short_cutoff_entry_enlarge_internal a L GA Gf rfl Ht β.val P0 (1+F+Ce)
      (max (4*(K*ε)) (κe*ε)) (q*ε) s.val β.property.le (by positivity)
      ((mul_le_mul_of_nonneg_right hβ.2 (by positivity : 0 ≤ 1+F+Ce)).trans hPhi) hq1 hpentry
    have hMbound : SummableCoerciveMatrix (ρ := ν) s a.succPNat ε P0 q
        (Sum.inl ⟨fun i => (i.val : ℤ),fun _ _ h => Fin.ext (Int.ofNat_inj.mp h)⟩) M :=
      short_scaled_cutoff_matrix_internal s a L _ ν hsupp Ht GA hGA β.val P0 q ε hP0
        (mul_nonneg hq hε.le) (hPlo.trans hβ.1) hsym hlow
        (hsupp.mono fun x hx i j => hentries x.val hx i j)
    have heq : ∀ᵐ x ∂ν,x ∈ G → H x = M x := ae_of_all _ (fun x hx => by
      change x.val ∈ GA at hx
      dsimp only [M,H]; rw [ite_eq_left hx])
    have hWmeas : Measurable W := InterpolantLocalLaws.measurable_exceptionalWeight s.val (n := a.succPNat)
      (fun x : AffineSimplex.chartDomain (a+1) ((e+a : ℕ)+1) => WithLp.ofLp x.val) (fun i => (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable.comp measurable_subtype_coe)
    have hW1 : ∀ x,1 ≤ W x := fun x => InterpolantLocalLaws.one_le_exceptionalWeight s.val _
      (fun i => (x.property.1 i).le)
    obtain ⟨h0',ht',_hprob',htail,_⟩ :=
      (hlocal (ofShort β s) rfl hβ.1 hβ.2 e f a he hf ha hsize hef (by simpa only [Nat.cast_succ] using hpower)).2 L y z
        (by linarith) (by linarith) hy hz t ht.1 ht.2
    have hw : w = (fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal (Real.exp (-β.val*
        ((∑ k,(θ.val ((a+1 : ℝ)^(-ε)*u.val k)+θ.val ((a+1 : ℝ)^(-ε)*(u.val k)⁻¹)))+
          (1-t)*physicalAmbientGapEnergy (ofShort β s) (e+a).succPNat
            ⟨Y u.val,InterpolationCoefficientBounds.fibre_mem_internal e a y L hyL u.property⟩+
          t*physicalAmbientGapEnergy (ofShort β s) (f+a).succPNat
            ⟨Z u.val,InterpolationCoefficientBounds.fibre_mem_internal f a z L hzL u.property⟩)))) := by
      funext u
      dsimp only [w,Ht]
      rw [hky u.val (InterpolationCoefficientBounds.fibre_mem_internal e a y L hyL u.property),
        hkz u.val (InterpolationCoefficientBounds.fibre_mem_internal f a z L hzL u.property)]
    have htail' : (∫⁻ x in Gᶜ,ENNReal.ofReal (W x) ∂ν) ≤
        ENNReal.ofReal (T0*Real.exp (-c*(a+1 : ℝ)^δ)) := by
      change (∫⁻ x in {x : AffineSimplex.chartDomain (a+1) ((e+a : ℕ)+1) | x.val ∈ GAᶜ},
        ENNReal.ofReal (InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s.val (WithLp.ofLp x.val))
        ∂(AffineFibre.normalizedMeasure μ w h0 htop).map (InterpolationTransport.inclusion a L _ hLN)) ≤ _
      rw [InterpolationTransport.lintegral_inclusion a L _ hLN
        (AffineFibre.normalizedMeasure μ w h0 htop) GAᶜ
        (fun u : EuclideanSpace ℝ (Fin (a+1)) => ENNReal.ofReal
          (InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s.val (WithLp.ofLp u)))]
      simpa only [AffineFibre.normalizedMeasure_eq_smul,hw,Nat.cast_succ,ofShort,μ,Y,Z,GA,compl_ofPred] using htail
    have hWi : IntegrableOn W Gᶜ ν := ⟨hWmeas.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => zero_le_one.trans (hW1 x))).mpr
        (htail'.trans_lt ENNReal.ofReal_lt_top)⟩
    have htailR : (∫ x in Gᶜ,W x ∂ν) ≤ T0*Real.exp (-c*(a+1 : ℝ)^δ) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hWi (ae_of_all _ fun x => zero_le_one.trans (hW1 x))] at htail'
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp htail'
    refine ⟨M,G,W,hMbound,hG,heq,hWi,ae_of_all _ hW1,?_,htailR⟩
    filter_upwards [ae_restrict_of_ae hsupp] with x hx i j
    have hi := hsquare (ofShort β s) rfl e f a hns' hsize (by omega) y z hy.1 hz.1 L hyL hzL
      Ky Kz hky hkz t ht x.val hx i j
    have hp := hforcing a ε hε.le x.val hx.1 i j
    have hW0 : 0 ≤ W x := zero_le_one.trans (hW1 x)
    have hpow : 1 ≤ (a+1 : ℝ)^Cs := Real.one_le_rpow hn1 hCs.le
    have hsplit := InterpolationCoercivity.interpolant_hessian_internal θ
      (Real.rpow_pos_of_pos hn (-ε)) hx.1 (hsm x.val hx).1 (hsm x.val hx).2 (t := t) i j
    change (β.val*hessianMatrix Ht x.val i j)^2 ≤ _
    rw [hsplit]
    simpa only [E0,add_comm Cs Fs] using short_add_square_envelope_internal β.val βhi
      _ _ Fs Cs ((a+1 : ℝ)^Cs) (W x) β.property.le hβ.2 hFs.le hCs.le hpow hW0
        (by simpa only [sq_abs] using hp) (by simpa only [sq_abs] using hi)
  intro frame
  obtain ⟨Q,hQ,hcons,hcert⟩ := hforms frame
  refine ⟨Q,hQ,hcons,hcert,?_⟩
  intro i₀ hi₀ χ
  have ha0 : 0 < P0⁻¹*(a+1 : ℝ)^(-(q*ε)) := by positivity
  refine ⟨MatrixEnergy.weightedWeakSolution_existsUnique Q hQ H (zeroSumComponents (Fin (a+1))) hHp
    _ ha0 (hlow.mono fun x hx v _ => hx v) hHm _,?_⟩
  intro ψ hψ B
  have hh := hdec a.succPNat _ ν Q hQ hcons H hHm hHp
    (by simpa only [Nat.succPNat_coe,Nat.cast_succ] using hlow) i₀
    (by simpa only [Nat.succPNat_coe,Nat.cast_succ] using hi₀) χ ψ hψ
    (by simpa only [Nat.succPNat_coe,Nat.cast_succ] using hcoeff)
  simp only [Nat.succPNat_coe,Nat.cast_succ] at hh
  constructor
  · apply hh.1.trans
    gcongr
    nlinarith only [hε]
  · apply hh.2.trans
    gcongr
    nlinarith only [hε]

end Riesz2.FixedLengthDecay
