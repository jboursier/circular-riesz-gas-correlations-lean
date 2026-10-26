/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.FixedLengthDecayPart4
public import Riesz2.Thermodynamic.FixedLengthBoundedOperator
public import Riesz2.Thermodynamic.InterpolationTransport
public import Riesz2.Thermodynamic.InterpolationBoundaryBridge

/-!
# Fixed-length comparison on the actual natural domain

Internal composition for Lemma 6.4. The coefficient envelope is needed only almost
everywhere for the included mass-fibre law. Bounded auxiliary tuples and their exact
mean corrections are placed in the physical natural domain before the tangent comparison
is applied.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical MatrixOrder ENNReal ContDiff

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.FixedLengthDecay

section Representatives

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- See Lemma 6.4 of the paper: a bounded scalar class is bounded almost
everywhere by its finite essential norm, including the zero class. -/
theorem bounded_ae_essentialNorm_internal (f : BoundedL2Pairings.boundedSubmodule ν) :
    ∀ᵐ x ∂ν, |f.val x| ≤ (eLpNorm (f.val : X → ℝ) ∞ ν).toReal := by
  simpa only [Real.norm_eq_abs, ← toReal_eLpNorm] using
    ae_le_lpNorm_exponent_top (BoundedL2Pairings.memLp_top f)

/-- See Lemma 6.4 of the paper: the actual scalar tuple, its mean correction,
and the physical tangent solution all have representatives in the same
unrestricted natural energy space. No projection of a natural domain is
assumed. The tangent solution needs no essential bound in this lemma. -/
theorem natural_representatives_internal (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (n : ℕ+)
    (H : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (hHm : ∀ i j, Measurable (fun x => H x i j))
    (hH : ∀ᵐ x ∂ν, (H x).PosSemidef)
    (hHi : ∀ i j, Integrable (fun x => H x i j) ν)
    (f : Fin (n : ℕ) → Lp ℝ 2 ν) (ψ v : Fin (n : ℕ) → Q.1)
    (hψ : WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ))) f ψ)
    (V : ℝ) (hv : ∀ i, ∀ᵐ x ∂ν, |(v i).val x| ≤ V) :
    ∃ Ψ vN rN : MatrixEnergy.Natural Q hQ H ⊤ hH,
      MatrixEnergy.tuple Q hQ H ⊤ hH Ψ = ψ ∧
      MatrixEnergy.tuple Q hQ H ⊤ hH vN = v ∧
      (∀ i, MatrixEnergy.tuple Q hQ H ⊤ hH rN i = (n : ℝ)⁻¹ • ∑ j, v j) ∧
      (∀ᵐ x ∂ν, |((n : ℝ)⁻¹ • ∑ j, v j : Q.1).val x| ≤ V) ∧
      ‖MatrixEnergy.values Q hQ H ⊤ hH rN‖ =
        (n : ℝ) ^ (-(1 : ℝ) / 2) * ‖(∑ j, v j : Q.1).val‖ := by
  have hψtop : WeightedFormDomain Q H ⊤ ψ :=
    ⟨ae_of_all _ (fun _ => Submodule.mem_top), hψ.1.2⟩
  have hvdom := bounded_tuple_physical_domain_internal Q H hHi v V hv
  have hr := normal_component_bound_internal Q n v V hv
  have hrdom := bounded_tuple_physical_domain_internal Q H hHi
    (fun _ : Fin (n : ℕ) => (n : ℝ)⁻¹ • ∑ j, v j) V (fun _ => hr)
  obtain ⟨Ψ, hΨ⟩ := MatrixEnergy.exists_tuple Q hQ H ⊤ hH hHm ψ hψtop
  obtain ⟨vN, hvN⟩ := MatrixEnergy.exists_tuple Q hQ H ⊤ hH hHm v hvdom
  obtain ⟨rN, hrN⟩ := MatrixEnergy.exists_tuple Q hQ H ⊤ hH hHm _ hrdom
  refine ⟨Ψ, vN, rN, hΨ, hvN, fun i => congrFun hrN i, hr, ?_⟩
  have he : MatrixEnergy.values Q hQ H ⊤ hH rN =
      WithLp.toLp 2 (fun _ : Fin (n : ℕ) => ((n : ℝ)⁻¹ • ∑ j, v j : Q.1).val) := by
    apply PiLp.ext
    intro i
    rw [MatrixEnergy.values_apply, congrFun hrN i]
  rw [he]
  exact normal_value_norm Q n (∑ j, v j)

/-- See Lemma 6.4 of the paper: the actual tangent test `v-r-psi` is bounded
by twice the auxiliary bound plus the physical bound. This is proved for
the natural-domain tuple, so its bounded L² class can be used in the native
point and signed-increment perturbation estimates. -/
theorem comparison_test_bound_internal (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (n : ℕ+)
    (H : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (hH : ∀ᵐ x ∂ν, (H x).PosSemidef)
    (ψ v r : MatrixEnergy.Natural Q hQ H ⊤ hH)
    (hr : ∀ i, MatrixEnergy.tuple Q hQ H ⊤ hH r i =
      (n : ℝ)⁻¹ • ∑ j, MatrixEnergy.tuple Q hQ H ⊤ hH v j)
    (U V : ℝ)
    (hψ : ∀ i, ∀ᵐ x ∂ν, |(MatrixEnergy.tuple Q hQ H ⊤ hH ψ i).val x| ≤ U)
    (hv : ∀ i, ∀ᵐ x ∂ν, |(MatrixEnergy.tuple Q hQ H ⊤ hH v i).val x| ≤ V) :
    ∀ i, ∀ᵐ x ∂ν, |(MatrixEnergy.tuple Q hQ H ⊤ hH (v-r-ψ) i).val x| ≤ 2*V+U := by
  have hrb := normal_component_bound_internal Q n
    (MatrixEnergy.tuple Q hQ H ⊤ hH v) V hv
  intro i
  have he : (MatrixEnergy.tuple Q hQ H ⊤ hH (v-r-ψ) i).val =
      (MatrixEnergy.tuple Q hQ H ⊤ hH v i).val -
        ((n : ℝ)⁻¹ • ∑ j, MatrixEnergy.tuple Q hQ H ⊤ hH v j : Q.1).val -
        (MatrixEnergy.tuple Q hQ H ⊤ hH ψ i).val := by
    simp only [map_sub, Pi.sub_apply, hr, Submodule.coe_sub]
  rw [he]
  filter_upwards [hv i, hrb, hψ i,
    Lp.coeFn_sub (MatrixEnergy.tuple Q hQ H ⊤ hH v i).val
      ((n : ℝ)⁻¹ • ∑ j, MatrixEnergy.tuple Q hQ H ⊤ hH v j : Q.1).val,
    Lp.coeFn_sub
      ((MatrixEnergy.tuple Q hQ H ⊤ hH v i).val -
        ((n : ℝ)⁻¹ • ∑ j, MatrixEnergy.tuple Q hQ H ⊤ hH v j : Q.1).val)
      (MatrixEnergy.tuple Q hQ H ⊤ hH ψ i).val] with x hvx hrx hψx hsub₁ hsub₂
  simp only [hsub₂, Pi.sub_apply, hsub₁]
  exact (abs_sub _ _).trans ((add_le_add ((abs_sub _ _).trans (add_le_add hvx hrx)) hψx).trans_eq
    (by ring))

end Representatives

section Coefficients

variable (β : InverseTemperature) (s : Riesz1.RieszExponent)
  (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (m : ℕ+) (hm : 2 ≤ (m : ℕ))
  (hnm : (n : ℕ) ≤ (m : ℕ)) (k : ℕ)
  (θ : PhysicalCutoff) (ε η t : ℝ)
  (ν : Measure (AffineSimplex.chartDomain n ((n+d : ℕ)+1)))
  (P : AffineSimplex.chartDomain n ((n+d : ℕ)+1) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)

local notation "H" => fun x : AffineSimplex.chartDomain n ((n+d : ℕ)+1) =>
  β.val • (InterpolationMatrix.penaltyHessian n θ ε (Subtype.val x) + P x)
local notation "Y" => InterpolationMatrix.multiplicationPart β s n d e hde m hm hnm k θ ε η t P

end Coefficients

section Tail

end Tail

section NativeTests

variable (β : InverseTemperature) (s : Riesz1.RieszExponent)
  (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (m : ℕ+) (hm : 2 ≤ (m : ℕ))
  (hnm : (n : ℕ) ≤ (m : ℕ)) (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ (m : ℕ)/4)
  (θ : PhysicalCutoff) (ε η t : ℝ)
  (ν : Measure (AffineSimplex.chartDomain n ((n+d : ℕ)+1)))
  (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
  (P : AffineSimplex.chartDomain n ((n+d : ℕ)+1) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)

local notation "Y" => InterpolationMatrix.multiplicationPart β s n d e hde m hm hnm k θ ε η t P
local notation "Bnd" => BoundedL2Pairings.boundedSubmodule ν
local notation "ess" => fun f : Bnd => ENNReal.toReal (eLpNorm (fun x => (Subtype.val f) x) ∞ ν)
local notation "w" => InteractionDifferential.boundaryWeight s.val n
local notation "depth" => fun i : Fin (n : ℕ) => (min (Fin.val i+1) ((n : ℕ)-Fin.val i) : ℕ)

/-- See Subsection 6.1 of the paper, supporting Lemma 6.4: the native point and
signed-increment estimates give the actual multiplication-plus-resolvent
row bounds on bounded L² classes. Integrability witnesses are retained,
and the original beta squared in each Schur pairing is unchanged. -/
theorem native_row_bounds_internal (A Err : ℝ)
    (htests : ∀ (φ ψ : Bnd) (i j l : Fin (n : ℕ)),
      ∃ hp : Integrable (matrixFieldPair Y (Pi.single j φ.val) (Pi.single i ψ.val)) ν,
      ∃ hd : Integrable (matrixFieldPair Y (Pi.single j φ.val)
        (fun a => (Pi.single i ψ.val : Fin (n : ℕ) → Lp ℝ 2 ν) a -
          (Pi.single l ψ.val : Fin (n : ℕ) → Lp ℝ 2 ν) a)) ν,
      |InterpolationMatrix.perturbationPair β s n d e hde m hm hnm k hk hkm θ ε η t
        ν Q hQ P (Pi.single j φ.val) (Pi.single i ψ.val) hp| ≤
        A*w j*w i*‖φ.val‖*‖ψ.val‖ + Err*ess φ*ess ψ ∧
      |InterpolationMatrix.perturbationPair β s n d e hde m hm hnm k hk hkm θ ε η t
        ν Q hQ P (Pi.single j φ.val)
        (fun a => (Pi.single i ψ.val : Fin (n : ℕ) → Lp ℝ 2 ν) a -
          (Pi.single l ψ.val : Fin (n : ℕ) → Lp ℝ 2 ν) a) hd| ≤
        A*w j*(Nat.dist i.val l.val : ℝ)*(min (depth i : ℝ) (depth l : ℝ))^(-1-s.val/2)*
          ‖φ.val‖*‖ψ.val‖ + Err*ess φ*ess ψ) :
    (∀ (φ ψ : Bnd) (j i : Fin (n : ℕ)),
      |(∫ x, φ.val x*Y x j i*ψ.val x ∂ν) +
        InterpolationMatrix.schurPointPair ν Q hQ s β m hm k hk hkm n φ.val ψ.val
          (j.castLE hnm) (i.castLE hnm)| ≤ A*w j*w i*‖φ.val‖*‖ψ.val‖ + Err*ess φ*ess ψ) ∧
    (∀ (φ ψ : Bnd) (j i l : Fin (n : ℕ)),
      |(∫ x, φ.val x*ψ.val x*(Y x j i-Y x j l) ∂ν) +
        InterpolationMatrix.schurIncrementPair ν Q hQ s β m hm k hk hkm n φ.val ψ.val
          (j.castLE hnm) (i.castLE hnm) (l.castLE hnm)| ≤
        A*w j*(Nat.dist i.val l.val : ℝ)*(min (depth i : ℝ) (depth l : ℝ))^(-1-s.val/2)*
          ‖φ.val‖*‖ψ.val‖ + Err*ess φ*ess ψ) := by
  constructor
  · intro φ ψ j i
    obtain ⟨hp, hd, hpoint, _⟩ := htests φ ψ i j i
    rw [InterpolationPerturbation.perturbation_point_eq_internal] at hpoint
    have he : (fun x => φ.val x*ψ.val x*Y x j i) = (fun x => φ.val x*Y x j i*ψ.val x) := by
      funext x
      ring
    rwa [he] at hpoint
  · intro φ ψ j i l
    obtain ⟨hp, hd, _, hinc⟩ := htests φ ψ i j l
    rwa [InterpolationPerturbation.perturbation_increment_eq_internal] at hinc

end NativeTests

section LongComparison

variable (β : InverseTemperature) (s : Riesz1.RieszExponent)
  (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (m : ℕ+) (hm : 2 ≤ (m : ℕ))
  (hnm : 2*(n : ℕ) ≤ (m : ℕ)) (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ (m : ℕ)/4)
  (θ : PhysicalCutoff) (ε η t : ℝ)
  (ν : Measure (AffineSimplex.chartDomain n ((n+d : ℕ)+1)))
  (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
  (P : AffineSimplex.chartDomain n ((n+d : ℕ)+1) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)

local notation "H" => fun x : AffineSimplex.chartDomain n ((n+d : ℕ)+1) =>
  β.val • (InterpolationMatrix.penaltyHessian n θ ε (Subtype.val x) + P x)
local notation "M" => InterpolationMatrix.matrix β s n d e hde m hm (by omega) k θ ε η t
local notation "Y" => InterpolationMatrix.multiplicationPart β s n d e hde m hm (by omega) k θ ε η t P
local notation "Bnd" => BoundedL2Pairings.boundedSubmodule ν
local notation "ess" => fun f : Bnd => ENNReal.toReal (eLpNorm (fun x => (Subtype.val f) x) ∞ ν)
local notation "w" => InteractionDifferential.boundaryWeight s.val n
local notation "depth" => fun i : Fin (n : ℕ) => (min (Fin.val i+1) ((n : ℕ)-Fin.val i) : ℕ)

/-- See Lemma 6.4 of the paper: long-range physical comparison from the native
coefficient and auxiliary conclusions. This internal implication constructs
all three natural representatives, applies the maximum principle to the
physical field, and instantiates column cancellation with the actual bounded
test. Its normal-energy term is derived from the same native point bound,
rather than assumed. No normal-row bound for the physical matrix is needed. -/
theorem long_comparison_from_native_bounds_internal
    (C κ γ : ℝ) (hC : 1 ≤ C)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm k C κ γ η M)
    (hPm : ∀ i j, Measurable (fun x => P x i j))
    (hH : ∀ᵐ x ∂ν, (H x).PosSemidef)
    (hHi : ∀ i j, Integrable (fun x => H x i j) ν)
    (hYi : ∀ i j, Integrable (fun x => Y x i j) ν)
    (a : ℝ) (ha : 0 < a)
    (hlower : ∀ᵐ x ∂ν, ∀ z : Fin (n : ℕ) → ℝ,
      a*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*H x i j*z j)
    (i₀ : Fin (n : ℕ)) (hi₀ : |(i₀.val : ℝ)+1-(n : ℝ)/2| ≤ (n : ℝ)/4)
    (χ : Lp ℝ 2 ν) (B V D A Err : ℝ)
    (hB : 0 ≤ B) (hV : 0 ≤ V) (hD : 0 ≤ D) (hA : 0 ≤ A) (hErr : 0 ≤ Err)
    (hχ : ∀ᵐ x ∂ν, |χ x| ≤ B)
    (ψ v : Fin (n : ℕ) → Q.1)
    (hψ : WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ)))
      (fun i => if i = i₀ then χ else 0) ψ)
    (hv : ∀ i, ∀ᵐ x ∂ν, |(v i).val x| ≤ V)
    (hvalue : ∀ i, ‖(v i).val‖ ≤ D*(1+(Nat.dist i.val i₀.val : ℝ))^(s.val-2)*‖χ‖)
    (hsum : ‖(∑ i, v i : Q.1).val‖ ≤ D*(n : ℝ)^(-(1-s.val))*‖χ‖)
    (haux : ∀ z : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ,
      SchurRestriction.schurForm Q hQ n m (by omega) s hm k C κ γ η β.val hC β.property M hM
        ((MatrixEnergy.vectorEquiv Q hQ).symm v) z =
          inner ℝ (WithLp.toLp 2 (fun i => if i = i₀ then χ else 0))
            (OperatorSchur.vectorValues Q hQ z))
    (hpoint : ∀ (φ ζ : Bnd) (j i : Fin (n : ℕ)),
      |(∫ x, φ.val x*Y x j i*ζ.val x ∂ν) +
        InterpolationMatrix.schurPointPair ν Q hQ s β m hm k hk hkm n φ.val ζ.val
          (j.castLE (by omega)) (i.castLE (by omega))| ≤ A*w j*w i*‖φ.val‖*‖ζ.val‖ + Err*ess φ*ess ζ)
    (hinc : ∀ (φ ζ : Bnd) (j i l : Fin (n : ℕ)),
      |(∫ x, φ.val x*ζ.val x*(Y x j i-Y x j l) ∂ν) +
        InterpolationMatrix.schurIncrementPair ν Q hQ s β m hm k hk hkm n φ.val ζ.val
          (j.castLE (by omega)) (i.castLE (by omega)) (l.castLE (by omega))| ≤
        A*w j*(Nat.dist i.val l.val : ℝ)*(min (depth i : ℝ) (depth l : ℝ))^(-1-s.val/2)*
          ‖φ.val‖*‖ζ.val‖ + Err*ess φ*ess ζ) :
    let S : Q.1 := ∑ i, v i
    let U := 2*V+a⁻¹*B
    let K := 2*8^(2-s.val)*(2/(1-s.val/2)) +
      8^(1+s.val/2)*(2/s.val) + 4^(s.val/2)
    let L := (K*Real.sqrt (2/(1-s.val)))*A*D*‖χ‖*(n : ℝ)^(-(1 : ℝ)/2)
    let τ := 3*(n : ℝ)^2*(Err*U*V)
    let R := (n : ℝ)⁻¹*Q.2 S S +
      ((β.val*(C*(1+1/s.val)*(2/(1-s.val))))*(n : ℝ)^(κ*η)*(n : ℝ)^(2-s.val) +
        A*(∑ j, w j)^2)*‖((n : ℝ)⁻¹ • S).val‖^2 + (n : ℝ)^2*Err*V^2
    ‖WithLp.toLp 2 (fun i => (ψ i).val-(v i).val)‖ ≤
      2*L/a + Real.sqrt ((2*τ+R)/a) + (n : ℝ)^(-(1 : ℝ)/2)*‖S.val‖ := by
  intro S U K L τ R
  have hHm : ∀ i j, Measurable (fun x => H x i j) := fun i j =>
    (((InterpolationMatrix.measurable_penaltyHessian n θ ε i j).comp measurable_subtype_coe).add
      (hPm i j)).const_mul β.val
  have hHa : ∀ᵐ x ∂ν, (∀ i j, H x i j = H x j i) ∧
      ∀ z : Fin (n : ℕ) → ℝ, a*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*H x i j*z j := by
    filter_upwards [hH, hlower] with x hx hl
    refine ⟨?_, hl⟩
    intro i j
    have ht : Matrix.transpose (H x) = H x := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hx.isHermitian.eq
    exact congrFun (congrFun ht j) i
  have hψb := (point_source_ae_bound_internal Q hQ H hHm a ha hHa
    (zeroSumComponents (Fin (n : ℕ))) i₀ χ B hB hχ ψ hψ).2
  obtain ⟨Ψ,vN,rN,hΨ,hvN,hrN,hrb,hrnorm⟩ := natural_representatives_internal Q hQ n H
    hHm hH hHi (fun i => if i = i₀ then χ else 0) ψ v hψ V hv
  have hψN : WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ)))
      (fun i => if i = i₀ then χ else 0) (MatrixEnergy.tuple Q hQ H ⊤ hH Ψ) := by
    rwa [hΨ]
  have hrmean : ∀ i, MatrixEnergy.tuple Q hQ H ⊤ hH rN i =
      (n : ℝ)⁻¹ • ∑ j, MatrixEnergy.tuple Q hQ H ⊤ hH vN j := by
    simpa only [hvN] using hrN
  have hvNb : ∀ i, ∀ᵐ x ∂ν, |(MatrixEnergy.tuple Q hQ H ⊤ hH vN i).val x| ≤ V := by
    simpa only [hvN] using hv
  have htest := comparison_test_bound_internal Q hQ n H hH Ψ vN rN hrmean (a⁻¹*B) V
    (by simpa only [hΨ] using hψb) hvNb
  let f : Bnd := ⟨((n : ℝ)⁻¹ • S).val, V, hrb⟩
  have hfp : ∀ j i : Fin (n : ℕ),
      |(∫ x, f.val x*Y x j i*f.val x ∂ν) +
        InterpolationMatrix.schurPointPair ν Q hQ s β m hm k hk hkm n f.val f.val
          (j.castLE (by omega)) (i.castLE (by omega))| ≤ A*w j*w i*‖f.val‖^2+Err*V^2 := by
    intro j i
    have he := BoundedL2Pairings.essentialNorm_le f V hV hrb
    have hsq : ess f*ess f ≤ V*V :=
      mul_le_mul he he ENNReal.toReal_nonneg hV
    have hh := (hpoint f f j i).trans (add_le_add le_rfl
      (show Err*ess f*ess f ≤ Err*V^2 by nlinarith [mul_le_mul_of_nonneg_left hsq hErr]))
    convert hh using 1; ring
  have hrenergy : MatrixEnergy.weakForm Q hQ H ⊤ hH rN rN ≤ R := by
    exact physical_long_normal_energy_internal β s n d e hde m hm (by omega) k hk hkm
      θ ε η t ν Q hQ P C κ γ hC hM hH hYi S rN hrN A Err V hrb hfp
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hK : 0 ≤ K := by
    have hs := s.property.1
    have hs1 : 0 < 1-s.val/2 := by linarith [s.property.2]
    dsimp only [K]
    positivity
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hτ : 0 ≤ τ := by dsimp only [τ]; positivity
  have hR : 0 ≤ R := (MatrixEnergy.weakForm_nonneg Q hQ H ⊤ hH rN).trans hrenergy
  have hauxN : ∀ z : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ,
      SchurRestriction.schurForm Q hQ n m (by omega) s hm k C κ γ η β.val hC β.property M hM
        (MatrixEnergy.base (ι := Fin (n : ℕ)) (κ := Fin (n : ℕ))
          (MatrixEnergy.vectorValue Q hQ) (fun x => CFC.sqrt (H x)) ⊤ vN) z =
        inner ℝ (WithLp.toLp 2 (fun i => if i = i₀ then χ else 0))
          (OperatorSchur.vectorValues Q hQ z) := by
    have hb : MatrixEnergy.base (ι := Fin (n : ℕ)) (κ := Fin (n : ℕ))
        (MatrixEnergy.vectorValue Q hQ) (fun x => CFC.sqrt (H x)) ⊤ vN =
        (MatrixEnergy.vectorEquiv Q hQ).symm v :=
      (MatrixEnergy.vectorEquiv Q hQ).injective (hvN.trans
        ((MatrixEnergy.vectorEquiv Q hQ).apply_symm_apply v).symm)
    simpa only [hb] using haux
  have hcompare := fixed_exterior_tangent_comparison_internal β s n d e hde m hm (by omega)
    k hk hkm θ ε η t ν Q hQ P C κ γ hC hM hH a ha hlower
      (fun i => if i = i₀ then χ else 0) Ψ vN rN hψN hrmean hauxN L τ R hL hτ hR hrenergy
  have hpert : ∀ hint : Integrable (matrixFieldPair Y
      (fun i => (MatrixEnergy.tuple Q hQ H ⊤ hH (vN-rN-Ψ) i).val)
      (fun i => (MatrixEnergy.tuple Q hQ H ⊤ hH vN i).val)) ν,
      |InterpolationMatrix.perturbationPair β s n d e hde m hm (by omega) k hk hkm θ ε η t
        ν Q hQ P (fun i => (MatrixEnergy.tuple Q hQ H ⊤ hH (vN-rN-Ψ) i).val)
          (fun i => (MatrixEnergy.tuple Q hQ H ⊤ hH vN i).val) hint| ≤
        L*‖WithLp.toLp 2 (fun i => (MatrixEnergy.tuple Q hQ H ⊤ hH (vN-rN-Ψ) i).val)‖+τ := by
    let u : Fin (n : ℕ) → Bnd := fun i =>
      ⟨(MatrixEnergy.tuple Q hQ H ⊤ hH (vN-rN-Ψ) i).val, U, htest i⟩
    let vB : Fin (n : ℕ) → Bnd := fun i => ⟨(v i).val, V, hv i⟩
    obtain ⟨hint,hp⟩ := native_long_perturbation_pairing_internal β s n d e hde m hm hnm
      k hk hkm θ ε η t ν Q hQ P hYi u vB i₀ hi₀ D ‖χ‖ A Err U V hD
        (norm_nonneg _) hA hErr hU hV htest hv hvalue
        (by simpa only [Submodule.coe_sum] using hsum)
        (fun j i ζ => hpoint (u j) ζ j i) (fun j i l ζ => hinc (u j) ζ j i l)
    intro hint'
    simpa only [u, vB, hvN, L, τ, K] using hp
  have hc := hcompare hpert
  have he : MatrixEnergy.values Q hQ H ⊤ hH (Ψ-vN) =
      WithLp.toLp 2 (fun i => (ψ i).val-(v i).val) := by
    apply PiLp.ext
    intro i
    change (MatrixEnergy.tuple Q hQ H ⊤ hH (Ψ-vN) i).val = _
    simp only [map_sub, Pi.sub_apply, Submodule.coe_sub, hΨ, hvN]
  rwa [he, hrnorm] at hc

/-- The probability-law comparison in Lemma 6.4, using the full
pairing theorem of Lemma 5.17 on the actual bounded-input
operator. The normal energy still uses the native point estimate. The
exceptional polynomial records both coordinate-to-vector conversions. -/
theorem long_comparison_from_column_subtraction_internal [IsProbabilityMeasure ν]
    (hn : 2 ≤ (n : ℕ)) (c δ : ℝ)
    (C κ γ : ℝ) (hC : 1 ≤ C)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm k C κ γ η M)
    (hPm : ∀ i j, Measurable (fun x => P x i j))
    (hH : ∀ᵐ x ∂ν, (H x).PosSemidef)
    (hHi : ∀ i j, Integrable (fun x => H x i j) ν)
    (hYi : ∀ i j, Integrable (fun x => Y x i j) ν)
    (a : ℝ) (ha : 0 < a)
    (hlower : ∀ᵐ x ∂ν, ∀ z : Fin (n : ℕ) → ℝ,
      a*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*H x i j*z j)
    (i₀ : Fin (n : ℕ)) (hi₀ : |(i₀.val : ℝ)+1-(n : ℝ)/2| ≤ (n : ℝ)/4)
    (χ : Lp ℝ 2 ν) (B V D A Err : ℝ)
    (hErrEq : Err = A*Real.exp (-c*(n : ℝ)^δ))
    (hB : 0 ≤ B) (hV : 0 ≤ V) (hD : 0 ≤ D) (hA : 0 ≤ A) (hErr : 0 ≤ Err)
    (hχ : ∀ᵐ x ∂ν, |χ x| ≤ B)
    (ψ v : Fin (n : ℕ) → Q.1)
    (hψ : WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ)))
      (fun i => if i = i₀ then χ else 0) ψ)
    (hv : ∀ i, ∀ᵐ x ∂ν, |(v i).val x| ≤ V)
    (hvalue : ∀ i, ‖(v i).val‖ ≤ D*(1+(Nat.dist i.val i₀.val : ℝ))^(s.val-2)*‖χ‖)
    (hsum : ‖(∑ i, v i : Q.1).val‖ ≤ D*(n : ℝ)^(-(1-s.val))*‖χ‖)
    (haux : ∀ z : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ,
      SchurRestriction.schurForm Q hQ n m (by omega) s hm k C κ γ η β.val hC β.property M hM
        ((MatrixEnergy.vectorEquiv Q hQ).symm v) z =
          inner ℝ (WithLp.toLp 2 (fun i => if i = i₀ then χ else 0))
            (OperatorSchur.vectorValues Q hQ z))
    (hpoint : ∀ (φ ζ : Bnd) (j i : Fin (n : ℕ)),
      |(∫ x, φ.val x*Y x j i*ζ.val x ∂ν) +
        InterpolationMatrix.schurPointPair ν Q hQ s β m hm k hk hkm n φ.val ζ.val
          (j.castLE (by omega)) (i.castLE (by omega))| ≤ A*w j*w i*‖φ.val‖*‖ζ.val‖ + Err*ess φ*ess ζ)
    (hinc : ∀ (φ ζ : Bnd) (j i l : Fin (n : ℕ)),
      |(∫ x, φ.val x*ζ.val x*(Y x j i-Y x j l) ∂ν) +
        InterpolationMatrix.schurIncrementPair ν Q hQ s β m hm k hk hkm n φ.val ζ.val
          (j.castLE (by omega)) (i.castLE (by omega)) (l.castLE (by omega))| ≤
        A*w j*(Nat.dist i.val l.val : ℝ)*(min (depth i : ℝ) (depth l : ℝ))^(-1-s.val/2)*
          ‖φ.val‖*‖ζ.val‖ + Err*ess φ*ess ζ) :
    let S : Q.1 := ∑ i, v i
    let U := 2*V+a⁻¹*B
    let K := ColumnSubtraction.sourceConstant s
    let L := (K*Real.sqrt (2/(1-s.val)))*A*D*‖χ‖*(n : ℝ)^(-(1 : ℝ)/2)
    let τ := 3*A*(n : ℝ)^(9/2 : ℝ)*Real.exp (-c*(n : ℝ)^δ)*U*V
    let R := (n : ℝ)⁻¹*Q.2 S S +
      ((β.val*(C*(1+1/s.val)*(2/(1-s.val))))*(n : ℝ)^(κ*η)*(n : ℝ)^(2-s.val) +
        A*(∑ j, w j)^2)*‖((n : ℝ)⁻¹ • S).val‖^2 + (n : ℝ)^2*Err*V^2
    ‖WithLp.toLp 2 (fun i => (ψ i).val-(v i).val)‖ ≤
      2*L/a + Real.sqrt ((2*τ+R)/a) + (n : ℝ)^(-(1 : ℝ)/2)*‖S.val‖ := by
  intro S U K L τ R
  have hHm : ∀ i j, Measurable (fun x => H x i j) := fun i j =>
    (((InterpolationMatrix.measurable_penaltyHessian n θ ε i j).comp measurable_subtype_coe).add
      (hPm i j)).const_mul β.val
  have hHa : ∀ᵐ x ∂ν, (∀ i j, H x i j = H x j i) ∧
      ∀ z : Fin (n : ℕ) → ℝ, a*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*H x i j*z j := by
    filter_upwards [hH, hlower] with x hx hl
    refine ⟨?_, hl⟩
    intro i j
    have ht : Matrix.transpose (H x) = H x := by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hx.isHermitian.eq
    exact congrFun (congrFun ht j) i
  have hψb := (point_source_ae_bound_internal Q hQ H hHm a ha hHa
    (zeroSumComponents (Fin (n : ℕ))) i₀ χ B hB hχ ψ hψ).2
  obtain ⟨Ψ,vN,rN,hΨ,hvN,hrN,hrb,hrnorm⟩ := natural_representatives_internal Q hQ n H
    hHm hH hHi (fun i => if i = i₀ then χ else 0) ψ v hψ V hv
  have hψN : WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ)))
      (fun i => if i = i₀ then χ else 0) (MatrixEnergy.tuple Q hQ H ⊤ hH Ψ) := by
    rwa [hΨ]
  have hrmean : ∀ i, MatrixEnergy.tuple Q hQ H ⊤ hH rN i =
      (n : ℝ)⁻¹ • ∑ j, MatrixEnergy.tuple Q hQ H ⊤ hH vN j := by
    simpa only [hvN] using hrN
  have hvNb : ∀ i, ∀ᵐ x ∂ν, |(MatrixEnergy.tuple Q hQ H ⊤ hH vN i).val x| ≤ V := by
    simpa only [hvN] using hv
  have htest := comparison_test_bound_internal Q hQ n H hH Ψ vN rN hrmean (a⁻¹*B) V
    (by simpa only [hΨ] using hψb) hvNb
  let f : Bnd := ⟨((n : ℝ)⁻¹ • S).val, V, hrb⟩
  have hfp : ∀ j i : Fin (n : ℕ),
      |(∫ x, f.val x*Y x j i*f.val x ∂ν) +
        InterpolationMatrix.schurPointPair ν Q hQ s β m hm k hk hkm n f.val f.val
          (j.castLE (by omega)) (i.castLE (by omega))| ≤ A*w j*w i*‖f.val‖^2+Err*V^2 := by
    intro j i
    have he := BoundedL2Pairings.essentialNorm_le f V hV hrb
    have hsq : ess f*ess f ≤ V*V :=
      mul_le_mul he he ENNReal.toReal_nonneg hV
    have hh := (hpoint f f j i).trans (add_le_add le_rfl
      (show Err*ess f*ess f ≤ Err*V^2 by nlinarith [mul_le_mul_of_nonneg_left hsq hErr]))
    convert hh using 1; ring
  have hrenergy : MatrixEnergy.weakForm Q hQ H ⊤ hH rN rN ≤ R := by
    exact physical_long_normal_energy_internal β s n d e hde m hm (by omega) k hk hkm
      θ ε η t ν Q hQ P C κ γ hC hM hH hYi S rN hrN A Err V hrb hfp
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hK : 0 ≤ K := (ColumnSubtraction.sourceConstant_pos s).le
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hτ : 0 ≤ τ := by dsimp only [τ]; positivity
  have hR : 0 ≤ R := (MatrixEnergy.weakForm_nonneg Q hQ H ⊤ hH rN).trans hrenergy
  have hauxN : ∀ z : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ,
      SchurRestriction.schurForm Q hQ n m (by omega) s hm k C κ γ η β.val hC β.property M hM
        (MatrixEnergy.base (ι := Fin (n : ℕ)) (κ := Fin (n : ℕ))
          (MatrixEnergy.vectorValue Q hQ) (fun x => CFC.sqrt (H x)) ⊤ vN) z =
        inner ℝ (WithLp.toLp 2 (fun i => if i = i₀ then χ else 0))
          (OperatorSchur.vectorValues Q hQ z) := by
    have hb : MatrixEnergy.base (ι := Fin (n : ℕ)) (κ := Fin (n : ℕ))
        (MatrixEnergy.vectorValue Q hQ) (fun x => CFC.sqrt (H x)) ⊤ vN =
        (MatrixEnergy.vectorEquiv Q hQ).symm v :=
      (MatrixEnergy.vectorEquiv Q hQ).injective (hvN.trans
        ((MatrixEnergy.vectorEquiv Q hQ).apply_symm_apply v).symm)
    simpa only [hb] using haux
  have hcompare := fixed_exterior_tangent_comparison_internal β s n d e hde m hm (by omega)
    k hk hkm θ ε η t ν Q hQ P C κ γ hC hM hH a ha hlower
      (fun i => if i = i₀ then χ else 0) Ψ vN rN hψN hrmean hauxN L τ R hL hτ hR hrenergy
  have hpert : ∀ hint : Integrable (matrixFieldPair Y
      (fun i => (MatrixEnergy.tuple Q hQ H ⊤ hH (vN-rN-Ψ) i).val)
      (fun i => (MatrixEnergy.tuple Q hQ H ⊤ hH vN i).val)) ν,
      |InterpolationMatrix.perturbationPair β s n d e hde m hm (by omega) k hk hkm θ ε η t
        ν Q hQ P (fun i => (MatrixEnergy.tuple Q hQ H ⊤ hH (vN-rN-Ψ) i).val)
          (fun i => (MatrixEnergy.tuple Q hQ H ⊤ hH vN i).val) hint| ≤
        L*‖WithLp.toLp 2 (fun i => (MatrixEnergy.tuple Q hQ H ⊤ hH (vN-rN-Ψ) i).val)‖+τ := by
    let u : Fin (n : ℕ) → Bnd := fun i =>
      ⟨(MatrixEnergy.tuple Q hQ H ⊤ hH (vN-rN-Ψ) i).val, U, htest i⟩
    let vB : Fin (n : ℕ) → Bnd := fun i => ⟨(v i).val, V, hv i⟩
    have hOp := fixedLength_operator_bounds_internal β s n d e hde m hm (by omega)
      k hk hkm θ ε η t ν Q hQ P hYi A c δ
      (by simpa only [hErrEq] using hpoint) (by simpa only [hErrEq] using hinc)
    have hdepth : (n : ℝ)/4 ≤ ((min (i₀.val+1) ((n : ℕ)-i₀.val) : ℕ) : ℝ) := by
      rw [Nat.cast_min,Nat.cast_add,Nat.cast_one,Nat.cast_sub (Nat.le_of_lt i₀.isLt)]
      obtain ⟨hil,hih⟩ := abs_le.mp hi₀
      exact le_min (by linarith) (by linarith)
    obtain ⟨hint,hp⟩ := fixedLength_column_subtraction_polynomial_internal β s n d e hde m hm
      (by omega) k hk hkm θ ε η t ν Q hQ P hYi hn A (D*‖χ‖) c δ hA
      (mul_nonneg hD (norm_nonneg _)) hOp i₀ hdepth vB
      (by simpa only [vB,show s.val-2 = -(2-s.val) by ring,mul_assoc,mul_comm,
        mul_left_comm] using hvalue)
      (by simpa only [Submodule.coe_sum,mul_assoc,mul_comm,mul_left_comm,vB] using hsum) u
    have hu := BoundedPerturbationOperator.field_norm_le u U hU htest
    have hvf := BoundedPerturbationOperator.field_norm_le vB V hV hv
    have herr : 3*A*(n : ℝ)^(5/2 : ℝ)*Real.exp (-c*(n : ℝ)^δ)*
        ‖BoundedPerturbationOperator.field u‖*‖BoundedPerturbationOperator.field vB‖ ≤ τ := by
      calc
        _ ≤ 3*A*(n : ℝ)^(5/2 : ℝ)*Real.exp (-c*(n : ℝ)^δ)*
            ((n : ℝ)*U)*((n : ℝ)*V) := by gcongr
        _ = τ := by
          dsimp only [τ]
          rw [show (9/2 : ℝ) = 5/2+1+1 by norm_num, Real.rpow_add (by positivity),
            Real.rpow_add (by positivity),Real.rpow_one]
          ring
    have hp' := hp.trans (add_le_add le_rfl herr)
    have hmain : A*ColumnSubtraction.sourceConstant s*(D*‖χ‖)*Real.sqrt (2/(1-s.val))*
        (n : ℝ)^(-(1/2 : ℝ)) = L := by
      dsimp only [L,K]
      simp only [neg_div]
      ring
    rw [hmain] at hp'
    intro hint'
    simpa only [u,vB,hvN] using hp'
  have hc := hcompare hpert
  have he : MatrixEnergy.values Q hQ H ⊤ hH (Ψ-vN) =
      WithLp.toLp 2 (fun i => (ψ i).val-(v i).val) := by
    apply PiLp.ext
    intro i
    change (MatrixEnergy.tuple Q hQ H ⊤ hH (Ψ-vN) i).val = _
    simp only [map_sub, Pi.sub_apply, Submodule.coe_sub, hΨ, hvN]
  rwa [he, hrnorm] at hc

end LongComparison

section PhysicalHessian

/-- See Lemma 6.4 of the paper, Subsection 6.1: arbitrary smooth
ambient realizations of the two actual endpoint energies have the literal
scaled ambient Hessian and the all-size curvature bound on the mass fibre.
Thus the endpoint realizations returned by the scalar-law construction can
be used directly. Equality is proved on open ambient neighborhoods, before
any restriction to tangent energies. -/
theorem physical_hessian_and_curvature_internal (p : Parameters) (θ : PhysicalCutoff)
    (ε : ℝ) (hε : 0 ≤ ε) (d e a : ℕ) (ha : 1 ≤ a)
    (y : AffineSimplex.chartDomain d ((d+a : ℕ)+1))
    (z : AffineSimplex.chartDomain e ((e+a : ℕ)+1)) (L : ℝ)
    (hyL : ((d+a : ℕ)+1 : ℝ)-∑ k, y.val k = L)
    (hzL : ((e+a : ℕ)+1 : ℝ)-∑ k, z.val k = L) :
    let Y := RetainedSimplex.assemble d a (InterpolatingDensities.exteriorPermutation d a) y.val
    let Z := RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) z.val
    let Dy := Y ⁻¹' gapAmbientDomain (d+a).succPNat
    let Dz := Z ⁻¹' gapAmbientDomain (e+a).succPNat
    ∀ Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ,
    ContDiffOn ℝ ∞ Ky Dy → ContDiffOn ℝ ∞ Kz Dz →
    (∀ x (hx : x ∈ Dy), Ky x = physicalAmbientGapEnergy p (d+a).succPNat ⟨Y x,hx⟩) →
    (∀ x (hx : x ∈ Dz), Kz x = physicalAmbientGapEnergy p (e+a).succPNat ⟨Z x,hx⟩) →
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ AffineSimplex.massSimplex a L,
    let Ht := fun u : EuclideanSpace ℝ (Fin (a+1)) =>
      (∑ k, (θ.val ((a+1 : ℝ)^(-ε)*u k) + θ.val ((a+1 : ℝ)^(-ε)*(u k)⁻¹))) +
        (1-t)*Ky u+t*Kz u
    let P := (1-t) • hessianMatrix Ky x + t • hessianMatrix Kz x
    let H := p.val.1 • (fun i j : Fin (a+1) => InterpolationMatrix.penaltyHessian (⟨a+1, by omega⟩ : ℕ+) θ ε x i j + P i j)
    hessianMatrix (fun u => p.val.1*Ht u) x = H ∧
    ∀ v : Fin (a+1) → ℝ,
      (p.val.1*min 1 (p.val.2*(p.val.2+1))*(a+1 : ℝ)^(-(p.val.2+2)*ε)) * (∑ i, v i^2) ≤
        ∑ i, ∑ j, v i*H i j*v j := by
  intro Y Z Dy Dz Ky Kz hKy hKz hky hkz t ht x hx Ht P H
  have hDy : IsOpen Dy := (PhysicalEnergy.isOpen_gapAmbientDomain _).preimage
    (InterpolantLocalLaws.contDiff_exterior_assembly d a y.val).continuous
  have hDz : IsOpen Dz := (PhysicalEnergy.isOpen_gapAmbientDomain _).preimage
    (InterpolantLocalLaws.contDiff_exterior_assembly e a z.val).continuous
  have hxDy : x ∈ Dy := PhysicalEnergy.simplex_subset_ambient _ _
    (InterpolantLocalLaws.assembled_physical_simplex d a y.val x y.property.1 hx.1 (by
      rw [hx.2, ← hyL]; push_cast; ring))
  have hxDz : x ∈ Dz := PhysicalEnergy.simplex_subset_ambient _ _
    (InterpolantLocalLaws.assembled_physical_simplex e a z.val x z.property.1 hx.1 (by
      rw [hx.2, ← hzL]; push_cast; ring))
  have hy := hKy.contDiffAt (hDy.mem_nhds hxDy)
  have hz := hKz.contDiffAt (hDz.mem_nhds hxDz)
  have hb : 0 < (a+1 : ℝ)^(-ε) := Real.rpow_pos_of_pos (by positivity) _
  have hHt : ContDiffAt ℝ ∞ Ht x :=
    ((InterpolationCoercivity.forcing_smooth θ hb hx.1).add
      (contDiffAt_const.mul hy)).add (contDiffAt_const.mul hz)
  have hmat : hessianMatrix Ht x = (fun i j : Fin (a+1) => InterpolationMatrix.penaltyHessian (⟨a+1, by omega⟩ : ℕ+) θ ε x i j + P i j) := by
    ext i j
    simpa only [Ht, P, InterpolationMatrix.penaltyHessian, PNat.mk_coe, Nat.cast_add, Nat.cast_one,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] using
      (InterpolationCoercivity.interpolant_hessian_internal (t := t) θ hb hx.1 hy hz i j)
  have hscaled : hessianMatrix (fun u => p.val.1*Ht u) x = p.val.1 • hessianMatrix Ht x := by
    ext i j
    rw [Intrinsic.hessianMatrix_eq_second (contDiffAt_const.mul hHt),
      PhysicalCollision.internal_hessian_const_mul (hHt.of_le (by simp)),
      ← Intrinsic.hessianMatrix_eq_second hHt]
    rfl
  refine ⟨hscaled.trans (congrArg (fun A => p.val.1 • A) hmat), ?_⟩
  obtain ⟨_,Ay,Az,_hAy,_hAz,hay,haz,hcoer⟩ :=
    InterpolationCoercivity.physical_interpolant_coercivity p θ ε hε d e a ha y z L hyL hzL
  have hEq : EqOn Ht (fun u : EuclideanSpace ℝ (Fin (a+1)) =>
      (∑ k, (θ.val ((a+1 : ℝ)^(-ε)*u k) + θ.val ((a+1 : ℝ)^(-ε)*(u k)⁻¹))) +
        (1-t)*Ay u+t*Az u) (Dy ∩ Dz) := by
    intro u hu
    dsimp only [Ht]
    rw [hky u hu.1, hkz u hu.2, hay u hu.1, haz u hu.2]
  have hhe := InterpolationExceptional.hessian_eqOn_internal (hDy.inter hDz) hEq ⟨hxDy,hxDz⟩
  have hlow := (hcoer t ht x hx).2
  rw [← hhe, hmat] at hlow
  intro v
  have hh := mul_le_mul_of_nonneg_left (hlow (WithLp.toLp 2 v)) p.property.1.le
  simpa only [H, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_assoc,
    mul_left_comm, mul_comm] using hh

end PhysicalHessian

section WeakTransport

variable {X Z ι : Type} [MeasurableSpace X] [MeasurableSpace Z] [Fintype ι]
  (μ : Measure X) (f : X → Z) (hf : MeasurableEmbedding f) (Q : ScalarFormData μ)

local notation "Q'" => ScalarFormEmbedding.form μ f hf Q
local notation "e" => ScalarFormEmbedding.domainEquiv μ f hf Q
local notation "T" => ScalarFormEmbedding.pullback μ f hf

/-- See Lemma 6.4 of the paper: the full matrix-energy domain, including
its fixed component subspace and unbounded matrix energy, is preserved by
the actual scalar embedding. No coefficient bound or core restriction is
used. This applies equally to the unrestricted and tangent domains. -/
theorem weighted_domain_embedding_iff_internal (M : Z → Matrix ι ι ℝ)
    (S : Submodule ℝ (ι → ℝ)) (u : ι → Q'.1) :
    WeightedFormDomain Q' M S u ↔
      WeightedFormDomain Q (M ∘ f) S (fun i => e (u i)) := by
  have he := ae_all_iff.mpr (fun i : ι => ScalarFormEmbedding.pullback_ae μ f hf (u i).val)
  have hmem : (∀ᵐ y ∂μ.map f, (fun i => (u i).val y) ∈ S) ↔
      ∀ᵐ x ∂μ, (fun i => (e (u i)).val x) ∈ S := by
    rw [hf.ae_map_iff]
    apply Filter.eventually_congr
    filter_upwards [he] with x hx
    have hh : (fun i => (e (u i)).val x) = (fun i => (u i).val (f x)) := by
      funext i
      exact hx i
    rw [hh]
  exact and_congr hmem (InterpolationTransport.matrixFieldPair_integrable_iff μ f hf ι M
    (fun i => (u i).val) (fun i => (u i).val))

end WeakTransport

end Riesz2.FixedLengthDecay
