/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.FixedLengthDecayLong

/-!
# Full column-subtraction comparison on the physical fibre

Probability-specific comparison and rate bookkeeping for Lemma 6.4, using the whole
bounded-input operator of Lemma 5.17.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Classical MatrixOrder ENNReal ContDiff
set_option backward.isDefEq.respectTransparency false
namespace Riesz2.FixedLengthDecay

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

/-- The squared comparison of Lemma 6.4 from the full pairing in
Lemma 5.17. The explicit absorption coefficient is chosen
uniformly before the volume in its physical application. -/
theorem column_subtraction_square_internal [IsProbabilityMeasure ν]
    (hn2 : 2 ≤ (n : ℕ))
    (C κ γ : ℝ) (hC : 1 ≤ C)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm k C κ γ η M)
    (hPm : ∀ i j, Measurable (fun x => P x i j))
    (hH : ∀ᵐ x ∂ν, (H x).PosSemidef)
    (hHi : ∀ i j, Integrable (fun x => H x i j) ν)
    (hYi : ∀ i j, Integrable (fun x => Y x i j) ν)
    (loss a0 D0 V0 A0 βhi c δ Ka : ℝ)
    (hKa : 0 ≤ Ka)
    (habsorb : (n : ℝ)^(loss+5/2)*Real.exp (-c*(n : ℝ)^δ) ≤
      Ka*Real.exp (-(c/2)*(n : ℝ)^δ))
    (hloss : 0 ≤ loss) (ha0 : 0 < a0) (hD0 : 0 ≤ D0)
    (hV0 : 0 ≤ V0) (hA0 : 0 ≤ A0)
    (hβhi : β.val ≤ βhi) (hκloss : κ*η ≤ loss)
    (hlower : ∀ᵐ x ∂ν, ∀ z : Fin (n : ℕ) → ℝ,
      (a0*(n : ℝ)^(-loss))*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*H x i j*z j)
    (i₀ : Fin (n : ℕ)) (hi₀ : |(i₀.val : ℝ)+1-(n : ℝ)/2| ≤ (n : ℝ)/4)
    (χ : Lp ℝ 2 ν) (B : ℝ) (hB : 0 ≤ B)
    (hχ : ∀ᵐ x ∂ν, |χ x| ≤ B)
    (ψ v : Fin (n : ℕ) → Q.1)
    (hψ : WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ)))
      (fun i => if i = i₀ then χ else 0) ψ)
    (hv : ∀ i, ∀ᵐ x ∂ν, |(v i).val x| ≤ V0*(n : ℝ)^loss*B)
    (hvalue : ∀ i, ‖(v i).val‖ ≤ (D0*(n : ℝ)^loss)*(1+(Nat.dist i.val i₀.val : ℝ))^(s.val-2)*‖χ‖)
    (hsum : ‖(∑ i, v i : Q.1).val‖ ≤ (D0*(n : ℝ)^loss)*(n : ℝ)^(-(1-s.val))*‖χ‖)
    (hgrad : Real.sqrt (Q.2 (∑ i, v i) (∑ i, v i)) ≤
      D0*(n : ℝ)^(loss-(1-s.val)/2)*‖χ‖)
    (haux : ∀ z : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ,
      SchurRestriction.schurForm Q hQ n m (by omega) s hm k C κ γ η β.val hC β.property M hM
        ((MatrixEnergy.vectorEquiv Q hQ).symm v) z =
          inner ℝ (WithLp.toLp 2 (fun i => if i = i₀ then χ else 0))
            (OperatorSchur.vectorValues Q hQ z))
    (hpoint : ∀ (φ ζ : Bnd) (j i : Fin (n : ℕ)),
      |(∫ x, φ.val x*Y x j i*ζ.val x ∂ν) +
        InterpolationMatrix.schurPointPair ν Q hQ s β m hm k hk hkm n φ.val ζ.val
          (j.castLE (by omega)) (i.castLE (by omega))| ≤ (A0*(n : ℝ)^loss)*w j*w i*‖φ.val‖*‖ζ.val‖ + (A0*(n : ℝ)^loss*Real.exp (-c*(n : ℝ)^δ))*ess φ*ess ζ)
    (hinc : ∀ (φ ζ : Bnd) (j i l : Fin (n : ℕ)),
      |(∫ x, φ.val x*ζ.val x*(Y x j i-Y x j l) ∂ν) +
        InterpolationMatrix.schurIncrementPair ν Q hQ s β m hm k hk hkm n φ.val ζ.val
          (j.castLE (by omega)) (i.castLE (by omega)) (l.castLE (by omega))| ≤
        (A0*(n : ℝ)^loss)*w j*(Nat.dist i.val l.val : ℝ)*(min (depth i : ℝ) (depth l : ℝ))^(-1-s.val/2)*
          ‖φ.val‖*‖ζ.val‖ + (A0*(n : ℝ)^loss*Real.exp (-c*(n : ℝ)^δ))*ess φ*ess ζ) :
    let K := 2*8^(2-s.val)*(2/(1-s.val/2)) +
      8^(1+s.val/2)*(2/s.val) + 4^(s.val/2)
    let L0 := (K*Real.sqrt (2/(1-s.val)))*A0*D0
    let K0 := βhi*(C*(1+1/s.val)*(2/(1-s.val))) + A0*(2/(1-s.val/2))^2
    ‖WithLp.toLp 2 (fun i => (ψ i).val-(v i).val)‖^2 ≤
      (3*((2*L0/a0)^2+(1+K0)*D0^2/a0+D0^2))*(n : ℝ)^(8*loss-1)*‖χ‖^2 +
      (9*(3*(A0*Ka)*(2*V0+a0⁻¹)*V0+(A0*Ka)*V0^2)/a0)*
        (n : ℝ)^(2+4*loss)*Real.exp (-(c/2)*(n : ℝ)^δ)*B^2 := by
  intro K L0 K0
  have hn : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have ha : 0 < a0*(n : ℝ)^(-loss) := by positivity
  have hC0 : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1).trans hC
  have hβ0 : 0 ≤ βhi := β.property.le.trans hβhi
  have hK : 0 ≤ K := by
    have hs := s.property.1
    have hs1 : 0 < 1-s.val/2 := by linarith [s.property.2]
    dsimp only [K]; positivity
  have hL0 : 0 ≤ L0 := by dsimp only [L0]; positivity
  have hK0 : 0 ≤ K0 := by
    have hs := s.property.1
    have hs1 : 0 < 1-s.val := sub_pos.mpr s.property.2
    dsimp only [K0]; positivity
  let S : Q.1 := ∑ i, v i
  let V := V0*(n : ℝ)^loss*B
  let D := D0*(n : ℝ)^loss
  let A := A0*(n : ℝ)^loss
  let Err := A0*(n : ℝ)^loss*Real.exp (-c*(n : ℝ)^δ)
  let a := a0*(n : ℝ)^(-loss)
  let L := (K*Real.sqrt (2/(1-s.val)))*A*D*‖χ‖*(n : ℝ)^(-(1 : ℝ)/2)
  let τ := 3*A*(n : ℝ)^(9/2 : ℝ)*Real.exp (-c*(n : ℝ)^δ)*(2*V+a⁻¹*B)*V
  let R := (n : ℝ)⁻¹*Q.2 S S +
    ((β.val*(C*(1+1/s.val)*(2/(1-s.val))))*(n : ℝ)^(κ*η)*(n : ℝ)^(2-s.val) +
      A*(∑ j, w j)^2)*‖((n : ℝ)⁻¹ • S).val‖^2 + (n : ℝ)^2*Err*V^2
  have hcomp := long_comparison_from_column_subtraction_internal β s n d e hde m hm hnm
    k hk hkm θ ε η t ν Q hQ P hn2 c δ C κ γ hC hM hPm hH hHi hYi a ha hlower
    i₀ hi₀ χ B V D A Err rfl hB (by dsimp [V]; positivity)
    (by dsimp [D]; positivity) (by dsimp [A]; positivity) (by dsimp [Err]; positivity)
    hχ ψ v hψ hv hvalue hsum haux hpoint hinc
  change ‖WithLp.toLp 2 (fun i => (ψ i).val-(v i).val)‖ ≤
    2*L/a+Real.sqrt ((2*τ+R)/a)+(n : ℝ)^(-(1 : ℝ)/2)*‖S.val‖ at hcomp
  have hm : ‖S.val‖ ≤ D0*(n : ℝ)^(loss-(1-s.val))*‖χ‖ := by
    apply hsum.trans_eq
    rw [show loss-(1-s.val) = loss+(-(1-s.val)) by ring, Real.rpow_add hn]
    ring
  have hLb : L ≤ L0*(n : ℝ)^(2*loss-1/2)*‖χ‖ := by
    apply le_of_eq
    dsimp only [L,L0,A,D]
    rw [show 2*loss-1/2 = (loss+loss)+(-(1 : ℝ)/2) by ring,
      Real.rpow_add hn,Real.rpow_add hn]
    ring
  have hinv : a⁻¹ = a0⁻¹*(n : ℝ)^loss := by
    dsimp only [a]
    rw [mul_inv, ←Real.rpow_neg hn.le, neg_neg]
  have herr : Err ≤ (A0*Ka)*Real.exp (-(c/2)*(n : ℝ)^δ) := by
    have hp : (n : ℝ)^loss ≤ (n : ℝ)^(loss+5/2) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have hh := (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le) hA0).trans
      (mul_le_mul_of_nonneg_left habsorb hA0)
    simpa only [Err,mul_assoc] using hh
  have hτb : τ ≤ 3*(n : ℝ)^2*((A0*Ka)*Real.exp (-(c/2)*(n : ℝ)^δ)*
      ((2*V0+a0⁻¹)*(n : ℝ)^loss*B)*(V0*(n : ℝ)^loss*B)) := by
    have hp : (n : ℝ)^(9/2 : ℝ) = (n : ℝ)^2*(n : ℝ)^(5/2 : ℝ) := by
      rw [← Real.rpow_natCast,← Real.rpow_add hn]
      norm_num
    have hh := mul_le_mul_of_nonneg_left habsorb
      (show 0 ≤ 3*(n : ℝ)^2*A0*((2*V0+a0⁻¹)*(n : ℝ)^loss*B)*(V0*(n : ℝ)^loss*B) by positivity)
    dsimp only [τ,A,V]
    rw [hinv,hp]
    rw [Real.rpow_add hn] at hh
    convert hh using 1 <;> ring
  have hRshape := long_normal_energy_shape_internal Q s n S R
    ((β.val*(C*(1+1/s.val)*(2/(1-s.val))))*(n : ℝ)^(κ*η)) A Err V
    (by dsimp [A]; positivity) le_rfl
  have hcoeff : (β.val*(C*(1+1/s.val)*(2/(1-s.val))))*(n : ℝ)^(κ*η) +
      A*(2/(1-s.val/2))^2 ≤ K0*(n : ℝ)^loss := by
    have hs : 0 < 1-s.val := sub_pos.mpr s.property.2
    have hsp := s.property.1
    dsimp only [A,K0]
    calc
      _ ≤ (βhi*(C*(1+1/s.val)*(2/(1-s.val))))*(n : ℝ)^loss +
          (A0*(n : ℝ)^loss)*(2/(1-s.val/2))^2 := by gcongr
      _ = _ := by ring
  have hRb : R ≤ (n : ℝ)⁻¹*Q.2 S S +
      K0*(n : ℝ)^loss*(n : ℝ)^(-s.val)*‖S.val‖^2 +
        (n : ℝ)^2*((A0*Ka)*Real.exp (-(c/2)*(n : ℝ)^δ))*(V0*(n : ℝ)^loss*B)^2 := by
    apply hRshape.trans
    exact add_le_add (add_le_add le_rfl (by gcongr)) (by gcongr)
  have hR : 0 ≤ R := by
    dsimp only [R]
    have hq := hQ.2.2.1 S
    have hβpos := β.property
    have hs := s.property.1
    have hs1 : 0 < 1-s.val := sub_pos.mpr s.property.2
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hErr : 0 ≤ Err := by dsimp [Err]; positivity
    positivity
  exact long_comparison_square_uniform_internal s loss a0 L0 K0 D0 V0 (A0*Ka) (c/2) δ
    hloss ha0 hL0 hK0 hD0 hV0 (mul_nonneg hA0 hKa) _ ν Q hQ n S ‖χ‖ B
    ‖WithLp.toLp 2 (fun i => (ψ i).val-(v i).val)‖ L τ R
    (norm_nonneg _) hB (norm_nonneg _) (by dsimp [L]; positivity)
    (by dsimp [τ,Err,V]; positivity) hR hm hgrad hLb hτb hRb hcomp


/-- Promote both coefficients to `(A0+E0) n^loss` in Lemma 6.4,
then use Lemma 5.17 and the physical squared comparison. -/
theorem column_subtraction_comparison_with_losses_internal [IsProbabilityMeasure ν]
    (hn2 : 2 ≤ (n : ℕ))
    (C κ γ : ℝ) (hC : 1 ≤ C)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm k C κ γ η M)
    (hPm : ∀ i j, Measurable (fun x => P x i j))
    (hH : ∀ᵐ x ∂ν, (H x).PosSemidef)
    (hHi : ∀ i j, Integrable (fun x => H x i j) ν)
    (hYi : ∀ i j, Integrable (fun x => Y x i j) ν)
    (loss auxloss rowloss a0 D0 V0 A0 E0 βhi c δ Ka : ℝ)
    (hKa : 0 ≤ Ka)
    (habsorb : (n : ℝ)^(loss+5/2)*Real.exp (-c*(n : ℝ)^δ) ≤
      Ka*Real.exp (-(c/2)*(n : ℝ)^δ))
    (hauxloss : auxloss ≤ loss) (hrowloss : rowloss ≤ loss)
    (hloss : 0 ≤ loss) (ha0 : 0 < a0) (hD0 : 0 ≤ D0)
    (hV0 : 0 ≤ V0) (hA0 : 0 ≤ A0) (hE0 : 0 ≤ E0)
    (hβhi : β.val ≤ βhi) (hκloss : κ*η ≤ loss)
    (hlower : ∀ᵐ x ∂ν, ∀ z : Fin (n : ℕ) → ℝ,
      (a0*(n : ℝ)^(-loss))*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*H x i j*z j)
    (i₀ : Fin (n : ℕ)) (hi₀ : |(i₀.val : ℝ)+1-(n : ℝ)/2| ≤ (n : ℝ)/4)
    (χ : Lp ℝ 2 ν) (B : ℝ) (hB : 0 ≤ B)
    (hχ : ∀ᵐ x ∂ν, |χ x| ≤ B)
    (ψ : Fin (n : ℕ) → Q.1)
    (v0 : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ)
    (hψ : WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ)))
      (fun i => if i = i₀ then χ else 0) ψ)
    (hv : ∀ i, ∀ᵐ x ∂ν, |((MatrixEnergy.vectorEquiv Q hQ v0) i).val x| ≤ V0*(n : ℝ)^auxloss*B)
    (hvalue : ∀ i, ‖((MatrixEnergy.vectorEquiv Q hQ v0) i).val‖ ≤ (D0*(n : ℝ)^auxloss)*(1+(Nat.dist i.val i₀.val : ℝ))^(s.val-2)*‖χ‖)
    (hsumnorm : (∑ i, ‖((MatrixEnergy.vectorEquiv Q hQ v0) i).val‖) ≤ D0*(n : ℝ)^auxloss*‖χ‖)
    (hsum : ‖(∑ i, (MatrixEnergy.vectorEquiv Q hQ v0) i : Q.1).val‖ ≤ D0*(n : ℝ)^(auxloss-(1-s.val))*‖χ‖)
    (hgrad : Real.sqrt (Q.2 (∑ i, (MatrixEnergy.vectorEquiv Q hQ v0) i) (∑ i, (MatrixEnergy.vectorEquiv Q hQ v0) i)) ≤
      D0*(n : ℝ)^(auxloss-(1-s.val)/2)*‖χ‖)
    (haux : ∀ z : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ,
      SchurRestriction.schurForm Q hQ n m (by omega) s hm k C κ γ η β.val hC β.property M hM
        v0 z =
          inner ℝ (WithLp.toLp 2 (fun i => if i = i₀ then χ else 0))
            (OperatorSchur.vectorValues Q hQ z))
    (hpoint : ∀ (φ ζ : Bnd) (j i : Fin (n : ℕ)),
      |(∫ x, φ.val x*Y x j i*ζ.val x ∂ν) +
        InterpolationMatrix.schurPointPair ν Q hQ s β m hm k hk hkm n φ.val ζ.val
          (j.castLE (by omega)) (i.castLE (by omega))| ≤ (A0*(n : ℝ)^rowloss)*w j*w i*‖φ.val‖*‖ζ.val‖ + (E0*Real.exp (-c*(n : ℝ)^δ))*ess φ*ess ζ)
    (hinc : ∀ (φ ζ : Bnd) (j i l : Fin (n : ℕ)),
      |(∫ x, φ.val x*ζ.val x*(Y x j i-Y x j l) ∂ν) +
        InterpolationMatrix.schurIncrementPair ν Q hQ s β m hm k hk hkm n φ.val ζ.val
          (j.castLE (by omega)) (i.castLE (by omega)) (l.castLE (by omega))| ≤
        (A0*(n : ℝ)^rowloss)*w j*(Nat.dist i.val l.val : ℝ)*(min (depth i : ℝ) (depth l : ℝ))^(-1-s.val/2)*
          ‖φ.val‖*‖ζ.val‖ + (E0*Real.exp (-c*(n : ℝ)^δ))*ess φ*ess ζ) :
    let K := 2*8^(2-s.val)*(2/(1-s.val/2)) +
      8^(1+s.val/2)*(2/s.val) + 4^(s.val/2)
    let L0 := (K*Real.sqrt (2/(1-s.val)))*(A0+E0)*D0
    let K0 := βhi*(C*(1+1/s.val)*(2/(1-s.val))) + (A0+E0)*(2/(1-s.val/2))^2
    (∀ i, ‖((MatrixEnergy.vectorEquiv Q hQ v0) i).val‖ ≤
      D0*(n : ℝ)^(4*loss)*(1+(Nat.dist i.val i₀.val : ℝ))^(s.val-2)*‖χ‖) ∧
    (∑ i, ‖((MatrixEnergy.vectorEquiv Q hQ v0) i).val‖) ≤ D0*(n : ℝ)^(4*loss)*‖χ‖ ∧
    ‖WithLp.toLp 2 (fun i => (ψ i).val-((MatrixEnergy.vectorEquiv Q hQ v0) i).val)‖^2 ≤
      (3*((2*L0/a0)^2+(1+K0)*D0^2/a0+D0^2))*(n : ℝ)^(8*loss-1)*‖χ‖^2 +
      (9*(3*((A0+E0)*Ka)*(2*V0+a0⁻¹)*V0+((A0+E0)*Ka)*V0^2)/a0)*
        (n : ℝ)^(2+4*loss)*Real.exp (-(c/2)*(n : ℝ)^δ)*B^2 := by
  intro K L0 K0
  let v := MatrixEnergy.vectorEquiv Q hQ v0
  have hn : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hfour : auxloss ≤ 4*loss := by linarith
  have hpower : (n : ℝ)^auxloss ≤ (n : ℝ)^loss :=
    Real.rpow_le_rpow_of_exponent_le hn1 hauxloss
  have hvalue' (i) : ‖(v i).val‖ ≤ (D0*(n : ℝ)^loss)*
      (1+(Nat.dist i.val i₀.val : ℝ))^(s.val-2)*‖χ‖ := by
    apply (hvalue i).trans
    gcongr
  have hsum' : ‖(∑ i, v i : Q.1).val‖ ≤ (D0*(n : ℝ)^loss)*(n : ℝ)^(-(1-s.val))*‖χ‖ := by
    have he : (n : ℝ)^(loss-(1-s.val)) = (n : ℝ)^loss*(n : ℝ)^(-(1-s.val)) := by
      rw [sub_eq_add_neg, Real.rpow_add hn]
    calc
      _ ≤ D0*(n : ℝ)^(loss-(1-s.val))*‖χ‖ := by apply hsum.trans; gcongr
      _ = _ := by rw [he]; ring
  have hgrad' : Real.sqrt (Q.2 (∑ i, v i) (∑ i, v i)) ≤
      D0*(n : ℝ)^(loss-(1-s.val)/2)*‖χ‖ := by apply hgrad.trans; gcongr
  have hv' (i) : ∀ᵐ x ∂ν, |(v i).val x| ≤ V0*(n : ℝ)^loss*B := by
    filter_upwards [hv i] with x hx
    apply hx.trans
    gcongr
  have hw (j : Fin (n : ℕ)) : 0 ≤ w j := (InteractionDifferential.boundaryWeight_pos s.val n j).le
  have hA : A0*(n : ℝ)^rowloss ≤ (A0+E0)*(n : ℝ)^loss := by
    calc
      _ ≤ A0*(n : ℝ)^loss := by gcongr
      _ ≤ _ := by gcongr; exact le_add_of_nonneg_right hE0
  have hE : E0 ≤ (A0+E0)*(n : ℝ)^loss := by
    calc
      _ ≤ A0+E0 := le_add_of_nonneg_left hA0
      _ ≤ _ := le_mul_of_one_le_right (add_nonneg hA0 hE0) (Real.one_le_rpow hn1 hloss)
  have hpoint' (φ ζ : Bnd) (j i : Fin (n : ℕ)) :=
    (hpoint φ ζ j i).trans (show _ ≤ ((A0+E0)*(n : ℝ)^loss)*w j*w i*‖φ.val‖*‖ζ.val‖ +
      ((A0+E0)*(n : ℝ)^loss*Real.exp (-c*(n : ℝ)^δ))*ess φ*ess ζ by
        gcongr <;> exact hw _)
  have hinc' (φ ζ : Bnd) (j i l : Fin (n : ℕ)) :=
    (hinc φ ζ j i l).trans (show _ ≤
      ((A0+E0)*(n : ℝ)^loss)*w j*(Nat.dist i.val l.val : ℝ)*(min (depth i : ℝ) (depth l : ℝ))^(-1-s.val/2)*
        ‖φ.val‖*‖ζ.val‖ + ((A0+E0)*(n : ℝ)^loss*Real.exp (-c*(n : ℝ)^δ))*ess φ*ess ζ by
        gcongr; exact hw _)
  refine ⟨?_,?_,?_⟩
  · intro i
    apply (hvalue i).trans
    gcongr
  · apply hsumnorm.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn1 hfour) hD0) (norm_nonneg _)
  · have haux' : ∀ z : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ,
        SchurRestriction.schurForm Q hQ n m (by omega) s hm k C κ γ η β.val hC β.property M hM
          ((MatrixEnergy.vectorEquiv Q hQ).symm (MatrixEnergy.vectorEquiv Q hQ v0)) z =
            inner ℝ (WithLp.toLp 2 (fun i => if i=i₀ then χ else 0))
              (OperatorSchur.vectorValues Q hQ z) := by
      simpa only [LinearEquiv.symm_apply_apply] using haux
    exact column_subtraction_square_internal β s n d e hde m hm hnm k hk hkm θ ε η t ν Q hQ P hn2
      C κ γ hC hM hPm hH hHi hYi loss a0 D0 V0 (A0+E0) βhi c δ Ka hKa habsorb
      hloss ha0 hD0 hV0 (add_nonneg hA0 hE0) hβhi hκloss hlower i₀ hi₀ χ B hB hχ ψ
      (MatrixEnergy.vectorEquiv Q hQ v0) hψ hv' hvalue' hsum' hgrad' haux' hpoint' hinc'

/-- The full pairing estimate of Lemma 5.17 in Lemma 6.4: obtain the actual auxiliary Schur inverse
and compare it on the same scalar form, retaining the entire original
auxiliary solvability and estimate certificate. -/
theorem column_subtraction_comparison_from_auxiliary_internal [IsProbabilityMeasure ν]
    (hn2 : 2 ≤ (n : ℕ))
    (C κ γ : ℝ) (hC : 1 ≤ C)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm k C κ γ η M)
    (hPm : ∀ i j, Measurable (fun x => P x i j))
    (hH : ∀ᵐ x ∂ν, (H x).PosSemidef)
    (hHi : ∀ i j, Integrable (fun x => H x i j) ν)
    (hYi : ∀ i j, Integrable (fun x => Y x i j) ν)
    (loss auxloss rowloss a0 D0 V0 A0 E0 βhi c δ Ka : ℝ)
    (hKa : 0 ≤ Ka)
    (habsorb : (n : ℝ)^(loss+5/2)*Real.exp (-c*(n : ℝ)^δ) ≤
      Ka*Real.exp (-(c/2)*(n : ℝ)^δ))
    (hauxloss : auxloss ≤ loss) (hrowloss : rowloss ≤ loss)
    (hloss : 0 ≤ loss) (ha0 : 0 < a0) (hD0 : 0 ≤ D0)
    (hV0 : 0 ≤ V0) (hA0 : 0 ≤ A0) (hE0 : 0 ≤ E0)
    (hβhi : β.val ≤ βhi) (hκloss : κ*η ≤ loss)
    (hlower : ∀ᵐ x ∂ν, ∀ z : Fin (n : ℕ) → ℝ,
      (a0*(n : ℝ)^(-loss))*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*H x i j*z j)
    (i₀ : Fin (n : ℕ)) (hi₀ : |(i₀.val : ℝ)+1-(n : ℝ)/2| ≤ (n : ℝ)/4)
    (χ : Lp ℝ 2 ν) (B : ℝ) (hB : 0 ≤ B)
    (hχ : ∀ᵐ x ∂ν, |χ x| ≤ B)
    (ψ : Fin (n : ℕ) → Q.1)
    (hψ : WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ)))
      (fun i => if i = i₀ then χ else 0) ψ)
    (hAux :
      (∃! v0 : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ,
        ∀ z, SchurRestriction.schurForm Q hQ n m (by omega) s hm k C κ γ η
          β.val hC β.property M hM v0 z =
            inner ℝ (WithLp.toLp 2 (fun i => if i=i₀ then χ else 0)) (OperatorSchur.vectorValues Q hQ z)) ∧
      ∀ v0 : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ,
        (∀ z, SchurRestriction.schurForm Q hQ n m (by omega) s hm k C κ γ η
          β.val hC β.property M hM v0 z =
            inner ℝ (WithLp.toLp 2 (fun i => if i=i₀ then χ else 0)) (OperatorSchur.vectorValues Q hQ z)) →
        let v := MatrixEnergy.vectorEquiv Q hQ v0
        (∀ j, ‖(v j).val‖ ≤ D0*(n : ℝ)^auxloss*(1+(Nat.dist j.val i₀.val : ℝ))^(s.val-2)*‖χ‖) ∧
        (∑ j, ‖(v j).val‖) ≤ D0*(n : ℝ)^auxloss*‖χ‖ ∧
        ‖(∑ j, v j : Q.1).val‖ ≤ D0*(n : ℝ)^(auxloss-(1-s.val))*‖χ‖ ∧
        Real.sqrt (Q.2 (∑ j, v j) (∑ j, v j)) ≤ D0*(n : ℝ)^(auxloss-(1-s.val)/2)*‖χ‖ ∧
        ∀ j, ∀ᵐ x ∂ν, |(v j).val x| ≤ V0*(n : ℝ)^auxloss*B)
    (hpoint : ∀ (φ ζ : Bnd) (j i : Fin (n : ℕ)),
      |(∫ x, φ.val x*Y x j i*ζ.val x ∂ν) +
        InterpolationMatrix.schurPointPair ν Q hQ s β m hm k hk hkm n φ.val ζ.val
          (j.castLE (by omega)) (i.castLE (by omega))| ≤ (A0*(n : ℝ)^rowloss)*w j*w i*‖φ.val‖*‖ζ.val‖ + (E0*Real.exp (-c*(n : ℝ)^δ))*ess φ*ess ζ)
    (hinc : ∀ (φ ζ : Bnd) (j i l : Fin (n : ℕ)),
      |(∫ x, φ.val x*ζ.val x*(Y x j i-Y x j l) ∂ν) +
        InterpolationMatrix.schurIncrementPair ν Q hQ s β m hm k hk hkm n φ.val ζ.val
          (j.castLE (by omega)) (i.castLE (by omega)) (l.castLE (by omega))| ≤
        (A0*(n : ℝ)^rowloss)*w j*(Nat.dist i.val l.val : ℝ)*(min (depth i : ℝ) (depth l : ℝ))^(-1-s.val/2)*
          ‖φ.val‖*‖ζ.val‖ + (E0*Real.exp (-c*(n : ℝ)^δ))*ess φ*ess ζ) :
    let K := 2*8^(2-s.val)*(2/(1-s.val/2)) +
      8^(1+s.val/2)*(2/s.val) + 4^(s.val/2)
    let L0 := (K*Real.sqrt (2/(1-s.val)))*(A0+E0)*D0
    let K0 := βhi*(C*(1+1/s.val)*(2/(1-s.val))) + (A0+E0)*(2/(1-s.val/2))^2
    ∃ v : Fin (n : ℕ) → Lp ℝ 2 ν,
    (∀ i, ‖v i‖ ≤ D0*(n : ℝ)^(4*loss)*(1+(Nat.dist i.val i₀.val : ℝ))^(s.val-2)*‖χ‖) ∧
    (∑ i, ‖v i‖) ≤ D0*(n : ℝ)^(4*loss)*‖χ‖ ∧
    ‖WithLp.toLp 2 (fun i => (ψ i).val-v i)‖^2 ≤
      (3*((2*L0/a0)^2+(1+K0)*D0^2/a0+D0^2))*(n : ℝ)^(8*loss-1)*‖χ‖^2 +
      (9*(3*((A0+E0)*Ka)*(2*V0+a0⁻¹)*V0+((A0+E0)*Ka)*V0^2)/a0)*
        (n : ℝ)^(2+4*loss)*Real.exp (-(c/2)*(n : ℝ)^δ)*B^2 := by
  intro K L0 K0
  obtain ⟨hex,hest⟩ := hAux
  obtain ⟨v0,hv0,_⟩ := hex
  obtain ⟨hvalue,hsumnorm,hsum,hgrad,hv⟩ := hest v0 hv0
  refine ⟨fun i => ((MatrixEnergy.vectorEquiv Q hQ v0) i).val, ?_⟩
  exact column_subtraction_comparison_with_losses_internal β s n d e hde m hm hnm k hk hkm θ ε η t ν Q hQ P hn2
    C κ γ hC hM hPm hH hHi hYi loss auxloss rowloss a0 D0 V0 A0 E0 βhi c δ Ka hKa habsorb hauxloss hrowloss
    hloss ha0 hD0 hV0 hA0 hE0 hβhi hκloss hlower i₀ hi₀ χ B hB hχ ψ v0 hψ
    hv hvalue hsumnorm hsum hgrad hv0 hpoint hinc

/-- Specialize the uniform auxiliary inverse on the probability law in
Lemma 6.4, retaining the full pairing estimate of Lemma 5.17. -/
theorem column_subtraction_comparison_from_uniform_auxiliary_internal
    [hprob : IsProbabilityMeasure ν]
    (hn2 : 2 ≤ (n : ℕ))
    (hcons : IsConservativeScalarForm Q)
    (C κ γ : ℝ) (hC : 1 ≤ C)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm k C κ γ η M)
    (hPm : ∀ i j, Measurable (fun x => P x i j))
    (hH : ∀ᵐ x ∂ν, (H x).PosSemidef)
    (hHi : ∀ i j, Integrable (fun x => H x i j) ν)
    (hYi : ∀ i j, Integrable (fun x => Y x i j) ν)
    (loss auxloss rowloss a0 D0 V0 A0 E0 βhi c δ Ka : ℝ)
    (hKa : 0 ≤ Ka)
    (habsorb : (n : ℝ)^(loss+5/2)*Real.exp (-c*(n : ℝ)^δ) ≤
      Ka*Real.exp (-(c/2)*(n : ℝ)^δ))
    (hauxloss : auxloss ≤ loss) (hrowloss : rowloss ≤ loss)
    (hloss : 0 ≤ loss) (ha0 : 0 < a0) (hD0 : 0 ≤ D0)
    (hV0 : 0 ≤ V0) (hA0 : 0 ≤ A0) (hE0 : 0 ≤ E0)
    (hβhi : β.val ≤ βhi) (hκloss : κ*η ≤ loss)
    (hlower : ∀ᵐ x ∂ν, ∀ z : Fin (n : ℕ) → ℝ,
      (a0*(n : ℝ)^(-loss))*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*H x i j*z j)
    (i₀ : Fin (n : ℕ)) (hi₀ : |(i₀.val : ℝ)+1-(n : ℝ)/2| ≤ (n : ℝ)/4)
    (χ : Lp ℝ 2 ν) (B : ℝ) (hB : 0 ≤ B)
    (hχ : ∀ᵐ x ∂ν, |χ x| ≤ B)
    (ψ : Fin (n : ℕ) → Q.1)
    (hψ : WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ)))
      (fun i => if i = i₀ then χ else 0) ψ)
    (hUniform : ∀ (X : Type) [MeasurableSpace X] (ν0 : Measure X) [IsProbabilityMeasure ν0],
      ∀ (Q0 : ScalarFormData ν0) (hQ0 : IsClosedScalarDirichletForm Q0),
      IsConservativeScalarForm Q0 →
      ∀ (M0 : X → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
        (hM0 : PeriodizedMatrixBounds (ν := ν0) s n m hm k C κ γ η M0),
      ∀ (i0 : Fin (n : ℕ)), |(i0.val : ℝ)+1-(n : ℝ)/2| ≤ (n : ℝ)/4 →
      ∀ (χ0 : Lp ℝ 2 ν0) (B0 : ℝ), 0 ≤ B0 → (∀ᵐ x ∂ν0, |χ0 x| ≤ B0) →
      (∃! v0 : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q0 hQ0,
        ∀ z, SchurRestriction.schurForm Q0 hQ0 n m (by omega) s hm k C κ γ η
          β.val hC β.property M0 hM0 v0 z =
            inner ℝ (WithLp.toLp 2 (fun i => if i=i0 then χ0 else 0)) (OperatorSchur.vectorValues Q0 hQ0 z)) ∧
      ∀ v0 : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q0 hQ0,
        (∀ z, SchurRestriction.schurForm Q0 hQ0 n m (by omega) s hm k C κ γ η
          β.val hC β.property M0 hM0 v0 z =
            inner ℝ (WithLp.toLp 2 (fun i => if i=i0 then χ0 else 0)) (OperatorSchur.vectorValues Q0 hQ0 z)) →
        let v := MatrixEnergy.vectorEquiv Q0 hQ0 v0
        (∀ j, ‖(v j).val‖ ≤ D0*(n : ℝ)^auxloss*(1+(Nat.dist j.val i0.val : ℝ))^(s.val-2)*‖χ0‖) ∧
        (∑ j, ‖(v j).val‖) ≤ D0*(n : ℝ)^auxloss*‖χ0‖ ∧
        ‖(∑ j, v j : Q0.1).val‖ ≤ D0*(n : ℝ)^(auxloss-(1-s.val))*‖χ0‖ ∧
        Real.sqrt (Q0.2 (∑ j, v j) (∑ j, v j)) ≤ D0*(n : ℝ)^(auxloss-(1-s.val)/2)*‖χ0‖ ∧
        ∀ j, ∀ᵐ x ∂ν0, |(v j).val x| ≤ V0*(n : ℝ)^auxloss*B0)
    (hpoint : ∀ (φ ζ : Bnd) (j i : Fin (n : ℕ)),
      |(∫ x, φ.val x*Y x j i*ζ.val x ∂ν) +
        InterpolationMatrix.schurPointPair ν Q hQ s β m hm k hk hkm n φ.val ζ.val
          (j.castLE (by omega)) (i.castLE (by omega))| ≤ (A0*(n : ℝ)^rowloss)*w j*w i*‖φ.val‖*‖ζ.val‖ + (E0*Real.exp (-c*(n : ℝ)^δ))*ess φ*ess ζ)
    (hinc : ∀ (φ ζ : Bnd) (j i l : Fin (n : ℕ)),
      |(∫ x, φ.val x*ζ.val x*(Y x j i-Y x j l) ∂ν) +
        InterpolationMatrix.schurIncrementPair ν Q hQ s β m hm k hk hkm n φ.val ζ.val
          (j.castLE (by omega)) (i.castLE (by omega)) (l.castLE (by omega))| ≤
        (A0*(n : ℝ)^rowloss)*w j*(Nat.dist i.val l.val : ℝ)*(min (depth i : ℝ) (depth l : ℝ))^(-1-s.val/2)*
          ‖φ.val‖*‖ζ.val‖ + (E0*Real.exp (-c*(n : ℝ)^δ))*ess φ*ess ζ) :
    let K := 2*8^(2-s.val)*(2/(1-s.val/2)) +
      8^(1+s.val/2)*(2/s.val) + 4^(s.val/2)
    let L0 := (K*Real.sqrt (2/(1-s.val)))*(A0+E0)*D0
    let K0 := βhi*(C*(1+1/s.val)*(2/(1-s.val))) + (A0+E0)*(2/(1-s.val/2))^2
    ∃ v : Fin (n : ℕ) → Lp ℝ 2 ν,
    (∀ i, ‖v i‖ ≤ D0*(n : ℝ)^(4*loss)*(1+(Nat.dist i.val i₀.val : ℝ))^(s.val-2)*‖χ‖) ∧
    (∑ i, ‖v i‖) ≤ D0*(n : ℝ)^(4*loss)*‖χ‖ ∧
    ‖WithLp.toLp 2 (fun i => (ψ i).val-v i)‖^2 ≤
      (3*((2*L0/a0)^2+(1+K0)*D0^2/a0+D0^2))*(n : ℝ)^(8*loss-1)*‖χ‖^2 +
      (9*(3*((A0+E0)*Ka)*(2*V0+a0⁻¹)*V0+((A0+E0)*Ka)*V0^2)/a0)*
        (n : ℝ)^(2+4*loss)*Real.exp (-(c/2)*(n : ℝ)^δ)*B^2 := by
  intro K L0 K0
  have hAux := hUniform _ ν Q hQ hcons M hM i₀ hi₀ χ B hB hχ
  exact column_subtraction_comparison_from_auxiliary_internal β s n d e hde m hm hnm k hk hkm θ ε η t ν Q hQ P hn2
    C κ γ hC hM hPm hH hHi hYi loss auxloss rowloss a0 D0 V0 A0 E0 βhi c δ Ka hKa habsorb hauxloss hrowloss
    hloss ha0 hD0 hV0 hA0 hE0 hβhi hκloss hlower i₀ hi₀ χ B hB hχ ψ hψ hAux hpoint hinc

end Riesz2.FixedLengthDecay
