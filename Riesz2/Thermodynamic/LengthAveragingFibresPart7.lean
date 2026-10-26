/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.LengthAveragingFibresPart5
public import Riesz2.Thermodynamic.FixedLengthDecayLong
public import Riesz2.DecayLong.PhysicalMeanPart2

/-!
# Long conditional native perturbations and auxiliary solutions

Composition for the proof of Lemma 6.5 on the retained marginal law. The physical
penalty and fine tolerance remain independent, and exceptional errors retain the
conditional envelope and its exponent.
-/

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Classical ContDiff

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.LengthAveragingFibres

/-- See the proof of Lemma 6.5 in the paper: the physical marginal
coefficient field in the native multiplication defect is the unpenalized
marginal Hessian divided by the actual temperature. Consequently its full
matrix is exactly the two-sided physical Hessian, including covariance. -/
theorem long_native_matrix_identity_internal
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ)
    (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1)) :
    let W := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      -Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (y,z)).toReal)
    let V := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      β.val*∑ i, (θ.val ((n : ℝ)^(-ε)*y i)+θ.val ((n : ℝ)^(-ε)*(y i)⁻¹)) + W y
    hessianMatrix V x.val = β.val • (InterpolationMatrix.penaltyHessian n θ ε x.val +
      β.val⁻¹ • hessianMatrix W x.val) := by
  intro W V
  ext i j
  have hh := marginal_penalty_hessian_internal (ofLong β s) n m θ
    (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < n) (-ε)) true x i j
  simp only [ite_true] at hh
  change hessianMatrix V x.val i j = _ at hh ⊢
  rw [hh]
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
    InterpolationMatrix.penaltyHessian]
  have hβ := β.property.ne'
  dsimp only [W]
  simp only [ofLong] at *
  field_simp

/-- See the proof of Lemma 6.5 in the paper: value, component sum,
mean, mean-gradient and bounded-source estimates for the interval matrix on the actual retained marginal law. The arbitrary
scalar-form theorem applies to the intrinsic form constructed in Part5,
so all five estimates use that same form without an additional chart. -/
theorem retained_long_auxiliary_estimates_internal
    (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (θ : PhysicalCutoff) (h : ℕ+) :
    let κstar := (s.val+7+(h : ℝ))+(s.val+2+(h : ℝ)*(1+s.val))
    let γstar := (h : ℝ)+1
    ∃ (Cstar : ℝ) (hCstar : 1 ≤ Cstar) (κ : ℝ), 0 < κ ∧
    ∀ η : ℝ, 0 < η → η ≤ 1-s.val/2 →
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    ∀ n m : ℕ, 1 ≤ n → 4*(n+1) ≤ n+1+m+1 →
    ∀ (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : (n.succPNat : ℕ) ≤ (M : ℕ)),
      2*(n+1) ≤ (M : ℕ) → (M : ℕ) ≤ n+1+m+1 →
      (n+1 : ℝ)^(1/2+1/s.val) ≤ (M : ℝ) →
      (M : ℝ) ≤ 2*(n+1 : ℝ)^(1/2+1/s.val) →
    ∀ ε : ℝ, 0 ≤ ε →
    let k := ⌊(n+1 : ℝ)^η⌋₊^(h : ℕ)
    1 ≤ k → 4*k ≤ (M : ℕ) →
    ∀ L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ),
    let ν := retainedKernel (ofLong β s) n m θ ε L
    let A := InterpolationMatrix.matrix β s n.succPNat m m le_rfl M hM hnM k θ ε η 0
    ∀ (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q),
      IsConservativeScalarForm Q →
    ∃ hA : PeriodizedMatrixBounds (ν := ν) s n.succPNat M hM k Cstar κstar γstar η A,
    ∀ i₀ : Fin (n+1), |(i₀.val : ℝ)+1-(n+1 : ℝ)/2| ≤ (n+1 : ℝ)/4 →
    ∀ (χ : Lp ℝ 2 ν) (B : ℝ), 0 ≤ B → (∀ᵐ x ∂ν, |χ x| ≤ B) →
    let f : PiLp 2 (fun _ : Fin (n+1) => Lp ℝ 2 ν) :=
      WithLp.toLp 2 (fun i => if i = i₀ then χ else 0)
    let Abar := SchurRestriction.schurForm Q hQ n.succPNat M hnM s hM k
      Cstar κstar γstar η β.val hCstar β.property A hA
    (∃! v : MatrixEnergy.Vector (ι := Fin (n+1)) Q hQ,
      ∀ w, Abar v w = inner ℝ f (OperatorSchur.vectorValues Q hQ w)) ∧
    ∀ v : MatrixEnergy.Vector (ι := Fin (n+1)) Q hQ,
      (∀ w, Abar v w = inner ℝ f (OperatorSchur.vectorValues Q hQ w)) →
    let v' := MatrixEnergy.vectorEquiv Q hQ v
    let S := ∑ i, v' i
    (∀ j : Fin (n+1), ‖(v' j).val‖ ≤ C*(n+1 : ℝ)^(κ*η)*
      (1+(Nat.dist j.val i₀.val : ℝ))^(s.val-2)*‖χ‖) ∧
    (∑ j, ‖(v' j).val‖) ≤ C*(n+1 : ℝ)^(κ*η)*‖χ‖ ∧
    ‖S.val‖ ≤ C*(n+1 : ℝ)^(κ*η-(1-s.val))*‖χ‖ ∧
    Real.sqrt (Q.2 S S) ≤ C*(n+1 : ℝ)^(κ*η-(1-s.val)/2)*‖χ‖ ∧
    ∀ i : Fin (n+1), ∀ᵐ x ∂ν, |(v' i).val x| ≤ C*(n+1 : ℝ)^(κ*η)*B := by
  intro κstar γstar
  obtain ⟨Cstar, hCstar, hb⟩ := InterpolationMatrix.matrix_bounds s θ (h : ℕ)
  have hκstar : 0 < κstar := by dsimp only [κstar]; have := s.property.1; positivity
  have hγstar : 0 < γstar := by dsimp only [γstar]; positivity
  obtain ⟨κ, hκ, ha⟩ := FixedLengthDecay.schur_on_scalar_form_internal hz s κstar γstar h
    hκstar hγstar
  refine ⟨Cstar, hCstar, κ, hκ, ?_⟩
  intro η hη hηs βlo βhi hlo hle
  obtain ⟨C, hC, ha⟩ := ha η hη Cstar hCstar βlo βhi hlo hle
  refine ⟨C, hC, ?_⟩
  intro β hβ n m hn hvol M hM hnM hhalf hMN hscale hupper ε hε k hk hkm L ν A Q hQ hcon
  have hs' : (n.succPNat : ℝ)^(1/2+1/s.val) ≤ (M : ℝ) := by
    simpa only [Nat.succPNat_coe, Nat.cast_succ] using hscale
  have hk' : ⌊(n.succPNat : ℝ)^η⌋₊^(h : ℕ) ≤ (M : ℕ)/4 := by
    dsimp only [k] at hkm ⊢
    simp only [Nat.succPNat_coe, Nat.cast_succ]
    omega
  have hA : PeriodizedMatrixBounds (ν := ν) s n.succPNat M hM k Cstar κstar γstar η A := by
    simpa only [A, k, Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using
      hb β n.succPNat m m le_rfl hvol M hM hhalf hMN hs' ε η 0 hε hη.le hηs
        le_rfl zero_le_one hk' ν
  refine ⟨hA, ?_⟩
  intro i₀ hi₀ χ B hB hχ
  have hn' : 2 ≤ (n.succPNat : ℕ) := by simpa only [Nat.succPNat_coe] using Nat.add_le_add_right hn 1
  have hu' : (M : ℝ) ≤ 2*(n.succPNat : ℝ)^(1/2+1/s.val) := by
    simpa only [Nat.succPNat_coe, Nat.cast_succ] using hupper
  have hest := ha β hβ n.succPNat M hn' hM hhalf hu'
    (by simpa only [k, Nat.succPNat_coe, Nat.cast_succ] using hk)
    (by simpa only [k, Nat.succPNat_coe, Nat.cast_succ] using hkm) _ ν Q hQ hcon A
    (by simpa only [k, Nat.succPNat_coe, Nat.cast_succ] using hA) i₀
    (by simpa only [Nat.succPNat_coe, Nat.cast_succ] using hi₀) χ B hB hχ
  simpa only [Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using hest

/-- See the proof of Lemma 6.5 in the paper: the Schur point and signed
column-increment estimates on the same retained scalar form as the literal
physical multiplication defect. The exceptional term is conditional and
retains the fixed power `1+2/s-C₀`. -/
theorem conditional_long_native_profiles_internal
    (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (κ₀ : ℝ) (hκ₀ : 1 ≤ κ₀) (h : ℕ) :
    ∃ κ > 0, ∀ η βlo βhi : ℝ, 0 < η → 0 < βlo → βlo ≤ βhi →
    ∃ A D : ℝ, 0 < A ∧ 0 < D ∧
    ∀ (β : InverseTemperature), β.val ∈ Icc βlo βhi →
    ∀ (n : ℕ+) (m : ℕ), 2*(n : ℕ) ≤ (n : ℕ)+m+1 →
    ∀ (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : (n : ℕ) ≤ (M : ℕ)),
      2*(n : ℕ) ≤ (M : ℕ) → (M : ℝ) ≤ 3*(n : ℝ)^(1/2+1/s.val) →
    let k := ⌊(n : ℝ)^η⌋₊^h
    ∀ (hk : 1 ≤ k) (hkm : k ≤ (M : ℕ)/4),
    ∀ (θ : PhysicalCutoff) (ε C₀ : ℝ)
      (ν : Measure (AffineSimplex.chartDomain n ((n+m : ℕ)+1))),
      (∫⁻ x in (longFineEvent β s n m η κ₀)ᶜ,
        ENNReal.ofReal (longEnvelope β s n m θ ε C₀ x) ∂ν) ≠ (∞ : ℝ≥0∞) →
    ∀ (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q),
    let d := fun a : Fin (n : ℕ) => ((min (a.val+1) ((n : ℕ)-a.val) : ℕ) : ℝ)
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      β.val*∑ i, (θ.val ((n : ℝ)^(-ε)*x i)+θ.val ((n : ℝ)^(-ε)*(x i)⁻¹)) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (x,z)).toReal)
    let Y := fun (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1)) a b =>
      hessianMatrix V x.val a b -
        β.val*InterpolationMatrix.activeBlock β s n m m le_rfl M hM hnM k θ ε η 0 x a b
    let e := (∫⁻ x in (longFineEvent β s n m η κ₀)ᶜ,
      ENNReal.ofReal (longEnvelope β s n m θ ε C₀ x) ∂ν).toReal
    ∀ (φ ζ : BoundedL2Pairings.boundedSubmodule ν) (j i l : Fin (n : ℕ)),
    let Mφ := (eLpNorm (φ.val : _ → ℝ) ∞ ν).toReal
    let Mζ := (eLpNorm (ζ.val : _ → ℝ) ∞ ν).toReal
    Integrable (fun x => φ.val x*Y x j i*ζ.val x) ν ∧
    Integrable (fun x => φ.val x*ζ.val x*(Y x j i-Y x j l)) ν ∧
    |(∫ x, φ.val x*Y x j i*ζ.val x ∂ν) +
      InterpolationMatrix.schurPointPair ν Q hQ s β M hM k hk hkm n φ.val ζ.val
        (j.castLE hnM) (i.castLE hnM)| ≤
      A*(n : ℝ)^(κ*η)*(d j)^(-s.val/2)*(d i)^(-s.val/2)*‖φ.val‖*‖ζ.val‖ +
        D*(n : ℝ)^(1+2/s.val-C₀)*e*Mφ*Mζ ∧
    |(∫ x, φ.val x*ζ.val x*(Y x j i-Y x j l) ∂ν) +
      InterpolationMatrix.schurIncrementPair ν Q hQ s β M hM k hk hkm n φ.val ζ.val
        (j.castLE hnM) (i.castLE hnM) (l.castLE hnM)| ≤
      A*(n : ℝ)^(κ*η)*(Nat.dist i.val l.val : ℝ)*(d j)^(-s.val/2)*
        (min (d i) (d l))^(-1-s.val/2)*‖φ.val‖*‖ζ.val‖ +
        D*(n : ℝ)^(1+2/s.val-C₀)*e*Mφ*Mζ := by
  obtain ⟨κm, hκm, hm⟩ := conditional_long_multiplication_pairings_internal s κ₀ hκ₀
  let κ := max κm (2*(h : ℝ))
  refine ⟨κ, hκm.trans_le (le_max_left _ _), ?_⟩
  intro η βlo βhi hη hlo hle
  obtain ⟨Am, D, hAm, hD, hm⟩ := hm η βlo βhi hη hlo hle
  obtain ⟨As, hAs, hs⟩ := InterpolationPerturbation.schur_cutoff_profiles_compact hz s h 1 βhi
    (hlo.trans_le hle)
  refine ⟨Am+As, D, add_pos hAm hAs, hD, ?_⟩
  intro β hβ n m hper M hM hnM hhalf hupper k hk hkm θ ε C₀ ν he Q hQ d V Y e φ ζ j i l Mφ Mζ
  have hφ := FixedLengthDecay.bounded_ae_essentialNorm_internal φ
  have hζ := FixedLengthDecay.bounded_ae_essentialNorm_internal ζ
  obtain ⟨hpi, hp, hdi, hd⟩ := hm β hβ n m hper M hM hnM k hhalf hupper θ ε C₀ ν he
    φ.val ζ.val Mφ Mζ ENNReal.toReal_nonneg ENNReal.toReal_nonneg hφ hζ j i l
  have heq : (fun x => φ.val x*ζ.val x*Y x j i) =
      (fun x => φ.val x*Y x j i*ζ.val x) := by funext x; ring
  change Integrable (fun x => φ.val x*ζ.val x*Y x j i) ν at hpi
  change |∫ x, φ.val x*ζ.val x*Y x j i ∂ν| ≤ _ at hp
  rw [heq] at hpi hp
  have hs' := hs β hβ.2 η n M hM hnM
    (by simpa only [one_mul] using hk) (by simpa only [one_mul] using hkm)
    ν Q hQ φ.val ζ.val i j l
  simp only [one_mul, mul_one] at hs'
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hpm : (n : ℝ)^(κm*η) ≤ (n : ℝ)^(κ*η) :=
    Real.rpow_le_rpow_of_exponent_le hn1
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hη.le)
  have hps : (n : ℝ)^((2*(h : ℝ))*η) ≤ (n : ℝ)^(κ*η) :=
    Real.rpow_le_rpow_of_exponent_le hn1
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hη.le)
  have hsp : |InterpolationMatrix.schurPointPair ν Q hQ s β M hM k hk hkm n φ.val ζ.val
      (j.castLE hnM) (i.castLE hnM)| ≤
      As*(n : ℝ)^(κ*η)*(d j)^(-s.val/2)*(d i)^(-s.val/2)*‖φ.val‖*‖ζ.val‖ := by
    apply hs'.1.trans
    dsimp only [d]
    calc
      _ ≤ As*(n : ℝ)^(κ*η)*
        (min (i.val+1) ((n : ℕ)-i.val) : ℕ)^(-s.val/2)*
        (min (j.val+1) ((n : ℕ)-j.val) : ℕ)^(-s.val/2)*‖φ.val‖*‖ζ.val‖ := by gcongr
      _ = _ := by ring
  have hsd : |InterpolationMatrix.schurIncrementPair ν Q hQ s β M hM k hk hkm n φ.val ζ.val
      (j.castLE hnM) (i.castLE hnM) (l.castLE hnM)| ≤
      As*(n : ℝ)^(κ*η)*(Nat.dist i.val l.val : ℝ)*(d j)^(-s.val/2)*
        (min (d i) (d l))^(-1-s.val/2)*‖φ.val‖*‖ζ.val‖ := by
    have hh := hs'.2
    simp only [Nat.cast_min] at hh
    apply hh.trans
    dsimp only [d]
    simp only [Nat.cast_min]
    gcongr
  refine ⟨hpi, hdi, ?_, ?_⟩
  · have hp' : |∫ x, φ.val x*Y x j i*ζ.val x ∂ν| ≤
        Am*(n : ℝ)^(κ*η)*(d j)^(-s.val/2)*(d i)^(-s.val/2)*‖φ.val‖*‖ζ.val‖ +
          D*(n : ℝ)^(1+2/s.val-C₀)*e*Mφ*Mζ := hp.trans (by gcongr)
    apply ((abs_add_le _ _).trans (add_le_add hp' hsp)).trans_eq
    ring
  · have hd' : |∫ x, φ.val x*ζ.val x*(Y x j i-Y x j l) ∂ν| ≤
        Am*(n : ℝ)^(κ*η)*(Nat.dist i.val l.val : ℝ)*(d j)^(-s.val/2)*
          (min (d i) (d l))^(-1-s.val/2)*‖φ.val‖*‖ζ.val‖ +
          D*(n : ℝ)^(1+2/s.val-C₀)*e*Mφ*Mζ := hd.trans (by gcongr)
    apply ((abs_add_le _ _).trans (add_le_add hd' hsd)).trans_eq
    ring

section ConditionalNativeComparison


variable (β : InverseTemperature) (s : Riesz1.RieszExponent)
  (n : ℕ+) (d e₁ : ℕ) (hde : d ≤ e₁) (m : ℕ+) (hm : 2 ≤ (m : ℕ))
  (hnm : 2*(n : ℕ) ≤ (m : ℕ)) (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ (m : ℕ)/4)
  (θ : PhysicalCutoff) (ε η t : ℝ)
  (ν : Measure (AffineSimplex.chartDomain n ((n+d : ℕ)+1)))
  (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
  (P : AffineSimplex.chartDomain n ((n+d : ℕ)+1) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)

local notation "H" => fun x : AffineSimplex.chartDomain n ((n+d : ℕ)+1) =>
  β.val • (InterpolationMatrix.penaltyHessian n θ ε (Subtype.val x) + P x)
local notation "M" => InterpolationMatrix.matrix β s n d e₁ hde m hm (by omega) k θ ε η t
local notation "Y" => InterpolationMatrix.multiplicationPart β s n d e₁ hde m hm (by omega) k θ ε η t P
local notation "Bnd" => BoundedL2Pairings.boundedSubmodule ν
local notation "ess" => fun f : Bnd => ENNReal.toReal (eLpNorm (fun x => (Subtype.val f) x) ∞ ν)
local notation "w" => InteractionDifferential.boundaryWeight s.val n
local notation "depth" => fun i : Fin (n : ℕ) => (min (Fin.val i+1) ((n : ℕ)-Fin.val i) : ℕ)

/-- See the proof of Lemma 6.5 in the paper: the long physical energy
comparison squared, with a conditional exceptional coefficient instead of
an unconditional tail. The actual normal energy and maximum principle
are supplied by the native comparison. -/
theorem conditional_native_square_internal
    (C κ γ : ℝ) (hC : 1 ≤ C)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm k C κ γ η M)
    (hPm : ∀ i j, Measurable (fun x => P x i j))
    (hH : ∀ᵐ x ∂ν, (H x).PosSemidef)
    (hHi : ∀ i j, Integrable (fun x => H x i j) ν)
    (hYi : ∀ i j, Integrable (fun x => Y x i j) ν)
    (loss a0 D0 V0 A0 Derr e b C₀ βhi : ℝ)
    (hloss : 0 ≤ loss) (ha0 : 0 < a0) (hD0 : 0 ≤ D0)
    (hV0 : 0 ≤ V0) (hA0 : 0 ≤ A0) (hDerr : 0 ≤ Derr) (he : 0 ≤ e)
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
          (j.castLE (by omega)) (i.castLE (by omega))| ≤ (A0*(n : ℝ)^loss)*w j*w i*‖φ.val‖*‖ζ.val‖ + (Derr*(n : ℝ)^(b-C₀)*e)*ess φ*ess ζ)
    (hinc : ∀ (φ ζ : Bnd) (j i l : Fin (n : ℕ)),
      |(∫ x, φ.val x*ζ.val x*(Y x j i-Y x j l) ∂ν) +
        InterpolationMatrix.schurIncrementPair ν Q hQ s β m hm k hk hkm n φ.val ζ.val
          (j.castLE (by omega)) (i.castLE (by omega)) (l.castLE (by omega))| ≤
        (A0*(n : ℝ)^loss)*w j*(Nat.dist i.val l.val : ℝ)*(min (depth i : ℝ) (depth l : ℝ))^(-1-s.val/2)*
          ‖φ.val‖*‖ζ.val‖ + (Derr*(n : ℝ)^(b-C₀)*e)*ess φ*ess ζ) :
    let K := 2*8^(2-s.val)*(2/(1-s.val/2)) +
      8^(1+s.val/2)*(2/s.val) + 4^(s.val/2)
    let L0 := (K*Real.sqrt (2/(1-s.val)))*A0*D0
    let K0 := βhi*(C*(1+1/s.val)*(2/(1-s.val))) + A0*(2/(1-s.val/2))^2
    ‖WithLp.toLp 2 (fun i => (ψ i).val-(v i).val)‖^2 ≤
      (3*((2*L0/a0)^2+(1+K0)*D0^2/a0+D0^2))*(n : ℝ)^(8*loss-1)*‖χ‖^2 +
      (9*(3*Derr*(2*V0+a0⁻¹)*V0+Derr*V0^2)/a0)*
        (n : ℝ)^(2+4*loss+b-C₀)*e*B^2 := by
  intro K L0 K0
  have hp : 0 ≤ Derr*(n : ℝ)^(b-C₀)*e := by positivity
  have hpoint' := hpoint
  have hinc' := hinc
  have hh := FixedLengthDecay.normalized_native_square_internal β s n d e₁ hde m hm hnm
    k hk hkm θ ε η t ν Q hQ P C κ γ hC hM hPm hH hHi hYi
    loss a0 D0 V0 A0 (Derr*(n : ℝ)^(b-C₀)*e) βhi 0 0
    hloss ha0 hD0 hV0 hA0 hp hβhi hκloss hlower i₀ hi₀ χ B hB hχ ψ v hψ
    hv hvalue hsum hgrad haux
    (by simpa only [neg_zero, zero_mul, Real.exp_zero, mul_one] using hpoint')
    (by simpa only [neg_zero, zero_mul, Real.exp_zero, mul_one] using hinc')
  simp only [neg_zero, zero_mul, Real.exp_zero, mul_one] at hh
  apply hh.trans_eq
  have hn : (0 : ℝ) < n := by positivity
  have hpow : (n : ℝ)^(2+4*loss+b-C₀) =
      (n : ℝ)^(2+4*loss)*(n : ℝ)^(b-C₀) := by
    rw [← Real.rpow_add hn]
    congr 1
    ring
  dsimp only [K, L0, K0] at *
  rw [hpow]
  ring

end ConditionalNativeComparison

/-- See the proof of Lemma 6.5 in the paper: identification of the
native coefficient with the full physical marginal defect, on the whole
positive carrier and with the original penalty exponent. -/
theorem long_native_defect_identity_internal
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : (n : ℕ) ≤ (M : ℕ)) (k : ℕ)
    (θ : PhysicalCutoff) (ε η : ℝ) :
    let W := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      -Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (y,z)).toReal)
    let V := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      β.val*∑ i, (θ.val ((n : ℝ)^(-ε)*y i)+θ.val ((n : ℝ)^(-ε)*(y i)⁻¹)) + W y
    let P := fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) =>
      β.val⁻¹ • hessianMatrix W x.val
    ∀ x, InterpolationMatrix.multiplicationPart β s n m m le_rfl M hM hnM k θ ε η 0 P x =
      hessianMatrix V x.val -
        β.val • InterpolationMatrix.activeBlock β s n m m le_rfl M hM hnM k θ ε η 0 x := by
  intro W V P x
  rw [InterpolationMatrix.multiplicationPart_eq_defect, smul_sub,
    ← long_native_matrix_identity_internal β s n m θ ε x]

/-- See the proof of Lemma 6.5 in the paper: fixing the envelope after
all exceptional losses yields the uniform squared comparison required by
the long fibre-sum transfer, for any prescribed final power. -/
theorem conditional_square_absorption_internal (n : ℕ+) (Λ η b C₀ P E T F B e z : ℝ)
    (hΛ : 0 ≤ Λ) (hη : η ≤ 1) (hT : 0 ≤ T) (he : 0 ≤ e)
    (hC₀ : b+2+4*Λ+2*P ≤ C₀)
    (hz : z^2 ≤ E*(n : ℝ)^(8*(Λ*η)-1)*F^2 +
      T*(n : ℝ)^(2+4*(Λ*η)+b-C₀)*e*B^2) :
    z^2 ≤ E*(n : ℝ)^(2*((4*Λ)*η)-1)*F^2 +
      T*(n : ℝ)^(-2*P)*B^2*e := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hpow : (n : ℝ)^(2+4*(Λ*η)+b-C₀) ≤ (n : ℝ)^(-2*P) := by
    apply Real.rpow_le_rpow_of_exponent_le hn1
    nlinarith only [hC₀, mul_le_mul_of_nonneg_left hη hΛ]
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hT) he) (sq_nonneg B)
  have hexp : 8*(Λ*η)-1 = 2*((4*Λ)*η)-1 := by ring
  rw [hexp] at hz
  exact hz.trans (add_le_add le_rfl (hh.trans_eq (by ring)))

/-- See the proof of Lemma 6.5 in the paper: native coefficient integrability
and both conditional Schur pairings for the literal marginal coefficient field. -/
theorem conditional_long_native_data_internal
    (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (κ₀ : ℝ) (hκ₀ : 1 ≤ κ₀) (h : ℕ) :
    ∃ κ > 0, ∀ η βlo βhi : ℝ, 0 < η → 0 < βlo → βlo ≤ βhi →
    ∃ A D : ℝ, 0 < A ∧ 0 < D ∧
    ∀ (β : InverseTemperature), β.val ∈ Icc βlo βhi →
    ∀ (n : ℕ+) (m : ℕ), 2*(n : ℕ) ≤ (n : ℕ)+m+1 →
    ∀ (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : (n : ℕ) ≤ (M : ℕ)),
      2*(n : ℕ) ≤ (M : ℕ) → (M : ℝ) ≤ 3*(n : ℝ)^(1/2+1/s.val) →
    let k := ⌊(n : ℝ)^η⌋₊^h
    ∀ (hk : 1 ≤ k) (hkm : k ≤ (M : ℕ)/4),
    ∀ (θ : PhysicalCutoff) (ε C₀ : ℝ)
      (ν : Measure (AffineSimplex.chartDomain n ((n+m : ℕ)+1))) [IsProbabilityMeasure ν],
      (∫⁻ x in (longFineEvent β s n m η κ₀)ᶜ,
        ENNReal.ofReal (longEnvelope β s n m θ ε C₀ x) ∂ν) ≠ (∞ : ℝ≥0∞) →
    ∀ (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q),
    let d := fun a : Fin (n : ℕ) => ((min (a.val+1) ((n : ℕ)-a.val) : ℕ) : ℝ)
    let W := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      -Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (y,z)).toReal)
    let P := fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) => β.val⁻¹ • hessianMatrix W x.val
    let Y := InterpolationMatrix.multiplicationPart β s n m m le_rfl M hM hnM k θ ε η 0 P
    let e := (∫⁻ x in (longFineEvent β s n m η κ₀)ᶜ,
      ENNReal.ofReal (longEnvelope β s n m θ ε C₀ x) ∂ν).toReal
    (∀ i j, Measurable (fun x => P x i j)) ∧
    (∀ i j, Integrable (fun x => Y x i j) ν) ∧
    ∀ (φ ζ : BoundedL2Pairings.boundedSubmodule ν) (j i l : Fin (n : ℕ)),
    let Mφ := (eLpNorm (φ.val : _ → ℝ) ∞ ν).toReal
    let Mζ := (eLpNorm (ζ.val : _ → ℝ) ∞ ν).toReal
    Integrable (fun x => φ.val x*Y x j i*ζ.val x) ν ∧
    Integrable (fun x => φ.val x*ζ.val x*(Y x j i-Y x j l)) ν ∧
    |(∫ x, φ.val x*Y x j i*ζ.val x ∂ν) +
      InterpolationMatrix.schurPointPair ν Q hQ s β M hM k hk hkm n φ.val ζ.val
        (j.castLE hnM) (i.castLE hnM)| ≤
      A*(n : ℝ)^(κ*η)*(d j)^(-s.val/2)*(d i)^(-s.val/2)*‖φ.val‖*‖ζ.val‖ +
        D*(n : ℝ)^(1+2/s.val-C₀)*e*Mφ*Mζ ∧
    |(∫ x, φ.val x*ζ.val x*(Y x j i-Y x j l) ∂ν) +
      InterpolationMatrix.schurIncrementPair ν Q hQ s β M hM k hk hkm n φ.val ζ.val
        (j.castLE hnM) (i.castLE hnM) (l.castLE hnM)| ≤
      A*(n : ℝ)^(κ*η)*(Nat.dist i.val l.val : ℝ)*(d j)^(-s.val/2)*
        (min (d i) (d l))^(-1-s.val/2)*‖φ.val‖*‖ζ.val‖ +
        D*(n : ℝ)^(1+2/s.val-C₀)*e*Mφ*Mζ := by
  obtain ⟨κ, hκ, hp⟩ := conditional_long_native_profiles_internal hz s κ₀ hκ₀ h
  refine ⟨κ, hκ, ?_⟩
  intro η βlo βhi hη hlo hle
  obtain ⟨A, D, hA, hD, hp⟩ := hp η βlo βhi hη hlo hle
  refine ⟨A, D, hA, hD, ?_⟩
  intro β hβ n m hnper M hM hnM hhalf hupper k hk hkm θ ε C₀ ν _ he Q hQ d W P Y e
  have htests := hp β hβ n m hnper M hM hnM hhalf hupper hk hkm θ ε C₀ ν he Q hQ
  have hY (x) (i j) : Y x i j =
      hessianMatrix (fun y => β.val*∑ a, (θ.val ((n : ℝ)^(-ε)*y a)+
        θ.val ((n : ℝ)^(-ε)*(y a)⁻¹)) + W y) x.val i j-
        β.val*InterpolationMatrix.activeBlock β s n m m le_rfl M hM hnM k θ ε η 0 x i j := by
    exact congrFun (congrFun (long_native_defect_identity_internal β s n m M hM hnM k θ ε η x) i) j
  have hPm (i j) : Measurable (fun x => P x i j) :=
    ((DifferentiatedPoisson.measurable_hessian_entries (V := W) i j).comp
      measurable_subtype_coe).const_mul β.val⁻¹
  let one : Lp ℝ 2 ν := (memLp_const (1 : ℝ) : MemLp (fun _ => (1 : ℝ)) 2 ν).toLp (fun _ => 1)
  have hone : (one : _ → ℝ) =ᵐ[ν] fun _ => 1 := (memLp_const (1 : ℝ)).coeFn_toLp
  let oneB : BoundedL2Pairings.boundedSubmodule ν :=
    ⟨one, 1, hone.mono fun _ hx => by simp only [hx, abs_one, le_refl]⟩
  have hYi (i j) : Integrable (fun x => Y x i j) ν := by
    have hi := (htests oneB oneB i j j).1
    apply hi.congr
    filter_upwards [hone] with x hx
    simp only [oneB, hx, one_mul, mul_one]
    exact (hY x i j).symm
  refine ⟨hPm, hYi, ?_⟩
  intro φ ζ j i l
  simpa only [hY, sub_eq_add_neg] using htests φ ζ j i l

/-- See the proof of Lemma 6.5 in the paper: all five auxiliary bounds
can be increased to one common loss, preserving the same form energy. -/
theorem auxiliary_loss_mono_internal {X : Type*} [MeasurableSpace X]
    {ν : Measure X} (Q : ScalarFormData ν) (s : ℝ) (n : ℕ+)
    (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν) (v : Fin (n : ℕ) → Q.1)
    (D B a b : ℝ) (hD : 0 ≤ D) (hB : 0 ≤ B) (hab : a ≤ b)
    (hv : (∀ j, ‖(v j).val‖ ≤ D*(n : ℝ)^a*(1+(Nat.dist j.val i₀.val : ℝ))^(s-2)*‖χ‖) ∧
      (∑ j, ‖(v j).val‖) ≤ D*(n : ℝ)^a*‖χ‖ ∧
      ‖(∑ j, v j : Q.1).val‖ ≤ D*(n : ℝ)^(a-(1-s))*‖χ‖ ∧
      Real.sqrt (Q.2 (∑ j, v j) (∑ j, v j)) ≤ D*(n : ℝ)^(a-(1-s)/2)*‖χ‖ ∧
      ∀ j, ∀ᵐ x ∂ν, |(v j).val x| ≤ D*(n : ℝ)^a*B) :
    (∀ j, ‖(v j).val‖ ≤ D*(n : ℝ)^b*(1+(Nat.dist j.val i₀.val : ℝ))^(s-2)*‖χ‖) ∧
      (∑ j, ‖(v j).val‖) ≤ D*(n : ℝ)^b*‖χ‖ ∧
      ‖(∑ j, v j : Q.1).val‖ ≤ D*(n : ℝ)^(b-(1-s))*‖χ‖ ∧
      Real.sqrt (Q.2 (∑ j, v j) (∑ j, v j)) ≤ D*(n : ℝ)^(b-(1-s)/2)*‖χ‖ ∧
      ∀ j, ∀ᵐ x ∂ν, |(v j).val x| ≤ D*(n : ℝ)^b*B := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hp := Real.rpow_le_rpow_of_exponent_le hn1 hab
  obtain ⟨hv, hs, hm, hg, hsup⟩ := hv
  refine ⟨fun j => (hv j).trans (by gcongr), hs.trans (by gcongr),
    hm.trans (by gcongr), hg.trans (by gcongr), ?_⟩
  intro j
  exact (hsup j).mono fun _ hx => hx.trans (by gcongr)

/-- See the proof of Lemma 6.5 in the paper: integrability of the
physical native matrix from its integrable defect and the bounded active block. This holds on the whole probability carrier. -/
theorem long_native_entries_internal
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : (n : ℕ) ≤ (M : ℕ)) (k : ℕ)
    (θ : PhysicalCutoff) (ε η C κ γ : ℝ)
    (ν : Measure (AffineSimplex.chartDomain n ((n+m : ℕ)+1))) [IsProbabilityMeasure ν]
    (P : AffineSimplex.chartDomain n ((n+m : ℕ)+1) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (hmat : PeriodizedMatrixBounds (ν := ν) s n M hM k C κ γ η
      (InterpolationMatrix.matrix β s n m m le_rfl M hM hnM k θ ε η 0))
    (hYi : ∀ i j, Integrable (fun x =>
      InterpolationMatrix.multiplicationPart β s n m m le_rfl M hM hnM k θ ε η 0 P x i j) ν) :
    ∀ i j, Integrable (fun x =>
      β.val*(InterpolationMatrix.penaltyHessian n θ ε x.val i j+P x i j)) ν := by
  obtain ⟨b, hbnd⟩ := SchurRestriction.periodized_scaled_bounded β.val hmat
  have hAi (i j : Fin (n : ℕ)) : Integrable (fun x =>
      β.val*InterpolationMatrix.activeBlock β s n m m le_rfl M hM hnM k θ ε η 0 x i j) ν := by
    apply (integrable_const b).mono'
      ((InterpolationMatrix.measurable_activeBlock β s n m m le_rfl M hM hnM k θ ε η 0 i j).const_mul β.val).aestronglyMeasurable
    filter_upwards [hbnd] with x hx
    simpa only [Real.norm_eq_abs, Matrix.smul_apply, smul_eq_mul,
      InterpolationMatrix.matrix_active] using hx (i.castLE hnM) (j.castLE hnM)
  intro i j
  apply ((hYi i j).add (hAi i j)).congr
  apply ae_of_all
  intro x
  change InterpolationMatrix.multiplicationPart β s n m m le_rfl M hM hnM k θ ε η 0 P x i j +
    β.val*InterpolationMatrix.activeBlock β s n m m le_rfl M hM hnM k θ ε η 0 x i j = _
  rw [InterpolationMatrix.multiplicationPart_eq_defect]
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
  ring

/-- See the proof of Lemma 6.5 in the paper: coercivity of the literal
native coefficient at a common fine-tolerance loss, uniformly over the
temperature interval and the whole retained carrier. -/
theorem long_native_coercivity_internal
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (θ : PhysicalCutoff) (ε η Λ βlo : ℝ) (hε : 0 ≤ ε) (hεη : ε ≤ η)
    (hη : 0 ≤ η) (hΛ : s.val+2 ≤ Λ) (_hlo : 0 < βlo) (hβ : βlo ≤ β.val) :
    let W := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      -Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (y,z)).toReal)
    let H := fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) =>
      β.val • (InterpolationMatrix.penaltyHessian n θ ε x.val+β.val⁻¹ • hessianMatrix W x.val)
    ∀ x, (H x).PosSemidef ∧ ∀ z : Fin (n : ℕ) → ℝ,
      ((βlo*min 1 (s.val*(s.val+1)))*(n : ℝ)^(-(Λ*η)))*(∑ i, z i^2) ≤
        ∑ i, ∑ j, z i*H x i j*z j := by
  intro W H x
  obtain ⟨_, hphysical⟩ := long_twoSided_matrix_internal β s n m θ ε hε
  have heq : H x = hessianMatrix
      (fun y => β.val*∑ i, (θ.val ((n : ℝ)^(-ε)*y i)+θ.val ((n : ℝ)^(-ε)*(y i)⁻¹)) + W y) x.val :=
    (long_native_matrix_identity_internal β s n m θ ε x).symm
  rw [heq]
  refine ⟨(hphysical x).1, fun z => le_trans ?_ ((hphysical x).2 z)⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hc : 0 < min 1 (s.val*(s.val+1)) := by have := s.property.1; positivity
  have hβpos := β.property
  gcongr
  nlinarith only [mul_le_mul_of_nonneg_left hεη (by linarith [s.property.1] : 0 ≤ s.val+2),
    mul_le_mul_of_nonneg_right hΛ hη]

/-- See the proof of Lemma 6.5 in the paper: point and increment
profiles increase to the common loss without changing their remainder. -/
theorem native_profile_loss_mono_internal (n : ℕ+) (a b A Err z d w r F G : ℝ)
    (hab : a ≤ b) (hA : 0 ≤ A) (hd : 0 ≤ d) (hw : 0 ≤ w) (hr : 0 ≤ r)
    (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hz : |z| ≤ A*(n : ℝ)^a*d*w*r*F*G+Err) :
    |z| ≤ (A*(n : ℝ)^b)*w*d*r*F*G+Err := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hp := Real.rpow_le_rpow_of_exponent_le hn1 hab
  apply hz.trans
  calc
    _ ≤ A*(n : ℝ)^b*d*w*r*F*G+Err := by gcongr
    _ = _ := by ring

/-- See the proof of Lemma 6.5 in the paper: uniform long physical
comparison on any conditional retained law with finite weighted error.
The matrix bounds, its Schur solution, all auxiliary estimates,
physical entry integrability and native perturbation bounds are proved
here. Only the standing closed conservative scalar form is supplied.
The exceptional exponent remains explicit until `C₀` is fixed. -/
theorem long_conditional_comparison_internal
    (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (κ₀ : ℝ) (hκ₀ : 1 ≤ κ₀) (h : ℕ+) :
    ∃ Λ : ℝ, 0 < Λ ∧
    ∀ η : ℝ, 0 < η → η ≤ 1-s.val/2 →
    ∀ (θ : PhysicalCutoff) (βlo βhi : ℝ), 0 < βlo → βlo ≤ βhi →
    ∃ D E T : ℝ, 0 < D ∧ 0 < E ∧ 0 < T ∧
    ∀ (β : InverseTemperature), β.val ∈ Icc βlo βhi →
    ∀ (n : ℕ+) (m : ℕ), 2 ≤ (n : ℕ) → 4*(n : ℕ) ≤ (n : ℕ)+m+1 →
    ∀ (M : ℕ+) (_hM : 2 ≤ (M : ℕ)) (_hnM : (n : ℕ) ≤ (M : ℕ)),
      2*(n : ℕ) ≤ (M : ℕ) → (M : ℕ) ≤ (n : ℕ)+m+1 →
      (n : ℝ)^(1/2+1/s.val) ≤ (M : ℝ) →
      (M : ℝ) ≤ 2*(n : ℝ)^(1/2+1/s.val) →
    ∀ ε C₀ : ℝ, 0 ≤ ε → ε ≤ η →
    let k := ⌊(n : ℝ)^η⌋₊^(h : ℕ)
    ∀ (_hk : 1 ≤ k), 4*k ≤ (M : ℕ) →
    ∀ (ν : Measure (AffineSimplex.chartDomain n ((n+m : ℕ)+1))) [IsProbabilityMeasure ν],
      (∫⁻ x in (longFineEvent β s n m η κ₀)ᶜ,
        ENNReal.ofReal (longEnvelope β s n m θ ε C₀ x) ∂ν) ≠ (∞ : ℝ≥0∞) →
    ∀ (Q : ScalarFormData ν) (_hQ : IsClosedScalarDirichletForm Q),
      IsConservativeScalarForm Q →
    ∀ i₀ : Fin (n : ℕ), |(i₀.val : ℝ)+1-(n : ℝ)/2| ≤ (n : ℝ)/4 →
    ∀ (χ : Lp ℝ 2 ν) (B : ℝ), 0 ≤ B → (∀ᵐ x ∂ν, |χ x| ≤ B) →
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      β.val*∑ i, (θ.val ((n : ℝ)^(-ε)*x i)+θ.val ((n : ℝ)^(-ε)*(x i)⁻¹)) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (x,z)).toReal)
    let H := fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) => hessianMatrix V x.val
    let e := (∫⁻ x in (longFineEvent β s n m η κ₀)ᶜ,
      ENNReal.ofReal (longEnvelope β s n m θ ε C₀ x) ∂ν).toReal
    ∃ v : Fin (n : ℕ) → Q.1,
    (∀ j : Fin (n : ℕ), ‖(v j).val‖ ≤ D*(n : ℝ)^(Λ*η)*
      (1+(Nat.dist j.val i₀.val : ℝ))^(s.val-2)*‖χ‖) ∧
    (∑ j, ‖(v j).val‖) ≤ D*(n : ℝ)^(Λ*η)*‖χ‖ ∧
    ‖(∑ j, v j : Q.1).val‖ ≤ D*(n : ℝ)^(Λ*η-(1-s.val))*‖χ‖ ∧
    Real.sqrt (Q.2 (∑ j, v j) (∑ j, v j)) ≤
      D*(n : ℝ)^(Λ*η-(1-s.val)/2)*‖χ‖ ∧
    (∀ j : Fin (n : ℕ), ∀ᵐ x ∂ν, |(v j).val x| ≤ D*(n : ℝ)^(Λ*η)*B) ∧
    ∀ ψ : Fin (n : ℕ) → Q.1,
      WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ)))
        (fun i => if i = i₀ then χ else 0) ψ →
      ‖WithLp.toLp 2 (fun i => (ψ i).val-(v i).val)‖^2 ≤
        E*(n : ℝ)^(8*(Λ*η)-1)*‖χ‖^2 +
          T*(n : ℝ)^(3+2/s.val+4*(Λ*η)-C₀)*e*B^2 := by
  let κstar := (s.val+7+(h : ℝ))+(s.val+2+(h : ℝ)*(1+s.val))
  let γstar := (h : ℝ)+1
  have hκstar : 0 < κstar := by dsimp only [κstar]; have := s.property.1; positivity
  have hγstar : 0 < γstar := by dsimp only [γstar]; positivity
  obtain ⟨κa, hκa, ha⟩ := FixedLengthDecay.schur_on_scalar_form_internal hz s κstar γstar h
    hκstar hγstar
  obtain ⟨κp, hκp, hp⟩ := conditional_long_native_data_internal hz s κ₀ hκ₀ (h : ℕ)
  let Λ := s.val+2+κstar+κa+κp
  have hΛ : 0 < Λ := by dsimp only [Λ]; have := s.property.1; positivity
  have hΛa : κa ≤ Λ := by dsimp only [Λ]; linarith [s.property.1]
  have hΛp : κp ≤ Λ := by dsimp only [Λ]; linarith [s.property.1]
  have hΛm : κstar ≤ Λ := by dsimp only [Λ]; linarith [s.property.1]
  have hΛs : s.val+2 ≤ Λ := by dsimp only [Λ]; linarith
  refine ⟨Λ, hΛ, ?_⟩
  intro η hη hηs θ βlo βhi hlo hle
  obtain ⟨Cstar, hCstar, hb⟩ := InterpolationMatrix.matrix_bounds s θ (h : ℕ)
  obtain ⟨D, hD, ha⟩ := ha η hη Cstar hCstar βlo βhi hlo hle
  obtain ⟨A, Derr, hA, hDerr, hp⟩ := hp η βlo βhi hη hlo hle
  let a0 := βlo*min 1 (s.val*(s.val+1))
  have ha0 : 0 < a0 := by dsimp only [a0]; have := s.property.1; positivity
  let K := 2*8^(2-s.val)*(2/(1-s.val/2))+8^(1+s.val/2)*(2/s.val)+4^(s.val/2)
  let L0 := (K*Real.sqrt (2/(1-s.val)))*A*D
  let K0 := βhi*(Cstar*(1+1/s.val)*(2/(1-s.val)))+A*(2/(1-s.val/2))^2
  let E := 3*((2*L0/a0)^2+(1+K0)*D^2/a0+D^2)
  let T := 9*(3*Derr*(2*D+a0⁻¹)*D+Derr*D^2)/a0
  have hT : 0 < T := by dsimp only [T]; positivity
  have hK0 : 0 ≤ K0 := by
    dsimp only [K0]
    have := s.property.1
    have := sub_pos.mpr s.property.2
    have : 0 < βhi := hlo.trans_le hle
    positivity
  have hE : 0 < E := by dsimp only [E]; positivity
  refine ⟨D, E, T, hD, hE, hT, ?_⟩
  intro β hβ n m hn hvol M hM hnM hhalf hMN hscale hupper ε C₀ hε hεη k hk hkm ν _ he Q hQ hcon i₀ hi₀ χ B hB hχ V H e
  have hn0 : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hkm' : k ≤ (M : ℕ)/4 := by omega
  let Afield := InterpolationMatrix.matrix β s n m m le_rfl M hM hnM k θ ε η 0
  have hmat : PeriodizedMatrixBounds (ν := ν) s n M hM k Cstar κstar γstar η Afield := by
    exact hb β n m m le_rfl hvol M hM hhalf hMN hscale ε η 0 hε hη.le hηs
      le_rfl zero_le_one hkm' ν
  have hauxAll := ha β hβ n M hn hM hhalf hupper hk hkm _ ν Q hQ hcon
    Afield hmat i₀ hi₀ χ B hB hχ
  obtain ⟨hex, haest⟩ := hauxAll
  obtain ⟨vaux, hvaux, _⟩ := hex
  let v := MatrixEnergy.vectorEquiv Q hQ vaux
  have hauxEst := haest vaux hvaux
  have hnormalized := auxiliary_loss_mono_internal Q s.val n i₀ χ v D B (κa*η) (Λ*η)
    hD.le hB (mul_le_mul_of_nonneg_right hΛa hη.le) hauxEst
  obtain ⟨hvalue', hsum', hmean', hgrad', hsup'⟩ := hnormalized
  refine ⟨v, hvalue', hsum', hmean', hgrad', hsup', ?_⟩
  intro ψ hψ
  let W := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
    -Real.log (∫ z : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (y,z)).toReal)
  let P := fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) => β.val⁻¹ • hessianMatrix W x.val
  let Hnat := fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) =>
    β.val • (InterpolationMatrix.penaltyHessian n θ ε x.val+P x)
  let Y := InterpolationMatrix.multiplicationPart β s n m m le_rfl M hM hnM k θ ε η 0 P
  have hHnat : Hnat = H := by
    funext x
    exact (long_native_matrix_identity_internal β s n m θ ε x).symm
  have hupper' : (M : ℝ) ≤ 3*(n : ℝ)^(1/2+1/s.val) := by linarith [Real.rpow_pos_of_pos hn0 (1/2+1/s.val)]
  have hnper : 2*(n : ℕ) ≤ (n : ℕ)+m+1 := by omega
  have hdataAll := hp β hβ n m hnper M hM hnM hhalf hupper' hk hkm' θ ε C₀ ν he Q hQ
  have hPm := hdataAll.1
  have hYi := hdataAll.2.1
  have htests := hdataAll.2.2
  have hpp : (n : ℝ)^(κp*η) ≤ (n : ℝ)^(Λ*η) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (mul_le_mul_of_nonneg_right hΛp hη.le)
  have hpoint (φ ζ : BoundedL2Pairings.boundedSubmodule ν) (j i : Fin (n : ℕ)) :=
    (htests φ ζ j i i).2.2.1
  have hinc (φ ζ : BoundedL2Pairings.boundedSubmodule ν) (j i l : Fin (n : ℕ)) :=
    (htests φ ζ j i l).2.2.2
  have hHi := long_native_entries_internal β s n m M hM hnM k θ ε η Cstar κstar γstar ν P hmat hYi
  have hphys := long_native_coercivity_internal β s n m θ ε η Λ βlo hε hεη hη.le hΛs hlo hβ.1
  have hH : ∀ᵐ x ∂ν, (Hnat x).PosSemidef := ae_of_all _ fun x => (hphys x).1
  have hlower : ∀ᵐ x ∂ν, ∀ z : Fin (n : ℕ) → ℝ,
      (a0*(n : ℝ)^(-(Λ*η)))*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*Hnat x i j*z j :=
    ae_of_all _ fun x => (hphys x).2
  have hsumshape : ‖(∑ i, v i : Q.1).val‖ ≤
      (D*(n : ℝ)^(Λ*η))*(n : ℝ)^(-(1-s.val))*‖χ‖ := by
    apply hmean'.trans_eq
    rw [show Λ*η-(1-s.val) = Λ*η+(-(1-s.val)) by ring, Real.rpow_add hn0]
    ring
  have haux : ∀ z, SchurRestriction.schurForm Q hQ n M hnM s hM k Cstar κstar γstar η
      β.val hCstar β.property Afield hmat ((MatrixEnergy.vectorEquiv Q hQ).symm v) z =
      inner ℝ (WithLp.toLp 2 (fun i => if i = i₀ then χ else 0))
        (OperatorSchur.vectorValues Q hQ z) := by
    simpa only [v, LinearEquiv.symm_apply_apply] using hvaux
  have hh := conditional_native_square_internal β s n m m le_rfl M hM hhalf k hk hkm'
    θ ε η 0 ν Q hQ P Cstar κstar γstar hCstar hmat hPm hH hHi hYi
    (Λ*η) a0 D D A Derr e (1+2/s.val) C₀ βhi (mul_pos hΛ hη).le ha0
    hD.le hD.le hA.le hDerr.le ENNReal.toReal_nonneg hβ.2
    (mul_le_mul_of_nonneg_right hΛm hη.le) hlower i₀ hi₀ χ B hB hχ ψ v
    (by
      change WeightedWeakSolution Q Hnat _ _ ψ
      rw [hHnat]
      exact hψ) hsup'  hvalue' hsumshape hgrad' haux
    (fun φ ζ j i => by
      have hh := native_profile_loss_mono_internal n (κp*η) (Λ*η) A
        ((Derr*(n : ℝ)^(1+2/s.val-C₀)*e)*
          (eLpNorm (φ.val : _ → ℝ) ∞ ν).toReal*(eLpNorm (ζ.val : _ → ℝ) ∞ ν).toReal)
        _ (((min (i.val+1) ((n : ℕ)-i.val) : ℕ) : ℝ)^(-s.val/2))
        (((min (j.val+1) ((n : ℕ)-j.val) : ℕ) : ℝ)^(-s.val/2)) 1 ‖φ.val‖ ‖ζ.val‖
        (mul_le_mul_of_nonneg_right hΛp hη.le) hA.le (by positivity) (by positivity)
        zero_le_one (norm_nonneg _) (norm_nonneg _)
        (by convert hpoint φ ζ j i using 1; ring)
      simpa only [mul_one, InteractionDifferential.boundaryWeight_long s.property.2] using hh)
    (fun φ ζ j i l => by
      simp only [InteractionDifferential.boundaryWeight_long s.property.2]
      apply native_profile_loss_mono_internal n (κp*η) (Λ*η) A _ _
        (Nat.dist i.val l.val : ℝ)
        (((min (j.val+1) ((n : ℕ)-j.val) : ℕ) : ℝ)^(-s.val/2))
        ((min ((min (i.val+1) ((n : ℕ)-i.val) : ℕ) : ℝ)
          ((min (l.val+1) ((n : ℕ)-l.val) : ℕ) : ℝ))^(-1-s.val/2)) ‖φ.val‖ ‖ζ.val‖
        (mul_le_mul_of_nonneg_right hΛp hη.le) hA.le (by positivity) (by positivity)
        (by positivity) (norm_nonneg _) (norm_nonneg _)
      exact hinc φ ζ j i l)
  have hexp : 2+4*(Λ*η)+(1+2/s.val)-C₀ = 3+2/s.val+4*(Λ*η)-C₀ := by ring
  simpa only [E, T, K, L0, K0, hexp] using hh

/-- See the proof of Lemma 6.5 and equation (6.23) of the paper:
the long conditional physical fibre sums, with volume-free exceptional
coefficients after a single uniform envelope-exponent choice. -/
theorem long_conditional_fibre_sums_internal
    (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (κ₀ : ℝ) (hκ₀ : 1 ≤ κ₀) (h : ℕ+) :
    ∃ κ b : ℝ, 0 < κ ∧ 0 < b ∧
    ∀ η : ℝ, 0 < η → η ≤ 1-s.val/2 →
    ∀ (θ : PhysicalCutoff) (βlo βhi : ℝ), 0 < βlo → βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧
    ∀ (β : InverseTemperature), β.val ∈ Icc βlo βhi →
    ∀ (n : ℕ+) (m : ℕ), 2 ≤ (n : ℕ) → 4*(n : ℕ) ≤ (n : ℕ)+m+1 →
    ∀ (M : ℕ+) (_hM : 2 ≤ (M : ℕ)) (_hnM : (n : ℕ) ≤ (M : ℕ)),
      2*(n : ℕ) ≤ (M : ℕ) → (M : ℕ) ≤ (n : ℕ)+m+1 →
      (n : ℝ)^(1/2+1/s.val) ≤ (M : ℝ) →
      (M : ℝ) ≤ 2*(n : ℝ)^(1/2+1/s.val) →
    ∀ ε C₀ Ptail : ℝ, 0 ≤ ε → ε ≤ η → 1/2 ≤ Ptail → b+2*Ptail ≤ C₀ →
    let k := ⌊(n : ℝ)^η⌋₊^(h : ℕ)
    ∀ (_hk : 1 ≤ k), 4*k ≤ (M : ℕ) →
    ∀ (ν : Measure (AffineSimplex.chartDomain n ((n+m : ℕ)+1))) [IsProbabilityMeasure ν],
      (∫⁻ x in (longFineEvent β s n m η κ₀)ᶜ,
        ENNReal.ofReal (longEnvelope β s n m θ ε C₀ x) ∂ν) ≠ (∞ : ℝ≥0∞) →
    ∀ (Q : ScalarFormData ν) (_hQ : IsClosedScalarDirichletForm Q),
      IsConservativeScalarForm Q →
    ∀ i₀ : Fin (n : ℕ), |(i₀.val : ℝ)+1-(n : ℝ)/2| ≤ (n : ℝ)/4 →
    ∀ (χ : Lp ℝ 2 ν) (B : ℝ), 0 ≤ B → (∀ᵐ x ∂ν, |χ x| ≤ B) →
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      β.val*∑ i, (θ.val ((n : ℝ)^(-ε)*x i)+θ.val ((n : ℝ)^(-ε)*(x i)⁻¹)) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (x,z)).toReal)
    let H := fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) => hessianMatrix V x.val
    let e := (∫⁻ x in (longFineEvent β s n m η κ₀)ᶜ,
      ENNReal.ofReal (longEnvelope β s n m θ ε C₀ x) ∂ν).toReal
    ∀ ψ : Fin (n : ℕ) → Q.1,
      WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ)))
        (fun i => if i = i₀ then χ else 0) ψ →
    (∑ j, InteractionDifferential.boundaryWeight s.val n j*‖(ψ j).val‖) ≤
      C*(n : ℝ)^(κ*η-s.val/2)*‖χ‖+C*B*Real.sqrt e ∧
    (∑ j, ‖(ψ j).val‖) ≤ C*(n : ℝ)^(κ*η)*‖χ‖+C*B*Real.sqrt e := by
  obtain ⟨Λ, hΛ, hcomp⟩ := long_conditional_comparison_internal hz s κ₀ hκ₀ h
  let b := 3+2/s.val+4*Λ
  have hb : 0 < b := by dsimp only [b]; have := s.property.1; positivity
  refine ⟨4*Λ, b, by positivity, hb, ?_⟩
  intro η hη hηs θ βlo βhi hlo hle
  obtain ⟨D, E, T, hD, hE, hT, hcomp⟩ := hcomp η hη hηs θ βlo βhi hlo hle
  let K := 8^(2-s.val)*(2/(1-s.val/2))+8^(s.val/2)
  let W := 2/(1-s.val)
  have hW : 0 < W := by dsimp only [W]; exact div_pos (by norm_num) (sub_pos.mpr s.property.2)
  have hK : 0 < K := by
    dsimp only [K]
    have : 0 < 1-s.val/2 := by linarith [s.property.2]
    positivity
  let C := 1+K*D+D+(Real.sqrt W+1)*(Real.sqrt E+Real.sqrt T)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro β hβ n m hn hvol M hM hnM hhalf hMN hscale hupper ε C₀ Ptail hε hεη hP hC₀ k hk hkm ν _ he Q hQ hcon i₀ hi₀ χ B hB hχ V H e ψ hψ
  have hcomp' := hcomp β hβ n m hn hvol M hM hnM hhalf hMN hscale hupper ε C₀ hε hεη hk hkm ν he Q hQ hcon i₀ hi₀ χ B hB hχ
  obtain ⟨v, hv, hs, hm, hg, hsup, hc⟩ := hcomp'
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hη1 : η ≤ 1 := by linarith [s.property.1]
  have herr := conditional_square_absorption_internal n Λ η (1+2/s.val) C₀ Ptail E T ‖χ‖ B e _
    hΛ.le hη1 hT.le ENNReal.toReal_nonneg
    (by dsimp only [b] at hC₀; linarith only [hC₀])
    (by simpa only [show 2+4*(Λ*η)+(1+2/s.val)-C₀ = 3+2/s.val+4*(Λ*η)-C₀ by ring] using hc ψ hψ)
  have hp : (n : ℝ)^(Λ*η) ≤ (n : ℝ)^((4*Λ)*η) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith only [mul_pos hΛ hη])
  have hv' (j) : ‖(v j).val‖ ≤ D*(n : ℝ)^((4*Λ)*η)*
      (1+(Nat.dist j.val i₀.val : ℝ))^(s.val-2)*‖χ‖ := (hv j).trans (by gcongr)
  have hs' : (∑ j, ‖(v j).val‖) ≤ D*(n : ℝ)^((4*Λ)*η)*‖χ‖ := hs.trans (by gcongr)
  have hf := conditional_long_fibre_sums_internal s n i₀ hi₀ D E T ((4*Λ)*η) Ptail ‖χ‖ B e
    hD.le hE.le hT.le (norm_nonneg _) hB ENNReal.toReal_nonneg hP
    (fun j => (ψ j).val) (fun j => (v j).val) hv' hs' herr
  have hCw : K*D+Real.sqrt W*Real.sqrt E ≤ C := by
    dsimp only [C]
    nlinarith only [Real.sqrt_nonneg E, Real.sqrt_nonneg T, Real.sqrt_nonneg W,
      mul_nonneg (Real.sqrt_nonneg W) (Real.sqrt_nonneg T), hD.le]
  have hCu : D+Real.sqrt E ≤ C := by
    dsimp only [C]
    nlinarith only [Real.sqrt_nonneg E, Real.sqrt_nonneg T, Real.sqrt_nonneg W,
      mul_nonneg (Real.sqrt_nonneg W) (Real.sqrt_nonneg E),
      mul_nonneg (Real.sqrt_nonneg W) (Real.sqrt_nonneg T), mul_nonneg hK.le hD.le]
  have hCt : Real.sqrt T ≤ C := by
    dsimp only [C]
    nlinarith only [Real.sqrt_nonneg E, Real.sqrt_nonneg W,
      mul_nonneg (Real.sqrt_nonneg W) (Real.sqrt_nonneg E),
      mul_nonneg (Real.sqrt_nonneg W) (Real.sqrt_nonneg T), mul_nonneg hK.le hD.le, hD.le]
  have hCwt : Real.sqrt W*Real.sqrt T ≤ C := by
    dsimp only [C]
    nlinarith only [Real.sqrt_nonneg E, Real.sqrt_nonneg T,
      mul_nonneg (Real.sqrt_nonneg W) (Real.sqrt_nonneg E), mul_nonneg hK.le hD.le, hD.le]
  refine ⟨hf.1.trans ?_, hf.2.trans (by gcongr)⟩
  change (K*D+Real.sqrt W*Real.sqrt E)*(n : ℝ)^((4*Λ)*η-s.val/2)*‖χ‖+
    Real.sqrt W*Real.sqrt T*B*Real.sqrt e ≤ _
  gcongr


/-- See the proof of Lemma 6.5 in the paper: the uniform squared
physical long comparison in the precise form consumed by the fibre-sum
transfer. The envelope is chosen once, after every conditional loss. -/
theorem long_conditional_square_internal
    (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (κ₀ : ℝ) (hκ₀ : 1 ≤ κ₀) (h : ℕ+) :
    ∃ κ b : ℝ, 0 < κ ∧ 0 < b ∧
    ∀ η : ℝ, 0 < η → η ≤ 1-s.val/2 →
    ∀ (θ : PhysicalCutoff) (βlo βhi : ℝ), 0 < βlo → βlo ≤ βhi →
    ∃ D E T : ℝ, 0 < D ∧ 0 < E ∧ 0 < T ∧
    ∀ (β : InverseTemperature), β.val ∈ Icc βlo βhi →
    ∀ (n : ℕ+) (m : ℕ), 2 ≤ (n : ℕ) → 4*(n : ℕ) ≤ (n : ℕ)+m+1 →
    ∀ (M : ℕ+) (_hM : 2 ≤ (M : ℕ)) (_hnM : (n : ℕ) ≤ (M : ℕ)),
      2*(n : ℕ) ≤ (M : ℕ) → (M : ℕ) ≤ (n : ℕ)+m+1 →
      (n : ℝ)^(1/2+1/s.val) ≤ (M : ℝ) →
      (M : ℝ) ≤ 2*(n : ℝ)^(1/2+1/s.val) →
    ∀ ε C₀ Ptail : ℝ, 0 ≤ ε → ε ≤ η → 1/2 ≤ Ptail → b+2*Ptail ≤ C₀ →
    let k := ⌊(n : ℝ)^η⌋₊^(h : ℕ)
    ∀ (_hk : 1 ≤ k), 4*k ≤ (M : ℕ) →
    ∀ (ν : Measure (AffineSimplex.chartDomain n ((n+m : ℕ)+1))) [IsProbabilityMeasure ν],
      (∫⁻ x in (longFineEvent β s n m η κ₀)ᶜ,
        ENNReal.ofReal (longEnvelope β s n m θ ε C₀ x) ∂ν) ≠ (∞ : ℝ≥0∞) →
    ∀ (Q : ScalarFormData ν) (_hQ : IsClosedScalarDirichletForm Q),
      IsConservativeScalarForm Q →
    ∀ i₀ : Fin (n : ℕ), |(i₀.val : ℝ)+1-(n : ℝ)/2| ≤ (n : ℝ)/4 →
    ∀ (χ : Lp ℝ 2 ν) (B : ℝ), 0 ≤ B → (∀ᵐ x ∂ν, |χ x| ≤ B) →
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      β.val*∑ i, (θ.val ((n : ℝ)^(-ε)*x i)+θ.val ((n : ℝ)^(-ε)*(x i)⁻¹)) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (x,z)).toReal)
    let H := fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) => hessianMatrix V x.val
    let e := (∫⁻ x in (longFineEvent β s n m η κ₀)ᶜ,
      ENNReal.ofReal (longEnvelope β s n m θ ε C₀ x) ∂ν).toReal
    ∃ v : Fin (n : ℕ) → Q.1,
    (∀ j : Fin (n : ℕ), ‖(v j).val‖ ≤ D*(n : ℝ)^(κ*η)*
      (1+(Nat.dist j.val i₀.val : ℝ))^(s.val-2)*‖χ‖) ∧
    (∑ j, ‖(v j).val‖) ≤ D*(n : ℝ)^(κ*η)*‖χ‖ ∧
    ‖(∑ j, v j : Q.1).val‖ ≤ D*(n : ℝ)^(κ*η-(1-s.val))*‖χ‖ ∧
    Real.sqrt (Q.2 (∑ j, v j) (∑ j, v j)) ≤
      D*(n : ℝ)^(κ*η-(1-s.val)/2)*‖χ‖ ∧
    (∀ j : Fin (n : ℕ), ∀ᵐ x ∂ν, |(v j).val x| ≤ D*(n : ℝ)^(κ*η)*B) ∧
    ∀ ψ : Fin (n : ℕ) → Q.1,
      WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ)))
        (fun i => if i = i₀ then χ else 0) ψ →
      ‖WithLp.toLp 2 (fun i => (ψ i).val-(v i).val)‖^2 ≤
        E*(n : ℝ)^(2*(κ*η)-1)*‖χ‖^2 +
          T*(n : ℝ)^(-2*Ptail)*B^2*e := by
  obtain ⟨Λ, hΛ, hcomp⟩ := long_conditional_comparison_internal hz s κ₀ hκ₀ h
  let b := 3+2/s.val+4*Λ
  have hb : 0 < b := by dsimp only [b]; have := s.property.1; positivity
  refine ⟨4*Λ, b, by positivity, hb, ?_⟩
  intro η hη hηs θ βlo βhi hlo hle
  obtain ⟨D, E, T, hD, hE, hT, hcomp⟩ := hcomp η hη hηs θ βlo βhi hlo hle
  refine ⟨D, E, T, hD, hE, hT, ?_⟩
  intro β hβ n m hn hvol M hM hnM hhalf hMN hscale hupper ε C₀ Ptail hε hεη hP hC₀ k hk hkm ν _ he Q hQ hcon i₀ hi₀ χ B hB hχ V H e
  have hcomp' := hcomp β hβ n m hn hvol M hM hnM hhalf hMN hscale hupper ε C₀ hε hεη hk hkm ν he Q hQ hcon i₀ hi₀ χ B hB hχ
  obtain ⟨v, hv, hs, hm, hg, hsup, hc⟩ := hcomp'
  have hn := auxiliary_loss_mono_internal Q s.val n i₀ χ v D B (Λ*η) ((4*Λ)*η)
    hD.le hB (by nlinarith only [mul_pos hΛ hη]) ⟨hv, hs, hm, hg, hsup⟩
  refine ⟨v, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2, ?_⟩
  intro ψ hψ
  have hη1 : η ≤ 1 := by linarith [s.property.1]
  exact conditional_square_absorption_internal n Λ η (1+2/s.val) C₀ Ptail E T ‖χ‖ B e _
    hΛ.le hη1 hT.le ENNReal.toReal_nonneg
    (by dsimp only [b] at hC₀; linarith only [hC₀])
    (by simpa only [show 2+4*(Λ*η)+(1+2/s.val)-C₀ = 3+2/s.val+4*(Λ*η)-C₀ by ring] using hc ψ hψ)

/-- See the proof of Lemma 6.5 in the paper: the actual capped
reference period has the required lower scale under the volume
assumption of the paper, including when the cap is attained. -/
theorem long_reference_scale_internal (s : Riesz1.RieszExponent) (n N : ℕ+)
    (hvol : 4*(n : ℕ) ≤ (N : ℕ)) (hpow : (n : ℝ)^(2/s.val) ≤ (N : ℝ)) :
    (n : ℝ)^(1/2+1/s.val) ≤ (PhysicalCore.properReferencePeriod s n N : ℝ) := by
  have hhalf : 2*(n : ℕ) ≤ (N : ℕ) := by omega
  rcases (PhysicalCore.properReferencePeriod_bounds s n N hhalf).2.2 with heq | hs
  · rw [heq]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
    have hi : 1 ≤ 1/s.val := (le_div_iff₀ s.property.1).mpr (by linarith [s.property.2])
    have hexp : 1/2+1/s.val ≤ 2/s.val := by
      calc
        1/2+1/s.val ≤ 2*(1/s.val) := by linarith
        _ = 2/s.val := by ring
    exact (Real.rpow_le_rpow_of_exponent_le hn1 hexp).trans hpow
  · exact hs

/-- See the proof of Lemma 6.5 and equation (6.23) of the paper:
long physical sums on almost every actual retained marginal length fibre.
The cutoff and period are the prescribed ones. Their size conditions are
proved from the volume assumptions of the paper. The exceptional error is the
literal `longRemainder`, proved finite before conversion to real numbers.
This form-level specialization applies in particular to the intrinsic
retained form constructed in Part5. -/
theorem retained_long_fibre_sums_internal
    (hz : External.PeriodicZeta) (hRig : External.LongRangeRigidityLocallyUniform)
    (s : Riesz1.RieszExponent) (κ₀ : ℝ) (hκ₀ : 1 ≤ κ₀) (h : ℕ+) :
    ∃ κ b η₀ : ℝ, 0 < κ ∧ 0 < b ∧ 0 < η₀ ∧
    ∀ η : ℝ, 0 < η → η ≤ η₀ →
    ∀ (θ : PhysicalCutoff) (βlo βhi : ℝ), 0 < βlo → βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    ∀ n m : ℕ, 1 ≤ n → 4*(n+1) ≤ n+1+m+1 →
      (n+1 : ℝ)^(2/s.val) ≤ ((n+1+m : ℕ)+1 : ℝ) →
    ∀ ε C₀ Ptail : ℝ, 0 < ε → ε ≤ η → 1/2 ≤ Ptail → b+2*Ptail ≤ C₀ →
    ∀ᵐ L ∂lengthMeasure (ofLong β s) n m θ ε,
    let ν := retainedKernel (ofLong β s) n m θ ε L
    let V := fun x : EuclideanSpace ℝ (Fin (n+1)) =>
      β.val*∑ i, (θ.val ((n+1 : ℝ)^(-ε)*x i)+θ.val ((n+1 : ℝ)^(-ε)*(x i)⁻¹)) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity (ofLong β s) (n+1) m (Equiv.refl _) (x,z)).toReal)
    let H := fun x : AffineSimplex.chartDomain (n+1) ((n+1+m : ℕ)+1) => hessianMatrix V x.val
    let e := (longRemainder β s n m θ ε C₀ η κ₀ L).toReal
    (longRemainder β s n m θ ε C₀ η κ₀ L < (∞ : ℝ≥0∞)) ∧
    ∀ (Q : ScalarFormData ν) (_hQ : IsClosedScalarDirichletForm Q),
      IsConservativeScalarForm Q →
    ∀ i₀ : Fin (n+1), |(i₀.val : ℝ)+1-(n+1 : ℝ)/2| ≤ (n+1 : ℝ)/4 →
    ∀ (χ : Lp ℝ 2 ν) (B : ℝ), 0 ≤ B → (∀ᵐ x ∂ν, |χ x| ≤ B) →
    (∃! ψ : Fin (n+1) → Q.1, WeightedWeakSolution Q H
      (zeroSumComponents (Fin (n+1))) (fun i => if i = i₀ then χ else 0) ψ) ∧
    ∀ ψ : Fin (n+1) → Q.1,
      WeightedWeakSolution Q H (zeroSumComponents (Fin (n+1)))
        (fun i => if i = i₀ then χ else 0) ψ →
    (∑ j, InteractionDifferential.boundaryWeight s.val n.succPNat j*‖(ψ j).val‖) ≤
      C*(n+1 : ℝ)^(κ*η-s.val/2)*‖χ‖+C*B*Real.sqrt e ∧
    (∑ j, ‖(ψ j).val‖) ≤ C*(n+1 : ℝ)^(κ*η)*‖χ‖+C*B*Real.sqrt e := by
  obtain ⟨κ, b, hκ, hb, hsums⟩ := long_conditional_fibre_sums_internal hz s κ₀ hκ₀ h
  let η₀ := min (1-s.val/2) (1/(4*(h : ℝ)))
  have hη₀ : 0 < η₀ := by
    dsimp only [η₀]
    have : 0 < 1-s.val/2 := by linarith [s.property.2]
    positivity
  refine ⟨κ, b, η₀, hκ, hb, hη₀, ?_⟩
  intro η hη hsmall θ βlo βhi hlo hle
  have hηs : η ≤ 1-s.val/2 := hsmall.trans (min_le_left _ _)
  have hprod : (h : ℝ)*η ≤ 1/4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*(h : ℝ))).mp
      (hsmall.trans (min_le_right _ _))
    nlinarith only [hh]
  obtain ⟨C, hC, hsums⟩ := hsums η hη hηs θ βlo βhi hlo hle
  refine ⟨C, hC, ?_⟩
  intro β hβ n m hn hvol hpow ε C₀ Ptail hε hεη hP hC₀
  let nA := n.succPNat
  let N := (n+1+m).succPNat
  have hnA : 2 ≤ (nA : ℕ) := by dsimp only [nA, Nat.succPNat_coe]; omega
  have hvol' : 4*(nA : ℕ) ≤ (N : ℕ) := hvol
  have hhalfN : 2*(n+1) ≤ n+1+m+1 := by omega
  have hpow' : (nA : ℝ)^(2/s.val) ≤ (N : ℝ) := by
    simpa only [nA, N, Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using hpow
  let M := PhysicalCore.properReferencePeriod s nA N
  have hmb := PhysicalCore.properReferencePeriod_bounds s nA N (by omega)
  have hM : 2 ≤ (M : ℕ) := by dsimp only [M]; have := hmb.1; have := nA.pos; omega
  have hnM : (nA : ℕ) ≤ (M : ℕ) := by dsimp only [M]; have := hmb.1; omega
  have hscale := long_reference_scale_internal s nA N hvol' hpow'
  have hupper : (M : ℝ) ≤ 2*(nA : ℝ)^(1/2+1/s.val) := by
    exact PhysicalMean.proper_period_upper_internal s nA N
  obtain ⟨hk, hkm⟩ := AuxiliaryMean.interpolation_cutoff_bounds_internal nA M hnA hmb.1 η (h : ℕ) hη.le hprod
  have hC₀0 : 0 ≤ C₀ := by linarith only [hb, hP, hC₀]
  have hfinite := longRemainder_finite_ae hRig β s n m θ ε η C₀ κ₀ hε hεη hC₀0 hκ₀ hn hhalfN
  filter_upwards [hfinite] with L hL
  intro ν V H e
  refine ⟨hL, ?_⟩
  intro Q hQ hcon i₀ hi₀ χ B hB hχ
  refine ⟨(long_retained_tangent_solution_internal β s n m θ ε hε.le L Q hQ i₀ χ).1, ?_⟩
  have he : (∫⁻ x in (longFineEvent β s nA m η κ₀)ᶜ,
      ENNReal.ofReal (longEnvelope β s nA m θ ε C₀ x) ∂ν) ≠ (∞ : ℝ≥0∞) := hL.ne
  have hs := hsums β hβ nA m hnA hvol' M hM hnM hmb.1 hmb.2.1 hscale hupper ε C₀ Ptail
    hε.le hεη hP hC₀ hk hkm ν he Q hQ hcon i₀
    (by simpa only [nA, Nat.succPNat_coe, Nat.cast_succ] using hi₀) χ B hB hχ
  simpa only [ν, V, H, e, nA, Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one,
    longRemainder, retainedExceptionalMass] using hs

/-- See the proof of Lemma 6.5 in the paper, auxiliary supremum step:
the Schur solution has the full Euclidean vector supremum bound on the
same scalar form. Restriction from the lifted reference cycle costs no
factor of the active dimension. This applies to the literal retained-law
matrix furnished by `retained_long_auxiliary_estimates_internal`. -/
theorem schur_auxiliary_vector_bound_internal
    {X : Type*} [MeasurableSpace X] {ν : Measure X}
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (s : Riesz1.RieszExponent) (n M : ℕ+) (hnM : (n : ℕ) ≤ (M : ℕ))
    (hM : 2 ≤ (M : ℕ)) (k : ℕ) (C κ γ η β : ℝ)
    (hC : 1 ≤ C) (hβ : 0 < β)
    (A : X → Matrix (Fin (M : ℕ)) (Fin (M : ℕ)) ℝ)
    (hA : PeriodizedMatrixBounds (ν := ν) s n M hM k C κ γ η A)
    (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν)
    (v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ)
    (hv : ∀ w, SchurRestriction.schurForm Q hQ n M hnM s hM k C κ γ η
      β hC hβ A hA v w = inner ℝ
        (WithLp.toLp 2 (fun i => if i = i₀ then χ else 0))
        (OperatorSchur.vectorValues Q hQ w))
    (B : ℝ) (hB : 0 ≤ B) (hχ : ∀ᵐ x ∂ν, |χ x| ≤ B) :
    let v' := MatrixEnergy.vectorEquiv Q hQ v
    let V := fun x => (WithLp.toLp 2 (fun i => (v' i).val x) : EuclideanSpace ℝ (Fin (n : ℕ)))
    (∀ᵐ x ∂ν, ‖V x‖ ≤ (β⁻¹*C*(n : ℝ)^(κ*η))*B) ∧
    eLpNorm V ∞ ν ≤ ENNReal.ofReal ((β⁻¹*C*(n : ℝ)^(κ*η))*B) := by
  intro v' V
  obtain ⟨u, hu, heq⟩ := (AuxiliaryMean.schur_lift_point_source_internal Q hQ s n M hnM
    hM k C κ γ η β hC hβ A hA i₀ χ).2 v hv
  let a := β*(C⁻¹*(n : ℝ)^(-κ*η))
  have ha : 0 < a := mul_pos hβ (SchurRestriction.periodized_mass_pos hC)
  have hlower := SchurRestriction.periodized_scaled_lower β hβ hA
  have hcoerc : ∀ᵐ x ∂ν, (∀ i j, (β • A x) i j = (β • A x) j i) ∧
      ∀ z : Fin (M : ℕ) → ℝ,
        a*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*(β • A x) i j*z j := by
    filter_upwards [hA.2.1, hlower] with x hx hy
    exact ⟨fun i j => by simp only [Matrix.smul_apply, hx.1 i j], hy⟩
  have hfull := (FixedLengthDecay.point_source_ae_bound_internal Q hQ (fun x => β • A x)
    (SchurRestriction.periodized_scaled_measurable β hA) a ha hcoerc ⊤
    (i₀.castLE hnM) χ B hB hχ u hu).1
  have hinv : a⁻¹ = β⁻¹*C*(n : ℝ)^(κ*η) := by
    dsimp only [a]
    rw [mul_inv, mul_inv, inv_inv, ← Real.rpow_neg (by positivity : (0 : ℝ) ≤ n)]
    rw [show -(-κ*η) = κ*η by ring]
    ring
  have hbound : ∀ᵐ x ∂ν, ‖V x‖ ≤ (β⁻¹*C*(n : ℝ)^(κ*η))*B := by
    filter_upwards [hfull] with x hx
    rw [hinv] at hx
    apply le_trans _ hx
    rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
    apply Real.sqrt_le_sqrt
    have he (i : Fin (n : ℕ)) : (u (i.castLE hnM)).val = (v' i).val :=
      congrArg Subtype.val (heq i)
    change (∑ i : Fin (n : ℕ), ‖(v' i).val x‖^2) ≤ ∑ i : Fin (M : ℕ), ‖(u i).val x‖^2
    simp_rw [← he]
    calc
      _ = ∑ j ∈ Finset.univ.image (Fin.castLE hnM), ‖(u j).val x‖^2 :=
        (Finset.sum_image (fun _ _ _ _ hij => Fin.castLE_injective hnM hij)).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  refine ⟨hbound, ?_⟩
  have hm : AEStronglyMeasurable V ν :=
    (VectorRadial.memLp_values (fun i => (v' i).val)).aestronglyMeasurable
  simpa only [ENNReal.toReal_top, inv_zero, ENNReal.rpow_zero, one_mul] using
    (eLpNorm_le_of_ae_bound (p := (∞ : ℝ≥0∞)) hm hbound)

end Riesz2.LengthAveragingFibres
