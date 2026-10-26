/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.PhysicalMeanPart2
public import Riesz2.DecayLong.PhysicalPerturbation
public import Riesz2.DecayLong.PhysicalBoundedOperator
public import Riesz2.DecayLong.LocalizedFieldPart3
import Riesz2.DecayShort.ShortRangeResultPart2

/-!
# Physical perturbation on the ambient scalar domain

Carrier and Schur-pairing bridges for the proof of Proposition 5.18.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Classical MatrixOrder ENNReal

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.PhysicalPerturbation

open PhysicalCore

/-- See the proof of Proposition 5.18 in the paper: entry and increment bounds on the
original ambient scalar form. Multiplication is integrated on the physical
chart. The exterior resolvent uses the original scalar generator. -/
theorem ambient_bilinear_internal (hRig : External.LongRangeRigidityLocallyUniform)
    (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (κ₀ : ℝ) (hκ₀ : 1 ≤ κ₀) (M₀ : ℕ) (hM₀ : 0 < M₀) :
    ∃ κ > 0, ∀ (ε Cθ βlo βhi : ℝ),
      0 < ε → 1 ≤ Cθ → 0 < βlo → βlo ≤ βhi →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n : ℕ+) (m : ℕ), 2 ≤ (n : ℕ) → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : (n : ℕ) ≤ (M : ℕ)),
      2 * (n : ℕ) ≤ (M : ℕ) → (M : ℝ) ≤ 3 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
      let K := ⌊(n : ℝ) ^ ε⌋₊ ^ M₀
      ∀ (hK : 1 ≤ K) (hKM : K ≤ (M : ℕ) / 4),
      let ν := activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n hn θ ε false
      let μ := ν.comap
        ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
      let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
        β.val * ∑ i, θ.val ((n : ℝ) ^ (-ε) * x i) -
          Real.log (∫ z : EuclideanSpace ℝ (Fin m),
            (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (x,z)).toReal)
      let A := fun (i j : Fin (n : ℕ)) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) =>
        hessianMatrix V x.val i j - β.val * PhysicalCore.properActive β s n m M hM hnM K θ ε κ₀ x i j
      ∀ (_hco : MeasurePreserving
        ((↑) : AffineSimplex.chartDomain n ((n+m : ℕ)+1) → EuclideanSpace ℝ (Fin (n : ℕ))) μ ν),
      ∀ (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q),
      let E := Finset.univ.filter (fun a : Fin (M : ℕ) => (n : ℕ) ≤ a.val)
      let D : Matrix E E ℝ := ((2 : ℝ) • referenceIntervalMatrix s M hM K).submatrix
        (Subtype.val : E → Fin (M : ℕ)) Subtype.val
      let hD := (ExteriorForces.exteriorBlock_posDef s M hM hK hKM E).1
      let col := fun (i : Fin (n : ℕ)) (a : E) => 2 * referenceIntervalMatrix s M hM K (i.castLE hnM) a.val
      let F := BoundarySchurBounds.constantForm Q hQ (β.val • D) (hD.posSemidef.smul β.property.le)
      let J := OperatorSchur.vectorValues (ι := E) Q hQ
      ∃ R : PiLp 2 (fun _ : E => Lp ℝ 2 ν) →L[ℝ] MatrixEnergy.Vector (ι := E) Q hQ,
        (∀ f w, F (R f) w = inner ℝ f (J w)) ∧
        (∀ f u, (∀ w, F u w = inner ℝ f (J w)) → u = R f) ∧
        ∀ (φ η : Lp ℝ 2 ν) (Mφ Mη : ℝ), 0 ≤ Mφ → 0 ≤ Mη →
          (∀ᵐ x ∂ν, |φ x| ≤ Mφ) → (∀ᵐ x ∂ν, |η x| ≤ Mη) →
        ∀ i j l : Fin (n : ℕ),
          let d := fun a : Fin (n : ℕ) => ((min (a.val + 1) ((n : ℕ) - a.val) : ℕ) : ℝ)
          let T := fun a b => (∫ x, φ x.val * η x.val * A a b x ∂μ) + β.val ^ 2 *
            inner ℝ (BoundarySchurBounds.tensor (col b) η) (J (R (BoundarySchurBounds.tensor (col a) φ)))
          let Err := C * Real.exp (-c * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη)
          Integrable (fun x => φ x.val * η x.val * A i j x) μ ∧
          Integrable (fun x => φ x.val * η x.val * (A i j x - A i l x)) μ ∧
          |T i j| ≤ C * (n : ℝ) ^ (κ * ε) * (d i) ^ (-s.val / 2) * (d j) ^ (-s.val / 2) * (‖φ‖ * ‖η‖) + Err ∧
          |T i j - T i l| ≤ C * (n : ℝ) ^ (κ * ε) * (Nat.dist j.val l.val : ℝ) *
            (d i) ^ (-s.val / 2) * (min (d j) (d l)) ^ (-1 - s.val / 2) * (‖φ‖ * ‖η‖) + Err := by
  obtain ⟨km, hkm, hm⟩ := PerturbationBounds.proper_multiplication_bilinear hRig s κ₀ hκ₀
  let κ := km + 2 * M₀
  have hκ : 0 < κ := by dsimp [κ]; positivity
  refine ⟨κ, hκ, fun ε Cθ βlo βhi hε hCθ hlo hle => ?_⟩
  obtain ⟨Cm, c, hCm, hc, hmult⟩ := hm ε Cθ βlo βhi hε hCθ hlo hle
  obtain ⟨Cs, hCs, hschur⟩ := BoundarySchurBounds.bilinear_schur_cutoff_uniform hz s βlo hlo
  let C := Cm + βhi ^ 2 * Cs
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, c, hC, hc, ?_⟩
  intro β hβ n m hn2 hper hn θ hcurv M hM hnM hhalf hscale K hK hKM ν μ V A hco Q hQ E D hD col F J
  obtain ⟨R, hR, huniq, hest⟩ := hschur β.val hβ.1 M hM K hK hKM n (by omega) ν Q hQ
  refine ⟨R, hR, huniq, ?_⟩
  intro φ η Mφ Mη hMφ hMη hφM hηM i j l d T Err
  have hφ := (Lp.stronglyMeasurable φ).measurable
  have hη := (Lp.stronglyMeasurable η).measurable
  obtain ⟨hi, hp, hi', hp'⟩ := hmult β hβ n m hn2 hper hn θ hcurv M hM hnM K hhalf hscale
    (fun x => φ x.val) (fun x => η x.val) Mφ Mη
    (hφ.comp measurable_subtype_coe) (hη.comp measurable_subtype_coe) hMφ hMη
    (hco.quasiMeasurePreserving.ae hφM) (hco.quasiMeasurePreserving.ae hηM) i j l
  change Integrable (fun x => φ x.val * η x.val * A i j x) μ at hi
  change Integrable (fun x => φ x.val * η x.val * (A i j x - A i l x)) μ at hi'
  have hf := MeasurableEmbedding.subtype_coe
    (AffineSimplex.isOpen_chartDomain (n : ℕ) ((n+m : ℕ)+1)).measurableSet
  have hnorm (f : Lp ℝ 2 ν) : Real.sqrt (∫ x, f x.val ^ 2 ∂μ) = ‖f‖ := by
    rw [hco.integral_comp hf (fun x => f x ^ 2)]
    simpa only [Lp.toLp_coeFn] using
      (PerturbationPairingAssembly.toLp_norm (Lp.memLp f)).symm
  dsimp only [μ, ν] at hnorm
  simp only [hnorm] at hp hp'
  obtain ⟨hr, hr'⟩ := hest η φ (i.castLE hnM) (j.castLE hnM) (l.castLE hnM) i.isLt j.isLt l.isLt
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hpow : (n : ℝ) ^ (km * ε) ≤ (n : ℝ) ^ (κ * ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [κ]; nlinarith only [hε, (Nat.cast_nonneg M₀ : (0 : ℝ) ≤ M₀)])
  have hcut : (K : ℝ) ^ 2 ≤ (n : ℝ) ^ (κ * ε) :=
    (BoundarySchurBounds.cutoff_sq_le n M₀ n.pos ε).trans
      (Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [κ]; nlinarith only [hkm, hε]))
  have hβsq : β.val ^ 2 ≤ βhi ^ 2 := pow_le_pow_left₀ β.property.le hβ.2 2
  have hmain (w : ℝ) (hw : 0 ≤ w) (u v : ℝ)
      (hu : |u| ≤ Cm * (n : ℝ) ^ (km * ε) * w * (‖φ‖ * ‖η‖) +
        Cm * Real.exp (-c * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη))
      (hv : |v| ≤ Cs * (K : ℝ) ^ 2 * w * (‖φ‖ * ‖η‖)) :
      |u + β.val ^ 2 * v| ≤ C * (n : ℝ) ^ (κ * ε) * w * (‖φ‖ * ‖η‖) + Err := by
    have hE : Cm * Real.exp (-c * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη) ≤ Err := by
      dsimp only [Err]
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hMφ hMη)
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact le_add_of_nonneg_right (by positivity)
    have hh := (abs_add_le u (β.val ^ 2 * v)).trans
      (add_le_add hu (by simpa only [abs_mul, abs_of_nonneg (sq_nonneg β.val)] using
        mul_le_mul_of_nonneg_left hv (sq_nonneg β.val)))
    apply hh.trans
    calc
      _ ≤ (Cm * (n : ℝ) ^ (κ * ε) * w * (‖φ‖ * ‖η‖) + Err) +
          βhi ^ 2 * (Cs * (n : ℝ) ^ (κ * ε) * w * (‖φ‖ * ‖η‖)) := by gcongr
      _ = _ := by dsimp [C]; ring
  have he : (∫ x, φ x.val * η x.val * A i j x ∂μ) - (∫ x, φ x.val * η x.val * A i l x ∂μ) =
      ∫ x, φ x.val * η x.val * (A i j x - A i l x) ∂μ := by
    rw [← integral_sub hi (hi.sub hi' |>.congr (ae_of_all μ fun x => by simp only [Pi.sub_apply]; ring))]
    apply integral_congr_ae
    exact ae_of_all μ fun x => by ring
  have hT : T i j - T i l = (∫ x, φ x.val * η x.val * (A i j x - A i l x) ∂μ) + β.val ^ 2 *
      inner ℝ (BoundarySchurBounds.tensor (col j - col l) η)
        (J (R (BoundarySchurBounds.tensor (col i) φ))) := by
    dsimp only [T]
    have ht : BoundarySchurBounds.tensor (col j - col l) η =
        BoundarySchurBounds.tensor (col j) η - BoundarySchurBounds.tensor (col l) η := by
      apply (WithLp.equiv 2 _).injective
      funext a
      change (col j a - col l a) • η = col j a • η - col l a • η
      exact sub_smul _ _ _
    rw [ht, inner_sub_left, ← he]
    ring
  refine ⟨hi, hi', ?_, ?_⟩
  · have hh := hmain ((d i) ^ (-s.val / 2) * (d j) ^ (-s.val / 2)) (by dsimp [d]; positivity)
      _ _ (by simpa only [mul_assoc] using hp)
      (by convert hr using 1; simp only [d, Fin.val_castLE]; ring)
    simpa only [T, mul_assoc] using hh
  · rw [hT]
    have hh := hmain ((Nat.dist j.val l.val : ℝ) * (d i) ^ (-s.val / 2) *
      (min (d j) (d l)) ^ (-1 - s.val / 2)) (by dsimp [d]; positivity)
      _ _ (by simpa only [mul_assoc] using hp')
      (by convert hr' using 1; simp only [d, Fin.val_castLE, Nat.cast_min]; ring)
    simpa only [mul_assoc] using hh


/-- The whole bounded-input operator in Proposition 5.18, before either
application of Lemma 5.17. The supported multiplication
coefficients, their integrability, both universal tests, and the native
point pairing share the same exterior resolvent and uniform constants. -/
theorem ambient_operator_internal
    (hRig : External.LongRangeRigidityLocallyUniform) (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κ₀ : ℝ) (hκ₀ : 1 ≤ κ₀) (M₀ : ℕ) (hM₀ : 0 < M₀) :
    ∃ κloss > 0, ∀ (ε Cθ βlo βhi : ℝ),
      0 < ε → 1 ≤ Cθ → 0 < βlo → βlo ≤ βhi →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n : ℕ+) (m : ℕ), 2 ≤ (n : ℕ) → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : (n : ℕ) ≤ (M : ℕ)),
      2 * (n : ℕ) ≤ (M : ℕ) → (M : ℝ) ≤ 3 * (n : ℝ) ^ (1/2 + 1/s.val) →
      let K := ⌊(n : ℝ) ^ ε⌋₊ ^ M₀
      ∀ (hK : 1 ≤ K) (hKM : K ≤ (M : ℕ) / 4),
      let ν := activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n hn θ ε false
      letI : IsProbabilityMeasure ν := IntrinsicScalarCore.probability
        (PhysicalFormDomain.proper_gibbs_potential β s n m θ ε)
      let μ := ν.comap
        ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
      let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
        β.val * ∑ i, θ.val ((n : ℝ) ^ (-ε) * x i) -
          Real.log (∫ z : EuclideanSpace ℝ (Fin m),
            (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (x,z)).toReal)
      let A := fun (i j : Fin (n : ℕ)) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) =>
        hessianMatrix V x.val i j - β.val * PhysicalCore.properActive β s n m M hM hnM K θ ε κ₀ x i j
      ∀ (_hco : MeasurePreserving
        ((↑) : AffineSimplex.chartDomain n ((n+m : ℕ)+1) → EuclideanSpace ℝ (Fin (n : ℕ))) μ ν),
      ∀ (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q),
      let Iext := Finset.univ.filter (fun a : Fin (M : ℕ) => (n : ℕ) ≤ a.val)
      let Dext : Matrix Iext Iext ℝ := ((2 : ℝ) • referenceIntervalMatrix s M hM K).submatrix
        (Subtype.val : Iext → Fin (M : ℕ)) Subtype.val
      let hDext := (ExteriorForces.exteriorBlock_posDef s M hM hK hKM Iext).1
      let col := fun (i : Fin (n : ℕ)) (a : Iext) =>
        2 * referenceIntervalMatrix s M hM K (i.castLE hnM) a.val
      let Fext := BoundarySchurBounds.constantForm Q hQ (β.val • Dext)
        (hDext.posSemidef.smul β.property.le)
      let J := OperatorSchur.vectorValues (ι := Iext) Q hQ
      ∃ R : PiLp 2 (fun _ : Iext => Lp ℝ 2 ν) →L[ℝ] MatrixEnergy.Vector (ι := Iext) Q hQ,
        (∀ f w, Fext (R f) w = inner ℝ f (J w)) ∧
        (∀ f u, (∀ w, Fext u w = inner ℝ f (J w)) → u = R f) ∧
        ∃ Y : EuclideanSpace ℝ (Fin (n : ℕ)) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ,
          (∀ x : AffineSimplex.chartDomain n ((n+m : ℕ)+1), ∀ i k, Y x.val i k = A i k x) ∧
        ∃ hY : ∀ i k, Integrable (fun x => Y x i k) ν,
        ColumnSubtraction.OperatorBounds s n (C*(n : ℝ)^(κloss*ε)) c
          (GoodBlocks.coefficientTailPower s.val ε)
          (BoundedPerturbationOperator.operator Y hY
            (properSchurOperator (Q := Q) (hQ := hQ) (s := s) (n := n) (M := M)
              (hnM := hnM) (hM := hM) (K := K) (β := β.val) R)) ∧
        ∀ (φ ψ : BoundedL2Pairings.boundedSubmodule ν) (i k : Fin (n : ℕ)),
          BoundedPerturbationOperator.point Y
            (properSchurOperator (Q := Q) (hQ := hQ) (s := s) (n := n) (M := M)
              (hnM := hnM) (hM := hM) (K := K) (β := β.val) R) φ ψ i k =
          (∫ x, φ.val x.val*ψ.val x.val*A i k x ∂μ) + β.val^2 *
            inner ℝ (BoundarySchurBounds.tensor (col k) ψ.val)
              (J (R (BoundarySchurBounds.tensor (col i) φ.val))) := by
  obtain ⟨κloss, hκloss, hb⟩ := ambient_bilinear_internal
    hRig hz s κ₀ hκ₀ M₀ hM₀
  refine ⟨κloss, hκloss, fun ε Cθ βlo βhi hε hCθ hlo hle => ?_⟩
  obtain ⟨C₀,c,hC₀,hc,hbound⟩ := hb ε Cθ βlo βhi hε hCθ hlo hle
  refine ⟨C₀,c,hC₀,hc,?_⟩
  intro β hβ n m hn2 hper hn θ hcurv M hM hnM hhalf hscale K hK hKM ν μ V A hco Q hQ
    Iext Dext hDext col Fext J
  obtain ⟨R,hR,huniq,ht⟩ := hbound β hβ n m hn2 hper hn θ hcurv M hM hnM
    hhalf hscale hK hKM hco Q hQ
  have hprob : IsProbabilityMeasure ν :=
    IntrinsicScalarCore.probability (PhysicalFormDomain.proper_gibbs_potential β s n m θ ε)
  have hf := MeasurableEmbedding.subtype_coe
    (AffineSimplex.isOpen_chartDomain (n : ℕ) ((n+m : ℕ)+1)).measurableSet
  let Ac := fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) => fun i k => A i k x
  have hAc : Measurable Ac := Measurable.of_eval fun i => Measurable.of_eval fun k =>
    ((DifferentiatedPoisson.measurable_hessian_entries i k).comp measurable_subtype_coe).sub
      ((PhysicalCore.measurable_properActive β s n m M hM hnM K θ ε κ₀ i k).const_mul β.val)
  obtain ⟨Y,hYm,hYe⟩ := hf.exists_measurable_extend hAc (fun _ => inferInstance)
  have hYe' (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1)) (i k : Fin (n : ℕ)) :
      Y x.val i k = A i k x := congrFun (congrFun (congrFun hYe x) i) k
  let one : Lp ℝ 2 ν := (memLp_const (1 : ℝ)).toLp (fun _ => 1)
  have hone : one =ᵐ[ν] fun _ => 1 := MemLp.coeFn_toLp _
  have honeB : ∀ᵐ x ∂ν, |one x| ≤ 1 := hone.mono fun x hx => by simp only [hx,abs_one,le_refl]
  have hY (i k : Fin (n : ℕ)) : Integrable (fun x => Y x i k) ν := by
    apply (hco.integrable_comp_emb hf).mp
    have hh := (ht one one 1 1 (by norm_num) (by norm_num) honeB honeB i k k).1
    apply hh.congr
    filter_upwards [hco.quasiMeasurePreserving.ae hone] with x hx
    simp only [Function.comp_apply,hx,hYe',one_mul]
    rfl
  let S := properSchurOperator (Q := Q) (hQ := hQ) (s := s) (n := n) (M := M)
    (hnM := hnM) (hM := hM) (K := K) (β := β.val) R
  have he (φ ψ : BoundedL2Pairings.boundedSubmodule ν) (i k : Fin (n : ℕ)) :
      BoundedPerturbationOperator.point Y S φ ψ i k =
        (∫ x, φ.val x.val*ψ.val x.val*A i k x ∂μ) + β.val^2 *
          inner ℝ (BoundarySchurBounds.tensor (col k) ψ.val)
            (J (R (BoundarySchurBounds.tensor (col i) φ.val))) := by
    unfold BoundedPerturbationOperator.point
    rw [show S = properSchurOperator (Q := Q) (hQ := hQ) (s := s) (n := n) (M := M)
      (hnM := hnM) (hM := hM) (K := K) (β := β.val) R from rfl,properSchurOperator_point]
    congr 1
    rw [← hco.integral_comp hf (fun x => φ.val x*Y x i k*ψ.val x)]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by dsimp only; rw [hYe']; ring
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by positivity
  let P := C₀*(n : ℝ)^(κloss*ε)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hC₀P : C₀ ≤ P := by
    have hp := Real.one_le_rpow hn1 (mul_pos hκloss hε).le
    simpa only [mul_one,P] using mul_le_mul_of_nonneg_left hp hC₀.le
  have hOp : ColumnSubtraction.OperatorBounds s n P c
      (GoodBlocks.coefficientTailPower s.val ε) (BoundedPerturbationOperator.operator Y hY S) := by
    apply BoundedPerturbationOperator.operator_bounds_internal s n P c _ Y hY S
    · intro φ ψ i k
      rw [he]
      have hh := (ht φ.val ψ.val _ _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg
        (BoundedPerturbationOperator.bounded_ae_essentialNorm φ)
        (BoundedPerturbationOperator.bounded_ae_essentialNorm ψ) i k k).2.2.1
      have herr := mul_le_mul_of_nonneg_right hC₀P
        (show 0 ≤ Real.exp (-c*(n : ℝ)^GoodBlocks.coefficientTailPower s.val ε)*
          (eLpNorm (φ.val : _ → ℝ) ∞ ν).toReal*(eLpNorm (ψ.val : _ → ℝ) ∞ ν).toReal by positivity)
      dsimp only [P]
      nlinarith only [hh,herr]
    · intro φ ψ i k l
      rw [he,he]
      have hh := (ht φ.val ψ.val _ _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg
        (BoundedPerturbationOperator.bounded_ae_essentialNorm φ)
        (BoundedPerturbationOperator.bounded_ae_essentialNorm ψ) i k l).2.2.2
      have herr := mul_le_mul_of_nonneg_right hC₀P
        (show 0 ≤ Real.exp (-c*(n : ℝ)^GoodBlocks.coefficientTailPower s.val ε)*
          (eLpNorm (φ.val : _ → ℝ) ∞ ν).toReal*(eLpNorm (ψ.val : _ → ℝ) ∞ ν).toReal by positivity)
      dsimp only [P]
      nlinarith only [hh,herr]
  exact ⟨R,hR,huniq,Y,hYe',hY,hOp,he⟩

/-- See the proof of Proposition 5.18 in the paper: a single component test has its
literal scalar value, with no additional form-domain condition. -/
theorem single_values_internal {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    [DecidableEq ι] {ν : Measure X} (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (j i : ι) (φ : Q.1) :
    MatrixEnergy.vectorEquiv Q hQ
      (PiLp.single 2 j ((ScalarFormHilbert.equiv Q hQ).symm φ)) i =
      if i=j then φ else 0 := by
  change ScalarFormHilbert.equiv Q hQ
    ((PiLp.single 2 j ((ScalarFormHilbert.equiv Q hQ).symm φ) :
      MatrixEnergy.Vector (ι := ι) Q hQ) i) = _
  by_cases hi : i=j
  · simp [hi]
  · simp [hi]

/-- See the proof of Proposition 5.18 in the paper: the physical exterior correction
is precisely the finite sum of dual resolvent pairings on the same scalar
domain. The hypotheses are its defining equations, under an internal name. -/
theorem schur_correction_row_internal {X : Type*} [MeasurableSpace X]
    {ν : Measure X} (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (s : Riesz1.RieszExponent) (n M : ℕ+) (hnM : (n : ℕ) ≤ (M : ℕ))
    (hM : 2 ≤ (M : ℕ)) (K : ℕ) (β : ℝ) (hβ : 0 < β)
    (hD : (β • (((2 : ℝ) • referenceIntervalMatrix s M hM K).submatrix
      (Subtype.val : ↥(Finset.univ.filter (fun a : Fin (M : ℕ) => (n : ℕ) ≤ a.val)) → Fin (M : ℕ))
      Subtype.val)).PosSemidef)
    (R : PiLp 2 (fun _ : ↥(Finset.univ.filter
      (fun a : Fin (M : ℕ) => (n : ℕ) ≤ a.val)) => Lp ℝ 2 ν) →L[ℝ]
      MatrixEnergy.Vector (ι := ↥(Finset.univ.filter
        (fun a : Fin (M : ℕ) => (n : ℕ) ≤ a.val))) Q hQ)
    (hR : ∀ f w, BoundarySchurBounds.constantForm Q hQ _ hD (R f) w =
      inner ℝ f (OperatorSchur.vectorValues Q hQ w))
    (huniq : ∀ f z, (∀ w, BoundarySchurBounds.constantForm Q hQ _ hD z w =
      inner ℝ f (OperatorSchur.vectorValues Q hQ w)) → z = R f)
    (Re : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := Fin ((M : ℕ)-(n : ℕ))) Q hQ)
    (G : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ] ℝ)
    (hRe : ∀ u w,
      β⁻¹ * OperatorSchur.vectorEnergy Q hQ (Re u) w +
        (∫ x, matrixFieldPair (fun _ : X => (2 : ℝ) • referenceIntervalMatrix s M hM K)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n M hnM (0,Re u)) i).val)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n M hnM (0,w)) i).val) x ∂ν) =
        ∫ x, matrixFieldPair (fun _ : X => (2 : ℝ) • referenceIntervalMatrix s M hM K)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n M hnM (u,0)) i).val)
          (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n M hnM (0,w)) i).val) x ∂ν)
    (hG : ∀ u v, G u v = β * ∫ x, matrixFieldPair
      (fun _ : X => (2 : ℝ) • referenceIntervalMatrix s M hM K)
      (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n M hnM (v,0)) i).val)
      (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n M hnM (0,Re u)) i).val) x ∂ν)
    (v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ) (j : Fin (n : ℕ)) (φ : Q.1) :
    let col := fun (i : Fin (n : ℕ))
      (a : ↥(Finset.univ.filter (fun a : Fin (M : ℕ) => (n : ℕ) ≤ a.val))) =>
        2 * referenceIntervalMatrix s M hM K (i.castLE hnM) a.val
    G v (PiLp.single 2 j ((ScalarFormHilbert.equiv Q hQ).symm φ)) =
      β^2 * ∑ k, inner ℝ (BoundarySchurBounds.tensor (col k) (MatrixEnergy.vectorEquiv Q hQ v k).val)
        (OperatorSchur.vectorValues Q hQ (R (BoundarySchurBounds.tensor (col j) φ.val))) := by
  intro col
  have he := LocalizedFieldPart3.reindexed_resolvent_internal Q hQ s n M hnM hM K β hβ hD R huniq
    v (Re v) (by simpa only [OperatorSchur.vectorEnergy_apply] using hRe v)
  have hsingle : (∑ i : Fin (n : ℕ), BoundarySchurBounds.tensor (col i)
      (MatrixEnergy.vectorEquiv Q hQ
        (PiLp.single 2 j ((ScalarFormHilbert.equiv Q hQ).symm φ)) i).val) =
      BoundarySchurBounds.tensor (col j) φ.val := by
    simp only [single_values_internal]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp only [ite_eq_right hb, ZeroMemClass.coe_zero]
      apply PiLp.ext
      intro a
      simp [BoundarySchurBounds.tensor]
    · simp
  rw [hG, LocalizedFieldPart3.cross_pair_internal, hsingle, he, map_smul, map_sum,
    real_inner_smul_right, inner_sum]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [PerturbationBounds.schur_pair_symm_internal Q hQ _ hD R hR]
  ring

/-- See the proof of Proposition 5.18 in the paper: continuous physical-form
solutions satisfy the weak equation on the whole domain. -/
theorem weak_of_form_internal {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    {ν : Measure X} (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (M : X → Matrix ι ι ℝ)
    (A : MatrixEnergy.Vector (ι := ι) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := ι) Q hQ →L[ℝ] ℝ)
    (hA : ∀ u v, Integrable (matrixFieldPair M
      (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val)
      (fun i => (MatrixEnergy.vectorEquiv Q hQ v i).val)) ν ∧
      A u v = OperatorSchur.vectorEnergy Q hQ u v + ∫ x, matrixFieldPair M
        (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ v i).val) x ∂ν)
    (f : ι → Lp ℝ 2 ν) (u : MatrixEnergy.Vector (ι := ι) Q hQ)
    (hu : ∀ z, A u z = inner ℝ (WithLp.toLp 2 f) (OperatorSchur.vectorValues Q hQ z)) :
    WeightedWeakSolution Q M ⊤ f (MatrixEnergy.vectorEquiv Q hQ u) := by
  refine ⟨⟨ae_of_all ν (fun _ => Submodule.mem_top), (hA u u).1⟩, ?_⟩
  intro v _
  let z := (MatrixEnergy.vectorEquiv Q hQ).symm v
  have hz : MatrixEnergy.vectorEquiv Q hQ z = v := LinearEquiv.apply_symm_apply _ _
  refine ⟨by simpa only [hz] using (hA u z).1, ?_⟩
  have he := hu z
  rw [(hA u z).2, OperatorSchur.vectorEnergy_apply] at he
  simpa only [hz, PiLp.inner_apply, PiLp.toLp_apply, OperatorSchur.vectorValues_apply] using he

/-- See the proof of Proposition 5.18 in the paper: literal multiplication row of a
single test. Symmetry is used only to orient the source column. -/
theorem multiplication_row_internal {X Y ι : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [Fintype ι] [DecidableEq ι]
    {μ : Measure X} {ν : Measure Y} (f : X → Y) (hco : MeasurePreserving f μ ν)
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (A : X → Matrix ι ι ℝ) (hA : ∀ x i j, A x i j = A x j i)
    (v : MatrixEnergy.Vector (ι := ι) Q hQ) (j : ι) (φ : Q.1)
    (hi : ∀ k, Integrable (fun x => φ.val (f x) *
      (MatrixEnergy.vectorEquiv Q hQ v k).val (f x) * A x j k) μ) :
    (∫ x, ∑ i, ∑ k, (MatrixEnergy.vectorEquiv Q hQ v i).val (f x) * A x i k *
      (MatrixEnergy.vectorEquiv Q hQ
        (PiLp.single 2 j ((ScalarFormHilbert.equiv Q hQ).symm φ)) k).val (f x) ∂μ) =
      ∑ k, ∫ x, φ.val (f x) * (MatrixEnergy.vectorEquiv Q hQ v k).val (f x) * A x j k ∂μ := by
  rw [← integral_finsetSum Finset.univ (fun k _ => hi k)]
  apply integral_congr_ae
  filter_upwards [hco.quasiMeasurePreserving.ae (Lp.coeFn_zero ℝ 2 ν)] with x hx
  change (0 : Lp ℝ 2 ν) (f x) = 0 at hx
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single j]
  · rw [single_values_internal, ite_eq_left rfl, hA x i j]
    ring
  · intro b _ hb
    rw [single_values_internal, ite_eq_right hb]
    change _ * (0 : Lp ℝ 2 ν) (f x) = 0
    rw [hx, mul_zero]
  · simp

/-- See the proof of Proposition 5.18 in the paper: the physical comparison uses
any realization of its literal Neumann graph, including the realization
already returned by the physical mean theorem. -/
theorem comparison_on_realization_internal (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (hn : 2 * (n : ℕ) ≤ (n : ℕ) + m + 1)
    (θ : PhysicalCutoff) (ε κ₀ : ℝ) (hε : 0 ≤ ε)
    (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : 2 * (n : ℕ) ≤ (M : ℕ))
    (K : ℕ) (hK : 1 ≤ K) (hKM : K ≤ (M : ℕ) / 4) :
    let p := ofLong β s
    let hnp : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ) := by simp; omega
    let ν := activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hnp θ ε false
    let Ω := AffineSimplex.chartDomain n ((n + m : ℕ) + 1)
    let μ := ν.comap ((↑) : Ω → EuclideanSpace ℝ (Fin (n : ℕ)))
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      β.val * ∑ i, θ.val ((n : ℝ) ^ (-ε) * x i) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal)
    let a := min 1 (s.val * (s.val + 1)) * (n : ℝ) ^ (-(s.val + 2) * ε)
    ∀ (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q),
      IsNeumannRealization Ω Q →
        (∀ (W : Submodule ℝ (Fin (n : ℕ) → ℝ)) (u : Fin (n : ℕ) → Q.1),
          WeightedFormDomain Q (hessianMatrix V) W u ↔
            ∀ᵐ x ∂ν, (fun i => (u i).val x) ∈ W) ∧
        ∃ (F : MatrixEnergy.Vector (ι := Fin (M : ℕ)) Q hQ →L[ℝ]
            MatrixEnergy.Vector (ι := Fin (M : ℕ)) Q hQ →L[ℝ] ℝ)
          (S G Aphys T : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ]
            MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ] ℝ)
          (R : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ]
            MatrixEnergy.Vector (ι := Fin ((M : ℕ) - (n : ℕ))) Q hQ),
          (∀ u v,
            let P := fun x : Ω => ∑ i, ∑ j,
              (MatrixEnergy.vectorEquiv Q hQ u i).val x.val *
                PhysicalCore.properMatrix β s n m M hM (by omega) K θ ε κ₀ x i j *
                (MatrixEnergy.vectorEquiv Q hQ v j).val x.val
            Integrable P μ ∧ F u v = OperatorSchur.vectorEnergy Q hQ u v + β.val * ∫ x, P x ∂μ) ∧
          (∀ u v, G u v = G v u) ∧ (∀ u, 0 ≤ G u u) ∧
          (∀ u v, S u v = F (SchurRestriction.assemble Q hQ n M (by omega) (u,0))
            (SchurRestriction.assemble Q hQ n M (by omega) (v,0)) - G u v) ∧
          (∀ u w,
            let P := fun z z' => fun x : Ω => matrixFieldPair
              (fun _ : EuclideanSpace ℝ (Fin (n : ℕ)) => (2 : ℝ) • referenceIntervalMatrix s M hM K)
              (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n M (by omega) z) i).val)
              (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n M (by omega) z') i).val) x.val
            Integrable (P (0,R u) (0,w)) μ ∧ Integrable (P (u,0) (0,w)) μ ∧
              β.val⁻¹ * OperatorSchur.vectorEnergy Q hQ (R u) w +
                (∫ x, P (0,R u) (0,w) x ∂μ) = ∫ x, P (u,0) (0,w) x ∂μ) ∧
          (∀ u v,
            let P := fun x : Ω => matrixFieldPair
              (fun _ : EuclideanSpace ℝ (Fin (n : ℕ)) => (2 : ℝ) • referenceIntervalMatrix s M hM K)
              (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n M (by omega) (v,0)) i).val)
              (fun i => (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n M (by omega) (0,R u)) i).val) x.val
            Integrable P μ ∧ G u v = β.val * ∫ x, P x ∂μ) ∧
          (∃ c : ℝ, 0 < c ∧ ∀ u, c * ‖u‖ ^ 2 ≤ S u u) ∧
          Aphys = S + T ∧
          (∀ u v,
            let U := fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val
            let W := fun i => (MatrixEnergy.vectorEquiv Q hQ v i).val
            let A₀ := PhysicalCore.properActive β s n m M hM (by omega) K θ ε κ₀
            let P := fun x : Ω => ∑ i, ∑ j, U i x.val * A₀ x i j * W j x.val
            let D := fun x : Ω => ∑ i, ∑ j,
              U i x.val * (hessianMatrix V x.val i j - β.val * A₀ x i j) * W j x.val
            Integrable (matrixFieldPair (hessianMatrix V) U W) ν ∧
              Aphys u v = OperatorSchur.vectorEnergy Q hQ u v +
                ∫ x, matrixFieldPair (hessianMatrix V) U W x ∂ν ∧
              T u v = Aphys u v - F (SchurRestriction.assemble Q hQ n M (by omega) (u,0))
                (SchurRestriction.assemble Q hQ n M (by omega) (v,0)) + G u v ∧
              Integrable P μ ∧ S u v = OperatorSchur.vectorEnergy Q hQ u v +
                β.val * (∫ x, P x ∂μ) - G u v ∧
              Integrable D μ ∧ T u v = (∫ x, D x ∂μ) + G u v) ∧
          (∀ f : PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν),
            (∃! v, ∀ z, S v z = inner ℝ f (OperatorSchur.vectorValues Q hQ z)) ∧
            (∃! ψ, ∀ z, Aphys ψ z = inner ℝ f (OperatorSchur.vectorValues Q hQ z))) ∧
          0 < a ∧ ∀ (f : PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν)) (v ψ),
            (∀ z, S v z = inner ℝ f (OperatorSchur.vectorValues Q hQ z)) →
            (∀ z, Aphys ψ z = inner ℝ f (OperatorSchur.vectorValues Q hQ z)) →
            (∀ z, Aphys (v - ψ) z = T v z) ∧
              β.val * a * ‖OperatorSchur.vectorValues Q hQ (v - ψ)‖ ^ 2 +
                OperatorSchur.vectorEnergy Q hQ (v - ψ) (v - ψ) ≤ T v (v - ψ) := by
  intro p hnp ν Ω μ V a Q hQ hreal
  obtain ⟨Qc,hrealc,hQc,rest⟩ := PhysicalIdentity.proper_comparison
    β s n m hn θ ε κ₀ hε M hM hnM K hK hKM
  have hQQ := GibbsPotentialComparison.neumannRealization_unique Qc Q hrealc hreal
  subst Qc
  exact rest

/-- See the proof of Proposition 5.18 in the paper: the physical and Schur forms on
the mean theorem's realization, retaining only the interfaces used below. -/
theorem comparison_interfaces_internal
    (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (hnN : 2*(n : ℕ) ≤ (n : ℕ)+m+1)
    (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hhalf : 2*(n : ℕ) ≤ (M : ℕ))
    (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ) (hK : 1 ≤ K) (hKM : K ≤ (M : ℕ)/4)
    (θ : PhysicalCutoff) (ε κ₀ : ℝ) (hε : 0 ≤ ε)
    (Cstar ks gs : ℝ) (hCstar : 1 ≤ Cstar) :
    let ν := activeTiltedGapLaw (ofLong β s) ((n : ℕ)+m).succPNat n (by simp; omega) θ ε false
    let Ω := AffineSimplex.chartDomain n ((n+m : ℕ)+1)
    let μ := ν.comap ((↑) : Ω → EuclideanSpace ℝ (Fin (n : ℕ)))
    ∀ (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q), IsNeumannRealization Ω Q →
    ∀ (_hco : MeasurePreserving ((↑) : Ω → EuclideanSpace ℝ (Fin (n : ℕ))) μ ν)
      (A : EuclideanSpace ℝ (Fin (n : ℕ)) → Matrix (Fin (M : ℕ)) (Fin (M : ℕ)) ℝ),
    (∀ x : Ω, A x.val = properMatrix β s n m M hM hnM K θ ε κ₀ x) →
    ∀ hA : PeriodizedMatrixBounds (ν := ν) s n M hM K Cstar ks gs ε A,
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      β.val*∑ i,θ.val ((n : ℝ)^(-ε)*x i) - Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (x,z)).toReal)
    let J := SchurRestriction.assemble Q hQ n M hnM
    let P := fun z z' => matrixFieldPair
      (fun _ : EuclideanSpace ℝ (Fin (n : ℕ)) => (2 : ℝ) • referenceIntervalMatrix s M hM K)
      (fun i => (MatrixEnergy.vectorEquiv Q hQ (J z) i).val)
      (fun i => (MatrixEnergy.vectorEquiv Q hQ (J z') i).val)
    ∃ (S Aphys T G : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ] ℝ)
      (Re : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ]
        MatrixEnergy.Vector (ι := Fin ((M : ℕ)-(n : ℕ))) Q hQ),
    (∀ (W : Submodule ℝ (Fin (n : ℕ) → ℝ)) (u : Fin (n : ℕ) → Q.1),
      WeightedFormDomain Q (hessianMatrix V) W u ↔ ∀ᵐ x ∂ν, (fun i => (u i).val x) ∈ W) ∧
    (∀ u z, Integrable (matrixFieldPair (hessianMatrix V)
      (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val)
      (fun i => (MatrixEnergy.vectorEquiv Q hQ z i).val)) ν ∧
      Aphys u z = OperatorSchur.vectorEnergy Q hQ u z + ∫ x, matrixFieldPair (hessianMatrix V)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ z i).val) x ∂ν) ∧
    S = SchurRestriction.schurForm Q hQ n M hnM s hM K Cstar ks gs ε β.val hCstar β.property A hA ∧
    Aphys = S+T ∧
    (∀ u w, β.val⁻¹*OperatorSchur.vectorEnergy Q hQ (Re u) w +
      (∫ x, P (0,Re u) (0,w) x ∂ν) = ∫ x, P (u,0) (0,w) x ∂ν) ∧
    (∀ u z, G u z = β.val * ∫ x, P (z,0) (0,Re u) x ∂ν) ∧
    (∀ u z, T u z = (∫ x : Ω, ∑ i,∑ k,
      (MatrixEnergy.vectorEquiv Q hQ u i).val x.val *
        (hessianMatrix V x.val i k - β.val*properActive β s n m M hM hnM K θ ε κ₀ x i k)*
          (MatrixEnergy.vectorEquiv Q hQ z k).val x.val ∂μ) + G u z) ∧
    (∀ f : PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν),
      (∃! v, ∀ z, S v z = inner ℝ f (OperatorSchur.vectorValues Q hQ z)) ∧
      (∃! ψ, ∀ z, Aphys ψ z = inner ℝ f (OperatorSchur.vectorValues Q hQ z))) := by
  intro ν Ω μ Q hQ hreal hco A heq hA V J P
  obtain ⟨hdom,F,S,G,Aphys,T,Re,hF,_,_,hS,hRe,hG,_,hAT,hforms,hsol,_⟩ :=
    comparison_on_realization_internal β s n m hnN θ ε κ₀ hε M hM hhalf K hK hKM Q hQ hreal
  have hf := MeasurableEmbedding.subtype_coe (AffineSimplex.isOpen_chartDomain (n : ℕ) ((n+m : ℕ)+1)).measurableSet
  obtain ⟨_,_,hSeq⟩ := PhysicalMean.carrier_schur_form_internal _ hf hco Q hQ s n M hnM hM K
    Cstar ks gs ε β.val hCstar β.property _ A heq hA F S G Re
    (fun u z => (hF u z).2) hS (fun u z => (hRe u z).2.2) (fun u z => (hG u z).2)
  have hint (z z') : (∫ x : Ω, P z z' x.val ∂μ) = ∫ x, P z z' x ∂ν :=
    hco.integral_comp hf _
  refine ⟨S,Aphys,T,G,Re,hdom,?_,hSeq,hAT,?_,?_,?_,hsol⟩
  · intro u z
    exact ⟨(hforms u z).1,(hforms u z).2.1⟩
  · intro u w
    have hh := (hRe u w).2.2
    change β.val⁻¹*OperatorSchur.vectorEnergy Q hQ (Re u) w +
      (∫ x : Ω, P (0,Re u) (0,w) x.val ∂μ) = ∫ x : Ω, P (u,0) (0,w) x.val ∂μ at hh
    rwa [hint,hint] at hh
  · intro u z
    have hh := (hG u z).2
    change G u z = β.val * ∫ x : Ω, P (z,0) (0,Re u) x.val ∂μ at hh
    rwa [hint] at hh
  · intro u z
    exact (hforms u z).2.2.2.2.2.2

/-- See the proof of Proposition 5.18 in the paper: the two actual equations have
a common polynomial supremum bound, on their full physical form domains. -/
theorem solution_suprema_internal
    (β : InverseTemperature) (s : Riesz1.RieszExponent) (n : ℕ+) (m : ℕ)
    (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) (hε : 0 < ε) (Cstar ks gs p q : ℝ) (hq : 0 < q)
    (hpks : ks ≤ p) (hps : s.val+2 ≤ p)
    (hqcore : q ≤ β.val*Cstar⁻¹) (hqphys : q ≤ β.val*min 1 (s.val*(s.val+1))) :
    let ν := activeTiltedGapLaw (ofLong β s) ((n : ℕ)+m).succPNat n (by simp; omega) θ ε false
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      β.val*∑ i,θ.val ((n : ℝ)^(-ε)*x i) - Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (x,z)).toReal)
    ∀ (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
      (A : EuclideanSpace ℝ (Fin (n : ℕ)) → Matrix (Fin (M : ℕ)) (Fin (M : ℕ)) ℝ),
      PeriodizedMatrixBounds (ν := ν) s n M hM K Cstar ks gs ε A →
    ∀ (Aphys : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ]
      MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ →L[ℝ] ℝ),
    (∀ u z, Integrable (matrixFieldPair (hessianMatrix V)
      (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val)
      (fun i => (MatrixEnergy.vectorEquiv Q hQ z i).val)) ν ∧
      Aphys u z = OperatorSchur.vectorEnergy Q hQ u z + ∫ x, matrixFieldPair (hessianMatrix V)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ u i).val)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ z i).val) x ∂ν) →
    ∀ (χ : Lp ℝ 2 ν) (B : ℝ), 0 ≤ B → (∀ᵐ x ∂ν, |χ x| ≤ B) →
    ∀ (i₀ : Fin (n : ℕ)) (Ψ : Fin (M : ℕ) → Q.1)
      (v ψ : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ),
    WeightedWeakSolution Q (fun x => β.val • A x) ⊤
      (fun j => if j=i₀.castLE hnM then χ else 0) Ψ →
    (∀ i, Ψ (i.castLE hnM) = MatrixEnergy.vectorEquiv Q hQ v i) →
    (∀ z, Aphys ψ z = inner ℝ (WithLp.toLp 2 (fun i => if i=i₀ then χ else 0))
      (OperatorSchur.vectorValues Q hQ z)) →
    let P := q⁻¹*(n : ℝ)^(p*ε)*B
    (∀ k, ∀ᵐ x ∂ν, |(MatrixEnergy.vectorEquiv Q hQ v k).val x| ≤ P) ∧
    ∀ j, ∀ᵐ x ∂ν, |(MatrixEnergy.vectorEquiv Q hQ (v-ψ) j).val x| ≤ 2*P := by
  intro ν V Q hQ A hA Aphys hphysical χ B hB hχ i₀ Ψ v ψ hΨ hcomp hψ
  let v' := MatrixEnergy.vectorEquiv Q hQ v
  have hpot := PhysicalFormDomain.proper_gibbs_potential β s n m θ ε
  have hΩ := AffineSimplex.isOpen_chartDomain (n : ℕ) ((n+m : ℕ)+1)
  let P := q⁻¹ * (n : ℝ)^(p*ε) * B
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by positivity
  let mass := q * (n : ℝ)^(-p*ε)
  have hmass : 0 < mass := by dsimp [mass]; positivity
  have hsmall (b k : ℝ) (hb : q ≤ β.val*b) (hk : k ≤ p) :
      mass ≤ β.val*b*(n : ℝ)^(-k*ε) := by
    exact mul_le_mul hb (Real.rpow_le_rpow_of_exponent_le hn1
      (by nlinarith only [hk,hε])) (Real.rpow_nonneg hn0.le _) (hq.le.trans hb)
  have hcoremass : mass ≤ β.val*Cstar⁻¹*(n : ℝ)^(-ks*ε) := hsmall _ _ hqcore hpks
  have hphysmass : mass ≤ β.val*(min 1 (s.val*(s.val+1)))*(n : ℝ)^(-(s.val+2)*ε) := hsmall _ _ hqphys hps
  have hmassB : mass⁻¹*B = P := by
    dsimp only [mass,P]
    rw [show -p*ε = -(p*ε) by ring, mul_inv_rev, Real.rpow_neg hn0.le, inv_inv]
    ring
  have hcoreM : ∀ᵐ x ∂ν, (∀ i k, (β.val • A x) i k = (β.val • A x) k i) ∧
      ∀ z : Fin (M : ℕ) → ℝ, mass*(∑ i,z i^2) ≤ ∑ i,∑ k,z i*(β.val • A x) i k*z k := by
    filter_upwards [hA.2.1,SchurRestriction.periodized_scaled_lower β.val β.property hA] with x hx hl
    refine ⟨fun i k => by simp only [Matrix.smul_apply,smul_eq_mul,hx.1 i k],?_⟩
    intro z
    apply (mul_le_mul_of_nonneg_right hcoremass (Finset.sum_nonneg (fun i _ => sq_nonneg (z i)))).trans
    simpa only [mul_assoc] using hl z
  have hΨB := point_source_component_bound_internal Q hQ (fun x => β.val • A x)
    (fun i k => measurable_const.mul (hA.1 i k)) mass hmass hcoreM (i₀.castLE hnM) χ B hB hχ Ψ hΨ
  have hvB (k : Fin (n : ℕ)) : ∀ᵐ x ∂ν, |(v' k).val x| ≤ P := by
    filter_upwards [hΨB] with x hx
    simpa only [hcomp,hmassB] using hx (k.castLE hnM)
  have hphysM : ∀ᵐ x ∂ν, (∀ i k, hessianMatrix V x i k = hessianMatrix V x k i) ∧
      ∀ z : Fin (n : ℕ) → ℝ, mass*(∑ i,z i^2) ≤ ∑ i,∑ k,z i*hessianMatrix V x i k*z k := by
    filter_upwards [IntrinsicScalarCore.supported hΩ hpot,
      (PhysicalIdentity.proper_physical_lower β s n m θ ε hε.le).2] with x hx hl
    refine ⟨fun i k => DecayShort.PhysicalComparison.hessianMatrix_symm
      ((hpot.1.of_le (by norm_num)).contDiffAt (hΩ.mem_nhds hx)) i k,?_⟩
    intro z
    exact (mul_le_mul_of_nonneg_right hphysmass (Finset.sum_nonneg (fun i _ => sq_nonneg (z i)))).trans
      (by simpa only [mul_assoc] using hl z)
  have hψweak := weak_of_form_internal Q hQ _ Aphys
    (fun u z => hphysical u z) (fun i => if i=i₀ then χ else 0) ψ hψ
  have hψB := point_source_component_bound_internal Q hQ _
    (fun i k => DifferentiatedPoisson.measurable_hessian_entries i k) mass hmass hphysM i₀ χ B hB hχ
    (MatrixEnergy.vectorEquiv Q hQ ψ) hψweak
  refine ⟨hvB,?_⟩
  intro j
  have hwB : ∀ᵐ x ∂ν, |(MatrixEnergy.vectorEquiv Q hQ (v-ψ) j).val x| ≤ 2*P := by
    filter_upwards [hvB j,hψB,Lp.coeFn_sub (v' j).val (MatrixEnergy.vectorEquiv Q hQ ψ j).val] with x hx hy he
    change |((v' j).val - (MatrixEnergy.vectorEquiv Q hQ ψ j).val : Lp ℝ 2 ν) x| ≤ _
    rw [he]
    exact (abs_sub _ _).trans (by simpa only [hmassB,two_mul] using add_le_add hx (hy j))
  exact hwB

/-- See the proof of Proposition 5.18 in the paper: form identification preserves
the equation without unfolding the constructions of the forms. -/
theorem equation_congr_internal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F G : E →L[ℝ] E →L[ℝ] ℝ) (he : F=G) (u : E) (r : E → ℝ)
    (hu : ∀ z, F u z = r z) : ∀ z, G u z = r z := by
  rw [← he]
  exact hu

end Riesz2.PhysicalPerturbation


