/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.LengthAveragingFibresPart3
public import Riesz2.Thermodynamic.LengthAveragingFibresPart4
public import Riesz2.DecayLong.PerturbationBoundsPart2
public import Riesz2.ToMathlib.GoodSetL2Comparison

/-!
# Physical normal estimates on marginal length fibres

Supporting estimates for the proof of Lemma 6.5 and equation (6.24). The physical
two-sided penalty retains its exponent. The fine event has its separate tolerance.
Comparison losses are explicit.
-/

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators Classical ContDiff

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.LengthAveragingFibres

/-- See the proof of Lemma 6.5 in the paper: the long conditional error
is finite almost everywhere, for every envelope exponent and fine event.
This uses the fourth moment, without a rigidity or tail hypothesis. -/
theorem longRemainder_finite_of_moments (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n m : ℕ) (θ : PhysicalCutoff) (ε C₀ η κ : ℝ) (hε : 0 < ε)
    (hhalf : 2 * (n + 1) ≤ n + 1 + m + 1) :
    ∀ᵐ L ∂lengthMeasure (ofLong β s) n m θ ε,
      longRemainder β s n m θ ε C₀ η κ L < (∞ : ℝ≥0∞) := by
  filter_upwards [longEnvelope_memLp_two_ae β s n m θ ε C₀ hε hhalf] with L hL
  have hInt := hL.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hnn (x) : 0 ≤ longEnvelope β s n.succPNat m θ ε C₀ x :=
    (Real.rpow_nonneg (by positivity) C₀).trans
      (longEnvelope_lower β s n.succPNat m θ ε C₀ x)
  have hfinite := (lintegral_ofReal_ne_top_iff_integrable hInt.aestronglyMeasurable
    (ae_of_all _ hnn)).mpr hInt
  exact (lintegral_mono' Measure.restrict_le_self le_rfl).trans_lt hfinite.lt_top

/-- Internal form-level maximum principle for the physical long marginal
in equation (6.24). Its curvature factor depends only on
`s` and temperature. Its size exponent is `(s+2)ε`. -/
theorem long_solution_bound_internal (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε : ℝ) (hε : 0 ≤ ε)
    (ρ : Measure (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)))
    (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q) :
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      β.val * ∑ i, (θ.val ((n : ℝ)^(-ε)*x i) + θ.val ((n : ℝ)^(-ε)*(x i)⁻¹)) -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (x,z)).toReal)
    ∀ (S : Submodule ℝ (Fin (n : ℕ) → ℝ)) (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ρ)
      (B : ℝ), 0 ≤ B → (∀ᵐ x ∂ρ, |χ x| ≤ B) → ∀ u : Fin (n : ℕ) → Q.1,
      WeightedWeakSolution Q (fun x => hessianMatrix V x.val) S
        (fun i => if i = i₀ then χ else 0) u →
      ∀ j, ∀ᵐ x ∂ρ, |(u j).val x| ≤
        β.val⁻¹ * (n : ℝ)^((s.val+2)*ε) * (min 1 (s.val*(s.val+1)))⁻¹ * B := by
  intro V S i₀ χ B hB hχ u hu
  obtain ⟨ha, hmatrix⟩ := long_twoSided_matrix_internal β s n m θ ε hε
  obtain ⟨hsm, _⟩ := long_twoSided_curvature_internal β s n m θ ε hε
  have hm (i j) : Measurable (fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) =>
      hessianMatrix V x.val i j) :=
    DecayShort.PhysicalComparison.measurable_hessianMatrix
      (AffineSimplex.isOpen_chartDomain n _) hsm i j
  have hM : ∀ᵐ x ∂ρ, (∀ i j, hessianMatrix V x.val i j = hessianMatrix V x.val j i) ∧
      ∀ z : Fin (n : ℕ) → ℝ,
        (β.val*min 1 (s.val*(s.val+1))*(n : ℝ)^(-(s.val+2)*ε))*(∑ i, z i^2) ≤
          ∑ i, ∑ j, z i*hessianMatrix V x.val i j*z j := by
    apply ae_of_all
    intro x
    refine ⟨?_, (hmatrix x).2⟩
    intro i j
    exact DecayShort.PhysicalComparison.hessianMatrix_symm
      ((hsm.contDiffAt ((AffineSimplex.isOpen_chartDomain n _).mem_nhds
        x.property)).of_le (by norm_num)) i j
  have hb := (FixedLengthDecay.point_source_ae_bound_internal Q hQ _ hm _ ha hM
    S i₀ χ B hB hχ u hu).2
  have he : (β.val*min 1 (s.val*(s.val+1))*(n : ℝ)^(-(s.val+2)*ε))⁻¹ =
      β.val⁻¹ * (n : ℝ)^((s.val+2)*ε) * (min 1 (s.val*(s.val+1)))⁻¹ := by
    rw [mul_inv, mul_inv, ← Real.rpow_neg (by positivity : (0 : ℝ) ≤ n)]
    rw [show -(-(s.val+2)*ε) = (s.val+2)*ε by ring]
    ring
  simpa only [he] using hb

/-- See equation (6.24) of the paper, long exceptional contribution on a
closed retained-fibre form. The actual physical maximum principle is
proved above. Finiteness precedes conversion of the conditional error. -/
theorem long_exceptional_multiplier_internal (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n m : ℕ) (θ : PhysicalCutoff) (ε C₀ η κ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hC₀ : s.val + 5 ≤ C₀) (hhalf : 2 * (n + 1) ≤ n + 1 + m + 1) :
    let V := fun x : EuclideanSpace ℝ (Fin (n + 1)) =>
      β.val * ∑ i, (θ.val ((n+1 : ℝ)^(-ε)*x i) + θ.val ((n+1 : ℝ)^(-ε)*(x i)⁻¹)) -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity (ofLong β s) (n+1) m (Equiv.refl _) (x,z)).toReal)
    let M := fun x : AffineSimplex.chartDomain (n+1) ((n+1+m : ℕ)+1) =>
      hessianMatrix V x.val
    ∀ᵐ L ∂lengthMeasure (ofLong β s) n m θ ε,
      let ρ := retainedKernel (ofLong β s) n m θ ε L
      ∀ (Q : ScalarFormData ρ), IsClosedScalarDirichletForm Q →
      ∀ (S : Submodule ℝ (Fin (n+1) → ℝ)) (i₀ : Fin (n+1)) (χ : Lp ℝ 2 ρ)
        (B : ℝ), 0 ≤ B → (∀ᵐ x ∂ρ, |χ x| ≤ B) → ∀ u : Fin (n+1) → Q.1,
        WeightedWeakSolution Q M S (fun i => if i = i₀ then χ else 0) u →
        let Λ := gapMultiplierField n.succPNat Q M (fun i => if i = i₀ then χ else 0) u
        longRemainder β s n m θ ε C₀ η κ L < (∞ : ℝ≥0∞) ∧ Integrable Λ ρ ∧
        |∫ x in (longFineEvent β s n.succPNat m η κ)ᶜ, Λ x ∂ρ| ≤
          2 * (min 1 (s.val*(s.val+1)))⁻¹ * B *
            (longRemainder β s n m θ ε C₀ η κ L).toReal := by
  intro V M
  let r := min 1 (s.val*(s.val+1))
  have hr : 0 < r := lt_min zero_lt_one (mul_pos s.property.1 (by linarith [s.property.1]))
  have hr1 : 1 ≤ r⁻¹ := (one_le_inv₀ hr).mpr (min_le_left _ _)
  obtain ⟨hsm, _⟩ := long_twoSided_curvature_internal β s n.succPNat m θ ε hε.le
  simp only [Nat.succPNat_coe, Nat.cast_succ] at hsm
  filter_upwards [longEnvelope_memLp_two_ae β s n m θ ε C₀ hε hhalf,
    longRemainder_finite_of_moments β s n m θ ε C₀ η κ hε hhalf] with L hW2 hfin
  intro ρ Q hQ S i₀ χ B hB hχ u hu Λ
  let W := longEnvelope β s n.succPNat m θ ε C₀
  have hW0 (x) : 0 ≤ W x := (Real.rpow_nonneg (by positivity) C₀).trans
    (longEnvelope_lower β s n.succPNat m θ ε C₀ x)
  have hentry (x : AffineSimplex.chartDomain (n+1) ((n+1+m : ℕ)+1)) (i j) :
      |M x i j| ≤ β.val*(n+1 : ℝ)^(2-C₀)*W x := by
    have hh := long_twoSided_envelope_internal β s n.succPNat m θ ε C₀ hε.le x i j
    simp only [Nat.succPNat_coe, Nat.cast_succ] at hh
    change |M x i j| ≤ _ at hh
    apply hh.trans
    have hp : (n+1 : ℝ)*(n+1 : ℝ)^(-C₀) ≤ (n+1 : ℝ)^(2-C₀) := by
      calc
        _ = (n+1 : ℝ)^(1-C₀) := by rw [Real.rpow_sub (by positivity), Real.rpow_one,
          Real.rpow_neg (by positivity)]; ring
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast n.succ_pos) (by linarith)
    simpa only [Nat.succPNat_coe, Nat.cast_succ, W, mul_assoc] using
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp (hW0 x)) β.property.le
  have hpair (i j) : Integrable (fun x => M x i j * (u j).val x) ρ := by
    have hm := DecayShort.PhysicalComparison.measurable_hessianMatrix
      (AffineSimplex.isOpen_chartDomain (n+1) _) hsm i j
    have hM2 := (hW2.const_mul (β.val*(n+1 : ℝ)^(2-C₀))).mono'
      hm.aestronglyMeasurable (ae_of_all _ fun x => by
        simpa only [Real.norm_eq_abs] using hentry x i j)
    exact hM2.integrable_mul (Lp.memLp (u j).val)
  have hΛ := (multiplier_mean_internal n.succPNat Q M
    (fun i => if i = i₀ then χ else 0) u hpair).1
  have huB := long_solution_bound_internal β s n.succPNat m θ ε hε.le ρ Q hQ
    S i₀ χ B hB hχ u (by simpa only [Nat.succPNat_coe, Nat.cast_succ] using hu)
  have hs0 := s.property.1
  have hbound : ∀ᵐ x ∂ρ, |Λ x| ≤ 2*(r⁻¹*B)*W x := by
    filter_upwards [ae_all_iff.mpr huB, hχ, Lp.coeFn_zero ℝ 2 ρ] with x hx hχx hz
    have hv : (∑ i, (if i = i₀ then χ else 0 : Lp ℝ 2 ρ) x) = χ x := by
      simp only [apply_ite (fun f : Lp ℝ 2 ρ => f x), hz, Pi.zero_apply,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    change |(n.succPNat : ℝ)⁻¹ * ((∑ i, ∑ j, M x i j * (u j).val x) -
      ∑ i, (if i = i₀ then χ else 0 : Lp ℝ 2 ρ) x)| ≤ _
    rw [hv]
    apply exceptional_normal_absorption_internal n.succPNat β.val ((s.val+2)*ε) C₀
      (W x) (r⁻¹*B) (χ x) β.property (by positivity)
      (by nlinarith [mul_le_mul_of_nonneg_left hε1 (by linarith [s.property.1] : 0 ≤ s.val+2)])
      (by positivity) (longEnvelope_lower β s n.succPNat m θ ε C₀ x) (M x)
      (fun j => (u j).val x)
    · simpa only [Nat.succPNat_coe, Nat.cast_succ] using hentry x
    · intro j
      simpa only [Nat.succPNat_coe, Nat.cast_succ, mul_assoc, r] using hx j
    · exact hχx.trans (le_mul_of_one_le_left hB hr1)
  let G := longFineEvent β s n.succPNat m η κ
  have hIW : Integrable W (ρ.restrict Gᶜ) :=
    (hW2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).mono_measure Measure.restrict_le_self
  have he : (∫ x in Gᶜ, W x ∂ρ) = (longRemainder β s n m θ ε C₀ η κ L).toReal :=
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hW0) hIW.aestronglyMeasurable
  refine ⟨hfin, hΛ, ?_⟩
  have hi := norm_integral_le_of_norm_le (f := Λ) (μ := ρ.restrict Gᶜ)
    (hIW.const_mul (2*(r⁻¹*B)))
    (ae_restrict_of_ae (hbound.mono fun x hx => by simpa only [Real.norm_eq_abs] using hx))
  rw [integral_const_mul, he, Real.norm_eq_abs] at hi
  simpa only [r, mul_assoc] using hi


/-- Internal covariance bridge for the proof of Lemma 6.5:
ambient realizations agreeing with the same physical energy give
the same compensated-score covariance under the actual exterior law. -/
theorem compensated_covariance_eq_internal (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ)
    (U W : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ)
    (hv : ∀ y : gapAmbientDomain ((n : ℕ)+m).succPNat, U y.val = W y.val)
    (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1)) (i j : Fin (n : ℕ)) :
    let c := fun z => RetainedSimplex.chart n m ((n+m : ℕ)+1) (Equiv.refl _) (x.val,z)
    let q := WithLp.toLp 2 (ConditionalForces.compensationVector n m)
    let X := fun A k z => β.val⁻¹ * (fderiv ℝ A (c z)
      (EuclideanSpace.single (k.castAdd m).castSucc 1) - fderiv ℝ A (c z) q)
    let μ := ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x
    ProbabilityTheory.covariance (X U i) (X U j) μ =
      ProbabilityTheory.covariance (X W i) (X W j) μ := by
  intro c q X μ
  have he (k : Fin (n : ℕ)) : X U k =ᵐ[μ] X W k := by
    have h₁ := DecayShort.PhysicalComparison.internal_score_extension_ae (ofLong β s) n m n.pos U W hv x
      (EuclideanSpace.single (k.castAdd m).castSucc 1)
    have h₂ := DecayShort.PhysicalComparison.internal_score_extension_ae (ofLong β s) n m n.pos U W hv x q
    filter_upwards [h₁, h₂] with z hz₁ hz₂
    change β.val⁻¹ * (_ - _) = β.val⁻¹ * (_ - _)
    rw [mul_sub, mul_sub]
    exact congrArg₂ (· - ·) hz₁ hz₂
  unfold ProbabilityTheory.covariance
  rw [integral_congr_ae (he i), integral_congr_ae (he j)]
  apply integral_congr_ae
  filter_upwards [he i, he j] with z hi hj
  rw [hi, hj]

/-- See the proof of Lemma 6.5 in the paper: long good-event physical
columns, with the simplified boundary profile and a prefactor uniform over
any prescribed compact temperature interval. The matrix is the Hessian of
the actual negative logarithm, so includes the factor `β`. -/
theorem long_fine_hessian_columns (s : Riesz1.RieszExponent) (θ : PhysicalCutoff)
    (κ : ℝ) (hκ : 1 ≤ κ) :
    ∃ k : ℝ, 0 < k ∧ ∀ η βlo βhi : ℝ, 0 < η → 0 < βlo → βlo ≤ βhi →
      ∃ C : ℝ, 0 < C ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n : ℕ+) (m : ℕ), 2*(n : ℕ) ≤ (n : ℕ)+m+1 →
      ∀ ε : ℝ, 0 ≤ ε →
      let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
        β.val * ∑ i, (θ.val ((n : ℝ)^(-ε)*x i) + θ.val ((n : ℝ)^(-ε)*(x i)⁻¹)) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (x,z)).toReal)
      ∀ x : AffineSimplex.chartDomain n ((n+m : ℕ)+1),
        x ∈ longFineEvent β s n m η κ → ∀ j : Fin (n : ℕ),
        (∑ i, |hessianMatrix V x.val i j|) ≤ C*(n : ℝ)^(k*η)*
          ((n : ℝ)^(1-s.val) + (n : ℝ)^(1-s.val/2)*
            InteractionDifferential.boundaryWeight s.val n j) := by
  obtain ⟨Cp, hCp, hpen⟩ := penalty_fine_bound θ
  let k := 2*(κ+7)+4
  refine ⟨k, by dsimp only [k]; linarith, fun η βlo βhi hη hlo hle => ?_⟩
  let T := βlo⁻¹*(128*(5/Real.log 2+4)*(Real.log 2+1/η)+1)
  let A := 2/(1-s.val)
  let D := 2/(1-s.val/2)
  let C := βhi*(Cp+A+3)+βhi^2*(T+1)^2*D
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hA : 0 < A := div_pos (by norm_num) (by linarith [s.property.2])
  have hD : 0 < D := div_pos (by norm_num) (by linarith [s.property.2])
  have hhi : 0 < βhi := hlo.trans_le hle
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro β hβ n m hhalf ε hε V x hx j
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  let N : ℝ := (n : ℝ)+m+1
  let P := GoodBlocks.conditionalHessian β s n m
  let b := ConditionalForces.compensationB β s n m
  let c := ConditionalForces.compensationC β s n m
  let w := InteractionDifferential.boundaryWeight s.val n
  let R := (n : ℝ)^(k*η)
  have hR : 0 ≤ R := Real.rpow_nonneg hn0.le _
  have hp (a : ℝ) (ha : a ≤ k) : (n : ℝ)^(a*η) ≤ R :=
    Real.rpow_le_rpow_of_exponent_le hn1 (mul_le_mul_of_nonneg_right ha hη.le)
  have hc0 : 0 ≤ c x := ConditionalForces.compensationC_nonneg β s n m x
  have hb0 (i) : 0 ≤ b i x := ConditionalForces.compensationB_nonneg β s n m i x
  have hbc (i) : c x + b i x ≤ (n : ℝ)^(κ*η)*N^(-s.val) := by
    have hh := hx.2.1 i
    change N^s.val*(c x+b i x) ≤ _ at hh
    have hN : 0 < N := by dsimp only [N]; positivity
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hN s.val)).mpr (by simpa only [mul_comm] using hh) |>.trans_eq
    rw [div_eq_mul_inv, ← Real.rpow_neg hN.le]
  have hc : c x ≤ (n : ℝ)^(κ*η)*N^(-s.val) :=
    (le_add_of_nonneg_right (hb0 j)).trans (hbc j)
  have hQ (i) : |ConditionalForces.compensationQ β s n m i j x| ≤
      3*(n : ℝ)^(κ*η)*N^(-s.val) := by
    have hi := (le_add_of_nonneg_left hc0).trans (hbc i)
    have hj := (le_add_of_nonneg_left hc0).trans (hbc j)
    have hh : |-b i x-b j x| ≤ b i x+b j x := by
      simpa only [abs_neg, abs_of_nonneg (hb0 i), abs_of_nonneg (hb0 j)] using
        abs_sub (-b i x) (b j x)
    have ht := (abs_add_le (-b i x-b j x) (c x)).trans
      (add_le_add hh (le_of_eq (abs_of_nonneg hc0)))
    change |-b i x-b j x+c x| ≤ _
    linarith
  have hsumP : (∑ i, P i j x) ≤ (n : ℝ)^(κ*η)*A*(n : ℝ)^(1-s.val) := by
    have hh := LocalizedBoundary.active_weight_sum_internal n ((n : ℕ)+m).succPNat
      (by simpa only [Nat.succPNat_coe] using hhalf) j s.val s.property.1 s.property.2
    have he (i : Fin (n : ℕ)) :
        (1+(Riesz1.cyclicIndexDistance ((n : ℕ)+m).succPNat
          (i.castAdd m).castSucc (j.castAdd m).castSucc : ℝ))^(-s.val) =
        weightRadius ((n : ℕ)+m).succPNat (j.castLE (by simp; omega))
          (i.castLE (by simp; omega)) ^ (-s.val) := by
      congr 1
      unfold weightRadius
      rw [cyclicIndexDistance_comm']
      rfl
    apply (Finset.sum_le_sum (fun i _ => hx.1.2 i j)).trans
    simp_rw [he]
    rw [← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by dsimp only [A]; ring)
  obtain ⟨U, hU, hv, hH⟩ := long_twoSided_hessian_internal β s n m θ ε
  obtain ⟨W, _hW, hw, hvar⟩ := ConditionalForces.compensated_force_variance β s n m
  let μ := ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x
  let q := WithLp.toLp 2 (ConditionalForces.compensationVector n m)
  let Xi := fun (Z : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ) (i : Fin (n : ℕ)) z => β.val⁻¹ *
    (fderiv ℝ Z (RetainedSimplex.chart n m ((n+m : ℕ)+1) (Equiv.refl _) (x.val,z))
      (EuclideanSpace.single (i.castAdd m).castSucc 1) -
     fderiv ℝ Z (RetainedSimplex.chart n m ((n+m : ℕ)+1) (Equiv.refl _) (x.val,z)) q)
  have : IsProbabilityMeasure μ := ProperMarginalChart.conditionalMeasure_probability
    (ofLong β s) n m n.pos (Equiv.refl _) x
  have hXi (i) : MemLp (Xi W i) 2 μ := (hvar x i).1.1
  have hvbound (i) : Real.sqrt (∫ z, (Xi W i z-∫ a, Xi W i a ∂μ)^2 ∂μ) ≤
      (T+1)*(n : ℝ)^((κ+7)*η)*w i := by
    have hh := (hvar x i).2.1.trans (hvar x i).2.2
    apply (Real.sqrt_le_sqrt hh).trans
    have hdepth := PerturbationBounds.variance_depth_bound β s βlo η κ hlo hβ.1 hη hκ n m
      hhalf x hx.1 hc i
    apply (Real.sqrt_le_sqrt hdepth).trans
    simpa only [InteractionDifferential.boundaryWeight_long s.property.2, w, T] using
      (PerturbationBounds.sqrt_depth_internal hT hn1
        (by nlinarith : 0 ≤ (κ+7)*η)
        (InteractionDifferential.boundary_distance_pos n i))
  have hcov (i) : |ProbabilityTheory.covariance (Xi U i) (Xi U j) μ| ≤
      (T+1)^2*R*w i*w j := by
    rw [compensated_covariance_eq_internal β s n m U W
      (fun y => (hv y).trans (hw y).symm) x i j]
    apply (CovarianceCauchySchwarz.abs_covariance_le (hXi i) (hXi j)).trans
    have hwi : 0 ≤ w i := by dsimp only [w, InteractionDifferential.boundaryWeight]; positivity
    have hh := mul_le_mul (hvbound i) (hvbound j) (Real.sqrt_nonneg _)
      (by positivity : 0 ≤ (T+1)*(n : ℝ)^((κ+7)*η)*w i)
    apply hh.trans
    have he : (n : ℝ)^((κ+7)*η)*(n : ℝ)^((κ+7)*η) =
        (n : ℝ)^((2*(κ+7))*η) := by rw [← Real.rpow_add hn0]; congr 1; ring
    have hr := hp (2*(κ+7)) (by dsimp only [k]; linarith)
    have hw0 : 0 ≤ w i*w j := by
      dsimp only [w, InteractionDifferential.boundaryWeight]; positivity
    calc
      _ = (T+1)^2*((n : ℝ)^((κ+7)*η)*(n : ℝ)^((κ+7)*η))*(w i*w j) := by ring
      _ ≤ (T+1)^2*R*(w i*w j) := by rw [he]; gcongr
      _ = _ := by ring
  have hws : (∑ i, w i) ≤ D*(n : ℝ)^(1-s.val/2) := by
    simpa only [w, InteractionDifferential.boundaryWeight_long s.property.2, D,
      neg_div] using LocalizedBoundary.boundary_weight_sum_internal n (s.val/2)
        (by linarith [s.property.1]) (by linarith [s.property.2])
  have hF : (∑ i, |InterpolationMatrix.penaltyHessian n θ ε x.val i j|) ≤
      Cp*(n : ℝ)^(4*η) := by
    exact (Finset.sum_le_sum (fun i _ => hpen n ε η hε hη.le x.val
      (fun a => (hx.1.1.1 a).1) i j)).trans_eq (by simp)
  have hentry (i) : |hessianMatrix V x.val i j| ≤
      β.val*(|InterpolationMatrix.penaltyHessian n θ ε x.val i j| + P i j x +
        3*(n : ℝ)^(κ*η)*N^(-s.val)) + β.val^2*((T+1)^2*R*w i*w j) := by
    rw [(hH x).2 i j]
    apply (abs_sub _ _).trans
    rw [abs_mul, abs_of_pos β.property, abs_mul, abs_of_nonneg (sq_nonneg β.val)]
    apply add_le_add _ (mul_le_mul_of_nonneg_left (hcov i) (sq_nonneg _))
    apply mul_le_mul_of_nonneg_left _ β.property.le
    apply (abs_add_le _ _).trans
    apply add_le_add ((abs_add_le _ _).trans (add_le_add le_rfl
      (le_of_eq (abs_of_nonneg (GoodBlocks.conditionalHessian_nonneg β s n m i j x))))) (hQ i)
  have hNpow : (n : ℝ)*N^(-s.val) ≤ (n : ℝ)^(1-s.val) := by
    have hh := Real.rpow_le_rpow_of_nonpos hn0
      (show (n : ℝ) ≤ N by dsimp only [N]; have := Nat.cast_nonneg m (α := ℝ); linarith)
      (neg_nonpos.mpr s.property.1.le)
    apply (mul_le_mul_of_nonneg_left hh hn0.le).trans_eq
    rw [Real.rpow_sub hn0, Real.rpow_one, Real.rpow_neg hn0.le, div_eq_mul_inv]
  have hQsum : (n : ℝ)*(3*(n : ℝ)^(κ*η)*N^(-s.val)) ≤
      3*R*(n : ℝ)^(1-s.val) := by
    have hh := mul_le_mul (hp κ (by dsimp only [k]; linarith)) hNpow
      (by positivity) hR
    nlinarith only [hh]
  have hmain := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hentry i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hmain
  have hP : (∑ i, P i j x) ≤ R*A*(n : ℝ)^(1-s.val) :=
    hsumP.trans (by gcongr; exact hp κ (by dsimp only [k]; linarith))
  have hF' := hF.trans (mul_le_mul_of_nonneg_left (hp 4 (by dsimp only [k]; linarith)) hCp.le)
  have hnsp : 1 ≤ (n : ℝ)^(1-s.val) := Real.one_le_rpow hn1 (by linarith [s.property.2])
  have hpen' : (∑ i, |InterpolationMatrix.penaltyHessian n θ ε x.val i j|) ≤
      Cp*R*(n : ℝ)^(1-s.val) := hF'.trans (le_mul_of_one_le_right (by positivity) hnsp)
  have hcol := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add hpen' hP) hQsum) β.property.le
  have hcv := mul_le_mul_of_nonneg_left hws
    (show 0 ≤ β.val^2*((T+1)^2*R)*w j by
      dsimp only [w, InteractionDifferential.boundaryWeight]; positivity)
  have hβ1 := mul_le_mul_of_nonneg_right hβ.2
    (show 0 ≤ (Cp+A+3)*R*(n : ℝ)^(1-s.val) by positivity)
  have hβ2 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ β.property.le hβ.2 2)
    (show 0 ≤ (T+1)^2*R*w j*(D*(n : ℝ)^(1-s.val/2)) by
      dsimp only [w, InteractionDifferential.boundaryWeight]; positivity)
  have hn1s : 0 ≤ (n : ℝ)^(1-s.val) := by positivity
  have hn2s : 0 ≤ (n : ℝ)^(1-s.val/2)*w j := by
    dsimp only [w, InteractionDifferential.boundaryWeight]; positivity
  dsimp only [C, R] at *
  nlinarith only [hmain, hcol, hcv, hβ1, hβ2,
    mul_nonneg (show 0 ≤ βhi*(Cp+A+3) by positivity)
      (mul_nonneg (Real.rpow_nonneg hn0.le (k*η)) hn2s),
    mul_nonneg (show 0 ≤ βhi^2*(T+1)^2*D by positivity)
      (mul_nonneg (Real.rpow_nonneg hn0.le (k*η)) hn1s)]


/-- See the proof of Lemma 6.5 in the paper, the common choice of `C₀`.
`Bℓ,Bₛ` are the squared comparison losses and `Dℓ,Dₛ` the subsequent
column/summation losses. Supplying these as functions of `s` gives a
single exponent depending only on `s`, before temperature or tolerance.
The comparison losses are parameters. -/
theorem common_envelope_exponent (s Bℓ Bₛ Dℓ Dₛ : ℝ) (hs : 0 < s) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ s+5 ≤ C₀ ∧
      Bℓ+2*Dℓ+10 < C₀ ∧ Bₛ+2*Dₛ+10 < C₀ ∧
      ∀ n : ℕ+, (n : ℝ)^Dℓ * Real.sqrt ((n : ℝ)^(Bℓ-C₀)) ≤ (n : ℝ)^(-5 : ℝ) ∧
        (n : ℝ)^Dₛ * Real.sqrt ((n : ℝ)^(Bₛ-C₀)) ≤ (n : ℝ)^(-5 : ℝ) := by
  let C₀ := max (s+5) (max (Bℓ+2*Dℓ+10) (Bₛ+2*Dₛ+10))+1
  have hCs : s+5 < C₀ := by
    dsimp only [C₀]
    linarith [le_max_left (s+5) (max (Bℓ+2*Dℓ+10) (Bₛ+2*Dₛ+10))]
  have hCℓ : Bℓ+2*Dℓ+10 < C₀ := by
    dsimp only [C₀]
    linarith [(le_max_left (Bℓ+2*Dℓ+10) (Bₛ+2*Dₛ+10)).trans
      (le_max_right (s+5) (max (Bℓ+2*Dℓ+10) (Bₛ+2*Dₛ+10)))]
  have hCₛ : Bₛ+2*Dₛ+10 < C₀ := by
    dsimp only [C₀]
    linarith [(le_max_right (Bℓ+2*Dℓ+10) (Bₛ+2*Dₛ+10)).trans
      (le_max_right (s+5) (max (Bℓ+2*Dℓ+10) (Bₛ+2*Dₛ+10)))]
  refine ⟨C₀, by linarith, hCs.le, hCℓ, hCₛ, fun n => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hb (B D : ℝ) (h : B+2*D+10 ≤ C₀) :
      (n : ℝ)^D * Real.sqrt ((n : ℝ)^(B-C₀)) ≤ (n : ℝ)^(-5 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn0.le, ← Real.rpow_add hn0]
    apply Real.rpow_le_rpow_of_exponent_le hn1
    linarith
  exact ⟨hb Bℓ Dℓ hCℓ.le, hb Bₛ Dₛ hCₛ.le⟩

/-- Internal good-set integration of equation (6.24).
The matrix and the multiplier are the existing physical objects supplied
by the caller. All pairings are globally integrable, and `χ` is an actual
L² point source. -/
theorem good_multiplier_integral_internal {X : Type*} [MeasurableSpace X]
    {ρ : Measure X} [IsProbabilityMeasure ρ] (n : ℕ+) (Q : ScalarFormData ρ)
    (M : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ρ) (u : Fin (n : ℕ) → Q.1)
    (G : Set X) (_hG : MeasurableSet G) (w : Fin (n : ℕ) → ℝ)
    (A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) (hw : ∀ j, 0 ≤ w j)
    (hpair : ∀ i j, Integrable (fun x => M x i j*(u j).val x) ρ)
    (hcol : ∀ᵐ x ∂ρ.restrict G, ∀ j, (∑ i, |M x i j|) ≤ A+D*w j) :
    let Λ := gapMultiplierField n Q M (fun i => if i = i₀ then χ else 0) u
    Integrable Λ ρ ∧ |∫ x in G, Λ x ∂ρ| ≤ (n : ℝ)⁻¹ *
      (A*(∑ j, ‖(u j).val‖) + D*(∑ j, w j*‖(u j).val‖) + ‖χ‖) := by
  intro Λ
  refine ⟨(multiplier_mean_internal n Q M _ u hpair).1, ?_⟩
  let H := fun x => (n : ℝ)⁻¹ *
    (A*(∑ j, |(u j).val x|) + D*(∑ j, w j*|(u j).val x|) + |χ x|)
  have hi (j) : Integrable (fun x => |(u j).val x|) ρ :=
    ((Lp.memLp (u j).val).integrable (by norm_num)).abs
  have hχ : Integrable (fun x => |χ x|) ρ :=
    ((Lp.memLp χ).integrable (by norm_num)).abs
  have hH : Integrable H ρ := by
    exact (((integrable_finsetSum _ (fun j _ => hi j)).const_mul A).add
      ((integrable_finsetSum _ (fun j _ => (hi j).const_mul (w j))).const_mul D)).add hχ |>.const_mul _
  have hbound : ∀ᵐ x ∂ρ.restrict G, |Λ x| ≤ H x := by
    filter_upwards [hcol, ae_restrict_of_ae (Lp.coeFn_zero ℝ 2 ρ)] with x hx hz
    have hv : (∑ i, (if i = i₀ then χ else 0 : Lp ℝ 2 ρ) x) = χ x := by
      simp only [apply_ite (fun f : Lp ℝ 2 ρ => f x), hz, Pi.zero_apply,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    change |(n : ℝ)⁻¹*((∑ i, ∑ j, M x i j*(u j).val x)-
      ∑ i, (if i = i₀ then χ else 0 : Lp ℝ 2 ρ) x)| ≤ _
    rw [hv]
    exact normal_column_bound_internal n (M x) (fun j => (u j).val x) w (χ x) A D hx
  have hnorm := norm_integral_le_of_norm_le (f := Λ) (μ := ρ.restrict G)
    (hH.mono_measure Measure.restrict_le_self)
    (hbound.mono fun x hx => by simpa only [Real.norm_eq_abs] using hx)
  rw [Real.norm_eq_abs] at hnorm
  apply hnorm.trans
  have hH0 : ∀ x, 0 ≤ H x := by
    intro x
    dsimp only [H]
    exact mul_nonneg (by positivity) (add_nonneg (add_nonneg
      (mul_nonneg hA (Finset.sum_nonneg fun _ _ => abs_nonneg _))
      (mul_nonneg hD (Finset.sum_nonneg fun j _ => mul_nonneg (hw j) (abs_nonneg _))))
      (abs_nonneg _))
  apply (setIntegral_le_integral hH (ae_of_all _ hH0)).trans
  dsimp only [H]
  rw [integral_const_mul, integral_add
    (f := fun x => A*(∑ j, |(u j).val x|)+D*(∑ j, w j*|(u j).val x|))
    (g := fun x => |χ x|)
    (((integrable_finsetSum _ (fun j _ => hi j)).const_mul A).add
      ((integrable_finsetSum _ (fun j _ => (hi j).const_mul (w j))).const_mul D)) hχ,
    integral_add (f := fun x => A*(∑ j, |(u j).val x|))
      (g := fun x => D*(∑ j, w j*|(u j).val x|)) ((integrable_finsetSum _ (fun j _ => hi j)).const_mul A)
      ((integrable_finsetSum _ (fun j _ => (hi j).const_mul (w j))).const_mul D),
    integral_const_mul, integral_const_mul,
    integral_finsetSum _ (fun j _ => hi j),
    integral_finsetSum _ (fun j _ => (hi j).const_mul (w j))]
  simp_rw [integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ =>
      GoodSetL2Comparison.integral_abs_le_norm (u j).val) hA)
    (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (GoodSetL2Comparison.integral_abs_le_norm (u j).val) (hw j)) hD))
    (GoodSetL2Comparison.integral_abs_le_norm χ)


namespace ShortUniform

open Riesz2.DecayShort Riesz2.DecayShort.ConditionalScores Riesz2.DecayShort.PhysicalComparison

/-- See Subsection 4.4 of the paper, reused by the proof of Lemma 6.5:
all short score bounds with one prefactor for every temperature above
`βlo`. This retains the explicit constants of the physical BL estimates. -/
theorem score_bounds (s βlo : ℝ) (hs : 1 < s) (hlo : 0 < βlo) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 →
      ∀ (n : ℕ+) (m : ℕ),
      4 ≤ (n : ℕ) + m + 1 → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∃ U : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ,
        ContDiffOn ℝ ∞ U (gapAmbientDomain ((n : ℕ) + m).succPNat) ∧
        (∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) //
            y ∈ gapAmbientDomain ((n : ℕ) + m).succPNat},
          U y.val = p.val.1 * physicalAmbientGapEnergy p ((n : ℕ) + m).succPNat y) ∧
        ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)),
          let μ := ProperMarginalChart.conditionalMeasure p n m n.pos (Equiv.refl _) x
          let F := fun (i : Fin (n : ℕ)) z => p.val.1⁻¹ * fderiv ℝ U
            (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z))
              (EuclideanSpace.single (Fin.castLE (by omega) i) 1)
          let G := fun z => p.val.1⁻¹ * fderiv ℝ U
            (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z))
              (WithLp.toLp 2 (ConditionalForces.compensationVector n m))
          let H := IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat
            ((n : ℕ) + m + 1) le_rfl (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
          let S := Finset.univ.filter (fun a : Fin ((n : ℕ) + m + 1) => (n : ℕ) ≤ a.val)
          let c := (m + 1 : ℝ)⁻¹ ^ 2 * ∑ a ∈ S, ∑ b ∈ S, H a b
          (∀ i, MemLp (F i) 2 μ ∧ (∫ z, (F i z - ∫ y, F i y ∂μ) ^ 2 ∂μ) ≤
            C * (PhysicalFibres.exteriorGradientEnergy p n m n.pos x i).toReal) ∧
          MemLp G 2 μ ∧ (∫ z, (G z - ∫ y, G y ∂μ) ^ 2 ∂μ) ≤ p.val.1⁻¹ * c ∧
          ∀ D : ℝ, 0 ≤ D → x ∈ ExceptionalEvent.coefficientEvent p n m (by simp; omega) D →
            (∀ i j, |ProbabilityTheory.covariance (F i) (F j) μ| ≤
              C * D * weight p.val.2 i * weight p.val.2 j) ∧
            (∀ i, |ProbabilityTheory.covariance (F i) G μ| ≤
              C * D * (((n : ℕ) + m + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) * weight p.val.2 i) ∧
            (∫ z, (G z - ∫ y, G y ∂μ) ^ 2 ∂μ) ≤ C * D / (((n : ℕ) + m + 1 : ℕ) : ℝ) := by
  classical
  let αlo := βlo*(2*(s*(s+1)))
  let C := αlo⁻¹+βlo⁻¹+1
  have hαlo : 0 < αlo := by dsimp only [αlo]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro p hp hβ n m hN hhalf
  let α := p.val.1*(2*(p.val.2*(p.val.2+1)))
  have hα : 0 < α := by dsimp only [α]; rw [hp]; have := p.property.1; positivity
  have hαloα : αlo ≤ α := by
    dsimp only [αlo, α]
    rw [hp]
    exact mul_le_mul_of_nonneg_right hβ (by positivity)
  have hαC : α⁻¹ ≤ C := by
    apply ((inv_le_inv₀ hα hαlo).mpr hαloα).trans
    dsimp only [C]; have := inv_pos.mpr hlo; linarith
  have hβC : p.val.1⁻¹ ≤ C := by
    apply ((inv_le_inv₀ p.property.1 hlo).mpr hβ).trans
    dsimp only [C]; have := inv_pos.mpr hαlo; linarith
  have hm : 1 ≤ m := by have := n.pos; omega
  obtain ⟨U,hU,hv,hFi⟩ := physical_individual_score_variance p n m n.pos (by omega) hm
  obtain ⟨W,_,hw,hGi⟩ := physical_compensation_score_variance p n m n.pos (by omega) hm
  refine ⟨U,hU,hv,fun x => ?_⟩
  intro μ F G H S c
  let q := WithLp.toLp 2 (ConditionalForces.compensationVector n m)
  let G' := fun z => p.val.1⁻¹ * fderiv ℝ W
    (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) q
  have heq : G =ᵐ[μ] G' := internal_score_extension_ae p n m n.pos U W
    (fun y => (hv y).trans (hw y).symm) x q
  have hmean : (∫ z, G z ∂μ) = ∫ z, G' z ∂μ := integral_congr_ae heq
  have hvar : (∫ z, (G z - ∫ y, G y ∂μ) ^ 2 ∂μ) =
      ∫ z, (G' z - ∫ y, G' y ∂μ) ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [heq] with z hz
    rw [hz,hmean]
  have hG : MemLp G 2 μ := MemLp.ae_eq heq.symm (hGi x).1
  have hVG : (∫ z, (G z - ∫ y, G y ∂μ) ^ 2 ∂μ) ≤ p.val.1⁻¹ * c := by
    rw [hvar]
    exact (hGi x).2
  have hF (i) : MemLp (F i) 2 μ ∧ (∫ z, (F i z - ∫ y, F i y ∂μ) ^ 2 ∂μ) ≤
      C * (PhysicalFibres.exteriorGradientEnergy p n m n.pos x i).toReal :=
    ⟨(hFi x i).1, (hFi x i).2.trans (mul_le_mul_of_nonneg_right hαC (ENNReal.toReal_nonneg))⟩
  refine ⟨hF,hG,hVG,fun D hD hx => ?_⟩
  have hHN (a b) : 0 ≤ H a b := by
    unfold H IntervalBoundary.intervalMatrix
    apply Finset.sum_nonneg
    intro t _
    apply mul_nonneg (conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x t)
    unfold IntervalBoundary.rankOne
    split_ifs <;> norm_num
  have hbn (i : Fin (n : ℕ)) : 0 ≤ (m + 1 : ℝ)⁻¹ *
      ∑ a ∈ S, H (Fin.castLE (by omega) i) a :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => hHN _ a)
  have hcn : 0 ≤ c := mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun a _ =>
    Finset.sum_nonneg fun b _ => hHN a b)
  have hcD : c ≤ D / (((n : ℕ) + m + 1 : ℕ) : ℝ) := by
    let i : Fin (n : ℕ) := ⟨0,n.pos⟩
    have ht := hx.2.2.2.2.1 i
    exact (le_add_of_nonneg_left (hbn i)).trans ht
  have hVFD (i) : (∫ z, (F i z - ∫ y, F i y ∂μ) ^ 2 ∂μ) ≤
      C * D * (boundaryDistance i : ℝ) ^ (1 - 2 * p.val.2) := by
    apply (hF i).2.trans
    have ht := mul_le_mul_of_nonneg_left (hx.2.2.2.2.2 i) hC.le
    simpa only [boundaryDistance, mul_assoc] using ht
  have hVGD : (∫ z, (G z - ∫ y, G y ∂μ) ^ 2 ∂μ) ≤
      C * D / (((n : ℕ) + m + 1 : ℕ) : ℝ) := by
    apply hVG.trans
    calc
      _ ≤ C * c := mul_le_mul_of_nonneg_right hβC hcn
      _ ≤ _ := by simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hcD hC.le
  have : IsProbabilityMeasure μ := ProperMarginalChart.conditionalMeasure_probability p n m n.pos (Equiv.refl _) x
  have hc := internal_score_covariances p.val.2 C D (((n : ℕ) + m + 1 : ℕ) : ℝ)
    hC.le hD (by positivity) F G (fun i => (hF i).1) hG hVFD hVGD
  exact ⟨hc.1,hc.2,hVGD⟩


/-- See Subsection 4.5 of the paper, reused by the proof of Lemma 6.5:
physical residual entries with a temperature-uniform covariance prefactor.
Both the original exterior contractions and the physical score are retained. -/
theorem residual_entries (s βlo : ℝ) (hs : 1 < s) (hlo : 0 < βlo) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 →
      ∀ (n : ℕ+) (m : ℕ),
      4 ≤ (n : ℕ) + m + 1 → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (θ : PhysicalCutoff) (h : ℝ) (b : Bool) (D : ℝ), 0 ≤ D →
      ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (i j : Fin (n : ℕ)),
      let hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ) := by
        change (n : ℕ) ≤ (n : ℕ) + m + 1; omega
      let B := IntervalBoundary.boundaryMatrix ((n : ℕ) + m).succPNat n hn
        (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
      let N : ℝ := ((n : ℕ) + m + 1 : ℕ)
      let w := ConditionalScores.weight p.val.2
      |(frozenPhysicalMatrix p n m θ h b D x - frozenInternalMatrix p n m θ h b D x) i j -
        (if x ∈ ExceptionalEvent.properGoodEvent p n m hn h D then B i j else 0)| ≤
        3 * D / N + p.val.1 * C * D *
          (w i * w j + N ^ (-(1 / 2 : ℝ)) * (w i + w j) + N⁻¹) ∧
      |(frozenPhysicalMatrix p n m θ h b D x - frozenInternalMatrix p n m θ h b D x) i j| ≤
        (if x ∈ ExceptionalEvent.properGoodEvent p n m hn h D then B i j else 0) +
        3 * D / N + p.val.1 * C * D *
          (w i * w j + N ^ (-(1 / 2 : ℝ)) * (w i + w j) + N⁻¹) := by
  classical
  obtain ⟨C,hC,hscore⟩ := score_bounds s βlo hs hlo
  refine ⟨C,hC,?_⟩
  intro p hp hβ n m hN hhalf θ h b D hD x i j hn B N w
  have hN0 : 0 < N := by dsimp only [N]; positivity
  have hrest : 0 ≤ 3 * D / N + p.val.1 * C * D *
      (w i * w j + N ^ (-(1 / 2 : ℝ)) * (w i + w j) + N⁻¹) := by
    have hi := (ConditionalScores.weight_pos p.val.2 i).le
    have hj := (ConditionalScores.weight_pos p.val.2 j).le
    have hβ := p.property.1.le
    positivity
  by_cases hx : x ∈ ExceptionalEvent.properGoodEvent p n m hn h D
  swap
  · rw [(frozenMatrices_off_event p n m θ h b D x hx).1,
      (frozenMatrices_off_event p n m θ h b D x hx).2, sub_self, Matrix.zero_apply,
      abs_zero, ite_eq_right hx, zero_add]
    simpa only [sub_zero, abs_zero] using And.intro hrest hrest
  obtain ⟨U,_,hv,hsc⟩ := hscore p hp hβ n m hN hhalf
  let μ := ProperMarginalChart.conditionalMeasure p n m n.pos (Equiv.refl _) x
  let e : Fin (n : ℕ) → EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) :=
    fun k => EuclideanSpace.single (Fin.castLE hn k) (1 : ℝ)
  let q : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) :=
    WithLp.toLp 2 (ConditionalForces.compensationVector n m)
  let F := fun k z => p.val.1⁻¹ * fderiv ℝ U
    (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) (e k)
  let G := fun z => p.val.1⁻¹ * fderiv ℝ U
    (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) q
  let H := IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat ((n : ℕ) + m + 1) le_rfl
    (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
  let S := Finset.univ.filter (fun a : Fin ((n : ℕ) + m + 1) => (n : ℕ) ≤ a.val)
  let bi := fun k : Fin (n : ℕ) => (m + 1 : ℝ)⁻¹ * ∑ a ∈ S, H (Fin.castLE hn k) a
  let c := (m + 1 : ℝ)⁻¹ ^ 2 * ∑ a ∈ S, ∑ b ∈ S, H a b
  have hsc' := hsc x
  change (∀ k, MemLp (F k) 2 μ ∧ _) ∧ MemLp G 2 μ ∧ _ ∧ _ at hsc'
  obtain ⟨hF,hG,_,hb⟩ := hsc'
  obtain ⟨hFF,hFG,hGG⟩ := hb D hD hx.2
  let _ := ProperMarginalChart.conditionalMeasure_probability p n m n.pos (Equiv.refl _) x
  have hcov : |ProbabilityTheory.covariance (F i - G) (F j - G) μ| ≤
      C * D * (w i * w j + N ^ (-(1 / 2 : ℝ)) * (w i + w j) + N⁻¹) := by
    rw [ProbabilityTheory.covariance_sub_sub (hF i).1 hG (hF j).1 hG]
    have hgg : |ProbabilityTheory.covariance G G μ| ≤ C * D / N := by
      have hn : 0 ≤ ProbabilityTheory.covariance G G μ := by
        unfold ProbabilityTheory.covariance
        exact integral_nonneg fun _ => mul_self_nonneg _
      rw [abs_of_nonneg hn]
      simpa only [ProbabilityTheory.covariance, pow_two] using hGG
    have hgf : |ProbabilityTheory.covariance G (F j) μ| ≤ C * D * N ^ (-(1 / 2 : ℝ)) * w j := by
      rw [ProbabilityTheory.covariance_comm]
      exact hFG j
    have ht := (abs_add_le
      (ProbabilityTheory.covariance (F i) (F j) μ - ProbabilityTheory.covariance (F i) G μ -
        ProbabilityTheory.covariance G (F j) μ) (ProbabilityTheory.covariance G G μ)).trans
      (add_le_add ((abs_sub _ _).trans (add_le_add
        ((abs_sub _ _).trans (add_le_add (hFF i j) (hFG i))) hgf)) hgg)
    exact ht.trans_eq (by simp only [div_eq_mul_inv]; ring)
  have hHnn (a k) : 0 ≤ H a k := IntervalBoundary.intervalMatrix_nonneg
    ((n : ℕ) + m).succPNat ((n : ℕ) + m + 1) le_rfl _
    (conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x) a k
  have hbn (k) : 0 ≤ bi k := mul_nonneg (by positivity)
    (Finset.sum_nonneg fun a _ => hHnn _ a)
  have hcn : 0 ≤ c := mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun a _ =>
    Finset.sum_nonneg fun k _ => hHnn a k)
  have hbc (k) : bi k + c ≤ D / N := hx.2.2.2.2.2.1 k
  have hbi (k) : bi k ≤ D / N := (le_add_of_nonneg_right hcn).trans (hbc k)
  have hc : c ≤ D / N := (le_add_of_nonneg_left (hbn i)).trans (hbc i)
  have hQ : |-bi i - bi j + c| ≤ 3 * D / N := by
    calc
      _ ≤ |-bi i - bi j| + |c| := abs_add_le _ _
      _ ≤ |-bi i| + |bi j| + |c| := add_le_add (abs_sub _ _) le_rfl
      _ = bi i + bi j + c := by rw [abs_neg, abs_of_nonneg (hbn i),
          abs_of_nonneg (hbn j), abs_of_nonneg hcn]
      _ ≤ D / N + D / N + D / N := add_le_add (add_le_add (hbi i) (hbi j)) hc
      _ = 3 * D / N := by ring
  have he := frozen_difference_decomposition p n m θ h b D U hv x i j
  change _ = (if x ∈ ExceptionalEvent.properGoodEvent p n m hn h D then
    B i j - bi i - bi j + c - p.val.1 * ProbabilityTheory.covariance
      (fun z => p.val.1⁻¹ * fderiv ℝ U
        (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) (e i - q))
      (fun z => p.val.1⁻¹ * fderiv ℝ U
        (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) (e j - q)) μ else 0) at he
  simp only [ite_eq_left hx, map_sub, mul_sub] at he
  change _ = B i j - bi i - bi j + c -
    p.val.1 * ProbabilityTheory.covariance (F i - G) (F j - G) μ at he
  rw [he, ite_eq_left hx]
  have hBnn := IntervalBoundary.boundaryMatrix_nonneg ((n : ℕ) + m).succPNat n hn _
    (conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x) i j
  have hsmall : |(-bi i - bi j + c) -
      p.val.1 * ProbabilityTheory.covariance (F i - G) (F j - G) μ| ≤
      3 * D / N + p.val.1 * C * D *
        (w i * w j + N ^ (-(1 / 2 : ℝ)) * (w i + w j) + N⁻¹) := by
    have hp : |p.val.1 * ProbabilityTheory.covariance (F i - G) (F j - G) μ| ≤
        p.val.1 * (C * D * (w i * w j + N ^ (-(1 / 2 : ℝ)) * (w i + w j) + N⁻¹)) := by
      rw [abs_mul, abs_of_pos p.property.1]
      exact mul_le_mul_of_nonneg_left hcov p.property.1.le
    exact ((abs_sub _ _).trans (add_le_add hQ hp)).trans_eq (by ring)
  constructor
  · exact (congrArg abs (by ring :
      B i j - bi i - bi j + c - p.val.1 * ProbabilityTheory.covariance (F i - G) (F j - G) μ - B i j =
      (-bi i - bi j + c) - p.val.1 * ProbabilityTheory.covariance (F i - G) (F j - G) μ)).le.trans hsmall
  · calc
      _ = |B i j + ((-bi i - bi j + c) -
          p.val.1 * ProbabilityTheory.covariance (F i - G) (F j - G) μ)| := congrArg abs (by ring)
      _ ≤ |B i j| + |(-bi i - bi j + c) -
          p.val.1 * ProbabilityTheory.covariance (F i - G) (F j - G) μ| := abs_add_le _ _
      _ ≤ B i j + (3 * D / N + p.val.1 * C * D *
          (w i * w j + N ^ (-(1 / 2 : ℝ)) * (w i + w j) + N⁻¹)) := by
        rw [abs_of_nonneg hBnn]
        exact add_le_add le_rfl hsmall
      _ = _ := by ring


/-- See the proof of Lemma 6.5 in the paper: the short physical column
calculation with both finite sums retained and a covariance prefactor
uniform for every temperature above `βlo`. -/
theorem columns_explicit (s βlo : ℝ) (hs_s : 1 < s) (hlo : 0 < βlo)
    (θ : PhysicalCutoff) :
    ∃ Cp Cr : ℝ, 0 < Cp ∧ 0 < Cr ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → ∀ (n : ℕ+) (m : ℕ),
      4 ≤ (n : ℕ) + m + 1 → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ ε η κ : ℝ, 0 ≤ ε → 0 < η →
      let F := fun (h : ℝ) (y : EuclideanSpace ℝ (Fin (n : ℕ))) =>
        ∑ i, (θ.val (((n : ℝ) ^ h)⁻¹ * y i) +
          θ.val (((n : ℝ) ^ h)⁻¹ * (y i)⁻¹))
      let K := fun h y => p.val.1⁻¹ * (p.val.1 * F h y -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,z)).toReal))
      ∀ x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
        x ∈ shortFineEvent p n m η κ → ∀ j,
        let D := (n : ℝ) ^ (κ * η)
        let N : ℝ := ((n : ℕ) + m + 1 : ℕ)
        let w := DecayShort.ConditionalScores.weight p.val.2 (n := (n : ℕ))
        let S := ∑ i, w i
        (∑ i, |hessianMatrix (K ε) x.val i j|) ≤
          Cp * (n : ℝ) ^ (4 * η) +
            D * (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-p.val.2)) +
            3 * D * (n : ℝ) / N + p.val.1 * Cr * D *
              ((S + (n : ℝ) * N ^ (-(1 / 2 : ℝ))) * w j +
                N ^ (-(1 / 2 : ℝ)) * S + (n : ℝ) / N) := by
  obtain ⟨Cp, hCp, hpen⟩ := penalty_fine_bound θ
  obtain ⟨Cr, hCr, hres⟩ := residual_entries s βlo hs_s hlo
  refine ⟨Cp, Cr, hCp, hCr, ?_⟩
  intro p hp hβ n m hN hhalf ε η κ hε hη F K x hx j D N w S
  have hs : 1 < p.val.2 := by rw [hp]; exact hs_s
  let hn : (n : ℕ) ≤ (n : ℕ) + m + 1 := by omega
  let A := DecayShort.conditionalIntervalWeight p n m n.pos (Equiv.refl _) x
  let P := IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat n hn A
  let I := IntervalBoundary.internalMatrix ((n : ℕ) + m).succPNat n hn A
  let E := IntervalBoundary.boundaryMatrix ((n : ℕ) + m).succPNat n hn A
  have hD : 0 ≤ D := Real.rpow_nonneg (by positivity) _
  have hx' : x ∈ DecayShort.ExceptionalEvent.properGoodEvent p n m hn η D := hx
  have hdecomp := IntervalBoundary.internal_add_boundary ((n : ℕ) + m).succPNat n hn A
  have hP0 (i k) : 0 ≤ P i k := IntervalBoundary.intervalMatrix_nonneg
    ((n : ℕ) + m).succPNat n hn A
    (DecayShort.conditionalIntervalWeight_nonneg p n m n.pos (Equiv.refl _) x) i k
  have hresid (i) : |hessianMatrix (K ε) x.val i j - hessianMatrix (F ε) x.val i j - P i j| ≤
      3 * D / N + p.val.1 * Cr * D *
        (w i * w j + N ^ (-(1 / 2 : ℝ)) * (w i + w j) + N⁻¹) := by
    have hb := (hres p hp hβ n m hN hhalf θ η true D hD x i j).1
    rw [ite_eq_left hx'] at hb
    change |(DecayShort.PhysicalComparison.frozenPhysicalMatrix p n m θ η true D x -
      DecayShort.PhysicalComparison.frozenInternalMatrix p n m θ η true D x) i j - E i j| ≤ _ at hb
    have hchange := marginal_penalty_difference_internal p n m θ ε η x i j
    change hessianMatrix (K ε) x.val i j - hessianMatrix (F ε) x.val i j =
      hessianMatrix (K η) x.val i j - hessianMatrix (F η) x.val i j at hchange
    rw [hchange]
    have hPi : P i j = I i j + E i j := congrArg (fun M => M i j) hdecomp.symm
    unfold DecayShort.PhysicalComparison.frozenPhysicalMatrix
      DecayShort.PhysicalComparison.frozenInternalMatrix at hb
    simp only [ite_eq_left hx', Matrix.sub_apply, Matrix.add_apply, ite_true] at hb
    change |(hessianMatrix (K η) x.val i j - (hessianMatrix (F η) x.val i j + I i j)) - E i j| ≤ _ at hb
    convert hb using 1
    congr 1
    rw [hPi]
    ring
  have hentry (i) : |hessianMatrix (K ε) x.val i j| ≤
      |hessianMatrix (F ε) x.val i j| + P i j +
      (3 * D / N + p.val.1 * Cr * D *
        (w i * w j + N ^ (-(1 / 2 : ℝ)) * (w i + w j) + N⁻¹)) := by
    have hb := hresid i
    have ht := abs_add_le (hessianMatrix (K ε) x.val i j - hessianMatrix (F ε) x.val i j - P i j)
      (hessianMatrix (F ε) x.val i j + P i j)
    rw [show (hessianMatrix (K ε) x.val i j - hessianMatrix (F ε) x.val i j - P i j) +
      (hessianMatrix (F ε) x.val i j + P i j) = hessianMatrix (K ε) x.val i j by ring] at ht
    have hf := abs_add_le (hessianMatrix (F ε) x.val i j) (P i j)
    rw [abs_of_nonneg (hP0 i j)] at hf
    linarith
  have hFsum : (∑ i, |hessianMatrix (F ε) x.val i j|) ≤ Cp * (n : ℝ) ^ (4 * η) := by
    have hb (i) := hpen n ε η hε hη.le x.val (fun k => (hx.1.2.1 k).1) i j
    have he : (fun y => ∑ i, (θ.val (((n : ℝ) ^ ε)⁻¹ * y i) +
        θ.val (((n : ℝ) ^ ε)⁻¹ * (y i)⁻¹))) = F ε := rfl
    simp only [InterpolationMatrix.penaltyHessian, Real.rpow_neg (by positivity : (0 : ℝ) ≤ n), he] at hb
    exact (Finset.sum_le_sum fun i _ => hb i).trans_eq (by simp)
  have hPsum := (DecayShort.PhysicalComparison.complete_schur_bounds p hs n m D hD x hx.2).2 j
  apply (Finset.sum_le_sum fun i _ => hentry i).trans
  simp only [Finset.sum_add_distrib]
  have he : (∑ i : Fin (n : ℕ), (3 * D / N + p.val.1 * Cr * D *
        (w i * w j + N ^ (-(1 / 2 : ℝ)) * (w i + w j) + N⁻¹))) =
      3 * D * (n : ℝ) / N + p.val.1 * Cr * D *
        ((S + (n : ℝ) * N ^ (-(1 / 2 : ℝ))) * w j + N ^ (-(1 / 2 : ℝ)) * S + (n : ℝ) / N) := by
    simp only [S, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← Finset.mul_sum, ← Finset.sum_mul, div_eq_mul_inv]
    ring
  simp only [Finset.sum_add_distrib] at he
  rw [he]
  linarith


end ShortUniform


/-- See the proof of Lemma 6.5 in the paper: the short score-weight
sum is bounded by a constant times `√n` for every `s>1`. A subcritical
power strictly above `1/2` avoids the unnecessary logarithmic loss. -/
theorem short_score_weight_sum (s : ℝ) (hs : 1 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ+,
      (∑ i : Fin (n : ℕ), DecayShort.ConditionalScores.weight s i) ≤ C*(n : ℝ)^(1/2 : ℝ) := by
  let q := min (s-1/2) (3/4)
  have hq0 : 0 < q := lt_min (by linarith) (by norm_num)
  have hq1 : q < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hqhalf : 1/2 ≤ q := le_min (by linarith) (by norm_num)
  let C := 2/(1-q)
  have hC : 0 < C := div_pos (by norm_num) (by linarith)
  refine ⟨C, hC, fun n => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hpoint (i : Fin (n : ℕ)) : DecayShort.ConditionalScores.weight s i ≤
      (min (i.val+1) ((n : ℕ)-i.val) : ℕ)^(-q) := by
    unfold DecayShort.ConditionalScores.weight DecayShort.ConditionalScores.boundaryDistance
    apply Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast DecayShort.ConditionalScores.boundaryDistance_pos i)
    linarith [min_le_left (s-1/2) (3/4 : ℝ)]
  exact (Finset.sum_le_sum (fun i _ => hpoint i)).trans
    ((LocalizedBoundary.boundary_weight_sum_internal n q hq0 hq1).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)) hC.le))

/-- See the proof of Lemma 6.5 in the paper: simplified short physical
columns. The penalty exponent is `ε`. The good tolerance is `η`. Both
prefactors in the explicit column calculation are uniform on
the prescribed compact temperature interval. -/
theorem short_fine_hessian_columns_uniform (s : ℝ) (hs : 1 < s)
    (θ : PhysicalCutoff) (κ : ℝ) (hκ : 1 ≤ κ) :
    ∃ k : ℝ, 0 < k ∧ ∀ η βlo βhi : ℝ, 0 < η → 0 < βlo → βlo ≤ βhi →
      ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (n : ℕ+) (m : ℕ),
      4 ≤ (n : ℕ)+m+1 → 2*(n : ℕ) ≤ (n : ℕ)+m+1 →
      ∀ ε : ℝ, 0 ≤ ε →
      let K := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) => p.val.1⁻¹ *
        (p.val.1 * (∑ i, (θ.val (((n : ℝ)^ε)⁻¹*y i) +
          θ.val (((n : ℝ)^ε)⁻¹*(y i)⁻¹))) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,z)).toReal))
      ∀ x : AffineSimplex.chartDomain n ((n+m : ℕ)+1),
        x ∈ shortFineEvent p n m η κ → ∀ j : Fin (n : ℕ),
        let N : ℝ := (n : ℝ)+m+1
        let w := DecayShort.ConditionalScores.weight s (n := (n : ℕ))
        let S := ∑ i, w i
        (∑ i, |hessianMatrix K x.val i j|) ≤ C*(n : ℝ)^((k)*η)*
          (1+(S+(n : ℝ)*N^(-(1/2 : ℝ)))*w j) := by
  refine ⟨κ+4, by linarith, fun η βlo βhi hη hlo hle => ?_⟩
  obtain ⟨Cp, Cr, hCp, hCr, hcol⟩ := ShortUniform.columns_explicit s βlo hs hlo θ
  obtain ⟨A, hA, hsum⟩ := short_score_weight_sum s hs
  let E := 2*∑' k : ℕ, (1+(k : ℝ))^(-s)
  have hE : 0 ≤ E := mul_nonneg (by norm_num) (tsum_nonneg fun k => by positivity)
  let C := Cp+E+3+βhi*Cr*(A+1)+βhi*Cr
  have hhi : 0 < βhi := hlo.trans_le hle
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro p hp hβlo hβhi n m hN hhalf ε hε K x hx j N w S
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hN0 : 0 < N := by dsimp only [N]; positivity
  have hnN : (n : ℝ) ≤ N := by dsimp only [N]; have := Nat.cast_nonneg m (α := ℝ); linarith
  have hnN' : (n : ℝ)/N ≤ 1 := (div_le_one hN0).mpr hnN
  have hw (i) : 0 ≤ w i := (DecayShort.ConditionalScores.weight_pos s i).le
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => hw i
  have hNS : N^(-(1/2 : ℝ))*S ≤ A := by
    have hh := Real.rpow_le_rpow_of_nonpos hn0 hnN (by norm_num : -(1/2 : ℝ) ≤ 0)
    have he : (n : ℝ)^(1/2 : ℝ)*(n : ℝ)^(-(1/2 : ℝ)) = 1 := by
      rw [← Real.rpow_add hn0]; norm_num
    calc
      _ ≤ (n : ℝ)^(-(1/2 : ℝ))*(A*(n : ℝ)^(1/2 : ℝ)) :=
        mul_le_mul hh (hsum n) hS (by positivity)
      _ = A*((n : ℝ)^(1/2 : ℝ)*(n : ℝ)^(-(1/2 : ℝ))) := by ring
      _ = A := by rw [he, mul_one]
  let R := (n : ℝ)^((κ+4)*η)
  let D := (n : ℝ)^(κ*η)
  let X := (S+(n : ℝ)*N^(-(1/2 : ℝ)))*w j
  have hX : 0 ≤ X := mul_nonneg (add_nonneg hS (by positivity)) (hw j)
  have hDR : D ≤ R := Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith)
  have hpR : (n : ℝ)^(4*η) ≤ R := Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith)
  have hraw := hcol p hp hβlo n m hN hhalf ε η κ hε hη x hx j
  change (∑ i, |hessianMatrix K x.val i j|) ≤ _ at hraw
  simp only [hp, Nat.cast_add, Nat.cast_one] at hraw
  change _ ≤ Cp*(n : ℝ)^(4*η)+D*E+3*D*(n : ℝ)/N+
    p.val.1*Cr*D*(X+N^(-(1/2 : ℝ))*S+(n : ℝ)/N) at hraw
  have hrest : X+N^(-(1/2 : ℝ))*S+(n : ℝ)/N ≤ X+A+1 := by linarith
  have h₁ := mul_le_mul_of_nonneg_left hpR hCp.le
  have h₂ := mul_le_mul_of_nonneg_right hDR hE
  have h₃ : 3*D*(n : ℝ)/N ≤ 3*R := by
    calc
      _ = 3*D*((n : ℝ)/N) := by ring
      _ ≤ 3*D := mul_le_of_le_one_right (by dsimp only [D]; positivity) hnN'
      _ ≤ _ := by linarith
  have h₄ := mul_le_mul (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hβhi hCr.le) (by dsimp only [D]; positivity : 0 ≤ D))
    hrest (by positivity) (by positivity : 0 ≤ βhi*Cr*D)
  have h₅ := mul_le_mul_of_nonneg_right hDR
    (show 0 ≤ βhi*Cr*(X+A+1) by positivity)
  change _ ≤ C*R*(1+X)
  dsimp only [C]
  nlinarith only [hraw, h₁, h₂, h₃, h₄, h₅,
    mul_nonneg (mul_nonneg hhi.le hCr.le) (show 0 ≤ R by dsimp only [R]; positivity),
    mul_nonneg (show 0 ≤ Cp+E+3+βhi*Cr*(A+1) by positivity)
      (show 0 ≤ R*X by dsimp only [R]; positivity)]


/-- Internal rate bookkeeping for equation (6.24).
The exceptional comparison factor `n^z` is kept until multiplication by
the good-column loss `n^a`. In particular it is never absorbed into a
conditional error whose envelope exponent has already been fixed. -/
theorem normal_sum_rates_internal (n : ℕ+) (τ a b z C U V T F B e S W : ℝ)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hz : a+z ≤ 0)
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hF : 0 ≤ F) (hB : 0 ≤ B) (_he : 0 ≤ e)
    (hS : S ≤ U*(n : ℝ)^b*F + T*(n : ℝ)^z*B*Real.sqrt e)
    (hW : W ≤ V*(n : ℝ)^(b-τ/2)*F + T*(n : ℝ)^z*B*Real.sqrt e) :
    (n : ℝ)⁻¹ * (C*(n : ℝ)^(a+1-τ)*S +
      C*(n : ℝ)^(a+1-τ/2)*W + F) ≤
        (C*(U+V)+1)*(n : ℝ)^(a+b-τ)*F + 2*C*T*B*Real.sqrt e := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hp (x y : ℝ) : (n : ℝ)^x*(n : ℝ)^y = (n : ℝ)^(x+y) :=
    (Real.rpow_add hn0 x y).symm
  have h₁ : (n : ℝ)⁻¹*(n : ℝ)^(a+1-τ)*(n : ℝ)^b = (n : ℝ)^(a+b-τ) := by
    rw [← Real.rpow_neg_one (n : ℝ), hp, hp]; congr 1; ring
  have h₂ : (n : ℝ)⁻¹*(n : ℝ)^(a+1-τ/2)*(n : ℝ)^(b-τ/2) =
      (n : ℝ)^(a+b-τ) := by
    rw [← Real.rpow_neg_one (n : ℝ), hp, hp]; congr 1; ring
  have h₃ : (n : ℝ)⁻¹*(n : ℝ)^(a+1-τ)*(n : ℝ)^z ≤ 1 := by
    rw [← Real.rpow_neg_one (n : ℝ), hp, hp]
    exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  have h₄ : (n : ℝ)⁻¹*(n : ℝ)^(a+1-τ/2)*(n : ℝ)^z ≤ 1 := by
    rw [← Real.rpow_neg_one (n : ℝ), hp, hp]
    exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  have h₅ : (n : ℝ)⁻¹ ≤ (n : ℝ)^(a+b-τ) := by
    rw [← Real.rpow_neg_one (n : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hsum := mul_le_mul_of_nonneg_left
    (add_le_add_right (add_le_add
      (mul_le_mul_of_nonneg_left hS (show 0 ≤ C*(n : ℝ)^(a+1-τ) by positivity))
      (mul_le_mul_of_nonneg_left hW (show 0 ≤ C*(n : ℝ)^(a+1-τ/2) by positivity))) F)
    (show 0 ≤ (n : ℝ)⁻¹ by positivity)
  have hmain : (n : ℝ)⁻¹ *
      (C*(n : ℝ)^(a+1-τ)*(U*(n : ℝ)^b*F+T*(n : ℝ)^z*B*Real.sqrt e)+
       C*(n : ℝ)^(a+1-τ/2)*(V*(n : ℝ)^(b-τ/2)*F+T*(n : ℝ)^z*B*Real.sqrt e)+F) =
      C*(U+V)*(n : ℝ)^(a+b-τ)*F +
        C*T*B*Real.sqrt e*((n : ℝ)⁻¹*(n : ℝ)^(a+1-τ)*(n : ℝ)^z +
          (n : ℝ)⁻¹*(n : ℝ)^(a+1-τ/2)*(n : ℝ)^z)+(n : ℝ)⁻¹*F := by
    linear_combination C*U*F*h₁ + C*V*F*h₂
  simp only [add_comm F] at hsum
  rw [hmain] at hsum
  have herr := mul_le_mul_of_nonneg_left (add_le_add h₃ h₄)
    (show 0 ≤ C*T*B*Real.sqrt e by positivity)
  have hsource := mul_le_mul_of_nonneg_right h₅ hF
  nlinarith only [hsum, herr, hsource]

/-- Internal assembly of equation (6.24), valid for
both regimes with `τ=min(s,1)`. The good-event columns and the two fibre
sums are separate interfaces, and the exceptional comparison exponent is
retained explicitly. -/
theorem multiplier_from_sums_internal {X : Type*} [MeasurableSpace X]
    {ρ : Measure X} [IsProbabilityMeasure ρ] (n : ℕ+) (Q : ScalarFormData ρ)
    (M : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ρ) (u : Fin (n : ℕ) → Q.1)
    (G : Set X) (hG : MeasurableSet G) (w : Fin (n : ℕ) → ℝ)
    (τ a b z C U V T K B e : ℝ)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hz : a+z ≤ 0)
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hB : 0 ≤ B) (he : 0 ≤ e) (hw : ∀ j, 0 ≤ w j)
    (hpair : ∀ i j, Integrable (fun x => M x i j*(u j).val x) ρ)
    (hcol : ∀ᵐ x ∂ρ.restrict G, ∀ j,
      (∑ i, |M x i j|) ≤ C*(n : ℝ)^(a+1-τ)+C*(n : ℝ)^(a+1-τ/2)*w j)
    (hsum : (∑ j, ‖(u j).val‖) ≤ U*(n : ℝ)^b*‖χ‖+T*(n : ℝ)^z*B*Real.sqrt e)
    (hweighted : (∑ j, w j*‖(u j).val‖) ≤
      V*(n : ℝ)^(b-τ/2)*‖χ‖+T*(n : ℝ)^z*B*Real.sqrt e)
    (hbad : |∫ x in Gᶜ, gapMultiplierField n Q M
      (fun i => if i = i₀ then χ else 0) u x ∂ρ| ≤ K*B*e) :
    |∫ x, gapMultiplierField n Q M (fun i => if i = i₀ then χ else 0) u x ∂ρ| ≤
      (C*(U+V)+1)*(n : ℝ)^(a+b-τ)*‖χ‖ + 2*C*T*B*Real.sqrt e + K*B*e := by
  obtain ⟨hΛ, hgood⟩ := good_multiplier_integral_internal n Q M i₀ χ u G hG w
    (C*(n : ℝ)^(a+1-τ)) (C*(n : ℝ)^(a+1-τ/2)) (by positivity) (by positivity)
    hw hpair hcol
  have hrate := normal_sum_rates_internal n τ a b z C U V T ‖χ‖ B e
    (∑ j, ‖(u j).val‖) (∑ j, w j*‖(u j).val‖)
    hτ hτ1 ha hb hz hC hT (norm_nonneg χ) hB he hsum hweighted
  rw [← integral_add_compl hG hΛ]
  exact (abs_add_le _ _).trans (add_le_add (hgood.trans hrate) hbad)


/-- Internal unabsorbed version of equation (6.23).
The squared comparison loss is `n^(B₀-C₀)`. The two sums retain the
common factor `n^((1+B₀-C₀)/2)` for the subsequent column calculation. -/
theorem fibre_sums_retaining_loss_internal {H : Type*} [NormedAddCommGroup H]
    (n : ℕ+) (w : Fin (n : ℕ) → ℝ) (hw : ∀ j, 0 ≤ w j)
    (q W A D E T b B₀ C₀ F B e : ℝ)
    (hq : 0 ≤ q) (hW : 0 ≤ W) (hE : 0 ≤ E) (hT : 0 ≤ T)
    (hF : 0 ≤ F) (hB : 0 ≤ B) (he : 0 ≤ e)
    (ψ v : Fin (n : ℕ) → H)
    (hweights : (∑ j, w j^2) ≤ W*(n : ℝ)^(1-2*q))
    (hweighted : (∑ j, w j*‖v j‖) ≤ A*(n : ℝ)^(b-q)*F)
    (hsum : (∑ j, ‖v j‖) ≤ D*(n : ℝ)^b*F)
    (herror : ‖WithLp.toLp 2 (fun j => ψ j-v j)‖^2 ≤
      E*(n : ℝ)^(2*b-1)*F^2+T*(n : ℝ)^(B₀-C₀)*B^2*e) :
    (∑ j, w j*‖ψ j‖) ≤ (A+Real.sqrt W*Real.sqrt E)*(n : ℝ)^(b-q)*F+
      ((1+Real.sqrt W)*Real.sqrt T)*(n : ℝ)^((1+B₀-C₀)/2)*B*Real.sqrt e ∧
    (∑ j, ‖ψ j‖) ≤ (D+Real.sqrt E)*(n : ℝ)^b*F+
      ((1+Real.sqrt W)*Real.sqrt T)*(n : ℝ)^((1+B₀-C₀)/2)*B*Real.sqrt e := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  let P := (C₀-B₀)/2
  have herr := conditional_comparison_sqrt_internal n b P E T F B e
    ‖WithLp.toLp 2 (fun j => ψ j-v j)‖ hE hT hF hB he (norm_nonneg _)
    (by simpa only [show -2*P = B₀-C₀ by dsimp only [P]; ring] using herror)
  have herr' : ‖WithLp.toLp 2 (fun j => ψ j-v j)‖ ≤
      (Real.sqrt E*(n : ℝ)^b)*(n : ℝ)^(-(1 : ℝ)/2)*F+
        (n : ℝ)^(-P)*(Real.sqrt T*B)*Real.sqrt e := by
    convert herr using 1
    rw [show b-1/2 = b+(-(1 : ℝ)/2) by ring, Real.rpow_add hn0]
    ring
  have hweighted' : (∑ j, w j*‖v j‖) ≤ (A*(n : ℝ)^b)*(n : ℝ)^(-q)*F := by
    convert hweighted using 1
    rw [show b-q = b+(-q) by ring, Real.rpow_add hn0]
    ring
  obtain ⟨hx, hy⟩ := conditional_sums_internal n w hw q W (A*(n : ℝ)^b)
    (D*(n : ℝ)^b) (Real.sqrt E*(n : ℝ)^b) F (Real.sqrt T*B) e P hW
    ψ v hweights hweighted' hsum herr'
  have heq : 1/2-P = (1+B₀-C₀)/2 := by dsimp only [P]; ring
  have hp : (n : ℝ)^(1/2-q-P) ≤ (n : ℝ)^((1+B₀-C₀)/2) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by rw [← heq]; linarith)
  have hfactor : Real.sqrt W ≤ 1+Real.sqrt W := by linarith
  constructor
  · apply hx.trans
    have hgood : (A*(n : ℝ)^b+Real.sqrt W*(Real.sqrt E*(n : ℝ)^b))*
        (n : ℝ)^(-q)*F = (A+Real.sqrt W*Real.sqrt E)*(n : ℝ)^(b-q)*F := by
      rw [Real.rpow_sub hn0, Real.rpow_neg hn0.le, div_eq_mul_inv]
      ring
    rw [hgood]
    apply add_le_add le_rfl
    have hh := mul_le_mul hfactor hp (by positivity) (by positivity)
    have hh' := mul_le_mul_of_nonneg_right hh
      (show 0 ≤ Real.sqrt T*B*Real.sqrt e by positivity)
    nlinarith only [hh']
  · apply hy.trans
    rw [heq]
    have hh := mul_le_mul_of_nonneg_right
      (show (1 : ℝ) ≤ 1+Real.sqrt W by linarith [Real.sqrt_nonneg W])
      (show 0 ≤ (n : ℝ)^((1+B₀-C₀)/2)*(Real.sqrt T*B)*Real.sqrt e by positivity)
    nlinarith only [hh]

/-- Internal assembly of equation (6.24) directly from
a squared physical comparison and auxiliary sums. One envelope exponent
absorbs the square-root and good-column losses. No absorbed fibre error
is multiplied by a growing column coefficient. -/
theorem multiplier_from_square_internal {X : Type*} [MeasurableSpace X]
    {ρ : Measure X} [IsProbabilityMeasure ρ] (n : ℕ+) (Q : ScalarFormData ρ)
    (M : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ρ) (u : Fin (n : ℕ) → Q.1)
    (v : Fin (n : ℕ) → Lp ℝ 2 ρ) (G : Set X) (hG : MeasurableSet G)
    (w : Fin (n : ℕ) → ℝ) (hw : ∀ j, 0 ≤ w j)
    (τ a b C W A D E T B₀ C₀ K B e : ℝ)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hC₀ : 1+B₀+2*a ≤ C₀) (hC : 0 ≤ C) (hW : 0 ≤ W)
    (hE : 0 ≤ E) (hT : 0 ≤ T) (hB : 0 ≤ B) (he : 0 ≤ e)
    (hpair : ∀ i j, Integrable (fun x => M x i j*(u j).val x) ρ)
    (hcol : ∀ᵐ x ∂ρ.restrict G, ∀ j,
      (∑ i, |M x i j|) ≤ C*(n : ℝ)^(a+1-τ)+C*(n : ℝ)^(a+1-τ/2)*w j)
    (hweights : (∑ j, w j^2) ≤ W*(n : ℝ)^(1-τ))
    (hweighted : (∑ j, w j*‖v j‖) ≤ A*(n : ℝ)^(b-τ/2)*‖χ‖)
    (hsum : (∑ j, ‖v j‖) ≤ D*(n : ℝ)^b*‖χ‖)
    (herror : ‖WithLp.toLp 2 (fun j => (u j).val-v j)‖^2 ≤
      E*(n : ℝ)^(2*b-1)*‖χ‖^2+T*(n : ℝ)^(B₀-C₀)*B^2*e)
    (hbad : |∫ x in Gᶜ, gapMultiplierField n Q M
      (fun i => if i = i₀ then χ else 0) u x ∂ρ| ≤ K*B*e) :
    |∫ x, gapMultiplierField n Q M (fun i => if i = i₀ then χ else 0) u x ∂ρ| ≤
      (C*(D+Real.sqrt E+A+Real.sqrt W*Real.sqrt E)+1)*(n : ℝ)^(a+b-τ)*‖χ‖+
        2*C*((1+Real.sqrt W)*Real.sqrt T)*B*Real.sqrt e+K*B*e := by
  obtain ⟨hwgt, hsum'⟩ := fibre_sums_retaining_loss_internal n w hw (τ/2) W A D E T b
    B₀ C₀ ‖χ‖ B e (by positivity) hW hE hT (norm_nonneg χ) hB he
    (fun j => (u j).val) v (by simpa only [show (1 : ℝ)-2*(τ/2) = 1-τ by ring] using hweights) hweighted hsum herror
  have hresult := multiplier_from_sums_internal n Q M i₀ χ u G hG w τ a b ((1+B₀-C₀)/2)
    C (D+Real.sqrt E) (A+Real.sqrt W*Real.sqrt E) ((1+Real.sqrt W)*Real.sqrt T)
    K B e hτ hτ1 ha hb (by linarith) hC (by positivity) hB he hw hpair hcol hsum' hwgt hbad
  simpa only [add_assoc] using hresult


/-- See the proof of Lemma 6.5 in the paper: short physical columns in
the common `τ=1` profile used by the multiplier assembly. This includes
`β` and the boundary weight. Its prefactor is uniform on
the prescribed compact temperature interval. -/
theorem short_fine_physical_columns (s : ℝ) (hs : 1 < s)
    (θ : PhysicalCutoff) (κ : ℝ) (hκ : 1 ≤ κ) :
    ∃ k : ℝ, 0 < k ∧ ∀ η βlo βhi : ℝ, 0 < η → 0 < βlo → βlo ≤ βhi →
      ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (n : ℕ+) (m : ℕ),
      4 ≤ (n : ℕ)+m+1 → 2*(n : ℕ) ≤ (n : ℕ)+m+1 →
      ∀ ε : ℝ, 0 ≤ ε →
      let K := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) => p.val.1⁻¹ *
        (p.val.1 * (∑ i, (θ.val (((n : ℝ)^ε)⁻¹*y i) +
          θ.val (((n : ℝ)^ε)⁻¹*(y i)⁻¹))) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,z)).toReal))
      ∀ x : AffineSimplex.chartDomain n ((n+m : ℕ)+1),
        x ∈ shortFineEvent p n m η κ → ∀ j : Fin (n : ℕ),
        (∑ i, |p.val.1*hessianMatrix K x.val i j|) ≤ C*(n : ℝ)^(k*η)*
          (1+(n : ℝ)^(1/2 : ℝ)*InteractionDifferential.boundaryWeight s n j) := by
  obtain ⟨k, hk, hcol⟩ := short_fine_hessian_columns_uniform s hs θ κ hκ
  obtain ⟨A, hA, hsum⟩ := short_score_weight_sum s hs
  refine ⟨k, hk, fun η βlo βhi hη hlo hle => ?_⟩
  obtain ⟨C, hC, hc⟩ := hcol η βlo βhi hη hlo hle
  have hhi : 0 < βhi := hlo.trans_le hle
  refine ⟨βhi*C*(A+2), by positivity, ?_⟩
  intro p hp hβlo hβhi n m hN hhalf ε hε K x hx j
  let N : ℝ := (n : ℝ)+m+1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hnN : (n : ℝ) ≤ N := by dsimp only [N]; have := Nat.cast_nonneg m (α := ℝ); linarith
  have hneg := Real.rpow_le_rpow_of_nonpos hn0 hnN (by norm_num : -(1/2 : ℝ) ≤ 0)
  have hNscale : (n : ℝ)*N^(-(1/2 : ℝ)) ≤ (n : ℝ)^(1/2 : ℝ) := by
    apply (mul_le_mul_of_nonneg_left hneg hn0.le).trans_eq
    simpa only [show (1 : ℝ)+(-(1/2 : ℝ)) = 1/2 by norm_num, Real.rpow_one] using
      (Real.rpow_add hn0 1 (-(1/2 : ℝ))).symm
  have hw : DecayShort.ConditionalScores.weight s j =
      InteractionDifferential.boundaryWeight s n j := by
    rw [InteractionDifferential.boundaryWeight_short hs]
    unfold DecayShort.ConditionalScores.weight DecayShort.ConditionalScores.boundaryDistance
    congr 1
    ring
  have hw0 : 0 ≤ InteractionDifferential.boundaryWeight s n j :=
    (InteractionDifferential.boundaryWeight_pos _ _ _).le
  have hprofile := mul_le_mul_of_nonneg_right (add_le_add (hsum n) hNscale) hw0
  have hraw := hc p hp hβlo hβhi n m hN hhalf ε hε x hx j
  change (∑ i, |hessianMatrix K x.val i j|) ≤ _ at hraw
  have hscaled := mul_le_mul_of_nonneg_left hraw p.property.1.le
  have hb : (∑ i, |p.val.1*hessianMatrix K x.val i j|) =
      p.val.1*(∑ i, |hessianMatrix K x.val i j|) := by
    simp only [abs_mul, abs_of_pos p.property.1, Finset.mul_sum]
  rw [hb]
  apply hscaled.trans
  have hβ := mul_le_mul_of_nonneg_right hβhi
    (show 0 ≤ C*(n : ℝ)^(k*η)*(1+((∑ i : Fin (n : ℕ), DecayShort.ConditionalScores.weight s i)+
      (n : ℝ)*N^(-(1/2 : ℝ)))*DecayShort.ConditionalScores.weight s j) by
        have hw' := (DecayShort.ConditionalScores.weight_pos s j).le
        have hsum' : 0 ≤ ∑ i : Fin (n : ℕ), DecayShort.ConditionalScores.weight s i :=
          Finset.sum_nonneg fun i _ => (DecayShort.ConditionalScores.weight_pos s i).le
        positivity)
  change p.val.1*(C*(n : ℝ)^(k*η)*(1+((∑ i : Fin (n : ℕ), DecayShort.ConditionalScores.weight s i)+
    (n : ℝ)*N^(-(1/2 : ℝ)))*DecayShort.ConditionalScores.weight s j)) ≤ _
  apply hβ.trans
  rw [hw]
  have ht := mul_le_mul_of_nonneg_left hprofile
    (show 0 ≤ βhi*C*(n : ℝ)^(k*η) by positivity)
  have hextra := mul_nonneg (show 0 ≤ βhi*C*(n : ℝ)^(k*η) by positivity)
    (show 0 ≤ (A+1)+(n : ℝ)^(1/2 : ℝ)*InteractionDifferential.boundaryWeight s n j by positivity)
  nlinarith only [ht, hextra]

end Riesz2.LengthAveragingFibres
