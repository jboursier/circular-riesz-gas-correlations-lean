/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.FullCycleComparison
public import Riesz2.DecayLong.OptimalLocalizationPart5
public import Riesz2.ToMathlib.StretchedCutoffRates

/-!
# Full-cycle physical decay

Full-cycle decay estimates in the proof of Theorem 1. The localization
induction on arbitrary measurable carriers is specialized to the intrinsic
gap law, preserving its scalar form and full matrix-energy domain.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology ContDiff Classical

namespace Riesz2.FullCycleComparison

set_option backward.isDefEq.respectTransparency false

/-- Carrier-independent version of the localization bootstrap,
supporting the proof of Theorem 1. This is the
same finite saturation used in Proposition 5.15, before its Euclidean
specialization. In particular it applies to the literal intrinsic scalar form. -/
theorem localization_profile_internal (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    OptimalLocalizationPart2.UniformProfile s (2-s.val) ((3-s.val)/2) true := by
  have hfinal : ∀ b, OptimalLocalizationPart2.UniformProfile s
      (2-s.val) ((3-s.val)/2) b := by
    apply OptimalLocalizationBootstrap.finite_saturation_internal s
      (fun A G => ∀ b, OptimalLocalizationPart2.UniformProfile s A G b)
      (OptimalLocalizationPart2.base_uniform_internal hzeta s)
    intro A G hA hA' hG hG' hGA h b
    have hc := OptimalLocalizationPart5.loc_constrained_step hzeta s A G
      hA hA' hG hG' hGA h
    cases b
    · exact OptimalLocalizationPart2.unconstrained_step_uniform_internal
        hzeta s A G hA hG (h false) hc
    · exact hc
  exact hfinal true

/-- Pull back every clause of the matrix bounds, including the
interval coefficients. Supporting the proof of Theorem 1. -/
theorem matrix_bounds_pullback_internal {α α' : Type*}
    [MeasurableSpace α] [MeasurableSpace α'] (ν : Measure α)
    (f : α → α') (hf : Measurable f)
    (s : Riesz1.RieszExponent) (n m : ℕ+) (hm : 2 ≤ (m : ℕ))
    (K : ℕ) (C κ γ ε : ℝ) (M : α' → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hM : PeriodizedMatrixBounds (ν := ν.map f) s n m hm K C κ γ ε M) :
    PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε (M ∘ f) := by
  refine ⟨fun i j => (hM.1 i j).comp hf,
    (show MeasurePreserving f ν (ν.map f) from ⟨hf, rfl⟩).quasiMeasurePreserving.ae hM.2.1, ?_⟩
  obtain ⟨a, ha, hb⟩ := hM.2.2
  exact ⟨fun i r => a i r ∘ f, fun i r => (ha i r).comp hf,
    (show MeasurePreserving f ν (ν.map f) from ⟨hf, rfl⟩).quasiMeasurePreserving.ae hb⟩

/-- A sublinear cutoff is available eventually, supporting the proof of Theorem 1. The threshold precedes volume. -/
theorem eventual_cutoff_internal (M₀ : ℕ+) {η : ℝ}
    (hη : 0 < η) (hsmall : (M₀ : ℝ)*η < 1) :
    ∃ L : ℝ, 2 ≤ L ∧ ∀ N : ℕ+, L ≤ (N : ℝ) →
      1 ≤ ⌊(N : ℝ)^η⌋₊^(M₀ : ℕ) ∧
      4*(⌊(N : ℝ)^η⌋₊^(M₀ : ℕ)) ≤ (N : ℕ) := by
  have ht : Tendsto (fun x : ℝ => x ^ (1-(M₀ : ℝ)*η)) atTop atTop :=
    tendsto_rpow_atTop (by linarith)
  obtain ⟨L, hL⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (4 : ℝ)))
  refine ⟨max L 2, le_max_right _ _, fun N hN => ?_⟩
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hn0 : (0 : ℝ) < N := by positivity
  have hp : 1 ≤ ⌊(N : ℝ)^η⌋₊ := (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hn1 hη.le)
  refine ⟨one_le_pow₀ hp, ?_⟩
  have hf : (⌊(N : ℝ)^η⌋₊ : ℝ) ≤ (N : ℝ)^η := Nat.floor_le (by positivity)
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (⌊(N : ℝ)^η⌋₊ : ℝ)) hf (M₀ : ℕ)
  have he : ((N : ℝ)^η)^(M₀ : ℕ) = (N : ℝ)^((M₀ : ℝ)*η) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le, mul_comm]
  rw [he] at hpow
  have hfour := hL (N : ℝ) ((le_max_left L 2).trans hN)
  have hmul := mul_le_mul_of_nonneg_right hfour
    (Real.rpow_nonneg hn0.le ((M₀ : ℝ)*η))
  rw [← Real.rpow_add hn0, sub_add_cancel, Real.rpow_one] at hmul
  have hh := (mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 4)).trans hmul
  exact_mod_cast hh

/-- Localization of the actual full-cycle auxiliary matrix on its intrinsic
base, supporting the proof of Theorem 1.
All structural exponents precede the cutoff, loss, and temperatures. -/
theorem auxiliary_localization_internal (hzeta : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (M₀ : ℕ+) :
    ∃ η₀ κ : ℝ, 0 < η₀ ∧ 0 < κ ∧
    ∀ θ : PhysicalCutoff, ∀ η : ℝ, 0 < η → η ≤ η₀ →
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)),
    let K := ⌊(N : ℝ)^η⌋₊^(M₀ : ℕ)
    1 ≤ K → 4*K ≤ (N : ℕ) →
    let ν := fullIntrinsicTiltedGapLaw (ofLong β s) N θ η false
    ∀ Q : ScalarFormData ν, IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
    ∀ (i₀ : Fin (N : ℕ)) (χ : Lp ℝ 2 ν),
    ∃ v : Fin (N : ℕ) → Q.1,
      WeightedWeakSolution Q (fun z => β.val • PhysicalCore.fullMatrix s N hN K θ η 1
        (WithLp.toLp 2 (fun i => 1+z.val i))) (zeroSumComponents _)
        (fun i => if i=i₀ then χ else 0) v ∧
      ∀ j, ‖(v j).val‖ ≤ C*(N : ℝ)^(κ*η)*
        (1+(Riesz1.cyclicIndexDistance N j i₀ : ℝ))^(-(2-s.val))*‖χ‖ := by
  obtain ⟨η₀, κstar, γstar, hη₀, hκstar, hγstar, hcore⟩ :=
    PhysicalCore.full_matrix_bounds s (M₀ : ℕ) 1
  obtain ⟨κ, hκ, hloc⟩ := localization_profile_internal hzeta s κstar γstar M₀ hκstar hγstar
  refine ⟨η₀, κ, hη₀, hκ, fun θ η hη hηmax βlo βhi hlo hle => ?_⟩
  obtain ⟨Cstar, hCstar, hcore⟩ := hcore θ ⟨1, zero_lt_one⟩
  obtain ⟨C, hC, hloc⟩ := hloc η hη Cstar hCstar βlo hlo βhi hle
  refine ⟨C, hC, ?_⟩
  intro β hβ N hN K hK hKN ν Q hQ hQc i₀ χ
  let : IsProbabilityMeasure ν := DefinitionSanity.full_intrinsic_tilted_probability _ _ _ _ _
  let Y := fun z : gapTangentSpace N => WithLp.toLp 2 (fun i => 1+z.val i)
  have hY : Measurable Y := (PhysicalCollision.intrinsic_chart_contDiff N).continuous.measurable
  have hKN' : K ≤ (N : ℕ)/4 := by omega
  have hM := matrix_bounds_pullback_internal ν Y hY s N N hN K Cstar κstar γstar η
    (PhysicalCore.fullMatrix s N hN K θ η 1)
    (hcore η hη.le hηmax N hN hKN' (ν.map Y))
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hs : (1 : ℝ) ≤ 1/2+1/s.val := by
    have hh : (1 : ℝ) < 1/s.val := (lt_div_iff₀ s.property.1).mpr (by simpa using s.property.2)
    linarith
  have hsize : (N : ℝ) ≤ 2*(N : ℝ)^(1/2+1/s.val) := by
    have hh := Real.rpow_le_rpow_of_exponent_le hn1 hs
    rw [Real.rpow_one] at hh
    linarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ N) (1/2+1/s.val)]
  obtain ⟨v, ⟨hv, he⟩, _⟩ := hloc η le_rfl ν Q hQ hQc N N hN hN le_rfl hsize
    hK hKN (PhysicalCore.fullMatrix s N hN K θ η 1 ∘ Y) hM β.val hβ.1 hβ.2 i₀ χ
  refine ⟨v, hv, fun j => ?_⟩
  simpa only [weightRadius] using (he j).1

/-- Absorb both coercivity losses and the entry-sum polynomial while retaining
the exact exceptional-set power, supporting the proof of Theorem 1. -/
theorem comparison_prefactor_internal (s : Riesz1.RieszExponent)
    (κ η c₀ C c δ βlo : ℝ) (hc₀ : 0 < c₀) (hC : 0 < C)
    (hc : 0 < c) (hδ : 0 < δ) (hlo : 0 < βlo) :
    ∃ D : ℝ, 0 < D ∧ ∀ β x t : ℝ, βlo ≤ β → 1 ≤ x → 0 ≤ t →
      (β*min 1 (s.val*(s.val+1))*x^(-(s.val+2)*η))⁻¹ *
        (x^4*((β*c₀*x^(-κ*η))⁻¹*t)*(C*Real.exp (-c*x^δ))) ≤
          D*Real.exp (-(c/2)*x^δ)*t := by
  let m := min 1 (s.val*(s.val+1))
  have hm : 0 < m := lt_min zero_lt_one (mul_pos s.property.1 (by linarith [s.property.1]))
  let A := (βlo*m)⁻¹*(βlo*c₀)⁻¹*C
  have hA : 0 < A := by dsimp only [A]; positivity
  obtain ⟨B, hB, hbound⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := 4+(s.val+2+κ)*η) (c := c) (c' := c/2) hδ (by linarith)
  refine ⟨A*(B+1), by positivity, fun β x t hβ hx ht => ?_⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hβ0 : 0 < β := hlo.trans_le hβ
  have hcoef : (β*m)⁻¹*(β*c₀)⁻¹*C ≤ A := by
    apply mul_le_mul_of_nonneg_right _ hC.le
    exact mul_le_mul
      (inv_anti₀ (mul_pos hlo hm) (mul_le_mul_of_nonneg_right hβ hm.le))
      (inv_anti₀ (mul_pos hlo hc₀) (mul_le_mul_of_nonneg_right hβ hc₀.le))
      (by positivity) (by positivity)
  have hp : x^4*x^((s.val+2)*η)*x^(κ*η) = x^(4+(s.val+2+κ)*η) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hx0, ← Real.rpow_add hx0]
    congr 1
    push_cast
    ring
  have he : (β*m*x^(-(s.val+2)*η))⁻¹ *
      (x^4*((β*c₀*x^(-κ*η))⁻¹*t)*(C*Real.exp (-c*x^δ))) =
      ((β*m)⁻¹*(β*c₀)⁻¹*C) *
        (x^(4+(s.val+2+κ)*η)*Real.exp (-c*x^δ))*t := by
    rw [show -(s.val+2)*η = -((s.val+2)*η) by ring,
      show -κ*η = -(κ*η) by ring, Real.rpow_neg hx0.le, Real.rpow_neg hx0.le]
    simp only [mul_inv_rev, inv_inv]
    rw [← hp]
    ring
  change (β*m*x^(-(s.val+2)*η))⁻¹ * _ ≤ _
  rw [he]
  calc
    _ ≤ A*(x^(4+(s.val+2+κ)*η)*Real.exp (-c*x^δ))*t :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (by positivity)) ht
    _ ≤ A*(B*Real.exp (-(c/2)*x^δ))*t :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hbound x hx) hA.le) ht
    _ ≤ (A*(B+1))*Real.exp (-(c/2)*x^δ)*t := by
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (show B ≤ B+1 by linarith) hA.le)
        (show 0 ≤ Real.exp (-(c/2)*x^δ)*t by positivity)
      convert hh using 1 <;> ring

/-- The coercive bound at bounded volumes has the required cyclic profile,
supporting the proof of Theorem 1. -/
theorem finite_volume_profile_internal (s : Riesz1.RieszExponent)
    {βlo β L n r loss : ℝ} (hlo : 0 < βlo) (hβ : βlo ≤ β)
    (hn : 1 ≤ n) (hnL : n ≤ L) (hr : 0 ≤ r) (hrn : r ≤ n) (hloss : 0 ≤ loss) :
    (β*(s.val*(s.val+1))*n^(-s.val-2))⁻¹ ≤
      ((βlo*(s.val*(s.val+1)))⁻¹*L^(s.val+2)*(1+L)^(2-s.val)) *
        n^loss*(1+r)^(-(2-s.val)) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hL0 : 0 < L := hn0.trans_le hnL
  have hs : 0 < s.val*(s.val+1) := mul_pos s.property.1 (by linarith [s.property.1])
  have hp : 0 < 2-s.val := by linarith [s.property.2]
  have hbase : (β*(s.val*(s.val+1))*n^(-s.val-2))⁻¹ ≤
      (βlo*(s.val*(s.val+1)))⁻¹*L^(s.val+2) := by
    rw [show -s.val-2 = -(s.val+2) by ring, Real.rpow_neg hn0.le, mul_inv_rev, inv_inv]
    rw [mul_comm]
    exact mul_le_mul (inv_anti₀ (mul_pos hlo hs)
      (mul_le_mul_of_nonneg_right hβ hs.le))
      (Real.rpow_le_rpow hn0.le hnL (by linarith [s.property.1]))
      (by positivity) (by positivity)
  have hprof : (1+L)^(-(2-s.val)) ≤ (1+r)^(-(2-s.val)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
  have hone : 1 ≤ (1+L)^(2-s.val)*(1+r)^(-(2-s.val)) := by
    have hh := mul_le_mul_of_nonneg_left hprof
      (Real.rpow_nonneg (show 0 ≤ 1+L by positivity) (2-s.val))
    rw [← Real.rpow_add (by positivity : 0 < 1+L), add_neg_cancel, Real.rpow_zero] at hh
    exact hh
  have hpower : 1 ≤ n^loss := Real.one_le_rpow hn hloss
  have hfactor : 1 ≤ (1+L)^(2-s.val)*n^loss*(1+r)^(-(2-s.val)) := by
    have hh := mul_le_mul_of_nonneg_left hpower
      (show 0 ≤ (1+L)^(2-s.val)*(1+r)^(-(2-s.val)) by positivity)
    rw [mul_one] at hh
    exact hone.trans (hh.trans_eq (by ring))
  apply hbase.trans
  have hh := mul_le_mul_of_nonneg_left hfactor
    (show 0 ≤ (βlo*(s.val*(s.val+1)))⁻¹*L^(s.val+2) by positivity)
  convert hh using 1 <;> ring

/-- See the proof of Theorem 1 in the paper: full-cycle physical
point-source decay on the intrinsic tangent form, with the exact exceptional-set
power of Subsection 5.1. The loss exponent and admissible loss threshold precede
the temperature. Both prefactors are uniform on each compact positive temperature
interval. The physical realization and unique weak solution are conclusions. -/
theorem decay_gap_correlations_full_cycle
    (hzeta : External.PeriodicZeta) (hRig : External.LongRangeRigidityLocallyUniform)
    (s : Riesz1.RieszExponent) (M₀ : ℕ+) :
    ∃ ηstar κ : ℝ, 0 < ηstar ∧ 0 < κ ∧
    ∀ η : ℝ, 0 < η → η < ηstar →
    0 < GoodBlocks.coefficientTailPower s.val η ∧
    ∀ (θ : PhysicalCutoff) (βlo βhi : ℝ), 0 < βlo → βlo ≤ βhi →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)),
    let ν := fullIntrinsicTiltedGapLaw (ofLong β s) N θ η false
    0 < tiltNormalizer (ofLong β s) N N le_rfl θ η false ∧
    tiltNormalizer (ofLong β s) N N le_rfl θ η false < ⊤ ∧ IsProbabilityMeasure ν ∧
    ∃ (W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ) (Q : ScalarFormData ν),
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = fullPhysicalPotentialValue (ofLong β s) N hN θ η false y) ∧
      IsEuclideanGibbsPotential volume ν (intrinsicGapDomain N)
        (fun z => W (WithLp.toLp 2 (fun i => 1+z.val i))) ∧
      IsNeumannRealization (intrinsicGapDomain N) Q ∧
      IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
      ∀ (i₀ : Fin (N : ℕ)) (χ : Lp ℝ 2 ν), eLpNorm χ ∞ ν < ⊤ →
      let H := fun z : gapTangentSpace N => hessianMatrix W
        (WithLp.toLp 2 (fun i => 1+z.val i))
      (∃! ψ : Fin (N : ℕ) → Q.1, WeightedWeakSolution Q H (zeroSumComponents _)
        (fun i => if i=i₀ then χ else 0) ψ) ∧
      ∀ ψ : Fin (N : ℕ) → Q.1,
        WeightedWeakSolution Q H (zeroSumComponents _)
          (fun i => if i=i₀ then χ else 0) ψ →
        ∀ j : Fin (N : ℕ), ‖(ψ j).val‖ ≤
          C*(N : ℝ)^(κ*η)*(1+(Riesz1.cyclicIndexDistance N j i₀ : ℝ))^(-(2-s.val))*‖χ‖ +
          C*Real.exp (-c*(N : ℝ)^GoodBlocks.coefficientTailPower s.val η)*(eLpNorm χ ∞ ν).toReal := by
  obtain ⟨η₀, κ, hη₀, hκ, haux⟩ := auxiliary_localization_internal hzeta s M₀
  obtain ⟨c₀, κe, hc₀, hκe, herror⟩ := physical_auxiliary_error hRig s (M₀ : ℕ)
  let ηstar := min η₀ (1/(2*((M₀ : ℝ)+1)))
  have hηstar : 0 < ηstar := lt_min hη₀ (by positivity)
  refine ⟨ηstar, κ, hηstar, hκ, fun η hη hηmax => ?_⟩
  have hδ := GoodBlocks.coefficientTailPower_pos s.property.1 s.property.2 hη
  have hηaux : η ≤ η₀ := hηmax.le.trans (min_le_left _ _)
  have hηcut : (M₀ : ℝ)*η < 1 := by
    have hh : η < 1/(2*((M₀ : ℝ)+1)) := hηmax.trans_le (min_le_right _ _)
    have hp := (lt_div_iff₀ (show 0 < 2*((M₀ : ℝ)+1) by positivity)).mp hh
    nlinarith [show (0 : ℝ) ≤ M₀ by positivity]
  obtain ⟨L, hL, hcut⟩ := eventual_cutoff_internal M₀ hη hηcut
  refine ⟨hδ, fun θ βlo βhi hlo hle => ?_⟩
  obtain ⟨Cθ, hCθ, hθ, _⟩ := θ.property.2.2.2.2
  obtain ⟨Ca, hCa, haux⟩ := haux θ η hη hηaux βlo βhi hlo hle
  obtain ⟨Ce, ce, hCe, hce, herror⟩ := herror hη hCθ βlo βhi hlo hle
  obtain ⟨D, hD, habsorb⟩ := comparison_prefactor_internal s κe η c₀ Ce ce
    (GoodBlocks.coefficientTailPower s.val η) βlo hc₀ hCe hce hδ hlo
  let F := (βlo*(s.val*(s.val+1)))⁻¹*L^(s.val+2)*(1+L)^(2-s.val)
  have hL0 : 0 < L := by linarith
  have hF : 0 < F := by
    have hs : 0 < s.val*(s.val+1) := mul_pos s.property.1 (by linarith [s.property.1])
    dsimp only [F]
    positivity
  let C := Ca+D+F+1
  have hC : 0 < C := by dsimp only [C]; positivity
  have hCaC : Ca ≤ C := by dsimp only [C]; linarith
  have hDC : D ≤ C := by dsimp only [C]; linarith
  have hFC : F ≤ C := by dsimp only [C]; linarith
  refine ⟨C, ce/2, hC, by positivity, ?_⟩
  intro β hβ N hN ν
  have hn0 : (0 : ℝ) < N := by positivity
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  obtain ⟨hZ0, hZt, hprob, W, Q, hW, hval, hG, hNeum, hQ, hcons, hsol⟩ :=
    DecayShort.PhysicalDecay.full_physical_wellposed (ofLong β s) N hN θ η false
  let : IsProbabilityMeasure ν := hprob
  refine ⟨hZ0, hZt, hprob, W, Q, hW, hval, hG, hNeum, hQ, hcons, ?_⟩
  intro i₀ χ hχ H
  refine ⟨(hsol (fun i => if i=i₀ then χ else 0)).1, ?_⟩
  intro ψ hψ j
  have hmainC : Ca*(N : ℝ)^(κ*η)*
      (1+(Riesz1.cyclicIndexDistance N j i₀ : ℝ))^(-(2-s.val))*‖χ‖ ≤
      C*(N : ℝ)^(κ*η)*
      (1+(Riesz1.cyclicIndexDistance N j i₀ : ℝ))^(-(2-s.val))*‖χ‖ := by
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCaC (by positivity)) (by positivity)) (norm_nonneg χ)
  by_cases hlarge : L ≤ (N : ℝ)
  · obtain ⟨hK, hKN⟩ := hcut N hlarge
    have hKN' : ⌊(N : ℝ)^η⌋₊^(M₀ : ℕ) ≤ (N : ℕ)/4 := by omega
    obtain ⟨v, hv, hvbound⟩ := haux β hβ N hN hK hKN Q hQ hcons i₀ χ
    have he := herror β hβ N hN θ hθ 1 (by norm_num) hKN' W hW hval Q hQ
      i₀ χ hχ ψ v hψ hv
    have he' := he.trans (habsorb β.val (N : ℝ) (eLpNorm χ ∞ ν).toReal hβ.1 hn1
      ENNReal.toReal_nonneg)
    have heC := he'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hDC (Real.exp_nonneg _)) ENNReal.toReal_nonneg)
    have ht : ‖(ψ j).val‖ ≤ ‖(v j).val‖+‖(ψ j-v j).val‖ := by
      have hh := norm_add_le (v j).val (ψ j-v j).val
      simpa only [Submodule.coe_sub, add_sub_cancel] using hh
    have hj : ‖(ψ j-v j).val‖ ≤ ‖WithLp.toLp 2 (fun i => (ψ i-v i).val)‖ :=
      PiLp.norm_apply_le (WithLp.toLp 2 (fun i => (ψ i-v i).val)) j
    exact ht.trans (add_le_add ((hvbound j).trans hmainC) (hj.trans heC))
  · have he := (hsol (fun i => if i=i₀ then χ else 0)).2 ψ hψ
    have hf : ‖WithLp.toLp 2 (fun i : Fin (N : ℕ) => if i=i₀ then χ else 0)‖ = ‖χ‖ := by
      convert PiLp.norm_single 2 (fun _ : Fin (N : ℕ) => Lp ℝ 2 ν) i₀ χ using 1
      congr 1
      apply PiLp.ext
      intro i
      simp only [PiLp.single_apply]
    rw [hf] at he
    have hrn : (Riesz1.cyclicIndexDistance N j i₀ : ℝ) ≤ (N : ℝ) := by
      have hh := Riesz1.APG.cyclicIndexDistance_le_half j i₀
      exact_mod_cast (show Riesz1.cyclicIndexDistance N j i₀ ≤ (N : ℕ) by omega)
    have hb := finite_volume_profile_internal s hlo hβ.1 hn1 (le_of_not_ge hlarge)
      (by positivity : (0 : ℝ) ≤ Riesz1.cyclicIndexDistance N j i₀) hrn
      (mul_nonneg hκ.le hη.le)
    have hb' := mul_le_mul_of_nonneg_right hb (norm_nonneg χ)
    have hn : ‖(ψ j).val‖ ≤ F*(N : ℝ)^(κ*η)*
        (1+(Riesz1.cyclicIndexDistance N j i₀ : ℝ))^(-(2-s.val))*‖χ‖ := by
      apply (PiLp.norm_apply_le (WithLp.toLp 2 (fun i => (ψ i).val)) j).trans
      exact he.trans hb'
    have hmono := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hFC (by positivity : (0 : ℝ) ≤ (N : ℝ)^(κ*η)))
      (by positivity : (0 : ℝ) ≤ (1+(Riesz1.cyclicIndexDistance N j i₀ : ℝ))^(-(2-s.val))))
      (norm_nonneg χ)
    exact (hn.trans hmono).trans (le_add_of_nonneg_right (by positivity))

end Riesz2.FullCycleComparison
