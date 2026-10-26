/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.CyclicFourierL2
public import Riesz2.DecayLong.AbstractEquation
public import Riesz2.ToMathlib.ConstrainedNormalMultiplier
public import Riesz2.DecayLong.DerivativeCommutatorsPart2
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Weighted derivative control

The weighted test of the periodized equation in Lemma 5.11. Component size
and scalar dimension are independent. All counting-measure mixed norms
are finite.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Riesz2.FiniteMixedL2

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι] {ν : Measure X}

/-- Every finite counting-measure component norm of L² fields belongs to L². -/
theorem norm_memLp (q : ℝ≥0∞) [Fact (1 ≤ q)] (u : ι → Lp ℝ 2 ν) :
    MemLp (fun x => ‖(WithLp.toLp q (fun i => u i x) : PiLp q (fun _ : ι => ℝ))‖) 2 ν := by
  exact (memLp_piLp_iff.mpr (fun i => Lp.memLp (u i))).norm

/-- The Euclidean norm of a finite deterministic weighting is in L². -/
theorem weighted_memLp (w : ι → ℝ) (u : ι → Lp ℝ 2 ν) :
    MemLp (fun x => Real.sqrt (∑ i, (w i * u i x) ^ 2)) 2 ν := by
  have h : MemLp (fun x => (WithLp.toLp 2 (fun i => w i * u i x) :
      PiLp 2 (fun _ : ι => ℝ))) 2 ν :=
    memLp_piLp_iff.mpr (fun i => (Lp.memLp (u i)).const_mul (w i))
  simpa only [PiLp.norm_eq_of_L2, Real.norm_eq_abs, sq_abs] using h.norm

/-- Square integration of the weighted Euclidean norm gives exactly the
sum of squared weighted component L² norms. -/
theorem weighted_sq_integral (w : ι → ℝ) (u : ι → Lp ℝ 2 ν) :
    (∫ x, (Real.sqrt (∑ i, (w i * u i x) ^ 2)) ^ 2 ∂ν) =
      ∑ i, (w i * ‖u i‖) ^ 2 := by
  simp_rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  exact (CyclicFourierL2.weighted_integral_sq w u).2

/-- Cauchy–Schwarz for two nonnegative L² functions, using finite real
square integrals. -/
theorem integral_mul_le {f g : X → ℝ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν)
    (hf0 : ∀ᵐ x ∂ν, 0 ≤ f x) (hg0 : ∀ᵐ x ∂ν, 0 ≤ g x) :
    (∫ x, f x * g x ∂ν) ≤
      Real.sqrt (∫ x, f x ^ 2 ∂ν) * Real.sqrt (∫ x, g x ^ 2 ∂ν) := by
  have htwo : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg htwo hf0 hg0
    (by simpa only [ENNReal.ofReal_ofNat] using hf)
    (by simpa only [ENNReal.ofReal_ofNat] using hg)
  simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow] using h

end Riesz2.FiniteMixedL2

namespace Riesz2.DerivativeControl

open Filter
open scoped Matrix

variable {X ι : Type*} [MeasurableSpace X] [Fintype ι]
  {ν : Measure X}

/-- Restoring a scalar multiplier in the unrestricted equation preserves
its restriction to zero-sum tests. -/
theorem constrained_of_multiplier (Q : ScalarFormData ν) (M : X → Matrix ι ι ℝ)
    (f : ι → Lp ℝ 2 ν) (lam : Lp ℝ 2 ν) (u : ι → Q.1)
    (hz : ∀ᵐ x ∂ν, ∑ i, (u i).val x = 0)
    (hu : WeightedWeakSolution Q M ⊤ (fun i => f i + lam) u) :
    WeightedWeakSolution Q M (zeroSumComponents ι) f u := by
  refine ⟨⟨hz, hu.1.2⟩, fun h hh => ?_⟩
  obtain ⟨hi, he⟩ := hu.2 h ⟨Eventually.of_forall (fun _ => Submodule.mem_top), hh.2⟩
  refine ⟨hi, ?_⟩
  have hs : ∑ i, (h i).val = 0 := AbstractEquation.sum_values_eq_zero _ hh.1
  simpa only [inner_add_left, Finset.sum_add_distrib, ← inner_sum, hs,
    inner_zero_right, add_zero] using he

/-- A deterministic diagonal weighting is an admissible unrestricted test
for every bounded matrix field. -/
theorem weighted_test_domain (Q : ScalarFormData ν) (M : X → Matrix ι ι ℝ)
    (hm : ∀ i j, Measurable (fun x => M x i j))
    (hb : ∃ B : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ B)
    (w : ι → ℝ) (u : ι → Q.1) :
    WeightedFormDomain Q M ⊤ (fun i => w i • u i) :=
  (BoundedMatrixForms.domain_iff Q M hm hb ⊤ _).mpr
    (Eventually.of_forall (fun _ => Submodule.mem_top))

/-- Symmetry moves the deterministic diagonal weight from the second
argument of the matrix pairing to the first one. -/
theorem weighted_pair (Q : ScalarFormData ν) (M : X → Matrix ι ι ℝ)
    (hs : ∀ᵐ x ∂ν, ∀ i j, M x i j = M x j i)
    (w : ι → ℝ) (u : ι → Q.1) :
    matrixFieldPair M (fun i => (u i).val) (fun i => (w i • u i).val) =ᵐ[ν]
      (fun x => ∑ i, w i * (u i).val x * (M x *ᵥ (fun j => (u j).val x)) i) := by
  filter_upwards [hs, ae_all_iff.mpr (fun i => Lp.coeFn_smul (w i) (u i).val)] with x hx hw
  simp only [matrixFieldPair, Submodule.coe_smul, hw, Pi.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hx j i]
  ring

/-- The scalar form term of the weighted test is the weighted gradient
square, with no differentiation of the matrix coefficients. -/
theorem weighted_form (Q : ScalarFormData ν) (w : ι → ℝ) (u : ι → Q.1) :
    (∑ i, Q.2 (u i) (w i • u i)) = ∑ i, w i * Q.2 (u i) (u i) := by
  simp only [map_smul, smul_eq_mul]

/-- The weighted multiplier pairing costs at most the cycle size. -/
theorem multiplier_norm (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (i₀ : Fin (N : ℕ)) (γ : ℝ) (u : Fin (N : ℕ) → Lp ℝ 2 ν) :
    ‖∑ i, weightRadius N i i₀ ^ (2 * (γ / 2 + 1 / 4)) • u i‖ ≤
      (N : ℝ) * Real.sqrt (∑ i, (weightRadius N i i₀ ^ γ * ‖u i‖) ^ 2) := by
  have hR (i : Fin (N : ℕ)) : 0 < weightRadius N i i₀ :=
    lt_of_lt_of_le zero_lt_one (one_le_weightRadius N i i₀)
  have hpow (i : Fin (N : ℕ)) : weightRadius N i i₀ ^ (2 * (γ / 2 + 1 / 4)) =
      weightRadius N i i₀ ^ (1 / 2 : ℝ) * weightRadius N i i₀ ^ γ := by
    rw [← Real.rpow_add (hR i)]
    congr 1
    ring
  have hrange (i : Fin (N : ℕ)) : weightRadius N i i₀ ≤ (N : ℝ) := by
    have hd : 2 * Riesz1.cyclicIndexDistance N i i₀ ≤ (N : ℕ) := by
      unfold Riesz1.cyclicIndexDistance Nat.dist
      have := i.isLt
      have := i₀.isLt
      omega
    have h := N.pos
    dsimp [weightRadius]
    exact_mod_cast (show 1 + Riesz1.cyclicIndexDistance N i i₀ ≤ (N : ℕ) by omega)
  have hs : (∑ i : Fin (N : ℕ), weightRadius N i i₀) ≤ (N : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin (N : ℕ), (N : ℝ) := Finset.sum_le_sum (fun i _ => hrange i)
      _ = _ := by simp [sq]
  have hp (i : Fin (N : ℕ)) : (weightRadius N i i₀ ^ (1 / 2 : ℝ)) ^ 2 =
      weightRadius N i i₀ := by rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (hR i).le]
  calc
    _ ≤ ∑ i, ‖weightRadius N i i₀ ^ (2 * (γ / 2 + 1 / 4)) • u i‖ := norm_sum_le _ _
    _ = ∑ i, weightRadius N i i₀ ^ (1 / 2 : ℝ) *
        (weightRadius N i i₀ ^ γ * ‖u i‖) := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (hR _) _)]
      simp_rw [hpow, mul_assoc]
    _ ≤ Real.sqrt (∑ i, weightRadius N i i₀) *
        Real.sqrt (∑ i, (weightRadius N i i₀ ^ γ * ‖u i‖) ^ 2) := by
      simpa only [hp] using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
        (fun i => weightRadius N i i₀ ^ (1 / 2 : ℝ))
        (fun i => weightRadius N i i₀ ^ γ * ‖u i‖)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact (Real.sqrt_le_sqrt hs).trans_eq (Real.sqrt_sq (by positivity))


/-- Finite matrices map L² component fields into every finite mixed L²,ℓᵖ
space. In particular the fractional primitive norm has a finite square integral. -/
theorem matrix_lp_memLp (p : ℝ) (hp : 1 ≤ p) (H : Matrix ι ι ℝ)
    (u : ι → Lp ℝ 2 ν) :
    MemLp (fun x => (∑ i, |(H *ᵥ (fun j => u j x)) i| ^ p) ^ (1 / p)) 2 ν := by
  let q := ENNReal.ofReal p
  have hq : 1 ≤ q := by simpa only [q, ← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have : Fact (1 ≤ q) := ⟨hq⟩
  have h : MemLp (fun x => (WithLp.toLp q (H *ᵥ (fun j => u j x)) :
      PiLp q (fun _ : ι => ℝ))) 2 ν := by
    apply memLp_piLp_iff.mpr
    intro i
    exact memLp_finsetSum Finset.univ (fun j _ => (Lp.memLp (u j)).const_mul (H i j))
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have he : q.toReal = p := ENNReal.toReal_ofReal hp0.le
  simpa only [PiLp.norm_eq_sum (by rw [he]; exact hp0), he, Real.norm_eq_abs] using h.norm

/-- Internal integrated matrix estimate: discard the positive retained
quadratic form and integrate the two established commutator estimates. -/
theorem matrix_lower_integral_internal (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (γ : ℝ) (hγ : 1 / 2 ≤ γ) :
    ∃ B D : ℝ, 0 < B ∧ 0 < D ∧
    ∀ {X : Type*} [MeasurableSpace X] (ν : Measure X),
    ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (i₀ : Fin (N : ℕ)) (η A : ℝ),
    0 < η → η < 1 / 4 → 0 ≤ A →
    ∀ (α : Fin (N : ℕ) → Fin ((N : ℕ) / 2) → X → ℝ)
      (M : X → Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ),
    (∀ᵐ x ∂ν, (∀ k r, 0 ≤ α k r x ∧ α k r x ≤
      A * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2)) ∧
      ∀ a b, M x a b = ∑ k, ∑ r, α k r x *
        (if a ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0) *
        (if b ∈ cyclicIndexInterval N k (r.val + 1) then 1 else 0)) →
    ∀ (u : Fin (N : ℕ) → Lp ℝ 2 ν),
    let t := γ / 2 + 1 / 4
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    let p := (1 - s.val / 2)⁻¹
    let V := fun x => (∑ i, |(rieszMatrix sh N hN *ᵥ
      (fun j => u j x)) i| ^ p) ^ (1 / p)
    let Xρ := fun ρ => Real.sqrt (∑ i, (weightRadius N i i₀ ^ ρ * ‖u i‖) ^ 2)
    let E := fun x => ∑ i, weightRadius N i i₀ ^ (2 * t) * u i x *
      (M x *ᵥ (fun j => u j x)) i
    Integrable E ν →
    -(∫ x, E x ∂ν) ≤ B * A * η ^ (3 - s.val) * Xρ γ * Xρ (3 / 2 - s.val) +
      D * A * η⁻¹ * Real.sqrt (Real.log (2 * (N : ℝ))) * Xρ γ *
        Real.sqrt (∫ x, V x ^ 2 ∂ν) := by
  obtain ⟨B, hB, hshort⟩ := DerivativeCommutators.diff_short_bound s γ hγ
  obtain ⟨D, hD, hlong⟩ := DerivativeCommutators.diff_long_pointwise hz s γ hγ
  refine ⟨B, D, hB, hD, ?_⟩
  intro X _ ν N hN i₀ η A hη hη' hA α M hα u t sh p V Xρ E hE
  let U := fun (ρ : ℝ) x => Real.sqrt (∑ i, (weightRadius N i i₀ ^ ρ * u i x) ^ 2)
  have hU (ρ : ℝ) : MemLp (U ρ) 2 ν :=
    FiniteMixedL2.weighted_memLp _ u
  have hp : 1 ≤ p := by
    dsimp [p]
    exact (one_le_inv₀ (by linarith [s.property.2])).mpr (by linarith [s.property.1])
  have hV : MemLp V 2 ν := matrix_lp_memLp p hp _ u
  have hU0 (ρ : ℝ) : ∀ᵐ x ∂ν, 0 ≤ U ρ x := Eventually.of_forall (fun _ => Real.sqrt_nonneg _)
  have hV0 : ∀ᵐ x ∂ν, 0 ≤ V x := Eventually.of_forall (fun _ => by dsimp [V]; positivity)
  have hUint (ρ : ℝ) : Real.sqrt (∫ x, (U ρ x) ^ 2 ∂ν) = Xρ ρ := by
    rw [FiniteMixedL2.weighted_sq_integral]
  let b := B * A * η ^ (3 - s.val)
  let d := D * A * η⁻¹ * Real.sqrt (Real.log (2 * (N : ℝ)))
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hbound : ∀ᵐ x ∂ν, -E x ≤ b * U γ x * U (3 / 2 - s.val) x + d * U γ x * V x := by
    filter_upwards [hα] with x hx
    let v := fun i => u i x
    let R := DerivativeCommutators.retainedMatrix N i₀ η (fun k r => α k r x)
    have hid := DerivativeCommutators.retained_commutator_identity N i₀ η t
      (fun k r => α k r x) (M x) v
    have hpos := DerivativeCommutators.retainedMatrix_posSemidef N i₀ η
      (fun k r => α k r x) (fun k r => (hx.1 k r).1)
    have hpos' : 0 ≤ ∑ i, (weightRadius N i i₀ ^ t * v i) *
        (R *ᵥ (fun j => weightRadius N j i₀ ^ t * v j)) i := by
      simpa only [dotProduct, star_trivial] using hpos.dotProduct_mulVec_nonneg
        (fun j => weightRadius N j i₀ ^ t * v j)
    have hs := hshort N i₀ η A hη hη' hA (fun k r => α k r x) hx.1 v
    have hl := hlong N hN i₀ η A hη hη' hA (fun k r => α k r x) hx.1 (M x) hx.2 v
    have hs' := neg_le_abs ((1 / 2 : ℝ) * ∑ i, ∑ j, R i j *
      (weightRadius N i i₀ ^ t - weightRadius N j i₀ ^ t) ^ 2 * v i * v j)
    have hl' := neg_le_abs (∑ i, weightRadius N i i₀ ^ (2 * t) * v i *
      (DerivativeCommutators.discardedMatrix N i₀ η (fun k r => α k r x) (M x) *ᵥ v) i)
    change - (∑ i, weightRadius N i i₀ ^ (2 * t) * v i * (M x *ᵥ v) i) ≤ _
    change _ ≤ b * U γ x * U (3 / 2 - s.val) x at hs
    change _ ≤ d * U γ x * V x at hl
    linarith
  have hprod₁ : Integrable (fun x => b * U γ x * U (3 / 2 - s.val) x) ν := by
    simpa only [Pi.mul_apply, mul_assoc] using
      ((hU γ).integrable_mul (hU (3 / 2 - s.val))).const_mul b
  have hprod₂ : Integrable (fun x => d * U γ x * V x) ν := by
    simpa only [Pi.mul_apply, mul_assoc] using ((hU γ).integrable_mul hV).const_mul d
  have hi : -(∫ x, E x ∂ν) ≤ b * ∫ x, U γ x * U (3 / 2 - s.val) x ∂ν +
      d * ∫ x, U γ x * V x ∂ν := by
    calc
      _ = ∫ x, -E x ∂ν := (integral_neg _).symm
      _ ≤ ∫ x, b * U γ x * U (3 / 2 - s.val) x + d * U γ x * V x ∂ν :=
        integral_mono_ae hE.neg (hprod₁.add hprod₂) hbound
      _ = _ := by
        rw [integral_add hprod₁ hprod₂]
        simp_rw [mul_assoc, integral_const_mul]
  have hcs₁ := FiniteMixedL2.integral_mul_le (hU γ) (hU (3 / 2 - s.val)) (hU0 _) (hU0 _)
  have hcs₂ := FiniteMixedL2.integral_mul_le (hU γ) hV (hU0 _) hV0
  rw [hUint, hUint] at hcs₁
  rw [hUint] at hcs₂
  calc
    _ ≤ b * ∫ x, U γ x * U (3 / 2 - s.val) x ∂ν + d * ∫ x, U γ x * V x ∂ν := hi
    _ ≤ b * (Xρ γ * Xρ (3 / 2 - s.val)) +
        d * (Xρ γ * Real.sqrt (∫ x, V x ^ 2 ∂ν)) :=
      add_le_add (mul_le_mul_of_nonneg_left hcs₁ hb) (mul_le_mul_of_nonneg_left hcs₂ hd)
    _ = _ := by dsimp [b, d]; ring


/-- Internal scalar bookkeeping for the final derivative estimate. -/
theorem absorb_internal {B D βlo βhi Cstar β L a F X Y Z T G : ℝ}
    (hB : 0 < B) (hD : 0 < D) (hCstar : 1 ≤ Cstar)
    (hβlo : 0 < βlo) (hβhi : βlo ≤ βhi) (_hβloβ : βlo ≤ β) (hββhi : β ≤ βhi)
    (hL : 1 ≤ L) (ha : a ≤ βlo⁻¹ * Cstar * L)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hZ : 0 ≤ Z) (hT : 0 ≤ T)
    (hraw : G ≤ a * F ^ 2 + T * X + β *
      (B * Cstar * L * X * Y + D * Cstar * L * X * Z)) :
    G ≤ (βlo⁻¹ * Cstar + βhi * (B + D) * Cstar + 1) * L *
      (F ^ 2 + X * (Y + Z + T)) := by
  let C := βlo⁻¹ * Cstar + βhi * (B + D) * Cstar + 1
  have hCstar0 : 0 ≤ Cstar := le_trans zero_le_one hCstar
  have hβhi0 : 0 ≤ βhi := (hβlo.trans_le hβhi).le
  have hC₁ : βlo⁻¹ * Cstar ≤ C := by
    have h := mul_nonneg (mul_nonneg hβhi0 (add_nonneg hB.le hD.le)) hCstar0
    dsimp [C]
    linarith
  have hC₂ : β * B * Cstar ≤ C := by
    have h := mul_le_mul_of_nonneg_right hββhi (mul_nonneg hB.le hCstar0)
    have h₁ := mul_nonneg hβhi0 (mul_nonneg hD.le hCstar0)
    have h₂ := mul_nonneg (inv_nonneg.mpr hβlo.le) hCstar0
    dsimp [C]
    nlinarith only [h, h₁, h₂]
  have hC₃ : β * D * Cstar ≤ C := by
    have h := mul_le_mul_of_nonneg_right hββhi (mul_nonneg hD.le hCstar0)
    have h₁ := mul_nonneg hβhi0 (mul_nonneg hB.le hCstar0)
    have h₂ := mul_nonneg (inv_nonneg.mpr hβlo.le) hCstar0
    dsimp [C]
    nlinarith only [h, h₁, h₂]
  have hC₄ : 1 ≤ C * L := by
    have hc : 1 ≤ C := by
      have h₁ := mul_nonneg (inv_nonneg.mpr hβlo.le) hCstar0
      have h₂ := mul_nonneg (mul_nonneg hβhi0 (add_nonneg hB.le hD.le)) hCstar0
      dsimp [C]
      linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hL)]
  have hL0 : 0 ≤ L := le_trans zero_le_one hL
  have h₁ := mul_le_mul_of_nonneg_right
    (ha.trans (mul_le_mul_of_nonneg_right hC₁ hL0)) (sq_nonneg F)
  have h₂ := mul_le_mul_of_nonneg_right hC₄ (mul_nonneg hT hX)
  have h₃ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₂ hL0) (mul_nonneg hX hY)
  have h₄ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₃ hL0) (mul_nonneg hX hZ)
  change G ≤ C * L * (F ^ 2 + X * (Y + Z + T))
  nlinarith only [hraw, h₁, h₂, h₃, h₄]

/-- See Lemma 5.11 of the paper (Control on derivatives). The scalar form gives
exactly the weighted gradient square. Constants are uniform in component
size, scalar probability space, source, retention parameter, and β in the
specified compact interval. The loss exponent is independent of β and ε.
The conclusion also asserts finiteness of the fractional mixed norm. -/
theorem diff_with_multiplier (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (γ : ℝ) (hγ : 1 / 2 ≤ γ) (κstar γstar : ℝ) (hκstar : 0 < κstar) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (Cstar : ℝ), 1 ≤ Cstar →
    ∀ (βlo : ℝ), 0 < βlo → ∀ (βhi : ℝ), βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ), 0 < ε →
    ∀ {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
      (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q →
    ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ)) (K : ℕ)
      (M : X → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ),
    PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M →
    ∀ (β : ℝ), βlo ≤ β → β ≤ βhi →
    ∀ (χ : Q.1) (i₀ : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1)
      (lam : Lp ℝ 2 ν),
    WeightedWeakSolution Q (fun x => β • M x) ⊤
      (fun i => (if i = i₀ then χ.val else 0) + lam) u →
    (∀ᵐ x ∂ν, ∑ i, (u i).val x = 0) →
    let t := γ / 2 + 1 / 4
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    let p := (1 - s.val / 2)⁻¹
    let V := fun x => (∑ i, |(rieszMatrix sh m hm *ᵥ
      (fun j => (u j).val x)) i| ^ p) ^ (1 / p)
    let Xρ := fun ρ => Real.sqrt (∑ i, (weightRadius m i i₀ ^ ρ * ‖(u i).val‖) ^ 2)
    Integrable (fun x => V x ^ 2) ν ∧
    ∀ (η : ℝ), 0 < η → η < 1 / 4 →
      (∑ i, weightRadius m i i₀ ^ (2 * t) * Q.2 (u i) (u i)) ≤
        C * (n : ℝ) ^ (κ * ε) * (‖χ.val‖ ^ 2 + Xρ γ *
          (η ^ (3 - s.val) * Xρ (3 / 2 - s.val) +
            η⁻¹ * Real.sqrt (Real.log (2 * (m : ℝ))) *
              Real.sqrt (∫ x, V x ^ 2 ∂ν) + (m : ℝ) * ‖lam‖)) := by
  obtain ⟨B, D, hB, hD, hmatrix⟩ := matrix_lower_integral_internal hz s γ hγ
  refine ⟨κstar, hκstar, fun Cstar hCstar βlo hβlo βhi hβhi => ?_⟩
  let C := βlo⁻¹ * Cstar + βhi * (B + D) * Cstar + 1
  have hCstar0 : 0 < Cstar := lt_of_lt_of_le zero_lt_one hCstar
  have hβhi0 : 0 < βhi := hβlo.trans_le hβhi
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro ε hε X _ ν _ Q hQ n m hm K M hM β hβloβ hββhi χ i₀ u lam hu hzero
    t sh p V Xρ
  let v := fun i => (u i).val
  let f := fun i => if i = i₀ then χ.val else 0
  let A := Cstar * (n : ℝ) ^ (κstar * ε)
  let a := Cstar⁻¹ * (n : ℝ) ^ (-κstar * ε)
  have hβ : 0 < β := hβlo.trans_le hβloβ
  have ha : 0 < a := SchurRestriction.periodized_mass_pos hCstar
  have hn : 1 ≤ (n : ℝ) := by exact_mod_cast n.pos
  have hP : 1 ≤ (n : ℝ) ^ (κstar * ε) :=
    Real.one_le_rpow hn (mul_nonneg hκstar.le hε.le)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hsym : ∀ᵐ x ∂ν, ∀ i j, M x i j = M x j i := hM.2.1.mono (fun _ hx => hx.1)
  have hMb := SchurRestriction.periodized_scaled_bounded β hM
  have hMm := SchurRestriction.periodized_scaled_measurable β hM
  have huC := constrained_of_multiplier Q _ f lam u hzero hu
  have hlower : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
      ∀ z : Fin (m : ℕ) → ℝ, a * (∑ i, z i ^ 2) ≤
        ∑ i, ∑ j, z i * M x i j * z j :=
    hM.2.1.mono (fun _ hx => ⟨hx.1, hx.2.2.1⟩)
  have henergy := (AbstractEquation.existence_energy Q hQ β hβ M hM.1 a ha hlower
    (zeroSumComponents (Fin (m : ℕ))) f).2 u huC
  have hf : ‖(WithLp.toLp 2 f : PiLp 2 (fun _ : Fin (m : ℕ) => Lp ℝ 2 ν))‖ = ‖χ.val‖ := by
    have hs : (WithLp.toLp 2 f : PiLp 2 (fun _ : Fin (m : ℕ) => Lp ℝ 2 ν)) =
        PiLp.single 2 i₀ χ.val := by
      ext i
      simp [f, PiLp.single_apply, eq_comm]
    rw [hs, PiLp.norm_single]
  rw [hf] at henergy
  have hcomponent : ‖(u i₀).val‖ ≤ (β * a)⁻¹ * ‖χ.val‖ :=
    (PiLp.norm_apply_le (WithLp.toLp 2 v) i₀).trans henergy.1
  have hsource : inner ℝ χ.val (u i₀).val ≤ (β * a)⁻¹ * ‖χ.val‖ ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hcomponent (norm_nonneg χ.val)
    nlinarith [real_inner_le_norm χ.val (u i₀).val]
  have hp : 1 ≤ p := by
    dsimp [p]
    exact (one_le_inv₀ (by linarith [s.property.2])).mpr (by linarith [s.property.1])
  have hV : MemLp V 2 ν := matrix_lp_memLp p hp _ v
  refine ⟨hV.integrable_sq, fun η hη hη' => ?_⟩
  let w := fun i => weightRadius m i i₀ ^ (2 * t)
  let E := fun x => ∑ i, w i * v i x * (M x *ᵥ (fun j => v j x)) i
  have htest := weighted_test_domain Q _ hMm hMb w u
  have heq := hu.2 (fun i => w i • u i) htest
  have hpair := weighted_pair Q M hsym w u
  have hE : Integrable E ν := by
    exact (BoundedMatrixForms.integrable_pair M hM.1
      (SchurRestriction.periodized_bounded hM) v (fun i => (w i • u i).val)).congr hpair
  have hscale : (∫ x, matrixFieldPair (fun x => β • M x) v
      (fun i => (w i • u i).val) x ∂ν) = β * ∫ x, E x ∂ν := by
    rw [SchurRestriction.integral_pair_smul, integral_congr_ae hpair]
  rw [weighted_form, hscale] at heq
  have hsourcepair : (∑ i, inner ℝ (f i + lam) (w i • u i).val) =
      inner ℝ χ.val (u i₀).val + inner ℝ lam (∑ i, w i • v i) := by
    simp only [inner_add_left, Finset.sum_add_distrib, Submodule.coe_smul,
      ← inner_sum]
    congr 1
    rw [Finset.sum_eq_single i₀]
    · simp [f, w, weightRadius, Riesz1.cyclicIndexDistance]
    · intro i _ hi
      simp [f, hi]
    · simp
  rw [hsourcepair] at heq
  have hlambda : inner ℝ lam (∑ i, w i • v i) ≤
      (m : ℝ) * ‖lam‖ * Xρ γ := by
    have hn := multiplier_norm m hm i₀ γ v
    have h := mul_le_mul_of_nonneg_left hn (norm_nonneg lam)
    have hb := real_inner_le_norm lam (∑ i, w i • v i)
    change inner ℝ lam (∑ i, w i • v i) ≤ _
    dsimp only [w, t] at hb
    nlinarith
  obtain ⟨α, _, hα⟩ := DerivativeCommutators.periodized_interval_entries s n m hm K
    Cstar κstar γstar ε M hM
  have hcoeff : ∀ᵐ x ∂ν, (∀ k r, 0 ≤ α k r x ∧ α k r x ≤
      A * ((r.val + 1 : ℕ) : ℝ) ^ (-s.val - 2)) ∧
      ∀ a b, M x a b = ∑ k, ∑ r, α k r x *
        (if a ∈ cyclicIndexInterval m k (r.val + 1) then 1 else 0) *
        (if b ∈ cyclicIndexInterval m k (r.val + 1) then 1 else 0) :=
    hα.mono (fun _ hx => ⟨fun k r => ⟨(hx.1 k r).1, (hx.1 k r).2.1⟩, hx.2⟩)
  have hmatrix' := hmatrix ν m hm i₀ η A hη hη' hA α M hcoeff v hE
  have hraw : (∑ i, w i * Q.2 (u i) (u i)) ≤
      (β * a)⁻¹ * ‖χ.val‖ ^ 2 + (m : ℝ) * ‖lam‖ * Xρ γ +
      β * (B * A * η ^ (3 - s.val) * Xρ γ * Xρ (3 / 2 - s.val) +
        D * A * η⁻¹ * Real.sqrt (Real.log (2 * (m : ℝ))) * Xρ γ *
          Real.sqrt (∫ x, V x ^ 2 ∂ν)) := by
    have h := mul_le_mul_of_nonneg_left hmatrix' hβ.le
    linarith
  have hinv : (β * a)⁻¹ ≤ βlo⁻¹ * Cstar * (n : ℝ) ^ (κstar * ε) := by
    have hn0 : 0 < (n : ℝ) := by positivity
    have he : (β * a)⁻¹ = β⁻¹ * Cstar * (n : ℝ) ^ (κstar * ε) := by
      dsimp [a]
      rw [mul_inv_rev, mul_inv_rev, inv_inv, ← Real.rpow_neg hn0.le]
      rw [neg_mul, neg_neg]
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (inv_anti₀ hβlo hβloβ) hCstar0.le) (by positivity)
  apply absorb_internal hB hD hCstar hβlo hβhi hβloβ hββhi hP hinv
    (Real.sqrt_nonneg _) (by positivity) (by positivity) (by positivity)
  convert hraw using 1
  dsimp only [A]
  ring


/-- The canonical normal multiplier is in L² for a bounded
measurable matrix, including scalar probability spaces of dimension zero. -/
theorem normal_multiplier_memLp (N : ℕ+) (Q : ScalarFormData ν)
    (M : X → Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hMb : ∃ B : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ B)
    (f : Fin (N : ℕ) → Lp ℝ 2 ν) (u : Fin (N : ℕ) → Q.1) :
    MemLp (gapMultiplierField N Q M f u) 2 ν := by
  obtain ⟨B, hB⟩ := hMb
  have hc (i j : Fin (N : ℕ)) : MemLp (fun x => M x i j * (u j).val x) 2 ν := by
    have hmul : ∀ᵐ x ∂ν, ‖M x i j * (u j).val x‖ ≤ B * ‖(u j).val x‖ := by
      filter_upwards [hB] with x hx
      simpa only [norm_mul, Real.norm_eq_abs] using
        mul_le_mul_of_nonneg_right (hx i j) (abs_nonneg ((u j).val x))
    exact (Lp.memLp (u j).val).of_le_mul
      ((hMm i j).aestronglyMeasurable.mul (Lp.aestronglyMeasurable (u j).val)) hmul
  exact ((memLp_finsetSum Finset.univ (fun i _ =>
    memLp_finsetSum Finset.univ (fun j _ => hc i j))).sub
      (memLp_finsetSum Finset.univ (fun i _ => Lp.memLp (f i)))).const_mul (N : ℝ)⁻¹

/-- The constrained equation for a bounded matrix restores the full weak
equation with its multiplier. L² membership of that multiplier
is a conclusion, so projected-source users need no multiplier regularity premise. -/
theorem restore_multiplier (N : ℕ+) (Q : ScalarFormData ν)
    (M : X → Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hMb : ∃ B : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ B)
    (hSymm : ∀ᵐ x ∂ν, ∀ i j, M x i j = M x j i)
    (f : Fin (N : ℕ) → Lp ℝ 2 ν) (u : Fin (N : ℕ) → Q.1)
    (hu : WeightedWeakSolution Q M (zeroSumComponents (Fin (N : ℕ))) f u) :
    ∃ lam : Lp ℝ 2 ν, (∀ᵐ x ∂ν, lam x = gapMultiplierField N Q M f u x) ∧
      WeightedWeakSolution Q M ⊤ (fun i => f i + lam) u := by
  have hm := normal_multiplier_memLp N Q M hMm hMb f u
  let lam := hm.toLp (gapMultiplierField N Q M f u)
  have hlam : ∀ᵐ x ∂ν, lam x = gapMultiplierField N Q M f u x := hm.coeFn_toLp
  refine ⟨lam, hlam, ⟨Eventually.of_forall (fun _ => Submodule.mem_top), hu.1.2⟩, ?_⟩
  intro k _
  let p := ConstrainedNormalMultiplier.projectTuple N Q k
  have hp : WeightedFormDomain Q M (zeroSumComponents (Fin (N : ℕ))) p :=
    (BoundedMatrixForms.domain_iff Q M hMm hMb _ _).mpr
      (ConstrainedNormalMultiplier.projectTuple_zeroSum N Q k)
  obtain ⟨hpi, heq⟩ := hu.2 p hp
  have hki := BoundedMatrixForms.integrable_pair M hMm hMb
    (fun i => (u i).val) (fun i => (k i).val)
  have hvk := ConstrainedNormalMultiplier.source_pair_integral N f (fun i => (k i).val)
  have hvp := ConstrainedNormalMultiplier.source_pair_integral N f (fun i => (p i).val)
  let A := matrixFieldPair M (fun i => (u i).val) (fun i => (k i).val)
  let Ap := matrixFieldPair M (fun i => (u i).val) (fun i => (p i).val)
  let F := fun x => ∑ i, f i x * (k i).val x
  let Fp := fun x => ∑ i, f i x * (p i).val x
  let L := fun x => lam x * ∑ i, (k i).val x
  have hLi : Integrable L ν := by
    exact (Lp.memLp lam).integrable_mul
      (memLp_finsetSum Finset.univ (fun i _ => Lp.memLp (k i).val))
  have hn : (fun x => A x - F x) =ᵐ[ν] fun x => (Ap x - Fp x) + L x := by
    filter_upwards [hSymm, ConstrainedNormalMultiplier.projectTuple_ae N Q k, hlam] with x hx hy hz
    have hi := ConstrainedNormalMultiplier.normal_projection_identity N (M x) hx
      (fun i => (u i).val x) (fun i => f i x) (fun i => (k i).val x)
    simpa only [A, Ap, F, Fp, L, matrixFieldPair, p, hy, hz, gapMultiplierField] using hi
  have he : (∫ x, A x ∂ν) - (∫ x, F x ∂ν) =
      ((∫ x, Ap x ∂ν) - (∫ x, Fp x ∂ν)) + ∫ x, L x ∂ν := by
    have hsub : Integrable (fun x => Ap x - Fp x) ν := hpi.sub hvp.1
    rw [← integral_sub hki hvk.1, integral_congr_ae hn,
      integral_add hsub hLi, integral_sub hpi hvp.1]
  rw [ConstrainedNormalMultiplier.diffusion_projectTuple N Q u k hu.1.1, hvp.2] at heq
  have hl : (∫ x, L x ∂ν) = ∑ i, inner ℝ lam (k i).val := by
    simp only [L, Finset.mul_sum]
    have hint (i : Fin (N : ℕ)) : Integrable (fun x => lam x * (k i).val x) ν :=
      (Lp.memLp lam).integrable_mul (Lp.memLp (k i).val)
    rw [integral_finsetSum _ (fun i _ => hint i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [L2.inner_def]
    simp only [Real.inner_apply, mul_comm]
  refine ⟨hki, ?_⟩
  simp only [inner_add_left, Finset.sum_add_distrib]
  rw [← hvk.2] at he
  rw [hl] at he
  linarith only [he, heq]


/-- See Lemma 5.11 of the paper, projected-source form. A constrained point-source
solution has the canonical L² multiplier and satisfies the weighted derivative
estimate for every retention parameter. The squared gradient norm is evaluated
in the scalar form. The fractional mixed norm is proved finite. -/
theorem diff (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (γ : ℝ) (hγ : 1 / 2 ≤ γ) (κstar γstar : ℝ) (hκstar : 0 < κstar) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (Cstar : ℝ), 1 ≤ Cstar →
    ∀ (βlo : ℝ), 0 < βlo → ∀ (βhi : ℝ), βlo ≤ βhi →
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ), 0 < ε →
    ∀ {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
      (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q →
    ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ)) (K : ℕ)
      (M : X → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ),
    PeriodizedMatrixBounds (ν := ν) s n m hm K Cstar κstar γstar ε M →
    ∀ (β : ℝ), βlo ≤ β → β ≤ βhi →
    ∀ (χ : Q.1) (i₀ : Fin (m : ℕ)) (u : Fin (m : ℕ) → Q.1),
    WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents (Fin (m : ℕ)))
      (fun i => if i = i₀ then χ.val else 0) u →
    let t := γ / 2 + 1 / 4
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    let p := (1 - s.val / 2)⁻¹
    let V := fun x => (∑ i, |(rieszMatrix sh m hm *ᵥ
      (fun j => (u j).val x)) i| ^ p) ^ (1 / p)
    let Xρ := fun ρ => Real.sqrt (∑ i, (weightRadius m i i₀ ^ ρ * ‖(u i).val‖) ^ 2)
    ∃ lam : Lp ℝ 2 ν,
      (∀ᵐ x ∂ν, lam x = gapMultiplierField m Q (fun x => β • M x)
        (fun i => if i = i₀ then χ.val else 0) u x) ∧
      WeightedWeakSolution Q (fun x => β • M x) ⊤
        (fun i => (if i = i₀ then χ.val else 0) + lam) u ∧
      Integrable (fun x => V x ^ 2) ν ∧
      ∀ (η : ℝ), 0 < η → η < 1 / 4 →
        (∑ i, weightRadius m i i₀ ^ (2 * t) * Q.2 (u i) (u i)) ≤
          C * (n : ℝ) ^ (κ * ε) * (‖χ.val‖ ^ 2 + Xρ γ *
            (η ^ (3 - s.val) * Xρ (3 / 2 - s.val) +
              η⁻¹ * Real.sqrt (Real.log (2 * (m : ℝ))) *
                Real.sqrt (∫ x, V x ^ 2 ∂ν) + (m : ℝ) * ‖lam‖)) := by
  obtain ⟨κ, hκ, hdiff⟩ := diff_with_multiplier hz s γ hγ κstar γstar hκstar
  refine ⟨κ, hκ, fun Cstar hCstar βlo hβlo βhi hβhi => ?_⟩
  obtain ⟨C, hC, hbound⟩ := hdiff Cstar hCstar βlo hβlo βhi hβhi
  refine ⟨C, hC, ?_⟩
  intro ε hε X _ ν _ Q hQ n m hm K M hM β hβloβ hββhi χ i₀ u hu t sh p V Xρ
  have hsym : ∀ᵐ x ∂ν, ∀ i j, (β • M x) i j = (β • M x) j i := by
    filter_upwards [hM.2.1] with x hx
    intro i j
    simp only [Matrix.smul_apply, smul_eq_mul, hx.1 i j]
  obtain ⟨lam, hlam, hfull⟩ := restore_multiplier m Q (fun x => β • M x)
    (SchurRestriction.periodized_scaled_measurable β hM)
    (SchurRestriction.periodized_scaled_bounded β hM) hsym _ u hu
  exact ⟨lam, hlam, hfull,
    hbound ε hε ν Q hQ n m hm K M hM β hβloβ hββhi χ i₀ u lam hfull hu.1.1⟩

end Riesz2.DerivativeControl
