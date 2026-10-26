/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.PhysicalComparisonPart3
public import Riesz2.ToMathlib.BoundedMatrixModes

/-!
# L² realization of the physical comparison

The actual matrix discrepancy in Subsection 4.5 acts on the same
scalar form as the internal auxiliary matrix, including after a measurable
restriction to a fixed fibre.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators

namespace Riesz2.DecayShort.PhysicalComparison

private theorem internal_l2_norm_sq {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ν : Measure α} (f : Lp E 2 ν) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  exact integral_congr_ae (ae_of_all _ fun x => real_inner_self_eq_norm_sq (f x))

private theorem internal_tuple_norm_sq {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {n : ℕ} (f : Fin n → Lp ℝ 2 ν) :
    ‖WithLp.toLp 2 f‖ ^ 2 = ∫ x, ∑ i, f i x ^ 2 ∂ν := by
  rw [PiLp.norm_sq_eq_of_L2, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [internal_l2_norm_sq]
    simp only [Real.norm_eq_abs, sq_abs]
  · intro i _
    exact (Lp.memLp (f i)).integrable_sq

private theorem internal_magnitude {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {n : ℕ} (f : Fin n → Lp ℝ 2 ν) :
    ∃ g : Lp ℝ 2 ν,
      (∀ᵐ x ∂ν, g x = ‖(WithLp.toLp 2 (fun i => f i x) : EuclideanSpace ℝ (Fin n))‖) ∧
      ‖g‖ = ‖WithLp.toLp 2 f‖ := by
  let F := fun x => (WithLp.toLp 2 (fun i => f i x) : EuclideanSpace ℝ (Fin n))
  have hm := (VectorRadial.memLp_values f).norm
  refine ⟨hm.toLp _, hm.coeFn_toLp, ?_⟩
  have he : ‖hm.toLp (fun x => ‖F x‖)‖ ^ 2 = ‖WithLp.toLp 2 f‖ ^ 2 := by
    rw [internal_l2_norm_sq, internal_tuple_norm_sq]
    apply integral_congr_ae
    filter_upwards [hm.coeFn_toLp] with x hx
    rw [hx, Real.norm_eq_abs, sq_abs, EuclideanSpace.real_norm_sq_eq]
  nlinarith [norm_nonneg (hm.toLp (fun x => ‖F x‖)), norm_nonneg (WithLp.toLp 2 f)]

private theorem internal_tuple_dominated {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {n : ℕ} (f : Fin n → Lp ℝ 2 ν) (g : Lp ℝ 2 ν)
    (hg : ∀ᵐ x ∂ν, ‖(WithLp.toLp 2 (fun i => f i x) : EuclideanSpace ℝ (Fin n))‖ ≤ g x) :
    ‖WithLp.toLp 2 f‖ ≤ ‖g‖ := by
  obtain ⟨F,hF,hn⟩ := internal_magnitude f
  rw [← hn]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [hF,hg] with x hx hle
  rw [hx, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact hle.trans (le_abs_self _)

/-- Internal L² realization of a matrix action used in Subsection 4.5.
The envelope is only an internal domination interface. The physical residual
below constructs and bounds it from the coefficients. -/
theorem internal_action_l2 {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {n : ℕ} (M : α → Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, Measurable (fun x => M x i j))
    (u : Fin n → Lp ℝ 2 ν) (G : Lp ℝ 2 ν)
    (hG : ∀ᵐ x ∂ν,
      ‖(WithLp.toLp 2 (fun i => ∑ j, M x i j * u j x) : EuclideanSpace ℝ (Fin n))‖ ≤ G x) :
    ∃ g : Fin n → Lp ℝ 2 ν,
      (∀ᵐ x ∂ν, ∀ i, g i x = ∑ j, M x i j * u j x) ∧
      ‖WithLp.toLp 2 g‖ ≤ ‖G‖ := by
  have hm (i) : MemLp (fun x => ∑ j, M x i j * u j x) 2 ν := by
    apply (Lp.memLp G).of_le_mul
      (Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
        (hM i j).aestronglyMeasurable.mul (Lp.aestronglyMeasurable (u j)))
      (c := 1)
    filter_upwards [hG] with x hx
    simpa only [one_mul, Real.norm_eq_abs, Pi.mul_apply] using
      (PiLp.norm_apply_le (WithLp.toLp 2 (fun i => ∑ j, M x i j * u j x)) i).trans
        (hx.trans (le_abs_self _))
  let g := fun i => (hm i).toLp _
  have hg : ∀ᵐ x ∂ν, ∀ i, g i x = ∑ j, M x i j * u j x :=
    ae_all_iff.mpr fun i => (hm i).coeFn_toLp
  refine ⟨g,hg,internal_tuple_dominated g G ?_⟩
  filter_upwards [hg,hG] with x hx hle
  simpa only [hx] using hle

private theorem internal_absolute {α : Type*} [MeasurableSpace α]
    {ν : Measure α} (f : Lp ℝ 2 ν) :
    ∃ g : Lp ℝ 2 ν, (∀ᵐ x ∂ν, g x = |f x|) ∧ ‖g‖ = ‖f‖ := by
  have hm := (Lp.memLp f).norm
  refine ⟨hm.toLp _,hm.coeFn_toLp,?_⟩
  rw [Lp.norm_toLp, eLpNorm_norm f (Lp.aestronglyMeasurable f), ← Lp.norm_def]

/-- Internal Minkowski and exact boundary mass identities for the actual
component contractions in Subsection 4.5. -/
theorem internal_l2_contractions {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {n : ℕ} (s : ℝ) (u : Fin n → Lp ℝ 2 ν) :
    ∃ Z ZW E : Lp ℝ 2 ν,
      (∀ᵐ x ∂ν,
        Z x = ∑ i, |u i x| ∧
        ZW x = ∑ i, ConditionalScores.weight s i * |u i x| ∧
        E x = Real.sqrt (∑ i, if (ConditionalScores.boundaryDistance i : ℝ) < (n : ℝ) / 8
          then u i x ^ 2 else 0)) ∧
      ‖Z‖ ≤ ∑ i, ‖u i‖ ∧
      ‖ZW‖ ≤ ∑ i, ConditionalScores.weight s i * ‖u i‖ ∧
      ‖E‖ = Real.sqrt (∑ i, if (ConditionalScores.boundaryDistance i : ℝ) < (n : ℝ) / 8
        then ‖u i‖ ^ 2 else 0) := by
  classical
  choose a ha han using fun i => internal_absolute (u i)
  let v := fun i => if (ConditionalScores.boundaryDistance i : ℝ) < (n : ℝ) / 8 then u i else 0
  obtain ⟨E,hE,hnE⟩ := internal_magnitude v
  refine ⟨∑ i, a i, ∑ i, ConditionalScores.weight s i • a i, E, ?_, ?_, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ a,
      BoundedMatrixModes.coe_sum_smul (ConditionalScores.weight s) a,
      ae_all_iff.mpr ha, hE,
      ae_all_iff.mpr (fun i : Fin n => show ∀ᵐ x ∂ν,
        v i x = if (ConditionalScores.boundaryDistance i : ℝ) < (n : ℝ) / 8 then u i x else 0 from by
          dsimp only [v]; split_ifs
          · exact ae_of_all _ fun _ => rfl
          · exact Lp.coeFn_zero _ _ _)]
      with x hZ hZW hx he hv
    refine ⟨hZ.trans (by simp only [hx]),hZW.trans (by simp only [hx]),?_⟩
    rw [he, EuclideanSpace.norm_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    change ‖v i x‖ ^ 2 = _
    rw [hv i]
    split_ifs <;> simp only [Real.norm_eq_abs, sq_abs, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, norm_zero]
  · exact (norm_sum_le _ _).trans (le_of_eq (by simp only [han]))
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (ConditionalScores.weight_pos s i), han i]
  · rw [hnE, ← Real.sqrt_sq (norm_nonneg (WithLp.toLp 2 v)), PiLp.norm_sq_eq_of_L2]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [v]
    split_ifs <;> simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]

private theorem internal_envelope3 {α : Type*} [MeasurableSpace α] {ν : Measure α}
    (Z W E : Lp ℝ 2 ν) (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ∃ G : Lp ℝ 2 ν,
      (∀ᵐ x ∂ν, G x = a * Z x + b * W x + c * E x) ∧
      ‖G‖ ≤ a * ‖Z‖ + b * ‖W‖ + c * ‖E‖ := by
  refine ⟨a • Z + b • W + c • E, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_add (a • Z + b • W) (c • E),
      Lp.coeFn_add (a • Z) (b • W), Lp.coeFn_smul a Z,
      Lp.coeFn_smul b W, Lp.coeFn_smul c E] with x h₁ h₂ h₃ h₄ h₅
    simp only [h₁,h₂,h₃,h₄,h₅,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  · calc
      _ ≤ (‖a • Z‖ + ‖b • W‖) + ‖c • E‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = _ := by simp only [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg ha,abs_of_nonneg hb,abs_of_nonneg hc]

set_option backward.isDefEq.respectTransparency false in
/-- The full physical discrepancy in L², supporting Subsection 4.5.
The residual is the matrix product. The three contractions are
component L² norms, so this statement applies on every measurable fibre. -/
theorem frozen_difference_l2_norm (p : Parameters) (hs : 1 < p.val.2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ+) (m : ℕ),
      4 ≤ (n : ℕ) + m + 1 → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (θ : PhysicalCutoff) (h : ℝ), 0 < h → ∀ (b : Bool) (D : ℝ), 0 ≤ D →
      ∀ (α : Type*) [MeasurableSpace α]
      (τ : α → AffineSimplex.chartDomain n ((n + m : ℕ) + 1)), Measurable τ →
      ∀ (ν : Measure α) (u : Fin (n : ℕ) → Lp ℝ 2 ν),
      let M := fun x => frozenPhysicalMatrix p n m θ h b D (τ x) -
        frozenInternalMatrix p n m θ h b D (τ x)
      let N : ℝ := ((n : ℕ) + m + 1 : ℕ)
      let a := N ^ (-(1 / 2 : ℝ))
      let S := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-p.val.2)
      let W := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(2 * p.val.2 - 1))
      let K := 2 * (8 : ℝ) ^ (p.val.2 + 1) + 1
      let cZ := K * D * (n : ℝ) ^ (-p.val.2) * Real.sqrt n +
        (3 * D / N + p.val.1 * C * D * N⁻¹) * Real.sqrt n +
        p.val.1 * C * D * a * Real.sqrt W
      let cW := p.val.1 * C * D * (a * Real.sqrt n + Real.sqrt W)
      ∃ g : Fin (n : ℕ) → Lp ℝ 2 ν,
        (∀ᵐ x ∂ν, ∀ i, g i x = ∑ j, M x i j * u j x) ∧
        ‖WithLp.toLp 2 g‖ ≤ cZ * (∑ i, ‖u i‖) +
          cW * (∑ i, ConditionalScores.weight p.val.2 i * ‖u i‖) +
          D * S * Real.sqrt (∑ i, if
            (ConditionalScores.boundaryDistance i : ℝ) < (n : ℝ) / 8 then ‖u i‖ ^ 2 else 0) := by
  classical
  obtain ⟨C,hC,hact⟩ := frozen_difference_action_norm p hs
  refine ⟨C,hC,?_⟩
  intro n m hN hhalf θ h hh b D hD α _ τ hτ ν u M N a S W K cZ cW
  have hβ := p.property.1.le
  have hN0 : 0 < N := by dsimp only [N]; positivity
  have hS : 0 ≤ S := mul_nonneg (by norm_num) (tsum_nonneg fun _ => by positivity)
  have hcZ : 0 ≤ cZ := by dsimp only [cZ,K,a]; positivity
  have hcW : 0 ≤ cW := by dsimp only [cW,a]; positivity
  obtain ⟨Z,ZW,E,hvals,hZn,hZWn,hEn⟩ := internal_l2_contractions p.val.2 u
  obtain ⟨G,hG,hGn⟩ := internal_envelope3 Z ZW E cZ cW (D*S) hcZ hcW (mul_nonneg hD hS)
  obtain ⟨hmH,hmM,_,_⟩ := frozenMatrices_measurable_symmetric p hs n m θ h hh b D
  have hm (i j) : Measurable (fun x => M x i j) := ((hmH i j).comp hτ).sub ((hmM i j).comp hτ)
  have hb : ∀ᵐ x ∂ν,
      ‖(WithLp.toLp 2 (fun i => ∑ j, M x i j * u j x) : EuclideanSpace ℝ (Fin (n : ℕ)))‖ ≤ G x := by
    filter_upwards [hvals,hG] with x hx hg
    rw [hg,hx.1,hx.2.1,hx.2.2]
    apply (hact n m hN hhalf θ h b D hD (τ x) (fun j => u j x)).trans_eq
    dsimp only [cZ,cW]
    ring
  obtain ⟨g,hg,hgn⟩ := internal_action_l2 M hm u G hb
  refine ⟨g,hg,hgn.trans (hGn.trans ?_)⟩
  rw [hEn]
  exact add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hZn hcZ) (mul_le_mul_of_nonneg_left hZWn hcW)) le_rfl

/-- Size arithmetic for the component-sum estimate in Subsection 4.5.
All powers have positive bases. -/
theorem comparison_size_bounds (s : ℝ) (hs : 1 < s) (n : ℕ+) (N : ℝ)
    (hnN : (n : ℝ) ≤ N) :
    (n : ℝ) ^ (-s) * Real.sqrt n = (n : ℝ) ^ (-(s - 1 / 2)) ∧
    Real.sqrt n / N ≤ N ^ (-(1 / 2 : ℝ)) ∧
    N ^ (-(1 / 2 : ℝ)) * Real.sqrt n ≤ 1 ∧
    Real.sqrt n * ((n : ℝ) ^ (-(s - 1 / 2)) + N ^ (-(1 / 2 : ℝ))) ≤ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hN : 0 < N := hn0.trans_le hnN
  have ha : N ^ (-(1 / 2 : ℝ)) = (Real.sqrt N)⁻¹ := by
    rw [Real.rpow_neg hN.le,Real.sqrt_eq_rpow]
  have hsqN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hsqn := Real.sqrt_le_sqrt hnN
  have h₁ : Real.sqrt n / N ≤ N ^ (-(1 / 2 : ℝ)) := by
    rw [ha, div_le_iff₀ hN]
    calc
      _ ≤ Real.sqrt N := hsqn
      _ = Real.sqrt N * ((Real.sqrt N)⁻¹ * Real.sqrt N) := by
        rw [inv_mul_cancel₀ hsqN.ne',mul_one]
      _ = (Real.sqrt N)⁻¹ * (Real.sqrt N)^2 := by ring
      _ = (Real.sqrt N)⁻¹ * N := by rw [Real.sq_sqrt hN.le]
  have h₂ : N ^ (-(1 / 2 : ℝ)) * Real.sqrt n ≤ 1 := by
    rw [ha, ← div_eq_inv_mul, div_le_one hsqN]
    exact hsqn
  refine ⟨?_,h₁,h₂,?_⟩
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn0]
    congr 1
    ring
  · have hp : Real.sqrt n * (n : ℝ) ^ (-(s - 1 / 2)) = (n : ℝ) ^ (1-s) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn0]
      congr 1
      ring
    have hle : (n : ℝ) ^ (1-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
    rw [mul_add,hp,mul_comm (Real.sqrt (n : ℝ))]
    linarith

/-- Internal boundary contraction of the actual component-decay envelope
in Subsection 4.5. -/
theorem internal_boundary_contraction {n : ℕ} (hn : 0 < n) (s : ℝ) (hs : 0 ≤ s)
    (i₀ : Fin n) (hlo : (n : ℝ)/4 ≤ (i₀.val : ℝ)+1)
    (hhi : (i₀.val : ℝ)+1 ≤ 3*(n : ℝ)/4) (V : ℝ) (hV : 0 ≤ V)
    (f : Fin n → ℝ) (hf0 : ∀ i, 0 ≤ f i)
    (hf : ∀ i, f i ≤ V * (1 + |(i.val : ℝ) - (i₀.val : ℝ)|) ^ (-s)) :
    Real.sqrt (∑ i, if (ConditionalScores.boundaryDistance i : ℝ) < (n : ℝ)/8
      then f i ^ 2 else 0) ≤ V * (8 : ℝ) ^ s * (n : ℝ) ^ (-(s-1/2)) := by
  classical
  calc
    _ ≤ Real.sqrt (∑ i, if (ConditionalScores.boundaryDistance i : ℝ) < (n : ℝ)/8
        then (V * (1 + |(i.val : ℝ) - (i₀.val : ℝ)|) ^ (-s)) ^ 2 else 0) := by
      apply Real.sqrt_le_sqrt
      apply Finset.sum_le_sum
      intro i _
      split_ifs
      · exact pow_le_pow_left₀ (hf0 i) (hf i) 2
      · exact le_rfl
    _ = V * Real.sqrt (∑ i, if (ConditionalScores.boundaryDistance i : ℝ) < (n : ℝ)/8
        then ((1 + |(i.val : ℝ) - (i₀.val : ℝ)|) ^ (-s)) ^ 2 else 0) := by
      have he : (∑ i : Fin n, if (ConditionalScores.boundaryDistance i : ℝ) < (n : ℝ)/8
          then (V * (1 + |(i.val : ℝ) - (i₀.val : ℝ)|) ^ (-s)) ^ 2 else 0) =
          V^2 * ∑ i : Fin n, if (ConditionalScores.boundaryDistance i : ℝ) < (n : ℝ)/8
          then ((1 + |(i.val : ℝ) - (i₀.val : ℝ)|) ^ (-s)) ^ 2 else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> simp only [mul_pow,mul_zero]
      rw [he,Real.sqrt_mul (sq_nonneg V),Real.sqrt_sq hV]
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (boundary_source_profile_square_sum hn s hs i₀ hlo hhi) hV

set_option backward.isDefEq.respectTransparency false in
/-- Internal contraction of the physical residual against a component
profile, supporting Subsection 4.5. The envelope hypothesis is
internal. The following theorem obtains it from the actual weak solution. -/
theorem internal_residual_profile (p : Parameters) (hs : 1 < p.val.2) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (n : ℕ+) (m : ℕ),
      4 ≤ (n : ℕ) + m + 1 → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (θ : PhysicalCutoff) (h : ℝ), 0 < h → ∀ (b : Bool) (D : ℝ), 0 ≤ D →
      ∀ (α : Type*) [MeasurableSpace α]
      (τ : α → AffineSimplex.chartDomain n ((n + m : ℕ) + 1)), Measurable τ →
      ∀ (ν : Measure α) (i₀ : Fin (n : ℕ)),
      (n : ℝ)/4 ≤ (i₀.val : ℝ)+1 → (i₀.val : ℝ)+1 ≤ 3*(n : ℝ)/4 →
      ∀ (V : ℝ), 0 ≤ V → ∀ u : Fin (n : ℕ) → Lp ℝ 2 ν,
      (∀ i, ‖u i‖ ≤ V * (1 + |(i.val : ℝ) - (i₀.val : ℝ)|) ^ (-p.val.2)) →
      ∃ g : Fin (n : ℕ) → Lp ℝ 2 ν,
        (∀ᵐ x ∂ν, ∀ i, g i x = ∑ j,
          (frozenPhysicalMatrix p n m θ h b D (τ x) -
            frozenInternalMatrix p n m θ h b D (τ x)) i j * u j x) ∧
        ‖WithLp.toLp 2 g‖ ≤ C * D * V *
          ((n : ℝ) ^ (-(p.val.2 - 1/2)) +
            (((n : ℕ) + m + 1 : ℕ) : ℝ) ^ (-(1/2 : ℝ))) := by
  classical
  obtain ⟨C,hC,hbound⟩ := frozen_difference_l2_norm p hs
  let S := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-p.val.2)
  let W := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(2 * p.val.2 - 1))
  let K := 2 * (8 : ℝ) ^ (p.val.2 + 1) + 1
  let B := p.val.1*C
  let L := (8 : ℝ) ^ (p.val.2 - 1/2)*S + (8 : ℝ) ^ p.val.2*Real.sqrt W
  let J := 1+K+3+B+B*Real.sqrt W
  let Cr := 1 + J*S+B*(1+Real.sqrt W)*L+S*(8 : ℝ)^p.val.2
  have hS : 0 ≤ S := mul_nonneg (by norm_num) (tsum_nonneg fun _ => by positivity)
  have hW : 0 ≤ W := mul_nonneg (by norm_num) (tsum_nonneg fun _ => by positivity)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hB : 0 ≤ B := mul_nonneg p.property.1.le hC.le
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  have hCr : 1 ≤ Cr := by
    have h₁ := mul_nonneg hJ hS
    have h₂ : 0 ≤ B*(1+Real.sqrt W)*L := by positivity
    have h₃ : 0 ≤ S*(8 : ℝ)^p.val.2 := by positivity
    dsimp only [Cr]
    linarith
  refine ⟨Cr,hCr,?_⟩
  intro n m hN hhalf θ h hh b D hD α _ τ hτ ν i₀ hlo hhi V hV u hu
  let N : ℝ := ((n : ℕ)+m+1 : ℕ)
  let a := N ^ (-(1/2 : ℝ))
  let l := (n : ℝ)^(-(p.val.2-1/2))
  let cZ := K*D*(n : ℝ)^(-p.val.2)*Real.sqrt n +
    (3*D/N+B*D*N⁻¹)*Real.sqrt n+B*D*a*Real.sqrt W
  let cW := B*D*(a*Real.sqrt n+Real.sqrt W)
  have hnN : (n : ℝ) ≤ N := by dsimp only [N]; norm_cast; omega
  obtain ⟨hp,hNrate,hNr,hsize⟩ := comparison_size_bounds p.val.2 hs n N hnN
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hl : 0 ≤ l := by dsimp only [l]; positivity
  have hr : 0 ≤ l+a := add_nonneg hl ha
  have hcZ : 0 ≤ cZ := by dsimp only [cZ]; positivity
  have hcW : 0 ≤ cW := by dsimp only [cW]; positivity
  have hzcoeff : cZ ≤ D*J*(l+a) := by
    have hmid := mul_le_mul_of_nonneg_left hNrate (mul_nonneg (by linarith : 0 ≤ 3+B) hD)
    have heq : cZ = K*D*l+(3+B)*D*(Real.sqrt n/N)+B*D*a*Real.sqrt W := by
      dsimp only [cZ,l]
      rw [← hp]
      simp only [div_eq_mul_inv]
      ring
    rw [heq]
    calc
      _ ≤ K*D*l+(3+B)*D*a+B*D*a*Real.sqrt W := by linarith only [hmid]
      _ = D*(K*l+(3+B+B*Real.sqrt W)*a) := by ring
      _ ≤ D*(J*l+J*a) := by
        apply mul_le_mul_of_nonneg_left _ hD
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right (by dsimp only [J]; nlinarith [mul_nonneg hB (Real.sqrt_nonneg W)] : K ≤ J) hl
        · exact mul_le_mul_of_nonneg_right (by dsimp only [J]; linarith : 3+B+B*Real.sqrt W ≤ J) ha
      _ = _ := by ring
  have hwcoeff : cW ≤ B*D*(1+Real.sqrt W) := by
    apply mul_le_mul_of_nonneg_left (add_le_add hNr le_rfl) (mul_nonneg hB hD)
  have hc := internal_profile_contractions p.val.2 hs n.pos i₀ hlo hhi V hV
    (fun i => ‖u i‖) hu
  have he := internal_boundary_contraction n.pos p.val.2 (by linarith) i₀ hlo hhi V hV
    (fun i => ‖u i‖) (fun i => norm_nonneg _) hu
  change (∑ i, ‖u i‖) ≤ V*S ∧
    (∑ i, ConditionalScores.weight p.val.2 i*‖u i‖) ≤ V*(L*l) at hc
  change _ ≤ V*(8 : ℝ)^p.val.2*l at he
  obtain ⟨g,hg,hgn⟩ := hbound n m hN hhalf θ h hh b D hD α τ hτ ν u
  change ‖WithLp.toLp 2 g‖ ≤ cZ*(∑ i, ‖u i‖) +
    cW*(∑ i, ConditionalScores.weight p.val.2 i*‖u i‖) + D*S*_ at hgn
  refine ⟨g,hg,hgn.trans ?_⟩
  calc
    _ ≤ cZ*(V*S)+cW*(V*(L*l))+D*S*(V*(8 : ℝ)^p.val.2*l) := by
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hc.1 hcZ)
        (mul_le_mul_of_nonneg_left hc.2 hcW))
        (mul_le_mul_of_nonneg_left he (mul_nonneg hD hS))
    _ ≤ (D*J*(l+a))*(V*S)+(B*D*(1+Real.sqrt W))*(V*(L*(l+a)))+
        D*S*(V*(8 : ℝ)^p.val.2*(l+a)) := by
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_right hzcoeff (mul_nonneg hV hS)
        · exact mul_le_mul hwcoeff
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right ha) hL) hV)
            (by positivity) (by positivity)
      · exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right ha) (by positivity))
          (mul_nonneg hD hS)
    _ = (J*S+B*(1+Real.sqrt W)*L+S*(8 : ℝ)^p.val.2)*D*V*(l+a) := by ring
    _ ≤ Cr*D*V*(l+a) := by
      apply mul_le_mul_of_nonneg_right _ hr
      apply mul_le_mul_of_nonneg_right _ hV
      apply mul_le_mul_of_nonneg_right _ hD
      dsimp only [Cr]
      linarith

set_option backward.isDefEq.respectTransparency false in
/-- The actual point-source residual estimate in Subsection 4.5.
Its size loss is quantified before the
cutoff, truncation prefactor, dimensions, scalar form and fibre restriction. -/
theorem auxiliary_residual_bound (p : Parameters) (hs : 1 < p.val.2)
    (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ (θ : PhysicalCutoff) (h : ℝ), 0 < h →
      ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, 1 ≤ C ∧ ∀ (n : ℕ+) (m : ℕ),
        4 ≤ (n : ℕ)+m+1 → 2*(n : ℕ) ≤ (n : ℕ)+m+1 → ∀ (b : Bool)
        (α : Type*) [MeasurableSpace α]
        (τ : α → AffineSimplex.chartDomain n ((n+m : ℕ)+1)), Measurable τ →
        ∀ (ν : Measure α) [IsProbabilityMeasure ν] (Q : ScalarFormData ν),
        IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
        ∀ (i₀ : Fin (n : ℕ)), (n : ℝ)/4 ≤ (i₀.val : ℝ)+1 →
          (i₀.val : ℝ)+1 ≤ 3*(n : ℝ)/4 → ∀ (χ : Lp ℝ 2 ν)
        (v : Fin (n : ℕ) → Q.1),
        WeightedWeakSolution Q (fun x => p.val.1 • frozenInternalMatrix p n m θ h b
          (A*(n : ℝ)^(κ*h)) (τ x)) ⊤ (fun i => if i=i₀ then χ else 0) v →
        ∃ g : Fin (n : ℕ) → Lp ℝ 2 ν,
          (∀ᵐ x ∂ν, ∀ i, g i x = ∑ j,
            (frozenPhysicalMatrix p n m θ h b (A*(n : ℝ)^(κ*h)) (τ x) -
             frozenInternalMatrix p n m θ h b (A*(n : ℝ)^(κ*h)) (τ x)) i j * (v j).val x) ∧
          ‖WithLp.toLp 2 g‖ ≤ C*(n : ℝ)^(r*h)*
            ((n : ℝ)^(-(p.val.2-1/2)) +
              (((n : ℕ)+m+1 : ℕ) : ℝ)^(-(1/2 : ℝ)))*‖χ‖ := by
  classical
  obtain ⟨Cd,hCd,hres⟩ := internal_residual_profile p hs
  obtain ⟨r,hr,hdec⟩ := internal_auxiliary_point_source_decay p hs κ hκ
  refine ⟨κ+r,add_nonneg hκ hr,?_⟩
  intro θ h hh A hA
  obtain ⟨Cv,hCv,hdec⟩ := hdec θ h hh A hA
  refine ⟨Cd*A*Cv,one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hCd hA) hCv,?_⟩
  intro n m hN hhalf b α _ τ hτ ν _ Q hQ hcons i₀ hlo hhi χ v hv
  let V := Cv*(n : ℝ)^(r*h)*‖χ‖
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hd := (hdec n m hN hhalf b α τ hτ ν Q hQ hcons i₀ χ).2 v hv
  have hp (i) : ‖(v i).val‖ ≤ V*(1+|(i.val : ℝ)-(i₀.val : ℝ)|)^(-p.val.2) :=
    (hd i).trans_eq (by dsimp only [V]; ring)
  obtain ⟨g,hg,hgn⟩ := hres n m hN hhalf θ h hh b (A*(n : ℝ)^(κ*h))
    (by positivity) α τ hτ ν i₀ hlo hhi V hV (fun i => (v i).val) hp
  refine ⟨g,hg,hgn.trans_eq ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have he : (n : ℝ)^(κ*h)*(n : ℝ)^(r*h) = (n : ℝ)^((κ+r)*h) := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  dsimp only [V]
  calc
    _ = Cd*A*Cv*((n : ℝ)^(κ*h)*(n : ℝ)^(r*h))*
        ((n : ℝ)^(-(p.val.2-1/2))+(((n : ℕ)+m+1 : ℕ) : ℝ)^(-(1/2 : ℝ)))*‖χ‖ := by ring
    _ = _ := by rw [he]

set_option backward.isDefEq.respectTransparency false in
/-- Internal subtraction of two bounded weak equations over the same
scalar form, for Subsection 4.5. The residual is identified almost
everywhere with the actual matrix difference applied to the second solution. -/
theorem internal_common_form_comparison {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {n : ℕ} (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (H M : α → Matrix (Fin n) (Fin n) ℝ)
    (hHm : ∀ i j, Measurable (fun x => H x i j))
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hHb : ∃ B : ℝ, ∀ᵐ x ∂ν, ∀ i j, |H x i j| ≤ B)
    (hMb : ∃ B : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ B)
    (hHp : ∀ᵐ x ∂ν, (H x).PosSemidef) (hMp : ∀ᵐ x ∂ν, (M x).PosSemidef)
    (a : ℝ) (ha : 0 < a)
    (hHa : ∀ᵐ x ∂ν, ∀ z : Fin n → ℝ,
      a*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*H x i j*z j)
    (f : Fin n → Lp ℝ 2 ν) (u v : Fin n → Q.1)
    (hu : WeightedWeakSolution Q H ⊤ f u) (hv : WeightedWeakSolution Q M ⊤ f v)
    (g : Fin n → Lp ℝ 2 ν)
    (hg : ∀ᵐ x ∂ν, ∀ i, g i x = ∑ j, (H x i j-M x i j)*(v j).val x) :
    ‖WithLp.toLp 2 (fun i => (u i-v i).val)‖ +
      Real.sqrt (∑ i, Q.2 (u i-v i) (u i-v i)) ≤
        2*(min 1 a)⁻¹*‖WithLp.toLp 2 g‖ := by
  classical
  let U := (MatrixEnergy.vectorEquiv Q hQ).symm u
  let V := (MatrixEnergy.vectorEquiv Q hQ).symm v
  let d := U-V
  let F := BoundedMatrixForms.form Q hQ H hHm hHb hHp
  let F₀ := BoundedMatrixForms.form Q hQ M hMm hMb hMp
  have hU := (BoundedMatrixForms.equation_iff Q hQ H hHm hHb hHp U f).mpr
    (by simpa only [U,LinearEquiv.apply_symm_apply] using hu)
  have hV := (BoundedMatrixForms.equation_iff Q hQ M hMm hMb hMp V f).mpr
    (by simpa only [V,LinearEquiv.apply_symm_apply] using hv)
  have hdiff (w : MatrixEnergy.Vector (ι := Fin n) Q hQ) :
      F V w - F₀ V w = inner ℝ (WithLp.toLp 2 g) (OperatorSchur.vectorValues Q hQ w) := by
    rw [BoundedMatrixForms.form_apply,BoundedMatrixForms.form_apply]
    simp only [PiLp.inner_apply,OperatorSchur.vectorValues_apply]
    have hIntH := BoundedMatrixForms.integrable_pair H hHm hHb
      (fun i => (MatrixEnergy.vectorEquiv Q hQ V i).val)
      (fun i => (MatrixEnergy.vectorEquiv Q hQ w i).val)
    have hIntM := BoundedMatrixForms.integrable_pair M hMm hMb
      (fun i => (MatrixEnergy.vectorEquiv Q hQ V i).val)
      (fun i => (MatrixEnergy.vectorEquiv Q hQ w i).val)
    have he : (∫ x, matrixFieldPair H (fun i => (MatrixEnergy.vectorEquiv Q hQ V i).val)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ w i).val) x ∂ν) -
        (∫ x, matrixFieldPair M (fun i => (MatrixEnergy.vectorEquiv Q hQ V i).val)
        (fun i => (MatrixEnergy.vectorEquiv Q hQ w i).val) x ∂ν) =
        ∑ i, inner ℝ (g i) (MatrixEnergy.vectorEquiv Q hQ w i).val := by
      rw [← integral_sub hIntH hIntM]
      simp_rw [L2.inner_def]
      rw [← integral_finsetSum _ (fun i _ => L2.integrable_inner (𝕜 := ℝ) _ _)]
      apply integral_congr_ae
      filter_upwards [hg,hHp,hMp] with x hx hH hM
      simp only [V,LinearEquiv.apply_symm_apply,matrixFieldPair,Real.inner_apply,hx]
      rw [← Finset.sum_sub_distrib]
      simp_rw [← Finset.sum_sub_distrib]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      have hHsym : H x j i = H x i j := by simpa using congrFun (congrFun hH.1 i) j
      have hMsym : M x j i = M x i j := by simpa using congrFun (congrFun hM.1 i) j
      rw [hHsym,hMsym]
      ring
    linarith only [he]
  have heq : F d d = -inner ℝ (WithLp.toLp 2 g) (OperatorSchur.vectorValues Q hQ d) := by
    have hu' := hU d
    have hv' := hV d
    have hd := hdiff d
    change F U d = _ at hu'
    change F₀ V d = _ at hv'
    have hdF : F d d = F U d-F V d := by
      change F (U-V) d = _
      exact congrArg (fun T : MatrixEnergy.Vector (ι := Fin n) Q hQ →L[ℝ] ℝ => T d)
        (map_sub F U V)
    rw [hdF]
    linarith only [hu',hv',hd]
  have hmass := OperatorSchur.vector_norm_sq Q hQ d
  have henergy := OperatorSchur.vectorEnergy_nonneg Q hQ d
  have hval : ‖OperatorSchur.vectorValues Q hQ d‖ ≤ ‖d‖ := by
    nlinarith [norm_nonneg d,norm_nonneg (OperatorSchur.vectorValues Q hQ d)]
  have hgrad : Real.sqrt (OperatorSchur.vectorEnergy Q hQ d d) ≤ ‖d‖ := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨norm_nonneg _,by nlinarith [sq_nonneg ‖OperatorSchur.vectorValues Q hQ d‖]⟩
  have hc := BoundedMatrixForms.form_coercive Q hQ H hHm hHb hHp a hHa d
  change min 1 a*‖d‖^2 ≤ F d d at hc
  have he : F d d ≤ ‖WithLp.toLp 2 g‖*‖d‖ := by
    rw [heq]
    apply (neg_le_abs _).trans
    apply (abs_real_inner_le_norm _ _).trans
    exact mul_le_mul_of_nonneg_left hval (norm_nonneg _)
  have hc0 : 0 < min 1 a := lt_min zero_lt_one ha
  have hn : ‖d‖ ≤ (min 1 a)⁻¹*‖WithLp.toLp 2 g‖ := by
    rw [← div_eq_inv_mul,le_div_iff₀ hc0]
    by_cases hz : ‖d‖ = 0
    · rw [hz,zero_mul]; exact norm_nonneg _
    · nlinarith [lt_of_le_of_ne (norm_nonneg d) (Ne.symm hz)]
  have ht := (add_le_add hval hgrad).trans (by linarith : ‖d‖+‖d‖ ≤ 2*((min 1 a)⁻¹*‖WithLp.toLp 2 g‖))
  have hdtuple : MatrixEnergy.vectorEquiv Q hQ d = fun i => u i-v i := by
    simp only [d,U,V,map_sub,LinearEquiv.apply_symm_apply]
    rfl
  have hdvals : OperatorSchur.vectorValues Q hQ d =
      WithLp.toLp 2 (fun i => (u i-v i).val) := by
    apply PiLp.ext
    intro i
    rw [OperatorSchur.vectorValues_apply,hdtuple]
  simpa only [hdvals,OperatorSchur.vectorEnergy_apply,hdtuple,mul_assoc] using ht

private theorem internal_entry_bound {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (B : ℝ) (hsym : ∀ i j, M i j=M j i)
    (hM : ∀ z : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, z i*M i j*z j)
    (hb : ∀ z : Fin n → ℝ, (∑ i, ∑ j, z i*M i j*z j) ≤ B*∑ i, z i^2)
    (i j : Fin n) : |M i j| ≤ B := by
  classical
  have hd (i : Fin n) : 0 ≤ M i i ∧ M i i ≤ B := by
    have hl := hM (Pi.single i 1)
    have hu := hb (Pi.single i 1)
    simpa [Pi.single_apply] using And.intro hl hu
  by_cases hij : i=j
  · subst j
    rw [abs_of_nonneg (hd i).1]
    exact (hd i).2
  have hp := hM (Pi.single i 1+Pi.single j 1)
  have hm := hM (Pi.single i 1-Pi.single j 1)
  simp only [Pi.add_apply,Pi.sub_apply,add_mul,mul_add,sub_mul,mul_sub,
    Finset.sum_add_distrib,Finset.sum_sub_distrib] at hp hm
  simp only [Pi.single_apply,ite_mul,mul_ite,one_mul,mul_one,zero_mul,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hp hm
  rw [hsym j i] at hp hm
  exact abs_le.mpr ⟨by linarith [(hd i).2,(hd j).2],by linarith [(hd i).2,(hd j).2]⟩

set_option backward.isDefEq.respectTransparency false in
/-- The comparison inequality of Subsection 4.5 for the physical matrices. Both equations use the same arbitrary closed conservative
scalar form. A measurable restriction covers every fixed-length fibre. -/
theorem physical_comparison_bound (p : Parameters) (hs : 1 < p.val.2)
    (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ (θ : PhysicalCutoff) (h : ℝ), 0 < h →
      ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, 1 ≤ C ∧ ∀ (n : ℕ+) (m : ℕ),
        4 ≤ (n : ℕ)+m+1 → 2*(n : ℕ) ≤ (n : ℕ)+m+1 → ∀ (b : Bool)
        (α : Type*) [MeasurableSpace α]
        (τ : α → AffineSimplex.chartDomain n ((n+m : ℕ)+1)), Measurable τ →
        ∀ (ν : Measure α) [IsProbabilityMeasure ν] (Q : ScalarFormData ν),
        IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
        ∀ (i₀ : Fin (n : ℕ)), (n : ℝ)/4 ≤ (i₀.val : ℝ)+1 →
          (i₀.val : ℝ)+1 ≤ 3*(n : ℝ)/4 → ∀ (χ : Lp ℝ 2 ν)
        (u v : Fin (n : ℕ) → Q.1),
        WeightedWeakSolution Q (fun x => p.val.1 • frozenPhysicalMatrix p n m θ h b
          (A*(n : ℝ)^(κ*h)) (τ x)) ⊤ (fun i => if i=i₀ then χ else 0) u →
        WeightedWeakSolution Q (fun x => p.val.1 • frozenInternalMatrix p n m θ h b
          (A*(n : ℝ)^(κ*h)) (τ x)) ⊤ (fun i => if i=i₀ then χ else 0) v →
        ‖WithLp.toLp 2 (fun i => (u i-v i).val)‖ +
          Real.sqrt (∑ i, Q.2 (u i-v i) (u i-v i)) ≤
          C*(n : ℝ)^(r*h)*((n : ℝ)^(-(p.val.2-1/2)) +
            (((n : ℕ)+m+1 : ℕ) : ℝ)^(-(1/2 : ℝ)))*‖χ‖ := by
  classical
  obtain ⟨q,hq,hmat⟩ := uniform_matrix_bounds p hs κ hκ
  obtain ⟨r,hr,hres⟩ := auxiliary_residual_bound p hs κ hκ
  refine ⟨q+r,add_nonneg hq hr,?_⟩
  intro θ h hh A hA
  obtain ⟨Cm,hCm,hmat⟩ := hmat θ h hh A hA
  obtain ⟨Cr,hCr,hres⟩ := hres θ h hh A hA
  let C := 1+2*(1+p.val.1⁻¹)*Cm*p.val.1*Cr
  have hβ := p.property.1
  have hC : 1 ≤ C := by
    dsimp only [C]
    have ht : 0 ≤ 2*(1+p.val.1⁻¹)*Cm*p.val.1*Cr := by positivity
    linarith
  refine ⟨C,hC,?_⟩
  intro n m hN hhalf b α _ τ hτ ν _ Q hQ hcons i₀ hlo hhi χ u v hu hv
  let D := A*(n : ℝ)^(κ*h)
  let B := Cm*(n : ℝ)^(q*h)
  let M := fun x => frozenInternalMatrix p n m θ h b D (τ x)
  let H := fun x => frozenPhysicalMatrix p n m θ h b D (τ x)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le hCm
    (Real.one_le_rpow hn1 (mul_nonneg hq hh.le))
  have hB0 : 0 < B := by linarith
  obtain ⟨hmH,hmM,hsH,hsM⟩ := frozenMatrices_measurable_symmetric p hs n m θ h hh b D
  have hHm (i j) : Measurable (fun x => H x i j) := (hmH i j).comp hτ
  have hMm (i j) : Measurable (fun x => M x i j) := (hmM i j).comp hτ
  have hmat' := hmat n m hN hhalf b
  have hHbounds (x) (z : Fin (n : ℕ) → ℝ) :
      B⁻¹*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*H x i j*z j ∧
      (∑ i, ∑ j, z i*H x i j*z j) ≤ B*(∑ i, z i^2) := hmat'.2.1 (τ x) z
  have hMbounds := ae_of_ae_map hτ.aemeasurable (hmat'.1 (ν.map τ)).2
  have hHl : ∀ᵐ x ∂ν, ∀ z : Fin (n : ℕ) → ℝ,
      B⁻¹*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*H x i j*z j :=
    ae_of_all _ fun x z => (hHbounds x z).1
  have hHnonneg (x) (z : Fin (n : ℕ) → ℝ) : 0 ≤ ∑ i, ∑ j, z i*H x i j*z j :=
    (mul_nonneg (inv_nonneg.mpr hB0.le) (Finset.sum_nonneg fun _ _ => sq_nonneg _)).trans
      (hHbounds x z).1
  have hHb : ∃ b : ℝ, ∀ᵐ x ∂ν, ∀ i j, |H x i j| ≤ b :=
    ⟨B,ae_of_all _ fun x i j => internal_entry_bound (H x) B (hsH (τ x))
      (hHnonneg x) (fun z => (hHbounds x z).2) i j⟩
  have hMb : ∃ b : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ b := by
    refine ⟨B,?_⟩
    filter_upwards [hMbounds] with x hx i j
    apply (hx.2.2 i j).trans
    apply mul_le_of_le_one_right hB0.le
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · exact le_add_of_nonneg_right (ComponentGeometryBounds.nonneg _ _ _)
    · linarith
  have hHp := AbstractEnergy.scaled_posSemidef (ρ := ν) p.val.1 B⁻¹ hβ.le
    (inv_nonneg.mpr hB0.le) H (ae_of_all _ fun x => ⟨hsH (τ x),fun z => (hHbounds x z).1⟩)
  have hMp := AbstractEnergy.scaled_posSemidef (ρ := ν) p.val.1 B⁻¹ hβ.le
    (inv_nonneg.mpr hB0.le) M (hMbounds.mono fun _ hx => ⟨hx.1,hx.2.1⟩)
  have hHsb : ∃ b : ℝ, ∀ᵐ x ∂ν, ∀ i j, |(p.val.1 • H x) i j| ≤ b := by
    obtain ⟨b,hb⟩ := hHb
    refine ⟨p.val.1*b,hb.mono fun x hx i j => ?_⟩
    simpa only [Matrix.smul_apply,smul_eq_mul,abs_mul,abs_of_pos hβ] using
      mul_le_mul_of_nonneg_left (hx i j) hβ.le
  have hMsb : ∃ b : ℝ, ∀ᵐ x ∂ν, ∀ i j, |(p.val.1 • M x) i j| ≤ b := by
    obtain ⟨b,hb⟩ := hMb
    refine ⟨p.val.1*b,hb.mono fun x hx i j => ?_⟩
    simpa only [Matrix.smul_apply,smul_eq_mul,abs_mul,abs_of_pos hβ] using
      mul_le_mul_of_nonneg_left (hx i j) hβ.le
  have hHa : ∀ᵐ x ∂ν, ∀ z : Fin (n : ℕ) → ℝ,
      (p.val.1*B⁻¹)*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*(p.val.1 • H x) i j*z j := by
    filter_upwards [hHl] with x hx z
    simpa only [Matrix.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc,mul_left_comm] using
      mul_le_mul_of_nonneg_left (hx z) hβ.le
  obtain ⟨g,hg,hgn⟩ := hres n m hN hhalf b α τ hτ ν Q hQ hcons i₀ hlo hhi χ v hv
  let G := fun i => p.val.1 • g i
  have hG : ∀ᵐ x ∂ν, ∀ i, G i x = ∑ j,
      ((p.val.1 • H x) i j-(p.val.1 • M x) i j)*(v j).val x := by
    filter_upwards [hg,ae_all_iff.mpr fun i => Lp.coeFn_smul p.val.1 (g i)] with x hx hsc i
    rw [hsc i]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [hx i]
    simp only [Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul,Finset.mul_sum,sub_mul]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [H,M,D]
    ring
  have hGn : ‖WithLp.toLp 2 G‖ = p.val.1*‖WithLp.toLp 2 g‖ := by
    change ‖p.val.1 • WithLp.toLp 2 g‖ = _
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hβ]
  have he := internal_common_form_comparison Q hQ (fun x => p.val.1 • H x)
    (fun x => p.val.1 • M x) (AbstractEnergy.scaled_measurable _ H hHm)
    (AbstractEnergy.scaled_measurable _ M hMm) hHsb hMsb hHp hMp
    (p.val.1*B⁻¹) (mul_pos hβ (inv_pos.mpr hB0)) hHa
    (fun i => if i=i₀ then χ else 0) u v hu hv G hG
  have hi : (min 1 (p.val.1*B⁻¹))⁻¹ ≤ (1+p.val.1⁻¹)*B := by
    by_cases ht : 1 ≤ p.val.1*B⁻¹
    · rw [min_eq_left ht,inv_one]
      have hp : 0 ≤ p.val.1⁻¹*B := mul_nonneg (inv_nonneg.mpr hβ.le) hB0.le
      nlinarith
    · rw [min_eq_right (le_of_not_ge ht),mul_inv_rev,inv_inv]
      nlinarith
  rw [hGn] at he
  apply he.trans
  calc
    _ ≤ 2*((1+p.val.1⁻¹)*B)*(p.val.1*
        (Cr*(n : ℝ)^(r*h)*((n : ℝ)^(-(p.val.2-1/2))+
          (((n : ℕ)+m+1 : ℕ) : ℝ)^(-(1/2 : ℝ)))*‖χ‖)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hi (by norm_num)
      · exact mul_le_mul_of_nonneg_left hgn hβ.le
      · positivity
      · positivity
    _ = (2*(1+p.val.1⁻¹)*Cm*p.val.1*Cr)*(n : ℝ)^((q+r)*h)*
        ((n : ℝ)^(-(p.val.2-1/2))+(((n : ℕ)+m+1 : ℕ) : ℝ)^(-(1/2 : ℝ)))*‖χ‖ := by
      dsimp only [B]
      rw [show (n : ℝ)^((q+r)*h)=(n : ℝ)^(q*h)*(n : ℝ)^(r*h) by
        rw [← Real.rpow_add hn0]; congr 1; ring]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg χ)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      dsimp only [C]
      linarith

private theorem internal_graph_norm_bound {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {n : ℕ} (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (u : Fin n → Q.1) :
    ‖(MatrixEnergy.vectorEquiv Q hQ).symm u‖ ≤
      ‖WithLp.toLp 2 (fun i => (u i).val)‖ + Real.sqrt (∑ i, Q.2 (u i) (u i)) := by
  let v := (MatrixEnergy.vectorEquiv Q hQ).symm u
  have hmass := OperatorSchur.vector_norm_sq Q hQ v
  have he := OperatorSchur.vectorEnergy_nonneg Q hQ v
  have htuple : MatrixEnergy.vectorEquiv Q hQ v = u := LinearEquiv.apply_symm_apply _ u
  have hvalues : OperatorSchur.vectorValues Q hQ v = WithLp.toLp 2 (fun i => (u i).val) := by
    apply PiLp.ext
    intro i
    rw [OperatorSchur.vectorValues_apply,htuple]
  rw [OperatorSchur.vectorEnergy_apply,htuple] at he hmass
  rw [hvalues] at hmass
  have hsq := Real.sq_sqrt he
  have hs := Real.sqrt_nonneg (∑ i, Q.2 (u i) (u i))
  change ‖v‖ ≤ _
  nlinarith [norm_nonneg v,norm_nonneg (WithLp.toLp 2 (fun i => (u i).val)),
    mul_nonneg (norm_nonneg (WithLp.toLp 2 (fun i => (u i).val))) hs]

private theorem internal_graph_sums {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {n : ℕ} (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (u : Fin n → Q.1) :
    (∑ i, ‖(u i).val‖) + Real.sqrt (Q.2 (∑ i, u i) (∑ i, u i)) ≤
      2 * ∑ i, ‖(ScalarFormHilbert.equiv Q hQ).symm (u i)‖ := by
  let v := fun i => (ScalarFormHilbert.equiv Q hQ).symm (u i)
  have hval (i) : ‖(u i).val‖ ≤ ‖v i‖ := by
    have he := ScalarFormHilbert.norm_sq Q hQ (v i)
    simp only [v,LinearEquiv.apply_symm_apply] at he
    nlinarith [hQ.2.2.1 (u i),norm_nonneg (u i).val,norm_nonneg (v i)]
  have hsum : ScalarFormHilbert.equiv Q hQ (∑ i, v i) = ∑ i, u i := by
    simp only [map_sum,v,LinearEquiv.apply_symm_apply]
  have he := ScalarFormHilbert.norm_sq Q hQ (∑ i, v i)
  rw [hsum] at he
  have hgrad : Real.sqrt (Q.2 (∑ i, u i) (∑ i, u i)) ≤ ‖∑ i, v i‖ := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨norm_nonneg _,by nlinarith [sq_nonneg ‖(∑ i, u i).val‖]⟩
  exact (add_le_add (Finset.sum_le_sum fun i _ => hval i)
    (hgrad.trans (norm_sum_le _ _))).trans_eq (by ring)

set_option backward.isDefEq.respectTransparency false in
/-- Internal weighted Cauchy–Schwarz step for the scalar energy of the
component sum in Subsection 4.5. It uses the form. -/
theorem internal_weighted_graph_sum {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {n : ℕ} (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (g : ComponentGeometry (Fin n)) (i₀ : Fin n) (a : ℝ) (ha : 1/2 < a)
    (u : Fin n → Q.1) :
    (∑ i, ‖(ScalarFormHilbert.equiv Q hQ).symm (u i)‖) ≤
      Real.sqrt (2*∑' k : ℕ, (1+(k : ℝ))^(-(2*a))) *
        (‖WithLp.toLp 2 (fun i => InitialDecay.distortionWeight g i₀ a i • (u i).val)‖ +
          Real.sqrt (∑ i, Q.2 (InitialDecay.distortionWeight g i₀ a i • u i)
            (InitialDecay.distortionWeight g i₀ a i • u i))) := by
  classical
  let w := InitialDecay.distortionWeight g i₀ a
  let c := InitialDecay.distortionWeight g i₀ (-a)
  let v := fun i => (ScalarFormHilbert.equiv Q hQ).symm (u i)
  let z := fun i => w i • v i
  let S := 2*∑' k : ℕ, (1+(k : ℝ))^(-(2*a))
  have hc (i) : c i*w i=1 := by
    dsimp only [c,w]
    rw [InitialDecay.distortionWeight_neg]
    exact inv_mul_cancel₀ (InitialDecay.distortionWeight_pos g i₀ a i).ne'
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ c (fun i => ‖z i‖)
  have he (i) : c i*‖z i‖=‖v i‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (InitialDecay.distortionWeight_pos g i₀ a i)]
    rw [← mul_assoc,hc i,one_mul]
  simp_rw [he] at hcs
  have hc2 (i) : c i^2 = (1+componentDistance g i₀ i)^(-(2*a)) := by
    rw [ComponentGeometryBounds.symm g i₀ i]
    change ((1+componentDistance g i i₀)^(-a))^2 = _
    rw [← Real.rpow_natCast,← Real.rpow_mul (by linarith [ComponentGeometryBounds.nonneg g i i₀])]
    congr 1
    norm_num
    ring
  have hsumc : (∑ i, c i^2) ≤ S := by
    simp_rw [hc2]
    exact ComponentGeometryBounds.sum_power_le g i₀ (by linarith : 1 < 2*a)
  have hz : Real.sqrt (∑ i, ‖z i‖^2) =
      ‖(MatrixEnergy.vectorEquiv Q hQ).symm (fun i => w i • u i)‖ := by
    have hz2 : ‖WithLp.toLp 2 z‖^2 = ∑ i, ‖z i‖^2 := by rw [PiLp.norm_sq_eq_of_L2]
    rw [← hz2,Real.sqrt_sq (norm_nonneg _)]
    rfl
  have hn : (∑ i, ‖v i‖) ≤ Real.sqrt S *
      (‖WithLp.toLp 2 (fun i => w i • (u i).val)‖+
        Real.sqrt (∑ i, Q.2 (w i • u i) (w i • u i))) := by
    apply hcs.trans
    rw [hz]
    apply mul_le_mul (Real.sqrt_le_sqrt hsumc)
      (internal_graph_norm_bound Q hQ (fun i => w i • u i)) (norm_nonneg _) (Real.sqrt_nonneg _)
  exact hn

set_option backward.isDefEq.respectTransparency false in
/-- Summable form norms of the actual internal auxiliary solution in
Subsection 4.5. This controls both the component values and the
scalar energy of their sum, uniformly in the form and the fibre. -/
theorem auxiliary_graph_sum_bound (p : Parameters) (hs : 1 < p.val.2)
    (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ (θ : PhysicalCutoff) (h : ℝ), 0 < h →
      ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, 1 ≤ C ∧ ∀ (n : ℕ+) (m : ℕ),
        4 ≤ (n : ℕ)+m+1 → 2*(n : ℕ) ≤ (n : ℕ)+m+1 → ∀ (b : Bool)
        (α : Type*) [MeasurableSpace α]
        (τ : α → AffineSimplex.chartDomain n ((n+m : ℕ)+1)), Measurable τ →
        ∀ (ν : Measure α) [IsProbabilityMeasure ν] (Q : ScalarFormData ν)
        (hQ : IsClosedScalarDirichletForm Q), IsConservativeScalarForm Q →
        ∀ (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν) (v : Fin (n : ℕ) → Q.1),
        WeightedWeakSolution Q (fun x => p.val.1 • frozenInternalMatrix p n m θ h b
          (A*(n : ℝ)^(κ*h)) (τ x)) ⊤ (fun i => if i=i₀ then χ else 0) v →
        (∑ i, ‖(ScalarFormHilbert.equiv Q hQ).symm (v i)‖) ≤ C*(n : ℝ)^(r*h)*‖χ‖ := by
  classical
  obtain ⟨q,hq,hmat⟩ := uniform_matrix_bounds p hs κ hκ
  let a := p.val.2/2
  have ha : 1/2<a := by dsimp only [a]; linarith
  have has : a<p.val.2-1/2 := by dsimp only [a]; linarith
  obtain ⟨r,Cd,hr,hCd,hdec⟩ := InitialDecay.initial_decay_uniform p.val.2 a p.val.1 hs ha has p.property.1
  let S := 2*∑' k : ℕ, (1+(k : ℝ))^(-(2*a))
  have hS : 0 ≤ S := mul_nonneg (by norm_num) (tsum_nonneg fun _ => by positivity)
  refine ⟨q*r,mul_nonneg hq hr,?_⟩
  intro θ h hh A hA
  obtain ⟨Cm,hCm,hmat⟩ := hmat θ h hh A hA
  let C := 1+Real.sqrt S*Cd*Cm^r
  have hC : 1 ≤ C := by
    dsimp only [C]
    have ht : 0 ≤ Real.sqrt S*Cd*Cm^r := by positivity
    linarith
  refine ⟨C,hC,?_⟩
  intro n m hN hhalf b α _ τ hτ ν _ Q hQ hcons i₀ χ v hv
  let B := Cm*(n : ℝ)^(q*h)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le hCm
    (Real.one_le_rpow hn1 (mul_nonneg hq hh.le))
  let g : ComponentGeometry (Fin (n : ℕ)) := Sum.inl
    ⟨fun i => (i.val : ℤ),fun i j hij => Fin.ext (Int.ofNat_inj.mp hij)⟩
  let M := fun x => frozenInternalMatrix p n m θ h b (A*(n : ℝ)^(κ*h)) (τ x)
  have hm := (hmat n m hN hhalf b).1 (ν.map τ)
  have hMm (i j) : Measurable (fun x => M x i j) := (hm.1 i j).comp hτ
  have hb := ae_of_ae_map hτ.aemeasurable hm.2
  have hd := (hdec α (Fin (n : ℕ)) ν Q hQ hcons g B hB M hMm hb i₀ χ).2 v hv
  have hsum := internal_weighted_graph_sum Q hQ g i₀ a ha v
  apply hsum.trans
  apply (mul_le_mul_of_nonneg_left hd (Real.sqrt_nonneg S)).trans
  have hfactor : Real.sqrt S*(Cd*B^r*‖χ‖) =
      (Real.sqrt S*Cd*Cm^r)*(n : ℝ)^((q*r)*h)*‖χ‖ := by
    dsimp only [B]
    rw [Real.mul_rpow (by linarith : 0 ≤ Cm) (by positivity),← Real.rpow_mul hn0.le,
      show (q*h)*r=(q*r)*h by ring]
    ring
  rw [hfactor]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg χ)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  dsimp only [C]
  linarith

private theorem internal_graph_sum_cauchy {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {n : ℕ} (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (u : Fin n → Q.1) :
    (∑ i, ‖(ScalarFormHilbert.equiv Q hQ).symm (u i)‖) ≤ Real.sqrt n *
      (‖WithLp.toLp 2 (fun i => (u i).val)‖ + Real.sqrt (∑ i, Q.2 (u i) (u i))) := by
  let z := fun i => (ScalarFormHilbert.equiv Q hQ).symm (u i)
  have hc := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : Fin n => (1 : ℝ)) (fun i => ‖z i‖)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hc
  have hz2 : ‖WithLp.toLp 2 z‖^2 = ∑ i, ‖z i‖^2 := by rw [PiLp.norm_sq_eq_of_L2]
  rw [← hz2,Real.sqrt_sq (norm_nonneg _)] at hc
  exact hc.trans (mul_le_mul_of_nonneg_left (internal_graph_norm_bound Q hQ u) (Real.sqrt_nonneg _))

set_option backward.isDefEq.respectTransparency false in
/-- Existence and uniqueness of the actual physical auxiliary solution
used in Subsection 4.5, over the common scalar form. -/
theorem physical_auxiliary_exists (p : Parameters) (hs : 1 < p.val.2)
    (κ : ℝ) (hκ : 0 ≤ κ) (θ : PhysicalCutoff) (h : ℝ) (hh : 0 < h)
    (A : ℝ) (hA : 1 ≤ A) (n : ℕ+) (m : ℕ)
    (hN : 4 ≤ (n : ℕ)+m+1) (hhalf : 2*(n : ℕ) ≤ (n : ℕ)+m+1) (b : Bool)
    (α : Type*) [MeasurableSpace α]
    (τ : α → AffineSimplex.chartDomain n ((n+m : ℕ)+1)) (hτ : Measurable τ)
    (ν : Measure α) [IsProbabilityMeasure ν] (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (hcons : IsConservativeScalarForm Q)
    (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν) :
    ∃! u : Fin (n : ℕ) → Q.1,
      WeightedWeakSolution Q (fun x => p.val.1 • frozenPhysicalMatrix p n m θ h b
        (A*(n : ℝ)^(κ*h)) (τ x)) ⊤ (fun i => if i=i₀ then χ else 0) u := by
  classical
  obtain ⟨q,hq,hmat⟩ := uniform_matrix_bounds p hs κ hκ
  obtain ⟨C,hC,hmat⟩ := hmat θ h hh A hA
  let B := C*(n : ℝ)^(q*h)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le hC
    (Real.one_le_rpow hn1 (mul_nonneg hq hh.le))
  have hB0 : 0 < B := by linarith
  have hHb := (hmat n m hN hhalf b).2.1
  obtain ⟨hmH,_,hsH,_⟩ := frozenMatrices_measurable_symmetric p hs n m θ h hh b (A*(n : ℝ)^(κ*h))
  let H := fun x => frozenPhysicalMatrix p n m θ h b (A*(n : ℝ)^(κ*h)) (τ x)
  have hHm (i j) : Measurable (fun x => H x i j) := (hmH i j).comp hτ
  have hbounds : ∀ᵐ x ∂ν, (∀ i j, H x i j=H x j i) ∧
      ∀ z : Fin (n : ℕ) → ℝ, B⁻¹*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*H x i j*z j ∧
      (∑ i, ∑ j, z i*H x i j*z j) ≤ B*(∑ i, z i^2) :=
    ae_of_all _ fun x => ⟨hsH (τ x),hHb (τ x)⟩
  obtain ⟨_,T,_,hT⟩ := AbstractEnergy.illustrative_energy p.val.1 p.property.1 Q hQ hcons
    H hHm B⁻¹ B (inv_pos.mpr hB0) ((inv_le_one_of_one_le₀ hB).trans hB) hbounds ⊤
  obtain ⟨u,hu,huniq,_⟩ := hT (WithLp.toLp 2 (fun i => if i=i₀ then χ else 0))
  exact ⟨u,hu,huniq⟩

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 4.5 of the paper (complete): comparison of the physical and
internal auxiliary solutions over a fixed scalar form, and both terms of
the physical component-sum estimate. Constants precede the sizes, the
arbitrary scalar form and the measurable fibre restriction. -/
theorem fixed_scalar_form_comparison (p : Parameters) (hs : 1 < p.val.2)
    (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ (θ : PhysicalCutoff) (h : ℝ), 0 < h →
      ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, 1 ≤ C ∧ ∀ (n : ℕ+) (m : ℕ),
        4 ≤ (n : ℕ)+m+1 → 2*(n : ℕ) ≤ (n : ℕ)+m+1 → ∀ (b : Bool)
        (α : Type*) [MeasurableSpace α]
        (τ : α → AffineSimplex.chartDomain n ((n+m : ℕ)+1)), Measurable τ →
        ∀ (ν : Measure α) [IsProbabilityMeasure ν] (Q : ScalarFormData ν),
        IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
        ∀ (i₀ : Fin (n : ℕ)), (n : ℝ)/4 ≤ (i₀.val : ℝ)+1 →
          (i₀.val : ℝ)+1 ≤ 3*(n : ℝ)/4 → ∀ χ : Lp ℝ 2 ν,
        let H := fun x => p.val.1 • frozenPhysicalMatrix p n m θ h b (A*(n : ℝ)^(κ*h)) (τ x)
        let M := fun x => p.val.1 • frozenInternalMatrix p n m θ h b (A*(n : ℝ)^(κ*h)) (τ x)
        let f := fun i => if i=i₀ then χ else 0
        (∃! u : Fin (n : ℕ) → Q.1, WeightedWeakSolution Q H ⊤ f u) ∧
        (∃! v : Fin (n : ℕ) → Q.1, WeightedWeakSolution Q M ⊤ f v) ∧
        ∀ (u v : Fin (n : ℕ) → Q.1), WeightedWeakSolution Q H ⊤ f u →
          WeightedWeakSolution Q M ⊤ f v →
          (‖WithLp.toLp 2 (fun i => (u i-v i).val)‖ +
            Real.sqrt (∑ i, Q.2 (u i-v i) (u i-v i)) ≤
            C*(n : ℝ)^(r*h)*((n : ℝ)^(-(p.val.2-1/2)) +
              (((n : ℕ)+m+1 : ℕ) : ℝ)^(-(1/2 : ℝ)))*‖χ‖) ∧
          ((∑ i, ‖(u i).val‖) + Real.sqrt (Q.2 (∑ i, u i) (∑ i, u i)) ≤
            C*(n : ℝ)^(r*h)*‖χ‖) := by
  classical
  obtain ⟨rc,hrc,hcomp⟩ := physical_comparison_bound p hs κ hκ
  obtain ⟨rv,hrv,haux⟩ := auxiliary_graph_sum_bound p hs κ hκ
  obtain ⟨_,_,hex⟩ := internal_auxiliary_point_source_decay p hs κ hκ
  refine ⟨rc+rv,add_nonneg hrc hrv,?_⟩
  intro θ h hh A hA
  obtain ⟨Cc,hCc,hcomp⟩ := hcomp θ h hh A hA
  obtain ⟨Cv,hCv,haux⟩ := haux θ h hh A hA
  obtain ⟨_,_,hex⟩ := hex θ h hh A hA
  let C := 1+2*Cv+4*Cc
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  have hCcC : Cc ≤ C := by dsimp only [C]; linarith
  have hsumC : 2*Cv+4*Cc ≤ C := by dsimp only [C]; linarith
  refine ⟨C,hC,?_⟩
  intro n m hN hhalf b α _ τ hτ ν _ Q hQ hcons i₀ hlo hhi χ H M f
  refine ⟨physical_auxiliary_exists p hs κ hκ θ h hh A hA n m hN hhalf b α τ hτ ν Q hQ hcons i₀ χ,
    (hex n m hN hhalf b α τ hτ ν Q hQ hcons i₀ χ).1,?_⟩
  intro u v hu hv
  have hc := hcomp n m hN hhalf b α τ hτ ν Q hQ hcons i₀ hlo hhi χ u v hu hv
  have ha := haux n m hN hhalf b α τ hτ ν Q hQ hcons i₀ χ v hv
  let P := (n : ℝ)^((rc+rv)*h)
  let R := (n : ℝ)^(-(p.val.2-1/2))+(((n : ℕ)+m+1 : ℕ) : ℝ)^(-(1/2 : ℝ))
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hpC : (n : ℝ)^(rc*h) ≤ P := Real.rpow_le_rpow_of_exponent_le hn1
    (by nlinarith : rc*h ≤ (rc+rv)*h)
  have hpV : (n : ℝ)^(rv*h) ≤ P := Real.rpow_le_rpow_of_exponent_le hn1
    (by nlinarith : rv*h ≤ (rc+rv)*h)
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hc' : ‖WithLp.toLp 2 (fun i => (u i-v i).val)‖+
      Real.sqrt (∑ i, Q.2 (u i-v i) (u i-v i)) ≤ Cc*P*R*‖χ‖ := by
    apply hc.trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpC (by linarith)) hR) (norm_nonneg χ)
  have ha' : (∑ i, ‖(ScalarFormHilbert.equiv Q hQ).symm (v i)‖) ≤ Cv*P*‖χ‖ :=
    ha.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpV (by linarith)) (norm_nonneg χ))
  constructor
  · exact hc'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCcC hP) hR) (norm_nonneg χ))
  have hd := internal_graph_sum_cauchy Q hQ (fun i => u i-v i)
  have hnN : (n : ℝ) ≤ (((n : ℕ)+m+1 : ℕ) : ℝ) := by norm_cast; omega
  have hsize := (comparison_size_bounds p.val.2 hs n _ hnN).2.2.2
  change Real.sqrt (n : ℝ)*R ≤ 2 at hsize
  have hd' : (∑ i, ‖(ScalarFormHilbert.equiv Q hQ).symm (u i-v i)‖) ≤ 2*Cc*P*‖χ‖ := by
    apply (hd.trans (mul_le_mul_of_nonneg_left hc' (Real.sqrt_nonneg _))).trans
    calc
      _ = (Real.sqrt (n : ℝ)*R)*(Cc*P*‖χ‖) := by ring
      _ ≤ 2*(Cc*P*‖χ‖) := mul_le_mul_of_nonneg_right hsize (by positivity)
      _ = _ := by ring
  have hs : (∑ i, ‖(ScalarFormHilbert.equiv Q hQ).symm (u i)‖) ≤
      (Cv+2*Cc)*P*‖χ‖ := by
    calc
      _ ≤ ∑ i, (‖(ScalarFormHilbert.equiv Q hQ).symm (v i)‖+
          ‖(ScalarFormHilbert.equiv Q hQ).symm (u i-v i)‖) := by
        apply Finset.sum_le_sum
        intro i _
        have he : (ScalarFormHilbert.equiv Q hQ).symm (u i) =
            (ScalarFormHilbert.equiv Q hQ).symm (v i)+
            (ScalarFormHilbert.equiv Q hQ).symm (u i-v i) := by
          rw [map_sub]
          abel
        rw [he]
        exact norm_add_le _ _
      _ = _ := Finset.sum_add_distrib
      _ ≤ Cv*P*‖χ‖+2*Cc*P*‖χ‖ := add_le_add ha' hd'
      _ = _ := by ring
  apply (internal_graph_sums Q hQ u).trans
  apply (mul_le_mul_of_nonneg_left hs (by norm_num)).trans
  calc
    _ = (2*Cv+4*Cc)*P*‖χ‖ := by ring
    _ ≤ C*P*‖χ‖ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsumC hP) (norm_nonneg χ)

end Riesz2.DecayShort.PhysicalComparison
