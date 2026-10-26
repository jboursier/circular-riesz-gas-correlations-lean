/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.LengthAveragingFibresPart6
public import Riesz2.Thermodynamic.LengthAveragingFibresPart7
public import Riesz2.Thermodynamic.LengthAveragingFibresPart9

/-!
# Final conditional length-fibre estimates

Physical substitution and common envelope selection for the proof of Lemma 6.5. The
physical penalty exponent is distinct from the fine tolerance, and all exceptional
quantities are conditional.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Classical ContDiff
set_option backward.isDefEq.respectTransparency false
namespace Riesz2.LengthAveragingFibres

/-- See the proof of Lemma 6.5 in the paper: the long column degree is
fixed before the physical cutoff, tolerance and temperature interval. -/
theorem long_columns_degree_internal (s : Riesz1.RieszExponent)
    (κ : ℝ) (hκ : 1 ≤ κ) :
    ∃ k : ℝ, 0 < k ∧ ∀ (θ : PhysicalCutoff) (η βlo βhi : ℝ), 0 < η → 0 < βlo → βlo ≤ βhi →
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
  let k := 2*(κ+7)+4
  refine ⟨k, by dsimp only [k]; linarith, fun θ η βlo βhi hη hlo hle => ?_⟩
  obtain ⟨Cp, hCp, hpen⟩ := penalty_fine_bound θ
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


/-- See the proof of Lemma 6.5 in the paper: short column degree
fixed before the physical cutoff and the fine tolerance. -/
theorem short_columns_degree_internal (s : ℝ) (hs : 1 < s)
    (κ : ℝ) (hκ : 1 ≤ κ) :
    ∃ k : ℝ, 0 < k ∧ ∀ (θ : PhysicalCutoff) (η βlo βhi : ℝ), 0 < η → 0 < βlo → βlo ≤ βhi →
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
  refine ⟨κ+4, by linarith, fun θ η βlo βhi hη hlo hle => ?_⟩
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


/-- See the proof of Lemma 6.5 in the paper: beta-scaled short
columns with a degree independent of the fixed cutoff. -/
theorem short_physical_columns_degree_internal (s : ℝ) (hs : 1 < s)
    (κ : ℝ) (hκ : 1 ≤ κ) :
    ∃ k : ℝ, 0 < k ∧ ∀ (θ : PhysicalCutoff) (η βlo βhi : ℝ), 0 < η → 0 < βlo → βlo ≤ βhi →
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
  obtain ⟨k, hk, hcol⟩ := short_columns_degree_internal s hs κ hκ
  obtain ⟨A, hA, hsum⟩ := short_score_weight_sum s hs
  refine ⟨k, hk, fun θ η βlo βhi hη hlo hle => ?_⟩
  obtain ⟨C, hC, hc⟩ := hcol θ η βlo βhi hη hlo hle
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


/-- See the proof of Lemma 6.5 in the paper: simultaneous two-sum and
multiplier absorption, keeping the square error until after the columns.
The prefactor is selected before the law, source and size. -/
theorem three_bounds_from_square_internal
    (τ C W A D E T K : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hC : 0 ≤ C) (hW : 0 ≤ W) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hE : 0 ≤ E) (hT : 0 ≤ T) (hK : 0 ≤ K) :
    ∃ Z : ℝ, 0 < Z ∧
    ∀ {X : Type*} [MeasurableSpace X] (ρ : Measure X) [IsProbabilityMeasure ρ]
      (n : ℕ+) (Q : ScalarFormData ρ)
      (M : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
      (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ρ) (u : Fin (n : ℕ) → Q.1)
      (v : Fin (n : ℕ) → Lp ℝ 2 ρ) (G : Set X) (_hG : MeasurableSet G)
      (w : Fin (n : ℕ) → ℝ), (∀ j, 0 ≤ w j) →
    ∀ a b B₀ C₀ B e : ℝ, 0 ≤ a → 0 ≤ b → 1+B₀+2*a ≤ C₀ →
      0 ≤ B → 0 ≤ e →
      (∀ i j, Integrable (fun x => M x i j*(u j).val x) ρ) →
      (∀ᵐ x ∂ρ.restrict G, ∀ j,
        (∑ i, |M x i j|) ≤ C*(n : ℝ)^(a+1-τ)+C*(n : ℝ)^(a+1-τ/2)*w j) →
      (∑ j, w j^2) ≤ W*(n : ℝ)^(1-τ) →
      (∑ j, w j*‖v j‖) ≤ A*(n : ℝ)^(b-τ/2)*‖χ‖ →
      (∑ j, ‖v j‖) ≤ D*(n : ℝ)^b*‖χ‖ →
      ‖WithLp.toLp 2 (fun j => (u j).val-v j)‖^2 ≤
        E*(n : ℝ)^(2*b-1)*‖χ‖^2+T*(n : ℝ)^(B₀-C₀)*B^2*e →
      |∫ x in Gᶜ, gapMultiplierField n Q M
        (fun i => if i = i₀ then χ else 0) u x ∂ρ| ≤ K*B*e →
      (∑ j, w j*‖(u j).val‖) ≤
        Z*(n : ℝ)^(a+b-τ/2)*‖χ‖+Z*B*Real.sqrt e ∧
      (∑ j, ‖(u j).val‖) ≤ Z*(n : ℝ)^(a+b)*‖χ‖+Z*B*Real.sqrt e ∧
      |∫ x, gapMultiplierField n Q M (fun i => if i = i₀ then χ else 0) u x ∂ρ| ≤
        Z*(n : ℝ)^(a+b-τ)*‖χ‖+Z*B*(Real.sqrt e+e) := by
  let U := A+Real.sqrt W*Real.sqrt E
  let V := D+Real.sqrt E
  let R := (1+Real.sqrt W)*Real.sqrt T
  let J := C*(D+Real.sqrt E+A+Real.sqrt W*Real.sqrt E)+1
  let Y := 2*C*R
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  have hY : 0 ≤ Y := by dsimp only [Y]; positivity
  let Z := 1+U+V+R+J+Y+K
  have hZ : 0 < Z := by dsimp only [Z]; positivity
  have hUZ : U ≤ Z := by dsimp only [Z]; linarith
  have hVZ : V ≤ Z := by dsimp only [Z]; linarith
  have hRZ : R ≤ Z := by dsimp only [Z]; linarith
  have hJZ : J ≤ Z := by dsimp only [Z]; linarith
  have hYZ : Y ≤ Z := by dsimp only [Z]; linarith
  have hKZ : K ≤ Z := by dsimp only [Z]; linarith
  refine ⟨Z, hZ, ?_⟩
  intro X _ ρ _ n Q M i₀ χ u v G hG w hw a b B₀ C₀ B e ha hb hC₀ hB he
    hpair hcol hweights hweighted hsum herror hbad
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hp (t : ℝ) : (n : ℝ)^t ≤ (n : ℝ)^(a+t) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hz : (n : ℝ)^((1+B₀-C₀)/2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  obtain ⟨hwgt, hsum'⟩ := fibre_sums_retaining_loss_internal n w hw (τ/2) W A D E T b
    B₀ C₀ ‖χ‖ B e (by positivity) hW hE hT (norm_nonneg χ) hB he
    (fun j => (u j).val) v
    (by simpa only [show (1 : ℝ)-2*(τ/2)=1-τ by ring] using hweights) hweighted hsum herror
  have herr : R*(n : ℝ)^((1+B₀-C₀)/2)*B*Real.sqrt e ≤ Z*B*Real.sqrt e := by
    have hh : R*(n : ℝ)^((1+B₀-C₀)/2) ≤ Z :=
      (mul_le_of_le_one_right hR hz).trans hRZ
    gcongr
  have hnormal := multiplier_from_square_internal n Q M i₀ χ u v G hG w hw
    τ a b C W A D E T B₀ C₀ K B e hτ hτ1 ha hb hC₀ hC hW hE hT hB he
    hpair hcol hweights hweighted hsum herror hbad
  refine ⟨hwgt.trans (add_le_add ?_ herr), hsum'.trans (add_le_add ?_ herr), ?_⟩
  · change U*(n : ℝ)^(b-τ/2)*‖χ‖ ≤ _
    have hh := hp (b-τ/2)
    rw [show a+(b-τ/2)=a+b-τ/2 by ring] at hh
    gcongr
  · change V*(n : ℝ)^b*‖χ‖ ≤ _
    gcongr
    linarith
  · apply hnormal.trans
    change J*(n : ℝ)^(a+b-τ)*‖χ‖+Y*B*Real.sqrt e+K*B*e ≤ _
    have hj := mul_le_mul_of_nonneg_right hJZ
      (show 0 ≤ (n : ℝ)^(a+b-τ)*‖χ‖ by positivity)
    have hy := mul_le_mul_of_nonneg_right hYZ (show 0 ≤ B*Real.sqrt e by positivity)
    have hk := mul_le_mul_of_nonneg_right hKZ (mul_nonneg hB he)
    nlinarith only [hj, hy, hk]

/-- The point-source estimates in the proof of Lemma 6.5 on a specified retained law and physical
Hessian.
Its finite remainder condition precedes every real-valued use of that remainder. -/
def FibreBoundsInternal {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (n : ℕ+) (M : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (s loss C : ℝ) (e : ℝ≥0∞) : Prop :=
  e < (∞ : ℝ≥0∞) ∧ ∀ (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q →
    IsConservativeScalarForm Q →
    ∀ i₀ : Fin (n : ℕ), |(i₀.val : ℝ)+1-(n : ℝ)/2| ≤ (n : ℝ)/4 →
    ∀ (χ : Lp ℝ 2 ν) (B : ℝ), 0 ≤ B → (∀ᵐ x ∂ν, |χ x| ≤ B) →
    (∃! ψ : Fin (n : ℕ) → Q.1, WeightedWeakSolution Q M
      (zeroSumComponents (Fin (n : ℕ))) (fun i => if i = i₀ then χ else 0) ψ) ∧
    ∀ ψ : Fin (n : ℕ) → Q.1, WeightedWeakSolution Q M
      (zeroSumComponents (Fin (n : ℕ))) (fun i => if i = i₀ then χ else 0) ψ →
    (∑ j, InteractionDifferential.boundaryWeight s n j*‖(ψ j).val‖) ≤
      C*(n : ℝ)^(loss-(min s 1)/2)*‖χ‖+C*B*Real.sqrt e.toReal ∧
    (∑ j, ‖(ψ j).val‖) ≤ C*(n : ℝ)^loss*‖χ‖+C*B*Real.sqrt e.toReal ∧
    Integrable (gapMultiplierField n Q M (fun i => if i = i₀ then χ else 0) ψ) ν ∧
    |∫ x, gapMultiplierField n Q M (fun i => if i = i₀ then χ else 0) ψ x ∂ν| ≤
      C*(n : ℝ)^(loss-min s 1)*‖χ‖+C*B*(Real.sqrt e.toReal+e.toReal)

/-- See the proof of Lemma 6.5 in the paper: the long square and its
auxiliary estimates on almost every actual length, uniformly before the
choice of scalar form and bounded middle-half source. -/
def RetainedLongSquareInternal
    (s : Riesz1.RieszExponent) (κ₀ : ℝ) : Prop :=
    ∃ κ b η₀ : ℝ, 0 < κ ∧ 0 < b ∧ 0 < η₀ ∧
    ∀ η : ℝ, 0 < η → η ≤ η₀ →
    ∀ (θ : PhysicalCutoff) (βlo βhi : ℝ), 0 < βlo → βlo ≤ βhi →
    ∃ D E T : ℝ, 0 < D ∧ 0 < E ∧ 0 < T ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
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
    ∃ v : Fin (n+1) → Q.1,
    (∀ j : Fin (n+1), ‖(v j).val‖ ≤ D*(n+1 : ℝ)^(κ*η)*
      (1+(Nat.dist j.val i₀.val : ℝ))^(s.val-2)*‖χ‖) ∧
    (∑ j, ‖(v j).val‖) ≤ D*(n+1 : ℝ)^(κ*η)*‖χ‖ ∧
    ‖(∑ j, v j : Q.1).val‖ ≤ D*(n+1 : ℝ)^(κ*η-(1-s.val))*‖χ‖ ∧
    Real.sqrt (Q.2 (∑ j, v j) (∑ j, v j)) ≤
      D*(n+1 : ℝ)^(κ*η-(1-s.val)/2)*‖χ‖ ∧
    (∀ j : Fin (n+1), ∀ᵐ x ∂ν, |(v j).val x| ≤ D*(n+1 : ℝ)^(κ*η)*B) ∧
    ∀ ψ : Fin (n+1) → Q.1,
      WeightedWeakSolution Q H (zeroSumComponents (Fin (n+1)))
        (fun i => if i = i₀ then χ else 0) ψ →
      ‖WithLp.toLp 2 (fun i => (ψ i).val-(v i).val)‖^2 ≤
        E*(n+1 : ℝ)^(2*(κ*η)-1)*‖χ‖^2 +
          T*(n+1 : ℝ)^(-2*Ptail)*B^2*e

/-- See the proof of Lemma 6.5 in the paper: retained-law specialization
of the long squared comparison with every auxiliary estimate. -/
theorem retained_long_square_internal
    (hz : External.PeriodicZeta) (hRig : External.LongRangeRigidityLocallyUniform)
    (s : Riesz1.RieszExponent) (κ₀ : ℝ) (hκ₀ : 1 ≤ κ₀) (h : ℕ+) : RetainedLongSquareInternal s κ₀ := by
  obtain ⟨κ, b, hκ, hb, hsums⟩ := long_conditional_square_internal hz s κ₀ hκ₀ h
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
  obtain ⟨D, E, T, hD, hE, hT, hsums⟩ := hsums η hη hηs θ βlo βhi hlo hle
  refine ⟨D, E, T, hD, hE, hT, ?_⟩
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
  have he : (∫⁻ x in (longFineEvent β s nA m η κ₀)ᶜ,
      ENNReal.ofReal (longEnvelope β s nA m θ ε C₀ x) ∂ν) ≠ (∞ : ℝ≥0∞) := hL.ne
  have hs := hsums β hβ nA m hnA hvol' M hM hnM hmb.1 hmb.2.1 hscale hupper ε C₀ Ptail
    hε.le hεη hP hC₀ hk hkm ν he Q hQ hcon i₀
    (by simpa only [nA, Nat.succPNat_coe, Nat.cast_succ] using hi₀) χ B hB hχ
  simpa only [ν, V, H, e, nA, Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one,
    longRemainder, retainedExceptionalMass] using hs


/-- See the proof of Lemma 6.5 in the paper, long regime, with fine
tolerance `2 ε`. All three displayed estimates and the weighted exceptional
integral are included. The degrees precede the cutoff and temperature. -/
def LongConclusionInternal (s : Riesz1.RieszExponent) : Prop :=
  ∃ κ C₀ ε₀ : ℝ, 0 < κ ∧ 0 < C₀ ∧ 0 < ε₀ ∧
  ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ δ : ℝ, 0 < δ ∧
  ∀ (θ : PhysicalCutoff) (βlo βhi : ℝ), 0 < βlo → βlo ≤ βhi →
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
  ∀ n m : ℕ, 1 ≤ n → 4*(n+1) ≤ n+1+m+1 →
    (n+1 : ℝ)^(2/s.val) ≤ ((n+1+m : ℕ)+1 : ℝ) →
  (∫⁻ L, longRemainder β s n m θ ε C₀ (2*ε) 1 L+
    longRemainder β s n m θ ε C₀ (2*ε) 1 L^2
    ∂lengthMeasure (ofLong β s) n m θ ε) ≤
      ENNReal.ofReal (C*Real.exp (-c*(n+1 : ℝ)^δ)) ∧
  ∀ᵐ L ∂lengthMeasure (ofLong β s) n m θ ε,
    let V := fun x : EuclideanSpace ℝ (Fin (n+1)) =>
      β.val*∑ i, (θ.val ((n+1 : ℝ)^(-ε)*x i)+θ.val ((n+1 : ℝ)^(-ε)*(x i)⁻¹)) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity (ofLong β s) (n+1) m (Equiv.refl _) (x,z)).toReal)
    FibreBoundsInternal (retainedKernel (ofLong β s) n m θ ε L) n.succPNat
      (fun x => hessianMatrix V x.val) s.val (κ*ε) C
      (longRemainder β s n m θ ε C₀ (2*ε) 1 L)

/-- See the proof of Lemma 6.5 in the paper: complete long physical
substitution, including the multiplier, on one common a.e. length set. -/
theorem long_length_averaging_fibres
    (hz : External.PeriodicZeta) (hRig : External.LongRangeRigidityLocallyUniform)
    (s : Riesz1.RieszExponent) : LongConclusionInternal s := by
  obtain ⟨r, b, η₀, hr, hb, hη₀, hsquare⟩ := retained_long_square_internal hz hRig s 1 le_rfl 1
  obtain ⟨rs, bs, ηs, hrs, hbs, hηs, hsums⟩ := retained_long_fibre_sums_internal hz hRig s 1 le_rfl 1
  obtain ⟨k, hk, hcols⟩ := long_columns_degree_internal s 1 le_rfl
  obtain ⟨C₀, hC₀, hCs, hCl, _, _⟩ :=
    common_envelope_exponent s.val (max b bs) 0 k 0 s.property.1
  let P := (C₀-b)/2
  have hP : 1/2 ≤ P := by dsimp only [P]; linarith [le_max_left b bs]
  have hPb : b+2*P ≤ C₀ := by dsimp only [P]; linarith
  let Ps := (C₀-bs)/2
  have hPs : 1/2 ≤ Ps := by dsimp only [Ps]; linarith [le_max_right b bs]
  have hPbs : bs+2*Ps ≤ C₀ := by dsimp only [Ps]; linarith
  let ε₀ := min 1 (min η₀ ηs)/2
  have hε₀ : 0 < ε₀ := by dsimp only [ε₀]; positivity
  refine ⟨2*(k+r), C₀, ε₀, by positivity, hC₀, hε₀, ?_⟩
  intro ε hε hsmall
  let η := 2*ε
  have hη : 0 < η := by dsimp only [η]; positivity
  have hη1 : η ≤ 1 := by
    have hh := hsmall.trans (show ε₀ ≤ 1/2 by dsimp only [ε₀]; gcongr; exact min_le_left _ _)
    dsimp only [η]; linarith
  have hεη : ε ≤ η := by dsimp only [η]; linarith
  have hsmallQ : η ≤ η₀ := by
    have hh := (min_le_right 1 (min η₀ ηs)).trans (min_le_left η₀ ηs)
    dsimp only [ε₀] at hsmall
    dsimp only [η]; linarith
  have hsmallS : η ≤ ηs := by
    have hh := (min_le_right 1 (min η₀ ηs)).trans (min_le_right η₀ ηs)
    dsimp only [ε₀] at hsmall
    dsimp only [η]; linarith
  let δ := GoodBlocks.coefficientTailPower s.val η
  have hδ : 0 < δ := GoodBlocks.coefficientTailPower_pos s.property.1 s.property.2 hη
  refine ⟨δ, hδ, ?_⟩
  intro θ βlo βhi hlo hle
  obtain ⟨D, E, T, hD, hE, hT, hsquare⟩ := hsquare η hη hsmallQ θ βlo βhi hlo hle
  obtain ⟨Cs, hCs', hsums⟩ := hsums η hη hsmallS θ βlo βhi hlo hle
  obtain ⟨Cc, hCc, hcols⟩ := hcols θ η βlo βhi hη hlo hle
  let W := 2/(1-s.val)
  let A := (8^(2-s.val)*(2/(1-s.val/2))+8^(s.val/2))*D
  let K := 2*(min 1 (s.val*(s.val+1)))⁻¹
  have hW : 0 ≤ W := by dsimp only [W]; have := s.property.2; positivity
  have hA : 0 ≤ A := by
    have : 0 < 1-s.val/2 := by linarith [s.property.2]
    dsimp only [A]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; have := s.property.1; positivity
  obtain ⟨Z, hZ, hthree⟩ := three_bounds_from_square_internal s.val Cc W A D E T K
    s.property.1 s.property.2.le hCc.le hW hA hD.le hE.le hT.le hK
  obtain ⟨Cb, c, hCb, hc, hbad⟩ := long_bad_remainder hRig s ε η C₀ hε hεη hC₀.le θ βlo βhi hlo hle
  let C := Z+Cb
  have hZC : Z ≤ C := by dsimp only [C]; linarith
  have hCbC : Cb ≤ C := by dsimp only [C]; linarith
  refine ⟨C, c, by dsimp only [C]; positivity, hc, ?_⟩
  intro β hβ n m hn hvol hpow
  have hhalf : 2*(n+1) ≤ n+1+m+1 := by omega
  refine ⟨(hbad β hβ n m hn hhalf 1 le_rfl).trans ?_, ?_⟩
  · apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right hCbC (Real.exp_pos _).le
  have hs := hsums β hβ n m hn hvol hpow ε C₀ Ps hε hεη hPs hPbs
  have hq := hsquare β hβ n m hn hvol hpow ε C₀ P hε hεη hP hPb
  have hx := long_exceptional_multiplier_internal β s n m θ ε C₀ η 1 hε
    (hεη.trans hη1) hCs hhalf
  filter_upwards [hs, hq, hx, longEnvelope_memLp_two_ae β s n m θ ε 0 hε hhalf]
    with L hLs hLq hLx hW2
  intro V
  let ν := retainedKernel (ofLong β s) n m θ ε L
  let H := fun x : AffineSimplex.chartDomain (n+1) ((n+1+m : ℕ)+1) => hessianMatrix V x.val
  refine ⟨hLs.1, ?_⟩
  intro Q hQ hcon i₀ hi₀ χ B hB hχ
  have hi₀' : |(i₀.val : ℝ)+1-(n+1 : ℝ)/2| ≤ (n+1 : ℝ)/4 := by
    simpa only [Nat.succPNat_coe, Nat.cast_succ] using hi₀
  refine ⟨(hLs.2 Q hQ hcon i₀ hi₀' χ B hB hχ).1, ?_⟩
  obtain ⟨v, hv, hvsum, _, _, _, herr⟩ := hLq.2 Q hQ hcon i₀ hi₀' χ B hB hχ
  have hn0 : (0 : ℝ) < n+1 := by positivity
  have hn1 : (1 : ℝ) ≤ n+1 := by exact_mod_cast n.succ_pos
  have hweighted := FixedLengthDecay.long_auxiliary_weighted_sum_internal s n.succPNat i₀ hi₀
    (D*(n+1 : ℝ)^(r*η)) ‖χ‖ (by positivity) (norm_nonneg _) (fun j => ‖(v j).val‖)
    (fun _ => norm_nonneg _) hv hvsum
  have hweighted' : (∑ j, InteractionDifferential.boundaryWeight s.val n.succPNat j*‖(v j).val‖) ≤
      A*(n+1 : ℝ)^(r*η-s.val/2)*‖χ‖ := by
    convert hweighted using 1
    simp only [A, Nat.succPNat_coe, Nat.cast_succ]
    rw [show r*η-s.val/2=r*η+(-s.val/2) by ring, Real.rpow_add hn0]
    ring
  have hcol := hcols β hβ n.succPNat m hhalf ε hε.le
  obtain ⟨hsm, _⟩ := long_twoSided_curvature_internal β s n.succPNat m θ ε hε.le
  simp only [Nat.succPNat_coe, Nat.cast_succ] at hsm hcol
  intro ψ hψ
  have hpair (i j) : Integrable (fun x => H x i j*(ψ j).val x) ν := by
    have hm := DecayShort.PhysicalComparison.measurable_hessianMatrix
      (AffineSimplex.isOpen_chartDomain _ _) hsm i j
    have hM2 := (hW2.const_mul (β.val*(n+1 : ℝ))).mono' hm.aestronglyMeasurable
      (ae_of_all _ fun x => by
        simpa only [H, V, Nat.succPNat_coe, Nat.cast_succ, sub_zero, neg_zero, Real.rpow_zero,
          mul_one, Real.norm_eq_abs] using
          long_twoSided_envelope_internal β s n.succPNat m θ ε 0 hε.le x i j)
    exact hM2.integrable_mul (Lp.memLp (ψ j).val)
  have hex := hLx Q hQ (zeroSumComponents _) i₀ χ B hB hχ ψ hψ
  have hcol' : ∀ᵐ x ∂ν.restrict (longFineEvent β s n.succPNat m η 1), ∀ j,
      (∑ i, |H x i j|) ≤ Cc*(n+1 : ℝ)^(k*η+1-s.val)+
        Cc*(n+1 : ℝ)^(k*η+1-s.val/2)*InteractionDifferential.boundaryWeight s.val n.succPNat j := by
    filter_upwards [ae_restrict_mem (measurableSet_longFineEvent β s n.succPNat m η 1)] with x hx
    intro j
    have hh := hcol x hx j
    convert hh using 1
    rw [show k*η+1-s.val=k*η+(1-s.val) by ring,
      show k*η+1-s.val/2=k*η+(1-s.val/2) by ring,
      Real.rpow_add hn0, Real.rpow_add hn0]
    ring
  have herr' := herr ψ hψ
  rw [show -2*P=b-C₀ by dsimp only [P]; ring] at herr'
  have hthreshold : 1+b+2*(k*η) ≤ C₀ := by
    have hh := mul_le_mul_of_nonneg_left hη1 hk.le
    linarith [le_max_left b bs]
  have ht := hthree ν n.succPNat Q H i₀ χ ψ (fun j => (v j).val)
    (longFineEvent β s n.succPNat m η 1) (measurableSet_longFineEvent _ _ _ _ _ _)
    (InteractionDifferential.boundaryWeight s.val n.succPNat)
    (fun j => (InteractionDifferential.boundaryWeight_pos _ _ _).le)
    (k*η) (r*η) b C₀ B (longRemainder β s n m θ ε C₀ η 1 L).toReal
    (by positivity) (by positivity) hthreshold hB ENNReal.toReal_nonneg
  simp only [Nat.succPNat_coe, Nat.cast_succ] at ht
  have ht := ht hpair hcol'
    (by simpa only [Nat.succPNat_coe, Nat.cast_succ] using
      FixedLengthDecay.long_boundary_square_sum s n.succPNat) hweighted' hvsum herr' hex.2.2
  have heq : k*η+r*η=(2*(k+r))*ε := by dsimp only [η]; ring
  simp only [heq] at ht
  simp only [Nat.succPNat_coe, Nat.cast_succ, min_eq_left s.property.2.le]
  exact ⟨ht.1.trans (by gcongr), ht.2.1.trans (by gcongr), hex.2.1,
    ht.2.2.trans (by gcongr)⟩

/-- See the proof of Lemma 6.5 in the paper: tangent solvability for
the actual beta-scaled short Hessian over the specified scalar form.
This uses the physical curvature, with its actual penalty exponent. -/
theorem short_tangent_solvability_internal (p : Parameters) (hs : 1 < p.val.2)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε : ℝ) (hε : 0 < ε)
    (ν : Measure (AffineSimplex.chartDomain n ((n+m : ℕ)+1)))
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q) :
    let F := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      ∑ i, (θ.val (((n : ℝ)^ε)⁻¹*y i)+θ.val (((n : ℝ)^ε)⁻¹*(y i)⁻¹))
    let K := fun y => p.val.1⁻¹*(p.val.1*F y-Real.log (∫ z : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,z)).toReal))
    let H := fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) =>
      p.val.1 • hessianMatrix K x.val
    ∀ i₀ : Fin (n : ℕ), ∀ χ : Lp ℝ 2 ν,
      ∃! ψ : Fin (n : ℕ) → Q.1, WeightedWeakSolution Q H
        (zeroSumComponents (Fin (n : ℕ))) (fun i => if i=i₀ then χ else 0) ψ := by
  intro F K H i₀ χ
  let V := fun y => p.val.1*F y-Real.log (∫ z : EuclideanSpace ℝ (Fin m),
    (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,z)).toReal)
  let a := p.val.1*(n : ℝ)^(-(p.val.2+2)*ε)
  have hn : (0 : ℝ) ≤ n := by positivity
  have hraw := short_twoSided_matrix_internal p hs n m θ ε hε
  have hV : ContDiffOn ℝ ∞ V (AffineSimplex.chartDomain n ((n+m : ℕ)+1)) := by
    simpa only [V, F, Real.rpow_neg hn] using hraw.1
  have hd (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1)) :
      (hessianMatrix V x.val).PosSemidef ∧ ∀ z : Fin (n : ℕ) → ℝ,
        a*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*hessianMatrix V x.val i j*z j := by
    simpa only [V, F, a, Real.rpow_neg hn] using hraw.2.2 x
  have heq (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1)) : H x = hessianMatrix V x.val := by
    have hvx : ContDiffAt ℝ 2 V x.val :=
      (hV.contDiffAt ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds x.property)).of_le (by norm_num)
    have hkx : ContDiffAt ℝ 2 K x.val := contDiffAt_const.mul hvx
    ext i j
    change p.val.1*hessianMatrix K x.val i j = hessianMatrix V x.val i j
    rw [DecayShort.PhysicalComparison.hessianMatrix_entry hkx,
      DecayShort.PhysicalComparison.hessianMatrix_entry hvx]
    change p.val.1*fderiv ℝ (fderiv ℝ (fun y => p.val.1⁻¹*V y)) x.val _ _ = _
    rw [PhysicalCollision.internal_hessian_const_mul hvx]
    exact mul_inv_cancel_left₀ p.property.1.ne' _
  rw [show H = (fun x => hessianMatrix V x.val) from funext heq]
  exact MatrixEnergy.weightedWeakSolution_existsUnique Q hQ _ (zeroSumComponents _)
    (ae_of_all _ fun x => (hd x).1) a hraw.2.1
    (ae_of_all _ fun x z _ => (hd x).2 z)
    (fun i j => DecayShort.PhysicalComparison.measurable_hessianMatrix
      (AffineSimplex.isOpen_chartDomain _ _) hV i j) _

/-- The uniform short-range square-comparison estimate used in the proof of
Lemma 6.5 is a hypothesis here. The law is arbitrary, so it specializes to
the retained kernel with the same scalar form. -/
def ShortSquareInputInternal (s κ₀ : ℝ) : Prop :=
    ∃ κ b : ℝ, 0 < κ ∧ 0 < b ∧
    ∀ (θ : PhysicalCutoff) (ε η : ℝ), 0 < ε → ε ≤ η → η ≤ 1 →
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
    ∃ D E T : ℝ, 1 ≤ D ∧ 0 < E ∧ 0 < T ∧
    ∀ (p : Parameters), p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
    ∀ (n : ℕ+) (m : ℕ), 4 ≤ (n : ℕ)+m+1 → 2*(n : ℕ) ≤ (n : ℕ)+m+1 →
    ∀ C₀ : ℝ,
    let FF := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      ∑ i, (θ.val (((n : ℝ)^ε)⁻¹*y i)+θ.val (((n : ℝ)^ε)⁻¹*(y i)⁻¹))
    let KK := fun y => p.val.1⁻¹*(p.val.1*FF y-Real.log (∫ z : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,z)).toReal))
    let HH := fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) => p.val.1 • hessianMatrix KK x.val
    ∀ (ν : Measure (AffineSimplex.chartDomain n ((n+m : ℕ)+1))) [IsProbabilityMeasure ν],
    (∫⁻ x in (shortFineEvent p n m η κ₀)ᶜ,
      ENNReal.ofReal (shortEnvelope p n m θ ε C₀ x) ∂ν) ≠ (∞ : ℝ≥0∞) →
    ∀ (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
    ∀ i₀ : Fin (n : ℕ), |(i₀.val : ℝ)+1-(n : ℝ)/2| ≤ (n : ℝ)/4 →
    ∀ (χ : Lp ℝ 2 ν) (B : ℝ), 0 ≤ B → (∀ᵐ x ∂ν,|χ x| ≤ B) →
    let e := (∫⁻ x in (shortFineEvent p n m η κ₀)ᶜ,
      ENNReal.ofReal (shortEnvelope p n m θ ε C₀ x) ∂ν).toReal
    ∃ v : Fin (n : ℕ) → Q.1,
      (∀ j, ‖(v j).val‖ ≤ D*(n : ℝ)^(κ*η)*
        (1+|(j.val : ℝ)-(i₀.val : ℝ)|)^(-s)*‖χ‖) ∧
      (∑ j,‖(v j).val‖) ≤ D*(n : ℝ)^(κ*η)*‖χ‖ ∧
      ∀ ψ : Fin (n : ℕ) → Q.1,
      WeightedWeakSolution Q HH (zeroSumComponents (Fin (n : ℕ)))
        (fun i => if i=i₀ then χ else 0) ψ →
      ‖WithLp.toLp 2 (fun j => (ψ j).val-(v j).val)‖^2 ≤
        E*(n : ℝ)^(2*(κ*η)-1)*‖χ‖^2+T*(n : ℝ)^(b-C₀)*B^2*e

/-- See the proof of Lemma 6.5 in the paper, complete short conclusion.
The fixed coefficient degree and envelope precede tolerance and temperature. -/
def ShortConclusionInternal (s : ℝ) : Prop :=
  ∃ κ₀ κ C₀ ε₀ : ℝ, 1 ≤ κ₀ ∧ 0 < κ ∧ 0 < C₀ ∧ 0 < ε₀ ∧
  ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ δ : ℝ, 0 < δ ∧
  ∀ (θ : PhysicalCutoff) (βlo βhi : ℝ), 0 < βlo → βlo ≤ βhi →
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
  ∀ n m : ℕ, 1 ≤ n → 4*(n+1) ≤ n+1+m+1 →
    (n+1 : ℝ)^(2/s) ≤ ((n+1+m : ℕ)+1 : ℝ) →
  (∫⁻ L, shortRemainder p n m θ ε C₀ (2*ε) κ₀ L+
    shortRemainder p n m θ ε C₀ (2*ε) κ₀ L^2 ∂lengthMeasure p n m θ ε) ≤
      ENNReal.ofReal (C*Real.exp (-c*(n+1 : ℝ)^δ)) ∧
  ∀ᵐ L ∂lengthMeasure p n m θ ε,
    let F := fun y : EuclideanSpace ℝ (Fin (n+1)) =>
      ∑ i, (θ.val (((n+1 : ℝ)^ε)⁻¹*y i)+θ.val (((n+1 : ℝ)^ε)⁻¹*(y i)⁻¹))
    let K := fun y => p.val.1⁻¹*(p.val.1*F y-Real.log (∫ z : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p (n+1) m (Equiv.refl _) (y,z)).toReal))
    FibreBoundsInternal (retainedKernel p n m θ ε L) n.succPNat
      (fun x => p.val.1 • hessianMatrix K x.val) s (κ*ε) C
      (shortRemainder p n m θ ε C₀ (2*ε) κ₀ L)

/-- The short physical multiplier and both fibre sums in the proof of
Lemma 6.5 follow from the retained squared comparison. The exceptional
moment estimate and physical column/normal estimates hold on one common
a.e. length set. -/
theorem short_length_averaging_fibres_internal (s : ℝ) (hs : 1 < s)
    (hshort : ∀ κ₀ : ℝ, 0 ≤ κ₀ → ShortSquareInputInternal s κ₀) :
    ShortConclusionInternal s := by
  obtain ⟨κbad, hκbad, hbad⟩ := short_bad_remainder s hs
  let κ₀ := max 1 κbad
  have hκ₀ : 1 ≤ κ₀ := le_max_left _ _
  have hκbad' : κbad ≤ κ₀ := le_max_right _ _
  obtain ⟨r, b, hr, hb, hsquare⟩ := hshort κ₀ (zero_le_one.trans hκ₀)
  obtain ⟨k, hk, hcols⟩ := short_physical_columns_degree_internal s hs κ₀ hκ₀
  obtain ⟨C₀, hC₀, hCs, _, hCl, _⟩ := common_envelope_exponent s 0 b 0 k (by linarith)
  let ε₀ : ℝ := 1/2
  have hε₀ : 0 < ε₀ := by dsimp only [ε₀]; positivity
  refine ⟨κ₀, 2*(k+r), C₀, ε₀, hκ₀, by positivity, hC₀, hε₀, ?_⟩
  intro ε hε hsmall
  let η := 2*ε
  have hη : 0 < η := by dsimp only [η]; positivity
  have hη1 : η ≤ 1 := by dsimp only [η, ε₀] at *; linarith
  have hεη : ε ≤ η := by dsimp only [η]; linarith
  obtain ⟨δ, hδ, hbad⟩ := hbad η hη
  refine ⟨δ, hδ, ?_⟩
  intro θ βlo βhi hlo hle
  obtain ⟨D, E, T, hD1, hE, hT, hsquare⟩ := hsquare θ ε η hε hεη hη1 βlo βhi hlo hle
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  obtain ⟨Cc, hCc, hcols⟩ := hcols θ η βlo βhi hη hlo hle
  obtain ⟨Cb, c, hCb, hc, hbad⟩ := hbad ε C₀ hε hεη hC₀.le θ βlo βhi hlo hle
  let W := 2*∑' j : ℕ, (1+(j : ℝ))^(-(2*s-1))
  let A := (4*8^s+Real.sqrt 8)*D
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  obtain ⟨Z, hZ, hthree⟩ := three_bounds_from_square_internal 1 Cc W A D E T 2
    zero_lt_one le_rfl hCc.le hW hA hD.le hE.le hT.le (by norm_num)
  let C := Z+Cb
  have hZC : Z ≤ C := by dsimp only [C]; linarith
  have hCbC : Cb ≤ C := by dsimp only [C]; linarith
  refine ⟨C, c, by dsimp only [C]; positivity, hc, ?_⟩
  intro p hp hlo' hhi' n m hn hvol _hpow
  have hsp : 1 < p.val.2 := hp ▸ hs
  have hhalf : 2*(n+1) ≤ n+1+m+1 := by omega
  have hN : 4 ≤ n+1+m+1 := by omega
  refine ⟨(hbad p hp hlo' hhi' n m hn hhalf κ₀ hκbad').trans ?_, ?_⟩
  · exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCbC (Real.exp_pos _).le)
  have hq := shortRemainder_finite_ae p hsp n m θ ε C₀ η κ₀ hε hhalf
  have hx := short_exceptional_multiplier_internal p hsp n m θ ε C₀ η κ₀ hε
    (hεη.trans hη1) (by simpa only [hp] using hCs) hhalf
  filter_upwards [hq, hx, shortEnvelope_memLp_two_ae p hsp n m θ ε 0 hε hhalf]
    with L hLq hLx hW2
  intro F K
  let ν := retainedKernel p n m θ ε L
  let H := fun x : AffineSimplex.chartDomain (n+1) ((n+1+m : ℕ)+1) =>
    p.val.1 • hessianMatrix K x.val
  refine ⟨hLq, ?_⟩
  intro Q hQ hcon i₀ hi₀ χ B hB hχ
  have hi₀' : |(i₀.val : ℝ)+1-(n+1 : ℝ)/2| ≤ (n+1 : ℝ)/4 := by
    simpa only [Nat.succPNat_coe, Nat.cast_succ] using hi₀
  have he : (∫⁻ x in (shortFineEvent p n.succPNat m η κ₀)ᶜ,
      ENNReal.ofReal (shortEnvelope p n.succPNat m θ ε C₀ x) ∂ν) ≠ (∞ : ℝ≥0∞) := hLq.ne
  have hcomp := hsquare p hp hlo' hhi' n.succPNat m hN hhalf C₀ ν he Q hQ hcon
  simp only [Nat.succPNat_coe, Nat.cast_succ] at hcomp
  obtain ⟨v, hv, hvsum, herr⟩ := hcomp i₀ hi₀' χ B hB hχ
  refine ⟨?_, ?_⟩
  · simpa only [Nat.succPNat_coe, Nat.cast_succ] using
      short_tangent_solvability_internal p hsp n.succPNat m θ ε hε ν Q hQ i₀ χ
  have hn0 : (0 : ℝ) < n+1 := by positivity
  have hweighted := FixedLengthDecay.short_auxiliary_weighted_sum_internal s hs n.succPNat i₀ hi₀
    (D*(n+1 : ℝ)^(r*η)) ‖χ‖ (by positivity) (norm_nonneg _) (fun j => ‖(v j).val‖)
    (fun _ => norm_nonneg _)
    (fun j => by
      have hd : (Nat.dist j.val i₀.val : ℝ) = |(j.val : ℝ)-(i₀.val : ℝ)| := by
        exact_mod_cast natCast_dist_eq_abs j.val i₀.val
      simpa only [hd] using hv j) hvsum
  have hweighted' : (∑ j, InteractionDifferential.boundaryWeight s n.succPNat j*‖(v j).val‖) ≤
      A*(n+1 : ℝ)^(r*η-1/2)*‖χ‖ := by
    convert hweighted using 1
    simp only [A, Nat.succPNat_coe, Nat.cast_succ]
    rw [show r*η-1/2=r*η+(-(1 : ℝ)/2) by ring, Real.rpow_add hn0]
    ring
  have hcol := hcols p hp hlo' hhi' n.succPNat m hN hhalf ε hε.le
  have hsm := (DecayShort.PhysicalFibres.active_marginal_curvature p hsp
    (n+1) m (by omega) (Equiv.refl _) θ ε hε true).1
  have hsm : ContDiffOn ℝ ∞ K (AffineSimplex.chartDomain (n+1) ((n+1+m : ℕ)+1)) := by
    simpa only [K, F, ite_true, Nat.cast_add, Nat.cast_one] using hsm
  simp only [Nat.succPNat_coe, Nat.cast_succ] at hcol
  intro ψ hψ
  have hpair (i j) : Integrable (fun x => H x i j*(ψ j).val x) ν := by
    have hm := (DecayShort.PhysicalComparison.measurable_hessianMatrix
      (AffineSimplex.isOpen_chartDomain _ _) hsm i j).const_mul p.val.1
    have hentry := short_physical_entry_envelope_internal p hsp n.succPNat m θ ε 0 hε
    simp only [Nat.succPNat_coe, Nat.cast_succ, sub_zero] at hentry
    have hM2 := (hW2.const_mul (p.val.1*(n+1 : ℝ)^(2 : ℝ))).mono' hm.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [H, K, F, Matrix.smul_apply, smul_eq_mul, Real.norm_eq_abs] using hentry x i j)
    exact hM2.integrable_mul (Lp.memLp (ψ j).val)
  have hex := hLx Q hQ (zeroSumComponents _) i₀ χ B hB hχ ψ hψ
  have hcol' : ∀ᵐ x ∂ν.restrict (shortFineEvent p n.succPNat m η κ₀), ∀ j,
      (∑ i, |H x i j|) ≤ Cc*(n+1 : ℝ)^(k*η+1-1)+
        Cc*(n+1 : ℝ)^(k*η+1-1/2)*InteractionDifferential.boundaryWeight s n.succPNat j := by
    filter_upwards [ae_restrict_mem (measurableSet_shortFineEvent p hsp n.succPNat m θ η κ₀)] with x hx
    intro j
    have hh := hcol x hx j
    convert hh using 1
    rw [show k*η+1-1=k*η by ring,
      show k*η+1-1/2=k*η+(1/2) by ring, Real.rpow_add hn0]
    ring
  have herr' := herr ψ hψ
  have hthreshold : 1+b+2*(k*η) ≤ C₀ := by
    have hh := mul_le_mul_of_nonneg_left hη1 hk.le
    linarith
  have ht := hthree ν n.succPNat Q H i₀ χ ψ (fun j => (v j).val)
    (shortFineEvent p n.succPNat m η κ₀) (measurableSet_shortFineEvent _ hsp _ _ θ _ _)
    (InteractionDifferential.boundaryWeight s n.succPNat)
    (fun j => (InteractionDifferential.boundaryWeight_pos _ _ _).le)
    (k*η) (r*η) b C₀ B (shortRemainder p n m θ ε C₀ η κ₀ L).toReal
    (by positivity) (by positivity) hthreshold hB ENNReal.toReal_nonneg
  simp only [Nat.succPNat_coe, Nat.cast_succ] at ht
  have ht := ht hpair hcol'
    (by
      convert FixedLengthDecay.short_boundary_square_sum s hs n.succPNat using 1
      · rfl
      · simp only [W, sub_self, Real.rpow_zero, mul_one]) hweighted' hvsum herr' hex.2.2
  have heq : k*η+r*η=(2*(k+r))*ε := by dsimp only [η]; ring
  simp only [heq] at ht
  simp only [Nat.succPNat_coe, Nat.cast_succ, min_eq_right hs.le]
  exact ⟨ht.1.trans (by gcongr), ht.2.1.trans (by gcongr), hex.2.1,
    ht.2.2.trans (by gcongr)⟩

/-- The fibre estimates in the proof of Lemma 6.5 hold in both regimes.
The short-range branch assumes the retained squared comparison. -/
theorem length_averaging_fibres_internal
    (hz : External.PeriodicZeta) (hRig : External.LongRangeRigidityLocallyUniform)
    (hshort : ∀ s : ℝ, 1 < s → ∀ κ₀ : ℝ, 0 ≤ κ₀ → ShortSquareInputInternal s κ₀) :
    (∀ s : Riesz1.RieszExponent, LongConclusionInternal s) ∧
    (∀ s : ℝ, 1 < s → ShortConclusionInternal s) :=
  ⟨long_length_averaging_fibres hz hRig,
    fun s hs => short_length_averaging_fibres_internal s hs (hshort s hs)⟩

end Riesz2.LengthAveragingFibres
