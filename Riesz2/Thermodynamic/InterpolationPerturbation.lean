/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.InterpolationMatrix
public import Riesz2.Thermodynamic.CrossingCoefficients
public import Riesz2.Thermodynamic.InterpolationCoercivity
public import Riesz2.ToMathlib.KernelCovarianceBounds
import all Riesz2.DecayLong.BoundarySchurBounds

/-!
# Fixed-exterior perturbation pairings

Ingredients for Subsection 6.1. Exceptional coefficients use the weighted exceptional
mass directly. No moments of all orders, and no conditional covariance, are used. The
scalar form in the Schur contribution is the same form and measure as in the
multiplication contribution.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Matrix
open scoped BigOperators ENNReal MatrixOrder

namespace Riesz2.InterpolationPerturbation

/-- See Subsection 6.1 of the paper: weighted exceptional mass controls the restricted
second norm. This internal implication needs a square bound only on the
exceptional set, and concludes finiteness of that norm. -/
theorem weighted_second_norm_internal {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {E : Set Ω} {Y W : Ω → ℝ} {B R : ℝ}
    (hY : Measurable Y) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hsq : ∀ᵐ x ∂ν.restrict E, |Y x| ^ 2 ≤ B * W x)
    (htail : (∫⁻ x in E, ENNReal.ofReal (W x) ∂ν) ≤ ENNReal.ofReal R) :
    eLpNorm Y 2 (ν.restrict E) ≤ ENNReal.ofReal (Real.sqrt (B * R)) := by
  have hb : (∫⁻ x in E, ENNReal.ofReal (|Y x| ^ (2 : ℝ)) ∂ν) ≤
      ENNReal.ofReal (B * R) := by
    calc
      _ ≤ ∫⁻ x in E, ENNReal.ofReal (B * W x) ∂ν :=
        lintegral_mono_ae (hsq.mono fun x hx => by
          simpa only [Real.rpow_two] using ENNReal.ofReal_le_ofReal hx)
      _ = ENNReal.ofReal B * ∫⁻ x in E, ENNReal.ofReal (W x) ∂ν := by
        simp_rw [ENNReal.ofReal_mul hB]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal B * ENNReal.ofReal R := by gcongr
      _ = _ := (ENNReal.ofReal_mul hB).symm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    hY.aestronglyMeasurable.restrict]
  norm_num only [ENNReal.toReal_ofNat]
  have he : (∫⁻ x in E, ‖Y x‖ₑ ^ (2 : ℝ) ∂ν) =
      ∫⁻ x in E, ENNReal.ofReal (|Y x| ^ (2 : ℝ)) ∂ν := by
    apply lintegral_congr
    intro x
    rw [Real.enorm_eq_ofReal_abs,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
  rw [he]
  exact (ENNReal.rpow_le_rpow hb (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq (by
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hB hR) (by norm_num),
      Real.sqrt_eq_rpow])

/-- See Subsection 6.1 of the paper: a weighted square envelope gives the exceptional
bilinear estimate and its actual integrability domain. Essential scalar
bounds suffice. No pointwise representative choice is imposed. -/
theorem weighted_exceptional_pair_internal {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {E : Set Ω}
    {Y W φ η : Ω → ℝ} {B R Mφ Mη : ℝ}
    (hY : Measurable Y) (hφ : Measurable φ) (hη : Measurable η)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (hMφ : 0 ≤ Mφ) (hMη : 0 ≤ Mη)
    (hφM : ∀ᵐ x ∂ν, |φ x| ≤ Mφ) (hηM : ∀ᵐ x ∂ν, |η x| ≤ Mη)
    (hsq : ∀ᵐ x ∂ν.restrict E, |Y x| ^ 2 ≤ B * W x)
    (htail : (∫⁻ x in E, ENNReal.ofReal (W x) ∂ν) ≤ ENNReal.ofReal R) :
    IntegrableOn (fun x => φ x * η x * Y x) E ν ∧
      |∫ x in E, φ x * η x * Y x ∂ν| ≤ Real.sqrt (B * R) * (Mφ * Mη) :=
  KernelCovarianceBounds.restricted_pair hY hφ hη (Real.sqrt_nonneg _) hMφ hMη
    hφM hηM (weighted_second_norm_internal hY hB hR hsq htail)

/-- See Subsection 6.1 of the paper: multiplication estimate with a good-set profile
and a whole-simplex square envelope. The remainder uses the weighted tail,
rather than an unweighted event probability or a full-law moment bound. -/
theorem multiplication_pair_internal {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsProbabilityMeasure ν] {G : Set Ω}
    {Y W φ η : Ω → ℝ} {A B R Mφ Mη : ℝ}
    (hG : MeasurableSet G) (hY : Measurable Y)
    (hφ : Measurable φ) (hη : Measurable η)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 0 ≤ R) (hMφ : 0 ≤ Mφ) (hMη : 0 ≤ Mη)
    (hφM : ∀ᵐ x ∂ν, |φ x| ≤ Mφ) (hηM : ∀ᵐ x ∂ν, |η x| ≤ Mη)
    (hφ2 : MemLp φ 2 ν) (hη2 : MemLp η 2 ν)
    (hgood : ∀ᵐ x ∂ν.restrict G, |Y x| ≤ A)
    (hsq : ∀ᵐ x ∂ν.restrict Gᶜ, |Y x| ^ 2 ≤ B * W x)
    (htail : (∫⁻ x in Gᶜ, ENNReal.ofReal (W x) ∂ν) ≤ ENNReal.ofReal R) :
    Integrable (fun x => φ x * η x * Y x) ν ∧
      |∫ x, φ x * η x * Y x ∂ν| ≤
        A * (Real.sqrt (∫ x, φ x ^ 2 ∂ν) * Real.sqrt (∫ x, η x ^ 2 ∂ν)) +
          Real.sqrt (B * R) * (Mφ * Mη) := by
  obtain ⟨hi, hCS⟩ := MomentEvent.integrable_mul_and_integral_abs_mul_le hφ hη
    ((memLp_two_iff_integrable_sq hφ.aestronglyMeasurable).mp hφ2)
    ((memLp_two_iff_integrable_sq hη.aestronglyMeasurable).mp hη2)
  have hpt : ∀ᵐ x ∂ν.restrict G, ‖φ x*η x*Y x‖ ≤ A*|φ x*η x| := by
    filter_upwards [hgood] with x hx
    rw [Real.norm_eq_abs, abs_mul, mul_comm A]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  have hig : IntegrableOn (fun x => φ x*η x*Y x) G ν :=
    ((hi.abs.const_mul A).integrableOn).mono'
      ((hφ.mul hη).mul hY).aestronglyMeasurable.restrict hpt
  have hbg : |∫ x in G, φ x*η x*Y x ∂ν| ≤
      A*(Real.sqrt (∫ x, φ x^2 ∂ν)*Real.sqrt (∫ x, η x^2 ∂ν)) := by
    calc
      _ ≤ ∫ x in G, |φ x*η x*Y x| ∂ν := abs_integral_le_integral_abs
      _ ≤ ∫ x in G, A*|φ x*η x| ∂ν :=
        integral_mono_ae hig.abs (hi.abs.const_mul A).integrableOn
          (hpt.mono fun x hx => by simpa only [Real.norm_eq_abs] using hx)
      _ = A*∫ x in G, |φ x*η x| ∂ν := integral_const_mul _ _
      _ ≤ A*∫ x, |φ x*η x| ∂ν := mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hi.abs (ae_of_all ν fun _ => abs_nonneg _)) hA
      _ ≤ _ := mul_le_mul_of_nonneg_left hCS hA
  obtain ⟨hie, hbe⟩ := weighted_exceptional_pair_internal
    hY hφ hη hB hR hMφ hMη hφM hηM hsq htail
  have hi : Integrable (fun x => φ x * η x * Y x) ν := by
    simpa only [union_compl_self, integrableOn_univ] using hig.union hie
  refine ⟨hi, ?_⟩
  rw [← integral_add_compl hG hi]
  exact (abs_add_le _ _).trans (add_le_add hbg hbe)

/-- See Subsection 6.1 of the paper: polynomial losses and a square root preserve the
tail exponent exactly. In particular `δ` is an input, preceding every
prefactor, and is never chosen as a function of temperature. -/
theorem weighted_tail_absorption_internal {δ c B D q : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) (hB : 0 < B) (hD : 0 < D) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℝ, 1 ≤ n →
      Real.sqrt ((B * n ^ q) * (D * Real.exp (-c * n ^ δ))) ≤
        C * Real.exp (-(c / 4) * n ^ δ) := by
  obtain ⟨A, hA, ha⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := q / 2) (c := c / 2) (c' := c / 4) hδ (by linarith)
  refine ⟨Real.sqrt (B * D) * (A + 1), by positivity, fun n hn => ?_⟩
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have he : Real.sqrt ((B * n ^ q) * (D * Real.exp (-c * n ^ δ))) =
      Real.sqrt (B * D) * (n ^ (q / 2) * Real.exp (-(c / 2) * n ^ δ)) := by
    rw [show (B * n ^ q) * (D * Real.exp (-c * n ^ δ)) =
      (B * D) * (n ^ q * Real.exp (-c * n ^ δ)) by ring,
      Real.sqrt_mul (by positivity)]
    rw [Real.sqrt_mul (by positivity : 0 ≤ n ^ q)]
    congr 1
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hn0.le,
      ← Real.exp_mul]
    congr 2 <;> ring
  rw [he]
  apply (mul_le_mul_of_nonneg_left (ha n hn) (Real.sqrt_nonneg _)).trans
  nlinarith [Real.sqrt_nonneg (B * D), Real.exp_pos (-(c / 4) * n ^ δ)]

/-- See Subsection 6.1 of the paper: the Schur prefactor grows at most linearly in
temperature. Its constant is chosen before temperature, so these bounds
are uniform on every bounded positive temperature interval. -/
theorem schur_temperature_profiles (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : InverseTemperature)
      (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (k : ℕ) (hk : 1 ≤ k)
      (hkm : k ≤ (M : ℕ)/4) (n : ℕ), n ≤ (M : ℕ) →
      ∀ {α : Type} [MeasurableSpace α] (ν : Measure α)
        (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
        (φ ψ : Lp ℝ 2 ν) (i j l : Fin (M : ℕ)),
      i.val < n → j.val < n → l.val < n →
      |InterpolationMatrix.schurPointPair ν Q hQ s β M hM k hk hkm n φ ψ j i| ≤
        β.val*C*(k : ℝ)^2*(min (i.val+1) (n-i.val) : ℕ)^(-s.val/2)*
          (min (j.val+1) (n-j.val) : ℕ)^(-s.val/2)*‖φ‖*‖ψ‖ ∧
      |InterpolationMatrix.schurIncrementPair ν Q hQ s β M hM k hk hkm n φ ψ j i l| ≤
        β.val*C*(k : ℝ)^2*(Nat.dist i.val l.val : ℝ)*
          (min (j.val+1) (n-j.val) : ℕ)^(-s.val/2)*
          (min (min (i.val+1) (n-i.val)) (min (l.val+1) (n-l.val)) : ℕ)^(-1-s.val/2)*‖φ‖*‖ψ‖ := by
  obtain ⟨B, hB, hforce⟩ := ExteriorForces.exterior_force_bounds hz s
  refine ⟨B^2, by positivity, ?_⟩
  intro β M hM k hk hkm n hn α _ ν Q hQ φ ψ i j l hi hj hl
  let E := InterpolationMatrix.exteriorIndices M n
  let D := InterpolationMatrix.referenceExteriorMatrix s M hM k n
  let col := InterpolationMatrix.referenceColumn s M hM k n
  have hD : D.PosDef := (ExteriorForces.exteriorBlock_posDef s M hM hk hkm E).1
  obtain ⟨a, ha, hlo⟩ := BoundarySchurBounds.reference_exterior_lower s M hM k hk hkm E β.val β.property
  let F := InterpolationMatrix.referenceExteriorForm ν Q hQ s β M hM k hk hkm n
  let R := CoerciveSolution.solution F (min 1 a) (lt_min zero_lt_one ha)
    (BoundarySchurBounds.constantForm_coercive Q hQ _ _ a hlo)
    (OperatorSchur.vectorValues Q hQ)
  have heq : R = InterpolationMatrix.referenceResolvent ν Q hQ s β M hM k hk hkm n :=
    InterpolationMatrix.referenceResolvent_unique ν Q hQ s β M hM k hk hkm n R
      (CoerciveSolution.solution_solves _ _ _ _ _)
  obtain ⟨hpoint, hinc⟩ := hforce M hM k hk hkm n hn
  dsimp only at hpoint hinc
  have hquad (b : Fin (M : ℕ)) (hb : b.val < n) :
      col b ⬝ᵥ (D⁻¹ *ᵥ col b) ≤
        (B*k*(min (b.val+1) (n-b.val) : ℕ)^(-s.val/2))^2 := by
    rw [← BoundarySchurBounds.gaussian_quadratic_norm hD.inv.posSemidef (col b)]
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg (hpoint b hb).2 2
  have hdiff : (col i-col l) ⬝ᵥ (D⁻¹ *ᵥ (col i-col l)) ≤
      (B*k*(Nat.dist i.val l.val : ℝ)*
        (min (min (i.val+1) (n-i.val)) (min (l.val+1) (n-l.val)) : ℕ)^(-1-s.val/2))^2 := by
    rw [← BoundarySchurBounds.gaussian_quadratic_norm hD.inv.posSemidef (col i-col l)]
    have hid : (fun z : EuclideanSpace ℝ E => ∑ a, (col i-col l) a*z a) =
        (fun z => ∑ a, col i a*z a)-(fun z => ∑ a, col l a*z a) := by
      funext z
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    rw [hid]
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg (hinc i l hi hl).2 2
  have hp := BoundarySchurBounds.constant_resolvent_pair Q hQ hD β.val β.property a ha hlo
    (col j) (col i) φ ψ _ _ (by positivity) (by positivity) (hquad j hj) (hquad i hi)
  have hd := BoundarySchurBounds.constant_resolvent_pair Q hQ hD β.val β.property a ha hlo
    (col i-col l) (col j) ψ φ _ _ (by positivity) (by positivity) hdiff (hquad j hj)
  change |inner ℝ (BoundarySchurBounds.tensor (col j) φ)
    (OperatorSchur.vectorValues Q hQ (R (BoundarySchurBounds.tensor (col i) ψ)))| ≤ _ at hp
  change |inner ℝ (BoundarySchurBounds.tensor (col i-col l) ψ)
    (OperatorSchur.vectorValues Q hQ (R (BoundarySchurBounds.tensor (col j) φ)))| ≤ _ at hd
  rw [heq] at hp hd
  have hβ : β.val^2*β.val⁻¹ = β.val := by
    field_simp [β.property.ne']
  constructor
  · unfold InterpolationMatrix.schurPointPair
    rw [abs_mul, abs_of_nonneg (sq_nonneg β.val)]
    apply (mul_le_mul_of_nonneg_left hp (sq_nonneg β.val)).trans_eq
    calc
      _ = (β.val^2*β.val⁻¹)*B^2*(k : ℝ)^2*
          (min (i.val+1) (n-i.val) : ℕ)^(-s.val/2)*
          (min (j.val+1) (n-j.val) : ℕ)^(-s.val/2)*‖φ‖*‖ψ‖ := by ring
      _ = _ := by rw [hβ]
  · have hsym := InterpolationMatrix.referenceResolvent_pair_symmetric ν Q hQ s β M hM k hk hkm n
      (BoundarySchurBounds.tensor (col j) φ) (BoundarySchurBounds.tensor (col i-col l) ψ)
    change |β.val^2*inner ℝ (BoundarySchurBounds.tensor (col j) φ)
      (OperatorSchur.vectorValues Q hQ (InterpolationMatrix.referenceResolvent ν Q hQ s β M hM k hk hkm n
        (BoundarySchurBounds.tensor (col i-col l) ψ)))| ≤ _
    rw [hsym, abs_mul, abs_of_nonneg (sq_nonneg β.val)]
    apply (mul_le_mul_of_nonneg_left hd (sq_nonneg β.val)).trans_eq
    calc
      _ = (β.val^2*β.val⁻¹)*B^2*(k : ℝ)^2*(Nat.dist i.val l.val : ℝ)*
          (min (j.val+1) (n-j.val) : ℕ)^(-s.val/2)*
          (min (min (i.val+1) (n-i.val)) (min (l.val+1) (n-l.val)) : ℕ)^(-1-s.val/2)*‖φ‖*‖ψ‖ := by ring
      _ = _ := by rw [hβ]

/-- See Subsection 6.1 of the paper: both already constructed Schur pairings with
the prescribed cutoff loss. The structural exponent `2*h*K` precedes
epsilon and temperature. This holds over any closed scalar form. -/
theorem schur_cutoff_profiles (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (h : ℕ) (K : ℝ) (β : InverseTemperature) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, ∀ (n : ℕ+) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
      (hnM : (n : ℕ) ≤ (M : ℕ)),
      let k := ⌊(n : ℝ) ^ (K * ε)⌋₊ ^ h
      ∀ (hk : 1 ≤ k) (hkm : k ≤ (M : ℕ) / 4),
      ∀ {α : Type} [MeasurableSpace α] (ν : Measure α)
        (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
        (φ η : Lp ℝ 2 ν) (i j l : Fin (n : ℕ)),
        |InterpolationMatrix.schurPointPair ν Q hQ s β M hM k hk hkm n
          φ η (j.castLE hnM) (i.castLE hnM)| ≤
          C * (n : ℝ) ^ ((2 * h * K) * ε) *
            (min (i.val + 1) ((n : ℕ) - i.val) : ℕ) ^ (-s.val / 2) *
            (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) ^ (-s.val / 2) * ‖φ‖ * ‖η‖ ∧
        |InterpolationMatrix.schurIncrementPair ν Q hQ s β M hM k hk hkm n
          φ η (j.castLE hnM) (i.castLE hnM) (l.castLE hnM)| ≤
          C * (n : ℝ) ^ ((2 * h * K) * ε) * (Nat.dist i.val l.val : ℝ) *
            (min (j.val + 1) ((n : ℕ) - j.val) : ℕ) ^ (-s.val / 2) *
            (min (min (i.val + 1) ((n : ℕ) - i.val))
              (min (l.val + 1) ((n : ℕ) - l.val)) : ℕ) ^ (-1 - s.val / 2) * ‖φ‖ * ‖η‖ := by
  obtain ⟨C, hC, hb⟩ := InterpolationMatrix.schur_pair_bounds hz s β
  refine ⟨C, hC, ?_⟩
  intro ε n M hM hnM k hk hkm α _ ν Q hQ φ η i j l
  have hcut : (k : ℝ) ^ 2 ≤ (n : ℝ) ^ ((2 * h * K) * ε) := by
    have hh := BoundarySchurBounds.cutoff_sq_le n h n.pos (K * ε)
    simpa only [show (2 * (h : ℝ)) * (K * ε) = (2 * h * K) * ε by ring] using hh
  obtain ⟨hp, hd⟩ := hb M hM k hk hkm n hnM ν Q hQ φ η
    (i.castLE hnM) (j.castLE hnM) (l.castLE hnM) i.isLt j.isLt l.isLt
  simp only [Fin.val_castLE] at hp hd
  constructor
  · exact hp.trans (by gcongr)
  · exact hd.trans (by gcongr)

/-- See Subsection 6.1 of the paper: the prescribed-cutoff Schur estimates uniformly
for all positive temperatures below a fixed upper endpoint. No loss or
tail exponent is selected after that temperature endpoint. -/
theorem schur_cutoff_profiles_compact (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (h : ℕ) (K βhi : ℝ) (hβhi : 0 < βhi) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : InverseTemperature), β.val ≤ βhi →
      ∀ (ε : ℝ) (n M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : (n : ℕ) ≤ (M : ℕ)),
      let k := ⌊(n : ℝ)^(K*ε)⌋₊^h
      ∀ (hk : 1 ≤ k) (hkm : k ≤ (M : ℕ)/4),
      ∀ {α : Type} [MeasurableSpace α] (ν : Measure α)
        (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
        (φ ψ : Lp ℝ 2 ν) (i j l : Fin (n : ℕ)),
      |InterpolationMatrix.schurPointPair ν Q hQ s β M hM k hk hkm n φ ψ
        (j.castLE hnM) (i.castLE hnM)| ≤
        C*(n : ℝ)^((2*h*K)*ε)*
          (min (i.val+1) ((n : ℕ)-i.val) : ℕ)^(-s.val/2)*
          (min (j.val+1) ((n : ℕ)-j.val) : ℕ)^(-s.val/2)*‖φ‖*‖ψ‖ ∧
      |InterpolationMatrix.schurIncrementPair ν Q hQ s β M hM k hk hkm n φ ψ
        (j.castLE hnM) (i.castLE hnM) (l.castLE hnM)| ≤
        C*(n : ℝ)^((2*h*K)*ε)*(Nat.dist i.val l.val : ℝ)*
          (min (j.val+1) ((n : ℕ)-j.val) : ℕ)^(-s.val/2)*
          (min (min (i.val+1) ((n : ℕ)-i.val))
            (min (l.val+1) ((n : ℕ)-l.val)) : ℕ)^(-1-s.val/2)*‖φ‖*‖ψ‖ := by
  obtain ⟨B, hB, hb⟩ := schur_temperature_profiles hz s
  refine ⟨βhi*B, by positivity, ?_⟩
  intro β hβ ε n M hM hnM k hk hkm α _ ν Q hQ φ ψ i j l
  obtain ⟨hp, hd⟩ := hb β M hM k hk hkm n hnM ν Q hQ φ ψ
    (i.castLE hnM) (j.castLE hnM) (l.castLE hnM) i.isLt j.isLt l.isLt
  simp only [Fin.val_castLE] at hp hd
  have htemp : β.val*B ≤ βhi*B := mul_le_mul_of_nonneg_right hβ hB.le
  have hcut : (k : ℝ)^2 ≤ (n : ℝ)^((2*h*K)*ε) := by
    have hh := BoundarySchurBounds.cutoff_sq_le n h n.pos (K*ε)
    simpa only [show (2*(h : ℝ))*(K*ε) = (2*h*K)*ε by ring] using hh
  exact ⟨hp.trans (by gcongr), hd.trans (by gcongr)⟩

/-- See Subsection 6.1 of the paper: all entries of the full reference matrix are
uniformly bounded, independently of its component period and cutoff. -/
theorem reference_entry_bound (s : Riesz1.RieszExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (k : ℕ)
      (i j : Fin (M : ℕ)), |2 * referenceIntervalMatrix s M hM k i j| ≤ C := by
  obtain ⟨C, hC, hb⟩ := PhysicalCore.Internal.referenceInternal_entry_bound s
  refine ⟨C, hC, fun M hM k i j => ?_⟩
  have he := BoundaryEntries.referenceInternal_add_crossing s M hM k M le_rfl i j
  rw [BoundaryEntries.referenceCrossing_full, Matrix.zero_apply, add_zero] at he
  simp only [Fin.castLE_refl] at he
  rw [← he]
  apply (hb M hM k M le_rfl i j).trans
  have hp : (1 + (Riesz1.cyclicIndexDistance M i j : ℝ)) ^ (-s.val) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by have := Nat.cast_nonneg (Riesz1.cyclicIndexDistance M i j) (α := ℝ); linarith) (by linarith [s.property.1])
  simpa only [mul_one, Fin.castLE_refl] using mul_le_mul_of_nonneg_left hp hC.le

/-- See Subsection 6.1 of the paper: the prescribed bad branch of the exact
multiplication defect inherits the whole-simplex sum-of-squares envelope.
Only the reference matrix is added. Its period introduces no loss. -/
theorem multiplication_bad_square_internal (s : Riesz1.RieszExponent) :
    ∃ A : ℝ, 0 < A ∧ ∀ (β : InverseTemperature)
      (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
      (hnM : (n : ℕ) ≤ (M : ℕ)) (k : ℕ) (θ : PhysicalCutoff) (ε η t : ℝ)
      (P : AffineSimplex.chartDomain n ((n+d : ℕ)+1) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
      (B : ℝ), 0 ≤ B →
      ∀ x : AffineSimplex.chartDomain n ((n+d : ℕ)+1),
      x ∉ InterpolationMatrix.goodSet s n d η → ∀ i j : Fin (n : ℕ),
      |P x i j| ^ 2 + |InterpolationMatrix.penaltyHessian n θ ε x.val i j| ^ 2 ≤
        B * (n : ℝ) ^ B * InterpolantLocalLaws.exceptionalWeight s.val (WithLp.ofLp x.val) →
      |InterpolationMatrix.multiplicationPart β s n d e hde M hM hnM k θ ε η t P x i j| ^ 2 ≤
        (3 * β.val ^ 2 * (B + A ^ 2)) * (n : ℝ) ^ B *
          InterpolantLocalLaws.exceptionalWeight s.val (WithLp.ofLp x.val) := by
  obtain ⟨A, hA, hb⟩ := reference_entry_bound s
  refine ⟨A, hA, fun β n d e hde M hM hnM k θ ε η t P B hB x hx i j hs => ?_⟩
  have hr := hb M hM k (i.castLE hnM) (j.castLE hnM)
  have hr2 := pow_le_pow_left₀ (abs_nonneg _) hr 2
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hp : 1 ≤ (n : ℝ) ^ B := Real.one_le_rpow hn1 hB
  have hw : 1 ≤ InterpolantLocalLaws.exceptionalWeight s.val (WithLp.ofLp x.val) :=
    InterpolantLocalLaws.one_le_exceptionalWeight s.val _ (fun i => (x.property.1 i).le)
  have hscale : 1 ≤ (n : ℝ) ^ B *
      InterpolantLocalLaws.exceptionalWeight s.val (WithLp.ofLp x.val) := by nlinarith
  have hr2' := mul_le_mul_of_nonneg_left hscale (sq_nonneg A)
  rw [InterpolationMatrix.multiplicationPart, ite_eq_right hx]
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.submatrix_apply, smul_eq_mul, sq_abs, mul_pow]
  simp only [sq_abs] at hs hr2
  have halg (a b c : ℝ) : (a + b - c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    nlinarith [sq_nonneg (a-b), sq_nonneg (a+c), sq_nonneg (b+c)]
  have hh := halg (InterpolationMatrix.penaltyHessian n θ ε x.val i j)
    (P x i j) (2 * referenceIntervalMatrix s M hM k (i.castLE hnM) (j.castLE hnM))
  have hs' : (InterpolationMatrix.penaltyHessian n θ ε x.val i j + P x i j -
      2 * referenceIntervalMatrix s M hM k (i.castLE hnM) (j.castLE hnM)) ^ 2 ≤
      3 * (B + A ^ 2) * (n : ℝ) ^ B *
        InterpolantLocalLaws.exceptionalWeight s.val (WithLp.ofLp x.val) := by
    nlinarith only [hs, hr2, hr2', hh]
  convert mul_le_mul_of_nonneg_left hs' (sq_nonneg β.val) using 1; ring

/-- See Subsection 6.1 of the paper: the real square integral of an L² scalar is
its squared Hilbert norm. -/
theorem scalar_two_norm (α : Type*) [MeasurableSpace α] (ν : Measure α)
    (φ : Lp ℝ 2 ν) : Real.sqrt (∫ x, φ x ^ 2 ∂ν) = ‖φ‖ := by
  have he : (∫ x, φ x ^ 2 ∂ν) = ‖φ‖ ^ 2 := by
    have hh := real_inner_self_eq_norm_sq φ
    rw [L2.inner_def] at hh
    simpa only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs] using hh
  rw [he, Real.sqrt_sq (norm_nonneg _)]

/-- See Subsection 6.1 of the paper: for an essentially bounded scalar, the finite
real supremum appearing in the pairing estimates is a valid a.e. bound.
The finiteness premise excludes the junk value of `ENNReal.toReal`. -/
theorem essential_scalar_bound_internal {α : Type*} [MeasurableSpace α]
    {ν : Measure α} (φ : Lp ℝ 2 ν) (hφ : MemLp (φ : α → ℝ) ∞ ν) :
    ∀ᵐ x ∂ν, |φ x| ≤ (eLpNorm (φ : α → ℝ) ∞ ν).toReal := by
  filter_upwards [enorm_ae_le_eLpNormEssSup (φ : α → ℝ) ν] with x hx
  have hh := ENNReal.toReal_mono hφ.ne
    (hx.trans (eLpNormEssSup_le_eLpNorm_top (f := (φ : α → ℝ))))
  simpa only [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _)] using hh

section PairIdentities

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- See Subsection 6.1 of the paper: the entry pairing of the multiplication field
uses the existing pointwise matrix pairing, up to its L² representatives. -/
theorem matrix_point_pair_ae_internal (Y : α → Matrix ι ι ℝ)
    (φ η : Lp ℝ 2 ν) (j i : ι) :
    matrixFieldPair Y ((Pi.single j φ : ι → Lp ℝ 2 ν)) ((Pi.single i η : ι → Lp ℝ 2 ν)) =ᵐ[ν]
      fun x => φ x * η x * Y x j i := by
  filter_upwards [Lp.coeFn_zero ℝ 2 ν] with x hx
  have hφ (a : ι) : ((Pi.single j φ : ι → Lp ℝ 2 ν) a : Lp ℝ 2 ν) x = if a = j then φ x else 0 := by
    by_cases ha : a = j
    · subst a; simp only [Pi.single_eq_same, ite_true]
    · simp only [Pi.single_eq_of_ne ha, ha, ite_false, hx, Pi.zero_apply]
  have hη (a : ι) : ((Pi.single i η : ι → Lp ℝ 2 ν) a : Lp ℝ 2 ν) x = if a = i then η x else 0 := by
    by_cases ha : a = i
    · subst a; simp only [Pi.single_eq_same, ite_true]
    · simp only [Pi.single_eq_of_ne ha, ha, ite_false, hx, Pi.zero_apply]
  simp only [matrixFieldPair, hφ, hη]
  simp only [ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- See Subsection 6.1 of the paper: column differences keep their exact signed
cancellation in the multiplication pairing. -/
theorem matrix_increment_pair_ae_internal (Y : α → Matrix ι ι ℝ)
    (φ η : Lp ℝ 2 ν) (j i l : ι) :
    matrixFieldPair Y ((Pi.single j φ : ι → Lp ℝ 2 ν)) ((Pi.single i η : ι → Lp ℝ 2 ν) - (Pi.single l η : ι → Lp ℝ 2 ν)) =ᵐ[ν]
      fun x => φ x * η x * (Y x j i - Y x j l) := by
  have hsub : ∀ᵐ x ∂ν, ∀ a : ι,
      (((Pi.single i η : ι → Lp ℝ 2 ν) - (Pi.single l η : ι → Lp ℝ 2 ν)) a) x =
        ((Pi.single i η : ι → Lp ℝ 2 ν) a) x - ((Pi.single l η : ι → Lp ℝ 2 ν) a) x := by
    exact ae_all_iff.mpr fun a => Lp.coeFn_sub _ _
  filter_upwards [hsub, matrix_point_pair_ae_internal Y φ η j i,
    matrix_point_pair_ae_internal Y φ η j l] with x hx hi hl
  change (∑ a, ∑ b, _ * Y x a b * _) = _
  simp only [hx, mul_sub, Finset.sum_sub_distrib]
  change matrixFieldPair Y ((Pi.single j φ : ι → Lp ℝ 2 ν)) ((Pi.single i η : ι → Lp ℝ 2 ν)) x -
    matrixFieldPair Y ((Pi.single j φ : ι → Lp ℝ 2 ν)) ((Pi.single l η : ι → Lp ℝ 2 ν)) x = _
  rw [hi, hl]

/-- See Subsection 6.1 of the paper: the exterior tensor of a point source is its
single reference column, with no component-period factor. -/
theorem tensor_point_sum_internal {κ : Type*} [Fintype κ]
    (col : ι → κ → ℝ) (η : Lp ℝ 2 ν) (i : ι) :
    (∑ a : ι, BoundarySchurBounds.tensor (col a) ((Pi.single i η : ι → Lp ℝ 2 ν) a)) =
      BoundarySchurBounds.tensor (col i) η := by
  rw [Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same]
  · intro a _ hai
    simp only [Pi.single_eq_of_ne hai, BoundarySchurBounds.tensor, smul_zero]
    rfl
  · simp

/-- See Subsection 6.1 of the paper: tensorizing a source column difference gives
exactly the difference of the two reference columns. -/
theorem tensor_increment_sum_internal {κ : Type*} [Fintype κ]
    (col : ι → κ → ℝ) (η : Lp ℝ 2 ν) (i l : ι) :
    (∑ a : ι, BoundarySchurBounds.tensor (col a)
      (((Pi.single i η : ι → Lp ℝ 2 ν) - (Pi.single l η : ι → Lp ℝ 2 ν)) a)) =
      BoundarySchurBounds.tensor (col i - col l) η := by
  have ht (v : κ → ℝ) (f g : Lp ℝ 2 ν) :
      BoundarySchurBounds.tensor v (f - g) =
        BoundarySchurBounds.tensor v f - BoundarySchurBounds.tensor v g := by
    apply PiLp.ext
    intro a
    exact smul_sub _ _ _
  simp only [Pi.sub_apply, ht, Finset.sum_sub_distrib,
    tensor_point_sum_internal]
  apply PiLp.ext
  intro a
  exact (sub_smul _ _ _).symm

end PairIdentities

section PerturbationIdentities

variable (β : InverseTemperature) (s : Riesz1.RieszExponent)
  (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
  (hnM : (n : ℕ) ≤ (M : ℕ)) (k : ℕ) (hk : 1 ≤ k) (hkm : k ≤ (M : ℕ) / 4)
  (θ : PhysicalCutoff) (ε η t : ℝ)
  (ν : Measure (AffineSimplex.chartDomain n ((n+d : ℕ)+1)))
  (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
  (P : AffineSimplex.chartDomain n ((n+d : ℕ)+1) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)

/-- See Subsection 6.1 of the paper: the complete perturbation on point tests is
exactly its physical multiplication integral plus its unique-resolvent
Schur pairing. The integrability certificate is retained explicitly. -/
theorem perturbation_point_eq_internal (φ ψ : Lp ℝ 2 ν) (j i : Fin (n : ℕ))
    (hint : Integrable (matrixFieldPair
      (InterpolationMatrix.multiplicationPart β s n d e hde M hM hnM k θ ε η t P)
      (Pi.single j φ) (Pi.single i ψ)) ν) :
    InterpolationMatrix.perturbationPair β s n d e hde M hM hnM k hk hkm
      θ ε η t ν Q hQ P (Pi.single j φ) (Pi.single i ψ) hint =
    (∫ x, φ x * ψ x *
      InterpolationMatrix.multiplicationPart β s n d e hde M hM hnM k θ ε η t P x j i ∂ν) +
    InterpolationMatrix.schurPointPair ν Q hQ s β M hM k hk hkm n φ ψ
      (j.castLE hnM) (i.castLE hnM) := by
  rw [InterpolationMatrix.perturbationPair, integral_congr_ae
    (matrix_point_pair_ae_internal _ φ ψ j i)]
  rw [tensor_point_sum_internal, tensor_point_sum_internal]
  rfl

/-- See Subsection 6.1 of the paper: the analogous identity for column differences,
including the exact signed reference-column increment. -/
theorem perturbation_increment_eq_internal (φ ψ : Lp ℝ 2 ν) (j i l : Fin (n : ℕ))
    (hint : Integrable (matrixFieldPair
      (InterpolationMatrix.multiplicationPart β s n d e hde M hM hnM k θ ε η t P)
      (Pi.single j φ) (fun a : Fin (n : ℕ) => (Pi.single i ψ : Fin (n : ℕ) → Lp ℝ 2 ν) a -
        (Pi.single l ψ : Fin (n : ℕ) → Lp ℝ 2 ν) a)) ν) :
    InterpolationMatrix.perturbationPair β s n d e hde M hM hnM k hk hkm
      θ ε η t ν Q hQ P (Pi.single j φ) (fun a : Fin (n : ℕ) => (Pi.single i ψ : Fin (n : ℕ) → Lp ℝ 2 ν) a -
        (Pi.single l ψ : Fin (n : ℕ) → Lp ℝ 2 ν) a) hint =
    (∫ x, φ x * ψ x *
      (InterpolationMatrix.multiplicationPart β s n d e hde M hM hnM k θ ε η t P x j i -
        InterpolationMatrix.multiplicationPart β s n d e hde M hM hnM k θ ε η t P x j l) ∂ν) +
    InterpolationMatrix.schurIncrementPair ν Q hQ s β M hM k hk hkm n φ ψ
      (j.castLE hnM) (i.castLE hnM) (l.castLE hnM) := by
  have hcol := tensor_increment_sum_internal
    (fun a : Fin (n : ℕ) => InterpolationMatrix.referenceColumn s M hM k n (a.castLE hnM)) ψ i l
  simp only [Pi.sub_apply] at hcol
  unfold InterpolationMatrix.perturbationPair InterpolationMatrix.schurIncrementPair
  rw [tensor_point_sum_internal, hcol]
  congr 1
  exact integral_congr_ae (matrix_increment_pair_ae_internal _ φ ψ j i l)

end PerturbationIdentities

/-- See Subsection 6.1 of the paper: assembly of both perturbation estimates, with
actual integrability certificates. This is an internal implication: the
physical good-set profiles and whole-simplex square bound must still be
supplied. The structural loss is chosen before epsilon and temperature. The tail power is an input and is preserved without alteration. -/
theorem perturbation_bounds_from_profiles_internal (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (h : ℕ) (K ρ : ℝ) (hρ : 0 < ρ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε δ : ℝ, 0 ≤ ε → 0 < δ →
      ∀ (βhi A B D c : ℝ),
      0 < βhi → 0 < A → 0 < B → 0 < D → 0 < c → ∃ C : ℝ, 0 < C ∧
      ∀ (β : InverseTemperature), β.val ≤ βhi →
      ∀ (n : ℕ+) (d e : ℕ) (hde : d ≤ e) (M : ℕ+) (hM : 2 ≤ (M : ℕ))
        (hnM : (n : ℕ) ≤ (M : ℕ)),
      let k := ⌊(n : ℝ) ^ (K * ε)⌋₊ ^ h
      ∀ (hk : 1 ≤ k) (hkm : k ≤ (M : ℕ) / 4) (θ : PhysicalCutoff) (t : ℝ)
        (ν : Measure (AffineSimplex.chartDomain n ((n+d : ℕ)+1)))
        [IsProbabilityMeasure ν] (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
        (P : AffineSimplex.chartDomain n ((n+d : ℕ)+1) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ),
      (∀ i j, Measurable (fun x => P x i j)) →
      let Y := InterpolationMatrix.multiplicationPart β s n d e hde M hM hnM k θ ε (K*ε) t P
      let W := fun x : AffineSimplex.chartDomain n ((n+d : ℕ)+1) =>
        InterpolantLocalLaws.exceptionalWeight s.val (WithLp.ofLp x.val)
      let G := InterpolationMatrix.goodSet s n d (K*ε)
      let w : Fin (n : ℕ) → ℝ := fun i =>
        (min (i.val+1) ((n : ℕ)-i.val) : ℕ) ^ (-s.val/2)
      let v : Fin (n : ℕ) → Fin (n : ℕ) → Fin (n : ℕ) → ℝ := fun j i l => (Nat.dist i.val l.val : ℝ) * w j *
        (min (min (i.val+1) ((n : ℕ)-i.val))
          (min (l.val+1) ((n : ℕ)-l.val)) : ℕ) ^ (-1-s.val/2)
      (∀ᵐ x ∂ν.restrict G, ∀ i j l,
        |Y x j i| ≤ A*(n : ℝ)^(ρ*ε)*w i*w j ∧
        |Y x j i-Y x j l| ≤ A*(n : ℝ)^(ρ*ε)*v j i l) →
      (∀ᵐ x ∂ν.restrict Gᶜ, ∀ i j,
        |P x i j|^2 + |InterpolationMatrix.penaltyHessian n θ ε x.val i j|^2 ≤
          B*(n : ℝ)^B*W x) →
      (∫⁻ x in Gᶜ, ENNReal.ofReal (W x) ∂ν) ≤
        ENNReal.ofReal (D*Real.exp (-c*(n : ℝ)^δ)) →
      ∀ (φ ψ : Lp ℝ 2 ν) (Mφ Mψ : ℝ), 0 ≤ Mφ → 0 ≤ Mψ →
      (∀ᵐ x ∂ν, |φ x| ≤ Mφ) → (∀ᵐ x ∂ν, |ψ x| ≤ Mψ) →
      ∀ i j l : Fin (n : ℕ),
      ∃ hp : Integrable (matrixFieldPair Y (Pi.single j φ) (Pi.single i ψ)) ν,
      ∃ hd : Integrable (matrixFieldPair Y (Pi.single j φ)
        (fun a : Fin (n : ℕ) => (Pi.single i ψ : Fin (n : ℕ) → Lp ℝ 2 ν) a - (Pi.single l ψ : Fin (n : ℕ) → Lp ℝ 2 ν) a)) ν,
        |InterpolationMatrix.perturbationPair β s n d e hde M hM hnM k hk hkm θ ε (K*ε) t
          ν Q hQ P (Pi.single j φ) (Pi.single i ψ) hp| ≤
          C*(n : ℝ)^(κ*ε)*w i*w j*‖φ‖*‖ψ‖ +
            C*Real.exp (-(c/4)*(n : ℝ)^δ)*(Mφ*Mψ) ∧
        |InterpolationMatrix.perturbationPair β s n d e hde M hM hnM k hk hkm θ ε (K*ε) t
          ν Q hQ P (Pi.single j φ)
          (fun a : Fin (n : ℕ) => (Pi.single i ψ : Fin (n : ℕ) → Lp ℝ 2 ν) a - (Pi.single l ψ : Fin (n : ℕ) → Lp ℝ 2 ν) a) hd| ≤
          C*(n : ℝ)^(κ*ε)*v j i l*‖φ‖*‖ψ‖ +
            C*Real.exp (-(c/4)*(n : ℝ)^δ)*(Mφ*Mψ) := by
  let κ := max ρ (2*h*K)
  refine ⟨κ, lt_of_lt_of_le hρ (le_max_left _ _), ?_⟩
  intro ε δ hε hδ βhi A B D c hβhi hA hB hD hc
  obtain ⟨Cs, hCs, hs⟩ := schur_cutoff_profiles_compact hz s h K βhi hβhi
  obtain ⟨Ar, hAr, hbad⟩ := multiplication_bad_square_internal s
  let Bb := 3*βhi^2*(B+Ar^2)
  have hBb : 0 < Bb := by dsimp [Bb]; positivity
  obtain ⟨Ce, hCe, he⟩ := weighted_tail_absorption_internal
    (q := B) hδ hc (by positivity : 0 < 4*Bb) hD
  refine ⟨A+Cs+Ce, by positivity, ?_⟩
  intro β hβ n d e hde M hM hnM k hk hkm θ t ν _ Q hQ P hP Y W G w v hg hwhole htail
    φ ψ Mφ Mψ hMφ hMψ hφ hψ i j l
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hw (a) : 0 ≤ w a := by dsimp only [w]; positivity
  have hv : 0 ≤ v j i l := by dsimp [v]; positivity
  have hmeas (a b) : Measurable (fun x => Y x a b) :=
    InterpolationMatrix.measurable_multiplicationPart β s n d e hde M hM hnM k θ ε (K*ε) t P hP a b
  have hsq : ∀ᵐ x ∂ν.restrict Gᶜ, ∀ a b, |Y x a b|^2 ≤ Bb*(n : ℝ)^B*W x := by
    filter_upwards [hwhole, ae_restrict_mem (InterpolationMatrix.measurableSet_goodSet s n d (K*ε)).compl]
      with x hx hxe a b
    apply (hbad β n d e hde M hM hnM k θ ε (K*ε) t P B hB.le x hxe a b (hx a b)).trans
    have hβsq := pow_le_pow_left₀ β.property.le hβ 2
    have hwx : 0 ≤ W x := zero_le_one.trans
      (InterpolantLocalLaws.one_le_exceptionalWeight s.val _ (fun a => (x.property.1 a).le))
    dsimp only [Bb]
    gcongr
  have hsqP : ∀ᵐ x ∂ν.restrict Gᶜ, |Y x j i|^2 ≤ (4*Bb)*(n : ℝ)^B*W x := by
    filter_upwards [hsq] with x hx
    apply (hx j i).trans
    have hwx : 0 ≤ W x := zero_le_one.trans
      (InterpolantLocalLaws.one_le_exceptionalWeight s.val _ (fun a => (x.property.1 a).le))
    nlinarith [mul_nonneg (mul_nonneg hBb.le (Real.rpow_nonneg (zero_le_one.trans hn1) B)) hwx]
  have hsqD : ∀ᵐ x ∂ν.restrict Gᶜ, |Y x j i-Y x j l|^2 ≤ (4*Bb)*(n : ℝ)^B*W x := by
    filter_upwards [hsq] with x hx
    have hi := hx j i
    have hl := hx j l
    simp only [sq_abs] at hi hl ⊢
    nlinarith [sq_nonneg (Y x j i+Y x j l)]
  have hmp := multiplication_pair_internal
    (InterpolationMatrix.measurableSet_goodSet s n d (K*ε)) (hmeas j i)
    (Lp.stronglyMeasurable φ).measurable (Lp.stronglyMeasurable ψ).measurable
    (by positivity : 0 ≤ A*(n : ℝ)^(ρ*ε)*w i*w j)
    (by positivity : 0 ≤ (4*Bb)*(n : ℝ)^B) (by positivity)
    hMφ hMψ hφ hψ (Lp.memLp φ) (Lp.memLp ψ) (hg.mono fun x hx => (hx i j l).1) hsqP htail
  have hmd := multiplication_pair_internal
    (InterpolationMatrix.measurableSet_goodSet s n d (K*ε)) ((hmeas j i).sub (hmeas j l))
    (Lp.stronglyMeasurable φ).measurable (Lp.stronglyMeasurable ψ).measurable
    (by positivity : 0 ≤ A*(n : ℝ)^(ρ*ε)*v j i l)
    (by positivity : 0 ≤ (4*Bb)*(n : ℝ)^B) (by positivity)
    hMφ hMψ hφ hψ (Lp.memLp φ) (Lp.memLp ψ) (hg.mono fun x hx => (hx i j l).2) hsqD htail
  have hp := hmp.1.congr (matrix_point_pair_ae_internal Y φ ψ j i).symm
  have hd := hmd.1.congr (matrix_increment_pair_ae_internal Y φ ψ j i l).symm
  obtain ⟨hsp, hsd⟩ := hs β hβ ε n M hM hnM hk hkm ν Q hQ φ ψ i j l
  have hgpow : (n : ℝ)^(ρ*ε) ≤ (n : ℝ)^(κ*ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (mul_le_mul_of_nonneg_right (le_max_left _ _) hε)
  have hspow : (n : ℝ)^((2*h*K)*ε) ≤ (n : ℝ)^(κ*ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (mul_le_mul_of_nonneg_right (le_max_right _ _) hε)
  have htail' := he (n : ℝ) hn1
  rw [scalar_two_norm, scalar_two_norm] at hmp hmd
  have hpbound := (abs_add_le _ _).trans (add_le_add hmp.2 hsp)
  refine ⟨hp, hd, ?_, ?_⟩
  · rw [perturbation_point_eq_internal]
    apply hpbound.trans
    have hg' : A*(n : ℝ)^(ρ*ε)*w i*w j*(‖φ‖*‖ψ‖) ≤
        A*(n : ℝ)^(κ*ε)*w i*w j*‖φ‖*‖ψ‖ := by
      calc
        _ = A*(n : ℝ)^(ρ*ε)*w i*w j*‖φ‖*‖ψ‖ := by ring
        _ ≤ _ := by gcongr
    have hs' : Cs*(n : ℝ)^((2*h*K)*ε)*w i*w j*‖φ‖*‖ψ‖ ≤
        Cs*(n : ℝ)^(κ*ε)*w i*w j*‖φ‖*‖ψ‖ := by gcongr
    have he' := mul_le_mul_of_nonneg_right htail' (mul_nonneg hMφ hMψ)
    dsimp only [w] at hs'
    have hh := add_le_add (add_le_add hg' he') hs'
    apply hh.trans
    dsimp only [w]
    nlinarith only [mul_nonneg hCe.le (show 0 ≤ (n : ℝ)^(κ*ε)*
      (min (i.val+1) ((n : ℕ)-i.val) : ℕ)^(-s.val/2)*
      (min (j.val+1) ((n : ℕ)-j.val) : ℕ)^(-s.val/2)*‖φ‖*‖ψ‖ by positivity),
      mul_nonneg (add_nonneg hA.le hCs.le)
        (show 0 ≤ Real.exp (-(c/4)*(n : ℝ)^δ)*(Mφ*Mψ) by positivity)]
  · rw [perturbation_increment_eq_internal]
    have hg' : A*(n : ℝ)^(ρ*ε)*v j i l*(‖φ‖*‖ψ‖) ≤
        A*(n : ℝ)^(κ*ε)*v j i l*‖φ‖*‖ψ‖ := by
      calc
        _ = A*(n : ℝ)^(ρ*ε)*v j i l*‖φ‖*‖ψ‖ := by ring
        _ ≤ _ := by gcongr
    have hs' : Cs*(n : ℝ)^((2*h*K)*ε)*v j i l*‖φ‖*‖ψ‖ ≤
        Cs*(n : ℝ)^(κ*ε)*v j i l*‖φ‖*‖ψ‖ := by gcongr
    have he' := mul_le_mul_of_nonneg_right htail' (mul_nonneg hMφ hMψ)
    have hsd' : |InterpolationMatrix.schurIncrementPair ν Q hQ s β M hM k hk hkm n φ ψ
        (j.castLE hnM) (i.castLE hnM) (l.castLE hnM)| ≤
        Cs*(n : ℝ)^((2*h*K)*ε)*v j i l*‖φ‖*‖ψ‖ := by
      convert hsd using 1; dsimp [v, w]; ring
    have hdbound := (abs_add_le _ _).trans (add_le_add hmd.2 hsd')
    apply hdbound.trans
    have hh := add_le_add (add_le_add hg' he') hs'
    apply hh.trans
    nlinarith only [mul_nonneg hCe.le
        (show 0 ≤ (n : ℝ)^(κ*ε)*v j i l*‖φ‖*‖ψ‖ by positivity),
        mul_nonneg (add_nonneg hA.le hCs.le)
          (show 0 ≤ Real.exp (-(c/4)*(n : ℝ)^δ)*(Mφ*Mψ) by positivity)]

/-- See Subsection 6.1 of the paper: the reference crossing block itself has both
boundary power profiles. Its sole small loss is `n^ε`, with the exponent
one fixed before epsilon, cutoff and component period. -/
theorem reference_crossing_profiles (s : Riesz1.RieszExponent) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (n M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : (n : ℕ) ≤ (M : ℕ)) (k : ℕ),
      2*(n : ℕ) ≤ (M : ℕ) → ∀ i j l : Fin (n : ℕ),
      |BoundaryEntries.referenceCrossing s M hM k n hnM j i| ≤
        C*(n : ℝ)^ε*(min (i.val+1) ((n : ℕ)-i.val) : ℕ)^(-s.val/2)*
          (min (j.val+1) ((n : ℕ)-j.val) : ℕ)^(-s.val/2) ∧
      |BoundaryEntries.referenceCrossing s M hM k n hnM j i -
        BoundaryEntries.referenceCrossing s M hM k n hnM j l| ≤
        C*(n : ℝ)^ε*(Nat.dist i.val l.val : ℝ)*
          (min (j.val+1) ((n : ℕ)-j.val) : ℕ)^(-s.val/2)*
          (min (min (i.val+1) ((n : ℕ)-i.val))
            (min (l.val+1) ((n : ℕ)-l.val)) : ℕ)^(-1-s.val/2) := by
  intro ε hε
  obtain ⟨B, hB, hb⟩ := BoundaryEntries.referenceWeight_bound s
  obtain ⟨D, hD, hd⟩ := CrossingCoefficients.boundary_rank_profiles_internal s
  let A := 1+Real.log 2+1/ε
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 1 ≤ A := by dsimp [A]; have := one_div_pos.mpr hε; linarith
  refine ⟨D*B*A, by positivity, fun n M hM hnM k hhalf i j l => ?_⟩
  obtain ⟨hp, hi⟩ := hd M n hnM hhalf B hB.le
    (BoundaryEntries.referenceWeight s M hM k)
    (BoundaryEntries.referenceWeight_nonneg s M hM k) (hb M hM k)
  rw [← BoundaryEntries.referenceCrossing_eq_boundaryMatrix s M hM k n hnM] at hp hi
  simp only [← Nat.cast_min] at hi
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
  have hnε : 1 ≤ (n : ℝ)^ε := Real.one_le_rpow hn1 hε.le
  have hlog : Real.log (2*(n : ℝ)) ≤ A*(n : ℝ)^ε := by
    have hh := Real.log_le_rpow_div hn0.le hε
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0.ne']
    dsimp [A]
    rw [div_eq_mul_inv] at hh ⊢
    nlinarith
  have hscale : 1 ≤ A*(n : ℝ)^ε := by nlinarith
  constructor
  · apply (hp j i).trans
    calc
      _ ≤ D*B*(A*(n : ℝ)^ε)*
          (min (j.val+1) ((n : ℕ)-j.val) : ℕ)^(-s.val/2)*
          (min (i.val+1) ((n : ℕ)-i.val) : ℕ)^(-s.val/2) := by gcongr
      _ = _ := by ring
  · apply (hi j i l).trans
    have hDB : D*B ≤ D*B*(A*(n : ℝ)^ε) := by nlinarith [mul_pos hD hB]
    calc
      _ ≤ (D*B*(A*(n : ℝ)^ε))*(Nat.dist i.val l.val : ℝ)*
          (min (j.val+1) ((n : ℕ)-j.val) : ℕ)^(-s.val/2)*
          (min (min (i.val+1) ((n : ℕ)-i.val))
            (min (l.val+1) ((n : ℕ)-l.val)) : ℕ)^(-1-s.val/2) := by gcongr
      _ = _ := by rw [Nat.cast_min]; ring

end Riesz2.InterpolationPerturbation
