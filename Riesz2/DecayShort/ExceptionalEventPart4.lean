/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.ConditionalScoresPart3
public import Riesz2.DecayShort.ExceptionalEventPart3
public import Riesz2.HelfferSjostrand.PhysicalCollisionPart2
import all Riesz2.HelfferSjostrand.MarginalHessianPart5

/-!
# Hessian moments and exceptional operator estimates

Completion of the moment clauses of Subsection 4.5. The positive
marginal Hessian is bounded through its diagonal, retaining both penalties.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators ContDiff
namespace Riesz2.DecayShort.ExceptionalEvent

/-- A bilinear form on Euclidean space is bounded by the sum of the absolute
values of its entries. -/
private theorem norm_le_sum_entries {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ) :
    ‖A‖ ≤ ∑ i, ∑ j, |A (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| := by
  let e := fun i : ι => EuclideanSpace.single i (1 : ℝ)
  have hexp (u : EuclideanSpace ℝ ι) : u = ∑ i, u i • e i := by
    ext j
    simp [e, EuclideanSpace.single, Pi.single_apply]
  have heq (u v : EuclideanSpace ℝ ι) :
      A u v = ∑ i, ∑ j, u i * A (e i) (e j) * v j := by
    conv_lhs => rw [hexp u, hexp v]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hnn : 0 ≤ ∑ i, ∑ j, |A (e i) (e j)| := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ hnn
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hnn (norm_nonneg u))
  intro v
  rw [Real.norm_eq_abs, heq]
  calc
    _ ≤ ∑ i, ∑ j, |u i * A (e i) (e j) * v j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
        Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, ‖u‖ * |A (e i) (e j)| * ‖v‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_mul]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (PiLp.norm_apply_le u i) (abs_nonneg _))
        (PiLp.norm_apply_le v j) (abs_nonneg _) (by positivity)
    _ = _ := by simp only [← Finset.mul_sum, ← Finset.sum_mul]; ring

/-- Positivity and symmetry control every entry by its two diagonal entries. -/
private theorem abs_entry_le_diagonals {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E →L[ℝ] ℝ) (hs : ∀ u v, A u v = A v u)
    (hp : ∀ u, 0 ≤ A u u) (u v : E) : |A u v| ≤ (A u u + A v v) / 2 := by
  have hm := hp (u - v)
  have ha := hp (u + v)
  simp only [map_sub, sub_apply, map_add, add_apply] at hm ha
  rw [hs v u] at hm ha
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A positive symmetric form is bounded in operator norm by a polynomial
multiple of its trace. No choice of eigenvectors is needed. -/
private theorem norm_le_card_mul_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (hs : ∀ u v, A u v = A v u) (hp : ∀ u, 0 ≤ A u u) :
    ‖A‖ ≤ (Fintype.card ι : ℝ) * ∑ i, A (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
  refine (norm_le_sum_entries A).trans ?_
  calc
    _ ≤ ∑ i, ∑ j, (A (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) +
        A (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)) / 2 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        abs_entry_le_diagonals A hs hp _ _
    _ = _ := by
      simp only [add_div, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, ← Finset.sum_div, ← Finset.mul_sum ]
      ring


set_option backward.isDefEq.respectTransparency false in
/-- Internal penalty estimate for Subsection 4.5. Its constant is
uniform in the number of active gaps and in the scale `0 < a ≤ 1`. -/
theorem internal_penalty_diagonal (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (a : ℝ), 0 < a → a ≤ 1 → ∀ b : Bool,
      let F := fun x : EuclideanSpace ℝ (Fin n) =>
        ∑ i, (θ.val (a * x i) + if b then θ.val (a * (x i)⁻¹) else 0)
      ∀ (x : EuclideanSpace ℝ (Fin n)), (∀ i, 0 < x i) → ∀ i : Fin n,
        fderiv ℝ (fderiv ℝ F) x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) ≤
          C * (1 + (x i)⁻¹ ^ 4) := by
  classical
  obtain ⟨Cu,hCu,hu⟩ := PhysicalCollision.upper_penalty_curvature θ
  obtain ⟨Ci,hCi,hi⟩ := PhysicalCollision.inverse_penalty_curvature θ
  refine ⟨Cu + Ci, by positivity, ?_⟩
  intro n a ha ha1 b F x hx i
  let φ := fun t : ℝ => θ.val (a * t) + if b then θ.val (a / t) else 0
  have hφ (t : ℝ) (ht : 0 < t) : ContDiffAt ℝ 2 φ t := by
    have h₁ := (PhysicalCollision.cutoff_contDiffAt θ (mul_pos ha ht)).comp t
      (contDiffAt_const.mul contDiffAt_id)
    cases b
    · simpa only [φ, Bool.false_eq_true, ↓reduceIte, add_zero, Function.comp_def] using
        h₁.of_le (by norm_num)
    · have h₂ := (PhysicalCollision.cutoff_contDiffAt θ (div_pos ha ht)).comp t
        (contDiffAt_const.div contDiffAt_id ht.ne')
      simpa only [φ, ↓reduceIte, Function.comp_def, Pi.div_apply] using
        (h₁.add h₂).of_le (by norm_num)
  have hsecond (t : ℝ) (ht : 0 < t) : deriv (deriv φ) t ≤
      Cu * a ^ 2 + Ci * a ^ 2 * t⁻¹ ^ 4 := by
    cases b
    · simp only [φ, Bool.false_eq_true, ↓reduceIte, add_zero]
      exact (hu a t ha ht).2.trans (le_add_of_nonneg_right (by positivity))
    · have h₁ := (PhysicalCollision.cutoff_contDiffAt θ (mul_pos ha ht)).comp t
        (contDiffAt_const.mul contDiffAt_id)
      have h₂ := (PhysicalCollision.cutoff_contDiffAt θ (div_pos ha ht)).comp t
        (contDiffAt_const.div contDiffAt_id ht.ne')
      have hh := PhysicalCollision.internal_hessian_add
        (h₁.of_le (by norm_num)) (h₂.of_le (by norm_num)) 1 1
      simp only [PhysicalCollision.internal_scalar_hessian, mul_one, Function.comp_def] at hh
      change deriv (deriv (fun t => θ.val (a * t) + θ.val (a / t))) t ≤ _
      rw [hh]
      exact add_le_add (hu a t ha ht).2 (hi a t ha ht).2
  have he := (finite_linear_potential_derivatives (fun _ : Fin n => (1 : ℝ))
    (fun _ => φ) (fun j => EuclideanSpace.proj j) (fun _ => Ioi (0 : ℝ))
    (fun _ => isOpen_Ioi) (fun _ t ht => (hφ t ht).contDiffWithinAt) x hx
    (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)).2
  simp [EuclideanSpace.single, PiLp.single_apply] at he
  have hF : F = fun x => ∑ j, φ (x j) := by
    funext x
    simp only [F, φ, div_eq_mul_inv]
  rw [hF, he]
  have ha2 : a ^ 2 ≤ 1 := by nlinarith
  calc
    _ ≤ Cu * a ^ 2 + Ci * a ^ 2 * (x i)⁻¹ ^ 4 := hsecond _ (hx i)
    _ ≤ Cu + Ci * (x i)⁻¹ ^ 4 := add_le_add
      (mul_le_of_le_one_right hCu.le ha2)
      (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hCi.le ha2) (by positivity))
    _ ≤ (Cu + Ci) * (1 + (x i)⁻¹ ^ 4) := by
      nlinarith [mul_nonneg hCu.le (pow_nonneg ((inv_pos.mpr (hx i)).le) 4)]

set_option backward.isDefEq.respectTransparency false in
/-- Internal translation bridge for Subsection 4.5: conditional
Hessian integrals on the centred exterior hyperplane retain their affine conditional interval-matrix values. -/
theorem internal_centred_hessian_mean (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (U : EuclideanSpace ℝ (Fin (n + m + 1)) → ℝ)
    (hv : ∀ y : {y : EuclideanSpace ℝ (Fin (n + m + 1)) //
        y ∈ gapAmbientDomain (n + m).succPNat},
      U y.val = p.val.1 * physicalAmbientGapEnergy p (n + m).succPNat y)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1))
    (ρ : Measure (EuclideanSpace ℝ (Fin m)))
    (hmap : ρ.map (fun z => z + AffineSimplex.coordinates m
      (AffineSimplex.centre m (((n + m : ℕ) + 1) - ∑ i, x.val i))) =
        ProperMarginalChart.conditionalMeasure p n m hn (Equiv.refl _) x)
    (u v : EuclideanSpace ℝ (Fin (n + m + 1))) :
    (∫ z, p.val.1⁻¹ * fderiv ℝ (fderiv ℝ U)
      (MarginalHessian.compensatedChart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) u v ∂ρ) =
        ∑ a, ∑ b, u a * IntervalBoundary.intervalMatrix (n + m).succPNat
          (n + m + 1) le_rfl (conditionalIntervalWeight p n m hn (Equiv.refl _) x) a b * v b := by
  obtain ⟨hi,he⟩ := ConditionalScores.internal_conditional_hessian_bilinear p n m hn U hv x u v
  let c₀ := AffineSimplex.coordinates m
    (AffineSimplex.centre m (((n + m : ℕ) + 1) - ∑ i, x.val i))
  change ρ.map (fun z => z+c₀) = _ at hmap
  have hmeas : Measurable (fun z => z+c₀) := measurable_id.add_const c₀
  have hInt := integral_map (μ := ρ) (f := fun z => fderiv ℝ (fderiv ℝ U)
    (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) u v)
    hmeas.aemeasurable (by rw [hmap]; exact hi.aestronglyMeasurable)
  rw [hmap] at hInt
  simp_rw [MarginalHessian.compensatedChart_eq_shift, MarginalHessian.compensatedShift]
  rw [integral_const_mul]
  change p.val.1⁻¹ * (∫ z, fderiv ℝ (fderiv ℝ U)
    (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z+c₀)) u v ∂ρ) = _
  rw [← hInt, he, inv_mul_cancel_left₀ p.property.1.ne']

private theorem conditional_matrix_nonneg (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (a b : Fin (n + m + 1)) :
    0 ≤ IntervalBoundary.intervalMatrix (n + m).succPNat (n + m + 1) le_rfl
      (conditionalIntervalWeight p n m hn (Equiv.refl _) x) a b := by
  classical
  unfold IntervalBoundary.intervalMatrix
  apply Finset.sum_nonneg
  intro t _
  apply mul_nonneg (conditionalIntervalWeight_nonneg p n m hn (Equiv.refl _) x t)
  unfold IntervalBoundary.rankOne
  split_ifs <;> norm_num

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 4.5 of the paper, the proper marginal diagonal upper bound.
Convexity will turn this bound into an operator estimate. The negative
score variance is discarded only after its sign is justified. -/
theorem proper_hessian_diagonal_upper (p : Parameters) (n m : ℕ) (hn : 1 ≤ n)
    (θ : PhysicalCutoff) (h : ℝ) (_hh : 0 < h) (ι : Bool) :
    let F := fun x : EuclideanSpace ℝ (Fin n) =>
      ∑ i, (θ.val (((n : ℝ) ^ h)⁻¹ * x i) +
        if ι then θ.val (((n : ℝ) ^ h)⁻¹ * (x i)⁻¹) else 0)
    let K := fun x => p.val.1⁻¹ * (p.val.1 * F x -
      Real.log (∫ z : EuclideanSpace ℝ (Fin m),
        (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal))
    ∀ (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) (i : Fin n),
      let H := IntervalBoundary.intervalMatrix (n + m).succPNat (n + m + 1) le_rfl
        (conditionalIntervalWeight p n m hn (Equiv.refl _) x)
      let S := Finset.univ.filter (fun a : Fin (n + m + 1) => n ≤ a.val)
      fderiv ℝ (fderiv ℝ K) x.val (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) ≤
        fderiv ℝ (fderiv ℝ F) x.val (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) +
          H (Fin.castLE (by omega) i) (Fin.castLE (by omega) i) +
          (m + 1 : ℝ)⁻¹ ^ 2 * ∑ a ∈ S, ∑ b ∈ S, H a b := by
  classical
  intro F K x i H S
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨U,hU,hv,_,hm⟩ := PhysicalFibres.active_marginal_hessian p n m hn θ
    (inv_pos.mpr (Real.rpow_pos_of_pos hn0 h)) ι
  obtain ⟨ρ,hρ,hmap,hB,hXi,he⟩ := hm x
  let _ := hρ
  let q := WithLp.toLp 2 (Fin.append (fun _ : Fin n => (0 : ℝ))
    (fun _ : Fin (m + 1) => (m + 1 : ℝ)⁻¹))
  let e := EuclideanSpace.single (i.castAdd m).castSucc (1 : ℝ)
  have hq (a : Fin (n + m + 1)) : q a = if n ≤ a.val then (m + 1 : ℝ)⁻¹ else 0 := by
    dsimp only [q]
    exact Fin.addCases (m := n) (n := m+1) (fun j => by simp [Fin.append, j.isLt])
      (fun j => by simp [Fin.append, Fin.val_natAdd]) a
  have hqq : (∑ a, ∑ b, q a * H a b * q b) =
      (m + 1 : ℝ)⁻¹ ^ 2 * ∑ a ∈ S, ∑ b ∈ S, H a b := by
    simp_rw [hq]
    simp only [S, Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> ring
    · simp
  have hmean (u v) := internal_centred_hessian_mean p n m hn U hv x ρ hmap u v
  have hee : (∑ a, ∑ b, e a * H a b * e b) =
      H (Fin.castLE (by omega) i) (Fin.castLE (by omega) i) := by
    simp [e, EuclideanSpace.single, PiLp.single_apply]
    rfl
  have hnonneg : 0 ≤ ∑ a, ∑ b, e a * H a b * q b := by
    apply Finset.sum_nonneg
    intro a _
    apply Finset.sum_nonneg
    intro b _
    refine mul_nonneg (mul_nonneg ?_ (conditional_matrix_nonneg p n m hn x a b)) ?_
    · simp only [e, EuclideanSpace.single, PiLp.single_apply]; split_ifs <;> norm_num
    · rw [hq]; split_ifs <;> positivity
  have hvar : 0 ≤ ProbabilityTheory.covariance
      (fun z => p.val.1⁻¹ * (fderiv ℝ U
        (MarginalHessian.compensatedChart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) e -
        fderiv ℝ U (MarginalHessian.compensatedChart n m ((n + m : ℕ) + 1)
          (Equiv.refl _) (x.val,z)) q))
      (fun z => p.val.1⁻¹ * (fderiv ℝ U
        (MarginalHessian.compensatedChart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) e -
        fderiv ℝ U (MarginalHessian.compensatedChart n m ((n + m : ℕ) + 1)
          (Equiv.refl _) (x.val,z)) q)) ρ := by
    unfold ProbabilityTheory.covariance
    apply integral_nonneg
    intro z
    exact mul_self_nonneg _
  have hh := he i i
  change fderiv ℝ (fderiv ℝ K) x.val _ _ = _ at hh
  change _ = fderiv ℝ (fderiv ℝ F) x.val _ _ +
    (∫ z, p.val.1⁻¹ * fderiv ℝ (fderiv ℝ U)
      (MarginalHessian.compensatedChart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) e e ∂ρ) -
    (∫ z, p.val.1⁻¹ * fderiv ℝ (fderiv ℝ U)
      (MarginalHessian.compensatedChart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) e q ∂ρ) -
    (∫ z, p.val.1⁻¹ * fderiv ℝ (fderiv ℝ U)
      (MarginalHessian.compensatedChart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) e q ∂ρ) +
    (∫ z, p.val.1⁻¹ * fderiv ℝ (fderiv ℝ U)
      (MarginalHessian.compensatedChart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) q q ∂ρ) - _ at hh
  rw [hmean e e, hmean e q, hmean q q] at hh
  change _ = fderiv ℝ (fderiv ℝ F) x.val _ _ +
    (∑ a, ∑ b, e a * H a b * e b) - (∑ a, ∑ b, e a * H a b * q b) -
    (∑ a, ∑ b, e a * H a b * q b) + (∑ a, ∑ b, q a * H a b * q b) - _ at hh
  rw [hee,hqq] at hh
  linarith [mul_nonneg p.property.1.le hvar]

/-- See Subsection 4.5 of the paper: fourth moments of the actual inverse-gap
penalty envelope under either active tilt, uniformly over both volumes. -/
theorem active_inverse_fourth_moments (s : ℝ) (hs : 1 < s)
    (θ : PhysicalCutoff) (βlo βhi h : ℝ)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (hh : 0 < h) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (N n : ℕ+) (hn : (n : ℕ) ≤ (N : ℕ)),
      2 ≤ (N : ℕ) → ∀ (ι : Bool) (j : ℤ),
        eLpNorm (fun X : Riesz1.Configuration N => (gap X j)⁻¹ ^ 4) 4
          (tiltedParticleMeasure p N n hn θ h ι) ≤ ENNReal.ofReal C := by
  obtain ⟨Cθ,hCθ,hθ,_⟩ := θ.property.2.2.2.2
  obtain ⟨z,hz,hz1,hZ⟩ := activeTilt_normalizer_uniform_lower s βlo βhi h Cθ
    hs hlo hle hh hCθ
  obtain ⟨M,hM,hm⟩ := SingleGapTails.single_gap_moments s βlo βhi
    (by linarith) (ne_of_gt hs) hlo hle 4 (by norm_num)
  refine ⟨z⁻¹ * (M * ((4 : ℝ) ^ (4 : ℝ) + (4 : ℝ) ^ (4 / s))), by positivity, ?_⟩
  intro p hp hpl hph N n hn hN ι j
  have hb := (le_add_of_nonneg_left (by positivity)).trans
    (hm p hp hpl hph N hN j 4 (by norm_num)).1
  norm_num only [ENNReal.ofReal_ofNat] at hb
  have he (X : Riesz1.Configuration N) : (gap X j)⁻¹ ^ 4 = gap X j ^ (-(4 : ℝ)) := by
    rw [Real.rpow_neg (show 0 ≤ gap X j from (Riesz1.gap_pos X j).le), Real.rpow_ofNat, inv_pow]
  simp_rw [← he] at hb
  have ht := internal_activeTilt_norm_le hz (by linarith) (hZ p hp hpl hph N n hN hn θ hθ ι)
    (fun X => (gap X j)⁻¹ ^ 4) (q := 4) (by norm_num)
  norm_num only [ENNReal.ofReal_ofNat] at ht
  refine ht.trans ?_
  calc
    _ ≤ ENNReal.ofReal z⁻¹ * ENNReal.ofReal (M * (256 + (4 : ℝ) ^ (4 / s))) := by gcongr
    _ = _ := by rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hz.le)]; norm_num

/-- Internal retained-coordinate transport for Subsection 4.5.
The chart's actual comap law only restricts the marginal. -/
theorem internal_retained_inverse_norm (p : Parameters) (n : ℕ+) (m : ℕ)
    (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ))
    (θ : PhysicalCutoff) (h : ℝ) (ι : Bool) (i : Fin (n : ℕ)) :
    let μ := (activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ h ι).comap
      ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
    eLpNorm (fun x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) => (x.val i)⁻¹ ^ 4) 4 μ ≤
      eLpNorm (fun X : Riesz1.Configuration ((n : ℕ) + m).succPNat => (gap X i.val)⁻¹ ^ 4) 4
        (tiltedParticleMeasure p ((n : ℕ) + m).succPNat n hn θ h ι) := by
  intro μ
  let f := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) => (x i)⁻¹ ^ 4
  have hf : Measurable f := ((EuclideanSpace.proj i).continuous.measurable.inv).pow_const 4
  have hg : Measurable (fun X : Riesz1.Configuration ((n : ℕ) + m).succPNat =>
      WithLp.toLp 2 (finiteGapBlock (K := n) X)) := by
    apply (PiLp.volume_preserving_toLp _).measurable.comp
    exact Measurable.of_eval fun j => Riesz1.measurable_gap (j.val : ℤ)
  have he : eLpNorm (fun x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) => (x.val i)⁻¹ ^ 4) 4 μ =
      eLpNorm f 4 (μ.map ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
        EuclideanSpace ℝ (Fin (n : ℕ)))) := by
    rw [eLpNorm_map_measure hf.aestronglyMeasurable measurable_subtype_coe.aemeasurable]
    rfl
  rw [he]
  change eLpNorm f 4 ((Measure.comap _ _).map _) ≤ _
  rw [map_comap_subtype_coe (AffineSimplex.isOpen_chartDomain n _).measurableSet]
  refine (eLpNorm_restrict_le f 4 _ _).trans_eq ?_
  rw [activeTiltedGapLaw, eLpNorm_map_measure hf.aestronglyMeasurable hg.aemeasurable]
  rfl

private theorem sum_four_norm_le {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) (f : I → Ω → ℝ) {C : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ i, eLpNorm (f i) 4 μ ≤ ENNReal.ofReal C) :
    eLpNorm (fun x => ∑ i, f i x) 4 μ ≤ ENNReal.ofReal ((Fintype.card I : ℝ) * C) := by
  calc
    _ ≤ ∑ i, eLpNorm (f i) 4 μ := by
      simpa only [Finset.sum_fn] using eLpNorm_sum_le (μ := μ) (s := Finset.univ)
        (by norm_num : (1 : ℝ≥0∞) ≤ 4) (f := f)
    _ ≤ ∑ _ : I, ENNReal.ofReal C := Finset.sum_le_sum fun i _ => hb i
    _ = _ := by rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]; simp

private theorem scale_four_norm_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) {a C : ℝ} (ha : 0 ≤ a)
    (hb : eLpNorm f 4 μ ≤ ENNReal.ofReal C) :
    eLpNorm (fun x => a * f x) 4 μ ≤ ENNReal.ofReal (a * C) := by
  change eLpNorm (a • f) 4 μ ≤ _
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg ha]
  calc
    _ ≤ ENNReal.ofReal a * ENNReal.ofReal C := by gcongr
    _ = _ := (ENNReal.ofReal_mul ha).symm

private theorem add_four_norm_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → ℝ) {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hf : eLpNorm f 4 μ ≤ ENNReal.ofReal C) (hg : eLpNorm g 4 μ ≤ ENNReal.ofReal D) :
    eLpNorm (fun x => f x + g x) 4 μ ≤ ENNReal.ofReal (C + D) := by
  exact (eLpNorm_add_le (by norm_num) ).trans
    ((add_le_add hf hg).trans_eq (ENNReal.ofReal_add hC hD).symm)

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 4.5 of the paper: operator fourth moments of the actual proper
marginal Hessian, for both active penalties. The norm grows at most as
`n²`, so the fourth moment grows at most as `n⁸`. The degree is independent
of the tolerance and temperature. -/
theorem proper_hessian_fourth_moments (s : ℝ) (hs : 1 < s)
    (θ : PhysicalCutoff) (βlo βhi h : ℝ)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (hh : 0 < h) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ (n : ℕ+) (m : ℕ) (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)),
      4 ≤ (n : ℕ) + m + 1 → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 → ∀ ι : Bool,
      let F := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
        ∑ i, (θ.val (((n : ℝ) ^ h)⁻¹ * x i) +
          if ι then θ.val (((n : ℝ) ^ h)⁻¹ * (x i)⁻¹) else 0)
      let K := fun x => p.val.1⁻¹ * (p.val.1 * F x -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal))
      let μ := (activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ h ι).comap
        ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
      let T := fun x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) =>
        ‖fderiv ℝ (fderiv ℝ K) x.val‖
      Measurable T ∧ MemLp T 4 μ ∧ eLpNorm T 4 μ ≤ ENNReal.ofReal (C * (n : ℝ) ^ 2) := by
  classical
  obtain ⟨Cp,hCp,hpen⟩ := internal_penalty_diagonal θ
  obtain ⟨Ci,hCi,hinv⟩ := active_inverse_fourth_moments s hs θ βlo βhi h hlo hle hh
  obtain ⟨D,_,hm⟩ := interval_counting_coefficient_moments s hs
  obtain ⟨M,hM,hcoeff⟩ := hm θ βlo βhi h hlo hle hh
  let L := M * (4 : ℝ) ^ D
  have hL : 0 < L := by dsimp [L]; positivity
  let C := Cp * (1 + Ci) + L + L
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro p hp hpl hph n m hn hN hhalf ι F K μ T
  let _ : IsProbabilityMeasure μ := activeTilt_proper_probability p n m hn θ h ι
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by positivity
  obtain ⟨hK,hcurv⟩ := PhysicalFibres.active_marginal_curvature p (by simpa [hp] using hs)
    n m n.pos (Equiv.refl _) θ h hh ι
  have hT : Measurable T := by
    apply Continuous.measurable
    apply continuous_iff_continuousAt.mpr
    intro x
    have hx := hK.contDiffAt ((AffineSimplex.isOpen_chartDomain n _).mem_nhds x.property)
    exact ((hx.fderiv_right (m := 2) (by norm_num)).continuousAt_fderiv (by norm_num)).norm.comp
      continuous_subtype_val.continuousAt
  let P := fun (i : Fin (n : ℕ)) x => IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat
    (n : ℕ) hn (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x) i i
  let S := Finset.univ.filter (fun a : Fin ((n : ℕ) + m + 1) => (n : ℕ) ≤ a.val)
  let H := fun x => IntervalBoundary.intervalMatrix ((n : ℕ) + m).succPNat
    ((n : ℕ) + m + 1) le_rfl (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x)
  let c := fun x => (m + 1 : ℝ)⁻¹ ^ 2 * ∑ a ∈ S, ∑ b ∈ S, H x a b
  let G := fun (i : Fin (n : ℕ)) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) =>
    Cp * (1 + (x.val i)⁻¹ ^ 4) + P i x + c x
  have hpoint (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) : T x ≤
      (n : ℝ) * ∑ i, G i x := by
    have hx := hK.contDiffAt ((AffineSimplex.isOpen_chartDomain n _).mem_nhds x.property)
    have hpos (v) : 0 ≤ fderiv ℝ (fderiv ℝ K) x.val v v :=
      (mul_nonneg (Real.rpow_nonneg hn0.le _) (sq_nonneg _)).trans (hcurv x.val x.property v)
    refine (norm_le_card_mul_trace (fderiv ℝ (fderiv ℝ K) x.val)
      (hx.isSymmSndFDerivAt (by norm_num)) hpos).trans ?_
    simp only [Fintype.card_fin]
    apply mul_le_mul_of_nonneg_left _ hn0.le
    apply Finset.sum_le_sum
    intro i _
    have hdiag := proper_hessian_diagonal_upper p n m n.pos θ h hh ι x i
    have hpen₀ := hpen n ((n : ℝ) ^ h)⁻¹ (by positivity)
      ((inv_le_one₀ (by positivity)).mpr (Real.one_le_rpow hnR hh.le)) ι x.val x.property.1 i
    have hPi : H x (Fin.castLE hn i) (Fin.castLE hn i) = P i x := by
      unfold H P IntervalBoundary.intervalMatrix IntervalBoundary.rankOne IntervalBoundary.trace
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.castLE_refl]
    change _ ≤ _ + H x (Fin.castLE hn i) (Fin.castLE hn i) + c x at hdiag
    rw [hPi] at hdiag
    change _ ≤ Cp * (1 + (x.val i)⁻¹ ^ 4) + P i x + c x
    linarith
  have hG (i : Fin (n : ℕ)) : eLpNorm (G i) 4 μ ≤ ENNReal.ofReal C := by
    obtain ⟨hP,_,_,hbc⟩ := (hcoeff p hp hpl hph).1 n m hn hhalf ι |>.2.2 4 (by norm_num)
    have hP₀ := (hP i i).2
    have hc₀ := (le_add_of_nonneg_left (by positivity)).trans (hbc i).2.2.1
    norm_num only [ENNReal.ofReal_ofNat] at hP₀ hc₀
    have hPbound : eLpNorm (P i) 4 μ ≤ ENNReal.ofReal L := hP₀.trans
      (ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right hL.le
        (Real.rpow_le_one_of_one_le_of_nonpos (le_add_of_nonneg_right (Nat.cast_nonneg _)) (by linarith))))
    have hcbound : eLpNorm c 4 μ ≤ ENNReal.ofReal L := hc₀.trans
      (ENNReal.ofReal_le_ofReal (div_le_self hL.le (by exact_mod_cast (show 1 ≤ (n : ℕ) + m + 1 by omega))))
    have hi₀ := (internal_retained_inverse_norm p n m hn θ h ι i).trans
      (hinv p hp hpl hph ((n : ℕ) + m).succPNat n hn (by simp only [Nat.succPNat_coe]; omega) ι i.val)
    have hone : eLpNorm (fun _ : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) => (1 : ℝ)) 4 μ ≤
        ENNReal.ofReal 1 := by simp [eLpNorm_const', (by norm_num : (4 : ℝ≥0∞) ≠ 0), (by norm_num : (4 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞))]
    exact add_four_norm_le μ _ _ (by positivity) hL.le
      (add_four_norm_le μ _ _ (by positivity) hL.le
        (scale_four_norm_le μ _ hCp.le (add_four_norm_le μ _ _ (by norm_num) hCi.le hone hi₀)) hPbound) hcbound
  have hnorm : eLpNorm T 4 μ ≤ ENNReal.ofReal (C * (n : ℝ) ^ 2) := by
    refine (eLpNorm_mono_real hT.aestronglyMeasurable (fun x => ?_)).trans
      (scale_four_norm_le μ (fun x => ∑ i, G i x) hn0.le (sum_four_norm_le μ G hC.le hG) |>.trans_eq ?_)
    · have ht : 0 ≤ T x := by dsimp only [T]; positivity
      rw [Real.norm_of_nonneg ht]
      exact hpoint x
    · simp only [Fintype.card_fin]
      congr 1
      ring
  exact ⟨hT, hnorm.trans_lt ENNReal.ofReal_lt_top, hnorm⟩

set_option backward.isDefEq.respectTransparency false in
private theorem penalty_smooth_convex (n : ℕ) (L : ℝ) (θ : PhysicalCutoff)
    {a : ℝ} (ha : 0 < a) (b : Bool) :
    let F := fun x : EuclideanSpace ℝ (Fin n) =>
      ∑ i, (θ.val (a * x i) + if b then θ.val (a * (x i)⁻¹) else 0)
    ContDiffOn ℝ ∞ F (AffineSimplex.chartDomain n L) ∧
      ConvexOn ℝ (AffineSimplex.chartDomain n L) F := by
  intro F
  let φ := fun t : ℝ => θ.val (a * t) + if b then θ.val (a / t) else 0
  have hφ (t : ℝ) (ht : 0 < t) : ContDiffAt ℝ ∞ φ t := by
    have h₁ := (PhysicalCollision.cutoff_contDiffAt θ (mul_pos ha ht)).comp t
      (contDiffAt_const.mul contDiffAt_id)
    cases b
    · simpa only [φ, Bool.false_eq_true, ↓reduceIte, add_zero, Function.comp_def] using h₁
    · have h₂ := (PhysicalCollision.cutoff_contDiffAt θ (div_pos ha ht)).comp t
        (contDiffAt_const.div contDiffAt_id ht.ne')
      simpa only [φ, ↓reduceIte, Function.comp_def, Pi.div_apply] using h₁.add h₂
  have hcφ : ConvexOn ℝ (Ioi (0 : ℝ)) φ := by
    cases b
    · simpa only [φ, Bool.false_eq_true, ↓reduceIte, add_zero] using
        PhysicalCollision.upper_penalty_convex θ ha
    · exact (PhysicalCollision.upper_penalty_convex θ ha).add
        (PhysicalCollision.inverse_penalty_convex θ ha)
  have he : F = fun x => ∑ i, φ (x i) := by
    funext x
    simp only [F, φ, div_eq_mul_inv]
  rw [he]
  constructor
  · apply ContDiffOn.sum
    intro i _ x hx
    exact ((hφ _ (hx.1 i)).comp x
      (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffAt).contDiffWithinAt
  · refine ⟨AffineSimplex.convex_chartDomain n L, fun x hx y hy α β hα hβ hab => ?_⟩
    have ht := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => hcφ.2 (hx.1 i) (hy.1 i) hα hβ hab)
    simpa only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      Finset.mul_sum, Finset.sum_add_distrib] using ht

set_option backward.isDefEq.respectTransparency false in
/-- Internal penalty operator bound for Subsection 4.5, with
constants independent of dimension and the cutoff scale. -/
theorem internal_penalty_operator_bound (θ : PhysicalCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (a : ℝ), 0 < a → a ≤ 1 → ∀ b : Bool,
      let F := fun x : EuclideanSpace ℝ (Fin n) =>
        ∑ i, (θ.val (a * x i) + if b then θ.val (a * (x i)⁻¹) else 0)
      ∀ x : EuclideanSpace ℝ (Fin n), (∀ i, 0 < x i) →
        ContDiffAt ℝ 2 F x ∧
        ‖fderiv ℝ (fderiv ℝ F) x‖ ≤
          (n : ℝ) * ∑ i, C * (1 + (x i)⁻¹ ^ 4) := by
  obtain ⟨C,hC,hdiag⟩ := internal_penalty_diagonal θ
  refine ⟨C,hC,?_⟩
  intro n a ha ha1 b F x hx
  let L := (∑ i, x i) + 1
  have hxL : x ∈ AffineSimplex.chartDomain n L := ⟨hx, by dsimp [L]; linarith⟩
  obtain ⟨hF,hconv⟩ := penalty_smooth_convex n L θ ha b
  have hFx := hF.contDiffAt ((AffineSimplex.isOpen_chartDomain n L).mem_nhds hxL)
  refine ⟨hFx.of_le (by norm_num), ?_⟩
  refine (norm_le_card_mul_trace (fderiv ℝ (fderiv ℝ F) x)
    (hFx.isSymmSndFDerivAt (by norm_num)) ?_).trans ?_
  · exact Riesz1.fderiv_fderiv_nonneg_of_convexOn (AffineSimplex.isOpen_chartDomain n L)
      hconv.1 hconv (hF.of_le (by norm_num)) hxL
  · simp only [Fintype.card_fin]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hdiag n a ha ha1 b x hx i)
      (Nat.cast_nonneg n)

set_option backward.isDefEq.respectTransparency false in
/-- See Subsection 4.5 of the paper: fourth operator moments of the ambient full
Hessian, including either active penalty. The ambient norm also bounds
the intrinsic compression to the mass hyperplane. The degree `3` here
(and hence fourth-moment degree `12`) is independent of `s,h,beta`. -/
theorem full_hessian_fourth_moments (s : ℝ) (hs : 1 < s)
    (θ : PhysicalCutoff) (βlo βhi h : ℝ)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (hh : 0 < h) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ N : ℕ+, 4 ≤ (N : ℕ) →
      ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
        ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
        (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
          W y.val = physicalAmbientGapEnergy p N y) ∧
        ∀ ι : Bool,
        let F := fun x : EuclideanSpace ℝ (Fin (N : ℕ)) =>
          ∑ i, (θ.val (((N : ℝ) ^ h)⁻¹ * x i) +
            if ι then θ.val (((N : ℝ) ^ h)⁻¹ * (x i)⁻¹) else 0)
        let T := fun X : Riesz1.Configuration N =>
          ‖fderiv ℝ (fderiv ℝ (fun x => W x + F x)) (WithLp.toLp 2 (gapVector X))‖
        Measurable T ∧ MemLp T 4 (tiltedParticleMeasure p N N le_rfl θ h ι) ∧
          eLpNorm T 4 (tiltedParticleMeasure p N N le_rfl θ h ι) ≤
            ENNReal.ofReal (C * (N : ℝ) ^ 3) := by
  classical
  obtain ⟨Cp,hCp,hpen⟩ := internal_penalty_operator_bound θ
  obtain ⟨Ci,hCi,hinv⟩ := active_inverse_fourth_moments s hs θ βlo βhi h hlo hle hh
  obtain ⟨M,hM,hint⟩ := full_interaction_fourth_moments s hs θ βlo βhi h hlo hle hh
  let C := M + Cp * (1 + Ci)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,fun p hp hpl hph N hN => ?_⟩
  obtain ⟨W,hW,hv,hentries⟩ := GoodBlocks.particleHessian_eq_second p N
  refine ⟨W,hW,hv,fun ι => ?_⟩
  intro F T
  let μ := tiltedParticleMeasure p N N le_rfl θ h ι
  let _ : IsProbabilityMeasure μ := DefinitionSanity.tilted_probability p N N le_rfl θ h ι
  let y := fun X : Riesz1.Configuration N => WithLp.toLp 2 (gapVector X)
  have hy (X) : ∀ i, 0 < y X i := fun i => Riesz1.gap_pos X i.val
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
  have hNg : 0 < (N : ℝ) ^ h := by positivity
  have hscale : ((N : ℝ) ^ h)⁻¹ ≤ 1 :=
    (inv_le_one₀ hNg).mpr (Real.one_le_rpow hN1 hh.le)
  have hpen₀ (X) := hpen N ((N : ℝ) ^ h)⁻¹ (inv_pos.mpr hNg) hscale ι (y X) (hy X)
  have hU (X) : ContDiffAt ℝ 2 W (y X) :=
    (hW.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds
      (GapChart.gapVector_mem_gapAmbientDomain X))).of_le (by norm_num)
  have hT : Measurable T := by
    have hWy : Measurable (fun X => fderiv ℝ (fderiv ℝ W) (y X)) := by
      have hc : ContinuousOn (fderiv ℝ (fderiv ℝ W)) (gapAmbientDomain N) := by
        intro z hz
        have hd := hW.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds hz)
        exact ((hd.fderiv_right (m := 2) (by norm_num)).continuousAt_fderiv (by norm_num)).continuousWithinAt
      exact (continuousOn_iff_continuous_domRestrict.mp hc).measurable.comp
        (((PiLp.volume_preserving_toLp _).measurable.comp (Riesz1.measurable_gapVector N)).subtype_mk
          (h := fun X => GapChart.gapVector_mem_gapAmbientDomain X))
    have hFy : Measurable (fun X => fderiv ℝ (fderiv ℝ F) (y X)) := by
      let L := (N : ℝ) + 1
      obtain ⟨hF,_⟩ := penalty_smooth_convex N L θ (inv_pos.mpr hNg) ι
      have hc : ContinuousOn (fderiv ℝ (fderiv ℝ F)) (AffineSimplex.chartDomain N L) := by
        intro z hz
        have hd := hF.contDiffAt ((AffineSimplex.isOpen_chartDomain N L).mem_nhds hz)
        exact ((hd.fderiv_right (m := 2) (by norm_num)).continuousAt_fderiv (by norm_num)).continuousWithinAt
      have hym : Measurable y := (PiLp.volume_preserving_toLp _).measurable.comp (Riesz1.measurable_gapVector N)
      have hys (X) : y X ∈ AffineSimplex.chartDomain N L := by
        refine ⟨hy X, ?_⟩
        have hs : (∑ i : Fin (N : ℕ), gapVector X i) = (N : ℝ) := by
          have ht := Riesz1.sum_gap_eq X
          rw [← Fin.sum_univ_eq_sum_range] at ht
          exact ht
        change (∑ i, gapVector X i) < (N : ℝ) + 1
        linarith
      exact (continuousOn_iff_continuous_domRestrict.mp hc).measurable.comp (hym.subtype_mk (h := hys))
    have he : T = fun X => ‖fderiv ℝ (fderiv ℝ W) (y X) + fderiv ℝ (fderiv ℝ F) (y X)‖ := by
      funext X
      apply congrArg norm
      ext u v
      exact PhysicalCollision.internal_hessian_add (hU X) (hpen₀ X).1 u v
    rw [he]
    exact (hWy.add hFy).norm
  let J := fun X : Riesz1.Configuration N => ∑ a : Fin (N : ℕ), ∑ b : Fin (N : ℕ), GoodBlocks.particleHessian p N a b X
  let P := fun X : Riesz1.Configuration N => (N : ℝ) * ∑ i : Fin (N : ℕ), Cp * (1 + (gap X i.val)⁻¹ ^ 4)
  have hpoint (X) : T X ≤ J X + P X := by
    have he : fderiv ℝ (fderiv ℝ (fun x => W x + F x)) (y X) =
        fderiv ℝ (fderiv ℝ W) (y X) + fderiv ℝ (fderiv ℝ F) (y X) := by
      ext u v
      exact PhysicalCollision.internal_hessian_add (hU X) (hpen₀ X).1 u v
    change ‖fderiv ℝ (fderiv ℝ (fun x => W x + F x)) (y X)‖ ≤ _
    rw [he]
    have ht : ‖fderiv ℝ (fderiv ℝ W) (y X) + fderiv ℝ (fderiv ℝ F) (y X)‖ ≤
        ‖fderiv ℝ (fderiv ℝ W) (y X)‖ + ‖fderiv ℝ (fderiv ℝ F) (y X)‖ := ContinuousLinearMap.opNorm_add_le _ _
    refine ht.trans ?_
    apply add_le_add _ (hpen₀ X).2
    refine (norm_le_sum_entries _).trans_eq ?_
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [hentries X a b, abs_of_nonneg (GoodBlocks.particleHessian_nonneg p N a b X)]
  have hJ : eLpNorm J 4 μ ≤ ENNReal.ofReal ((N : ℝ) ^ 2 * M) := by
    have hb (a) := sum_four_norm_le μ (fun b => GoodBlocks.particleHessian p N a b) hM.le
      (fun b => (hint p hp hpl hph N hN ι a b).2)
    have hh := sum_four_norm_le μ (fun a X => ∑ b, GoodBlocks.particleHessian p N a b X)
      (by positivity) hb
    simp only [Fintype.card_fin] at hh
    exact hh.trans_eq (congrArg ENNReal.ofReal (by ring))
  have hP : eLpNorm P 4 μ ≤ ENNReal.ofReal ((N : ℝ) ^ 2 * (Cp * (1 + Ci))) := by
    have hone : eLpNorm (fun _ : Riesz1.Configuration N => (1 : ℝ)) 4 μ ≤ ENNReal.ofReal 1 := by
      simp [eLpNorm_const', (by norm_num : (4 : ℝ≥0∞) ≠ 0), (by norm_num : (4 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞))]
    have hb (i : Fin (N : ℕ)) := scale_four_norm_le μ _ hCp.le
      (add_four_norm_le μ _ _ (by norm_num) hCi.le hone
        (hinv p hp hpl hph N N le_rfl (by omega) ι i.val))
    have ht := scale_four_norm_le μ _ (Nat.cast_nonneg (N : ℕ))
      (sum_four_norm_le μ _ (by positivity) hb)
    simp only [Fintype.card_fin] at ht
    exact ht.trans_eq (congrArg ENNReal.ofReal (by ring))
  have hnorm : eLpNorm T 4 μ ≤ ENNReal.ofReal (C * (N : ℝ) ^ 3) := by
    refine (eLpNorm_mono_real hT.aestronglyMeasurable (fun X => ?_)).trans
      ((add_four_norm_le μ J P (by positivity) (by positivity) hJ hP).trans ?_)
    · have ht : 0 ≤ T X := by dsimp only [T]; positivity
      rw [Real.norm_of_nonneg ht]
      exact hpoint X
    · apply ENNReal.ofReal_le_ofReal
      dsimp only [C]
      have ht : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 3 := by nlinarith [sq_nonneg ((N : ℝ) - 1)]
      nlinarith [mul_le_mul_of_nonneg_right ht hC.le]
  exact ⟨hT, hnorm.trans_lt ENNReal.ofReal_lt_top, hnorm⟩

/-- Fourth-to-second-moment estimate in Subsection 4.5,
including every fixed real polynomial weight. -/
theorem internal_weighted_exceptional {δ c B M d a : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) (hB : 0 < B) (hM : 0 < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℝ, 1 ≤ n →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (T : Ω → ℝ) (E : Set Ω),
        Measurable T → eLpNorm T 4 μ ≤ ENNReal.ofReal (M * n ^ d) →
        μ E ≤ ENNReal.ofReal (B * Real.exp (-c * n ^ δ)) →
        ENNReal.ofReal (n ^ a) * eLpNorm T 2 (μ.restrict E) ≤
          ENNReal.ofReal (C * Real.exp (-(c / 8) * n ^ δ)) := by
  obtain ⟨K,hK,habs⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := a + d) (c := c / 4) (c' := c / 8) hδ (by linarith)
  refine ⟨M * B ^ (1 / 4 : ℝ) * (K + 1), by positivity, ?_⟩
  intro n hn Ω _ μ T E hT hm hp
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hres := MomentEvent.restricted_two_norm_le hT E
    (mul_nonneg hM.le (Real.rpow_nonneg hn0.le _)) hB.le (t := c * n ^ δ) hm (by simpa only [neg_mul] using hp)
  calc
    _ ≤ ENNReal.ofReal (n ^ a) *
        ENNReal.ofReal (M * n ^ d * B ^ (1 / 4 : ℝ) * Real.exp (-(c * n ^ δ) / 4)) := by gcongr
    _ = ENNReal.ofReal ((M * B ^ (1 / 4 : ℝ)) *
        (n ^ (a + d) * Real.exp (-(c / 4) * n ^ δ))) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hn0.le _), Real.rpow_add hn0]
      congr 1
      rw [show -(c * n ^ δ) / 4 = -(c / 4) * n ^ δ by ring]
      ring
    _ ≤ ENNReal.ofReal ((M * B ^ (1 / 4 : ℝ)) *
        (K * Real.exp (-(c / 8) * n ^ δ))) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (habs n hn) (by positivity))
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      nlinarith [mul_nonneg (mul_nonneg hM.le (Real.rpow_nonneg hB.le (1 / 4 : ℝ)))
        (Real.exp_pos (-(c / 8) * n ^ δ)).le])

private theorem properGoodEvent_mono (p : Parameters) (n : ℕ+) (m : ℕ)
    (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (h : ℝ)
    {D E : ℝ} (hDE : D ≤ E) : properGoodEvent p n m hn h D ⊆ properGoodEvent p n m hn h E := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  obtain ⟨hP,hp,hq,hd,hbc,hV⟩ := hx.2
  refine ⟨fun i j => (hP i j).trans ?_, fun k => (hp k).trans ?_,
    fun k => (hq k).trans ?_, hd.trans ?_, fun i => (hbc i).trans ?_, fun i => (hV i).trans ?_⟩
  all_goals first
    | exact mul_le_mul_of_nonneg_right hDE (Real.rpow_nonneg (by positivity) _)
    | exact div_le_div_of_nonneg_right hDE (by positivity)

private theorem fullGoodEvent_mono (p : Parameters) (N : ℕ+) (h : ℝ)
    {D E : ℝ} (hDE : D ≤ E) : fullGoodEvent p N h D ⊆ fullGoodEvent p N h E := by
  intro X hx
  refine ⟨hx.1,hx.2.1,fun a b => (hx.2.2 a b).trans ?_⟩
  exact mul_le_mul_of_nonneg_right hDE (Real.rpow_nonneg (by positivity) _)

private theorem truncation_level_le {n h κ κ' A A' : ℝ}
    (hn : 1 ≤ n) (hh : 0 < h) (hκ : κ ≤ κ') (hA : 0 ≤ A) (hAA : A ≤ A') :
    A * n ^ (κ * h) ≤ A' * n ^ (κ' * h) := by
  exact mul_le_mul hAA
    (Real.rpow_le_rpow_of_exponent_le hn (mul_le_mul_of_nonneg_right hκ hh.le))
    (Real.rpow_nonneg (by linarith) _) (hA.trans hAA)

private theorem weaken_exp_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) {n B B' c c' δ δ' : ℝ}
    (hn : 1 ≤ n) (hB : 0 ≤ B) (hBB : B ≤ B') (hc : 0 ≤ c)
    (hcc : c' ≤ c) (hδ : δ' ≤ δ)
    (hp : μ E ≤ ENNReal.ofReal (B * Real.exp (-c * n ^ δ))) :
    μ E ≤ ENNReal.ofReal (B' * Real.exp (-c' * n ^ δ')) := by
  refine hp.trans (ENNReal.ofReal_le_ofReal ?_)
  apply mul_le_mul hBB _ (Real.exp_pos _).le (hB.trans hBB)
  apply Real.exp_le_exp.mpr
  have ht := mul_le_mul hcc (Real.rpow_le_rpow_of_exponent_le hn hδ)
    (Real.rpow_nonneg (by linarith) _) hc
  linarith

/-- See Subsection 4.5 of the paper, a single choice of truncation degree,
truncation prefactor and tail constants for proper blocks and full cycles.
The degree precedes `h`. The tail power precedes the temperature interval. -/
theorem good_event_probability (s : ℝ) (hs : 1 < s) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ h : ℝ, 0 < h → ∃ δ : ℝ, 0 < δ ∧
      ∀ (θ : PhysicalCutoff) (βlo βhi : ℝ), 0 < βlo → βlo ≤ βhi →
      ∃ A C c : ℝ, 1 ≤ A ∧ 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
        (∀ (n : ℕ+) (m : ℕ) (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)),
          4 ≤ (n : ℕ) + m + 1 → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 → ∀ ι : Bool,
          let μ := (activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ h ι).comap
            ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
          μ (properGoodEvent p n m hn h (A * (n : ℝ) ^ (κ * h)))ᶜ ≤
            ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ δ))) ∧
        (∀ N : ℕ+, 4 ≤ (N : ℕ) → ∀ ι : Bool,
          (tiltedParticleMeasure p N N le_rfl θ h ι)
            (fullGoodEvent p N h (A * (N : ℝ) ^ (κ * h)))ᶜ ≤
              ENNReal.ofReal (C * Real.exp (-c * (N : ℝ) ^ δ))) := by
  obtain ⟨κp,hκp,hp⟩ := proper_good_event_probability s hs
  obtain ⟨κf,hκf,hf⟩ := full_good_event_probability s hs
  let κ := max κp κf
  refine ⟨κ,lt_max_of_lt_left hκp,fun h hh => ?_⟩
  obtain ⟨δp,hδp,hp⟩ := hp h hh
  obtain ⟨δf,hδf,hf⟩ := hf h hh
  let δ := min δp δf
  refine ⟨δ,lt_min hδp hδf,fun θ βlo βhi hlo hle => ?_⟩
  obtain ⟨Ap,Cp,cp,hAp,hCp,hcp,hp⟩ := hp θ βlo βhi hlo hle
  obtain ⟨Af,Cf,cf,hAf,hCf,hcf,hf⟩ := hf θ βlo βhi hlo hle
  let A := max Ap Af
  let C := Cp + Cf
  let c := min cp cf
  refine ⟨A,C,c,hAp.trans (le_max_left _ _),by positivity,lt_min hcp hcf,?_⟩
  intro p hps hpl hph
  constructor
  · intro n m hn hN hhalf ι μ
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
    have hlev := truncation_level_le hn1 hh (le_max_left κp κf) (zero_le_one.trans hAp)
      (le_max_left Ap Af)
    refine (measure_mono (compl_subset_compl.mpr (properGoodEvent_mono p n m hn h hlev))).trans ?_
    exact weaken_exp_probability μ _ hn1 hCp.le (by dsimp [C]; linarith) hcp.le
      (min_le_left cp cf) (min_le_left δp δf) (hp p hps hpl hph n m hn hN hhalf ι)
  · intro N hN ι
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
    have hlev := truncation_level_le hN1 hh (le_max_right κp κf) (zero_le_one.trans hAf)
      (le_max_right Ap Af)
    refine (measure_mono (compl_subset_compl.mpr (fullGoodEvent_mono p N h hlev))).trans ?_
    exact weaken_exp_probability _ _ hN1 hCf.le (by dsimp [C]; linarith) hcf.le
      (min_le_right cp cf) (min_le_right δp δf) (hf p hps hpl hph N hN ι)

private theorem fourth_moment_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → ℝ) (hT : Measurable T) {M : ℝ} (hM : 0 ≤ M)
    (hb : eLpNorm T 4 μ ≤ ENNReal.ofReal M) :
    Integrable (fun x => T x ^ 4) μ ∧ (∫ x, T x ^ 4 ∂μ) ≤ M ^ 4 := by
  have hb₀ : eLpNorm T (ENNReal.ofReal (4 : ℝ)) μ ≤ ENNReal.ofReal M := by
    norm_num only [ENNReal.ofReal_ofNat]
    exact hb
  have hh := MomentEvent.integrable_rpow_abs_and_integral_le_of_eLpNorm_le hT
    (by norm_num : (0 : ℝ) < 4) hM hb₀
  have he : (fun x => |T x| ^ (4 : ℝ)) = fun x => T x ^ 4 := by
    funext x
    rw [Real.rpow_ofNat]
    calc
      |T x| ^ 4 = (|T x| ^ 2) ^ 2 := by ring
      _ = (T x ^ 2) ^ 2 := by rw [sq_abs]
      _ = T x ^ 4 := by ring
  rw [he, Real.rpow_ofNat] at hh
  exact hh

private theorem weighted_probability_bound {δ b B a : ℝ}
    (hδ : 0 < δ) (hb : 0 < b) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℝ, 1 ≤ n →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (E : Set Ω),
      μ E ≤ ENNReal.ofReal (B * Real.exp (-b * n ^ δ)) →
      ENNReal.ofReal (n ^ a) * μ E ≤ ENNReal.ofReal (C * Real.exp (-(b / 8) * n ^ δ)) := by
  obtain ⟨K,hK,habs⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := a) (c := b) (c' := b / 8) hδ (by linarith)
  refine ⟨B * (K + 1),by positivity,fun n hn Ω _ μ E hp => ?_⟩
  have hn0 : 0 ≤ n := zero_le_one.trans hn
  calc
    _ ≤ ENNReal.ofReal (n ^ a) * ENNReal.ofReal (B * Real.exp (-b * n ^ δ)) := by gcongr
    _ = ENNReal.ofReal (B * (n ^ a * Real.exp (-b * n ^ δ))) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hn0 _)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (B * (K * Real.exp (-(b / 8) * n ^ δ))) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (habs n hn) hB.le)
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [mul_pos hB (Real.exp_pos (-(b / 8) * n ^ δ))])

/-- See Subsection 4.5 of the paper, complete probability, fourth-moment and
exceptional operator estimates in both geometries, for either active tilt.
The common good-event parameters precede every polynomial weight. Taking
`a = 0` gives the unweighted statement. The fourth-moment degree is `12`,
chosen independently of `h` and beta. The full ambient operator bound also
controls its intrinsic restriction. -/
theorem exceptional_event_estimates (s : ℝ) (hs : 1 < s) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ h : ℝ, 0 < h → ∃ δ : ℝ, 0 < δ ∧
      ∀ (θ : PhysicalCutoff) (βlo βhi : ℝ), 0 < βlo → βlo ≤ βhi →
      ∃ A : ℝ, 1 ≤ A ∧ ∀ a : ℝ, ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
        (∀ (n : ℕ+) (m : ℕ) (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)),
          4 ≤ (n : ℕ) + m + 1 → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 → ∀ ι : Bool,
          let F := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
            ∑ i, (θ.val (((n : ℝ) ^ h)⁻¹ * x i) +
              if ι then θ.val (((n : ℝ) ^ h)⁻¹ * (x i)⁻¹) else 0)
          let K := fun x => p.val.1⁻¹ * (p.val.1 * F x -
            Real.log (∫ z : EuclideanSpace ℝ (Fin m),
              (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (x,z)).toReal))
          let μ := (activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ h ι).comap
            ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
          let T := fun x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) =>
            ‖fderiv ℝ (fderiv ℝ K) x.val‖
          let E := (properGoodEvent p n m hn h (A * (n : ℝ) ^ (κ * h)))ᶜ
          μ E ≤ ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ δ)) ∧
          ENNReal.ofReal ((n : ℝ) ^ a) * μ E ≤ ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ δ)) ∧
          Integrable (fun x => T x ^ 4) μ ∧ (∫ x, T x ^ 4 ∂μ) ≤ C * (n : ℝ) ^ 12 ∧
          ENNReal.ofReal ((n : ℝ) ^ a) * eLpNorm T 2 (μ.restrict E) ≤
            ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ δ))) ∧
        (∀ N : ℕ+, 4 ≤ (N : ℕ) →
          ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
            ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
            (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
              W y.val = physicalAmbientGapEnergy p N y) ∧
            ∀ ι : Bool,
            let F := fun x : EuclideanSpace ℝ (Fin (N : ℕ)) =>
              ∑ i, (θ.val (((N : ℝ) ^ h)⁻¹ * x i) +
                if ι then θ.val (((N : ℝ) ^ h)⁻¹ * (x i)⁻¹) else 0)
            let T := fun X : Riesz1.Configuration N =>
              ‖fderiv ℝ (fderiv ℝ (fun x => W x + F x)) (WithLp.toLp 2 (gapVector X))‖
            let μ := tiltedParticleMeasure p N N le_rfl θ h ι
            let E := (fullGoodEvent p N h (A * (N : ℝ) ^ (κ * h)))ᶜ
            μ E ≤ ENNReal.ofReal (C * Real.exp (-c * (N : ℝ) ^ δ)) ∧
            ENNReal.ofReal ((N : ℝ) ^ a) * μ E ≤ ENNReal.ofReal (C * Real.exp (-c * (N : ℝ) ^ δ)) ∧
            Integrable (fun x => T x ^ 4) μ ∧ (∫ x, T x ^ 4 ∂μ) ≤ C * (N : ℝ) ^ 12 ∧
            ENNReal.ofReal ((N : ℝ) ^ a) * eLpNorm T 2 (μ.restrict E) ≤
              ENNReal.ofReal (C * Real.exp (-c * (N : ℝ) ^ δ))) := by
  obtain ⟨κ,hκ,hprob⟩ := good_event_probability s hs
  refine ⟨κ,hκ,fun h hh => ?_⟩
  obtain ⟨δ,hδ,hprob⟩ := hprob h hh
  refine ⟨δ,hδ,fun θ βlo βhi hlo hle => ?_⟩
  obtain ⟨A,B,b,hA,hB,hb,hprob⟩ := hprob θ βlo βhi hlo hle
  obtain ⟨Mp,hMp,hproper⟩ := proper_hessian_fourth_moments s hs θ βlo βhi h hlo hle hh
  obtain ⟨Mf,hMf,hfull⟩ := full_hessian_fourth_moments s hs θ βlo βhi h hlo hle hh
  refine ⟨A,hA,fun a => ?_⟩
  obtain ⟨Kp,hKp,hrareP⟩ := internal_weighted_exceptional (a := a) (d := 2) hδ hb hB hMp
  obtain ⟨Kf,hKf,hrareF⟩ := internal_weighted_exceptional (a := a) (d := 3) hδ hb hB hMf
  obtain ⟨Kq,hKq,hrareQ⟩ := weighted_probability_bound (a := a) hδ hb hB
  let C := B + Mp ^ 4 + Mf ^ 4 + Kp + Kf + Kq
  have hC : 0 < C := by dsimp [C]; positivity
  have hBC : B ≤ C := by dsimp [C]; linarith [pow_nonneg hMp.le 4, pow_nonneg hMf.le 4]
  have hPC : Mp ^ 4 ≤ C := by dsimp [C]; linarith [pow_nonneg hMp.le 4, pow_nonneg hMf.le 4]
  have hFC : Mf ^ 4 ≤ C := by dsimp [C]; linarith [pow_nonneg hMp.le 4, pow_nonneg hMf.le 4]
  have hKPC : Kp ≤ C := by dsimp [C]; linarith [pow_nonneg hMp.le 4, pow_nonneg hMf.le 4]
  have hKQC : Kq ≤ C := by dsimp [C]; linarith [pow_nonneg hMp.le 4, pow_nonneg hMf.le 4]
  have hKFC : Kf ≤ C := by dsimp [C]; linarith [pow_nonneg hMp.le 4, pow_nonneg hMf.le 4]
  refine ⟨C,b / 8,hC,by positivity,?_⟩
  intro p hp hpl hph
  obtain ⟨hprobP,hprobF⟩ := hprob p hp hpl hph
  constructor
  · intro n m hn hN hhalf ι F K μ T E
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
    obtain ⟨hT,_,h4⟩ := hproper p hp hpl hph n m hn hN hhalf ι
    have htail := hprobP n m hn hN hhalf ι
    obtain ⟨hI,hIbound⟩ := fourth_moment_le μ T hT (by positivity) h4
    have hrare := hrareP n hn1 μ T E hT (by norm_num only [Real.rpow_ofNat]; exact h4) htail
    refine ⟨weaken_exp_probability μ E hn1 hB.le hBC hb.le (by linarith) le_rfl htail,
      (hrareQ _ hn1 μ E htail).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hKQC (Real.exp_pos _).le)),
      hI,hIbound.trans ?_,hrare.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    · have hpowers : (Mp * (n : ℝ) ^ 2) ^ 4 = Mp ^ 4 * (n : ℝ) ^ 8 := by ring
      rw [hpowers]
      apply mul_le_mul hPC _ (by positivity) hC.le
      exact pow_le_pow_right₀ hn1 (by norm_num : 8 ≤ 12)
    · exact mul_le_mul_of_nonneg_right hKPC (Real.exp_pos _).le
  · intro N hN
    obtain ⟨W,hW,hv,hfull⟩ := hfull p hp hpl hph N hN
    refine ⟨W,hW,hv,fun ι => ?_⟩
    intro F T μ E
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
    obtain ⟨hT,_,h4⟩ := hfull ι
    have htail := hprobF N hN ι
    obtain ⟨hI,hIbound⟩ := fourth_moment_le μ T hT (by positivity) h4
    have hrare := hrareF N hN1 μ T E hT (by norm_num only [Real.rpow_ofNat]; exact h4) htail
    refine ⟨weaken_exp_probability μ E hN1 hB.le hBC hb.le (by linarith) le_rfl htail,
      (hrareQ _ hN1 μ E htail).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hKQC (Real.exp_pos _).le)),
      hI,hIbound.trans ?_,hrare.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    · have hpowers : (Mf * (N : ℝ) ^ 3) ^ 4 = Mf ^ 4 * (N : ℝ) ^ 12 := by ring
      rw [hpowers]
      exact mul_le_mul_of_nonneg_right hFC (by positivity)
    · exact mul_le_mul_of_nonneg_right hKFC (Real.exp_pos _).le



/-- Definition of the full potential for Subsection 4.5: the
full potential used above is exactly the temperature-unscaled `fullPhysicalPotentialValue`, on its entire ambient domain. -/
theorem internal_full_physical_realization (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (θ : PhysicalCutoff) (h : ℝ) (ι : Bool)
    (W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ)
    (hv : ∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
      W y.val = physicalAmbientGapEnergy p N y)
    (y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N}) :
    p.val.1 * (W y.val + ∑ i : Fin (N : ℕ),
      (θ.val (((N : ℝ) ^ h)⁻¹ * y.val i) +
        if ι then θ.val (((N : ℝ) ^ h)⁻¹ * (y.val i)⁻¹) else 0)) =
      fullPhysicalPotentialValue p N hN θ h ι y := by
  rw [hv y]
  simp only [fullPhysicalPotentialValue, Real.rpow_neg (show 0 ≤ (N : ℝ) from Nat.cast_nonneg _)]

end Riesz2.DecayShort.ExceptionalEvent
