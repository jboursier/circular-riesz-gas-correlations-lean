/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.InitialDecay
public import Riesz2.Frozen.SummableCoerciveMatrix
public import Riesz2.Frozen.InverseTemperature

/-!
# Initial weighted short-range decay

See Lemma 4.4 of the paper. The estimates complete the commutation
argument of `InitialDecay`.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set InnerProductSpace
open scoped ENNReal NNReal Topology BigOperators

namespace Riesz2.InitialDecay.Internal

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]
  {ν : Measure α}

/-- The entry envelope gives a dimension-independent quadratic upper bound.
This is the Schur bridge from Assumptions 4.2 to Lemma 4.4. -/
theorem summable_quadratic_upper (s : ℝ) (hs : 1 < s)
    (g : ComponentGeometry ι) (B : ℝ) (hB : 0 ≤ B)
    (M : Matrix ι ι ℝ)
    (hM : ∀ i j, |M i j| ≤ B * (1 + componentDistance g i j) ^ (-s))
    (z : ι → ℝ) :
    (∑ i, ∑ j, z i * M i j * z j) ≤
      (B * (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s))) * ∑ i, z i ^ 2 := by
  let H := fun i j => B * (1 + componentDistance g i j) ^ (-s)
  let T := B * (2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s))
  have hr (i : ι) : ∑ j, H i j ≤ T := by
    dsimp [H, T]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (ComponentGeometryBounds.sum_power_le g i hs) hB
  have hc (j : ι) : ∑ i, H i j ≤ T := by
    simpa only [H, ComponentGeometryBounds.symm g] using hr j
  have hh := schur_quadratic_le H (fun i j => by
    dsimp [H]
    exact mul_nonneg hB (Real.rpow_nonneg (by linarith [ComponentGeometryBounds.nonneg g i j]) _)) T T hr hc z
  calc
    _ ≤ ∑ i, ∑ j, |z i| * H i j * |z j| := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact (le_abs_self _).trans (by
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hM i j) (abs_nonneg _)) (abs_nonneg _))
    _ ≤ _ := by convert hh using 1; dsimp [T]; ring

/-- Integrating a finite square sum agrees with the Hilbert product norm.
No choice of a vector-valued representative is needed. -/
theorem integral_square_sum (v : ι → Lp ℝ 2 ν) :
    (∫ x, ∑ i, v i x ^ 2 ∂ν) = ‖WithLp.toLp 2 v‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    exact integral_congr_ae (Eventually.of_forall fun x => by
      dsimp only
      rw [Real.inner_apply, sq])
  · intro i _
    exact (Lp.memLp (v i)).integrable_sq

/-- On the local ball, the distortion costs at most its maximal radial weight. -/
theorem local_distortion_sq_le [DecidableEq ι]
    (g : ComponentGeometry ι) (i₀ : ι) (a K : ℝ) (ha : 0 ≤ a) (_hK : 0 ≤ K)
    (v : ι → ℝ) :
    (∑ j ∈ Finset.univ.filter (fun j => componentDistance g j i₀ ≤ 2 * K),
      (distortionWeight g i₀ a j * v j) ^ 2) ≤
        ((1 + 2 * K) ^ a) ^ 2 * ∑ j, v j ^ 2 := by
  rw [Finset.mul_sum]
  apply (Finset.sum_le_sum fun j hj => ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun j _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  have hw : distortionWeight g i₀ a j ≤ (1 + 2 * K) ^ a := by
    apply Real.rpow_le_rpow
    · linarith [ComponentGeometryBounds.nonneg g j i₀]
    · linarith [(Finset.mem_filter.mp hj).2]
    · exact ha
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (le_of_lt (distortionWeight_pos g i₀ a j)) hw 2) (sq_nonneg _)

/-- Young absorption at a fixed cutoff. This pointwise inequality is integrated
as a whole, following Lemma 4.4. The sharp local loss
`t = 1/2` gives the paper's intermediate power `K^(1/2+a)`. -/
theorem conjugated_lower_of_cutoff [DecidableEq ι]
    (g : ComponentGeometry ι) (i₀ : ι) (a B C t ρ K : ℝ)
    (ha : 0 ≤ a) (hB : 0 < B) (hC : 0 ≤ C) (hK : 1 ≤ K)
    (htail : C * B * K ^ (-ρ) ≤ (4 * B)⁻¹)
    (M : Matrix ι ι ℝ)
    (hlow : ∀ z : ι → ℝ, B⁻¹ * ∑ i, z i ^ 2 ≤ ∑ i, ∑ j, z i * M i j * z j)
    (hcomm : ∀ z : ι → ℝ,
      |∑ i, ∑ j, z i *
        (distortionMatrix g i₀ a * M * distortionMatrix g i₀ (-a) - M) i j * z j| ≤
        C * B * K ^ (-ρ) * (∑ i, z i ^ 2) +
          C * B * K ^ t * Real.sqrt (∑ i, z i ^ 2) *
            Real.sqrt (∑ j ∈ Finset.univ.filter
              (fun j => componentDistance g j i₀ ≤ 2 * K), z j ^ 2))
    (v : ι → ℝ) :
    (2 * B)⁻¹ * (∑ i, (distortionWeight g i₀ a i * v i) ^ 2) -
      B * (C * B * 3 ^ a * K ^ (t + a)) ^ 2 * (∑ i, v i ^ 2) ≤
        ∑ i, ∑ j, (distortionWeight g i₀ a i * v i) *
          (distortionMatrix g i₀ a * M * distortionMatrix g i₀ (-a)) i j *
            (distortionWeight g i₀ a j * v j) := by
  let u := fun i => distortionWeight g i₀ a i * v i
  let U := ∑ i, u i ^ 2
  let V := ∑ i, v i ^ 2
  let L := C * B * 3 ^ a * K ^ (t + a)
  have hU : 0 ≤ U := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hV : 0 ≤ V := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hloc : Real.sqrt (∑ j ∈ Finset.univ.filter
      (fun j => componentDistance g j i₀ ≤ 2 * K), u j ^ 2) ≤
        (1 + 2 * K) ^ a * Real.sqrt V := by
    apply (Real.sqrt_le_sqrt (local_distortion_sq_le g i₀ a K ha (by linarith) v)).trans_eq
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hweight : K ^ t * (1 + 2 * K) ^ a ≤ 3 ^ a * K ^ (t + a) := by
    calc
      _ ≤ K ^ t * (3 * K) ^ a := by gcongr; linarith
      _ = _ := by
        rw [Real.mul_rpow (by norm_num) (by linarith), Real.rpow_add (by linarith)]
        ring
  have hh := hcomm u
  have ht := mul_le_mul_of_nonneg_right htail hU
  have hloc' : C * B * K ^ t * Real.sqrt U *
      Real.sqrt (∑ j ∈ Finset.univ.filter
        (fun j => componentDistance g j i₀ ≤ 2 * K), u j ^ 2) ≤
      L * Real.sqrt U * Real.sqrt V := by
    calc _ ≤ C * B * K ^ t * Real.sqrt U *
          ((1 + 2 * K) ^ a * Real.sqrt V) := by gcongr
      _ = C * B * (K ^ t * (1 + 2 * K) ^ a) * Real.sqrt U * Real.sqrt V := by ring
      _ ≤ C * B * (3 ^ a * K ^ (t + a)) * Real.sqrt U * Real.sqrt V := by gcongr
      _ = L * Real.sqrt U * Real.sqrt V := by dsimp [L]; ring
  have hy : L * Real.sqrt U * Real.sqrt V ≤ (4 * B)⁻¹ * U + B * L ^ 2 * V := by
    have hh := sq_nonneg (Real.sqrt U - 2 * B * L * Real.sqrt V)
    have hUs := Real.sq_sqrt hU
    have hVs := Real.sq_sqrt hV
    simp only [sub_sq, mul_pow, hUs, hVs] at hh
    calc
      _ ≤ (U + 4 * B ^ 2 * L ^ 2 * V) / (4 * B) := by
        apply (le_div_iff₀ (by positivity : 0 < 4 * B)).mpr
        nlinarith only [hh, hUs, hVs]
      _ = _ := by field_simp
  have hab := neg_abs_le (∑ i, ∑ j, u i *
      (distortionMatrix g i₀ a * M * distortionMatrix g i₀ (-a) - M) i j * u j)
  have he : (∑ i, ∑ j, u i *
      (distortionMatrix g i₀ a * M * distortionMatrix g i₀ (-a) - M) i j * u j) =
      (∑ i, ∑ j, u i *
        (distortionMatrix g i₀ a * M * distortionMatrix g i₀ (-a)) i j * u j) -
        ∑ i, ∑ j, u i * M i j * u j := by
    simp only [Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
  have hinv : B⁻¹ - (4 * B)⁻¹ - (4 * B)⁻¹ = (2 * B)⁻¹ := by field_simp; ring
  change (2 * B)⁻¹ * U - B * L ^ 2 * V ≤ _
  rw [he] at hh hab
  have hl := hlow u
  change B⁻¹ * U ≤ _ at hl
  nlinarith

/-- A cutoff polynomial in the matrix loss absorbs the exterior commutator.
This is the cutoff step of Lemma 4.4. The exponent is
chosen before the loss B, as required by Section 4. -/
theorem polynomial_cutoff (C t a ρ : ℝ) (hC : 0 < C) (ht : 0 < t)
    (ha : 0 ≤ a) (hρ : 0 < ρ) :
    ∃ p D : ℝ, 0 ≤ p ∧ 1 ≤ D ∧ ∀ B : ℝ, 1 ≤ B → ∃ K : ℝ, 1 ≤ K ∧
      C * B * K ^ (-ρ) ≤ (4 * B)⁻¹ ∧
      B * (C * B * 3 ^ a * K ^ (t + a)) ^ 2 ≤ D * B ^ p := by
  let d := 4 * (C + 1)
  let k := 2 / ρ
  let z := t + a
  let L := C * 3 ^ a * d ^ (k * z)
  have hd : 1 ≤ d := by dsimp [d]; linarith
  have hk : 0 < k := by dsimp [k]; positivity
  have hz : 0 < z := by dsimp [z]; linarith
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨3 + 2 * k * z, 1 + L ^ 2, by positivity, by nlinarith [sq_nonneg L], ?_⟩
  intro B hB
  have hB0 : 0 < B := by linarith
  let K := (d * B) ^ k
  have hK : 1 ≤ K := Real.one_le_rpow (one_le_mul_of_one_le_of_one_le hd hB) hk.le
  refine ⟨K, hK, ?_, ?_⟩
  · have he : K ^ (-ρ) = (d * B)⁻¹ ^ 2 := by
      dsimp [K]
      rw [← Real.rpow_mul (by positivity), show k * (-ρ) = -(2 : ℝ) by dsimp [k]; field_simp,
        Real.rpow_neg (by positivity), Real.rpow_two, inv_pow]
    rw [he]
    have hdpos : 0 < d := by linarith
    apply (mul_le_mul_iff_right₀ (show 0 < 4 * B * d ^ 2 by positivity)).mp
    have he1 : (4 * B * d ^ 2) * (C * B * (d * B)⁻¹ ^ 2) = 4 * C := by
      field_simp
    have he2 : (4 * B * d ^ 2) * (4 * B)⁻¹ = d ^ 2 := by field_simp
    rw [he1, he2]
    dsimp [d]
    nlinarith [sq_nonneg C]
  · have hl : C * B * 3 ^ a * K ^ (t + a) = L * B ^ (1 + k * z) := by
      dsimp [L, K]
      rw [← Real.rpow_mul (by positivity), Real.mul_rpow (by positivity) hB0.le,
        Real.rpow_add hB0, Real.rpow_one]
      ring
    have he : B * (L * B ^ (1 + k * z)) ^ 2 = L ^ 2 * B ^ (3 + 2 * k * z) := by
      rw [mul_pow, ← Real.rpow_mul_natCast hB0.le]
      calc
        B * (L ^ 2 * B ^ ((1 + k * z) * (2 : ℝ))) =
            L ^ 2 * (B ^ (1 : ℝ) * B ^ ((1 + k * z) * (2 : ℝ))) := by
          rw [Real.rpow_one]; ring
        _ = _ := by rw [← Real.rpow_add hB0]; congr 2; ring
    calc
      _ ≤ B * (L * B ^ (1 + k * z)) ^ 2 := by rw [hl]
      _ = L ^ 2 * B ^ (3 + 2 * k * z) := he
      _ ≤ (1 + L ^ 2) * B ^ (3 + 2 * k * z) := by gcongr; linarith

/-- Uniform polynomial lower bound for the distorted matrix, the algebraic
core of Lemma 4.4. No cardinality or diameter occurs. -/
theorem polynomial_conjugated_lower (s a : ℝ) (hs : 1 < s)
    (ha : 1 / 2 < a) (has : a < s - 1 / 2) :
    ∃ p D : ℝ, 0 ≤ p ∧ 1 ≤ D ∧
      ∀ (ι : Type*) [Fintype ι] [DecidableEq ι] (g : ComponentGeometry ι)
        (i₀ : ι) (B : ℝ), 1 ≤ B → ∀ M : Matrix ι ι ℝ,
        (∀ z : ι → ℝ, B⁻¹ * ∑ i, z i ^ 2 ≤ ∑ i, ∑ j, z i * M i j * z j) →
        (∀ i j, |M i j| ≤ B * (1 + componentDistance g i j) ^ (-s)) →
        ∀ v : ι → ℝ,
          (2 * B)⁻¹ * (∑ i, (distortionWeight g i₀ a i * v i) ^ 2) -
            D * B ^ p * (∑ i, v i ^ 2) ≤
          ∑ i, ∑ j, (distortionWeight g i₀ a i * v i) *
            (distortionMatrix g i₀ a * M * distortionMatrix g i₀ (-a)) i j *
              (distortionWeight g i₀ a j * v j) := by
  let ρ := min 1 (s - 1 / 2 - a) / 2
  have hm : 0 < min 1 (s - 1 / 2 - a) := by positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hr2 : ρ < 1 := by
    dsimp [ρ]; linarith [min_le_left 1 (s - 1 / 2 - a)]
  have hr3 : ρ < s - 1 / 2 - a := by
    dsimp [ρ]; linarith [min_le_right 1 (s - 1 / 2 - a)]
  obtain ⟨C, hC, hcomm⟩ := commutator_estimate_sqrt_local s a ρ hs ha has hρ hr2 hr3
  obtain ⟨p, D, hp, hD, hcut⟩ := polynomial_cutoff C (1 / 2) a ρ hC
    (by norm_num) (by linarith) hρ
  refine ⟨p, D, hp, hD, ?_⟩
  intro ι _ _ g i₀ B hB M hlow hentry v
  obtain ⟨K, hK, htail, hlocal⟩ := hcut B hB
  have hh := conjugated_lower_of_cutoff g i₀ a B C (1 / 2) ρ K (by linarith)
    (by linarith) hC.le hK htail M hlow (hcomm ι g i₀ B (by linarith) M hentry K hK) v
  have hlocal' := mul_le_mul_of_nonneg_right hlocal
    (show 0 ≤ ∑ i, v i ^ 2 from Finset.sum_nonneg (fun i _ => sq_nonneg (v i)))
  linarith

/-- Square integrability and the norm identity for constant component weights. -/
theorem weighted_square_integral (w : ι → ℝ) (v : ι → Lp ℝ 2 ν) :
    Integrable (fun x => ∑ i, (w i * v i x) ^ 2) ν ∧
      (∫ x, ∑ i, (w i * v i x) ^ 2 ∂ν) =
        ‖WithLp.toLp 2 (fun i => w i • v i)‖ ^ 2 := by
  have hae : ∀ᵐ x ∂ν, ∀ i, (w i • v i) x = w i * v i x := by
    apply ae_all_iff.mpr
    intro i
    simpa only [Filter.EventuallyEq, Pi.smul_apply, smul_eq_mul] using Lp.coeFn_smul (w i) (v i)
  have he : (fun x => ∑ i, (w i * v i x) ^ 2) =ᵐ[ν]
      (fun x => ∑ i, (w i • v i) x ^ 2) := by
    filter_upwards [hae] with x hx
    simp only [hx]
  refine ⟨(integrable_finsetSum _ (fun i _ => (Lp.memLp (w i • v i)).integrable_sq)).congr
    he.symm, ?_⟩
  rw [integral_congr_ae he, integral_square_sum]

/-- Integrating a pointwise distorted lower bound on the whole scalar form domain. -/
theorem weighted_energy_inequality [DecidableEq ι]
    (Q : ScalarFormData ν) (g : ComponentGeometry ι) (i₀ : ι) (a : ℝ)
    (M : α → Matrix ι ι ℝ) (hMmeas : ∀ i j, Measurable (fun x => M x i j))
    (b : ℝ) (hsym : ∀ᵐ x ∂ν, ∀ i j, M x i j = M x j i)
    (hM : ∀ᵐ x ∂ν, ∀ z : ι → ℝ,
      0 ≤ (∑ i, ∑ j, z i * M x i j * z j) ∧
      (∑ i, ∑ j, z i * M x i j * z j) ≤ b * ∑ i, z i ^ 2)
    (c D : ℝ)
    (hlower : ∀ᵐ x ∂ν, ∀ v : ι → ℝ,
      c * (∑ i, (distortionWeight g i₀ a i * v i) ^ 2) - D * (∑ i, v i ^ 2) ≤
        ∑ i, ∑ j, (distortionWeight g i₀ a i * v i) *
          (distortionMatrix g i₀ a * M x * distortionMatrix g i₀ (-a)) i j *
            (distortionWeight g i₀ a j * v j))
    (χ : Lp ℝ 2 ν) (u : ι → Q.1)
    (hu : WeightedWeakSolution Q M ⊤ (fun i => if i = i₀ then χ else 0) u) :
    (∑ i, Q.2 (distortionWeight g i₀ a i • u i) (distortionWeight g i₀ a i • u i)) +
      c * ‖WithLp.toLp 2 (fun i => distortionWeight g i₀ a i • (u i).val)‖ ^ 2 ≤
        inner ℝ χ (u i₀).val + D * ‖WithLp.toLp 2 (fun i => (u i).val)‖ ^ 2 := by
  have he := distorted_weak_energy_identity Q g i₀ a M hMmeas b hsym hM χ u hu
  have hw := weighted_square_integral (distortionWeight g i₀ a) (fun i => (u i).val)
  have hv : Integrable (fun x => ∑ i, (u i).val x ^ 2) ν :=
    integrable_finsetSum _ (fun i _ => (Lp.memLp (u i).val).integrable_sq)
  have hi := integral_mono_ae ((hw.1.const_mul c).sub (hv.const_mul D)) he.1
    (hlower.mono (fun x hx => hx (fun i => (u i).val x)))
  simp only [Pi.sub_apply] at hi
  rw [integral_sub (hw.1.const_mul c) (hv.const_mul D),
    integral_const_mul, integral_const_mul, hw.2, integral_square_sum] at hi
  linarith [he.2]

/-- The energy theorem specialized to a point source, retaining unique existence and the unweighted mass bound for every weak solution. -/
theorem point_source_energy [DecidableEq ι] [IsProbabilityMeasure ν]
    (β : ℝ) (hβ : 0 < β) (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (hconserv : IsConservativeScalarForm Q)
    (M : α → Matrix ι ι ℝ) (hMmeas : ∀ i j, Measurable (fun x => M x i j))
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hM : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧ ∀ z : ι → ℝ,
      a * (∑ i, z i ^ 2) ≤ (∑ i, ∑ j, z i * M x i j * z j) ∧
      (∑ i, ∑ j, z i * M x i j * z j) ≤ b * ∑ i, z i ^ 2)
    (i₀ : ι) (χ : Lp ℝ 2 ν) :
    (∃! u : ι → Q.1, WeightedWeakSolution Q (fun x => β • M x) ⊤
      (fun i => if i = i₀ then χ else 0) u) ∧
    ∀ u : ι → Q.1, WeightedWeakSolution Q (fun x => β • M x) ⊤
      (fun i => if i = i₀ then χ else 0) u →
      ‖WithLp.toLp 2 (fun i => (u i).val)‖ ≤ (β * a)⁻¹ * ‖χ‖ := by
  obtain ⟨_, T, _, hT⟩ := AbstractEnergy.illustrative_energy β hβ Q hQ hconserv
    M hMmeas a b ha hab hM ⊤
  let f : PiLp 2 (fun _ : ι => Lp ℝ 2 ν) :=
    WithLp.toLp 2 (fun i => if i = i₀ then χ else 0)
  have hf : ‖f‖ = ‖χ‖ := by
    have he : ‖f‖ ^ 2 = ‖χ‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      rw [Finset.sum_eq_single i₀]
      · simp [f]
      · intro i _ hi
        simp [f, hi]
      · simp
    nlinarith [norm_nonneg f, norm_nonneg χ]
  obtain ⟨u, hu, huniq, hTu, hnorm, _⟩ := hT f
  refine ⟨⟨u, hu, fun v hv => huniq v hv⟩, ?_⟩
  intro v hv
  rw [huniq v hv, ← hTu, ← hf]
  exact hnorm

/-- Polynomial energy bounds imply the two norms in Lemma 4.4.
The intentionally loose exponent avoids any dependence on the input prefactor. -/
theorem norms_of_polynomial_energy (β B p H X E F : ℝ)
    (hβ : 0 < β) (hB : 1 ≤ B) (hp : 0 ≤ p) (hH : 0 ≤ H)
    (_hX : 0 ≤ X) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (he : E + (β * (2 * B)⁻¹) * X ^ 2 ≤ H * B ^ (p + 2) * F ^ 2) :
    X + Real.sqrt E ≤ (Real.sqrt (2 * H / β) + Real.sqrt H) * B ^ (p + 3) * F := by
  have hB0 : 0 < B := by linarith
  have hc : 0 < β * (2 * B)⁻¹ := by positivity
  have hx : X ^ 2 ≤ (2 * H / β) * B ^ (p + 3) * F ^ 2 := by
    apply (mul_le_mul_iff_left₀ hc).mp
    have heq : ((2 * H / β) * B ^ (p + 3) * F ^ 2) * (β * (2 * B)⁻¹) =
        H * B ^ (p + 2) * F ^ 2 := by
      rw [show p + 3 = (p + 2) + 1 by ring, Real.rpow_add hB0, Real.rpow_one]
      field_simp
    rw [← heq] at he
    nlinarith
  have hpow1 : B ^ (p + 2) ≤ (B ^ (p + 3)) ^ 2 := by
    rw [← Real.rpow_mul_natCast hB0.le]
    apply Real.rpow_le_rpow_of_exponent_le hB
    norm_num
    linarith
  have hpow2 : B ^ (p + 3) ≤ (B ^ (p + 3)) ^ 2 := by
    have hh := Real.one_le_rpow hB (show 0 ≤ p + 3 by linarith)
    nlinarith
  have hx' : X ≤ Real.sqrt (2 * H / β) * B ^ (p + 3) * F := by
    have hb := hx.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow2 (by positivity : 0 ≤ 2 * H / β)) (sq_nonneg F))
    have hs := Real.sq_sqrt (show 0 ≤ 2 * H / β by positivity)
    have hr : 0 ≤ Real.sqrt (2 * H / β) * B ^ (p + 3) * F := by positivity
    have heq : (Real.sqrt (2 * H / β) * B ^ (p + 3) * F) ^ 2 =
        (2 * H / β) * (B ^ (p + 3)) ^ 2 * F ^ 2 := by rw [mul_pow, mul_pow, hs]
    nlinarith
  have hg : Real.sqrt E ≤ Real.sqrt H * B ^ (p + 3) * F := by
    have hb : E ≤ H * (B ^ (p + 3)) ^ 2 * F ^ 2 := by
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow1 hH) (sq_nonneg F)
      have hn := mul_nonneg hc.le (sq_nonneg X)
      linarith
    apply (Real.sqrt_le_sqrt hb).trans_eq
    rw [Real.sqrt_mul (mul_nonneg hH (sq_nonneg _)), Real.sqrt_mul hH,
      Real.sqrt_sq (by positivity), Real.sqrt_sq hF]
  nlinarith

end Riesz2.InitialDecay.Internal

namespace Riesz2.InitialDecay

/-- Uniform version of Lemma 4.4 in terms of a single loss
B. The constants precede the base space, component geometry, matrix and source. -/
theorem initial_decay_uniform (s a β : ℝ) (hs : 1 < s)
    (ha : 1 / 2 < a) (has : a < s - 1 / 2) (hβ : 0 < β) :
    ∃ r C : ℝ, 0 ≤ r ∧ 1 ≤ C ∧
      ∀ (α ι : Type*) [MeasurableSpace α] [Fintype ι] [DecidableEq ι]
        (ν : Measure α) [IsProbabilityMeasure ν]
        (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q →
        IsConservativeScalarForm Q → ∀ (g : ComponentGeometry ι) (B : ℝ), 1 ≤ B →
        ∀ M : α → Matrix ι ι ℝ, (∀ i j, Measurable (fun x => M x i j)) →
        (∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧
          (∀ z : ι → ℝ, B⁻¹ * ∑ i, z i ^ 2 ≤ ∑ i, ∑ j, z i * M x i j * z j) ∧
          (∀ i j, |M x i j| ≤ B * (1 + componentDistance g i j) ^ (-s))) →
        ∀ (i₀ : ι) (χ : Lp ℝ 2 ν),
          (∃! u : ι → Q.1, WeightedWeakSolution Q (fun x => β • M x) ⊤
            (fun i => if i = i₀ then χ else 0) u) ∧
          (∀ u : ι → Q.1, WeightedWeakSolution Q (fun x => β • M x) ⊤
              (fun i => if i = i₀ then χ else 0) u →
            ‖WithLp.toLp 2 (fun i => distortionWeight g i₀ a i • (u i).val)‖ +
              Real.sqrt (∑ i, Q.2 (distortionWeight g i₀ a i • u i)
                (distortionWeight g i₀ a i • u i)) ≤ C * B ^ r * ‖χ‖) := by
  obtain ⟨p, D, hp, hD, hpoly⟩ := Internal.polynomial_conjugated_lower s a hs ha has
  let H := (1 + D) / β
  have hH : 0 < H := by dsimp [H]; positivity
  let C := 1 + Real.sqrt (2 * H / β) + Real.sqrt H
  refine ⟨p + 3, C, by linarith, by dsimp [C]; linarith [Real.sqrt_nonneg (2 * H / β), Real.sqrt_nonneg H], ?_⟩
  intro α ι _ _ _ ν _ Q hQ hcons g B hB M hMmeas hM i₀ χ
  have hB0 : 0 < B := by linarith
  let S := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s)
  have hS : 0 ≤ S := mul_nonneg (by norm_num) (tsum_nonneg fun k => by positivity)
  let b := B * (1 + S)
  have hab : B⁻¹ ≤ b := by
    have hh : B ≤ b := by dsimp [b]; nlinarith
    exact (inv_le_one_of_one_le₀ hB).trans (hB.trans hh)
  have hbnd : ∀ᵐ x ∂ν, (∀ i j, M x i j = M x j i) ∧ ∀ z : ι → ℝ,
      B⁻¹ * (∑ i, z i ^ 2) ≤ (∑ i, ∑ j, z i * M x i j * z j) ∧
        (∑ i, ∑ j, z i * M x i j * z j) ≤ b * ∑ i, z i ^ 2 := by
    filter_upwards [hM] with x hx
    refine ⟨hx.1, fun z => ⟨hx.2.1 z, ?_⟩⟩
    have hh := Internal.summable_quadratic_upper s hs g B hB0.le (M x) hx.2.2 z
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    dsimp [b]
    nlinarith
  have henergy := Internal.point_source_energy β hβ Q hQ hcons M hMmeas
    B⁻¹ b (inv_pos.mpr hB0) hab hbnd i₀ χ
  refine ⟨henergy.1, ?_⟩
  intro u hu
  have hscaled : ∀ᵐ x ∂ν, ∀ z : ι → ℝ,
      0 ≤ (∑ i, ∑ j, z i * (β • M x) i j * z j) ∧
        (∑ i, ∑ j, z i * (β • M x) i j * z j) ≤ (β * b) * ∑ i, z i ^ 2 := by
    filter_upwards [hbnd] with x hx z
    have hlow := (mul_nonneg (inv_nonneg.mpr hB0.le)
      (Finset.sum_nonneg (fun i _ => sq_nonneg (z i)))).trans (hx.2 z).1
    have hupp := mul_le_mul_of_nonneg_left (hx.2 z).2 hβ.le
    have he : (∑ i, ∑ j, z i * (β • M x) i j * z j) =
        β * (∑ i, ∑ j, z i * M x i j * z j) := by
      simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc, mul_left_comm]
    rw [he]
    exact ⟨mul_nonneg hβ.le hlow, by simpa only [mul_assoc] using hupp⟩
  have hsym : ∀ᵐ x ∂ν, ∀ i j, (β • M x) i j = (β • M x) j i := by
    filter_upwards [hM] with x hx i j
    change β * M x i j = β * M x j i
    rw [hx.1 i j]
  have hconj : ∀ᵐ x ∂ν, ∀ v : ι → ℝ,
      (β * (2 * B)⁻¹) * (∑ i, (distortionWeight g i₀ a i * v i) ^ 2) -
        (β * D * B ^ p) * (∑ i, v i ^ 2) ≤
      ∑ i, ∑ j, (distortionWeight g i₀ a i * v i) *
        (distortionMatrix g i₀ a * (β • M x) * distortionMatrix g i₀ (-a)) i j *
          (distortionWeight g i₀ a j * v j) := by
    filter_upwards [hM] with x hx v
    have hh := mul_le_mul_of_nonneg_left
      (hpoly ι g i₀ B hB (M x) hx.2.1 hx.2.2 v) hβ.le
    have he : distortionMatrix g i₀ a * (β • M x) * distortionMatrix g i₀ (-a) =
        β • (distortionMatrix g i₀ a * M x * distortionMatrix g i₀ (-a)) := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [he]
    simpa only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_sub,
      mul_assoc, mul_left_comm] using hh
  have he := Internal.weighted_energy_inequality Q g i₀ a (fun x => β • M x)
    (AbstractEnergy.scaled_measurable β M hMmeas) (β * b) hsym hscaled
    (β * (2 * B)⁻¹) (β * D * B ^ p) hconj χ u hu
  let V := ‖WithLp.toLp 2 (fun i => (u i).val)‖
  have hV : V ≤ B / β * ‖χ‖ := by
    have hh := henergy.2 u hu
    convert hh using 1
    congr 1
    field_simp
  have hi : inner ℝ χ (u i₀).val ≤ B / β * ‖χ‖ ^ 2 := by
    calc
      _ ≤ ‖χ‖ * ‖(u i₀).val‖ := real_inner_le_norm _ _
      _ ≤ ‖χ‖ * V := mul_le_mul_of_nonneg_left
        (PiLp.norm_apply_le (WithLp.toLp 2 (fun i => (u i).val)) i₀) (norm_nonneg _)
      _ ≤ ‖χ‖ * (B / β * ‖χ‖) := mul_le_mul_of_nonneg_left hV (norm_nonneg _)
      _ = _ := by ring
  have hVV : V ^ 2 ≤ (B / β * ‖χ‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hV 2
  have hrest : inner ℝ χ (u i₀).val + (β * D * B ^ p) * V ^ 2 ≤
      H * B ^ (p + 2) * ‖χ‖ ^ 2 := by
    have hpow : B ≤ B ^ (p + 2) := by
      calc B = B ^ (1 : ℝ) := (Real.rpow_one B).symm
           _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hB (by linarith)
    calc
      _ ≤ B / β * ‖χ‖ ^ 2 + (β * D * B ^ p) * (B / β * ‖χ‖) ^ 2 := by
        exact add_le_add hi (mul_le_mul_of_nonneg_left hVV (by positivity))
      _ = (B + D * B ^ (p + 2)) / β * ‖χ‖ ^ 2 := by
        rw [Real.rpow_add hB0, Real.rpow_two]
        field_simp
      _ ≤ H * B ^ (p + 2) * ‖χ‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        calc
          (B + D * B ^ (p + 2)) / β ≤
              (B ^ (p + 2) + D * B ^ (p + 2)) / β :=
            div_le_div_of_nonneg_right (add_le_add hpow le_rfl) hβ.le
          _ = H * B ^ (p + 2) := by dsimp [H]; ring
  have he' := he.trans hrest
  have hnorm := Internal.norms_of_polynomial_energy β B p H
    ‖WithLp.toLp 2 (fun i => distortionWeight g i₀ a i • (u i).val)‖
    (∑ i, Q.2 (distortionWeight g i₀ a i • u i) (distortionWeight g i₀ a i • u i))
    ‖χ‖ hβ hB hp hH.le (norm_nonneg _)
    (Finset.sum_nonneg (fun i _ => hQ.2.2.1 _)) (norm_nonneg _) he'
  exact hnorm.trans (by dsimp [C]; gcongr; linarith)

/-- See Lemma 4.4 of the paper (initial weighted decay), with unique
existence in the full weak form domain. Both the weighted value norm and
the weighted diffusion norm are bounded, uniformly over inherited subsets.
The loss exponent is selected before h, A, all spaces, sizes and sources. -/
theorem illustrative (s : ShortExponent) (β : InverseTemperature)
    (a : ℝ) (ha : 1 / 2 < a) (has : a < s.val - 1 / 2)
    (q : ℝ) (hq : 0 ≤ q) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ h : ℝ, 0 < h → ∀ A : ℝ, 1 ≤ A →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ (n : ℕ+) (α ι : Type*)
        [MeasurableSpace α] [Fintype ι] [DecidableEq ι],
        Fintype.card ι ≤ (n : ℕ) → ∀ (g : ComponentGeometry ι)
          (ν : Measure α) [IsProbabilityMeasure ν] (Q : ScalarFormData ν),
        IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
        ∀ M : α → Matrix ι ι ℝ, SummableCoerciveMatrix (ρ := ν) s n h A q g M →
        ∀ (i₀ : ι) (χ : Lp ℝ 2 ν),
          (∃! u : ι → Q.1, WeightedWeakSolution Q (fun x => β.val • M x) ⊤
            (fun i => if i = i₀ then χ else 0) u) ∧
          (∀ u : ι → Q.1, WeightedWeakSolution Q (fun x => β.val • M x) ⊤
              (fun i => if i = i₀ then χ else 0) u →
            ‖WithLp.toLp 2 (fun i => distortionWeight g i₀ a i • (u i).val)‖ +
              Real.sqrt (∑ i, Q.2 (distortionWeight g i₀ a i • u i)
                (distortionWeight g i₀ a i • u i)) ≤ C * (n : ℝ) ^ (r * h) * ‖χ‖) := by
  obtain ⟨r, C, hr, hC, hbound⟩ :=
    initial_decay_uniform s.val a β.val s.property ha has β.property
  refine ⟨q * r, mul_nonneg hq hr, ?_⟩
  intro h hh A hA
  have hA0 : 0 < A := by linarith
  refine ⟨C * A ^ r, one_le_mul_of_one_le_of_one_le hC (Real.one_le_rpow hA hr), ?_⟩
  intro n α ι _ _ _ _hcard g ν _ Q hQ hcons M hM i₀ χ
  have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.property
  have hn0 : (0 : ℝ) < (n : ℝ) := by positivity
  have hB : 1 ≤ A * (n : ℝ) ^ (q * h) :=
    one_le_mul_of_one_le_of_one_le hA (Real.one_le_rpow hn (mul_nonneg hq hh.le))
  have he := hbound α ι ν Q hQ hcons g (A * (n : ℝ) ^ (q * h)) hB M hM.1 hM.2 i₀ χ
  have hfactor : C * (A * (n : ℝ) ^ (q * h)) ^ r =
      (C * A ^ r) * (n : ℝ) ^ ((q * r) * h) := by
    rw [Real.mul_rpow hA0.le (by positivity), ← Real.rpow_mul hn0.le,
      show (q * h) * r = (q * r) * h by ring]
    ring
  simpa only [hfactor] using he

end Riesz2.InitialDecay
