/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.IntegratedCovariance
public import Riesz2.ToMathlib.BoundedExponentialPath
public import Riesz2.HelfferSjostrand.ConditionalEnergyMomentsPart2

/-!
# Domination for physical interpolation

The common nearest-gap barrier controls both endpoint energies. It supplies dominated
differentiation on an open interval containing the whole physical path, including both
endpoints, without requiring bounded endpoint energies.
-/

public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal Topology ContDiff

namespace Riesz2.IntegratedCovariance

/-- The reference measure on the positive intrinsic carrier is exactly
Hausdorff measure on the physical active simplex under the existing isometry.
Thus normalized densities in this chart use the reference measure of
Subsection 6.1, with no change of metric or normalization. -/
theorem map_intrinsic_carrier_volume (n : ℕ) (L : ℝ) :
    let Ω := AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L
    ((volume : Measure (AffineSimplex.Tangent n)).comap (Subtype.val : Ω → _)).map
      (fun w : Ω => AffineSimplex.centredChart n L w.val) =
        AffineSimplex.simplexVolume n L := by
  intro Ω
  have hΩ := (ConditionalWellPosedness.fibre_isOpen n L).measurableSet
  have he := map_comap_subtype_coe (μ := (volume : Measure (AffineSimplex.Tangent n))) hΩ
  change ((volume : Measure (AffineSimplex.Tangent n)).comap (Subtype.val : Ω → _)).map
    (AffineSimplex.centredChart n L ∘ (Subtype.val : Ω → _)) = _
  rw [← Measure.map_map (AffineSimplex.isometry_centredChart n L).continuous.measurable
    measurable_subtype_coe, he, ← AffineSimplex.simplexVolume_eq_centredChart_map]

/-- Internal identification of Mathlib's exponential tilt with the existing
positive finite extended normalization. Integrability excludes a junk zero. -/
theorem internal_tilted_normalization {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [NeZero μ] (f : X → ℝ)
    (hf : Integrable (fun x => Real.exp (f x)) μ) :
    ∃ h0 ht, μ.tilted f = AffineFibre.normalizedMeasure μ
      (fun x => ENNReal.ofReal (Real.exp (f x))) h0 ht := by
  have hp := integral_exp_pos hf
  have h0 : (∫⁻ x, ENNReal.ofReal (Real.exp (f x)) ∂μ) ≠ 0 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hf (ae_of_all _ fun x => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_ne_zero_iff.mpr hp
  have ht : (∫⁻ x, ENNReal.ofReal (Real.exp (f x)) ∂μ) ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hf (ae_of_all _ fun x => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_ne_top
  refine ⟨h0, ht, ?_⟩
  unfold Measure.tilted AffineFibre.normalizedMeasure
  congr 1
  funext x
  exact (AffineFibre.normalizedDensity_ofReal μ hf (fun x => (Real.exp_pos _).le) hp x).symm

/-- Internal normalization bridge from the positive intrinsic carrier to
the existing Hausdorff simplex law. Agreement is required only on the
physical carrier, and the positive finite normalizer is proved from the
integrable exponential weight. -/
theorem internal_normalized_intrinsic_chart (n : ℕ) (L : ℝ)
    (w : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞) (hw : Measurable w)
    (f : (AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L) → ℝ)
    (he : ∀ x, w (AffineSimplex.centredChart n L x.val) = ENNReal.ofReal (Real.exp (f x)))
    (hf : Integrable (fun x => Real.exp (f x)) (volume.comap Subtype.val))
    (hp : 0 < ∫ x, Real.exp (f x) ∂volume.comap Subtype.val) :
    ∃ h0 ht,
      ((volume.comap Subtype.val).tilted f).map
        (fun x => AffineSimplex.centredChart n L x.val) =
      AffineFibre.normalizedMeasure (AffineSimplex.simplexVolume n L) w h0 ht := by
  let Ω := AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L
  let μ : Measure Ω := volume.comap Subtype.val
  let e := fun x : Ω => AffineSimplex.centredChart n L x.val
  have hΩ := (ConditionalWellPosedness.fibre_isOpen n L).measurableSet
  have hemb : MeasurableEmbedding e :=
    (AffineSimplex.isometry_centredChart n L).isClosedEmbedding.measurableEmbedding.comp
      (MeasurableEmbedding.subtype_coe hΩ)
  let : NeZero μ := ⟨fun hh => by
    change 0 < ∫ x, Real.exp (f x) ∂μ at hp
    rw [hh, integral_zero_measure] at hp
    exact lt_irrefl _ hp⟩
  obtain ⟨h0, ht, htilt⟩ := internal_tilted_normalization μ f hf
  have hweight : (fun x : Ω => w (e x)) = fun x => ENNReal.ofReal (Real.exp (f x)) :=
    funext he
  have h0w : (∫⁻ x, w (e x) ∂μ) ≠ 0 := by rw [hweight]; exact h0
  have htw : (∫⁻ x, w (e x) ∂μ) ≠ ⊤ := by rw [hweight]; exact ht
  have hm := AffineFibre.normalizedMeasure_map μ hemb hw h0w htw
  have hvol : μ.map e = AffineSimplex.simplexVolume n L := map_intrinsic_carrier_volume n L
  have h0full : (∫⁻ x, w x ∂AffineSimplex.simplexVolume n L) ≠ 0 := by
    rw [← hvol, hemb.lintegral_map]
    exact h0w
  have htfull : (∫⁻ x, w x ∂AffineSimplex.simplexVolume n L) ≠ ⊤ := by
    rw [← hvol, hemb.lintegral_map]
    exact htw
  simp only [hvol] at hm
  refine ⟨h0full, htfull, ?_⟩
  change (μ.tilted f).map e = _
  rw [htilt]
  simpa only [AffineFibre.normalizedMeasure_eq_smul, hweight] using hm.symm

/-- Internal scalar domination for differentiating an exponential density.
Every power of a linearly controlled score is absorbed by the Gibbs barrier. -/
theorem internal_score_power_bound {c B C : ℝ} (hc : 0 < c) (hB : 0 ≤ B) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ T D V : ℝ, 0 ≤ T →
      |D| ≤ B * (1 + T) → c * T - C ≤ V →
      Real.exp (-V) * |D| ^ k ≤ M := by
  refine ⟨(B / c) ^ k * (Nat.factorial k : ℝ) * Real.exp (C + c), by positivity,
    fun T D V hT hD hV => ?_⟩
  have he := Real.pow_div_factorial_le_exp (c * (1 + T)) (by positivity) k
  have hfac : (0 : ℝ) < Nat.factorial k := by positivity
  rw [div_le_iff₀ hfac] at he
  have hp := pow_le_pow_left₀ (abs_nonneg D) hD k
  have hscale : (B / c) ^ k * (c * (1 + T)) ^ k = (B * (1 + T)) ^ k := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hexp : Real.exp (-V) ≤ Real.exp (C - c * T) :=
    Real.exp_le_exp.mpr (by linarith)
  calc
    Real.exp (-V) * |D| ^ k ≤ Real.exp (C - c * T) * (B * (1 + T)) ^ k :=
      mul_le_mul hexp hp (pow_nonneg (abs_nonneg D) _) (Real.exp_pos _).le
    _ = Real.exp (C - c * T) * ((B / c) ^ k * (c * (1 + T)) ^ k) := by rw [hscale]
    _ ≤ Real.exp (C - c * T) * ((B / c) ^ k *
        (Real.exp (c * (1 + T)) * (Nat.factorial k : ℝ))) := by gcongr
    _ = (B / c) ^ k * (Nat.factorial k : ℝ) *
        (Real.exp (C - c * T) * Real.exp (c * (1 + T))) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

/-- Summation of a scalar function over the actual assembled full gaps.
Reindexing changes neither the active contribution nor the fixed exterior. -/
theorem sum_assemble (n m : ℕ) (σ : Equiv.Perm (Fin (n + m + 1)))
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin (m + 1))) (f : ℝ → ℝ) :
    ∑ i, f (RetainedSimplex.assemble n m σ x y i) =
      (∑ i, f (x i)) + ∑ j, f (y j) := by
  change (∑ i, f (RetainedSimplex.join n (m + 1) (x, y) (σ.symm i))) = _
  calc
    _ = ∑ i, f (RetainedSimplex.join n (m + 1) (x, y) i) :=
      Equiv.sum_comp σ.symm (fun i => f (RetainedSimplex.join n (m + 1) (x, y) i))
    _ = _ := ?_
  rw [Fin.sum_univ_add]
  simp only [RetainedSimplex.join_left, RetainedSimplex.join_right]

/-- The full temperature-weighted energy is bounded above by a multiple of
the sum of inverse-gap powers. This uses the physical energy bound,
with its lower-gap parameter chosen at an attained minimum. -/
theorem physical_energy_sum_upper (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (y : EuclideanSpace ℝ (Fin (N : ℕ)))
      (hy : WithLp.ofLp y ∈ Riesz1.gapSimplex N),
      p.val.1 * physicalAmbientGapEnergy p N
        ⟨y, PhysicalEnergy.simplex_subset_ambient N _ hy⟩ ≤
          C * ∑ i, (y i) ^ (-p.val.2) := by
  classical
  obtain ⟨C, hC, hb⟩ := ConditionalEnergyMoments.physical_energy_upper p N hN
  refine ⟨C, hC, fun y hy => ?_⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ (fun i : Fin (N : ℕ) => y i)
    Finset.univ_nonempty
  exact (hb y hy (y i) (hy.1 i) (fun j => hi j (Finset.mem_univ j))).trans
    (mul_le_mul_of_nonneg_left (Finset.single_le_sum
      (fun j _ => Real.rpow_nonneg (hy.1 j).le _) (Finset.mem_univ i)) hC.le)

/-- Physical endpoint control for Lemma 6.1.
Both bounds use the same active inverse-gap sum. All exterior contributions
enter a finite constant. The energy is the ambient physical energy. -/
theorem fixed_exterior_energy_bounds (p : Parameters) (n m : ℕ)
    (σ : Equiv.Perm (Fin ((n + 1) + m + 1))) {L : ℝ}
    (y : EuclideanSpace ℝ (Fin (m + 1))) (hy : ∀ j, 0 < y j)
    (hcompat : L + ∑ j, y j = ((n + 1 + m : ℕ) + 1 : ℝ)) :
    let Ω := AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L
    let T := fun w : AffineSimplex.Tangent n =>
      ∑ i, (AffineSimplex.centredChart n L w i) ^ (-p.val.2)
    ∃ K : AffineSimplex.Tangent n → ℝ,
      ContDiffOn ℝ ∞ K Ω ∧
      (∀ w (hw : w ∈ Ω), K w = physicalAmbientGapEnergy p (n + 1 + m).succPNat
        ⟨RetainedSimplex.assemble (n + 1) m σ (AffineSimplex.centredChart n L w) y,
          PhysicalEnergy.simplex_subset_ambient _ _ (by
            have hh := ConditionalWellPosedness.assemble_fixed_exterior_mem n m σ y hy hcompat hw
            rw [AffineSimplex.massSimplex_physical] at hh
            exact hh)⟩) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ w ∈ Ω,
        2 * p.val.1 * T w - C ≤ p.val.1 * K w ∧
        |p.val.1 * K w| ≤ C * (1 + T w) := by
  intro Ω T
  obtain ⟨K, hKs, hK⟩ := ConditionalWellPosedness.fixed_exterior_smooth p n m σ y hy hcompat
  obtain ⟨Cl, hCl, hl⟩ := ConditionalEnergyMoments.physical_energy_lower p
    (n + 1 + m).succPNat (by simp only [Nat.succPNat_coe]; omega)
  obtain ⟨Cu, hCu, hu⟩ := physical_energy_sum_upper p (n + 1 + m).succPNat
    (by simp only [Nat.succPNat_coe]; omega)
  let Y := ∑ j, (y j) ^ (-p.val.2)
  have hY : 0 ≤ Y := Finset.sum_nonneg fun j _ => Real.rpow_nonneg (hy j).le _
  let C := Cu * (1 + Y) + Cl
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨K, hKs, hK, C, hC, fun w hw => ?_⟩
  have hw' : AffineSimplex.centredChart n L w ∈ AffineSimplex.massSimplex n L := hw
  have hT : 0 ≤ T w := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hw'.1 i).le _
  let q := RetainedSimplex.assemble (n + 1) m σ (AffineSimplex.centredChart n L w) y
  have hq : WithLp.ofLp q ∈ Riesz1.gapSimplex (n + 1 + m).succPNat := by
    have hh := ConditionalWellPosedness.assemble_fixed_exterior_mem n m σ y hy hcompat hw
    rw [AffineSimplex.massSimplex_physical] at hh
    exact hh
  have hlw := hl q hq
  have huw := hu q hq
  have hsum : (∑ i, (q i) ^ (-p.val.2)) = T w + Y :=
    sum_assemble (n + 1) m σ (AffineSimplex.centredChart n L w) y (fun u => u ^ (-p.val.2))
  simp only [Nat.succPNat_coe] at hlw huw
  rw [hsum, ← hK w hw] at hlw huw
  have hClC : Cl ≤ C := by
    have hh : 0 ≤ Cu * (1 + Y) := by positivity
    dsimp only [C]
    linarith
  constructor
  · nlinarith [mul_nonneg p.property.1.le hY]
  · rw [abs_le]
    constructor
    · have hc := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 1 + T w by linarith) hC.le
      nlinarith [mul_nonneg p.property.1.le (add_nonneg hT hY)]
    · dsimp only [C]
      nlinarith [mul_nonneg (mul_nonneg hCu.le hY) hT, mul_nonneg hCl.le hT]

/-- Internal extension of a common coercive barrier to an open parameter
interval around the closed interpolation segment. -/
theorem internal_interpolation_domination {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ T P Y Z t : ℝ,
      0 ≤ T → 0 ≤ P → a * T - b ≤ Y → a * T - b ≤ Z →
      |Y| ≤ b * (1 + T) → |Z| ≤ b * (1 + T) →
      t ∈ Ioo (-δ) (1 + δ) →
      a / 2 * T - C ≤ P + (1 - t) * Y + t * Z := by
  let δ := a / (4 * b)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have he : δ * (2 * b) = a / 2 := by dsimp [δ]; field_simp; ring
  refine ⟨δ, b + a / 2, hδ, by positivity, fun T P Y Z t hT hP hY hZ hbY hbZ ht => ?_⟩
  have hD : |Y - Z| ≤ 2 * b * (1 + T) :=
    (show |Y - Z| ≤ |Y| + |Z| by simpa using abs_sub_le Y 0 Z).trans (by linarith)
  by_cases ht0 : t < 0
  · have habs : |t| ≤ δ := by rw [abs_of_neg ht0]; linarith [ht.1]
    have hmul := mul_le_mul habs hD (abs_nonneg _) hδ.le
    rw [← abs_mul] at hmul
    have hl := le_abs_self (t * (Y - Z))
    have hmul' : |t * (Y - Z)| ≤ a / 2 * (1 + T) := by
      simpa only [← mul_assoc, he] using hmul
    nlinarith
  · by_cases ht1 : t ≤ 1
    · have h0 : 0 ≤ t := le_of_not_gt ht0
      have hy := mul_le_mul_of_nonneg_left hY (show 0 ≤ 1 - t by linarith)
      have hz := mul_le_mul_of_nonneg_left hZ h0
      nlinarith [mul_nonneg ha.le hT]
    · have habs : |t - 1| ≤ δ := by rw [abs_of_pos (by linarith : 0 < t - 1)]; linarith [ht.2]
      have hmul := mul_le_mul habs hD (abs_nonneg _) hδ.le
      rw [← abs_mul] at hmul
      have hl := le_abs_self ((t - 1) * (Y - Z))
      have hmul' : |(t - 1) * (Y - Z)| ≤ a / 2 * (1 + T) := by
        simpa only [← mul_assoc, he] using hmul
      nlinarith

section DominatedPath

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
variable {V D T G : X → ℝ} {J : Set ℝ} {c B C A : ℝ}

/-- Internal integrability of every score moment, uniformly on a parameter
interval where the common Gibbs barrier persists. -/
theorem internal_moment_integrable (hV : Measurable V) (hD : Measurable D)
    (hG : Measurable G) (hc : 0 < c) (hB : 0 ≤ B) (_hA : 0 ≤ A)
    (hT : ∀ x, 0 ≤ T x) (hDb : ∀ x, |D x| ≤ B * (1 + T x))
    (hGb : ∀ x, |G x| ≤ A)
    (hco : ∀ t ∈ J, ∀ x, c * T x - C ≤ V x - t * D x)
    (k : ℕ) {t : ℝ} (ht : t ∈ J) :
    Integrable (fun x => Real.exp (-V x + t * D x) * D x ^ k * G x) μ := by
  obtain ⟨M, hM, hb⟩ := internal_score_power_bound (C := C) hc hB k
  apply (integrable_const (M * A)).mono'
    ((((hV.neg.add (hD.const_mul t)).exp).mul (hD.pow_const k)).mul hG).aestronglyMeasurable
  apply ae_of_all
  intro x
  change |Real.exp (-V x + t * D x) * D x ^ k * G x| ≤ M * A
  rw [abs_mul, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul _ (hGb x) (abs_nonneg _) hM
  have hh := hb (T x) (D x) (V x - t * D x) (hT x) (hDb x) (hco t ht x)
  rwa [show -(V x - t * D x) = -V x + t * D x by ring] at hh

/-- Internal dominated derivative of each raw score moment. A common
collision barrier, rather than boundedness of the score, gives domination. -/
theorem internal_moment_hasDerivAt (hJ : IsOpen J)
    (hV : Measurable V) (hD : Measurable D) (hG : Measurable G)
    (hc : 0 < c) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hT : ∀ x, 0 ≤ T x) (hDb : ∀ x, |D x| ≤ B * (1 + T x))
    (hGb : ∀ x, |G x| ≤ A)
    (hco : ∀ t ∈ J, ∀ x, c * T x - C ≤ V x - t * D x)
    (k : ℕ) {t : ℝ} (ht : t ∈ J) :
    HasDerivAt (fun u => ∫ x, Real.exp (-V x + u * D x) * D x ^ k * G x ∂μ)
      (∫ x, Real.exp (-V x + t * D x) * D x ^ (k + 1) * G x ∂μ) t := by
  obtain ⟨M, hM, hb⟩ := internal_score_power_bound (C := C) hc hB (k + 1)
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun u x => Real.exp (-V x + u * D x) * D x ^ (k + 1) * G x)
    (bound := fun _ => M * A) (s := J) (hJ.mem_nhds ht)
    (Eventually.of_forall fun u =>
      ((((hV.neg.add (hD.const_mul u)).exp).mul (hD.pow_const k)).mul hG).aestronglyMeasurable)
    (internal_moment_integrable hV hD hG hc hB hA hT hDb hGb hco k ht)
    (((((hV.neg.add (hD.const_mul t)).exp).mul (hD.pow_const (k + 1))).mul hG).aestronglyMeasurable)
    ?_ (integrable_const _) ?_).2
  · apply ae_of_all
    intro x u hu
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul _ (hGb x) (abs_nonneg _) hM
    have hh := hb (T x) (D x) (V x - u * D x) (hT x) (hDb x) (hco u hu x)
    rwa [show -(V x - u * D x) = -V x + u * D x by ring] at hh
  · apply ae_of_all
    intro x u _
    convert (((hasDerivAt_const u (-V x)).add
      ((hasDerivAt_id u).mul_const (D x))).exp.mul_const (D x ^ k)).mul_const (G x) using 1
    · funext v
      simp only [Pi.mul_apply, Pi.add_apply, Pi.neg_apply, id_eq]
    · simp only [Pi.add_apply, id_eq, zero_add, one_mul, pow_succ]
      ring

/-- Internal smoothness of raw moments under a common collision barrier. -/
theorem internal_moment_smooth (hJ : IsOpen J)
    (hV : Measurable V) (hD : Measurable D) (hG : Measurable G)
    (hc : 0 < c) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hT : ∀ x, 0 ≤ T x) (hDb : ∀ x, |D x| ≤ B * (1 + T x))
    (hGb : ∀ x, |G x| ≤ A)
    (hco : ∀ t ∈ J, ∀ x, c * T x - C ≤ V x - t * D x) (k : ℕ) :
    ContDiffOn ℝ ∞ (fun u => ∫ x, Real.exp (-V x + u * D x) * D x ^ k * G x ∂μ) J := by
  apply contDiffOn_infty.mpr
  intro n
  induction n generalizing k with
  | zero =>
    apply contDiffOn_zero.mpr
    intro t ht
    exact (internal_moment_hasDerivAt hJ hV hD hG hc hB hA hT hDb hGb hco k ht).continuousAt.continuousWithinAt
  | succ n ih =>
    rw [show ((n + 1 : ℕ) : ℕ∞ω) = (n : ℕ∞ω) + 1 by simp,
      contDiffOn_succ_iff_deriv_of_isOpen hJ]
    refine ⟨fun t ht =>
      (internal_moment_hasDerivAt hJ hV hD hG hc hB hA hT hDb hGb hco k ht).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    exact (ih (k + 1)).congr fun t ht =>
      (internal_moment_hasDerivAt hJ hV hD hG hc hB hA hT hDb hGb hco k ht).deriv

variable [NeZero μ]

/-- Internal normalized calculus with an unbounded score controlled by the
common collision barrier. All square integrabilities are proved. -/
theorem internal_expectation_calculus (hJ : IsOpen J)
    (hV : Measurable V) (hD : Measurable D) (hG : Measurable G)
    (hc : 0 < c) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hT : ∀ x, 0 ≤ T x) (hDb : ∀ x, |D x| ≤ B * (1 + T x))
    (hGb : ∀ x, |G x| ≤ A)
    (hco : ∀ t ∈ J, ∀ x, c * T x - C ≤ V x - t * D x) :
    ContDiffOn ℝ ∞ (fun t => ∫ x, G x ∂μ.tilted (fun x => -V x + t * D x)) J ∧
      ∀ t ∈ J,
        IsProbabilityMeasure (μ.tilted (fun x => -V x + t * D x)) ∧
        MemLp G 2 (μ.tilted (fun x => -V x + t * D x)) ∧
        MemLp D 2 (μ.tilted (fun x => -V x + t * D x)) ∧
        HasDerivAt (fun u => ∫ x, G x ∂μ.tilted (fun x => -V x + u * D x))
          (covariance G D (μ.tilted (fun x => -V x + t * D x))) t := by
  have h1 : ∀ x : X, |(1 : ℝ)| ≤ 1 := fun _ => by norm_num
  have hint (t : ℝ) (ht : t ∈ J) : Integrable (fun x => Real.exp (-V x + t * D x)) μ := by
    simpa only [pow_zero, mul_one] using internal_moment_integrable (μ := μ)
      hV hD measurable_const hc hB (show (0 : ℝ) ≤ 1 by norm_num) hT hDb h1 hco 0 ht
  have hpos (t : ℝ) (ht : t ∈ J) : 0 < ∫ x, Real.exp (-V x + t * D x) ∂μ :=
    integral_exp_pos (hint t ht)
  have he (t : ℝ) : (∫ x, G x ∂μ.tilted (fun x => -V x + t * D x)) =
      (∫ x, Real.exp (-V x + t * D x) * G x ∂μ) /
        (∫ x, Real.exp (-V x + t * D x) ∂μ) := by
    simpa only [one_mul] using BoundedExponentialPath.integral_eq_ratio μ
      (fun x => -V x + t * D x) G 1
  have hsnum : ContDiffOn ℝ ∞ (fun t => ∫ x, Real.exp (-V x + t * D x) * G x ∂μ) J := by
    simpa only [pow_zero, mul_one] using internal_moment_smooth (μ := μ)
      hJ hV hD hG hc hB hA hT hDb hGb hco 0
  have hsden : ContDiffOn ℝ ∞ (fun t => ∫ x, Real.exp (-V x + t * D x) ∂μ) J := by
    simpa only [pow_zero, mul_one] using internal_moment_smooth (μ := μ)
      hJ hV hD measurable_const hc hB (show (0 : ℝ) ≤ 1 by norm_num) hT hDb h1 hco 0
  refine ⟨?_, fun t ht => ?_⟩
  · simp_rw [he]
    exact hsnum.div hsden (fun t ht => (hpos t ht).ne')
  · have hp := isProbabilityMeasure_tilted (hint t ht)
    have hG2 : MemLp G 2 (μ.tilted (fun x => -V x + t * D x)) :=
      MemLp.of_bound hG.aestronglyMeasurable A (ae_of_all _ hGb)
    have hD2 : MemLp D 2 (μ.tilted (fun x => -V x + t * D x)) := by
      apply (memLp_two_iff_integrable_sq hD.aestronglyMeasurable).mpr
      apply (integrable_tilted_iff (hint t ht) (fun x => D x ^ 2)).mpr
      simpa only [smul_eq_mul, mul_one] using internal_moment_integrable (μ := μ)
        hV hD measurable_const hc hB (show (0 : ℝ) ≤ 1 by norm_num) hT hDb h1 hco 2 ht
    refine ⟨hp, hG2, hD2, ?_⟩
    have hnum : HasDerivAt (fun u => ∫ x, Real.exp (-V x + u * D x) * G x ∂μ)
        (∫ x, Real.exp (-V x + t * D x) * D x * G x ∂μ) t := by
      simpa only [Nat.zero_add, pow_zero, pow_one, mul_one] using internal_moment_hasDerivAt (μ := μ)
        hJ hV hD hG hc hB hA hT hDb hGb hco 0 ht
    have hden : HasDerivAt (fun u => ∫ x, Real.exp (-V x + u * D x) ∂μ)
        (∫ x, Real.exp (-V x + t * D x) * D x ∂μ) t := by
      simpa only [Nat.zero_add, pow_zero, pow_one, mul_one] using internal_moment_hasDerivAt (μ := μ)
        hJ hV hD measurable_const hc hB (show (0 : ℝ) ≤ 1 by norm_num) hT hDb h1 hco 0 ht
    simp_rw [he]
    convert hnum.div hden (hpos t ht).ne' using 1
    rw [covariance_eq_sub hG2 hD2]
    simp_rw [show ∀ F : X → ℝ, (∫ x, F x ∂μ.tilted (fun x => -V x + t * D x)) =
        (∫ x, Real.exp (-V x + t * D x) * F x ∂μ) /
          (∫ x, Real.exp (-V x + t * D x) ∂μ) from fun F => by
      simpa only [one_mul] using BoundedExponentialPath.integral_eq_ratio μ
        (fun x => -V x + t * D x) F 1]
    simp only [Pi.mul_apply]
    have hcomm : (∫ x, Real.exp (-V x + t * D x) * (G x * D x) ∂μ) =
        ∫ x, Real.exp (-V x + t * D x) * D x * G x ∂μ := by
      congr 1
      funext x
      ring
    rw [hcomm]
    field_simp

/-- Internal integrated covariance identity under common-barrier domination,
including differentiability on a neighborhood of both endpoints. -/
theorem internal_integrated_covariance (hJ : IsOpen J) (h01 : Icc (0 : ℝ) 1 ⊆ J)
    (hV : Measurable V) (hD : Measurable D) (hG : Measurable G)
    (hc : 0 < c) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hT : ∀ x, 0 ≤ T x) (hDb : ∀ x, |D x| ≤ B * (1 + T x))
    (hGb : ∀ x, |G x| ≤ A)
    (hco : ∀ t ∈ J, ∀ x, c * T x - C ≤ V x - t * D x) :
    ContDiffOn ℝ ∞ (fun t => ∫ x, G x ∂μ.tilted (fun x => -V x + t * D x)) J ∧
    IntervalIntegrable
      (fun t => covariance G D (μ.tilted (fun x => -V x + t * D x))) volume 0 1 ∧
    (∫ x, G x ∂μ.tilted (fun x => -V x + D x)) -
      (∫ x, G x ∂μ.tilted (fun x => -V x)) =
        ∫ t in (0 : ℝ)..1, covariance G D (μ.tilted (fun x => -V x + t * D x)) := by
  obtain ⟨hs, hd⟩ := internal_expectation_calculus (μ := μ) hJ hV hD hG hc hB hA hT hDb hGb hco
  have hcont : ContinuousOn
      (fun t => covariance G D (μ.tilted (fun x => -V x + t * D x))) (Icc 0 1) := by
    apply ((hs.continuousOn_deriv_of_isOpen hJ (by simp)).mono h01).congr
    intro t ht
    exact (hd t (h01 ht)).2.2.2.deriv.symm
  have hi' : IntervalIntegrable
      (fun t => covariance G D (μ.tilted (fun x => -V x + t * D x))) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hcont
  refine ⟨hs, hi', ?_⟩
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => (hd t (h01 (by simpa using ht))).2.2.2) hi'
  simpa only [one_mul, zero_mul, add_zero] using hf.symm

end DominatedPath

/-- See Lemma 6.1 of the paper, in the existing isometric intrinsic
chart on its positive carrier. The energies are the physical
energies with compatible positive exteriors and the exact two-sided penalty.
The expectation is smooth on an open neighborhood of `[0,1]`. All moments
needed for covariance and the time integral are finite. No typicality or
additional domination hypothesis is imposed. -/
theorem integrated_representation (p : Parameters) (n m r : ℕ) (_hn : 1 ≤ n)
    (σ : Equiv.Perm (Fin ((n + 1) + m + 1)))
    (τ : Equiv.Perm (Fin ((n + 1) + r + 1))) {L : ℝ} (hL : 0 < L)
    (y : EuclideanSpace ℝ (Fin (m + 1))) (hy : ∀ j, 0 < y j)
    (z : EuclideanSpace ℝ (Fin (r + 1))) (hz : ∀ j, 0 < z j)
    (hcompatY : L + ∑ j, y j = ((n + 1 + m : ℕ) + 1 : ℝ))
    (hcompatZ : L + ∑ j, z j = ((n + 1 + r : ℕ) + 1 : ℝ))
    (θ : PhysicalCutoff) (ε : ℝ) (_hε : 0 < ε)
    (G : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) (hG : Measurable G)
    (hGb : ∃ A : ℝ, ∀ x, |G x| ≤ A) :
    let Ω := AffineSimplex.centredChart n L ⁻¹' AffineSimplex.massSimplex n L
    ∃ Ky Kz : AffineSimplex.Tangent n → ℝ,
      (∀ w (hw : w ∈ Ω), Ky w = physicalAmbientGapEnergy p (n + 1 + m).succPNat
        ⟨RetainedSimplex.assemble (n + 1) m σ (AffineSimplex.centredChart n L w) y,
          PhysicalEnergy.simplex_subset_ambient _ _ (by
            have hh := ConditionalWellPosedness.assemble_fixed_exterior_mem n m σ y hy hcompatY hw
            rw [AffineSimplex.massSimplex_physical] at hh
            exact hh)⟩) ∧
      (∀ w (hw : w ∈ Ω), Kz w = physicalAmbientGapEnergy p (n + 1 + r).succPNat
        ⟨RetainedSimplex.assemble (n + 1) r τ (AffineSimplex.centredChart n L w) z,
          PhysicalEnergy.simplex_subset_ambient _ _ (by
            have hh := ConditionalWellPosedness.assemble_fixed_exterior_mem n r τ z hz hcompatZ hw
            rw [AffineSimplex.massSimplex_physical] at hh
            exact hh)⟩) ∧
      let μ : Measure Ω := volume.comap Subtype.val
      let P := fun w : AffineSimplex.Tangent n => ∑ i,
        (θ.val (((n + 1 : ℕ) : ℝ) ^ (-ε) * AffineSimplex.centredChart n L w i) +
          θ.val (((n + 1 : ℕ) : ℝ) ^ (-ε) * (AffineSimplex.centredChart n L w i)⁻¹))
      let V := fun t w => p.val.1 * (P w + (1 - t) * Ky w + t * Kz w)
      let ν := fun t => μ.tilted (fun w : Ω => -V t w.val)
      let g := fun w : Ω => G (AffineSimplex.centredChart n L w.val)
      let D := fun w : Ω => Ky w.val - Kz w.val
      ∃ δ : ℝ, 0 < δ ∧
        ContDiffOn ℝ ∞ (fun t => ∫ w, g w ∂ν t) (Ioo (-δ) (1 + δ)) ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          Integrable (fun w : Ω => Real.exp (-V t w.val)) μ ∧
          (0 < ∫ w, Real.exp (-V t w.val) ∂μ) ∧
          (∃ h0 ht, ν t = AffineFibre.normalizedMeasure μ
            (fun w : Ω => ENNReal.ofReal (Real.exp (-V t w.val))) h0 ht) ∧
          IsProbabilityMeasure (ν t) ∧
          MemLp g 2 (ν t) ∧ MemLp D 2 (ν t) ∧
          HasDerivAt (fun u => ∫ w, g w ∂ν u) (p.val.1 * covariance g D (ν t)) t) ∧
        IntervalIntegrable (fun t => covariance g D (ν t)) volume 0 1 ∧
        (∫ w, g w ∂ν 1) - (∫ w, g w ∂ν 0) =
          p.val.1 * ∫ t in (0 : ℝ)..1, covariance g D (ν t) := by
  intro Ω
  obtain ⟨Ky, hKys, hKy, Cy, hCy, hby⟩ := fixed_exterior_energy_bounds p n m σ y hy hcompatY
  obtain ⟨Kz, hKzs, hKz, Cz, hCz, hbz⟩ := fixed_exterior_energy_bounds p n r τ z hz hcompatZ
  refine ⟨Ky, Kz, hKy, hKz, ?_⟩
  intro μ P V ν g D
  have hΩ := ConditionalWellPosedness.fibre_isOpen n L
  have hΩb := ConditionalWellPosedness.fibre_isBounded n L
  have hμ : μ univ = volume Ω := by
    change (volume.comap (Subtype.val : Ω → AffineSimplex.Tangent n)) univ = volume Ω
    rw [comap_subtype_coe_apply hΩ.measurableSet, Set.image_univ, Subtype.range_coe]
  let : IsFiniteMeasure μ := ⟨by
    rw [hμ]
    exact lt_of_le_of_lt (measure_mono subset_closure) hΩb.isCompact_closure.measure_lt_top⟩
  have hzero : (0 : AffineSimplex.Tangent n) ∈ Ω := by
    simpa only [Ω, mem_preimage, AffineSimplex.centredChart, Submodule.coe_zero, zero_add]
      using AffineSimplex.centre_mem_simplex n hL
  let : NeZero μ := ⟨fun hh => by
    have hp := hΩ.measure_pos (volume : Measure (AffineSimplex.Tangent n)) ⟨0, hzero⟩
    rw [← hμ, hh] at hp
    simp at hp⟩
  let T := fun w : Ω => ∑ i, (AffineSimplex.centredChart n L w.val i) ^ (-p.val.2)
  let E := fun w : Ω => p.val.1 * (P w.val + Ky w.val)
  let S := fun w : Ω => p.val.1 * D w
  have hT : ∀ w, 0 ≤ T w := fun w => Finset.sum_nonneg fun i _ =>
    Real.rpow_nonneg (w.property.1 i).le _
  have ha : 0 < ((n + 1 : ℕ) : ℝ) ^ (-ε) := Real.rpow_pos_of_pos (by positivity) _
  have hPs : ContDiffOn ℝ ∞ P Ω := by
    simpa only [ite_true] using ConditionalWellPosedness.fibre_penalty_smooth n L θ ha Finset.univ true
  have hP : ∀ w : Ω, 0 ≤ p.val.1 * P w.val := by
    intro w
    apply mul_nonneg p.property.1.le
    apply Finset.sum_nonneg
    intro i _
    exact add_nonneg
      (θ.property.2.2.1 _ (mul_nonneg ha.le (w.property.1 i).le))
      (θ.property.2.2.1 _ (mul_nonneg ha.le (inv_nonneg.mpr (w.property.1 i).le)))
  have hE : Measurable E := ((hPs.add hKys).continuousOn.comp_continuous
    continuous_subtype_val (fun w => w.property)).measurable.const_mul _
  have hD : Measurable D := ((hKys.sub hKzs).continuousOn.comp_continuous
    continuous_subtype_val (fun w => w.property)).measurable
  have hS : Measurable S := hD.const_mul _
  have hg : Measurable g := hG.comp
    (((ConditionalWellPosedness.centredChart_smooth n L).continuous.comp continuous_subtype_val).measurable)
  obtain ⟨A, hA⟩ := hGb
  have hAn : 0 ≤ A := (abs_nonneg (G 0)).trans (hA 0)
  have hgA : ∀ w, |g w| ≤ A := fun w => hA _
  let b := Cy + Cz
  have hb : 0 < b := add_pos hCy hCz
  have hbY (w : Ω) : |p.val.1 * Ky w.val| ≤ b * (1 + T w) :=
    (hby w.val w.property).2.trans
      (mul_le_mul_of_nonneg_right (by dsimp [b]; linarith) (by linarith [hT w]))
  have hbZ (w : Ω) : |p.val.1 * Kz w.val| ≤ b * (1 + T w) :=
    (hbz w.val w.property).2.trans
      (mul_le_mul_of_nonneg_right (by dsimp [b]; linarith) (by linarith [hT w]))
  have hSb : ∀ w, |S w| ≤ (2 * b) * (1 + T w) := by
    intro w
    have hh : |p.val.1 * Ky w.val - p.val.1 * Kz w.val| ≤
        |p.val.1 * Ky w.val| + |p.val.1 * Kz w.val| := by
      simpa using abs_sub_le (p.val.1 * Ky w.val) 0 (p.val.1 * Kz w.val)
    dsimp only [S, D]
    rw [mul_sub]
    linarith [hbY w, hbZ w]
  obtain ⟨δ, C, hδ, _, hdom⟩ := internal_interpolation_domination
    (a := 2 * p.val.1) (mul_pos (by norm_num) p.property.1) hb
  have hco : ∀ t ∈ Ioo (-δ) (1 + δ), ∀ w, p.val.1 * T w - C ≤ E w - t * S w := by
    intro t ht w
    have hyw := (hby w.val w.property).1
    have hzw := (hbz w.val w.property).1
    have hh := hdom (T w) (p.val.1 * P w.val) (p.val.1 * Ky w.val)
      (p.val.1 * Kz w.val) t (hT w) (hP w)
      (by dsimp [b]; linarith) (by dsimp [b]; linarith) (hbY w) (hbZ w) ht
    dsimp only [E, S, D]
    nlinarith only [hh]
  have he (t : ℝ) : (fun w : Ω => -E w + t * S w) = fun w : Ω => -V t w.val := by
    funext w
    dsimp only [E, S, D, V]
    ring
  have h01 : Icc (0 : ℝ) 1 ⊆ Ioo (-δ) (1 + δ) := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨hs, hi, hid⟩ := internal_integrated_covariance (μ := μ) isOpen_Ioo h01
    hE hS hg p.property.1 (by positivity) hAn hT hSb hgA hco
  obtain ⟨_, hd⟩ := internal_expectation_calculus (μ := μ) isOpen_Ioo
    hE hS hg p.property.1 (by positivity) hAn hT hSb hgA hco
  simp_rw [he] at hs hi hd
  change ContDiffOn ℝ ∞ (fun t => ∫ w, g w ∂ν t) _ at hs
  change IntervalIntegrable (fun t => covariance g S (ν t)) volume 0 1 at hi
  have hcov (t : ℝ) : covariance g S (ν t) = p.val.1 * covariance g D (ν t) :=
    covariance_const_mul_right p.val.1
  refine ⟨δ, hδ, hs, fun t ht => ?_, ?_, ?_⟩
  · obtain ⟨hp, hg2, hS2, hder⟩ := hd t (h01 ht)
    have hint : Integrable (fun w : Ω => Real.exp (-V t w.val)) μ := by
      have hh := internal_moment_integrable (μ := μ) (G := fun _ : Ω => (1 : ℝ))
        hE hS measurable_const p.property.1 (by positivity) (show (0 : ℝ) ≤ 1 by norm_num)
        hT hSb (fun _ => by norm_num) hco 0 (h01 ht)
      simp only [pow_zero, mul_one] at hh
      convert hh using 1
      funext w
      congr 1
      exact (congrFun (he t) w).symm
    have hD2 : MemLp D 2 (ν t) := by
      convert hS2.const_mul p.val.1⁻¹ using 1
      funext w
      dsimp only [S]
      rw [inv_mul_cancel_left₀ p.property.1.ne']
    change HasDerivAt (fun u => ∫ w, g w ∂ν u) (covariance g S (ν t)) t at hder
    rw [hcov] at hder
    exact ⟨hint, integral_exp_pos hint, internal_tilted_normalization μ _ hint,
      hp, hg2, hD2, hder⟩
  · have hh := hi.const_mul p.val.1⁻¹
    convert hh using 1
    funext t
    rw [hcov, inv_mul_cancel_left₀ p.property.1.ne']
  · have he0 : (fun w => -E w) = fun w : Ω => -V 0 w.val := by
      simpa only [zero_mul, add_zero] using he 0
    have he1 : (fun w => -E w + S w) = fun w : Ω => -V 1 w.val := by
      simpa only [one_mul] using he 1
    rw [he0, he1] at hid
    simp_rw [he] at hid
    change (∫ w, g w ∂ν 1) - (∫ w, g w ∂ν 0) =
      ∫ t in (0 : ℝ)..1, covariance g S (ν t) at hid
    simp_rw [hcov] at hid
    rw [intervalIntegral.integral_const_mul] at hid
    exact hid

end Riesz2.IntegratedCovariance
