/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.InterpolantLocalLawsPart8
public import Riesz2.Thermodynamic.InterpolantLocalLawsPart9
public import Riesz2.DecayLong.PaperCutoffDegree

/-!
# Admissibility and physical interpolation local laws

Assembly of the estimates for Appendix C.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal BigOperators Topology

namespace Riesz2.InterpolantLocalLaws

/-- Internal numerical absorption for Appendix C.
The strictly larger negative power retains its exponent, including bounded sizes. -/
theorem internal_competing_powers {a b B c : ℝ} (ha : 0 < a) (hab : a < b)
    (hB : 0 ≤ B) (hc : 0 < c) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, 1 ≤ n →
      Real.exp (B * (n : ℝ) ^ a - c * (n : ℝ) ^ b) ≤
        D * Real.exp (-(c / 2) * (n : ℝ) ^ b) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  obtain ⟨T, hT⟩ := eventually_atTop.mp (ht.eventually_ge_atTop (2 * B / c))
  let R : ℝ := max T 1
  let Q := B * R ^ a + c / 2 * R ^ b
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨Real.exp Q, Real.exp_pos _, ?_⟩
  intro n hn
  have hnp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  by_cases hlarge : T ≤ n
  · have hp : B * (n : ℝ) ^ a ≤ c / 2 * (n : ℝ) ^ b := by
      have hh := (div_le_iff₀ hc).mp (hT n hlarge)
      have hmul := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hnp.le a)
      have he : (n : ℝ) ^ (b - a) * (n : ℝ) ^ a = (n : ℝ) ^ b := by
        rw [← Real.rpow_add hnp]; congr 1; ring
      have he' : (n : ℝ) ^ (b - a) * c * (n : ℝ) ^ a = c * (n : ℝ) ^ b := by
        rw [← he]; ring
      rw [he'] at hmul
      nlinarith
    linarith
  · have hnR : (n : ℝ) ≤ R := by
      apply le_trans _ (le_max_left _ _)
      exact_mod_cast (show n ≤ T by omega)
    have hna := Real.rpow_le_rpow hnp.le hnR ha.le
    have hnb := Real.rpow_le_rpow hnp.le hnR (show 0 ≤ b by linarith)
    have hb0 : 0 ≤ (n : ℝ) ^ b := by positivity
    dsimp only [Q]
    nlinarith [mul_le_mul_of_nonneg_left hna hB,
      mul_le_mul_of_nonneg_left hnb (show 0 ≤ c / 2 by positivity)]

/-- Internal common-exponent comparison for Appendix C. -/
theorem internal_lower_tail_power {n δ q c d C : ℝ} (hn : 1 ≤ n)
    (hδ : δ ≤ q) (hd : 0 ≤ d) (hdc : d ≤ c) (hC : 0 ≤ C) :
    C * Real.exp (-c * n ^ q) ≤ C * Real.exp (-d * n ^ δ) := by
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.mpr
  have hp := Real.rpow_le_rpow_of_exponent_le hn hδ
  have hh := mul_le_mul hp hdc hd (Real.rpow_nonneg (by linarith) q)
  linarith

/-- See Appendix C in the paper, complete typicality clause equation (6.10).
The structural constants precede the tolerance, and the positive tail power
precedes every compact temperature interval. -/
theorem admissible_exteriors_typical (hRig : External.LongRangeRigidityLocallyUniform)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) (A : ℝ) (hA : 1 < A) :
    ∃ K ε₀ : ℝ, 1 < K ∧ 0 < ε₀ ∧
      ε₀ ≤ min (1 - min s 1 / 2) (s - min s 1 / 2) / 4 ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
      ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
        ∀ d m : ℕ, ∀ hd : 1 ≤ d, 1 ≤ m → 4 * (m + 1) ≤ d + m + 1 →
          ((m + 1 : ℕ) : ℝ) ^ (2 / s) ≤ ((d + m : ℕ) + 1 : ℝ) →
          (physicalExteriorLaw p d m θ ε) {y | ¬admissibleExterior p d m hd θ ε A K y} ≤
            ENNReal.ofReal (C * Real.exp (-c * ((m + 1 : ℕ) : ℝ) ^ δ)) := by
  obtain ⟨ηstar, astar, εstar, hηstar, hastar, hεstar, hfull⟩ :=
    full_law_local_laws hRig s hs hs1
  let K := 2 + (3 * A + 1) / astar
  have hK : 1 < K := by
    dsimp [K]
    have : 0 < (3 * A + 1) / astar := by positivity
    linarith
  have hAK : 3 * A < astar * K := by
    dsimp [K]; field_simp; nlinarith
  let margin := min (1 - min s 1 / 2) (s - min s 1 / 2) / 4
  have hmargin : 0 < margin := by
    apply div_pos _ (by norm_num)
    apply lt_min
    · linarith [min_le_right s 1]
    · linarith [min_le_left s 1]
  let ε₀ := min (ηstar / (4 * K)) (min εstar (min (1 / 4) margin))
  have hε₀ : 0 < ε₀ := lt_min (by positivity)
    (lt_min hεstar (lt_min (by norm_num) hmargin))
  refine ⟨K, ε₀, hK, hε₀,
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)), ?_⟩
  intro ε hε hεε
  have hεK : ε < ηstar / (4 * K) := hεε.trans_le (min_le_left _ _)
  have hKη : K * ε ≤ ηstar := by
    have hh := (lt_div_iff₀ (show 0 < 4 * K by positivity)).mp hεK
    nlinarith
  have hεη : ε ≤ ηstar := (by nlinarith : ε ≤ K * ε).trans hKη
  have hεstar' : ε ≤ εstar := hεε.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεquarter : ε ≤ 1 / 4 := hεε.le.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεmargin : ε < margin := hεε.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hεgeo : ε / 2 ≤ (1 - min s 1 / 2) / 4 := by
    have hh := hεmargin.trans_le (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
    linarith
  let g := ε * ((1 - min s 1 / 2) / 4) / (4 * (4 * (s + 2)))
  have hg : 0 < g := by
    dsimp [g]
    have : 0 < 1 - min s 1 / 2 := by linarith [min_le_right s 1]
    positivity
  let δ := min (astar * ε) g
  have hδ : 0 < δ := lt_min (mul_pos hastar hε) hg
  refine ⟨δ, hδ, ?_⟩
  intro βlo βhi hlo hle θ
  obtain ⟨_, _, _, hcoarse⟩ := hfull ε hε hεη ε hε hεstar'
  obtain ⟨C₀, c₀, hC₀, hc₀, hcoarse⟩ := hcoarse βlo βhi hlo hle θ
  obtain ⟨_, _, _, hfine⟩ := hfull (K * ε) (by positivity) hKη ε hε hεstar'
  obtain ⟨C₁, c₁, hC₁, hc₁, hfine⟩ := hfine βlo βhi hlo hle θ
  obtain ⟨Cg, cg, hCg, hcg, hgeom⟩ := compact_exterior_marginal_geometry hRig s ε βlo βhi
    hs hs1 hε hεquarter hεgeo hlo hle θ
  obtain ⟨D, hD, hDtail⟩ := internal_competing_powers (a := 2 * A * ε)
    (b := astar * (K * ε)) (B := 1) (by positivity)
    (by nlinarith [mul_pos hε (show 0 < astar * K - 3 * A by linarith)]) (by norm_num) hc₁
  let c := min cg (min c₀ (c₁ / 2))
  have hc : 0 < c := lt_min hcg (lt_min hc₀ (by positivity))
  refine ⟨Cg + 2 * C₀ + C₁ * D, c, by positivity, hc, ?_⟩
  intro p hps hpl hph d m hd hm hsize hsize'
  let n : ℝ := ((m + 1 : ℕ) : ℝ)
  have hn : 1 ≤ n := by dsimp [n]; exact_mod_cast (show 1 ≤ m + 1 by omega)
  have hpδ : δ ≤ astar * (K * ε) := (min_le_left (astar * ε) g).trans
    (mul_le_mul_of_nonneg_left (by nlinarith : ε ≤ K * ε) hastar.le)
  have hc₀' : c ≤ c₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hc₁' : c ≤ c₁ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hgeo := (hgeom p hps hpl hph d m hd hm hsize).trans
    (ENNReal.ofReal_le_ofReal (internal_lower_tail_power (δ := δ) hn (min_le_right (astar * ε) g) hc.le
      (min_le_left _ _) hCg.le))
  have hcoarse' := (hcoarse p hps hpl hph (d + m).succPNat m.succPNat
    (by change 2 ≤ m + 1; omega) hsize
    (by simpa only [Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using hsize')
    (by change m + 1 ≤ d + m + 1; omega)).1
  have hfine' := (hfine p hps hpl hph (d + m).succPNat m.succPNat
    (by change 2 ≤ m + 1; omega) hsize
    (by simpa only [Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using hsize')
    (by change m + 1 ≤ d + m + 1; omega)).1
  have hbase := admissible_failure_decomposition p d m hd θ ε A K
  dsimp only at hbase
  rw [hps] at hbase
  apply hbase.trans
  apply (add_le_add (add_le_add hgeo (mul_le_mul' le_rfl hcoarse'))
    (ENNReal.div_le_div_right hfine' _)).trans
  have hlow₀ := internal_lower_tail_power hn (min_le_left (astar * ε) g) hc.le hc₀' hC₀.le
  have hlow₁ := internal_lower_tail_power hn hpδ hc.le hc₁' (show 0 ≤ C₁ * D by positivity)
  have hmarkov : ENNReal.ofReal (C₁ * Real.exp (-c₁ * n ^ (astar * (K * ε)))) /
      ENNReal.ofReal (Real.exp (-n ^ (2 * A * ε))) ≤
      ENNReal.ofReal ((C₁ * D) * Real.exp (-c * n ^ δ)) := by
    rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _)]
    apply ENNReal.ofReal_le_ofReal
    have he : C₁ * Real.exp (-c₁ * n ^ (astar * (K * ε))) /
        Real.exp (-n ^ (2 * A * ε)) =
        C₁ * Real.exp (n ^ (2 * A * ε) - c₁ * n ^ (astar * (K * ε))) := by
      rw [mul_div_assoc, ← Real.exp_sub]; congr 2; ring
    rw [he]
    have hh := mul_le_mul_of_nonneg_left (hDtail (m + 1) (by omega)) hC₁.le
    simp only [one_mul] at hh
    exact hh.trans (by simpa only [mul_assoc] using hlow₁)
  apply (add_le_add (add_le_add le_rfl
    (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hlow₀))) hmarkov).trans_eq
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  dsimp only [n]
  ring

/-- See Subsection 6.1 of the paper: the actual exterior kernel is
normalization of its literal physical energy on the entire positive mass
simplex. The reference is the existing Hausdorff simplex volume, transported
only by the inclusion of its support. -/
theorem physical_endpoint_on_simplex (p : Parameters) (d m : ℕ) (hd : 1 ≤ d)
    (θ : PhysicalCutoff) (ε L : ℝ)
    (y : AffineSimplex.chartDomain d ((d + m : ℕ) + 1))
    (hcompat : (∑ i, y.val i) + L = ((d + m : ℕ) + 1 : ℝ)) :
    let S := AffineSimplex.massSimplex m L
    let μ : Measure S := (AffineSimplex.simplexVolume m L).comap Subtype.val
    let P := fun u : S => ∑ i, (θ.val (((m + 1 : ℕ) : ℝ) ^ (-ε) * u.val i) +
      θ.val (((m + 1 : ℕ) : ℝ) ^ (-ε) * (u.val i)⁻¹))
    let Ky := fun u : S => physicalAmbientGapEnergy p (d + m).succPNat
      ⟨RetainedSimplex.assemble d m (InterpolatingDensities.exteriorPermutation d m) y.val u.val,
        ProperMarginalChart.simplex_ambient _ (InterpolatingDensities.assemble_exterior_mem d m y u.val
          (by
            have hr : ((d + m : ℕ) + 1 : ℝ) - ∑ i, y.val i = L := by linarith
            rw [hr]
            exact u.property))⟩
    Measurable P ∧ Measurable Ky ∧
    ∃ h0 ht,
      let h : m + 1 ≤ d + m + 1 := by omega
      InterpolatingDensities.simplexFibreKernel p d m hd
        (InterpolatingDensities.exteriorPermutation d m) θ
        (Real.rpow_pos_of_pos (show (0 : ℝ) < (m + 1 : ℕ) by positivity) (-ε))
        (Finset.univ.map (Fin.castLEEmb h)) true y =
      (AffineFibre.normalizedMeasure μ
        (fun u => ENNReal.ofReal (Real.exp (-p.val.1 * (P u + Ky u)))) h0 ht).map Subtype.val := by
  have hres : ((d + m : ℕ) + 1 : ℝ) - ∑ i, y.val i = L := by linarith
  subst L
  intro S μ P Ky
  have hS : MeasurableSet S := RetainedSimplex.measurableSet_simplex m _
  have hemb : MeasurableEmbedding (Subtype.val : S → EuclideanSpace ℝ (Fin (m + 1))) :=
    MeasurableEmbedding.subtype_coe hS
  have hvol : μ.map Subtype.val = AffineSimplex.simplexVolume m (((d + m : ℕ) + 1 : ℝ) - ∑ i, y.val i) := by
    rw [map_comap_subtype_coe hS]
    rw [AffineSimplex.simplexVolume_eq_restrict, Measure.restrict_restrict hS, inter_self]
  have ha : 0 < ((m + 1 : ℕ) : ℝ) ^ (-ε) := Real.rpow_pos_of_pos (by positivity) _
  have hP : Measurable P := by
    apply Continuous.measurable
    apply continuous_finsetSum
    intro i _
    have hi : Continuous (fun u : S => u.val i) :=
      (PiLp.continuous_apply 2 (fun _ : Fin (m + 1) => ℝ) i).comp continuous_subtype_val
    exact (θ.property.1.continuousOn.comp_continuous (continuous_const.mul hi)
      (fun u => mul_nonneg ha.le (u.property.1 i).le)).add
      (θ.property.1.continuousOn.comp_continuous
        (continuous_const.mul (hi.inv₀ (fun u => (u.property.1 i).ne')))
        (fun u => mul_nonneg ha.le (inv_nonneg.mpr (u.property.1 i).le)))
  obtain ⟨W, hW, hv, _⟩ := physical_pinned_force_decomposition p (d + m).succPNat
    (by change 2 ≤ d + m + 1; omega)
  have hK : Measurable Ky := by
    have hc : Continuous (fun u : S => W
        (RetainedSimplex.assemble d m (InterpolatingDensities.exteriorPermutation d m) y.val u.val)) :=
      hW.continuousOn.comp_continuous
        ((RetainedSimplex.continuous_assemble d m _ y.val).comp continuous_subtype_val)
        (fun u => ProperMarginalChart.simplex_ambient _
          (InterpolatingDensities.assemble_exterior_mem d m y u.val u.property))
    have he : (fun u : S => W
        (RetainedSimplex.assemble d m (InterpolatingDensities.exteriorPermutation d m) y.val u.val)) = Ky := by
      funext u
      exact hv ⟨_, ProperMarginalChart.simplex_ambient _
        (InterpolatingDensities.assemble_exterior_mem d m y u.val u.property)⟩
    rw [he] at hc
    exact hc.measurable
  refine ⟨hP, hK, ?_⟩
  let h : m + 1 ≤ d + m + 1 := by omega
  let w := fun u => ProperMarginalChart.penalizedDensity p (d + m) θ
    (((m + 1 : ℕ) : ℝ) ^ (-ε)) (Finset.univ.map (Fin.castLEEmb h)) true
    (RetainedSimplex.assemble d m (InterpolatingDensities.exteriorPermutation d m) y.val u)
  have hw : Measurable w := (ProperMarginalChart.measurable_penalizedDensity p (d + m) θ ha _ true).comp
    (RetainedSimplex.continuous_assemble d m _ y.val).measurable
  have hwval : (fun u : S => w u.val) =
      (fun u : S => ENNReal.ofReal (Real.exp (-p.val.1 * (P u + Ky u)))) := by
    funext u
    have hh := InterpolatingDensities.exterior_fibre_weight p d m θ
      (((m + 1 : ℕ) : ℝ) ^ (-ε)) y u.val u.property h
    change w u.val = _ at hh
    calc
      w u.val = ENNReal.ofReal (Real.exp (-p.val.1 * (Ky u + P u))) := hh
      _ = _ := by rw [add_comm (Ky u) (P u)]
  obtain ⟨_, h0, ht, he⟩ := InterpolatingDensities.simplexFibreKernel_density p d m hd
    (InterpolatingDensities.exteriorPermutation d m) θ ha (Finset.univ.map (Fin.castLEEmb h)) true y
  change (∫⁻ u, w u ∂AffineSimplex.simplexVolume m _) ≠ 0 at h0
  change (∫⁻ u, w u ∂AffineSimplex.simplexVolume m _) ≠ ∞ at ht
  have hmass : (∫⁻ u : S, w u.val ∂μ) = ∫⁻ u, w u ∂AffineSimplex.simplexVolume m (((d + m : ℕ) + 1 : ℝ) - ∑ i, y.val i) := by
    rw [← hvol, hemb.lintegral_map]
  have h0' : (∫⁻ u : S, w u.val ∂μ) ≠ 0 := by rw [hmass]; exact h0
  have ht' : (∫⁻ u : S, w u.val ∂μ) ≠ ∞ := by rw [hmass]; exact ht
  have hm := AffineFibre.normalizedMeasure_map μ hemb hw h0' ht'
  rw [hwval] at h0' ht'
  refine ⟨h0', ht', ?_⟩
  simp only [AffineFibre.normalizedMeasure_eq_smul] at he hm ⊢
  rw [hvol] at hm
  rw [hwval] at hm
  exact he.trans hm

namespace Internal

/-- See Subsection 6.1 of the paper: endpoint positive finite partition functions imply
the same for every intermediate physical Gibbs density, including both endpoints. -/
theorem gibbs_interpolation_normalizer {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (P Ky Kz : X → ℝ)
    (hP : Measurable P) (hKy : Measurable Ky) (hKz : Measurable Kz)
    (β : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h00 : (∫⁻ x, ENNReal.ofReal (Real.exp (-β * (P x + Ky x))) ∂μ) ≠ 0)
    (h0t : (∫⁻ x, ENNReal.ofReal (Real.exp (-β * (P x + Ky x))) ∂μ) ≠ ∞)
    (h1t : (∫⁻ x, ENNReal.ofReal (Real.exp (-β * (P x + Kz x))) ∂μ) ≠ ∞) :
    (∫⁻ x, ENNReal.ofReal
      (Real.exp (-β * (P x + (1 - t) * Ky x + t * Kz x))) ∂μ) ≠ 0 ∧
    (∫⁻ x, ENNReal.ofReal
      (Real.exp (-β * (P x + (1 - t) * Ky x + t * Kz x))) ∂μ) ≠ ∞ := by
  let wy := fun x => ENNReal.ofReal (Real.exp (-β * (P x + Ky x)))
  let wz := fun x => ENNReal.ofReal (Real.exp (-β * (P x + Kz x)))
  let wt := fun x => ENNReal.ofReal (Real.exp (-β * (P x + (1 - t) * Ky x + t * Kz x)))
  have hwy : Measurable wy := ((hP.add hKy).const_mul (-β)).exp.ennreal_ofReal
  have hwz : Measurable wz := ((hP.add hKz).const_mul (-β)).exp.ennreal_ofReal
  have hwt : Measurable wt :=
    (((hP.add (hKy.const_mul (1 - t))).add (hKz.const_mul t)).const_mul (-β)).exp.ennreal_ofReal
  have he : wt = fun x => wy x ^ (1 - t) * wz x ^ t := by
    funext x
    dsimp only [wt, wy, wz]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (sub_nonneg.mpr ht1),
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le ht0,
      ← Real.exp_mul, ← Real.exp_mul,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  constructor
  · intro hz
    have hae := (lintegral_eq_zero_iff hwt).mp hz
    have hfalse : ∀ᵐ x ∂μ, False := hae.mono fun x hx =>
      (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)) hx
    have hzero : μ = 0 := by simpa only [ae_iff, not_false_eq_true, ofPred_true, Measure.measure_univ_eq_zero] using hfalse
    apply h00
    rw [hzero, lintegral_zero_measure]
  · have hh := ENNReal.lintegral_mul_norm_pow_le (μ := μ) hwy.aemeasurable hwz.aemeasurable
      (sub_nonneg.mpr ht1) ht0 (show 1 - t + t = 1 by ring)
    change (∫⁻ x, wt x ∂μ) ≠ ∞
    rw [he]
    apply ne_top_of_le_ne_top _ hh
    exact ENNReal.mul_ne_top
      (ENNReal.rpow_lt_top_of_nonneg (sub_nonneg.mpr ht1) h0t).ne
      (ENNReal.rpow_lt_top_of_nonneg ht0 h1t).ne

end Internal

/-- See Subsection 6.1 of the paper: filtered prefixes are literal initial-rank sums. -/
theorem exterior_prefix_filter (d r : ℕ) (hr : r ≤ d)
    (y : EuclideanSpace ℝ (Fin d)) :
    (∑ k : Fin r, y ⟨k.val, by have := k.isLt; omega⟩) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < r), y i := by
  classical
  apply Finset.sum_bij (fun k _ => (⟨k.val, by have := k.isLt; omega⟩ : Fin d))
  · intro k _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, k.isLt⟩
  · intro a _ b _ hab
    exact Fin.ext (congrArg (fun k : Fin d => k.val) hab)
  · intro k hk
    have hkr := (Finset.mem_filter.mp hk).2
    exact ⟨⟨k.val, hkr⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro k _
    rfl

/-- See Subsection 6.1 of the paper: filtered suffixes include all exterior ranks,
with exactly the order used by the physical force estimate. -/
theorem exterior_suffix_filter (d r : ℕ) (hr : r ≤ d)
    (y : EuclideanSpace ℝ (Fin d)) :
    (∑ k : Fin r, y ⟨d - r + k.val, by have := k.isLt; omega⟩) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin d => d - r ≤ i.val), y i := by
  classical
  apply Finset.sum_bij (fun k _ => (⟨d - r + k.val, by have := k.isLt; omega⟩ : Fin d))
  · intro k _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change d - r ≤ d - r + k.val; omega⟩
  · intro a _ b _ hab
    have hh := congrArg (fun k : Fin d => k.val) hab
    apply Fin.ext
    dsimp only at hh
    omega
  · intro k hk
    have hkr := (Finset.mem_filter.mp hk).2
    refine ⟨⟨k.val - (d - r), by have := k.isLt; omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    dsimp only
    omega
  · intro k _
    rfl

/-- See Appendix C in the paper: the physical coarse oscillation at
all active sizes. Its large-size exponent is chosen before ε and β. Its
bounded-size constants are uniform in both volumes and both exteriors. -/
theorem physical_coarse_oscillation (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ A : ℝ, 1 < A ∧ ∀ ε : ℝ, 0 < ε →
      ε < min (1 - min s 1 / 2) (s - min s 1 / 2) / 4 →
      ∃ n₀ : ℕ, ∀ m : ℕ, 1 ≤ m → ∃ B : ℝ, 0 < B ∧
        (n₀ ≤ m + 1 → B ≤ ((m + 1 : ℕ) : ℝ) ^ (A * ε)) ∧
      ∀ d e : ℕ, ∀ _hd : 1 ≤ d, ∀ _he : 1 ≤ e,
        4 * (m + 1) ≤ d + m + 1 → d ≤ e →
        ((m + 1 : ℕ) : ℝ) ^ (2 / s) ≤ ((d + m : ℕ) + 1 : ℝ) →
      ∀ p : Parameters, p.val.2 = s → ∀ L : ℝ,
      ∀ y : AffineSimplex.chartDomain d ((d + m : ℕ) + 1),
      ∀ z : AffineSimplex.chartDomain e ((e + m : ℕ) + 1),
      ∀ hcompatY : (∑ i, y.val i) + L = ((d + m : ℕ) + 1 : ℝ),
      ∀ hcompatZ : (∑ i, z.val i) + L = ((e + m : ℕ) + 1 : ℝ),
      exteriorGeometry s ε d m y.val → exteriorGeometry s ε e m z.val →
      let S := AffineSimplex.massSimplex m L
      let Ky := fun u : S => physicalAmbientGapEnergy p (d + m).succPNat
        ⟨RetainedSimplex.assemble d m (InterpolatingDensities.exteriorPermutation d m) y.val u.val,
          ProperMarginalChart.simplex_ambient _ (InterpolatingDensities.assemble_exterior_mem d m y u.val
            (by
              have hr : ((d + m : ℕ) + 1 : ℝ) - ∑ i, y.val i = L := by linarith
              rw [hr]; exact u.property))⟩
      let Kz := fun u : S => physicalAmbientGapEnergy p (e + m).succPNat
        ⟨RetainedSimplex.assemble e m (InterpolatingDensities.exteriorPermutation e m) z.val u.val,
          ProperMarginalChart.simplex_ambient _ (InterpolatingDensities.assemble_exterior_mem e m z u.val
            (by
              have hr : ((e + m : ℕ) + 1 : ℝ) - ∑ i, z.val i = L := by linarith
              rw [hr]; exact u.property))⟩
      ∀ u v : S,
        WithLp.ofLp u.val ∈ goodBlockEvent s m.succPNat (d + m).succPNat ε →
        WithLp.ofLp v.val ∈ goodBlockEvent s m.succPNat (d + m).succPNat ε →
        |(Ky u - Kz u) - (Ky v - Kz v)| ≤ B := by
  obtain ⟨C, A, hC, hA, hforce⟩ := exterior_force_and_coarse_oscillation s hs hs1
  refine ⟨A, hA, ?_⟩
  intro ε hε hεs
  obtain ⟨n₀, hn₀⟩ := hforce ε hε hεs
  refine ⟨n₀, ?_⟩
  intro m hm
  have hfixed := bounded_size_oscillation s hs hs1 ε hε hεs m hm
  obtain ⟨Bfixed, hBfixed, hfixed⟩ := hfixed
  let B := if n₀ ≤ m + 1 then ((m + 1 : ℕ) : ℝ) ^ (A * ε) else Bfixed
  refine ⟨B, by dsimp only [B]; split <;> positivity,
    (fun hh => by simp only [B, ite_eq_left hh, le_refl]), ?_⟩
  intro d e hd he hsize hde hpower p hps L y z hcompatY hcompatZ hy hz S Ky Kz
  have hmassY : (∑ i, y.val i) + L = (d + m + 1 : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hcompatY
  have hmassZ : (∑ i, z.val i) + L = (e + m + 1 : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hcompatZ
  have hlength : |L - (m + 1 : ℝ)| ≤ (m + 1 : ℝ) ^ (min s 1 / 2 + ε) := by
    have hh := hy.1
    have hr : ((d + m : ℕ) + 1 : ℝ) - ∑ i, y.val i = L := by linarith
    rw [hr] at hh
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  have rank_bounds (b : ℕ) (w : EuclideanSpace ℝ (Fin b))
      (hw : exteriorGeometry s ε b m w) :
      (∀ r : ℕ, (_hr : 0 < r) → (hrb : r ≤ b) →
        |(∑ k : Fin r, w ⟨k.val, by have := k.isLt; omega⟩) - r| ≤
          4 * (m + 1 : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε)) ∧
      (∀ r : ℕ, (_hr : 0 < r) → (hrb : r ≤ b) →
        |(∑ k : Fin r, w ⟨b - r + k.val, by have := k.isLt; omega⟩) - r| ≤
          4 * (m + 1 : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε)) := by
    constructor
    · intro r hr hrb
      rw [exterior_prefix_filter b r hrb w]
      simpa only [Nat.cast_add, Nat.cast_one] using (hw.2 r hr hrb).1
    · intro r hr hrb
      rw [exterior_suffix_filter b r hrb w]
      simpa only [Nat.cast_add, Nat.cast_one] using (hw.2 r hr hrb).2
  obtain ⟨hYR, hYL⟩ := rank_bounds d y.val hy
  obtain ⟨hZR, hZL⟩ := rank_bounds e z.val hz
  have hpow : (m + 1 : ℝ) ^ (2 / s) ≤ (d + m + 1 : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hpower
  have assembleY (u : S) : RetainedSimplex.assemble d m
      (InterpolatingDensities.exteriorPermutation d m) y.val u.val ∈ gapAmbientDomain (d + m).succPNat :=
    ProperMarginalChart.simplex_ambient _ (InterpolatingDensities.assemble_exterior_mem d m y u.val (by
      have hr : ((d + m : ℕ) + 1 : ℝ) - ∑ i, y.val i = L := by linarith
      rw [hr]; exact u.property))
  have assembleZ (u : S) : RetainedSimplex.assemble e m
      (InterpolatingDensities.exteriorPermutation e m) z.val u.val ∈ gapAmbientDomain (e + m).succPNat :=
    ProperMarginalChart.simplex_ambient _ (InterpolatingDensities.assemble_exterior_mem e m z u.val (by
      have hr : ((e + m : ℕ) + 1 : ℝ) - ∑ i, z.val i = L := by linarith
      rw [hr]; exact u.property))
  by_cases hlarge : n₀ ≤ m + 1
  · obtain ⟨WN, WM, _, _, hvN, hvM, hb⟩ := hn₀ m d e hlarge hm hsize hde hpow p hps
    intro u v hu hv
    have hh := (hb L y.val z.val y.property.1 z.property.1 hmassY hmassZ
      hlength hYR hYL hZR hZL u.val u.property.1 u.property.2).2.2 hu v.val hv v.property.2
    dsimp only at hh
    rw [hvN ⟨_, assembleY v⟩, hvM ⟨_, assembleZ v⟩,
      hvN ⟨_, assembleY u⟩, hvM ⟨_, assembleZ u⟩] at hh
    change |(Ky v - Kz v) - (Ky u - Kz u)| ≤ (m + 1 : ℝ) ^ (A * ε) at hh
    rw [abs_sub_comm] at hh
    simpa only [B, ite_eq_left hlarge, Nat.cast_add, Nat.cast_one] using hh
  · obtain ⟨WN, WM, _, _, hvN, hvM, hb⟩ := hfixed d e hsize hde hpow p hps
    intro u v hu hv
    have hh := hb L y.val z.val y.property.1 z.property.1 hmassY hmassZ
      hlength hYR hYL hZR hZL u.val v.val hu hv u.property.2 v.property.2
    dsimp only at hh
    rw [hvN ⟨_, assembleY v⟩, hvM ⟨_, assembleZ v⟩,
      hvN ⟨_, assembleY u⟩, hvM ⟨_, assembleZ u⟩] at hh
    change |(Ky v - Kz v) - (Ky u - Kz u)| ≤ Bfixed at hh
    rw [abs_sub_comm] at hh
    simpa only [B, ite_eq_right hlarge] using hh

/-- Internal bounded-size assembly for Appendix C.
Only a finite sum of size-dependent oscillation constants is used. The tail
power and its coefficient are fixed before the temperature is specialized. -/
theorem internal_all_size_interpolation_tail (a δ βhi c : ℝ)
    (ha : 0 < a) (hδ : 0 < δ) (hδa : δ ≤ 2 * a)
    (hβhi : 0 ≤ βhi) (hc : 0 < c) (hc1 : c ≤ 1 / 2)
    (n₀ : ℕ) (B : ℕ+ → ℝ) (hB : ∀ m, 0 < B m)
    (hlarge : ∀ m : ℕ+, n₀ ≤ (m : ℕ) + 1 → B m ≤ ((m : ℝ) + 1) ^ a) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, 0 ≤ β → β ≤ βhi → ∀ m : ℕ+,
      2 * Real.exp (β * B m - ((m : ℝ) + 1) ^ (2 * a)) ≤
        C * Real.exp (-c * ((m : ℝ) + 1) ^ δ) := by
  obtain ⟨D, hD, htail⟩ := internal_competing_powers ha (by linarith : a < 2 * a) hβhi zero_lt_one
  let S := ∑ i : Fin (n₀ + 1), 2 * Real.exp (βhi * B i.val.succPNat)
  let T : ℝ := (n₀ + 1 : ℕ)
  let Csmall := S * Real.exp (c * T ^ δ)
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => by positivity
  have hCsmall : 0 ≤ Csmall := by dsimp [Csmall]; positivity
  refine ⟨2 * D + Csmall, by positivity, ?_⟩
  intro β hβ hβhi' m
  have hn : 1 ≤ (m : ℝ) + 1 := by
    have : (0 : ℝ) ≤ m := by positivity
    linarith
  have hfirst : β * B m ≤ βhi * B m := mul_le_mul_of_nonneg_right hβhi' (hB m).le
  by_cases hn₀ : n₀ ≤ (m : ℕ) + 1
  · have hB' := hlarge m hn₀
    have he : β * B m ≤ βhi * ((m : ℝ) + 1) ^ a :=
      hfirst.trans (mul_le_mul_of_nonneg_left hB' hβhi)
    have hh := htail ((m : ℕ) + 1) (by omega)
    simp only [one_mul, Nat.cast_add, Nat.cast_one] at hh
    have hlo := internal_lower_tail_power hn hδa hc.le hc1 (show 0 ≤ 2 * D by positivity)
    calc
      _ ≤ 2 * Real.exp (βhi * ((m : ℝ) + 1) ^ a - ((m : ℝ) + 1) ^ (2 * a)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
      _ ≤ 2 * (D * Real.exp (-(1 / 2) * ((m : ℝ) + 1) ^ (2 * a))) :=
        mul_le_mul_of_nonneg_left hh (by norm_num)
      _ ≤ (2 * D) * Real.exp (-c * ((m : ℝ) + 1) ^ δ) := by simpa only [mul_assoc] using hlo
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  · have hsmall : (m : ℕ) + 1 < n₀ := by omega
    let i : Fin (n₀ + 1) := ⟨(m : ℕ) - 1, by omega⟩
    have hi : i.val.succPNat = m := by apply PNat.coe_injective; change (m : ℕ) - 1 + 1 = _; have := m.pos; omega
    have hterm : 2 * Real.exp (βhi * B m) ≤ S := by
      have hh := Finset.single_le_sum (s := Finset.univ)
        (f := fun i : Fin (n₀ + 1) => 2 * Real.exp (βhi * B i.val.succPNat))
        (fun i _ => by positivity) (Finset.mem_univ i)
      rw [hi] at hh
      exact hh
    have hnT : (m : ℝ) + 1 ≤ T := by dsimp [T]; exact_mod_cast (show (m : ℕ) + 1 ≤ n₀ + 1 by omega)
    have hp := Real.rpow_le_rpow (by positivity : 0 ≤ (m : ℝ) + 1) hnT hδ.le
    have hfactor : 1 ≤ Real.exp (c * T ^ δ - c * ((m : ℝ) + 1) ^ δ) :=
      Real.one_le_exp (by nlinarith)
    have hSbound : S ≤ Csmall * Real.exp (-c * ((m : ℝ) + 1) ^ δ) := by
      dsimp only [Csmall]
      rw [mul_assoc, ← Real.exp_add]
      rw [show c * T ^ δ + -c * ((m : ℝ) + 1) ^ δ =
        c * T ^ δ - c * ((m : ℝ) + 1) ^ δ by ring]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hfactor hS
    calc
      _ ≤ 2 * Real.exp (βhi * B m) := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by linarith [Real.rpow_nonneg (show 0 ≤ (m : ℝ) + 1 by positivity) (2 * a)])) (by norm_num)
      _ ≤ S := hterm
      _ ≤ Csmall * Real.exp (-c * ((m : ℝ) + 1) ^ δ) := hSbound
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

namespace Internal

set_option backward.isDefEq.respectTransparency false in
/-- Internal physical specialization of the density transfer in Appendix C. The oscillation premise is confined to this internal
lemma. Both endpoint measures are the physical conditional kernels. -/
theorem physical_interpolant_transfer (p : Parameters) (d e m : ℕ) (hd : 1 ≤ d) (he : 1 ≤ e)
    (θ : PhysicalCutoff) (ε A K L : ℝ)
    (y : AffineSimplex.chartDomain d ((d + m : ℕ) + 1))
    (z : AffineSimplex.chartDomain e ((e + m : ℕ) + 1))
    (hcompatY : (∑ i, y.val i) + L = ((d + m : ℕ) + 1 : ℝ))
    (hcompatZ : (∑ i, z.val i) + L = ((e + m : ℕ) + 1 : ℝ))
    (hy : admissibleExterior p d m hd θ ε A K y)
    (hz : admissibleExterior p e m he θ ε A K z) (B : ℝ) (hB : 0 ≤ B) :
    let S := AffineSimplex.massSimplex m L
    let Ky := fun u : S => physicalAmbientGapEnergy p (d + m).succPNat
      ⟨RetainedSimplex.assemble d m (InterpolatingDensities.exteriorPermutation d m) y.val u.val,
        ProperMarginalChart.simplex_ambient _ (InterpolatingDensities.assemble_exterior_mem d m y u.val
          (by
            have hr : ((d + m : ℕ) + 1 : ℝ) - ∑ i, y.val i = L := by linarith
            rw [hr]; exact u.property))⟩
    let Kz := fun u : S => physicalAmbientGapEnergy p (e + m).succPNat
      ⟨RetainedSimplex.assemble e m (InterpolatingDensities.exteriorPermutation e m) z.val u.val,
        ProperMarginalChart.simplex_ambient _ (InterpolatingDensities.assemble_exterior_mem e m z u.val
          (by
            have hr : ((e + m : ℕ) + 1 : ℝ) - ∑ i, z.val i = L := by linarith
            rw [hr]; exact u.property))⟩
    let μ : Measure S := (AffineSimplex.simplexVolume m L).comap Subtype.val
    let P := fun u : S => ∑ i, (θ.val (((m + 1 : ℕ) : ℝ) ^ (-ε) * u.val i) +
      θ.val (((m + 1 : ℕ) : ℝ) ^ (-ε) * (u.val i)⁻¹))
    (∀ u v : S,
      WithLp.ofLp u.val ∈ goodBlockEvent p.val.2 m.succPNat (d + m).succPNat ε →
      WithLp.ofLp v.val ∈ goodBlockEvent p.val.2 m.succPNat (d + m).succPNat ε →
      |(Ky u - Kz u) - (Ky v - Kz v)| ≤ B) →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ h0 ht,
      let ν := (AffineFibre.normalizedMeasure μ (fun u => ENNReal.ofReal
        (Real.exp (-p.val.1 * (P u + (1 - t) * Ky u + t * Kz u)))) h0 ht).map Subtype.val
      IsProbabilityMeasure ν ∧
      (∫⁻ u in {u : EuclideanSpace ℝ (Fin (m + 1)) |
          WithLp.ofLp u ∉ goodBlockEvent p.val.2 m.succPNat (d + m).succPNat (K * ε)},
        ENNReal.ofReal (exceptionalWeight p.val.2 (n := m.succPNat) (WithLp.ofLp u)) ∂ν) ≤
        ENNReal.ofReal (2 * Real.exp (p.val.1 * B - ((m + 1 : ℕ) : ℝ) ^ (2 * A * ε))) := by
  intro S Ky Kz μ P hOsc t ht0 ht1
  obtain ⟨hP, hKy, h00, h0t, hymeasure⟩ := physical_endpoint_on_simplex p d m hd θ ε L y hcompatY
  obtain ⟨_, hKz, h10, h1t, hzmeasure⟩ := physical_endpoint_on_simplex p e m he θ ε L z hcompatZ
  obtain ⟨hT0, hTt⟩ := gibbs_interpolation_normalizer μ P Ky Kz hP hKy hKz p.val.1 ht0 ht1 h00 h0t h1t
  refine ⟨hT0, hTt, ?_⟩
  let w := fun u : S => ENNReal.ofReal (Real.exp (-p.val.1 * (P u + (1 - t) * Ky u + t * Kz u)))
  have hw : Measurable w := (((hP.add (hKy.const_mul (1 - t))).add
    (hKz.const_mul t)).const_mul (-p.val.1)).exp.ennreal_ofReal
  let ρ := AffineFibre.normalizedMeasure μ w hT0 hTt
  let ν := ρ.map Subtype.val
  let : IsProbabilityMeasure ρ := AffineFibre.isProbabilityMeasure_normalizedMeasure μ hw hT0 hTt
  have hν : IsProbabilityMeasure ν := inferInstance
  refine ⟨hν, ?_⟩
  have hsumpos (b : ℕ) (hb : 1 ≤ b)
      (v : AffineSimplex.chartDomain b ((b + m : ℕ) + 1)) : 0 < ∑ i, v.val i := by
    apply Finset.sum_pos'
    · intro i _; exact (v.property.1 i).le
    · exact ⟨⟨0, by omega⟩, Finset.mem_univ _, v.property.1 _⟩
  have hLN : L < ((d + m : ℕ) + 1 : ℝ) := by linarith [hsumpos d hd y]
  have hLM : L < ((e + m : ℕ) + 1 : ℝ) := by linarith [hsumpos e he z]
  let E := {u : S | WithLp.ofLp u.val ∈ goodBlockEvent p.val.2 m.succPNat (d + m).succPNat ε}
  let F := {u : S | WithLp.ofLp u.val ∉ goodBlockEvent p.val.2 m.succPNat (d + m).succPNat (K * ε)}
  let W := fun u : EuclideanSpace ℝ (Fin (m + 1)) => ENNReal.ofReal
    (exceptionalWeight p.val.2 (n := m.succPNat) (WithLp.ofLp u))
  have hW : Measurable W := (measurable_exceptionalWeight p.val.2 (n := m.succPNat) _
    (fun i => (PiLp.continuous_apply 2 _ i).measurable)).ennreal_ofReal
  have hEvent (b : ℕ) (η : ℝ) : MeasurableSet {u : EuclideanSpace ℝ (Fin (m + 1)) |
      WithLp.ofLp u ∈ goodBlockEvent p.val.2 m.succPNat (b + m).succPNat η} :=
    (measurableSet_goodBlockEvent _ _ _ _).preimage (WithLp.measurable_ofLp 2 _)
  have hE : MeasurableSet E := (hEvent d ε).preimage measurable_subtype_coe
  have hF : MeasurableSet F := (hEvent d (K * ε)).compl.preimage measurable_subtype_coe
  have hperiod (η : ℝ) :
      (Subtype.val ⁻¹' {u : EuclideanSpace ℝ (Fin (m + 1)) |
        WithLp.ofLp u ∈ goodBlockEvent p.val.2 m.succPNat (e + m).succPNat η} : Set S) =
      {u : S | WithLp.ofLp u.val ∈ goodBlockEvent p.val.2 m.succPNat (d + m).succPNat η} := by
    ext u
    change ((∑ i, u.val i) < ((e + m).succPNat : ℝ) ∧ _) ↔
      ((∑ i, u.val i) < ((d + m).succPNat : ℝ) ∧ _)
    rw [u.property.2]
    simp only [show ((e + m).succPNat : ℝ) = ((e + m : ℕ) + 1 : ℝ) by simp [Nat.succPNat],
      show ((d + m).succPNat : ℝ) = ((d + m : ℕ) + 1 : ℝ) by simp [Nat.succPNat],
      hLN, hLM, true_and]
  have hpm := hy.2.1
  have hqm := hz.2.1
  have hfp := hy.2.2
  have hfq := hz.2.2
  rw [hymeasure, Measure.map_apply measurable_subtype_coe (hEvent d ε)] at hpm
  rw [hzmeasure, Measure.map_apply measurable_subtype_coe (hEvent e ε), hperiod ε] at hqm
  change (∫⁻ u in {u : EuclideanSpace ℝ (Fin (m + 1)) |
    WithLp.ofLp u ∈ goodBlockEvent p.val.2 m.succPNat (d + m).succPNat (K * ε)}ᶜ, W u ∂_) ≤ _ at hfp
  change (∫⁻ u in {u : EuclideanSpace ℝ (Fin (m + 1)) |
    WithLp.ofLp u ∈ goodBlockEvent p.val.2 m.succPNat (e + m).succPNat (K * ε)}ᶜ, W u ∂_) ≤ _ at hfq
  rw [hymeasure, setLIntegral_map (hEvent d (K * ε)).compl hW measurable_subtype_coe] at hfp
  rw [hzmeasure, setLIntegral_map (hEvent e (K * ε)).compl hW measurable_subtype_coe,
    preimage_compl, hperiod (K * ε)] at hfq
  have hf : Measurable (F.indicator (fun u : S => W u.val)) :=
    (hW.comp measurable_subtype_coe).indicator hF
  have hfp' := (lintegral_indicator (μ := AffineFibre.normalizedMeasure μ _ h00 h0t)
    hF (fun u : S => W u.val)).trans_le hfp
  have hfq' := (lintegral_indicator (μ := AffineFibre.normalizedMeasure μ _ h10 h1t)
    hF (fun u : S => W u.val)).trans_le hfq
  have hb := gibbs_weighted_transfer_of_oscillation μ P Ky Kz hP hKy hKz p.property.1.le hB
    ht0 ht1 h00 h0t h10 h1t hT0 hTt hE
    (fun u hu v hv => hOsc u v hu hv) hpm hqm hf hfp' hfq'
  change (∫⁻ u in {u : EuclideanSpace ℝ (Fin (m + 1)) |
      WithLp.ofLp u ∈ goodBlockEvent p.val.2 m.succPNat (d + m).succPNat (K * ε)}ᶜ,
      W u ∂ρ.map (Subtype.val : S → EuclideanSpace ℝ (Fin (m + 1)))) ≤ _
  rw [setLIntegral_map (hEvent d (K * ε)).compl hW measurable_subtype_coe]
  apply ((lintegral_indicator (μ := ρ) hF (fun u : S => W u.val)).symm.trans_le hb).trans_eq
  rw [mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num), ← Real.exp_add]
  rfl

end Internal

set_option backward.isDefEq.respectTransparency false in
/-- See Appendix C in the paper, all conclusions. The two physical
endpoint kernels have their literal common-simplex Gibbs interpolation.
Admissibility, weighted exceptional mass, and both individual local laws
have one tail power chosen before the compact temperature interval.
There is no additional analytic or oscillation premise.
Appendix C, proof of Lemma 6.2 of the paper, restricts the
long-range tolerance by `4 * (m + 1) * K * ε ≤ 1`, with the least degree
of Lemma 5.4. The short-range branch only needs `K * ε ≤ 1/4`. -/
theorem local_laws (hRig : External.LongRangeRigidityLocallyUniform)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ A K ε₀ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
      ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ d e m : ℕ, ∀ hd : 1 ≤ d, ∀ he : 1 ≤ e,
        1 ≤ m → 4 * (m + 1) ≤ d + m + 1 → d ≤ e →
        ((m + 1 : ℕ) : ℝ) ^ (2 / s) ≤ ((d + m : ℕ) + 1 : ℝ) →
        let R := ENNReal.ofReal (C * Real.exp (-c * ((m + 1 : ℕ) : ℝ) ^ δ))
        (physicalExteriorLaw p d m θ ε) {y | ¬admissibleExterior p d m hd θ ε A K y} ≤ R ∧
        ∀ L : ℝ,
        ∀ y : AffineSimplex.chartDomain d ((d + m : ℕ) + 1),
        ∀ z : AffineSimplex.chartDomain e ((e + m : ℕ) + 1),
        ∀ hcompatY : (∑ i, y.val i) + L = ((d + m : ℕ) + 1 : ℝ),
        ∀ hcompatZ : (∑ i, z.val i) + L = ((e + m : ℕ) + 1 : ℝ),
        admissibleExterior p d m hd θ ε A K y →
        admissibleExterior p e m he θ ε A K z →
            let S := AffineSimplex.massSimplex m L
            let Ky := fun u : S => physicalAmbientGapEnergy p (d + m).succPNat
              ⟨RetainedSimplex.assemble d m (InterpolatingDensities.exteriorPermutation d m) y.val u.val,
                ProperMarginalChart.simplex_ambient _ (InterpolatingDensities.assemble_exterior_mem d m y u.val
                  (by
                    have hr : ((d + m : ℕ) + 1 : ℝ) - ∑ i, y.val i = L := by linarith
                    rw [hr]; exact u.property))⟩
            let Kz := fun u : S => physicalAmbientGapEnergy p (e + m).succPNat
              ⟨RetainedSimplex.assemble e m (InterpolatingDensities.exteriorPermutation e m) z.val u.val,
                ProperMarginalChart.simplex_ambient _ (InterpolatingDensities.assemble_exterior_mem e m z u.val
                  (by
                    have hr : ((e + m : ℕ) + 1 : ℝ) - ∑ i, z.val i = L := by linarith
                    rw [hr]; exact u.property))⟩
            let μ : Measure S := (AffineSimplex.simplexVolume m L).comap Subtype.val
            let P := fun u : S => ∑ i, (θ.val (((m + 1 : ℕ) : ℝ) ^ (-ε) * u.val i) +
              θ.val (((m + 1 : ℕ) : ℝ) ^ (-ε) * (u.val i)⁻¹))
            ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∃ h0 ht,
              let ν := (AffineFibre.normalizedMeasure μ (fun u => ENNReal.ofReal
                (Real.exp (-p.val.1 * (P u + (1 - t) * Ky u + t * Kz u)))) h0 ht).map Subtype.val
              IsProbabilityMeasure ν ∧
              (∫⁻ u in {u : EuclideanSpace ℝ (Fin (m + 1)) |
                  WithLp.ofLp u ∉ goodBlockEvent s m.succPNat (d + m).succPNat (K * ε)},
                ENNReal.ofReal (exceptionalWeight s (n := m.succPNat) (WithLp.ofLp u)) ∂ν) ≤ R ∧
              (∀ i : Fin (m + 1),
                1 - R ≤ ν {u | ((m + 1 : ℕ) : ℝ) ^ (-(K * ε)) ≤ u i ∧
                  u i ≤ ((m + 1 : ℕ) : ℝ) ^ (K * ε)}) ∧
              ∀ a b : ℕ, a < b → b ≤ m + 1 →
                ν {u | ((m + 1 : ℕ) : ℝ) ^ (K * ε) * (b - a : ℕ) ^ (min s 1 / 2) <
                  |(∑ i ∈ Finset.univ.filter (fun i : Fin (m + 1) => a ≤ i.val ∧ i.val < b), u i) -
                    (b - a : ℕ)|} ≤ R := by
  obtain ⟨A, hA, hosc⟩ := physical_coarse_oscillation s hs hs1
  obtain ⟨K, εbase, hK, hεbase, hmargin, htyp⟩ := admissible_exteriors_typical hRig s hs hs1 A hA
  -- Appendix C, proof of Lemma 6.2: use the degree of Lemma 5.4.
  let εcut : ℝ := if hlong : s < 1 then
    (4 * K * ((paperReferenceCutoffExponent ⟨s, hs, hlong⟩ : ℝ) + 1))⁻¹
    else (4 * K)⁻¹
  have hεcut : 0 < εcut := by
    dsimp only [εcut]
    split <;> positivity
  let ε₀ := min εbase εcut
  refine ⟨A, K, ε₀, hA, hK, lt_min hεbase hεcut, ?_⟩
  intro ε hε hεε
  have hεb : ε < εbase := hεε.trans_le (min_le_left _ _)
  have hεmargin := hεb.trans_le hmargin
  obtain ⟨δtyp, hδtyp, htyp⟩ := htyp ε hε hεb
  obtain ⟨n₀, hosc⟩ := hosc ε hε hεmargin
  choose B hBp hBl hBphys using (fun m : ℕ+ => hosc (m : ℕ) m.pos)
  let δ := min δtyp (A * ε)
  have ha : 0 < A * ε := by positivity
  have hδ : 0 < δ := lt_min hδtyp ha
  refine ⟨δ, hδ, ?_⟩
  intro βlo βhi hlo hle θ
  obtain ⟨Ctyp, ctyp, hCtyp, hctyp, htyp⟩ := htyp βlo βhi hlo hle θ
  let c := min ctyp (1 / 2)
  have hc : 0 < c := lt_min hctyp (by norm_num)
  obtain ⟨Ctail, hCtail, htail⟩ := internal_all_size_interpolation_tail (A * ε) δ βhi c ha hδ
    ((min_le_right δtyp (A * ε)).trans (by linarith)) (by linarith) hc
    (min_le_right _ _) n₀ B hBp (fun m hm => by
      simpa only [Nat.cast_add, Nat.cast_one] using hBl m hm)
  refine ⟨Ctyp + Ctail, c, by positivity, hc, ?_⟩
  intro p hps hpl hph d e m hd he hm hsize hde hpower R
  have hn : (1 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast (show 1 ≤ m + 1 by omega)
  constructor
  · apply (htyp p hps hpl hph d m hd hm hsize hpower).trans
    apply ENNReal.ofReal_le_ofReal
    apply (internal_lower_tail_power hn (min_le_left δtyp (A * ε)) hc.le
      (min_le_left _ _) hCtyp.le).trans
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  · intro L y z hcompatY hcompatZ hy hz S Ky Kz μ P t ht0 ht1
    let mpos : ℕ+ := ⟨m, by omega⟩
    have hgy := hy.1
    have hgz := hz.1
    rw [hps] at hgy hgz
    have hphysical := hBphys mpos d e hd he hsize hde hpower p hps L y z
      hcompatY hcompatZ hgy hgz
    have htransfer := Internal.physical_interpolant_transfer p d e m hd he θ ε A K L y z
      hcompatY hcompatZ hy hz (B mpos) (hBp mpos).le
    obtain ⟨h0, ht, hprob, hbad⟩ := htransfer
      (fun u v hu hv => hphysical u v (by simpa only [hps, mpos, PNat.mk_coe] using hu) (by simpa only [hps, mpos, PNat.mk_coe] using hv)) t ht0 ht1
    refine ⟨h0, ht, hprob, ?_⟩
    let ρ := AffineFibre.normalizedMeasure μ (fun u => ENNReal.ofReal
      (Real.exp (-p.val.1 * (P u + (1 - t) * Ky u + t * Kz u)))) h0 ht
    let ν := ρ.map Subtype.val
    let : IsProbabilityMeasure ν := hprob
    rw [hps] at hbad
    have hnum := htail p.val.1 p.property.1.le hph mpos
    have hnum' : 2 * Real.exp (p.val.1 * B mpos - ((m + 1 : ℕ) : ℝ) ^ (2 * A * ε)) ≤
        (Ctyp + Ctail) * Real.exp (-c * ((m + 1 : ℕ) : ℝ) ^ δ) := by
      have heq : 2 * A * ε = 2 * (A * ε) := by ring
      rw [heq]
      have hnum0 : 2 * Real.exp (p.val.1 * B mpos - ((m + 1 : ℕ) : ℝ) ^ (2 * (A * ε))) ≤
          Ctail * Real.exp (-c * ((m + 1 : ℕ) : ℝ) ^ δ) := by
        simpa only [mpos, PNat.mk_coe, Nat.cast_add, Nat.cast_one] using hnum
      exact hnum0.trans (mul_le_mul_of_nonneg_right (show Ctail ≤ Ctyp + Ctail by linarith) (Real.exp_pos _).le)
    have hbad' := hbad.trans (ENNReal.ofReal_le_ofReal hnum')
    refine ⟨hbad', ?_⟩
    have hnonneg : ∀ᵐ u ∂ν, ∀ i, 0 ≤ u i := by
      apply (MeasurableEmbedding.subtype_coe (RetainedSimplex.measurableSet_simplex m L)).ae_map_iff.mpr
      exact ae_of_all _ (fun u i => (u.property.1 i).le)
    exact Internal.block_events_of_weighted_failure s (K * ε) m.succPNat (d + m).succPNat ν hnonneg hbad'

end Riesz2.InterpolantLocalLaws
