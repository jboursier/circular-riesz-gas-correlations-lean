/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.CompatibleComparisonPart6
public import Riesz2.Thermodynamic.CompatibleComparisonPart7
public import Riesz2.Thermodynamic.FixedLengthDecayLongPart2
public import Riesz2.Thermodynamic.FixedLengthDecayShort

/-!
# Time families and constants for compatible comparison

Composition interfaces for the proof of Proposition 6.6. The time selection retains the
entire original form and any dependent decay property.
-/

public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal ContDiff Topology

namespace Riesz2.CompatibleComparison

/-- See Subsection 6.1 of the paper: increasing the tolerance enlarges the literal
fine event, including its boundary and every ordinary interval. -/
theorem fine_event_mono_internal (s : ℝ) (n N : ℕ+) {η ζ : ℝ}
    (hηζ : η ≤ ζ) : goodBlockEvent s n N η ⊆ goodBlockEvent s n N ζ := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hup := Real.rpow_le_rpow_of_exponent_le hn hηζ
  have hlo := Real.rpow_le_rpow_of_exponent_le hn (neg_le_neg hηζ)
  intro x hx
  refine ⟨hx.1, fun i => ⟨hlo.trans (hx.2.1 i).1, (hx.2.1 i).2.trans hup⟩, ?_⟩
  intro a b hab hbn
  exact (hx.2.2 a b hab hbn).trans
    (mul_le_mul_of_nonneg_right hup (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- See Subsection 6.1 and the proof of Proposition 6.6 of the paper: a larger endpoint
tail exponent and a smaller fine-event parameter imply the original
admissibility predicate. The conditional law and coarse event stay literal. -/
theorem admissible_exterior_mono_internal (p : Parameters) (d a : ℕ) (hd : 1 ≤ d)
    (θ : PhysicalCutoff) (ε : ℝ) (hε : 0 ≤ ε)
    {A A' K K' : ℝ} (hA : A ≤ A') (hK : K' ≤ K)
    (y : AffineSimplex.chartDomain d ((d+a : ℕ)+1))
    (hy : InterpolantLocalLaws.admissibleExterior p d a hd θ ε A' K' y) :
    InterpolantLocalLaws.admissibleExterior p d a hd θ ε A K y := by
  refine ⟨hy.1, hy.2.1, ?_⟩
  apply le_trans (lintegral_mono_set ?_) (hy.2.2.trans ?_)
  · intro u hu
    exact fun h => hu (fine_event_mono_internal p.val.2 a.succPNat (d+a).succPNat
      (mul_le_mul_of_nonneg_right hK hε) h)
  · apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (show 1 ≤ a+1 by omega))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA (by norm_num)) hε)

section Physical

variable (p : Parameters) (a d e : ℕ) (ha : 1 ≤ a)
    (θ : PhysicalCutoff) (ε L : ℝ) (hL : 0 < L)
    (y : AffineSimplex.chartDomain (d+1) ((d+1+a : ℕ)+1))
    (z : AffineSimplex.chartDomain (e+1) ((e+1+a : ℕ)+1))
    (hyL : ((d+1+a : ℕ)+1 : ℝ)-∑ i, y.val i = L)
    (hzL : ((e+1+a : ℕ)+1 : ℝ)-∑ i, z.val i = L)
    (Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ)
    (hKy : ∀ u (hu : RetainedSimplex.assemble (d+1) a
      (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u ∈
        gapAmbientDomain (d+1+a).succPNat),
      Ky u = physicalAmbientGapEnergy p (d+1+a).succPNat
        ⟨RetainedSimplex.assemble (d+1) a
          (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u,hu⟩)
    (hKz : ∀ u (hu : RetainedSimplex.assemble (e+1) a
      (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u ∈
        gapAmbientDomain (e+1+a).succPNat),
      Kz u = physicalAmbientGapEnergy p (e+1+a).succPNat
        ⟨RetainedSimplex.assemble (e+1) a
          (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u,hu⟩)

include ha hL hyL hzL hKy hKz in
/-- See Subsection 6.1 and the proof of Proposition 6.6 of the paper: choose a whole
time family of the original physical certificates and retain any property
of their full dependent forms (in particular the two decay bounds). The
chart laws are probability measures for every real time, using the physical
path composed with the projection onto `[0,1]`. Only times in that interval
are used in the conclusion about the specified potential and property. -/
theorem physical_certificate_time_family_internal (N : ℝ) (hLN : L < N)
    (frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a)) :
    let H := fun (t : ℝ) (u : EuclideanSpace ℝ (Fin (a+1))) => p.val.1*
      ((∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u i)+θ.val ((a+1 : ℝ)^(-ε)*(u i)⁻¹)))+
        (1-t)*Ky u+t*Kz u)
    let U := frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
    let g := fun x => AffineSimplex.centredChart a L (frame.symm x)
    let j := InterpolationTransport.orthonormalInclusion a L N hLN frame
    let σ : Measure (AffineSimplex.massSimplex a L) :=
    (AffineSimplex.simplexVolume a L).comap Subtype.val
    let w := fun t (u : AffineSimplex.massSimplex a L) => ENNReal.ofReal (Real.exp (-H t u.val))
    ∀ P : (t : ℝ) → (ν : Measure (AffineSimplex.chartDomain (a+1) N)) →
      ScalarFormData ν → Prop,
    (∀ t ∈ Icc (0 : ℝ) 1, ∃ (h0 : (∫⁻ u, w t u ∂σ) ≠ 0)
      (htop : (∫⁻ u, w t u ∂σ) ≠ ⊤),
      let ν := (AffineFibre.normalizedMeasure σ (w t) h0 htop).map
        (InterpolationTransport.inclusion a L N hLN)
      ∃ Q : ScalarFormData ν, IsClosedScalarDirichletForm Q ∧
        InterpolationCoefficientBounds.IsIntrinsicFibreForm a L N hLN frame ν Q ∧ P t ν Q) →
    ∃ μ : ℝ → Measure (EuclideanSpace ℝ (Fin a)),
      (∀ t, IsProbabilityMeasure (μ t)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, IsEuclideanGibbsPotential volume (μ t) U (H t ∘ g)) ∧
      let ν := fun t => ((μ t).comap (Subtype.val : U → _)).map j
      ∃ Q : (t : ℝ) → ScalarFormData (ν t),
        (∀ t, IsProbabilityMeasure (ν t)) ∧
        (∀ t, IsClosedScalarDirichletForm (Q t)) ∧
        (∀ t, InterpolationCoefficientBounds.IsIntrinsicFibreForm a L N hLN frame (ν t) (Q t)) ∧
        ∀ t ∈ Icc (0 : ℝ) 1, P t (ν t) (Q t) := by
  intro H U g j σ w P hP
  have hKys := physical_realization_smooth_internal p a d y Ky hKy
  have hKzs := physical_realization_smooth_internal p a e z Kz hKz
  obtain ⟨_, _, hchart⟩ := physical_chart_wellposed_internal p a d e ha θ ε L hL
    y z hyL hzL Ky Kz hKy hKz
  have hex (t : Icc (0 : ℝ) 1) :
      ∃ μ : Measure (EuclideanSpace ℝ (Fin a)),
        IsEuclideanGibbsPotential volume μ U (H t.val ∘ g) ∧
        ∃ Q : ScalarFormData ((μ.comap (Subtype.val : U → _)).map j),
          IsClosedScalarDirichletForm Q ∧
          InterpolationCoefficientBounds.IsIntrinsicFibreForm a L N hLN frame
            ((μ.comap (Subtype.val : U → _)).map j) Q ∧
          P t.val ((μ.comap (Subtype.val : U → _)).map j) Q := by
    obtain ⟨μ, hV, _⟩ := hchart t.val t.property frame
    refine ⟨μ, hV, ?_⟩
    obtain ⟨h0, htop, Q, hc, hi, hp⟩ := hP t.val t.property
    obtain ⟨h0', htop', hlaw⟩ := physical_normalized_chart_internal p a d e θ ε L
      y z hyL hzL Ky Kz hKys hKzs t.val N hLN frame μ hV
    rw [hlaw]
    exact ⟨Q, hc, hi, hp⟩
  choose μ₀ hV₀ Q₀ hc₀ hi₀ hp₀ using hex
  let clip : ℝ → Icc (0 : ℝ) 1 := fun t =>
    ⟨max 0 (min 1 t), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hclip (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (clip t).val = t := by
    simp only [clip, min_eq_right ht.2, max_eq_right ht.1]
  refine ⟨fun t => μ₀ (clip t), fun t => IntrinsicScalarCore.probability (hV₀ _),
    fun t ht => ?_, fun t => Q₀ (clip t), ?_, fun t => hc₀ _, fun t => hi₀ _, ?_⟩
  · simpa only [hclip t ht] using hV₀ (clip t)
  · intro t
    have hV := hV₀ (clip t)
    have := IntrinsicScalarCore.probability hV
    have hlaw := (InterpolationTransport.orthonormal_law a L N hLN frame
      (μ₀ (clip t)) (H (clip t).val ∘ g) hV).1
    have : IsProbabilityMeasure
        (((μ₀ (clip t)).comap (Subtype.val : U → _)).map Subtype.val) := by
      rw [hlaw]; infer_instance
    have : IsProbabilityMeasure ((μ₀ (clip t)).comap (Subtype.val : U → _)) :=
      Measure.isProbabilityMeasure_of_map measurable_subtype_coe.aemeasurable
    infer_instance
  · intro t ht
    simpa only [hclip t ht] using hp₀ (clip t)

end Physical

/-- See the proof of Proposition 6.6 in the paper: the loss appearing in the
fine-force absorption has an upper bound fixed before the tolerance.
 -/
theorem fine_force_loss_uniform_internal (s K : ℝ) (hs : 0 < s) (hK : 0 ≤ K) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, ε ≤ 1/4 →
      1/(1-(min s 1/2+ε))+K*(s+1)+2 ≤ κ := by
  refine ⟨K*(s+1)+6, by positivity, ?_⟩
  intro ε hε
  have hm := min_le_right s 1
  have hden : 0 < 1-(min s 1/2+ε) := by linarith
  have hi : 1/(1-(min s 1/2+ε)) ≤ (4 : ℝ) :=
    (div_le_iff₀ hden).mpr (by linarith)
  linarith

section Hessian

variable (p : Parameters) (a d e : ℕ) (θ : PhysicalCutoff) (ε L : ℝ)
    (y : AffineSimplex.chartDomain (d+1) ((d+1+a : ℕ)+1))
    (z : AffineSimplex.chartDomain (e+1) ((e+1+a : ℕ)+1))
    (hyL : ((d+1+a : ℕ)+1 : ℝ)-∑ i,y.val i = L)
    (hzL : ((e+1+a : ℕ)+1 : ℝ)-∑ i,z.val i = L)
    (Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ)
    (hKys : ContDiffOn ℝ ∞ Ky (RetainedSimplex.assemble (d+1) a
      (InterpolatingDensities.exteriorPermutation (d+1) a) y.val ⁻¹'
        gapAmbientDomain (d+1+a).succPNat))
    (hKzs : ContDiffOn ℝ ∞ Kz (RetainedSimplex.assemble (e+1) a
      (InterpolatingDensities.exteriorPermutation (e+1) a) z.val ⁻¹'
        gapAmbientDomain (e+1+a).succPNat))

include hyL hzL hKys hKzs in
/-- See Subsection 6.1 and the proof of Proposition 6.6 of the paper: the short-range
decay theorem's scaled Hessian is the Hessian of the literal scaled
potential, at every physical fibre point. No global smooth extension is
assumed outside the physical domains. -/
theorem physical_interpolant_hessian_scale_internal (t : ℝ) :
    let H := fun u : EuclideanSpace ℝ (Fin (a+1)) =>
      (∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u i)+θ.val ((a+1 : ℝ)^(-ε)*(u i)⁻¹)))+
        (1-t)*Ky u+t*Kz u
    ∀ u ∈ AffineSimplex.massSimplex a L,
      hessianMatrix (fun v => p.val.1*H v) u = p.val.1 • hessianMatrix H u := by
  intro H u hu
  have hs := physical_interpolant_smooth_internal p a d e θ ε L y z hyL hzL
    Ky Kz hKys hKzs t u hu
  change ContDiffAt ℝ ∞ (fun v => p.val.1*H v) u at hs
  have hβ : p.val.1 ≠ 0 := p.property.1.ne'
  have he : H = fun v => p.val.1⁻¹*(p.val.1*H v) := by
    funext v
    rw [← mul_assoc, inv_mul_cancel₀ hβ, one_mul]
  have hs₀ : ContDiffAt ℝ ∞ H u := by
    rw [he]
    exact contDiffAt_const.mul hs
  ext i j
  rw [Intrinsic.hessianMatrix_eq_second hs,
    PhysicalCollision.internal_hessian_const_mul (hs₀.of_le (by simp)),
    ← Intrinsic.hessianMatrix_eq_second hs₀]
  rfl

end Hessian

/-- See Lemma 6.4 and the proof of Proposition 6.6 of the paper: the long-range decay theorem on a single real-time family of the actual chart
laws and original intrinsic certificates. Both point-source decay bounds and unique solvability are conclusions. -/
theorem long_range_decay_time_family_internal (hzeta : External.PeriodicZeta)
    (hRig : External.LongRangeRigidityLocallyUniform) (s : Riesz1.RieszExponent) :
    ∃ A K ε₀ κ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧ 0 < κ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    ∀ (a d e : ℕ) (_ha : 1 ≤ a), d ≤ e →
      4*(a+1) ≤ (a+1+d)+1 →
      (a+1 : ℝ)^(2/s.val) ≤ ((a+1+d : ℕ)+1 : ℝ) →
    ∀ (y : AffineSimplex.chartDomain (d+1) ((d+1+a : ℕ)+1))
      (z : AffineSimplex.chartDomain (e+1) ((e+1+a : ℕ)+1)) (L : ℝ),
      ((d+1+a : ℕ)+1 : ℝ)-∑ i, y.val i = L →
      ((e+1+a : ℕ)+1 : ℝ)-∑ i, z.val i = L →
      InterpolantLocalLaws.admissibleExterior (ofLong β s) (d+1) a (by omega) θ ε A K y →
      InterpolantLocalLaws.admissibleExterior (ofLong β s) (e+1) a (by omega) θ ε A K z →
    let N : ℝ := ((a+1+d : ℕ)+1 : ℝ)
    ∃ Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ,
      (∀ u (hu : RetainedSimplex.assemble (d+1) a
        (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u ∈
          gapAmbientDomain (d+1+a).succPNat),
        Ky u = physicalAmbientGapEnergy (ofLong β s) (d+1+a).succPNat
          ⟨RetainedSimplex.assemble (d+1) a
            (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u,hu⟩) ∧
      (∀ u (hu : RetainedSimplex.assemble (e+1) a
        (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u ∈
          gapAmbientDomain (e+1+a).succPNat),
        Kz u = physicalAmbientGapEnergy (ofLong β s) (e+1+a).succPNat
          ⟨RetainedSimplex.assemble (e+1) a
            (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u,hu⟩) ∧
    ∃ hLN : L < N,
    ∀ frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a),
    let H := fun (t : ℝ) (u : EuclideanSpace ℝ (Fin (a+1))) => β.val*
      ((∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u i)+θ.val ((a+1 : ℝ)^(-ε)*(u i)⁻¹)))+
        (1-t)*Ky u+t*Kz u)
    let U := frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
    let g := fun x => AffineSimplex.centredChart a L (frame.symm x)
    let j := InterpolationTransport.orthonormalInclusion a L N hLN frame
    ∃ μ : ℝ → Measure (EuclideanSpace ℝ (Fin a)),
      (∀ t, IsProbabilityMeasure (μ t)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, IsEuclideanGibbsPotential volume (μ t) U (H t ∘ g)) ∧
    let ν := fun t => ((μ t).comap (Subtype.val : U → _)).map j
    ∃ Q : (t : ℝ) → ScalarFormData (ν t),
      (∀ t, IsProbabilityMeasure (ν t)) ∧
      (∀ t, IsClosedScalarDirichletForm (Q t)) ∧
      (∀ t, InterpolationCoefficientBounds.IsIntrinsicFibreForm a L N hLN frame (ν t) (Q t)) ∧
    ∀ t ∈ Icc (0 : ℝ) 1,
      (∀ (i : Fin (a+1)) (χ : Lp ℝ 2 (ν t)), ∃! ψ : Fin (a+1) → (Q t).1,
        WeightedWeakSolution (Q t) (fun x => hessianMatrix (H t) x.val)
          (zeroSumComponents (Fin (a+1))) (fun l => if l = i then χ else 0) ψ) ∧
      ∀ i : Fin (a+1), |(i.val : ℝ)+1-(a+1 : ℝ)/2| ≤ (a+1 : ℝ)/4 →
      ∀ χ : BoundedL2Pairings.boundedSubmodule (ν t), ∀ ψ : Fin (a+1) → (Q t).1,
        WeightedWeakSolution (Q t) (fun x => hessianMatrix (H t) x.val)
          (zeroSumComponents (Fin (a+1))) (fun l => if l = i then χ.val else 0) ψ →
        (∑ l, InteractionDifferential.boundaryWeight s.val a.succPNat l*‖(ψ l).val‖) ≤
          C*(a+1 : ℝ)^(κ*ε-s.val/2)*
            (‖χ.val‖+Real.exp (-c*(a+1 : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ (ν t)).toReal) ∧
        (∑ l, ‖(ψ l).val‖) ≤ C*(a+1 : ℝ)^(κ*ε)*
            (‖χ.val‖+Real.exp (-c*(a+1 : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ (ν t)).toReal) := by
  obtain ⟨A,K,ε₀,κ,hA,hK,hε₀,hκ,hdec⟩ :=
    FixedLengthDecay.long_range_fixed_length_decay hzeta hRig s
  refine ⟨A,K,ε₀,κ,hA,hK,hε₀,hκ,?_⟩
  intro ε hε hsmall
  obtain ⟨δ,hδ,hdec⟩ := hdec ε hε hsmall
  refine ⟨δ,hδ,?_⟩
  intro βlo βhi hlo hle θ
  obtain ⟨C,c,hC,hc,hdec⟩ := hdec βlo βhi hlo hle θ
  refine ⟨C,c,hC,hc,?_⟩
  intro β hβ a d e ha hde hsize hpower y z L hyL hzL hy hz N
  obtain ⟨Ky,Kz,_hKys,_hKzs,hKy,hKz,hdec⟩ :=
    hdec β hβ a d e ha hde hsize (by simpa only [Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using hpower) y z L hyL hzL hy hz
  have hL : 0 < L := by linarith only [y.property.2,hyL]
  have hLN : L < N := by
    have h := InterpolationTransport.compatible_mass_lt a (d+1) (by omega) L y (by linarith only [hyL])
    dsimp only [N]
    simp only [Nat.cast_add,Nat.cast_one] at h ⊢
    linarith only [h]
  refine ⟨Ky,Kz,hKy,hKz,hLN,?_⟩
  intro frame H U g j
  let P := (fun (t : ℝ) (ν : Measure (AffineSimplex.chartDomain (a+1) N))
      (Q : ScalarFormData ν) =>
      (∀ (i : Fin (a+1)) (χ : Lp ℝ 2 ν), ∃! ψ : Fin (a+1) → Q.1,
        WeightedWeakSolution Q (fun x => hessianMatrix (H t) x.val)
          (zeroSumComponents (Fin (a+1))) (fun l => if l = i then χ else 0) ψ) ∧
      ∀ i : Fin (a+1), |(i.val : ℝ)+1-(a+1 : ℝ)/2| ≤ (a+1 : ℝ)/4 →
      ∀ χ : BoundedL2Pairings.boundedSubmodule ν, ∀ ψ : Fin (a+1) → Q.1,
        WeightedWeakSolution Q (fun x => hessianMatrix (H t) x.val)
          (zeroSumComponents (Fin (a+1))) (fun l => if l = i then χ.val else 0) ψ →
        (∑ l, InteractionDifferential.boundaryWeight s.val a.succPNat l*‖(ψ l).val‖) ≤
          C*(a+1 : ℝ)^(κ*ε-s.val/2)*
            (‖χ.val‖+Real.exp (-c*(a+1 : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ ν).toReal) ∧
        (∑ l, ‖(ψ l).val‖) ≤ C*(a+1 : ℝ)^(κ*ε)*
            (‖χ.val‖+Real.exp (-c*(a+1 : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ ν).toReal))
  refine physical_certificate_time_family_internal (ofLong β s) a d e ha θ ε L hL
    y z hyL hzL Ky Kz hKy hKz N hLN frame
    P ?_
  intro t ht
  obtain ⟨h0,htop,hLN',_hprob,hforms⟩ := hdec t ht
  obtain ⟨Q,hclosed,_hcons,hintr,hsol,hbound⟩ := hforms frame
  let σ : Measure (AffineSimplex.massSimplex a L) :=
    (AffineSimplex.simplexVolume a L).comap Subtype.val
  let w₀ := fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal
    (Real.exp (-β.val*((∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u.val i)+
      θ.val ((a+1 : ℝ)^(-ε)*(u.val i)⁻¹)))+(1-t)*Ky u.val+t*Kz u.val)))
  let w₁ := fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal (Real.exp (-H t u.val))
  have hw : w₁ = w₀ := by funext u; simp only [w₁,w₀,H,neg_mul]
  have h01 : (∫⁻ u,w₁ u ∂σ) ≠ 0 := by rw [hw]; exact h0
  have ht1 : (∫⁻ u,w₁ u ∂σ) ≠ ⊤ := by rw [hw]; exact htop
  refine ⟨h01,ht1,?_⟩
  have he : AffineFibre.normalizedMeasure σ w₁ h01 ht1 =
      AffineFibre.normalizedMeasure σ w₀ h0 htop := by congr 1
  have heν := congrArg (Measure.map (InterpolationTransport.inclusion a L N hLN)) he
  let R := fun ν : Measure (AffineSimplex.chartDomain (a+1) N) =>
    ∃ Q : ScalarFormData ν, IsClosedScalarDirichletForm Q ∧
      InterpolationCoefficientBounds.IsIntrinsicFibreForm a L N hLN frame ν Q ∧ P t ν Q
  have hf : R ((AffineFibre.normalizedMeasure σ w₀ h0 htop).map
      (InterpolationTransport.inclusion a L N hLN)) := by
    refine ⟨Q,hclosed,hintr,?_⟩
    simpa only [P,H,Nat.succPNat_coe,Nat.cast_succ,Nat.cast_add,Nat.cast_one] using And.intro hsol hbound
  exact (congrArg R heν).mpr hf

/-- See Lemma 6.4 and the proof of Proposition 6.6 of the paper: the short-range decay theorem on a single real-time family of the actual chart
laws and original intrinsic certificates. Both point-source decay bounds and unique solvability are conclusions. -/
theorem short_range_decay_time_family_internal (hRig : External.LongRangeRigidityLocallyUniform) (s : ShortExponent) :
    ∃ A K ε₀ κ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧ 0 < κ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    ∀ (a d e : ℕ) (_ha : 1 ≤ a), d ≤ e →
      4*(a+1) ≤ (d+1+a)+1 →
      (a+1 : ℝ)^(2/s.val) ≤ ((d+1+a : ℕ)+1 : ℝ) →
    ∀ (y : AffineSimplex.chartDomain (d+1) ((d+1+a : ℕ)+1))
      (z : AffineSimplex.chartDomain (e+1) ((e+1+a : ℕ)+1)) (L : ℝ),
      ((d+1+a : ℕ)+1 : ℝ)-∑ i, y.val i = L →
      ((e+1+a : ℕ)+1 : ℝ)-∑ i, z.val i = L →
      InterpolantLocalLaws.admissibleExterior (ofShort β s) (d+1) a (by omega) θ ε A K y →
      InterpolantLocalLaws.admissibleExterior (ofShort β s) (e+1) a (by omega) θ ε A K z →
    let N : ℝ := ((d+1+a : ℕ)+1 : ℝ)
    ∃ Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ,
      (∀ u (hu : RetainedSimplex.assemble (d+1) a
        (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u ∈
          gapAmbientDomain (d+1+a).succPNat),
        Ky u = physicalAmbientGapEnergy (ofShort β s) (d+1+a).succPNat
          ⟨RetainedSimplex.assemble (d+1) a
            (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u,hu⟩) ∧
      (∀ u (hu : RetainedSimplex.assemble (e+1) a
        (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u ∈
          gapAmbientDomain (e+1+a).succPNat),
        Kz u = physicalAmbientGapEnergy (ofShort β s) (e+1+a).succPNat
          ⟨RetainedSimplex.assemble (e+1) a
            (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u,hu⟩) ∧
    ∃ hLN : L < N,
    ∀ frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a),
    let H := fun (t : ℝ) (u : EuclideanSpace ℝ (Fin (a+1))) =>
      ((∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u i)+θ.val ((a+1 : ℝ)^(-ε)*(u i)⁻¹)))+
        (1-t)*Ky u+t*Kz u)
    let U := frame '' (AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L)
    let g := fun x => AffineSimplex.centredChart a L (frame.symm x)
    let j := InterpolationTransport.orthonormalInclusion a L N hLN frame
    ∃ μ : ℝ → Measure (EuclideanSpace ℝ (Fin a)),
      (∀ t, IsProbabilityMeasure (μ t)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, IsEuclideanGibbsPotential volume (μ t) U (fun x => β.val*H t (g x))) ∧
    let ν := fun t => ((μ t).comap (Subtype.val : U → _)).map j
    ∃ Q : (t : ℝ) → ScalarFormData (ν t),
      (∀ t, IsProbabilityMeasure (ν t)) ∧
      (∀ t, IsClosedScalarDirichletForm (Q t)) ∧
      (∀ t, InterpolationCoefficientBounds.IsIntrinsicFibreForm a L N hLN frame (ν t) (Q t)) ∧
    ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ i : Fin (a+1), |(i.val : ℝ)+1-(a+1 : ℝ)/2| ≤ (a+1 : ℝ)/4 →
      ∀ χ : BoundedL2Pairings.boundedSubmodule (ν t),
      (∃! ψ : Fin (a+1) → (Q t).1, WeightedWeakSolution (Q t)
        (fun x => hessianMatrix (fun v => β.val*H t v) x.val) (zeroSumComponents (Fin (a+1)))
        (fun l => if l = i then χ.val else 0) ψ) ∧
      ∀ ψ : Fin (a+1) → (Q t).1,
        WeightedWeakSolution (Q t) (fun x => hessianMatrix (fun v => β.val*H t v) x.val)
          (zeroSumComponents (Fin (a+1))) (fun l => if l = i then χ.val else 0) ψ →
        (∑ l, InteractionDifferential.boundaryWeight s.val a.succPNat l*‖(ψ l).val‖) ≤
          C*(a+1 : ℝ)^(κ*ε-1/2)*
            (‖χ.val‖+Real.exp (-c*(a+1 : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ (ν t)).toReal) ∧
        (∑ l, ‖(ψ l).val‖) ≤ C*(a+1 : ℝ)^(κ*ε)*
            (‖χ.val‖+Real.exp (-c*(a+1 : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ (ν t)).toReal) := by
  obtain ⟨A,K,ε₀,κ,hA,hK,hε₀,hκ,hdec⟩ :=
    FixedLengthDecay.short_fixed_length_decay hRig s
  refine ⟨A,K,ε₀,κ,hA,hK,hε₀,hκ,?_⟩
  intro ε hε hsmall
  obtain ⟨δ,hδ,hdec⟩ := hdec ε hε hsmall
  refine ⟨δ,hδ,?_⟩
  intro βlo βhi hlo hle θ
  obtain ⟨C,c,hC,hc,hdec⟩ := hdec βlo βhi hlo hle θ
  refine ⟨C,c,hC,hc,?_⟩
  intro β hβ a d e ha hde hsize hpower y z L hyL hzL hy hz N
  obtain ⟨Ky,Kz,_hKys,_hKzs,hKy,hKz,hdec⟩ :=
    hdec β hβ a (d+1) (e+1) ha (by omega) (by omega) (by omega) hsize
      (by simpa only [Nat.cast_add,Nat.cast_one] using hpower) y z L hyL hzL hy hz
  have hL : 0 < L := by linarith only [y.property.2,hyL]
  have hLN : L < N := by
    have h := InterpolationTransport.compatible_mass_lt a (d+1) (by omega) L y (by linarith only [hyL])
    dsimp only [N]
    simp only [Nat.cast_add,Nat.cast_one] at h ⊢
    linarith only [h]
  refine ⟨Ky,Kz,hKy,hKz,hLN,?_⟩
  intro frame H U g j
  let P := (fun (t : ℝ) (ν : Measure (AffineSimplex.chartDomain (a+1) N))
      (Q : ScalarFormData ν) =>
      ∀ i : Fin (a+1), |(i.val : ℝ)+1-(a+1 : ℝ)/2| ≤ (a+1 : ℝ)/4 →
      ∀ χ : BoundedL2Pairings.boundedSubmodule ν,
      (∃! ψ : Fin (a+1) → Q.1, WeightedWeakSolution Q
        (fun x => hessianMatrix (fun v => β.val*H t v) x.val) (zeroSumComponents (Fin (a+1)))
        (fun l => if l = i then χ.val else 0) ψ) ∧
      ∀ ψ : Fin (a+1) → Q.1,
        WeightedWeakSolution Q (fun x => hessianMatrix (fun v => β.val*H t v) x.val)
          (zeroSumComponents (Fin (a+1))) (fun l => if l = i then χ.val else 0) ψ →
        (∑ l, InteractionDifferential.boundaryWeight s.val a.succPNat l*‖(ψ l).val‖) ≤
          C*(a+1 : ℝ)^(κ*ε-1/2)*
            (‖χ.val‖+Real.exp (-c*(a+1 : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ ν).toReal) ∧
        (∑ l, ‖(ψ l).val‖) ≤ C*(a+1 : ℝ)^(κ*ε)*
            (‖χ.val‖+Real.exp (-c*(a+1 : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ ν).toReal))
  refine physical_certificate_time_family_internal (ofShort β s) a d e ha θ ε L hL
    y z hyL hzL Ky Kz hKy hKz N hLN frame
    P ?_
  intro t ht
  obtain ⟨h0,htop,_hprob,hforms⟩ := hdec t ht
  obtain ⟨Q,hclosed,_hcons,hintr,hbound⟩ := hforms frame
  let σ : Measure (AffineSimplex.massSimplex a L) :=
    (AffineSimplex.simplexVolume a L).comap Subtype.val
  let w₀ := fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal
    (Real.exp (-β.val*((∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u.val i)+
      θ.val ((a+1 : ℝ)^(-ε)*(u.val i)⁻¹)))+(1-t)*Ky u.val+t*Kz u.val)))
  let w₁ := fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal (Real.exp (-(β.val*H t u.val)))
  have hw : w₁ = w₀ := by funext u; simp only [w₁,w₀,H,neg_mul]
  have h01 : (∫⁻ u,w₁ u ∂σ) ≠ 0 := by rw [hw]; exact h0
  have ht1 : (∫⁻ u,w₁ u ∂σ) ≠ ⊤ := by rw [hw]; exact htop
  refine ⟨h01,ht1,?_⟩
  have he : AffineFibre.normalizedMeasure σ w₁ h01 ht1 =
      AffineFibre.normalizedMeasure σ w₀ h0 htop := by congr 1
  have heν := congrArg (Measure.map (InterpolationTransport.inclusion a L N hLN)) he
  let R := fun ν : Measure (AffineSimplex.chartDomain (a+1) N) =>
    ∃ Q : ScalarFormData ν, IsClosedScalarDirichletForm Q ∧
      InterpolationCoefficientBounds.IsIntrinsicFibreForm a L N hLN frame ν Q ∧ P t ν Q
  have hf : R ((AffineFibre.normalizedMeasure σ w₀ h0 htop).map
      (InterpolationTransport.inclusion a L N hLN)) := by
    refine ⟨Q,hclosed,hintr,?_⟩
    let ν := (AffineFibre.normalizedMeasure σ w₀ h0 htop).map
      (InterpolationTransport.inclusion a L N hLN)
    have hscale : (fun x : AffineSimplex.chartDomain (a+1) N =>
        hessianMatrix (fun v => β.val*H t v) x.val) =ᵐ[ν]
        (fun x => β.val • hessianMatrix (H t) x.val) := by
      apply (InterpolationTransport.measurableEmbedding_inclusion a L N hLN).ae_map_iff.mpr
      exact ae_of_all _ (fun u => physical_interpolant_hessian_scale_internal
        (ofShort β s) a d e θ ε L y z hyL hzL Ky Kz _hKys _hKzs t u.val u.property)
    intro i hi χ
    obtain ⟨hsol,hest⟩ := hbound i hi χ
    have heq (ψ : Fin (a+1) → Q.1) := MatrixFieldTransport.weak_congr Q hscale
      (zeroSumComponents (Fin (a+1))) (fun l => if l = i then χ.val else 0) ψ
    refine ⟨?_,fun ψ hψ => hest ψ ((heq ψ).mp hψ)⟩
    obtain ⟨ψ,hψ,huniq⟩ := hsol
    exact ⟨ψ,(heq ψ).mpr hψ,fun u hu => huniq u ((heq u).mp hu)⟩
  exact (congrArg R heν).mpr hf

end Riesz2.CompatibleComparison
