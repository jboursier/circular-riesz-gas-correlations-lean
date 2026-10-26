/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.InterpolantLocalLawsPart4
public import Riesz2.Thermodynamic.InterpolatingDensitiesPart2
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Admissible exteriors and conditional exceptional masses

Definitions from Subsection 6.1 and preparatory estimates for Appendix C. The exterior
carrier and conditional probability kernel are the physical ones. The rigidity event is
`goodBlockEvent`.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators

namespace Riesz2.InterpolantLocalLaws

/-- See Subsection 6.1 of the paper, geometric conditions on an exterior with `d`
gaps and `m+1` active gaps. Prefix and suffix tests include the full exterior. -/
def exteriorGeometry (s ε : ℝ) (d m : ℕ)
    (y : EuclideanSpace ℝ (Fin d)) : Prop :=
  |(((d + m : ℕ) + 1 : ℝ) - ∑ i, y i) - (m + 1 : ℕ)| ≤
      ((m + 1 : ℕ) : ℝ) ^ (min s 1 / 2 + ε) ∧
    ∀ r : ℕ, 1 ≤ r → r ≤ d →
      |(∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < r), y i) - r| ≤
          4 * ((m + 1 : ℕ) : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε) ∧
      |(∑ i ∈ Finset.univ.filter (fun i : Fin d => d - r ≤ i.val), y i) - r| ≤
          4 * ((m + 1 : ℕ) : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε)

/-- See Subsection 6.1 of the paper: the geometric exterior conditions are Borel. -/
theorem measurableSet_exteriorGeometry (s ε : ℝ) (d m : ℕ) :
    MeasurableSet {y | exteriorGeometry s ε d m y} := by
  unfold exteriorGeometry
  simp only [ofPred_and, ofPred_forall]
  refine (measurableSet_le ?_ measurable_const).inter ?_
  · exact ((measurable_const.sub (Finset.measurable_sum _ fun i _ =>
      (PiLp.continuous_apply 2 _ i).measurable)).sub measurable_const).abs
  · apply MeasurableSet.iInter
    intro r
    apply MeasurableSet.iInter
    intro _
    apply MeasurableSet.iInter
    intro _
    exact (measurableSet_le
      ((Finset.measurable_sum _ fun i _ =>
        (PiLp.continuous_apply 2 _ i).measurable).sub measurable_const).abs
      measurable_const).inter (measurableSet_le
      ((Finset.measurable_sum _ fun i _ =>
        (PiLp.continuous_apply 2 _ i).measurable).sub measurable_const).abs
      measurable_const)

/-- See Subsection 6.1 of the paper: admissibility on the positive exterior
carrier. Its residual active length is positive by the carrier condition.
The two endpoint tests use the existing Hausdorff-normalized physical kernel. -/
def admissibleExterior (p : Parameters) (d m : ℕ) (hd : 1 ≤ d)
    (θ : PhysicalCutoff) (ε A K : ℝ)
    (y : AffineSimplex.chartDomain d ((d + m : ℕ) + 1)) : Prop :=
  let h : m + 1 ≤ d + m + 1 := by omega
  let κ := InterpolatingDensities.simplexFibreKernel p d m hd
    (InterpolatingDensities.exteriorPermutation d m) θ
    (Real.rpow_pos_of_pos (show (0 : ℝ) < (m + 1 : ℕ) by positivity) (-ε))
    (Finset.univ.map (Fin.castLEEmb h)) true
  let E := {u : EuclideanSpace ℝ (Fin (m + 1)) |
    WithLp.ofLp u ∈ goodBlockEvent p.val.2 m.succPNat (d + m).succPNat ε}
  let F := {u : EuclideanSpace ℝ (Fin (m + 1)) |
    WithLp.ofLp u ∉ goodBlockEvent p.val.2 m.succPNat (d + m).succPNat (K * ε)}
  exteriorGeometry p.val.2 ε d m y.val ∧
    (2 : ℝ≥0∞)⁻¹ ≤ κ y E ∧
    (∫⁻ u in F, ENNReal.ofReal (exceptionalWeight p.val.2 (n := m.succPNat) (WithLp.ofLp u)) ∂κ y) ≤
      ENNReal.ofReal (Real.exp (-((m + 1 : ℕ) : ℝ) ^ (2 * A * ε)))

/-- See Subsection 6.1 of the paper: every endpoint exceptional mass in the
admissibility definition is a Borel function of the whole exterior. -/
theorem measurable_endpoint_exceptional_mass (p : Parameters) (d m : ℕ) (hd : 1 ≤ d)
    (θ : PhysicalCutoff) (ε η : ℝ) :
    let h : m + 1 ≤ d + m + 1 := by omega
    let κ := InterpolatingDensities.simplexFibreKernel p d m hd
      (InterpolatingDensities.exteriorPermutation d m) θ
      (Real.rpow_pos_of_pos (show (0 : ℝ) < (m + 1 : ℕ) by positivity) (-ε))
      (Finset.univ.map (Fin.castLEEmb h)) true
    Measurable (fun y => ∫⁻ u in {u : EuclideanSpace ℝ (Fin (m + 1)) |
        WithLp.ofLp u ∉ goodBlockEvent p.val.2 m.succPNat (d + m).succPNat η},
      ENNReal.ofReal (exceptionalWeight p.val.2 (n := m.succPNat) (WithLp.ofLp u)) ∂κ y) := by
  intro h κ
  have hE := (measurableSet_goodBlockEvent p.val.2 m.succPNat (d + m).succPNat η).preimage
    (WithLp.measurable_ofLp 2 _)
  have hW := (measurable_exceptionalWeight p.val.2 (n := m.succPNat)
    (fun u : EuclideanSpace ℝ (Fin (m + 1)) => WithLp.ofLp u)
    (fun i => (PiLp.continuous_apply 2 _ i).measurable)).ennreal_ofReal
  have hm := (hW.indicator hE.compl).lintegral_kernel (κ := κ)
  have he (y) := lintegral_indicator (μ := κ y) hE.compl
    (fun u => ENNReal.ofReal (exceptionalWeight p.val.2 (n := m.succPNat) (WithLp.ofLp u)))
  convert hm using 1
  funext y
  exact (he y).symm

/-- See Subsection 6.1 of the paper: admissible compatible positive exteriors form
a Borel subset of their actual carrier. No off-carrier conditional version
is selected. -/
theorem measurableSet_admissibleExterior (p : Parameters) (d m : ℕ) (hd : 1 ≤ d)
    (θ : PhysicalCutoff) (ε A K : ℝ) :
    MeasurableSet {y | admissibleExterior p d m hd θ ε A K y} := by
  unfold admissibleExterior
  dsimp only
  refine ((measurableSet_exteriorGeometry p.val.2 ε d m).preimage
    measurable_subtype_coe).inter ?_
  apply MeasurableSet.inter
  · exact measurableSet_le (measurable_const (a := (2 : ℝ≥0∞)⁻¹))
      (Kernel.measurable_coe _
        ((measurableSet_goodBlockEvent p.val.2 m.succPNat (d + m).succPNat ε).preimage
          (WithLp.measurable_ofLp 2 _)))
  · exact measurableSet_le (measurable_endpoint_exceptional_mass p d m hd θ ε (K * ε))
      measurable_const

/-- See Subsection 6.1 of the paper: the physical conditional law is supported
on its exact positive mass simplex, for every compatible exterior. -/
theorem ae_mem_exterior_simplex (p : Parameters) (d m : ℕ) (hd : 1 ≤ d)
    (σ : Equiv.Perm (Fin (d + m + 1))) (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (J : Finset (Fin (d + m + 1))) (b : Bool)
    (y : AffineSimplex.chartDomain d ((d + m : ℕ) + 1)) :
    ∀ᵐ u ∂InterpolatingDensities.simplexFibreKernel p d m hd σ θ ha J b y,
      u ∈ AffineSimplex.massSimplex m (((d + m : ℕ) + 1 : ℝ) - ∑ i, y.val i) := by
  obtain ⟨_, h0, ht, he⟩ :=
    InterpolatingDensities.simplexFibreKernel_density p d m hd σ θ ha J b y
  rw [he, AffineFibre.normalizedMeasure]
  apply (withDensity_absolutelyContinuous _ _).ae_le
  rw [AffineSimplex.simplexVolume_eq_restrict]
  apply ae_restrict_mem
  change MeasurableSet ({u | ∀ i, 0 < u i} ∩ AffineSimplex.massHyperplane m _)
  simp only [ofPred_forall]
  refine (MeasurableSet.iInter fun i : Fin (m + 1) => ?_).inter
    (AffineSimplex.isClosed_massHyperplane m _).measurableSet
  exact measurableSet_lt measurable_const (PiLp.continuous_apply 2 _ i).measurable

/-- See Subsection 6.1 of the paper: the weight is at least one almost everywhere
for every physical conditional, before any admissibility restriction. -/
theorem ae_one_le_exterior_weight (p : Parameters) (d m : ℕ) (hd : 1 ≤ d)
    (σ : Equiv.Perm (Fin (d + m + 1))) (θ : PhysicalCutoff) {a : ℝ} (ha : 0 < a)
    (J : Finset (Fin (d + m + 1))) (b : Bool)
    (y : AffineSimplex.chartDomain d ((d + m : ℕ) + 1)) :
    ∀ᵐ u ∂InterpolatingDensities.simplexFibreKernel p d m hd σ θ ha J b y,
      (1 : ℝ≥0∞) ≤ ENNReal.ofReal
        (exceptionalWeight p.val.2 (n := m.succPNat) (WithLp.ofLp u)) := by
  filter_upwards [ae_mem_exterior_simplex p d m hd σ θ ha J b y] with u hu
  simpa only [ENNReal.ofReal_one] using
    (ENNReal.ofReal_le_ofReal (one_le_exceptionalWeight p.val.2
      (WithLp.ofLp u) (fun i => (hu.1 i).le)))

/-- See Subsection 6.1 of the paper: the admissible set is Borel also as a subset
of the ambient exterior space, via its actual compatible carrier. -/
theorem measurableSet_admissibleExterior_image (p : Parameters) (d m : ℕ) (hd : 1 ≤ d)
    (θ : PhysicalCutoff) (ε A K : ℝ) :
    MeasurableSet (Subtype.val '' {y | admissibleExterior p d m hd θ ε A K y}) := by
  exact (MeasurableEmbedding.subtype_coe
    (AffineSimplex.isOpen_chartDomain d ((d + m : ℕ) + 1)).measurableSet).measurableSet_image.mpr
      (measurableSet_admissibleExterior p d m hd θ ε A K)

/-- Reconstruction from the retained coordinates on the actual
mass simplex. See Subsection 6.1. -/
theorem retained_chart_coordinates (d m : ℕ) (L : ℝ)
    (σ : Equiv.Perm (Fin (d + m + 1)))
    (u : EuclideanSpace ℝ (Fin (d + m + 1)))
    (hu : u ∈ AffineSimplex.massSimplex (d + m) L) :
    RetainedSimplex.chart d m L σ (RetainedSimplex.coordinates d m σ u) = u := by
  have hs := ((RetainedSimplex.reindex_mem_simplex (d + m) L σ.symm u).mpr hu).2
  simp only [RetainedSimplex.chart, RetainedSimplex.coordinates]
  rw [(RetainedSimplex.join d m).apply_symm_apply, AffineSimplex.chart_coordinates (d + m) L hs]
  simpa only [← LinearIsometryEquiv.piLpCongrLeft_symm] using
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ).apply_symm_apply u

/-- In the exterior-first chart, reconstructing the fibre from the
coordinates of a particle configuration gives its literal first block.
See Subsection 6.1 of the paper. The last active gap is included. -/
theorem exterior_chart_particle_active (d m : ℕ)
    (X : Riesz1.Configuration (d + m).succPNat) :
    let q := RetainedSimplex.coordinates d m (InterpolatingDensities.exteriorPermutation d m)
      (WithLp.toLp 2 (gapVector X))
    AffineSimplex.chart m (((d + m : ℕ) + 1 : ℝ) - ∑ i, q.1 i) q.2 =
      WithLp.toLp 2 (finiteGapBlock (K := m.succPNat) X) := by
  intro q
  have hu : WithLp.toLp 2 (gapVector X) ∈ AffineSimplex.massSimplex (d + m) (((d + m : ℕ) + 1 : ℝ)) :=
    (GapChart.gapVector_eq_chart (d + m) X).symm ▸
      (AffineSimplex.chart_mem_simplex_iff _ _ _).mpr (GapChart.gaps _ X).property
  have he := retained_chart_coordinates d m (((d + m : ℕ) + 1 : ℝ))
    (InterpolatingDensities.exteriorPermutation d m) _ hu
  rw [← RetainedSimplex.assemble_chart] at he
  ext i
  have hi := congrArg (fun v => v (Fin.castLE (show m + 1 ≤ d + m + 1 by omega) i)) he
  rw [InterpolatingDensities.assemble_exterior_active] at hi
  change _ = gap X (i.val : ℤ)
  rw [gap_eq_gapVector_labelOf]
  have hl := Riesz1.labelOf_natCast (d + m).succPNat
    (Fin.castLE (show m + 1 ≤ d + m + 1 by omega) i)
  change Riesz1.labelOf (d + m).succPNat (i.val : ℤ) =
    Fin.castLE (show m + 1 ≤ d + m + 1 by omega) i at hl
  rw [hl]
  exact hi

/-- Exterior coordinates in the retained chart are the literal physical
gaps after the active block. See Subsection 6.1. -/
theorem exterior_coordinates_gap (d m : ℕ)
    (X : Riesz1.Configuration (d + m).succPNat) (i : Fin d) :
    (RetainedSimplex.coordinates d m (InterpolatingDensities.exteriorPermutation d m)
      (WithLp.toLp 2 (gapVector X))).1 i = gap X (((m + 1 : ℕ) : ℤ) + i.val) := by
  rw [RetainedSimplex.coordinates_retained, InterpolatingDensities.exteriorPermutation_retained,
    gap_eq_gapVector_labelOf]
  have hl := Riesz1.labelOf_natCast (d + m).succPNat
    (⟨m + 1 + i.val, by omega⟩ : Fin (d + m + 1))
  convert congrArg (gapVector X) hl.symm using 1
  push_cast
  rfl

/-- Every exterior prefix, including the full exterior, is the actual
particle block starting at an exterior endpoint of Subsection 6.1. -/
theorem exterior_coordinates_prefix (d m : ℕ)
    (X : Riesz1.Configuration (d + m).succPNat) (r : ℕ) (hr : r ≤ d) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin d => i.val < r),
      (RetainedSimplex.coordinates d m (InterpolatingDensities.exteriorPermutation d m)
        (WithLp.toLp 2 (gapVector X))).1 i) =
      Riesz1.blockLength X ((m + 1 : ℕ) : ℤ) r := by
  rw [← anchored_exterior_sum]
  apply Finset.sum_bij (fun i _ => i.val)
  · intro i hi
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro a ha
    exact ⟨⟨a, by have := Finset.mem_range.mp ha; omega⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_range.mp ha⟩, rfl⟩
  · intro i _
    exact exterior_coordinates_gap d m X i

/-- Every exterior suffix, including the full exterior, is the actual
block ending at the end of the physical cycle. See Subsection 6.1. -/
theorem exterior_coordinates_suffix (d m : ℕ)
    (X : Riesz1.Configuration (d + m).succPNat) (r : ℕ) (hr : r ≤ d) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin d => d - r ≤ i.val),
      (RetainedSimplex.coordinates d m (InterpolatingDensities.exteriorPermutation d m)
        (WithLp.toLp 2 (gapVector X))).1 i) =
      Riesz1.blockLength X (((d + m + 1 - r : ℕ) : ℤ)) r := by
  rw [← anchored_exterior_sum]
  apply Finset.sum_bij (fun i _ => i.val - (d - r))
  · intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    exact Finset.mem_range.mpr (by omega)
  · intro i hi j hj hij
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    apply Fin.ext
    omega
  · intro a ha
    have ha' := Finset.mem_range.mp ha
    refine ⟨⟨d - r + a, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · change d - r ≤ d - r + a
      omega
    · simp
  · intro i hi
    rw [exterior_coordinates_gap]
    have hi' := (Finset.mem_filter.mp hi).2
    congr 1
    omega

/-- The residual length of an actual exterior is exactly the active
block length. See Subsection 6.1. -/
theorem exterior_coordinates_length (d m : ℕ)
    (X : Riesz1.Configuration (d + m).succPNat) :
    ((d + m : ℕ) + 1 : ℝ) -
      (∑ i, (RetainedSimplex.coordinates d m (InterpolatingDensities.exteriorPermutation d m)
        (WithLp.toLp 2 (gapVector X))).1 i) = Riesz1.blockLength X 0 (m + 1) := by
  have hp := exterior_coordinates_prefix d m X d le_rfl
  simp only [Fin.is_lt, Finset.filter_true] at hp
  rw [hp, ← anchored_exterior_sum]
  have he := exterior_residual_length (N := (d + m).succPNat) (n := m.succPNat)
    (by change m + 1 ≤ d + m + 1; omega) X
  have hc : ((d + m).succPNat : ℕ) - (m.succPNat : ℕ) = d := by
    change d + m + 1 - (m + 1) = d
    omega
  rw [hc] at he
  convert he using 1 <;> simp [Nat.succPNat]

/-- See Subsection 6.1 of the paper: every geometric condition on the literal
exterior is exactly the corresponding physical particle-block condition. -/
theorem exteriorGeometry_particle_iff (s ε : ℝ) (d m : ℕ)
    (X : Riesz1.Configuration (d + m).succPNat) :
    exteriorGeometry s ε d m
      (RetainedSimplex.coordinates d m (InterpolatingDensities.exteriorPermutation d m)
        (WithLp.toLp 2 (gapVector X))).1 ↔
      |Riesz1.blockLength X 0 (m + 1) - (m + 1 : ℕ)| ≤
        ((m + 1 : ℕ) : ℝ) ^ (min s 1 / 2 + ε) ∧
      ∀ r : ℕ, 1 ≤ r → r ≤ d →
        |Riesz1.blockLength X ((m + 1 : ℕ) : ℤ) r - r| ≤
            4 * ((m + 1 : ℕ) : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε) ∧
        |Riesz1.blockLength X ((d + m + 1 - r : ℕ) : ℤ) r - r| ≤
            4 * ((m + 1 : ℕ) : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε) := by
  unfold exteriorGeometry
  rw [exterior_coordinates_length]
  constructor
  · rintro ⟨hL, hR⟩
    refine ⟨hL, fun r hr1 hrd => ?_⟩
    have hh := hR r hr1 hrd
    rwa [exterior_coordinates_prefix d m X r hrd,
      exterior_coordinates_suffix d m X r hrd] at hh
  · rintro ⟨hL, hR⟩
    refine ⟨hL, fun r hr1 hrd => ?_⟩
    rw [exterior_coordinates_prefix d m X r hrd,
      exterior_coordinates_suffix d m X r hrd]
    exact hR r hr1 hrd

/-- The physical exterior marginal in the exterior-first chart, with the
exact tilt, Gibbs and chart normalizers. See Subsection 6.1 of the paper.
`physical_exterior_disintegration` proves that this is a probability and
identifies its conditional integrals. -/
def physicalExteriorLaw (p : Parameters) (d m : ℕ) (θ : PhysicalCutoff) (ε : ℝ) :
    Measure (AffineSimplex.chartDomain d ((d + m : ℕ) + 1)) :=
  let h : m + 1 ≤ d + m + 1 := by omega
  (tiltNormalizer p (d + m).succPNat m.succPNat h θ ε true)⁻¹ •
    (partitionFunction p (d + m).succPNat)⁻¹ •
    ENNReal.ofReal ((d + m + 1 : ℝ) ^ (d + m))⁻¹ •
      (((volume : Measure (EuclideanSpace ℝ (Fin d))).comap
        ((↑) : AffineSimplex.chartDomain d ((d + m : ℕ) + 1) → _)).withDensity
        (fun y => AffineFibre.fibreMass volume
          (ProperMarginalChart.penalizedChartDensity p d m
            (InterpolatingDensities.exteriorPermutation d m) θ (((m + 1 : ℕ) : ℝ) ^ (-ε))
            (Finset.univ.map (Fin.castLEEmb h)) true) y.val))

/-- See Subsection 6.1 of the paper, in the exact form needed to disintegrate the
full-law estimate of Appendix C. The displayed exterior
marginal is a probability, and all measurable nonnegative active tests
disintegrate through the existing physical simplex kernel. -/
theorem physical_exterior_disintegration (p : Parameters) (d m : ℕ) (hd : 1 ≤ d)
    (θ : PhysicalCutoff) (ε : ℝ) :
    let h : m + 1 ≤ d + m + 1 := by omega
    let σ := InterpolatingDensities.exteriorPermutation d m
    let ha := Real.rpow_pos_of_pos (show (0 : ℝ) < (m + 1 : ℕ) by positivity) (-ε)
    let J := Finset.univ.map (Fin.castLEEmb h)
    let κ := InterpolatingDensities.simplexFibreKernel p d m hd σ θ ha J true
    let ν := physicalExteriorLaw p d m θ ε
    IsProbabilityMeasure ν ∧ ∀ f :
      EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin (m + 1)) → ℝ≥0∞,
      Measurable f →
      (∫⁻ X, f ((RetainedSimplex.coordinates d m σ (WithLp.toLp 2 (gapVector X))).1,
        WithLp.toLp 2 (finiteGapBlock (K := m.succPNat) X))
        ∂tiltedParticleMeasure p (d + m).succPNat m.succPNat h θ ε true) =
      ∫⁻ y, ∫⁻ u, f (y.val, u) ∂κ y ∂ν := by
  intro h σ ha J κ ν
  let a := ((m + 1 : ℕ) : ℝ) ^ (-ε)
  let ρ := tiltedParticleMeasure p (d + m).succPNat m.succPNat h θ ε true
  let κ0 := InterpolatingDensities.penalizedFibreKernel p d m hd σ θ ha J true
  let μ0 := ((volume : Measure (EuclideanSpace ℝ (Fin d))).comap
    ((↑) : AffineSimplex.chartDomain d ((d + m : ℕ) + 1) → _)).withDensity
    (fun y => AffineFibre.fibreMass volume
      (ProperMarginalChart.penalizedChartDensity p d m σ θ a J true) y.val)
  have hcoords : Measurable (fun X : Riesz1.Configuration (d + m).succPNat =>
      RetainedSimplex.coordinates d m σ (WithLp.toLp 2 (gapVector X))) :=
    (RetainedSimplex.continuous_coordinates d m σ).measurable.comp
      ((PiLp.volume_preserving_toLp _).measurable.comp (Riesz1.measurable_gapVector _))
  have hdis := InterpolatingDensities.tilted_coordinates_disintegration p d m hd σ
    m.succPNat h θ ε true
  have hall (f : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin (m + 1)) → ℝ≥0∞)
      (hf : Measurable f) :
      (∫⁻ X, f ((RetainedSimplex.coordinates d m σ (WithLp.toLp 2 (gapVector X))).1,
        WithLp.toLp 2 (finiteGapBlock (K := m.succPNat) X)) ∂ρ) =
        ∫⁻ y, ∫⁻ u, f (y.val, u) ∂κ y ∂ν := by
    let g := fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin m) =>
      f (q.1, AffineSimplex.chart m (((d + m : ℕ) + 1 : ℝ) - ∑ i, q.1 i) q.2)
    have hg : Measurable g := hf.comp (measurable_fst.prodMk
      ((AffineFibre.SumChart.totalChart m).continuous.measurable.comp
        ((measurable_const.sub (Finset.measurable_sum _ fun i _ =>
          (PiLp.continuous_apply 2 _ i).measurable.comp measurable_fst)).prodMk measurable_snd)))
    calc
      _ = ∫⁻ X, g (RetainedSimplex.coordinates d m σ (WithLp.toLp 2 (gapVector X))) ∂ρ := by
        apply lintegral_congr
        intro X
        exact congrArg (fun u => f (_, u)) (exterior_chart_particle_active d m X).symm
      _ = ∫⁻ q, g q ∂ρ.map (fun X : Riesz1.Configuration (d + m).succPNat => RetainedSimplex.coordinates d m σ
          (WithLp.toLp 2 (gapVector X))) := (lintegral_map hg hcoords).symm
      _ = _ := by
        rw [hdis]
        simp only [ν, physicalExteriorLaw, lintegral_smul_measure]
        congr 3
        change (∫⁻ q, g q ∂(μ0 ⊗ₘ κ0).map (fun q => (q.1.val, q.2))) =
          ∫⁻ y, ∫⁻ u, f (y.val, u) ∂κ y ∂μ0
        rw [lintegral_map (μ := μ0 ⊗ₘ κ0) (f := g)
          (g := fun q => (q.1.val, q.2)) hg
          ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)]
        rw [Measure.lintegral_compProd (μ := μ0) (κ := κ0)
          (f := fun q : AffineSimplex.chartDomain d ((d + m : ℕ) + 1) ×
            EuclideanSpace ℝ (Fin m) => g (q.1.val, q.2)) (hg.comp
          ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd))]
        apply lintegral_congr
        intro y
        change (∫⁻ z, f (y.val, AffineSimplex.chart m
            (((d + m : ℕ) + 1 : ℝ) - ∑ i, y.val i) z) ∂κ0 y) =
          ∫⁻ u, f (y.val, u) ∂(κ0 y).map
            (AffineSimplex.chart m (((d + m : ℕ) + 1 : ℝ) - ∑ i, y.val i))
        exact (lintegral_map (μ := κ0 y) (f := fun u => f (y.val, u))
          (hf.comp measurable_prodMk_left) (AffineSimplex.continuous_chart m _).measurable).symm
  have hprob : IsProbabilityMeasure ρ := (InterpolatingDensities.tilt_valid _ _ _ _ _ _ _).2.2
  refine ⟨⟨?_⟩, hall⟩
  have hone := hall (fun _ => 1) measurable_const
  simpa only [lintegral_const, measure_univ, mul_one, one_mul] using hone.symm

/-- The exterior marginal gives the actual probability of every Borel
exterior event, not merely an abstract base density. See Subsection 6.1. -/
theorem physical_exterior_event (p : Parameters) (d m : ℕ) (hd : 1 ≤ d)
    (θ : PhysicalCutoff) (ε : ℝ) (S : Set (EuclideanSpace ℝ (Fin d)))
    (hS : MeasurableSet S) :
    let h : m + 1 ≤ d + m + 1 := by omega
    (physicalExteriorLaw p d m θ ε) (Subtype.val ⁻¹' S) =
      (tiltedParticleMeasure p (d + m).succPNat m.succPNat h θ ε true)
        {X | (RetainedSimplex.coordinates d m (InterpolatingDensities.exteriorPermutation d m)
          (WithLp.toLp 2 (gapVector X))).1 ∈ S} := by
  intro h
  let ρ := tiltedParticleMeasure p (d + m).succPNat m.succPNat h θ ε true
  have hm := (physical_exterior_disintegration p d m hd θ ε).2
    (fun q => S.indicator (fun _ => (1 : ℝ≥0∞)) q.1)
    ((measurable_const.indicator hS).comp measurable_fst)
  have hX : Measurable (fun X : Riesz1.Configuration (d + m).succPNat =>
      (RetainedSimplex.coordinates d m (InterpolatingDensities.exteriorPermutation d m)
        (WithLp.toLp 2 (gapVector X))).1) :=
    measurable_fst.comp ((RetainedSimplex.continuous_coordinates _ _ _).measurable.comp
      ((PiLp.volume_preserving_toLp _).measurable.comp (Riesz1.measurable_gapVector _)))
  have he : (fun X : Riesz1.Configuration (d + m).succPNat =>
      S.indicator (fun _ => (1 : ℝ≥0∞))
        (RetainedSimplex.coordinates d m (InterpolatingDensities.exteriorPermutation d m)
          (WithLp.toLp 2 (gapVector X))).1) =
      {X : Riesz1.Configuration (d + m).succPNat |
        (RetainedSimplex.coordinates d m (InterpolatingDensities.exteriorPermutation d m)
          (WithLp.toLp 2 (gapVector X))).1 ∈ S}.indicator (fun _ => (1 : ℝ≥0∞)) := by
    rfl
  change (∫⁻ X : Riesz1.Configuration (d + m).succPNat, S.indicator (fun _ => (1 : ℝ≥0∞))
    (RetainedSimplex.coordinates d m (InterpolatingDensities.exteriorPermutation d m)
      (WithLp.toLp 2 (gapVector X))).1 ∂ρ) = _ at hm
  have hEvent : MeasurableSet {X : Riesz1.Configuration (d + m).succPNat |
      (RetainedSimplex.coordinates d m (InterpolatingDensities.exteriorPermutation d m)
        (WithLp.toLp 2 (gapVector X))).1 ∈ S} := hX hS
  rw [he] at hm
  have hm' := (lintegral_indicator_one (μ := ρ) hEvent).symm.trans hm
  simp only [lintegral_const, measure_univ, mul_one] at hm'
  change _ = ∫⁻ y, (Subtype.val ⁻¹' S).indicator (fun _ => (1 : ℝ≥0∞)) y
    ∂physicalExteriorLaw p d m θ ε at hm'
  have hi := lintegral_indicator_one (μ := physicalExteriorLaw p d m θ ε)
    (hS.preimage measurable_subtype_coe)
  exact hi.symm.trans hm'.symm

/-- The physical weighted block failure disintegrates into precisely the
endpoint exceptional masses in admissibility. Appendix C. This is an equality, without a tail hypothesis. -/
theorem disintegrated_weighted_block_failure (p : Parameters) (d m : ℕ) (hd : 1 ≤ d)
    (θ : PhysicalCutoff) (ε η : ℝ) :
    let h : m + 1 ≤ d + m + 1 := by omega
    let κ := InterpolatingDensities.simplexFibreKernel p d m hd
      (InterpolatingDensities.exteriorPermutation d m) θ
      (Real.rpow_pos_of_pos (show (0 : ℝ) < (m + 1 : ℕ) by positivity) (-ε))
      (Finset.univ.map (Fin.castLEEmb h)) true
    (∫⁻ X in {X | finiteGapBlock X ∉ goodBlockEvent p.val.2 m.succPNat (d + m).succPNat η},
      ENNReal.ofReal (exceptionalWeight p.val.2 (finiteGapBlock (K := m.succPNat) X))
      ∂tiltedParticleMeasure p (d + m).succPNat m.succPNat h θ ε true) =
    ∫⁻ y, ∫⁻ u in {u : EuclideanSpace ℝ (Fin (m + 1)) |
        WithLp.ofLp u ∉ goodBlockEvent p.val.2 m.succPNat (d + m).succPNat η},
      ENNReal.ofReal (exceptionalWeight p.val.2 (n := m.succPNat) (WithLp.ofLp u))
      ∂κ y ∂physicalExteriorLaw p d m θ ε := by
  intro h κ
  let E := {u : EuclideanSpace ℝ (Fin (m + 1)) |
    WithLp.ofLp u ∉ goodBlockEvent p.val.2 m.succPNat (d + m).succPNat η}
  let W := fun u : EuclideanSpace ℝ (Fin (m + 1)) =>
    ENNReal.ofReal (exceptionalWeight p.val.2 (n := m.succPNat) (WithLp.ofLp u))
  have hE : MeasurableSet E := ((measurableSet_goodBlockEvent p.val.2 m.succPNat (d + m).succPNat η).preimage
    (WithLp.measurable_ofLp 2 _)).compl
  have hW : Measurable W := (measurable_exceptionalWeight p.val.2
    (n := m.succPNat) _ (fun i => (PiLp.continuous_apply 2 _ i).measurable)).ennreal_ofReal
  have hevent : MeasurableSet {X : Riesz1.Configuration (d + m).succPNat |
      finiteGapBlock (K := m.succPNat) X ∉ goodBlockEvent p.val.2 m.succPNat (d + m).succPNat η} :=
    ((measurableSet_goodBlockEvent p.val.2 m.succPNat (d + m).succPNat η).preimage
      (show Measurable (finiteGapBlock (N := (d + m).succPNat) (K := m.succPNat)) from
        Measurable.of_eval (fun i => Riesz1.measurable_gap i.val))).compl
  have hm := (physical_exterior_disintegration p d m hd θ ε).2
    (fun q => E.indicator W q.2) ((hW.indicator hE).comp measurable_snd)
  change (∫⁻ X, {X : Riesz1.Configuration (d + m).succPNat |
      finiteGapBlock (K := m.succPNat) X ∉ goodBlockEvent p.val.2 m.succPNat (d + m).succPNat η}.indicator
        (fun X => ENNReal.ofReal (exceptionalWeight p.val.2
          (finiteGapBlock (K := m.succPNat) X))) X ∂_) = _ at hm
  rw [lintegral_indicator hevent] at hm
  simpa only [lintegral_indicator hE] using hm

namespace Internal

variable {B F : Type*} [MeasurableSpace B] [MeasurableSpace F]

/-- The disintegrated endpoint Markov estimate in Appendix C. It applies to the measurable physical kernel
without selecting any conditional version. -/
theorem endpoint_weight_failure (μ : Measure B) [SFinite μ]
    (κ : Kernel B F) [IsMarkovKernel κ] {f : F → ℝ≥0∞} (hf : Measurable f)
    {a : ℝ≥0∞} (ha : a ≠ 0) (hat : a ≠ ∞) :
    μ {y | a < ∫⁻ u, f u ∂κ y} ≤
      (∫⁻ q, f q.2 ∂μ ⊗ₘ κ) / a := by
  have hs : {y | a < ∫⁻ u, f u ∂κ y} ⊆
      {y | a ≤ ∫⁻ u, f u ∂κ y} := by
    intro y hy
    change a < ∫⁻ u, f u ∂κ y at hy
    exact hy.le
  apply (measure_mono hs).trans
  rw [Measure.lintegral_compProd (f := fun q : B × F => f q.2) (hf.comp measurable_snd)]
  exact meas_ge_le_lintegral_div (hf.lintegral_kernel (κ := κ)).aemeasurable ha hat

/-- Failure of endpoint mass one half costs at most twice the
disintegrated weighted exceptional integral. See Appendix C. The weight only needs its actual a.e. lower bound. -/
theorem endpoint_half_mass_failure (μ : Measure B) [SFinite μ]
    (κ : Kernel B F) [IsMarkovKernel κ] {E : Set F} (hE : MeasurableSet E)
    {W : F → ℝ≥0∞} (hW : Measurable W)
    (hW1 : ∀ y, ∀ᵐ u ∂κ y, 1 ≤ W u) :
    μ {y | κ y E < (2 : ℝ≥0∞)⁻¹} ≤
      2 * ∫⁻ q, Eᶜ.indicator W q.2 ∂μ ⊗ₘ κ := by
  have hs : {y | κ y E < (2 : ℝ≥0∞)⁻¹} ⊆
      {y | (2 : ℝ≥0∞)⁻¹ ≤ ∫⁻ u, Eᶜ.indicator W u ∂κ y} := by
    intro y hy
    change κ y E < (2 : ℝ≥0∞)⁻¹ at hy
    have hcomp : (2 : ℝ≥0∞)⁻¹ ≤ κ y Eᶜ := by
      rw [prob_compl_eq_one_sub hE]
      apply ENNReal.le_sub_of_add_le_left (measure_ne_top _ _)
      calc
        κ y E + (2 : ℝ≥0∞)⁻¹ ≤ (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ :=
          add_le_add hy.le le_rfl
        _ = 1 := by
          rw [← mul_two, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
    apply hcomp.trans
    rw [lintegral_indicator hE.compl]
    calc
      κ y Eᶜ = ∫⁻ _ in Eᶜ, (1 : ℝ≥0∞) ∂κ y := by simp
      _ ≤ ∫⁻ u in Eᶜ, W u ∂κ y :=
        lintegral_mono_ae ((ae_restrict_of_ae (hW1 y)))
  apply (measure_mono hs).trans
  have h := meas_ge_le_lintegral_div (μ := μ)
    ((hW.indicator hE.compl).lintegral_kernel (κ := κ)).aemeasurable
    (show (2 : ℝ≥0∞)⁻¹ ≠ 0 by norm_num)
    (show (2 : ℝ≥0∞)⁻¹ ≠ ∞ by norm_num)
  rw [← Measure.lintegral_compProd (f := fun q : B × F => Eᶜ.indicator W q.2)
    ((hW.indicator hE.compl).comp measurable_snd)] at h
  simpa only [div_eq_mul_inv, inv_inv, mul_comm] using h

variable {X : Type*} [MeasurableSpace X]

/-- Weighted Hölder on one reference simplex, including `t=0,1`.
This is the numerator estimate of Appendix C. No finite Bochner expectation is substituted for an infinite integral. -/
theorem weighted_geometric_holder (μ : Measure X) {p q f : X → ℝ≥0∞}
    (hp : Measurable p) (hq : Measurable q) (hf : Measurable f)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫⁻ x, f x * (p x ^ (1 - t) * q x ^ t) ∂μ) ≤
      (∫⁻ x, f x * p x ∂μ) ^ (1 - t) * (∫⁻ x, f x * q x ∂μ) ^ t := by
  have he (x : X) : f x * (p x ^ (1 - t) * q x ^ t) =
      (f x * p x) ^ (1 - t) * (f x * q x) ^ t := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (sub_nonneg.mpr ht1),
      ENNReal.mul_rpow_of_nonneg _ _ ht0]
    calc
      _ = (f x ^ (1 - t) * f x ^ t) * (p x ^ (1 - t) * q x ^ t) := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.mpr ht1) ht0]
        simp
      _ = _ := by ac_rfl
  simp_rw [he]
  exact ENNReal.lintegral_mul_norm_pow_le (hf.mul hp).aemeasurable
    (hf.mul hq).aemeasurable (sub_nonneg.mpr ht1) ht0 (by ring)

/-- A pointwise density comparison yields the reverse estimate for the
geometric normalizer. Used on normalized restrictions to the coarse
rigidity set in Appendix C. -/
theorem geometric_lower_of_domination (μ : Measure X) {p q : X → ℝ≥0∞}
    (hp : Measurable p) (hq : Measurable q) (hp1 : ∫⁻ x, p x ∂μ = 1)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ∞) (hdom : ∀ᵐ x ∂μ, p x ≤ c * q x)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (c ^ t)⁻¹ ≤ ∫⁻ x, p x ^ (1 - t) * q x ^ t ∂μ := by
  have hc0' : c ^ t ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hc0) hct).ne'
  have hct' : c ^ t ≠ ∞ := (ENNReal.rpow_lt_top_of_nonneg ht0 hct).ne
  rw [← one_div, ENNReal.div_le_iff hc0' hct', mul_comm]
  calc
    1 = ∫⁻ x, p x ∂μ := hp1.symm
    _ ≤ ∫⁻ x, c ^ t * (p x ^ (1 - t) * q x ^ t) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hdom] with x hx
      calc
        p x = p x ^ (1 - t) * p x ^ t := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.mpr ht1) ht0]
          simp
        _ ≤ p x ^ (1 - t) * (c * q x) ^ t :=
          mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hx ht0)
        _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ ht0]; ac_rfl
    _ = _ := lintegral_const_mul _ ((hp.pow_const _).mul (hq.pow_const _))

/-- The cross-density bound obtained by exponentiating an oscillation
estimate controls the normalized restrictions to the coarse event.
This is the density-ratio step in Appendix C. -/
theorem restricted_density_comparison (μ : Measure X) {p q : X → ℝ≥0∞}
    (hp : Measurable p) (hq : Measurable q) {E : Set X} (hE : MeasurableSet E)
    {c : ℝ≥0∞}
    (ha0 : (∫⁻ x in E, p x ∂μ) ≠ 0) (hat : (∫⁻ x in E, p x ∂μ) ≠ ∞)
    (hb0 : (∫⁻ x in E, q x ∂μ) ≠ 0) (hbt : (∫⁻ x in E, q x ∂μ) ≠ ∞)
    (hcross : ∀ x ∈ E, ∀ y ∈ E, p x * q y ≤ c * q x * p y)
    {x : X} (hx : x ∈ E) :
    (∫⁻ y in E, p y ∂μ)⁻¹ * p x ≤
      c * ((∫⁻ y in E, q y ∂μ)⁻¹ * q x) := by
  let a := ∫⁻ y in E, p y ∂μ
  let b := ∫⁻ y in E, q y ∂μ
  have h : p x * b ≤ c * q x * a := by
    rw [← lintegral_const_mul _ hq, ← lintegral_const_mul _ hp]
    exact setLIntegral_mono' hE (fun y hy => hcross x hx y hy)
  have h' := mul_le_mul' (le_refl a⁻¹) (mul_le_mul' h (le_refl b⁻¹))
  calc
    a⁻¹ * p x = a⁻¹ * (p x * b * b⁻¹) := by
      rw [ENNReal.mul_inv_cancel_right hb0 hbt]
    _ ≤ a⁻¹ * (c * q x * a * b⁻¹) := h'
    _ = c * (b⁻¹ * q x) := by
      calc
        _ = (a⁻¹ * a) * (c * (b⁻¹ * q x)) := by ac_rfl
        _ = _ := by rw [ENNReal.inv_mul_cancel ha0 hat, one_mul]

/-- Common-simplex normalizer lower bound of Appendix C. A cross-density ratio of at most `c` on an
event of endpoint mass at least one half gives `Z_t ≥ 1/(2c)`.
The proof includes both endpoints of the interpolation interval. -/
theorem geometric_normalizer_lower (μ : Measure X) {p q : X → ℝ≥0∞}
    (hp : Measurable p) (hq : Measurable q)
    (hp1 : ∫⁻ x, p x ∂μ = 1) (hq1 : ∫⁻ x, q x ∂μ = 1)
    {E : Set X} (hE : MeasurableSet E)
    (hpm : (2 : ℝ≥0∞)⁻¹ ≤ ∫⁻ x in E, p x ∂μ)
    (hqm : (2 : ℝ≥0∞)⁻¹ ≤ ∫⁻ x in E, q x ∂μ)
    {c : ℝ≥0∞} (hc : 1 ≤ c) (hct : c ≠ ∞)
    (hcross : ∀ x ∈ E, ∀ y ∈ E, p x * q y ≤ c * q x * p y)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (2 : ℝ≥0∞)⁻¹ * c⁻¹ ≤ ∫⁻ x, p x ^ (1 - t) * q x ^ t ∂μ := by
  let a := ∫⁻ x in E, p x ∂μ
  let b := ∫⁻ x in E, q x ∂μ
  have ha0 : a ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hpm)
  have hb0 : b ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hqm)
  have hat : a ≠ ∞ := ne_top_of_le_ne_top (by simp) ((setLIntegral_le_lintegral E p).trans_eq hp1)
  have hbt : b ≠ ∞ := ne_top_of_le_ne_top (by simp) ((setLIntegral_le_lintegral E q).trans_eq hq1)
  have hc0 : c ≠ 0 := ne_of_gt (zero_lt_one.trans_le hc)
  have htn : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  let pE := fun x => a⁻¹ * p x
  let qE := fun x => b⁻¹ * q x
  have hpE : Measurable pE := measurable_const.mul hp
  have hqE : Measurable qE := measurable_const.mul hq
  have hpE1 : ∫⁻ x in E, pE x ∂μ = 1 := by
    rw [lintegral_const_mul _ hp, ENNReal.inv_mul_cancel ha0 hat]
  have hdom : ∀ᵐ x ∂μ.restrict E, pE x ≤ c * qE x := by
    filter_upwards [ae_restrict_mem hE] with x hx
    exact restricted_density_comparison μ hp hq hE ha0 hat hb0 hbt hcross hx
  have hlow := geometric_lower_of_domination (μ.restrict E) hpE hqE hpE1 hc0 hct hdom ht0 ht1
  have hscale (x : X) : p x ^ (1 - t) * q x ^ t =
      (a ^ (1 - t) * b ^ t) * (pE x ^ (1 - t) * qE x ^ t) := by
    calc
      _ = (a * pE x) ^ (1 - t) * (b * qE x) ^ t := by
        rw [ENNReal.mul_inv_cancel_left ha0 hat, ENNReal.mul_inv_cancel_left hb0 hbt]
      _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ htn, ENNReal.mul_rpow_of_nonneg _ _ ht0]
        ac_rfl
  have hmass : (2 : ℝ≥0∞)⁻¹ ≤ a ^ (1 - t) * b ^ t := by
    calc
      _ = ((2 : ℝ≥0∞)⁻¹) ^ (1 - t) * ((2 : ℝ≥0∞)⁻¹) ^ t := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ htn ht0]
        simp
      _ ≤ _ := mul_le_mul' (ENNReal.rpow_le_rpow hpm htn) (ENNReal.rpow_le_rpow hqm ht0)
  have hpow : c⁻¹ ≤ (c ^ t)⁻¹ := ENNReal.inv_le_inv.mpr (by
    simpa only [ENNReal.rpow_one] using ENNReal.rpow_le_rpow_of_exponent_le hc ht1)
  calc
    _ ≤ (a ^ (1 - t) * b ^ t) * (c ^ t)⁻¹ := mul_le_mul' hmass hpow
    _ ≤ (a ^ (1 - t) * b ^ t) * ∫⁻ x in E, pE x ^ (1 - t) * qE x ^ t ∂μ :=
      mul_le_mul' le_rfl hlow
    _ = ∫⁻ x in E, p x ^ (1 - t) * q x ^ t ∂μ := by
      simp_rw [hscale]
      exact (lintegral_const_mul _ ((hpE.pow_const (1 - t)).mul (hqE.pow_const t))).symm
    _ ≤ _ := setLIntegral_le_lintegral _ _

/-- See Appendix C in the paper, the full weighted transfer on one
simplex from a cross-density bound. Both endpoint normalizations and the
interpolating normalization are probability normalizations. -/
theorem normalized_geometric_weighted_transfer (μ : Measure X) {p q f : X → ℝ≥0∞}
    (hp : Measurable p) (hq : Measurable q) (hf : Measurable f)
    (hp1 : ∫⁻ x, p x ∂μ = 1) (hq1 : ∫⁻ x, q x ∂μ = 1)
    {E : Set X} (hE : MeasurableSet E)
    (hpm : (2 : ℝ≥0∞)⁻¹ ≤ ∫⁻ x in E, p x ∂μ)
    (hqm : (2 : ℝ≥0∞)⁻¹ ≤ ∫⁻ x in E, q x ∂μ)
    {c : ℝ≥0∞} (hc : 1 ≤ c) (hct : c ≠ ∞)
    (hcross : ∀ x ∈ E, ∀ y ∈ E, p x * q y ≤ c * q x * p y)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let g := fun x => p x ^ (1 - t) * q x ^ t
    ∃ h0 ht,
      IsProbabilityMeasure (AffineFibre.normalizedMeasure μ g h0 ht) ∧
      (∫⁻ x, f x ∂AffineFibre.normalizedMeasure μ g h0 ht) ≤
        (2 * c) * ((∫⁻ x, f x * p x ∂μ) ^ (1 - t) * (∫⁻ x, f x * q x ∂μ) ^ t) := by
  intro g
  have hg : Measurable g := (hp.pow_const _).mul (hq.pow_const _)
  have hlo := geometric_normalizer_lower μ hp hq hp1 hq1 hE hpm hqm hc hct hcross ht0 ht1
  have hpos : 0 < (2 : ℝ≥0∞)⁻¹ * c⁻¹ :=
    ENNReal.mul_pos (by norm_num) (ENNReal.inv_ne_zero.mpr hct)
  have h0 : (∫⁻ x, g x ∂μ) ≠ 0 := ne_of_gt (hpos.trans_le hlo)
  have hle : (∫⁻ x, g x ∂μ) ≤ 1 := by
    have h := ENNReal.lintegral_mul_norm_pow_le (μ := μ) hp.aemeasurable hq.aemeasurable
      (sub_nonneg.mpr ht1) ht0 (show 1 - t + t = 1 by ring)
    simpa only [hp1, hq1, ENNReal.one_rpow, mul_one] using h
  have ht : (∫⁻ x, g x ∂μ) ≠ ∞ := ne_top_of_le_ne_top (by simp) hle
  have hi : (∫⁻ x, g x ∂μ)⁻¹ ≤ 2 * c := by
    have h := ENNReal.inv_le_inv.mpr hlo
    rwa [← ENNReal.mul_inv (Or.inl (show (2 : ℝ≥0∞) ≠ 0 by norm_num))
      (Or.inl (show (2 : ℝ≥0∞) ≠ ∞ by norm_num)), inv_inv] at h
  refine ⟨h0, ht, AffineFibre.isProbabilityMeasure_normalizedMeasure μ hg h0 ht, ?_⟩
  rw [AffineFibre.lintegral_normalizedMeasure μ hg h0 ht hf]
  have hholder := weighted_geometric_holder μ hp hq hf ht0 ht1
  have hnum : (∫⁻ x, g x * f x ∂μ) ≤
      (∫⁻ x, f x * p x ∂μ) ^ (1 - t) * (∫⁻ x, f x * q x ∂μ) ^ t := by
    simpa only [mul_comm (f _)] using hholder
  exact mul_le_mul' hi hnum

/-- Exponentiating the precise energy-difference oscillation in Appendix C gives the cross-density bound. Normalizing each
endpoint by its own partition function preserves that bound. -/
theorem exponential_cross_of_oscillation (μ : Measure X) (P Ky Kz : X → ℝ)
    {β B : ℝ} (hβ : 0 ≤ β) {E : Set X}
    (hOsc : ∀ x ∈ E, ∀ y ∈ E, |(Ky x - Kz x) - (Ky y - Kz y)| ≤ B)
    (h00 : (∫⁻ x, ENNReal.ofReal (Real.exp (-β * (P x + Ky x))) ∂μ) ≠ 0)
    (h0t : (∫⁻ x, ENNReal.ofReal (Real.exp (-β * (P x + Ky x))) ∂μ) ≠ ∞)
    (h10 : (∫⁻ x, ENNReal.ofReal (Real.exp (-β * (P x + Kz x))) ∂μ) ≠ 0)
    (h1t : (∫⁻ x, ENNReal.ofReal (Real.exp (-β * (P x + Kz x))) ∂μ) ≠ ∞) :
    let p := AffineFibre.normalizedDensity μ
      (fun x => ENNReal.ofReal (Real.exp (-β * (P x + Ky x)))) h00 h0t
    let q := AffineFibre.normalizedDensity μ
      (fun x => ENNReal.ofReal (Real.exp (-β * (P x + Kz x)))) h10 h1t
    ∀ x ∈ E, ∀ y ∈ E,
      p x * q y ≤ ENNReal.ofReal (Real.exp (β * B)) * q x * p y := by
  intro p q x hx y hy
  have hd : (Ky y - Kz y) - (Ky x - Kz x) ≤ B := by
    have h := hOsc y hy x hx
    exact (le_abs_self _).trans h
  have he : -β * (P x + Ky x) + -β * (P y + Kz y) ≤
      β * B + -β * (P x + Kz x) + -β * (P y + Ky y) := by
    nlinarith [mul_le_mul_of_nonneg_left hd hβ]
  have hw : ENNReal.ofReal (Real.exp (-β * (P x + Ky x))) *
      ENNReal.ofReal (Real.exp (-β * (P y + Kz y))) ≤
      ENNReal.ofReal (Real.exp (β * B)) *
        ENNReal.ofReal (Real.exp (-β * (P x + Kz x))) *
        ENNReal.ofReal (Real.exp (-β * (P y + Ky y))) := by
    simp_rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr he)
  dsimp only [p, q, AffineFibre.normalizedDensity]
  calc
    _ = ((∫⁻ u, ENNReal.ofReal (Real.exp (-β * (P u + Ky u))) ∂μ)⁻¹ *
        (∫⁻ u, ENNReal.ofReal (Real.exp (-β * (P u + Kz u))) ∂μ)⁻¹) *
        (ENNReal.ofReal (Real.exp (-β * (P x + Ky x))) *
          ENNReal.ofReal (Real.exp (-β * (P y + Kz y)))) := by ac_rfl
    _ ≤ _ := (mul_le_mul' le_rfl hw).trans_eq (by ac_rfl)

/-- The normalized geometric interpolation of normalized exponential
endpoint densities equals the physical exponential interpolation on the
same reference measure. See Subsection 6.1 of the paper. The assertion requires
positive finite normalizers and introduces no alternate law. -/
theorem normalized_geometric_eq_gibbs (μ : Measure X) (P Ky Kz : X → ℝ)
    (hP : Measurable P) (hKy : Measurable Ky) (hKz : Measurable Kz)
    (β : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h00 : (∫⁻ x, ENNReal.ofReal (Real.exp (-β * (P x + Ky x))) ∂μ) ≠ 0)
    (h0t : (∫⁻ x, ENNReal.ofReal (Real.exp (-β * (P x + Ky x))) ∂μ) ≠ ∞)
    (h10 : (∫⁻ x, ENNReal.ofReal (Real.exp (-β * (P x + Kz x))) ∂μ) ≠ 0)
    (h1t : (∫⁻ x, ENNReal.ofReal (Real.exp (-β * (P x + Kz x))) ∂μ) ≠ ∞)
    (hT0 : (∫⁻ x, ENNReal.ofReal
      (Real.exp (-β * (P x + (1 - t) * Ky x + t * Kz x))) ∂μ) ≠ 0)
    (hTt : (∫⁻ x, ENNReal.ofReal
      (Real.exp (-β * (P x + (1 - t) * Ky x + t * Kz x))) ∂μ) ≠ ∞) :
    let p := AffineFibre.normalizedDensity μ
      (fun x => ENNReal.ofReal (Real.exp (-β * (P x + Ky x)))) h00 h0t
    let q := AffineFibre.normalizedDensity μ
      (fun x => ENNReal.ofReal (Real.exp (-β * (P x + Kz x)))) h10 h1t
    ∀ hG0 hGt,
      AffineFibre.normalizedMeasure μ (fun x => p x ^ (1 - t) * q x ^ t) hG0 hGt =
        AffineFibre.normalizedMeasure μ (fun x => ENNReal.ofReal
          (Real.exp (-β * (P x + (1 - t) * Ky x + t * Kz x)))) hT0 hTt := by
  intro p q hG0 hGt
  let a := (∫⁻ x, ENNReal.ofReal (Real.exp (-β * (P x + Ky x))) ∂μ)⁻¹
  let b := (∫⁻ x, ENNReal.ofReal (Real.exp (-β * (P x + Kz x))) ∂μ)⁻¹
  let w := fun x => ENNReal.ofReal
    (Real.exp (-β * (P x + (1 - t) * Ky x + t * Kz x)))
  let c := a ^ (1 - t) * b ^ t
  have htn : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have ha0 : a ≠ 0 := ENNReal.inv_ne_zero.mpr h0t
  have hat : a ≠ ∞ := ENNReal.inv_ne_top.mpr h00
  have hb0 : b ≠ 0 := ENNReal.inv_ne_zero.mpr h1t
  have hbt : b ≠ ∞ := ENNReal.inv_ne_top.mpr h10
  have hc0 : c ≠ 0 := mul_ne_zero
    (ENNReal.rpow_pos (pos_iff_ne_zero.mpr ha0) hat).ne'
    (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hb0) hbt).ne'
  have hct : c ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.rpow_lt_top_of_nonneg htn hat).ne
    (ENNReal.rpow_lt_top_of_nonneg ht0 hbt).ne
  have hw : Measurable w :=
    (((hP.add (hKy.const_mul (1 - t))).add (hKz.const_mul t)).const_mul (-β)).exp.ennreal_ofReal
  have he : (fun x => p x ^ (1 - t) * q x ^ t) = fun x => c * w x := by
    funext x
    dsimp only [p, q, AffineFibre.normalizedDensity]
    rw [ENNReal.mul_rpow_of_nonneg _ _ htn, ENNReal.mul_rpow_of_nonneg _ _ ht0]
    change (a ^ (1 - t) * _ ) * (b ^ t * _) = _
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le htn,
      ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le ht0,
      ← Real.exp_mul, ← Real.exp_mul]
    calc
      _ = c * (ENNReal.ofReal (Real.exp ((-β * (P x + Ky x)) * (1 - t))) *
          ENNReal.ofReal (Real.exp ((-β * (P x + Kz x)) * t))) := by dsimp [c]; ac_rfl
      _ = c * w x := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 3
        ring
  simpa only [AffineFibre.normalizedMeasure_eq_smul, he] using
    (AffineFibre.normalizedMeasure_mul_const (B := Unit)
      (w := fun q : Unit × X => w q.2) μ (hw.comp measurable_snd) () hT0 hTt hc0 hct)

/-- Internal oscillation-to-weighted-tail transfer for Appendix C. It uses exactly the oscillation of `Ky-Kz`,
and returns the actual exponential interpolation, including its endpoints. -/
theorem gibbs_weighted_transfer_of_oscillation (μ : Measure X) (P Ky Kz : X → ℝ)
    (hP : Measurable P) (hKy : Measurable Ky) (hKz : Measurable Kz)
    {β B : ℝ} (hβ : 0 ≤ β) (hB : 0 ≤ B) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h00 : (∫⁻ x, ENNReal.ofReal (Real.exp (-β * (P x + Ky x))) ∂μ) ≠ 0)
    (h0t : (∫⁻ x, ENNReal.ofReal (Real.exp (-β * (P x + Ky x))) ∂μ) ≠ ∞)
    (h10 : (∫⁻ x, ENNReal.ofReal (Real.exp (-β * (P x + Kz x))) ∂μ) ≠ 0)
    (h1t : (∫⁻ x, ENNReal.ofReal (Real.exp (-β * (P x + Kz x))) ∂μ) ≠ ∞)
    (hT0 : (∫⁻ x, ENNReal.ofReal
      (Real.exp (-β * (P x + (1 - t) * Ky x + t * Kz x))) ∂μ) ≠ 0)
    (hTt : (∫⁻ x, ENNReal.ofReal
      (Real.exp (-β * (P x + (1 - t) * Ky x + t * Kz x))) ∂μ) ≠ ∞)
    {E : Set X} (hE : MeasurableSet E)
    (hOsc : ∀ x ∈ E, ∀ y ∈ E, |(Ky x - Kz x) - (Ky y - Kz y)| ≤ B)
    (hpm : (2 : ℝ≥0∞)⁻¹ ≤ (AffineFibre.normalizedMeasure μ
      (fun x => ENNReal.ofReal (Real.exp (-β * (P x + Ky x)))) h00 h0t) E)
    (hqm : (2 : ℝ≥0∞)⁻¹ ≤ (AffineFibre.normalizedMeasure μ
      (fun x => ENNReal.ofReal (Real.exp (-β * (P x + Kz x)))) h10 h1t) E)
    {f : X → ℝ≥0∞} (hf : Measurable f) {R : ℝ≥0∞}
    (hfp : (∫⁻ x, f x ∂AffineFibre.normalizedMeasure μ
      (fun x => ENNReal.ofReal (Real.exp (-β * (P x + Ky x)))) h00 h0t) ≤ R)
    (hfq : (∫⁻ x, f x ∂AffineFibre.normalizedMeasure μ
      (fun x => ENNReal.ofReal (Real.exp (-β * (P x + Kz x)))) h10 h1t) ≤ R) :
    (∫⁻ x, f x ∂AffineFibre.normalizedMeasure μ (fun x => ENNReal.ofReal
      (Real.exp (-β * (P x + (1 - t) * Ky x + t * Kz x)))) hT0 hTt) ≤
      (2 * ENNReal.ofReal (Real.exp (β * B))) * R := by
  let w0 := fun x => ENNReal.ofReal (Real.exp (-β * (P x + Ky x)))
  let w1 := fun x => ENNReal.ofReal (Real.exp (-β * (P x + Kz x)))
  have hw0 : Measurable w0 := ((hP.add hKy).const_mul (-β)).exp.ennreal_ofReal
  have hw1 : Measurable w1 := ((hP.add hKz).const_mul (-β)).exp.ennreal_ofReal
  let p := AffineFibre.normalizedDensity μ w0 h00 h0t
  let q := AffineFibre.normalizedDensity μ w1 h10 h1t
  have hp := AffineFibre.measurable_normalizedDensity μ hw0 h00 h0t
  have hq := AffineFibre.measurable_normalizedDensity μ hw1 h10 h1t
  have hp1 := AffineFibre.lintegral_normalizedDensity μ hw0 h00 h0t
  have hq1 := AffineFibre.lintegral_normalizedDensity μ hw1 h10 h1t
  change (2 : ℝ≥0∞)⁻¹ ≤ μ.withDensity p E at hpm
  change (2 : ℝ≥0∞)⁻¹ ≤ μ.withDensity q E at hqm
  rw [withDensity_apply _ hE] at hpm hqm
  have hc : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (β * B)) := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
      (Real.one_le_exp (mul_nonneg hβ hB))
  obtain ⟨hG0, hGt, _, htransfer⟩ := normalized_geometric_weighted_transfer μ hp hq hf
    hp1 hq1 hE hpm hqm hc ENNReal.ofReal_ne_top
    (exponential_cross_of_oscillation μ P Ky Kz hβ hOsc h00 h0t h10 h1t) ht0 ht1
  rw [normalized_geometric_eq_gibbs μ P Ky Kz hP hKy hKz β ht0 ht1
    h00 h0t h10 h1t hT0 hTt hG0 hGt] at htransfer
  have hfp' : (∫⁻ x, f x * p x ∂μ) ≤ R := by
    change (∫⁻ x, f x ∂μ.withDensity p) ≤ R at hfp
    rw [lintegral_withDensity_eq_lintegral_mul _ hp hf] at hfp
    simpa only [Pi.mul_apply, mul_comm (f _)] using hfp
  have hfq' : (∫⁻ x, f x * q x ∂μ) ≤ R := by
    change (∫⁻ x, f x ∂μ.withDensity q) ≤ R at hfq
    rw [lintegral_withDensity_eq_lintegral_mul _ hq hf] at hfq
    simpa only [Pi.mul_apply, mul_comm (f _)] using hfq
  apply htransfer.trans
  apply mul_le_mul' le_rfl
  calc
    _ ≤ R ^ (1 - t) * R ^ t := mul_le_mul'
      (ENNReal.rpow_le_rpow hfp' (sub_nonneg.mpr ht1)) (ENNReal.rpow_le_rpow hfq' ht0)
    _ = R := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.mpr ht1) ht0]
      simp

/-- The coarse-oscillation and endpoint exponents in Appendix C imply its
pre-absorption weighted bound, assuming the physical oscillation estimate. -/
theorem interpolant_tail_of_coarse_oscillation (s β ε A K L : ℝ) (m : ℕ) (N : ℕ+)
    (_hL : 0 < L) (_hLN : L < (N : ℝ)) (hβ : 0 ≤ β)
    (P Ky Kz : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hP : Measurable P) (hKy : Measurable Ky) (hKz : Measurable Kz)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let μ := AffineSimplex.simplexVolume m L
    let w0 := fun x => ENNReal.ofReal (Real.exp (-β * (P x + Ky x)))
    let w1 := fun x => ENNReal.ofReal (Real.exp (-β * (P x + Kz x)))
    let wt := fun x => ENNReal.ofReal (Real.exp (-β * (P x + (1 - t) * Ky x + t * Kz x)))
    ∀ h00 h0t h10 h1t hT0 hTt,
    let ν0 := AffineFibre.normalizedMeasure μ w0 h00 h0t
    let ν1 := AffineFibre.normalizedMeasure μ w1 h10 h1t
    let νt := AffineFibre.normalizedMeasure μ wt hT0 hTt
    let E := AffineSimplex.massSimplex m L ∩
      {x | WithLp.ofLp x ∈ goodBlockEvent s m.succPNat N ε}
    let F := {x : EuclideanSpace ℝ (Fin (m + 1)) |
      WithLp.ofLp x ∉ goodBlockEvent s m.succPNat N (K * ε)}
    let W := fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
      ENNReal.ofReal (exceptionalWeight s (n := m.succPNat) (WithLp.ofLp x))
    (∀ x ∈ E, ∀ y ∈ E, |(Ky x - Kz x) - (Ky y - Kz y)| ≤
      ((m + 1 : ℕ) : ℝ) ^ (A * ε)) →
    (2 : ℝ≥0∞)⁻¹ ≤ ν0 E → (2 : ℝ≥0∞)⁻¹ ≤ ν1 E →
    (∫⁻ x in F, W x ∂ν0) ≤ ENNReal.ofReal (Real.exp (-((m + 1 : ℕ) : ℝ) ^ (2 * A * ε))) →
    (∫⁻ x in F, W x ∂ν1) ≤ ENNReal.ofReal (Real.exp (-((m + 1 : ℕ) : ℝ) ^ (2 * A * ε))) →
    (∫⁻ x in F, W x ∂νt) ≤ ENNReal.ofReal
      (2 * Real.exp (β * ((m + 1 : ℕ) : ℝ) ^ (A * ε) -
        ((m + 1 : ℕ) : ℝ) ^ (2 * A * ε))) := by
  intro μ w0 w1 wt h00 h0t h10 h1t hT0 hTt ν0 ν1 νt E F W hOsc hpm hqm hfp hfq
  have hE : MeasurableSet E := (RetainedSimplex.measurableSet_simplex m L).inter
    ((measurableSet_goodBlockEvent s m.succPNat N ε).preimage (WithLp.measurable_ofLp 2 _))
  have hF : MeasurableSet F := ((measurableSet_goodBlockEvent s m.succPNat N (K * ε)).preimage
    (WithLp.measurable_ofLp 2 _)).compl
  have hW : Measurable W := (measurable_exceptionalWeight s (n := m.succPNat) _
    (fun i => (PiLp.continuous_apply 2 _ i).measurable)).ennreal_ofReal
  have hy := (lintegral_indicator (μ := ν0) hF W).trans_le hfp
  have hz := (lintegral_indicator (μ := ν1) hF W).trans_le hfq
  have hb := gibbs_weighted_transfer_of_oscillation μ P Ky Kz hP hKy hKz hβ
    (show 0 ≤ ((m + 1 : ℕ) : ℝ) ^ (A * ε) by positivity) ht0 ht1
    h00 h0t h10 h1t hT0 hTt hE hOsc hpm hqm (hW.indicator hF) hy hz
  apply (lintegral_indicator (μ := νt) hF W).symm.trans_le
  apply hb.trans_eq
  rw [mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num), ← Real.exp_add]
  rfl

/-- The two local-law consequences in Appendix C follow from the weighted
exceptional-mass bound. -/
theorem block_events_of_weighted_failure (s η : ℝ) (n N : ℕ+)
    (μ : Measure (EuclideanSpace ℝ (Fin (n : ℕ)))) [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ x ∂μ, ∀ i, 0 ≤ x i) {R : ℝ≥0∞}
    (hfailure : (∫⁻ x in {x : EuclideanSpace ℝ (Fin (n : ℕ)) |
        WithLp.ofLp x ∉ goodBlockEvent s n N η},
      ENNReal.ofReal (exceptionalWeight s (WithLp.ofLp x)) ∂μ) ≤ R) :
    (∀ i : Fin (n : ℕ),
      1 - R ≤ μ {x | (n : ℝ) ^ (-η) ≤ x i ∧ x i ≤ (n : ℝ) ^ η}) ∧
    ∀ a b : ℕ, a < b → b ≤ (n : ℕ) →
      μ {x | (n : ℝ) ^ η * (b - a : ℕ) ^ (min s 1 / 2) <
        |(∑ i ∈ Finset.univ.filter (fun i : Fin (n : ℕ) => a ≤ i.val ∧ i.val < b), x i) -
          (b - a : ℕ)|} ≤ R := by
  let E := {x : EuclideanSpace ℝ (Fin (n : ℕ)) | WithLp.ofLp x ∈ goodBlockEvent s n N η}
  have hE : MeasurableSet E := (measurableSet_goodBlockEvent s n N η).preimage
    (WithLp.measurable_ofLp 2 _)
  have hweight : ∀ᵐ x ∂μ, (1 : ℝ≥0∞) ≤ ENNReal.ofReal (exceptionalWeight s (WithLp.ofLp x)) := by
    filter_upwards [hpos] with x hx
    simpa only [ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal (one_le_exceptionalWeight s (WithLp.ofLp x) hx)
  have hbad : μ Eᶜ ≤ R := by
    apply le_trans _ hfailure
    calc
      μ Eᶜ = ∫⁻ _ in Eᶜ, (1 : ℝ≥0∞) ∂μ := by simp
      _ ≤ _ := lintegral_mono_ae (ae_restrict_of_ae hweight)
  constructor
  · intro i
    let C := {x : EuclideanSpace ℝ (Fin (n : ℕ)) |
      (n : ℝ) ^ (-η) ≤ x i ∧ x i ≤ (n : ℝ) ^ η}
    have hC : MeasurableSet C :=
      (measurableSet_le measurable_const (PiLp.continuous_apply 2 _ i).measurable).inter
        (measurableSet_le (PiLp.continuous_apply 2 _ i).measurable measurable_const)
    have hsub : Cᶜ ⊆ Eᶜ := by
      intro x hx hgood
      exact hx (hgood.2.1 i)
    have hc : μ Cᶜ ≤ R := (measure_mono hsub).trans hbad
    apply tsub_le_iff_right.mpr
    calc
      1 = μ Cᶜ + μ C := by rw [add_comm, prob_add_prob_compl hC]
      _ ≤ R + μ C := add_le_add hc le_rfl
      _ = μ C + R := add_comm _ _
  · intro a b hab hbn
    apply le_trans (measure_mono ?_) hbad
    intro x hx hgood
    exact (not_lt_of_ge (hgood.2.2 a b hab hbn)) hx

end Internal

/-- See Appendix C in the paper, both disintegrated endpoint-failure
inequalities before numerical tail absorption. They hold for the actual
physical exterior marginal and conditional kernel, at every active size. -/
theorem physical_endpoint_failure_bounds (p : Parameters) (d m : ℕ) (hd : 1 ≤ d)
    (θ : PhysicalCutoff) (ε η : ℝ) :
    let h : m + 1 ≤ d + m + 1 := by omega
    let κ := InterpolatingDensities.simplexFibreKernel p d m hd
      (InterpolatingDensities.exteriorPermutation d m) θ
      (Real.rpow_pos_of_pos (show (0 : ℝ) < (m + 1 : ℕ) by positivity) (-ε))
      (Finset.univ.map (Fin.castLEEmb h)) true
    let E := {u : EuclideanSpace ℝ (Fin (m + 1)) |
      WithLp.ofLp u ∈ goodBlockEvent p.val.2 m.succPNat (d + m).succPNat η}
    let W := fun u : EuclideanSpace ℝ (Fin (m + 1)) => ENNReal.ofReal
      (exceptionalWeight p.val.2 (n := m.succPNat) (WithLp.ofLp u))
    let M := ∫⁻ X in {X | finiteGapBlock X ∉ goodBlockEvent p.val.2 m.succPNat (d + m).succPNat η},
      ENNReal.ofReal (exceptionalWeight p.val.2 (finiteGapBlock (K := m.succPNat) X))
      ∂tiltedParticleMeasure p (d + m).succPNat m.succPNat h θ ε true
    (physicalExteriorLaw p d m θ ε) {y | κ y E < (2 : ℝ≥0∞)⁻¹} ≤ 2 * M ∧
    ∀ R : ℝ≥0∞, R ≠ 0 → R ≠ ∞ →
      (physicalExteriorLaw p d m θ ε) {y | R < ∫⁻ u in Eᶜ, W u ∂κ y} ≤ M / R := by
  intro h κ E W M
  let ν := physicalExteriorLaw p d m θ ε
  have := (physical_exterior_disintegration p d m hd θ ε).1
  have hE : MeasurableSet E := (measurableSet_goodBlockEvent p.val.2
    m.succPNat (d + m).succPNat η).preimage (WithLp.measurable_ofLp 2 _)
  have hW : Measurable W := (measurable_exceptionalWeight p.val.2
    (n := m.succPNat) _ (fun i => (PiLp.continuous_apply 2 _ i).measurable)).ennreal_ofReal
  have hdis : (∫⁻ q, Eᶜ.indicator W q.2 ∂ν ⊗ₘ κ) = M := by
    rw [Measure.lintegral_compProd (f := fun q => Eᶜ.indicator W q.2)
      ((hW.indicator hE.compl).comp measurable_snd)]
    have hm := (disintegrated_weighted_block_failure p d m hd θ ε η).symm
    change (∫⁻ y, ∫⁻ u in Eᶜ, W u ∂κ y ∂ν) = M at hm
    calc
      _ = ∫⁻ y, ∫⁻ u in Eᶜ, W u ∂κ y ∂ν := by
        apply lintegral_congr
        intro y
        exact lintegral_indicator (μ := κ y) hE.compl W
      _ = M := hm
  constructor
  · have hb := Internal.endpoint_half_mass_failure ν κ hE hW
      (ae_one_le_exterior_weight p d m hd _ θ _ _ true)
    rwa [hdis] at hb
  · intro R hR hRt
    have hb := Internal.endpoint_weight_failure ν κ (hW.indicator hE.compl) hR hRt
    rw [hdis] at hb
    have hi (y) := lintegral_indicator (μ := κ y) hE.compl W
    simpa only [hi] using hb

/-- Endpoint failure tails for Appendix C, obtained
from `full_law_local_laws`. The structural power precedes both tolerances
and the temperature interval. The second estimate retains the threshold
as a variable so it can be specialized to `exp(-n^(2*A*ε))`. -/
theorem compact_endpoint_failure_tails (hRig : External.LongRangeRigidityLocallyUniform)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ ηstar astar εstar : ℝ, 0 < ηstar ∧ 0 < astar ∧ 0 < εstar ∧
      ∀ η : ℝ, 0 < η → η ≤ ηstar → ∀ ε : ℝ, 0 < ε → ε ≤ εstar →
      ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
        ∀ d m : ℕ, ∀ hd : 1 ≤ d, 1 ≤ m → 4 * (m + 1) ≤ d + m + 1 →
          ((m + 1 : ℕ) : ℝ) ^ (2 / s) ≤ ((d + m : ℕ) + 1 : ℝ) →
          let h : m + 1 ≤ d + m + 1 := by omega
          let κ := InterpolatingDensities.simplexFibreKernel p d m hd
            (InterpolatingDensities.exteriorPermutation d m) θ
            (Real.rpow_pos_of_pos (show (0 : ℝ) < (m + 1 : ℕ) by positivity) (-ε))
            (Finset.univ.map (Fin.castLEEmb h)) true
          let E := {u : EuclideanSpace ℝ (Fin (m + 1)) |
            WithLp.ofLp u ∈ goodBlockEvent s m.succPNat (d + m).succPNat η}
          let W := fun u : EuclideanSpace ℝ (Fin (m + 1)) => ENNReal.ofReal
            (exceptionalWeight s (n := m.succPNat) (WithLp.ofLp u))
          (physicalExteriorLaw p d m θ ε) {y | κ y E < (2 : ℝ≥0∞)⁻¹} ≤
            ENNReal.ofReal (C * Real.exp (-c * ((m + 1 : ℕ) : ℝ) ^ (astar * η))) ∧
          ∀ R : ℝ≥0∞, R ≠ 0 → R ≠ ∞ →
            (physicalExteriorLaw p d m θ ε) {y | R < ∫⁻ u in Eᶜ, W u ∂κ y} ≤
              ENNReal.ofReal (C * Real.exp (-c * ((m + 1 : ℕ) : ℝ) ^ (astar * η))) / R := by
  obtain ⟨ηstar, astar, εstar, hηstar, hastar, hεstar, hfull⟩ :=
    full_law_local_laws hRig s hs hs1
  refine ⟨ηstar, astar, εstar, hηstar, hastar, hεstar, ?_⟩
  intro η hη hηs ε hε hεs βlo βhi hlo hle θ
  obtain ⟨_, _, _, hinput⟩ := hfull η hη hηs ε hε hεs
  obtain ⟨C, c, hC, hc, hbound⟩ := hinput βlo βhi hlo hle θ
  refine ⟨2 * C, c, by positivity, hc, ?_⟩
  intro p hps hpl hph d m hd hm hsize hsize' h κ E W
  obtain ⟨hhalf, hweight⟩ := physical_endpoint_failure_bounds p d m hd θ ε η
  rw [hps] at hhalf hweight
  have hnreal : (m.succPNat : ℝ) = ((m + 1 : ℕ) : ℝ) := rfl
  have hNreal : ((d + m).succPNat : ℝ) = ((d + m : ℕ) + 1 : ℝ) := by
    simp [Nat.succPNat]
  have hfullbound := (hbound p hps hpl hph (d + m).succPNat m.succPNat
    (by change 2 ≤ m + 1; omega) hsize (by rw [hnreal, hNreal]; exact hsize') h).1
  rw [hnreal] at hfullbound
  have h2 : (2 : ℝ≥0∞) * ENNReal.ofReal
      (C * Real.exp (-c * ((m + 1 : ℕ) : ℝ) ^ (astar * η))) =
      ENNReal.ofReal ((2 * C) * Real.exp (-c * ((m + 1 : ℕ) : ℝ) ^ (astar * η))) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  refine ⟨hhalf.trans ((mul_le_mul' le_rfl hfullbound).trans_eq h2), ?_⟩
  intro R hR hRt
  apply (hweight R hR hRt).trans
  apply ENNReal.div_le_div_right
  apply hfullbound.trans
  apply ENNReal.ofReal_le_ofReal
  nlinarith [Real.exp_pos (-c * ((m + 1 : ℕ) : ℝ) ^ (astar * η))]

/-- The geometric part of admissibility fails with the full-law tail,
uniformly in exterior dimension and compact positive temperature intervals.
See Appendix C in the paper, the geometric clause of equation (6.10). -/
theorem compact_exterior_marginal_geometry (hRig : External.LongRangeRigidityLocallyUniform)
    (s ε βlo βhi : ℝ) (hs : 0 < s) (hs1 : s ≠ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) (hεs : ε / 2 ≤ (1 - min s 1 / 2) / 4)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (θ : PhysicalCutoff) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ d m : ℕ, 1 ≤ d → 1 ≤ m → 4 * (m + 1) ≤ d + m + 1 →
        (physicalExteriorLaw p d m θ ε) {y | ¬exteriorGeometry s ε d m y.val} ≤
          ENNReal.ofReal (C * Real.exp (-c * ((m + 1 : ℕ) : ℝ) ^
            (ε * ((1 - min s 1 / 2) / 4) / (4 * (4 * (s + 2)))))) := by
  obtain ⟨C, c, hC, hc, hbound⟩ := compact_exterior_geometry hRig s ε βlo βhi
    hs hs1 hε hε1 hεs hlo hle θ
  refine ⟨C, c, hC, hc, ?_⟩
  intro p hps hpl hph d m hd hm hsize
  change (physicalExteriorLaw p d m θ ε)
    (Subtype.val ⁻¹' {y | ¬exteriorGeometry s ε d m y}) ≤ _
  rw [physical_exterior_event p d m hd θ ε {y | ¬exteriorGeometry s ε d m y}
    (measurableSet_exteriorGeometry s ε d m).compl]
  have h := hbound p hps hpl hph (d + m).succPNat m.succPNat
    (by change 2 ≤ m + 1; omega) hsize (by change m + 1 ≤ d + m + 1; omega)
  have hc' : ((d + m).succPNat : ℕ) - (m.succPNat : ℕ) = d := by
    change d + m + 1 - (m + 1) = d
    omega
  have he : {X : Riesz1.Configuration (d + m).succPNat |
      ¬exteriorGeometry s ε d m
        (RetainedSimplex.coordinates d m (InterpolatingDensities.exteriorPermutation d m)
          (WithLp.toLp 2 (gapVector X))).1} =
      {X | ((m + 1 : ℕ) : ℝ) ^ (min s 1 / 2 + ε) <
          |Riesz1.blockLength X 0 (m + 1) - (m + 1 : ℕ)| ∨
        ∃ r : ℕ, 1 ≤ r ∧ r ≤ d ∧
          (4 * ((m + 1 : ℕ) : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε) <
            |Riesz1.blockLength X ((m + 1 : ℕ) : ℤ) r - r| ∨
           4 * ((m + 1 : ℕ) : ℝ) ^ ε * (r : ℝ) ^ (min s 1 / 2 + ε) <
            |Riesz1.blockLength X ((d + m + 1 - r : ℕ) : ℤ) r - r|)} := by
    ext X
    simp only [mem_ofPred_eq, exteriorGeometry_particle_iff,
      not_and_or, not_forall, not_le, exists_prop]
  let ρ := tiltedParticleMeasure p (d + m).succPNat m.succPNat
    (show m + 1 ≤ d + m + 1 by omega) θ ε true
  change ρ {X | ¬exteriorGeometry s ε d m
    (RetainedSimplex.coordinates d m (InterpolatingDensities.exteriorPermutation d m)
      (WithLp.toLp 2 (gapVector X))).1} ≤ _
  rw [he]
  rw [hc'] at h
  simpa only [Nat.succPNat_coe, Nat.succ_eq_add_one] using h

/-- Exact admissibility failure decomposition in Appendix C. Both endpoint terms are already disintegrated
back to the full physical tilted law. This holds at bounded sizes too. -/
theorem admissible_failure_decomposition (p : Parameters) (d m : ℕ) (hd : 1 ≤ d)
    (θ : PhysicalCutoff) (ε A K : ℝ) :
    let h : m + 1 ≤ d + m + 1 := by omega
    let M := fun η => ∫⁻ X in
      {X | finiteGapBlock X ∉ goodBlockEvent p.val.2 m.succPNat (d + m).succPNat η},
      ENNReal.ofReal (exceptionalWeight p.val.2 (finiteGapBlock (K := m.succPNat) X))
      ∂tiltedParticleMeasure p (d + m).succPNat m.succPNat h θ ε true
    (physicalExteriorLaw p d m θ ε) {y | ¬admissibleExterior p d m hd θ ε A K y} ≤
      (physicalExteriorLaw p d m θ ε) {y | ¬exteriorGeometry p.val.2 ε d m y.val} +
        2 * M ε + M (K * ε) /
          ENNReal.ofReal (Real.exp (-((m + 1 : ℕ) : ℝ) ^ (2 * A * ε))) := by
  intro h M
  let ν := physicalExteriorLaw p d m θ ε
  let κ := InterpolatingDensities.simplexFibreKernel p d m hd
    (InterpolatingDensities.exteriorPermutation d m) θ
    (Real.rpow_pos_of_pos (show (0 : ℝ) < (m + 1 : ℕ) by positivity) (-ε))
    (Finset.univ.map (Fin.castLEEmb h)) true
  let E := {u : EuclideanSpace ℝ (Fin (m + 1)) |
    WithLp.ofLp u ∈ goodBlockEvent p.val.2 m.succPNat (d + m).succPNat ε}
  let F := {u : EuclideanSpace ℝ (Fin (m + 1)) |
    WithLp.ofLp u ∉ goodBlockEvent p.val.2 m.succPNat (d + m).succPNat (K * ε)}
  let W := fun u : EuclideanSpace ℝ (Fin (m + 1)) =>
    ENNReal.ofReal (exceptionalWeight p.val.2 (n := m.succPNat) (WithLp.ofLp u))
  let R := ENNReal.ofReal (Real.exp (-((m + 1 : ℕ) : ℝ) ^ (2 * A * ε)))
  have hsub : {y | ¬admissibleExterior p d m hd θ ε A K y} ⊆
      {y | ¬exteriorGeometry p.val.2 ε d m y.val} ∪
        ({y | κ y E < (2 : ℝ≥0∞)⁻¹} ∪ {y | R < ∫⁻ u in F, W u ∂κ y}) := by
    intro y hy
    by_cases hg : exteriorGeometry p.val.2 ε d m y.val
    · by_cases he : (2 : ℝ≥0∞)⁻¹ ≤ κ y E
      · by_cases hf : (∫⁻ u in F, W u ∂κ y) ≤ R
        · exact False.elim (hy ⟨hg, he, hf⟩)
        · exact Or.inr (Or.inr (lt_of_not_ge hf))
      · exact Or.inr (Or.inl (lt_of_not_ge he))
    · exact Or.inl hg
  have hhalf := (physical_endpoint_failure_bounds p d m hd θ ε ε).1
  have hweight := (physical_endpoint_failure_bounds p d m hd θ ε (K * ε)).2
    R (ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)) ENNReal.ofReal_ne_top
  apply ((measure_mono hsub).trans (measure_union_le _ _)).trans
  apply (add_le_add le_rfl ((measure_union_le _ _).trans (add_le_add hhalf hweight))).trans_eq
  exact (add_assoc _ _ _).symm

end Riesz2.InterpolantLocalLaws
