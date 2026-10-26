/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.TwoVolumeComparisonPart2
public import Riesz2.Thermodynamic.TwoVolumeComparisonPart3
public import Riesz2.Thermodynamic.CompatibleComparisonFinal
public import Riesz2.ToMathlib.CommonMarginalComparison

/-!
# Composition bridges for the two-volume comparison

Physical endpoint identification and the common-length exterior law for Proposition 6.6,
with the middle-half support.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace Riesz2.TwoVolumeComparison

/-- See Proposition 6.6 of the paper: the endpoint law in the compatible
comparison is exactly the existing physical active conditional kernel.
The equality uses the whole physical energy on the positive simplex. -/
theorem physical_endpoint_expectation (p : Parameters) (d a : ℕ) (hd : 1 ≤ d)
    (θ : PhysicalCutoff) (ε L : ℝ)
    (y : AffineSimplex.chartDomain d ((d+a : ℕ)+1))
    (hyL : ((d+a : ℕ)+1 : ℝ) - ∑ i, y.val i = L)
    (Ky : EuclideanSpace ℝ (Fin (a+1)) → ℝ)
    (hKy : ∀ u (hu : RetainedSimplex.assemble d a
      (InterpolatingDensities.exteriorPermutation d a) y.val u ∈
        gapAmbientDomain (d+a).succPNat),
      Ky u = physicalAmbientGapEnergy p (d+a).succPNat
        ⟨RetainedSimplex.assemble d a
          (InterpolatingDensities.exteriorPermutation d a) y.val u, hu⟩)
    (G : BlockObservable a.succPNat) :
    let σ := (AffineSimplex.simplexVolume a L).comap Subtype.val
    let P := fun u : AffineSimplex.massSimplex a L =>
      ∑ i, (θ.val ((a+1 : ℝ)^(-ε)*u.val i) +
        θ.val ((a+1 : ℝ)^(-ε)*(u.val i)⁻¹))
    let w := fun u : AffineSimplex.massSimplex a L =>
      ENNReal.ofReal (Real.exp (-(p.val.1*(P u+Ky u.val))))
    ∀ (h0 : (∫⁻ u, w u ∂σ) ≠ 0) (ht : (∫⁻ u, w u ∂σ) ≠ ⊤),
      (∫ u, G.val (WithLp.ofLp u) ∂InterpolatingDensities.simplexFibreKernel
        p d a hd (InterpolatingDensities.exteriorPermutation d a) θ
        (Real.rpow_pos_of_pos (show (0 : ℝ) < (a+1 : ℕ) by positivity) (-ε))
        (Finset.univ.map (Fin.castLEEmb (show a+1 ≤ d+a+1 by omega))) true y) =
      ∫ u, G.val (WithLp.ofLp u.val) ∂AffineFibre.normalizedMeasure σ w h0 ht := by
  intro σ P w h0 ht
  obtain ⟨_, _, h00, htt, he⟩ := InterpolantLocalLaws.physical_endpoint_on_simplex
    p d a hd θ ε L y (by linarith only [hyL])
  simp_rw [← hKy] at he
  have he' : InterpolatingDensities.simplexFibreKernel p d a hd
      (InterpolatingDensities.exteriorPermutation d a) θ
      (Real.rpow_pos_of_pos (show (0 : ℝ) < (a+1 : ℕ) by positivity) (-ε))
      (Finset.univ.map (Fin.castLEEmb (show a+1 ≤ d+a+1 by omega))) true y =
      (AffineFibre.normalizedMeasure σ w h0 ht).map Subtype.val := by
    simpa only [σ, P, w, Nat.cast_add, Nat.cast_one, neg_mul] using he
  rw [he']
  exact integral_map measurable_subtype_coe.aemeasurable
    (G.property.choose_spec.continuous.measurable.comp
      (WithLp.measurable_ofLp 2 _)).aestronglyMeasurable

/-- See Proposition 6.6 of the paper: the complete fixed-exterior
comparison, transported to the literal conditional kernels used by Bayes.
No endpoint energy or conditional expectation identity remains an input. -/
theorem physical_conditional_comparison
    (hz : External.PeriodicZeta) (hRig : External.LongRangeRigidityLocallyUniform)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ A K ε₀ κ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧ 0 < κ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
    ∀ a d e : ℕ, 1 ≤ a → 4*(a+1) ≤ d+1+a+1 → d ≤ e →
      (a+1 : ℝ)^(2/s) ≤ (d+1+a+1 : ℝ) →
    ∀ (L : ℝ), 0 < L →
    ∀ (y : AffineSimplex.chartDomain (d+1) ((d+1+a : ℕ)+1))
      (z : AffineSimplex.chartDomain (e+1) ((e+1+a : ℕ)+1)),
      InterpolantLocalLaws.admissibleExterior p (d+1) a (by omega) θ ε A K y →
      InterpolantLocalLaws.admissibleExterior p (e+1) a (by omega) θ ε A K z →
      ((d+1+a : ℕ)+1 : ℝ)-∑ i, y.val i = L →
      ((e+1+a : ℕ)+1 : ℝ)-∑ i, z.val i = L →
    ∀ (R : ℕ), R ≤ (a+1)/4 → ((a+1)%4 ≠ 1 ∨ R < (a+1)/4) →
    ∀ G : BlockObservable a.succPNat,
      DependsOnBlockCoordinates G (symmetricMiddleBlock a.succPNat R) →
    let ky := InterpolatingDensities.simplexFibreKernel p (d+1) a (by omega)
      (InterpolatingDensities.exteriorPermutation (d+1) a) θ
      (Real.rpow_pos_of_pos (show (0 : ℝ) < (a+1 : ℕ) by positivity) (-ε))
      (Finset.univ.map (Fin.castLEEmb (show a+1 ≤ d+1+a+1 by omega))) true
    let kz := InterpolatingDensities.simplexFibreKernel p (e+1) a (by omega)
      (InterpolatingDensities.exteriorPermutation (e+1) a) θ
      (Real.rpow_pos_of_pos (show (0 : ℝ) < (a+1 : ℕ) by positivity) (-ε))
      (Finset.univ.map (Fin.castLEEmb (show a+1 ≤ e+1+a+1 by omega))) true
    |(∫ u, G.val (WithLp.ofLp u) ∂ky y) -
        ∫ u, G.val (WithLp.ofLp u) ∂kz z| ≤
      C*(a+1 : ℝ)^(κ*ε-min s 1/2)*
        (restrictedBlockDerivativeNorm G (symmetricMiddleBlock a.succPNat R)
          (goodBlockEvent s a.succPNat (d+1+a).succPNat (K*ε)) +
          Real.exp (-c*(a+1 : ℝ)^δ)*blockDerivativeNorm G) := by
  obtain ⟨A,K,ε₀,κ,hA,hK,hε₀,hκ,hcomp⟩ :=
    CompatibleComparison.compatible_conditional_comparison hz hRig s hs hs1
  refine ⟨A,K,ε₀,κ,hA,hK,hε₀,hκ,fun ε hε hsmall => ?_⟩
  obtain ⟨δ,hδ,_,hcomp⟩ := hcomp ε hε hsmall
  refine ⟨δ,hδ,fun βlo βhi hlo hle θ => ?_⟩
  obtain ⟨C,c,hC,hc,hcomp⟩ := hcomp βlo βhi hlo hle θ
  refine ⟨C,c,hC,hc,fun p hps hpl hph a d e ha h4 hde hpow L hL y z hy hz hyL hzL
    R hR hround G hG => ?_⟩
  obtain ⟨_,Ky,Kz,hKy,hKz,h00,h0t,h10,h1t,hbound⟩ :=
    hcomp p hps hpl hph a d e ha h4 hde hpow L hL y z hy hz hyL hzL
  have hh := (hbound G (symmetricMiddleBlock a.succPNat R) hG
    (fun i hi => by
      simpa only [Nat.succPNat_coe, Nat.cast_succ] using
        symmetricMiddleBlock_middle_half a.succPNat R hR hround i hi)).2.2
  dsimp only
  rw [physical_endpoint_expectation p (d+1) a (by omega) θ ε L y hyL Ky hKy G h00 h0t,
    physical_endpoint_expectation p (e+1) a (by omega) θ ε L z hzL Kz hKz G h10 h1t]
  exact hh

/-- See Proposition 6.6 of the paper: a real common length law dominated
by both original laws pulls back to a probability on the smaller carrier.
Its image in the larger carrier has the corresponding domination bound.
This does not discard the part of the larger original law above the smaller
volume. -/
theorem common_length_carrier (p : Parameters) (n m m' : ℕ) (hmm' : m ≤ m')
    (θ : PhysicalCutoff) (ε : ℝ) (ρR : Measure ℝ) [IsProbabilityMeasure ρR]
    (b : ℝ≥0∞)
    (hleft : ρR ≤ b • (LengthAveragingFibres.lengthMeasure p n m θ ε).map Subtype.val)
    (hright : ρR ≤ b • (LengthAveragingFibres.lengthMeasure p n m' θ ε).map Subtype.val) :
    let ρ := ρR.comap (Subtype.val : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ) → ℝ)
    IsProbabilityMeasure ρ ∧ ρ.map Subtype.val = ρR ∧
      ρ ≤ b • LengthAveragingFibres.lengthMeasure p n m θ ε ∧
      ρ.map (largerLength n m m' hmm') ≤ b • LengthAveragingFibres.lengthMeasure p n m' θ ε ∧
      (ρ.map (largerLength n m m' hmm')).map Subtype.val = ρR := by
  intro ρ
  let emb := MeasurableEmbedding.subtype_coe
    (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ)))
  let emb' := MeasurableEmbedding.subtype_coe
    (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) ((n+1+m' : ℕ)+1 : ℝ)))
  have hs : ∀ᵐ x ∂ρR, x ∈ Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ) := by
    apply (Measure.absolutelyContinuous_of_le_smul hleft).ae_le
    exact emb.ae_map_iff.mpr (ae_of_all _ fun x => x.property)
  have hmap : ρ.map Subtype.val = ρR := by
    rw [show ρ = ρR.comap Subtype.val from rfl, map_comap_subtype_coe measurableSet_Ioo]
    exact Measure.restrict_eq_self_of_ae_mem hs
  have hp : IsProbabilityMeasure ρ := by
    have : IsProbabilityMeasure (ρ.map (Subtype.val : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ) → ℝ)) :=
      hmap.symm ▸ inferInstance
    exact Measure.isProbabilityMeasure_of_map measurable_subtype_coe.aemeasurable
  have hmap' : (ρ.map (largerLength n m m' hmm')).map Subtype.val = ρR := by
    rw [Measure.map_map measurable_subtype_coe (measurable_largerLength n m m' hmm')]
    exact hmap
  have he : ρ.map (largerLength n m m' hmm') = ρR.comap Subtype.val := by
    rw [← hmap', emb'.comap_map]
  refine ⟨hp,hmap,TwoLawComparison.comap_le_of_le_map emb ρR _ b hleft,?_,hmap'⟩
  rw [he]
  exact TwoLawComparison.comap_le_of_le_map emb' ρR _ b hright

/-- See Proposition 6.6 of the paper: mixing the larger exterior kernel
pulled back to the smaller length interval is exactly mixing it against
the image length law. -/
theorem charted_larger_comp (p : Parameters) (n m m' : ℕ) (hmm' : m ≤ m')
    (θ : PhysicalCutoff) (ε : ℝ)
    (ρ : Measure (Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ))) :
    ((chartedExteriorKernel p n m' θ ε).comap
      (largerLength n m m' hmm') (measurable_largerLength n m m' hmm')) ∘ₘ ρ =
      chartedExteriorKernel p n m' θ ε ∘ₘ (ρ.map (largerLength n m m' hmm')) := by
  apply Measure.ext
  intro E hE
  rw [Measure.bind_apply hE (Kernel.aemeasurable _),
    Measure.bind_apply hE (Kernel.aemeasurable _)]
  simp only [Kernel.comap_apply]
  exact (lintegral_map ((chartedExteriorKernel p n m' θ ε).measurable_coe hE)
    (measurable_largerLength n m m' hmm')).symm

/-- See Proposition 6.6 of the paper: domination of each common-base
marginal by the actual original physical exterior law, on its own carrier. -/
theorem physical_common_marginals (p : Parameters) (n m m' : ℕ) (hmm' : m ≤ m')
    (θ : PhysicalCutoff) (ε : ℝ)
    (ρ : Measure (Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ)))
    (b : ℝ≥0∞)
    (hleft : ρ ≤ b • LengthAveragingFibres.lengthMeasure p n m θ ε)
    (hright : ρ.map (largerLength n m m' hmm') ≤ b • LengthAveragingFibres.lengthMeasure p n m' θ ε) :
    let κ := chartedExteriorKernel p n m θ ε
    let η := (chartedExteriorKernel p n m' θ ε).comap
      (largerLength n m m' hmm') (measurable_largerLength n m m' hmm')
    let π := CommonBaseKernel.law κ η ρ
    π.fst ≤ b • InterpolantLocalLaws.physicalExteriorLaw p (m+1) n θ ε ∧
      π.snd ≤ b • InterpolantLocalLaws.physicalExteriorLaw p (m'+1) n θ ε := by
  intro κ η π
  constructor
  · rw [CommonBaseKernel.fst_law]
    exact (CommonBaseKernel.comp_le_smul κ ρ _ b hleft).trans_eq
      (congrArg (fun μ => b • μ) (chartedExteriorKernel_comp_lengthMeasure p n m θ ε))
  · rw [CommonBaseKernel.snd_law, charted_larger_comp]
    exact (CommonBaseKernel.comp_le_smul (chartedExteriorKernel p n m' θ ε) _ _ b hright).trans_eq
      (congrArg (fun μ => b • μ) (chartedExteriorKernel_comp_lengthMeasure p n m' θ ε))

/-- See Proposition 6.6 of the paper: the charted common-base product
is supported on pairs with exactly the same positive residual length. -/
theorem physical_common_compatible (p : Parameters) (n m m' : ℕ) (hmm' : m ≤ m')
    (θ : PhysicalCutoff) (ε : ℝ)
    (ρ : Measure (Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ))) :
    let κ := chartedExteriorKernel p n m θ ε
    let η := (chartedExteriorKernel p n m' θ ε).comap
      (largerLength n m m' hmm') (measurable_largerLength n m m' hmm')
    ∀ᵐ q ∂CommonBaseKernel.law κ η ρ,
      (exteriorLength n m q.1).val = (exteriorLength n m' q.2).val := by
  intro κ η
  have hE : MeasurableSet {q :
      AffineSimplex.chartDomain (m+1) ((m+1+n : ℕ)+1) ×
        AffineSimplex.chartDomain (m'+1) ((m'+1+n : ℕ)+1) |
      (exteriorLength n m q.1).val = (exteriorLength n m' q.2).val} :=
    measurableSet_eq_fun
      (measurable_subtype_coe.comp ((measurable_exteriorLength n m).comp measurable_fst))
      (measurable_subtype_coe.comp ((measurable_exteriorLength n m').comp measurable_snd))
  apply Measure.ae_comp_of_ae_ae hE
  apply ae_of_all
  intro L
  rw [Kernel.prod_apply, Kernel.comap_apply]
  apply (Measure.ae_prod_iff_ae_ae hE).mpr
  filter_upwards [exteriorLength_ae p n m θ ε L] with y hy
  filter_upwards [exteriorLength_ae p n m' θ ε (largerLength n m m' hmm' L)] with z hz
  exact (congrArg Subtype.val hy).trans (congrArg Subtype.val hz).symm

section BayesComposition

set_option quotPrecheck false

variable (p : Parameters) (n m m' : ℕ) (hmm' : m ≤ m')
    (θ : PhysicalCutoff) (ε : ℝ)

local notation "I" => Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ)
local notation "D" => AffineSimplex.chartDomain (m+1) ((m+1+n : ℕ)+1)
local notation "D'" => AffineSimplex.chartDomain (m'+1) ((m'+1+n : ℕ)+1)
local notation "κ" => chartedExteriorKernel p n m θ ε
local notation "η" => (chartedExteriorKernel p n m' θ ε).comap
  (largerLength n m m' hmm') (measurable_largerLength n m m' hmm')
local notation "ky" => InterpolatingDensities.simplexFibreKernel p (m+1) n (Nat.succ_pos m)
  (InterpolatingDensities.exteriorPermutation (m+1) n) θ
  (Real.rpow_pos_of_pos (show (0 : ℝ) < (n+1 : ℕ) by positivity) (-ε))
  (Finset.univ.map (Fin.castLEEmb (Nat.add_le_add_right (Nat.le_add_left n (m+1)) 1))) true
local notation "kz" => InterpolatingDensities.simplexFibreKernel p (m'+1) n (Nat.succ_pos m')
  (InterpolatingDensities.exteriorPermutation (m'+1) n) θ
  (Real.rpow_pos_of_pos (show (0 : ℝ) < (n+1 : ℕ) by positivity) (-ε))
  (Finset.univ.map (Fin.castLEEmb (Nat.add_le_add_right (Nat.le_add_left n (m'+1)) 1))) true

/-- See Proposition 6.6 of the paper: Bayes for both marginals of the
actual common-length product, including integrability, on unequal length
carriers. The right side uses the same real length variable for both laws. -/
theorem physical_common_bayes (ρ : Measure I) [IsProbabilityMeasure ρ]
    (b : ℝ≥0∞)
    (hleft : ρ ≤ b • LengthAveragingFibres.lengthMeasure p n m θ ε)
    (hright : ρ.map (largerLength n m m' hmm') ≤ b • LengthAveragingFibres.lengthMeasure p n m' θ ε)
    (G : BlockObservable n.succPNat) :
    let F := fun y : D => ∫ u, G.val (WithLp.ofLp u) ∂ky y
    let H := fun z : D' => ∫ u, G.val (WithLp.ofLp u) ∂kz z
    let π := CommonBaseKernel.law κ η ρ
    Integrable (fun q => F q.1) π ∧ Integrable (fun q => H q.2) π ∧
      (∫ q, F q.1 ∂π) - (∫ q, H q.2 ∂π) =
        (∫ L, LengthOverlap.realAveragedObservable p n m θ ε G L.val ∂ρ) -
        (∫ L, LengthOverlap.realAveragedObservable p n m' θ ε G L.val ∂ρ) := by
  intro F H π
  have hg : Measurable (fun u : EuclideanSpace ℝ (Fin (n+1)) => G.val (WithLp.ofLp u)) :=
    G.property.choose_spec.continuous.measurable.comp (WithLp.measurable_ofLp 2 _)
  have hF : Measurable F := hg.stronglyMeasurable.integral_kernel.measurable
  have hH : Measurable H := hg.stronglyMeasurable.integral_kernel.measurable
  obtain ⟨hiF,_,hbayesF⟩ := bayes_dominated_common p n m θ ε G ρ b hleft
  obtain ⟨hiH,_,hbayesH⟩ := bayes_dominated_common p n m' θ ε G
    (ρ.map (largerLength n m m' hmm')) b hright
  have hfmap : π.map Prod.fst = κ ∘ₘ ρ := CommonBaseKernel.fst_law κ η ρ
  have hhmap : π.map Prod.snd = chartedExteriorKernel p n m' θ ε ∘ₘ
      ρ.map (largerLength n m m' hmm') :=
    (CommonBaseKernel.snd_law κ η ρ).trans (charted_larger_comp p n m m' hmm' θ ε ρ)
  have hiF' : Integrable F (π.map Prod.fst) := hfmap.symm ▸ hiF
  have hiH' : Integrable H (π.map Prod.snd) := hhmap.symm ▸ hiH
  refine ⟨(integrable_map_measure hF.aestronglyMeasurable measurable_fst.aemeasurable).mp hiF',
    (integrable_map_measure hH.aestronglyMeasurable measurable_snd.aemeasurable).mp hiH', ?_⟩
  have heF : (∫ q, F q.1 ∂π) =
      ∫ L, LengthOverlap.realAveragedObservable p n m θ ε G L.val ∂ρ := by
    rw [← integral_map measurable_fst.aemeasurable hF.aestronglyMeasurable, hfmap, hbayesF]
    exact integral_congr_ae (ae_of_all _ fun L => (LengthOverlap.realAveragedObservable_apply p n m θ ε G L).symm)
  have heH : (∫ q, H q.2 ∂π) =
      ∫ L, LengthOverlap.realAveragedObservable p n m' θ ε G L.val ∂ρ := by
    rw [← integral_map measurable_snd.aemeasurable hH.aestronglyMeasurable, hhmap, hbayesH]
    have he := integral_map (μ := ρ) (measurable_largerLength n m m' hmm').aemeasurable
      (LengthDerivative.measurable_averagedObservable p n m' θ ε G).aestronglyMeasurable
    rw [he]
    exact integral_congr_ae (ae_of_all _ fun L =>
      (LengthOverlap.realAveragedObservable_apply p n m' θ ε G (largerLength n m m' hmm' L)).symm)
  rw [heF,heH]

/-- See Proposition 6.6 of the paper: subtracting the same constant before
conditional integration agrees at every exterior with centering the actual
conditional expectation. -/
theorem centered_physical_average (G : BlockObservable n.succPNat) (y : D) :
    (∫ u, G.val (WithLp.ofLp u)-G.val (fun _ => 1) ∂ky y) =
      (∫ u, G.val (WithLp.ofLp u) ∂ky y)-G.val (fun _ => 1) := by
  have hi : Integrable (fun u : EuclideanSpace ℝ (Fin (n+1)) => G.val (WithLp.ofLp u)) (ky y) :=
    (fixed_exterior_average_bound p n m θ ε G y).1
  rw [integral_sub hi (integrable_const _)]
  simp only [integral_const, probReal_univ, one_smul]

/-- See Proposition 6.6 of the paper: quantitative common-length comparison
from the actual physical conditional estimate and the two original exterior
tails. This is an internal implication. Moment and tail estimates are explicit
inputs, and the physical coupling and Bayes identities are proved here. -/
theorem physical_common_comparison_internal (ρ : Measure I) [IsProbabilityMeasure ρ]
    (b H T₁ T₂ P A K : ℝ) (hb : 0 ≤ b) (hH : 0 ≤ H) (hP : 0 ≤ P)
    (hleft : ρ ≤ ENNReal.ofReal b • LengthAveragingFibres.lengthMeasure p n m θ ε)
    (hright : ρ.map (largerLength n m m' hmm') ≤
      ENNReal.ofReal b • LengthAveragingFibres.lengthMeasure p n m' θ ε)
    (G : BlockObservable n.succPNat)
    (hmF : (∫⁻ y : D, ENNReal.ofReal
      ((∫ u, G.val (WithLp.ofLp u)-G.val (fun _ => 1) ∂ky y)^2)
      ∂InterpolantLocalLaws.physicalExteriorLaw p (m+1) n θ ε) ≤
        ENNReal.ofReal (H*blockDerivativeNorm G^2))
    (hmH : (∫⁻ z : D', ENNReal.ofReal
      ((∫ u, G.val (WithLp.ofLp u)-G.val (fun _ => 1) ∂kz z)^2)
      ∂InterpolantLocalLaws.physicalExteriorLaw p (m'+1) n θ ε) ≤
        ENNReal.ofReal (H*blockDerivativeNorm G^2))
    (hT₁ : (InterpolantLocalLaws.physicalExteriorLaw p (m+1) n θ ε)
      {y | ¬ InterpolantLocalLaws.admissibleExterior p (m+1) n (Nat.succ_pos m) θ ε A K y} ≤
        ENNReal.ofReal T₁)
    (hT₂ : (InterpolantLocalLaws.physicalExteriorLaw p (m'+1) n θ ε)
      {z | ¬ InterpolantLocalLaws.admissibleExterior p (m'+1) n (Nat.succ_pos m') θ ε A K z} ≤
        ENNReal.ofReal T₂)
    (hfixed : ∀ (y : D) (z : D'),
      InterpolantLocalLaws.admissibleExterior p (m+1) n (Nat.succ_pos m) θ ε A K y →
      InterpolantLocalLaws.admissibleExterior p (m'+1) n (Nat.succ_pos m') θ ε A K z →
      (exteriorLength n m y).val = (exteriorLength n m' z).val →
      |(∫ u, G.val (WithLp.ofLp u) ∂ky y) -
        ∫ u, G.val (WithLp.ofLp u) ∂kz z| ≤ P) :
    |(∫ L, LengthOverlap.realAveragedObservable p n m θ ε G L.val ∂ρ) -
        ∫ L, LengthOverlap.realAveragedObservable p n m' θ ε G L.val ∂ρ| ≤
      P + (Real.sqrt (b*(H*blockDerivativeNorm G^2)) +
        Real.sqrt (b*(H*blockDerivativeNorm G^2)))*
        Real.sqrt (b*(max T₁ 0+max T₂ 0)) := by
  let F := fun y : D => ∫ u, G.val (WithLp.ofLp u)-G.val (fun _ => 1) ∂ky y
  let H' := fun z : D' => ∫ u, G.val (WithLp.ofLp u)-G.val (fun _ => 1) ∂kz z
  have hg : Measurable (fun u : EuclideanSpace ℝ (Fin (n+1)) =>
      G.val (WithLp.ofLp u)-G.val (fun _ => 1)) :=
    (G.property.choose_spec.continuous.measurable.comp (WithLp.measurable_ofLp 2 _)).sub_const _
  have hF : Measurable F := hg.stronglyMeasurable.integral_kernel.measurable
  have hH' : Measurable H' := hg.stronglyMeasurable.integral_kernel.measurable
  let π := CommonBaseKernel.law κ η ρ
  obtain ⟨hμ,hν⟩ := physical_common_marginals p n m m' hmm' θ ε ρ (ENNReal.ofReal b) hleft hright
  let E := {y : D | ¬ InterpolantLocalLaws.admissibleExterior p (m+1) n (Nat.succ_pos m) θ ε A K y}
  let E' := {z : D' | ¬ InterpolantLocalLaws.admissibleExterior p (m'+1) n (Nat.succ_pos m') θ ε A K z}
  have hE : MeasurableSet E :=
    (InterpolantLocalLaws.measurableSet_admissibleExterior p (m+1) n (Nat.succ_pos m) θ ε A K).compl
  have hE' : MeasurableSet E' :=
    (InterpolantLocalLaws.measurableSet_admissibleExterior p (m'+1) n (Nat.succ_pos m') θ ε A K).compl
  have hgood : ∀ᵐ q ∂π.restrict ((Prod.fst ⁻¹' E) ∪ (Prod.snd ⁻¹' E'))ᶜ,
      |F q.1-H' q.2| ≤ P := by
    filter_upwards [ae_restrict_of_ae (physical_common_compatible p n m m' hmm' θ ε ρ),
      ae_restrict_mem ((hE.preimage measurable_fst).union (hE'.preimage measurable_snd)).compl]
      with q hq hgood
    have hy : InterpolantLocalLaws.admissibleExterior p (m+1) n (Nat.succ_pos m) θ ε A K q.1 := by
      have : q.1 ∉ E := fun hy => hgood (Or.inl hy)
      simpa only [E, mem_ofPred_eq, not_not] using this
    have hz : InterpolantLocalLaws.admissibleExterior p (m'+1) n (Nat.succ_pos m') θ ε A K q.2 := by
      have : q.2 ∉ E' := fun hz => hgood (Or.inr hz)
      simpa only [E', mem_ofPred_eq, not_not] using this
    dsimp only [F,H']
    rw [centered_physical_average, centered_physical_average]
    simpa only [sub_sub_sub_cancel_right] using hfixed q.1 q.2 hy hz hq
  have hbound := TwoLawComparison.comparison_of_marginals π
    (InterpolantLocalLaws.physicalExteriorLaw p (m+1) n θ ε)
    (InterpolantLocalLaws.physicalExteriorLaw p (m'+1) n θ ε)
    hb (mul_nonneg hH (sq_nonneg _)) (mul_nonneg hH (sq_nonneg _)) hP
    hμ hν F H' hF hH' hmF hmH E E' hE hE' hT₁ hT₂ hgood
  obtain ⟨hiF,hiH,he⟩ := physical_common_bayes p n m m' hmm' θ ε ρ (ENNReal.ofReal b) hleft hright G
  have hiC : Integrable (fun _q : D × D' => G.val (fun _ => 1)) π := integrable_const _
  have heF : (∫ q, F q.1 ∂π) = (∫ q, ∫ u, G.val (WithLp.ofLp u) ∂ky q.1 ∂π)-G.val (fun _ => 1) := by
    simp_rw [F, centered_physical_average]
    rw [integral_sub hiF hiC, integral_const, probReal_univ, one_smul]
  have heH : (∫ q, H' q.2 ∂π) = (∫ q, ∫ u, G.val (WithLp.ofLp u) ∂kz q.2 ∂π)-G.val (fun _ => 1) := by
    simp_rw [H', centered_physical_average]
    rw [integral_sub hiH hiC, integral_const, probReal_univ, one_smul]
  rw [heF,heH,sub_sub_sub_cancel_right,he] at hbound
  exact hbound

end BayesComposition

/-- See Proposition 6.6 of the paper: the fixed-exterior estimate is
integrated over the actual common-length coupling with the physical
second moments supplied. Only the original exterior bad-event masses remain
as quantitative inputs to this internal interface. All structural constants
and the positive tail power keep their original quantifier order. -/
theorem integrated_physical_comparison_internal
    (hz : External.PeriodicZeta) (hRig : External.LongRangeRigidityLocallyUniform)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ A K ε₀ κ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧ 0 < κ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ C c H : ℝ, 0 < C ∧ 0 < c ∧ 0 < H ∧
    ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
    ∀ n m m' : ℕ, 1 ≤ n → 4*(n+1) ≤ m+1+n+1 → ∀ (hmm' : m ≤ m'),
      (n+1 : ℝ)^(2/s) ≤ (m+1+n+1 : ℝ) →
    ∀ (ρ : Measure (Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ))), IsProbabilityMeasure ρ →
    ∀ b : ℝ, 0 ≤ b →
      ρ ≤ ENNReal.ofReal b • LengthAveragingFibres.lengthMeasure p n m θ ε →
      ρ.map (largerLength n m m' hmm') ≤
        ENNReal.ofReal b • LengthAveragingFibres.lengthMeasure p n m' θ ε →
    ∀ T₁ T₂ : ℝ,
      (InterpolantLocalLaws.physicalExteriorLaw p (m+1) n θ ε)
        {y | ¬ InterpolantLocalLaws.admissibleExterior p (m+1) n (by omega) θ ε A K y} ≤
          ENNReal.ofReal T₁ →
      (InterpolantLocalLaws.physicalExteriorLaw p (m'+1) n θ ε)
        {z | ¬ InterpolantLocalLaws.admissibleExterior p (m'+1) n (by omega) θ ε A K z} ≤
          ENNReal.ofReal T₂ →
    ∀ R : ℕ, R ≤ (n+1)/4 → ((n+1)%4 ≠ 1 ∨ R < (n+1)/4) →
    ∀ G : BlockObservable n.succPNat,
      DependsOnBlockCoordinates G (symmetricMiddleBlock n.succPNat R) →
    |(∫ L, LengthOverlap.realAveragedObservable p n m θ ε G L.val ∂ρ) -
        ∫ L, LengthOverlap.realAveragedObservable p n m' θ ε G L.val ∂ρ| ≤
      C*(n+1 : ℝ)^(κ*ε-min s 1/2)*
        (restrictedBlockDerivativeNorm G (symmetricMiddleBlock n.succPNat R)
          (goodBlockEvent s n.succPNat (m+1+n).succPNat (K*ε)) +
          Real.exp (-c*(n+1 : ℝ)^δ)*blockDerivativeNorm G) +
      (Real.sqrt (b*(H*blockDerivativeNorm G^2)) +
        Real.sqrt (b*(H*blockDerivativeNorm G^2)))*
        Real.sqrt (b*(max T₁ 0+max T₂ 0)) := by
  obtain ⟨A,K,ε₀,κ,hA,hK,hε₀,hκ,hcomp⟩ := physical_conditional_comparison hz hRig s hs hs1
  refine ⟨A,K,ε₀,κ,hA,hK,hε₀,hκ,fun ε hε hsmall => ?_⟩
  obtain ⟨δ,hδ,hcomp⟩ := hcomp ε hε hsmall
  refine ⟨δ,hδ,fun βlo βhi hlo hle θ => ?_⟩
  obtain ⟨C,c,hC,hc,hcomp⟩ := hcomp βlo βhi hlo hle θ
  obtain ⟨H,hH,hm⟩ := compact_conditional_centered_second_moment
    s ε βlo βhi hs hs1 hε hlo hle θ
  refine ⟨C,c,H,hC,hc,hH,fun p hps hpl hph n m m' hn h4 hmm' hpow
    ρ hρ b hb hleft hright T₁ T₂ hT₁ hT₂ R hR hround G hG => ?_⟩
  have : IsProbabilityMeasure ρ := hρ
  have hmF := (hm p hps hpl hph (m+1) n (by omega) G).2
  have hmH := (hm p hps hpl hph (m'+1) n (by omega) G).2
  have hP : 0 ≤ C*(n+1 : ℝ)^(κ*ε-min s 1/2)*
      (restrictedBlockDerivativeNorm G (symmetricMiddleBlock n.succPNat R)
        (goodBlockEvent s n.succPNat (m+1+n).succPNat (K*ε)) +
        Real.exp (-c*(n+1 : ℝ)^δ)*blockDerivativeNorm G) := by
    have hD : 0 ≤ blockDerivativeNorm G := Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _
    have hA : 0 ≤ restrictedBlockDerivativeNorm G (symmetricMiddleBlock n.succPNat R)
        (goodBlockEvent s n.succPNat (m+1+n).succPNat (K*ε)) :=
      Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _
    positivity
  apply physical_common_comparison_internal p n m m' hmm' θ ε ρ b H T₁ T₂ _ A K hb hH.le hP
    hleft hright G hmF hmH hT₁ hT₂
  intro y z hy hz hres
  apply hcomp p hps hpl hph n m m' hn h4 hmm' hpow
    (exteriorLength n m y).val (exteriorLength n m y).property.1 y z hy hz rfl hres.symm
    R hR hround G hG

/-- See Proposition 6.6 of the paper: instantiate the common carrier with
the literal normalized minimum of the physical length densities. Both
measure domination bounds and the two real-mean transport identities are
conclusions. The only positivity premise is the actual overlap mass. -/
theorem overlap_common_carrier (p : Parameters) (n m m' : ℕ) (hmm' : m ≤ m')
    (θ : PhysicalCutoff) (ε : ℝ) :
    let f := LengthOverlap.realLengthDensity p n m θ ε
    let f' := LengthOverlap.realLengthDensity p n m' θ ε
    let a₀ := DensityOverlap.mass volume f f'
    0 < a₀ →
    let μρ := volume.withDensity (fun L => ENNReal.ofReal (min (f L) (f' L)/a₀))
    let ρ := μρ.comap (Subtype.val : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ) → ℝ)
    IsProbabilityMeasure ρ ∧ ρ.map Subtype.val = μρ ∧
      ρ ≤ ENNReal.ofReal a₀⁻¹ • LengthAveragingFibres.lengthMeasure p n m θ ε ∧
      ρ.map (largerLength n m m' hmm') ≤
        ENNReal.ofReal a₀⁻¹ • LengthAveragingFibres.lengthMeasure p n m' θ ε ∧
      ∀ G : BlockObservable n.succPNat,
        (∫ L, LengthOverlap.realAveragedObservable p n m θ ε G L.val ∂ρ) =
          (∫ L, LengthOverlap.realAveragedObservable p n m θ ε G L ∂μρ) ∧
        (∫ L, LengthOverlap.realAveragedObservable p n m' θ ε G L.val ∂ρ) =
          ∫ L, LengthOverlap.realAveragedObservable p n m' θ ε G L ∂μρ := by
  intro f f' a₀ ha₀ μρ ρ
  have hf := LengthOverlap.realLengthDensity_measurable p n m θ ε
  have hf' := LengthOverlap.realLengthDensity_measurable p n m' θ ε
  have hfi := (LengthOverlap.realLengthDensity_integral p n m θ ε).1
  have hfi' := (LengthOverlap.realLengthDensity_integral p n m' θ ε).1
  have hp : IsProbabilityMeasure μρ := DensityOverlap.probability volume hfi hfi' hf.2 hf'.2 ha₀
  have hl : μρ ≤ ENNReal.ofReal a₀⁻¹ •
      (LengthAveragingFibres.lengthMeasure p n m θ ε).map Subtype.val := by
    rw [LengthAveragingFibres.lengthMeasure_map, ← LengthOverlap.realLengthDensity_law]
    exact DensityOverlap.measure_le_left volume hf.1 hf'.1 ha₀
  have hr : μρ ≤ ENNReal.ofReal a₀⁻¹ •
      (LengthAveragingFibres.lengthMeasure p n m' θ ε).map Subtype.val := by
    rw [LengthAveragingFibres.lengthMeasure_map, ← LengthOverlap.realLengthDensity_law]
    have hm : DensityOverlap.mass volume f' f = a₀ := by
      change (∫ x, min (f' x) (f x)) = ∫ x, min (f x) (f' x)
      exact integral_congr_ae (ae_of_all _ fun x => min_comm _ _)
    have hh := DensityOverlap.measure_le_left volume (f := f') (g := f) hf'.1 hf.1 (hm.symm ▸ ha₀)
    simp only [DensityOverlap.density, hm] at hh
    simpa only [μρ, min_comm] using hh
  obtain ⟨hρ,hmap,hleft,hright,_⟩ :=
    common_length_carrier p n m m' hmm' θ ε μρ (ENNReal.ofReal a₀⁻¹) hl hr
  refine ⟨hρ,hmap,hleft,hright,fun G => ?_⟩
  constructor
  · rw [← hmap]
    exact (integral_map measurable_subtype_coe.aemeasurable
      (LengthOverlap.realAveragedObservable_measurable p n m θ ε G).aestronglyMeasurable).symm
  · rw [← hmap]
    exact (integral_map measurable_subtype_coe.aemeasurable
      (LengthOverlap.realAveragedObservable_measurable p n m' θ ε G).aestronglyMeasurable).symm

/-- See Proposition 6.6 of the paper: the integrated fixed comparison for
the canonical overlap density, with the original second moments, both
Bayes identities and both carrier transports supplied. The remaining tail
premises refer to the very same admissibility constants as the comparison. They are not asserted for an independently chosen pair. -/
theorem overlap_integrated_comparison_internal
    (hz : External.PeriodicZeta) (hRig : External.LongRangeRigidityLocallyUniform)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) :
    ∃ A K ε₀ κ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧ 0 < κ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ C c H : ℝ, 0 < C ∧ 0 < c ∧ 0 < H ∧
    ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
    ∀ n m m' : ℕ, 1 ≤ n → 4*(n+1) ≤ m+1+n+1 → m ≤ m' →
      (n+1 : ℝ)^(2/s) ≤ (m+1+n+1 : ℝ) →
    let f := LengthOverlap.realLengthDensity p n m θ ε
    let f' := LengthOverlap.realLengthDensity p n m' θ ε
    let a₀ := DensityOverlap.mass volume f f'
    let μρ := volume.withDensity (fun L => ENNReal.ofReal (min (f L) (f' L)/a₀))
    0 < a₀ → ∀ T₁ T₂ : ℝ,
      (InterpolantLocalLaws.physicalExteriorLaw p (m+1) n θ ε)
        {y | ¬ InterpolantLocalLaws.admissibleExterior p (m+1) n (by omega) θ ε A K y} ≤
          ENNReal.ofReal T₁ →
      (InterpolantLocalLaws.physicalExteriorLaw p (m'+1) n θ ε)
        {z | ¬ InterpolantLocalLaws.admissibleExterior p (m'+1) n (by omega) θ ε A K z} ≤
          ENNReal.ofReal T₂ →
    ∀ R : ℕ, R ≤ (n+1)/4 → ((n+1)%4 ≠ 1 ∨ R < (n+1)/4) →
    ∀ G : BlockObservable n.succPNat,
      DependsOnBlockCoordinates G (symmetricMiddleBlock n.succPNat R) →
    |(∫ L, LengthOverlap.realAveragedObservable p n m θ ε G L ∂μρ) -
        ∫ L, LengthOverlap.realAveragedObservable p n m' θ ε G L ∂μρ| ≤
      C*(n+1 : ℝ)^(κ*ε-min s 1/2)*
        (restrictedBlockDerivativeNorm G (symmetricMiddleBlock n.succPNat R)
          (goodBlockEvent s n.succPNat (m+1+n).succPNat (K*ε)) +
          Real.exp (-c*(n+1 : ℝ)^δ)*blockDerivativeNorm G) +
      (Real.sqrt (a₀⁻¹*(H*blockDerivativeNorm G^2)) +
        Real.sqrt (a₀⁻¹*(H*blockDerivativeNorm G^2)))*
        Real.sqrt (a₀⁻¹*(max T₁ 0+max T₂ 0)) := by
  obtain ⟨A,K,ε₀,κ,hA,hK,hε₀,hκ,hcomp⟩ := integrated_physical_comparison_internal hz hRig s hs hs1
  refine ⟨A,K,ε₀,κ,hA,hK,hε₀,hκ,fun ε hε hsmall => ?_⟩
  obtain ⟨δ,hδ,hcomp⟩ := hcomp ε hε hsmall
  refine ⟨δ,hδ,fun βlo βhi hlo hle θ => ?_⟩
  obtain ⟨C,c,H,hC,hc,hH,hcomp⟩ := hcomp βlo βhi hlo hle θ
  refine ⟨C,c,H,hC,hc,hH,fun p hps hpl hph n m m' hn h4 hmm' hpow => ?_⟩
  intro f f' a₀ μρ ha₀ T₁ T₂ hT₁ hT₂ R hR hround G hG
  let ρ := μρ.comap (Subtype.val : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ) → ℝ)
  obtain ⟨hρ,_hmap,hleft,hright,hmeans⟩ := overlap_common_carrier p n m m' hmm' θ ε ha₀
  have hh := hcomp p hps hpl hph n m m' hn h4 hmm' hpow ρ hρ
    a₀⁻¹ (inv_nonneg.mpr ha₀.le) hleft hright T₁ T₂ hT₁ hT₂ R hR hround G hG
  rw [(hmeans G).1,(hmeans G).2] at hh
  exact hh

/-- See Lemma 6.5 and Proposition 6.6 of the paper: enlarging the good
set enlarges the restricted derivative sum. -/
theorem restricted_norm_mono {n : ℕ+} (G : BlockObservable n)
    (J : Finset (Fin (n : ℕ))) {E F : Set (Fin (n : ℕ) → ℝ)} (hEF : E ⊆ F) :
    restrictedBlockDerivativeNorm G J E ≤ restrictedBlockDerivativeNorm G J F := by
  unfold restrictedBlockDerivativeNorm
  apply Finset.sum_le_sum
  intro j _
  apply NNReal.coe_le_coe.mpr
  apply csInf_le (OrderBot.bddBelow _)
  intro x t hx ht
  exact CompatibleComparison.restricted_coordinate_bound_internal G F j x t (hEF hx) (hEF ht)

/-- See Proposition 6.6 of the paper: the overlap averaging tolerance and
the fixed-exterior comparison tolerance can share a larger good-set norm.
This concerns the observable norm only, not exterior admissibility. -/
theorem restricted_good_norm_mono {n N : ℕ+} (s : ℝ) (G : BlockObservable n)
    (J : Finset (Fin (n : ℕ))) {η ζ : ℝ} (hηζ : η ≤ ζ) :
    restrictedBlockDerivativeNorm G J (goodBlockEvent s n N η) ≤
      restrictedBlockDerivativeNorm G J (goodBlockEvent s n N ζ) :=
  restricted_norm_mono G J (CompatibleComparison.fine_event_mono_internal s n N hηζ)

end Riesz2.TwoVolumeComparison
