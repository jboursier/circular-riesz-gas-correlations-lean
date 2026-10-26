/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.JointAdmissibilityTime

/-!
# One choice for comparison and original typicality

Strengthened interfaces for Proposition 6.6: the same structural choice retains
original-law exterior typicality throughout the analytic chain.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal ContDiff Topology MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
open Riesz2.JointAdmissibility

namespace Riesz2.CompatibleComparison

open Riesz2.InterpolantLocalLaws

/-- See the proof of Proposition 6.6 in the paper: the analytic conclusion and original exterior
typicality use one choice of A,K. A may exceed a prescribed threshold. -/
theorem long_range_common_choice_internal_joint (hzeta : External.PeriodicZeta)
    (hRig : External.LongRangeRigidityLocallyUniform) (s : Riesz1.RieszExponent) :
    ∃ A K ε₀ κ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧ 0 < κ ∧
    OriginalTypicality s.val A K ε₀ ∧
    (∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ p : Parameters, p.val.2 = s.val → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
    ∀ d e m : ℕ, ∀ hd : 1 ≤ d, ∀ he : 1 ≤ e,
      1 ≤ m → 4*(m+1) ≤ d+m+1 → d ≤ e →
      (m+1 : ℝ)^(2/s.val) ≤ ((d+m : ℕ)+1 : ℝ) →
    let R := ENNReal.ofReal (C*Real.exp (-c*(m+1 : ℝ)^δ))
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
              WithLp.ofLp u ∉ goodBlockEvent s.val m.succPNat (d + m).succPNat (K * ε)},
            ENNReal.ofReal (exceptionalWeight s.val (n := m.succPNat) (WithLp.ofLp u)) ∂ν) ≤ R ∧
          (∀ i : Fin (m + 1),
            1 - R ≤ ν {u | ((m + 1 : ℕ) : ℝ) ^ (-(K * ε)) ≤ u i ∧
              u i ≤ ((m + 1 : ℕ) : ℝ) ^ (K * ε)}) ∧
          ∀ a b : ℕ, a < b → b ≤ m + 1 →
            ν {u | ((m + 1 : ℕ) : ℝ) ^ (K * ε) * (b - a : ℕ) ^ (min s.val 1 / 2) <
              |(∑ i ∈ Finset.univ.filter (fun i : Fin (m + 1) => a ≤ i.val ∧ i.val < b), u i) -
                (b - a : ℕ)|} ≤ R) ∧
    (∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (p : Parameters), p.val.2 = s.val → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
    ∀ a d e : ℕ, 1 ≤ a → 4*(a+1) ≤ d+1+a+1 → d ≤ e →
      (a+1 : ℝ)^(2/s.val) ≤ (d+1+a+1 : ℝ) →
    ∀ (L : ℝ), 0 < L →
    ∀ (y : AffineSimplex.chartDomain (d+1) ((d+1+a : ℕ)+1))
      (z : AffineSimplex.chartDomain (e+1) ((e+1+a : ℕ)+1)),
      InterpolantLocalLaws.admissibleExterior p (d+1) a (by omega) θ ε A K y →
      InterpolantLocalLaws.admissibleExterior p (e+1) a (by omega) θ ε A K z →
      ((d+1+a : ℕ)+1 : ℝ)-∑ i, y.val i = L →
      ((e+1+a : ℕ)+1 : ℝ)-∑ i, z.val i = L →
    ∀ (Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ),
      (∀ u (hu : RetainedSimplex.assemble (d+1) a
        (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u ∈
          gapAmbientDomain (d+1+a).succPNat),
        Ky u = physicalAmbientGapEnergy p (d+1+a).succPNat
          ⟨RetainedSimplex.assemble (d+1) a
            (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u,hu⟩) →
      (∀ u (hu : RetainedSimplex.assemble (e+1) a
        (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u ∈
          gapAmbientDomain (e+1+a).succPNat),
        Kz u = physicalAmbientGapEnergy p (e+1+a).succPNat
          ⟨RetainedSimplex.assemble (e+1) a
            (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u,hu⟩) →
    ∀ (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
    ∀ (frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
      (M : Matrix (Fin (a+1)) (Fin a) ℝ),
      (∀ v : Fin a → ℝ, M *ᵥ v = (frame.symm (WithLp.toLp 2 v)).val) →
    let Ω := AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L
    let U := frame '' Ω
    let g := fun x => AffineSimplex.centredChart a L (frame.symm x)
    let V := fun x => p.val.1*
      ((∑ i, (θ.val ((a+1 : ℝ)^(-ε)*g x i)+θ.val ((a+1 : ℝ)^(-ε)*(g x i)⁻¹)))+
        (1-t)*Ky (g x)+t*Kz (g x))
    let D := fun u => Ky u-Kz u
    let b := fun j x => InteractionDifferential.pinnedRepresentative (fun i : Fin a =>
      fderiv ℝ D (g x) (WithLp.toLp 2 (Pi.single i.castSucc 1-Pi.single i.succ 1))) j
    ∀ (μ : Measure (EuclideanSpace ℝ (Fin a)))
      (hV : IsEuclideanGibbsPotential volume μ U V),
    let hU := frame.toHomeomorph.isOpenMap Ω (ConditionalWellPosedness.fibre_isOpen a L)
    let hB := frame.isometry.lipschitzWith.isBounded_image
      (ConditionalWellPosedness.fibre_isBounded a L)
    (∫⁻ x in {x | WithLp.ofLp (g x) ∉
        goodBlockEvent s.val a.succPNat (d+1+a).succPNat (K*ε)},
      ENNReal.ofReal (InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s.val
        (WithLp.ofLp (g x))) ∂μ) ≤
      ENNReal.ofReal (C*Real.exp (-c*(a+1 : ℝ)^δ)) ∧
    (∫ x in {x | WithLp.ofLp (g x) ∉
        goodBlockEvent s.val a.succPNat (d+1+a).succPNat (K*ε)},
      InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s.val
        (WithLp.ofLp (g x)) ∂μ) ≤ C*Real.exp (-c*(a+1 : ℝ)^δ) ∧
    μ.real {x | WithLp.ofLp (g x) ∉
      goodBlockEvent s.val a.succPNat (d+1+a).succPNat (K*ε)} ≤
      C*Real.exp (-c*(a+1 : ℝ)^δ) ∧
    IntegrableOn
      (fun x => InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s.val (WithLp.ofLp (g x)))
      {x | WithLp.ofLp (g x) ∉ goodBlockEvent s.val a.succPNat (d+1+a).succPNat (K*ε)} μ ∧
    ∃ F : ScalarForm.Domain (IntrinsicScalarCore.jet hU hB hV),
      ScalarForm.value _ F =ᵐ[μ] D ∘ g ∧
      ∃ b₂ : Fin (a+1) → Lp ℝ 2 μ,
        (∀ j, b₂ j =ᵐ[μ] b j) ∧
        RectangularFormTransport.tupleMap M.transpose b₂ =
          fun k => DifferentiatedPoisson.coordinateLp k (ScalarForm.deriv _ F)) ∧
    (∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
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
            (‖χ.val‖+Real.exp (-c*(a+1 : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ (ν t)).toReal)) := by
  obtain ⟨Al,εl,hAl,hεl,hlocal⟩ :=
    chosen_fine_event_local_laws_internal s.val s.property.1 (ne_of_lt s.property.2)
  obtain ⟨Aj,εj,hAj,hεj,hjet⟩ :=
    chosen_fine_event_jet_internal s.val s.property.1 (ne_of_lt s.property.2)
  obtain ⟨Ad,K,εd,κ,hAd,hK,hεd,hκ,hthreshold,htyp,hdec⟩ :=
    long_range_decay_time_family_internal_joint hzeta hRig s (max Al Aj)
  let A := Ad
  let ε₀ := min εd (min εl εj)
  have hAdA : Ad ≤ A := le_rfl
  have hAlA : Al ≤ A := (le_max_left _ _).trans hthreshold
  have hAjA : Aj ≤ A := (le_max_right _ _).trans hthreshold
  have hε₀ : 0 < ε₀ := lt_min hεd (lt_min hεl hεj)
  refine ⟨A,K,ε₀,κ,hAd.trans_le hAdA,hK,hε₀,hκ,htyp.restrict (min_le_left _ _),?_,?_,?_⟩
  · intro ε hε hsmall
    exact hlocal A hAlA K ε hε
      (hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  · intro ε hε hsmall
    exact hjet A hAjA K hK ε hε
      (hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  · intro ε hε hsmall
    obtain ⟨δ,hδ,hdec⟩ := hdec ε hε (hsmall.trans_le (min_le_left _ _))
    refine ⟨δ,hδ,?_⟩
    intro βlo βhi hlo hle θ
    obtain ⟨C,c,hC,hc,hdec⟩ := hdec βlo βhi hlo hle θ
    refine ⟨C,c,hC,hc,?_⟩
    intro β hβ a d e ha hde hsize hpower y z L hyL hzL hy hz
    have hy₀ := admissible_exterior_mono_internal (ofLong β s)
      (d+1) a (by omega) θ ε hε.le hAdA le_rfl y hy
    have hz₀ := admissible_exterior_mono_internal (ofLong β s)
      (e+1) a (by omega) θ ε hε.le hAdA le_rfl z hz
    exact hdec β hβ a d e ha hde hsize hpower y z L hyL hzL hy₀ hz₀

/-- See the proof of Proposition 6.6 in the paper: the analytic conclusion and original exterior
typicality use one choice of A,K. A may exceed a prescribed threshold. -/
theorem short_range_common_choice_internal_joint (hRig : External.LongRangeRigidityLocallyUniform) (s : ShortExponent) :
    ∃ A K ε₀ κ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧ 0 < κ ∧
    OriginalTypicality s.val A K ε₀ ∧
    (∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ p : Parameters, p.val.2 = s.val → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
    ∀ d e m : ℕ, ∀ hd : 1 ≤ d, ∀ he : 1 ≤ e,
      1 ≤ m → 4*(m+1) ≤ d+m+1 → d ≤ e →
      (m+1 : ℝ)^(2/s.val) ≤ ((d+m : ℕ)+1 : ℝ) →
    let R := ENNReal.ofReal (C*Real.exp (-c*(m+1 : ℝ)^δ))
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
              WithLp.ofLp u ∉ goodBlockEvent s.val m.succPNat (d + m).succPNat (K * ε)},
            ENNReal.ofReal (exceptionalWeight s.val (n := m.succPNat) (WithLp.ofLp u)) ∂ν) ≤ R ∧
          (∀ i : Fin (m + 1),
            1 - R ≤ ν {u | ((m + 1 : ℕ) : ℝ) ^ (-(K * ε)) ≤ u i ∧
              u i ≤ ((m + 1 : ℕ) : ℝ) ^ (K * ε)}) ∧
          ∀ a b : ℕ, a < b → b ≤ m + 1 →
            ν {u | ((m + 1 : ℕ) : ℝ) ^ (K * ε) * (b - a : ℕ) ^ (min s.val 1 / 2) <
              |(∑ i ∈ Finset.univ.filter (fun i : Fin (m + 1) => a ≤ i.val ∧ i.val < b), u i) -
                (b - a : ℕ)|} ≤ R) ∧
    (∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ (p : Parameters), p.val.2 = s.val → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
    ∀ a d e : ℕ, 1 ≤ a → 4*(a+1) ≤ d+1+a+1 → d ≤ e →
      (a+1 : ℝ)^(2/s.val) ≤ (d+1+a+1 : ℝ) →
    ∀ (L : ℝ), 0 < L →
    ∀ (y : AffineSimplex.chartDomain (d+1) ((d+1+a : ℕ)+1))
      (z : AffineSimplex.chartDomain (e+1) ((e+1+a : ℕ)+1)),
      InterpolantLocalLaws.admissibleExterior p (d+1) a (by omega) θ ε A K y →
      InterpolantLocalLaws.admissibleExterior p (e+1) a (by omega) θ ε A K z →
      ((d+1+a : ℕ)+1 : ℝ)-∑ i, y.val i = L →
      ((e+1+a : ℕ)+1 : ℝ)-∑ i, z.val i = L →
    ∀ (Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ),
      (∀ u (hu : RetainedSimplex.assemble (d+1) a
        (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u ∈
          gapAmbientDomain (d+1+a).succPNat),
        Ky u = physicalAmbientGapEnergy p (d+1+a).succPNat
          ⟨RetainedSimplex.assemble (d+1) a
            (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u,hu⟩) →
      (∀ u (hu : RetainedSimplex.assemble (e+1) a
        (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u ∈
          gapAmbientDomain (e+1+a).succPNat),
        Kz u = physicalAmbientGapEnergy p (e+1+a).succPNat
          ⟨RetainedSimplex.assemble (e+1) a
            (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u,hu⟩) →
    ∀ (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
    ∀ (frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a))
      (M : Matrix (Fin (a+1)) (Fin a) ℝ),
      (∀ v : Fin a → ℝ, M *ᵥ v = (frame.symm (WithLp.toLp 2 v)).val) →
    let Ω := AffineSimplex.centredChart a L ⁻¹' AffineSimplex.massSimplex a L
    let U := frame '' Ω
    let g := fun x => AffineSimplex.centredChart a L (frame.symm x)
    let V := fun x => p.val.1*
      ((∑ i, (θ.val ((a+1 : ℝ)^(-ε)*g x i)+θ.val ((a+1 : ℝ)^(-ε)*(g x i)⁻¹)))+
        (1-t)*Ky (g x)+t*Kz (g x))
    let D := fun u => Ky u-Kz u
    let b := fun j x => InteractionDifferential.pinnedRepresentative (fun i : Fin a =>
      fderiv ℝ D (g x) (WithLp.toLp 2 (Pi.single i.castSucc 1-Pi.single i.succ 1))) j
    ∀ (μ : Measure (EuclideanSpace ℝ (Fin a)))
      (hV : IsEuclideanGibbsPotential volume μ U V),
    let hU := frame.toHomeomorph.isOpenMap Ω (ConditionalWellPosedness.fibre_isOpen a L)
    let hB := frame.isometry.lipschitzWith.isBounded_image
      (ConditionalWellPosedness.fibre_isBounded a L)
    (∫⁻ x in {x | WithLp.ofLp (g x) ∉
        goodBlockEvent s.val a.succPNat (d+1+a).succPNat (K*ε)},
      ENNReal.ofReal (InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s.val
        (WithLp.ofLp (g x))) ∂μ) ≤
      ENNReal.ofReal (C*Real.exp (-c*(a+1 : ℝ)^δ)) ∧
    (∫ x in {x | WithLp.ofLp (g x) ∉
        goodBlockEvent s.val a.succPNat (d+1+a).succPNat (K*ε)},
      InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s.val
        (WithLp.ofLp (g x)) ∂μ) ≤ C*Real.exp (-c*(a+1 : ℝ)^δ) ∧
    μ.real {x | WithLp.ofLp (g x) ∉
      goodBlockEvent s.val a.succPNat (d+1+a).succPNat (K*ε)} ≤
      C*Real.exp (-c*(a+1 : ℝ)^δ) ∧
    IntegrableOn
      (fun x => InterpolantLocalLaws.exceptionalWeight (n := a.succPNat) s.val (WithLp.ofLp (g x)))
      {x | WithLp.ofLp (g x) ∉ goodBlockEvent s.val a.succPNat (d+1+a).succPNat (K*ε)} μ ∧
    ∃ F : ScalarForm.Domain (IntrinsicScalarCore.jet hU hB hV),
      ScalarForm.value _ F =ᵐ[μ] D ∘ g ∧
      ∃ b₂ : Fin (a+1) → Lp ℝ 2 μ,
        (∀ j, b₂ j =ᵐ[μ] b j) ∧
        RectangularFormTransport.tupleMap M.transpose b₂ =
          fun k => DifferentiatedPoisson.coordinateLp k (ScalarForm.deriv _ F)) ∧
    (∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
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
            (‖χ.val‖+Real.exp (-c*(a+1 : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ (ν t)).toReal)) := by
  obtain ⟨Al,εl,hAl,hεl,hlocal⟩ :=
    chosen_fine_event_local_laws_internal s.val (zero_lt_one.trans s.property) (ne_of_gt s.property)
  obtain ⟨Aj,εj,hAj,hεj,hjet⟩ :=
    chosen_fine_event_jet_internal s.val (zero_lt_one.trans s.property) (ne_of_gt s.property)
  obtain ⟨Ad,K,εd,κ,hAd,hK,hεd,hκ,hthreshold,htyp,hdec⟩ :=
    short_range_decay_time_family_internal_joint hRig s (max Al Aj)
  let A := Ad
  let ε₀ := min εd (min εl εj)
  have hAdA : Ad ≤ A := le_rfl
  have hAlA : Al ≤ A := (le_max_left _ _).trans hthreshold
  have hAjA : Aj ≤ A := (le_max_right _ _).trans hthreshold
  have hε₀ : 0 < ε₀ := lt_min hεd (lt_min hεl hεj)
  refine ⟨A,K,ε₀,κ,hAd.trans_le hAdA,hK,hε₀,hκ,htyp.restrict (min_le_left _ _),?_,?_,?_⟩
  · intro ε hε hsmall
    exact hlocal A hAlA K ε hε
      (hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  · intro ε hε hsmall
    exact hjet A hAjA K hK ε hε
      (hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  · intro ε hε hsmall
    obtain ⟨δ,hδ,hdec⟩ := hdec ε hε (hsmall.trans_le (min_le_left _ _))
    refine ⟨δ,hδ,?_⟩
    intro βlo βhi hlo hle θ
    obtain ⟨C,c,hC,hc,hdec⟩ := hdec βlo βhi hlo hle θ
    refine ⟨C,c,hC,hc,?_⟩
    intro β hβ a d e ha hde hsize hpower y z L hyL hzL hy hz
    have hy₀ := admissible_exterior_mono_internal (ofShort β s)
      (d+1) a (by omega) θ ε hε.le hAdA le_rfl y hy
    have hz₀ := admissible_exterior_mono_internal (ofShort β s)
      (e+1) a (by omega) θ ε hε.le hAdA le_rfl z hz
    exact hdec β hβ a d e ha hde hsize hpower y z L hyL hzL hy₀ hz₀

end Riesz2.CompatibleComparison
