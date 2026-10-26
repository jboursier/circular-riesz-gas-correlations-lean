/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.CompatibleComparisonFinal
public import Riesz2.Thermodynamic.TwoVolumeComparisonV2

/-!
# Joint admissibility choices

See Appendix C and Proposition 6.6 of the paper: retain original-law exterior typicality
while choosing the structural admissibility parameters.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter ProbabilityTheory Matrix
open scoped BigOperators ENNReal NNReal ContDiff Topology MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable

namespace Riesz2.JointAdmissibility

/-- The original-law exterior tail in Appendix C,
with its structural parameters and tolerance range fixed. This predicate
only packages the quantified estimate for the existing physical exterior law. -/
def OriginalTypicality (s A K ε₀ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ δ : ℝ, 0 < δ ∧
  ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
  ∀ d m : ℕ, ∀ hd : 1 ≤ d, 1 ≤ m → 4*(m+1) ≤ d+m+1 →
    (m+1 : ℝ)^(2/s) ≤ ((d+m : ℕ)+1 : ℝ) →
    (InterpolantLocalLaws.physicalExteriorLaw p d m θ ε)
      {y | ¬InterpolantLocalLaws.admissibleExterior p d m hd θ ε A K y} ≤
      ENNReal.ofReal (C*Real.exp (-c*(m+1 : ℝ)^δ))

/-- See Appendix C in the paper: shrinking the tolerance range
preserves the original-law estimate and its quantifier order. -/
theorem OriginalTypicality.restrict {s A K ε₀ ε₁ : ℝ}
    (h : OriginalTypicality s A K ε₀) (hle : ε₁ ≤ ε₀) :
    OriginalTypicality s A K ε₁ := by
  intro ε hε hsmall
  exact h ε hε (hsmall.trans_le hle)

end Riesz2.JointAdmissibility

namespace Riesz2.InterpolantLocalLaws
open Riesz2.JointAdmissibility

/-- See Appendix C in the paper: all conclusions, with A chosen above a
prescribed threshold before choosing K for original-law typicality.
The long-range tolerance uses the least degree and the factor
`4 * (m + 1) * K` from Appendix C, in the proof of Lemma 6.2. The short-range branch only needs `K * ε ≤ 1/4`. -/
theorem joint_local_laws (hRig : External.LongRangeRigidityLocallyUniform)
    (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) (Areq : ℝ) :
    ∃ A K ε₀ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧ Areq ≤ A ∧
      OriginalTypicality s A K ε₀ ∧
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
  obtain ⟨Ac, hAc, hosc⟩ := physical_coarse_oscillation s hs hs1
  let A := max Ac Areq
  have hAcA : Ac ≤ A := le_max_left _ _
  have hA : 1 < A := hAc.trans_le hAcA
  obtain ⟨K, εbase, hK, hεbase, hmargin, htyp⟩ := admissible_exteriors_typical hRig s hs hs1 A hA
  -- Appendix C, proof of Lemma 6.2: use the degree of Lemma 5.4.
  let εcut : ℝ := if hlong : s < 1 then
    (4 * K * ((paperReferenceCutoffExponent ⟨s, hs, hlong⟩ : ℝ) + 1))⁻¹
    else (4 * K)⁻¹
  have hεcut : 0 < εcut := by
    dsimp only [εcut]
    split <;> positivity
  let ε₀ := min εbase εcut
  refine ⟨A, K, ε₀, hA, hK, lt_min hεbase hεcut, le_max_right _ _, ?_, ?_⟩
  · intro ε hε hsmall
    simpa only [Nat.cast_add, Nat.cast_one] using htyp ε hε
      (hsmall.trans_le (min_le_left _ _))
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
      have hh : B m ≤ ((m : ℝ)+1)^(Ac*ε) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hBl m hm
      apply hh.trans
      apply Real.rpow_le_rpow_of_exponent_le (by have := Nat.cast_nonneg (m : ℕ) (α := ℝ); linarith)
      exact mul_le_mul_of_nonneg_right hAcA hε.le)
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
