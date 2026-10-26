/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Preliminaries.GapChart
public import Riesz1.Rigidity.GapLawSymmetry
public import Riesz1.Auxiliary.LoopCutoffRotation
public import Riesz1.Gibbs.AnchoredCoordinates
public import Riesz1.Variance.APrioriGoodComparison
public import Riesz2.ToMathlib.FractTranslation
public import Riesz2.ToMathlib.InvariantDensity
public import Riesz2.Frozen.ShortKernelLift
public import Riesz2.Frozen.ShortEnergy
public import Riesz2.Frozen.Energy

/-!
# Finite symmetries and first gap moments

See Subsection 2.2 of the paper: common rotation preserves the Gibbs law, cyclic relabelling
preserves the gap law, the first particle is uniform and independent of the gaps, and every gap
and every span has the expected mean.

The proof works in the coordinates relative to the first particle `(X_0, (X_{j+1} - X_0)_j)` of Riesz 1, in which the
configuration volume is a product of Lebesgue measures. The common rotation acts on the first
coordinate only, and the cyclic relabelling `cycleConfig` acts on the offsets by
`Riesz1.anchorCycle`. Both preserve the configuration volume and the energy, hence the Gibbs law.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz2
namespace GapSymmetries

variable {N : ℕ+}

/-- The relabelled lift lies in the library configuration domain. Entry `k` is the periodic lift
at index `k + 1`, shifted by the integer part of `cyclicLift X 1`, so the first entry is the
fractional part of `cyclicLift X 1`. -/
theorem cycleLift_mem_orderedDomain (X : Riesz1.Configuration N) :
    (fun k : Fin (N : ℕ) => Riesz1.cyclicLift X (((k : ℕ) : ℤ) + 1) -
      ((⌊Riesz1.cyclicLift X 1⌋ : ℤ) : ℝ)) ∈ Riesz1.orderedDomain N := by
  have hmono : ∀ a b : Fin (N : ℕ), a < b →
      Riesz1.cyclicLift X (((a : ℕ) : ℤ) + 1) < Riesz1.cyclicLift X (((b : ℕ) : ℤ) + 1) := by
    intro a b hab
    apply Riesz1.cyclicLift_strictMono X
    have : (a : ℕ) < b := hab
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b hab
    show Riesz1.cyclicLift X (((a : ℕ) : ℤ) + 1) - (⌊Riesz1.cyclicLift X 1⌋ : ℝ) <
      Riesz1.cyclicLift X (((b : ℕ) : ℤ) + 1) - (⌊Riesz1.cyclicLift X 1⌋ : ℝ)
    linarith [hmono a b hab]
  · show 0 ≤ Riesz1.cyclicLift X (((0 : ℕ) : ℤ) + 1) - (⌊Riesz1.cyclicLift X 1⌋ : ℝ)
    rw [show ((0 : ℕ) : ℤ) + 1 = 1 by norm_num, Int.self_sub_floor]
    exact Int.fract_nonneg _
  · show Riesz1.cyclicLift X (((0 : ℕ) : ℤ) + 1) - (⌊Riesz1.cyclicLift X 1⌋ : ℝ) < 1
    rw [show ((0 : ℕ) : ℤ) + 1 = 1 by norm_num, Int.self_sub_floor]
    exact Int.fract_lt_one _
  · intro i
    show Riesz1.cyclicLift X (((i : ℕ) : ℤ) + 1) - (⌊Riesz1.cyclicLift X 1⌋ : ℝ) <
      Riesz1.cyclicLift X (((0 : ℕ) : ℤ) + 1) - (⌊Riesz1.cyclicLift X 1⌋ : ℝ) + 1
    have hlt : Riesz1.cyclicLift X (((i : ℕ) : ℤ) + 1) < Riesz1.cyclicLift X (1 + ((N : ℕ) : ℤ)) := by
      apply Riesz1.cyclicLift_strictMono X
      have := i.isLt
      omega
    have hN1 := Riesz1.cyclicLift_add_N X 1
    rw [show ((0 : ℕ) : ℤ) + 1 = 1 by norm_num]
    linarith

/-- The cyclic relabelling of a configuration: particle `k` of the result is particle `k + 1` of
`X` (taken cyclically), and the first particle lies in `[0, 1)`. -/
def cycleConfig (X : Riesz1.Configuration N) : Riesz1.Configuration N :=
  ⟨fun k : Fin (N : ℕ) => Riesz1.cyclicLift X (((k : ℕ) : ℤ) + 1) -
      ((⌊Riesz1.cyclicLift X 1⌋ : ℤ) : ℝ), cycleLift_mem_orderedDomain X⟩

/-- The periodic lift of the relabelled configuration is the periodic lift of `X` shifted by one
index and by the integer part of the first particle. -/
theorem cyclicLift_cycleConfig (X : Riesz1.Configuration N) (j : ℤ) :
    Riesz1.cyclicLift (cycleConfig X) j =
      Riesz1.cyclicLift X (j + 1) - ((⌊Riesz1.cyclicLift X 1⌋ : ℤ) : ℝ) := by
  have hN : (0 : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast N.pos
  have hmod_nonneg : 0 ≤ j % ((N : ℕ) : ℤ) := Int.emod_nonneg _ hN.ne'
  obtain ⟨i, hi_eq⟩ : ∃ i : ℕ, (i : ℤ) = j % ((N : ℕ) : ℤ) :=
    ⟨(j % ((N : ℕ) : ℤ)).toNat, Int.toNat_of_nonneg hmod_nonneg⟩
  have hi : i < (N : ℕ) := by
    have := Int.emod_lt_of_pos j hN
    omega
  obtain ⟨q, rfl⟩ : ∃ q : ℤ, j = (i : ℤ) + ((N : ℕ) : ℤ) * q :=
    ⟨j / ((N : ℕ) : ℤ), by rw [hi_eq, Int.emod_def]; ring⟩
  rw [Riesz1.cyclicLift_add_mul (cycleConfig X) hi q,
    show (i : ℤ) + ((N : ℕ) : ℤ) * q + 1 = ((i : ℤ) + 1) + ((N : ℕ) : ℤ) * q by ring,
    Riesz1.APG.cyclicLift_add_N_mul X ((i : ℤ) + 1) q]
  show (Riesz1.cyclicLift X (((i : ℕ) : ℤ) + 1) - ((⌊Riesz1.cyclicLift X 1⌋ : ℤ) : ℝ)) + q =
    Riesz1.cyclicLift X ((i : ℤ) + 1) + q - ((⌊Riesz1.cyclicLift X 1⌋ : ℤ) : ℝ)
  ring

/-- The microscopic gap of the relabelled configuration is the gap one index later. -/
theorem gap_cycleConfig (X : Riesz1.Configuration N) (j : ℤ) :
    Riesz2.gap (cycleConfig X) j = Riesz2.gap X (j + 1) := by
  unfold Riesz2.gap
  rw [cyclicLift_cycleConfig, cyclicLift_cycleConfig]
  ring_nf

/-- The gap vector of the relabelled configuration is the cyclic shift of the gap vector. -/
theorem gapVector_cycleConfig (X : Riesz1.Configuration N) (i : Fin (N : ℕ)) :
    Riesz2.gapVector (cycleConfig X) i = Riesz2.gapVector X (finRotate (N : ℕ) i) := by
  have h : Riesz2.gapVector X (finRotate (N : ℕ) i) = Riesz1.gap X (((i : ℕ) : ℤ) + 1) :=
    Riesz1.gapVector_finRotate N X i
  rw [h]
  change Riesz2.gap (cycleConfig X) (i : ℕ) = Riesz2.gap X (((i : ℕ) : ℤ) + 1)
  rw [gap_cycleConfig]

/-- The cyclic relabelling is measurable. -/
theorem measurable_cycleConfig : Measurable (cycleConfig (N := N)) := by
  refine Measurable.subtype_mk (measurable_pi_iff.mpr fun k => ?_)
  exact (Riesz1.measurable_cyclicLift _).sub
    ((Measurable.of_discrete (f := fun k : ℤ => (k : ℝ))).comp
      (Int.measurable_floor.comp (Riesz1.measurable_cyclicLift 1)))

/-- The common rotation is measurable. -/
theorem measurable_loopRotate (t : ℝ) : Measurable (Riesz1.loopRotate N t) := by
  have h0 : Measurable (fun X : Riesz1.Configuration N => X.val ⟨0, N.pos⟩) :=
    (measurable_pi_apply _).comp measurable_subtype_coe
  have hfl : Measurable (fun X : Riesz1.Configuration N => ((⌊X.val ⟨0, N.pos⟩ + t⌋ : ℤ) : ℝ)) :=
    (Measurable.of_discrete (f := fun k : ℤ => (k : ℝ))).comp
      (Int.measurable_floor.comp (h0.add_const t))
  refine Measurable.subtype_mk (measurable_pi_iff.mpr fun i => ?_)
  exact ((measurable_pi_apply i).comp measurable_subtype_coe).add (measurable_const.sub hfl)

/-! ### Coordinates relative to the first particle

A configuration on `m + 2` particles is coded by its first lift `X_0 ∈ [0,1)` and by the
offsets `X_{j+1} - X_0`. In these coordinates the common rotation acts on the first coordinate
only, and the cyclic relabelling acts on the offsets by `Riesz1.anchorCycle`. -/

section Anchored

variable {m : ℕ}

/-- Rotating a configuration by `t` changes only the rotation coordinate, modulo one. -/
theorem anchorCoords_loopRotate (t : ℝ) (X : Riesz1.Configuration (m + 1).succPNat) :
    Riesz1.anchorCoords (m + 1) (Riesz1.loopRotate (m + 1).succPNat t X).val =
      (Int.fract ((Riesz1.anchorCoords (m + 1) X.val).1 + t),
        (Riesz1.anchorCoords (m + 1) X.val).2) := by
  refine Prod.ext ?_ ?_
  · change X.val 0 + (t - ⌊X.val 0 + t⌋) = Int.fract (X.val 0 + t)
    rw [Int.fract]
    ring
  · funext j
    change (X.val j.succ + (t - ⌊X.val 0 + t⌋)) - (X.val 0 + (t - ⌊X.val 0 + t⌋)) =
      X.val j.succ - X.val 0
    ring

/-- The coordinates relative to the first particle of the cycled configuration. The first coordinate is the fractional
part of the first particle of `X` moved to `X_1`, and the offsets are cyclically relabelled. -/
theorem anchorCoords_cycleConfig (X : Riesz1.Configuration (m + 1).succPNat) :
    Riesz1.anchorCoords (m + 1) (cycleConfig X).val =
      (Int.fract ((Riesz1.anchorCoords (m + 1) X.val).1 + (Riesz1.anchorCoords (m + 1) X.val).2 0),
        Riesz1.anchorCycle m (Riesz1.anchorCoords (m + 1) X.val).2) := by
  have hN : Riesz1.cyclicLift X (((((m + 1).succPNat : ℕ)) : ℤ)) = X.val 0 + 1 := by
    have h := Riesz1.cyclicLift_add_N X 0
    have h0 : Riesz1.cyclicLift X 0 = X.val 0 := by
      simpa using Riesz1.cyclicLift_natCast X 0
    rw [zero_add, h0] at h
    exact h
  refine Prod.ext ?_ ?_
  · have h1 : Riesz1.cyclicLift X 1 = X.val (Fin.succ 0) := by
      simpa using Riesz1.cyclicLift_natCast X (Fin.succ 0)
    change Riesz1.cyclicLift X (((0 : ℕ) : ℤ) + 1) - ((⌊Riesz1.cyclicLift X 1⌋ : ℤ) : ℝ) =
      Int.fract (X.val 0 + (X.val (Fin.succ 0) - X.val 0))
    rw [show ((0 : ℕ) : ℤ) + 1 = 1 by norm_num, h1, show X.val 0 + (X.val (Fin.succ 0) - X.val 0) =
      X.val (Fin.succ 0) by ring, Int.fract]
  · funext j
    induction j using Fin.lastCases with
    | last =>
      dsimp only
      rw [Riesz1.anchorCycle_last]
      change Riesz1.cyclicLift X (((((Fin.last m).succ : Fin (m + 2)) : ℕ) : ℤ) + 1) -
          ((⌊Riesz1.cyclicLift X 1⌋ : ℤ) : ℝ) -
        (Riesz1.cyclicLift X 1 - ((⌊Riesz1.cyclicLift X 1⌋ : ℤ) : ℝ)) =
        1 - (X.val (Fin.succ 0) - X.val 0)
      have h1 : Riesz1.cyclicLift X 1 = X.val (Fin.succ 0) := by
        simpa using Riesz1.cyclicLift_natCast X (Fin.succ 0)
      have hv : ((((Fin.last m).succ : Fin (m + 2)) : ℕ) : ℤ) + 1 = ((m + 1).succPNat : ℕ) := by
        simp
      rw [hv, hN, h1]
      ring
    | cast i =>
      dsimp only
      rw [Riesz1.anchorCycle_castSucc]
      change Riesz1.cyclicLift X (((((i.castSucc).succ : Fin (m + 2)) : ℕ) : ℤ) + 1) -
          ((⌊Riesz1.cyclicLift X 1⌋ : ℤ) : ℝ) -
        (Riesz1.cyclicLift X 1 - ((⌊Riesz1.cyclicLift X 1⌋ : ℤ) : ℝ)) =
        (X.val i.succ.succ - X.val 0) - (X.val (Fin.succ 0) - X.val 0)
      have h1 : Riesz1.cyclicLift X 1 = X.val (Fin.succ 0) := by
        simpa using Riesz1.cyclicLift_natCast X (Fin.succ 0)
      have hv : ((((i.castSucc).succ : Fin (m + 2)) : ℕ) : ℤ) + 1 = ((i.succ.succ : Fin (m + 2)) : ℕ) := by
        simp
      rw [hv, Riesz1.cyclicLift_natCast X i.succ.succ, h1]
      ring

/-- The coordinates relative to the first particle identify a configuration: the first coordinate and the offsets
determine every particle. -/
theorem measurableEmbedding_anchorCoords :
    MeasurableEmbedding (fun X : Riesz1.Configuration (m + 1).succPNat =>
      Riesz1.anchorCoords (m + 1) X.val) := by
  let _ : StandardBorelSpace (Riesz1.Configuration (m + 1).succPNat) :=
    (Riesz1.measurableSet_orderedDomain _).standardBorel
  refine (Riesz1.measurable_anchorCoords_config (m + 1)).measurableEmbedding ?_
  intro X Y hXY
  have h1 : X.val 0 = Y.val 0 := congrArg Prod.fst hXY
  have h2 : ∀ j : Fin (m + 1), X.val j.succ - X.val 0 = Y.val j.succ - Y.val 0 := fun j =>
    congrFun (congrArg Prod.snd hXY) j
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact h1
  · have := h2 j
    linarith

/-- Rotation of the rotation coordinate, modulo one, preserves the product law. -/
theorem measurePreserving_rotPair (t : ℝ) :
    MeasurePreserving (fun p : ℝ × (Fin (m + 1) → ℝ) => (Int.fract (p.1 + t), p.2))
      ((volume.restrict (Ico (0 : ℝ) 1)).prod (volume.restrict (Riesz1.anchoredDomain (m + 1))))
      ((volume.restrict (Ico (0 : ℝ) 1)).prod (volume.restrict (Riesz1.anchoredDomain (m + 1)))) := by
  have h1 : MeasurePreserving (fun x : ℝ => Int.fract (x + t))
      (volume.restrict (Ico (0 : ℝ) 1)) (volume.restrict (Ico (0 : ℝ) 1)) :=
    ⟨measurable_fract.comp (measurable_id.add_const t),
      FractTranslation.map_fract_add_restrict_Ico t⟩
  exact h1.prod (MeasurePreserving.id _)

/-- The cyclic relabelling of the coordinates relative to the first particle preserves the product law: the offsets
move by `Riesz1.anchorCycle` and the first coordinate moves by the first offset. -/
theorem measurePreserving_cycleAnchored :
    MeasurePreserving
      (fun p : ℝ × (Fin (m + 1) → ℝ) => (Int.fract (p.1 + p.2 0), Riesz1.anchorCycle m p.2))
      ((volume.restrict (Ico (0 : ℝ) 1)).prod (volume.restrict (Riesz1.anchoredDomain (m + 1))))
      ((volume.restrict (Ico (0 : ℝ) 1)).prod (volume.restrict (Riesz1.anchoredDomain (m + 1)))) := by
  set P1 := volume.restrict (Riesz1.anchoredDomain (m + 1)) with hP1
  set P2 := volume.restrict (Ico (0 : ℝ) 1) with hP2
  have hac : MeasurePreserving (Riesz1.anchorCycle m) P1 P1 :=
    ⟨(Riesz1.measurePreserving_anchorCycle m).measurable, Riesz1.map_anchorCycle_restrict m⟩
  have hg : Measurable (Function.uncurry fun (y : Fin (m + 1) → ℝ) (x : ℝ) =>
      Int.fract (x + y 0)) :=
    measurable_fract.comp (measurable_snd.add ((measurable_pi_apply 0).comp measurable_fst))
  have hfib : ∀ᵐ y ∂P1, Measure.map (fun x : ℝ => Int.fract (x + y 0)) P2 = P2 :=
    Filter.Eventually.of_forall (fun y => FractTranslation.map_fract_add_restrict_Ico (y 0))
  have hK := MeasurePreserving.skew_product (μc := P2) hac hg hfib
  have hs1 := (Measure.measurePreserving_swap (μ := P2) (ν := P1))
  have hs2 := (Measure.measurePreserving_swap (μ := P1) (ν := P2))
  exact hs2.comp (hK.comp hs1)

/-- The configuration volume is invariant under the common rotation `loopRotate`. -/
theorem configurationVolume_map_loopRotate (t : ℝ) :
    (Riesz1.configurationVolume (m + 1).succPNat).map (Riesz1.loopRotate (m + 1).succPNat t) =
      Riesz1.configurationVolume (m + 1).succPNat := by
  apply (measurableEmbedding_anchorCoords (m := m)).map_injective
  have hΦ : Measurable (fun X : Riesz1.Configuration (m + 1).succPNat =>
      Riesz1.anchorCoords (m + 1) X.val) := Riesz1.measurable_anchorCoords_config (m + 1)
  have hR : Measurable (fun p : ℝ × (Fin (m + 1) → ℝ) => (Int.fract (p.1 + t), p.2)) :=
    (measurable_fract.comp (measurable_fst.add_const t)).prodMk measurable_snd
  rw [Measure.map_map hΦ (measurable_loopRotate t)]
  have hcomp : (fun X : Riesz1.Configuration (m + 1).succPNat => Riesz1.anchorCoords (m + 1) X.val) ∘
      Riesz1.loopRotate (m + 1).succPNat t =
      (fun p : ℝ × (Fin (m + 1) → ℝ) => (Int.fract (p.1 + t), p.2)) ∘
        (fun X : Riesz1.Configuration (m + 1).succPNat => Riesz1.anchorCoords (m + 1) X.val) :=
    funext (anchorCoords_loopRotate t)
  rw [hcomp, ← Measure.map_map hR hΦ, Riesz1.map_anchorCoords_configurationVolume,
    (measurePreserving_rotPair t).map_eq]

/-- The configuration volume is invariant under the cyclic relabelling `cycleConfig`. -/
theorem configurationVolume_map_cycleConfig :
    (Riesz1.configurationVolume (m + 1).succPNat).map (cycleConfig (N := (m + 1).succPNat)) =
      Riesz1.configurationVolume (m + 1).succPNat := by
  apply (measurableEmbedding_anchorCoords (m := m)).map_injective
  have hΦ : Measurable (fun X : Riesz1.Configuration (m + 1).succPNat =>
      Riesz1.anchorCoords (m + 1) X.val) := Riesz1.measurable_anchorCoords_config (m + 1)
  have hS : Measurable (fun p : ℝ × (Fin (m + 1) → ℝ) =>
      (Int.fract (p.1 + p.2 0), Riesz1.anchorCycle m p.2)) :=
    (measurable_fract.comp (measurable_fst.add ((measurable_pi_apply 0).comp measurable_snd))).prodMk
      (((Riesz1.measurePreserving_anchorCycle m).measurable).comp measurable_snd)
  rw [Measure.map_map hΦ (measurable_cycleConfig)]
  have hcomp : (fun X : Riesz1.Configuration (m + 1).succPNat => Riesz1.anchorCoords (m + 1) X.val) ∘
      cycleConfig (N := (m + 1).succPNat) =
      (fun p : ℝ × (Fin (m + 1) → ℝ) => (Int.fract (p.1 + p.2 0), Riesz1.anchorCycle m p.2)) ∘
        (fun X : Riesz1.Configuration (m + 1).succPNat => Riesz1.anchorCoords (m + 1) X.val) :=
    funext (anchorCoords_cycleConfig)
  rw [hcomp, ← Measure.map_map hS hΦ, Riesz1.map_anchorCoords_configurationVolume,
    (measurePreserving_cycleAnchored (m := m)).map_eq]

end Anchored

/-! ### Energy invariance

The energy depends on the lifts only through the differences `X_i - X_j`, and the kernels are
periodic. Hence a relabelling `e` that preserves every difference modulo one leaves the energy
unchanged. -/

/-- The short-range kernel is unchanged when its argument is shifted by an integer. -/
theorem shortKernelLift_eq_of_int (s : ShortExponent) (a b : ℝ) (k : ℤ) (h : a = b + k)
    (ha : (a : UnitAddCircle) ≠ 0) (hb : (b : UnitAddCircle) ≠ 0) :
    Riesz2.shortKernelLift s ⟨a, ha⟩ = Riesz2.shortKernelLift s ⟨b, hb⟩ := by
  subst h
  unfold Riesz2.shortKernelLift
  calc ∑' j : ℤ, 1 / |(j : ℝ) + (b + k)| ^ s.val
      = ∑' j : ℤ, (fun j : ℤ => 1 / |(j : ℝ) + b| ^ s.val) ((Equiv.addRight k) j) :=
        tsum_congr fun j => by
          simp only [Equiv.coe_addRight]
          congr 3
          push_cast
          ring
    _ = ∑' j : ℤ, 1 / |(j : ℝ) + b| ^ s.val :=
        Equiv.tsum_eq (Equiv.addRight k) (fun j : ℤ => 1 / |(j : ℝ) + b| ^ s.val)

/-- Sums over ordered pairs of distinct indices are invariant under a relabelling, provided each
summand is invariant. -/
theorem sum_subtype_ne_perm {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M]
    (e : ι ≃ ι) (F G : (i : ι) → {j : ι // j ≠ i} → M)
    (h : ∀ (i : ι) (j : {j : ι // j ≠ i}), F i j = G (e i) ⟨e j.1, e.injective.ne j.2⟩) :
    ∑ i, ∑ j, F i j = ∑ i, ∑ j, G i j := by
  calc ∑ i, ∑ j, F i j = ∑ i, ∑ j : {j : ι // j ≠ i}, G (e i) ⟨e j.1, e.injective.ne j.2⟩ :=
        Fintype.sum_congr _ _ fun i => Fintype.sum_congr _ _ fun j => h i j
    _ = ∑ i, ∑ j : {j : ι // j ≠ e i}, G (e i) j :=
        Fintype.sum_congr _ _ fun i =>
          Fintype.sum_equiv
            (Equiv.subtypeEquiv (p := fun j => j ≠ i) (q := fun j => j ≠ e i) e
              (fun j => e.injective.ne_iff.symm))
            (fun j => G (e i) ⟨e j.1, e.injective.ne j.2⟩) (G (e i)) fun j => rfl
    _ = ∑ i, ∑ j : {j : ι // j ≠ i}, G i j :=
        Fintype.sum_equiv e (fun i => ∑ j : {j : ι // j ≠ e i}, G (e i) j)
          (fun i => ∑ j : {j : ι // j ≠ i}, G i j) fun i => rfl

/-- The circle class of a real number is unchanged by an integer shift. -/
theorem coe_add_int_circle (a : ℝ) (k : ℤ) :
    ((a + k : ℝ) : UnitAddCircle) = (a : UnitAddCircle) := by
  simp

/-- The Riesz energy of the library is invariant under a relabelling that preserves the pairwise
differences modulo one. -/
theorem riesz1_energy_eq_of_offset_perm {N : ℕ+} (s : Riesz1.RieszExponent)
    (X Y : Riesz1.Configuration N) (e : Equiv.Perm (Fin (N : ℕ)))
    (hYX : ∀ i j : Fin (N : ℕ), ∃ k : ℤ, Y.val i - Y.val j = X.val (e i) - X.val (e j) + k) :
    Riesz1.energy s Y = Riesz1.energy s X := by
  unfold Riesz1.energy
  congr 1
  calc ∑ i, ∑ j ∈ Finset.univ.erase i,
        Riesz1.rieszRepresentative s ((Y.val i - Y.val j : ℝ) : UnitAddCircle)
      = ∑ i, ∑ j ∈ Finset.univ.erase i,
          Riesz1.rieszRepresentative s ((X.val (e i) - X.val (e j) : ℝ) : UnitAddCircle) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
          obtain ⟨k, hk⟩ := hYX i j
          rw [hk, coe_add_int_circle]
    _ = ∑ i, ∑ j ∈ Finset.univ.erase i,
          Riesz1.rieszRepresentative s ((X.val i - X.val j : ℝ) : UnitAddCircle) :=
        Riesz1.sum_offDiagonal_equiv e (fun i j =>
          Riesz1.rieszRepresentative s ((X.val i - X.val j : ℝ) : UnitAddCircle))

/-- The short-range energy is invariant under a relabelling that preserves the pairwise
differences modulo one. -/
theorem shortEnergy_eq_of_offset_perm (s : ShortExponent) {N : ℕ+}
    (X Y : Riesz1.Configuration N) (e : Equiv.Perm (Fin (N : ℕ)))
    (hYX : ∀ i j : Fin (N : ℕ), ∃ k : ℤ, Y.val i - Y.val j = X.val (e i) - X.val (e j) + k) :
    Riesz2.shortEnergy s Y = Riesz2.shortEnergy s X := by
  unfold Riesz2.shortEnergy
  congr 1
  refine sum_subtype_ne_perm e _ _ fun i j => ?_
  obtain ⟨k, hk⟩ := hYX i j.1
  exact shortKernelLift_eq_of_int s _ _ k hk _ _

/-- The energy of the library and the short-range energy are invariant under a relabelling that
preserves the pairwise differences modulo one. -/
theorem energy_eq_of_offset_perm (p : Parameters) {N : ℕ+}
    (X Y : Riesz1.Configuration N) (e : Equiv.Perm (Fin (N : ℕ)))
    (hYX : ∀ i j : Fin (N : ℕ), ∃ k : ℤ, Y.val i - Y.val j = X.val (e i) - X.val (e j) + k) :
    Riesz2.energy p Y = Riesz2.energy p X := by
  unfold Riesz2.energy
  split_ifs
  · exact riesz1_energy_eq_of_offset_perm _ X Y e hYX
  · exact shortEnergy_eq_of_offset_perm _ X Y e hYX

/-- Each lift of the relabelled configuration is a lift of `X` at the cyclically next index, up to
an integer. -/
theorem cyclicLift_succ_eq_val_finRotate (X : Riesz1.Configuration N) (i : Fin (N : ℕ)) :
    ∃ k : ℤ, Riesz1.cyclicLift X (((i : ℕ) : ℤ) + 1) = X.val (finRotate (N : ℕ) i) + k := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n.succPNat := ⟨N.natPred, (PNat.succPNat_natPred N).symm⟩
  have hi_lt : (i : ℕ) < n + 1 := i.isLt
  by_cases hi : (i : ℕ) = n
  · have hlast : i = Fin.last n := Fin.ext (by simpa using hi)
    have hfr : finRotate (n.succPNat : ℕ) i = 0 := by
      rw [hlast]
      exact finRotate_last
    refine ⟨1, ?_⟩
    have h := Riesz1.cyclicLift_add_N X 0
    have h0 : Riesz1.cyclicLift X 0 = X.val 0 := by
      simpa using Riesz1.cyclicLift_natCast X 0
    rw [zero_add, h0] at h
    have hv : ((i : ℕ) : ℤ) + 1 = ((n.succPNat : ℕ) : ℤ) := by
      rw [hi]
      simp
    rw [hv, hfr, Int.cast_one]
    exact h
  · have hne : i ≠ Fin.last n := fun h => hi (by rw [h]; simp)
    have hval : ((finRotate (n.succPNat : ℕ) i : Fin (n.succPNat : ℕ)) : ℕ) = (i : ℕ) + 1 :=
      coe_finRotate_of_ne_last hne
    refine ⟨0, ?_⟩
    rw [Int.cast_zero, add_zero]
    have hfin : finRotate (n.succPNat : ℕ) i = ⟨(i : ℕ) + 1, by omega⟩ := Fin.ext hval
    rw [hfin]
    simpa using Riesz1.cyclicLift_natCast X ⟨(i : ℕ) + 1, by omega⟩

/-! ### Invariance of the Gibbs and gap laws -/

/-- The energy of the common rotation of a configuration is unchanged. -/
theorem energy_loopRotate (p : Parameters) {N : ℕ+} (t : ℝ) (X : Riesz1.Configuration N) :
    Riesz2.energy p (Riesz1.loopRotate N t X) = Riesz2.energy p X := by
  refine energy_eq_of_offset_perm p X _ (Equiv.refl _) fun i j => ⟨0, ?_⟩
  simp only [Equiv.refl_apply, Int.cast_zero, add_zero]
  change (X.val i + (t - ⌊X.val ⟨0, N.pos⟩ + t⌋)) - (X.val j + (t - ⌊X.val ⟨0, N.pos⟩ + t⌋)) =
    X.val i - X.val j
  ring

/-- The offsets of the cycled configuration are those of `X` relabelled, up to integers. -/
theorem cycleConfig_offset (X : Riesz1.Configuration N) (i j : Fin (N : ℕ)) :
    ∃ k : ℤ, (cycleConfig X).val i - (cycleConfig X).val j =
      X.val (finRotate (N : ℕ) i) - X.val (finRotate (N : ℕ) j) + k := by
  obtain ⟨ki, hi⟩ := cyclicLift_succ_eq_val_finRotate X i
  obtain ⟨kj, hj⟩ := cyclicLift_succ_eq_val_finRotate X j
  refine ⟨ki - kj, ?_⟩
  change Riesz1.cyclicLift X (((i : ℕ) : ℤ) + 1) - ((⌊Riesz1.cyclicLift X 1⌋ : ℤ) : ℝ) -
    (Riesz1.cyclicLift X (((j : ℕ) : ℤ) + 1) - ((⌊Riesz1.cyclicLift X 1⌋ : ℤ) : ℝ)) = _
  rw [hi, hj]
  push_cast
  ring

/-- The energy is invariant under the cyclic relabelling. -/
theorem energy_cycleConfig (p : Parameters) (X : Riesz1.Configuration N) :
    Riesz2.energy p (cycleConfig X) = Riesz2.energy p X :=
  energy_eq_of_offset_perm p X _ (finRotate (N : ℕ)) (cycleConfig_offset X)

/-- The Gibbs law is invariant under a common rotation of the particles. -/
theorem gibbsMeasure_map_loopRotate (p : Parameters) (m : ℕ) (t : ℝ) :
    (gibbsMeasure p (m + 1).succPNat).map (Riesz1.loopRotate (m + 1).succPNat t) =
      gibbsMeasure p (m + 1).succPNat := by
  rw [GapChart.gibbsMeasure_eq_withDensity, Measure.map_smul _ (measurable_loopRotate t).aemeasurable]
  congr 1
  refine InvariantDensity.map_withDensity_eq_self
    ⟨measurable_loopRotate t, configurationVolume_map_loopRotate t⟩ ?_ fun X => ?_
  · exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul (Riesz2.measurable_energy p _)))
  · simp only [energy_loopRotate]

/-- The Gibbs law is invariant under the cyclic relabelling of the particles. -/
theorem gibbsMeasure_map_cycleConfig (p : Parameters) (m : ℕ) :
    (gibbsMeasure p (m + 1).succPNat).map (cycleConfig (N := (m + 1).succPNat)) =
      gibbsMeasure p (m + 1).succPNat := by
  rw [GapChart.gibbsMeasure_eq_withDensity,
    Measure.map_smul _ measurable_cycleConfig.aemeasurable]
  congr 1
  refine InvariantDensity.map_withDensity_eq_self
    ⟨measurable_cycleConfig, configurationVolume_map_cycleConfig⟩ ?_ fun X => ?_
  · exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul (Riesz2.measurable_energy p _)))
  · simp only [energy_cycleConfig]

/-- The gap law is invariant under the cyclic relabelling of the gap coordinates. -/
theorem gapLaw_map_finRotate (p : Parameters) (m : ℕ) :
    (gapLaw p (m + 1).succPNat).map
      (fun g : Fin ((m + 1).succPNat : ℕ) → ℝ => fun i => g (finRotate _ i)) =
      gapLaw p (m + 1).succPNat := by
  have hQ : Measurable (fun g : Fin ((m + 1).succPNat : ℕ) → ℝ => fun i => g (finRotate _ i)) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply _
  have hV : Measurable (Riesz2.gapVector (N := (m + 1).succPNat)) :=
    Riesz1.measurable_gapVector _
  unfold Riesz2.gapLaw
  rw [Measure.map_map hQ hV]
  have hcomp : (fun g : Fin ((m + 1).succPNat : ℕ) → ℝ => fun i => g (finRotate _ i)) ∘
      Riesz2.gapVector =
      Riesz2.gapVector ∘ cycleConfig (N := (m + 1).succPNat) :=
    funext fun X => funext fun i => (gapVector_cycleConfig X i).symm
  rw [hcomp, ← Measure.map_map hV measurable_cycleConfig, gibbsMeasure_map_cycleConfig]

/-! ### First gap moments -/

section Moments

variable {m : ℕ}

/-- The periodic lift at the number of particles is the lift at zero plus one. -/
theorem cyclicLift_card (X : Riesz1.Configuration (m + 1).succPNat) :
    Riesz1.cyclicLift X (((m + 1).succPNat : ℕ) : ℤ) = X.val 0 + 1 := by
  have h := Riesz1.cyclicLift_add_N X 0
  have h0 : Riesz1.cyclicLift X 0 = X.val 0 := by
    simpa using Riesz1.cyclicLift_natCast X 0
  rw [zero_add, h0] at h
  exact h

/-- The gaps of a configuration sum to the number of particles. -/
theorem sum_gapVector (X : Riesz1.Configuration (m + 1).succPNat) :
    ∑ i : Fin ((m + 1).succPNat : ℕ), Riesz2.gapVector X i = (((m + 1).succPNat : ℕ) : ℝ) := by
  set f : ℕ → ℝ := fun k => Riesz1.cyclicLift X (k : ℤ) with hf
  have h1 : ∀ i : Fin ((m + 1).succPNat : ℕ),
      Riesz2.gapVector X i = (((m + 1).succPNat : ℕ) : ℝ) * (f ((i : ℕ) + 1) - f (i : ℕ)) := by
    intro i
    simp only [Riesz2.gapVector, Riesz2.gap, hf]
    push_cast
    ring_nf
  calc ∑ i : Fin ((m + 1).succPNat : ℕ), Riesz2.gapVector X i
      = ∑ i : Fin ((m + 1).succPNat : ℕ),
          (((m + 1).succPNat : ℕ) : ℝ) * (f ((i : ℕ) + 1) - f (i : ℕ)) :=
        Finset.sum_congr rfl fun i _ => h1 i
    _ = (((m + 1).succPNat : ℕ) : ℝ) * ∑ i ∈ Finset.range ((m + 1).succPNat : ℕ),
          (f (i + 1) - f i) := by
        rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i => f (i + 1) - f i)]
    _ = (((m + 1).succPNat : ℕ) : ℝ) * (f ((m + 1).succPNat : ℕ) - f 0) := by
        rw [Finset.sum_range_sub]
    _ = (((m + 1).succPNat : ℕ) : ℝ) := by
        have hN : f ((m + 1).succPNat : ℕ) = X.val 0 + 1 := by
          simp only [hf]
          exact_mod_cast cyclicLift_card X
        have h0 : f 0 = X.val 0 := by
          simp only [hf, Nat.cast_zero]
          simpa using Riesz1.cyclicLift_natCast X 0
        rw [hN, h0]
        ring

/-- Every gap is positive. -/
theorem gapVector_pos (X : Riesz1.Configuration (m + 1).succPNat)
    (i : Fin ((m + 1).succPNat : ℕ)) : 0 < Riesz2.gapVector X i := by
  change 0 < ((((m + 1).succPNat : ℕ)) : ℝ) *
    (Riesz1.cyclicLift X (((i : ℕ) : ℤ) + 1) - Riesz1.cyclicLift X ((i : ℕ) : ℤ))
  have hlt := Riesz1.cyclicLift_lt_succ X ((i : ℕ) : ℤ)
  have hpos : (0 : ℝ) < (((m + 1).succPNat : ℕ) : ℝ) := by
    exact_mod_cast (m + 1).succPNat.pos
  have hsub : 0 < Riesz1.cyclicLift X (((i : ℕ) : ℤ) + 1) -
      Riesz1.cyclicLift X ((i : ℕ) : ℤ) := by linarith
  exact mul_pos hpos hsub

/-- Every gap is smaller than the number of particles, since the lift at `i + 1` lies below the
lift at `i + N`. -/
theorem gapVector_lt (X : Riesz1.Configuration (m + 1).succPNat)
    (i : Fin ((m + 1).succPNat : ℕ)) :
    Riesz2.gapVector X i < (((m + 1).succPNat : ℕ) : ℝ) := by
  change (((m + 1).succPNat : ℕ) : ℝ) *
    (Riesz1.cyclicLift X (((i : ℕ) : ℤ) + 1) - Riesz1.cyclicLift X ((i : ℕ) : ℤ)) <
      (((m + 1).succPNat : ℕ) : ℝ)
  have hlt : Riesz1.cyclicLift X (((i : ℕ) : ℤ) + 1) <
      Riesz1.cyclicLift X (((i : ℕ) : ℤ) + ((m + 1).succPNat : ℕ)) := by
    apply Riesz1.cyclicLift_strictMono X
    have : (2 : ℤ) ≤ ((m + 1).succPNat : ℕ) := by
      simp only [Nat.succPNat_coe]
      omega
    have hi : ((i : ℕ) : ℤ) ≥ 0 := by positivity
    omega
  rw [Riesz1.cyclicLift_add_N] at hlt
  have hpos : (0 : ℝ) < (((m + 1).succPNat : ℕ) : ℝ) := by
    exact_mod_cast (m + 1).succPNat.pos
  have hsub : Riesz1.cyclicLift X (((i : ℕ) : ℤ) + 1) -
      Riesz1.cyclicLift X ((i : ℕ) : ℤ) < 1 := by linarith
  have := mul_lt_mul_of_pos_left hsub hpos
  linarith

/-- Each gap is integrable under the Gibbs law, since it is bounded. -/
theorem integrable_gapVector (p : Parameters) (i : Fin ((m + 1).succPNat : ℕ)) :
    Integrable (fun X : Riesz1.Configuration (m + 1).succPNat => Riesz2.gapVector X i)
      (gibbsMeasure p (m + 1).succPNat) := by
  have := gibbsMeasure_probability p (m + 1).succPNat
  refine Integrable.of_bound ?_ (((m + 1).succPNat : ℕ) : ℝ) (ae_of_all _ fun X => ?_)
  · exact ((measurable_pi_apply i).comp (Riesz1.measurable_gapVector _)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (le_of_lt (gapVector_pos X i))]
    exact le_of_lt (gapVector_lt X i)

/-- Cyclic relabelling does not change the mean of a gap under the Gibbs law. -/
theorem integral_gapVector_finRotate (p : Parameters) (i : Fin ((m + 1).succPNat : ℕ)) :
    ∫ X, Riesz2.gapVector X (finRotate ((m + 1).succPNat : ℕ) i) ∂gibbsMeasure p (m + 1).succPNat =
      ∫ X, Riesz2.gapVector X i ∂gibbsMeasure p (m + 1).succPNat := by
  have hmeas : Measurable (fun X : Riesz1.Configuration (m + 1).succPNat =>
      Riesz2.gapVector X i) :=
    (measurable_pi_apply i).comp (Riesz1.measurable_gapVector _)
  have key : ∫ X, Riesz2.gapVector (cycleConfig X) i ∂gibbsMeasure p (m + 1).succPNat =
      ∫ X, Riesz2.gapVector X i ∂gibbsMeasure p (m + 1).succPNat := by
    rw [← integral_map measurable_cycleConfig.aemeasurable hmeas.aestronglyMeasurable,
      gibbsMeasure_map_cycleConfig]
  rw [← key]
  exact integral_congr_ae (ae_of_all _ fun X => (gapVector_cycleConfig X i).symm)

/-- Every gap has mean one under the Gibbs law. -/
theorem integral_gapVector_eq_one (p : Parameters) (i : Fin ((m + 1).succPNat : ℕ)) :
    ∫ X, Riesz2.gapVector X i ∂gibbsMeasure p (m + 1).succPNat = 1 := by
  have := gibbsMeasure_probability p (m + 1).succPNat
  set μ := gibbsMeasure p (m + 1).succPNat with hμ
  set c := ∫ X, Riesz2.gapVector X ⟨0, (m + 1).succPNat.pos⟩ ∂μ with hc
  have hall : ∀ k : ℕ, (hk : k < ((m + 1).succPNat : ℕ)) →
      ∫ X, Riesz2.gapVector X ⟨k, hk⟩ ∂μ = c := by
    intro k
    induction k with
    | zero => intro hk; rfl
    | succ k ih =>
      intro hk
      have hk' : k < ((m + 1).succPNat : ℕ) := by omega
      have hk2 : k + 1 < m + 1 + 1 := by simpa using hk
      have hne : (⟨k, by omega⟩ : Fin (m + 1).succ) ≠ Fin.last (m + 1) := by
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_last] at this
        omega
      have hfr : finRotate ((m + 1).succPNat : ℕ) ⟨k, hk'⟩ = ⟨k + 1, hk⟩ := by
        apply Fin.ext
        exact coe_finRotate_of_ne_last hne
      rw [← hfr, integral_gapVector_finRotate p ⟨k, hk'⟩]
      exact ih hk'
  have hsum : ∑ j : Fin ((m + 1).succPNat : ℕ), ∫ X, Riesz2.gapVector X j ∂μ =
      (((m + 1).succPNat : ℕ) : ℝ) := by
    rw [← integral_finsetSum _ fun j _ => integrable_gapVector p j]
    simp only [sum_gapVector]
    rw [integral_const, probReal_univ (μ := μ)]
    simp
  have hall_c : ∀ j : Fin ((m + 1).succPNat : ℕ), ∫ X, Riesz2.gapVector X j ∂μ = c :=
    fun j => hall j j.isLt
  simp only [hall_c, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hpos : (((m + 1).succPNat : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (m + 1).succPNat.ne_zero
  have hc1 : c = 1 := by
    have := hsum
    field_simp at this
    linarith
  rw [hall_c i, hc1]

/-- Every span of `r` consecutive gaps has mean `r` under the Gibbs law. -/
theorem integral_cyclicGapSum_eq (p : Parameters) (i : Fin ((m + 1).succPNat : ℕ)) (r : ℕ) :
    ∫ X, cyclicGapSum (m + 1).succPNat i r (Riesz2.gapVector X) ∂gibbsMeasure p (m + 1).succPNat =
      (r : ℝ) := by
  have := gibbsMeasure_probability p (m + 1).succPNat
  unfold cyclicGapSum
  rw [integral_finsetSum _ fun a _ => ?_]
  · simp only [integral_gapVector_eq_one]
    simp
  · exact (integrable_gapVector p _)

end Moments

/-! ### The finite symmetry lemma -/

/-- See Subsection 2.2 of the paper. For `s ∈ (0,1) ∪ (1,∞)`, `β > 0` and `N ≥ 2`: common rotation
preserves the Gibbs law, cyclic relabelling preserves the gap law, the first particle is uniform
on `[0,1)` and independent of the gap vector, every gap has mean one, and every span of `r ≥ 1`
consecutive gaps has mean `r`. -/
theorem finite_symmetries_and_first_gap_moments (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    (∀ t : ℝ, (gibbsMeasure p N).map (Riesz1.loopRotate N t) = gibbsMeasure p N) ∧
    (gapLaw p N).map (fun g : Fin (N : ℕ) → ℝ => fun i => g (finRotate (N : ℕ) i)) =
      gapLaw p N ∧
    (gibbsMeasure p N).map (fun X => (X.val 0, gapVector X)) =
      (volume.restrict (Ico (0 : ℝ) 1)).prod (gapLaw p N) ∧
    (∀ i : Fin (N : ℕ), Integrable (fun g : Fin (N : ℕ) → ℝ => g i) (gapLaw p N) ∧
      ∫ g, g i ∂gapLaw p N = 1) ∧
    (∀ (i : Fin (N : ℕ)) (r : ℕ), 1 ≤ r →
      Integrable (fun g : Fin (N : ℕ) → ℝ => cyclicGapSum N i r g) (gapLaw p N) ∧
        ∫ g, cyclicGapSum N i r g ∂gapLaw p N = r) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, N = (m + 1).succPNat :=
    ⟨(N : ℕ) - 2, PNat.eq (by simp only [Nat.succPNat_coe]; omega)⟩
  have hV : Measurable (Riesz2.gapVector (N := (m + 1).succPNat)) :=
    Riesz1.measurable_gapVector _
  refine ⟨fun t => gibbsMeasure_map_loopRotate p m t, gapLaw_map_finRotate p m,
    GapChart.map_rotation_gapVector p (m + 1), fun i => ⟨?_, ?_⟩, fun i r _ => ⟨?_, ?_⟩⟩
  · exact (integrable_map_measure (measurable_pi_apply i).aestronglyMeasurable
      hV.aemeasurable).mpr (integrable_gapVector p i)
  · unfold Riesz2.gapLaw
    rw [integral_map hV.aemeasurable (measurable_pi_apply i).aestronglyMeasurable]
    exact integral_gapVector_eq_one p i
  · have hmeas : Measurable (fun g : Fin ((m + 1).succPNat : ℕ) → ℝ => cyclicGapSum (m + 1).succPNat i r g) := by
      unfold cyclicGapSum
      exact Finset.measurable_sum _ fun a _ => measurable_pi_apply _
    have hint : Integrable (fun X : Riesz1.Configuration (m + 1).succPNat =>
        cyclicGapSum (m + 1).succPNat i r (Riesz2.gapVector X)) (gibbsMeasure p (m + 1).succPNat) := by
      unfold cyclicGapSum
      exact integrable_finsetSum _ fun a _ => integrable_gapVector p _
    exact (integrable_map_measure hmeas.aestronglyMeasurable hV.aemeasurable).mpr hint
  · unfold Riesz2.gapLaw
    have hmeas : Measurable (fun g : Fin ((m + 1).succPNat : ℕ) → ℝ => cyclicGapSum (m + 1).succPNat i r g) := by
      unfold cyclicGapSum
      exact Finset.measurable_sum _ fun a _ => measurable_pi_apply _
    rw [integral_map hV.aemeasurable hmeas.aestronglyMeasurable]
    exact integral_cyclicGapSum_eq p i r

end GapSymmetries
end Riesz2
end
end
