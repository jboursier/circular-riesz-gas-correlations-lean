/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.PerturbationBoundsPart2
public import Riesz2.ToMathlib.PerturbationPairingAssembly
public import Riesz2.DecayLong.PhysicalIdentityPart4
import all Riesz2.DecayLong.BoundarySchurBounds
import all Riesz2.DecayLong.BoundaryEntriesPart4

/-!
# Full physical perturbation bounds, continuation

Uniform boundary estimates and realization identities for Lemma 5.8,
using the physical conditional laws and perturbation forms.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Matrix
open scoped BigOperators ContDiff Topology MatrixOrder Classical

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.BoundaryEntries

/-- See the proof of Lemma 5.6 in the paper: the prefactor is independent
of temperature, as its physical coefficient bounds use the good event alone. -/
theorem boundary_endpoints_uniform (s : Riesz1.RieszExponent) (κ₀ : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∀ β : InverseTemperature, ∀ (n : ℕ+) (m : ℕ),
        2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
        ∀ (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ),
        2 * (n : ℕ) ≤ (M : ℕ) →
        ∀ x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
        x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀ →
        EndpointBounds s n (C * (n : ℝ) ^ (κ * ε))
          (physicalCrossing β s n m x) (physicalPrefix β s n m x)
          (physicalSuffix β s n m x) (physicalFull β s n m x) ∧
        EndpointBounds s n (C * (n : ℝ) ^ (κ * ε))
          (referenceCrossing s M hM K n hnM)
          (fun b => IntervalBoundary.prefixCoefficient M n hnM (referenceWeight s M hM K) (b.val + 1))
          (fun b => IntervalBoundary.suffixCoefficient M n hnM (referenceWeight s M hM K) (b.val + 1))
          (IntervalBoundary.fullCoefficient M n hnM (referenceWeight s M hM K)) := by
  obtain ⟨R, hR, href⟩ := reference_endpoint_bounds s
  let B := 5 / Real.log 2 + 4
  have hB : 1 ≤ B := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    dsimp [B]
    have : 0 ≤ 5 / Real.log 2 := by positivity
    linarith
  let κ := max κ₀ 0 + 6
  have hκ : 0 < κ := by dsimp [κ]; have := le_max_right κ₀ 0; linarith
  refine ⟨κ, hκ, ?_⟩
  intro ε hε
  let C := (128 + R) * B
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro β n m hn M hM hnM K hhalf x hx
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hpow : (n : ℝ) ^ ((κ₀ + 6) * ε) ≤ (n : ℝ) ^ (κ * ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [κ]; nlinarith [le_max_left κ₀ 0])
  have hp1 : 1 ≤ (n : ℝ) ^ (κ * ε) := Real.one_le_rpow hn1 (mul_nonneg hκ.le hε.le)
  have hphys : 128 * B * (n : ℝ) ^ ((κ₀ + 6) * ε) ≤ C * (n : ℝ) ^ (κ * ε) := by
    have hc : 128 * B ≤ C := by dsimp [C]; nlinarith
    exact mul_le_mul hc hpow (by positivity) (by positivity)
  have hrefC : R * B ≤ C * (n : ℝ) ^ (κ * ε) := by
    have hc : R * B ≤ C := by dsimp [C]; nlinarith
    exact hc.trans (le_mul_of_one_le_right hC.le hp1)
  have hP : EndpointBounds s n (128 * B * (n : ℝ) ^ ((κ₀ + 6) * ε))
      (physicalCrossing β s n m x) (physicalPrefix β s n m x)
      (physicalSuffix β s n m x) (physicalFull β s n m x) := by
    have hc : 128 * (n : ℝ) ^ ((κ₀ + 6) * ε) ≤
        128 * B * (n : ℝ) ^ ((κ₀ + 6) * ε) := by gcongr; nlinarith
    refine ⟨fun b => ⟨(physical_prefix_bound β s ε κ₀ hε.le n m hn x hx b).trans ?_,
      (physical_suffix_bound β s ε κ₀ hε.le n m hn x hx b).trans ?_⟩, ?_, ?_⟩
    · gcongr
    · gcongr
      exact Real.rpow_nonneg (suffix_length_nonneg n _) _
    · apply (physical_full_bound β s n m hn ε κ₀ x hx).trans
      have hp := Real.rpow_le_rpow_of_exponent_le hn1
        (show κ₀ * ε ≤ (κ₀ + 6) * ε by nlinarith)
      have hc1 : (n : ℝ) ^ (κ₀ * ε) ≤ 128 * B * (n : ℝ) ^ ((κ₀ + 6) * ε) :=
        hp.trans (le_mul_of_one_le_left (by positivity) (by nlinarith))
      exact mul_le_mul_of_nonneg_right hc1 (by positivity)
    · exact physical_diagonal_bound β s ε κ₀ hε.le n m hn x hx
  have hr := href M hM K n hnM hhalf
  have hQ : EndpointBounds s n (R * B) (referenceCrossing s M hM K n hnM)
      (fun b => IntervalBoundary.prefixCoefficient M n hnM (referenceWeight s M hM K) (b.val + 1))
      (fun b => IntervalBoundary.suffixCoefficient M n hnM (referenceWeight s M hM K) (b.val + 1))
      (IntervalBoundary.fullCoefficient M n hnM (referenceWeight s M hM K)) := by
    have hc : R ≤ R * B := le_mul_of_one_le_right hR.le hB
    refine ⟨fun b => ⟨(hr.1 b).1.trans ?_, (hr.1 b).2.trans ?_⟩, hr.2.1.trans ?_, hr.2.2⟩
    all_goals gcongr
    all_goals exact Real.rpow_nonneg (suffix_length_nonneg n _) _
  exact ⟨endpointBounds_mono_internal s n hphys _ _ _ _ hP,
    endpointBounds_mono_internal s n hrefC _ _ _ _ hQ⟩


/-- See Lemma 5.6 of the paper: temperature-uniform boundary entries
and column increments, with the loss fixed before tolerance. -/
theorem boundary_intervals_uniform (s : Riesz1.RieszExponent) (κ₀ : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∀ β : InverseTemperature, ∀ (n : ℕ+) (m : ℕ),
        2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
        ∀ (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ),
        2 * (n : ℕ) ≤ (M : ℕ) →
        ∀ x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
        x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀ → ∀ i j l : Fin (n : ℕ),
        |boundaryRemainder β s n m M hM hnM K x i j| ≤
          C * (n : ℝ) ^ (κ * ε) *
            ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val / 2) *
            ((min (j.val + 1) ((n : ℕ) - j.val) : ℕ) : ℝ) ^ (-s.val / 2) ∧
        |boundaryRemainder β s n m M hM hnM K x i j -
          boundaryRemainder β s n m M hM hnM K x i l| ≤
          C * (n : ℝ) ^ (κ * ε) * (Nat.dist j.val l.val : ℝ) *
            ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val / 2) *
            (min (((min (j.val + 1) ((n : ℕ) - j.val) : ℕ) : ℝ))
              (((min (l.val + 1) ((n : ℕ) - l.val) : ℕ) : ℝ))) ^ (-1 - s.val / 2) := by
  obtain ⟨κ, hκ, hb⟩ := boundary_endpoints_uniform s κ₀
  refine ⟨κ + 1, by linarith, ?_⟩
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := hb ε hε
  let A := Real.log 2 + 1 / ε + 1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 1 ≤ A := by dsimp [A]; have := one_div_pos.mpr hε; linarith
  refine ⟨2 * C * A, by positivity, ?_⟩
  intro β n m hn M hM hnM K hhalf x hx i j l
  let E := C * (n : ℝ) ^ (κ * ε)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hp := physicalCrossing_grouped β s n m hn x
  have hr := referenceCrossing_grouped s M hM K n hnM hhalf
  obtain ⟨hP, hR⟩ := hbound β n m hn M hM hnM K hhalf x hx
  have hPG : EndpointBounds s n E
      (groupedBoundaryMatrix n (physicalPrefix β s n m x) (physicalSuffix β s n m x)
        (physicalFull β s n m x))
      (physicalPrefix β s n m x) (physicalSuffix β s n m x) (physicalFull β s n m x) := by
    simpa only [← hp] using hP
  have hRG : EndpointBounds s n E
      (groupedBoundaryMatrix n
        (fun b => IntervalBoundary.prefixCoefficient M n hnM (referenceWeight s M hM K) (b.val + 1))
        (fun b => IntervalBoundary.suffixCoefficient M n hnM (referenceWeight s M hM K) (b.val + 1))
        (IntervalBoundary.fullCoefficient M n hnM (referenceWeight s M hM K)))
      (fun b => IntervalBoundary.prefixCoefficient M n hnM (referenceWeight s M hM K) (b.val + 1))
      (fun b => IntervalBoundary.suffixCoefficient M n hnM (referenceWeight s M hM K) (b.val + 1))
      (IntervalBoundary.fullCoefficient M n hnM (referenceWeight s M hM K)) := by
    simpa only [← hr] using hR
  have hpu (b) : 0 ≤ physicalPrefix β s n m x b := physicalGroup_nonneg β s n m x _
  have hpv (b) : 0 ≤ physicalSuffix β s n m x b := physicalGroup_nonneg β s n m x _
  have hpd : 0 ≤ physicalFull β s n m x := physicalGroup_nonneg β s n m x _
  have hru (b : Fin ((n : ℕ) - 1)) :=
    (referenceCoefficients_nonneg s M hM K n hnM (b.val + 1)).1
  have hrv (b : Fin ((n : ℕ) - 1)) :=
    (referenceCoefficients_nonneg s M hM K n hnM (b.val + 1)).2.1
  have hrd := (referenceCoefficients_nonneg s M hM K n hnM 0).2.2
  have hpe := grouped_entry_bound_internal s n E hE _ _ _ hpu hpv hpd hPG i j
  have hre := grouped_entry_bound_internal s n E hE _ _ _ hru hrv hrd hRG i j
  have hpi := grouped_increment_bound_internal s n E hE _ _ _ hpu hpv hPG i j l
  have hri := grouped_increment_bound_internal s n E hE _ _ _ hru hrv hRG i j l
  rw [← hp] at hpe hpi
  rw [← hr] at hre hri
  have hlog : Real.log (2 * (n : ℝ)) ≤ A * (n : ℝ) ^ ε := by
    have hnε : 1 ≤ (n : ℝ) ^ ε := Real.one_le_rpow hn1 hε.le
    have hl := Real.log_le_rpow_div hn0.le hε
    rw [div_eq_mul_inv] at hl
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0.ne']
    dsimp [A]
    rw [one_div]
    nlinarith [mul_le_mul_of_nonneg_left hnε hlog2.le]
  have hpow : (n : ℝ) ^ (κ * ε) * (n : ℝ) ^ ε = (n : ℝ) ^ ((κ + 1) * ε) := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  have hfac : 2 * E * Real.log (2 * (n : ℝ)) ≤ 2 * C * A * (n : ℝ) ^ ((κ + 1) * ε) := by
    calc
      _ ≤ 2 * E * (A * (n : ℝ) ^ ε) := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = _ := by dsimp [E]; rw [← hpow]; ring
  have hfac' : 2 * E ≤ 2 * C * A * (n : ℝ) ^ ((κ + 1) * ε) := by
    have hpε : (n : ℝ) ^ (κ * ε) ≤ (n : ℝ) ^ ((κ + 1) * ε) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by nlinarith)
    calc
      _ ≤ 2 * C * (n : ℝ) ^ ((κ + 1) * ε) := by dsimp [E]; nlinarith
      _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hA) (Real.rpow_nonneg hn0.le ((κ + 1) * ε))]
  constructor
  · change |physicalCrossing β s n m x i j - referenceCrossing s M hM K n hnM i j| ≤ _
    apply (abs_sub _ _).trans
    apply (add_le_add hpe hre).trans
    calc
      _ = (2 * E * Real.log (2 * (n : ℝ))) *
          ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val / 2) *
          ((min (j.val + 1) ((n : ℕ) - j.val) : ℕ) : ℝ) ^ (-s.val / 2) := by ring
      _ ≤ _ := by gcongr
  · change |(physicalCrossing β s n m x i j - referenceCrossing s M hM K n hnM i j) -
      (physicalCrossing β s n m x i l - referenceCrossing s M hM K n hnM i l)| ≤ _
    have heq : (physicalCrossing β s n m x i j - referenceCrossing s M hM K n hnM i j) -
        (physicalCrossing β s n m x i l - referenceCrossing s M hM K n hnM i l) =
        (physicalCrossing β s n m x i j - physicalCrossing β s n m x i l) -
        (referenceCrossing s M hM K n hnM i j - referenceCrossing s M hM K n hnM i l) := by ring
    rw [heq]
    apply (abs_sub _ _).trans
    apply (add_le_add hpi hri).trans
    calc
      _ = (2 * E) * (Nat.dist j.val l.val : ℝ) *
          ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-s.val / 2) *
          (min (((min (j.val + 1) ((n : ℕ) - j.val) : ℕ) : ℝ))
            (((min (l.val + 1) ((n : ℕ) - l.val) : ℕ) : ℝ))) ^ (-1 - s.val / 2) := by ring
      _ ≤ _ := by gcongr

end Riesz2.BoundaryEntries

namespace Riesz2.PerturbationBounds

/-- See Lemma 5.8 of the paper: both boundary pairings with a prefactor
uniform over all positive temperatures. -/
theorem boundary_bilinear_uniform (s : Riesz1.RieszExponent) (κ₀ : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∀ β : InverseTemperature, ∀ (n : ℕ+) (m : ℕ),
      2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ),
      2 * (n : ℕ) ≤ (M : ℕ) →
      ∀ (ν : Measure (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)))
        (φ η : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → ℝ),
      Measurable φ → Measurable η → MemLp φ 2 ν → MemLp η 2 ν →
      ∀ i j l : Fin (n : ℕ),
        let G := GoodBlocks.properGoodEvent β s n m ε κ₀
        let R := BoundaryEntries.boundaryRemainder β s n m M hM hnM K
        let d := fun a : Fin (n : ℕ) => ((min (a.val + 1) ((n : ℕ) - a.val) : ℕ) : ℝ)
        let L := Real.sqrt (∫ x, φ x ^ 2 ∂ν) * Real.sqrt (∫ x, η x ^ 2 ∂ν)
        IntegrableOn (fun x => φ x * η x * R x i j) G ν ∧
        |∫ x in G, φ x * η x * R x i j ∂ν| ≤
          C * (n : ℝ) ^ (κ * ε) * (d i) ^ (-s.val / 2) * (d j) ^ (-s.val / 2) * L ∧
        IntegrableOn (fun x => φ x * η x * (R x i j - R x i l)) G ν ∧
        |∫ x in G, φ x * η x * (R x i j - R x i l) ∂ν| ≤
          C * (n : ℝ) ^ (κ * ε) * (Nat.dist j.val l.val : ℝ) *
            (d i) ^ (-s.val / 2) * (min (d j) (d l)) ^ (-1 - s.val / 2) * L := by
  obtain ⟨κ, hκ, ht⟩ := BoundaryEntries.boundary_intervals_uniform s κ₀
  refine ⟨κ, hκ, fun ε hε => ?_⟩
  obtain ⟨C, hC, hb⟩ := ht ε hε
  refine ⟨C, hC, ?_⟩
  intro β n m hper M hM hnM K hhalf ν φ η hφ hη hφ2 hη2 i j l G R d L
  have hG : MeasurableSet G := GoodBlocks.measurableSet_properGoodEvent β s n m ε κ₀
  have hR (a b : Fin (n : ℕ)) : Measurable (fun x => R x a b) :=
    (BoundaryEntries.measurable_physicalCrossing β s n m a b).sub measurable_const
  obtain ⟨hi, hentry⟩ := PolynomialProfileTruncation.bounded_coefficient_pair
    hG (hR i j)
    (show 0 ≤ C * (n : ℝ) ^ (κ * ε) * (d i) ^ (-s.val / 2) * (d j) ^ (-s.val / 2) by positivity)
    (fun x hx => (hb β n m hper M hM hnM K hhalf x hx i j l).1) hφ hη hφ2 hη2
  obtain ⟨hi', hinc⟩ := PolynomialProfileTruncation.bounded_coefficient_pair
    hG ((hR i j).sub (hR i l))
    (show 0 ≤ C * (n : ℝ) ^ (κ * ε) * (Nat.dist j.val l.val : ℝ) *
      (d i) ^ (-s.val / 2) * (min (d j) (d l)) ^ (-1 - s.val / 2) by positivity)
    (fun x hx => (hb β n m hper M hM hnM K hhalf x hx i j l).2) hφ hη hφ2 hη2
  exact ⟨hi, hentry, hi', hinc⟩


end Riesz2.PerturbationBounds

namespace Riesz2.BoundarySchurBounds

/-- See Lemma 5.5 of the paper: the cutoff resolvent estimate has one prefactor
for every temperature bounded below by βlo. -/
theorem bilinear_schur_cutoff_uniform (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (βlo : ℝ) (hlo : 0 < βlo) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) (hβlo : βlo ≤ β), ∀ (m : ℕ+) (hm : 2 ≤ (m : ℕ)) (K : ℕ),
      ∀ (hK : 1 ≤ K) (hKm : K ≤ (m : ℕ) / 4), ∀ n : ℕ, n ≤ (m : ℕ) →
      ∀ {α : Type} [MeasurableSpace α] (ν : Measure α)
        (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q),
      let E := Finset.univ.filter (fun j : Fin (m : ℕ) => n ≤ j.val)
      let D : Matrix E E ℝ := ((2 : ℝ) • referenceIntervalMatrix s m hm K).submatrix
        (Subtype.val : E → Fin (m : ℕ)) Subtype.val
      let hD := (ExteriorForces.exteriorBlock_posDef s m hm hK hKm E).1
      let col := fun (i : Fin (m : ℕ)) (a : E) => 2 * referenceIntervalMatrix s m hm K i a.val
      let F := constantForm Q hQ (β • D) (hD.posSemidef.smul (hlo.le.trans hβlo))
      let J := OperatorSchur.vectorValues (ι := E) Q hQ
      ∃ R : PiLp 2 (fun _ : E => Lp ℝ 2 ν) →L[ℝ] MatrixEnergy.Vector (ι := E) Q hQ,
        (∀ f w, F (R f) w = inner ℝ f (J w)) ∧
        (∀ f u, (∀ w, F u w = inner ℝ f (J w)) → u = R f) ∧
        ∀ (η φ : Lp ℝ 2 ν) (i j l : Fin (m : ℕ)),
          i.val < n → j.val < n → l.val < n →
          |inner ℝ (tensor (col j) η) (J (R (tensor (col i) φ)))| ≤
            C * (K : ℝ) ^ 2 * (min (i.val + 1) (n - i.val) : ℕ) ^ (-s.val / 2) *
              (min (j.val + 1) (n - j.val) : ℕ) ^ (-s.val / 2) * ‖η‖ * ‖φ‖ ∧
          |inner ℝ (tensor (col j - col l) η) (J (R (tensor (col i) φ)))| ≤
            C * (K : ℝ) ^ 2 * (Nat.dist j.val l.val : ℝ) *
              (min (i.val + 1) (n - i.val) : ℕ) ^ (-s.val / 2) *
              (min (min (j.val + 1) (n - j.val)) (min (l.val + 1) (n - l.val)) : ℕ) ^
                (-1 - s.val / 2) * ‖η‖ * ‖φ‖ := by
  obtain ⟨B, hB, hforce⟩ := ExteriorForces.exterior_force_bounds hz s
  refine ⟨βlo⁻¹ * B ^ 2, by positivity, ?_⟩
  intro β hβlo m hm K hK hKm n hn α _ ν Q hQ
  have hβ : 0 < β := hlo.trans_le hβlo
  dsimp only
  let E := Finset.univ.filter (fun j : Fin (m : ℕ) => n ≤ j.val)
  let D : Matrix E E ℝ := ((2 : ℝ) • referenceIntervalMatrix s m hm K).submatrix
    (Subtype.val : E → Fin (m : ℕ)) Subtype.val
  let col := fun (i : Fin (m : ℕ)) (a : E) => 2 * referenceIntervalMatrix s m hm K i a.val
  have hD := (ExteriorForces.exteriorBlock_posDef s m hm hK hKm E).1
  obtain ⟨a, ha, hlow⟩ := reference_exterior_lower s m hm K hK hKm E β hβ
  let F := constantForm Q hQ (β • D) (hD.posSemidef.smul hβ.le)
  let J := OperatorSchur.vectorValues (ι := E) Q hQ
  let R := CoerciveSolution.solution F (min 1 a) (lt_min zero_lt_one ha)
    (constantForm_coercive Q hQ _ _ a hlow) J
  refine ⟨R, CoerciveSolution.solution_solves _ _ _ _ _, ?_, ?_⟩
  · intro f u hu
    apply CoerciveSolution.inverse_unique F (min 1 a) (lt_min zero_lt_one ha)
      (constantForm_coercive Q hQ _ _ a hlow)
    exact hu
  intro η φ i j l hi hj hl
  obtain ⟨hpoint, hinc⟩ := hforce m hm K hK hKm n hn
  dsimp only at hpoint hinc
  have hq (k : Fin (m : ℕ)) (hk : k.val < n) :
      col k ⬝ᵥ (D⁻¹ *ᵥ col k) ≤
        (B * K * (min (k.val + 1) (n - k.val) : ℕ) ^ (-s.val / 2)) ^ 2 := by
    rw [← gaussian_quadratic_norm hD.inv.posSemidef (col k)]
    exact pow_le_pow_left₀ (ENNReal.toReal_nonneg) (hpoint k hk).2 2
  have hqi : (col j - col l) ⬝ᵥ (D⁻¹ *ᵥ (col j - col l)) ≤
      (B * K * (Nat.dist j.val l.val : ℝ) *
        (min (min (j.val + 1) (n - j.val)) (min (l.val + 1) (n - l.val)) : ℕ) ^
          (-1 - s.val / 2)) ^ 2 := by
    rw [← gaussian_quadratic_norm hD.inv.posSemidef (col j - col l)]
    have heq : (fun z : EuclideanSpace ℝ E => ∑ t, (col j - col l) t * z t) =
        ((fun z : EuclideanSpace ℝ E => ∑ t, col j t * z t) -
          (fun z : EuclideanSpace ℝ E => ∑ t, col l t * z t)) := by
      funext z
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    rw [heq]
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg (hinc j l hj hl).2 2
  constructor
  · have h := constant_resolvent_pair Q hQ hD β hβ a ha hlow (col j) (col i) η φ _ _
      (by positivity) (by positivity) (hq j hj) (hq i hi)
    dsimp only at h
    apply h.trans
    have hinv : β⁻¹ ≤ βlo⁻¹ := inv_anti₀ hlo hβlo
    calc
      _ ≤ βlo⁻¹ * _ * _ * ‖η‖ * ‖φ‖ := by gcongr
      _ = _ := by ring
  · have h := constant_resolvent_pair Q hQ hD β hβ a ha hlow (col j - col l) (col i) η φ _ _
      (by positivity) (by positivity) hqi (hq i hi)
    dsimp only at h
    apply h.trans
    have hinv : β⁻¹ ≤ βlo⁻¹ := inv_anti₀ hlo hβlo
    calc
      _ ≤ βlo⁻¹ * _ * _ * ‖η‖ * ‖φ‖ := by gcongr
      _ = _ := by ring



end Riesz2.BoundarySchurBounds

namespace Riesz2.PerturbationBounds

/-- See Subsection 5.1 of the paper, internal identification of the two dual Schur
pairings. The symmetric resolvent lets the estimate use the source on the
first index or on the second index with exactly the same value. -/
theorem schur_pair_symm_internal {α ι : Type*} [MeasurableSpace α]
    [Fintype ι] [DecidableEq ι] {ν : Measure α}
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (D : Matrix ι ι ℝ) (hD : D.PosSemidef)
    (R : PiLp 2 (fun _ : ι => Lp ℝ 2 ν) →L[ℝ] MatrixEnergy.Vector (ι := ι) Q hQ)
    (hR : ∀ f w, BoundarySchurBounds.constantForm Q hQ D hD (R f) w =
      inner ℝ f (OperatorSchur.vectorValues Q hQ w))
    (f g : PiLp 2 (fun _ : ι => Lp ℝ 2 ν)) :
    inner ℝ f (OperatorSchur.vectorValues Q hQ (R g)) =
      inner ℝ g (OperatorSchur.vectorValues Q hQ (R f)) := by
  rw [← hR f (R g), BoundarySchurBounds.constantForm_symmetric Q hQ D hD, hR g (R f)]

/-- See Lemma 5.8 of the paper: compensated forces and their covariance
are independent of the ambient realization, since the energy is fixed
on the entire open ambient domain. Equality holds on every conditional fibre. -/
theorem force_realization_eq (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ)
    (U W : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ)
    (hU : ∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) //
        y ∈ gapAmbientDomain ((n : ℕ) + m).succPNat},
      U y.val = β.val * physicalAmbientGapEnergy (ofLong β s) ((n : ℕ) + m).succPNat y)
    (hW : ∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) //
        y ∈ gapAmbientDomain ((n : ℕ) + m).succPNat},
      W y.val = β.val * physicalAmbientGapEnergy (ofLong β s) ((n : ℕ) + m).succPNat y)
    (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :
    ∀ᵐ z ∂ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x,
      fderiv ℝ U (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) =
      fderiv ℝ W (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) := by
  filter_upwards [PhysicalIdentity.Internal.conditional_simplex β s n m x] with z hz
  have hy := PhysicalEnergy.simplex_subset_ambient ((n : ℕ) + m).succPNat _ hz
  have heq : U =ᶠ[𝓝 (RetainedSimplex.chart n m ((n + m : ℕ) + 1)
      (Equiv.refl _) (x.val,z))] W := by
    filter_upwards [(PhysicalEnergy.isOpen_gapAmbientDomain _).mem_nhds hy] with y hy
    exact (hU ⟨y,hy⟩).trans (hW ⟨y,hy⟩).symm
  exact heq.fderiv_eq

/-- See Subsection 5.1 of the paper, multiplication part: the exact physical
Hessian-minus-core identity for any realization selected by the moment
bounds. It retains β, β, and −β² on its three signed terms. -/
theorem multiplication_defect_any (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε κ₀ : ℝ)
    (U : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) → ℝ)
    (hU : ∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ) + m + 1)) //
        y ∈ gapAmbientDomain ((n : ℕ) + m).succPNat},
      U y.val = β.val * physicalAmbientGapEnergy (ofLong β s) ((n : ℕ) + m).succPNat y) :
    let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      β.val * ∑ i, θ.val ((n : ℝ) ^ (-ε) * x i) -
        Real.log (∫ z : EuclideanSpace ℝ (Fin m),
          (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (x,z)).toReal)
    ∀ x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1),
      let μ := ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x
      let q := WithLp.toLp 2 (ConditionalForces.compensationVector n m)
      let Xi := fun i z => β.val⁻¹ *
        (fderiv ℝ U (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z))
            (EuclideanSpace.single (i.castAdd m).castSucc 1) -
         fderiv ℝ U (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) q)
      ∀ (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : (n : ℕ) ≤ (M : ℕ))
        (K : ℕ) (i j : Fin (n : ℕ)),
        hessianMatrix V x.val i j -
          β.val * PhysicalCore.properActive β s n m M hM hnM K θ ε κ₀ x i j =
        β.val * (if x ∈ GoodBlocks.properGoodEvent β s n m ε κ₀ then
            BoundaryEntries.boundaryRemainder β s n m M hM hnM K x i j
          else PhysicalCore.forcingHessian n θ ε x.val i j +
            GoodBlocks.conditionalHessian β s n m i j x -
            2 * referenceIntervalMatrix s M hM K (i.castLE hnM) (j.castLE hnM)) +
        β.val * ConditionalForces.compensationQ β s n m i j x -
        β.val ^ 2 * ProbabilityTheory.covariance (Xi i) (Xi j) μ := by
  intro V
  obtain ⟨W, _, hW, hdef⟩ := PhysicalIdentity.proper_multiplication_defect β s n m θ ε κ₀
  intro x μ q Xi M hM hnM K i j
  have heq := force_realization_eq β s n m U W hU hW x
  have hXi (a : Fin (n : ℕ)) : Xi a =ᵐ[μ] (fun z => β.val⁻¹ *
      (fderiv ℝ W (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z))
        (EuclideanSpace.single (a.castAdd m).castSucc 1) -
       fderiv ℝ W (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) q)) := by
    filter_upwards [heq] with z hz
    simp only [Xi, hz]
  let XW := fun (a : Fin (n : ℕ)) z => β.val⁻¹ *
      (fderiv ℝ W (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z))
        (EuclideanSpace.single (a.castAdd m).castSucc 1) -
       fderiv ℝ W (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z)) q)
  have hcov : ProbabilityTheory.covariance (Xi i) (Xi j) μ =
      ProbabilityTheory.covariance (XW i) (XW j) μ := by
    unfold ProbabilityTheory.covariance
    rw [integral_congr_ae (hXi i), integral_congr_ae (hXi j)]
    apply integral_congr_ae
    filter_upwards [hXi i, hXi j] with z hi hj
    rw [hi, hj]
  rw [hcov]
  exact (hdef x).2 M hM hnM K i j

end Riesz2.PerturbationBounds

namespace Riesz2.PerturbationBounds

/-- See Lemma 5.8 of the paper, complete proper-window multiplication
part of `T`: the actual Hessian-minus-core, with its signed β factors.
Constants are uniform on compact temperature intervals, and the loss is
chosen before temperature and tolerance. -/
theorem proper_multiplication_bilinear (hRig : External.LongRangeRigidityLocallyUniform)
    (s : Riesz1.RieszExponent) (κ₀ : ℝ) (hκ₀ : 1 ≤ κ₀) :
    ∃ κ > 0, ∀ (ε Cθ βlo βhi : ℝ),
      0 < ε → 1 ≤ Cθ → 0 < βlo → βlo ≤ βhi →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n : ℕ+) (m : ℕ), 2 ≤ (n : ℕ) → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : (n : ℕ) ≤ (M : ℕ)) (K : ℕ),
      2 * (n : ℕ) ≤ (M : ℕ) → (M : ℝ) ≤ 3 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
      let ν := (activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n hn θ ε false).comap
        ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
      let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
        β.val * ∑ i, θ.val ((n : ℝ) ^ (-ε) * x i) -
          Real.log (∫ z : EuclideanSpace ℝ (Fin m),
            (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (x,z)).toReal)
      let D := fun (i j : Fin (n : ℕ)) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) =>
        hessianMatrix V x.val i j - β.val * PhysicalCore.properActive β s n m M hM hnM K θ ε κ₀ x i j
      ∀ (φ η : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → ℝ) (Mφ Mη : ℝ),
        Measurable φ → Measurable η → 0 ≤ Mφ → 0 ≤ Mη →
        (∀ᵐ x ∂ν, |φ x| ≤ Mφ) → (∀ᵐ x ∂ν, |η x| ≤ Mη) →
      ∀ i j l : Fin (n : ℕ),
        let d := fun a : Fin (n : ℕ) => ((min (a.val + 1) ((n : ℕ) - a.val) : ℕ) : ℝ)
        let L := Real.sqrt (∫ x, φ x ^ 2 ∂ν) * Real.sqrt (∫ x, η x ^ 2 ∂ν)
        let E := C * Real.exp (-c * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη)
        Integrable (fun x => φ x * η x * D i j x) ν ∧
        |∫ x, φ x * η x * D i j x ∂ν| ≤
          C * (n : ℝ) ^ (κ * ε) * (d i) ^ (-s.val / 2) * (d j) ^ (-s.val / 2) * L + E ∧
        Integrable (fun x => φ x * η x * (D i j x - D i l x)) ν ∧
        |∫ x, φ x * η x * (D i j x - D i l x) ∂ν| ≤
          C * (n : ℝ) ^ (κ * ε) * (Nat.dist j.val l.val : ℝ) *
            (d i) ^ (-s.val / 2) * (min (d j) (d l)) ^ (-1 - s.val / 2) * L + E := by
  obtain ⟨kb, hkb, hb⟩ := boundary_bilinear_uniform s κ₀
  obtain ⟨kv, hkv, hv⟩ := covariance_bilinear hRig s κ₀ hκ₀
  let κ := kb + kv + 1
  have hκ : 0 < κ := by dsimp [κ]; linarith
  refine ⟨κ, hκ, fun ε Cθ βlo βhi hε hCθ hlo hle => ?_⟩
  obtain ⟨Cb, hCb, hbound⟩ := hb ε hε
  obtain ⟨Cv, cv, hCv, hcv, hcov⟩ := hv ε Cθ βlo βhi hε hCθ hlo hle
  obtain ⟨Cq, cq, hCq, hcq, hcomp⟩ := compensation_bilinear s βlo βhi ε Cθ hlo hle hε hCθ
  obtain ⟨Cf, cf, hCf, hcf, hfreeze⟩ := proper_freezing_bilinear hRig s ε Cθ βlo βhi hε hCθ hlo hle
  let c := min cf (min cq cv)
  let C := βhi * (Cb + Cf + Cq) + βhi ^ 2 * Cv
  have hC : 0 < C := by have hhi := hlo.trans_le hle; dsimp [C]; positivity
  have hc : 0 < c := lt_min hcf (lt_min hcq hcv)
  refine ⟨C, c, hC, hc, ?_⟩
  intro β hβ n m hn2 hper hn θ hcurv M hM hnM K hhalf hscale ν V D φ η Mφ Mη
    hφ hη hMφ hMη hφM hηM i j l d L E
  have : IsProbabilityMeasure ν := GoodBlocks.proper_active_probability _ _ _ _ _ _
  have hφ2 : MemLp φ 2 ν := MemLp.of_bound hφ.aestronglyMeasurable Mφ
    (by simpa only [Real.norm_eq_abs] using hφM)
  have hη2 : MemLp η 2 ν := MemLp.of_bound hη.aestronglyMeasurable Mη
    (by simpa only [Real.norm_eq_abs] using hηM)
  obtain ⟨U, _, hU, _, hY⟩ := hcov β hβ n m hper hn θ hcurv
  let Xi := fun (a : Fin (n : ℕ)) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) z =>
    β.val⁻¹ * (fderiv ℝ U (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z))
      (EuclideanSpace.single (a.castAdd m).castSucc 1) -
      fderiv ℝ U (RetainedSimplex.chart n m ((n + m : ℕ) + 1) (Equiv.refl _) (x.val,z))
        (WithLp.toLp 2 (ConditionalForces.compensationVector n m)))
  let Y := fun a b x => ProbabilityTheory.covariance (Xi a x) (Xi b x)
    (ProperMarginalChart.conditionalMeasure (ofLong β s) n m n.pos (Equiv.refl _) x)
  let G := GoodBlocks.properGoodEvent β s n m ε κ₀
  let B := fun a b x => BoundaryEntries.boundaryRemainder β s n m M hM hnM K x a b
  let F := fun a b x => PhysicalCore.forcingHessian n θ ε x.val a b +
    GoodBlocks.conditionalHessian β s n m a b x -
      2 * referenceIntervalMatrix s M hM K (a.castLE hnM) (b.castLE hnM)
  let Q := ConditionalForces.compensationQ β s n m
  have hG : MeasurableSet G := GoodBlocks.measurableSet_properGoodEvent β s n m ε κ₀
  have hD (a b) (x) : D a b x = β.val * (if x ∈ G then B a b x else F a b x) +
      β.val * Q a b x - β.val ^ 2 * Y a b x :=
    multiplication_defect_any β s n m θ ε κ₀ U hU x M hM hnM K a b
  obtain ⟨hbI, hbP, hbJ, hbR⟩ := hbound β n m hper M hM hnM K hhalf ν φ η hφ hη hφ2 hη2 i j l
  obtain ⟨hfI, hfP, hfJ, hfR⟩ := hfreeze β hβ n m hper hn θ hcurv M hM hnM K hscale κ₀ hκ₀
    φ η Mφ Mη hφ hη hMφ hMη hφM hηM i j l
  obtain ⟨hqI, hqP, hqJ, hqR⟩ := hcomp β hβ n m hn2 hper hn θ hcurv
    φ η Mφ Mη hφ hη hMφ hMη hφM hηM i j l
  obtain ⟨hyI, hyP, hyJ, hyR⟩ := hY φ η Mφ Mη hφ hη hMφ hMη hφM hηM i j l
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hpowb : (n : ℝ) ^ (kb * ε) ≤ (n : ℝ) ^ (κ * ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [κ]; nlinarith only [hkv, hε])
  have hpowq : (n : ℝ) ^ ε ≤ (n : ℝ) ^ (κ * ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [κ]; nlinarith only [hkb, hkv, hε])
  have hpowv : (n : ℝ) ^ (kv * ε) ≤ (n : ℝ) ^ (κ * ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [κ]; nlinarith only [hkb, hε])
  let Z := Real.exp (-c * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη)
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have herr (a : ℝ) (ha : c ≤ a) (A : ℝ) (hA : 0 ≤ A) :
      A * Real.exp (-a * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη) ≤ A * Z := by
    calc
      _ ≤ A * Real.exp (-c * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hMφ hMη)
        apply mul_le_mul_of_nonneg_left _ hA
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right (neg_le_neg ha) (by positivity)
      _ = A * Z := by dsimp [Z]; ring
  have hqE := herr cq ((min_le_right cf (min cq cv)).trans (min_le_left cq cv)) Cq hCq.le
  have hvE := herr cv ((min_le_right cf (min cq cv)).trans (min_le_right cq cv)) Cv hCv.le
  have hfE := herr cf (min_le_left cf (min cq cv)) Cf hCf.le
  have hs (w : ℝ) (hw : 0 ≤ w)
      (bp : ℝ) (hbp : bp ≤ Cb * (n : ℝ) ^ (kb * ε) * w * L)
      (qp : ℝ) (hqp : qp ≤ Cq * (n : ℝ) ^ ε * w * L +
        Cq * Real.exp (-cq * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη))
      (yp : ℝ) (hyp : yp ≤ Cv * (n : ℝ) ^ (kv * ε) * w * L +
        Cv * Real.exp (-cv * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη)) :
      bp ≤ Cb * ((n : ℝ) ^ (κ * ε) * w * L) ∧
      qp ≤ Cq * ((n : ℝ) ^ (κ * ε) * w * L) + Cq * Z ∧
      yp ≤ Cv * ((n : ℝ) ^ (κ * ε) * w * L) + Cv * Z := by
    have hL : 0 ≤ L := by dsimp [L]; positivity
    refine ⟨hbp.trans ?_, hqp.trans ?_, hyp.trans ?_⟩
    · calc
        _ ≤ Cb * (n : ℝ) ^ (κ * ε) * w * L := by gcongr
        _ = _ := by ring
    · apply add_le_add _ hqE
      calc
        _ ≤ Cq * (n : ℝ) ^ (κ * ε) * w * L := by gcongr
        _ = _ := by ring
    · apply add_le_add _ hvE
      calc
        _ ≤ Cv * (n : ℝ) ^ (κ * ε) * w * L := by gcongr
        _ = _ := by ring
  let w := (d i) ^ (-s.val / 2) * (d j) ^ (-s.val / 2)
  have hw : 0 ≤ w := by dsimp [w, d]; positivity
  obtain ⟨hbP', hqP', hyP'⟩ := hs w hw _ (by simpa only [w, mul_assoc] using hbP)
    _ (by simpa only [w, mul_assoc] using hqP) _ (by simpa only [w, mul_assoc] using hyP)
  have hentry := PerturbationPairingAssembly.multiplication_internal hG hbI hfI hqI hyI
    (P := (n : ℝ) ^ (κ * ε) * w * L) (E := Z)
    (d := fun x => φ x * η x * D i j x) (fun x => by rw [hD]; split_ifs <;> simp only [B, F, Q] <;> ring)
    β.property.le hβ.2 (by dsimp [w, L, d]; positivity) hZ hCb.le hCf.le hCq.le hCv.le
    (by simpa only [mul_assoc] using hbP') (hfP.trans hfE)
    (by simpa only [mul_assoc] using hqP') (by simpa only [mul_assoc] using hyP')
  let v := (Nat.dist j.val l.val : ℝ) * (d i) ^ (-s.val / 2) *
    (min (d j) (d l)) ^ (-1 - s.val / 2)
  have hv0 : 0 ≤ v := by dsimp [v, d]; positivity
  obtain ⟨hbR', hqR', hyR'⟩ := hs v hv0 _ (by simpa only [v, mul_assoc] using hbR)
    _ (by simpa only [v, mul_assoc] using hqR) _ (by simpa only [v, mul_assoc] using hyR)
  have hinc := PerturbationPairingAssembly.multiplication_internal hG hbJ hfJ hqJ hyJ
    (P := (n : ℝ) ^ (κ * ε) * v * L) (E := Z)
    (d := fun x => φ x * η x * (D i j x - D i l x))
    (fun x => by rw [hD, hD]; split_ifs <;> simp only [B, F, Q] <;> ring)
    β.property.le hβ.2 (by dsimp [v, L, d]; positivity) hZ hCb.le hCf.le hCq.le hCv.le
    (by simpa only [mul_assoc] using hbR') (hfR.trans hfE)
    (by simpa only [mul_assoc] using hqR') (by simpa only [mul_assoc] using hyR')
  refine ⟨hentry.1, ?_, hinc.1, ?_⟩
  · simpa only [C, Z, E, w, mul_assoc] using hentry.2
  · simpa only [C, Z, E, v, mul_assoc] using hinc.2

end Riesz2.PerturbationBounds

namespace Riesz2.PerturbationBounds

/-- The intrinsic full-cycle law is the pushforward by the centering
map. This transports full-cycle estimates without introducing a proper fibre. -/
theorem full_intrinsic_map (p : Parameters) (N : ℕ+) (θ : PhysicalCutoff) (ε : ℝ) :
    fullIntrinsicTiltedGapLaw p N θ ε false =
      (tiltedParticleMeasure p N N le_rfl θ ε false).map
        (fun X => centeredGapChart N (WithLp.toLp 2 (gapVector X))) := by
  let T := fun X : Riesz1.Configuration N => centeredGapChart N (WithLp.toLp 2 (gapVector X))
  let Y := fun z : gapTangentSpace N => WithLp.toLp 2 (fun i => 1 + z.val i)
  have hraw (X : Riesz1.Configuration N) : Y (T X) = WithLp.toLp 2 (gapVector X) := by
    ext i
    change 1 + (gap X i.val - (∑ j : Fin (N : ℕ), gap X j.val) / (N : ℝ)) = gap X i.val
    rw [DefinitionSanity.actual_gap_sum, div_self (show (N : ℝ) ≠ 0 by exact_mod_cast N.pos.ne')]
    ring
  change ((tiltedParticleMeasure p N N le_rfl θ ε false).map
    (fun X => WithLp.toLp 2 (gapVector X))).comap Y = _
  have he : (fun X : Riesz1.Configuration N => WithLp.toLp 2 (gapVector X)) = Y ∘ T :=
    funext (fun X => (hraw X).symm)
  rw [he, ← Measure.map_map (DefinitionSanity.full_chart_embedding N).measurable
    (DefinitionSanity.intrinsic_projection_measurable N), (DefinitionSanity.full_chart_embedding N).comap_map]

/-- See Subsection 5.1 of the paper on the intrinsic full-cycle carrier. This is the
coordinate transport of `GoodBlocks.fullGoodEvent`, not the proper-window
chart at exterior dimension zero. -/
def fullIntrinsicGoodEvent (s : Riesz1.RieszExponent) (N : ℕ+) (ε κ₀ : ℝ) : Set (gapTangentSpace N) :=
  {z | ((∀ i : Fin (N : ℕ), (N : ℝ) ^ (-ε) ≤ 1 + z.val i ∧ 1 + z.val i ≤ (N : ℝ) ^ ε) ∧
    ∀ (j : Fin (N : ℕ)) (k : Fin ((N : ℕ) + 1)), 1 ≤ k.val → k.val ≤ (N : ℕ) / 2 →
      |cyclicGapSum N j k.val (fun i => 1 + z.val i) - (k.val : ℝ)| ≤
        (N : ℝ) ^ ε * (k.val : ℝ) ^ (s.val / 2)) ∧
    ∀ a b : Fin (N : ℕ), GoodBlocks.gapHessian s N a b (WithLp.toLp 2 (fun i => 1 + z.val i)) ≤
      (N : ℝ) ^ (κ₀ * ε) * (1 + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-s.val)}

/-- Measurability of the exact transported full-cycle good event. -/
theorem measurableSet_fullIntrinsicGoodEvent (s : Riesz1.RieszExponent) (N : ℕ+) (ε κ₀ : ℝ) :
    MeasurableSet (fullIntrinsicGoodEvent s N ε κ₀) := by
  have hall {ι : Type} [Countable ι] {P : ι → gapTangentSpace N → Prop}
      (h : ∀ i, MeasurableSet {x | P i x}) : MeasurableSet {x | ∀ i, P i x} := by
    simpa only [ofPred_forall] using MeasurableSet.iInter h
  have hY : Measurable (fun z : gapTangentSpace N => WithLp.toLp 2 (fun i => 1 + z.val i)) := by fun_prop
  unfold fullIntrinsicGoodEvent
  apply MeasurableSet.inter
  · apply MeasurableSet.inter
    · apply hall
      intro i
      have hi : Measurable (fun z : gapTangentSpace N => 1 + z.val i) := by fun_prop
      exact (measurableSet_le measurable_const hi).inter (measurableSet_le hi measurable_const)
    · apply hall
      intro j
      apply hall
      intro k
      by_cases h1 : 1 ≤ k.val
      · simp only [h1, true_implies]
        by_cases h2 : k.val ≤ (N : ℕ) / 2
        · simp only [h2, true_implies]
          apply measurableSet_le _ measurable_const
          have hm : Measurable (fun z : gapTangentSpace N =>
              cyclicGapSum N j k.val (fun i => 1 + z.val i)) := by
            simpa only [Function.comp_def, PhysicalEnergy.intervalLinear_apply, WithLp.ofLp_toLp] using
              ((PhysicalEnergy.intervalLinear N j k.val).continuous.measurable.comp hY)
          exact continuous_abs.measurable.comp (hm.sub_const _)
        · simp only [h2, false_implies]
          exact MeasurableSet.univ
      · simp only [h1, false_implies]
        exact MeasurableSet.univ
  · apply hall
    intro a
    apply hall
    intro b
    exact measurableSet_le ((GoodBlocks.measurable_gapHessian s N a b).comp hY) measurable_const

/-- Exact preimage equality of the intrinsic and particle full-cycle events,
including the two-particle and antipodal conventions. -/
theorem fullIntrinsicGoodEvent_preimage (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (ε κ₀ : ℝ) :
    (fun X => centeredGapChart N (WithLp.toLp 2 (gapVector X))) ⁻¹'
      fullIntrinsicGoodEvent s N ε κ₀ = GoodBlocks.fullGoodEvent (ofLong β s) N ε κ₀ := by
  ext X
  have hraw : (fun i => 1 + (centeredGapChart N (WithLp.toLp 2 (gapVector X))).val i) = gapVector X := by
    funext i
    change 1 + (gap X i.val - (∑ j : Fin (N : ℕ), gap X j.val) / (N : ℝ)) = gap X i.val
    rw [DefinitionSanity.actual_gap_sum, div_self (show (N : ℝ) ≠ 0 by exact_mod_cast N.pos.ne')]
    ring
  have hcoord (i : Fin (N : ℕ)) :
      1 + (centeredGapChart N (WithLp.toLp 2 (gapVector X))).val i = gap X i.val := congrFun hraw i
  simp only [mem_preimage, fullIntrinsicGoodEvent, mem_ofPred_eq, GoodBlocks.fullGoodEvent,
    hcoord]
  have hvec : (fun i : Fin (N : ℕ) => gap X i.val) = gapVector X := rfl
  simp only [hvec, GoodBlocks.gapHessian_particle β s, GapChart.cyclicGapSum_gapVector]
  rfl

/-- See Subsection 5.1 of the paper, full-cycle tail on the literal intrinsic carrier.
The exponent and loss parameters are retained before temperature. -/
theorem full_intrinsic_good_event (hRig : External.LongRangeRigidityLocallyUniform)
    (s : Riesz1.RieszExponent) {ε Cθ : ℝ} (hε : 0 < ε) (hCθ : 1 ≤ Cθ)
    (βlo βhi : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ N : ℕ+, 2 ≤ (N : ℕ) → ∀ θ : PhysicalCutoff,
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ κ₀ : ℝ, 1 ≤ κ₀ →
        fullIntrinsicTiltedGapLaw (ofLong β s) N θ ε false (fullIntrinsicGoodEvent s N ε κ₀)ᶜ ≤
          ENNReal.ofReal (C * Real.exp (-c * (N : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε)) := by
  obtain ⟨C, c, hC, hc, ht⟩ := GoodBlocks.full_good_event hRig s hε hCθ βlo βhi hlo hle
  refine ⟨C, c, hC, hc, fun β hβ N hN θ hcurv κ₀ hκ₀ => ?_⟩
  rw [full_intrinsic_map, Measure.map_apply (DefinitionSanity.intrinsic_projection_measurable N)
    (measurableSet_fullIntrinsicGoodEvent s N ε κ₀).compl, preimage_compl,
    fullIntrinsicGoodEvent_preimage β s N ε κ₀]
  exact ht β hβ N hN θ hcurv κ₀ hκ₀

end Riesz2.PerturbationBounds

namespace Riesz2.PerturbationBounds

/-- See Subsection 5.1 of the paper, full-cycle coefficient moments in the intrinsic
chart of the full law. -/
theorem full_intrinsic_hessian_moments (s : Riesz1.RieszExponent)
    (βlo βhi ε Cθ : ℝ) (hlo : 0 < βlo) (hle : βlo ≤ βhi) (hε : 0 < ε) (hCθ : 1 ≤ Cθ) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ N : ℕ+, 2 ≤ (N : ℕ) → ∀ θ : PhysicalCutoff,
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ (a b : Fin (N : ℕ)) (q : ℝ), 1 ≤ q →
      eLpNorm (fun z : gapTangentSpace N =>
        GoodBlocks.gapHessian s N a b (WithLp.toLp 2 (fun i => 1 + z.val i))) (ENNReal.ofReal q)
        (fullIntrinsicTiltedGapLaw (ofLong β s) N θ ε false) ≤
      ENNReal.ofReal (C * q ^ ((s.val + 2) / s.val) *
        (1 + (Riesz1.cyclicIndexDistance N a b : ℝ)) ^ (-s.val)) := by
  obtain ⟨C, hC, hm⟩ := GoodBlocks.tilted_hessian_moments s.val βlo βhi ε Cθ
    s.property.1 hlo hle hε hCθ
  refine ⟨C, hC, fun β hβ N hN θ hcurv a b q hq => ?_⟩
  have hY : Measurable (fun z : gapTangentSpace N => WithLp.toLp 2 (fun i => 1 + z.val i)) := by fun_prop
  rw [full_intrinsic_map]
  rw [eLpNorm_map_measure (g := fun z : gapTangentSpace N =>
    GoodBlocks.gapHessian s N a b (WithLp.toLp 2 (fun i => 1 + z.val i)))
    ((GoodBlocks.measurable_gapHessian s N a b).comp hY).aestronglyMeasurable
    (DefinitionSanity.intrinsic_projection_measurable N).aemeasurable]
  have heq : (fun z : gapTangentSpace N =>
      GoodBlocks.gapHessian s N a b (WithLp.toLp 2 (fun i => 1 + z.val i))) ∘
      (fun X => centeredGapChart N (WithLp.toLp 2 (gapVector X))) =
      GoodBlocks.particleHessian (ofLong β s) N a b := by
    funext X
    have hraw := DefinitionSanity.actual_gap_in_chart X
    obtain ⟨z, hz⟩ := hraw
    have he := congrArg (centeredGapChart N) hz
    rw [PhysicalCollision.centered_chart_inverse] at he
    simp only [Function.comp_apply, ← he, hz, GoodBlocks.gapHessian_particle β s]
  rw [heq]
  exact hm (ofLong β s) rfl hβ.1 hβ.2 N N hN le_rfl θ hcurv a b q hq

/-- See Section 5 of the paper: the cutoff Hessian on the intrinsic full cycle
has the prescribed curvature bound almost everywhere. -/
theorem full_forcing_bound (N : ℕ+) (θ : PhysicalCutoff) {ε Cθ : ℝ}
    (hε : 0 < ε) (hCθ : 1 ≤ Cθ)
    (hcurv : ∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ)
    (p : Parameters) (a b : Fin (N : ℕ)) :
    ∀ᵐ z ∂fullIntrinsicTiltedGapLaw p N θ ε false,
      |PhysicalCore.forcingHessian N θ ε (WithLp.toLp 2 (fun i => 1 + z.val i)) a b| ≤ Cθ := by
  rw [full_intrinsic_map]
  have hm : Measurable (fun z : gapTangentSpace N =>
      PhysicalCore.forcingHessian N θ ε (WithLp.toLp 2 (fun i => 1 + z.val i)) a b) :=
    (PhysicalCore.measurable_forcingHessian N θ ε a b).comp (by fun_prop)
  apply (ae_map_iff (DefinitionSanity.intrinsic_projection_measurable N).aemeasurable
    (measurableSet_le (continuous_abs.measurable.comp hm) measurable_const)).mpr
  apply ae_of_all
  intro X
  obtain ⟨z, hz⟩ := DefinitionSanity.actual_gap_in_chart X
  have he := congrArg (centeredGapChart N) hz
  rw [PhysicalCollision.centered_chart_inverse] at he
  change |PhysicalCore.forcingHessian N θ ε
    (WithLp.toLp 2 (fun i => 1 + (centeredGapChart N (WithLp.toLp 2 (gapVector X))).val i)) a b| ≤ Cθ
  change WithLp.toLp 2 (fun i => 1 + z.val i) = WithLp.toLp 2 (gapVector X) at hz
  rw [← he, hz]
  have hraw : WithLp.toLp 2 (gapVector X) ∈ AffineSimplex.chartDomain N ((N + 0 : ℕ) + 1) := by
    refine ⟨fun i => DefinitionSanity.gap_positive X i.val, ?_⟩
    change (∑ i : Fin (N : ℕ), gap X i.val) < (N + 0 : ℕ) + 1
    rw [DefinitionSanity.actual_gap_sum]
    push_cast
    linarith
  rw [PhysicalCore.forcingHessian_apply N 0 θ ε ⟨_,hraw⟩ a b]
  split_ifs
  · have hn0 : (0 : ℝ) < N := by exact_mod_cast N.pos
    have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
    have hc := hcurv ((N : ℝ) ^ (-ε) * gapVector X a)
      (mul_pos (Real.rpow_pos_of_pos hn0 _) (DefinitionSanity.gap_positive X a.val))
    rw [abs_of_nonneg (div_nonneg hc.1 (sq_nonneg _))]
    apply (div_le_iff₀ (by positivity : 0 < ((N : ℝ) ^ ε) ^ 2)).mpr
    exact hc.2.trans (le_mul_of_one_le_right (by linarith only [hCθ])
      (one_le_pow₀ (Real.one_le_rpow hn1 hε.le)))
  · simpa only [abs_zero] using (show 0 ≤ Cθ by linarith only [hCθ])

end Riesz2.PerturbationBounds

namespace Riesz2.PerturbationBounds

/-- See Lemma 5.8 of the paper, full-cycle alternative: both signed
freezing pairings on the intrinsic carrier, with compact-uniform constants.
The conditional and exterior terms are absent. -/
theorem full_freezing_bilinear (hRig : External.LongRangeRigidityLocallyUniform)
    (s : Riesz1.RieszExponent) (ε Cθ βlo βhi : ℝ)
    (hε : 0 < ε) (hCθ : 1 ≤ Cθ) (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n : ℕ+) (hn2 : 2 ≤ (n : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ K : ℕ,
      ∀ κ₀ : ℝ, 1 ≤ κ₀ →
      let ν := fullIntrinsicTiltedGapLaw (ofLong β s) n θ ε false
      let E := (fullIntrinsicGoodEvent s n ε κ₀)ᶜ
      let F := fun i j (z : gapTangentSpace n) =>
        PhysicalCore.forcingHessian n θ ε (WithLp.toLp 2 (fun a => 1 + z.val a)) i j +
        GoodBlocks.gapHessian s n i j (WithLp.toLp 2 (fun a => 1 + z.val a)) -
        2 * referenceIntervalMatrix s n hn2 K i j
      ∀ (φ η : gapTangentSpace n → ℝ) (Mφ Mη : ℝ),
        Measurable φ → Measurable η → 0 ≤ Mφ → 0 ≤ Mη →
        (∀ᵐ x ∂ν, |φ x| ≤ Mφ) → (∀ᵐ x ∂ν, |η x| ≤ Mη) →
      ∀ i j l : Fin (n : ℕ),
        IntegrableOn (fun x => φ x * η x * F i j x) E ν ∧
        |∫ x in E, φ x * η x * F i j x ∂ν| ≤
          C * Real.exp (-c * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη) ∧
        IntegrableOn (fun x => φ x * η x * (F i j x - F i l x)) E ν ∧
        |∫ x in E, φ x * η x * (F i j x - F i l x) ∂ν| ≤
          C * Real.exp (-c * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη) := by
  obtain ⟨R, hR, href⟩ := reference_freezing_bound s
  obtain ⟨H, hH, hhmom⟩ := full_intrinsic_hessian_moments s βlo βhi ε Cθ
    hlo hle hε hCθ
  obtain ⟨D, b, hD, hb, hgood⟩ := full_intrinsic_good_event hRig s hε hCθ βlo βhi hlo hle
  let B : ℝ := 2
  have hB : 0 ≤ B := by
    norm_num [B]
  have hδ := GoodBlocks.coefficientTailPower_pos s.property.1 s.property.2 hε
  obtain ⟨A, hA, habsorb⟩ := MomentEvent.exists_rpow_mul_exp_neg_le (a := B)
    (c := b / 4) (c' := b / 8) hδ (by linarith only [hb])
  let T := Cθ + H * (4 : ℝ) ^ ((s.val + 2) / s.val) + 18 * R
  have hT : 0 < T := by
    have hCθ0 : 0 < Cθ := by linarith only [hCθ]
    dsimp [T]
    positivity
  let Q := T * D ^ (1 / 4 : ℝ) * (A + 1)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  refine ⟨2 * Q, b / 8, by positivity, by positivity, ?_⟩
  intro β hβ n hn2 θ hcurv K κ₀ hκ₀ ν E F φ η Mφ Mη
    hφ hη hMφ hMη hφM hηM i j l
  have : IsProbabilityMeasure ν := DefinitionSanity.full_intrinsic_tilted_probability _ _ _ _ _
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hnp : 1 ≤ (n : ℝ) ^ B := Real.one_le_rpow hn1 hB
  have hY : Measurable (fun z : gapTangentSpace n => WithLp.toLp 2 (fun a => 1 + z.val a)) := by fun_prop
  have hFmeas (a b) : Measurable (F a b) :=
    (((PhysicalCore.measurable_forcingHessian n θ ε a b).comp hY).add
      ((GoodBlocks.measurable_gapHessian s n a b).comp hY)).sub measurable_const
  have hforcing (a b : Fin (n : ℕ)) := full_forcing_bound n θ hε hCθ hcurv (ofLong β s) a b
  have hnorm4 (a b : Fin (n : ℕ)) : eLpNorm (F a b) 4 ν ≤ ENNReal.ofReal (T * (n : ℝ) ^ B) := by
    have hf := eLpNorm_le_of_ae_bound (p := 4)
      (((PhysicalCore.measurable_forcingHessian n θ ε a b).comp
        hY).aestronglyMeasurable (μ := ν))
      (by simpa only [Real.norm_eq_abs, Function.comp_apply] using hforcing a b)
    simp only [measure_univ, ENNReal.one_rpow, one_mul] at hf
    have hh := hhmom β hβ n hn2 θ hcurv a b 4 (by norm_num)
    norm_num only [ENNReal.ofReal_ofNat] at hh
    have hh' : eLpNorm ((fun z : gapTangentSpace n => GoodBlocks.gapHessian s n a b (WithLp.toLp 2 (fun t => 1 + z.val t)))) 4 ν ≤
        ENNReal.ofReal (H * (4 : ℝ) ^ ((s.val + 2) / s.val)) := hh.trans
      (ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (by positivity)
        (Real.rpow_le_one_of_one_le_of_nonpos
          (le_add_of_nonneg_right (Nat.cast_nonneg _)) (by linarith [s.property.1]))))
    have hr := eLpNorm_le_of_ae_bound (p := 4) (μ := ν)
      (f := fun _ => 2 * referenceIntervalMatrix s n hn2 K a b)
      measurable_const.aestronglyMeasurable (ae_of_all ν fun _ => show
        ‖2 * referenceIntervalMatrix s n hn2 K a b‖ ≤
          2 * R * (n : ℝ) ^ 2 by
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
            exact (mul_le_mul_of_nonneg_left (href n hn2 K a b)
              (by norm_num)).trans_eq (by ring))
    simp only [measure_univ, ENNReal.one_rpow, one_mul] at hr
    apply ((eLpNorm_sub_le (by norm_num)).trans
      (add_le_add (eLpNorm_add_le (by norm_num)) le_rfl)).trans
    apply (add_le_add (add_le_add hf hh') hr).trans
    rw [← ENNReal.ofReal_add (by linarith only [hCθ]) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (Cθ + H * (4 : ℝ) ^ ((s.val + 2) / s.val)) * (n : ℝ) ^ B +
          2 * R * (n : ℝ) ^ B := by
        exact add_le_add (le_mul_of_one_le_right (by positivity) hnp)
          (by dsimp [B]; rw [Real.rpow_two])
      _ ≤ T * (n : ℝ) ^ B := by
        calc
          _ = (Cθ + H * (4 : ℝ) ^ ((s.val + 2) / s.val) + 2 * R) * (n : ℝ) ^ B := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp only [T]; linarith only [hR])
            (Real.rpow_nonneg hn0.le B)
  have hnorm (a z : Fin (n : ℕ)) : eLpNorm (F a z) 2 (ν.restrict E) ≤
      ENNReal.ofReal (Q * Real.exp (-(b / 8) * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε)) := by
    have hh := MomentEvent.restricted_two_norm_le (hFmeas a z) E
      (show 0 ≤ T * (n : ℝ) ^ B by positivity) hD.le (hnorm4 a z)
      (by simpa only [neg_mul] using hgood β hβ n hn2 θ hcurv κ₀ hκ₀)
    apply hh.trans
    apply ENNReal.ofReal_le_ofReal
    calc
      _ = T * D ^ (1 / 4 : ℝ) * ((n : ℝ) ^ B *
          Real.exp (-(b / 4) * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε)) := by
        rw [show -(b * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) / 4 =
          -(b / 4) * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε by ring]
        ring
      _ ≤ T * D ^ (1 / 4 : ℝ) * (A *
          Real.exp (-(b / 8) * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε)) :=
        mul_le_mul_of_nonneg_left (habsorb (n : ℝ) hn1) (by positivity)
      _ ≤ Q * Real.exp (-(b / 8) * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) := by
        dsimp [Q]
        have he := Real.exp_pos (-(b / 8) * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε)
        nlinarith only [mul_pos hT (Real.rpow_pos_of_pos hD (1 / 4 : ℝ)), he]
  have hdiffnorm : eLpNorm (fun x => F i j x - F i l x) 2 (ν.restrict E) ≤
      ENNReal.ofReal (2 * Q * Real.exp (-(b / 8) * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε)) := by
    apply (eLpNorm_sub_le (by norm_num)).trans
    apply (add_le_add (hnorm i j) (hnorm i l)).trans_eq
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  obtain ⟨hi, hbd⟩ := KernelCovarianceBounds.restricted_pair (hFmeas i j) hφ hη
    (by positivity) hMφ hMη hφM hηM (hnorm i j)
  obtain ⟨hi', hbd'⟩ := KernelCovarianceBounds.restricted_pair ((hFmeas i j).sub (hFmeas i l)) hφ hη
    (by positivity) hMφ hMη hφM hηM hdiffnorm
  refine ⟨hi, hbd.trans ?_, hi', hbd'⟩
  gcongr
  linarith only [hQ]

end Riesz2.PerturbationBounds

namespace Riesz2.PerturbationBounds

/-- See Subsection 5.1 of the paper: the prescribed proper-window period has exactly
the half-window and polynomial bounds used in the perturbation proof. -/
theorem reference_geometry (s : Riesz1.RieszExponent) (N n : ℕ+) (hper : 2 * (n : ℕ) ≤ (N : ℕ)) :
    let M := min (N : ℕ) (max (2 * (n : ℕ)) ⌈(n : ℝ) ^ (1 / 2 + 1 / s.val)⌉₊)
    2 ≤ M ∧ (n : ℕ) ≤ M ∧ 2 * (n : ℕ) ≤ M ∧
      (M : ℝ) ≤ 3 * (n : ℝ) ^ (1 / 2 + 1 / s.val) := by
  intro M
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hhalf : 2 * (n : ℕ) ≤ M := le_min hper (le_max_left _ _)
  have ha : (1 : ℝ) ≤ 1 / 2 + 1 / s.val := by
    have hs := s.property
    have hi : 1 ≤ 1 / s.val := (le_div_iff₀ hs.1).mpr (by linarith only [hs.2])
    linarith only [hi]
  have hpower : (n : ℝ) ≤ (n : ℝ) ^ (1 / 2 + 1 / s.val) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 ha
  refine ⟨by have := n.pos; omega, by omega, hhalf, ?_⟩
  have hceil := Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n)
    (1 / 2 + 1 / s.val))
  have hceil' : (⌈(n : ℝ) ^ (1 / 2 + 1 / s.val)⌉₊ : ℝ) ≤
      3 * (n : ℝ) ^ (1 / 2 + 1 / s.val) := by linarith only [hceil, hpower, hn1]
  have hmax : (max (2 * (n : ℕ)) ⌈(n : ℝ) ^ (1 / 2 + 1 / s.val)⌉₊ : ℕ) ≤
      3 * (n : ℝ) ^ (1 / 2 + 1 / s.val) := by
    rw [Nat.cast_max]
    apply max_le _ hceil'
    push_cast
    linarith only [hpower]
  exact (show (M : ℝ) ≤ (max (2 * (n : ℕ)) ⌈(n : ℝ) ^ (1 / 2 + 1 / s.val)⌉₊ : ℕ) by
    exact_mod_cast min_le_right (N : ℕ) _).trans hmax

end Riesz2.PerturbationBounds

namespace Riesz2.PerturbationBounds

/-- See Lemma 5.8 of the paper, complete proper-window form `T` of
Subsection 5.1. The inverse below solves βD+L, so its correction has factor β².
All bounded L² sources are allowed. On this probability law that is exactly
the essentially bounded source class. The scalar form may be any closed
Dirichlet form, in particular the intrinsic physical scalar form. -/
theorem proper_perturbation_bilinear (hRig : External.LongRangeRigidityLocallyUniform)
    (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (κ₀ : ℝ) (hκ₀ : 1 ≤ κ₀) (M₀ : ℕ) (hM₀ : 0 < M₀) :
    ∃ κ > 0, ∀ (ε Cθ βlo βhi : ℝ),
      0 < ε → 1 ≤ Cθ → 0 < βlo → βlo ≤ βhi →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n : ℕ+) (m : ℕ), 2 ≤ (n : ℕ) → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : (n : ℕ) ≤ (M : ℕ)),
      2 * (n : ℕ) ≤ (M : ℕ) → (M : ℝ) ≤ 3 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
      let K := ⌊(n : ℝ) ^ ε⌋₊ ^ M₀
      ∀ (hK : 1 ≤ K) (hKM : K ≤ (M : ℕ) / 4),
      let ν := (activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n hn θ ε false).comap
        ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
      let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
        β.val * ∑ i, θ.val ((n : ℝ) ^ (-ε) * x i) -
          Real.log (∫ z : EuclideanSpace ℝ (Fin m),
            (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (x,z)).toReal)
      let A := fun (i j : Fin (n : ℕ)) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) =>
        hessianMatrix V x.val i j - β.val * PhysicalCore.properActive β s n m M hM hnM K θ ε κ₀ x i j
      ∀ (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q),
      let E := Finset.univ.filter (fun a : Fin (M : ℕ) => (n : ℕ) ≤ a.val)
      let D : Matrix E E ℝ := ((2 : ℝ) • referenceIntervalMatrix s M hM K).submatrix
        (Subtype.val : E → Fin (M : ℕ)) Subtype.val
      let hD := (ExteriorForces.exteriorBlock_posDef s M hM hK hKM E).1
      let col := fun (i : Fin (n : ℕ)) (a : E) => 2 * referenceIntervalMatrix s M hM K (i.castLE hnM) a.val
      let F := BoundarySchurBounds.constantForm Q hQ (β.val • D) (hD.posSemidef.smul β.property.le)
      let J := OperatorSchur.vectorValues (ι := E) Q hQ
      ∃ R : PiLp 2 (fun _ : E => Lp ℝ 2 ν) →L[ℝ] MatrixEnergy.Vector (ι := E) Q hQ,
        (∀ f w, F (R f) w = inner ℝ f (J w)) ∧
        (∀ f u, (∀ w, F u w = inner ℝ f (J w)) → u = R f) ∧
        ∀ (φ η : Lp ℝ 2 ν) (Mφ Mη : ℝ), 0 ≤ Mφ → 0 ≤ Mη →
          (∀ᵐ x ∂ν, |φ x| ≤ Mφ) → (∀ᵐ x ∂ν, |η x| ≤ Mη) →
        ∀ i j l : Fin (n : ℕ),
          let d := fun a : Fin (n : ℕ) => ((min (a.val + 1) ((n : ℕ) - a.val) : ℕ) : ℝ)
          let T := fun a b => (∫ x, φ x * η x * A a b x ∂ν) + β.val ^ 2 *
            inner ℝ (BoundarySchurBounds.tensor (col b) η) (J (R (BoundarySchurBounds.tensor (col a) φ)))
          let Err := C * Real.exp (-c * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη)
          Integrable (fun x => φ x * η x * A i j x) ν ∧
          Integrable (fun x => φ x * η x * (A i j x - A i l x)) ν ∧
          |T i j| ≤ C * (n : ℝ) ^ (κ * ε) * (d i) ^ (-s.val / 2) * (d j) ^ (-s.val / 2) * (‖φ‖ * ‖η‖) + Err ∧
          |T i j - T i l| ≤ C * (n : ℝ) ^ (κ * ε) * (Nat.dist j.val l.val : ℝ) *
            (d i) ^ (-s.val / 2) * (min (d j) (d l)) ^ (-1 - s.val / 2) * (‖φ‖ * ‖η‖) + Err := by
  obtain ⟨km, hkm, hm⟩ := proper_multiplication_bilinear hRig s κ₀ hκ₀
  let κ := km + 2 * M₀
  have hκ : 0 < κ := by dsimp [κ]; positivity
  refine ⟨κ, hκ, fun ε Cθ βlo βhi hε hCθ hlo hle => ?_⟩
  obtain ⟨Cm, c, hCm, hc, hmult⟩ := hm ε Cθ βlo βhi hε hCθ hlo hle
  obtain ⟨Cs, hCs, hschur⟩ := BoundarySchurBounds.bilinear_schur_cutoff_uniform hz s βlo hlo
  let C := Cm + βhi ^ 2 * Cs
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, c, hC, hc, ?_⟩
  intro β hβ n m hn2 hper hn θ hcurv M hM hnM hhalf hscale K hK hKM ν V A Q hQ E D hD col F J
  obtain ⟨R, hR, huniq, hest⟩ := hschur β.val hβ.1 M hM K hK hKM n (by omega) ν Q hQ
  refine ⟨R, hR, huniq, ?_⟩
  intro φ η Mφ Mη hMφ hMη hφM hηM i j l d T Err
  have hφ := (Lp.stronglyMeasurable φ).measurable
  have hη := (Lp.stronglyMeasurable η).measurable
  obtain ⟨hi, hp, hi', hp'⟩ := hmult β hβ n m hn2 hper hn θ hcurv M hM hnM K hhalf hscale
    φ η Mφ Mη hφ hη hMφ hMη hφM hηM i j l
  change Integrable (fun x => φ x * η x * A i j x) ν at hi
  change Integrable (fun x => φ x * η x * (A i j x - A i l x)) ν at hi'
  have hnφ : Real.sqrt (∫ x, φ x ^ 2 ∂ν) = ‖φ‖ := by
    simpa only [Lp.toLp_coeFn] using (PerturbationPairingAssembly.toLp_norm (Lp.memLp φ)).symm
  have hnη : Real.sqrt (∫ x, η x ^ 2 ∂ν) = ‖η‖ := by
    simpa only [Lp.toLp_coeFn] using (PerturbationPairingAssembly.toLp_norm (Lp.memLp η)).symm
  dsimp only [ν] at hnφ hnη
  simp only [hnφ, hnη] at hp hp'
  obtain ⟨hr, hr'⟩ := hest η φ (i.castLE hnM) (j.castLE hnM) (l.castLE hnM) i.isLt j.isLt l.isLt
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hpow : (n : ℝ) ^ (km * ε) ≤ (n : ℝ) ^ (κ * ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [κ]; nlinarith only [hε, (Nat.cast_nonneg M₀ : (0 : ℝ) ≤ M₀)])
  have hcut : (K : ℝ) ^ 2 ≤ (n : ℝ) ^ (κ * ε) :=
    (BoundarySchurBounds.cutoff_sq_le n M₀ n.pos ε).trans
      (Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp [κ]; nlinarith only [hkm, hε]))
  have hβsq : β.val ^ 2 ≤ βhi ^ 2 := pow_le_pow_left₀ β.property.le hβ.2 2
  have hmain (w : ℝ) (hw : 0 ≤ w) (u v : ℝ)
      (hu : |u| ≤ Cm * (n : ℝ) ^ (km * ε) * w * (‖φ‖ * ‖η‖) +
        Cm * Real.exp (-c * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη))
      (hv : |v| ≤ Cs * (K : ℝ) ^ 2 * w * (‖φ‖ * ‖η‖)) :
      |u + β.val ^ 2 * v| ≤ C * (n : ℝ) ^ (κ * ε) * w * (‖φ‖ * ‖η‖) + Err := by
    have hE : Cm * Real.exp (-c * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη) ≤ Err := by
      dsimp only [Err]
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg hMφ hMη)
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact le_add_of_nonneg_right (by positivity)
    have hh := (abs_add_le u (β.val ^ 2 * v)).trans
      (add_le_add hu (by simpa only [abs_mul, abs_of_nonneg (sq_nonneg β.val)] using
        mul_le_mul_of_nonneg_left hv (sq_nonneg β.val)))
    apply hh.trans
    calc
      _ ≤ (Cm * (n : ℝ) ^ (κ * ε) * w * (‖φ‖ * ‖η‖) + Err) +
          βhi ^ 2 * (Cs * (n : ℝ) ^ (κ * ε) * w * (‖φ‖ * ‖η‖)) := by gcongr
      _ = _ := by dsimp [C]; ring
  have he : (∫ x, φ x * η x * A i j x ∂ν) - (∫ x, φ x * η x * A i l x ∂ν) =
      ∫ x, φ x * η x * (A i j x - A i l x) ∂ν := by
    rw [← integral_sub hi (hi.sub hi' |>.congr (ae_of_all ν fun x => by simp only [Pi.sub_apply]; ring))]
    apply integral_congr_ae
    exact ae_of_all ν fun x => by ring
  have hT : T i j - T i l = (∫ x, φ x * η x * (A i j x - A i l x) ∂ν) + β.val ^ 2 *
      inner ℝ (BoundarySchurBounds.tensor (col j - col l) η)
        (J (R (BoundarySchurBounds.tensor (col i) φ))) := by
    dsimp only [T]
    have ht : BoundarySchurBounds.tensor (col j - col l) η =
        BoundarySchurBounds.tensor (col j) η - BoundarySchurBounds.tensor (col l) η := by
      apply (WithLp.equiv 2 _).injective
      funext a
      change (col j a - col l a) • η = col j a • η - col l a • η
      exact sub_smul _ _ _
    rw [ht, inner_sub_left, ← he]
    ring
  refine ⟨hi, hi', ?_, ?_⟩
  · have hh := hmain ((d i) ^ (-s.val / 2) * (d j) ^ (-s.val / 2)) (by dsimp [d]; positivity)
      _ _ (by simpa only [mul_assoc] using hp)
      (by convert hr using 1; simp only [d, Fin.val_castLE]; ring)
    simpa only [T, mul_assoc] using hh
  · rw [hT]
    have hh := hmain ((Nat.dist j.val l.val : ℝ) * (d i) ^ (-s.val / 2) *
      (min (d j) (d l)) ^ (-1 - s.val / 2)) (by dsimp [d]; positivity)
      _ _ (by simpa only [mul_assoc] using hp')
      (by convert hr' using 1; simp only [d, Fin.val_castLE, Nat.cast_min]; ring)
    simpa only [mul_assoc] using hh

end Riesz2.PerturbationBounds

namespace Riesz2.PerturbationBounds

/-- See Lemma 5.8 of the paper, full-cycle `T`: its sole freezing term
with its actual β factor is exponentially small. Both pairings are absolutely
integrable. Constants precede all sizes and tests and are compact-uniform. -/
theorem full_perturbation_bilinear (hRig : External.LongRangeRigidityLocallyUniform)
    (s : Riesz1.RieszExponent) (ε Cθ βlo βhi : ℝ)
    (hε : 0 < ε) (hCθ : 1 ≤ Cθ) (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n : ℕ+) (hn2 : 2 ≤ (n : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ K : ℕ,
      ∀ κ₀ : ℝ, 1 ≤ κ₀ →
      let ν := fullIntrinsicTiltedGapLaw (ofLong β s) n θ ε false
      let E := (fullIntrinsicGoodEvent s n ε κ₀)ᶜ
      let F := fun i j (z : gapTangentSpace n) =>
        PhysicalCore.forcingHessian n θ ε (WithLp.toLp 2 (fun a => 1 + z.val a)) i j +
        GoodBlocks.gapHessian s n i j (WithLp.toLp 2 (fun a => 1 + z.val a)) -
        2 * referenceIntervalMatrix s n hn2 K i j
      ∀ (φ η : gapTangentSpace n → ℝ) (Mφ Mη : ℝ),
        Measurable φ → Measurable η → 0 ≤ Mφ → 0 ≤ Mη →
        (∀ᵐ x ∂ν, |φ x| ≤ Mφ) → (∀ᵐ x ∂ν, |η x| ≤ Mη) →
      ∀ i j l : Fin (n : ℕ),
        IntegrableOn (fun x => φ x * η x * (β.val * F i j x)) E ν ∧
        |∫ x in E, φ x * η x * (β.val * F i j x) ∂ν| ≤
          C * Real.exp (-c * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη) ∧
        IntegrableOn (fun x => φ x * η x * (β.val * (F i j x - F i l x))) E ν ∧
        |∫ x in E, φ x * η x * (β.val * (F i j x - F i l x)) ∂ν| ≤
          C * Real.exp (-c * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη) := by
  obtain ⟨C, c, hC, hc, hb⟩ := full_freezing_bilinear hRig s ε Cθ βlo βhi hε hCθ hlo hle
  have hhi : 0 < βhi := hlo.trans_le hle
  refine ⟨βhi * C, c, mul_pos hhi hC, hc, ?_⟩
  intro β hβ n hn2 θ hcurv K κ₀ hκ₀ ν E F φ η Mφ Mη hφ hη hMφ hMη hφM hηM i j l
  obtain ⟨hi, hp, hi', hp'⟩ := hb β hβ n hn2 θ hcurv K κ₀ hκ₀
    φ η Mφ Mη hφ hη hMφ hMη hφM hηM i j l
  have heq (Y : gapTangentSpace n → ℝ) :
      (fun x => φ x * η x * (β.val * Y x)) = fun x => β.val * (φ x * η x * Y x) := by
    funext x
    ring
  simp only [heq]
  refine ⟨hi.const_mul _, ?_, hi'.const_mul _, ?_⟩
  all_goals
    rw [integral_const_mul, abs_mul, abs_of_pos β.property]
    calc
      _ ≤ β.val * (C * Real.exp (-c * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη)) := by
        apply mul_le_mul_of_nonneg_left _ β.property.le
        first | exact hp | exact hp'
      _ ≤ _ := by
        have hnonneg : 0 ≤ C * Real.exp (-c * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη) := by positivity
        calc
          _ ≤ βhi * (C * Real.exp (-c * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη)) :=
            mul_le_mul_of_nonneg_right hβ.2 hnonneg
          _ = _ := by ring

end Riesz2.PerturbationBounds

namespace Riesz2.PerturbationBounds

/-- See Lemma 5.8 of the paper (both geometries). The full cycle has
only the exponentially small freezing term. The proper window has both
entry and column-difference estimates for the literal five-term form `T`,
using exactly the period and cutoff of Subsection 5.1. The same prefactor and
rate work in both cases. The exponent κ precedes ε and every temperature interval. -/
theorem cond_variance (hRig : External.LongRangeRigidityLocallyUniform)
    (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent)
    (κ₀ : ℝ) (hκ₀ : 1 ≤ κ₀) (M₀ : ℕ) (hM₀ : 0 < M₀) :
    ∃ κ > 0, ∀ (ε Cθ βlo βhi : ℝ),
      0 < ε → 1 ≤ Cθ → 0 < βlo → βlo ≤ βhi →
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      (∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n : ℕ+) (hn2 : 2 ≤ (n : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ K : ℕ,
      let ν := fullIntrinsicTiltedGapLaw (ofLong β s) n θ ε false
      let E := (fullIntrinsicGoodEvent s n ε κ₀)ᶜ
      let F := fun i j (z : gapTangentSpace n) =>
        PhysicalCore.forcingHessian n θ ε (WithLp.toLp 2 (fun a => 1 + z.val a)) i j +
        GoodBlocks.gapHessian s n i j (WithLp.toLp 2 (fun a => 1 + z.val a)) -
        2 * referenceIntervalMatrix s n hn2 K i j
      ∀ (φ η : gapTangentSpace n → ℝ) (Mφ Mη : ℝ),
        Measurable φ → Measurable η → 0 ≤ Mφ → 0 ≤ Mη →
        (∀ᵐ x ∂ν, |φ x| ≤ Mφ) → (∀ᵐ x ∂ν, |η x| ≤ Mη) →
      ∀ i j l : Fin (n : ℕ),
        IntegrableOn (fun x => φ x * η x * (β.val * F i j x)) E ν ∧
        |∫ x in E, φ x * η x * (β.val * F i j x) ∂ν| ≤
          C * Real.exp (-c * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη) ∧
        IntegrableOn (fun x => φ x * η x * (β.val * (F i j x - F i l x))) E ν ∧
        |∫ x in E, φ x * η x * (β.val * (F i j x - F i l x)) ∂ν| ≤
          C * Real.exp (-c * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη)) ∧
      ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
      ∀ (n : ℕ+) (m : ℕ), 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (θ : PhysicalCutoff),
      (∀ x : ℝ, 0 < x → 0 ≤ deriv (deriv θ.val) x ∧ deriv (deriv θ.val) x ≤ Cθ) →
      ∀ (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : (n : ℕ) ≤ (M : ℕ)),
      (M : ℕ) = min ((n : ℕ) + m + 1)
        (max (2 * (n : ℕ)) ⌈(n : ℝ) ^ (1 / 2 + 1 / s.val)⌉₊) →
      let K := ⌊(n : ℝ) ^ ε⌋₊ ^ M₀
      ∀ (hK : 1 ≤ K) (hKM : K ≤ (M : ℕ) / 4),
      let ν := (activeTiltedGapLaw (ofLong β s) ((n : ℕ) + m).succPNat n hn θ ε false).comap
        ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) → EuclideanSpace ℝ (Fin (n : ℕ)))
      let V := fun x : EuclideanSpace ℝ (Fin (n : ℕ)) =>
        β.val * ∑ i, θ.val ((n : ℝ) ^ (-ε) * x i) -
          Real.log (∫ z : EuclideanSpace ℝ (Fin m),
            (ProperMarginalChart.chartDensity (ofLong β s) n m (Equiv.refl _) (x,z)).toReal)
      let A := fun (i j : Fin (n : ℕ)) (x : AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) =>
        hessianMatrix V x.val i j - β.val * PhysicalCore.properActive β s n m M hM hnM K θ ε κ₀ x i j
      ∀ (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q),
      let E := Finset.univ.filter (fun a : Fin (M : ℕ) => (n : ℕ) ≤ a.val)
      let D : Matrix E E ℝ := ((2 : ℝ) • referenceIntervalMatrix s M hM K).submatrix
        (Subtype.val : E → Fin (M : ℕ)) Subtype.val
      let hD := (ExteriorForces.exteriorBlock_posDef s M hM hK hKM E).1
      let col := fun (i : Fin (n : ℕ)) (a : E) => 2 * referenceIntervalMatrix s M hM K (i.castLE hnM) a.val
      let F := BoundarySchurBounds.constantForm Q hQ (β.val • D) (hD.posSemidef.smul β.property.le)
      let J := OperatorSchur.vectorValues (ι := E) Q hQ
      ∃ R : PiLp 2 (fun _ : E => Lp ℝ 2 ν) →L[ℝ] MatrixEnergy.Vector (ι := E) Q hQ,
        (∀ f w, F (R f) w = inner ℝ f (J w)) ∧
        (∀ f u, (∀ w, F u w = inner ℝ f (J w)) → u = R f) ∧
        ∀ (φ η : Lp ℝ 2 ν) (Mφ Mη : ℝ), 0 ≤ Mφ → 0 ≤ Mη →
          (∀ᵐ x ∂ν, |φ x| ≤ Mφ) → (∀ᵐ x ∂ν, |η x| ≤ Mη) →
        ∀ i j l : Fin (n : ℕ),
          let d := fun a : Fin (n : ℕ) => ((min (a.val + 1) ((n : ℕ) - a.val) : ℕ) : ℝ)
          let T := fun a b => (∫ x, φ x * η x * A a b x ∂ν) + β.val ^ 2 *
            inner ℝ (BoundarySchurBounds.tensor (col b) η) (J (R (BoundarySchurBounds.tensor (col a) φ)))
          let Err := C * Real.exp (-c * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη)
          Integrable (fun x => φ x * η x * A i j x) ν ∧
          Integrable (fun x => φ x * η x * (A i j x - A i l x)) ν ∧
          |T i j| ≤ C * (n : ℝ) ^ (κ * ε) * (d i) ^ (-s.val / 2) * (d j) ^ (-s.val / 2) * (‖φ‖ * ‖η‖) + Err ∧
          |T i j - T i l| ≤ C * (n : ℝ) ^ (κ * ε) * (Nat.dist j.val l.val : ℝ) *
            (d i) ^ (-s.val / 2) * (min (d j) (d l)) ^ (-1 - s.val / 2) * (‖φ‖ * ‖η‖) + Err := by
  obtain ⟨κ, hκ, hp⟩ := proper_perturbation_bilinear hRig hz s κ₀ hκ₀ M₀ hM₀
  refine ⟨κ, hκ, fun ε Cθ βlo βhi hε hCθ hlo hle => ?_⟩
  obtain ⟨Cp, cp, hCp, hcp, hp⟩ := hp ε Cθ βlo βhi hε hCθ hlo hle
  obtain ⟨Cf, cf, hCf, hcf, hf⟩ := full_perturbation_bilinear hRig s ε Cθ βlo βhi hε hCθ hlo hle
  let C := Cp + Cf
  let c := min cp cf
  have hC : 0 < C := add_pos hCp hCf
  have hc : 0 < c := lt_min hcp hcf
  refine ⟨C, c, hC, hc, ?_, ?_⟩
  · intro β hβ n hn2 θ hcurv K ν E F φ η Mφ Mη hφ hη hMφ hMη hφM hηM i j l
    obtain ⟨hi, hb, hi', hb'⟩ := hf β hβ n hn2 θ hcurv K κ₀ hκ₀
      φ η Mφ Mη hφ hη hMφ hMη hφM hηM i j l
    have hbump (u : ℝ) (hu : |u| ≤ Cf * Real.exp (-cf * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη)) :
        |u| ≤ C * Real.exp (-c * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη) := by
      have hh := PerturbationPairingAssembly.enlarge_internal (P := 0) le_rfl
        (mul_nonneg hMφ hMη) hCf.le (show Cf ≤ C by dsimp only [C]; linarith only [hCp])
        (min_le_right cp cf) (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n) _)
        (by simpa only [mul_zero, zero_add] using hu)
      simpa only [mul_zero, zero_add] using hh
    exact ⟨hi, hbump _ hb, hi', hbump _ hb'⟩
  · intro β hβ n m hper hn θ hcurv M hM hnM hgeom K hK hKM ν V A Q hQ E D hD col F J
    have hgeo := reference_geometry s ((n : ℕ) + m).succPNat n (by simpa using hper)
    dsimp only [Nat.succPNat_coe] at hgeo
    rw [← hgeom] at hgeo
    have hn2 : 2 ≤ (n : ℕ) := by
      by_contra hh
      have hn1 : (n : ℕ) = 1 := by have := n.pos; omega
      have hN2 : 2 ≤ 1 + m + 1 := by omega
      have hM2 : (M : ℕ) = 2 := by
        simpa only [hn1, Nat.cast_one, Real.one_rpow, Nat.ceil_one,
          show max (2 * 1) 1 = (2 : ℕ) by norm_num, min_eq_right hN2] using hgeom
      omega
    obtain ⟨R, hR, hu, ht⟩ := hp β hβ n m hn2 hper hn θ hcurv M hM hnM hgeo.2.2.1 hgeo.2.2.2
      hK hKM Q hQ
    refine ⟨R, hR, hu, ?_⟩
    intro φ η Mφ Mη hMφ hMη hφM hηM i j l d T Err
    obtain ⟨hi, hi', hb, hb'⟩ := ht φ η Mφ Mη hMφ hMη hφM hηM i j l
    change |T i j| ≤ Cp * (n : ℝ) ^ (κ * ε) * (d i) ^ (-s.val / 2) *
      (d j) ^ (-s.val / 2) * (‖φ‖ * ‖η‖) +
      Cp * Real.exp (-cp * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη) at hb
    change |T i j - T i l| ≤ Cp * (n : ℝ) ^ (κ * ε) * (Nat.dist j.val l.val : ℝ) *
      (d i) ^ (-s.val / 2) * (min (d j) (d l)) ^ (-1 - s.val / 2) * (‖φ‖ * ‖η‖) +
      Cp * Real.exp (-cp * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη) at hb'
    have hbump (w u : ℝ) (hw : 0 ≤ w)
        (hu : |u| ≤ Cp * (n : ℝ) ^ (κ * ε) * w * (‖φ‖ * ‖η‖) +
          Cp * Real.exp (-cp * (n : ℝ) ^ GoodBlocks.coefficientTailPower s.val ε) * (Mφ * Mη)) :
        |u| ≤ C * (n : ℝ) ^ (κ * ε) * w * (‖φ‖ * ‖η‖) + Err := by
      have hh := PerturbationPairingAssembly.enlarge_internal
        (P := (n : ℝ) ^ (κ * ε) * w * (‖φ‖ * ‖η‖)) (by positivity)
        (mul_nonneg hMφ hMη) hCp.le (show Cp ≤ C by dsimp only [C]; linarith only [hCf])
        (min_le_left cp cf) (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ n) _)
        (by simpa only [mul_assoc] using hu)
      simpa only [mul_assoc, Err] using hh
    refine ⟨hi, hi', ?_, ?_⟩
    · have hh := hbump ((d i) ^ (-s.val / 2) * (d j) ^ (-s.val / 2)) (T i j)
        (by dsimp only [d]; positivity) (by simpa only [mul_assoc] using hb)
      simpa only [mul_assoc] using hh
    · have hh := hbump ((Nat.dist j.val l.val : ℝ) * (d i) ^ (-s.val / 2) *
        (min (d j) (d l)) ^ (-1 - s.val / 2)) (T i j - T i l)
        (by dsimp only [d]; positivity) (by simpa only [mul_assoc] using hb')
      simpa only [mul_assoc] using hh

end Riesz2.PerturbationBounds
