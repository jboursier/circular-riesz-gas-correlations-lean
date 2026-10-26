/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.External.LongRangeRigidityLocallyUniform
public import Riesz2.Bridges.GapRigidity
public import Riesz2.ToMathlib.External.RigidityUniformReduction
public import Riesz2.ToMathlib.External.RigidityUniformBlocks
public import Riesz1.Rigidity.RigidityGapsSplit

/-!
# Locally uniform long-range gap rigidity

The compact-temperature clause of the companion rigidity theorem.
The uniform reduction and block-difference estimates are combined using the
companion splitting identity. All constants are selected before the temperature.
Only the positive lower endpoint of the interval is used.
-/

public section

noncomputable section

open MeasureTheory

namespace Riesz2.ExternalRigidity

private theorem split_tail_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f g h H : Ω → ℝ)
    (hsplit : ∀ x, H x = f x - g x + h x) {a b d T : ℝ}
    (htotal : a + b + d ≤ T) :
    μ.real {x | T ≤ |H x|} ≤
      μ.real {x | a ≤ |f x|} + μ.real {x | b ≤ |g x|} +
        μ.real {x | d ≤ |h x|} := by
  have hinclusion : {x | T ≤ |H x|} ⊆
      ({x | a ≤ |f x|} ∪ {x | b ≤ |g x|}) ∪ {x | d ≤ |h x|} := by
    intro x hx
    by_contra hn
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hn
    have htriangle : |H x| ≤ |f x| + |g x| + |h x| := by
      rw [hsplit]
      exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    change T ≤ |H x| at hx
    linarith [hn.1.1, hn.1.2, hn.2]
  exact (measureReal_mono hinclusion (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans
      (add_le_add (measureReal_union_le _ _) le_rfl))

/-- The companion rigidity theorem, its compact-temperature clause,
with constants uniform over a compact interval of positive temperatures.
 -/
theorem longRangeRigidityLocallyUniform_result :
    Riesz2.External.LongRangeRigidityLocallyUniform := by
  intro s b hb _ βlo _ hβlo _
  obtain ⟨cR, CR, hcR, hCR, reduction⟩ := reduction_av_uniform s (half_pos hb) hβlo
  obtain ⟨cB, CB, hcB, hCB, blocks⟩ := rigidity_blocks_uniform s hb hβlo
  let c := min cR cB
  let C := 2 * CR + CB + Real.exp (3 * c)
  have hc : 0 < c := lt_min hcR hcB
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, c, hC, hc, ?_⟩
  intro β hβ N hN i k hk hkN
  let P : Riesz1.Parameters := ⟨(β.val, s.val), β.property, s.property⟩
  have hPs : Riesz1.parametersExponent P = s := Subtype.ext rfl
  have := Riesz1.isProbabilityMeasure_gibbsMeasure P N
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := lt_of_lt_of_le zero_lt_one hk1
  let T := (k : ℝ) ^ (s.val / 2 + b)
  let U := (k : ℝ) ^ (s.val / 2 + b / 2)
  let A := (k : ℝ) ^ (b / (4 * (s.val + 2)))
  let G := (k : ℝ) ^ (b / (2 * (s.val + 2)))
  have hAG : A ≤ G := Real.rpow_le_rpow_of_exponent_le hk1
    (div_le_div_of_nonneg_left hb.le (by linarith [s.property.1])
      (by linarith [s.property.1]))
  have hAhalf : A ≤ (k : ℝ) ^ (b / 2) :=
    Real.rpow_le_rpow_of_exponent_le hk1
      (div_le_div_of_nonneg_left hb.le two_pos (by linarith [s.property.1]))
  have hrates {r : ℝ} (hr : c ≤ r) :
      Real.exp (-r * G) ≤ Real.exp (-c * A) := by
    apply Real.exp_le_exp.mpr
    have hrate : c * A ≤ r * G :=
      (mul_le_mul_of_nonneg_left hAG hc.le).trans
        (mul_le_mul_of_nonneg_right hr (Real.rpow_nonneg hk0.le _))
    linarith
  rw [gibbsMeasure_ofLong]
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
    (mul_nonneg hC.le (Real.exp_pos _).le)).mpr
  change (Riesz1.gibbsMeasure P N).real
    {X | T ≤ |Riesz1.blockLength X i k - k|} ≤ C * Real.exp (-c * A)
  by_cases hlarge : 3 ≤ (k : ℝ) ^ (b / 2)
  · have hTU : 3 * U ≤ T := by
      have hfactor : T = U * (k : ℝ) ^ (b / 2) := by
        dsimp [T, U]
        rw [← Real.rpow_add hk0]
        congr 1
        ring
      rw [hfactor]
      nlinarith [mul_le_mul_of_nonneg_left hlarge (Real.rpow_nonneg hk0.le
        (s.val / 2 + b / 2))]
    have hsplit := split_tail_le (Riesz1.gibbsMeasure P N)
      (fun X => (N : ℝ) * (Riesz1.cyclicLift X (i + k) -
        Riesz1.blockAverage X (i + k) k))
      (fun X => (N : ℝ) * (Riesz1.cyclicLift X i - Riesz1.blockAverage X i k))
      (fun X => Riesz1.centeredBlockDiff X i k)
      (fun X => Riesz1.blockLength X i k - k)
      (fun X => Riesz1.blockLength_sub_eq_split X i k)
      (a := U) (b := U) (d := T / 3) (T := T) (by linarith)
    have hleft := reduction P rfl hβ.1 N hN (i + k) hk (by omega)
    have hright := reduction P rfl hβ.1 N hN i hk (by omega)
    have hblock := blocks P hPs hβ.1 N hN i k hk hkN
    have hpower : b / 2 / (s.val + 2) = b / (2 * (s.val + 2)) := div_div _ _ _
    rw [hpower] at hleft hright
    have hredRate := mul_le_mul_of_nonneg_left (hrates (min_le_left _ _)) hCR.le
    have hblockRate := mul_le_mul_of_nonneg_left (hrates (min_le_right _ _)) hCB.le
    have hpadding : 0 ≤ Real.exp (3 * c) * Real.exp (-c * A) := by positivity
    dsimp only [C]
    nlinarith [hsplit, hleft, hright, hblock, hredRate, hblockRate]
  · have hAsmall : A ≤ 3 := hAhalf.trans (le_of_lt (lt_of_not_ge hlarge))
    have hcover : 1 ≤ Real.exp (3 * c) * Real.exp (-c * A) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      nlinarith [mul_le_mul_of_nonneg_left hAsmall hc.le]
    exact measureReal_le_one.trans (hcover.trans
      (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (Real.exp_pos _).le))

end Riesz2.ExternalRigidity

end
