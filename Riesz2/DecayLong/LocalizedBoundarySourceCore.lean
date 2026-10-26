/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.LocalizedBoundaryPart2
public import Riesz2.DecayLong.LocalizedMatrixPart4
public import Riesz2.DecayLong.LocalizedMatrixPart5
public import Riesz2.ToMathlib.BoundedMatrixModes

/-!
# Boundary source infrastructure

See the proof of Proposition 5.15. All component
operations retain the original scalar form and its full domain.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter
open scoped BigOperators Classical Fin.NatCast

namespace Riesz2.LocalizedBoundary

open LocalizedMatrix IntervalBoundary

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {ν : Measure Ω}

/-- See Subsection 5.5 of the paper: a measurable finite row with a uniform Euclidean
bound acts on L² tuples with that same bound, without a cardinality loss. -/
theorem row_source_internal (r : ι → Ω → ℝ) (hr : ∀ i, Measurable (r i))
    (B : ℝ) (_hB : 0 ≤ B)
    (hb : ∀ᵐ x ∂ν, Real.sqrt (∑ i, r i x ^ 2) ≤ B)
    (v : ι → Lp ℝ 2 ν) :
    ∃ f : Lp ℝ 2 ν, (∀ᵐ x ∂ν, f x = ∑ i, r i x * v i x) ∧
      ‖f‖ ≤ B * Real.sqrt (∑ i, ‖v i‖ ^ 2) := by
  let V := fun x => Real.sqrt (∑ i, v i x ^ 2)
  have hV : MemLp V 2 ν := by
    simpa only [one_mul] using FiniteMixedL2.weighted_memLp (fun _ : ι => 1) v
  have hpt : ∀ᵐ x ∂ν, ‖∑ i, r i x * v i x‖ ≤ B * ‖V x‖ := by
    filter_upwards [hb] with x hx
    have hc := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => |r i x|)
      (fun i => |v i x|)
    simp only [sq_abs] at hc
    calc
      _ ≤ ∑ i, |r i x| * |v i x| := by
        simpa only [Real.norm_eq_abs, abs_mul] using Finset.abs_sum_le_sum_abs (fun i => r i x * v i x) Finset.univ
      _ ≤ _ := hc
      _ ≤ _ := by
        simpa only [V, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using
          mul_le_mul_of_nonneg_right hx (Real.sqrt_nonneg _)
  have hf : MemLp (fun x => ∑ i, r i x * v i x) 2 ν :=
    hV.of_le_mul (Finset.univ.aestronglyMeasurable_fun_sum (fun i _ => (hr i).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable (v i)))) hpt
  refine ⟨hf.toLp _, hf.coeFn_toLp, ?_⟩
  have hn : ‖hf.toLp _‖ ≤ B * ‖hV.toLp V‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hf.coeFn_toLp, hV.coeFn_toLp, hpt] with x hx hy hz
    simpa only [hx, hy] using hz
  have hnorm : ‖hV.toLp V‖ = Real.sqrt (∑ i, ‖v i‖ ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg (hV.toLp V)),
      ← CyclicFourierL2.integral_sq]
    rw [integral_congr_ae ((hV.coeFn_toLp).mono (fun x hx => congrArg (fun y : ℝ => y ^ 2) hx))]
    simpa only [V, one_mul] using congrArg Real.sqrt (FiniteMixedL2.weighted_sq_integral (fun _ : ι => 1) v)
  simpa only [hnorm] using hn

/-- See the proof of Proposition 5.15 in the paper: finite superposition of bounded
matrix weak equations on the entire unrestricted scalar form domain. -/
theorem weak_sum_internal {τ : Type*} [Fintype τ]
    (Q : ScalarFormData ν) (M : Ω → Matrix ι ι ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hMb : ∃ B : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ B)
    (f : τ → ι → Lp ℝ 2 ν) (u : τ → ι → Q.1)
    (hu : ∀ t, WeightedWeakSolution Q M ⊤ (f t) (u t)) :
    WeightedWeakSolution Q M ⊤ (fun i => ∑ t, f t i) (fun i => ∑ t, u t i) := by
  refine ⟨(BoundedMatrixForms.domain_iff Q M hMm hMb ⊤ _).mpr
    (Eventually.of_forall (fun _ => Submodule.mem_top)), ?_⟩
  intro z hz
  have hp : matrixFieldPair M (fun i => (∑ t, u t i).val) (fun i => (z i).val) =ᵐ[ν]
      fun x => ∑ t, matrixFieldPair M (fun i => (u t i).val) (fun i => (z i).val) x := by
    filter_upwards [ae_all_iff.mpr (fun i =>
      Lp.coeFn_fun_finsetSum Finset.univ (fun t => (u t i).val))] with x hx
    simp only [Submodule.coe_sum, hx, matrixFieldPair, Finset.sum_mul]
    calc
      _ = ∑ i, ∑ t, ∑ j, (u t i).val x * M x i j * (z j).val x := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := Finset.sum_comm
  refine ⟨BoundedMatrixForms.integrable_pair M hMm hMb _ _, ?_⟩
  rw [integral_congr_ae hp, integral_finsetSum _ (fun t _ => ((hu t).2 z hz).1)]
  simp only [map_sum, LinearMap.sum_apply, sum_inner]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  calc
    _ = ∑ t, ∑ i, inner ℝ (f t i) (z i).val :=
      Finset.sum_congr rfl (fun t _ => ((hu t).2 z hz).2)
    _ = _ := Finset.sum_comm

/-- See the proof of Proposition 5.15 in the paper: the square root of the scalar
energy is subadditive, including functions of zero energy. -/
theorem energy_sqrt_add_internal (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (u v : Q.1) :
    Real.sqrt (Q.2 (u + v) (u + v)) ≤ Real.sqrt (Q.2 u u) + Real.sqrt (Q.2 v v) := by
  have hu := hQ.2.2.1 u
  have hv := hQ.2.2.1 v
  have hcs : Q.2 u v ≤ Real.sqrt (Q.2 u u) * Real.sqrt (Q.2 v v) := by
    have hdisc : (Q.2 u v) ^ 2 ≤ Q.2 u u * Q.2 v v := by
      by_cases hz : Q.2 v v = 0
      · have hall (a : ℝ) := hQ.2.2.1 (u - a • v)
        have hzero : Q.2 u v = 0 := by
          by_contra hne
          have hh := hall ((Q.2 u u + 1) / (2 * Q.2 u v))
          simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
            smul_eq_mul, hQ.2.1 v u, hz, mul_zero, sub_zero] at hh
          field_simp at hh
          nlinarith [sq_pos_of_ne_zero hne]
        rw [hzero, hz]
        norm_num
      · have hh := hQ.2.2.1 (u - (Q.2 u v / Q.2 v v) • v)
        simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
          smul_eq_mul, hQ.2.1 v u] at hh
        have hvp : 0 < Q.2 v v := lt_of_le_of_ne hv (Ne.symm hz)
        have hh' := mul_nonneg hvp.le hh
        field_simp at hh'
        nlinarith
    nlinarith [Real.sq_sqrt hu, Real.sq_sqrt hv, Real.sqrt_nonneg (Q.2 u u),
      Real.sqrt_nonneg (Q.2 v v), mul_nonneg (Real.sqrt_nonneg (Q.2 u u))
        (Real.sqrt_nonneg (Q.2 v v))]
  have hsum := hQ.2.2.1 (u + v)
  have he : Q.2 (u + v) (u + v) = Q.2 u u + 2 * Q.2 u v + Q.2 v v := by
    simp only [map_add, LinearMap.add_apply, hQ.2.1 v u]
    ring
  nlinarith [Real.sq_sqrt hu, Real.sq_sqrt hv, Real.sq_sqrt hsum,
    Real.sqrt_nonneg (Q.2 u u), Real.sqrt_nonneg (Q.2 v v),
    Real.sqrt_nonneg (Q.2 (u + v) (u + v))]

/-- See the proof of Proposition 5.15 in the paper: the finite energy triangle inequality
needed for source-by-source superposition. -/
theorem energy_sqrt_sum_internal {τ : Type*} (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (T : Finset τ) (u : τ → Q.1) :
    Real.sqrt (Q.2 (∑ t ∈ T, u t) (∑ t ∈ T, u t)) ≤
      ∑ t ∈ T, Real.sqrt (Q.2 (u t) (u t)) := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert t T ht ih =>
    simp only [Finset.sum_insert ht]
    exact (energy_sqrt_add_internal Q hQ _ _).trans (add_le_add_right ih _)

/-- See the proof of Proposition 5.15 in the paper: summation of the two boundary
weights on an ordered interval, uniformly down to an interval of size one. -/
theorem boundary_weight_sum_internal (n : ℕ+) (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    (∑ i : Fin (n : ℕ),
      ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-t)) ≤
      2 / (1 - t) * (n : ℝ) ^ (1 - t) := by
  have hmin (i : Fin (n : ℕ)) :
      ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-t) ≤
        (1 + (i.val : ℝ)) ^ (-t) + (1 + (i.rev.val : ℝ)) ^ (-t) := by
    have hrev : (1 + (i.rev.val : ℝ)) = ((n : ℕ) - i.val : ℕ) := by
      have hi := i.isLt
      have he : 1 + i.rev.val = (n : ℕ) - i.val := by simp only [Fin.val_rev]; omega
      exact_mod_cast he
    rw [hrev]
    rcases le_total (i.val + 1) ((n : ℕ) - i.val) with h | h
    · rw [min_eq_left h]
      have he : ((i.val + 1 : ℕ) : ℝ) = 1 + (i.val : ℝ) := by push_cast; ring
      rw [he]
      exact le_add_of_nonneg_right (Real.rpow_nonneg (by positivity) _)
    · rw [min_eq_right h]
      exact le_add_of_nonneg_left (Real.rpow_nonneg (by positivity) _)
  have hr : (∑ i : Fin (n : ℕ), (1 + (i.rev.val : ℝ)) ^ (-t)) =
      ∑ i : Fin (n : ℕ), (1 + (i.val : ℝ)) ^ (-t) :=
    Equiv.sum_comp Fin.revPerm (fun i : Fin (n : ℕ) => (1 + (i.val : ℝ)) ^ (-t))
  have hb : (∑ i : Fin (n : ℕ), (1 + (i.val : ℝ)) ^ (-t)) ≤
      (n : ℝ) ^ (1 - t) / (1 - t) := by
    have hh := sum_range_one_add_rpow_le_of_lt_one ht ht1 n.pos
    simpa only [← Fin.sum_univ_eq_sum_range] using hh
  calc
    _ ≤ ∑ i : Fin (n : ℕ), ((1 + (i.val : ℝ)) ^ (-t) +
        (1 + (i.rev.val : ℝ)) ^ (-t)) := Finset.sum_le_sum (fun i _ => hmin i)
    _ = 2 * ∑ i : Fin (n : ℕ), (1 + (i.val : ℝ)) ^ (-t) := by
      rw [Finset.sum_add_distrib, hr]; ring
    _ ≤ 2 * ((n : ℝ) ^ (1 - t) / (1 - t)) := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by ring

/-- See the proof of Proposition 5.15 in the paper: the cyclic weight sum over an
embedded half-cycle interval has the usual subcritical bound. -/
theorem active_weight_sum_internal (n m : ℕ+) (hn : 2 * (n : ℕ) ≤ (m : ℕ))
    (j : Fin (n : ℕ)) (b : ℝ) (hb : 0 < b) (hb1 : b < 1) :
    (∑ i : Fin (n : ℕ),
      weightRadius m (j.castLE (by omega)) (i.castLE (by omega)) ^ (-b)) ≤
        2 / (1 - b) * (n : ℝ) ^ (1 - b) := by
  let e : Fin (n : ℕ) ↪ Fin (m : ℕ) := ⟨Fin.castLE (by omega), Fin.castLE_injective _⟩
  let c := j.castLE (by omega : (n : ℕ) ≤ (m : ℕ))
  have hs : Finset.univ.map e ⊆ Finset.univ.filter (fun i => weightRadius m i c ≤ (n : ℝ)) := by
    intro i hi
    obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    change 1 + (Riesz1.cyclicIndexDistance m (k.castLE (by omega)) (j.castLE (by omega)) : ℝ) ≤ _
    rw [LocalizedMatrix.active_distance m n hn]
    have hdist : 1 + Nat.dist k.val j.val ≤ (n : ℕ) := by
      have := k.isLt
      have := j.isLt
      unfold Nat.dist
      omega
    exact_mod_cast hdist
  have hh := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun i => weightRadius m i c ^ (-b)) hs
    (fun i _ _ => Real.rpow_nonneg (by linarith [one_le_weightRadius m i c]) (-b))
  have hbound := sum_weightRadius_le_of_lt_one m c hb hb1
    (show (1 : ℝ) ≤ n by exact_mod_cast n.pos)
  have he : (∑ i ∈ Finset.univ.map e, weightRadius m i c ^ (-b)) =
      ∑ i : Fin (n : ℕ), weightRadius m (j.castLE (by omega)) (i.castLE (by omega)) ^ (-b) := by
    simp only [Finset.sum_map, e, c, Function.Embedding.coeFn_mk, weightRadius,
      cyclicIndexDistance_comm']
  rw [he] at hh
  exact hh.trans hbound

/-- See the proof of Proposition 5.15 in the paper: the boundary convolution at the
middle of an odd interval. The two exponents are strictly below one, so
the bound has no logarithmic loss. -/
theorem boundary_convolution_internal (s : Riesz1.RieszExponent) (n m : ℕ+)
    (hn : 2 * (n : ℕ) ≤ (m : ℕ)) (q : ℕ) (hq : (n : ℕ) = 2 * q + 1)
    (j : Fin (n : ℕ)) (hj : j.val = q) :
    (∑ i : Fin (n : ℕ),
      weightRadius m (j.castLE (by omega)) (i.castLE (by omega)) ^ (-(1 - s.val / 2)) *
        ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ) ^ (-(1 + s.val) / 2)) ≤
      (4 ^ ((1 + s.val) / 2) * (2 / (s.val / 2)) +
        4 ^ (1 - s.val / 2) * (2 / ((1 - s.val) / 2))) * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  let b := 1 - s.val / 2
  let t := (1 + s.val) / 2
  have hb : 0 < b := by dsimp [b]; linarith [s.property.2]
  have hb1 : b < 1 := by dsimp [b]; linarith [s.property.1]
  have ht : 0 < t := by dsimp [t]; linarith [s.property.1]
  have ht1 : t < 1 := by dsimp [t]; linarith [s.property.2]
  let r := fun i : Fin (n : ℕ) => weightRadius m (j.castLE (by omega)) (i.castLE (by omega))
  let δ := fun i : Fin (n : ℕ) => ((min (i.val + 1) ((n : ℕ) - i.val) : ℕ) : ℝ)
  have hr (i) : 0 < r i := by dsimp [r]; linarith [one_le_weightRadius m (j.castLE (by omega)) (i.castLE (by omega))]
  have hd (i : Fin (n : ℕ)) : 0 < δ i := by
    dsimp [δ]
    exact_mod_cast (show 0 < min (i.val + 1) ((n : ℕ) - i.val) by have := i.isLt; omega)
  have hsep (i : Fin (n : ℕ)) : (n : ℝ) / 4 ≤ δ i ∨ (n : ℝ) / 4 ≤ r i := by
    have he : δ i + r i = (q : ℝ) + 2 := by
      dsimp [δ, r, weightRadius]
      rw [LocalizedMatrix.active_distance m n hn, hj]
      have he : min (i.val + 1) ((n : ℕ) - i.val) + Nat.dist q i.val = q + 1 := by
        have := i.isLt
        unfold Nat.dist
        omega
      exact_mod_cast (show min (i.val + 1) ((n : ℕ) - i.val) +
        (1 + Nat.dist q i.val) = q + 2 by omega)
    have hnq : (n : ℝ) = 2 * (q : ℝ) + 1 := by exact_mod_cast hq
    by_cases hh : (n : ℝ) / 4 ≤ δ i
    · exact Or.inl hh
    · exact Or.inr (by linarith)
  have hpt (i : Fin (n : ℕ)) : r i ^ (-b) * δ i ^ (-t) ≤
      ((n : ℝ) / 4) ^ (-t) * r i ^ (-b) + ((n : ℝ) / 4) ^ (-b) * δ i ^ (-t) := by
    rcases hsep i with h | h
    · have hh := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < (n : ℝ) / 4) h (neg_nonpos.mpr ht.le)
      nlinarith only [mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg (hr i).le (-b)),
        mul_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ (n : ℝ) / 4) (-b))
          (Real.rpow_nonneg (hd i).le (-t))]
    · have hh := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < (n : ℝ) / 4) h (neg_nonpos.mpr hb.le)
      nlinarith only [mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg (hd i).le (-t)),
        mul_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ (n : ℝ) / 4) (-t))
          (Real.rpow_nonneg (hr i).le (-b))]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpt i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  have hsr := active_weight_sum_internal n m hn j b hb hb1
  have hsd := boundary_weight_sum_internal n t ht ht1
  have hexp : 1 - b - t = -(1 / 2 : ℝ) := by dsimp [b, t]; ring
  have hp (a c : ℝ) : ((n : ℝ) / 4) ^ (-a) * (2 / (1 - c) * (n : ℝ) ^ (1 - c)) =
      (4 : ℝ) ^ a * (2 / (1 - c)) * (n : ℝ) ^ (1 - c - a) := by
    rw [Real.div_rpow (by positivity) (by norm_num), div_eq_mul_inv,
      ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), neg_neg]
    calc
      _ = 4 ^ a * (2 / (1 - c)) * ((n : ℝ) ^ (-a) * (n : ℝ) ^ (1 - c)) := by ring
      _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 2; ring
  simp only [show -(1 + s.val) / 2 = -((1 + s.val) / 2) by ring]
  change (∑ i, r i ^ (-b) * δ i ^ (-t)) ≤ _
  calc
    _ ≤ ((n : ℝ) / 4) ^ (-t) * (2 / (1 - b) * (n : ℝ) ^ (1 - b)) +
        ((n : ℝ) / 4) ^ (-b) * (2 / (1 - t) * (n : ℝ) ^ (1 - t)) :=
      hs.trans (add_le_add (mul_le_mul_of_nonneg_left hsr (by positivity))
        (mul_le_mul_of_nonneg_left hsd (by positivity)))
    _ = _ := by
      rw [hp t b, hp b t, hexp, show 1 - t - b = -(1 / 2 : ℝ) by linarith only [hexp]]
      dsimp [b, t]
      rw [show 1 - (1 - s.val / 2) = s.val / 2 by ring,
        show 1 - (1 + s.val) / 2 = (1 - s.val) / 2 by ring]
      ring

/-- See the proof of Proposition 5.15 in the paper: the local tuple norm is exactly
the norm of the original solution on the literal cyclic window. -/
theorem window_tuple_norm (m : ℕ+) (j i₀ : Fin (m : ℕ))
    (v : Fin (m : ℕ) → Lp ℝ 2 ν) :
    (∑ l : Fin (LocalizedMatrix.windowSize m j i₀ : ℕ),
      ‖v (LocalizedMatrix.windowEmbedding m j i₀ l)‖ ^ 2) =
        ∑ i ∈ LocalizedMatrix.window m j i₀, ‖v i‖ ^ 2 := by
  have he : Finset.univ.map (LocalizedMatrix.windowEmbedding m j i₀) =
      LocalizedMatrix.window m j i₀ := by
    ext i
    simp only [Finset.mem_map, Finset.mem_univ, true_and,
      LocalizedMatrix.mem_window_iff_exists_embedding]
  rw [← he, Finset.sum_map]

/-- See the proof of Proposition 5.15 in the paper: the remainder row bound
holds for every measurable representation of the same parent matrix. It
therefore applies to the witness chosen by the local structural theorem. -/
theorem window_row_for_representation_internal (s : Riesz1.RieszExponent) :
    ∃ Cp : ℝ, 0 < Cp ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω),
    ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ)) (K : ℕ) (C κ γ ε : ℝ), 1 ≤ C →
    ∀ M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ,
    PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M →
    ∀ A : Fin (m : ℕ) × Fin ((m : ℕ) / 2) → Ω → ℝ,
    (∀ᵐ x ∂ν, IntervalBoundary.intervalMatrix m m le_rfl (fun t => A t x) = M x) →
    ∀ (j i₀ : Fin (m : ℕ)) (hR : 16 ≤ Riesz1.cyclicIndexDistance m j i₀),
    let n₀ := LocalizedMatrix.windowSize m j i₀
    let m₀ := LocalizedMatrix.windowPeriod s m j i₀
    let hn : (n₀ : ℕ) ≤ (m : ℕ) := by
      dsimp only [n₀]
      have := (LocalizedMatrix.window_size_bounds m j i₀ hR).2.2.2; omega
    let hn₀ : (n₀ : ℕ) ≤ (m₀ : ℕ) := by
      dsimp only [n₀, m₀]
      have := LocalizedMatrix.two_windowSize_lt_period s m j i₀ hR; omega
    let hm₀ : 2 ≤ (m₀ : ℕ) := by
      dsimp only [m₀]
      have := LocalizedMatrix.two_windowSize_lt_period s m j i₀ hR
      have := (LocalizedMatrix.windowSize m j i₀).pos; omega
    let b := j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ))
    let P := fun x (l i : Fin (n₀ : ℕ)) => M x (l.castLE hn + b) (i.castLE hn + b)
    ∀ᵐ x ∂ν, ∀ l : Fin (n₀ : ℕ),
      Real.sqrt (∑ i, (LocalizedMatrix.remainder s m m₀ n₀ hm₀ hn hn₀ K
        (fun t => A (t.1 + b, t.2)) P x l i) ^ 2) ≤
      (4 * Real.sqrt (2 + 1 / (1 + s.val)) * (C * (n : ℝ) ^ (κ * ε)) + Cp) *
        ((min (l.val + 1) ((n₀ : ℕ) - l.val) : ℕ) : ℝ) ^ (-(1 + s.val) / 2) := by
  obtain ⟨Cp, hCp, hb⟩ := LocalizedMatrix.remainder_row_bound_internal s
  refine ⟨Cp, hCp, ?_⟩
  intro Ω inst ν n m hm K C κ γ ε hC M hM A hA j i₀ hR
  dsimp only
  filter_upwards [hA, periodizedMatrixBounds_truncated_error s n m hm K C κ γ ε
    (by linarith : 0 ≤ C) M hM] with x hx he
  intro l
  let Ar := fun t : Fin (m : ℕ) × Fin ((m : ℕ) / 2) => A t x
  have hmatrix : intervalMatrix m m le_rfl Ar = M x := hx
  let n₀ := windowSize m j i₀
  let m₀ := windowPeriod s m j i₀
  let b : Fin (m : ℕ) := j - ((Riesz1.cyclicIndexDistance m j i₀ / 8 : ℕ) : Fin (m : ℕ))
  have hn : 4 * (n₀ : ℕ) ≤ (m : ℕ) := (window_size_bounds m j i₀ hR).2.2.2
  have hn₀ : 2 * (n₀ : ℕ) < (m₀ : ℕ) := two_windowSize_lt_period s m j i₀ hR
  have hfive : 5 ≤ (n₀ : ℕ) := (window_size_bounds m j i₀ hR).1
  have hm₀ : 4 ≤ (m₀ : ℕ) := by omega
  have hle : (m₀ : ℕ) ≤ (m : ℕ) := windowPeriod_le_parent s m j i₀
  have hscale : m₀ = m ∨ (n₀ : ℝ) ^ (1 / 2 + 1 / s.val) ≤ (m₀ : ℝ) := by
    by_cases h : m₀ = m
    · exact Or.inl h
    · right
      have hlt : (m₀ : ℕ) < (m : ℕ) := by
        have hh : (m₀ : ℕ) ≠ (m : ℕ) := fun hh => h (Subtype.ext hh)
        omega
      exact power_le_windowPeriod_of_lt s m j i₀ hlt
  have henv (p w : Fin (m : ℕ)) :
      |intervalMatrix m m le_rfl
        ((fun t => Ar (t.1 + b, t.2)) - BoundaryEntries.referenceWeight s m hm K) p w| ≤
        (C * (n : ℝ) ^ (κ * ε)) *
          (1 + (Riesz1.cyclicIndexDistance m p w : ℝ)) ^ (-1 - s.val / 2) := by
    have hcoef : ((fun t => Ar (t.1 + b, t.2)) - BoundaryEntries.referenceWeight s m hm K) =
        (fun t => (Ar - BoundaryEntries.referenceWeight s m hm K) (t.1 + b, t.2)) := rfl
    rw [hcoef, intervalMatrix_translate, intervalMatrix_sub, hmatrix,
      intervalMatrix_referenceWeight, Matrix.sub_apply]
    simpa only [distance_add, show -(1 + s.val / 2) = -1 - s.val / 2 by ring] using he (p + b) (w + b)
  have hh := hb m m₀ n₀ hm hm₀ hle hn hn₀ hscale K (fun t => Ar (t.1 + b, t.2))
    (C * (n : ℝ) ^ (κ * ε)) (mul_nonneg (by linarith) (by positivity)) henv l
  have hprincipal (i k : Fin (n₀ : ℕ)) :
      M x (i.castLE (by omega : (n₀ : ℕ) ≤ (m : ℕ)) + b)
        (k.castLE (by omega : (n₀ : ℕ) ≤ (m : ℕ)) + b) =
        intervalMatrix m n₀ (by omega) (fun t => Ar (t.1 + b, t.2)) i k := by
    rw [intervalMatrix_restrict, intervalMatrix_translate, hmatrix]
  simp only [remainder, Matrix.sub_apply]
  convert hh using 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change (M x (l.castLE (by omega : (n₀ : ℕ) ≤ (m : ℕ)) + b)
      (i.castLE (by omega : (n₀ : ℕ) ≤ (m : ℕ)) + b) -
      internalMatrix m n₀ (by omega) (fun t => Ar (t.1 + b, t.2)) l i -
      BoundaryEntries.referenceCrossing s m₀ (by omega) K n₀ (by omega) l i) ^ 2 = _
  rw [hprincipal l i,
    intervalMatrix_symm m n₀ (by omega) (fun t => Ar (t.1 + b, t.2)) l i,
    internalMatrix_symm m n₀ (by omega) (fun t => Ar (t.1 + b, t.2)) l i,
    BoundaryEntries.referenceCrossing_eq_boundaryMatrix,
    boundaryMatrix_symm m₀ n₀ (by omega) (BoundaryEntries.referenceWeight s m₀ (by omega) K) l i]


/-- See Subsection 5.5 of the paper: finite bounded matrix multiplication defines an
L² source and represents its pairing on the entire scalar domain. -/
theorem matrix_source_pair_internal (M : Ω → Matrix ι ι ℝ)
    (hMm : ∀ i j, Measurable (fun x => M x i j))
    (hMb : ∃ B : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ B)
    (u : ι → Lp ℝ 2 ν) :
    ∃ f : ι → Lp ℝ 2 ν,
      (∀ j, ∀ᵐ x ∂ν, f j x = ∑ i, u i x * M x i j) ∧
      ∀ v : ι → Lp ℝ 2 ν,
        (∫ x, matrixFieldPair M u v x ∂ν) = ∑ j, inner ℝ (f j) (v j) := by
  obtain ⟨B, hB⟩ := hMb
  have hp : ∀ i j, ∃ g : Lp ℝ 2 ν,
      (∀ᵐ x ∂ν, g x = M x i j * u i x) := by
    intro i j
    obtain ⟨g, hg, _⟩ := BoundedMatrixModes.exists_multiplier (fun x => M x i j) (hMm i j)
      (max B 0) (le_max_right _ _) (hB.mono (fun _ hx => (hx i j).trans (le_max_left _ _))) (u i)
    exact ⟨g, hg⟩
  choose g hg using hp
  let f := fun j => ∑ i, g i j
  have hf (j) : ∀ᵐ x ∂ν, f j x = ∑ i, u i x * M x i j := by
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => g i j),
      ae_all_iff.mpr (fun i => hg i j)] with x hx hy
    change (∑ i, g i j) x = _
    rw [hx]
    exact Finset.sum_congr rfl (fun i _ => (hy i).trans (mul_comm _ _))
  refine ⟨f, hf, fun v => ?_⟩
  have he : matrixFieldPair M u v =ᵐ[ν] fun x => ∑ j, f j x * v j x := by
    filter_upwards [ae_all_iff.mpr hf] with x hx
    simp only [matrixFieldPair, hx, Finset.sum_mul]
    exact Finset.sum_comm
  rw [integral_congr_ae he, integral_finsetSum]
  swap
  · intro j _
    exact (Lp.memLp (f j)).integrable_mul (Lp.memLp (v j))
  apply Finset.sum_congr rfl
  intro j _
  rw [L2.inner_def]
  simp only [Real.inner_apply]

/-- See Subsection 5.5 of the paper: evaluation of the actual reassembled exterior
field in its exterior coordinates. -/
theorem assemble_right_apply_internal (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
    (u : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ)
    (w : MatrixEnergy.Vector (ι := Fin ((m : ℕ) - (n : ℕ))) Q hQ)
    (i : Fin ((m : ℕ) - (n : ℕ))) :
    SchurRestriction.assemble Q hQ n m hnm (u, w)
      (Fin.cast (Nat.add_sub_of_le hnm) (Fin.natAdd (n : ℕ) i)) = w i := by
  change SchurRestriction.join Q hQ n ((m : ℕ) - (n : ℕ)) (u, w)
    (Fin.cast (Nat.add_sub_of_le hnm).symm
      (Fin.cast (Nat.add_sub_of_le hnm) (Fin.natAdd (n : ℕ) i))) = w i
  have he : Fin.cast (Nat.add_sub_of_le hnm).symm
      (Fin.cast (Nat.add_sub_of_le hnm) (Fin.natAdd (n : ℕ) i)) = Fin.natAdd (n : ℕ) i := Fin.ext rfl
  rw [he]
  exact SchurRestriction.join_right_apply Q hQ n ((m : ℕ) - (n : ℕ)) u w i

/-- See Subsection 5.5 of the paper: an ambient source paired with a zero-extended
active test restricts to the original active L² pairing. -/
theorem assembled_active_pair_internal (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
    (f : Fin (m : ℕ) → Lp ℝ 2 ν)
    (v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ) :
    (∑ i, inner ℝ (f i) (MatrixEnergy.vectorEquiv Q hQ
      (SchurRestriction.assemble Q hQ n m hnm (v, 0)) i).val) =
        ∑ i : Fin (n : ℕ), inner ℝ (f (i.castLE hnm))
          (MatrixEnergy.vectorEquiv Q hQ v i).val := by
  let F := fun i : Fin (m : ℕ) => inner ℝ (f i) (MatrixEnergy.vectorEquiv Q hQ
    (SchurRestriction.assemble Q hQ n m hnm (v, 0)) i).val
  have he := (finCongr (Nat.add_sub_of_le hnm)).sum_comp F
  rw [Fin.sum_univ_add] at he
  rw [← he]
  have hleft (i : Fin (n : ℕ)) : (finCongr (Nat.add_sub_of_le hnm))
      (Fin.castAdd ((m : ℕ) - (n : ℕ)) i) = i.castLE hnm := Fin.ext rfl
  have hright (i : Fin ((m : ℕ) - (n : ℕ))) :
      F ((finCongr (Nat.add_sub_of_le hnm)) (Fin.natAdd (n : ℕ) i)) = 0 := by
    change inner ℝ _ (ScalarFormHilbert.equiv Q hQ
      (SchurRestriction.assemble Q hQ n m hnm (v, 0)
        (Fin.cast (Nat.add_sub_of_le hnm) (Fin.natAdd (n : ℕ) i)))).val = 0
    rw [assemble_right_apply_internal]
    simp only [PiLp.zero_apply, map_zero, Submodule.coe_zero, inner_zero_right]
  simp only [hright, Finset.sum_const_zero, add_zero, hleft]
  apply Finset.sum_congr rfl
  intro i _
  change inner ℝ (f (i.castLE hnm)) (ScalarFormHilbert.equiv Q hQ
    (SchurRestriction.assemble Q hQ n m hnm (v, 0) (i.castLE hnm))).val = _
  rw [SchurRestriction.assemble_left_apply]
  rfl

/-- See the proof of Proposition 5.15: concrete harmonic
embedding on the scalar form domain. The Schur correction is an L²
matrix source, and the resulting unique weak solution has precisely the
prescribed active coordinates. The active equation is an internal input. -/
theorem harmonic_embedding_internal
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (s : Riesz1.RieszExponent) (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
    (hm : 2 ≤ (m : ℕ)) (K : ℕ) (C κ γ ε β : ℝ) (hC : 1 ≤ C) (hβ : 0 < β)
    (M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M)
    (p : Fin (n : ℕ) → Q.1) (f : Fin (n : ℕ) → Lp ℝ 2 ν)
    (hactive : ∀ v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ,
      SchurRestriction.active Q hQ n ((m : ℕ) - (n : ℕ))
        (SchurRestriction.splitForm Q hQ n m hnm s hm K C κ γ ε β hC hβ M hM)
        ((MatrixEnergy.vectorEquiv Q hQ).symm p) v =
          ∑ i, inner ℝ (f i) (MatrixEnergy.vectorEquiv Q hQ v i).val) :
    let pv := (MatrixEnergy.vectorEquiv Q hQ).symm p
    let e := SchurRestriction.exteriorResponse Q hQ n m hnm s hm K C κ γ ε β hC hβ M hM pv
    let W := SchurRestriction.assemble Q hQ n m hnm (0, e)
    ∃ c : Fin (n : ℕ) → Lp ℝ 2 ν,
      (∀ l, ∀ᵐ x ∂ν, c l x = ∑ i,
        (MatrixEnergy.vectorEquiv Q hQ W i).val x * (β * M x i (l.castLE hnm))) ∧
      ∃! ψ : Fin (m : ℕ) → Q.1,
        WeightedWeakSolution Q (fun x => β • M x) ⊤
          (SchurRestriction.extendSource n m hnm
            (WithLp.toLp 2 (fun i => f i - c i))).ofLp ψ ∧
        ∀ i : Fin (n : ℕ), ψ (i.castLE hnm) = p i := by
  dsimp only
  let pv := (MatrixEnergy.vectorEquiv Q hQ).symm p
  let F := SchurRestriction.periodizedForm Q hQ n m s hm K C κ γ ε β hC hβ M hM
  let G := SchurRestriction.splitForm Q hQ n m hnm s hm K C κ γ ε β hC hβ M hM
  let J := SchurRestriction.assemble Q hQ n m hnm
  let e := SchurRestriction.exteriorResponse Q hQ n m hnm s hm K C κ γ ε β hC hβ M hM pv
  have hFs (a b : MatrixEnergy.Vector (ι := Fin (m : ℕ)) Q hQ) : F a b = F b a :=
    BoundedMatrixForms.form_symmetric Q hQ (fun x => β • M x)
      (SchurRestriction.periodized_scaled_measurable β hM)
      (SchurRestriction.periodized_scaled_bounded β hM)
      (SchurRestriction.periodized_scaled_psd β hβ hC hM) a b
  have hGs (a b : MatrixEnergy.Vector (ι := Fin ((n : ℕ) + ((m : ℕ) - (n : ℕ)))) Q hQ) :
      G a b = G b a := hFs _ _
  obtain ⟨c, hc, hcpair⟩ := matrix_source_pair_internal (fun x => β • M x)
    (SchurRestriction.periodized_scaled_measurable β hM)
    (SchurRestriction.periodized_scaled_bounded β hM)
    (fun i => (MatrixEnergy.vectorEquiv Q hQ (J (0, e)) i).val)
  let ca := fun i : Fin (n : ℕ) => c (i.castLE hnm)
  have hcross (v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ) :
      SchurRestriction.cross Q hQ n ((m : ℕ) - (n : ℕ)) G v e =
        ∑ i, inner ℝ (ca i) (MatrixEnergy.vectorEquiv Q hQ v i).val := by
    change F (J (v, 0)) (J (0, e)) = _
    rw [hFs]
    dsimp only [F, SchurRestriction.periodizedForm, J]
    rw [BoundedMatrixForms.form_apply, SchurRestriction.assemble_energy]
    simp only [map_zero, Pi.zero_apply, LinearMap.zero_apply, Finset.sum_const_zero, zero_add,
      add_zero]
    rw [hcpair]
    exact assembled_active_pair_internal Q hQ n m hnm c v
  let ψv := J (pv, -e)
  have hF : ∀ w, F ψv w = inner ℝ (WithLp.toLp 2 (fun i => f i - ca i))
      (OperatorSchur.vectorValues Q hQ (J.symm w).1) := by
    intro w
    let v := (J.symm w).1
    let z := (J.symm w).2
    have hw : J (v, z) = w := J.apply_symm_apply w
    rw [← hw]
    change G (SchurRestriction.join Q hQ n ((m : ℕ) - (n : ℕ)) (pv, -e))
      (SchurRestriction.join Q hQ n ((m : ℕ) - (n : ℕ)) (v, z)) = _
    rw [← SchurRestriction.blockForm_eq Q hQ n ((m : ℕ) - (n : ℕ)) G hGs pv v (-e) z]
    simp only [OperatorSchur.blockForm_apply, map_neg, neg_apply]
    have he : SchurRestriction.exteriorForm Q hQ n ((m : ℕ) - (n : ℕ)) G e z =
        SchurRestriction.cross Q hQ n ((m : ℕ) - (n : ℕ)) G pv z :=
      OperatorSchur.exterior_solves _ _
        (min 1 (β * (C⁻¹ * (n : ℝ) ^ (-κ * ε))))
        (SchurRestriction.coercivity_pos n C κ ε β hC hβ)
        (SchurRestriction.exterior_coercive Q hQ n ((m : ℕ) - (n : ℕ)) G _
          (SchurRestriction.splitForm_coercive Q hQ n m hnm s hm K C κ γ ε β hC hβ M hM)) pv z
    rw [hactive, hcross, he]
    simp only [ContinuousLinearEquiv.symm_apply_apply, PiLp.inner_apply,
      OperatorSchur.vectorValues_apply, inner_sub_left,
      Finset.sum_sub_distrib]
    ring
  have hψ := (SchurRestriction.periodizedForm_equation_iff Q hQ n m hnm s hm K
    C κ γ ε β hC hβ M hM ψv (WithLp.toLp 2 (fun i => f i - ca i))).mp hF
  refine ⟨ca, fun l => ?_, MatrixEnergy.vectorEquiv Q hQ ψv, ⟨hψ, ?_⟩, ?_⟩
  · simpa only [Matrix.smul_apply, smul_eq_mul] using hc (l.castLE hnm)
  · intro i
    change ScalarFormHilbert.equiv Q hQ (J (pv, -e) (i.castLE hnm)) = p i
    rw [SchurRestriction.assemble_left_apply]
    exact congrFun ((MatrixEnergy.vectorEquiv Q hQ).apply_symm_apply p) i
  · intro ψ hψ'
    exact (SchurRestriction.schur_restriction_weak Q hQ n m hnm s hm K C κ γ ε
      β hC hβ M hM (WithLp.toLp 2 (fun i => f i - ca i))).1.unique hψ'.1 hψ

/-- See the proof of Proposition 5.15 in the paper: summation of a full-cycle function
supported on the retained initial block, with no size factor. -/
theorem sum_active_internal (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
    (f : Fin (m : ℕ) → ℝ) (hf : ∀ i, (n : ℕ) ≤ i.val → f i = 0) :
    (∑ i, f i) = ∑ i : Fin (n : ℕ), f (i.castLE hnm) := by
  have he := (finCongr (Nat.add_sub_of_le hnm)).sum_comp f
  rw [Fin.sum_univ_add] at he
  rw [← he]
  have hl (i : Fin (n : ℕ)) : (finCongr (Nat.add_sub_of_le hnm))
      (Fin.castAdd ((m : ℕ) - (n : ℕ)) i) = i.castLE hnm := Fin.ext rfl
  have hr (i : Fin ((m : ℕ) - (n : ℕ))) :
      f ((finCongr (Nat.add_sub_of_le hnm)) (Fin.natAdd (n : ℕ) i)) = 0 :=
    hf _ (by change (n : ℕ) ≤ (n : ℕ) + i.val; omega)
  simp only [hl, hr, Finset.sum_const_zero, add_zero]

/-- See Subsection 5.5 of the paper: an active field extended by zero has exactly
zero exterior L² coordinates. -/
theorem active_extension_zero_internal (Q : ScalarFormData ν)
    (hQ : IsClosedScalarDirichletForm Q) (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
    (p : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ)
    (i : Fin (m : ℕ)) (hi : (n : ℕ) ≤ i.val) :
    (MatrixEnergy.vectorEquiv Q hQ (SchurRestriction.assemble Q hQ n m hnm (p, 0)) i).val = 0 := by
  let k : Fin ((m : ℕ) - (n : ℕ)) := ⟨i.val - (n : ℕ), by have := i.isLt; omega⟩
  have he : Fin.cast (Nat.add_sub_of_le hnm) (Fin.natAdd (n : ℕ) k) = i := by
    apply Fin.ext
    change (n : ℕ) + (i.val - (n : ℕ)) = i.val
    omega
  change (ScalarFormHilbert.equiv Q hQ
    (SchurRestriction.assemble Q hQ n m hnm (p, 0) i)).val = 0
  rw [← he, assemble_right_apply_internal]
  simp only [PiLp.zero_apply, map_zero, Submodule.coe_zero]

/-- See the proof of Proposition 5.15 in the paper: componentwise principal equations
imply the actual active block form equation used by harmonic embedding.
Every matrix integral is proved integrable from the structural data. -/
theorem active_form_from_rows_internal
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (s : Riesz1.RieszExponent) (n m : ℕ+) (hnm : (n : ℕ) ≤ (m : ℕ))
    (hm : 2 ≤ (m : ℕ)) (K : ℕ) (C κ γ ε β : ℝ) (hC : 1 ≤ C) (hβ : 0 < β)
    (M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M)
    (p : Fin (n : ℕ) → Q.1) (f : Fin (n : ℕ) → Lp ℝ 2 ν)
    (hrows : ∀ (l : Fin (n : ℕ)) (v : Q.1),
      Q.2 (p l) v + (∫ x, ∑ i : Fin (n : ℕ),
        β * M x (l.castLE hnm) (i.castLE hnm) * (p i).val x * v.val x ∂ν) =
          inner ℝ (f l) v.val)
    (v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ) :
    SchurRestriction.active Q hQ n ((m : ℕ) - (n : ℕ))
      (SchurRestriction.splitForm Q hQ n m hnm s hm K C κ γ ε β hC hβ M hM)
      ((MatrixEnergy.vectorEquiv Q hQ).symm p) v =
        ∑ i, inner ℝ (f i) (MatrixEnergy.vectorEquiv Q hQ v i).val := by
  let pv := (MatrixEnergy.vectorEquiv Q hQ).symm p
  let J := SchurRestriction.assemble Q hQ n m hnm
  let U := fun i => (MatrixEnergy.vectorEquiv Q hQ (J (pv, 0)) i).val
  let V := fun i => (MatrixEnergy.vectorEquiv Q hQ (J (v, 0)) i).val
  let vt := MatrixEnergy.vectorEquiv Q hQ v
  have hU (i : Fin (n : ℕ)) : U (i.castLE hnm) = (p i).val := by
    change (ScalarFormHilbert.equiv Q hQ (J (pv, 0) (i.castLE hnm))).val = _
    rw [SchurRestriction.assemble_left_apply]
    exact congrArg Subtype.val (congrFun ((MatrixEnergy.vectorEquiv Q hQ).apply_symm_apply p) i)
  have hV (i : Fin (n : ℕ)) : V (i.castLE hnm) = (vt i).val := by
    change (ScalarFormHilbert.equiv Q hQ (J (v, 0) (i.castLE hnm))).val = _
    rw [SchurRestriction.assemble_left_apply]
    rfl
  have hpair : matrixFieldPair (fun x => β • M x) U V =ᵐ[ν]
      fun x => ∑ l : Fin (n : ℕ), ∑ i : Fin (n : ℕ),
        β * M x (l.castLE hnm) (i.castLE hnm) * (p i).val x * (vt l).val x := by
    filter_upwards [hM.2.1, Lp.coeFn_zero ℝ 2 ν] with x hx hz
    have hu0 (i : Fin (m : ℕ)) (hi : (n : ℕ) ≤ i.val) : U i x = 0 := by
      rw [show U i = 0 from active_extension_zero_internal Q hQ n m hnm pv i hi]
      exact hz
    have hv0 (i : Fin (m : ℕ)) (hi : (n : ℕ) ≤ i.val) : V i x = 0 := by
      rw [show V i = 0 from active_extension_zero_internal Q hQ n m hnm v i hi]
      exact hz
    unfold matrixFieldPair
    rw [Finset.sum_comm, sum_active_internal n m hnm _ (fun l hl => by
      simp only [hv0 l hl, mul_zero, Finset.sum_const_zero])]
    apply Finset.sum_congr rfl
    intro l _
    rw [sum_active_internal n m hnm _ (fun i hi => by simp only [hu0 i hi, zero_mul])]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hU, hV, Matrix.smul_apply, smul_eq_mul, hx.1 (i.castLE hnm) (l.castLE hnm)]
    ring
  have hrowI (l : Fin (n : ℕ)) : Integrable (fun x => ∑ i : Fin (n : ℕ),
      β * M x (l.castLE hnm) (i.castLE hnm) * (p i).val x * (vt l).val x) ν := by
    obtain ⟨B, hb⟩ := SchurRestriction.periodized_scaled_bounded β hM
    exact row_integrable_internal (fun x (l i : Fin (n : ℕ)) =>
      (β • M x) (l.castLE hnm) (i.castLE hnm))
      (fun l i => SchurRestriction.periodized_scaled_measurable β hM _ _)
      ⟨B, hb.mono (fun _ hx l i => hx _ _)⟩ (fun i => (p i).val) (vt l).val l Finset.univ
  change SchurRestriction.periodizedForm Q hQ n m s hm K C κ γ ε β hC hβ M hM
    (J (pv, 0)) (J (v, 0)) = _
  dsimp only [SchurRestriction.periodizedForm]
  rw [BoundedMatrixForms.form_apply, SchurRestriction.assemble_energy]
  simp only [map_zero, Pi.zero_apply, Finset.sum_const_zero, add_zero]
  change (∑ i, Q.2 (MatrixEnergy.vectorEquiv Q hQ pv i) (vt i)) +
    (∫ x, matrixFieldPair (fun x => β • M x) U V x ∂ν) = _
  rw [show MatrixEnergy.vectorEquiv Q hQ pv = p from (MatrixEnergy.vectorEquiv Q hQ).apply_symm_apply p,
    integral_congr_ae hpair, integral_finsetSum _ (fun l _ => hrowI l), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun l _ => hrows l (vt l))

/-- The projected equation in the proof of Proposition 5.15 gives the local
principal row equations, with the original multiplier and exterior L²
source. The negative remainder source restores the parent principal block.
This implication assumes the exact block identity for the matrix inputs. -/
theorem projected_rows_internal
    (Q : ScalarFormData ν) (s : Riesz1.RieszExponent) (n m : ℕ+)
    (hm : 2 ≤ (m : ℕ)) (K : ℕ) (C κ γ ε β : ℝ)
    (M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm K C κ γ ε M)
    (χ : Lp ℝ 2 ν) (i₀ j : Fin (m : ℕ))
    (u : Fin (m : ℕ) → Q.1)
    (hu : WeightedWeakSolution Q (fun x => β • M x) (zeroSumComponents _)
      (fun i => if i = i₀ then χ else 0) u)
    (hR : 0 < Riesz1.cyclicIndexDistance m j i₀)
    (m₀ : ℕ+) (hn₀ : (windowSize m j i₀ : ℕ) ≤ (m₀ : ℕ))
    (Ml : Ω → Matrix (Fin (m₀ : ℕ)) (Fin (m₀ : ℕ)) ℝ)
    (hMlm : ∀ i l, Measurable (fun x => Ml x i l))
    (hMlb : ∃ B : ℝ, ∀ᵐ x ∂ν, ∀ i l, |Ml x i l| ≤ B)
    (Rem : Ω → Matrix (Fin (windowSize m j i₀ : ℕ)) (Fin (windowSize m j i₀ : ℕ)) ℝ)
    (hblock : ∀ x l i, Ml x (l.castLE hn₀) (i.castLE hn₀) + Rem x l i =
      M x (windowEmbedding m j i₀ l) (windowEmbedding m j i₀ i))
    (g : Fin (windowSize m j i₀ : ℕ) → Lp ℝ 2 ν)
    (hg : ∀ l, ∀ᵐ x ∂ν, g l x = -β * ∑ i, Rem x l i *
      (u (windowEmbedding m j i₀ i)).val x) :
    ∃ lam : Lp ℝ 2 ν,
      (∀ᵐ x ∂ν, lam x = gapMultiplierField m Q (fun x => β • M x)
        (fun i => if i = i₀ then χ else 0) u x) ∧
      ∃ q : Fin (windowSize m j i₀ : ℕ) → Lp ℝ 2 ν,
        (∀ l, ∀ᵐ x ∂ν, q l x = -β *
          (∑ i ∈ (window m j i₀)ᶜ, M x (windowEmbedding m j i₀ l) i * (u i).val x) + lam x) ∧
        ∀ (l : Fin (windowSize m j i₀ : ℕ)) (v : Q.1),
          Q.2 (u (windowEmbedding m j i₀ l)) v +
            (∫ x, ∑ i : Fin (windowSize m j i₀ : ℕ),
              β * Ml x (l.castLE hn₀) (i.castLE hn₀) *
                (u (windowEmbedding m j i₀ i)).val x * v.val x ∂ν) =
                  inner ℝ (q l + g l) v.val := by
  obtain ⟨lam, hlam, hproj⟩ := projected_equation s n m hm K C κ γ ε Q M hM β χ i₀ u hu
  let J := window m j i₀
  let e := windowEmbedding m j i₀
  let vo := fun i : Fin (m : ℕ) => if i ∈ J then (0 : Lp ℝ 2 ν) else (u i).val
  obtain ⟨co, hco, _⟩ := matrix_source_pair_internal (fun x => β • M x)
    (SchurRestriction.periodized_scaled_measurable β hM)
    (SchurRestriction.periodized_scaled_bounded β hM) vo
  have hco' (l : Fin (windowSize m j i₀ : ℕ)) : ∀ᵐ x ∂ν,
      co (e l) x = β * ∑ i ∈ Jᶜ, M x (e l) i * (u i).val x := by
    filter_upwards [hco (e l), hM.2.1, Lp.coeFn_zero ℝ 2 ν] with x hx hs hz
    have hv (i : Fin (m : ℕ)) : vo i x = if i ∈ J then 0 else (u i).val x := by
      by_cases hi : i ∈ J
      · simpa only [vo, hi, ite_true, Pi.zero_apply] using hz
      · simp only [vo, hi, ite_false]
    rw [hx]
    simp only [hv, Matrix.smul_apply, smul_eq_mul, ite_mul, zero_mul, Finset.mul_sum]
    have heq : Jᶜ = Finset.univ.filter (fun i => i ∉ J) := by ext i; simp
    rw [heq, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ J
    · simp only [hi, ite_true, not_true_eq_false, ite_false]
    · simp only [hi, ite_false, not_false_eq_true, ite_true, hs.1 i (e l)]
      ring
  let q := fun l => lam - co (e l)
  refine ⟨lam, hlam, q, fun l => ?_, fun l v => ?_⟩
  · filter_upwards [Lp.coeFn_sub lam (co (e l)), hco' l] with x hx hy
    change (lam - co (e l)) x = _
    rw [hx, Pi.sub_apply, hy]
    ring
  · have hl : e l ∈ J := (mem_window_iff_exists_embedding m j i₀ (e l)).mpr ⟨l, rfl⟩
    obtain ⟨hI, hO, hp⟩ := hproj J (source_not_mem_window m j i₀ hR) (e l) hl v
    have houter : (∫ x, ∑ i ∈ Jᶜ, β * M x (e l) i * (u i).val x * v.val x ∂ν) =
        inner ℝ (co (e l)) v.val := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hco' l] with x hx
      simp only [Real.inner_apply, hx, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [houter] at hp
    have hJ : Finset.univ.map e = J := by
      ext i
      simp only [Finset.mem_map, Finset.mem_univ, true_and,
        mem_window_iff_exists_embedding, J, e]
    have hretained : (fun x => ∑ i ∈ J, β * M x (e l) i * (u i).val x * v.val x) =ᵐ[ν]
        fun x => (∑ i : Fin (windowSize m j i₀ : ℕ),
          β * Ml x (l.castLE hn₀) (i.castLE hn₀) * (u (e i)).val x * v.val x) -
            g l x * v.val x := by
      filter_upwards [hg l] with x hx
      rw [← hJ, Finset.sum_map, hx]
      simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← hblock x l i]
      ring
    have hlocalI : Integrable (fun x => ∑ i : Fin (windowSize m j i₀ : ℕ),
        β * Ml x (l.castLE hn₀) (i.castLE hn₀) * (u (e i)).val x * v.val x) ν := by
      obtain ⟨B, hB⟩ := hMlb
      exact row_integrable_internal (fun x (l i : Fin (windowSize m j i₀ : ℕ)) =>
        β * Ml x (l.castLE hn₀) (i.castLE hn₀))
        (fun l i => measurable_const.mul (hMlm _ _))
        ⟨|β| * B, hB.mono (fun x hx l i => by
          simpa only [abs_mul] using mul_le_mul_of_nonneg_left (hx _ _) (abs_nonneg β))⟩
        (fun i => (u (e i)).val) v.val l Finset.univ
    have hgI : Integrable (fun x => g l x * v.val x) ν :=
      (Lp.memLp (g l)).integrable_mul (Lp.memLp v.val)
    have heI : (∫ x, (∑ i : Fin (windowSize m j i₀ : ℕ),
        β * Ml x (l.castLE hn₀) (i.castLE hn₀) * (u (e i)).val x * v.val x) -
          g l x * v.val x ∂ν) =
        (∫ x, ∑ i : Fin (windowSize m j i₀ : ℕ),
          β * Ml x (l.castLE hn₀) (i.castLE hn₀) * (u (e i)).val x * v.val x ∂ν) -
            ∫ x, g l x * v.val x ∂ν := integral_sub hlocalI hgI
    rw [integral_congr_ae hretained, heI] at hp
    have hginner : (∫ x, g l x * v.val x ∂ν) = inner ℝ (g l) v.val := by
      rw [L2.inner_def]; simp only [Real.inner_apply]
    rw [hginner] at hp
    simp only [q, inner_add_left, inner_sub_left]
    linarith only [hp]

end Riesz2.LocalizedBoundary
