/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.IntervalCoefficientsPart4
public import Riesz2.ToMathlib.MomentEventBounds
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Exceptional coefficient events for the short-range physical law

The coefficient estimates of Subsections 4.4 and 4.5.
Optimizing the polynomial moment bounds for the physical coefficients
and exterior energy gives one simultaneous stretched-exponential estimate
under the active tilted marginal, including the one-gap block and both penalties.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators ContDiff

namespace Riesz2.DecayShort.ExceptionalEvent

/-- An auxiliary coefficient event for Subsection 4.4, on the full physical
retained carrier. The truncation level `D` is `A n^(κh)`. Prefix and suffix
cuts use zero-based labels: cut `k` has prefix length `k+1` and suffix
length `n-(k+1)`. -/
def coefficientEvent (p : Parameters) (n : ℕ+) (m : ℕ)
    (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)) (D : ℝ) :
    Set (AffineSimplex.chartDomain n ((n + m : ℕ) + 1)) :=
  let N := ((n : ℕ) + m).succPNat
  let A := fun x => conditionalIntervalWeight p n m n.pos (Equiv.refl _) x
  let H := fun x => IntervalBoundary.intervalMatrix N ((n : ℕ) + m + 1) le_rfl (A x)
  let S := Finset.univ.filter (fun a : Fin ((n : ℕ) + m + 1) => (n : ℕ) ≤ a.val)
  {x | (∀ i j : Fin (n : ℕ), IntervalBoundary.intervalMatrix N n hn (A x) i j ≤
      D * (1 + (Riesz1.cyclicIndexDistance N (Fin.castLE hn i) (Fin.castLE hn j) : ℝ)) ^ (-p.val.2)) ∧
    (∀ k : Fin ((n : ℕ) - 1),
      IntervalBoundary.prefixCoefficient N n hn (A x) (k.val + 1) ≤
        D * (k.val + 1 : ℕ) ^ (-p.val.2 - 1)) ∧
    (∀ k : Fin ((n : ℕ) - 1),
      IntervalBoundary.suffixCoefficient N n hn (A x) (k.val + 1) ≤
        D * ((n : ℕ) - (k.val + 1) : ℕ) ^ (-p.val.2 - 1)) ∧
    IntervalBoundary.fullCoefficient N n hn (A x) ≤ D * (n : ℝ) ^ (-p.val.2) ∧
    (∀ i : Fin (n : ℕ), (m + 1 : ℝ)⁻¹ * ∑ a ∈ S, H x (Fin.castLE hn i) a +
      (m + 1 : ℝ)⁻¹ ^ 2 * ∑ a ∈ S, ∑ b ∈ S, H x a b ≤ D / (N : ℝ)) ∧
    (∀ i : Fin (n : ℕ), (PhysicalFibres.exteriorGradientEnergy p n m n.pos x i).toReal ≤
      D * (min (i.val + 1) ((n : ℕ) - i.val) : ℕ) ^ (1 - 2 * p.val.2))}

/-- Every ordinary nontrivial cut occurs exactly at its positive prefix
length. There is no condition at a zero or full prefix. -/
theorem cuts_iff {n : ℕ+} {P : ℕ → Prop} :
    (∀ k : Fin ((n : ℕ) - 1), P (k.val + 1)) ↔
      ∀ k : ℕ, 1 ≤ k → k < (n : ℕ) → P k := by
  constructor
  · intro h k hk hkn
    have hsub : k - 1 + 1 = k := by omega
    simpa only [hsub] using h ⟨k - 1, by omega⟩
  · intro h k
    exact h _ (by omega) (by have := k.isLt; omega)

/-- Internal Markov step in Subsection 4.5, keeping the complete
coefficient profile. The real moment exponent `n^h` avoids a floor and
also applies at `n=1`. -/
theorem internal_profile_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    {n D h C A w : ℝ} (hn : 1 ≤ n) (_hD : 0 < D) (hh : 0 < h)
    (hC : 0 < C) (hA : Real.exp 1 * C ≤ A) (hw : 0 < w)
    (hm : ∀ q : ℝ, 1 ≤ q → eLpNorm f (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal (C * q ^ D * w)) :
    μ.real {x | A * n ^ (D * h) * w < f x} ≤ Real.exp (-(n ^ h)) := by
  let q := n ^ h
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hq : 1 ≤ q := Real.one_le_rpow hn hh.le
  have hqD : q ^ D = n ^ (D * h) := by
    dsimp only [q]
    rw [← Real.rpow_mul hn0.le, mul_comm h D]
  have hA0 : 0 < A := lt_of_lt_of_le (mul_pos (Real.exp_pos _) hC) hA
  have hCA : C ≤ Real.exp (-1) * A := by
    have hb := mul_le_mul_of_nonneg_left hA (Real.exp_pos (-1)).le
    have he : Real.exp (-1) * (Real.exp 1 * C) = C := by
      rw [← mul_assoc, ← Real.exp_add]
      norm_num
    rwa [he] at hb
  have hscale : 0 < n ^ (D * h) * w := mul_pos (Real.rpow_pos_of_pos hn0 _) hw
  have ht : 0 < A * n ^ (D * h) * w := by positivity
  have hb : C * q ^ D * w ≤ Real.exp (-1) * (A * n ^ (D * h) * w) := by
    rw [hqD]
    nlinarith [mul_le_mul_of_nonneg_right hCA hscale.le]
  have htail := MomentEvent.measureReal_abs_ge_le_exp_neg_of_eLpNorm_le hf
    (lt_of_lt_of_le zero_lt_one hq) (by positivity) ht (hm q hq) hb
  apply (measureReal_mono (show {x | A * n ^ (D * h) * w < f x} ⊆
    {x | A * n ^ (D * h) * w ≤ |f x|} from fun x hx =>
      (show A * n ^ (D * h) * w < f x from hx).le.trans (le_abs_self _))).trans
  exact htail

/-- Probability bound for the auxiliary coefficient event in Subsection 4.5.
The exponent `κ` depends only on `s`. The stretched-exponential power
is `h`, independently of temperature. All six families in
`coefficientEvent` are included. -/
theorem coefficient_exception_probability (s : ℝ) (hs : 1 < s) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (θ : PhysicalCutoff) (βlo βhi h : ℝ),
      0 < βlo → βlo ≤ βhi → 0 < h →
      ∃ A C c : ℝ, 1 ≤ A ∧ 0 < C ∧ 0 < c ∧
      ∀ p : Parameters, p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ (n : ℕ+) (m : ℕ) (hn : (n : ℕ) ≤ (((n : ℕ) + m).succPNat : ℕ)),
        2 * (n : ℕ) ≤ (n : ℕ) + m + 1 → ∀ ι : Bool,
        let μ := (activeTiltedGapLaw p ((n : ℕ) + m).succPNat n hn θ h ι).comap
          ((↑) : AffineSimplex.chartDomain n ((n + m : ℕ) + 1) →
            EuclideanSpace ℝ (Fin (n : ℕ)))
        μ (coefficientEvent p n m hn (A * (n : ℝ) ^ (κ * h)))ᶜ ≤
          ENNReal.ofReal (C * Real.exp (-c * (n : ℝ) ^ h)) := by
  classical
  obtain ⟨D, hD, hm⟩ := interval_counting_coefficient_moments s hs
  refine ⟨D, hD, ?_⟩
  intro θ βlo βhi h hlo hle hh
  obtain ⟨C₀, hC₀, hcoeff⟩ := hm θ βlo βhi h hlo hle hh
  obtain ⟨Cθ, hCθ, hcurv, _⟩ := θ.property.2.2.2.2
  obtain ⟨_, _, hVmeas⟩ := activeTilt_conditional_exterior_energy_moments s βlo βhi h Cθ
    hs hlo hle hh hCθ
  obtain ⟨K, hK, hpoly⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := 2) (c := 1) (c' := 1 / 2) hh (by norm_num)
  let A := max 1 (Real.exp 1 * C₀)
  refine ⟨A, 6 * (K + 1), 1 / 2, le_max_left _ _, by positivity, by norm_num, ?_⟩
  intro p hp hpl hph n m hn hhalf ι μ
  have hμ : IsProbabilityMeasure μ := activeTilt_proper_probability p n m hn θ h ι
  let N := ((n : ℕ) + m).succPNat
  let B := AffineSimplex.chartDomain n ((n + m : ℕ) + 1)
  let a := fun x => conditionalIntervalWeight p n m n.pos (Equiv.refl _) x
  let H := fun x => IntervalBoundary.intervalMatrix N ((n : ℕ) + m + 1) le_rfl (a x)
  let S := Finset.univ.filter (fun a : Fin ((n : ℕ) + m + 1) => (n : ℕ) ≤ a.val)
  let b := fun i x => (m + 1 : ℝ)⁻¹ * ∑ a ∈ S, H x (Fin.castLE hn i) a
  let c := fun x => (m + 1 : ℝ)⁻¹ ^ 2 * ∑ a ∈ S, ∑ b ∈ S, H x a b
  let V := fun i x => (PhysicalFibres.exteriorGradientEnergy p n m n.pos x i).toReal
  let J := (Fin (n : ℕ) × Fin (n : ℕ)) ⊕
    (Fin ((n : ℕ) - 1) ⊕ (Fin ((n : ℕ) - 1) ⊕ (Unit ⊕ (Fin (n : ℕ) ⊕ Fin (n : ℕ)))))
  let f : J → B → ℝ := Sum.elim
    (fun ij x => IntervalBoundary.intervalMatrix N n hn (a x) ij.1 ij.2)
    (Sum.elim (fun k x => IntervalBoundary.prefixCoefficient N n hn (a x) (k.val + 1))
      (Sum.elim (fun k x => IntervalBoundary.suffixCoefficient N n hn (a x) (k.val + 1))
        (Sum.elim (fun _ x => IntervalBoundary.fullCoefficient N n hn (a x))
          (Sum.elim (fun i x => b i x + c x) V))))
  let w : J → ℝ := Sum.elim
    (fun ij => (1 + (Riesz1.cyclicIndexDistance N (Fin.castLE hn ij.1)
      (Fin.castLE hn ij.2) : ℝ)) ^ (-s))
    (Sum.elim (fun k => (k.val + 1 : ℕ) ^ (-s - 1))
      (Sum.elim (fun k => ((n : ℕ) - (k.val + 1) : ℕ) ^ (-s - 1))
        (Sum.elim (fun _ => (n : ℝ) ^ (-s))
          (Sum.elim (fun _ => (N : ℝ)⁻¹)
            (fun i => (min (i.val + 1) ((n : ℕ) - i.val) : ℕ) ^ (1 - 2 * s))))))
  have hw (j : J) : 0 < w j := by
    rcases j with ij | (k | (k | (_ | (i | i))))
    · dsimp only [w, Sum.elim_inl]; positivity
    · dsimp only [w, Sum.elim_inr, Sum.elim_inl]; positivity
    · dsimp only [w, Sum.elim_inr, Sum.elim_inl]
      apply Real.rpow_pos_of_pos
      exact_mod_cast (show 0 < (n : ℕ) - (k.val + 1) by have := k.isLt; omega)
    · dsimp only [w, Sum.elim_inr, Sum.elim_inl]; positivity
    · dsimp only [w, Sum.elim_inr, Sum.elim_inl]; positivity
    · dsimp only [w, Sum.elim_inr]
      apply Real.rpow_pos_of_pos
      exact_mod_cast (show 0 < min (i.val + 1) ((n : ℕ) - i.val) by have := i.isLt; omega)
  have hH (i j) : Measurable (fun x : B => H x i j) :=
    measurable_conditional_intervalMatrix p n m n.pos _ le_rfl i j
  have hb (i) : Measurable (b i) := by
    exact (Finset.measurable_sum _ fun a _ => hH _ a).const_mul _
  have hc : Measurable c := by
    exact (Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => hH a b).const_mul _
  have hf (j : J) : Measurable (f j) := by
    rcases j with ij | (k | (k | (_ | (i | i))))
    · exact measurable_conditional_intervalMatrix p n m n.pos _ hn ij.1 ij.2
    · exact (measurable_physical_boundary_coefficients p n m n.pos hn).1 _
    · exact (measurable_physical_boundary_coefficients p n m n.pos hn).2.1 _
    · exact (measurable_physical_boundary_coefficients p n m n.pos hn).2.2
    · exact (hb i).add hc
    · exact (hVmeas p hp hpl hph n m hn θ hcurv ι i 1 le_rfl).1
  have hmom (j : J) (q : ℝ) (hq : 1 ≤ q) :
      eLpNorm (f j) (ENNReal.ofReal q) μ ≤ ENNReal.ofReal (C₀ * q ^ D * w j) := by
    obtain ⟨hP, hpq, hd₀, hbcV⟩ := ((hcoeff p hp hpl hph).1 n m hn hhalf ι).2.2 q hq
    rcases j with ij | (k | (k | (_ | (i | i))))
    · exact (hP ij.1 ij.2).2
    · exact (hpq (k.val + 1) (by omega) (by have := k.isLt; omega)).2.1
    · exact (hpq (k.val + 1) (by omega) (by have := k.isLt; omega)).2.2.2
    · exact hd₀.2
    · have hx := (hbcV i).2.2.1
      have hqE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
        simpa using ENNReal.ofReal_le_ofReal hq
      apply (eLpNorm_add_le hqE).trans
      simpa only [w, f, Sum.elim_inr, Sum.elim_inl, div_eq_mul_inv,
        N, Nat.succPNat_coe, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using hx
    · exact (hbcV i).2.2.2.2
  have htail (j : J) : μ.real {x | A * (n : ℝ) ^ (D * h) * w j < f j x} ≤
      Real.exp (-((n : ℝ) ^ h)) :=
    internal_profile_tail μ (f j) (hf j) (by exact_mod_cast n.pos) hD hh hC₀
      (le_max_right _ _) (hw j) (hmom j)
  have hevent : (coefficientEvent p n m hn (A * (n : ℝ) ^ (D * h)))ᶜ =
      ⋃ j : J, {x | A * (n : ℝ) ^ (D * h) * w j < f j x} := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iUnion]
    change (¬ x ∈ coefficientEvent p n m hn (A * (n : ℝ) ^ (D * h))) ↔
      ∃ j : J, A * (n : ℝ) ^ (D * h) * w j < f j x
    rw [show (∃ j : J, A * (n : ℝ) ^ (D * h) * w j < f j x) ↔
      ¬ ∀ j : J, f j x ≤ A * (n : ℝ) ^ (D * h) * w j by simp]
    apply not_congr
    dsimp only [J]
    simp only [coefficientEvent, hp, mem_ofPred_eq, f, w, Sum.forall,
      Sum.elim_inl, Sum.elim_inr, Prod.forall, forall_const, div_eq_mul_inv]
    rfl
  have hcard : (Fintype.card J : ℝ) ≤ 6 * (n : ℝ) ^ 2 := by
    have hnat : Fintype.card J ≤ 6 * (n : ℕ) ^ 2 := by
      dsimp [J]
      simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_unit]
      have hnpos := n.pos
      nlinarith [Nat.sub_le (n : ℕ) 1]
    exact_mod_cast hnat
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).mpr
  change μ.real _ ≤ _
  rw [hevent]
  calc
    _ ≤ ∑ j : J, μ.real {x | A * (n : ℝ) ^ (D * h) * w j < f j x} :=
      measureReal_iUnion_fintype_le _
    _ ≤ (Fintype.card J : ℝ) * Real.exp (-((n : ℝ) ^ h)) := by
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
        (Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => htail j)
    _ ≤ 6 * ((n : ℝ) ^ 2 * Real.exp (-((n : ℝ) ^ h))) := by
      nlinarith [mul_le_mul_of_nonneg_right hcard (Real.exp_pos (-((n : ℝ) ^ h))).le]
    _ ≤ 6 * (K * Real.exp (-(1 / 2) * (n : ℝ) ^ h)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [Real.rpow_two, neg_mul, one_mul] using hpoly (n : ℝ) (by exact_mod_cast n.pos)
    _ ≤ 6 * (K + 1) * Real.exp (-(1 / 2) * (n : ℝ) ^ h) := by
      nlinarith [Real.exp_pos (-(1 / 2) * (n : ℝ) ^ h)]

/-- Fourth-moment input for the full-cycle clause of Subsection 4.5.
Every entry of the ambient interaction Hessian has a uniform fourth moment
under either full active tilt. The Hessian is the physical interval
Hessian (`GoodBlocks.particleHessian_eq_second`). This does not include
the Hessian of the active penalty. -/
theorem full_interaction_fourth_moments (s : ℝ) (hs : 1 < s)
    (θ : PhysicalCutoff) (βlo βhi h : ℝ)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (hh : 0 < h) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ N : ℕ+, 4 ≤ (N : ℕ) → ∀ ι : Bool,
      ∀ a b : Fin (N : ℕ),
        MemLp (GoodBlocks.particleHessian p N a b) 4
          (tiltedParticleMeasure p N N le_rfl θ h ι) ∧
        eLpNorm (GoodBlocks.particleHessian p N a b) 4
          (tiltedParticleMeasure p N N le_rfl θ h ι) ≤ ENNReal.ofReal C := by
  obtain ⟨D, _, hm⟩ := interval_counting_coefficient_moments s hs
  obtain ⟨C, hC, hb⟩ := hm θ βlo βhi h hlo hle hh
  refine ⟨C * (4 : ℝ) ^ D, by positivity, ?_⟩
  intro p hp hpl hph N hN ι a b
  obtain ⟨hmem, hnorm⟩ := (hb p hp hpl hph).2 N hN ι 4 (by norm_num) a b
  norm_num only [ENNReal.ofReal_ofNat] at hmem hnorm
  refine ⟨hmem, hnorm.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  apply mul_le_of_le_one_right (by positivity)
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (le_add_of_nonneg_right (Nat.cast_nonneg _)) (by linarith)

/-- The entrywise exceptional `L²` estimate used in Subsection 4.5,
for an arbitrary measurable rare event. -/
theorem internal_full_interaction_exceptional (s : ℝ) (hs : 1 < s)
    (θ : PhysicalCutoff) (βlo βhi h : ℝ)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) (hh : 0 < h) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : Parameters, p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ N : ℕ+, 4 ≤ (N : ℕ) → ∀ ι : Bool,
      ∀ (E : Set (Riesz1.Configuration N)) (B t : ℝ), 0 ≤ B →
        (tiltedParticleMeasure p N N le_rfl θ h ι) E ≤ ENNReal.ofReal (B * Real.exp (-t)) →
        ∀ a b : Fin (N : ℕ),
          eLpNorm (GoodBlocks.particleHessian p N a b) 2
            ((tiltedParticleMeasure p N N le_rfl θ h ι).restrict E) ≤
              ENNReal.ofReal (C * B ^ (1 / 4 : ℝ) * Real.exp (-t / 4)) := by
  obtain ⟨C, hC, hb⟩ := full_interaction_fourth_moments s hs θ βlo βhi h hlo hle hh
  refine ⟨C, hC, ?_⟩
  intro p hp hpl hph N hN ι E B t hB hprob a b
  exact MomentEvent.restricted_two_norm_le (GoodBlocks.measurable_particleHessian p N a b)
    E hC.le hB (hb p hp hpl hph N hN ι a b).2 hprob

end Riesz2.DecayShort.ExceptionalEvent
