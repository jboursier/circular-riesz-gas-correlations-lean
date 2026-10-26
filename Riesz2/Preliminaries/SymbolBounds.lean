/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Preliminaries.InverseIntervalKernelCore
public import Riesz2.Frozen.External.PeriodicZeta
public import Riesz2.ToMathlib.CyclicSecondDifference
public import Riesz2.ToMathlib.IteratedDerivScaling
public import Riesz1.ToMathlib.HurwitzKernel.EndpointEstimates
public import Riesz1.ToMathlib.HurwitzKernel.Recurrence

/-!
# The lattice symbol and finite Fourier eigenvalues

The symbol is defined only on the open angular interval. Its absolutely convergent
curvature representation is identified with the ordered cosine limit, so no endpoint
value or rearrangement of a conditionally convergent series is used.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology BigOperators ContDiff

namespace Riesz2

/-- The lattice symbol of Subsection 2.4, on its exact open-interval domain.
The curvature series is absolutely convergent and equals the ordered cosine limit. -/
def latticeRieszSymbol (s : Riesz1.RieszExponent) (θ : Ioo (0 : ℝ) (2 * Real.pi)) : ℝ :=
  ∑' r : ℕ, latticeRieszCurvature s ((r : ℤ) + 1) *
    ((1 - Real.cos (((r + 1 : ℕ) : ℝ) * θ.val)) / (1 - Real.cos θ.val))

/-- The symbol is the ordered limit in Subsection 2.4. -/
theorem latticeRieszSymbol_tendsto (s : Riesz1.RieszExponent)
    (θ : Ioo (0 : ℝ) (2 * Real.pi)) :
    Tendsto (fun M : ℕ => 2 + 2 * ∑ r ∈ Finset.range M,
      (((r + 1 : ℕ) : ℝ) ^ (-s.val)) * Real.cos (((r + 1 : ℕ) : ℝ) * θ.val))
      atTop (𝓝 (latticeRieszSymbol s θ)) := by
  obtain ⟨S, hS, rfl, _⟩ := latticeRieszSymbol_ordered s θ θ.property.1 θ.property.2
  exact hS

/-- The strict lower bound from the proof of Lemma 2.5. -/
theorem latticeRieszSymbol_lower (s : Riesz1.RieszExponent)
    (θ : Ioo (0 : ℝ) (2 * Real.pi)) :
    (2 : ℝ) ^ (-s.val) ≤ latticeRieszSymbol s θ := by
  obtain ⟨S, _, rfl, hS, _⟩ := latticeRieszSymbol_ordered s θ θ.property.1 θ.property.2
  exact hS

/-- Nonzero cycle frequencies belong to the domain of the lattice symbol. -/
theorem cycleAngle_mem_Ioo (N : ℕ+) (k : Fin (N : ℕ)) (hk : k ≠ 0) :
    cycleAngle N k ∈ Ioo (0 : ℝ) (2 * Real.pi) := by
  have hN : (0 : ℝ) < N := by positivity
  have hk0 : (0 : ℝ) < k.val := by
    exact_mod_cast (Nat.pos_of_ne_zero (fun h => hk (Fin.ext h)))
  have hkN : (k.val : ℝ) < N := by exact_mod_cast k.isLt
  constructor
  · exact div_pos (mul_pos (by positivity) hk0) hN
  · rw [cycleAngle, div_lt_iff₀ hN]
    exact mul_lt_mul_of_pos_left hkN (by positivity)

/-- The zeta normalization in the proof of Lemma 2.5 is positive. -/
theorem symbolZetaFactor_pos (s : Riesz1.RieszExponent) :
    0 < (2 * Real.pi) ^ s.val /
      (2 * Real.Gamma s.val * Real.cos (Real.pi * s.val / 2)) := by
  have hc : 0 < Real.cos (Real.pi * s.val / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> nlinarith [Real.pi_pos, s.property.1, s.property.2]
  exact div_pos (Real.rpow_pos_of_pos (by positivity) _)
    (mul_pos (mul_pos (by norm_num) (Real.Gamma_pos_of_pos s.property.1)) hc)

/-- The exact periodic-zeta identity of the proof of Lemma 2.5.
The periodic-zeta connection formula is an explicit hypothesis. -/
theorem latticeRieszSymbol_eq_zeta (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (θ : Ioo (0 : ℝ) (2 * Real.pi)) :
    latticeRieszSymbol s θ = 2 +
      ((2 * Real.pi) ^ s.val / (2 * Real.Gamma s.val *
        Real.cos (Real.pi * s.val / 2))) *
      ((Riesz1.hurwitzZetaPos ((1 - s.val : ℝ) : ℂ) (θ.val / (2 * Real.pi))).re +
        (Riesz1.hurwitzZetaPos ((1 - s.val : ℝ) : ℂ)
          (1 - θ.val / (2 * Real.pi))).re) := by
  have hx0 : 0 < θ.val / (2 * Real.pi) := div_pos θ.property.1 (by positivity)
  have hx1 : θ.val / (2 * Real.pi) < 1 :=
    (div_lt_one (by positivity)).mpr θ.property.2
  obtain ⟨L, hL, heq⟩ := hz s.val (θ.val / (2 * Real.pi))
    s.property.1 s.property.2 hx0 hx1
  have hlim : Tendsto (fun M : ℕ => 2 + 2 * ∑ r ∈ Finset.range M,
      (((r + 1 : ℕ) : ℝ) ^ (-s.val)) * Real.cos (((r + 1 : ℕ) : ℝ) * θ.val))
      atTop (𝓝 (2 + 2 * L)) := by
    convert tendsto_const_nhds.add (tendsto_const_nhds.mul hL) using 1
    ext M
    congr 2
    apply Finset.sum_congr rfl
    intro r _
    congr 2
    push_cast
    field_simp
  have hS := tendsto_nhds_unique (latticeRieszSymbol_tendsto s θ) hlim
  rw [Riesz1.hurwitzZetaPos_eq_hurwitzZeta_of_mem hx0 hx1.le,
    Riesz1.hurwitzZetaPos_eq_hurwitzZeta_of_mem (by linarith) (by linarith), heq, hS]
  have hG := Real.Gamma_pos_of_pos s.property.1
  have hF := symbolZetaFactor_pos s
  have hpow : (2 * Real.pi) ^ s.val ≠ 0 := (Real.rpow_pos_of_pos (by positivity) _).ne'
  have hcos : Real.cos (Real.pi * s.val / 2) ≠ 0 := by
    intro h
    simp [h] at hF
  field_simp
  ring


/-- The full absolutely convergent transform of the curvature, used in the proof of Lemma 2.5. The original kernel series is never regrouped. -/
theorem latticeRieszCurvature_fourier (s : Riesz1.RieszExponent)
    (θ : Ioo (0 : ℝ) (2 * Real.pi)) :
    latticeFourier (fun n => (latticeRieszCurvature s n : ℂ))
      (by simpa using summable_norm_latticeRieszCurvature s) θ.val =
        ((-2 * (1 - Real.cos θ.val) * latticeRieszSymbol s θ : ℝ) : ℂ) := by
  let f : ℤ → ℂ := fun n => (latticeRieszCurvature s n : ℂ) *
    Complex.exp (Complex.I * (n : ℂ) * (θ.val : ℂ))
  have hs : Summable f := (summable_norm_latticeFourier _
    (by simpa using summable_norm_latticeRieszCurvature s) θ.val).of_norm
  have hp : Summable (fun n : ℕ => f ((n : ℤ) + 1)) :=
    hs.comp_injective (fun a b h => by omega)
  have hm : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) :=
    hs.comp_injective (fun a b h => by omega)
  have hpair (n : ℕ) : f ((n : ℤ) + 1) + f (-((n : ℤ) + 1)) =
      (2 * latticeRieszCurvature s ((n : ℤ) + 1) *
        Real.cos (((n + 1 : ℕ) : ℝ) * θ.val) : ℝ) := by
    dsimp only [f]
    rw [latticeRieszCurvature_even]
    have he : Complex.I * (-((n : ℤ) + 1) : ℤ) * (θ.val : ℂ) =
        -((((n + 1 : ℕ) : ℝ) * θ.val : ℝ) : ℂ) * Complex.I := by push_cast; ring
    have he' : Complex.I * (((n : ℤ) + 1) : ℤ) * (θ.val : ℂ) =
        ((((n + 1 : ℕ) : ℝ) * θ.val : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [he, he', ← mul_add, ← Complex.two_cos, ← Complex.ofReal_cos]
    push_cast
    ring
  have hsum : latticeFourier (fun n => (latticeRieszCurvature s n : ℂ))
      (by simpa using summable_norm_latticeRieszCurvature s) θ.val =
      (-2 : ℂ) + (2 * ∑' n : ℕ, latticeRieszCurvature s ((n : ℤ) + 1) *
        Real.cos (((n + 1 : ℕ) : ℝ) * θ.val) : ℝ) := by
    change (∑' n : ℤ, f n) = _
    rw [tsum_of_add_one_of_neg_add_one hp hm]
    have hz : f 0 = -2 := by simp [f, latticeRieszCurvature_zero]
    rw [hz]
    have hh := hp.tsum_add hm
    rw [show (∑' n : ℕ, f ((n : ℤ) + 1)) + -2 +
        (∑' n : ℕ, f (-((n : ℤ) + 1))) =
        -2 + ((∑' n : ℕ, f ((n : ℤ) + 1)) + (∑' n : ℕ, f (-((n : ℤ) + 1)))) by ring,
      ← hh]
    simp_rw [hpair]
    rw [← Complex.ofReal_tsum]
    simp only [mul_assoc, tsum_mul_left]
  have hD : 1 - Real.cos θ.val ≠ 0 := by
    intro h
    have hh : Real.cos θ.val = 1 := by linarith
    have := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [θ.property.1, Real.pi_pos])
      θ.property.2).mp hh
    linarith [θ.property.1]
  have hrepr : latticeRieszSymbol s θ =
      (1 - ∑' n : ℕ, latticeRieszCurvature s ((n : ℤ) + 1) *
        Real.cos (((n + 1 : ℕ) : ℝ) * θ.val)) / (1 - Real.cos θ.val) := by
    unfold latticeRieszSymbol
    simp_rw [← mul_div_assoc, mul_sub, mul_one]
    rw [tsum_div_const, (summable_latticeRieszCurvature_pos s).tsum_sub
      (summable_latticeRieszCurvature_cos s θ.val), tsum_latticeRieszCurvature_pos]
  rw [hsum]
  have hr : -2 + 2 * (∑' n : ℕ, latticeRieszCurvature s ((n : ℤ) + 1) *
      Real.cos (((n + 1 : ℕ) : ℝ) * θ.val)) =
      -2 * (1 - Real.cos θ.val) * latticeRieszSymbol s θ := by
    rw [hrepr]
    generalize (∑' n : ℕ, latticeRieszCurvature s ((n : ℤ) + 1) *
      Real.cos (((n + 1 : ℕ) : ℝ) * θ.val)) = T
    field_simp
    ring
  exact_mod_cast hr


/-- See the proof of Lemma 2.5 in the paper: every nonzero finite Fourier eigenvalue
is the ordered lattice symbol at the corresponding angle. This part does not need
the periodic-zeta external predicate. -/
theorem sampledRieszKernel_nonzero_eigenvalue (s : Riesz1.RieszExponent)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (k : Fin (N : ℕ)) (hk : k ≠ 0) :
    cycleFourier N (fun n => (sampledRieszKernel s N hN n : ℂ)) k =
      (latticeRieszSymbol s ⟨cycleAngle N k, cycleAngle_mem_Ioo N k hk⟩ : ℂ) := by
  let θ : Ioo (0 : ℝ) (2 * Real.pi) :=
    ⟨cycleAngle N k, cycleAngle_mem_Ioo N k hk⟩
  have hφ : Summable (fun n : ℤ => ‖(latticeRieszCurvature s n : ℂ)‖) := by
    simpa using summable_norm_latticeRieszCurvature s
  have hperiod : (fun n => (sampledSecondDifference s N hN n : ℂ)) =
      periodizeSequence N (fun n => (latticeRieszCurvature s n : ℂ)) hφ := by
    funext n
    rw [sampledSecondDifference_periodization]
    exact Complex.ofReal_tsum _
  have h := inverse_aliasing N _ hφ k
  rw [← hperiod, latticeRieszCurvature_fourier s θ] at h
  have hsecond := cycleFourier_secondDifference N hN
    (fun n => (sampledRieszKernel s N hN n : ℂ)) k
  have hcast : (fun n => (sampledSecondDifference s N hN n : ℂ)) =
      (fun n => (sampledRieszKernel s N hN (n + 1) : ℂ) +
        (sampledRieszKernel s N hN (n - 1) : ℂ) -
        2 * (sampledRieszKernel s N hN n : ℂ)) := by
    funext n
    simp only [sampledSecondDifference, Complex.ofReal_sub, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [hcast, hsecond, Complex.ofReal_mul] at h
  have hne : (-2 * (1 - Real.cos (cycleAngle N k)) : ℝ) ≠ 0 := by
    apply mul_ne_zero (by norm_num)
    intro hh
    have hc : Real.cos θ.val = 1 := by dsimp [θ]; linarith
    have hz := (Real.cos_eq_one_iff_of_lt_of_lt
      (by linarith [θ.property.1, Real.pi_pos]) θ.property.2).mp hc
    linarith [θ.property.1]
  apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hne)
  simpa only [Complex.ofReal_mul] using h

/-- Strict positivity of the nonzero eigenvalues, from the same curvature formula. -/
theorem sampledRieszKernel_nonzero_eigenvalue_pos (s : Riesz1.RieszExponent)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (k : Fin (N : ℕ)) (hk : k ≠ 0) :
    0 < (cycleFourier N (fun n => (sampledRieszKernel s N hN n : ℂ)) k).re := by
  rw [sampledRieszKernel_nonzero_eigenvalue s N hN k hk, Complex.ofReal_re]
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _)
    (latticeRieszSymbol_lower s _)


/-- Distance to the singular endpoints, Subsection 2.4. -/
def symbolEndpointDistance (θ : Ioo (0 : ℝ) (2 * Real.pi)) : ℝ :=
  min θ.val (2 * Real.pi - θ.val)

/-- Positivity of the endpoint distance on its exact domain. -/
theorem symbolEndpointDistance_pos (θ : Ioo (0 : ℝ) (2 * Real.pi)) :
    0 < symbolEndpointDistance θ :=
  lt_min θ.property.1 (sub_pos.mpr θ.property.2)

/-- The coefficient in the zeta expression for the symbol. -/
def symbolZetaFactor (s : Riesz1.RieszExponent) : ℝ :=
  (2 * Real.pi) ^ s.val /
    (2 * Real.Gamma s.val * Real.cos (Real.pi * s.val / 2))

/-- Identification with the existing Riesz 1 kernel, at the complementary exponent.
This is an equality only on the symbol's open angular domain. -/
theorem latticeRieszSymbol_eq_hurwitzKernel (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (θ : Ioo (0 : ℝ) (2 * Real.pi)) :
    latticeRieszSymbol s θ = 2 + symbolZetaFactor s *
      Riesz1.hurwitzKernel (1 - s.val) (θ.val / (2 * Real.pi)) := by
  have hx0 : 0 < θ.val / (2 * Real.pi) := div_pos θ.property.1 (by positivity)
  have hx1 : θ.val / (2 * Real.pi) < 1 :=
    (div_lt_one (by positivity)).mpr θ.property.2
  rw [latticeRieszSymbol_eq_zeta hz]
  have h := congrArg Complex.re
    (Riesz1.hurwitzZetaEven_re_eq_hurwitzZeta_add (1 - s.val) (θ.val / (2 * Real.pi)))
  rw [Riesz1.hurwitzZetaPos_eq_hurwitzZeta_of_mem hx0 hx1.le,
    Riesz1.hurwitzZetaPos_eq_hurwitzZeta_of_mem (by linarith) (by linarith)]
  change 2 + symbolZetaFactor s * _ = 2 + symbolZetaFactor s * _
  congr 2
  exact h.symm

/-- The circle distance in the reused kernel derivative bound equals the normalized
angular endpoint distance. -/
theorem symbol_circle_distance (θ : Ioo (0 : ℝ) (2 * Real.pi)) :
    dist ((θ.val / (2 * Real.pi) : ℝ) : UnitAddCircle) 0 =
      symbolEndpointDistance θ / (2 * Real.pi) := by
  have hx0 : 0 < θ.val / (2 * Real.pi) := div_pos θ.property.1 (by positivity)
  have hx1 : θ.val / (2 * Real.pi) < 1 :=
    (div_lt_one (by positivity)).mpr θ.property.2
  rw [dist_zero_right, UnitAddCircle.norm_eq, abs_sub_round_eq_min,
    Int.fract_eq_self.mpr ⟨hx0.le, hx1⟩]
  unfold symbolEndpointDistance
  rw [← min_div_div_right (by positivity : 0 ≤ 2 * Real.pi)]
  congr 1
  field_simp

/-- The complementary-kernel representative is smooth on the open angular interval. -/
theorem symbol_hurwitz_contDiff (s : Riesz1.RieszExponent) :
    ContDiffOn ℝ ∞ (fun θ : ℝ => 2 + symbolZetaFactor s *
      Riesz1.hurwitzKernel (1 - s.val) (θ / (2 * Real.pi)))
        (Ioo 0 (2 * Real.pi)) := by
  intro θ hθ
  have hK : ContDiffAt ℝ ∞ (Riesz1.hurwitzKernel (1 - s.val))
      (θ / (2 * Real.pi)) :=
    contDiffAt_const.mul (Riesz1.contDiffAt_hurwitzZetaEven_re_of_mem_Ioo
      (1 - s.val) (by linarith [s.property.2]) (by linarith [s.property.1])
      (θ / (2 * Real.pi)) (div_pos hθ.1 (by positivity))
      ((div_lt_one (by positivity)).mpr hθ.2))
  exact (contDiffAt_const.add (contDiffAt_const.mul
    (hK.comp θ (contDiffAt_id.div_const (2 * Real.pi))))).contDiffWithinAt


/-- The Hurwitz recurrence isolates the singular power. Its two shifted zeta
arguments remain in `[1/2, 3/2]`, so their continuous sum is bounded on the
closed half-cell. Reflection gives the estimate on the other half-cell. -/
theorem SymbolBoundsInternal.hurwitzKernel_recurrence_bounds (s : Riesz1.RieszExponent) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 0 < x → x < 1 →
      |Riesz1.hurwitzKernel s.val x - (min x (1 - x)) ^ (-s.val)| ≤ K := by
  let Z := fun x : ℝ => (Riesz1.hurwitzZetaPos (s.val : ℂ) x).re
  have hZ : ContinuousOn Z (Ioi 0) :=
    Complex.continuous_re.comp_continuousOn
      (Riesz1.contDiffOn_hurwitzZetaPos (by simpa using (by
        linarith [s.property.1] : (-1 : ℝ) < s.val))
        (by exact_mod_cast s.property.2.ne)).continuousOn
  let R := fun y : ℝ => Z (y + 1) + Z (1 - y)
  have hR : ContinuousOn R (Icc (0 : ℝ) (1 / 2)) := by
    apply ContinuousOn.add
    · exact hZ.comp (by fun_prop) (fun y hy => by change 0 < y + 1; linarith [hy.1])
    · exact hZ.comp (by fun_prop) (fun y hy => by change 0 < 1 - y; linarith [hy.2])
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hR.norm
  refine ⟨|B| + 1, by positivity, fun x hx0 hx1 => ?_⟩
  let y := min x (1 - x)
  have hy0 : 0 < y := lt_min hx0 (by linarith)
  have hy1 : y ≤ 1 / 2 := by
    dsimp [y]
    rcases le_total x (1 - x) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  have he : Riesz1.hurwitzKernel s.val y = Riesz1.hurwitzKernel s.val x := by
    dsimp only [y]
    rcases le_total x (1 - x) with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h, Riesz1.hurwitzKernel_one_sub]
  have hpair : Riesz1.hurwitzKernel s.val y = Z y + Z (1 - y) := by
    have hh := congrArg Complex.re
      (Riesz1.hurwitzZetaEven_re_eq_hurwitzZeta_add s.val y)
    rw [← Riesz1.hurwitzZetaPos_eq_hurwitzZeta_of_mem hy0 (by linarith),
      ← Riesz1.hurwitzZetaPos_eq_hurwitzZeta_of_mem (by linarith) (by linarith)] at hh
    exact hh
  have hrec : Z y = y ^ (-s.val) + Z (y + 1) := by
    have hh := congrArg Complex.re (Riesz1.hurwitzZetaPos_recurrence hy0 (s.val : ℂ))
    have hp : (y : ℂ) ^ (-(s.val : ℂ)) = (y ^ (-s.val) : ℝ) := by
      rw [← Complex.ofReal_neg, ← Complex.ofReal_cpow hy0.le]
    simpa only [Complex.add_re, hp, Complex.ofReal_re] using hh
  have hform : Riesz1.hurwitzKernel s.val x - y ^ (-s.val) = R y := by
    rw [← he, hpair, hrec]
    dsimp only [R]
    ring
  have hb : ‖R y‖ ≤ B := hB ⟨y, ⟨hy0.le, hy1⟩, rfl⟩
  rw [show min x (1 - x) = y from rfl, hform]
  exact (show |R y| ≤ B by simpa only [Real.norm_eq_abs] using hb).trans
    (by linarith [le_abs_self B])

/-- The two-sided symbol comparison of the proof of Lemma 2.5.
The constants are chosen before the angle. -/
theorem latticeRieszSymbol_power_bounds (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ θ : Ioo (0 : ℝ) (2 * Real.pi),
      c * symbolEndpointDistance θ ^ (s.val - 1) ≤ latticeRieszSymbol s θ ∧
      latticeRieszSymbol s θ ≤ C * symbolEndpointDistance θ ^ (s.val - 1) := by
  let t : Riesz1.RieszExponent := ⟨1 - s.val, by linarith [s.property.2],
    by linarith [s.property.1]⟩
  let A := symbolZetaFactor s
  have hA : 0 < A := symbolZetaFactor_pos s
  obtain ⟨K, hK, hremainder⟩ := SymbolBoundsInternal.hurwitzKernel_recurrence_bounds t
  let D := 1 + K
  have hD : 0 < D := by dsimp [D]; positivity
  let d := (2 : ℝ) ^ (-s.val)
  have hd : 0 < d := Real.rpow_pos_of_pos (by norm_num) _
  let Q := (2 * Real.pi) ^ (s.val - 1)
  have hQ : 0 < Q := Real.rpow_pos_of_pos (by positivity) _
  let c := d * A / (d + A * K) / Q
  let C := (2 + A * D) / Q
  refine ⟨c, C, by dsimp [c]; positivity, by dsimp [C]; positivity, fun θ => ?_⟩
  let x := θ.val / (2 * Real.pi)
  have hx0 : 0 < x := div_pos θ.property.1 (by positivity)
  have hx1 : x < 1 := (div_lt_one (by positivity)).mpr θ.property.2
  have hdist : dist (x : UnitAddCircle) 0 = min x (1 - x) := by
    rw [dist_zero_right, UnitAddCircle.norm_eq, abs_sub_round_eq_min,
      Int.fract_eq_self.mpr ⟨hx0.le, hx1⟩]
  have heq := latticeRieszSymbol_eq_hurwitzKernel hz s θ
  change latticeRieszSymbol s θ = 2 + A * Riesz1.hurwitzKernel t.val x at heq
  have hr := abs_le.mp (hremainder x hx0 hx1)
  have hm0 : 0 < min x (1 - x) := lt_min hx0 (by linarith)
  have hm1 : min x (1 - x) ≤ 1 := (min_le_left _ _).trans hx1.le
  have hp : 1 ≤ (min x (1 - x)) ^ (s.val - 1) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hm0 hm1 (by linarith [s.property.2])
  have hpower : (min x (1 - x)) ^ (s.val - 1) =
      symbolEndpointDistance θ ^ (s.val - 1) / Q := by
    rw [← hdist, symbol_circle_distance, Real.div_rpow
      (symbolEndpointDistance_pos θ).le (by positivity)]
  have ht : -t.val = s.val - 1 := by dsimp [t]; ring
  rw [ht] at hr
  have hl : (min x (1 - x)) ^ (s.val - 1) ≤ Riesz1.hurwitzKernel t.val x + K := by
    linarith [hr.1]
  have hu : |Riesz1.hurwitzKernel t.val x| ≤ D * (min x (1 - x)) ^ (s.val - 1) := by
    have hab : |Riesz1.hurwitzKernel t.val x| ≤ (min x (1 - x)) ^ (s.val - 1) + K := by
      apply abs_le.mpr
      constructor <;> linarith [hr.1, hr.2,
        Real.rpow_nonneg hm0.le (s.val - 1)]
    have hkp := mul_le_mul_of_nonneg_left hp hK.le
    dsimp only [D]
    nlinarith
  have hlow0 : d ≤ latticeRieszSymbol s θ := latticeRieszSymbol_lower s θ
  have hlo : d * A * ((min x (1 - x)) ^ (s.val - 1)) ≤
      (d + A * K) * latticeRieszSymbol s θ := by
    have h1 := mul_le_mul_of_nonneg_left hl hA.le
    have h2 := mul_le_mul_of_nonneg_left h1 hd.le
    have h3 := mul_le_mul_of_nonneg_left hlow0 (mul_nonneg hA.le hK.le)
    nlinarith
  have hup : latticeRieszSymbol s θ ≤
      (2 + A * D) * ((min x (1 - x)) ^ (s.val - 1)) := by
    have h1 := mul_le_mul_of_nonneg_left (le_abs_self (Riesz1.hurwitzKernel t.val x)) hA.le
    have h2 := mul_le_mul_of_nonneg_left hu hA.le
    nlinarith
  constructor
  · have hh : d * A * ((min x (1 - x)) ^ (s.val - 1)) / (d + A * K) ≤
        latticeRieszSymbol s θ :=
      (div_le_iff₀ (by positivity)).mpr (by nlinarith [hlo])
    rw [hpower] at hh
    dsimp only [c]
    convert hh using 1
    ring
  · rw [hpower] at hup
    dsimp only [C]
    convert hup using 1
    ring


/-- All derivative orders in the proof of Lemma 2.5, including
order zero. Derivatives are taken of the smooth ambient representative on the open
interval. No value is assigned to the symbol at its singular endpoints. -/
theorem latticeRieszSymbol_all_derivatives (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ : Ioo (0 : ℝ) (2 * Real.pi),
      |iteratedDeriv j (fun y : ℝ => 2 + symbolZetaFactor s *
        Riesz1.hurwitzKernel (1 - s.val) (y / (2 * Real.pi))) θ.val| ≤
          C * symbolEndpointDistance θ ^ (s.val - 1 - (j : ℝ)) := by
  cases j with
  | zero =>
    obtain ⟨_, C, _, hC, hb⟩ := latticeRieszSymbol_power_bounds hz s
    refine ⟨C, hC, fun θ => ?_⟩
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero,
      ← latticeRieszSymbol_eq_hurwitzKernel hz s θ]
    rw [abs_of_pos (lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _)
      (latticeRieszSymbol_lower s θ))]
    exact (hb θ).2
  | succ j =>
    let A := symbolZetaFactor s
    let a := (2 * Real.pi)⁻¹
    let p := s.val - 1 - ((j + 1 : ℕ) : ℝ)
    have hA : 0 < A := symbolZetaFactor_pos s
    have ha : 0 < a := inv_pos.mpr (by positivity)
    have hp : 0 < (2 * Real.pi) ^ p := Real.rpow_pos_of_pos (by positivity) _
    obtain ⟨D, hD, hbound⟩ := Riesz1.iteratedDeriv_hurwitzKernel_bound (1 - s.val)
      (by linarith [s.property.2]) (by linarith [s.property.1]) (j + 1)
    refine ⟨A * a ^ (j + 1) * D / (2 * Real.pi) ^ p, by positivity, fun θ => ?_⟩
    have hx0 : 0 < θ.val / (2 * Real.pi) := div_pos θ.property.1 (by positivity)
    have hx1 : θ.val / (2 * Real.pi) < 1 :=
      (div_lt_one (by positivity)).mpr θ.property.2
    have hxne : ((θ.val / (2 * Real.pi) : ℝ) : UnitAddCircle) ≠ 0 :=
      Riesz1.coe_ne_zero_of_mem_Ioo_int 0 _ (by simpa using And.intro hx0 hx1)
    have hb := hbound (θ.val / (2 * Real.pi)) hxne
    rw [show -(1 - s.val) - ((j + 1 : ℕ) : ℝ) = p by dsimp [p]; ring] at hb
    have he : iteratedDeriv (j + 1)
        (fun y : ℝ => Riesz1.hurwitzKernel (1 - s.val) (y / (2 * Real.pi))) θ.val =
        a ^ (j + 1) * iteratedDeriv (j + 1) (Riesz1.hurwitzKernel (1 - s.val))
          (θ.val / (2 * Real.pi)) := by
      simpa only [a, div_eq_mul_inv, mul_comm ((2 * Real.pi)⁻¹)] using
        congrFun (iteratedDeriv_scale (Riesz1.hurwitzKernel (1 - s.val)) a (j + 1)) θ.val
    rw [iteratedDeriv_const_add (Nat.succ_pos j), iteratedDeriv_const_mul_field, he,
      abs_mul, abs_of_pos hA, abs_mul, abs_of_pos (pow_pos ha _)]
    calc
      A * (a ^ (j + 1) * |iteratedDeriv (j + 1) (Riesz1.hurwitzKernel (1 - s.val))
          (θ.val / (2 * Real.pi))|) ≤
          A * (a ^ (j + 1) * (D * dist
            ((θ.val / (2 * Real.pi) : ℝ) : UnitAddCircle) 0 ^ p)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (pow_pos ha _).le) hA.le
      _ = _ := by
        rw [symbol_circle_distance, Real.div_rpow (symbolEndpointDistance_pos θ).le
          (by positivity)]
        ring

/-- See the proof of Lemma 2.5 in the paper, with the zeta identity, smoothness,
two-sided comparison and every derivative order together. Smoothness of a function
on an open interval is expressed by a smooth ambient representative agreeing there.
The existential representative leaves the symbol undefined at the endpoints. -/
theorem latticeRieszSymbol_bounds (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) :
    (∀ θ : Ioo (0 : ℝ) (2 * Real.pi),
      latticeRieszSymbol s θ = 2 + symbolZetaFactor s *
        ((Riesz1.hurwitzZetaPos ((1 - s.val : ℝ) : ℂ) (θ.val / (2 * Real.pi))).re +
          (Riesz1.hurwitzZetaPos ((1 - s.val : ℝ) : ℂ)
            (1 - θ.val / (2 * Real.pi))).re)) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ θ : Ioo (0 : ℝ) (2 * Real.pi),
      c * symbolEndpointDistance θ ^ (s.val - 1) ≤ latticeRieszSymbol s θ ∧
      latticeRieszSymbol s θ ≤ C * symbolEndpointDistance θ ^ (s.val - 1)) ∧
    ∃ F : ℝ → ℝ, ContDiffOn ℝ ∞ F (Ioo 0 (2 * Real.pi)) ∧
      (∀ θ : Ioo (0 : ℝ) (2 * Real.pi), F θ.val = latticeRieszSymbol s θ) ∧
      ∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ θ : Ioo (0 : ℝ) (2 * Real.pi),
        |iteratedDeriv j F θ.val| ≤
          C * symbolEndpointDistance θ ^ (s.val - 1 - (j : ℝ)) := by
  refine ⟨latticeRieszSymbol_eq_zeta hz s, latticeRieszSymbol_power_bounds hz s,
    (fun θ => 2 + symbolZetaFactor s *
      Riesz1.hurwitzKernel (1 - s.val) (θ / (2 * Real.pi))),
    symbol_hurwitz_contDiff s, ?_, latticeRieszSymbol_all_derivatives hz s⟩
  intro θ
  exact (latticeRieszSymbol_eq_hurwitzKernel hz s θ).symm

end Riesz2

end
