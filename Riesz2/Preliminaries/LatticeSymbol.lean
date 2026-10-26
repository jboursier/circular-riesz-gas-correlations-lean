/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.CyclicFourier
public import Riesz2.ToMathlib.DiscreteIntervalReconstruction
public import Riesz1.Frozen.RieszExponent
public import Riesz1.ToMathlib.LogConcave.NegativePower
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Aliasing for absolutely summable lattice sequences

The positive Fourier sign agrees with `cycleFourier`. The summability certificate in
each definition ensures that its series is evaluated only on its mathematical domain.
See Subsection 2.3 and the proof of Lemma 2.5 of the paper.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Riesz2

/-- The continuous representative of the positive-sign Fourier series of an absolutely
summable sequence (the ℓ¹ case of Subsection 2.3). -/
def latticeFourier (φ : ℤ → ℂ) (_hφ : Summable (fun n => ‖φ n‖)) (θ : ℝ) : ℂ :=
  ∑' n : ℤ, φ n * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))

/-- Periodization on the existing cycle carrier (Subsection 2.3). -/
def periodizeSequence (N : ℕ+) (φ : ℤ → ℂ) (_hφ : Summable (fun n => ‖φ n‖))
    (n : Fin (N : ℕ)) : ℂ :=
  ∑' l : ℤ, φ ((n.val : ℤ) + l * (N : ℕ))

private theorem norm_latticeCharacter (n : ℤ) (θ : ℝ) :
    ‖Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- The defining lattice series converges absolutely at every angle. -/
theorem summable_norm_latticeFourier (φ : ℤ → ℂ) (hφ : Summable (fun n => ‖φ n‖))
    (θ : ℝ) :
    Summable (fun n : ℤ => ‖φ n * Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ))‖) := by
  simpa only [norm_mul, norm_latticeCharacter, mul_one] using hφ

/-- The ℓ¹ Fourier representative is continuous (Subsection 2.3). -/
theorem continuous_latticeFourier (φ : ℤ → ℂ) (hφ : Summable (fun n => ‖φ n‖)) :
    Continuous (latticeFourier φ hφ) := by
  apply continuous_tsum (fun n => by fun_prop) hφ
  intro n θ
  simp only [norm_mul, norm_latticeCharacter, mul_one, le_refl]

/-- Absolute convergence of every periodization fibre (Subsection 2.3). -/
theorem summable_norm_periodizeSequence (N : ℕ+) (φ : ℤ → ℂ)
    (hφ : Summable (fun n => ‖φ n‖)) (x : ℤ) :
    Summable (fun l : ℤ => ‖φ (x + l * (N : ℕ))‖) := by
  apply hφ.comp_injective
  intro a b hab
  have hN : ((N : ℕ) : ℤ) ≠ 0 := by exact_mod_cast N.ne_zero
  exact mul_right_cancel₀ hN (add_left_cancel hab)

/-- Changing the integer lift does not change a periodization fibre. -/
theorem periodizeSequence_lift (N : ℕ+) (φ : ℤ → ℂ)
    (_hφ : Summable (fun n => ‖φ n‖)) (x q : ℤ) :
    (∑' l : ℤ, φ (x + q * (N : ℕ) + l * (N : ℕ))) =
      ∑' l : ℤ, φ (x + l * (N : ℕ)) := by
  simpa only [Equiv.coe_addLeft, add_mul, add_assoc] using
    (Equiv.addLeft q).tsum_eq (fun l : ℤ => φ (x + l * (N : ℕ)))

private theorem bijective_residue_lift (N : ℕ+) :
    Function.Bijective (fun p : Fin (N : ℕ) × ℤ => (p.1.val : ℤ) + p.2 * (N : ℕ)) := by
  constructor
  · rintro ⟨i, a⟩ ⟨j, b⟩ h
    have hij : i = j := eq_of_dvd_sub i j ⟨b - a, by dsimp at h ⊢; linarith⟩
    subst j
    have hN : ((N : ℕ) : ℤ) ≠ 0 := by exact_mod_cast N.ne_zero
    have hab : a = b := mul_right_cancel₀ hN (add_left_cancel h)
    subst b
    rfl
  · intro x
    exact ⟨(Riesz1.labelOf N x, x / (N : ℕ)), by
      simpa only [mul_comm] using (Riesz1.APG.val_labelOf_add (N := N) x).symm⟩

private def residueLiftEquiv (N : ℕ+) : (Fin (N : ℕ) × ℤ) ≃ ℤ :=
  Equiv.ofBijective _ (bijective_residue_lift N)

/-- Regroup an absolutely summable integer series by residues. -/
theorem tsum_eq_sum_periodizeSequence (N : ℕ+) (φ : ℤ → ℂ)
    (hφ : Summable (fun n => ‖φ n‖)) :
    (∑' x : ℤ, φ x) = ∑ n : Fin (N : ℕ), periodizeSequence N φ hφ n := by
  have hs : Summable (fun p : Fin (N : ℕ) × ℤ => φ (residueLiftEquiv N p)) :=
    (hφ.of_norm).comp_injective (residueLiftEquiv N).injective
  rw [← (residueLiftEquiv N).tsum_eq φ, hs.tsum_prod, tsum_fintype]
  rfl

private theorem character_residue_lift (N : ℕ+) (n k : Fin (N : ℕ)) (l : ℤ) :
    Complex.exp (Complex.I * ((n.val : ℤ) + l * (N : ℕ) : ℤ) *
      (cycleAngle N k : ℂ)) =
      Complex.exp (Complex.I * (n.val : ℂ) * (cycleAngle N k : ℂ)) := by
  rw [exp_mul_angle_eq_zpow, kernel_eq]
  apply zpow_eq_of_dvd
  exact ⟨l * k.val, by ring⟩

/-- Aliasing, the proof of Lemma 2.5: the Fourier transform of the
periodization is the continuous lattice representative sampled at the cycle frequencies.
The proof in fact works also for the one-point cycle. -/
theorem inverse_aliasing (N : ℕ+) (φ : ℤ → ℂ) (hφ : Summable (fun n => ‖φ n‖))
    (k : Fin (N : ℕ)) :
    cycleFourier N (periodizeSequence N φ hφ) k = latticeFourier φ hφ (cycleAngle N k) := by
  rw [latticeFourier, tsum_eq_sum_periodizeSequence N _
    (summable_norm_latticeFourier φ hφ (cycleAngle N k))]
  unfold cycleFourier periodizeSequence
  apply Finset.sum_congr rfl
  intro n _
  rw [← tsum_mul_right]
  apply tsum_congr
  intro l
  dsimp only
  rw [character_residue_lift]

/-- Injectivity of the finite transform, for comparing kernels through their symbols. -/
theorem cycleFourier_injective (N : ℕ+) : Function.Injective (cycleFourier N) := by
  intro f g h
  funext n
  have h' := congrArg (fun F => cycleFourierInv N F n) h
  simpa only [cycleFourierInv_cycleFourier] using h'

/-- The symbol of a periodized sequence with the constant mode supplied separately. -/
theorem cycleFourier_periodize_add_constant (N : ℕ+) (φ : ℤ → ℂ)
    (hφ : Summable (fun n => ‖φ n‖)) (c : ℂ) (k : Fin (N : ℕ)) :
    cycleFourier N (fun n => periodizeSequence N φ hφ n + c) k =
      latticeFourier φ hφ (cycleAngle N k) +
        if k = 0 then ((N : ℕ) : ℂ) * c else 0 := by
  have hadd : cycleFourier N (fun n => periodizeSequence N φ hφ n + c) k =
      cycleFourier N (periodizeSequence N φ hφ) k + cycleFourier N (fun _ => c) k := by
    simp only [cycleFourier, add_mul, Finset.sum_add_distrib]
  rw [hadd, inverse_aliasing, cycleFourier_const]

/-- Constant-mode correction in the proof of Lemma 2.5.
Nonzero symbols suffice: the identity holds for arbitrary complex kernels, without a
positivity assumption. The matrix is the existing circulant matrix, and its inverse is
the actual matrix inverse, whose existence follows from the nonzero symbols. -/
theorem inverse_aliasing_constant_mode (N : ℕ+) (φ : ℤ → ℂ)
    (hφ : Summable (fun n => ‖φ n‖)) (f : Fin (N : ℕ) → ℂ) (lambda : ℂ)
    (hlambda : cycleFourier N f 0 = lambda) (hlambdane : lambda ≠ 0)
    (hzero : latticeFourier φ hφ 0 = 0)
    (hinv : ∀ k : Fin (N : ℕ), k ≠ 0 →
      latticeFourier φ hφ (cycleAngle N k) = (cycleFourier N f k)⁻¹)
    (hne : ∀ k : Fin (N : ℕ), k ≠ 0 → cycleFourier N f k ≠ 0) :
    ∀ i j : Fin (N : ℕ), (cycleMatrix N f)⁻¹ i j =
      periodizeSequence N φ hφ
        (Riesz1.labelOf N ((j.val : ℤ) - (i.val : ℤ))) +
      1 / (((N : ℕ) : ℂ) * lambda) := by
  have hN : ((N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast N.ne_zero
  have hnonzero : ∀ k, cycleFourier N f k ≠ 0 := by
    intro k
    by_cases hk : k = 0
    · simpa only [hk, hlambda] using hlambdane
    · exact hne k hk
  obtain ⟨g, hg, hgFourier⟩ := cycleMatrix_inv_circulant f hnonzero
  have hFourier : ∀ k : Fin (N : ℕ),
      cycleFourier N (fun n => periodizeSequence N φ hφ n +
        1 / (((N : ℕ) : ℂ) * lambda)) k = (cycleFourier N f k)⁻¹ := by
    intro k
    rw [cycleFourier_periodize_add_constant]
    by_cases hk : k = 0
    · subst k
      simp only [cycleAngle, Fin.val_zero, Nat.cast_zero, mul_zero, zero_div,
        hzero, ite_true, zero_add, hlambda]
      field_simp
    · rw [ite_eq_right hk, add_zero, hinv k hk]
  have hg' : g = fun n => periodizeSequence N φ hφ n + 1 / (((N : ℕ) : ℂ) * lambda) :=
    cycleFourier_injective N (funext fun k => (hgFourier k).trans (hFourier k).symm)
  intro i j
  rw [hg i j, hg']

/-- The two-sided inverse property underlying the proof of Lemma 2.5.
This also rules out the totalized singular-matrix value of `Matrix.inv`. -/
theorem inverse_aliasing_mul_eq_one (N : ℕ+) (φ : ℤ → ℂ)
    (hφ : Summable (fun n => ‖φ n‖)) (f : Fin (N : ℕ) → ℂ) (lambda : ℂ)
    (hlambda : cycleFourier N f 0 = lambda) (hlambdane : lambda ≠ 0)
    (hzero : latticeFourier φ hφ 0 = 0)
    (hinv : ∀ k : Fin (N : ℕ), k ≠ 0 →
      latticeFourier φ hφ (cycleAngle N k) = (cycleFourier N f k)⁻¹)
    (hne : ∀ k : Fin (N : ℕ), k ≠ 0 → cycleFourier N f k ≠ 0) :
    let v := fun n => periodizeSequence N φ hφ n + 1 / (((N : ℕ) : ℂ) * lambda)
    cycleMatrix N f * cycleMatrix N v = 1 ∧
      cycleMatrix N v * cycleMatrix N f = 1 := by
  dsimp only
  have hV : cycleMatrix N (fun n => periodizeSequence N φ hφ n +
      1 / (((N : ℕ) : ℂ) * lambda)) =
      cycleUnitary N * Matrix.diagonal (fun k => (cycleFourier N f k)⁻¹) *
        star (cycleUnitary N) := by
    rw [cycleMatrix_eq_unitary_diagonal]
    apply congrArg (fun d : Fin (N : ℕ) → ℂ =>
      cycleUnitary N * Matrix.diagonal d * star (cycleUnitary N))
    funext k
    rw [cycleFourier_periodize_add_constant]
    by_cases hk : k = 0
    · subst k
      simp only [cycleAngle, Fin.val_zero, Nat.cast_zero, mul_zero, zero_div,
        hzero, ite_true, zero_add, hlambda]
      have hN : ((N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast N.ne_zero
      field_simp
    · rw [ite_eq_right hk, add_zero, hinv k hk]
  have hd : Matrix.diagonal (cycleFourier N f) *
      Matrix.diagonal (fun k => (cycleFourier N f k)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    apply mul_inv_cancel₀
    by_cases hk : k = 0
    · simpa only [hk, hlambda] using hlambdane
    · exact hne k hk
  have hprod : cycleMatrix N f * cycleMatrix N (fun n => periodizeSequence N φ hφ n +
      1 / (((N : ℕ) : ℂ) * lambda)) = 1 := by
    rw [cycleMatrix_eq_unitary_diagonal, hV]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star (cycleUnitary N)) (cycleUnitary N),
      star_cycleUnitary_mul_cycleUnitary, Matrix.one_mul,
      ← Matrix.mul_assoc (Matrix.diagonal (cycleFourier N f)), hd, Matrix.one_mul,
      cycleUnitary_mul_star_cycleUnitary]
  exact ⟨hprod, mul_eq_one_comm.mp hprod⟩

private theorem real_inverse_of_complex_inverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (B : Matrix ι ι ℂ)
    (hAB : A.map Complex.ofReal * B = 1) (hBA : B * A.map Complex.ofReal = 1) :
    (A⁻¹).map Complex.ofReal = B := by
  have hreal : A * B.map Complex.re = 1 := by
    ext i j
    have h := congrArg Complex.re (congrFun (congrFun hAB i) j)
    simpa only [Matrix.mul_apply, Matrix.map_apply, Complex.re_sum, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Matrix.one_apply,
      apply_ite Complex.re, Complex.one_re, Complex.zero_re] using h
  have hmap : A.map Complex.ofReal * (B.map Complex.re).map Complex.ofReal = 1 := by
    have hA : A.map Complex.ofRealHom = A.map Complex.ofReal := by
      ext i j
      exact Complex.ofRealHom_eq_coe _
    have hB : (B.map Complex.re).map Complex.ofRealHom =
        (B.map Complex.re).map Complex.ofReal := by
      ext i j
      exact Complex.ofRealHom_eq_coe _
    rw [← hA, ← hB, ← Matrix.map_mul, hreal, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [Matrix.inv_eq_right_inv hreal]
  calc
    (B.map Complex.re).map Complex.ofReal = 1 * (B.map Complex.re).map Complex.ofReal :=
      (one_mul _).symm
    _ = (B * A.map Complex.ofReal) * (B.map Complex.re).map Complex.ofReal := by rw [hBA]
    _ = B := by rw [Matrix.mul_assoc, hmap, mul_one]

/-- See the proof of Lemma 2.5 in the paper, for a real even circulant with `N ≥ 2`. The inverse entries are those of the real matrix.
The equality is written in `ℂ` to retain the complex periodized sequence. -/
theorem inverse_aliasing_real (N : ℕ+) (_hN : 2 ≤ (N : ℕ)) (φ : ℤ → ℂ)
    (hφ : Summable (fun n => ‖φ n‖)) (f : Fin (N : ℕ) → ℝ)
    (_heven : ∀ x : ℤ, f (Riesz1.labelOf N (-x)) = f (Riesz1.labelOf N x))
    (lambda : ℝ) (hlambda : cycleFourier N (fun n => (f n : ℂ)) 0 = (lambda : ℂ))
    (hlambdane : lambda ≠ 0) (hzero : latticeFourier φ hφ 0 = 0)
    (hinv : ∀ k : Fin (N : ℕ), k ≠ 0 → latticeFourier φ hφ (cycleAngle N k) =
      (cycleFourier N (fun n => (f n : ℂ)) k)⁻¹)
    (hne : ∀ k : Fin (N : ℕ), k ≠ 0 → cycleFourier N (fun n => (f n : ℂ)) k ≠ 0) :
    (∀ k : Fin (N : ℕ), cycleFourier N (periodizeSequence N φ hφ) k =
      latticeFourier φ hφ (cycleAngle N k)) ∧
    (∀ i j : Fin (N : ℕ),
      ((Matrix.of (fun a b : Fin (N : ℕ) =>
        f (Riesz1.labelOf N ((b.val : ℤ) - a.val))))⁻¹ i j : ℂ) =
      periodizeSequence N φ hφ (Riesz1.labelOf N ((j.val : ℤ) - i.val)) +
        1 / (((N : ℕ) : ℂ) * (lambda : ℂ))) := by
  refine ⟨fun k => inverse_aliasing N φ hφ k, ?_⟩
  have hneC : (lambda : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlambdane
  obtain ⟨hAB, hBA⟩ := inverse_aliasing_mul_eq_one N φ hφ (fun n => (f n : ℂ))
    (lambda : ℂ) hlambda hneC hzero hinv hne
  let A : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ :=
    Matrix.of fun a b => f (Riesz1.labelOf N ((b.val : ℤ) - a.val))
  let B := cycleMatrix N (fun n => periodizeSequence N φ hφ n +
    1 / (((N : ℕ) : ℂ) * (lambda : ℂ)))
  have h := real_inverse_of_complex_inverse A B hAB hBA
  intro i j
  exact congrFun (congrFun h i) j

/-- The regularized whole-lattice kernel in Subsection 2.4. The diagonal
value two is the specified regularization. Off zero this is the ordinary power. -/
def latticeRieszKernel (s : Riesz1.RieszExponent) (n : ℤ) : ℝ :=
  if n = 0 then 2 else |(n : ℝ)| ^ (-s.val)

/-- Discrete curvature of the lattice kernel (Subsection 2.4). -/
def latticeRieszCurvature (s : Riesz1.RieszExponent) (n : ℤ) : ℝ :=
  latticeRieszKernel s (n + 1) + latticeRieszKernel s (n - 1) -
    2 * latticeRieszKernel s n

/-- Evenness of the whole-lattice kernel. -/
theorem latticeRieszKernel_even (s : Riesz1.RieszExponent) (n : ℤ) :
    latticeRieszKernel s (-n) = latticeRieszKernel s n := by
  simp only [latticeRieszKernel, neg_eq_zero, Int.cast_neg, abs_neg]

/-- Evenness of the lattice curvature. -/
theorem latticeRieszCurvature_even (s : Riesz1.RieszExponent) (n : ℤ) :
    latticeRieszCurvature s (-n) = latticeRieszCurvature s n := by
  simp only [latticeRieszCurvature, show -n + 1 = -(n - 1) by omega,
    show -n - 1 = -(n + 1) by omega, latticeRieszKernel_even]
  ring

/-- The negative curvature at zero is kept out of all nonzero-residue estimates. -/
theorem latticeRieszCurvature_zero (s : Riesz1.RieszExponent) :
    latticeRieszCurvature s 0 = -2 := by
  norm_num [latticeRieszCurvature, latticeRieszKernel]

/-- The exceptional first curvature in the proof of Lemma 2.5. -/
theorem latticeRieszCurvature_one (s : Riesz1.RieszExponent) :
    latticeRieszCurvature s 1 = (2 : ℝ) ^ (-s.val) := by
  norm_num [latticeRieszCurvature, latticeRieszKernel]

/-- Away from the regularized site, nonnegative lattice curvature follows from the
proved Riesz 1 negative-power convexity theorem. This is a component of the proof of Lemma 2.5, without the quantitative comparison. -/
theorem latticeRieszCurvature_nonneg (s : Riesz1.RieszExponent) {r : ℤ} (hr : 1 ≤ r) :
    0 ≤ latticeRieszCurvature s r := by
  by_cases hr1 : r = 1
  · rw [hr1, latticeRieszCurvature_one]
    exact (Real.rpow_pos_of_pos (by norm_num) _).le
  have hr2 : 2 ≤ r := by omega
  have hpos : (0 : ℝ) < (r : ℝ) - 1 := by exact_mod_cast (show 0 < r - 1 by omega)
  have hplus : (0 : ℝ) < (r : ℝ) + 1 := by linarith
  have hmid := (Riesz1.convexOn_rpow_neg_Ioi s.property.1).2
    (show (r : ℝ) - 1 ∈ Set.Ioi (0 : ℝ) from hpos)
    (show (r : ℝ) + 1 ∈ Set.Ioi (0 : ℝ) from hplus)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  have hcenter : (1 / 2 : ℝ) * ((r : ℝ) - 1) + (1 / 2 : ℝ) * ((r : ℝ) + 1) = r := by ring
  simp only [smul_eq_mul, hcenter] at hmid
  have hr0 : r ≠ 0 := by omega
  have hrp : r + 1 ≠ 0 := by omega
  have hrm : r - 1 ≠ 0 := by omega
  simp only [latticeRieszCurvature, latticeRieszKernel, hr0, hrp, hrm, ite_false,
    Int.cast_add, Int.cast_one, Int.cast_sub, abs_of_pos hpos, abs_of_pos hplus,
    abs_of_pos (show (0 : ℝ) < r by exact_mod_cast (show 0 < r by omega))]
  linarith

/-- The ordinary power formula at positive lattice sites. -/
theorem latticeRieszKernel_pos_nat (s : Riesz1.RieszExponent) {r : ℕ} (hr : 1 ≤ r) :
    latticeRieszKernel s r = (r : ℝ) ^ (-s.val) := by
  have hr0 : (r : ℤ) ≠ 0 := by omega
  simp only [latticeRieszKernel, hr0, ite_false, Int.cast_natCast,
    abs_of_nonneg (show (0 : ℝ) ≤ r from Nat.cast_nonneg r)]

/-- Telescoping identity for the positive curvature partial sums, as used in the
proof of Lemma 2.5. -/
theorem sum_latticeRieszCurvature (s : Riesz1.RieszExponent) (M : ℕ) :
    (∑ r ∈ Finset.range M, latticeRieszCurvature s ((r : ℤ) + 1)) =
      1 + latticeRieszKernel s ((M : ℤ) + 1) - latticeRieszKernel s M := by
  have htel := Finset.sum_range_sub
    (fun r : ℕ => latticeRieszKernel s ((r : ℤ) + 1) - latticeRieszKernel s r) M
  have hcurv (r : ℕ) : latticeRieszCurvature s ((r : ℤ) + 1) =
      (latticeRieszKernel s (((r + 1 : ℕ) : ℤ) + 1) -
        latticeRieszKernel s ((r + 1 : ℕ) : ℤ)) -
      (latticeRieszKernel s ((r : ℤ) + 1) - latticeRieszKernel s r) := by
    simp only [latticeRieszCurvature, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    ring
  simp_rw [hcurv]
  rw [htel]
  norm_num [latticeRieszKernel]
  ring

/-- Absolute summability of the positive curvature series. This follows from
convexity and telescoping, without assuming the quantitative power comparison. -/
theorem summable_latticeRieszCurvature_pos (s : Riesz1.RieszExponent) :
    Summable (fun r : ℕ => latticeRieszCurvature s ((r : ℤ) + 1)) := by
  apply summable_of_sum_range_le (c := 1)
    (fun r => latticeRieszCurvature_nonneg s (by omega))
  intro M
  by_cases hM : M = 0
  · subst M
    simp
  rw [sum_latticeRieszCurvature]
  have hM1 : 1 ≤ M := by omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  rw [show (M : ℤ) + 1 = ((M + 1 : ℕ) : ℤ) by omega,
    latticeRieszKernel_pos_nat s (by omega), latticeRieszKernel_pos_nat s hM1]
  have hmono : ((M + 1 : ℕ) : ℝ) ^ (-s.val) ≤ (M : ℝ) ^ (-s.val) :=
    Real.rpow_le_rpow_of_nonpos hMpos (by norm_num) (by linarith [s.property.1])
  linarith

/-- Absolute convergence of the curvature sequence on the whole integer lattice,
including the separate (negative) value at zero. -/
theorem summable_norm_latticeRieszCurvature (s : Riesz1.RieszExponent) :
    Summable (fun r : ℤ => ‖latticeRieszCurvature s r‖) := by
  have hs := summable_latticeRieszCurvature_pos s
  have hnat : Summable (fun r : ℕ => latticeRieszCurvature s r) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.cast_add, Nat.cast_one] using hs
  have hneg : Summable (fun r : ℕ => latticeRieszCurvature s (-((r : ℤ) + 1))) := by
    simpa only [latticeRieszCurvature_even] using hs
  exact hnat.norm.of_nat_of_neg_add_one hneg.norm

/-- The whole-lattice kernel tends to zero along positive sites. -/
theorem tendsto_latticeRieszKernel_nat (s : Riesz1.RieszExponent) :
    Filter.Tendsto (fun M : ℕ => latticeRieszKernel s M) Filter.atTop (nhds 0) := by
  have h := (tendsto_rpow_neg_atTop s.property.1).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply h.congr'
  filter_upwards [Filter.eventually_ge_atTop 1] with M hM
  exact (latticeRieszKernel_pos_nat s hM).symm

/-- The positive lattice curvatures have total mass one (proof of Lemma 2.5). The series here is absolutely convergent. -/
theorem tsum_latticeRieszCurvature_pos (s : Riesz1.RieszExponent) :
    (∑' r : ℕ, latticeRieszCurvature s ((r : ℤ) + 1)) = 1 := by
  have h := tendsto_latticeRieszKernel_nat s
  have hshift : Filter.Tendsto (fun M : ℕ => latticeRieszKernel s ((M : ℤ) + 1))
      Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using h.comp (Filter.tendsto_add_atTop_nat 1)
  have hlim : Filter.Tendsto
      (fun M : ℕ => ∑ r ∈ Finset.range M, latticeRieszCurvature s ((r : ℤ) + 1))
      Filter.atTop (nhds 1) := by
    simp only [sum_latticeRieszCurvature]
    convert (tendsto_const_nhds.add hshift).sub h using 1
    norm_num
  exact tendsto_nhds_unique (summable_latticeRieszCurvature_pos s).hasSum.tendsto_sum_nat hlim

private theorem cosine_recurrence (θ : ℝ) (n : ℕ) :
    Real.cos (((n + 2 : ℕ) : ℝ) * θ) + Real.cos ((n : ℝ) * θ) =
      2 * Real.cos θ * Real.cos (((n + 1 : ℕ) : ℝ) * θ) := by
  have hp : ((n + 2 : ℕ) : ℝ) * θ = ((n + 1 : ℕ) : ℝ) * θ + θ := by push_cast; ring
  have hm : (n : ℝ) * θ = ((n + 1 : ℕ) : ℝ) * θ - θ := by push_cast; ring
  rw [hp, hm, Real.cos_add, Real.cos_sub]
  ring

private theorem latticeRieszCurvature_nat_succ (s : Riesz1.RieszExponent) (r : ℕ) :
    latticeRieszCurvature s ((r : ℤ) + 1) =
      latticeRieszKernel s ((r + 2 : ℕ) : ℤ) + latticeRieszKernel s r -
        2 * latticeRieszKernel s ((r + 1 : ℕ) : ℤ) := by
  simp only [latticeRieszCurvature, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    add_sub_cancel_right]
  congr 2

/-- Absolute convergence of the cosine series of lattice curvatures. This is
distinct from the conditionally convergent series of the original kernel. -/
theorem summable_latticeRieszCurvature_cos (s : Riesz1.RieszExponent) (θ : ℝ) :
    Summable (fun r : ℕ => latticeRieszCurvature s ((r : ℤ) + 1) *
      Real.cos (((r + 1 : ℕ) : ℝ) * θ)) := by
  apply (summable_latticeRieszCurvature_pos s).of_norm_bounded
  intro r
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (latticeRieszCurvature_nonneg s (by omega))]
  exact mul_le_of_le_one_right (latticeRieszCurvature_nonneg s (by omega))
    (Real.abs_cos_le_one _)

/-- The ordered lattice cosine series converges, and has the positive curvature
representation in the proof of Lemma 2.5. In particular its
limit is at least `2^(-s)`. This theorem does not include the quantitative bounds
on the individual curvatures from the first part of that . -/
theorem latticeRieszSymbol_ordered (s : Riesz1.RieszExponent) (θ : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 2 * Real.pi) :
    ∃ S : ℝ,
      Filter.Tendsto (fun M : ℕ => 2 + 2 *
        ∑ r ∈ Finset.range M, (((r + 1 : ℕ) : ℝ) ^ (-s.val)) *
          Real.cos (((r + 1 : ℕ) : ℝ) * θ)) Filter.atTop (nhds S) ∧
      S = ∑' r : ℕ, latticeRieszCurvature s ((r : ℤ) + 1) *
        ((1 - Real.cos (((r + 1 : ℕ) : ℝ) * θ)) / (1 - Real.cos θ)) ∧
      (2 : ℝ) ^ (-s.val) ≤ S ∧ 0 < S := by
  have hcos : Real.cos θ ≠ 1 := by
    intro h
    have hzero := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos]) hθ1).mp h
    linarith
  have hD : 0 < 1 - Real.cos θ := sub_pos.mpr (lt_of_le_of_ne (Real.cos_le_one _) hcos)
  let T := ∑' r : ℕ, latticeRieszCurvature s ((r : ℤ) + 1) *
    Real.cos (((r + 1 : ℕ) : ℝ) * θ)
  let S := (1 - T) / (1 - Real.cos θ)
  have hkernel := tendsto_latticeRieszKernel_nat s
  have hkernel' : Filter.Tendsto (fun M : ℕ => latticeRieszKernel s ((M + 1 : ℕ) : ℤ))
      Filter.atTop (nhds 0) := hkernel.comp (Filter.tendsto_add_atTop_nat 1)
  have hbound (v : ℕ → ℝ) (hv : Filter.Tendsto v Filter.atTop (nhds 0)) (j : ℕ) :
      Filter.Tendsto (fun M : ℕ => v M * Real.cos (((M + j : ℕ) : ℝ) * θ))
        Filter.atTop (nhds 0) := by
    apply squeeze_zero_norm (a := fun M => |v M|) ?_ (by simpa using hv.abs)
    intro M
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have hboundary : Filter.Tendsto (fun M : ℕ =>
      latticeRieszKernel s ((M + 1 : ℕ) : ℤ) * Real.cos ((M : ℝ) * θ) -
        latticeRieszKernel s M * Real.cos (((M + 1 : ℕ) : ℝ) * θ))
      Filter.atTop (nhds 0) := by
    simpa only [Nat.add_zero, sub_self] using (hbound _ hkernel' 0).sub (hbound _ hkernel 1)
  have hfinite (M : ℕ) :
      2 + 2 * (∑ r ∈ Finset.range M, (((r + 1 : ℕ) : ℝ) ^ (-s.val)) *
        Real.cos (((r + 1 : ℕ) : ℝ) * θ)) =
      (1 - (∑ r ∈ Finset.range M, latticeRieszCurvature s ((r : ℤ) + 1) *
        Real.cos (((r + 1 : ℕ) : ℝ) * θ)) +
        (latticeRieszKernel s ((M + 1 : ℕ) : ℤ) * Real.cos ((M : ℝ) * θ) -
          latticeRieszKernel s M * Real.cos (((M + 1 : ℕ) : ℝ) * θ))) /
        (1 - Real.cos θ) := by
    have h := cosine_second_difference_sum (fun n : ℕ => latticeRieszKernel s n)
      (fun n : ℕ => Real.cos ((n : ℝ) * θ)) (Real.cos θ)
      (by simp) (by simp) (cosine_recurrence θ) M
    simp_rw [← latticeRieszCurvature_nat_succ] at h
    have ha0 : latticeRieszKernel s 0 = 2 := by simp [latticeRieszKernel]
    have ha1 : latticeRieszKernel s 1 = 1 := by simp [latticeRieszKernel]
    simp only [Nat.cast_zero, Nat.cast_one, ha0, ha1] at h
    have heq :
        (2 + 2 * (∑ r ∈ Finset.range M, latticeRieszKernel s ((r + 1 : ℕ) : ℤ) *
          Real.cos (((r + 1 : ℕ) : ℝ) * θ))) * (1 - Real.cos θ) =
        1 - (∑ r ∈ Finset.range M, latticeRieszCurvature s ((r : ℤ) + 1) *
          Real.cos (((r + 1 : ℕ) : ℝ) * θ)) +
          (latticeRieszKernel s ((M + 1 : ℕ) : ℤ) * Real.cos ((M : ℝ) * θ) -
            latticeRieszKernel s M * Real.cos (((M + 1 : ℕ) : ℝ) * θ)) := by
      linear_combination (1 / 2 : ℝ) * h
    apply (eq_div_iff hD.ne').mpr
    simpa only [latticeRieszKernel_pos_nat s (Nat.succ_le_succ (Nat.zero_le _))] using heq
  have hlim : Filter.Tendsto (fun M : ℕ => 2 + 2 *
      ∑ r ∈ Finset.range M, (((r + 1 : ℕ) : ℝ) ^ (-s.val)) *
        Real.cos (((r + 1 : ℕ) : ℝ) * θ)) Filter.atTop (nhds S) := by
    simp_rw [hfinite]
    have h := (((tendsto_const_nhds (x := (1 : ℝ))).sub
      (summable_latticeRieszCurvature_cos s θ).hasSum.tendsto_sum_nat).add hboundary).div_const
      (1 - Real.cos θ)
    simpa only [add_zero] using h
  have hs := summable_latticeRieszCurvature_pos s
  have hc := summable_latticeRieszCurvature_cos s θ
  have hseries : Summable (fun r : ℕ => latticeRieszCurvature s ((r : ℤ) + 1) *
      ((1 - Real.cos (((r + 1 : ℕ) : ℝ) * θ)) / (1 - Real.cos θ))) := by
    convert (hs.sub hc).div_const (1 - Real.cos θ) using 1
    ext r
    ring
  have hrepr : S = ∑' r : ℕ, latticeRieszCurvature s ((r : ℤ) + 1) *
      ((1 - Real.cos (((r + 1 : ℕ) : ℝ) * θ)) / (1 - Real.cos θ)) := by
    simp_rw [← mul_div_assoc, mul_sub, mul_one]
    rw [tsum_div_const, hs.tsum_sub hc, tsum_latticeRieszCurvature_pos]
  have hlower : (2 : ℝ) ^ (-s.val) ≤ S := by
    rw [hrepr]
    have h := hseries.le_tsum 0 (fun r _ =>
      mul_nonneg (latticeRieszCurvature_nonneg s (by omega))
        (div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) hD.le))
    simpa only [Nat.zero_add, Nat.cast_one, one_mul, Nat.cast_zero, zero_add,
      latticeRieszCurvature_one, div_self hD.ne', mul_one] using h
  exact ⟨S, hlim, hrepr, hlower, lt_of_lt_of_le (Real.rpow_pos_of_pos (by norm_num) _) hlower⟩

end Riesz2

end
end
