/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriGoodComparison
public import Riesz1.Variance.APrioriGoodGradientCount
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic

/-!
# Finite Fourier conventions on the cycle

The cycle `C_N` is `Fin N`, with the residue of an integer `x` given by `Riesz1.labelOf N x`.
Frequencies `θ_k = 2πk/N` are indexed by the same carrier `Fin N`, through the representatives
`k = 0, …, N - 1`.

The finite Fourier transform `cycleFourier` carries the positive sign of Subsection 2.3:
`𝓕_d f(θ_k) = ∑_n f(n) e^{i n θ_k}`. Its inverse is `cycleFourierInv`, and the cyclic convolution
is `cycleConvolution`. Mathlib's `ZMod.dft` has the negative sign, and `cycleFourier_eq_zmod_dft`
gives the translation.

The proofs write every character as a power `cycleRoot N ^ m` of the primitive root
`cycleRoot N = e^{2πi/N}`, with `m` an integer. The orthogonality relation is then a geometric sum.

Inversion, Parseval, convolution and matrix diagonalization follow the conventions
of Subsection 2.3.
-/

@[expose] public section

open Finset
open scoped ComplexConjugate ComplexOrder Real

namespace Riesz2

variable {N : ℕ+}

/-- The angle `θ_k = 2πk/N` of the frequency index `k` in `{0, …, N - 1}`. -/
noncomputable def cycleAngle (N : ℕ+) (k : Fin (N : ℕ)) : ℝ :=
  2 * π * ((k : ℕ) : ℝ) / ((N : ℕ) : ℝ)

/-- The primitive root `e^{2πi/N}` of unity. Its integer powers are the characters of the cycle. -/
noncomputable def cycleRoot (N : ℕ+) : ℂ :=
  Complex.exp (2 * π * Complex.I / ((N : ℕ) : ℂ))

/-- The finite Fourier transform of `f` with the positive sign (Subsection 2.3):
`𝓕_d f(θ_k) = ∑_{n=0}^{N-1} f(n) e^{i n θ_k}`. -/
noncomputable def cycleFourier (N : ℕ+) (f : Fin (N : ℕ) → ℂ) (k : Fin (N : ℕ)) : ℂ :=
  ∑ n : Fin (N : ℕ), f n * Complex.exp (Complex.I * ((n : ℕ) : ℂ) * (cycleAngle N k : ℂ))

/-- The inverse finite Fourier transform (Subsection 2.3):
`𝓕_d^{-1} Φ(n) = N^{-1} ∑_{k=0}^{N-1} Φ(θ_k) e^{-i n θ_k}`. -/
noncomputable def cycleFourierInv (N : ℕ+) (Φ : Fin (N : ℕ) → ℂ) (n : Fin (N : ℕ)) : ℂ :=
  ((N : ℕ) : ℂ)⁻¹ * ∑ k : Fin (N : ℕ),
    Φ k * Complex.exp (-(Complex.I * ((n : ℕ) : ℂ) * (cycleAngle N k : ℂ)))

/-- The cyclic convolution `(f * u)(i) = ∑_j f(i - j) u(j)` (Subsection 2.3), where the
argument `i - j` of `f` is read through its residue `Riesz1.labelOf N`. -/
noncomputable def cycleConvolution (N : ℕ+) (f u : Fin (N : ℕ) → ℂ) (i : Fin (N : ℕ)) : ℂ :=
  ∑ j : Fin (N : ℕ), f (Riesz1.labelOf N (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) * u j

/-! ### The primitive root and the character sums -/

/-- The root `cycleRoot N` is a primitive `N`-th root of unity. -/
theorem isPrimitiveRoot_cycleRoot (N : ℕ+) : IsPrimitiveRoot (cycleRoot N) (N : ℕ) :=
  Complex.isPrimitiveRoot_exp (N : ℕ) N.ne_zero

theorem cycleRoot_ne_zero (N : ℕ+) : cycleRoot N ≠ 0 :=
  Complex.exp_ne_zero _

/-- The character `e^{i x θ_k}` of an integer `x`, written as a power of `cycleRoot N`. -/
theorem exp_mul_angle_eq_zpow (x : ℤ) (k : Fin (N : ℕ)) :
    Complex.exp (Complex.I * (x : ℂ) * (cycleAngle N k : ℂ)) =
      cycleRoot N ^ (x * ((k : ℕ) : ℤ)) := by
  have hN : ((N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast N.ne_zero
  rw [cycleRoot, ← Complex.exp_int_mul]
  congr 1
  unfold cycleAngle
  push_cast
  field_simp

/-- The kernel `e^{i n θ_k}` of the forward transform, written as a power of `cycleRoot N`. -/
theorem kernel_eq (n k : Fin (N : ℕ)) :
    Complex.exp (Complex.I * ((n : ℕ) : ℂ) * (cycleAngle N k : ℂ)) =
      cycleRoot N ^ (((n : ℕ) : ℤ) * ((k : ℕ) : ℤ)) := by
  have h := exp_mul_angle_eq_zpow (N := N) ((n : ℕ) : ℤ) k
  rw [Int.cast_natCast] at h
  exact h

/-- The kernel `e^{-i n θ_k}` of the inverse transform, written as a power of `cycleRoot N`. -/
theorem kernel_neg_eq (n k : Fin (N : ℕ)) :
    Complex.exp (-(Complex.I * ((n : ℕ) : ℂ) * (cycleAngle N k : ℂ))) =
      cycleRoot N ^ (-((n : ℕ) : ℤ) * ((k : ℕ) : ℤ)) := by
  have h := exp_mul_angle_eq_zpow (N := N) (-((n : ℕ) : ℤ)) k
  rw [show Complex.I * (((-((n : ℕ) : ℤ)) : ℤ) : ℂ) * (cycleAngle N k : ℂ) =
      -(Complex.I * ((n : ℕ) : ℂ) * (cycleAngle N k : ℂ)) by push_cast; ring] at h
  exact h

/-- The product of the forward kernel at `i` and the inverse kernel at `j` is the character of
the difference `i - j`. -/
theorem kernel_mul_kernel_neg (i j k : Fin (N : ℕ)) :
    Complex.exp (Complex.I * ((i : ℕ) : ℂ) * (cycleAngle N k : ℂ)) *
        Complex.exp (-(Complex.I * ((j : ℕ) : ℂ) * (cycleAngle N k : ℂ))) =
      cycleRoot N ^ ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * ((k : ℕ) : ℤ)) := by
  rw [kernel_eq, kernel_neg_eq, ← zpow_add₀ (cycleRoot_ne_zero N)]
  congr 1
  ring

/-- Characters depend only on the residue of their exponent: `ζ^{x} = ζ^{y}` when `N ∣ x - y`. -/
theorem zpow_eq_of_dvd {x y : ℤ} (h : ((N : ℕ) : ℤ) ∣ x - y) :
    cycleRoot N ^ x = cycleRoot N ^ y := by
  obtain ⟨q, hq⟩ := h
  have hpow : cycleRoot N ^ ((N : ℕ) : ℤ) = 1 := by
    rw [zpow_natCast]
    exact (isPrimitiveRoot_cycleRoot N).pow_eq_one
  have hx : x = y + ((N : ℕ) : ℤ) * q := by linarith
  rw [hx, zpow_add₀ (cycleRoot_ne_zero N), zpow_mul, hpow, one_zpow, mul_one]

/-- Replacing an integer exponent `x` by its label `Riesz1.labelOf N x` does not change the
character `ζ^{x m}`. -/
theorem zpow_labelOf (x m : ℤ) :
    cycleRoot N ^ (((Riesz1.labelOf N x : ℕ) : ℤ) * m) = cycleRoot N ^ (x * m) := by
  apply zpow_eq_of_dvd
  have hx := Riesz1.APG.val_labelOf_add (N := N) x
  exact ⟨-(m * (x / ((N : ℕ) : ℤ))), by linear_combination (-m) * hx⟩

/-- Orthogonality of the characters: `∑_{k=0}^{N-1} ζ^{m k} = N` when `N ∣ m`, and `0`
otherwise. -/
theorem sum_cycleRoot_zpow (m : ℤ) :
    ∑ k : Fin (N : ℕ), cycleRoot N ^ (m * ((k : ℕ) : ℤ)) =
      if ((N : ℕ) : ℤ) ∣ m then ((N : ℕ) : ℂ) else 0 := by
  have hprim := isPrimitiveRoot_cycleRoot N
  have hpow : ∀ k : ℕ, cycleRoot N ^ (m * (k : ℤ)) = (cycleRoot N ^ m) ^ k := by
    intro k
    rw [zpow_mul, zpow_natCast]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => cycleRoot N ^ (m * (k : ℤ))) (N : ℕ)]
  simp_rw [hpow]
  split_ifs with h
  · have h1 : cycleRoot N ^ m = 1 := (hprim.zpow_eq_one_iff_dvd m).2 h
    simp [h1]
  · have hne : cycleRoot N ^ m ≠ 1 := fun h1 => h ((hprim.zpow_eq_one_iff_dvd m).1 h1)
    have hn : (cycleRoot N ^ m) ^ (N : ℕ) = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hprim.pow_eq_one,
        one_zpow]
    rw [geom_sum_eq hne, hn, sub_self, zero_div]

/-- Two residues of `Fin N` whose difference is divisible by `N` are equal. -/
theorem eq_of_dvd_sub (i i' : Fin (N : ℕ)) (h : ((N : ℕ) : ℤ) ∣ ((i : ℕ) : ℤ) - ((i' : ℕ) : ℤ)) :
    i = i' := by
  have h0 := Int.eq_zero_of_abs_lt_dvd h (by
    rw [abs_lt]
    constructor <;> have := i.isLt <;> have := i'.isLt <;> omega)
  exact Fin.ext (by omega)

/-- The difference of two residues is divisible by `N` exactly when they coincide. -/
theorem dvd_sub_iff_eq (i j : Fin (N : ℕ)) :
    ((N : ℕ) : ℤ) ∣ ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) ↔ i = j :=
  ⟨fun h => eq_of_dvd_sub i j h, fun h => by rw [h, sub_self]; exact dvd_zero _⟩

/-- For fixed `j`, the map `i ↦ labelOf (i - j)` is a bijection of the cycle. -/
theorem bijective_labelOf_sub (j : Fin (N : ℕ)) :
    Function.Bijective (fun i : Fin (N : ℕ) =>
      Riesz1.labelOf N (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) := by
  apply Finite.injective_iff_bijective.mp
  intro i i' h
  have hd := Riesz1.dvd_of_labelOf_eq N h
  have hrw : ((i' : ℕ) : ℤ) - ((i : ℕ) : ℤ) =
      (((i' : ℕ) : ℤ) - ((j : ℕ) : ℤ)) - (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) := by ring
  have hdiv : ((N : ℕ) : ℤ) ∣ ((i' : ℕ) : ℤ) - ((i : ℕ) : ℤ) := by rw [hrw]; exact hd
  exact (eq_of_dvd_sub i' i hdiv).symm

/-- The map `i ↦ labelOf (-i)` is a bijection of the cycle. -/
theorem bijective_labelOf_neg :
    Function.Bijective (fun i : Fin (N : ℕ) => Riesz1.labelOf N (-((i : ℕ) : ℤ))) := by
  apply Finite.injective_iff_bijective.mp
  intro i i' h
  have hd := Riesz1.dvd_of_labelOf_eq N h
  have hrw : ((i : ℕ) : ℤ) - ((i' : ℕ) : ℤ) = (-((i' : ℕ) : ℤ)) - (-((i : ℕ) : ℤ)) := by ring
  have hdiv : ((N : ℕ) : ℤ) ∣ ((i : ℕ) : ℤ) - ((i' : ℕ) : ℤ) := by rw [hrw]; exact hd
  exact eq_of_dvd_sub i i' hdiv

/-! ### Inversion -/

/-- The inverse transform of the forward transform is the identity (Subsection 2.3). -/
theorem cycleFourierInv_cycleFourier (f : Fin (N : ℕ) → ℂ) (n : Fin (N : ℕ)) :
    cycleFourierInv N (cycleFourier N f) n = f n := by
  have hN : ((N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast N.ne_zero
  have hsum : ∀ m : Fin (N : ℕ),
      ∑ k : Fin (N : ℕ), f m * Complex.exp (Complex.I * ((m : ℕ) : ℂ) * (cycleAngle N k : ℂ)) *
          Complex.exp (-(Complex.I * ((n : ℕ) : ℂ) * (cycleAngle N k : ℂ))) =
        f m * (if m = n then ((N : ℕ) : ℂ) else 0) := by
    intro m
    have hite : (if m = n then ((N : ℕ) : ℂ) else 0) =
        ∑ k : Fin (N : ℕ), cycleRoot N ^ ((((m : ℕ) : ℤ) - ((n : ℕ) : ℤ)) * ((k : ℕ) : ℤ)) := by
      rw [sum_cycleRoot_zpow]
      simp only [dvd_sub_iff_eq]
    rw [hite, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_assoc, kernel_mul_kernel_neg]
  unfold cycleFourierInv cycleFourier
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [hsum, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  field_simp


/-- The forward transform of the inverse transform is the identity (Subsection 2.3). -/
theorem cycleFourier_cycleFourierInv (Φ : Fin (N : ℕ) → ℂ) (k : Fin (N : ℕ)) :
    cycleFourier N (cycleFourierInv N Φ) k = Φ k := by
  have hN : ((N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast N.ne_zero
  have hsum : ∀ k' : Fin (N : ℕ), ∑ n : Fin (N : ℕ),
      ((N : ℕ) : ℂ)⁻¹ * (Φ k' * Complex.exp (-(Complex.I * ((n : ℕ) : ℂ) * (cycleAngle N k' : ℂ))))
        * Complex.exp (Complex.I * ((n : ℕ) : ℂ) * (cycleAngle N k : ℂ)) =
      ((N : ℕ) : ℂ)⁻¹ * (Φ k' * if k = k' then ((N : ℕ) : ℂ) else 0) := by
    intro k'
    have hite : (if k = k' then ((N : ℕ) : ℂ) else 0) =
        ∑ n : Fin (N : ℕ), cycleRoot N ^ ((((k : ℕ) : ℤ) - ((k' : ℕ) : ℤ)) * ((n : ℕ) : ℤ)) := by
      rw [sum_cycleRoot_zpow]
      simp only [dvd_sub_iff_eq]
    rw [hite, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    have key : Complex.exp (-(Complex.I * ((n : ℕ) : ℂ) * (cycleAngle N k' : ℂ))) *
        Complex.exp (Complex.I * ((n : ℕ) : ℂ) * (cycleAngle N k : ℂ)) =
        cycleRoot N ^ ((((k : ℕ) : ℤ) - ((k' : ℕ) : ℤ)) * ((n : ℕ) : ℤ)) := by
      rw [kernel_neg_eq, kernel_eq, ← zpow_add₀ (cycleRoot_ne_zero N)]
      congr 1
      ring
    calc ((N : ℕ) : ℂ)⁻¹ * (Φ k' * Complex.exp (-(Complex.I * ((n : ℕ) : ℂ) * (cycleAngle N k' : ℂ))))
          * Complex.exp (Complex.I * ((n : ℕ) : ℂ) * (cycleAngle N k : ℂ))
        = ((N : ℕ) : ℂ)⁻¹ * (Φ k' * (Complex.exp (-(Complex.I * ((n : ℕ) : ℂ) * (cycleAngle N k' : ℂ)))
          * Complex.exp (Complex.I * ((n : ℕ) : ℂ) * (cycleAngle N k : ℂ)))) := by ring
      _ = _ := by rw [key]
  unfold cycleFourier cycleFourierInv
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [hsum, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  field_simp

/-! ### Parseval and the convolution theorem -/

/-- The conjugate of the forward transform is the sum of the conjugate values against the
inverse kernel. -/
theorem conj_cycleFourier (u : Fin (N : ℕ) → ℂ) (k : Fin (N : ℕ)) :
    conj (cycleFourier N u k) = ∑ j : Fin (N : ℕ),
      conj (u j) * Complex.exp (-(Complex.I * ((j : ℕ) : ℂ) * (cycleAngle N k : ℂ))) := by
  unfold cycleFourier
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, ← Complex.exp_conj]
  congr 2
  simp [map_mul, Complex.conj_I, Complex.conj_ofReal]

/-- Parseval's identity in complex form: the frequency sum of `|𝓕_d u|²` is `N` times the
sum of `|u|²`. -/
theorem sum_mul_conj_cycleFourier (u : Fin (N : ℕ) → ℂ) :
    ∑ k : Fin (N : ℕ), cycleFourier N u k * conj (cycleFourier N u k) =
      ((N : ℕ) : ℂ) * ∑ i : Fin (N : ℕ), u i * conj (u i) := by
  have hprod : ∀ k : Fin (N : ℕ), cycleFourier N u k * conj (cycleFourier N u k) =
      ∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ),
        u i * conj (u j) * cycleRoot N ^ ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * ((k : ℕ) : ℤ)) := by
    intro k
    rw [conj_cycleFourier]
    unfold cycleFourier
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [← kernel_mul_kernel_neg]
    ring
  calc ∑ k : Fin (N : ℕ), cycleFourier N u k * conj (cycleFourier N u k)
      = ∑ k : Fin (N : ℕ), ∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ),
          u i * conj (u j) * cycleRoot N ^ ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * ((k : ℕ) : ℤ)) :=
        Finset.sum_congr rfl (fun k _ => hprod k)
    _ = ∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ), u i * conj (u j) *
          ∑ k : Fin (N : ℕ), cycleRoot N ^ ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * ((k : ℕ) : ℤ)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
    _ = ∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ), u i * conj (u j) *
          (if i = j then ((N : ℕ) : ℂ) else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [sum_cycleRoot_zpow]
        simp only [dvd_sub_iff_eq]
    _ = ((N : ℕ) : ℂ) * ∑ i : Fin (N : ℕ), u i * conj (u i) := by
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring

/-- Parseval's identity for the finite Fourier transform (Subsection 2.3):
`∑_i |u(i)|² = N^{-1} ∑_k |𝓕_d u(θ_k)|²`. -/
theorem sum_norm_sq_cycleFourier (u : Fin (N : ℕ) → ℂ) :
    ∑ i : Fin (N : ℕ), ‖u i‖ ^ 2 =
      ((N : ℕ) : ℝ)⁻¹ * ∑ k : Fin (N : ℕ), ‖cycleFourier N u k‖ ^ 2 := by
  have hz : ∀ z : ℂ, ((‖z‖ : ℝ) : ℂ) ^ 2 = z * conj z := by
    intro z
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    norm_cast
  have hN : ((N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast N.ne_zero
  apply Complex.ofReal_injective
  push_cast
  simp only [hz]
  rw [sum_mul_conj_cycleFourier, ← mul_assoc, inv_mul_cancel₀ hN, one_mul]

/-- The convolution theorem (Subsection 2.3): `𝓕_d(f * u) = 𝓕_d f · 𝓕_d u`. -/
theorem cycleFourier_convolution (f u : Fin (N : ℕ) → ℂ) (k : Fin (N : ℕ)) :
    cycleFourier N (cycleConvolution N f u) k = cycleFourier N f k * cycleFourier N u k := by
  have hne := cycleRoot_ne_zero N
  have hcore : ∀ i j : Fin (N : ℕ),
      f (Riesz1.labelOf N (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) * u j *
          cycleRoot N ^ (((i : ℕ) : ℤ) * ((k : ℕ) : ℤ)) =
        (u j * cycleRoot N ^ (((j : ℕ) : ℤ) * ((k : ℕ) : ℤ))) *
          (f (Riesz1.labelOf N (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) *
            cycleRoot N ^ (((Riesz1.labelOf N (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) : ℕ) : ℤ) *
              ((k : ℕ) : ℤ))) := by
    intro i j
    rw [zpow_labelOf]
    have hsplit : cycleRoot N ^ (((i : ℕ) : ℤ) * ((k : ℕ) : ℤ)) =
        cycleRoot N ^ (((j : ℕ) : ℤ) * ((k : ℕ) : ℤ)) *
          cycleRoot N ^ ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * ((k : ℕ) : ℤ)) := by
      rw [← zpow_add₀ hne]
      congr 1
      ring
    rw [hsplit]
    ring
  unfold cycleFourier cycleConvolution
  simp only [kernel_eq]
  calc ∑ i : Fin (N : ℕ), (∑ j : Fin (N : ℕ),
          f (Riesz1.labelOf N (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) * u j) *
            cycleRoot N ^ (((i : ℕ) : ℤ) * ((k : ℕ) : ℤ))
      = ∑ i : Fin (N : ℕ), ∑ j : Fin (N : ℕ),
          f (Riesz1.labelOf N (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) * u j *
            cycleRoot N ^ (((i : ℕ) : ℤ) * ((k : ℕ) : ℤ)) := by
        simp only [Finset.sum_mul]
    _ = ∑ j : Fin (N : ℕ), ∑ i : Fin (N : ℕ),
          f (Riesz1.labelOf N (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) * u j *
            cycleRoot N ^ (((i : ℕ) : ℤ) * ((k : ℕ) : ℤ)) := Finset.sum_comm
    _ = ∑ j : Fin (N : ℕ), ∑ i : Fin (N : ℕ), (u j * cycleRoot N ^ (((j : ℕ) : ℤ) * ((k : ℕ) : ℤ))) *
          (f (Riesz1.labelOf N (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) *
            cycleRoot N ^ (((Riesz1.labelOf N (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) : ℕ) : ℤ) *
              ((k : ℕ) : ℤ))) :=
        Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun i _ => hcore i j))
    _ = ∑ j : Fin (N : ℕ), (u j * cycleRoot N ^ (((j : ℕ) : ℤ) * ((k : ℕ) : ℤ))) *
          ∑ n : Fin (N : ℕ), f n * cycleRoot N ^ (((n : ℕ) : ℤ) * ((k : ℕ) : ℤ)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← Finset.mul_sum]
        congr 1
        exact Fintype.sum_bijective _ (bijective_labelOf_sub j) _ _ (fun _ => rfl)
    _ = (∑ n : Fin (N : ℕ), f n * cycleRoot N ^ (((n : ℕ) : ℤ) * ((k : ℕ) : ℤ))) *
          ∑ j : Fin (N : ℕ), u j * cycleRoot N ^ (((j : ℕ) : ℤ) * ((k : ℕ) : ℤ)) := by
        rw [← Finset.sum_mul]
        exact mul_comm _ _

/-! ### The constant mode and the delta function -/

/-- The constant mode (Subsection 2.3): the transform of a constant `c` is `N c` at the
zero frequency and vanishes at every other frequency. -/
theorem cycleFourier_const (c : ℂ) (k : Fin (N : ℕ)) :
    cycleFourier N (fun _ => c) k = if k = 0 then ((N : ℕ) : ℂ) * c else 0 := by
  have hk : ((N : ℕ) : ℤ) ∣ ((k : ℕ) : ℤ) ↔ k = 0 := by
    simpa using dvd_sub_iff_eq k 0
  have hswap : ∑ n : Fin (N : ℕ), cycleRoot N ^ (((n : ℕ) : ℤ) * ((k : ℕ) : ℤ)) =
      ∑ n : Fin (N : ℕ), cycleRoot N ^ (((k : ℕ) : ℤ) * ((n : ℕ) : ℤ)) :=
    Finset.sum_congr rfl (fun n _ => by rw [mul_comm])
  unfold cycleFourier
  simp only [kernel_eq]
  rw [← Finset.mul_sum, hswap, sum_cycleRoot_zpow]
  simp only [hk]
  by_cases hk0 : k = 0 <;> simp [hk0, mul_comm]

/-- The transform of the Kronecker delta at `0` is the constant `1` (Subsection 2.3). -/
theorem cycleFourier_delta (k : Fin (N : ℕ)) :
    cycleFourier N (fun n => if n = 0 then 1 else 0) k = 1 := by
  unfold cycleFourier
  simp [ite_mul]

/-! ### The sign bridge to Mathlib's `ZMod.dft` -/

/-- The representative in `Fin N` of a residue class in `ZMod N`. -/
def zmodRep (x : ZMod (N : ℕ)) : Fin (N : ℕ) := ⟨x.val, ZMod.val_lt x⟩

/-- The representative of the residue of `n` is `n`. -/
theorem zmodRep_natCast (n : Fin (N : ℕ)) : zmodRep ((n : ℕ) : ZMod (N : ℕ)) = n := by
  apply Fin.ext
  unfold zmodRep
  exact ZMod.val_natCast_of_lt n.isLt

/-- The residue map `Fin N → ZMod N` is bijective. -/
theorem bijective_natCast_zmod :
    Function.Bijective (fun n : Fin (N : ℕ) => ((n : ℕ) : ZMod (N : ℕ))) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp⟩
  intro a b h
  apply Fin.ext
  have h' := congrArg ZMod.val h
  simp only at h'
  rwa [ZMod.val_natCast_of_lt a.isLt, ZMod.val_natCast_of_lt b.isLt] at h'

/-- The positive-sign transform is Mathlib's `ZMod.dft` at the negated frequency, with the
representatives identified (Subsection 2.3, sign convention). -/
theorem cycleFourier_eq_zmod_dft (f : Fin (N : ℕ) → ℂ) (k : Fin (N : ℕ)) :
    cycleFourier N f k =
      ZMod.dft (fun x : ZMod (N : ℕ) => f (zmodRep x)) (-((k : ℕ) : ZMod (N : ℕ))) := by
  rw [ZMod.dft_apply]
  refine Fintype.sum_bijective _ bijective_natCast_zmod _ _ (fun n => ?_)
  rw [zmodRep_natCast, smul_eq_mul, mul_comm (f n)]
  congr 1
  have hX : -(((n : ℕ) : ZMod (N : ℕ)) * -((k : ℕ) : ZMod (N : ℕ))) =
      (((n : ℕ) * (k : ℕ) : ℕ) : ZMod (N : ℕ)) := by
    push_cast
    ring
  rw [hX, ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
  congr 1
  unfold cycleAngle
  push_cast
  ring

/-! ### The circulant matrix and its unitary diagonalization -/

/-- The circulant matrix `H_{ij} = f(j - i)` of a function `f` on the cycle (Subsection 2.3). -/
noncomputable def cycleMatrix (N : ℕ+) (f : Fin (N : ℕ) → ℂ) :
    Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℂ :=
  Matrix.of fun i j => f (Riesz1.labelOf N (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)))

/-- The unitary matrix of characters `U_{ik} = N^{-1/2} e^{i i θ_k}`. -/
noncomputable def cycleUnitary (N : ℕ+) : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℂ :=
  Matrix.of fun i k => (((Real.sqrt ((N : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) *
    Complex.exp (Complex.I * ((i : ℕ) : ℂ) * (cycleAngle N k : ℂ))

/-- The conjugate of a forward kernel is the inverse kernel. -/
theorem conj_kernel (n k : Fin (N : ℕ)) :
    conj (Complex.exp (Complex.I * ((n : ℕ) : ℂ) * (cycleAngle N k : ℂ))) =
      Complex.exp (-(Complex.I * ((n : ℕ) : ℂ) * (cycleAngle N k : ℂ))) := by
  rw [← Complex.exp_conj]
  congr 1
  simp [map_mul, Complex.conj_I, Complex.conj_ofReal]

/-- The inverse kernel at the label of `j - i` is the character of `i - j`. -/
theorem kernel_neg_label (i j k : Fin (N : ℕ)) :
    Complex.exp (-(Complex.I * ((Riesz1.labelOf N (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : ℕ) : ℂ) *
        (cycleAngle N k : ℂ))) =
      cycleRoot N ^ ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * ((k : ℕ) : ℤ)) := by
  rw [kernel_neg_eq, show -(((Riesz1.labelOf N (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : ℕ) : ℤ)) *
      ((k : ℕ) : ℤ) = ((Riesz1.labelOf N (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) : ℕ) : ℤ) *
      (-((k : ℕ) : ℤ)) by ring, zpow_labelOf]
  congr 1
  ring

/-- The square of the scalar `N^{-1/2}` is `N^{-1}`. -/
theorem cycleUnitary_scalar_sq :
    (((Real.sqrt ((N : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) * (((Real.sqrt ((N : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) =
      ((N : ℕ) : ℂ)⁻¹ := by
  rw [← Complex.ofReal_mul, ← sq, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _),
    Complex.ofReal_inv, Complex.ofReal_natCast]

/-- The unitary matrix satisfies `U^* U = 1` (Subsection 2.3, orthogonality of the
characters). -/
theorem star_cycleUnitary_mul_cycleUnitary : star (cycleUnitary N) * cycleUnitary N = 1 := by
  have hne := cycleRoot_ne_zero N
  have hN : ((N : ℕ) : ℂ) ≠ 0 := by exact_mod_cast N.ne_zero
  ext k k'
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ i : Fin (N : ℕ), star (cycleUnitary N) k i * cycleUnitary N i k' =
      ((N : ℕ) : ℂ)⁻¹ * cycleRoot N ^ ((((k' : ℕ) : ℤ) - ((k : ℕ) : ℤ)) * ((i : ℕ) : ℤ)) := by
    intro i
    simp only [Matrix.star_apply, Complex.star_def, cycleUnitary, Matrix.of_apply, map_mul,
      Complex.conj_ofReal, conj_kernel]
    rw [kernel_neg_eq, kernel_eq]
    have hz : cycleRoot N ^ (-((i : ℕ) : ℤ) * ((k : ℕ) : ℤ)) *
        cycleRoot N ^ (((i : ℕ) : ℤ) * ((k' : ℕ) : ℤ)) =
        cycleRoot N ^ ((((k' : ℕ) : ℤ) - ((k : ℕ) : ℤ)) * ((i : ℕ) : ℤ)) := by
      rw [← zpow_add₀ hne]
      congr 1
      ring
    calc _ = (((Real.sqrt ((N : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) * (((Real.sqrt ((N : ℕ) : ℝ))⁻¹ : ℝ) : ℂ) *
          (cycleRoot N ^ (-((i : ℕ) : ℤ) * ((k : ℕ) : ℤ)) *
            cycleRoot N ^ (((i : ℕ) : ℤ) * ((k' : ℕ) : ℤ))) := by ring
      _ = _ := by rw [cycleUnitary_scalar_sq, hz]
  simp only [hterm]
  rw [← Finset.mul_sum, sum_cycleRoot_zpow]
  by_cases h : k = k'
  · subst h
    simp [hN]
  · have hnd : ¬ ((N : ℕ) : ℤ) ∣ ((k' : ℕ) : ℤ) - ((k : ℕ) : ℤ) :=
      fun hd => h ((dvd_sub_iff_eq k' k).1 hd).symm
    simp [h, hnd]

/-- The unitary matrix satisfies `U U^* = 1`. -/
theorem cycleUnitary_mul_star_cycleUnitary : cycleUnitary N * star (cycleUnitary N) = 1 :=
  mul_eq_one_comm.mp star_cycleUnitary_mul_cycleUnitary

/-- The entries of `U D U^*` are the inverse transform of `d`. -/
theorem unitary_diagonal_apply (d : Fin (N : ℕ) → ℂ) (i j : Fin (N : ℕ)) :
    (cycleUnitary N * Matrix.diagonal d * star (cycleUnitary N)) i j =
      ((N : ℕ) : ℂ)⁻¹ * ∑ k : Fin (N : ℕ), d k *
        cycleRoot N ^ ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) * ((k : ℕ) : ℤ)) := by
  have hUD : cycleUnitary N * Matrix.diagonal d =
      Matrix.of fun i k => cycleUnitary N i k * d k := by
    ext i k
    exact Matrix.mul_diagonal d _ i k
  rw [hUD]
  simp only [Matrix.mul_apply, Matrix.star_apply, Complex.star_def, cycleUnitary, Matrix.of_apply,
    map_mul, Complex.conj_ofReal, conj_kernel]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← kernel_mul_kernel_neg, ← cycleUnitary_scalar_sq]
  ring

/-- Finite diagonalization (Subsection 2.3): the circulant matrix of `f` equals
`U D U^*`, where `D` is the diagonal matrix of the transform `𝓕_d f(θ_k)` and `U` is the unitary
matrix of characters. -/
theorem cycleMatrix_eq_unitary_diagonal (f : Fin (N : ℕ) → ℂ) :
    cycleMatrix N f = cycleUnitary N * Matrix.diagonal (fun k => cycleFourier N f k) *
      star (cycleUnitary N) := by
  ext i j
  have hf := cycleFourierInv_cycleFourier f (Riesz1.labelOf N (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)))
  rw [unitary_diagonal_apply]
  simp only [cycleMatrix, Matrix.of_apply]
  rw [← hf]
  simp only [cycleFourierInv, kernel_neg_label]

/-- The columns of the unitary matrix of characters are eigenvectors of the circulant matrix, with
eigenvalues `𝓕_d f(θ_k)` (Subsection 2.3). -/
theorem cycleMatrix_mulVec_column (f : Fin (N : ℕ) → ℂ) (k : Fin (N : ℕ)) :
    Matrix.mulVec (cycleMatrix N f) (fun i => cycleUnitary N i k) =
      cycleFourier N f k • fun i => cycleUnitary N i k := by
  have hWU := star_cycleUnitary_mul_cycleUnitary (N := N)
  have hcol : (fun i => cycleUnitary N i k) = Matrix.mulVec (cycleUnitary N) (Pi.single k 1) := by
    ext i
    simp
  have hde : Matrix.mulVec (Matrix.diagonal (fun k' => cycleFourier N f k')) (Pi.single k 1) =
      cycleFourier N f k • Pi.single k 1 := by
    ext x
    by_cases hx : x = k
    · subst hx
      simp
    · simp [hx]
  have hA : cycleUnitary N * Matrix.diagonal (fun k' => cycleFourier N f k') *
      star (cycleUnitary N) * cycleUnitary N =
        cycleUnitary N * Matrix.diagonal (fun k' => cycleFourier N f k') := by
    simp only [Matrix.mul_assoc]
    rw [hWU, Matrix.mul_one]
  rw [hcol, cycleMatrix_eq_unitary_diagonal f, Matrix.mulVec_mulVec, hA, ← Matrix.mulVec_mulVec,
    hde, Matrix.mulVec_smul]

/-- A real even function gives a Hermitian circulant matrix (Subsection 2.3). -/
theorem cycleMatrix_isHermitian (f : Fin (N : ℕ) → ℝ)
    (heven : ∀ x : ℤ, f (Riesz1.labelOf N (-x)) = f (Riesz1.labelOf N x)) :
    (cycleMatrix N (fun n => (f n : ℂ))).IsHermitian := by
  ext i j
  have h := heven (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ))
  rw [show -(((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)) = ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) by ring] at h
  simp only [Matrix.conjTranspose_apply, cycleMatrix, Matrix.of_apply, Complex.star_def,
    Complex.conj_ofReal]
  rw [h]

/-- The transform of a real even function is real at every frequency: its conjugate equals
itself (Subsection 2.3). -/
theorem conj_cycleFourier_real (f : Fin (N : ℕ) → ℝ)
    (heven : ∀ x : ℤ, f (Riesz1.labelOf N (-x)) = f (Riesz1.labelOf N x))
    (k : Fin (N : ℕ)) :
    conj (cycleFourier N (fun n => (f n : ℂ)) k) = cycleFourier N (fun n => (f n : ℂ)) k := by
  rw [conj_cycleFourier]
  simp only [Complex.conj_ofReal]
  unfold cycleFourier
  refine Fintype.sum_bijective _ bijective_labelOf_neg _ _ (fun j => ?_)
  dsimp only
  have hf : f (Riesz1.labelOf N (-((j : ℕ) : ℤ))) = f j := by
    rw [heven, Riesz1.labelOf_natCast]
  rw [hf, kernel_neg_eq, kernel_eq, zpow_labelOf]

/-- The eigenvalues `𝓕_d f(θ_k)` of a real even function are real. -/
theorem cycleFourier_im_eq_zero (f : Fin (N : ℕ) → ℝ)
    (heven : ∀ x : ℤ, f (Riesz1.labelOf N (-x)) = f (Riesz1.labelOf N x))
    (k : Fin (N : ℕ)) : (cycleFourier N (fun n => (f n : ℂ)) k).im = 0 :=
  Complex.conj_eq_iff_im.mp (conj_cycleFourier_real f heven k)

/-- A matrix with a right inverse of the form `A B = 1` on the left gives injectivity. -/
theorem injective_mulVec_of_mul_eq_one {A B : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℂ}
    (h : B * A = 1) : Function.Injective A.mulVec := by
  intro x y hxy
  have h2 := congrArg (B.mulVec) hxy
  simpa only [Matrix.mulVec_mulVec, h, Matrix.one_mulVec] using h2

/-- Positive definiteness of a circulant matrix is equivalent to the positivity of every frequency
value `𝓕_d f(θ_k)` (Subsection 2.3). For a real even `f`, the matrix is real symmetric and
its frequency values are real. -/
theorem cycleMatrix_posDef_iff (f : Fin (N : ℕ) → ℂ) :
    (cycleMatrix N f).PosDef ↔ ∀ k : Fin (N : ℕ), 0 < cycleFourier N f k := by
  have hM2 := cycleMatrix_eq_unitary_diagonal (N := N) f
  have hWU := star_cycleUnitary_mul_cycleUnitary (N := N)
  constructor
  · intro hM
    have hD := Matrix.PosDef.conjTranspose_mul_mul_same hM
      (injective_mulVec_of_mul_eq_one hWU)
    rw [← Matrix.star_eq_conjTranspose] at hD
    have hEq : star (cycleUnitary N) * cycleMatrix N f * cycleUnitary N =
        Matrix.diagonal (fun k => cycleFourier N f k) := by
      rw [hM2]
      calc star (cycleUnitary N) * (cycleUnitary N * Matrix.diagonal
            (fun k => cycleFourier N f k) * star (cycleUnitary N)) * cycleUnitary N
          = (star (cycleUnitary N) * cycleUnitary N) * Matrix.diagonal
            (fun k => cycleFourier N f k) * (star (cycleUnitary N) * cycleUnitary N) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hWU, Matrix.one_mul, Matrix.mul_one]
    rw [hEq] at hD
    exact Matrix.posDef_diagonal_iff.mp hD
  · intro hpos
    have hdiag : (Matrix.diagonal (fun k => cycleFourier N f k)).PosDef :=
      Matrix.posDef_diagonal_iff.mpr hpos
    have hD := Matrix.PosDef.conjTranspose_mul_mul_same hdiag
      (injective_mulVec_of_mul_eq_one cycleUnitary_mul_star_cycleUnitary)
    rw [← Matrix.star_eq_conjTranspose, star_star] at hD
    rw [hM2]
    exact hD

/-- The inverse of a circulant matrix with nonvanishing transform is circulant, with symbol the
inverse transform `(𝓕_d f)^{-1}` (Subsection 2.3). -/
theorem cycleMatrix_inv_circulant (f : Fin (N : ℕ) → ℂ) (hne : ∀ k, cycleFourier N f k ≠ 0) :
    ∃ g : Fin (N : ℕ) → ℂ,
      (∀ i j : Fin (N : ℕ),
        (cycleMatrix N f)⁻¹ i j = g (Riesz1.labelOf N (((j : ℕ) : ℤ) - ((i : ℕ) : ℤ)))) ∧
      ∀ k : Fin (N : ℕ), cycleFourier N g k = (cycleFourier N f k)⁻¹ := by
  refine ⟨cycleFourierInv N (fun k => (cycleFourier N f k)⁻¹), ?_,
    fun k => cycleFourier_cycleFourierInv _ k⟩
  have hWU := star_cycleUnitary_mul_cycleUnitary (N := N)
  have hUW := cycleUnitary_mul_star_cycleUnitary (N := N)
  have hdd : Matrix.diagonal (fun k => cycleFourier N f k) *
      Matrix.diagonal (fun k => (cycleFourier N f k)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    exact mul_inv_cancel₀ (hne k)
  have key : ∀ D D' : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℂ,
      cycleUnitary N * D * star (cycleUnitary N) * (cycleUnitary N * D' * star (cycleUnitary N)) =
        cycleUnitary N * (D * D') * star (cycleUnitary N) := by
    intro D D'
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star (cycleUnitary N)) (cycleUnitary N), hWU, Matrix.one_mul]
  have hinv : (cycleMatrix N f)⁻¹ = cycleUnitary N *
      Matrix.diagonal (fun k => (cycleFourier N f k)⁻¹) * star (cycleUnitary N) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [cycleMatrix_eq_unitary_diagonal f, key, hdd, Matrix.mul_one, hUW]
  intro i j
  rw [hinv, unitary_diagonal_apply]
  unfold cycleFourierInv
  simp only [kernel_neg_label]

end Riesz2

end
