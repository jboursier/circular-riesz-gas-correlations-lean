/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.ColumnSubtraction
public import Riesz2.ToMathlib.MomentEventBounds

/-!
# Row and full pairing estimates for column subtraction

The proof of Lemma 5.17 uses boundary entry bounds, bulk increment bounds,
the mean column, and Cauchy–Schwarz. The constants in the paper's `C_n`
notation are explicit here.
-/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace Riesz2.ColumnSubtraction

/-- The three source-sum constants in Lemma 5.17. -/
def sourceConstant (s : Riesz1.RieszExponent) : ℝ :=
  (2 * 8 ^ (2-s.val) * (2 / (1-s.val/2))) +
    (8 ^ (1+s.val/2) * (2/s.val)) + 4 ^ (s.val/2)

/-- Positivity of the explicit constant in Lemma 5.17. -/
theorem sourceConstant_pos (s : Riesz1.RieszExponent) : 0 < sourceConstant s := by
  have := s.property.1
  have := s.property.2
  have hden : 0 < 1-s.val/2 := by linarith [s.property.2]
  unfold sourceConstant
  positivity

/-- The finite scalar boundary/bulk assembly in
Lemma 5.17, with separate entry and mean errors. -/
theorem row_bound_internal {E : Type*} [AddCommGroup E] (s : Riesz1.RieszExponent) (n : ℕ+)
    (i₀ : Fin (n : ℕ)) (b : Fin (n : ℕ) → E → ℝ) (v : Fin (n : ℕ) → E)
    (hsumb : (∑ k, b i₀ (v k)) = b i₀ (∑ k, v k))
    (a : Fin (n : ℕ) → ℝ) (aS P Err ErrS : ℝ) (_hP : 0 ≤ P)
    (hErr : 0 ≤ Err)
    (hentry : ∀ k l,
      |b l (v k)| ≤ P *
        ((min (l.val + 1) ((n : ℕ) - l.val) : ℕ) : ℝ) ^ (-s.val/2) * a k + Err)
    (hincrement : ∀ k,
      |b k (v k) - b i₀ (v k)| ≤ P * (Nat.dist k.val i₀.val : ℝ) *
        (min (((min (k.val + 1) ((n : ℕ) - k.val) : ℕ) : ℝ))
          (((min (i₀.val + 1) ((n : ℕ) - i₀.val) : ℕ) : ℝ))) ^ (-1-s.val/2) * a k + Err)
    (hmean : |b i₀ (∑ k, v k)| ≤ P *
      ((min (i₀.val + 1) ((n : ℕ) - i₀.val) : ℕ) : ℝ) ^ (-s.val/2) * aS + ErrS) :
    let d := fun k : Fin (n : ℕ) => ((min (k.val + 1) ((n : ℕ) - k.val) : ℕ) : ℝ)
    let B := Finset.univ.filter (fun k : Fin (n : ℕ) => d k ≤ (n : ℝ)/8)
    let U := Finset.univ.filter (fun k : Fin (n : ℕ) => (n : ℝ)/8 < d k)
    |∑ k, b k (v k)| ≤
      P * ((∑ k ∈ B, ((d k) ^ (-s.val/2) + (d i₀) ^ (-s.val/2)) * a k) +
        (∑ k ∈ U, (Nat.dist k.val i₀.val : ℝ) *
          (min (d k) (d i₀)) ^ (-1-s.val/2) * a k) + (d i₀) ^ (-s.val/2) * aS) +
        2 * (n : ℝ) * Err + ErrS := by
  intro d B U
  let t := fun k => b k (v k) - b i₀ (v k)
  let q := fun k => if k ∈ B then ((d k) ^ (-s.val/2) + (d i₀) ^ (-s.val/2)) * a k
    else (Nat.dist k.val i₀.val : ℝ) * (min (d k) (d i₀)) ^ (-1-s.val/2) * a k
  have hb (k) : |t k| ≤ P * q k + 2 * Err := by
    by_cases hk : k ∈ B
    · have hh := (abs_sub (b k (v k)) (b i₀ (v k))).trans
        (add_le_add (hentry k k) (hentry k i₀))
      dsimp only [t, q]
      rw [ite_eq_left hk]
      change |b k (v k) - b i₀ (v k)| ≤ _
      dsimp only [d]
      nlinarith only [hh]
    · have hh := hincrement k
      dsimp only [t, q]
      rw [ite_eq_right hk]
      exact hh.trans (by dsimp only [d]; linarith only [hErr])
  have hq : (∑ k, q k) = (∑ k ∈ B, ((d k) ^ (-s.val/2) + (d i₀) ^ (-s.val/2)) * a k) +
      (∑ k ∈ U, (Nat.dist k.val i₀.val : ℝ) * (min (d k) (d i₀)) ^ (-1-s.val/2) * a k) := by
    simp only [q, B, U, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : d k ≤ (n : ℝ)/8 <;> simp [hk]
  have hsub : (∑ k, b k (v k)) = (∑ k, (b k (v k) - b i₀ (v k))) + b i₀ (∑ k, v k) := by
    rw [Finset.sum_sub_distrib, hsumb]
    ring
  rw [hsub]
  calc
    _ ≤ |∑ k, t k| + |b i₀ (∑ k, v k)| := abs_add_le _ _
    _ ≤ (∑ k, |t k|) + |b i₀ (∑ k, v k)| :=
      add_le_add (Finset.abs_sum_le_sum_abs _ _) le_rfl
    _ ≤ (∑ k, (P * q k + 2 * Err)) +
        (P * (d i₀) ^ (-s.val/2) * aS + ErrS) := add_le_add (Finset.sum_le_sum (fun k _ => hb k)) hmean
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin, hq]
      ring

/-- Internal composition of the boundary, bulk and mean estimates in
Lemma 5.17, using only the depth of the centre. -/
theorem source_sums_internal {E : Type*} [AddCommGroup E]
    (s : Riesz1.RieszExponent) (n : ℕ+) (i₀ : Fin (n : ℕ))
    (hdepth : (n : ℝ)/4 ≤ ((min (i₀.val+1) ((n : ℕ)-i₀.val) : ℕ) : ℝ))
    (b : Fin (n : ℕ) → E → ℝ) (v : Fin (n : ℕ) → E)
    (hsumb : (∑ k, b i₀ (v k)) = b i₀ (∑ k, v k))
    (a : Fin (n : ℕ) → ℝ) (aS D P Err ErrS : ℝ)
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hErr : 0 ≤ Err)
    (hvalue : ∀ k, a k ≤ D * (1 + (Nat.dist k.val i₀.val : ℝ)) ^ (-(2-s.val)))
    (hsum : aS ≤ D * (n : ℝ) ^ (-(1-s.val)))
    (hentry : ∀ k l,
      |b l (v k)| ≤ P *
        ((min (l.val+1) ((n : ℕ)-l.val) : ℕ) : ℝ)^(-s.val/2) * a k + Err)
    (hincrement : ∀ k,
      |b k (v k) - b i₀ (v k)| ≤ P * (Nat.dist k.val i₀.val : ℝ) *
        (min (((min (k.val+1) ((n : ℕ)-k.val) : ℕ) : ℝ))
          (((min (i₀.val+1) ((n : ℕ)-i₀.val) : ℕ) : ℝ)))^(-1-s.val/2) * a k + Err)
    (hmean : |b i₀ (∑ k, v k)| ≤ P *
      ((min (i₀.val+1) ((n : ℕ)-i₀.val) : ℕ) : ℝ)^(-s.val/2) * aS + ErrS) :
    |∑ k, b k (v k)| ≤ P * sourceConstant s * D *
      (n : ℝ)^(-1+s.val/2) + 2*(n : ℝ)*Err + ErrS := by
  have hh := row_bound_internal s n i₀ b v hsumb
    a aS P Err ErrS hP hErr hentry hincrement hmean
  have hb := boundary_source_sum_internal s n i₀ hdepth a D 1 hD (by norm_num)
    (by simpa using hvalue)
  have hu := bulk_source_sum_internal s n (n+n) (by simp only [PNat.add_coe]; omega)
    i₀ hdepth a D 1 hD (by norm_num) (by simpa using hvalue)
  have hs := mean_source_column_internal s n i₀ hdepth aS D 1 hD (by norm_num)
    (by simpa using hsum)
  simp only [mul_one] at hb hu hs
  apply hh.trans
  calc
    _ ≤ P * ((2*8^(2-s.val)*(2/(1-s.val/2))) * D * (n : ℝ)^(-1+s.val/2) +
        (8^(1+s.val/2)*(2/s.val)) * D * (n : ℝ)^(-1+s.val/2) +
        4^(s.val/2) * D * (n : ℝ)^(-1+s.val/2)) + 2*(n : ℝ)*Err + ErrS := by
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hb hu) hs) hP) le_rfl) le_rfl
    _ = _ := by unfold sourceConstant; ring

/-- The final Cauchy–Schwarz step of Lemma 5.17. -/
theorem boundary_pair_sum_internal (s : Riesz1.RieszExponent) (n : ℕ+)
    (x : Fin (n : ℕ) → ℝ) (W : ℝ) (hW : 0 ≤ W)
    (hx : (∑ j, (x j)^2) = W^2) :
    (∑ j : Fin (n : ℕ),
      ((min (j.val+1) ((n : ℕ)-j.val) : ℕ) : ℝ)^(-s.val/2) * x j) ≤
      Real.sqrt (2/(1-s.val)) * (n : ℝ)^((1-s.val)/2) * W := by
  let d := fun j : Fin (n : ℕ) =>
    ((min (j.val+1) ((n : ℕ)-j.val) : ℕ) : ℝ)^(-s.val/2)
  have hd : ∑ j, (d j)^2 ≤ 2/(1-s.val)*(n : ℝ)^(1-s.val) := by
    have he (j : Fin (n : ℕ)) : (d j)^2 =
        ((min (j.val+1) ((n : ℕ)-j.val) : ℕ) : ℝ)^(-s.val) := by
      dsimp only [d]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1
      push_cast
      ring
    simp_rw [he]
    exact boundary_weight_sum_internal n s.val s.property.1 s.property.2
  have hh := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ d x
  rw [hx, Real.sqrt_sq hW] at hh
  apply hh.trans
  have hh' := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hd) hW
  apply hh'.trans_eq
  rw [Real.sqrt_mul (by have := s.property.2; positivity)]
  have he : Real.sqrt ((n : ℝ)^(1-s.val)) = (n : ℝ)^((1-s.val)/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ n)]
    congr 1
    ring
  rw [he]

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} [IsProbabilityMeasure ν]

/-- The abstract single-row estimate in
Lemma 5.17, for arbitrary `L∞ → L¹` linear maps.
`A` and `D` separate the operator and source occurrences of `C_n`.
The exceptional factor retains independent norms of the two fields. -/
theorem column_subtraction_row
    (s : Riesz1.RieszExponent) (n : ℕ+) (_hn : 2 ≤ (n : ℕ))
    (A c δ : ℝ) (hA : 0 ≤ A)
    (M : Lp (EuclideanSpace ℝ (Fin (n : ℕ))) ∞ ν →ₗ[ℝ]
      Lp (EuclideanSpace ℝ (Fin (n : ℕ))) 1 ν)
    (hentry : ∀ (φ ψ : Lp ℝ ∞ ν) (i k : Fin (n : ℕ)),
      |pairing (injection ∞ i φ) (M (injection ∞ k ψ))| ≤
        A * ‖toL2 φ‖ * ‖toL2 ψ‖ *
          ((min (i.val+1) ((n : ℕ)-i.val) : ℕ) : ℝ)^(-s.val/2) *
          ((min (k.val+1) ((n : ℕ)-k.val) : ℕ) : ℝ)^(-s.val/2) +
        A * Real.exp (-c*(n : ℝ)^δ) * ‖φ‖ * ‖ψ‖)
    (hincrement : ∀ (φ ψ : Lp ℝ ∞ ν) (i k l : Fin (n : ℕ)),
      |pairing (injection ∞ i φ)
        (M (injection ∞ k ψ - injection ∞ l ψ))| ≤
        A * (Nat.dist k.val l.val : ℝ) * ‖toL2 φ‖ * ‖toL2 ψ‖ *
          ((min (i.val+1) ((n : ℕ)-i.val) : ℕ) : ℝ)^(-s.val/2) *
          (min (((min (k.val+1) ((n : ℕ)-k.val) : ℕ) : ℝ))
            (((min (l.val+1) ((n : ℕ)-l.val) : ℕ) : ℝ)))^(-1-s.val/2) +
        A * Real.exp (-c*(n : ℝ)^δ) * ‖φ‖ * ‖ψ‖)
    (i₀ : Fin (n : ℕ))
    (hdepth : (n : ℝ)/4 ≤ ((min (i₀.val+1) ((n : ℕ)-i₀.val) : ℕ) : ℝ))
    (v : Lp (EuclideanSpace ℝ (Fin (n : ℕ))) ∞ ν) (D : ℝ) (hD : 0 ≤ D)
    (hvalue : ∀ k, ‖toL2 (coordinate ∞ k v)‖ ≤
      D * (1+(Nat.dist k.val i₀.val : ℝ))^(-(2-s.val)))
    (hsum : ‖toL2 (coordinateSum ∞ v)‖ ≤ D * (n : ℝ)^(-(1-s.val)))
    (u : Lp (EuclideanSpace ℝ (Fin (n : ℕ))) ∞ ν) (j : Fin (n : ℕ)) :
    |pairing (injection ∞ j (coordinate ∞ j u)) (M v)| ≤
      A * sourceConstant s * D * (n : ℝ)^(-1+s.val/2) *
        ((min (j.val+1) ((n : ℕ)-j.val) : ℕ) : ℝ)^(-s.val/2) *
        ‖toL2 (coordinate ∞ j u)‖ +
      3*A*(n : ℝ)^(3/2 : ℝ)*Real.exp (-c*(n : ℝ)^δ)*‖u‖*‖v‖ := by
  let φ := coordinate ∞ j u
  let vk := fun k => coordinate ∞ k v
  let b := fun k => (((pairing (injection ∞ j φ)).toLinearMap.comp M).comp
    (injection ∞ k))
  let P := A * ((min (j.val+1) ((n : ℕ)-j.val) : ℕ) : ℝ)^(-s.val/2) * ‖toL2 φ‖
  let Err := A * Real.exp (-c*(n : ℝ)^δ) * ‖u‖ * ‖v‖
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hErr : 0 ≤ Err := by dsimp [Err]; positivity
  have hφ : ‖φ‖ ≤ ‖u‖ := coordinate_norm_le ∞ j u
  have hvk (k) : ‖vk k‖ ≤ ‖v‖ := coordinate_norm_le ∞ k v
  have hS : (∑ k, vk k) = coordinateSum ∞ v := by
    simp [vk, coordinateSum, LinearMap.sum_apply]
  have he : pairing (injection ∞ j φ) (M v) = ∑ k, b k (vk k) := by
    rw [column_subtraction_identity M v i₀, map_add, map_sum]
    simp only [map_sub]
    change (∑ k, (b k (vk k) - b i₀ (vk k))) +
      b i₀ (coordinateSum ∞ v) = ∑ k, b k (vk k)
    rw [← hS, map_sum, Finset.sum_sub_distrib]
    ring
  have hb (k l) : |b l (vk k)| ≤ P *
      ((min (l.val+1) ((n : ℕ)-l.val) : ℕ) : ℝ)^(-s.val/2) * ‖toL2 (vk k)‖ + Err := by
    have hh := hentry φ (vk k) j l
    have herr : A * Real.exp (-c*(n : ℝ)^δ) * ‖φ‖ * ‖vk k‖ ≤ Err := by
      dsimp only [Err]; gcongr; exact hvk k
    apply hh.trans
    dsimp only [P]
    calc
      _ ≤ A * ‖toL2 φ‖ * ‖toL2 (vk k)‖ *
          ((min (j.val+1) ((n : ℕ)-j.val) : ℕ) : ℝ)^(-s.val/2) *
          ((min (l.val+1) ((n : ℕ)-l.val) : ℕ) : ℝ)^(-s.val/2) + Err := add_le_add_right herr _
      _ = _ := by ring
  have hi (k) : |b k (vk k) - b i₀ (vk k)| ≤ P *
      (Nat.dist k.val i₀.val : ℝ) *
      (min (((min (k.val+1) ((n : ℕ)-k.val) : ℕ) : ℝ))
        (((min (i₀.val+1) ((n : ℕ)-i₀.val) : ℕ) : ℝ)))^(-1-s.val/2) *
      ‖toL2 (vk k)‖ + Err := by
    have hh := hincrement φ (vk k) j k i₀
    simp only [map_sub] at hh
    have herr : A * Real.exp (-c*(n : ℝ)^δ) * ‖φ‖ * ‖vk k‖ ≤ Err := by
      dsimp only [Err]; gcongr; exact hvk k
    apply hh.trans
    dsimp only [P]
    nlinarith only [herr]
  have hm : |b i₀ (∑ k, vk k)| ≤ P *
      ((min (i₀.val+1) ((n : ℕ)-i₀.val) : ℕ) : ℝ)^(-s.val/2) *
      ‖toL2 (coordinateSum ∞ v)‖ + Real.sqrt n * Err := by
    rw [hS]
    have hh := hentry φ (coordinateSum ∞ v) j i₀
    have herr : A * Real.exp (-c*(n : ℝ)^δ) * ‖φ‖ * ‖coordinateSum ∞ v‖ ≤
        Real.sqrt n * Err := by
      calc
        _ ≤ A * Real.exp (-c*(n : ℝ)^δ) * ‖u‖ * (Real.sqrt n * ‖v‖) := by
          gcongr; exact coordinateSum_norm_le ∞ v
        _ = _ := by dsimp only [Err]; ring
    apply hh.trans
    dsimp only [P]
    nlinarith only [herr]
  have hh := source_sums_internal s n i₀ hdepth (fun k => b k) vk
    (by rw [map_sum]) (fun k => ‖toL2 (vk k)‖) ‖toL2 (coordinateSum ∞ v)‖
    D P Err (Real.sqrt n * Err) hD hP hErr hvalue hsum hb hi hm
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hsq : Real.sqrt n ≤ (n : ℝ) := (Real.sqrt_le_iff).mpr ⟨by positivity, by nlinarith⟩
  have hpow : (n : ℝ) ≤ (n : ℝ)^(3/2 : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1 : ℝ) ≤ 3/2)
  rw [he]
  apply hh.trans
  dsimp only [P, φ, Err]
  nlinarith only [mul_le_mul_of_nonneg_right (hsq.trans hpow) hErr,
    mul_le_mul_of_nonneg_right hpow hErr]


/-- The two tested operator assumptions of Lemma 5.17.
The pairing is the expectation of the Euclidean dot product, and the
exceptional term uses independent scalar essential suprema. -/
def OperatorBounds (s : Riesz1.RieszExponent) (n : ℕ+) (A c δ : ℝ)
    (M : Lp (EuclideanSpace ℝ (Fin (n : ℕ))) ∞ ν →ₗ[ℝ]
      Lp (EuclideanSpace ℝ (Fin (n : ℕ))) 1 ν) : Prop :=
  (∀ (φ ψ : Lp ℝ ∞ ν) (i k : Fin (n : ℕ)),
      |pairing (injection ∞ i φ) (M (injection ∞ k ψ))| ≤
        A * ‖toL2 φ‖ * ‖toL2 ψ‖ *
          ((min (i.val+1) ((n : ℕ)-i.val) : ℕ) : ℝ)^(-s.val/2) *
          ((min (k.val+1) ((n : ℕ)-k.val) : ℕ) : ℝ)^(-s.val/2) +
        A * Real.exp (-c*(n : ℝ)^δ) * ‖φ‖ * ‖ψ‖) ∧
  (∀ (φ ψ : Lp ℝ ∞ ν) (i k l : Fin (n : ℕ)),
      |pairing (injection ∞ i φ)
        (M (injection ∞ k ψ - injection ∞ l ψ))| ≤
        A * (Nat.dist k.val l.val : ℝ) * ‖toL2 φ‖ * ‖toL2 ψ‖ *
          ((min (i.val+1) ((n : ℕ)-i.val) : ℕ) : ℝ)^(-s.val/2) *
          (min (((min (k.val+1) ((n : ℕ)-k.val) : ℕ) : ℝ))
            (((min (l.val+1) ((n : ℕ)-l.val) : ℕ) : ℝ)))^(-1-s.val/2) +
        A * Real.exp (-c*(n : ℝ)^δ) * ‖φ‖ * ‖ψ‖)

/-- Lemma 5.17 before absorbing the polynomial in the
exceptional term. The leading coefficient expands the paper's
changing `C_n`. -/
theorem column_subtraction_pairing_polynomial
    (s : Riesz1.RieszExponent) (n : ℕ+) (hn : 2 ≤ (n : ℕ))
    (A c δ : ℝ) (hA : 0 ≤ A)
    (M : Lp (EuclideanSpace ℝ (Fin (n : ℕ))) ∞ ν →ₗ[ℝ]
      Lp (EuclideanSpace ℝ (Fin (n : ℕ))) 1 ν)
    (hM : OperatorBounds s n A c δ M)
    (i₀ : Fin (n : ℕ))
    (hdepth : (n : ℝ)/4 ≤ ((min (i₀.val+1) ((n : ℕ)-i₀.val) : ℕ) : ℝ))
    (v : Lp (EuclideanSpace ℝ (Fin (n : ℕ))) ∞ ν) (D : ℝ) (hD : 0 ≤ D)
    (hvalue : ∀ k, ‖toL2 (coordinate ∞ k v)‖ ≤
      D * (1+(Nat.dist k.val i₀.val : ℝ))^(-(2-s.val)))
    (hsum : ‖toL2 (coordinateSum ∞ v)‖ ≤ D * (n : ℝ)^(-(1-s.val)))
    (u : Lp (EuclideanSpace ℝ (Fin (n : ℕ))) ∞ ν) :
    |pairing u (M v)| ≤
      A * sourceConstant s * D * Real.sqrt (2/(1-s.val)) *
        (n : ℝ)^(-(1/2 : ℝ)) * ‖toL2 u‖ +
      3*A*(n : ℝ)^(5/2 : ℝ)*Real.exp (-c*(n : ℝ)^δ)*‖u‖*‖v‖ := by
  have hrow := fun j => column_subtraction_row s n hn A c δ hA M hM.1 hM.2
    i₀ hdepth v D hD hvalue hsum u j
  have he : pairing u (M v) = ∑ j, pairing (injection ∞ j (coordinate ∞ j u)) (M v) := by
    conv_lhs => rw [← sum_injection_coordinate ∞ u]
    exact map_sum (pairing.flip (M v)) _ _
  have hCS := boundary_pair_sum_internal s n
    (fun j => ‖toL2 (coordinate ∞ j u)‖) ‖toL2 u‖ (norm_nonneg _)
    (sum_coordinate_norm_sq u)
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (fun j _ => hrow j)).trans
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hmain : (∑ j : Fin (n : ℕ), A*sourceConstant s*D*(n : ℝ)^(-1+s.val/2)*
      ((min (j.val+1) ((n : ℕ)-j.val) : ℕ) : ℝ)^(-s.val/2)*
      ‖toL2 (coordinate ∞ j u)‖) ≤
      A*sourceConstant s*D*Real.sqrt (2/(1-s.val))*(n : ℝ)^(-(1/2 : ℝ))*‖toL2 u‖ := by
    have hh := mul_le_mul_of_nonneg_left hCS
      (by have := (sourceConstant_pos s).le; positivity :
        0 ≤ A*sourceConstant s*D*(n : ℝ)^(-1+s.val/2))
    rw [Finset.mul_sum] at hh
    simp only [← mul_assoc] at hh
    apply hh.trans_eq
    have hp : (n : ℝ)^(-1+s.val/2)*(n : ℝ)^((1-s.val)/2) =
        (n : ℝ)^(-(1/2 : ℝ)) := by
      rw [← Real.rpow_add (by positivity : (0 : ℝ) < n)]
      congr 1
      ring
    rw [← hp]
    ring
  have herr : (n : ℝ)*(3*A*(n : ℝ)^(3/2 : ℝ)*Real.exp (-c*(n : ℝ)^δ)*‖u‖*‖v‖) =
      3*A*(n : ℝ)^(5/2 : ℝ)*Real.exp (-c*(n : ℝ)^δ)*‖u‖*‖v‖ := by
    have hp : (n : ℝ)*(n : ℝ)^(3/2 : ℝ) = (n : ℝ)^(5/2 : ℝ) := by
      calc
        _ = (n : ℝ)^1*(n : ℝ)^(3/2 : ℝ) := by rw [Real.rpow_one]
        _ = (n : ℝ)^(1+3/2 : ℝ) := (Real.rpow_add (by positivity) _ _).symm
        _ = _ := by norm_num
    calc
      _ = 3*A*((n : ℝ)*(n : ℝ)^(3/2 : ℝ))*Real.exp (-c*(n : ℝ)^δ)*‖u‖*‖v‖ := by ring
      _ = _ := by rw [hp]
  rw [herr]
  exact add_le_add hmain le_rfl

/-- The full Lemma 5.17 of the paper, with its `C_n`
convention made explicit: operator coefficient `A n^a`, source coefficient
`D n^d`, and output coefficient `C n^(a+d)`. The constant is chosen before
`n`, the operator, the centre and both fields. The map is an arbitrary
linear map on actual bounded vector fields, with integrable output. -/
theorem column_subtraction_pairing_uniform
    (s : Riesz1.RieszExponent) (A D a d c δ : ℝ)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hc : 0 < c) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ+), 2 ≤ (n : ℕ) →
      ∀ (M : Lp (EuclideanSpace ℝ (Fin (n : ℕ))) ∞ ν →ₗ[ℝ]
        Lp (EuclideanSpace ℝ (Fin (n : ℕ))) 1 ν),
      OperatorBounds s n (A*(n : ℝ)^a) c δ M →
      ∀ (i₀ : Fin (n : ℕ)),
      (n : ℝ)/4 ≤ ((min (i₀.val+1) ((n : ℕ)-i₀.val) : ℕ) : ℝ) →
      ∀ (v : Lp (EuclideanSpace ℝ (Fin (n : ℕ))) ∞ ν),
      (∀ k, ‖toL2 (coordinate ∞ k v)‖ ≤
        D*(n : ℝ)^d*(1+(Nat.dist k.val i₀.val : ℝ))^(-(2-s.val))) →
      ‖toL2 (coordinateSum ∞ v)‖ ≤ D*(n : ℝ)^d*(n : ℝ)^(-(1-s.val)) →
      ∀ (u : Lp (EuclideanSpace ℝ (Fin (n : ℕ))) ∞ ν),
      |pairing u (M v)| ≤ C*(n : ℝ)^(a+d)*(n : ℝ)^(-(1/2 : ℝ))*‖toL2 u‖ +
        C*Real.exp (-(c/2)*(n : ℝ)^δ)*‖u‖*‖v‖ := by
  obtain ⟨K, hK, habsorb⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := a+5/2) (c := c) (c' := c/2) hδ (by linarith)
  let B := A*sourceConstant s*D*Real.sqrt (2/(1-s.val))
  let C := B + 3*A*K + 1
  have hB : 0 ≤ B := by dsimp only [B]; have := (sourceConstant_pos s).le; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, fun n hn M hM i₀ hdepth v hvalue hsum u => ?_⟩
  have hn0 : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hh := column_subtraction_pairing_polynomial s n hn (A*(n : ℝ)^a) c δ
    (by positivity) M hM i₀ hdepth v (D*(n : ℝ)^d) (by positivity) hvalue hsum u
  have hscale : A*(n : ℝ)^a*sourceConstant s*(D*(n : ℝ)^d)*
      Real.sqrt (2/(1-s.val)) = B*(n : ℝ)^(a+d) := by
    rw [Real.rpow_add hn0]
    dsimp only [B]
    ring
  have herror : 3*(A*(n : ℝ)^a)*(n : ℝ)^(5/2 : ℝ)*Real.exp (-c*(n : ℝ)^δ) ≤
      (3*A*K)*Real.exp (-(c/2)*(n : ℝ)^δ) := by
    calc
      _ = 3*A*((n : ℝ)^(a+5/2)*Real.exp (-c*(n : ℝ)^δ)) := by
        rw [Real.rpow_add hn0]; ring
      _ ≤ 3*A*(K*Real.exp (-(c/2)*(n : ℝ)^δ)) :=
        mul_le_mul_of_nonneg_left (habsorb n hn1) (by positivity)
      _ = _ := by ring
  rw [hscale] at hh
  apply hh.trans
  apply add_le_add
  · gcongr
    dsimp only [C]
    have : 0 ≤ 3*A*K := by positivity
    linarith
  · calc
      _ ≤ (3*A*K)*Real.exp (-(c/2)*(n : ℝ)^δ)*‖u‖*‖v‖ := by gcongr
      _ ≤ C*Real.exp (-(c/2)*(n : ℝ)^δ)*‖u‖*‖v‖ := by
        gcongr
        dsimp only [C]
        linarith


/-- The statement of Lemma 5.17 in the paper's order:
fix the size, probability measure, operator and source field, then choose
one constant valid for every bounded test field. Its `C_n` notation is
expanded as in `column_subtraction_pairing_uniform`. -/
theorem column_subtraction_pairing
    (s : Riesz1.RieszExponent) (n : ℕ+) (hn : 2 ≤ (n : ℕ))
    (A D a d c δ : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D) (hc : 0 < c) (hδ : 0 < δ)
    (M : Lp (EuclideanSpace ℝ (Fin (n : ℕ))) ∞ ν →ₗ[ℝ]
      Lp (EuclideanSpace ℝ (Fin (n : ℕ))) 1 ν)
    (hM : OperatorBounds s n (A*(n : ℝ)^a) c δ M)
    (i₀ : Fin (n : ℕ))
    (hdepth : (n : ℝ)/4 ≤ ((min (i₀.val+1) ((n : ℕ)-i₀.val) : ℕ) : ℝ))
    (v : Lp (EuclideanSpace ℝ (Fin (n : ℕ))) ∞ ν)
    (hvalue : ∀ k, ‖toL2 (coordinate ∞ k v)‖ ≤
      D*(n : ℝ)^d*(1+(Nat.dist k.val i₀.val : ℝ))^(-(2-s.val)))
    (hsum : ‖toL2 (coordinateSum ∞ v)‖ ≤ D*(n : ℝ)^d*(n : ℝ)^(-(1-s.val))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Lp (EuclideanSpace ℝ (Fin (n : ℕ))) ∞ ν),
      |pairing u (M v)| ≤ C*(n : ℝ)^(a+d)*(n : ℝ)^(-(1/2 : ℝ))*‖toL2 u‖ +
        C*Real.exp (-(c/2)*(n : ℝ)^δ)*‖u‖*‖v‖ := by
  obtain ⟨C, hC, hbound⟩ := column_subtraction_pairing_uniform (ν := ν) s A D a d c δ hA hD hc hδ
  exact ⟨C, hC, hbound n hn M hM i₀ hdepth v hvalue hsum⟩

end Riesz2.ColumnSubtraction
