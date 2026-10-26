/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.GlobalSpatialTail

/-!
# Regional endpoint applications in the spatial commutator

Lemma 5.13, Step 2: assemble the reference and compact-error
applications of Lemma 5.12, choose the error cutoff first,
and then choose the endpoint radius. The polynomial loss exponent is existential.
-/

@[expose] public section

noncomputable section

open Matrix Finset MeasureTheory
open scoped BigOperators Fin.NatCast Matrix.Norms.L2Operator MatrixOrder ENNReal

namespace Riesz2.GlobalCommutators.Internal

/-- Deterministic commutator estimate at an arbitrary positive cutoff
scale, assembling the reference, compact error and all tail regions of
Lemma 5.13, Step 2, and Lemma 5.12. -/
theorem spatial_commutator_scale_by_regions (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent) :
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    let p := (1 - s.val / 2)⁻¹
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (a : ℝ) (ha : 0 < a) (B K L R : ℝ), 1 ≤ K → 0 ≤ L → 1 ≤ R →
      ∀ E : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ,
      (∀ k j, |E k j| ≤ L * weightRadius N k j ^ (-(1 + s.val / 2))) →
      (∀ k j, |E k j - E (k + 1) j| + |E k j - E k (j + 1)| ≤
        L * weightRadius N k j ^ (-(1 + s.val))) →
      (∀ k j, |(E k j - E (k + 1) j) -
        (E k (j + 1) - E (k + 1) (j + 1))| ≤ L * weightRadius N k j ^ (-(2 + s.val))) →
      (∀ j, ∑ k, |E k j| ≤ L) →
      ∀ (i₀ : Fin (N : ℕ)) (v : Fin (N : ℕ) → ℝ),
      let A := factorizationMatrix s N hN a ha B
      let M := (2 : ℝ) • rieszMatrix s N hN + E
      let w := fun i => weightRadius N i i₀ ^ (3 / 2 - s.val)
      let X := Real.sqrt (∑ j, (w j * v j) ^ 2)
      let Z := Real.sqrt (∑ j, (weightRadius N j i₀ ^ (1 / 2 : ℝ) * v j) ^ 2)
      let P := (∑ j, |(rieszMatrix sh N hN *ᵥ v) j| ^ p) ^ (1 / p)
      Real.sqrt (∑ i, (w i * ((A * M) *ᵥ v) i - ((A * M) *ᵥ (fun j => w j * v j)) i) ^ 2) ≤
        C * (1 + (a + B ^ 2 / a)) ^ 2 * (1 + L) *
          ((2 * K ^ (-s.val / 2) +
              (1 + (1 + 2 * K) ^ (2 - s.val)) * R ^ (s.val - 1)) * X +
            ((16 * K) ^ (3 / 2 - s.val) * K ^ (-s.val / 2) +
              (2 + (1 + 2 * K) ^ (2 - s.val)) * (R ^ 2 + Real.log (2 * (N : ℝ)))) * Z + P) := by
  intro sh p
  obtain ⟨Cr, hCr, href⟩ := spatial_reference_endpoint_by_regions hz s
  obtain ⟨Cc, hCc, hcompact⟩ := spatial_compact_error_endpoint_by_regions hz s
  obtain ⟨Ct, hCt, htail⟩ := spatial_tail_action hz s
  let S := 2 * (1 + 2 / s.val)
  have hS : 0 < S := by dsimp [S]; have := s.property.1; positivity
  let C := 1 + Cr + Cc + Ct + S
  have hC : 1 ≤ C := by dsimp [C]; linarith only [hCr, hCc, hCt, hS]
  have hCrC : Cr ≤ C := by dsimp [C]; linarith only [hCc, hCt, hS]
  have hCcC : Cc ≤ C := by dsimp [C]; linarith only [hCr, hCt, hS]
  have hCtC : Ct ≤ C := by dsimp [C]; linarith only [hCr, hCc, hS]
  have hSC : S ≤ C := by dsimp [C]; linarith only [hCr, hCc, hCt]
  refine ⟨C, hC, ?_⟩
  intro N hN a ha B K L R hK hL hR E hE hΔ hΔ₂ hcol i₀ v A M w X Z P
  let μ := a + B ^ 2 / a
  let H := (2 : ℝ) • rieszMatrix s N hN
  let z := fun i j => 1 - CutoffApproximation.scalarCutoff ((Riesz1.cyclicIndexDistance N i j : ℝ) / K)
  let T : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ := fun i j => z i j * E i j
  let Ec : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ := fun i j =>
    CutoffApproximation.scalarCutoff ((Riesz1.cyclicIndexDistance N i j : ℝ) / K) * E i j
  let f := fun i => w i * ((A * H) *ᵥ v) i - ((A * H) *ᵥ (fun j => w j * v j)) i
  let g := fun i => w i * ((A * Ec) *ᵥ v) i - ((A * Ec) *ᵥ (fun j => w j * v j)) i
  let u := fun i => w i * ((A * T) *ᵥ v) i
  let t := fun i => -((A * T) *ᵥ (fun j => w j * v j)) i
  let k := K ^ (-s.val / 2)
  let b := (16 * K) ^ (3 / 2 - s.val) * k
  let d := (1 + 2 * K) ^ (2 - s.val)
  let logN := Real.log (2 * (N : ℝ))
  have hμ : 0 < μ := factorization_shift_pos ha B
  have hlog : 0 ≤ logN := by
    dsimp [logN]; apply Real.log_nonneg
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hX : 0 ≤ X := Real.sqrt_nonneg _
  have hZ : 0 ≤ Z := Real.sqrt_nonneg _
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hz₁ (i j) : |z i j| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (CutoffApproximation.scalarCutoff_le_one _))]
    linarith [CutoffApproximation.scalarCutoff_nonneg ((Riesz1.cyclicIndexDistance N i j : ℝ) / K)]
  have hz₀ (i j) (hij : (Riesz1.cyclicIndexDistance N i j : ℝ) ≤ K) : z i j = 0 := by
    dsimp [z]
    rw [CutoffApproximation.scalarCutoff_eq_one ((div_le_one (by linarith : 0 < K)).mpr hij)]
    ring
  have hE' (i j) : |E i j| ≤ L * (1 + (Riesz1.cyclicIndexDistance N i j : ℝ)) ^ (-1 - s.val / 2) := by
    simpa only [weightRadius, show -(1 + s.val / 2) = -1 - s.val / 2 by ring] using hE i j
  have hc (j) : ∑ i, |Ec i j| ≤ L := by
    apply (sum_le_sum (fun i _ => ?_)).trans (hcol j)
    dsimp [Ec]
    rw [abs_mul, abs_of_nonneg (CutoffApproximation.scalarCutoff_nonneg _)]
    exact mul_le_of_le_one_left (abs_nonneg _) (CutoffApproximation.scalarCutoff_le_one _)
  have hsupp (i j) (hij : 2 * K < (Riesz1.cyclicIndexDistance N i j : ℝ)) : Ec i j = 0 := by
    dsimp [Ec]
    rw [CutoffApproximation.scalarCutoff_eq_zero ((le_div_iff₀ (by linarith : 0 < K)).mpr (by linarith)), zero_mul]
  let q := R ^ (s.val - 1)
  let e := R ^ 2 + logN
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hf : Real.sqrt (∑ i, f i ^ 2) ≤ Cr * μ ^ 2 * (q * X + e * Z) :=
    href N hN a ha B i₀ R hR v
  have hg : Real.sqrt (∑ i, g i ^ 2) ≤ Cc * μ * d * (1 + L) * (q * X + e * Z) :=
    hcompact N hN a ha B K L (by linarith) hL Ec hsupp hc i₀ R hR v
  have hu : Real.sqrt (∑ i, u i ^ 2) ≤ Ct * (1 + μ) * L * (k * X + (b + logN) * Z + P) :=
    htail N hN a ha B K L hK hL E hE hΔ hΔ₂ i₀ v
  have ht : Real.sqrt (∑ i, t i ^ 2) ≤ S * L * k * X := by
    have hh := spatial_unweighted_tail s N hN a ha B K L hK hL E z hE' hz₁ hz₀
      (fun j => w j * v j)
    simpa only [t, neg_sq] using hh
  have he (i) : w i * ((A * M) *ᵥ v) i - ((A * M) *ᵥ (fun j => w j * v j)) i =
      ((f i + g i) + u i) + t i := by
    have heM : M = (H + Ec) + T := by
      ext k j
      change H k j + E k j = (H k j + Ec k j) + T k j
      dsimp [Ec, T, z]
      ring
    rw [heM, mul_add, mul_add]
    simp only [add_mulVec, Pi.add_apply]
    dsimp [f, g, u, t]
    ring
  simp_rw [he]
  have hsum := (spatial_norm_add (fun i => (f i + g i) + u i) t).trans
    (add_le_add ((spatial_norm_add (fun i => f i + g i) u).trans
      (add_le_add (spatial_norm_add f g) le_rfl)) le_rfl)
  apply hsum.trans ((add_le_add (add_le_add (add_le_add hf hg) hu) ht).trans ?_)
  let Q := C * (1 + μ) ^ 2 * (1 + L)
  have hC0 : 0 ≤ C := by linarith only [hC]
  have hLadd : L ≤ 1 + L := by linarith
  have hCrQ : Cr * μ ^ 2 ≤ Q := by
    dsimp [Q]
    exact (mul_le_mul hCrC (by nlinarith only [hμ]) (sq_nonneg μ) hC0).trans
      (le_mul_of_one_le_right (by positivity) (by linarith only [hL]))
  have hCcQ : Cc * μ * (1 + L) ≤ Q := by
    have h1 : μ ≤ (1 + μ) ^ 2 := by nlinarith only [hμ, sq_nonneg μ]
    calc _ ≤ C * (1 + μ) ^ 2 * (1 + L) := by gcongr
         _ = _ := rfl
  have hCtQ : Ct * (1 + μ) * L ≤ Q := by
    have h1 : 1 + μ ≤ (1 + μ) ^ 2 := by nlinarith only [hμ, sq_nonneg μ]
    calc _ ≤ C * (1 + μ) ^ 2 * (1 + L) := by gcongr
         _ = _ := rfl
  have hSQ : S * L ≤ Q := by
    have h1 : 1 ≤ (1 + μ) ^ 2 := by nlinarith only [hμ, sq_nonneg μ]
    calc _ = S * 1 * L := by ring
         _ ≤ C * (1 + μ) ^ 2 * (1 + L) := by gcongr
         _ = _ := rfl
  have h1 := mul_le_mul_of_nonneg_right hCrQ
    (show 0 ≤ q * X + e * Z by positivity)
  have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCcQ hd)
    (show 0 ≤ q * X + e * Z by positivity)
  have h3 := mul_le_mul_of_nonneg_right hCtQ (show 0 ≤ k * X + (b + logN) * Z + P by positivity)
  have h4 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSQ hk) hX
  have hh : ((Cr * μ ^ 2 * (q * X + e * Z) +
      Cc * μ * d * (1 + L) * (q * X + e * Z)) +
      Ct * (1 + μ) * L * (k * X + (b + logN) * Z + P)) + S * L * k * X ≤
      Q * ((2 * k + (1 + d) * q) * X + (b + logN + (1 + d) * e) * Z + P) := by
    convert add_le_add (add_le_add (add_le_add h1 h2) h3) h4 using 1 <;> ring
  apply hh.trans
  have hrest : b + logN + (1 + d) * e ≤ b + (2 + d) * e := by
    dsimp only [e]
    nlinarith only [sq_nonneg R]
  exact mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hrest hZ)) le_rfl)
    (by dsimp [Q]; positivity)

/-- Lemma 5.13, Step 2, equation (5.47): choose `K` to absorb
the tail Schur term, then `R` to absorb the two regional endpoint terms.
The loss exponent is chosen before every matrix parameter and vector. -/
theorem spatial_commutator_pointwise_by_regions (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent) :
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    let p := (1 - s.val / 2)⁻¹
    ∃ D C : ℝ, 0 < D ∧ 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (a : ℝ) (ha : 0 < a) (B L : ℝ), 0 ≤ L →
      ∀ E : Matrix (Fin (N : ℕ)) (Fin (N : ℕ)) ℝ,
      (∀ k j, |E k j| ≤ L * weightRadius N k j ^ (-(1 + s.val / 2))) →
      (∀ k j, |E k j - E (k + 1) j| + |E k j - E k (j + 1)| ≤
        L * weightRadius N k j ^ (-(1 + s.val))) →
      (∀ k j, |(E k j - E (k + 1) j) -
        (E k (j + 1) - E (k + 1) (j + 1))| ≤ L * weightRadius N k j ^ (-(2 + s.val))) →
      (∀ j, ∑ k, |E k j| ≤ L) →
      ∀ (i₀ : Fin (N : ℕ)) (v : Fin (N : ℕ) → ℝ) (η : ℝ), 0 < η → η < 1 →
      let A := factorizationMatrix s N hN a ha B
      let M := (2 : ℝ) • rieszMatrix s N hN + E
      let w := fun i => weightRadius N i i₀ ^ (3 / 2 - s.val)
      let X := Real.sqrt (∑ j, (w j * v j) ^ 2)
      let Z := Real.sqrt (∑ j, (weightRadius N j i₀ ^ (1 / 2 : ℝ) * v j) ^ 2)
      let P := (∑ j, |(rieszMatrix sh N hN *ᵥ v) j| ^ p) ^ (1 / p)
      Real.sqrt (∑ i, (w i * ((A * M) *ᵥ v) i - ((A * M) *ᵥ (fun j => w j * v j)) i) ^ 2) ≤
        η * X + (C * (1 + (a + B ^ 2 / a)) ^ (2 * (1 + D)) * (1 + L) ^ (1 + D) * η ^ (-D)) *
          (Real.log (2 * (N : ℝ)) * Z + P) := by
  intro sh p
  obtain ⟨C₀, hC₀, hscale⟩ := spatial_commutator_scale_by_regions hz s
  let F := 4 / s.val
  let T := (1 + F) / (1 - s.val)
  let D := F + 2 * T
  let Epow := 1 + D
  let H := 267 / Real.log 2 + 11
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hH : 1 ≤ H := by
    have h : 0 < 267 / Real.log 2 := by positivity
    dsimp [H]; linarith only [h]
  have hH0 : 0 < H := by linarith only [hH]
  have hs : 0 < s.val := s.property.1
  have hs1 : 1 - s.val ≠ 0 := ne_of_gt (by linarith [s.property.2])
  have hF : 0 < F := by dsimp [F]; positivity
  have hT : 0 < T := by dsimp [T]; exact div_pos (by linarith only [hF]) (by linarith [s.property.2])
  have hD : 0 < D := by dsimp [D]; positivity
  have hc : 0 < C₀ := by linarith only [hC₀]
  refine ⟨D, H * 20 ^ D * C₀ ^ Epow, hD, by positivity, ?_⟩
  intro N hN a ha B L hL E hE hΔ hΔ₂ hcol i₀ v η hη hη1 A M w X Z P
  let μ := a + B ^ 2 / a
  let Q := C₀ * (1 + μ) ^ 2 * (1 + L)
  let base := 20 * Q / η
  let K := base ^ (2 / s.val)
  let R := base ^ T
  let logN := Real.log (2 * (N : ℝ))
  have hμ : 0 < μ := factorization_shift_pos ha B
  have hQ : 1 ≤ Q := by
    have hμsq : 1 ≤ (1 + μ) ^ 2 := by nlinarith only [hμ, sq_nonneg μ]
    dsimp [Q]
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
         _ ≤ C₀ * (1 + μ) ^ 2 * (1 + L) := by gcongr; linarith only [hL]
  have hQ0 : 0 < Q := by linarith
  have hbase : 1 ≤ base := (le_div_iff₀ hη).mpr (by linarith)
  have hbase0 : 0 < base := by linarith only [hbase]
  have hR : 1 ≤ R := Real.one_le_rpow hbase hT.le
  have hR2 : 1 ≤ R ^ 2 := by nlinarith only [hR]
  have hK : 1 ≤ K := Real.one_le_rpow hbase (by have := s.property.1; positivity)
  have hK0 : 0 < K := by linarith
  have hK2 : 1 ≤ K ^ 2 := by nlinarith only [hK]
  have hlog : Real.log 2 ≤ logN := by
    dsimp [logN]
    apply Real.log_le_log (by norm_num)
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hlog0 : 0 ≤ logN := hlog2.le.trans hlog
  have hcancel : Q * (2 * K ^ (-s.val / 2)) ≤ η / 2 := by
    have he : K ^ (-s.val / 2) = base⁻¹ := by
      dsimp [K]
      rw [← Real.rpow_mul hbase0.le,
        show (2 / s.val) * (-s.val / 2) = -1 by field_simp [hs.ne'],
        Real.rpow_neg_one]
    rw [he]
    dsimp [base]
    field_simp
    linarith
  have hcancelR : Q * (10 * K ^ 2 * R ^ (s.val - 1)) = η / 2 := by
    have he : K ^ 2 * R ^ (s.val - 1) = base⁻¹ := by
      dsimp [K, R]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hbase0.le,
        ← Real.rpow_mul hbase0.le, ← Real.rpow_add hbase0, Nat.cast_ofNat]
      rw [show (2 / s.val) * (2 : ℝ) + T * (s.val - 1) = -1 by
        dsimp [T, F]; field_simp [hs.ne', hs1]; ring, Real.rpow_neg_one]
    calc _ = 10 * Q * (K ^ 2 * R ^ (s.val - 1)) := by ring
         _ = 10 * Q * base⁻¹ := by rw [he]
         _ = _ := by dsimp [base]; field_simp; ring
  have hk : K ^ (-s.val / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hK (by linarith [s.property.1])
  have hb : (16 * K) ^ (3 / 2 - s.val) * K ^ (-s.val / 2) ≤ 256 * K ^ 2 := by
    calc _ ≤ (16 * K) ^ (3 / 2 - s.val) := mul_le_of_le_one_right (by positivity) hk
         _ ≤ (16 * K) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le
           (by linarith) (by linarith [s.property.1])
         _ = _ := by rw [Real.rpow_two]; ring
  have hd : (1 + 2 * K) ^ (2 - s.val) ≤ 9 * K ^ 2 := by
    calc _ ≤ (1 + 2 * K) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le
           (by linarith) (by linarith [s.property.1])
         _ = (1 + 2 * K) ^ 2 := Real.rpow_two _
         _ ≤ (3 * K) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) _
         _ = _ := by ring
  have hbZ : (16 * K) ^ (3 / 2 - s.val) * K ^ (-s.val / 2) +
      (2 + (1 + 2 * K) ^ (2 - s.val)) * (R ^ 2 + logN) ≤ H * K ^ 2 * R ^ 2 * logN := by
    have hsmall : 267 ≤ (267 / Real.log 2) * logN := by
      have h := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 267 / Real.log 2 by positivity)
      have he : (267 / Real.log 2) * Real.log 2 = 267 := by field_simp
      rwa [he] at h
    have hlarge : 2 + (1 + 2 * K) ^ (2 - s.val) ≤ 11 * K ^ 2 := by linarith only [hd, hK2]
    calc _ ≤ 256 * K ^ 2 + (11 * K ^ 2) * (R ^ 2 + logN) :=
            add_le_add hb (mul_le_mul_of_nonneg_right hlarge (by positivity))
         _ ≤ 267 * K ^ 2 * R ^ 2 + 11 * K ^ 2 * R ^ 2 * logN := by
           nlinarith only [mul_nonneg hlog0 (show 0 ≤ K ^ 2 * (R ^ 2 - 1) by positivity),
             show 0 ≤ K ^ 2 * (R ^ 2 - 1) by positivity]
         _ ≤ ((267 / Real.log 2) * logN) * K ^ 2 * R ^ 2 +
                11 * K ^ 2 * R ^ 2 * logN := by gcongr
         _ = _ := by dsimp [H]; ring
  have hcoeff : H * Q * K ^ 2 * R ^ 2 = H * 20 ^ D * Q ^ Epow * η ^ (-D) := by
    have he : K ^ 2 * R ^ 2 = base ^ D := by
      dsimp [K, R, D, F]
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hbase0.le,
        ← Real.rpow_mul hbase0.le, ← Real.rpow_add hbase0]
      congr 1
      ring
    calc _ = H * Q * (K ^ 2 * R ^ 2) := by ring
         _ = H * Q * base ^ D := by rw [he]
         _ = H * 20 ^ D * Q ^ Epow * η ^ (-D) := by
           dsimp [base]
           rw [Real.div_rpow (by positivity : 0 ≤ 20 * Q) hη.le,
             Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 20) hQ0.le,
             Real.rpow_neg hη.le]
           have hqe : Q * Q ^ D = Q ^ Epow := by
             dsimp only [Epow]
             rw [Real.rpow_add hQ0 (1 : ℝ) D, Real.rpow_one]
           calc _ = H * 20 ^ D * (Q * Q ^ D) * (η ^ D)⁻¹ := by ring
                _ = _ := by rw [hqe]
  have hQP : Q ≤ H * Q * K ^ 2 * R ^ 2 := by
    calc Q = 1 * Q * 1 * 1 := by ring
         _ ≤ H * Q * K ^ 2 * R ^ 2 := by gcongr
  have hX : 0 ≤ X := Real.sqrt_nonneg _
  have hZ : 0 ≤ Z := Real.sqrt_nonneg _
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hh := hscale N hN a ha B K L R hK hL hR E hE hΔ hΔ₂ hcol i₀ v
  change _ ≤ Q * ((2 * K ^ (-s.val / 2) +
    (1 + (1 + 2 * K) ^ (2 - s.val)) * R ^ (s.val - 1)) * X +
    ((16 * K) ^ (3 / 2 - s.val) * K ^ (-s.val / 2) +
      (2 + (1 + 2 * K) ^ (2 - s.val)) * (R ^ 2 + logN)) * Z + P) at hh
  have hhigh : Q * (2 * K ^ (-s.val / 2) +
      (1 + (1 + 2 * K) ^ (2 - s.val)) * R ^ (s.val - 1)) ≤ η := by
    have hd' : 1 + (1 + 2 * K) ^ (2 - s.val) ≤ 10 * K ^ 2 := by linarith only [hd, hK2]
    have h := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hd' (Real.rpow_nonneg (by linarith : 0 ≤ R) (s.val - 1))) hQ0.le
    nlinarith only [hcancel, hcancelR, h]
  apply hh.trans
  calc
    _ ≤ η * X + (H * Q * K ^ 2 * R ^ 2) * (logN * Z + P) := by
      have hz := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbZ hQ0.le) hZ
      have hp := mul_le_mul_of_nonneg_right hQP hP
      have hx := mul_le_mul_of_nonneg_right hhigh hX
      nlinarith only [hz, hp, hx]
    _ = _ := by
      rw [hcoeff]
      have hqe : Q ^ (1 + D) = C₀ ^ (1 + D) *
          (1 + μ) ^ (2 * (1 + D)) * (1 + L) ^ (1 + D) := by
        dsimp [Q]
        rw [Real.mul_rpow (by positivity) (by linarith),
          Real.mul_rpow (by linarith) (sq_nonneg _), ← Real.rpow_natCast,
          ← Real.rpow_mul (by linarith : 0 ≤ 1 + μ), Nat.cast_ofNat]
      rw [hqe]
      dsimp [μ, logN]
      ring

end Riesz2.GlobalCommutators.Internal
