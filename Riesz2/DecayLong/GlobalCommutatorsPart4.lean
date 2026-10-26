/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.GlobalSpatialRegions

/-!
# Polynomial global spatial commutator bounds

Regional estimates for Step 2 of the proof of Lemma 5.13. The file also
gives pointwise bounds with fixed exponents.
-/

@[expose] public section

noncomputable section

open Matrix Finset MeasureTheory
open scoped BigOperators Fin.NatCast Matrix.Norms.L2Operator MatrixOrder ENNReal

namespace Riesz2.GlobalCommutators
namespace Internal

/-- Deterministic commutator estimate at an arbitrary positive cutoff
scale, assembling the reference, compact error and all tail regions of
the proof of Lemma 5.13. -/
theorem spatial_commutator_scale (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent) :
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    let p := (1 - s.val / 2)⁻¹
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
      (a : ℝ) (ha : 0 < a) (B K L : ℝ), 1 ≤ K → 0 ≤ L →
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
          (2 * K ^ (-s.val / 2) * X +
            ((16 * K) ^ (3 / 2 - s.val) * K ^ (-s.val / 2) +
              (2 + (1 + 2 * K) ^ (2 - s.val)) * Real.log (2 * (N : ℝ))) * Z + P) := by
  intro sh p
  obtain ⟨Cr, hCr, href⟩ := spatial_reference_endpoint hz s
  obtain ⟨Cc, hCc, hcompact⟩ := spatial_compact_error_endpoint hz s
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
  intro N hN a ha B K L hK hL E hE hΔ hΔ₂ hcol i₀ v A M w X Z P
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
  have hf : Real.sqrt (∑ i, f i ^ 2) ≤ Cr * μ ^ 2 * logN * Z := href N hN a ha B i₀ v
  have hg : Real.sqrt (∑ i, g i ^ 2) ≤ Cc * μ * d * L * logN * Z :=
    hcompact N hN a ha B K L (by linarith) hL Ec hsupp hc i₀ v
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
  have hCcQ : Cc * μ * L ≤ Q := by
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
  have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCrQ hlog) hZ
  have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCcQ (mul_nonneg hd hlog)) hZ
  have h3 := mul_le_mul_of_nonneg_right hCtQ (show 0 ≤ k * X + (b + logN) * Z + P by positivity)
  have h4 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hSQ hk) hX
  have hh : ((Cr * μ ^ 2 * logN * Z + Cc * μ * d * L * logN * Z) +
      Ct * (1 + μ) * L * (k * X + (b + logN) * Z + P)) + S * L * k * X ≤
      Q * (2 * k * X + (b + (2 + d) * logN) * Z + P) := by
    convert add_le_add (add_le_add (add_le_add h1 h2) h3) h4 using 1 <;> ring
  -- The coefficient two is retained explicitly before the cutoff is chosen.
  exact hh

/-- Polynomial cutoff choice for the deterministic estimate in the proof of Lemma 5.13. No integrability or zero-sum condition
is imposed on the input vector. -/
theorem spatial_commutator_pointwise (hz : External.PeriodicZeta) (s : Riesz1.RieszExponent) :
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    let p := (1 - s.val / 2)⁻¹
    let D := 4 / s.val
    let Epow := 1 + D
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ))
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
        η * X + (C * (1 + (a + B ^ 2 / a)) ^ (2 * Epow) * (1 + L) ^ Epow * η ^ (-D)) *
          (Real.log (2 * (N : ℝ)) * Z + P) := by
  intro sh p D Epow
  obtain ⟨C₀, hC₀, hscale⟩ := spatial_commutator_scale hz s
  let H := 256 / Real.log 2 + 11
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hH : 1 ≤ H := by
    have h : 0 < 256 / Real.log 2 := by positivity
    dsimp [H]; linarith only [h]
  have hH0 : 0 < H := by linarith only [hH]
  have hs : 0 < s.val := s.property.1
  have hD : 0 < D := by dsimp [D]; positivity
  have hc : 0 < C₀ := by linarith only [hC₀]
  refine ⟨H * 2 ^ D * C₀ ^ Epow, by positivity, ?_⟩
  intro N hN a ha B L hL E hE hΔ hΔ₂ hcol i₀ v η hη hη1 A M w X Z P
  let μ := a + B ^ 2 / a
  let Q := C₀ * (1 + μ) ^ 2 * (1 + L)
  let K := (2 * Q / η) ^ (2 / s.val)
  let logN := Real.log (2 * (N : ℝ))
  have hμ : 0 < μ := factorization_shift_pos ha B
  have hQ : 1 ≤ Q := by
    have hμsq : 1 ≤ (1 + μ) ^ 2 := by nlinarith only [hμ, sq_nonneg μ]
    dsimp [Q]
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
         _ ≤ C₀ * (1 + μ) ^ 2 * (1 + L) := by gcongr; linarith only [hL]
  have hQ0 : 0 < Q := by linarith
  have hbase : 1 ≤ 2 * Q / η := (le_div_iff₀ hη).mpr (by linarith)
  have hK : 1 ≤ K := Real.one_le_rpow hbase (by have := s.property.1; positivity)
  have hK0 : 0 < K := by linarith
  have hK2 : 1 ≤ K ^ 2 := by nlinarith only [hK]
  have hlog : Real.log 2 ≤ logN := by
    dsimp [logN]
    apply Real.log_le_log (by norm_num)
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hlog0 : 0 ≤ logN := hlog2.le.trans hlog
  have hcancel : Q * (2 * K ^ (-s.val / 2)) = η := by
    dsimp [K]
    rw [← Real.rpow_mul (show 0 ≤ 2 * Q / η by positivity),
      show (2 / s.val) * (-s.val / 2) = -1 by field_simp [hs.ne']]
    rw [Real.rpow_neg_one]
    field_simp
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
      (2 + (1 + 2 * K) ^ (2 - s.val)) * logN ≤ H * K ^ 2 * logN := by
    have hsmall : 256 ≤ (256 / Real.log 2) * logN := by
      have h := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 256 / Real.log 2 by positivity)
      have he : (256 / Real.log 2) * Real.log 2 = 256 := by field_simp
      rwa [he] at h
    have hlarge : 2 + (1 + 2 * K) ^ (2 - s.val) ≤ 11 * K ^ 2 := by linarith only [hd, hK2]
    calc _ ≤ 256 * K ^ 2 + (11 * K ^ 2) * logN := add_le_add hb
                (mul_le_mul_of_nonneg_right hlarge hlog0)
         _ ≤ ((256 / Real.log 2) * logN) * K ^ 2 + (11 * K ^ 2) * logN := by gcongr
         _ = _ := by dsimp [H]; ring
  have hcoeff : H * Q * K ^ 2 = H * 2 ^ D * Q ^ Epow * η ^ (-D) := by
    have hbase0 : 0 < 2 * Q / η := by positivity
    dsimp [K]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hbase0.le, Nat.cast_ofNat,
      show (2 / s.val) * (2 : ℝ) = D by dsimp [D]; ring,
      Real.div_rpow (by positivity : 0 ≤ 2 * Q) hη.le,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hQ0.le,
      Real.rpow_neg hη.le]
    have hqe : Q * Q ^ D = Q ^ Epow := by
      dsimp only [Epow]
      rw [Real.rpow_add hQ0, Real.rpow_one]
    calc _ = H * 2 ^ D * (Q * Q ^ D) * (η ^ D)⁻¹ := by ring
         _ = _ := by rw [hqe]
  have hQP : Q ≤ H * Q * K ^ 2 := by
    calc Q = 1 * Q * 1 := by ring
         _ ≤ H * Q * K ^ 2 := by gcongr
  have hX : 0 ≤ X := Real.sqrt_nonneg _
  have hZ : 0 ≤ Z := Real.sqrt_nonneg _
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hh := hscale N hN a ha B K L hK hL E hE hΔ hΔ₂ hcol i₀ v
  change _ ≤ Q * (2 * K ^ (-s.val / 2) * X +
    ((16 * K) ^ (3 / 2 - s.val) * K ^ (-s.val / 2) +
      (2 + (1 + 2 * K) ^ (2 - s.val)) * logN) * Z + P) at hh
  apply hh.trans
  calc
    _ ≤ η * X + (H * Q * K ^ 2) * (logN * Z + P) := by
      have hz := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbZ hQ0.le) hZ
      have hp := mul_le_mul_of_nonneg_right hQP hP
      have hc := congrArg (· * X) hcancel
      nlinarith only [hz, hp, hc]
    _ = _ := by
      rw [hcoeff]
      have hqe : Q ^ Epow = C₀ ^ Epow *
          (1 + μ) ^ (2 * Epow) * (1 + L) ^ Epow := by
        dsimp [Q]
        rw [Real.mul_rpow (by positivity) (by linarith),
          Real.mul_rpow (by linarith) (sq_nonneg _), ← Real.rpow_natCast,
          ← Real.rpow_mul (by linarith : 0 ≤ 1 + μ), Nat.cast_ofNat]
      rw [hqe]
      dsimp [μ, logN]
      ring

/-- Identification with the weighted norm of Subsection 5.4.
The identity holds also for infinite norms. -/
theorem spatial_weighted_norm_eq {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (N : ℕ+) (i₀ : Fin (N : ℕ)) (ρ : ℝ) (f : Ω → Fin (N : ℕ) → ℝ)
    (hf : ∀ j, Measurable fun x => f x j) :
    eLpNorm (fun x => Real.sqrt (∑ j, (weightRadius N j i₀ ^ ρ * f x j) ^ 2)) 2 ν =
      weightedRadiusNorm ν N i₀ ρ f := by
  have hg : Measurable (fun x => Real.sqrt (∑ j, (weightRadius N j i₀ ^ ρ * f x j) ^ 2)) :=
    (Finset.measurable_sum _ fun j _ => ((hf j).const_mul _).pow_const 2).sqrt
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hg.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, weightedRadiusNorm, weightedNorm, weightedSqNorm, one_div]
  congr 1
  apply lintegral_congr
  intro x
  rw [Real.enorm_eq_ofReal (Real.sqrt_nonneg _),
    ← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2,
    Real.sq_sqrt (sum_nonneg fun j _ => sq_nonneg _),
    ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)]
  apply sum_congr rfl
  intro j _
  have hr : 0 < weightRadius N j i₀ := by linarith [one_le_weightRadius N j i₀]
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)]
  congr 1
  rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hr.le, Nat.cast_ofNat]
  congr 2
  ring

/-- Passing the pointwise spatial estimate to extended `L²` norms.
This internal lemma permits infinite source norms and uses no real-valued
integral of a potentially nonintegrable function. -/
theorem spatial_integrate {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (f X Z P : Ω → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (η C b : ℝ) (hη : 0 ≤ η) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (h : ∀ᵐ x ∂ν, f x ≤ η * X x + C * (b * Z x + P x)) :
    eLpNorm f 2 ν ≤ ENNReal.ofReal η * eLpNorm X 2 ν +
      ENNReal.ofReal C * (ENNReal.ofReal b * eLpNorm Z 2 ν + eLpNorm P 2 ν) := by
  have hm := eLpNorm_mono_ae_real (p := (2 : ℝ≥0∞)) hf.aestronglyMeasurable
    (h.mono fun x hx => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 x)] using hx)
  change eLpNorm f 2 ν ≤ eLpNorm (η • X + C • (b • Z + P)) 2 ν at hm
  have htwo : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have ht := eLpNorm_add_le (μ := ν) (f := η • X) (g := C • (b • Z + P)) htwo
  rw [eLpNorm_const_smul, eLpNorm_const_smul,
    Real.enorm_eq_ofReal hη, Real.enorm_eq_ofReal hC] at ht
  apply (hm.trans ht).trans
  apply add_le_add le_rfl
  have hh := eLpNorm_add_le (μ := ν) (f := b • Z) (g := P) htwo
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hb] at hh
  gcongr

/-- Polynomial shift bookkeeping for the proof of Lemma 5.13, from the prescribed `a,B` ranges. -/
theorem spatial_shift_bound {a B T : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hB : 1 ≤ B) (hT : 1 ≤ T) (hab : a⁻¹ + B ≤ T) :
    1 + (a + B ^ 2 / a) ≤ 3 * T ^ 3 := by
  have hi : 0 < a⁻¹ := inv_pos.mpr ha
  have hBT : B ≤ T := by linarith only [hab, hi]
  have hiT : a⁻¹ ≤ T := by linarith only [hab, hB]
  have hm : B ^ 2 * a⁻¹ ≤ T ^ 2 * T := mul_le_mul
    (pow_le_pow_left₀ (by linarith only [hB]) hBT 2) hiT hi.le (sq_nonneg _)
  have hT3 : 1 ≤ T ^ 3 := one_le_pow₀ hT
  rw [div_eq_mul_inv]
  nlinarith only [hm, ha1, hT3]

end Internal

/-- The large-radius far-row action in the proof of Lemma 5.13, for the actual doubly localized error.
All component Hölder and output summation steps are discharged. Constants
precede sizes, measure, matrix, shift, cutoff, center and source. -/
theorem spatial_far_error_action (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κₛ γₛ : ℝ) (hκₛ : 0 ≤ κₛ) (hγₛ : 0 ≤ γₛ) (M₀ : ℕ) :
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    let p := (1 - s.val / 2)⁻¹
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ∀ Cₛ : ℝ, 1 ≤ Cₛ →
      ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ))
        (_hn : 2 ≤ (n : ℕ)) (_hnm : (n : ℕ) ≤ (m : ℕ))
        (_hmn : (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val)),
        let K₀ := ⌊(n : ℝ) ^ ε⌋₊ ^ M₀
        1 ≤ K₀ → 4 * K₀ ≤ (m : ℕ) →
        ∀ {α : Type*} [MeasurableSpace α] (ν : MeasureTheory.Measure α)
          (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ),
        PeriodizedMatrixBounds (ν := ν) s n m hm K₀ Cₛ κₛ γₛ ε M →
        ∀ᵐ x ∂ν, ∀ (a : ℝ) (ha : 0 < a) (B R : ℝ), 1 ≤ R →
          ∀ (i₀ : Fin (m : ℕ)) (v : Fin (m : ℕ) → ℝ),
          let r := fun i => weightRadius m i i₀
          let E := M x - (2 : ℝ) • rieszMatrix s m hm
          let F : Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ := fun i j =>
            (1 - CutoffApproximation.scalarCutoff
              (4 * (Riesz1.cyclicIndexDistance m i j : ℝ) / r i)) *
            ∑ l, (factorizationMatrix s m hm a ha B i l *
              CutoffApproximation.scalarCutoff (16 * (Riesz1.cyclicIndexDistance m i l : ℝ) / r i)) *
              ((1 - CutoffApproximation.scalarCutoff
                ((Riesz1.cyclicIndexDistance m l j : ℝ) / R)) * E l j)
          Real.sqrt (∑ i, (if 16 * R ≤ r i then
            r i ^ (3 / 2 - s.val) * (F *ᵥ v) i else 0) ^ 2) ≤
            C * (a + B ^ 2 / a) * (n : ℝ) ^ (κ * ε) *
              (∑ j, |(rieszMatrix sh m hm *ᵥ v) j| ^ p) ^ (1 / p) := by
  intro sh p
  obtain ⟨κ, hκ, hrows⟩ := spatial_far_error_row_norms hz s κₛ γₛ hκₛ hγₛ M₀
  refine ⟨κ, hκ, ?_⟩
  intro ε hε Cₛ hCₛ
  obtain ⟨C, hC, hrows⟩ := hrows ε hε Cₛ hCₛ
  let δ := s.val ^ 2 * (2 - s.val) / 4
  have hδ : 0 < δ := by dsimp [δ]; exact div_pos (mul_pos (sq_pos_of_pos s.property.1)
    (by linarith [s.property.2])) (by norm_num)
  refine ⟨Real.sqrt (2 * (1 + 1 / (2 * δ))) * C, by positivity, ?_⟩
  intro n m hm hn hnm hmn K₀ hK₀ hK₀m α _ ν M hM
  filter_upwards [hrows n m hm hn hnm hmn hK₀ hK₀m ν M hM] with x hx
  intro a ha B R hR i₀ v r E F
  let J := univ.filter (fun i => 16 * R ≤ r i)
  have hL : 0 ≤ C * (a + B ^ 2 / a) * (n : ℝ) ^ (κ * ε) := by
    have := (factorization_shift_pos ha B).le
    positivity
  have h := Internal.spatial_fractional_row_action s m hm i₀ J
    (C * (a + B ^ 2 / a) * (n : ℝ) ^ (κ * ε)) hL F
    (fun i hi => (hx a ha B R hR i₀ i (by
      have := (mem_filter.mp hi).2
      dsimp [r] at this ⊢
      linarith) (mem_filter.mp hi).2).2.2) v
  simpa only [J, mem_filter, mem_univ, true_and,
    mul_assoc] using h

/-- See the proof of Lemma 5.13 in the paper: the complete spatial
commutator bound, with shared polynomial losses and arbitrary measurable
sources. The auxiliary shift bound is quantified as part of the structural
data. The result holds for every measure, hence in particular for every
scalar probability space of Assumptions 5.2, uniformly in temperature.
All norms are extended `L²` norms. -/
theorem global_spatial_commutator (hz : External.PeriodicZeta)
    (s : Riesz1.RieszExponent) (κₛ γₛ : ℝ) (hκₛ : 0 ≤ κₛ) (hγₛ : 0 ≤ γₛ)
    (M₀ : ℕ) (κₐ : ℝ) (hκₐ : 0 ≤ κₐ) :
    let sh : Riesz1.RieszExponent := ⟨s.val / 2, by
      constructor <;> linarith [s.property.1, s.property.2]⟩
    let p := (1 - s.val / 2)⁻¹
    ∃ κ D : ℝ, 0 < κ ∧ 0 < D ∧
      ∀ ε : ℝ, 0 < ε → ∀ Cₛ Cₐ : ℝ, 1 ≤ Cₛ → 1 ≤ Cₐ →
      ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ+) (hm : 2 ≤ (m : ℕ))
        (hn : 2 ≤ (n : ℕ)) (hnm : (n : ℕ) ≤ (m : ℕ))
        (hmn : (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val)),
        let K₀ := ⌊(n : ℝ) ^ ε⌋₊ ^ M₀
        1 ≤ K₀ → 4 * K₀ ≤ (m : ℕ) →
        ∀ {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
          (M : Ω → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ),
        PeriodizedMatrixBounds (ν := ν) s n m hm K₀ Cₛ κₛ γₛ ε M →
        ∀ (a : ℝ) (ha : 0 < a), a ≤ 1 → ∀ B : ℝ, 1 ≤ B →
        a⁻¹ + B ≤ Cₐ * (n : ℝ) ^ (κₐ * ε) →
        (∀ᵐ x ∂ν, a • (1 : Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ) ≤ M x ∧
          ‖M x - (2 : ℝ) • rieszMatrix s m hm‖ ≤ B) →
        ∀ (i₀ : Fin (m : ℕ)) (ψ : Ω → Fin (m : ℕ) → ℝ),
        (∀ j, Measurable fun x => ψ x j) →
        ∀ η : ℝ, 0 < η → η < 1 →
        let A := factorizationMatrix s m hm a ha B
        let w := fun i => weightRadius m i i₀ ^ (3 / 2 - s.val)
        let X := weightedRadiusNorm ν m i₀ (3 / 2 - s.val) ψ
        let Z := weightedRadiusNorm ν m i₀ (1 / 2 : ℝ) ψ
        let P := eLpNorm (fun x =>
          (∑ j, |(rieszMatrix sh m hm *ᵥ ψ x) j| ^ p) ^ (1 / p)) 2 ν
        ∃ Cnη : ℝ, 0 ≤ Cnη ∧ Cnη ≤ C * (n : ℝ) ^ (κ * ε) * η ^ (-D) ∧
          eLpNorm (fun x => Real.sqrt (∑ i,
            (w i * ((A * M x) *ᵥ ψ x) i -
              ((A * M x) *ᵥ (fun j => w j * ψ x j)) i) ^ 2)) 2 ν ≤
            ENNReal.ofReal η * X + ENNReal.ofReal Cnη *
              (ENNReal.ofReal (Real.log (2 * (m : ℝ))) * Z + P) := by
  intro sh p
  obtain ⟨κe, hκe, herr⟩ := global_error_differences s κₛ γₛ hκₛ hγₛ M₀
  obtain ⟨D, Cp, hD, hCp, hpoint⟩ := Internal.spatial_commutator_pointwise_by_regions hz s
  let Epow := 1 + D
  let κ := (6 * κₐ + κe) * Epow
  have hEp : 0 < Epow := by dsimp [Epow]; linarith only [hD]
  have hκ : 0 < κ := by dsimp [κ]; exact mul_pos (by linarith only [hκe, hκₐ]) hEp
  refine ⟨κ, D, hκ, hD, ?_⟩
  intro ε hε Cₛ Cₐ hCₛ hCₐ
  obtain ⟨Ce, hCe, herr⟩ := herr ε hε Cₛ hCₛ
  let C := Cp * 3 ^ (2 * Epow) * 2 ^ Epow * Cₐ ^ (6 * Epow) * Ce ^ Epow
  have hCe0 : 0 < Ce := by linarith only [hCe]
  have hCₐ0 : 0 < Cₐ := by linarith only [hCₐ]
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro n m hm hn hnm hmn K₀ hK₀ hK₀m Ω _ ν M hM a ha ha1 B hB hab _hcoerc i₀ ψ hψ η hη hη1 A w X Z P
  obtain ⟨_, _, _, _, _, _, he⟩ := herr n m hm hn hnm hmn hK₀ hK₀m ν M hM
  let L := Ce * (n : ℝ) ^ (κe * ε)
  let T := Cₐ * (n : ℝ) ^ (κₐ * ε)
  let Cnη := C * (n : ℝ) ^ (κ * ε) * η ^ (-D)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ (n : ℕ) by omega)
  have hL : 1 ≤ L := by
    dsimp [L]
    have hh := Real.one_le_rpow hn1 (mul_nonneg hκe.le hε.le)
    nlinarith only [hCe, hh]
  have hT : 1 ≤ T := by
    dsimp [T]
    have hh := Real.one_le_rpow hn1 (mul_nonneg hκₐ hε.le)
    nlinarith only [hCₐ, hh]
  have hL0 : 0 < L := by linarith only [hL]
  have hT0 : 0 < T := by linarith only [hT]
  have hshift := Internal.spatial_shift_bound ha ha1 hB hT hab
  have hLplus : 1 + L ≤ 2 * L := by linarith only [hL]
  have hcoef : Cp * (1 + (a + B ^ 2 / a)) ^ (2 * Epow) * (1 + L) ^ Epow * η ^ (-D) ≤ Cnη := by
    have hμ : 0 < a + B ^ 2 / a := factorization_shift_pos ha B
    have hpow₁ := Real.rpow_le_rpow (by linarith : 0 ≤ 1 + (a + B ^ 2 / a)) hshift
      (by positivity : 0 ≤ 2 * Epow)
    have hpow₂ := Real.rpow_le_rpow (by linarith : 0 ≤ 1 + L) hLplus hEp.le
    calc
      _ ≤ Cp * (3 * T ^ 3) ^ (2 * Epow) * (2 * L) ^ Epow * η ^ (-D) := by gcongr
      _ = Cnη := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (by positivity : 0 ≤ T ^ 3),
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hL0.le,
          ← Real.rpow_natCast, ← Real.rpow_mul hT0.le, Nat.cast_ofNat,
          show 3 * (2 * Epow) = 6 * Epow by ring]
        dsimp only [T, L]
        rw [Real.mul_rpow hCₐ0.le (Real.rpow_nonneg hn0.le _),
          Real.mul_rpow hCe0.le (Real.rpow_nonneg hn0.le _),
          ← Real.rpow_mul hn0.le, ← Real.rpow_mul hn0.le]
        have hexp : (κₐ * ε) * (6 * Epow) + (κe * ε) * Epow = κ * ε := by dsimp [κ]; ring
        calc _ = C * ((n : ℝ) ^ ((κₐ * ε) * (6 * Epow)) *
              (n : ℝ) ^ ((κe * ε) * Epow)) * η ^ (-D) := by dsimp [C]; ring
             _ = Cnη := by rw [← Real.rpow_add hn0, hexp]
  have hCnη : 0 ≤ Cnη := by dsimp [Cnη]; positivity
  refine ⟨Cnη, hCnη, le_rfl, ?_⟩
  let out := fun x => Real.sqrt (∑ i,
    (w i * ((A * M x) *ᵥ ψ x) i - ((A * M x) *ᵥ (fun j => w j * ψ x j)) i) ^ 2)
  let xf := fun x => Real.sqrt (∑ j, (w j * ψ x j) ^ 2)
  let zf := fun x => Real.sqrt (∑ j, (weightRadius m j i₀ ^ (1 / 2 : ℝ) * ψ x j) ^ 2)
  let pf := fun x => (∑ j, |(rieszMatrix sh m hm *ᵥ ψ x) j| ^ p) ^ (1 / p)
  have hmul (v : Ω → Fin (m : ℕ) → ℝ) (hv : ∀ j, Measurable fun x => v x j) (i) :
      Measurable (fun x => ((A * M x) *ᵥ v x) i) := by
    simp only [mulVec, dotProduct, Matrix.mul_apply]
    exact Finset.measurable_sum _ fun j _ =>
      (Finset.measurable_sum _ fun k _ => (hM.1 k j).const_mul (A i k)).mul (hv j)
  have hout : Measurable out := by
    apply Measurable.sqrt
    apply Finset.measurable_sum
    intro i _
    exact (((hmul ψ hψ i).const_mul (w i)).sub
      (hmul (fun x j => w j * ψ x j) (fun j => (hψ j).const_mul (w j)) i)).pow_const 2
  have hpointwise : ∀ᵐ x ∂ν, out x ≤ η * xf x + Cnη * (Real.log (2 * (m : ℝ)) * zf x + pf x) := by
    filter_upwards [he] with x hx
    let E := M x - (2 : ℝ) • rieszMatrix s m hm
    have hE (k j) : |E k j| ≤ L * weightRadius m k j ^ (-(1 + s.val / 2)) := by
      simpa only [weightRadius, show -(1 + s.val / 2) = -1 - s.val / 2 by ring] using hx.1 k j
    have hΔ (k j) : |E k j - E (k + 1) j| + |E k j - E k (j + 1)| ≤
        L * weightRadius m k j ^ (-(1 + s.val)) := by
      simpa only [weightRadius, show -(1 + s.val) = -1 - s.val by ring] using hx.2.1 k j
    have hΔ₂ (k j) : |(E k j - E (k + 1) j) -
        (E k (j + 1) - E (k + 1) (j + 1))| ≤ L * weightRadius m k j ^ (-(2 + s.val)) := by
      simpa only [weightRadius, show -(2 + s.val) = -2 - s.val by ring] using hx.2.2.1 k j
    have hh := hpoint m hm a ha B L hL0.le E hE hΔ hΔ₂ hx.2.2.2.2.1 i₀ (ψ x) η hη hη1
    have heM : (2 : ℝ) • rieszMatrix s m hm + E = M x := by dsimp [E]; abel
    dsimp only at hh
    rw [heM] at hh
    apply hh.trans
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_right hcoef
    have hlog : 0 ≤ Real.log (2 * (m : ℝ)) := by
      apply Real.log_nonneg
      have : (2 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    positivity
  have hXnorm : eLpNorm xf 2 ν = X := Internal.spatial_weighted_norm_eq ν m i₀ _ ψ hψ
  have hZnorm : eLpNorm zf 2 ν = Z := Internal.spatial_weighted_norm_eq ν m i₀ _ ψ hψ
  have hh := Internal.spatial_integrate ν out xf zf pf hout (fun _ => Real.sqrt_nonneg _)
    η Cnη (Real.log (2 * (m : ℝ))) hη.le hCnη (by
      apply Real.log_nonneg
      have : (2 : ℝ) ≤ m := by exact_mod_cast hm
      linarith) hpointwise
  rwa [hXnorm, hZnorm] at hh

end Riesz2.GlobalCommutators
