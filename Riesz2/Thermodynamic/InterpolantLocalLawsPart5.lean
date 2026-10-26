/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.PhysicalEnergy
public import Riesz2.ToMathlib.FiniteIntervalForce
import all Riesz2.Preliminaries.GapChart

/-!
# Pinned derivatives of the physical interval energy

Exact force identities used by Appendix C. The ambient energy is the short-interval
extension, including its antipodal weight. These identities precede any estimates or
comparison of exterior configurations.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped BigOperators Topology ContDiff

namespace Riesz2.InterpolantLocalLaws

/-- The normalized first derivative of an interval interaction, used in
Appendix C. Its argument is strictly inside the
physical period, just as for `PhysicalEnergy.intervalCoefficient`. -/
def intervalForce (p : Parameters) (N : ℕ+)
    (L : {L : ℝ // 0 < L ∧ L < (N : ℝ)}) : ℝ :=
  (N : ℝ) ^ (-p.val.2 - 1) *
    PhysicalEnergy.kernelDerivative p 1 (PhysicalEnergy.scaledSeparation N L)

/-- See Appendix C in the paper: the first derivative is the
absolutely summable signed image force, with the physical period and sign. -/
theorem intervalForce_images (p : Parameters) (N : ℕ+)
    (L : {L : ℝ // 0 < L ∧ L < (N : ℝ)}) :
    intervalForce p N L = -p.val.2 * ∑' k : ℤ,
      Real.sign (L.val + k * (N : ℝ)) *
        |L.val + k * (N : ℝ)| ^ (-p.val.2 - 1) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  unfold intervalForce
  rw [PhysicalEnergy.kernelDerivative_images]
  norm_num only [PNat.val_ofNat, Finset.prod_range_succ, Finset.prod_range_zero,
    Nat.cast_zero, Nat.cast_one, one_mul, add_zero, pow_one, neg_one_mul]
  change (N : ℝ) ^ (-p.val.2 - 1) *
    (-p.val.2 * ∑' k : ℤ, Real.sign (L.val / N + k) /
      |L.val / N + k| ^ (p.val.2 + 1)) = _
  rw [mul_left_comm, ← tsum_mul_left]
  congr 1
  apply tsum_congr
  intro k
  have he : L.val / (N : ℝ) + k = (L.val + k * N) / N := by field_simp
  have hsgn (x : ℝ) : Real.sign (x / (N : ℝ)) = Real.sign x := by
    rcases lt_trichotomy x 0 with hx | hx | hx
    · rw [Real.sign_of_neg hx, Real.sign_of_neg (div_neg_of_neg_of_pos hx hN)]
    · simp [hx]
    · rw [Real.sign_of_pos hx, Real.sign_of_pos (div_pos hx hN)]
  rw [he, hsgn, abs_div, abs_of_pos hN,
    Real.div_rpow (abs_nonneg _) hN.le]
  rw [div_eq_mul_inv, inv_div, div_eq_mul_inv,
    ← Real.rpow_neg (abs_nonneg _)]
  rw [show -(p.val.2 + 1) = -p.val.2 - 1 by ring]
  have hscale : (N : ℝ) ^ (-p.val.2 - 1) * (N : ℝ) ^ (p.val.2 + 1) = 1 := by
    rw [← Real.rpow_add hN]
    simp
  calc
    _ = ((N : ℝ) ^ (-p.val.2 - 1) * (N : ℝ) ^ (p.val.2 + 1)) *
        (Real.sign (L.val + k * (N : ℝ)) *
          |L.val + k * (N : ℝ)| ^ (-p.val.2 - 1)) := by ring
    _ = _ := by rw [hscale, one_mul]

/-- Absolute summability of the image force in Appendix C. No totalized nonsummable series is used. -/
theorem summable_intervalForce_images (p : Parameters) (N : ℕ+)
    (L : {L : ℝ // 0 < L ∧ L < (N : ℝ)}) :
    Summable (fun k : ℤ => Real.sign (L.val + k * (N : ℝ)) *
      |L.val + k * (N : ℝ)| ^ (-p.val.2 - 1)) := by
  have hp : 1 < p.val.2 + 1 := by linarith [p.property.2.1]
  have hd : 0 < min L.val ((N : ℝ) - L.val) :=
    lt_min L.property.1 (sub_pos.mpr L.property.2)
  have hS := (PeriodicPower.summable_and_le hp hd (min_le_left _ _) (min_le_right _ _)).1
  rw [show -(p.val.2 + 1) = -p.val.2 - 1 by ring] at hS
  apply hS.of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  apply mul_le_of_le_one_left (Real.rpow_nonneg (abs_nonneg _) _)
  rcases Real.sign_apply_eq (L.val + k * (N : ℝ)) with h | h | h <;> rw [h] <;> norm_num

/-- Reflection about the two endpoints reverses the physical force.
This is the sign needed when replacing an interval by its complement in
Appendix C, including the antipodal case. -/
theorem intervalForce_complement (p : Parameters) (N : ℕ+)
    (L : {L : ℝ // 0 < L ∧ L < (N : ℝ)}) :
    intervalForce p N ⟨(N : ℝ) - L.val, sub_pos.mpr L.property.2,
      by linarith [L.property.1]⟩ = -intervalForce p N L := by
  rw [intervalForce_images, intervalForce_images]
  let e : ℤ ≃ ℤ := Equiv.subLeft (-1)
  have he (k : ℤ) : (N : ℝ) - L.val + (e k : ℤ) * (N : ℝ) =
      -(L.val + k * (N : ℝ)) := by
    change (N : ℝ) - L.val + ((-1 - k : ℤ) : ℝ) * (N : ℝ) = _
    push_cast
    ring
  rw [← e.tsum_eq (fun k : ℤ => Real.sign ((N : ℝ) - L.val + k * (N : ℝ)) *
    |(N : ℝ) - L.val + k * (N : ℝ)| ^ (-p.val.2 - 1))]
  simp_rw [he, Real.sign_neg, abs_neg, neg_mul]
  rw [tsum_neg]
  ring

/-- The antipodal first derivative vanishes, including the two-particle
case in Appendix C. -/
theorem intervalForce_antipodal (p : Parameters) (N : ℕ+) :
    intervalForce p N ⟨(N : ℝ) / 2, by positivity,
      by
        have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
        linarith⟩ = 0 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  let L : {L : ℝ // 0 < L ∧ L < (N : ℝ)} := ⟨(N : ℝ) / 2, by linarith, by linarith⟩
  have hc := intervalForce_complement p N L
  have he : (⟨(N : ℝ) - L.val, sub_pos.mpr L.property.2,
      by linarith [L.property.1]⟩ : {L : ℝ // 0 < L ∧ L < (N : ℝ)}) = L := by
    apply Subtype.ext
    dsimp [L]
    ring
  rw [he] at hc
  change intervalForce p N L = 0
  linarith

/-- The zeroth image is precisely the inverse-power singularity common to
both volumes, as used in Appendix C.
The remaining series is summable by `summable_intervalForce_images`. -/
theorem intervalForce_remove_singularity (p : Parameters) (N : ℕ+)
    (L : {L : ℝ // 0 < L ∧ L < (N : ℝ)}) :
    intervalForce p N L + p.val.2 * L.val ^ (-p.val.2 - 1) =
      -p.val.2 * ∑' k : ℤ, if k = 0 then 0 else
        Real.sign (L.val + k * (N : ℝ)) *
          |L.val + k * (N : ℝ)| ^ (-p.val.2 - 1) := by
  rw [intervalForce_images,
    (summable_intervalForce_images p N L).tsum_eq_add_tsum_ite 0]
  simp only [Int.cast_zero, zero_mul, add_zero,
    Real.sign_of_pos L.property.1, abs_of_pos L.property.1, one_mul]
  ring

/-- For intervals shorter than half a period the nonzero images have a
bound independent of the singular separation. This proves the internal
period-correction estimate used in Appendix C before
summing over particles. -/
theorem intervalForce_period_correction (p : Parameters) (N : ℕ+)
    (L : {L : ℝ // 0 < L ∧ L < (N : ℝ)}) (hL : L.val ≤ (N : ℝ) / 2) :
    |intervalForce p N L + p.val.2 * L.val ^ (-p.val.2 - 1)| ≤
      p.val.2 * ((N : ℝ) / 2) ^ (-p.val.2 - 1) *
        ∑' k : ℤ, |(k : ℝ)| ^ (-p.val.2 - 1) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hp : 1 < p.val.2 + 1 := by linarith [p.property.2.1]
  have hS : Summable (fun k : ℤ => |(k : ℝ)| ^ (-p.val.2 - 1)) := by
    simpa only [show -(p.val.2 + 1) = -p.val.2 - 1 by ring] using
      Real.summable_abs_int_rpow hp
  let f : ℤ → ℝ := fun k => if k = 0 then 0 else
    Real.sign (L.val + k * (N : ℝ)) *
      |L.val + k * (N : ℝ)| ^ (-p.val.2 - 1)
  let g : ℤ → ℝ := fun k => ((N : ℝ) / 2) ^ (-p.val.2 - 1) *
    |(k : ℝ)| ^ (-p.val.2 - 1)
  have hg : Summable g := hS.mul_left _
  have hle (k : ℤ) : ‖f k‖ ≤ g k := by
    by_cases hk : k = 0
    · subst k
      simp only [f, ↓reduceIte, norm_zero]
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (abs_nonneg _) _)
    · have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
        exact_mod_cast (show (1 : ℤ) ≤ |k| from Int.one_le_abs hk)
      have hdist : (N : ℝ) / 2 * |(k : ℝ)| ≤ |L.val + k * (N : ℝ)| := by
        have ht : |(k : ℝ)| * (N : ℝ) ≤ |L.val + k * (N : ℝ)| + L.val := by
          calc
            _ = |(L.val + k * (N : ℝ)) + (-L.val)| := by
              rw [show L.val + k * (N : ℝ) + -L.val = k * (N : ℝ) by ring,
                abs_mul, abs_of_pos hN]
            _ ≤ |L.val + k * (N : ℝ)| + |-L.val| := abs_add_le _ _
            _ = _ := by rw [abs_neg, abs_of_pos L.property.1]
        nlinarith
      have hbase : 0 < (N : ℝ) / 2 * |(k : ℝ)| := by positivity
      have hpow := Real.rpow_le_rpow_of_nonpos hbase hdist
        (show -p.val.2 - 1 ≤ 0 by linarith [p.property.2.1])
      rw [Real.mul_rpow (by positivity : 0 ≤ (N : ℝ) / 2) (abs_nonneg _)] at hpow
      simp only [f, hk, ↓reduceIte, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
      apply le_trans _ hpow
      apply mul_le_of_le_one_left (Real.rpow_nonneg (abs_nonneg _) _)
      rcases Real.sign_apply_eq (L.val + k * (N : ℝ)) with h | h | h <;>
        rw [h] <;> norm_num
  have hf : Summable f := hg.of_norm_bounded hle
  rw [intervalForce_remove_singularity]
  change |-p.val.2 * ∑' k, f k| ≤ _
  rw [abs_mul, abs_neg, abs_of_pos p.property.2.1]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ p.property.2.1.le
  calc
    |∑' k, f k| ≤ ∑' k, ‖f k‖ := norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' k, g k := hf.norm.tsum_le_tsum hle hg
    _ = _ := tsum_mul_left

/-- The interval force is independent of temperature. This reuses the
kernel derivative equality rather than a second kernel definition. -/
theorem intervalForce_eq_of_exponent_eq (p q : Parameters)
    (hpq : p.val.2 = q.val.2) (N : ℕ+)
    (L : {L : ℝ // 0 < L ∧ L < (N : ℝ)}) :
    intervalForce p N L = intervalForce q N L := by
  unfold intervalForce
  rw [hpq, PhysicalEnergy.kernelDerivative_eq_of_exponent_eq p q hpq]

/-- Internal helper for Appendix C: the common
inverse-power singularity cancels exactly between the two physical
periods. The bound remains finite as the shared separation tends to zero. -/
theorem internal_intervalForce_difference (p : Parameters) (N M : ℕ+)
    (hNM : (N : ℕ) ≤ (M : ℕ))
    (L : {L : ℝ // 0 < L ∧ L < (N : ℝ)}) (hL : L.val ≤ (N : ℝ) / 2) :
    |intervalForce p N L - intervalForce p M
      ⟨L.val, L.property.1, L.property.2.trans_le (by exact_mod_cast hNM)⟩| ≤
      2 * p.val.2 * ((N : ℝ) / 2) ^ (-p.val.2 - 1) *
        ∑' k : ℤ, |(k : ℝ)| ^ (-p.val.2 - 1) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hM : (N : ℝ) ≤ M := by exact_mod_cast hNM
  let L' : {L : ℝ // 0 < L ∧ L < (M : ℝ)} :=
    ⟨L.val, L.property.1, L.property.2.trans_le hM⟩
  have hleft := intervalForce_period_correction p N L hL
  have hright := intervalForce_period_correction p M L' (by dsimp [L']; linarith)
  have hpow : ((M : ℝ) / 2) ^ (-p.val.2 - 1) ≤
      ((N : ℝ) / 2) ^ (-p.val.2 - 1) := by
    apply Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (N : ℝ) / 2)
      (by linarith)
    linarith [p.property.2.1]
  have hS : 0 ≤ ∑' k : ℤ, |(k : ℝ)| ^ (-p.val.2 - 1) :=
    tsum_nonneg (fun _ => Real.rpow_nonneg (abs_nonneg _) _)
  change |intervalForce p N L - intervalForce p M L'| ≤ _
  calc
    _ = |(intervalForce p N L + p.val.2 * L.val ^ (-p.val.2 - 1)) -
        (intervalForce p M L' + p.val.2 * L.val ^ (-p.val.2 - 1))| := by
      congr 1
      ring
    _ ≤ |intervalForce p N L + p.val.2 * L.val ^ (-p.val.2 - 1)| +
        |intervalForce p M L' + p.val.2 * L.val ^ (-p.val.2 - 1)| := abs_sub _ _
    _ ≤ p.val.2 * ((N : ℝ) / 2) ^ (-p.val.2 - 1) *
          (∑' k : ℤ, |(k : ℝ)| ^ (-p.val.2 - 1)) +
        p.val.2 * ((M : ℝ) / 2) ^ (-p.val.2 - 1) *
          (∑' k : ℤ, |(k : ℝ)| ^ (-p.val.2 - 1)) := add_le_add hleft hright
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow p.property.2.1.le) hS
      nlinarith

/-- The cyclic interval sum uses precisely the additive cyclic
labels needed by the endpoint-cancellation identity. -/
theorem cyclicGapSum_additive (N : ℕ+) (i : Fin (N : ℕ)) (r : ℕ)
    (x : Fin (N : ℕ) → ℝ) :
    cyclicGapSum N i r x = ∑ a ∈ Finset.range r, x (i + a • (1 : Fin (N : ℕ))) := by
  have hn (a : ℕ) : a • (1 : Fin (N : ℕ)) = ⟨a % (N : ℕ), Nat.mod_lt _ N.pos⟩ := by
    induction a with
    | zero => rfl
    | succ a ih =>
      rw [succ_nsmul, ih]
      apply Fin.ext
      change (a % (N : ℕ) + 1 % (N : ℕ)) % (N : ℕ) = (a + 1) % (N : ℕ)
      exact (Nat.add_mod _ _ _).symm
  unfold cyclicGapSum
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  apply Fin.ext
  simp only [hn, Fin.val_add]
  exact (Nat.add_mod_mod _ _ _).symm

/-- See Appendix C in the paper: a full cyclic sum
has exactly the physical total mass. -/
theorem cyclicGapSum_full (N : ℕ+) (i : Fin (N : ℕ))
    (x : Fin (N : ℕ) → ℝ) : cyclicGapSum N i N x = ∑ a, x a := by
  calc
    cyclicGapSum N i N x = ∑ a : Fin (N : ℕ),
        x ⟨(i.val + a.val) % (N : ℕ), Nat.mod_lt _ N.pos⟩ :=
      (Fin.sum_univ_eq_sum_range
        (fun a => x ⟨(i.val + a) % (N : ℕ), Nat.mod_lt _ N.pos⟩) (N : ℕ)).symm
    _ = ∑ a : Fin (N : ℕ), x (i + a) := rfl
    _ = ∑ a, x a := Equiv.sum_comp (Equiv.addLeft i) x

/-- See Appendix C in the paper: splitting a cyclic
interval retains its endpoint, including wrapping and an empty part. -/
theorem cyclicGapSum_split (N : ℕ+) (i : Fin (N : ℕ)) (r t : ℕ)
    (x : Fin (N : ℕ) → ℝ) :
    cyclicGapSum N i (r + t) x = cyclicGapSum N i r x +
      cyclicGapSum N (i + r • (1 : Fin (N : ℕ))) t x := by
  simp_rw [cyclicGapSum_additive]
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  rw [add_nsmul]
  abel

/-- The complementary interval has the remaining mass. This is the
geometric identity used with `intervalForce_complement` in the physical
pinned-force computation of Appendix C. -/
theorem cyclicGapSum_complement (N : ℕ+) (i : Fin (N : ℕ)) {r : ℕ}
    (hr : r ≤ (N : ℕ)) (x : Fin (N : ℕ) → ℝ) :
    cyclicGapSum N (i + r • (1 : Fin (N : ℕ))) ((N : ℕ) - r) x =
      (∑ a, x a) - cyclicGapSum N i r x := by
  have h := cyclicGapSum_split N i r ((N : ℕ) - r) x
  rw [Nat.add_sub_of_le hr, cyclicGapSum_full] at h
  linarith

/-- See Appendix C in the paper: after pairing a pinned
variation with the interval sums, only the two endpoints
remain. The identity includes wrapping, full cycles and the even case. -/
theorem cyclicGapSum_pinned_endpoints (N : ℕ+) (h : Fin (N : ℕ) → ℝ)
    (j : Fin (N : ℕ)) (r : ℕ) :
    (∑ i, h i * cyclicGapSum N i r
      (Pi.single j 1 - Pi.single (j + 1) 1)) =
      h (j + 1 - r • (1 : Fin (N : ℕ))) - h (j + 1) := by
  simp_rw [cyclicGapSum_additive]
  exact FiniteIntervalForce.sum_pinned_intervals h j 1 r

/-- See Appendix C in the paper: a smooth realization of the
energy has this exact pinned particle derivative. The antipodal
weight is retained before estimating any term. -/
theorem physical_pinned_derivatives (p : Parameters) (N : ℕ+) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ∀ (y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N})
        (j : Fin (N : ℕ)),
        let F := fun (r : Fin ((N : ℕ) / 2)) (i : Fin (N : ℕ)) =>
          intervalForce p N
            ⟨cyclicGapSum N i (r.val + 1) (WithLp.ofLp y.val),
              y.property i (r.val + 1) (by omega) (by have := r.isLt; omega)⟩
        fderiv ℝ W y.val
          (WithLp.toLp 2 (Pi.single j 1 - Pi.single (j + 1) 1)) =
          ∑ r : Fin ((N : ℕ) / 2),
            (2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0) *
              (F r (j + 1 - (r.val + 1) • (1 : Fin (N : ℕ))) - F r (j + 1)) := by
  classical
  obtain ⟨W, hW, hv, hd⟩ := PhysicalEnergy.ambient_derivatives p N
  refine ⟨W, hW, hv, ?_⟩
  intro y j
  dsimp only
  rw [(hd y (WithLp.toLp 2 (Pi.single j 1 - Pi.single (j + 1) 1)) 0).1]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  let c : ℝ := 2 - if 2 * (r.val + 1) = (N : ℕ) then (1 : ℝ) else 0
  let F : Fin (N : ℕ) → ℝ := fun i => intervalForce p N
    ⟨cyclicGapSum N i (r.val + 1) (WithLp.ofLp y.val),
      y.property i (r.val + 1) (by omega) (by have := r.isLt; omega)⟩
  change (∑ i, (N : ℝ) ^ (-p.val.2 - 1) *
    ((c * PhysicalEnergy.kernelDerivative p 1
      (PhysicalEnergy.scaledSeparation N
        ⟨cyclicGapSum N i (r.val + 1) (WithLp.ofLp y.val),
          y.property i (r.val + 1) (by omega) (by have := r.isLt; omega)⟩)) *
      cyclicGapSum N i (r.val + 1) (Pi.single j 1 - Pi.single (j + 1) 1))) =
    c * (F (j + 1 - (r.val + 1) • (1 : Fin (N : ℕ))) - F (j + 1))
  have he (i : Fin (N : ℕ)) : (N : ℝ) ^ (-p.val.2 - 1) *
    ((c * PhysicalEnergy.kernelDerivative p 1
      (PhysicalEnergy.scaledSeparation N
        ⟨cyclicGapSum N i (r.val + 1) (WithLp.ofLp y.val),
          y.property i (r.val + 1) (by omega) (by have := r.isLt; omega)⟩)) *
      cyclicGapSum N i (r.val + 1) (Pi.single j 1 - Pi.single (j + 1) 1)) =
    c * (F i * cyclicGapSum N i (r.val + 1) (Pi.single j 1 - Pi.single (j + 1) 1)) := by
    dsimp [F, intervalForce]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, cyclicGapSum_pinned_endpoints]

/-- Complementary positive intervals in a physical mass simplex carry
opposite first derivatives. This applies the kernel reflection identity
to the literal gap sums used by Appendix C. -/
theorem physical_intervalForce_complement (p : Parameters) (N : ℕ+)
    (x : Fin (N : ℕ) → ℝ) (hx : x ∈ Riesz1.gapSimplex N)
    (i : Fin (N : ℕ)) {r : ℕ} (hr : 0 < r) (hrN : r < (N : ℕ)) :
    intervalForce p N
      ⟨cyclicGapSum N (i + r • (1 : Fin (N : ℕ))) ((N : ℕ) - r) x,
        PhysicalEnergy.gapSum_mem N _ (by omega) (by omega) x hx⟩ =
      -intervalForce p N
        ⟨cyclicGapSum N i r x, PhysicalEnergy.gapSum_mem N i hr hrN x hx⟩ := by
  have he := cyclicGapSum_complement N i hrN.le x
  rw [hx.2] at he
  have hc := intervalForce_complement p N
    ⟨cyclicGapSum N i r x, PhysicalEnergy.gapSum_mem N i hr hrN x hx⟩
  convert hc using 1
  congr 1
  exact Subtype.ext he

/-- See Appendix C in the paper: the short-interval derivative
is exactly the sum over every nonzero particle rank. Complementary ranks
supply the second copy, and the even antipodal rank supplies only one.
This is an identity for the energy on the full physical simplex. -/
theorem physical_pinned_derivatives_all_ranks (p : Parameters) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ∀ (x : Fin (N : ℕ) → ℝ) (hx : x ∈ Riesz1.gapSimplex N)
        (j : Fin (N : ℕ)),
        let F := fun (r : Fin ((N : ℕ) - 1)) (i : Fin (N : ℕ)) =>
          intervalForce p N
            ⟨cyclicGapSum N i (r.val + 1) x,
              PhysicalEnergy.gapSum_mem N i (by omega) (by have := r.isLt; omega) x hx⟩
        fderiv ℝ W (WithLp.toLp 2 x)
          (WithLp.toLp 2 (Pi.single j 1 - Pi.single (j + 1) 1)) =
          ∑ r : Fin ((N : ℕ) - 1),
            (F r (j + 1 - (r.val + 1) • (1 : Fin (N : ℕ))) - F r (j + 1)) := by
  classical
  obtain ⟨W, hW, hv, hd⟩ := physical_pinned_derivatives p N
  refine ⟨W, hW, hv, ?_⟩
  intro x hx j
  let F := fun (r : Fin ((N : ℕ) - 1)) (i : Fin (N : ℕ)) =>
    intervalForce p N
      ⟨cyclicGapSum N i (r.val + 1) x,
        PhysicalEnergy.gapSum_mem N i (by omega) (by have := r.isLt; omega) x hx⟩
  let A := fun r : Fin ((N : ℕ) - 1) =>
    F r (j + 1 - (r.val + 1) • (1 : Fin (N : ℕ))) - F r (j + 1)
  have hperiod : (N : ℕ) • (1 : Fin (N : ℕ)) = 0 := by
    simpa only [Fintype.card_fin] using (card_nsmul_eq_zero (x := (1 : Fin (N : ℕ))))
  have hreflect (r : Fin ((N : ℕ) - 1)) :
      A ⟨(N : ℕ) - 2 - r.val, by have := r.isLt; omega⟩ = A r := by
    let q : Fin ((N : ℕ) - 1) := ⟨(N : ℕ) - 2 - r.val, by have := r.isLt; omega⟩
    have hlen : q.val + 1 = (N : ℕ) - (r.val + 1) := by
      dsimp [q]
      have := r.isLt
      omega
    have hadd : (r.val + 1) • (1 : Fin (N : ℕ)) +
        (q.val + 1) • (1 : Fin (N : ℕ)) = 0 := by
      rw [← add_nsmul, hlen, Nat.add_sub_of_le (by have := r.isLt; omega), hperiod]
    have hshift : j + 1 - (q.val + 1) • (1 : Fin (N : ℕ)) =
        j + 1 + (r.val + 1) • (1 : Fin (N : ℕ)) := by
      apply (sub_eq_iff_eq_add).mpr
      rw [add_assoc, hadd, add_zero]
    have hfirst : F q (j + 1 - (q.val + 1) • (1 : Fin (N : ℕ))) = -F r (j + 1) := by
      have hc := physical_intervalForce_complement p N x hx (j + 1)
        (r := r.val + 1) (by omega) (by have := r.isLt; omega)
      dsimp only [F]
      rw [hshift]
      convert hc using 1
      congr 2
      exact congrArg (fun t => cyclicGapSum N _ t x) hlen
    have hsecond : F q (j + 1) =
        -F r (j + 1 - (r.val + 1) • (1 : Fin (N : ℕ))) := by
      have hc := physical_intervalForce_complement p N x hx
        (j + 1 - (r.val + 1) • (1 : Fin (N : ℕ)))
        (r := r.val + 1) (by omega) (by have := r.isLt; omega)
      rw [sub_add_cancel] at hc
      dsimp only [F]
      convert hc using 1
      congr 2
      exact congrArg (fun t => cyclicGapSum N _ t x) hlen
    change F q (j + 1 - (q.val + 1) • (1 : Fin (N : ℕ))) - F q (j + 1) = _
    rw [hfirst, hsecond]
    dsimp only [A]
    ring
  have hsum := GapChart.sum_reflected_lengths hN A hreflect
  have hp := hd ⟨WithLp.toLp 2 x, PhysicalEnergy.simplex_subset_ambient N x hx⟩ j
  dsimp only at hp ⊢
  rw [hp]
  exact hsum.symm

/-- See Appendix C in the paper: each pinned particle force
is twice its pair-force sum. The factor two is derived from the short-interval energy, including an even antipodal rank, rather than
assumed from a separate energy encoding. -/
theorem physical_pinned_pair_force (p : Parameters) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) :
    ∃ W : EuclideanSpace ℝ (Fin (N : ℕ)) → ℝ,
      ContDiffOn ℝ ∞ W (gapAmbientDomain N) ∧
      (∀ y : {y : EuclideanSpace ℝ (Fin (N : ℕ)) // y ∈ gapAmbientDomain N},
        W y.val = physicalAmbientGapEnergy p N y) ∧
      ∀ (x : Fin (N : ℕ) → ℝ) (hx : x ∈ Riesz1.gapSimplex N)
        (j : Fin (N : ℕ)),
        fderiv ℝ W (WithLp.toLp 2 x)
          (WithLp.toLp 2 (Pi.single j 1 - Pi.single (j + 1) 1)) =
          -2 * ∑ r : Fin ((N : ℕ) - 1),
            intervalForce p N
              ⟨cyclicGapSum N (j + 1) (r.val + 1) x,
                PhysicalEnergy.gapSum_mem N _ (by omega) (by have := r.isLt; omega) x hx⟩ := by
  classical
  obtain ⟨W, hW, hv, hd⟩ := physical_pinned_derivatives_all_ranks p N hN
  refine ⟨W, hW, hv, ?_⟩
  intro x hx j
  let F := fun (r : Fin ((N : ℕ) - 1)) (i : Fin (N : ℕ)) =>
    intervalForce p N
      ⟨cyclicGapSum N i (r.val + 1) x,
        PhysicalEnergy.gapSum_mem N i (by omega) (by have := r.isLt; omega) x hx⟩
  have hreflect (r : Fin ((N : ℕ) - 1)) :
      F r (j + 1 - (r.val + 1) • (1 : Fin (N : ℕ))) = -F r.rev (j + 1) := by
    have hc := physical_intervalForce_complement p N x hx
      (j + 1 - (r.val + 1) • (1 : Fin (N : ℕ)))
      (r := r.val + 1) (by omega) (by have := r.isLt; omega)
    rw [sub_add_cancel] at hc
    have he : F r.rev (j + 1) =
        -F r (j + 1 - (r.val + 1) • (1 : Fin (N : ℕ))) := by
      dsimp only [F]
      convert hc using 1
      congr 2
      apply congrArg (fun t => cyclicGapSum N (j + 1) t x)
      simp only [Fin.val_rev]
      have := r.isLt
      omega
    linarith
  have hsum : (∑ r, F r (j + 1 - (r.val + 1) • (1 : Fin (N : ℕ)))) =
      -(∑ r, F r (j + 1)) := by
    simp_rw [hreflect]
    rw [Finset.sum_neg_distrib]
    congr 1
    exact Equiv.sum_comp Fin.revPerm (fun r => F r (j + 1))
  rw [hd x hx j]
  change (∑ r, (F r (j + 1 - (r.val + 1) • (1 : Fin (N : ℕ))) - F r (j + 1))) =
    -2 * ∑ r, F r (j + 1)
  rw [Finset.sum_sub_distrib, hsum]
  ring

end Riesz2.InterpolantLocalLaws
