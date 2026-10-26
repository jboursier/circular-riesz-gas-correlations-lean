/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayLong.MesoscopicVariancePart3
public import Riesz2.Preliminaries.GapSymmetries
public import Riesz2.ToMathlib.CovarianceThreeTerm
public import Riesz2.ToMathlib.RpowThreeQuarters
import Riesz2.Sanity.FiniteLaws

/-!
# Separated-block lower bound

See the lower bound argument in the proof of Theorem 1. For `0 < s < 1` and `β > 0`, there is `c₀ > 0` such that, for
every integer sequence `n_N` with `n_N → ∞` and `n_N / N → 0`, for all sufficiently large `N`
there are gap labels `i, j` with `n_N / 2 ≤ d_N(i, j) ≤ n_N` and `Cov(Y_i, Y_j) ≤ -c₀ d_N(i, j)^{s-2}`.

Sequences are indexed by `m` with `N = m + 1`, as in `Riesz2.IsMesoscopicSequence`. Gap labels
are the labels of `Riesz2.gap`, which are the paper labels shifted down by one, and `Cov` is
`ProbabilityTheory.covariance` of the two gaps, which is `Riesz2.gapCorrelation` with identity
test functions.

Two blocks `A` and `B` of length `⌊n/4⌋` at distance about
`n` and a middle block `C` of length `n - 2⌊n/4⌋` satisfy
`2 Cov(A, B) = Var(A+B+C) + Var(C) - Var(A+C) - Var(B+C)`. Cyclic invariance and the finite
mesoscopic variance limit of `Riesz2.MesoscopicVariance` then give `Cov(A, B) / n^s → L < 0`,
where `L < 0` by strict concavity of `t^s`. Averaging over the pairs of gaps in `A × B` gives a
pair with the stated bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology

namespace Riesz2.LowerCorrelations

/-- The block of `k` consecutive gaps starting at the label `i`: the sum of `Riesz2.gap X` over
the labels `i, i+1, …, i+k-1`. -/
def gapBlock (N : ℕ+) (i k : ℕ) (X : Riesz1.Configuration N) : ℝ :=
  ∑ a ∈ Finset.range k, Riesz2.gap X ((i + a : ℕ) : ℤ)

/-! ### Measurability and square integrability of gaps and blocks -/

theorem measurable_gap (N : ℕ+) (j : ℤ) :
    Measurable fun X : Riesz1.Configuration N => Riesz2.gap X j :=
  Riesz1.measurable_gap j

theorem abs_gap_le (N : ℕ+) (j : ℤ) (X : Riesz1.Configuration N) :
    ‖Riesz2.gap X j‖ ≤ (N : ℝ) := by
  change ‖Riesz1.gap X j‖ ≤ (N : ℝ)
  rw [Real.norm_eq_abs, abs_of_pos (Riesz1.gap_pos X j)]
  exact Riesz1.gap_le_N X j

theorem gap_memLp (p : Parameters) (N : ℕ+) (j : ℤ) :
    MemLp (fun X : Riesz1.Configuration N => Riesz2.gap X j) 2 (gibbsMeasure p N) := by
  have := FrozenSanity.gibbsMeasure_probability p N
  exact MemLp.of_bound (measurable_gap N j).aestronglyMeasurable (N : ℝ)
    (Filter.Eventually.of_forall fun X => abs_gap_le N j X)

theorem gapBlock_measurable (N : ℕ+) (i k : ℕ) : Measurable (gapBlock N i k) := by
  unfold gapBlock
  exact Finset.measurable_sum _ fun a _ => measurable_gap N _

theorem gapBlock_memLp (p : Parameters) (N : ℕ+) (i k : ℕ) :
    MemLp (gapBlock N i k) 2 (gibbsMeasure p N) := by
  unfold gapBlock
  apply memLp_finsetSum
  intro a _
  exact gap_memLp p N _

/-- The gap at a natural label depends only on the label modulo `N`. -/
theorem gap_nat_eq_mod (N : ℕ+) (X : Riesz1.Configuration N) (x : ℕ) :
    Riesz2.gap X (x : ℤ) = Riesz2.gap X ((x % (N : ℕ) : ℕ) : ℤ) := by
  have key : ∀ q : ℕ, Riesz2.gap X ((x % (N : ℕ) + (N : ℕ) * q : ℕ) : ℤ) =
      Riesz2.gap X ((x % (N : ℕ) : ℕ) : ℤ) := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [← ih]
      have e : ((x % (N : ℕ) + (N : ℕ) * (q + 1) : ℕ) : ℤ) =
          ((x % (N : ℕ) + (N : ℕ) * q : ℕ) : ℤ) + ((N : ℕ) : ℤ) := by
        push_cast
        ring
      rw [e]
      exact Riesz1.gap_add_N X _
  conv_lhs => rw [← Nat.mod_add_div x (N : ℕ)]
  exact key (x / (N : ℕ))

/-- The block of gaps is the cyclic gap sum `Riesz2.cyclicGapSum` of the gap vector,
started at the label `i` modulo `N` (Subsection 3.2). -/
theorem gapBlock_eq_cyclicGapSum (N : ℕ+) (i k : ℕ) (X : Riesz1.Configuration N) :
    gapBlock N i k X =
      Riesz2.cyclicGapSum N ⟨i % (N : ℕ), Nat.mod_lt _ N.pos⟩ k (Riesz2.gapVector X) := by
  unfold gapBlock Riesz2.cyclicGapSum
  apply Finset.sum_congr rfl
  intro a _
  change Riesz2.gap X ((i + a : ℕ) : ℤ) = Riesz2.gap X ((((i % (N : ℕ)) + a) % (N : ℕ) : ℕ) : ℤ)
  rw [gap_nat_eq_mod N X (i + a), Nat.mod_add_mod]

/-! ### Cyclic invariance -/

/-- The Gibbs law is invariant under the cyclic relabelling for every `N ≥ 2`. -/
theorem gibbsMeasure_map_cycle (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    (gibbsMeasure p N).map (Riesz2.GapSymmetries.cycleConfig (N := N)) = gibbsMeasure p N := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, N = (k + 1).succPNat :=
    ⟨(N : ℕ) - 2, PNat.eq (by simp only [Nat.succPNat_coe]; omega)⟩
  exact Riesz2.GapSymmetries.gibbsMeasure_map_cycleConfig p k

/-- The cyclic relabelling shifts the starting label of a gap block by one. -/
theorem gapBlock_comp_cycle (N : ℕ+) (i k : ℕ) :
    gapBlock N i k ∘ Riesz2.GapSymmetries.cycleConfig = gapBlock N (i + 1) k := by
  funext X
  unfold gapBlock
  simp only [Function.comp_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [Riesz2.GapSymmetries.gap_cycleConfig]
  congr 1
  push_cast
  ring

/-- The variance of a block is unchanged when its starting label moves by one. -/
theorem covariance_gapBlock_succ (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (i k : ℕ) :
    ProbabilityTheory.covariance (gapBlock N i k) (gapBlock N i k) (gibbsMeasure p N) =
      ProbabilityTheory.covariance (gapBlock N (i + 1) k) (gapBlock N (i + 1) k)
        (gibbsMeasure p N) := by
  have h := ProbabilityTheory.covariance_map (μ := gibbsMeasure p N)
    (Z := Riesz2.GapSymmetries.cycleConfig (N := N)) (X := gapBlock N i k)
    (Y := gapBlock N i k) (gapBlock_measurable N i k).aestronglyMeasurable
    (gapBlock_measurable N i k).aestronglyMeasurable
    (Riesz2.GapSymmetries.measurable_cycleConfig).aemeasurable
  rw [gibbsMeasure_map_cycle p N hN, gapBlock_comp_cycle] at h
  exact h

/-- Every block has the variance of the block starting at label zero. -/
theorem covariance_gapBlock_start (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (k i : ℕ) :
    ProbabilityTheory.covariance (gapBlock N i k) (gapBlock N i k) (gibbsMeasure p N) =
      ProbabilityTheory.covariance (gapBlock N 0 k) (gapBlock N 0 k) (gibbsMeasure p N) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [← covariance_gapBlock_succ p N hN i k, ih]

/-! ### Algebra of blocks -/

/-- Two adjacent blocks form one block. -/
theorem gapBlock_add (N : ℕ+) (i k l : ℕ) :
    gapBlock N i (k + l) = fun X => gapBlock N i k X + gapBlock N (i + k) l X := by
  funext X
  unfold gapBlock
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  congr 2
  omega

/-- The finite block of the gaps is the block starting at label zero. -/
theorem finiteGapBlock_sum_eq (N K : ℕ+) :
    (fun X : Riesz1.Configuration N => ∑ j : Fin (K : ℕ), finiteGapBlock X j) =
      gapBlock N 0 (K : ℕ) := by
  funext X
  unfold gapBlock
  simp only [Nat.zero_add]
  exact Fin.sum_univ_eq_sum_range (fun a : ℕ => Riesz2.gap X (a : ℤ)) (K : ℕ)

/-- The library variance of the finite block is the covariance of the block. -/
theorem variance_toReal_eq_covariance (p : Parameters) (N K : ℕ+) :
    (Riesz1.variance (gibbsMeasure p N)
        (fun X : Riesz1.Configuration N => ∑ j : Fin (K : ℕ), finiteGapBlock X j)
        (MesoscopicVariance.integrable_finiteGapBlock_sum p N K)).toReal =
      ProbabilityTheory.covariance (gapBlock N 0 (K : ℕ)) (gapBlock N 0 (K : ℕ))
        (gibbsMeasure p N) := by
  have h2 := (MesoscopicVariance.finiteGapBlock_variance_finite p N K).2
  dsimp only at h2
  rw [h2, ← finiteGapBlock_sum_eq N K]
  unfold ProbabilityTheory.covariance
  simp only [pow_two]

/-- The covariance of two blocks is the double sum of the covariances of their gaps. -/
theorem covariance_gapBlock_pair (p : Parameters) (N : ℕ+) (i j k l : ℕ) :
    ProbabilityTheory.covariance (gapBlock N i k) (gapBlock N j l) (gibbsMeasure p N) =
      ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range l,
        ProbabilityTheory.covariance
          (fun X : Riesz1.Configuration N => Riesz2.gap X ((i + a : ℕ) : ℤ))
          (fun X : Riesz1.Configuration N => Riesz2.gap X ((j + b : ℕ) : ℤ))
          (gibbsMeasure p N) := by
  have := FrozenSanity.gibbsMeasure_probability p N
  exact ProbabilityTheory.covariance_fun_sum_fun_sum'
    (X := fun a X => Riesz2.gap X ((i + a : ℕ) : ℤ))
    (Y := fun b X => Riesz2.gap X ((j + b : ℕ) : ℤ))
    (s := Finset.range k) (t := Finset.range l)
    (fun a _ => gap_memLp p N _) (fun b _ => gap_memLp p N _)

/-- Two blocks of length `q` separated by a middle block: with `2 q ≤ n`, the covariance of the
first and second blocks is the combination `(Cov(0, n) + Cov(0, n-2q) - 2 Cov(0, n-q)) / 2` of
block covariances starting at zero. -/
theorem covariance_three_blocks (p : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (n q : ℕ)
    (hq : 2 * q ≤ n) :
    ProbabilityTheory.covariance (gapBlock N 0 q) (gapBlock N (n - q) q) (gibbsMeasure p N) =
      (ProbabilityTheory.covariance (gapBlock N 0 n) (gapBlock N 0 n) (gibbsMeasure p N) +
        ProbabilityTheory.covariance (gapBlock N 0 (n - 2 * q)) (gapBlock N 0 (n - 2 * q))
          (gibbsMeasure p N) -
        2 * ProbabilityTheory.covariance (gapBlock N 0 (n - q)) (gapBlock N 0 (n - q))
          (gibbsMeasure p N)) / 2 := by
  have := FrozenSanity.gibbsMeasure_probability p N
  have hA := gapBlock_memLp p N 0 q
  have hB := gapBlock_memLp p N (n - q) q
  have hC := gapBlock_memLp p N q (n - 2 * q)
  have hAC : gapBlock N 0 q + gapBlock N q (n - 2 * q) = gapBlock N 0 (n - q) := by
    have h := gapBlock_add N 0 q (n - 2 * q)
    rw [show q + (n - 2 * q) = n - q by omega, Nat.zero_add] at h
    rw [h]
    rfl
  have hBC : gapBlock N (n - q) q + gapBlock N q (n - 2 * q) = gapBlock N q (n - q) := by
    have h := gapBlock_add N q (n - 2 * q) q
    rw [show n - 2 * q + q = n - q by omega, show q + (n - 2 * q) = n - q by omega] at h
    rw [h]
    funext X
    simp only [Pi.add_apply]
    ring
  have hABC : gapBlock N 0 q + gapBlock N (n - q) q + gapBlock N q (n - 2 * q) =
      gapBlock N 0 n := by
    have h := gapBlock_add N 0 q (n - q)
    rw [show q + (n - q) = n by omega, Nat.zero_add] at h
    rw [h, ← hBC]
    funext X
    simp only [Pi.add_apply]
    ring
  have h2 := Riesz2.ToMathlib.two_covariance_eq_three_sum hA hB hC
  rw [hABC, hAC, hBC, covariance_gapBlock_start p N hN (n - 2 * q) q,
    covariance_gapBlock_start p N hN (n - q) q] at h2
  linarith

/-! ### Mesoscopic variance in the particle-number convention -/

/-- The covariance of the first `k` gaps under the Gibbs law with `N = m + 1` particles, the
block variance of `Riesz2.MesoscopicVariance`. -/
def blockCov (β : InverseTemperature) (s : Riesz1.RieszExponent) (m k : ℕ) : ℝ :=
  ProbabilityTheory.covariance (gapBlock (Riesz1.particleNumber m) 0 k)
    (gapBlock (Riesz1.particleNumber m) 0 k) (gibbsMeasure (ofLong β s) (Riesz1.particleNumber m))

/-- The block length `g m` clamped into `[1, N]` at `N = m + 1` particles, as a positive integer
sequence indexed by the particle number. -/
def clampLength (g : ℕ → ℕ) : ℕ+ → ℕ+ := fun N =>
  ⟨max 1 (min (g ((N : ℕ) - 1)) (N : ℕ)), lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)⟩

theorem clampLength_le (g : ℕ → ℕ) (N : ℕ+) : (clampLength g N : ℕ) ≤ (N : ℕ) :=
  max_le N.pos (min_le_right _ _)

theorem clampLength_particleNumber (g : ℕ → ℕ) (m : ℕ) :
    ((clampLength g (Riesz1.particleNumber m) : ℕ+) : ℕ) = max 1 (min (g m) (m + 1)) := by
  simp [clampLength, Riesz1.particleNumber]

/-- The normalized block variance `blockCov m (g m) / (g m)^s` converges to the limiting variance
along any block length `g` with `1 ≤ g m ≤ m + 1` eventually, `g → ∞` and `g / N → 0`. This is
`Riesz2.MesoscopicVariance.mesoscopic_variance` with the block lengths clamped. -/
theorem tendsto_blockCov_div (β : InverseTemperature) (s : Riesz1.RieszExponent) (g : ℕ → ℕ)
    (hg : ∀ᶠ m in atTop, 1 ≤ g m ∧ g m ≤ m + 1)
    (htop : Tendsto g atTop atTop)
    (hratio : Tendsto (fun m => (g m : ℝ) / (Riesz1.particleNumber m : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun m => blockCov β s m (g m) / ((g m : ℕ) : ℝ) ^ s.val) atTop
      (𝓝 (Riesz1.countVariance (longParameters β s))) := by
  have hE : ∀ᶠ m in atTop, ((clampLength g (Riesz1.particleNumber m) : ℕ+) : ℕ) = g m := by
    filter_upwards [hg] with m hm
    rw [clampLength_particleNumber, min_eq_left hm.2, max_eq_right hm.1]
  have hK : Riesz2.IsMesoscopicSequence (clampLength g) := by
    refine ⟨Tendsto.congr' (hE.mono fun m h => h.symm) htop, ?_⟩
    refine Tendsto.congr' ?_ hratio
    filter_upwards [hE] with m hm
    rw [hm]
  have hmain := Riesz2.MesoscopicVariance.mesoscopic_variance s β (clampLength g) hK
    (fun N => clampLength_le g N)
  refine Tendsto.congr' ?_ hmain.1
  filter_upwards [hE] with m hm
  dsimp only
  rw [variance_toReal_eq_covariance, hm]
  rfl

/-- The block variance scaled by `n^s` converges when the block lengths `f m` satisfy
`f m / n m → r > 0`, with `n` a sequence of particle-scale lengths. -/
theorem tendsto_blockCov_scaled (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n f : ℕ → ℕ) (r : ℝ) (hr : 0 < r)
    (hn : Tendsto (fun m => (n m : ℝ)) atTop atTop)
    (hnratio : Tendsto (fun m => (n m : ℝ) / (Riesz1.particleNumber m : ℝ)) atTop (𝓝 0))
    (hf : Tendsto (fun m => (f m : ℝ) / (n m : ℝ)) atTop (𝓝 r)) :
    Tendsto (fun m => blockCov β s m (f m) / (n m : ℝ) ^ s.val) atTop
      (𝓝 (Riesz1.countVariance (longParameters β s) * r ^ s.val)) := by
  have hn0 : ∀ᶠ m in atTop, (0 : ℝ) < n m := hn.eventually_gt_atTop 0
  have hfR : Tendsto (fun m => (f m : ℝ)) atTop atTop := by
    refine Tendsto.congr' ?_ (hf.pos_mul_atTop hr hn)
    filter_upwards [hn0] with m hm
    field_simp
  have hfN : Tendsto f atTop atTop := tendsto_natCast_atTop_iff.1 hfR
  have hfratio : Tendsto (fun m => (f m : ℝ) / (Riesz1.particleNumber m : ℝ)) atTop (𝓝 0) := by
    have h := hf.mul hnratio
    rw [mul_zero] at h
    refine Tendsto.congr' ?_ h
    filter_upwards [hn0] with m hm
    field_simp
  have hg : ∀ᶠ m in atTop, 1 ≤ f m ∧ f m ≤ m + 1 := by
    filter_upwards [hfN.eventually_ge_atTop 1, (tendsto_order.1 hfratio).2 1 one_pos] with m h1 h2
    refine ⟨h1, ?_⟩
    have hpos : (0 : ℝ) < ((Riesz1.particleNumber m : ℕ+) : ℕ) := by
      show (0 : ℝ) < ((m + 1 : ℕ) : ℝ)
      positivity
    rw [div_lt_one hpos] at h2
    have h3 : (f m : ℝ) < ((m + 1 : ℕ) : ℝ) := by
      simpa [Riesz1.particleNumber] using h2
    have h4 : f m < m + 1 := by exact_mod_cast h3
    omega
  have hcov := tendsto_blockCov_div β s f hg hfN hfratio
  have hpow : Tendsto (fun m => ((f m : ℝ) / (n m : ℝ)) ^ s.val) atTop (𝓝 (r ^ s.val)) :=
    hf.rpow_const (Or.inl hr.ne')
  refine Tendsto.congr' ?_ (hcov.mul hpow)
  filter_upwards [hn0, hg] with m hm hgm
  have hfpos : (0 : ℝ) < (f m : ℝ) := by exact_mod_cast (show 0 < f m by omega)
  rw [Real.div_rpow hfpos.le hm.le]
  have hfs : 0 < (f m : ℝ) ^ s.val := Real.rpow_pos_of_pos hfpos _
  have hns : 0 < (n m : ℝ) ^ s.val := Real.rpow_pos_of_pos hm _
  field_simp

/-! ### Limits of the block-length ratios -/

/-- The ratio `⌊n/4⌋ / n` converges to `1/4`. -/
theorem tendsto_quarter_ratio (n : ℕ → ℕ) (hn : Tendsto (fun m => (n m : ℝ)) atTop atTop) :
    Tendsto (fun m => ((n m / 4 : ℕ) : ℝ) / (n m : ℝ)) atTop (𝓝 (1 / 4)) := by
  have hinv : Tendsto (fun m => ((n m : ℝ))⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hn
  have hlow : Tendsto (fun m => (1 / 4 : ℝ) - 3 / 4 * ((n m : ℝ))⁻¹) atTop (𝓝 (1 / 4)) := by
    have h := (tendsto_const_nhds (x := (1 / 4 : ℝ))).sub (hinv.const_mul (3 / 4 : ℝ))
    rwa [mul_zero, sub_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [hn.eventually_gt_atTop 0] with m hm
    rw [le_div_iff₀ hm]
    have h4 : (n m : ℝ) ≤ 4 * ((n m / 4 : ℕ) : ℝ) + 3 := by
      exact_mod_cast (show n m ≤ 4 * (n m / 4) + 3 by omega)
    have hx : (1 / 4 - 3 / 4 * ((n m : ℝ))⁻¹) * (n m : ℝ) = (n m : ℝ) / 4 - 3 / 4 := by
      field_simp
    rw [hx]
    linarith
  · filter_upwards [hn.eventually_gt_atTop 0] with m hm
    rw [div_le_iff₀ hm]
    have h4 : 4 * ((n m / 4 : ℕ) : ℝ) ≤ (n m : ℝ) := by
      exact_mod_cast (show 4 * (n m / 4) ≤ n m by omega)
    linarith

/-- The ratio `(n - ⌊n/4⌋) / n` converges to `3/4`. -/
theorem tendsto_sub_quarter_ratio (n : ℕ → ℕ) (hn : Tendsto (fun m => (n m : ℝ)) atTop atTop) :
    Tendsto (fun m => ((n m - n m / 4 : ℕ) : ℝ) / (n m : ℝ)) atTop (𝓝 (3 / 4)) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_quarter_ratio n hn)
  rw [show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num] at h
  refine Tendsto.congr' ?_ h
  filter_upwards [hn.eventually_gt_atTop 0] with m hm
  rw [Nat.cast_sub (Nat.div_le_self _ _), sub_div, div_self hm.ne']

/-- The ratio `(n - 2⌊n/4⌋) / n` converges to `1/2`. -/
theorem tendsto_sub_two_quarter_ratio (n : ℕ → ℕ)
    (hn : Tendsto (fun m => (n m : ℝ)) atTop atTop) :
    Tendsto (fun m => ((n m - 2 * (n m / 4) : ℕ) : ℝ) / (n m : ℝ)) atTop (𝓝 (1 / 2)) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
    ((tendsto_const_nhds (x := (2 : ℝ))).mul (tendsto_quarter_ratio n hn))
  rw [show (1 : ℝ) - 2 * (1 / 4) = 1 / 2 by norm_num] at h
  refine Tendsto.congr' ?_ h
  filter_upwards [hn.eventually_gt_atTop 0] with m hm
  have h2 : 2 * (n m / 4) ≤ n m := by omega
  rw [Nat.cast_sub h2, sub_div, div_self hm.ne']
  push_cast
  ring

/-! ### The pair selection and the final bound -/

/-- Averaging over the `q²` pairs of gaps with one label in each of two blocks of length
`q = ⌊n/4⌋`: one pair has covariance at most `16 T / n²`, where `T ≤ 0` bounds the block
covariance and the distance is `n/2 ≤ d ≤ n`. -/
theorem exists_separated_pair (p : Parameters) (N : ℕ+) (n : ℕ) (hn4 : 4 ≤ n)
    (h2n : 2 * n ≤ (N : ℕ)) (T : ℝ) (hT0 : T ≤ 0)
    (hT : ProbabilityTheory.covariance (gapBlock N 0 (n / 4)) (gapBlock N (n - n / 4) (n / 4))
      (gibbsMeasure p N) ≤ T) :
    ∃ i j : Fin (N : ℕ), (n : ℝ) / 2 ≤ (Riesz1.cyclicIndexDistance N i j : ℝ) ∧
      (Riesz1.cyclicIndexDistance N i j : ℝ) ≤ n ∧
      ProbabilityTheory.covariance (fun X => Riesz2.gap X (i.val : ℤ))
        (fun X => Riesz2.gap X (j.val : ℤ)) (gibbsMeasure p N) ≤ 16 * T / (n : ℝ) ^ 2 := by
  have hq1 : 1 ≤ n / 4 := by omega
  have h4q : 4 * (n / 4) ≤ n := by omega
  have hsum0 := covariance_gapBlock_pair p N 0 (n - n / 4) (n / 4) (n / 4)
  simp only [Nat.zero_add] at hsum0
  set q := n / 4 with hqdef
  set S : Finset (ℕ × ℕ) := Finset.range q ×ˢ Finset.range q with hS
  set c : ℕ × ℕ → ℝ := fun ab => ProbabilityTheory.covariance
    (fun X : Riesz1.Configuration N => Riesz2.gap X ((ab.1 : ℕ) : ℤ))
    (fun X : Riesz1.Configuration N => Riesz2.gap X ((n - q + ab.2 : ℕ) : ℤ))
    (gibbsMeasure p N) with hc
  have hsumc : ∑ ab ∈ S, c ab =
      ProbabilityTheory.covariance (gapBlock N 0 q) (gapBlock N (n - q) q) (gibbsMeasure p N) := by
    rw [hsum0, hS, Finset.sum_product]
  have hcard : (S.card : ℝ) = (q : ℝ) * q := by
    rw [hS, Finset.card_product, Finset.card_range]
    push_cast
    ring
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq1
  have hq2 : (0 : ℝ) < (q : ℝ) * q := mul_pos hqR hqR
  obtain ⟨ab, hab, hle⟩ : ∃ ab ∈ S, c ab ≤ T / ((q : ℝ) * q) := by
    by_contra hcon
    simp only [not_exists, not_and, not_le] at hcon
    have hne : S.Nonempty := ⟨(0, 0), by rw [hS, Finset.mem_product, Finset.mem_range]; omega⟩
    have hlt := Finset.sum_lt_sum_of_nonempty hne (fun ab hab => hcon ab hab)
    rw [Finset.sum_const, nsmul_eq_mul, hcard, hsumc] at hlt
    have heq : (q : ℝ) * q * (T / ((q : ℝ) * q)) = T := by
      field_simp
    linarith
  obtain ⟨a, b⟩ := ab
  simp only [hS, Finset.mem_product, Finset.mem_range] at hab
  obtain ⟨ha, hb⟩ := hab
  have ha' : a < N := by omega
  have hc' : n - q + b < N := by omega
  have hdist : Riesz1.cyclicIndexDistance N ⟨a, ha'⟩ ⟨n - q + b, hc'⟩ = n - q + b - a := by
    have hd : Nat.dist a (n - q + b) = n - q + b - a := by
      unfold Nat.dist
      omega
    show min (Nat.dist a (n - q + b)) ((N : ℕ) - Nat.dist a (n - q + b)) = _
    rw [hd, min_eq_left (by omega)]
  have hd1 : (n : ℝ) / 2 ≤ (Riesz1.cyclicIndexDistance N ⟨a, ha'⟩ ⟨n - q + b, hc'⟩ : ℝ) := by
    rw [hdist, div_le_iff₀ (two_pos : (0 : ℝ) < 2)]
    exact_mod_cast (show n ≤ (n - q + b - a) * 2 by omega)
  have hd2 : (Riesz1.cyclicIndexDistance N ⟨a, ha'⟩ ⟨n - q + b, hc'⟩ : ℝ) ≤ n := by
    rw [hdist]
    exact_mod_cast (show n - q + b - a ≤ n by omega)
  refine ⟨⟨a, ha'⟩, ⟨n - q + b, hc'⟩, hd1, hd2, ?_⟩
  have hnR : (4 * q : ℝ) ≤ n := by exact_mod_cast h4q
  have hnpos : (0 : ℝ) < n := by linarith
  have key : T / ((q : ℝ) * q) ≤ 16 * T / (n : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ hq2 (by positivity)]
    have h1 : T * ((n : ℝ) ^ 2 - 16 * ((q : ℝ) * q)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hT0 (by nlinarith)
    nlinarith [h1]
  exact le_trans hle key

/-- The identity `16 (L/2) n^s / n² = 8 L n^(s-2)` for `n > 0`. -/
theorem sixteen_half_rpow_div_sq (L s : ℝ) {n : ℝ} (hn : 0 < n) :
    16 * (L / 2 * n ^ s) / n ^ 2 = 8 * L * n ^ (s - 2) := by
  rw [Real.rpow_sub hn, Real.rpow_two]
  field_simp
  ring

/-- For `n/2 ≤ d ≤ n` and an exponent `s - 2 ≤ 0`, the rpow comparison `2^(s-2) d^(s-2) ≤ n^(s-2)`
holds. -/
theorem two_rpow_mul_le_rpow (s : ℝ) {n d : ℝ} (hn : 0 < n) (hd : n / 2 ≤ d)
    (hs : s - 2 ≤ 0) :
    (2 : ℝ) ^ (s - 2) * d ^ (s - 2) ≤ n ^ (s - 2) := by
  have h1 : d ^ (s - 2) ≤ (n / 2) ^ (s - 2) :=
    Real.rpow_le_rpow_of_nonpos (half_pos hn) hd hs
  have h2 : (n / 2) ^ (s - 2) = n ^ (s - 2) / (2 : ℝ) ^ (s - 2) :=
    Real.div_rpow hn.le (by norm_num) _
  have h3 : (2 : ℝ) ^ (s - 2) * d ^ (s - 2) ≤ (2 : ℝ) ^ (s - 2) * (n ^ (s - 2) / (2 : ℝ) ^ (s - 2)) :=
    mul_le_mul_of_nonneg_left (h1.trans h2.le) (by positivity)
  have h4 : (2 : ℝ) ^ (s - 2) * (n ^ (s - 2) / (2 : ℝ) ^ (s - 2)) = n ^ (s - 2) := by
    field_simp
  linarith

/-- The covariance of two blocks in the particle-number convention is the combination of block
covariances from `covariance_three_blocks`. -/
theorem covariance_separated_identity (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (m n : ℕ) (hN : 2 ≤ (Riesz1.particleNumber m : ℕ)) (hn : 2 * (n / 4) ≤ n) :
    ProbabilityTheory.covariance (gapBlock (Riesz1.particleNumber m) 0 (n / 4))
        (gapBlock (Riesz1.particleNumber m) (n - n / 4) (n / 4))
        (gibbsMeasure (ofLong β s) (Riesz1.particleNumber m)) =
      (blockCov β s m n + blockCov β s m (n - 2 * (n / 4)) -
        2 * blockCov β s m (n - n / 4)) / 2 := by
  unfold blockCov
  have h := covariance_three_blocks (ofLong β s) (Riesz1.particleNumber m) hN n (n / 4) hn
  linarith

/-- See the proof of Theorem 1 in the paper, Lemma "Two separated blocks have negative
covariance". For `0 < s < 1` and `β > 0`, there is `c₀ > 0` such that, for every sequence `n`
with `n m → ∞` and `n m / N → 0` (where `N = m + 1`), for all sufficiently large `m` there are gap
labels `i, j` in `Fin N` with `n m / 2 ≤ d_N(i, j) ≤ n m` and
`Cov(Y_i, Y_j) ≤ -c₀ d_N(i, j)^(s-2)`. The constant `c₀` depends only on `s` and `β`. -/
theorem separated_block_covariance_lower (β : InverseTemperature) (s : Riesz1.RieszExponent) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ n : ℕ → ℕ,
      Tendsto (fun m => (n m : ℝ)) atTop atTop →
      Tendsto (fun m => (n m : ℝ) / (Riesz1.particleNumber m : ℝ)) atTop (𝓝 0) →
      ∀ᶠ m in atTop, ∃ i j : Fin (Riesz1.particleNumber m : ℕ),
        (n m : ℝ) / 2 ≤ (Riesz1.cyclicIndexDistance (Riesz1.particleNumber m) i j : ℝ) ∧
        (Riesz1.cyclicIndexDistance (Riesz1.particleNumber m) i j : ℝ) ≤ (n m : ℝ) ∧
        ProbabilityTheory.covariance (fun X => Riesz2.gap X (i.val : ℤ))
          (fun X => Riesz2.gap X (j.val : ℤ))
          (gibbsMeasure (ofLong β s) (Riesz1.particleNumber m)) ≤
          -c₀ * (Riesz1.cyclicIndexDistance (Riesz1.particleNumber m) i j : ℝ) ^ (s.val - 2) := by
  have hσ : 0 < Riesz1.countVariance (longParameters β s) :=
    Riesz2.MesoscopicVariance.limiting_variance_pos β s
  have hs0 : 0 < s.val := s.property.1
  have hs1 : s.val < 1 := s.property.2
  have hconc := Riesz2.ToMathlib.one_add_half_rpow_lt_two_three_quarters_rpow hs0 hs1
  set σ := Riesz1.countVariance (longParameters β s) with hσdef
  set L : ℝ := σ * (1 + (1 / 2 : ℝ) ^ s.val - 2 * (3 / 4 : ℝ) ^ s.val) / 2 with hLdef
  have hL : L < 0 := by
    have h1 : 1 + (1 / 2 : ℝ) ^ s.val - 2 * (3 / 4 : ℝ) ^ s.val < 0 := by linarith
    rw [hLdef]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hσ h1) two_pos
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ (s.val - 2) := Real.rpow_pos_of_pos two_pos _
  refine ⟨-(8 * L * (2 : ℝ) ^ (s.val - 2)), ?_, ?_⟩
  · have h8 : 8 * L * (2 : ℝ) ^ (s.val - 2) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) h2pos
    linarith
  intro n hn hnratio
  have hr1 : Tendsto (fun m => (n m : ℝ) / (n m : ℝ)) atTop (𝓝 1) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hn.eventually_gt_atTop 0] with m hm
    exact (div_self hm.ne').symm
  have V1 := tendsto_blockCov_scaled β s n n 1 one_pos hn hnratio hr1
  have V2 := tendsto_blockCov_scaled β s n (fun m => n m - 2 * (n m / 4)) (1 / 2) (by norm_num) hn
    hnratio (tendsto_sub_two_quarter_ratio n hn)
  have V3 := tendsto_blockCov_scaled β s n (fun m => n m - n m / 4) (3 / 4) (by norm_num) hn
    hnratio (tendsto_sub_quarter_ratio n hn)
  have hlim := ((V1.add V2).sub (V3.const_mul 2)).div_const 2
  have hLval : (σ * (1 : ℝ) ^ s.val + σ * (1 / 2 : ℝ) ^ s.val -
      2 * (σ * (3 / 4 : ℝ) ^ s.val)) / 2 = L := by
    rw [Real.one_rpow, hLdef]
    ring
  rw [hLval] at hlim
  have hΨ : Tendsto (fun m => ProbabilityTheory.covariance
      (gapBlock (Riesz1.particleNumber m) 0 (n m / 4))
      (gapBlock (Riesz1.particleNumber m) (n m - n m / 4) (n m / 4))
      (gibbsMeasure (ofLong β s) (Riesz1.particleNumber m)) / (n m : ℝ) ^ s.val) atTop (𝓝 L) := by
    refine Tendsto.congr' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with m hm1
    have hN : 2 ≤ (Riesz1.particleNumber m : ℕ) := by
      show 2 ≤ m + 1
      omega
    rw [covariance_separated_identity β s m (n m) hN (by omega)]
    ring
  have hΨlt := (tendsto_order.1 hΨ).2 (L / 2) (by linarith)
  have h2n : ∀ᶠ m in atTop, 2 * n m ≤ (Riesz1.particleNumber m : ℕ) := by
    filter_upwards [(tendsto_order.1 hnratio).2 (1 / 2 : ℝ) (by norm_num),
      hn.eventually_gt_atTop 0] with m h hpos
    have hp : (0 : ℝ) < ((Riesz1.particleNumber m : ℕ) : ℝ) := by
      show (0 : ℝ) < ((m + 1 : ℕ) : ℝ)
      positivity
    rw [div_lt_iff₀ hp] at h
    have h' : ((2 * n m : ℕ) : ℝ) < (((Riesz1.particleNumber m : ℕ)) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h'.le
  have h4 : ∀ᶠ m in atTop, 4 ≤ n m := by
    filter_upwards [hn.eventually_ge_atTop (4 : ℝ)] with m hm
    exact_mod_cast hm
  filter_upwards [hΨlt, h2n, h4] with m hΨm h2nm h4m
  have hn0 : (0 : ℝ) < n m := by exact_mod_cast (show 0 < n m by omega)
  have hns : 0 < (n m : ℝ) ^ s.val := Real.rpow_pos_of_pos hn0 _
  have hT : ProbabilityTheory.covariance (gapBlock (Riesz1.particleNumber m) 0 (n m / 4))
      (gapBlock (Riesz1.particleNumber m) (n m - n m / 4) (n m / 4))
      (gibbsMeasure (ofLong β s) (Riesz1.particleNumber m)) ≤ L / 2 * (n m : ℝ) ^ s.val := by
    rw [div_lt_iff₀ hns] at hΨm
    exact hΨm.le
  have hT0 : L / 2 * (n m : ℝ) ^ s.val ≤ 0 := by
    have := Real.rpow_nonneg hn0.le s.val
    nlinarith
  obtain ⟨i, j, hd1, hd2, hcov⟩ := exists_separated_pair (ofLong β s)
    (Riesz1.particleNumber m) (n m) h4m h2nm _ hT0 hT
  refine ⟨i, j, hd1, hd2, ?_⟩
  have hk := two_rpow_mul_le_rpow s.val hn0 hd1 (by linarith)
  have hL8 : 8 * L < 0 := by linarith
  have hfin := mul_le_mul_of_nonpos_left hk hL8.le
  have hid := sixteen_half_rpow_div_sq L s.val hn0
  nlinarith

end Riesz2.LowerCorrelations

end
end
