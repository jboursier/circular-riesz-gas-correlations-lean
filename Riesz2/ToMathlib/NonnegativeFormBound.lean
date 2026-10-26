/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.MatrixEnergySpaces
public import Riesz2.HelfferSjostrand.IntrinsicScalarCore
public import Riesz2.ToMathlib.IntrinsicLangevin

/-!
# Nonnegative multiplication bounds on completed forms

A scalar estimate on a dense form core extends to the whole Hilbert form
space. The conclusion includes integrability, so a Bochner junk value cannot
satisfy the estimate. This uses Fatou and the existing L² subsequence theorem.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Riesz2.NonnegativeFormBound

variable {α H : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Internal completion lemma: a nonnegative multiplication form bounded
on a dense submodule has the same bound everywhere, with finite energy. -/
theorem extend_from_dense (J : H →L[ℝ] Lp ℝ 2 μ)
    (D : Submodule ℝ H) (hD : Dense (D : Set H))
    (w : α → ℝ) (hw : AEStronglyMeasurable w μ) (hw0 : 0 ≤ᵐ[μ] w)
    (C : ℝ) (hC : 0 ≤ C) (hcore : ∀ f ∈ D,
      Integrable (fun x => w x * (J f x) ^ 2) μ ∧
        (∫ x, w x * (J f x) ^ 2 ∂μ) ≤ C * ‖f‖ ^ 2) (f : H) :
    Integrable (fun x => w x * (J f x) ^ 2) μ ∧
      (∫ x, w x * (J f x) ^ 2 ∂μ) ≤ C * ‖f‖ ^ 2 := by
  obtain ⟨g, hgD, hg⟩ := mem_closure_iff_seq_limit.mp (hD f)
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (J.continuous.tendsto f |>.comp hg)).exists_seq_tendsto_ae
  let F := fun n x => w x * (J (g (ns n)) x) ^ 2
  let G := fun x => w x * (J f x) ^ 2
  have hi (n) : Integrable (F n) μ := (hcore _ (hgD _)).1
  have hnonneg (n) : 0 ≤ᵐ[μ] F n := hw0.mono fun x hx => mul_nonneg hx (sq_nonneg _)
  have hG : AEStronglyMeasurable G μ := hw.mul ((Lp.aestronglyMeasurable _).pow 2)
  have hG0 : 0 ≤ᵐ[μ] G := hw0.mono fun x hx => mul_nonneg hx (sq_nonneg _)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => ENNReal.ofReal (F n x)) atTop
      (𝓝 (ENNReal.ofReal (G x))) := by
    filter_upwards [hae] with x hx
    exact ENNReal.tendsto_ofReal (tendsto_const_nhds.mul (hx.pow 2))
  have hf := lintegral_liminf_le' (μ := μ) (u := atTop)
    (fun n => (hi n).aemeasurable.ennreal_ofReal)
  have he : (∫⁻ x, atTop.liminf (fun n => ENNReal.ofReal (F n x)) ∂μ) =
      ∫⁻ x, ENNReal.ofReal (G x) ∂μ :=
    lintegral_congr_ae (hlim.mono fun _ hx => hx.liminf_eq)
  have hb (n) : (∫⁻ x, ENNReal.ofReal (F n x) ∂μ) ≤
      ENNReal.ofReal (C * ‖g (ns n)‖ ^ 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hi n) (hnonneg n)]
    exact ENNReal.ofReal_le_ofReal (hcore _ (hgD _)).2
  have hbound : (∫⁻ x, ENNReal.ofReal (G x) ∂μ) ≤ ENNReal.ofReal (C * ‖f‖ ^ 2) := by
    rw [← he]
    apply hf.trans
    apply (liminf_le_liminf (Eventually.of_forall hb)).trans_eq
    exact (ENNReal.tendsto_ofReal (tendsto_const_nhds.mul
      (((hg.comp hns.tendsto_atTop).norm).pow 2))).liminf_eq
  have hGi : Integrable G μ := by
    exact ⟨hG, (hasFiniteIntegral_iff_ofReal hG0).mpr
      (hbound.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hGi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hGi hG0] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbound

section Gibbs

open InnerProductSpace
open scoped ContDiff Laplacian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {U : Set E} {ρ : Measure E} {V : E → ℝ}

/-- The normalized Gibbs certificate agrees with exponential tilting,
including its finite positive normalization. -/
theorem gibbs_eq_tilted (hU : IsOpen U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) :
    ρ = (volume.restrict U).tilted (fun x => -V x) := by
  let Z := ∫⁻ x in U, ENNReal.ofReal (Real.exp (-V x))
  have hZ : 0 < Z.toReal := ENNReal.toReal_pos hV.2.1.ne' hV.2.2.1.ne
  have hI : (∫ x in U, Real.exp (-V x)) = Z.toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => Real.exp_nonneg _)
      (hV.1.neg.exp.continuousOn.aestronglyMeasurable hU.measurableSet)
  rw [hV.2.2.2, ← withDensity_smul' _ _ (ENNReal.inv_ne_top.mpr hV.2.1.ne'),
    Measure.tilted, hI]
  apply congrArg ((volume.restrict U).withDensity)
  funext x
  rw [div_eq_mul_inv, ENNReal.ofReal_mul (Real.exp_nonneg _),
    ENNReal.ofReal_inv_of_pos hZ, ENNReal.ofReal_toReal hV.2.2.1.ne]
  simp only [Pi.smul_apply, smul_eq_mul, mul_comm]

/-- Internal compact-test score identity behind the physical trace bound.
It uses the Euclidean metric of the base space, including intrinsic bases. -/
theorem compact_gibbs_score_identity (hU : IsOpen U)
    (hV : IsEuclideanGibbsPotential volume ρ U V)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hfU : tsupport f ⊆ U) :
    (∫ x, f x ^ 2 * ‖gradient V x‖ ^ 2 ∂ρ) =
      (∫ x, f x ^ 2 * Δ V x ∂ρ) +
        2 * ∫ x, f x * inner ℝ (gradient f x) (gradient V x) ∂ρ := by
  have := IntrinsicScalarCore.probability hV
  let b := stdOrthonormalBasis ℝ E
  let dv := fun i x => fderiv ℝ V x (b i)
  let df := fun i x => fderiv ℝ f x (b i)
  let ddv := fun i x => fderiv ℝ (dv i) x (b i)
  have hdv (i) : ContDiffOn ℝ ∞ (dv i) U :=
    (hV.1.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  have hddv (i) : ContinuousOn (ddv i) U :=
    ((hdv i).continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const
  have hdf (i) : ContDiff ℝ ∞ (df i) :=
    (hf.fderiv_right (by simp)).clm_apply contDiff_const
  have hfsq : HasCompactSupport (fun x => f x ^ 2) := by
    simpa only [pow_two] using (show HasCompactSupport (fun x => f x * f x) from hfc.mul_right)
  have hfsU : tsupport (fun x => f x ^ 2) ⊆ U := by
    simpa only [pow_two] using
      (tsupport_mul_subset_left (f := f) (g := f)).trans hfU
  have hi₁ (i) : Integrable (fun x => f x ^ 2 * (dv i x) ^ 2) ρ :=
    Intrinsic.integrable_cutoff_mul hU (hf.pow 2).continuous hfsq
      hfsU ((hdv i).pow 2).continuousOn
  have hi₂ (i) : Integrable (fun x => f x ^ 2 * ddv i x) ρ :=
    Intrinsic.integrable_cutoff_mul hU (hf.pow 2).continuous hfsq
      hfsU (hddv i)
  have hi₃ (i) : Integrable (fun x => f x * df i x * dv i x) ρ :=
    Intrinsic.integrable_cutoff_mul hU (hf.mul (hdf i)).continuous
      (hfc.mul_right) (tsupport_mul_subset_left.trans hfU) (hdv i).continuousOn
  have hid (i) : (∫ x, f x ^ 2 * ddv i x ∂ρ) =
      (∫ x, f x ^ 2 * dv i x ^ 2 ∂ρ) -
        2 * ∫ x, f x * df i x * dv i x ∂ρ := by
    have hh := Intrinsic.directional_integrationByParts volume hU hV.1
      (hf.pow 2) hfsq hfsU (hdv i) (b i)
    rw [← gibbs_eq_tilted hU hV] at hh
    have hder (x) : fderiv ℝ (fun x => f x ^ 2) x (b i) = 2 * f x * df i x := by
      rw [((hf.differentiable (by simp) x).hasFDerivAt.pow 2).fderiv]
      simp [df, mul_assoc]
    simp_rw [hder] at hh
    change (∫ x, f x ^ 2 * ddv i x ∂ρ) = _ at hh
    rw [show (fun x => dv i x * (dv i x * f x ^ 2 - 2 * f x * df i x)) =
      fun x => f x ^ 2 * dv i x ^ 2 - 2 * (f x * df i x * dv i x) by funext x; ring,
      integral_sub (hi₁ i) ((hi₃ i).const_mul 2), integral_const_mul] at hh
    exact hh
  have hg (x) : ‖gradient V x‖ ^ 2 = ∑ i, (dv i x) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner]
    simp only [dv, inner_gradient_left, inner_gradient_right, conj_trivial, sq]
  have hc (x) : inner ℝ (gradient f x) (gradient V x) =
      ∑ i, df i x * dv i x := by
    rw [← b.sum_inner_mul_inner]
    simp only [df, dv, inner_gradient_left, inner_gradient_right, conj_trivial]
  have hl (x) (hx : x ∈ U) : Δ V x = ∑ i, ddv i x := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis V b]
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    apply Finset.sum_congr rfl
    intro i _
    have hd := ((hV.1.contDiffAt (hU.mem_nhds hx)).fderiv_right
      (m := ∞) (by simp)).differentiableAt (by simp)
    change _ = fderiv ℝ (fun y => fderiv ℝ V y (b i)) x (b i)
    rw [fderiv_clm_apply hd (differentiableAt_const (b i))]
    simp
  have htrace : (fun x => f x ^ 2 * Δ V x) =ᵐ[ρ]
      (fun x => ∑ i, f x ^ 2 * ddv i x) :=
    (IntrinsicScalarCore.supported hU hV).mono (fun x hx => by dsimp only; rw [hl x hx, Finset.mul_sum])
  rw [integral_congr_ae htrace]
  simp_rw [hg, hc, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hi₁ i),
    integral_finsetSum _ (fun i _ => hi₂ i),
    integral_finsetSum _ (fun i _ => by simpa only [mul_assoc] using hi₃ i)]
  simp only [← mul_assoc]
  have hsum := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hid i)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  linarith

/-- Internal compact-test estimate: domination of the trace by one quarter
of the squared score bounds its multiplication form by mass and diffusion.
Integrability is a conclusion, independent of the sign of the trace. -/
theorem compact_gibbs_trace_bound (hU : IsOpen U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) (C : ℝ)
    (hsub : ∀ x ∈ U, Δ V x ≤ (1 / 4 : ℝ) * ‖gradient V x‖ ^ 2 + C)
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hfU : tsupport f ⊆ U) :
    Integrable (fun x => f x ^ 2 * Δ V x) ρ ∧
      (∫ x, f x ^ 2 * Δ V x ∂ρ) ≤
        2 * (∫ x, ‖gradient f x‖ ^ 2 ∂ρ) + 2 * C * (∫ x, f x ^ 2 ∂ρ) := by
  have := IntrinsicScalarCore.probability hV
  have hgv : ContinuousOn (gradient V) U :=
    (toDual ℝ E).symm.continuous.comp_continuousOn
      (hV.1.continuousOn_fderiv_of_isOpen hU (by simp))
  have hgf : Continuous (gradient f) :=
    (toDual ℝ E).symm.continuous.comp (hf.continuous_fderiv (by simp))
  have hvd : ContDiffOn ℝ ∞ (fderiv ℝ V) U := hV.1.fderiv_of_isOpen hU (by simp)
  have hΔ : ContinuousOn (Δ V) U := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis V
      (stdOrthonormalBasis ℝ E)]
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    apply continuousOn_finsetSum
    intro i _
    exact ((hvd.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply continuousOn_const).clm_apply continuousOn_const
  have hfs : HasCompactSupport (fun x => f x ^ 2) := by
    simpa only [pow_two] using (show HasCompactSupport (fun x => f x * f x) from hfc.mul_right)
  have hfsU : tsupport (fun x => f x ^ 2) ⊆ U := by
    simpa only [pow_two] using (tsupport_mul_subset_left (f := f) (g := f)).trans hfU
  have hA : Integrable (fun x => f x ^ 2 * ‖gradient V x‖ ^ 2) ρ :=
    Intrinsic.integrable_cutoff_mul hU (hf.pow 2).continuous hfs hfsU (hgv.norm.pow 2)
  have hB : Integrable (fun x => f x ^ 2 * Δ V x) ρ :=
    Intrinsic.integrable_cutoff_mul hU (hf.pow 2).continuous hfs hfsU hΔ
  have hX : Integrable (fun x => f x * inner ℝ (gradient f x) (gradient V x)) ρ :=
    Intrinsic.integrable_cutoff_mul hU hf.continuous hfc hfU
      (hgf.continuousOn.inner hgv)
  have hD : Integrable (fun x => ‖gradient f x‖ ^ 2) ρ :=
    (Intrinsic.memLp_gradient hf hfc).norm.integrable_sq
  have hF : Integrable (fun x => f x ^ 2) ρ :=
    (hf.continuous.memLp_of_hasCompactSupport hfc).integrable_sq
  have hscore := compact_gibbs_score_identity hU hV hf hfc hfU
  have hyoung : 2 * (∫ x, f x * inner ℝ (gradient f x) (gradient V x) ∂ρ) ≤
      (1 / 2 : ℝ) * (∫ x, f x ^ 2 * ‖gradient V x‖ ^ 2 ∂ρ) +
        2 * (∫ x, ‖gradient f x‖ ^ 2 ∂ρ) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (hA.const_mul _) (hD.const_mul _)]
    apply integral_mono (hX.const_mul _) ((hA.const_mul _).add (hD.const_mul _))
    intro x
    have h : 0 ≤ inner ℝ (f x • gradient V x - (2 : ℝ) • gradient f x)
        (f x • gradient V x - (2 : ℝ) • gradient f x) := real_inner_self_nonneg
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq,
      real_inner_comm (gradient V x) (gradient f x)] at h
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
    have hcomm : inner ℝ (gradient V x) (gradient f x) =
        inner ℝ (gradient f x) (gradient V x) := real_inner_comm _ _
    rw [hcomm] at h
    change 2 * (f x * inner ℝ (gradient f x) (gradient V x)) ≤
      (1 / 2 : ℝ) * (f x ^ 2 * ‖gradient V x‖ ^ 2) + 2 * ‖gradient f x‖ ^ 2
    nlinarith only [h]
  have hupper : (∫ x, f x ^ 2 * Δ V x ∂ρ) ≤
      (1 / 4 : ℝ) * (∫ x, f x ^ 2 * ‖gradient V x‖ ^ 2 ∂ρ) +
        C * (∫ x, f x ^ 2 ∂ρ) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (hA.const_mul _) (hF.const_mul _)]
    apply integral_mono_ae hB ((hA.const_mul _).add (hF.const_mul _))
    filter_upwards [IntrinsicScalarCore.supported hU hV] with x hx
    change f x ^ 2 * Δ V x ≤ (1 / 4 : ℝ) * (f x ^ 2 * ‖gradient V x‖ ^ 2) + C * f x ^ 2
    nlinarith only [mul_le_mul_of_nonneg_left (hsub x hx) (sq_nonneg (f x))]
  exact ⟨hB, by linarith only [hscore, hyoung, hupper]⟩

set_option backward.isDefEq.respectTransparency false in
/-- Internal Sobolev trace estimate on the literal completed scalar jets.
The compact-test estimate extends by Fatou. Integrability is concluded for
every completed value. The only core premise is the usual collision bound. -/
theorem gibbs_trace_bound [Nontrivial E] (hU : IsOpen U)
    (hbounded : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V)
    (C : ℝ) (hC : 0 ≤ C)
    (hsub : ∀ x ∈ U, Δ V x ≤ (1 / 4 : ℝ) * ‖gradient V x‖ ^ 2 + C)
    (htrace : ∀ x ∈ U, 0 ≤ Δ V x)
    (B : ℝ) (hB : 0 ≤ B)
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹ ^ 2 - B ≤
      ‖gradient V x‖ ^ 2 / 4 - Δ V x / 2)
    (f : ScalarForm.Domain (IntrinsicScalarCore.jet hU hbounded hV)) :
    let J := IntrinsicScalarCore.jet hU hbounded hV
    Integrable (fun x => Δ V x * (ScalarForm.value J f x) ^ 2) ρ ∧
      (∫ x, Δ V x * (ScalarForm.value J f x) ^ 2 ∂ρ) ≤ (2 + 2 * C) * ‖f‖ ^ 2 := by
  intro J
  have := IntrinsicScalarCore.probability hV
  have hΔ : ContinuousOn (Δ V) U := by
    have hd : ContDiffOn ℝ ∞ (fderiv ℝ V) U := hV.1.fderiv_of_isOpen hU (by simp)
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis V
      (stdOrthonormalBasis ℝ E)]
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact continuousOn_finsetSum _ fun i _ =>
      ((hd.continuousOn_fderiv_of_isOpen hU (by simp)).clm_apply
        continuousOn_const).clm_apply continuousOn_const
  have hmeas : AEStronglyMeasurable (Δ V) ρ := by
    have h := hΔ.aestronglyMeasurable (μ := ρ) hU.measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem (IntrinsicScalarCore.supported hU hV)] at h
  apply extend_from_dense (ScalarForm.value J)
    (IntrinsicScalarCore.compactFormDomain hU hbounded hV)
    (IntrinsicScalarCore.dense_compactFormDomain hU hbounded hV hB hbar)
    (Δ V) hmeas ((IntrinsicScalarCore.supported hU hV).mono fun x hx => htrace x hx)
    (2 + 2 * C) (by positivity) _ f
  intro g hg
  obtain ⟨c, hc, rfl⟩ := hg
  have hclp := Riesz1.WeightedSobolev.memLp_of_smoothNearClosure
    hbounded (IntrinsicScalarCore.supported hU hV) c.property
  have hv : (ScalarForm.value J (ScalarForm.ofCore J c) : E → ℝ) =ᵐ[ρ] c.val :=
    hclp.1.coeFn_toLp
  have hd : (ScalarForm.deriv J (ScalarForm.ofCore J c) : E → E) =ᵐ[ρ] gradient c.val :=
    hclp.2.coeFn_toLp
  have hmass : (∫ x, c.val x ^ 2 ∂ρ) = ‖ScalarForm.value J (ScalarForm.ofCore J c)‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    simp only [real_inner_self_eq_norm_sq, hx, Real.norm_eq_abs, sq_abs]
  have hdiff : (∫ x, ‖gradient c.val x‖ ^ 2 ∂ρ) =
      ‖ScalarForm.deriv J (ScalarForm.ofCore J c)‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hd] with x hx
    simp only [real_inner_self_eq_norm_sq, hx]
  have he : (fun x => c.val x ^ 2 * Δ V x) =ᵐ[ρ]
      (fun x => Δ V x * (ScalarForm.value J (ScalarForm.ofCore J c) x) ^ 2) :=
    hv.mono fun x hx => by dsimp only; rw [hx, mul_comm]
  obtain ⟨hi, hb⟩ := compact_gibbs_trace_bound hU hV C hsub hc.1 hc.2.1 hc.2.2
  refine ⟨hi.congr he, ?_⟩
  rw [← integral_congr_ae he, hmass, hdiff] at *
  have hn := ScalarForm.norm_sq J (ScalarForm.ofCore J c)
  rw [ScalarForm.energy, real_inner_self_eq_norm_sq] at hn
  nlinarith [sq_nonneg ‖ScalarForm.value J (ScalarForm.ofCore J c)‖,
    sq_nonneg ‖ScalarForm.deriv J (ScalarForm.ofCore J c)‖]

end Gibbs

end Riesz2.NonnegativeFormBound
