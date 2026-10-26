/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.IntrinsicScalarForms
public import Riesz2.Frozen.IsNeumannRealization
public import Riesz2.Frozen.IsConservativeScalarForm
public import Riesz2.Frozen.IsEuclideanGibbsPotential
public import Riesz2.Bridges.BoundaryKernel
public import Riesz1.ToMathlib.GroundStateProductRule
public import Riesz1.ToMathlib.NonnegativeOperatorCore
public import Riesz1.ToMathlib.LaplacianDirectionalDerivative
public import Riesz1.ToMathlib.SquareDensityL2
public import Riesz1.ToMathlib.EllipticRegularity.GlobalBridge
public import Riesz1.ToMathlib.EllipticRegularity.WeakOperations
public import Riesz1.ToMathlib.PeriodizationLaplacian

/-!
# Intrinsic scalar Neumann operator and form cores

The completion in `IntrinsicScalarForms` uses the Hilbert product norm. The
`neumannSobolevGraph` uses the ordinary product topology. Their
identification below transports the existing energy to `ScalarFormData`,
without changing either the Sobolev domain or the gradient metric.
The collision-barrier kernel theorem then gives every conclusion of
Appendix A, including graph approximants and equality of
the two smooth completion conventions. The form and its operator use
Subsection 3.1 throughout.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff Laplacian

namespace Riesz2
namespace ScalarForm

variable {Ω C G : Type*} [MeasurableSpace Ω]
  [AddCommGroup C] [Module ℝ C]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  {μ : Measure Ω} (J : C →ₗ[ℝ] Jet μ G)

/-- Identify completed jets with their values when the gradient is closable. -/
def valueEquiv (hinj : Function.Injective (value J)) :
    Domain J ≃ₗ[ℝ] (value J).range :=
  LinearEquiv.ofInjective (value J).toLinearMap hinj

/-- The existing closed scalar energy, on its actual L² value subspace. -/
def realization (hinj : Function.Injective (value J)) : ScalarFormData μ :=
  ⟨(value J).range,
    { toFun := fun f =>
        { toFun := fun g => energy J ((valueEquiv J hinj).symm f) ((valueEquiv J hinj).symm g)
          map_add' := fun _ _ => by rw [map_add, energy_add_right]
          map_smul' := fun _ _ => by rw [map_smul, energy_smul_right]; rfl }
      map_add' := fun _ _ => by
        ext g
        change energy J ((valueEquiv J hinj).symm (_ + _)) _ = _
        rw [map_add, energy_add_left]
        rfl
      map_smul' := fun _ _ => by
        ext g
        change energy J ((valueEquiv J hinj).symm (_ • _)) _ = _
        rw [map_smul, energy_smul_left]
        rfl }⟩

/-- Evaluation of the transported form on two completed jets. -/
theorem realization_energy (hinj : Function.Injective (value J)) (f g : Domain J) :
    (realization J hinj).2 (valueEquiv J hinj f) (valueEquiv J hinj g) = energy J f g := by
  change energy J ((valueEquiv J hinj).symm (valueEquiv J hinj f))
    ((valueEquiv J hinj).symm (valueEquiv J hinj g)) = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

section GraphApproximation

variable [CompleteSpace G]

/-- The resolvent recovers a form element from its value and operator value.
This is also the continuous map used to pass from graph to form convergence. -/
theorem resolvent_graph_input (u : Domain J) (a : Lp ℝ 2 μ)
    (hu : (u, a) ∈ neumannGraph J) :
    resolvent J (value J u + a) = u := by
  symm
  apply resolvent_unique
  intro v
  rw [hu v, inner_add_left]
  ring

/-- Graph-to-form convergence used in Appendix A.
The continuous resolvent recovers derivative convergence. -/
theorem tendsto_form_of_tendsto_graph
    (u : ℕ → Domain J) (a : ℕ → Lp ℝ 2 μ) (v : Domain J) (b : Lp ℝ 2 μ)
    (hu : ∀ k, (u k, a k) ∈ neumannGraph J) (hv : (v, b) ∈ neumannGraph J)
    (hval : Tendsto (fun k => value J (u k)) atTop (𝓝 (value J v)))
    (hout : Tendsto a atTop (𝓝 b)) : Tendsto u atTop (𝓝 v) := by
  have ht := (resolvent J).continuous.tendsto (value J v + b) |>.comp (hval.add hout)
  simpa only [Function.comp_def, resolvent_graph_input J v b hv,
    resolvent_graph_input J (u _) (a _) (hu _)] using ht

/-- Internal core criterion in the form space. Once a test graph has the
full generator graph as its closure, its recovered test functions are a
form core. The shifted-kernel argument must supply `hgraph` separately. -/
theorem dense_form_of_graph_closure (hinj : Function.Injective (value J))
    (T : Submodule ℝ (Domain J)) (S : Submodule ℝ (Lp ℝ 2 μ × Lp ℝ 2 μ))
    (hgraph : S.topologicalClosure = l2Graph J)
    (htest : ∀ p ∈ S, resolvent J (p.1 + p.2) ∈ T) :
    Dense (T : Set (Domain J)) := by
  let F : (Lp ℝ 2 μ × Lp ℝ 2 μ) →L[ℝ] Domain J :=
    (resolvent J).comp (ContinuousLinearMap.fst ℝ _ _ + ContinuousLinearMap.snd ℝ _ _)
  have hsub : (l2Graph J : Set _) ⊆ F ⁻¹' closure (T : Set (Domain J)) := by
    rw [← hgraph, Submodule.topologicalClosure_coe]
    exact closure_minimal (fun p hp => subset_closure (htest p hp))
      (isClosed_closure.preimage F.continuous)
  have hdom : operatorDomain J ⊆ closure (T : Set (Domain J)) := by
    rintro u ⟨a, ha⟩
    have hp : (value J u, a) ∈ l2Graph J :=
      (mem_l2Graph_iff J _ _).mpr ⟨u, rfl, ha⟩
    have he : F (value J u, a) = u := resolvent_graph_input J u a ha
    exact he ▸ hsub hp
  intro u
  exact (isClosed_closure.closure_subset_iff.mpr hdom) (dense_operatorDomain J hinj u)

end GraphApproximation

end ScalarForm

namespace EuclideanScalarForm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {U : Set E} {μ : Measure E} [IsFiniteMeasure μ]
  (hU : IsOpen U) (hbounded : Bornology.IsBounded U) (hμ : ∀ᵐ x ∂μ, x ∈ U)

/-- See Subsection 3.1 of the paper: the graph equals the existing jet
completion, including both value and gradient. -/
theorem mem_neumannSobolevGraph_iff (f : Lp ℝ 2 μ) (g : Lp E 2 μ) :
    (f, g) ∈ neumannSobolevGraph μ U ↔
      WithLp.toLp 2 (f, g) ∈ ScalarForm.completionSubmodule (smoothJet hU hbounded hμ) := by
  let e := WithLp.homeomorphProd 2 (Lp ℝ 2 μ) (Lp E 2 μ)
  have hcore : {p | ∃ (f : E → ℝ) (hf : MemLp f 2 μ)
      (hg : MemLp (gradient f) 2 μ),
      (∃ V : Set E, IsOpen V ∧ closure U ⊆ V ∧ ContDiffOn ℝ (⊤ : ℕ∞) f V) ∧
      p = (hf.toLp f, hg.toLp (gradient f))} =
      e '' ((smoothJet hU hbounded hμ).range : Set _) := by
    ext p
    constructor
    · rintro ⟨f, hf, hg, hs, rfl⟩
      refine ⟨smoothJet hU hbounded hμ ⟨f, hs⟩, ⟨⟨f, hs⟩, rfl⟩, ?_⟩
      rfl
    · rintro ⟨_, ⟨f, rfl⟩, rfl⟩
      exact ⟨f.val, _, _, f.property, rfl⟩
  change (f, g) ∈ closure _ ↔ WithLp.toLp 2 (f, g) ∈ closure _
  rw [hcore, ← e.image_closure]
  constructor
  · rintro ⟨p, hp, he⟩
    have : p = WithLp.toLp 2 (f, g) := e.injective he
    exact this ▸ hp
  · intro hp
    exact ⟨WithLp.toLp 2 (f, g), hp, rfl⟩

/-- The realization predicate for the value-space energy. Its only
internal input is the closability of the already constructed gradient. -/
theorem isNeumannRealization
    (hinj : Function.Injective (ScalarForm.value (smoothJet hU hbounded hμ))) :
    IsNeumannRealization U (ScalarForm.realization (smoothJet hU hbounded hμ) hinj) := by
  let J := smoothJet hU hbounded hμ
  have hpair (v : ScalarForm.Domain J) :
      (ScalarForm.value J v, ScalarForm.deriv J v) ∈ neumannSobolevGraph μ U := by
    rw [mem_neumannSobolevGraph_iff hU hbounded hμ]
    exact v.property
  have hrecover (f : Lp ℝ 2 μ) (g : Lp E 2 μ)
      (hfg : (f, g) ∈ neumannSobolevGraph μ U) :
      ∃ v : ScalarForm.Domain J, ScalarForm.value J v = f ∧ ScalarForm.deriv J v = g := by
    exact ⟨⟨WithLp.toLp 2 (f, g),
      (mem_neumannSobolevGraph_iff hU hbounded hμ f g).mp hfg⟩, rfl, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro f
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨ScalarForm.deriv J v, hpair v⟩
    · rintro ⟨g, hfg⟩
      obtain ⟨v, hv, _⟩ := hrecover f g hfg
      exact ⟨v, hv⟩
  · intro f g k hfg hfk
    obtain ⟨v, hv, hvg⟩ := hrecover f g hfg
    obtain ⟨w, hw, hwk⟩ := hrecover f k hfk
    exact hvg.symm.trans ((congrArg (ScalarForm.deriv J) (hinj (hv.trans hw.symm))).trans hwk)
  · intro f h g k hfg hhk
    obtain ⟨v, hv, hvg⟩ := hrecover f.val g hfg
    obtain ⟨w, hw, hwk⟩ := hrecover h.val k hhk
    have hf : ScalarForm.valueEquiv J hinj v = f := Subtype.ext hv
    have hh : ScalarForm.valueEquiv J hinj w = h := Subtype.ext hw
    rw [← hf, ← hh, ScalarForm.realization_energy]
    exact congrArg₂ (inner ℝ) hvg hwk

/-- Constants in the original Neumann completion give the exact conservativity predicate after passing to values. -/
theorem isConservativeScalarForm
    (hinj : Function.Injective (ScalarForm.value (smoothJet hU hbounded hμ))) :
    IsConservativeScalarForm (ScalarForm.realization (smoothJet hU hbounded hμ) hinj) := by
  refine ⟨ScalarForm.valueEquiv _ hinj (constant hU hbounded hμ 1),
    value_constant hU hbounded hμ 1, ?_⟩
  rw [ScalarForm.realization_energy]
  exact conservative hU hbounded hμ

end EuclideanScalarForm

namespace IntrinsicScalarCore

/-- Internal a.e.-measurable version of square-density multiplication.
The measured function is never changed: a measurable representative is used
only inside this proof to apply the existing Riesz1 isometry lemma. -/
theorem memLp_squareDensity_mul_ae {α : Type*} [MeasurableSpace α]
    {μ ν : Measure α} {w : α → ℝ} (hw : AEMeasurable w μ)
    (hpos : ∀ᵐ x ∂μ, 0 < w x)
    (hν : ν = μ.withDensity (fun x => ENNReal.ofReal (w x ^ 2)))
    (u : Lp ℝ 2 ν) : MemLp (fun x => w x * u x) 2 μ := by
  have hac : μ ≪ ν := by
    rw [hν]
    exact withDensity_absolutelyContinuous' (hw.pow_const 2).ennreal_ofReal
      (hpos.mono fun x hx => (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hx)).ne')
  have heq : w =ᵐ[μ] hw.mk w := hw.ae_eq_mk
  have hν' : ν = μ.withDensity (fun x => ENNReal.ofReal (hw.mk w x ^ 2)) := by
    rw [hν]
    exact withDensity_congr_ae (heq.mono fun x hx => by dsimp only; rw [hx])
  have hL := (Riesz1.Internal.memLp_squareDensity_mul_iff hw.measurable_mk hν'
    ((Lp.aestronglyMeasurable u).mono_ac hac)).mpr (Lp.memLp u)
  exact hL.ae_eq (heq.symm.mono fun x hx => by simp only [smul_eq_mul, hx])

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {U : Set E} {ρ : Measure E} {V : E → ℝ}

omit [MeasurableSpace E] [BorelSpace E] in
/-- Interior ground-state calculus used in Appendix A.
The generic product rule from Riesz1 applies in any intrinsic Euclidean
chart. There is no particle pair-potential assumption. -/
theorem inverse_groundState_differential (hU : IsOpen U)
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V U) {φ : E → ℝ}
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ U) {x : E} (hx : x ∈ U) :
    inner ℝ (gradient V x)
        (gradient (fun y => Real.exp ((1 / 2 : ℝ) * V y) * φ y) x) -
      Δ (fun y => Real.exp ((1 / 2 : ℝ) * V y) * φ y) x =
    Real.exp ((1 / 2 : ℝ) * V x) *
      (-Δ φ x + (‖gradient V x‖ ^ 2 / 4 - Δ V x / 2) * φ x) := by
  have hg : gradient (fun y => Real.exp ((1 / 2 : ℝ) * V y) * φ y) x =
      Real.exp ((1 / 2 : ℝ) * V x) •
        (gradient φ x + ((1 / 2 : ℝ) * φ x) • gradient V x) := by
    apply ext_inner_right ℝ
    intro v
    rw [inner_gradient_left, real_inner_smul_left, inner_add_left,
      real_inner_smul_left, inner_gradient_left, inner_gradient_left,
      Riesz1.fderiv_exp_mul_apply hU hV hφ (1 / 2) hx]
    ring
  rw [hg, inner_smul_right, inner_add_right, inner_smul_right,
    real_inner_self_eq_norm_sq, Riesz1.laplacian_exp_mul hU hV hφ (1 / 2) hx]
  ring

omit [MeasurableSpace E] [BorelSpace E] in
/-- The intrinsic ground-state potential is smooth in the interior.
The displayed expression is precisely `W_V` of Appendix A. -/
theorem groundState_potential_smooth (hU : IsOpen U)
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V U) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => ‖gradient V x‖ ^ 2 / 4 - Δ V x / 2) U := by
  have hd := hV.fderiv_of_isOpen hU (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) (gradient V) U :=
    (InnerProductSpace.toDual ℝ E).symm.contDiff.comp_contDiffOn hd
  have hdd := hd.fderiv_of_isOpen hU (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
  have hl : ContDiffOn ℝ (⊤ : ℕ∞) (Δ V) U := by
    have hh := ContDiffOn.sum (s := Finset.univ) (fun (i : Fin (Module.finrank ℝ E)) _ =>
      (hdd.clm_apply (contDiffOn_const (c := stdOrthonormalBasis ℝ E i))).clm_apply
        (contDiffOn_const (c := stdOrthonormalBasis ℝ E i)))
    convert hh using 1
    funext x
    simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
      iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact (hg.norm_sq ℝ |>.div_const 4).sub (hl.div_const 2)

/-- The Gibbs certificate includes a positive finite normalizer and
therefore determines a probability, without an extra finiteness premise. -/
theorem probability (hV : IsEuclideanGibbsPotential volume ρ U V) :
    IsProbabilityMeasure ρ := by
  obtain ⟨_, hZ0, hZt, hρ⟩ := hV
  apply isProbabilityMeasure_iff.mpr
  rw [hρ, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  exact ENNReal.inv_mul_cancel hZ0.ne' hZt.ne

/-- The normalized Gibbs law is supported on its stated open domain. -/
theorem supported (hU : IsOpen U) (hV : IsEuclideanGibbsPotential volume ρ U V) :
    ∀ᵐ x ∂ρ, x ∈ U := by
  rw [hV.2.2.2]
  apply Measure.smul_absolutelyContinuous.ae_le
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hU.measurableSet)

/-- The real normalized density, with its interior smoothness and positivity.
No exterior values of the potential are used to assert smoothness. -/
theorem density (hV : IsEuclideanGibbsPotential volume ρ U V) :
    ∃ w : E → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) w U ∧ (∀ x ∈ U, 0 < w x) ∧
      ρ = (volume.restrict U).withDensity (fun x => ENNReal.ofReal (w x)) := by
  let Z := ∫⁻ x in U, ENNReal.ofReal (Real.exp (-V x))
  have hZ : 0 < Z.toReal := ENNReal.toReal_pos hV.2.1.ne' hV.2.2.1.ne
  refine ⟨fun x => Z.toReal⁻¹ * Real.exp (-V x),
    contDiffOn_const.mul hV.1.neg.exp, fun _ _ => mul_pos (inv_pos.mpr hZ) (Real.exp_pos _), ?_⟩
  rw [hV.2.2.2, ← withDensity_smul' _ _ (ENNReal.inv_ne_top.mpr hV.2.1.ne')]
  congr 1
  funext x
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos hZ,
    ENNReal.ofReal_toReal hV.2.2.1.ne]
  rfl

/-- Conversion of a Gibbs integral to intrinsic Euclidean volume. The
normalizer is positive and finite by the certificate. -/
theorem integral_eq (hU : IsOpen U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) (f : E → ℝ) :
    (∫ x, f x ∂ρ) =
      (∫⁻ x in U, ENNReal.ofReal (Real.exp (-V x))).toReal⁻¹ *
        ∫ x in U, Real.exp (-V x) * f x := by
  rw [hV.2.2.2, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul₀
      (hV.1.neg.exp.continuousOn.aemeasurable hU.measurableSet).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul]

/-- Ground-state multiplication sends a weighted L² representative to
Lebesgue L² on the domain, using only the local smoothness in the Gibbs certificate. This does not assume a globally measurable potential. -/
theorem memLp_groundState (hU : IsOpen U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) (u : Lp ℝ 2 ρ) :
    MemLp (fun x => Real.exp ((-1 / 2 : ℝ) * V x) * u x) 2 (volume.restrict U) := by
  let Z := ∫⁻ x in U, ENNReal.ofReal (Real.exp (-V x))
  let ν := (volume.restrict U).withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))
  have hν : ν = Z • ρ := by
    rw [hV.2.2.2, smul_smul, ENNReal.mul_inv_cancel hV.2.1.ne' hV.2.2.1.ne, one_smul]
  have hLu : MemLp (u : E → ℝ) 2 ν := by
    rw [hν]
    exact (Lp.memLp u).smul_measure hV.2.2.1.ne
  have hw : AEMeasurable (fun x => Real.exp ((-1 / 2 : ℝ) * V x)) (volume.restrict U) :=
    (contDiffOn_const.mul hV.1).exp.continuousOn.aemeasurable hU.measurableSet
  have hsq : ν = (volume.restrict U).withDensity
      (fun x => ENNReal.ofReal (Real.exp ((-1 / 2 : ℝ) * V x) ^ 2)) := by
    dsimp only [ν]
    congr 1
    funext x
    rw [sq, ← Real.exp_add]
    congr 2
    ring
  have hac : volume.restrict U ≪ ν := by
    change volume.restrict U ≪ (volume.restrict U).withDensity _
    exact withDensity_absolutelyContinuous'
      (hV.1.neg.exp.continuousOn.aemeasurable hU.measurableSet).ennreal_ofReal
      (Eventually.of_forall fun x => (ENNReal.ofReal_pos.mpr (Real.exp_pos (-V x))).ne')
  have ht := memLp_squareDensity_mul_ae hw
    (Eventually.of_forall fun _ => Real.exp_pos _) hsq (hLu.toLp _)
  have hcoe : (hLu.toLp _ : E → ℝ) =ᵐ[volume.restrict U] (u : E → ℝ) :=
    hac.ae_le hLu.coeFn_toLp
  exact ht.ae_eq (hcoe.mono fun x hx => by dsimp only; rw [hx])

/-- Internal compact-test integration by parts in the intrinsic metric.
Only the test is supported away from the boundary. The other function is
interior smooth and has finite weighted value and gradient norms. -/
theorem compact_integrationByParts_interior (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V)
    {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U)
    {g : E → ℝ} (hgU : ContDiffOn ℝ (⊤ : ℕ∞) g U)
    (hgL : MemLp g 2 ρ ∧ MemLp (gradient g) 2 ρ) :
    (∫ x, inner ℝ (gradient f x) (gradient g x) ∂ρ) =
      ∫ x, (inner ℝ (gradient V x) (gradient f x) - Δ f x) * g x ∂ρ := by
  have := probability hV
  let b := stdOrthonormalBasis ℝ E
  let ψ (i : Fin (Module.finrank ℝ E)) (x : E) := fderiv ℝ f x (b i)
  let q (i : Fin (Module.finrank ℝ E)) (x : E) :=
    -fderiv ℝ (ψ i) x (b i) + ψ i x * fderiv ℝ V x (b i)
  have hψ (i) : ContDiff ℝ (⊤ : ℕ∞) (ψ i) :=
    (hf.fderiv_right (by simp)).clm_apply contDiff_const
  have hψc (i) : HasCompactSupport (ψ i) := hfc.fderiv_apply ℝ (b i)
  have hψU (i) : tsupport (ψ i) ⊆ U := (tsupport_fderiv_apply_subset ℝ (b i)).trans hfU
  have hqc (i) : Continuous (q i) := by
    apply Continuous.add
    · exact (((hψ i).continuous_fderiv (by simp)).clm_apply continuous_const).neg
    · exact Riesz1.WeightedSobolev.continuous_cutoff_mul hU (hψ i).continuous (hψU i)
        ((hV.1.continuousOn_fderiv_of_isOpen hU (by norm_num)).clm_apply continuousOn_const)
  have hqL (i) : MemLp (q i) 2 ρ :=
    Riesz1.WeightedSobolev.memLp_of_continuousOn_closure hB (supported hU hV) (hqc i).continuousOn
  have hψL (i) : MemLp (ψ i) 2 ρ :=
    Riesz1.WeightedSobolev.memLp_of_continuousOn_closure hB (supported hU hV) (hψ i).continuous.continuousOn
  have hgdir (i) : MemLp (fun x => fderiv ℝ g x (b i)) 2 ρ := by
    simpa only [Function.comp_def, innerSL_apply_apply, inner_gradient_right, RCLike.conj_to_real] using
      (innerSL ℝ (b i)).comp_memLp' hgL.2
  have hcoord (i) :
      (∫ x, ψ i x * fderiv ℝ g x (b i) ∂ρ) = ∫ x, q i x * g x ∂ρ := by
    rw [integral_eq hU hV, integral_eq hU hV]
    congr 1
    have he := Riesz1.WeightedSobolev.integral_weighted_fderiv_of_compact_test
      (μ := volume) hU (hψ i) (hψc i) (hψU i) hgU hV.1.neg.exp (b i)
    have hwd (x : E) (hx : x ∈ U) :
        fderiv ℝ (fun y => ψ i y * Real.exp (-V y)) x (b i) =
          Real.exp (-V x) * (-q i x) := by
      have hvd := (hV.1.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
      have hd := ((hψ i).differentiable (by norm_num) x).hasFDerivAt.mul
        hvd.hasFDerivAt.neg.exp
      change HasFDerivAt (fun y => ψ i y * Real.exp (-V y)) _ x at hd
      rw [hd.fderiv]
      dsimp only [q]
      simp only [add_apply, smul_apply,
        neg_apply, Pi.neg_apply, smul_eq_mul]
      ring
    calc
      _ = ∫ x, (ψ i x * Real.exp (-V x)) * fderiv ℝ g x (b i) := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun x hx => by
            rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hψU i h))]
            ring)]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by ring
      _ = -∫ x, g x * fderiv ℝ (fun y => ψ i y * Real.exp (-V y)) x (b i) := he
      _ = ∫ x in U, Real.exp (-V x) * (q i x * g x) := by
        rw [← integral_neg]
        have hdU : tsupport (fun x =>
            fderiv ℝ (fun y => ψ i y * Real.exp (-V y)) x (b i)) ⊆ U :=
          (tsupport_fderiv_apply_subset ℝ (b i)).trans
            (tsupport_mul_subset_left.trans (hψU i))
        rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
          (s := U) (fun x hx => by
            rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hdU h))]
            ring)]
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
        rw [hwd x hx]
        ring
  have hinner (x : E) : inner ℝ (gradient f x) (gradient g x) =
      ∑ i, ψ i x * fderiv ℝ g x (b i) := by
    rw [← b.sum_inner_mul_inner]
    simp only [ψ, inner_gradient_left, inner_gradient_right, RCLike.conj_to_real]
  have hsum (x : E) : ∑ i, q i x = inner ℝ (gradient V x) (gradient f x) - Δ f x := by
    rw [Riesz1.laplacian_eq_sum_fderiv_direction hf b x, ← b.sum_inner_mul_inner]
    simp only [q, ψ, inner_gradient_left, inner_gradient_right, RCLike.conj_to_real,
      Finset.sum_add_distrib, Finset.sum_neg_distrib, mul_comm]
    ring
  simp_rw [hinner]
  rw [integral_finsetSum Finset.univ (f := fun i x => ψ i x * fderiv ℝ g x (b i))
    (fun i _ => (hψL i).integrable_mul (hgdir i))]
  simp_rw [hcoord]
  rw [← integral_finsetSum Finset.univ (f := fun i x => q i x * g x)
    (fun i _ => (hqL i).integrable_mul hgL.1)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by dsimp only; rw [← Finset.sum_mul, hsum]

/-- Compact-test integration by parts for the original Neumann smooth core. -/
theorem compact_integrationByParts (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V)
    {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U)
    (g : EuclideanScalarForm.smoothCore U) :
    (∫ x, inner ℝ (gradient f x) (gradient g.val x) ∂ρ) =
      ∫ x, (inner ℝ (gradient V x) (gradient f x) - Δ f x) * g.val x ∂ρ := by
  have := probability hV
  obtain ⟨O, _, hUO, hg⟩ := g.property
  exact compact_integrationByParts_interior hU hB hV hf hfc hfU
    (hg.mono (subset_closure.trans hUO))
    (Riesz1.WeightedSobolev.memLp_of_smoothNearClosure hB (supported hU hV) g.property)

/-- Shifted-kernel step for Appendix A. Orthogonality to
the differential compact tests implies zero. -/
theorem shift_kernel_of_test_pairings [Nontrivial E] (hU : IsOpen U)
    (hB : Bornology.IsBounded U) (hV : IsEuclideanGibbsPotential volume ρ U V)
    {C lam : ℝ} (hlam : C + 1 < lam)
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹ ^ 2 - C ≤
      ‖gradient V x‖ ^ 2 / 4 - Δ V x / 2)
    (u : Lp ℝ 2 ρ)
    (hpair : ∀ f : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → tsupport f ⊆ U →
      (∫ x, (inner ℝ (gradient V x) (gradient f x) - Δ f x + lam * f x) * u x ∂ρ) = 0) :
    u = 0 := by
  let v : E → ℝ := fun x => Real.exp ((-1 / 2 : ℝ) * V x) * u x
  let W : E → ℝ := fun x => ‖gradient V x‖ ^ 2 / 4 - Δ V x / 2
  have hvL : MemLp v 2 (volume.restrict U) := memLp_groundState hU hV u
  have hvloc : Riesz1.LocallySquareIntegrableOn U v := by
    intro K _ hKU
    exact hvL.mono_measure (Measure.restrict_mono_set volume hKU)
  have hvi : LocallyIntegrableOn v U := hvloc.locallyIntegrableOn hU
  have hWs : ContDiffOn ℝ (⊤ : ℕ∞) W U := groundState_potential_smooth hU hV.1
  have hWvi : LocallyIntegrableOn (fun x => (W x + lam) • v x) U :=
    (hvloc.smul_continuousOn (hWs.continuousOn.add continuousOn_const)).locallyIntegrableOn hU
  have hsol : Riesz1.IsDistributionalSchrodingerSolution U W lam v := by
    refine ⟨hvi, hWvi, fun ψ hψ hψc hψU => ?_⟩
    let f : E → ℝ := fun x => ψ x * Real.exp ((1 / 2 : ℝ) * V x)
    have hfs : ContDiff ℝ (⊤ : ℕ∞) f :=
      Riesz1.WeightedSobolev.contDiff_cutoff_mul hU hψ hψU (contDiffOn_const.mul hV.1).exp
    have hfc : HasCompactSupport f := hψc.mul_right
    have hfU : tsupport f ⊆ U := tsupport_mul_subset_left.trans hψU
    have hfexp : f = fun x => Real.exp ((1 / 2 : ℝ) * V x) * ψ x := by
      funext x
      exact mul_comm _ _
    have hdiff (x : E) (hx : x ∈ U) :
        inner ℝ (gradient V x) (gradient f x) - Δ f x + lam * f x =
          Real.exp ((1 / 2 : ℝ) * V x) * (-Δ ψ x + (W x + lam) * ψ x) := by
      rw [hfexp, inverse_groundState_differential hU hV.1 hψ.contDiffOn hx]
      dsimp only [W]
      ring
    have hz := hpair f hfs hfc hfU
    rw [integral_eq hU hV] at hz
    have hnorm : (∫⁻ x in U, ENNReal.ofReal (Real.exp (-V x))).toReal⁻¹ ≠ 0 :=
      inv_ne_zero (ENNReal.toReal_pos hV.2.1.ne' hV.2.2.1.ne).ne'
    have hz' : (∫ x in U, (-Δ ψ x + (W x + lam) * ψ x) * v x) = 0 := by
      have he := (mul_eq_zero.mp hz).resolve_left hnorm
      rw [← he]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
      dsimp only [v]
      rw [hdiff x hx]
      have hexp : Real.exp (-V x) * Real.exp ((1 / 2 : ℝ) * V x) =
          Real.exp ((-1 / 2 : ℝ) * V x) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [← hexp]
      ring
    have hψout : ∀ x ∉ U, ψ x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport (fun h => hx (hψU h))
    have hΔout : ∀ x ∉ U, Δ ψ x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport
        (fun h => hx (hψU (Riesz1.tsupport_laplacian_subset ψ h)))
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [hψout x hx, hΔout x hx]; ring)] at hz'
    have hi := Riesz1.integrable_smul_of_compact_interior hWvi hψ.continuous hψc hψU
    have hj := Riesz1.integrable_smul_of_compact_interior hvi
      (Riesz1.contDiff_laplacian hψ).continuous (Riesz1.hasCompactSupport_laplacian hψc)
      ((Riesz1.tsupport_laplacian_subset ψ).trans hψU)
    have heq : (fun x => (-Δ ψ x + (W x + lam) * ψ x) * v x) =
        (fun x => ψ x • ((W x + lam) • v x) - Δ ψ x • v x) := by
      funext x
      simp only [smul_eq_mul]
      ring
    rw [heq, integral_sub hi hj] at hz'
    exact sub_eq_zero.mp hz'
  have hv0 := collisionBarrierKernel hU hB hWs hlam hbar hvL hsol
  have hu0 : (u : E → ℝ) =ᵐ[volume.restrict U] 0 := by
    filter_upwards [hv0] with x hx
    exact (mul_eq_zero.mp hx).resolve_left (Real.exp_ne_zero _)
  have hac : ρ ≪ volume.restrict U := by
    rw [hV.2.2.2]
    exact Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
  apply Lp.ext
  filter_upwards [hac.ae_le hu0, Lp.coeFn_zero ℝ 2 ρ] with x hx hz
  exact hx.trans hz.symm

/-- The original intrinsic smooth-jet map, now supplied with the finiteness
and support certificates proved from the Gibbs data. -/
def jet (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) :
    EuclideanScalarForm.smoothCore U →ₗ[ℝ] ScalarForm.Jet ρ E := by
  have := probability hV
  exact EuclideanScalarForm.smoothJet hU hB (supported hU hV)

/-- Local integration by parts proves gradient closability for the actual
Gibbs potential. This is the first step of Appendix A. -/
theorem value_injective (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) :
    Function.Injective (ScalarForm.value (jet hU hB hV)) := by
  have := probability hV
  obtain ⟨w, hws, hwp, hw⟩ := density hV
  exact EuclideanScalarForm.value_injective_of_smooth_density hU hB
    (supported hU hV) volume w hws hwp hw

/-- The form domain of the intrinsic Gibbs law is dense in L². -/
theorem value_dense (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) :
    DenseRange (ScalarForm.value (jet hU hB hV)) := by
  have := probability hV
  exact EuclideanScalarForm.denseRange_value hU hB (supported hU hV)

/-- The scalar generator on its full intrinsic Neumann domain. The existing
variational construction has no value assigned outside its operator domain. -/
def operator (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) : Lp ℝ 2 ρ →ₗ.[ℝ] Lp ℝ 2 ρ :=
  ScalarForm.l2Operator (jet hU hB hV) (value_dense hU hB hV)

/-- The existing jet energy as scalar form data, on exactly its L²
value subspace (Subsection 3.1). -/
def form (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) : ScalarFormData ρ :=
  ScalarForm.realization (jet hU hB hV) (value_injective hU hB hV)

/-- See Appendix A of the paper, self-adjointness part, valid even without
the strict-curvature or collision-barrier hypotheses. -/
theorem selfAdjoint (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) :
    IsSelfAdjoint (operator hU hB hV) :=
  ScalarForm.l2Operator_selfAdjoint _ _

/-- See Appendix A of the paper, nonnegativity part. -/
theorem nonnegative (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) {f g : Lp ℝ 2 ρ}
    (hfg : (f, g) ∈ (operator hU hB hV).graph) : 0 ≤ inner ℝ g f :=
  ScalarForm.l2Operator_nonneg _ _ hfg

/-- The construction realizes the whole Neumann graph. -/
theorem realization (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) :
    IsNeumannRealization U (form hU hB hV) := by
  have := probability hV
  exact EuclideanScalarForm.isNeumannRealization hU hB (supported hU hV)
    (value_injective hU hB hV)

/-- See Appendix A of the paper, conservativity part, for the exact scalar form data rather than a separate Sobolev encoding. -/
theorem conservative (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) :
    IsConservativeScalarForm (form hU hB hV) := by
  have := probability hV
  exact EuclideanScalarForm.isConservativeScalarForm hU hB (supported hU hV)
    (value_injective hU hB hV)

/-- See Subsection 3.1 of the paper: the generator graph is exactly the weak equation
for the scalar form, with every test in its full form domain. -/
theorem graph_iff (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) (f a : Lp ℝ 2 ρ) :
    (f, a) ∈ (operator hU hB hV).graph ↔
      ∃ hf : f ∈ (form hU hB hV).1, ∀ h : (form hU hB hV).1,
        (form hU hB hV).2 ⟨f, hf⟩ h = inner ℝ a h.val := by
  let J := jet hU hB hV
  let e := ScalarForm.valueEquiv J (value_injective hU hB hV)
  change (f, a) ∈ (ScalarForm.l2Operator J (value_dense hU hB hV)).graph ↔ _
  rw [ScalarForm.l2Operator_graph, ScalarForm.mem_l2Graph_iff]
  constructor
  · rintro ⟨u, hu, he⟩
    refine ⟨⟨u, hu⟩, fun h => ?_⟩
    have hf : e u = (⟨f, ⟨u, hu⟩⟩ : (form hU hB hV).1) := Subtype.ext hu
    have hh : e (e.symm h) = h := e.apply_symm_apply h
    rw [← hf, ← hh]
    change ScalarForm.energy J (e.symm (e u)) (e.symm (e (e.symm h))) = _
    simpa only [LinearEquiv.symm_apply_apply, e, ScalarForm.valueEquiv,
      LinearEquiv.ofInjective_apply, ContinuousLinearMap.coe_coe] using he (e.symm h)
  · rintro ⟨hf, he⟩
    let u := e.symm ⟨f, hf⟩
    have hu : ScalarForm.value J u = f := congrArg Subtype.val (e.apply_symm_apply ⟨f, hf⟩)
    refine ⟨u, hu, fun h => ?_⟩
    have ht := he (e h)
    have heq : e u = (⟨f, hf⟩ : (form hU hB hV).1) := e.apply_symm_apply _
    rw [← heq] at ht
    change ScalarForm.energy J (e.symm (e u)) (e.symm (e h)) = _ at ht
    simpa only [LinearEquiv.symm_apply_apply, e, ScalarForm.valueEquiv,
      LinearEquiv.ofInjective_apply, ContinuousLinearMap.coe_coe] using ht

/-- See Appendix A of the paper, the operator meaning of conservativity:
the actual constant-one L² class belongs to the graph with output zero. -/
theorem kills_one (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) :
    ∃ one : Lp ℝ 2 ρ, (∀ᵐ x ∂ρ, one x = 1) ∧
      (one, 0) ∈ (operator hU hB hV).graph := by
  have := probability hV
  let J := jet hU hB hV
  let u := EuclideanScalarForm.constant hU hB (supported hU hV) 1
  refine ⟨ScalarForm.value J u,
    EuclideanScalarForm.value_constant hU hB (supported hU hV) 1, ?_⟩
  rw [operator, ScalarForm.l2Operator_graph, ScalarForm.mem_l2Graph_iff]
  refine ⟨u, rfl, fun h => ?_⟩
  change inner ℝ (ScalarForm.deriv J u) _ = _
  rw [show ScalarForm.deriv J u = 0 from
    EuclideanScalarForm.deriv_constant hU hB (supported hU hV) 1,
    inner_zero_left, inner_zero_left]

/-- The actual compact smooth tests, as a subspace of the existing
Neumann smooth functions. No new value or gradient encoding is introduced. -/
def compactTests (U : Set E) : Submodule ℝ (EuclideanScalarForm.smoothCore U) where
  carrier := {f | ContDiff ℝ (⊤ : ℕ∞) f.val ∧ HasCompactSupport f.val ∧ tsupport f.val ⊆ U}
  zero_mem' := by
    change ContDiff ℝ (⊤ : ℕ∞) (0 : E → ℝ) ∧ HasCompactSupport (0 : E → ℝ) ∧
      tsupport (0 : E → ℝ) ⊆ U
    exact ⟨contDiff_const, by simp [HasCompactSupport], by simp⟩
  add_mem' := by
    intro f g hf hg
    exact ⟨hf.1.add hg.1, hf.2.1.add hg.2.1,
      (tsupport_add _ _).trans (union_subset hf.2.2 hg.2.2)⟩
  smul_mem' := by
    intro a f hf
    exact ⟨hf.1.const_smul a, hf.2.1.smul_left,
      (tsupport_smul_subset_right (fun _ : E => a) f.val).trans hf.2.2⟩

/-- The differential expression on a compact test is in weighted L².
This uses local smoothness at the support, not bounds on the potential
or its derivatives at collision faces. -/
theorem memLp_compact_langevin (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) {f : E → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfU : tsupport f ⊆ U) :
    MemLp (fun x => inner ℝ (gradient V x) (gradient f x) - Δ f x) 2 ρ := by
  have := probability hV
  have hgV : ContDiffOn ℝ (⊤ : ℕ∞) (gradient V) U :=
    (InnerProductSpace.toDual ℝ E).symm.contDiff.comp_contDiffOn
      (hV.1.fderiv_of_isOpen hU (by simp))
  have hgf : ContDiff ℝ (⊤ : ℕ∞) (gradient f) :=
    (InnerProductSpace.toDual ℝ E).symm.contDiff.comp (hf.fderiv_right (by simp))
  have hcont : Continuous (fun x => inner ℝ (gradient V x) (gradient f x) - Δ f x) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ U
    · exact ((hgV.continuousOn.continuousAt (hU.mem_nhds hx)).inner hgf.continuous.continuousAt).sub
        (Riesz1.contDiff_laplacian hf).continuous.continuousAt
    · have he : f =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hfU h))
      apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [he.eventuallyEq_nhds] with y hy
      rw [hy.gradient_eq, (InnerProductSpace.laplacian_congr_nhds hy).eq_of_nhds]
      have hg0 : gradient (0 : E → ℝ) y = 0 := gradient_const y (0 : ℝ)
      have hl0 : Δ (0 : E → ℝ) y = 0 :=
        congrFun (InnerProductSpace.laplacian_const (c := (0 : ℝ))) y
      rw [hg0, hl0, inner_zero_right, sub_self]
  exact Riesz1.WeightedSobolev.memLp_of_continuousOn_closure hB (supported hU hV) hcont.continuousOn

/-- Every compact smooth test lies in the full Neumann graph, with its
classical differential output. This is a proved domain inclusion, not an
extra hypothesis on the operator-core statement. -/
theorem compact_mem_graph (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) (f : compactTests U) :
    ∃ a : Lp ℝ 2 ρ,
      (ScalarForm.ofCore (jet hU hB hV) f.val, a) ∈ ScalarForm.neumannGraph (jet hU hB hV) ∧
      (∀ᵐ x ∂ρ, a x = inner ℝ (gradient V x) (gradient f.val.val x) - Δ f.val.val x) := by
  have := probability hV
  let J := jet hU hB hV
  let A : E → ℝ := fun x => inner ℝ (gradient V x) (gradient f.val.val x) - Δ f.val.val x
  have hA : MemLp A 2 ρ := memLp_compact_langevin hU hB hV f.property.1 f.property.2.2
  let a := hA.toLp A
  have hcore (g : EuclideanScalarForm.smoothCore U) :
      inner ℝ (ScalarForm.deriv J (ScalarForm.ofCore J g))
        (ScalarForm.deriv J (ScalarForm.ofCore J f.val)) =
        inner ℝ (ScalarForm.value J (ScalarForm.ofCore J g)) a := by
    rw [L2.inner_def, L2.inner_def]
    calc
      _ = ∫ x, inner ℝ (gradient f.val.val x) (gradient g.val x) ∂ρ := by
        apply integral_congr_ae
        filter_upwards [(Riesz1.WeightedSobolev.memLp_of_smoothNearClosure hB (supported hU hV)
          g.property).2.coeFn_toLp,
          (Riesz1.WeightedSobolev.memLp_of_smoothNearClosure hB (supported hU hV)
            f.val.property).2.coeFn_toLp] with x hx hy
        change ScalarForm.deriv J (ScalarForm.ofCore J g) x = gradient g.val x at hx
        change ScalarForm.deriv J (ScalarForm.ofCore J f.val) x = gradient f.val.val x at hy
        rw [hx, hy, real_inner_comm]
      _ = ∫ x, A x * g.val x ∂ρ :=
        compact_integrationByParts hU hB hV f.property.1 f.property.2.1 f.property.2.2 g
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [(Riesz1.WeightedSobolev.memLp_of_smoothNearClosure hB (supported hU hV)
          g.property).1.coeFn_toLp, hA.coeFn_toLp] with x hx hy
        change ScalarForm.value J (ScalarForm.ofCore J g) x = g.val x at hx
        change a x = A x at hy
        rw [hx, hy, Real.inner_apply, mul_comm]
  refine ⟨a, fun g => ?_, hA.coeFn_toLp⟩
  change inner ℝ (ScalarForm.deriv J (ScalarForm.ofCore J f.val)) (ScalarForm.deriv J g) = _
  rw [real_inner_comm, ScalarForm.pairing_of_core J _ a hcore, real_inner_comm]

/-- Compact tests inside the existing Hilbert form domain. -/
def compactFormDomain (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) : Submodule ℝ (ScalarForm.Domain (jet hU hB hV)) :=
  (compactTests U).map (ScalarForm.ofCore (jet hU hB hV))

/-- Their actual L² value classes. This is the operator-core subspace. -/
def compactValueDomain (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) : Submodule ℝ (Lp ℝ 2 ρ) :=
  (compactFormDomain hU hB hV).map (ScalarForm.value (jet hU hB hV)).toLinearMap

/-- The generator restricted to the compact smooth test subspace. -/
def testOperator (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) : Lp ℝ 2 ρ →ₗ.[ℝ] Lp ℝ 2 ρ :=
  (operator hU hB hV).domRestrict (compactValueDomain hU hB hV)

/-- The test graph is the full variational graph with a compact test input. -/
theorem mem_testOperator_graph_iff (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) (p : Lp ℝ 2 ρ × Lp ℝ 2 ρ) :
    p ∈ (testOperator hU hB hV).graph ↔
      p ∈ (operator hU hB hV).graph ∧ p.1 ∈ compactValueDomain hU hB hV := by
  constructor
  · intro hp
    refine ⟨LinearPMap.le_graph_of_le LinearPMap.domRestrict_le hp, ?_⟩
    obtain ⟨x, hx, _⟩ := (LinearPMap.mem_graph_iff _).mp hp
    exact hx ▸ x.property.1
  · rintro ⟨hp, hT⟩
    obtain ⟨x, hx, hxa⟩ := (LinearPMap.mem_graph_iff _).mp hp
    refine (LinearPMap.mem_graph_iff _).mpr ⟨⟨x.val, hx.symm ▸ hT, x.property⟩, hx, ?_⟩
    exact (LinearPMap.domRestrict_apply rfl).trans hxa

/-- Compact tests are contained in the operator domain, before any
barrier or curvature condition is imposed. -/
theorem compactValueDomain_le (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) :
    compactValueDomain hU hB hV ≤ (operator hU hB hV).domain := by
  rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
  obtain ⟨a, ha, _⟩ := compact_mem_graph hU hB hV ⟨f, hf⟩
  apply LinearPMap.mem_domain_of_mem_graph (y := a)
  rw [operator, ScalarForm.l2Operator_graph, ScalarForm.mem_l2Graph_iff]
  exact ⟨ScalarForm.ofCore _ f, rfl, ha⟩

/-- See Appendix A of the paper, the essential operator-core step. The
closure equality is for the actual variational Neumann operator. -/
theorem test_graph_closure [Nontrivial E] (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) {C : ℝ} (hC : 0 ≤ C)
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹ ^ 2 - C ≤
      ‖gradient V x‖ ^ 2 / 4 - Δ V x / 2) :
    (testOperator hU hB hV).graph.topologicalClosure = (operator hU hB hV).graph := by
  have := probability hV
  let J := jet hU hB hV
  apply Riesz1.Internal.graph_closure_eq_of_shift_kernel _ _ (selfAdjoint hU hB hV).isClosed
    (LinearPMap.le_graph_of_le LinearPMap.domRestrict_le)
    (fun p hp => nonnegative hU hB hV hp) (lam := C + 2) (by linarith)
  intro u hu
  apply shift_kernel_of_test_pairings hU hB hV (C := C) (lam := C + 2) (by linarith) hbar u
  intro f hf hfc hfU
  let c : EuclideanScalarForm.smoothCore U :=
    ⟨f, univ, isOpen_univ, subset_univ _, hf.contDiffOn⟩
  obtain ⟨a, ha, hae⟩ := compact_mem_graph hU hB hV (⟨c, hf, hfc, hfU⟩ : compactTests U)
  have hp : (ScalarForm.value J (ScalarForm.ofCore J c), a) ∈
      (testOperator hU hB hV).graph := by
    apply (mem_testOperator_graph_iff hU hB hV _).mpr
    constructor
    · rw [operator, ScalarForm.l2Operator_graph, ScalarForm.mem_l2Graph_iff]
      exact ⟨ScalarForm.ofCore J c, rfl, ha⟩
    · exact ⟨_, ⟨c, ⟨hf, hfc, hfU⟩, rfl⟩, rfl⟩
  have hz := hu _ hp
  change inner ℝ (a + (C + 2) • ScalarForm.value J (ScalarForm.ofCore J c)) u = 0 at hz
  rw [L2.inner_def] at hz
  rw [← hz]
  apply integral_congr_ae
  filter_upwards [hae, Lp.coeFn_add a ((C + 2) • ScalarForm.value J (ScalarForm.ofCore J c)),
    Lp.coeFn_smul (C + 2) (ScalarForm.value J (ScalarForm.ofCore J c)),
    (Riesz1.WeightedSobolev.memLp_of_smoothNearClosure hB (supported hU hV) c.property).1.coeFn_toLp]
    with x hx hadd hsmul hval
  change ScalarForm.value J (ScalarForm.ofCore J c) x = f x at hval
  rw [hadd, Pi.add_apply, hsmul, Pi.smul_apply, smul_eq_mul, hval, hx, Real.inner_apply]

/-- See Appendix A of the paper: compact smooth functions form an operator
core. Strict curvature and polytope geometry can be omitted for this part. -/
theorem hasCore [Nontrivial E] (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) {C : ℝ} (hC : 0 ≤ C)
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹ ^ 2 - C ≤
      ‖gradient V x‖ ^ 2 / 4 - Δ V x / 2) :
    (operator hU hB hV).HasCore (compactValueDomain hU hB hV) := by
  refine ⟨compactValueDomain_le hU hB hV, ?_⟩
  have hclose : (testOperator hU hB hV).IsClosable :=
    (selfAdjoint hU hB hV).isClosed.isClosable.leIsClosable LinearPMap.domRestrict_le
  apply LinearPMap.eq_of_eq_graph
  change (testOperator hU hB hV).closure.graph = _
  rw [← hclose.graph_closure_eq_closure_graph, test_graph_closure hU hB hV hC hbar]

/-- See Appendix A of the paper: graph approximation also gives a form
core, in the Hilbert norm of the existing intrinsic Sobolev space. -/
theorem dense_compactFormDomain [Nontrivial E] (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) {C : ℝ} (hC : 0 ≤ C)
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹ ^ 2 - C ≤
      ‖gradient V x‖ ^ 2 / 4 - Δ V x / 2) :
    Dense (compactFormDomain hU hB hV : Set (ScalarForm.Domain (jet hU hB hV))) := by
  let J := jet hU hB hV
  apply ScalarForm.dense_form_of_graph_closure J (value_injective hU hB hV)
    _ (testOperator hU hB hV).graph
  · rw [test_graph_closure hU hB hV hC hbar, operator, ScalarForm.l2Operator_graph]
  · intro p hp
    obtain ⟨hpa, v, hv, he⟩ := (mem_testOperator_graph_iff hU hB hV p).mp hp
    rw [operator, ScalarForm.l2Operator_graph, ScalarForm.mem_l2Graph_iff] at hpa
    obtain ⟨u, hu, hua⟩ := hpa
    have huv : u = v := value_injective hU hB hV (hu.trans he.symm)
    have hr : ScalarForm.resolvent J (p.1 + p.2) = u := by
      rw [← hu]
      exact ScalarForm.resolvent_graph_input J u p.2 hua
    rw [hr, huv]
    exact hv

/-- All finite-norm interior smooth functions, for the alternate core convention
in Appendix A. Values and gradients still use the same L² jets. -/
def interiorCore (hU : IsOpen U) (hρ : ∀ᵐ x ∂ρ, x ∈ U) : Submodule ℝ (E → ℝ) where
  carrier := {f | ContDiffOn ℝ (⊤ : ℕ∞) f U ∧ MemLp f 2 ρ ∧ MemLp (gradient f) 2 ρ}
  zero_mem' := by
    have hg : gradient (0 : E → ℝ) = 0 := funext fun x => gradient_const x 0
    exact ⟨contDiffOn_const, MemLp.zero, hg.symm ▸ (MemLp.zero : MemLp (0 : E → E) 2 ρ)⟩
  add_mem' := by
    intro f g hf hg
    refine ⟨hf.1.add hg.1, hf.2.1.add hg.2.1, (hf.2.2.add hg.2.2).ae_eq ?_⟩
    filter_upwards [hρ] with x hx
    have hfd := (hf.1.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
    have hgd := (hg.1.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
    simp only [gradient, fderiv_add hfd hgd, map_add, Pi.add_apply]
  smul_mem' := by
    intro a f hf
    refine ⟨hf.1.const_smul a, hf.2.1.const_smul a, (hf.2.2.const_smul a).ae_eq ?_⟩
    filter_upwards [hρ] with x hx
    have hfd := (hf.1.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
    simp only [gradient, fderiv_const_smul hfd, map_smul, Pi.smul_apply]

/-- The alternate smooth family mapped to the original ambient jet space. -/
def interiorJet (hU : IsOpen U) (hρ : ∀ᵐ x ∂ρ, x ∈ U) :
    interiorCore hU hρ →ₗ[ℝ] ScalarForm.Jet ρ E where
  toFun f := WithLp.toLp 2 (f.property.2.1.toLp f.val,
    f.property.2.2.toLp (gradient f.val))
  map_add' f g := by
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext
    · exact MemLp.toLp_add f.property.2.1 g.property.2.1
    · have he : gradient (f.val + g.val) =ᵐ[ρ] gradient f.val + gradient g.val := by
        filter_upwards [hρ] with x hx
        have hfd := (f.property.1.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
        have hgd := (g.property.1.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
        simp only [gradient, fderiv_add hfd hgd, map_add]
        rfl
      exact (MemLp.toLp_congr (f + g).property.2.2
        (f.property.2.2.add g.property.2.2) he).trans
          (MemLp.toLp_add f.property.2.2 g.property.2.2)
  map_smul' a f := by
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext
    · exact MemLp.toLp_const_smul a f.property.2.1
    · have he : gradient (a • f.val) =ᵐ[ρ] a • gradient f.val := by
        filter_upwards [hρ] with x hx
        have hfd := (f.property.1.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
        simp only [gradient, fderiv_const_smul hfd, map_smul]
        rfl
      exact (MemLp.toLp_congr (a • f).property.2.2
        (f.property.2.2.const_smul a) he).trans (MemLp.toLp_const_smul a f.property.2.2)

/-- Coordinate integration by parts against every finite-energy interior
smooth function. This supplies closability for the alternate convention. -/
theorem interior_directional_pairing (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V)
    {ψ : E → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U) (v : E) :
    ∃ q : E → ℝ, MemLp q 2 ρ ∧ ∀ f : interiorCore hU (supported hU hV),
      (∫ x, ψ x * inner ℝ v (gradient f.val x) ∂ρ) = ∫ x, f.val x * q x ∂ρ := by
  have := probability hV
  let q : E → ℝ := fun x => -fderiv ℝ ψ x v + ψ x * fderiv ℝ V x v
  have hqc : Continuous q :=
    (((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const).neg).add
      (Riesz1.WeightedSobolev.continuous_cutoff_mul hU hψ.continuous hψU
        ((hV.1.continuousOn_fderiv_of_isOpen hU (by norm_num)).clm_apply continuousOn_const))
  refine ⟨q, Riesz1.WeightedSobolev.memLp_of_continuousOn_closure hB
    (supported hU hV) hqc.continuousOn, fun f => ?_⟩
  have he := Riesz1.WeightedSobolev.integral_weighted_fderiv_of_compact_test
    (μ := volume) hU hψ hψc hψU f.property.1 hV.1.neg.exp v
  have hd (x : E) (hx : x ∈ U) :
      fderiv ℝ (fun y => ψ y * Real.exp (-V y)) x v = -Real.exp (-V x) * q x := by
    have hvd := (hV.1.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
    have hder := ((hψ.differentiable (by norm_num) x).hasFDerivAt).mul hvd.hasFDerivAt.neg.exp
    change HasFDerivAt (fun y => ψ y * Real.exp (-V y)) _ x at hder
    rw [hder.fderiv]
    simp only [add_apply, smul_apply, neg_apply, Pi.neg_apply, smul_eq_mul, q]
    ring
  rw [integral_eq hU hV, integral_eq hU hV]
  congr 1
  calc
    _ = ∫ x, (ψ x * Real.exp (-V x)) * fderiv ℝ f.val x v := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hψU h))]; ring)]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp only; rw [inner_gradient_right]; simp only [RCLike.conj_to_real]; ring
    _ = -∫ x, f.val x * fderiv ℝ (fun y => ψ y * Real.exp (-V y)) x v := he
    _ = _ := by
      rw [← integral_neg]
      have hs : tsupport (fun x => fderiv ℝ (fun y => ψ y * Real.exp (-V y)) x v) ⊆ U :=
        (tsupport_fderiv_apply_subset ℝ v).trans (tsupport_mul_subset_left.trans hψU)
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := U) (fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))]; ring)]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
      rw [hd x hx]
      ring

/-- Local weighted integration by parts makes the larger smooth completion
inject into L², with no barrier assumption. -/
theorem interior_value_injective (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) :
    Function.Injective (ScalarForm.value (interiorJet hU (supported hU hV))) := by
  have := probability hV
  let J := interiorJet hU (supported hU hV)
  apply ScalarForm.value_injective_of_chart_pairings J id MeasurableEmbedding.id U hU (supported hU hV)
  intro ψ hψ hψc hψU v
  obtain ⟨q, hq, he⟩ := interior_directional_pairing hU hB hV hψ hψc hψU v
  refine ⟨hq.toLp q, fun f => ?_⟩
  rw [L2.inner_def]
  calc
    _ = ∫ x, ψ x * inner ℝ v (gradient f.val x) ∂ρ := by
      apply integral_congr_ae
      filter_upwards [f.property.2.2.coeFn_toLp] with x hx
      change ScalarForm.deriv J (ScalarForm.ofCore J f) x = gradient f.val x at hx
      simp only [id_eq, hx]
    _ = _ := he f
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [f.property.2.1.coeFn_toLp, hq.coeFn_toLp] with x hx hy
      change ScalarForm.value J (ScalarForm.ofCore J f) x = f.val x at hx
      rw [hx, hy, Real.inner_apply]

/-- Inclusion of the original Neumann jet completion in the completion
using finite-energy interior smooth functions. -/
theorem completion_le_interior (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) :
    ScalarForm.completionSubmodule (jet hU hB hV) ≤
      ScalarForm.completionSubmodule (interiorJet hU (supported hU hV)) := by
  have := probability hV
  apply Submodule.topologicalClosure_mono
  rintro _ ⟨f, rfl⟩
  have hfU : ContDiffOn ℝ (⊤ : ℕ∞) f.val U := by
    obtain ⟨O, _, hUO, hf⟩ := f.property
    exact hf.mono (subset_closure.trans hUO)
  have hfL := Riesz1.WeightedSobolev.memLp_of_smoothNearClosure hB (supported hU hV) f.property
  exact ⟨⟨f.val, hfU, hfL⟩, rfl⟩

/-- Compact differential tests belong to the alternate variational graph. -/
theorem compact_mem_interior_graph (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) (f : compactTests U) :
    ∃ a : Lp ℝ 2 ρ,
      (ScalarForm.value (jet hU hB hV) (ScalarForm.ofCore (jet hU hB hV) f.val), a) ∈
        ScalarForm.l2Graph (interiorJet hU (supported hU hV)) ∧
      (ScalarForm.ofCore (jet hU hB hV) f.val, a) ∈ ScalarForm.neumannGraph (jet hU hB hV) := by
  have := probability hV
  let J := jet hU hB hV
  let K := interiorJet hU (supported hU hV)
  obtain ⟨a, ha, hae⟩ := compact_mem_graph hU hB hV f
  let u : ScalarForm.Domain K := ⟨(ScalarForm.ofCore J f.val).val,
    completion_le_interior hU hB hV (ScalarForm.ofCore J f.val).property⟩
  refine ⟨a, (ScalarForm.mem_l2Graph_iff K _ _).mpr ⟨u, rfl, ?_⟩, ha⟩
  have he (g : interiorCore hU (supported hU hV)) :
      inner ℝ (ScalarForm.deriv K (ScalarForm.ofCore K g)) (ScalarForm.deriv K u) =
        inner ℝ (ScalarForm.value K (ScalarForm.ofCore K g)) a := by
    rw [L2.inner_def, L2.inner_def]
    calc
      _ = ∫ x, inner ℝ (gradient f.val.val x) (gradient g.val x) ∂ρ := by
        apply integral_congr_ae
        filter_upwards [g.property.2.2.coeFn_toLp,
          (Riesz1.WeightedSobolev.memLp_of_smoothNearClosure hB (supported hU hV)
            f.val.property).2.coeFn_toLp] with x hx hy
        change ScalarForm.deriv K (ScalarForm.ofCore K g) x = gradient g.val x at hx
        change ScalarForm.deriv K u x = gradient f.val.val x at hy
        rw [hx, hy, real_inner_comm]
      _ = ∫ x, (inner ℝ (gradient V x) (gradient f.val.val x) - Δ f.val.val x) * g.val x ∂ρ :=
        compact_integrationByParts_interior hU hB hV f.property.1 f.property.2.1
          f.property.2.2 g.property.1 g.property.2
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [g.property.2.1.coeFn_toLp, hae] with x hx hy
        change ScalarForm.value K (ScalarForm.ofCore K g) x = g.val x at hx
        rw [hx, hy, Real.inner_apply, mul_comm]
  intro g
  change inner ℝ (ScalarForm.deriv K u) (ScalarForm.deriv K g) = _
  rw [real_inner_comm, ScalarForm.pairing_of_core K _ a he, real_inner_comm]

/-- The two smooth conventions have the same generator graph: both are
symmetric closed extensions of the compact test operator core. -/
theorem interior_l2Graph_eq [Nontrivial E] (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) {C : ℝ} (hC : 0 ≤ C)
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹ ^ 2 - C ≤
      ‖gradient V x‖ ^ 2 / 4 - Δ V x / 2) :
    ScalarForm.l2Graph (interiorJet hU (supported hU hV)) = ScalarForm.l2Graph (jet hU hB hV) := by
  let J := jet hU hB hV
  let K := interiorJet hU (supported hU hV)
  have hsub : ScalarForm.l2Graph J ≤ ScalarForm.l2Graph K := by
    rw [← ScalarForm.l2Operator_graph J (value_dense hU hB hV)]
    change (operator hU hB hV).graph ≤ _
    rw [← test_graph_closure hU hB hV hC hbar]
    apply Submodule.topologicalClosure_minimal _ ?_ (ScalarForm.isClosed_l2Graph K)
    intro p hp
    obtain ⟨_, v, ⟨f, hf, rfl⟩, hv⟩ := (mem_testOperator_graph_iff hU hB hV p).mp hp
    obtain ⟨a, ha, hJa⟩ := compact_mem_interior_graph hU hB hV ⟨f, hf⟩
    have hpa : (p.1, a) ∈ (operator hU hB hV).graph := by
      rw [operator, ScalarForm.l2Operator_graph, ScalarForm.mem_l2Graph_iff]
      exact ⟨ScalarForm.ofCore J f, hv, hJa⟩
    have hp' := (mem_testOperator_graph_iff hU hB hV p).mp hp |>.1
    have hea : a = p.2 := by
      obtain ⟨x, hx, hxa⟩ := (LinearPMap.mem_graph_iff _).mp hpa
      obtain ⟨y, hy, hya⟩ := (LinearPMap.mem_graph_iff _).mp hp'
      have hxy : x = y := Subtype.ext (hx.trans hy.symm)
      exact hxa.symm.trans ((congrArg (operator hU hB hV) hxy).trans hya)
    change (ScalarForm.value J (ScalarForm.ofCore J f), a) ∈ ScalarForm.l2Graph K at ha
    change ScalarForm.value J (ScalarForm.ofCore J f) = p.1 at hv
    rw [hv, hea] at ha
    exact ha
  apply le_antisymm _ hsub
  intro p hp
  rw [← ScalarForm.l2Graph_adjoint J, Submodule.mem_adjoint_iff]
  intro a b hab
  exact (Submodule.mem_adjoint_iff _ _).mp
    (show p ∈ (ScalarForm.l2Graph K).adjoint by rw [ScalarForm.l2Graph_adjoint]; exact hp)
    a b (hsub hab)

/-- See Appendix A of the paper: completing all finite-energy interior
smooth functions gives exactly the original Neumann Sobolev space,
as equality of closed submodules of the same value–gradient space. -/
theorem interior_completion_eq [Nontrivial E] (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) {C : ℝ} (hC : 0 ≤ C)
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹ ^ 2 - C ≤
      ‖gradient V x‖ ^ 2 / 4 - Δ V x / 2) :
    ScalarForm.completionSubmodule (interiorJet hU (supported hU hV)) =
      ScalarForm.completionSubmodule (jet hU hB hV) := by
  let J := jet hU hB hV
  let K := interiorJet hU (supported hU hV)
  have hinj := interior_value_injective hU hB hV
  have hclosed : IsClosed (ScalarForm.completionSubmodule J : Set (ScalarForm.Jet ρ E)) :=
    J.range.isClosed_topologicalClosure
  have hc : IsClosed {u : ScalarForm.Domain K | u.val ∈ ScalarForm.completionSubmodule J} :=
    hclosed.preimage (continuous_subtype_val :
      Continuous (Subtype.val : ScalarForm.Domain K → ScalarForm.Jet ρ E))
  have hsub : ScalarForm.operatorDomain K ⊆
      {u : ScalarForm.Domain K | u.val ∈ ScalarForm.completionSubmodule J} := by
    rintro u ⟨a, ha⟩
    have hp : (ScalarForm.value K u, a) ∈ ScalarForm.l2Graph J := by
      rw [← interior_l2Graph_eq hU hB hV hC hbar]
      exact (ScalarForm.mem_l2Graph_iff K _ _).mpr ⟨u, rfl, ha⟩
    obtain ⟨v, hv, _⟩ := (ScalarForm.mem_l2Graph_iff J _ _).mp hp
    let v' : ScalarForm.Domain K := ⟨v.val, completion_le_interior hU hB hV v.property⟩
    have he : v' = u := hinj hv
    have heval : v.val = u.val := congrArg Subtype.val he
    change u.val ∈ ScalarForm.completionSubmodule J
    rw [← heval]
    exact v.property
  apply le_antisymm _ (completion_le_interior hU hB hV)
  intro u hu
  exact (hc.closure_subset_iff.mpr hsub) ((ScalarForm.dense_operatorDomain K hinj) ⟨u, hu⟩)

omit [BorelSpace E] in
/-- The alternate linear family is exactly the library's finite-norm
interior-smooth jet core, without a new encoding of the completion. -/
theorem range_interiorJet (hU : IsOpen U) (hρ : ∀ᵐ x ∂ρ, x ∈ U) :
    ((interiorJet hU hρ).range : Set (ScalarForm.Jet ρ E)) =
      Riesz1.WeightedSobolev.jetCore ρ (fun f => ContDiffOn ℝ (⊤ : ℕ∞) f U) id gradient := by
  ext z
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f.val, f.property.1, f.property.2.1, f.property.2.2, rfl⟩
  · rintro ⟨f, hf, hv, hg, rfl⟩
    exact ⟨⟨f, hf, hv, hg⟩, rfl⟩

/-- See Appendix A of the paper, equality of smooth conventions stated
using the existing Riesz1 completion and the Sobolev graph. -/
theorem mem_interior_completion_iff [Nontrivial E] (hU : IsOpen U)
    (hB : Bornology.IsBounded U) (hV : IsEuclideanGibbsPotential volume ρ U V)
    {C : ℝ} (hC : 0 ≤ C)
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹ ^ 2 - C ≤
      ‖gradient V x‖ ^ 2 / 4 - Δ V x / 2) (f : Lp ℝ 2 ρ) (g : Lp E 2 ρ) :
    WithLp.toLp 2 (f, g) ∈ Riesz1.WeightedSobolev.JetCompletion ρ
      (fun f => ContDiffOn ℝ (⊤ : ℕ∞) f U) id gradient ↔
      (f, g) ∈ neumannSobolevGraph ρ U := by
  have := probability hV
  rw [EuclideanScalarForm.mem_neumannSobolevGraph_iff hU hB (supported hU hV)]
  change _ ↔ WithLp.toLp 2 (f, g) ∈ ScalarForm.completionSubmodule (jet hU hB hV)
  rw [← interior_completion_eq hU hB hV hC hbar]
  change _ ↔ WithLp.toLp 2 (f, g) ∈
    closure ((interiorJet hU (supported hU hV)).range : Set (ScalarForm.Jet ρ E))
  rw [range_interiorJet]
  rfl

/-- See Appendix A of the paper, the explicit graph approximation:
for each generator graph pair there are compact smooth functions whose
values and generator outputs converge in their respective L² spaces. -/
theorem graph_approximation [Nontrivial E] (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) {C : ℝ} (hC : 0 ≤ C)
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹ ^ 2 - C ≤
      ‖gradient V x‖ ^ 2 / 4 - Δ V x / 2)
    {f a : Lp ℝ 2 ρ} (hfa : (f, a) ∈ (operator hU hB hV).graph) :
    ∃ c : ℕ → compactTests U, ∃ b : ℕ → Lp ℝ 2 ρ,
      (∀ k, (ScalarForm.value (jet hU hB hV) (ScalarForm.ofCore (jet hU hB hV) (c k).val),
        b k) ∈ (operator hU hB hV).graph) ∧
      Tendsto (fun k => ScalarForm.value (jet hU hB hV)
        (ScalarForm.ofCore (jet hU hB hV) (c k).val)) atTop (𝓝 f) ∧
      Tendsto b atTop (𝓝 a) := by
  let J := jet hU hB hV
  have hp : (f, a) ∈ closure ((testOperator hU hB hV).graph : Set _) := by
    rw [← Submodule.topologicalClosure_coe, test_graph_closure hU hB hV hC hbar]
    exact hfa
  obtain ⟨p, hp, ht⟩ := mem_closure_iff_seq_limit.mp hp
  have hc (k : ℕ) : ∃ c : compactTests U,
      ScalarForm.value J (ScalarForm.ofCore J c.val) = (p k).1 := by
    obtain ⟨_, v, ⟨c, hc, rfl⟩, hv⟩ := (mem_testOperator_graph_iff hU hB hV (p k)).mp (hp k)
    exact ⟨⟨c, hc⟩, hv⟩
  choose c hc using hc
  refine ⟨c, fun k => (p k).2, fun k => ?_, ?_, continuous_snd.tendsto _ |>.comp ht⟩
  · rw [hc k]
    exact (mem_testOperator_graph_iff hU hB hV (p k)).mp (hp k) |>.1
  · change Tendsto (fun k => ScalarForm.value J (ScalarForm.ofCore J (c k).val)) atTop (𝓝 f)
    simpa only [Function.comp_def, hc] using continuous_fst.tendsto (f, a) |>.comp ht

/-- See Appendix A of the paper. The result holds on every bounded open domain
with the stated collision barrier. The Sobolev form is the Neumann realization.
Both completions are identified as value–gradient pairs. -/
theorem scalar_operator_core [Nontrivial E] (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) {C : ℝ} (hC : 0 ≤ C)
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹ ^ 2 - C ≤
      ‖gradient V x‖ ^ 2 / 4 - Δ V x / 2) :
    IsNeumannRealization U (form hU hB hV) ∧
    IsSelfAdjoint (operator hU hB hV) ∧
    (∀ f a : Lp ℝ 2 ρ, (f, a) ∈ (operator hU hB hV).graph → 0 ≤ inner ℝ a f) ∧
    IsConservativeScalarForm (form hU hB hV) ∧
    (∃ one : Lp ℝ 2 ρ, (∀ᵐ x ∂ρ, one x = 1) ∧ (one, 0) ∈ (operator hU hB hV).graph) ∧
    (operator hU hB hV).HasCore (compactValueDomain hU hB hV) ∧
    Dense (compactFormDomain hU hB hV : Set (ScalarForm.Domain (jet hU hB hV))) ∧
    (∀ f : Lp ℝ 2 ρ, ∀ g : Lp E 2 ρ,
      WithLp.toLp 2 (f, g) ∈ Riesz1.WeightedSobolev.JetCompletion ρ
        (fun f => ContDiffOn ℝ (⊤ : ℕ∞) f U) id gradient ↔ (f, g) ∈ neumannSobolevGraph ρ U) ∧
    (∀ f a : Lp ℝ 2 ρ, (f, a) ∈ (operator hU hB hV).graph →
      ∃ c : ℕ → compactTests U, ∃ b : ℕ → Lp ℝ 2 ρ,
        (∀ k, (ScalarForm.value (jet hU hB hV) (ScalarForm.ofCore (jet hU hB hV) (c k).val),
          b k) ∈ (operator hU hB hV).graph) ∧
        Tendsto (fun k => ScalarForm.value (jet hU hB hV)
          (ScalarForm.ofCore (jet hU hB hV) (c k).val)) atTop (𝓝 f) ∧
        Tendsto b atTop (𝓝 a)) :=
  ⟨realization hU hB hV, selfAdjoint hU hB hV,
    fun _ _ hp => nonnegative hU hB hV hp, conservative hU hB hV, kills_one hU hB hV,
    hasCore hU hB hV hC hbar, dense_compactFormDomain hU hB hV hC hbar,
    mem_interior_completion_iff hU hB hV hC hbar,
    fun _ _ hp => graph_approximation hU hB hV hC hbar hp⟩

end IntrinsicScalarCore
end Riesz2
