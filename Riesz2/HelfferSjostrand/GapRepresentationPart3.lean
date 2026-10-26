/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.NeumannIsometryTransport
public import Riesz2.Frozen.ScalarPoissonSolution
public import Riesz2.Frozen.WeightedWeakSolution
public import Riesz2.HelfferSjostrand.DifferentiatedPoissonPart3
public import Riesz2.HelfferSjostrand.GapRepresentationPart2
public import Riesz2.ToMathlib.RectangularFormTransport
public import Riesz2.ToMathlib.NeumannScalarDirichlet
public import Riesz2.ToMathlib.ConstrainedNormalMultiplier

/-!
# Complete intrinsic gap representation

See Proposition 3.3 of the paper. The proof transports the full
differentiated equation through an orthonormal base chart and its rectangular
tangent inclusion. It identifies the intrinsic scalar gradient and proves
the full-domain and local ambient distribution statements.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped BigOperators RealInnerProductSpace ContDiff Laplacian

namespace Riesz2.NeumannFormIsometry

open NeumannIsometryTransport

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
/-- Surjectivity of scalar L² transport in Proposition 3.3. -/
theorem valueMap_surjective (e : E ≃ₗᵢ[ℝ] F) (ρ : Measure E) :
    Function.Surjective (valueMap e ρ) := by
  intro f
  let hp : MeasurePreserving e ρ (ρ.map e) := ⟨e.continuous.measurable, rfl⟩
  refine ⟨Lp.compMeasurePreserving e hp f, ?_⟩
  apply Lp.ext
  filter_upwards [valueMap_ae e ρ (Lp.compMeasurePreserving e hp f),
    (measurePreserving_symm e ρ).quasiMeasurePreserving.ae
      (Lp.coeFn_compMeasurePreserving f hp)] with y hy hz
  exact hy.trans (by simpa only [Function.comp_apply, e.apply_symm_apply] using hz)

/-- The existing scalar value map as a linear equivalence, Proposition 3.3. -/
def valueEquiv (e : E ≃ₗᵢ[ℝ] F) (ρ : Measure E) :
    Lp ℝ 2 ρ ≃ₗ[ℝ] Lp ℝ 2 (ρ.map e) :=
  LinearEquiv.ofBijective (valueMap e ρ).toLinearMap
    ⟨(valueMap e ρ).injective, valueMap_surjective e ρ⟩

/-- Two-sided membership of the full realized scalar domains, Proposition 3.3. -/
theorem mem_domain_iff (e : E ≃ₗᵢ[ℝ] F) {ρ : Measure E} [IsFiniteMeasure ρ]
    {U : Set E} (hB : Bornology.IsBounded U) (hρ : ∀ᵐ x ∂ρ, x ∈ U)
    (Q : ScalarFormData ρ) (Q' : ScalarFormData (ρ.map e))
    (hQ : IsNeumannRealization U Q) (hQ' : IsNeumannRealization (e '' U) Q')
    (f : Lp ℝ 2 ρ) : valueMap e ρ f ∈ Q'.1 ↔ f ∈ Q.1 := by
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := (hQ'.1 _).mp hf
    have hs : ∀ᵐ y ∂ρ.map e, y ∈ e '' U :=
      e.toHomeomorph.measurableEmbedding.ae_map_iff.mpr
        (hρ.mono fun x hx => mem_image_of_mem e hx)
    have hh : Riesz1.WeightedSobolev.IsWeightedH1 (ρ.map e) (e '' U)
        (valueMap e ρ f) g := by
      apply (VectorRadial.isWeightedH1_iff_neumannSobolevGraph
        (e.isometry.lipschitzWith.isBounded_image hB) hs (Lp.memLp _) (Lp.memLp _)).mpr
      simpa only [Lp.toLp_coeFn] using hg
    have hb := SobolevIsometry.weightedH1 e.symm hs hh
    have hμ : (ρ.map e).map e.symm = ρ := e.toHomeomorph.toMeasurableEquiv.map_symm_map
    rw [hμ,
      show e.symm '' (e '' U) = U by ext x; simp] at hb
    have hp : MeasurePreserving e ρ (ρ.map e) := ⟨e.continuous.measurable, rfl⟩
    have hv : (valueMap e ρ f ∘ e) =ᵐ[ρ] f := by
      filter_upwards [hp.quasiMeasurePreserving.ae (valueMap_ae e ρ f)] with x hx
      simpa only [Function.comp_apply, e.symm_apply_apply] using hx
    have hh' := hb.congr hv (EventuallyEq.rfl)
    have hn := (VectorRadial.isWeightedH1_iff_neumannSobolevGraph hB hρ
      (Lp.memLp f) hh'.2.1).mp hh'
    apply (hQ.1 f).mpr
    exact ⟨_, by simpa only [Lp.toLp_coeFn] using hn⟩
  · intro hf
    obtain ⟨g, hg⟩ := (hQ.1 f).mp hf
    exact (hQ'.1 _).mpr ⟨gradientMap e ρ g, neumannSobolevGraph_map e hB hρ f g hg⟩

/-- Linear equivalence of the complete realized H¹ carriers, Proposition 3.3. -/
def domainEquiv (e : E ≃ₗᵢ[ℝ] F) {ρ : Measure E} [IsFiniteMeasure ρ]
    {U : Set E} (hB : Bornology.IsBounded U) (hρ : ∀ᵐ x ∂ρ, x ∈ U)
    (Q : ScalarFormData ρ) (Q' : ScalarFormData (ρ.map e))
    (hQ : IsNeumannRealization U Q) (hQ' : IsNeumannRealization (e '' U) Q') :
    Q.1 ≃ₗ[ℝ] Q'.1 :=
  (valueEquiv e ρ).submoduleMap Q.1 |>.trans
    (LinearEquiv.ofEq _ _ (by
      ext f
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact (mem_domain_iff e hB hρ Q Q' hQ hQ' g).mpr hg
      · intro hf
        obtain ⟨g, rfl⟩ := valueMap_surjective e ρ f
        exact ⟨g, (mem_domain_iff e hB hρ Q Q' hQ hQ' g).mp hf, rfl⟩))

variable (e : E ≃ₗᵢ[ℝ] F) {ρ : Measure E} [IsFiniteMeasure ρ]
  {U : Set E} (hB : Bornology.IsBounded U) (hρ : ∀ᵐ x ∂ρ, x ∈ U)
  (Q : ScalarFormData ρ) (Q' : ScalarFormData (ρ.map e))
  (hQ : IsNeumannRealization U Q) (hQ' : IsNeumannRealization (e '' U) Q')

local notation "T" => domainEquiv e hB hρ Q Q' hQ hQ'

/-- Values of the realized-domain equivalence, Proposition 3.3. -/
theorem domainEquiv_value (f : Q.1) : (T f).val = valueMap e ρ f.val := rfl

/-- Mixed scalar energies are preserved on the full domains, Proposition 3.3. -/
theorem energy_map (f h : Q.1) : Q'.2 (T f) (T h) = Q.2 f h := by
  obtain ⟨g, hg⟩ := (hQ.1 f.val).mp f.property
  obtain ⟨k, hk⟩ := (hQ.1 h.val).mp h.property
  exact realization_energy_map e Q Q' hQ hQ' f h (T f) (T h) g k hg hk
    (neumannSobolevGraph_map e hB hρ f.val g hg)
    (neumannSobolevGraph_map e hB hρ h.val k hk)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsFiniteMeasure ρ] in
/-- Change of variables with arbitrary a.e. representatives, Proposition 3.3. -/
theorem integrable_transport (f : E → ℝ) (f' : F → ℝ)
    (hf : f' =ᵐ[ρ.map e] f ∘ e.symm) :
    Integrable f' (ρ.map e) ↔ Integrable f ρ := by
  have hp : MeasurePreserving e ρ (ρ.map e) := ⟨e.continuous.measurable, rfl⟩
  have he : (f' ∘ e) =ᵐ[ρ] f := by
    filter_upwards [hp.quasiMeasurePreserving.ae hf] with x hx
    simpa only [Function.comp_apply, e.symm_apply_apply] using hx
  exact e.toHomeomorph.measurableEmbedding.integrable_map_iff.trans (integrable_congr he)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsFiniteMeasure ρ] in
/-- Integral transport does not depend on representatives, Proposition 3.3. -/
theorem integral_transport (f : E → ℝ) (f' : F → ℝ)
    (hf : f' =ᵐ[ρ.map e] f ∘ e.symm) :
    (∫ y, f' y ∂ρ.map e) = ∫ x, f x ∂ρ := by
  erw [e.toHomeomorph.measurableEmbedding.integral_map]
  have hp : MeasurePreserving e ρ (ρ.map e) := ⟨e.continuous.measurable, rfl⟩
  apply integral_congr_ae
  filter_upwards [hp.quasiMeasurePreserving.ae hf] with x hx
  change f' (e x) = f x
  simpa only [Function.comp_apply, e.symm_apply_apply] using hx

/-- The scalar mean is invariant, Proposition 3.3. -/
theorem mean_map (f : Q.1) : (∫ y, (T f).val y ∂ρ.map e) = ∫ x, f.val x ∂ρ :=
  integral_transport e _ _ (valueMap_ae e ρ f.val)

/-- The complete scalar Poisson predicate transports, Proposition 3.3. Tests range over the whole scalar domain. -/
theorem scalarPoissonSolution_map (G ψ : Q.1) :
    ScalarPoissonSolution Q' (T G) (T ψ) ↔ ScalarPoissonSolution Q G ψ := by
  have hi (f : Q.1) : Integrable (T f).val (ρ.map e) ↔ Integrable f.val ρ :=
    integrable_transport e _ _ (valueMap_ae e ρ f.val)
  have hp (h : Q.1) :
      (fun y => ((T G).val y - ∫ z, (T G).val z ∂ρ.map e) * (T h).val y) =ᵐ[ρ.map e]
        (fun x => (G.val x - ∫ z, G.val z ∂ρ) * h.val x) ∘ e.symm := by
    rw [mean_map e hB hρ Q Q' hQ hQ' G]
    filter_upwards [valueMap_ae e ρ G.val, valueMap_ae e ρ h.val] with y hy hz
    rw [domainEquiv_value, domainEquiv_value, hy, hz]
    rfl
  constructor
  · rintro ⟨hG, hψ, hm, hw⟩
    refine ⟨(hi G).mp hG, (hi ψ).mp hψ, ?_, fun h => ?_⟩
    · rwa [mean_map e hB hρ Q Q' hQ hQ'] at hm
    · obtain ⟨hh, he⟩ := hw (T h)
      refine ⟨(integrable_transport e _ _ (hp h)).mp hh, ?_⟩
      rwa [energy_map e hB hρ Q Q' hQ hQ', integral_transport e _ _ (hp h)] at he
  · rintro ⟨hG, hψ, hm, hw⟩
    refine ⟨(hi G).mpr hG, (hi ψ).mpr hψ, ?_, fun h' => ?_⟩
    · rwa [mean_map e hB hρ Q Q' hQ hQ']
    · let h : Q.1 := (T).symm h'
      have hrec : T h = h' := (T).apply_symm_apply h'
      rw [← hrec]
      obtain ⟨hh, he⟩ := hw h
      refine ⟨(integrable_transport e _ _ (hp h)).mpr hh, ?_⟩
      rwa [energy_map e hB hρ Q Q' hQ hQ', integral_transport e _ _ (hp h)]

variable {ι : Type*} [Fintype ι]

/-- Matrix cross integrands transform on the complete domains, Proposition 3.3. Component and base dimensions are independent. -/
theorem matrixPair_map (M : E → Matrix ι ι ℝ) (u w : ι → Q.1) :
    matrixFieldPair (M ∘ e.symm) (fun i => (T (u i)).val) (fun i => (T (w i)).val)
      =ᵐ[ρ.map e] matrixFieldPair M (fun i => (u i).val) (fun i => (w i).val) ∘ e.symm := by
  filter_upwards [ae_all_iff.mpr (fun i => valueMap_ae e ρ (u i).val),
    ae_all_iff.mpr (fun i => valueMap_ae e ρ (w i).val)] with y hy hz
  simp only [matrixFieldPair, domainEquiv_value, hy, hz, Function.comp_apply]

/-- Exact transport of all finite matrix-energy fields, Proposition 3.3. -/
theorem weightedFormDomain_map (M : E → Matrix ι ι ℝ) (S : Submodule ℝ (ι → ℝ))
    (u : ι → Q.1) :
    WeightedFormDomain Q' (M ∘ e.symm) S (fun i => T (u i)) ↔
      WeightedFormDomain Q M S u := by
  have hp : MeasurePreserving e ρ (ρ.map e) := ⟨e.continuous.measurable, rfl⟩
  have hv : (∀ᵐ y ∂ρ.map e, (fun i => (T (u i)).val y) ∈ S) ↔
      ∀ᵐ x ∂ρ, (fun i => (u i).val x) ∈ S := by
    erw [e.toHomeomorph.measurableEmbedding.ae_map_iff]
    apply eventually_congr
    filter_upwards [hp.quasiMeasurePreserving.ae
      (ae_all_iff.mpr (fun i => valueMap_ae e ρ (u i).val))] with x hx
    have he : (fun i => (T (u i)).val (e.toHomeomorph x)) = fun i => (u i).val x := by
      funext i
      exact (hx i).trans (by simp only [Function.comp_apply, e.symm_apply_apply])
    rw [he]
  exact and_congr hv (integrable_transport e _ _ (matrixPair_map e hB hρ Q Q' hQ hQ' M u u))

/-- Mixed source pairings are preserved, Proposition 3.3. -/
theorem source_map (v : ι → Lp ℝ 2 ρ) (u : ι → Q.1) :
    (∑ i, inner ℝ (valueMap e ρ (v i)) (T (u i)).val) =
      ∑ i, inner ℝ (v i) (u i).val := by
  apply Finset.sum_congr rfl
  intro i _
  exact (valueMap e ρ).inner_map_map (v i) (u i).val

/-- Transport of the full-domain weak equation, including all cross
integrability clauses, Proposition 3.3. -/
theorem weightedWeakSolution_map (M : E → Matrix ι ι ℝ) (S : Submodule ℝ (ι → ℝ))
    (v : ι → Lp ℝ 2 ρ) (u : ι → Q.1) :
    WeightedWeakSolution Q' (M ∘ e.symm) S (fun i => valueMap e ρ (v i)) (fun i => T (u i)) ↔
      WeightedWeakSolution Q M S v u := by
  have hd := weightedFormDomain_map e hB hρ Q Q' hQ hQ' M S
  have hp := matrixPair_map e hB hρ Q Q' hQ hQ' M
  have he (u w : ι → Q.1) : (∑ i, Q'.2 (T (u i)) (T (w i))) = ∑ i, Q.2 (u i) (w i) :=
    Finset.sum_congr rfl (fun i _ => energy_map e hB hρ Q Q' hQ hQ' (u i) (w i))
  constructor
  · rintro ⟨hu, hw⟩
    refine ⟨(hd u).mp hu, fun w hw' => ?_⟩
    obtain ⟨hi, hh⟩ := hw (fun i => T (w i)) ((hd w).mpr hw')
    refine ⟨(integrable_transport e _ _ (hp u w)).mp hi, ?_⟩
    rwa [he, integral_transport e _ _ (hp u w), source_map e hB hρ Q Q' hQ hQ'] at hh
  · rintro ⟨hu, hw⟩
    refine ⟨(hd u).mpr hu, fun w' hw' => ?_⟩
    let w : ι → Q.1 := fun i => (T).symm (w' i)
    have hrec : (fun i => T (w i)) = w' := funext (fun i => (T).apply_symm_apply (w' i))
    rw [← hrec] at hw' ⊢
    obtain ⟨hi, hh⟩ := hw w ((hd w).mp hw')
    refine ⟨(integrable_transport e _ _ (hp u w)).mpr hi, ?_⟩
    rwa [he, integral_transport e _ _ (hp u w), source_map e hB hρ Q Q' hQ hQ']

/-- The entire vector variational functional is invariant, Proposition 3.3. -/
theorem functional_map (M : E → Matrix ι ι ℝ) (v : ι → Lp ℝ 2 ρ) (u : ι → Q.1) :
    (∑ i, Q'.2 (T (u i)) (T (u i))) +
        (∫ y, matrixFieldPair (M ∘ e.symm) (fun i => (T (u i)).val)
          (fun i => (T (u i)).val) y ∂ρ.map e) -
        2 * (∑ i, inner ℝ (valueMap e ρ (v i)) (T (u i)).val) =
      (∑ i, Q.2 (u i) (u i)) +
        (∫ x, matrixFieldPair M (fun i => (u i).val) (fun i => (u i).val) x ∂ρ) -
        2 * (∑ i, inner ℝ (v i) (u i).val) := by
  rw [integral_transport e _ _ (matrixPair_map e hB hρ Q Q' hQ hQ' M u u),
    source_map e hB hρ Q Q' hQ hQ']
  congr 2
  exact Finset.sum_congr rfl (fun i _ => energy_map e hB hρ Q Q' hQ hQ' (u i) (u i))

/-- Unique minimization transports over every finite-energy competitor,
Proposition 3.3. This is an internal criterion. -/
theorem unique_minimum_map (M : E → Matrix ι ι ℝ) (S : Submodule ℝ (ι → ℝ))
    (v : ι → Lp ℝ 2 ρ) (u : ι → Q.1) :
    let J := fun w : ι → Q.1 => (∑ i, Q.2 (w i) (w i)) +
      (∫ x, matrixFieldPair M (fun i => (w i).val) (fun i => (w i).val) x ∂ρ) -
      2 * (∑ i, inner ℝ (v i) (w i).val)
    let J' := fun w : ι → Q'.1 => (∑ i, Q'.2 (w i) (w i)) +
      (∫ y, matrixFieldPair (M ∘ e.symm) (fun i => (w i).val) (fun i => (w i).val) y ∂ρ.map e) -
      2 * (∑ i, inner ℝ (valueMap e ρ (v i)) (w i).val)
    (∀ w : ι → Q'.1, WeightedFormDomain Q' (M ∘ e.symm) S w →
      J' (fun i => T (u i)) ≤ J' w ∧ (J' w = J' (fun i => T (u i)) → w = fun i => T (u i))) →
    ∀ w : ι → Q.1, WeightedFormDomain Q M S w →
      J u ≤ J w ∧ (J w = J u → w = u) := by
  intro J J' hmin w hw
  have ht := hmin (fun i => T (w i))
    ((weightedFormDomain_map e hB hρ Q Q' hQ hQ' M S w).mpr hw)
  have hu : J' (fun i => T (u i)) = J u := functional_map e hB hρ Q Q' hQ hQ' M v u
  have hh : J' (fun i => T (w i)) = J w := functional_map e hB hρ Q Q' hQ hQ' M v w
  refine ⟨by linarith only [ht.1, hu, hh], fun he => ?_⟩
  have heq := ht.2 (by linarith only [he, hu, hh])
  funext i
  exact (T).injective (congrFun heq i)

end Riesz2.NeumannFormIsometry

namespace Riesz2.NeumannIsometryTransport

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The intrinsic Laplacian is invariant under orthonormal base change,
Proposition 3.3. Smoothness is required only inside the domain. -/
theorem laplacian_comp_symm (e : E ≃ₗᵢ[ℝ] F) {U : Set E} (hU : IsOpen U)
    {V : E → ℝ} (hV : ContDiffOn ℝ 2 V U) {x : F} (hx : e.symm x ∈ U) :
    Laplacian.laplacian (V ∘ e.symm) x = Laplacian.laplacian V (e.symm x) := by
  let b := stdOrthonormalBasis ℝ F
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ b,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ (b.map e.symm)]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    OrthonormalBasis.map_apply]
  exact Finset.sum_congr rfl (fun i _ => SobolevIsometry.hessian_comp_symm e hU hV hx _ _)

/-- The complete collision barrier transports to the orthonormal chart,
Proposition 3.3. -/
theorem barrier_map (e : E ≃ₗᵢ[ℝ] F) {U : Set E} (hU : IsOpen U)
    {V : E → ℝ} (hV : ContDiffOn ℝ 2 V U) {C : ℝ}
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹ ^ 2 - C ≤
      ‖gradient V x‖ ^ 2 / 4 - Laplacian.laplacian V x / 2) :
    ∀ y ∈ e '' U, (Metric.infDist y (frontier (e '' U)))⁻¹ ^ 2 - C ≤
      ‖gradient (V ∘ e.symm) y‖ ^ 2 / 4 - Laplacian.laplacian (V ∘ e.symm) y / 2 := by
  rintro y ⟨x, hx, rfl⟩
  have hd : Metric.infDist (e x) (frontier (e '' U)) = Metric.infDist x (frontier U) := by
    change Metric.infDist (e.toHomeomorph x) (frontier (e.toHomeomorph '' U)) = _
    rw [← e.toHomeomorph.image_frontier]
    exact Metric.infDist_image e.isometry
  have hx' : e.symm (e x) ∈ U := by simpa only [e.symm_apply_apply] using hx
  rw [hd, laplacian_comp_symm e hU hV hx',
    SobolevIsometry.gradient_comp_symm e ((hV.contDiffAt (hU.mem_nhds hx')).differentiableAt
      (by norm_num)), e.norm_map, e.symm_apply_apply]
  exact hbar x hx

end Riesz2.NeumannIsometryTransport

namespace Riesz2.NeumannDifferentiatedTransport

open IntrinsicScalarCore NeumannIsometryTransport NeumannFormIsometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {d : ℕ} {ρ : Measure E} {U : Set E} {V : E → ℝ}

/-- A native L² gradient's coordinate in the chosen orthonormal chart,
Proposition 3.3. This is the continuous linear L² functor. -/
def coordinateValue (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    Lp E 2 ρ →L[ℝ] Lp ℝ 2 ρ :=
  ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).comp
    e.toContinuousLinearEquiv.toContinuousLinearMap).compLpL 2 ρ

omit [FiniteDimensional ℝ E] in
/-- Coordinate extraction commutes with base transport and gradient rotation,
Proposition 3.3. -/
theorem coordinateValue_map (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (i : Fin d) (g : Lp E 2 ρ) :
    valueMap e ρ (coordinateValue e i g) =
      DifferentiatedPoisson.coordinateLp i (gradientMap e ρ g) := by
  apply Lp.ext
  have hc := ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).comp
    e.toContinuousLinearEquiv.toContinuousLinearMap).coeFn_compLpL (p := 2) (μ := ρ) g
  filter_upwards [valueMap_ae e ρ (coordinateValue e i g),
    (measurePreserving_symm e ρ).quasiMeasurePreserving.ae hc,
    DifferentiatedPoisson.coordinateLp_ae i (gradientMap e ρ g), gradientMap_ae e ρ g]
    with y hy hc hd hg
  exact hy.trans (hc.trans (by rw [hd, hg]; rfl))

/-- A scalar solution in the realized domain is the same solution in completed
jets, Proposition 3.3. -/
theorem scalar_solution_jet (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V)
    (G ψ : ScalarForm.Domain (jet hU hB hV))
    (hψ : ScalarPoissonSolution (form hU hB hV)
      (ScalarForm.valueEquiv _ (value_injective hU hB hV) G)
      (ScalarForm.valueEquiv _ (value_injective hU hB hV) ψ)) :
    (ψ, @Riesz1.poissonCenter _ _ ρ (probability hV) (ScalarForm.value _ G)) ∈
      ScalarForm.neumannGraph (jet hU hB hV) := by
  have := probability hV
  intro h
  have he := (hψ.2.2.2 (ScalarForm.valueEquiv _ (value_injective hU hB hV) h)).2
  have he' := (ScalarForm.realization_energy (jet hU hB hV)
    (value_injective hU hB hV) ψ h).symm.trans he
  rw [he', Riesz1.poisson_inner_eq_integral]
  apply integral_congr_ae
  exact (Riesz1.poissonCenter_ae ρ (ScalarForm.value _ G)).symm.mono
    (fun x hx => congrArg (· * ScalarForm.value _ h x) hx)

/-- The derivative of a completed jet is its weak gradient,
Proposition 3.3. -/
theorem jet_gradient (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V)
    (f : ScalarForm.Domain (jet hU hB hV)) :
    (ScalarForm.value _ f, ScalarForm.deriv _ f) ∈ neumannSobolevGraph ρ U := by
  have := probability hV
  exact (EuclideanScalarForm.mem_neumannSobolevGraph_iff hU hB (supported hU hV) _ _).mpr f.property

/-- The differentiated equation on the realized Euclidean value carrier,
Proposition 3.3. The gradient representatives are arbitrary
members of the graph. -/
theorem realized_gradient_equation
    {U : Set (EuclideanSpace ℝ (Fin d))} {ρ : Measure (EuclideanSpace ℝ (Fin d))}
    {V : EuclideanSpace ℝ (Fin d) → ℝ} (hd : 1 ≤ d)
    (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) {κ : ℝ} (hκ : 0 < κ)
    (hH : ∀ x ∈ U, ∀ v, κ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    {C : ℝ} (hC : 0 ≤ C)
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹ ^ 2 - C ≤
      ‖gradient V x‖ ^ 2 / 4 - Laplacian.laplacian V x / 2)
    (G ψ : (form hU hB hV).1) (hψ : ScalarPoissonSolution (form hU hB hV) G ψ)
    (gG gψ : Lp (EuclideanSpace ℝ (Fin d)) 2 ρ)
    (hgG : (G.val, gG) ∈ neumannSobolevGraph ρ U)
    (hgψ : (ψ.val, gψ) ∈ neumannSobolevGraph ρ U) :
    ∃ u : Fin d → (form hU hB hV).1,
      WeightedWeakSolution (form hU hB hV) (hessianMatrix V) ⊤
        (fun i => DifferentiatedPoisson.coordinateLp i gG) u ∧
      ∀ i, (u i).val = DifferentiatedPoisson.coordinateLp i gψ := by
  have := probability hV
  have : NeZero d := ⟨by omega⟩
  let J := jet hU hB hV
  let R := ScalarForm.valueEquiv J (value_injective hU hB hV)
  let G' := R.symm G
  let ψ' := R.symm ψ
  have hGval : ScalarForm.value J G' = G.val := congrArg Subtype.val (R.apply_symm_apply G)
  have hψval : ScalarForm.value J ψ' = ψ.val := congrArg Subtype.val (R.apply_symm_apply ψ)
  have hGder : ScalarForm.deriv J G' = gG := by
    apply (realization hU hB hV).2.1 G.val
    · rw [← hGval]
      exact jet_gradient hU hB hV G'
    · exact hgG
  have hψder : ScalarForm.deriv J ψ' = gψ := by
    apply (realization hU hB hV).2.1 ψ.val
    · rw [← hψval]
      exact jet_gradient hU hB hV ψ'
    · exact hgψ
  dsimp only [J] at hGder hψder
  have hs : ScalarPoissonSolution (form hU hB hV) (R G') (R ψ') := by
    rwa [show R G' = G from R.apply_symm_apply _, show R ψ' = ψ from R.apply_symm_apply _]
  have hgraph := scalar_solution_jet hU hB hV G' ψ' hs
  have hm := DifferentiatedPoisson.hessian_posSemidef_on hU hV
    (fun x hx v => (mul_nonneg hκ.le (sq_nonneg ‖v‖)).trans (hH x hx v))
  obtain ⟨z, hv, hz⟩ := DifferentiatedPoisson.gradient_graph_equation hU hB hV
    ((supported hU hV).mono (fun x hx => hm x hx)) hC hbar G' ψ' hgraph
  refine ⟨DifferentiatedPoisson.graphTuple hU hB hV z.val, ?_, ?_⟩
  · simpa only [hGder] using
      DifferentiatedPoisson.frozen_gradient_equation hU hB hV hC hbar hm G' z hz
  · intro i
    rw [DifferentiatedPoisson.graphTuple_value]
    simpa only [hψder] using hv i

/-- The differentiated scalar solution has native H¹ coordinate components and
satisfies the full native weak vector equation, Proposition 3.3.
This internal chart theorem applies to every given scalar solution. -/
theorem native_gradient_equation
    (e : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (hd : 1 ≤ d)
    (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) {κ : ℝ} (hκ : 0 < κ)
    (hH : ∀ x ∈ U, ∀ v, κ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x v v)
    {C : ℝ} (hC : 0 ≤ C)
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹ ^ 2 - C ≤
      ‖gradient V x‖ ^ 2 / 4 - Laplacian.laplacian V x / 2)
    (G ψ : (form hU hB hV).1) (hψ : ScalarPoissonSolution (form hU hB hV) G ψ)
    (gG gψ : Lp E 2 ρ) (hgG : (G.val, gG) ∈ neumannSobolevGraph ρ U)
    (hgψ : (ψ.val, gψ) ∈ neumannSobolevGraph ρ U) :
    ∃ u : Fin d → (form hU hB hV).1,
      WeightedWeakSolution (form hU hB hV)
        (fun x => hessianMatrix (V ∘ e.symm) (e x)) ⊤
        (fun i => coordinateValue e i gG) u ∧
      ∀ i, (u i).val = coordinateValue e i gψ := by
  have := probability hV
  let Q := form hU hB hV
  have hQ := realization hU hB hV
  let hU' := e.toHomeomorph.isOpenMap U hU
  let hB' := e.isometry.lipschitzWith.isBounded_image hB
  let hV' := IntrinsicScalarPoisson.gibbs_isometry e hV
  let Q' := form hU' hB' hV'
  have hQ' := realization hU' hB' hV'
  let T := domainEquiv e hB (supported hU hV) Q Q' hQ hQ'
  have hH' : ∀ y ∈ e '' U, ∀ v,
      κ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (V ∘ e.symm)) y v v := by
    rintro y ⟨x, hx, rfl⟩ v
    rw [SobolevIsometry.hessian_comp_symm e hU (hV.1.of_le (by norm_num))
      (by simpa only [e.symm_apply_apply] using hx), e.symm_apply_apply]
    simpa only [e.symm.norm_map] using hH x hx (e.symm v)
  obtain ⟨u', hu', hv⟩ := realized_gradient_equation hd hU' hB' hV' hκ hH' hC
    (barrier_map e hU (hV.1.of_le (by norm_num)) hbar) (T G) (T ψ)
    ((scalarPoissonSolution_map e hB (supported hU hV) Q Q' hQ hQ' G ψ).mpr hψ)
    (gradientMap e ρ gG) (gradientMap e ρ gψ)
    (neumannSobolevGraph_map e hB (supported hU hV) _ _ hgG)
    (neumannSobolevGraph_map e hB (supported hU hV) _ _ hgψ)
  let u : Fin d → Q.1 := fun i => T.symm (u' i)
  have hrec (i) : T (u i) = u' i := T.apply_symm_apply _
  have hM : (fun x => hessianMatrix (V ∘ e.symm) (e x)) ∘ e.symm = hessianMatrix (V ∘ e.symm) := by
    funext y
    simp only [Function.comp_apply, e.apply_symm_apply]
  refine ⟨u, ?_, fun i => ?_⟩
  · apply (weightedWeakSolution_map e hB (supported hU hV) Q Q' hQ hQ'
      (fun x => hessianMatrix (V ∘ e.symm) (e x)) ⊤ (fun i => coordinateValue e i gG) u).mp
    have hrec' : (fun i => domainEquiv e hB (supported hU hV) Q Q' hQ hQ' (u i)) = u' :=
      funext hrec
    simpa only [hM, coordinateValue_map, hrec'] using hu'
  · apply (valueMap e ρ).injective
    rw [coordinateValue_map]
    change (T (u i)).val = _
    rw [hrec]
    exact hv i

end Riesz2.NeumannDifferentiatedTransport

namespace Riesz2.CoerciveSolution

/-- A coercive symmetric form has a unique quadratic minimum at every weak
solution, Proposition 3.3. -/
theorem unique_minimum_of_equation
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (B : H →L[ℝ] H →L[ℝ] ℝ) (f : H →L[ℝ] ℝ)
    {c : ℝ} (hc : 0 < c) (hB : ∀ w, c * ‖w‖ ^ 2 ≤ B w w)
    (hs : ∀ u w, B u w = B w u) (u : H) (hu : ∀ w, B u w = f w) (w : H) :
    B u u - 2 * f u ≤ B w w - 2 * f w ∧
      (B w w - 2 * f w = B u u - 2 * f u → w = u) := by
  have he := Riesz1.Internal.quadratic_pairing_identity B u w (f u) (f w)
    (hu u) (hu w) (hs w u)
  have hn : 0 ≤ B (w - u) (w - u) :=
    (mul_nonneg hc.le (sq_nonneg _)).trans (hB _)
  refine ⟨by linarith only [he, hu u, hn], fun hh => ?_⟩
  have hz : B (w - u) (w - u) = 0 := by linarith only [he, hu u, hh]
  have hb := hB (w - u)
  rw [hz] at hb
  have hsq : ‖w - u‖ ^ 2 ≤ 0 := (mul_le_mul_iff_right₀ hc).mp (by simpa only [mul_zero, zero_mul, mul_comm] using hb)
  have hnorm : ‖w - u‖ = 0 := by nlinarith [norm_nonneg (w - u)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

end Riesz2.CoerciveSolution

namespace Riesz2.MatrixEnergy

open scoped BigOperators

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι]
  {ρ : Measure α}

/-- A full-domain weak solution uniquely minimizes the full finite-energy
functional, Proposition 3.3. This internal criterion permits
arbitrary fixed component constraints and unbounded measurable coefficients. -/
theorem weightedWeakSolution_unique_minimum
    (Q : ScalarFormData ρ) (hQ : IsClosedScalarDirichletForm Q)
    (M : α → Matrix ι ι ℝ) (S : Submodule ℝ (ι → ℝ))
    (hM : ∀ᵐ x ∂ρ, (M x).PosSemidef) (a : ℝ) (ha : 0 < a)
    (hlower : ∀ᵐ x ∂ρ, ∀ t ∈ S,
      a * (∑ i, t i ^ 2) ≤ ∑ i, ∑ j, t i * M x i j * t j)
    (hMmeas : ∀ i j, Measurable (fun x => M x i j))
    (f : ι → Lp ℝ 2 ρ) (u : ι → Q.1) (hu : WeightedWeakSolution Q M S f u) :
    ∀ w : ι → Q.1, WeightedFormDomain Q M S w →
      let Ju := (∑ i, Q.2 (u i) (u i)) +
        (∫ x, matrixFieldPair M (fun i => (u i).val) (fun i => (u i).val) x ∂ρ) -
        2 * (∑ i, inner ℝ (f i) (u i).val)
      let Jw := (∑ i, Q.2 (w i) (w i)) +
        (∫ x, matrixFieldPair M (fun i => (w i).val) (fun i => (w i).val) x ∂ρ) -
        2 * (∑ i, inner ℝ (f i) (w i).val)
      Ju ≤ Jw ∧ (Jw = Ju → w = u) := by
  obtain ⟨z, rfl⟩ := exists_tuple Q hQ M S hM hMmeas u hu.1
  have hz := (weightedWeakSolution_iff Q hQ M S hM hMmeas f z).mp hu
  intro w hw
  obtain ⟨t, rfl⟩ := exists_tuple Q hQ M S hM hMmeas w hw
  have hmin := CoerciveSolution.unique_minimum_of_equation
    (weakForm Q hQ M S hM) (sourcePairing Q hQ M S hM f)
    (div_pos ha (add_pos zero_lt_one ha)) (weakForm_coercivity Q hQ M S hM a ha hlower)
    (weakForm_symm Q hQ M S hM) z hz t
  dsimp only
  simp only [weakForm_apply, sourcePairing_apply] at hmin
  exact ⟨hmin.1, fun he => congrArg (tuple Q hQ M S hM) (hmin.2 he)⟩

end Riesz2.MatrixEnergy

namespace Riesz2.MatrixFieldTransport

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι] {ρ : Measure α}

/-- Almost-everywhere matrix equality identifies all cross integrands,
Proposition 3.3. -/
theorem pair_congr {M M' : α → Matrix ι ι ℝ} (hM : M =ᵐ[ρ] M')
    (u w : ι → Lp ℝ 2 ρ) : matrixFieldPair M u w =ᵐ[ρ] matrixFieldPair M' u w :=
  hM.mono (fun _ hx => by simp only [matrixFieldPair, hx])

/-- Almost-everywhere coefficients identify the entire energy domain,
Proposition 3.3. -/
theorem domain_congr (Q : ScalarFormData ρ) {M M' : α → Matrix ι ι ℝ}
    (hM : M =ᵐ[ρ] M') (S : Submodule ℝ (ι → ℝ)) (u : ι → Q.1) :
    WeightedFormDomain Q M S u ↔ WeightedFormDomain Q M' S u :=
  and_congr Iff.rfl (integrable_congr (pair_congr hM _ _))

/-- Almost-everywhere coefficients identify the full weak predicate,
Proposition 3.3. -/
theorem weak_congr (Q : ScalarFormData ρ) {M M' : α → Matrix ι ι ℝ}
    (hM : M =ᵐ[ρ] M') (S : Submodule ℝ (ι → ℝ)) (v : ι → Lp ℝ 2 ρ) (u : ι → Q.1) :
    WeightedWeakSolution Q M S v u ↔ WeightedWeakSolution Q M' S v u := by
  have hp (u w : ι → Q.1) := pair_congr hM (fun i => (u i).val) (fun i => (w i).val)
  simp only [WeightedWeakSolution, domain_congr Q hM S,
    integrable_congr (hp u _), integral_congr_ae (hp u _)]

end Riesz2.MatrixFieldTransport

namespace Riesz2.GapRepresentation

open AffineMetric IntrinsicScalarCore NeumannIsometryTransport RectangularFormTransport

variable {N : ℕ+} {d : ℕ}

/-- The matrix of the canonical tangent inclusion in an orthonormal basis,
Proposition 3.3. This changes only vector components. -/
def tangentBasisMatrix (b : OrthonormalBasis (Fin d) ℝ (gapTangentSpace N)) :
    Matrix (Fin (N : ℕ)) (Fin d) ℝ := fun i a => (b a).val i

/-- The rectangular matrix includes the actual native tangent vector,
Proposition 3.3. -/
theorem tangentBasisMatrix_mulVec (b : OrthonormalBasis (Fin d) ℝ (gapTangentSpace N))
    (t : Fin d → ℝ) :
    tangentBasisMatrix b *ᵥ t = (b.repr.symm (WithLp.toLp 2 t)).val := by
  have hs := b.sum_repr_symm (WithLp.toLp 2 t)
  have he := congrArg (fun z : gapTangentSpace N => z.val) hs
  ext i
  simpa only [tangentBasisMatrix, Matrix.mulVec, dotProduct, Submodule.coe_sum,
    Submodule.coe_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, mul_comm] using
    congrArg (fun z : EuclideanSpace ℝ (Fin (N : ℕ)) => z i) he

/-- The tangent inclusion has orthonormal columns, Proposition 3.3. It need not be onto the ambient space. -/
theorem tangentBasisMatrix_orthonormal (b : OrthonormalBasis (Fin d) ℝ (gapTangentSpace N)) :
    (tangentBasisMatrix b).transpose * tangentBasisMatrix b = 1 := by
  ext a k
  have hi := b.inner_eq_ite a k
  change (∑ i, (b a).val i * (b k).val i) = if a = k then 1 else 0
  simpa only [Submodule.coe_inner, PiLp.inner_apply, Real.inner_apply, mul_comm] using hi

/-- The rectangular range is exactly the zero-sum component subspace,
Proposition 3.3. -/
theorem tangentBasisMatrix_range (b : OrthonormalBasis (Fin d) ℝ (gapTangentSpace N)) :
    (tangentBasisMatrix b).mulVecLin.range = zeroSumComponents (Fin (N : ℕ)) := by
  ext t
  constructor
  · rintro ⟨v, rfl⟩
    change (∑ i, (tangentBasisMatrix b *ᵥ v) i) = 0
    rw [tangentBasisMatrix_mulVec]
    exact (b.repr.symm (WithLp.toLp 2 v)).property
  · intro ht
    let z : gapTangentSpace N := ⟨WithLp.toLp 2 t, ht⟩
    refine ⟨WithLp.ofLp (b.repr z), ?_⟩
    change tangentBasisMatrix b *ᵥ WithLp.ofLp (b.repr z) = t
    rw [tangentBasisMatrix_mulVec]
    simp only [WithLp.toLp_ofLp, LinearIsometryEquiv.symm_apply_apply]
    rfl

/-- Compression of the actual ambient Hessian is exactly the intrinsic Hessian
in the orthonormal chart, Proposition 3.3. -/
theorem tangentBasisMatrix_hessian (b : OrthonormalBasis (Fin d) ℝ (gapTangentSpace N))
    {hN : 2 ≤ (N : ℕ)} {χ : ParticlePairData N} {c : ℝ}
    (hχ : AdmissibleParticlePairs hN χ c) {z : gapTangentSpace N}
    (hz : z ∈ intrinsicGapDomain N) :
    (tangentBasisMatrix b).transpose *
        hessianMatrix (pairAmbientGapPotential χ) (WithLp.toLp 2 (fun i => 1 + z.val i)) *
        tangentBasisMatrix b =
      hessianMatrix ((fun z : gapTangentSpace N =>
        pairAmbientGapPotential χ (WithLp.toLp 2 (fun i => 1 + z.val i))) ∘ b.repr.symm)
        (b.repr z) := by
  let V := fun z : gapTangentSpace N =>
    pairAmbientGapPotential χ (WithLp.toLp 2 (fun i => 1 + z.val i))
  have hx : ContDiffAt ℝ ∞ V (b.repr.symm (b.repr z)) := by
    simpa only [LinearIsometryEquiv.symm_apply_apply] using
      (contDiffAt_intrinsicGapPotential hχ hz)
  have hV : ContDiffAt ℝ ∞ (V ∘ b.repr.symm) (b.repr z) :=
    hx.comp _ b.repr.symm.contDiff.contDiffAt
  ext a k
  rw [Intrinsic.hessianMatrix_eq_second hV,
    SobolevIsometry.hessian_comp_symm b.repr (intrinsicGapDomain_isOpen N)
      (fun x hx => (contDiffAt_intrinsicGapPotential hχ hx).of_le (by norm_num) |>.contDiffWithinAt)
      (by simpa using hz), LinearIsometryEquiv.symm_apply_apply,
    b.repr_symm_single, b.repr_symm_single,
    ambientHessian_tangent_pair hχ hz]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, tangentBasisMatrix, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The source components obtained by base rotation and rectangular inclusion
are the canonical ambient components of the native L² gradient, Proposition 3.3. -/
theorem tangentBasisMatrix_gradient_components
    (b : OrthonormalBasis (Fin d) ℝ (gapTangentSpace N))
    (ρ : Measure (gapTangentSpace N)) (g : Lp (gapTangentSpace N) 2 ρ) :
    tupleMap (tangentBasisMatrix b)
        (fun a => DifferentiatedPoisson.coordinateLp a (gradientMap b.repr ρ g)) =
      fun i => valueMap b.repr ρ (tangentCoordinateLp i g) := by
  funext i
  apply Lp.ext
  have hcoords := ae_all_iff.mpr (fun a =>
    DifferentiatedPoisson.coordinateLp_ae a (gradientMap b.repr ρ g))
  have ht := ae_all_iff.mpr (fun i => valueMap_ae b.repr ρ (tangentCoordinateLp i g))
  have hg := (measurePreserving_symm b.repr ρ).quasiMeasurePreserving.ae
    (ae_all_iff.mpr (fun i => tangentCoordinateLp_ae i g))
  filter_upwards [tupleMap_lp_ae (tangentBasisMatrix b)
      (fun a => DifferentiatedPoisson.coordinateLp a (gradientMap b.repr ρ g)),
    hcoords, gradientMap_ae b.repr ρ g, ht, hg] with y hy hc hv ht hg
  rw [hy i, ht i, Function.comp_apply, hg i]
  simp only [hc, hv]
  simpa only [WithLp.toLp_ofLp, LinearIsometryEquiv.symm_apply_apply, Matrix.mulVec, dotProduct] using
    congrFun (tangentBasisMatrix_mulVec b (WithLp.ofLp (b.repr (g (b.repr.symm y))))) i

/-- Coordinate inclusion on the native base recovers the canonical ambient
components, Proposition 3.3. -/
theorem tangentBasisMatrix_native_components
    (b : OrthonormalBasis (Fin d) ℝ (gapTangentSpace N))
    (ρ : Measure (gapTangentSpace N)) (g : Lp (gapTangentSpace N) 2 ρ) :
    tupleMap (tangentBasisMatrix b) (fun a =>
      (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) a).comp
        b.repr.toContinuousLinearEquiv.toContinuousLinearMap).compLpL 2 ρ) g) =
      fun i => tangentCoordinateLp i g := by
  funext i
  apply Lp.ext
  have hc := ae_all_iff.mpr (fun a =>
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) a).comp
      b.repr.toContinuousLinearEquiv.toContinuousLinearMap).coeFn_compLpL (p := 2) (μ := ρ) g)
  filter_upwards [hc, tupleMap_lp_ae (tangentBasisMatrix b) (fun a =>
    (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) a).comp
      b.repr.toContinuousLinearEquiv.toContinuousLinearMap).compLpL 2 ρ) g),
    tangentCoordinateLp_ae i g] with x hx hy hz
  rw [hy i, hz]
  simp only [hx, ContinuousLinearMap.comp_apply, PiLp.proj_apply]
  change (∑ a, tangentBasisMatrix b i a * (b.repr (g x)) a) = (g x).val i
  simpa only [WithLp.toLp_ofLp, LinearIsometryEquiv.symm_apply_apply, Matrix.mulVec, dotProduct] using
    congrFun (tangentBasisMatrix_mulVec b (WithLp.ofLp (b.repr (g x)))) i

/-- The actual collision criterion in the boundary convention required by
scalar graph approximation, Proposition 3.3. -/
theorem intrinsicGap_frontier_barrier (hN : 2 ≤ (N : ℕ)) {c : ℝ} (hc : 0 < c)
    {χ : ParticlePairData N} (hχ : AdmissibleParticlePairs hN χ c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ intrinsicGapDomain N,
      (Metric.infDist z (frontier (intrinsicGapDomain N)))⁻¹ ^ 2 - C ≤
        ‖gradient (fun z : gapTangentSpace N =>
          pairAmbientGapPotential χ (WithLp.toLp 2 (fun i => 1 + z.val i))) z‖ ^ 2 / 4 -
        Laplacian.laplacian (fun z : gapTangentSpace N =>
          pairAmbientGapPotential χ (WithLp.toLp 2 (fun i => 1 + z.val i))) z / 2 := by
  obtain ⟨C, hC, hb⟩ := (intrinsicGap_collision_criterion hN c hc χ hχ).1
  refine ⟨C, hC, fun z hz => ?_⟩
  have hne : (intrinsicGapDomain N)ᶜ.Nonempty := by
    have : Nontrivial (gapTangentSpace N) := tangent_nontrivial hN
    by_contra h
    apply (domain_bounded N).isCompact_closure.ne_univ
    apply eq_univ_of_forall
    intro x
    apply subset_closure
    by_contra hx
    exact h ⟨x, hx⟩
  rw [infDist_frontier_eq_infDist_compl (intrinsicGapDomain_isOpen N) hz hne]
  exact hb z hz

end Riesz2.GapRepresentation

namespace Riesz2.GapRepresentation
open AffineMetric IntrinsicScalarCore NeumannIsometryTransport RectangularFormTransport
open NeumannDifferentiatedTransport

variable {N : ℕ+}

/-- Internal native vector realization for Proposition 3.3. -/
theorem native_ambient_gradient
    (hN : 2 ≤ (N : ℕ)) {c : ℝ} (hc : 0 < c)
    {χ : ParticlePairData N} (hχ : AdmissibleParticlePairs hN χ c)
    {ν : Measure (gapTangentSpace N)}
    (hV : IsEuclideanGibbsPotential volume ν (intrinsicGapDomain N)
      (fun z => pairAmbientGapPotential χ (WithLp.toLp 2 (fun i => 1 + z.val i))))
    (G ψ : (form (intrinsicGapDomain_isOpen N) (domain_bounded N) hV).1)
    (hψ : ScalarPoissonSolution (form (intrinsicGapDomain_isOpen N) (domain_bounded N) hV) G ψ)
    (gG gψ : Lp (gapTangentSpace N) 2 ν)
    (hgG : (G.val, gG) ∈ neumannSobolevGraph ν (intrinsicGapDomain N))
    (hgψ : (ψ.val, gψ) ∈ neumannSobolevGraph ν (intrinsicGapDomain N)) :
    ∃ u : Fin (N : ℕ) → (form (intrinsicGapDomain_isOpen N) (domain_bounded N) hV).1,
      WeightedWeakSolution (form (intrinsicGapDomain_isOpen N) (domain_bounded N) hV)
        (fun z => hessianMatrix (pairAmbientGapPotential χ) (WithLp.toLp 2 (fun i => 1 + z.val i)))
        (zeroSumComponents _) (fun i => tangentCoordinateLp i gG) u ∧
      ∀ i, (u i).val = tangentCoordinateLp i gψ := by
  have := probability hV
  have := tangent_nontrivial hN
  let b := stdOrthonormalBasis ℝ (gapTangentSpace N)
  let Q := form (intrinsicGapDomain_isOpen N) (domain_bounded N) hV
  let M := fun z : gapTangentSpace N =>
    hessianMatrix (pairAmbientGapPotential χ) (WithLp.toLp 2 (fun i => 1 + z.val i))
  let V := fun z : gapTangentSpace N =>
    pairAmbientGapPotential χ (WithLp.toLp 2 (fun i => 1 + z.val i))
  obtain ⟨C, hC, hbar⟩ := intrinsicGap_frontier_barrier hN hc hχ
  obtain ⟨u, hu, hv⟩ := native_gradient_equation b.repr
    (Module.finrank_pos (R := ℝ) (M := gapTangentSpace N))
    (intrinsicGapDomain_isOpen N) (domain_bounded N) hV
    (div_pos hc (by positivity))
    (fun x hx v => intrinsicGapPotential_curvature hc hχ hx v) hC hbar G ψ hψ gG gψ hgG hgψ
  have hcomp : (fun z => (tangentBasisMatrix b).transpose * M z * tangentBasisMatrix b) =ᵐ[ν]
      fun z => hessianMatrix (V ∘ b.repr.symm) (b.repr z) :=
    (supported (intrinsicGapDomain_isOpen N) hV).mono (fun z hz => tangentBasisMatrix_hessian b hχ hz)
  have hut : WeightedWeakSolution Q (fun z => (tangentBasisMatrix b).transpose * M z * tangentBasisMatrix b)
      ⊤ (fun i => coordinateValue b.repr i gG) u :=
    (MatrixFieldTransport.weak_congr Q hcomp ⊤ _ u).mpr hu
  have hua := (weightedWeakSolution_tupleMap Q (tangentBasisMatrix b)
    (tangentBasisMatrix_orthonormal b) M (fun i => coordinateValue b.repr i gG) u).mpr hut
  refine ⟨tupleMap (tangentBasisMatrix b) u, ?_, ?_⟩
  · simpa only [tangentBasisMatrix_range, coordinateValue, tangentBasisMatrix_native_components] using hua
  · intro i
    rw [tupleMap_value]
    simp_rw [hv]
    exact congrFun (tangentBasisMatrix_native_components b ν gψ) i

end Riesz2.GapRepresentation

namespace Riesz2.GapRepresentation
open AffineMetric IntrinsicScalarCore NeumannIsometryTransport RectangularFormTransport

/-- Native coordinate coercivity for Proposition 3.3. -/
theorem ambientHessian_coordinate_lower
    {N : ℕ+} {hN : 2 ≤ (N : ℕ)} {c : ℝ} (hc : 0 < c)
    {χ : ParticlePairData N} (hχ : AdmissibleParticlePairs hN χ c)
    {z : gapTangentSpace N} (hz : z ∈ intrinsicGapDomain N)
    (t : Fin (N : ℕ) → ℝ) (ht : t ∈ zeroSumComponents _) :
    c / (2 * (N : ℝ)) * (∑ i, t i ^ 2) ≤ ∑ i, ∑ j, t i *
      hessianMatrix (pairAmbientGapPotential χ) (WithLp.toLp 2 (fun i => 1 + z.val i)) i j * t j := by
  let v : gapTangentSpace N := ⟨WithLp.toLp 2 t, ht⟩
  have hn : ‖v‖ ^ 2 = ∑ i, t i ^ 2 := by
    change ‖(WithLp.toLp 2 t : EuclideanSpace ℝ (Fin (N : ℕ)))‖ ^ 2 = _
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Real.norm_eq_abs, sq_abs]
  have he := ambientHessian_tangent_lower hc hχ hz v
  rw [hn] at he
  exact he

/-- Full-domain vector uniqueness and minimum for the actual gap Hessian,
Proposition 3.3. This internal criterion is applied only
after constructing the scalar solution's gradient. -/
theorem ambient_solution_unique_minimum
    {N : ℕ+} {hN : 2 ≤ (N : ℕ)} {c : ℝ} (hc : 0 < c)
    {χ : ParticlePairData N} (hχ : AdmissibleParticlePairs hN χ c)
    {ν : Measure (gapTangentSpace N)}
    (hV : IsEuclideanGibbsPotential volume ν (intrinsicGapDomain N)
      (fun z => pairAmbientGapPotential χ (WithLp.toLp 2 (fun i => 1 + z.val i))))
    (v : Fin (N : ℕ) → Lp ℝ 2 ν) :
    let Q := form (intrinsicGapDomain_isOpen N) (domain_bounded N) hV
    let M := fun z : gapTangentSpace N =>
      hessianMatrix (pairAmbientGapPotential χ) (WithLp.toLp 2 (fun i => 1 + z.val i))
    ∀ u : Fin (N : ℕ) → Q.1, WeightedWeakSolution Q M (zeroSumComponents _) v u →
      (∀ w : Fin (N : ℕ) → Q.1, WeightedWeakSolution Q M (zeroSumComponents _) v w → w = u) ∧
      (∀ w : Fin (N : ℕ) → Q.1, WeightedFormDomain Q M (zeroSumComponents _) w →
        let Ju := (∑ i, Q.2 (u i) (u i)) +
          (∫ z, matrixFieldPair M (fun i => (u i).val) (fun i => (u i).val) z ∂ν) -
            2 * (∑ i, inner ℝ (v i) (u i).val)
        let Jw := (∑ i, Q.2 (w i) (w i)) +
          (∫ z, matrixFieldPair M (fun i => (w i).val) (fun i => (w i).val) z ∂ν) -
            2 * (∑ i, inner ℝ (v i) (w i).val)
        Ju ≤ Jw ∧ (Jw = Ju → w = u)) := by
  intro Q M u hu
  have hsupp := supported (intrinsicGapDomain_isOpen N) hV
  have hclosed := closed_dirichlet (intrinsicGapDomain_isOpen N) (domain_bounded N) hV
  have hκ : 0 < c / (2 * (N : ℝ)) := div_pos hc (by positivity)
  have hma : ∀ᵐ z ∂ν, (M z).PosSemidef := hsupp.mono fun z hz =>
    ambientHessian_posSemidef hc.le hχ hz
  have hlow : ∀ᵐ z ∂ν, ∀ t ∈ zeroSumComponents (Fin (N : ℕ)),
      c / (2 * (N : ℝ)) * (∑ i, t i ^ 2) ≤ ∑ i, ∑ j, t i * M z i j * t j :=
    hsupp.mono fun z hz t ht => ambientHessian_coordinate_lower hc hχ hz t ht
  have hmeas : ∀ i j, Measurable (fun z => M z i j) := ambientHessian_measurable χ
  have huniq := MatrixEnergy.weightedWeakSolution_unique Q hclosed M (zeroSumComponents _) hma
    (c / (2 * (N : ℝ))) hκ hlow hmeas v
  exact ⟨fun w hw => (huniq w hw).trans (huniq u hu).symm,
    MatrixEnergy.weightedWeakSolution_unique_minimum Q hclosed M (zeroSumComponents _) hma
      (c / (2 * (N : ℝ))) hκ hlow hmeas v u hu⟩

/-- Extract the unique intrinsic weak gradient on the abstract scalar carrier,
Proposition 3.3. -/
theorem weak_gradient_exists {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] {ν : Measure E} {Ω : Set E}
    (Q : ScalarFormData ν) (hQ : IsNeumannRealization Ω Q) (f : Q.1) :
    ∃ g : Lp E 2 ν, (f.val, g) ∈ neumannSobolevGraph ν Ω :=
  (hQ.1 f.val).mp f.property

/-- Pullback L² under an identified gap law, Proposition 3.3. -/
theorem memLp_pullback_of_eq {N : ℕ+} {μ : Measure (Riesz1.Configuration N)}
    {ν : Measure (gapTangentSpace N)} (hpush : intrinsicGapLaw μ = ν) (G : Lp ℝ 2 ν) :
    MemLp (fun X : Riesz1.Configuration N =>
      G (centeredGapChart N (WithLp.toLp 2 (gapVector X)))) 2 μ := by
  subst ν
  exact memLp_pullback G

/-- Variance under an identified gap law, Proposition 3.3. -/
theorem variance_pullback_of_eq {N : ℕ+} {μ : Measure (Riesz1.Configuration N)}
    {ν : Measure (gapTangentSpace N)} (hpush : intrinsicGapLaw μ = ν) (G : Lp ℝ 2 ν) :
    ProbabilityTheory.variance (fun X : Riesz1.Configuration N =>
      G (centeredGapChart N (WithLp.toLp 2 (gapVector X)))) μ = ProbabilityTheory.variance G ν := by
  subst ν
  exact variance_pullback G

/-- Native gradient transport on an identified scalar realization,
Proposition 3.3. Internal carrier bridge. -/
theorem native_ambient_gradient_realized
    {N : ℕ+} (hN : 2 ≤ (N : ℕ)) {c : ℝ} (hc : 0 < c)
    {χ : ParticlePairData N} (hχ : AdmissibleParticlePairs hN χ c)
    {ν : Measure (gapTangentSpace N)}
    (hV : IsEuclideanGibbsPotential volume ν (intrinsicGapDomain N)
      (fun z => pairAmbientGapPotential χ (WithLp.toLp 2 (fun i => 1 + z.val i))))
    (Q : ScalarFormData ν)
    (hQeq : Q = form (intrinsicGapDomain_isOpen N) (domain_bounded N) hV)
    (G ψ : Q.1)
    (hψ : ScalarPoissonSolution Q G ψ)
    (gG gψ : Lp (gapTangentSpace N) 2 ν)
    (hgG : (G.val, gG) ∈ neumannSobolevGraph ν (intrinsicGapDomain N))
    (hgψ : (ψ.val, gψ) ∈ neumannSobolevGraph ν (intrinsicGapDomain N)) :
    ∃ u : Fin (N : ℕ) → Q.1,
      WeightedWeakSolution Q
        (fun z => hessianMatrix (pairAmbientGapPotential χ) (WithLp.toLp 2 (fun i => 1 + z.val i)))
        (zeroSumComponents _) (fun i => tangentCoordinateLp i gG) u ∧
      ∀ i, (u i).val = tangentCoordinateLp i gψ := by
  subst Q
  exact native_ambient_gradient hN hc hχ hV G ψ hψ gG gψ hgG hgψ

/-- Native minimum and uniqueness on an identified scalar realization,
Proposition 3.3. Internal carrier bridge. -/
theorem ambient_solution_unique_minimum_realized
    {N : ℕ+} {hN : 2 ≤ (N : ℕ)} {c : ℝ} (hc : 0 < c)
    {χ : ParticlePairData N} (hχ : AdmissibleParticlePairs hN χ c)
    {ν : Measure (gapTangentSpace N)}
    (hV : IsEuclideanGibbsPotential volume ν (intrinsicGapDomain N)
      (fun z => pairAmbientGapPotential χ (WithLp.toLp 2 (fun i => 1 + z.val i))))
    (Q : ScalarFormData ν)
    (hQeq : Q = form (intrinsicGapDomain_isOpen N) (domain_bounded N) hV)
    (v : Fin (N : ℕ) → Lp ℝ 2 ν) :
    let M := fun z : gapTangentSpace N =>
      hessianMatrix (pairAmbientGapPotential χ) (WithLp.toLp 2 (fun i => 1 + z.val i))
    ∀ u : Fin (N : ℕ) → Q.1, WeightedWeakSolution Q M (zeroSumComponents _) v u →
      (∀ w : Fin (N : ℕ) → Q.1, WeightedWeakSolution Q M (zeroSumComponents _) v w → w = u) ∧
      (∀ w : Fin (N : ℕ) → Q.1, WeightedFormDomain Q M (zeroSumComponents _) w →
        let Ju := (∑ i, Q.2 (u i) (u i)) +
          (∫ z, matrixFieldPair M (fun i => (u i).val) (fun i => (u i).val) z ∂ν) -
            2 * (∑ i, inner ℝ (v i) (u i).val)
        let Jw := (∑ i, Q.2 (w i) (w i)) +
          (∫ z, matrixFieldPair M (fun i => (w i).val) (fun i => (w i).val) z ∂ν) -
            2 * (∑ i, inner ℝ (v i) (w i).val)
        Ju ≤ Jw ∧ (Jw = Ju → w = u)) := by
  subst Q
  exact ambient_solution_unique_minimum hc hχ hV v

/-- Scalar solvability on an identified native realization,
Proposition 3.3. Internal carrier bridge. -/
theorem scalar_solution_exists_realized
    {N : ℕ+} {hN : 2 ≤ (N : ℕ)} {c : ℝ} (hc : 0 < c)
    {χ : ParticlePairData N} (hχ : AdmissibleParticlePairs hN χ c)
    {ν : Measure (gapTangentSpace N)}
    (hV : IsEuclideanGibbsPotential volume ν (intrinsicGapDomain N)
      (fun z => pairAmbientGapPotential χ (WithLp.toLp 2 (fun i => 1 + z.val i))))
    (Q : ScalarFormData ν)
    (hQeq : Q = form (intrinsicGapDomain_isOpen N) (domain_bounded N) hV)
    (G : Q.1) : ∃! ψ : Q.1, ScalarPoissonSolution Q G ψ := by
  subst Q
  have := tangent_nontrivial hN
  exact IntrinsicScalarPoisson.scalarPoissonSolution_existsUnique
    (intrinsicGapDomain_isOpen N) (domain_bounded N) (domain_convex N) hV
    (div_pos hc (by positivity)) (fun _ hy => intrinsicGapPotential_curvature hc hχ hy) G

/-- Compact ambient tests in an identified scalar carrier,
Proposition 3.3. Internal carrier bridge. -/
theorem compact_test_representatives_realized
    {N : ℕ+} {ν : Measure (gapTangentSpace N)} {V : gapTangentSpace N → ℝ}
    (hV : IsEuclideanGibbsPotential volume ν (intrinsicGapDomain N) V)
    (Q : ScalarFormData ν)
    (hQeq : Q = form (intrinsicGapDomain_isOpen N) (domain_bounded N) hV)
    (h : Fin (N : ℕ) → gapTangentSpace N → ℝ)
    (hh : ∀ i, ContDiff ℝ ∞ (h i) ∧ HasCompactSupport (h i) ∧ tsupport (h i) ⊆ intrinsicGapDomain N) :
    ∃ k : Fin (N : ℕ) → Q.1, ∀ᵐ z ∂ν, ∀ i, (k i).val z = h i z := by
  subst Q
  obtain ⟨k, hk, _⟩ := compact_test_representatives (intrinsicGapDomain_isOpen N) (domain_bounded N) hV h hh
  exact ⟨k, hk⟩

/-- The complete vector representation of each particular scalar solution,
Proposition 3.3. Internal assembly over the actual gap law. -/
theorem solution_gap_representation
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (c : ℝ) (hc : 0 < c)
    (χ : ParticlePairData N) (hχ : AdmissibleParticlePairs hN χ c)
    (μ : Measure (Riesz1.Configuration N))
    (ν : Measure (gapTangentSpace N)) (hpush : intrinsicGapLaw μ = ν)
    (hV : IsEuclideanGibbsPotential volume ν (intrinsicGapDomain N)
      (fun z => pairAmbientGapPotential χ (WithLp.toLp 2 (fun i => 1 + z.val i))))
    (Q : ScalarFormData ν)
    (hQeq : Q = form (intrinsicGapDomain_isOpen N) (domain_bounded N) hV)
    (G ψ : Q.1)
    (hψ : ScalarPoissonSolution Q G ψ)
    (gG : Lp (gapTangentSpace N) 2 ν)
    (hgG : (G.val, gG) ∈ neumannSobolevGraph ν (intrinsicGapDomain N)) :
    let Ω := intrinsicGapDomain N
    let M := fun z : gapTangentSpace N =>
      hessianMatrix (pairAmbientGapPotential χ) (WithLp.toLp 2 (fun i => 1 + z.val i))
    let v := fun i => tangentCoordinateLp i gG
    ∃ (u : Fin (N : ℕ) → Q.1) (gψ : Lp (gapTangentSpace N) 2 ν),
        WeightedWeakSolution Q M (zeroSumComponents _) v u ∧
        (∀ w : Fin (N : ℕ) → Q.1,
          WeightedWeakSolution Q M (zeroSumComponents _) v w → w = u) ∧
        (ψ.val, gψ) ∈ neumannSobolevGraph ν Ω ∧
        (∀ᵐ z ∂ν, ∀ i, (u i).val z = (gψ z).val i) ∧
        MemLp (fun X : Riesz1.Configuration N =>
          G.val (centeredGapChart N (WithLp.toLp 2 (gapVector X)))) 2 μ ∧
        ProbabilityTheory.variance (fun X : Riesz1.Configuration N =>
          G.val (centeredGapChart N (WithLp.toLp 2 (gapVector X)))) μ =
            ∑ i, inner ℝ (v i) (u i).val ∧
        (∀ (K : Q.1) (gK : Lp (gapTangentSpace N) 2 ν),
          (K.val, gK) ∈ neumannSobolevGraph ν Ω →
          Integrable K.val ν ∧
          ProbabilityTheory.covariance G.val K.val ν = inner ℝ gK gψ) ∧
        (∀ w : Fin (N : ℕ) → Q.1, WeightedFormDomain Q M (zeroSumComponents _) w →
          let Ju := (∑ i, Q.2 (u i) (u i)) +
            (∫ z, matrixFieldPair M (fun i => (u i).val) (fun i => (u i).val) z ∂ν) -
              2 * (∑ i, inner ℝ (v i) (u i).val)
          let Jw := (∑ i, Q.2 (w i) (w i)) +
            (∫ z, matrixFieldPair M (fun i => (w i).val) (fun i => (w i).val) z ∂ν) -
              2 * (∑ i, inner ℝ (v i) (w i).val)
          Ju ≤ Jw ∧ (Jw = Ju → w = u)) ∧
        (∃ du : Fin (N : ℕ) → Lp (gapTangentSpace N) 2 ν,
          (∀ i, ((u i).val, du i) ∈ neumannSobolevGraph ν Ω) ∧
          (∑ i, Q.2 (u i) (u i)) = ∑ i, ‖du i‖ ^ 2) ∧
        (∀ φ : gapTangentSpace N → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Ω → Integrable (fun z => gapMultiplierField N Q M v u z * φ z) ν) ∧
        (∀ h : Fin (N : ℕ) → gapTangentSpace N → ℝ,
          (∀ i, ContDiff ℝ (⊤ : ℕ∞) (h i) ∧ HasCompactSupport (h i) ∧ tsupport (h i) ⊆ Ω) →
          ∃ k : Fin (N : ℕ) → Q.1,
            (∀ᵐ z ∂ν, ∀ i, (k i).val z = h i z) ∧
            Integrable (matrixFieldPair M (fun i => (u i).val) (fun i => (k i).val)) ν ∧
            (∑ i, Q.2 (u i) (k i)) +
              (∫ z, matrixFieldPair M (fun i => (u i).val) (fun i => (k i).val) z ∂ν) =
                (∑ i, inner ℝ (v i) (k i).val) +
                  ∫ z, gapMultiplierField N Q M v u z * (∑ i, h i z) ∂ν) := by
  intro Ω M v
  have := probability hV
  let hΩ := intrinsicGapDomain_isOpen N
  let hB := domain_bounded N
  have hQ : IsNeumannRealization (intrinsicGapDomain N) Q := by
    rw [hQeq]
    exact realization hΩ hB hV
  have hsupp := supported hΩ hV
  have hex : ∃ g : Lp (gapTangentSpace N) 2 ν,
      (ψ.val, g) ∈ neumannSobolevGraph ν Ω :=
    @weak_gradient_exists (gapTangentSpace N) _ _ _ _ ν (intrinsicGapDomain N) Q hQ ψ
  obtain ⟨gψ, hgψ⟩ := hex
  have hnative : ∃ u : Fin (N : ℕ) → Q.1,
      WeightedWeakSolution Q M (zeroSumComponents _) v u ∧
      ∀ i, (u i).val = tangentCoordinateLp i gψ :=
    native_ambient_gradient_realized (N := N) (c := c) (χ := χ) (ν := ν)
      hN hc hχ hV Q hQeq G ψ hψ gG gψ hgG hgψ
  obtain ⟨u, hu, hug⟩ := hnative
  have hboth :
      (∀ w : Fin (N : ℕ) → Q.1, WeightedWeakSolution Q M (zeroSumComponents _) v w → w = u) ∧
      (∀ w : Fin (N : ℕ) → Q.1, WeightedFormDomain Q M (zeroSumComponents _) w →
        let Ju := (∑ i, Q.2 (u i) (u i)) +
          (∫ z, matrixFieldPair M (fun i => (u i).val) (fun i => (u i).val) z ∂ν) -
            2 * (∑ i, inner ℝ (v i) (u i).val)
        let Jw := (∑ i, Q.2 (w i) (w i)) +
          (∫ z, matrixFieldPair M (fun i => (w i).val) (fun i => (w i).val) z ∂ν) -
            2 * (∑ i, inner ℝ (v i) (w i).val)
        Ju ≤ Jw ∧ (Jw = Ju → w = u)) :=
    ambient_solution_unique_minimum_realized (N := N) (hN := hN) (c := c) (χ := χ) (ν := ν)
      hc hχ hV Q hQeq v u hu
  obtain ⟨huniq, hmin⟩ := hboth
  have hcov := covariance_of_scalar_solution Q hQ G ψ hψ gψ hgψ
  refine ⟨u, gψ, hu, huniq, hgψ, ?_, memLp_pullback_of_eq (N := N) hpush G.val, ?_, hcov,
    hmin,
    component_gradients Q hQ u, ?_, ?_⟩
  · simp_rw [hug]
    exact ae_all_iff.mpr (fun i => tangentCoordinateLp_ae i gψ)
  · simp_rw [hug]
    rw [variance_pullback_of_eq (N := N) hpush G.val, tangentCoordinateLp_inner]
    exact (ProbabilityTheory.covariance_self (Lp.aestronglyMeasurable G.val).aemeasurable).symm.trans
      (hcov G gG hgG).2
  · intro φ hφ hcφ hφΩ
    exact ConstrainedNormalMultiplier.multiplier_test_integrable N Q M hΩ
      (ambientHessian_continuousOn hχ) v u φ hφ.continuous hcφ hφΩ
  · intro h hh
    obtain ⟨k, hk⟩ := compact_test_representatives_realized (N := N) hV Q hQeq h hh
    have hsym : ∀ᵐ z ∂ν, ∀ i j, M z i j = M z j i := hsupp.mono fun z hz =>
      ambientHessian_symmetric hχ hz
    have ha := ConstrainedNormalMultiplier.ambient_equation_of_tangent_solution N Q M hΩ
      (ambientHessian_continuousOn hχ) hsym v u hu k h
      (fun i => ⟨(hh i).1.continuous, (hh i).2⟩) hk
    exact ⟨k, hk, ha.1, ha.2.2⟩


/-- Every scalar solution has the complete native vector representation,
Proposition 3.3. Internal assembly over an actual gap law. -/
theorem observable_gap_representation
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (c : ℝ) (hc : 0 < c)
    (χ : ParticlePairData N) (hχ : AdmissibleParticlePairs hN χ c)
    (μ : Measure (Riesz1.Configuration N))
    (ν : Measure (gapTangentSpace N)) (hpush : intrinsicGapLaw μ = ν)
    (hV : IsEuclideanGibbsPotential volume ν (intrinsicGapDomain N)
      (fun z => pairAmbientGapPotential χ (WithLp.toLp 2 (fun i => 1 + z.val i))))
    (Q : ScalarFormData ν)
    (hQeq : Q = form (intrinsicGapDomain_isOpen N) (domain_bounded N) hV) :
    let Ω := intrinsicGapDomain N
    let M := fun z : gapTangentSpace N =>
      hessianMatrix (pairAmbientGapPotential χ) (WithLp.toLp 2 (fun i => 1 + z.val i))
    ∀ G : Q.1, ∃ (gG : Lp (gapTangentSpace N) 2 ν) (v : Fin (N : ℕ) → Lp ℝ 2 ν),
      (G.val, gG) ∈ neumannSobolevGraph ν Ω ∧
      (∀ᵐ z ∂ν, ∀ i, v i z = (gG z).val i) ∧
      (∃! ψ : Q.1, ScalarPoissonSolution Q G ψ) ∧
      ∀ ψ : Q.1, ScalarPoissonSolution Q G ψ →
      ∃ (u : Fin (N : ℕ) → Q.1) (gψ : Lp (gapTangentSpace N) 2 ν),
        WeightedWeakSolution Q M (zeroSumComponents _) v u ∧
        (∀ w : Fin (N : ℕ) → Q.1,
          WeightedWeakSolution Q M (zeroSumComponents _) v w → w = u) ∧
        (ψ.val, gψ) ∈ neumannSobolevGraph ν Ω ∧
        (∀ᵐ z ∂ν, ∀ i, (u i).val z = (gψ z).val i) ∧
        MemLp (fun X : Riesz1.Configuration N =>
          G.val (centeredGapChart N (WithLp.toLp 2 (gapVector X)))) 2 μ ∧
        ProbabilityTheory.variance (fun X : Riesz1.Configuration N =>
          G.val (centeredGapChart N (WithLp.toLp 2 (gapVector X)))) μ =
            ∑ i, inner ℝ (v i) (u i).val ∧
        (∀ (K : Q.1) (gK : Lp (gapTangentSpace N) 2 ν),
          (K.val, gK) ∈ neumannSobolevGraph ν Ω →
          Integrable K.val ν ∧
          ProbabilityTheory.covariance G.val K.val ν = inner ℝ gK gψ) ∧
        (∀ w : Fin (N : ℕ) → Q.1, WeightedFormDomain Q M (zeroSumComponents _) w →
          let Ju := (∑ i, Q.2 (u i) (u i)) +
            (∫ z, matrixFieldPair M (fun i => (u i).val) (fun i => (u i).val) z ∂ν) -
              2 * (∑ i, inner ℝ (v i) (u i).val)
          let Jw := (∑ i, Q.2 (w i) (w i)) +
            (∫ z, matrixFieldPair M (fun i => (w i).val) (fun i => (w i).val) z ∂ν) -
              2 * (∑ i, inner ℝ (v i) (w i).val)
          Ju ≤ Jw ∧ (Jw = Ju → w = u)) ∧
        (∃ du : Fin (N : ℕ) → Lp (gapTangentSpace N) 2 ν,
          (∀ i, ((u i).val, du i) ∈ neumannSobolevGraph ν Ω) ∧
          (∑ i, Q.2 (u i) (u i)) = ∑ i, ‖du i‖ ^ 2) ∧
        (∀ φ : gapTangentSpace N → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Ω → Integrable (fun z => gapMultiplierField N Q M v u z * φ z) ν) ∧
        (∀ h : Fin (N : ℕ) → gapTangentSpace N → ℝ,
          (∀ i, ContDiff ℝ (⊤ : ℕ∞) (h i) ∧ HasCompactSupport (h i) ∧ tsupport (h i) ⊆ Ω) →
          ∃ k : Fin (N : ℕ) → Q.1,
            (∀ᵐ z ∂ν, ∀ i, (k i).val z = h i z) ∧
            Integrable (matrixFieldPair M (fun i => (u i).val) (fun i => (k i).val)) ν ∧
            (∑ i, Q.2 (u i) (k i)) +
              (∫ z, matrixFieldPair M (fun i => (u i).val) (fun i => (k i).val) z ∂ν) =
                (∑ i, inner ℝ (v i) (k i).val) +
                  ∫ z, gapMultiplierField N Q M v u z * (∑ i, h i z) ∂ν) := by
  intro Ω M
  have := tangent_nontrivial hN
  have := probability hV
  let hΩ := intrinsicGapDomain_isOpen N
  let hB := domain_bounded N
  have hQ : IsNeumannRealization (intrinsicGapDomain N) Q := by
    rw [hQeq]
    exact realization hΩ hB hV
  have hκ : 0 < c / (2 * (N : ℝ)) := div_pos hc (by positivity)
  have hsupp := supported hΩ hV
  intro G
  have hex : ∃ g : Lp (gapTangentSpace N) 2 ν,
      (G.val, g) ∈ neumannSobolevGraph ν Ω :=
    @weak_gradient_exists (gapTangentSpace N) _ _ _ _ ν (intrinsicGapDomain N) Q hQ G
  obtain ⟨gG, hgG⟩ := hex
  have hsol := scalar_solution_exists_realized (N := N) (hN := hN) (c := c) (χ := χ) (ν := ν) hc hχ hV Q hQeq G
  refine ⟨gG, fun i => tangentCoordinateLp i gG, hgG,
    ae_all_iff.mpr (fun i => tangentCoordinateLp_ae i gG), hsol, fun ψ hψ => ?_⟩
  exact solution_gap_representation N hN c hc χ hχ μ ν hpush hV Q hQeq G ψ hψ gG hgG

/-- See Proposition 3.3 of the paper: the complete gap representation. -/
theorem gap_representation :
  ∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (c : ℝ), 0 < c →
  ∀ χ : ParticlePairData N, AdmissibleParticlePairs hN χ c →
  ∃ (hMeas : Measurable (fun X : Riesz1.Configuration N =>
      ENNReal.ofReal (Real.exp (-particlePairEnergy χ (WithLp.toLp 2 X.val)))))
    (hZ : 0 < pairGibbsNormalizer χ ∧ pairGibbsNormalizer χ < ⊤),
  let μ := pairGibbsMeasure χ hMeas hZ
  let ν := intrinsicGapLaw μ
  let Ω := intrinsicGapDomain N
  let M := fun z : gapTangentSpace N =>
    hessianMatrix (pairAmbientGapPotential χ) (WithLp.toLp 2 (fun i => 1 + z.val i))
  IsProbabilityMeasure μ ∧ IsProbabilityMeasure ν ∧
  ∃ Q : ScalarFormData ν,
    IsEuclideanGibbsPotential volume ν Ω
      (fun z => pairAmbientGapPotential χ (WithLp.toLp 2 (fun i => 1 + z.val i))) ∧
    IsNeumannRealization Ω Q ∧ IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
    ∀ G : Q.1, ∃ (gG : Lp (gapTangentSpace N) 2 ν) (v : Fin (N : ℕ) → Lp ℝ 2 ν),
      (G.val, gG) ∈ neumannSobolevGraph ν Ω ∧
      (∀ᵐ z ∂ν, ∀ i, v i z = (gG z).val i) ∧
      (∃! ψ : Q.1, ScalarPoissonSolution Q G ψ) ∧
      ∀ ψ : Q.1, ScalarPoissonSolution Q G ψ →
      ∃ (u : Fin (N : ℕ) → Q.1) (gψ : Lp (gapTangentSpace N) 2 ν),
        WeightedWeakSolution Q M (zeroSumComponents _) v u ∧
        (∀ w : Fin (N : ℕ) → Q.1,
          WeightedWeakSolution Q M (zeroSumComponents _) v w → w = u) ∧
        (ψ.val, gψ) ∈ neumannSobolevGraph ν Ω ∧
        (∀ᵐ z ∂ν, ∀ i, (u i).val z = (gψ z).val i) ∧
        MemLp (fun X : Riesz1.Configuration N =>
          G.val (centeredGapChart N (WithLp.toLp 2 (gapVector X)))) 2 μ ∧
        ProbabilityTheory.variance (fun X : Riesz1.Configuration N =>
          G.val (centeredGapChart N (WithLp.toLp 2 (gapVector X)))) μ =
            ∑ i, inner ℝ (v i) (u i).val ∧
        (∀ (K : Q.1) (gK : Lp (gapTangentSpace N) 2 ν),
          (K.val, gK) ∈ neumannSobolevGraph ν Ω →
          Integrable K.val ν ∧
          ProbabilityTheory.covariance G.val K.val ν = inner ℝ gK gψ) ∧
        (∀ w : Fin (N : ℕ) → Q.1, WeightedFormDomain Q M (zeroSumComponents _) w →
          let Ju := (∑ i, Q.2 (u i) (u i)) +
            (∫ z, matrixFieldPair M (fun i => (u i).val) (fun i => (u i).val) z ∂ν) -
              2 * (∑ i, inner ℝ (v i) (u i).val)
          let Jw := (∑ i, Q.2 (w i) (w i)) +
            (∫ z, matrixFieldPair M (fun i => (w i).val) (fun i => (w i).val) z ∂ν) -
              2 * (∑ i, inner ℝ (v i) (w i).val)
          Ju ≤ Jw ∧ (Jw = Ju → w = u)) ∧
        (∃ du : Fin (N : ℕ) → Lp (gapTangentSpace N) 2 ν,
          (∀ i, ((u i).val, du i) ∈ neumannSobolevGraph ν Ω) ∧
          (∑ i, Q.2 (u i) (u i)) = ∑ i, ‖du i‖ ^ 2) ∧
        (∀ φ : gapTangentSpace N → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Ω → Integrable (fun z => gapMultiplierField N Q M v u z * φ z) ν) ∧
        (∀ h : Fin (N : ℕ) → gapTangentSpace N → ℝ,
          (∀ i, ContDiff ℝ (⊤ : ℕ∞) (h i) ∧ HasCompactSupport (h i) ∧ tsupport (h i) ⊆ Ω) →
          ∃ k : Fin (N : ℕ) → Q.1,
            (∀ᵐ z ∂ν, ∀ i, (k i).val z = h i z) ∧
            Integrable (matrixFieldPair M (fun i => (u i).val) (fun i => (k i).val)) ν ∧
            (∑ i, Q.2 (u i) (k i)) +
              (∫ z, matrixFieldPair M (fun i => (u i).val) (fun i => (k i).val) z ∂ν) =
                (∑ i, inner ℝ (v i) (k i).val) +
                  ∫ z, gapMultiplierField N Q M v u z * (∑ i, h i z) ∂ν) := by
  intro N hN c hc χ hχ
  have := tangent_nontrivial hN
  let hm := pairGibbsWeight_measurable hχ
  let hZ := (particle_hessian_normalization hN c hc χ hχ).1
  let μ := pairGibbsMeasure χ hm hZ
  let ν := intrinsicGapLaw μ
  have hp : IsProbabilityMeasure μ := by
    rw [show μ = (Riesz1.hsGibbsProbability (libraryPairs hχ) hc : Measure _) from
      pairGibbsMeasure_eq_library hc hχ]
    infer_instance
  have hV := intrinsicGapLaw_gibbsPotential hN c hc χ hχ
  have hν : IsProbabilityMeasure ν := probability hV
  have := hν
  let hΩ := intrinsicGapDomain_isOpen N
  let hB := domain_bounded N
  let Q := form hΩ hB hV
  have hQ : IsNeumannRealization (intrinsicGapDomain N) Q := realization hΩ hB hV
  have hclosed := closed_dirichlet hΩ hB hV
  exact ⟨hm, hZ, hp, hν, Q, hV, hQ, hclosed, conservative hΩ hB hV,
    observable_gap_representation N hN c hc χ hχ μ ν rfl hV Q rfl⟩

end Riesz2.GapRepresentation
