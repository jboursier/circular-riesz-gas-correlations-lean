/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.ScalarPoisson
public import Riesz2.HelfferSjostrand.IntrinsicIntegrationByParts
public import Riesz2.Frozen.WeightedFormDomain
public import Mathlib.Probability.Moments.Covariance

/-!
# Differentiating the intrinsic Poisson equation

Steps in the proof of Proposition 3.3: covariance on the whole scalar
form domain and convergence of scalar graph approximants in value and
weak-gradient norms. The compact Bochner identity gives the Cauchy estimate
in diffusion plus Hessian energy. Compact gradients belong to the
finite-energy domain. All gradients use the intrinsic metric.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff Laplacian

namespace Riesz2.DifferentiatedPoisson

open IntrinsicScalarCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {U : Set E} {ρ : Measure E} {V : E → ℝ}

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Internal scalar pairing used in the proof of Proposition 3.3.
Centering only the first factor gives the covariance, with every product
integrable because both factors are L². -/
theorem covariance_eq_centered_inner [IsProbabilityMeasure ρ] (G K : Lp ℝ 2 ρ) :
    ProbabilityTheory.covariance G K ρ = inner ℝ (Riesz1.poissonCenter ρ G) K := by
  rw [ProbabilityTheory.covariance_eq_sub (Lp.memLp G) (Lp.memLp K),
    Riesz1.poisson_inner_eq_integral]
  have hi : Integrable (fun x => G x * K x) ρ := (Lp.memLp G).integrable_mul (Lp.memLp K)
  have hK : Integrable K ρ := (Lp.memLp K).integrable one_le_two
  rw [integral_congr_ae ((Riesz1.poissonCenter_ae ρ G).mono
    (fun x hx => congrArg (· * K x) hx))]
  simp_rw [sub_mul]
  rw [integral_sub hi (hK.const_mul _), integral_const_mul]
  rfl

/-- Covariance part of the proof of Proposition 3.3, for an
arbitrary generator graph pair. It needs no collision barrier. Both the scalar
and vector integrands are explicitly integrable, and the tests range over the
whole Neumann form domain. -/
theorem covariance_of_graph (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) (G : Lp ℝ 2 ρ)
    (ψ : ScalarForm.Domain (jet hU hB hV))
    (hψ : (ψ, @Riesz1.poissonCenter E _ ρ (probability hV) G) ∈
      ScalarForm.neumannGraph (jet hU hB hV))
    (K : ScalarForm.Domain (jet hU hB hV)) :
    Integrable (fun x => (G x - ∫ y, G y ∂ρ) *
      (ScalarForm.value (jet hU hB hV) K x -
        ∫ y, ScalarForm.value (jet hU hB hV) K y ∂ρ)) ρ ∧
    Integrable (fun x => inner ℝ (ScalarForm.deriv (jet hU hB hV) ψ x)
      (ScalarForm.deriv (jet hU hB hV) K x)) ρ ∧
    ProbabilityTheory.covariance G (ScalarForm.value (jet hU hB hV) K) ρ =
      ∫ x, inner ℝ (ScalarForm.deriv (jet hU hB hV) ψ x)
        (ScalarForm.deriv (jet hU hB hV) K x) ∂ρ := by
  have := probability hV
  refine ⟨?_, L2.integrable_inner _ _, ?_⟩
  · exact ((Lp.memLp G).sub (memLp_const _)).integrable_mul
      ((Lp.memLp (ScalarForm.value (jet hU hB hV) K)).sub (memLp_const _))
  · rw [covariance_eq_centered_inner, ← hψ K]
    exact ScalarForm.energy_integral _ _ _

/-- Existence and covariance in the proof of Proposition 3.3,
for every L² source, including every H¹ observable. -/
theorem exists_poisson_covariance [Nontrivial E] (hU : IsOpen U)
    (hB : Bornology.IsBounded U) (hc : Convex ℝ U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) {κ : ℝ} (hκ : 0 < κ)
    (hH : ∀ x ∈ U, ∀ h, κ * ‖h‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x h h)
    (G : Lp ℝ 2 ρ) :
    ∃ ψ : ScalarForm.Domain (jet hU hB hV),
      (∫ x, ScalarForm.value (jet hU hB hV) ψ x ∂ρ) = 0 ∧
      (ψ, @Riesz1.poissonCenter E _ ρ (probability hV) G) ∈
        ScalarForm.neumannGraph (jet hU hB hV) ∧
      ∀ K : ScalarForm.Domain (jet hU hB hV),
        Integrable (fun x => inner ℝ (ScalarForm.deriv (jet hU hB hV) ψ x)
          (ScalarForm.deriv (jet hU hB hV) K x)) ρ ∧
        ProbabilityTheory.covariance G (ScalarForm.value (jet hU hB hV) K) ρ =
          ∫ x, inner ℝ (ScalarForm.deriv (jet hU hB hV) ψ x)
            (ScalarForm.deriv (jet hU hB hV) K x) ∂ρ := by
  have := probability hV
  obtain ⟨f, ⟨hm, hf⟩, _⟩ := IntrinsicScalarPoisson.poisson_existsUnique hU hB hc hV hκ hH G
  rw [operator, ScalarForm.l2Operator_graph, ScalarForm.mem_l2Graph_iff] at hf
  obtain ⟨ψ, hv, hψ⟩ := hf
  refine ⟨ψ, hv ▸ hm, hψ, fun K => ?_⟩
  exact (covariance_of_graph hU hB hV G ψ hψ K).2

/-- Graph approximants used in the proof of Proposition 3.3
also converge in the actual scalar H¹ space, hence in weak gradient. The
gradient convergence is a consequence of the scalar graph convergence, not an
additional hypothesis. The approximants are compact interior smooth tests. -/
theorem graph_approximation_with_gradient [Nontrivial E] (hU : IsOpen U)
    (hB : Bornology.IsBounded U) (hV : IsEuclideanGibbsPotential volume ρ U V)
    {C : ℝ} (hC : 0 ≤ C)
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹ ^ 2 - C ≤
      ‖gradient V x‖ ^ 2 / 4 - Δ V x / 2)
    (ψ : ScalarForm.Domain (jet hU hB hV)) (a : Lp ℝ 2 ρ)
    (hψ : (ψ, a) ∈ ScalarForm.neumannGraph (jet hU hB hV)) :
    ∃ c : ℕ → compactTests U, ∃ b : ℕ → Lp ℝ 2 ρ,
      (∀ k, (ScalarForm.ofCore (jet hU hB hV) (c k).val, b k) ∈
        ScalarForm.neumannGraph (jet hU hB hV)) ∧
      Tendsto (fun k => ScalarForm.ofCore (jet hU hB hV) (c k).val) atTop (𝓝 ψ) ∧
      Tendsto b atTop (𝓝 a) ∧
      Tendsto (fun k => ScalarForm.deriv (jet hU hB hV)
        (ScalarForm.ofCore (jet hU hB hV) (c k).val)) atTop
        (𝓝 (ScalarForm.deriv (jet hU hB hV) ψ)) := by
  let J := jet hU hB hV
  have hp : (ScalarForm.value J ψ, a) ∈ (operator hU hB hV).graph := by
    rw [operator, ScalarForm.l2Operator_graph, ScalarForm.mem_l2Graph_iff]
    exact ⟨ψ, rfl, hψ⟩
  obtain ⟨c, b, hb, hv, ha⟩ := graph_approximation hU hB hV hC hbar hp
  have hb' (k) : (ScalarForm.ofCore J (c k).val, b k) ∈ ScalarForm.neumannGraph J := by
    have hh := hb k
    rw [operator, ScalarForm.l2Operator_graph, ScalarForm.mem_l2Graph_iff] at hh
    obtain ⟨v, hval, he⟩ := hh
    have heq := value_injective hU hB hV hval
    exact heq ▸ he
  have ht := ScalarForm.tendsto_form_of_tendsto_graph J _ b ψ a hb' hψ hv ha
  exact ⟨c, b, hb', ht, ha, (ScalarForm.deriv J).continuous.tendsto ψ |>.comp ht⟩

/-- A directional derivative of a compact interior scalar test is again a
compact interior scalar test. This is the concrete core used in the proof of Proposition 3.3. No Sobolev space is redefined. -/
def compactDerivative (f : compactTests U) (v : E) : compactTests U := by
  let g : E → ℝ := fun x => fderiv ℝ f.val.val x v
  have hg : ContDiff ℝ ∞ g :=
    (f.property.1.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  exact ⟨⟨g, univ, isOpen_univ, subset_univ _, hg.contDiffOn⟩, hg,
    f.property.2.1.fderiv_apply ℝ v,
    (tsupport_fderiv_apply_subset ℝ v).trans f.property.2.2⟩

/-- Compact Bochner identity in the proof of Proposition 3.3.
The source is the generator graph output. The full diffusion-plus-Hessian
energy is integrable. -/
theorem compact_gradient_energy (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) (f : compactTests U)
    (a : Lp ℝ 2 ρ)
    (ha : (ScalarForm.ofCore (jet hU hB hV) f.val, a) ∈
      ScalarForm.neumannGraph (jet hU hB hV)) :
    let B := stdOrthonormalBasis ℝ E
    let e := fun x =>
      (∑ i, ‖gradient (fun y => fderiv ℝ f.val.val y (B i)) x‖ ^ 2) +
        fderiv ℝ (fderiv ℝ V) x (gradient f.val.val x) (gradient f.val.val x)
    Integrable e ρ ∧ (∫ x, e x ∂ρ) = ‖a‖ ^ 2 := by
  have := probability hV
  have hρ := IntrinsicScalarPoisson.gibbs_eq_tilted hU hV
  obtain ⟨hm, hi, he⟩ := Intrinsic.gradient_energy volume hU hV.1
    (stdOrthonormalBasis ℝ E) f.property.1 f.property.2.1 f.property.2.2
  rw [← hρ] at hm hi he
  have hgraph : (ScalarForm.ofCore (jet hU hB hV) f.val,
      hm.toLp (Intrinsic.langevin V f.val.val)) ∈ ScalarForm.neumannGraph (jet hU hB hV) := by
    obtain ⟨b, hb, hbae⟩ := compact_mem_graph hU hB hV f
    have hab : b = hm.toLp (Intrinsic.langevin V f.val.val) := by
      apply Lp.ext
      filter_upwards [hbae, hm.coeFn_toLp] with x hx hy
      exact hx.trans hy.symm
    exact hab ▸ hb
  have hpa (b : Lp ℝ 2 ρ)
      (hb : (ScalarForm.ofCore (jet hU hB hV) f.val, b) ∈
        ScalarForm.neumannGraph (jet hU hB hV)) :
      (ScalarForm.value (jet hU hB hV)
        (ScalarForm.ofCore (jet hU hB hV) f.val), b) ∈ (operator hU hB hV).graph := by
    rw [operator, ScalarForm.l2Operator_graph, ScalarForm.mem_l2Graph_iff]
    exact ⟨_, rfl, hb⟩
  have heq := (operator hU hB hV).mem_graph_snd_inj (hpa _ ha) (hpa _ hgraph) rfl
  dsimp only
  simp only [real_inner_self_eq_norm_sq] at hi he
  refine ⟨hi, he.trans ?_⟩
  rw [heq, Riesz1.poisson_norm_sq]
  apply integral_congr_ae
  exact hm.coeFn_toLp.symm.mono (fun x hx => congrArg (· ^ 2) hx)

/-- The full compact gradient energies of graph-approximant differences
are Cauchy, as used in the proof of Proposition 3.3.
The energy estimate includes integrability for every pair. -/
theorem graph_approximation_energy_cauchy [Nontrivial E] (hU : IsOpen U)
    (hB : Bornology.IsBounded U) (hV : IsEuclideanGibbsPotential volume ρ U V)
    {C : ℝ} (hC : 0 ≤ C)
    (hbar : ∀ x ∈ U, (Metric.infDist x (frontier U))⁻¹ ^ 2 - C ≤
      ‖gradient V x‖ ^ 2 / 4 - Δ V x / 2)
    (ψ : ScalarForm.Domain (jet hU hB hV)) (a : Lp ℝ 2 ρ)
    (hψ : (ψ, a) ∈ ScalarForm.neumannGraph (jet hU hB hV)) :
    ∃ c : ℕ → compactTests U, ∃ b : ℕ → Lp ℝ 2 ρ,
      (∀ k, (ScalarForm.ofCore (jet hU hB hV) (c k).val, b k) ∈
        ScalarForm.neumannGraph (jet hU hB hV)) ∧
      Tendsto (fun k => ScalarForm.ofCore (jet hU hB hV) (c k).val) atTop (𝓝 ψ) ∧
      Tendsto b atTop (𝓝 a) ∧
      (let B := stdOrthonormalBasis ℝ E
       let e := fun k l x =>
         (∑ i, ‖gradient (fun y => fderiv ℝ (c k - c l).val.val y (B i)) x‖ ^ 2) +
           fderiv ℝ (fderiv ℝ V) x (gradient (c k - c l).val.val x)
             (gradient (c k - c l).val.val x)
       (∀ k l, Integrable (e k l) ρ ∧ (∫ x, e k l x ∂ρ) = ‖b k - b l‖ ^ 2) ∧
         ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, ∀ k l, n ≤ k → n ≤ l →
           (∫ x, e k l x ∂ρ) < ε) := by
  obtain ⟨c, b, hb, ht, ha, _⟩ := graph_approximation_with_gradient hU hB hV hC hbar ψ a hψ
  refine ⟨c, b, hb, ht, ha, ?_⟩
  dsimp only
  have he (k l : ℕ) := compact_gradient_energy hU hB hV (c k - c l) (b k - b l)
    (by
      have hh := (ScalarForm.neumannGraph (jet hU hB hV)).sub_mem (hb k) (hb l)
      change (ScalarForm.ofCore (jet hU hB hV) (c k).val -
        ScalarForm.ofCore (jet hU hB hV) (c l).val, b k - b l) ∈ _ at hh
      simpa only [Submodule.coe_sub, map_sub] using hh)
  refine ⟨he, fun ε hε => ?_⟩
  obtain ⟨n, hn⟩ := Metric.cauchySeq_iff.mp ha.cauchySeq (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
  refine ⟨n, fun k l hk hl => ?_⟩
  rw [(he k l).2]
  have hh := hn k hk l hl
  rw [dist_eq_norm] at hh
  nlinarith [norm_nonneg (b k - b l), Real.sq_sqrt hε.le]

/-- Compact gradients in the proof of Proposition 3.3 belong to the finite-energy
domain for the Hessian. The components are existing scalar
Neumann jets, and the value equality is asserted modulo a.e. equality. This
bridge is valid before passing to any completion of compact vector fields. -/
theorem compact_gradient_finite_energy {d : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin d))} {ρ : Measure (EuclideanSpace ℝ (Fin d))}
    {V : EuclideanSpace ℝ (Fin d) → ℝ}
    (hU : IsOpen U) (hB : Bornology.IsBounded U)
    (hV : IsEuclideanGibbsPotential volume ρ U V) (f : compactTests U) :
    ∃ u : Fin d → (form hU hB hV).1,
      WeightedFormDomain (form hU hB hV) (hessianMatrix V) ⊤ u ∧
      ∀ i, (u i).val =ᵐ[ρ] fun x => gradient f.val.val x i := by
  have := probability hV
  let J := jet hU hB hV
  let u : Fin d → (form hU hB hV).1 := fun i =>
    ScalarForm.valueEquiv J (value_injective hU hB hV)
      (ScalarForm.ofCore J (compactDerivative f (EuclideanSpace.single i 1)).val)
  have hu (i : Fin d) : (u i).val =ᵐ[ρ] fun x => gradient f.val.val x i := by
    have he := (Riesz1.WeightedSobolev.memLp_of_smoothNearClosure hB (supported hU hV)
      (compactDerivative f (EuclideanSpace.single i 1)).val.property).1.coeFn_toLp
    change (u i).val =ᵐ[ρ] (fun x => fderiv ℝ f.val.val x (EuclideanSpace.single i 1)) at he
    apply he.trans
    exact Eventually.of_forall fun x => by
      change fderiv ℝ f.val.val x (EuclideanSpace.single i 1) = _
      rw [← inner_gradient_left, EuclideanSpace.inner_single_right]
      simp only [one_mul, conj_trivial]
  have hq : Integrable (fun x => fderiv ℝ (fderiv ℝ V) x
      (gradient f.val.val x) (gradient f.val.val x)) ρ := by
    obtain ⟨a, ha, _⟩ := compact_mem_graph hU hB hV f
    have he := (compact_gradient_energy hU hB hV f a ha).1
    let B := stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin d))
    have hi : Integrable (fun x => ∑ i, ‖gradient
        (fun y => fderiv ℝ f.val.val y (B i)) x‖ ^ 2) ρ := by
      apply integrable_finsetSum
      intro i _
      exact (Intrinsic.memLp_gradient (compactDerivative f (B i)).property.1
        (compactDerivative f (B i)).property.2.1).norm.integrable_sq
    have hh := he.sub hi
    convert hh using 1
    ext x
    dsimp only [B, Pi.sub_apply]
    ring
  refine ⟨u, ⟨Eventually.of_forall (fun _ => Submodule.mem_top), ?_⟩, hu⟩
  apply hq.congr
  have hua := ae_all_iff.mpr hu
  filter_upwards [supported hU hV, hua] with x hx hux
  rw [Intrinsic.hessianMatrix_bilinear (hV.1.contDiffAt (hU.mem_nhds hx))]
  simp only [matrixFieldPair, hux]

end Riesz2.DifferentiatedPoisson
