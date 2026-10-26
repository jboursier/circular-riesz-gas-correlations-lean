/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.AffineSimplexCharts
public import Riesz1.ToMathlib.WeightedSobolev.Graph
public import Riesz1.ToMathlib.WeightedSobolev.TestDensity
public import Riesz1.ToMathlib.WeightedSobolev.VariationalPairing
public import Riesz1.ToMathlib.WeightedSobolev.LocalIntegrationByParts
public import Riesz1.HelfferSjostrand.SettingForm
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Closed scalar forms in weighted coordinates

Scalar-form constructions for Subsections 3.1 and 4.1. A linear family of finite
weighted jets is completed in `Riesz1.WeightedSobolev.L2Jet`.
The derivative Hilbert space is a parameter and may be an intrinsic tangent space.

The completion is a Hilbert space of pairs. The local pairing criterion makes
its value projection injective. The chart-test criterion proves density in L².
The variational generator then uses the Riesz 1 construction on this domain.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz2
namespace ScalarForm

variable {Ω C G : Type*} [MeasurableSpace Ω]
  [AddCommGroup C] [Module ℝ C]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  {μ : Measure Ω}

/-- A finite weighted test jet. The derivative metric is the supplied Hilbert metric. -/
abbrev Jet (μ : Measure Ω) (G : Type*) [NormedAddCommGroup G] :=
  Riesz1.WeightedSobolev.L2Jet μ G

variable (J : C →ₗ[ℝ] Jet μ G)

/-- Closed completion of the prescribed linear test jets (Subsection 3.1). -/
def completionSubmodule : Submodule ℝ (Jet μ G) := J.range.topologicalClosure

/-- The form domain, with the sum-of-squares Hilbert norm (Subsection 4.1). -/
abbrev Domain := completionSubmodule J

instance [CompleteSpace G] : CompleteSpace (Domain J) := by
  unfold Domain completionSubmodule
  infer_instance

/-- Inclusion of tests into their completion. -/
def ofCore : C →ₗ[ℝ] Domain J :=
  J.codRestrict _ (fun c => Submodule.le_topologicalClosure _ ⟨c, rfl⟩)

/-- The value projection into scalar L². -/
def value : Domain J →L[ℝ] Lp ℝ 2 μ :=
  (WithLp.fstL 2 ℝ _ _).comp (completionSubmodule J).subtypeL

/-- The derivative projection into the chosen, possibly intrinsic, metric. -/
def deriv : Domain J →L[ℝ] Lp G 2 μ :=
  (WithLp.sndL 2 ℝ _ _).comp (completionSubmodule J).subtypeL

/-- The scalar energy of two completed jets (Subsection 3.1, Subsection 4.1). -/
def energy (f h : Domain J) : ℝ := inner ℝ (deriv J f) (deriv J h)

theorem energy_integral (f h : Domain J) :
    energy J f h = ∫ x, inner ℝ (deriv J f x) (deriv J h x) ∂μ := rfl

theorem energy_symm (f h : Domain J) : energy J f h = energy J h f :=
  real_inner_comm _ _

theorem energy_nonneg (f : Domain J) : 0 ≤ energy J f f := real_inner_self_nonneg

theorem energy_add_left (f g h : Domain J) :
    energy J (f + g) h = energy J f h + energy J g h := by
  simp only [energy, map_add, inner_add_left]

theorem energy_smul_left (a : ℝ) (f h : Domain J) :
    energy J (a • f) h = a * energy J f h := by
  simp only [energy, map_smul, real_inner_smul_left]

/-- Bilinearity in the second test variable. -/
theorem energy_add_right (f g h : Domain J) :
    energy J f (g + h) = energy J f g + energy J f h := by
  simp only [energy, map_add, inner_add_right]

theorem energy_smul_right (a : ℝ) (f h : Domain J) :
    energy J f (a • h) = a * energy J f h := by
  simp only [energy, map_smul, inner_smul_right]

/-- Joint continuity for the form norm. -/
theorem continuous_energy : Continuous (fun p : Domain J × Domain J => energy J p.1 p.2) :=
  ((deriv J).continuous.comp continuous_fst).inner
    ((deriv J).continuous.comp continuous_snd)

/-- The norm of the completion is precisely the Hilbert form norm. -/
theorem norm_sq (f : Domain J) :
    ‖f‖ ^ 2 = ‖value J f‖ ^ 2 + energy J f f := by
  rw [energy, real_inner_self_eq_norm_sq]
  exact WithLp.prod_norm_sq_eq_of_L2 f.val

/-- The Hilbert inner product splits into its mass and energy terms. -/
theorem inner_eq (f h : Domain J) :
    inner ℝ f h = inner ℝ (value J f) (value J h) + energy J f h :=
  WithLp.prod_inner_apply f.val h.val

/-- Test jets are dense in the form norm. -/
theorem denseRange_ofCore : DenseRange (ofCore J) := by
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_forall
  intro f
  rw [(Topology.IsEmbedding.subtypeVal : Topology.IsEmbedding
    (Subtype.val : Domain J → Jet μ G)).closure_eq_preimage_closure_image]
  have himage : Subtype.val '' range (ofCore J) = range J := by
    ext z
    constructor
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩; exact ⟨c, rfl⟩
    · rintro ⟨c, rfl⟩; exact ⟨ofCore J c, ⟨c, rfl⟩, rfl⟩
  change f.val ∈ closure (Subtype.val '' range (ofCore J))
  rw [himage, ← LinearMap.coe_range]
  exact f.property

/-- A continuous integration-by-parts identity on tests extends to the entire domain.
The test field and its divergence are L² classes, so no integrability is implicit. -/
theorem pairing_of_core (t : Lp G 2 μ) (q : Lp ℝ 2 μ)
    (hcore : ∀ c, inner ℝ (deriv J (ofCore J c)) t =
      inner ℝ (value J (ofCore J c)) q) (f : Domain J) :
    inner ℝ (deriv J f) t = inner ℝ (value J f) q := by
  have h := (denseRange_ofCore J).equalizer
    ((deriv J).continuous.inner continuous_const)
    ((value J).continuous.inner continuous_const) (funext hcore)
  exact congrFun h f

/-- Internal local closability criterion: a separating family of L² vector tests with
L² divergences forces a zero-valued completed jet to have zero derivative. -/
theorem value_injective_of_pairings {T : Type*} (t : T → Lp G 2 μ)
    (q : T → Lp ℝ 2 μ)
    (hcore : ∀ a c, inner ℝ (deriv J (ofCore J c)) (t a) =
      inner ℝ (value J (ofCore J c)) (q a))
    (hsep : ∀ g : Lp G 2 μ, (∀ a, inner ℝ g (t a) = 0) → g = 0) :
    Function.Injective (value J) := by
  intro f h heq
  have hv : value J (f - h) = 0 := by rw [map_sub, heq, sub_self]
  have hd : deriv J (f - h) = 0 := by
    apply hsep
    intro a
    rw [pairing_of_core J (t a) (q a) (hcore a), hv, inner_zero_left]
  have hz : f - h = 0 := by
    apply Subtype.ext
    apply (WithLp.equiv 2 _).injective
    exact Prod.ext hv hd
  exact sub_eq_zero.mp hz

/-- Internal density criterion in any measurable Euclidean chart, using the Riesz1
compact-test density theorem. No absolute continuity of the measure is needed. -/
theorem denseRange_value_of_chart [IsFiniteMeasure μ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (s : Ω → E) (hs : MeasurableEmbedding s) (U : Set E) (hU : IsOpen U)
    (hμ : ∀ᵐ x ∂μ, s x ∈ U)
    (htest : ∀ g : E → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ U →
      ∃ c : C, (value J (ofCore J c) : Ω → ℝ) =ᵐ[μ] g ∘ s) :
    DenseRange (value J) := by
  apply Riesz1.Internal.denseRange_of_chart_tests μ (value J).toLinearMap s hs U hU hμ
  intro g hg hgc hgU
  obtain ⟨c, hc⟩ := htest g hg hgc hgU
  exact ⟨ofCore J c, hc⟩

/-- Internal chart-local closability criterion. Compact scalar tests in every derivative
coordinate separate vector L². The only analytic input is integration by parts on the core. -/
theorem value_injective_of_chart_pairings [IsFiniteMeasure μ] [FiniteDimensional ℝ G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (s : Ω → E) (hs : MeasurableEmbedding s) (U : Set E) (hU : IsOpen U)
    (hμ : ∀ᵐ x ∂μ, s x ∈ U)
    (hlocal : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∀ v : G, ∃ q : Lp ℝ 2 μ, ∀ c : C,
        (∫ x, ψ (s x) * inner ℝ v (deriv J (ofCore J c) x) ∂μ) =
          inner ℝ (value J (ofCore J c)) q) :
    Function.Injective (value J) := by
  let T := {ψ : E → ℝ // ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ U} × G
  have ht (a : T) : MemLp (fun x => a.1.val (s x) • a.2) 2 μ := by
    obtain ⟨M, hM⟩ := a.1.property.2.1.exists_bound_of_continuous a.1.property.1.continuous
    apply MemLp.of_bound
      ((a.1.property.1.continuous.measurable.comp hs.measurable).aestronglyMeasurable.smul_const a.2)
      (M * ‖a.2‖)
    exact Eventually.of_forall (fun x => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hM (s x)) (norm_nonneg _))
  let t (a : T) : Lp G 2 μ := (ht a).toLp _
  choose q hq using fun a : T => hlocal a.1.val a.1.property.1
    a.1.property.2.1 a.1.property.2.2 a.2
  apply value_injective_of_pairings J t q
  · intro a c
    rw [L2.inner_def]
    calc
      _ = ∫ x, a.1.val (s x) * inner ℝ a.2 (deriv J (ofCore J c) x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [(ht a).coeFn_toLp] with x hx
        rw [hx, inner_smul_right, real_inner_comm]
      _ = _ := hq a c
  · intro g hg
    let b := stdOrthonormalBasis ℝ G
    have hi (i : Fin (Module.finrank ℝ G)) : (innerSL ℝ (b i)).compLpL 2 μ g = 0 := by
      apply Riesz1.Internal.eq_zero_of_chart_tests μ s hs U hU hμ
      intro ψ hψ hψc hψU
      let a : T := (⟨ψ, hψ, hψc, hψU⟩, b i)
      have he := hg a
      rw [L2.inner_def] at he
      calc
        _ = ∫ x, inner ℝ (g x) (t a x) ∂μ := by
          apply integral_congr_ae
          filter_upwards [(innerSL ℝ (b i)).coeFn_compLpL (p := 2) (μ := μ) g,
            (ht a).coeFn_toLp] with x hx hy
          rw [hx, hy, inner_smul_right, innerSL_apply_apply, real_inner_comm]
        _ = 0 := he
    have hz (i : Fin (Module.finrank ℝ G)) : ∀ᵐ x ∂μ, inner ℝ (b i) (g x) = 0 := by
      have he := (innerSL ℝ (b i)).coeFn_compLpL (p := 2) (μ := μ) g
      rw [hi i] at he
      filter_upwards [he, Lp.coeFn_zero ℝ 2 μ] with x hx h0
      exact hx.symm.trans h0
    apply Lp.ext
    filter_upwards [ae_all_iff.mpr hz, Lp.coeFn_zero G 2 μ] with x hx h0
    rw [h0]
    apply b.repr.injective
    ext i
    simpa [OrthonormalBasis.repr_apply_apply] using hx i

/-- Full variational graph. It is defined before density or closability is invoked. -/
def neumannGraph : Submodule ℝ (Domain J × Lp ℝ 2 μ) where
  carrier := {p | ∀ h, energy J p.1 h = inner ℝ p.2 (value J h)}
  zero_mem' := by simp [energy]
  add_mem' := by
    intro p q hp hq h
    change energy J (p.1 + q.1) h = inner ℝ (p.2 + q.2) (value J h)
    rw [energy_add_left, hp, hq, inner_add_left]
  smul_mem' := by
    intro a p hp h
    change energy J (a • p.1) h = inner ℝ (a • p.2) (value J h)
    rw [energy_smul_left, hp, real_inner_smul_left]

/-- Variational domain in the form space. -/
def operatorDomain : Set (Domain J) :=
  Riesz1.Internal.formOperatorDomain (value J) (energy J)

/-- The graph identity is exactly the weak Neumann integration-by-parts formula. -/
theorem mem_neumannGraph_iff_integral (f : Domain J) (a : Lp ℝ 2 μ) :
    (f, a) ∈ neumannGraph J ↔ ∀ h : Domain J,
      (∫ x, inner ℝ (deriv J f x) (deriv J h x) ∂μ) =
        ∫ x, a x * value J h x ∂μ := by
  change (∀ h, energy J f h = inner ℝ a (value J h)) ↔ _
  simp only [energy_integral, L2.inner_def, Real.inner_apply]

/-- Closedness in the form-space × L² topology. -/
theorem isClosed_neumannGraph : IsClosed (neumannGraph J : Set (Domain J × Lp ℝ 2 μ)) := by
  change IsClosed {p : Domain J × Lp ℝ 2 μ | ∀ h,
    energy J p.1 h = inner ℝ p.2 (value J h)}
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro h
  exact isClosed_eq (((deriv J).continuous.comp continuous_fst).inner continuous_const)
    (continuous_snd.inner continuous_const)

/-- The nonnegative generator, selected only on its full variational domain. -/
def generator (hdense : DenseRange (value J)) (f : operatorDomain J) : Lp ℝ 2 μ :=
  Riesz1.Internal.formOperator (value J) hdense (energy J) f

theorem generator_eq_iff (hdense : DenseRange (value J))
    (f : operatorDomain J) (a : Lp ℝ 2 μ) :
    generator J hdense f = a ↔ ∀ h, energy J f.val h = inner ℝ a (value J h) :=
  Riesz1.Internal.formOperator_eq_iff (value J) hdense (energy J) f a

theorem generator_symmetric (hdense : DenseRange (value J)) (f g : operatorDomain J) :
    inner ℝ (generator J hdense f) (value J g.val) =
      inner ℝ (value J f.val) (generator J hdense g) :=
  Riesz1.Internal.formOperator_symmetric _ hdense _ (energy_symm J) f g

theorem generator_nonneg (hdense : DenseRange (value J)) (f : operatorDomain J) :
    0 ≤ inner ℝ (generator J hdense f) (value J f.val) :=
  Riesz1.Internal.formOperator_nonnegative _ hdense _ (energy_nonneg J) f

section Resolvent
variable [CompleteSpace G]

/-- The form resolvent is the adjoint of the value embedding. -/
def resolvent : Lp ℝ 2 μ →L[ℝ] Domain J := (value J).adjoint

theorem resolvent_equation (a : Lp ℝ 2 μ) (h : Domain J) :
    energy J (resolvent J a) h + inner ℝ (value J (resolvent J a)) (value J h) =
      inner ℝ a (value J h) := by
  rw [add_comm, ← inner_eq]
  exact (value J).adjoint_inner_left h a

/-- Every source has a unique solution for `1 + L`, in the form domain. -/
theorem resolvent_unique (a : Lp ℝ 2 μ) (f : Domain J)
    (hf : ∀ h, energy J f h + inner ℝ (value J f) (value J h) = inner ℝ a (value J h)) :
    f = resolvent J a := by
  apply ext_inner_right ℝ
  intro h
  rw [inner_eq, add_comm, hf, ← resolvent_equation, add_comm, ← inner_eq]

/-- The resolvent lands in the full variational domain, with output `a - f`. -/
theorem resolvent_mem_graph (a : Lp ℝ 2 μ) :
    (resolvent J a, a - value J (resolvent J a)) ∈ neumannGraph J := by
  intro h
  rw [inner_sub_left]
  linarith [resolvent_equation J a h]

/-- The whole variational domain is the range of the form resolvent. -/
theorem range_resolvent : range (resolvent J) = operatorDomain J := by
  ext f
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨_, resolvent_mem_graph J a⟩
  · rintro ⟨a, ha⟩
    refine ⟨a + value J f, (resolvent_unique J _ f ?_).symm⟩
    intro h
    rw [ha, inner_add_left]

/-- Closability makes the generator domain dense even for the stronger form norm. -/
theorem dense_operatorDomain (hclosed : Function.Injective (value J)) :
    Dense (operatorDomain J) := by
  rw [← range_resolvent]
  change DenseRange (resolvent J)
  rw [denseRange_iff_closure_range]
  change closure ((value J).adjoint.range : Set (Domain J)) = univ
  rw [← Submodule.topologicalClosure_coe, ← ContinuousLinearMap.orthogonal_ker,
    LinearMap.ker_eq_bot.mpr hclosed, Submodule.bot_orthogonal_eq_top]
  rfl

/-- Bounded L² resolvent, obtained without choosing coordinates or a differential expression. -/
def l2Resolvent : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := (value J).comp (resolvent J)

/-- The L² resolvent has dense range as soon as the form domain is dense in L². -/
theorem denseRange_l2Resolvent (hdense : DenseRange (value J)) :
    DenseRange (l2Resolvent J) := by
  have hinj : Function.Injective (resolvent J) := by
    intro a b hab
    apply Riesz1.Internal.formRepresentative_unique (value J) hdense
      (fun f h => inner ℝ f h) (resolvent J a)
    · intro h
      exact (value J).adjoint_inner_left h a
    · intro h
      rw [hab]
      exact (value J).adjoint_inner_left h b
  have hker : (l2Resolvent J).ker = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    intro a b hab
    change l2Resolvent J a = l2Resolvent J b at hab
    apply hinj
    apply sub_eq_zero.mp
    have hnorm : ‖resolvent J (a - b)‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq]
      change inner ℝ ((value J).adjoint (a - b)) _ = 0
      rw [(value J).adjoint_inner_left]
      have hz : value J (resolvent J (a - b)) = 0 := by
        change l2Resolvent J (a - b) = 0
        rw [map_sub, hab, sub_self]
      rw [hz, inner_zero_right]
    have hz : resolvent J (a - b) = 0 := by
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
    simpa only [map_sub] using hz
  have hsymm : (l2Resolvent J).adjoint = l2Resolvent J := by
    rw [l2Resolvent, resolvent, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint]
  have hd : DenseRange (l2Resolvent J).adjoint := by
    rw [denseRange_iff_closure_range]
    change closure ((l2Resolvent J).adjoint.range : Set (Lp ℝ 2 μ)) = univ
    rw [← Submodule.topologicalClosure_coe, ← ContinuousLinearMap.orthogonal_ker,
      hker, Submodule.bot_orthogonal_eq_top]
    rfl
  simpa only [hsymm] using hd

/-- Ambient generator graph, parametrized by the bounded resolvent.
This is an equality of L² classes and is closed in the ambient L² × L² topology. -/
def l2Graph : Submodule ℝ (Lp ℝ 2 μ × Lp ℝ 2 μ) :=
  ((l2Resolvent J).comp ((ContinuousLinearMap.fst ℝ _ _) +
    (ContinuousLinearMap.snd ℝ _ _)) - ContinuousLinearMap.fst ℝ _ _).ker

theorem mem_l2Graph (f a : Lp ℝ 2 μ) :
    (f, a) ∈ l2Graph J ↔ l2Resolvent J (f + a) = f := by
  change l2Resolvent J (f + a) - f = 0 ↔ _
  exact sub_eq_zero

/-- The ambient graph has exactly the variational meaning in Subsection 3.1. -/
theorem mem_l2Graph_iff (f a : Lp ℝ 2 μ) :
    (f, a) ∈ l2Graph J ↔
      ∃ u : Domain J, value J u = f ∧ ∀ h, energy J u h = inner ℝ a (value J h) := by
  rw [mem_l2Graph]
  constructor
  · intro he
    refine ⟨resolvent J (f + a), he, ?_⟩
    intro h
    have ht := resolvent_mem_graph J (f + a) h
    change value J (resolvent J (f + a)) = f at he
    dsimp only [Prod.fst, Prod.snd] at ht
    rw [he, add_sub_cancel_left] at ht
    exact ht
  · rintro ⟨u, hu, hform⟩
    have he : u = resolvent J (f + a) := by
      apply resolvent_unique
      intro h
      rw [hform, hu, inner_add_left]
      ring
    change value J (resolvent J (f + a)) = f
    rw [← he, hu]

theorem isClosed_l2Graph : IsClosed (l2Graph J : Set (Lp ℝ 2 μ × Lp ℝ 2 μ)) :=
  ContinuousLinearMap.isClosed_ker _

/-- Dense form range makes the ambient graph single-valued. -/
theorem l2Graph_zero_fst (hdense : DenseRange (value J))
    {p : Lp ℝ 2 μ × Lp ℝ 2 μ} (hp : p ∈ l2Graph J) (hz : p.1 = 0) : p.2 = 0 := by
  obtain ⟨u, hu, he⟩ := (mem_l2Graph_iff J p.1 p.2).mp hp
  have hu0 : u = 0 := by
    have hnorm : inner ℝ u u = 0 := by
      rw [inner_eq, hu, hz, inner_zero_left, he u, hu, hz, inner_zero_right]
      norm_num
    exact inner_self_eq_zero.mp hnorm
  apply Riesz1.Internal.formRepresentative_unique (value J) hdense (energy J) u
  · exact he
  · intro h
    simp only [hu0, energy, map_zero, inner_zero_left]

/-- The graph equals its Hilbert-space adjoint graph. -/
theorem l2Graph_adjoint : (l2Graph J).adjoint = l2Graph J := by
  have hsymm (a b : Lp ℝ 2 μ) :
      inner ℝ (l2Resolvent J a) b = inner ℝ a (l2Resolvent J b) := by
    change inner ℝ (value J (resolvent J a)) b = inner ℝ a (value J (resolvent J b))
    calc
      _ = inner ℝ (resolvent J a) (resolvent J b) :=
        ((value J).adjoint_inner_right (resolvent J a) b).symm
      _ = _ := (value J).adjoint_inner_left (resolvent J b) a
  apply le_antisymm
  · rintro ⟨f, a⟩ hp
    apply (mem_l2Graph J f a).mpr
    apply ext_inner_left ℝ
    intro b
    have ht : (l2Resolvent J b, b - l2Resolvent J b) ∈ l2Graph J := by
      rw [mem_l2Graph, add_sub_cancel]
    have he := (Submodule.mem_adjoint_iff _ _).mp hp _ _ ht
    change inner ℝ (b - l2Resolvent J b) f - inner ℝ (l2Resolvent J b) a = 0 at he
    rw [inner_sub_left, hsymm, hsymm] at he
    rw [map_add, inner_add_right]
    linarith
  · rintro ⟨f, a⟩ hp
    obtain ⟨u, hu, hua⟩ := (mem_l2Graph_iff J f a).mp hp
    apply (Submodule.mem_adjoint_iff _ _).mpr
    intro g b hgb
    obtain ⟨v, hv, hvb⟩ := (mem_l2Graph_iff J g b).mp hgb
    change inner ℝ b f - inner ℝ g a = 0
    have hba : inner ℝ b f = inner ℝ g a := by
      calc
        _ = energy J v u := by rw [← hu, ← hvb u]
        _ = energy J u v := energy_symm J v u
        _ = inner ℝ g a := (hua v).trans (by rw [hv, real_inner_comm])
    exact sub_eq_zero.mpr hba

/-- A linear generator on its full ambient domain, without a fallback outside that domain. -/
def l2Operator (hdense : DenseRange (value J)) : Lp ℝ 2 μ →ₗ.[ℝ] Lp ℝ 2 μ where
  domain := (l2Graph J).map (LinearMap.fst ℝ _ _)
  toFun := (l2Graph J).toLinearPMapAux (fun _ hp hz => l2Graph_zero_fst J hdense hp hz)

theorem l2Operator_graph (hdense : DenseRange (value J)) :
    (l2Operator J hdense).graph = l2Graph J := by
  have he : l2Operator J hdense = (l2Graph J).toLinearPMap := by
    apply LinearPMap.ext (f := l2Operator J hdense) (g := (l2Graph J).toLinearPMap) rfl
    intro x hx hy
    exact (Submodule.toLinearPMap_apply_aux
      (fun _ hp hz => l2Graph_zero_fst J hdense hp hz) ⟨x, hx⟩).symm
  rw [he]
  exact Submodule.toLinearPMap_graph_eq _ (fun _ hp hz => l2Graph_zero_fst J hdense hp hz)

theorem dense_l2Operator_domain (hdense : DenseRange (value J)) :
    Dense ((l2Operator J hdense).domain : Set (Lp ℝ 2 μ)) := by
  apply (denseRange_l2Resolvent J hdense).mono
  rintro _ ⟨a, rfl⟩
  exact ⟨(l2Resolvent J a, a - l2Resolvent J a),
    (mem_l2Graph J _ _).mpr (by rw [add_sub_cancel]), rfl⟩

/-- The full-domain operator and the form-domain representative describe the same solutions. -/
theorem generator_mem_l2Operator_graph (hdense : DenseRange (value J))
    (f : operatorDomain J) :
    (value J f.val, generator J hdense f) ∈ (l2Operator J hdense).graph := by
  rw [l2Operator_graph, mem_l2Graph_iff]
  exact ⟨f.val, rfl, (generator_eq_iff J hdense f _).mp rfl⟩

/-- Nonnegativity in the ambient L² formulation. -/
theorem l2Operator_nonneg (hdense : DenseRange (value J))
    {f a : Lp ℝ 2 μ} (h : (f, a) ∈ (l2Operator J hdense).graph) :
    0 ≤ inner ℝ a f := by
  rw [l2Operator_graph, mem_l2Graph_iff] at h
  obtain ⟨u, hu, he⟩ := h
  rw [← hu, ← he u]
  exact energy_nonneg J u

/-- The variational generator is self-adjoint on its dense ambient L² domain. -/
theorem l2Operator_selfAdjoint (hdense : DenseRange (value J)) :
    IsSelfAdjoint (l2Operator J hdense) := by
  change (l2Operator J hdense).adjoint = l2Operator J hdense
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (dense_l2Operator_domain J hdense),
    l2Operator_graph, l2Graph_adjoint]

end Resolvent

/-- A zero-gradient element is in the generator domain and is killed by the generator. -/
theorem zero_deriv_mem_domain (f : Domain J) (hf : deriv J f = 0) : f ∈ operatorDomain J := by
  refine ⟨0, fun h => ?_⟩
  simp only [energy, hf, inner_zero_left]

theorem generator_zero_of_deriv_zero (hdense : DenseRange (value J))
    (f : Domain J) (hf : deriv J f = 0) :
    generator J hdense ⟨f, zero_deriv_mem_domain J f hf⟩ = 0 := by
  apply (generator_eq_iff J hdense _ _).mpr
  intro h
  simp only [energy, hf, inner_zero_left]

end ScalarForm

namespace EuclideanScalarForm

open Riesz1.WeightedSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {U : Set E} {μ : Measure E} [IsFiniteMeasure μ]

/-- Smooth functions near the closure, before imposing the finite weighted norm. -/
def smoothCore (U : Set E) : Submodule ℝ (E → ℝ) where
  carrier := SmoothNearClosure U
  zero_mem' := ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
  add_mem' := by
    rintro f g ⟨W, hW, hUW, hf⟩ ⟨V, hV, hUV, hg⟩
    exact ⟨W ∩ V, hW.inter hV, subset_inter hUW hUV,
      (hf.mono inter_subset_left).add (hg.mono inter_subset_right)⟩
  smul_mem' := by
    rintro a f ⟨W, hW, hUW, hf⟩
    exact ⟨W, hW, hUW, hf.const_smul a⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The core is differentiable at every interior point, irrespective of ambient values. -/
theorem differentiableAt_core (_hU : IsOpen U) (f : smoothCore U) {x : E} (hx : x ∈ U) :
    DifferentiableAt ℝ f.val x := by
  obtain ⟨W, hW, hUW, hf⟩ := f.property
  exact (hf.contDiffAt (hW.mem_nhds (hUW (subset_closure hx)))).differentiableAt (by norm_num)

/-- Weighted smooth jets with the actual Euclidean metric of the chart.
Boundedness and finite measure guarantee both L² components. -/
def smoothJet (hU : IsOpen U) (hbounded : Bornology.IsBounded U)
    (hμ : ∀ᵐ x ∂μ, x ∈ U) : smoothCore U →ₗ[ℝ] ScalarForm.Jet μ E where
  toFun f := WithLp.toLp 2
    ((memLp_of_smoothNearClosure hbounded hμ f.property).1.toLp f.val,
      (memLp_of_smoothNearClosure hbounded hμ f.property).2.toLp (gradient f.val))
  map_add' f g := by
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext
    · exact MemLp.toLp_add (memLp_of_smoothNearClosure hbounded hμ f.property).1
        (memLp_of_smoothNearClosure hbounded hμ g.property).1
    · have he : gradient (f.val + g.val) =ᵐ[μ] gradient f.val + gradient g.val := by
        filter_upwards [hμ] with x hx
        simp only [gradient, fderiv_add (differentiableAt_core hU f hx)
          (differentiableAt_core hU g hx), map_add]
        rfl
      exact (MemLp.toLp_congr
        (memLp_of_smoothNearClosure hbounded hμ (f + g).property).2
        ((memLp_of_smoothNearClosure hbounded hμ f.property).2.add
          (memLp_of_smoothNearClosure hbounded hμ g.property).2) he).trans
        (MemLp.toLp_add (memLp_of_smoothNearClosure hbounded hμ f.property).2
          (memLp_of_smoothNearClosure hbounded hμ g.property).2)
  map_smul' a f := by
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext
    · exact MemLp.toLp_const_smul a (memLp_of_smoothNearClosure hbounded hμ f.property).1
    · have he : gradient (a • f.val) =ᵐ[μ] a • gradient f.val := by
        filter_upwards [hμ] with x hx
        simp only [gradient, fderiv_const_smul (differentiableAt_core hU f hx), map_smul]
        rfl
      exact (MemLp.toLp_congr
        (memLp_of_smoothNearClosure hbounded hμ (a • f).property).2
        ((memLp_of_smoothNearClosure hbounded hμ f.property).2.const_smul a) he).trans
        (MemLp.toLp_const_smul a (memLp_of_smoothNearClosure hbounded hμ f.property).2)

variable (hU : IsOpen U) (hbounded : Bornology.IsBounded U) (hμ : ∀ᵐ x ∂μ, x ∈ U)

/-- This construction is precisely the library's smooth finite-norm jet core. -/
theorem range_smoothJet :
    ((smoothJet hU hbounded hμ).range : Set (ScalarForm.Jet μ E)) =
      jetCore μ (SmoothNearClosure U) id gradient := by
  ext z
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f.val, f.property, _, _, rfl⟩
  · rintro ⟨f, hf, hv, hg, rfl⟩
    exact ⟨⟨f, hf⟩, rfl⟩

/-- The Hilbert domain consists exactly of the library's weighted Sobolev pairs.
This is an equivalence, not a second Sobolev encoding. -/
theorem mem_completion_iff (F : E → ℝ) (G : E → E)
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    WithLp.toLp 2 (hF.toLp F, hG.toLp G) ∈
      ScalarForm.completionSubmodule (smoothJet hU hbounded hμ) ↔ IsWeightedH1 μ U F G := by
  change WithLp.toLp 2 (hF.toLp F, hG.toLp G) ∈
    closure ((smoothJet hU hbounded hμ).range : Set _) ↔ _
  rw [range_smoothJet]
  exact (isGraphH1_iff_mem_closure
    (fun f hf => (memLp_of_smoothNearClosure hbounded hμ hf).1)
    (fun f hf => (memLp_of_smoothNearClosure hbounded hμ hf).2) F G hF hG).symm

/-- Smooth weighted form domains are dense in scalar L² for every supported finite measure,
including point masses and dimension zero. -/
theorem denseRange_value :
    DenseRange (ScalarForm.value (smoothJet hU hbounded hμ)) := by
  apply ScalarForm.denseRange_value_of_chart _ id MeasurableEmbedding.id U hU hμ
  intro g hg hgc hgU
  let c : smoothCore U := ⟨g, univ, isOpen_univ, subset_univ _, hg.contDiffOn⟩
  refine ⟨c, ?_⟩
  exact (memLp_of_smoothNearClosure hbounded hμ c.property).1.coeFn_toLp

/-- Local integration by parts suffices for closability, without boundary traces.
This internal interface is usable for nonsmooth weights once their local pairing is proved. -/
theorem value_injective_of_local_pairings
    (hlocal : ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      ∀ v : E, ∃ q : E → ℝ, MemLp q 2 μ ∧ ∀ f : smoothCore U,
        (∫ x, ψ x * inner ℝ v (gradient f.val x) ∂μ) = ∫ x, f.val x * q x ∂μ) :
    Function.Injective (ScalarForm.value (smoothJet hU hbounded hμ)) := by
  apply ScalarForm.value_injective_of_chart_pairings _ id MeasurableEmbedding.id U hU hμ
  intro ψ hψ hψc hψU v
  obtain ⟨q, hq, hcore⟩ := hlocal ψ hψ hψc hψU v
  refine ⟨hq.toLp q, fun c => ?_⟩
  rw [L2.inner_def]
  calc
    _ = ∫ x, ψ x * inner ℝ v (gradient c.val x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [(memLp_of_smoothNearClosure hbounded hμ c.property).2.coeFn_toLp]
        with x hx
      change (ScalarForm.deriv (smoothJet hU hbounded hμ)
        (ScalarForm.ofCore (smoothJet hU hbounded hμ) c) : E → E) x = gradient c.val x at hx
      simp only [id_eq, hx]
    _ = _ := hcore c
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [(memLp_of_smoothNearClosure hbounded hμ c.property).1.coeFn_toLp,
        hq.coeFn_toLp] with x hx hy
      change (ScalarForm.value (smoothJet hU hbounded hμ)
        (ScalarForm.ofCore (smoothJet hU hbounded hμ) c) : E → ℝ) x = c.val x at hx
      rw [hx, hy, Real.inner_apply]

/-- Constant functions are smooth core elements for the Neumann convention. -/
def constantCore (a : ℝ) : smoothCore U :=
  ⟨fun _ => a, univ, isOpen_univ, subset_univ _, contDiffOn_const⟩

/-- Constant completed function, with its canonical zero gradient. -/
def constant (a : ℝ) : ScalarForm.Domain (smoothJet hU hbounded hμ) :=
  ScalarForm.ofCore (smoothJet hU hbounded hμ) (constantCore a)

theorem value_constant (a : ℝ) :
    (ScalarForm.value (smoothJet hU hbounded hμ) (constant hU hbounded hμ a) : E → ℝ)
      =ᵐ[μ] fun _ => a :=
  (memLp_const a).coeFn_toLp

theorem deriv_constant (a : ℝ) :
    ScalarForm.deriv (smoothJet hU hbounded hμ) (constant hU hbounded hμ a) = 0 := by
  apply Lp.ext
  have h := (memLp_of_smoothNearClosure hbounded hμ
    (constantCore (U := U) a).property).2.coeFn_toLp
  filter_upwards [h, Lp.coeFn_zero E 2 μ] with x hx h0
  rw [h0]
  exact hx.trans (gradient_const x a)

/-- Conservativity (Subsection 4.1): one belongs to the Neumann form domain and has zero energy. -/
theorem conservative :
    ScalarForm.energy (smoothJet hU hbounded hμ)
      (constant hU hbounded hμ 1) (constant hU hbounded hμ 1) = 0 := by
  rw [ScalarForm.energy, deriv_constant, inner_zero_left]

/-- The variational generator kills constants, with no boundary trace assumption. -/
theorem generator_constant (a : ℝ) :
    ScalarForm.generator (smoothJet hU hbounded hμ) (denseRange_value hU hbounded hμ)
      ⟨constant hU hbounded hμ a, ScalarForm.zero_deriv_mem_domain _ _
        (deriv_constant hU hbounded hμ a)⟩ = 0 :=
  ScalarForm.generator_zero_of_deriv_zero _ _ _ (deriv_constant hU hbounded hμ a)


section SmoothDensity

variable (σ : Measure E) [σ.IsAddHaarMeasure]

include hU hbounded hμ in
/-- A finite positive smooth weight has the local integration-by-parts data required
for closability. The density can be singular at the boundary. All tests are interior. -/
theorem local_pairings_of_smooth_density (w : E → ℝ)
    (hws : ContDiffOn ℝ ∞ w U) (hwpos : ∀ x ∈ U, 0 < w x)
    (hweight : μ = (σ.restrict U).withDensity (fun x => ENNReal.ofReal (w x)))
    (ψ : E → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U)
    (v : E) : ∃ q : E → ℝ, MemLp q 2 μ ∧ ∀ f : smoothCore U,
      (∫ x, ψ x * inner ℝ v (gradient f.val x) ∂μ) = ∫ x, f.val x * q x ∂μ := by
  let q : E → ℝ := fun x => -fderiv ℝ ψ x v - ψ x * (fderiv ℝ w x v / w x)
  have hc : Continuous q := by
    apply Continuous.sub
    · exact ((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const).neg
    · apply Riesz1.WeightedSobolev.continuous_cutoff_mul hU hψ.continuous hψU
      exact ((hws.continuousOn_fderiv_of_isOpen hU (by norm_num)).clm_apply
        continuousOn_const).div hws.continuousOn (fun x hx => ne_of_gt (hwpos x hx))
  refine ⟨q, memLp_of_continuousOn_closure hbounded hμ hc.continuousOn, fun f => ?_⟩
  have hconv (b : E → ℝ) : (∫ x, b x ∂μ) = ∫ x in U, w x * b x ∂σ := by
    have hwm : AEMeasurable w (σ.restrict U) := hws.continuousOn.aemeasurable hU.measurableSet
    rw [hweight, integral_withDensity_eq_integral_toReal_smul₀ hwm.ennreal_ofReal
      (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    rw [ENNReal.toReal_ofReal (le_of_lt (hwpos x hx)), smul_eq_mul]
  have hf : ContDiffOn ℝ ∞ f.val U := by
    obtain ⟨W, hW, hUW, hfW⟩ := f.property
    exact hfW.mono (subset_closure.trans hUW)
  have hid := Riesz1.WeightedSobolev.integral_weighted_fderiv_of_compact_test
    (μ := σ) hU hψ hψc hψU hf hws v
  have hproduct : ∀ x ∈ U, fderiv ℝ (fun y => ψ y * w y) x v =
      (fderiv ℝ ψ x v) * w x + ψ x * fderiv ℝ w x v := by
    intro x hx
    have hwd := (hws.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
    rw [fderiv_fun_mul (hψ.differentiable (by norm_num) x) hwd]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hleft : (∫ x, ψ x * inner ℝ v (gradient f.val x) ∂μ) =
      ∫ x, (ψ x * w x) * fderiv ℝ f.val x v ∂σ := by
    rw [hconv, setIntegral_eq_integral_of_forall_compl_eq_zero]
    · apply integral_congr_ae
      exact Eventually.of_forall (fun x => by
        dsimp only
        rw [real_inner_comm, inner_gradient_left]
        ring)
    · intro x hx
      have hz : ψ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hψU h))
      simp only [hz, zero_mul, mul_zero]
  have hright : (∫ x, f.val x * q x ∂μ) =
      -∫ x, f.val x * fderiv ℝ (fun y => ψ y * w y) x v ∂σ := by
    rw [hconv]
    have hsupp : tsupport (fun x => fderiv ℝ (fun y => ψ y * w y) x v) ⊆ U :=
      (tsupport_fderiv_apply_subset ℝ v).trans (tsupport_mul_subset_left.trans hψU)
    calc
      _ = ∫ x in U, -(f.val x * fderiv ℝ (fun y => ψ y * w y) x v) ∂σ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
        dsimp only [q]
        rw [hproduct x hx]
        field_simp [ne_of_gt (hwpos x hx)]
        ring
      _ = ∫ x, -(f.val x * fderiv ℝ (fun y => ψ y * w y) x v) ∂σ := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        have hnot : x ∉ tsupport (fun y => fderiv ℝ (fun z => ψ z * w z) y v) :=
          fun h => hx (hsupp h)
        have hz := image_eq_zero_of_notMem_tsupport hnot
        simp only [hz, mul_zero, neg_zero]
      _ = _ := integral_neg _
  exact hleft.trans (hid.trans hright.symm)

/-- Closability for a smooth positive finite density in any bounded open Euclidean chart.
No curvature, collision barrier or positive dimension is required. -/
theorem value_injective_of_smooth_density (w : E → ℝ)
    (hws : ContDiffOn ℝ ∞ w U) (hwpos : ∀ x ∈ U, 0 < w x)
    (hweight : μ = (σ.restrict U).withDensity (fun x => ENNReal.ofReal (w x))) :
    Function.Injective (ScalarForm.value (smoothJet hU hbounded hμ)) := by
  apply value_injective_of_local_pairings hU hbounded hμ
  exact local_pairings_of_smooth_density hU hbounded hμ σ w hws hwpos hweight

end SmoothDensity

end EuclideanScalarForm
end Riesz2
