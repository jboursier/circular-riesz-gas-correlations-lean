/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Frozen.PeriodizedMatrixBounds
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.MeasureTheory.Measure.Map

/-!
# Transport of periodized matrix bounds through measurable embeddings

The target matrix is supplied on its entire carrier. Only the existential
measurable coefficient witnesses are extended outside the image, where the
pushforward measure vanishes. No matrix field or operator is extended.
-/

public section
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Riesz2.PeriodizedMatrixPushforward

/-- Matrix bounds are preserved by a measurable embedding, provided the
target matrix is measurable and agrees with the source on the image. -/
theorem of_embedding {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (f : α → β) (hf : MeasurableEmbedding f)
    (s : Riesz1.RieszExponent) (n m : ℕ+) (hm : 2 ≤ (m : ℕ))
    (K : ℕ) (C κ γ ε : ℝ)
    (M : α → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (M' : β → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hmeas : ∀ i j, Measurable (fun x => M' x i j)) (heq : M' ∘ f = M)
    (hM : PeriodizedMatrixBounds (ν := μ) s n m hm K C κ γ ε M) :
    PeriodizedMatrixBounds (ν := μ.map f) s n m hm K C κ γ ε M' := by
  refine ⟨hmeas, ?_, ?_⟩
  · rw [hf.ae_map_iff]
    simpa only [← heq, Function.comp_apply] using hM.2.1
  · obtain ⟨a, ha, hb⟩ := hM.2.2
    have hex (i : Fin (m : ℕ)) (r : Fin ((m : ℕ)/2)) :=
      hf.exists_measurable_extend (ha i r) (fun _ => inferInstance : β → Nonempty ℝ)
    choose b hbm hbe using hex
    refine ⟨b, hbm, ?_⟩
    rw [hf.ae_map_iff]
    have hbe' (i r x) : b i r (f x) = a i r x := congrFun (hbe i r) x
    simpa only [← heq, Function.comp_apply, hbe'] using hb

end Riesz2.PeriodizedMatrixPushforward
