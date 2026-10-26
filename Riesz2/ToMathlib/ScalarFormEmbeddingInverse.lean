/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.ToMathlib.ScalarFormEmbedding

/-!
# Inverse identities for scalar form transport

Transporting and restricting along the same measurable embedding recover
the literal scalar form, with its whole domain and mixed bilinear energy.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Riesz2.ScalarFormEmbedding

/-- Equality of scalar forms from equality of domains and all mixed energies. -/
theorem formData_ext {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (P Q : ScalarFormData μ) (hD : P.1 = Q.1)
    (hB : ∀ u v, P.2 u v = Q.2 (LinearEquiv.ofEq P.1 Q.1 hD u) (LinearEquiv.ofEq P.1 Q.1 hD v)) : P = Q := by
  rcases P with ⟨D,B⟩
  rcases Q with ⟨D',B'⟩
  dsimp only at hD
  subst D'
  congr 1
  ext u v
  exact hB u v

variable {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
  (μ : Measure X) (f : X → Z) (hf : MeasurableEmbedding f)

/-- Pushing the restriction of a scalar form back to its image recovers it exactly. -/
theorem form_restriction (Q : ScalarFormData (μ.map f)) :
    form μ f hf (restriction μ f hf Q) = Q := by
  let P := form μ f hf (restriction μ f hf Q)
  have hD : P.1 = Q.1 := by
    ext u
    change (pullback μ f hf).symm (pullback μ f hf u) ∈ Q.1 ↔ u ∈ Q.1
    rw [LinearIsometryEquiv.symm_apply_apply]
  apply formData_ext P Q hD
  intro u v
  change Q.2 (restrictionEquiv μ f hf Q (domainEquiv μ f hf _ u))
    (restrictionEquiv μ f hf Q (domainEquiv μ f hf _ v)) = _
  have he (w : P.1) : restrictionEquiv μ f hf Q (domainEquiv μ f hf _ w) =
      LinearEquiv.ofEq P.1 Q.1 hD w := by
    apply Subtype.ext
    exact (pullback μ f hf).symm_apply_apply w.val
  rw [he,he]

/-- Restriction of the pushed scalar form recovers the original form exactly. -/
theorem restriction_form (Q : ScalarFormData μ) :
    restriction μ f hf (form μ f hf Q) = Q := by
  let P := restriction μ f hf (form μ f hf Q)
  have hD : P.1 = Q.1 := by
    ext u
    change pullback μ f hf ((pullback μ f hf).symm u) ∈ Q.1 ↔ u ∈ Q.1
    rw [LinearIsometryEquiv.apply_symm_apply]
  apply formData_ext P Q hD
  intro u v
  change Q.2 (domainEquiv μ f hf Q (restrictionEquiv μ f hf _ u))
    (domainEquiv μ f hf Q (restrictionEquiv μ f hf _ v)) = _
  have he (w : P.1) : domainEquiv μ f hf Q (restrictionEquiv μ f hf _ w) =
      LinearEquiv.ofEq P.1 Q.1 hD w := by
    apply Subtype.ext
    exact (pullback μ f hf).apply_symm_apply w.val
  rw [he,he]

end Riesz2.ScalarFormEmbedding
