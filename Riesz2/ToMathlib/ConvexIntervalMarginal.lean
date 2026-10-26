/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.HelfferSjostrand.ConvexLocalization

/-!
# Continuous interval marginals with a removable potential

The density is the actual fibre integral. Positivity, finiteness and continuity
hold at every point of the open projection, including zero-dimensional fibres.
-/

public section

noncomputable section

open MeasureTheory Set

namespace Riesz2

/-- Internal fibre-integral interface: a potential depending only on the base
coordinate factors out of the marginal. Both convex potentials give concave
logarithms on the entire projection. -/
theorem convex_interval_marginal {n : ℕ}
    {Q : Set (ℝ × EuclideanSpace ℝ (Fin n))}
    {V R : ℝ × EuclideanSpace ℝ (Fin n) → ℝ}
    (hQo : IsOpen Q) (hQb : Bornology.IsBounded Q)
    (hV : ConvexOn ℝ Q V) (hR : ConvexOn ℝ Q R)
    (B : ℝ → ℝ) (he : ∀ p ∈ Q, V p = B p.1 + R p)
    {c : ℝ} (hc : 0 < c) :
    let f := fun u => c * ∫ z, Q.indicator (fun p => Real.exp (-V p)) (u, z)
    let h := fun u => c * ∫ z, Q.indicator (fun p => Real.exp (-R p)) (u, z)
    ContinuousOn f (Prod.fst '' Q) ∧
      (∀ u ∈ Prod.fst '' Q, 0 < f u ∧ 0 < h u) ∧
      (∀ u, f u = Real.exp (-B u) * h u) ∧
      ConcaveOn ℝ (Prod.fst '' Q) (fun u => Real.log (f u)) ∧
      ConcaveOn ℝ (Prod.fst '' Q) (fun u => Real.log (h u)) := by
  dsimp only
  have hJ := convexLocalization hQo hV.1 hQb hV (fun _ => 0)
  have hK := convexLocalization hQo hR.1 hQb hR (fun _ => 0)
  have hlog {A : ℝ × EuclideanSpace ℝ (Fin n) → ℝ}
      (hp : ∀ u ∈ Prod.fst '' Q,
        0 < ∫ z, Q.indicator (fun p => Real.exp (-A p)) (u, z))
      (hconv : ConvexOn ℝ (Prod.fst '' Q)
        (fun u => (0 - Real.log (∫ z,
          Q.indicator (fun p => Real.exp (-A p)) (u, z))) - 0)) :
      ConcaveOn ℝ (Prod.fst '' Q) (fun u => Real.log
        (c * ∫ z, Q.indicator (fun p => Real.exp (-A p)) (u, z))) := by
    have ht : ConcaveOn ℝ (Prod.fst '' Q)
        (fun u => Real.log (∫ z, Q.indicator (fun p => Real.exp (-A p)) (u, z))) := by
      apply hconv.neg.congr
      intro u _
      change -((0 - _) - 0) = _
      ring
    have hh := (concaveOn_const (c := Real.log c) ht.1).add ht
    apply hh.congr
    intro u hu
    exact (Real.log_mul hc.ne' (hp u hu).ne').symm
  refine ⟨(Riesz1.continuousOn_marginal_exp_indicator hQo hV.1 hQb hV).const_mul c,
    fun u hu => ⟨mul_pos hc (hJ.1 u hu).2, mul_pos hc (hK.1 u hu).2⟩, ?_,
    hlog (fun u hu => (hJ.1 u hu).2) hJ.2,
    hlog (fun u hu => (hK.1 u hu).2) hK.2⟩
  intro u
  have hi : (fun z => Q.indicator (fun p => Real.exp (-V p)) (u, z)) =
      fun z => Real.exp (-B u) * Q.indicator (fun p => Real.exp (-R p)) (u, z) := by
    funext z
    by_cases hz : (u, z) ∈ Q
    · rw [indicator_of_mem hz, indicator_of_mem hz, he _ hz,
        neg_add, Real.exp_add]
    · rw [indicator_of_notMem hz, indicator_of_notMem hz, mul_zero]
  rw [hi, integral_const_mul]
  ring

end Riesz2

end
