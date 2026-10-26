/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.InterpolationMatrixPart2
public import Riesz2.Thermodynamic.InterpolationPerturbation
public import Riesz2.Thermodynamic.InterpolationExceptional

/-!
# Fixed-exterior boundary identification

See Subsection 6.1 of the paper. The active-first internal matrix and exterior-first
physical assembly have the same internal coefficients. Their difference is the literal
fixed-exterior boundary matrix, with the original ordered-pair and antipodal
multiplicities.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical ContDiff

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.InterpolationBoundaryBridge

/-- See Subsection 6.1 of the paper: an internal interval weight depends only on
active coordinates, irrespective of the assembly used for the exterior. -/
theorem internal_weight_congr (s : Riesz1.RieszExponent) (N : ℕ+) (n : ℕ)
    (hn : n ≤ (N : ℕ)) (x y : EuclideanSpace ℝ (Fin (N : ℕ)))
    (hxy : ∀ j : Fin n, x (j.castLE hn) = y (j.castLE hn))
    (i : Fin (N : ℕ)) (r : Fin ((N : ℕ)/2))
    (hi : IntervalBoundary.IsInternal N n (i,r)) :
    BoundaryEntries.intervalWeight s N r i x = BoundaryEntries.intervalWeight s N r i y := by
  have hsum : cyclicGapSum N i (r.val+1) (WithLp.ofLp x) =
      cyclicGapSum N i (r.val+1) (WithLp.ofLp y) := by
    rw [← sum_cyclicIndexInterval_eq_cyclicGapSum _ _ (by have := r.isLt; omega),
      ← sum_cyclicIndexInterval_eq_cyclicGapSum _ _ (by have := r.isLt; omega)]
    apply Finset.sum_congr rfl
    intro j hj
    let a : Fin n := ⟨j.val, hi j hj⟩
    have ha : a.castLE hn = j := Fin.ext rfl
    simpa only [ha] using hxy a
  simp only [BoundaryEntries.intervalWeight, hsum]

/-- See Subsection 6.1 of the paper: internal matrices agree for any two ambient
vectors with the same retained coordinates. -/
theorem internal_matrix_congr (s : Riesz1.RieszExponent) (N : ℕ+) (n : ℕ)
    (hn : n ≤ (N : ℕ)) (x y : EuclideanSpace ℝ (Fin (N : ℕ)))
    (hxy : ∀ j : Fin n, x (j.castLE hn) = y (j.castLE hn)) :
    IntervalBoundary.internalMatrix N n hn (fun ir => BoundaryEntries.intervalWeight s N ir.2 ir.1 x) =
      IntervalBoundary.internalMatrix N n hn (fun ir => BoundaryEntries.intervalWeight s N ir.2 ir.1 y) := by
  ext a b
  apply Finset.sum_congr rfl
  intro ir _
  by_cases hi : IntervalBoundary.IsInternal N n ir
  · simp only [hi, ite_true]
    rw [internal_weight_congr s N n hn x y hxy ir.1 ir.2 hi]
  · simp only [hi, ite_false]

/-- See Subsection 6.1 of the paper: the active-first physical internal matrix is
also the internal matrix of any full vector having these active gaps.
The period equality is only an index binding, with no analytic premise. -/
theorem physical_internal_eq (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (n : ℕ+) (d : ℕ) (N : ℕ+) (hN : (N : ℕ) = (n : ℕ)+d+1)
    (hn : 2*(n : ℕ) ≤ (N : ℕ))
    (x : AffineSimplex.chartDomain n ((n+d : ℕ)+1))
    (v : EuclideanSpace ℝ (Fin (N : ℕ)))
    (hv : ∀ j : Fin (n : ℕ), v (j.castLE (show (n : ℕ) ≤ (N : ℕ) by omega)) = x.val j) :
    BoundaryEntries.physicalInternal β s n d x =
      IntervalBoundary.internalMatrix N n (by omega)
        (fun ir => BoundaryEntries.intervalWeight s N ir.2 ir.1 v) := by
  rcases N with ⟨N,hpos⟩
  change N = (n : ℕ)+d+1 at hN
  subst N
  rw [InterpolationMatrix.physicalInternal_eq_internalMatrix β s n d hn x 0]
  apply internal_matrix_congr
  intro j
  rw [hv]
  change RetainedSimplex.join n (d+1) (x.val,0) (j.castLE _) = x.val j
  have hj : j.castLE (show (n : ℕ) ≤ (n : ℕ)+d+1 by omega) = j.castAdd (d+1) := Fin.ext rfl
  rw [hj, RetainedSimplex.join_left]

/-- See Subsection 6.1 of the paper: the differential interval weight equals the
physical coefficient on the whole open ambient domain, including its
antipodal multiplier. The positivity certificate does not affect its value. -/
theorem interval_weight_physical (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (N : ℕ+) (v : EuclideanSpace ℝ (Fin (N : ℕ)))
    (H : ∀ ir : Fin (N : ℕ) × Fin ((N : ℕ)/2),
      0 < cyclicGapSum N ir.1 (ir.2.val+1) (WithLp.ofLp v) ∧
      cyclicGapSum N ir.1 (ir.2.val+1) (WithLp.ofLp v) < (N : ℝ))
    (ir : Fin (N : ℕ) × Fin ((N : ℕ)/2)) :
    BoundaryEntries.intervalWeight s N ir.2 ir.1 v =
      (2 - if 2*(ir.2.val+1) = (N : ℕ) then (1 : ℝ) else 0) *
        PhysicalEnergy.intervalCoefficient (ofLong β s) N
          ⟨cyclicGapSum N ir.1 (ir.2.val+1) (WithLp.ofLp v), H ir⟩ := by
  simp only [BoundaryEntries.intervalWeight, PhysicalEnergy.intervalCoefficient,
    PhysicalEnergy.kernelDerivative, ofLong, s.property.2, ↓reduceDIte,
    PhysicalEnergy.scaledSeparation, PNat.val_ofNat]

/-- Internal realization bridge for Subsection 6.1: the
unrestricted Hessian of any realization of the ambient endpoint
energy is the literal full interval matrix. Agreement is required on the
entire open assembly preimage, so normal derivatives are fixed too. -/
theorem endpoint_hessian_internal (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (e a : ℕ) (y : AffineSimplex.chartDomain e ((e+a : ℕ)+1))
    (Ky : EuclideanSpace ℝ (Fin (a+1)) → ℝ)
    (hKy : ∀ u, ∀ hu : RetainedSimplex.assemble e a
        (InterpolatingDensities.exteriorPermutation e a) y.val u ∈ gapAmbientDomain (e+a).succPNat,
      Ky u = physicalAmbientGapEnergy (ofLong β s) (e+a).succPNat
        ⟨RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val u, hu⟩)
    (u : EuclideanSpace ℝ (Fin (a+1)))
    (hu : u ∈ AffineSimplex.massSimplex a (((e+a : ℕ)+1 : ℝ)-∑ k, y.val k))
    (H : ∀ ir : Fin (e+a+1) × Fin ((e+a+1)/2),
      0 < cyclicGapSum (e+a).succPNat ir.1 (ir.2.val+1)
        (WithLp.ofLp (RetainedSimplex.assemble e a
          (InterpolatingDensities.exteriorPermutation e a) y.val u)) ∧
      cyclicGapSum (e+a).succPNat ir.1 (ir.2.val+1)
        (WithLp.ofLp (RetainedSimplex.assemble e a
          (InterpolatingDensities.exteriorPermutation e a) y.val u)) < ((e+a).succPNat : ℝ)) :
    hessianMatrix Ky u = IntervalBoundary.intervalMatrix (e+a).succPNat (a+1) (by change a+1 ≤ e+a+1; omega)
      (fun ir => (2 - if 2*(ir.2.val+1) = e+a+1 then (1 : ℝ) else 0) *
        PhysicalEnergy.intervalCoefficient (ofLong β s) (e+a).succPNat
          ⟨cyclicGapSum (e+a).succPNat ir.1 (ir.2.val+1)
            (WithLp.ofLp (RetainedSimplex.assemble e a
              (InterpolatingDensities.exteriorPermutation e a) y.val u)), H ir⟩) := by
  let N := (e+a).succPNat
  let Y := RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) y.val
  let D := Y ⁻¹' gapAmbientDomain N
  have hD : IsOpen D := (PhysicalEnergy.isOpen_gapAmbientDomain N).preimage
    (RetainedSimplex.continuous_assemble e a _ y.val)
  have hsimplex := InterpolatingDensities.assemble_exterior_mem e a y u hu
  have hs : WithLp.ofLp (Y u) ∈ Riesz1.gapSimplex N :=
    ⟨hsimplex.1, by simpa only [N, Nat.succPNat_coe, Nat.cast_succ] using hsimplex.2⟩
  have huD : u ∈ D := PhysicalEnergy.simplex_subset_ambient N _ hs
  obtain ⟨W, hW, hval, hmat⟩ :=
    CrossingCoefficients.ambient_hessian_intervalMatrix_internal (ofLong β s) N
  have heq : EqOn Ky (fun v => W (Y v)) D := by
    intro v hv
    exact (hKy v hv).trans (hval ⟨Y v,hv⟩).symm
  rw [InterpolationExceptional.hessian_eqOn_internal hD heq huD]
  ext i j
  rw [InterpolationExceptional.hessian_assembly_internal e a y.val W u
    (hW.contDiffAt ((PhysicalEnergy.isOpen_gapAmbientDomain N).mem_nhds huD)) i j]
  exact hmat ⟨Y u,huD⟩ a.succPNat (by dsimp [N]; omega) i j

/-- Internal bridge for Subsection 6.1: subtracting the physical
active-first internal block from the actual fixed-exterior endpoint
Hessian leaves exactly its exterior-first boundary interval matrix. -/
theorem endpoint_boundary_internal (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (a d b : ℕ) (hN : b+a+1 = (a+1)+d+1) (hn : 2*(a+1) ≤ b+a+1)
    (y : AffineSimplex.chartDomain b ((b+a : ℕ)+1))
    (x : AffineSimplex.chartDomain a.succPNat ((a.succPNat+d : ℕ)+1))
    (hx : x.val ∈ AffineSimplex.massSimplex a (((b+a : ℕ)+1 : ℝ)-∑ k, y.val k))
    (Ky : EuclideanSpace ℝ (Fin (a+1)) → ℝ)
    (hKy : ∀ u, ∀ hu : RetainedSimplex.assemble b a
        (InterpolatingDensities.exteriorPermutation b a) y.val u ∈ gapAmbientDomain (b+a).succPNat,
      Ky u = physicalAmbientGapEnergy (ofLong β s) (b+a).succPNat
        ⟨RetainedSimplex.assemble b a (InterpolatingDensities.exteriorPermutation b a) y.val u, hu⟩)
    (H : ∀ ir : Fin (b+a+1) × Fin ((b+a+1)/2),
      0 < cyclicGapSum (b+a).succPNat ir.1 (ir.2.val+1)
        (WithLp.ofLp (RetainedSimplex.assemble b a
          (InterpolatingDensities.exteriorPermutation b a) y.val x.val)) ∧
      cyclicGapSum (b+a).succPNat ir.1 (ir.2.val+1)
        (WithLp.ofLp (RetainedSimplex.assemble b a
          (InterpolatingDensities.exteriorPermutation b a) y.val x.val)) < ((b+a).succPNat : ℝ)) :
    hessianMatrix Ky x.val - (show Matrix (Fin (a+1)) (Fin (a+1)) ℝ from
      BoundaryEntries.physicalInternal β s a.succPNat d x) =
      IntervalBoundary.boundaryMatrix (b+a).succPNat (a+1) (by change a+1 ≤ b+a+1; omega)
        (fun ir => (2 - if 2*(ir.2.val+1) = b+a+1 then (1 : ℝ) else 0) *
          PhysicalEnergy.intervalCoefficient (ofLong β s) (b+a).succPNat
            ⟨cyclicGapSum (b+a).succPNat ir.1 (ir.2.val+1)
              (WithLp.ofLp (RetainedSimplex.assemble b a
                (InterpolatingDensities.exteriorPermutation b a) y.val x.val)), H ir⟩) := by
  let V := RetainedSimplex.assemble b a (InterpolatingDensities.exteriorPermutation b a) y.val x.val
  have hi := physical_internal_eq β s a.succPNat d (b+a).succPNat hN hn x V
    (fun j => InterpolatingDensities.assemble_exterior_active b a y.val x.val j (by omega))
  have hF := funext (interval_weight_physical β s (b+a).succPNat V H)
  rw [hF] at hi
  rw [endpoint_hessian_internal β s b a y Ky hKy x.val hx H, hi]
  apply sub_eq_iff_eq_add.mpr
  exact (IntervalBoundary.internal_add_boundary _ _ _ _).symm.trans (add_comm _ _)

/-- Internal finite assembly for Subsection 6.1:
on the common mass fibre the physical interpolated interaction Hessian
minus `internalBlock` is literally the convex combination of the two
fixed-exterior boundary matrices used by the crossing-profile theorem. -/
theorem interpolant_boundary_internal (β : InverseTemperature) (s : Riesz1.RieszExponent)
    (a d e b c : ℕ) (hde : d ≤ e)
    (hN : b+a+1 = (a+1)+d+1) (hM : c+a+1 = (a+1)+e+1)
    (hn : 2*(a+1) ≤ b+a+1)
    (y : AffineSimplex.chartDomain b ((b+a : ℕ)+1))
    (z : AffineSimplex.chartDomain c ((c+a : ℕ)+1))
    (Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ)
    (hKy : ∀ u, ∀ hu : RetainedSimplex.assemble b a
        (InterpolatingDensities.exteriorPermutation b a) y.val u ∈ gapAmbientDomain (b+a).succPNat,
      Ky u = physicalAmbientGapEnergy (ofLong β s) (b+a).succPNat
        ⟨RetainedSimplex.assemble b a (InterpolatingDensities.exteriorPermutation b a) y.val u, hu⟩)
    (hKz : ∀ u, ∀ hu : RetainedSimplex.assemble c a
        (InterpolatingDensities.exteriorPermutation c a) z.val u ∈ gapAmbientDomain (c+a).succPNat,
      Kz u = physicalAmbientGapEnergy (ofLong β s) (c+a).succPNat
        ⟨RetainedSimplex.assemble c a (InterpolatingDensities.exteriorPermutation c a) z.val u, hu⟩)
    (t : ℝ) (x : AffineSimplex.chartDomain a.succPNat ((a.succPNat+d : ℕ)+1))
    (hxy : x.val ∈ AffineSimplex.massSimplex a (((b+a : ℕ)+1 : ℝ)-∑ k, y.val k))
    (hxz : x.val ∈ AffineSimplex.massSimplex a (((c+a : ℕ)+1 : ℝ)-∑ k, z.val k)) :
    let v := WithLp.ofLp (RetainedSimplex.assemble b a
      (InterpolatingDensities.exteriorPermutation b a) y.val x.val)
    let w := WithLp.ofLp (RetainedSimplex.assemble c a
      (InterpolatingDensities.exteriorPermutation c a) z.val x.val)
    ∀ (H : ∀ ir : Fin (b+a+1) × Fin ((b+a+1)/2),
      0 < cyclicGapSum (b+a).succPNat ir.1 (ir.2.val+1) v ∧
      cyclicGapSum (b+a).succPNat ir.1 (ir.2.val+1) v < ((b+a).succPNat : ℝ))
    (J : ∀ ir : Fin (c+a+1) × Fin ((c+a+1)/2),
      0 < cyclicGapSum (c+a).succPNat ir.1 (ir.2.val+1) w ∧
      cyclicGapSum (c+a).succPNat ir.1 (ir.2.val+1) w < ((c+a).succPNat : ℝ)),
    let Py := IntervalBoundary.boundaryMatrix (b+a).succPNat (a+1)
      (by change a+1 ≤ b+a+1; omega)
      (fun ir => (2 - if 2*(ir.2.val+1) = b+a+1 then (1 : ℝ) else 0) *
        PhysicalEnergy.intervalCoefficient (ofLong β s) (b+a).succPNat
          ⟨cyclicGapSum (b+a).succPNat ir.1 (ir.2.val+1) v, H ir⟩)
    let Pz := IntervalBoundary.boundaryMatrix (c+a).succPNat (a+1)
      (by change a+1 ≤ c+a+1; omega)
      (fun ir => (2 - if 2*(ir.2.val+1) = c+a+1 then (1 : ℝ) else 0) *
        PhysicalEnergy.intervalCoefficient (ofLong β s) (c+a).succPNat
          ⟨cyclicGapSum (c+a).succPNat ir.1 (ir.2.val+1) w, J ir⟩)
    let P : AffineSimplex.chartDomain a.succPNat ((a.succPNat+d : ℕ)+1) →
        Matrix (Fin (a+1)) (Fin (a+1)) ℝ :=
      fun q => (1-t) • hessianMatrix Ky q.val + t • hessianMatrix Kz q.val
    P x - (show Matrix (Fin (a+1)) (Fin (a+1)) ℝ from
      InterpolationMatrix.internalBlock β s a.succPNat d e hde t x) = (1-t) • Py + t • Pz := by
  intro v w H J Py Pz P
  have hy := endpoint_boundary_internal β s a d b hN hn y x hxy Ky hKy H
  have hz := endpoint_boundary_internal β s a e c hM (by omega) z
    (InterpolationMatrix.largerChart a.succPNat d e hde x) hxz Kz hKz J
  ext i j
  have hyij := congrArg (fun A : Matrix (Fin (a+1)) (Fin (a+1)) ℝ => A i j) hy
  have hzij := congrArg (fun A : Matrix (Fin (a+1)) (Fin (a+1)) ℝ => A i j) hz
  simp only [Matrix.sub_apply] at hyij hzij
  change (1-t)*hessianMatrix Ky x.val i j + t*hessianMatrix Kz x.val i j -
    ((1-t)*BoundaryEntries.physicalInternal β s a.succPNat d x i j +
      t*BoundaryEntries.physicalInternal β s a.succPNat e
        (InterpolationMatrix.largerChart a.succPNat d e hde x) i j) =
    (1-t)*Py i j + t*Pz i j
  change hessianMatrix Ky x.val i j - _ = Py i j at hyij
  change hessianMatrix Kz x.val i j - _ = Pz i j at hzij
  linear_combination (1-t)*hyij + t*hzij

/-- See Subsection 6.1 of the paper, good branch of the multiplication defect.
The physical field is the actual interpolated endpoint Hessian. The loss
exponent precedes ε, the size threshold precedes temperature, and one
prefactor works for all positive temperatures bounded by `βhi`.
The realization premises specify the energy on an open ambient
neighborhood, rather than assuming a Hessian or coefficient estimate. -/
theorem physical_good_profiles_internal (s : Riesz1.RieszExponent)
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → s.val/2+2*ε < 1 →
      ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ βhi : ℝ, 0 < βhi → ∃ A : ℝ, 0 < A ∧
      ∀ (β : InverseTemperature), β.val ≤ βhi →
      ∀ (a d e b c : ℕ) (hde : d ≤ e),
      b+a+1 = (a+1)+d+1 → c+a+1 = (a+1)+e+1 →
      n₀ ≤ a+1 → 4*(a+1) ≤ b+a+1 →
      ∀ (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : a+1 ≤ (M : ℕ)) (k : ℕ),
      2*(a+1) ≤ (M : ℕ) →
      ∀ (θ : PhysicalCutoff) (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
      ∀ (y : AffineSimplex.chartDomain b ((b+a : ℕ)+1))
        (z : AffineSimplex.chartDomain c ((c+a : ℕ)+1)),
      InterpolantLocalLaws.exteriorGeometry s.val ε b a y.val →
      InterpolantLocalLaws.exteriorGeometry s.val ε c a z.val →
      ∀ Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ,
      (∀ u, ∀ hu : RetainedSimplex.assemble b a
          (InterpolatingDensities.exteriorPermutation b a) y.val u ∈ gapAmbientDomain (b+a).succPNat,
        Ky u = physicalAmbientGapEnergy (ofLong β s) (b+a).succPNat
          ⟨RetainedSimplex.assemble b a (InterpolatingDensities.exteriorPermutation b a) y.val u, hu⟩) →
      (∀ u, ∀ hu : RetainedSimplex.assemble c a
          (InterpolatingDensities.exteriorPermutation c a) z.val u ∈ gapAmbientDomain (c+a).succPNat,
        Kz u = physicalAmbientGapEnergy (ofLong β s) (c+a).succPNat
          ⟨RetainedSimplex.assemble c a (InterpolatingDensities.exteriorPermutation c a) z.val u, hu⟩) →
      let n := a.succPNat
      let P : AffineSimplex.chartDomain n ((n+d : ℕ)+1) →
          Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ :=
        fun q i j => (1-t)*hessianMatrix Ky q.val i j + t*hessianMatrix Kz q.val i j
      let Y := InterpolationMatrix.multiplicationPart β s n d e hde M hM hnM k θ ε (K*ε) t P
      let w : Fin (n : ℕ) → ℝ := fun i =>
        (min (i.val+1) ((n : ℕ)-i.val) : ℕ)^(-s.val/2)
      let v : Fin (n : ℕ) → Fin (n : ℕ) → Fin (n : ℕ) → ℝ := fun j i l =>
        (Nat.dist i.val l.val : ℝ)*w j*
          (min (min (i.val+1) ((n : ℕ)-i.val))
            (min (l.val+1) ((n : ℕ)-l.val)) : ℕ)^(-1-s.val/2)
      ∀ x : AffineSimplex.chartDomain n ((n+d : ℕ)+1),
      x.val ∈ AffineSimplex.massSimplex a (((b+a : ℕ)+1 : ℝ)-∑ k, y.val k) →
      x.val ∈ AffineSimplex.massSimplex a (((c+a : ℕ)+1 : ℝ)-∑ k, z.val k) →
      x ∈ InterpolationMatrix.goodSet s n d (K*ε) →
      ∀ i j l : Fin (n : ℕ),
      |Y x j i| ≤ A*(n : ℝ)^(ρ*ε)*w i*w j ∧
      |Y x j i-Y x j l| ≤ A*(n : ℝ)^(ρ*ε)*v j i l := by
  obtain ⟨κ, hκ, hp⟩ := CrossingCoefficients.physical_interpolant_boundary_profiles s K hK
  let ρ := max κ 1
  have hρ : 0 < ρ := lt_of_lt_of_le hκ (le_max_left _ _)
  refine ⟨ρ,hρ,fun ε hε hσε => ?_⟩
  obtain ⟨Cp,hCp,n₀,hn₀,hp⟩ := hp ε hε hσε
  obtain ⟨Cr,hCr,hr⟩ := InterpolationPerturbation.reference_crossing_profiles s ε hε
  refine ⟨n₀,hn₀,fun βhi hβhi => ⟨βhi*(Cp+Cr),by positivity,?_⟩⟩
  intro β hβ a d e b c hde hN hM' hnn hsize M hM hnM k hhalf θ t ht y z hgy hgz
    Ky Kz hKy hKz n P Y w v x hxy hxz hx i j l
  have hbc : b ≤ c := by omega
  have hgood : WithLp.ofLp x.val ∈ goodBlockEvent s.val a.succPNat (b+a).succPNat (K*ε) := by
    have hper : (b+a).succPNat = ((a.succPNat : ℕ)+d).succPNat := by
      apply PNat.eq
      simpa only [Nat.succPNat_coe] using hN
    rw [hper]
    exact hx
  obtain ⟨H,J,hprofile⟩ := hp (ofLong β s) rfl b c a hbc hnn hsize y z hgy hgz x.val hxy hxz hgood
  have hid := interpolant_boundary_internal β s a d e b c hde hN hM' (by omega)
    y z Ky Kz hKy hKz t x hxy hxz H J
  obtain ⟨hpp,hpd⟩ := hprofile t ht
  obtain ⟨hrp,hrd⟩ := hr n M hM hnM k hhalf i j l
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hpowp : (n : ℝ)^(κ*ε) ≤ (n : ℝ)^(ρ*ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (mul_le_mul_of_nonneg_right (le_max_left _ _) hε.le)
  have hpowr : (n : ℝ)^ε ≤ (n : ℝ)^(ρ*ε) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by
      have hh := mul_le_mul_of_nonneg_right (le_max_right κ 1) hε.le
      simpa only [one_mul] using hh)
  have hnreal : (n : ℝ) = a+1 := by simp only [n, Nat.succPNat_coe, Nat.cast_succ]
  have hw (q : Fin (n : ℕ)) : 0 ≤ w q := by dsimp only [w]; positivity
  have hv : 0 ≤ v j i l := by dsimp only [v]; positivity
  let B : Matrix (Fin (a+1)) (Fin (a+1)) ℝ :=
    (1-t) • IntervalBoundary.boundaryMatrix (b+a).succPNat (a+1)
      (by change a+1 ≤ b+a+1; omega)
      (fun ir => (2 - if 2*(ir.2.val+1) = b+a+1 then (1 : ℝ) else 0) *
        PhysicalEnergy.intervalCoefficient (ofLong β s) (b+a).succPNat
          ⟨cyclicGapSum (b+a).succPNat ir.1 (ir.2.val+1)
            (WithLp.ofLp (RetainedSimplex.assemble b a
              (InterpolatingDensities.exteriorPermutation b a) y.val x.val)),H ir⟩) +
    t • IntervalBoundary.boundaryMatrix (c+a).succPNat (a+1)
      (by change a+1 ≤ c+a+1; omega)
      (fun ir => (2 - if 2*(ir.2.val+1) = c+a+1 then (1 : ℝ) else 0) *
        PhysicalEnergy.intervalCoefficient (ofLong β s) (c+a).succPNat
          ⟨cyclicGapSum (c+a).succPNat ir.1 (ir.2.val+1)
            (WithLp.ofLp (RetainedSimplex.assemble c a
              (InterpolatingDensities.exteriorPermutation c a) z.val x.val)),J ir⟩)
  have hpB : |B j i| ≤ Cp*(n : ℝ)^(ρ*ε)*w i*w j := by
    have hh := hpp j i
    change |B j i| ≤ Cp*(a+1 : ℝ)^(κ*ε)*w j*w i at hh
    apply hh.trans
    calc
      _ ≤ Cp*(n : ℝ)^(ρ*ε)*w j*w i := by
        rw [← hnreal]
        gcongr
      _ = _ := by ring
  have hdB : |B j i-B j l| ≤ Cp*(n : ℝ)^(ρ*ε)*v j i l := by
    have hh := hpd j i l
    simp only [← Nat.cast_min] at hh
    have hh' : |B j i-B j l| ≤ Cp*(n : ℝ)^(κ*ε)*v j i l := by
      convert hh using 1
      · rfl
      · simp only [v,w,n,Nat.succPNat_coe,Nat.cast_succ]
        ring
    exact hh'.trans (by gcongr)
  have hpR : |BoundaryEntries.referenceCrossing s M hM k n hnM j i| ≤
      Cr*(n : ℝ)^(ρ*ε)*w i*w j := hrp.trans (by gcongr)
  have hdR : |BoundaryEntries.referenceCrossing s M hM k n hnM j i-
      BoundaryEntries.referenceCrossing s M hM k n hnM j l| ≤
      Cr*(n : ℝ)^(ρ*ε)*v j i l := by
    have hh : |BoundaryEntries.referenceCrossing s M hM k n hnM j i-
        BoundaryEntries.referenceCrossing s M hM k n hnM j l| ≤
        Cr*(n : ℝ)^ε*v j i l := by
      convert hrd using 1
      dsimp only [v,w]
      ring
    exact hh.trans (by gcongr)
  have hY (q r : Fin (n : ℕ)) : Y x q r =
      β.val*(B q r-BoundaryEntries.referenceCrossing s M hM k n hnM q r) := by
    have hh := congrArg (fun A : Matrix (Fin (a+1)) (Fin (a+1)) ℝ => A q r) hid
    change P x q r-InterpolationMatrix.internalBlock β s n d e hde t x q r = B q r at hh
    change (InterpolationMatrix.multiplicationPart β s n d e hde M hM hnM k θ ε (K*ε) t P x) q r = _
    rw [InterpolationMatrix.multiplicationPart,ite_eq_left hx]
    change β.val*(P x q r-InterpolationMatrix.internalBlock β s n d e hde t x q r-
      BoundaryEntries.referenceCrossing s M hM k n hnM q r) = _
    rw [hh]
  constructor
  · rw [hY,abs_mul,abs_of_pos β.property]
    have hb := (abs_sub _ _).trans (add_le_add hpB hpR)
    calc
      _ ≤ β.val*((Cp+Cr)*(n : ℝ)^(ρ*ε)*w i*w j) := by
        apply mul_le_mul_of_nonneg_left _ β.property.le
        convert hb using 1
        ring
      _ ≤ βhi*((Cp+Cr)*(n : ℝ)^(ρ*ε)*w i*w j) := by gcongr
      _ = _ := by ring
  · rw [hY,hY,← mul_sub,abs_mul,abs_of_pos β.property]
    have halg : (B j i-BoundaryEntries.referenceCrossing s M hM k n hnM j i)-
        (B j l-BoundaryEntries.referenceCrossing s M hM k n hnM j l) =
        (B j i-B j l)-(BoundaryEntries.referenceCrossing s M hM k n hnM j i-
          BoundaryEntries.referenceCrossing s M hM k n hnM j l) := by ring
    rw [halg]
    have hb := (abs_sub _ _).trans (add_le_add hdB hdR)
    calc
      _ ≤ β.val*((Cp+Cr)*(n : ℝ)^(ρ*ε)*v j i l) := by
        apply mul_le_mul_of_nonneg_left _ β.property.le
        convert hb using 1
        ring
      _ ≤ βhi*((Cp+Cr)*(n : ℝ)^(ρ*ε)*v j i l) := by gcongr
      _ = _ := by ring

/-- Internal transport interface for Subsection 6.1.
For the actual physical Hessian field this is precisely premise 1 of
`InterpolationPerturbation.perturbation_bounds_from_profiles_internal`.
The only law premise is support on the common physical mass fibre. The
transport composition must supply it for its chart measure. No profile
estimate is assumed. Constants have the same order as the pointwise theorem. -/
theorem physical_good_profiles_ae_internal (s : Riesz1.RieszExponent)
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → s.val/2+2*ε < 1 →
      ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ βhi : ℝ, 0 < βhi → ∃ A : ℝ, 0 < A ∧
      ∀ (β : InverseTemperature), β.val ≤ βhi →
      ∀ (a d e b c : ℕ) (hde : d ≤ e),
      b+a+1 = (a+1)+d+1 → c+a+1 = (a+1)+e+1 →
      n₀ ≤ a+1 → 4*(a+1) ≤ b+a+1 →
      ∀ (M : ℕ+) (hM : 2 ≤ (M : ℕ)) (hnM : a+1 ≤ (M : ℕ)) (k : ℕ),
      2*(a+1) ≤ (M : ℕ) →
      ∀ (θ : PhysicalCutoff) (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
      ∀ (y : AffineSimplex.chartDomain b ((b+a : ℕ)+1))
        (z : AffineSimplex.chartDomain c ((c+a : ℕ)+1)),
      InterpolantLocalLaws.exteriorGeometry s.val ε b a y.val →
      InterpolantLocalLaws.exteriorGeometry s.val ε c a z.val →
      ∀ Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ,
      (∀ u, ∀ hu : RetainedSimplex.assemble b a
          (InterpolatingDensities.exteriorPermutation b a) y.val u ∈ gapAmbientDomain (b+a).succPNat,
        Ky u = physicalAmbientGapEnergy (ofLong β s) (b+a).succPNat
          ⟨RetainedSimplex.assemble b a (InterpolatingDensities.exteriorPermutation b a) y.val u, hu⟩) →
      (∀ u, ∀ hu : RetainedSimplex.assemble c a
          (InterpolatingDensities.exteriorPermutation c a) z.val u ∈ gapAmbientDomain (c+a).succPNat,
        Kz u = physicalAmbientGapEnergy (ofLong β s) (c+a).succPNat
          ⟨RetainedSimplex.assemble c a (InterpolatingDensities.exteriorPermutation c a) z.val u, hu⟩) →
      let n := a.succPNat
      let P : AffineSimplex.chartDomain n ((n+d : ℕ)+1) →
          Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ :=
        fun q i j => (1-t)*hessianMatrix Ky q.val i j + t*hessianMatrix Kz q.val i j
      let Y := InterpolationMatrix.multiplicationPart β s n d e hde M hM hnM k θ ε (K*ε) t P
      let w : Fin (n : ℕ) → ℝ := fun i =>
        (min (i.val+1) ((n : ℕ)-i.val) : ℕ)^(-s.val/2)
      let v : Fin (n : ℕ) → Fin (n : ℕ) → Fin (n : ℕ) → ℝ := fun j i l =>
        (Nat.dist i.val l.val : ℝ)*w j*
          (min (min (i.val+1) ((n : ℕ)-i.val))
            (min (l.val+1) ((n : ℕ)-l.val)) : ℕ)^(-1-s.val/2)
      ∀ ν : Measure (AffineSimplex.chartDomain n ((n+d : ℕ)+1)),
      (∀ᵐ x ∂ν,
        x.val ∈ AffineSimplex.massSimplex a (((b+a : ℕ)+1 : ℝ)-∑ k, y.val k) ∧
        x.val ∈ AffineSimplex.massSimplex a (((c+a : ℕ)+1 : ℝ)-∑ k, z.val k)) →
      ∀ᵐ x ∂ν.restrict (InterpolationMatrix.goodSet s n d (K*ε)),
      ∀ i j l : Fin (n : ℕ),
      |Y x j i| ≤ A*(n : ℝ)^(ρ*ε)*w i*w j ∧
      |Y x j i-Y x j l| ≤ A*(n : ℝ)^(ρ*ε)*v j i l := by
  obtain ⟨ρ,hρ,hp⟩ := physical_good_profiles_internal s K hK
  refine ⟨ρ,hρ,fun ε hε hσε => ?_⟩
  obtain ⟨n₀,hn₀,hp⟩ := hp ε hε hσε
  refine ⟨n₀,hn₀,fun βhi hβhi => ?_⟩
  obtain ⟨A,hA,hp⟩ := hp βhi hβhi
  refine ⟨A,hA,?_⟩
  intro β hβ a d e b c hde hN hM' hnn hsize M hM hnM k hhalf θ t ht y z hgy hgz
    Ky Kz hKy hKz n P Y w v ν hfibre
  have hp' := hp β hβ a d e b c hde hN hM' hnn hsize M hM hnM k hhalf θ t ht
    y z hgy hgz Ky Kz hKy hKz
  filter_upwards [ae_restrict_of_ae hfibre,
    ae_restrict_mem (InterpolationMatrix.measurableSet_goodSet s n d (K*ε))] with x hx hxg
  exact hp' x hx.1 hx.2 hxg

end Riesz2.InterpolationBoundaryBridge
