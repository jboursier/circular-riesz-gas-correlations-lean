/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.FixedLengthDecayLong
public import Riesz2.Thermodynamic.FixedLengthColumnComparison

/-!
# Long-range physical fixed-length decay

Composition on the normalized physical fibre law for Lemma 6.4. The auxiliary inverse
uses the same intrinsic scalar form as the physical comparison. The size threshold is
used only for upper coefficient estimates.
-/

@[expose] public section
noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators Classical MatrixOrder ENNReal ContDiff

set_option backward.isDefEq.respectTransparency false

namespace Riesz2.FixedLengthDecay

/-- See Lemma 6.4 of the paper: changing the loss unit preserves the literal
matrix predicate, including the long-interval threshold. -/
theorem matrix_bounds_rescale_internal {X : Type} [MeasurableSpace X]
    {ν : Measure X} (s : Riesz1.RieszExponent) (n m : ℕ+)
    (hm : 2 ≤ (m : ℕ)) (k : ℕ) (C κ γ ε K : ℝ) (hK : K ≠ 0)
    (M : X → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
    (hM : PeriodizedMatrixBounds (ν := ν) s n m hm k C κ γ ε M) :
    PeriodizedMatrixBounds (ν := ν) s n m hm k C (κ/K) (γ/K) (K*ε) M := by
  have hk : κ/K*(K*ε) = κ*ε := by field_simp
  have hg : γ/K*(K*ε) = γ*ε := by field_simp
  simpa only [PeriodizedMatrixBounds, hk, hg, neg_mul] using hM

/-- See Lemma 6.4 of the paper: normalize the physical curvature and Hessian
identity on an arbitrary included fibre measure. In particular the lower
curvature is uniform on a compact positive temperature interval. -/
theorem included_physical_lower_internal (p : Parameters) (θ : PhysicalCutoff)
    (ε : ℝ) (hε : 0 ≤ ε) (d e a : ℕ) (ha : 1 ≤ a)
    (y : AffineSimplex.chartDomain d ((d+a : ℕ)+1))
    (z : AffineSimplex.chartDomain e ((e+a : ℕ)+1)) (L : ℝ)
    (hyL : ((d+a : ℕ)+1 : ℝ)-∑ k, y.val k = L)
    (hzL : ((e+a : ℕ)+1 : ℝ)-∑ k, z.val k = L)
    (Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ)
    (hKy : ContDiffOn ℝ ∞ Ky (RetainedSimplex.assemble d a
      (InterpolatingDensities.exteriorPermutation d a) y.val ⁻¹' gapAmbientDomain (d+a).succPNat))
    (hKz : ContDiffOn ℝ ∞ Kz (RetainedSimplex.assemble e a
      (InterpolatingDensities.exteriorPermutation e a) z.val ⁻¹' gapAmbientDomain (e+a).succPNat))
    (hky : ∀ u (hu : RetainedSimplex.assemble d a
      (InterpolatingDensities.exteriorPermutation d a) y.val u ∈ gapAmbientDomain (d+a).succPNat),
      Ky u = physicalAmbientGapEnergy p (d+a).succPNat
        ⟨RetainedSimplex.assemble d a (InterpolatingDensities.exteriorPermutation d a) y.val u,hu⟩)
    (hkz : ∀ u (hu : RetainedSimplex.assemble e a
      (InterpolatingDensities.exteriorPermutation e a) z.val u ∈ gapAmbientDomain (e+a).succPNat),
      Kz u = physicalAmbientGapEnergy p (e+a).succPNat
        ⟨RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) z.val u,hu⟩)
    (N : ℝ) (hLN : L < N) (ρ : Measure (AffineSimplex.massSimplex a L))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (b : ℝ) (_hb : 0 < b) (hbp : b ≤ p.val.1) :
    let ν := ρ.map (InterpolationTransport.inclusion a L N hLN)
    let Ht := fun u : EuclideanSpace ℝ (Fin (a+1)) =>
      (∑ k, (θ.val ((a+1 : ℝ)^(-ε)*u k)+θ.val ((a+1 : ℝ)^(-ε)*(u k)⁻¹)))+(1-t)*Ky u+t*Kz u
    let H : AffineSimplex.chartDomain (a+1) N → Matrix (Fin (a+1)) (Fin (a+1)) ℝ :=
      fun q i j => p.val.1*(InterpolationMatrix.penaltyHessian a.succPNat θ ε q.val i j+
        ((1-t)*hessianMatrix Ky q.val i j+t*hessianMatrix Kz q.val i j))
    (fun q : AffineSimplex.chartDomain (a+1) N =>
      hessianMatrix (fun u => p.val.1*Ht u) q.val) =ᵐ[ν] H ∧
    (∀ᵐ q ∂ν, (H q).PosSemidef) ∧
    (∀ᵐ q ∂ν, ∀ v : Fin (a+1) → ℝ,
      (b*min 1 (p.val.2*(p.val.2+1))*(a.succPNat : ℝ)^(-((p.val.2+2)*ε)))*(∑ i, v i^2) ≤
        ∑ i,∑ j, v i*H q i j*v j) := by
  intro ν Ht H
  have hdata := included_physical_curvature_internal p θ ε hε d e a ha y z L
    hyL hzL Ky Kz hKy hKz hky hkz N hLN ρ t ht
  refine ⟨hdata.mono (fun _ hx => hx.1), hdata.mono (fun _ hx => hx.2.1), ?_⟩
  filter_upwards [hdata] with q hq
  intro v
  apply le_trans _ (hq.2.2 v)
  have hmin : 0 ≤ min 1 (p.val.2*(p.val.2+1)) := by have hs := p.property.2.1; positivity
  simpa only [Nat.succPNat_coe,Nat.cast_succ,neg_mul] using
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbp hmin)
        (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ a+1) (-((p.val.2+2)*ε))))
      (Finset.sum_nonneg fun i _ => sq_nonneg (v i))

/-- Transfer the almost-everywhere Hessian identification in Lemma 6.4
to positivity and tangent coercivity on the included physical fibre law. -/
theorem fibre_lower_congr_internal {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (n : ℕ+) (H G : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (a : ℝ) (he : H =ᵐ[ν] G) (hG : ∀ᵐ x ∂ν, (G x).PosSemidef)
    (hl : ∀ᵐ x ∂ν, ∀ z : Fin (n : ℕ) → ℝ,
      a*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*G x i j*z j) :
    (∀ᵐ x ∂ν, (H x).PosSemidef) ∧
      ∀ᵐ x ∂ν, ∀ z ∈ zeroSumComponents (Fin (n : ℕ)),
        a*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*H x i j*z j := by
  refine ⟨?_,?_⟩
  · filter_upwards [he,hG] with x hx hp
    rwa [hx]
  · filter_upwards [he,hl] with x hx hp
    intro z _
    rw [hx]
    exact hp z

/-- The comparison input in Lemma 6.4 is vacuous below its natural
size threshold. Convert the threshold to real size before the physical instantiation. -/
theorem comparison_below_threshold_internal (n : ℕ+) (n₀ : ℕ)
    (hn : ¬ n₀ ≤ (n : ℕ)) {P : Prop} : (n₀ : ℝ) ≤ (n : ℝ) → P := by
  intro h
  exact False.elim (hn (by exact_mod_cast h))

/-- In the long-range case of Lemma 6.4, the generic all-size
comparison weight has `min(s,1)=s`. This substitution preserves both sums. -/
theorem long_min_bounds_internal (s : Riesz1.RieszExponent)
    {x y C n loss F : ℝ}
    (h : x ≤ C*n^(loss-min s.val 1/2)*F ∧ y ≤ C*n^loss*F) :
    x ≤ C*n^(loss-s.val/2)*F ∧ y ≤ C*n^loss*F := by
  simpa only [min_eq_left s.property.2.le] using h

/-- Positivity, tangent coercivity and unique solvability for the coarse
physical sizes in Lemma 6.4, on the original included scalar form. -/
theorem included_physical_solvability_internal (p : Parameters) (θ : PhysicalCutoff)
    (ε : ℝ) (hε : 0 ≤ ε) (d e a : ℕ) (ha : 1 ≤ a)
    (y : AffineSimplex.chartDomain d ((d+a : ℕ)+1))
    (z : AffineSimplex.chartDomain e ((e+a : ℕ)+1)) (L : ℝ)
    (hyL : ((d+a : ℕ)+1 : ℝ)-∑ k, y.val k = L)
    (hzL : ((e+a : ℕ)+1 : ℝ)-∑ k, z.val k = L)
    (Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ)
    (hKy : ContDiffOn ℝ ∞ Ky (RetainedSimplex.assemble d a
      (InterpolatingDensities.exteriorPermutation d a) y.val ⁻¹' gapAmbientDomain (d+a).succPNat))
    (hKz : ContDiffOn ℝ ∞ Kz (RetainedSimplex.assemble e a
      (InterpolatingDensities.exteriorPermutation e a) z.val ⁻¹' gapAmbientDomain (e+a).succPNat))
    (hky : ∀ u (hu : RetainedSimplex.assemble d a
      (InterpolatingDensities.exteriorPermutation d a) y.val u ∈ gapAmbientDomain (d+a).succPNat),
      Ky u = physicalAmbientGapEnergy p (d+a).succPNat
        ⟨RetainedSimplex.assemble d a (InterpolatingDensities.exteriorPermutation d a) y.val u,hu⟩)
    (hkz : ∀ u (hu : RetainedSimplex.assemble e a
      (InterpolatingDensities.exteriorPermutation e a) z.val u ∈ gapAmbientDomain (e+a).succPNat),
      Kz u = physicalAmbientGapEnergy p (e+a).succPNat
        ⟨RetainedSimplex.assemble e a (InterpolatingDensities.exteriorPermutation e a) z.val u,hu⟩)
    (N : ℝ) (hLN : L < N) (ρ : Measure (AffineSimplex.massSimplex a L))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (b : ℝ) (_hb : 0 < b) (hbp : b ≤ p.val.1) :
    let ν := ρ.map (InterpolationTransport.inclusion a L N hLN)
    let Ht := fun u : EuclideanSpace ℝ (Fin (a+1)) =>
      (∑ k, (θ.val ((a+1 : ℝ)^(-ε)*u k)+θ.val ((a+1 : ℝ)^(-ε)*(u k)⁻¹)))+(1-t)*Ky u+t*Kz u
    let H : AffineSimplex.chartDomain (a+1) N → Matrix (Fin (a+1)) (Fin (a+1)) ℝ :=
      fun q => hessianMatrix (fun u => p.val.1*Ht u) q.val
    let mass := b*min 1 (p.val.2*(p.val.2+1))*(a.succPNat : ℝ)^(-((p.val.2+2)*ε))
    ∀ (Q : ScalarFormData ν) (_hQ : IsClosedScalarDirichletForm Q),
    (∀ i j, Measurable (fun q => H q i j)) ∧
    (∀ᵐ q ∂ν, (H q).PosSemidef) ∧
    (∀ᵐ q ∂ν, ∀ v ∈ zeroSumComponents (Fin (a+1)),
      mass*(∑ i, v i^2) ≤ ∑ i, ∑ j, v i*H q i j*v j) ∧
    ∀ (i₀ : Fin (a+1)) (χ : Lp ℝ 2 ν), ∃! ψ : Fin (a+1) → Q.1,
      WeightedWeakSolution Q H (zeroSumComponents (Fin (a+1)))
        (fun i => if i=i₀ then χ else 0) ψ := by
  intro ν Ht H mass Q hQ
  obtain ⟨he,hpos,hl⟩ := included_physical_lower_internal p θ ε hε d e a ha y z L hyL hzL
    Ky Kz hKy hKz hky hkz N hLN ρ t ht b _hb hbp
  obtain ⟨hH,hlower⟩ := fibre_lower_congr_internal ν a.succPNat H _ mass he hpos hl
  have hm : ∀ i j, Measurable (fun q => H q i j) := fun i j =>
    (DifferentiatedPoisson.measurable_hessian_entries (V := fun u => p.val.1*Ht u) i j).comp
      measurable_subtype_coe
  have ha0 : 0 < mass := by
    have hs := p.property.2.1
    dsimp only [mass]
    positivity
  exact ⟨hm,hH,hlower,fun i₀ χ => MatrixEnergy.weightedWeakSolution_existsUnique
    Q hQ H _ hH mass ha0 hlower hm _⟩

/-- The native coefficient and physical-form family in Lemma 6.4, with its
original quantifiers and whole-carrier fields retained. -/
def NativePhysicalFamilyInternal (s : Riesz1.RieszExponent) (h : ℕ) (A K κM γ ε : ℝ) (n0 : ℕ)
    (δ βlo βhi : ℝ) (θ : PhysicalCutoff) (C0 c : ℝ) : Prop :=
∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    ∀ (a d e : ℕ) (_ha : 1 ≤ a) (hde : d ≤ e),
    let n := a.succPNat
    let N := ((n : ℕ)+d).succPNat
    ∀ _hN : 4*(n : ℕ) ≤ (N : ℕ), (n : ℝ)^(2/s.val) ≤ (N : ℝ) →
    ∀ (y : AffineSimplex.chartDomain (d+1) ((d+1+a : ℕ)+1))
      (z : AffineSimplex.chartDomain (e+1) ((e+1+a : ℕ)+1)) (L : ℝ),
    ((d+1+a : ℕ)+1 : ℝ)-∑ k, y.val k = L →
    ((e+1+a : ℕ)+1 : ℝ)-∑ k, z.val k = L →
    InterpolantLocalLaws.admissibleExterior (ofLong β s) (d+1) a (Nat.succ_le_succ (Nat.zero_le d)) θ ε A K y →
    InterpolantLocalLaws.admissibleExterior (ofLong β s) (e+1) a (Nat.succ_le_succ (Nat.zero_le e)) θ ε A K z →
    let Dy := RetainedSimplex.assemble (d+1) a (InterpolatingDensities.exteriorPermutation (d+1) a) y.val ⁻¹'
      gapAmbientDomain (d+1+a).succPNat
    let Dz := RetainedSimplex.assemble (e+1) a (InterpolatingDensities.exteriorPermutation (e+1) a) z.val ⁻¹'
      gapAmbientDomain (e+1+a).succPNat
    ∃ Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ,
      ContDiffOn ℝ ∞ Ky Dy ∧ ContDiffOn ℝ ∞ Kz Dz ∧
      (∀ u (hu : u ∈ Dy), Ky u = physicalAmbientGapEnergy (ofLong β s) (d+1+a).succPNat
        ⟨RetainedSimplex.assemble (d+1) a (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u,hu⟩) ∧
      (∀ u (hu : u ∈ Dz), Kz u = physicalAmbientGapEnergy (ofLong β s) (e+1+a).succPNat
        ⟨RetainedSimplex.assemble (e+1) a (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u,hu⟩) ∧
    ∀ t ∈ Icc (0 : ℝ) 1,
    let H := fun u : EuclideanSpace ℝ (Fin (a+1)) =>
      (∑ k, (θ.val ((a+1 : ℝ)^(-ε)*u k)+θ.val ((a+1 : ℝ)^(-ε)*(u k)⁻¹)))+(1-t)*Ky u+t*Kz u
    let m := PhysicalCore.properReferencePeriod s n N
    let k := ⌊(n : ℝ)^(K*ε)⌋₊^h
    ∃ (hm : 2 ≤ (m : ℕ)) (hnm : (n : ℕ) ≤ (m : ℕ))
      (hk : 1 ≤ k) (hkm : k ≤ (m : ℕ)/4),
      (∀ μ : Measure (AffineSimplex.chartDomain n ((n+d : ℕ)+1)),
        PeriodizedMatrixBounds (ν := μ) s n m hm k C0 κM γ ε
          (InterpolationMatrix.matrix β s n d e hde m hm hnm k θ ε (K*ε) t)) ∧
      (∀ x ∈ AffineSimplex.massSimplex a L, ∀ v : EuclideanSpace ℝ (Fin (a+1)),
        C0⁻¹*(n : ℝ)^(-κM*ε)*(∑ i, (v i)^2) ≤ ∑ i,∑ j, v i*hessianMatrix H x i j*v j) ∧
    (n0 ≤ (n : ℕ) →
      (∀ x ∈ AffineSimplex.massSimplex a L, ∀ i j : Fin (a+1),
        |(1-t)*hessianMatrix Ky x i j+t*hessianMatrix Kz x i j|^2+
          |InterpolationMatrix.penaltyHessian n θ ε x i j|^2 ≤
          C0*(n : ℝ)^C0*InterpolantLocalLaws.exceptionalWeight (n := n) s.val (WithLp.ofLp x)) ∧
      let μ : Measure (AffineSimplex.massSimplex a L) := (AffineSimplex.simplexVolume a L).comap Subtype.val
      let w := fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal (Real.exp (-β.val*H u.val))
      ∃ (h0 : (∫⁻ u, w u ∂μ) ≠ 0) (htop : (∫⁻ u, w u ∂μ) ≠ ⊤),
      ∃ hLN : L < ((n+d : ℕ)+1 : ℝ),
      let ρ := AffineFibre.normalizedMeasure μ w h0 htop
      let ν := ρ.map (InterpolationTransport.inclusion a L ((n+d : ℕ)+1) hLN)
      IsProbabilityMeasure ν ∧
      ∀ frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a),
      ∃ Q : ScalarFormData ν, ∃ hQ : IsClosedScalarDirichletForm Q,
      IsConservativeScalarForm Q ∧
      InterpolationCoefficientBounds.IsIntrinsicFibreForm a L ((n+d : ℕ)+1) hLN frame ν Q ∧
      let P : AffineSimplex.chartDomain n ((n+d : ℕ)+1) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ :=
        fun q i j => (1-t)*hessianMatrix Ky q.val i j+t*hessianMatrix Kz q.val i j
      let Y := InterpolationMatrix.multiplicationPart β s n d e hde m hm hnm k θ ε (K*ε) t P
      (∀ i j : Fin (n : ℕ), Integrable
        (fun x : AffineSimplex.chartDomain n ((n+d : ℕ)+1) =>
          β.val*(InterpolationMatrix.penaltyHessian n θ ε x.val i j+P x i j)) ν) ∧
      (∀ i j : Fin (n : ℕ), Integrable (fun x => Y x i j) ν) ∧
      (∀ (φ ψ : BoundedL2Pairings.boundedSubmodule ν) (j i : Fin (n : ℕ)),
        |(∫ x, φ.val x*Y x j i*ψ.val x ∂ν)+
          InterpolationMatrix.schurPointPair ν Q hQ s β m hm k hk hkm n φ.val ψ.val
            (j.castLE hnm) (i.castLE hnm)| ≤
          (C0*(n : ℝ)^(κM*ε))*InteractionDifferential.boundaryWeight s.val n j*InteractionDifferential.boundaryWeight s.val n i*‖φ.val‖*‖ψ.val‖+
            (C0*Real.exp (-c*(n : ℝ)^δ))*
              (eLpNorm (fun x => φ.val x) ∞ ν).toReal*(eLpNorm (fun x => ψ.val x) ∞ ν).toReal) ∧
      (∀ (φ ψ : BoundedL2Pairings.boundedSubmodule ν) (j i l : Fin (n : ℕ)),
        |(∫ x, φ.val x*ψ.val x*(Y x j i-Y x j l) ∂ν)+
          InterpolationMatrix.schurIncrementPair ν Q hQ s β m hm k hk hkm n φ.val ψ.val
            (j.castLE hnm) (i.castLE hnm) (l.castLE hnm)| ≤
          (C0*(n : ℝ)^(κM*ε))*InteractionDifferential.boundaryWeight s.val n j*
            (Nat.dist i.val l.val : ℝ)*
              (min ((min (i.val+1) ((n : ℕ)-i.val) : ℕ) : ℝ)
                ((min (l.val+1) ((n : ℕ)-l.val) : ℕ) : ℝ))^(-1-s.val/2)*‖φ.val‖*‖ψ.val‖+
            (C0*Real.exp (-c*(n : ℝ)^δ))*
              (eLpNorm (fun x => φ.val x) ∞ ν).toReal*(eLpNorm (fun x => ψ.val x) ∞ ν).toReal))

/-- The uniform auxiliary inverse and its five estimates in Lemma 6.4, with its
original quantifiers and whole-carrier fields retained. -/
def AuxiliaryProfileInternal (s : Riesz1.RieszExponent) (h : ℕ+) (κM K γ ε Cstar κaux : ℝ)
    (hCstar : 1 ≤ Cstar) (βlo βhi D : ℝ) : Prop :=
∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    ∀ (n m : ℕ+) (hn : 2 ≤ (n : ℕ)) (hm : 2 ≤ (m : ℕ)),
    ∀ (hnm : 2 * (n : ℕ) ≤ (m : ℕ)),
      (m : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 + 1 / s.val) →
    let kcut := ⌊(n : ℝ) ^ (K*ε)⌋₊ ^ (h : ℕ)
    1 ≤ kcut → 4 * kcut ≤ (m : ℕ) →
    ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν],
    ∀ (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q), IsConservativeScalarForm Q →
    ∀ (M : X → Matrix (Fin (m : ℕ)) (Fin (m : ℕ)) ℝ)
      (hM : PeriodizedMatrixBounds (ν := ν) s n m hm kcut Cstar (κM/K) (γ/K) (K*ε) M),
    ∀ i₀ : Fin (n : ℕ), |(i₀.val : ℝ) + 1 - (n : ℝ) / 2| ≤ (n : ℝ) / 4 →
    ∀ (χ : Lp ℝ 2 ν) (Bχ : ℝ), 0 ≤ Bχ → (∀ᵐ x ∂ν, |χ x| ≤ Bχ) →
    let f : PiLp 2 (fun _ : Fin (n : ℕ) => Lp ℝ 2 ν) :=
      WithLp.toLp 2 (fun i => if i = i₀ then χ else 0)
    let Abar := SchurRestriction.schurForm Q hQ n m (by omega) s hm kcut
      Cstar (κM/K) (γ/K) (K*ε) β.val hCstar β.property M hM
    (∃! v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ,
      ∀ w, Abar v w = inner ℝ f (OperatorSchur.vectorValues Q hQ w)) ∧
    ∀ v : MatrixEnergy.Vector (ι := Fin (n : ℕ)) Q hQ,
      (∀ w, Abar v w = inner ℝ f (OperatorSchur.vectorValues Q hQ w)) →
    let v' := MatrixEnergy.vectorEquiv Q hQ v
    let S := ∑ i, v' i
    (∀ j : Fin (n : ℕ), ‖(v' j).val‖ ≤ D * (n : ℝ) ^ (κaux * (K*ε)) *
      (1 + (Nat.dist j.val i₀.val : ℝ)) ^ (s.val - 2) * ‖χ‖) ∧
    (∑ j, ‖(v' j).val‖) ≤ D * (n : ℝ) ^ (κaux * (K*ε)) * ‖χ‖ ∧
    ‖S.val‖ ≤ D * (n : ℝ) ^ (κaux * (K*ε) - (1 - s.val)) * ‖χ‖ ∧
    Real.sqrt (Q.2 S S) ≤ D * (n : ℝ) ^ (κaux * (K*ε) - (1 - s.val) / 2) * ‖χ‖ ∧
    ∀ i, ∀ᵐ x ∂ν, |(v' i).val x| ≤ D*(n : ℝ)^(κaux*(K*ε))*Bχ

/-- The all-size comparison-to-decay certificate in Lemma 6.4, with its
original quantifiers and whole-carrier fields retained. -/
def AllSizeRatesInternal (s : Riesz1.RieszExponent) (ell ε : ℝ) (n0 : ℕ)
    (a0 D Asq Tsq c δ C : ℝ) : Prop :=
∀ (n : ℕ+) (X : Type) [MeasurableSpace X] (ν : Measure X)
      (Q : ScalarFormData ν) (_hQ : IsClosedScalarDirichletForm Q)
      (M : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ),
      (∀ i j, Measurable (fun x => M x i j)) →
      ∀ _hM : ∀ᵐ x ∂ν, (M x).PosSemidef,
      (∀ᵐ x ∂ν, ∀ z ∈ zeroSumComponents (Fin (n : ℕ)),
        (a0*(n : ℝ)^(-((s.val+2)*ε)))*(∑ i, z i^2) ≤
          ∑ i, ∑ j, z i*M x i j*z j) →
      ∀ (i₀ : Fin (n : ℕ)), |(i₀.val : ℝ)+1-(n : ℝ)/2| ≤ (n : ℝ)/4 →
      ∀ χ : BoundedL2Pairings.boundedSubmodule ν,
      ∀ ψ : Fin (n : ℕ) → Q.1,
      WeightedWeakSolution Q M (zeroSumComponents (Fin (n : ℕ)))
        (fun i => if i = i₀ then χ.val else 0) ψ →
      let B := (eLpNorm (χ.val : X → ℝ) ∞ ν).toReal
      ((n0 : ℝ) ≤ (n : ℝ) → ∃ v : Fin (n : ℕ) → Lp ℝ 2 ν,
        (∀ j, ‖v j‖ ≤ D*(n : ℝ)^((4*ell)*ε)*
          (1+(Nat.dist j.val i₀.val : ℝ))^(if s.val < 1 then s.val-2 else -s.val)*‖χ.val‖) ∧
        (∑ j, ‖v j‖) ≤ D*(n : ℝ)^((4*ell)*ε)*‖χ.val‖ ∧
        ‖WithLp.toLp 2 (fun j => (ψ j).val-v j)‖^2 ≤
          Asq*(n : ℝ)^(2*((4*ell)*ε)-1)*‖χ.val‖^2 +
            Tsq*(n : ℝ)^(2+4*(ell*ε))*Real.exp (-(c/2)*(n : ℝ)^δ)*B^2) →
      (∑ j, InteractionDifferential.boundaryWeight s.val n j*‖(ψ j).val‖) ≤
        C*(n : ℝ)^((max (s.val+2) (4*ell))*ε-min s.val 1/2)*
          (‖χ.val‖+Real.exp (-((c/2)/4)*(n : ℝ)^δ)*B) ∧
      (∑ j, ‖(ψ j).val‖) ≤ C*(n : ℝ)^((max (s.val+2) (4*ell))*ε)*
          (‖χ.val‖+Real.exp (-((c/2)/4)*(n : ℝ)^δ)*B)

/-- The physical-fibre instantiation of Lemma 6.4 from the native
coefficient family, the uniform auxiliary inverse and the all-size comparison.
This distinct internal implication preserves the constants chosen before volume
and uses the full pairing of Lemma 5.17 at the energy comparison. -/
theorem physical_instantiation_internal :
∀ (_hzeta : External.PeriodicZeta),
∀ (_hRig : External.LongRangeRigidityLocallyUniform),
∀ (s : Riesz1.RieszExponent),
∀ (A : ℝ),
∀ (K : ℝ),
∀ (εbase : ℝ),
∀ (κM : ℝ),
∀ (γ : ℝ),
∀ (_hA : 1 < A),
∀ (_hK : 1 < K),
∀ (_hεbase : 0 < εbase),
∀ (_hκM : 0 < κM),
∀ (_hγ : 0 < γ),
∀ (_hKpos : 0 < K),
let h : ℕ+ := paperReferenceCutoffExponent s;
∀ (κaux : ℝ),
∀ (_hκaux : 0 < κaux),
let ell : ℝ := max (κaux * K) (max κM (s.val + 2));
∀ (_hell : 0 < ell),
∀ (_heaux : κaux * K ≤ ell),
∀ (_heM : κM ≤ ell),
∀ (_hes : s.val + 2 ≤ ell),
∀ (ε : ℝ),
∀ (_hε : 0 < ε),
∀ (_hsmall : ε < εbase),
∀ (n0 : ℕ),
∀ (δ : ℝ),
∀ (_hn0 : 2 ≤ n0),
∀ (_hδ : 0 < δ),
∀ (_hthreshold : 128 ≤ (n0 : ℝ) ^ (1 - s.val / 2 - 2 * ε)),
∀ (βlo : ℝ),
∀ (βhi : ℝ),
∀ (_hlo : 0 < βlo),
∀ (_hle : βlo ≤ βhi),
∀ (θ : PhysicalCutoff),
∀ (C0 : ℝ),
∀ (c : ℝ),
∀ (_hC0 : 0 < C0),
∀ (_hc : 0 < c),
∀ (_hfamily : NativePhysicalFamilyInternal s (h : ℕ) A K κM γ ε n0 δ βlo βhi θ C0 c),
let Cstar : ℝ := max C0 1;
∀ (hCstar : 1 ≤ Cstar),
∀ (D : ℝ),
∀ (_hD : 0 < D),
∀ (_haux : AuxiliaryProfileInternal s h κM K γ ε Cstar κaux hCstar βlo βhi D),
let a0 : ℝ := βlo * min 1 (s.val * (s.val + 1));
∀ (_ha0 : 0 < a0),
let G : ℝ := 2*8^(2-s.val)*(2/(1-s.val/2)) +
  8^(1+s.val/2)*(2/s.val) + 4^(s.val/2);
∀ (Ka : ℝ),
∀ (_hKa : 0 ≤ Ka),
∀ (_habsorb : ∀ (x : ℝ), 1 ≤ x → x ^ (ell * ε + 5 / 2) * Real.exp (-c * x ^ δ) ≤ Ka * Real.exp (-(c / 2) * x ^ δ)),
let L0 : ℝ := G * √(2 / (1 - s.val)) * (C0 + C0) * D;
let K0 : ℝ := βhi * (Cstar * (1 + 1 / s.val) * (2 / (1 - s.val))) + (C0 + C0) * (2 / (1 - s.val / 2)) ^ 2;
let Asq : ℝ := 3 * ((2 * L0 / a0) ^ 2 + (1 + K0) * D ^ 2 / a0 + D ^ 2);
let Tsq : ℝ := 9 * (3 * ((C0 + C0) * Ka) * (2 * D + a0⁻¹) * D + (C0 + C0) * Ka * D ^ 2) / a0;
∀ (_hK0 : 0 ≤ K0),
∀ (_hAsq : 0 ≤ Asq),
∀ (_hTsq : 0 ≤ Tsq),
∀ (C : ℝ),
∀ (_hC : 0 < C),
∀ (_hrates : AllSizeRatesInternal s ell ε n0 a0 D Asq Tsq c δ C),
∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    ∀ (a d e : ℕ) (_ha : 1 ≤ a) (_hde : d ≤ e),
    let n := a.succPNat
    let N := ((n : ℕ)+d).succPNat
    ∀ _hN : 4*(n : ℕ) ≤ (N : ℕ), (n : ℝ)^(2/s.val) ≤ (N : ℝ) →
    ∀ (y : AffineSimplex.chartDomain (d+1) ((d+1+a : ℕ)+1))
      (z : AffineSimplex.chartDomain (e+1) ((e+1+a : ℕ)+1)) (L : ℝ),
    ((d+1+a : ℕ)+1 : ℝ)-∑ k, y.val k = L →
    ((e+1+a : ℕ)+1 : ℝ)-∑ k, z.val k = L →
    InterpolantLocalLaws.admissibleExterior (ofLong β s) (d+1) a
      (Nat.succ_le_succ (Nat.zero_le d)) θ ε A K y →
    InterpolantLocalLaws.admissibleExterior (ofLong β s) (e+1) a
      (Nat.succ_le_succ (Nat.zero_le e)) θ ε A K z →
    let Dy := RetainedSimplex.assemble (d+1) a (InterpolatingDensities.exteriorPermutation (d+1) a) y.val ⁻¹'
      gapAmbientDomain (d+1+a).succPNat
    let Dz := RetainedSimplex.assemble (e+1) a (InterpolatingDensities.exteriorPermutation (e+1) a) z.val ⁻¹'
      gapAmbientDomain (e+1+a).succPNat
    ∃ Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ,
      ContDiffOn ℝ ∞ Ky Dy ∧ ContDiffOn ℝ ∞ Kz Dz ∧
      (∀ u (hu : u ∈ Dy), Ky u = physicalAmbientGapEnergy (ofLong β s) (d+1+a).succPNat
        ⟨RetainedSimplex.assemble (d+1) a (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u,hu⟩) ∧
      (∀ u (hu : u ∈ Dz), Kz u = physicalAmbientGapEnergy (ofLong β s) (e+1+a).succPNat
        ⟨RetainedSimplex.assemble (e+1) a (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u,hu⟩) ∧
    ∀ t ∈ Icc (0 : ℝ) 1,
    let Ht := fun u : EuclideanSpace ℝ (Fin (a+1)) =>
      (∑ k, (θ.val ((a+1 : ℝ)^(-ε)*u k)+θ.val ((a+1 : ℝ)^(-ε)*(u k)⁻¹)))+(1-t)*Ky u+t*Kz u
    let μ : Measure (AffineSimplex.massSimplex a L) := (AffineSimplex.simplexVolume a L).comap Subtype.val
    let w := fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal (Real.exp (-β.val*Ht u.val))
    ∃ (h0 : (∫⁻ u, w u ∂μ) ≠ 0) (htop : (∫⁻ u, w u ∂μ) ≠ ⊤),
    ∃ hLN : L < ((n+d : ℕ)+1 : ℝ),
    let ν := (AffineFibre.normalizedMeasure μ w h0 htop).map
      (InterpolationTransport.inclusion a L ((n+d : ℕ)+1) hLN)
    IsProbabilityMeasure ν ∧
    ∀ frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a),
    ∃ Q : ScalarFormData ν, IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
      InterpolationCoefficientBounds.IsIntrinsicFibreForm a L ((n+d : ℕ)+1) hLN frame ν Q ∧
    let H := fun q : AffineSimplex.chartDomain n ((n+d : ℕ)+1) =>
      hessianMatrix (fun u => β.val*Ht u) q.val
    (∀ (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν),
      ∃! ψ : Fin (n : ℕ) → Q.1, WeightedWeakSolution Q H
        (zeroSumComponents (Fin (n : ℕ))) (fun i => if i = i₀ then χ else 0) ψ) ∧
    ∀ (i₀ : Fin (n : ℕ)), |(i₀.val : ℝ)+1-(n : ℝ)/2| ≤ (n : ℝ)/4 →
    ∀ χ : BoundedL2Pairings.boundedSubmodule ν, ∀ ψ : Fin (n : ℕ) → Q.1,
      WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ)))
        (fun i => if i = i₀ then χ.val else 0) ψ →
      (∑ j, InteractionDifferential.boundaryWeight s.val n j*‖(ψ j).val‖) ≤
        C*(n : ℝ)^((max (s.val+2) (4*ell))*ε-s.val/2)*
          (‖χ.val‖+Real.exp (-((c/2)/4)*(n : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ ν).toReal) ∧
      (∑ j, ‖(ψ j).val‖) ≤ C*(n : ℝ)^((max (s.val+2) (4*ell))*ε)*
          (‖χ.val‖+Real.exp (-((c/2)/4)*(n : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ ν).toReal) := by
  intro hzeta hRig s A K εbase κM γ hA hK hεbase hκM hγ hKpos h κaux hκaux ell hell heaux heM hes ε hε hsmall n0 δ hn0 hδ _hthreshold βlo βhi hlo hle θ C0 c hC0 hc hfamily Cstar hCstar D hD haux a0 ha0 G Ka hKa habsorb L0 K0 Asq Tsq hK0 hAsq hTsq C hC hrates β hβ a d e ha hde n N hN hNpower y z L hyL hzL hy hz Dy Dz
  obtain ⟨Ky,Kz,hKy,hKz,hky,hkz,hfamilyNext⟩ :=
    hfamily β hβ a d e ha hde hN hNpower y z L hyL hzL hy hz
  clear hfamily
  rename' hfamilyNext => hfamily
  refine ⟨Ky,Kz,hKy,hKz,hky,hkz,?_⟩
  intro t ht Ht μ w
  obtain ⟨hm,hnm,hk,hkm,hmat,_hcoerc,hlarge⟩ := hfamily t ht
  clear hfamily
  let m := PhysicalCore.properReferencePeriod s n N
  let k := ⌊(n : ℝ)^(K*ε)⌋₊^(h : ℕ)
  change k ≤ (m : ℕ)/4 at hkm
  have hkm4 : 4*k ≤ (m : ℕ) := by omega
  have hn : 2 ≤ (n : ℕ) := by change 2 ≤ a+1; omega
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hnm2 : 2*(n : ℕ) ≤ (m : ℕ) :=
    (PhysicalCore.properReferencePeriod_bounds s n N (by omega)).1
  have hmupper : (m : ℝ) ≤ 2*(n : ℝ)^(1/2+1/s.val) :=
    PhysicalMean.proper_period_upper_internal s n N
  have hCmat (ν : Measure (AffineSimplex.chartDomain n ((n+d : ℕ)+1))) :
      PeriodizedMatrixBounds (ν := ν) s n m hm k Cstar (κM/K) (γ/K) (K*ε)
        (InterpolationMatrix.matrix β s n d e hde m hm hnm k θ ε (K*ε) t) := by
    apply matrix_bounds_rescale_internal s n m hm k Cstar κM γ ε K (ne_of_gt hKpos)
    exact PhysicalCore.Internal.matrix_bounds_mono s n m hm k C0 Cstar κM κM γ γ ε
      hC0 (le_max_left _ _) le_rfl le_rfl hε.le _ (hmat ν)
  have hκloss : κM/K*(K*ε) ≤ ell*ε := by
    have he : κM/K*(K*ε) = κM*ε := by field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_right heM hε.le
  have hauxloss : κaux*(K*ε) ≤ ell*ε := by nlinarith only [heaux,hε]
  have hcoercloss : (s.val+2)*ε ≤ ell*ε := mul_le_mul_of_nonneg_right hes hε.le
  -- The small-size branch constructs the same physical law directly.
  -- the large-size branch retains the native family's form and certificates.
  by_cases hbig : n0 ≤ (n : ℕ)
  · obtain ⟨_hsquare,h0,htop,hLN,hprob,hforms⟩ := hlarge hbig
    refine ⟨h0,htop,hLN,hprob,?_⟩
    intro frame
    obtain ⟨Q,hQ,hcons,hIntrinsic,hHi,hYi,hpoint,hinc⟩ := hforms frame
    clear hforms hlarge
    let ν := (AffineFibre.normalizedMeasure μ w h0 htop).map
      (InterpolationTransport.inclusion a L ((n+d : ℕ)+1) hLN)
    change ScalarFormData ν at Q
    let : IsProbabilityMeasure ν := hprob
    let P : AffineSimplex.chartDomain n ((n+d : ℕ)+1) → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ :=
      fun q i j => (1-t)*hessianMatrix Ky q.val i j+t*hessianMatrix Kz q.val i j
    let H := fun q : AffineSimplex.chartDomain n ((n+d : ℕ)+1) =>
      β.val • (InterpolationMatrix.penaltyHessian n θ ε q.val+P q)
    obtain ⟨hHeq,hH,hlower⟩ := included_physical_lower_internal (ofLong β s) θ ε hε.le
      (d+1) (e+1) a ha y z L hyL hzL Ky Kz hKy hKz hky hkz
      ((n+d : ℕ)+1 : ℝ) hLN (AffineFibre.normalizedMeasure μ w h0 htop) t ht βlo hlo hβ.1
    have hPm : ∀ i j, Measurable (fun q => P q i j) := by
      intro i j
      exact (((DifferentiatedPoisson.measurable_hessian_entries (V := Ky) i j).comp measurable_subtype_coe).const_mul (1-t)).add
        (((DifferentiatedPoisson.measurable_hessian_entries (V := Kz) i j).comp measurable_subtype_coe).const_mul t)
    have hHm : ∀ i j, Measurable (fun q => H q i j) := fun i j =>
      (((InterpolationMatrix.measurable_penaltyHessian n θ ε i j).comp measurable_subtype_coe).add
        (hPm i j)).const_mul β.val
    have hlower0 : ∀ᵐ q ∂ν, ∀ v : Fin (n : ℕ) → ℝ,
        (a0*(n : ℝ)^(-((s.val+2)*ε)))*(∑ i, v i^2) ≤ ∑ i,∑ j, v i*H q i j*v j := hlower
    have hlower' : ∀ᵐ q ∂ν, ∀ v : Fin (n : ℕ) → ℝ,
        (a0*(n : ℝ)^(-(ell*ε)))*(∑ i, v i^2) ≤ ∑ i,∑ j, v i*H q i j*v j := by
      filter_upwards [hlower0] with q hq
      intro v
      apply le_trans _ (hq v)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg hcoercloss)) ha0.le)
        (Finset.sum_nonneg fun i _ => sq_nonneg (v i))
    have hHex : ∀ i₀ χ, ∃! ψ : Fin (n : ℕ) → Q.1,
        WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ)))
          (fun i => if i=i₀ then χ else 0) ψ := by
      intro i₀ χ
      exact MatrixEnergy.weightedWeakSolution_existsUnique Q hQ H _ hH
        (a0*(n : ℝ)^(-((s.val+2)*ε))) (by positivity)
        (hlower.mono fun _ hx v _ => hx v) hHm _
    refine ⟨Q,hQ,hcons,hIntrinsic,?_⟩
    intro Hphys
    have hsol (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν) (ψ : Fin (n : ℕ) → Q.1) :
        WeightedWeakSolution Q Hphys (zeroSumComponents (Fin (n : ℕ)))
          (fun i => if i=i₀ then χ else 0) ψ ↔
        WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ)))
          (fun i => if i=i₀ then χ else 0) ψ := by
      exact MatrixFieldTransport.weak_congr Q hHeq _ _ _
    refine ⟨?_,?_⟩
    · intro i₀ χ
      exact (existsUnique_congr (fun ψ => hsol i₀ χ ψ)).mpr (hHex i₀ χ)
    · intro i₀ hi₀ χ ψ hψ
      have hψH := (hsol i₀ χ.val ψ).mp hψ
      have hh := hrates n _ ν Q hQ H hHm hH (hlower.mono fun _ hx v _ => hx v)
        i₀ hi₀ χ ψ hψH
      clear hrates
      apply long_min_bounds_internal s
      apply hh
      intro _
      have hχ := bounded_ae_essentialNorm_internal χ
      have hcomparison := column_subtraction_comparison_from_uniform_auxiliary_internal β s n d e hde m hm hnm2 k hk hkm
        θ ε (K*ε) t ν Q hQ P hn hcons Cstar (κM/K) (γ/K) hCstar (hCmat ν)
        hPm hH hHi hYi (ell*ε) (κaux*(K*ε)) (κM*ε) a0 D D C0 C0 βhi c δ Ka hKa (habsorb n hn1)
        hauxloss (mul_le_mul_of_nonneg_right heM hε.le)
        (by positivity) ha0 hD.le hD.le hC0.le hC0.le hβ.2 hκloss hlower'
        i₀ hi₀ χ.val _ ENNReal.toReal_nonneg hχ ψ hψH
        (haux β hβ n m hn hm hnm2 hmupper hk hkm4) hpoint hinc
      obtain ⟨v,hv,hs,he⟩ := hcomparison
      refine ⟨v,?_,?_,?_⟩
      · simpa only [s.property.2,↓reduceIte,mul_assoc] using hv
      · simpa only [mul_assoc] using hs
      · simpa only [show 2*((4*ell)*ε)-1 = 8*(ell*ε)-1 by ring] using he
  · clear hlarge hmat hCmat haux
    have hNident : ((d+1+a : ℕ)+1 : ℝ) = ((n+d : ℕ)+1 : ℝ) := by
      have hi : d+1+a = (n : ℕ)+d := by change d+1+a = a+1+d; omega
      rw [hi]
    have hLN : L < ((n+d : ℕ)+1 : ℝ) := by
      rw [← hNident]
      exact InterpolationTransport.compatible_mass_lt a (d+1) (by omega) L y (by linarith)
    obtain ⟨h0,htop,hprob,hforms⟩ := InterpolationCoefficientBounds.physical_form_internal
      (ofLong β s) θ ε (d+1) (e+1) a (by omega) (by omega) y z L hyL hzL
      Ky Kz hky hkz ((n+d : ℕ)+1 : ℝ) hNident hLN t ht
    refine ⟨h0,htop,hLN,hprob,?_⟩
    intro frame
    obtain ⟨Q,hQ,hcons,hIntrinsic⟩ := hforms frame
    let ν := (AffineFibre.normalizedMeasure μ w h0 htop).map
      (InterpolationTransport.inclusion a L ((n+d : ℕ)+1) hLN)
    refine ⟨Q,hQ,hcons,hIntrinsic,?_⟩
    intro H
    obtain ⟨hHm,hH,hlower,hex⟩ := included_physical_solvability_internal (ofLong β s) θ ε hε.le
      (d+1) (e+1) a ha y z L hyL hzL Ky Kz hKy hKz hky hkz
      ((n+d : ℕ)+1 : ℝ) hLN (AffineFibre.normalizedMeasure μ w h0 htop) t ht βlo hlo hβ.1 Q hQ
    refine ⟨hex,?_⟩
    intro i₀ hi₀ χ ψ hψ
    have hh := hrates n _ ν Q hQ H hHm hH hlower i₀ hi₀ χ ψ hψ
      (comparison_below_threshold_internal n n0 hbig)
    exact long_min_bounds_internal s hh

/-- See Lemma 6.4 of the paper: all long-range exponents, both coordinate
conclusions, and all physical sizes. The loss degree precedes epsilon and
temperature. The tail power precedes the compact temperature interval.
The law is the normalized intrinsic Hausdorff law, and the equation is the
tangent weak equation on its intrinsic scalar form.
The lifted auxiliary solution uses the least cutoff degree of Lemma 5.4
as prescribed in the proof of Lemma 6.4. -/
theorem long_range_fixed_length_decay (hzeta : External.PeriodicZeta)
    (hRig : External.LongRangeRigidityLocallyUniform) (s : Riesz1.RieszExponent) :
    ∃ A K ε₀ κ : ℝ, 1 < A ∧ 1 < K ∧ 0 < ε₀ ∧ 0 < κ ∧
    ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    ∃ δ : ℝ, 0 < δ ∧
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∀ θ : PhysicalCutoff,
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ β : InverseTemperature, β.val ∈ Icc βlo βhi →
    ∀ (a d e : ℕ) (_ha : 1 ≤ a) (_hde : d ≤ e),
    let n := a.succPNat
    let N := ((n : ℕ)+d).succPNat
    ∀ _hN : 4*(n : ℕ) ≤ (N : ℕ), (n : ℝ)^(2/s.val) ≤ (N : ℝ) →
    ∀ (y : AffineSimplex.chartDomain (d+1) ((d+1+a : ℕ)+1))
      (z : AffineSimplex.chartDomain (e+1) ((e+1+a : ℕ)+1)) (L : ℝ),
    ((d+1+a : ℕ)+1 : ℝ)-∑ k, y.val k = L →
    ((e+1+a : ℕ)+1 : ℝ)-∑ k, z.val k = L →
    InterpolantLocalLaws.admissibleExterior (ofLong β s) (d+1) a
      (Nat.succ_le_succ (Nat.zero_le d)) θ ε A K y →
    InterpolantLocalLaws.admissibleExterior (ofLong β s) (e+1) a
      (Nat.succ_le_succ (Nat.zero_le e)) θ ε A K z →
    let Dy := RetainedSimplex.assemble (d+1) a (InterpolatingDensities.exteriorPermutation (d+1) a) y.val ⁻¹'
      gapAmbientDomain (d+1+a).succPNat
    let Dz := RetainedSimplex.assemble (e+1) a (InterpolatingDensities.exteriorPermutation (e+1) a) z.val ⁻¹'
      gapAmbientDomain (e+1+a).succPNat
    ∃ Ky Kz : EuclideanSpace ℝ (Fin (a+1)) → ℝ,
      ContDiffOn ℝ ∞ Ky Dy ∧ ContDiffOn ℝ ∞ Kz Dz ∧
      (∀ u (hu : u ∈ Dy), Ky u = physicalAmbientGapEnergy (ofLong β s) (d+1+a).succPNat
        ⟨RetainedSimplex.assemble (d+1) a (InterpolatingDensities.exteriorPermutation (d+1) a) y.val u,hu⟩) ∧
      (∀ u (hu : u ∈ Dz), Kz u = physicalAmbientGapEnergy (ofLong β s) (e+1+a).succPNat
        ⟨RetainedSimplex.assemble (e+1) a (InterpolatingDensities.exteriorPermutation (e+1) a) z.val u,hu⟩) ∧
    ∀ t ∈ Icc (0 : ℝ) 1,
    let Ht := fun u : EuclideanSpace ℝ (Fin (a+1)) =>
      (∑ k, (θ.val ((a+1 : ℝ)^(-ε)*u k)+θ.val ((a+1 : ℝ)^(-ε)*(u k)⁻¹)))+(1-t)*Ky u+t*Kz u
    let μ : Measure (AffineSimplex.massSimplex a L) := (AffineSimplex.simplexVolume a L).comap Subtype.val
    let w := fun u : AffineSimplex.massSimplex a L => ENNReal.ofReal (Real.exp (-β.val*Ht u.val))
    ∃ (h0 : (∫⁻ u, w u ∂μ) ≠ 0) (htop : (∫⁻ u, w u ∂μ) ≠ ⊤),
    ∃ hLN : L < ((n+d : ℕ)+1 : ℝ),
    let ν := (AffineFibre.normalizedMeasure μ w h0 htop).map
      (InterpolationTransport.inclusion a L ((n+d : ℕ)+1) hLN)
    IsProbabilityMeasure ν ∧
    ∀ frame : AffineSimplex.Tangent a ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin a),
    ∃ Q : ScalarFormData ν, IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q ∧
      InterpolationCoefficientBounds.IsIntrinsicFibreForm a L ((n+d : ℕ)+1) hLN frame ν Q ∧
    let H := fun q : AffineSimplex.chartDomain n ((n+d : ℕ)+1) =>
      hessianMatrix (fun u => β.val*Ht u) q.val
    (∀ (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν),
      ∃! ψ : Fin (n : ℕ) → Q.1, WeightedWeakSolution Q H
        (zeroSumComponents (Fin (n : ℕ))) (fun i => if i = i₀ then χ else 0) ψ) ∧
    ∀ (i₀ : Fin (n : ℕ)), |(i₀.val : ℝ)+1-(n : ℝ)/2| ≤ (n : ℝ)/4 →
    ∀ χ : BoundedL2Pairings.boundedSubmodule ν, ∀ ψ : Fin (n : ℕ) → Q.1,
      WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ)))
        (fun i => if i = i₀ then χ.val else 0) ψ →
      (∑ j, InteractionDifferential.boundaryWeight s.val n j*‖(ψ j).val‖) ≤
        C*(n : ℝ)^(κ*ε-s.val/2)*
          (‖χ.val‖+Real.exp (-c*(n : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ ν).toReal) ∧
      (∑ j, ‖(ψ j).val‖) ≤ C*(n : ℝ)^(κ*ε)*
          (‖χ.val‖+Real.exp (-c*(n : ℝ)^δ)*(eLpNorm (χ.val : _ → ℝ) ∞ ν).toReal) := by
  obtain ⟨A,K,εbase,κM,γ,hA,hK,hεbase,hκM,hγ,hfamily⟩ :=
    long_range_native_physical_inputs hzeta hRig s
  have hKpos : 0 < K := by linarith
  let h : ℕ+ := paperReferenceCutoffExponent s
  obtain ⟨κaux,hκaux,haux⟩ := schur_on_scalar_form_internal hzeta s (κM/K) (γ/K) h
    (div_pos hκM hKpos) (div_pos hγ hKpos)
  let ell := max (κaux*K) (max κM (s.val+2))
  have hell : 0 < ell := lt_of_lt_of_le (mul_pos hκaux hKpos) (le_max_left _ _)
  have heaux : κaux*K ≤ ell := le_max_left _ _
  have heM : κM ≤ ell := (le_max_left _ _).trans (le_max_right _ _)
  have hes : s.val+2 ≤ ell := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨A,K,εbase, max (s.val+2) (4*ell),hA,hK,hεbase,by positivity,?_⟩
  intro ε hε hsmall
  obtain ⟨n0,δ,hn0,hδ,_hthreshold,hfamilyNext⟩ := hfamily ε hε hsmall
  clear hfamily
  rename' hfamilyNext => hfamily
  refine ⟨δ,hδ,?_⟩
  intro βlo βhi hlo hle θ
  obtain ⟨C0,c,hC0,hc,hfamilyNext⟩ := hfamily βlo βhi hlo hle θ
  clear hfamily
  rename' hfamilyNext => hfamily
  let Cstar := max C0 1
  have hCstar : 1 ≤ Cstar := le_max_right _ _
  obtain ⟨D,hD,hauxNext⟩ := haux (K*ε) (mul_pos hKpos hε) Cstar hCstar βlo βhi hlo hle
  clear haux
  rename' hauxNext => haux
  let a0 := βlo*min 1 (s.val*(s.val+1))
  have ha0 : 0 < a0 := by have hs := s.property.1; dsimp only [a0]; positivity
  let G := 2*8^(2-s.val)*(2/(1-s.val/2)) + 8^(1+s.val/2)*(2/s.val) + 4^(s.val/2)
  obtain ⟨Ka,hKa,habsorb⟩ := MomentEvent.exists_rpow_mul_exp_neg_le
    (a := ell*ε+5/2) (c := c) (c' := c/2) hδ (by linarith)
  let L0 := (G*Real.sqrt (2/(1-s.val)))*(C0+C0)*D
  let K0 := βhi*(Cstar*(1+1/s.val)*(2/(1-s.val)))+(C0+C0)*(2/(1-s.val/2))^2
  let Asq := 3*((2*L0/a0)^2+(1+K0)*D^2/a0+D^2)
  let Tsq := 9*(3*((C0+C0)*Ka)*(2*D+a0⁻¹)*D+((C0+C0)*Ka)*D^2)/a0
  have hK0 : 0 ≤ K0 := by
    have hs := s.property.1
    have hs1 : 0 < 1-s.val := sub_pos.mpr s.property.2
    have hβhi : 0 < βhi := hlo.trans_le hle
    dsimp only [K0]; positivity
  have hAsq : 0 ≤ Asq := by dsimp only [Asq]; positivity
  have hTsq : 0 ≤ Tsq := by dsimp only [Tsq]; positivity
  obtain ⟨C,hC,hrates⟩ := fixed_length_decay_from_comparison_internal
    s.val s.property.1 (ne_of_lt s.property.2) (s.val+2) (4*ell) ε hε.le n0
    a0 D Asq Tsq (2+4*(ell*ε)) (c/2) δ ha0 hD.le hAsq hTsq (by positivity) hδ
  refine ⟨C,(c/2)/4,hC,by positivity,?_⟩
  exact physical_instantiation_internal hzeta hRig s A K εbase κM γ hA hK hεbase hκM hγ hKpos κaux hκaux hell heaux heM hes ε hε hsmall n0 δ hn0 hδ _hthreshold βlo βhi hlo hle θ C0 c hC0 hc hfamily hCstar D hD haux ha0 Ka hKa habsorb hK0 hAsq hTsq C hC hrates

end Riesz2.FixedLengthDecay
