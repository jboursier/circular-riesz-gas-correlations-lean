/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.DecayShort.PaperInteriorComparison
import all Riesz2.DecayShort.PhysicalComparisonPart4

/-!
# The residual and common-form energy comparison

The central-source residual and the first conclusion of Lemma 4.9.
All fields use the paper event. Constants are locally uniform in temperature.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators

namespace Riesz2.DecayShort
open PhysicalComparison

attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false in
/-- Internal contraction against optimal component decay in Lemma 4.9,
with a prefactor uniform on every positive temperature interval. -/
theorem internal_paper_residual_profile_compact (s βlo βhi : ℝ) (hs : 1 < s)
    (hlo : 0 < βlo) (hle : βlo ≤ βhi) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : Parameters), p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
      ∀ (n : ℕ+) (m : ℕ)
      (U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ),
      (∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) //
        y ∈ gapAmbientDomain ((n : ℕ)+m).succPNat},
        U y.val = p.val.1*physicalAmbientGapEnergy p ((n : ℕ)+m).succPNat y) →
      2 ≤ (n : ℕ) + m + 1 → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 →
      ∀ (θ : PhysicalCutoff) (h : ℝ), 0 < h → ∀ (b : Bool) (D : ℝ), 0 ≤ D →
      ∀ (α : Type*) [MeasurableSpace α]
      (τ : α → AffineSimplex.chartDomain n ((n + m : ℕ) + 1)), Measurable τ →
      ∀ (ν : Measure α) (i₀ : Fin (n : ℕ)),
      (n : ℝ)/4 ≤ (i₀.val : ℝ)+1 → (i₀.val : ℝ)+1 ≤ 3*(n : ℝ)/4 →
      ∀ (V : ℝ), 0 ≤ V → ∀ u : Fin (n : ℕ) → Lp ℝ 2 ν,
      (∀ i, ‖u i‖ ≤ V * (1 + |(i.val : ℝ) - (i₀.val : ℝ)|) ^ (-p.val.2)) →
      ∃ g : Fin (n : ℕ) → Lp ℝ 2 ν,
        (∀ᵐ x ∂ν, ∀ i, g i x = ∑ j,
          (paperFrozenPhysicalMatrix p n m U θ h b D (τ x) -
            paperFrozenInteriorMatrix p n m U θ h b D (τ x)) i j * u j x) ∧
        ‖WithLp.toLp 2 g‖ ≤ C * D * V *
          ((n : ℝ) ^ (-(p.val.2 - 1/2)) +
            (((n : ℕ) + m + 1 : ℕ) : ℝ) ^ (-(1/2 : ℝ))) := by
  classical
  let S := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-s)
  let W := 2 * ∑' k : ℕ, (1 + (k : ℝ)) ^ (-(2 * s - 1))
  let K := 2 * (8 : ℝ) ^ s
  let B := βhi
  let L := (8 : ℝ) ^ (s - 1/2)*S + (8 : ℝ) ^ s*Real.sqrt W
  let J := 1+K+3+B+B*Real.sqrt W
  let Cr := 1 + J*S+B*(1+Real.sqrt W)*L+S*(8 : ℝ)^s
  have hS : 0 ≤ S := mul_nonneg (by norm_num) (tsum_nonneg fun _ => by positivity)
  have hW : 0 ≤ W := mul_nonneg (by norm_num) (tsum_nonneg fun _ => by positivity)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hB : 0 ≤ B := hlo.le.trans hle
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hJ : 0 ≤ J := by dsimp only [J]; positivity
  have hCr : 1 ≤ Cr := by
    have h₁ := mul_nonneg hJ hS
    have h₂ : 0 ≤ B*(1+Real.sqrt W)*L := by positivity
    have h₃ : 0 ≤ S*(8 : ℝ)^s := by positivity
    dsimp only [Cr]
    linarith
  refine ⟨Cr,hCr,?_⟩
  intro p hp hpl hph
  subst s
  have hs : 1 < p.val.2 := hs
  have hbound := paper_frozen_difference_l2_norm p hs
  intro n m U hvU hN hhalf θ h hh b D hD α _ τ hτ ν i₀ hlo hhi V hV u hu
  let N : ℝ := ((n : ℕ)+m+1 : ℕ)
  let a := N ^ (-(1/2 : ℝ))
  let l := (n : ℝ)^(-(p.val.2-1/2))
  let cZ := K*D*(n : ℝ)^(-p.val.2)*Real.sqrt n +
    (3*D/N+B*D*N⁻¹)*Real.sqrt n+B*D*a*Real.sqrt W
  let cW := B*D*(a*Real.sqrt n+Real.sqrt W)
  have hnN : (n : ℝ) ≤ N := by dsimp only [N]; norm_cast; omega
  obtain ⟨hp,hNrate,hNr,hsize⟩ := comparison_size_bounds p.val.2 hs n N hnN
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hl : 0 ≤ l := by dsimp only [l]; positivity
  have hr : 0 ≤ l+a := add_nonneg hl ha
  have hcZ : 0 ≤ cZ := by dsimp only [cZ]; positivity
  have hcW : 0 ≤ cW := by dsimp only [cW]; positivity
  have hzcoeff : cZ ≤ D*J*(l+a) := by
    have hmid := mul_le_mul_of_nonneg_left hNrate (mul_nonneg (by linarith : 0 ≤ 3+B) hD)
    have heq : cZ = K*D*l+(3+B)*D*(Real.sqrt n/N)+B*D*a*Real.sqrt W := by
      dsimp only [cZ,l]
      rw [← hp]
      simp only [div_eq_mul_inv]
      ring
    rw [heq]
    calc
      _ ≤ K*D*l+(3+B)*D*a+B*D*a*Real.sqrt W := by linarith only [hmid]
      _ = D*(K*l+(3+B+B*Real.sqrt W)*a) := by ring
      _ ≤ D*(J*l+J*a) := by
        apply mul_le_mul_of_nonneg_left _ hD
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right (by dsimp only [J]; nlinarith [mul_nonneg hB (Real.sqrt_nonneg W)] : K ≤ J) hl
        · exact mul_le_mul_of_nonneg_right (by dsimp only [J]; linarith : 3+B+B*Real.sqrt W ≤ J) ha
      _ = _ := by ring
  have hwcoeff : cW ≤ B*D*(1+Real.sqrt W) := by
    apply mul_le_mul_of_nonneg_left (add_le_add hNr le_rfl) (mul_nonneg hB hD)
  have hc := internal_profile_contractions p.val.2 hs n.pos i₀ hlo hhi V hV
    (fun i => ‖u i‖) hu
  have he := internal_boundary_contraction n.pos p.val.2 (by linarith) i₀ hlo hhi V hV
    (fun i => ‖u i‖) (fun i => norm_nonneg _) hu
  change (∑ i, ‖u i‖) ≤ V*S ∧
    (∑ i, ConditionalScores.weight p.val.2 i*‖u i‖) ≤ V*(L*l) at hc
  change _ ≤ V*(8 : ℝ)^p.val.2*l at he
  obtain ⟨g,hg,hgn⟩ := hbound n m hN hhalf U hvU θ h hh b D hD α τ hτ ν u
  have hgn0 : ‖WithLp.toLp 2 g‖ ≤ cZ*(∑ i, ‖u i‖) +
    cW*(∑ i, ConditionalScores.weight p.val.2 i*‖u i‖) + D*S*Real.sqrt (∑ i, if
      (ConditionalScores.boundaryDistance i : ℝ) < (n : ℝ) / 8 then ‖u i‖ ^ 2 else 0) := by
    apply hgn.trans
    dsimp only [cZ,cW,B,K,W,N,a]
    have hsw : 0 ≤ ∑ i, ConditionalScores.weight p.val.2 i * ‖u i‖ :=
      Finset.sum_nonneg fun i _ => mul_nonneg (ConditionalScores.weight_pos p.val.2 i).le (norm_nonneg _)
    gcongr
  refine ⟨g,hg,hgn0.trans ?_⟩
  calc
    _ ≤ cZ*(V*S)+cW*(V*(L*l))+D*S*(V*(8 : ℝ)^p.val.2*l) := by
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hc.1 hcZ)
        (mul_le_mul_of_nonneg_left hc.2 hcW))
        (mul_le_mul_of_nonneg_left he (mul_nonneg hD hS))
    _ ≤ (D*J*(l+a))*(V*S)+(B*D*(1+Real.sqrt W))*(V*(L*(l+a)))+
        D*S*(V*(8 : ℝ)^p.val.2*(l+a)) := by
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_right hzcoeff (mul_nonneg hV hS)
        · exact mul_le_mul hwcoeff
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right ha) hL) hV)
            (by positivity) (by positivity)
      · exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right ha) (by positivity))
          (mul_nonneg hD hS)
    _ = (J*S+B*(1+Real.sqrt W)*L+S*(8 : ℝ)^p.val.2)*D*V*(l+a) := by ring
    _ ≤ Cr*D*V*(l+a) := by
      apply mul_le_mul_of_nonneg_right _ hr
      apply mul_le_mul_of_nonneg_right _ hV
      apply mul_le_mul_of_nonneg_right _ hD
      dsimp only [Cr]
      linarith

set_option backward.isDefEq.respectTransparency false in
/-- The optimal core-solution estimate used first in Lemma 4.9,
for the matrix `M_0` of equation (4.13). -/
theorem paper_auxiliary_decay_compact (s : ℝ) (hs : 1 < s)
    (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ (θ : PhysicalCutoff) (h : ℝ), 0 < h →
      ∀ A : ℝ, 1 ≤ A → ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : Parameters), p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (n : ℕ+) (m : ℕ)
      (U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ),
      (∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) //
        y ∈ gapAmbientDomain ((n : ℕ)+m).succPNat},
        U y.val = p.val.1*physicalAmbientGapEnergy p ((n : ℕ)+m).succPNat y) →
        2 ≤ (n : ℕ) + m + 1 → 2 * (n : ℕ) ≤ (n : ℕ) + m + 1 → ∀ (b : Bool)
        (α : Type*) [MeasurableSpace α]
        (τ : α → AffineSimplex.chartDomain n ((n + m : ℕ) + 1)), Measurable τ →
        ∀ (ν : Measure α) [IsProbabilityMeasure ν] (Q : ScalarFormData ν),
        IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
        ∀ (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν),
        let M := fun x => paperFrozenInteriorMatrix p n m U θ h b (A * (n : ℝ) ^ (κ * h)) (τ x)
        (∃! u : Fin (n : ℕ) → Q.1, WeightedWeakSolution Q (fun x => p.val.1 • M x) ⊤
          (fun i => if i = i₀ then χ else 0) u) ∧
        (∀ u : Fin (n : ℕ) → Q.1, WeightedWeakSolution Q (fun x => p.val.1 • M x) ⊤
          (fun i => if i = i₀ then χ else 0) u → ∀ j : Fin (n : ℕ),
            ‖(u j).val‖ ≤ C * (n : ℝ) ^ (r * h) *
              (1 + |(j.val : ℝ) - (i₀.val : ℝ)|) ^ (-p.val.2) * ‖χ‖) := by
  classical
  obtain ⟨q,hq,hmat⟩ := paper_uniform_matrix_bounds s hs κ hκ
  obtain ⟨r,hr,hdecay⟩ := PhysicalDecay.optimal_decay_compact s hs
  refine ⟨q * r,mul_nonneg hq hr,?_⟩
  intro θ h hh A hA βlo βhi hlo hle
  obtain ⟨Cd,hCd,hdecay⟩ := hdecay βlo βhi hlo hle
  obtain ⟨Cm,hCm,hmat⟩ := hmat θ h hh A hA
  have hCm0 : 0 < Cm := by linarith
  refine ⟨Cd * Cm ^ r, one_le_mul_of_one_le_of_one_le hCd (Real.one_le_rpow hCm hr), ?_⟩
  intro p hp hpl hph
  subst s
  have hs : 1 < p.val.2 := hs
  have hmat := hmat p rfl
  have hdecay := hdecay p.val.1 ⟨hpl,hph⟩
  intro n m U hvU hN hhalf b α _ τ hτ ν _ Q hQ hcons i₀ χ M
  let B := Cm * (n : ℝ) ^ (q * h)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le hCm
    (Real.one_le_rpow hn1 (mul_nonneg hq hh.le))
  let g : ComponentGeometry (Fin (n : ℕ)) := Sum.inl
    ⟨fun i => (i.val : ℤ), fun i j hij => Fin.ext (Int.ofNat_inj.mp hij)⟩
  have hM := (hmat n m U hvU hN hhalf b).1 (ν.map τ)
  have hm (i j) : Measurable (fun x => M x i j) := (hM.1 i j).comp hτ
  have hb : ∀ᵐ x ∂ν,
      (∀ i j, M x i j = M x j i) ∧
      (∀ z : Fin (n : ℕ) → ℝ, B⁻¹ * (∑ i, z i ^ 2) ≤ ∑ i, ∑ j, z i * M x i j * z j) ∧
      (∀ i j, |M x i j| ≤ B * (1 + componentDistance g i j) ^ (-p.val.2)) :=
    ae_of_ae_map hτ.aemeasurable hM.2
  have he := hdecay α (Fin (n : ℕ)) ν Q hQ hcons g B hB M hm hb i₀ χ
  have hfactor : Cd * B ^ r = (Cd * Cm ^ r) * (n : ℝ) ^ ((q * r) * h) := by
    dsimp only [B]
    rw [Real.mul_rpow hCm0.le (by positivity), ← Real.rpow_mul hn0.le,
      show (q * h) * r = (q * r) * h by ring]
    ring
  have hd (i j : Fin (n : ℕ)) : componentDistance g i j = |(i.val : ℝ) - (j.val : ℝ)| := by
    change |((i.val : ℤ) : ℝ) - ((j.val : ℤ) : ℝ)| = _
    rw [Int.cast_natCast, Int.cast_natCast]
  simpa only [hfactor, hd] using he

set_option backward.isDefEq.respectTransparency false in
/-- The actual matrix-action residual in Lemma 4.9.
Its rate is proved on every measurable fiber with no probability estimate. -/
theorem paper_auxiliary_residual_compact (s : ℝ) (hs : 1 < s)
    (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ (θ : PhysicalCutoff) (h : ℝ), 0 < h →
      ∀ A : ℝ, 1 ≤ A → ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : Parameters), p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (n : ℕ+) (m : ℕ)
      (U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ),
      (∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) //
        y ∈ gapAmbientDomain ((n : ℕ)+m).succPNat},
        U y.val = p.val.1*physicalAmbientGapEnergy p ((n : ℕ)+m).succPNat y) →
        2 ≤ (n : ℕ)+m+1 → 2*(n : ℕ) ≤ (n : ℕ)+m+1 → ∀ (b : Bool)
        (α : Type*) [MeasurableSpace α]
        (τ : α → AffineSimplex.chartDomain n ((n+m : ℕ)+1)), Measurable τ →
        ∀ (ν : Measure α) [IsProbabilityMeasure ν] (Q : ScalarFormData ν),
        IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
        ∀ (i₀ : Fin (n : ℕ)), (n : ℝ)/4 ≤ (i₀.val : ℝ)+1 →
          (i₀.val : ℝ)+1 ≤ 3*(n : ℝ)/4 → ∀ (χ : Lp ℝ 2 ν)
        (v : Fin (n : ℕ) → Q.1),
        WeightedWeakSolution Q (fun x => p.val.1 • paperFrozenInteriorMatrix p n m U θ h b
          (A*(n : ℝ)^(κ*h)) (τ x)) ⊤ (fun i => if i=i₀ then χ else 0) v →
        ∃ g : Fin (n : ℕ) → Lp ℝ 2 ν,
          (∀ᵐ x ∂ν, ∀ i, g i x = ∑ j,
            (paperFrozenPhysicalMatrix p n m U θ h b (A*(n : ℝ)^(κ*h)) (τ x) -
             paperFrozenInteriorMatrix p n m U θ h b (A*(n : ℝ)^(κ*h)) (τ x)) i j * (v j).val x) ∧
          ‖WithLp.toLp 2 g‖ ≤ C*(n : ℝ)^(r*h)*
            ((n : ℝ)^(-(p.val.2-1/2)) +
              (((n : ℕ)+m+1 : ℕ) : ℝ)^(-(1/2 : ℝ)))*‖χ‖ := by
  classical
  obtain ⟨r,hr,hdec⟩ := paper_auxiliary_decay_compact s hs κ hκ
  refine ⟨κ+r,add_nonneg hκ hr,?_⟩
  intro θ h hh A hA βlo βhi hlo hle
  obtain ⟨Cd,hCd,hres⟩ := internal_paper_residual_profile_compact s βlo βhi hs hlo hle
  obtain ⟨Cv,hCv,hdec⟩ := hdec θ h hh A hA βlo βhi hlo hle
  refine ⟨Cd*A*Cv,one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hCd hA) hCv,?_⟩
  intro p hp hpl hph
  subst s
  have hres := hres p rfl hpl hph
  have hdec := hdec p rfl hpl hph
  intro n m U hvU hN hhalf b α _ τ hτ ν _ Q hQ hcons i₀ hlo hhi χ v hv
  let V := Cv*(n : ℝ)^(r*h)*‖χ‖
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hd := (hdec n m U hvU hN hhalf b α τ hτ ν Q hQ hcons i₀ χ).2 v hv
  have hp (i) : ‖(v i).val‖ ≤ V*(1+|(i.val : ℝ)-(i₀.val : ℝ)|)^(-p.val.2) :=
    (hd i).trans_eq (by dsimp only [V]; ring)
  obtain ⟨g,hg,hgn⟩ := hres n m U hvU hN hhalf θ h hh b (A*(n : ℝ)^(κ*h))
    (by positivity) α τ hτ ν i₀ hlo hhi V hV (fun i => (v i).val) hp
  refine ⟨g,hg,hgn.trans_eq ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have he : (n : ℝ)^(κ*h)*(n : ℝ)^(r*h) = (n : ℝ)^((κ+r)*h) := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  dsimp only [V]
  calc
    _ = Cd*A*Cv*((n : ℝ)^(κ*h)*(n : ℝ)^(r*h))*
        ((n : ℝ)^(-(p.val.2-1/2))+(((n : ℕ)+m+1 : ℕ) : ℝ)^(-(1/2 : ℝ)))*‖χ‖ := by ring
    _ = _ := by rw [he]

set_option backward.isDefEq.respectTransparency false in
/-- The first conclusion, equation (4.14), of
Lemma 4.9, with degree chosen before the tilt and temperatures. -/
theorem paper_physical_comparison_compact (s : ℝ) (hs : 1 < s)
    (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ (θ : PhysicalCutoff) (h : ℝ), 0 < h →
      ∀ A : ℝ, 1 ≤ A → ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : Parameters), p.val.2 = s →
      βlo ≤ p.val.1 → p.val.1 ≤ βhi → ∀ (n : ℕ+) (m : ℕ)
      (U : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) → ℝ),
      (∀ y : {y : EuclideanSpace ℝ (Fin ((n : ℕ)+m+1)) //
        y ∈ gapAmbientDomain ((n : ℕ)+m).succPNat},
        U y.val = p.val.1*physicalAmbientGapEnergy p ((n : ℕ)+m).succPNat y) →
        2 ≤ (n : ℕ)+m+1 → 2*(n : ℕ) ≤ (n : ℕ)+m+1 → ∀ (b : Bool)
        (α : Type*) [MeasurableSpace α]
        (τ : α → AffineSimplex.chartDomain n ((n+m : ℕ)+1)), Measurable τ →
        ∀ (ν : Measure α) [IsProbabilityMeasure ν] (Q : ScalarFormData ν),
        IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
        ∀ (i₀ : Fin (n : ℕ)), (n : ℝ)/4 ≤ (i₀.val : ℝ)+1 →
          (i₀.val : ℝ)+1 ≤ 3*(n : ℝ)/4 → ∀ (χ : Lp ℝ 2 ν)
        (u v : Fin (n : ℕ) → Q.1),
        WeightedWeakSolution Q (fun x => p.val.1 • paperFrozenPhysicalMatrix p n m U θ h b
          (A*(n : ℝ)^(κ*h)) (τ x)) ⊤ (fun i => if i=i₀ then χ else 0) u →
        WeightedWeakSolution Q (fun x => p.val.1 • paperFrozenInteriorMatrix p n m U θ h b
          (A*(n : ℝ)^(κ*h)) (τ x)) ⊤ (fun i => if i=i₀ then χ else 0) v →
        ‖WithLp.toLp 2 (fun i => (u i-v i).val)‖ +
          Real.sqrt (∑ i, Q.2 (u i-v i) (u i-v i)) ≤
          C*(n : ℝ)^(r*h)*((n : ℝ)^(-(p.val.2-1/2)) +
            (((n : ℕ)+m+1 : ℕ) : ℝ)^(-(1/2 : ℝ)))*‖χ‖ := by
  classical
  obtain ⟨q,hq,hmat⟩ := paper_uniform_matrix_bounds s hs κ hκ
  obtain ⟨r,hr,hres⟩ := paper_auxiliary_residual_compact s hs κ hκ
  refine ⟨q+r,add_nonneg hq hr,?_⟩
  intro θ h hh A hA βlo βhi hlo hle
  obtain ⟨Cm,hCm,hmat⟩ := hmat θ h hh A hA
  obtain ⟨Cr,hCr,hres⟩ := hres θ h hh A hA βlo βhi hlo hle
  let C := 1+2*(1+βlo⁻¹)*Cm*βhi*Cr
  have hhi : 0 < βhi := hlo.trans_le hle
  have hC : 1 ≤ C := by
    dsimp only [C]
    have ht : 0 ≤ 2*(1+βlo⁻¹)*Cm*βhi*Cr := by positivity
    linarith
  refine ⟨C,hC,?_⟩
  intro p hp hpl hph
  subst s
  have hs : 1 < p.val.2 := hs
  have hβ := p.property.1
  have hmat := hmat p rfl
  have hres := hres p rfl hpl hph
  have hβinv : p.val.1⁻¹ ≤ βlo⁻¹ := (inv_le_inv₀ hβ hlo).mpr hpl
  intro n m U hvU hN hhalf b α _ τ hτ ν _ Q hQ hcons i₀ hlo hhi χ u v hu hv
  let D := A*(n : ℝ)^(κ*h)
  let B := Cm*(n : ℝ)^(q*h)
  let M := fun x => paperFrozenInteriorMatrix p n m U θ h b D (τ x)
  let H := fun x => paperFrozenPhysicalMatrix p n m U θ h b D (τ x)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast n.pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hB : 1 ≤ B := one_le_mul_of_one_le_of_one_le hCm
    (Real.one_le_rpow hn1 (mul_nonneg hq hh.le))
  have hB0 : 0 < B := by linarith
  obtain ⟨hmH,hmM,hsH,hsM⟩ := paperFrozenMatrices_measurable_symmetric p hs n m U θ h hh b D
  have hHm (i j) : Measurable (fun x => H x i j) := (hmH i j).comp hτ
  have hMm (i j) : Measurable (fun x => M x i j) := (hmM i j).comp hτ
  have hmat' := hmat n m U hvU hN hhalf b
  have hHbounds (x) (z : Fin (n : ℕ) → ℝ) :
      B⁻¹*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*H x i j*z j ∧
      (∑ i, ∑ j, z i*H x i j*z j) ≤ B*(∑ i, z i^2) := hmat'.2.1 (τ x) z
  have hMbounds := ae_of_ae_map hτ.aemeasurable (hmat'.1 (ν.map τ)).2
  have hHl : ∀ᵐ x ∂ν, ∀ z : Fin (n : ℕ) → ℝ,
      B⁻¹*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*H x i j*z j :=
    ae_of_all _ fun x z => (hHbounds x z).1
  have hHnonneg (x) (z : Fin (n : ℕ) → ℝ) : 0 ≤ ∑ i, ∑ j, z i*H x i j*z j :=
    (mul_nonneg (inv_nonneg.mpr hB0.le) (Finset.sum_nonneg fun _ _ => sq_nonneg _)).trans
      (hHbounds x z).1
  have hHb : ∃ b : ℝ, ∀ᵐ x ∂ν, ∀ i j, |H x i j| ≤ b :=
    ⟨B,ae_of_all _ fun x i j => internal_entry_bound (H x) B (hsH (τ x))
      (hHnonneg x) (fun z => (hHbounds x z).2) i j⟩
  have hMb : ∃ b : ℝ, ∀ᵐ x ∂ν, ∀ i j, |M x i j| ≤ b := by
    refine ⟨B,?_⟩
    filter_upwards [hMbounds] with x hx i j
    apply (hx.2.2 i j).trans
    apply mul_le_of_le_one_right hB0.le
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · exact le_add_of_nonneg_right (ComponentGeometryBounds.nonneg _ _ _)
    · linarith
  have hHp := AbstractEnergy.scaled_posSemidef (ρ := ν) p.val.1 B⁻¹ hβ.le
    (inv_nonneg.mpr hB0.le) H (ae_of_all _ fun x => ⟨hsH (τ x),fun z => (hHbounds x z).1⟩)
  have hMp := AbstractEnergy.scaled_posSemidef (ρ := ν) p.val.1 B⁻¹ hβ.le
    (inv_nonneg.mpr hB0.le) M (hMbounds.mono fun _ hx => ⟨hx.1,hx.2.1⟩)
  have hHsb : ∃ b : ℝ, ∀ᵐ x ∂ν, ∀ i j, |(p.val.1 • H x) i j| ≤ b := by
    obtain ⟨b,hb⟩ := hHb
    refine ⟨p.val.1*b,hb.mono fun x hx i j => ?_⟩
    simpa only [Matrix.smul_apply,smul_eq_mul,abs_mul,abs_of_pos hβ] using
      mul_le_mul_of_nonneg_left (hx i j) hβ.le
  have hMsb : ∃ b : ℝ, ∀ᵐ x ∂ν, ∀ i j, |(p.val.1 • M x) i j| ≤ b := by
    obtain ⟨b,hb⟩ := hMb
    refine ⟨p.val.1*b,hb.mono fun x hx i j => ?_⟩
    simpa only [Matrix.smul_apply,smul_eq_mul,abs_mul,abs_of_pos hβ] using
      mul_le_mul_of_nonneg_left (hx i j) hβ.le
  have hHa : ∀ᵐ x ∂ν, ∀ z : Fin (n : ℕ) → ℝ,
      (p.val.1*B⁻¹)*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*(p.val.1 • H x) i j*z j := by
    filter_upwards [hHl] with x hx z
    simpa only [Matrix.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc,mul_left_comm] using
      mul_le_mul_of_nonneg_left (hx z) hβ.le
  obtain ⟨g,hg,hgn⟩ := hres n m U hvU hN hhalf b α τ hτ ν Q hQ hcons i₀ hlo hhi χ v hv
  let G := fun i => p.val.1 • g i
  have hG : ∀ᵐ x ∂ν, ∀ i, G i x = ∑ j,
      ((p.val.1 • H x) i j-(p.val.1 • M x) i j)*(v j).val x := by
    filter_upwards [hg,ae_all_iff.mpr fun i => Lp.coeFn_smul p.val.1 (g i)] with x hx hsc i
    rw [hsc i]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [hx i]
    simp only [Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul,Finset.mul_sum,sub_mul]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [H,M,D]
    ring
  have hGn : ‖WithLp.toLp 2 G‖ = p.val.1*‖WithLp.toLp 2 g‖ := by
    change ‖p.val.1 • WithLp.toLp 2 g‖ = _
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hβ]
  have he := internal_common_form_comparison Q hQ (fun x => p.val.1 • H x)
    (fun x => p.val.1 • M x) (AbstractEnergy.scaled_measurable _ H hHm)
    (AbstractEnergy.scaled_measurable _ M hMm) hHsb hMsb hHp hMp
    (p.val.1*B⁻¹) (mul_pos hβ (inv_pos.mpr hB0)) hHa
    (fun i => if i=i₀ then χ else 0) u v hu hv G hG
  have hi : (min 1 (p.val.1*B⁻¹))⁻¹ ≤ (1+p.val.1⁻¹)*B := by
    by_cases ht : 1 ≤ p.val.1*B⁻¹
    · rw [min_eq_left ht,inv_one]
      have hp : 0 ≤ p.val.1⁻¹*B := mul_nonneg (inv_nonneg.mpr hβ.le) hB0.le
      nlinarith
    · rw [min_eq_right (le_of_not_ge ht),mul_inv_rev,inv_inv]
      nlinarith
  rw [hGn] at he
  apply he.trans
  calc
    _ ≤ 2*((1+p.val.1⁻¹)*B)*(p.val.1*
        (Cr*(n : ℝ)^(r*h)*((n : ℝ)^(-(p.val.2-1/2))+
          (((n : ℕ)+m+1 : ℕ) : ℝ)^(-(1/2 : ℝ)))*‖χ‖)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hi (by norm_num)
      · exact mul_le_mul_of_nonneg_left hgn hβ.le
      · positivity
      · positivity
    _ = (2*(1+p.val.1⁻¹)*Cm*p.val.1*Cr)*(n : ℝ)^((q+r)*h)*
        ((n : ℝ)^(-(p.val.2-1/2))+(((n : ℕ)+m+1 : ℕ) : ℝ)^(-(1/2 : ℝ)))*‖χ‖ := by
      dsimp only [B]
      rw [show (n : ℝ)^((q+r)*h)=(n : ℝ)^(q*h)*(n : ℝ)^(r*h) by
        rw [← Real.rpow_add hn0]; congr 1; ring]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg χ)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply (show 2*(1+p.val.1⁻¹)*Cm*p.val.1*Cr ≤
        2*(1+βlo⁻¹)*Cm*βhi*Cr by gcongr).trans
      dsimp only [C]
      linarith

end Riesz2.DecayShort
