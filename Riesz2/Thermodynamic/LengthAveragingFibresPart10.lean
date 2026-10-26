/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz2.Thermodynamic.LengthAveragingFibresPart9
public import Riesz2.Thermodynamic.LengthAveragingFibresPart6
import all Riesz2.DecayShort.PhysicalComparisonPart4

/-!
# Short conditional comparisons on retained length fibres

Supporting results for the proof of Lemma 6.5. The physical penalty exponent and the
fine-event exponent remain independent. All three solutions use one scalar form on the
retained marginal law. Exceptional powers are retained until the envelope exponent is
chosen.
-/

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Classical ContDiff

set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false

attribute [local instance] Classical.propDecidable

namespace Riesz2.LengthAveragingFibres

open DecayShort DecayShort.PhysicalComparison

/-- See the proof of Lemma 6.5 in the paper: the short volume-rate comparison
transfers both value sums and the mean gradient on the common scalar form. -/
theorem short_pair_rate_internal {X : Type*} [MeasurableSpace X] {ν : Measure X}
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (s : ℝ) (hs : 1 < s) (n : ℕ+) (m : ℕ) (i₀ : Fin (n : ℕ))
    (χ : Lp ℝ 2 ν) (u v : Fin (n : ℕ) → Q.1)
    (rv rc η Cv Cc : ℝ) (_hrv : 0 ≤ rv) (hrc : 0 ≤ rc) (hη : 0 < η)
    (hCv : 1 ≤ Cv) (hCc : 1 ≤ Cc)
    (hvp : ∀ j, ‖(v j).val‖ ≤ Cv*(n : ℝ)^(rv*η)*
      (1+|(j.val : ℝ)-(i₀.val : ℝ)|)^(-s)*‖χ‖)
    (hvs : (∑ j,‖(v j).val‖)+Real.sqrt (Q.2 (∑ j,v j) (∑ j,v j)) ≤
      Cv*(n : ℝ)^(rv*η)*‖χ‖)
    (hc : ‖WithLp.toLp 2 (fun j => (u j-v j).val)‖+
      Real.sqrt (∑ j,Q.2 (u j-v j) (u j-v j)) ≤
      Cc*(n : ℝ)^(rc*η)*(Cv*(n : ℝ)^(rv*η)*‖χ‖)*
        ((n : ℝ)^(-(s-1/2))+(((n : ℕ)+m+1 : ℕ) : ℝ)^(-(1/2 : ℝ)))) :
    let r := 1+rv+rc
    let C := 1+Cv+6*Cc*Cv
    (∀ j, ‖(v j).val‖ ≤ C*(n : ℝ)^(r*η)*
      (1+|(j.val : ℝ)-(i₀.val : ℝ)|)^(-s)*‖χ‖) ∧
    (∑ j, ‖(v j).val‖) ≤ C*(n : ℝ)^(r*η)*‖χ‖ ∧
    ‖(∑ j,u j : Q.1).val‖+Real.sqrt (Q.2 (∑ j,u j) (∑ j,u j)) ≤ C*(n : ℝ)^(r*η)*‖χ‖ ∧
    ‖WithLp.toLp 2 (fun j => (u j-v j).val)‖+
      Real.sqrt (∑ j,Q.2 (u j-v j) (u j-v j)) ≤ C*(n : ℝ)^(r*η-1/2)*‖χ‖ := by
  intro r C
  have hCvC : Cv ≤ C := by dsimp only [C]; nlinarith
  have hDcC : 2*Cc*Cv ≤ C := by dsimp only [C]; nlinarith
  have hDmC : Cv+4*Cc*Cv ≤ C := by dsimp only [C]; nlinarith
  have hn : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  let V := Cv*(n : ℝ)^(rv*η)*‖χ‖
  let d := ‖WithLp.toLp 2 (fun j => (u j-v j).val)‖+
    Real.sqrt (∑ j,Q.2 (u j-v j) (u j-v j))
  have hsize := (comparison_size_bounds s hs n (((n : ℕ)+m+1 : ℕ) : ℝ)
    (by exact_mod_cast (show (n : ℕ) ≤ (n : ℕ)+m+1 by omega))).2.2.2
  have hrate : (n : ℝ)^(-(s-1/2))+(((n : ℕ)+m+1 : ℕ) : ℝ)^(-(1/2 : ℝ)) ≤
      2*(n : ℝ)^(-(1/2 : ℝ)) := by
    have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn
    apply (mul_le_mul_iff_right₀ hsqrt).mp
    convert hsize using 1
    rw [Real.sqrt_eq_rpow,show (n : ℝ)^(1/2 : ℝ)*(2*(n : ℝ)^(-(1/2 : ℝ))) =
      2*((n : ℝ)^(1/2 : ℝ)*(n : ℝ)^(-(1/2 : ℝ))) by ring,
      ← Real.rpow_add hn,add_neg_cancel,Real.rpow_zero,mul_one]
  have hd : d ≤ (2*Cc*Cv)*(n : ℝ)^(r*η-1/2)*‖χ‖ := by
    calc
      _ ≤ Cc*(n : ℝ)^(rc*η)*V*(2*(n : ℝ)^(-(1/2 : ℝ))) :=
        hc.trans (mul_le_mul_of_nonneg_left hrate (by positivity))
      _ = (2*Cc*Cv)*(n : ℝ)^((rc+rv)*η-1/2)*‖χ‖ := by
        dsimp only [V]
        rw [show (n : ℝ)^((rc+rv)*η-1/2) =
          (n : ℝ)^(rc*η)*(n : ℝ)^(rv*η)*(n : ℝ)^(-(1/2 : ℝ)) by
          rw [← Real.rpow_add hn,← Real.rpow_add hn]; congr 1; ring]
        ring
      _ ≤ _ := by
        gcongr
        dsimp only [r]
        nlinarith only [hη.le]
  have hpow : (n : ℝ)^(rv*η) ≤ (n : ℝ)^(r*η) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by dsimp only [r]; nlinarith only [hη.le,hrc])
  have hsqrtpow : Real.sqrt (n : ℝ)*(n : ℝ)^(r*η-1/2) = (n : ℝ)^(r*η) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_add hn]
    congr 1
    ring
  have hfull := short_auxiliary_mean_transfer_internal Q hQ n u v
  have hfull' : (∑ j,‖(u j).val‖)+Real.sqrt (Q.2 (∑ j,u j) (∑ j,u j)) ≤
      C*(n : ℝ)^(r*η)*‖χ‖ := by
    calc
      _ ≤ Cv*(n : ℝ)^(rv*η)*‖χ‖+2*Real.sqrt (n : ℝ)*d :=
        hfull.trans (add_le_add hvs le_rfl)
      _ ≤ Cv*(n : ℝ)^(r*η)*‖χ‖+
          2*Real.sqrt (n : ℝ)*((2*Cc*Cv)*(n : ℝ)^(r*η-1/2)*‖χ‖) := by gcongr
      _ = (Cv+4*Cc*Cv)*(n : ℝ)^(r*η)*‖χ‖ := by
        calc
          _ = Cv*(n : ℝ)^(r*η)*‖χ‖+
            (4*Cc*Cv)*(Real.sqrt (n : ℝ)*(n : ℝ)^(r*η-1/2))*‖χ‖ := by ring
          _ = _ := by rw [hsqrtpow]; ring
      _ ≤ _ := by gcongr
  have hmean : ‖(∑ j,u j : Q.1).val‖ ≤ ∑ j,‖(u j).val‖ := by
    rw [Submodule.coe_sum]
    exact norm_sum_le _ _
  refine ⟨fun j => ?_,?_,?_,?_⟩
  · exact (hvp j).trans (by gcongr)
  · exact (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans (hvs.trans (by gcongr))
  · exact (add_le_add hmean le_rfl).trans hfull'
  · exact hd.trans (by gcongr)


/-- See the proof of Lemma 6.5 in the paper: compose internal existence
and the two-matrix estimate on a common scalar form. -/
theorem short_pair_on_form_internal {X : Type*} [MeasurableSpace X] {ν : Measure X}
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (s : ℝ) (hs : 1 < s) (n : ℕ+) (m : ℕ) (i₀ : Fin (n : ℕ))
    (χ : Lp ℝ 2 ν) (u : Fin (n : ℕ) → Q.1)
    (MM : X → Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ)
    (rv rc η Cv Cc : ℝ) (hrv : 0 ≤ rv) (hrc : 0 ≤ rc) (hη : 0 < η)
    (hCv : 1 ≤ Cv) (hCc : 1 ≤ Cc)
    (haux : ∃ v : Fin (n : ℕ) → Q.1,
      WeightedWeakSolution Q MM ⊤ (fun i => if i=i₀ then χ else 0) v ∧
      (∀ j, ‖(v j).val‖ ≤ Cv*(n : ℝ)^(rv*η)*(1+|(j.val : ℝ)-(i₀.val : ℝ)|)^(-s)*‖χ‖) ∧
      (∑ j,‖(v j).val‖)+Real.sqrt (Q.2 (∑ j,v j) (∑ j,v j)) ≤ Cv*(n : ℝ)^(rv*η)*‖χ‖)
    (hcomp : ∀ v : Fin (n : ℕ) → Q.1,
      WeightedWeakSolution Q MM ⊤ (fun i => if i=i₀ then χ else 0) v →
      (∀ j, ‖(v j).val‖ ≤ (Cv*(n : ℝ)^(rv*η)*‖χ‖)*(1+|(j.val : ℝ)-(i₀.val : ℝ)|)^(-s)) →
      ‖WithLp.toLp 2 (fun j => (u j-v j).val)‖+Real.sqrt (∑ j,Q.2 (u j-v j) (u j-v j)) ≤
      Cc*(n : ℝ)^(rc*η)*(Cv*(n : ℝ)^(rv*η)*‖χ‖)*
        ((n : ℝ)^(-(s-1/2))+(((n : ℕ)+m+1 : ℕ) : ℝ)^(-(1/2 : ℝ)))) :
    let r := 1+rv+rc
    let C := 1+Cv+6*Cc*Cv
    ∃ v : Fin (n : ℕ) → Q.1,
      WeightedWeakSolution Q MM ⊤ (fun i => if i=i₀ then χ else 0) v ∧
      (∀ j, ‖(v j).val‖ ≤ C*(n : ℝ)^(r*η)*(1+|(j.val : ℝ)-(i₀.val : ℝ)|)^(-s)*‖χ‖) ∧
      (∑ j,‖(v j).val‖) ≤ C*(n : ℝ)^(r*η)*‖χ‖ ∧
      ‖(∑ j,u j : Q.1).val‖+Real.sqrt (Q.2 (∑ j,u j) (∑ j,u j)) ≤ C*(n : ℝ)^(r*η)*‖χ‖ ∧
      ‖WithLp.toLp 2 (fun j => (u j-v j).val)‖+Real.sqrt (∑ j,Q.2 (u j-v j) (u j-v j)) ≤
        C*(n : ℝ)^(r*η-1/2)*‖χ‖ := by
  intro r C
  obtain ⟨v,hv,hvp,hvs⟩ := haux
  have hc := hcomp v hv (fun j => by simpa only [mul_assoc,mul_left_comm,mul_comm] using hvp j)
  exact ⟨v,hv,short_pair_rate_internal Q hQ s hs n m i₀ χ u v
    rv rc η Cv Cc hrv hrc hη hCv hCc hvp hvs hc⟩

/-- See the proof of Lemma 6.5 in the paper: one curvature power
controls the physical and full cutoff matrices at independent exponents. -/
theorem short_common_curvature_factors_internal (s : ℝ) (hs : 1 < s)
    (n : ℕ+) (ε η q r C β βlo βhi : ℝ)
    (hε : 0 < ε) (hεη : ε ≤ η) (_hq : 0 ≤ q) (hqr : q ≤ r) (hsr : s+2 ≤ r)
    (hC : 1 ≤ C) (hlo : 0 < βlo) (hβlo : βlo ≤ β) (hβhi : β ≤ βhi) :
    (βlo/C)*(n : ℝ)^(-(r*η)) ≤ β*(n : ℝ)^(-(s+2)*ε) ∧
    (βlo/C)*(n : ℝ)^(-(r*η)) ≤ β*(C*(n : ℝ)^(q*η))⁻¹ ∧
    β*(C*(n : ℝ)^(q*η)) ≤ (βhi*C)*(n : ℝ)^(r*η) := by
  have hn : (0 : ℝ) < n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hη : 0 < η := hε.trans_le hεη
  have hβ : 0 < β := hlo.trans_le hβlo
  have hβhi0 : 0 < βhi := hβ.trans_le hβhi
  have hBC : βlo/C ≤ β := (div_le_self hlo.le hC).trans hβlo
  refine ⟨mul_le_mul hBC (Real.rpow_le_rpow_of_exponent_le hn1 ?_) (by positivity) hβ.le,?_,?_⟩
  · nlinarith only [mul_le_mul_of_nonneg_left hεη (by linarith : 0 ≤ s+2),
      mul_le_mul_of_nonneg_right hsr hη.le]
  · rw [mul_inv,← Real.rpow_neg hn.le,div_eq_mul_inv,mul_assoc βlo]
    exact mul_le_mul hβlo
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1
        (by nlinarith only [hqr,hη.le])) (by positivity)) (by positivity) hβ.le
  · calc
      _ ≤ βhi*(C*(n : ℝ)^(r*η)) := by
        gcongr
      _ = _ := by ring

/-- See the proof of Lemma 6.5 in the paper: transfer to the internal
field while retaining the exceptional power, before fixing C0. -/
theorem short_unabsorbed_square_transfer_internal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (n : ℕ+) (r η C₀ A T D F B e : ℝ)
    (hr : 0 ≤ r) (hη : 0 ≤ η) (hη1 : η ≤ 1) (hT : 0 ≤ T) (hD : 0 ≤ D)
    (hF : 0 ≤ F) (he : 0 ≤ e) (ψ u v : Fin (n : ℕ) → E)
    (hphysical : ‖WithLp.toLp 2 (fun i => ψ i-u i)‖^2 ≤
      A*(n : ℝ)^(8*(r*η)-1)*F^2+T*(n : ℝ)^(8+4*(r*η)-C₀)*B^2*e)
    (hcutoff : ‖WithLp.toLp 2 (fun i => u i-v i)‖ ≤ D*(n : ℝ)^(r*η-1/2)*F) :
    ‖WithLp.toLp 2 (fun i => ψ i-v i)‖^2 ≤
      (2*A+2*D^2)*(n : ℝ)^(2*((4*r)*η)-1)*F^2+
        (2*T)*(n : ℝ)^(8+4*r-C₀)*B^2*e := by
  let P := (C₀-(8+4*(r*η)))/2
  have hh := short_square_transfer_internal n (r*η) 4 C₀ P A T D F B e
    (mul_nonneg hr hη) hT hD hF he (by dsimp only [P]; linarith) ψ u v
    (by simpa only [show 4+4*(r*η)+4-C₀ = 8+4*(r*η)-C₀ by ring] using hphysical) hcutoff
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hp : (n : ℝ)^(-2*P) ≤ (n : ℝ)^(8+4*r-C₀) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by
      dsimp only [P]
      nlinarith only [mul_le_mul_of_nonneg_left hη1 hr])
  have ht := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2*T))
      (sq_nonneg B)) he
  simpa only [show 2*(4*(r*η))-1 = 2*((4*r)*η)-1 by ring] using
    hh.trans (add_le_add le_rfl ht)

/-- See the proof of Lemma 6.5 in the paper: the short internal value
profile gives the exact boundary-weighted auxiliary sum. -/
theorem short_auxiliary_weighted_profile_internal {E : Type*} [NormedAddCommGroup E]
    (s : ℝ) (hs : 1 < s) (n : ℕ+) (i₀ : Fin (n : ℕ))
    (hi₀ : |(i₀.val : ℝ)+1-(n : ℝ)/2| ≤ (n : ℝ)/4)
    (D loss F : ℝ) (hD : 0 ≤ D) (hF : 0 ≤ F) (v : Fin (n : ℕ) → E)
    (hprofile : ∀ j, ‖v j‖ ≤ D*(n : ℝ)^loss*(1+|(j.val : ℝ)-(i₀.val : ℝ)|)^(-s)*F)
    (hsum : (∑ j,‖v j‖) ≤ D*(n : ℝ)^loss*F) :
    (∑ j,InteractionDifferential.boundaryWeight s n j*‖v j‖) ≤
      ((4*8^s+Real.sqrt 8)*D)*(n : ℝ)^(loss-1/2)*F := by
  have hn : (0 : ℝ) < n := by positivity
  have hvalue (j : Fin (n : ℕ)) : ‖v j‖ ≤
      (D*(n : ℝ)^loss)*(1+(Nat.dist j.val i₀.val : ℝ))^(-s)*F := by
    rw [show (Nat.dist j.val i₀.val : ℝ) = |(j.val : ℝ)-(i₀.val : ℝ)| by
      exact_mod_cast natCast_dist_eq_abs j.val i₀.val]
    exact hprofile j
  have hh := FixedLengthDecay.short_auxiliary_weighted_sum_internal s hs n i₀ hi₀
    (D*(n : ℝ)^loss) F (by positivity) hF (fun j => ‖v j‖) (fun _ => norm_nonneg _) hvalue hsum
  convert hh using 1
  rw [show loss-1/2 = loss+(-(1 : ℝ)/2) by ring,Real.rpow_add hn]
  ring

/-- See the proof of Lemma 6.5 in the paper: choose a common prefactor
for auxiliary sums, squared comparison and the two physical fibre sums. -/
theorem short_common_prefactor_internal (s D E T : ℝ) (hD : 0 ≤ D)
    (hE : 0 ≤ E) (hT : 0 ≤ T) :
    let K := 4*8^s+Real.sqrt 8
    let W := 2*∑' k : ℕ,(1+(k : ℝ))^(-(2*s-1))
    ∃ C : ℝ, 0 < C ∧ D ≤ C ∧ E ≤ C ∧ T ≤ C ∧ K*D ≤ C ∧
      K*D+Real.sqrt W*Real.sqrt E ≤ C ∧ D+Real.sqrt E ≤ C ∧
      (1+Real.sqrt W)*Real.sqrt T ≤ C := by
  intro K W
  let C := 1+D+E+T+K*D+Real.sqrt W*Real.sqrt E+Real.sqrt E+(1+Real.sqrt W)*Real.sqrt T
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hKD : 0 ≤ K*D := mul_nonneg hK hD
  have hWE : 0 ≤ Real.sqrt W*Real.sqrt E := by positivity
  have hTE : 0 ≤ (1+Real.sqrt W)*Real.sqrt T := by positivity
  refine ⟨C,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    dsimp only [C] <;> linarith [Real.sqrt_nonneg E]

/-- See equation (6.23) of the paper: assemble the common short
prefactor while absorbing only a nonpositive exceptional sum exponent. -/
theorem short_common_fibre_bounds_internal {V : Type*} [NormedAddCommGroup V]
    (s : ℝ) (hs : 1 < s) (n : ℕ+) (i₀ : Fin (n : ℕ))
    (hi₀ : |(i₀.val : ℝ)+1-(n : ℝ)/2| ≤ (n : ℝ)/4)
    (D E T C loss b C₀ F B e : ℝ)
    (hD : 0 ≤ D) (hE : 0 ≤ E) (hT : 0 ≤ T) (hF : 0 ≤ F) (hB : 0 ≤ B) (he : 0 ≤ e)
    (hC₀ : 1+b ≤ C₀) (hDC : D ≤ C) (hEC : E ≤ C) (hTC : T ≤ C) :
    let K := 4*8^s+Real.sqrt 8
    let W := 2*∑' k : ℕ,(1+(k : ℝ))^(-(2*s-1))
    K*D ≤ C → K*D+Real.sqrt W*Real.sqrt E ≤ C → D+Real.sqrt E ≤ C →
    (1+Real.sqrt W)*Real.sqrt T ≤ C →
    ∀ v : Fin (n : ℕ) → V,
    (∀ j,‖v j‖ ≤ D*(n : ℝ)^loss*(1+|(j.val : ℝ)-(i₀.val : ℝ)|)^(-s)*F) →
    (∑ j,‖v j‖) ≤ D*(n : ℝ)^loss*F →
    (∑ j,InteractionDifferential.boundaryWeight s n j*‖v j‖) ≤ C*(n : ℝ)^(loss-1/2)*F ∧
    (∑ j,‖v j‖) ≤ C*(n : ℝ)^loss*F ∧
    ∀ ψ : Fin (n : ℕ) → V,
    (‖WithLp.toLp 2 (fun j => ψ j-v j)‖^2 ≤
      E*(n : ℝ)^(2*loss-1)*F^2+T*(n : ℝ)^(b-C₀)*B^2*e) →
    (‖WithLp.toLp 2 (fun j => ψ j-v j)‖^2 ≤
      C*(n : ℝ)^(2*loss-1)*F^2+C*(n : ℝ)^(b-C₀)*B^2*e) ∧
    (∑ j,InteractionDifferential.boundaryWeight s n j*‖ψ j‖) ≤
      C*(n : ℝ)^(loss-1/2)*F+C*B*Real.sqrt e ∧
    (∑ j,‖ψ j‖) ≤ C*(n : ℝ)^loss*F+C*B*Real.sqrt e := by
  intro K W hKDC hWEC hSEC hTEC v hvp hvs
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hvw := short_auxiliary_weighted_profile_internal s hs n i₀ hi₀ D loss F hD hF v hvp hvs
  have hweights : (∑ j,InteractionDifferential.boundaryWeight s n j^2) ≤ W*(n : ℝ)^(1-2*(1/2) : ℝ) := by
    simpa only [show (1 : ℝ)-2*(1/2) = 0 by ring,Real.rpow_zero,mul_one,W] using
      FixedLengthDecay.short_boundary_square_sum s hs n
  have htail : (n : ℝ)^((1+b-C₀)/2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith only [hC₀])
  refine ⟨hvw.trans (by gcongr),hvs.trans (by gcongr),?_⟩
  intro ψ herr
  obtain ⟨hw,hu⟩ := fibre_sums_retaining_loss_internal n
    (InteractionDifferential.boundaryWeight s n)
    (fun j => (InteractionDifferential.boundaryWeight_pos _ _ _).le)
    (1/2) W (K*D) D E T loss b C₀ F B e (by norm_num) hW hE hT hF hB he
    ψ v hweights hvw hvs herr
  refine ⟨herr.trans (by gcongr),hw.trans ?_,hu.trans ?_⟩
  · apply add_le_add
    · gcongr
    · calc
        _ ≤ ((1+Real.sqrt W)*Real.sqrt T)*1*B*Real.sqrt e := by gcongr
        _ ≤ C*B*Real.sqrt e := by rw [mul_one]; gcongr
  · apply add_le_add
    · gcongr
    · calc
        _ ≤ ((1+Real.sqrt W)*Real.sqrt T)*1*B*Real.sqrt e := by gcongr
        _ ≤ C*B*Real.sqrt e := by rw [mul_one]; gcongr

section Notation

variable (p : Parameters) (n : ℕ+) (m : ℕ) (θ : PhysicalCutoff) (ε η κ₀ : ℝ)

local notation "F" => (fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
  ∑ i, (θ.val (((n : ℝ)^ε)⁻¹*y i)+θ.val (((n : ℝ)^ε)⁻¹*(y i)⁻¹)))
local notation "K" => (fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
  p.val.1⁻¹*(p.val.1*F y-Real.log (∫ z : EuclideanSpace ℝ (Fin m),
    (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,z)).toReal)))
local notation "G" => shortFineEvent p n m η κ₀
local notation "I" => (fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) =>
  IntervalBoundary.internalMatrix ((n : ℕ)+m).succPNat n (by simp; omega)
    (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x))
local notation "Hf" => (fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) =>
  if x ∈ G then hessianMatrix K x.val else (1 : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ))
local notation "Mf" => (fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) =>
  if x ∈ G then hessianMatrix F x.val+I x else (1 : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ))
local notation "H" => (fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) =>
  p.val.1 • hessianMatrix K x.val)
local notation "U" => (fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) => p.val.1 • Hf x)
local notation "M" => (fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) => p.val.1 • Mf x)

/-- See the proof of Lemma 6.5 in the paper: the literal beta-scaled
short marginal Hessian is measurable, positive and coercive on its full
carrier, with the physical penalty exponent epsilon. -/
theorem short_physical_matrix_data_internal (hs : 1 < p.val.2) (hε : 0 < ε) :
    (∀ i j, Measurable (fun x => H x i j)) ∧
    (∀ x, (H x).PosSemidef) ∧
    ∀ x, (∀ i j, H x i j = H x j i) ∧ ∀ z : Fin (n : ℕ) → ℝ,
      (p.val.1*(n : ℝ)^(-(p.val.2+2)*ε))*(∑ i,z i^2) ≤
        ∑ i,∑ j,z i*H x i j*z j := by
  obtain ⟨hK,hcurv⟩ := PhysicalFibres.active_marginal_curvature p hs
    n m n.pos (Equiv.refl _) θ ε hε true
  change ContDiffOn ℝ ∞ K _ at hK
  have ha : 0 < p.val.1*(n : ℝ)^(-(p.val.2+2)*ε) := by positivity [p.property.1]
  have hdata (x : AffineSimplex.chartDomain n ((n+m : ℕ)+1)) :
      (∀ i j, H x i j = H x j i) ∧ ∀ z : Fin (n : ℕ) → ℝ,
      (p.val.1*(n : ℝ)^(-(p.val.2+2)*ε))*(∑ i,z i^2) ≤
        ∑ i,∑ j,z i*H x i j*z j := by
    have hx : ContDiffAt ℝ 2 K x.val :=
      (hK.contDiffAt ((AffineSimplex.isOpen_chartDomain _ _).mem_nhds x.property)).of_le
        (by norm_num)
    refine ⟨fun i j => congrArg (fun t => p.val.1*t) (hessianMatrix_symm hx i j),?_⟩
    intro z
    have hh := mul_le_mul_of_nonneg_left (hcurv x.val x.property (WithLp.toLp 2 z)) p.property.1.le
    change p.val.1*((n : ℝ)^(-(p.val.2+2)*ε)*‖WithLp.toLp 2 z‖^2) ≤
      p.val.1*fderiv ℝ (fderiv ℝ K) x.val (WithLp.toLp 2 z) (WithLp.toLp 2 z) at hh
    rw [← PhysicalEnergy.hessianMatrix_quadratic hx,EuclideanSpace.real_norm_sq_eq] at hh
    change p.val.1*(n : ℝ)^(-(p.val.2+2)*ε)*(∑ i,z i^2) ≤
      ∑ i,∑ j,z i*(p.val.1*hessianMatrix K x.val i j)*z j
    generalize hessianMatrix K x.val = A at hh ⊢
    simpa only [Finset.mul_sum,mul_assoc,mul_left_comm] using hh
  refine ⟨fun i j => (measurable_hessianMatrix (AffineSimplex.isOpen_chartDomain _ _) hK i j).const_mul _,
    fun x => ?_,hdata⟩
  exact Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨by
    ext i j
    simpa only [Matrix.conjTranspose_apply,star_trivial] using (hdata x).1 j i,
    fun z => by
      simpa only [dotProduct,Matrix.mulVec,star_trivial,Finset.mul_sum,mul_assoc] using
        (mul_nonneg ha.le (Finset.sum_nonneg fun i _ => sq_nonneg (z i))).trans ((hdata x).2 z)⟩

/-- See the proof of Lemma 6.5 in the paper: unrestricted existence for
the full cutoff over the specified common fibre form. -/
theorem short_full_cutoff_exists_internal (hs : 1 < p.val.2)
    (hε : 0 < ε) (hεη : ε ≤ η) (hhalf : 2*(n : ℕ) ≤ (n : ℕ)+m+1)
    (ν : Measure (AffineSimplex.chartDomain n ((n+m : ℕ)+1))) [IsProbabilityMeasure ν]
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q) (hcon : IsConservativeScalarForm Q)
    (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν) :
    ∃ u : Fin (n : ℕ) → Q.1,
      WeightedWeakSolution Q U ⊤ (fun i => if i=i₀ then χ else 0) u := by
  have hh := short_independent_full_solution_internal p hs n m θ ε η κ₀
    hε hεη hhalf ν Q hQ hcon i₀ χ
  exact hh.exists

/-- See the proof of Lemma 6.5 in the paper: existence and summable
value/mean-gradient bounds for the actual internal cutoff on a specified
conservative form, with constants before the volumes and the source. -/
theorem short_internal_auxiliary_exists_internal (s : ℝ) (hs : 1 < s)
    (κ₀ : ℝ) (hκ₀ : 0 ≤ κ₀) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ (θ : PhysicalCutoff) (ε η : ℝ), 0 < ε → ε ≤ η →
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∃ C : ℝ, 1 ≤ C ∧
    ∀ (p : Parameters), p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
    ∀ (n : ℕ+) (m : ℕ), 4 ≤ (n : ℕ)+m+1 → 2*(n : ℕ) ≤ (n : ℕ)+m+1 →
    let FF := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      ∑ i, (θ.val (((n : ℝ)^ε)⁻¹*y i)+θ.val (((n : ℝ)^ε)⁻¹*(y i)⁻¹))
    let MM := fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) => p.val.1 •
      (if x ∈ shortFineEvent p n m η κ₀ then hessianMatrix FF x.val+
        IntervalBoundary.internalMatrix ((n : ℕ)+m).succPNat n (by simp; omega)
          (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x) else 1)
    ∀ (ν : Measure (AffineSimplex.chartDomain n ((n+m : ℕ)+1))) [IsProbabilityMeasure ν]
      (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
    ∀ i₀ : Fin (n : ℕ), |(i₀.val : ℝ)+1-(n : ℝ)/2| ≤ (n : ℝ)/4 → ∀ χ : Lp ℝ 2 ν,
    ∃ v : Fin (n : ℕ) → Q.1,
      WeightedWeakSolution Q MM ⊤ (fun i => if i=i₀ then χ else 0) v ∧
      (∀ j, ‖(v j).val‖ ≤ C*(n : ℝ)^(r*η)*
        (1+|(j.val : ℝ)-(i₀.val : ℝ)|)^(-s)*‖χ‖) ∧
      (∑ j, ‖(v j).val‖)+Real.sqrt (Q.2 (∑ j,v j) (∑ j,v j)) ≤ C*(n : ℝ)^(r*η)*‖χ‖ := by
  obtain ⟨r,hr,haux⟩ := short_independent_auxiliary_internal s hs κ₀ hκ₀
  refine ⟨r,hr,?_⟩
  intro θ ε η hε hεη βlo βhi hlo hle
  obtain ⟨C,hC,haux⟩ := haux θ ε η hε hεη βlo βhi hlo hle
  refine ⟨C,hC,?_⟩
  intro p hp hpl hph n m hN hhalf FF MM ν _ Q hQ hcon i₀ hi₀ χ
  have hi := abs_le.mp hi₀
  have hiL : (n : ℝ)/4 ≤ (i₀.val : ℝ)+1 := by linarith only [hi.1]
  have hiR : (i₀.val : ℝ)+1 ≤ 3*(n : ℝ)/4 := by linarith only [hi.2]
  specialize haux p hp hpl hph n m hN hhalf
  dsimp only at haux
  specialize haux ν Q hQ hcon i₀ hiL hiR χ
  obtain ⟨v,hv,_⟩ := haux.1
  exact ⟨v,hv,(haux.2 v hv).1,(haux.2 v hv).2.1⟩

/-- See the proof of Lemma 6.5 in the paper, short use of Subsection 4.5:
construct the internal solution and estimate both solutions
over the same conservative form, including the full mean-gradient estimate
and the volume-rate comparison. The full solution is supplied by the
preceding existence theorem.
The loss is fixed before both exponents and temperature. -/
theorem short_uniform_auxiliary_pair_internal (s : ℝ) (hs : 1 < s)
    (κ₀ : ℝ) (hκ₀ : 0 ≤ κ₀) :
    ∃ r : ℝ, 0 < r ∧ ∀ (θ : PhysicalCutoff) (ε η : ℝ), 0 < ε → ε ≤ η →
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∃ C : ℝ, 1 ≤ C ∧
    ∀ (p : Parameters), p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
    ∀ (n : ℕ+) (m : ℕ), 4 ≤ (n : ℕ)+m+1 → 2*(n : ℕ) ≤ (n : ℕ)+m+1 →
    let FF := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      ∑ i, (θ.val (((n : ℝ)^ε)⁻¹*y i)+θ.val (((n : ℝ)^ε)⁻¹*(y i)⁻¹))
    let KK := fun y => p.val.1⁻¹*(p.val.1*FF y-Real.log (∫ z : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,z)).toReal))
    let UU := fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) => p.val.1 •
      (if x ∈ shortFineEvent p n m η κ₀ then hessianMatrix KK x.val else 1)
    let MM := fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) => p.val.1 •
      (if x ∈ shortFineEvent p n m η κ₀ then hessianMatrix FF x.val+
        IntervalBoundary.internalMatrix ((n : ℕ)+m).succPNat n (by simp; omega)
          (conditionalIntervalWeight p n m n.pos (Equiv.refl _) x) else 1)
    ∀ (ν : Measure (AffineSimplex.chartDomain n ((n+m : ℕ)+1))) [IsProbabilityMeasure ν]
      (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
    ∀ i₀ : Fin (n : ℕ), |(i₀.val : ℝ)+1-(n : ℝ)/2| ≤ (n : ℝ)/4 → ∀ χ : Lp ℝ 2 ν,
    ∀ u : Fin (n : ℕ) → Q.1,
      WeightedWeakSolution Q UU ⊤ (fun i => if i=i₀ then χ else 0) u →
    ∃ v : Fin (n : ℕ) → Q.1,
      WeightedWeakSolution Q MM ⊤ (fun i => if i=i₀ then χ else 0) v ∧
      (∀ j, ‖(v j).val‖ ≤ C*(n : ℝ)^(r*η)*
        (1+|(j.val : ℝ)-(i₀.val : ℝ)|)^(-s)*‖χ‖) ∧
      (∑ j, ‖(v j).val‖) ≤ C*(n : ℝ)^(r*η)*‖χ‖ ∧
      ‖(∑ j,u j : Q.1).val‖+Real.sqrt (Q.2 (∑ j,u j) (∑ j,u j)) ≤ C*(n : ℝ)^(r*η)*‖χ‖ ∧
      ‖WithLp.toLp 2 (fun j => (u j-v j).val)‖+
        Real.sqrt (∑ j,Q.2 (u j-v j) (u j-v j)) ≤ C*(n : ℝ)^(r*η-1/2)*‖χ‖ := by
  obtain ⟨rv,hrv,haux⟩ := short_internal_auxiliary_exists_internal s hs κ₀ hκ₀
  obtain ⟨rc,hrc,hcomp⟩ := short_independent_comparison_internal s hs κ₀ hκ₀
  let r := 1+rv+rc
  have hr : 0 < r := by dsimp only [r]; linarith
  refine ⟨r,hr,?_⟩
  intro θ ε η hε hεη βlo βhi hlo hle
  obtain ⟨Cv,hCv,haux⟩ := haux θ ε η hε hεη βlo βhi hlo hle
  obtain ⟨Cc,hCc,hcomp⟩ := hcomp θ ε η hε hεη βlo βhi hlo hle
  let C := 1+Cv+6*Cc*Cv
  have hC : 1 ≤ C := by dsimp only [C]; nlinarith
  refine ⟨C,hC,?_⟩
  intro p hp hpl hph n m hN hhalf FF KK UU MM ν _ Q hQ hcon i₀ hi₀ χ u hu
  have hi := abs_le.mp hi₀
  have hiL : (n : ℝ)/4 ≤ (i₀.val : ℝ)+1 := by linarith only [hi.1]
  have hiR : (i₀.val : ℝ)+1 ≤ 3*(n : ℝ)/4 := by linarith only [hi.2]
  have hη : 0 < η := hε.trans_le hεη
  apply short_pair_on_form_internal Q hQ s hs n m i₀ χ u MM
    rv rc η Cv Cc hrv hrc hη hCv hCc
  · exact haux p hp hpl hph n m hN hhalf ν Q hQ hcon i₀ hi₀ χ
  · intro v hv hprof
    exact hcomp p hp hpl hph n m hN hhalf ν Q hQ i₀ hiL hiR χ
      (Cv*(n : ℝ)^(rv*η)*‖χ‖) (by positivity) u v hu hv hprof

/-- See the proof of Lemma 6.5 in the paper: instantiate the conditional
physical/full-cutoff square with the actual short envelope and event. The
coefficient bounds and the full mean estimates remain internal inputs. The exceptional coefficient is derived from the physical marginal. -/
theorem short_actual_square_internal (hs : 1 < p.val.2)
    (hε : 0 < ε) (hεη : ε ≤ η)
    (q r Cm D0 βlo βhi C₀ : ℝ) (hq : 0 ≤ q) (hqr : q ≤ r)
    (hsr : p.val.2+2 ≤ r) (hCm : 1 ≤ Cm) (hD0 : 0 ≤ D0)
    (hlo : 0 < βlo) (hpl : βlo ≤ p.val.1) (hph : p.val.1 ≤ βhi)
    (hcut : ∀ x, (∀ i j,Hf x i j = Hf x j i) ∧ ∀ z : Fin (n : ℕ) → ℝ,
      (Cm*(n : ℝ)^(q*η))⁻¹*(∑ i,z i^2) ≤ ∑ i,∑ j,z i*Hf x i j*z j ∧
      (∑ i,∑ j,z i*Hf x i j*z j) ≤ Cm*(n : ℝ)^(q*η)*(∑ i,z i^2))
    (ν : Measure (AffineSimplex.chartDomain n ((n+m : ℕ)+1))) [IsProbabilityMeasure ν]
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (he : (∫⁻ x in Gᶜ,ENNReal.ofReal (shortEnvelope p n m θ ε C₀ x) ∂ν) ≠ (∞ : ℝ≥0∞))
    (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν) (B : ℝ) (hB : 0 ≤ B)
    (hχ : ∀ᵐ x ∂ν,|χ x| ≤ B) (ψ u : Fin (n : ℕ) → Q.1)
    (hψ : WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ)))
      (fun i => if i=i₀ then χ else 0) ψ)
    (hu : WeightedWeakSolution Q U ⊤ (fun i => if i=i₀ then χ else 0) u)
    (hmean : ‖(∑ i,u i : Q.1).val‖+Real.sqrt (Q.2 (∑ i,u i) (∑ i,u i)) ≤
      D0*(n : ℝ)^(r*η)*‖χ‖) :
    let a0 := βlo/Cm
    let A := 3*((1+βhi*Cm)*D0^2/a0+D0^2)
    let T := 36*(2*βhi)*a0⁻¹^2/a0
    let e := (∫⁻ x in Gᶜ,ENNReal.ofReal (shortEnvelope p n m θ ε C₀ x) ∂ν).toReal
    ‖WithLp.toLp 2 (fun i => (ψ i).val-(u i).val)‖^2 ≤
      A*(n : ℝ)^(8*(r*η)-1)*‖χ‖^2+T*(n : ℝ)^(8+4*(r*η)-C₀)*B^2*e := by
  intro a0 A T e
  have hη : 0 < η := hε.trans_le hεη
  have hr : 0 ≤ r := hq.trans hqr
  have hβhi : 0 < βhi := (hlo.trans_le hpl).trans_le hph
  have hn : (0 : ℝ) < n := by positivity
  have hfac := short_common_curvature_factors_internal p.val.2 hs n ε η q r Cm
    p.val.1 βlo βhi hε hεη hq hqr hsr hCm hlo hpl hph
  obtain ⟨hHm,hHp,hHa⟩ := short_physical_matrix_data_internal p n m θ ε hs hε
  obtain ⟨hUm,_,hUs,_⟩ := short_independent_measurable_symmetric_internal p n m θ ε η κ₀ hs hε
  have hUb : ∃ b : ℝ, ∀ᵐ x ∂ν,∀ i j,|U x i j| ≤ b := by
    refine ⟨p.val.1*(Cm*(n : ℝ)^(q*η)),ae_of_all _ fun x i j => ?_⟩
    have hh := internal_entry_bound (Hf x) (Cm*(n : ℝ)^(q*η)) (hcut x).1
      (fun z => (mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg (z i))).trans
        ((hcut x).2 z).1) (fun z => ((hcut x).2 z).2) i j
    simpa only [Matrix.smul_apply,smul_eq_mul,abs_mul,abs_of_pos p.property.1] using
      mul_le_mul_of_nonneg_left hh p.property.1.le
  have hUl : ∀ᵐ x ∂ν,(∀ i j,U x i j = U x j i) ∧ ∀ z : Fin (n : ℕ) → ℝ,
      (a0*(n : ℝ)^(-(r*η)))*(∑ i,z i^2) ≤ ∑ i,∑ j,z i*U x i j*z j := by
    apply ae_of_all
    intro x
    refine ⟨fun i j => congrArg (fun t => p.val.1*t) ((hcut x).1 i j),fun z => ?_⟩
    have hh := mul_le_mul_of_nonneg_left ((hcut x).2 z).1 p.property.1.le
    change _ ≤ ∑ i,∑ j,z i*(p.val.1*Hf x i j)*z j
    generalize Hf x = A at hh ⊢
    have hc := mul_le_mul_of_nonneg_right hfac.2.1 (Finset.sum_nonneg (s := Finset.univ) fun (i : Fin (n : ℕ)) _ => sq_nonneg (z i))
    exact hc.trans (by simpa only [Finset.mul_sum,mul_assoc,mul_left_comm] using hh)
  have hHl : ∀ᵐ x ∂ν,(∀ i j,H x i j = H x j i) ∧ ∀ z : Fin (n : ℕ) → ℝ,
      (a0*(n : ℝ)^(-(r*η)))*(∑ i,z i^2) ≤ ∑ i,∑ j,z i*H x i j*z j :=
    ae_of_all _ fun x => ⟨(hHa x).1,fun z =>
      (mul_le_mul_of_nonneg_right hfac.1 (Finset.sum_nonneg fun i _ => sq_nonneg (z i))).trans
        ((hHa x).2 z)⟩
  have hUp := AbstractEnergy.scaled_posSemidef (ρ := ν) 1 (a0*(n : ℝ)^(-(r*η)))
    zero_le_one (by positivity : 0 ≤ a0*(n : ℝ)^(-(r*η))) U hUl
  simp only [one_smul] at hUp
  have heq : ∀ x,x ∈ G → H x = U x := by intro x hx; simp only [hx,↓reduceIte]
  have hgood : ∀ᵐ x ∂ν.restrict G,(∑ i,∑ j,H x i j) ≤ (βhi*Cm)*(n : ℝ)^(r*η+1) := by
    filter_upwards [ae_restrict_mem (measurableSet_shortFineEvent p hs n m θ η κ₀)] with x hx
    have hh := mul_le_mul_of_nonneg_left ((hcut x).2 (fun _ => 1)).2 p.property.1.le
    have hc := mul_le_mul_of_nonneg_right hfac.2.2 (show 0 ≤ (n : ℝ) by positivity)
    have hsum : (∑ i,∑ j,U x i j) ≤ p.val.1*(Cm*(n : ℝ)^(q*η))*(n : ℝ) := by
      change (∑ i,∑ j,p.val.1*Hf x i j) ≤ _
      generalize Hf x = A at hh ⊢
      simpa only [one_mul,mul_one,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
        nsmul_eq_mul,Finset.mul_sum,mul_assoc] using hh
    have heqsum := congrArg (fun A : Matrix (Fin (n : ℕ)) (Fin (n : ℕ)) ℝ => ∑ i,∑ j,A i j) (heq x hx)
    apply heqsum.le.trans (hsum.trans ?_)
    convert hc using 1
    rw [Real.rpow_add hn,Real.rpow_one]
    ring
  have hdef := short_physical_cutoff_defect_internal p hs n m θ ε η κ₀ C₀ hε
  have hW0 (x) : 0 ≤ shortEnvelope p n m θ ε C₀ x :=
    (Real.rpow_nonneg hn.le C₀).trans (shortEnvelope_lower p n m θ ε C₀ x)
  have hD : 2*p.val.1 ≤ 2*βhi := by linarith only [hph]
  have hbad := fun x => (hdef x).2.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD (by positivity)) (hW0 x))
  have hh := short_conditional_square_internal Q hQ n H U hHm
    (AbstractEnergy.scaled_measurable _ _ hUm) hUb (ae_of_all _ hHp) hUp
    a0 (r*η) (βhi*Cm) D0 (2*βhi) 4 C₀ (by positivity) (mul_nonneg hr hη.le)
    (by positivity) hD0 (by positivity) hHl hUl
    (shortEnvelope p n m θ ε C₀) (measurable_shortEnvelope p n m θ ε C₀) hW0
    G (measurableSet_shortFineEvent p hs n m θ η κ₀) he (ae_of_all _ heq)
    (ae_of_all _ fun x i j => ((hdef x).1 i j).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD (by positivity)) (hW0 x)))
    hgood (ae_of_all _ hbad) i₀ χ B hB hχ ψ u hψ hu
    ((le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans hmean)
    ((le_add_of_nonneg_left (norm_nonneg _)).trans hmean)
  simpa only [A,T,e,show 4+4*(r*η)+4-C₀ = 8+4*(r*η)-C₀ by ring] using hh

/-- See the proof of Lemma 6.5 in the paper: join the actual physical
square and the comparison, with one enlarged loss and an unabsorbed
exceptional size power. -/
theorem short_actual_transfer_internal (hs : 1 < p.val.2)
    (hε : 0 < ε) (hεη : ε ≤ η) (hη1 : η ≤ 1)
    (q r ℓ Cm D0 βlo βhi C₀ : ℝ) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hqr : q ≤ ℓ) (hrℓ : r ≤ ℓ) (hsℓ : p.val.2+2 ≤ ℓ)
    (hCm : 1 ≤ Cm) (hD0 : 0 ≤ D0)
    (hlo : 0 < βlo) (hpl : βlo ≤ p.val.1) (hph : p.val.1 ≤ βhi)
    (hcut : ∀ x, (∀ i j,Hf x i j = Hf x j i) ∧ ∀ z : Fin (n : ℕ) → ℝ,
      (Cm*(n : ℝ)^(q*η))⁻¹*(∑ i,z i^2) ≤ ∑ i,∑ j,z i*Hf x i j*z j ∧
      (∑ i,∑ j,z i*Hf x i j*z j) ≤ Cm*(n : ℝ)^(q*η)*(∑ i,z i^2))
    (ν : Measure (AffineSimplex.chartDomain n ((n+m : ℕ)+1))) [IsProbabilityMeasure ν]
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (he : (∫⁻ x in Gᶜ,ENNReal.ofReal (shortEnvelope p n m θ ε C₀ x) ∂ν) ≠ (∞ : ℝ≥0∞))
    (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν) (B : ℝ) (hB : 0 ≤ B)
    (hχ : ∀ᵐ x ∂ν,|χ x| ≤ B) (u v : Fin (n : ℕ) → Q.1)
    (hu : WeightedWeakSolution Q U ⊤ (fun i => if i=i₀ then χ else 0) u)
    (hmean : ‖(∑ i,u i : Q.1).val‖+Real.sqrt (Q.2 (∑ i,u i) (∑ i,u i)) ≤
      D0*(n : ℝ)^(r*η)*‖χ‖)
    (hcomp : ‖WithLp.toLp 2 (fun i => (u i-v i).val)‖+
      Real.sqrt (∑ i,Q.2 (u i-v i) (u i-v i)) ≤ D0*(n : ℝ)^(r*η-1/2)*‖χ‖) :
    let a0 := βlo/Cm
    let A := 3*((1+βhi*Cm)*D0^2/a0+D0^2)
    let T := 36*(2*βhi)*a0⁻¹^2/a0
    let e := (∫⁻ x in Gᶜ,ENNReal.ofReal (shortEnvelope p n m θ ε C₀ x) ∂ν).toReal
    ∀ ψ : Fin (n : ℕ) → Q.1,
    WeightedWeakSolution Q H (zeroSumComponents (Fin (n : ℕ)))
      (fun i => if i=i₀ then χ else 0) ψ →
    ‖WithLp.toLp 2 (fun i => (ψ i).val-(v i).val)‖^2 ≤
      (2*A+2*D0^2)*(n : ℝ)^(2*((4*ℓ)*η)-1)*‖χ‖^2+
        (2*T)*(n : ℝ)^(8+4*ℓ-C₀)*B^2*e := by
  intro a0 A T e ψ hψ
  have hη : 0 < η := hε.trans_le hεη
  have hℓ : 0 ≤ ℓ := hr.trans hrℓ
  have hβhi : 0 < βhi := (hlo.trans_le hpl).trans_le hph
  have ha0 : 0 < a0 := by dsimp only [a0]; positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hmean' : ‖(∑ i,u i : Q.1).val‖+Real.sqrt (Q.2 (∑ i,u i) (∑ i,u i)) ≤
      D0*(n : ℝ)^(ℓ*η)*‖χ‖ := hmean.trans (by gcongr)
  have hc : ‖WithLp.toLp 2 (fun i => (u i-v i).val)‖ ≤ D0*(n : ℝ)^(ℓ*η-1/2)*‖χ‖ :=
    (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans (hcomp.trans (by gcongr))
  have hh := short_actual_square_internal p n m θ ε η κ₀ hs hε hεη q ℓ Cm D0
    βlo βhi C₀ hq hqr hsℓ hCm hD0 hlo hpl hph hcut ν Q hQ he i₀ χ B hB hχ ψ u hψ hu hmean'
  exact short_unabsorbed_square_transfer_internal n ℓ η C₀ A T D0 ‖χ‖ B e hℓ hη.le hη1
    (by dsimp only [T]; positivity) hD0 (norm_nonneg _) ENNReal.toReal_nonneg
    (fun i => (ψ i).val) (fun i => (u i).val) (fun i => (v i).val) hh
    (by simpa only [Submodule.coe_sub] using hc)

/-- See the proof of Lemma 6.5 in the paper: unique physical tangent
solvability on the same specified closed scalar form as the two cutoffs. -/
theorem short_tangent_solution_internal (hs : 1 < p.val.2) (hε : 0 < ε)
    (ν : Measure (AffineSimplex.chartDomain n ((n+m : ℕ)+1)))
    (Q : ScalarFormData ν) (hQ : IsClosedScalarDirichletForm Q)
    (i₀ : Fin (n : ℕ)) (χ : Lp ℝ 2 ν) :
    ∃! ψ : Fin (n : ℕ) → Q.1, WeightedWeakSolution Q H
      (zeroSumComponents (Fin (n : ℕ))) (fun i => if i=i₀ then χ else 0) ψ := by
  obtain ⟨hm,hp,hl⟩ := short_physical_matrix_data_internal p n m θ ε hs hε
  let a := p.val.1*(n : ℝ)^(-(p.val.2+2)*ε)
  have ha : 0 < a := by dsimp only [a]; positivity [p.property.1]
  exact MatrixEnergy.weightedWeakSolution_existsUnique Q hQ H (zeroSumComponents (Fin (n : ℕ)))
    (ae_of_all _ hp) a ha (ae_of_all _ fun x z _ => (hl x).2 z) hm _

end Notation

/-- See the proof of Lemma 6.5 in the paper: uniform short conditional
comparison on any retained-coordinate probability, with the actual fine event,
physical penalty, and conditional first-moment error. No auxiliary estimate is
assumed. The loss and exceptional size power precede temperature and both
exponents. -/
theorem short_uniform_conditional_comparison_internal (s : ℝ) (hs : 1 < s)
    (κ₀ : ℝ) (hκ₀ : 0 ≤ κ₀) :
    ∃ κ b : ℝ, 0 < κ ∧ 0 < b ∧
    ∀ (θ : PhysicalCutoff) (ε η : ℝ), 0 < ε → ε ≤ η → η ≤ 1 →
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi →
    ∃ D E T : ℝ, 1 ≤ D ∧ 0 < E ∧ 0 < T ∧
    ∀ (p : Parameters), p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
    ∀ (n : ℕ+) (m : ℕ), 4 ≤ (n : ℕ)+m+1 → 2*(n : ℕ) ≤ (n : ℕ)+m+1 →
    ∀ C₀ : ℝ,
    let FF := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      ∑ i, (θ.val (((n : ℝ)^ε)⁻¹*y i)+θ.val (((n : ℝ)^ε)⁻¹*(y i)⁻¹))
    let KK := fun y => p.val.1⁻¹*(p.val.1*FF y-Real.log (∫ z : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,z)).toReal))
    let HH := fun x : AffineSimplex.chartDomain n ((n+m : ℕ)+1) => p.val.1 • hessianMatrix KK x.val
    ∀ (ν : Measure (AffineSimplex.chartDomain n ((n+m : ℕ)+1))) [IsProbabilityMeasure ν],
    (∫⁻ x in (shortFineEvent p n m η κ₀)ᶜ,
      ENNReal.ofReal (shortEnvelope p n m θ ε C₀ x) ∂ν) ≠ (∞ : ℝ≥0∞) →
    ∀ (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
    ∀ i₀ : Fin (n : ℕ), |(i₀.val : ℝ)+1-(n : ℝ)/2| ≤ (n : ℝ)/4 →
    ∀ (χ : Lp ℝ 2 ν) (B : ℝ), 0 ≤ B → (∀ᵐ x ∂ν,|χ x| ≤ B) →
    let e := (∫⁻ x in (shortFineEvent p n m η κ₀)ᶜ,
      ENNReal.ofReal (shortEnvelope p n m θ ε C₀ x) ∂ν).toReal
    ∃ v : Fin (n : ℕ) → Q.1,
      (∀ j, ‖(v j).val‖ ≤ D*(n : ℝ)^(κ*η)*
        (1+|(j.val : ℝ)-(i₀.val : ℝ)|)^(-s)*‖χ‖) ∧
      (∑ j,‖(v j).val‖) ≤ D*(n : ℝ)^(κ*η)*‖χ‖ ∧
      ∀ ψ : Fin (n : ℕ) → Q.1,
      WeightedWeakSolution Q HH (zeroSumComponents (Fin (n : ℕ)))
        (fun i => if i=i₀ then χ else 0) ψ →
      ‖WithLp.toLp 2 (fun j => (ψ j).val-(v j).val)‖^2 ≤
        E*(n : ℝ)^(2*(κ*η)-1)*‖χ‖^2+T*(n : ℝ)^(b-C₀)*B^2*e := by
  obtain ⟨q,hq,hmat⟩ := short_independent_matrix_bounds_internal s hs κ₀
  obtain ⟨r,hr,hpair⟩ := short_uniform_auxiliary_pair_internal s hs κ₀ hκ₀
  let ℓ := 1+r+q+(s+2)
  have hℓ : 0 < ℓ := by dsimp only [ℓ]; linarith
  have hqr : q ≤ ℓ := by dsimp only [ℓ]; linarith
  have hrℓ : r ≤ ℓ := by dsimp only [ℓ]; linarith
  have hsℓ : s+2 ≤ ℓ := by dsimp only [ℓ]; linarith
  have hrκ : r ≤ 4*ℓ := by linarith
  refine ⟨4*ℓ,8+4*ℓ,by positivity,by positivity,?_⟩
  intro θ ε η hε hεη hη1 βlo βhi hlo hle
  obtain ⟨Cm,hCm,hmat⟩ := hmat θ
  obtain ⟨D,hD,hpair⟩ := hpair θ ε η hε hεη βlo βhi hlo hle
  let a0 := βlo/Cm
  let A := 3*((1+βhi*Cm)*D^2/a0+D^2)
  let T := 36*(2*βhi)*a0⁻¹^2/a0
  have hβhi : 0 < βhi := hlo.trans_le hle
  have ha0 : 0 < a0 := by dsimp only [a0]; positivity
  have hA : 0 < A := by dsimp only [A]; positivity
  have hT : 0 < T := by dsimp only [T]; positivity
  refine ⟨D,2*A+2*D^2,2*T,hD,by positivity,by positivity,?_⟩
  intro p hp hpl hph n m hN hhalf C₀ FF KK HH ν _ he Q hQ hcon i₀ hi₀ χ B hB hχ e
  have hps : 1 < p.val.2 := hp ▸ hs
  have hη : 0 < η := hε.trans_le hεη
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.pos
  have hpower : (n : ℝ)^(r*η) ≤ (n : ℝ)^((4*ℓ)*η) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (mul_le_mul_of_nonneg_right hrκ hη.le)
  have hex := short_full_cutoff_exists_internal p n m θ ε η κ₀ hps hε hεη hhalf ν Q hQ hcon i₀ χ
  obtain ⟨u,hu⟩ := hex
  obtain ⟨v,hv,hvp,hvs,hmean,hcomp⟩ := hpair p hp hpl hph n m hN hhalf ν Q hQ hcon i₀ hi₀ χ u hu
  obtain ⟨_,_,hsym,hbound⟩ := hmat p hp n m hhalf ε η hε hεη
  have hcut := fun x => And.intro (hsym x) (hbound x)
  refine ⟨v,fun j => (hvp j).trans (by gcongr),hvs.trans (by gcongr),?_⟩
  exact short_actual_transfer_internal p n m θ ε η κ₀ hps hε hεη hη1 q r ℓ Cm D
    βlo βhi C₀ hq hr.le hqr hrℓ (hp ▸ hsℓ) hCm (by linarith) hlo hpl hph
    hcut ν Q hQ he i₀ χ B hB hχ u v hu hmean hcomp

/-- See Lemma 6.5 and the proof of Lemma 6.5 of the paper: the actual
retained marginal admits an intrinsic closed conservative scalar form. -/
theorem retained_common_scalar_form_internal (p : Parameters) (n m : ℕ)
    (θ : PhysicalCutoff) (ε : ℝ) (L : Ioo (0 : ℝ) ((n+1+m : ℕ)+1 : ℝ)) :
    ∃ Q : ScalarFormData (retainedKernel p n m θ ε L),
      IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q := by
  let b := (stdOrthonormalBasis ℝ (AffineSimplex.Tangent n)).reindex
    (finCongr (AffineSimplex.finrank_tangent n))
  obtain ⟨ν,_,_,hQ⟩ := retained_intrinsic_scalar_internal p n m θ ε L b.repr
  exact hQ

/-- See the proof of Lemma 6.5 and equation (6.23) of the paper:
one uniform retained-law theorem supplies both auxiliary sums, the unabsorbed
squared physical comparison, and both physical fibre sums. The actual intrinsic
form exists. All three equations use that same form. C0 can be chosen before
temperature, the physical and fine exponents, the volumes, the length and the
source. Any larger common envelope exponent is also permitted. -/
theorem retained_short_fibre_data_internal (s : ℝ) (hs : 1 < s)
    (κ₀ : ℝ) (hκ₀ : 1 ≤ κ₀) :
    ∃ κ b Cstar : ℝ, 0 < κ ∧ 0 < b ∧ s+5 ≤ Cstar ∧
      1+b+2*(κ₀+4) ≤ Cstar ∧
    ∀ (θ : PhysicalCutoff) (ε η : ℝ), 0 < ε → ε ≤ η → η ≤ 1 →
    ∀ βlo βhi : ℝ, 0 < βlo → βlo ≤ βhi → ∃ C : ℝ, 0 < C ∧
    ∀ (p : Parameters), p.val.2 = s → βlo ≤ p.val.1 → p.val.1 ≤ βhi →
    ∀ a m : ℕ, 1 ≤ a → 4*(a+1) ≤ a+1+m+1 → ∀ C₀ : ℝ, Cstar ≤ C₀ →
    ∀ᵐ L ∂lengthMeasure p a m θ ε,
    let n := a.succPNat
    let ν := retainedKernel p a m θ ε L
    let FF := fun y : EuclideanSpace ℝ (Fin (n : ℕ)) =>
      ∑ i, (θ.val (((n : ℝ)^ε)⁻¹*y i)+θ.val (((n : ℝ)^ε)⁻¹*(y i)⁻¹))
    let KK := fun y => p.val.1⁻¹*(p.val.1*FF y-Real.log (∫ z : EuclideanSpace ℝ (Fin m),
      (ProperMarginalChart.chartDensity p n m (Equiv.refl _) (y,z)).toReal))
    let HH := fun x : AffineSimplex.chartDomain n ((a+1+m : ℕ)+1) => p.val.1 • hessianMatrix KK x.val
    let e := (shortRemainder p a m θ ε C₀ η κ₀ L).toReal
    (shortRemainder p a m θ ε C₀ η κ₀ L < (∞ : ℝ≥0∞)) ∧
    (∃ Q : ScalarFormData ν, IsClosedScalarDirichletForm Q ∧ IsConservativeScalarForm Q) ∧
    ∀ (Q : ScalarFormData ν), IsClosedScalarDirichletForm Q → IsConservativeScalarForm Q →
    ∀ i₀ : Fin (n : ℕ), |(i₀.val : ℝ)+1-(n : ℝ)/2| ≤ (n : ℝ)/4 →
    ∀ (χ : Lp ℝ 2 ν) (B : ℝ), 0 ≤ B → (∀ᵐ x ∂ν,|χ x| ≤ B) →
    (∃! ψ : Fin (n : ℕ) → Q.1, WeightedWeakSolution Q HH (zeroSumComponents (Fin (n : ℕ)))
      (fun i => if i=i₀ then χ else 0) ψ) ∧
    ∃ v : Fin (n : ℕ) → Q.1,
      (∑ j,InteractionDifferential.boundaryWeight s n j*‖(v j).val‖) ≤
        C*(n : ℝ)^(κ*η-1/2)*‖χ‖ ∧
      (∑ j,‖(v j).val‖) ≤ C*(n : ℝ)^(κ*η)*‖χ‖ ∧
      ∀ ψ : Fin (n : ℕ) → Q.1, WeightedWeakSolution Q HH (zeroSumComponents (Fin (n : ℕ)))
        (fun i => if i=i₀ then χ else 0) ψ →
      (‖WithLp.toLp 2 (fun j => (ψ j).val-(v j).val)‖^2 ≤
        C*(n : ℝ)^(2*(κ*η)-1)*‖χ‖^2+C*(n : ℝ)^(b-C₀)*B^2*e) ∧
      (∑ j,InteractionDifferential.boundaryWeight s n j*‖(ψ j).val‖) ≤
        C*(n : ℝ)^(κ*η-1/2)*‖χ‖+C*B*Real.sqrt e ∧
      (∑ j,‖(ψ j).val‖) ≤ C*(n : ℝ)^(κ*η)*‖χ‖+C*B*Real.sqrt e := by
  obtain ⟨κ,b,hκ,hb,hcomp⟩ := short_uniform_conditional_comparison_internal s hs κ₀ (by linarith)
  let Cstar := max (s+5) (1+b+2*(κ₀+4))
  refine ⟨κ,b,Cstar,hκ,hb,le_max_left _ _,le_max_right _ _,?_⟩
  intro θ ε η hε hεη hη1 βlo βhi hlo hle
  obtain ⟨D,E,T,hD,hE,hT,hcomp⟩ := hcomp θ ε η hε hεη hη1 βlo βhi hlo hle
  let K := 4*8^s+Real.sqrt 8
  let W := 2*∑' k : ℕ,(1+(k : ℝ))^(-(2*s-1))
  obtain ⟨C,hC,hDC,hEC,hTC,hKDC,hWEC,hSEC,hTEC⟩ :=
    short_common_prefactor_internal s D E T (by linarith) hE.le hT.le
  refine ⟨C,hC,?_⟩
  intro p hp hpl hph a m _ha hvol C₀ hC₀
  have hps : 1 < p.val.2 := hp ▸ hs
  have hhalf : 2*(a+1) ≤ a+1+m+1 := by omega
  have hfinite := shortRemainder_finite_ae p hps a m θ ε C₀ η κ₀ hε hhalf
  filter_upwards [hfinite] with L hL
  intro n ν FF KK HH e
  refine ⟨hL,retained_common_scalar_form_internal p a m θ ε L,?_⟩
  intro Q hQ hcon i₀ hi₀ χ B hB hχ
  have he : (∫⁻ x in (shortFineEvent p n m η κ₀)ᶜ,
      ENNReal.ofReal (shortEnvelope p n m θ ε C₀ x) ∂ν) ≠ (∞ : ℝ≥0∞) := hL.ne
  have hdata := hcomp p hp hpl hph n m (by dsimp only [n,Nat.succPNat_coe]; omega)
    hhalf C₀ ν he Q hQ hcon i₀ hi₀ χ B hB hχ
  obtain ⟨v,hvp,hvs,herror⟩ := hdata
  have hC₀b : 1+b ≤ C₀ := by
    have hc := (le_max_right (s+5) (1+b+2*(κ₀+4))).trans hC₀
    linarith only [hc,hκ₀]
  have hbounds := short_common_fibre_bounds_internal s hs n i₀ hi₀
    D E T C (κ*η) b C₀ ‖χ‖ B e (by linarith) hE.le hT.le (norm_nonneg _) hB
    ENNReal.toReal_nonneg hC₀b hDC hEC hTC hKDC hWEC hSEC hTEC
    (fun j => (v j).val) hvp hvs
  refine ⟨short_tangent_solution_internal p n m θ ε hps hε ν Q hQ i₀ χ,
    v,hbounds.1,hbounds.2.1,?_⟩
  intro ψ hψ
  exact hbounds.2.2 (fun j => (ψ j).val) (herror ψ hψ)

end Riesz2.LengthAveragingFibres
