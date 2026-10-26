/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import Mathlib.Order.Filter.AtTopBot.Finite
public import Mathlib.Data.PNat.Basic
public import Mathlib.Order.SuccPred.PNat

/-!
# Extending parameter sequences across omitted sizes

An injectively indexed sequence can be filled at unused sizes without changing its limit.
This gives a two-parameter sequential criterion from results stated for full size sequences.
-/

public section

open Filter

namespace Riesz2

/-- Extension along distinct positive integer sizes preserves a limit shared with the filler. -/
theorem tendsto_extend_sizes {α : Type*} {l : Filter α} (n : ℕ → ℕ+)
    (hn : Function.Injective n) (a : ℕ → α) (b : ℕ+ → α)
    (ha : Tendsto a atTop l) (hb : Tendsto b atTop l) :
    Tendsto (Function.extend n a b) atTop l := by
  classical
  intro s hs
  obtain ⟨k, hk⟩ := eventually_atTop.mp (ha.eventually_mem hs)
  obtain ⟨m, hm⟩ := eventually_atTop.mp (hb.eventually_mem hs)
  change ∀ᶠ N : ℕ+ in atTop, Function.extend n a b N ∈ s
  filter_upwards [eventually_ge_atTop (max m ((Finset.range k).sup n + 1))] with N hN
  by_cases h : ∃ j, n j = N
  · obtain ⟨j, rfl⟩ := h
    rw [hn.extend_apply]
    apply hk
    by_contra hj
    have hjk : j < k := Nat.lt_of_not_ge hj
    have := Finset.le_sup (f := n) (Finset.mem_range.mpr hjk)
    have := (le_max_right m ((Finset.range k).sup n + 1)).trans hN
    exact (not_lt_of_ge this) (lt_of_le_of_lt ‹n j ≤ (Finset.range k).sup n›
      (Order.lt_succ _))
  · rw [Function.extend_apply' a b N h]
    exact hm N ((le_max_left _ _).trans hN)

/-- Applying a size-dependent observable commutes with extension along distinct sizes. -/
theorem apply_extend_sizes {α β : Type*} (n : ℕ → ℕ+)
    (hn : Function.Injective n) (a : ℕ → α) (b : ℕ+ → α) (p : ℕ+ → α → β) :
    (fun N => p N (Function.extend n a b N)) =
      Function.extend n (fun j => p (n j) (a j)) (fun N => p N (b N)) := by
  classical
  funext N
  by_cases h : ∃ j, n j = N
  · obtain ⟨j, rfl⟩ := h
    rw [hn.extend_apply, hn.extend_apply]
  · rw [Function.extend_apply' a b N h, Function.extend_apply' _ _ N h]

/-- A full-size limit with two asymptotic parameter conditions holds along arbitrary pairs.
The filler satisfies the same asymptotic conditions. -/
theorem tendsto_pairs_of_sections {α β γ δ : Type*}
    (p : ℕ+ → α → β) (q : ℕ+ → α → γ) (f : ℕ+ → α → δ)
    (lp : Filter β) (lq : Filter γ) (lf : Filter δ) (b : ℕ+ → α)
    (hbp : Tendsto (fun N => p N (b N)) atTop lp)
    (hbq : Tendsto (fun N => q N (b N)) atTop lq)
    (h : ∀ a : ℕ+ → α, Tendsto (fun N => p N (a N)) atTop lp →
      Tendsto (fun N => q N (a N)) atTop lq →
      Tendsto (fun N => f N (a N)) atTop lf)
    (n : ℕ → ℕ+) (a : ℕ → α) (hn : Tendsto n atTop atTop)
    (hp : Tendsto (fun j => p (n j) (a j)) atTop lp)
    (hq : Tendsto (fun j => q (n j) (a j)) atTop lq) :
    Tendsto (fun j => f (n j) (a j)) atTop lf := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, hms, hmono⟩ := strictMono_subseq_of_tendsto_atTop (hn.comp hns)
  let t := fun j => n (ns (ms j))
  let c := fun j => a (ns (ms j))
  have ht : Function.Injective t := hmono.injective
  let e := Function.extend t c b
  have hep : Tendsto (fun N => p N (e N)) atTop lp := by
    rw [show (fun N => p N (e N)) =
      Function.extend t (fun j => p (t j) (c j)) (fun N => p N (b N)) from
      apply_extend_sizes t ht c b p]
    exact tendsto_extend_sizes t ht _ _ ((hp.comp hns).comp hms.tendsto_atTop) hbp
  have heq : Tendsto (fun N => q N (e N)) atTop lq := by
    rw [show (fun N => q N (e N)) =
      Function.extend t (fun j => q (t j) (c j)) (fun N => q N (b N)) from
      apply_extend_sizes t ht c b q]
    exact tendsto_extend_sizes t ht _ _ ((hq.comp hns).comp hms.tendsto_atTop) hbq
  refine ⟨ms, ?_⟩
  have he := (h e hep heq).comp ((hn.comp hns).comp hms.tendsto_atTop)
  change Tendsto (fun j => f (t j) (e (t j))) atTop lf at he
  simpa only [e, ht.extend_apply, t, c] using he

end Riesz2
