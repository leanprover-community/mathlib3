/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import data.set.lattice
import tactic.wlog

/-!
# Relations holding pairwise

This file defines pairwise relations.

## Main declarations

* `pairwise p`: States that `p i j` for all `i ≠ j`.

-/
open set

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}
  {s t u : set α}

/-- A relation `p` holds pairwise if `p i j` for all `i ≠ j`. -/
def pairwise {α : Type*} (p : α → α → Prop) := ∀ i j, i ≠ j → p i j

theorem set.pairwise_on_univ {r : α → α → Prop} :
  (univ : set α).pairwise_on r ↔ pairwise r :=
by simp only [pairwise_on, pairwise, mem_univ, forall_const]

theorem set.pairwise_on.on_injective {s : set α} {r : α → α → Prop} (hs : pairwise_on s r)
  {f : β → α} (hf : function.injective f) (hfs : ∀ x, f x ∈ s) :
  pairwise (r on f) :=
λ i j hij, hs _ (hfs i) _ (hfs j) (hf.ne hij)

theorem pairwise.mono {p q : α → α → Prop} (h : ∀ ⦃i j⦄, p i j → q i j) (hp : pairwise p) :
  pairwise q :=
λ i j hij, h (hp i j hij)

theorem pairwise_on_bool {r} (hr : symmetric r) {a b : α} :
  pairwise (r on (λ c, cond c a b)) ↔ r a b :=
by simpa [pairwise, function.on_fun] using @hr a b

theorem pairwise_disjoint_on_bool [semilattice_inf_bot α] {a b : α} :
  pairwise (disjoint on (λ c, cond c a b)) ↔ disjoint a b :=
pairwise_on_bool disjoint.symm

theorem pairwise_on_nat {r} (hr : symmetric r) (f : ℕ → α) :
  pairwise (r on f) ↔ ∀ (m n) (h : m < n), r (f m) (f n) :=
⟨λ p m n w, p m n w.ne, λ p m n w, by { wlog w' : m ≤ n, exact p m n ((ne.le_iff_lt w).mp w'), }⟩

theorem pairwise_disjoint_on_nat [semilattice_inf_bot α] (f : ℕ → α) :
  pairwise (disjoint on f) ↔ ∀ (m n) (h : m < n), disjoint (f m) (f n) :=
pairwise_on_nat disjoint.symm f

theorem pairwise.pairwise_on {p : α → α → Prop} (h : pairwise p) (s : set α) : s.pairwise_on p :=
λ x hx y hy, h x y

theorem pairwise_disjoint_fiber (f : α → β) : pairwise (disjoint on (λ y : β, f ⁻¹' {y})) :=
set.pairwise_on_univ.1 $ pairwise_on_disjoint_fiber f univ

lemma pairwise_disjoint_on_inter {f : β → set α} {a : set α}
  (hf : pairwise (disjoint on f)) : pairwise (disjoint on (λ n, a ∩ f n)) :=
hf.mono $ λ i j, disjoint.mono inf_le_right inf_le_right
