/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import data.equiv.list

/-!
# W types

Given `α : Type` and `β : α → Type`, the W type determined by this data, `W_type β`, is the
inductively defined type of trees where the nodes are labeled by elements of `α` and the children of
a node labeled `a` are indexed by elements of `β a`.

This file is currently a stub, awaiting a full development of the theory. Currently, the main result
is that if `α` is an encodable fintype and `β a` is encodable for every `a : α`, then `W_type β` is
encodable. This can be used to show the encodability of other inductive types, such as those that
are commonly used to formalize syntax, e.g. terms and expressions in a given language. The strategy
is illustrated in the example found in the file `prop_encodable` in the `archive/examples` folder of
mathlib.

## Implementation details

While the name `W_type` is somewhat verbose, it is preferable to putting a single character
identifier `W` in the root namespace.
-/

/--
Given `β : α → Type*`, `W_type β` is the type of finitely branching trees where nodes are labeled by
elements of `α` and the children of a node labeled `a` are indexed by elements of `β a`.
-/
inductive W_type {α : Type*} (β : α → Type*)
| mk (a : α) (f : β a → W_type) : W_type

instance : inhabited (W_type (λ (_ : unit), empty)) :=
⟨W_type.mk unit.star empty.elim⟩

namespace W_type

variables {α : Type*} {β : α → Type*} [Π a : α, fintype (β a)]

/-- The depth of a finitely branching tree. -/
def depth : W_type β → ℕ
| ⟨a, f⟩ := finset.sup finset.univ (λ n, depth (f n)) + 1

lemma depth_pos (t : W_type β) : 0 < t.depth :=
by { cases t, apply nat.succ_pos }

lemma depth_lt_depth_mk (a : α) (f : β a → W_type β) (i : β a) :
  depth (f i) < depth ⟨a, f⟩ :=
nat.lt_succ_of_le (finset.le_sup (finset.mem_univ i))

end W_type

/-
Show that W types are encodable when `α` is an encodable fintype and for every `a : α`, `β a` is
encodable.

We define an auxiliary type `W_type' β n` of trees of depth at most `n`, and then we show by
induction on `n` that these are all encodable. These auxiliary constructions are not interesting in
and of themselves, so we mark them as `private`.
-/

namespace encodable

@[reducible] private def W_type' {α : Type*} (β : α → Type*)
    [Π a : α, fintype (β a)] [Π a : α, encodable (β a)] (n : ℕ) :=
{ t : W_type β // t.depth ≤ n}

variables {α : Type*} {β : α → Type*} [Π a : α, fintype (β a)] [Π a : α, encodable (β a)]

private def encodable_zero : encodable (W_type' β 0) :=
let f    : W_type' β 0 → empty := λ ⟨x, h⟩, false.elim $ not_lt_of_ge h (W_type.depth_pos _),
    finv : empty → W_type' β 0 := by { intro x, cases x} in
have ∀ x, finv (f x) = x, from λ ⟨x, h⟩, false.elim $ not_lt_of_ge h (W_type.depth_pos _),
encodable.of_left_inverse f finv this

private def f (n : ℕ) : W_type' β (n + 1) → Σ a : α, β a → W_type' β n
| ⟨t, h⟩ :=
  begin
    cases t with a f,
    have h₀ : ∀ i : β a, W_type.depth (f i) ≤ n,
      from λ i, nat.le_of_lt_succ (lt_of_lt_of_le (W_type.depth_lt_depth_mk a f i) h),
    exact ⟨a, λ i : β a, ⟨f i, h₀ i⟩⟩
  end

private def finv (n : ℕ) :
  (Σ a : α, β a → W_type' β n) → W_type' β (n + 1)
| ⟨a, f⟩ :=
  let f' := λ i : β a, (f i).val in
  have W_type.depth ⟨a, f'⟩ ≤ n + 1,
    from add_le_add_right (finset.sup_le (λ b h, (f b).2)) 1,
  ⟨⟨a, f'⟩, this⟩

variables [encodable α]

private def encodable_succ (n : nat) (h : encodable (W_type' β n)) :
  encodable (W_type' β (n + 1)) :=
encodable.of_left_inverse (f n) (finv n) (by { rintro ⟨⟨_, _⟩, _⟩, refl })

/-- `W_type` is encodable when `α` is an encodable fintype and for every `a : α`, `β a` is
encodable. -/
instance : encodable (W_type β) :=
begin
  haveI h' : Π n, encodable (W_type' β n) :=
    λ n, nat.rec_on n encodable_zero encodable_succ,
  let f    : W_type β → Σ n, W_type' β n   := λ t, ⟨t.depth, ⟨t, le_refl _⟩⟩,
  let finv : (Σ n, W_type' β n) → W_type β := λ p, p.2.1,
  have : ∀ t, finv (f t) = t, from λ t, rfl,
  exact encodable.of_left_inverse f finv this
end

end encodable
