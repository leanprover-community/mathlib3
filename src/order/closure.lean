/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Bhavik Mehta
-/
import order.basic
import order.preorder_hom
import tactic.monotonicity

/-!
# Closure operators on a partial order

We define (bundled) closure operators on a partial order as an monotone (increasing), extensive
(inflationary) and idempotent function.
We define closed elements for the operator as elements which are fixed by it.

## References

* https://en.wikipedia.org/wiki/Closure_operator#Closure_operators_on_partially_ordered_sets

-/
universe u

variables (α : Type u) [partial_order α]

/--
A closure operator on the partial order `α` is a monotone function which is extensive (every x
is less than its closure) and idempotent.
-/
@[ext]
structure closure_operator extends α →ₘ α :=
(le_closure' : ∀ x, x ≤ to_fun x)
(idempotent' : ∀ x, to_fun (to_fun x) = to_fun x)

instance : has_coe_to_fun (closure_operator α) :=
{ F := _, coe := λ c, c.to_fun }

initialize_simps_projections closure_operator (to_fun → apply)

namespace closure_operator

/-- The identity function as a closure operator. -/
@[simps]
def id : closure_operator α :=
{ to_fun := λ x, x,
  monotone' := λ _ _ h, h,
  le_closure' := λ _, le_refl _,
  idempotent' := λ _, rfl }

instance : inhabited (closure_operator α) := ⟨id α⟩

variables {α} (c : closure_operator α)

@[mono] lemma monotone : monotone c := c.monotone'
/--
Every element is less than its closure. This property is sometimes referred to as extensivity or
inflationary.
-/
lemma le_closure (x : α) : x ≤ c x := c.le_closure' x
@[simp] lemma idempotent (x : α) : c (c x) = c x := c.idempotent' x

lemma le_closure_iff (x y : α) : x ≤ c y ↔ c x ≤ c y :=
⟨λ h, c.idempotent y ▸ c.monotone h, λ h, le_trans (c.le_closure x) h⟩

lemma closure_top {α : Type u} [order_top α] (c : closure_operator α) : c ⊤ = ⊤ :=
le_antisymm le_top (c.le_closure _)

lemma closure_inter_le {α : Type u} [semilattice_inf α] (c : closure_operator α) (x y : α) :
  c (x ⊓ y) ≤ c x ⊓ c y :=
le_inf (c.monotone inf_le_left) (c.monotone inf_le_right)

lemma closure_union_closure_le {α : Type u} [semilattice_sup α] (c : closure_operator α) (x y : α) :
  c x ⊔ c y ≤ c (x ⊔ y) :=
sup_le (c.monotone le_sup_left) (c.monotone le_sup_right)

/-- An element `x` is closed for the closure operator `c` if it is a fixed point for it. -/
def is_closed (x : α) : Prop := c x = x

lemma is_closed_iff (x : α) : c.is_closed x ↔ c x = x := iff.rfl

lemma top_is_closed {α : Type u} [order_top α] (c : closure_operator α) : c.is_closed ⊤ :=
c.closure_top

end closure_operator
