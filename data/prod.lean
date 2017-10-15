/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Extends theory on products
-/

universes u v
variables {α : Type u} {β : Type v}

-- copied from parser
@[simp] lemma prod.mk.eta : ∀{p : α × β}, (p.1, p.2) = p
| (a, b) := rfl

def prod.swap : (α×β) → (β×α) := λp, (p.2, p.1)

@[simp] lemma prod.swap_swap : ∀x:α×β, prod.swap (prod.swap x) = x
| ⟨a, b⟩ := rfl

@[simp] lemma prod.fst_swap {p : α×β} : (prod.swap p).1 = p.2 := rfl

@[simp] lemma prod.snd_swap {p : α×β} : (prod.swap p).2 = p.1 := rfl

@[simp] lemma prod.swap_prod_mk {a : α} {b : β} : prod.swap (a, b) = (b, a) := rfl

@[simp] lemma prod.swap_swap_eq : prod.swap ∘ prod.swap = @id (α × β) :=
funext $ prod.swap_swap

@[simp] lemma prod.swap_left_inverse : function.left_inverse (@prod.swap α β) prod.swap :=
prod.swap_swap

@[simp] lemma prod.swap_right_inverse : function.right_inverse (@prod.swap α β) prod.swap :=
prod.swap_swap
