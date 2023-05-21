/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.list.basic

/-!
# Boolean quantifiers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This proves a few properties about `list.all` and `list.any`, which are the `bool` universal and
existential quantifiers. Their definitions are in core Lean.
-/

variables {α : Type*} {p : α → Prop} [decidable_pred p] {l : list α} {a : α}

namespace list

@[simp] theorem all_nil (p : α → bool) : all [] p = tt := rfl

@[simp] theorem all_cons (p : α → bool) (a : α) (l : list α) : all (a::l) p = (p a && all l p) :=
rfl

theorem all_iff_forall {p : α → bool} : all l p ↔ ∀ a ∈ l, p a :=
begin
  induction l with a l ih,
  { exact iff_of_true rfl (forall_mem_nil _) },
  simp only [all_cons, band_coe_iff, ih, forall_mem_cons]
end

theorem all_iff_forall_prop : all l (λ a, p a) ↔ ∀ a ∈ l, p a :=
by simp only [all_iff_forall, bool.of_to_bool_iff]

@[simp] theorem any_nil (p : α → bool) : any [] p = ff := rfl

@[simp] theorem any_cons (p : α → bool) (a : α) (l : list α) : any (a :: l) p = (p a || any l p) :=
rfl

theorem any_iff_exists {p : α → bool} : any l p ↔ ∃ a ∈ l, p a :=
begin
  induction l with a l ih,
  { exact iff_of_false bool.not_ff (not_exists_mem_nil _) },
  simp only [any_cons, bor_coe_iff, ih, exists_mem_cons_iff]
end

theorem any_iff_exists_prop : any l (λ a, p a) ↔ ∃ a ∈ l, p a := by simp [any_iff_exists]

theorem any_of_mem {p : α → bool} (h₁ : a ∈ l) (h₂ : p a) : any l p := any_iff_exists.2 ⟨_, h₁, h₂⟩

end list
