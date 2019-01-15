/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro

A type for VM-erased data.
-/

import data.set.basic data.equiv.basic

/-- `erased α` is the same as `α`, except that the elements
  of `erased α` are erased in the VM in the same way as types
  and proofs. This can be used to track data without storing it
  literally. -/
def erased (α : Sort*) : Sort* :=
Σ' s : α → Prop, ∃ a, (λ b, a = b) = s

namespace erased

@[inline] def mk {α} (a : α) : erased α := ⟨λ b, a = b, a, rfl⟩

noncomputable def out {α} : erased α → α
| ⟨s, h⟩ := classical.some h

@[reducible] def out_type (a : erased Sort*) : Sort* := out a

theorem out_proof {p : Prop} (a : erased p) : p := out a

@[simp] theorem out_mk {α} (a : α) : (mk a).out = a :=
begin
  let h, show classical.some h = a,
  have := classical.some_spec h,
  exact cast (congr_fun this a).symm rfl
end

@[simp] theorem mk_out {α} : ∀ (a : erased α), mk (out a) = a
| ⟨s, h⟩ := by simp [mk]; congr; exact classical.some_spec h

noncomputable def equiv (α) : erased α ≃ α :=
⟨out, mk, mk_out, out_mk⟩

instance (α : Type*) : has_repr (erased α) := ⟨λ _, "erased"⟩

def choice {α} (h : nonempty α) : erased α := mk (classical.choice h)

theorem nonempty_iff {α} : nonempty (erased α) ↔ nonempty α :=
⟨λ ⟨a⟩, ⟨a.out⟩, λ ⟨a⟩, ⟨mk a⟩⟩

instance {α} [h : nonempty α] : nonempty (erased α) :=
erased.nonempty_iff.2 h

instance {α} [h : inhabited α] : inhabited (erased α) :=
⟨mk (default _)⟩

def bind {α β} (a : erased α) (f : α → erased β) : erased β :=
⟨λ b, (f a.out).1 b, (f a.out).2⟩

@[simp] theorem bind_eq_out {α β} (a f) : @bind α β a f = f a.out :=
by delta bind bind._proof_1; cases f a.out; refl

def join {α} (a : erased (erased α)) : erased α := bind a id

@[simp] theorem join_eq_out {α} (a) : @join α a = a.out := bind_eq_out _ _

instance : monad erased := { pure := @mk, bind := @bind }

instance : is_lawful_monad erased := by refine {..}; intros; simp

end erased
