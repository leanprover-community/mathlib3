/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.equiv.basic

/-!
# A type for VM-erased data

This file defines a type `erased α` which is classically isomorphic to `α`,
but erased in the VM. That is, at runtime every value of `erased α` is
represented as `0`, just like types and proofs.
-/

universes u

/-- `erased α` is the same as `α`, except that the elements
  of `erased α` are erased in the VM in the same way as types
  and proofs. This can be used to track data without storing it
  literally. -/
def erased (α : Sort u) : Sort (max 1 u) :=
Σ' s : α → Prop, ∃ a, (λ b, a = b) = s

namespace erased

/-- Erase a value. -/
@[inline] def mk {α} (a : α) : erased α := ⟨λ b, a = b, a, rfl⟩

/-- Extracts the erased value, noncomputably. -/
noncomputable def out {α} : erased α → α
| ⟨s, h⟩ := classical.some h

/--
Extracts the erased value, if it is a type.

Note: `(mk a).out_type` is not definitionally equal to `a`.
-/
@[reducible] def out_type (a : erased (Sort u)) : Sort u := out a

/-- Extracts the erased value, if it is a proof. -/
theorem out_proof {p : Prop} (a : erased p) : p := out a

@[simp] theorem out_mk {α} (a : α) : (mk a).out = a :=
begin
  let h, show classical.some h = a,
  have := classical.some_spec h,
  exact cast (congr_fun this a).symm rfl
end

@[simp] theorem mk_out {α} : ∀ (a : erased α), mk (out a) = a
| ⟨s, h⟩ := by simp [mk]; congr; exact classical.some_spec h

@[ext] lemma out_inj {α} (a b : erased α) (h : a.out = b.out) : a = b :=
by simpa using congr_arg mk h

/-- Equivalence between `erased α` and `α`. -/
noncomputable def equiv (α) : erased α ≃ α :=
⟨out, mk, mk_out, out_mk⟩

instance (α : Type u) : has_repr (erased α) := ⟨λ _, "erased"⟩
instance (α : Type u) : has_to_string (erased α) := ⟨λ _, "erased"⟩
meta instance (α : Type u) : has_to_format (erased α) := ⟨λ _, ("erased" : format)⟩

/-- Computably produce an erased value from a proof of nonemptiness. -/
def choice {α} (h : nonempty α) : erased α := mk (classical.choice h)

@[simp] theorem nonempty_iff {α} : nonempty (erased α) ↔ nonempty α :=
⟨λ ⟨a⟩, ⟨a.out⟩, λ ⟨a⟩, ⟨mk a⟩⟩

instance {α} [h : nonempty α] : inhabited (erased α) :=
⟨choice h⟩

/--
`(>>=)` operation on `erased`.

This is a separate definition because `α` and `β` can live in different
universes (the universe is fixed in `monad`).
-/
def bind {α β} (a : erased α) (f : α → erased β) : erased β :=
⟨λ b, (f a.out).1 b, (f a.out).2⟩

@[simp] theorem bind_eq_out {α β} (a f) : @bind α β a f = f a.out :=
by delta bind bind._proof_1; cases f a.out; refl

/--
Collapses two levels of erasure.
-/
def join {α} (a : erased (erased α)) : erased α := bind a id

@[simp] theorem join_eq_out {α} (a) : @join α a = a.out := bind_eq_out _ _

/--
`(<$>)` operation on `erased`.

This is a separate definition because `α` and `β` can live in different
universes (the universe is fixed in `functor`).
-/
def map {α β} (f : α → β) (a : erased α) : erased β :=
bind a (mk ∘ f)

@[simp] theorem map_out {α β} {f : α → β} (a : erased α) : (a.map f).out = f a.out :=
by simp [map]

instance : monad erased := { pure := @mk, bind := @bind, map := @map }

@[simp] lemma pure_def {α} : (pure : α → erased α) = @mk _ := rfl
@[simp] lemma bind_def {α β} : ((>>=) : erased α → (α → erased β) → erased β) = @bind _ _ := rfl
@[simp] lemma map_def {α β} : ((<$>) : (α → β) → erased α → erased β) = @map _ _ := rfl

instance : is_lawful_monad erased := by refine {..}; intros; ext; simp

end erased
