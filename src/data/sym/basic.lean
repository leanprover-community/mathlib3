/-
Copyright (c) 2020 Kyle Miller All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/

import data.multiset.basic
import data.vector.basic
import data.setoid.basic
import tactic.apply_fun

/-!
# Symmetric powers

This file defines symmetric powers of a type.  The nth symmetric power
consists of homogeneous n-tuples modulo permutations by the symmetric
group.

The special case of 2-tuples is called the symmetric square, which is
addressed in more detail in `data.sym.sym2`.

TODO: This was created as supporting material for `sym2`; it
needs a fleshed-out interface.

## Tags

symmetric powers

-/

universes u

/--
The nth symmetric power is n-tuples up to permutation.  We define it
as a subtype of `multiset` since these are well developed in the
library.  We also give a definition `sym.sym'` in terms of vectors, and we
show these are equivalent in `sym.sym_equiv_sym'`.
-/
def sym (α : Type u) (n : ℕ) := {s : multiset α // s.card = n}

/--
This is the `list.perm` setoid lifted to `vector`.

See note [reducible non-instances].
-/
@[reducible]
def vector.perm.is_setoid (α : Type u) (n : ℕ) : setoid (vector α n) :=
(list.is_setoid α).comap subtype.val

local attribute [instance] vector.perm.is_setoid

namespace sym

variables {α : Type u} {n : ℕ}

/--
The unique element in `sym α 0`.
-/
@[pattern] def nil : sym α 0 := ⟨0, multiset.card_zero⟩

/--
Inserts an element into the term of `sym α n`, increasing the length by one.
-/
@[pattern] def cons (a : α) (s : sym α n) : sym α (nat.succ n) :=
⟨a ::ₘ s.1, by rw [multiset.card_cons, s.2]⟩

notation a :: b := cons a b

@[simp]
lemma cons_inj_right (a : α) (s s' : sym α n) : a :: s = a :: s' ↔ s = s' :=
subtype.ext_iff.trans $ (multiset.cons_inj_right _).trans subtype.ext_iff.symm

@[simp]
lemma cons_inj_left (a a' : α) (s : sym α n) : a :: s = a' :: s ↔ a = a' :=
subtype.ext_iff.trans $ multiset.cons_inj_left _

lemma cons_swap (a b : α) (s : sym α n) : a :: b :: s = b :: a :: s :=
subtype.ext $ multiset.cons_swap a b s.1

/--
This is the quotient map that takes a list of n elements as an n-tuple and produces an nth
symmetric power.
-/
instance : has_lift (vector α n) (sym α n) :=
{ lift := λ x, ⟨↑x.val, (multiset.coe_card _).trans x.2⟩ }

@[simp] lemma of_vector_nil : ↑(vector.nil : vector α 0) = (sym.nil : sym α 0) := rfl

@[simp] lemma of_vector_cons (a : α) (v : vector α n) :
  ↑(vector.cons a v) = a :: (↑v : sym α n) := by { cases v, refl }

/--
`α ∈ s` means that `a` appears as one of the factors in `s`.
-/
instance : has_mem α (sym α n) := ⟨λ a s, a ∈ s.1⟩

instance decidable_mem [decidable_eq α] (a : α) (s : sym α n) : decidable (a ∈ s) :=
s.1.decidable_mem _

@[simp] lemma mem_cons {a b : α} {s : sym α n} : a ∈ b :: s ↔ a = b ∨ a ∈ s :=
multiset.mem_cons

lemma mem_cons_of_mem {a b : α} {s : sym α n} (h : a ∈ s) : a ∈ b :: s :=
multiset.mem_cons_of_mem h

@[simp] lemma mem_cons_self (a : α) (s : sym α n) : a ∈ a :: s :=
multiset.mem_cons_self a s.1

lemma cons_of_coe_eq (a : α) (v : vector α n) : a :: (↑v : sym α n) = ↑(a ::ᵥ v) :=
subtype.ext $ by { cases v, refl }

lemma sound {a b : vector α n} (h : a.val ~ b.val) : (↑a : sym α n) = ↑b :=
subtype.ext $ quotient.sound h

/-- `erase s a h` is the sym that subtracts 1 from the
  multiplicity of `a` if a is present in the sym. -/
def erase [decidable_eq α] (s : sym α (n + 1)) (a : α) (h : a ∈ s) : sym α n :=
⟨s.val.erase a, (multiset.card_erase_of_mem h).trans $ s.property.symm ▸ n.pred_succ⟩

@[simp] lemma cons_erase [decidable_eq α] (s : sym α (n + 1)) (a : α) (h : a ∈ s) :
  a :: s.erase a h = s := subtype.ext $ multiset.cons_erase h

/--
Another definition of the nth symmetric power, using vectors modulo permutations. (See `sym`.)
-/
def sym' (α : Type u) (n : ℕ) := quotient (vector.perm.is_setoid α n)

/--
This is `cons` but for the alternative `sym'` definition.
-/
def cons' {α : Type u} {n : ℕ} : α → sym' α n → sym' α (nat.succ n) :=
λ a, quotient.map (vector.cons a) (λ ⟨l₁, h₁⟩ ⟨l₂, h₂⟩ h, list.perm.cons _ h)

notation a :: b := cons' a b

/--
Multisets of cardinality n are equivalent to length-n vectors up to permutations.
-/
def sym_equiv_sym' {α : Type u} {n : ℕ} : sym α n ≃ sym' α n :=
equiv.subtype_quotient_equiv_quotient_subtype _ _ (λ _, by refl) (λ _ _, by refl)

lemma cons_equiv_eq_equiv_cons (α : Type u) (n : ℕ) (a : α) (s : sym α n) :
  a :: sym_equiv_sym' s = sym_equiv_sym' (a :: s) :=
by { rcases s with ⟨⟨l⟩, _⟩, refl, }

instance : has_zero (sym α 0) := ⟨⟨0, rfl⟩⟩
instance : has_emptyc (sym α 0) := ⟨0⟩

lemma eq_nil_of_card_zero (s : sym α 0) : s = nil :=
subtype.ext $ multiset.card_eq_zero.1 s.2

instance unique_zero : unique (sym α 0) :=
⟨⟨nil⟩, eq_nil_of_card_zero⟩

/-- `repeat a n` is the sym containing only `a` with multiplicity `n`. -/
def repeat (a : α) (n : ℕ) : sym α n := ⟨multiset.repeat a n, multiset.card_repeat _ _⟩

lemma repeat_succ {a : α} {n : ℕ} : repeat a n.succ = a :: repeat a n := rfl

lemma exists_mem (s : sym α n.succ) : ∃ a, a ∈ s :=
multiset.card_pos_iff_exists_mem.1 $ s.2.symm ▸ n.succ_pos

lemma exists_eq_cons_of_succ (s : sym α n.succ) : ∃ (a : α) (s' : sym α n), s = a :: s' :=
begin
  obtain ⟨a, ha⟩ := exists_mem s,
  classical,
  exact ⟨a, s.erase a ha, (s.cons_erase _ _).symm⟩,
end

lemma eq_repeat {a : α} {n : ℕ} {s : sym α n} : s = repeat a n ↔ ∀ b ∈ s, b = a :=
subtype.ext_iff.trans $ multiset.eq_repeat.trans $ and_iff_right s.prop

lemma eq_repeat_of_subsingleton [subsingleton α] (a : α) {n : ℕ} (s : sym α n) : s = repeat a n :=
eq_repeat.2 $ λ b hb, subsingleton.elim _ _

instance [subsingleton α] (n : ℕ) : subsingleton (sym α n) :=
⟨begin
  cases n,
  { simp, },
  { intros s s',
    obtain ⟨b, -⟩ := exists_mem s,
    rw [eq_repeat_of_subsingleton b s', eq_repeat_of_subsingleton b s], },
end⟩

instance inhabited_sym [inhabited α] (n : ℕ) : inhabited (sym α n) :=
⟨repeat (default α) n⟩

instance inhabited_sym' [inhabited α] (n : ℕ) : inhabited (sym' α n) :=
⟨quotient.mk' (vector.repeat (default α) n)⟩

instance (n : ℕ) [is_empty α] : is_empty (sym α n.succ) :=
⟨λ s, by { obtain ⟨a, -⟩ := exists_mem s, exact is_empty_elim a }⟩

instance (n : ℕ) [unique α] : unique (sym α n) := unique.mk' _

lemma repeat_left_inj {a b : α} {n : ℕ} (h : n ≠ 0) : repeat a n = repeat b n ↔ a = b :=
subtype.ext_iff.trans (multiset.repeat_left_inj h)

lemma repeat_left_injective {n : ℕ} (h : n ≠ 0) : function.injective (λ x : α, repeat x n) :=
λ a b, (repeat_left_inj h).1

instance (n : ℕ) [nontrivial α] : nontrivial (sym α (n + 1)) :=
(repeat_left_injective n.succ_ne_zero).nontrivial

/-- A function `α → β` induces a function `sym α n → sym β n` by applying it to every element of
the underlying `n`-tuple. -/
def map {α β : Type*} {n : ℕ} (f : α → β) (x : sym α n) : sym β n :=
⟨x.val.map f, by simpa [multiset.card_map] using x.property⟩

@[simp] lemma mem_map {α β : Type*} {n : ℕ} {f : α → β} {b : β} {l : sym α n} :
  b ∈ sym.map f l ↔ ∃ a, a ∈ l ∧ f a = b := multiset.mem_map

@[simp] lemma map_id {α : Type*} {n : ℕ} (s : sym α n) : sym.map id s = s :=
by simp [sym.map, subtype.mk.inj_eq]

@[simp] lemma map_map {α β γ : Type*} {n : ℕ} (g : β → γ) (f : α → β) (s : sym α n) :
  sym.map g (sym.map f s) = sym.map (g ∘ f) s :=
by simp [sym.map, subtype.mk.inj_eq]

@[simp] lemma map_zero {α β : Type*} (f : α → β) :
  sym.map f (0 : sym α 0) = (0 : sym β 0) := rfl

@[simp] lemma map_cons {α β : Type*} {n : ℕ} (f : α → β) (a : α) (s : sym α n) :
  (a :: s).map f = (f a) :: s.map f :=
by { cases s, simp [map, cons] }

/-- Mapping an equivalence `α ≃ β` using `sym.map` gives an equivalence between `sym α n` and
`sym β n`. -/
@[simps]
def equiv_congr {β : Type u} (e : α ≃ β) : sym α n ≃ sym β n :=
{ to_fun := map e,
  inv_fun := map e.symm,
  left_inv := λ x, by rw [map_map, equiv.symm_comp_self, map_id],
  right_inv := λ x, by rw [map_map, equiv.self_comp_symm, map_id] }

end sym
