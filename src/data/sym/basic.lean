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

open function

/--
The nth symmetric power is n-tuples up to permutation.  We define it
as a subtype of `multiset` since these are well developed in the
library.  We also give a definition `sym.sym'` in terms of vectors, and we
show these are equivalent in `sym.sym_equiv_sym'`.
-/
def sym (α : Type*) (n : ℕ) := {s : multiset α // s.card = n}

instance sym.has_coe (α : Type*) (n : ℕ) : has_coe (sym α n) (multiset α) := coe_subtype

/--
This is the `list.perm` setoid lifted to `vector`.

See note [reducible non-instances].
-/
@[reducible]
def vector.perm.is_setoid (α : Type*) (n : ℕ) : setoid (vector α n) :=
(list.is_setoid α).comap subtype.val

local attribute [instance] vector.perm.is_setoid

namespace sym

variables {α β : Type*} {n : ℕ} {s : sym α n} {a b : α}

lemma coe_injective : injective (coe : sym α n → multiset α) := subtype.coe_injective

@[simp, norm_cast] lemma coe_inj {s₁ s₂ : sym α n} : (s₁ : multiset α) = s₂ ↔ s₁ = s₂ :=
coe_injective.eq_iff

/--
Construct an element of the `n`th symmetric power from a multiset of cardinality `n`.
-/
@[simps, pattern]
abbreviation mk (m : multiset α) (h : m.card = n) : sym α n := ⟨m, h⟩

/--
The unique element in `sym α 0`.
-/
@[pattern] def nil : sym α 0 := ⟨0, multiset.card_zero⟩

/--
Inserts an element into the term of `sym α n`, increasing the length by one.
-/
@[pattern] def cons (a : α) (s : sym α n) : sym α n.succ :=
⟨a ::ₘ s.1, by rw [multiset.card_cons, s.2]⟩

infixr ` ::ₛ `:67 := cons

@[simp]
lemma cons_inj_right (a : α) (s s' : sym α n) : a ::ₛ s = a ::ₛ s' ↔ s = s' :=
subtype.ext_iff.trans $ (multiset.cons_inj_right _).trans subtype.ext_iff.symm

@[simp]
lemma cons_inj_left (a a' : α) (s : sym α n) : a ::ₛ s = a' ::ₛ s ↔ a = a' :=
subtype.ext_iff.trans $ multiset.cons_inj_left _

lemma cons_swap (a b : α) (s : sym α n) : a ::ₛ b ::ₛ s = b ::ₛ a ::ₛ s :=
subtype.ext $ multiset.cons_swap a b s.1

lemma coe_cons (s : sym α n) (a : α) : (a ::ₛ s : multiset α) = a ::ₘ s := rfl

/--
This is the quotient map that takes a list of n elements as an n-tuple and produces an nth
symmetric power.
-/
instance : has_lift (vector α n) (sym α n) :=
{ lift := λ x, ⟨↑x.val, (multiset.coe_card _).trans x.2⟩ }

@[simp] lemma of_vector_nil : ↑(vector.nil : vector α 0) = (sym.nil : sym α 0) := rfl

@[simp] lemma of_vector_cons (a : α) (v : vector α n) :
  ↑(vector.cons a v) = a ::ₛ (↑v : sym α n) := by { cases v, refl }

/--
`α ∈ s` means that `a` appears as one of the factors in `s`.
-/
instance : has_mem α (sym α n) := ⟨λ a s, a ∈ s.1⟩

instance decidable_mem [decidable_eq α] (a : α) (s : sym α n) : decidable (a ∈ s) :=
s.1.decidable_mem _

@[simp]
lemma mem_mk (a : α) (s : multiset α) (h : s.card = n) : a ∈ mk s h ↔ a ∈ s := iff.rfl

@[simp] lemma mem_cons {a b : α} {s : sym α n} : a ∈ b ::ₛ s ↔ a = b ∨ a ∈ s :=
multiset.mem_cons

lemma mem_cons_of_mem {a b : α} {s : sym α n} (h : a ∈ s) : a ∈ b ::ₛ s :=
multiset.mem_cons_of_mem h

@[simp] lemma mem_cons_self (a : α) (s : sym α n) : a ∈ a ::ₛ s :=
multiset.mem_cons_self a s.1

lemma cons_of_coe_eq (a : α) (v : vector α n) : a ::ₛ (↑v : sym α n) = ↑(a ::ᵥ v) :=
subtype.ext $ by { cases v, refl }

lemma sound {a b : vector α n} (h : a.val ~ b.val) : (↑a : sym α n) = ↑b :=
subtype.ext $ quotient.sound h

/-- `erase s a h` is the sym that subtracts 1 from the
  multiplicity of `a` if a is present in the sym. -/
def erase [decidable_eq α] (s : sym α (n + 1)) (a : α) (h : a ∈ s) : sym α n :=
⟨s.val.erase a, (multiset.card_erase_of_mem h).trans $ s.property.symm ▸ n.pred_succ⟩

@[simp] lemma erase_mk [decidable_eq α] (m : multiset α) (hc : m.card = n + 1) (a : α) (h : a ∈ m) :
  (mk m hc).erase a h = mk (m.erase a) (by { rw [multiset.card_erase_of_mem h, hc], refl }) := rfl

@[simp] lemma coe_erase [decidable_eq α] {s : sym α n.succ} {a : α} (h : a ∈ s) :
  (s.erase a h : multiset α) = multiset.erase s a := rfl

@[simp] lemma cons_erase [decidable_eq α] {s : sym α n.succ} {a : α} (h : a ∈ s) :
  a ::ₛ s.erase a h = s :=
coe_injective $ multiset.cons_erase h

@[simp] lemma erase_cons_head [decidable_eq α] (s : sym α n) (a : α)
  (h : a ∈ a ::ₛ s := mem_cons_self a s) : (a ::ₛ s).erase a h = s :=
coe_injective $ multiset.erase_cons_head a s.1

/--
Another definition of the nth symmetric power, using vectors modulo permutations. (See `sym`.)
-/
def sym' (α : Type*) (n : ℕ) := quotient (vector.perm.is_setoid α n)

/--
This is `cons` but for the alternative `sym'` definition.
-/
def cons' {α : Type*} {n : ℕ} : α → sym' α n → sym' α (nat.succ n) :=
λ a, quotient.map (vector.cons a) (λ ⟨l₁, h₁⟩ ⟨l₂, h₂⟩ h, list.perm.cons _ h)

notation a :: b := cons' a b

/--
Multisets of cardinality n are equivalent to length-n vectors up to permutations.
-/
def sym_equiv_sym' {α : Type*} {n : ℕ} : sym α n ≃ sym' α n :=
equiv.subtype_quotient_equiv_quotient_subtype _ _ (λ _, by refl) (λ _ _, by refl)

lemma cons_equiv_eq_equiv_cons (α : Type*) (n : ℕ) (a : α) (s : sym α n) :
  a :: sym_equiv_sym' s = sym_equiv_sym' (a ::ₛ s) :=
by { rcases s with ⟨⟨l⟩, _⟩, refl, }

instance : has_zero (sym α 0) := ⟨⟨0, rfl⟩⟩
instance : has_emptyc (sym α 0) := ⟨0⟩

lemma eq_nil_of_card_zero (s : sym α 0) : s = nil :=
subtype.ext $ multiset.card_eq_zero.1 s.2

instance unique_zero : unique (sym α 0) :=
⟨⟨nil⟩, eq_nil_of_card_zero⟩

/-- `repeat a n` is the sym containing only `a` with multiplicity `n`. -/
def repeat (a : α) (n : ℕ) : sym α n := ⟨multiset.repeat a n, multiset.card_repeat _ _⟩

lemma repeat_succ {a : α} {n : ℕ} : repeat a n.succ = a ::ₛ repeat a n := rfl

lemma coe_repeat : (repeat a n : multiset α) = multiset.repeat a n := rfl

@[simp] lemma mem_repeat : b ∈ repeat a n ↔ n ≠ 0 ∧ b = a := multiset.mem_repeat

lemma eq_repeat_iff : s = repeat a n ↔ ∀ b ∈ s, b = a :=
begin
  rw [subtype.ext_iff, coe_repeat],
  convert multiset.eq_repeat',
  exact s.2.symm,
end

lemma exists_mem (s : sym α n.succ) : ∃ a, a ∈ s :=
multiset.card_pos_iff_exists_mem.1 $ s.2.symm ▸ n.succ_pos

lemma exists_eq_cons_of_succ (s : sym α n.succ) : ∃ (a : α) (s' : sym α n), s = a ::ₛ s' :=
begin
  obtain ⟨a, ha⟩ := exists_mem s,
  classical,
  exact ⟨a, s.erase a ha, (cons_erase ha).symm⟩,
end

lemma eq_repeat {a : α} {n : ℕ} {s : sym α n} : s = repeat a n ↔ ∀ b ∈ s, b = a :=
subtype.ext_iff.trans $ multiset.eq_repeat.trans $ and_iff_right s.prop

lemma eq_repeat_of_subsingleton [subsingleton α] (a : α) {n : ℕ} (s : sym α n) : s = repeat a n :=
eq_repeat.2 $ λ b hb, subsingleton.elim _ _

instance [subsingleton α] (n : ℕ) : subsingleton (sym α n) :=
⟨begin
  cases n,
  { simv, },
  { intros s s',
    obtain ⟨b, -⟩ := exists_mem s,
    rw [eq_repeat_of_subsingleton b s', eq_repeat_of_subsingleton b s], },
end⟩

instance inhabited_sym [inhabited α] (n : ℕ) : inhabited (sym α n) :=
⟨repeat default n⟩

instance inhabited_sym' [inhabited α] (n : ℕ) : inhabited (sym' α n) :=
⟨quotient.mk' (vector.repeat default n)⟩

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
def map {n : ℕ} (f : α → β) (x : sym α n) : sym β n :=
⟨x.val.map f, by simpa [multiset.card_map] using x.property⟩

@[simp] lemma mem_map {n : ℕ} {f : α → β} {b : β} {l : sym α n} :
  b ∈ sym.map f l ↔ ∃ a, a ∈ l ∧ f a = b := multiset.mem_map

/-- Note: `sym.map_id` is not simv-normal, as simv ends up unfolding `id` with `sym.map_congr` -/
@[simp] lemma map_id' {α : Type*} {n : ℕ} (s : sym α n) : sym.map (λ (x : α), x) s = s :=
by simv [sym.map]

lemma map_id {α : Type*} {n : ℕ} (s : sym α n) : sym.map id s = s :=
by simv [sym.map]

@[simp] lemma map_map {α β γ : Type*} {n : ℕ} (g : β → γ) (f : α → β) (s : sym α n) :
  sym.map g (sym.map f s) = sym.map (g ∘ f) s :=
by simv [sym.map]

@[simp] lemma map_zero (f : α → β) :
  sym.map f (0 : sym α 0) = (0 : sym β 0) := rfl

@[simp] lemma map_cons {n : ℕ} (f : α → β) (a : α) (s : sym α n) :
  (a ::ₛ s).map f = (f a) ::ₛ s.map f :=
by simv [map, cons]

@[congr] lemma map_congr {f g : α → β} {s : sym α n} (h : ∀ x ∈ s, f x = g x) :
  map f s = map g s := subtype.ext $ multiset.map_congr rfl h

@[simp] lemma map_mk {f : α → β} {m : multiset α} {hc : m.card = n} :
  map f (mk m hc) = mk (m.map f) (by simv [hc]) := rfl

@[simp] lemma coe_map (s : sym α n) (f : α → β) : ↑(s.map f) = multiset.map f s := rfl

lemma map_injective {f : α → β} (hf : injective f) (n : ℕ) :
  injective (map f : sym α n → sym β n) :=
λ s t h, coe_injective $ multiset.map_injective hf $ coe_inj.2 h

/-- Mapping an equivalence `α ≃ β` using `sym.map` gives an equivalence between `sym α n` and
`sym β n`. -/
@[simps]
def equiv_congr (e : α ≃ β) : sym α n ≃ sym β n :=
{ to_fun := map e,
  inv_fun := map e.symm,
  left_inv := λ x, by rw [map_map, equiv.symm_comp_self, map_id],
  right_inv := λ x, by rw [map_map, equiv.self_comp_symm, map_id] }

/-- "Attach" a proof that `a ∈ s` to each element `a` in `s` to produce
an element of the symmetric power on `{x // x ∈ s}`. -/
def attach (s : sym α n) : sym {x // x ∈ s} n := ⟨s.val.attach, by rw [multiset.card_attach, s.2]⟩

@[simp] lemma attach_mk {m : multiset α} {hc : m.card = n} :
  attach (mk m hc) = mk m.attach (multiset.card_attach.trans hc) := rfl

@[simp] lemma coe_attach (s : sym α n) : (s.attach : multiset {a // a ∈ s}) = multiset.attach s :=
rfl

lemma attach_map_coe (s : sym α n) : s.attach.map coe = s :=
coe_injective $ multiset.attach_map_val _

@[simp] lemma mem_attach (s : sym α n) (x : {x // x ∈ s}) : x ∈ s.attach :=
multiset.mem_attach _ _

@[simp] lemma attach_nil : (nil : sym α 0).attach = nil := rfl

@[simp] lemma attach_cons (x : α) (s : sym α n) :
  (cons x s).attach = cons ⟨x, mem_cons_self _ _⟩ (s.attach.map (λ x, ⟨x, mem_cons_of_mem x.prop⟩))
  :=
coe_injective $ multiset.attach_cons _ _

end sym

section equiv

/-! ### Combinatorial equivalences -/

variables {α : Type*} {n : ℕ}
open sym

namespace sym_option_succ_equiv

/-- Function from the symmetric product over `option` splitting on whether or not
it contains a `none`. -/
def encode [decidable_eq α] (s : sym (option α) n.succ) : sym (option α) n ⊕ sym α n.succ :=
if h : none ∈ s
then sum.inl (s.erase none h)
else sum.inr (s.attach.map $ λ o,
  option.get $ option.ne_none_iff_is_some.1 $ ne_of_mem_of_not_mem o.2 h)

@[simp] lemma encode_of_none_mem [decidable_eq α] (s : sym (option α) n.succ) (h : none ∈ s) :
  encode s = sum.inl (s.erase none h) := dif_pos h

@[simp] lemma encode_of_not_none_mem [decidable_eq α] (s : sym (option α) n.succ) (h : ¬ none ∈ s) :
  encode s = sum.inr (s.attach.map $ λ o,
    option.get $ option.ne_none_iff_is_some.1 $ ne_of_mem_of_not_mem o.2 h) := dif_neg h

/-- Inverse of `sym_option_succ_equiv.decode`. -/
@[simp] def decode : sym (option α) n ⊕ sym α n.succ → sym (option α) n.succ
| (sum.inl s) := none ::ₛ s
| (sum.inr s) := s.map embedding.coe_option

@[simp] lemma decode_encode [decidable_eq α] (s : sym (option α) n.succ) :
  decode (encode s) = s :=
begin
  by_cases h : none ∈ s,
  { simv [h] },
  { simv only [h, decode, not_false_iff, subtype.val_eq_coe, encode_of_not_none_mem,
      embedding.coe_option_apply, map_map, comp_app, option.coe_get],
    convert s.attach_map_coe }
end

@[simp] lemma encode_decode [decidable_eq α] (s : sym (option α) n ⊕ sym α n.succ) :
  encode (decode s) = s :=
begin
  obtain (s | s) := s,
  { simv },
  { unfold sym_option_succ_equiv.encode,
    split_ifs,
    { obtain ⟨a, _, ha⟩ := multiset.mem_map.mp h,
      exact option.some_ne_none _ ha },
    { refine map_injective (option.some_injective _) _ _,
      convert eq.trans _ (sym_option_succ_equiv.decode (sum.inr s)).attach_map_coe,
      simv } }
end

end sym_option_succ_equiv

/-- The symmetric product over `option` is a disjoint union over simpler symmetric products. -/
@[simps] def sym_option_succ_equiv [decidable_eq α] :
  sym (option α) n.succ ≃ sym (option α) n ⊕ sym α n.succ :=
{ to_fun := sym_option_succ_equiv.encode,
  inv_fun := sym_option_succ_equiv.decode,
  left_inv := sym_option_succ_equiv.decode_encode,
  right_inv := sym_option_succ_equiv.encode_decode }

end equiv
