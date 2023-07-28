/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.finsupp.order
import data.dfinsupp.lex
import data.finsupp.to_dfinsupp

/-!
# Lexicographic order on finitely supported functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the lexicographic order on `finsupp`.
-/

variables {α N : Type*}

namespace finsupp

section N_has_zero
variables [has_zero N]

/-- `finsupp.lex r s` is the lexicographic relation on `α →₀ N`, where `α` is ordered by `r`,
and `N` is ordered by `s`.

The type synonym `lex (α →₀ N)` has an order given by `finsupp.lex (<) (<)`.
-/
protected def lex (r : α → α → Prop) (s : N → N → Prop) (x y : α →₀ N) : Prop :=
pi.lex r (λ _, s) x y

lemma _root_.pi.lex_eq_finsupp_lex {r : α → α → Prop} {s : N → N → Prop} (a b : α →₀ N) :
  pi.lex r (λ _, s) (a : α → N) (b : α → N) = finsupp.lex r s a b :=
rfl

lemma lex_def {r : α → α → Prop} {s : N → N → Prop} {a b : α →₀ N} :
  finsupp.lex r s a b ↔ ∃ j, (∀ d, r d j → a d = b d) ∧ s (a j) (b j) := iff.rfl

lemma lex_eq_inv_image_dfinsupp_lex (r : α → α → Prop) (s : N → N → Prop) :
  finsupp.lex r s = inv_image (dfinsupp.lex r $ λ a, s) to_dfinsupp := rfl

instance [has_lt α] [has_lt N] : has_lt (lex (α →₀ N)) :=
⟨λ f g, finsupp.lex (<) (<) (of_lex f) (of_lex g)⟩

lemma lex_lt_of_lt_of_preorder [preorder N] (r) [is_strict_order α r]
  {x y : α →₀ N} (hlt : x < y) : ∃ i, (∀ j, r j i → x j ≤ y j ∧ y j ≤ x j) ∧ x i < y i :=
dfinsupp.lex_lt_of_lt_of_preorder r (id hlt : x.to_dfinsupp < y.to_dfinsupp)

lemma lex_lt_of_lt [partial_order N] (r) [is_strict_order α r]
  {x y : α →₀ N} (hlt : x < y) : pi.lex r (λ i, (<)) x y :=
dfinsupp.lex_lt_of_lt r (id hlt : x.to_dfinsupp < y.to_dfinsupp)

instance lex.is_strict_order [linear_order α] [partial_order N] :
  is_strict_order (lex (α →₀ N)) (<) :=
let i : is_strict_order (lex (α → N)) (<) := pi.lex.is_strict_order in
{ irrefl := to_lex.surjective.forall.2 $ λ a, @irrefl _ _ i.to_is_irrefl a,
  trans := to_lex.surjective.forall₃.2 $ λ a b c, @trans _ _ i.to_is_trans a b c }

variables [linear_order α]

/-- The partial order on `finsupp`s obtained by the lexicographic ordering.
See `finsupp.lex.linear_order` for a proof that this partial order is in fact linear. -/
instance lex.partial_order [partial_order N] : partial_order (lex (α →₀ N)) :=
partial_order.lift (λ x, to_lex ⇑(of_lex x)) finsupp.coe_fn_injective--fun_like.coe_injective

/--  The linear order on `finsupp`s obtained by the lexicographic ordering. -/
instance lex.linear_order [linear_order N] : linear_order (lex (α →₀ N)) :=
{ ..lex.partial_order,
  ..linear_order.lift' (to_lex ∘ to_dfinsupp ∘ of_lex) finsupp_equiv_dfinsupp.injective }

variable [partial_order N]

lemma to_lex_monotone : monotone (@to_lex (α →₀ N)) :=
λ a b h, dfinsupp.to_lex_monotone (id h : ∀ i, of_lex (to_dfinsupp a) i ≤ of_lex (to_dfinsupp b) i)

lemma lt_of_forall_lt_of_lt (a b : lex (α →₀ N)) (i : α) :
  (∀ j < i, of_lex a j = of_lex b j) → of_lex a i < of_lex b i → a < b :=
λ h1 h2, ⟨i, h1, h2⟩

end N_has_zero

section covariants
variables [linear_order α] [add_monoid N] [linear_order N]

/-!  We are about to sneak in a hypothesis that might appear to be too strong.
We assume `covariant_class` with *strict* inequality `<` also when proving the one with the
*weak* inequality `≤`.  This is actually necessary: addition on `lex (α →₀ N)` may fail to be
monotone, when it is "just" monotone on `N`.

See `counterexamples.zero_divisors_in_add_monoid_algebras` for a counterexample. -/
section left
variables [covariant_class N N (+) (<)]

instance lex.covariant_class_lt_left : covariant_class (lex (α →₀ N)) (lex (α →₀ N)) (+) (<) :=
⟨λ f g h ⟨a, lta, ha⟩, ⟨a, λ j ja, congr_arg ((+) _) (lta j ja), add_lt_add_left ha _⟩⟩

instance lex.covariant_class_le_left : covariant_class (lex (α →₀ N)) (lex (α →₀ N)) (+) (≤) :=
has_add.to_covariant_class_left _

end left

section right
variables [covariant_class N N (function.swap (+)) (<)]

instance lex.covariant_class_lt_right :
  covariant_class (lex (α →₀ N)) (lex (α →₀ N)) (function.swap (+)) (<) :=
⟨λ f g h ⟨a, lta, ha⟩, ⟨a, λ j ja, congr_arg (+ (of_lex f j)) (lta j ja), add_lt_add_right ha _⟩⟩

instance lex.covariant_class_le_right :
  covariant_class (lex (α →₀ N)) (lex (α →₀ N)) (function.swap (+)) (≤) :=
has_add.to_covariant_class_right _

end right

end covariants

end finsupp
