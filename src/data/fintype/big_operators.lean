/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.fintype.option
import data.fintype.powerset
import data.fintype.sigma
import data.fintype.sum
import data.fintype.vector
import algebra.big_operators.ring
import algebra.big_operators.option

/-!
Results about "big operations" over a `fintype`, and consequent
results about cardinalities of certain types.

## Implementation note

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
This content had previously been in `data.fintype.basic`, but was moved here to avoid
requiring `algebra.big_operators` (and hence many other imports) as a
dependency of `fintype`.

However many of the results here really belong in `algebra.big_operators.basic`
and should be moved at some point.
-/

universes u v

variables {α : Type*} {β : Type*} {γ : Type*}

open_locale big_operators

namespace fintype

@[to_additive]
lemma prod_bool [comm_monoid α] (f : bool → α) : ∏ b, f b = f tt * f ff := by simp

lemma card_eq_sum_ones {α} [fintype α] : fintype.card α = ∑ a : α, 1 :=
finset.card_eq_sum_ones _

section
open finset

variables {ι : Type*} [decidable_eq ι] [fintype ι]

@[to_additive]
lemma prod_extend_by_one [comm_monoid α] (s : finset ι) (f : ι → α) :
  ∏ i, (if i ∈ s then f i else 1) = ∏ i in s, f i :=
by rw [← prod_filter, filter_mem_eq_inter, univ_inter]

end

section
variables {M : Type*} [fintype α] [comm_monoid M]

@[to_additive]
lemma prod_eq_one (f : α → M) (h : ∀ a, f a = 1) :
  (∏ a, f a) = 1 :=
finset.prod_eq_one $ λ a ha, h a

@[to_additive]
lemma prod_congr (f g : α → M) (h : ∀ a, f a = g a) :
  (∏ a, f a) = ∏ a, g a :=
finset.prod_congr rfl $ λ a ha, h a

@[to_additive]
lemma prod_eq_single {f : α → M} (a : α) (h : ∀ x ≠ a, f x = 1) :
  (∏ x, f x) = f a :=
finset.prod_eq_single a (λ x _ hx, h x hx) $ λ ha, (ha (finset.mem_univ a)).elim

@[to_additive]
lemma prod_eq_mul {f : α → M} (a b : α) (h₁ : a ≠ b) (h₂ : ∀ x, x ≠ a ∧ x ≠ b → f x = 1) :
  (∏ x, f x) = (f a) * (f b) :=
begin
  apply finset.prod_eq_mul a b h₁ (λ x _ hx, h₂ x hx);
  exact λ hc, (hc (finset.mem_univ _)).elim
end

/-- If a product of a `finset` of a subsingleton type has a given
value, so do the terms in that product. -/
@[to_additive "If a sum of a `finset` of a subsingleton type has a given
value, so do the terms in that sum."]
lemma eq_of_subsingleton_of_prod_eq {ι : Type*} [subsingleton ι] {s : finset ι}
    {f : ι → M} {b : M} (h : ∏ i in s, f i = b) : ∀ i ∈ s, f i = b :=
finset.eq_of_card_le_one_of_prod_eq (finset.card_le_one_of_subsingleton s) h

end

end fintype

open finset

section

variables {M : Type*} [fintype α] [comm_monoid M]

@[simp, to_additive]
lemma fintype.prod_option (f : option α → M) : ∏ i, f i = f none * ∏ i, f (some i) :=
finset.prod_insert_none f univ

end

open finset

@[simp] theorem fintype.card_sigma {α : Type*} (β : α → Type*)
  [fintype α] [∀ a, fintype (β a)] :
  fintype.card (sigma β) = ∑ a, fintype.card (β a) :=
card_sigma _ _

@[simp] lemma finset.card_pi [decidable_eq α] {δ : α → Type*}
  (s : finset α) (t : Π a, finset (δ a)) :
  (s.pi t).card = ∏ a in s, card (t a) :=
multiset.card_pi _ _

@[simp] lemma fintype.card_pi_finset [decidable_eq α] [fintype α]
  {δ : α → Type*} (t : Π a, finset (δ a)) :
  (fintype.pi_finset t).card = ∏ a, card (t a) :=
by simp [fintype.pi_finset, card_map]

@[simp] lemma fintype.card_pi {β : α → Type*} [decidable_eq α] [fintype α]
  [f : Π a, fintype (β a)] : fintype.card (Π a, β a) = ∏ a, fintype.card (β a) :=
fintype.card_pi_finset _

-- FIXME ouch, this should be in the main file.
@[simp] lemma fintype.card_fun [decidable_eq α] [fintype α] [fintype β] :
  fintype.card (α → β) = fintype.card β ^ fintype.card α :=
by rw [fintype.card_pi, finset.prod_const]; refl

@[simp] lemma card_vector [fintype α] (n : ℕ) :
  fintype.card (vector α n) = fintype.card α ^ n :=
by rw fintype.of_equiv_card; simp

@[simp, to_additive]
lemma finset.prod_attach_univ [fintype α] [comm_monoid β] (f : {a : α // a ∈ @univ α _} → β) :
  ∏ x in univ.attach, f x = ∏ x, f ⟨x, (mem_univ _)⟩ :=
fintype.prod_equiv (equiv.subtype_univ_equiv (λ x, mem_univ _)) _ _ (λ x, by simp)

/-- Taking a product over `univ.pi t` is the same as taking the product over `fintype.pi_finset t`.
  `univ.pi t` and `fintype.pi_finset t` are essentially the same `finset`, but differ
  in the type of their element, `univ.pi t` is a `finset (Π a ∈ univ, t a)` and
  `fintype.pi_finset t` is a `finset (Π a, t a)`. -/
@[to_additive "Taking a sum over `univ.pi t` is the same as taking the sum over
  `fintype.pi_finset t`. `univ.pi t` and `fintype.pi_finset t` are essentially the same `finset`,
  but differ in the type of their element, `univ.pi t` is a `finset (Π a ∈ univ, t a)` and
  `fintype.pi_finset t` is a `finset (Π a, t a)`."]
lemma finset.prod_univ_pi [decidable_eq α] [fintype α] [comm_monoid β]
  {δ : α → Type*} {t : Π (a : α), finset (δ a)}
  (f : (Π (a : α), a ∈ (univ : finset α) → δ a) → β) :
  ∏ x in univ.pi t, f x = ∏ x in fintype.pi_finset t, f (λ a _, x a) :=
prod_bij (λ x _ a, x a (mem_univ _))
  (by simp)
  (by simp)
  (by simp [function.funext_iff] {contextual := tt})
  (λ x hx, ⟨λ a _, x a, by simp * at *⟩)

/-- The product over `univ` of a sum can be written as a sum over the product of sets,
  `fintype.pi_finset`. `finset.prod_sum` is an alternative statement when the product is not
  over `univ` -/
lemma finset.prod_univ_sum [decidable_eq α] [fintype α] [comm_semiring β] {δ : α → Type u_1}
  [Π (a : α), decidable_eq (δ a)] {t : Π (a : α), finset (δ a)}
  {f : Π (a : α), δ a → β} :
  ∏ a, ∑ b in t a, f a b = ∑ p in fintype.pi_finset t, ∏ x, f x (p x) :=
by simp only [finset.prod_attach_univ, prod_sum, finset.sum_univ_pi]

/-- Summing `a^s.card * b^(n-s.card)` over all finite subsets `s` of a fintype of cardinality `n`
gives `(a + b)^n`. The "good" proof involves expanding along all coordinates using the fact that
`x^n` is multilinear, but multilinear maps are only available now over rings, so we give instead
a proof reducing to the usual binomial theorem to have a result over semirings. -/
lemma fintype.sum_pow_mul_eq_add_pow
  (α : Type*) [fintype α] {R : Type*} [comm_semiring R] (a b : R) :
  ∑ s : finset α, a ^ s.card * b ^ (fintype.card α - s.card) =
  (a + b) ^ (fintype.card α) :=
finset.sum_pow_mul_eq_add_pow _ _ _

@[to_additive]
lemma function.bijective.prod_comp [fintype α] [fintype β] [comm_monoid γ] {f : α → β}
  (hf : function.bijective f) (g : β → γ) :
  ∏ i, g (f i) = ∏ i, g i :=
fintype.prod_bijective f hf _ _ (λ x, rfl)

@[to_additive]
lemma equiv.prod_comp [fintype α] [fintype β] [comm_monoid γ] (e : α ≃ β) (f : β → γ) :
  ∏ i, f (e i) = ∏ i, f i :=
e.bijective.prod_comp f

@[to_additive]
lemma equiv.prod_comp' [fintype α] [fintype β] [comm_monoid γ] (e : α ≃ β) (f : α → γ) (g : β → γ)
  (h : ∀ i, f i = g (e i)) : ∏ i, f i = ∏ i, g i :=
(show f = g ∘ e, from funext h).symm ▸ e.prod_comp _

/-- It is equivalent to compute the product of a function over `fin n` or `finset.range n`. -/
@[to_additive "It is equivalent to sum a function over `fin n` or `finset.range n`."]
lemma fin.prod_univ_eq_prod_range [comm_monoid α] (f : ℕ → α) (n : ℕ) :
  ∏ i : fin n, f i = ∏ i in range n, f i :=
calc (∏ i : fin n, f i) = ∏ i : {x // x ∈ range n}, f i :
  (fin.equiv_subtype.trans (equiv.subtype_equiv_right (by simp))).prod_comp' _ _ (by simp)
... = ∏ i in range n, f i : by rw [← attach_eq_univ, prod_attach]

@[to_additive]
lemma finset.prod_fin_eq_prod_range [comm_monoid β] {n : ℕ} (c : fin n → β) :
  ∏ i, c i = ∏ i in finset.range n, if h : i < n then c ⟨i, h⟩ else 1 :=
begin
  rw [← fin.prod_univ_eq_prod_range, finset.prod_congr rfl],
  rintros ⟨i, hi⟩ _,
  simp only [fin.coe_eq_val, hi, dif_pos]
end

@[to_additive]
lemma finset.prod_to_finset_eq_subtype {M : Type*} [comm_monoid M] [fintype α]
  (p : α → Prop) [decidable_pred p] (f : α → M) :
    ∏ a in {x | p x}.to_finset, f a = ∏ a : subtype p, f a :=
by { rw ← finset.prod_subtype, simp }

@[to_additive] lemma finset.prod_fiberwise [decidable_eq β] [fintype β] [comm_monoid γ]
  (s : finset α) (f : α → β) (g : α → γ) :
  ∏ b : β, ∏ a in s.filter (λ a, f a = b), g a = ∏ a in s, g a :=
finset.prod_fiberwise_of_maps_to (λ x _, mem_univ _) _

@[to_additive]
lemma fintype.prod_fiberwise [fintype α] [decidable_eq β] [fintype β] [comm_monoid γ]
  (f : α → β) (g : α → γ) :
  (∏ b : β, ∏ a : {a // f a = b}, g (a : α)) = ∏ a, g a :=
begin
  rw [← (equiv.sigma_fiber_equiv f).prod_comp, ← univ_sigma_univ, prod_sigma],
  refl
end

lemma fintype.prod_dite [fintype α] {p : α → Prop} [decidable_pred p]
  [comm_monoid β] (f : Π (a : α) (ha : p a), β) (g : Π (a : α) (ha : ¬p a), β) :
  (∏ a, dite (p a) (f a) (g a)) = (∏ a : {a // p a}, f a a.2) * (∏ a : {a // ¬p a}, g a a.2) :=
begin
  simp only [prod_dite, attach_eq_univ],
  congr' 1,
  { convert (equiv.subtype_equiv_right _).prod_comp (λ x : {x // p x}, f x x.2),
    simp },
  { convert (equiv.subtype_equiv_right _).prod_comp (λ x : {x // ¬p x}, g x x.2),
    simp }
end

section
open finset

variables {α₁ : Type*} {α₂ : Type*} {M : Type*} [fintype α₁] [fintype α₂] [comm_monoid M]

@[to_additive]
lemma fintype.prod_sum_elim (f : α₁ → M) (g : α₂ → M) :
  (∏ x, sum.elim f g x) = (∏ a₁, f a₁) * (∏ a₂, g a₂) :=
prod_disj_sum _ _ _

@[simp, to_additive]
lemma fintype.prod_sum_type (f : α₁ ⊕ α₂ → M) :
  (∏ x, f x) = (∏ a₁, f (sum.inl a₁)) * (∏ a₂, f (sum.inr a₂)) :=
prod_disj_sum _ _ _

end
