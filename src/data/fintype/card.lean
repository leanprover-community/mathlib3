/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/

import data.fintype
import algebra.big_operators

/-!
Results about "big operations" over a `fintype`, and consequent
results about cardinalities of certain types.

## Implementation note
This content had previously been in `data.fintype`, but was moved here to avoid
requiring `algebra.big_operators` (and hence many other imports) as a
dependency of `fintype`.
-/

universes u v

variables {α : Type*} {β : Type*} {γ : Type*}

namespace fintype

lemma card_eq_sum_ones {α} [fintype α] : fintype.card α = (finset.univ : finset α).sum (λ _, 1) :=
finset.card_eq_sum_ones _

end fintype

open finset

theorem fin.prod_univ_succ [comm_monoid β] {n:ℕ} (f : fin n.succ → β) :
  univ.prod f = f 0 * univ.prod (λ i:fin n, f i.succ) :=
begin
  rw [fin.univ_succ, prod_insert, prod_image],
  { intros x _ y _ hxy, exact fin.succ.inj hxy },
  { simpa using fin.succ_ne_zero }
end

@[simp, to_additive] theorem fin.prod_univ_zero [comm_monoid β] (f : fin 0 → β) : univ.prod f = 1 := rfl

theorem fin.sum_univ_succ [add_comm_monoid β] {n:ℕ} (f : fin n.succ → β) :
  univ.sum f = f 0 + univ.sum (λ i:fin n, f i.succ) :=
by apply @fin.prod_univ_succ (multiplicative β)

attribute [to_additive] fin.prod_univ_succ

theorem fin.prod_univ_cast_succ [comm_monoid β] {n:ℕ} (f : fin n.succ → β) :
  univ.prod f = univ.prod (λ i:fin n, f i.cast_succ) * f (fin.last n) :=
begin
  rw [fin.univ_cast_succ, prod_insert, prod_image, mul_comm],
  { intros x _ y _ hxy, exact fin.cast_succ_inj.mp hxy },
  { simpa using fin.cast_succ_ne_last }
end

theorem fin.sum_univ_cast_succ [add_comm_monoid β] {n:ℕ} (f : fin n.succ → β) :
  univ.sum f = univ.sum (λ i:fin n, f i.cast_succ) + f (fin.last n) :=
by apply @fin.prod_univ_cast_succ (multiplicative β)
attribute [to_additive] fin.prod_univ_cast_succ

@[simp] theorem fintype.card_sigma {α : Type*} (β : α → Type*)
  [fintype α] [∀ a, fintype (β a)] :
  fintype.card (sigma β) = univ.sum (λ a, fintype.card (β a)) :=
card_sigma _ _

-- FIXME ouch, this should be in the main file.
@[simp] theorem fintype.card_sum (α β : Type*) [fintype α] [fintype β] :
  fintype.card (α ⊕ β) = fintype.card α + fintype.card β :=
by rw [sum.fintype, fintype.of_equiv_card]; simp

@[simp] lemma fintype.card_pi {β : α → Type*} [fintype α] [decidable_eq α]
  [f : Π a, fintype (β a)] : fintype.card (Π a, β a) = univ.prod (λ a, fintype.card (β a)) :=
by letI f' : fintype (Πa∈univ, β a) :=
  ⟨(univ.pi $ λa, univ), assume f, finset.mem_pi.2 $ assume a ha, mem_univ _⟩;
exact calc fintype.card (Π a, β a) = fintype.card (Π a ∈ univ, β a) : fintype.card_congr
  ⟨λ f a ha, f a, λ f a, f a (mem_univ a), λ _, rfl, λ _, rfl⟩
... = univ.prod (λ a, fintype.card (β a)) : finset.card_pi _ _

-- FIXME ouch, this should be in the main file.
@[simp] lemma fintype.card_fun [fintype α] [decidable_eq α] [fintype β] :
  fintype.card (α → β) = fintype.card β ^ fintype.card α :=
by rw [fintype.card_pi, finset.prod_const, nat.pow_eq_pow]; refl

@[simp] lemma card_vector [fintype α] (n : ℕ) :
  fintype.card (vector α n) = fintype.card α ^ n :=
by rw fintype.of_equiv_card; simp


@[simp, to_additive]
lemma finset.prod_attach_univ [fintype α] [comm_monoid β] (f : {a : α // a ∈ @univ α _} → β) :
  univ.attach.prod (λ x, f x) = univ.prod (λ x, f ⟨x, (mem_univ _)⟩) :=
prod_bij (λ x _, x.1) (λ _ _, mem_univ _) (λ _ _ , by simp) (by simp) (λ b _, ⟨⟨b, mem_univ _⟩, by simp⟩)

@[to_additive]
lemma finset.range_prod_eq_univ_prod [comm_monoid β] (n : ℕ) (f : ℕ → β) :
  (range n).prod f = univ.prod (λ (k : fin n), f k) :=
begin
  symmetry,
  refine prod_bij (λ k hk, k) _ _ _ _,
  { rintro ⟨k, hk⟩ _, simp * },
  { rintro ⟨k, hk⟩ _, simp * },
  { intros, rwa fin.eq_iff_veq },
  { intros k hk, rw mem_range at hk,
    exact ⟨⟨k, hk⟩, mem_univ _, rfl⟩ }
end

@[simp] lemma fintype.card_pi_finset [decidable_eq α] [fintype α]
  {δ : α → Type*} [decidable_eq (Π a, δ a)] (t : Π a, finset (δ a)) :
  (fintype.pi_finset t).card = finset.univ.prod (λ a, card (t a)) :=
begin
  dsimp [fintype.pi_finset],
  rw card_image_of_injective,
  { simp },
  { assume f g hfg,
    ext a ha,
    exact (congr_fun hfg a : _) }
end

@[to_additive] lemma finset.prod_univ_pi [decidable_eq α] [fintype α] [comm_monoid β]
  {δ : α → Type u_1} [Π (a : α), decidable_eq (δ a)] {t : Π (a : α), finset (δ a)}
  (f : (Π (a : α), a ∈ (univ : finset α) → δ a) → β) :
  (univ.pi t).prod f = (fintype.pi_finset t).prod (λ x, f (λ a _, x a)) :=
prod_bij (λ x _ a, x a (mem_univ _))
  (by simp)
  (by simp)
  (by simp [function.funext_iff] {contextual := tt})
  (λ x hx, ⟨λ a _, x a, by simp * at *⟩)

lemma finset.prod_univ_sum [decidable_eq α] [fintype α] [comm_semiring β] {δ : α → Type u_1}
  [Π (a : α), decidable_eq (δ a)] {t : Π (a : α), finset (δ a)}
  {f : Π (a : α), δ a → β} :
  univ.prod (λ a, (t a).sum (λ b, f a b)) =
  (fintype.pi_finset t).sum (λ p, univ.prod (λ x, f x (p x))) :=
by simp only [finset.prod_attach_univ, prod_sum, finset.sum_univ_pi]
