/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/

import data.nat.enat
import algebra.big_operators.order
import data.finset.pi
import data.finset.powerset

universes u v w

open_locale big_operators

variables {α : Type u} {β : Type v} {γ : Type w}

namespace finset
variables {s s₁ s₂ : finset α} {a : α} {f g : α → β}

lemma sum_const_nat {m : ℕ} {f : α → ℕ} (h₁ : ∀x ∈ s, f x = m) :
  (∑ x in s, f x) = card s * m :=
begin
  rw [← nat.nsmul_eq_mul, ← sum_const],
  apply sum_congr rfl h₁
end

@[simp]
lemma sum_boole {s : finset α} {p : α → Prop} [semiring β] {hp : decidable_pred p} :
  (∑ x in s, if p x then (1 : β) else (0 : β)) = (s.filter p).card :=
by simp [sum_ite]

@[norm_cast]
lemma sum_nat_cast [add_comm_monoid β] [has_one β] (s : finset α) (f : α → ℕ) :
  ↑(∑ x in s, f x : ℕ) = (∑ x in s, (f x : β)) :=
(nat.cast_add_monoid_hom β).map_sum f s

@[norm_cast]
lemma prod_nat_cast [comm_semiring β] (s : finset α) (f : α → ℕ) :
  ↑(∏ x in s, f x : ℕ) = (∏ x in s, (f x : β)) :=
(nat.cast_ring_hom β).map_prod f s

protected lemma sum_nat_coe_enat (s : finset α) (f : α → ℕ) :
  (∑ x in s, (f x : enat)) = (∑ x  in s, f x : ℕ) :=
begin
  classical,
  induction s using finset.induction with a s has ih h,
  { simp },
  { simp [has, ih] }
end

theorem dvd_sum [comm_semiring α] {a : α} {s : finset β} {f : β → α}
  (h : ∀ x ∈ s, a ∣ f x) : a ∣ ∑ x in s, f x :=
multiset.dvd_sum (λ y hy, by rcases multiset.mem_map.1 hy with ⟨x, hx, rfl⟩; exact h x hx)


/-- A product over all subsets of `s ∪ {x}` is obtained by multiplying the product over all subsets
of `s`, and over all subsets of `s` to which one adds `x`. -/
@[to_additive]
lemma prod_powerset_insert [decidable_eq α] [comm_monoid β] {s : finset α} {x : α} (h : x ∉ s) (f : finset α → β) :
  (∏ a in (insert x s).powerset, f a) =
    (∏ a in s.powerset, f a) * (∏ t in s.powerset, f (insert x t)) :=
begin
  rw [powerset_insert, finset.prod_union, finset.prod_image],
  { assume t₁ h₁ t₂ h₂ heq,
    rw [← finset.erase_insert (not_mem_of_mem_powerset_of_not_mem h₁ h),
        ← finset.erase_insert (not_mem_of_mem_powerset_of_not_mem h₂ h), heq] },
  { rw finset.disjoint_iff_ne,
    assume t₁ h₁ t₂ h₂,
    rcases finset.mem_image.1 h₂ with ⟨t₃, h₃, H₃₂⟩,
    rw ← H₃₂,
    exact ne_insert_of_not_mem _ _ (not_mem_of_mem_powerset_of_not_mem h₁ h) }
end

section comm_group
variables [comm_group β]

@[simp, to_additive]
lemma prod_inv_distrib : (∏ x in s, (f x)⁻¹) = (∏ x in s, f x)⁻¹ :=
s.prod_hom has_inv.inv

end comm_group

@[simp] theorem card_sigma {σ : α → Type*} (s : finset α) (t : Π a, finset (σ a)) :
  card (s.sigma t) = ∑ a in s, card (t a) :=
multiset.card_sigma _ _

lemma card_bind [decidable_eq β] {s : finset α} {t : α → finset β}
  (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → disjoint (t x) (t y)) :
  (s.bind t).card = ∑ u in s, card (t u) :=
calc (s.bind t).card = ∑ i in s.bind t, 1 : by simp
... = ∑ a in s, ∑ i in t a, 1 : finset.sum_bind h
... = ∑ u in s, card (t u) : by simp

lemma card_bind_le [decidable_eq β] {s : finset α} {t : α → finset β} :
  (s.bind t).card ≤ ∑ a in s, (t a).card :=
by haveI := classical.dec_eq α; exact
finset.induction_on s (by simp)
  (λ a s has ih,
    calc ((insert a s).bind t).card ≤ (t a).card + (s.bind t).card :
    by rw bind_insert; exact finset.card_union_le _ _
    ... ≤ ∑ a in insert a s, card (t a) :
    by rw sum_insert has; exact add_le_add_left ih _)

theorem card_eq_sum_card_image [decidable_eq β] (f : α → β) (s : finset α) :
  s.card = ∑ a in s.image f, (s.filter (λ x, f x = a)).card :=
by letI := classical.dec_eq α; exact
calc s.card = ((s.image f).bind (λ a, s.filter (λ x, f x = a))).card :
  congr_arg _ (finset.ext $ λ x,
    ⟨λ hs, mem_bind.2 ⟨f x, mem_image_of_mem _ hs,
      mem_filter.2 ⟨hs, rfl⟩⟩,
    λ h, let ⟨a, ha₁, ha₂⟩ := mem_bind.1 h in by convert filter_subset s ha₂⟩)
... = ∑ a in s.image f, (s.filter (λ x, f x = a)).card :
  card_bind (by simp [disjoint_left, finset.ext_iff] {contextual := tt})

lemma gsmul_sum [add_comm_group β] {f : α → β} {s : finset α} (z : ℤ) :
  gsmul z (∑ a in s, f a) = ∑ a in s, gsmul z (f a) :=
(s.sum_hom (gsmul z)).symm

end finset

namespace finset
variables {s s₁ s₂ : finset α} {f g : α → β} {b : β} {a : α}

@[simp] lemma sum_sub_distrib [add_comm_group β] :
  ∑ x in s, (f x - g x) = (∑ x in s, f x) - (∑ x in s, g x) :=
sum_add_distrib.trans $ congr_arg _ sum_neg_distrib

section comm_monoid
variables [comm_monoid β]

lemma prod_pow_boole [decidable_eq α] (s : finset α) (f : α → β) (a : α) :
  (∏ x in s, (f x)^(ite (a = x) 1 0)) = ite (a ∈ s) (f a) 1 :=
by simp

end comm_monoid

section prod_eq_zero
variables [comm_monoid_with_zero β]

lemma prod_eq_zero (ha : a ∈ s) (h : f a = 0) : (∏ x in s, f x) = 0 :=
by haveI := classical.dec_eq α;
calc (∏ x in s, f x) = ∏ x in insert a (erase s a), f x : by rw insert_erase ha
                 ... = 0 : by rw [prod_insert (not_mem_erase _ _), h, zero_mul]

variables [nontrivial β] [no_zero_divisors β]

lemma prod_eq_zero_iff : (∏ x in s, f x) = 0 ↔ (∃a∈s, f a = 0) :=
begin
  classical,
  apply finset.induction_on s,
  exact ⟨not.elim one_ne_zero, λ ⟨_, H, _⟩, H.elim⟩,
  assume a s ha ih,
  rw [prod_insert ha, mul_eq_zero, bex_def, exists_mem_insert, ih, ← bex_def]
end

theorem prod_ne_zero_iff : (∏ x in s, f x) ≠ 0 ↔ (∀ a ∈ s, f a ≠ 0) :=
by { rw [ne, prod_eq_zero_iff], push_neg }

end prod_eq_zero


@[simp] lemma card_pi [decidable_eq α] {δ : α → Type*}
  (s : finset α) (t : Π a, finset (δ a)) :
  (s.pi t).card = ∏ a in s, card (t a) :=
multiset.card_pi _ _

theorem card_le_mul_card_image [decidable_eq β] {f : α → β} (s : finset α)
  (n : ℕ) (hn : ∀ a ∈ s.image f, (s.filter (λ x, f x = a)).card ≤ n) :
  s.card ≤ n * (s.image f).card :=
calc s.card = (∑ a in s.image f, (s.filter (λ x, f x = a)).card) :
  card_eq_sum_card_image _ _
... ≤ (∑ _ in s.image f, n) : sum_le_sum hn
... = _ : by simp [mul_comm]

lemma card_eq_sum_ones (s : finset α) : s.card = ∑ _ in s, 1 :=
by simp

end finset

@[to_additive is_add_group_hom_finset_sum]
lemma is_group_hom_finset_prod {α β γ} [group α] [comm_group β] (s : finset γ)
  (f : γ → α → β) [∀c, is_group_hom (f c)] : is_group_hom (λa, ∏ c in s, f c a) :=
{ map_mul := assume a b, by simp only [λc, is_mul_hom.map_mul (f c), finset.prod_mul_distrib] }

attribute [instance] is_group_hom_finset_prod is_add_group_hom_finset_sum

namespace multiset
variables [decidable_eq α]

@[simp] lemma to_finset_sum_count_eq (s : multiset α) :
  (∑ a in s.to_finset, s.count a) = s.card :=
multiset.induction_on s rfl
  (assume a s ih,
    calc (∑ x in to_finset (a :: s), count x (a :: s)) =
      ∑ x in to_finset (a :: s), ((if x = a then 1 else 0) + count x s) :
        finset.sum_congr rfl $ λ _ _, by split_ifs;
        [simp only [h, count_cons_self, nat.one_add], simp only [count_cons_of_ne h, zero_add]]
      ... = card (a :: s) :
      begin
        by_cases a ∈ s.to_finset,
        { have : ∑ x in s.to_finset, ite (x = a) 1 0 = ∑ x in {a}, ite (x = a) 1 0,
          { rw [finset.sum_ite_eq', if_pos h, finset.sum_singleton, if_pos rfl], },
          rw [to_finset_cons, finset.insert_eq_of_mem h, finset.sum_add_distrib, ih, this,
            finset.sum_singleton, if_pos rfl, add_comm, card_cons] },
        { have ha : a ∉ s, by rwa mem_to_finset at h,
          have : ∑ x in to_finset s, ite (x = a) 1 0 = ∑ x in to_finset s, 0, from
            finset.sum_congr rfl (λ x hx, if_neg $ by rintro rfl; cc),
          rw [to_finset_cons, finset.sum_insert h, if_pos rfl, finset.sum_add_distrib, this,
            finset.sum_const_zero, ih, count_eq_zero_of_not_mem ha, zero_add, add_comm, card_cons] }
      end)

end multiset
