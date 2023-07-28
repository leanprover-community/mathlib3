/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import data.fintype.card
import algebra.hom.commute
import algebra.big_operators.basic

/-!
# Products (respectively, sums) over a finset or a multiset.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The regular `finset.prod` and `multiset.prod` require `[comm_monoid α]`.
Often, there are collections `s : finset α` where `[monoid α]` and we know,
in a dependent fashion, that for all the terms `∀ (x ∈ s) (y ∈ s), commute x y`.
This allows to still have a well-defined product over `s`.

## Main definitions

- `finset.noncomm_prod`, requiring a proof of commutativity of held terms
- `multiset.noncomm_prod`, requiring a proof of commutativity of held terms

## Implementation details

While `list.prod` is defined via `list.foldl`, `noncomm_prod` is defined via
`multiset.foldr` for neater proofs and definitions. By the commutativity assumption,
the two must be equal.

-/

variables {F ι α β γ : Type*} (f : α → β → β) (op : α → α → α)

namespace multiset

/-- Fold of a `s : multiset α` with `f : α → β → β`, given a proof that `left_commutative f`
on all elements `x ∈ s`. -/
def noncomm_foldr (s : multiset α)
  (comm : {x | x ∈ s}.pairwise $ λ x y, ∀ b, f x (f y b) = f y (f x b)) (b : β) :
  β :=
s.attach.foldr (f ∘ subtype.val) (λ ⟨x, hx⟩ ⟨y, hy⟩, begin
    haveI : is_refl α (λ x y, ∀ b, f x (f y b) = f y (f x b)) := ⟨λ x b, rfl⟩,
    exact comm.of_refl hx hy,
  end) b

@[simp] lemma noncomm_foldr_coe (l : list α) (comm) (b : β) :
  noncomm_foldr f (l : multiset α) comm b = l.foldr f b :=
begin
  simp only [noncomm_foldr, coe_foldr, coe_attach, list.attach],
  rw ←list.foldr_map,
  simp [list.map_pmap, list.pmap_eq_map]
end

@[simp] lemma noncomm_foldr_empty (h) (b : β) : noncomm_foldr f (0 : multiset α) h b = b := rfl

lemma noncomm_foldr_cons (s : multiset α) (a : α) (h h') (b : β) :
  noncomm_foldr f (a ::ₘ s) h b = f a (noncomm_foldr f s h' b) :=
begin
  induction s using quotient.induction_on,
  simp
end

lemma noncomm_foldr_eq_foldr (s : multiset α) (h : left_commutative f) (b : β) :
  noncomm_foldr f s (λ x _ y _ _, h x y) b = foldr f h b s :=
begin
  induction s using quotient.induction_on,
  simp
end

variables [assoc : is_associative α op]
include assoc

/-- Fold of a `s : multiset α` with an associative `op : α → α → α`, given a proofs that `op`
is commutative on all elements `x ∈ s`. -/
def noncomm_fold (s : multiset α) (comm : {x | x ∈ s}.pairwise $ λ x y, op x y = op y x) : α → α :=
noncomm_foldr op s (λ x hx y hy h b, by rw [←assoc.assoc, comm hx hy h, assoc.assoc])

@[simp] lemma noncomm_fold_coe (l : list α) (comm) (a : α) :
  noncomm_fold op (l : multiset α) comm a = l.foldr op a :=
by simp [noncomm_fold]

@[simp] lemma noncomm_fold_empty (h) (a : α) : noncomm_fold op (0 : multiset α) h a = a := rfl

lemma noncomm_fold_cons (s : multiset α) (a : α) (h h') (x : α) :
  noncomm_fold op (a ::ₘ s) h x = op a (noncomm_fold op s h' x) :=
begin
  induction s using quotient.induction_on,
  simp
end

lemma noncomm_fold_eq_fold (s : multiset α) [is_commutative α op] (a : α) :
  noncomm_fold op s (λ x _ y _ _, is_commutative.comm x y) a = fold op a s :=
begin
  induction s using quotient.induction_on,
  simp
end

omit assoc
variables [monoid α] [monoid β]

/-- Product of a `s : multiset α` with `[monoid α]`, given a proof that `*` commutes
on all elements `x ∈ s`. -/
@[to_additive "Sum of a `s : multiset α` with `[add_monoid α]`, given a proof that `+` commutes
on all elements `x ∈ s`." ]
def noncomm_prod (s : multiset α) (comm : {x | x ∈ s}.pairwise commute) : α :=
s.noncomm_fold (*) comm 1

@[simp, to_additive] lemma noncomm_prod_coe (l : list α) (comm) :
  noncomm_prod (l : multiset α) comm = l.prod :=
begin
  rw [noncomm_prod],
  simp only [noncomm_fold_coe],
  induction l with hd tl hl,
  { simp },
  { rw [list.prod_cons, list.foldr, hl],
    intros x hx y hy,
    exact comm (list.mem_cons_of_mem _ hx) (list.mem_cons_of_mem _ hy) }
end

@[simp, to_additive] lemma noncomm_prod_empty (h) : noncomm_prod (0 : multiset α) h = 1 := rfl

@[simp, to_additive] lemma noncomm_prod_cons (s : multiset α) (a : α) (comm) :
  noncomm_prod (a ::ₘ s) comm = a * noncomm_prod s (comm.mono $ λ _, mem_cons_of_mem) :=
by { induction s using quotient.induction_on, simp }

@[to_additive] lemma noncomm_prod_cons' (s : multiset α) (a : α) (comm) :
  noncomm_prod (a ::ₘ s) comm = noncomm_prod s (comm.mono $ λ _, mem_cons_of_mem) * a :=
begin
  induction s using quotient.induction_on with s,
  simp only [quot_mk_to_coe, cons_coe, noncomm_prod_coe, list.prod_cons],
  induction s with hd tl IH,
  { simp },
  { rw [list.prod_cons, mul_assoc, ←IH, ←mul_assoc, ←mul_assoc],
    { congr' 1,
      apply comm.of_refl;
      simp },
    { intros x hx y hy,
      simp only [quot_mk_to_coe, list.mem_cons_iff, mem_coe, cons_coe] at hx hy,
      apply comm,
      { cases hx;
        simp [hx] },
      { cases hy;
        simp [hy] } } }
end

@[to_additive] lemma noncomm_prod_add (s t : multiset α) (comm) :
  noncomm_prod (s + t) comm =
  noncomm_prod s (comm.mono $ subset_of_le $ s.le_add_right t) *
  noncomm_prod t (comm.mono $ subset_of_le $ t.le_add_left s) :=
by { rcases s, rcases t, simp }

@[protected, to_additive]
lemma noncomm_prod_map_aux [monoid_hom_class F α β] (s : multiset α)
  (comm : {x | x ∈ s}.pairwise commute) (f : F) :
  {x | x ∈ s.map f}.pairwise commute :=
begin
  simp only [multiset.mem_map],
  rintros _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _,
  exact (comm.of_refl hx hy).map f,
end

@[to_additive]
lemma noncomm_prod_map [monoid_hom_class F α β] (s : multiset α) (comm) (f : F) :
  f (s.noncomm_prod comm) = (s.map f).noncomm_prod (noncomm_prod_map_aux s comm f) :=
begin
  induction s using quotient.induction_on,
  simpa using map_list_prod f _,
end

@[to_additive noncomm_sum_eq_card_nsmul]
lemma noncomm_prod_eq_pow_card (s : multiset α) (comm) (m : α) (h : ∀ x ∈ s, x = m) :
  s.noncomm_prod comm = m ^ s.card :=
begin
  induction s using quotient.induction_on,
  simp only [quot_mk_to_coe, noncomm_prod_coe, coe_card, mem_coe] at *,
  exact list.prod_eq_pow_card _ m h,
end

@[to_additive] lemma noncomm_prod_eq_prod {α : Type*} [comm_monoid α] (s : multiset α) :
  noncomm_prod s (λ _ _ _ _ _, commute.all _ _) = prod s :=
begin
  induction s using quotient.induction_on,
  simp
end

@[to_additive noncomm_sum_add_commute]
lemma noncomm_prod_commute (s : multiset α) (comm) (y : α) (h : ∀ x ∈ s, commute y x) :
  commute y (s.noncomm_prod comm) :=
begin
  induction s using quotient.induction_on,
  simp only [quot_mk_to_coe, noncomm_prod_coe],
  exact commute.list_prod_right _ _ h,
end

end multiset

namespace finset

variables [monoid β] [monoid γ]

/-- Product of a `s : finset α` mapped with `f : α → β` with `[monoid β]`,
given a proof that `*` commutes on all elements `f x` for `x ∈ s`. -/
@[to_additive "Sum of a `s : finset α` mapped with `f : α → β` with `[add_monoid β]`,
given a proof that `+` commutes on all elements `f x` for `x ∈ s`."]
def noncomm_prod (s : finset α) (f : α → β)
  (comm : (s : set α).pairwise (λ a b, commute (f a) (f b))) : β :=
(s.1.map f).noncomm_prod $
  by { simp_rw multiset.mem_map, rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _, exact comm.of_refl ha hb }

@[congr, to_additive]
lemma noncomm_prod_congr {s₁ s₂ : finset α} {f g : α → β} (h₁ : s₁ = s₂)
  (h₂ : ∀ (x ∈ s₂), f x = g x) (comm) :
  noncomm_prod s₁ f comm = noncomm_prod s₂ g
    (λ x hx y hy h, by { rw [←h₂ _ hx, ←h₂ _ hy], subst h₁, exact comm hx hy h }) :=
by simp_rw [noncomm_prod, multiset.map_congr (congr_arg _ h₁) h₂]

@[simp, to_additive] lemma noncomm_prod_to_finset [decidable_eq α] (l : list α) (f : α → β) (comm)
  (hl : l.nodup) :
  noncomm_prod l.to_finset f comm = (l.map f).prod :=
begin
  rw ←list.dedup_eq_self at hl,
  simp [noncomm_prod, hl]
end

@[simp, to_additive] lemma noncomm_prod_empty (f : α → β) (h) :
  noncomm_prod (∅ : finset α) f h = 1 := rfl

@[simp, to_additive] lemma noncomm_prod_insert_of_not_mem [decidable_eq α] (s : finset α) (a : α)
  (f : α → β) (comm) (ha : a ∉ s) :
  noncomm_prod (insert a s) f comm = f a * noncomm_prod s f (comm.mono $ λ _, mem_insert_of_mem) :=
by simp [insert_val_of_not_mem ha, noncomm_prod]

@[to_additive] lemma noncomm_prod_insert_of_not_mem' [decidable_eq α] (s : finset α) (a : α)
  (f : α → β) (comm) (ha : a ∉ s) :
  noncomm_prod (insert a s) f comm = noncomm_prod s f (comm.mono $ λ _, mem_insert_of_mem) * f a :=
by simp [noncomm_prod, insert_val_of_not_mem ha, multiset.noncomm_prod_cons']

@[simp, to_additive] lemma noncomm_prod_singleton (a : α) (f : α → β) :
  noncomm_prod ({a} : finset α) f (by { norm_cast, exact set.pairwise_singleton _ _ }) = f a :=
by simp [noncomm_prod, ←multiset.cons_zero]

@[to_additive]
lemma noncomm_prod_map [monoid_hom_class F β γ] (s : finset α) (f : α → β) (comm) (g : F) :
  g (s.noncomm_prod f comm) = s.noncomm_prod (λ i, g (f i))
  (λ x hx y hy h, (comm.of_refl hx hy).map g)  :=
by simp [noncomm_prod, multiset.noncomm_prod_map]

@[to_additive noncomm_sum_eq_card_nsmul]
lemma noncomm_prod_eq_pow_card (s : finset α) (f : α → β) (comm) (m : β) (h : ∀ x ∈ s, f x = m) :
  s.noncomm_prod f comm = m ^ s.card :=
begin
  rw [noncomm_prod, multiset.noncomm_prod_eq_pow_card _ _ m],
  simp only [finset.card_def, multiset.card_map],
  simpa using h,
end

@[to_additive noncomm_sum_add_commute]
lemma noncomm_prod_commute (s : finset α) (f : α → β) (comm) (y : β)
  (h : ∀ x ∈ s, commute y (f x)) : commute y (s.noncomm_prod f comm) :=
begin
  apply multiset.noncomm_prod_commute,
  intro y,
  rw multiset.mem_map,
  rintros ⟨x, ⟨hx, rfl⟩⟩,
  exact h x hx,
end

@[to_additive] lemma noncomm_prod_eq_prod {β : Type*} [comm_monoid β] (s : finset α) (f : α → β) :
  noncomm_prod s f (λ _ _ _ _ _, commute.all _ _) = s.prod f :=
begin
  classical,
  induction s using finset.induction_on with a s ha IH,
  { simp },
  { simp [ha, IH] }
end

/-- The non-commutative version of `finset.prod_union` -/
@[to_additive "The non-commutative version of `finset.sum_union`"]
lemma noncomm_prod_union_of_disjoint [decidable_eq α] {s t : finset α}
  (h : disjoint s t) (f : α → β) (comm : {x | x ∈ s ∪ t}.pairwise $ λ a b, commute (f a) (f b)) :
  noncomm_prod (s ∪ t) f comm = noncomm_prod s f (comm.mono $ coe_subset.2 $ subset_union_left _ _)
    * noncomm_prod t f (comm.mono $ coe_subset.2 $ subset_union_right _ _) :=
begin
  obtain ⟨sl, sl', rfl⟩ := exists_list_nodup_eq s,
  obtain ⟨tl, tl', rfl⟩ := exists_list_nodup_eq t,
  rw list.disjoint_to_finset_iff_disjoint at h,
  simp [sl', tl', noncomm_prod_to_finset, ←list.prod_append, ←list.to_finset_append,
    sl'.append tl' h]
end

@[protected, to_additive]
lemma noncomm_prod_mul_distrib_aux {s : finset α} {f : α → β} {g : α → β}
  (comm_ff : (s : set α).pairwise $ λ x y, commute (f x) (f y))
  (comm_gg : (s : set α).pairwise $ λ x y, commute (g x) (g y))
  (comm_gf : (s : set α).pairwise $ λ x y, commute (g x) (f y)) :
  (s : set α).pairwise $ λ x y, commute ((f * g) x) ((f * g) y) :=
begin
  intros x hx y hy h,
  apply commute.mul_left; apply commute.mul_right,
  { exact comm_ff.of_refl hx hy },
  { exact (comm_gf hy hx h.symm).symm },
  { exact comm_gf hx hy h },
  { exact comm_gg.of_refl hx hy }
end

/-- The non-commutative version of `finset.prod_mul_distrib` -/
@[to_additive "The non-commutative version of `finset.sum_add_distrib`"]
lemma noncomm_prod_mul_distrib {s : finset α} (f : α → β) (g : α → β) (comm_ff comm_gg comm_gf) :
  noncomm_prod s (f * g) (noncomm_prod_mul_distrib_aux comm_ff comm_gg comm_gf)
    = noncomm_prod s f comm_ff * noncomm_prod s g comm_gg :=
begin
  classical,
  induction s using finset.induction_on with x s hnmem ih,
  { simp, },
  simp only [finset.noncomm_prod_insert_of_not_mem _ _ _ _ hnmem],
  specialize ih (comm_ff.mono $ λ _, mem_insert_of_mem) (comm_gg.mono $ λ _, mem_insert_of_mem)
    (comm_gf.mono $ λ _, mem_insert_of_mem),
  rw [ih, pi.mul_apply],
  simp only [mul_assoc],
  congr' 1,
  simp only [← mul_assoc],
  congr' 1,
  refine noncomm_prod_commute _ _ _ _ (λ y hy, _),
  exact comm_gf (mem_insert_self x s) (mem_insert_of_mem hy) (ne_of_mem_of_not_mem hy hnmem).symm,
end

section finite_pi
variables {M : ι → Type*} [Π i, monoid (M i)]

@[to_additive]
lemma noncomm_prod_mul_single [fintype ι] [decidable_eq ι] (x : Π i, M i) :
  univ.noncomm_prod (λ i, pi.mul_single i (x i)) (λ i _ j _ _, pi.mul_single_apply_commute x i j)
  = x :=
begin
  ext i,
  apply (univ.noncomm_prod_map (λ i, monoid_hom.single M i (x i)) _
    (pi.eval_monoid_hom M i)).trans,
  rw [ ← insert_erase (mem_univ i),
    noncomm_prod_insert_of_not_mem' _ _ _ _ (not_mem_erase _ _),
    noncomm_prod_eq_pow_card,
    one_pow],
  { simp, },
  { intros i h, simp at h, simp [h], },
end

@[to_additive]
lemma _root_.monoid_hom.pi_ext [finite ι] [decidable_eq ι] {f g : (Π i, M i) →* γ}
  (h : ∀ i x, f (pi.mul_single i x) = g (pi.mul_single i x)) :
  f = g :=
begin
  casesI nonempty_fintype ι,
  ext x,
  rw [← noncomm_prod_mul_single x, univ.noncomm_prod_map, univ.noncomm_prod_map],
  congr' 1 with i, exact h i (x i),
end

end finite_pi

end finset
