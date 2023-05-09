/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.list.nodup
import data.multiset.bind
import data.multiset.range

/-!
# The `nodup` predicate for multisets without duplicate elements.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

namespace multiset
open function list

variables {α β γ : Type*} {r : α → α → Prop} {s t : multiset α} {a : α}

/- nodup -/

/-- `nodup s` means that `s` has no duplicates, i.e. the multiplicity of
  any element is at most 1. -/
def nodup (s : multiset α) : Prop :=
quot.lift_on s nodup (λ s t p, propext p.nodup_iff)

@[simp] theorem coe_nodup {l : list α} : @nodup α l ↔ l.nodup := iff.rfl

@[simp] theorem nodup_zero : @nodup α 0 := pairwise.nil

@[simp] theorem nodup_cons {a : α} {s : multiset α} : nodup (a ::ₘ s) ↔ a ∉ s ∧ nodup s :=
quot.induction_on s $ λ l, nodup_cons

lemma nodup.cons (m : a ∉ s) (n : nodup s) : nodup (a ::ₘ s) := nodup_cons.2 ⟨m, n⟩

@[simp] theorem nodup_singleton : ∀ a : α, nodup ({a} : multiset α) := nodup_singleton

lemma nodup.of_cons (h : nodup (a ::ₘ s)) : nodup s := (nodup_cons.1 h).2

theorem nodup.not_mem (h : nodup (a ::ₘ s)) : a ∉ s := (nodup_cons.1 h).1

theorem nodup_of_le {s t : multiset α} (h : s ≤ t) : nodup t → nodup s :=
le_induction_on h $ λ l₁ l₂, nodup.sublist

theorem not_nodup_pair : ∀ a : α, ¬ nodup (a ::ₘ a ::ₘ 0) := not_nodup_pair

theorem nodup_iff_le {s : multiset α} : nodup s ↔ ∀ a : α, ¬ a ::ₘ a ::ₘ 0 ≤ s :=
quot.induction_on s $ λ l, nodup_iff_sublist.trans $ forall_congr $ λ a,
  (@replicate_le_coe _ a 2 _).symm.not

lemma nodup_iff_ne_cons_cons {s : multiset α} : s.nodup ↔ ∀ a t, s ≠ a ::ₘ a ::ₘ t :=
nodup_iff_le.trans
  ⟨λ h a t s_eq, h a (s_eq.symm ▸ cons_le_cons a (cons_le_cons a (zero_le _))),
   λ h a le, let ⟨t, s_eq⟩ := le_iff_exists_add.mp le in
     h a t (by rwa [cons_add, cons_add, zero_add] at s_eq )⟩

theorem nodup_iff_count_le_one [decidable_eq α] {s : multiset α} : nodup s ↔ ∀ a, count a s ≤ 1 :=
quot.induction_on s $ λ l, nodup_iff_count_le_one

@[simp] theorem count_eq_one_of_mem [decidable_eq α] {a : α} {s : multiset α}
  (d : nodup s) (h : a ∈ s) : count a s = 1 :=
le_antisymm (nodup_iff_count_le_one.1 d a) (count_pos.2 h)

lemma count_eq_of_nodup [decidable_eq α] {a : α} {s : multiset α}
  (d : nodup s) : count a s = if a ∈ s then 1 else 0 :=
begin
  split_ifs with h,
  { exact count_eq_one_of_mem d h },
  { exact count_eq_zero_of_not_mem h },
end

lemma nodup_iff_pairwise {α} {s : multiset α} : nodup s ↔ pairwise (≠) s :=
quotient.induction_on s $ λ l, (pairwise_coe_iff_pairwise (by exact λ a b, ne.symm)).symm

protected lemma nodup.pairwise : (∀ a ∈ s, ∀ b ∈ s, a ≠ b → r a b) → nodup s → pairwise r s :=
quotient.induction_on s $ assume l h hl, ⟨l, rfl, hl.imp_of_mem $ assume a b ha hb, h a ha b hb⟩

lemma pairwise.forall (H : symmetric r) (hs : pairwise r s) :
  ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ≠ b → r a b :=
let ⟨l, hl₁, hl₂⟩ := hs in hl₁.symm ▸ hl₂.forall H

theorem nodup_add {s t : multiset α} : nodup (s + t) ↔ nodup s ∧ nodup t ∧ disjoint s t :=
quotient.induction_on₂ s t $ λ l₁ l₂, nodup_append

theorem disjoint_of_nodup_add {s t : multiset α} (d : nodup (s + t)) : disjoint s t :=
(nodup_add.1 d).2.2

lemma nodup.add_iff (d₁ : nodup s) (d₂ : nodup t) : nodup (s + t) ↔ disjoint s t :=
by simp [nodup_add, d₁, d₂]

lemma nodup.of_map (f : α → β) : nodup (map f s) → nodup s :=
quot.induction_on s $ λ l, nodup.of_map f

lemma nodup.map_on {f : α → β} : (∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y) →
  nodup s → nodup (map f s) :=
quot.induction_on s $ λ l, nodup.map_on

lemma nodup.map {f : α → β} {s : multiset α} (hf : injective f) : nodup s → nodup (map f s) :=
nodup.map_on (λ x _ y _ h, hf h)

theorem inj_on_of_nodup_map {f : α → β} {s : multiset α} :
  nodup (map f s) → ∀ (x ∈ s) (y ∈ s), f x = f y → x = y :=
quot.induction_on s $ λ l, inj_on_of_nodup_map

theorem nodup_map_iff_inj_on {f : α → β} {s : multiset α} (d : nodup s) :
  nodup (map f s) ↔ (∀ (x ∈ s) (y ∈ s), f x = f y → x = y) :=
⟨inj_on_of_nodup_map, λ h, d.map_on h⟩

lemma nodup.filter (p : α → Prop) [decidable_pred p] {s} : nodup s → nodup (filter p s) :=
quot.induction_on s $ λ l, nodup.filter p

@[simp] theorem nodup_attach {s : multiset α} : nodup (attach s) ↔ nodup s :=
quot.induction_on s $ λ l, nodup_attach

lemma nodup.pmap {p : α → Prop} {f : Π a, p a → β} {s : multiset α} {H}
  (hf : ∀ a ha b hb, f a ha = f b hb → a = b) : nodup s → nodup (pmap f s H) :=
quot.induction_on s (λ l H, nodup.pmap hf) H

instance nodup_decidable [decidable_eq α] (s : multiset α) : decidable (nodup s) :=
quotient.rec_on_subsingleton s $ λ l, l.nodup_decidable

lemma nodup.erase_eq_filter [decidable_eq α] (a : α) {s} : nodup s → s.erase a = filter (≠ a) s :=
quot.induction_on s $ λ l d, congr_arg coe $ d.erase_eq_filter a

lemma nodup.erase [decidable_eq α] (a : α) {l} : nodup l → nodup (l.erase a) :=
nodup_of_le (erase_le _ _)

lemma nodup.mem_erase_iff [decidable_eq α] {a b : α} {l} (d : nodup l) :
  a ∈ l.erase b ↔ a ≠ b ∧ a ∈ l :=
by rw [d.erase_eq_filter b, mem_filter, and_comm]

lemma nodup.not_mem_erase [decidable_eq α] {a : α} {s} (h : nodup s) : a ∉ s.erase a :=
λ ha, (h.mem_erase_iff.1 ha).1 rfl

protected lemma nodup.product {t : multiset β} : nodup s → nodup t → nodup (product s t) :=
quotient.induction_on₂ s t $ λ l₁ l₂ d₁ d₂, by simp [d₁.product d₂]

protected lemma nodup.sigma {σ : α → Type*} {t : Π a, multiset (σ a)} :
  nodup s → (∀ a, nodup (t a)) → nodup (s.sigma t) :=
quot.induction_on s $ assume l₁,
begin
  choose f hf using assume a, quotient.exists_rep (t a),
  rw show t = λ a, f a, from (eq.symm $ funext $ λ a, hf a),
  simpa using nodup.sigma
end

protected lemma nodup.filter_map (f : α → option β) (H : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a') :
  nodup s → nodup (filter_map f s) :=
quot.induction_on s $ λ l, nodup.filter_map H

theorem nodup_range (n : ℕ) : nodup (range n) := nodup_range _

lemma nodup.inter_left [decidable_eq α] (t) : nodup s → nodup (s ∩ t) :=
nodup_of_le $ inter_le_left _ _

lemma nodup.inter_right [decidable_eq α] (s) : nodup t → nodup (s ∩ t) :=
nodup_of_le $ inter_le_right _ _

@[simp] theorem nodup_union [decidable_eq α] {s t : multiset α} :
  nodup (s ∪ t) ↔ nodup s ∧ nodup t :=
⟨λ h, ⟨nodup_of_le (le_union_left _ _) h, nodup_of_le (le_union_right _ _) h⟩,
 λ ⟨h₁, h₂⟩, nodup_iff_count_le_one.2 $ λ a, by rw [count_union]; exact
   max_le (nodup_iff_count_le_one.1 h₁ a) (nodup_iff_count_le_one.1 h₂ a)⟩

@[simp] lemma nodup_bind {s : multiset α} {t : α → multiset β} :
  nodup (bind s t) ↔ ((∀a∈s, nodup (t a)) ∧ (s.pairwise (λa b, disjoint (t a) (t b)))) :=
have h₁ : ∀a, ∃l:list β, t a = l, from
  assume a, quot.induction_on (t a) $ assume l, ⟨l, rfl⟩,
let ⟨t', h'⟩ := classical.axiom_of_choice h₁ in
have t = λa, t' a, from funext h',
have hd : symmetric (λa b, list.disjoint (t' a) (t' b)), from assume a b h, h.symm,
quot.induction_on s $ by simp [this, list.nodup_bind, pairwise_coe_iff_pairwise hd]

lemma nodup.ext {s t : multiset α} : nodup s → nodup t → (s = t ↔ ∀ a, a ∈ s ↔ a ∈ t) :=
quotient.induction_on₂ s t $ λ l₁ l₂ d₁ d₂, quotient.eq.trans $ perm_ext d₁ d₂

theorem le_iff_subset {s t : multiset α} : nodup s → (s ≤ t ↔ s ⊆ t) :=
quotient.induction_on₂ s t $ λ l₁ l₂ d, ⟨subset_of_le, d.subperm⟩

theorem range_le {m n : ℕ} : range m ≤ range n ↔ m ≤ n :=
(le_iff_subset (nodup_range _)).trans range_subset

theorem mem_sub_of_nodup [decidable_eq α] {a : α} {s t : multiset α} (d : nodup s) :
  a ∈ s - t ↔ a ∈ s ∧ a ∉ t :=
⟨λ h, ⟨mem_of_le tsub_le_self h, λ h',
  by refine count_eq_zero.1 _ h; rw [count_sub a s t, tsub_eq_zero_iff_le];
     exact le_trans (nodup_iff_count_le_one.1 d _) (count_pos.2 h')⟩,
 λ ⟨h₁, h₂⟩, or.resolve_right (mem_add.1 $ mem_of_le le_tsub_add h₁) h₂⟩

lemma map_eq_map_of_bij_of_nodup (f : α → γ) (g : β → γ) {s : multiset α} {t : multiset β}
  (hs : s.nodup) (ht : t.nodup) (i : Πa∈s, β)
  (hi : ∀a ha, i a ha ∈ t) (h : ∀a ha, f a = g (i a ha))
  (i_inj : ∀a₁ a₂ ha₁ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
  (i_surj : ∀b∈t, ∃a ha, b = i a ha) :
  s.map f = t.map g :=
have t = s.attach.map (λ x, i x x.2),
  from (ht.ext $ (nodup_attach.2 hs).map $
      show injective (λ x : {x // x ∈ s}, i x x.2), from λ x y hxy,
        subtype.ext $ i_inj x y x.2 y.2 hxy).2
    (λ x, by simp only [mem_map, true_and, subtype.exists, eq_comm, mem_attach];
      exact ⟨i_surj _, λ ⟨y, hy⟩, hy.snd.symm ▸ hi _ _⟩),
calc s.map f = s.pmap (λ x _, f x) (λ _, id) : by rw [pmap_eq_map]
... = s.attach.map (λ x, f x) : by rw [pmap_eq_map_attach]
... = t.map g : by rw [this, multiset.map_map]; exact map_congr rfl (λ x _, h _ _)

end multiset
