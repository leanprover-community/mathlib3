/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau
-/
import data.list.lattice
import data.list.pairwise
import data.list.forall2

/-!
# Lists with no duplicates

`list.nodup` is defined in `data/list/defs`. In this file we prove various properties of this
predicate.
-/

universes u v

open nat function

variables {α : Type u} {β : Type v}

namespace list

@[simp] theorem forall_mem_ne {a : α} {l : list α} : (∀ (a' : α), a' ∈ l → ¬a = a') ↔ a ∉ l :=
⟨λ h m, h _ m rfl, λ h a' m e, h (e.symm ▸ m)⟩

@[simp] theorem nodup_nil : @nodup α [] := pairwise.nil

@[simp] theorem nodup_cons {a : α} {l : list α} : nodup (a::l) ↔ a ∉ l ∧ nodup l :=
by simp only [nodup, pairwise_cons, forall_mem_ne]

protected lemma pairwise.nodup {l : list α} {r : α → α → Prop} [is_irrefl α r] (h : pairwise r l) :
  nodup l :=
h.imp $ λ a b, ne_of_irrefl

lemma rel_nodup {r : α → β → Prop} (hr : relator.bi_unique r) : (forall₂ r ⇒ (↔)) nodup nodup
| _ _ forall₂.nil      := by simp only [nodup_nil]
| _ _ (forall₂.cons hab h) :=
  by simpa only [nodup_cons] using relator.rel_and (relator.rel_not (rel_mem hr hab h))
    (rel_nodup h)

theorem nodup_cons_of_nodup {a : α} {l : list α} (m : a ∉ l) (n : nodup l) : nodup (a::l) :=
nodup_cons.2 ⟨m, n⟩

theorem nodup_singleton (a : α) : nodup [a] :=
nodup_cons_of_nodup (not_mem_nil a) nodup_nil

theorem nodup_of_nodup_cons {a : α} {l : list α} (h : nodup (a::l)) : nodup l :=
(nodup_cons.1 h).2

theorem not_mem_of_nodup_cons {a : α} {l : list α} (h : nodup (a::l)) : a ∉ l :=
(nodup_cons.1 h).1

theorem not_nodup_cons_of_mem {a : α} {l : list α} : a ∈ l → ¬ nodup (a :: l) :=
imp_not_comm.1 not_mem_of_nodup_cons

theorem nodup_of_sublist {l₁ l₂ : list α} : l₁ <+ l₂ → nodup l₂ → nodup l₁ :=
pairwise_of_sublist

theorem not_nodup_pair (a : α) : ¬ nodup [a, a] :=
not_nodup_cons_of_mem $ mem_singleton_self _

theorem nodup_iff_sublist {l : list α} : nodup l ↔ ∀ a, ¬ [a, a] <+ l :=
⟨λ d a h, not_nodup_pair a (nodup_of_sublist h d), begin
  induction l with a l IH; intro h, {exact nodup_nil},
  exact nodup_cons_of_nodup
    (λ al, h a $ cons_sublist_cons _ $ singleton_sublist.2 al)
    (IH $ λ a s, h a $ sublist_cons_of_sublist _ s)
end⟩

theorem nodup_iff_nth_le_inj {l : list α} :
  nodup l ↔ ∀ i j h₁ h₂, nth_le l i h₁ = nth_le l j h₂ → i = j :=
pairwise_iff_nth_le.trans
⟨λ H i j h₁ h₂ h, ((lt_trichotomy _ _)
  .resolve_left (λ h', H _ _ h₂ h' h))
  .resolve_right (λ h', H _ _ h₁ h' h.symm),
 λ H i j h₁ h₂ h, ne_of_lt h₂ (H _ _ _ _ h)⟩

theorem nodup.nth_le_inj_iff {α : Type*} {l : list α} (h : nodup l)
  {i j : ℕ} (hi : i < l.length) (hj : j < l.length) :
  l.nth_le i hi = l.nth_le j hj ↔ i = j :=
⟨nodup_iff_nth_le_inj.mp h _ _ _ _, by simp {contextual := tt}⟩

lemma nodup.ne_singleton_iff {l : list α} (h : nodup l) (x : α) :
  l ≠ [x] ↔ l = [] ∨ ∃ y ∈ l, y ≠ x :=
begin
  induction l with hd tl hl,
  { simp },
  { specialize hl (nodup_of_nodup_cons h),
    by_cases hx : tl = [x],
    { simpa [hx, and.comm, and_or_distrib_left] using h },
    { rw [←ne.def, hl] at hx,
      rcases hx with rfl | ⟨y, hy, hx⟩,
      { simp },
      { have : tl ≠ [] := ne_nil_of_mem hy,
        suffices : ∃ (y : α) (H : y ∈ hd :: tl), y ≠ x,
          { simpa [ne_nil_of_mem hy] },
        exact ⟨y, mem_cons_of_mem _ hy, hx⟩ } } }
end

lemma nth_le_eq_of_ne_imp_not_nodup (xs : list α) (n m : ℕ) (hn : n < xs.length)
  (hm : m < xs.length) (h : xs.nth_le n hn = xs.nth_le m hm) (hne : n ≠ m) :
  ¬ nodup xs :=
begin
  rw nodup_iff_nth_le_inj,
  simp only [exists_prop, exists_and_distrib_right, not_forall],
  exact ⟨n, m, ⟨hn, hm, h⟩, hne⟩
end

@[simp] theorem nth_le_index_of [decidable_eq α] {l : list α} (H : nodup l) (n h) :
  index_of (nth_le l n h) l = n :=
nodup_iff_nth_le_inj.1 H _ _ _ h $
index_of_nth_le $ index_of_lt_length.2 $ nth_le_mem _ _ _

theorem nodup_iff_count_le_one [decidable_eq α] {l : list α} : nodup l ↔ ∀ a, count a l ≤ 1 :=
nodup_iff_sublist.trans $ forall_congr $ λ a,
have [a, a] <+ l ↔ 1 < count a l, from (@le_count_iff_repeat_sublist _ _ a l 2).symm,
(not_congr this).trans not_lt

theorem nodup_repeat (a : α) : ∀ {n : ℕ}, nodup (repeat a n) ↔ n ≤ 1
| 0 := by simp [nat.zero_le]
| 1 := by simp
| (n+2) := iff_of_false
  (λ H, nodup_iff_sublist.1 H a ((repeat_sublist_repeat _).2 (nat.le_add_left 2 n)))
  (not_le_of_lt $ nat.le_add_left 2 n)

@[simp] theorem count_eq_one_of_mem [decidable_eq α] {a : α} {l : list α}
  (d : nodup l) (h : a ∈ l) : count a l = 1 :=
le_antisymm (nodup_iff_count_le_one.1 d a) (count_pos.2 h)

theorem nodup_of_nodup_append_left {l₁ l₂ : list α} : nodup (l₁++l₂) → nodup l₁ :=
nodup_of_sublist (sublist_append_left l₁ l₂)

theorem nodup_of_nodup_append_right {l₁ l₂ : list α} : nodup (l₁++l₂) → nodup l₂ :=
nodup_of_sublist (sublist_append_right l₁ l₂)

theorem nodup_append {l₁ l₂ : list α} : nodup (l₁++l₂) ↔ nodup l₁ ∧ nodup l₂ ∧ disjoint l₁ l₂ :=
by simp only [nodup, pairwise_append, disjoint_iff_ne]

theorem disjoint_of_nodup_append {l₁ l₂ : list α} (d : nodup (l₁++l₂)) : disjoint l₁ l₂ :=
(nodup_append.1 d).2.2

theorem nodup_append_of_nodup {l₁ l₂ : list α} (d₁ : nodup l₁) (d₂ : nodup l₂)
  (dj : disjoint l₁ l₂) : nodup (l₁++l₂) :=
nodup_append.2 ⟨d₁, d₂, dj⟩

theorem nodup_append_comm {l₁ l₂ : list α} : nodup (l₁++l₂) ↔ nodup (l₂++l₁) :=
by simp only [nodup_append, and.left_comm, disjoint_comm]

theorem nodup_middle {a : α} {l₁ l₂ : list α} : nodup (l₁ ++ a::l₂) ↔ nodup (a::(l₁++l₂)) :=
by simp only [nodup_append, not_or_distrib, and.left_comm, and_assoc, nodup_cons, mem_append,
  disjoint_cons_right]

theorem nodup_of_nodup_map (f : α → β) {l : list α} : nodup (map f l) → nodup l :=
pairwise_of_pairwise_map f $ λ a b, mt $ congr_arg f

theorem nodup_map_on {f : α → β} {l : list α} (H : ∀x∈l, ∀y∈l, f x = f y → x = y)
  (d : nodup l) : nodup (map f l) :=
pairwise_map_of_pairwise _ (by exact λ a b ⟨ma, mb, n⟩ e, n (H a ma b mb e)) (pairwise.and_mem.1 d)

theorem inj_on_of_nodup_map {f : α → β} {l : list α} (d : nodup (map f l)) :
  ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → f x = f y → x = y :=
begin
  induction l with hd tl ih,
  { simp },
  { simp only [map, nodup_cons, mem_map, not_exists, not_and, ←ne.def] at d,
    rintro _ (rfl | h₁) _ (rfl | h₂) h₃,
    { refl },
    { apply (d.1 _ h₂ h₃.symm).elim },
    { apply (d.1 _ h₁ h₃).elim },
    { apply ih d.2 h₁ h₂ h₃ } }
end

theorem nodup_map_iff_inj_on {f : α → β} {l : list α} (d : nodup l) :
  nodup (map f l) ↔ (∀ (x ∈ l) (y ∈ l), f x = f y → x = y) :=
⟨inj_on_of_nodup_map, λ h, nodup_map_on h d⟩

theorem nodup_map {f : α → β} {l : list α} (hf : injective f) : nodup l → nodup (map f l) :=
nodup_map_on (assume x _ y _ h, hf h)

theorem nodup_map_iff {f : α → β} {l : list α} (hf : injective f) : nodup (map f l) ↔ nodup l :=
⟨nodup_of_nodup_map _, nodup_map hf⟩

@[simp] theorem nodup_attach {l : list α} : nodup (attach l) ↔ nodup l :=
⟨λ h, attach_map_val l ▸ nodup_map (λ a b, subtype.eq) h,
 λ h, nodup_of_nodup_map subtype.val ((attach_map_val l).symm ▸ h)⟩

theorem nodup_pmap {p : α → Prop} {f : Π a, p a → β} {l : list α} {H}
  (hf : ∀ a ha b hb, f a ha = f b hb → a = b) (h : nodup l) : nodup (pmap f l H) :=
by rw [pmap_eq_map_attach]; exact nodup_map
  (λ ⟨a, ha⟩ ⟨b, hb⟩ h, by congr; exact hf a (H _ ha) b (H _ hb) h)
  (nodup_attach.2 h)

theorem nodup_filter (p : α → Prop) [decidable_pred p] {l} : nodup l → nodup (filter p l) :=
pairwise_filter_of_pairwise p

@[simp] theorem nodup_reverse {l : list α} : nodup (reverse l) ↔ nodup l :=
pairwise_reverse.trans $ by simp only [nodup, ne.def, eq_comm]

theorem nodup_erase_eq_filter [decidable_eq α] (a : α) {l} (d : nodup l) :
  l.erase a = filter (≠ a) l :=
begin
  induction d with b l m d IH, {refl},
  by_cases b = a,
  { subst h, rw [erase_cons_head, filter_cons_of_neg],
    symmetry, rw filter_eq_self, simpa only [ne.def, eq_comm] using m, exact not_not_intro rfl },
  { rw [erase_cons_tail _ h, filter_cons_of_pos, IH], exact h }
end

theorem nodup_erase_of_nodup [decidable_eq α] (a : α) {l} : nodup l → nodup (l.erase a) :=
nodup_of_sublist (erase_sublist _ _)

theorem nodup_diff [decidable_eq α] : ∀ {l₁ l₂ : list α} (h : l₁.nodup), (l₁.diff l₂).nodup
| l₁ []      h := h
| l₁ (a::l₂) h := by rw diff_cons; exact nodup_diff (nodup_erase_of_nodup _ h)

theorem mem_erase_iff_of_nodup [decidable_eq α] {a b : α} {l} (d : nodup l) :
  a ∈ l.erase b ↔ a ≠ b ∧ a ∈ l :=
by rw nodup_erase_eq_filter b d; simp only [mem_filter, and_comm]

theorem mem_erase_of_nodup [decidable_eq α] {a : α} {l} (h : nodup l) : a ∉ l.erase a :=
λ H, ((mem_erase_iff_of_nodup h).1 H).1 rfl

theorem nodup_join {L : list (list α)} :
  nodup (join L) ↔ (∀ l ∈ L, nodup l) ∧ pairwise disjoint L :=
by simp only [nodup, pairwise_join, disjoint_left.symm, forall_mem_ne]

theorem nodup_bind {l₁ : list α} {f : α → list β} : nodup (l₁.bind f) ↔
  (∀ x ∈ l₁, nodup (f x)) ∧ pairwise (λ (a b : α), disjoint (f a) (f b)) l₁ :=
by simp only [list.bind, nodup_join, pairwise_map, and_comm, and.left_comm, mem_map,
  exists_imp_distrib, and_imp];
   rw [show (∀ (l : list β) (x : α), f x = l → x ∈ l₁ → nodup l) ↔
            (∀ (x : α), x ∈ l₁ → nodup (f x)),
       from forall_swap.trans $ forall_congr $ λ_, forall_eq']

theorem nodup_product {l₁ : list α} {l₂ : list β} (d₁ : nodup l₁) (d₂ : nodup l₂) :
  nodup (product l₁ l₂) :=
 nodup_bind.2
  ⟨λ a ma, nodup_map (left_inverse.injective (λ b, (rfl : (a,b).2 = b))) d₂,
  d₁.imp $ λ a₁ a₂ n x h₁ h₂, begin
    rcases mem_map.1 h₁ with ⟨b₁, mb₁, rfl⟩,
    rcases mem_map.1 h₂ with ⟨b₂, mb₂, ⟨⟩⟩,
    exact n rfl
  end⟩

theorem nodup_sigma {σ : α → Type*} {l₁ : list α} {l₂ : Π a, list (σ a)}
  (d₁ : nodup l₁) (d₂ : ∀ a, nodup (l₂ a)) : nodup (l₁.sigma l₂) :=
 nodup_bind.2
  ⟨λ a ma, nodup_map (λ b b' h, by injection h with _ h; exact eq_of_heq h) (d₂ a),
  d₁.imp $ λ a₁ a₂ n x h₁ h₂, begin
    rcases mem_map.1 h₁ with ⟨b₁, mb₁, rfl⟩,
    rcases mem_map.1 h₂ with ⟨b₂, mb₂, ⟨⟩⟩,
    exact n rfl
  end⟩

theorem nodup_filter_map {f : α → option β} {l : list α}
  (H : ∀ (a a' : α) (b : β), b ∈ f a → b ∈ f a' → a = a') :
  nodup l → nodup (filter_map f l) :=
pairwise_filter_map_of_pairwise f $ λ a a' n b bm b' bm' e, n $ H a a' b' (e ▸ bm) bm'

theorem nodup_concat {a : α} {l : list α} (h : a ∉ l) (h' : nodup l) : nodup (concat l a) :=
by rw concat_eq_append; exact nodup_append_of_nodup h' (nodup_singleton _) (disjoint_singleton.2 h)

theorem nodup_insert [decidable_eq α] {a : α} {l : list α} (h : nodup l) : nodup (insert a l) :=
if h' : a ∈ l then by rw [insert_of_mem h']; exact h
else by rw [insert_of_not_mem h', nodup_cons]; split; assumption

theorem nodup_union [decidable_eq α] (l₁ : list α) {l₂ : list α} (h : nodup l₂) :
  nodup (l₁ ∪ l₂) :=
begin
  induction l₁ with a l₁ ih generalizing l₂,
  { exact h },
  apply nodup_insert,
  exact ih h
end

theorem nodup_inter_of_nodup [decidable_eq α] {l₁ : list α} (l₂) : nodup l₁ → nodup (l₁ ∩ l₂) :=
nodup_filter _

@[simp] theorem nodup_sublists {l : list α} : nodup (sublists l) ↔ nodup l :=
⟨λ h, nodup_of_nodup_map _ (nodup_of_sublist (map_ret_sublist_sublists _) h),
 λ h, (pairwise_sublists h).imp (λ _ _ h, mt reverse_inj.2 h.to_ne)⟩

@[simp] theorem nodup_sublists' {l : list α} : nodup (sublists' l) ↔ nodup l :=
by rw [sublists'_eq_sublists, nodup_map_iff reverse_injective,
       nodup_sublists, nodup_reverse]

lemma nodup_sublists_len {α : Type*} (n) {l : list α}
  (nd : nodup l) : (sublists_len n l).nodup :=
nodup_of_sublist (sublists_len_sublist_sublists' _ _) (nodup_sublists'.2 nd)

lemma diff_eq_filter_of_nodup [decidable_eq α] :
  ∀ {l₁ l₂ : list α} (hl₁ : l₁.nodup), l₁.diff l₂ = l₁.filter (∉ l₂)
| l₁ []      hl₁ := by simp
| l₁ (a::l₂) hl₁ :=
begin
  rw [diff_cons, diff_eq_filter_of_nodup (nodup_erase_of_nodup _ hl₁),
    nodup_erase_eq_filter _ hl₁, filter_filter],
  simp only [mem_cons_iff, not_or_distrib, and.comm],
  congr
end

lemma mem_diff_iff_of_nodup [decidable_eq α] {l₁ l₂ : list α} (hl₁ : l₁.nodup) {a : α} :
  a ∈ l₁.diff l₂ ↔ a ∈ l₁ ∧ a ∉ l₂ :=
by rw [diff_eq_filter_of_nodup hl₁, mem_filter]

lemma nodup_update_nth : ∀ {l : list α} {n : ℕ} {a : α} (hl : l.nodup) (ha : a ∉ l),
  (l.update_nth n a).nodup
| []     n     a hl ha := nodup_nil
| (b::l) 0     a hl ha := nodup_cons.2 ⟨mt (mem_cons_of_mem _) ha, (nodup_cons.1 hl).2⟩
| (b::l) (n+1) a hl ha := nodup_cons.2
  ⟨λ h, (mem_or_eq_of_mem_update_nth h).elim
      (nodup_cons.1 hl).1
      (λ hba, ha (hba ▸ mem_cons_self _ _)),
    nodup_update_nth (nodup_cons.1 hl).2 (mt (mem_cons_of_mem _) ha)⟩

lemma nodup.map_update [decidable_eq α] {l : list α} (hl : l.nodup) (f : α → β) (x : α) (y : β) :
  l.map (function.update f x y) =
    if x ∈ l then (l.map f).update_nth (l.index_of x) y else l.map f :=
begin
  induction l with hd tl ihl, { simp },
  rw [nodup_cons] at hl,
  simp only [mem_cons_iff, map, ihl hl.2],
  by_cases H : hd = x,
  { subst hd,
    simp [update_nth, hl.1] },
  { simp [ne.symm H, H, update_nth, ← apply_ite (cons (f hd))] }
end

lemma nodup.pairwise_of_forall_ne {l : list α} {r : α → α → Prop}
  (hl : l.nodup) (h : ∀ (a ∈ l) (b ∈ l), a ≠ b → r a b) : l.pairwise r :=
begin
  classical,
  refine pairwise_of_reflexive_on_dupl_of_forall_ne _ h,
  intros x hx,
  rw nodup_iff_count_le_one at hl,
  exact absurd (hl x) hx.not_le
end

lemma nodup.pairwise_of_set_pairwise_on {l : list α} {r : α → α → Prop}
  (hl : l.nodup) (h : {x | x ∈ l}.pairwise_on r) : l.pairwise r :=
hl.pairwise_of_forall_ne h

end list

theorem option.to_list_nodup {α} : ∀ o : option α, o.to_list.nodup
| none     := list.nodup_nil
| (some x) := list.nodup_singleton x
