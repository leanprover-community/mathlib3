/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau
-/
import data.list.lattice
import data.list.pairwise
import data.list.forall2
import data.set.pairwise

/-!
# Lists with no duplicates

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

`list.nodup` is defined in `data/list/defs`. In this file we prove various properties of this
predicate.
-/

universes u v

open nat function

variables {α : Type u} {β : Type v} {l l₁ l₂ : list α} {r : α → α → Prop} {a b : α}

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

protected lemma nodup.cons (ha : a ∉ l) (hl : nodup l) : nodup (a :: l) := nodup_cons.2 ⟨ha, hl⟩

lemma nodup_singleton (a : α) : nodup [a] := pairwise_singleton _ _

lemma nodup.of_cons (h : nodup (a :: l)) : nodup l := (nodup_cons.1 h).2
lemma nodup.not_mem (h : (a :: l).nodup) : a ∉ l := (nodup_cons.1 h).1

lemma not_nodup_cons_of_mem : a ∈ l → ¬ nodup (a :: l) := imp_not_comm.1 nodup.not_mem

protected lemma nodup.sublist : l₁ <+ l₂ → nodup l₂ → nodup l₁ := pairwise.sublist

theorem not_nodup_pair (a : α) : ¬ nodup [a, a] :=
not_nodup_cons_of_mem $ mem_singleton_self _

theorem nodup_iff_sublist {l : list α} : nodup l ↔ ∀ a, ¬ [a, a] <+ l :=
⟨λ d a h, not_nodup_pair a (d.sublist h), begin
  induction l with a l IH; intro h, {exact nodup_nil},
  exact (IH $ λ a s, h a $ sublist_cons_of_sublist _ s).cons
    (λ al, h a $ (singleton_sublist.2 al).cons_cons _)
end⟩

theorem nodup_iff_nth_le_inj {l : list α} :
  nodup l ↔ ∀ i j h₁ h₂, nth_le l i h₁ = nth_le l j h₂ → i = j :=
pairwise_iff_nth_le.trans
⟨λ H i j h₁ h₂ h, ((lt_trichotomy _ _)
  .resolve_left (λ h', H _ _ h₂ h' h))
  .resolve_right (λ h', H _ _ h₁ h' h.symm),
 λ H i j h₁ h₂ h, ne_of_lt h₂ (H _ _ _ _ h)⟩

theorem nodup.nth_le_inj_iff {l : list α} (h : nodup l)
  {i j : ℕ} (hi : i < l.length) (hj : j < l.length) :
  l.nth_le i hi = l.nth_le j hj ↔ i = j :=
⟨nodup_iff_nth_le_inj.mp h _ _ _ _, by simp {contextual := tt}⟩

lemma nodup_iff_nth_ne_nth {l : list α} :
  l.nodup ↔ ∀ (i j : ℕ), i < j → j < l.length → l.nth i ≠ l.nth j :=
begin
  rw nodup_iff_nth_le_inj,
  simp only [nth_le_eq_iff, some_nth_le_eq],
  split; rintro h i j h₁ h₂,
  { exact mt (h i j (h₁.trans h₂) h₂) (ne_of_lt h₁) },
  { intro h₃,
    by_contra h₄,
    cases lt_or_gt_of_ne h₄ with h₅ h₅,
    { exact h i j h₅ h₂ h₃ },
    { exact h j i h₅ h₁ h₃.symm }},
end

lemma nodup.ne_singleton_iff {l : list α} (h : nodup l) (x : α) :
  l ≠ [x] ↔ l = [] ∨ ∃ y ∈ l, y ≠ x :=
begin
  induction l with hd tl hl,
  { simp },
  { specialize hl h.of_cons,
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
have [a, a] <+ l ↔ 1 < count a l, from (@le_count_iff_replicate_sublist _ _ a l 2).symm,
(not_congr this).trans not_lt

theorem nodup_replicate (a : α) : ∀ {n : ℕ}, nodup (replicate n a) ↔ n ≤ 1
| 0 := by simp [nat.zero_le]
| 1 := by simp
| (n+2) := iff_of_false
  (λ H, nodup_iff_sublist.1 H a ((replicate_sublist_replicate _).2 (nat.le_add_left 2 n)))
  (not_le_of_lt $ nat.le_add_left 2 n)

@[simp] theorem count_eq_one_of_mem [decidable_eq α] {a : α} {l : list α}
  (d : nodup l) (h : a ∈ l) : count a l = 1 :=
le_antisymm (nodup_iff_count_le_one.1 d a) (count_pos.2 h)

lemma count_eq_of_nodup [decidable_eq α] {a : α} {l : list α}
  (d : nodup l) : count a l = if a ∈ l then 1 else 0 :=
begin
  split_ifs with h,
  { exact count_eq_one_of_mem d h },
  { exact count_eq_zero_of_not_mem h },
end

lemma nodup.of_append_left : nodup (l₁ ++ l₂) → nodup l₁ :=
nodup.sublist (sublist_append_left l₁ l₂)

lemma nodup.of_append_right : nodup (l₁ ++ l₂) → nodup l₂ :=
nodup.sublist (sublist_append_right l₁ l₂)

theorem nodup_append {l₁ l₂ : list α} : nodup (l₁++l₂) ↔ nodup l₁ ∧ nodup l₂ ∧ disjoint l₁ l₂ :=
by simp only [nodup, pairwise_append, disjoint_iff_ne]

theorem disjoint_of_nodup_append {l₁ l₂ : list α} (d : nodup (l₁++l₂)) : disjoint l₁ l₂ :=
(nodup_append.1 d).2.2

lemma nodup.append (d₁ : nodup l₁) (d₂ : nodup l₂) (dj : disjoint l₁ l₂) : nodup (l₁ ++ l₂) :=
nodup_append.2 ⟨d₁, d₂, dj⟩

theorem nodup_append_comm {l₁ l₂ : list α} : nodup (l₁++l₂) ↔ nodup (l₂++l₁) :=
by simp only [nodup_append, and.left_comm, disjoint_comm]

theorem nodup_middle {a : α} {l₁ l₂ : list α} : nodup (l₁ ++ a::l₂) ↔ nodup (a::(l₁++l₂)) :=
by simp only [nodup_append, not_or_distrib, and.left_comm, and_assoc, nodup_cons, mem_append,
  disjoint_cons_right]

lemma nodup.of_map (f : α → β) {l : list α} : nodup (map f l) → nodup l :=
pairwise.of_map f $ λ a b, mt $ congr_arg f

lemma nodup.map_on {f : α → β} (H : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) (d : nodup l) :
  (map f l).nodup :=
pairwise.map _ (by exact λ a b ⟨ma, mb, n⟩ e, n (H a ma b mb e)) (pairwise.and_mem.1 d)

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
⟨inj_on_of_nodup_map, λ h, d.map_on h⟩

protected lemma nodup.map {f : α → β} (hf : injective f) : nodup l → nodup (map f l) :=
nodup.map_on (assume x _ y _ h, hf h)

theorem nodup_map_iff {f : α → β} {l : list α} (hf : injective f) : nodup (map f l) ↔ nodup l :=
⟨nodup.of_map _, nodup.map hf⟩

@[simp] theorem nodup_attach {l : list α} : nodup (attach l) ↔ nodup l :=
⟨λ h, attach_map_val l ▸ h.map (λ a b, subtype.eq),
  λ h, nodup.of_map subtype.val ((attach_map_val l).symm ▸ h)⟩

alias nodup_attach ↔ nodup.of_attach nodup.attach

attribute [protected] nodup.attach

lemma nodup.pmap {p : α → Prop} {f : Π a, p a → β} {l : list α} {H}
  (hf : ∀ a ha b hb, f a ha = f b hb → a = b) (h : nodup l) : nodup (pmap f l H) :=
by rw [pmap_eq_map_attach]; exact h.attach.map
  (λ ⟨a, ha⟩ ⟨b, hb⟩ h, by congr; exact hf a (H _ ha) b (H _ hb) h)

lemma nodup.filter (p : α → Prop) [decidable_pred p] {l} : nodup l → nodup (filter p l) :=
pairwise.filter p

@[simp] theorem nodup_reverse {l : list α} : nodup (reverse l) ↔ nodup l :=
pairwise_reverse.trans $ by simp only [nodup, ne.def, eq_comm]

lemma nodup.erase_eq_filter [decidable_eq α] {l} (d : nodup l) (a : α) :
  l.erase a = filter (≠ a) l :=
begin
  induction d with b l m d IH, {refl},
  by_cases b = a,
  { subst h, rw [erase_cons_head, filter_cons_of_neg],
    symmetry, rw filter_eq_self, simpa only [ne.def, eq_comm] using m, exact not_not_intro rfl },
  { rw [erase_cons_tail _ h, filter_cons_of_pos, IH], exact h }
end

lemma nodup.erase [decidable_eq α] (a : α) : nodup l → nodup (l.erase a) :=
nodup.sublist $ erase_sublist _ _

lemma nodup.diff [decidable_eq α] : l₁.nodup → (l₁.diff l₂).nodup :=
nodup.sublist $ diff_sublist _ _

lemma nodup.mem_erase_iff [decidable_eq α] (d : nodup l) : a ∈ l.erase b ↔ a ≠ b ∧ a ∈ l :=
by rw [d.erase_eq_filter, mem_filter, and_comm]

lemma nodup.not_mem_erase [decidable_eq α] (h : nodup l) : a ∉ l.erase a :=
λ H, (h.mem_erase_iff.1 H).1 rfl

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

protected lemma nodup.product {l₂ : list β} (d₁ : l₁.nodup) (d₂ : l₂.nodup) :
  (l₁.product l₂).nodup :=
nodup_bind.2
  ⟨λ a ma, d₂.map $ left_inverse.injective $ λ b, (rfl : (a,b).2 = b),
  d₁.imp $ λ a₁ a₂ n x h₁ h₂, begin
    rcases mem_map.1 h₁ with ⟨b₁, mb₁, rfl⟩,
    rcases mem_map.1 h₂ with ⟨b₂, mb₂, ⟨⟩⟩,
    exact n rfl
  end⟩

lemma nodup.sigma {σ : α → Type*} {l₂ : Π a, list (σ a)} (d₁ : nodup l₁) (d₂ : ∀ a, nodup (l₂ a)) :
  (l₁.sigma l₂).nodup :=
nodup_bind.2
  ⟨λ a ma, (d₂ a).map (λ b b' h, by injection h with _ h; exact eq_of_heq h),
  d₁.imp $ λ a₁ a₂ n x h₁ h₂, begin
    rcases mem_map.1 h₁ with ⟨b₁, mb₁, rfl⟩,
    rcases mem_map.1 h₂ with ⟨b₂, mb₂, ⟨⟩⟩,
    exact n rfl
  end⟩

protected lemma nodup.filter_map {f : α → option β} (h : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a') :
  nodup l → nodup (filter_map f l) :=
pairwise.filter_map f $ λ a a' n b bm b' bm' e, n $ h a a' b' (e ▸ bm) bm'

protected lemma nodup.concat (h : a ∉ l) (h' : l.nodup) : (l.concat a).nodup :=
by rw concat_eq_append; exact h'.append (nodup_singleton _) (disjoint_singleton.2 h)

lemma nodup.insert [decidable_eq α] (h : l.nodup) : (insert a l).nodup :=
if h' : a ∈ l then by rw [insert_of_mem h']; exact h
else by rw [insert_of_not_mem h', nodup_cons]; split; assumption

lemma nodup.union [decidable_eq α] (l₁ : list α) (h : nodup l₂) : (l₁ ∪ l₂).nodup  :=
begin
  induction l₁ with a l₁ ih generalizing l₂,
  { exact h },
  { exact (ih h).insert }
end

lemma nodup.inter [decidable_eq α] (l₂ : list α) : nodup l₁ → nodup (l₁ ∩ l₂) := nodup.filter _

lemma nodup.diff_eq_filter [decidable_eq α] :
  ∀ {l₁ l₂ : list α} (hl₁ : l₁.nodup), l₁.diff l₂ = l₁.filter (∉ l₂)
| l₁ []      hl₁ := by simp
| l₁ (a::l₂) hl₁ :=
begin
  rw [diff_cons, (hl₁.erase _).diff_eq_filter, hl₁.erase_eq_filter, filter_filter],
  simp only [mem_cons_iff, not_or_distrib, and.comm]
end

lemma nodup.mem_diff_iff [decidable_eq α] (hl₁ : l₁.nodup) : a ∈ l₁.diff l₂ ↔ a ∈ l₁ ∧ a ∉ l₂ :=
by rw [hl₁.diff_eq_filter, mem_filter]

protected lemma nodup.update_nth : ∀ {l : list α} {n : ℕ} {a : α} (hl : l.nodup) (ha : a ∉ l),
  (l.update_nth n a).nodup
| []     n     a hl ha := nodup_nil
| (b::l) 0     a hl ha := nodup_cons.2 ⟨mt (mem_cons_of_mem _) ha, (nodup_cons.1 hl).2⟩
| (b::l) (n+1) a hl ha := nodup_cons.2
  ⟨λ h, (mem_or_eq_of_mem_update_nth h).elim
      (nodup_cons.1 hl).1
      (λ hba, ha (hba ▸ mem_cons_self _ _)), hl.of_cons.update_nth (mt (mem_cons_of_mem _) ha)⟩

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

lemma nodup.pairwise_of_set_pairwise {l : list α} {r : α → α → Prop}
  (hl : l.nodup) (h : {x | x ∈ l}.pairwise r) : l.pairwise r :=
hl.pairwise_of_forall_ne h

@[simp] lemma nodup.pairwise_coe [is_symm α r] (hl : l.nodup) :
  {a | a ∈ l}.pairwise r ↔ l.pairwise r :=
begin
  induction l with a l ih,
  { simp },
  rw list.nodup_cons at hl,
  have : ∀ b ∈ l, ¬a = b → r a b ↔ r a b :=
    λ b hb, imp_iff_right (ne_of_mem_of_not_mem hb hl.1).symm,
  simp [set.set_of_or, set.pairwise_insert_of_symmetric (@symm_of _ r _), ih hl.2, and_comm,
    forall₂_congr this],
end

end list

theorem option.to_list_nodup {α} : ∀ o : option α, o.to_list.nodup
| none     := list.nodup_nil
| (some x) := list.nodup_singleton x
