/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau, Scott Morrison, Anne Baanen
-/
import data.list.bag_inter
import data.list.chain
import data.list.nodup
import data.list.of_fn
import data.list.sort

open nat

section has_enum

/-- `has_enum α` is a typeclass stating that values in `α` between given bounds can be enumerated.

It is used to implement `Ico` and `Icc` for `list`, `multiset` and `finset`.

This typeclass is equivalent to the `Enum` typeclass in Haskell.

The fields in this typeclass are for internal use, it is preferred to use `list.Ico` instead.
-/
class has_enum (α : Type*) :=
(enum : α → α → list α)

/-- `has_enum.enum b t` is a list of the values between `b` (inclusive) and `t` (exclusive).

It is preferred to use `list.Ico` instead.
-/
add_decl_doc has_enum.enum

variables {α : Type*} [has_enum α] (b t : α)

/-- `list.Ico b t` is a list of the values between `b` (inclusive) and `t` (exclusive).
(Ico stands for "interval, closed-open".)

See also `data/set/intervals.lean` for `set.Ico`, modelling intervals in general preorders, and
`multiset.Ico` and `finset.Ico` for `n ≤ x < m` as a multiset or as a finset.
-/
def list.Ico : list α := has_enum.enum b t

@[simp] lemma has_enum.enum_eq : @has_enum.enum α _ = list.Ico := rfl

/-- `list.Icc b t` is a list of the values between `b` (inclusive) and `t` (inclusive).

Edge cases (assuming `has_lawful_enum α`):
 - if `t < b`, this list is empty
 - if `b = t` this list has one element.
-/
def list.Icc [has_le α] [@decidable_rel α (≤)] : list α :=
if b ≤ t then list.Ico b t ++ [t] else []

lemma list.Ico_append_top [has_le α] [@decidable_rel α (≤)] (h : b ≤ t) :
  list.Ico b t ++ [t] = list.Icc b t :=
(if_pos h).symm

/-- `list.Ioo b t` is a list of the values between `b` (exclusive) and `t` (inclusive).

Edge cases (assuming `has_lawful_enum α`):
- if `t ≤ b`, this list is empty
-/
def list.Ioo : list α := (list.Ico b t).tail

end has_enum

section has_lawful_enum

/-- `has_lawful_enum α` expresses `list.Ico b t` and `list.Icc b t` are
strictly ordered lists between the given bounds.
-/
class has_lawful_enum (α : Type*) [linear_order α] extends has_enum α :=
(mem_Ico : ∀ (x b t : α), x ∈ list.Ico b t ↔ b ≤ x ∧ x < t)
(sorted_Ico : ∀ (b t : α), list.sorted (<) (list.Ico b t))

namespace list

variables {α β : Type*} [linear_order α] [linear_order β] [has_lawful_enum α] [has_lawful_enum β]

lemma sorted_Ico (b t : α) : sorted (<) (Ico b t) := has_lawful_enum.sorted_Ico b t

lemma sorted_le_Ico (b t : α) : sorted (≤) (Ico b t) :=
pairwise.imp (λ a b, le_of_lt) (sorted_Ico b t)

lemma nodup_Ico (b t : α) : nodup (Ico b t) :=
pairwise.imp (λ a b, ne_of_lt) (sorted_Ico b t)

@[simp] lemma mem_Ico {x b t : α} : x ∈ Ico b t ↔ b ≤ x ∧ x < t := has_lawful_enum.mem_Ico x b t

lemma sorted_Icc (b t : α) [@decidable_rel α (≤)] : sorted (<) (Icc b t) :=
begin
  unfold Icc,
  split_ifs with h,
  { refine pairwise_append.mpr ⟨sorted_Ico b t, sorted_singleton t, _⟩,
    intros x hx t' ht',
    rw mem_singleton.mp ht',
    exact (mem_Ico.mp hx).2 },
  { exact sorted_nil }
end

lemma sorted_le_Icc (b t : α) [@decidable_rel α (≤)] : sorted (≤) (Icc b t) :=
pairwise.imp (λ a b, le_of_lt) (sorted_Icc b t)

lemma nodup_Icc (b t : α) [@decidable_rel α (≤)] : nodup (Icc b t) :=
pairwise.imp (λ a b, ne_of_lt) (sorted_Icc b t)

@[simp] lemma mem_Icc {x b t : α} [@decidable_rel α (≤)] : x ∈ Icc b t ↔ b ≤ x ∧ x ≤ t :=
begin
  unfold Icc,
  split_ifs with h,
  { rw [mem_append, mem_Ico, mem_singleton, @le_iff_lt_or_eq _ _ x t],
    by_cases hx : x = t,
    { rw hx, tauto },
    { tauto } },
  { simp only [mem_nil_iff, false_iff],
    intro hx,
    exact h (le_trans hx.1 hx.2) },
end

lemma pairwise_tail {r : α → α → Prop} : ∀ {l : list α} (h : pairwise r l), pairwise r (l.tail)
| [] h := pairwise.nil
| (x :: xs) h := (pairwise_cons.mp h).2

lemma sorted_Ioo (b t : α) : sorted (<) (Ioo b t) :=
pairwise_tail (sorted_Ico b t)

lemma sorted_le_Ioo (b t : α) : sorted (≤) (Ioo b t) :=
pairwise.imp (λ a b, le_of_lt) (sorted_Ioo b t)

lemma nodup_Ioo (b t : α) : nodup (Ioo b t) :=
pairwise.imp (λ a b, ne_of_lt) (sorted_Ioo b t)

lemma mem_tail_of_nodup {x : α} : ∀ {l : list α} (hl : l.nodup), x ∈ l.tail ↔ x ∉ l.nth 0 ∧ x ∈ l
| [] hl := by simp
| (y :: l) hl :=
by { simp only [tail, nth, option.mem_def, mem_cons_iff, eq_comm,
    and_or_distrib_left, not_and_self, false_or],
  refine ⟨λ h, ⟨_, h⟩, λ h, h.2⟩,
  cases hl with _ _ y_ne,
  exact (y_ne _ h).symm }

lemma Ico_unique_iff {b t : α} {l : list α}  :
  l = Ico b t ↔ sorted (<) l ∧ ∀ x, x ∈ l ↔ b ≤ x ∧ x < t :=
⟨λ h, h.symm ▸ ⟨h.symm ▸ sorted_Ico b t, λ x, mem_Ico⟩,
 λ ⟨hs, hm⟩, eq_of_sorted_of_perm
    ((perm_ext (pairwise.imp (λ _ _ h, ne_of_lt h) hs) (nodup_Ico b t)).mpr
      (by simpa only [mem_Ico]))
  hs
  (sorted_Ico b t)⟩

/-- The properties in `has_lawful_enum` uniquely specify `Ico b t`. -/
theorem Ico_unique {b t : α} {l : list α}
  (hs : sorted (<) l) (hm : ∀ x, x ∈ l ↔ b ≤ x ∧ x < t) :
  l = Ico b t :=
Ico_unique_iff.mpr ⟨hs, hm⟩

lemma Icc_unique_iff {b t : α} {l : list α}  :
  l = Icc b t ↔ sorted (<) l ∧ ∀ x, x ∈ l ↔ b ≤ x ∧ x ≤ t :=
⟨λ h, h.symm ▸ ⟨h.symm ▸ sorted_Icc b t, λ x, mem_Icc⟩,
 λ ⟨hs, hm⟩, eq_of_sorted_of_perm
    ((perm_ext (pairwise.imp (λ _ _ h, ne_of_lt h) hs) (nodup_Icc b t)).mpr
      (by simpa only [mem_Icc]))
  hs
  (sorted_Icc b t)⟩

/-- The properties in `has_lawful_enum` uniquely specify `Icc b t`. -/
theorem Icc_unique {b t : α} {l : list α}
  (hs : sorted (<) l) (hm : ∀ x, x ∈ l ↔ b ≤ x ∧ x ≤ t) :
  l = Icc b t :=
Icc_unique_iff.mpr ⟨hs, hm⟩

lemma bot_le_of_mem_Ico {x b t : α} (h : x ∈ Ico b t) : b ≤ x := (mem_Ico.mp h).1

lemma lt_top_of_mem_Ico {x b t : α} (h : x ∈ Ico b t) : x < t := (mem_Ico.mp h).2

lemma bot_le_of_mem_Icc {x b t : α} [@decidable_rel α (≤)] (h : x ∈ Icc b t) : b ≤ x :=
(mem_Icc.mp h).1

lemma le_top_of_mem_Icc {x b t : α} [@decidable_rel α (≤)] (h : x ∈ Icc b t) : x ≤ t :=
(mem_Icc.mp h).2

lemma bot_mem_Ico {b t : α} : b ∈ Ico b t ↔ b < t :=
mem_Ico.trans ⟨λ ⟨_, h⟩, h, λ h, ⟨le_rfl, h⟩⟩

lemma top_not_mem_Ico (b t : α) : ¬ t ∈ Ico b t := mt lt_top_of_mem_Ico (lt_irrefl t)

lemma bot_mem_Icc {b t : α} [@decidable_rel α (≤)] : b ∈ Icc b t ↔ b ≤ t :=
mem_Icc.trans ⟨λ ⟨_, h⟩, h, λ h, ⟨le_rfl, h⟩⟩

lemma not_mem_Ico_of_le {x b t : α} (htb : t ≤ b) : ¬ x ∈ Ico b t :=
λ h, not_lt_of_ge htb (lt_of_le_of_lt (bot_le_of_mem_Ico h) (lt_top_of_mem_Ico h))

lemma not_mem_Icc_of_lt {x b t : α} (htb : t < b) [@decidable_rel α (≤)] : ¬ x ∈ Icc b t :=
λ h, not_le_of_gt htb (le_trans (bot_le_of_mem_Icc h) (le_top_of_mem_Icc h))

@[simp] lemma Ico_eq_nil {b t : α} :
  Ico b t = [] ↔ t ≤ b :=
eq_nil_iff_forall_not_mem.trans
  ⟨λ h, le_of_not_gt (mt bot_mem_Ico.mpr (h b)),
   λ h x, not_mem_Ico_of_le h⟩

@[simp] lemma Ico_self {b : α} : Ico b b = [] :=
Ico_eq_nil.mpr le_rfl

@[simp] lemma Icc_self {b : α} : Icc b b = [b] :=
by rw [← Ico_append_top _ _ (le_refl b), Ico_self, nil_append]

@[simp] lemma length_Ico_pos_iff {b t : α} :
  0 < length (Ico b t) ↔ b < t :=
begin
  refine ⟨λ h, _, λ h, length_pos_of_mem (bot_mem_Ico.mpr h)⟩,
  obtain ⟨x, hx⟩ := exists_mem_of_length_pos h,
  calc b ≤ x : bot_le_of_mem_Ico hx
     ... < t : lt_top_of_mem_Ico hx
end

lemma exists_le_mem_Ico_of_lt {x b t : α} (hbt : b < t) (hxt : x < t) :
  ∃ y ∈ Ico b t, x ≤ y :=
begin
  by_cases hbx : b ≤ x,
  { exact ⟨x, mem_Ico.mpr ⟨hbx, hxt⟩, le_rfl⟩ },
  { exact ⟨b, bot_mem_Ico.mpr hbt, le_of_not_ge hbx⟩ }
end

lemma exists_le_mem_Icc_of_le [@decidable_rel α (≤)] {x b t : α} (hbt : b ≤ t) (hxt : x ≤ t) :
  ∃ y ∈ Icc b t, x ≤ y :=
begin
  by_cases hbx : b ≤ x,
  { exact ⟨x, mem_Icc.mpr ⟨hbx, hxt⟩, le_rfl⟩ },
  { exact ⟨b, bot_mem_Icc.mpr hbt, le_of_not_ge hbx⟩ }
end

lemma sorted_Ico_append {b t : α} {l : list α} (hl : l.sorted (<)) (ht : ∀ y ∈ l, t ≤ y) :
  sorted (<) (Ico b t ++ l) :=
pairwise_append.mpr ⟨sorted_Ico b t, hl,
  λ x x_mem y y_mem, lt_of_lt_of_le (mem_Ico.mp x_mem).2 (ht y y_mem)⟩

lemma sorted_Ico_append_Ico {b t b' t' : α} (h : t ≤ b') :
  sorted (<) (Ico b t ++ Ico b' t') :=
sorted_Ico_append (sorted_Ico b' t') (λ y hy, le_trans h (bot_le_of_mem_Ico hy))

@[simp] lemma sorted_Ico_append_iff {b t : α} {l : list α} :
  sorted (<) (Ico b t ++ l) ↔ l.sorted (<) ∧ (t ≤ b ∨ ∀ y ∈ l, t ≤ y) :=
begin
  refine pairwise_append.trans ⟨_, _⟩,
  { rintros ⟨-, hl, ht⟩,
    use hl,
    by_cases htb : t ≤ b,
    { exact or.inl htb},
    { refine or.inr (λ y y_mem, le_of_not_lt (λ hyt, _)),
      obtain ⟨x, x_mem, hyx⟩ := exists_le_mem_Ico_of_lt (lt_of_not_ge htb) hyt,
      exact not_lt_of_ge hyx (ht x x_mem y y_mem) } },
  rintros ⟨hl, ht⟩,
  refine ⟨sorted_Ico b t, hl, λ x x_mem y y_mem, _⟩,
  have ht := or.resolve_left ht (λ h, not_mem_Ico_of_le h x_mem),
  exact lt_of_lt_of_le (lt_top_of_mem_Ico x_mem) (ht y y_mem)
end

@[simp] lemma sorted_Icc_append_iff [@decidable_rel α (≤)] {b t : α} {l : list α} :
  sorted (<) (Icc b t ++ l) ↔ l.sorted (<) ∧ (t < b ∨ ∀ y ∈ l, t < y) :=
begin
  refine pairwise_append.trans ⟨_, _⟩,
  { rintros ⟨-, hl, ht⟩,
    use hl,
    by_cases htb : t < b,
    { exact or.inl htb},
    { refine or.inr (λ y y_mem, lt_of_not_ge (λ hyt, _)),
      obtain ⟨x, x_mem, hyx⟩ := exists_le_mem_Icc_of_le (le_of_not_gt htb) hyt,
      exact not_lt_of_ge hyx (ht x x_mem y y_mem) } },
  rintros ⟨hl, ht⟩,
  refine ⟨sorted_Icc b t, hl, λ x x_mem y y_mem, _⟩,
  have ht := or.resolve_left ht (λ h, not_mem_Icc_of_lt h x_mem),
  exact lt_of_le_of_lt (le_top_of_mem_Icc x_mem) (ht y y_mem)
end

lemma sorted_Ico_append_Icc {b t b' t' : α} (h : t ≤ b') :
  sorted (<) (Ico b t ++ Icc b' t') :=
sorted_Ico_append (sorted_Icc b' t') (λ y hy, le_trans h (bot_le_of_mem_Icc hy))

@[simp] lemma Ico_append_Ico {b m t : α} (hbm : b ≤ m) (hmt : m ≤ t) :
  Ico b m ++ Ico m t = Ico b t :=
Ico_unique (sorted_Ico_append_Ico le_rfl) (λ x, by
  { simp only [mem_append, mem_Ico], split,
    { rintro (⟨hbx, hxm⟩ | ⟨hmx, hxt⟩),
      { exact ⟨hbx, lt_of_lt_of_le hxm hmt⟩ },
      { exact ⟨le_trans hbm hmx, hxt⟩ } },
    { rintro ⟨hbx, hbt⟩,
      cases le_or_lt m x with hmx hxm,
      { exact or.inr ⟨hmx, hbt⟩ },
      { exact or.inl ⟨hbx, hxm⟩ } } })

@[simp] lemma Ico_append_Icc {b m t : α} (hbm : b ≤ m) (hmt : m ≤ t) :
  Ico b m ++ Icc m t = Icc b t :=
Icc_unique (sorted_Ico_append_Icc le_rfl) (λ x, by
  { simp only [mem_append, mem_Ico, mem_Icc], split,
    { rintro (⟨hbx, hxm⟩ | ⟨hmx, hxt⟩),
      { exact ⟨hbx, le_trans (le_of_lt hxm) hmt⟩ },
      { exact ⟨le_trans hbm hmx, hxt⟩ } },
    { rintro ⟨hbx, hbt⟩,
      cases le_or_lt m x with hmx hxm,
      { exact or.inr ⟨hmx, hbt⟩ },
      { exact or.inl ⟨hbx, hxm⟩ } } })

lemma map_Ico_eq_Ico (f : α → β) (f_mono : strict_mono f)
  (f_surj' : ∀ (x y : α) (z : β) (hxz : f x ≤ z) (hzy : z ≤ f y), ∃ z', f z' = z)
  (b t : α) :
  map f (Ico b t) = Ico (f b) (f t) :=
Ico_unique
  ((pairwise_map _).mpr (pairwise.imp f_mono (sorted_Ico b t)))
  (λ x, by { simp only [mem_map, mem_Ico], split,
    { rintro ⟨x, ⟨hbx, hxt⟩, rfl⟩,
      exact ⟨f_mono.monotone hbx, f_mono hxt⟩ },
    { rintro ⟨hbx, hxt⟩,
      obtain ⟨x, rfl⟩ := f_surj' b t x hbx (le_of_lt hxt),
      exact ⟨x, ⟨f_mono.le_iff_le.mp hbx, f_mono.lt_iff_lt.mp hxt⟩, rfl⟩ } })

lemma bot_le_bot_of_Ico_subset_Ico {b b' t t' : α} (hlt : b < t)
  (h : Ico b t ⊆ Ico b' t') : b' ≤ b :=
bot_le_of_mem_Ico (h (bot_mem_Ico.mpr hlt))

lemma bot_lt_top_of_Ico_subset_Ico {b b' t t' : α} (hlt : b < t)
  (h : Ico b t ⊆ Ico b' t') : b < t' :=
lt_top_of_mem_Ico (h (bot_mem_Ico.mpr hlt))

lemma top_le_top_of_Ico_subset_Ico {b b' t t' : α} (hbt : b < t)
  (h : Ico b t ⊆ Ico b' t') : t ≤ t' :=
le_of_not_lt (λ htt', top_not_mem_Ico b' t' (h (mem_Ico.mpr
  ⟨le_of_lt (bot_lt_top_of_Ico_subset_Ico hbt h), htt'⟩)))

theorem Ico_sublist_Ico {b t b' t' : α} (hlt : b < t) : Ico b t <+ Ico b' t' ↔ b' ≤ b ∧ t ≤ t' :=
begin
  split,
  { intro h,
    exact ⟨bot_le_bot_of_Ico_subset_Ico hlt h.subset, top_le_top_of_Ico_subset_Ico hlt h.subset⟩ },
  { rintros ⟨hb, ht⟩,
    rw [← Ico_append_Ico hb (le_trans (le_of_lt hlt) ht), ← Ico_append_Ico (le_of_lt hlt) ht],
    exact sublist_append_of_sublist_right (sublist_append_left _ _) }
end

theorem Ico_subset_Ico {b t b' t' : α} (hlt : b < t) : Ico b t ⊆ Ico b' t' ↔ b' ≤ b ∧ t ≤ t' :=
begin
  split,
  { intro h,
    exact ⟨bot_le_bot_of_Ico_subset_Ico hlt h, top_le_top_of_Ico_subset_Ico hlt h⟩ },
  { rintros ⟨hb, ht⟩,
    rw [← Ico_append_Ico hb (le_trans (le_of_lt hlt) ht), ← Ico_append_Ico (le_of_lt hlt) ht],
    exact subset_append_of_subset_right _ _ _ (subset_append_left _ _) }
end

@[simp] lemma Ico_inter_Ico_consecutive [decidable_eq α] (b m t : α) : Ico b m ∩ Ico m t = [] :=
begin
  apply eq_nil_iff_forall_not_mem.2,
  intro a,
  simp only [and_imp, not_and, not_lt, mem_inter, mem_Ico],
  intros h₁ h₂ h₃,
  exfalso,
  exact not_lt_of_ge h₃ h₂
end

@[simp] lemma Ico_bag_inter_Ico_consecutive [decidable_eq α] (b m t : α) :
  list.bag_inter (Ico b m) (Ico m t) = [] :=
(bag_inter_nil_iff_inter_nil _ _).2 (Ico_inter_Ico_consecutive b m t)

@[simp] lemma Ico_nth_le_zero {b t : α} (h : 0 < (Ico b t).length) :
  (Ico b t).nth_le 0 h = b :=
begin
  refine le_antisymm _ (bot_le_of_mem_Ico (nth_le_mem _ _ _)),
  have h' := length_Ico_pos_iff.mp h,
  obtain ⟨i, i_lt, eq_b⟩ := nth_le_of_mem (bot_mem_Ico.mpr h'),
  conv_rhs { rw ← eq_b },
  exact nth_le_of_sorted_of_le (sorted_le_Ico b t) (nat.zero_le i),
end

lemma mem_Ico_nth_zero {b t x : α} : x ∈ (Ico b t).nth 0 ↔ x = b ∧ b < t :=
begin
  set y := (Ico b t).nth 0 with ← hy,
  revert hy,
  refine @option.cases_on _ (λ y, (Ico b t).nth 0 = y → (x ∈ y ↔ x = b ∧ b < t)) y _ _,
  { intros h,
    rw [nth_eq_none_iff, nat.le_zero_iff, length_eq_zero, Ico_eq_nil] at h,
    simp only [h, false_iff, not_and, not_lt, option.not_mem_none, forall_true_iff] },
  { intros y h,
    rw [option.mem_def, option.some_inj],
    obtain ⟨len_pos, rfl⟩ := nth_eq_some.mp h,
    simp only [Ico_nth_le_zero, length_Ico_pos_iff.mp len_pos, and_true, eq_comm] },
end

@[simp] lemma mem_Ioo {x b t : α} : x ∈ Ioo b t ↔ b < x ∧ x < t :=
begin
  unfold Ioo,
  rw [mem_tail_of_nodup (nodup_Ico b t), mem_Ico_nth_zero, mem_Ico, not_and],
  split,
  { rintros ⟨ne, le, lt⟩,
    exact ⟨lt_of_le_of_ne le (λ h, ne h.symm (lt_of_le_of_lt le lt)), lt⟩ },
  { rintros ⟨b_lt_x, x_lt_t⟩,
    refine ⟨_, le_of_lt b_lt_x, x_lt_t⟩,
    rintro rfl,
    have := lt_asymm b_lt_x,
    contradiction }
end

lemma bot_lt_of_mem_Ioo {x b t : α} (h : x ∈ Ioo b t) : b < x := (mem_Ioo.mp h).1

lemma lt_top_of_mem_Ioo {x b t : α} (h : x ∈ Ioo b t) : x < t := (mem_Ioo.mp h).2

lemma Icc_append_Ioo {b m t : α} (b_le_m : b ≤ m) (m_lt_t : m < t) :
  Icc b m ++ Ioo m t = Ico b t :=
Ico_unique (sorted_Icc_append_iff.mpr ⟨sorted_Ioo _ _, or.inr (λ x hx, bot_lt_of_mem_Ioo hx)⟩)
  (λ x, mem_append.trans ⟨λ h, h.elim
      (λ hx, ⟨bot_le_of_mem_Icc hx, lt_of_le_of_lt (le_top_of_mem_Icc hx) m_lt_t⟩)
      (λ hx, ⟨le_trans b_le_m (le_of_lt (bot_lt_of_mem_Ioo hx)), lt_top_of_mem_Ioo hx⟩),
    λ ⟨b_le, lt_t⟩, if h : x ≤ m
      then or.inl (mem_Icc.mpr ⟨b_le, h⟩)
      else or.inr (mem_Ioo.mpr ⟨lt_of_not_ge h, lt_t⟩)⟩)

namespace Ico

lemma filter_lt_of_top_le [decidable_rel ((<) : α → α → Prop)] {n m l : α} (hml : m ≤ l) :
  (Ico n m).filter (λ x, x < l) = Ico n m :=
filter_eq_self.2 $ assume k hk, lt_of_lt_of_le (mem_Ico.1 hk).2 hml

lemma filter_lt_of_le_bot [decidable_rel ((<) : α → α → Prop)] {n m l : α} (hln : l ≤ n) :
  (Ico n m).filter (λ x, x < l) = [] :=
filter_eq_nil.2 $ assume k hk, not_lt_of_le $ le_trans hln $ (mem_Ico.1 hk).1

lemma filter_lt_of_ge [decidable_rel ((<) : α → α → Prop)] {n m l : α} (hlm : l ≤ m) :
  (Ico n m).filter (λ x, x < l) = Ico n l :=
begin
  cases le_total n l with hnl hln,
  { rw [← Ico_append_Ico hnl hlm, filter_append,
      filter_lt_of_top_le (le_refl l), filter_lt_of_le_bot (le_refl l), append_nil] },
  { rw [Ico_eq_nil.mpr hln, filter_lt_of_le_bot hln] }
end

@[simp] lemma filter_lt (n m l : α) :
  (Ico n m).filter (λ x, x < l) = Ico n (min m l) :=
begin
  cases le_total m l with hml hlm,
  { rw [min_eq_left hml, filter_lt_of_top_le hml] },
  { rw [min_eq_right hlm, filter_lt_of_ge hlm] }
end

lemma le_filter_of_le_bot [decidable_rel ((≤) : α → α → Prop)] {n m l : α} (hln : l ≤ n) :
  (Ico n m).filter (λ x, l ≤ x) = Ico n m :=
filter_eq_self.2 $ assume k hk, le_trans hln (mem_Ico.1 hk).1

lemma le_filter_of_top_le [decidable_rel ((≤) : α → α → Prop)] {n m l : α} (hml : m ≤ l) :
  (Ico n m).filter (λ x, l ≤ x) = [] :=
filter_eq_nil.2 $ assume k hk, not_le_of_gt (lt_of_lt_of_le (mem_Ico.1 hk).2 hml)

lemma le_filter_of_le [decidable_rel ((≤) : α → α → Prop)] {n m l : α} (hnl : n ≤ l) :
  (Ico n m).filter (λ x, l ≤ x) = Ico l m :=
begin
  cases le_total l m with hlm hml,
  { rw [← Ico_append_Ico hnl hlm, filter_append,
        le_filter_of_top_le (le_refl l), le_filter_of_le_bot (le_refl l), nil_append] },
  { rw [Ico_eq_nil.mpr hml, le_filter_of_top_le hml] }
end

@[simp] lemma le_filter (n m l : α) :
  (Ico n m).filter (λ x, l ≤ x) = Ico (max n l) m :=
begin
  cases le_total n l with hnl hln,
  { rw [max_eq_right hnl, le_filter_of_le hnl] },
  { rw [max_eq_left hln, le_filter_of_le_bot hln] }
end

lemma filter_le_of_top_le {n m l : α} (hml : m ≤ l) :
  (Ico n m).filter (λ x, x ≤ l) = Ico n m :=
filter_eq_self.2 $ assume k hk, le_trans (le_of_lt (mem_Ico.1 hk).2) hml

lemma filter_le_of_le_bot {n m l : α} (hln : l < n) :
  (Ico n m).filter (λ x, x ≤ l) = [] :=
filter_eq_nil.2 $ assume k hk, not_le_of_lt $ lt_of_lt_of_le hln $ (mem_Ico.1 hk).1

lemma filter_le_of_gt {n m l : α} (hlm : l < m) :
  (Ico n m).filter (λ x, x ≤ l) = Icc n l :=
Icc_unique ((pairwise_filter _).mpr (pairwise.imp (λ _ _ h _ _, h) (sorted_Ico n m)))
  (λ x, mem_filter.trans ⟨λ ⟨hx, hxl⟩, ⟨bot_le_of_mem_Ico hx, hxl⟩,
    λ ⟨hnx, hxl⟩, ⟨mem_Ico.mpr ⟨hnx, lt_of_le_of_lt hxl hlm⟩, hxl⟩⟩)

@[simp] lemma filter_le_of_bot {n m : α}
  (hnm : n < m) : (Ico n m).filter (λ x, x ≤ n) = [n] :=
by rwa [Ico.filter_le_of_gt, Icc_self]

end Ico

/--
For any `n a b : α`, one of the following holds:
1. n < a
2. n ≥ b
3. n ∈ Ico a b
-/
lemma trichotomy (n a b : α) : n < a ∨ b ≤ n ∨ n ∈ Ico a b :=
begin
  by_cases h₁ : n < a,
  { left, exact h₁ },
  { right,
    by_cases h₂ : n ∈ Ico a b,
    { right, exact h₂ },
    { left,  simp only [mem_Ico, not_and, not_lt] at *, exact h₂ h₁ } }
end

end list

end has_lawful_enum

section ordered_monoid

variables {α : Type*}

open list

/-- If `z - x` exists when `x + y ≤ z`, then `((+) x)` maps `Ico`s to `Ico`s. -/
lemma linear_ordered_cancel_add_comm_monoid.map_add_list_Ico
  [linear_ordered_cancel_add_comm_monoid α] [has_lawful_enum α]
  (h : ∀ (x y z : α), x + y ≤ z → ∃ z', x + z' = z) (x b t : α) :
  map ((+) x) (Ico b t) = Ico (x + b) (x + t) :=
map_Ico_eq_Ico ((+) x) (λ a b h, add_lt_add_left h _)
  (λ a b c hac hcb, h _ _ _ hac)
  _ _

/-- `((+) x)` maps `Ico`s to `Ico`s. -/
@[simp]
lemma linear_ordered_add_comm_group.map_add_list_Ico
  [linear_ordered_add_comm_group α] [has_lawful_enum α] (x b t : α) :
  map ((+) x) (Ico b t) = Ico (x + b) (x + t) :=
linear_ordered_cancel_add_comm_monoid.map_add_list_Ico
  (λ x y z _, ⟨z - x, add_sub_cancel'_right _ _⟩) _ _ _

end ordered_monoid

namespace list
/- iota and intervals -/

universe u

variables {α : Type u}

section nat

/-- `Ico'_ℕ s n` is the list of natural numbers `[s, s+1, ..., s+n-1]`.
It is intended mainly for implementing `nat.has_enum`. -/
@[simp] def Ico'_ℕ : ℕ → ℕ → list ℕ
| s 0     := []
| s (n+1) := s :: Ico'_ℕ (s+1) n

instance nat.has_enum : has_enum ℕ :=
⟨λ b t, Ico'_ℕ b (t - b)⟩

@[simp] lemma Ico'_ℕ_eq_Ico (s n : ℕ) : Ico'_ℕ s n = Ico s (s + n) :=
congr_arg (Ico'_ℕ s) (nat.add_sub_cancel_left _ _).symm

lemma Ico'_ℕ_succ (s n : ℕ) : Ico'_ℕ s (n + 1) = s :: Ico'_ℕ (s + 1) n := rfl

theorem length_Ico'_ℕ : ∀ (s n : ℕ), length (Ico'_ℕ s n) = n
| s 0     := rfl
| s (n+1) := congr_arg succ (length_Ico'_ℕ _ _)

-- TODO: is this generalizable to `ℤ`? `fin n`?
@[simp] lemma length_Ico (b t : ℕ) : length (Ico b t) = t - b :=
length_Ico'_ℕ _ _

lemma length_Ico_zero (t : ℕ) : length (Ico 0 t) = t :=
length_Ico 0 t

theorem mem_Ico'_ℕ {m : ℕ} : ∀ {s n : ℕ}, m ∈ Ico'_ℕ s n ↔ s ≤ m ∧ m < s + n
| s 0     := (false_iff _).2 $ λ ⟨H1, H2⟩, not_le_of_lt H2 H1
| s (succ n) :=
  have m = s → m < s + n + 1,
    from λ e, e ▸ lt_succ_of_le (le_add_right _ _),
  have l : m = s ∨ s + 1 ≤ m ↔ s ≤ m,
    by simpa only [eq_comm] using (@le_iff_eq_or_lt _ _ s m).symm,
  (mem_cons_iff _ _ _).trans $ by simp only [mem_Ico'_ℕ,
    or_and_distrib_left, or_iff_right_of_imp this, l, add_right_comm]; refl

theorem chain_succ_Ico'_ℕ : ∀ s n : ℕ, chain (λ a b, b = succ a) s (Ico'_ℕ (s+1) n)
| s 0     := chain.nil
| s (n+1) := (chain_succ_Ico'_ℕ (s+1) n).cons rfl

theorem chain_lt_Ico'_ℕ (s n : ℕ) : chain (<) s (Ico'_ℕ (s+1) n) :=
(chain_succ_Ico'_ℕ s n).imp (λ a b e, e.symm ▸ lt_succ_self _)

theorem pairwise_lt_Ico'_ℕ : ∀ s n : ℕ, pairwise (<) (Ico'_ℕ s n)
| s 0     := pairwise.nil
| s (n+1) := (chain_iff_pairwise (by exact λ a b c, lt_trans)).1 (chain_lt_Ico'_ℕ s n)

instance nat.has_lawful_enum : has_lawful_enum ℕ :=
{ mem_Ico := λ x b t, mem_Ico'_ℕ.trans
    ⟨λ ⟨hb, ht⟩, ⟨hb,
      by { cases le_total b t with hnm hmn,
           { rwa nat.add_sub_of_le hnm at ht },
           { have := not_lt_of_le hb,
             rw [nat.sub_eq_zero_of_le hmn, add_zero] at ht,
             contradiction } }⟩,
     λ ⟨hb, (ht : x < t)⟩, ⟨hb, by rwa nat.add_sub_cancel' (le_trans hb (le_of_lt ht))⟩⟩,
  sorted_Ico := λ b t, pairwise_lt_Ico'_ℕ _ _,
  .. nat.has_enum }

theorem map_add_Ico'_ℕ (a) : ∀ s n : ℕ, map ((+) a) (Ico'_ℕ s n) = Ico'_ℕ (a + s) n
| s 0     := rfl
| s (n+1) := congr_arg (cons _) (map_add_Ico'_ℕ (s+1) n)

@[simp]
lemma map_add_Ico_ℕ (x b t : ℕ) : map ((+) x) (Ico b t) = Ico (x + b) (x + t) :=
linear_ordered_cancel_add_comm_monoid.map_add_list_Ico
  (λ x y z h, ⟨z - x, nat.add_sub_cancel' (le_trans (nat.le_add_right _ _) h)⟩) _ _ _

lemma map_add_Ico_ℕ' (x b t : ℕ) : map ((+) x) (Ico b t) = Ico (b + x) (t + x) :=
by rw [map_add_Ico_ℕ, add_comm b x, add_comm t x]

lemma map_succ_Ico'_ℕ : ∀ (s n : ℕ), map nat.succ (Ico'_ℕ s n) = Ico'_ℕ (s + 1) n
| s 0       := rfl
| s (n + 1) := congr_arg (cons _) (map_succ_Ico'_ℕ _ _)

@[simp]
lemma map_succ_Ico (b t : ℕ) : map nat.succ (Ico b t) = Ico (b + 1) (t + 1) :=
by rw [add_comm b 1, add_comm t 1, ← map_add_Ico_ℕ, show ((+) 1) = nat.succ, from funext nat.one_add]

theorem map_sub_Ico'_ℕ (a) :
  ∀ (s n : ℕ) (h : a ≤ s), map (λ x, x - a) (Ico'_ℕ s n) = Ico'_ℕ (s - a) n
| s 0     _ := rfl
| s (n+1) h :=
begin
  convert congr_arg (cons (s-a)) (map_sub_Ico'_ℕ (s+1) n (nat.le_succ_of_le h)),
  rw nat.succ_sub h,
  refl,
end

theorem map_sub_Ico_ℕ (a b t : ℕ) (h : a ≤ b) : (Ico b t).map (λ x, x - a) = Ico (b - a) (t - a) :=
begin
  refine trans (map_sub_Ico'_ℕ a b _ h) (congr_arg (Ico'_ℕ (b - a)) _),
  rw [nat.sub_sub, nat.add_sub_cancel' h],
end

theorem nodup_Ico'_ℕ (s n : ℕ) : nodup (Ico'_ℕ s n) :=
(pairwise_lt_Ico'_ℕ s n).imp (λ a b, ne_of_lt)

theorem Ico'_ℕ_append : ∀ s m n : ℕ, Ico'_ℕ s m ++ Ico'_ℕ (s+m) n = Ico'_ℕ s (n+m)
| s 0     n := rfl
| s (m+1) n := show s :: (Ico'_ℕ (s+1) m ++ Ico'_ℕ (s+m+1) n) = s :: Ico'_ℕ (s+1) (n+m),
               by rw [add_right_comm, Ico'_ℕ_append]

theorem Ico'_ℕ_sublist_right {s m n : ℕ} : Ico'_ℕ s m <+ Ico'_ℕ s n ↔ m ≤ n :=
⟨λ h, by simpa only [length_Ico'_ℕ] using length_le_of_sublist h,
 λ h, by rw [← nat.sub_add_cancel h, ← Ico'_ℕ_append]; apply sublist_append_left⟩

theorem Ico'_ℕ_subset_right {s m n : ℕ} : Ico'_ℕ s m ⊆ Ico'_ℕ s n ↔ m ≤ n :=
⟨λ h, le_of_not_lt $ λ hn, lt_irrefl (s+n) $
  (mem_Ico'_ℕ.1 $ h $ mem_Ico'_ℕ.2 ⟨le_add_right _ _, nat.add_lt_add_left hn s⟩).2,
 λ h, (Ico'_ℕ_sublist_right.2 h).subset⟩

theorem nth_Ico'_ℕ : ∀ s {m n : ℕ}, m < n → nth (Ico'_ℕ s n) m = some (s + m)
| s 0     (n+1) _ := rfl
| s (m+1) (n+1) h := (nth_Ico'_ℕ (s+1) (lt_of_add_lt_add_right h)).trans $
    by rw add_right_comm; refl

theorem Ico'_ℕ_concat (s n : ℕ) : Ico'_ℕ s (n + 1) = Ico'_ℕ s n ++ [s+n] :=
by rw add_comm n 1; exact (Ico'_ℕ_append s n 1).symm

theorem range_core_Ico'_ℕ : ∀ s n : ℕ, range_core s (Ico'_ℕ s n) = Ico'_ℕ 0 (n + s)
| 0     n := rfl
| (s+1) n := by rw [show n+(s+1) = n+1+s, from add_right_comm n s 1];
exact range_core_Ico'_ℕ s (n+1)

@[nolint deprecated]
theorem range_eq_Ico'_ℕ (n : ℕ) : range n = Ico'_ℕ 0 n :=
(range_core_Ico'_ℕ n 0).trans $ by rw zero_add

theorem Ico_zero_eq_Ico'_ℕ (n : ℕ) : Ico 0 n = Ico'_ℕ 0 n :=
rfl

@[nolint deprecated, simp]
theorem range_eq_Ico_ℕ (n : ℕ) : range n = Ico 0 n :=
range_eq_Ico'_ℕ n

@[simp] theorem self_mem_Ico_zero_succ (n : ℕ) : n ∈ Ico 0 (n + 1) :=
by simp only [succ_pos', lt_add_iff_pos_right, mem_Ico, nat.zero_le n, true_and]

theorem nth_Ico_zero {m n : ℕ} (h : m < n) : nth (Ico 0 n) m = some m :=
(nth_Ico'_ℕ _ (by rwa nat.sub_zero)).trans $ by rw zero_add

theorem Ico_succ_right {b t : ℕ} (h : b ≤ t) : Ico b (t + 1) = b :: Ico (b + 1) (t + 1) :=
by { conv_lhs { rw [← nat.add_sub_cancel' h, add_assoc, ← Ico'_ℕ_eq_Ico, Ico'_ℕ_succ] },
rw [Ico'_ℕ_eq_Ico, succ_add, nat.add_sub_cancel' h] }

theorem Ico_succ_right' {b t : ℕ} (h : b ≤ t) : Ico b (t + 1) = Ico b t ++ [t] :=
begin
  rw Ico_append_top _ _ h,
  apply Icc_unique (sorted_Ico _ _),
  intro x,
  rw [mem_Ico, nat.lt_succ_iff]
end

theorem Ico_eq_cons {b t : ℕ} (h : b < t) : Ico b t = b :: Ico (b + 1) t :=
by { cases t, { cases h }, exact Ico_succ_right (nat.lt_succ_iff.mp h) }

@[simp] lemma Ico_succ_self (n : ℕ) : Ico n (n + 1) = [n] :=
by rw [Ico_succ_right (le_refl n), Ico_self]

@[simp] lemma Ico_pred_self {n : ℕ} (h : 0 < n) : Ico (n - 1) n = [n - 1] :=
by { cases n, { cases h }, exact Ico_succ_self n }

theorem Ico_zero_succ (n : ℕ) : Ico 0 (succ n) = Ico 0 n ++ [n] :=
by simp only [Ico_zero_eq_Ico'_ℕ, Ico'_ℕ_concat, zero_add]

theorem chain'_succ_Ico (n m : ℕ) : chain' (λa b, b = succ a) (Ico n m) :=
begin
  by_cases n < m,
  { rw [Ico_eq_cons h], exact chain_succ_Ico'_ℕ _ _ },
  { rw [Ico_eq_nil.mpr (le_of_not_gt h)], trivial }
end

lemma filter_lt_of_succ_bot {n m : ℕ} (hnm : n < m) : (Ico n m).filter (λ x, x < n + 1) = [n] :=
begin
  have r : min m (n + 1) = n + 1 := (@inf_eq_right _ _ m (n + 1)).mpr hnm,
  simp [Ico.filter_lt n m (n + 1), r],
end

section iota

theorem iota_eq_reverse_Ico'_ℕ : ∀ n : ℕ, iota n = reverse (Ico'_ℕ 1 n)
| 0     := rfl
| (n + 1) := by { simp only [iota, Ico'_ℕ_concat, iota_eq_reverse_Ico'_ℕ n, reverse_append, add_comm],
                refl }

@[simp] theorem length_iota (n : ℕ) : length (iota n) = n :=
by simp only [iota_eq_reverse_Ico'_ℕ, length_reverse, length_Ico'_ℕ]

theorem pairwise_gt_iota (n : ℕ) : pairwise (>) (iota n) :=
by simp only [iota_eq_reverse_Ico'_ℕ, pairwise_reverse, pairwise_lt_Ico'_ℕ]

theorem nodup_iota (n : ℕ) : nodup (iota n) :=
by simp only [iota_eq_reverse_Ico'_ℕ, nodup_reverse, nodup_Ico'_ℕ]

theorem mem_iota {m n : ℕ} : m ∈ iota n ↔ 1 ≤ m ∧ m ≤ n :=
by simp only [iota_eq_reverse_Ico'_ℕ, mem_reverse, mem_Ico'_ℕ, add_comm, lt_succ_iff]

theorem reverse_Ico'_ℕ : ∀ s n : ℕ,
  reverse (Ico'_ℕ s n) = map (λ i, s + n - 1 - i) (Ico 0 n)
| s 0       := rfl
| s (n + 1) := begin
  simp_rw [Ico'_ℕ_concat, reverse_append, reverse_singleton, singleton_append,
    Ico_succ_right (nat.zero_le _), ← map_add_Ico_ℕ', reverse_Ico'_ℕ,
    map_cons, map_map, nat.sub_zero, nat.add_succ, nat.succ_sub_one, add_zero, eq_self_iff_true,
    true_and],
  congr,
  ext i,
  rw nat.sub_sub
end

end iota

end nat

section fin

instance (n : ℕ) : has_enum (fin n) :=
⟨λ b t, (Ico (b : ℕ) (t : ℕ)).pmap fin.mk (λ i hi, lt_trans (lt_top_of_mem_Ico hi) t.2)⟩

@[simp] lemma coe_fin_nat_mem_Ico_coe_coe {n : ℕ} {x b t : fin n} :
  (x : ℕ) ∈ Ico (b : ℕ) (t : ℕ) ↔ x ∈ Ico b t :=
begin
  refine (mem_pmap.trans ⟨_, _⟩).symm,
  { rintros ⟨x, hx, rfl⟩,
    exact hx },
  { intro hx,
    exact ⟨x, hx, fin.mk_coe x⟩ }
end

instance (n : ℕ) : has_lawful_enum (fin n) :=
{ mem_Ico := λ x b t, iff.trans coe_fin_nat_mem_Ico_coe_coe.symm mem_Ico,
  sorted_Ico := λ b t, pairwise_pmap.mpr (pairwise.imp (λ x y (h : x < y) _ _, h)
                        (sorted_Ico (b : ℕ) (t : ℕ))) }

/-- All elements of `fin n`, from `0` to `n-1`. -/
def fin_range (n : ℕ) : list (fin n) :=
(Ico 0 n).pmap fin.mk (λ _ h, (mem_Ico.mp h).2)

@[simp] lemma fin_range_zero : fin_range 0 = [] := rfl

@[simp] lemma mem_fin_range {n : ℕ} (a : fin n) : a ∈ fin_range n :=
mem_pmap.2 ⟨a.1, mem_Ico.mpr ⟨nat.zero_le _, a.2⟩, fin.eta _ _⟩

lemma nodup_fin_range (n : ℕ) : (fin_range n).nodup :=
nodup_pmap (λ _ _ _ _, fin.veq_of_eq) (nodup_Ico _ _)

@[simp] lemma length_fin_range (n : ℕ) : (fin_range n).length = n :=
by rw [fin_range, length_pmap, length_Ico_zero]

@[simp] lemma fin_range_eq_nil {n : ℕ} : fin_range n = [] ↔ n = 0 :=
by rw [← length_eq_zero, length_fin_range]

end fin

@[to_additive]
theorem prod_Ico_zero_succ {α : Type u} [monoid α] (f : ℕ → α) (n : ℕ) :
  ((Ico 0 n.succ).map f).prod = ((Ico 0 n).map f).prod * f n :=
by rw [Ico_zero_succ, map_append, map_singleton,
  prod_append, prod_cons, prod_nil, mul_one]

/-- A variant of `prod_Ico_zero_succ` which pulls off the first
  term in the product rather than the last.-/
@[to_additive "A variant of `sum_Ico_zero_succ` which pulls off the first term in the sum
  rather than the last."]
theorem prod_range_succ' {α : Type u} [monoid α] (f : ℕ → α) (n : ℕ) :
  ((Ico 0 n.succ).map f).prod = f 0 * ((Ico 0 n).map (λ i, f (succ i))).prod :=
nat.rec_on n
  (show 1 * f 0 = f 0 * 1, by rw [one_mul, mul_one])
  (λ _ hd, by rw [list.prod_Ico_zero_succ, hd, mul_assoc, ←list.prod_Ico_zero_succ])

@[simp] theorem enum_from_map_fst : ∀ n (l : list α),
  map prod.fst (enum_from n l) = Ico'_ℕ n l.length
| n []       := rfl
| n (a :: l) := congr_arg (cons _) (enum_from_map_fst _ _)

@[simp] theorem enum_map_fst (l : list α) :
  map prod.fst (enum l) = Ico 0 l.length :=
by simp only [enum, enum_from_map_fst, Ico'_ℕ_eq_Ico, zero_add]

@[simp] lemma nth_le_Ico_zero {n} (i) (H : i < (Ico 0 n).length) :
  nth_le (Ico 0 n) i H = i :=
option.some.inj $ by rw [← nth_le_nth _, nth_Ico_zero (by simpa using H)]

theorem of_fn_eq_pmap {α n} {f : fin n → α} :
  of_fn f = pmap (λ i hi, f ⟨i, hi⟩) (Ico 0 n) (λ _ h, (mem_Ico.mp h).2) :=
by rw [pmap_eq_map_attach]; from ext_le (by simp)
  (λ i hi1 hi2, by { simp at hi1, simp [nth_le_of_fn f ⟨i, hi1⟩, -subtype.val_eq_coe] })

theorem of_fn_id (n) : of_fn id = fin_range n := of_fn_eq_pmap

theorem of_fn_eq_map {α n} {f : fin n → α} :
  of_fn f = (fin_range n).map f :=
by rw [← of_fn_id, map_of_fn, function.right_id]

theorem nodup_of_fn {α n} {f : fin n → α} (hf : function.injective f) :
  nodup (of_fn f) :=
by rw of_fn_eq_pmap; from nodup_pmap
  (λ _ _ _ _ H, fin.veq_of_eq $ hf H) (nodup_Ico _ n)

end list
