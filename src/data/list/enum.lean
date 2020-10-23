/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau, Scott Morrison, Anne Baanen
-/
import data.list.chain
import data.list.of_fn
import data.list.nodup
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

/-- `list.Ico b t` is a list of the values between `b` (inclusive) and `t` (exclusive). -/
def list.Ico : list α := has_enum.enum b t

@[simp] lemma has_enum.enum_eq : @has_enum.enum α _ = list.Ico := rfl

/-- `list.Icc b t` is a list of the values between `b` (inclusive) and `t` (inclusive).

Edge cases (assuming `has_lawful_enum α`):
 - if `t < b`, this list is empty
 - if `b = t` this list has one element.
-/
def list.Icc [has_le α] [@decidable_rel α (≤)] : list α :=
if b ≤ t then list.Ico b t ++ [t] else []

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

lemma Ico_unique_iff {b t : α} {l : list α}  :
  l = Ico b t ↔ sorted (<) l ∧ ∀ x, x ∈ l ↔ b ≤ x ∧ x < t :=
⟨λ h, h.symm ▸ ⟨h.symm ▸ sorted_Ico b t, λ x, mem_Ico⟩,
 λ ⟨hs, hm⟩, eq_of_sorted_of_perm
    ((perm_ext (pairwise.imp (λ _ _ h, ne_of_lt h) hs) (nodup_Ico b t)).mpr
      (by simpa only [mem_Ico]))
  hs
  (sorted_Ico b t)⟩

/-- The properties in `has_lawful_Ico` uniquely specify `Ico b t`. -/
theorem Ico_unique {b t : α} {l : list α}
  (hs : sorted (<) l) (hm : ∀ x, x ∈ l ↔ b ≤ x ∧ x < t) :
  l = Ico b t :=
Ico_unique_iff.mpr ⟨hs, hm⟩

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

lemma top_le_top_of_Ico_subset_Ico {b b' t t' : α} (hle : b ≤ t')
  (h : Ico b t ⊆ Ico b' t') : t ≤ t' :=
le_of_not_lt (λ hlt, top_not_mem_Ico b' t' (h (mem_Ico.mpr ⟨hle, hlt⟩)))

theorem Ico_sublist {b t b' t' : α} (hle : b < t) : Ico b t <+ Ico b' t' ↔ b' ≤ b ∧ t ≤ t' :=
begin
  split,
  { intro h,
    refine ⟨bot_le_bot_of_Ico_subset_Ico hle h.subset, top_le_top_of_Ico_subset_Ico _ h.subset⟩, },
end

theorem range_subset {m n : ℕ} : range m ⊆ range n ↔ m ≤ n :=
by simp only [range_eq_Ico'_ℕ, Ico'_ℕ_subset_right]

@[simp] theorem mem_range {m n : ℕ} : m ∈ range n ↔ m < n :=
by simp only [range_eq_Ico'_ℕ, mem_Ico'_ℕ, nat.zero_le, true_and, zero_add]

@[simp] theorem not_mem_range_self {n : ℕ} : n ∉ range n :=
mt mem_range.1 $ lt_irrefl _

@[simp] theorem self_mem_range_succ (n : ℕ) : n ∈ range (n + 1) :=
by simp only [succ_pos', lt_add_iff_pos_right, mem_range]

theorem nth_range {m n : ℕ} (h : m < n) : nth (range n) m = some m :=
by simp only [range_eq_Ico'_ℕ, nth_Ico'_ℕ _ h, zero_add]

theorem range_concat (n : ℕ) : range (succ n) = range n ++ [n] :=
by simp only [range_eq_Ico'_ℕ, Ico'_ℕ_concat, zero_add]

end list

end has_lawful_enum

section ordered_monoid

variables {α : Type*}

open list

/-- If `z - x` exists when `x + y ≤ z`, then `((+) x)` maps `Ico`s to `Ico`s. -/
lemma decidable_linear_ordered_cancel_add_comm_monoid.map_add_list_Ico
  [decidable_linear_ordered_cancel_add_comm_monoid α] [has_lawful_enum α]
  (h : ∀ (x y z : α), x + y ≤ z → ∃ z', x + z' = z) (x b t : α) :
  map ((+) x) (Ico b t) = Ico (x + b) (x + t) :=
map_Ico_eq_Ico ((+) x) (λ a b h, add_lt_add_left h _)
  (λ a b c hac hcb, h _ _ _ hac)
  _ _

/-- `((+) x)` maps `Ico`s to `Ico`s. -/
@[simp]
lemma decidable_linear_ordered_add_comm_group.map_add_list_Ico
  [decidable_linear_ordered_add_comm_group α] [has_lawful_enum α] (x b t : α) :
  map ((+) x) (Ico b t) = Ico (x + b) (x + t) :=
decidable_linear_ordered_cancel_add_comm_monoid.map_add_list_Ico
  (λ x y z _, ⟨z - x, add_sub_cancel'_right _ _⟩) _ _ _

end ordered_monoid

namespace list
/- iota and intervals -/

universe u

variables {α : Type u}

section Ico'_ℕ

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

example {m n l : ℕ} : n ≤ l ∧ l < n + (m - n) ↔ n ≤ l ∧ l < m :=
begin
  cases le_total n m with hnm hmn,
  { rw [nat.add_sub_of_le hnm] },
  { rw [nat.sub_eq_zero_of_le hmn, add_zero],
    exact and_congr_right (assume hnl, iff.intro
    (assume hln, (not_le_of_gt hln hnl).elim)
    (assume hlm, lt_of_lt_of_le hlm hmn)) }
end

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
decidable_linear_ordered_cancel_add_comm_monoid.map_add_list_Ico
  (λ x y z h, ⟨z - x, nat.add_sub_cancel' (le_trans (nat.le_add_right _ _) h)⟩) _ _ _

theorem map_sub_Ico'_ℕ (a) :
  ∀ (s n : ℕ) (h : a ≤ s), map (λ x, x - a) (Ico'_ℕ s n) = Ico'_ℕ (s - a) n
| s 0     _ := rfl
| s (n+1) h :=
begin
  convert congr_arg (cons (s-a)) (map_sub_Ico'_ℕ (s+1) n (nat.le_succ_of_le h)),
  rw nat.succ_sub h,
  refl,
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

@[nolint deprecated, simp]
theorem range_eq_Ico_ℕ (n : ℕ) : range n = Ico 0 n :=
range_eq_Ico'_ℕ n

end Ico'_ℕ

theorem Ico_succ_right {b t : ℕ} (h : b ≤ t) : Ico b (t + 1) = b :: Ico (b + 1) (t + 1) :=
by { conv_lhs { rw [← nat.add_sub_cancel' h, add_assoc, ← Ico'_ℕ_eq_Ico, Ico'_ℕ_succ] },
     rw [Ico'_ℕ_eq_Ico, succ_add, nat.add_sub_cancel' h] }

theorem iota_eq_reverse_Ico'_ℕ : ∀ n : ℕ, iota n = reverse (Ico'_ℕ 1 n)
| 0     := rfl
| (n+1) := by simp only [iota, Ico'_ℕ_concat, iota_eq_reverse_Ico'_ℕ n, reverse_append, add_comm]; refl

@[simp] theorem length_iota (n : ℕ) : length (iota n) = n :=
by simp only [iota_eq_reverse_Ico'_ℕ, length_reverse, length_Ico'_ℕ]

theorem pairwise_gt_iota (n : ℕ) : pairwise (>) (iota n) :=
by simp only [iota_eq_reverse_Ico'_ℕ, pairwise_reverse, pairwise_lt_Ico'_ℕ]

theorem nodup_iota (n : ℕ) : nodup (iota n) :=
by simp only [iota_eq_reverse_Ico'_ℕ, nodup_reverse, nodup_Ico'_ℕ]

theorem mem_iota {m n : ℕ} : m ∈ iota n ↔ 1 ≤ m ∧ m ≤ n :=
by simp only [iota_eq_reverse_Ico'_ℕ, mem_reverse, mem_Ico'_ℕ, add_comm, lt_succ_iff]

theorem reverse_Ico'_ℕ : ∀ s n : ℕ,
  reverse (Ico'_ℕ s n) = map (λ i, s + n - 1 - i) (range n)
| s 0     := rfl
| s (n+1) := by rw [Ico'_ℕ_concat, reverse_append, range_succ_eq_map];
  simpa only [show s + (n + 1) - 1 = s + n, from rfl, (∘),
    λ a i, show a - 1 - i = a - succ i, from pred_sub _ _,
    reverse_singleton, map_cons, nat.sub_zero, cons_append,
    nil_append, eq_self_iff_true, true_and, map_map]
  using reverse_Ico'_ℕ s n

/-- All elements of `fin n`, from `0` to `n-1`. -/
def fin_range (n : ℕ) : list (fin n) :=
(range n).pmap fin.mk (λ _, list.mem_range.1)

@[simp] lemma fin_range_zero : fin_range 0 = [] := rfl

@[simp] lemma mem_fin_range {n : ℕ} (a : fin n) : a ∈ fin_range n :=
mem_pmap.2 ⟨a.1, mem_range.2 a.2, fin.eta _ _⟩

lemma nodup_fin_range (n : ℕ) : (fin_range n).nodup :=
nodup_pmap (λ _ _ _ _, fin.veq_of_eq) (nodup_range _)

@[simp] lemma length_fin_range (n : ℕ) : (fin_range n).length = n :=
by rw [fin_range, length_pmap, length_range]

@[simp] lemma fin_range_eq_nil {n : ℕ} : fin_range n = [] ↔ n = 0 :=
by rw [← length_eq_zero, length_fin_range]

@[to_additive]
theorem prod_range_succ {α : Type u} [monoid α] (f : ℕ → α) (n : ℕ) :
  ((range n.succ).map f).prod = ((range n).map f).prod * f n :=
by rw [range_concat, map_append, map_singleton,
  prod_append, prod_cons, prod_nil, mul_one]

/-- A variant of `prod_range_succ` which pulls off the first
  term in the product rather than the last.-/
@[to_additive "A variant of `sum_range_succ` which pulls off the first term in the sum
  rather than the last."]
theorem prod_range_succ' {α : Type u} [monoid α] (f : ℕ → α) (n : ℕ) :
  ((range n.succ).map f).prod = f 0 * ((range n).map (λ i, f (succ i))).prod :=
nat.rec_on n
  (show 1 * f 0 = f 0 * 1, by rw [one_mul, mul_one])
  (λ _ hd, by rw [list.prod_range_succ, hd, mul_assoc, ←list.prod_range_succ])

@[simp] theorem enum_from_map_fst : ∀ n (l : list α),
  map prod.fst (enum_from n l) = Ico'_ℕ n l.length
| n []       := rfl
| n (a :: l) := congr_arg (cons _) (enum_from_map_fst _ _)

@[simp] theorem enum_map_fst (l : list α) :
  map prod.fst (enum l) = range l.length :=
by simp only [enum, enum_from_map_fst, range_eq_Ico'_ℕ]

@[simp] lemma nth_le_range {n} (i) (H : i < (range n).length) :
  nth_le (range n) i H = i :=
option.some.inj $ by rw [← nth_le_nth _, nth_range (by simpa using H)]

theorem of_fn_eq_pmap {α n} {f : fin n → α} :
  of_fn f = pmap (λ i hi, f ⟨i, hi⟩) (range n) (λ _, mem_range.1) :=
by rw [pmap_eq_map_attach]; from ext_le (by simp)
  (λ i hi1 hi2, by { simp at hi1, simp [nth_le_of_fn f ⟨i, hi1⟩, -subtype.val_eq_coe] })

theorem of_fn_id (n) : of_fn id = fin_range n := of_fn_eq_pmap

theorem of_fn_eq_map {α n} {f : fin n → α} :
  of_fn f = (fin_range n).map f :=
by rw [← of_fn_id, map_of_fn, function.right_id]

theorem nodup_of_fn {α n} {f : fin n → α} (hf : function.injective f) :
  nodup (of_fn f) :=
by rw of_fn_eq_pmap; from nodup_pmap
  (λ _ _ _ _ H, fin.veq_of_eq $ hf H) (nodup_range n)

end list

#lint
